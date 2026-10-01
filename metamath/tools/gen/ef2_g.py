"""Sortie EF2: the derivative of a holomorphic function is holomorphic near every point (ef2dvl), from the local
power series ef2pse and set.mm's pserdv / dvradcnv / radcnvle."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
import lin
lin.FASTPATH = True
import ef2_e, ef2_f
from ef2_e import AC, HYP0, SQE, base
from z4blib import fvmd

K = '( TopOpen ` CCfld )'
U = BL()
A1C = '( e e. NN0 |-> ( ( e + 1 ) x. ( %s ` ( e + 1 ) ) ) )' % AC


def PSGA(A, v):
    return '( %s e. CC |-> ( n e. NN0 |-> ( ( %s ` n ) x. ( %s ^ n ) ) ) )' % (v, A, v)


def RADf(A, v='c'):
    return 'sup ( { r e. RR | seq 0 ( + , ( %s ` r ) ) e. dom ~~> } , RR* , < )' % PSGA(A, v)


def SDf(A):
    return "( `' abs \" ( 0 [,) %s ) )" % RADf(A)


def FSf(A):
    return '( y e. %s |-> sum_ j e. NN0 ( ( %s ` y ) ` j ) )' % (SDf(A), PSGA(A, 'x'))


def Mf(A):
    R = RADf(A)
    return 'if ( %s e. RR , ( ( ( abs ` a ) + %s ) / 2 ) , ( ( abs ` a ) + 1 ) )' % (R, R)


def Bf(A):
    return '( 0 ( ball ` ( abs o. - ) ) ( ( ( abs ` a ) + %s ) / 2 ) )' % Mf(A)


def DSf(A, y):
    return 'sum_ k e. NN0 ( ( ( k + 1 ) x. ( %s ` ( k + 1 ) ) ) x. ( %s ^ k ) )' % (A, y)


def ESf(A, y):
    return 'sum_ j e. NN0 ( ( %s ` %s ) ` j )' % (PSGA(A, 'x'), y)


S['ef2dvl'] = '( %s -> %s C_ dom ( CC _D ( ( CC _D F ) |` %s ) ) )' % (HYP0, U, U)


def frame(w, C, A, acf):
    """pserdv / psercn / radius facts for the power series with coefficients A (acf : ( C -> A : NN0 --> CC ))"""
    Gx, Gc = PSGA(A, 'x'), PSGA(A, 'c')
    idc = w.s([], 'id', '( c = x -> c = x )')
    cs, _ = w.congr('( n e. NN0 |-> ( ( %s ` n ) x. ( c ^ n ) ) )' % A, {'c': 'x'}, 'c = x', {'c': idc})
    eqG = w.s([cs], 'cbvmptv', '%s = %s' % (Gc, Gx))
    r1 = w.s([eqG], 'fveq1i', '( %s ` r ) = ( %s ` r )' % (Gc, Gx))
    r2 = w.s([r1, w.inst('seqeq3')], 'ax-mp', 'seq 0 ( + , ( %s ` r ) ) = seq 0 ( + , ( %s ` r ) )' % (Gc, Gx))
    r3 = w.s([r2], 'eleq1i', '( seq 0 ( + , ( %s ` r ) ) e. dom ~~> <-> seq 0 ( + , ( %s ` r ) ) e. dom ~~> )' % (Gc, Gx))
    r4 = w.s([r3], 'rabbii', '{ r e. RR | seq 0 ( + , ( %s ` r ) ) e. dom ~~> } = { r e. RR | seq 0 ( + , ( %s ` r ) ) e. dom ~~> }' % (Gc, Gx))
    RX = 'sup ( { r e. RR | seq 0 ( + , ( %s ` r ) ) e. dom ~~> } , RR* , < )' % Gx
    req = w.s([r4], 'supeq1i', '%s = %s' % (RADf(A), RX))
    gq = w.s([], 'eqid', '%s = %s' % (Gx, Gx))
    fq = w.s([], 'eqid', '%s = %s' % (FSf(A), FSf(A)))
    sq = w.s([], 'eqid', '%s = %s' % (SDf(A), SDf(A)))
    mq = w.s([], 'eqid', '%s = %s' % (Mf(A), Mf(A)))
    bq = w.s([], 'eqid', '%s = %s' % (Bf(A), Bf(A)))
    dv = w.s([gq, fq, acf, req, sq, mq, bq], 'pserdv', '( %s -> ( CC _D %s ) = ( y e. %s |-> %s ) )' % (C, FSf(A), SDf(A), DSf(A, 'y')))
    cn = w.s([gq, fq, acf, req, sq, mq], 'psercn', '( %s -> %s e. ( %s -cn-> CC ) )' % (C, FSf(A), SDf(A)))
    rc = w.s([gq, acf, req], 'radcnvcl', '( %s -> %s e. ( 0 [,] +oo ) )' % (C, RADf(A)))
    rx = w.s([w.s([w.s([], 'iccssxr', '( 0 [,] +oo ) C_ RR*')], 'a1i', '( %s -> ( 0 [,] +oo ) C_ RR* )' % C), rc], 'sseldd', '( %s -> %s e. RR* )' % (C, RADf(A)))
    return {'gq': gq, 'req': req, 'dv': dv, 'cn': cn, 'rx': rx, 'A': A, 'acf': acf}


def radle(w, C, fr, X, xst, cvg):
    """( C -> ( abs ` X ) <_ RAD ) from xst : ( C -> X e. CC ) and cvg : ( C -> seq 0 ( + , ( G ` X ) ) e. dom ~~> )"""
    return w.s([fr['gq'], up(w, fr['acf'], C), fr['req'], xst, cvg], 'radcnvle', '( %s -> ( abs ` %s ) <_ %s )' % (C, X, RADf(fr['A'])))


def fs_cc(w, C, fr, Y, yin):
    """( C -> ESf(A, Y) e. CC ) from yin : ( C -> Y e. SDf(A) )"""
    A = fr['A']
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    ff = s([up(w, fr['cn'], C), w.inst('cncff')], 'syl', '%s : %s --> CC' % (FSf(A), SDf(A)))
    fv = s([ff, yin], 'ffvelcdmd', '( %s ` %s ) e. CC' % (FSf(A), Y))
    exs = w.s([w.s([], 'sumex', '%s e. _V' % ESf(A, Y))], 'a1i', '( %s -> %s e. _V )' % (C, ESf(A, Y)))
    if Y == 'y':
        e_ = w.s([], 'eqid', '%s = %s' % (FSf(A), FSf(A)))
        val = w.s([yin, exs, w.s([e_], 'fvmpt2', '( ( y e. %s /\\ %s e. _V ) -> ( %s ` y ) = %s )' % (SDf(A), ESf(A, 'y'), FSf(A), ESf(A, 'y')))], 'syl2anc',
                  '( %s -> ( %s ` y ) = %s )' % (C, FSf(A), ESf(A, 'y')))
    else:
        val = fvmd(w, C, 'y', SDf(A), ESf(A, 'y'), Y, yin, exs)
    return s([val, fv], 'eqeltrrd', '%s e. CC' % ESf(A, Y))


def in_disc(w, C, fr, Y, yc, ylt):
    """( C -> Y e. SDf(A) ) from yc : Y e. CC and ylt : ( abs ` Y ) < RAD"""
    A = fr['A']
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    afn = s([w.s([w.s([], 'absf', 'abs : CC --> RR'), w.inst('ffn')], 'ax-mp', 'abs Fn CC')], 'a1i', 'abs Fn CC')
    R = RADf(A)
    ep = s([afn, w.inst('elpreima')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ ( abs ` %s ) e. ( 0 [,) %s ) ) )' % (Y, SDf(A), Y, Y, R))
    ay = s([yc], 'abscld', '( abs ` %s ) e. RR' % Y)
    eo = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), up(w, fr['rx'], C), w.inst('elico2')], 'syl2anc',
           '( ( abs ` %s ) e. ( 0 [,) %s ) <-> ( ( abs ` %s ) e. RR /\\ 0 <_ ( abs ` %s ) /\\ ( abs ` %s ) < %s ) )' % (Y, R, Y, Y, Y, R))
    io = s([s([ay, s([yc], 'absge0d', '0 <_ ( abs ` %s )' % Y), ylt], '3jca', '( ( abs ` %s ) e. RR /\\ 0 <_ ( abs ` %s ) /\\ ( abs ` %s ) < %s )' % (Y, Y, Y, R)), eo], 'mpbird',
           '( abs ` %s ) e. ( 0 [,) %s )' % (Y, R))
    return s([s([yc, io], 'jca', '( %s e. CC /\\ ( abs ` %s ) e. ( 0 [,) %s ) )' % (Y, Y, R)), ep], 'mpbird', '%s e. %s' % (Y, SDf(A)))


def dvco(w, C, fr, Ew, DSw, a_step, da_step):
    """( C -> ( CC _D ( w e. U |-> Ew ) ) = ( w e. U |-> ( DSw x. ( 1 - 0 ) ) ) ) by dvmptco with the outer series FSf(A)"""
    A = fr['A']
    Aw = '( %s /\\ w e. %s )' % (C, U)
    Ay = '( %s /\\ y e. %s )' % (C, SDf(A))
    cp = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % C)
    b1 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % Aw), w.s([], '0cnd', '( %s -> 0 e. CC )' % Aw)], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % Aw)
    cc = fs_cc(w, Ay, fr, 'y', w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, SDf(A))))
    dd = w.s([w.s([], 'sumex', '%s e. _V' % DSf(A, 'y'))], 'a1i', '( %s -> %s e. _V )' % (Ay, DSf(A, 'y')))
    idy = w.s([], 'id', '( y = ( w - P ) -> y = ( w - P ) )')
    ce, _ = w.congr(ESf(A, 'y'), {'y': '( w - P )'}, 'y = ( w - P )', {'y': idy})
    cf, _ = w.congr(DSf(A, 'y'), {'y': '( w - P )'}, 'y = ( w - P )', {'y': idy})
    return w.s([cp, cp, a_step, b1, cc, dd, da_step, fr['dv'], ce, cf], 'dvmptco',
               '( %s -> ( CC _D ( w e. %s |-> %s ) ) = ( w e. %s |-> ( %s x. ( 1 - 0 ) ) ) )' % (C, U, Ew, U, DSw))


def gen_dvl():
    w = W('ef2dvl', 'The derivative of a function holomorphic near the square of half-side ` E ` about ` P ` is differentiable on the disc of radius ` E / 4 ` about ` P ` : there ` F ( P + X ) ` is a power series in ` X ` ( ~ ef2pse ), whose derivative ( ~ pserdv ) is again a power series with at least the same radius ( ~ dvradcnv ).')
    C = HYP0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    d = base(w, C, w.s([], 'id', '( %s -> %s )' % (C, C)))
    acf = w.s([], 'ef2psa', S['ef2psa'])
    Ce = '( %s /\\ e e. NN0 )' % C
    se = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ce, f))
    en = se([], 'simpr', 'e e. NN0')
    e1 = se([en, w.inst('peano2nn0')], 'syl', '( e + 1 ) e. NN0')
    a1v = se([se([e1], 'nn0cnd', '( e + 1 ) e. CC'), se([up(w, acf, Ce), e1], 'ffvelcdmd', '( %s ` ( e + 1 ) ) e. CC' % AC)], 'mulcld', '( ( e + 1 ) x. ( %s ` ( e + 1 ) ) ) e. CC' % AC)
    a1f = s([a1v], 'fmpttd', '%s : NN0 --> CC' % A1C)
    F0 = frame(w, C, AC, acf); F1 = frame(w, C, A1C, a1f)
    er = d['er']; erp = d['erp']
    def frac(k):
        q = s([erp, numst(w, C, k, 'RR+')], 'rpdivcld', '( E / %s ) e. RR+' % k)
        return q, s([q], 'rpred', '( E / %s ) e. RR' % k), s([q], 'rpcnd', '( E / %s ) e. CC' % k)
    e2p, e2r, e2c = frac('2'); e3p, e3r, e3c = frac('3'); e4p, e4r, e4c = frac('4')
    ab2 = s([e2r, s([e2p], 'rpge0d', '0 <_ ( E / 2 )')], 'absidd', '( abs ` ( E / 2 ) ) = ( E / 2 )')
    ab3 = s([e3r, s([e3p], 'rpge0d', '0 <_ ( E / 3 )')], 'absidd', '( abs ` ( E / 3 ) ) = ( E / 3 )')
    # convergence at E / 2 and the radius
    PE = tsub(S['ef2pse'], {'X': '( E / 2 )'})
    pa, pc_ = ante_of(PE)
    le2 = lin8(w, C, [ab2], '( abs ` ( E / 2 ) ) <_ ( E / 2 )', {'( abs ` ( E / 2 ) )': s([e2c], 'abscld', '( abs ` ( E / 2 ) ) e. RR'), 'E': er})
    cv2 = s([s([s([], 'id', HYP0), s([e2c, le2], 'jca', top_and(pa)[1])], 'jca', pa), w.inst('ef2pse')], 'syl', pc_)
    rel = s([w.s([], 'climrel', 'Rel ~~>')], 'a1i', 'Rel ~~>')
    G0 = PSGA(AC, 'x')
    dm2 = s([rel, cv2, w.inst('releldm')], 'syl2anc', 'seq 0 ( + , ( %s ` ( E / 2 ) ) ) e. dom ~~>' % G0)
    rl0 = w.s([F0['gq'], acf, F0['req'], e2c, dm2], 'radcnvle', '( %s -> ( abs ` ( E / 2 ) ) <_ %s )' % (C, RADf(AC)))
    # derived series converges at E / 3
    HX = '( n e. NN0 |-> ( ( ( n + 1 ) x. ( %s ` ( n + 1 ) ) ) x. ( ( E / 3 ) ^ n ) ) )' % AC
    lt3 = s([s([s([e3c], 'abscld', '( abs ` ( E / 3 ) ) e. RR')], 'rexrd', '( abs ` ( E / 3 ) ) e. RR*'),
             s([s([e2c], 'abscld', '( abs ` ( E / 2 ) ) e. RR')], 'rexrd', '( abs ` ( E / 2 ) ) e. RR*'), F0['rx'],
             lin8(w, C, [ab2, ab3, s([erp], 'rpgt0d', '0 < E')], '( abs ` ( E / 3 ) ) < ( abs ` ( E / 2 ) )',
                  {'( abs ` ( E / 3 ) )': s([e3c], 'abscld', '( abs ` ( E / 3 ) ) e. RR'), '( abs ` ( E / 2 ) )': s([e2c], 'abscld', '( abs ` ( E / 2 ) ) e. RR'), 'E': er}), rl0],
            'xrltletrd', '( abs ` ( E / 3 ) ) < %s' % RADf(AC))
    dvr = w.s([F0['gq'], F0['req'], w.s([], 'eqid', '%s = %s' % (HX, HX)), acf, e3c, lt3], 'dvradcnv', '( %s -> seq 0 ( + , %s ) e. dom ~~> )' % (C, HX))
    G1 = PSGA(A1C, 'x')
    V1 = '( n e. NN0 |-> ( ( %s ` n ) x. ( ( E / 3 ) ^ n ) ) )' % A1C
    g1v = fvmd(w, C, 'x', 'CC', '( n e. NN0 |-> ( ( %s ` n ) x. ( x ^ n ) ) )' % A1C, '( E / 3 )', e3c, w.s([w.s([], 'mptex', '%s e. _V' % V1)], 'a1i', '( %s -> %s e. _V )' % (C, V1)))
    Cn = '( %s /\\ n e. NN0 )' % C
    nn = w.s([], 'simpr', '( %s -> n e. NN0 )' % Cn)
    a1n = fvmd(w, Cn, 'e', 'NN0', '( ( e + 1 ) x. ( %s ` ( e + 1 ) ) )' % AC, 'n', nn, w.s([], 'ovexd', '( %s -> ( ( n + 1 ) x. ( %s ` ( n + 1 ) ) ) e. _V )' % (Cn, AC)))
    tm = w.s([a1n], 'oveq1d', '( %s -> ( ( %s ` n ) x. ( ( E / 3 ) ^ n ) ) = ( ( ( n + 1 ) x. ( %s ` ( n + 1 ) ) ) x. ( ( E / 3 ) ^ n ) ) )' % (Cn, A1C, AC))
    mq = s([tm], 'mpteq2dva', '%s = %s' % (V1, HX))
    gh = s([g1v, mq], 'eqtrd', '( %s ` ( E / 3 ) ) = %s' % (G1, HX))
    dv1 = s([dvr, s([s([gh], 'seqeq3d', 'seq 0 ( + , ( %s ` ( E / 3 ) ) ) = seq 0 ( + , %s )' % (G1, HX))], 'eleq1d',
                    '( seq 0 ( + , ( %s ` ( E / 3 ) ) ) e. dom ~~> <-> seq 0 ( + , %s ) e. dom ~~> )' % (G1, HX))], 'mpbird', 'seq 0 ( + , ( %s ` ( E / 3 ) ) ) e. dom ~~>' % G1)
    rl1 = w.s([F1['gq'], a1f, F1['req'], e3c, dv1], 'radcnvle', '( %s -> ( abs ` ( E / 3 ) ) <_ %s )' % (C, RADf(A1C)))
    # ---- the points of U ----
    Aw = '( %s /\\ w e. %s )' % (C, U)
    sw = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aw, f))
    pce = s([d['pc'], erp], 'jca', '( P e. CC /\\ E e. RR+ )')
    bm = sw([sw([up(w, pce, Aw), sw([], 'simpr', 'w e. %s' % U)], 'jca', '( ( P e. CC /\\ E e. RR+ ) /\\ w e. %s )' % U), w.inst('ef2blm')], 'syl',
            '( w e. CC /\\ ( abs ` ( w - P ) ) < ( E / 4 ) )')
    wc = sw([bm, w.inst('simpl')], 'syl', 'w e. CC'); wlt = sw([bm, w.inst('simpr')], 'syl', '( abs ` ( w - P ) ) < ( E / 4 )')
    XW = '( w - P )'
    pcw = up(w, d['pc'], Aw)
    xc = sw([wc, pcw], 'subcld', '%s e. CC' % XW)
    ax = sw([xc], 'abscld', '( abs ` %s ) e. RR' % XW)
    erw = up(w, er, Aw); e0w = sw([up(w, erp, Aw)], 'rpgt0d', '0 < E')
    ylt = {}
    for k, fr, ab, rl in (('2', F0, ab2, rl0), ('3', F1, ab3, rl1)):
        ak = sw([up(w, s([up(w, {'2': e2c, '3': e3c}[k], C)], 'abscld', '( abs ` ( E / %s ) ) e. RR' % k), Aw)], 'idi', '( abs ` ( E / %s ) ) e. RR' % k)
        l1 = lin8(w, Aw, [wlt, up(w, ab, Aw), e0w], '( abs ` %s ) < ( abs ` ( E / %s ) )' % (XW, k), {'( abs ` %s )' % XW: ax, '( abs ` ( E / %s ) )' % k: ak, 'E': erw})
        ylt[k] = sw([sw([ax], 'rexrd', '( abs ` %s ) e. RR*' % XW), sw([ak], 'rexrd', '( abs ` ( E / %s ) ) e. RR*' % k), up(w, fr['rx'], Aw), l1, up(w, rl, Aw)], 'xrltletrd',
                    '( abs ` %s ) < %s' % (XW, RADf(fr['A'])))
    in0 = in_disc(w, Aw, F0, XW, xc, ylt['2'])
    in1 = in_disc(w, Aw, F1, XW, xc, ylt['3'])
    # F ( w ) is the series at w - P
    PE = tsub(S['ef2pse'], {'X': XW})
    pa, pc_ = ante_of(PE)
    lw2 = lin8(w, Aw, [wlt, e0w], '( abs ` %s ) <_ ( E / 2 )' % XW, {'( abs ` %s )' % XW: ax, 'E': erw})
    cvw = sw([sw([up(w, w.s([], 'id', '( %s -> %s )' % (C, C)), Aw), sw([xc, lw2], 'jca', top_and(pa)[1])], 'jca', pa), w.inst('ef2pse')], 'syl', pc_)
    Ajw = '( %s /\\ j e. NN0 )' % Aw
    gfn = w.s([F0['gq'], up(w, acf, Aw), xc], 'psergf', '( %s -> ( %s ` %s ) : NN0 --> CC )' % (Aw, G0, XW))
    tj = w.s([up(w, gfn, Ajw), w.s([], 'simpr', '( %s -> j e. NN0 )' % Ajw)], 'ffvelcdmd', '( %s -> ( ( %s ` %s ) ` j ) e. CC )' % (Ajw, G0, XW))
    E0W = ESf(AC, XW)
    isc = sw([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )'), sw([], '0zd', '0 e. ZZ'), w.s([], 'eqidd', '( %s -> ( ( %s ` %s ) ` j ) = ( ( %s ` %s ) ` j ) )' % (Ajw, G0, XW, G0, XW)), tj, cvw],
             'isumclim', '%s = ( F ` ( P + %s ) )' % (E0W, XW))
    fwe = sw([sw([sw([pcw, wc], 'pncan3d', '( P + %s ) = w' % XW)], 'fveq2d', '( F ` ( P + %s ) ) = ( F ` w )' % XW), isc], 'eqtr2d', '( F ` w ) = %s' % E0W)
    # F restricted to U
    ud = s([s([pce, w.inst('ef2bsq')], 'syl', '%s C_ %s' % (U, SQE)), d['ssd']], 'sstrd', '%s C_ D' % U)
    fcn = s([d['hol'], w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )')
    ff = s([fcn, w.inst('cncff')], 'syl', 'F : D --> CC')
    dcc = s([fcn, w.inst('cncfrss')], 'syl', 'D C_ CC')
    ucc = s([ud, dcc], 'sstrd', '%s C_ CC' % U)
    fe = s([ff], 'feqmptd', 'F = ( w e. D |-> ( F ` w ) )')
    r1 = s([fe], 'reseq1d', '( F |` %s ) = ( ( w e. D |-> ( F ` w ) ) |` %s )' % (U, U))
    r2 = s([ud, w.inst('resmpt')], 'syl', '( ( w e. D |-> ( F ` w ) ) |` %s ) = ( w e. %s |-> ( F ` w ) )' % (U, U))
    r3 = s([fwe], 'mpteq2dva', '( w e. %s |-> ( F ` w ) ) = ( w e. %s |-> %s )' % (U, U, E0W))
    rr = s([s([r1, r2], 'eqtrd', '( F |` %s ) = ( w e. %s |-> ( F ` w ) )' % (U, U)), r3], 'eqtrd', '( F |` %s ) = ( w e. %s |-> %s )' % (U, U, E0W))
    # dvres with the interior of the open disc
    k_ = w.s([], 'eqid', '%s = %s' % (K, K))
    tk = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (K, K))], 'eqcomi', '%s = ( %s |`t CC )' % (K, K))
    dva = s([s([s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), ff], 'jca', '( CC C_ CC /\\ F : D --> CC )'), s([dcc, ucc], 'jca', '( D C_ CC /\\ %s C_ CC )' % U)], 'jca',
            '( ( CC C_ CC /\\ F : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) )' % U)
    dvr_ = s([dva, w.s([k_, tk], 'dvres', '( ( ( CC C_ CC /\\ F : D --> CC ) /\\ ( D C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( F |` %s ) ) = ( ( CC _D F ) |` ( ( int ` %s ) ` %s ) ) )' % (U, U, K, U))],
             'syl', '( CC _D ( F |` %s ) ) = ( ( CC _D F ) |` ( ( int ` %s ) ` %s ) )' % (U, K, U))
    met = s([w.s([], 'cnxmet', '( abs o. - ) e. ( *Met ` CC )')], 'a1i', '( abs o. - ) e. ( *Met ` CC )')
    kn = w.s([k_], 'cnfldtopn', '%s = ( MetOpen ` ( abs o. - ) )' % K)
    uo = s([met, d['pc'], s([e4p], 'rpxrd', '( E / 4 ) e. RR*'), w.s([kn], 'blopn', '( ( ( abs o. - ) e. ( *Met ` CC ) /\\ P e. CC /\\ ( E / 4 ) e. RR* ) -> %s e. %s )' % (U, K))], 'syl3anc', '%s e. %s' % (U, K))
    kt = s([w.s([k_], 'cnfldtop', '%s e. Top' % K)], 'a1i', '%s e. Top' % K)
    ints = s([kt, uo, w.inst('isopn3i')], 'syl2anc', '( ( int ` %s ) ` %s ) = %s' % (K, U, U))
    dres = s([dvr_, s([ints], 'reseq2d', '( ( CC _D F ) |` ( ( int ` %s ) ` %s ) ) = ( ( CC _D F ) |` %s )' % (K, U, U))], 'eqtrd', '( CC _D ( F |` %s ) ) = ( ( CC _D F ) |` %s )' % (U, U))
    # the inner derivative
    cp = s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', 'CC e. { RR , CC }')
    Cw = '( %s /\\ w e. CC )' % C
    scw = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Cw, f))
    wcw = scw([], 'simpr', 'w e. CC')
    pcc = up(w, d['pc'], Cw)
    dsub = s([cp, wcw, scw([], '1cnd', '1 e. CC'), s([cp], 'dvmptid', '( CC _D ( w e. CC |-> w ) ) = ( w e. CC |-> 1 )'), pcc, scw([], '0cnd', '0 e. CC'),
              s([cp, d['pc']], 'dvmptc', '( CC _D ( w e. CC |-> P ) ) = ( w e. CC |-> 0 )')], 'dvmptsub', '( CC _D ( w e. CC |-> ( w - P ) ) ) = ( w e. CC |-> ( 1 - 0 ) )')
    dres2 = s([cp, scw([wcw, pcc], 'subcld', '( w - P ) e. CC'), scw([scw([], '1cnd', '1 e. CC'), scw([], '0cnd', '0 e. CC')], 'subcld', '( 1 - 0 ) e. CC'), dsub, ucc, tk, k_, uo],
              'dvmptres', '( CC _D ( w e. %s |-> ( w - P ) ) ) = ( w e. %s |-> ( 1 - 0 ) )' % (U, U))
    co1 = dvco(w, C, F0, E0W, DSf(AC, XW), in0, dres2)
    DS0 = DSf(AC, XW)
    f1 = s([s([dres], 'eqcomd', '( ( CC _D F ) |` %s ) = ( CC _D ( F |` %s ) )' % (U, U)), s([rr], 'oveq2d', '( CC _D ( F |` %s ) ) = ( CC _D ( w e. %s |-> %s ) )' % (U, U, E0W))], 'eqtrd',
           '( ( CC _D F ) |` %s ) = ( CC _D ( w e. %s |-> %s ) )' % (U, U, E0W))
    f2 = s([f1, co1], 'eqtrd', '( ( CC _D F ) |` %s ) = ( w e. %s |-> ( %s x. ( 1 - 0 ) ) )' % (U, U, DS0))
    # the derived series at w - P
    E1W = ESf(A1C, XW)
    G1x = PSGA(A1C, 'x')
    pv = w.s([up(w, xc, Ajw), w.s([], 'simpr', '( %s -> j e. NN0 )' % Ajw), w.s([F1['gq']], 'pserval2', '( ( %s e. CC /\\ j e. NN0 ) -> ( ( %s ` %s ) ` j ) = ( ( %s ` j ) x. ( %s ^ j ) ) )' % (XW, G1x, XW, A1C, XW))],
             'syl2anc', '( %s -> ( ( %s ` %s ) ` j ) = ( ( %s ` j ) x. ( %s ^ j ) ) )' % (Ajw, G1x, XW, A1C, XW))
    aj = fvmd(w, Ajw, 'e', 'NN0', '( ( e + 1 ) x. ( %s ` ( e + 1 ) ) )' % AC, 'j', w.s([], 'simpr', '( %s -> j e. NN0 )' % Ajw),
              w.s([], 'ovexd', '( %s -> ( ( j + 1 ) x. ( %s ` ( j + 1 ) ) ) e. _V )' % (Ajw, AC)))
    TJ = lambda v: '( ( ( %s + 1 ) x. ( %s ` ( %s + 1 ) ) ) x. ( %s ^ %s ) )' % (v, AC, v, XW, v)
    tj2 = w.s([pv, w.s([aj], 'oveq1d', '( %s -> ( ( %s ` j ) x. ( %s ^ j ) ) = %s )' % (Ajw, A1C, XW, TJ('j')))], 'eqtrd', '( %s -> ( ( %s ` %s ) ` j ) = %s )' % (Ajw, G1x, XW, TJ('j')))
    se1 = sw([tj2], 'sumeq2dv', '%s = sum_ j e. NN0 %s' % (E1W, TJ('j')))
    idkj = w.s([], 'id', '( k = j -> k = j )')
    ckj, _ = w.congr(TJ('k'), {'k': 'j'}, 'k = j', {'k': idkj})
    cbs = sw([w.s([ckj], 'cbvsumv', '%s = sum_ j e. NN0 %s' % (DS0, TJ('j')))], 'a1i', '%s = sum_ j e. NN0 %s' % (DS0, TJ('j')))
    d0e1 = sw([cbs, se1], 'eqtr4d', '%s = %s' % (DS0, E1W))
    e1c = fs_cc(w, Aw, F1, XW, in1)
    d0c = sw([d0e1, e1c], 'eqeltrd', '%s e. CC' % DS0)
    m1 = sw([sw([w.s([], '1m0e1', '( 1 - 0 ) = 1')], 'a1i', '( 1 - 0 ) = 1')], 'oveq2d', '( %s x. ( 1 - 0 ) ) = ( %s x. 1 )' % (DS0, DS0))
    m2 = sw([sw([m1, sw([d0c], 'mulridd', '( %s x. 1 ) = %s' % (DS0, DS0))], 'eqtrd', '( %s x. ( 1 - 0 ) ) = %s' % (DS0, DS0)), d0e1], 'eqtrd', '( %s x. ( 1 - 0 ) ) = %s' % (DS0, E1W))
    mq2 = s([m2], 'mpteq2dva', '( w e. %s |-> ( %s x. ( 1 - 0 ) ) ) = ( w e. %s |-> %s )' % (U, DS0, U, E1W))
    dfu = s([f2, mq2], 'eqtrd', '( ( CC _D F ) |` %s ) = ( w e. %s |-> %s )' % (U, U, E1W))
    co2 = dvco(w, C, F1, E1W, DSf(A1C, XW), in1, dres2)
    DS1 = DSf(A1C, XW)
    d2 = s([s([dfu], 'oveq2d', '( CC _D ( ( CC _D F ) |` %s ) ) = ( CC _D ( w e. %s |-> %s ) )' % (U, U, E1W)), co2], 'eqtrd',
           '( CC _D ( ( CC _D F ) |` %s ) ) = ( w e. %s |-> ( %s x. ( 1 - 0 ) ) )' % (U, U, DS1))
    V2 = '( %s x. ( 1 - 0 ) )' % DS1
    dmm = s([w.s([w.s([w.s([], 'ovex', '%s e. _V' % V2)], 'a1i', '( w e. %s -> %s e. _V )' % (U, V2))], 'rgen', 'A. w e. %s %s e. _V' % (U, V2))], 'a1i', 'A. w e. %s %s e. _V' % (U, V2))
    dm1 = s([dmm, w.inst('dmmptg')], 'syl', 'dom ( w e. %s |-> %s ) = %s' % (U, V2, U))
    dd2 = s([s([d2], 'dmeqd', 'dom ( CC _D ( ( CC _D F ) |` %s ) ) = dom ( w e. %s |-> %s )' % (U, U, V2)), dm1], 'eqtrd', 'dom ( CC _D ( ( CC _D F ) |` %s ) ) = %s' % (U, U))
    w.qed([s([dd2], 'eqcomd', '%s = dom ( CC _D ( ( CC _D F ) |` %s ) )' % (U, U))], 'eqimssd', S['ef2dvl'])
    return run8(w)


def gen_dvh():
    w = W('ef2dvh', 'The derivative of a holomorphic function on an open set is holomorphic there (Mathlib ` AnalyticOnNhd.deriv ` ; C1 has no counterpart): locally by ~ ef2dvl , glued by ~ holloc .')
    C, GC = ante_of(S['ef2dvh'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    hc = s([], 'id', C)
    fcn = s([hc, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )')
    dcc = s([fcn, w.inst('cncfrss')], 'syl', 'D C_ CC')
    hf = s([hc, w.inst('holf')], 'syl', '( CC _D F ) : D --> CC')
    dop = s([hc, w.inst('holopn')], 'syl', 'D e. %s' % K)
    Cy = '( %s /\\ y e. D )' % C
    sy = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Cy, f))
    yd = sy([], 'simpr', 'y e. D')
    yc = sy([up(w, dcc, Cy), yd], 'sseldd', 'y e. CC')
    SQy = lambda e: SQ('y', e)
    sqo = sy([up(w, dop, Cy), yd, yc, w.inst('ef2sqo')], 'syl3anc', 'E. e e. RR+ %s C_ D' % SQy('e'))
    Ce = '( ( %s /\\ e e. RR+ ) /\\ %s C_ D )' % (Cy, SQy('e'))
    se = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ce, f))
    ycc = up(w, yc, Ce); erp = se([], 'simplr', 'e e. RR+'); sqd = se([], 'simpr', '%s C_ D' % SQy('e'))
    UB = BL('y', '( e / 4 )')
    e4 = se([erp, numst(w, Ce, '4', 'RR+')], 'rpdivcld', '( e / 4 ) e. RR+')
    met = se([w.s([], 'cnxmet', '( abs o. - ) e. ( *Met ` CC )')], 'a1i', '( abs o. - ) e. ( *Met ` CC )')
    k_ = w.s([], 'eqid', '%s = %s' % (K, K))
    kn = w.s([k_], 'cnfldtopn', '%s = ( MetOpen ` ( abs o. - ) )' % K)
    uo = se([met, ycc, se([e4], 'rpxrd', '( e / 4 ) e. RR*'), w.s([kn], 'blopn', '( ( ( abs o. - ) e. ( *Met ` CC ) /\\ y e. CC /\\ ( e / 4 ) e. RR* ) -> %s e. %s )' % (UB, K))],
            'syl3anc', '%s e. %s' % (UB, K))
    yu = se([met, ycc, e4, w.inst('blcntr')], 'syl3anc', 'y e. %s' % UB)
    ye = se([ycc, erp], 'jca', '( y e. CC /\\ e e. RR+ )')
    bs = se([ye, w.inst('ef2bsq')], 'syl', '%s C_ %s' % (UB, SQy('e')))
    ud = se([bs, sqd], 'sstrd', '%s C_ D' % UB)
    DL_ = tsub(S['ef2dvl'], {'P': 'y', 'E': 'e'})
    dla, dlc = ante_of(DL_)
    dl = se([se([up(w, hc, Ce), se([ycc, erp, sqd], '3jca', top_and(dla)[1])], 'jca', dla), w.inst('ef2dvl')], 'syl', dlc)
    BODY = lambda u: '( y e. %s /\\ %s C_ D /\\ %s C_ dom ( CC _D ( ( CC _D F ) |` %s ) ) )' % (u, u, u, u)
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (UB, UB))
    cs, _ = w.wcongr(BODY('u'), {'u': UB}, 'u = %s' % UB, {'u': idu})
    ex = se([uo, se([yu, ud, dl], '3jca', BODY(UB)), w.s([cs], 'rspcev', '( ( %s e. %s /\\ %s ) -> E. u e. %s %s )' % (UB, K, BODY(UB), K, BODY('u')))], 'syl2anc',
            'E. u e. %s %s' % (K, BODY('u')))
    EX = 'E. u e. %s %s' % (K, BODY('u'))
    ey = sy([sqo, w.s([w.s([ex], 'ex', '( ( %s /\\ e e. RR+ ) -> ( %s C_ D -> %s ) )' % (Cy, SQy('e'), EX))], 'rexlimdva', '( %s -> ( E. e e. RR+ %s C_ D -> %s ) )' % (Cy, SQy('e'), EX))],
            'mpd', EX)
    al = w.s([ey], 'ralrimiva', '( %s -> A. y e. D %s )' % (C, EX))
    HL = tsub(stmt('holloc'), {'G': '( CC _D F )'})
    hla, hlc = ante_of(HL)
    w.qed([s([s([hf, dcc], 'jca', top_and(hla)[0]), al], 'jca', hla), w.inst('holloc')], 'syl', S['ef2dvh'])
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2dvl', 'ef2dvh']:
        {'ef2dvl': gen_dvl, 'ef2dvh': gen_dvh}[g]()
