"""Sortie Z6b, section 5: the strip bounds (z6gstrip, z6cvxb, z6lstrip).
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_m.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp, lift
from z6a_e3 import conjs, build, unpack, c_
import lin
from lin import linarith, nlinarith
import num

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def inst_all(w, a, allstep, x, X, body, T, tmem):
    """( a -> body[T/x] ) from allstep: ( a -> A. x e. X body ) and tmem: ( a -> T e. X )"""
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, T, x, T))
    sb, new = w.wcongr(body, {x: T}, '%s = %s' % (x, T), {x: idk})
    rs = w.s([sb], 'rspcv', '( %s e. %s -> ( A. %s e. %s %s -> %s ) )' % (T, X, x, X, body, new))
    return w.s([tmem, allstep, rs], 'sylc', '( %s -> %s )' % (a, new)), new


def omgfacts(w, a, nn):
    """( a -> OMG e. RR ) , ( a -> 1 <_ OMG )"""
    st = mkst(w, a)
    PS = '{ p e. Prime | p || N }'
    hc = st([st([nn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PS), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % PS)
    two = c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR')
    rr = st([two, hc], 'reexpcld', '%s e. RR' % OMGN)
    ge = st([two, hc, c_(w, a, w.s([], '1le2', '1 <_ 2'), '1 <_ 2'), w.inst('expge1')], 'syl3anc', '1 <_ %s' % OMGN)
    return rr, ge


def z6gstrip():
    w = W('z6gstrip', 'Gamma on ` -u 99/100 <_ Re W <_ 3 ` , ` | Im W | >_ 1 ` : ` | _G ( W ) | <_ 1632 2 ^ ( - | Im W | / 2 ) ` ; right of '
          '` Re = 1/100 ` this is ~ z6gam1632 , left of it one step of the functional equation (~ z6mgdiv , ` | W | >_ 1 ` ).')
    a = ante('z6gstrip'); f = unpack(w, a); st = mkst(w, a)
    wc = f['W e. CC']; lo = f['-u ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` W )']; hi = f['( Re ` W ) <_ 3']; y1 = f['1 <_ ( abs ` ( Im ` W ) )']
    rw = st([wc], 'recld', '( Re ` W ) e. RR')
    c100 = c_(w, a, num.real(w, '( 1 / ; ; 1 0 0 )'), '( 1 / ; ; 1 0 0 ) e. RR')
    dis = st([c100, rw, w.inst('lelttric')], 'syl2anc', '( ( 1 / ; ; 1 0 0 ) <_ ( Re ` W ) \\/ ( Re ` W ) < ( 1 / ; ; 1 0 0 ) )')
    GB = '( ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( ; ; ; 1 6 3 2 x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) ) )'
    gall = c_(w, a, w.s([], 'z6gam1632', STATEMENTS['z6gam1632']), STATEMENTS['z6gam1632'])
    TG = split_imp(STATEMENTS['z6gstrip'])[1]
    # case 1
    c1 = '( %s /\\ ( 1 / ; ; 1 0 0 ) <_ ( Re ` W ) )' % a; s1 = mkst(w, c1)
    g1, new1 = inst_all(w, c1, lift(w, gall, c1), 'd', 'CC', GB, 'W', lift(w, wc, c1))
    r1 = s1([s1([s1([], 'simpr', '( 1 / ; ; 1 0 0 ) <_ ( Re ` W )'), lift(w, hi, c1)], 'jca', '( ( 1 / ; ; 1 0 0 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 3 )'), g1], 'mpd', TG)
    # case 2
    c2 = '( %s /\\ ( Re ` W ) < ( 1 / ; ; 1 0 0 ) )' % a; s2 = mkst(w, c2)
    wc2 = lift(w, wc, c2)
    imc = s2([s2([wc2], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')
    ay = s2([imc], 'abscld', '( abs ` ( Im ` W ) ) e. RR')
    gt0 = linarith(w, c2, [lift(w, y1, c2)], '0 < ( abs ` ( Im ` W ) )', leaves={'( abs ` ( Im ` W ) )': ay})
    ine = s2([gt0, s2([imc, w.inst('absgt0')], 'syl', '( ( Im ` W ) =/= 0 <-> 0 < ( abs ` ( Im ` W ) ) )')], 'mpbird', '( Im ` W ) =/= 0')
    wdg = s2([s2([wc2, s2([ine], 'olcd', '( -. ( Re ` W ) e. ZZ \\/ ( Im ` W ) =/= 0 )')], 'jca', '( W e. CC /\\ ( -. ( Re ` W ) e. ZZ \\/ ( Im ` W ) =/= 0 ) )'),
              w.inst('z6mndg')], 'syl', 'W e. %s' % DG)
    aw = s2([wc2], 'abscld', '( abs ` W ) e. RR')
    w1 = linarith(w, c2, [lift(w, y1, c2), s2([wc2, w.inst('absimle')], 'syl', '( abs ` ( Im ` W ) ) <_ ( abs ` W )')], '1 <_ ( abs ` W )',
                  leaves={'( abs ` ( Im ` W ) )': ay, '( abs ` W )': aw})
    gd = s2([wdg, s2([c_(w, c2, w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), w1], 'jca', '( 1 e. RR+ /\\ 1 <_ ( abs ` W ) )'), w.inst('z6mgdiv')], 'syl2anc',
            '( abs ` ( _G ` W ) ) <_ ( ( abs ` ( _G ` ( W + 1 ) ) ) / 1 )')
    W1 = '( W + 1 )'
    one = c_(w, c2, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    w1c = s2([wc2, one], 'addcld', '%s e. CC' % W1)
    re1 = s2([wc2, w.inst('z6mre1')], 'syl', '( ( Re ` %s ) = ( ( Re ` W ) + 1 ) /\\ ( Im ` %s ) = ( Im ` W ) )' % (W1, W1))
    rw1 = s2([re1], 'simpld', '( Re ` %s ) = ( ( Re ` W ) + 1 )' % W1); iw1 = s2([re1], 'simprd', '( Im ` %s ) = ( Im ` W )' % W1)
    rwr = lift(w, rw, c2)
    lo1 = s2([linarith(w, c2, [lift(w, lo, c2)], '( 1 / ; ; 1 0 0 ) <_ ( ( Re ` W ) + 1 )', leaves={'( Re ` W )': rwr}), rw1], 'breqtrrd', '( 1 / ; ; 1 0 0 ) <_ ( Re ` %s )' % W1)
    hi1 = s2([rw1, linarith(w, c2, [s2([], 'simpr', '( Re ` W ) < ( 1 / ; ; 1 0 0 )')], '( ( Re ` W ) + 1 ) <_ 3', leaves={'( Re ` W )': rwr})], 'eqbrtrd',
             '( Re ` %s ) <_ 3' % W1)
    g2, new2 = inst_all(w, c2, lift(w, gall, c2), 'd', 'CC', GB, W1, w1c)
    b2 = s2([s2([lo1, hi1], 'jca', '( ( 1 / ; ; 1 0 0 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (W1, W1)), g2], 'mpd', split_imp(new2)[1])
    E2W1 = E2('( abs ` ( Im ` %s ) )' % W1); E2W = E2('( abs ` ( Im ` W ) )')
    ee = s2([s2([s2([s2([s2([iw1], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` W ) )' % W1)], 'oveq1d',
                        '( ( abs ` ( Im ` %s ) ) / 2 ) = ( ( abs ` ( Im ` W ) ) / 2 )' % W1)], 'negeqd',
                  '-u ( ( abs ` ( Im ` %s ) ) / 2 ) = -u ( ( abs ` ( Im ` W ) ) / 2 )' % W1)], 'oveq2d', '%s = %s' % (E2W1, E2W))], 'oveq2d',
            '( ; ; ; 1 6 3 2 x. %s ) = ( ; ; ; 1 6 3 2 x. %s )' % (E2W1, E2W))
    b3 = s2([b2, ee], 'breqtrd', '( abs ` ( _G ` %s ) ) <_ ( ; ; ; 1 6 3 2 x. %s )' % (W1, E2W))
    # | _G ( W + 1 ) | e. CC for div1d: W + 1 e. DG (Re > 0)
    rpos = s2([linarith(w, c2, [lift(w, lo, c2)], '0 < ( ( Re ` W ) + 1 )', leaves={'( Re ` W )': rwr}), rw1], 'breqtrrd', '0 < ( Re ` %s )' % W1)
    hp = s2([s2([w1c, rpos], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W1, W1)), s2([c_(w, c2, w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl',
                                                                             '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (W1, HPZ, W1, W1))], 'mpbird', '%s e. %s' % (W1, HPZ))
    # HPZ C_ DG: Re > 0 is not a nonpositive integer; use z6rdg ( -u 1 < Re , =/= 0 )
    rw1r = s2([w1c], 'recld', '( Re ` %s ) e. RR' % W1)
    m1 = linarith(w, c2, [rpos], '-u 1 < ( Re ` %s )' % W1, leaves={'( Re ` %s )' % W1: rw1r})
    # W + 1 =/= 0 : Re ( W + 1 ) > 0
    A0 = '( %s /\\ %s = 0 )' % (c2, W1); t0 = mkst(w, A0)
    r00 = t0([t0([t0([], 'simpr', '%s = 0' % W1)], 'fveq2d', '( Re ` %s ) = ( Re ` 0 )' % W1), c_(w, A0, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')], 'eqtrd',
             '( Re ` %s ) = 0' % W1)
    rne = s2([rpos], 'gt0ne0d', '( Re ` %s ) =/= 0' % W1)
    nw = w.s([r00, lift(w, s2([rne], 'neneqd', '-. ( Re ` %s ) = 0' % W1), A0)], 'pm2.65da', '( %s -> -. %s = 0 )' % (c2, W1))
    w1n = s2([nw], 'neqned', '%s =/= 0' % W1)
    wdg1 = s2([s2([w1c, s2([m1, w1n], 'jca', '( -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (W1, W1))], 'jca', '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ %s =/= 0 ) )' % (W1, W1, W1)),
               w.inst('z6rdg')], 'syl', '%s e. %s' % (W1, DG))
    gw1c = s2([wdg1, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % W1)
    d1 = s2([s2([gw1c], 'abscld', '( abs ` ( _G ` %s ) ) e. RR' % W1)], 'recnd', '( abs ` ( _G ` %s ) ) e. CC' % W1)
    gd2 = s2([gd, s2([d1], 'div1d', '( ( abs ` ( _G ` %s ) ) / 1 ) = ( abs ` ( _G ` %s ) )' % (W1, W1))], 'breqtrd', '( abs ` ( _G ` W ) ) <_ ( abs ` ( _G ` %s ) )' % W1)
    gwr = s2([s2([wdg, w.inst('gamcl')], 'syl', '( _G ` W ) e. CC')], 'abscld', '( abs ` ( _G ` W ) ) e. RR')
    g1r = s2([gw1c], 'abscld', '( abs ` ( _G ` %s ) ) e. RR' % W1)
    e2r = s2([c_(w, c2, num.real(w, '; ; ; 1 6 3 2'), '; ; ; 1 6 3 2 e. RR'),
              s2([c_(w, c2, w.s([], '2re', '2 e. RR'), '2 e. RR'), s2([s2([ay], 'rehalfcld', '( ( abs ` ( Im ` W ) ) / 2 ) e. RR')], 'renegcld',
                  '-u ( ( abs ` ( Im ` W ) ) / 2 ) e. RR')], 'rpcxpcld' if False else 'recxpcld' if False else 'x', 'x') if False else
              s2([s2([c_(w, c2, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), s2([s2([ay], 'rehalfcld', '( ( abs ` ( Im ` W ) ) / 2 ) e. RR')], 'renegcld',
                  '-u ( ( abs ` ( Im ` W ) ) / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E2W)], 'rpred', '%s e. RR' % E2W)], 'remulcld', '( ; ; ; 1 6 3 2 x. %s ) e. RR' % E2W)
    r2 = s2([gwr, g1r, e2r, gd2, b3], 'letrd', TG)
    w.qed([r1, r2, dis], 'mpjaodan', STATEMENTS['z6gstrip'])
    return w


def z6cvxb():
    w = W('z6cvxb', 'Lean ` norm_LFunction_strip_le ` (convexity case), generic in the value: below ` CVXB ( W ) ` with ` Re W >_ 0 ` , '
          '` | W - 1 | >_ 1 ` is below ` 400000 2 ^ omega ( N ) ( N ( | Im W | + 3 ) ) ^ 2 ` (the exponent is at most 1, ~ loglet ).')
    a = ante('z6cvxb'); f = unpack(w, a); st = mkst(w, a)
    nn = f['N e. NN']; wc = f['W e. CC']; re0 = f['0 <_ ( Re ` W )']; d1 = f['1 <_ ( abs ` ( W - 1 ) )']; vr = f['V e. RR']; vle = f['V <_ %s' % CVXB('W')]
    nr = st([nn], 'nnred', 'N e. RR'); n1 = st([nn], 'nnge1d', '1 <_ N'); n0 = st([st([nn], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N')
    Y = '( abs ` ( Im ` W ) )'
    imc = st([st([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')
    yr = st([imc], 'abscld', '%s e. RR' % Y); y0 = st([imc], 'absge0d', '0 <_ %s' % Y)
    Y2 = '( %s + 2 )' % Y; Y3 = '( %s + 3 )' % Y
    y2r = st([yr, c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR')], 'readdcld', '%s e. RR' % Y2)
    y3r = st([yr, c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'readdcld', '%s e. RR' % Y3)
    Lv = {Y: yr, 'N': nr, '( Re ` W )': st([wc], 'recld', '( Re ` W ) e. RR')}
    y20 = linarith(w, a, [y0], '0 <_ %s' % Y2, leaves=Lv)
    y30 = linarith(w, a, [y0], '0 <_ %s' % Y3, leaves=Lv)
    B = '( N x. %s )' % Y2; Cc = '( N x. %s )' % Y3
    br = st([nr, y2r], 'remulcld', '%s e. RR' % B); cr = st([nr, y3r], 'remulcld', '%s e. RR' % Cc)
    Lv.update({B: br, Cc: cr})
    bl = st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), nr, y2r, y20, n1], 'lemul1ad', '( 1 x. %s ) <_ %s' % (Y2, B))
    b1 = linarith(w, a, [bl, y0], '1 < %s' % B, leaves=Lv)
    b0 = linarith(w, a, [bl, y0], '0 <_ %s' % B, leaves=Lv)
    cl_ = st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), nr, y3r, y30, n1], 'lemul1ad', '( 1 x. %s ) <_ %s' % (Y3, Cc))
    c1 = linarith(w, a, [cl_, y0], '1 <_ %s' % Cc, leaves=Lv)
    bc = st([y2r, y3r, nr, n0, linarith(w, a, [], '%s <_ %s' % (Y2, Y3), leaves=Lv)], 'lemul2ad', '%s <_ %s' % (B, Cc))
    EX = 'if ( 1 <_ ( Re ` W ) , 0 , ( ( 1 - ( Re ` W ) ) / 2 ) )'
    rwr = Lv['( Re ` W )']
    hx = st([st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), rwr], 'resubcld', '( 1 - ( Re ` W ) ) e. RR')], 'rehalfcld', '( ( 1 - ( Re ` W ) ) / 2 ) e. RR')
    exr = st([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), hx], 'ifcld', '%s e. RR' % EX)
    # EX <_ 1
    k1 = '( %s /\\ 1 <_ ( Re ` W ) )' % a; t1 = mkst(w, k1)
    e1 = t1([t1([t1([], 'simpr', '1 <_ ( Re ` W )')], 'iftrued', '%s = 0' % EX), c_(w, k1, w.s([], '0le1', '0 <_ 1'), '0 <_ 1')], 'eqbrtrd', '%s <_ 1' % EX)
    k2 = '( %s /\\ ( Re ` W ) < 1 )' % a; t2 = mkst(w, k2)
    rwr2 = lift(w, rwr, k2)
    nl = t2([t2([], 'simpr', '( Re ` W ) < 1'), t2([rwr2, c_(w, k2, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'ltnled', '( ( Re ` W ) < 1 <-> -. 1 <_ ( Re ` W ) )')], 'mpbid',
            '-. 1 <_ ( Re ` W )')
    e2 = t2([t2([nl], 'iffalsed', '%s = ( ( 1 - ( Re ` W ) ) / 2 )' % EX),
             linarith(w, k2, [lift(w, re0, k2)], '( ( 1 - ( Re ` W ) ) / 2 ) <_ 1', leaves={'( Re ` W )': rwr2})], 'eqbrtrd', '%s <_ 1' % EX)
    exl = st([e1, e2, st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), rwr, w.inst('lelttric')], 'syl2anc', '( 1 <_ ( Re ` W ) \\/ ( Re ` W ) < 1 )')], 'mpjaodan', '%s <_ 1' % EX)
    BP = '( %s ^c %s )' % (B, EX)
    cx = st([st([st([br, b1], 'jca', '( %s e. RR /\\ 1 < %s )' % (B, B)), st([exr, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'jca', '( %s e. RR /\\ 1 e. RR )' % EX)],
                'jca', '( ( %s e. RR /\\ 1 < %s ) /\\ ( %s e. RR /\\ 1 e. RR ) )' % (B, B, EX)), w.inst('cxple')], 'syl',
            '( %s <_ 1 <-> %s <_ ( %s ^c 1 ) )' % (EX, BP, B))
    bp1 = st([st([exl, cx], 'mpbid', '%s <_ ( %s ^c 1 )' % (BP, B)), st([st([br], 'recnd', '%s e. CC' % B), w.inst('cxp1')], 'syl', '( %s ^c 1 ) = %s' % (B, B))], 'breqtrd',
             '%s <_ %s' % (BP, B))
    bprr = st([br, b0, exr], 'recxpcld', '%s e. RR' % BP)
    bpc = st([bprr, br, cr, bp1, bc], 'letrd', '%s <_ %s' % (BP, Cc))
    bp0 = st([br, b0, exr, w.inst('cxpge0')], 'syl3anc', '0 <_ %s' % BP)
    LG = '( log ` %s )' % Cc
    crp = st([cr, linarith(w, a, [c1], '0 < %s' % Cc, leaves=Lv)], 'elrpd', '%s e. RR+' % Cc)
    lgr = st([crp], 'relogcld', '%s e. RR' % LG)
    lgle = st([cr, c1, w.inst('loglet')], 'syl2anc', '%s <_ %s' % (LG, Cc))
    lg0 = st([cr, c1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % LG)
    pr = st([bprr, cr, lgr, cr, bp0, lg0, bpc, lgle], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (BP, LG, Cc, Cc))
    AW = '( abs ` ( W - 1 ) )'
    awr = st([st([wc, c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')], 'subcld', '( W - 1 ) e. CC')], 'abscld', '%s e. RR' % AW)
    awp = linarith(w, a, [d1], '0 < %s' % AW, leaves={AW: awr})
    lrb = st([st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), c_(w, a, w.s([], '0lt1', '0 < 1'), '0 < 1')], 'jca', '( 1 e. RR /\\ 0 < 1 )'),
              st([awr, awp], 'jca', '( %s e. RR /\\ 0 < %s )' % (AW, AW)), w.inst('lerec')], 'syl2anc', '( 1 <_ %s <-> ( 1 / %s ) <_ ( 1 / 1 ) )' % (AW, AW))
    rc1 = st([st([d1, lrb], 'mpbid', '( 1 / %s ) <_ ( 1 / 1 )' % AW), c_(w, a, w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')], 'breqtrd', '( 1 / %s ) <_ 1' % AW)
    Z = '( ( %s x. %s ) + ( 1 / %s ) )' % (BP, LG, AW)
    CC2 = '( %s x. %s )' % (Cc, Cc)
    ccr = st([cr, cr], 'remulcld', '%s e. RR' % CC2)
    ivr = st([awr, st([awp], 'gt0ne0d', '%s =/= 0' % AW)], 'rereccld', '( 1 / %s ) e. RR' % AW)
    zr = st([st([bprr, lgr], 'remulcld', '( %s x. %s ) e. RR' % (BP, LG)), ivr], 'readdcld', '%s e. RR' % Z)
    zle = st([pr, rc1], 'le2addd', '%s <_ ( %s + 1 )' % (Z, CC2))
    rr, ge1 = omgfacts(w, a, nn)
    K = '( ; ; ; ; ; 2 0 0 0 0 0 x. %s )' % OMGN
    kr = st([c_(w, a, num.real(w, '; ; ; ; ; 2 0 0 0 0 0'), '; ; ; ; ; 2 0 0 0 0 0 e. RR'), rr], 'remulcld', '%s e. RR' % K)
    k0 = linarith(w, a, [ge1], '0 <_ %s' % K, leaves={OMGN: rr})
    c2r = st([ccr, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'readdcld', '( %s + 1 ) e. RR' % CC2)
    kz = st([zr, c2r, kr, k0, zle], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s + 1 ) )' % (K, Z, K, CC2))
    c11 = st([c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), cr, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), cr,
              c_(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), c_(w, a, w.s([], '0le1', '0 <_ 1'), '0 <_ 1'), c1, c1], 'lemul12ad', '( 1 x. 1 ) <_ %s' % CC2)
    kzr = st([kr, zr], 'remulcld', '( %s x. %s ) e. RR' % (K, Z))
    k2r = st([kr, c2r], 'remulcld', '( %s x. ( %s + 1 ) ) e. RR' % (K, CC2))
    DD = '( %s + %s )' % (CC2, CC2)
    ddr = st([ccr, ccr], 'readdcld', '%s e. RR' % DD)
    k3r = st([kr, ddr], 'remulcld', '( %s x. %s ) e. RR' % (K, DD))
    le3 = st([c2r, ddr, kr, k0, linarith(w, a, [c11], '( %s + 1 ) <_ %s' % (CC2, DD), leaves={CC2: ccr})], 'lemul2ad',
             '( %s x. ( %s + 1 ) ) <_ ( %s x. %s )' % (K, CC2, K, DD))
    vr_ = st([vr, kzr, k2r, vle, kz], 'letrd', 'V <_ ( %s x. ( %s + 1 ) )' % (K, CC2))
    v3 = st([vr, k2r, k3r, vr_, le3], 'letrd', 'V <_ ( %s x. %s )' % (K, DD))
    GOAL = '( ( ; ; ; ; ; 4 0 0 0 0 0 x. %s ) x. %s )' % (OMGN, CC2)
    ccc = st([ccr], 'recnd', '%s e. CC' % CC2); kc = st([kr], 'recnd', '%s e. CC' % K)
    two = c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC')
    q1 = st([st([ccc], '2timesd', '( 2 x. %s ) = %s' % (CC2, DD))], 'eqcomd', '%s = ( 2 x. %s )' % (DD, CC2))
    q2 = st([st([kc, two, ccc], 'mulassd', '( ( %s x. 2 ) x. %s ) = ( %s x. ( 2 x. %s ) )' % (K, CC2, K, CC2))], 'eqcomd',
            '( %s x. ( 2 x. %s ) ) = ( ( %s x. 2 ) x. %s )' % (K, CC2, K, CC2))
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    q3 = lin.lineq(w, a, '( %s x. 2 )' % K, K4, leaves={OMGN: rr}, atoms=[OMGN])
    eqg = st([st([st([q1], 'oveq2d', '( %s x. %s ) = ( %s x. ( 2 x. %s ) )' % (K, DD, K, CC2)), q2], 'eqtrd', '( %s x. %s ) = ( ( %s x. 2 ) x. %s )' % (K, DD, K, CC2)),
              st([q3], 'oveq1d', '( ( %s x. 2 ) x. %s ) = %s' % (K, CC2, GOAL))], 'eqtrd', '( %s x. %s ) = %s' % (K, DD, GOAL))
    fin = st([v3, eqg], 'breqtrd', 'V <_ %s' % GOAL)
    sq = st([st([cr], 'recnd', '%s e. CC' % Cc)], 'sqvald', '( %s ^ 2 ) = %s' % (Cc, CC2))
    w.qed([fin, st([sq], 'oveq2d', '( ( ; ; ; ; ; 4 0 0 0 0 0 x. %s ) x. ( %s ^ 2 ) ) = %s' % (OMGN, Cc, GOAL))], 'breqtrrd', STATEMENTS['z6cvxb'])
    return w


def z6lstrip():
    w = W('z6lstrip', 'Lean ` norm_LFunction_strip_le ` : ` | E ( W ) / ( W - 1 ) | <_ 400000 2 ^ omega ( N ) ( N ( | Im W | + 3 ) ) ^ 2 ` on '
          '` Re W >_ 1/100 ` , ` | Im W | >_ 1 ` : the convexity bound ` CVXH ` for ` Re W <_ 2 ` (~ z6cvxb ), the Dirichlet series ` DSER ` and '
          '~ dserbnd above.')
    a = ante('z6lstrip'); f = unpack(w, a); st = mkst(w, a)
    nn = f['N e. NN']; cf = f['C : NN --> CC']; cb = f[CB]; dser = f[DSER]; cvxh = f[CVXH]
    wc = f['W e. CC']; lo = f['( 1 / ; ; 1 0 0 ) <_ ( Re ` W )']; y1 = f['1 <_ ( abs ` ( Im ` W ) )']
    rw = st([wc], 'recld', '( Re ` W ) e. RR')
    one = c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    wm1 = st([wc, one], 'subcld', '( W - 1 ) e. CC')
    imc = st([st([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')
    ay = st([imc], 'abscld', '( abs ` ( Im ` W ) ) e. RR')
    iw = st([st([wc, one], 'imsubd', '( Im ` ( W - 1 ) ) = ( ( Im ` W ) - ( Im ` 1 ) )'),
             st([c_(w, a, w.s([], 'im1', '( Im ` 1 ) = 0'), '( Im ` 1 ) = 0')], 'oveq2d', '( ( Im ` W ) - ( Im ` 1 ) ) = ( ( Im ` W ) - 0 )')], 'eqtrd',
            '( Im ` ( W - 1 ) ) = ( ( Im ` W ) - 0 )')
    iw2 = st([iw, st([imc], 'subid1d', '( ( Im ` W ) - 0 ) = ( Im ` W )')], 'eqtrd', '( Im ` ( W - 1 ) ) = ( Im ` W )')
    ai = st([st([wm1, w.inst('absimle')], 'syl', '( abs ` ( Im ` ( W - 1 ) ) ) <_ ( abs ` ( W - 1 ) )'), st([iw2], 'fveq2d', '( abs ` ( Im ` ( W - 1 ) ) ) = ( abs ` ( Im ` W ) )')],
            'eqbrtrrd', '( abs ` ( Im ` W ) ) <_ ( abs ` ( W - 1 ) )')
    AW = '( abs ` ( W - 1 ) )'
    awr = st([wm1], 'abscld', '%s e. RR' % AW)
    d1 = linarith(w, a, [y1, ai], '1 <_ %s' % AW, leaves={AW: awr, '( abs ` ( Im ` W ) )': ay})
    w10 = st([linarith(w, a, [d1], '0 < %s' % AW, leaves={AW: awr}), st([wm1, w.inst('absgt0')], 'syl', '( ( W - 1 ) =/= 0 <-> 0 < %s )' % AW)], 'mpbird', '( W - 1 ) =/= 0')
    wne1 = st([wc, one, w10], 'subne0ad', 'W =/= 1')
    whp = st([st([wc, linarith(w, a, [lo], '0 < ( Re ` W )', leaves={'( Re ` W )': rw})], 'jca', '( W e. CC /\\ 0 < ( Re ` W ) )'),
              st([c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( W e. %s <-> ( W e. CC /\\ 0 < ( Re ` W ) ) )' % HPZ)], 'mpbird', 'W e. %s' % HPZ)
    TG = split_imp(STATEMENTS['z6lstrip'])[1]
    Q = '( ( E ` W ) / ( W - 1 ) )'
    # case Re W <_ 2
    c1 = '( %s /\\ ( Re ` W ) <_ 2 )' % a; s1 = mkst(w, c1)
    BODY = CVXH[len('A. s e. %s ' % HPZ):]
    g, new = inst_all(w, c1, lift(w, cvxh, c1), 's', HPZ, BODY, 'W', lift(w, whp, c1))
    hyp3 = s1([linarith(w, c1, [lift(w, lo, c1)], '( 1 / ; ; 2 0 0 ) <_ ( Re ` W )', leaves={'( Re ` W )': lift(w, rw, c1)}), s1([], 'simpr', '( Re ` W ) <_ 2'),
               lift(w, wne1, c1)], '3jca', '( ( 1 / ; ; 2 0 0 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 2 /\\ W =/= 1 )')
    cv = s1([hyp3, g], 'mpd', split_imp(new)[1])
    qc = w.s([cv, w.inst('z6absle')], 'syl', '( %s -> %s e. CC )' % (c1, Q))
    vr = s1([qc], 'abscld', '( abs ` %s ) e. RR' % Q)
    re0 = linarith(w, c1, [lift(w, lo, c1)], '0 <_ ( Re ` W )', leaves={'( Re ` W )': lift(w, rw, c1)})
    h = s1([lift(w, nn, c1), s1([lift(w, wc, c1), s1([re0, lift(w, d1, c1)], 'jca', '( 0 <_ ( Re ` W ) /\\ 1 <_ %s )' % AW)], 'jca',
                                '( W e. CC /\\ ( 0 <_ ( Re ` W ) /\\ 1 <_ %s ) )' % AW), s1([vr, cv], 'jca', '( ( abs ` %s ) e. RR /\\ ( abs ` %s ) <_ %s )' % (Q, Q, CVXB('W')))],
           '3jca', sub(split_imp(STATEMENTS['z6cvxb'])[0], {'V': '( abs ` %s )' % Q}))
    r1 = s1([h, w.inst('z6cvxb')], 'syl', TG)
    # case 2 < Re W
    c2 = '( %s /\\ 2 < ( Re ` W ) )' % a; s2 = mkst(w, c2)
    rw2 = lift(w, rw, c2)
    g1 = linarith(w, c2, [s2([], 'simpr', '2 < ( Re ` W )')], '1 < ( Re ` W )', leaves={'( Re ` W )': rw2})
    BODY2 = DSER[len('A. s e. %s ' % HPZ):]
    gd, newd = inst_all(w, c2, lift(w, dser, c2), 's', HPZ, BODY2, 'W', lift(w, whp, c2))
    SUM = 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u W ) )'
    ew = s2([g1, gd], 'mpd', '( E ` W ) = ( ( W - 1 ) x. %s )' % SUM)
    db = s2([s2([lift(w, cf, c2), c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'), lift(w, cb, c2)], '3jca', '( C : NN --> CC /\\ 1 e. RR /\\ %s )' % CB),
             s2([lift(w, wc, c2), g1], 'jca', '( W e. CC /\\ 1 < ( Re ` W ) )'), w.inst('dserbnd')], 'syl2anc',
            '( abs ` %s ) <_ ( 1 x. ( 1 + ( 1 / ( ( Re ` W ) - 1 ) ) ) )' % SUM)
    sc_ = w.s([db, w.inst('z6absle')], 'syl', '( %s -> %s e. CC )' % (c2, SUM))
    qv = s2([s2([ew], 'oveq1d', '%s = ( ( ( W - 1 ) x. %s ) / ( W - 1 ) )' % (Q, SUM)), s2([sc_, lift(w, wm1, c2), lift(w, w10, c2)], 'divcan3d',
                                                                                          '( ( ( W - 1 ) x. %s ) / ( W - 1 ) ) = %s' % (SUM, SUM))], 'eqtrd', '%s = %s' % (Q, SUM))
    RM = '( ( Re ` W ) - 1 )'
    rmr = s2([rw2, c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'resubcld', '%s e. RR' % RM)
    rm1 = linarith(w, c2, [s2([], 'simpr', '2 < ( Re ` W )')], '1 <_ %s' % RM, leaves={'( Re ` W )': rw2})
    rmp = linarith(w, c2, [s2([], 'simpr', '2 < ( Re ` W )')], '0 < %s' % RM, leaves={'( Re ` W )': rw2})
    lr = s2([s2([c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'), c_(w, c2, w.s([], '0lt1', '0 < 1'), '0 < 1')], 'jca', '( 1 e. RR /\\ 0 < 1 )'),
             s2([rmr, rmp], 'jca', '( %s e. RR /\\ 0 < %s )' % (RM, RM)), w.inst('lerec')], 'syl2anc', '( 1 <_ %s <-> ( 1 / %s ) <_ ( 1 / 1 ) )' % (RM, RM))
    iv = s2([s2([rm1, lr], 'mpbid', '( 1 / %s ) <_ ( 1 / 1 )' % RM), c_(w, c2, w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')], 'breqtrd', '( 1 / %s ) <_ 1' % RM)
    ivr = s2([rmr, s2([rmp], 'gt0ne0d', '%s =/= 0' % RM)], 'rereccld', '( 1 / %s ) e. RR' % RM)
    b2 = linarith(w, c2, [iv], '( 1 x. ( 1 + ( 1 / %s ) ) ) <_ 2' % RM, leaves={'( 1 / %s )' % RM: ivr})
    sr = s2([sc_], 'abscld', '( abs ` %s ) e. RR' % SUM)
    # 2 <_ CVX4 ( W )
    nr = s2([lift(w, nn, c2)], 'nnred', 'N e. RR'); n1 = s2([lift(w, nn, c2)], 'nnge1d', '1 <_ N')
    Y3 = '( ( abs ` ( Im ` W ) ) + 3 )'; Cc = '( N x. %s )' % Y3
    ay2 = lift(w, ay, c2)
    y3r = s2([ay2, c_(w, c2, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'readdcld', '%s e. RR' % Y3)
    y30 = linarith(w, c2, [s2([lift(w, imc, c2)], 'absge0d', '0 <_ ( abs ` ( Im ` W ) )')], '0 <_ %s' % Y3, leaves={'( abs ` ( Im ` W ) )': ay2})
    cr = s2([nr, y3r], 'remulcld', '%s e. RR' % Cc)
    cl_ = s2([c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'), nr, y3r, y30, n1], 'lemul1ad', '( 1 x. %s ) <_ %s' % (Y3, Cc))
    c1_ = linarith(w, c2, [cl_, s2([lift(w, imc, c2)], 'absge0d', '0 <_ ( abs ` ( Im ` W ) )')], '1 <_ %s' % Cc, leaves={Cc: cr, '( abs ` ( Im ` W ) )': ay2})
    C2 = '( %s ^ 2 )' % Cc
    c2r = s2([cr], 'resqcld', '%s e. RR' % C2)
    csq = s2([s2([s2([cr], 'recnd', '%s e. CC' % Cc)], 'sqvald', '%s = ( %s x. %s )' % (C2, Cc, Cc)), None][:1] + [], 'id', 'x') if False else None
    sqv = s2([s2([cr], 'recnd', '%s e. CC' % Cc)], 'sqvald', '%s = ( %s x. %s )' % (C2, Cc, Cc))
    one_ = c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'); z1 = c_(w, c2, w.s([], '0le1', '0 <_ 1'), '0 <_ 1')
    cc1 = s2([one_, cr, one_, cr, z1, z1, c1_, c1_], 'lemul12ad', '( 1 x. 1 ) <_ ( %s x. %s )' % (Cc, Cc))
    c21 = s2([cc1, sqv], 'breqtrrd', '( 1 x. 1 ) <_ %s' % C2)
    rr, ge1 = omgfacts(w, c2, lift(w, nn, c2))
    c21b = s2([c_(w, c2, w.s([], '1t1e1', '( 1 x. 1 ) = 1'), '( 1 x. 1 ) = 1'), c21], 'eqbrtrrd', '1 <_ %s' % C2)
    om1 = s2([one_, rr, one_, c2r, z1, z1, ge1, c21b], 'lemul12ad', '( 1 x. 1 ) <_ ( %s x. %s )' % (OMGN, C2))
    P_ = '( %s x. %s )' % (OMGN, C2)
    pr_ = s2([rr, c2r], 'remulcld', '%s e. RR' % P_)
    c4 = CVX4('W')
    K4 = '( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % OMGN
    ass = s2([c_(w, c2, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR') if False else
              s2([c_(w, c2, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR')], 'recnd', '; ; ; ; ; 4 0 0 0 0 0 e. CC'),
              s2([rr], 'recnd', '%s e. CC' % OMGN), s2([c2r], 'recnd', '%s e. CC' % C2)], 'mulassd', '%s = ( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % (c4, P_))
    two4 = s2([linarith(w, c2, [om1], '2 <_ ( ; ; ; ; ; 4 0 0 0 0 0 x. %s )' % P_, leaves={P_: pr_}), ass], 'breqtrrd', '2 <_ %s' % c4)
    c4r = s2([s2([c_(w, c2, num.real(w, '; ; ; ; ; 4 0 0 0 0 0'), '; ; ; ; ; 4 0 0 0 0 0 e. RR'), rr], 'remulcld', '%s e. RR' % K4), c2r], 'remulcld', '%s e. RR' % c4)
    b3 = s2([db, b2], 'letrd' if False else 'x', 'x') if False else None
    brr = s2([s2([c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'), s2([c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'), ivr], 'readdcld', '( 1 + ( 1 / %s ) ) e. RR' % RM)],
                 'remulcld', '( 1 x. ( 1 + ( 1 / %s ) ) ) e. RR' % RM)], 'id' if False else 'x', 'x') if False else \
        s2([c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'), s2([c_(w, c2, w.s([], '1re', '1 e. RR'), '1 e. RR'), ivr], 'readdcld', '( 1 + ( 1 / %s ) ) e. RR' % RM)],
           'remulcld', '( 1 x. ( 1 + ( 1 / %s ) ) ) e. RR' % RM)
    b3 = s2([sr, brr, c_(w, c2, w.s([], '2re', '2 e. RR'), '2 e. RR'), db, b2], 'letrd', '( abs ` %s ) <_ 2' % SUM)
    b4 = s2([sr, c_(w, c2, w.s([], '2re', '2 e. RR'), '2 e. RR'), c4r, b3, two4], 'letrd', '( abs ` %s ) <_ %s' % (SUM, c4))
    r2 = s2([s2([qv], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (Q, SUM)), b4], 'eqbrtrd', TG)
    dis = st([rw, c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), w.inst('lelttric')], 'syl2anc', '( ( Re ` W ) <_ 2 \\/ 2 < ( Re ` W ) )')
    w.qed([r1, r2, dis], 'mpjaodan', STATEMENTS['z6lstrip'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6gstrip, z6cvxb, z6lstrip]:
        if want(fn.__name__):
            if not run(fn()):
                break
