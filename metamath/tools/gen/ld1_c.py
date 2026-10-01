"""Sortie LD1, section 3: L1.c, the truncation of the detector series
(ld1fdv ld1ttabs ld1ttcvg ld1hexp ld1xexp ld1tailn ld1tailpt ld1tailsum ld1trunc).
Run: MM_DB=sorties/ld1.mm MM_ENGINE=mmatch python3 tools/gen/ld1_c.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ld1lib import *
import lin as _L
_L.MAXPOW = 8

only = sys.argv[1:]
want = lambda l: not only or l in only
L = '( log ` D )'
E4 = '( exp ` ( -u 4 x. %s ) )' % L
D2 = '( 2 x. D )'
PF1 = '( N PFun 1 )'
FDT = lambda n: 'if ( D < %s , ( ( ( ( %s x. ( %s ` %s ) ) x. %s ) x. ( C ` %s ) ) x. ( %s ^c -u S ) ) , 0 )' % (n, BVA(n), PF1, n, EXY(n), n, n)


def fin(w):
    qedlast(w)
    return go(w)


def setup(w, A):
    """parts, base closure (D, log D, YP, JPAR, NMAX) and the HA facts under an antecedent containing HA's conjuncts"""
    P = parts(w, A)
    c, F = basecl(w, A, P)
    nn = P['N e. NN']; cf = P['C : NN --> CC']; cb = P[CB]; sc = P['S e. CC']
    re = dst(w, A, [sc], 'recld', '( Re ` S ) e. RR')
    c.leaf('S', 'CC', sc); c.leaf('( Re ` S )', 'RR', re); c.leaf('( Im ` S )', 'RR', dst(w, A, [sc], 'imcld', '( Im ` S ) e. RR'))
    F.update(nN=nn, cf=cf, cb=cb, sc=sc, re=re)
    return P, c, F


def hab(w, A, F):
    """( A -> HAB0[D, 2D] ) and the RR+ triple"""
    dr, z = F['dr'], F['z']
    d2r = dst(w, A, [dr], 'x', 'x') if False else dst(w, A, [a1(w, A, '2re', '2 e. RR'), dr], 'remulcld', '%s e. RR' % D2)
    lt = linarith(w, A, [z], 'D < %s' % D2, closure=Closure(w, A, {'D': ('RR', dr)}))
    h0 = J(w, A, J(w, A, dr, z), J(w, A, d2r, lt))
    rp3 = J(w, A, F['rp'], dst(w, A, [d2r, linarith(w, A, [z], '0 < %s' % D2, closure=Closure(w, A, {'D': ('RR', dr)}))], 'elrpd', '%s e. RR+' % D2), lt)
    return h0, rp3


def termcl(w, An, c, n, nstep, F, rp3):
    """leaves for BVA(n), ( C ` n ) under An (n e. NN by nstep); returns the closure"""
    c.leaf(n, 'NN', nstep)
    c.leaf(BVA(n), 'RR', ap(w, An, 'bvare', [lift(w, rp3, An), nstep], '%s e. RR' % BVA(n)))
    c.leaf('( C ` %s )' % n, 'CC', dst(w, An, [lift(w, F['cf'], An), nstep], 'ffvelcdmd', '( C ` %s ) e. CC' % n))
    return c


def child(w, A, c, An, n, nstep, F, rp3):
    """a child closure under An = ( A /\\ n e. NN-ish ) knowing the term leaves"""
    cc = Closure(w, An, {}, parent=c) if False else Closure(w, An, {k: v for k, v in []})
    for e, kinds in c.leaves.items():
        pass
    return cc


def liftcl(w, A, c, An, names):
    """a fresh closure under An with the leaves NAMES lifted from c's facts recorded in F"""
    lv = {}
    for e, kind, stp in names:
        lv.setdefault(e, []).append((kind, lift(w, stp, An)))
    return Closure(w, An, lv)


def basefacts(F):
    return [('D', 'RR+', F['rp']), ('D', 'gt1', F['d1']), (L, 'RR', F['lr']), (YP, 'RR+', F['yrp']), (YP, 'gt1', F['y1']),
            (JPAR, 'NN', F['jn']), (NMAX, 'NN', F['nn']), ('S', 'CC', F['sc']), ('( Re ` S )', 'RR', F['re'])]


def fdt_tt(w, A, An, n, nstep, F, c):
    """( An -> FDT(n) = TT(n) ) from dshpf1 and mulridd; c knows BVA(n)"""
    pf = ap(w, An, 'dshpf1', [J(w, An, lift(w, F['nN'], An), nstep)], '( %s ` %s ) = 1' % (PF1, n))
    r1, t1 = w.rewrite(FDT(n), {'( %s ` %s )' % (PF1, n): ('1', pf)}, An)
    bc = c.mem(BVA(n), 'CC')
    m1 = dst(w, An, [bc], 'mulridd', '( %s x. 1 ) = %s' % (BVA(n), BVA(n)))
    r2, t2 = w.rewrite(t1, {'( %s x. 1 )' % BVA(n): (BVA(n), m1)}, An)
    assert t2 == TT(n), (t2, TT(n))
    return eqt(w, An, r1, r2)


def ld1fdv():
    w = W('ld1fdv', 'Lean ` fdetTerm_one_eq ` and ` Fdet_eq_tsum_truncTerm ` : the half-line detector is the series of the truncation summands ` truncTerm ` (~ z5fdetval , ~ dshpf1 ).')
    A = ante('ld1fdv'); P, c, F = setup(w, A)
    h0, rp3 = hab(w, A, F)
    dv = dst(w, A, [F['dr']], 'elexd', 'D e. _V'); d2v = dst(w, A, [], 'ovexd', '%s e. _V' % D2)
    pv = dst(w, A, [], 'ovexd', '%s e. _V' % PF1); yv = dst(w, A, [], 'ovexd', '%s e. _V' % YP)
    cv = dst(w, A, [F['cf'], a1(w, A, 'nnex', 'NN e. _V')], 'fexd', 'C e. _V')
    fv = ap(w, A, 'z5fdetval', [J(w, A, J(w, A, dv, d2v), J(w, A, pv, yv, cv)), F['sc']], '%s = sum_ n e. NN %s' % (FDVH, FDT('n')))
    An = '( %s /\\ n e. NN )' % A
    nst = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    cn = liftcl(w, A, c, An, basefacts(F)); termcl(w, An, cn, 'n', nst, F, rp3)
    eq = fdt_tt(w, A, An, 'n', nst, F, cn)
    s = dst(w, A, [eq], 'sumeq2dv', 'sum_ n e. NN %s = sum_ n e. NN %s' % (FDT('n'), TT('n')))
    eqt(w, A, fv, s)
    return fin(w)


def ld1ttabs():
    w = W('ld1ttabs', 'Lean ` norm_truncTerm_le ` : ` abs truncTerm ( n ) <_ n e ^ ( -u n / Y ) ` (~ z5bvaabs , ~ abscxp , ~ cxplea ).')
    A = ante('ld1ttabs'); P, c, F = setup(w, A)
    kn = P['K e. NN']
    h0, rp3 = hab(w, A, F)
    termcl(w, A, c, 'K', kn, F, rp3)
    a, e, ck, p = BVA('K'), EXY('K'), '( C ` K )', '( K ^c -u S )'
    BND = '( K x. %s )' % e
    A1 = '( %s /\\ D < K )' % A; A2 = '( %s /\\ -. D < K )' % A
    # case D < K
    c1 = liftcl(w, A, c, A1, basefacts(F) + [('K', 'NN', kn), (a, 'RR', c.mem(a, 'RR')), (ck, 'CC', c.mem(ck, 'CC'))])
    t1 = dst(w, A1, [w.s([], 'simpr', '( %s -> D < K )' % A1)], 'iftrued', '%s = %s' % (TT('K'), BODY('K')))
    ae = '( %s x. %s )' % (a, e); aec = '( %s x. %s )' % (ae, ck)
    m1 = dst(w, A1, [c1.mem(aec, 'CC'), c1.mem(p, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (BODY('K'), aec, p))
    m2 = dst(w, A1, [c1.mem(ae, 'CC'), c1.mem(ck, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (aec, ae, ck))
    m3 = dst(w, A1, [c1.mem(a, 'CC'), c1.mem(e, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (ae, a, e))
    ei = dst(w, A1, [c1.mem(e, 'RR'), c1.ge0(e)], 'absidd', '( abs ` %s ) = %s' % (e, e))
    AE = '( ( abs ` %s ) x. %s )' % (a, e)
    m3b = eqt(w, A1, m3, dst(w, A1, [ei], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = %s' % (a, e, AE)))
    full = eqt(w, A1, m1, dst(w, A1, [eqt(w, A1, m2, dst(w, A1, [m3b], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (ae, ck, AE, ck)))], 'oveq1d',
                                   '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( %s x. ( abs ` %s ) ) x. ( abs ` %s ) )' % (aec, p, AE, ck, p)))
    # the factor bounds
    ab = ap(w, A1, 'z5bvaabs', [J(w, A1, lift(w, h0, A1), lift(w, kn, A1))], '( abs ` %s ) <_ K' % a)
    cg, _ = w.wcongr('( abs ` ( C ` j ) ) <_ 1', {'j': 'K'}, 'j = K', {'j': w.s([], 'id', '( j = K -> j = K )')})
    cb1 = w.s([cg, lift(w, F['cb'], A1), lift(w, kn, A1)], 'rspcdva', '( %s -> ( abs ` %s ) <_ 1 )' % (A1, ck))
    krp = dst(w, A1, [lift(w, kn, A1)], 'nnrpd', 'K e. RR+')
    nsc = dst(w, A1, [lift(w, F['sc'], A1)], 'negcld', '-u S e. CC')
    ax = ap(w, A1, 'abscxp', [krp, nsc], '( abs ` %s ) = ( K ^c ( Re ` -u S ) )' % p)
    rn = ap(w, A1, 'reneg', [lift(w, F['sc'], A1)], '( Re ` -u S ) = -u ( Re ` S )')
    ax2 = eqt(w, A1, ax, dst(w, A1, [rn], 'oveq2d', '( K ^c ( Re ` -u S ) ) = ( K ^c -u ( Re ` S ) )'))
    kr = c1.mem('K', 'RR'); k1 = dst(w, A1, [lift(w, kn, A1)], 'nnge1d', '1 <_ K')
    re0 = lift(w, P['0 <_ ( Re ` S )'], A1)
    nre = linarith(w, A1, [re0], '-u ( Re ` S ) <_ 0', closure=c1)
    cx = ap(w, A1, 'cxplea', [J(w, A1, kr, k1), J(w, A1, c1.mem('-u ( Re ` S )', 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % A1)), nre], '( K ^c -u ( Re ` S ) ) <_ ( K ^c 0 )')
    c0 = ap(w, A1, 'cxp0', [c1.mem('K', 'CC')], '( K ^c 0 ) = 1')
    pb = dst(w, A1, [ax2, dst(w, A1, [cx, c0], 'breqtrd', '( K ^c -u ( Re ` S ) ) <_ 1')], 'eqbrtrd', '( abs ` %s ) <_ 1' % p)
    # assemble
    AA, AC, AP = '( abs ` %s )' % a, '( abs ` %s )' % ck, '( abs ` %s )' % p
    for x in (AA, AC, AP):
        c1.leaf(x, 'RR', dst(w, A1, [c1.mem(x[8:-2], 'CC')], 'abscld', '%s e. RR' % x))
        c1.leaf(x, 'ge0', dst(w, A1, [c1.mem(x[8:-2], 'CC')], 'absge0d', '0 <_ %s' % x))
    b1 = lemul(w, A1, c1, ab, e, side=1)                                                     # AA e <_ K e
    b2 = dst(w, A1, [c1.mem(AC, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % A1), c1.mem(AP, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % A1),
                     c1.ge0(AC), c1.ge0(AP), cb1, pb], 'lemul12ad', '( %s x. %s ) <_ ( 1 x. 1 )' % (AC, AP))
    CP = '( %s x. %s )' % (AC, AP)
    b3 = dst(w, A1, [c1.mem(AE, 'RR'), c1.mem(BND, 'RR'), c1.mem(CP, 'RR'), c1.mem('( 1 x. 1 )', 'RR'), c1.ge0(AE), c1.ge0(CP), b1, b2], 'lemul12ad',
             '( %s x. %s ) <_ ( %s x. ( 1 x. 1 ) )' % (AE, CP, BND))
    asc = dst(w, A1, [c1.mem(AE, 'CC'), c1.mem(AC, 'CC'), c1.mem(AP, 'CC')], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (AE, AC, AP, AE, CP))
    one = dst(w, A1, [dst(w, A1, [a1(w, A1, '1t1e1', '( 1 x. 1 ) = 1')], 'oveq2d', '( %s x. ( 1 x. 1 ) ) = ( %s x. 1 )' % (BND, BND)), dst(w, A1, [c1.mem(BND, 'CC')], 'mulridd', '( %s x. 1 ) = %s' % (BND, BND))], 'eqtrd',
              '( %s x. ( 1 x. 1 ) ) = %s' % (BND, BND))
    bb = dst(w, A1, [eqt(w, A1, full, asc), dst(w, A1, [b3, one], 'breqtrd', '( %s x. %s ) <_ %s' % (AE, CP, BND))], 'eqbrtrd', '( abs ` %s ) <_ %s' % (BODY('K'), BND))
    case1 = dst(w, A1, [dst(w, A1, [t1], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (TT('K'), BODY('K'))), bb], 'eqbrtrd', '( abs ` %s ) <_ %s' % (TT('K'), BND))
    # case -. D < K
    c2 = liftcl(w, A, c, A2, basefacts(F) + [('K', 'NN', kn)])
    t2 = dst(w, A2, [w.s([], 'simpr', '( %s -> -. D < K )' % A2)], 'iffalsed', '%s = 0' % TT('K'))
    z = dst(w, A2, [dst(w, A2, [t2], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % TT('K')), a1(w, A2, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % TT('K'))
    case2 = dst(w, A2, [z, c2.ge0(BND)], 'eqbrtrd', '( abs ` %s ) <_ %s' % (TT('K'), BND))
    dst(w, A, [case1, case2], 'pm2.61dan', '( abs ` %s ) <_ %s' % (TT('K'), BND))
    return fin(w)


def ld1ttcvg():
    w = W('ld1ttcvg', 'Lean ` summable_truncTerm ` : the truncation summands and their absolute values are summable (~ z5fdetcvg , ~ dshpf1 ).')
    A = ante('ld1ttcvg'); P, c, F = setup(w, A)
    h0, rp3 = hab(w, A, F)
    hfd = J(w, A, h0, J(w, A, F['yrp'], J(w, A, F['nN'], J(w, A, a1(w, A, '1re', '1 e. RR'), a1(w, A, '0le1', '0 <_ 1')))))
    cv = ap(w, A, 'z5fdetcvg', [hfd, J(w, A, P[CFN], J(w, A, F['sc'], P['0 <_ ( Re ` S )']))],
            '( seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~> /\\ seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (FDT('n'), FDT('n')))
    An = '( %s /\\ n e. NN )' % A
    nst = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    cn = liftcl(w, A, c, An, basefacts(F)); termcl(w, An, cn, 'n', nst, F, rp3)
    eq = fdt_tt(w, A, An, 'n', nst, F, cn)
    m1 = dst(w, A, [eq], 'mpteq2dva', '( n e. NN |-> %s ) = ( n e. NN |-> %s )' % (FDT('n'), TT('n')))
    m2 = dst(w, A, [dst(w, An, [eq], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (FDT('n'), TT('n')))], 'mpteq2dva', '( n e. NN |-> ( abs ` %s ) ) = ( n e. NN |-> ( abs ` %s ) )' % (FDT('n'), TT('n')))
    s1 = dst(w, A, [dst(w, A, [m1], 'seqeq3d', 'seq 1 ( + , ( n e. NN |-> %s ) ) = seq 1 ( + , ( n e. NN |-> %s ) )' % (FDT('n'), TT('n')))], 'eleq1d',
             '( seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> <-> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (FDT('n'), TT('n')))
    s2 = dst(w, A, [dst(w, A, [m2], 'seqeq3d', 'seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) = seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) )' % (FDT('n'), TT('n')))], 'eleq1d',
             '( seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~> <-> seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~> )' % (FDT('n'), TT('n')))
    p1 = dst(w, A, [dst(w, A, [cv], 'simprd', 'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % FDT('n')), s1], 'mpbid', 'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % TT('n'))
    p2 = dst(w, A, [dst(w, A, [cv], 'simpld', 'seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~>' % FDT('n')), s2], 'mpbid', 'seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~>' % TT('n'))
    J(w, A, p2, p1)
    return fin(w)


def ld1hexp():
    w = W('ld1hexp', 'Lean ` half_le_one_sub_exp_neg ` : ` x / 2 <_ 1 - e ^ -u x ` on ` [ 0 , 1 ] ` (~ bvefge1p , ~ efneg , ~ lerec , ~ ledivmul ).')
    A = ante('ld1hexp'); P = parts(w, A); xr, x0, x1 = P['X e. RR'], P['0 <_ X'], P['X <_ 1']
    c = Closure(w, A, {'X': [('RR', xr), ('ge0', x0)]})
    xc = dst(w, A, [xr], 'recnd', 'X e. CC'); EX = '( exp ` X )'
    ef = ap(w, A, 'bvefge1p', [J(w, A, xr, x0)], '( 1 + X ) <_ %s' % EX)
    en = ap(w, A, 'efneg', [xc], '( exp ` -u X ) = ( 1 / %s )' % EX)
    lr = ap(w, A, 'lerec', [J(w, A, c.mem('( 1 + X )', 'RR'), c.gt0('( 1 + X )')), J(w, A, c.mem(EX, 'RR'), c.gt0(EX))], '( ( 1 + X ) <_ %s <-> ( 1 / %s ) <_ ( 1 / ( 1 + X ) ) )' % (EX, EX))
    h1 = dst(w, A, [ef, lr], 'mpbid', '( 1 / %s ) <_ ( 1 / ( 1 + X ) )' % EX)
    Q = '( 1 - ( X / 2 ) )'
    ldm = ap(w, A, 'ledivmul', [w.s([], '1red', '( %s -> 1 e. RR )' % A), c.mem(Q, 'RR'), J(w, A, c.mem('( 1 + X )', 'RR'), c.gt0('( 1 + X )'))], '( ( 1 / ( 1 + X ) ) <_ %s <-> 1 <_ ( ( 1 + X ) x. %s ) )' % (Q, Q))
    nl = nlinarith(w, A, [x0, x1], '1 <_ ( ( 1 + X ) x. %s )' % Q, closure=c)
    h2 = dst(w, A, [nl, ldm], 'mpbird', '( 1 / ( 1 + X ) ) <_ %s' % Q)
    for e in ('( exp ` -u X )', '( 1 / %s )' % EX, '( 1 / ( 1 + X ) )'):
        c.leaf(e, 'RR', c.mem(e, 'RR'))
    linarith(w, A, [en, h1, h2], '( X / 2 ) <_ ( 1 - ( exp ` -u X ) )', closure=c, name='qed')
    return go(w)


def ld1xexp():
    w = W('ld1xexp', '` x e ^ -u x <_ 1 ` for ` x >_ 0 ` (~ bvefge1p , ~ efneg , ~ ledivmul ).')
    A = ante('ld1xexp'); P = parts(w, A); xr, x0 = P['X e. RR'], P['0 <_ X']
    c = Closure(w, A, {'X': [('RR', xr), ('ge0', x0)]})
    xc = dst(w, A, [xr], 'recnd', 'X e. CC'); EX = '( exp ` X )'
    ef = ap(w, A, 'bvefge1p', [J(w, A, xr, x0)], '( 1 + X ) <_ %s' % EX)
    en = ap(w, A, 'efneg', [xc], '( exp ` -u X ) = ( 1 / %s )' % EX)
    dr = dst(w, A, [xc, c.mem(EX, 'CC'), c.ne0(EX)], 'divrecd', '( X / %s ) = ( X x. ( 1 / %s ) )' % (EX, EX))
    e1 = eqt(w, A, dst(w, A, [en], 'oveq2d', '( X x. ( exp ` -u X ) ) = ( X x. ( 1 / %s ) )' % EX), eqc(w, A, dr))
    ldm = ap(w, A, 'ledivmul', [xr, w.s([], '1red', '( %s -> 1 e. RR )' % A), J(w, A, c.mem(EX, 'RR'), c.gt0(EX))], '( ( X / %s ) <_ 1 <-> X <_ ( %s x. 1 ) )' % (EX, EX))
    c.leaf(EX, 'RR', c.mem(EX, 'RR'))
    l1 = linarith(w, A, [ef], 'X <_ ( %s x. 1 )' % EX, closure=c)
    dst(w, A, [e1, dst(w, A, [l1, ldm], 'mpbird', '( X / %s ) <_ 1' % EX)], 'eqbrtrd', '( X x. ( exp ` -u X ) ) <_ 1')
    return fin(w)


def ld1tailn():
    w = W('ld1tailn', 'Lean ` tail_numeric ` (with 32 for 16, LD1-HANDOFF section 2 item 7): ` 32 Y ^ 2 e ^ ( -u 4 log D ) = 32 / e ^ ( ( 49 / 50 ) log D ) <_ 1 / 8 ` (~ cxpefd , ~ efexp , ~ efadd , ~ ld1ntail ).')
    A = HZH; P = parts(w, A); c, F = basecl(w, A, P)
    dc = dst(w, A, [F['dr']], 'recnd', 'D e. CC'); d0 = dst(w, A, [F['rp']], 'rpne0d', 'D =/= 0')
    C151 = '( ; ; 1 5 1 / ; ; 1 0 0 )'; B1 = '( %s x. %s )' % (C151, L)
    y = dst(w, A, [dc, d0, c.mem(C151, 'CC')], 'cxpefd', '%s = ( exp ` %s )' % (YP, B1))
    ex = ap(w, A, 'efexp', [c.mem(B1, 'CC'), a1(w, A, '2z', '2 e. ZZ')], '( exp ` ( 2 x. %s ) ) = ( ( exp ` %s ) ^ 2 )' % (B1, B1))
    y2 = eqt(w, A, dst(w, A, [y], 'oveq1d', '( %s ^ 2 ) = ( ( exp ` %s ) ^ 2 )' % (YP, B1)), eqc(w, A, ex))
    T2 = '( 2 x. %s )' % B1; T4 = '( -u 4 x. %s )' % L
    ea = eqc(w, A, ap(w, A, 'efadd', [c.mem(T2, 'CC'), c.mem(T4, 'CC')], '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. %s )' % (T2, T4, T2, E4)))
    B2 = '( ( ; 4 9 / ; 5 0 ) x. %s )' % L
    idn = ringeq(w, A, '( %s + %s )' % (T2, T4), '-u %s' % B2, c)
    en = ap(w, A, 'efneg', [c.mem(B2, 'CC')], '( exp ` -u %s ) = ( 1 / ( exp ` %s ) )' % (B2, B2))
    E = '( exp ` %s )' % B2
    pr = eqt(w, A, eqt(w, A, dst(w, A, [y2], 'oveq1d', '( ( %s ^ 2 ) x. %s ) = ( ( exp ` %s ) x. %s )' % (YP, E4, T2, E4)), ea),
             eqt(w, A, dst(w, A, [idn], 'fveq2d', '( exp ` ( %s + %s ) ) = ( exp ` -u %s )' % (T2, T4, B2)), en))   # YP^2 E4 = 1 / E
    Y2 = '( %s ^ 2 )' % YP
    asc = dst(w, A, [c.mem('; 3 2', 'CC'), c.mem(Y2, 'CC'), c.mem(E4, 'CC')], 'mulassd', '( ( ; 3 2 x. %s ) x. %s ) = ( ; 3 2 x. ( %s x. %s ) )' % (Y2, E4, Y2, E4))
    dr = dst(w, A, [c.mem('; 3 2', 'CC'), c.mem(E, 'CC'), c.ne0(E)], 'divrecd', '( ; 3 2 / %s ) = ( ; 3 2 x. ( 1 / %s ) )' % (E, E))
    lhs = eqt(w, A, eqt(w, A, asc, dst(w, A, [pr], 'oveq2d', '( ; 3 2 x. ( %s x. %s ) ) = ( ; 3 2 x. ( 1 / %s ) )' % (Y2, E4, E))), eqc(w, A, dr))
    nt = ap(w, A, 'ld1ntail', [J(w, A, F['lr'], F['dl'])], '; ; 2 5 6 <_ %s' % E)
    ldm = ap(w, A, 'ledivmul', [c.mem('; 3 2', 'RR'), c.mem('( 1 / 8 )', 'RR'), J(w, A, c.mem(E, 'RR'), c.gt0(E))], '( ( ; 3 2 / %s ) <_ ( 1 / 8 ) <-> ; 3 2 <_ ( %s x. ( 1 / 8 ) ) )' % (E, E))
    c.leaf(E, 'RR', c.mem(E, 'RR'))
    l1 = linarith(w, A, [nt], '; 3 2 <_ ( %s x. ( 1 / 8 ) )' % E, closure=c)
    dst(w, A, [lhs, dst(w, A, [l1, ldm], 'mpbird', '( ; 3 2 / %s ) <_ ( 1 / 8 )' % E)], 'eqbrtrd', '%s <_ ( 1 / 8 )' % TAILC)
    return fin(w)


def ld1tailpt():
    w = W('ld1tailpt', 'The pointwise tail majorant of L1.c: for ` n > Nmax ` , ` abs truncTerm ( n ) <_ 4 Y e ^ ( -u 4 log D ) q ^ n ` , ` q = e ^ ( -u 1 / ( 4 Y ) ) ` (~ ld1ttabs , ~ ld1xexp , ~ efadd , ~ efexp ).')
    A = ante('ld1tailpt'); P, c, F = setup(w, A)
    kn = P['K e. NN']; kge = P['( %s + 1 ) <_ K' % NMAX]; ha = P[HA]
    c.leaf('K', 'NN', kn)
    h0, rp3 = hab(w, A, F); termcl(w, A, c, 'K', kn, F, rp3)
    Y = YP
    tt = ap(w, A, 'ld1ttabs', [J(w, A, ha, kn)], concl('ld1ttabs'))
    u = '( K / %s )' % Y
    ur = c.mem(u, 'RR'); u0 = c.ge0(u); c.leaf(u, 'RR', ur); c.leaf(u, 'ge0', u0)
    kc = c.mem('K', 'CC'); yc = c.mem(Y, 'CC'); y0 = c.ne0(Y)
    dn = eqc(w, A, dst(w, A, [kc, yc, y0], 'divnegd', '-u %s = ( -u K / %s )' % (u, Y)))          # ( -u K / Y ) = -u u
    e1 = '( exp ` -u ( %s / 2 ) )' % u; e2 = '( exp ` -u ( %s / 4 ) )' % u
    spl = ringeq(w, A, '-u %s' % u, '( -u ( %s / 2 ) + ( -u ( %s / 4 ) + -u ( %s / 4 ) ) )' % (u, u, u), c)
    T1 = '-u ( %s / 2 )' % u; T2 = '-u ( %s / 4 )' % u
    ea1 = ap(w, A, 'efadd', [c.mem(T1, 'CC'), c.mem('( %s + %s )' % (T2, T2), 'CC')], '( exp ` ( %s + ( %s + %s ) ) ) = ( %s x. ( exp ` ( %s + %s ) ) )' % (T1, T2, T2, e1, T2, T2))
    ea2 = ap(w, A, 'efadd', [c.mem(T2, 'CC'), c.mem(T2, 'CC')], '( exp ` ( %s + %s ) ) = ( %s x. %s )' % (T2, T2, e2, e2))
    exy = eqt(w, A, eqt(w, A, dst(w, A, [eqt(w, A, dn, spl)], 'fveq2d', '%s = ( exp ` ( %s + ( %s + %s ) ) )' % (EXY('K'), T1, T2, T2)), ea1),
              dst(w, A, [ea2], 'oveq2d', '( %s x. ( exp ` ( %s + %s ) ) ) = ( %s x. ( %s x. %s ) )' % (e1, T2, T2, e1, e2, e2)))   # EXY(K) = e1 (e2 e2)
    for e in (e1, e2):
        c.leaf(e, 'RR', c.mem(e, 'RR')); c.leaf(e, 'ge0', c.ge0(e))
    # (i) K e2 <_ 4 Y
    ky = dst(w, A, [kc, yc, y0], 'divcan2d', '( %s x. %s ) = K' % (Y, u))
    r1 = dst(w, A, [eqc(w, A, ky)], 'oveq1d', '( K x. %s ) = ( ( %s x. %s ) x. %s )' % (e2, Y, u, e2))
    r2 = ringeq(w, A, '( ( %s x. %s ) x. %s )' % (Y, u, e2), '( ( 4 x. %s ) x. ( ( %s / 4 ) x. %s ) )' % (Y, u, e2), c)
    xe = ap(w, A, 'ld1xexp', [J(w, A, c.mem('( %s / 4 )' % u, 'RR'), c.ge0('( %s / 4 )' % u))], '( ( %s / 4 ) x. %s ) <_ 1' % (u, e2))
    b1 = dst(w, A, [lemul(w, A, c, xe, '( 4 x. %s )' % Y), dst(w, A, [c.mem('( 4 x. %s )' % Y, 'CC')], 'mulridd', '( ( 4 x. %s ) x. 1 ) = ( 4 x. %s )' % (Y, Y))], 'breqtrd',
             '( ( 4 x. %s ) x. ( ( %s / 4 ) x. %s ) ) <_ ( 4 x. %s )' % (Y, u, e2, Y))
    ke2 = dst(w, A, [eqt(w, A, r1, r2), b1], 'eqbrtrd', '( K x. %s ) <_ ( 4 x. %s )' % (e2, Y))
    # (ii) e1 <_ E4
    nm = ap(w, A, 'ld1nmax', [F['hz']], concl('ld1nmax'))
    nge = dst(w, A, [nm], 'simp2d', '( ( 8 x. %s ) x. %s ) <_ %s' % (Y, L, NMAX))
    c.atom('( %s x. %s )' % (Y, L)); c.atom('( %s x. %s )' % (Y, u))
    pre = linarith(w, A, [kge, nge, ky], '( %s x. ( 8 x. %s ) ) <_ ( %s x. %s )' % (Y, L, Y, u), closure=c, products=True)
    lm = ap(w, A, 'lemul2d', [c.mem('( 8 x. %s )' % L, 'RR'), ur, F['yrp']], '( ( 8 x. %s ) <_ %s <-> ( %s x. ( 8 x. %s ) ) <_ ( %s x. %s ) )' % (L, u, Y, L, Y, u))
    u8 = dst(w, A, [pre, lm], 'mpbird', '( 8 x. %s ) <_ %s' % (L, u))
    efl = ap(w, A, 'efle', [c.mem(T1, 'RR'), c.mem('( -u 4 x. %s )' % L, 'RR')], '( %s <_ ( -u 4 x. %s ) <-> %s <_ %s )' % (T1, L, e1, E4))
    b2 = dst(w, A, [linarith(w, A, [u8], '%s <_ ( -u 4 x. %s )' % (T1, L), closure=c), efl], 'mpbid', '%s <_ %s' % (e1, E4))
    # (iii) e2 = Q4 ^ K
    R4 = '( -u 1 / ( 4 x. %s ) )' % Y
    ex = ap(w, A, 'efexp', [c.mem(R4, 'CC'), c.mem('K', 'ZZ')], '( exp ` ( K x. %s ) ) = ( %s ^ K )' % (R4, Q4))
    m1c = c.mem('-u 1', 'CC'); y4c = c.mem('( 4 x. %s )' % Y, 'CC'); y40 = c.ne0('( 4 x. %s )' % Y)
    sa = eqc(w, A, dst(w, A, [kc, m1c, y4c, y40], 'divassd', '( ( K x. -u 1 ) / ( 4 x. %s ) ) = ( K x. %s )' % (Y, R4)))
    sb = dst(w, A, [dst(w, A, [kc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'mulneg2d', '( K x. -u 1 ) = -u ( K x. 1 )'), dst(w, A, [dst(w, A, [kc], 'mulridd', '( K x. 1 ) = K')], 'negeqd', '-u ( K x. 1 ) = -u K')], 'eqtrd', '( K x. -u 1 ) = -u K')
    sb2 = dst(w, A, [sb], 'oveq1d', '( ( K x. -u 1 ) / ( 4 x. %s ) ) = ( -u K / ( 4 x. %s ) )' % (Y, Y))
    nkc = c.mem('-u K', 'CC'); fc = c.mem('4', 'CC'); f0 = c.ne0('4')
    dd = dst(w, A, [nkc, yc, fc, y0, f0], 'divdiv1d', '( ( -u K / %s ) / 4 ) = ( -u K / ( %s x. 4 ) )' % (Y, Y))
    mc = dst(w, A, [dst(w, A, [yc, fc], 'mulcomd', '( %s x. 4 ) = ( 4 x. %s )' % (Y, Y))], 'oveq2d', '( -u K / ( %s x. 4 ) ) = ( -u K / ( 4 x. %s ) )' % (Y, Y))
    sc_ = eqc(w, A, eqt(w, A, dd, mc))                                                      # ( -u K / ( 4 Y ) ) = ( ( -u K / Y ) / 4 )
    sd = dst(w, A, [dn], 'oveq1d', '( ( -u K / %s ) / 4 ) = ( -u %s / 4 )' % (Y, u))
    se = eqc(w, A, dst(w, A, [c.mem(u, 'CC'), fc, f0], 'divnegd', '-u ( %s / 4 ) = ( -u %s / 4 )' % (u, u)))
    kk = eqt(w, A, eqt(w, A, eqt(w, A, eqt(w, A, sa, sb2), sc_), sd), se)                   # ( K x. R4 ) = -u ( u / 4 )
    e2q = eqt(w, A, eqc(w, A, ex), dst(w, A, [kk], 'fveq2d', '( exp ` ( K x. %s ) ) = %s' % (R4, e2)))   # Q4^K = e2
    # assemble
    prod = ringeq(w, A, '( K x. ( %s x. ( %s x. %s ) ) )' % (e1, e2, e2), '( ( ( K x. %s ) x. %s ) x. %s )' % (e2, e1, e2), c)
    KE = '( K x. %s )' % e2; Y4 = '( 4 x. %s )' % Y
    b12 = dst(w, A, [c.mem(KE, 'RR'), c.mem(Y4, 'RR'), c.mem(e1, 'RR'), c.mem(E4, 'RR'), c.ge0(KE), c.ge0(e1), ke2, b2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (KE, e1, Y4, E4))
    b3 = lemul(w, A, c, b12, e2, side=1)
    fin_ = dst(w, A, [b3, dst(w, A, [eqc(w, A, e2q)], 'oveq2d', '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. ( %s ^ K ) )' % (Y4, E4, e2, Y4, E4, Q4))], 'breqtrd',
               '( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. ( %s ^ K ) )' % (KE, e1, e2, Y4, E4, Q4))
    bnd = eqt(w, A, dst(w, A, [exy], 'oveq2d', '( K x. %s ) = ( K x. ( %s x. ( %s x. %s ) ) )' % (EXY('K'), e1, e2, e2)), prod)
    last = dst(w, A, [dst(w, A, [tt], 'x', 'x') if False else tt, bnd], 'x', 'x') if False else None
    ab2 = dst(w, A, [tt, bnd], 'breqtrd', '( abs ` %s ) <_ ( ( %s x. %s ) x. %s )' % (TT('K'), KE, e1, e2))
    dst(w, A, [c.mem('( abs ` %s )' % TT('K'), 'RR') if False else dst(w, A, [c.mem(TT('K'), 'CC')], 'abscld', '( abs ` %s ) e. RR' % TT('K')),
               c.mem('( ( %s x. %s ) x. %s )' % (KE, e1, e2), 'RR'), c.mem('( ( %s x. %s ) x. ( %s ^ K ) )' % (Y4, E4, Q4), 'RR'), ab2, fin_], 'letrd',
        '( abs ` %s ) <_ ( ( %s x. %s ) x. ( %s ^ K ) )' % (TT('K'), Y4, E4, Q4))
    return fin(w)


def cvgm(w, A, c, F, rp3):
    """the convergences of F = ( m e. NN |-> TT(m) ) and G = ( m e. NN |-> abs TT(m) ) at 1 (from ld1ttcvg, renamed), with the closures of
    TT(n) under ( A /\\ n e. NN ); returns (FM, GM, cvF1, cvG1, ttcl) where ttcl(An, nstep) gives ( An -> TT(n) e. CC )"""
    FM = '( m e. NN |-> %s )' % TT('m'); GM = '( m e. NN |-> ( abs ` %s ) )' % TT('m')
    cv = ap(w, A, 'ld1ttcvg', [F['ha']], concl('ld1ttcvg'))
    cg, _ = w.congr(TT('n'), {'n': 'm'}, 'n = m', {'n': w.s([], 'id', '( n = m -> n = m )')})
    cb = w.s([cg], 'cbvmptv', '( n e. NN |-> %s ) = %s' % (TT('n'), FM))
    cg2 = w.s([cg], 'fveq2d', '( n = m -> ( abs ` %s ) = ( abs ` %s ) )' % (TT('n'), TT('m')))
    cb2 = w.s([cg2], 'cbvmptv', '( n e. NN |-> ( abs ` %s ) ) = %s' % (TT('n'), GM))
    def move(cbst, src, F_):
        s = dst(w, A, [dst(w, A, [w.s([cbst], 'a1i', '( %s -> %s )' % (A, body(w, cbst, '') if False else cbst_formula(w, cbst)))], 'seqeq3d',
                            'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (cbst_lhs(w, cbst), F_))], 'eleq1d',
                '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (cbst_lhs(w, cbst), F_))
        return dst(w, A, [src, s], 'mpbid', 'seq 1 ( + , %s ) e. dom ~~>' % F_)
    cvF = move(cb, dst(w, A, [cv], 'simprd', 'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % TT('n')), FM)
    cvG = move(cb2, dst(w, A, [cv], 'simpld', 'seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~>' % TT('n')), GM)
    def ttcl(An, nstep):
        cn = liftcl(w, A, c, An, basefacts(F)); termcl(w, An, cn, 'n', nstep, F, rp3)
        return cn, cn.mem(TT('n'), 'CC')
    return FM, GM, cvF, cvG, ttcl


def cbst_formula(w, st):
    for l in w.lines:
        if l.startswith(st + ':'):
            return l.split('|- ', 1)[1]
    raise KeyError(st)


def cbst_lhs(w, st):
    return cbst_formula(w, st).split(' = ', 1)[0]


def ld1tailsum():
    w = W('ld1tailsum', 'The tail of the truncated detector series: ` abs sum_ ( n > Nmax ) truncTerm ( n ) <_ 32 Y ^ 2 e ^ ( -u 4 log D ) ` (~ iserabs , ~ isumle , ~ geolim2 , ~ geoisum1c , ~ ld1tailpt , ~ ld1hexp ).')
    A = ante('ld1tailsum'); P, c, F = setup(w, A); F['ha'] = w.s([], 'id', '( %s -> %s )' % (A, A))
    h0, rp3 = hab(w, A, F)
    FM, GM, cvF1, cvG1, ttcl = cvgm(w, A, c, F, rp3)
    Y = YP; M1 = '( %s + 1 )' % NMAX; W_ = '( ZZ>= ` %s )' % M1
    m1n = ap(w, A, 'peano2nn', [F['nn']], '%s e. NN' % M1); m1z = dst(w, A, [m1n], 'nnzd', '%s e. ZZ' % M1)
    z1 = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); zw = w.s([], 'eqid', '%s = %s' % (W_, W_))
    CQ = '( ( 4 x. %s ) x. %s )' % (Y, E4)
    GQ = '( m e. NN |-> ( %s x. ( %s ^ m ) ) )' % (CQ, Q4); FQ = '( m e. NN |-> ( %s ^ m ) )' % Q4
    # q facts
    R4 = '( -u 1 / ( 4 x. %s ) )' % Y
    qr = c.mem(Q4, 'RR'); q0 = c.ge0(Q4); c.leaf(Q4, 'RR', qr); c.leaf(Q4, 'ge0', q0)
    r4n = eqc(w, A, dst(w, A, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A), c.mem('( 4 x. %s )' % Y, 'CC'), c.ne0('( 4 x. %s )' % Y)], 'divnegd', '-u ( 1 / ( 4 x. %s ) ) = %s' % (Y, R4)))
    r4l = linarith(w, A, [r4n], '%s < 0' % R4, closure=c) if False else None
    c.leaf('( 1 / ( 4 x. %s ) )' % Y, 'RR', c.mem('( 1 / ( 4 x. %s ) )' % Y, 'RR')); c.leaf('( 1 / ( 4 x. %s ) )' % Y, 'gt0', c.gt0('( 1 / ( 4 x. %s ) )' % Y))
    r4l = linarith(w, A, [r4n, c.gt0('( 1 / ( 4 x. %s ) )' % Y)], '%s < 0' % R4, closure=c)
    efl = ap(w, A, 'eflt', [c.mem(R4, 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % A)], '( %s < 0 <-> %s < ( exp ` 0 ) )' % (R4, Q4))
    q1 = dst(w, A, [dst(w, A, [r4l, efl], 'mpbid', '%s < ( exp ` 0 )' % Q4), a1(w, A, 'ef0', '( exp ` 0 ) = 1')], 'breqtrd', '%s < 1' % Q4)
    qa = dst(w, A, [dst(w, A, [qr, q0], 'absidd', '( abs ` %s ) = %s' % (Q4, Q4)), q1], 'eqbrtrd', '( abs ` %s ) < 1' % Q4)
    qc = c.mem(Q4, 'CC')
    c.leaf('( 1 - %s )' % Q4, 'gt0', linarith(w, A, [q1], '0 < ( 1 - %s )' % Q4, closure=c))
    # geometric convergences at 1 and at M1
    Ak = '( %s /\\ n e. ( ZZ>= ` 1 ) )' % A
    kn1 = dst(w, Ak, [w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` 1 ) )' % Ak), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrrdi', 'n e. NN')
    ck = liftcl(w, A, c, Ak, basefacts(F) + [(Q4, 'RR', qr)]); ck.leaf('n', 'NN', kn1)
    fq = fvmd(w, Ak, 'm', 'NN', '( %s ^ m )' % Q4, 'n', kn1, ck.mem('( %s ^ n )' % Q4, 'CC'))
    gl = w.s([qc, qa, a1(w, A, '1nn0', '1 e. NN0'), fq], 'geolim2', '( %s -> seq 1 ( + , %s ) ~~> ( ( %s ^ 1 ) / ( 1 - %s ) ) )' % (A, FQ, Q4, Q4))
    An1 = '( %s /\\ n e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> n e. NN )' % An1)
    cn1 = liftcl(w, A, c, An1, basefacts(F) + [(Q4, 'RR', qr), (Q4, 'ge0', q0)]); cn1.leaf('n', 'NN', kn)
    fqn = fvmd(w, An1, 'm', 'NN', '( %s ^ m )' % Q4, 'n', kn, cn1.mem('( %s ^ n )' % Q4, 'CC'))
    gqn = fvmd(w, An1, 'm', 'NN', '( %s x. ( %s ^ m ) )' % (CQ, Q4), 'n', kn, cn1.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'CC'))
    gq = dst(w, An1, [gqn, dst(w, An1, [eqc(w, An1, fqn)], 'oveq2d', '( %s x. ( %s ^ n ) ) = ( %s x. ( %s ` n ) )' % (CQ, Q4, CQ, FQ))], 'eqtrd', '( %s ` n ) = ( %s x. ( %s ` n ) )' % (GQ, CQ, FQ))
    fqc = dst(w, An1, [fqn, cn1.mem('( %s ^ n )' % Q4, 'CC')], 'eqeltrd', '( %s ` n ) e. CC' % FQ)
    LQ = '( ( %s ^ 1 ) / ( 1 - %s ) )' % (Q4, Q4)
    im = w.s([z1, a1(w, A, '1z', '1 e. ZZ'), c.mem(CQ, 'CC'), gl, fqc, gq], 'isermulc2', '( %s -> seq 1 ( + , %s ) ~~> ( %s x. %s ) )' % (A, GQ, CQ, LQ))
    cvq1 = ap(w, A, 'breldmg', [a1(w, A, 'seqex', 'seq 1 ( + , %s ) e. _V' % GQ), c.mem('( %s x. %s )' % (CQ, LQ), 'CC'), im], 'seq 1 ( + , %s ) e. dom ~~>' % GQ)
    gqc1 = dst(w, An1, [gqn, cn1.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'CC')], 'eqeltrd', '( %s ` n ) e. CC' % GQ)
    def tom1(cv1, Fn, fcl):
        ie = w.s([z1, m1n, fcl], 'iserex', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq %s ( + , %s ) e. dom ~~> ) )' % (A, Fn, M1, Fn))
        return dst(w, A, [cv1, ie], 'mpbid', 'seq %s ( + , %s ) e. dom ~~>' % (M1, Fn))
    cn2, ttc = ttcl(An1, kn)
    fv = fvmd(w, An1, 'm', 'NN', TT('m'), 'n', kn, ttc)
    gv = fvmd(w, An1, 'm', 'NN', '( abs ` %s )' % TT('m'), 'n', kn, dst(w, An1, [ttc], 'abscld' if False else 'x', 'x') if False else dst(w, An1, [dst(w, An1, [ttc], 'abscld', '( abs ` %s ) e. RR' % TT('n'))], 'recnd', '( abs ` %s ) e. CC' % TT('n')))
    fvc = dst(w, An1, [fv, ttc], 'eqeltrd', '( %s ` n ) e. CC' % FM)
    gvc = dst(w, An1, [gv, dst(w, An1, [dst(w, An1, [ttc], 'abscld', '( abs ` %s ) e. RR' % TT('n'))], 'recnd', '( abs ` %s ) e. CC' % TT('n'))], 'eqeltrd', '( %s ` n ) e. CC' % GM)
    cvF = tom1(cvF1, FM, fvc); cvG = tom1(cvG1, GM, gvc); cvQ = tom1(cvq1, GQ, gqc1)
    # the values on W
    Aw = '( %s /\\ n e. %s )' % (A, W_)
    nw = w.s([], 'simpr', '( %s -> n e. %s )' % (Aw, W_))
    nnw = ap(w, Aw, 'eluznn', [lift(w, m1n, Aw), nw], 'n e. NN')
    cw, ttw = ttcl(Aw, nnw)
    for e, k_, s_ in [(Q4, 'RR', qr), (Q4, 'ge0', q0)]:
        cw.leaf(e, k_, lift(w, s_, Aw))
    fvw = fvmd(w, Aw, 'm', 'NN', TT('m'), 'n', nnw, ttw)
    absw = dst(w, Aw, [ttw], 'abscld', '( abs ` %s ) e. RR' % TT('n'))
    gvw = fvmd(w, Aw, 'm', 'NN', '( abs ` %s )' % TT('m'), 'n', nnw, dst(w, Aw, [absw], 'recnd', '( abs ` %s ) e. CC' % TT('n')))
    gqw = fvmd(w, Aw, 'm', 'NN', '( %s x. ( %s ^ m ) )' % (CQ, Q4), 'n', nnw, cw.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'CC'))
    SA = 'sum_ n e. %s %s' % (W_, TT('n')); SB = 'sum_ n e. %s ( abs ` %s )' % (W_, TT('n')); SQ = 'sum_ n e. %s ( %s x. ( %s ^ n ) )' % (W_, CQ, Q4)
    clA = w.s([zw, m1z, fvw, ttw, cvF], 'isumclim2', '( %s -> seq %s ( + , %s ) ~~> %s )' % (A, M1, FM, SA))
    clB = w.s([zw, m1z, gvw, dst(w, Aw, [absw], 'recnd', '( abs ` %s ) e. CC' % TT('n')), cvG], 'isumclim2', '( %s -> seq %s ( + , %s ) ~~> %s )' % (A, M1, GM, SB))
    gf = dst(w, Aw, [gvw, dst(w, Aw, [eqc(w, Aw, fvw)], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s ` n ) )' % (TT('n'), FM))], 'eqtrd', '( %s ` n ) = ( abs ` ( %s ` n ) )' % (GM, FM))
    ia = w.s([zw, clA, clB, m1z, dst(w, Aw, [fvw, ttw], 'eqeltrd', '( %s ` n ) e. CC' % FM), gf], 'iserabs', '( %s -> ( abs ` %s ) <_ %s )' % (A, SA, SB))
    # pointwise: abs TT(n) <_ CQ q^n on W
    ge = ap(w, Aw, 'eluzle', [nw], '%s <_ n' % M1)
    pt = ap(w, Aw, 'ld1tailpt', [J(w, Aw, lift(w, F['ha'], Aw), J(w, Aw, nnw, ge))], '( abs ` %s ) <_ ( %s x. ( %s ^ n ) )' % (TT('n'), CQ, Q4))
    il = w.s([zw, m1z, gvw, absw, gqw, cw.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'RR'), pt, cvG, cvQ], 'isumle', '( %s -> %s <_ %s )' % (A, SB, SQ))
    # sum over W <_ sum over NN = CQ q / ( 1 - q )
    Aq = '( %s /\\ n e. NN )' % A
    sp = w.s([z1, zw, m1n, gqn, cn1.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'CC'), cvq1], 'isumsplit',
             '( %s -> sum_ n e. NN ( %s x. ( %s ^ n ) ) = ( sum_ n e. ( 1 ... ( %s - 1 ) ) ( %s x. ( %s ^ n ) ) + %s ) )' % (A, CQ, Q4, M1, CQ, Q4, SQ))
    Af = '( %s /\\ n e. ( 1 ... ( %s - 1 ) ) )' % (A, M1)
    nf = ap(w, Af, 'elfznn', [w.s([], 'simpr', '( %s -> n e. ( 1 ... ( %s - 1 ) ) )' % (Af, M1))], 'n e. NN')
    cf = liftcl(w, A, c, Af, basefacts(F) + [(Q4, 'RR', qr), (Q4, 'ge0', q0)]); cf.leaf('n', 'NN', nf)
    f0 = dst(w, A, [dst(w, A, [], 'fzfid', '( 1 ... ( %s - 1 ) ) e. Fin' % M1), cf.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'RR'), cf.ge0('( %s x. ( %s ^ n ) )' % (CQ, Q4))], 'fsumge0',
             '0 <_ sum_ n e. ( 1 ... ( %s - 1 ) ) ( %s x. ( %s ^ n ) )' % (M1, CQ, Q4))
    gs = ap(w, A, 'geoisum1c', [c.mem(CQ, 'CC'), qc, qa], 'sum_ n e. NN ( %s x. ( %s ^ n ) ) = ( ( %s x. %s ) / ( 1 - %s ) )' % (CQ, Q4, CQ, Q4, Q4))
    SNN = 'sum_ n e. NN ( %s x. ( %s ^ n ) )' % (CQ, Q4); SF = 'sum_ n e. ( 1 ... ( %s - 1 ) ) ( %s x. ( %s ^ n ) )' % (M1, CQ, Q4)
    VQ = '( ( %s x. %s ) / ( 1 - %s ) )' % (CQ, Q4, Q4)
    c.leaf(SQ, 'RR', w.s([zw, m1z, gqw, cw.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'RR'), cvQ], 'isumrecl', '( %s -> %s e. RR )' % (A, SQ)))
    c.leaf(SF, 'RR', dst(w, A, [dst(w, A, [], 'fzfid', '( 1 ... ( %s - 1 ) ) e. Fin' % M1), cf.mem('( %s x. ( %s ^ n ) )' % (CQ, Q4), 'RR')], 'fsumrecl', '%s e. RR' % SF))
    c.leaf(SNN, 'RR', dst(w, A, [gs, c.mem(VQ, 'RR')], 'eqeltrd', '%s e. RR' % SNN))
    wle = linarith(w, A, [sp, f0], '%s <_ %s' % (SQ, SNN), closure=c)
    # VQ <_ 8 Y CQ = TAILC
    R8 = '( 1 / ( 8 x. %s ) )' % Y
    hx = ap(w, A, 'ld1hexp', [J(w, A, c.mem('( 1 / ( 4 x. %s ) )' % Y, 'RR'), c.ge0('( 1 / ( 4 x. %s ) )' % Y), linarith(w, A, [F['y4']], '( 1 / ( 4 x. %s ) ) <_ 1' % Y, closure=c) if False else None)], 'x') if False else None
    R4p = '( 1 / ( 4 x. %s ) )' % Y
    # ( 1 / ( 4 Y ) ) <_ 1 from 4 <_ Y: 1 <_ 4 Y
    le1 = dst(w, A, [linarith(w, A, [F['y4']], '1 <_ ( 4 x. %s )' % Y, closure=c), ap(w, A, 'ledivmul', [w.s([], '1red', '( %s -> 1 e. RR )' % A), w.s([], '1red', '( %s -> 1 e. RR )' % A), J(w, A, c.mem('( 4 x. %s )' % Y, 'RR'), c.gt0('( 4 x. %s )' % Y))],
                                                                                              '( %s <_ 1 <-> 1 <_ ( ( 4 x. %s ) x. 1 ) )' % (R4p, Y))], 'x', 'x') if False else None
    ldm1 = ap(w, A, 'ledivmul', [w.s([], '1red', '( %s -> 1 e. RR )' % A), w.s([], '1red', '( %s -> 1 e. RR )' % A), J(w, A, c.mem('( 4 x. %s )' % Y, 'RR'), c.gt0('( 4 x. %s )' % Y))], '( %s <_ 1 <-> 1 <_ ( ( 4 x. %s ) x. 1 ) )' % (R4p, Y))
    le1 = dst(w, A, [linarith(w, A, [F['y4']], '1 <_ ( ( 4 x. %s ) x. 1 )' % Y, closure=c), ldm1], 'mpbird', '%s <_ 1' % R4p)
    hx = ap(w, A, 'ld1hexp', [J(w, A, c.mem(R4p, 'RR'), c.ge0(R4p), le1)], '( %s / 2 ) <_ ( 1 - ( exp ` -u %s ) )' % (R4p, R4p))
    hx2 = dst(w, A, [dst(w, A, [eqc(w, A, r4n)], 'fveq2d', '( exp ` -u %s ) = %s' % (R4p, Q4))], 'oveq2d', '( 1 - ( exp ` -u %s ) ) = ( 1 - %s )' % (R4p, Q4))
    hx3 = dst(w, A, [hx, hx2], 'breqtrd', '( %s / 2 ) <_ ( 1 - %s )' % (R4p, Q4))
    d8 = eqt(w, A, dst(w, A, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A), c.mem('( 4 x. %s )' % Y, 'CC'), c.mem('2', 'CC'), c.ne0('( 4 x. %s )' % Y), c.ne0('2')], 'divdiv1d', '( %s / 2 ) = ( 1 / ( ( 4 x. %s ) x. 2 ) )' % (R4p, Y)),
             dst(w, A, [ringeq(w, A, '( ( 4 x. %s ) x. 2 )' % Y, '( 8 x. %s )' % Y, c)], 'oveq2d', '( 1 / ( ( 4 x. %s ) x. 2 ) ) = %s' % (Y, R8)))
    h8 = dst(w, A, [d8, hx3], 'eqbrtrrd', '%s <_ ( 1 - %s )' % (R8, Q4))
    rc = dst(w, A, [c.mem('( 8 x. %s )' % Y, 'CC'), c.ne0('( 8 x. %s )' % Y)], 'recidd', '( ( 8 x. %s ) x. %s ) = 1' % (Y, R8))
    h8b = dst(w, A, [eqc(w, A, rc), lemul(w, A, c, h8, '( 8 x. %s )' % Y)], 'eqbrtrd', '1 <_ ( ( 8 x. %s ) x. ( 1 - %s ) )' % (Y, Q4))
    c.leaf(E4, 'RR', c.mem(E4, 'RR')); c.leaf(E4, 'ge0', c.ge0(E4))
    cq0 = c.ge0(CQ)
    ldm2 = ap(w, A, 'ledivmul', [c.mem('( %s x. %s )' % (CQ, Q4), 'RR'), c.mem('( ( 8 x. %s ) x. %s )' % (Y, CQ), 'RR'), J(w, A, c.mem('( 1 - %s )' % Q4, 'RR'), c.gt0('( 1 - %s )' % Q4))],
              '( %s <_ ( ( 8 x. %s ) x. %s ) <-> ( %s x. %s ) <_ ( ( 1 - %s ) x. ( ( 8 x. %s ) x. %s ) ) )' % (VQ, Y, CQ, CQ, Q4, Q4, Y, CQ))
    tc = ringeqp(w, A, '( ( 8 x. %s ) x. %s )' % (Y, CQ), TAILC, c)
    c.leaf(CQ, 'ge0', cq0)
    q1le = ltle(w, A, c, q1)
    s2 = lemul(w, A, c, q1le, CQ)                                                          # CQ Q4 <_ CQ 1
    s3 = lemul(w, A, c, h8b, CQ)                                                           # CQ 1 <_ CQ ( 8Y ( 1 - Q4 ) )
    s4 = dst(w, A, [c.mem('( %s x. %s )' % (CQ, Q4), 'RR'), c.mem('( %s x. 1 )' % CQ, 'RR'), c.mem('( %s x. ( ( 8 x. %s ) x. ( 1 - %s ) ) )' % (CQ, Y, Q4), 'RR'), s2, s3], 'letrd',
             '( %s x. %s ) <_ ( %s x. ( ( 8 x. %s ) x. ( 1 - %s ) ) )' % (CQ, Q4, CQ, Y, Q4))
    nl = dst(w, A, [s4, ringeq(w, A, '( %s x. ( ( 8 x. %s ) x. ( 1 - %s ) ) )' % (CQ, Y, Q4), '( ( 1 - %s ) x. ( ( 8 x. %s ) x. %s ) )' % (Q4, Y, CQ), c)], 'breqtrd',
             '( %s x. %s ) <_ ( ( 1 - %s ) x. ( ( 8 x. %s ) x. %s ) )' % (CQ, Q4, Q4, Y, CQ))
    vb = dst(w, A, [nl, ldm2], 'mpbird', '%s <_ ( ( 8 x. %s ) x. %s )' % (VQ, Y, CQ))
    vb2 = dst(w, A, [vb, tc], 'breqtrd', '%s <_ %s' % (VQ, TAILC))
    c.leaf(VQ, 'RR', c.mem(VQ, 'RR'))
    c.leaf(SB, 'RR', w.s([zw, m1z, gvw, absw, cvG], 'isumrecl', '( %s -> %s e. RR )' % (A, SB)))
    c.leaf('( abs ` %s )' % SA, 'RR', dst(w, A, [w.s([zw, m1z, fvw, ttw, cvF], 'isumcl', '( %s -> %s e. CC )' % (A, SA))], 'abscld', '( abs ` %s ) e. RR' % SA))
    c.leaf(TAILC, 'RR', c.mem(TAILC, 'RR'))
    linarith(w, A, [ia, il, wle, gs, vb2], '( abs ` %s ) <_ %s' % (SA, TAILC), closure=c, name='qed')
    return go(w)


def ld1trunc():
    w = W('ld1trunc', 'Lean ` norm_Fdet_sub_truncation_le ` (L1.c, Lemma 2.4): the half-line detector is within ` 1 / 8 ` of its truncation at ` Nmax ` (~ ld1fdv , ~ isumsplit , ~ ld1tailsum , ~ ld1tailn ).')
    A = ante('ld1trunc'); P, c, F = setup(w, A)
    re0 = linarith(w, A, [P['( ; 3 9 / ; 5 0 ) <_ ( Re ` S )']], '0 <_ ( Re ` S )', closure=c)
    ha = J(w, A, P['( %s /\\ N e. NN )' % HZH], J(w, A, P[CFN], J(w, A, F['sc'], re0)))
    assert body(w, ha, A) == HA
    F['ha'] = ha
    h0, rp3 = hab(w, A, F)
    FM, GM, cvF1, cvG1, ttcl = cvgm(w, A, c, F, rp3)
    M1 = '( %s + 1 )' % NMAX; W_ = '( ZZ>= ` %s )' % M1
    m1n = ap(w, A, 'peano2nn', [F['nn']], '%s e. NN' % M1)
    z1 = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); zw = w.s([], 'eqid', '%s = %s' % (W_, W_))
    An1 = '( %s /\\ n e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> n e. NN )' % An1)
    cn, ttc = ttcl(An1, kn)
    fv = fvmd(w, An1, 'm', 'NN', TT('m'), 'n', kn, ttc)
    sp = w.s([z1, zw, m1n, fv, ttc, cvF1], 'isumsplit', '( %s -> sum_ n e. NN %s = ( sum_ n e. ( 1 ... ( %s - 1 ) ) %s + sum_ n e. %s %s ) )' % (A, TT('n'), M1, TT('n'), W_, TT('n')))
    pc = dst(w, A, [c.mem(NMAX, 'CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'pncand', '( %s - 1 ) = %s' % (M1, NMAX))
    SW = 'sum_ n e. %s %s' % (W_, TT('n'))
    sp2 = eqt(w, A, sp, dst(w, A, [dst(w, A, [dst(w, A, [pc], 'oveq2d', '( 1 ... ( %s - 1 ) ) = %s' % (M1, FZN))], 'sumeq1d', 'sum_ n e. ( 1 ... ( %s - 1 ) ) %s = %s' % (M1, TT('n'), TRUNC))], 'oveq1d',
                                   '( sum_ n e. ( 1 ... ( %s - 1 ) ) %s + %s ) = ( %s + %s )' % (M1, TT('n'), SW, TRUNC, SW)))
    fdv = ap(w, A, 'ld1fdv', [ha], concl('ld1fdv'))
    Af = '( %s /\\ n e. %s )' % (A, FZN)
    nf = ap(w, Af, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Af, FZN))], 'n e. NN')
    cf, ttf = ttcl(Af, nf)
    trc = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % FZN), ttf], 'fsumcl', '%s e. CC' % TRUNC)
    Aw = '( %s /\\ n e. %s )' % (A, W_)
    nw = w.s([], 'simpr', '( %s -> n e. %s )' % (Aw, W_))
    nnw = ap(w, Aw, 'eluznn', [lift(w, m1n, Aw), nw], 'n e. NN')
    cw, ttw = ttcl(Aw, nnw)
    fvw = fvmd(w, Aw, 'm', 'NN', TT('m'), 'n', nnw, ttw)
    fvc = dst(w, An1, [fv, ttc], 'eqeltrd', '( %s ` n ) e. CC' % FM)
    ie = w.s([z1, m1n, fvc], 'iserex', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq %s ( + , %s ) e. dom ~~> ) )' % (A, FM, M1, FM))
    cvF = dst(w, A, [cvF1, ie], 'mpbid', 'seq %s ( + , %s ) e. dom ~~>' % (M1, FM))
    swc = w.s([zw, dst(w, A, [m1n], 'nnzd', '%s e. ZZ' % M1), fvw, ttw, cvF], 'isumcl', '( %s -> %s e. CC )' % (A, SW))
    df = eqt(w, A, dst(w, A, [eqt(w, A, fdv, sp2)], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (FDVH, TRUNC, TRUNC, SW, TRUNC)), dst(w, A, [trc, swc], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (TRUNC, SW, TRUNC, SW)))
    ts = ap(w, A, 'ld1tailsum', [ha], concl('ld1tailsum'))
    tn = ap(w, A, 'ld1tailn', [F['hz']], concl('ld1tailn'))
    lt = dst(w, A, [dst(w, A, [swc], 'abscld', '( abs ` %s ) e. RR' % SW), c.mem(TAILC, 'RR'), c.mem('( 1 / 8 )', 'RR'), ts, tn], 'letrd', '( abs ` %s ) <_ ( 1 / 8 )' % SW)
    dst(w, A, [dst(w, A, [df], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (FDVH, TRUNC, SW)), lt], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( 1 / 8 )' % (FDVH, TRUNC))
    return fin(w)


if __name__ == '__main__':
    for lab in ['ld1fdv', 'ld1ttabs', 'ld1ttcvg', 'ld1hexp', 'ld1xexp', 'ld1tailn', 'ld1tailpt', 'ld1tailsum', 'ld1trunc']:
        if want(lab):
            if not globals()[lab]():
                sys.exit(1)
