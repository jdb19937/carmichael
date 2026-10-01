"""T15 (b): TMLab and TMWalk equations."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *

D30 = '; 3 0'
LABBODY = '( ( TMFam ` ( ; 3 0 - ( # ` w ) ) ) ` w )'


def labval(w, ante, Wd, wm):
    ex = w.s([], 'fvexd', '( %s -> ( ( TMFam ` ( ; 3 0 - ( # ` %s ) ) ) ` %s ) e. _V )' % (ante, Wd, Wd))
    return fvm(w, ante, 'TMLab', 'df-tmlab', 'w', 'Word NN0', LABBODY, Wd, wm, ex)


def tmlabap():
    w = W('tmlabap', 'Applying the address label of W to an index gives the label of the extended address.')
    ph = '( W e. Word NN0 /\\ ( # ` W ) < ; 3 0 /\\ I e. NN0 )'
    wm = w.s([], 'simp1', '( %s -> W e. Word NN0 )' % ph)
    lt = w.s([], 'simp2', '( %s -> ( # ` W ) < ; 3 0 )' % ph)
    im = w.s([], 'simp3', '( %s -> I e. NN0 )' % ph)
    X = '( # ` W )'
    xn = w.s([wm, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, X))
    t30 = w.s([], 'dec0h' if False else '3nn0', '3 e. NN0')
    d30 = w.s([t30, w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 3 0 e. NN0')
    d30d = a1(w, ph, d30, '; 3 0 e. NN0')
    le = w.s([xn, d30d, w.inst('nn0ltp1le')], 'syl2anc', '( %s -> ( %s < ; 3 0 <-> ( %s + 1 ) <_ ; 3 0 ) )' % (ph, X, X))
    le2 = w.s([lt, le], 'mpbid', '( %s -> ( %s + 1 ) <_ ; 3 0 )' % (ph, X))
    x1 = w.s([xn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, X))
    sb = w.s([x1, d30d, w.inst('nn0sub')], 'syl2anc', '( %s -> ( ( %s + 1 ) <_ ; 3 0 <-> ( ; 3 0 - ( %s + 1 ) ) e. NN0 ) )' % (ph, X, X))
    Dm = '( ; 3 0 - ( %s + 1 ) )' % X
    dn = w.s([le2, sb], 'mpbid', '( %s -> %s e. NN0 )' % (ph, Dm))
    # ( Dm + 1 ) = ( 30 - X )
    c30 = w.s([d30d], 'nn0cnd', '( %s -> ; 3 0 e. CC )' % ph)
    xc = w.s([xn], 'nn0cnd', '( %s -> %s e. CC )' % (ph, X))
    one = a1(w, ph, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    e1 = w.s([c30, xc, one], 'subsub4d', '( %s -> ( ( ; 3 0 - %s ) - 1 ) = %s )' % (ph, X, Dm))
    e2 = w.s([e1], 'oveq1d', '( %s -> ( ( ( ; 3 0 - %s ) - 1 ) + 1 ) = ( %s + 1 ) )' % (ph, X, Dm))
    sc = w.s([c30, xc], 'subcld', '( %s -> ( ; 3 0 - %s ) e. CC )' % (ph, X))
    e3 = w.s([sc, w.inst('npcan1')], 'syl', '( %s -> ( ( ( ; 3 0 - %s ) - 1 ) + 1 ) = ( ; 3 0 - %s ) )' % (ph, X, X))
    e4 = w.s([e2, e3], 'eqtr3d', '( %s -> ( %s + 1 ) = ( ; 3 0 - %s ) )' % (ph, Dm, X))
    # left side
    a, _ = labval(w, ph, 'W', wm)
    a2 = w.s([a], 'fveq1d', '( %s -> ( ( TMLab ` W ) ` I ) = ( ( ( TMFam ` ( ; 3 0 - %s ) ) ` W ) ` I ) )' % (ph, X))
    f1 = w.s([e4], 'fveq2d', '( %s -> ( TMFam ` ( %s + 1 ) ) = ( TMFam ` ( ; 3 0 - %s ) ) )' % (ph, Dm, X))
    f2 = w.s([f1], 'fveq1d', '( %s -> ( ( TMFam ` ( %s + 1 ) ) ` W ) = ( ( TMFam ` ( ; 3 0 - %s ) ) ` W ) )' % (ph, Dm, X))
    f3 = w.s([f2], 'fveq1d', '( %s -> ( ( ( TMFam ` ( %s + 1 ) ) ` W ) ` I ) = ( ( ( TMFam ` ( ; 3 0 - %s ) ) ` W ) ` I ) )' % (ph, Dm, X))
    f4 = w.s([dn, wm, im, w.inst('tmfamap')], 'syl3anc', '( %s -> ( ( ( TMFam ` ( %s + 1 ) ) ` W ) ` I ) = ( ( TMFam ` %s ) ` ( W ++ <" I "> ) ) )' % (ph, Dm, Dm))
    lhs = w.s([a2, f3, f4], '3eqtr2d', '( %s -> ( ( TMLab ` W ) ` I ) = ( ( TMFam ` %s ) ` ( W ++ <" I "> ) ) )' % (ph, Dm))
    # right side
    W1 = '( W ++ <" I "> )'
    w1m = w.s([wm, im, w.inst('ccatws1cl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (ph, W1))
    b, _ = labval(w, ph, W1, w1m)
    ln = w.s([wm, w.inst('ccatws1len')], 'syl', '( %s -> ( # ` %s ) = ( %s + 1 ) )' % (ph, W1, X))
    b2 = w.s([ln], 'oveq2d', '( %s -> ( ; 3 0 - ( # ` %s ) ) = %s )' % (ph, W1, Dm))
    b3 = w.s([b2], 'fveq2d', '( %s -> ( TMFam ` ( ; 3 0 - ( # ` %s ) ) ) = ( TMFam ` %s ) )' % (ph, W1, Dm))
    b4 = w.s([b3], 'fveq1d', '( %s -> ( ( TMFam ` ( ; 3 0 - ( # ` %s ) ) ) ` %s ) = ( ( TMFam ` %s ) ` %s ) )' % (ph, W1, W1, Dm, W1))
    rhs = w.s([b, b4], 'eqtrd', '( %s -> ( TMLab ` %s ) = ( ( TMFam ` %s ) ` %s ) )' % (ph, W1, Dm, W1))
    w.qed([lhs, rhs], 'eqtr4d', '( %s -> ( ( TMLab ` W ) ` I ) = ( TMLab ` %s ) )' % (ph, W1))
    return w


def tmlabadr():
    w = W('tmlabadr', 'The address label of W returns W at -u 1.')
    ph = '( W e. Word NN0 /\\ ( # ` W ) <_ ; 3 0 )'
    wm = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % ph)
    le = w.s([], 'simpr', '( %s -> ( # ` W ) <_ ; 3 0 )' % ph)
    X = '( # ` W )'
    xn = w.s([wm, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, X))
    d30 = w.s([w.s([], '3nn0', '3 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 3 0 e. NN0')
    d30d = a1(w, ph, d30, '; 3 0 e. NN0')
    sb = w.s([xn, d30d, w.inst('nn0sub')], 'syl2anc', '( %s -> ( %s <_ ; 3 0 <-> ( ; 3 0 - %s ) e. NN0 ) )' % (ph, X, X))
    dn = w.s([le, sb], 'mpbid', '( %s -> ( ; 3 0 - %s ) e. NN0 )' % (ph, X))
    a, _ = labval(w, ph, 'W', wm)
    a2 = w.s([a], 'fveq1d', '( %s -> ( ( TMLab ` W ) ` -u 1 ) = ( ( ( TMFam ` ( ; 3 0 - %s ) ) ` W ) ` -u 1 ) )' % (ph, X))
    b = w.s([dn, wm, w.inst('tmfamadr')], 'syl2anc', '( %s -> ( ( ( TMFam ` ( ; 3 0 - %s ) ) ` W ) ` -u 1 ) = W )' % (ph, X))
    w.qed([a2, b], 'eqtrd', '( %s -> ( ( TMLab ` W ) ` -u 1 ) = W )' % ph)
    return w


WBODY = '( seq 0 ( %s , ( n e. NN0 |-> if ( n = 0 , r , ( w ` ( n - 1 ) ) ) ) ) ` ( # ` w ) )' % OPA


def walkval(w, ante, R, Wd, rm, wmv):
    """( ante -> ( R TMWalk Wd ) = ( WSEQ ` ( # ` Wd ) ) ); rm, wmv prove R e. _V, Wd e. _V"""
    ex = w.s([], 'fvexd', '( %s -> ( %s ` ( # ` %s ) ) e. _V )' % (ante, WSEQ(R, Wd), Wd))
    return ovm(w, ante, 'TMWalk', 'df-tmwalk', 'r', 'w', '_V', '_V', WBODY, R, Wd, rm, wmv, ex)


def tmwalk0():
    w = W('tmwalk0', 'The walk along the empty address is the trie itself.')
    ph = 'R e. V'
    rm = w.s([], 'elexd' if False else 'elex', '( R e. V -> R e. _V )')
    zm = a1(w, ph, w.s([], '0ex', '(/) e. _V'), '(/) e. _V')
    a, v = walkval(w, ph, 'R', '(/)', rm, zm)
    h0 = a1(w, ph, w.s([], 'hash0', '( # ` (/) ) = 0'), '( # ` (/) ) = 0')
    b = w.s([h0], 'fveq2d', '( %s -> ( %s ` ( # ` (/) ) ) = ( %s ` 0 ) )' % (ph, WSEQ('R', '(/)'), WSEQ('R', '(/)')))
    z = w.s([], '0z', '0 e. ZZ')
    c0 = w.s([z, w.inst('seq1')], 'ax-mp', '( %s ` 0 ) = ( %s ` 0 )' % (WSEQ('R', '(/)'), WF('R', '(/)')))
    c = a1(w, ph, c0, '( %s ` 0 ) = ( %s ` 0 )' % (WSEQ('R', '(/)'), WF('R', '(/)')))
    n0 = a1(w, ph, w.s([], '0nn0', '0 e. NN0'), '0 e. NN0')
    ifx = w.s([], 'ifexd', '( %s -> if ( 0 = 0 , R , ( (/) ` ( 0 - 1 ) ) ) e. _V )' % ph) if False else None
    rv = w.s([rm], 'a1i', '( %s -> ( R e. V -> R e. _V ) )' % ph) if False else None
    rm2 = w.s([], 'elex', '( R e. V -> R e. _V )')
    fx = w.s([], 'fvex', '( (/) ` ( 0 - 1 ) ) e. _V')
    fxd = a1(w, ph, fx, '( (/) ` ( 0 - 1 ) ) e. _V')
    ie = w.s([rm2, fxd], 'ifcld', '( %s -> if ( 0 = 0 , R , ( (/) ` ( 0 - 1 ) ) ) e. _V )' % ph)
    d, v2 = fvm(w, ph, WF('R', '(/)'), None, 'n', 'NN0', 'if ( n = 0 , R , ( (/) ` ( n - 1 ) ) )', '0', n0, ie)
    e0 = w.s([], 'eqid', '0 = 0')
    e = a1(w, ph, w.s([e0], 'iftruei', 'if ( 0 = 0 , R , ( (/) ` ( 0 - 1 ) ) ) = R'), 'if ( 0 = 0 , R , ( (/) ` ( 0 - 1 ) ) ) = R')
    w.qed([a, b, c, d, e], 'eqtrd' if False else 'syl5req', '')
    w.lines.pop()
    s1 = w.s([a, b], 'eqtrd', '( %s -> ( R TMWalk (/) ) = ( %s ` 0 ) )' % (ph, WSEQ('R', '(/)')))
    s2 = w.s([s1, c], 'eqtrd', '( %s -> ( R TMWalk (/) ) = ( %s ` 0 ) )' % (ph, WF('R', '(/)')))
    s3 = w.s([s2, d], 'eqtrd', '( %s -> ( R TMWalk (/) ) = if ( 0 = 0 , R , ( (/) ` ( 0 - 1 ) ) ) )' % ph)
    w.qed([s3, e], 'eqtrd', '( %s -> ( R TMWalk (/) ) = R )' % ph)
    return w


GENS = {'tmlabap': tmlabap, 'tmlabadr': tmlabadr, 'tmwalk0': tmwalk0}


def tmwalks1():
    w = W('tmwalks1', 'The walk along W ++ <" I "> is the walk along W applied to I.')
    ph = '( R e. V /\\ W e. Word U /\\ I e. U )'
    rv = w.s([], 'simp1', '( %s -> R e. V )' % ph)
    rm = w.s([rv], 'elexd', '( %s -> R e. _V )' % ph)
    wm = w.s([], 'simp2', '( %s -> W e. Word U )' % ph)
    im = w.s([], 'simp3', '( %s -> I e. U )' % ph)
    W1 = '( W ++ <" I "> )'
    X = '( # ` W )'
    w1m = w.s([wm, im, w.inst('ccatws1cl')], 'syl2anc', '( %s -> %s e. Word U )' % (ph, W1))
    w1v = w.s([w1m], 'elexd', '( %s -> %s e. _V )' % (ph, W1))
    wv = w.s([wm], 'elexd', '( %s -> W e. _V )' % ph)
    S1_, S0 = WSEQ('R', W1), WSEQ('R', 'W')
    F1, F0_ = WF('R', W1), WF('R', 'W')
    l1, _ = walkval(w, ph, 'R', W1, rm, w1v)
    ln = w.s([wm, w.inst('ccatws1len')], 'syl', '( %s -> ( # ` %s ) = ( %s + 1 ) )' % (ph, W1, X))
    l2 = w.s([ln], 'fveq2d', '( %s -> ( %s ` ( # ` %s ) ) = ( %s ` ( %s + 1 ) ) )' % (ph, S1_, W1, S1_, X))
    xn = w.s([wm, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, X))
    xu = w.s([xn, w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (ph, X))
    B1 = '( %s ` ( %s + 1 ) )' % (F1, X)
    l3 = w.s([xu, w.inst('seqp1')], 'syl', '( %s -> ( %s ` ( %s + 1 ) ) = ( ( %s ` %s ) %s %s ) )' % (ph, S1_, X, S1_, X, OPA, B1))
    # seqfveq
    pk = '( %s /\\ k e. ( 0 ... %s ) )' % (ph, X)
    kf = w.s([], 'simpr', '( %s -> k e. ( 0 ... %s ) )' % (pk, X))
    kn = w.s([kf, w.inst('elfznn0')], 'syl', '( %s -> k e. NN0 )' % pk)
    rm2 = w.s([rm], 'adantr', '( %s -> R e. _V )' % pk)

    def fval(Wd):
        fx = w.s([], 'fvexd', '( %s -> ( %s ` ( k - 1 ) ) e. _V )' % (pk, Wd))
        ie = w.s([rm2, fx], 'ifcld', '( %s -> if ( k = 0 , R , ( %s ` ( k - 1 ) ) ) e. _V )' % (pk, Wd))
        return fvm(w, pk, WF('R', Wd), None, 'n', 'NN0', 'if ( n = 0 , R , ( %s ` ( n - 1 ) ) )' % Wd, 'k', kn, ie)[0]
    g1 = fval(W1)
    g0 = fval('W')
    pn = '( %s /\\ -. k = 0 )' % pk
    k1 = w.s([], 'simpr', '( %s -> -. k = 0 )' % pn)
    k2 = w.s([k1], 'neqned', '( %s -> k =/= 0 )' % pn)
    kf2 = w.s([kf], 'adantr', '( %s -> k e. ( 0 ... %s ) )' % (pn, X))
    k3 = w.s([kf2, k2, w.inst('fzne1')], 'syl2anc', '( %s -> k e. ( ( 0 + 1 ) ... %s ) )' % (pn, X))
    p01 = w.s([], '0p1e1', '( 0 + 1 ) = 1')
    k4 = w.s([p01], 'oveq1i', '( ( 0 + 1 ) ... %s ) = ( 1 ... %s )' % (X, X))
    k5 = w.s([k3, k4], 'eleqtrdi', '( %s -> k e. ( 1 ... %s ) )' % (pn, X))
    k6 = w.s([k5, w.inst('fz1fzo0m1')], 'syl', '( %s -> ( k - 1 ) e. ( 0 ..^ %s ) )' % (pn, X))
    wm3 = w.s([wm], 'ad2antrr', '( %s -> W e. Word U )' % pn)
    im3 = w.s([im], 'ad2antrr', '( %s -> I e. U )' % pn)
    s1m = w.s([im3, w.inst('s1cl')], 'syl', '( %s -> <" I "> e. Word U )' % pn)
    cv = w.s([wm3, s1m, k6, w.inst('ccatval1')], 'syl3anc', '( %s -> ( %s ` ( k - 1 ) ) = ( W ` ( k - 1 ) ) )' % (pn, W1))
    ie = w.s([cv], 'ifeq2da', '( %s -> if ( k = 0 , R , ( %s ` ( k - 1 ) ) ) = if ( k = 0 , R , ( W ` ( k - 1 ) ) ) )' % (pk, W1))
    hk = w.s([g1, ie, g0], '3eqtr4d', '( %s -> ( %s ` k ) = ( %s ` k ) )' % (pk, F1, F0_))
    sq = w.s([xu, hk], 'seqfveq', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, S1_, X, S0, X))
    # B1 = I
    x1n = w.s([xn, w.inst('nn0p1nn')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, X)) if False else None
    x1nn = w.s([xn, w.inst('nn0p1nn')], 'syl', '( %s -> ( %s + 1 ) e. NN )' % (ph, X))
    x1n0 = w.s([x1nn], 'nnnn0d', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, X))
    fx = w.s([], 'fvexd', '( %s -> ( %s ` ( ( %s + 1 ) - 1 ) ) e. _V )' % (ph, W1, X))
    ie2 = w.s([rm, fx], 'ifcld', '( %s -> if ( ( %s + 1 ) = 0 , R , ( %s ` ( ( %s + 1 ) - 1 ) ) ) e. _V )' % (ph, X, W1, X))
    bv, _ = fvm(w, ph, F1, None, 'n', 'NN0', 'if ( n = 0 , R , ( %s ` ( n - 1 ) ) )' % W1, '( %s + 1 )' % X, x1n0, ie2)
    ne = w.s([x1nn], 'nnne0d', '( %s -> ( %s + 1 ) =/= 0 )' % (ph, X))
    ne2 = w.s([ne], 'neneqd', '( %s -> -. ( %s + 1 ) = 0 )' % (ph, X))
    bi = w.s([ne2], 'iffalsed', '( %s -> if ( ( %s + 1 ) = 0 , R , ( %s ` ( ( %s + 1 ) - 1 ) ) ) = ( %s ` ( ( %s + 1 ) - 1 ) ) )' % (ph, X, W1, X, W1, X))
    xc = w.s([xn], 'nn0cnd', '( %s -> %s e. CC )' % (ph, X))
    pc = w.s([xc, w.inst('pncan1')], 'syl', '( %s -> ( ( %s + 1 ) - 1 ) = %s )' % (ph, X, X))
    b3 = w.s([pc], 'fveq2d', '( %s -> ( %s ` ( ( %s + 1 ) - 1 ) ) = ( %s ` %s ) )' % (ph, W1, X, W1, X))
    eqx = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, X, X))
    b4 = w.s([wm, im, eqx, w.inst('ccats1val2')], 'syl3anc', '( %s -> ( %s ` %s ) = I )' % (ph, W1, X))
    bb = w.s([bv, bi, b3, b4], 'eqtrd', '')
    w.lines.pop()
    bb1 = w.s([bv, bi], 'eqtrd', '( %s -> %s = ( %s ` ( ( %s + 1 ) - 1 ) ) )' % (ph, B1, W1, X))
    bb2 = w.s([bb1, b3, b4], '3eqtrd', '( %s -> %s = I )' % (ph, B1))
    l4 = w.s([sq, bb2], 'oveq12d', '( %s -> ( ( %s ` %s ) %s %s ) = ( ( %s ` %s ) %s I ) )' % (ph, S1_, X, OPA, B1, S0, X, OPA))
    zv = w.s([], 'fvexd', '( %s -> ( %s ` %s ) e. _V )' % (ph, S0, X))
    iv = w.s([im], 'elexd', '( %s -> I e. _V )' % ph)
    ex = w.s([], 'fvexd', '( %s -> ( ( %s ` %s ) ` I ) e. _V )' % (ph, S0, X))
    OPC = '( c e. _V , d e. _V |-> ( c ` d ) )'
    cb1 = w.s([], 'fveq1', '( a = c -> ( a ` b ) = ( c ` b ) )')
    cb2 = w.s([], 'fveq2', '( b = d -> ( c ` b ) = ( c ` d ) )')
    cb = w.s([cb1, cb2], 'cbvmpov', '%s = %s' % (OPA, OPC))
    Z = '( %s ` %s )' % (S0, X)
    l5a = a1(w, ph, w.s([cb], 'oveqi', '( %s %s I ) = ( %s %s I )' % (Z, OPA, Z, OPC)), '( %s %s I ) = ( %s %s I )' % (Z, OPA, Z, OPC))
    l5b, _ = ovm(w, ph, OPC, None, 'c', 'd', '_V', '_V', '( c ` d )', Z, 'I', zv, iv, ex)
    l5 = w.s([l5a, l5b], 'eqtrd', '( %s -> ( %s %s I ) = ( %s ` I ) )' % (ph, Z, OPA, Z))
    lhs = w.s([l1, l2, l3], '3eqtrd', '( %s -> ( R TMWalk %s ) = ( ( %s ` %s ) %s %s ) )' % (ph, W1, S1_, X, OPA, B1))
    lhs2 = w.s([lhs, l4, l5], '3eqtrd', '( %s -> ( R TMWalk %s ) = ( ( %s ` %s ) ` I ) )' % (ph, W1, S0, X))
    r1, _ = walkval(w, ph, 'R', 'W', rm, wv)
    r2 = w.s([r1], 'fveq1d', '( %s -> ( ( R TMWalk W ) ` I ) = ( ( %s ` %s ) ` I ) )' % (ph, S0, X))
    w.qed([lhs2, r2], 'eqtr4d', '( %s -> ( R TMWalk %s ) = ( ( R TMWalk W ) ` I ) )' % (ph, W1))
    return w


GENS['tmwalks1'] = tmwalks1


if __name__ == '__main__':
    for lab in sys.argv[1:] or list(GENS):
        GENS[lab]().run()
