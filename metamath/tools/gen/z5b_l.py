"""Sortie Z5b, section L: the kernel hBV and Lemmas 3.2-3.3 (Detector.lean 394-575)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5blib import *
from cl import Closure, lift
import lin


def pp(w, a, mem, v='p'):
    """( a -> v e. Prime ) from mem: ( a -> v e. { q e. Prime | ... } )"""
    return w.s([mem, w.inst('elrabi')], 'syl', '( %s -> %s e. Prime )' % (a, v))


def fmpre(w, a, pnn, p='p'):
    """( a -> FMP(p) e. RR ) from pnn: ( a -> p e. NN )"""
    st = mkst(w, a)
    mu = st([sy(w, a, pnn, 'mucl', '( mmu ` %s ) e. ZZ' % p)], 'zred', '( mmu ` %s ) e. RR' % p)
    ph = st([sy(w, a, pnn, 'phicl', '( phi ` %s ) e. NN' % p)], 'nnred', '( phi ` %s ) e. RR' % p)
    return st([mu, ph], 'remulcld', '%s e. RR' % FMP(p))


def hpre(w, a, pnn, R, S, p='p'):
    """( a -> HP(R,S,p) e. RR )"""
    st = mkst(w, a)
    f = fmpre(w, a, pnn, p)
    one = st([], '1red', '1 e. RR')
    i1 = st([f, one], 'ifcld', '%s e. RR' % IFP(p, R))
    i2 = st([f, one], 'ifcld', '%s e. RR' % IFP(p, S))
    return st([st([i1, i2], 'remulcld', '( %s x. %s ) e. RR' % (IFP(p, R), IFP(p, S))), one], 'resubcld', '%s e. RR' % HP(R, S, p))


def elpf(w, X, v='p'):
    """closed: ( v e. PF(X) <-> ( v e. Prime /\\ v || X ) )"""
    return w.s([w.s([], 'breq1', '( q = %s -> ( q || %s <-> %s || %s ) )' % (v, X, v, X))], 'elrab', '( %s e. %s <-> ( %s e. Prime /\\ %s || %s ) )' % (v, PF(X), v, v, X))


def pfdvd(w, a, mem, X, v='p'):
    """( a -> v || X ) from mem: ( a -> v e. PF(X) )"""
    e = w.s([elpf(w, X, v)], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. Prime /\\ %s || %s ) ) )' % (a, v, PF(X), v, v, X))
    m = w.s([mem, e], 'mpbid', '( %s -> ( %s e. Prime /\\ %s || %s ) )' % (a, v, v, X))
    return w.s([m], 'simprd', '( %s -> %s || %s )' % (a, v, X))


def z5sqfdvd():
    w = W('z5sqfdvd', "A divisor of a squarefree number is squarefree (Lean Squarefree.squarefree_of_dvd): mmu ( D ) = 0 would give "
                      "mmu ( D ( M / D ) ) = 0 by mumullem1.")
    ante = '( %s /\\ ( D e. NN /\\ D || M ) )' % SQF('M')
    st = mkst(w, ante)
    mnn = st([], 'simpll', 'M e. NN'); m0 = st([], 'simplr', '( mmu ` M ) =/= 0')
    dnn = st([], 'simprl', 'D e. NN'); dvm = st([], 'simprr', 'D || M')
    q = st([dvm, st([mnn, dnn, w.inst('nndivdvds')], 'syl2anc', '( D || M <-> ( M / D ) e. NN )')], 'mpbid', '( M / D ) e. NN')
    dc = st([dnn], 'nncnd', 'D e. CC'); mc = st([mnn], 'nncnd', 'M e. CC')
    can = st([mc, dc, st([dnn], 'nnne0d', 'D =/= 0')], 'divcan2d', '( D x. ( M / D ) ) = M')
    b = '( %s /\\ ( mmu ` D ) = 0 )' % ante
    sb = mkst(w, b)
    z = sb([lift(w, dnn, b), lift(w, q, b), sb([], 'simpr', '( mmu ` D ) = 0'), w.inst('mumullem1')], 'syl21anc', '( mmu ` ( D x. ( M / D ) ) ) = 0')
    z2 = sb([sb([lift(w, can, b)], 'fveq2d', '( mmu ` ( D x. ( M / D ) ) ) = ( mmu ` M )'), z], 'eqtr3d', '( mmu ` M ) = 0')
    imp = w.s([z2], 'ex', '( %s -> ( ( mmu ` D ) = 0 -> ( mmu ` M ) = 0 ) )' % ante)
    nc = st([imp], 'necon3d', '( ( mmu ` M ) =/= 0 -> ( mmu ` D ) =/= 0 )')
    w.qed([m0, nc], 'mpd', STATEMENTS['z5sqfdvd'])
    return w


HBB = lambda a, b: '( d e. NN |-> if ( ( mmu ` d ) =/= 0 , prod_ p e. %s %s , 0 ) )' % (PF('d'), HP(a, b, 'p'))


def z5hbvval():
    w = W('z5hbvval', "Value of the product kernel (Lean hBV, hPrime, Detector.lean 394-405): for D in NN, ( ( R hBV S ) ` D ) is "
                      "prod_ p | D hPrime ( p ) if D is squarefree, else 0.")
    ante = '( ( R e. V /\\ S e. W ) /\\ D e. NN )'
    st = mkst(w, ante)
    e1 = cg(w, HBB('a', 'b'), 'a', 'R')
    e2 = cg(w, HBB('R', 'b'), 'b', 'S')
    df = w.s([], 'df-hbv', 'hBV = ( a e. _V , b e. _V |-> %s )' % HBB('a', 'b'))
    ex = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % HBB('R', 'S'))
    ov = w.s([e1, e2, df, ex], 'ovmpo', '( ( R e. _V /\\ S e. _V ) -> ( R hBV S ) = %s )' % HBB('R', 'S'))
    both = st([st([st([], 'simpll', 'R e. V')], 'elexd', 'R e. _V'), st([st([], 'simplr', 'S e. W')], 'elexd', 'S e. _V')], 'jca', '( R e. _V /\\ S e. _V )')
    pv = st([both, ov], 'syl', '( R hBV S ) = %s' % HBB('R', 'S'))
    body = 'if ( ( mmu ` d ) =/= 0 , prod_ p e. %s %s , 0 )' % (PF('d'), HP('R', 'S', 'p'))
    VAL = 'if ( ( mmu ` D ) =/= 0 , prod_ p e. %s %s , 0 )' % (PF('D'), HP('R', 'S', 'p'))
    exv = w.s([w.s([], 'prodex', 'prod_ p e. %s %s e. _V' % (PF('D'), HP('R', 'S', 'p'))), w.s([], 'c0ex', '0 e. _V')], 'ifex', '%s e. _V' % VAL)
    val, v = mpv(w, ante, 'd', 'NN', body, 'D', st([], 'simpr', 'D e. NN'), exs=w.s([exv], 'a1i', '( %s -> %s e. _V )' % (ante, VAL)))
    w.qed([st([pv], 'fveq1d', '( ( R hBV S ) ` D ) = ( %s ` D )' % HBB('R', 'S')), val], 'eqtrd', STATEMENTS['z5hbvval'])
    return w


def z5hbvre():
    w = W('z5hbvre', "The product kernel is real (Lean hBV : RR).")
    ante = '( ( R e. V /\\ S e. W ) /\\ D e. NN )'
    st = mkst(w, ante)
    val = st([st([], 'id', ante), w.inst('z5hbvval')], 'syl', '%s = if ( ( mmu ` D ) =/= 0 , prod_ p e. %s %s , 0 )' % (HB('R', 'S', 'D'), PF('D'), HP('R', 'S', 'p')))
    fin = sy(w, ante, st([], 'simpr', 'D e. NN'), 'pffinq', '%s e. Fin' % PF('D'))
    a = '( %s /\\ p e. %s )' % (ante, PF('D'))
    pn = sy(w, a, pp(w, a, w.s([], 'simpr', '( %s -> p e. %s )' % (a, PF('D')))), 'prmnn', 'p e. NN')
    hr = hpre(w, a, pn, 'R', 'S')
    pr = st([fin, hr], 'fprodrecl', 'prod_ p e. %s %s e. RR' % (PF('D'), HP('R', 'S', 'p')))
    ifr = st([pr, st([], '0red', '0 e. RR')], 'ifcld', 'if ( ( mmu ` D ) =/= 0 , prod_ p e. %s %s , 0 ) e. RR' % (PF('D'), HP('R', 'S', 'p')))
    w.qed([val, ifr], 'eqeltrd', STATEMENTS['z5hbvre'])
    return w


def z5hbvdiv():
    w = W('z5hbvdiv', "The kernel divided by D (Lean hterm of sum_hBV_div_eq): ( hBV ( D ) / D ) = prod_ p | D ( hPrime ( p ) / p ) for "
                      "squarefree D (D = prod_ p | D p), else 0.")
    ante = '( ( R e. V /\\ S e. W ) /\\ D e. NN )'
    st = mkst(w, ante)
    P1 = 'prod_ p e. %s %s' % (PF('D'), HP('R', 'S', 'p'))
    P2 = 'prod_ p e. %s ( %s / p )' % (PF('D'), HP('R', 'S', 'p'))
    C = '( mmu ` D ) =/= 0'
    val = st([st([], 'id', ante), w.inst('z5hbvval')], 'syl', '%s = if ( %s , %s , 0 )' % (HB('R', 'S', 'D'), C, P1))
    e1 = st([val], 'oveq1d', '( %s / D ) = ( if ( %s , %s , 0 ) / D )' % (HB('R', 'S', 'D'), C, P1))
    e2 = w.s([], 'ovif', '( if ( %s , %s , 0 ) / D ) = if ( %s , ( %s / D ) , ( 0 / D ) )' % (C, P1, C, P1))
    e12 = st([e1, w.s([e2], 'a1i', '( %s -> ( if ( %s , %s , 0 ) / D ) = if ( %s , ( %s / D ) , ( 0 / D ) ) )' % (ante, C, P1, C, P1))], 'eqtrd',
             '( %s / D ) = if ( %s , ( %s / D ) , ( 0 / D ) )' % (HB('R', 'S', 'D'), C, P1))
    dnn = st([], 'simpr', 'D e. NN')
    dc = st([dnn], 'nncnd', 'D e. CC'); d0 = st([dnn], 'nnne0d', 'D =/= 0')
    z = st([dc, d0], 'div0d', '( 0 / D ) = 0')
    # true branch under ( ante /\ C )
    b = '( %s /\\ %s )' % (ante, C)
    sb = mkst(w, b)
    sid = sb([lift(w, dnn, b), sb([], 'simpr', C), w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = D' % PF('D'))
    fin = sy(w, b, lift(w, dnn, b), 'pffinq', '%s e. Fin' % PF('D'))
    a = '( %s /\\ p e. %s )' % (b, PF('D'))
    pn = sy(w, a, pp(w, a, w.s([], 'simpr', '( %s -> p e. %s )' % (a, PF('D')))), 'prmnn', 'p e. NN')
    hc = w.s([hpre(w, a, pn, 'R', 'S')], 'recnd', '( %s -> %s e. CC )' % (a, HP('R', 'S', 'p')))
    pc = w.s([pn], 'nncnd', '( %s -> p e. CC )' % a); p0 = w.s([pn], 'nnne0d', '( %s -> p =/= 0 )' % a)
    fd = sb([fin, hc, pc, p0], 'fproddiv', '%s = ( %s / prod_ p e. %s p )' % (P2, P1, PF('D')))
    fd2 = sb([fd, sb([sid], 'oveq2d', '( %s / prod_ p e. %s p ) = ( %s / D )' % (P1, PF('D'), P1))], 'eqtrd', '%s = ( %s / D )' % (P2, P1))
    tb = w.s([sb([fd2], 'eqcomd', '( %s / D ) = %s' % (P1, P2))], 'ifeq1da', '( %s -> if ( %s , ( %s / D ) , ( 0 / D ) ) = if ( %s , %s , ( 0 / D ) ) )' % (ante, C, P1, C, P2))
    fb = st([z], 'ifeq2d', 'if ( %s , %s , ( 0 / D ) ) = if ( %s , %s , 0 )' % (C, P2, C, P2))
    ch = st([e12, tb], 'eqtrd', '( %s / D ) = if ( %s , %s , ( 0 / D ) )' % (HB('R', 'S', 'D'), C, P2))
    w.qed([ch, fb], 'eqtrd', STATEMENTS['z5hbvdiv'])
    return w


def z5psiprod():
    w = W('z5psiprod', "Lean psi_eq_prod: for squarefree R and N in NN, psi_R ( N ) = f ( ( R , N ) ) = prod_ p | N ( if p | R then f ( p ) else 1 ).")
    ante = '( %s /\\ N e. NN )' % SQF('R')
    st = mkst(w, ante)
    rnn = st([], 'simpll', 'R e. NN'); r0 = st([], 'simplr', '( mmu ` R ) =/= 0'); nnn = st([], 'simpr', 'N e. NN')
    g = '( R gcd N )'
    gnn = st([rnn, nnn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % g)
    gd = st([st([rnn], 'nnzd', 'R e. ZZ'), st([nnn], 'nnzd', 'N e. ZZ'), w.inst('gcddvds')], 'syl2anc', '( %s || R /\\ %s || N )' % (g, g))
    gdr = st([gd], 'simpld', '%s || R' % g); gdn = st([gd], 'simprd', '%s || N' % g)
    g0 = st([rnn, r0, gnn, gdr, w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` %s ) =/= 0' % g)
    fp = st([gnn, g0, w.inst('z5fmpprod')], 'syl2anc', '%s = prod_ p e. %s %s' % (FMP(g), PF(g), FMP('p')))
    b = '( %s /\\ p e. Prime )' % ante
    fc = w.s([fmpre(w, b, sy(w, b, w.s([], 'simpr', '( %s -> p e. Prime )' % b), 'prmnn', 'p e. NN'))], 'recnd', '( %s -> %s e. CC )' % (b, FMP('p')))
    pf = w.s([nnn, gnn, gdn, fc], 'z5pfif', '( %s -> prod_ p e. %s if ( p || %s , %s , 1 ) = prod_ p e. %s %s )' % (ante, PF('N'), g, FMP('p'), PF(g), FMP('p')))
    a = '( %s /\\ p e. %s )' % (ante, PF('N'))
    sa = mkst(w, a)
    mem = sa([], 'simpr', 'p e. %s' % PF('N'))
    ppr = pp(w, a, mem)
    pz = sy(w, a, ppr, 'prmz', 'p e. ZZ')
    pdn = pfdvd(w, a, mem, 'N')
    bi1 = sa([pz, sa([lift(w, rnn, a)], 'nnzd', 'R e. ZZ'), sa([lift(w, nnn, a)], 'nnzd', 'N e. ZZ'), w.inst('dvdsgcdb')], 'syl3anc', '( ( p || R /\\ p || N ) <-> p || %s )' % g)
    bi2 = sa([pdn], 'biantrud', '( p || R <-> ( p || R /\\ p || N ) )')
    bi = sa([bi2, bi1], 'bitrd', '( p || R <-> p || %s )' % g)
    ifb = sa([bi], 'ifbid', '%s = if ( p || %s , %s , 1 )' % (IFP('p', 'R'), g, FMP('p')))
    pe = st([ifb], 'prodeq2dv', 'prod_ p e. %s %s = prod_ p e. %s if ( p || %s , %s , 1 )' % (PF('N'), IFP('p', 'R'), PF('N'), g, FMP('p')))
    ch = st([pe, pf], 'eqtrd', 'prod_ p e. %s %s = prod_ p e. %s %s' % (PF('N'), IFP('p', 'R'), PF(g), FMP('p')))
    w.qed([fp, st([ch], 'eqcomd', 'prod_ p e. %s %s = prod_ p e. %s %s' % (PF(g), FMP('p'), PF('N'), IFP('p', 'R')))], 'eqtrd', STATEMENTS['z5psiprod'])
    return w


def z5psipsi():
    w = W('z5psipsi', "Blueprint Lemma 3.2 (Lean psi_mul_psi_eq_sum_hBV, Jutila Lemma 2): psi_R ( N ) psi_S ( N ) = sum_ d | N hBV ( d ; R , S ) "
                      "for squarefree R, S and N in NN (the engine z5sqfeul at the summand hPrime).")
    ante = '( %s /\\ %s /\\ N e. NN )' % (SQF('R'), SQF('S'))
    st = mkst(w, ante)
    sr = st([], 'simp1', SQF('R')); ss_ = st([], 'simp2', SQF('S')); nnn = st([], 'simp3', 'N e. NN')
    rnn = st([sr], 'simpld', 'R e. NN'); snn = st([ss_], 'simpld', 'S e. NN')
    DVN = DV('N')
    IFS = 'if ( ( mmu ` d ) =/= 0 , prod_ p e. %s %s , 0 )' % (PF('d'), HP('R', 'S', 'p'))
    a = '( %s /\\ d e. %s )' % (ante, DVN)
    dn = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (a, DVN)), w.inst('elrabi')], 'syl', '( %s -> d e. NN )' % a)
    hv = w.s([lift(w, rnn, a), lift(w, snn, a), dn, w.inst('z5hbvval')], 'syl21anc', '( %s -> %s = %s )' % (a, HB('R', 'S', 'd'), IFS))
    s1 = st([hv], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (DVN, HB('R', 'S', 'd'), DVN, IFS))
    b = '( %s /\\ p e. Prime )' % ante
    hc = w.s([hpre(w, b, sy(w, b, w.s([], 'simpr', '( %s -> p e. Prime )' % b), 'prmnn', 'p e. NN'), 'R', 'S')], 'recnd', '( %s -> %s e. CC )' % (b, HP('R', 'S', 'p')))
    s2 = w.s([nnn, hc], 'z5sqfeul', '( %s -> sum_ d e. %s %s = prod_ p e. %s ( 1 + %s ) )' % (ante, DVN, IFS, PF('N'), HP('R', 'S', 'p')))
    c = '( %s /\\ p e. %s )' % (ante, PF('N'))
    sc = mkst(w, c)
    pn = sy(w, c, pp(w, c, sc([], 'simpr', 'p e. %s' % PF('N'))), 'prmnn', 'p e. NN')
    f = fmpre(w, c, pn)
    one = sc([], '1red', '1 e. RR')
    i1 = sc([sc([f, one], 'ifcld', '%s e. RR' % IFP('p', 'R'))], 'recnd', '%s e. CC' % IFP('p', 'R'))
    i2 = sc([sc([f, one], 'ifcld', '%s e. RR' % IFP('p', 'S'))], 'recnd', '%s e. CC' % IFP('p', 'S'))
    X = '( %s x. %s )' % (IFP('p', 'R'), IFP('p', 'S'))
    xc = sc([i1, i2], 'mulcld', '%s e. CC' % X)
    pc = sc([sc([], '1cnd', '1 e. CC'), xc, w.inst('pncan3')], 'syl2anc', '( 1 + %s ) = %s' % (HP('R', 'S', 'p'), X))
    s3 = st([pc], 'prodeq2dv', 'prod_ p e. %s ( 1 + %s ) = prod_ p e. %s %s' % (PF('N'), HP('R', 'S', 'p'), PF('N'), X))
    fin = sy(w, ante, nnn, 'pffinq', '%s e. Fin' % PF('N'))
    PR = 'prod_ p e. %s %s' % (PF('N'), IFP('p', 'R')); PS = 'prod_ p e. %s %s' % (PF('N'), IFP('p', 'S'))
    s4 = st([fin, i1, i2], 'fprodmul', 'prod_ p e. %s %s = ( %s x. %s )' % (PF('N'), X, PR, PS))
    q1 = st([sr, nnn, w.inst('z5psiprod')], 'syl2anc', '%s = %s' % (PSI('R', 'N'), PR))
    q2 = st([ss_, nnn, w.inst('z5psiprod')], 'syl2anc', '%s = %s' % (PSI('S', 'N'), PS))
    q = st([q1, q2], 'oveq12d', '( %s x. %s ) = ( %s x. %s )' % (PSI('R', 'N'), PSI('S', 'N'), PR, PS))
    L = 'sum_ d e. %s %s' % (DVN, HB('R', 'S', 'd'))
    c1 = st([s1, s2], 'eqtrd', '%s = prod_ p e. %s ( 1 + %s )' % (L, PF('N'), HP('R', 'S', 'p')))
    c2 = st([c1, s3], 'eqtrd', '%s = prod_ p e. %s %s' % (L, PF('N'), X))
    c3 = st([c2, s4], 'eqtrd', '%s = ( %s x. %s )' % (L, PR, PS))
    w.qed([q, c3], 'eqtr4d', STATEMENTS['z5psipsi'])
    return w


def ifv(w, a, P, R, dvd, truth):
    """( a -> IFP(P,R) = v ) with v = -u ( P - 1 ) (dvd: ( a -> P || R ), truth) or 1 (dvd: ( a -> -. P || R ))"""
    if truth:
        t = w.s([dvd], 'iftrued', '( %s -> %s = %s )' % (a, IFP(P, R), FMP(P)))
        return t, FMP(P)
    return w.s([dvd], 'iffalsed', '( %s -> %s = 1 )' % (a, IFP(P, R))), '1'


def fmpv(w, a, ppr, P='P'):
    """( a -> FMP(P) = -u ( P - 1 ) )"""
    return sy(w, a, ppr, 'z5fmpprm', '%s = -u ( %s - 1 )' % (FMP(P), P))


def z5hpone():
    w = W('z5hpone', "The Euler factor of Lemma 3.3(a) at a prime dividing exactly one of R, S vanishes: hPrime ( p ) = f ( p ) - 1 = - p, "
                     "so 1 + hPrime ( p ) / p = 0 (Lean sum_hBV_div_eq, hzero).")
    ante = '( P e. Prime /\\ ( P || R /\\ -. P || S ) )'
    st = mkst(w, ante)
    ppr = st([], 'simpl', 'P e. Prime')
    pnn = sy(w, ante, ppr, 'prmnn', 'P e. NN')
    pr = st([pnn], 'nnred', 'P e. RR'); pc = st([pnn], 'nncnd', 'P e. CC'); p0 = st([pnn], 'nnne0d', 'P =/= 0')
    tR = st([st([], 'simprl', 'P || R')], 'iftrued', '%s = %s' % (IFP('P', 'R'), FMP('P')))
    tR = st([tR, fmpv(w, ante, ppr)], 'eqtrd', '%s = -u ( P - 1 )' % IFP('P', 'R'))
    tS = st([st([], 'simprr', '-. P || S')], 'iffalsed', '%s = 1' % IFP('P', 'S'))
    hx, x = w.rewrite(HP('R', 'S', 'P'), {IFP('P', 'R'): ('-u ( P - 1 )', tR), IFP('P', 'S'): ('1', tS)}, ante)
    lv = {'P': ('RR', pr)}
    xe = lin.lineq(w, ante, x, '-u P', leaves=lv)
    hp = st([hx, xe], 'eqtrd', '%s = -u P' % HP('R', 'S', 'P'))
    d1 = st([hp], 'oveq1d', '( %s / P ) = ( -u P / P )' % HP('R', 'S', 'P'))
    d2 = st([st([pc, pc, p0], 'divnegd', '-u ( P / P ) = ( -u P / P )')], 'eqcomd', '( -u P / P ) = -u ( P / P )')
    d3 = st([st([pc, p0], 'dividd', '( P / P ) = 1')], 'negeqd', '-u ( P / P ) = -u 1')
    d = st([st([d1, d2], 'eqtrd', '( %s / P ) = -u ( P / P )' % HP('R', 'S', 'P')), d3], 'eqtrd', '( %s / P ) = -u 1' % HP('R', 'S', 'P'))
    e = st([d], 'oveq2d', '( 1 + ( %s / P ) ) = ( 1 + -u 1 )' % HP('R', 'S', 'P'))
    w.qed([e, st([st([], '1cnd', '1 e. CC')], 'negidd', '( 1 + -u 1 ) = 0')], 'eqtrd', STATEMENTS['z5hpone'])
    return w


def z5hptwo():
    w = W('z5hptwo', "The Euler factor of Lemma 3.3(a) at a prime dividing both R and S: hPrime ( p ) = ( p - 1 ) ^ 2 - 1 = p ( p - 2 ), "
                     "so 1 + hPrime ( p ) / p = p - 1 (Lean sum_hBV_div_eq, the case r = r').")
    ante = '( P e. Prime /\\ ( P || R /\\ P || S ) )'
    st = mkst(w, ante)
    ppr = st([], 'simpl', 'P e. Prime')
    pnn = sy(w, ante, ppr, 'prmnn', 'P e. NN')
    pr = st([pnn], 'nnred', 'P e. RR'); pc = st([pnn], 'nncnd', 'P e. CC'); p0 = st([pnn], 'nnne0d', 'P =/= 0')
    fv = fmpv(w, ante, ppr)
    tR = st([st([st([], 'simprl', 'P || R')], 'iftrued', '%s = %s' % (IFP('P', 'R'), FMP('P'))), fv], 'eqtrd', '%s = -u ( P - 1 )' % IFP('P', 'R'))
    tS = st([st([st([], 'simprr', 'P || S')], 'iftrued', '%s = %s' % (IFP('P', 'S'), FMP('P'))), fv], 'eqtrd', '%s = -u ( P - 1 )' % IFP('P', 'S'))
    hx, x = w.rewrite(HP('R', 'S', 'P'), {IFP('P', 'R'): ('-u ( P - 1 )', tR), IFP('P', 'S'): ('-u ( P - 1 )', tS)}, ante)
    lv = {'P': ('RR', pr)}
    xe = lin.lineq(w, ante, x, '( P x. ( P - 2 ) )', leaves=lv, products=True)
    hp = st([hx, xe], 'eqtrd', '%s = ( P x. ( P - 2 ) )' % HP('R', 'S', 'P'))
    d1 = st([hp], 'oveq1d', '( %s / P ) = ( ( P x. ( P - 2 ) ) / P )' % HP('R', 'S', 'P'))
    p2c = st([pc, st([], '2cnd', '2 e. CC')], 'subcld', '( P - 2 ) e. CC')
    d2 = st([p2c, pc, p0], 'divcan3d', '( ( P x. ( P - 2 ) ) / P ) = ( P - 2 )')
    d = st([d1, d2], 'eqtrd', '( %s / P ) = ( P - 2 )' % HP('R', 'S', 'P'))
    e = st([d], 'oveq2d', '( 1 + ( %s / P ) ) = ( 1 + ( P - 2 ) )' % HP('R', 'S', 'P'))
    e2 = lin.lineq(w, ante, '( 1 + ( P - 2 ) )', '( P - 1 )', leaves=lv)
    w.qed([e, e2], 'eqtrd', STATEMENTS['z5hptwo'])
    return w


def pfside(w, X, Y):
    """closed: ( ( c e. PF(X) /\\ -. c e. PF(Y) ) -> ( c e. Prime /\\ ( c || X /\\ -. c || Y ) ) )"""
    A = '( c e. %s /\\ -. c e. %s )' % (PF(X), PF(Y))
    sa = mkst(w, A)
    m1 = sa([sa([], 'simpl', 'c e. %s' % PF(X)), elpf(w, X, 'c')], 'sylib', '( c e. Prime /\\ c || %s )' % X)
    n1 = sa([sa([], 'simpr', '-. c e. %s' % PF(Y)), elpf(w, Y, 'c')], 'sylnib', '-. ( c e. Prime /\\ c || %s )' % Y)
    cp = sa([m1], 'simpld', 'c e. Prime'); cx = sa([m1], 'simprd', 'c || %s' % X)
    n2 = sa([n1, w.s([], 'imnan', '( ( c e. Prime -> -. c || %s ) <-> -. ( c e. Prime /\\ c || %s ) )' % (Y, Y))], 'sylibr', '( c e. Prime -> -. c || %s )' % Y)
    ny = sa([cp, n2], 'mpd', '-. c || %s' % Y)
    return sa([cp, sa([cx, ny], 'jca', '( c || %s /\\ -. c || %s )' % (X, Y))], 'jca', '( c e. Prime /\\ ( c || %s /\\ -. c || %s ) )' % (X, Y))


def z5sqfne():
    w = W('z5sqfne', "Two distinct squarefree numbers R =/= S have a prime dividing exactly one of them (Lean sum_hBV_div_eq, hne and "
                     "Finset.symmDiff_nonempty): equal prime sets would give R = prod_ p | R p = prod_ p | S p = S.")
    ante = '( %s /\\ R =/= S )' % HRS
    st = mkst(w, ante)
    sr = st([], 'simpll', SQF('R')); ss_ = st([], 'simplr', SQF('S'))
    A = PF('R'); B = PF('S')
    b = '( %s /\\ %s = %s )' % (ante, A, B)
    sb = mkst(w, b)
    r1 = sb([lift(w, sr, b), w.inst('sqfprodid')], 'syl', 'prod_ p e. %s p = R' % A)
    s1 = sb([lift(w, ss_, b), w.inst('sqfprodid')], 'syl', 'prod_ p e. %s p = S' % B)
    pe = sb([sb([], 'simpr', '%s = %s' % (A, B))], 'prodeq1d', 'prod_ p e. %s p = prod_ p e. %s p' % (A, B))
    rs = sb([sb([r1], 'eqcomd', 'R = prod_ p e. %s p' % A), pe], 'eqtrd', 'R = prod_ p e. %s p' % B)
    rs = sb([rs, s1], 'eqtrd', 'R = S')
    imp = w.s([rs], 'ex', '( %s -> ( %s = %s -> R = S ) )' % (ante, A, B))
    nrs = st([st([], 'simpr', 'R =/= S')], 'neneqd', '-. R = S')
    nab = st([nrs, imp], 'mtod', '-. %s = %s' % (A, B))
    e1 = st([nab, w.s([], 'eqss', '( %s = %s <-> ( %s C_ %s /\\ %s C_ %s ) )' % (A, B, A, B, B, A))], 'sylnib', '-. ( %s C_ %s /\\ %s C_ %s )' % (A, B, B, A))
    e2 = st([e1, w.s([], 'ianor', '( -. ( %s C_ %s /\\ %s C_ %s ) <-> ( -. %s C_ %s \\/ -. %s C_ %s ) )' % (A, B, B, A, A, B, B, A))], 'sylib',
            '( -. %s C_ %s \\/ -. %s C_ %s )' % (A, B, B, A))
    D1 = '( c || R /\\ -. c || S )'; D2 = '( c || S /\\ -. c || R )'
    def side(X, Y, Dx):
        ns = w.s([], 'nss', '( -. %s C_ %s <-> E. c ( c e. %s /\\ -. c e. %s ) )' % (PF(X), PF(Y), PF(X), PF(Y)))
        ex = w.s([pfside(w, X, Y)], 'eximi', '( E. c ( c e. %s /\\ -. c e. %s ) -> E. c ( c e. Prime /\\ %s ) )' % (PF(X), PF(Y), Dx))
        dr = w.s([], 'df-rex', '( E. c e. Prime %s <-> E. c ( c e. Prime /\\ %s ) )' % (Dx, Dx))
        ex2 = w.s([ex, dr], 'sylibr', '( E. c ( c e. %s /\\ -. c e. %s ) -> E. c e. Prime %s )' % (PF(X), PF(Y), Dx))
        return w.s([ns, ex2], 'sylbi', '( -. %s C_ %s -> E. c e. Prime %s )' % (PF(X), PF(Y), Dx))
    o = w.s([side('R', 'S', D1), side('S', 'R', D2)], 'orim12i', '( ( -. %s C_ %s \\/ -. %s C_ %s ) -> ( E. c e. Prime %s \\/ E. c e. Prime %s ) )' % (A, B, B, A, D1, D2))
    o2 = st([e2, o], 'syl', '( E. c e. Prime %s \\/ E. c e. Prime %s )' % (D1, D2))
    r = w.s([], 'r19.43', '( E. c e. Prime ( %s \\/ %s ) <-> ( E. c e. Prime %s \\/ E. c e. Prime %s ) )' % (D1, D2, D1, D2))
    w.qed([o2, r], 'sylibr', STATEMENTS['z5sqfne'])
    return w


def fterm(w, a, pnn, p='p', R='R', S='S'):
    """( a -> ( HP / p ) e. CC ), ( a -> ( 1 + ( HP / p ) ) e. CC )"""
    st = mkst(w, a)
    hc = st([hpre(w, a, pnn, R, S, p)], 'recnd', '%s e. CC' % HP(R, S, p))
    q = st([hc, st([pnn], 'nncnd', '%s e. CC' % p), st([pnn], 'nnne0d', '%s =/= 0' % p)], 'divcld', '( %s / %s ) e. CC' % (HP(R, S, p), p))
    f = st([st([], '1cnd', '1 e. CC'), q], 'addcld', '( 1 + ( %s / %s ) ) e. CC' % (HP(R, S, p), p))
    return q, f


def z5hbvorth():
    w = W('z5hbvorth', "Blueprint Lemma 3.3(a) (Lean sum_hBV_div_eq, EXACT ORTHOGONALITY, Jutila Lemma 3): for squarefree R, S, "
                       "sum_ d | R S hBV ( d ; R , S ) / d = phi ( R ) if R = S and 0 otherwise.")
    ante = HRS
    st = mkst(w, ante)
    rnn = st([], 'simpll', 'R e. NN'); snn = st([], 'simprl', 'S e. NN')
    RS = '( R x. S )'
    rsn = st([rnn, snn], 'nnmulcld', '%s e. NN' % RS)
    DVN = DV(RS)
    F = lambda p: '( 1 + ( %s / %s ) )' % (HP('R', 'S', p), p)
    BP = '( %s / p )' % HP('R', 'S', 'p')
    IFD = 'if ( ( mmu ` d ) =/= 0 , prod_ p e. %s %s , 0 )' % (PF('d'), BP)
    a = '( %s /\\ d e. %s )' % (ante, DVN)
    dn = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (a, DVN)), w.inst('elrabi')], 'syl', '( %s -> d e. NN )' % a)
    hv = w.s([lift(w, rnn, a), lift(w, snn, a), dn, w.inst('z5hbvdiv')], 'syl21anc', '( %s -> ( %s / d ) = %s )' % (a, HB('R', 'S', 'd'), IFD))
    L = 'sum_ d e. %s ( %s / d )' % (DVN, HB('R', 'S', 'd'))
    s1 = st([hv], 'sumeq2dv', '%s = sum_ d e. %s %s' % (L, DVN, IFD))
    b0 = '( %s /\\ p e. Prime )' % ante
    q0, f0 = fterm(w, b0, sy(w, b0, w.s([], 'simpr', '( %s -> p e. Prime )' % b0), 'prmnn', 'p e. NN'))
    PR = 'prod_ p e. %s %s' % (PF(RS), F('p'))
    s2 = w.s([rsn, q0], 'z5sqfeul', '( %s -> sum_ d e. %s %s = %s )' % (ante, DVN, IFD, PR))
    # case R = S
    b = '( %s /\\ R = S )' % ante
    c = '( %s /\\ p e. %s )' % (b, PF(RS))
    sc = mkst(w, c)
    mem = sc([], 'simpr', 'p e. %s' % PF(RS))
    ppr = pp(w, c, mem)
    pnn = sy(w, c, ppr, 'prmnn', 'p e. NN')
    rz = sc([lift(w, rnn, c)], 'nnzd', 'R e. ZZ'); sz = sc([lift(w, snn, c)], 'nnzd', 'S e. ZZ')
    eu = sc([ppr, rz, sz, w.inst('euclemma')], 'syl3anc', '( p || %s <-> ( p || R \\/ p || S ) )' % RS)
    orr = sc([pfdvd(w, c, mem, RS), eu], 'mpbid', '( p || R \\/ p || S )')
    req = sc([], 'simplr', 'R = S')
    brq = sc([req], 'breq2d', '( p || R <-> p || S )')
    pr_ = sc([sc([], 'idd', '( p || R -> p || R )'), sc([brq], 'biimprd', '( p || S -> p || R )')], 'jaod', '( ( p || R \\/ p || S ) -> p || R )')
    pr_ = sc([orr, pr_], 'mpd', 'p || R')
    ps_ = sc([pr_, brq], 'mpbid', 'p || S')
    two = sc([ppr, pr_, ps_, w.inst('z5hptwo')], 'syl12anc', '%s = ( p - 1 )' % F('p'))
    IFm = 'if ( p || R , ( p - 1 ) , 1 )'
    itr = sc([pr_], 'iftrued', '%s = ( p - 1 )' % IFm)
    fe = sc([two, itr], 'eqtr4d', '%s = %s' % (F('p'), IFm))
    pe = w.s([fe], 'prodeq2dv', '( %s -> %s = prod_ p e. %s %s )' % (b, PR, PF(RS), IFm))
    bb = '( %s /\\ p e. Prime )' % b
    pm1 = w.s([w.s([sy(w, bb, w.s([], 'simpr', '( %s -> p e. Prime )' % bb), 'prmnn', 'p e. NN')], 'nncnd', '( %s -> p e. CC )' % bb),
               w.s([], '1cnd', '( %s -> 1 e. CC )' % bb)], 'subcld', '( %s -> ( p - 1 ) e. CC )' % bb)
    rdv = lift(w, st([st([rnn], 'nnzd', 'R e. ZZ'), st([snn], 'nnzd', 'S e. ZZ'), w.inst('dvdsmul1')], 'syl2anc', 'R || %s' % RS), b)
    pf = w.s([lift(w, rsn, b), lift(w, rnn, b), rdv, pm1], 'z5pfif', '( %s -> prod_ p e. %s %s = prod_ p e. %s ( p - 1 ) )' % (b, PF(RS), IFm, PF('R')))
    ph_ = w.s([lift(w, st([], 'simpl', SQF('R')), b), w.inst('phisqf')], 'syl', '( %s -> ( phi ` R ) = prod_ p e. %s ( p - 1 ) )' % (b, PF('R')))
    caseT = w.s([w.s([pe, pf], 'eqtrd', '( %s -> %s = prod_ p e. %s ( p - 1 ) )' % (b, PR, PF('R'))), ph_], 'eqtr4d', '( %s -> %s = ( phi ` R ) )' % (b, PR))
    # case -. R = S
    b2 = '( %s /\\ -. R = S )' % ante
    ne = w.s([w.s([], 'simpr', '( %s -> -. R = S )' % b2)], 'neqned', '( %s -> R =/= S )' % b2)
    D1 = '( c || R /\\ -. c || S )'; D2 = '( c || S /\\ -. c || R )'
    DJ = '( %s \\/ %s )' % (D1, D2)
    exs = w.s([w.s([], 'simpl', '( %s -> %s )' % (b2, ante)), ne, w.inst('z5sqfne')], 'syl2anc', '( %s -> E. c e. Prime %s )' % (b2, DJ))
    e = '( ( %s /\\ c e. Prime ) /\\ %s )' % (b2, DJ)
    se = mkst(w, e)
    cpr = se([], 'simplr', 'c e. Prime'); dj = se([], 'simpr', DJ)
    cz = sy(w, e, cpr, 'prmz', 'c e. ZZ')
    rze = se([lift(w, rnn, e)], 'nnzd', 'R e. ZZ'); sze = se([lift(w, snn, e)], 'nnzd', 'S e. ZZ')
    o1 = w.s([w.s([], 'simpl', '( %s -> c || R )' % D1)], 'a1i', '( %s -> ( %s -> c || R ) )' % (e, D1))
    o2 = w.s([w.s([], 'simpl', '( %s -> c || S )' % D2)], 'a1i', '( %s -> ( %s -> c || S ) )' % (e, D2))
    oo = se([dj, se([o1, o2], 'orim12d', '( %s -> ( c || R \\/ c || S ) )' % DJ)], 'mpd', '( c || R \\/ c || S )')
    cd = se([oo, se([cpr, rze, sze, w.inst('euclemma')], 'syl3anc', '( c || %s <-> ( c || R \\/ c || S ) )' % RS)], 'mpbird', 'c || %s' % RS)
    cin = se([se([cpr, cd], 'jca', '( c e. Prime /\\ c || %s )' % RS), w.s([elpf(w, RS, 'c')], 'a1i', '( %s -> ( c e. %s <-> ( c e. Prime /\\ c || %s ) ) )' % (e, PF(RS), RS))],
             'mpbird', 'c e. %s' % PF(RS))
    z1 = w.s([w.s([cpr, w.inst('z5hpone')], 'sylan', '( ( %s /\\ %s ) -> %s = 0 )' % (e, D1, F('c')))], 'ex', '( %s -> ( %s -> %s = 0 ) )' % (e, D1, F('c')))
    Fsr = '( 1 + ( %s / c ) )' % HP('S', 'R', 'c')
    z2a = w.s([cpr, w.inst('z5hpone')], 'sylan', '( ( %s /\\ %s ) -> %s = 0 )' % (e, D2, Fsr))
    cnn = sy(w, e, cpr, 'prmnn', 'c e. NN')
    fce = fmpre(w, e, cnn, 'c')
    one = se([], '1red', '1 e. RR')
    iR = se([se([fce, one], 'ifcld', '%s e. RR' % IFP('c', 'R'))], 'recnd', '%s e. CC' % IFP('c', 'R'))
    iS = se([se([fce, one], 'ifcld', '%s e. RR' % IFP('c', 'S'))], 'recnd', '%s e. CC' % IFP('c', 'S'))
    mc = se([iS, iR], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (IFP('c', 'S'), IFP('c', 'R'), IFP('c', 'R'), IFP('c', 'S')))
    hsr = se([mc], 'oveq1d', '%s = %s' % (HP('S', 'R', 'c'), HP('R', 'S', 'c')))
    fsr = se([se([hsr], 'oveq1d', '( %s / c ) = ( %s / c )' % (HP('S', 'R', 'c'), HP('R', 'S', 'c')))], 'oveq2d', '%s = %s' % (Fsr, F('c')))
    e2_ = '( %s /\\ %s )' % (e, D2)
    z2b = w.s([lift(w, fsr, e2_), z2a], 'eqtr3d', '( %s -> %s = 0 )' % (e2_, F('c')))
    z2 = w.s([z2b], 'ex', '( %s -> ( %s -> %s = 0 ) )' % (e, D2, F('c')))
    zc = se([dj, se([z1, z2], 'jaod', '( %s -> %s = 0 )' % (DJ, F('c')))], 'mpd', '%s = 0' % F('c'))
    fin = sy(w, e, lift(w, rsn, e), 'pffinq', '%s e. Fin' % PF(RS))
    ep = '( %s /\\ p e. %s )' % (e, PF(RS))
    q1, f1 = fterm(w, ep, sy(w, ep, pp(w, ep, w.s([], 'simpr', '( %s -> p e. %s )' % (ep, PF(RS)))), 'prmnn', 'p e. NN'))
    eq_ = '( %s /\\ p = c )' % e
    idp = w.s([], 'simpr', '( %s -> p = c )' % eq_)
    cgp, newf = w.congr(F('p'), {'p': 'c'}, eq_, {'p': idp})
    b0z = w.s([cgp, lift(w, zc, eq_)], 'eqtrd', '( %s -> %s = 0 )' % (eq_, F('p')))
    z0 = w.s([w.s([], 'nfv', 'F/ p %s' % e), fin, f1, cin, b0z], 'fprodeq0g', '( %s -> %s = 0 )' % (e, PR))
    rx = w.s([w.s([z0], 'ex', '( ( %s /\\ c e. Prime ) -> ( %s -> %s = 0 ) )' % (b2, DJ, PR))], 'rexlimdva', '( %s -> ( E. c e. Prime %s -> %s = 0 ) )' % (b2, DJ, PR))
    caseF = w.s([exs, rx], 'mpd', '( %s -> %s = 0 )' % (b2, PR))
    IFR = 'if ( R = S , ( phi ` R ) , 0 )'
    ib = w.s([w.s([], 'eqeq2', '( ( phi ` R ) = %s -> ( %s = ( phi ` R ) <-> %s = %s ) )' % (IFR, PR, PR, IFR)),
              w.s([], 'eqeq2', '( 0 = %s -> ( %s = 0 <-> %s = %s ) )' % (IFR, PR, PR, IFR)), caseT, caseF], 'ifbothda', '( %s -> %s = %s )' % (ante, PR, IFR))
    ch = st([s1, s2], 'eqtrd', '%s = %s' % (L, PR))
    w.qed([ch, ib], 'eqtrd', STATEMENTS['z5hbvorth'])
    return w


def z5hpabs():
    w = W('z5hpabs', "Lean sum_abs_hBV_le, hUI and hI: at a prime P, 1 + | hPrime ( P ) | <_ ( P + 1 ) ^ [ P | R ] ( P + 1 ) ^ [ P | S ] "
                     "(hPrime = ( P - 1 ) ^ 2 - 1, - P or 0).")
    top = 'P e. Prime'
    RHS = '( %s x. %s )' % (IF1('P', 'R', '( P + 1 )'), IF1('P', 'S', '( P + 1 )'))
    GOAL = '( 1 + ( abs ` %s ) ) <_ %s' % (HP('R', 'S', 'P'), RHS)
    res = {}
    for ar in (True, False):
        for as_ in (True, False):
            AR = 'P || R' if ar else '-. P || R'
            AS = 'P || S' if as_ else '-. P || S'
            c = '( ( %s /\\ %s ) /\\ %s )' % (top, AR, AS)
            st = mkst(w, c)
            ppr = st([], 'simpll', top)
            pnn = sy(w, c, ppr, 'prmnn', 'P e. NN')
            pr = st([pnn], 'nnred', 'P e. RR')
            p2 = st([sy(w, c, ppr, 'prmuz2', 'P e. ( ZZ>= ` 2 )'), w.inst('eluzle')], 'syl', '2 <_ P')
            dR = st([], 'simplr', AR); dS = st([], 'simpr', AS)
            fv = fmpv(w, c, ppr)
            rules = {}; rules2 = {}
            for X, tr, d in (('R', ar, dR), ('S', as_, dS)):
                if tr:
                    t = st([st([d], 'iftrued', '%s = %s' % (IFP('P', X), FMP('P'))), fv], 'eqtrd', '%s = -u ( P - 1 )' % IFP('P', X))
                    rules[IFP('P', X)] = ('-u ( P - 1 )', t)
                    rules2[IF1('P', X, '( P + 1 )')] = ('( P + 1 )', st([d], 'iftrued', '%s = ( P + 1 )' % IF1('P', X, '( P + 1 )')))
                else:
                    rules[IFP('P', X)] = ('1', st([d], 'iffalsed', '%s = 1' % IFP('P', X)))
                    rules2[IF1('P', X, '( P + 1 )')] = ('1', st([d], 'iffalsed', '%s = 1' % IF1('P', X, '( P + 1 )')))
            hx, x = w.rewrite(HP('R', 'S', 'P'), rules, c)
            hy, Y = w.rewrite(RHS, rules2, c)
            cl = Closure(w, c, {'P': ('RR', pr)})
            xr = cl.mem(x, 'RR'); yr = cl.mem(Y, 'RR')
            Y1 = '( %s - 1 )' % Y
            y1r = st([yr, st([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % Y1)
            lv = {'P': ('RR', pr)}
            lo = lin.nlinarith(w, c, [p2], '-u %s <_ %s' % (Y1, x), leaves=lv)
            hi = lin.nlinarith(w, c, [p2], '%s <_ %s' % (x, Y1), leaves=lv)
            ab = st([st([lo, hi], 'jca', '( -u %s <_ %s /\\ %s <_ %s )' % (Y1, x, x, Y1)), st([xr, y1r], 'absled', '( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) )' % (x, Y1, Y1, x, x, Y1))],
                    'mpbird', '( abs ` %s ) <_ %s' % (x, Y1))
            axr = st([st([xr], 'recnd', '%s e. CC' % x)], 'abscld', '( abs ` %s ) e. RR' % x)
            fin = lin.linarith(w, c, [ab], '( 1 + ( abs ` %s ) ) <_ %s' % (x, Y), leaves={'P': ('RR', pr), '( abs ` %s )' % x: ('RR', axr)}, atoms=['( abs ` %s )' % x])
            e1 = st([st([hx], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (HP('R', 'S', 'P'), x))], 'oveq2d', '( 1 + ( abs ` %s ) ) = ( 1 + ( abs ` %s ) )' % (HP('R', 'S', 'P'), x))
            g1 = st([e1, fin], 'eqbrtrd', '( 1 + ( abs ` %s ) ) <_ %s' % (HP('R', 'S', 'P'), Y))
            res[(ar, as_)] = st([g1, hy], 'breqtrrd', GOAL)
    r1 = w.s([res[(True, True)], res[(True, False)]], 'pm2.61dan', '( ( %s /\\ P || R ) -> %s )' % (top, GOAL))
    r2 = w.s([res[(False, True)], res[(False, False)]], 'pm2.61dan', '( ( %s /\\ -. P || R ) -> %s )' % (top, GOAL))
    w.qed([r1, r2], 'pm2.61dan', STATEMENTS['z5hpabs'])
    return w


def z5hbvabs():
    w = W('z5hbvabs', "Blueprint Lemma 3.3(b) (Lean sum_abs_hBV_le, the h-mass): for squarefree R, S, sum_ d | R S | hBV ( d ; R , S ) | <_ "
                      "prod_ p | R ( p + 1 ) prod_ p | S ( p + 1 ) (the engine at | hPrime |, bounded prime by prime).")
    ante = HRS
    st = mkst(w, ante)
    rnn = st([], 'simpll', 'R e. NN'); snn = st([], 'simprl', 'S e. NN')
    RS = '( R x. S )'
    rsn = st([rnn, snn], 'nnmulcld', '%s e. NN' % RS)
    DVN = DV(RS)
    AH = '( abs ` %s )' % HP('R', 'S', 'p')
    PH = 'prod_ p e. %s %s' % (PF('d'), HP('R', 'S', 'p'))
    C = '( mmu ` d ) =/= 0'
    IFA = 'if ( %s , prod_ p e. %s %s , 0 )' % (C, PF('d'), AH)
    a = '( %s /\\ d e. %s )' % (ante, DVN)
    sa = mkst(w, a)
    dn = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (a, DVN)), w.inst('elrabi')], 'syl', '( %s -> d e. NN )' % a)
    hv = w.s([lift(w, rnn, a), lift(w, snn, a), dn, w.inst('z5hbvval')], 'syl21anc', '( %s -> %s = if ( %s , %s , 0 ) )' % (a, HB('R', 'S', 'd'), C, PH))
    t1 = sa([hv], 'fveq2d', '( abs ` %s ) = ( abs ` if ( %s , %s , 0 ) )' % (HB('R', 'S', 'd'), C, PH))
    t2 = w.s([w.s([], 'fvif', '( abs ` if ( %s , %s , 0 ) ) = if ( %s , ( abs ` %s ) , ( abs ` 0 ) )' % (C, PH, C, PH))], 'a1i',
             '( %s -> ( abs ` if ( %s , %s , 0 ) ) = if ( %s , ( abs ` %s ) , ( abs ` 0 ) ) )' % (a, C, PH, C, PH))
    fd = sy(w, a, dn, 'pffinq', '%s e. Fin' % PF('d'))
    ad = '( %s /\\ p e. %s )' % (a, PF('d'))
    hcd = w.s([hpre(w, ad, sy(w, ad, pp(w, ad, w.s([], 'simpr', '( %s -> p e. %s )' % (ad, PF('d')))), 'prmnn', 'p e. NN'), 'R', 'S')], 'recnd', '( %s -> %s e. CC )' % (ad, HP('R', 'S', 'p')))
    pa = w.s([fd, hcd], 'z5fprodabs', '( %s -> ( abs ` %s ) = prod_ p e. %s %s )' % (a, PH, PF('d'), AH))
    t3 = sa([pa, w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % a)], 'ifeq12d',
            'if ( %s , ( abs ` %s ) , ( abs ` 0 ) ) = %s' % (C, PH, IFA))
    t = sa([sa([t1, t2], 'eqtrd', '( abs ` %s ) = if ( %s , ( abs ` %s ) , ( abs ` 0 ) )' % (HB('R', 'S', 'd'), C, PH)), t3], 'eqtrd', '( abs ` %s ) = %s' % (HB('R', 'S', 'd'), IFA))
    L = 'sum_ d e. %s ( abs ` %s )' % (DVN, HB('R', 'S', 'd'))
    s1 = st([t], 'sumeq2dv', '%s = sum_ d e. %s %s' % (L, DVN, IFA))
    b0 = '( %s /\\ p e. Prime )' % ante
    hc0 = w.s([hpre(w, b0, sy(w, b0, w.s([], 'simpr', '( %s -> p e. Prime )' % b0), 'prmnn', 'p e. NN'), 'R', 'S')], 'recnd', '( %s -> %s e. CC )' % (b0, HP('R', 'S', 'p')))
    ac0 = w.s([w.s([hc0], 'abscld', '( %s -> %s e. RR )' % (b0, AH))], 'recnd', '( %s -> %s e. CC )' % (b0, AH))
    PA = 'prod_ p e. %s ( 1 + %s )' % (PF(RS), AH)
    s2 = w.s([rsn, ac0], 'z5sqfeul', '( %s -> sum_ d e. %s %s = %s )' % (ante, DVN, IFA, PA))
    IR = IF1('p', 'R', '( p + 1 )'); IS = IF1('p', 'S', '( p + 1 )')
    PB = 'prod_ p e. %s ( %s x. %s )' % (PF(RS), IR, IS)
    fin = sy(w, ante, rsn, 'pffinq', '%s e. Fin' % PF(RS))
    c = '( %s /\\ p e. %s )' % (ante, PF(RS))
    sc = mkst(w, c)
    ppr = pp(w, c, sc([], 'simpr', 'p e. %s' % PF(RS)))
    pnn = sy(w, c, ppr, 'prmnn', 'p e. NN')
    pr = sc([pnn], 'nnred', 'p e. RR')
    ahr = sc([sc([hpre(w, c, pnn, 'R', 'S')], 'recnd', '%s e. CC' % HP('R', 'S', 'p'))], 'abscld', '%s e. RR' % AH)
    ahc = sc([sc([hpre(w, c, pnn, 'R', 'S')], 'recnd', '%s e. CC' % HP('R', 'S', 'p'))], 'absge0d', '0 <_ %s' % AH)
    bodyr = sc([sc([], '1red', '1 e. RR'), ahr], 'readdcld', '( 1 + %s ) e. RR' % AH)
    b0le = lin.linarith(w, c, [ahc], '0 <_ ( 1 + %s )' % AH, leaves={AH: ('RR', ahr)}, atoms=[AH])
    p1 = sc([pr, sc([], '1red', '1 e. RR')], 'readdcld', '( p + 1 ) e. RR')
    irr = sc([p1, sc([], '1red', '1 e. RR')], 'ifcld', '%s e. RR' % IR)
    isr = sc([p1, sc([], '1red', '1 e. RR')], 'ifcld', '%s e. RR' % IS)
    bnd = sc([irr, isr], 'remulcld', '( %s x. %s ) e. RR' % (IR, IS))
    hp = sy(w, c, ppr, 'z5hpabs', '( 1 + %s ) <_ ( %s x. %s )' % (AH, IR, IS))
    s3 = w.s([w.s([], 'nfv', 'F/ p %s' % ante), fin, bodyr, b0le, bnd, hp], 'fprodle', '( %s -> %s <_ %s )' % (ante, PA, PB))
    PR_ = 'prod_ p e. %s %s' % (PF(RS), IR); PS_ = 'prod_ p e. %s %s' % (PF(RS), IS)
    s4 = st([fin, sc([irr], 'recnd', '%s e. CC' % IR), sc([isr], 'recnd', '%s e. CC' % IS)], 'fprodmul', '%s = ( %s x. %s )' % (PB, PR_, PS_))
    bb = '( %s /\\ p e. Prime )' % ante
    p1c = w.s([w.s([sy(w, bb, w.s([], 'simpr', '( %s -> p e. Prime )' % bb), 'prmnn', 'p e. NN')], 'nncnd', '( %s -> p e. CC )' % bb),
               w.s([], '1cnd', '( %s -> 1 e. CC )' % bb)], 'addcld', '( %s -> ( p + 1 ) e. CC )' % bb)
    rz = st([rnn], 'nnzd', 'R e. ZZ'); sz = st([snn], 'nnzd', 'S e. ZZ')
    rd = st([rz, sz, w.inst('dvdsmul1')], 'syl2anc', 'R || %s' % RS)
    sd = st([rz, sz, w.inst('dvdsmul2')], 'syl2anc', 'S || %s' % RS)
    fr = w.s([rsn, rnn, rd, p1c], 'z5pfif', '( %s -> %s = prod_ p e. %s ( p + 1 ) )' % (ante, PR_, PF('R')))
    fs = w.s([rsn, snn, sd, p1c], 'z5pfif', '( %s -> %s = prod_ p e. %s ( p + 1 ) )' % (ante, PS_, PF('S')))
    s5 = st([fr, fs], 'oveq12d', '( %s x. %s ) = ( prod_ p e. %s ( p + 1 ) x. prod_ p e. %s ( p + 1 ) )' % (PR_, PS_, PF('R'), PF('S')))
    RHS = '( prod_ p e. %s ( p + 1 ) x. prod_ p e. %s ( p + 1 ) )' % (PF('R'), PF('S'))
    e1 = st([s1, s2], 'eqtrd', '%s = %s' % (L, PA))
    e2 = st([s4, s5], 'eqtrd', '%s = %s' % (PB, RHS))
    g = st([e1, s3], 'eqbrtrd', '%s <_ %s' % (L, PB))
    w.qed([g, e2], 'breqtrd', STATEMENTS['z5hbvabs'])
    return w


if __name__ == '__main__':
    import z5blib
    for f in sys.argv[1:]:
        z5blib.run(globals()[f]())
