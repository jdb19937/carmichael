"""Sortie Z5c, section T: tOf and the gcd splitting (Detector.lean 583-652)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5clib import *
from cl import Closure, lift

TTs = TT('D', 'R')
QSs = QS('D', 'R')
QUs = QSU('D', 'R')
QSBODY = lambda v: '( %s || R /\\ -. %s || D )' % (v, v)


def cns(lab):
    """the consequent of a closed frozen statement ( ante -> concl )"""
    from cl import split_imp
    return split_imp(STATEMENTS[lab])[1]


def z5tofsq():
    w = W('z5tofsq', "Lean squarefree_tOf, tOf_ne_zero, tOf_primeFactors: t ( D ; R ) = prod_ ( p | R , -. p | D ) p is a squarefree "
                     "positive integer whose prime set is { p | R : -. p | D } (V2's sqfprod on that finite set of primes).")
    ante = 'R e. NN'
    st = mkst(w, ante)
    PFRu = '{ u e. Prime | u || R }'
    imp = w.s([], 'simpl', '( %s -> u || R )' % QSBODY('u'))
    imp2 = w.s([imp], 'a1i', '( u e. Prime -> ( %s -> u || R ) )' % QSBODY('u'))
    ss1 = w.s([imp2], 'ss2rabi', '%s C_ %s' % (QUs, PFRu))
    cb = w.s([w.s([], 'breq1', '( u = q -> ( u || R <-> q || R ) )')], 'cbvrabv', '%s = %s' % (PFRu, PF('R')))
    ss2 = w.s([ss1, cb], 'sseqtri', '%s C_ %s' % (QUs, PF('R')))
    fr = w.s([], 'pffinq', '( R e. NN -> %s e. Fin )' % PF('R'))
    qf = st([fr, w.s([ss2], 'a1i', '( %s -> %s C_ %s )' % (ante, QUs, PF('R')))], 'ssfid', '%s e. Fin' % QUs)
    qp = w.s([w.s([], 'ssrab2', '%s C_ Prime' % QUs)], 'a1i', '( %s -> %s C_ Prime )' % (ante, QUs))
    P = 'prod_ p e. %s p' % QUs
    c0 = '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s )' % (P, P, P, QUs)
    sq = st([qf, qp, w.inst('sqfprod')], 'syl2anc', c0)
    cbp = w.s([w.s([], 'id', '( p = w -> p = w )')], 'cbvprodv', '%s = %s' % (P, TTs))
    idq = w.s([], 'id', '( u = q -> u = q )')
    stb, newb = w.wcongr(QSBODY('u'), {'u': 'q'}, 'u = q', {'u': idq})
    cbq = w.s([stb], 'cbvrabv', '%s = %s' % (QUs, QSs))
    rules = {P: (TTs, w.s([cbp], 'a1i', '( %s -> %s = %s )' % (ante, P, TTs))), QUs: (QSs, w.s([cbq], 'a1i', '( %s -> %s = %s )' % (ante, QUs, QSs)))}
    bi, new = w.wcongr(c0, {}, ante, {}, rules=rules)
    assert new == cns('z5tofsq'), new
    w.qed([sq, bi], 'mpbid', STATEMENTS['z5tofsq'])
    return w


def elqs(w, v):
    """closed: ( v e. QS <-> ( v e. Prime /\\ QSBODY(v) ) )"""
    idq = w.s([], 'id', '( q = %s -> q = %s )' % (v, v))
    stb, newb = w.wcongr(QSBODY('q'), {'q': v}, 'q = %s' % v, {'q': idq})
    return w.s([stb], 'elrab', '( %s e. %s <-> ( %s e. Prime /\\ %s ) )' % (v, QSs, v, newb))


def z5tofcop():
    w = W('z5tofcop', "Lean coprime_tOf_left: D and t ( D ; R ) are coprime (a common prime divisor would divide t ( D ; R ), so it is a "
                      "prime of R not dividing D).")
    ante = '( R e. NN /\\ D e. NN )'
    st = mkst(w, ante)
    rn = st([], 'simpl', 'R e. NN'); dn = st([], 'simpr', 'D e. NN')
    tq = st([rn, w.inst('z5tofsq')], 'syl', cns('z5tofsq'))
    ttn = st([tq], 'simplld', '%s e. NN' % TTs)
    pfe = st([tq], 'simprd', '%s = %s' % (PF(TTs), QSs))
    bi = st([dn, ttn], 'prmdvdsncoprmbd', '( E. p e. Prime ( p || D /\\ p || %s ) <-> ( D gcd %s ) =/= 1 )' % (TTs, TTs))
    c = '( ( %s /\\ p e. Prime ) /\\ ( p || D /\\ p || %s ) )' % (ante, TTs)
    sc = mkst(w, c)
    pp_ = sc([], 'simplr', 'p e. Prime')
    ptt = sc([], 'simprr', 'p || %s' % TTs)
    pd = sc([], 'simprl', 'p || D')
    e1 = w.s([w.s([], 'breq1', '( q = p -> ( q || %s <-> p || %s ) )' % (TTs, TTs))], 'elrab', '( p e. %s <-> ( p e. Prime /\\ p || %s ) )' % (PF(TTs), TTs))
    inpf = sc([pp_, ptt, w.s([e1], 'a1i', '( %s -> ( p e. %s <-> ( p e. Prime /\\ p || %s ) ) )' % (c, PF(TTs), TTs))], 'mpbir2and', 'p e. %s' % PF(TTs))
    inqs = sc([inpf, lift(w, pfe, c)], 'eleqtrd', 'p e. %s' % QSs)
    parts = sc([inqs, w.s([elqs(w, 'p')], 'a1i', '( %s -> ( p e. %s <-> ( p e. Prime /\\ %s ) ) )' % (c, QSs, QSBODY('p')))], 'mpbid',
               '( p e. Prime /\\ %s )' % QSBODY('p'))
    npd = sc([parts], 'simprrd', '-. p || D')
    nq = w.s([pd, npd], 'pm2.65da', '( ( %s /\\ p e. Prime ) -> -. ( p || D /\\ p || %s ) )' % (ante, TTs))
    ral = st([nq], 'ralrimiva', 'A. p e. Prime -. ( p || D /\\ p || %s )' % TTs)
    nex = st([ral, w.s([], 'ralnex', '( A. p e. Prime -. ( p || D /\\ p || %s ) <-> -. E. p e. Prime ( p || D /\\ p || %s ) )' % (TTs, TTs))], 'sylib',
             '-. E. p e. Prime ( p || D /\\ p || %s )' % TTs)
    n1 = st([nex, bi], 'mtbid', '-. ( D gcd %s ) =/= 1' % TTs)
    w.qed([n1, w.s([], 'nne', '( -. ( D gcd %s ) =/= 1 <-> ( D gcd %s ) = 1 )' % (TTs, TTs))], 'sylib', STATEMENTS['z5tofcop'])
    return w


def z5gcdcop():
    w = W('z5gcdcop', "Lean coprime_gcd_gcd_tOf: the two factors ( R , D ) and ( t ( D ; R ) , M ) of the gcd splitting are coprime.")
    ante = '( R e. NN /\\ ( D e. NN /\\ M e. NN ) )'
    st = mkst(w, ante)
    rn = st([], 'simpl', 'R e. NN'); dn = st([], 'simprl', 'D e. NN'); mn = st([], 'simprr', 'M e. NN')
    cop = st([rn, dn, w.inst('z5tofcop')], 'syl2anc', '( D gcd %s ) = 1' % TTs)
    tq = st([rn, w.inst('z5tofsq')], 'syl', cns('z5tofsq'))
    ttn = st([tq], 'simplld', '%s e. NN' % TTs)
    G2 = '( R gcd D )'; G3 = '( %s gcd M )' % TTs
    rz = st([rn], 'nnzd', 'R e. ZZ'); dz = st([dn], 'nnzd', 'D e. ZZ'); mz = st([mn], 'nnzd', 'M e. ZZ'); tz = st([ttn], 'nnzd', '%s e. ZZ' % TTs)
    g2z = st([st([rn, dn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G2)], 'nnzd', '%s e. ZZ' % G2)
    g3z = st([st([ttn, mn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G3)], 'nnzd', '%s e. ZZ' % G3)
    g2d = st([st([rz, dz, w.inst('gcddvds')], 'syl2anc', '( %s || R /\\ %s || D )' % (G2, G2))], 'simprd', '%s || D' % G2)
    g3t = st([st([tz, mz, w.inst('gcddvds')], 'syl2anc', '( %s || %s /\\ %s || M )' % (G3, TTs, G3))], 'simpld', '%s || %s' % (G3, TTs))
    s1 = st([dz, g3z, tz, cop, g3t, w.inst('rpdvds')], 'syl32anc', '( D gcd %s ) = 1' % G3)
    s2 = st([st([g3z, dz, w.inst('gcdcom')], 'syl2anc', '( %s gcd D ) = ( D gcd %s )' % (G3, G3)), s1], 'eqtrd', '( %s gcd D ) = 1' % G3)
    s3 = st([g3z, g2z, dz, s2, g2d, w.inst('rpdvds')], 'syl32anc', '( %s gcd %s ) = 1' % (G3, G2))
    w.qed([st([g2z, g3z, w.inst('gcdcom')], 'syl2anc', '( %s gcd %s ) = ( %s gcd %s )' % (G2, G3, G3, G2)), s3], 'eqtrd', STATEMENTS['z5gcdcop'])
    return w


def z5gcdspl():
    w = W('z5gcdspl', "Lean gcd_mul_split: for squarefree R, ( R , D M ) = ( R , D ) ( t ( D ; R ) , M ): both sides are squarefree with the "
                      "same primes, p | R and ( p | D or p | M ) against ( p | R and p | D ) or ( p | R , -. p | D and p | M ).")
    ante = '( %s /\\ ( D e. NN /\\ M e. NN ) )' % SQF('R')
    st = mkst(w, ante)
    rn = st([], 'simpll', 'R e. NN'); r0 = st([], 'simplr', '( mmu ` R ) =/= 0'); dn = st([], 'simprl', 'D e. NN'); mn = st([], 'simprr', 'M e. NN')
    tq = st([rn, w.inst('z5tofsq')], 'syl', cns('z5tofsq'))
    ttn = st([tq], 'simplld', '%s e. NN' % TTs); tt0 = st([tq], 'simplrd', '( mmu ` %s ) =/= 0' % TTs)
    pfe = st([tq], 'simprd', '%s = %s' % (PF(TTs), QSs))
    DM = '( D x. M )'
    G1 = '( R gcd %s )' % DM; G2 = '( R gcd D )'; G3 = '( %s gcd M )' % TTs; P = '( %s x. %s )' % (G2, G3)
    rz = st([rn], 'nnzd', 'R e. ZZ'); dz = st([dn], 'nnzd', 'D e. ZZ'); mz = st([mn], 'nnzd', 'M e. ZZ'); tz = st([ttn], 'nnzd', '%s e. ZZ' % TTs)
    dmn = st([dn, mn], 'nnmulcld', '%s e. NN' % DM); dmz = st([dmn], 'nnzd', '%s e. ZZ' % DM)
    g1n = st([rn, dmn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G1)
    g2n = st([rn, dn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G2)
    g3n = st([ttn, mn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G3)
    g1r = st([st([rz, dmz, w.inst('gcddvds')], 'syl2anc', '( %s || R /\\ %s || %s )' % (G1, G1, DM))], 'simpld', '%s || R' % G1)
    g2r = st([st([rz, dz, w.inst('gcddvds')], 'syl2anc', '( %s || R /\\ %s || D )' % (G2, G2))], 'simpld', '%s || R' % G2)
    g3t = st([st([tz, mz, w.inst('gcddvds')], 'syl2anc', '( %s || %s /\\ %s || M )' % (G3, TTs, G3))], 'simpld', '%s || %s' % (G3, TTs))
    g1s = st([rn, r0, g1n, g1r, w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` %s ) =/= 0' % G1)
    g2s = st([rn, r0, g2n, g2r, w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` %s ) =/= 0' % G2)
    g3s = st([ttn, tt0, g3n, g3t, w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` %s ) =/= 0' % G3)
    cop = st([rn, dn, mn, w.inst('z5gcdcop')], 'syl12anc', '( %s gcd %s ) = 1' % (G2, G3))
    pn = st([g2n, g3n], 'nnmulcld', '%s e. NN' % P)
    mup = st([g2n, g3n, cop, w.inst('mumul')], 'syl3anc', '( mmu ` %s ) = ( ( mmu ` %s ) x. ( mmu ` %s ) )' % (P, G2, G3))
    m2c = st([st([g2n, w.inst('mucl')], 'syl', '( mmu ` %s ) e. ZZ' % G2)], 'zcnd', '( mmu ` %s ) e. CC' % G2)
    m3c = st([st([g3n, w.inst('mucl')], 'syl', '( mmu ` %s ) e. ZZ' % G3)], 'zcnd', '( mmu ` %s ) e. CC' % G3)
    mne = st([m2c, m3c, g2s, g3s], 'mulne0d', '( ( mmu ` %s ) x. ( mmu ` %s ) ) =/= 0' % (G2, G3))
    ps = st([mup, mne], 'eqnetrd', '( mmu ` %s ) =/= 0' % P)
    # the prime sets
    b = '( %s /\\ q e. Prime )' % ante
    sb = mkst(w, b)
    qp = sb([], 'simpr', 'q e. Prime')
    qz = sy(w, b, qp, 'prmz', 'q e. ZZ')
    L = lambda x: lift(w, x, b)
    l1 = sb([sb([qz, L(rz), L(dmz), w.inst('dvdsgcdb')], 'syl3anc', '( ( q || R /\\ q || %s ) <-> q || %s )' % (DM, G1))], 'bicomd',
            '( q || %s <-> ( q || R /\\ q || %s ) )' % (G1, DM))
    l2 = sb([qp, L(dz), L(mz), w.inst('euclemma')], 'syl3anc', '( q || %s <-> ( q || D \\/ q || M ) )' % DM)
    l3 = sb([l2], 'anbi2d', '( ( q || R /\\ q || %s ) <-> ( q || R /\\ ( q || D \\/ q || M ) ) )' % DM)
    LF = '( q || R /\\ ( q || D \\/ q || M ) )'
    lf = sb([l1, l3], 'bitrd', '( q || %s <-> %s )' % (G1, LF))
    g2z = sb([L(g2n)], 'nnzd', '%s e. ZZ' % G2); g3z = sb([L(g3n)], 'nnzd', '%s e. ZZ' % G3)
    r1 = sb([qp, g2z, g3z, w.inst('euclemma')], 'syl3anc', '( q || %s <-> ( q || %s \\/ q || %s ) )' % (P, G2, G3))
    r2 = sb([sb([qz, L(rz), L(dz), w.inst('dvdsgcdb')], 'syl3anc', '( ( q || R /\\ q || D ) <-> q || %s )' % G2)], 'bicomd', '( q || %s <-> ( q || R /\\ q || D ) )' % G2)
    r3 = sb([sb([qz, L(tz), L(mz), w.inst('dvdsgcdb')], 'syl3anc', '( ( q || %s /\\ q || M ) <-> q || %s )' % (TTs, G3))], 'bicomd',
            '( q || %s <-> ( q || %s /\\ q || M ) )' % (G3, TTs))
    # q || TT <-> QSBODY(q)
    t1 = sb([qp], 'biantrurd', '( q || %s <-> ( q e. Prime /\\ q || %s ) )' % (TTs, TTs))
    t2 = w.s([], 'rabid', '( q e. %s <-> ( q e. Prime /\\ q || %s ) )' % (PF(TTs), TTs))
    t3 = sb([t1, w.s([t2], 'a1i', '( %s -> ( q e. %s <-> ( q e. Prime /\\ q || %s ) ) )' % (b, PF(TTs), TTs))], 'bitr4d', '( q || %s <-> q e. %s )' % (TTs, PF(TTs)))
    t4 = sb([L(pfe)], 'eleq2d', '( q e. %s <-> q e. %s )' % (PF(TTs), QSs))
    t5 = w.s([], 'rabid', '( q e. %s <-> ( q e. Prime /\\ %s ) )' % (QSs, QSBODY('q')))
    t6 = sb([qp], 'biantrurd', '( %s <-> ( q e. Prime /\\ %s ) )' % (QSBODY('q'), QSBODY('q')))
    t7 = sb([w.s([t5], 'a1i', '( %s -> ( q e. %s <-> ( q e. Prime /\\ %s ) ) )' % (b, QSs, QSBODY('q'))), t6], 'bitr4d', '( q e. %s <-> %s )' % (QSs, QSBODY('q')))
    tt = sb([sb([t3, t4], 'bitrd', '( q || %s <-> q e. %s )' % (TTs, QSs)), t7], 'bitrd', '( q || %s <-> %s )' % (TTs, QSBODY('q')))
    r4 = sb([tt], 'anbi1d', '( ( q || %s /\\ q || M ) <-> ( %s /\\ q || M ) )' % (TTs, QSBODY('q')))
    r34 = sb([r3, r4], 'bitrd', '( q || %s <-> ( %s /\\ q || M ) )' % (G3, QSBODY('q')))
    RF = '( ( q || R /\\ q || D ) \\/ ( %s /\\ q || M ) )' % QSBODY('q')
    r5 = sb([r2, r34], 'orbi12d', '( ( q || %s \\/ q || %s ) <-> %s )' % (G2, G3, RF))
    rf = sb([r1, r5], 'bitrd', '( q || %s <-> %s )' % (P, RF))
    # the tautology ( a /\ ( b \/ c ) ) <-> ( ( a /\ b ) \/ ( ( a /\ -. b ) /\ c ) )
    a_, b_, c_ = 'q || R', 'q || D', 'q || M'
    u1 = w.s([], 'pm5.63', '( ( %s \\/ %s ) <-> ( %s \\/ ( -. %s /\\ %s ) ) )' % (b_, c_, b_, b_, c_))
    u2 = w.s([u1], 'anbi2i', '( ( %s /\\ ( %s \\/ %s ) ) <-> ( %s /\\ ( %s \\/ ( -. %s /\\ %s ) ) ) )' % (a_, b_, c_, a_, b_, b_, c_))
    X = '( ( %s /\\ %s ) \\/ ( %s /\\ ( -. %s /\\ %s ) ) )' % (a_, b_, a_, b_, c_)
    u3 = w.s([], 'andi', '( ( %s /\\ ( %s \\/ ( -. %s /\\ %s ) ) ) <-> %s )' % (a_, b_, b_, c_, X))
    u4 = w.s([], 'anass', '( ( ( %s /\\ -. %s ) /\\ %s ) <-> ( %s /\\ ( -. %s /\\ %s ) ) )' % (a_, b_, c_, a_, b_, c_))
    u5 = w.s([u4], 'orbi2i', '( %s <-> %s )' % (RF, X))
    u23 = w.s([u2, u3], 'bitri', '( %s <-> %s )' % (LF, X))
    taut = w.s([u23, u5], 'bitr4i', '( %s <-> %s )' % (LF, RF))
    bq = sb([sb([lf, w.s([taut], 'a1i', '( %s -> ( %s <-> %s ) )' % (b, LF, RF))], 'bitrd', '( q || %s <-> %s )' % (G1, RF)), rf], 'bitr4d',
            '( q || %s <-> q || %s )' % (G1, P))
    rab = st([bq], 'rabbidva', '%s = %s' % (PF(G1), PF(P)))
    pe = st([rab], 'prodeq1d', 'prod_ p e. %s p = prod_ p e. %s p' % (PF(G1), PF(P)))
    s1 = st([g1n, g1s, w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = %s' % (PF(G1), G1))
    s2 = st([pn, ps, w.inst('sqfprodid')], 'syl2anc', 'prod_ p e. %s p = %s' % (PF(P), P))
    e = st([s1, pe], 'eqtr3d', '%s = prod_ p e. %s p' % (G1, PF(P)))
    w.qed([e, s2], 'eqtrd', STATEMENTS['z5gcdspl'])
    return w


def z5psispl():
    w = W('z5psispl', "Lean psi_mul_split (blueprint Lemma 3.1, first display): psi_R ( D M ) = f ( ( R , D ) ) psi_t ( M ) with "
                      "t = t ( D ; R ), from the gcd splitting and the multiplicativity of f = mmu phi.")
    ante = '( %s /\\ ( D e. NN /\\ M e. NN ) )' % SQF('R')
    st = mkst(w, ante)
    rn = st([], 'simpll', 'R e. NN'); dn = st([], 'simprl', 'D e. NN'); mn = st([], 'simprr', 'M e. NN')
    tq = st([rn, w.inst('z5tofsq')], 'syl', cns('z5tofsq'))
    ttn = st([tq], 'simplld', '%s e. NN' % TTs)
    DM = '( D x. M )'
    G1 = '( R gcd %s )' % DM; G2 = '( R gcd D )'; G3 = '( %s gcd M )' % TTs; P = '( %s x. %s )' % (G2, G3)
    e = st([st([], 'id', ante), w.inst('z5gcdspl')], 'syl', '%s = %s' % (G1, P))
    f = st([st([e], 'fveq2d', '( mmu ` %s ) = ( mmu ` %s )' % (G1, P)), st([e], 'fveq2d', '( phi ` %s ) = ( phi ` %s )' % (G1, P))], 'oveq12d',
           '%s = %s' % (FMP(G1), FMP(P)))
    g2n = st([rn, dn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G2)
    g3n = st([ttn, mn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G3)
    cop = st([rn, dn, mn, w.inst('z5gcdcop')], 'syl12anc', '( %s gcd %s ) = 1' % (G2, G3))
    m = st([g2n, g3n, cop, w.inst('z5fmpmul')], 'syl3anc', '%s = ( %s x. %s )' % (FMP(P), FMP(G2), FMP(G3)))
    w.qed([f, m], 'eqtrd', STATEMENTS['z5psispl'])
    return w


if __name__ == '__main__':
    import z5clib
    for f in sys.argv[1:]:
        z5clib.run(globals()[f]())
