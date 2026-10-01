"""Sortie BM: the small closed lemmas (bmeldiv, bmhashim, bmhashsum, bmlog4, bmpow, bmtot)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from bm_base import *


def gen_eldiv():
    w = W('bmeldiv', 'Membership in the divisor set ` { m e. ( 1 ... N ) | m || N } ` of carmsw.3 (Lean ` Nat.mem_divisors ` ): a natural number dividing ` N ` (~ elrab , ~ elfz1b , ~ dvdsle ).')
    D = DIV('N')
    e1 = w.s([], 'breq1', '( m = A -> ( m || N <-> A || N ) )')
    e2 = w.s([e1], 'elrab', '( A e. %s <-> ( A e. ( 1 ... N ) /\\ A || N ) )' % D)
    f1 = w.s([], 'elfznn', '( A e. ( 1 ... N ) -> A e. NN )')
    f2 = w.s([f1], 'anim1i', '( ( A e. ( 1 ... N ) /\\ A || N ) -> ( A e. NN /\\ A || N ) )')
    f3 = w.s([f2], 'a1i', '( N e. NN -> ( ( A e. ( 1 ... N ) /\\ A || N ) -> ( A e. NN /\\ A || N ) ) )')
    C = '( N e. NN /\\ ( A e. NN /\\ A || N ) )'
    s = S_(w, C)
    g1 = s([], 'simpl', 'N e. NN'); g2 = s([], 'simprl', 'A e. NN'); g3 = s([], 'simprr', 'A || N')
    g4 = s([g2], 'nnzd', 'A e. ZZ')
    g5 = s([g4, g1, w.inst('dvdsle')], 'syl2anc', '( A || N -> A <_ N )')
    g6 = s([g3, g5], 'mpd', 'A <_ N')
    g7 = s([g2, g1, g6], '3jca', '( A e. NN /\\ N e. NN /\\ A <_ N )')
    g8 = w.s([], 'elfz1b', '( A e. ( 1 ... N ) <-> ( A e. NN /\\ N e. NN /\\ A <_ N ) )')
    g9 = s([g7, g8], 'sylibr', 'A e. ( 1 ... N )')
    g10 = s([g9, g3], 'jca', '( A e. ( 1 ... N ) /\\ A || N )')
    g11 = w.s([g10], 'ex', '( N e. NN -> ( ( A e. NN /\\ A || N ) -> ( A e. ( 1 ... N ) /\\ A || N ) ) )')
    h1 = w.s([f3, g11], 'impbid', '( N e. NN -> ( ( A e. ( 1 ... N ) /\\ A || N ) <-> ( A e. NN /\\ A || N ) ) )')
    w.qed([e2, h1], 'bitrid', S['bmeldiv'])
    return go(w)


def gen_hashim():
    w = W('bmhashim', 'The image of a finite set under a function has at most as many elements (~ fores , ~ fodomfi , ~ hashdomi ).')
    C = '( F Fn A /\\ B e. Fin /\\ B C_ A )'
    s = S_(w, C)
    a1 = s([], 'simp1', 'F Fn A'); a2 = s([], 'simp2', 'B e. Fin'); a3 = s([], 'simp3', 'B C_ A')
    b1 = s([a1], 'fnfund', 'Fun F')
    b2 = s([a1, w.inst('fndm')], 'syl', 'dom F = A')
    b3 = s([a3, b2], 'sseqtrrd', 'B C_ dom F')
    b4 = s([b1, b3, w.inst('fores')], 'syl2anc', '( F |` B ) : B -onto-> ( F " B )')
    b5 = s([a2, b4, w.inst('fodomfi')], 'syl2anc', '( F " B ) ~<_ B')
    w.qed([b5, w.inst('hashdomi')], 'syl', S['bmhashim'])
    return go(w)


def gen_hashsum():
    w = W('bmhashsum', 'The number of elements of a finite set satisfying a condition is the sum of the indicator of the condition (~ sumhash , ~ elrab3 ).')
    h1 = hyp(w, 'h1', 'bmhashsum.1', H['bmhashsum'][1])
    R = '{ x e. A | ph }'
    s1 = w.s([], 'ssrab2', '%s C_ A' % R)
    i0 = w.s([], 'id', '( A e. Fin -> A e. Fin )')
    s2 = w.s([s1], 'a1i', '( A e. Fin -> %s C_ A )' % R)
    s3 = w.s([i0, s2], 'jca', '( A e. Fin -> ( A e. Fin /\\ %s C_ A ) )' % R)
    s4 = w.s([s3, w.inst('sumhash')], 'syl', '( A e. Fin -> sum_ y e. A if ( y e. %s , 1 , 0 ) = ( # ` %s ) )' % (R, R))
    C2 = '( A e. Fin /\\ y e. A )'
    t1 = w.s([], 'simpr', '( %s -> y e. A )' % C2)
    t2 = w.s([h1], 'elrab3', '( y e. A -> ( y e. %s <-> ps ) )' % R)
    t3 = w.s([t1, t2], 'syl', '( %s -> ( y e. %s <-> ps ) )' % (C2, R))
    t4 = w.s([t3], 'ifbid', '( %s -> if ( y e. %s , 1 , 0 ) = if ( ps , 1 , 0 ) )' % (C2, R))
    t5 = w.s([t4], 'sumeq2dv', '( A e. Fin -> sum_ y e. A if ( y e. %s , 1 , 0 ) = sum_ y e. A if ( ps , 1 , 0 ) )' % R)
    w.qed([s4, t5], 'eqtr3d', S['bmhashsum'])
    return go(w)


def gen_log4():
    w = W('bmlog4', '` log 4 + 1 / 10 <_ 11 / 6 ` (Lean ` log_four_lt ` : ` log 4 < 139 / 100 ` , from ~ log2ub ).')
    L2 = '( log ` 2 )'; L4 = '( log ` 4 )'
    l1 = w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % L2)
    l2 = w.s([], '2rp', '2 e. RR+'); l3 = w.s([], '2z', '2 e. ZZ')
    l4 = w.s([l2, l3, w.inst('relogexp')], 'mp2an', '( log ` ( 2 ^ 2 ) ) = ( 2 x. %s )' % L2)
    l5 = w.s([], 'sq2', '( 2 ^ 2 ) = 4')
    l6 = w.s([l5], 'fveq2i', '( log ` ( 2 ^ 2 ) ) = %s' % L4)
    l7 = w.s([l6, l4], 'eqtr3i', '%s = ( 2 x. %s )' % (L4, L2))
    A = '( %s e. RR /\\ %s e. RR )' % (L2, L4)
    r2 = w.s([], 'simpl', '( %s -> %s e. RR )' % (A, L2)); r4 = w.s([], 'simpr', '( %s -> %s e. RR )' % (A, L4))
    h1 = w.s([l1], 'a1i', '( %s -> %s < ( ; ; 2 5 3 / ; ; 3 6 5 ) )' % (A, L2))
    h2 = w.s([l7], 'a1i', '( %s -> %s = ( 2 x. %s ) )' % (A, L4, L2))
    g = lin.linarith(w, A, [h1, h2], S['bmlog4'], leaves={L2: r2, L4: r4}, fast=False)
    c2 = w.s([l2, w.inst('relogcl')], 'ax-mp', '%s e. RR' % L2)
    c4 = w.s([num.rp_nat(w, 4), w.inst('relogcl')], 'ax-mp', '%s e. RR' % L4)
    both = w.s([c2, c4], 'pm3.2i', A)
    w.qed([both, g], 'ax-mp', S['bmlog4'])
    return go(w)


def gen_pow():
    w = W('bmpow', '` 2 ^ ( - ( J + 3 ) - 2 ) x. 2 ^ J = 1 / 32 ` (Lean ` hpow ` in ` pigeonhole_of_BMembership ` ; ~ cxpadd , ~ cxpneg , ~ cxpexp , ~ 2exp5 ).')
    A = 'J e. NN0'
    s = S_(w, A)
    jn = w.s([], 'id', '( J e. NN0 -> J e. NN0 )')
    jr = s([jn], 'nn0red', 'J e. RR'); jc = s([jn], 'nn0cnd', 'J e. CC')
    two = s([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')
    twon0 = s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0')
    E1 = '( -u ( J + 3 ) - 2 )'; E2 = '( -u 5 + -u J )'
    eq = lin.lineq(w, A, E1, E2, leaves={'J': jr})
    five = s([num.cc_nat(w, 5)], 'a1i', '5 e. CC')
    n5 = s([five], 'negcld', '-u 5 e. CC'); nj = s([jc], 'negcld', '-u J e. CC')
    c1 = s([eq], 'oveq2d', '( 2 ^c %s ) = ( 2 ^c %s )' % (E1, E2))
    c2 = s([two, twon0, n5, nj], 'cxpaddd', '( 2 ^c %s ) = ( ( 2 ^c -u 5 ) x. ( 2 ^c -u J ) )' % E2)
    c3 = s([two, twon0, five], 'cxpnegd', '( 2 ^c -u 5 ) = ( 1 / ( 2 ^c 5 ) )')
    c4 = s([two, s([num.nn0(w, 5)], 'a1i', '5 e. NN0'), w.inst('cxpexp')], 'syl2anc', '( 2 ^c 5 ) = ( 2 ^ 5 )')
    c5 = s([c4, s([w.s([], '2exp5', '( 2 ^ 5 ) = ; 3 2')], 'a1i', '( 2 ^ 5 ) = ; 3 2')], 'eqtrd', '( 2 ^c 5 ) = ; 3 2')
    c6 = s([c5], 'oveq2d', '( 1 / ( 2 ^c 5 ) ) = ( 1 / ; 3 2 )')
    c7 = s([c3, c6], 'eqtrd', '( 2 ^c -u 5 ) = ( 1 / ; 3 2 )')
    c8 = s([two, twon0, jc], 'cxpnegd', '( 2 ^c -u J ) = ( 1 / ( 2 ^c J ) )')
    c9 = s([two, jn, w.inst('cxpexp')], 'syl2anc', '( 2 ^c J ) = ( 2 ^ J )')
    c10 = s([c9], 'oveq2d', '( 1 / ( 2 ^c J ) ) = ( 1 / ( 2 ^ J ) )')
    c11 = s([c8, c10], 'eqtrd', '( 2 ^c -u J ) = ( 1 / ( 2 ^ J ) )')
    c12 = s([c7, c11], 'oveq12d', '( ( 2 ^c -u 5 ) x. ( 2 ^c -u J ) ) = ( ( 1 / ; 3 2 ) x. ( 1 / ( 2 ^ J ) ) )')
    c13 = s([c1, c2], 'eqtrd', '( 2 ^c %s ) = ( ( 2 ^c -u 5 ) x. ( 2 ^c -u J ) )' % E1)
    c14 = s([c13, c12], 'eqtrd', '( 2 ^c %s ) = ( ( 1 / ; 3 2 ) x. ( 1 / ( 2 ^ J ) ) )' % E1)
    c15 = s([c14], 'oveq1d', '( ( 2 ^c %s ) x. ( 2 ^ J ) ) = ( ( ( 1 / ; 3 2 ) x. ( 1 / ( 2 ^ J ) ) ) x. ( 2 ^ J ) )' % E1)
    pj = s([two, jn, w.inst('expcl')], 'syl2anc', '( 2 ^ J ) e. CC')
    pj0 = s([s([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), s([jn], 'nn0zd', 'J e. ZZ')], 'rpexpcld', '( 2 ^ J ) e. RR+')
    pjn0 = s([pj0], 'rpne0d', '( 2 ^ J ) =/= 0')
    r32 = s([num.cc(w, '( 1 / ; 3 2 )')], 'a1i', '( 1 / ; 3 2 ) e. CC')
    inv = s([pj, pjn0], 'reccld', '( 1 / ( 2 ^ J ) ) e. CC')
    c16 = s([r32, inv, pj], 'mulassd', '( ( ( 1 / ; 3 2 ) x. ( 1 / ( 2 ^ J ) ) ) x. ( 2 ^ J ) ) = ( ( 1 / ; 3 2 ) x. ( ( 1 / ( 2 ^ J ) ) x. ( 2 ^ J ) ) )')
    c17 = s([s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), pj, pjn0], 'divcan1d', '( ( 1 / ( 2 ^ J ) ) x. ( 2 ^ J ) ) = 1')
    c18 = s([c17], 'oveq2d', '( ( 1 / ; 3 2 ) x. ( ( 1 / ( 2 ^ J ) ) x. ( 2 ^ J ) ) ) = ( ( 1 / ; 3 2 ) x. 1 )')
    c19 = s([r32], 'mulridd', '( ( 1 / ; 3 2 ) x. 1 ) = ( 1 / ; 3 2 )')
    c20 = s([c16, c18], 'eqtrd', '( ( ( 1 / ; 3 2 ) x. ( 1 / ( 2 ^ J ) ) ) x. ( 2 ^ J ) ) = ( ( 1 / ; 3 2 ) x. 1 )')
    c21 = s([c20, c19], 'eqtrd', '( ( ( 1 / ; 3 2 ) x. ( 1 / ( 2 ^ J ) ) ) x. ( 2 ^ J ) ) = ( 1 / ; 3 2 )')
    w.qed([c15, c21], 'eqtrd', S['bmpow'])
    return go(w)


def gen_tot():
    w = W('bmtot', '` phi ( D ) ( Q - 1 ) <_ phi ( D Q ) ` for a prime ` Q ` , whether or not ` Q ` divides ` D ` (Lean ` totient_mul_prime_lower ` ): split ` D = Q ^ k D0 ` with ` Q ` not dividing ` D0 ` (~ pcdvds , ~ pcndvds2 ), use ~ phimul , ~ phiprmpw and ` phi ( Q ^ k ) <_ Q ^ k ` (~ phicl2 ).')
    A = '( D e. NN /\\ Q e. Prime )'
    s = S_(w, A)
    dn = s([], 'simpl', 'D e. NN'); qp = s([], 'simpr', 'Q e. Prime')
    qn = s([qp, w.inst('prmnn')], 'syl', 'Q e. NN'); qz = s([qn], 'nnzd', 'Q e. ZZ'); qc = s([qn], 'nncnd', 'Q e. CC')
    dc = s([dn], 'nncnd', 'D e. CC')
    K = '( Q pCnt D )'; PK = '( Q ^ %s )' % K; D0 = '( D / %s )' % PK; K1 = '( %s + 1 )' % K; PK1 = '( Q ^ %s )' % K1
    kn0 = s([qp, dn, w.inst('pccl')], 'syl2anc', '%s e. NN0' % K)
    kc = s([kn0], 'nn0cnd', '%s e. CC' % K)
    pkn = s([qn, kn0, w.inst('nnexpcl')], 'syl2anc', '%s e. NN' % PK)
    pkc = s([pkn], 'nncnd', '%s e. CC' % PK); pkn0 = s([pkn], 'nnne0d', '%s =/= 0' % PK); pkz = s([pkn], 'nnzd', '%s e. ZZ' % PK)
    pkd = s([qp, dn, w.inst('pcdvds')], 'syl2anc', '%s || D' % PK)
    d0b = s([dn, pkn, w.inst('nndivdvds')], 'syl2anc', '( %s || D <-> %s e. NN )' % (PK, D0))
    d0n = s([pkd, d0b], 'mpbid', '%s e. NN' % D0)
    d0z = s([d0n], 'nnzd', '%s e. ZZ' % D0); d0c = s([d0n], 'nncnd', '%s e. CC' % D0)
    nd = s([qp, dn, w.inst('pcndvds2')], 'syl2anc', '-. Q || %s' % D0)
    copb = s([qp, d0z, w.inst('coprm')], 'syl2anc', '( -. Q || %s <-> ( Q gcd %s ) = 1 )' % (D0, D0))
    cop = s([nd, copb], 'mpbid', '( Q gcd %s ) = 1' % D0)
    copk = s([cop, s([qz, d0z, kn0, w.inst('rpexp1i')], 'syl3anc', '( ( Q gcd %s ) = 1 -> ( %s gcd %s ) = 1 )' % (D0, PK, D0))], 'mpd', '( %s gcd %s ) = 1' % (PK, D0))
    k1n = s([kn0, w.inst('nn0p1nn')], 'syl', '%s e. NN' % K1)
    k1n0 = s([k1n], 'nnnn0d', '%s e. NN0' % K1)
    copk1 = s([cop, s([qz, d0z, k1n0, w.inst('rpexp1i')], 'syl3anc', '( ( Q gcd %s ) = 1 -> ( %s gcd %s ) = 1 )' % (D0, PK1, D0))], 'mpd', '( %s gcd %s ) = 1' % (PK1, D0))
    pk1n = s([qn, k1n0, w.inst('nnexpcl')], 'syl2anc', '%s e. NN' % PK1)
    # D = PK x. D0
    eqD = s([dc, pkc, pkn0], 'divcan2d', '( %s x. %s ) = D' % (PK, D0))
    # phi D = phi PK x. phi D0
    ph1 = s([pkn, d0n, copk, w.inst('phimul')], 'syl3anc', '( phi ` ( %s x. %s ) ) = ( ( phi ` %s ) x. ( phi ` %s ) )' % (PK, D0, PK, D0))
    ph2 = s([eqD], 'fveq2d', '( phi ` ( %s x. %s ) ) = ( phi ` D )' % (PK, D0))
    phD = s([ph1, ph2], 'eqtr3d', '( ( phi ` %s ) x. ( phi ` %s ) ) = ( phi ` D )' % (PK, D0))
    # D x. Q = PK1 x. D0
    e1 = s([eqD], 'oveq1d', '( ( %s x. %s ) x. Q ) = ( D x. Q )' % (PK, D0))
    e2 = s([pkc, d0c, qc], 'mul32d', '( ( %s x. %s ) x. Q ) = ( ( %s x. Q ) x. %s )' % (PK, D0, PK, D0))
    e3 = s([qc, kn0, w.inst('expp1')], 'syl2anc', '%s = ( %s x. Q )' % (PK1, PK))
    e4 = s([e3], 'oveq1d', '( %s x. %s ) = ( ( %s x. Q ) x. %s )' % (PK1, D0, PK, D0))
    e5 = s([e2, e4], 'eqtr4d', '( ( %s x. %s ) x. Q ) = ( %s x. %s )' % (PK, D0, PK1, D0))
    eDQ = s([e1, e5], 'eqtr3d', '( D x. Q ) = ( %s x. %s )' % (PK1, D0))
    # phi ( D x. Q ) = ( PK x. ( Q - 1 ) ) x. phi D0
    f1 = s([eDQ], 'fveq2d', '( phi ` ( D x. Q ) ) = ( phi ` ( %s x. %s ) )' % (PK1, D0))
    f2 = s([pk1n, d0n, copk1, w.inst('phimul')], 'syl3anc', '( phi ` ( %s x. %s ) ) = ( ( phi ` %s ) x. ( phi ` %s ) )' % (PK1, D0, PK1, D0))
    f3 = s([qp, k1n, w.inst('phiprmpw')], 'syl2anc', '( phi ` %s ) = ( ( Q ^ ( %s - 1 ) ) x. ( Q - 1 ) )' % (PK1, K1))
    f4 = s([kc, s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'pncand', '( %s - 1 ) = %s' % (K1, K))
    f5 = s([f4], 'oveq2d', '( Q ^ ( %s - 1 ) ) = %s' % (K1, PK))
    f6 = s([f5], 'oveq1d', '( ( Q ^ ( %s - 1 ) ) x. ( Q - 1 ) ) = ( %s x. ( Q - 1 ) )' % (K1, PK))
    f7 = s([f3, f6], 'eqtrd', '( phi ` %s ) = ( %s x. ( Q - 1 ) )' % (PK1, PK))
    f8 = s([f7], 'oveq1d', '( ( phi ` %s ) x. ( phi ` %s ) ) = ( ( %s x. ( Q - 1 ) ) x. ( phi ` %s ) )' % (PK1, D0, PK, D0))
    f9 = s([f1, f2], 'eqtrd', '( phi ` ( D x. Q ) ) = ( ( phi ` %s ) x. ( phi ` %s ) )' % (PK1, D0))
    phDQ = s([f9, f8], 'eqtrd', '( phi ` ( D x. Q ) ) = ( ( %s x. ( Q - 1 ) ) x. ( phi ` %s ) )' % (PK, D0))
    # phi PK <_ PK
    g1 = s([pkn, w.inst('phicl2')], 'syl', '( phi ` %s ) e. ( 1 ... %s )' % (PK, PK))
    g2 = s([g1, w.inst('elfzle2')], 'syl', '( phi ` %s ) <_ %s' % (PK, PK))
    # reals
    X = '( phi ` %s )' % PK; Y = PK; PD0 = '( phi ` %s )' % D0; Q1 = '( Q - 1 )'
    xr = s([s([pkn], 'phicld', '%s e. NN' % X)], 'nnred', '%s e. RR' % X)
    yr = s([pkn], 'nnred', '%s e. RR' % Y)
    pd0n = s([d0n], 'phicld', '%s e. NN' % PD0)
    pd0r = s([pd0n], 'nnred', '%s e. RR' % PD0); pd0c = s([pd0n], 'nncnd', '%s e. CC' % PD0)
    q1r = s([s([qn], 'nnred', 'Q e. RR'), s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'resubcld', '%s e. RR' % Q1)
    q1c = s([q1r], 'recnd', '%s e. CC' % Q1)
    q1ge0 = s([qp, w.inst('prmgt1')], 'syl', '1 < Q')
    q1ge0 = lin.linarith(w, A, [q1ge0], '0 <_ %s' % Q1, leaves={'Q': s([qn], 'nnred', 'Q e. RR')})
    Z = '( %s x. %s )' % (PD0, Q1)
    zr = s([pd0r, q1r], 'remulcld', '%s e. RR' % Z); zc = s([zr], 'recnd', '%s e. CC' % Z)
    z0 = s([pd0r, q1r, s([pd0n], 'nnnn0d', '%s e. NN0' % PD0), q1ge0], 'x', 'x') if False else None
    pd0ge0 = s([s([pd0n], 'nnnn0d', '%s e. NN0' % PD0)], 'nn0ge0d', '0 <_ %s' % PD0)
    z0 = s([pd0r, q1r, pd0ge0, q1ge0], 'mulge0d', '0 <_ %s' % Z)
    main = s([xr, yr, zr, z0, g2], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (X, Z, Y, Z))
    # left side
    xc = s([xr], 'recnd', '%s e. CC' % X); yc = s([yr], 'recnd', '%s e. CC' % Y)
    l1 = s([phD], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( ( phi ` D ) x. %s )' % (X, PD0, Q1, Q1))
    l2 = s([xc, pd0c, q1c], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (X, PD0, Q1, X, Z))
    lhs = s([l1, l2], 'eqtr3d', '( ( phi ` D ) x. %s ) = ( %s x. %s )' % (Q1, X, Z))
    r1 = s([yc, q1c, pd0c], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (Y, Q1, PD0, Y, Q1, PD0))
    r2 = s([q1c, pd0c], 'mulcomd', '( %s x. %s ) = %s' % (Q1, PD0, Z))
    r3 = s([r2], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (Y, Q1, PD0, Y, Z))
    r4 = s([r1, r3], 'eqtrd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (Y, Q1, PD0, Y, Z))
    rhs = s([phDQ, r4], 'eqtrd', '( phi ` ( D x. Q ) ) = ( %s x. %s )' % (Y, Z))
    fin = s([lhs, main], 'eqbrtrd', '( ( phi ` D ) x. %s ) <_ ( %s x. %s )' % (Q1, Y, Z))
    w.qed([fin, rhs], 'breqtrrd', S['bmtot'])
    return go(w)


ALL = {'bmeldiv': gen_eldiv, 'bmhashim': gen_hashim, 'bmhashsum': gen_hashsum, 'bmlog4': gen_log4,
       'bmpow': gen_pow, 'bmtot': gen_tot}

if __name__ == '__main__':
    for n in (only or list(ALL)):
        ALL[n]()
