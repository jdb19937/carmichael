"""Sortie Z6a (agent z6ae): I9(d), 2 ^ omega ( N ) <_ C_tau N ^ ( 1 / 800 ) (LConvexityCorollaries two_pow_card_primeFactors_le_rpow)
and its spent form (DetectionShift two_pow_card_primeFactors_le_Ctau_mul).

Route: split P = { p e. Prime | p || N } into T = { p e. P | 2 ^ 800 <_ p } and P \\ T.  The primes of P \\ T lie in
( 1 ... 2 ^ 800 ), so 2 ^ # ( P \\ T ) <_ 2 ^ ( 2 ^ 800 ) = CTau.  The product of the primes of T divides N (extrwprmdvds),
and each is at least 2 ^ 800, so ( 2 ^ # T ) ^ 800 = prod_ T 2 ^ 800 <_ prod_ T j <_ N, hence 2 ^ # T <_ N ^ ( 1 / 800 ).
The numeral 2 ^ 800 is never evaluated."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6alib import *
import num

E8 = '; ; 8 0 0'
K = '( 2 ^ %s )' % E8
P = '{ p e. Prime | p || N }'
T = '{ q e. %s | %s <_ q }' % (P, K)
D_ = '( %s \\ %s )' % (P, T)
R8 = '( 1 / %s )' % E8


def ctau_re(w):
    """closed: CTau e. RR (2 ^ 800 is never evaluated)"""
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % K)
    k0 = w.s([knn], 'nnnn0i', '%s e. NN0' % K)
    e = w.s([w.s([], '2re', '2 e. RR'), k0, w.inst('reexpcl')], 'mp2an', '( 2 ^ %s ) e. RR' % K)
    return w.s([w.s([], 'df-ctau', 'CTau = ( 2 ^ %s )' % K), e], 'eqeltri', 'CTau e. RR')


def c(w, ante, step, f):
    return w.s([step], 'a1i', '( %s -> %s )' % (ante, f))


def z6omg():
    w = W('z6omg', 'I9(d) (Lean LConvexityCorollaries two_pow_card_primeFactors_le_rpow): 2 ^ omega ( N ) <_ C_tau N ^ ( 1 / 800 ), '
                   'C_tau = 2 ^ ( 2 ^ 800 ).  The primes below 2 ^ 800 contribute at most 2 ^ ( 2 ^ 800 ); the product of the others '
                   'divides N and is at least ( 2 ^ 800 ) ^ k.')
    a = 'N e. NN'
    st = mkst(w, a)
    nn = w.s([], 'id', '( N e. NN -> N e. NN )')
    nre = st([nn], 'nnred', 'N e. RR')
    nz = st([nn], 'nnzd', 'N e. ZZ')
    # closed numerals
    e8nn = num.nn(w, 800); e8nn0 = num.nn0(w, 800); e8re = num.re_nat(w, 800); e8cc = num.cc_nat(w, 800); e8ne = num.ne0_nat(w, 800)
    knn = w.s([w.s([], '2nn', '2 e. NN'), e8nn0, w.inst('nnexpcl')], 'mp2an', '%s e. NN' % K)
    knn0 = w.s([knn], 'nnnn0i', '%s e. NN0' % K)
    kre = w.s([knn], 'nnrei', '%s e. RR' % K)
    kge0 = w.s([knn0], 'nn0ge0i', '0 <_ %s' % K)
    r8rp = num.rp(w, R8)
    # finiteness and subsets
    pf = st([nn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % P)
    tsp0 = w.s([], 'ssrab2', '%s C_ %s' % (T, P))
    psp = w.s([], 'ssrab2', '%s C_ Prime' % P)
    tpr0 = w.s([tsp0, psp], 'sstri', '%s C_ Prime' % T)
    tf = st([pf, c(w, a, tsp0, '%s C_ %s' % (T, P))], 'ssfid', '%s e. Fin' % T)
    df = st([pf, c(w, a, w.s([], 'difss', '%s C_ %s' % (D_, P)), '%s C_ %s' % (D_, P))], 'ssfid', '%s e. Fin' % D_)
    # ---- the large primes: members of T
    b = '( %s /\\ j e. %s )' % (a, T)
    sb = mkst(w, b)
    jt = w.s([], 'simpr', '( %s -> j e. %s )' % (b, T))
    elT = w.s([w.s([], 'breq2', '( q = j -> ( %s <_ q <-> %s <_ j ) )' % (K, K))], 'elrab', '( j e. %s <-> ( j e. %s /\\ %s <_ j ) )' % (T, P, K))
    jt2 = sb([jt, elT], 'sylib', '( j e. %s /\\ %s <_ j )' % (P, K))
    jP = sb([jt2], 'simpld', 'j e. %s' % P)
    kj = sb([jt2], 'simprd', '%s <_ j' % K)
    elP = w.s([w.s([], 'breq1', '( p = j -> ( p || N <-> j || N ) )')], 'elrab', '( j e. %s <-> ( j e. Prime /\\ j || N ) )' % P)
    jP2 = sb([jP, elP], 'sylib', '( j e. Prime /\\ j || N )')
    jpr = sb([jP2], 'simpld', 'j e. Prime'); jdv = sb([jP2], 'simprd', 'j || N')
    jnn = sb([jpr, w.inst('prmnn')], 'syl', 'j e. NN')
    jre = sb([jnn], 'nnred', 'j e. RR')
    allj = st([jdv], 'ralrimiva', 'A. j e. %s j || N' % T)
    fpr = st([tf, c(w, a, tpr0, '%s C_ Prime' % T)], 'jca', '( %s e. Fin /\\ %s C_ Prime )' % (T, T))
    nza = st([nz, allj], 'jca', '( N e. ZZ /\\ A. j e. %s j || N )' % T)
    PR = 'prod_ j e. %s j' % T
    dv = st([fpr, nza, w.inst('extrwprmdvds')], 'sylc', '%s || N' % PR)
    pnn = st([tf, jnn], 'fprodnncl', '%s e. NN' % PR)
    ple = st([st([st([pnn], 'nnzd', '%s e. ZZ' % PR), nn], 'jca', '( %s e. ZZ /\\ N e. NN )' % PR), dv, w.inst('dvdsle')], 'sylc', '%s <_ N' % PR)
    PK = 'prod_ j e. %s %s' % (T, K)
    nfv = w.s([], 'nfv', 'F/ j N e. NN')
    fle = st([nfv, tf, c(w, b, kre, '%s e. RR' % K), c(w, b, kge0, '0 <_ %s' % K), jre, kj], 'fprodle', '%s <_ %s' % (PK, PR))
    kcc = w.s([kre], 'recni', '%s e. CC' % K)
    fc = st([tf, c(w, a, kcc, '%s e. CC' % K), w.inst('fprodconst')], 'syl2anc', '%s = ( %s ^ ( # ` %s ) )' % (PK, K, T))
    ht0 = st([tf, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % T)
    two = w.s([], '2cn', '2 e. CC')
    em1 = st([c(w, a, two, '2 e. CC'), c(w, a, e8nn0, '%s e. NN0' % E8), ht0, w.inst('expmul')], 'syl3anc',
             '( 2 ^ ( %s x. ( # ` %s ) ) ) = ( %s ^ ( # ` %s ) )' % (E8, T, K, T))
    em2 = st([c(w, a, two, '2 e. CC'), ht0, c(w, a, e8nn0, '%s e. NN0' % E8), w.inst('expmul')], 'syl3anc',
             '( 2 ^ ( ( # ` %s ) x. %s ) ) = ( ( 2 ^ ( # ` %s ) ) ^ %s )' % (T, E8, T, E8))
    mc = st([st([ht0], 'nn0cnd', '( # ` %s ) e. CC' % T), c(w, a, e8cc, '%s e. CC' % E8)], 'mulcomd',
            '( ( # ` %s ) x. %s ) = ( %s x. ( # ` %s ) )' % (T, E8, E8, T))
    em3 = st([mc], 'oveq2d', '( 2 ^ ( ( # ` %s ) x. %s ) ) = ( 2 ^ ( %s x. ( # ` %s ) ) )' % (T, E8, E8, T))
    X = '( 2 ^ ( # ` %s ) )' % T
    X8 = '( %s ^ %s )' % (X, E8)
    q1 = st([em2, em3], 'eqtr3d', '%s = ( 2 ^ ( %s x. ( # ` %s ) ) )' % (X8, E8, T))
    q2 = st([q1, em1], 'eqtrd', '%s = ( %s ^ ( # ` %s ) )' % (X8, K, T))
    q3 = st([q2, fc], 'eqtr4d', '%s = %s' % (X8, PK))
    q4 = st([q3, fle], 'eqbrtrd', '%s <_ %s' % (X8, PR))
    pre = st([pnn], 'nnred', '%s e. RR' % PR)
    x8re = st([st([c(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), ht0], 'reexpcld', '%s e. RR' % X), c(w, a, e8nn0, '%s e. NN0' % E8)], 'reexpcld', '%s e. RR' % X8)
    q5 = st([x8re, pre, nre, q4, ple], 'letrd', '%s <_ N' % X8)
    # X8 <_ N  ->  X <_ N ^c ( 1 / 800 )
    xrp = st([c(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([ht0], 'nn0zd', '( # ` %s ) e. ZZ' % T)], 'rpexpcld', '%s e. RR+' % X)
    x8ge = st([st([xrp], 'rpred', '%s e. RR' % X), c(w, a, e8nn0, '%s e. NN0' % E8)], 'reexpcld', '%s e. RR' % X8)
    x8rp = st([xrp, st([c(w, a, e8nn0, '%s e. NN0' % E8)], 'nn0zd', '%s e. ZZ' % E8)], 'rpexpcld', '%s e. RR+' % X8)
    cx = st([st([x8rp], 'rpred', '%s e. RR' % X8), st([x8rp], 'rpge0d', '0 <_ %s' % X8)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (X8, X8))
    n0 = st([st([nn], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N')
    cN = st([nre, n0], 'jca', '( N e. RR /\\ 0 <_ N )')
    ple2 = st([cx, cN, c(w, a, r8rp, '%s e. RR+' % R8), w.inst('cxple2')], 'syl3anc',
              '( %s <_ N <-> ( %s ^c %s ) <_ ( N ^c %s ) )' % (X8, X8, R8, R8))
    q6 = st([q5, ple2], 'mpbid', '( %s ^c %s ) <_ ( N ^c %s )' % (X8, R8, R8))
    xc = st([xrp], 'rpcnd', '%s e. CC' % X)
    E1 = st([xrp, c(w, a, e8re, '%s e. RR' % E8), c(w, a, num.cc(w, R8), '%s e. CC' % R8), w.inst('cxpmul')], 'syl3anc',
            '( %s ^c ( %s x. %s ) ) = ( ( %s ^c %s ) ^c %s )' % (X, E8, R8, X, E8, R8))
    E2 = st([xc, c(w, a, e8nn0, '%s e. NN0' % E8), w.inst('cxpexp')], 'syl2anc', '( %s ^c %s ) = %s' % (X, E8, X8))
    E3 = st([E2], 'oveq1d', '( ( %s ^c %s ) ^c %s ) = ( %s ^c %s )' % (X, E8, R8, X8, R8))
    E13 = st([E1, E3], 'eqtrd', '( %s ^c ( %s x. %s ) ) = ( %s ^c %s )' % (X, E8, R8, X8, R8))
    E4 = w.s([w.s([e8cc, e8ne], 'recidi', '( %s x. %s ) = 1' % (E8, R8))], 'oveq2i', '( %s ^c ( %s x. %s ) ) = ( %s ^c 1 )' % (X, E8, R8, X))
    E14 = st([E4, E13], 'eqtr3id', '( %s ^c 1 ) = ( %s ^c %s )' % (X, X8, R8))
    E5 = st([xc, w.inst('cxp1')], 'syl', '( %s ^c 1 ) = %s' % (X, X))
    E6 = st([E14, E5], 'eqtr3d', '( %s ^c %s ) = %s' % (X8, R8, X))
    big = st([E6, q6], 'eqbrtrrd', '%s <_ ( N ^c %s )' % (X, R8))
    # ---- the small primes: P \\ T C_ ( 1 ... 2 ^ 800 )
    bb = '( %s /\\ x e. %s )' % (a, D_)
    sbb = mkst(w, bb)
    pd = w.s([], 'simpr', '( %s -> x e. %s )' % (bb, D_))
    ed = sbb([pd, w.s([], 'eldif', '( x e. %s <-> ( x e. %s /\\ -. x e. %s ) )' % (D_, P, T))], 'sylib', '( x e. %s /\\ -. x e. %s )' % (P, T))
    pP = sbb([ed], 'simpld', 'x e. %s' % P)
    npt = sbb([ed], 'simprd', '-. x e. %s' % T)
    pP2 = sbb([pP, w.s([w.s([], 'breq1', '( p = x -> ( p || N <-> x || N ) )')], 'elrab', '( x e. %s <-> ( x e. Prime /\\ x || N ) )' % P)], 'sylib', '( x e. Prime /\\ x || N )')
    ppr = sbb([pP2], 'simpld', 'x e. Prime')
    pnn2 = sbb([ppr, w.inst('prmnn')], 'syl', 'x e. NN')
    ib = sbb([pP, w.inst('ibar')], 'syl', '( %s <_ x <-> ( x e. %s /\\ %s <_ x ) )' % (K, P, K))
    ib2 = sbb([ib, w.s([w.s([], 'breq2', '( q = x -> ( %s <_ q <-> %s <_ x ) )' % (K, K))], 'elrab', '( x e. %s <-> ( x e. %s /\\ %s <_ x ) )' % (T, P, K))], 'bitr4di', '( %s <_ x <-> x e. %s )' % (K, T))
    nk = sbb([npt, ib2], 'mtbird', '-. %s <_ x' % K)
    pre2 = sbb([pnn2], 'nnred', 'x e. RR')
    kreb = c(w, bb, kre, '%s e. RR' % K)
    lt = sbb([nk, sbb([pre2, kreb], 'ltnled', '( x < %s <-> -. %s <_ x )' % (K, K))], 'mpbird', 'x < %s' % K)
    le = sbb([pre2, kreb, lt], 'ltled', 'x <_ %s' % K)
    j3 = sbb([pnn2, c(w, bb, knn, '%s e. NN' % K), le], '3jca', '( x e. NN /\\ %s e. NN /\\ x <_ %s )' % (K, K))
    efz = sbb([j3, c(w, bb, w.s([], 'elfz1b', '( x e. ( 1 ... %s ) <-> ( x e. NN /\\ %s e. NN /\\ x <_ %s ) )' % (K, K, K)),
                     '( x e. ( 1 ... %s ) <-> ( x e. NN /\\ %s e. NN /\\ x <_ %s ) )' % (K, K, K))], 'mpbird', 'x e. ( 1 ... %s )' % K)
    imp_ = st([efz], 'ex', '( x e. %s -> x e. ( 1 ... %s ) )' % (D_, K))
    ss = st([imp_], 'ssrdv', '%s C_ ( 1 ... %s )' % (D_, K))
    fzv = c(w, a, w.s([], 'ovex', '( 1 ... %s ) e. _V' % K), '( 1 ... %s ) e. _V' % K)
    hs = st([fzv, ss, w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` ( 1 ... %s ) )' % (D_, K))
    hfz = w.s([knn0, w.inst('hashfz1')], 'ax-mp', '( # ` ( 1 ... %s ) ) = %s' % (K, K))
    hk = st([hs, hfz], 'breqtrdi', '( # ` %s ) <_ %s' % (D_, K))
    hd0 = st([df, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % D_)
    uz = st([st([st([hd0], 'nn0zd', '( # ` %s ) e. ZZ' % D_), c(w, a, w.s([knn], 'nnzi', '%s e. ZZ' % K), '%s e. ZZ' % K), hk], '3jca',
                '( ( # ` %s ) e. ZZ /\\ %s e. ZZ /\\ ( # ` %s ) <_ %s )' % (D_, K, D_, K)),
             c(w, a, w.s([], 'eluz2', '( %s e. ( ZZ>= ` ( # ` %s ) ) <-> ( ( # ` %s ) e. ZZ /\\ %s e. ZZ /\\ ( # ` %s ) <_ %s ) )' % (K, D_, D_, K, D_, K)),
               '( %s e. ( ZZ>= ` ( # ` %s ) ) <-> ( ( # ` %s ) e. ZZ /\\ %s e. ZZ /\\ ( # ` %s ) <_ %s ) )' % (K, D_, D_, K, D_, K))],
            'mpbird', '%s e. ( ZZ>= ` ( # ` %s ) )' % (K, D_))
    lx = st([c(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), c(w, a, w.s([], '1le2', '1 <_ 2'), '1 <_ 2'), uz, w.inst('leexp2a')], 'syl3anc',
            '( 2 ^ ( # ` %s ) ) <_ ( 2 ^ %s )' % (D_, K))
    small = st([lx, w.s([], 'df-ctau', 'CTau = ( 2 ^ %s )' % K)], 'breqtrrdi', '( 2 ^ ( # ` %s ) ) <_ CTau' % D_)
    # ---- assembly
    un = w.s([tsp0, w.s([], 'undif', '( %s C_ %s <-> ( %s u. %s ) = %s )' % (T, P, T, D_, P))], 'mpbi', '( %s u. %s ) = %s' % (T, D_, P))
    hu0 = w.s([un], 'fveq2i', '( # ` ( %s u. %s ) ) = ( # ` %s )' % (T, D_, P))
    hu = st([tf, df, c(w, a, w.s([], 'disjdif', '( %s i^i %s ) = (/)' % (T, D_)), '( %s i^i %s ) = (/)' % (T, D_)), w.inst('hashun')], 'syl3anc',
            '( # ` ( %s u. %s ) ) = ( ( # ` %s ) + ( # ` %s ) )' % (T, D_, T, D_))
    hp = st([hu0, hu], 'eqtr3id', '( # ` %s ) = ( ( # ` %s ) + ( # ` %s ) )' % (P, T, D_))
    x1 = st([hp], 'oveq2d', '%s = ( 2 ^ ( ( # ` %s ) + ( # ` %s ) ) )' % (OMG(), T, D_))
    x2 = st([c(w, a, two, '2 e. CC'), ht0, hd0, w.inst('expadd')], 'syl3anc',
            '( 2 ^ ( ( # ` %s ) + ( # ` %s ) ) ) = ( %s x. ( 2 ^ ( # ` %s ) ) )' % (T, D_, X, D_))
    x3 = st([x1, x2], 'eqtrd', '%s = ( %s x. ( 2 ^ ( # ` %s ) ) )' % (OMG(), X, D_))
    XD = '( 2 ^ ( # ` %s ) )' % D_
    xdrp = st([c(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([hd0], 'nn0zd', '( # ` %s ) e. ZZ' % D_)], 'rpexpcld', '%s e. RR+' % XD)
    ctre = ctau_re(w)
    nr8 = st([nre, n0, c(w, a, num.real(w, R8), '%s e. RR' % R8)], 'recxpcld', '( N ^c %s ) e. RR' % R8)
    m = st([st([xrp], 'rpred', '%s e. RR' % X), nr8, st([xdrp], 'rpred', '%s e. RR' % XD), c(w, a, ctre, 'CTau e. RR'),
            st([xrp], 'rpge0d', '0 <_ %s' % X), st([xdrp], 'rpge0d', '0 <_ %s' % XD), big, small], 'lemul12ad',
           '( %s x. %s ) <_ ( ( N ^c %s ) x. CTau )' % (X, XD, R8))
    mc2 = st([st([nr8], 'recnd', '( N ^c %s ) e. CC' % R8), c(w, a, w.s([ctre], 'recni', 'CTau e. CC'), 'CTau e. CC')], 'mulcomd',
             '( ( N ^c %s ) x. CTau ) = ( CTau x. ( N ^c %s ) )' % (R8, R8))
    m2 = st([m, mc2], 'breqtrd', '( %s x. %s ) <_ ( CTau x. ( N ^c %s ) )' % (X, XD, R8))
    w.qed([x3, m2], 'eqbrtrd', STATEMENTS['z6omg'])
    return w


def z6omgd():
    w = W('z6omgd', 'Lean two_pow_card_primeFactors_le_Ctau_mul: z6omg with N <_ D, 2 ^ omega ( N ) <_ C_tau D ^ ( 1 / 800 ).')
    a = ante('z6omgd')
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN'); dr = st([], 'simprl', 'D e. RR'); nd = st([], 'simprr', 'N <_ D')
    om = st([nn, w.inst('z6omg')], 'syl', '%s <_ ( CTau x. ( N ^c %s ) )' % (OMG(), R8))
    nre = st([nn], 'nnred', 'N e. RR')
    n0 = st([st([nn], 'nnnn0d', 'N e. NN0')], 'nn0ge0d', '0 <_ N')
    d0 = st([c(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), nre, dr, n0, nd], 'letrd', '0 <_ D')
    r8rp = num.rp(w, R8)
    le2 = st([st([nre, n0], 'jca', '( N e. RR /\\ 0 <_ N )'), st([dr, d0], 'jca', '( D e. RR /\\ 0 <_ D )'), c(w, a, r8rp, '%s e. RR+' % R8),
              w.inst('cxple2')], 'syl3anc', '( N <_ D <-> ( N ^c %s ) <_ ( D ^c %s ) )' % (R8, R8))
    pw = st([nd, le2], 'mpbid', '( N ^c %s ) <_ ( D ^c %s )' % (R8, R8))
    r8 = c(w, a, num.real(w, R8), '%s e. RR' % R8)
    nr8 = st([nre, n0, r8], 'recxpcld', '( N ^c %s ) e. RR' % R8)
    dr8 = st([dr, d0, r8], 'recxpcld', '( D ^c %s ) e. RR' % R8)
    ctre = ctau_re(w)
    ctge = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], '0le2', '0 <_ 2'),
                     w.s([w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % K)], 'nnnn0i', '%s e. NN0' % K),
                     w.inst('expge0')], 'mp3an', '0 <_ ( 2 ^ %s )' % K), w.s([], 'df-ctau', 'CTau = ( 2 ^ %s )' % K)], 'breqtrri', '0 <_ CTau')
    m = st([nr8, dr8, c(w, a, ctre, 'CTau e. RR'), c(w, a, ctge, '0 <_ CTau'), pw], 'lemul2ad',
           '( CTau x. ( N ^c %s ) ) <_ ( CTau x. ( D ^c %s ) )' % (R8, R8))
    omre = st([c(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), st([st([nn, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % P), w.inst('hashcl')], 'syl',
                                                                 '( # ` %s ) e. NN0' % P)], 'reexpcld', '%s e. RR' % OMG())
    ctr = c(w, a, ctre, 'CTau e. RR')
    w.qed([omre, st([ctr, nr8], 'remulcld', '( CTau x. ( N ^c %s ) ) e. RR' % R8), st([ctr, dr8], 'remulcld', '( CTau x. ( D ^c %s ) ) e. RR' % R8), om, m],
          'letrd', STATEMENTS['z6omgd'])
    return w


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        run(w)
