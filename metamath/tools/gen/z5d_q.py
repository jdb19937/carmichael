"""Sortie Z5d, section Q: the sifted factor Q_R (Detection.lean 815-1146)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5dlib import *
from cl import Closure, lift, split_imp
import lin
import num

QS_ = QSQ(); QU = QSU(); QN = QRN(); QP = QRP()
PFN = lambda X, v='q': '{ %s e. Prime | %s || %s }' % (v, v, X)


def qsfacts(w, a, nn):
    """( a -> QU e. Fin ), ( a -> QU C_ Prime ), closed QU = QS_, from nn: ( a -> N e. NN )"""
    st = mkst(w, a)
    sub = w.s([w.s([], 'simpl', '( ( u || N /\\ u <_ R ) -> u || N )')], 'a1i', '( u e. Prime -> ( ( u || N /\\ u <_ R ) -> u || N ) )')
    ss = w.s([sub], 'ss2rabi', '%s C_ %s' % (QU, PFN('N', 'u')))
    cb = w.s([w.s([], 'breq1', '( p = u -> ( p || N <-> u || N ) )')], 'cbvrabv', '%s = %s' % (PFN('N', 'p'), PFN('N', 'u')))
    pf = st([a1(w, a, cb, '%s = %s' % (PFN('N', 'p'), PFN('N', 'u'))), sy(w, a, nn, 'prmdvdsfi', '%s e. Fin' % PFN('N', 'p'))], 'eqeltrrd', '%s e. Fin' % PFN('N', 'u'))
    fin = st([pf, a1(w, a, ss, '%s C_ %s' % (QU, PFN('N', 'u')))], 'ssfid', '%s e. Fin' % QU)
    sp = a1(w, a, w.s([], 'ssrab2', '%s C_ Prime' % QU), '%s C_ Prime' % QU)
    uq = w.s([w.s([w.s([], 'breq1', '( u = q -> ( u || N <-> q || N ) )'), w.s([], 'breq1', '( u = q -> ( u <_ R <-> q <_ R ) )')], 'anbi12d',
                  '( u = q -> ( ( u || N /\\ u <_ R ) <-> ( q || N /\\ q <_ R ) ) )')], 'cbvrabv', '%s = %s' % (QU, QS_))
    return fin, sp, uq


def z5dqr():
    w = W('z5dqr', "The R-smooth radical q_R = prod over the primes p || N with p <_ R of p (Lean qR) is a squarefree positive integer "
                   "whose prime factors are exactly those primes, and phi ( q_R ) / q_R is the sifted factor Q_R = prod ( 1 - 1 / p ) "
                   "(Lean qR_squarefree, qR_pos, qR_primeFactors, QR, QR_eq_prod).")
    a = 'N e. NN'
    st = mkst(w, a)
    nn = st([], 'id', 'N e. NN')
    fin, sp, uq = qsfacts(w, a, nn)
    PP = 'prod_ p e. %s p' % QU
    sq = st([fin, sp, w.inst('sqfprod')], 'syl2anc', '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )' % (PP, PP, PFN(PP), QU))
    cp = w.s([w.s([], 'id', '( p = w -> p = w )')], 'cbvprodv', '%s = %s' % (PP, QN))
    cpa = a1(w, a, cp, '%s = %s' % (PP, QN))
    s1 = st([sq], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (PP, PP))
    qn = st([cpa, st([s1], 'simpld', '%s e. NN' % PP)], 'eqeltrrd', '%s e. NN' % QN)
    mu = st([st([cpa], 'fveq2d', '( mmu ` %s ) = ( mmu ` %s )' % (PP, QN)), st([s1], 'simprd', '( mmu ` %s ) =/= 0' % PP)], 'eqnetrrd', '( mmu ` %s ) =/= 0' % QN)
    pfe = st([sq], 'simprd', '%s = %s' % (PFN(PP), QU))
    pfq = st([st([cpa], 'breq2d', '( q || %s <-> q || %s )' % (PP, QN))], 'rabbidv', '%s = %s' % (PFN(PP), PFN(QN)))
    pf2 = st([st([pfq, pfe], 'eqtr3d', '%s = %s' % (PFN(QN), QU)), a1(w, a, uq, '%s = %s' % (QU, QS_))], 'eqtrd', '%s = %s' % (PFN(QN), QS_))
    ph = sy(w, a, qn, 'phipfprod', 'prod_ p e. %s ( 1 - ( 1 / p ) ) = ( ( phi ` %s ) / %s )' % (PFN(QN), QN, QN))
    ph2 = st([st([pf2], 'prodeq1d', 'prod_ p e. %s ( 1 - ( 1 / p ) ) = %s' % (PFN(QN), QP)), ph], 'eqtr3d', '%s = ( ( phi ` %s ) / %s )' % (QP, QN, QN))
    w.qed([st([qn, mu], 'jca', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (QN, QN)), st([pf2, st([ph2], 'eqcomd', '( ( phi ` %s ) / %s ) = %s' % (QN, QN, QP))], 'jca',
                                                                                      '( %s = %s /\\ ( ( phi ` %s ) / %s ) = %s )' % (PFN(QN), QS_, QN, QN, QP))],
          'jca', STATEMENTS['z5dqr'])
    return w


def elqs(w, X, S_=None):
    """closed: ( X e. QS_ <-> ( X e. Prime /\\ ( X || N /\\ X <_ R ) ) )"""
    c = w.s([w.s([], 'breq1', '( q = %s -> ( q || N <-> %s || N ) )' % (X, X)), w.s([], 'breq1', '( q = %s -> ( q <_ R <-> %s <_ R ) )' % (X, X))], 'anbi12d',
            '( q = %s -> ( ( q || N /\\ q <_ R ) <-> ( %s || N /\\ %s <_ R ) ) )' % (X, X, X))
    return w.s([c], 'elrab', '( %s e. %s <-> ( %s e. Prime /\\ ( %s || N /\\ %s <_ R ) ) )' % (X, QS_, X, X, X))


def elpfn(w, X, M):
    """closed: ( X e. PFN(M) <-> ( X e. Prime /\\ X || M ) )"""
    return w.s([w.s([], 'breq1', '( q = %s -> ( q || %s <-> %s || %s ) )' % (X, M, X, M))], 'elrab', '( %s e. %s <-> ( %s e. Prime /\\ %s || %s ) )' % (X, PFN(M), X, X, M))


def qrfacts(w, a, nn):
    st = mkst(w, a)
    q = sy(w, a, nn, 'z5dqr', cns('z5dqr'))
    s1 = st([q], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (QN, QN))
    s2 = st([q], 'simprd', '( %s = %s /\\ ( ( phi ` %s ) / %s ) = %s )' % (PFN(QN), QS_, QN, QN, QP))
    return dict(sqf=s1, qn=st([s1], 'simpld', '%s e. NN' % QN), pf=st([s2], 'simpld', '%s = %s' % (PFN(QN), QS_)),
                ph=st([s2], 'simprd', '( ( phi ` %s ) / %s ) = %s' % (QN, QN, QP)))


def z5dqrset():
    w = W('z5dqrset', "The structural key of the Q_R block (Lean coprime_qR_iff, hRsetq): an integer k <_ R is coprime to q_R exactly "
                      "when it is coprime to N, since its prime factors are <_ R; so RSet is the same at the moduli q_R and N.")
    a = '( N e. NN /\\ R e. RR )'
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN'); rr = st([], 'simpr', 'R e. RR')
    f = qrfacts(w, a, nn)
    # q_R || N
    ap = '( %s /\\ p e. Prime )' % a
    sp = mkst(w, ap)
    apd = '( %s /\\ p || %s )' % (ap, QN)
    sd = mkst(w, apd)
    pin = sd([sd([sd([], 'simplr', 'p e. Prime'), sd([], 'simpr', 'p || %s' % QN)], 'jca', '( p e. Prime /\\ p || %s )' % QN),
              a1(w, apd, elpfn(w, 'p', QN), '( p e. %s <-> ( p e. Prime /\\ p || %s ) )' % (PFN(QN), QN))], 'mpbird', 'p e. %s' % PFN(QN))
    pqs = sd([pin, lift(w, f['pf'], apd)], 'eleqtrd', 'p e. %s' % QS_)
    pn = sd([sd([sd([pqs, a1(w, apd, elqs(w, 'p'), '( p e. %s <-> ( p e. Prime /\\ ( p || N /\\ p <_ R ) ) )' % QS_)], 'mpbid', '( p e. Prime /\\ ( p || N /\\ p <_ R ) )')],
                'simprd', '( p || N /\\ p <_ R )')], 'simpld', 'p || N')
    ra = st([w.s([pn], 'ex', '( %s -> ( p || %s -> p || N ) )' % (ap, QN))], 'ralrimiva', 'A. p e. Prime ( p || %s -> p || N )' % QN)
    qd = st([f['sqf'], st([nn, ra], 'jca', '( N e. NN /\\ A. p e. Prime ( p || %s -> p || N ) )' % QN), w.inst('z5sqfpdvd')], 'syl2anc', '%s || N' % QN)
    # per k
    FZ = '( 1 ... ( |_ ` R ) )'
    ak = '( %s /\\ k e. %s )' % (a, FZ)
    sk = mkst(w, ak)
    lk = lambda x: lift(w, x, ak)
    kin = sk([], 'simpr', 'k e. %s' % FZ)
    kn = sy(w, ak, kin, 'elfznn', 'k e. NN')
    kfl = sy(w, ak, kin, 'elfzle2', 'k <_ ( |_ ` R )')
    klr = sk([sk([kn], 'nnred', 'k e. RR'), sk([sk([lk(rr)], 'flcld', '( |_ ` R ) e. ZZ')], 'zred', '( |_ ` R ) e. RR'),
              lk(rr), kfl, sy(w, ak, lk(rr), 'flle', '( |_ ` R ) <_ R')], 'letrd', 'k <_ R')
    qnk = lk(f['qn']); nnk = lk(nn)
    # <-: coprime to N gives coprime to q_R
    ag = '( %s /\\ ( k gcd N ) = 1 )' % ak
    sg = mkst(w, ag)
    lg = lambda x: lift(w, x, ag)
    bwd0 = sg([sg([sg([lg(kn)], 'nnzd', 'k e. ZZ'), sg([lg(qnk)], 'nnzd', '%s e. ZZ' % QN), sg([lg(nnk)], 'nnzd', 'N e. ZZ')], '3jca', '( k e. ZZ /\\ %s e. ZZ /\\ N e. ZZ )' % QN),
               sg([sg([], 'simpr', '( k gcd N ) = 1'), lg(lk(qd))], 'jca', '( ( k gcd N ) = 1 /\\ %s || N )' % QN), w.inst('rpdvds')], 'syl2anc', '( k gcd %s ) = 1' % QN)
    bwd = w.s([bwd0], 'ex', '( %s -> ( ( k gcd N ) = 1 -> ( k gcd %s ) = 1 ) )' % (ak, QN))
    # ->: a common prime of k and N is a common prime of k and q_R
    akp = '( %s /\\ p e. Prime )' % ak
    ac = '( %s /\\ ( p || k /\\ p || N ) )' % akp
    sc = mkst(w, ac)
    lc = lambda x: lift(w, x, ac)
    pp = sc([], 'simplr', 'p e. Prime')
    pk = sc([sc([], 'simpr', '( p || k /\\ p || N )')], 'simpld', 'p || k')
    pN = sc([sc([], 'simpr', '( p || k /\\ p || N )')], 'simprd', 'p || N')
    pz = sy(w, ac, sy(w, ac, pp, 'prmnn', 'p e. NN'), 'nnz', 'p e. ZZ')
    ple = sc([pk, sc([pz, lc(kn), w.inst('dvdsle')], 'syl2anc', '( p || k -> p <_ k )')], 'mpd', 'p <_ k')
    plr = sc([sy(w, ac, pz, 'zre', 'p e. RR'), sc([lc(kn)], 'nnred', 'k e. RR'), lc(lk(rr)), ple, lc(klr)], 'letrd', 'p <_ R')
    pq = sc([sc([pp, sc([pN, plr], 'jca', '( p || N /\\ p <_ R )')], 'jca', '( p e. Prime /\\ ( p || N /\\ p <_ R ) )'),
             a1(w, ac, elqs(w, 'p'), '( p e. %s <-> ( p e. Prime /\\ ( p || N /\\ p <_ R ) ) )' % QS_)], 'mpbird', 'p e. %s' % QS_)
    ppf = sc([pq, lc(lk(f['pf']))], 'eleqtrrd', 'p e. %s' % PFN(QN))
    pdq = sc([sc([ppf, a1(w, ac, elpfn(w, 'p', QN), '( p e. %s <-> ( p e. Prime /\\ p || %s ) )' % (PFN(QN), QN))], 'mpbid', '( p e. Prime /\\ p || %s )' % QN)],
             'simprd', 'p || %s' % QN)
    imp = w.s([sc([pk, pdq], 'jca', '( p || k /\\ p || %s )' % QN)], 'ex', '( %s -> ( ( p || k /\\ p || N ) -> ( p || k /\\ p || %s ) ) )' % (akp, QN))
    rx = w.s([imp], 'reximdva', '( %s -> ( E. p e. Prime ( p || k /\\ p || N ) -> E. p e. Prime ( p || k /\\ p || %s ) ) )' % (ak, QN))
    b1 = sk([kn, nnk], 'prmdvdsncoprmbd', '( E. p e. Prime ( p || k /\\ p || N ) <-> ( k gcd N ) =/= 1 )')
    b2 = sk([kn, qnk], 'prmdvdsncoprmbd', '( E. p e. Prime ( p || k /\\ p || %s ) <-> ( k gcd %s ) =/= 1 )' % (QN, QN))
    i1 = sk([rx, b1], 'sylbird', '( ( k gcd N ) =/= 1 -> E. p e. Prime ( p || k /\\ p || %s ) )' % QN)
    i2 = sk([i1, b2], 'sylibd', '( ( k gcd N ) =/= 1 -> ( k gcd %s ) =/= 1 )' % QN)
    fwd = sk([i2], 'necon4d', '( ( k gcd %s ) = 1 -> ( k gcd N ) = 1 )' % QN)
    eq = sk([fwd, bwd], 'impbid', '( ( k gcd %s ) = 1 <-> ( k gcd N ) = 1 )' % QN)
    eq2 = sk([eq], 'anbi2d', '( ( ( mmu ` k ) =/= 0 /\\ ( k gcd %s ) = 1 ) <-> ( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 ) )' % QN)
    rb = st([eq2], 'rabbidva', '{ k e. %s | ( ( mmu ` k ) =/= 0 /\\ ( k gcd %s ) = 1 ) } = { k e. %s | ( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 ) }' % (FZ, QN, FZ))
    v1 = st([f['qn'], rr, w.inst('z5rsetval')], 'syl2anc', '( %s RSet R ) = { k e. %s | ( ( mmu ` k ) =/= 0 /\\ ( k gcd %s ) = 1 ) }' % (QN, FZ, QN))
    v2 = st([nn, rr, w.inst('z5rsetval')], 'syl2anc', '( N RSet R ) = { k e. %s | ( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 ) }' % FZ)
    w.qed([st([v1, rb], 'eqtrd', '( %s RSet R ) = { k e. %s | ( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 ) }' % (QN, FZ)), v2], 'eqtr4d', STATEMENTS['z5dqrset'])
    return w


def primefac(w, ante, pp, v='p'):
    """from pp: ( ante -> v e. Prime ): the Euler factor ( 1 - ( 1 / v ) ) is real, in ( 0 , 1 ]"""
    s = mkst(w, ante)
    vn = sy(w, ante, pp, 'prmnn', '%s e. NN' % v)
    vr = s([vn], 'nnred', '%s e. RR' % v)
    v1 = sy(w, ante, pp, 'prmgt1', '1 < %s' % v)
    rc = s([vr, v1, w.inst('recgt1i')], 'syl2anc', '( 0 < ( 1 / %s ) /\\ ( 1 / %s ) < 1 )' % (v, v))
    iv = '( 1 / %s )' % v
    ir = s([vn], 'nnrecred', '%s e. RR' % iv)
    F = '( 1 - %s )' % iv
    lv = {iv: ('RR', ir)}
    gt0 = lin.linarith(w, ante, [s([rc], 'simprd', '%s < 1' % iv)], '0 < %s' % F, leaves=lv, atoms=[iv])
    le1 = lin.linarith(w, ante, [s([rc], 'simpld', '0 < %s' % iv)], '%s <_ 1' % F, leaves=lv, atoms=[iv])
    fr = s([s([], '1red', '1 e. RR'), ir], 'resubcld', '%s e. RR' % F)
    return dict(vn=vn, vr=vr, ir=ir, fr=fr, gt0=gt0, ge0=s([gt0], 'ltled', '0 <_ %s' % F), le1=le1, fc=s([fr], 'recnd', '%s e. CC' % F))


def z5dtotqr():
    w = W('z5dtotqr', "phi ( N ) / N <_ Q_R (Lean totient_div_le_QR): phi ( N ) / N = prod over the primes of N of ( 1 - 1 / p ) "
                      "(phipfprod), and the factors at the primes p > R lie in ( 0 , 1 ].")
    a = 'N e. NN'
    st = mkst(w, a)
    nn = st([], 'id', 'N e. NN')
    PF = PFN('N')
    ph = sy(w, a, nn, 'phipfprod', 'prod_ p e. %s ( 1 - ( 1 / p ) ) = ( ( phi ` N ) / N )' % PF)
    ss = w.s([w.s([w.s([], 'simpl', '( ( q || N /\\ q <_ R ) -> q || N )')], 'a1i', '( q e. Prime -> ( ( q || N /\\ q <_ R ) -> q || N ) )')],
             'ss2rabi', '%s C_ %s' % (QS_, PF))
    RS = '( %s \\ %s )' % (PF, QS_)
    un = w.s([ss, w.s([], 'undif', '( %s C_ %s <-> ( %s u. %s ) = %s )' % (QS_, PF, QS_, RS, PF))], 'mpbi', '( %s u. %s ) = %s' % (QS_, RS, PF))
    dj = a1(w, a, w.s([], 'disjdif', '( %s i^i %s ) = (/)' % (QS_, RS)), '( %s i^i %s ) = (/)' % (QS_, RS))
    un2 = a1(w, a, w.s([un], 'eqcomi', '%s = ( %s u. %s )' % (PF, QS_, RS)), '%s = ( %s u. %s )' % (PF, QS_, RS))
    pfin = sy(w, a, nn, 'prmdvdsfi', '%s e. Fin' % PFN('N', 'p'))
    cbq = a1(w, a, w.s([w.s([], 'breq1', '( p = q -> ( p || N <-> q || N ) )')], 'cbvrabv', '%s = %s' % (PFN('N', 'p'), PF)), '%s = %s' % (PFN('N', 'p'), PF))
    fin = st([cbq, pfin], 'eqeltrrd', '%s e. Fin' % PF)
    E = '( 1 - ( 1 / p ) )'
    def ctx(Sset):
        ap = '( %s /\\ p e. %s )' % (a, Sset)
        return ap
    apf = ctx(PF)
    ppf = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (apf, PF)), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % apf)
    fpf = primefac(w, apf, ppf)
    spl = st([dj, un2, fin, fpf['fc']], 'fprodsplit', 'prod_ p e. %s %s = ( prod_ p e. %s %s x. prod_ p e. %s %s )' % (PF, E, QS_, E, RS, E))
    aq = ctx(QS_)
    pq = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (aq, QS_)), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % aq)
    fq = primefac(w, aq, pq)
    ar = ctx(RS)
    pr_ = w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (ar, RS)), w.inst('eldifi')], 'syl', '( %s -> p e. %s )' % (ar, PF)), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % ar)
    fr_ = primefac(w, ar, pr_)
    qfin = st([fin, a1(w, a, ss, '%s C_ %s' % (QS_, PF))], 'ssfid', '%s e. Fin' % QS_)
    rfin = st([fin, a1(w, a, w.s([], 'difss', '%s C_ %s' % (RS, PF)), '%s C_ %s' % (RS, PF))], 'ssfid', '%s e. Fin' % RS)
    nf = w.s([], 'nfv', 'F/ p %s' % a)
    PQ = 'prod_ p e. %s %s' % (QS_, E); PR = 'prod_ p e. %s %s' % (RS, E)
    pqr = st([qfin, fq['fr']], 'fprodrecl', '%s e. RR' % PQ)
    pq0 = w.s([nf, qfin, fq['fr'], fq['ge0']], 'fprodge0', '( %s -> 0 <_ %s )' % (a, PQ))
    prr = st([rfin, fr_['fr']], 'fprodrecl', '%s e. RR' % PR)
    le = w.s([nf, rfin, fr_['fr'], fr_['ge0'], w.s([], '1red', '( %s -> 1 e. RR )' % ar), fr_['le1']], 'fprodle', '( %s -> %s <_ prod_ p e. %s 1 )' % (a, PR, RS))
    p1 = st([st([rfin], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (RS, RS)), w.inst('prod1')], 'syl', 'prod_ p e. %s 1 = 1' % RS)
    le1 = st([le, p1], 'breqtrd', '%s <_ 1' % PR)
    m = st([prr, litr(w, a, '1'), pqr, pq0, le1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 1 )' % (PQ, PR, PQ))
    m2 = st([m, st([st([pqr], 'recnd', '%s e. CC' % PQ)], 'mulridd', '( %s x. 1 ) = %s' % (PQ, PQ))], 'breqtrd', '( %s x. %s ) <_ %s' % (PQ, PR, PQ))
    w.qed([st([ph, spl], 'eqtr3d', '( ( phi ` N ) / N ) = ( %s x. %s )' % (PQ, PR)), m2], 'eqbrtrd', STATEMENTS['z5dtotqr'])
    return w


def z5dp1qr():
    w = W('z5dp1qr', "Blueprint interface I9(b) in the sifted form (Lean P1_lower_log_QR, frozen Z6c-Q first display): "
                     "( 1 / 2 ) Q_R log R <_ P ( 1 ): P1_lower_log (z5dp1k) read at the modulus q_R, where Q_R = phi ( q_R ) / q_R and "
                     "RSet is unchanged (z5dqr, z5dqrset).")
    a = '( N e. NN /\\ R e. RR+ )'
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN'); rp = st([], 'simpr', 'R e. RR+')
    f = qrfacts(w, a, nn)
    L = '( log ` R )'
    b = st([f['qn'], rp, w.inst('z5dp1k')], 'syl2anc', '( ( ( 1 / 2 ) x. ( ( phi ` %s ) / %s ) ) x. %s ) <_ %s' % (QN, QN, L, P1(QN, 'R')))
    e1 = st([st([f['ph']], 'oveq2d', '( ( 1 / 2 ) x. ( ( phi ` %s ) / %s ) ) = ( ( 1 / 2 ) x. %s )' % (QN, QN, QP))], 'oveq1d',
            '( ( ( 1 / 2 ) x. ( ( phi ` %s ) / %s ) ) x. %s ) = ( ( ( 1 / 2 ) x. %s ) x. %s )' % (QN, QN, L, QP, L))
    rs = st([nn, st([rp], 'rpred', 'R e. RR'), w.inst('z5dqrset')], 'syl2anc', '( %s RSet R ) = ( N RSet R )' % QN)
    e2 = st([rs], 'sumeq1d', '%s = %s' % (P1(QN, 'R'), P1('N', 'R')))
    w.qed([e1, b, e2], '3brtr3d', STATEMENTS['z5dp1qr'])
    return w


def z5dp1qrd():
    w = W('z5dp1qrd', "The Q_R form of P1_lower (Lean P1_lower_QR, frozen Z6c-Q, Rpar corollary): ( 1 / 200 ) Q_R log D <_ P ( 1 ) "
                      "at R = D ^ ( 1 / 100 ).")
    a = '( N e. NN /\\ D e. RR+ )'
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN'); dp = st([], 'simpr', 'D e. RR+')
    rp = st([dp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % RPD)
    L = '( log ` D )'; LR = '( log ` %s )' % RPD
    q = QRP('N', RPD)
    b = st([nn, rp, w.inst('z5dp1qr')], 'syl2anc', '( ( ( 1 / 2 ) x. %s ) x. %s ) <_ %s' % (q, LR, P1D))
    lc = st([dp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'logcxpd', '%s = ( ( 1 / ; ; 1 0 0 ) x. %s )' % (LR, L))
    b2 = st([st([lc], 'oveq2d', '( ( ( 1 / 2 ) x. %s ) x. %s ) = ( ( ( 1 / 2 ) x. %s ) x. ( ( 1 / ; ; 1 0 0 ) x. %s ) )' % (q, LR, q, L)), b], 'eqbrtrrd',
            '( ( ( 1 / 2 ) x. %s ) x. ( ( 1 / ; ; 1 0 0 ) x. %s ) ) <_ %s' % (q, L, P1D))
    # Q_R is real: a finite product of reals
    aq = '( %s /\\ p e. %s )' % (a, QSQ('N', RPD))
    pq = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (aq, QSQ('N', RPD))), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % aq)
    fq = primefac(w, aq, pq)
    sub = w.s([w.s([w.s([], 'simpl', '( ( q || N /\\ q <_ %s ) -> q || N )' % RPD)], 'a1i', '( q e. Prime -> ( ( q || N /\\ q <_ %s ) -> q || N ) )' % RPD)],
              'ss2rabi', '%s C_ %s' % (QSQ('N', RPD), PFN('N')))
    pfin = st([a1(w, a, w.s([w.s([], 'breq1', '( p = q -> ( p || N <-> q || N ) )')], 'cbvrabv', '%s = %s' % (PFN('N', 'p'), PFN('N'))), '%s = %s' % (PFN('N', 'p'), PFN('N'))),
               sy(w, a, nn, 'prmdvdsfi', '%s e. Fin' % PFN('N', 'p'))], 'eqeltrrd', '%s e. Fin' % PFN('N'))
    qfin = st([pfin, a1(w, a, sub, '%s C_ %s' % (QSQ('N', RPD), PFN('N')))], 'ssfid', '%s e. Fin' % QSQ('N', RPD))
    qr = st([qfin, fq['fr']], 'fprodrecl', '%s e. RR' % q)
    lr = st([dp], 'relogcld', '%s e. RR' % L)
    cl = Closure(w, a, {q: [('RR', qr)], L: [('RR', lr)]})
    cl.atom(q); cl.atom(L)
    e = lin.lineq(w, a, '( ( ( 1 / ; ; 2 0 0 ) x. %s ) x. %s )' % (q, L), '( ( ( 1 / 2 ) x. %s ) x. ( ( 1 / ; ; 1 0 0 ) x. %s ) )' % (q, L), closure=cl, products=True)
    w.qed([e, b2], 'eqbrtrd', STATEMENTS['z5dp1qrd'])
    return w


def z5dp1mert():
    w = W('z5dp1mert', "Blueprint interface I9(c) upper bound in the Q_R form (Lean P1_le_QR_mul_MertensProd, frozen Z6c-Q third display): "
                       "P ( 1 ) <_ Q_R prod over the primes p <_ R of ( 1 - 1 / p ) ^ -1: every r in RSet is built from primes <_ R not "
                       "dividing N, so P ( 1 ) is at most V3's smooth sum over those primes (smsum), and the Euler product over the primes "
                       "p <_ R splits along p || N, the p || N half cancelling Q_R.")
    a = '( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) )'
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN'); rr = st([], 'simprl', 'R e. RR'); r1 = st([], 'simprr', '1 <_ R')
    W_ = '( |_ ` R )'; FZ = '( 1 ... %s )' % W_; PR = '( %s i^i Prime )' % FZ; S = '( %s \\ %s )' % (PR, QS_)
    SM = '{ v e. %s | { r e. Prime | r || v } C_ %s }' % (FZ, S)
    RS = '( N RSet R )'
    wn = st([rr, r1, w.inst('flge1nn')], 'syl2anc', '%s e. NN' % W_)
    wz = st([wn], 'nnzd', '%s e. ZZ' % W_)
    def infz(ante, X, xn, xle):
        s_ = mkst(w, ante)
        return s_([s_([xn, xle], 'jca', '( %s e. NN /\\ %s <_ %s )' % (X, X, W_)), s_([lift(w, wz, ante), w.inst('fznn')], 'syl', '( %s e. %s <-> ( %s e. NN /\\ %s <_ %s ) )' % (X, FZ, X, X, W_))],
                  'mpbird', '%s e. %s' % (X, FZ))
    def inpr(ante, X, xfz, xp):
        s_ = mkst(w, ante)
        return s_([s_([xfz, xp], 'jca', '( %s e. %s /\\ %s e. Prime )' % (X, FZ, X)), a1(w, ante, w.s([], 'elin', '( %s e. %s <-> ( %s e. %s /\\ %s e. Prime ) )' % (X, PR, X, FZ, X)),
                                                                                         '( %s e. %s <-> ( %s e. %s /\\ %s e. Prime ) )' % (X, PR, X, FZ, X))], 'mpbird', '%s e. %s' % (X, PR))
    # (A) QS_ C_ PR
    ay = '( %s /\\ y e. %s )' % (a, QS_)
    sy_ = mkst(w, ay)
    yq = sy_([sy_([], 'simpr', 'y e. %s' % QS_), a1(w, ay, elqs(w, 'y'), '( y e. %s <-> ( y e. Prime /\\ ( y || N /\\ y <_ R ) ) )' % QS_)], 'mpbid',
             '( y e. Prime /\\ ( y || N /\\ y <_ R ) )')
    yp = sy_([yq], 'simpld', 'y e. Prime'); yr = sy_([sy_([yq], 'simprd', '( y || N /\\ y <_ R )')], 'simprd', 'y <_ R')
    yn = sy(w, ay, yp, 'prmnn', 'y e. NN')
    yw = sy_([yr, sy_([lift(w, rr, ay), sy_([yn], 'nnzd', 'y e. ZZ'), w.inst('flge')], 'syl2anc', '( y <_ R <-> y <_ %s )' % W_)], 'mpbid', 'y <_ %s' % W_)
    ypr = inpr(ay, 'y', infz(ay, 'y', yn, yw), yp)
    qss = st([w.s([ypr], 'ex', '( %s -> ( y e. %s -> y e. %s ) )' % (a, QS_, PR))], 'ssrdv', '%s C_ %s' % (QS_, PR))
    # (B), (C)
    fzf = st([], 'fzfid', '%s e. Fin' % FZ)
    prf = st([fzf, a1(w, a, w.s([], 'inss1', '%s C_ %s' % (PR, FZ)), '%s C_ %s' % (PR, FZ))], 'ssfid', '%s e. Fin' % PR)
    sf = st([prf, a1(w, a, w.s([], 'difss', '%s C_ %s' % (S, PR)), '%s C_ %s' % (S, PR))], 'ssfid', '%s e. Fin' % S)
    sp = a1(w, a, w.s([w.s([], 'difss', '%s C_ %s' % (S, PR)), w.s([], 'inss2', '%s C_ Prime' % PR)], 'sstri', '%s C_ Prime' % S), '%s C_ Prime' % S)
    # (D) RSet C_ SM
    ck = '( %s /\\ k e. %s )' % (a, RS)
    sk = mkst(w, ck)
    el = sk([lift(w, nn, ck), lift(w, rr, ck), w.inst('z5elrset')], 'syl2anc', '( k e. %s <-> ( k e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 ) ) )' % RS)
    ke = sk([sk([], 'simpr', 'k e. %s' % RS), el], 'mpbid', '( k e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 ) )')
    kfz = sk([ke], 'simpld', 'k e. %s' % FZ)
    kg = sk([sk([ke], 'simprd', '( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 )')], 'simprd', '( k gcd N ) = 1')
    kn = sy(w, ck, kfz, 'elfznn', 'k e. NN')
    kw = sy(w, ck, kfz, 'elfzle2', 'k <_ %s' % W_)
    PFK = '{ r e. Prime | r || k }'
    cy = '( %s /\\ y e. %s )' % (ck, PFK)
    sc = mkst(w, cy)
    lc = lambda x: lift(w, x, cy)
    ye = sc([sc([], 'simpr', 'y e. %s' % PFK), a1(w, cy, w.s([w.s([], 'breq1', '( r = y -> ( r || k <-> y || k ) )')], 'elrab', '( y e. %s <-> ( y e. Prime /\\ y || k ) )' % PFK),
                                                   '( y e. %s <-> ( y e. Prime /\\ y || k ) )' % PFK)], 'mpbid', '( y e. Prime /\\ y || k )')
    yp2 = sc([ye], 'simpld', 'y e. Prime'); yk = sc([ye], 'simprd', 'y || k')
    yn2 = sy(w, cy, yp2, 'prmnn', 'y e. NN')
    yle = sc([yk, sc([sc([yn2], 'nnzd', 'y e. ZZ'), lc(kn), w.inst('dvdsle')], 'syl2anc', '( y || k -> y <_ k )')], 'mpd', 'y <_ k')
    yw2 = sc([sc([yn2], 'nnred', 'y e. RR'), sc([lc(kn)], 'nnred', 'k e. RR'), sc([lift(w, wz, cy)], 'zred', '%s e. RR' % W_), yle, lc(kw)], 'letrd', 'y <_ %s' % W_)
    ypr2 = inpr(cy, 'y', infz(cy, 'y', yn2, yw2), yp2)
    cq = '( %s /\\ y e. %s )' % (cy, QS_)
    sq = mkst(w, cq)
    yN = sq([sq([sq([sq([], 'simpr', 'y e. %s' % QS_), a1(w, cq, elqs(w, 'y'), '( y e. %s <-> ( y e. Prime /\\ ( y || N /\\ y <_ R ) ) )' % QS_)], 'mpbid',
                    '( y e. Prime /\\ ( y || N /\\ y <_ R ) )')], 'simprd', '( y || N /\\ y <_ R )')], 'simpld', 'y || N')
    sub_ = w.s([w.s([w.s([], 'breq1', '( p = y -> ( p || k <-> y || k ) )'), w.s([], 'breq1', '( p = y -> ( p || N <-> y || N ) )')], 'anbi12d',
                    '( p = y -> ( ( p || k /\\ p || N ) <-> ( y || k /\\ y || N ) ) )')], 'rspcev', '( ( y e. Prime /\\ ( y || k /\\ y || N ) ) -> E. p e. Prime ( p || k /\\ p || N ) )')
    rx = sq([sq([lift(w, yp2, cq), sq([lift(w, yk, cq), yN], 'jca', '( y || k /\\ y || N )')], 'jca', '( y e. Prime /\\ ( y || k /\\ y || N ) )'), sub_], 'syl',
            'E. p e. Prime ( p || k /\\ p || N )')
    ne = sq([rx, sq([lift(w, kn, cq), lift(w, nn, cq)], 'prmdvdsncoprmbd', '( E. p e. Prime ( p || k /\\ p || N ) <-> ( k gcd N ) =/= 1 )')], 'mpbid', '( k gcd N ) =/= 1')
    nq = w.s([lift(w, kg, cq), sq([ne], 'neneqd', '-. ( k gcd N ) = 1')], 'pm2.65da', '( %s -> -. y e. %s )' % (cy, QS_))
    ys = sc([sc([ypr2, nq], 'jca', '( y e. %s /\\ -. y e. %s )' % (PR, QS_)), a1(w, cy, w.s([], 'eldif', '( y e. %s <-> ( y e. %s /\\ -. y e. %s ) )' % (S, PR, QS_)),
                                                                                  '( y e. %s <-> ( y e. %s /\\ -. y e. %s ) )' % (S, PR, QS_))], 'mpbird', 'y e. %s' % S)
    pfs = sk([w.s([ys], 'ex', '( %s -> ( y e. %s -> y e. %s ) )' % (ck, PFK, S))], 'ssrdv', '%s C_ %s' % (PFK, S))
    vk = w.s([w.s([w.s([w.s([], 'breq2', '( v = k -> ( r || v <-> r || k ) )')], 'rabbidv', '( v = k -> { r e. Prime | r || v } = %s )' % PFK)],
                  'sseq1d', '( v = k -> ( { r e. Prime | r || v } C_ %s <-> %s C_ %s ) )' % (S, PFK, S))], 'elrab',
             '( k e. %s <-> ( k e. %s /\\ %s C_ %s ) )' % (SM, FZ, PFK, S))
    ksm = sk([kfz, pfs, a1(w, ck, vk, '( k e. %s <-> ( k e. %s /\\ %s C_ %s ) )' % (SM, FZ, PFK, S))], 'mpbir2and', 'k e. %s' % SM)
    rss = st([w.s([ksm], 'ex', '( %s -> ( k e. %s -> k e. %s ) )' % (a, RS, SM))], 'ssrdv', '%s C_ %s' % (RS, SM))
    # (E) sum over RSet <_ smooth sum
    smf = st([fzf, a1(w, a, w.s([], 'ssrab2', '%s C_ %s' % (SM, FZ)), '%s C_ %s' % (SM, FZ))], 'ssfid', '%s e. Fin' % SM)
    aj = '( %s /\\ j e. %s )' % (a, SM)
    sj = mkst(w, aj)
    jn = sy(w, aj, sj([sj([], 'simpr', 'j e. %s' % SM), w.inst('elrabi')], 'syl', 'j e. %s' % FZ), 'elfznn', 'j e. NN')
    jr = sj([jn], 'nnrecred', '( 1 / j ) e. RR'); j0 = sj([sj([jn], 'nnrpd', 'j e. RR+')], 'rpreccld' , '( 1 / j ) e. RR+')
    le1 = st([smf, jr, sj([j0], 'rpge0d', '0 <_ ( 1 / j )'), rss], 'fsumless', 'sum_ j e. %s ( 1 / j ) <_ sum_ j e. %s ( 1 / j )' % (RS, SM))
    cb = a1(w, a, w.s([w.s([], 'oveq2', '( r = j -> ( 1 / r ) = ( 1 / j ) )')], 'cbvsumv', '%s = sum_ j e. %s ( 1 / j )' % (P1('N', 'R'), RS)),
            '%s = sum_ j e. %s ( 1 / j )' % (P1('N', 'R'), RS))
    # (F) smsum
    INV = '( 1 / ( 1 - ( 1 / p ) ) )'
    PS = 'prod_ p e. %s %s' % (S, INV)
    le2 = st([sf, sp, wn, w.inst('smsum')], 'syl3anc', 'sum_ j e. %s ( 1 / j ) <_ %s' % (SM, PS))
    # (G) the Euler product splits
    ap_ = '( %s /\\ p e. %s )' % (a, PR)
    pp = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (ap_, PR)), w.inst('elinel2')], 'syl', '( %s -> p e. Prime )' % ap_)
    fp = primefac(w, ap_, pp)
    s_p = mkst(w, ap_)
    ic = s_p([fp['fc'], s_p([fp['gt0']], 'gt0ne0d', '( 1 - ( 1 / p ) ) =/= 0')], 'reccld', '%s e. CC' % INV)
    un = st([qss, a1(w, a, w.s([], 'undif', '( %s C_ %s <-> ( %s u. %s ) = %s )' % (QS_, PR, QS_, S, PR)),
                                                                                                     '( %s C_ %s <-> ( %s u. %s ) = %s )' % (QS_, PR, QS_, S, PR))], 'mpbid', '( %s u. %s ) = %s' % (QS_, S, PR))
    spl = st([a1(w, a, w.s([], 'disjdif', '( %s i^i %s ) = (/)' % (QS_, S)), '( %s i^i %s ) = (/)' % (QS_, S)), st([un], 'eqcomd', '%s = ( %s u. %s )' % (PR, QS_, S)), prf, ic],
             'fprodsplit', '%s = ( prod_ p e. %s %s x. %s )' % (MERT(), QS_, INV, PS))
    # (H) Q_R times the p || N half is 1
    aq = '( %s /\\ p e. %s )' % (a, QS_)
    s_q = mkst(w, aq)
    pq = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (aq, QS_)), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % aq)
    fq = primefac(w, aq, pq)
    fqn = s_q([fq['gt0']], 'gt0ne0d', '( 1 - ( 1 / p ) ) =/= 0')
    iq = s_q([fq['fc'], fqn], 'reccld', '%s e. CC' % INV)
    qfin = st([prf, qss], 'ssfid', '%s e. Fin' % QS_)
    fm = st([qfin, fq['fc'], iq], 'fprodmul', 'prod_ p e. %s ( ( 1 - ( 1 / p ) ) x. %s ) = ( %s x. prod_ p e. %s %s )' % (QS_, INV, QP, QS_, INV))
    rid = s_q([fq['fc'], fqn], 'recidd', '( ( 1 - ( 1 / p ) ) x. %s ) = 1' % INV)
    p1 = st([rid], 'prodeq2dv', 'prod_ p e. %s ( ( 1 - ( 1 / p ) ) x. %s ) = prod_ p e. %s 1' % (QS_, INV, QS_))
    pone = st([st([qfin], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (QS_, QS_)), w.inst('prod1')], 'syl', 'prod_ p e. %s 1 = 1' % QS_)
    one = st([st([fm], 'eqcomd', '( %s x. prod_ p e. %s %s ) = prod_ p e. %s ( ( 1 - ( 1 / p ) ) x. %s )' % (QP, QS_, INV, QS_, INV)), st([p1, pone], 'eqtrd',
              'prod_ p e. %s ( ( 1 - ( 1 / p ) ) x. %s ) = 1' % (QS_, INV))], 'eqtrd', '( %s x. prod_ p e. %s %s ) = 1' % (QP, QS_, INV))
    # (I) Q_R x. MERT = prod over S
    PQI = 'prod_ p e. %s %s' % (QS_, INV)
    qpc = st([qfin, fq['fc']], 'fprodcl', '%s e. CC' % QP)
    pqc = st([qfin, iq], 'fprodcl', '%s e. CC' % PQI)
    aS = '( %s /\\ p e. %s )' % (a, S)
    pS = w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (aS, S)), w.inst('eldifi')], 'syl', '( %s -> p e. %s )' % (aS, PR)), w.inst('elinel2')], 'syl', '( %s -> p e. Prime )' % aS)
    fS = primefac(w, aS, pS)
    s_S = mkst(w, aS)
    iS = s_S([fS['fc'], s_S([fS['gt0']], 'gt0ne0d', '( 1 - ( 1 / p ) ) =/= 0')], 'reccld', '%s e. CC' % INV)
    psc = st([sf, iS], 'fprodcl', '%s e. CC' % PS)
    m1 = st([spl], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (QP, MERT(), QP, PQI, PS))
    m2 = st([qpc, pqc, psc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (QP, PQI, PS, QP, PQI, PS))
    m3 = st([st([one], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 1 x. %s )' % (QP, PQI, PS, PS)), st([psc], 'mullidd', '( 1 x. %s ) = %s' % (PS, PS))], 'eqtrd',
            '( ( %s x. %s ) x. %s ) = %s' % (QP, PQI, PS, PS))
    meq = st([m1, st([m2, m3], 'eqtr3d', '( %s x. ( %s x. %s ) ) = %s' % (QP, PQI, PS, PS))], 'eqtrd', '( %s x. %s ) = %s' % (QP, MERT(), PS))
    # chain
    rsf = st([nn, rr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RS, RS))
    aj2 = '( %s /\\ j e. %s )' % (a, RS)
    sj2 = mkst(w, aj2)
    jn2 = sy(w, aj2, sj2([w.s([st([rsf], 'simpld', '%s C_ %s' % (RS, FZ))], 'adantr', '( %s -> %s C_ %s )' % (aj2, RS, FZ)), sj2([], 'simpr', 'j e. %s' % RS)], 'sseldd',
                         'j e. %s' % FZ), 'elfznn', 'j e. NN')
    s1r = st([st([rsf], 'simprd', '%s e. Fin' % RS), sj2([jn2], 'nnrecred', '( 1 / j ) e. RR')], 'fsumrecl', 'sum_ j e. %s ( 1 / j ) e. RR' % RS)
    s2r = st([smf, jr], 'fsumrecl', 'sum_ j e. %s ( 1 / j ) e. RR' % SM)
    psr = st([sf, s_S([fS['fr'], s_S([fS['gt0']], 'gt0ne0d', '( 1 - ( 1 / p ) ) =/= 0')], 'rereccld', '%s e. RR' % INV)], 'fprodrecl', '%s e. RR' % PS)
    ch = st([s1r, s2r, psr, le1, le2], 'letrd', 'sum_ j e. %s ( 1 / j ) <_ %s' % (RS, PS))
    w.qed([cb, ch, meq], '3brtr4d', STATEMENTS['z5dp1mert'])
    return w


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        if os.environ.get('Z5D_WRITE_ONLY'):
            w.write()
        else:
            run(w)
