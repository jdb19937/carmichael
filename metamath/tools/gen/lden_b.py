"""Sortie LDEN, part b: class I (Lemma 3.4, LV1 on one Taylor component):
ldencj ldencjs ldenrp ldenblk ldenv8 ldenlv ldenc1b ldenc1.

    MM_DB=sorties/lden.mm MM_ENGINE=mmatch python3 tools/gen/lden_b.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ldenlib import *
import ldenlib as LL
from ld1lib import BVA, EXY, LOGR, DV
from mvlib import DS as MVDS, SA2 as MVSA2
import lin as _lin
_lin.MAXPOW = 12
_lin.MAXDEG = 12

only = sys.argv[1:]
S = STATEMENTS
NBJ = NB('J')
NB2 = '( ( 2 ^ ( J + 1 ) ) x. D )'
COND = lambda n: '( %s < %s /\\ %s <_ %s /\\ %s <_ %s )' % (NBJ, n, n, NB2, n, NMAX)
BODY = lambda n: '( ( ( %s x. %s ) x. ( %s ^ I ) ) x. ( %s ^c -u S ) )' % (BVA(n), EXY(n), LOGR(n, NBJ), n)
assert COEFF('J', 'I', 'N', 'S') == 'if ( %s , %s , 0 )' % (COND('N'), BODY('N'))
NBS = '( %s ^c -u S )' % NBJ
PE = '( D ^c %s )' % EXPS


def num_(w, A, n, dom='RR'):
    return numst8(w, A, n, dom)


def tau_facts(w, A, c, n, nst):
    """TAU(n) e. NN0 (and RR, ge0 as leaves) for n e. NN under A"""
    dfi = w.s([nst, w.inst('dvdsfi')], 'syl', '( %s -> %s e. Fin )' % (A, DV(n)))
    tn = w.s([dfi, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A, TAU(n)))
    c.leaf(TAU(n), 'NN0', tn)
    return tn


def nb2_eq(w, A, c, jn):
    """( A -> ( ( 2 ^ ( J + 1 ) ) x. D ) = ( 2 x. ( ( 2 ^ J ) x. D ) ) ) by expp1 (c knows D, 2 ^ J atomic)"""
    e1 = w.s([num_(w, A, '2', 'CC'), jn, w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( J + 1 ) ) = ( ( 2 ^ J ) x. 2 ) )' % A)
    e2 = dst(w, A, [e1], 'oveq1d', '%s = ( ( ( 2 ^ J ) x. 2 ) x. D )' % NB2)
    c.atom('( 2 ^ J )'); c.leaf('( 2 ^ J )', 'RR', c.mem('( 2 ^ J )', 'RR'))
    return eqt(w, A, e2, ringeq(w, A, '( ( ( 2 ^ J ) x. 2 ) x. D )', '( 2 x. %s )' % NBJ, c))


def gen_cj():
    w = W('ldencj', 'Lean ` norm_coeffJK_le ` : the coefficient ` coeffJK D sigma j k n ` is bounded by ` tau ( n ) ( 2 ^ j D ) ^ - sigma ` ( ~ ld1bvatau , ~ log2le1 , ~ exple1 ).')
    A = ante('ldencj'); P = parts(w, A)
    dr, d0, sr, s0, jn, inn, nn = P['D e. RR'], P['0 < D'], P['S e. RR'], P['0 <_ S'], P['J e. NN0'], P['I e. NN0'], P['N e. NN']
    rp = dst(w, A, [dr, d0], 'elrpd', 'D e. RR+')
    c = Closure(w, A, {'D': [('RR+', rp)], 'S': [('RR', sr), ('ge0', s0)], 'J': ('NN0', jn), 'I': ('NN0', inn), 'N': ('NN', nn)})
    tn = tau_facts(w, A, c, 'N', nn)
    nbr = c.mem(NBJ, 'RR+'); nbs = c.mem(NBS, 'RR+')
    RHS = '( %s x. %s )' % (TAU('N'), NBS)
    rhs0 = c.ge0(RHS)
    CO = COND('N'); CF = COEFF('J', 'I', 'N', 'S')
    # the true branch
    A1 = '( %s /\\ %s )' % (A, CO)
    c1 = Closure(w, A1, parent=c)
    for e_, k_ in ((NBJ, 'RR+'), (NBS, 'RR+'), ('D', 'RR+'), ('N', 'NN'), ('S', 'RR'), ('S', 'ge0'), ('J', 'NN0'), ('I', 'NN0'), (TAU('N'), 'NN0')):
        c1.leaf(e_, k_, lift(w, c.mem(e_, k_), A1))
    co = w.s([], 'simpr', '( %s -> %s )' % (A1, CO))
    lt = dst(w, A1, [co], 'simp1d', '%s < N' % NBJ); le2 = dst(w, A1, [co], 'simp2d', 'N <_ %s' % NB2)
    ift = dst(w, A1, [co], 'iftrued', '%s = %s' % (CF, BODY('N')))
    # abs of the body
    bva = dst(w, A1, [lift(w, J(w, A, J(w, A, dr, d0), J(w, A, c.mem('( 2 x. D )', 'RR'), linarith(w, A, [d0], 'D < ( 2 x. D )', closure=c))), A1), c1.mem('N', 'NN')], 'jca',
              '( %s /\\ N e. NN )' % tsub(LL.ZR.__dict__.get('HAB0', '( ( D e. RR /\\ 0 < D ) /\\ ( ( 2 x. D ) e. RR /\\ D < ( 2 x. D ) ) )'), {'A': 'D', 'B': '( 2 x. D )'}))
    bvab = dst(w, A1, [bva, w.inst('ld1bvatau')], 'syl', '( abs ` %s ) <_ %s' % (BVA('N'), TAU('N')))
    rp3 = J(w, A1, c1.mem('D', 'RR+'), c1.mem('( 2 x. D )', 'RR+'), lift(w, linarith(w, A, [d0], 'D < ( 2 x. D )', closure=c), A1))
    c1.leaf(BVA('N'), 'RR', ap(w, A1, 'bvare', [J(w, A1, rp3, c1.mem('N', 'NN'))], '%s e. RR' % BVA('N')))
    # EXY <_ 1
    EX_ = EXY('N'); ARG = '( -u N / %s )' % YP
    c1.leaf(YP, 'RR+', c1.mem(YP, 'RR+'))
    nyp = dst(w, A1, [c1.mem('N', 'RR'), c1.mem(YP, 'RR+')], 'rerpdivcld', '( N / %s ) e. RR' % YP)
    nyp0 = dst(w, A1, [c1.mem('N', 'RR'), c1.mem(YP, 'RR+'), linarith(w, A1, [c1.mem('N', 'ge0')], '0 <_ N', closure=c1)], 'divge0d', '0 <_ ( N / %s )' % YP)
    neg = dst(w, A1, [c1.mem('N', 'CC'), c1.mem(YP, 'CC'), c1.ne0(YP)], 'divnegd', '-u ( N / %s ) = ( -u N / %s )' % (YP, YP))
    argr = dst(w, A1, [c1.mem('-u N', 'RR'), c1.mem(YP, 'RR+')], 'rerpdivcld', '%s e. RR' % ARG)
    arg_le = dst(w, A1, [neg, linarith(w, A1, [nyp0], '-u ( N / %s ) <_ 0' % YP, closure=Closure(w, A1, {'( N / %s )' % YP: nyp}))], 'eqbrtrrd', '%s <_ 0' % ARG)
    efl = dst(w, A1, [arg_le, dst(w, A1, [argr, w.s([], '0red', '( %s -> 0 e. RR )' % A1), w.inst('efle')], 'syl2anc', '( %s <_ 0 <-> ( exp ` %s ) <_ ( exp ` 0 ) )' % (ARG, ARG))], 'mpbid', '( exp ` %s ) <_ ( exp ` 0 )' % ARG)
    ex1 = dst(w, A1, [efl, a1(w, A1, 'ef0', '( exp ` 0 ) = 1')], 'breqtrd', '%s <_ 1' % EX_)
    c1.leaf(EX_, 'RR+', c1.mem(EX_, 'RR+'))
    # abs ( LOGR ^ I ) <_ 1
    Qr = '( N / %s )' % NBJ
    qrp = c1.mem(Qr, 'RR+')
    # 1 < N / NB from NB < N  (ltdivmul-free: ldivmul? use ltdiv1: A < B <-> A / C < B / C)
    dv1 = dst(w, A1, [c1.mem(NBJ, 'RR'), c1.mem('N', 'RR'), c1.mem(NBJ, 'RR+'), lt], 'ltdiv1dd', '( %s / %s ) < ( N / %s )' % (NBJ, NBJ, NBJ))
    dvid = dst(w, A1, [c1.mem(NBJ, 'CC'), c1.ne0(NBJ)], 'dividd', '( %s / %s ) = 1' % (NBJ, NBJ))
    q_gt1 = dst(w, A1, [dvid, dv1], 'eqbrtrrd', '1 < %s' % Qr)
    # N / NB <_ 2 from N <_ 2 NB
    e2 = nb2_eq(w, A1, c1, c1.mem('J', 'NN0'))
    le2b = dst(w, A1, [le2, e2], 'breqtrd', 'N <_ ( 2 x. %s )' % NBJ)
    q_le2 = dst(w, A1, [le2b, dst(w, A1, [c1.mem('N', 'RR'), num_(w, A1, '2'), c1.mem(NBJ, 'RR+')], 'ledivmul2d', '( ( N / %s ) <_ 2 <-> N <_ ( 2 x. %s ) )' % (NBJ, NBJ))], 'mpbird', '%s <_ 2' % Qr)
    lq = dst(w, A1, [qrp], 'relogcld', '( log ` %s ) e. RR' % Qr)
    lq0 = dst(w, A1, [c1.mem(Qr, 'RR'), ltle(w, A1, c1, q_gt1)], 'logge0d', '0 <_ ( log ` %s )' % Qr)
    lq2 = dst(w, A1, [q_le2, dst(w, A1, [qrp, num_(w, A1, '2', 'RR+')], 'logled', '( %s <_ 2 <-> ( log ` %s ) <_ ( log ` 2 ) )' % (Qr, Qr))], 'mpbid', '( log ` %s ) <_ ( log ` 2 )' % Qr)
    l2 = a1(w, A1, 'log2le1', '( log ` 2 ) < 1')
    lq1 = linarith(w, A1, [lq2, l2], '( log ` %s ) <_ 1' % Qr, closure=Closure(w, A1, {'( log ` %s )' % Qr: lq, '( log ` 2 )': a1(w, A1, 'relogcli', '') if False else dst(w, A1, [num_(w, A1, '2', 'RR+')], 'relogcld', '( log ` 2 ) e. RR')}))
    LR = LOGR('N', NBJ)
    assert LR == '-u ( log ` %s )' % Qr
    abl = dst(w, A1, [dst(w, A1, [lq], 'recnd', '( log ` %s ) e. CC' % Qr)], 'absnegd', '( abs ` %s ) = ( abs ` ( log ` %s ) )' % (LR, Qr))
    abl2 = dst(w, A1, [abl, dst(w, A1, [lq, lq0], 'absidd', '( abs ` ( log ` %s ) ) = ( log ` %s )' % (Qr, Qr))], 'eqtrd', '( abs ` %s ) = ( log ` %s )' % (LR, Qr))
    lrc = dst(w, A1, [dst(w, A1, [lq], 'recnd', '( log ` %s ) e. CC' % Qr)], 'negcld', '%s e. CC' % LR)
    abp = dst(w, A1, [lrc, c1.mem('I', 'NN0')], 'absexpd', '( abs ` ( %s ^ I ) ) = ( ( abs ` %s ) ^ I )' % (LR, LR))
    ablr = dst(w, A1, [lrc], 'abscld', '( abs ` %s ) e. RR' % LR); abl0 = dst(w, A1, [lrc], 'absge0d', '0 <_ ( abs ` %s )' % LR)
    ab1 = dst(w, A1, [abl2, lq1], 'eqbrtrd', '( abs ` %s ) <_ 1' % LR)
    p1 = ap(w, A1, 'exple1', [J(w, A1, J(w, A1, ablr, abl0, ab1), c1.mem('I', 'NN0'))], '( ( abs ` %s ) ^ I ) <_ 1' % LR)
    p1b = dst(w, A1, [abp, p1], 'eqbrtrd', '( abs ` ( %s ^ I ) ) <_ 1' % LR)
    # N ^c -u S <_ NB ^c -u S
    NSS = '( N ^c -u S )'
    nss = c1.mem(NSS, 'RR+')
    ns = dst(w, A1, [c1.mem('N', 'CC'), c1.ne0('N'), c1.mem('S', 'CC')], 'cxpnegd', '%s = ( 1 / ( N ^c S ) )' % NSS)
    nbs_ = dst(w, A1, [c1.mem(NBJ, 'CC'), c1.ne0(NBJ), c1.mem('S', 'CC')], 'cxpnegd', '%s = ( 1 / ( %s ^c S ) )' % (NBS, NBJ))
    mono = ap(w, A1, 'cxple2a', [J(w, A1, c1.mem(NBJ, 'RR'), c1.mem('N', 'RR'), c1.mem('S', 'RR')), J(w, A1, c1.ge0(NBJ), c1.mem('S', 'ge0')), ltle(w, A1, c1, lt)], '( %s ^c S ) <_ ( N ^c S )' % NBJ)
    rec = dst(w, A1, [mono, ap(w, A1, 'lerec', [J(w, A1, c1.mem('( %s ^c S )' % NBJ, 'RR'), c1.gt0('( %s ^c S )' % NBJ)), J(w, A1, c1.mem('( N ^c S )', 'RR'), c1.gt0('( N ^c S )'))],
                                      '( ( %s ^c S ) <_ ( N ^c S ) <-> ( 1 / ( N ^c S ) ) <_ ( 1 / ( %s ^c S ) ) )' % (NBJ, NBJ))], 'mpbid', '( 1 / ( N ^c S ) ) <_ ( 1 / ( %s ^c S ) )' % NBJ)
    nle = dst(w, A1, [ns, dst(w, A1, [rec, eqc(w, A1, nbs_)], 'breqtrd', '( 1 / ( N ^c S ) ) <_ %s' % NBS)], 'eqbrtrd', '%s <_ %s' % (NSS, NBS))
    # assemble: abs BODY = ( ( abs BVA x. abs EX ) x. abs ( LR ^ I ) ) x. abs NSS
    F1, F2, F3, F4 = BVA('N'), EX_, '( %s ^ I )' % LR, NSS
    c1.leaf(F3, 'RR', c1.mem(F3, 'RR'))
    a12 = dst(w, A1, [c1.mem(F1, 'CC'), c1.mem(F2, 'CC')], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (F1, F2, F1, F2))
    a123 = dst(w, A1, [c1.mem('( %s x. %s )' % (F1, F2), 'CC'), c1.mem(F3, 'CC')], 'absmuld', '( abs ` ( ( %s x. %s ) x. %s ) ) = ( ( abs ` ( %s x. %s ) ) x. ( abs ` %s ) )' % (F1, F2, F3, F1, F2, F3))
    a1234 = dst(w, A1, [c1.mem('( ( %s x. %s ) x. %s )' % (F1, F2, F3), 'CC'), c1.mem(F4, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` ( ( %s x. %s ) x. %s ) ) x. ( abs ` %s ) )' % (BODY('N'), F1, F2, F3, F4))
    ex_id = dst(w, A1, [c1.mem(F2, 'RR'), c1.ge0(F2)], 'absidd', '( abs ` %s ) = %s' % (F2, F2))
    ns_id = dst(w, A1, [c1.mem(F4, 'RR'), c1.ge0(F4)], 'absidd', '( abs ` %s ) = %s' % (F4, F4))
    ab1_ = dst(w, A1, [c1.mem(F1, 'CC')], 'abscld', '( abs ` %s ) e. RR' % F1); ab1_0 = dst(w, A1, [c1.mem(F1, 'CC')], 'absge0d', '0 <_ ( abs ` %s )' % F1)
    ab3_ = dst(w, A1, [c1.mem(F3, 'CC')], 'abscld', '( abs ` %s ) e. RR' % F3); ab3_0 = dst(w, A1, [c1.mem(F3, 'CC')], 'absge0d', '0 <_ ( abs ` %s )' % F3)
    ex_le = dst(w, A1, [ex_id, ex1], 'eqbrtrd', '( abs ` %s ) <_ 1' % F2)
    ns_le = dst(w, A1, [ns_id, nle], 'eqbrtrd', '( abs ` %s ) <_ %s' % (F4, NBS))
    one = num_(w, A1, '1')
    m1 = dst(w, A1, [ab1_, c1.mem(TAU('N'), 'RR'), dst(w, A1, [c1.mem(F2, 'CC')], 'abscld', '( abs ` %s ) e. RR' % F2), one, ab1_0, dst(w, A1, [c1.mem(F2, 'CC')], 'absge0d', '0 <_ ( abs ` %s )' % F2), bvab, ex_le],
             'lemul12ad', '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( %s x. 1 )' % (F1, F2, TAU('N')))
    T1 = '( %s x. 1 )' % TAU('N')
    A12 = '( abs ` ( %s x. %s ) )' % (F1, F2)
    m1b = dst(w, A1, [a12, m1], 'eqbrtrd', '%s <_ %s' % (A12, T1))
    m2 = dst(w, A1, [dst(w, A1, [c1.mem('( %s x. %s )' % (F1, F2), 'CC')], 'abscld', '%s e. RR' % A12), c1.mem(T1, 'RR'), ab3_, one,
                     dst(w, A1, [c1.mem('( %s x. %s )' % (F1, F2), 'CC')], 'absge0d', '0 <_ %s' % A12), ab3_0, m1b, p1b],
             'lemul12ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. 1 )' % (A12, F3, T1))
    T2 = '( %s x. 1 )' % T1
    m2b = dst(w, A1, [a123, m2], 'eqbrtrd', '( abs ` ( ( %s x. %s ) x. %s ) ) <_ %s' % (F1, F2, F3, T2))
    m3 = dst(w, A1, [c1.mem('( abs ` ( ( %s x. %s ) x. %s ) )' % (F1, F2, F3), 'RR'), c1.mem(T2, 'RR'), dst(w, A1, [c1.mem(F4, 'CC')], 'abscld', '( abs ` %s ) e. RR' % F4), c1.mem(NBS, 'RR'),
                      dst(w, A1, [c1.mem('( ( %s x. %s ) x. %s )' % (F1, F2, F3), 'CC')], 'absge0d', '0 <_ ( abs ` ( ( %s x. %s ) x. %s ) )' % (F1, F2, F3)), dst(w, A1, [c1.mem(F4, 'CC')], 'absge0d', '0 <_ ( abs ` %s )' % F4), m2b, ns_le],
             'lemul12ad', '( ( abs ` ( ( %s x. %s ) x. %s ) ) x. ( abs ` %s ) ) <_ ( %s x. %s )' % (F1, F2, F3, F4, T2, NBS))
    m3b = dst(w, A1, [a1234, m3], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. %s )' % (BODY('N'), T2, NBS))
    e_ = ringeq(w, A1, '( %s x. %s )' % (T2, NBS), RHS, c1)
    tb = dst(w, A1, [dst(w, A1, [ift], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (CF, BODY('N'))), dst(w, A1, [m3b, e_], 'breqtrd', '( abs ` %s ) <_ %s' % (BODY('N'), RHS))], 'eqbrtrd', '( abs ` %s ) <_ %s' % (CF, RHS))
    # the false branch
    A2 = '( %s /\\ -. %s )' % (A, CO)
    nco = w.s([], 'simpr', '( %s -> -. %s )' % (A2, CO))
    iff = dst(w, A2, [nco], 'iffalsed', '%s = 0' % CF)
    ab0 = dst(w, A2, [dst(w, A2, [iff], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % CF), a1(w, A2, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % CF)
    fb = dst(w, A2, [ab0, lift(w, rhs0, A2)], 'eqbrtrd', '( abs ` %s ) <_ %s' % (CF, RHS))
    fin_ = dst(w, A, [tb, fb], 'pm2.61dan', concl('ldencj'))
    return fin(w, fin_)


def gen_cjs():
    w = W('ldencjs', 'Lean ` sum_sq_coeffJK_le ` : the coefficient mass ` sum_ n <_ M abs coeffJK ^ 2 <_ ( ( 2 ^ j D ) ^ - sigma ) ^ 2 M ( 1 + log M ) ^ 3 ` ( ~ ldencj , ~ ld1tau2 ).')
    A = ante('ldencjs'); P = parts(w, A)
    dr, d0, sr, s0, jn, inn, mn = P['D e. RR'], P['0 < D'], P['S e. RR'], P['0 <_ S'], P['J e. NN0'], P['I e. NN0'], P['M e. NN']
    rp = dst(w, A, [dr, d0], 'elrpd', 'D e. RR+')
    c = Closure(w, A, {'D': [('RR+', rp)], 'S': [('RR', sr), ('ge0', s0)], 'J': ('NN0', jn), 'I': ('NN0', inn), 'M': ('NN', mn)})
    c.leaf(NBS, 'RR+', c.mem(NBS, 'RR+'))
    FZ = '( 1 ... M )'
    An = '( %s /\\ n e. %s )' % (A, FZ)
    cn = c.child('n', FZ)
    nN = cn.mem('n', 'NN')
    tn = tau_facts(w, An, cn, 'n', nN)
    CFn = COEFF('J', 'I', 'n', 'S')
    hy = J(w, An, lift(w, J(w, A, J(w, A, dr, d0), J(w, A, sr, s0)), An), J(w, An, lift(w, J(w, A, jn, inn), An), nN))
    cj = ap(w, An, 'ldencj', [hy], tsub(concl('ldencj'), {'N': 'n'}))
    rp3 = J(w, A, c.mem('D', 'RR+'), c.mem('( 2 x. D )', 'RR+'), linarith(w, A, [d0], 'D < ( 2 x. D )', closure=c))
    cn.leaf(BVA('n'), 'RR', ap(w, An, 'bvare', [J(w, An, lift(w, rp3, An), nN)], '%s e. RR' % BVA('n')))
    cn.leaf(CFn, 'CC', cn.mem(CFn, 'CC'))
    AB = '( abs ` %s )' % CFn
    abr = dst(w, An, [cn.mem(CFn, 'CC')], 'abscld', '%s e. RR' % AB); ab0 = dst(w, An, [cn.mem(CFn, 'CC')], 'absge0d', '0 <_ %s' % AB)
    RH = '( %s x. %s )' % (TAU('n'), NBS)
    sq = ap(w, An, 'le2sq2', [J(w, An, abr, ab0), J(w, An, cn.mem(RH, 'RR'), cj)], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (AB, RH))
    TM = '( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (NBS, TAU('n'))
    e1 = ringeqp(w, An, '( %s ^ 2 )' % RH, TM, cn)
    sq2 = dst(w, An, [sq, e1], 'breqtrd', '( %s ^ 2 ) <_ %s' % (AB, TM))
    fi = dst(w, A, [], 'fzfid', '%s e. Fin' % FZ)
    LHS = 'sum_ n e. %s ( %s ^ 2 )' % (FZ, AB)
    fl = dst(w, A, [fi, dst(w, An, [abr], 'resqcld', '( %s ^ 2 ) e. RR' % AB), cn.mem(TM, 'RR'), sq2], 'fsumle', '%s <_ sum_ n e. %s %s' % (LHS, FZ, TM))
    SQ2 = '( %s ^ 2 )' % NBS
    ST = 'sum_ n e. %s ( %s ^ 2 )' % (FZ, TAU('n'))
    fm = dst(w, A, [fi, c.mem(SQ2, 'CC'), cn.mem('( %s ^ 2 )' % TAU('n'), 'CC')], 'fsummulc2', '( %s x. %s ) = sum_ n e. %s %s' % (SQ2, ST, FZ, TM))
    # ld1tau2 at X := M
    mr = c.mem('M', 'RR'); m1 = dst(w, A, [mn], 'nnge1d', '1 <_ M')
    t2 = ap(w, A, 'ld1tau2', [J(w, A, mr, m1)], tsub(concl('ld1tau2'), {'X': 'M'}))
    fl_ = w.s([dst(w, A, [mn], 'nnzd', 'M e. ZZ'), w.inst('flid')], 'syl', '( %s -> ( |_ ` M ) = M )' % A)
    rng = dst(w, A, [dst(w, A, [fl_], 'oveq2d', '( 1 ... ( |_ ` M ) ) = %s' % FZ)], 'sumeq1d', 'sum_ n e. ( 1 ... ( |_ ` M ) ) ( %s ^ 2 ) = %s' % (TAU('n'), ST))
    t2b = dst(w, A, [eqc(w, A, rng), t2], 'eqbrtrd', '%s <_ ( M x. ( ( 1 + ( log ` M ) ) ^ 3 ) )' % ST)
    c.leaf(ST, 'RR', dst(w, A, [fi, cn.mem('( %s ^ 2 )' % TAU('n'), 'RR')], 'fsumrecl', '%s e. RR' % ST))
    m2 = lemul(w, A, c, t2b, SQ2, side=2)
    lhsr = dst(w, A, [fi, dst(w, An, [abr], 'resqcld', '( %s ^ 2 ) e. RR' % AB)], 'fsumrecl', '%s e. RR' % LHS)
    st1 = dst(w, A, [fl, eqc(w, A, fm)], 'breqtrd', '%s <_ ( %s x. %s )' % (LHS, SQ2, ST))
    fin_ = dst(w, A, [lhsr, c.mem('( %s x. %s )' % (SQ2, ST), 'RR'), c.mem('( %s x. ( M x. ( ( 1 + ( log ` M ) ) ^ 3 ) ) )' % SQ2, 'RR'), st1, m2], 'letrd', concl('ldencjs'))
    return fin(w, fin_)


def gen_rp():
    w = W('ldenrp', 'Lean ` rpow_neg_sq_mul_sq ` : ` ( x ^ - s ) ^ 2 x ^ 2 = x ^ ( 2 - 2 s ) ` ( ~ cxpmuld , ~ cxpaddd ).')
    A = ante('ldenrp'); P = parts(w, A)
    xp, sr = P['X e. RR+'], P['S e. RR']
    c = Closure(w, A, {'X': ('RR+', xp), 'S': ('RR', sr)})
    XS = '( X ^c -u S )'
    e1 = w.s([c.mem(XS, 'CC'), a1(w, A, '2nn0', '2 e. NN0'), w.inst('cxpexp')], 'syl2anc', '( %s -> ( %s ^c 2 ) = ( %s ^ 2 ) )' % (A, XS, XS))
    e2 = dst(w, A, [xp, c.mem('-u S', 'RR'), c.mem('2', 'CC')], 'cxpmuld', '( X ^c ( -u S x. 2 ) ) = ( %s ^c 2 )' % XS)
    e3 = w.s([c.mem('X', 'CC'), a1(w, A, '2nn0', '2 e. NN0'), w.inst('cxpexp')], 'syl2anc', '( %s -> ( X ^c 2 ) = ( X ^ 2 ) )' % A)
    e4 = dst(w, A, [c.mem('X', 'CC'), c.ne0('X'), c.mem('( -u S x. 2 )', 'CC'), c.mem('2', 'CC')], 'cxpaddd', '( X ^c ( ( -u S x. 2 ) + 2 ) ) = ( ( X ^c ( -u S x. 2 ) ) x. ( X ^c 2 ) )')
    pr = dst(w, A, [eqt(w, A, e2, e1), e3], 'oveq12d', '( ( X ^c ( -u S x. 2 ) ) x. ( X ^c 2 ) ) = ( ( %s ^ 2 ) x. ( X ^ 2 ) )' % XS)
    ex = dst(w, A, [ringeq(w, A, '( ( -u S x. 2 ) + 2 )', '( 2 - ( 2 x. S ) )', c)], 'oveq2d', '( X ^c ( ( -u S x. 2 ) + 2 ) ) = ( X ^c ( 2 - ( 2 x. S ) ) )')
    fin_ = eqt(w, A, eqc(w, A, eqt(w, A, e4, pr)), ex)
    return fin(w, fin_)


def gen_blk():
    w = W('ldenblk', 'Lean ` block_rpow_le ` : for a block below ` Nmax D <_ 9 log D Ypar D ` , ` ( 2 ^ j D ) ^ ( 2 - 2 sigma ) <_ 9 log D D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) ` ( ~ ld1nmax , ~ cxplea ).')
    A = ante('ldenblk'); P = parts(w, A)
    c, F = basecl(w, A, P)
    sr, s39, s1, jn, blk = P['S e. RR'], P['( ; 3 9 / ; 5 0 ) <_ S'], P['S <_ 1'], P['J e. NN0'], P['%s < %s' % (NBJ, NMAX)]
    c.leaf('S', 'RR', sr); c.leaf('J', 'NN0', jn)
    L = LOGD
    c.leaf(L, 'ge0', linarith(w, A, [F['dl']], '0 <_ %s' % L, closure=c))
    E = '( 2 - ( 2 x. S ) )'
    e0 = linarith(w, A, [s1], '0 <_ %s' % E, closure=c); e1 = linarith(w, A, [s39], '%s <_ 1' % E, closure=c)
    nm3 = dst(w, A, [F['nm']], 'simp3d', '%s <_ ( ( ( 8 x. %s ) x. %s ) + 1 )' % (NMAX, YP, L))
    yl = dst(w, A, [c.mem(YP, 'RR'), c.mem(L, 'RR'), num_(w, A, '4'), num_(w, A, '; 4 0'), linarith(w, A, [], '0 <_ 4', closure=c), linarith(w, A, [], '0 <_ ; 4 0', closure=c), F['y4'], F['dl']], 'lemul12ad', '( 4 x. ; 4 0 ) <_ ( %s x. %s )' % (YP, L))
    c.atom(YP); c.atom(L)
    NM9 = '( ( 9 x. %s ) x. %s )' % (L, YP)
    nm9 = nlinarith(w, A, [nm3, F['y4'], F['dl']], '%s <_ %s' % (NMAX, NM9), closure=c)
    nble = linarith(w, A, [blk, nm9], '%s <_ %s' % (NBJ, NM9), closure=c)
    c.leaf(NBJ, 'RR+', c.mem(NBJ, 'RR+'))
    m1 = ap(w, A, 'cxple2a', [J(w, A, c.mem(NBJ, 'RR'), c.mem(NM9, 'RR'), c.mem(E, 'RR')), J(w, A, c.ge0(NBJ), e0), nble], '( %s ^c %s ) <_ ( %s ^c %s )' % (NBJ, E, NM9, E))
    L9 = '( 9 x. %s )' % L
    m2 = dst(w, A, [c.mem(L9, 'RR'), c.ge0(L9), c.mem(YP, 'RR'), c.ge0(YP), c.mem(E, 'CC')], 'mulcxpd', '( %s ^c %s ) = ( ( %s ^c %s ) x. ( %s ^c %s ) )' % (NM9, E, L9, E, YP, E))
    l9ge1 = linarith(w, A, [F['dl']], '1 <_ %s' % L9, closure=c)
    m3 = ap(w, A, 'cxplea', [J(w, A, c.mem(L9, 'RR'), l9ge1), J(w, A, c.mem(E, 'RR'), num_(w, A, '1')), e1], '( %s ^c %s ) <_ ( %s ^c 1 )' % (L9, E, L9))
    m3b = dst(w, A, [m3, dst(w, A, [c.mem(L9, 'CC')], 'cxp1d', '( %s ^c 1 ) = %s' % (L9, L9))], 'breqtrd', '( %s ^c %s ) <_ %s' % (L9, E, L9))
    YE = '( %s ^c %s )' % (YP, E)
    c.leaf(YE, 'RR+', c.mem(YE, 'RR+'))
    m4 = dst(w, A, [c.mem('( %s ^c %s )' % (L9, E), 'RR'), c.mem(L9, 'RR'), c.mem(YE, 'RR'), c.ge0(YE), m3b], 'lemul1ad', '( ( %s ^c %s ) x. %s ) <_ ( %s x. %s )' % (L9, E, YE, L9, YE))
    # YP ^c E = D ^c EXPS
    y1 = dst(w, A, [F['rp'], c.mem('( ; ; 1 5 1 / ; ; 1 0 0 )', 'RR'), c.mem(E, 'CC')], 'cxpmuld', '( D ^c ( ( ; ; 1 5 1 / ; ; 1 0 0 ) x. %s ) ) = %s' % (E, YE))
    y2 = dst(w, A, [ringeq(w, A, '( ( ; ; 1 5 1 / ; ; 1 0 0 ) x. %s )' % E, EXPS, c)], 'oveq2d', '( D ^c ( ( ; ; 1 5 1 / ; ; 1 0 0 ) x. %s ) ) = ( D ^c %s )' % (E, EXPS))
    ye = eqt(w, A, eqc(w, A, y1), y2)
    m4b = dst(w, A, [m4, dst(w, A, [ye], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (L9, YE, L9, PE))], 'breqtrd', '( ( %s ^c %s ) x. %s ) <_ ( %s x. %s )' % (L9, E, YE, L9, PE))
    c.leaf(PE, 'RR+', c.mem(PE, 'RR+'))
    fin_ = dst(w, A, [c.mem('( %s ^c %s )' % (NBJ, E), 'RR'), c.mem('( %s ^c %s )' % (NM9, E), 'RR'), c.mem('( %s x. %s )' % (L9, PE), 'RR'), m1, dst(w, A, [m2, m4b], 'eqbrtrd', '( %s ^c %s ) <_ ( %s x. %s )' % (NM9, E, L9, PE))], 'letrd', concl('ldenblk'))
    return fin(w, fin_)


def gen_v8():
    w = W('ldenv8', 'Lean ` Vthr_pos ` and the threshold arithmetic of ` classI_card_le ` ( ` hVW ` , ` hW ` , ` hJ2 ` ): ` Vthr D = 1 / ( 8 J ( J + 1 ) ) ` is positive, its inverse ` 8 J ( J + 1 ) <_ 32 log ^ 2 D ` , and ` J , J + 1 <_ 2 log D ` ( ~ ld1jpar ).')
    A = ante('ldenv8'); P = parts(w, A)
    c, F = basecl(w, A, P)
    L = LOGD
    c.leaf(L, 'ge0', linarith(w, A, [F['dl']], '0 <_ %s' % L, closure=c))
    jp2 = dst(w, A, [F['jp']], 'simprd', '( %s <_ %s /\\ %s <_ ( %s + 1 ) /\\ %s <_ ( 2 x. %s ) )' % (L, JPAR, JPAR, L, JPAR, L))
    jl1 = dst(w, A, [jp2], 'simp2d', '%s <_ ( %s + 1 )' % (JPAR, L)); jl2 = dst(w, A, [jp2], 'simp3d', '%s <_ ( 2 x. %s )' % (JPAR, L))
    c.atom(JPAR); c.atom(L)
    jl3 = linarith(w, A, [jl1, F['dl']], '( %s + 1 ) <_ ( 2 x. %s )' % (JPAR, L), closure=c)
    c.have(W8, 'RR+', c.mem(W8, 'RR+'))
    v8p = c.mem(V8, 'RR+')
    vw = dst(w, A, [c.mem(W8, 'CC'), c.ne0(W8)], 'recid2d', '( %s x. %s ) = 1' % (V8, W8))
    L2 = '( 2 x. %s )' % L
    pr = dst(w, A, [c.mem(JPAR, 'RR'), c.mem(L2, 'RR'), c.mem('( %s + 1 )' % JPAR, 'RR'), c.mem(L2, 'RR'), c.ge0(JPAR), c.ge0('( %s + 1 )' % JPAR), jl2, jl3], 'lemul12ad',
             '( %s x. ( %s + 1 ) ) <_ ( %s x. %s )' % (JPAR, JPAR, L2, L2))
    pr8 = lemul(w, A, c, pr, '8', side=2)
    e1 = ringeq(w, A, W8, '( 8 x. ( %s x. ( %s + 1 ) ) )' % (JPAR, JPAR), c)
    e2 = ringeqp(w, A, '( 8 x. ( %s x. %s ) )' % (L2, L2), '( ; 3 2 x. ( %s ^ 2 ) )' % L, c)
    w8le = dst(w, A, [e1, dst(w, A, [pr8, e2], 'breqtrd', '( 8 x. ( %s x. ( %s + 1 ) ) ) <_ ( ; 3 2 x. ( %s ^ 2 ) )' % (JPAR, JPAR, L))], 'eqbrtrd', '%s <_ ( ; 3 2 x. ( %s ^ 2 ) )' % (W8, L))
    fin_ = J(w, A, J(w, A, v8p, vw), J(w, A, w8le, J(w, A, jl2, jl3)))
    return fin(w, fin_)


def famparts(w, A, P):
    """the family conjuncts of A (HFAMP, RNGA, SEPY, LVA) as steps"""
    F = {}
    F['fin'] = P['F e. Fin']; F['kal'] = P['A. a e. F ( K ` a ) e. %s' % DB()]; F['yal'] = P['A. a e. F ( Y ` a ) e. CC']
    F['rng'] = P[RNGA]; F['sep'] = P[SEPY]
    if LVA in P:
        F['lva'] = P[LVA]
    return F


def gen_lv():
    w = W('ldenlv', 'The LV1 instance of ` classI_card_le ` ( ` hLV ` ): ~ mvlvm at the block length ` N = ceil ( 2 ^ ( j + 1 ) D ) ` , the coefficients ` coeffJK ` , the frequencies ` Im rho_r ` and the threshold ` Vthr D ` ; the maps written as mappings (binder ` e ` ) and their values rewritten; the family quantifiers in the letters ` c g ` (the antecedent binds ` a b ` ).')
    A = ante('ldenlv'); P = parts(w, A)
    c, F = basecl(w, A, P)
    nn_, tr, t2, sr, s0, jn, inn = P['N e. NN'], P['T e. RR'], P['2 <_ T'], P['S e. RR'], P['0 <_ S'], P['J e. NN0'], P['I e. NN0']
    G = famparts(w, A, P)
    for e_, st_ in (('N', nn_), ('T', tr), ('S', sr), ('J', jn), ('I', inn)):
        c.leaf(e_, {'N': 'NN', 'T': 'RR', 'S': 'RR', 'J': 'NN0', 'I': 'NN0'}[e_], st_)
    c.have('S', 'ge0', s0)
    FZ = '( 1 ... %s )' % MJ
    # MJ e. NN, 1 <_ MJ
    nb2 = c.mem(NB2, 'RR+')
    mz = dst(w, A, [c.mem(NB2, 'RR')], 'ceilcld', '%s e. ZZ' % MJ)
    mge = dst(w, A, [c.mem(NB2, 'RR')], 'ceilged', '%s <_ %s' % (NB2, MJ))
    m0 = linarith(w, A, [mge, c.gt0(NB2)], '0 < %s' % MJ, closure=Closure(w, A, {MJ: dst(w, A, [mz], 'zred', '%s e. RR' % MJ), NB2: c.mem(NB2, 'RR')}))
    mn = dst(w, A, [J(w, A, mz, m0), w.inst('elnnz')], 'sylibr', '%s e. NN' % MJ)
    c.leaf(MJ, 'NN', mn)
    m1 = dst(w, A, [mn], 'nnge1d', '1 <_ %s' % MJ)
    # the coefficient mapping
    AF = '( d e. NN |-> %s )' % COEFF('J', 'I', 'd', 'S')
    Ak = '( %s /\\ k e. %s )' % (A, FZ)
    ck = c.child('k', FZ)
    kN = ck.mem('k', 'NN')
    rp3 = J(w, A, c.mem('D', 'RR+'), c.mem('( 2 x. D )', 'RR+'), linarith(w, A, [F['d1']], 'D < ( 2 x. D )', closure=c))
    ck.leaf(BVA('k'), 'RR', ap(w, Ak, 'bvare', [J(w, Ak, lift(w, rp3, Ak), kN)], '%s e. RR' % BVA('k')))
    CFk = COEFF('J', 'I', 'k', 'S')
    cfk = ck.mem(CFk, 'CC')
    afk = fvmd(w, Ak, 'd', 'NN', COEFF('J', 'I', 'd', 'S'), 'k', kN, cfk)
    akc = dst(w, Ak, [afk, cfk], 'eqeltrd', '( %s ` k ) e. CC' % AF)
    aok = dst(w, A, [akc], 'ralrimiva', 'A. k e. %s ( %s ` k ) e. CC' % (FZ, AF))
    hlv = J(w, A, J(w, A, J(w, A, nn_, tr, t2), J(w, A, dst(w, A, [mn], 'nnnn0d', '%s e. NN0' % MJ), aok)), m1)
    # the maps K', Y' (binder e); the family quantifiers of mvlvm in the letters c (for a) and g (for b)
    KP = '( e e. F |-> ( K ` e ) )'; YQ = '( e e. F |-> ( Im ` ( Y ` e ) ) )'
    Ae = '( %s /\\ e e. F )' % A
    ein = w.s([], 'simpr', '( %s -> e e. F )' % Ae)
    ke_, _ = inst_forall(w, Ae, lift(w, G['kal'], Ae), 'a', '( K ` a ) e. %s' % DB(), 'e', ein)
    ye_, _ = inst_forall(w, Ae, lift(w, G['yal'], Ae), 'a', '( Y ` a ) e. CC', 'e', ein)
    kf = dst(w, A, [ke_], 'fmpttd', '%s : F --> %s' % (KP, DB()))
    yf = dst(w, A, [dst(w, Ae, [ye_], 'imcld', '( Im ` ( Y ` e ) ) e. RR')], 'fmpttd', '%s : F --> RR' % YQ)
    hfam = J(w, A, G['fin'], kf, yf)
    v8p = dst(w, A, [ap(w, A, 'ldenv8', [F['hz']], concl('ldenv8'))], 'simpld', '( %s e. RR+ /\\ ( %s x. %s ) = 1 )' % (V8, V8, W8))
    v8p = dst(w, A, [v8p], 'simpld', '%s e. RR+' % V8)
    hv = J(w, A, dst(w, A, [v8p], 'rpred', '%s e. RR' % V8), dst(w, A, [v8p], 'rpge0d', '0 <_ %s' % V8))

    def vals(Az, Z, zin):
        """( Az -> ( KP ` Z ) = ( K ` Z ) ), ( Az -> ( YQ ` Z ) = Im ( Y ` Z ) ), plus ( K Z ) e. DB, ( Y Z ) e. CC"""
        kz, _ = inst_forall(w, Az, lift(w, G['kal'], Az), 'a', '( K ` a ) e. %s' % DB(), Z, zin)
        yz, _ = inst_forall(w, Az, lift(w, G['yal'], Az), 'a', '( Y ` a ) e. CC', Z, zin)
        kv = fvmd(w, Az, 'e', 'F', '( K ` e )', Z, zin, dst(w, Az, [kz], 'elexd', '( K ` %s ) e. _V' % Z))
        yv = fvmd(w, Az, 'e', 'F', '( Im ` ( Y ` e ) )', Z, zin, dst(w, Az, [dst(w, Az, [yz], 'imcld', '( Im ` ( Y ` %s ) ) e. RR' % Z)], 'recnd', '( Im ` ( Y ` %s ) ) e. CC' % Z))
        return kv, yv, kz, yz
    # RNGF (letter c)
    Ac = '( %s /\\ c e. F )' % A
    cin = w.s([], 'simpr', '( %s -> c e. F )' % Ac)
    kvc, yvc, kzc, yzc = vals(Ac, 'c', cin)
    rngc, _ = inst_forall(w, Ac, lift(w, G['rng'], Ac), 'a', RNGA[len('A. a e. F '):], 'c', cin)
    rng2 = dst(w, Ac, [dst(w, Ac, [yvc], 'fveq2d', '( abs ` ( %s ` c ) ) = ( abs ` ( Im ` ( Y ` c ) ) )' % YQ), rngc], 'eqbrtrd', '( abs ` ( %s ` c ) ) <_ T' % YQ)
    rngf = dst(w, A, [rng2], 'ralrimiva', 'A. c e. F ( abs ` ( %s ` c ) ) <_ T' % YQ)
    # SEPF (letters c g)
    Acg = '( %s /\\ ( c e. F /\\ g e. F ) )' % A
    cin2 = w.s([], 'simprl', '( %s -> c e. F )' % Acg); gin2 = w.s([], 'simprr', '( %s -> g e. F )' % Acg)
    kvc2, yvc2, _, _ = vals(Acg, 'c', cin2); kvg2, yvg2, _, _ = vals(Acg, 'g', gin2)
    SB = SEPY[len('A. a e. F A. b e. F '):]
    cg1, S1 = w.wcongr(SB, {'a': 'c'}, 'a = c', {'a': w.s([], 'id', '( a = c -> a = c )')})
    cg1b = w.s([cg1], 'ralbidv', '( a = c -> ( A. b e. F %s <-> A. b e. F %s ) )' % (SB, S1))
    sep1 = w.s([cg1b, lift(w, G['sep'], Acg), cin2], 'rspcdva', '( %s -> A. b e. F %s )' % (Acg, S1))
    cg2, S2 = w.wcongr(S1, {'b': 'g'}, 'b = g', {'b': w.s([], 'id', '( b = g -> b = g )')})
    sep2 = w.s([cg2, sep1, gin2], 'rspcdva', '( %s -> %s )' % (Acg, S2))
    HYP = '( c =/= g /\\ ( K ` c ) = ( K ` g ) )'
    HYP2 = '( c =/= g /\\ ( %s ` c ) = ( %s ` g ) )' % (KP, KP)
    IMc, IMg = '( Im ` ( Y ` c ) )', '( Im ` ( Y ` g ) )'
    CON = '1 <_ ( abs ` ( %s - %s ) )' % (IMc, IMg)
    CON2 = '1 <_ ( abs ` ( ( %s ` c ) - ( %s ` g ) ) )' % (YQ, YQ)
    assert S2 == '( %s -> %s )' % (HYP, CON), S2
    hb = dst(w, Acg, [dst(w, Acg, [kvc2, kvg2], 'eqeq12d', '( ( %s ` c ) = ( %s ` g ) <-> ( K ` c ) = ( K ` g ) )' % (KP, KP))], 'anbi2d', '( %s <-> %s )' % (HYP2, HYP))
    cb = dst(w, Acg, [dst(w, Acg, [dst(w, Acg, [yvc2, yvg2], 'oveq12d', '( ( %s ` c ) - ( %s ` g ) ) = ( %s - %s )' % (YQ, YQ, IMc, IMg))], 'fveq2d', '( abs ` ( ( %s ` c ) - ( %s ` g ) ) ) = ( abs ` ( %s - %s ) )' % (YQ, YQ, IMc, IMg))],
             'breq2d', '( %s <-> %s )' % (CON2, CON))
    ib = dst(w, Acg, [hb, cb], 'imbi12d', '( ( %s -> %s ) <-> ( %s -> %s ) )' % (HYP2, CON2, HYP, CON))
    sep4 = dst(w, Acg, [sep2, ib], 'mpbird', '( %s -> %s )' % (HYP2, CON2))
    sepf = dst(w, A, [sep4], 'ralrimivva', 'A. c e. F A. g e. F ( %s -> %s )' % (HYP2, CON2))
    # the large-values hypothesis: TWISTX ( J , I , Im Y c , S , K c ) = DS ( KP c , YQ c )
    # the sum letter n is bound in the antecedent (LVA): the rewriting runs in the letter h (sumeq2dv's $d)
    DSc = MVDS('( %s ` c )' % KP, '( %s ` c )' % YQ, A=AF, n='h').replace('( 1 ... M )', FZ)
    TWn = TWISTX('J', 'I', IMc, 'S', '( K ` c )')
    TWc = tsub(TWn, {'n': 'h'})
    lvc0, _ = inst_forall(w, Ac, lift(w, G['lva'], Ac), 'a', LVA[len('A. a e. F '):], 'c', cin)
    BODYn = TWn[len('sum_ n e. %s ' % FZ):]
    cg, BODYh = w.congr(BODYn, {'n': 'h'}, 'n = h', {'n': w.s([], 'id', '( n = h -> n = h )')})
    assert 'sum_ h e. %s %s' % (FZ, BODYh) == TWc
    cbv = w.s([cg], 'cbvsumv', '%s = %s' % (TWn, TWc))
    cbvb = w.s([w.s([cbv], 'fveq2i', '( abs ` %s ) = ( abs ` %s )' % (TWn, TWc))], 'breq2i', '( %s <_ ( abs ` %s ) <-> %s <_ ( abs ` %s ) )' % (V8, TWn, V8, TWc))
    lvc = w.s([lvc0, cbvb], 'sylib', '( %s -> %s <_ ( abs ` %s ) )' % (Ac, V8, TWc))
    Acn = '( %s /\\ h e. %s )' % (Ac, FZ)
    nN = ap(w, Acn, 'elfznn', [w.s([], 'simpr', '( %s -> h e. %s )' % (Acn, FZ))], 'h e. NN')
    can = Closure(w, Acn, {'D': [('RR+', lift(w, F['rp'], Acn)), ('gt1', lift(w, F['d1'], Acn))], 'h': ('NN', nN), 'J': ('NN0', lift(w, jn, Acn)), 'I': ('NN0', lift(w, inn, Acn)), 'S': ('RR', lift(w, sr, Acn)),
                             YP: ('RR+', lift(w, F['yrp'], Acn))})
    can.leaf(BVA('h'), 'RR', ap(w, Acn, 'bvare', [J(w, Acn, lift(w, rp3, Acn), nN)], '%s e. RR' % BVA('h')))
    CFh = COEFF('J', 'I', 'h', 'S')
    afn = fvmd(w, Acn, 'd', 'NN', COEFF('J', 'I', 'd', 'S'), 'h', nN, can.mem(CFh, 'CC'))
    CH = lambda X: CHV(X, 'h')
    t1 = dst(w, Acn, [afn, dst(w, Acn, [lift(w, kvc, Acn)], 'fveq1d', '%s = %s' % (CH('( %s ` c )' % KP), CH('( K ` c )')))], 'oveq12d',
             '( ( %s ` h ) x. %s ) = ( %s x. %s )' % (AF, CH('( %s ` c )' % KP), CFh, CH('( K ` c )')))
    t2_ = dst(w, Acn, [dst(w, Acn, [dst(w, Acn, [lift(w, yvc, Acn)], 'oveq2d', '( -u ( log ` h ) x. ( %s ` c ) ) = ( -u ( log ` h ) x. %s )' % (YQ, IMc))], 'oveq2d',
                                    '( _i x. ( -u ( log ` h ) x. ( %s ` c ) ) ) = ( _i x. ( -u ( log ` h ) x. %s ) )' % (YQ, IMc))], 'fveq2d', '%s = %s' % (NEX('h', '( %s ` c )' % YQ), NEX('h', IMc)))
    t3 = dst(w, Acn, [t1, t2_], 'oveq12d', '( ( ( %s ` h ) x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (AF, CH('( %s ` c )' % KP), NEX('h', '( %s ` c )' % YQ), CFh, CH('( K ` c )'), NEX('h', IMc)))
    se = dst(w, Ac, [t3], 'sumeq2dv', '%s = %s' % (DSc, TWc))
    bi = dst(w, Ac, [dst(w, Ac, [se], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (DSc, TWc))], 'breq2d', '( %s <_ ( abs ` %s ) <-> %s <_ ( abs ` %s ) )' % (V8, DSc, V8, TWc))
    lv2 = dst(w, Ac, [lvc, bi], 'mpbird', '%s <_ ( abs ` %s )' % (V8, DSc))
    lvf = dst(w, A, [lv2], 'ralrimiva', 'A. c e. F %s <_ ( abs ` %s )' % (V8, DSc))
    # mvlvm
    SUB = {'S': 'F', 'K': KP, 'Y': YQ, 'A': AF, 'M': MJ, 'V': V8, 'a': 'c', 'b': 'g', 'n': 'h'}
    hyp = J(w, A, J(w, A, hlv, J(w, A, hfam, hv), J(w, A, rngf, sepf)), lvf)
    import mvlib
    mvc = split_imp(mvlib.STATEMENTS['mvlvm'])[1]
    mv = ap(w, A, 'mvlvm', [hyp], subst(mvc, SUB))
    # rewrite the mass sum
    An = '( %s /\\ h e. %s )' % (A, FZ)
    nN2 = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> h e. %s )' % (An, FZ))], 'h e. NN')
    cn = Closure(w, An, {'D': [('RR+', lift(w, F['rp'], An)), ('gt1', lift(w, F['d1'], An))], 'h': ('NN', nN2), 'J': ('NN0', lift(w, jn, An)), 'I': ('NN0', lift(w, inn, An)), 'S': ('RR', lift(w, sr, An)),
                          YP: ('RR+', lift(w, F['yrp'], An))})
    cn.leaf(BVA('h'), 'RR', ap(w, An, 'bvare', [J(w, An, lift(w, rp3, An), nN2)], '%s e. RR' % BVA('h')))
    afn2 = fvmd(w, An, 'd', 'NN', COEFF('J', 'I', 'd', 'S'), 'h', nN2, cn.mem(CFh, 'CC'))
    tt = dst(w, An, [dst(w, An, [afn2], 'fveq2d', '( abs ` ( %s ` h ) ) = ( abs ` %s )' % (AF, CFh))], 'oveq1d', '( ( abs ` ( %s ` h ) ) ^ 2 ) = ( ( abs ` %s ) ^ 2 )' % (AF, CFh))
    SH = 'sum_ h e. %s ( ( abs ` %s ) ^ 2 )' % (FZ, CFh)
    CFn = COEFF('J', 'I', 'n', 'S')
    SN = 'sum_ n e. %s ( ( abs ` %s ) ^ 2 )' % (FZ, CFn)
    se2 = dst(w, A, [tt], 'sumeq2dv', 'sum_ h e. %s ( ( abs ` ( %s ` h ) ) ^ 2 ) = %s' % (FZ, AF, SH))
    cg2, _ = w.congr('( ( abs ` %s ) ^ 2 )' % CFh, {'h': 'n'}, 'h = n', {'h': w.s([], 'id', '( h = n -> h = n )')})
    cbv2 = w.s([cg2], 'cbvsumv', '%s = %s' % (SH, SN))
    se3 = dst(w, A, [se2, w.s([cbv2], 'a1i', '( %s -> %s = %s )' % (A, SH, SN))], 'eqtrd', 'sum_ h e. %s ( ( abs ` ( %s ` h ) ) ^ 2 ) = %s' % (FZ, AF, SN))
    PREF = '( ( ; ; 3 0 0 x. ( ( 1 + ( log ` %s ) ) ^ 2 ) ) x. ( %s + ( N x. T ) ) )' % (MJ, MJ)
    rw = dst(w, A, [se3], 'oveq2d', '( %s x. sum_ h e. %s ( ( abs ` ( %s ` h ) ) ^ 2 ) ) = ( %s x. %s )' % (PREF, FZ, AF, PREF, SN))
    fin_ = dst(w, A, [mv, rw], 'breqtrd', concl('ldenlv'))
    return fin(w, fin_)


def c1parts(w, A, P):
    """the ldenc1(b) antecedent's facts: base closure plus N T S J I family and the block/twist pieces"""
    c, F = basecl(w, A, P)
    for e_, f_, k_ in (('N', 'N e. NN', 'NN'), ('T', 'T e. RR', 'RR'), ('S', 'S e. RR', 'RR'), ('J', 'J e. NN0', 'NN0'), ('I', 'I e. NN0', 'NN0')):
        F[e_] = P[f_]; c.leaf(e_, k_, F[e_])
    F['t2'] = P['2 <_ T']; F['ntd'] = P['( N x. T ) <_ D']; F['s39'] = P['( ; 3 9 / ; 5 0 ) <_ S']; F['s1'] = P['S <_ 1']; F['jlt'] = P['J < %s' % JPAR]
    F['s0'] = linarith(w, A, [F['s39']], '0 <_ S', closure=c); c.have('S', 'ge0', F['s0'])
    c.have('T', 'ge0', linarith(w, A, [F['t2']], '0 <_ T', closure=c))
    c.leaf(LOGD, 'ge0', linarith(w, A, [F['dl']], '0 <_ %s' % LOGD, closure=c))
    G = famparts(w, A, P)
    F.update(G)
    return c, F


def gen_c1b():
    w = W('ldenc1b', 'Lean ` classI_card_le ` , the case of a nonempty block ` 2 ^ j D < Nmax D ` : LV1 ( ~ ldenlv ) with the coefficient mass ( ~ ldencjs ), the block exponent ( ~ ldenblk , ~ ldenrp ) and the threshold ( ~ ldenv8 ): ` card <_ 8062156800 log ^ 10 D D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) <_ 10 ^ 10 log ^ 10 D D ^ ( ... ) ` .')
    A = ante('ldenc1b'); P = parts(w, A)
    c, F = c1parts(w, A, P)
    blk = P['%s < %s' % (NBJ, NMAX)]
    L = LOGD
    # ldenlv
    hlv = J(w, A, J(w, A, J(w, A, F['hz'], J(w, A, F['N'], J(w, A, F['T'], F['t2']))), J(w, A, J(w, A, F['S'], F['s0']), J(w, A, F['J'], F['I']))),
            J(w, A, J(w, A, J(w, A, F['fin'], J(w, A, F['kal'], F['yal'])), J(w, A, F['rng'], F['sep'])), F['lva']))
    lv0 = ap(w, A, 'ldenlv', [hlv], concl('ldenlv'))
    FZ = '( 1 ... %s )' % MJ
    CFn = COEFF('J', 'I', 'n', 'S'); CFh = COEFF('J', 'I', 'h', 'S')
    SN = 'sum_ n e. %s ( ( abs ` %s ) ^ 2 )' % (FZ, CFn)
    Gs = 'sum_ h e. %s ( ( abs ` %s ) ^ 2 )' % (FZ, CFh)
    # the antecedent binds n (LVA): the mass sum is handled in the letter h
    cgn, _ = w.congr('( ( abs ` %s ) ^ 2 )' % CFn, {'n': 'h'}, 'n = h', {'n': w.s([], 'id', '( n = h -> n = h )')})
    cbvg = w.s([cgn], 'cbvsumv', '%s = %s' % (SN, Gs))
    X1 = '( 1 + ( log ` %s ) )' % MJ
    PREF0 = '( ( ; ; 3 0 0 x. ( %s ^ 2 ) ) x. ( %s + ( N x. T ) ) )' % (X1, MJ)
    lv = dst(w, A, [lv0, w.s([w.s([cbvg], 'oveq2i', '( %s x. %s ) = ( %s x. %s )' % (PREF0, SN, PREF0, Gs))], 'a1i', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A, PREF0, SN, PREF0, Gs))], 'breqtrd',
             '( ( # ` F ) x. ( %s ^ 2 ) ) <_ ( %s x. %s )' % (V8, PREF0, Gs))
    # MJ facts
    c.leaf(NBJ, 'RR+', c.mem(NBJ, 'RR+')); c.leaf(NB2, 'RR+', c.mem(NB2, 'RR+'))
    mz = dst(w, A, [c.mem(NB2, 'RR')], 'ceilcld', '%s e. ZZ' % MJ)
    mge = dst(w, A, [c.mem(NB2, 'RR')], 'ceilged', '%s <_ %s' % (NB2, MJ))
    mlt = w.s([c.mem(NB2, 'RR'), w.inst('ceilm1lt')], 'syl', '( %s -> ( %s - 1 ) < %s )' % (A, MJ, NB2))
    mr = dst(w, A, [mz], 'zred', '%s e. RR' % MJ)
    c.leaf(MJ, 'RR', mr)
    m0 = linarith(w, A, [mge, c.gt0(NB2)], '0 < %s' % MJ, closure=c)
    mn = dst(w, A, [J(w, A, mz, m0), w.inst('elnnz')], 'sylibr', '%s e. NN' % MJ)
    c.leaf(MJ, 'NN', mn)
    mrp = c.mem(MJ, 'RR+')
    nb2e = nb2_eq(w, A, c, F['J'])
    e2j = ap(w, A, 'expge1', [J(w, A, num_(w, A, '2'), F['J'], linarith(w, A, [], '1 <_ 2', closure=c))], '1 <_ ( 2 ^ J )')
    c.atom('( 2 ^ J )'); c.leaf('( 2 ^ J )', 'RR', c.mem('( 2 ^ J )', 'RR'))
    nbge = dst(w, A, [num_(w, A, '1'), c.mem('( 2 ^ J )', 'RR'), c.mem('D', 'RR'), c.ge0('D'), e2j], 'lemul1ad', '( 1 x. D ) <_ ( ( 2 ^ J ) x. D )')
    dnb = dst(w, A, [eqc(w, A, dst(w, A, [c.mem('D', 'CC')], 'mullidd', '( 1 x. D ) = D')), nbge], 'eqbrtrd', 'D <_ %s' % NBJ)
    c.atom(NBJ)
    m3 = linarith(w, A, [mlt, nb2e, dnb, F['d1']], '%s <_ ( 3 x. %s )' % (MJ, NBJ), closure=c)
    ntnb = linarith(w, A, [F['ntd'], dnb], '( N x. T ) <_ %s' % NBJ, closure=c)
    c.leaf('( N x. T )', 'RR', c.mem('( N x. T )', 'RR'))
    m4 = linarith(w, A, [m3, ntnb], '( %s + ( N x. T ) ) <_ ( 4 x. %s )' % (MJ, NBJ), closure=c)
    # 1 + log MJ <_ 3 L
    lm = dst(w, A, [c.mem(MJ, 'RR+')], 'relogcld', '( log ` %s ) e. RR' % MJ)
    NB3 = '( 3 x. %s )' % NBJ
    lm1 = dst(w, A, [m3, dst(w, A, [mrp, c.mem(NB3, 'RR+')], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (MJ, NB3, MJ, NB3))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (MJ, NB3))
    l3 = dst(w, A, [num_(w, A, '3', 'RR+'), c.mem(NBJ, 'RR+')], 'relogmuld', '( log ` %s ) = ( ( log ` 3 ) + ( log ` %s ) )' % (NB3, NBJ))
    lnb = dst(w, A, [c.mem('( 2 ^ J )', 'RR+'), F['rp']], 'relogmuld', '( log ` %s ) = ( ( log ` ( 2 ^ J ) ) + ( log ` D ) )' % NBJ)
    l2j = w.s([num_(w, A, '2', 'RR+'), dst(w, A, [F['J']], 'nn0zd', 'J e. ZZ'), w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( 2 ^ J ) ) = ( J x. ( log ` 2 ) ) )' % A)
    log3 = ap(w, A, 'loglet', [J(w, A, num_(w, A, '3'), linarith(w, A, [], '1 <_ 3', closure=c))], '( log ` 3 ) <_ 3')
    log2 = a1(w, A, 'log2le1', '( log ` 2 ) < 1')
    lg2r = dst(w, A, [num_(w, A, '2', 'RR+')], 'relogcld', '( log ` 2 ) e. RR')
    c.leaf('( log ` 2 )', 'RR', lg2r); c.leaf('( log ` 3 )', 'RR', dst(w, A, [num_(w, A, '3', 'RR+')], 'relogcld', '( log ` 3 ) e. RR'))
    jl = dst(w, A, [F['jlt'], w.s([dst(w, A, [F['J']], 'nn0zd', 'J e. ZZ'), dst(w, A, [F['jn']], 'nnzd', '%s e. ZZ' % JPAR), w.inst('zltp1le')], 'syl2anc', '( %s -> ( J < %s <-> ( J + 1 ) <_ %s ) )' % (A, JPAR, JPAR))], 'mpbid', '( J + 1 ) <_ %s' % JPAR)
    jp2 = dst(w, A, [F['jp']], 'simprd', '( %s <_ %s /\\ %s <_ ( %s + 1 ) /\\ %s <_ ( 2 x. %s ) )' % (L, JPAR, JPAR, L, JPAR, L))
    jl1 = dst(w, A, [jp2], 'simp2d', '%s <_ ( %s + 1 )' % (JPAR, L))
    c.atom(JPAR); c.atom(L)
    jle = linarith(w, A, [jl, jl1], 'J <_ %s' % L, closure=c)
    jl2 = dst(w, A, [lg2r, num_(w, A, '1'), c.mem('J', 'RR'), c.ge0('J'), ltle(w, A, c, log2)], 'lemul2ad', '( J x. ( log ` 2 ) ) <_ ( J x. 1 )')
    jl3 = dst(w, A, [jl2, dst(w, A, [c.mem('J', 'CC')], 'mulridd', '( J x. 1 ) = J')], 'breqtrd', '( J x. ( log ` 2 ) ) <_ J')
    c.leaf('( J x. ( log ` 2 ) )', 'RR', c.mem('( J x. ( log ` 2 ) )', 'RR'))
    c.leaf('( log ` %s )' % MJ, 'RR', lm); c.leaf('( log ` %s )' % NB3, 'RR', c.mem('( log ` %s )' % NB3, 'RR')); c.leaf('( log ` ( 2 ^ J ) )', 'RR', c.mem('( log ` ( 2 ^ J ) )', 'RR')); c.leaf('( log ` %s )' % NBJ, 'RR', c.mem('( log ` %s )' % NBJ, 'RR'))
    x1le = linarith(w, A, [lm1, l3, lnb, l2j, log3, jl3, jle, F['dl']], '%s <_ ( 3 x. %s )' % (X1, L), closure=c)
    lm0 = dst(w, A, [mr, dst(w, A, [mn], 'nnge1d', '1 <_ %s' % MJ)], 'logge0d', '0 <_ ( log ` %s )' % MJ)
    x1ge0 = linarith(w, A, [lm0], '0 <_ %s' % X1, closure=c)
    L3 = '( 3 x. %s )' % L
    x1sq = ap(w, A, 'le2sq2', [J(w, A, c.mem(X1, 'RR'), x1ge0), J(w, A, c.mem(L3, 'RR'), x1le)], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (X1, L3))
    x1cu = ap(w, A, 'leexp1a', [J(w, A, c.mem(X1, 'RR'), c.mem(L3, 'RR'), a1(w, A, '3nn0', '3 e. NN0')), J(w, A, x1ge0, x1le)], '( %s ^ 3 ) <_ ( %s ^ 3 )' % (X1, L3))
    # hX: ( MJ + NT ) G <_ 12 (3L)^3 ( 9 L PE )
    hg0 = ap(w, A, 'ldencjs', [J(w, A, J(w, A, J(w, A, F['dr'], F['z']), J(w, A, F['S'], F['s0'])), J(w, A, J(w, A, F['J'], F['I']), mn))], tsub(concl('ldencjs'), {'M': MJ}))
    hg = dst(w, A, [w.s([cbvg], 'a1i', '( %s -> %s = %s )' % (A, SN, Gs)), hg0], 'eqbrtrrd', '%s <_ %s' % (Gs, tsub(concl('ldencjs'), {'M': MJ}).rsplit(' <_ ', 1)[1]))
    c.leaf(NBS, 'RR+', c.mem(NBS, 'RR+'))
    SQ2 = '( %s ^ 2 )' % NBS
    An = '( %s /\\ h e. %s )' % (A, FZ)
    nN = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> h e. %s )' % (An, FZ))], 'h e. NN')
    cn = Closure(w, An, {'D': [('RR+', lift(w, F['rp'], An)), ('gt1', lift(w, F['d1'], An))], 'h': ('NN', nN), 'J': ('NN0', lift(w, F['J'], An)), 'I': ('NN0', lift(w, F['I'], An)), 'S': ('RR', lift(w, F['S'], An)),
                          YP: ('RR+', lift(w, F['yrp'], An))})
    rp3 = J(w, A, c.mem('D', 'RR+'), c.mem('( 2 x. D )', 'RR+'), linarith(w, A, [F['d1']], 'D < ( 2 x. D )', closure=c))
    cn.leaf(BVA('h'), 'RR', ap(w, An, 'bvare', [J(w, An, lift(w, rp3, An), nN)], '%s e. RR' % BVA('h')))
    ab2 = dst(w, An, [dst(w, An, [cn.mem(CFh, 'CC')], 'abscld', '( abs ` %s ) e. RR' % CFh)], 'resqcld', '( ( abs ` %s ) ^ 2 ) e. RR' % CFh)
    ab20 = dst(w, An, [dst(w, An, [cn.mem(CFh, 'CC')], 'abscld', '( abs ` %s ) e. RR' % CFh)], 'sqge0d', '0 <_ ( ( abs ` %s ) ^ 2 )' % CFh)
    fi = dst(w, A, [], 'fzfid', '%s e. Fin' % FZ)
    gr = dst(w, A, [fi, ab2], 'fsumrecl', '%s e. RR' % Gs); g0 = dst(w, A, [fi, ab2, ab20], 'fsumge0', '0 <_ %s' % Gs)
    c.leaf(Gs, 'RR', gr); c.have(Gs, 'ge0', g0)
    MX = '( %s x. ( %s ^ 3 ) )' % (MJ, X1)
    mx2 = dst(w, A, [mr, c.mem(NB3, 'RR'), c.mem('( %s ^ 3 )' % X1, 'RR'), c.mem('( %s ^ 3 )' % L3, 'RR'), c.ge0(MJ), c.ge0('( %s ^ 3 )' % X1), m3, x1cu], 'lemul12ad', '%s <_ ( %s x. ( %s ^ 3 ) )' % (MX, NB3, L3))
    MX2 = '( %s x. ( %s ^ 3 ) )' % (NB3, L3)
    g1 = dst(w, A, [gr, c.mem('( %s x. %s )' % (SQ2, MX), 'RR'), c.mem('( %s x. %s )' % (SQ2, MX2), 'RR'), hg, lemul(w, A, c, mx2, SQ2, side=2)], 'letrd', '%s <_ ( %s x. %s )' % (Gs, SQ2, MX2))
    NB4 = '( 4 x. %s )' % NBJ
    hx = dst(w, A, [c.mem('( %s + ( N x. T ) )' % MJ, 'RR'), c.mem(NB4, 'RR'), gr, c.mem('( %s x. %s )' % (SQ2, MX2), 'RR'), c.ge0('( %s + ( N x. T ) )' % MJ), g0, m4, g1], 'lemul12ad',
             '( ( %s + ( N x. T ) ) x. %s ) <_ ( %s x. ( %s x. %s ) )' % (MJ, Gs, NB4, SQ2, MX2))
    E = '( 2 - ( 2 x. S ) )'
    rpw = ap(w, A, 'ldenrp', [J(w, A, c.mem(NBJ, 'RR+'), F['S'])], tsub(concl('ldenrp'), {'X': NBJ}))
    L33 = '( ; 1 2 x. ( %s ^ 3 ) )' % L3
    e1 = ringeqp(w, A, '( %s x. ( %s x. %s ) )' % (NB4, SQ2, MX2), '( %s x. ( %s x. ( %s ^ 2 ) ) )' % (L33, SQ2, NBJ), c)
    e2 = dst(w, A, [rpw], 'oveq2d', '( %s x. ( %s x. ( %s ^ 2 ) ) ) = ( %s x. ( %s ^c %s ) )' % (L33, SQ2, NBJ, L33, NBJ, E))
    bl = ap(w, A, 'ldenblk', [J(w, A, J(w, A, F['hz'], J(w, A, F['S'], J(w, A, F['s39'], F['s1']))), J(w, A, F['J'], blk))], concl('ldenblk'))
    L9PE = '( ( 9 x. %s ) x. %s )' % (L, PE)
    c.leaf(PE, 'RR+', c.mem(PE, 'RR+')); c.leaf('( %s ^c %s )' % (NBJ, E), 'RR+', c.mem('( %s ^c %s )' % (NBJ, E), 'RR+'))
    bl2 = lemul(w, A, c, bl, L33, side=2)
    hx2 = dst(w, A, [c.mem('( ( %s + ( N x. T ) ) x. %s )' % (MJ, Gs), 'RR'), c.mem('( %s x. ( %s ^c %s ) )' % (L33, NBJ, E), 'RR'), c.mem('( %s x. %s )' % (L33, L9PE), 'RR'),
                     dst(w, A, [hx, eqt(w, A, e1, e2)], 'breqtrd', '( ( %s + ( N x. T ) ) x. %s ) <_ ( %s x. ( %s ^c %s ) )' % (MJ, Gs, L33, NBJ, E)), bl2], 'letrd',
              '( ( %s + ( N x. T ) ) x. %s ) <_ ( %s x. %s )' % (MJ, Gs, L33, L9PE))
    # the threshold
    v8 = ap(w, A, 'ldenv8', [F['hz']], concl('ldenv8'))
    v8a = dst(w, A, [v8], 'simpld', '( %s e. RR+ /\\ ( %s x. %s ) = 1 )' % (V8, V8, W8)); v8b = dst(w, A, [v8], 'simprd', '( %s <_ ( ; 3 2 x. ( %s ^ 2 ) ) /\\ ( %s <_ ( 2 x. %s ) /\\ ( %s + 1 ) <_ ( 2 x. %s ) ) )' % (W8, L, JPAR, L, JPAR, L))
    v8p = dst(w, A, [v8a], 'simpld', '%s e. RR+' % V8); vw = dst(w, A, [v8a], 'simprd', '( %s x. %s ) = 1' % (V8, W8)); w8le = dst(w, A, [v8b], 'simpld', '%s <_ ( ; 3 2 x. ( %s ^ 2 ) )' % (W8, L))
    c.leaf(V8, 'RR+', v8p); c.leaf(W8, 'RR+', c.mem(W8, 'RR+'))
    HF = '( # ` F )'
    hf = w.s([F['fin'], w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A, HF)); c.leaf(HF, 'NN0', hf)
    W82 = '( %s ^ 2 )' % W8
    e3 = ringeqp(w, A, '( ( %s x. ( %s ^ 2 ) ) x. %s )' % (HF, V8, W82), '( %s x. ( ( %s x. %s ) ^ 2 ) )' % (HF, V8, W8), c)
    e4 = dst(w, A, [dst(w, A, [dst(w, A, [vw], 'oveq1d', '( ( %s x. %s ) ^ 2 ) = ( 1 ^ 2 )' % (V8, W8)), a1(w, A, 'sq1', '( 1 ^ 2 ) = 1')], 'eqtrd', '( ( %s x. %s ) ^ 2 ) = 1' % (V8, W8))], 'oveq2d', '( %s x. ( ( %s x. %s ) ^ 2 ) ) = ( %s x. 1 )' % (HF, V8, W8, HF))
    e5 = eqt(w, A, eqt(w, A, e3, e4), dst(w, A, [c.mem(HF, 'CC')], 'mulridd', '( %s x. 1 ) = %s' % (HF, HF)))
    PREF = '( ( ; ; 3 0 0 x. ( %s ^ 2 ) ) x. ( %s + ( N x. T ) ) )' % (X1, MJ)
    RHS0 = '( %s x. %s )' % (PREF, Gs)
    lvb = lemul(w, A, c, lv, W82, side=1)
    hc = dst(w, A, [eqc(w, A, e5), lvb], 'eqbrtrd', '%s <_ ( %s x. %s )' % (HF, RHS0, W82))
    # bound the three factors
    X12 = '( ; ; 3 0 0 x. ( %s ^ 2 ) )' % X1; L32 = '( ; ; 3 0 0 x. ( %s ^ 2 ) )' % L3
    f1 = lemul(w, A, c, x1sq, '; ; 3 0 0', side=2)
    MG = '( ( %s + ( N x. T ) ) x. %s )' % (MJ, Gs)
    ea = ringeq(w, A, RHS0, '( %s x. %s )' % (X12, MG), c)
    BND2 = '( %s x. %s )' % (L33, L9PE)
    p12 = dst(w, A, [c.mem(X12, 'RR'), c.mem(L32, 'RR'), c.mem(MG, 'RR'), c.mem(BND2, 'RR'), c.ge0(X12), c.ge0(MG), f1, hx2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (X12, MG, L32, BND2))
    L2S = '( ( ; 3 2 x. ( %s ^ 2 ) ) ^ 2 )' % L
    w82 = ap(w, A, 'le2sq2', [J(w, A, c.mem(W8, 'RR'), c.ge0(W8)), J(w, A, c.mem('( ; 3 2 x. ( %s ^ 2 ) )' % L, 'RR'), w8le)], '%s <_ %s' % (W82, L2S))
    p3 = dst(w, A, [c.mem('( %s x. %s )' % (X12, MG), 'RR'), c.mem('( %s x. %s )' % (L32, BND2), 'RR'), c.mem(W82, 'RR'), c.mem(L2S, 'RR'), c.ge0('( %s x. %s )' % (X12, MG)), c.ge0(W82), p12, w82], 'lemul12ad',
             '( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. %s )' % (X12, MG, W82, L32, BND2, L2S))
    hc2 = dst(w, A, [hc, dst(w, A, [ea], 'oveq1d', '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (RHS0, W82, X12, MG, W82))], 'breqtrd', '%s <_ ( ( %s x. %s ) x. %s )' % (HF, X12, MG, W82))
    BIGC = '; ; ; ; ; ; ; ; ; 8 0 6 2 1 5 6 8 0 0'
    LP = '( ( %s ^ ; 1 0 ) x. %s )' % (L, PE)
    en = ringeqp(w, A, '( ( %s x. %s ) x. %s )' % (L32, BND2, L2S), '( %s x. %s )' % (BIGC, LP), c)
    # 8062156800 <_ 10 ^ 10
    p8 = pow10_8(w)
    ten = '; 1 0'
    e10 = w.s([num.fact(w, ten, 'CC'), num.fact(w, '8', 'NN0'), num.fact(w, '2', 'NN0'), w.inst('expadd')], 'mp3an', '( %s ^ ( 8 + 2 ) ) = ( ( %s ^ 8 ) x. ( %s ^ 2 ) )' % (ten, ten, ten))
    e82 = w.s([w.s([num.add_nat(w, '8', '2')], 'oveq2i', '( %s ^ ( 8 + 2 ) ) = ( %s ^ ; 1 0 )' % (ten, ten))], 'eqcomi', '( %s ^ ; 1 0 ) = ( %s ^ ( 8 + 2 ) )' % (ten, ten))
    e2_ = w.s([num.fact(w, ten, 'NN0'), num.fact(w, '1', 'NN0'), w.s([], '2t1e2', '( 2 x. 1 ) = 2'), w.s([num.fact(w, ten, 'CC'), w.inst('exp1')], 'ax-mp', '( %s ^ 1 ) = %s' % (ten, ten)), num.mul_lits(w, ten, ten)], 'numexp2x', '( %s ^ 2 ) = ; ; 1 0 0' % ten)
    e100 = w.s([p8, e2_], 'oveq12i', '( ( %s ^ 8 ) x. ( %s ^ 2 ) ) = ( ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 x. ; ; 1 0 0 )' % (ten, ten))
    TEN10 = '; ; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0 0'
    e10b = w.s([w.s([w.s([e82, e10], 'eqtri', '( %s ^ ; 1 0 ) = ( ( %s ^ 8 ) x. ( %s ^ 2 ) )' % (ten, ten, ten)), e100], 'eqtri', '( %s ^ ; 1 0 ) = ( ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 x. ; ; 1 0 0 )' % ten),
                num.mul_lits(w, '; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0', '; ; 1 0 0')], 'eqtri', '( %s ^ ; 1 0 ) = %s' % (ten, TEN10))
    le = w.s([num.le_nat(w, 8062156800, 10000000000), e10b], 'breqtrri', '%s <_ ( %s ^ ; 1 0 )' % (BIGC, ten))
    c.have(LP, 'RR', c.mem(LP, 'RR')); c.have(LP, 'ge0', c.ge0(LP))
    P10_ = '( %s ^ ; 1 0 )' % ten
    c.leaf(P10_, 'RR', num_(w, A, P10_) if False else dst(w, A, [w.s([w.s([w.s([], '10nn', '; 1 0 e. NN'), w.s([], '10nn0', '; 1 0 e. NN0'), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % P10_)], 'a1i', '( %s -> %s e. NN )' % (A, P10_))], 'nnred', '%s e. RR' % P10_))
    m10 = dst(w, A, [num_(w, A, BIGC), c.mem(P10_, 'RR'), c.mem(LP, 'RR'), c.ge0(LP), w.s([le], 'a1i', '( %s -> %s <_ %s )' % (A, BIGC, P10_))], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (BIGC, LP, P10_, LP))
    ef = ringeq(w, A, '( %s x. %s )' % (P10_, LP), C1(), c)
    t1 = dst(w, A, [c.mem(HF, 'RR'), c.mem('( ( %s x. %s ) x. %s )' % (X12, MG, W82), 'RR'), c.mem('( ( %s x. %s ) x. %s )' % (L32, BND2, L2S), 'RR'), hc2, p3], 'letrd', '%s <_ ( ( %s x. %s ) x. %s )' % (HF, L32, BND2, L2S))
    t2 = dst(w, A, [t1, en], 'breqtrd', '%s <_ ( %s x. %s )' % (HF, BIGC, LP))
    t3 = dst(w, A, [c.mem(HF, 'RR'), c.mem('( %s x. %s )' % (BIGC, LP), 'RR'), c.mem('( %s x. %s )' % (P10_, LP), 'RR'), t2, m10], 'letrd', '%s <_ ( %s x. %s )' % (HF, P10_, LP))
    fin_ = dst(w, A, [t3, ef], 'breqtrd', concl('ldenc1b'))
    return fin(w, fin_)


def gen_c1():
    w = W('ldenc1', '**Lean ` classI_card_le ` ** (Lemma 3.4, audit F1): a ` 1 ` -spaced family on which the ` ( j , k ) ` Taylor component is at least ` Vthr D ` has at most ` 10 ^ 10 log ^ 10 D D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) ` members: the block below ` Nmax D ` by ~ ldenc1b , an empty block by ` coeffJK = 0 ` .')
    A = ante('ldenc1'); P = parts(w, A)
    c, F = c1parts(w, A, P)
    L = LOGD
    CON = concl('ldenc1')
    Ab = '( %s /\\ %s < %s )' % (A, NBJ, NMAX)
    b1 = w.s([w.s([], 'id', '( %s -> %s )' % (Ab, Ab)), w.inst('ldenc1b')], 'syl', '( %s -> %s )' % (Ab, CON))
    # the empty block: NMAX <_ NB
    Ae = '( %s /\\ -. %s < %s )' % (A, NBJ, NMAX)
    ce = Closure(w, Ae, parent=c)
    for e_, k_ in (('D', 'RR+'), (NMAX, 'NN'), ('N', 'NN'), ('T', 'RR'), ('S', 'RR'), ('J', 'NN0'), ('I', 'NN0'), (YP, 'RR+'), (L, 'RR')):
        ce.leaf(e_, k_, lift(w, c.mem(e_, k_), Ae))
    ce.leaf(NBJ, 'RR+', ce.mem(NBJ, 'RR+'))
    nlt = w.s([], 'simpr', '( %s -> -. %s < %s )' % (Ae, NBJ, NMAX))
    nle = dst(w, Ae, [nlt, dst(w, Ae, [ce.mem(NMAX, 'RR'), ce.mem(NBJ, 'RR')], 'lenltd', '( %s <_ %s <-> -. %s < %s )' % (NMAX, NBJ, NBJ, NMAX))], 'mpbird', '%s <_ %s' % (NMAX, NBJ))
    # every member gives V8 <_ abs TWIST = 0: contradiction
    Ar = '( %s /\\ r e. F )' % Ae
    rin = w.s([], 'simpr', '( %s -> r e. F )' % Ar)
    IMr = '( Im ` ( Y ` r ) )'
    lvr, _ = inst_forall(w, Ar, lift(w, F['lva'], Ar), 'a', LVA[len('A. a e. F '):], 'r', rin)
    TWn = TWISTX('J', 'I', IMr, 'S', '( K ` r )')
    FZ = '( 1 ... %s )' % MJ
    TWr = tsub(TWn, {'n': 'h'})
    cgn, _ = w.congr(TWn[len('sum_ n e. %s ' % FZ):], {'n': 'h'}, 'n = h', {'n': w.s([], 'id', '( n = h -> n = h )')})
    cbvt = w.s([cgn], 'cbvsumv', '%s = %s' % (TWn, TWr))
    cbvb = w.s([w.s([cbvt], 'fveq2i', '( abs ` %s ) = ( abs ` %s )' % (TWn, TWr))], 'breq2i', '( %s <_ ( abs ` %s ) <-> %s <_ ( abs ` %s ) )' % (V8, TWn, V8, TWr))
    lvr = w.s([lvr, cbvb], 'sylib', '( %s -> %s <_ ( abs ` %s ) )' % (Ar, V8, TWr))
    Arn = '( %s /\\ h e. %s )' % (Ar, FZ)
    nN = ap(w, Arn, 'elfznn', [w.s([], 'simpr', '( %s -> h e. %s )' % (Arn, FZ))], 'h e. NN')
    cn = Closure(w, Arn, {'h': ('NN', nN), NMAX: ('NN', lift(w, ce.mem(NMAX, 'NN'), Arn)), NBJ: ('RR+', lift(w, ce.mem(NBJ, 'RR+'), Arn))})
    CO = COND('h'); CFn = COEFF('J', 'I', 'h', 'S')
    # -. COND: from NB < n /\ n <_ NMAX contradiction with NMAX <_ NB
    A3 = '( %s /\\ %s )' % (Arn, CO)
    co = w.s([], 'simpr', '( %s -> %s )' % (A3, CO))
    c3 = Closure(w, A3, {'h': ('NN', lift(w, nN, A3)), NMAX: ('NN', lift(w, ce.mem(NMAX, 'NN'), A3)), NBJ: ('RR+', lift(w, ce.mem(NBJ, 'RR+'), A3))})
    c3.atom(NBJ)
    lt1 = dst(w, A3, [co], 'simp1d', '%s < h' % NBJ); le3 = dst(w, A3, [co], 'simp3d', 'h <_ %s' % NMAX)
    bad = linarith(w, A3, [lt1, le3, lift(w, nle, A3)], '%s < %s' % (NBJ, NBJ), closure=c3)
    irr = dst(w, A3, [c3.mem(NBJ, 'RR')], 'ltnrd', '-. %s < %s' % (NBJ, NBJ))
    # ( Arn -> -. COND ) by pm2.65da: ( ( Arn /\ CO ) -> ps ) and ( ( Arn /\ CO ) -> -. ps )
    ncond = w.s([bad, irr], 'pm2.65da', '( %s -> -. %s )' % (Arn, CO))
    iff = dst(w, Arn, [ncond], 'iffalsed', '%s = 0' % CFn)
    CH = CHV('( K ` r )', 'h'); NX = NEX('h', IMr)
    kr, _ = inst_forall(w, Ar, lift(w, F['kal'], Ar), 'a', '( K ` a ) e. %s' % DB(), 'r', rin)
    yr, _ = inst_forall(w, Ar, lift(w, F['yal'], Ar), 'a', '( Y ` a ) e. CC', 'r', rin)
    # ( K r ) ` ( ZRHom n ) e. CC : dchrzrhcl
    g_ = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); z_ = w.s([], 'eqid', '( Z/nZ ` N ) = ( Z/nZ ` N )')
    b_ = w.s([], 'eqid', '%s = %s' % (DB(), DB())); l_ = w.s([], 'eqid', '( ZRHom ` ( Z/nZ ` N ) ) = ( ZRHom ` ( Z/nZ ` N ) )')
    chc = w.s([g_, z_, b_, l_, lift(w, kr, Arn), dst(w, Arn, [nN], 'nnzd', 'h e. ZZ')], 'dchrzrhcl', '( %s -> %s e. CC )' % (Arn, CH))
    cnx = Closure(w, Arn, {'h': ('NN', nN), IMr: ('RR', lift(w, dst(w, Ar, [yr], 'imcld', '%s e. RR' % IMr), Arn)), CH: ('CC', chc), '_i': ('CC', a1(w, Arn, 'ax-icn', '_i e. CC'))})
    t1 = dst(w, Arn, [dst(w, Arn, [iff], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (CFn, CH, CH)), dst(w, Arn, [chc], 'mul02d', '( 0 x. %s ) = 0' % CH)], 'eqtrd', '( %s x. %s ) = 0' % (CFn, CH))
    t2 = dst(w, Arn, [dst(w, Arn, [t1], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( 0 x. %s )' % (CFn, CH, NX, NX)), dst(w, Arn, [cnx.mem(NX, 'CC')], 'mul02d', '( 0 x. %s ) = 0' % NX)], 'eqtrd', '( ( %s x. %s ) x. %s ) = 0' % (CFn, CH, NX))
    se = dst(w, Ar, [t2], 'sumeq2dv', '%s = sum_ h e. %s 0' % (TWr, FZ))
    sz = w.s([w.s([w.s([], 'fzfi', '%s e. Fin' % FZ)], 'olci', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (FZ, FZ)), w.inst('sumz')], 'ax-mp', 'sum_ h e. %s 0 = 0' % FZ)
    tw0 = dst(w, Ar, [se, w.s([sz], 'a1i', '( %s -> sum_ h e. %s 0 = 0 )' % (Ar, FZ))], 'eqtrd', '%s = 0' % TWr)
    ab0 = dst(w, Ar, [dst(w, Ar, [tw0], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % TWr), a1(w, Ar, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % TWr)
    v8le0 = dst(w, Ar, [lvr, ab0], 'breqtrd', '%s <_ 0' % V8)
    v8p = dst(w, A, [dst(w, A, [ap(w, A, 'ldenv8', [F['hz']], concl('ldenv8'))], 'simpld', '( %s e. RR+ /\\ ( %s x. %s ) = 1 )' % (V8, V8, W8))], 'simpld', '%s e. RR+' % V8)
    v8gt = dst(w, Ar, [lift(w, lift(w, v8p, Ae), Ar)], 'rpgt0d', '0 < %s' % V8)
    v8n = dst(w, Ar, [v8gt, dst(w, Ar, [w.s([], '0red', '( %s -> 0 e. RR )' % Ar), lift(w, lift(w, dst(w, A, [v8p], 'rpred', '%s e. RR' % V8), Ae), Ar)], 'ltnled', '( 0 < %s <-> -. %s <_ 0 )' % (V8, V8))], 'mpbid', '-. %s <_ 0' % V8)
    nr = w.s([v8le0, v8n], 'pm2.65da', '( %s -> -. r e. F )' % Ae)
    al = w.s([nr], 'alrimiv', '( %s -> A. r -. r e. F )' % Ae)
    f0 = dst(w, Ae, [al, w.s([], 'eq0', '( F = (/) <-> A. r -. r e. F )')], 'sylibr', 'F = (/)')
    h0 = dst(w, Ae, [dst(w, Ae, [f0], 'fveq2d', '( # ` F ) = ( # ` (/) )'), a1(w, Ae, 'hash0', '( # ` (/) ) = 0')], 'eqtrd', '( # ` F ) = 0')
    ce.leaf(PE, 'RR+', ce.mem(PE, 'RR+'))
    rhs0 = ce.ge0(C1())
    b2 = dst(w, Ae, [h0, rhs0], 'eqbrtrd', CON)
    fin_ = dst(w, A, [b1, b2], 'pm2.61dan', CON)
    return fin(w, fin_)


GENS = {'ldencj': gen_cj, 'ldencjs': gen_cjs, 'ldenrp': gen_rp, 'ldenblk': gen_blk, 'ldenv8': gen_v8, 'ldenlv': gen_lv, 'ldenc1b': gen_c1b, 'ldenc1': gen_c1}
if __name__ == '__main__':
    for lab in (only or list(GENS)):
        GENS[lab]()
