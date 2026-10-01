"""Sortie KD2: step 3 (kd2lsb).  MM_DB=sorties/kd2.mm MM_ENGINE=mmatch python3 tools/gen/kd2_c.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd2lib import *
from cl import formula_of, split_imp
from c9lib import top_and
from lin import linarith, nlinarith
from mvlib import ringeq
import num

only = sys.argv[1:]
ONET = ONE('T')
S0T = S0()


def fterm(q, K='( J + 2 )'):
    return '( %s / ( ( %s - %s ) ^ %s ) )' % (MU(q), S0T, q, K)


def zfacts(w, Ah, z, zmem, chi, tr, ep):
    """under Ah with zmem : ( Ah -> z e. ZD ): z e. CC, Re z <_ 1, E <_ abs ( S0 - z ), 0 < abs ( S0 - z ), S0 - z =/= 0"""
    d = lambda ref, h, c: D(w, Ah, ref, h, c)
    zc = zcc(w, Ah, z, zmem, tr)
    re1 = use(w, Ah, 'kdre1', {'Q': z}, d('3jca', [chi, tr, zmem], '( %s /\\ T e. RR /\\ %s e. %s )' % (CHI, z, ZD())))
    er = d('rpred', [ep], 'E e. RR')
    s0c = d('addcld', [d('recnd', [d('readdcld', [a1(w, Ah, '1re', '1 e. RR'), er], '( 1 + E ) e. RR')], '( 1 + E ) e. CC'),
                       d('mulcld', [a1(w, Ah, 'ax-icn', '_i e. CC'), d('recnd', [tr], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % S0T)
    rs = d('syl2anc', [d('readdcld', [a1(w, Ah, '1re', '1 e. RR'), er], '( 1 + E ) e. RR'), tr, w.inst('crre')], '( Re ` %s ) = ( 1 + E )' % S0T)
    DZ = '( %s - %s )' % (S0T, z)
    rd = d('resubd', [s0c, zc], '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (DZ, S0T, z))
    rz = d('recld', [zc], '( Re ` %s ) e. RR' % z)
    dzc = d('subcld', [s0c, zc], '%s e. CC' % DZ)
    ra = d('releabsd', [dzc], '( Re ` %s ) <_ ( abs ` %s )' % (DZ, DZ))
    cl = Closure(w, Ah, {'E': ('RR', er), '( Re ` %s )' % z: ('RR', rz), '( Re ` %s )' % DZ: ('RR', d('recld', [dzc], '( Re ` %s ) e. RR' % DZ)),
                          '( Re ` %s )' % S0T: ('RR', d('recld', [s0c], '( Re ` %s ) e. RR' % S0T)), '( abs ` %s )' % DZ: ('RR', d('abscld', [dzc], '( abs ` %s ) e. RR' % DZ))})
    for a in ('( Re ` %s )' % z, '( Re ` %s )' % DZ, '( Re ` %s )' % S0T, '( abs ` %s )' % DZ):
        cl.atom(a)
    eab = linarith(w, Ah, [re1, rs, rd, ra], 'E <_ ( abs ` %s )' % DZ, closure=cl)
    e0 = d('rpgt0d', [ep], '0 < E')
    g0 = d('ltletrd', [a1(w, Ah, '0re', '0 e. RR'), er, cl.mem('( abs ` %s )' % DZ, 'RR'), e0, eab], '0 < ( abs ` %s )' % DZ)
    ne = d('mpbid', [g0, d('absgt0d' if False else 'syl', [dzc, w.inst('absgt0')], '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (DZ, DZ))], '%s =/= 0' % DZ) if False else None
    ne = d('sylibr', [g0, d('syl', [dzc, w.inst('absgt0')], '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (DZ, DZ))], '%s =/= 0' % DZ) if False else \
        d('mpbird', [g0, d('syl', [dzc, w.inst('absgt0')], '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (DZ, DZ))], '%s =/= 0' % DZ)
    return dict(zc=zc, re1=re1, s0c=s0c, g0=g0, ne=ne, dzc=dzc, eab=eab)

def ltcc(w, Ah, n, nn_, nxh, kn, sc):
    """( Ah -> LT(K,S,n) e. CC )"""
    d = lambda ref, h, c: D(w, Ah, ref, h, c)
    K = kn[1]; S_ = sc[1]
    lg = d('recnd', [d('relogcld', [d('nnrpd', [nn_], '%s e. RR+' % n)], '( log ` %s ) e. RR' % n)], '( log ` %s ) e. CC' % n)
    lk = d('expcld', [lg, kn[0]], '( ( log ` %s ) ^ %s ) e. CC' % (n, K))
    ch = d('syl2anc', [nxh, nn_, w.inst('lchrcl')], '%s e. CC' % CHV(n))
    lm = d('recnd', [d('syl', [nn_, w.inst('vmacl')], '( Lam ` %s ) e. RR' % n)], '( Lam ` %s ) e. CC' % n)
    a = d('mulcld', [lk, d('mulcld', [ch, lm], '( %s x. ( Lam ` %s ) ) e. CC' % (CHV(n), n))], '( ( ( log ` %s ) ^ %s ) x. ( %s x. ( Lam ` %s ) ) ) e. CC' % (n, K, CHV(n), n))
    c = d('cxpcld', [d('nncnd', [nn_], '%s e. CC' % n), d('negcld', [sc[0]], '-u %s e. CC' % S_)], '( %s ^c -u %s ) e. CC' % (n, S_))
    return d('mulcld', [a, c], '%s e. CC' % LT(K, S_, n))


def gen_lscl():
    w = W('kd2lscl', 'The twisted series ` LSK ( K , S ) ` is a complex number on ` Re S = 1 + E ` ( ~ kdlsb convergence, ~ isumcl ).')
    A = LSH
    d = lambda ref, h, c: D(w, A, ref, h, c)
    kl = w.s([], 'id', '( %s -> %s )' % (A, A))
    kd = use(w, A, 'kdlsb', {}, kl)
    kc = split_imp(stmt('kdlsb'))[1]
    cvn = d('simpld', [kd], top_and(kc)[0])
    Fn = '( n e. NN |-> %s )' % LT('K', 'S', 'n'); Fm = '( m e. NN |-> %s )' % LT('K', 'S', 'm')
    ce = w.s([tcong(w, 'n', 'm', 'K', 'S')], 'cbvmptv', '%s = %s' % (Fn, Fm))
    cvm = d('mpbid', [cvn, w.s([w.s([w.s([ce, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (Fn, Fm))], 'eleq1i', '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (Fn, Fm))],
                              'a1i', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (A, Fn, Fm))],
              'seq 1 ( + , %s ) e. dom ~~>' % Fm)
    An = '( %s /\\ n e. NN )' % A
    nn_ = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    nxh = D(w, An, 'simp1d', [w.s([], 'simpl', '( %s -> %s )' % (An, A))], NXH)
    g3 = D(w, An, 'simp3d', [w.s([], 'simpl', '( %s -> %s )' % (An, A))], '( S e. CC /\\ ( Re ` S ) = ( 1 + E ) /\\ K e. NN0 )')
    sc = D(w, An, 'simp1d', [g3], 'S e. CC'); kn = D(w, An, 'simp3d', [g3], 'K e. NN0')
    tc_ = ltcc(w, An, 'n', nn_, nxh, (kn, 'K'), (sc, 'S'))
    mc = w.s([tcong(w, 'm', 'n', 'K', 'S')], 'adantl', '( ( %s /\\ m = n ) -> %s = %s )' % (An, LT('K', 'S', 'm'), LT('K', 'S', 'n')))
    fv = D(w, An, 'fvmptd', [a1(w, An, 'eqid', '%s = %s' % (Fm, Fm)), mc, nn_, tc_], '( %s ` n ) = %s' % (Fm, LT('K', 'S', 'n')))
    fin = d('isumcl', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, A, '1z', '1 e. ZZ'), fv, tc_, cvm], '%s e. CC' % LSK('K', 'S'))
    w.qed([fin], 'idi', S['kd2lscl'])
    return only_run(w, only)



def gen_lsb():
    w = W('kd2lsb', 'Lean ` KDerivDetect.norm_LSeries_ge_of_turan ` (section 4.4 step 3): the Turan floor ` Q ` of the ` 6 eta ` family, far zeros and Cauchy remainder each ` <_ Q / 8 ` , give ` (j+1)! ( 3 / 4 ) Q <_ abs LSK ( j + 1 , s0 ) ` ( ~ kdrep , ~ kdfar with ~ kdl2 , ~ kddist , ~ kdre1 ).')
    A0 = S['kd2lsb'].split(' -> ( ( ! `')[0][2:]
    H1 = '( T e. RR /\\ E e. RR+ /\\ E <_ %s )' % R120
    A1 = '( ( %s /\\ %s ) /\\ J e. NN0 )' % (CHI, H1)
    d1 = lambda ref, h, c: D(w, A1, ref, h, c)
    g1 = d1('simpl', [], '( %s /\\ %s )' % (CHI, H1))
    chi = d1('simpld', [g1], CHI); h1 = d1('simprd', [g1], H1)
    tr = d1('simp1d', [h1], 'T e. RR'); ep = d1('simp2d', [h1], 'E e. RR+'); e20 = d1('simp3d', [h1], 'E <_ %s' % R120)
    jn = d1('simpr', [], 'J e. NN0')
    er = d1('rpred', [ep], 'E e. RR')
    # ZD finite, orders NN
    lz = use(w, A1, 'lchrzc8', {}, d1('jca', [chi, tr], '( %s /\\ T e. RR )' % CHI))
    lzc = split_imp(stmt('lchrzc8'))[1]
    zfin = d1('simp1d', [lz], top_and(lzc)[0]); zord = d1('simp2d', [lz], top_and(lzc)[1])
    # element facts under ( A1 /\ q e. ZD )
    Aq = '( %s /\\ q e. %s )' % (A1, ZD())
    dq = lambda ref, h, c: D(w, Aq, ref, h, c)
    qz = w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, ZD()))
    zf = zfacts(w, Aq, 'q', qz, lift(w, chi, Aq), lift(w, tr, Aq), lift(w, ep, Aq))
    mun = dq('mpd', [qz, dq('syl', [lift(w, zord, Aq), w.inst('rsp')], '( q e. %s -> %s e. NN )' % (ZD(), MU()))], '%s e. NN' % MU())
    j2 = d1('nn0addcld', [jn, a1(w, A1, '2nn0', '2 e. NN0')], '( J + 2 ) e. NN0')
    fc = dq('divcld', [dq('nncnd', [mun], '%s e. CC' % MU()), dq('expcld', [zf['dzc'], lift(w, j2, Aq)], '( ( %s - q ) ^ ( J + 2 ) ) e. CC' % S0T),
                       dq('expne0d', [zf['dzc'], zf['ne'], dq('nn0zd', [lift(w, j2, Aq)], '( J + 2 ) e. ZZ')], '( ( %s - q ) ^ ( J + 2 ) ) =/= 0' % S0T)], '%s e. CC' % fterm('q'))
    # the split ZD = Z6x u. YF
    PH = '( abs ` ( x - %s ) ) <_ ( 6 x. E )' % ONET
    Z6x = '{ x e. %s | %s }' % (ZD(), PH)
    YF = '{ x e. %s | -. %s }' % (ZD(), PH)
    un = a1(w, A1, 'rabxm', '%s = ( %s u. %s )' % (ZD(), Z6x, YF))
    dj = a1(w, A1, 'rabnc', '( %s i^i %s ) = (/)' % (Z6x, YF))
    spl = d1('fsumsplit', [dj, un, zfin, fc], 'sum_ q e. %s %s = ( sum_ q e. %s %s + sum_ q e. %s %s )' % (ZD(), fterm('q'), Z6x, fterm('q'), YF, fterm('q')))
    # Z6x = Z6 (cbvrabv)
    xe = w.s([], 'oveq1', '( x = p -> ( x - %s ) = ( p - %s ) )' % (ONET, ONET))
    xe2 = w.s([xe], 'fveq2d', '( x = p -> ( abs ` ( x - %s ) ) = ( abs ` ( p - %s ) ) )' % (ONET, ONET))
    xe3 = w.s([xe2], 'breq1d', '( x = p -> ( %s <-> ( abs ` ( p - %s ) ) <_ ( 6 x. E ) ) )' % (PH, ONET))
    z6e = w.s([xe3], 'cbvrabv', '%s = %s' % (Z6x, Z6))
    s6 = d1('sumeq1d', [w.s([z6e], 'a1i', '( %s -> %s = %s )' % (A1, Z6x, Z6))], 'sum_ q e. %s %s = sum_ q e. %s %s' % (Z6x, fterm('q'), Z6, fterm('q')))
    SA = 'sum_ q e. %s %s' % (ZD(), fterm('q')); SN = 'sum_ q e. %s %s' % (Z6, fterm('q')); SY = 'sum_ q e. %s %s' % (YF, fterm('q'))
    spl2 = d1('eqtrd', [spl, d1('oveq1d', [s6], '( sum_ q e. %s %s + %s ) = ( %s + %s )' % (Z6x, fterm('q'), SY, SN, SY))], '%s = ( %s + %s )' % (SA, SN, SY))
    # kdrep at K = J + 1
    j1 = d1('syl', [jn, w.inst('peano2nn0')], '( J + 1 ) e. NN0')
    KDHs = d1('jca', [chi, d1('3jca', [tr, d1('jca', [ep, e20], '( E e. RR+ /\\ E <_ %s )' % R120), j1], '( T e. RR /\\ ( E e. RR+ /\\ E <_ %s ) /\\ ( J + 1 ) e. NN0 )' % R120)],
              '( %s /\\ ( T e. RR /\\ ( E e. RR+ /\\ E <_ %s ) /\\ ( J + 1 ) e. NN0 ) )' % (CHI, R120))
    rep = use(w, A1, 'kdrep', {'K': '( J + 1 )'}, KDHs)
    jc = d1('nn0cnd', [jn], 'J e. CC')
    kk = d1('eqtrd', [d1('addassd', [jc, a1(w, A1, 'ax-1cn', '1 e. CC'), a1(w, A1, 'ax-1cn', '1 e. CC')], '( ( J + 1 ) + 1 ) = ( J + ( 1 + 1 ) )'),
                      d1('oveq2d', [a1(w, A1, '1p1e2', '( 1 + 1 ) = 2')], '( J + ( 1 + 1 ) ) = ( J + 2 )')], '( ( J + 1 ) + 1 ) = ( J + 2 )')
    t1 = d1('oveq2d', [d1('oveq2d', [kk], '( ( %s - q ) ^ ( ( J + 1 ) + 1 ) ) = ( ( %s - q ) ^ ( J + 2 ) )' % (S0T, S0T))],
            '%s = %s' % (fterm('q', '( ( J + 1 ) + 1 )'), fterm('q')))
    SA1 = 'sum_ q e. %s %s' % (ZD(), fterm('q', '( ( J + 1 ) + 1 )'))
    t2 = d1('sumeq2sdv', [t1], '%s = %s' % (SA1, SA))
    LS = LSK('( J + 1 )', S0T)
    F = '( ! ` ( J + 1 ) )'
    t3 = d1('oveq1d', [t2], '( %s + ( %s / %s ) ) = ( %s + ( %s / %s ) )' % (SA1, LS, F, SA, LS, F))
    t4 = d1('oveq1d', [d1('eqtrd', [t3, d1('oveq1d', [spl2], '( %s + ( %s / %s ) ) = ( ( %s + %s ) + ( %s / %s ) )' % (SA, LS, F, SN, SY, LS, F))],
                          '( %s + ( %s / %s ) ) = ( ( %s + %s ) + ( %s / %s ) )' % (SA1, LS, F, SN, SY, LS, F))], 'T.') if False else None
    t5 = d1('eqtrd', [t3, d1('oveq1d', [spl2], '( %s + ( %s / %s ) ) = ( ( %s + %s ) + ( %s / %s ) )' % (SA, LS, F, SN, SY, LS, F))],
            '( %s + ( %s / %s ) ) = ( ( %s + %s ) + ( %s / %s ) )' % (SA1, LS, F, SN, SY, LS, F))
    rep2 = d1('eqbrtrrd' if False else 'breqtrd', [d1('fveq2d', [t5], '( abs ` ( %s + ( %s / %s ) ) ) = ( abs ` ( ( %s + %s ) + ( %s / %s ) ) )' % (SA1, LS, F, SN, SY, LS, F)), rep] if False else [rep, d1('fveq2d', [t5], '( abs ` ( %s + ( %s / %s ) ) ) = ( abs ` ( ( %s + %s ) + ( %s / %s ) ) )' % (SA1, LS, F, SN, SY, LS, F))],
               'T.') if False else None
    rep2 = d1('eqbrtrrd', [d1('fveq2d', [t5], '( abs ` ( %s + ( %s / %s ) ) ) = ( abs ` ( ( %s + %s ) + ( %s / %s ) ) )' % (SA1, LS, F, SN, SY, LS, F)), rep],
              '( abs ` ( ( %s + %s ) + ( %s / %s ) ) ) <_ %s' % (SN, SY, LS, F, CAU(KL)))
    # far zeros: kdfar on YF
    Ap = '( %s /\\ p e. %s )' % (A1, ZD())
    pz = w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, ZD()))
    zp = zfacts(w, Ap, 'p', pz, lift(w, chi, Ap), lift(w, tr, Ap), lift(w, ep, Ap))
    ral0 = d1('ralrimiva', [zp['g0']], 'A. p e. %s 0 < ( abs ` ( %s - p ) )' % (ZD(), S0T))
    s0c = zp['s0c']
    s0c1 = d1('addcld', [d1('recnd', [d1('readdcld', [a1(w, A1, '1re', '1 e. RR'), er], '( 1 + E ) e. RR')], '( 1 + E ) e. CC'),
                         d1('mulcld', [a1(w, A1, 'ax-icn', '_i e. CC'), d1('recnd', [tr], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % S0T)
    Ay = '( %s /\\ p e. %s )' % (A1, YF)
    dy = lambda ref, h, c: D(w, Ay, ref, h, c)
    py = w.s([], 'simpr', '( %s -> p e. %s )' % (Ay, YF))
    xe4 = w.s([xe3], 'notbid', '( x = p -> ( -. %s <-> -. ( abs ` ( p - %s ) ) <_ ( 6 x. E ) ) )' % (PH, ONET))
    ely = w.s([xe4], 'elrab', '( p e. %s <-> ( p e. %s /\\ -. ( abs ` ( p - %s ) ) <_ ( 6 x. E ) ) )' % (YF, ZD(), ONET))
    pyy = dy('sylib', [py, a1(w, Ay, None, None)] if False else [py, w.s([ely], 'a1i', '( %s -> ( p e. %s <-> ( p e. %s /\\ -. ( abs ` ( p - %s ) ) <_ ( 6 x. E ) ) ) )' % (Ay, YF, ZD(), ONET))],
             '( p e. %s /\\ -. ( abs ` ( p - %s ) ) <_ ( 6 x. E ) )' % (ZD(), ONET)) if False else \
        dy('mpbid', [py, w.s([ely], 'a1i', '( %s -> ( p e. %s <-> ( p e. %s /\\ -. ( abs ` ( p - %s ) ) <_ ( 6 x. E ) ) ) )' % (Ay, YF, ZD(), ONET))],
           '( p e. %s /\\ -. ( abs ` ( p - %s ) ) <_ ( 6 x. E ) )' % (ZD(), ONET))
    pyz = dy('simpld', [pyy], 'p e. %s' % ZD()); pyn = dy('simprd', [pyy], '-. ( abs ` ( p - %s ) ) <_ ( 6 x. E )' % ONET)
    zy = zfacts(w, Ay, 'p', pyz, lift(w, chi, Ay), lift(w, tr, Ay), lift(w, ep, Ay))
    ery = lift(w, er, Ay)
    ony = dy('addcld', [a1(w, Ay, 'ax-1cn', '1 e. CC'), dy('mulcld', [a1(w, Ay, 'ax-icn', '_i e. CC'), dy('recnd', [lift(w, tr, Ay)], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % ONET)
    abo = dy('abscld', [dy('subcld', [zy['zc'], ony], '( p - %s ) e. CC' % ONET)], '( abs ` ( p - %s ) ) e. RR' % ONET)
    e6r = dy('remulcld', [a1(w, Ay, '6re', '6 e. RR'), ery], '( 6 x. E ) e. RR')
    lt6 = dy('mpbird', [pyn, dy('ltnled', [e6r, abo], '( ( 6 x. E ) < ( abs ` ( p - %s ) ) <-> -. ( abs ` ( p - %s ) ) <_ ( 6 x. E ) )' % (ONET, ONET))],
             '( 6 x. E ) < ( abs ` ( p - %s ) )' % ONET)
    dist = use(w, Ay, 'kddist', {'Q': 'p'}, dy('jca', [dy('3jca', [ery, dy('rpge0d', [lift(w, ep, Ay)], '0 <_ E'), lift(w, tr, Ay)], '( E e. RR /\\ 0 <_ E /\\ T e. RR )'),
                                                         dy('jca', [zy['zc'], zy['re1']], '( p e. CC /\\ ( Re ` p ) <_ 1 )')],
                                                   '( ( E e. RR /\\ 0 <_ E /\\ T e. RR ) /\\ ( p e. CC /\\ ( Re ` p ) <_ 1 ) )'))
    lt6b = dy('ltletrd', [e6r, abo, dy('abscld', [zy['dzc']], '( abs ` ( %s - p ) ) e. RR' % S0T), lt6, dist], '( 6 x. E ) < ( abs ` ( %s - p ) )' % S0T)
    raly = d1('ralrimiva', [lt6b], 'A. p e. %s ( 6 x. E ) < ( abs ` ( %s - p ) )' % (YF, S0T))
    e6p = d1('rpmulcld', [a1(w, A1, '6rp' if False else 'idi', 'T.') if False else w.s([num.rp(w, '6')], 'a1i', '( %s -> 6 e. RR+ )' % A1), ep], '( 6 x. E ) e. RR+')
    yss = a1(w, A1, 'ssrab2', '%s C_ %s' % (YF, ZD()))
    # kdl2, renamed to binder p
    l2 = use(w, A1, 'kdl2', {}, d1('jca', [chi, d1('3jca', [tr, ep, e20], H1)], '( %s /\\ %s )' % (CHI, H1)))
    AA = '( ( 1 / E ) x. ( ( ( ( 5 / 4 ) / E ) + 5 ) + %s ) )' % KL
    qe1 = w.s([], 'oveq2', '( q = p -> ( %s holord q ) = ( %s holord p ) )' % (LFN, LFN))
    qe2 = w.s([w.s([], 'oveq2', '( q = p -> ( %s - q ) = ( %s - p ) )' % (S0T, S0T))], 'fveq2d', '( q = p -> ( abs ` ( %s - q ) ) = ( abs ` ( %s - p ) ) )' % (S0T, S0T))
    qe3 = w.s([qe2], 'oveq1d', '( q = p -> ( ( abs ` ( %s - q ) ) ^ 2 ) = ( ( abs ` ( %s - p ) ) ^ 2 ) )' % (S0T, S0T))
    qe4 = w.s([qe1, qe3], 'oveq12d', '( q = p -> ( %s / ( ( abs ` ( %s - q ) ) ^ 2 ) ) = ( %s / ( ( abs ` ( %s - p ) ) ^ 2 ) ) )' % (MU(), S0T, MU('p'), S0T))
    cb = w.s([qe4], 'cbvsumv', 'sum_ q e. %s ( %s / ( ( abs ` ( %s - q ) ) ^ 2 ) ) = sum_ p e. %s ( %s / ( ( abs ` ( %s - p ) ) ^ 2 ) )' % (ZD(), MU(), S0T, ZD(), MU('p'), S0T))
    l2p = d1('eqbrtrrd', [w.s([cb], 'a1i', '( %s -> sum_ q e. %s ( %s / ( ( abs ` ( %s - q ) ) ^ 2 ) ) = sum_ p e. %s ( %s / ( ( abs ` ( %s - p ) ) ^ 2 ) ) )' % (A1, ZD(), MU(), S0T, ZD(), MU('p'), S0T)), l2],
              'sum_ p e. %s ( %s / ( ( abs ` ( %s - p ) ) ^ 2 ) ) <_ %s' % (ZD(), MU('p'), S0T, AA))
    clA = Closure(w, A1, {'J': ('NN0', jn), 'E': ('RR+', ep), 'N': ('NN', d1('simpld', [d1('simpld', [chi], NXH)], 'N e. NN')), 'T': ('RR', tr)})
    at = d1('abscld', [d1('recnd', [tr], 'T e. CC')], '( abs ` T ) e. RR')
    t2p = d1('elrpd', [d1('readdcld', [at, a1(w, A1, '2re', '2 e. RR')], '( ( abs ` T ) + 2 ) e. RR'),
                       linarith(w, A1, [d1('absge0d', [d1('recnd', [tr], 'T e. CC')], '0 <_ ( abs ` T )')], '0 < ( ( abs ` T ) + 2 )', closure=Closure(w, A1, {'( abs ` T )': ('RR', at)}))],
              '( ( abs ` T ) + 2 ) e. RR+')
    lg = d1('relogcld', [d1('rpmulcld', [d1('nnrpd', [d1('simpld', [d1('simpld', [chi], NXH)], 'N e. NN')], 'N e. RR+'), t2p], '( N x. ( ( abs ` T ) + 2 ) ) e. RR+')], '%s e. RR' % LOGX)
    clA.leaf(LOGX, 'RR', lg)
    far = use(w, A1, 'kdfar', {'Y': YF, 'S': S0T, 'R': '( 6 x. E )', 'A': AA},
              d1('jca', [d1('3jca', [d1('jca', [chi, tr], '( %s /\\ T e. RR )' % CHI), d1('jca', [s0c1, ral0], '( %s e. CC /\\ A. p e. %s 0 < ( abs ` ( %s - p ) ) )' % (S0T, ZD(), S0T)),
                                     d1('3jca', [yss, e6p, raly], '( %s C_ %s /\\ ( 6 x. E ) e. RR+ /\\ A. p e. %s ( 6 x. E ) < ( abs ` ( %s - p ) ) )' % (YF, ZD(), YF, S0T))],
                         '( ( %s /\\ T e. RR ) /\\ ( %s e. CC /\\ A. p e. %s 0 < ( abs ` ( %s - p ) ) ) /\\ ( %s C_ %s /\\ ( 6 x. E ) e. RR+ /\\ A. p e. %s ( 6 x. E ) < ( abs ` ( %s - p ) ) ) )' % (CHI, S0T, ZD(), S0T, YF, ZD(), YF, S0T)),
                         d1('3jca', [jn, clA.mem(AA, 'RR'), l2p], '( J e. NN0 /\\ %s e. RR /\\ sum_ p e. %s ( %s / ( ( abs ` ( %s - p ) ) ^ 2 ) ) <_ %s )' % (AA, ZD(), MU('p'), S0T, AA))],
                 split_imp(__import__('c8lib').tsub(stmt('kdfar'), {'Y': YF, 'S': S0T, 'R': '( 6 x. E )', 'A': AA}))[0]))
    # memberships for the final arithmetic
    Aq6 = '( %s /\\ q e. %s )' % (A1, Z6)
    q6z = D(w, Aq6, 'sseldd', [a1(w, Aq6, 'ssrab2', '%s C_ %s' % (Z6, ZD())), w.s([], 'simpr', '( %s -> q e. %s )' % (Aq6, Z6))], 'q e. %s' % ZD())
    fcA = w.s([fc], 'ex', '( %s -> ( q e. %s -> %s e. CC ) )' % (A1, ZD(), fterm('q')))
    fc6 = D(w, Aq6, 'mpd', [q6z, lift(w, fcA, Aq6)], '%s e. CC' % fterm('q'))
    AqY = '( %s /\\ q e. %s )' % (A1, YF)
    qyz = D(w, AqY, 'sseldd', [a1(w, AqY, 'ssrab2', '%s C_ %s' % (YF, ZD())), w.s([], 'simpr', '( %s -> q e. %s )' % (AqY, YF))], 'q e. %s' % ZD())
    fcY = D(w, AqY, 'mpd', [qyz, lift(w, fcA, AqY)], '%s e. CC' % fterm('q'))
    snc = d1('fsumcl', [d1('ssfid', [zfin, a1(w, A1, 'ssrab2', '%s C_ %s' % (Z6, ZD()))], '%s e. Fin' % Z6), fc6], '%s e. CC' % SN)
    syc = d1('fsumcl', [d1('ssfid', [zfin, yss], '%s e. Fin' % YF), fcY], '%s e. CC' % SY)
    lsc = use(w, A1, 'kd2lscl', {'K': '( J + 1 )', 'S': S0T},
              d1('3jca', [d1('simpld', [chi], NXH), d1('jca', [ep, linarith(w, A1, [e20], 'E <_ 1', closure=Closure(w, A1, {'E': ('RR', er)}))], '( E e. RR+ /\\ E <_ 1 )'),
                          d1('3jca', [s0c1, d1('syl2anc', [d1('readdcld', [a1(w, A1, '1re', '1 e. RR'), er], '( 1 + E ) e. RR'), tr, w.inst('crre')], '( Re ` %s ) = ( 1 + E )' % S0T), j1],
                             '( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) /\\ ( J + 1 ) e. NN0 )' % (S0T, S0T))],
                 split_imp(__import__('c8lib').tsub(S['kd2lscl'], {'K': '( J + 1 )', 'S': S0T}))[0]))
    fnn = d1('faccld', [j1], '%s e. NN' % F)
    fcc = d1('nncnd', [fnn], '%s e. CC' % F); fne = d1('nnne0d', [fnn], '%s =/= 0' % F)
    C_ = '( %s / %s )' % (LS, F)
    cc_ = d1('divcld', [lsc, fcc, fne], '%s e. CC' % C_)
    clc = Closure(w, A1, {SN: ('CC', snc), SY: ('CC', syc), C_: ('CC', cc_)})
    for a in (SN, SY, C_):
        clc.atom(a)
    X1 = '( ( %s + %s ) + %s )' % (SN, SY, C_); X2 = '( %s + %s )' % (SY, C_)
    x1 = ringeq(w, A1, SN, '( %s - %s )' % (X1, X2), clc)
    x1c = clc.mem(X1, 'CC'); x2c = clc.mem(X2, 'CC')
    x2 = d1('breqtrd' if False else 'eqbrtrd', [d1('fveq2d', [x1], '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (SN, X1, X2)), d1('abs2dif2d', [x1c, x2c], '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (X1, X2, X1, X2))],
            '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (SN, X1, X2))
    x3 = d1('abstrid', [syc, cc_], '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (X2, SY, C_))
    fr = d1('nnred', [fnn], '%s e. RR' % F)
    x4 = d1('eqtrd', [d1('absdivd', [lsc, fcc, fne], '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (C_, LS, F)),
                      d1('oveq2d', [d1('absidd', [fr, d1('nn0ge0d', [d1('nnnn0d', [fnn], '%s e. NN0' % F)], '0 <_ %s' % F)], '( abs ` %s ) = %s' % (F, F))],
                         '( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / %s )' % (LS, F, LS, F))], '( abs ` %s ) = ( ( abs ` %s ) / %s )' % (C_, LS, F))
    # lift everything to A0
    a01 = w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (A0, CHI, H1)) if False else None
    g1_ = D(w, A0, 'simpl', [], '( %s /\\ %s )' % (CHI, H1))
    g2_ = D(w, A0, 'simpr', [], '( ( J e. NN0 /\\ Q e. RR ) /\\ ( Q <_ ( abs ` %s ) /\\ %s <_ ( Q / 8 ) /\\ %s <_ ( Q / 8 ) ) )' % (SN, FAR(KL), CAU(KL)))
    jq = D(w, A0, 'simpld', [g2_], '( J e. NN0 /\\ Q e. RR )')
    a1s = D(w, A0, 'jca', [g1_, D(w, A0, 'simpld', [jq], 'J e. NN0')], A1)
    L0 = lambda st: D(w, A0, 'syl', [a1s, st], formula_of(w, st).split(' -> ', 1)[1][:-2])
    qr = D(w, A0, 'simprd', [jq], 'Q e. RR')
    hs = D(w, A0, 'simprd', [g2_], '( Q <_ ( abs ` %s ) /\\ %s <_ ( Q / 8 ) /\\ %s <_ ( Q / 8 ) )' % (SN, FAR(KL), CAU(KL)))
    hq = D(w, A0, 'simp1d', [hs], 'Q <_ ( abs ` %s )' % SN); hf = D(w, A0, 'simp2d', [hs], '%s <_ ( Q / 8 )' % FAR(KL)); hc = D(w, A0, 'simp3d', [hs], '%s <_ ( Q / 8 )' % CAU(KL))
    atoms = {}
    def rr(E, st):
        atoms[E] = ('RR', L0(D(w, A1, 'abscld', [st], '( abs ` %s ) e. RR' % E[8:-2])) if st else None)
    cl0 = Closure(w, A0, {'Q': ('RR', qr)})
    for E, st in (('( abs ` %s )' % SN, snc), ('( abs ` %s )' % X1, x1c), ('( abs ` %s )' % X2, x2c), ('( abs ` %s )' % SY, syc), ('( abs ` %s )' % C_, cc_)):
        cl0.leaf(E, 'RR', L0(d1('abscld', [st], '%s e. RR' % E)))
    ALS = '( ( abs ` %s ) / %s )' % (LS, F)
    cl0.leaf(ALS, 'RR', L0(d1('rerpdivcld', [d1('abscld', [lsc], '( abs ` %s ) e. RR' % LS), d1('nnrpd', [fnn], '%s e. RR+' % F)], '%s e. RR' % ALS)))
    cl0.leaf(FAR(KL), 'RR', L0(clA.mem(FAR(KL), 'RR')))
    cl0.leaf(CAU(KL), 'RR', L0(clA.mem(CAU(KL), 'RR')))
    k1 = linarith(w, A0, [hq, hf, hc, L0(x2), L0(x3), L0(x4), L0(rep2), L0(far)], '( ( 3 / 4 ) x. Q ) <_ %s' % ALS, closure=cl0)
    fin = D(w, A0, 'mpbird', [k1, D(w, A0, 'lemuldiv2d', [cl0.mem('( ( 3 / 4 ) x. Q )', 'RR'), L0(d1('abscld', [lsc], '( abs ` %s ) e. RR' % LS)), L0(d1('nnrpd', [fnn], '%s e. RR+' % F))],
                                     '( ( %s x. ( ( 3 / 4 ) x. Q ) ) <_ ( abs ` %s ) <-> ( ( 3 / 4 ) x. Q ) <_ %s )' % (F, LS, ALS))],
            '( %s x. ( ( 3 / 4 ) x. Q ) ) <_ ( abs ` %s )' % (F, LS))
    w.qed([fin], 'idi', S['kd2lsb'])
    return only_run(w, only)


if __name__ == '__main__':
    gen_lscl()
    gen_lsb()

