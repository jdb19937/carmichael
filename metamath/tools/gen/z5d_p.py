"""Sortie Z5d, section P: I9(b), the lower bound for P ( 1 ) (Detection.lean 497-784)."""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5dlib import *
from cl import Closure, lift, split_imp
import lin
import num

HERE = os.path.dirname(os.path.abspath(__file__))
WSD = os.path.join(HERE, '..', '..', 'worksheets')


def z5dhk():
    """cophrm's chain up to the harmonic sum (worksheets/cophrm.mmp, V3), stopped before its log W step."""
    w = W('z5dhk', "The harmonic sum up to W is at most K / phi ( K ) times the harmonic sum over the integers up to W coprime to K "
                   "(V3's cophrm chain: the smooth/coprime split cof1, sumprodub, smsum, phipfprod), before its log W step; "
                   "Detection.lean's P1_lower_log reads it at W = |_ R.")
    src = open(os.path.join(WSD, 'cophrm.mmp')).read().split('\n')
    steps = [l for l in src if re.match(r'^(s|i)\d+:', l)]
    drop = set(['s%d' % i for i in range(150, 159)] + ['i151', 'i154'] + ['s%d' % i for i in range(349, 368)])
    keep = [l for l in steps if l.split(':', 1)[0] not in drop]
    for l in keep:
        refs = l.split(':')[1].split(',') if l.split(':')[1] else []
        assert not (set(refs) & drop), l[:80]
    w.lines = keep
    w.qed(['s343', 's347', 's348', 's149', 's346'], 'letrd', STATEMENTS['z5dhk'])
    return w


def z5dinvsq():
    w = W('z5dinvsq', "The inverse squares up to W sum to at most 2 (Lean sum_inv_sq_Icc_le): 1 / k ^ 2 <_ 2 / ( k ( k + 1 ) ) and "
                      "the telescoping series sums to 2 (set.mm's trirecip).")
    a = 'W e. NN0'
    st = mkst(w, a)
    FZ = '( 1 ... W )'
    fi = st([], 'fzfid', '%s e. Fin' % FZ)
    ak = '( %s /\\ k e. %s )' % (a, FZ)
    sk = mkst(w, ak)
    kn = sy(w, ak, sk([], 'simpr', 'k e. %s' % FZ), 'elfznn', 'k e. NN')
    kr = sk([kn], 'nnred', 'k e. RR')
    krp = sk([kn], 'nnrpd', 'k e. RR+')
    k1 = sk([kn], 'nnge1d', '1 <_ k')
    cl = Closure(w, ak, {'k': [('RR', kr), ('RR+', krp), ('NN', kn)]})
    A_ = '( k x. ( k + 1 ) )'; B_ = '( 2 x. ( k ^ 2 ) )'
    arp = cl.mem(A_, 'RR+'); brp = cl.mem(B_, 'RR+')
    ab = lin.nlinarith(w, ak, [k1], '%s <_ %s' % (A_, B_), closure=cl)
    le = sk([arp, brp, litr(w, ak, '2'), w.s([num.le_lit(w, '0', '2')], 'a1i', '( %s -> 0 <_ 2 )' % ak), ab], 'lediv2ad',
            '( 2 / %s ) <_ ( 2 / %s )' % (B_, A_))
    k2c = cl.mem('( k ^ 2 )', 'CC'); k2n = cl.ne0('( k ^ 2 )')
    dc = sk([sk([], '1cnd', '1 e. CC'), k2c, sk([], '2cnd', '2 e. CC'), k2n, w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % ak)],
            'divcan5d', '( ( 2 x. 1 ) / %s ) = ( 1 / ( k ^ 2 ) )' % B_)
    t1 = w.s([w.s([], '2t1e2', '( 2 x. 1 ) = 2')], 'a1i', '( %s -> ( 2 x. 1 ) = 2 )' % ak)
    dc2 = sk([sk([t1], 'oveq1d', '( ( 2 x. 1 ) / %s ) = ( 2 / %s )' % (B_, B_)), dc], 'eqtr3d', '( 2 / %s ) = ( 1 / ( k ^ 2 ) )' % B_)
    term = sk([dc2, le], 'eqbrtrrd', '( 1 / ( k ^ 2 ) ) <_ ( 2 / %s )' % A_)
    t2r = cl.mem('( 2 / %s )' % A_, 'RR'); t1r = cl.mem('( 1 / ( k ^ 2 ) )', 'RR')
    s1 = st([fi, t1r, t2r, term], 'fsumle', 'sum_ k e. %s ( 1 / ( k ^ 2 ) ) <_ sum_ k e. %s ( 2 / %s )' % (FZ, FZ, A_))
    # the series of 2 / ( k ( k + 1 ) ) converges (trireciplem, isermulc2)
    FN = '( n e. NN |-> ( 1 / ( n x. ( n + 1 ) ) ) )'
    GN = '( n e. NN |-> ( 2 / ( n x. ( n + 1 ) ) ) )'
    tl = w.s([w.s([], 'eqid', '%s = %s' % (FN, FN))], 'trireciplem', 'seq 1 ( + , %s ) ~~> 1' % FN)
    az = '( %s /\\ k e. NN )' % a
    sz = mkst(w, az)
    zn = sz([], 'simpr', 'k e. NN')
    clz = Closure(w, az, {'k': [('NN', zn), ('RR+', sz([zn], 'nnrpd', 'k e. RR+'))]})
    fv, _ = mpv(w, az, 'n', 'NN', '( 1 / ( n x. ( n + 1 ) ) )', 'k', zn)
    gv, _ = mpv(w, az, 'n', 'NN', '( 2 / ( n x. ( n + 1 ) ) )', 'k', zn)
    fcc = sz([fv, clz.mem('( 1 / %s )' % A_, 'CC')], 'eqeltrd', '( %s ` k ) e. CC' % FN)
    dr = sz([clz.mem('2', 'CC'), clz.mem(A_, 'CC'), clz.ne0(A_)], 'divrecd', '( 2 / %s ) = ( 2 x. ( 1 / %s ) )' % (A_, A_))
    g7 = sz([gv, sz([dr, sz([fv], 'oveq2d', '( 2 x. ( %s ` k ) ) = ( 2 x. ( 1 / %s ) )' % (FN, A_))], 'eqtr4d',
                    '( 2 / %s ) = ( 2 x. ( %s ` k ) )' % (A_, FN))], 'eqtrd', '( %s ` k ) = ( 2 x. ( %s ` k ) )' % (GN, FN))
    nuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = st([], '1zzd', '1 e. ZZ')
    cv = w.s([nuz, one, st([], '2cnd', '2 e. CC'), a1(w, a, tl, 'seq 1 ( + , %s ) ~~> 1' % FN), fcc, g7], 'isermulc2',
             '( %s -> seq 1 ( + , %s ) ~~> ( 2 x. 1 ) )' % (a, GN))
    dm = st([a1(w, a, w.s([], 'climrel', 'Rel ~~>'), 'Rel ~~>'), cv], 'jca',
            '( Rel ~~> /\\ seq 1 ( + , %s ) ~~> ( 2 x. 1 ) )' % GN)
    dm2 = st([dm, w.inst('releldm')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % GN)
    # isumless
    ss = a1(w, a, w.s([], 'fz1ssnn', '%s C_ NN' % FZ), '%s C_ NN' % FZ)
    gv2 = gv
    gre = clz.mem('( 2 / %s )' % A_, 'RR'); gge = clz.ge0('( 2 / %s )' % A_)
    il = w.s([nuz, one, fi, ss, gv2, gre, gge, dm2], 'isumless', '( %s -> sum_ k e. %s ( 2 / %s ) <_ sum_ k e. NN ( 2 / %s ) )' % (a, FZ, A_, A_))
    tr = a1(w, a, w.s([], 'trirecip', 'sum_ k e. NN ( 2 / %s ) = 2' % A_), 'sum_ k e. NN ( 2 / %s ) = 2' % A_)
    s2 = st([il, tr], 'breqtrd', 'sum_ k e. %s ( 2 / %s ) <_ 2' % (FZ, A_))
    s1r = st([fi, t1r], 'fsumrecl', 'sum_ k e. %s ( 1 / ( k ^ 2 ) ) e. RR' % FZ)
    s2r = st([fi, t2r], 'fsumrecl', 'sum_ k e. %s ( 2 / %s ) e. RR' % (FZ, A_))
    w.qed([s1r, s2r, litr(w, a, '2'), s1, s2], 'letrd', STATEMENTS['z5dinvsq'])
    return w


def elrabk(w, X, cond, var, setA, T_):
    """closed: ( X e. { var e. setA | cond(var) } <-> ( X e. setA /\\ cond(X) ) ) where cond is ( var ^ 2 ) || T_"""
    c1 = w.s([], 'oveq1', '( %s = %s -> ( %s ^ 2 ) = ( %s ^ 2 ) )' % (var, X, var, X))
    c2 = w.s([c1], 'breq1d', '( %s = %s -> ( ( %s ^ 2 ) || %s <-> ( %s ^ 2 ) || %s ) )' % (var, X, var, T_, X, T_))
    return w.s([c2], 'elrab', '( %s e. { %s e. %s | ( %s ^ 2 ) || %s } <-> ( %s e. %s /\\ ( %s ^ 2 ) || %s ) )'
               % (X, var, setA, var, T_, X, setA, X, T_))


def z5dsqp():
    w = W('z5dsqp', "Every positive integer T is K ^ 2 times a squarefree number, for K the largest integer whose square divides T "
                    "(Lean Nat.sq_mul_squarefree, used through choose in sum_inv_Icc_le_sq_mul_squarefree): if p ^ 2 divided "
                    "T / K ^ 2, then ( K p ) ^ 2 would divide T.")
    a = 'T e. NN'
    st = mkst(w, a)
    SA = '{ k e. NN | ( k ^ 2 ) || T }'
    K = 'sup ( %s , RR , < )' % SA
    tn = st([], 'id', 'T e. NN')
    tz = st([tn], 'nnzd', 'T e. ZZ')
    # A C_ ( 1 ... T )
    akn = '( %s /\\ k e. NN )' % a
    sk = mkst(w, akn)
    kn = sk([], 'simpr', 'k e. NN')
    ak2 = '( %s /\\ ( k ^ 2 ) || T )' % akn
    s2 = mkst(w, ak2)
    kn2 = s2([], 'simplr', 'k e. NN')
    k2z = s2([s2([kn2], 'nnzd', 'k e. ZZ'), a1(w, ak2, w.s([], '2nn0', '2 e. NN0'), '2 e. NN0')], 'zexpcld', '( k ^ 2 ) e. ZZ')
    tn2 = s2([], 'simpll', 'T e. NN')
    k2t = s2([s2([], 'simpr', '( k ^ 2 ) || T'), s2([k2z, tn2, w.inst('dvdsle')], 'syl2anc', '( ( k ^ 2 ) || T -> ( k ^ 2 ) <_ T )')], 'mpd', '( k ^ 2 ) <_ T')
    kk2 = sy(w, ak2, kn2, 'nnlesq', 'k <_ ( k ^ 2 )')
    kr2 = s2([kn2], 'nnred', 'k e. RR')
    kt = s2([kr2, s2([k2z], 'zred', '( k ^ 2 ) e. RR'), s2([tn2], 'nnred', 'T e. RR'), kk2, k2t], 'letrd', 'k <_ T')
    fz = s2([s2([kn2, kt], 'jca', '( k e. NN /\\ k <_ T )'), s2([s2([tn2], 'nnzd', 'T e. ZZ'), w.inst('fznn')], 'syl', '( k e. ( 1 ... T ) <-> ( k e. NN /\\ k <_ T ) )')],
            'mpbird', 'k e. ( 1 ... T )')
    imp = w.s([fz], 'ex', '( %s -> ( ( k ^ 2 ) || T -> k e. ( 1 ... T ) ) )' % akn)
    ral = st([imp], 'ralrimiva', 'A. k e. NN ( ( k ^ 2 ) || T -> k e. ( 1 ... T ) )')
    sub = st([ral, w.s([], 'rabss', '( %s C_ ( 1 ... T ) <-> A. k e. NN ( ( k ^ 2 ) || T -> k e. ( 1 ... T ) ) )' % SA)], 'sylibr', '%s C_ ( 1 ... T )' % SA)
    fin = st([st([], 'fzfid', '( 1 ... T ) e. Fin'), sub], 'ssfid', '%s e. Fin' % SA)
    # 1 e. A
    e1 = elrabk(w, '1', None, 'k', 'NN', 'T')
    one = st([a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN'),
              st([a1(w, a, w.s([], 'sq1', '( 1 ^ 2 ) = 1'), '( 1 ^ 2 ) = 1'), sy(w, a, tz, '1dvds', '1 || T')], 'eqbrtrd', '( 1 ^ 2 ) || T'),
              a1(w, a, e1, '( 1 e. %s <-> ( 1 e. NN /\\ ( 1 ^ 2 ) || T ) )' % SA)], 'mpbir2and', '1 e. %s' % SA)
    ne = sy(w, a, one, 'ne0i', '%s =/= (/)' % SA)
    ssr = a1(w, a, w.s([w.s([], 'ssrab2', '%s C_ NN' % SA), w.s([], 'nnssre', 'NN C_ RR')], 'sstri', '%s C_ RR' % SA), '%s C_ RR' % SA)
    so = a1(w, a, w.s([], 'ltso', '< Or RR'), '< Or RR')
    kin = st([so, st([fin, ne, ssr], '3jca', '( %s e. Fin /\\ %s =/= (/) /\\ %s C_ RR )' % (SA, SA, SA)), w.inst('fisupcl')], 'syl2anc', '%s e. %s' % (K, SA))
    SAJ = '{ j e. NN | ( j ^ 2 ) || T }'
    cj = w.s([w.s([w.s([], 'oveq1', '( k = j -> ( k ^ 2 ) = ( j ^ 2 ) )')], 'breq1d', '( k = j -> ( ( k ^ 2 ) || T <-> ( j ^ 2 ) || T ) )')],
             'cbvrabv', '%s = %s' % (SA, SAJ))
    kinj = st([kin, a1(w, a, cj, '%s = %s' % (SA, SAJ))], 'eleqtrd', '%s e. %s' % (K, SAJ))
    eK = a1(w, a, elrabk(w, K, None, 'j', 'NN', 'T'), '( %s e. %s <-> ( %s e. NN /\\ ( %s ^ 2 ) || T ) )' % (K, SAJ, K, K))
    kp = st([kinj, eK], 'mpbid', '( %s e. NN /\\ ( %s ^ 2 ) || T )' % (K, K))
    Kn = st([kp], 'simpld', '%s e. NN' % K)
    Kd = st([kp], 'simprd', '( %s ^ 2 ) || T' % K)
    bnd = st([ssr, fin, w.inst('fimaxre2')], 'syl2anc', 'E. x e. RR A. y e. %s y <_ x' % SA)
    K2 = '( %s ^ 2 )' % K
    K2n = st([Kn], 'nnsqcld', '%s e. NN' % K2)
    Q = '( T / %s )' % K2
    qn = st([Kd, st([tn, K2n, w.inst('nndivdvds')], 'syl2anc', '( %s || T <-> %s e. NN )' % (K2, Q))], 'mpbid', '%s e. NN' % Q)
    # no prime square divides Q
    ap = '( %s /\\ p e. Prime )' % a
    c = '( %s /\\ ( p ^ 2 ) || %s )' % (ap, Q)
    sc = mkst(w, c)
    lf = lambda s_: lift(w, s_, c)
    pp = sc([], 'simplr', 'p e. Prime')
    pn = sy(w, c, pp, 'prmnn', 'p e. NN')
    p2 = sy(w, c, sy(w, c, pp, 'prmuz2', 'p e. ( ZZ>= ` 2 )'), 'eluzle', '2 <_ p')
    Knc = lf(Kn)
    cl = Closure(w, c, {'p': [('NN', pn)], K: [('NN', Knc)], K2: [('NN', lf(K2n))], 'T': [('NN', lf(tn))], Q: [('NN', lf(qn))]})
    cl.atom(K); cl.atom(Q)
    p2z = cl.mem('( p ^ 2 )', 'ZZ'); qz = cl.mem(Q, 'ZZ'); K2z = cl.mem(K2, 'ZZ')
    dm = sc([sc([], 'simpr', '( p ^ 2 ) || %s' % Q), sc([p2z, qz, K2z, w.inst('dvdscmul')], 'syl3anc',
                                                      '( ( p ^ 2 ) || %s -> ( %s x. ( p ^ 2 ) ) || ( %s x. %s ) )' % (Q, K2, K2, Q))], 'mpd',
            '( %s x. ( p ^ 2 ) ) || ( %s x. %s )' % (K2, K2, Q))
    dc = sc([cl.mem('T', 'CC'), cl.mem(K2, 'CC'), cl.ne0(K2)], 'divcan2d', '( %s x. %s ) = T' % (K2, Q))
    KP = '( %s x. p )' % K
    sq = sc([cl.mem(K, 'CC'), cl.mem('p', 'CC')], 'sqmuld', '( %s ^ 2 ) = ( %s x. ( p ^ 2 ) )' % (KP, K2))
    kpd = sc([sq, sc([dm, dc], 'breqtrd', '( %s x. ( p ^ 2 ) ) || T' % K2)], 'eqbrtrd', '( %s ^ 2 ) || T' % KP)
    kpn = sc([Knc, pn], 'nnmulcld', '%s e. NN' % KP); cl.have(KP, 'NN', kpn)
    ekp = a1(w, c, elrabk(w, KP, None, 'j', 'NN', 'T'), '( %s e. %s <-> ( %s e. NN /\\ ( %s ^ 2 ) || T ) )' % (KP, SAJ, KP, KP))
    kpin = sc([sc([kpn, kpd, ekp], 'mpbir2and', '%s e. %s' % (KP, SAJ)), a1(w, c, cj, '%s = %s' % (SA, SAJ))], 'eleqtrrd', '%s e. %s' % (KP, SA))
    ub = sc([sc([lf(ssr), lf(ne), lf(bnd)], '3jca', '( %s C_ RR /\\ %s =/= (/) /\\ E. x e. RR A. y e. %s y <_ x )' % (SA, SA, SA)), kpin, w.inst('suprub')],
            'syl2anc', '%s <_ %s' % (KP, K))
    k1 = sc([Knc], 'nnge1d', '1 <_ %s' % K)
    p1 = sy(w, c, pp, 'prmgt1', '1 < p')
    lt = sc([p1, sc([cl.mem('p', 'RR'), cl.mem(K, 'RR+')], 'ltmulgt11d', '( 1 < p <-> %s < %s )' % (K, KP))], 'mpbid', '%s < %s' % (K, KP))
    nlt = sc([ub, sc([cl.mem(KP, 'RR'), cl.mem(K, 'RR')], 'lenltd', '( %s <_ %s <-> -. %s < %s )' % (KP, K, K, KP))], 'mpbid', '-. %s < %s' % (K, KP))
    nd = w.s([lt, nlt], 'pm2.65da', '( %s -> -. ( p ^ 2 ) || %s )' % (ap, Q))
    ra = st([nd], 'ralrimiva', 'A. p e. Prime -. ( p ^ 2 ) || %s' % Q)
    ne2 = st([ra, w.s([], 'ralnex', '( A. p e. Prime -. ( p ^ 2 ) || %s <-> -. E. p e. Prime ( p ^ 2 ) || %s )' % (Q, Q))], 'sylib',
             '-. E. p e. Prime ( p ^ 2 ) || %s' % Q)
    mz = st([ne2, sy(w, a, qn, 'isnsqf', '( ( mmu ` %s ) = 0 <-> E. p e. Prime ( p ^ 2 ) || %s )' % (Q, Q))], 'mtbird', '-. ( mmu ` %s ) = 0' % Q)
    mn = st([mz], 'neqned', '( mmu ` %s ) =/= 0' % Q)
    w.qed([st([Kn, Kd], 'jca', '( %s e. NN /\\ %s || T )' % (K, K2)), mn], 'jca', STATEMENTS['z5dsqp'])
    return w


def kscong(w, ante, t, s, eq):
    """( ante -> KS(t) = KS(s) ) from eq: ( ante -> t = s )"""
    b = w.s([eq], 'breq2d', '( %s -> ( ( k ^ 2 ) || %s <-> ( k ^ 2 ) || %s ) )' % (ante, t, s))
    r = w.s([b], 'rabbidv', '( %s -> { k e. NN | ( k ^ 2 ) || %s } = { k e. NN | ( k ^ 2 ) || %s } )' % (ante, t, s))
    return w.s([r], 'supeq1d', '( %s -> %s = %s )' % (ante, KS(t), KS(s)))


def splitfacts(w, a, v, U, kst, wst, K='K', Wv='W'):
    """under ante = ( a /\\ v e. U ), U = CS(K,W): the facts of the square split of v"""
    an = '( %s /\\ %s e. %s )' % (a, v, U)
    s = mkst(w, an)
    vin = s([], 'simpr', '%s e. %s' % (v, U))
    FZ = '( 1 ... %s )' % Wv
    vfz = s([vin, w.inst('elrabi')], 'syl', '%s e. %s' % (v, FZ))
    vn = sy(w, an, vfz, 'elfznn', '%s e. NN' % v)
    ex = w.s([w.s([w.s([], 'oveq1', '( x = %s -> ( x gcd %s ) = ( %s gcd %s ) )' % (v, K, v, K))], 'eqeq1d',
                  '( x = %s -> ( ( x gcd %s ) = 1 <-> ( %s gcd %s ) = 1 ) )' % (v, K, v, K))], 'elrab',
             '( %s e. %s <-> ( %s e. %s /\\ ( %s gcd %s ) = 1 ) )' % (v, U, v, FZ, v, K))
    vco = s([s([vin, a1(w, an, ex, '( %s e. %s <-> ( %s e. %s /\\ ( %s gcd %s ) = 1 ) )' % (v, U, v, FZ, v, K))], 'mpbid',
               '( %s e. %s /\\ ( %s gcd %s ) = 1 )' % (v, FZ, v, K))], 'simprd', '( %s gcd %s ) = 1' % (v, K))
    Kv = KS(v); K2 = '( %s ^ 2 )' % Kv; Q = '( %s / %s )' % (v, K2)
    sq = sy(w, an, vn, 'z5dsqp', '( ( %s e. NN /\\ %s || %s ) /\\ ( mmu ` %s ) =/= 0 )' % (Kv, K2, v, Q))
    kn = s([s([sq], 'simpld', '( %s e. NN /\\ %s || %s )' % (Kv, K2, v))], 'simpld', '%s e. NN' % Kv)
    kd = s([s([sq], 'simpld', '( %s e. NN /\\ %s || %s )' % (Kv, K2, v))], 'simprd', '%s || %s' % (K2, v))
    mu = s([sq], 'simprd', '( mmu ` %s ) =/= 0' % Q)
    k2n = s([kn], 'nnsqcld', '%s e. NN' % K2)
    qn = s([kd, s([vn, k2n, w.inst('nndivdvds')], 'syl2anc', '( %s || %s <-> %s e. NN )' % (K2, v, Q))], 'mpbid', '%s e. NN' % Q)
    wn = w.s([wst], 'adantr', '( %s -> %s e. NN )' % (an, Wv))
    wz = s([wn], 'nnzd', '%s e. ZZ' % Wv)
    vle = s([vfz, s([wz, w.inst('fznn')], 'syl', '( %s e. %s <-> ( %s e. NN /\\ %s <_ %s ) )' % (v, FZ, v, v, Wv))], 'mpbid', '( %s e. NN /\\ %s <_ %s )' % (v, v, Wv))
    vw = s([vle], 'simprd', '%s <_ %s' % (v, Wv))
    # KS <_ KS ^ 2 <_ v <_ W
    k2v = s([kd, s([s([k2n], 'nnzd', '%s e. ZZ' % K2), vn, w.inst('dvdsle')], 'syl2anc', '( %s || %s -> %s <_ %s )' % (K2, v, K2, v))], 'mpd', '%s <_ %s' % (K2, v))
    kk2 = sy(w, an, kn, 'nnlesq', '%s <_ %s' % (Kv, K2))
    vr = s([vn], 'nnred', '%s e. RR' % v); wr = s([wn], 'nnred', '%s e. RR' % Wv)
    kw = s([s([kn], 'nnred', '%s e. RR' % Kv), s([vn], 'nnred', '%s e. RR' % v), wr,
            s([s([kn], 'nnred', '%s e. RR' % Kv), s([k2n], 'nnred', '%s e. RR' % K2), vr, kk2, k2v], 'letrd', '%s <_ %s' % (Kv, v)), vw], 'letrd', '%s <_ %s' % (Kv, Wv))
    kfz = s([s([kn, kw], 'jca', '( %s e. NN /\\ %s <_ %s )' % (Kv, Kv, Wv)), s([wz, w.inst('fznn')], 'syl', '( %s e. %s <-> ( %s e. NN /\\ %s <_ %s ) )' % (Kv, FZ, Kv, Kv, Wv))],
            'mpbird', '%s e. %s' % (Kv, FZ))
    # K2 x. Q = v, Q || v, Q <_ W, ( Q gcd K ) = 1
    k2c = s([k2n], 'nncnd', '%s e. CC' % K2)
    dc = s([s([vn], 'nncnd', '%s e. CC' % v), k2c, s([k2n], 'nnne0d', '%s =/= 0' % K2)], 'divcan2d', '( %s x. %s ) = %s' % (K2, Q, v))
    qz = s([qn], 'nnzd', '%s e. ZZ' % Q)
    qd = s([s([s([k2n], 'nnzd', '%s e. ZZ' % K2), qz, w.inst('dvdsmul2')], 'syl2anc', '%s || ( %s x. %s )' % (Q, K2, Q)), dc], 'breqtrd', '%s || %s' % (Q, v))
    qv = s([qd, s([qz, vn, w.inst('dvdsle')], 'syl2anc', '( %s || %s -> %s <_ %s )' % (Q, v, Q, v))], 'mpd', '%s <_ %s' % (Q, v))
    qw = s([s([qn], 'nnred', '%s e. RR' % Q), vr, wr, qv, vw], 'letrd', '%s <_ %s' % (Q, Wv))
    kz = w.s([kst], 'adantr', '( %s -> %s e. NN )' % (an, K))
    kzz = s([kz], 'nnzd', '%s e. ZZ' % K)
    kv1 = s([s([s([vn], 'nnzd', '%s e. ZZ' % v), kzz, w.inst('gcdcom')], 'syl2anc', '( %s gcd %s ) = ( %s gcd %s )' % (v, K, K, v)), vco], 'eqtr3d', '( %s gcd %s ) = 1' % (K, v))
    rp = s([s([kzz, qz, s([vn], 'nnzd', '%s e. ZZ' % v)], '3jca', '( %s e. ZZ /\\ %s e. ZZ /\\ %s e. ZZ )' % (K, Q, v)),
            s([kv1, qd], 'jca', '( ( %s gcd %s ) = 1 /\\ %s || %s )' % (K, v, Q, v)), w.inst('rpdvds')], 'syl2anc', '( %s gcd %s ) = 1' % (K, Q))
    qk = s([s([kzz, qz, w.inst('gcdcom')], 'syl2anc', '( %s gcd %s ) = ( %s gcd %s )' % (K, Q, Q, K)), rp], 'eqtr3d', '( %s gcd %s ) = 1' % (Q, K))
    flw = sy(w, an, wz, 'flid', '( |_ ` %s ) = %s' % (Wv, Wv))
    qfz = s([s([qn, qw], 'jca', '( %s e. NN /\\ %s <_ %s )' % (Q, Q, Wv)), s([wz, w.inst('fznn')], 'syl', '( %s e. %s <-> ( %s e. NN /\\ %s <_ %s ) )' % (Q, FZ, Q, Q, Wv))],
            'mpbird', '%s e. %s' % (Q, FZ))
    qfz2 = s([qfz, s([flw], 'oveq2d', '( 1 ... ( |_ ` %s ) ) = %s' % (Wv, FZ))], 'eleqtrrd', '%s e. ( 1 ... ( |_ ` %s ) )' % (Q, Wv))
    RS = '( %s RSet %s )' % (K, Wv)
    el = s([kz, wn, w.inst('z5elrset')], 'syl2anc', '( %s e. %s <-> ( %s e. ( 1 ... ( |_ ` %s ) ) /\\ ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd %s ) = 1 ) ) )'
           % (Q, RS, Q, Wv, Q, Q, K))
    qrs = s([qfz2, s([mu, qk], 'jca', '( ( mmu ` %s ) =/= 0 /\\ ( %s gcd %s ) = 1 )' % (Q, Q, K)), el], 'mpbir2and', '%s e. %s' % (Q, RS))
    return dict(an=an, vn=vn, kn=kn, k2n=k2n, qn=qn, kfz=kfz, qrs=qrs, dc=dc, Kv=Kv, K2=K2, Q=Q)


def z5dcs2():
    w = W('z5dcs2', "The harmonic sum over the integers up to W coprime to K is at most twice P ( 1 ) = sum over the squarefree "
                    "r <_ W coprime to K of 1 / r (Lean sum_inv_Icc_le_sq_mul_squarefree with sum_le_mul_sum_of_split, read on the "
                    "coprime integers): t = K ( t ) ^ 2 ( t / K ( t ) ^ 2 ) with the cofactor squarefree and coprime, an injection "
                    "into ( 1 ... W ) X. RSet, V3's sumprodub, and sum 1 / k ^ 2 <_ 2.")
    a = '( K e. NN /\\ W e. NN )'
    st = mkst(w, a)
    U = CS('K', 'W'); S = '( 1 ... W )'; T = '( K RSet W )'
    kn = st([], 'simpl', 'K e. NN'); wn = st([], 'simpr', 'W e. NN')
    Ft = '<. %s , ( t / ( %s ^ 2 ) ) >.' % (KS('t'), KS('t'))
    Fs = '<. %s , ( s / ( %s ^ 2 ) ) >.' % (KS('s'), KS('s'))
    F = '( t e. %s |-> %s )' % (U, Ft)
    G = '( o e. %s |-> ( 1 / ( o ^ 2 ) ) )' % S
    H = '( f e. %s |-> ( 1 / f ) )' % T
    fz = st([], 'fzfid', '%s e. Fin' % S)
    ufin = st([fz, a1(w, a, w.s([], 'ssrab2', '%s C_ %s' % (U, S)), '%s C_ %s' % (U, S))], 'ssfid', '%s e. Fin' % U)
    rsf = st([kn, wn, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` W ) ) /\\ %s e. Fin )' % (T, T))
    tfin = st([rsf], 'simprd', '%s e. Fin' % T)
    tss = st([rsf], 'simpld', '%s C_ ( 1 ... ( |_ ` W ) )' % T)
    # G, H into [0,+oo)
    ao = '( %s /\\ o e. %s )' % (a, S)
    so = mkst(w, ao)
    on = sy(w, ao, so([], 'simpr', 'o e. %s' % S), 'elfznn', 'o e. NN')
    clo_ = Closure(w, ao, {'o': [('NN', on)]})
    g0 = so([clo_.mem('( 1 / ( o ^ 2 ) )', 'RR'), clo_.ge0('( 1 / ( o ^ 2 ) )'), a1(w, ao, w.s([], 'elrege0', '( ( 1 / ( o ^ 2 ) ) e. ( 0 [,) +oo ) <-> ( ( 1 / ( o ^ 2 ) ) e. RR /\\ 0 <_ ( 1 / ( o ^ 2 ) ) ) )'),
                                                                             '( ( 1 / ( o ^ 2 ) ) e. ( 0 [,) +oo ) <-> ( ( 1 / ( o ^ 2 ) ) e. RR /\\ 0 <_ ( 1 / ( o ^ 2 ) ) ) )')],
            'mpbir2and', '( 1 / ( o ^ 2 ) ) e. ( 0 [,) +oo )')
    gf = st([g0], 'fmpttd', '%s : %s --> ( 0 [,) +oo )' % (G, S))
    af = '( %s /\\ f e. %s )' % (a, T)
    sf = mkst(w, af)
    fn_ = sy(w, af, sf([lift(w, tss, af), sf([], 'simpr', 'f e. %s' % T)], 'sseldd', 'f e. ( 1 ... ( |_ ` W ) )'), 'elfznn', 'f e. NN')
    clf = Closure(w, af, {'f': [('NN', fn_)]})
    h0 = sf([clf.mem('( 1 / f )', 'RR'), clf.ge0('( 1 / f )'), a1(w, af, w.s([], 'elrege0', '( ( 1 / f ) e. ( 0 [,) +oo ) <-> ( ( 1 / f ) e. RR /\\ 0 <_ ( 1 / f ) ) )'),
                                                                     '( ( 1 / f ) e. ( 0 [,) +oo ) <-> ( ( 1 / f ) e. RR /\\ 0 <_ ( 1 / f ) ) )')],
            'mpbir2and', '( 1 / f ) e. ( 0 [,) +oo )')
    hf = st([h0], 'fmpttd', '%s : %s --> ( 0 [,) +oo )' % (H, T))
    # F is injective into S X. T
    ft = splitfacts(w, a, 't', U, kn, wn)
    atn = ft['an']
    mem = w.s([ft['kfz'], ft['qrs'], w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( %s X. %s ) )' % (atn, Ft, S, T))
    ra1 = st([mem], 'ralrimiva', 'A. t e. %s %s e. ( %s X. %s )' % (U, Ft, S, T))
    ats = '( %s /\\ s e. %s )' % (atn, U)
    atn0 = '( %s /\\ t e. %s )' % (a, U)
    fs = splitfacts(w, atn0, 's', U, w.s([kn], 'adantr', '( %s -> K e. NN )' % atn0), w.s([wn], 'adantr', '( %s -> W e. NN )' % atn0))
    ae = '( %s /\\ %s = %s )' % (ats, Ft, Fs)
    se = mkst(w, ae)
    KT = KS('t'); KSs = KS('s')
    ov1 = w.s([], 'ovex', '( t / ( %s ^ 2 ) ) e. _V' % KT)
    op = w.s([w.s([], 'supex', '%s e. _V' % KT), ov1], 'opth', '( %s = %s <-> ( %s = %s /\\ ( t / ( %s ^ 2 ) ) = ( s / ( %s ^ 2 ) ) ) )' % (Ft, Fs, KT, KSs, KT, KSs))
    pe = se([se([], 'simpr', '%s = %s' % (Ft, Fs)), a1(w, ae, op, '( %s = %s <-> ( %s = %s /\\ ( t / ( %s ^ 2 ) ) = ( s / ( %s ^ 2 ) ) ) )' % (Ft, Fs, KT, KSs, KT, KSs))], 'mpbid',
            '( %s = %s /\\ ( t / ( %s ^ 2 ) ) = ( s / ( %s ^ 2 ) ) )' % (KT, KSs, KT, KSs))
    e1 = se([pe], 'simpld', '%s = %s' % (KT, KSs)); e2 = se([pe], 'simprd', '( t / ( %s ^ 2 ) ) = ( s / ( %s ^ 2 ) )' % (KT, KSs))
    e12 = se([se([e1], 'oveq1d', '( %s ^ 2 ) = ( %s ^ 2 )' % (KT, KSs)), e2], 'oveq12d', '( ( %s ^ 2 ) x. ( t / ( %s ^ 2 ) ) ) = ( ( %s ^ 2 ) x. ( s / ( %s ^ 2 ) ) )' % (KT, KT, KSs, KSs))
    dct = lift(w, w.s([ft['dc']], 'adantr', '( %s -> ( ( %s ^ 2 ) x. ( t / ( %s ^ 2 ) ) ) = t )' % (ats, KT, KT)), ae)
    dcs = lift(w, fs['dc'], ae)
    ts = se([se([dct, e12], 'eqtr3d', 't = ( ( %s ^ 2 ) x. ( s / ( %s ^ 2 ) ) )' % (KSs, KSs)), dcs], 'eqtrd', 't = s')
    inj = w.s([ts], 'ex', '( %s -> ( %s = %s -> t = s ) )' % (ats, Ft, Fs))
    ra2 = st([w.s([inj], 'ralrimiva', '( %s -> A. s e. %s ( %s = %s -> t = s ) )' % (atn, U, Ft, Fs))], 'ralrimiva', 'A. t e. %s A. s e. %s ( %s = %s -> t = s )' % (U, U, Ft, Fs))
    idts = w.s([], 'id', '( t = s -> t = s )')
    kc = kscong(w, 't = s', 't', 's', idts)
    cF = w.s([kc, w.s([idts, w.s([kc], 'oveq1d', '( t = s -> ( %s ^ 2 ) = ( %s ^ 2 ) )' % (KT, KSs))], 'oveq12d', '( t = s -> ( t / ( %s ^ 2 ) ) = ( s / ( %s ^ 2 ) ) )' % (KT, KSs))],
             'opeq12d', '( t = s -> %s = %s )' % (Ft, Fs))
    fm = w.s([w.s([], 'eqid', '%s = %s' % (F, F)), cF], 'f1mpt', '( %s : %s -1-1-> ( %s X. %s ) <-> ( A. t e. %s %s e. ( %s X. %s ) /\\ A. t e. %s A. s e. %s ( %s = %s -> t = s ) ) )'
             % (F, U, S, T, U, Ft, S, T, U, U, Ft, Fs))
    f1 = st([st([ra1, ra2], 'jca', '( A. t e. %s %s e. ( %s X. %s ) /\\ A. t e. %s A. s e. %s ( %s = %s -> t = s ) )' % (U, Ft, S, T, U, U, Ft, Fs)), a1(w, a, fm, '( %s : %s -1-1-> ( %s X. %s ) <-> ( A. t e. %s %s e. ( %s X. %s ) /\\ A. t e. %s A. s e. %s ( %s = %s -> t = s ) ) )'
             % (F, U, S, T, U, Ft, S, T, U, U, Ft, Fs))], 'mpbird', '%s : %s -1-1-> ( %s X. %s )' % (F, U, S, T))
    # sumprodub
    SUMm = 'sum_ m e. %s ( ( %s ` ( 1st ` ( %s ` m ) ) ) x. ( %s ` ( 2nd ` ( %s ` m ) ) ) )' % (U, G, F, H, F)
    RHS = '( sum_ i e. %s ( %s ` i ) x. sum_ j e. %s ( %s ` j ) )' % (S, G, T, H)
    sp = st([st([fz, tfin, ufin], '3jca', '( %s e. Fin /\\ %s e. Fin /\\ %s e. Fin )' % (S, T, U)), st([gf, hf], 'jca', '( %s : %s --> ( 0 [,) +oo ) /\\ %s : %s --> ( 0 [,) +oo ) )' % (G, S, H, T)),
             f1, w.inst('sumprodub')], 'syl3anc', '%s <_ %s' % (SUMm, RHS))
    # the summand is 1 / m
    fm_ = splitfacts(w, a, 'm', U, kn, wn)
    am = fm_['an']; sm = mkst(w, am)
    KM = KS('m'); Qm = fm_['Q']; K2m = fm_['K2']
    Fm = '<. %s , %s >.' % (KM, Qm)
    idtm = w.s([], 'id', '( t = m -> t = m )')
    kcm = kscong(w, 't = m', 't', 'm', idtm)
    cFm = w.s([kcm, w.s([idtm, w.s([kcm], 'oveq1d', '( t = m -> ( %s ^ 2 ) = ( %s ^ 2 ) )' % (KS('t'), KM))], 'oveq12d', '( t = m -> ( t / ( %s ^ 2 ) ) = %s )' % (KS('t'), Qm))],
              'opeq12d', '( t = m -> %s = %s )' % (Ft, Fm))
    fvc = w.s([cFm, w.s([], 'eqid', '%s = %s' % (F, F))], 'fvmptg', '( ( m e. %s /\\ %s e. _V ) -> ( %s ` m ) = %s )' % (U, Fm, F, Fm))
    fvF = sm([sm([sm([], 'simpr', 'm e. %s' % U), a1(w, am, w.s([], 'opex', '%s e. _V' % Fm), '%s e. _V' % Fm)], 'jca', '( m e. %s /\\ %s e. _V )' % (U, Fm)), fvc], 'syl',
             '( %s ` m ) = %s' % (F, Fm))
    ovq = w.s([], 'ovex', '%s e. _V' % Qm); spx = w.s([], 'supex', '%s e. _V' % KM)
    f1st = sm([sm([fvF], 'fveq2d', '( 1st ` ( %s ` m ) ) = ( 1st ` %s )' % (F, Fm)), a1(w, am, w.s([spx, ovq], 'op1st', '( 1st ` %s ) = %s' % (Fm, KM)), '( 1st ` %s ) = %s' % (Fm, KM))],
              'eqtrd', '( 1st ` ( %s ` m ) ) = %s' % (F, KM))
    f2nd = sm([sm([fvF], 'fveq2d', '( 2nd ` ( %s ` m ) ) = ( 2nd ` %s )' % (F, Fm)), a1(w, am, w.s([spx, ovq], 'op2nd', '( 2nd ` %s ) = %s' % (Fm, Qm)), '( 2nd ` %s ) = %s' % (Fm, Qm))],
              'eqtrd', '( 2nd ` ( %s ` m ) ) = %s' % (F, Qm))
    gv, _ = mpv(w, am, 'o', S, '( 1 / ( o ^ 2 ) )', KM, fm_['kfz'], exs=sm([], 'ovexd', '( 1 / ( %s ^ 2 ) ) e. _V' % KM))
    hv, _ = mpv(w, am, 'f', T, '( 1 / f )', Qm, fm_['qrs'], exs=sm([], 'ovexd', '( 1 / %s ) e. _V' % Qm))
    gq = sm([sm([f1st], 'fveq2d', '( %s ` ( 1st ` ( %s ` m ) ) ) = ( %s ` %s )' % (G, F, G, KM)), gv], 'eqtrd', '( %s ` ( 1st ` ( %s ` m ) ) ) = ( 1 / ( %s ^ 2 ) )' % (G, F, KM))
    hq = sm([sm([f2nd], 'fveq2d', '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( %s ` %s )' % (H, F, H, Qm)), hv], 'eqtrd', '( %s ` ( 2nd ` ( %s ` m ) ) ) = ( 1 / %s )' % (H, F, Qm))
    k2c = sm([fm_['k2n']], 'nncnd', '%s e. CC' % K2m); qc = sm([fm_['qn']], 'nncnd', '%s e. CC' % Qm)
    dmd = sm([sm([sm([], '1cnd', '1 e. CC'), sm([], '1cnd', '1 e. CC')], 'jca', '( 1 e. CC /\\ 1 e. CC )'),
              sm([sm([k2c, sm([fm_['k2n']], 'nnne0d', '%s =/= 0' % K2m)], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (K2m, K2m)),
                  sm([qc, sm([fm_['qn']], 'nnne0d', '%s =/= 0' % Qm)], 'jca', '( %s e. CC /\\ %s =/= 0 )' % (Qm, Qm))], 'jca',
                 '( ( %s e. CC /\\ %s =/= 0 ) /\\ ( %s e. CC /\\ %s =/= 0 ) )' % (K2m, K2m, Qm, Qm)), w.inst('divmuldiv')], 'syl2anc',
             '( ( 1 / %s ) x. ( 1 / %s ) ) = ( ( 1 x. 1 ) / ( %s x. %s ) )' % (K2m, Qm, K2m, Qm))
    one = sm([a1(w, am, w.s([], '1t1e1', '( 1 x. 1 ) = 1'), '( 1 x. 1 ) = 1'), fm_['dc']], 'oveq12d', '( ( 1 x. 1 ) / ( %s x. %s ) ) = ( 1 / m )' % (K2m, Qm))
    val = sm([sm([gq, hq], 'oveq12d', '( ( %s ` ( 1st ` ( %s ` m ) ) ) x. ( %s ` ( 2nd ` ( %s ` m ) ) ) ) = ( ( 1 / %s ) x. ( 1 / %s ) )' % (G, F, H, F, K2m, Qm)),
              sm([dmd, one], 'eqtrd', '( ( 1 / %s ) x. ( 1 / %s ) ) = ( 1 / m )' % (K2m, Qm))], 'eqtrd',
             '( ( %s ` ( 1st ` ( %s ` m ) ) ) x. ( %s ` ( 2nd ` ( %s ` m ) ) ) ) = ( 1 / m )' % (G, F, H, F))
    lhs = st([val], 'sumeq2dv', '%s = sum_ m e. %s ( 1 / m )' % (SUMm, U))
    cbm = a1(w, a, w.s([w.s([], 'oveq2', '( m = j -> ( 1 / m ) = ( 1 / j ) )')], 'cbvsumv', 'sum_ m e. %s ( 1 / m ) = sum_ j e. %s ( 1 / j )' % (U, U)),
             'sum_ m e. %s ( 1 / m ) = sum_ j e. %s ( 1 / j )' % (U, U))
    # the right-hand side
    ai = '( %s /\\ i e. %s )' % (a, S)
    si = mkst(w, ai)
    gi, _ = mpv(w, ai, 'o', S, '( 1 / ( o ^ 2 ) )', 'i', si([], 'simpr', 'i e. %s' % S))
    sg = st([gi], 'sumeq2dv', 'sum_ i e. %s ( %s ` i ) = sum_ i e. %s ( 1 / ( i ^ 2 ) )' % (S, G, S))
    cbi = a1(w, a, w.s([w.s([w.s([], 'oveq1', '( i = k -> ( i ^ 2 ) = ( k ^ 2 ) )')], 'oveq2d', '( i = k -> ( 1 / ( i ^ 2 ) ) = ( 1 / ( k ^ 2 ) ) )')], 'cbvsumv',
                       'sum_ i e. %s ( 1 / ( i ^ 2 ) ) = sum_ k e. %s ( 1 / ( k ^ 2 ) )' % (S, S)), 'sum_ i e. %s ( 1 / ( i ^ 2 ) ) = sum_ k e. %s ( 1 / ( k ^ 2 ) )' % (S, S))
    aj = '( %s /\\ j e. %s )' % (a, T)
    sj = mkst(w, aj)
    hj, _ = mpv(w, aj, 'f', T, '( 1 / f )', 'j', sj([], 'simpr', 'j e. %s' % T))
    sh = st([hj], 'sumeq2dv', 'sum_ j e. %s ( %s ` j ) = sum_ j e. %s ( 1 / j )' % (T, H, T))
    cbj = a1(w, a, w.s([w.s([], 'oveq2', '( j = r -> ( 1 / j ) = ( 1 / r ) )')], 'cbvsumv', 'sum_ j e. %s ( 1 / j ) = sum_ r e. %s ( 1 / r )' % (T, T)),
             'sum_ j e. %s ( 1 / j ) = sum_ r e. %s ( 1 / r )' % (T, T))
    SK = 'sum_ k e. %s ( 1 / ( k ^ 2 ) )' % S; PP = P1('K', 'W')
    rv = st([st([sg, cbi], 'eqtrd', 'sum_ i e. %s ( %s ` i ) = %s' % (S, G, SK)), st([sh, cbj], 'eqtrd', 'sum_ j e. %s ( %s ` j ) = %s' % (T, H, PP))], 'oveq12d',
            '%s = ( %s x. %s )' % (RHS, SK, PP))
    b1 = st([st([st([lhs, cbm], 'eqtrd', '%s = sum_ j e. %s ( 1 / j )' % (SUMm, U)), sp], 'eqbrtrrd', 'sum_ j e. %s ( 1 / j ) <_ %s' % (U, RHS)), rv], 'breqtrd',
            'sum_ j e. %s ( 1 / j ) <_ ( %s x. %s )' % (U, SK, PP))
    # sum 1 / k ^ 2 <_ 2 and P ( 1 ) >_ 0
    inv = sy(w, a, st([wn], 'nnnn0d', 'W e. NN0'), 'z5dinvsq', '%s <_ 2' % SK)
    p0 = st([kn, wn, w.inst('z5p1ge0')], 'syl2anc', '0 <_ %s' % PP)
    ar = '( %s /\\ r e. %s )' % (a, T)
    sr = mkst(w, ar)
    rn = sy(w, ar, sr([lift(w, tss, ar), sr([], 'simpr', 'r e. %s' % T)], 'sseldd', 'r e. ( 1 ... ( |_ ` W ) )'), 'elfznn', 'r e. NN')
    ppr = st([tfin, sr([rn], 'nnrecred', '( 1 / r ) e. RR')], 'fsumrecl', '%s e. RR' % PP)
    ak = '( %s /\\ k e. %s )' % (a, S)
    sk = mkst(w, ak)
    kn2 = sy(w, ak, sk([], 'simpr', 'k e. %s' % S), 'elfznn', 'k e. NN')
    skr = st([fz, sk([sk([kn2], 'nnsqcld', '( k ^ 2 ) e. NN')], 'nnrecred', '( 1 / ( k ^ 2 ) ) e. RR')], 'fsumrecl', '%s e. RR' % SK)
    b2 = st([skr, litr(w, a, '2'), ppr, p0, inv], 'lemul1ad', '( %s x. %s ) <_ ( 2 x. %s )' % (SK, PP, PP))
    ur = st([ufin, sm([fm_['vn']], 'nnrecred', '( 1 / m ) e. RR')], 'fsumrecl', 'sum_ m e. %s ( 1 / m ) e. RR' % U)
    ujr = st([cbm, ur], 'eqeltrrd', 'sum_ j e. %s ( 1 / j ) e. RR' % U)
    w.qed([ujr, st([skr, ppr], 'remulcld', '( %s x. %s ) e. RR' % (SK, PP)), st([litr(w, a, '2'), ppr], 'remulcld', '( 2 x. %s ) e. RR' % PP), b1, b2], 'letrd', STATEMENTS['z5dcs2'])
    return w


def z5dp1k():
    w = W('z5dp1k', "Blueprint interface I9(b) (Lean P1_lower_log): ( 1 / 2 ) ( phi ( K ) / K ) log R <_ P ( 1 ) = sum over the squarefree "
                    "r <_ R coprime to K of 1 / r, for every R > 0: log R <_ H ( |_ R ) <_ ( K / phi ( K ) ) sum over the coprime integers "
                    "<_ 2 ( K / phi ( K ) ) P ( 1 ) (z5dhk, z5dcs2); for R < 1 the left side is negative.")
    a = '( K e. NN /\\ R e. RR+ )'
    st = mkst(w, a)
    kn = st([], 'simpl', 'K e. NN'); rp = st([], 'simpr', 'R e. RR+')
    rr = st([rp], 'rpred', 'R e. RR')
    PP = P1('K', 'R')
    q = '( ( phi ` K ) / K )'; L = '( log ` R )'
    GOAL = '( ( ( 1 / 2 ) x. %s ) x. %s ) <_ %s' % (q, L, PP)
    # common facts
    phn = st([kn], 'phicld', '( phi ` K ) e. NN')
    qrp = st([st([phn], 'nnrpd', '( phi ` K ) e. RR+'), st([kn], 'nnrpd', 'K e. RR+')], 'rpdivcld', '%s e. RR+' % q)
    lr = st([rp], 'relogcld', '%s e. RR' % L)
    rsf = st([kn, rr, w.inst('z5rsetfi')], 'syl2anc', '( ( K RSet R ) C_ ( 1 ... ( |_ ` R ) ) /\\ ( K RSet R ) e. Fin )')
    ar = '( %s /\\ r e. ( K RSet R ) )' % a
    sr = mkst(w, ar)
    rn = sy(w, ar, sr([w.s([st([rsf], 'simpld', '( K RSet R ) C_ ( 1 ... ( |_ ` R ) )')], 'adantr', '( %s -> ( K RSet R ) C_ ( 1 ... ( |_ ` R ) ) )' % ar),
                       sr([], 'simpr', 'r e. ( K RSet R )')], 'sseldd', 'r e. ( 1 ... ( |_ ` R ) )'), 'elfznn', 'r e. NN')
    pr = st([st([rsf], 'simprd', '( K RSet R ) e. Fin'), sr([rn], 'nnrecred', '( 1 / r ) e. RR')], 'fsumrecl', '%s e. RR' % PP)
    p0 = st([kn, rr, w.inst('z5p1ge0')], 'syl2anc', '0 <_ %s' % PP)
    # case 1 <_ R
    c1 = '( %s /\\ 1 <_ R )' % a
    s1 = mkst(w, c1)
    lf = lambda x: w.s([x], 'adantr', '( %s -> %s )' % (c1, split_imp(w_formula(w, x))[1]))
    W_ = '( |_ ` R )'
    rr1 = lf(rr); kn1 = lf(kn)
    wn = s1([rr1, s1([], 'simpr', '1 <_ R'), w.inst('flge1nn')], 'syl2anc', '%s e. NN' % W_)
    H = 'sum_ m e. ( 1 ... %s ) ( 1 / m )' % W_
    C = 'sum_ j e. %s ( 1 / j )' % CS('K', W_)
    PW = P1('K', W_)
    h1 = sy(w, c1, lf(rp), 'harmoniclbnd', '%s <_ %s' % (L, H))
    kq = '( K / ( phi ` K ) )'
    h2 = s1([kn1, wn, w.inst('z5dhk')], 'syl2anc', '%s <_ ( %s x. %s )' % (H, kq, C))
    h3 = s1([kn1, wn, w.inst('z5dcs2')], 'syl2anc', '%s <_ ( 2 x. %s )' % (C, PW))
    # RSet at |_ R is RSet at R
    BODY = '( ( mmu ` k ) =/= 0 /\\ ( k gcd K ) = 1 )'
    v1 = s1([kn1, s1([wn], 'nnred', '%s e. RR' % W_), w.inst('z5rsetval')], 'syl2anc', '( K RSet %s ) = { k e. ( 1 ... ( |_ ` %s ) ) | %s }' % (W_, W_, BODY))
    v2 = s1([kn1, rr1, w.inst('z5rsetval')], 'syl2anc', '( K RSet R ) = { k e. ( 1 ... %s ) | %s }' % (W_, BODY))
    fl = sy(w, c1, rr1, 'flidm', '( |_ ` %s ) = %s' % (W_, W_))
    v3 = s1([s1([fl], 'oveq2d', '( 1 ... ( |_ ` %s ) ) = ( 1 ... %s )' % (W_, W_))], 'rabeqdv', '{ k e. ( 1 ... ( |_ ` %s ) ) | %s } = { k e. ( 1 ... %s ) | %s }' % (W_, BODY, W_, BODY))
    rse = s1([s1([v1, v3], 'eqtrd', '( K RSet %s ) = { k e. ( 1 ... %s ) | %s }' % (W_, W_, BODY)), v2], 'eqtr4d', '( K RSet %s ) = ( K RSet R )' % W_)
    pe = s1([rse], 'sumeq1d', '%s = %s' % (PW, PP))
    h3b = s1([h3, s1([pe], 'oveq2d', '( 2 x. %s ) = ( 2 x. %s )' % (PW, PP))], 'breqtrd', '%s <_ ( 2 x. %s )' % (C, PP))
    kqp = lf(st([st([kn], 'nnrpd', 'K e. RR+'), st([phn], 'nnrpd', '( phi ` K ) e. RR+')], 'rpdivcld', '%s e. RR+' % kq))
    kqrp = s1([kqp], 'rpred', '%s e. RR' % kq)
    kq0 = s1([kqp], 'rpge0d', '0 <_ %s' % kq)
    ai = '( %s /\\ j e. %s )' % (c1, CS('K', W_))
    si = mkst(w, ai)
    jn = sy(w, ai, si([si([], 'simpr', 'j e. %s' % CS('K', W_)), w.inst('elrabi')], 'syl', 'j e. ( 1 ... %s )' % W_), 'elfznn', 'j e. NN')
    cfin = s1([s1([], 'fzfid', '( 1 ... %s ) e. Fin' % W_), a1(w, c1, w.s([], 'ssrab2', '%s C_ ( 1 ... %s )' % (CS('K', W_), W_)), '%s C_ ( 1 ... %s )' % (CS('K', W_), W_))],
              'ssfid', '%s e. Fin' % CS('K', W_))
    cr = s1([cfin, si([jn], 'nnrecred', '( 1 / j ) e. RR')], 'fsumrecl', '%s e. RR' % C)
    pr1 = lf(pr)
    m2 = s1([cr, s1([litr(w, c1, '2'), pr1], 'remulcld', '( 2 x. %s ) e. RR' % PP), kqrp, kq0, h3b], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( 2 x. %s ) )' % (kq, C, kq, PP))
    am = '( %s /\\ m e. ( 1 ... %s ) )' % (c1, W_)
    sm_ = mkst(w, am)
    mn = sy(w, am, sm_([], 'simpr', 'm e. ( 1 ... %s )' % W_), 'elfznn', 'm e. NN')
    hr = s1([s1([], 'fzfid', '( 1 ... %s ) e. Fin' % W_), sm_([mn], 'nnrecred', '( 1 / m ) e. RR')], 'fsumrecl', '%s e. RR' % H)
    x1 = s1([kqrp, cr], 'remulcld', '( %s x. %s ) e. RR' % (kq, C))
    x2 = s1([kqrp, s1([litr(w, c1, '2'), pr1], 'remulcld', '( 2 x. %s ) e. RR' % PP)], 'remulcld', '( %s x. ( 2 x. %s ) ) e. RR' % (kq, PP))
    lr1 = lf(lr)
    l1 = s1([lr1, hr, x1, h1, h2], 'letrd', '%s <_ ( %s x. %s )' % (L, kq, C))
    l2 = s1([lr1, x1, x2, l1, m2], 'letrd', '%s <_ ( %s x. ( 2 x. %s ) )' % (L, kq, PP))
    qr1 = lf(st([qrp], 'rpred', '%s e. RR' % q)); q01 = lf(st([qrp], 'rpge0d', '0 <_ %s' % q))
    l3 = s1([lr1, x2, qr1, q01, l2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s x. ( 2 x. %s ) ) )' % (q, L, q, kq, PP))
    qc = s1([qr1], 'recnd', '%s e. CC' % q); kqc = s1([kqrp], 'recnd', '%s e. CC' % kq)
    pc2 = s1([s1([litr(w, c1, '2'), pr1], 'remulcld', '( 2 x. %s ) e. RR' % PP)], 'recnd', '( 2 x. %s ) e. CC' % PP)
    ma = s1([qc, kqc, pc2], 'mulassd', '( ( %s x. %s ) x. ( 2 x. %s ) ) = ( %s x. ( %s x. ( 2 x. %s ) ) )' % (q, kq, PP, q, kq, PP))
    d6 = s1([s1([lf(phn)], 'nncnd', '( phi ` K ) e. CC'), s1([kn1], 'nncnd', 'K e. CC'), s1([lf(phn)], 'nnne0d', '( phi ` K ) =/= 0'), s1([kn1], 'nnne0d', 'K =/= 0')],
            'divcan6d', '( %s x. %s ) = 1' % (q, kq))
    one = s1([s1([d6], 'oveq1d', '( ( %s x. %s ) x. ( 2 x. %s ) ) = ( 1 x. ( 2 x. %s ) )' % (q, kq, PP, PP)), s1([pc2], 'mullidd', '( 1 x. ( 2 x. %s ) ) = ( 2 x. %s )' % (PP, PP))],
             'eqtrd', '( ( %s x. %s ) x. ( 2 x. %s ) ) = ( 2 x. %s )' % (q, kq, PP, PP))
    l4 = s1([l3, s1([ma, one], 'eqtr3d', '( %s x. ( %s x. ( 2 x. %s ) ) ) = ( 2 x. %s )' % (q, kq, PP, PP))], 'breqtrd', '( %s x. %s ) <_ ( 2 x. %s )' % (q, L, PP))
    cl1 = Closure(w, c1, {q: [('RR', qr1)], L: [('RR', lr1)], PP: [('RR', pr1)]})
    for x in (q, L, PP):
        cl1.atom(x)
    g1 = lin.linarith(w, c1, [l4], GOAL, closure=cl1, products=True)
    # case R < 1
    c2 = '( %s /\\ -. 1 <_ R )' % a
    s2 = mkst(w, c2)
    rr2 = w.s([rr], 'adantr', '( %s -> R e. RR )' % c2)
    r1 = s2([s2([], 'simpr', '-. 1 <_ R'), s2([rr2, s2([], '1red', '1 e. RR')], 'ltnled', '( R < 1 <-> -. 1 <_ R )')], 'mpbird', 'R < 1')
    lt = s2([r1, s2([w.s([rp], 'adantr', '( %s -> R e. RR+ )' % c2), a1(w, c2, w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), w.inst('logltb')], 'syl2anc',
                    '( R < 1 <-> %s < ( log ` 1 ) )' % L)], 'mpbid', '%s < ( log ` 1 )' % L)
    lt0 = s2([lt, a1(w, c2, w.s([], 'log1', '( log ` 1 ) = 0'), '( log ` 1 ) = 0')], 'breqtrd', '%s < 0' % L)
    q02 = w.s([st([qrp], 'rpge0d', '0 <_ %s' % q)], 'adantr', '( %s -> 0 <_ %s )' % (c2, q))
    p02 = w.s([p0], 'adantr', '( %s -> 0 <_ %s )' % (c2, PP))
    cl2 = Closure(w, c2, {q: [('RR', w.s([st([qrp], 'rpred', '%s e. RR' % q)], 'adantr', '( %s -> %s e. RR )' % (c2, q)))],
                          L: [('RR', w.s([lr], 'adantr', '( %s -> %s e. RR )' % (c2, L)))], PP: [('RR', w.s([pr], 'adantr', '( %s -> %s e. RR )' % (c2, PP)))]})
    for x in (q, L, PP):
        cl2.atom(x)
    g2 = lin.nlinarith(w, c2, [lt0, q02, p02], GOAL, closure=cl2)
    w.qed([g1, g2], 'pm2.61dan', STATEMENTS['z5dp1k'])
    return w


def rparlow(w, lab, qx, desc):
    """z5dp1low / z5dp1qrd: the Rpar form of a ( 1 / 2 ) qx log R <_ P ( 1 ) bound (lab0 is the generic one)"""
    a = '( N e. NN /\\ D e. RR+ )'
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN'); dp = st([], 'simpr', 'D e. RR+')
    rp = st([dp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % RPD)
    L = '( log ` D )'; LR = '( log ` %s )' % RPD
    qR = qx(RPD)
    return st, a, nn, dp, rp, L, LR, qR


def z5dp1low():
    w = W('z5dp1low', "Blueprint interface I9(b) in the Rpar form consumed by detector_lower_bound (Lean P1_lower): "
                      "( 1 / 200 ) ( phi ( N ) / N ) log D <_ P ( 1 ) at R = D ^ ( 1 / 100 ), from P1_lower_log (z5dp1k).")
    q = '( ( phi ` N ) / N )'
    st, a, nn, dp, rp, L, LR, _ = rparlow(w, 'z5dp1low', lambda R: q, '')
    b = st([nn, rp, w.inst('z5dp1k')], 'syl2anc', '( ( ( 1 / 2 ) x. %s ) x. %s ) <_ %s' % (q, LR, P1D))
    lc = st([dp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'logcxpd', '%s = ( ( 1 / ; ; 1 0 0 ) x. %s )' % (LR, L))
    b2 = st([b, st([lc], 'oveq2d', '( ( ( 1 / 2 ) x. %s ) x. %s ) = ( ( ( 1 / 2 ) x. %s ) x. ( ( 1 / ; ; 1 0 0 ) x. %s ) )' % (q, LR, q, L))], 'eqbrtrrd',
            '( ( ( 1 / 2 ) x. %s ) x. ( ( 1 / ; ; 1 0 0 ) x. %s ) ) <_ %s' % (q, L, P1D))
    phn = st([nn], 'phicld', '( phi ` N ) e. NN')
    qr = st([st([phn], 'nnred', '( phi ` N ) e. RR'), st([nn], 'nnrpd', 'N e. RR+')], 'rerpdivcld', '%s e. RR' % q)
    lr = st([dp], 'relogcld', '%s e. RR' % L)
    cl = Closure(w, a, {q: [('RR', qr)], L: [('RR', lr)]})
    cl.atom(q); cl.atom(L)
    e = lin.lineq(w, a, '( ( ( 1 / ; ; 2 0 0 ) x. %s ) x. %s )' % (q, L), '( ( ( 1 / 2 ) x. %s ) x. ( ( 1 / ; ; 1 0 0 ) x. %s ) )' % (q, L), closure=cl, products=True)
    w.qed([e, b2], 'eqbrtrd', STATEMENTS['z5dp1low'])
    return w


def w_formula(w, name):
    from cl import formula_of
    return formula_of(w, name)


if __name__ == '__main__':
    import lin as _lin
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        if os.environ.get('Z5D_WRITE_ONLY'):
            w.write()
        else:
            run(w)
