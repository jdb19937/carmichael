"""Z6a (block z6ab): the log-Gamma term functions on Re z > -1 -- domain facts,
derivative, holomorphy."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_ghlib import *
from lin import linarith

V1 = HPT('-u 1')
DD = '( CC \\ ( -oo (,] 0 ) )'
CK = lambda K='K': '( log ` ( ( %s + 1 ) / %s ) )' % (K, K)
TK = lambda K='K', z='z': '( ( %s x. %s ) - ( log ` ( ( %s / %s ) + 1 ) ) )' % (z, CK(K), z, K)
DTK = lambda K='K', z='z': '( %s - ( 1 / ( %s + %s ) ) )' % (CK(K), z, K)
S_HV1 = '( ( K e. NN /\\ Z e. %s ) -> ( ( ( Z / K ) + 1 ) e. %s /\\ ( Z + K ) =/= 0 ) )' % (V1, DD)
S_HTDV = '( ( K e. NN /\\ U e. %s /\\ U C_ %s ) -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (TOP, V1, TK(), DTK())
S_HTHOL = '( ( K e. NN /\\ U e. %s /\\ U C_ %s ) -> %s )' % (TOP, V1, HOLG('( z e. U |-> %s )' % TK(), 'U'))


def hv1():
    w = W('z6hv1', 'For ` K e. NN ` and ` -u 1 < Re Z `, ` ( Z / K ) + 1 ` lies in the slit plane and '
          '` Z + K ` is nonzero: the domain facts of the log-Gamma term functions.')
    A0 = '( K e. NN /\\ Z e. %s )' % V1
    s = st(w, A0)
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
    zv = w.s([], 'simpr', '( %s -> Z e. %s )' % (A0, V1))
    m1 = w.s([w.s([], '1re', '1 e. RR')], 'renegcli', '-u 1 e. RR')
    bi = s([w.s([m1, w.inst('elhp2')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ -u 1 < ( Re ` Z ) ) )' % V1)], 'a1i',
           '( Z e. %s <-> ( Z e. CC /\\ -u 1 < ( Re ` Z ) ) )' % V1)
    both = s([zv, bi], 'mpbid', '( Z e. CC /\\ -u 1 < ( Re ` Z ) )')
    zc = s([both], 'simpld', 'Z e. CC')
    lt = s([both], 'simprd', '-u 1 < ( Re ` Z )')
    kr = s([kn], 'nnred', 'K e. RR')
    kc = s([kn], 'nncnd', 'K e. CC')
    k1 = s([kn, w.inst('nnge1')], 'syl', '1 <_ K')
    rz = s([zc], 'recld', '( Re ` Z ) e. RR')
    pos = linarith(w, A0, [lt, k1], '0 < ( ( Re ` Z ) + K )', leaves={'( Re ` Z )': rz, 'K': kr})
    re = s([s([zc, kc], 'readdd', '( Re ` ( Z + K ) ) = ( ( Re ` Z ) + ( Re ` K ) )'),
            s([s([kr, w.inst('rere')], 'syl', '( Re ` K ) = K')], 'oveq2d', '( ( Re ` Z ) + ( Re ` K ) ) = ( ( Re ` Z ) + K )')], 'eqtrd',
           '( Re ` ( Z + K ) ) = ( ( Re ` Z ) + K )')
    pos2 = s([pos, re], 'breqtrrd', '0 < ( Re ` ( Z + K ) )')
    ne = s([pos2], 'gt0ne0d', '( Re ` ( Z + K ) ) =/= 0')
    imp = w.s([w.s([w.s([], 'fveq2', '( ( Z + K ) = 0 -> ( Re ` ( Z + K ) ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi',
                   '( ( Z + K ) = 0 -> ( Re ` ( Z + K ) ) = 0 )')], 'necon3i', '( ( Re ` ( Z + K ) ) =/= 0 -> ( Z + K ) =/= 0 )')
    zkne = s([ne, imp], 'syl', '( Z + K ) =/= 0')
    k0 = s([kn], 'nnne0d', 'K =/= 0')
    zkc = s([zc, kc], 'addcld', '( Z + K ) e. CC')
    q = s([s([zc, kc, kc, k0], 'divdird', '( ( Z + K ) / K ) = ( ( Z / K ) + ( K / K ) )'),
           s([s([kc, k0], 'dividd', '( K / K ) = 1')], 'oveq2d', '( ( Z / K ) + ( K / K ) ) = ( ( Z / K ) + 1 )')], 'eqtrd',
          '( ( Z + K ) / K ) = ( ( Z / K ) + 1 )')
    rq = s([kr, zkc, k0], 'redivd', '( Re ` ( ( Z + K ) / K ) ) = ( ( Re ` ( Z + K ) ) / K )')
    rpos = s([s([zkc], 'recld', '( Re ` ( Z + K ) ) e. RR'), kr, pos2, s([kn], 'nngt0d', '0 < K')], 'divgt0d', '0 < ( ( Re ` ( Z + K ) ) / K )')
    rq2 = s([s([q], 'fveq2d', '( Re ` ( ( Z + K ) / K ) ) = ( Re ` ( ( Z / K ) + 1 ) )'), rq], 'eqtr3d',
            '( Re ` ( ( Z / K ) + 1 ) ) = ( ( Re ` ( Z + K ) ) / K )')
    rpos3 = s([rpos, rq2], 'breqtrrd', '0 < ( Re ` ( ( Z / K ) + 1 ) )')
    qc = s([s([zc, kc, k0], 'divcld', '( Z / K ) e. CC'), c1(w, A0, 'ax-1cn', '1 e. CC')], 'addcld', '( ( Z / K ) + 1 ) e. CC')
    bi0 = s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( ( ( Z / K ) + 1 ) e. %s <-> ( ( ( Z / K ) + 1 ) e. CC /\\ 0 < ( Re ` ( ( Z / K ) + 1 ) ) ) )' % HPZ)],
            'a1i', '( ( ( Z / K ) + 1 ) e. %s <-> ( ( ( Z / K ) + 1 ) e. CC /\\ 0 < ( Re ` ( ( Z / K ) + 1 ) ) ) )' % HPZ)
    hp = s([s([qc, rpos3], 'jca', '( ( ( Z / K ) + 1 ) e. CC /\\ 0 < ( Re ` ( ( Z / K ) + 1 ) ) )'), bi0], 'mpbird', '( ( Z / K ) + 1 ) e. %s' % HPZ)
    dd = s([hp, w.inst('hp0logdm')], 'syl', '( ( Z / K ) + 1 ) e. %s' % DD)
    w.qed([dd, zkne], 'jca', S_HV1)
    return run(w)


def htdv():
    w = W('z6htdv', 'The derivative of a log-Gamma term function ` z log ( ( K + 1 ) / K ) - log ( z / K + 1 ) ` '
          'on an open subset of ` -u 1 < Re z ` ( ~ dvlog , ~ dvmptco ).')
    A0 = '( K e. NN /\\ U e. %s /\\ U C_ %s )' % (TOP, V1)
    s = st(w, A0)
    kn = w.s([], 'simp1', '( %s -> K e. NN )' % A0)
    uo = w.s([], 'simp2', '( %s -> U e. %s )' % (A0, TOP))
    uv = w.s([], 'simp3', '( %s -> U C_ %s )' % (A0, V1))
    ucc = opnss(w, A0, uo, 'U')
    kc = s([kn], 'nncnd', 'K e. CC')
    k0 = s([kn], 'nnne0d', 'K =/= 0')
    krp = s([kn], 'nnrpd', 'K e. RR+')
    k1rp = s([s([kn, w.inst('peano2nn')], 'syl', '( K + 1 ) e. NN')], 'nnrpd', '( K + 1 ) e. RR+')
    cr = s([s([k1rp, krp], 'rpdivcld', '( ( K + 1 ) / K ) e. RR+')], 'relogcld', '%s e. RR' % CK())
    cc = s([cr], 'recnd', '%s e. CC' % CK())
    sc = c1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    Ac = '( %s /\\ z e. CC )' % A0
    zc = w.s([], 'simpr', '( %s -> z e. CC )' % Ac)
    o1 = c1(w, Ac, 'ax-1cn', '1 e. CC')
    ccz = w.s([cc], 'adantr', '( %s -> %s e. CC )' % (Ac, CK()))
    kcz = w.s([kc], 'adantr', '( %s -> K e. CC )' % Ac)
    did = s([sc], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    # the linear part
    dcm = s([sc, zc, o1, did, cc], 'dvmptcmul', '( CC _D ( z e. CC |-> ( %s x. z ) ) ) = ( z e. CC |-> ( %s x. 1 ) )' % (CK(), CK()))
    com = s([w.s([ccz, zc], 'mulcomd', '( %s -> ( %s x. z ) = ( z x. %s ) )' % (Ac, CK(), CK()))], 'mpteq2dva',
            '( z e. CC |-> ( %s x. z ) ) = ( z e. CC |-> ( z x. %s ) )' % (CK(), CK()))
    dlin = s([s([com], 'oveq2d', '( CC _D ( z e. CC |-> ( %s x. z ) ) ) = ( CC _D ( z e. CC |-> ( z x. %s ) ) )' % (CK(), CK())), dcm], 'eqtr3d',
             '( CC _D ( z e. CC |-> ( z x. %s ) ) ) = ( z e. CC |-> ( %s x. 1 ) )' % (CK(), CK()))
    zcm = w.s([zc, ccz], 'mulcld', '( %s -> ( z x. %s ) e. CC )' % (Ac, CK()))
    c1c = w.s([ccz, o1], 'mulcld', '( %s -> ( %s x. 1 ) e. CC )' % (Ac, CK()))
    dlinu = dvres(w, A0, 'z', 'U', '( z x. %s )' % CK(), '( %s x. 1 )' % CK(), dlin, zcm, c1c, uo, ucc)
    # the inner function ( z / K ) + 1
    ddiv = s([sc, zc, o1, did, kc, k0], 'dvmptdivc', '( CC _D ( z e. CC |-> ( z / K ) ) ) = ( z e. CC |-> ( 1 / K ) )')
    d1 = s([sc, c1(w, A0, 'ax-1cn', '1 e. CC')], 'dvmptc', '( CC _D ( z e. CC |-> 1 ) ) = ( z e. CC |-> 0 )')
    zk = w.s([zc, kcz, w.s([k0], 'adantr', '( %s -> K =/= 0 )' % Ac)], 'divcld', '( %s -> ( z / K ) e. CC )' % Ac)
    rk = w.s([o1, kcz, w.s([k0], 'adantr', '( %s -> K =/= 0 )' % Ac)], 'divcld', '( %s -> ( 1 / K ) e. CC )' % Ac)
    dadd = s([sc, zk, rk, ddiv, o1, c1(w, Ac, 'c0ex', '0 e. _V'), d1], 'dvmptadd',
             '( CC _D ( z e. CC |-> ( ( z / K ) + 1 ) ) ) = ( z e. CC |-> ( ( 1 / K ) + 0 ) )')
    inn = w.s([zk, o1], 'addcld', '( %s -> ( ( z / K ) + 1 ) e. CC )' % Ac)
    rk0 = w.s([rk, w.s([], '0cnd', '( %s -> 0 e. CC )' % Ac)], 'addcld', '( %s -> ( ( 1 / K ) + 0 ) e. CC )' % Ac)
    dinu = dvres(w, A0, 'z', 'U', '( ( z / K ) + 1 )', '( ( 1 / K ) + 0 )', dadd, inn, rk0, uo, ucc)
    # log on the slit plane
    ed = w.s([], 'eqid', '%s = %s' % (DD, DD))
    lf = s([c1(w, A0, 'logf1o', 'log : ( CC \\ { 0 } ) -1-1-onto-> ran log'), w.inst('f1of')], 'syl', 'log : ( CC \\ { 0 } ) --> ran log')
    lres = s([lf, c1(w, A0, 'slitss', '%s C_ ( CC \\ { 0 } )' % DD)], 'feqresmpt', '( log |` %s ) = ( x e. %s |-> ( log ` x ) )' % (DD, DD))
    dlog = s([s([lres], 'oveq2d', '( CC _D ( log |` %s ) ) = ( CC _D ( x e. %s |-> ( log ` x ) ) )' % (DD, DD)), w.s([w.s([ed], 'dvlog', '( CC _D ( log |` %s ) ) = ( x e. %s |-> ( 1 / x ) )' % (DD, DD))], 'a1i', '( %s -> ( CC _D ( log |` %s ) ) = ( x e. %s |-> ( 1 / x ) ) )' % (A0, DD, DD))],
             'eqtr3d', '( CC _D ( x e. %s |-> ( log ` x ) ) ) = ( x e. %s |-> ( 1 / x ) )' % (DD, DD))
    Au = '( %s /\\ z e. U )' % A0
    zu = w.s([], 'simpr', '( %s -> z e. U )' % Au)
    zv1 = w.s([w.s([uv], 'adantr', '( %s -> U C_ %s )' % (Au, V1)), zu], 'sseldd', '( %s -> z e. %s )' % (Au, V1))
    fac = w.s([w.s([w.s([kn], 'adantr', '( %s -> K e. NN )' % Au), zv1], 'jca', '( %s -> ( K e. NN /\\ z e. %s ) )' % (Au, V1)), w.inst('z6hv1')], 'syl',
              '( %s -> ( ( ( z / K ) + 1 ) e. %s /\\ ( z + K ) =/= 0 ) )' % (Au, DD))
    ind = w.s([fac], 'simpld', '( %s -> ( ( z / K ) + 1 ) e. %s )' % (Au, DD))
    zkn = w.s([fac], 'simprd', '( %s -> ( z + K ) =/= 0 )' % Au)
    Ax = '( %s /\\ x e. %s )' % (A0, DD)
    xd = w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, DD))
    xc = w.s([xd], 'eldifad', '( %s -> x e. CC )' % Ax)
    xn = w.s([xd, w.s([ed], 'logdmn0', '( x e. %s -> x =/= 0 )' % DD)], 'syl', '( %s -> x =/= 0 )' % Ax)
    lx = w.s([xc, xn], 'logcld', '( %s -> ( log ` x ) e. CC )' % Ax)
    ix = w.s([xc, xn], 'reccld', '( %s -> ( 1 / x ) e. CC )' % Ax)
    kcu = w.s([kc], 'adantr', '( %s -> K e. CC )' % Au)
    k0u = w.s([k0], 'adantr', '( %s -> K =/= 0 )' % Au)
    rk0u = w.s([w.s([c1(w, Au, 'ax-1cn', '1 e. CC'), kcu, k0u], 'divcld', '( %s -> ( 1 / K ) e. CC )' % Au), w.s([], '0cnd', '( %s -> 0 e. CC )' % Au)], 'addcld',
               '( %s -> ( ( 1 / K ) + 0 ) e. CC )' % Au)
    INN = '( ( z / K ) + 1 )'
    e1 = w.s([], 'fveq2', '( x = %s -> ( log ` x ) = ( log ` %s ) )' % (INN, INN))
    e2 = w.s([], 'oveq2', '( x = %s -> ( 1 / x ) = ( 1 / %s ) )' % (INN, INN))
    DL = '( ( 1 / %s ) x. ( ( 1 / K ) + 0 ) )' % INN
    dco = s([sc, sc, ind, rk0u, lx, ix, dinu, dlog, e1, e2], 'dvmptco', '( CC _D ( z e. U |-> ( log ` %s ) ) ) = ( z e. U |-> %s )' % (INN, DL))
    # the difference
    zuc = w.s([w.s([ucc], 'adantr', '( %s -> U C_ CC )' % Au), zu], 'sseldd', '( %s -> z e. CC )' % Au)
    ccu = w.s([cc], 'adantr', '( %s -> %s e. CC )' % (Au, CK()))
    zcmu = w.s([zuc, ccu], 'mulcld', '( %s -> ( z x. %s ) e. CC )' % (Au, CK()))
    c1u = w.s([ccu, c1(w, Au, 'ax-1cn', '1 e. CC')], 'mulcld', '( %s -> ( %s x. 1 ) e. CC )' % (Au, CK()))
    innc = w.s([ind], 'eldifad', '( %s -> %s e. CC )' % (Au, INN))
    inn0 = w.s([ind, w.s([ed], 'logdmn0', '( %s e. %s -> %s =/= 0 )' % (INN, DD, INN))], 'syl', '( %s -> %s =/= 0 )' % (Au, INN))
    lgc = w.s([innc, inn0], 'logcld', '( %s -> ( log ` %s ) e. CC )' % (Au, INN))
    dlc = w.s([w.s([innc, inn0], 'reccld', '( %s -> ( 1 / %s ) e. CC )' % (Au, INN)), rk0u], 'mulcld', '( %s -> %s e. CC )' % (Au, DL))
    dsub = s([sc, zcmu, c1u, dlinu, lgc, dlc, dco], 'dvmptsub', '( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> ( ( %s x. 1 ) - %s ) )' % (TK(), CK(), DL))
    # simplify the body
    b1 = w.s([ccu], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (Au, CK(), CK()))
    r0 = w.s([w.s([w.s([c1(w, Au, 'ax-1cn', '1 e. CC'), kcu, k0u], 'divcld', '( %s -> ( 1 / K ) e. CC )' % Au)], 'addridd', '( %s -> ( ( 1 / K ) + 0 ) = ( 1 / K ) )' % Au)], 'oveq2d',
             '( %s -> %s = ( ( 1 / %s ) x. ( 1 / K ) ) )' % (Au, DL, INN))
    one = c1(w, Au, 'ax-1cn', '1 e. CC')
    dm = w.s([one, innc, one, kcu, inn0, k0u], 'divmuldivd', '( %s -> ( ( 1 / %s ) x. ( 1 / K ) ) = ( ( 1 x. 1 ) / ( %s x. K ) ) )' % (Au, INN, INN))
    num = w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % Au)
    zkd = w.s([zuc, kcu, k0u], 'divcld', '( %s -> ( z / K ) e. CC )' % Au)
    den = w.s([w.s([zkd, one, kcu], 'adddird', '( %s -> ( %s x. K ) = ( ( ( z / K ) x. K ) + ( 1 x. K ) ) )' % (Au, INN)),
               w.s([w.s([zuc, kcu, k0u], 'divcan1d', '( %s -> ( ( z / K ) x. K ) = z )' % Au), w.s([kcu], 'mullidd', '( %s -> ( 1 x. K ) = K )' % Au)], 'oveq12d',
                   '( %s -> ( ( ( z / K ) x. K ) + ( 1 x. K ) ) = ( z + K ) )' % Au)], 'eqtrd', '( %s -> ( %s x. K ) = ( z + K ) )' % (Au, INN))
    frac = w.s([num, den], 'oveq12d', '( %s -> ( ( 1 x. 1 ) / ( %s x. K ) ) = ( 1 / ( z + K ) ) )' % (Au, INN))
    b2 = w.s([r0, dm, frac], '3eqtrd', '( %s -> %s = ( 1 / ( z + K ) ) )' % (Au, DL))
    body = w.s([b1, b2], 'oveq12d', '( %s -> ( ( %s x. 1 ) - %s ) = %s )' % (Au, CK(), DL, DTK()))
    w.qed([dsub, s([body], 'mpteq2dva', '( z e. U |-> ( ( %s x. 1 ) - %s ) ) = ( z e. U |-> %s )' % (CK(), DL, DTK()))], 'eqtrd', S_HTDV)
    return run(w)


def hthol():
    w = W('z6hthol', 'A log-Gamma term function is holomorphic on every open subset of ` -u 1 < Re z ` .')
    A0 = '( K e. NN /\\ U e. %s /\\ U C_ %s )' % (TOP, V1)
    s = st(w, A0)
    kn = w.s([], 'simp1', '( %s -> K e. NN )' % A0)
    uo = w.s([], 'simp2', '( %s -> U e. %s )' % (A0, TOP))
    uv = w.s([], 'simp3', '( %s -> U C_ %s )' % (A0, V1))
    ucc = opnss(w, A0, uo, 'U')
    kc = s([kn], 'nncnd', 'K e. CC')
    krp = s([kn], 'nnrpd', 'K e. RR+')
    k1rp = s([s([kn, w.inst('peano2nn')], 'syl', '( K + 1 ) e. NN')], 'nnrpd', '( K + 1 ) e. RR+')
    cc = s([s([s([k1rp, krp], 'rpdivcld', '( ( K + 1 ) / K ) e. RR+')], 'relogcld', '%s e. RR' % CK())], 'recnd', '%s e. CC' % CK())
    Au = '( %s /\\ z e. U )' % A0
    zu = w.s([], 'simpr', '( %s -> z e. U )' % Au)
    zv1 = w.s([w.s([uv], 'adantr', '( %s -> U C_ %s )' % (Au, V1)), zu], 'sseldd', '( %s -> z e. %s )' % (Au, V1))
    fac = w.s([w.s([w.s([kn], 'adantr', '( %s -> K e. NN )' % Au), zv1], 'jca', '( %s -> ( K e. NN /\\ z e. %s ) )' % (Au, V1)), w.inst('z6hv1')], 'syl',
              '( %s -> ( ( ( z / K ) + 1 ) e. %s /\\ ( z + K ) =/= 0 ) )' % (Au, DD))
    ind = w.s([fac], 'simpld', '( %s -> ( ( z / K ) + 1 ) e. %s )' % (Au, DD))
    zkn = w.s([fac], 'simprd', '( %s -> ( z + K ) =/= 0 )' % Au)
    zc = w.s([w.s([ucc], 'adantr', '( %s -> U C_ CC )' % Au), zu], 'sseldd', '( %s -> z e. CC )' % Au)
    ccu = w.s([cc], 'adantr', '( %s -> %s e. CC )' % (Au, CK()))
    ed = w.s([], 'eqid', '%s = %s' % (DD, DD))
    INN = '( ( z / K ) + 1 )'
    innc = w.s([ind], 'eldifad', '( %s -> %s e. CC )' % (Au, INN))
    inn0 = w.s([ind, w.s([ed], 'logdmn0', '( %s e. %s -> %s =/= 0 )' % (INN, DD, INN))], 'syl', '( %s -> %s =/= 0 )' % (Au, INN))
    tc = w.s([w.s([zc, ccu], 'mulcld', '( %s -> ( z x. %s ) e. CC )' % (Au, CK())), w.s([innc, inn0], 'logcld', '( %s -> ( log ` %s ) e. CC )' % (Au, INN))], 'subcld',
             '( %s -> %s e. CC )' % (Au, TK()))
    zkc = w.s([zc, w.s([kc], 'adantr', '( %s -> K e. CC )' % Au)], 'addcld', '( %s -> ( z + K ) e. CC )' % Au)
    dc = w.s([ccu, w.s([zkc, zkn], 'reccld', '( %s -> ( 1 / ( z + K ) ) e. CC )' % Au)], 'subcld', '( %s -> %s e. CC )' % (Au, DTK()))
    dv = w.s([], 'z6htdv', '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (A0, TK(), DTK()))
    h = holfromdv(w, A0, 'z', 'U', TK(), DTK(), dv, tc, dc, ucc)
    w.lines[-1] = w.lines[-1].replace(h + ':', 'qed:', 1)
    return run(w)


if __name__ == '__main__':
    want = sys.argv[1:]
    for lab, fn in [('z6hv1', hv1), ('z6htdv', htdv), ('z6hthol', hthol)]:
        if lab in want:
            if fn():
                status(lab)
