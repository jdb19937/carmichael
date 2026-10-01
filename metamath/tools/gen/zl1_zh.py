"""ZL1: holomorphy of z |-> sum_k HT ( k , z ) on the open right half-plane
(zl1hthol, zl1zcv, zl1zcl, zl1hvbx, zl1hdbx, zl1zuh, zl1zbx, zl1zhol): C5's
abthol / abtbnd / abtdvb / abbxuh / abbxhol / abhol route for the zeta terms."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl1lib import *
from zl1lib import mptval_ as mptval
from cl import Closure

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    return w.run()


EXP = '( -u %s - 1 )' % RZ
AA = '( ( abs ` Z ) x. ( abs ` ( Z - 1 ) ) )'
V_ = '( ( 2 x. Z ) - 1 )'
INB = lambda Z: '( %s e. CC /\\ ( L < ( Re ` %s ) /\\ ( Re ` %s ) < R ) /\\ ( -u R < ( Im ` %s ) /\\ ( Im ` %s ) < R ) )' % (Z, Z, Z, Z, Z)


def bxctx(w, A1, lrp, rr, zb):
    d = {}
    inb = w.s([zb, w.inst('elbxi')], 'syl', '( %s -> %s )' % (A1, INB('Z')))
    d['zc'] = zc = w.s([inb, w.inst('simp1')], 'syl', '( %s -> Z e. CC )' % A1)
    d['rz'] = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A1, RZ))
    d['lr'] = lr = w.s([lrp], 'rpred', '( %s -> L e. RR )' % A1)
    d['l0'] = l0 = w.s([lrp], 'rpgt0d', '( %s -> 0 < L )' % A1)
    d['lltz'] = lltz = w.s([w.s([inb, w.inst('simp2')], 'syl', '( %s -> ( L < %s /\\ %s < R ) )' % (A1, RZ, RZ))], 'simpld', '( %s -> L < %s )' % (A1, RZ))
    d['z0'] = w.s([a1(w, A1, '0re', '0 e. RR'), lr, d['rz'], l0, lltz], 'lttrd', '( %s -> 0 < %s )' % (A1, RZ))
    d['az'] = w.s([w.s([w.s([lr, w.s([lrp], 'rpge0d', '( %s -> 0 <_ L )' % A1), rr], '3jca', '( %s -> ( L e. RR /\\ 0 <_ L /\\ R e. RR ) )' % A1), zb], 'jca',
                      '( %s -> ( ( L e. RR /\\ 0 <_ L /\\ R e. RR ) /\\ Z e. %s ) )' % (A1, B_)), w.inst('bxabs')], 'syl', '( %s -> ( abs ` Z ) <_ ( 2 x. R ) )' % A1)
    return d


def expmono(w, ante, kn, rz, lr, lltz):
    """( ante -> ( K ^c EXP ) <_ ( K ^c -u ( L + 1 ) ) )"""
    r1 = a1(w, ante, '1re', '1 e. RR')
    T1 = '( %s + 1 )' % RZ
    t1r = w.s([rz, r1], 'readdcld', '( %s -> %s e. RR )' % (ante, T1))
    l1r = w.s([lr, r1], 'readdcld', '( %s -> ( L + 1 ) e. RR )' % ante)
    le = w.s([lr, rz, r1, w.s([lr, rz, lltz], 'ltled', '( %s -> L <_ %s )' % (ante, RZ))], 'leadd1dd', '( %s -> ( L + 1 ) <_ %s )' % (ante, T1))
    nle = w.s([le, w.s([l1r, t1r], 'lenegd', '( %s -> ( ( L + 1 ) <_ %s <-> -u %s <_ -u ( L + 1 ) ) )' % (ante, T1, T1))], 'mpbid', '( %s -> -u %s <_ -u ( L + 1 ) )' % (ante, T1))
    kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % ante)
    mono = w.s([w.s([w.s([kr, w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % ante)], 'jca', '( %s -> ( K e. RR /\\ 1 <_ K ) )' % ante),
                     w.s([w.s([t1r], 'renegcld', '( %s -> -u %s e. RR )' % (ante, T1)), w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % ante)], 'jca',
                         '( %s -> ( -u %s e. RR /\\ -u ( L + 1 ) e. RR ) )' % (ante, T1)), nle], '3jca',
                    '( %s -> ( ( K e. RR /\\ 1 <_ K ) /\\ ( -u %s e. RR /\\ -u ( L + 1 ) e. RR ) /\\ -u %s <_ -u ( L + 1 ) ) )' % (ante, T1, T1)), w.inst('cxplea')], 'syl',
                '( %s -> ( K ^c -u %s ) <_ ( K ^c -u ( L + 1 ) ) )' % (ante, T1))
    ee = w.s([w.s([rz], 'recnd', '( %s -> %s e. CC )' % (ante, RZ)), a1(w, ante, 'ax-1cn', '1 e. CC')], 'negdi2d', '( %s -> -u %s = %s )' % (ante, T1, EXP))
    return w.s([w.s([w.s([ee], 'oveq2d', '( %s -> ( K ^c -u %s ) = ( K ^c %s ) )' % (ante, T1, EXP))], 'eqcomd', '( %s -> ( K ^c %s ) = ( K ^c -u %s ) )' % (ante, EXP, T1)), mono],
               'eqbrtrd', '( %s -> ( K ^c %s ) <_ ( K ^c -u ( L + 1 ) ) )' % (ante, EXP))


# ---------------------------------------------------------------- zl1hthol
if not only or 'zl1hthol' in only:
    w = W('zl1hthol', 'The zeta continuation term ` z |-> HT ( K , z ) ` is holomorphic on every open set ( ~ zl1hdv ).')
    A0 = '( K e. NN /\\ U e. %s )' % TOPO
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
    uo = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, TOPO))
    dv = w.s([], 'zl1hdv', '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (A0, HT('K', 'z'), HD('K', 'z')))
    ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ton = w.s([w.s([ek], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOP)], 'a1i', '( %s -> %s e. ( TopOn ` CC ) )' % (A0, TOP))
    ucc = w.s([ton, uo, w.inst('toponss')], 'syl2anc', '( %s -> U C_ CC )' % A0)
    Az = '( %s /\\ z e. U )' % A0
    zc = w.s([w.s([ucc], 'adantr', '( %s -> U C_ CC )' % Az), w.s([], 'simpr', '( %s -> z e. U )' % Az)], 'sseldd', '( %s -> z e. CC )' % Az)
    cz = Closure(w, Az, {'z': ('CC', zc), 'K': ('NN', w.s([kn], 'adantr', '( %s -> K e. NN )' % Az))})
    HM = '( z e. U |-> %s )' % HT('K', 'z')
    DM = '( z e. U |-> %s )' % HD('K', 'z')
    df = w.s([cz.mem(HD('K', 'z'), 'CC'), w.s([], 'eqid', '%s = %s' % (DM, DM))], 'fmptd', '( %s -> %s : U --> CC )' % (A0, DM))
    hf = w.s([cz.mem(HT('K', 'z'), 'CC'), w.s([], 'eqid', '%s = %s' % (HM, HM))], 'fmptd', '( %s -> %s : U --> CC )' % (A0, HM))
    dm = w.s([w.s([dv], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, HM, DM)), w.s([df, w.inst('fdm')], 'syl', '( %s -> dom %s = U )' % (A0, DM))], 'eqtrd',
             '( %s -> dom ( CC _D %s ) = U )' % (A0, HM))
    cn = w.s([w.s([w.s([a1(w, A0, 'ssid', 'CC C_ CC'), hf, ucc], '3jca', '( %s -> ( CC C_ CC /\\ %s : U --> CC /\\ U C_ CC ) )' % (A0, HM)), dm], 'jca',
                  '( %s -> ( ( CC C_ CC /\\ %s : U --> CC /\\ U C_ CC ) /\\ dom ( CC _D %s ) = U ) )' % (A0, HM, HM)), w.inst('dvcn')], 'syl', '( %s -> %s e. ( U -cn-> CC ) )' % (A0, HM))
    ss = w.s([w.s([dm], 'eqcomd', '( %s -> U = dom ( CC _D %s ) )' % (A0, HM))], 'eqimssd', '( %s -> U C_ dom ( CC _D %s ) )' % (A0, HM))
    w.qed([cn, ss], 'jca', '( %s -> %s )' % (A0, HOL(HM, 'U')))
    go(w)

# ---------------------------------------------------------------- zl1zcv, zl1zcl
T1 = '( %s + 1 )' % RZ
MJ = '( n e. NN |-> ( %s x. ( n ^c -u %s ) ) )' % (AA, T1)
HTS = '( m e. NN |-> %s )' % HT('m', 'Z')
if not only or 'zl1zcv' in only:
    w = W('zl1zcv', 'The series of the zeta continuation terms converges on the open right half-plane '
          '( ~ zl1hvb , ~ zsercvgc , ~ cvgcmpce ).')
    A0 = '( Z e. CC /\\ 0 < %s )' % RZ
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
    rzp = w.s([], 'simpr', '( %s -> 0 < %s )' % (A0, RZ))
    rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    r1 = a1(w, A0, '1re', '1 e. RR')
    t1r = w.s([rz, r1], 'readdcld', '( %s -> %s e. RR )' % (A0, T1))
    t1g = w.s([rzp, w.s([rz, r1, w.inst('ltaddpos')], 'syl2anc', '( %s -> ( 0 < %s <-> 1 < ( 1 + %s ) ) )' % (A0, RZ, RZ))], 'mpbid', '( %s -> 1 < ( 1 + %s ) )' % (A0, RZ))
    t1g2 = w.s([t1g, w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), w.s([rz], 'recnd', '( %s -> %s e. CC )' % (A0, RZ))], 'addcomd', '( %s -> ( 1 + %s ) = %s )' % (A0, RZ, T1))],
               'breqtrd', '( %s -> 1 < %s )' % (A0, T1))
    zm1 = w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % A0)
    aar = w.s([w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0), w.s([zm1], 'abscld', '( %s -> ( abs ` ( Z - 1 ) ) e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, AA))
    cvm = w.s([w.s([w.s([t1r, t1g2], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, T1, T1)), w.s([aar], 'recnd', '( %s -> %s e. CC )' % (A0, AA))], 'jca',
                   '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ %s e. CC ) )' % (A0, T1, T1, AA)), w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MJ))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    ck = Closure(w, Ak, {'k': ('NN', kn), 'Z': ('CC', w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))})
    KT = '( k ^c -u %s )' % T1
    ktr = w.s([w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak), w.s([w.s([t1r], 'renegcld', '( %s -> -u %s e. RR )' % (A0, T1))], 'adantr', '( %s -> -u %s e. RR )' % (Ak, T1))],
                   'rpcxpcld', '( %s -> %s e. RR+ )' % (Ak, KT))], 'rpred', '( %s -> %s e. RR )' % (Ak, KT))
    mvr = w.s([w.s([aar], 'adantr', '( %s -> %s e. RR )' % (Ak, AA)), ktr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Ak, AA, KT))
    mk, _ = mptval(w, Ak, 'n', 'NN', '( %s x. ( n ^c -u %s ) )' % (AA, T1), 'k', kn, mp=MJ)
    mkr = w.s([mk, mvr], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, MJ))
    htc = ck.mem(HT('k', 'Z'), 'CC')
    hk, _ = mptval(w, Ak, 'm', 'NN', HT('m', 'Z'), 'k', kn, mp=HTS)
    hkc = w.s([hk, htc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, HTS))
    Ak1 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A0
    k1 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Ak1), w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'eleqtrdi', '( %s -> k e. NN )' % Ak1)
    hb = w.s([w.s([w.s([k1, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak1)], 'jca', '( %s -> ( k e. NN /\\ Z e. CC ) )' % Ak1), w.s([rzp], 'adantr', '( %s -> 0 < %s )' % (Ak1, RZ))],
                  'jca', '( %s -> ( ( k e. NN /\\ Z e. CC ) /\\ 0 < %s ) )' % (Ak1, RZ)), w.inst('zl1hvb')], 'syl',
             '( %s -> ( abs ` %s ) <_ ( %s x. ( k ^c %s ) ) )' % (Ak1, HT('k', 'Z'), AA, EXP))
    ee = w.s([w.s([w.s([rz], 'recnd', '( %s -> %s e. CC )' % (A0, RZ)), a1(w, A0, 'ax-1cn', '1 e. CC')], 'negdi2d', '( %s -> -u %s = %s )' % (A0, T1, EXP))], 'adantr',
             '( %s -> -u %s = %s )' % (Ak1, T1, EXP))
    hk1 = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Ak1, A0)), k1], 'jca', '( %s -> %s )' % (Ak1, Ak)), hk], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak1, HTS, HT('k', 'Z')))
    mk1, _ = mptval(w, Ak1, 'n', 'NN', '( %s x. ( n ^c -u %s ) )' % (AA, T1), 'k', k1, mp=MJ)
    kt1 = w.s([w.s([w.s([k1], 'nnrpd', '( %s -> k e. RR+ )' % Ak1), w.s([w.s([t1r], 'renegcld', '( %s -> -u %s e. RR )' % (A0, T1))], 'adantr', '( %s -> -u %s e. RR )' % (Ak1, T1))],
                   'rpcxpcld', '( %s -> %s e. RR+ )' % (Ak1, KT))], 'rpred', '( %s -> %s e. RR )' % (Ak1, KT))
    mc1 = w.s([w.s([w.s([aar], 'adantr', '( %s -> %s e. RR )' % (Ak1, AA)), kt1], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Ak1, AA, KT))], 'recnd',
              '( %s -> ( %s x. %s ) e. CC )' % (Ak1, AA, KT))
    rhs = chain(w, Ak1, ['( 1 x. ( %s ` k ) )' % MJ, '( 1 x. ( %s x. %s ) )' % (AA, KT), '( %s x. %s )' % (AA, KT), '( %s x. ( k ^c %s ) )' % (AA, EXP)],
                [E(w, Ak1, 'oveq2d', [mk1], '( 1 x. ( %s ` k ) )' % MJ, '( 1 x. ( %s x. %s ) )' % (AA, KT)),
                 E(w, Ak1, 'mullidd', [mc1], '( 1 x. ( %s x. %s ) )' % (AA, KT), '( %s x. %s )' % (AA, KT)),
                 E(w, Ak1, 'oveq2d', [E(w, Ak1, 'oveq2d', [ee], KT, '( k ^c %s )' % EXP)], '( %s x. %s )' % (AA, KT), '( %s x. ( k ^c %s ) )' % (AA, EXP))])
    lhs = w.s([hk1], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak1, HTS, HT('k', 'Z')))
    cmp = w.s([w.s([lhs, hb], 'eqbrtrd', '( %s -> ( abs ` ( %s ` k ) ) <_ ( %s x. ( k ^c %s ) ) )' % (Ak1, HTS, AA, EXP)), rhs], 'breqtrrd',
              '( %s -> ( abs ` ( %s ` k ) ) <_ ( 1 x. ( %s ` k ) ) )' % (Ak1, HTS, MJ))
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    w.qed([nu, a1(w, A0, '1nn', '1 e. NN'), mkr, hkc, cvm, a1(w, A0, '1re', '1 e. RR'), cmp], 'cvgcmpce', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HTS))
    go(w)

if not only or 'zl1zcl' in only:
    w = W('zl1zcl', 'The sum of the zeta continuation terms is a complex number on the open right half-plane ( ~ zl1zcv ).')
    A0 = '( Z e. CC /\\ 0 < %s )' % RZ
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
    cv = w.s([], 'zl1zcv', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HTS))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    ck = Closure(w, Ak, {'k': ('NN', kn), 'Z': ('CC', w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))})
    htc = ck.mem(HT('k', 'Z'), 'CC')
    hk, _ = mptval(w, Ak, 'm', 'NN', HT('m', 'Z'), 'k', kn, mp=HTS)
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    w.qed([nu, a1(w, A0, '1z', '1 e. ZZ'), hk, htc, cv], 'isumcl', '( %s -> %s e. CC )' % (A0, HS('Z')))
    go(w)


# ---------------------------------------------------------------- box bounds
def boxpre(_w, label, desc):
    w = W(label, desc)
    A0 = '( K e. NN /\\ %s )' % BXH
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
    lrp = w.s([], 'simprll', '( %s -> L e. RR+ )' % A0)
    rr = w.s([], 'simprlr', '( %s -> R e. RR )' % A0)
    zb = w.s([], 'simprr', '( %s -> Z e. %s )' % (A0, B_))
    b = bxctx(w, A0, lrp, rr, zb)
    zc = b['zc']
    r1 = a1(w, A0, '1re', '1 e. RR')
    az = w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)
    az0 = w.s([zc], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % A0)
    zm1 = w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % A0)
    az1 = w.s([zm1], 'abscld', '( %s -> ( abs ` ( Z - 1 ) ) e. RR )' % A0)
    az10 = w.s([zm1], 'absge0d', '( %s -> 0 <_ ( abs ` ( Z - 1 ) ) )' % A0)
    r2 = w.s([a1(w, A0, '2re', '2 e. RR'), rr], 'remulcld', '( %s -> ( 2 x. R ) e. RR )' % A0)
    r21 = w.s([r2, r1], 'readdcld', '( %s -> ( ( 2 x. R ) + 1 ) e. RR )' % A0)
    t1 = w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC'), w.inst('abs2dif2')], 'syl2anc', '( %s -> ( abs ` ( Z - 1 ) ) <_ ( ( abs ` Z ) + ( abs ` 1 ) ) )' % A0)
    t2 = w.s([t1, w.s([a1(w, A0, 'abs1', '( abs ` 1 ) = 1')], 'oveq2d', '( %s -> ( ( abs ` Z ) + ( abs ` 1 ) ) = ( ( abs ` Z ) + 1 ) )' % A0)],
             'breqtrd', '( %s -> ( abs ` ( Z - 1 ) ) <_ ( ( abs ` Z ) + 1 ) )' % A0)
    t3 = w.s([az, r2, r1, b['az']], 'leadd1dd', '( %s -> ( ( abs ` Z ) + 1 ) <_ ( ( 2 x. R ) + 1 ) )' % A0)
    t4 = w.s([az1, w.s([az, r1], 'readdcld', '( %s -> ( ( abs ` Z ) + 1 ) e. RR )' % A0), r21, t2, t3], 'letrd', '( %s -> ( abs ` ( Z - 1 ) ) <_ ( ( 2 x. R ) + 1 ) )' % A0)
    aar = w.s([az, az1], 'remulcld', '( %s -> %s e. RR )' % (A0, AA))
    aa0 = w.s([az, az1, az0, az10], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, AA))
    c1r = w.s([r2, r21], 'remulcld', '( %s -> %s e. RR )' % (A0, C1))
    aac = w.s([az, r2, az1, r21, az0, az10, b['az'], t4], 'lemul12ad', '( %s -> %s <_ %s )' % (A0, AA, C1))
    krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
    kxr = w.s([w.s([krp, w.s([w.s([b['rz']], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ)), r1], 'resubcld', '( %s -> %s e. RR )' % (A0, EXP))], 'rpcxpcld',
                   '( %s -> ( K ^c %s ) e. RR+ )' % (A0, EXP))], 'idi', '( %s -> ( K ^c %s ) e. RR+ )' % (A0, EXP))
    l1r = w.s([b['lr'], r1], 'readdcld', '( %s -> ( L + 1 ) e. RR )' % A0)
    kl1 = w.s([krp, w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % A0)], 'rpcxpcld', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR+ )' % A0)
    mono = expmono(w, A0, kn, b['rz'], b['lr'], b['lltz'])
    return w, A0, locals()


BXH = '( ( L e. RR+ /\\ R e. RR ) /\\ Z e. %s )' % B_

if not only or 'zl1hvbx' in only:
    w, A0, v = boxpre(None, 'zl1hvbx', 'The uniform bound on the zeta continuation term on an open box in the right half-plane '
                      '( ~ zl1hvb , ~ bxabs ).')
    hvb = w.s([w.s([w.s([v['kn'], v['zc']], 'jca', '( %s -> ( K e. NN /\\ Z e. CC ) )' % A0), v['b']['z0']], 'jca', '( %s -> ( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s ) )' % (A0, RZ)),
               w.inst('zl1hvb')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, HT('K', 'Z'), MV))
    m2 = w.s([v['aar'], v['c1r'], w.s([v['kxr']], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EXP)), w.s([v['kl1']], 'rpred', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR )' % A0),
              v['aa0'], w.s([v['kxr']], 'rpge0d', '( %s -> 0 <_ ( K ^c %s ) )' % (A0, EXP)), v['aac'], v['mono']], 'lemul12ad',
             '( %s -> %s <_ ( %s x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, MV, C1))
    cz = Closure(w, A0, {'K': ('NN', v['kn']), 'Z': ('CC', v['zc'])})
    w.qed([w.s([cz.mem(HT('K', 'Z'), 'CC')], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, HT('K', 'Z'))),
           w.s([v['aar'], w.s([v['kxr']], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EXP))], 'remulcld', '( %s -> %s e. RR )' % (A0, MV)),
           w.s([v['c1r'], w.s([v['kl1']], 'rpred', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR )' % A0)], 'remulcld', '( %s -> ( %s x. ( K ^c -u ( L + 1 ) ) ) e. RR )' % (A0, C1)),
           hvb, m2], 'letrd', '( %s -> ( abs ` %s ) <_ ( %s x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, HT('K', 'Z'), C1))
    go(w)

if not only or 'zl1hdbx' in only:
    w, A0, v = boxpre(None, 'zl1hdbx', 'The uniform bound on the ` z ` -derivative of the zeta continuation term on an open box '
                      'in the right half-plane ( ~ zl1hdb , ~ logp1bnd , ~ bxabs ).')
    kn = v['kn']; zc = v['zc']; rr = v['rr']; r1 = v['r1']; krp = v['krp']; lrp = v['lrp']
    lr = v['b']['lr']
    hdb = w.s([w.s([w.s([kn, zc], 'jca', '( %s -> ( K e. NN /\\ Z e. CC ) )' % A0), v['b']['z0']], 'jca', '( %s -> ( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s ) )' % (A0, RZ)),
               w.inst('zl1hdb')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A0, HD('K', 'Z'), MD))
    c2 = a1(w, A0, '2cn', '2 e. CC')
    zz2 = w.s([c2, zc], 'mulcld', '( %s -> ( 2 x. Z ) e. CC )' % A0)
    vc = w.s([zz2, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> %s e. CC )' % (A0, V_))
    vr = w.s([vc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, V_))
    v0 = w.s([vc], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, V_))
    a2z = w.s([w.s([c2, zc], 'absmuld', '( %s -> ( abs ` ( 2 x. Z ) ) = ( ( abs ` 2 ) x. ( abs ` Z ) ) )' % A0),
               w.s([w.s([a1(w, A0, '2re', '2 e. RR'), a1(w, A0, '0le2', '0 <_ 2')], 'absidd', '( %s -> ( abs ` 2 ) = 2 )' % A0)], 'oveq1d',
                   '( %s -> ( ( abs ` 2 ) x. ( abs ` Z ) ) = ( 2 x. ( abs ` Z ) ) )' % A0)], 'eqtrd', '( %s -> ( abs ` ( 2 x. Z ) ) = ( 2 x. ( abs ` Z ) ) )' % A0)
    R4 = '( 4 x. R )'
    r4 = w.s([a1(w, A0, '4re', '4 e. RR'), rr], 'remulcld', '( %s -> %s e. RR )' % (A0, R4))
    le2z = w.s([v['az'], v['r2'], a1(w, A0, '2re', '2 e. RR'), a1(w, A0, '0le2', '0 <_ 2'), v['b']['az']], 'lemul2ad', '( %s -> ( 2 x. ( abs ` Z ) ) <_ ( 2 x. ( 2 x. R ) ) )' % A0)
    e4 = w.s([w.s([c2, c2, w.s([rr], 'recnd', '( %s -> R e. CC )' % A0)], 'mulassd', '( %s -> ( ( 2 x. 2 ) x. R ) = ( 2 x. ( 2 x. R ) ) )' % A0)], 'eqcomd',
             '( %s -> ( 2 x. ( 2 x. R ) ) = ( ( 2 x. 2 ) x. R ) )' % A0)
    e4b = w.s([e4, w.s([a1(w, A0, '2t2e4', '( 2 x. 2 ) = 4')], 'oveq1d', '( %s -> ( ( 2 x. 2 ) x. R ) = %s )' % (A0, R4))], 'eqtrd', '( %s -> ( 2 x. ( 2 x. R ) ) = %s )' % (A0, R4))
    le2z2 = w.s([w.s([a2z, le2z], 'eqbrtrd', '( %s -> ( abs ` ( 2 x. Z ) ) <_ ( 2 x. ( 2 x. R ) ) )' % A0), e4b], 'breqtrd', '( %s -> ( abs ` ( 2 x. Z ) ) <_ %s )' % (A0, R4))
    tv1 = w.s([zz2, a1(w, A0, 'ax-1cn', '1 e. CC'), w.inst('abs2dif2')], 'syl2anc', '( %s -> ( abs ` %s ) <_ ( ( abs ` ( 2 x. Z ) ) + ( abs ` 1 ) ) )' % (A0, V_))
    tv2 = w.s([tv1, w.s([a1(w, A0, 'abs1', '( abs ` 1 ) = 1')], 'oveq2d', '( %s -> ( ( abs ` ( 2 x. Z ) ) + ( abs ` 1 ) ) = ( ( abs ` ( 2 x. Z ) ) + 1 ) )' % A0)],
              'breqtrd', '( %s -> ( abs ` %s ) <_ ( ( abs ` ( 2 x. Z ) ) + 1 ) )' % (A0, V_))
    tv3 = w.s([w.s([zz2], 'abscld', '( %s -> ( abs ` ( 2 x. Z ) ) e. RR )' % A0), r4, r1, le2z2], 'leadd1dd', '( %s -> ( ( abs ` ( 2 x. Z ) ) + 1 ) <_ ( %s + 1 ) )' % (A0, R4))
    R41 = '( %s + 1 )' % R4
    r41 = w.s([r4, r1], 'readdcld', '( %s -> %s e. RR )' % (A0, R41))
    vle = w.s([vr, w.s([w.s([zz2], 'abscld', '( %s -> ( abs ` ( 2 x. Z ) ) e. RR )' % A0), r1], 'readdcld', '( %s -> ( ( abs ` ( 2 x. Z ) ) + 1 ) e. RR )' % A0), r41, tv2, tv3],
              'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, V_, R41))
    r410 = w.s([a1(w, A0, '0re', '0 e. RR'), vr, r41, v0, vle], 'letrd', '( %s -> 0 <_ %s )' % (A0, R41))
    # log ( K + 1 ) <_ Q K ^ EL
    elrp = w.s([lrp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, EL))
    elr = w.s([elrp], 'rpred', '( %s -> %s e. RR )' % (A0, EL))
    LG1 = '( log ` ( K + 1 ) )'
    Q = '( ( 2 ^c %s ) / %s )' % (EL, EL)
    KE = '( K ^c %s )' % EL
    lgb = w.s([kn, elrp, w.inst('logp1bnd')], 'syl2anc', '( %s -> %s <_ ( %s x. %s ) )' % (A0, LG1, Q, KE))
    qrp = w.s([w.s([a1(w, A0, '2rp', '2 e. RR+'), elr], 'rpcxpcld', '( %s -> ( 2 ^c %s ) e. RR+ )' % (A0, EL)), elrp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, Q))
    kerp = w.s([krp, elr], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, KE))
    qk = w.s([qrp, kerp], 'rpmulcld', '( %s -> ( %s x. %s ) e. RR+ )' % (A0, Q, KE))
    k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
    lg1r = w.s([w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'relogcld', '( %s -> %s e. RR )' % (A0, LG1))
    lg10 = w.s([w.s([k1n], 'nnred', '( %s -> ( K + 1 ) e. RR )' % A0), w.s([k1n], 'nnge1d', '( %s -> 1 <_ ( K + 1 ) )' % A0), w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (A0, LG1))
    al = w.s([v['aar'], v['c1r'], lg1r, w.s([qk], 'rpred', '( %s -> ( %s x. %s ) e. RR )' % (A0, Q, KE)), v['aa0'], lg10, v['aac'], lgb], 'lemul12ad',
             '( %s -> ( %s x. %s ) <_ ( %s x. ( %s x. %s ) ) )' % (A0, AA, LG1, C1, Q, KE))
    C1Q = '( %s x. %s )' % (C1, Q)
    as1 = w.s([w.s([v['c1r']], 'recnd', '( %s -> %s e. CC )' % (A0, C1)), w.s([qrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, Q)), w.s([kerp], 'rpcnd', '( %s -> %s e. CC )' % (A0, KE))],
              'mulassd', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. %s ) ) )' % (A0, C1Q, KE, C1, Q, KE))
    al2 = w.s([al, w.s([as1], 'eqcomd', '( %s -> ( %s x. ( %s x. %s ) ) = ( %s x. %s ) )' % (A0, C1, Q, KE, C1Q, KE))], 'breqtrd', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (A0, AA, LG1, C1Q, KE))
    c1qr = w.s([v['c1r'], w.s([qrp], 'rpred', '( %s -> %s e. RR )' % (A0, Q))], 'remulcld', '( %s -> %s e. RR )' % (A0, C1Q))
    ker = w.s([kerp], 'rpred', '( %s -> %s e. RR )' % (A0, KE))
    W1 = '( ( abs ` %s ) + ( %s x. %s ) )' % (V_, AA, LG1)
    aalg = w.s([v['aar'], lg1r], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, AA, LG1))
    s1 = w.s([vr, aalg, r41, w.s([c1qr, ker], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, C1Q, KE)), vle, al2], 'le2addd',
             '( %s -> %s <_ ( %s + ( %s x. %s ) ) )' % (A0, W1, R41, C1Q, KE))
    # 1 <_ K ^ EL
    ke1 = w.s([w.s([w.s([w.s([kn], 'nnred', '( %s -> K e. RR )' % A0), w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)], 'jca', '( %s -> ( K e. RR /\\ 1 <_ K ) )' % A0),
                    w.s([a1(w, A0, '0re', '0 e. RR'), elr], 'jca', '( %s -> ( 0 e. RR /\\ %s e. RR ) )' % (A0, EL)), w.s([elrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, EL))], '3jca',
                   '( %s -> ( ( K e. RR /\\ 1 <_ K ) /\\ ( 0 e. RR /\\ %s e. RR ) /\\ 0 <_ %s ) )' % (A0, EL, EL)), w.inst('cxplea')], 'syl', '( %s -> ( K ^c 0 ) <_ %s )' % (A0, KE))
    ke1b = w.s([w.s([w.s([w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0), w.inst('cxp0')], 'syl', '( %s -> ( K ^c 0 ) = 1 )' % A0)], 'eqcomd', '( %s -> 1 = ( K ^c 0 ) )' % A0), ke1], 'eqbrtrd',
               '( %s -> 1 <_ %s )' % (A0, KE))
    s2 = w.s([w.s([w.s([r41, ker], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (A0, R41, KE)), w.s([r410, ke1b], 'jca', '( %s -> ( 0 <_ %s /\\ 1 <_ %s ) )' % (A0, R41, KE))], 'jca',
                  '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( 0 <_ %s /\\ 1 <_ %s ) ) )' % (A0, R41, KE, R41, KE)), w.inst('lemulge11')], 'syl', '( %s -> %s <_ ( %s x. %s ) )' % (A0, R41, R41, KE))
    s3 = w.s([r41, w.s([r41, ker], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, R41, KE)), w.s([c1qr, ker], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, C1Q, KE)), s2], 'leadd1dd',
             '( %s -> ( %s + ( %s x. %s ) ) <_ ( ( %s x. %s ) + ( %s x. %s ) ) )' % (A0, R41, C1Q, KE, R41, KE, C1Q, KE))
    dist = w.s([w.s([r41], 'recnd', '( %s -> %s e. CC )' % (A0, R41)), w.s([c1qr], 'recnd', '( %s -> %s e. CC )' % (A0, C1Q)), w.s([ker], 'recnd', '( %s -> %s e. CC )' % (A0, KE))], 'adddird',
               '( %s -> ( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) ) )' % (A0, C2, KE, R41, KE, C1Q, KE))
    w1r = w.s([vr, aalg], 'readdcld', '( %s -> %s e. RR )' % (A0, W1))
    c2r = w.s([r41, c1qr], 'readdcld', '( %s -> %s e. RR )' % (A0, C2))
    s4 = w.s([w1r, w.s([r41, w.s([c1qr, ker], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, C1Q, KE))], 'readdcld', '( %s -> ( %s + ( %s x. %s ) ) e. RR )' % (A0, R41, C1Q, KE)),
              w.s([w.s([r41, ker], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, R41, KE)), w.s([c1qr, ker], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, C1Q, KE))], 'readdcld',
                  '( %s -> ( ( %s x. %s ) + ( %s x. %s ) ) e. RR )' % (A0, R41, KE, C1Q, KE)), s1, s3], 'letrd',
             '( %s -> %s <_ ( ( %s x. %s ) + ( %s x. %s ) ) )' % (A0, W1, R41, KE, C1Q, KE))
    s5 = w.s([s4, w.s([dist], 'eqcomd', '( %s -> ( ( %s x. %s ) + ( %s x. %s ) ) = ( %s x. %s ) )' % (A0, R41, KE, C1Q, KE, C2, KE))], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, W1, C2, KE))
    w10 = w.s([vr, aalg, v0, w.s([v['aar'], lg1r, v['aa0'], lg10], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (A0, AA, LG1))], 'addge0d', '( %s -> 0 <_ %s )' % (A0, W1))
    kxr = w.s([v['kxr']], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EXP))
    kl1r = w.s([v['kl1']], 'rpred', '( %s -> ( K ^c -u ( L + 1 ) ) e. RR )' % A0)
    m2 = w.s([w1r, w.s([c2r, ker], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, C2, KE)), kxr, kl1r, w10, w.s([v['kxr']], 'rpge0d', '( %s -> 0 <_ ( K ^c %s ) )' % (A0, EXP)), s5, v['mono']],
             'lemul12ad', '( %s -> %s <_ ( ( %s x. %s ) x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, MD, C2, KE))
    # ( C2 K^EL ) K^-(L+1) = C2 K^-(1+EL)
    kc = w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0)
    elc = w.s([elr], 'recnd', '( %s -> %s e. CC )' % (A0, EL))
    l1r = w.s([lr, r1], 'readdcld', '( %s -> ( L + 1 ) e. RR )' % A0)
    nl1c = w.s([w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % A0)], 'recnd', '( %s -> -u ( L + 1 ) e. CC )' % A0)
    cadd = w.s([w.s([kc, w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)], 'jca', '( %s -> ( K e. CC /\\ K =/= 0 ) )' % A0), elc, nl1c, w.inst('cxpadd')], 'syl3anc',
               '( %s -> ( K ^c ( %s + -u ( L + 1 ) ) ) = ( %s x. ( K ^c -u ( L + 1 ) ) ) )' % (A0, EL, KE))
    lc = w.s([lr], 'recnd', '( %s -> L e. CC )' % A0)
    onec = a1(w, A0, 'ax-1cn', '1 e. CC')
    e1 = w.s([elc, w.s([lc, onec], 'addcld', '( %s -> ( L + 1 ) e. CC )' % A0)], 'negsubd', '( %s -> ( %s + -u ( L + 1 ) ) = ( %s - ( L + 1 ) ) )' % (A0, EL, EL))
    e2 = w.s([w.s([elc, lc, onec], 'subsub4d', '( %s -> ( ( %s - L ) - 1 ) = ( %s - ( L + 1 ) ) )' % (A0, EL, EL))], 'eqcomd', '( %s -> ( %s - ( L + 1 ) ) = ( ( %s - L ) - 1 ) )' % (A0, EL, EL))
    hv = w.s([lc, w.inst('2halves')], 'syl', '( %s -> ( %s + %s ) = L )' % (A0, EL, EL))
    e3 = chain(w, A0, ['( %s - L )' % EL, '( %s - ( %s + %s ) )' % (EL, EL, EL), '( ( %s - %s ) - %s )' % (EL, EL, EL), '( 0 - %s )' % EL, '-u %s' % EL],
               [w.s([w.s([hv], 'eqcomd', '( %s -> L = ( %s + %s ) )' % (A0, EL, EL))], 'oveq2d', '( %s -> ( %s - L ) = ( %s - ( %s + %s ) ) )' % (A0, EL, EL, EL, EL)),
                ('r', w.s([elc, elc, elc], 'subsub4d', '( %s -> ( ( %s - %s ) - %s ) = ( %s - ( %s + %s ) ) )' % (A0, EL, EL, EL, EL, EL, EL))),
                w.s([w.s([elc], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (A0, EL, EL))], 'oveq1d', '( %s -> ( ( %s - %s ) - %s ) = ( 0 - %s ) )' % (A0, EL, EL, EL, EL)),
                ('r', w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (EL, EL))], 'a1i', '( %s -> -u %s = ( 0 - %s ) )' % (A0, EL, EL)))])
    e4 = chain(w, A0, ['( ( %s - L ) - 1 )' % EL, '( -u %s - 1 )' % EL, '-u ( %s + 1 )' % EL, '-u ( 1 + %s )' % EL],
               [w.s([e3], 'oveq1d', '( %s -> ( ( %s - L ) - 1 ) = ( -u %s - 1 ) )' % (A0, EL, EL)),
                ('r', w.s([elc, onec], 'negdi2d', '( %s -> -u ( %s + 1 ) = ( -u %s - 1 ) )' % (A0, EL, EL))),
                w.s([w.s([elc, onec], 'addcomd', '( %s -> ( %s + 1 ) = ( 1 + %s ) )' % (A0, EL, EL))], 'negeqd', '( %s -> -u ( %s + 1 ) = -u ( 1 + %s ) )' % (A0, EL, EL))])
    expeq = chain(w, A0, ['( %s + -u ( L + 1 ) )' % EL, '( %s - ( L + 1 ) )' % EL, '( ( %s - L ) - 1 )' % EL, '-u ( 1 + %s )' % EL], [e1, e2, e4])
    prod = chain(w, A0, ['( %s x. ( K ^c -u ( L + 1 ) ) )' % KE, '( K ^c ( %s + -u ( L + 1 ) ) )' % EL, '( K ^c -u ( 1 + %s ) )' % EL],
                 [('r', cadd), w.s([expeq], 'oveq2d', '( %s -> ( K ^c ( %s + -u ( L + 1 ) ) ) = ( K ^c -u ( 1 + %s ) ) )' % (A0, EL, EL))])
    fin = chain(w, A0, ['( ( %s x. %s ) x. ( K ^c -u ( L + 1 ) ) )' % (C2, KE), '( %s x. ( %s x. ( K ^c -u ( L + 1 ) ) ) )' % (C2, KE), '( %s x. ( K ^c -u ( 1 + %s ) ) )' % (C2, EL)],
                [w.s([w.s([c2r], 'recnd', '( %s -> %s e. CC )' % (A0, C2)), w.s([ker], 'recnd', '( %s -> %s e. CC )' % (A0, KE)), w.s([kl1r], 'recnd', '( %s -> ( K ^c -u ( L + 1 ) ) e. CC )' % A0)],
                     'mulassd', '( %s -> ( ( %s x. %s ) x. ( K ^c -u ( L + 1 ) ) ) = ( %s x. ( %s x. ( K ^c -u ( L + 1 ) ) ) ) )' % (A0, C2, KE, C2, KE)),
                 w.s([prod], 'oveq2d', '( %s -> ( %s x. ( %s x. ( K ^c -u ( L + 1 ) ) ) ) = ( %s x. ( K ^c -u ( 1 + %s ) ) ) )' % (A0, C2, KE, C2, EL))])
    m3 = w.s([m2, fin], 'breqtrd', '( %s -> %s <_ ( %s x. ( K ^c -u ( 1 + %s ) ) ) )' % (A0, MD, C2, EL))
    cz = Closure(w, A0, {'K': ('NN', kn), 'Z': ('CC', zc)})
    w.qed([w.s([cz.mem(HD('K', 'Z'), 'CC')], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, HD('K', 'Z'))), w.s([w1r, kxr], 'remulcld', '( %s -> %s e. RR )' % (A0, MD)),
           w.s([c2r, w.s([w.s([krp, w.s([w.s([w.s([r1, elr], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A0, EL))], 'renegcld', '( %s -> -u ( 1 + %s ) e. RR )' % (A0, EL))], 'idi',
                                                         '( %s -> -u ( 1 + %s ) e. RR )' % (A0, EL))], 'rpcxpcld', '( %s -> ( K ^c -u ( 1 + %s ) ) e. RR+ )' % (A0, EL))], 'rpred',
                               '( %s -> ( K ^c -u ( 1 + %s ) ) e. RR )' % (A0, EL))], 'remulcld', '( %s -> ( %s x. ( K ^c -u ( 1 + %s ) ) ) e. RR )' % (A0, C2, EL)),
           hdb, m3], 'letrd', '( %s -> ( abs ` %s ) <_ ( %s x. ( K ^c -u ( 1 + %s ) ) ) )' % (A0, HD('K', 'Z'), C2, EL))
    go(w)


# ---------------------------------------------------------------- zl1zuh, zl1zbx, zl1zhol
INBP = lambda P: '( p e. %s |-> %s )' % (B_, HT(P, 'p'))
DINBP = lambda P: '( p e. %s |-> %s )' % (B_, HD(P, 'p'))
bxex = lambda w, ante: w.s([w.s([w.s([], 'bxopn', '%s e. %s' % (B_, TOP))], 'elexi', '%s e. _V' % B_)], 'a1i', '( %s -> %s e. _V )' % (ante, B_))


def htfv(w, ante, K, mk):
    """( ante -> ( HTF ` K ) = ( p e. BX |-> HT(K,p) ) )"""
    ex = w.s([w.s([w.s([w.s([], 'bxopn', '%s e. %s' % (B_, TOP))], 'elexi', '%s e. _V' % B_)], 'mptex', '%s e. _V' % INBP(K))], 'a1i', '( %s -> %s e. _V )' % (ante, INBP(K)))
    st, _ = mptval(w, ante, 'a', 'NN', INBP('a'), K, mk, mp=HTF, exs=ex)
    return st


def inval(w, ante, K, Y, my, cz):
    """( ante -> ( ( p e. BX |-> HT(K,p) ) ` Y ) = HT(K,Y) )"""
    st, _ = mptv(w, ante, "p", B_, HT(K, "p"), Y, my, closure=cz)
    return st


def dinval(w, ante, K, Y, my, cz):
    st, _ = mptv(w, ante, "p", B_, HD(K, "p"), Y, my, closure=cz)
    return st


if not only or 'zl1zuh' in only:
    w = W('zl1zuh', 'The zeta continuation term functions on an open box in the right half-plane satisfy the '
          'hypotheses of the uniform-limit theorem ~ uhhol ( ~ zl1hvbx , ~ zl1hdbx , ~ zl1hthol ).')
    A0 = '( L e. RR+ /\\ R e. RR )'
    lrp = w.s([], 'simpl', '( %s -> L e. RR+ )' % A0)
    rr = w.s([], 'simpr', '( %s -> R e. RR )' % A0)
    lr = w.s([lrp], 'rpred', '( %s -> L e. RR )' % A0)
    bo = a1(w, A0, 'bxopn', '%s e. %s' % (B_, TOP))
    # HTF : NN --> ( CC ^m BX )
    Aa = '( %s /\\ a e. NN )' % A0
    an = w.s([], 'simpr', '( %s -> a e. NN )' % Aa)
    Aap = '( %s /\\ p e. %s )' % (Aa, B_)
    pc = w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (Aap, B_)), w.inst('elbxi')], 'syl', '( %s -> %s )' % (Aap, INB('p'))), w.inst('simp1')], 'syl', '( %s -> p e. CC )' % Aap)
    cap = Closure(w, Aap, {'p': ('CC', pc), 'a': ('NN', w.s([an], 'adantr', '( %s -> a e. NN )' % Aap))})
    mf = w.s([cap.mem(HT('a', 'p'), 'CC'), w.s([], 'eqid', '%s = %s' % (INBP('a'), INBP('a')))], 'fmptd', '( %s -> %s : %s --> CC )' % (Aa, INBP('a'), B_))
    mm = elmapf(w, Aa, INBP('a'), bxex(w, Aa), mf, B_)
    fm = w.s([mm, w.s([], 'eqid', '%s = %s' % (HTF, HTF))], 'fmptd', '( %s -> %s : NN --> ( CC ^m %s ) )' % (A0, HTF, B_))
    # termwise HOL
    Aj = '( %s /\\ j e. NN )' % A0
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    sv = htfv(w, Aj, 'j', jn)
    hol = w.s([w.s([jn, w.s([bo], 'adantr', '( %s -> %s e. %s )' % (Aj, B_, TOP))], 'jca', '( %s -> ( j e. NN /\\ %s e. %s ) )' % (Aj, B_, TOP)), w.inst('zl1hthol')], 'syl',
              '( %s -> %s )' % (Aj, HOL(INBP('j'), B_)))
    c1_ = w.s([sv, w.s([hol], 'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Aj, INBP('j'), B_))], 'eqeltrd', '( %s -> ( %s ` j ) e. ( %s -cn-> CC ) )' % (Aj, HTF, B_))
    dm = w.s([w.s([sv], 'oveq2d', '( %s -> ( CC _D ( %s ` j ) ) = ( CC _D %s ) )' % (Aj, HTF, INBP('j')))], 'dmeqd', '( %s -> dom ( CC _D ( %s ` j ) ) = dom ( CC _D %s ) )' % (Aj, HTF, INBP('j')))
    c2_ = w.s([w.s([hol], 'simprd', '( %s -> %s C_ dom ( CC _D %s ) )' % (Aj, B_, INBP('j'))), dm], 'sseqtrrd', '( %s -> %s C_ dom ( CC _D ( %s ` j ) ) )' % (Aj, B_, HTF))
    UT = UHT(HTF, B_)
    ral = w.s([w.s([c1_, c2_], 'jca', '( %s -> %s )' % (Aj, HOL('( %s ` j )' % HTF, B_)))], 'ralrimiva', '( %s -> %s )' % (A0, UT))
    left = w.s([fm, ral], 'jca', '( %s -> ( %s : NN --> ( CC ^m %s ) /\\ %s ) )' % (A0, HTF, B_, UT))
    # the majorant M
    r1 = a1(w, A0, '1re', '1 e. RR')
    l1r = w.s([lr, r1], 'readdcld', '( %s -> ( L + 1 ) e. RR )' % A0)
    l1gt = w.s([w.s([r1, lrp, w.inst('ltaddrp')], 'syl2anc', '( %s -> 1 < ( 1 + L ) )' % A0), w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), w.s([lr], 'recnd', '( %s -> L e. CC )' % A0)], 'addcomd',
                                                                                                    '( %s -> ( 1 + L ) = ( L + 1 ) )' % A0)], 'breqtrd', '( %s -> 1 < ( L + 1 ) )' % A0)
    r2 = w.s([a1(w, A0, '2re', '2 e. RR'), rr], 'remulcld', '( %s -> ( 2 x. R ) e. RR )' % A0)
    c1r = w.s([r2, w.s([r2, r1], 'readdcld', '( %s -> ( ( 2 x. R ) + 1 ) e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, C1))
    An = '( %s /\\ n e. NN )' % A0
    nn = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    mre = w.s([w.s([c1r], 'adantr', '( %s -> %s e. RR )' % (An, C1)), w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % An),
                                                                               w.s([w.s([l1r], 'renegcld', '( %s -> -u ( L + 1 ) e. RR )' % A0)], 'adantr', '( %s -> -u ( L + 1 ) e. RR )' % An)],
                                                                              'rpcxpcld', '( %s -> ( n ^c -u ( L + 1 ) ) e. RR+ )' % An)], 'rpred', '( %s -> ( n ^c -u ( L + 1 ) ) e. RR )' % An)],
              'remulcld', '( %s -> ( %s x. ( n ^c -u ( L + 1 ) ) ) e. RR )' % (An, C1))
    mf2 = w.s([mre, w.s([], 'eqid', '%s = %s' % (MAJZ, MAJZ))], 'fmptd', '( %s -> %s : NN --> RR )' % (A0, MAJZ))
    mcv = w.s([w.s([w.s([l1r, l1gt], 'jca', '( %s -> ( ( L + 1 ) e. RR /\\ 1 < ( L + 1 ) ) )' % A0), w.s([c1r], 'recnd', '( %s -> %s e. CC )' % (A0, C1))], 'jca',
                   '( %s -> ( ( ( L + 1 ) e. RR /\\ 1 < ( L + 1 ) ) /\\ %s e. CC ) )' % (A0, C1)), w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAJZ))
    Ajy = '( %s /\\ ( j e. NN /\\ y e. %s ) )' % (A0, B_)
    jn2 = w.s([], 'simprl', '( %s -> j e. NN )' % Ajy)
    yb = w.s([], 'simprr', '( %s -> y e. %s )' % (Ajy, B_))
    yc = w.s([w.s([yb, w.inst('elbxi')], 'syl', '( %s -> %s )' % (Ajy, INB('y'))), w.inst('simp1')], 'syl', '( %s -> y e. CC )' % Ajy)
    cy = Closure(w, Ajy, {'y': ('CC', yc), 'j': ('NN', jn2)})
    BXY = '( ( L e. RR+ /\\ R e. RR ) /\\ y e. %s )' % B_
    pk = w.s([jn2, w.s([w.s([], 'simpl', '( %s -> ( L e. RR+ /\\ R e. RR ) )' % Ajy), yb], 'jca', '( %s -> %s )' % (Ajy, BXY))], 'jca', '( %s -> ( j e. NN /\\ %s ) )' % (Ajy, BXY))
    bd = w.s([pk, w.inst('zl1hvbx')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. ( j ^c -u ( L + 1 ) ) ) )' % (Ajy, HT('j', 'y'), C1))
    vv = w.s([w.s([htfv(w, Ajy, 'j', jn2)], 'fveq1d', '( %s -> ( ( %s ` j ) ` y ) = ( %s ` y ) )' % (Ajy, HTF, INBP('j'))), inval(w, Ajy, 'j', 'y', yb, cy)], 'eqtrd',
             '( %s -> ( ( %s ` j ) ` y ) = %s )' % (Ajy, HTF, HT('j', 'y')))
    mv, _ = mptval(w, Ajy, 'n', 'NN', '( %s x. ( n ^c -u ( L + 1 ) ) )' % C1, 'j', jn2, mp=MAJZ)
    bd2 = w.s([w.s([w.s([vv], 'fveq2d', '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) = ( abs ` %s ) )' % (Ajy, HTF, HT('j', 'y'))), bd], 'eqbrtrd',
                   '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s x. ( j ^c -u ( L + 1 ) ) ) )' % (Ajy, HTF, C1)), mv], 'breqtrrd', '( %s -> ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (Ajy, HTF, MAJZ))
    mb = w.s([bd2], 'ralrimivva', '( %s -> A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (A0, B_, HTF, MAJZ))
    um = w.s([mf2, mcv, mb], '3jca', '( %s -> %s )' % (A0, UHM(HTF, MAJZ, B_)))
    # the majorant R
    elrp = w.s([lrp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, EL))
    elr = w.s([elrp], 'rpred', '( %s -> %s e. RR )' % (A0, EL))
    e1r = w.s([r1, elr], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A0, EL))
    e1gt = w.s([r1, elrp, w.inst('ltaddrp')], 'syl2anc', '( %s -> 1 < ( 1 + %s ) )' % (A0, EL))
    Q = '( ( 2 ^c %s ) / %s )' % (EL, EL)
    qr = w.s([w.s([w.s([a1(w, A0, '2rp', '2 e. RR+'), elr], 'rpcxpcld', '( %s -> ( 2 ^c %s ) e. RR+ )' % (A0, EL)), elrp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, Q))], 'rpred', '( %s -> %s e. RR )' % (A0, Q))
    r4 = w.s([a1(w, A0, '4re', '4 e. RR'), rr], 'remulcld', '( %s -> ( 4 x. R ) e. RR )' % A0)
    c2r = w.s([w.s([r4, r1], 'readdcld', '( %s -> ( ( 4 x. R ) + 1 ) e. RR )' % A0), w.s([c1r, qr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, C1, Q))], 'readdcld',
              '( %s -> %s e. RR )' % (A0, C2))
    rre = w.s([w.s([c2r], 'adantr', '( %s -> %s e. RR )' % (An, C2)), w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % An), w.s([w.s([e1r], 'renegcld', '( %s -> -u ( 1 + %s ) e. RR )' % (A0, EL))], 'adantr',
                                                                                                                                  '( %s -> -u ( 1 + %s ) e. RR )' % (An, EL))], 'rpcxpcld',
                                                                          '( %s -> ( n ^c -u ( 1 + %s ) ) e. RR+ )' % (An, EL))], 'rpred', '( %s -> ( n ^c -u ( 1 + %s ) ) e. RR )' % (An, EL))], 'remulcld',
              '( %s -> ( %s x. ( n ^c -u ( 1 + %s ) ) ) e. RR )' % (An, C2, EL))
    rf = w.s([rre, w.s([], 'eqid', '%s = %s' % (MAJZD, MAJZD))], 'fmptd', '( %s -> %s : NN --> RR )' % (A0, MAJZD))
    rcv = w.s([w.s([w.s([e1r, e1gt], 'jca', '( %s -> ( ( 1 + %s ) e. RR /\\ 1 < ( 1 + %s ) ) )' % (A0, EL, EL)), w.s([c2r], 'recnd', '( %s -> %s e. CC )' % (A0, C2))], 'jca',
                   '( %s -> ( ( ( 1 + %s ) e. RR /\\ 1 < ( 1 + %s ) ) /\\ %s e. CC ) )' % (A0, EL, EL, C2)), w.inst('zsercvgc')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAJZD))
    dvj = w.s([w.s([jn2, w.s([bo], 'adantr', '( %s -> %s e. %s )' % (Ajy, B_, TOP))], 'jca', '( %s -> ( j e. NN /\\ %s e. %s ) )' % (Ajy, B_, TOP)), w.inst('zl1hdv')], 'syl',
              '( %s -> ( CC _D %s ) = %s )' % (Ajy, INBP('j'), DINBP('j')))
    svj = w.s([w.s([htfv(w, Ajy, 'j', jn2)], 'oveq2d', '( %s -> ( CC _D ( %s ` j ) ) = ( CC _D %s ) )' % (Ajy, HTF, INBP('j'))), dvj], 'eqtrd',
              '( %s -> ( CC _D ( %s ` j ) ) = %s )' % (Ajy, HTF, DINBP('j')))
    dvv = w.s([w.s([svj], 'fveq1d', '( %s -> ( ( CC _D ( %s ` j ) ) ` y ) = ( %s ` y ) )' % (Ajy, HTF, DINBP('j'))), dinval(w, Ajy, 'j', 'y', yb, cy)], 'eqtrd',
              '( %s -> ( ( CC _D ( %s ` j ) ) ` y ) = %s )' % (Ajy, HTF, HD('j', 'y')))
    KE1 = lambda k: '( %s ^c -u ( 1 + %s ) )' % (k, EL)
    tb = w.s([pk, w.inst('zl1hdbx')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (Ajy, HD('j', 'y'), C2, KE1('j')))
    rv, _ = mptval(w, Ajy, 'n', 'NN', '( %s x. %s )' % (C2, KE1('n')), 'j', jn2, mp=MAJZD)
    db2 = w.s([w.s([w.s([dvv], 'fveq2d', '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) = ( abs ` %s ) )' % (Ajy, HTF, HD('j', 'y'))), tb], 'eqbrtrd',
                   '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s x. %s ) )' % (Ajy, HTF, C2, KE1('j'))), rv], 'breqtrrd',
              '( %s -> ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (Ajy, HTF, MAJZD))
    rb = w.s([db2], 'ralrimivva', '( %s -> A. j e. NN A. y e. %s ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (A0, B_, HTF, MAJZD))
    ud = w.s([rf, rcv, rb], '3jca', '( %s -> %s )' % (A0, UHD(HTF, MAJZD, B_)))
    w.qed([left, w.s([um, ud], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, UHM(HTF, MAJZ, B_), UHD(HTF, MAJZD, B_)))], 'jca', '( %s -> %s )' % (A0, UHZ()))
    go(w)

GSZ = GSUM(HTF, B_)
ASZ = '( z e. %s |-> %s )' % (B_, HS('z'))
if not only or 'zl1zbx' in only:
    w = W('zl1zbx', 'The series of the zeta continuation terms is holomorphic on every open box in the right half-plane '
          '( ~ uhhol at ~ zl1zuh ).')
    A0 = '( L e. RR+ /\\ R e. RR )'
    hol = w.s([w.s([], 'zl1zuh', '( %s -> %s )' % (A0, UHZ())), w.inst('uhhol')], 'syl', '( %s -> %s )' % (A0, HOL(GSZ, B_)))
    Azk = '( z e. %s /\\ k e. NN )' % B_
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Azk)
    zb = w.s([], 'simpl', '( %s -> z e. %s )' % (Azk, B_))
    zc = w.s([w.s([zb, w.inst('elbxi')], 'syl', '( %s -> %s )' % (Azk, INB('z'))), w.inst('simp1')], 'syl', '( %s -> z e. CC )' % Azk)
    cz = Closure(w, Azk, {'z': ('CC', zc), 'k': ('NN', kn)})
    vv = w.s([w.s([htfv(w, Azk, 'k', kn)], 'fveq1d', '( %s -> ( ( %s ` k ) ` z ) = ( %s ` z ) )' % (Azk, HTF, INBP('k'))), inval(w, Azk, 'k', 'z', zb, cz)], 'eqtrd',
             '( %s -> ( ( %s ` k ) ` z ) = %s )' % (Azk, HTF, HT('k', 'z')))
    ge = w.s([w.s([vv], 'sumeq2dv', '( z e. %s -> sum_ k e. NN ( ( %s ` k ) ` z ) = %s )' % (B_, HTF, HS('z')))], 'mpteq2ia', '%s = %s' % (GSZ, ASZ))
    b1 = w.s([ge], 'eleq1i', '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (GSZ, B_, ASZ, B_))
    b2 = w.s([w.s([w.s([ge], 'oveq2i', '( CC _D %s ) = ( CC _D %s )' % (GSZ, ASZ))], 'dmeqi', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (GSZ, ASZ))], 'sseq2i',
             '( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) )' % (B_, GSZ, B_, ASZ))
    w.qed([hol, w.s([b1, b2], 'anbi12i', '( %s <-> %s )' % (HOL(GSZ, B_), HOL(ASZ, B_)))], 'sylib', '( %s -> %s )' % (A0, HOL(ASZ, B_)))
    go(w)

if not only or 'zl1zhol' in only:
    D = HPZ
    ASH = '( z e. %s |-> %s )' % (D, HS('z'))
    w = W('zl1zhol', 'The series of the zeta continuation terms is holomorphic on the open right half-plane '
          '( ~ zl1zbx on boxes, ~ holloc ; C5\'s ~ abhol route).')
    # G : HP 0 --> CC
    Az = 'z e. %s' % D
    bi = w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( z e. %s <-> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % D)
    both = w.s([bi], 'biimpi', '( z e. %s -> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % D)
    cl = w.s([both, w.inst('zl1zcl')], 'syl', '( z e. %s -> %s e. CC )' % (D, HS('z')))
    gf = w.s([w.s([cl], 'rgen', 'A. z e. %s %s e. CC' % (D, HS('z')))], 'idi', 'A. z e. %s %s e. CC' % (D, HS('z')))
    gf2 = w.s([w.s([], 'eqid', '%s = %s' % (ASH, ASH))], 'fmpt', '( A. z e. %s %s e. CC <-> %s : %s --> CC )' % (D, HS('z'), ASH, D))
    gff = w.s([gf, gf2], 'mpbi', '%s : %s --> CC' % (ASH, D))
    hss = w.s([], 'hpss', '%s C_ CC' % D)
    # the local box at y
    Ay = 'y e. %s' % D
    by = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( y e. %s <-> ( y e. CC /\\ 0 < ( Re ` y ) ) )' % D)], 'biimpi',
             '( y e. %s -> ( y e. CC /\\ 0 < ( Re ` y ) ) )' % D)
    yc = w.s([by], 'simpld', '( %s -> y e. CC )' % Ay)
    y0 = w.s([by], 'simprd', '( %s -> 0 < ( Re ` y ) )' % Ay)
    ry = w.s([yc], 'recld', '( %s -> ( Re ` y ) e. RR )' % Ay)
    iy = w.s([yc], 'imcld', '( %s -> ( Im ` y ) e. RR )' % Ay)
    L0 = '( ( Re ` y ) / 2 )'
    R0 = '( ( abs ` y ) + 1 )'
    BXY = BX(L0, R0)
    ryp = w.s([ry, y0], 'elrpd', '( %s -> ( Re ` y ) e. RR+ )' % Ay)
    l0rp = w.s([ryp], 'rphalfcld', '( %s -> %s e. RR+ )' % (Ay, L0))
    l0r = w.s([l0rp], 'rpred', '( %s -> %s e. RR )' % (Ay, L0))
    ay = w.s([yc], 'abscld', '( %s -> ( abs ` y ) e. RR )' % Ay)
    r0r = w.s([ay, a1(w, Ay, '1re', '1 e. RR')], 'readdcld', '( %s -> %s e. RR )' % (Ay, R0))
    l0lt = w.s([ryp, w.inst('rphalflt')], 'syl', '( %s -> %s < ( Re ` y ) )' % (Ay, L0))
    ary = w.s([yc, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` y ) ) <_ ( abs ` y ) )' % Ay)
    aiy = w.s([yc, w.inst('absimle')], 'syl', '( %s -> ( abs ` ( Im ` y ) ) <_ ( abs ` y ) )' % Ay)
    arylt = w.s([w.s([w.s([ry], 'recnd', '( %s -> ( Re ` y ) e. CC )' % Ay)], 'abscld', '( %s -> ( abs ` ( Re ` y ) ) e. RR )' % Ay), ay, r0r, ary, w.s([ay], 'ltp1d', '( %s -> ( abs ` y ) < %s )' % (Ay, R0))], 'lelttrd',
                '( %s -> ( abs ` ( Re ` y ) ) < %s )' % (Ay, R0))
    aiylt = w.s([w.s([w.s([iy], 'recnd', '( %s -> ( Im ` y ) e. CC )' % Ay)], 'abscld', '( %s -> ( abs ` ( Im ` y ) ) e. RR )' % Ay), ay, r0r, aiy, w.s([ay], 'ltp1d', '( %s -> ( abs ` y ) < %s )' % (Ay, R0))], 'lelttrd',
                '( %s -> ( abs ` ( Im ` y ) ) < %s )' % (Ay, R0))
    rypair = w.s([arylt, w.s([ry, r0r, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` ( Re ` y ) ) < %s <-> ( -u %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) ) )' % (Ay, R0, R0, R0))], 'mpbid',
                 '( %s -> ( -u %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) )' % (Ay, R0, R0))
    iypair = w.s([aiylt, w.s([iy, r0r, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` ( Im ` y ) ) < %s <-> ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) ) )' % (Ay, R0, R0, R0))], 'mpbid',
                 '( %s -> ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) )' % (Ay, R0, R0))
    inb = w.s([yc, w.s([l0lt, w.s([rypair], 'simprd', '( %s -> ( Re ` y ) < %s )' % (Ay, R0))], 'jca', '( %s -> ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) )' % (Ay, L0, R0)), iypair], '3jca',
              '( %s -> ( y e. CC /\\ ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) /\\ ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) ) )' % (Ay, L0, R0, R0, R0))
    ybx = w.s([w.s([w.s([l0r, r0r], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (Ay, L0, R0)), inb], 'jca',
                   '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( y e. CC /\\ ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) /\\ ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) ) ) )' % (Ay, L0, R0, L0, R0, R0, R0)),
               w.inst('elbxr')], 'syl', '( %s -> y e. %s )' % (Ay, BXY))
    # BXY C_ HP 0
    Aw = '( %s /\\ w e. %s )' % (Ay, BXY)
    inw = w.s([w.s([], 'simpr', '( %s -> w e. %s )' % (Aw, BXY)), w.inst('elbxi')], 'syl',
              '( %s -> ( w e. CC /\\ ( %s < ( Re ` w ) /\\ ( Re ` w ) < %s ) /\\ ( -u %s < ( Im ` w ) /\\ ( Im ` w ) < %s ) ) )' % (Aw, L0, R0, R0, R0))
    wc = w.s([inw, w.inst('simp1')], 'syl', '( %s -> w e. CC )' % Aw)
    l0w = w.s([w.s([inw, w.inst('simp2')], 'syl', '( %s -> ( %s < ( Re ` w ) /\\ ( Re ` w ) < %s ) )' % (Aw, L0, R0))], 'simpld', '( %s -> %s < ( Re ` w ) )' % (Aw, L0))
    tw = w.s([a1(w, Aw, '0re', '0 e. RR'), w.s([l0r], 'adantr', '( %s -> %s e. RR )' % (Aw, L0)), w.s([wc], 'recld', '( %s -> ( Re ` w ) e. RR )' % Aw),
              w.s([w.s([l0rp], 'rpgt0d', '( %s -> 0 < %s )' % (Ay, L0))], 'adantr', '( %s -> 0 < %s )' % (Aw, L0)), l0w], 'lttrd', '( %s -> 0 < ( Re ` w ) )' % Aw)
    whp = w.s([w.s([wc, tw], 'jca', '( %s -> ( w e. CC /\\ 0 < ( Re ` w ) ) )' % Aw),
               w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( w e. %s <-> ( w e. CC /\\ 0 < ( Re ` w ) ) )' % D)], 'a1i',
                   '( %s -> ( w e. %s <-> ( w e. CC /\\ 0 < ( Re ` w ) ) ) )' % (Aw, D))], 'mpbird', '( %s -> w e. %s )' % (Aw, D))
    bss = w.s([w.s([whp], 'ex', '( %s -> ( w e. %s -> w e. %s ) )' % (Ay, BXY, D))], 'ssrdv', '( %s -> %s C_ %s )' % (Ay, BXY, D))
    ASB = '( z e. %s |-> %s )' % (BXY, HS('z'))
    res = w.s([bss, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (Ay, ASH, BXY, ASB))
    bh = w.s([w.s([l0rp, r0r], 'jca', '( %s -> ( %s e. RR+ /\\ %s e. RR ) )' % (Ay, L0, R0)), w.inst('zl1zbx')], 'syl', '( %s -> %s )' % (Ay, HOL(ASB, BXY)))
    dss = w.s([w.s([bh], 'simprd', '( %s -> %s C_ dom ( CC _D %s ) )' % (Ay, BXY, ASB)),
               w.s([w.s([res], 'oveq2d', '( %s -> ( CC _D ( %s |` %s ) ) = ( CC _D %s ) )' % (Ay, ASH, BXY, ASB))], 'dmeqd', '( %s -> dom ( CC _D ( %s |` %s ) ) = dom ( CC _D %s ) )' % (Ay, ASH, BXY, ASB))],
              'sseqtrrd', '( %s -> %s C_ dom ( CC _D ( %s |` %s ) ) )' % (Ay, BXY, ASH, BXY))
    LOC = lambda u: '( y e. %s /\\ %s C_ %s /\\ %s C_ dom ( CC _D ( %s |` %s ) ) )' % (u, u, D, u, ASH, u)
    sub = w.s([w.s([], 'eleq2', '( u = %s -> ( y e. u <-> y e. %s ) )' % (BXY, BXY)), w.s([], 'sseq1', '( u = %s -> ( u C_ %s <-> %s C_ %s ) )' % (BXY, D, BXY, D)),
               w.s([w.s([], 'id', '( u = %s -> u = %s )' % (BXY, BXY)), w.s([w.s([w.s([], 'reseq2', '( u = %s -> ( %s |` u ) = ( %s |` %s ) )' % (BXY, ASH, ASH, BXY))], 'oveq2d',
                                                                              '( u = %s -> ( CC _D ( %s |` u ) ) = ( CC _D ( %s |` %s ) ) )' % (BXY, ASH, ASH, BXY))], 'dmeqd',
                                                                         '( u = %s -> dom ( CC _D ( %s |` u ) ) = dom ( CC _D ( %s |` %s ) ) )' % (BXY, ASH, ASH, BXY))], 'sseq12d',
                   '( u = %s -> ( u C_ dom ( CC _D ( %s |` u ) ) <-> %s C_ dom ( CC _D ( %s |` %s ) ) ) )' % (BXY, ASH, BXY, ASH, BXY))], '3anbi123d',
              '( u = %s -> ( %s <-> %s ) )' % (BXY, LOC('u'), LOC(BXY)))
    bo = a1(w, Ay, 'bxopn', '%s e. %s' % (BXY, TOP))
    rsp = w.s([sub], 'rspcev', '( ( %s e. %s /\\ %s ) -> E. u e. %s %s )' % (BXY, TOP, LOC(BXY), TOP, LOC('u')))
    ex = w.s([w.s([bo, w.s([ybx, bss, dss], '3jca', '( %s -> %s )' % (Ay, LOC(BXY)))], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (Ay, BXY, TOP, LOC(BXY))), rsp], 'syl',
             '( %s -> E. u e. %s %s )' % (Ay, TOP, LOC('u')))
    ral = w.s([ex], 'rgen', 'A. y e. %s E. u e. %s %s' % (D, TOP, LOC('u')))
    w.qed([w.s([w.s([gff, hss], 'pm3.2i', '( %s : %s --> CC /\\ %s C_ CC )' % (ASH, D, D)), ral], 'pm3.2i',
               '( ( %s : %s --> CC /\\ %s C_ CC ) /\\ A. y e. %s E. u e. %s %s )' % (ASH, D, D, D, TOP, LOC('u'))), w.inst('holloc')], 'ax-mp', HOL(ASH, D))
    go(w)
