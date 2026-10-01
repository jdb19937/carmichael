"""Sortie KD1: helpers and the frozen statements (KDerivDetect.lean 162-1480: the frozen definitions, the
Landau remainder with its Cauchy estimate on squares, the pole derivatives, step 1, far zeros, the general-k
diagonal bound, the Turan event).

    python3 tools/kd1lib.py print                                   # the frozen table
    MM_DB=sorties/kd1.mm python3 tools/kd1lib.py check [LABEL...]    # grammar check (mmatch)

Letters.  Headlines: character N X, height T, eta E, exponent K (J for the Turan count), zero sum q over the
square zero set ZD (binder r), Dirichlet sum n (LFN binds s k i).  Generic Cauchy lemmas: F D P R K, integrand
binder z (rectintcau/ef2psa forbid it in class variables), frame binder u.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from tm import W
import lin
import cl as _cl
from cl import lift, Closure
from c9lib import SQ, HP0, CHI, LFN, R138
lin.FASTPATH = True

DB = 'sorties/kd1.mm'


def stmt(label):
    """the assertion of LABEL from sorties/kd1.mm or carmichael.mm, without |-"""
    for fn in (DB, 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- objects -----------------------------------------------------------------------
HOLF = lambda F, D: '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (F, D, D, F)
HP = lambda T: "( `' Re \" ( %s (,) +oo ) )" % T
CT = lambda t: '( 2 + ( _i x. %s ) )' % t
ONE = lambda t: '( 1 + ( _i x. %s ) )' % t
S0 = lambda E='E', T='T': '( ( 1 + %s ) + ( _i x. %s ) )' % (E, T)
ZD = lambda T='T': '{ r e. %s | ( %s ` r ) = 0 }' % (SQ(CT(T), R138), LFN)
MU = lambda q='q': '( %s holord %s )' % (LFN, q)
CHV = lambda n: '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) )' % n
LOGX = '( log ` ( N x. ( ( abs ` T ) + 2 ) ) )'
KLAN = '; ; ; ; ; ; ; 1 7 5 0 0 0 0 0'
KL = '( %s x. %s )' % (KLAN, LOGX)
R120 = '( 1 / ; 2 0 )'


def LSK(K='K', S='S', n='n'):
    """LSeries ( log^K . chi . Lam ) at S"""
    return 'sum_ %s e. NN ( ( ( ( log ` %s ) ^ %s ) x. ( %s x. ( Lam ` %s ) ) ) x. ( %s ^c -u %s ) )' % (
        n, n, K, CHV(n), n, n, S)


def DIAG(K, X, n='n'):
    """sum Lam(n) (log n)^K n^-X"""
    return 'sum_ %s e. NN ( ( ( Lam ` %s ) x. ( ( log ` %s ) ^ %s ) ) x. ( %s ^c -u %s ) )' % (n, n, n, K, n, X)


def DIAGSEQ(K, X, n='n'):
    return 'seq 1 ( + , ( %s e. NN |-> ( ( ( Lam ` %s ) x. ( ( log ` %s ) ^ %s ) ) x. ( %s ^c -u %s ) ) ) )' % (n, n, n, K, n, X)


def ZSUB(Z, cond, p='p'):
    return '{ %s e. %s | %s }' % (p, Z, cond)


# frame of the square SQ(P,R) (the carrier rectint reads)
def FRM(A, B):
    b1 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (B, A)
    a1 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (A, B)
    return '( ( ( %s cseg %s ) u. ( %s cseg %s ) ) u. ( ( %s cseg %s ) u. ( %s cseg %s ) ) )' % (A, b1, b1, B, B, a1, a1, A)


def QLO(P, R): return '( %s - ( %s + ( _i x. %s ) ) )' % (P, R, R)
def QHI(P, R): return '( %s + ( %s + ( _i x. %s ) ) )' % (P, R, R)
def FSQ(P, R): return FRM(QLO(P, R), QHI(P, R))


def TCI(F, P, R, M, z='z'):
    """Cauchy kernel F(z)/(z-P)^(M+1) on the punctured square (ef2psa's integrand)"""
    return '( %s e. ( %s \\ { %s } ) |-> ( ( %s ` %s ) / ( ( %s - %s ) ^ ( %s + 1 ) ) ) )' % (
        z, SQ(P, R), P, F, z, z, P, M)


def TC(F, P, R, M, z='z'):
    """the M-th Taylor coefficient of F at P by the boundary integral of SQ(P,R)"""
    return '( ( %s rectint <. %s , %s >. ) / ( 2 x. ( _i x. _pi ) ) )' % (TCI(F, P, R, M, z), QLO(P, R), QHI(P, R))


def DS(A, T, z='z', k='k'):
    """Dirichlet series mapping on the half-plane Re > T (C3's dserdv form)"""
    return '( %s e. %s |-> sum_ %s e. NN ( ( %s ` %s ) x. ( %s ^c -u %s ) ) )' % (z, HP(T), k, A, k, k, z)


# frozen parameters (KDerivDetect 167-174), Ndet's constant from sdzc: 70000000 . 6 . 2 = 840000000
CNDET = '; ; ; ; ; ; ; ; 8 4 0 0 0 0 0 0 0'
def NDET(E='E', L='L'): return '( |^ ` ( 6 + ( ( %s x. %s ) x. %s ) ) )' % (CNDET, E, L)
def MDET(E='E', L='L'): return '( 6 x. %s )' % NDET(E, L)
def XONE(E='E', L='L'): return '( exp ` ( %s / ( ; 1 6 x. %s ) ) )' % (MDET(E, L), E)
def XTWO(E='E', L='L'): return '( exp ` ( ( ; 1 6 x. %s ) / %s ) )' % (MDET(E, L), E)
def PWS(T='T', Y='Y', U='U', p='p', a='a'):
    """primeWindowSum chi T Y U = sum over primes Y < p <_ U of chi(p) log p p^(-1 - i T)"""
    return 'sum_ %s e. { %s e. ( 1 ... ( |_ ` %s ) ) | ( %s e. Prime /\\ %s < %s ) } ( ( %s x. ( log ` %s ) ) x. ( %s ^c ( -u 1 - ( %s x. _i ) ) ) )' % (
        p, a, U, a, Y, a, CHV(p), p, p, T)


# ---- frozen statements -------------------------------------------------------------
S = {}
AB = '( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) )'
S['kdftc'] = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) /\\ '
              '( ( G : U --> CC /\\ ( CC _D G ) = F ) /\\ ( F e. ( U -cn-> CC ) /\\ %s C_ U ) ) ) -> '
              '( F rectint <. A , B >. ) = 0 )') % FRM('A', 'B')
SQH = '( P e. CC /\\ R e. RR+ /\\ %s C_ D )' % SQ('P', 'R')
S['kdibp'] = '( ( %s /\\ %s /\\ K e. NN0 ) -> %s = ( ( K + 1 ) x. %s ) )' % (
    HOLF('F', 'D'), SQH, TC('( CC _D F )', 'P', 'R', 'K'), TC('F', 'P', 'R', '( K + 1 )'))
S['kdholdn'] = '( ( %s /\\ K e. NN0 ) -> %s )' % (HOLF('F', 'D'), HOLF('( ( CC Dn F ) ` K )', 'D'))
S['kdcdn'] = '( ( %s /\\ %s /\\ K e. NN0 ) -> ( ( ( CC Dn F ) ` K ) ` P ) = ( ( ! ` K ) x. %s ) )' % (
    HOLF('F', 'D'), SQH, TC('F', 'P', 'R', 'K'))
S['kdcest'] = ('( ( ( F e. ( D -cn-> CC ) /\\ %s ) /\\ ( K e. NN0 /\\ M e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ M ) ) -> '
               '( abs ` %s ) <_ ( ( 2 x. M ) / ( R ^ K ) ) )') % (SQH, FSQ('P', 'R'), TC('F', 'P', 'R', 'K'))

AGR = '( A : NN --> CC /\\ C e. RR /\\ ( B e. RR+ /\\ A. m e. NN ( abs ` ( A ` m ) ) <_ ( C x. ( m ^c B ) ) ) )'
S['kddsdv'] = '( ( %s /\\ ( T e. RR /\\ ( 1 + B ) < T ) ) -> ( %s /\\ ( CC _D %s ) = ( z e. %s |-> sum_ k e. NN -u ( ( ( A ` k ) x. ( log ` k ) ) x. ( k ^c -u z ) ) ) ) )' % (
    AGR, HOLF(DS('A', 'T'), HP('T')), DS('A', 'T'), HP('T'))
S['kddsdn'] = ('( ( %s /\\ ( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T ) /\\ K e. NN0 ) -> ( ( CC Dn %s ) ` K ) = '
               '( z e. %s |-> sum_ k e. NN ( ( -u ( log ` k ) ^ K ) x. ( ( A ` k ) x. ( k ^c -u z ) ) ) ) )') % (AGR, DS('A', 'T'), HP('T'))
PL = '( z e. ( CC \\ { Q } ) |-> ( 1 / ( z - Q ) ) )'
S['kdpoledn'] = ('( ( Q e. CC /\\ K e. NN0 ) -> ( ( CC Dn %s ) ` K ) = '
                 '( z e. ( CC \\ { Q } ) |-> ( ( ( -u 1 ^ K ) x. ( ! ` K ) ) / ( ( z - Q ) ^ ( K + 1 ) ) ) ) )') % PL
S['kdlogdv'] = ('( ( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) ) -> ( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = '
                '-u sum_ k e. NN ( ( %s x. ( Lam ` k ) ) x. ( k ^c -u S ) ) )') % (CHI, LFN, LFN, CHV('k'))

KDH = '( %s /\\ ( T e. RR /\\ ( E e. RR+ /\\ E <_ %s ) /\\ K e. NN0 ) )' % (CHI, R120)
S['kdrep'] = '( %s -> ( abs ` ( sum_ q e. %s ( %s / ( ( %s - q ) ^ ( K + 1 ) ) ) + ( %s / ( ! ` K ) ) ) ) <_ ( ( 2 x. ( 3 ^ K ) ) x. %s ) )' % (
    KDH, ZD(), MU(), S0(), LSK('K', S0()), KL)

# far zeros
S['kdre1'] = '( ( %s /\\ T e. RR /\\ Q e. %s ) -> ( Re ` Q ) <_ 1 )' % (CHI, ZD())
S['kddist'] = ('( ( ( E e. RR /\\ 0 <_ E /\\ T e. RR ) /\\ ( Q e. CC /\\ ( Re ` Q ) <_ 1 ) ) -> '
               '( abs ` ( Q - %s ) ) <_ ( abs ` ( %s - Q ) ) )') % (ONE('T'), S0())
S['kdl2'] = '( ( %s /\\ ( T e. RR /\\ E e. RR+ /\\ E <_ %s ) ) -> sum_ q e. %s ( %s / ( ( abs ` ( %s - q ) ) ^ 2 ) ) <_ ( ( 1 / E ) x. ( ( ( ( 5 / 4 ) / E ) + 5 ) + %s ) ) )' % (
    CHI, R120, ZD(), MU(), S0(), KL)
S['kdfar'] = ('( ( ( ( %s /\\ T e. RR ) /\\ ( S e. CC /\\ A. p e. %s 0 < ( abs ` ( S - p ) ) ) /\\ ( Y C_ %s /\\ R e. RR+ /\\ A. p e. Y R < ( abs ` ( S - p ) ) ) ) /\\ '
              '( J e. NN0 /\\ A e. RR /\\ sum_ p e. %s ( %s / ( ( abs ` ( S - p ) ) ^ 2 ) ) <_ A ) ) -> '
              '( abs ` sum_ q e. Y ( %s / ( ( S - q ) ^ ( J + 2 ) ) ) ) <_ ( A / ( R ^ J ) ) )') % (CHI, ZD(), ZD(), ZD(), MU('p'), MU())

# diagonal
S['kdlogpow'] = '( ( B e. RR+ /\\ K e. NN0 /\\ M e. NN ) -> ( ( log ` M ) ^ K ) <_ ( ( ( ! ` K ) x. ( M ^c B ) ) / ( B ^ K ) ) )'
S['kddiag'] = '( ( ( V e. RR+ /\\ W e. RR+ /\\ W <_ 1 ) /\\ K e. NN0 ) -> ( %s e. dom ~~> /\\ %s <_ ( ( ( ! ` K ) / ( V ^ K ) ) x. ( ( ( 5 / 4 ) / W ) + 5 ) ) ) )' % (
    DIAGSEQ('K', '( 1 + ( V + W ) )'), DIAG('K', '( 1 + ( V + W ) )'))
S['kddiag2'] = '( ( ( U e. RR+ /\\ U <_ %s ) /\\ K e. NN0 ) -> ( %s e. dom ~~> /\\ %s <_ ( ( ( ( ! ` K ) x. ( exp ` 1 ) ) x. ( ( 5 / 4 ) x. ( K + 2 ) ) ) / ( U ^ ( K + 1 ) ) ) ) )' % (
    R120, DIAGSEQ('K', '( 1 + U )'), DIAG('K', '( 1 + U )'))

# bridge
NXH = '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'
S['kdterm'] = ('( ( %s /\\ ( S e. CC /\\ K e. NN0 /\\ M e. NN ) ) -> ( abs ` ( ( ( ( log ` M ) ^ K ) x. ( %s x. ( Lam ` M ) ) ) x. ( M ^c -u S ) ) ) '
               '<_ ( ( ( Lam ` M ) x. ( ( log ` M ) ^ K ) ) x. ( M ^c -u ( Re ` S ) ) ) )') % (NXH, CHV('M'))
S['kdlsb'] = ('( ( %s /\\ ( E e. RR+ /\\ E <_ 1 ) /\\ ( S e. CC /\\ ( Re ` S ) = ( 1 + E ) /\\ K e. NN0 ) ) -> '
              '( seq 1 ( + , ( n e. NN |-> ( ( ( ( log ` n ) ^ K ) x. ( %s x. ( Lam ` n ) ) ) x. ( n ^c -u S ) ) ) ) e. dom ~~> /\\ '
              '( abs ` %s ) <_ %s ) )') % (NXH, CHV('n'), LSK('K', 'S'), DIAG('K', '( 1 + E )'))
S['kdnear'] = ('( ( %s /\\ ( T e. RR /\\ E e. RR+ /\\ ( W e. RR+ /\\ ( W + E ) <_ %s ) ) ) -> '
               'sum_ q e. %s %s <_ ( 6 + ( ( ; ; ; ; ; ; ; 7 0 0 0 0 0 0 0 x. ( W + E ) ) x. %s ) ) )') % (
    CHI, R120, ZSUB(ZD(), '( abs ` ( %s - p ) ) <_ W' % S0()), MU(), LOGX)

# Turan event
S['kdmemzd'] = ('( ( ( %s /\\ T e. RR ) /\\ ( Q e. CC /\\ ( %s ` Q ) = 0 ) /\\ ( W e. RR /\\ W <_ ( 1 / 2 ) /\\ '
                '( abs ` ( Q - %s ) ) <_ W ) ) -> Q e. %s )') % (CHI, LFN, ONE('T'), ZD())
Z6 = ZSUB(ZD(), '( abs ` ( p - %s ) ) <_ ( 6 x. E )' % ONE('T'))
S['kdturan'] = ('( ( ( %s /\\ ( T e. RR /\\ E e. RR+ /\\ E <_ ( 1 / 2 ) ) ) /\\ ( ( J e. NN /\\ sum_ q e. %s %s <_ J ) /\\ '
                'E. p e. CC ( ( %s ` p ) = 0 /\\ ( abs ` ( p - %s ) ) <_ E ) /\\ M e. NN0 ) ) -> '
                'E. l e. ( ( M + 1 ) ... ( M + J ) ) ( ( ( J / ( ( 8 x. ( exp ` 1 ) ) x. ( M + J ) ) ) ^ J ) x. ( ( 1 / ( 2 x. E ) ) ^ l ) ) '
                '<_ ( abs ` sum_ q e. %s ( %s / ( ( %s - q ) ^ l ) ) ) )') % (CHI, Z6, MU(), LFN, ONE('T'), Z6, MU(), S0())

# frozen parameters
S['kdndet'] = ('( ( ( E e. RR /\\ 0 <_ E ) /\\ ( L e. RR /\\ 0 <_ L ) ) -> ( %s e. NN /\\ 6 <_ %s /\\ '
               '( ( 6 + ( ( %s x. E ) x. L ) ) <_ %s /\\ %s < ( 7 + ( ( %s x. E ) x. L ) ) ) ) )') % (
    NDET(), NDET(), CNDET, NDET(), NDET(), CNDET)
S['kdxlt'] = '( ( E e. RR+ /\\ L e. RR /\\ 0 <_ L ) -> ( %s e. NN /\\ %s < %s ) )' % (MDET(), XONE(), XTWO())

HEAD = ['kdrep', 'kdcdn', 'kdcest', 'kdl2', 'kdfar', 'kddist', 'kdre1', 'kddiag', 'kddiag2', 'kdlogpow', 'kdterm',
        'kdlsb', 'kdnear', 'kdmemzd', 'kdturan', 'kdndet', 'kdxlt']


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'kd1gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'kd1gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=kd1gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::kd1gc%s.1 |- %s\n' % (lab, S[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch', MM_DB=DB)
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


# ---- helpers ----------------------------------------------------------------------------
def holeq(w, ante, eq, A, B, D):
    """( ante -> ( HOLF(A,D) <-> HOLF(B,D) ) ) from eq : ( ante -> A = B )"""
    e1 = w.s([eq], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (ante, A, D, B, D))
    d1 = w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (ante, A, B))
    d2 = w.s([d1], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (ante, A, B))
    d3 = w.s([d2], 'sseq2d', '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (ante, D, A, D, B))
    return w.s([e1, d3], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (ante, HOLF(A, D), HOLF(B, D)))


def pmcc(w, ante, hol, F, D):
    """( ante -> F e. ( CC ^pm CC ) ) from hol : ( ante -> HOLF(F, D) ); also returns ( ante -> D C_ CC )"""
    cn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (ante, F, D))
    ff = w.s([cn, w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (ante, F, D))
    ds = w.s([cn, w.inst('cncfrss')], 'syl', '( %s -> %s C_ CC )' % (ante, D))
    cx = w.s([], 'cnex', 'CC e. _V')
    cc2 = w.s([w.s([cx, cx], 'pm3.2i', '( CC e. _V /\\ CC e. _V )')], 'a1i', '( %s -> ( CC e. _V /\\ CC e. _V ) )' % ante)
    j = w.s([ff, ds], 'jca', '( %s -> ( %s : %s --> CC /\\ %s C_ CC ) )' % (ante, F, D, D))
    return w.s([cc2, j, w.inst('elpm2r')], 'syl2anc', '( %s -> %s e. ( CC ^pm CC ) )' % (ante, F)), ds


def fvmd(w, ante, M, X, val, xin, valcl, eq, var='z'):
    """( ante -> ( M ` X ) = val ) for M = ( var e. dom |-> body ); eq : ( var = X -> body = val ) closed,
    xin : ( ante -> X e. dom ), valcl : ( ante -> val e. V )"""
    from cl import formula_of
    f = formula_of(w, eq)
    rhs = f.split(' -> ', 1)[1][:-2]
    m1 = w.s([w.s([], 'eqid', '%s = %s' % (M, M))], 'a1i', '( %s -> %s = %s )' % (ante, M, M))
    m2 = w.s([eq], 'adantl', '( ( %s /\\ %s = %s ) -> %s )' % (ante, var, X, rhs))
    return w.s([m1, m2, xin, valcl], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ante, M, X, val))


# ---- the combined Dirichlet-plus-poles function (kdpsidn, kdtcs) ------------------------
def VSET(T='T', Z='Z'): return '( %s \\ %s )' % (HP(T), Z)
def S1(x, z): return 'sum_ k e. NN ( ( -u ( log ` k ) ^ %s ) x. ( ( A ` k ) x. ( k ^c -u %s ) ) )' % (x, z)
def PQ(x, z, q='q'): return '( ( ( -u 1 ^ %s ) x. ( ! ` %s ) ) / ( ( %s - %s ) ^ ( %s + 1 ) ) )' % (x, x, z, q, x)
def PSIK(x, z): return '( -u %s - sum_ q e. Z ( ( W ` q ) x. %s ) )' % (S1(x, z), PQ(x, z))
def PSI(T='T'): return '( z e. %s |-> %s )' % (VSET(T), PSIK('0', 'z'))
ZH = '( Z e. Fin /\\ Z C_ CC /\\ W : Z --> CC )'
S['kdpsidn'] = ('( ( ( ( %s /\\ ( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T ) ) /\\ %s ) /\\ K e. NN0 ) -> '
                '( %s /\\ ( ( CC Dn %s ) ` K ) = ( z e. %s |-> %s ) ) )') % (AGR, ZH, HOLF(PSI(), VSET()), PSI(), VSET(), PSIK('K', 'z'))

S['kdtcs'] = ('( ( ( %s /\\ ( P e. CC /\\ R e. RR+ /\\ %s C_ D ) ) /\\ ( ( %s /\\ ( T e. RR /\\ ( 1 + ( 2 x. B ) ) < T ) ) /\\ %s ) /\\ '
              '( %s C_ %s /\\ A. z e. %s ( G ` z ) = %s /\\ K e. NN0 ) ) -> ( ( ( CC Dn G ) ` K ) ` P ) = %s )') % (
    HOLF('G', 'D'), SQ('P', 'R'), AGR, ZH, SQ('P', 'R'), VSET(), SQ('P', 'R'), PSIK('0', 'z'), PSIK('K', 'P'))

S['kdfrm'] = ('( ( Z e. Fin /\\ Z C_ CC /\\ P e. CC ) -> E. r e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) A. u e. %s -. u e. Z )') % FSQ('P', 'r')

def OREC(A, B): return "( ( `' Re \" ( ( Re ` %s ) (,) ( Re ` %s ) ) ) i^i ( `' Im \" ( ( Im ` %s ) (,) ( Im ` %s ) ) ) )" % (A, B, A, B)
A13 = QLO(CT('T'), R138); B13 = QHI(CT('T'), R138)
O13 = OREC(A13, B13)
S['kdgeo'] = ('( ( T e. RR /\\ ( E e. RR+ /\\ E <_ %s ) /\\ R e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) ) -> ( ( %s C_ %s /\\ A. u e. %s ( abs ` ( u - %s ) ) <_ ( 3 / 2 ) ) /\\ '
              '( %s C_ %s /\\ %s C_ %s ) ) )') % (R120, SQ(S0(), 'R'), O13, SQ(S0(), 'R'), CT('T'), SQ(S0(), '( E / 2 )'), O13, SQ(S0(), '( E / 2 )'), HP('( 1 + ( E / 4 ) )'))



def sqctx2(w, A0, P, R, pc, rp):
    """corners, P inside, corner order, frame in SQ minus P for SQ(P,R) with P, R expressions;
    pc : ( A0 -> P e. CC ), rp : ( A0 -> R e. RR+ )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    A, B = QLO(P, R), QHI(P, R)
    rr = s([rp], 'rpred', '%s e. RR' % R)
    rc = s([rr], 'recnd', '%s e. CC' % R)
    ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
    irc = s([ic, rc], 'mulcld', '( _i x. %s ) e. CC' % R)
    ri = s([rc, irc], 'addcld', '( %s + ( _i x. %s ) ) e. CC' % (R, R))
    ac = s([pc, ri], 'subcld', '%s e. CC' % A)
    bc = s([pc, ri], 'addcld', '%s e. CC' % B)
    ab = s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (A, B))
    z0 = s([pc], 'subidd', '( %s - %s ) = 0' % (P, P))
    a0 = s([z0], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` 0 )' % (P, P))
    ab0 = w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % A0)
    a00 = s([a0, ab0], 'eqtrd', '( abs ` ( %s - %s ) ) = 0' % (P, P))
    r0 = s([rp], 'rpgt0d', '0 < %s' % R)
    lt = s([a00, r0], 'eqbrtrd', '( abs ` ( %s - %s ) ) < %s' % (P, P, R))
    INT = '( %s e. CC /\\ ( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) ) )' % (
        P, A, P, P, B, A, P, P, B)
    j1 = s([pc, rr], 'jca', '( %s e. CC /\\ %s e. RR )' % (P, R))
    j2 = s([pc, lt], 'jca', '( %s e. CC /\\ ( abs ` ( %s - %s ) ) < %s )' % (P, P, P, R))
    inn = s([j1, j2, w.inst('sqint')], 'syl2anc', INT)
    rl = s([inn], 'simprd', '( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) )' % (A, P, P, B, A, P, P, B))
    re_ = s([rl], 'simpld', '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (A, P, P, B))
    im_ = s([rl], 'simprd', '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (A, P, P, B))
    ra = s([ac], 'recld', '( Re ` %s ) e. RR' % A); rb = s([bc], 'recld', '( Re ` %s ) e. RR' % B)
    ia = s([ac], 'imcld', '( Im ` %s ) e. RR' % A); ib = s([bc], 'imcld', '( Im ` %s ) e. RR' % B)
    rpr = s([pc], 'recld', '( Re ` %s ) e. RR' % P); ipr = s([pc], 'imcld', '( Im ` %s ) e. RR' % P)
    r1 = s([re_], 'simpld', '( Re ` %s ) < ( Re ` %s )' % (A, P)); r2 = s([re_], 'simprd', '( Re ` %s ) < ( Re ` %s )' % (P, B))
    i1 = s([im_], 'simpld', '( Im ` %s ) < ( Im ` %s )' % (A, P)); i2 = s([im_], 'simprd', '( Im ` %s ) < ( Im ` %s )' % (P, B))
    rlt = s([ra, rpr, rb, r1, r2], 'lttrd', '( Re ` %s ) < ( Re ` %s )' % (A, B))
    ilt = s([ia, ipr, ib, i1, i2], 'lttrd', '( Im ` %s ) < ( Im ` %s )' % (A, B))
    rle = s([ra, rb, rlt], 'ltled', '( Re ` %s ) <_ ( Re ` %s )' % (A, B))
    ile = s([ia, ib, ilt], 'ltled', '( Im ` %s ) <_ ( Im ` %s )' % (A, B))
    ordr = s([rle, ile], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (A, B, A, B))
    inp = s([ab, inn], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ %s )' % (A, B, INT))
    fr = s([inp, w.inst('crectfrp')], 'syl', '%s C_ ( %s \\ { %s } )' % (FRM(A, B), SQ(P, R), P))
    fru = s([ab, ordr, w.inst('crectfru')], 'syl2anc', '%s C_ %s' % (FRM(A, B), SQ(P, R)))
    return dict(A=A, B=B, ac=ac, bc=bc, ab=ab, INT=INT, inn=inn, ordr=ordr, fr=fr, fru=fru, rr=rr, rc=rc, inp=inp)

S['kdrem'] = ('( ( %s /\\ T e. RR ) -> E. g ( %s /\\ A. z e. %s ( ( %s ` z ) =/= 0 -> ( g ` z ) = ( ( ( ( CC _D %s ) ` z ) / ( %s ` z ) ) - sum_ q e. %s ( %s / ( z - q ) ) ) ) ) )') % (
    CHI, HOLF('g', O13), O13, LFN, LFN, LFN, ZD(), MU())

HGP = lambda g='g': '( %s /\\ A. z e. %s ( ( %s ` z ) =/= 0 -> ( %s ` z ) = ( ( ( ( CC _D %s ) ` z ) / ( %s ` z ) ) - sum_ q e. %s ( %s / ( z - q ) ) ) ) )' % (
    HOLF(g, O13), O13, LFN, g, LFN, LFN, ZD(), MU())
CVM = '( n e. NN |-> ( %s x. ( Lam ` n ) ) )' % CHV('n')
WMM = '( p e. %s |-> %s )' % (ZD(), MU('p'))
def PSINST(K, P):
    from c8lib import tsub
    return tsub(PSIK(K, P), {'A': CVM, 'W': WMM, 'Z': ZD()})
S['kdrepg'] = '( ( %s /\\ %s ) -> ( ( ( CC Dn g ) ` K ) ` %s ) = %s )' % (KDH, HGP(), S0(), PSINST('K', S0()))
S['kdrepb'] = '( ( %s /\\ %s ) -> ( abs ` ( ( ( CC Dn g ) ` K ) ` %s ) ) <_ ( ( ! ` K ) x. ( ( 2 x. ( 3 ^ K ) ) x. %s ) ) )' % (KDH, HGP(), S0(), KL)

S['kdps0'] = ('( ( ( ( %s /\\ T e. RR ) /\\ z e. CC ) /\\ -. z e. %s ) -> %s = ( -u sum_ k e. NN ( ( %s x. ( Lam ` k ) ) x. ( k ^c -u z ) ) - sum_ q e. %s ( %s / ( z - q ) ) ) )') % (
    CHI, ZD(), PSINST('0', 'z'), CHV('k'), ZD(), MU())
def S1I(K, P): return 'sum_ k e. NN ( ( -u ( log ` k ) ^ %s ) x. ( ( %s ` k ) x. ( k ^c -u %s ) ) )' % (K, CVM, P)
S['kdlsalg'] = ('( ( %s /\\ ( ( E e. RR+ /\\ E <_ 1 ) /\\ ( S e. CC /\\ ( Re ` S ) = ( 1 + E ) /\\ K e. NN0 ) ) ) -> %s = ( ( -u 1 ^ K ) x. %s ) )') % (NXH, S1I('K', 'S'), LSK('K', 'S'))


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in S:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or list(S))
