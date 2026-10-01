"""Sortie C7: shared expressions and step patterns (the Perron far regime,
the Gamma line moment, the eta series).  Built on tools/c5lib.py."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c5lib import *
from cl import formula_of

only = sys.argv[1:]


def run7(w, h=False):
    if only and w.label not in only:
        return True
    return runh(w) if h else w.run()


# ---- the Perron kernel --------------------------------------------------------
DOM = '( CC \\ { 0 } )'
PK0 = PKF('U')
LO = CPT('C', '-u T'); HI = CPT('C', 'T')
PK = '( %s lint <. %s , %s >. )' % (PK0, LO, HI)
LGU = '( log ` U )'
NLGU = '-u ( log ` U )'


def E(A, B):
    return '( %s lint <. %s , %s >. )' % (PK0, A, B)


def FOUR(F, P, Q, S, R):
    """the four edges of the rectangle with corners P + iS, Q + iR, in the
    order rectintval produces them"""
    return '( ( ( %s lint <. %s , %s >. ) + ( %s lint <. %s , %s >. ) ) + ( ( %s lint <. %s , %s >. ) + ( %s lint <. %s , %s >. ) ) )' % (
        F, CPT(P, S), CPT(Q, S), F, CPT(Q, S), CPT(Q, R), F, CPT(Q, R), CPT(P, R), F, CPT(P, R), CPT(P, S))


FA = '( 1 + ( ( log ` ( ( ( T ^ 2 ) x. %s ) + 1 ) ) / %s ) )' % (LGU, LGU)
FB = '( ( C + 1 ) + ( ( log ` ( ( ( T ^ 2 ) x. %s ) + 1 ) ) / %s ) )' % (NLGU, NLGU)
BND1 = '( ( 2 x. ( U ^c C ) ) / ( T x. %s ) )' % LGU
BND0 = '( ( 2 x. ( U ^c C ) ) / ( T x. %s ) )' % NLGU
UGT1 = '( U e. RR /\\ 1 < U )'
ULT1 = '( U e. RR+ /\\ U < 1 )'
CT = '( C e. RR+ /\\ T e. RR+ )'

# ---- the Gamma line moment ----------------------------------------------------
HUND = '( 1 / ; ; 1 0 0 )'
GML = '( ( abs ` ( _G ` ( X + ( _i x. u ) ) ) ) x. ( ( 1 + ( abs ` u ) ) ^ 2 ) )'
GSB = 'A. d e. CC ( ( %s <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 ) -> ( abs ` ( _G ` d ) ) <_ ( H x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) ) )' % HUND

# ---- the eta series -----------------------------------------------------------
SM2 = '( q e. NN |-> ( q mod 2 ) )'
ALT = '( q e. NN |-> ( ( 2 x. ( q mod 2 ) ) - 1 ) )'


def ETT(K, Z):
    return '( ( %s mod 2 ) x. ( ( %s ^c -u %s ) - ( ( %s + 1 ) ^c -u %s ) ) )' % (K, K, Z, K, Z)


def ETA(Z, k='k'):
    return 'sum_ %s e. NN %s' % (k, ETT(k, Z))


def ZS(Z, k='k'):
    return 'sum_ %s e. NN ( %s ^c -u %s )' % (k, k, Z)


def ALTT(K):
    """the alternating coefficient ( -u 1 ) ^ ( K + 1 ) as ( 2 ( K mod 2 ) - 1 )"""
    return '( ( 2 x. ( %s mod 2 ) ) - 1 )' % K


def EVT(K):
    """the indicator of the even numbers as ( 1 - ( K mod 2 ) )"""
    return '( 1 - ( %s mod 2 ) )' % K


def M2(K):
    return '( %s mod 2 )' % K


def DIF(K, Z):
    return '( ( %s ^c -u %s ) - ( ( %s + 1 ) ^c -u %s ) )' % (K, Z, K, Z)


def mod2facts(w, ante, kz):
    """from kz: ( ante -> K e. ZZ ), the steps ( K mod 2 ) e. NN0, e. RR, e. CC,
    0 <_ ( K mod 2 ), ( K mod 2 ) <_ 1, as a dict"""
    K = formula_of(w, kz).split('-> ')[-1].split(' e. ZZ')[0].strip()
    m = M2(K); d = {}
    d['nn0'] = w.s([kz, a1(w, ante, '2nn', '2 e. NN'), w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ante, m))
    d['re'] = w.s([d['nn0']], 'nn0red', '( %s -> %s e. RR )' % (ante, m))
    d['cn'] = w.s([d['nn0']], 'nn0cnd', '( %s -> %s e. CC )' % (ante, m))
    d['ge0'] = w.s([d['nn0'], w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ %s )' % (ante, m))
    fz = w.s([kz, a1(w, ante, '2nn', '2 e. NN'), w.inst('zmodfz')], 'syl2anc', '( %s -> %s e. ( 0 ... ( 2 - 1 ) ) )' % (ante, m))
    d['le1'] = w.s([w.s([fz, w.inst('elfzle2')], 'syl', '( %s -> %s <_ ( 2 - 1 ) )' % (ante, m)), a1(w, ante, '2m1e1', '( 2 - 1 ) = 1')], 'breqtrd', '( %s -> %s <_ 1 )' % (ante, m))
    return d


def ettsub(w, K, Z, n='n'):
    """( n = K -> ETT(n,Z) = ETT(K,Z) )"""
    a = w.s([], 'oveq1', '( %s = %s -> ( %s mod 2 ) = ( %s mod 2 ) )' % (n, K, n, K))
    b = w.s([], 'oveq1', '( %s = %s -> ( %s ^c -u %s ) = ( %s ^c -u %s ) )' % (n, K, n, Z, K, Z))
    c = w.s([w.s([], 'oveq1', '( %s = %s -> ( %s + 1 ) = ( %s + 1 ) )' % (n, K, n, K))], 'oveq1d', '( %s = %s -> ( ( %s + 1 ) ^c -u %s ) = ( ( %s + 1 ) ^c -u %s ) )' % (n, K, n, Z, K, Z))
    d = w.s([b, c], 'oveq12d', '( %s = %s -> %s = %s )' % (n, K, DIF(n, Z), DIF(K, Z)))
    return w.s([a, d], 'oveq12d', '( %s = %s -> %s = %s )' % (n, K, ETT(n, Z), ETT(K, Z)))


def difcl(w, ante, K, kn, zc):
    """( ante -> DIF(K,Z) e. CC ) from kn: K e. NN, zc: Z e. CC"""
    Z = formula_of(w, zc).split('-> ')[-1].split(' e. CC')[0].strip()
    nzc = w.s([zc], 'negcld', '( %s -> -u %s e. CC )' % (ante, Z))
    kc = w.s([kn], 'nncnd', '( %s -> %s e. CC )' % (ante, K))
    a = w.s([kc, nzc], 'cxpcld', '( %s -> ( %s ^c -u %s ) e. CC )' % (ante, K, Z))
    b = w.s([w.s([kc, a1(w, ante, 'ax-1cn', '1 e. CC')], 'addcld', '( %s -> ( %s + 1 ) e. CC )' % (ante, K)), nzc], 'cxpcld', '( %s -> ( ( %s + 1 ) ^c -u %s ) e. CC )' % (ante, K, Z))
    return w.s([a, b], 'subcld', '( %s -> %s e. CC )' % (ante, DIF(K, Z)))


def ettcl(w, ante, K, kn, zc):
    """( ante -> ETT(K,Z) e. CC )"""
    Z = formula_of(w, zc).split('-> ')[-1].split(' e. CC')[0].strip()
    m = mod2facts(w, ante, w.s([kn], 'nnzd', '( %s -> %s e. ZZ )' % (ante, K)))
    return w.s([m['cn'], difcl(w, ante, K, kn, zc)], 'mulcld', '( %s -> %s e. CC )' % (ante, ETT(K, Z)))


def sm2val(w, K):
    """closed: ( K e. NN -> ( SM2 ` K ) = ( K mod 2 ) )"""
    sub = w.s([], 'oveq1', '( q = %s -> ( q mod 2 ) = ( %s mod 2 ) )' % (K, K))
    return w.s([sub, w.s([], 'eqid', '%s = %s' % (SM2, SM2)), w.s([], 'ovex', '( %s mod 2 ) e. _V' % K)], 'fvmpt', '( %s e. NN -> ( %s ` %s ) = ( %s mod 2 ) )' % (K, SM2, K, K))


GF = '( 1 - ( 2 ^c ( 1 - Z ) ) )'
ZP1 = '( Z e. CC /\\ 1 < ( Re ` Z ) )'
ZP0 = '( Z e. CC /\\ 0 < ( Re ` Z ) )'


# ---- step patterns for the Perron edges -------------------------------------
def pkfcn_(w, ante, urp):
    """( ante -> PK0 e. ( DOM -cn-> CC ) )"""
    return w.s([w.s([urp, a1(w, ante, 'ssid', '%s C_ %s' % (DOM, DOM))], 'jca', '( %s -> ( U e. RR+ /\\ %s C_ %s ) )' % (ante, DOM, DOM)),
                w.inst('pkfcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (ante, PK0, DOM))


def cptcl(w, ante, x, y, xr, yr):
    """( ante -> ( x + ( _i x. y ) ) e. CC ) from xr: x e. RR, yr: y e. RR"""
    return w.s([w.s([xr], 'recnd', '( %s -> %s e. CC )' % (ante, x)),
                w.s([a1(w, ante, 'ax-icn', '_i e. CC'), w.s([yr], 'recnd', '( %s -> %s e. CC )' % (ante, y))], 'mulcld',
                    '( %s -> ( _i x. %s ) e. CC )' % (ante, y))], 'addcld', '( %s -> %s e. CC )' % (ante, CPT(x, y)))


def dfss(w, ante, A, B, ral):
    """( ante -> ( A cseg B ) C_ DOM ) from ral: A. u e. ( A cseg B ) u e. DOM"""
    bi = w.s([], 'dfss3', '( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s )' % (A, B, DOM, A, B, DOM))
    return w.s([ral, w.s([bi], 'a1i', '( %s -> ( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s ) )' % (ante, A, B, DOM, A, B, DOM))],
               'mpbird', '( %s -> ( %s cseg %s ) C_ %s )' % (ante, A, B, DOM))


def segh(w, ante, S, P, Q, sr, sne, pr, qr):
    """( ante -> ( CPT(P,S) cseg CPT(Q,S) ) C_ DOM ), a horizontal segment off the real axis"""
    h = w.s([w.s([sr, sne], 'jca', '( %s -> ( %s e. RR /\\ %s =/= 0 ) )' % (ante, S, S)),
             w.s([pr, qr], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (ante, P, Q))], 'jca',
            '( %s -> ( ( %s e. RR /\\ %s =/= 0 ) /\\ ( %s e. RR /\\ %s e. RR ) ) )' % (ante, S, S, P, Q))
    ral = w.s([h, w.inst('cseghne0')], 'syl', '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (ante, CPT(P, S), CPT(Q, S), DOM))
    return dfss(w, ante, CPT(P, S), CPT(Q, S), ral)


def segv(w, ante, P, S1, S2, pr, pne, s1r, s2r):
    """( ante -> ( CPT(P,S1) cseg CPT(P,S2) ) C_ DOM ), a vertical segment off the imaginary axis"""
    h = w.s([w.s([pr, pne], 'jca', '( %s -> ( %s e. RR /\\ %s =/= 0 ) )' % (ante, P, P)),
             w.s([s1r, s2r], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (ante, S1, S2))], 'jca',
            '( %s -> ( ( %s e. RR /\\ %s =/= 0 ) /\\ ( %s e. RR /\\ %s e. RR ) ) )' % (ante, P, P, S1, S2))
    ral = w.s([h, w.inst('csegne0')], 'syl', '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (ante, CPT(P, S1), CPT(P, S2), DOM))
    return dfss(w, ante, CPT(P, S1), CPT(P, S2), ral)


def edgecl(w, ante, A, B, ac, bc, fcn, ss):
    """( ante -> E(A,B) e. CC ) and the lintrev form; returns (cl, pairs)"""
    abp = w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ante, A, B))
    fp = w.s([fcn, ss], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (ante, PK0, DOM, A, B, DOM))
    return w.s([abp, fp, w.inst('lintcl')], 'syl2anc', '( %s -> %s e. CC )' % (ante, E(A, B))), (abp, fp)


def vdiff(w, ante, P, S1, S2, pc, s1c, s2c):
    """( ante -> ( CPT(P,S2) - CPT(P,S1) ) = ( _i x. ( S2 - S1 ) ) )"""
    ic = a1(w, ante, 'ax-icn', '_i e. CC')
    i1 = w.s([ic, s1c], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (ante, S1))
    i2 = w.s([ic, s2c], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (ante, S2))
    d1 = w.s([pc, i2, pc, i1], 'addsub4d', '( %s -> ( %s - %s ) = ( ( %s - %s ) + ( ( _i x. %s ) - ( _i x. %s ) ) ) )' % (ante, CPT(P, S2), CPT(P, S1), P, P, S2, S1))
    z = w.s([pc], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (ante, P, P))
    sd = w.s([w.s([ic, s2c, s1c], 'subdid', '( %s -> ( _i x. ( %s - %s ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (ante, S2, S1, S2, S1))], 'eqcomd',
             '( %s -> ( ( _i x. %s ) - ( _i x. %s ) ) = ( _i x. ( %s - %s ) ) )' % (ante, S2, S1, S2, S1))
    d2 = w.s([d1, w.s([z, sd], 'oveq12d', '( %s -> ( ( %s - %s ) + ( ( _i x. %s ) - ( _i x. %s ) ) ) = ( 0 + ( _i x. ( %s - %s ) ) ) )' % (ante, P, P, S2, S1, S2, S1))],
             'eqtrd', '( %s -> ( %s - %s ) = ( 0 + ( _i x. ( %s - %s ) ) ) )' % (ante, CPT(P, S2), CPT(P, S1), S2, S1))
    dc = w.s([ic, w.s([s2c, s1c], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (ante, S2, S1))], 'mulcld', '( %s -> ( _i x. ( %s - %s ) ) e. CC )' % (ante, S2, S1))
    return w.s([d2, w.s([dc], 'addlidd', '( %s -> ( 0 + ( _i x. ( %s - %s ) ) ) = ( _i x. ( %s - %s ) ) )' % (ante, S2, S1, S2, S1))], 'eqtrd',
               '( %s -> ( %s - %s ) = ( _i x. ( %s - %s ) ) )' % (ante, CPT(P, S2), CPT(P, S1), S2, S1))


def absi_(w, ante, X, xc):
    """( ante -> ( abs ` ( _i x. X ) ) = ( abs ` X ) )"""
    ic = a1(w, ante, 'ax-icn', '_i e. CC')
    m = w.s([ic, xc], 'absmuld', '( %s -> ( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) ) )' % (ante, X, X))
    o = w.s([a1(w, ante, 'absi', '( abs ` _i ) = 1')], 'oveq1d', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) ) )' % (ante, X, X))
    axc = w.s([w.s([xc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (ante, X))], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (ante, X))
    u = w.s([axc], 'mullidd', '( %s -> ( 1 x. ( abs ` %s ) ) = ( abs ` %s ) )' % (ante, X, X))
    return w.s([m, w.s([o, u], 'eqtrd', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( abs ` %s ) )' % (ante, X, X))], 'eqtrd',
               '( %s -> ( abs ` ( _i x. %s ) ) = ( abs ` %s ) )' % (ante, X, X))


# ---- the Gamma continuity block (2b) -----------------------------------------
HP0 = HP('0')
LOGDM = '( CC \\ ( -oo (,] 0 ) )'
TOP = '( TopOpen ` CCfld )'


def UR(R='R'):
    """lgamgulm's set U at the radius R"""
    return '{ b e. CC | ( ( abs ` b ) <_ %s /\\ A. l e. NN0 ( 1 / %s ) <_ ( abs ` ( b + l ) ) ) }' % (R, R)


def TERM(M, Z):
    """the M-th term of the log-Gamma series at Z (lgamgulm.g)"""
    return '( ( %s x. ( log ` ( ( %s + 1 ) / %s ) ) ) - ( log ` ( ( %s / %s ) + 1 ) ) )' % (Z, M, M, Z, M)


def GR(R='R'):
    return '( m e. NN |-> ( z e. %s |-> %s ) )' % (UR(R), TERM('m', 'z'))


def termsub(w, K, Z, m='m'):
    """( m = K -> TERM(m,Z) = TERM(K,Z) )"""
    a = w.s([w.s([w.s([], 'oveq1', '( %s = %s -> ( %s + 1 ) = ( %s + 1 ) )' % (m, K, m, K)), w.s([], 'id', '( %s = %s -> %s = %s )' % (m, K, m, K))], 'oveq12d',
                 '( %s = %s -> ( ( %s + 1 ) / %s ) = ( ( %s + 1 ) / %s ) )' % (m, K, m, m, K, K))], 'fveq2d', '( %s = %s -> ( log ` ( ( %s + 1 ) / %s ) ) = ( log ` ( ( %s + 1 ) / %s ) ) )' % (m, K, m, m, K, K))
    a2 = w.s([a], 'oveq2d', '( %s = %s -> ( %s x. ( log ` ( ( %s + 1 ) / %s ) ) ) = ( %s x. ( log ` ( ( %s + 1 ) / %s ) ) ) )' % (m, K, Z, m, m, Z, K, K))
    b = w.s([w.s([w.s([], 'oveq2', '( %s = %s -> ( %s / %s ) = ( %s / %s ) )' % (m, K, Z, m, Z, K))], 'oveq1d', '( %s = %s -> ( ( %s / %s ) + 1 ) = ( ( %s / %s ) + 1 ) )' % (m, K, Z, m, Z, K))], 'fveq2d',
             '( %s = %s -> ( log ` ( ( %s / %s ) + 1 ) ) = ( log ` ( ( %s / %s ) + 1 ) ) )' % (m, K, Z, m, Z, K))
    return w.s([a2, b], 'oveq12d', '( %s = %s -> %s = %s )' % (m, K, TERM(m, Z), TERM(K, Z)))


def hp0facts(w, ante, zhp, Z):
    """from zhp: ( ante -> Z e. HP0 ): Z e. CC, 0 < Re Z, Z e. dom Gamma, Z e. LOGDM, Z =/= 0"""
    d = {}
    bi = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (Z, HP0, Z, Z))], 'a1i',
             '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (ante, Z, HP0, Z, Z))
    both = w.s([zhp, bi], 'mpbid', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (ante, Z, Z))
    d['zc'] = w.s([both, w.inst('simpl')], 'syl', '( %s -> %s e. CC )' % (ante, Z))
    d['gt'] = w.s([both, w.inst('simpr')], 'syl', '( %s -> 0 < ( Re ` %s ) )' % (ante, Z))
    d['dm'] = w.s([both, w.inst('zrenn')], 'syl', '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (ante, Z))
    d['ld'] = w.s([zhp, w.inst('hp0logdm')], 'syl', '( %s -> %s e. %s )' % (ante, Z, LOGDM))
    d['ne0'] = w.s([d['ld'], w.s([w.s([], 'eqid', '%s = %s' % (LOGDM, LOGDM))], 'logdmn0', '( %s e. %s -> %s =/= 0 )' % (Z, LOGDM, Z))], 'syl', '( %s -> %s =/= 0 )' % (ante, Z))
    return d


def termcl(w, ante, K, Z, zhp, kn):
    """( ante -> TERM(K,Z) e. CC ) from zhp: Z e. HP0, kn: K e. NN"""
    f = hp0facts(w, ante, zhp, Z)
    krp = w.s([kn], 'nnrpd', '( %s -> %s e. RR+ )' % (ante, K))
    q = w.s([w.s([kn], 'peano2nnd', '( %s -> ( %s + 1 ) e. NN )' % (ante, K))], 'nnrpd', '( %s -> ( %s + 1 ) e. RR+ )' % (ante, K))
    lk = w.s([w.s([w.s([q, krp], 'rpdivcld', '( %s -> ( ( %s + 1 ) / %s ) e. RR+ )' % (ante, K, K)), w.inst('relogcl')], 'syl', '( %s -> ( log ` ( ( %s + 1 ) / %s ) ) e. RR )' % (ante, K, K))], 'recnd',
             '( %s -> ( log ` ( ( %s + 1 ) / %s ) ) e. CC )' % (ante, K, K))
    a = w.s([f['zc'], lk], 'mulcld', '( %s -> ( %s x. ( log ` ( ( %s + 1 ) / %s ) ) ) e. CC )' % (ante, Z, K, K))
    p1 = w.s([zhp, kn, w.inst('hp0divp1')], 'syl2anc', '( %s -> ( ( %s / %s ) + 1 ) e. %s )' % (ante, Z, K, HP0))
    g = hp0facts(w, ante, p1, '( ( %s / %s ) + 1 )' % (Z, K))
    b = w.s([g['zc'], g['ne0'], w.inst('logcl')], 'syl2anc', '( %s -> ( log ` ( ( %s / %s ) + 1 ) ) e. CC )' % (ante, Z, K))
    return w.s([a, b], 'subcld', '( %s -> %s e. CC )' % (ante, TERM(K, Z)))


def hp0cc(w, ante):
    """( ante -> HP0 C_ CC )"""
    dm = w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('fdm')], 'ax-mp', 'dom Re = CC')
    ss = w.s([w.s([], 'cnvimass', '%s C_ dom Re' % HP0), dm], 'sseqtri', '%s C_ CC' % HP0)
    return w.s([ss], 'a1i', '( %s -> %s C_ CC )' % (ante, HP0))


def logmapcn(w, ante, S, sshp, MPZ, body, bodyd):
    """( ante -> ( z e. S |-> ( log ` body ) ) e. ( S -cn-> CC ) ) from
    MPZ: ( ante -> ( z e. S |-> body ) e. ( S -cn-> CC ) ) and
    bodyd: ( ( ante /\\ z e. S ) -> body e. LOGDM ); sshp: ( ante -> S C_ HP0 )"""
    Az = '( %s /\\ z e. %s )' % (ante, S)
    MP = '( z e. %s |-> %s )' % (S, body)
    dss = a1(w, ante, 'difss', '%s C_ CC' % LOGDM)
    fmp = w.s([bodyd, w.s([], 'eqid', '%s = %s' % (MP, MP))], 'fmptd', '( %s -> %s : %s --> %s )' % (ante, MP, S, LOGDM))
    intod = w.s([fmp, w.s([dss, MPZ, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( %s e. ( %s -cn-> %s ) <-> %s : %s --> %s ) )' % (ante, MP, S, LOGDM, MP, S, LOGDM))], 'mpbird',
                '( %s -> %s e. ( %s -cn-> %s ) )' % (ante, MP, S, LOGDM))
    lcn = w.s([w.s([w.s([], 'eqid', '%s = %s' % (LOGDM, LOGDM))], 'logcn', '( log |` %s ) e. ( %s -cn-> CC )' % (LOGDM, LOGDM))], 'a1i', '( %s -> ( log |` %s ) e. ( %s -cn-> CC ) )' % (ante, LOGDM, LOGDM))
    co = w.s([intod, lcn], 'cncfco', '( %s -> ( ( log |` %s ) o. %s ) e. ( %s -cn-> CC ) )' % (ante, LOGDM, MP, S))
    lf = w.s([lcn, w.inst('cncff')], 'syl', '( %s -> ( log |` %s ) : %s --> CC )' % (ante, LOGDM, LOGDM))
    cof = w.s([lf, bodyd], 'cofmpt', '( %s -> ( ( log |` %s ) o. %s ) = ( z e. %s |-> ( ( log |` %s ) ` %s ) ) )' % (ante, LOGDM, MP, S, LOGDM, body))
    fvr = w.s([w.s([bodyd, w.inst('fvres')], 'syl', '( %s -> ( ( log |` %s ) ` %s ) = ( log ` %s ) )' % (Az, LOGDM, body, body))], 'mpteq2dva',
              '( %s -> ( z e. %s |-> ( ( log |` %s ) ` %s ) ) = ( z e. %s |-> ( log ` %s ) ) )' % (ante, S, LOGDM, body, S, body))
    return w.s([w.s([cof, fvr], 'eqtrd', '( %s -> ( ( log |` %s ) o. %s ) = ( z e. %s |-> ( log ` %s ) ) )' % (ante, LOGDM, MP, S, body)), co], 'eqeltrrd',
               '( %s -> ( z e. %s |-> ( log ` %s ) ) e. ( %s -cn-> CC ) )' % (ante, S, body, S))
