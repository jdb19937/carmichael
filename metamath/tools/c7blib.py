"""Sortie C7b: shared expressions and step patterns (the Dirichlet-series
product dconvlim, the -L'/L limit block, the von Mangoldt series bound).
Built on tools/c7lib.py (C5, C4, C3 helpers underneath)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c7lib import *
from cl import formula_of

only = sys.argv[1:]


def run7b(w, h=False):
    if only and w.label not in only:
        return True
    return runh(w) if h else w.run()


# ---- letters ------------------------------------------------------------------
# i  partial-sum index in every statement          e  divisor-sum index under LAV
# d  divisor index of dvdsflsumcom / CV / LAV      m  the CFB quantifier
# n  mapping binder of the term sequences          x  the divisor set { x e. NN | x || k }
# y  the LAV quantifier                            k  the consumer-facing series index
# l  clim/fsumser index inside proofs (never in a statement)
# q  the binder of AX / AXL / AXM

RZ = '( Re ` Z )'
E1 = '( ( Re ` Z ) - 1 )'
ZP1 = '( Z e. CC /\\ 1 < ( Re ` Z ) )'


def TRM(A, K, Z='Z'):
    return '( ( %s ` %s ) x. ( %s ^c -u %s ) )' % (A, K, K, Z)


def MAP(A, Z='Z', n='n'):
    """the term sequence ( n e. NN |-> ( ( A ` n ) x. ( n ^c -u Z ) ) )"""
    return '( %s e. NN |-> %s )' % (n, TRM(A, n, Z))


def PS(A, M, Z='Z', i='i'):
    """the partial sum sum_ i e. ( 1 ... M ) ( ( A ` i ) x. ( i ^c -u Z ) )"""
    return 'sum_ %s e. ( 1 ... %s ) %s' % (i, M, TRM(A, i, Z))


def SER(A, Z='Z', k='k'):
    return 'sum_ %s e. NN %s' % (k, TRM(A, k, Z))


def CV(K, A='A', B='B', d='d', x='x'):
    """the Dirichlet convolution value sum_ d | K ( A ` d ) ( B ` ( K / d ) )"""
    return 'sum_ %s e. { %s e. NN | %s || %s } ( ( %s ` %s ) x. ( %s ` ( %s / %s ) ) )' % (d, x, x, K, A, d, B, K, d)


def CTRM(K, Z='Z', A='A', B='B'):
    return '( %s x. ( %s ^c -u %s ) )' % (CV(K, A, B), K, Z)


def CMAP(Z='Z', A='A', B='B', n='n'):
    return '( %s e. NN |-> %s )' % (n, CTRM(n, Z, A, B))


def CPS(M, Z='Z', A='A', B='B', i='i'):
    return 'sum_ %s e. ( 1 ... %s ) %s' % (i, M, CTRM(i, Z, A, B))


def CSER(Z='Z', A='A', B='B', k='k'):
    return 'sum_ %s e. NN %s' % (k, CTRM(k, Z, A, B))


def CFBX(A, C):
    return '( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (A, C, A, C)


def LAV(A='A', K='K'):
    """the logarithmic-average bound on the coefficients"""
    return '( %s : NN --> CC /\\ %s e. RR /\\ A. y e. RR ( 1 <_ y -> sum_ d e. ( 1 ... ( |_ ` y ) ) ( ( abs ` ( %s ` d ) ) / d ) <_ ( ( log ` y ) + %s ) ) )' % (A, K, A, K)


CFBB = CFBX('B', 'C')
DCH = '( ( %s /\\ %s ) /\\ ( %s /\\ seq 1 ( + , %s ) e. dom ~~> ) )' % (LAV(), CFBB, ZP1, MAP('A'))
DK = '( ( ( 2 ^c %s ) x. C ) / %s )' % (E1, E1)
FLD = '( |_ ` ( N / D ) )'


def MJ(D='D', K='K', E='E', n='n'):
    """the majorant sequence D ( n ^c -u E ) ( log n + K )"""
    return '( %s e. NN |-> ( %s x. ( ( %s ^c -u %s ) x. ( ( log ` %s ) + %s ) ) ) )' % (n, D, n, E, n, K)


# ---- the character objects (C5 conventions) -------------------------------------
NX = '( N e. NN /\\ X e. %s )' % DC
AX = '( q e. NN |-> %s )' % CHV('q')
AXL = '( q e. NN |-> ( %s x. ( Lam ` q ) ) )' % CHV('q')
AXM = '( q e. NN |-> ( %s x. ( mmu ` q ) ) )' % CHV('q')
K4 = '( ( log ` 4 ) + 4 )'


def VMT(K, Z='Z'):
    """( ( chi(K) x. ( Lam ` K ) ) x. ( K ^c -u Z ) )"""
    return '( ( %s x. ( Lam ` %s ) ) x. ( %s ^c -u %s ) )' % (CHV(K), K, K, Z)


def LGT(K, Z='Z'):
    return '( ( %s x. ( log ` %s ) ) x. ( %s ^c -u %s ) )' % (CHV(K), K, K, Z)


def MUT(K, Z='Z'):
    return '( ( %s x. ( mmu ` %s ) ) x. ( %s ^c -u %s ) )' % (CHV(K), K, K, Z)


def CHT(K, Z='Z'):
    return '( %s x. ( %s ^c -u %s ) )' % (CHV(K), K, Z)


def RVT(K, T='T'):
    """the real von Mangoldt term ( ( Lam ` K ) x. ( K ^c -u T ) )"""
    return '( ( Lam ` %s ) x. ( %s ^c -u %s ) )' % (K, K, T)


LSFX = '( z e. %s |-> sum_ k e. NN %s )' % (HP(), CHT('k', 'z'))
T1 = '( T e. RR /\\ 1 < T )'


# ---- step patterns ---------------------------------------------------------------
def nnuz1(w, ante):
    """steps NN = ( ZZ>= ` 1 ), ( ante -> 1 e. ZZ )"""
    return w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, ante, '1z', '1 e. ZZ')


def trmsub(w, A, K, Z='Z', n='n'):
    """( n = K -> TRM(A,n) = TRM(A,K) )"""
    s1 = w.s([], 'fveq2', '( %s = %s -> ( %s ` %s ) = ( %s ` %s ) )' % (n, K, A, n, A, K))
    s2 = w.s([], 'oveq1', '( %s = %s -> ( %s ^c -u %s ) = ( %s ^c -u %s ) )' % (n, K, n, Z, K, Z))
    return w.s([s1, s2], 'oveq12d', '( %s = %s -> %s = %s )' % (n, K, TRM(A, n, Z), TRM(A, K, Z)))


def trmcl(w, ante, A, K, af, kn, zc, Z='Z'):
    """( ante -> TRM(A,K) e. CC ) from af: A : NN --> CC, kn: K e. NN, zc: Z e. CC"""
    ak = w.s([af, kn], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (ante, A, K))
    pz = w.s([w.s([kn], 'nncnd', '( %s -> %s e. CC )' % (ante, K)), w.s([zc], 'negcld', '( %s -> -u %s e. CC )' % (ante, Z))], 'cxpcld',
             '( %s -> ( %s ^c -u %s ) e. CC )' % (ante, K, Z))
    return w.s([ak, pz], 'mulcld', '( %s -> %s e. CC )' % (ante, TRM(A, K, Z)))


def cxpz(w, ante, K, kn, zc, Z='Z'):
    """( ante -> ( K ^c -u Z ) e. CC )"""
    return w.s([w.s([kn], 'nncnd', '( %s -> %s e. CC )' % (ante, K)), w.s([zc], 'negcld', '( %s -> -u %s e. CC )' % (ante, Z))], 'cxpcld',
               '( %s -> ( %s ^c -u %s ) e. CC )' % (ante, K, Z))


def rpcxp(w, ante, K, krp, er, E):
    """( ante -> ( K ^c -u E ) e. RR+ ) from krp: K e. RR+, er: E e. RR"""
    return w.s([krp, w.s([er], 'renegcld', '( %s -> -u %s e. RR )' % (ante, E))], 'rpcxpcld', '( %s -> ( %s ^c -u %s ) e. RR+ )' % (ante, K, E))


def fsumfin(w, ante, M):
    return w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (ante, M))


def zctx(w, A0, zp):
    """from zp: ( A0 -> ZP1 ): Z e. CC, 1 < Re Z, Re Z e. RR, ( Re Z - 1 ) e. RR+"""
    zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
    z1 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 1 < %s )' % (A0, RZ))
    rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    r1 = a1(w, A0, '1re', '1 e. RR')
    e1re = w.s([rz, r1], 'resubcld', '( %s -> %s e. RR )' % (A0, E1))
    e1gt = w.s([z1, w.s([r1, rz], 'posdifd', '( %s -> ( 1 < %s <-> 0 < %s ) )' % (A0, RZ, E1))], 'mpbid', '( %s -> 0 < %s )' % (A0, E1))
    e1rp = w.s([e1re, e1gt], 'elrpd', '( %s -> %s e. RR+ )' % (A0, E1))
    return dict(zc=zc, z1=z1, rz=rz, r1=r1, e1re=e1re, e1gt=e1gt, e1rp=e1rp)


def cfbctx(w, A0, cfb, B='B', C='C'):
    """the three conjuncts of CFB(B,C) and 0 <_ C"""
    bf = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> %s : NN --> CC )' % (A0, B))
    cr = w.s([cfb, w.inst('simp2')], 'syl', '( %s -> %s e. RR )' % (A0, C))
    ral = w.s([cfb, w.inst('simp3')], 'syl', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ %s )' % (A0, B, C))
    return dict(bf=bf, cr=cr, ral=ral)


def dchctx(w, A0, nx):
    """the DChr context: N e. NN, X e. DC, the four eqid steps"""
    nn = w.s([nx, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    xd = w.s([nx, w.inst('simpr')], 'syl', '( %s -> X e. %s )' % (A0, DC))
    g, z, b, l = dchyp(w)
    return dict(nn=nn, xd=xd, g=g, z=z, b=b, l=l)


def chvcl(w, ante, K, c, kz):
    """( ante -> chi(K) e. CC ) from kz: ( ante -> K e. ZZ ) and the DChr context c (with xd lifted to ante)"""
    return w.s([c['g'], c['z'], c['b'], c['l'], c['xd'], kz], 'dchrzrhcl', '( %s -> %s e. CC )' % (ante, CHV(K)))


def chvabs(w, ante, K, nxk):
    """( ante -> ( abs ` chi(K) ) <_ 1 ) from nxk: ( ante -> ( NX /\\ K e. NN ) )"""
    return w.s([nxk, w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (ante, CHV(K)))


def pscl(w, ante, A, M, af, zc, i='i'):
    """( ante -> PS(A,M) e. CC ) from af: ( ante -> A : NN --> CC ), zc: ( ante -> Z e. CC )"""
    Ai = '( %s /\\ %s e. ( 1 ... %s ) )' % (ante, i, M)
    inn = w.s([w.s([], 'simpr', '( %s -> %s e. ( 1 ... %s ) )' % (Ai, i, M)), w.inst('elfznn')], 'syl', '( %s -> %s e. NN )' % (Ai, i))
    ti = trmcl(w, Ai, A, i, w.s([af], 'adantr', '( %s -> %s : NN --> CC )' % (Ai, A)), inn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ai))
    return w.s([fsumfin(w, ante, M), ti], 'fsumcl', '( %s -> %s e. CC )' % (ante, PS(A, M, i=i)))


def cvcl(w, ante, K, kn, af, bf):
    """( ante -> CV(K) e. CC ) from kn: ( ante -> K e. NN )"""
    DV = '{ x e. NN | x || %s }' % K
    Ad = '( %s /\\ d e. %s )' % (ante, DV)
    dd = w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, DV))
    ss = w.s([w.s([], 'ssrab2', '%s C_ NN' % DV)], 'a1i', '( %s -> %s C_ NN )' % (Ad, DV))
    dn = w.s([ss, dd], 'sseldd', '( %s -> d e. NN )' % Ad)
    kd = w.s([kn], 'adantr', '( %s -> %s e. NN )' % (Ad, K))
    qn = w.s([ss, w.s([kd, dd, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( %s / d ) e. %s )' % (Ad, K, DV))], 'sseldd', '( %s -> ( %s / d ) e. NN )' % (Ad, K))
    a = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ad), dn], 'ffvelcdmd', '( %s -> ( A ` d ) e. CC )' % Ad)
    b = w.s([w.s([bf], 'adantr', '( %s -> B : NN --> CC )' % Ad), qn], 'ffvelcdmd', '( %s -> ( B ` ( %s / d ) ) e. CC )' % (Ad, K))
    ab = w.s([a, b], 'mulcld', '( %s -> ( ( A ` d ) x. ( B ` ( %s / d ) ) ) e. CC )' % (Ad, K))
    fi = w.s([kn, w.inst('dvdsfi')], 'syl', '( %s -> %s e. Fin )' % (ante, DV))
    return w.s([fi, ab], 'fsumcl', '( %s -> %s e. CC )' % (ante, CV(K)))


def ctrmcl(w, ante, K, kn, af, bf, zc):
    """( ante -> CTRM(K) e. CC )"""
    return w.s([cvcl(w, ante, K, kn, af, bf), cxpz(w, ante, K, kn, zc)], 'mulcld', '( %s -> %s e. CC )' % (ante, CTRM(K)))


def cpscl(w, ante, M, af, bf, zc):
    """( ante -> CPS(M) e. CC )"""
    Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (ante, M)
    inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (Ai, M)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
    t = ctrmcl(w, Ai, 'i', inn, w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ai), w.s([bf], 'adantr', '( %s -> B : NN --> CC )' % Ai),
               w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ai))
    return w.s([fsumfin(w, ante, M), t], 'fsumcl', '( %s -> %s e. CC )' % (ante, CPS(M)))


def cpscl2(w, ante, M, af, bf, zc, mn):
    """( ante -> CPS(M) e. CC ) proved under the clean antecedent
    ( ( A : NN --> CC /\\ B : NN --> CC ) /\\ ( Z e. CC /\\ M e. NN ) ) (so that
    ante may bind d and x) and transported by syl; mn: ( ante -> M e. NN )"""
    AB = '( ( A : NN --> CC /\\ B : NN --> CC ) /\\ ( Z e. CC /\\ %s e. NN ) )' % M
    a = w.s([], 'simpll', '( %s -> A : NN --> CC )' % AB)
    b = w.s([], 'simplr', '( %s -> B : NN --> CC )' % AB)
    z = w.s([], 'simprl', '( %s -> Z e. CC )' % AB)
    st = cpscl(w, AB, M, a, b, z)
    j = w.s([w.s([af, bf], 'jca', '( %s -> ( A : NN --> CC /\\ B : NN --> CC ) )' % ante), w.s([zc, mn], 'jca', '( %s -> ( Z e. CC /\\ %s e. NN ) )' % (ante, M))],
            'jca', '( %s -> %s )' % (ante, AB))
    return w.s([j, st], 'syl', '( %s -> %s e. CC )' % (ante, CPS(M)))


def ctrmcl2(w, ante, K, af, bf, zc, kn):
    """( ante -> CTRM(K) e. CC ) under a clean antecedent, transported"""
    AB = '( ( A : NN --> CC /\\ B : NN --> CC ) /\\ ( Z e. CC /\\ %s e. NN ) )' % K
    a = w.s([], 'simpll', '( %s -> A : NN --> CC )' % AB)
    b = w.s([], 'simplr', '( %s -> B : NN --> CC )' % AB)
    z = w.s([], 'simprl', '( %s -> Z e. CC )' % AB)
    k = w.s([], 'simprr', '( %s -> %s e. NN )' % (AB, K))
    st = ctrmcl(w, AB, K, k, a, b, z)
    j = w.s([w.s([af, bf], 'jca', '( %s -> ( A : NN --> CC /\\ B : NN --> CC ) )' % ante), w.s([zc, kn], 'jca', '( %s -> ( Z e. CC /\\ %s e. NN ) )' % (ante, K))],
            'jca', '( %s -> %s )' % (ante, AB))
    return w.s([j, st], 'syl', '( %s -> %s e. CC )' % (ante, CTRM(K)))
