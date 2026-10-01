"""Sortie C5: shared expressions and step patterns (holomorphy of Dirichlet
series on a half-plane by uniform limits, the continuation of L(s,chi) to
Re s > 0).  Built on tools/gen/c4_lib.py."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'gen'))
from c4_lib import *

only = sys.argv[1:]


def run5(w, h=False):
    if only and w.label not in only:
        return True
    return runh(w) if h else w.run()


# ---- generic objects --------------------------------------------------------
def HOLG2(Fn, Dm):
    return '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (Fn, Dm, Dm, Fn)


def PSQ(Fn):
    """the partial-sum function sequence seq 1 ( oF + , F )"""
    return 'seq 1 ( oF + , %s )' % Fn


def FVV(Fn, K, Z):
    return '( ( %s ` %s ) ` %s )' % (Fn, K, Z)


def DVFV(Fn, K, Z):
    return '( ( CC _D ( %s ` %s ) ) ` %s )' % (Fn, K, Z)


def UHM(Fn, Mn, U='U'):
    """the summable majorant package for the term-function sequence Fn"""
    return '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( %s ` j ) ` y ) ) <_ ( %s ` j ) )' % (
        Mn, Mn, U, Fn, Mn)


def UHD(Fn, Rn, U='U'):
    """the summable majorant package for the derivatives of Fn"""
    return '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ A. j e. NN A. y e. %s ( abs ` ( ( CC _D ( %s ` j ) ) ` y ) ) <_ ( %s ` j ) )' % (
        Rn, Rn, U, Fn, Rn)


def FMAP(Fn, U='U'):
    return '%s : NN --> ( CC ^m %s )' % (Fn, U)


def UHS(Fn='F', Mn='M', U='U'):
    return '( %s /\\ %s )' % (FMAP(Fn, U), UHM(Fn, Mn, U))


def UHT(Fn='F', U='U'):
    """termwise holomorphy"""
    return 'A. j e. NN ( ( %s ` j ) e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D ( %s ` j ) ) )' % (Fn, U, U, Fn)


def UH(Fn='F', Mn='M', Rn='R', U='U'):
    return '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (FMAP(Fn, U), UHT(Fn, U), UHM(Fn, Mn, U), UHD(Fn, Rn, U))


def GSUM(Fn='F', U='U', z='z', k='k'):
    return '( %s e. %s |-> sum_ %s e. NN ( ( %s ` %s ) ` %s ) )' % (z, U, k, Fn, k, z)


def HSUM(Fn='F', U='U', z='z', k='k'):
    return '( %s e. %s |-> sum_ %s e. NN ( ( CC _D ( %s ` %s ) ) ` %s ) )' % (z, U, k, Fn, k, z)


def DF(Fn='F', h='h'):
    return '( %s e. NN |-> ( CC _D ( %s ` %s ) ) )' % (h, Fn, h)


def PSMAP(Fn, N, U='U', z='z', k='k'):
    return '( %s e. %s |-> sum_ %s e. ( 1 ... %s ) ( ( %s ` %s ) ` %s ) )' % (z, U, k, N, Fn, k, z)


# ---- the Dirichlet instance -------------------------------------------------
def LTRM(A, K, Z):
    return '( ( ( %s ` %s ) x. ( log ` %s ) ) x. ( %s ^c -u %s ) )' % (A, K, K, K, Z)


def SQF(A='A', T='T', h='a', z='p'):
    return '( %s e. NN |-> ( %s e. %s |-> %s ) )' % (h, z, HP(T), TRM(A, h, z))


def LSF(A='A', T='T', z='z', k='k'):
    return '( %s e. %s |-> sum_ %s e. NN %s )' % (z, HP(T), k, TRM(A, k, z))


def DSF(A='A', T='T', z='z', k='k'):
    return '( %s e. %s |-> sum_ %s e. NN -u %s )' % (z, HP(T), k, LTRM(A, k, z))


HYP = '( %s /\\ ( T e. RR /\\ 1 < T ) )' % CFB
EH = '( ( T - 1 ) / 2 )'
MAJ = '( n e. NN |-> ( C x. ( n ^c -u T ) ) )'
MAJD = '( n e. NN |-> ( ( C / %s ) x. ( n ^c -u ( T - %s ) ) ) )' % (EH, EH)

# ---- the character objects --------------------------------------------------
GG = '( DChr ` N )'
ZN = '( Z/nZ ` N )'
LH = '( ZRHom ` %s )' % ZN
DC = '( Base ` %s )' % GG
BZ = '( Base ` %s )' % ZN
ONE = '( 0g ` %s )' % GG
PG = '( +g ` %s )' % ZN
CHR = '( ( N e. NN /\\ X e. %s ) /\\ X =/= %s )' % (DC, ONE)


def CHV(K):
    return '( X ` ( %s ` %s ) )' % (LH, K)


def CSUM(M, i='i'):
    return 'sum_ %s e. ( 1 ... %s ) %s' % (i, M, CHV(i))


def CSF(q='q', i='i'):
    return '( %s e. NN |-> %s )' % (q, CSUM(q, i))


def dchyp(w):
    """the four defining equations of the DChr context, as steps"""
    return [w.s([], 'eqid', '%s = %s' % (GG, GG)), w.s([], 'eqid', '%s = %s' % (ZN, ZN)),
            w.s([], 'eqid', '%s = %s' % (DC, DC)), w.s([], 'eqid', '%s = %s' % (LH, LH))]


# ---- the Abel series --------------------------------------------------------
def ATM(S, K, Z):
    return '( ( %s ` %s ) x. ( ( %s ^c -u %s ) - ( ( %s + 1 ) ^c -u %s ) ) )' % (S, K, K, Z, K, Z)


def DAT(S, K, Z):
    """the derivative of ATM(S,K,z) at z = Z"""
    return '( ( %s ` %s ) x. ( ( ( log ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u %s ) ) - ( ( log ` %s ) x. ( %s ^c -u %s ) ) ) )' % (
        S, K, K, K, Z, K, K, Z)


def PSUM(A, M, i='i'):
    return 'sum_ %s e. ( 1 ... %s ) ( %s ` %s )' % (i, M, A, i)


def ATMS(A, K, Z, i='i'):
    """the Abel term with the partial sum written out"""
    return '( %s x. ( ( %s ^c -u %s ) - ( ( %s + 1 ) ^c -u %s ) ) )' % (PSUM(A, K, i), K, Z, K, Z)


def PSF(A='A', q='q', i='i'):
    return '( %s e. NN |-> %s )' % (q, PSUM(A, q, i))


ABS = '( S : NN --> CC /\\ B e. RR /\\ A. m e. NN ( abs ` ( S ` m ) ) <_ B )'


def BX(L='L', R='R'):
    """the open box L < Re z < R, -R < Im z < R"""
    return '( ( `\' Re " ( %s (,) %s ) ) i^i ( `\' Im " ( -u %s (,) %s ) ) )' % (L, R, R, R)


def ABF(S='S', U='U', h='a', z='p'):
    return '( %s e. NN |-> ( %s e. %s |-> %s ) )' % (h, z, U, ATM(S, h, z))


def ASF(S='S', U='U', z='z', k='k'):
    return '( %s e. %s |-> sum_ %s e. NN %s )' % (z, U, k, ATM(S, k, z))


# ---- step patterns ----------------------------------------------------------
def a1(w, ante, ref, fact):
    """closed fact lifted into the antecedent"""
    return w.s([w.s([], ref, fact)], 'a1i', '( %s -> %s )' % (ante, fact))


def cnfldtop(w, ante):
    """( ante -> TOP e. Top ) and the eqid step"""
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    return e, w.s([w.s([e], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (ante, TOP))


def opnss(w, ante, uo, U='U'):
    """( ante -> U C_ CC ) from uo: ( ante -> U e. TOP )"""
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ton = w.s([w.s([e], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOP)], 'a1i', '( %s -> %s e. ( TopOn ` CC ) )' % (ante, TOP))
    return w.s([ton, uo, w.inst('toponss')], 'syl2anc', '( %s -> %s C_ CC )' % (ante, U))


def nnuz(w, ante):
    """steps NN = ( ZZ>= ` 1 ), ( ante -> 1 e. ZZ ), ( ante -> 1 e. NN )"""
    return (w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, ante, '1z', '1 e. ZZ'), a1(w, ante, '1nn', '1 e. NN'))


def elmapf(w, ante, X, S, fs, U='U'):
    """( ante -> X e. ( CC ^m U ) ) from fs: ( ante -> X : U --> CC ) and S: ( ante -> U e. _V )"""
    cn = a1(w, ante, 'cnex', 'CC e. _V')
    bi = w.s([cn, S], 'elmapd', '( %s -> ( %s e. ( CC ^m %s ) <-> %s : %s --> CC ) )' % (ante, X, U, X, U))
    return w.s([fs, bi], 'mpbird', '( %s -> %s e. ( CC ^m %s ) )' % (ante, X, U))


def opnex(w, ante, uo, U='U'):
    """( ante -> U e. _V ) from ( ante -> U e. TOP )"""
    return w.s([uo], 'elexd', '( %s -> %s e. _V )' % (ante, U))


def uex(w, ante, ff, n1, Fn='F', U='U'):
    """( ante -> U e. _V ) from ff: F : NN --> ( CC ^m U ) and n1: 1 e. NN"""
    f1 = w.s([ff, n1], 'ffvelcdmd', '( %s -> ( %s ` 1 ) e. ( CC ^m %s ) )' % (ante, Fn, U))
    both = w.s([f1, w.inst('elmapex')], 'syl', '( %s -> ( CC e. _V /\\ %s e. _V ) )' % (ante, U))
    return w.s([both, w.inst('simpr')], 'syl', '( %s -> %s e. _V )' % (ante, U))


def fval(w, ante, i, mem, ff, Fn='F', U='U'):
    """( ante -> ( F ` i ) : U --> CC ) from mem: ( ante -> i e. NN )"""
    fi = w.s([ff, mem], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. ( CC ^m %s ) )' % (ante, Fn, i, U))
    return w.s([fi, w.inst('elmapi')], 'syl', '( %s -> ( %s ` %s ) : %s --> CC )' % (ante, Fn, i, U))
