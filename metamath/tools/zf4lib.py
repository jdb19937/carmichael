"""Shared expressions of sortie ZF4 (Gauss sums of Dirichlet characters;
Mathlib NumberTheory/GaussSum.lean, DirichletCharacter/GaussSum.lean)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zf2lib import DB, LZ, BZ, UZ, ONE, MUL, INV, IND, INDOP, COND, PRIM, FZO, EV, COP, HX, H3

HC = '( N e. NN /\\ X e. %s )' % DB('N')

def R(n='N'): return '( -u 1 ^c ( 2 / %s ) )' % n
def RP(k, n='N'): return '( %s ^ %s )' % (R(n), k)
def E(a, n='N'): return '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s / %s ) ) )' % (a, n)
def GS(n, x): return '( %s DChrGS %s )' % (n, x)
def TERM(x, n, a, sh=None):
    """the exp-form summand ( X ` ( L ` a ) ) x. E( A x. a ) (or E( a ) when sh is None)"""
    return '( %s x. %s )' % (EV(x, n, a), E(a if sh is None else '( %s x. %s )' % (sh, a), n))
def TERMR(x, n, a, sh=None):
    """the root-form summand ( X ` ( L ` a ) ) x. ( R ^ ( A x. a ) )"""
    return '( %s x. %s )' % (EV(x, n, a), RP(a if sh is None else '( %s x. %s )' % (sh, a), n))
def G(x, n, sh, a='a'):
    """G(X,A): the shifted Gauss sum in exp form"""
    return 'sum_ %s e. %s %s' % (a, FZO(n), TERM(x, n, a, sh))
def GR(x, n, sh, a='a'):
    """GR(X,A): the shifted Gauss sum in root form"""
    return 'sum_ %s e. %s %s' % (a, FZO(n), TERMR(x, n, a, sh))
def GSBODY(n='n', x='x', a='a'):
    return 'sum_ %s e. %s %s' % (a, FZO(n), TERM(x, n, a))
def GSMPO(n='n', x='x', a='a'):
    return '( %s e. NN , %s e. %s |-> %s )' % (n, x, DB(n), GSBODY(n, x, a))


def dchyp(w, n='N'):
    """the four eqid hypotheses G Z D L of set.mm's dchr* lemmas at level n"""
    return (w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (n, n)),
            w.s([], 'eqid', '( Z/nZ ` %s ) = ( Z/nZ ` %s )' % (n, n)),
            w.s([], 'eqid', '%s = %s' % (DB(n), DB(n))),
            w.s([], 'eqid', '%s = %s' % (LZ(n), LZ(n))))


def sylanc(w, hyps, ref, formula):
    """apply REF in deduction form: syl / syl2anc / syl3anc by hypothesis count"""
    n = len(hyps)
    if n == 1:
        return w.s([hyps[0], w.inst(ref)], 'syl', formula)
    if n == 2:
        return w.s([hyps[0], hyps[1], w.inst(ref)], 'syl2anc', formula)
    if n == 3:
        return w.s(hyps + [w.inst(ref)], 'syl3anc', formula)
    raise ValueError(n)


def zrh_el(w, ante, nstep, astep, n='N', A='A'):
    """( ante -> ( LN ` A ) e. BN ) from nstep: N e. NN and astep: A e. ZZ"""
    fo = w.s([w.s([nstep], 'nnnn0d', '( %s -> %s e. NN0 )' % (ante, n)),
              w.s([w.s([], 'eqid', '( Z/nZ ` %s ) = ( Z/nZ ` %s )' % (n, n)),
                   w.s([], 'eqid', '%s = %s' % (BZ(n), BZ(n))),
                   w.s([], 'eqid', '%s = %s' % (LZ(n), LZ(n)))], 'znzrhfo',
                  '( %s e. NN0 -> %s : ZZ -onto-> %s )' % (n, LZ(n), BZ(n)))], 'syl',
             '( %s -> %s : ZZ -onto-> %s )' % (ante, LZ(n), BZ(n)))
    f = w.s([fo, w.inst('fof')], 'syl', '( %s -> %s : ZZ --> %s )' % (ante, LZ(n), BZ(n)))
    return w.s([f, astep], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. %s )' % (ante, LZ(n), A, BZ(n)))


def dchr_conj(w, ante, nstep, xstep, astep, n='N', x='X', A='A'):
    """( ante -> ( ( IN ` X ) ` ( LN ` A ) ) = ( * ` ( X ` ( LN ` A ) ) ) ) (dchrinv, fvco3)"""
    g = w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (n, n))
    d = w.s([], 'eqid', '%s = %s' % (DB(n), DB(n)))
    i = w.s([], 'eqid', '%s = %s' % (INV(n), INV(n)))
    inv = w.s([g, d, xstep, i], 'dchrinv', '( %s -> ( %s ` %s ) = ( * o. %s ) )' % (ante, INV(n), x, x))
    fv = w.s([inv], 'fveq1d', '( %s -> ( ( %s ` %s ) ` ( %s ` %s ) ) = ( ( * o. %s ) ` ( %s ` %s ) ) )' % (ante, INV(n), x, LZ(n), A, x, LZ(n), A))
    z = w.s([], 'eqid', '( Z/nZ ` %s ) = ( Z/nZ ` %s )' % (n, n))
    b = w.s([], 'eqid', '%s = %s' % (BZ(n), BZ(n)))
    xf = w.s([g, z, d, b, xstep], 'dchrf', '( %s -> %s : %s --> CC )' % (ante, x, BZ(n)))
    el = zrh_el(w, ante, nstep, astep, n, A)
    co = w.s([xf, el, w.inst('fvco3')], 'syl2anc', '( %s -> ( ( * o. %s ) ` ( %s ` %s ) ) = ( * ` ( %s ` ( %s ` %s ) ) ) )' % (ante, x, LZ(n), A, x, LZ(n), A))
    return w.s([fv, co], 'eqtrd', '( %s -> ( ( %s ` %s ) ` ( %s ` %s ) ) = ( * ` ( %s ` ( %s ` %s ) ) ) )' % (ante, INV(n), x, LZ(n), A, x, LZ(n), A))


_PFX = [0]
def _pfx():
    _PFX[0] += 1
    return chr(ord('a') + (_PFX[0] - 1) % 26) * (1 + (_PFX[0] - 1) // 26)


def fsumf1o(w, ante, k, A, B, n, C, F, G, fin, bij, val, bcl):
    """( ante -> sum_ k e. A B = sum_ n e. C D ), D = B[k := G], by fsumf1o;
    returns (step, D).  fin: C e. Fin; bij: F : C -1-1-onto-> A;
    val: ( ( ante /\\ n e. C ) -> ( F ` n ) = G ); bcl: ( ( ante /\\ k e. A ) -> B e. CC )"""
    from congr import congruence, StepGen
    eq = '%s = %s' % (k, G)
    leaf = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    gen = StepGen('f' + _pfx())
    st, D = congruence(B, {k: G}, eq, {k: leaf}, gen)
    w.lines.extend(gen.lines)
    if st is None:
        st = w.s([], 'eqidd', '( %s -> %s = %s )' % (eq, B, D))
    out = w.s([st, fin, bij, val, bcl], 'fsumf1o', '( %s -> sum_ %s e. %s %s = sum_ %s e. %s %s )' % (ante, k, A, B, n, C, D))
    return out, D


def cbvsum(w, A, B, j, k):
    """sum_ j e. A B = sum_ k e. A C with C = B[j := k] (cbvsumv); returns (step, C)"""
    from congr import congruence, StepGen
    eq = '%s = %s' % (j, k)
    leaf = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    gen = StepGen('v' + _pfx())
    st, C = congruence(B, {j: k}, eq, {j: leaf}, gen)
    w.lines.extend(gen.lines)
    return w.s([st], 'cbvsumv', 'sum_ %s e. %s %s = sum_ %s e. %s %s' % (j, A, B, k, A, C)), C
