"""Sortie C8: shared expressions and step patterns (the analytic logarithm on
a rectangle; the log-derivative bound).  Built on tools/c6blib.py (C6b, C6,
C2, C1, C0c, C0b, C0 helpers underneath)."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from c6blib import *

only = sys.argv[1:]


def run8(w):
    """run the worksheet unless the command line names other labels"""
    if only and w.label not in only:
        return True
    return w.run()


# ---- letters ------------------------------------------------------------------
# y  the nonvanishing quantifier NZ0 in every statement
# z  the headline conclusion quantifier;  g  the headline existential
# x  the mapping binder of the logarithm LAM;  k  its sum index
# w  the mapping binder of the term lemmas (dvfaff, hlogtdv)
# v  hypothesis quantifiers of the term lemmas
# p, j  the quantifiers of the slit-plane property (hlogN, hlogh)
# m, l, n  existentials of the bounds;  u, q the bound lemmas' quantifiers

SLIT = '( CC \\ ( -oo (,] 0 ) )'
K = '( A crect B )'
NZ0 = 'A. y e. ( A crect B ) ( F ` y ) =/= 0'
ABG = '( %s /\\ ( %s /\\ %s ) )' % (HOL, AB, GEO)          # HOL /\ ( AB /\ GEO )
EOPN = '( E e. %s /\\ E C_ ( A crect B ) )' % TOP


def AFF(T, X, a='A'):
    """the point a + T ( X - a )"""
    return '( %s + ( %s x. ( %s - %s ) ) )' % (a, T, X, a)


def FA(T, X):
    return '( F ` %s )' % AFF(T, X)


def QT(U, T, X):
    """the quotient F ( A + U ( X - A ) ) / F ( A + T ( X - A ) )"""
    return '( %s / %s )' % (FA(U, X), FA(T, X))


def KP1(k, N):
    return '( ( %s + 1 ) / %s )' % (k, N)


def KN(k, N):
    return '( %s / %s )' % (k, N)


def TERM(k, N, X):
    return '( log ` %s )' % QT(KP1(k, N), KN(k, N), X)


def SUMT(N, X, k='k'):
    return 'sum_ %s e. ( 0 ..^ %s ) %s' % (k, N, TERM(k, N, X))


def LAMB(N, X, k='k'):
    """the body of the logarithm at X"""
    return '( ( log ` ( F ` A ) ) + %s )' % SUMT(N, X, k)


def LAM(N, x='x', k='k'):
    return '( %s e. E |-> %s )' % (x, LAMB(N, x, k))


def SLITP(N, p='p', j='j'):
    """the slit-plane property of the quotients at the grid of N steps"""
    return 'A. %s e. ( A crect B ) A. %s e. ( 0 ..^ %s ) %s e. %s' % (p, j, N, QT(KP1(j, N), KN(j, N), p), SLIT)


def HOLE(G, Dm='E'):
    return '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (G, Dm, Dm, G)


def ORECT(a, b):
    return "( ( `' Re \" ( ( Re ` %s ) (,) ( Re ` %s ) ) ) i^i ( `' Im \" ( ( Im ` %s ) (,) ( Im ` %s ) ) ) )" % (a, b, a, b)


def SQ(c, r):
    """the closed square of half-side r about c"""
    return '( ( %s - ( %s + ( _i x. %s ) ) ) crect ( %s + ( %s + ( _i x. %s ) ) ) )' % (c, r, r, c, r, r)


def SQA(c, r):
    return '( %s - ( %s + ( _i x. %s ) ) )' % (c, r, r)


def SQB(c, r):
    return '( %s + ( %s + ( _i x. %s ) ) )' % (c, r, r)


# ---- statements of cited theorems -------------------------------------------------
def stmt(label):
    """the assertion of LABEL ($p or $a) from sorties/c8.mm or carmichael.mm, without |-"""
    import re as _re
    for fn in ('sorties/c8.mm', 'carmichael.mm'):
        txt = open(os.path.join(os.path.dirname(HERE), 'metamath', fn) if False else os.path.join(HERE, '..', fn)).read()
        m = _re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % _re.escape(label), txt, _re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def tsub(f, m):
    """simultaneous token substitution"""
    return ' '.join(m.get(t, t) for t in f.split())


def ante_of(f):
    """( A -> B ) -> (A, B) for a top-level implication"""
    from cl import split_imp
    return split_imp(f)


def lin8(w, ante, hyps, goal, leaves, products=False):
    """tools/lin.py linarith with every leaf declared atomic"""
    import lin as _lin, cl as _cl
    c = _cl.Closure(w, ante, leaves)
    for k in leaves:
        c.atom(k)
    return _lin.linarith(w, ante, hyps, goal, closure=c, products=products)
