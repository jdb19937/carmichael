"""Sortie C3: shared expressions and step patterns (Dirichlet series and
L-functions).  Built on tools/gen/c2_lib.py (sorties C0, C0b, C0c, C1, C2)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c2_lib import *

only = sys.argv[1:]


def run3(w, h=False):
    if only and w.label not in only:
        return True
    return runh(w) if h else w.run()


# ---- the open half-plane ( Re ` z ) > T, as a preimage (C2's convention) ----
def HP(T='T'):
    return '( `\' Re " ( %s (,) +oo ) )' % T


IOOT = '( T (,) +oo )'
RETOP = '( topGen ` ran (,) )'

# ---- the Dirichlet series ---------------------------------------------------
def TRM(A, K, Z):
    """the K-th term ( A ` K ) x. ( K ^c -u Z )"""
    return '( ( %s ` %s ) x. ( %s ^c -u %s ) )' % (A, K, K, Z)


def DSER(A='A', Z='Z', k='k'):
    return 'sum_ %s e. NN %s' % (k, TRM(A, k, Z))


def ZTRM(K, T):
    return '( %s ^c -u %s )' % (K, T)


def ZSER(T='T', k='k'):
    return 'sum_ %s e. NN ( %s ^c -u %s )' % (k, k, T)


def SEQ1(F):
    return 'seq 1 ( + , %s ) ' % F


CFB = '( A : NN --> CC /\\ C e. RR /\\ A. m e. NN ( abs ` ( A ` m ) ) <_ C )'


def mpt(x, X, E):
    return '( %s e. %s |-> %s )' % (x, X, E)


def vexd(w, ante, expr, kind='ov'):
    """step ( ante -> expr e. _V )"""
    c = w.s([], kind + 'ex', '%s e. _V' % expr)
    return w.s([c], 'a1i', '( %s -> %s e. _V )' % (ante, expr))


def mpv(w, ante, mp, arg, val, sub, mem, exs, dom='NN'):
    """step ( ante -> ( mp ` arg ) = val ) from sub: ( n = arg -> body = val ),
    mem: ( ante -> arg e. dom ), exs: ( ante -> val e. _V )"""
    em = w.s([], 'eqid', '%s = %s' % (mp, mp))
    fv = w.s([sub, em], 'fvmptg',
             '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (arg, dom, val, mp, arg, val))
    return w.s([mem, exs, fv], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, arg, val))
