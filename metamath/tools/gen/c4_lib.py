"""Sortie C4: shared expressions and step patterns (Perron kernel, Abel
summation, the Gamma strip bound).  Built on tools/gen/c3_lib.py."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c3_lib import *

only = sys.argv[1:]


def run4(w, h=False):
    if only and w.label not in only:
        return True
    return runh(w) if h else w.run()


# ---- Euler's product term (set.mm gamcvg2.f) --------------------------------
def EUT(Z, m='m'):
    return '( %s e. NN |-> ( ( ( ( %s + 1 ) / %s ) ^c %s ) / ( ( %s / %s ) + 1 ) ) )' % (m, m, m, Z, Z, m)


def EUTB(Z, M):
    """the body of EUT at an explicit argument M"""
    return '( ( ( ( %s + 1 ) / %s ) ^c %s ) / ( ( %s / %s ) + 1 ) )' % (M, M, Z, Z, M)


# ---- the Perron integrand ---------------------------------------------------
def PKF(U='U', z='z'):
    return '( %s e. ( CC \\ { 0 } ) |-> ( ( %s ^c %s ) / %s ) )' % (z, U, z, z)


def CXF(U='U', z='z'):
    return '( %s e. CC |-> ( %s ^c %s ) )' % (z, U, z)


def CPT(P, S):
    """the point P + i S"""
    return '( %s + ( _i x. %s ) )' % (P, S)


TPI = '( 2 x. ( _i x. _pi ) )'
