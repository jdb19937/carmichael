"""Sortie C0c: shared expressions for the winding integral and Cauchy's
integral formula.  Built on tools/gen/c0b_lib.py (sortie C0b)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c0b_lib import *

DD = '( CC \\ ( -oo (,] 0 ) )'
IPI = '( _i x. _pi )'
TWOPII = '( 2 x. ( _i x. _pi ) )'
INV = '( x e. %s |-> ( 1 / x ) )' % DD


def WP(P='P'):
    return '( z e. ( CC \\ { %s } ) |-> ( 1 / ( z - %s ) ) )' % (P, P)


def LOG(X):
    return '( log ` %s )' % X


def eqidd(w, ante, a):
    return w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, a, a))
