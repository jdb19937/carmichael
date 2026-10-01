"""Sortie v3: shared expressions for the twin-type sieve and Brun-Titchmarsh."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W


def PF(X, v='r'):
    """the set of prime divisors of X"""
    return '{ %s e. Prime | %s || %s }' % (v, v, X)


def OM(X, v='r'):
    return '( # ` %s )' % PF(X, v)


def DV(X, v='x'):
    return '{ %s e. NN | %s || %s }' % (v, v, X)


def CS(K, Wb, v='x'):
    """the integers in ( 1 ... Wb ) coprime to K"""
    return '{ %s e. ( 1 ... %s ) | ( %s gcd %s ) = 1 }' % (v, Wb, v, K)


def SM(Q, Wb, v='x', r='r'):
    """the Q-smooth integers in ( 1 ... Wb )"""
    return '{ %s e. ( 1 ... %s ) | %s C_ %s }' % (v, Wb, PF(v, r), Q)


def RAD(X, p='p', r='r'):
    return 'prod_ %s e. %s %s' % (p, PF(X, r), p)


def NUC(X, p='p', r='r'):
    return 'prod_ %s e. %s ( ( 2 / %s ) ^ ( %s pCnt %s ) )' % (p, PF(X, r), p, p, X)


def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))


def SMS(Q, Wb, v='v', r='r'):
    """the Q-smooth integers in ( 1 ... Wb ), outer binder v"""
    return '{ %s e. ( 1 ... %s ) | { %s e. Prime | %s || %s } C_ %s }' % (v, Wb, r, r, v, Q)


def smel(w, ante, st, N, Q, Wb, v='v', r='r'):
    """steps ( ante -> N e. ( 1 ... Wb ) ) and ( ante -> PF( N ) C_ Q ) from
    ( ante -> N e. SMS( Q , Wb ) ); returns (fz, pf)"""
    S = SMS(Q, Wb, v, r)
    sb0 = w.s([], 'breq2', '( %s = %s -> ( %s || %s <-> %s || %s ) )' % (v, N, r, v, r, N))
    sb1 = w.s([sb0], 'rabbidv',
              '( %s = %s -> { %s e. Prime | %s || %s } = { %s e. Prime | %s || %s } )'
              % (v, N, r, r, v, r, r, N))
    sb = w.s([sb1], 'sseq1d',
             '( %s = %s -> ( { %s e. Prime | %s || %s } C_ %s <-> { %s e. Prime | %s || %s } C_ %s ) )'
             % (v, N, r, r, v, Q, r, r, N, Q))
    el = w.s([sb], 'elrab',
             '( %s e. %s <-> ( %s e. ( 1 ... %s ) /\\ { %s e. Prime | %s || %s } C_ %s ) )'
             % (N, S, N, Wb, r, r, N, Q))
    return el
