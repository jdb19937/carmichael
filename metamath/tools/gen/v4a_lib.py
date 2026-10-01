"""Sortie v4a: shared expressions for the twin-type sieve."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W


def QF(X, m='M'):
    """the support quadratic X ( M X + 1 )"""
    return '( %s x. ( ( %s x. %s ) + 1 ) )' % (X, m, X)


def RT(D, v='v', m='M'):
    """the roots of X ( M X + 1 ) modulo D"""
    return '{ %s e. ( 0 ..^ %s ) | %s || %s }' % (v, D, D, QF(v, m))


def PF(X, v='w'):
    return '{ %s e. Prime | %s || %s }' % (v, v, X)


def OM(X, v='r'):
    return '( # ` %s )' % PF(X, v)


def DVS(X, v='x'):
    return '{ %s e. NN | %s || %s }' % (v, v, X)


def CS(K, C, v='x'):
    return '{ %s e. ( 1 ... %s ) | ( %s gcd %s ) = 1 }' % (v, C, v, K)


def RS(Q, C, v='v', p='r'):
    """the j <_ C whose set of prime divisors is exactly Q"""
    return '{ %s e. ( 1 ... %s ) | { %s e. Prime | %s || %s } = %s }' % (v, C, p, p, v, Q)


def SMS(Q, C, v='v', r='r'):
    """the Q-smooth integers in ( 1 ... C ), V3's set"""
    return '{ %s e. ( 1 ... %s ) | { %s e. Prime | %s || %s } C_ %s }' % (v, C, r, r, v, Q)


def rsel(w, N, Q, C):
    """the elrab biconditional for RS( Q , C ) at N"""
    b = w.s([], 'breq2', '( v = %s -> ( r || v <-> r || %s ) )' % (N, N))
    rb = w.s([b], 'rabbidv',
             '( v = %s -> { r e. Prime | r || v } = { r e. Prime | r || %s } )' % (N, N))
    eq = w.s([rb], 'eqeq1d',
             '( v = %s -> ( { r e. Prime | r || v } = %s <-> { r e. Prime | r || %s } = %s ) )'
             % (N, Q, N, Q))
    return w.s([eq], 'elrab',
               '( %s e. %s <-> ( %s e. ( 1 ... %s ) /\\ { r e. Prime | r || %s } = %s ) )'
               % (N, RS(Q, C), N, C, N, Q))


def smel(w, N, Q, C):
    """the elrab biconditional for SMS( Q , C ) at N"""
    b = w.s([], 'breq2', '( v = %s -> ( r || v <-> r || %s ) )' % (N, N))
    rb = w.s([b], 'rabbidv',
             '( v = %s -> { r e. Prime | r || v } = { r e. Prime | r || %s } )' % (N, N))
    eq = w.s([rb], 'sseq1d',
             '( v = %s -> ( { r e. Prime | r || v } C_ %s <-> { r e. Prime | r || %s } C_ %s ) )'
             % (N, Q, N, Q))
    return w.s([eq], 'elrab',
               '( %s e. %s <-> ( %s e. ( 1 ... %s ) /\\ { r e. Prime | r || %s } C_ %s ) )'
               % (N, SMS(Q, C), N, C, N, Q))


def pfel(w, P, N):
    """the elrab biconditional for { r e. Prime | r || N } at P"""
    b = w.s([], 'breq1', '( r = %s -> ( r || %s <-> %s || %s ) )' % (P, N, P, N))
    return w.s([b], 'elrab',
               '( %s e. { r e. Prime | r || %s } <-> ( %s e. Prime /\\ %s || %s ) )'
               % (P, N, P, P, N))


def DEN(J):
    return '( ( 0 sigma %s ) / %s )' % (J, J)


def RAD(J, p='p', w='w'):
    return 'prod_ %s e. %s %s' % (p, PF(J, w), p)


def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))


def csel(w, N, K, C):
    """the elrab biconditional for CS( K , C ) at N"""
    o = w.s([], 'oveq1', '( x = %s -> ( x gcd %s ) = ( %s gcd %s ) )' % (N, K, N, K))
    e = w.s([o], 'eqeq1d',
            '( x = %s -> ( ( x gcd %s ) = 1 <-> ( %s gcd %s ) = 1 ) )' % (N, K, N, K))
    return w.s([e], 'elrab',
               '( %s e. %s <-> ( %s e. ( 1 ... %s ) /\\ ( %s gcd %s ) = 1 ) )'
               % (N, CS(K, C), N, C, N, K))
