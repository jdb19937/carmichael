"""Sortie v4b: shared expressions for Brun-Titchmarsh in the progression 1 mod M."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W

# ---- the sieve data (section 1 of V4b-blueprint.md) ----------------------
T = '{ u e. ( 0 ... Z ) | ( u e. Prime /\\ -. u || M ) }'
P = 'prod_ p e. %s p' % T
A = '{ i e. ( 1 ... N ) | ( i mod M ) = ( 1 mod M ) }'
WF = '( c e. NN |-> 1 )'
X = '( N / M )'
Y = '( Z ^ 2 )'
V = '( t e. NN |-> prod_ f e. { g e. Prime | g || t } ( 1 / f ) )'

PH = '( M e. ( ZZ>= ` 2 ) /\\ Z e. NN /\\ N e. NN0 )'


def PF(Xe, v='r'):
    return '{ %s e. Prime | %s || %s }' % (v, v, Xe)


def OM(Xe, v='r'):
    return '( # ` %s )' % PF(Xe, v)


def DV(Xe, v='x'):
    return '{ %s e. NN | %s || %s }' % (v, v, Xe)


def RAD(J, e='e', u='u'):
    return 'prod_ %s e. %s %s' % (e, PF(J, u), e)


def SMS(Q, Wb, v='v', r='r'):
    return '{ %s e. ( 1 ... %s ) | { %s e. Prime | %s || %s } C_ %s }' % (v, Wb, r, r, v, Q)


def GTV(L, Vx=V, q='q', r='r'):
    """the Selberg term at L for the density Vx"""
    return '( ( %s ` %s ) x. prod_ %s e. %s ( 1 / ( 1 - ( %s ` %s ) ) ) )' % (
        Vx, L, q, PF(L, r), Vx, q)


def GTR(L, q='q', r='r'):
    """the Selberg term at L written with ( 1 / p ) in place of ( V ` p )"""
    return '( ( 1 / %s ) x. prod_ %s e. %s ( 1 / ( 1 - ( 1 / %s ) ) ) )' % (L, q, PF(L, r), q)


SS = 'sum_ l e. %s if ( ( l ^ 2 ) <_ %s , %s , 0 )' % (DV(P), Y, GTV('l'))
SF = 'sum_ n e. %s if ( ( %s gcd n ) = 1 , ( %s ` n ) , 0 )' % (A, P, WF)
MS = lambda D: 'sum_ n e. %s if ( %s || n , ( %s ` n ) , 0 )' % (A, D, WF)
RM = lambda D: '( %s - ( ( %s ` %s ) x. %s ) )' % (MS(D), V, D, X)
ERR = 'sum_ d e. %s if ( d <_ %s , ( ( 3 ^ %s ) x. ( abs ` %s ) ) , 0 )' % (
    DV(P), Y, OM('d'), RM('d'))

SH = ('( ( ( %s e. Fin /\\ %s C_ NN /\\ %s : NN --> RR ) /\\ ( A. k e. NN 0 <_ ( %s ` k ) '
      '/\\ %s e. RR /\\ ( %s e. RR /\\ 1 <_ %s ) ) ) /\\ ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) '
      '/\\ ( %s : NN --> RR /\\ ( %s ` 1 ) = 1 /\\ ( A. a e. NN A. b e. NN ( ( a gcd b ) = 1 '
      '-> ( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) ) ) /\\ A. s e. Prime ( s || %s -> '
      '( 0 < ( %s ` s ) /\\ ( %s ` s ) < 1 ) ) ) ) ) )'
      % (A, A, WF, WF, X, Y, Y, P, P, V, V, V, V, V, P, V, V))

# the prime-counting set of the headline statement
TT = '{ i e. ( 0 ... N ) | ( i e. Prime /\\ ( i mod M ) = ( 1 mod M ) ) }'
# the residue-class count of block 4
CT = lambda D: '{ i e. ( 1 ... N ) | ( ( i mod M ) = ( 1 mod M ) /\\ %s || i ) }' % D


def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))
