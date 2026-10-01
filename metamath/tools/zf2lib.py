"""Shared expressions of sortie ZF2 (induced characters, conductor, primitive
characters; Mathlib DirichletCharacter/Basic.lean)."""

def DB(n): return '( Base ` ( DChr ` %s ) )' % n
def LZ(n): return '( ZRHom ` ( Z/nZ ` %s ) )' % n
def BZ(n): return '( Base ` ( Z/nZ ` %s ) )' % n
def UZ(n): return '( Unit ` ( Z/nZ ` %s ) )' % n
def ONE(n): return '( 0g ` ( DChr ` %s ) )' % n
def MUL(n): return '( +g ` ( DChr ` %s ) )' % n
def INV(n): return '( invg ` ( DChr ` %s ) )' % n
def IND(n, m, x): return '( ( %s DChrInd %s ) ` %s )' % (n, m, x)
def INDOP(n, m): return '( %s DChrInd %s )' % (n, m)
def COND(n, x): return '( %s DChrCond %s )' % (n, x)
def PRIM(n, x): return '( %s DChrPrim %s )' % (n, x)
def FZO(m): return '( 0 ..^ %s )' % m
def REPF(m): return '( %s |` %s )' % (LZ(m), FZO(m))
def REP(m, k='k'): return "( `' %s ` %s )" % (REPF(m), k)
def EV(x, n, a): return '( %s ` ( %s ` %s ) )' % (x, LZ(n), a)
def INDV(n, m, x, k='k'): return '( %s ` ( %s ` %s ) )' % (x, LZ(n), REP(m, k))
def INDBODY(n, m, x, k='k'):
    return '( %s e. %s |-> if ( %s e. %s , %s , 0 ) )' % (k, BZ(m), k, UZ(m), INDV(n, m, x, k))
def INDMPT(n, m, x='x'): return '( %s e. %s |-> %s )' % (x, DB(n), INDBODY(n, m, x))
def CSET(n, x, d='d', y='y'):
    return '{ %s e. NN | ( %s || %s /\\ E. %s e. %s %s = %s ) }' % (d, d, n, y, DB(d), x, IND(d, n, y))
def CONDBODY(n, x, d='d', y='y'): return 'inf ( %s , RR , < )' % CSET(n, x, d, y)
def PRIMBODY(n, x, y='y'):
    return '( iota_ %s e. %s %s = %s )' % (y, DB(COND(n, x)), x, IND(COND(n, x), n, y))
def COP(a, n): return '( %s gcd %s ) = 1' % (a, n)

H3 = '( N e. NN /\\ M e. NN /\\ N || M )'
HX = '( %s /\\ X e. %s )' % (H3, DB('N'))

# batch 5: periodicity and the witness construction
def PER(d, n='N', x='X', a='a', b='b'):
    return 'A. %s e. ZZ A. %s e. ZZ ( ( ( %s /\\ %s ) /\\ %s || ( %s - %s ) ) -> %s = %s )' % (
        a, b, COP(a, n), COP(b, n), d, a, b, EV(x, n, a), EV(x, n, b))
def PERAB(A, B, d, n='N', x='X'):
    return '( ( ( %s /\\ %s ) /\\ %s || ( %s - %s ) ) -> %s = %s )' % (COP(A, n), COP(B, n), d, A, B, EV(x, n, A), EV(x, n, B))
def SK(d, n, k, c='c'): return '{ %s e. NN | ( ( %s ` %s ) = %s /\\ %s ) }' % (c, LZ(d), c, k, COP(c, n))
def WIT(d, n, k, c='c'): return 'inf ( %s , RR , < )' % SK(d, n, k, c)
def WV(d, n, x, k, c='c'): return '( %s ` ( %s ` %s ) )' % (x, LZ(n), WIT(d, n, k, c))
def YMPT(d, n, x, k='k'): return '( %s e. %s |-> if ( %s e. %s , %s , 0 ) )' % (k, BZ(d), k, UZ(d), WV(d, n, x, k))
