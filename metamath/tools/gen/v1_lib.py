"""Shared expressions of sortie V1 (PsiTheta.lean, Mertens.lean)."""

def COND(n, q, a): return '( %s mod %s ) = ( %s mod %s )' % (n, q, a, q)
def IFL(n, q, a): return 'if ( %s , ( Lam ` %s ) , 0 )' % (COND(n, q, a), n)
def FZ(y): return '( 1 ... ( |_ ` %s ) )' % y
def PSISUM(q, a, y, n='n'): return 'sum_ %s e. %s %s' % (n, FZ(y), IFL(n, q, a))
def RAB(q, a, y, n='n'): return '{ %s e. %s | ( %s e. Prime /\\ %s ) }' % (n, FZ(y), n, COND(n, q, a))
def THSUM(q, a, y): return 'sum_ p e. %s ( log ` p )' % RAB(q, a, y)
def PISUM(q, a, y): return '( # ` %s )' % RAB(q, a, y)
def LZ(q): return '( ZRHom ` ( Z/nZ ` %s ) )' % q
def DB(q): return '( Base ` ( DChr ` %s ) )' % q
def CHTERM(q, x, n): return '( ( %s ` ( %s ` %s ) ) x. ( Lam ` %s ) )' % (x, LZ(q), n, n)
def CHSUM(q, x, y, n='n'): return 'sum_ %s e. %s %s' % (n, FZ(y), CHTERM(q, x, n))
def MPO(body): return '( a e. ZZ , y e. RR |-> %s )' % body
def MPOX(q, body): return '( x e. %s , y e. RR |-> %s )' % (DB(q), body)

H = '( Q e. NN /\\ A e. ZZ /\\ Y e. RR )'
HX = '( Q e. NN /\\ X e. %s /\\ Y e. RR )' % DB('Q')
PSI = '( A ( psiAP ` Q ) Y )'
TH = '( A ( thetaAP ` Q ) Y )'
PI = '( A ( piAP ` Q ) Y )'
PSICH = '( X ( psiChar ` Q ) Y )'
S = RAB('Q', 'A', 'Y')
M = '( |_ ` Y )'
P = '( ( 1 ... ( |_ ` Y ) ) i^i Prime )'
NP = '( ( 1 ... ( |_ ` Y ) ) \\ Prime )'
SL = '( ( 2 x. ( sqrt ` Y ) ) x. ( log ` Y ) )'
