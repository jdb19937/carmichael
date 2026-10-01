"""Sortie C9: helpers (the Landau assembly on squares).  Built on
tools/c8lib.py (C8) and everything underneath it."""
import sys, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from c8lib import *

R74 = '( 7 / 4 )'
R138 = '( ; 1 3 / 8 )'
R18 = '( 1 / 8 )'
K6N = '; ; ; 6 2 7 2'


def stmt(label):
    """the assertion of LABEL from sorties/c9.mm or carmichael.mm, without |-"""
    for fn in ('sorties/c9.mm', 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def ZSQ(c='C', r=R138, F='F'):
    return '{ r e. %s | ( %s ` r ) = 0 }' % (SQ(c, r), F)


SQ74 = SQ('C', R74)
SQ138 = SQ('C', R138)
A74, B74 = SQA('C', R74), SQB('C', R74)
A138, B138 = SQA('C', R138), SQB('C', R138)


def PRZ(T, z, O='O', q='q'):
    return 'prod_ %s e. %s ( ( %s - %s ) ^ ( %s ` %s ) )' % (q, T, z, q, O, q)


def NSUM(T='Z', O='O', q='q'):
    return 'sum_ %s e. %s ( %s ` %s )' % (q, T, O, q)


def EXPL(T, R, O='O'):
    """exp ( ( sum O ) x. log R )"""
    return '( exp ` ( %s x. ( log ` %s ) ) )' % (NSUM(T, O), R)


LOGM = '( ( log ` ( B / ( abs ` ( F ` C ) ) ) ) + ( W x. ( log ` ; 2 6 ) ) )'
FAC = 'A. z e. D ( F ` z ) = ( %s x. ( H ` z ) )' % PRZ('Z', 'z')
DATA = ('( ( %s /\\ ( C e. CC /\\ %s C_ D ) ) /\\ ( ( Z e. Fin /\\ Z C_ %s ) /\\ ( O : Z --> NN /\\ %s ) ) '
        '/\\ ( %s /\\ A. z e. %s ( H ` z ) =/= 0 ) )') % (HOL, SQ74, SQ138, HOLG('H', 'D'), FAC, SQ138)
FBD = '( B e. RR /\\ A. x e. %s ( abs ` ( F ` x ) ) <_ B )' % SQ74

FACQ = 'A. z e. D ( F ` z ) = ( %s x. ( H ` z ) )' % PRZ('Z', 'z')
NZH = 'A. z e. %s ( H ` z ) =/= 0' % SQ138


def data_parts(w, A0, dst):
    """facts from dst : ( A0 -> DATA )"""
    X1 = '( %s /\\ ( C e. CC /\\ %s C_ D ) )' % (HOL, SQ74)
    X2 = '( ( Z e. Fin /\\ Z C_ %s ) /\\ ( O : Z --> NN /\\ %s ) )' % (SQ138, HOLG('H', 'D'))
    X3 = '( %s /\\ %s )' % (FACQ, NZH)
    assert DATA == '( %s /\\ %s /\\ %s )' % (X1, X2, X3)
    x1 = w.s([dst, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, X1))
    x2 = w.s([dst, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, X2))
    x3 = w.s([dst, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, X3))
    d = {}
    d['hol'] = w.s([x1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    d['cs'] = w.s([x1, w.inst('simprl')], 'syl', '( %s -> C e. CC )' % A0)
    d['s74d'] = w.s([x1, w.inst('simprr')], 'syl', '( %s -> %s C_ D )' % (A0, SQ74))
    d['zfin'] = w.s([x2, w.inst('simpll')], 'syl', '( %s -> Z e. Fin )' % A0)
    d['zsq'] = w.s([x2, w.inst('simplr')], 'syl', '( %s -> Z C_ %s )' % (A0, SQ138))
    d['of'] = w.s([x2, w.inst('simprl')], 'syl', '( %s -> O : Z --> NN )' % A0)
    d['holh'] = w.s([x2, w.inst('simprr')], 'syl', '( %s -> %s )' % (A0, HOLG('H', 'D')))
    d['fac'] = w.s([x3, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, FACQ))
    d['hnz'] = w.s([x3, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, NZH))
    return d


def top_and(s):
    """top-level conjuncts of ( a /\\ b [/\\ c] )"""
    t = s.split()
    assert t[0] == '(' and t[-1] == ')'
    t = t[1:-1]
    d = 0; parts = []; cur = []
    for x in t:
        if x == '(':
            d += 1
        elif x == ')':
            d -= 1
        if x == '/\\' and d == 0:
            parts.append(' '.join(cur)); cur = []
            continue
        cur.append(x)
    parts.append(' '.join(cur))
    return parts

# ---- the L-function instance ----------------------------------------------------
HP0 = "( `' Re \" ( 0 (,) +oo ) )"
CHI = '( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ X =/= ( 0g ` ( DChr ` N ) ) )'
C0 = '( 2 + ( _i x. T ) )'
B20 = '( ( ; 2 0 x. N ) x. ( ( abs ` T ) + 2 ) )'


def LSs(v):
    return 'sum_ k e. NN ( sum_ i e. ( 1 ... k ) ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` i ) ) x. ( ( k ^c -u %s ) - ( ( k + 1 ) ^c -u %s ) ) )' % (v, v)


LFN = '( s e. %s |-> %s )' % (HP0, LSs('s'))
