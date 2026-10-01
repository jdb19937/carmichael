"""Sortie C10: helpers (the zero count and the centre bound for the Landau
expansion).  Built on tools/c9lib.py (C9) and everything underneath it."""
import sys, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from c9lib import *


def stmt(label):
    """the assertion of LABEL from sorties/c10.mm or carmichael.mm, without |-"""
    for fn in ('sorties/c10.mm', 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def FRM(c, r):
    """the frame of SQ(c, r)"""
    return FRG(SQA(c, r), SQB(c, r))


def BLF(k, s, C='C', R='R'):
    """the normalised Blaschke numerator ( R - ( ( * ( k - C ) / R ) x. ( s - C ) ) )"""
    return '( %s - ( ( ( * ` ( %s - %s ) ) / %s ) x. ( %s - %s ) ) )' % (R, k, C, R, s, C)


def PBL(s, Z='Z', O='O', k='k', C='C', R='R'):
    return 'prod_ %s e. %s ( %s ^ ( %s ` %s ) )' % (k, Z, BLF(k, s, C, R), O, k)


def ENT(M):
    return '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (M, M)


R2524 = '( ; 2 5 / ; 2 4 )'
R4225 = '( ; 4 2 / ; 2 5 )'
R1332 = '( ; 1 3 / ; 3 2 )'
R3932 = '( ; 3 9 / ; 3 2 )'
XT = '( N x. ( ( abs ` T ) + 2 ) )'
B40 = '( ; 4 0 x. %s )' % XT
B80 = '( ; 8 0 x. %s )' % XT


def QA(t):
    return '( ( 3 / 8 ) + ( _i x. ( %s - %s ) ) )' % (t, R1332)


def QB(t):
    return '( ( ; 2 9 / 8 ) + ( _i x. ( %s + %s ) ) )' % (t, R1332)


def ZQ(t, F=None):
    F = F or LFN
    return '{ r e. ( %s crect %s ) | ( %s ` r ) = 0 }' % (QA(t), QB(t), F)


def CT(t):
    return '( 2 + ( _i x. %s ) )' % t


def ent_tr(w, ante, eq, ent, M1, M2, D='CC'):
    """( ante -> HOL(M2, D) ) from eq : ( ante -> M1 = M2 ), ent : ( ante -> HOL(M1, D) )"""
    E1 = '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (M1, D, D, M1)
    cn1 = w.s([ent, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (ante, M1, D))
    dm1 = w.s([ent, w.inst('simpr')], 'syl', '( %s -> %s C_ dom ( CC _D %s ) )' % (ante, D, M1))
    cn2 = w.s([w.s([eq], 'eqcomd', '( %s -> %s = %s )' % (ante, M2, M1)), cn1], 'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (ante, M2, D))
    de = w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (ante, M1, M2))], 'dmeqd',
             '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (ante, M1, M2))
    dm2 = w.s([dm1, de], 'sseqtrd', '( %s -> %s C_ dom ( CC _D %s ) )' % (ante, D, M2))
    return w.s([cn2, dm2], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (ante, M2, D, D, M2))


def subst_eq(w, body, x, y):
    """closed step ( x = y -> body = body[x:=y] ); returns (step, new)"""
    import congr as _cg
    eq = '%s = %s' % (x, y)
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    g = w.g
    st, val = _cg.congruence(body, {x: y}, eq, {x: idx}, g)
    w.lines.extend(g.lines); g.lines = []
    return st, val


def patch_stmt(*mods):
    """point stmt() of C9's generator modules at this sortie's database"""
    for m in mods:
        m.stmt = stmt
