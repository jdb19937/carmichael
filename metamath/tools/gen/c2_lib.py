"""Sortie C2: shared expressions and step patterns (growth and convexity).
Built on tools/gen/c1_lib.py (sorties C0, C0b, C0c, C1)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c1_lib import *

# holomorphy on an open domain: continuous on D and differentiable at every
# point of D (which forces D open, holopn)
HOL = '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) )'


def HOLG(Fn, Dm='D'):
    return '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (Fn, Dm, Dm, Fn)


def MP(x, X, E):
    return '( %s e. %s |-> %s )' % (x, X, E)


PER = '( ( %s - %s ) + ( %s - %s ) )' % (RB, RA, IB, IA)
RP = RE('P'); IP = IM('P'); RZ = RE('Z'); IZ = IM('Z')
INTP = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RP, RP, RB, IA, IP, IP, IB)
INTZ = '( Z e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RZ, RZ, RB, IA, IZ, IZ, IB)
HOLO = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) )'


def RBD(V, R='R'):
    rv = RE(V); iv = IM(V)
    return '( %s e. RR /\\ ( ( %s <_ ( %s - %s ) /\\ %s <_ ( %s - %s ) ) /\\ ( %s <_ ( %s - %s ) /\\ %s <_ ( %s - %s ) ) ) )' % (
        R, R, rv, RA, R, RB, rv, R, iv, IA, R, IB, iv)


def simps(w, A0, st, n, forms):
    """split a step proving ( A0 -> ( f1 /\\ ... /\\ fn ) ) into its conjuncts"""
    refs = {2: ['simpl', 'simpr'], 3: ['simp1', 'simp2', 'simp3'],
            4: ['simp1', 'simp2', 'simp3', 'simp4'], 5: ['simp1', 'simp2', 'simp3', 'simp4', 'simp5'],
            6: ['simp1', 'simp2', 'simp3', 'simp4', 'simp5', 'simp6']}[n]
    return [w.s([st, w.inst(refs[i])], 'syl', '( %s -> %s )' % (A0, forms[i])) for i in range(n)]


def top(w, A0):
    """(eqid step J = TOP, step ( A0 -> TOP e. Top ))"""
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    t = w.s([w.s([e], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP))
    return e, t


def dvdom(w, A0, mp, x, X, rhs, dveq, cls):
    """( A0 -> X C_ dom ( CC _D mp ) ) from dveq: ( A0 -> ( CC _D mp ) = ( x e. X |-> rhs ) )
    and cls: ( ( A0 /\\ x e. X ) -> rhs e. CC )"""
    eqm = w.s([], 'eqid', '%s = %s' % (MP(x, X, rhs), MP(x, X, rhs)))
    ffn = w.s([cls, eqm], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, MP(x, X, rhs), X))
    dm = w.s([ffn, w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (A0, MP(x, X, rhs), X))
    d1 = w.s([dveq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (A0, mp, MP(x, X, rhs)))
    d2 = w.s([d1, dm], 'eqtrd', '( %s -> dom ( CC _D %s ) = %s )' % (A0, mp, X))
    return w.s([w.s([d2], 'eqcomd', '( %s -> %s = dom ( CC _D %s ) )' % (A0, X, mp))], 'eqimssd',
               '( %s -> %s C_ dom ( CC _D %s ) )' % (A0, X, mp))


def mptval(w, ante, x, X, MPX, T, bodyT, sub, mem):
    """( ante -> ( MPX ` T ) = bodyT ) from sub: ( x = T -> body = bodyT ) and mem: ( ante -> T e. X )"""
    em = w.s([], 'eqid', '%s = %s' % (MPX, MPX))
    fm = w.s([sub, em], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (T, X, bodyT, MPX, T, bodyT))
    return w.s([mem, ovexd(w, ante, bodyT), fm], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, MPX, T, bodyT))


def absbnds(w, ante, X, xr):
    """steps ( ante -> -u ( abs ` X ) <_ X ) and ( ante -> X <_ ( abs ` X ) )"""
    ax = w.s([w.s([xr], 'recnd', '( %s -> %s e. CC )' % (ante, X))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (ante, X))
    bi = w.s([xr, ax, w.inst('absle')], 'syl2anc',
             '( %s -> ( ( abs ` %s ) <_ ( abs ` %s ) <-> ( -u ( abs ` %s ) <_ %s /\\ %s <_ ( abs ` %s ) ) ) )' % (ante, X, X, X, X, X, X))
    both = w.s([w.s([ax], 'leidd', '( %s -> ( abs ` %s ) <_ ( abs ` %s ) )' % (ante, X, X)), bi], 'mpbid',
               '( %s -> ( -u ( abs ` %s ) <_ %s /\\ %s <_ ( abs ` %s ) ) )' % (ante, X, X, X, X))
    return (w.s([both, w.inst('simpl')], 'syl', '( %s -> -u ( abs ` %s ) <_ %s )' % (ante, X, X)),
            w.s([both, w.inst('simpr')], 'syl', '( %s -> %s <_ ( abs ` %s ) )' % (ante, X, X)), ax)
