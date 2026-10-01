"""Sortie C1: shared expressions and step patterns (holomorphic functions on
open sets).  Built on tools/gen/c0c_lib.py (sorties C0, C0b, C0c)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c0c_lib import *

only = sys.argv[1:]


def run1(w, h=False):
    if only and w.label not in only:
        return True
    return runh(w) if h else w.run()


# ---- the frame of a rectangle, written out as the union of its four edges ---
EDGES = [('A', P10), (P10, 'B'), ('B', P01), (P01, 'A')]
SEGS = ['( %s cseg %s )' % (s, t) for s, t in EDGES]
FR = '( ( %s u. %s ) u. ( %s u. %s ) )' % tuple(SEGS)
FCNE = '( F e. ( D -cn-> CC ) /\\ %s C_ E /\\ E C_ D )' % FR
PSE = '( %s /\\ %s /\\ %s )' % (AB, GEO, FCNE)


def edges4(w, ante, fr, T='E'):
    """the four edge inclusions ( ante -> ( S cseg T ) C_ E ) from a step fr
    proving ( ante -> FR C_ E )"""
    l = w.s([fr], 'unssad', '( %s -> ( %s u. %s ) C_ %s )' % (ante, SEGS[0], SEGS[1], T))
    r = w.s([fr], 'unssbd', '( %s -> ( %s u. %s ) C_ %s )' % (ante, SEGS[2], SEGS[3], T))
    return [w.s([l], 'unssad', '( %s -> %s C_ %s )' % (ante, SEGS[0], T)),
            w.s([l], 'unssbd', '( %s -> %s C_ %s )' % (ante, SEGS[1], T)),
            w.s([r], 'unssad', '( %s -> %s C_ %s )' % (ante, SEGS[2], T)),
            w.s([r], 'unssbd', '( %s -> %s C_ %s )' % (ante, SEGS[3], T))]


def ovexd(w, ante, expr):
    e = w.s([], 'ovex', '%s e. _V' % expr)
    return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, expr))


def cornerc(w, A0, ac, bc, ar, br, ai, bi):
    """closure of the two computed corners"""
    ic = closed(w, A0, 'ax-icn', '_i e. CC')
    arc = w.s([ar], 'recnd', '( %s -> %s e. CC )' % (A0, RA))
    brc = w.s([br], 'recnd', '( %s -> %s e. CC )' % (A0, RB))
    aic = w.s([ai], 'recnd', '( %s -> %s e. CC )' % (A0, IA))
    bic = w.s([bi], 'recnd', '( %s -> %s e. CC )' % (A0, IB))
    c10 = w.s([brc, w.s([ic, aic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IA))], 'addcld', '( %s -> %s e. CC )' % (A0, P10))
    c01 = w.s([arc, w.s([ic, bic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IB))], 'addcld', '( %s -> %s e. CC )' % (A0, P01))
    return {'A': ac, 'B': bc, P10: c10, P01: c01}


def ctxe(w, A0, ps=None):
    """the standing context of a generic-frame rectangle lemma:
    PSE = ( AB /\\ GEO /\\ ( F e. ( D -cn-> CC ) /\\ FR C_ E /\\ E C_ D ) )"""
    d = {}
    if ps is None:
        ps = w.s([], 'simp1', '( %s -> %s )' % (A0, PSE))
    d['ab'] = ab = w.s([ps, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    d['geo'] = geo = w.s([ps, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, GEO))
    fc = w.s([ps, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, FCNE))
    d['fcn'] = w.s([fc, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    d['fre'] = w.s([fc, w.inst('simp2')], 'syl', '( %s -> %s C_ E )' % (A0, FR))
    d['ed'] = w.s([fc, w.inst('simp3')], 'syl', '( %s -> E C_ D )' % A0)
    d['ac'] = ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    d['bc'] = bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    d['ar'] = ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
    d['br'] = br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
    d['ai'] = ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
    d['bi'] = bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
    d['ler'] = w.s([geo, w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A0, RA, RB))
    d['lei'] = w.s([geo, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A0, IA, IB))
    d['fex'] = w.s([d['fcn'], w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
    d['cc'] = cornerc(w, A0, ac, bc, ar, br, ai, bi)
    d['se'] = se = edges4(w, A0, d['fre'])
    d['sd'] = [w.s([x, d['ed']], 'sstrd', '( %s -> %s C_ D )' % (A0, SEGS[i])) for i, x in enumerate(se)]
    return d


def phsege(w, A0, d, i, Fn='F', fcn=None):
    """( A0 -> PHSEG(S,T) ) for edge i, from the corner closures and edge C_ D"""
    S, T = EDGES[i]
    l = w.s([d['cc'][S], d['cc'][T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
    r = w.s([fcn or d['fcn'], d['sd'][i]], 'jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, Fn, SEGS[i]))
    return w.s([l, r], 'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( D -cn-> CC ) /\\ %s C_ D ) ) )' % (A0, S, T, Fn, SEGS[i]))
