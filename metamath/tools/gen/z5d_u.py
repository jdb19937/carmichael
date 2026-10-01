"""Sortie Z5d, section U: Proposition 4.4 with I8(b) and I9(b) discharged (Detection.lean 432-488, 796-803)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5dlib import *
from cl import Closure, lift, split_imp
import lin
import num

TS = '( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) )'
SS = '( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) )'
K60 = '( ; 6 0 e. RR /\\ 1 <_ ; 6 0 )'
GAM60 = GAMH60


def z5ddlb1():
    w = W('z5ddlb1', "Blueprint Proposition 4.4 with I8(b) discharged (Lean detector_lower_bound_of_P1): z5dlbe at CGamma' = 60 with the "
                     "Gamma decay z5dgamh; I9(b) (hP1) and the detection estimate remain hypotheses.")
    a = ante('z5ddlb1')
    st = mkst(w, a)
    a1d = st([], 'simpl', A1D)
    hz = st([a1d], 'simpld', '( %s /\\ N e. NN )' % HZD3)
    ts = st([st([a1d], 'simprd', '( %s /\\ %s )' % (TS, SS))], 'simpld', TS)
    ss = st([st([a1d], 'simprd', '( %s /\\ %s )' % (TS, SS))], 'simprd', SS)
    k60 = st([a1(w, a, num.real(w, '; 6 0'), '; 6 0 e. RR'), a1(w, a, num.le_lit(w, '1', '; 6 0'), '1 <_ ; 6 0')], 'jca', K60)
    gh = a1(w, a, w.s([], 'z5dgamh', GAM60), GAM60)
    A1 = st([hz, st([st([ts, k60], 'jca', '( %s /\\ %s )' % (TS, K60)), st([gh, ss], 'jca', '( %s /\\ %s )' % (GAM60, SS))], 'jca',
                    '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (TS, K60, GAM60, SS))], 'jca', '( ( %s /\\ N e. NN ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (HZD3, TS, K60, GAM60, SS))
    A2 = st([], 'simpr', '( ( C : NN --> CC /\\ %s ) /\\ ( F e. CC /\\ ( %s /\\ %s ) ) )' % (HGAM60, HP1_, HDET_))
    inst = Z5CS['z5dlbe'].replace('( K e. RR /\\ 1 <_ K )', K60).replace('( K x. ', '( ; 6 0 x. ').replace('x. K ) )', 'x. ; 6 0 ) )')
    ai, ci = split_imp(inst)
    w.qed([st([A1, A2], 'jca', ai), w.inst('z5dlbe')], 'syl', STATEMENTS['z5ddlb1'])
    return w


def z5ddlb():
    w = W('z5ddlb', "THE DELIVERABLE of Detection.lean (Lean detector_lower_bound_uncond): blueprint Proposition 4.4 with I8(b) (z5dgamh, "
                    "CGamma' = 60), I9(b) (P1_lower, z5dp1low) and I9(c) (its corrected replacement inside z5epole) discharged; the frozen "
                    "conclusion ( 1 / 400 ) ( phi ( N ) / N ) log D <_ | F | under the frozen Lambda0 clause, the detection estimate "
                    "(blueprint Lemmas 4.1 + 4.2) the one hypothesis left.")
    a = ante('z5ddlb')
    st = mkst(w, a)
    a1d = st([], 'simpl', A1D)
    hz = st([a1d], 'simpld', '( %s /\\ N e. NN )' % HZD3)
    h3 = st([hz], 'simpld', HZD3)
    nn = st([hz], 'simprd', 'N e. NN')
    dr = st([h3], 'simp1d', 'D e. RR'); d1 = st([h3], 'simp2d', '1 < D')
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': ('RR', dr)})], 'elrpd', 'D e. RR+')
    hp = st([nn, drp, w.inst('z5dp1low')], 'syl2anc', HP1_)
    a2 = st([], 'simpr', '( ( C : NN --> CC /\\ %s ) /\\ ( F e. CC /\\ %s ) )' % (HGAM60, HDET_))
    cg = st([a2], 'simpld', '( C : NN --> CC /\\ %s )' % HGAM60)
    fd = st([a2], 'simprd', '( F e. CC /\\ %s )' % HDET_)
    fc = st([fd], 'simpld', 'F e. CC'); hd = st([fd], 'simprd', HDET_)
    b = st([a1d, st([cg, st([fc, st([hp, hd], 'jca', '( %s /\\ %s )' % (HP1_, HDET_))], 'jca', '( F e. CC /\\ ( %s /\\ %s ) )' % (HP1_, HDET_))], 'jca',
                    '( ( C : NN --> CC /\\ %s ) /\\ ( F e. CC /\\ ( %s /\\ %s ) ) )' % (HGAM60, HP1_, HDET_))], 'jca', ante('z5ddlb1'))
    w.qed([b, w.inst('z5ddlb1')], 'syl', STATEMENTS['z5ddlb'])
    return w


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        if os.environ.get('Z5D_WRITE_ONLY'):
            w.write()
        else:
            run(w)
