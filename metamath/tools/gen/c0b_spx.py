"""Sortie C0b, batch 10: the splits parametrised by the cut coordinate
(rectinthspx, rectintvspx)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

RA = RE('A'); RB = RE('B'); IA = IM('A'); IB = IM('B')


def spx(label, desc, lo, hi, lolab, hilab, itv, isre):
    w = W(label, desc)
    A0 = '( %s /\\ %s < %s /\\ X e. %s )' % (PS, lo, hi, itv)
    d = ctx(w, A0)
    lt = w.s([], 'simp2', '( %s -> %s < %s )' % (A0, lo, hi))
    xi = w.s([], 'simp3', '( %s -> X e. %s )' % (A0, itv))
    lor = d[lolab]; hir = d[hilab]
    ex = w.s([lor, hir, w.inst('elicc2')], 'syl2anc', '( %s -> ( X e. %s <-> ( X e. RR /\\ %s <_ X /\\ X <_ %s ) ) )' % (A0, itv, lo, hi))
    tx = w.s([xi, ex], 'mpbid', '( %s -> ( X e. RR /\\ %s <_ X /\\ X <_ %s ) )' % (A0, lo, hi))
    xr = w.s([tx, w.inst('simp1')], 'syl', '( %s -> X e. RR )' % A0)
    lex = w.s([tx, w.inst('simp2')], 'syl', '( %s -> %s <_ X )' % (A0, lo))
    xle = w.s([tx, w.inst('simp3')], 'syl', '( %s -> X <_ %s )' % (A0, hi))
    DEN = '( %s - %s )' % (hi, lo)
    dr = w.s([hir, lor], 'resubcld', '( %s -> %s e. RR )' % (A0, DEN))
    dp = w.s([w.s([lor, hir], 'posdifd', '( %s -> ( %s < %s <-> 0 < %s ) )' % (A0, lo, hi, DEN)), lt], 'mpbid', '( %s -> 0 < %s )' % (A0, DEN))
    drp = w.s([dr, dp], 'elrpd', '( %s -> %s e. RR+ )' % (A0, DEN))
    NUM = '( X - %s )' % lo
    nr = w.s([xr, lor], 'resubcld', '( %s -> %s e. RR )' % (A0, NUM))
    ng = w.s([w.s([xr, lor], 'subge0d', '( %s -> ( 0 <_ %s <-> %s <_ X ) )' % (A0, NUM, lo)), lex], 'mpbird', '( %s -> 0 <_ %s )' % (A0, NUM))
    SS = '( %s / %s )' % (NUM, DEN)
    sr = w.s([nr, drp], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, SS))
    sg = w.s([nr, drp, ng], 'divge0d', '( %s -> 0 <_ %s )' % (A0, SS))
    nle = w.s([w.s([xr, hir, lor], 'lesub1d', '( %s -> ( X <_ %s <-> %s <_ %s ) )' % (A0, hi, NUM, DEN)), xle], 'mpbid', '( %s -> %s <_ %s )' % (A0, NUM, DEN))
    s1le = w.s([w.s([nr, closed(w, A0, '1re', '1 e. RR'), drp], 'ledivmuld', '( %s -> ( %s <_ 1 <-> %s <_ ( %s x. 1 ) ) )' % (A0, SS, NUM, DEN)),
                w.s([nle, w.s([w.s([w.s([dr], 'recnd', '( %s -> %s e. CC )' % (A0, DEN))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A0, DEN, DEN))], 'eqcomd', '( %s -> %s = ( %s x. 1 ) )' % (A0, DEN, DEN))], 'breqtrd', '( %s -> %s <_ ( %s x. 1 ) )' % (A0, NUM, DEN))], 'mpbird',
               '( %s -> %s <_ 1 )' % (A0, SS))
    s01 = w.s([w.s([closed(w, A0, '0re', '0 e. RR'), closed(w, A0, '1re', '1 e. RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) ) )' % (A0, SS, SS, SS, SS)),
               w.s([sr, sg, s1le], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (A0, SS, SS, SS))], 'mpbird', '( %s -> %s e. ( 0 [,] 1 ) )' % (A0, SS))
    dc = w.s([w.s([nr], 'recnd', '( %s -> %s e. CC )' % (A0, NUM)), w.s([dr], 'recnd', '( %s -> %s e. CC )' % (A0, DEN)), w.s([drp, w.inst('rpne0')], 'syl', '( %s -> %s =/= 0 )' % (A0, DEN))], 'divcan2d',
             '( %s -> ( %s x. %s ) = %s )' % (A0, DEN, SS, NUM))
    cmm = w.s([w.s([dr], 'recnd', '( %s -> %s e. CC )' % (A0, DEN)), w.s([sr], 'recnd', '( %s -> %s e. CC )' % (A0, SS))], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, DEN, SS, SS, DEN))
    sd = w.s([w.s([cmm], 'eqcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, SS, DEN, DEN, SS)), dc], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (A0, SS, DEN, NUM))
    xeq = w.s([w.s([sd], 'oveq2d', '( %s -> ( %s + ( %s x. %s ) ) = ( %s + %s ) )' % (A0, lo, SS, DEN, lo, NUM)),
               w.s([w.s([lor], 'recnd', '( %s -> %s e. CC )' % (A0, lo)), w.s([xr], 'recnd', '( %s -> X e. CC )' % A0), w.inst('pncan3')], 'syl2anc', '( %s -> ( %s + %s ) = X )' % (A0, lo, NUM))], 'eqtrd',
              '( %s -> ( %s + ( %s x. %s ) ) = X )' % (A0, lo, SS, DEN))
    xeqc = w.s([xeq], 'eqcomd', '( %s -> X = ( %s + ( %s x. %s ) ) )' % (A0, lo, SS, DEN))
    psx = w.s([d['ab'], d['geo'], w.s([d['fcn'], d['rss']], 'jca', '( %s -> %s )' % (A0, FCN))], '3jca', '( %s -> %s )' % (A0, PS))
    lab = 'rectinthsp' if isre else 'rectintvsp'
    if isre:
        concl = '( %s -> ( F rectint <. A , B >. ) = ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) )' % (A0, PT('X', IB), PT('X', IA))
    else:
        concl = '( %s -> ( F rectint <. A , B >. ) = ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) )' % (A0, PT(RB, 'X'), PT(RA, 'X'))
    w.qed([psx, s01, xeqc, w.inst(lab)], 'syl3anc', concl)
    run(w)


spx('rectinthspx', 'A rectangle boundary integral splits at a vertical cut given by its coordinate.', RA, RB, 'ar', 'br', RI('A', 'B'), True)
spx('rectintvspx', 'A rectangle boundary integral splits at a horizontal cut given by its coordinate.', IA, IB, 'ai', 'bi', II('A', 'B'), False)
