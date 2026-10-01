"""Sortie BM: BMembership21.lean (bmlow = bMembership21.lower, bmpil = piLower_of_density,
bmpig21b = bMembership21 + pigeonhole_21 at the witnesses, bmpig21a = pigeonhole_21,
bmpig21 = pigeonhole_21')."""
import sys, os
from fractions import Fraction
sys.path.insert(0, os.path.dirname(__file__))
from bm_base import *
from bm_pdl import frac_add


def gen_low():
    w = W('bmlow', 'The ` B ` -membership lower bound at ` B = 21 / 100 ` (Lean ` bMembership21.lower ` ): T2.1 at ` 1 / 12 ` gives ` theta ( g ; e , q ) >_ ( 11 / 12 ) g / phi ( e ) ` , ~ lepiap turns it into ` pi ( g ; e , q ) ` , and Chebyshev\'s ` pi ( g ) <_ ( log 4 + 1 / 10 ) g / log g ` with ` log 4 + 1 / 10 <_ 11 / 6 ` (~ bmlog4 ) gives ` pi ( g ) / ( 2 phi ( e ) ) <_ pi ( g ; e , q ) ` ; the threshold ` |B| + ( S + 1 ) ^ 2 + 2 ` puts ` g ` past the Chebyshev threshold ` S ` .')
    BPX = BP('B', 'S')
    A0 = '( ( B e. RR /\\ %s ) /\\ %s /\\ ( S e. NN /\\ %s ) )' % (FMAP('F'), THETA('B', 'F'), PPIB('S'))
    u0 = unpack(w, A0)
    C1 = '( %s /\\ ( ( c e. NN0 /\\ g e. NN0 ) /\\ ( e e. NN /\\ q e. ZZ ) ) )' % A0
    LB = LOWER(BPX, 'F')[len('A. c e. NN0 A. g e. NN0 A. e e. NN A. q e. ZZ '):]
    HYPL, GOALL = split_imp(LB)
    C2 = '( %s /\\ %s )' % (C1, HYPL)
    s = S_(w, C2)
    L = lambda st: lift(w, st, C2)
    br, fmap, theta, sn, ppib = L(u0['B e. RR']), L(u0[FMAP('F')]), L(u0[THETA('B', 'F')]), L(u0['S e. NN']), L(u0[PPIB('S')])
    vars_ = w.s([], 'simpr', '( %s -> ( ( c e. NN0 /\\ g e. NN0 ) /\\ ( e e. NN /\\ q e. ZZ ) ) )' % C1)
    vu = unpack_step(w, C1, vars_, '( ( c e. NN0 /\\ g e. NN0 ) /\\ ( e e. NN /\\ q e. ZZ ) )')
    cn0, gn0, en, qz = L(vu['c e. NN0']), L(vu['g e. NN0']), L(vu['e e. NN']), L(vu['q e. ZZ'])
    hy = s([], 'simpr', HYPL)
    hu = unpack_step(w, C2, hy, HYPL)
    bpc, qe, exb, ex1g, gc, bad = hu['%s <_ c' % BPX], hu['( q gcd e ) = 1'], hu['e <_ %s' % XB('c')], hu['( e x. %s ) <_ g' % X1B('c')], hu['g <_ c'], hu['A. i e. ( F ` c ) -. i || e']
    cr = s([cn0], 'nn0red', 'c e. RR'); gr = s([gn0], 'nn0red', 'g e. RR'); er = s([en], 'nnred', 'e e. RR')
    babs = s([s([br], 'recnd', 'B e. CC')], 'abscld', '( abs ` B ) e. RR'); bleabs = s([br], 'leabsd', 'B <_ ( abs ` B )')
    S1 = '( S + 1 )'
    s1r = s([s([sn], 'nnred', 'S e. RR'), s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')], 'readdcld', '%s e. RR' % S1)
    s1sq = s([s1r], 'resqcld', '( %s ^ 2 ) e. RR' % S1); s1sq0 = s([s1r], 'sqge0d', '0 <_ ( %s ^ 2 )' % S1)
    lv = {'B': br, '( abs ` B )': babs, '( %s ^ 2 )' % S1: s1sq, 'c': cr, 'S': s([sn], 'nnred', 'S e. RR')}
    bc = lin.linarith(w, C2, [bpc, bleabs, s1sq0], 'B <_ c', leaves=lv, atoms=['( %s ^ 2 )' % S1], fast=False)
    sqc = lin.linarith(w, C2, [bpc, s([s([br], 'recnd', 'B e. CC')], 'absge0d', '0 <_ ( abs ` B )')], '( %s ^ 2 ) <_ c' % S1, leaves=lv, atoms=['( %s ^ 2 )' % S1], fast=False)
    c2 = lin.linarith(w, C2, [bpc, s([s([br], 'recnd', 'B e. CC')], 'absge0d', '0 <_ ( abs ` B )'), s1sq0], '2 <_ c', leaves=lv, atoms=['( %s ^ 2 )' % S1], fast=False)
    c1 = lin.linarith(w, C2, [c2], '1 <_ c', leaves={'c': cr}); c1lt = lin.linarith(w, C2, [c2], '1 < c', leaves={'c': cr})
    # T2.1 at ( c , e , q , g )
    TB = THETA('B', 'F')[len('A. n e. NN0 A. d e. NN A. a e. ZZ A. z e. RR '):]
    t1, b1 = wc(w, TB, 'n', 'c'); t2, b2 = wc(w, b1, 'd', 'e'); t3, b3 = wc(w, b2, 'a', 'q'); t4, b4 = wc(w, b3, 'z', 'g')
    TH = '( q ( thetaAP ` e ) g )'; GP = '( g / ( phi ` e ) )'; BND = '( ( %s x. g ) / ( phi ` e ) )' % F112
    TANTE = '( ( B <_ c /\\ ( q gcd e ) = 1 ) /\\ ( e <_ ( c ^c %s ) /\\ ( e x. ( c ^c %s ) ) <_ g /\\ g <_ c ) /\\ A. i e. ( F ` c ) -. i || e )' % (F191, F709)
    TINST = '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (TANTE, TH, GP, BND)
    assert b4 == TINST, (b4[:200], TINST[:200])
    MEM4 = '( ( c e. NN0 /\\ e e. NN ) /\\ ( q e. ZZ /\\ g e. RR ) )'
    r4 = w.s([t1, t2, t3, t4], 'rspc4v', '( %s -> ( %s -> %s ) )' % (MEM4, THETA('B', 'F'), TINST))
    mem4 = s([s([cn0, en], 'jca', '( c e. NN0 /\\ e e. NN )'), s([qz, gr], 'jca', '( q e. ZZ /\\ g e. RR )')], 'jca', MEM4)
    tinst = s([theta, s([mem4, r4], 'syl', '( %s -> %s )' % (THETA('B', 'F'), TINST))], 'mpd', TINST)
    xbr = s([cr, s([cn0], 'nn0ge0d', '0 <_ c'), s([num.real(w, F21)], 'a1i', '%s e. RR' % F21)], 'recxpcld', '%s e. RR' % XB('c'))
    c191r = s([cr, s([cn0], 'nn0ge0d', '0 <_ c'), s([num.real(w, F191)], 'a1i', '%s e. RR' % F191)], 'recxpcld', '( c ^c %s ) e. RR' % F191)
    le191 = s([cr, c1, s([num.real(w, F21)], 'a1i', '%s e. RR' % F21), s([num.real(w, F191)], 'a1i', '%s e. RR' % F191), s([num.le_lit(w, F21, F191)], 'a1i', '%s <_ %s' % (F21, F191))], 'cxplead', '%s <_ ( c ^c %s )' % (XB('c'), F191))
    e191 = s([er, xbr, c191r, exb, le191], 'letrd', 'e <_ ( c ^c %s )' % F191)
    c709r = s([cr, s([cn0], 'nn0ge0d', '0 <_ c'), s([num.real(w, F709)], 'a1i', '%s e. RR' % F709)], 'recxpcld', '( c ^c %s ) e. RR' % F709)
    x1r = s([cr, s([cn0], 'nn0ge0d', '0 <_ c'), s([num.real(w, F79)], 'a1i', '%s e. RR' % F79)], 'recxpcld', '%s e. RR' % X1B('c'))
    le709 = s([cr, c1, s([num.real(w, F709)], 'a1i', '%s e. RR' % F709), s([num.real(w, F79)], 'a1i', '%s e. RR' % F79), s([num.le_lit(w, F709, F79)], 'a1i', '%s <_ %s' % (F709, F79))], 'cxplead', '( c ^c %s ) <_ %s' % (F709, X1B('c')))
    ege0 = s([s([en], 'nnnn0d', 'e e. NN0')], 'nn0ge0d', '0 <_ e')
    ex709 = s([s([er, c709r], 'remulcld', '( e x. ( c ^c %s ) ) e. RR' % F709), s([er, x1r], 'remulcld', '( e x. %s ) e. RR' % X1B('c')), gr, s([c709r, x1r, er, ege0, le709], 'lemul2ad', '( e x. ( c ^c %s ) ) <_ ( e x. %s )' % (F709, X1B('c'))), ex1g], 'letrd', '( e x. ( c ^c %s ) ) <_ g' % F709)
    tante = s([s([bc, qe], 'jca', '( B <_ c /\\ ( q gcd e ) = 1 )'), s([e191, ex709, gc], '3jca', '( e <_ ( c ^c %s ) /\\ ( e x. ( c ^c %s ) ) <_ g /\\ g <_ c )' % (F191, F709)), bad], '3jca', TANTE)
    tabs = s([tante, tinst], 'mpd', '( abs ` ( %s - %s ) ) <_ %s' % (TH, GP, BND))
    # ( 11 / 12 ) GP <_ TH
    phn = s([en], 'phicld', '( phi ` e ) e. NN'); phr = s([phn], 'nnred', '( phi ` e ) e. RR'); phrp = s([phn], 'nnrpd', '( phi ` e ) e. RR+')
    thr = s([en, qz, gr, w.inst('thetaapcl')], 'syl3anc', '%s e. RR' % TH)
    gpr = s([gr, phrp], 'rerpdivcld', '%s e. RR' % GP)
    bndr = s([s([s([num.real(w, F112)], 'a1i', '%s e. RR' % F112), gr], 'remulcld', '( %s x. g ) e. RR' % F112), phrp], 'rerpdivcld', '%s e. RR' % BND)
    absl = s([tabs, s([s([thr, gpr], 'resubcld', '( %s - %s ) e. RR' % (TH, GP)), bndr], 'absled', '( ( abs ` ( %s - %s ) ) <_ %s <-> ( -u %s <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s ) )' % (TH, GP, BND, BND, TH, GP, TH, GP, BND))], 'mpbid', '( -u %s <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s )' % (BND, TH, GP, TH, GP, BND))
    lo = s([absl], 'simpld', '-u %s <_ ( %s - %s )' % (BND, TH, GP))
    bnde = s([s([num.cc(w, F112)], 'a1i', '%s e. CC' % F112), s([gr], 'recnd', 'g e. CC'), s([phrp], 'rpcnd', '( phi ` e ) e. CC'), s([phrp], 'rpne0d', '( phi ` e ) =/= 0')], 'divassd', '%s = ( %s x. %s )' % (BND, F112, GP))
    F1112 = '( ; 1 1 / ; 1 2 )'
    thlow = lin.linarith(w, C2, [lo, bnde], '( %s x. %s ) <_ %s' % (F1112, GP, TH), leaves={TH: thr, GP: gpr, BND: bndr}, atoms=[TH, GP, BND], fast=False)
    # 1 < g
    c0 = s([cr, s([cn0], 'nn0ge0d', '0 <_ c'), s([num.real(w, F79)], 'a1i', '%s e. RR' % F79)], 'cxpge0d', '0 <_ %s' % X1B('c'))
    lt0 = s([s([num.fact(w, F79, 'gt0')], 'a1i', '0 < %s' % F79), s([cr, c1lt, s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([num.real(w, F79)], 'a1i', '%s e. RR' % F79)], 'cxpltd', '( 0 < %s <-> ( c ^c 0 ) < %s )' % (F79, X1B('c')))], 'mpbid', '( c ^c 0 ) < %s' % X1B('c'))
    x1gt1 = s([s([s([cr], 'recnd', 'c e. CC')], 'cxp0d', '( c ^c 0 ) = 1'), lt0], 'eqbrtrrd', '1 < %s' % X1B('c'))
    x1lee = s([x1r, er, c0, s([en], 'nnge1d', '1 <_ e')], 'lemulge12d', '%s <_ ( e x. %s )' % (X1B('c'), X1B('c')))
    x1leg = s([x1r, s([er, x1r], 'remulcld', '( e x. %s ) e. RR' % X1B('c')), gr, x1lee, ex1g], 'letrd', '%s <_ g' % X1B('c'))
    g1 = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), x1r, gr, x1gt1, x1leg], 'ltletrd', '1 < g')
    # pi ( g ; e , q ) >_ ( ( 11 / 12 ) GP ) / log g, and = the count
    HALF = '( %s x. %s )' % (F1112, GP)
    halfr = s([s([num.real(w, F1112)], 'a1i', '%s e. RR' % F1112), gpr], 'remulcld', '%s e. RR' % HALF)
    LG = '( log ` g )'
    pia = s([s([s([en, qz], 'jca', '( e e. NN /\\ q e. ZZ )'), s([gr, g1], 'jca', '( g e. RR /\\ 1 < g )'), s([halfr, thlow], 'jca', '( %s e. RR /\\ %s <_ %s )' % (HALF, HALF, TH))], '3jca', '( ( e e. NN /\\ q e. ZZ ) /\\ ( g e. RR /\\ 1 < g ) /\\ ( %s e. RR /\\ %s <_ %s ) )' % (HALF, HALF, TH)), w.inst('lepiap')], 'syl', '( %s / %s ) <_ ( q ( piAP ` e ) g )' % (HALF, LG))
    pnn = s([en, qz, gn0, w.inst('piapnn')], 'syl3anc', '( q ( piAP ` e ) g ) = %s' % RESCNT('g', 'e', 'q'))
    pib = s([pia, pnn], 'breqtrd', '( %s / %s ) <_ %s' % (HALF, LG, RESCNT('g', 'e', 'q')))
    # Chebyshev at g
    s1ge1 = lin.linarith(w, C2, [s([sn], 'nnge1d', '1 <_ S')], '1 <_ %s' % S1, leaves={'S': s([sn], 'nnred', 'S e. RR')})
    s1rp = s([sn], 'peano2nnd', '%s e. NN' % S1); s1rp = s([s1rp], 'nnrpd', '%s e. RR+' % S1)
    F7950 = num.lit_text(Fraction(79, 50))
    y1 = s([s1r, s1ge1, s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), s([num.real(w, F7950)], 'a1i', '%s e. RR' % F7950), s([num.le_lit(w, '1', F7950)], 'a1i', '1 <_ %s' % F7950)], 'cxplead', '( %s ^c 1 ) <_ ( %s ^c %s )' % (S1, S1, F7950))
    y2 = s([s([s([s1r], 'recnd', '%s e. CC' % S1)], 'cxp1d', '( %s ^c 1 ) = %s' % (S1, S1)), y1], 'eqbrtrrd', '%s <_ ( %s ^c %s )' % (S1, S1, F7950))
    y3 = s([s1rp, s([num.real(w, '2')], 'a1i', '2 e. RR'), s([num.cc(w, F79)], 'a1i', '%s e. CC' % F79)], 'cxpmuld', '( %s ^c ( 2 x. %s ) ) = ( ( %s ^c 2 ) ^c %s )' % (S1, F79, S1, F79))
    y4 = s([s([num.mul_lits(w, '2', F79)], 'a1i', '( 2 x. %s ) = %s' % (F79, F7950))], 'oveq2d', '( %s ^c ( 2 x. %s ) ) = ( %s ^c %s )' % (S1, F79, S1, F7950))
    y5 = s([s([s1r], 'recnd', '%s e. CC' % S1), s([num.nn0(w, 2)], 'a1i', '2 e. NN0'), w.inst('cxpexp')], 'syl2anc', '( %s ^c 2 ) = ( %s ^ 2 )' % (S1, S1))
    y6 = s([y5], 'oveq1d', '( ( %s ^c 2 ) ^c %s ) = ( ( %s ^ 2 ) ^c %s )' % (S1, F79, S1, F79))
    y7 = s([s([y4, y3], 'eqtr3d', '( %s ^c %s ) = ( ( %s ^c 2 ) ^c %s )' % (S1, F7950, S1, F79)), y6], 'eqtrd', '( %s ^c %s ) = ( ( %s ^ 2 ) ^c %s )' % (S1, F7950, S1, F79))
    y8 = s([s1sq, s1sq0, cr, s([num.real(w, F79)], 'a1i', '%s e. RR' % F79), s([num.fact(w, F79, 'ge0')], 'a1i', '0 <_ %s' % F79), sqc], 'cxple2ad', '( ( %s ^ 2 ) ^c %s ) <_ %s' % (S1, F79, X1B('c')))
    sq79r = s([s1sq, s1sq0, s([num.real(w, F79)], 'a1i', '%s e. RR' % F79)], 'recxpcld', '( ( %s ^ 2 ) ^c %s ) e. RR' % (S1, F79))
    y9 = s([s1r, sq79r, x1r, s([y2, y7], 'breqtrd', '%s <_ ( ( %s ^ 2 ) ^c %s )' % (S1, S1, F79)), y8], 'letrd', '%s <_ %s' % (S1, X1B('c')))
    sleg = s([s([sn], 'nnred', 'S e. RR'), s1r, gr, lin.linarith(w, C2, [], 'S <_ %s' % S1, leaves={'S': s([sn], 'nnred', 'S e. RR')}), s([s1r, x1r, gr, y9, x1leg], 'letrd', '%s <_ g' % S1)], 'letrd', 'S <_ g')
    guz = s([s([s([sn], 'nnzd', 'S e. ZZ'), s([gn0], 'nn0zd', 'g e. ZZ'), sleg], '3jca', '( S e. ZZ /\\ g e. ZZ /\\ S <_ g )'), w.s([], 'eluz2', '( g e. ( ZZ>= ` S ) <-> ( S e. ZZ /\\ g e. ZZ /\\ S <_ g ) )')], 'sylibr', 'g e. ( ZZ>= ` S )')
    cg, chb = wc(w, PPIB('S')[len('A. y e. ( ZZ>= ` S ) '):], 'y', 'g')
    cheb = s([cg, ppib, guz], 'rspcdva', chb)
    L4 = '( ( log ` 4 ) + %s )' % F110
    assert chb == '( ppi ` g ) <_ ( ( %s x. g ) / %s )' % (L4, LG), chb
    # the chain
    lgrp = s([gr, g1], 'rplogcld', '%s e. RR+' % LG)
    l4r = s([s([s([num.rp_nat(w, 4)], 'a1i', '4 e. RR+')], 'relogcld', '( log ` 4 ) e. RR'), s([num.real(w, F110)], 'a1i', '%s e. RR' % F110)], 'readdcld', '%s e. RR' % L4)
    gge0 = s([gn0], 'nn0ge0d', '0 <_ g')
    m1 = s([l4r, s([num.real(w, F116)], 'a1i', '%s e. RR' % F116), gr, gge0, s([w.s([], 'bmlog4', S['bmlog4'])], 'a1i', S['bmlog4'])], 'lemul1ad', '( %s x. g ) <_ ( %s x. g )' % (L4, F116))
    m2 = s([m1, s([s([l4r, gr], 'remulcld', '( %s x. g ) e. RR' % L4), s([s([num.real(w, F116)], 'a1i', '%s e. RR' % F116), gr], 'remulcld', '( %s x. g ) e. RR' % F116), lgrp], 'lediv1d', '( ( %s x. g ) <_ ( %s x. g ) <-> ( ( %s x. g ) / %s ) <_ ( ( %s x. g ) / %s ) )' % (L4, F116, L4, LG, F116, LG))], 'mpbid', '( ( %s x. g ) / %s ) <_ ( ( %s x. g ) / %s )' % (L4, LG, F116, LG))
    ppir = s([s([gr, w.inst('ppicl')], 'syl', '( ppi ` g ) e. NN0')], 'nn0red', '( ppi ` g ) e. RR')
    Q6 = '( ( %s x. g ) / %s )' % (F116, LG)
    q6r = s([s([s([num.real(w, F116)], 'a1i', '%s e. RR' % F116), gr], 'remulcld', '( %s x. g ) e. RR' % F116), lgrp], 'rerpdivcld', '%s e. RR' % Q6)
    m3 = s([ppir, s([s([l4r, gr], 'remulcld', '( %s x. g ) e. RR' % L4), lgrp], 'rerpdivcld', '( ( %s x. g ) / %s ) e. RR' % (L4, LG)), q6r, cheb, m2], 'letrd', '( ppi ` g ) <_ %s' % Q6)
    P2 = '( 2 x. ( phi ` e ) )'
    p2rp = s([s([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), phrp], 'rpmulcld', '%s e. RR+' % P2)
    m4 = s([m3, s([ppir, q6r, p2rp], 'lediv1d', '( ( ppi ` g ) <_ %s <-> ( ( ppi ` g ) / %s ) <_ ( %s / %s ) )' % (Q6, P2, Q6, P2))], 'mpbid', '( ( ppi ` g ) / %s ) <_ ( %s / %s )' % (P2, Q6, P2))
    # ( Q6 / P2 ) = ( HALF / LG ) by cross multiplication
    ea = s([s([s([s([num.real(w, F116)], 'a1i', '%s e. RR' % F116), gr], 'remulcld', '( %s x. g ) e. RR' % F116)], 'recnd', '( %s x. g ) e. CC' % F116), s([lgrp], 'rpcnd', '%s e. CC' % LG), s([lgrp], 'rpne0d', '%s =/= 0' % LG)], 'divcan1d', '( %s x. %s ) = ( %s x. g )' % (Q6, LG, F116))
    eb = s([s([gr], 'recnd', 'g e. CC'), s([phrp], 'rpcnd', '( phi ` e ) e. CC'), s([phrp], 'rpne0d', '( phi ` e ) =/= 0')], 'divcan1d', '( %s x. ( phi ` e ) ) = g' % GP)
    poly = lin.lineq(w, C2, '( %s x. %s )' % (Q6, LG), '( %s x. %s )' % (HALF, P2), hyps=[ea, eb], leaves={Q6: q6r, LG: s([lgrp], 'rpred', '%s e. RR' % LG), GP: gpr, 'g': gr, '( phi ` e )': phr}, atoms=[Q6, GP, LG], products=True)
    dm = s([s([q6r], 'recnd', '%s e. CC' % Q6), s([p2rp], 'rpcnd', '%s e. CC' % P2), s([halfr], 'recnd', '%s e. CC' % HALF), s([lgrp], 'rpcnd', '%s e. CC' % LG), s([p2rp], 'rpne0d', '%s =/= 0' % P2), s([lgrp], 'rpne0d', '%s =/= 0' % LG)], 'divmuleqd', '( ( %s / %s ) = ( %s / %s ) <-> ( %s x. %s ) = ( %s x. %s ) )' % (Q6, P2, HALF, LG, Q6, LG, HALF, P2))
    ident = s([poly, dm], 'mpbird', '( %s / %s ) = ( %s / %s )' % (Q6, P2, HALF, LG))
    m5 = s([m4, ident], 'breqtrd', '( ( ppi ` g ) / %s ) <_ ( %s / %s )' % (P2, HALF, LG))
    cntr = s([mpi(w, finrab(w, RESCNT('g', 'e', 'q')[len('( # ` '):-2]), 'hashcl', '%s e. NN0' % RESCNT('g', 'e', 'q'))], 'a1i', '%s e. NN0' % RESCNT('g', 'e', 'q')); cntr = s([cntr], 'nn0red', '%s e. RR' % RESCNT('g', 'e', 'q'))
    fin = s([s([ppir, p2rp], 'rerpdivcld', '( ( ppi ` g ) / %s ) e. RR' % P2), s([halfr, lgrp], 'rerpdivcld', '( %s / %s ) e. RR' % (HALF, LG)), cntr, m5, pib], 'letrd', GOALL)
    i1 = w.s([fin], 'ex', '( %s -> ( %s -> %s ) )' % (C1, HYPL, GOALL))
    C1a = '( %s /\\ ( c e. NN0 /\\ g e. NN0 ) )' % A0
    i2 = w.s([w.s([i1], 'exp32', '( %s -> ( ( c e. NN0 /\\ g e. NN0 ) -> ( ( e e. NN /\\ q e. ZZ ) -> ( %s -> %s ) ) ) )' % (A0, HYPL, GOALL))], 'imp', '( %s -> ( ( e e. NN /\\ q e. ZZ ) -> ( %s -> %s ) ) )' % (C1a, HYPL, GOALL))
    i3 = w.s([i2], 'ralrimivv', '( %s -> A. e e. NN A. q e. ZZ ( %s -> %s ) )' % (C1a, HYPL, GOALL))
    i4 = w.s([i3], 'ex', '( %s -> ( ( c e. NN0 /\\ g e. NN0 ) -> A. e e. NN A. q e. ZZ ( %s -> %s ) ) )' % (A0, HYPL, GOALL))
    w.qed([i4], 'ralrimivv', S['bmlow'])
    return go(w)


def gen_pil():
    w = W('bmpil', 'The Chebyshev lower bound ` pi ( y ) >_ y / ( ( 11 / 10 ) log y ) ` from T2.1 at ` d = a = 1 ` (Lean ` piLower_of_density ` ): ` theta ( y ; 1 , 1 ) >_ ( 11 / 12 ) y ` , ~ lepiap and ~ piapleppi .')
    A0 = '( ( B e. RR /\\ %s ) /\\ %s /\\ %s )' % (FMAP('F'), GE2('F'), THETA('B', 'F'))
    u0 = unpack(w, A0)
    UPB = UP('B')
    C = '( ( %s /\\ y e. NN0 ) /\\ %s <_ y )' % (A0, UPB)
    s = S_(w, C)
    L = lambda st: lift(w, st, C)
    br, fmap, ge2, theta = L(u0['B e. RR']), L(u0[FMAP('F')]), L(u0[GE2('F')]), L(u0[THETA('B', 'F')])
    yn0 = L(w.s([], 'simpr', '( ( %s /\\ y e. NN0 ) -> y e. NN0 )' % A0))
    uy = s([], 'simpr', '%s <_ y' % UPB)
    yr = s([yn0], 'nn0red', 'y e. RR'); yc = s([yr], 'recnd', 'y e. CC'); yz = s([yn0], 'nn0zd', 'y e. ZZ')
    babs = s([s([br], 'recnd', 'B e. CC')], 'abscld', '( abs ` B ) e. RR')
    lv = {'B': br, '( abs ` B )': babs, 'y': yr}
    by = lin.linarith(w, C, [uy, s([br], 'leabsd', 'B <_ ( abs ` B )')], 'B <_ y', leaves=lv, fast=False)
    y2 = lin.linarith(w, C, [uy, s([s([br], 'recnd', 'B e. CC')], 'absge0d', '0 <_ ( abs ` B )')], '2 <_ y', leaves=lv, fast=False)
    y1 = lin.linarith(w, C, [y2], '1 <_ y', leaves={'y': yr}); y1lt = lin.linarith(w, C, [y2], '1 < y', leaves={'y': yr})
    yge0 = s([yn0], 'nn0ge0d', '0 <_ y')
    # A. i e. ( F ` y ) -. i || 1 under the i-free antecedent ( FMAP /\ y e. NN0 )
    X = '( %s /\\ y e. NN0 )' % FMAP('F')
    XI = '( ( %s /\\ i e. ( F ` y ) ) /\\ 2 <_ i )' % X
    sx = S_(w, XI)
    fy = w.s([w.s([], 'simpl', '( %s -> %s )' % (X, FMAP('F'))), w.s([], 'simpr', '( %s -> y e. NN0 )' % X)], 'ffvelcdmd', '( %s -> ( F ` y ) e. ( ~P NN i^i Fin ) )' % X)
    fyss = w.s([w.s([fy, w.inst('elinel1')], 'syl', '( %s -> ( F ` y ) e. ~P NN )' % X), w.inst('elpwi')], 'syl', '( %s -> ( F ` y ) C_ NN )' % X)
    iin = sx([lift(w, fyss, XI), lift(w, w.s([], 'simpr', '( ( %s /\\ i e. ( F ` y ) ) -> i e. ( F ` y ) )' % X), XI)], 'sseldd', 'i e. NN')
    in0 = sx([iin], 'nnnn0d', 'i e. NN0')
    i2 = sx([], 'simpr', '2 <_ i')
    d1 = sx([in0, w.inst('dvds1')], 'syl', '( i || 1 <-> i = 1 )')
    XI2 = '( %s /\\ i = 1 )' % XI
    bq = w.s([], 'breq2', '( i = 1 -> ( 2 <_ i <-> 2 <_ 1 ) )')
    bq2 = w.s([bq], 'biimpa', '( ( i = 1 /\\ 2 <_ i ) -> 2 <_ 1 )')
    c21 = w.s([w.s([], 'simpr', '( %s -> i = 1 )' % XI2), lift(w, i2, XI2), bq2], 'syl2anc', '( %s -> 2 <_ 1 )' % XI2)
    n21 = w.s([w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '1re', '1 e. RR'), w.s([], '2re', '2 e. RR'), w.inst('ltnle')], 'mp2an', '( 1 < 2 <-> -. 2 <_ 1 )')], 'mpbi', '-. 2 <_ 1')], 'a1i', '( %s -> -. 2 <_ 1 )' % XI2)
    ni1 = w.s([c21, n21], 'pm2.65da', '( %s -> -. i = 1 )' % XI)
    nd = sx([ni1, sx([d1], 'biimpd', '( i || 1 -> i = 1 )')], 'mtod', '-. i || 1')
    itr = w.s([w.s([nd], 'ex', '( ( %s /\\ i e. ( F ` y ) ) -> ( 2 <_ i -> -. i || 1 ) )' % X)], 'ralimdva', '( %s -> ( A. i e. ( F ` y ) 2 <_ i -> A. i e. ( F ` y ) -. i || 1 ) )' % X)
    cgn, ge2y = wc(w, 'A. i e. ( F ` n ) 2 <_ i', 'n', 'y')
    g2y = s([cgn, ge2, yn0], 'rspcdva', ge2y)
    bad = s([g2y, s([s([fmap, yn0], 'jca', X), itr], 'syl', '( A. i e. ( F ` y ) 2 <_ i -> A. i e. ( F ` y ) -. i || 1 )')], 'mpd', 'A. i e. ( F ` y ) -. i || 1')
    # T2.1 at ( y , 1 , 1 , y )
    TB = THETA('B', 'F')[len('A. n e. NN0 A. d e. NN A. a e. ZZ A. z e. RR '):]
    t1, b1 = wc(w, TB, 'n', 'y'); t2, b2 = wc(w, b1, 'd', '1'); t3, b3 = wc(w, b2, 'a', '1'); t4, b4 = wc(w, b3, 'z', 'y')
    TH = '( 1 ( thetaAP ` 1 ) y )'; GP = '( y / ( phi ` 1 ) )'; BND = '( ( %s x. y ) / ( phi ` 1 ) )' % F112
    TANTE = '( ( B <_ y /\\ ( 1 gcd 1 ) = 1 ) /\\ ( 1 <_ ( y ^c %s ) /\\ ( 1 x. ( y ^c %s ) ) <_ y /\\ y <_ y ) /\\ A. i e. ( F ` y ) -. i || 1 )' % (F191, F709)
    TINST = '( %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (TANTE, TH, GP, BND)
    assert b4 == TINST, (b4[:300], TINST[:300])
    one_nn = s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'); one_z = s([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ')
    r4 = w.s([t1, t2, t3, t4], 'rspc4v', '( ( ( y e. NN0 /\\ 1 e. NN ) /\\ ( 1 e. ZZ /\\ y e. RR ) ) -> ( %s -> %s ) )' % (THETA('B', 'F'), TINST))
    mem = s([s([yn0, one_nn], 'jca', '( y e. NN0 /\\ 1 e. NN )'), s([one_z, yr], 'jca', '( 1 e. ZZ /\\ y e. RR )')], 'jca', '( ( y e. NN0 /\\ 1 e. NN ) /\\ ( 1 e. ZZ /\\ y e. RR ) )')
    tinst = s([theta, s([mem, r4], 'syl', '( %s -> %s )' % (THETA('B', 'F'), TINST))], 'mpd', TINST)
    g11 = s([one_z, w.inst('1gcd')], 'syl', '( 1 gcd 1 ) = 1')
    a191 = s([s([yc], 'cxp0d', '( y ^c 0 ) = 1'), s([yr, y1, s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([num.real(w, F191)], 'a1i', '%s e. RR' % F191), s([num.fact(w, F191, 'ge0')], 'a1i', '0 <_ %s' % F191)], 'cxplead', '( y ^c 0 ) <_ ( y ^c %s )' % F191)], 'eqbrtrrd', '1 <_ ( y ^c %s )' % F191)
    y709r = s([yr, yge0, s([num.real(w, F709)], 'a1i', '%s e. RR' % F709)], 'recxpcld', '( y ^c %s ) e. RR' % F709)
    a709 = s([s([s([y709r], 'recnd', '( y ^c %s ) e. CC' % F709)], 'mullidd', '( 1 x. ( y ^c %s ) ) = ( y ^c %s )' % (F709, F709)), s([s([yr, y1, s([num.real(w, F709)], 'a1i', '%s e. RR' % F709), s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), s([num.le_lit(w, F709, '1')], 'a1i', '%s <_ 1' % F709)], 'cxplead', '( y ^c %s ) <_ ( y ^c 1 )' % F709), s([yc], 'cxp1d', '( y ^c 1 ) = y')], 'breqtrd', '( y ^c %s ) <_ y' % F709)], 'eqbrtrd', '( 1 x. ( y ^c %s ) ) <_ y' % F709)
    tante = s([s([by, g11], 'jca', '( B <_ y /\\ ( 1 gcd 1 ) = 1 )'), s([a191, a709, s([yr], 'leidd', 'y <_ y')], '3jca', '( 1 <_ ( y ^c %s ) /\\ ( 1 x. ( y ^c %s ) ) <_ y /\\ y <_ y )' % (F191, F709)), bad], '3jca', TANTE)
    tabs = s([tante, tinst], 'mpd', '( abs ` ( %s - %s ) ) <_ %s' % (TH, GP, BND))
    thr = s([one_nn, one_z, yr, w.inst('thetaapcl')], 'syl3anc', '%s e. RR' % TH)
    ph1 = s([w.s([], 'phi1', '( phi ` 1 ) = 1')], 'a1i', '( phi ` 1 ) = 1')
    gpe = s([s([ph1], 'oveq2d', '%s = ( y / 1 )' % GP), s([yc], 'div1d', '( y / 1 ) = y')], 'eqtrd', '%s = y' % GP)
    bnde = s([s([ph1], 'oveq2d', '%s = ( ( %s x. y ) / 1 )' % (BND, F112)), s([s([s([num.cc(w, F112)], 'a1i', '%s e. CC' % F112), yc], 'mulcld', '( %s x. y ) e. CC' % F112)], 'div1d', '( ( %s x. y ) / 1 ) = ( %s x. y )' % (F112, F112))], 'eqtrd', '%s = ( %s x. y )' % (BND, F112))
    gpr = s([gpe, yr], 'eqeltrd', '%s e. RR' % GP); bndr = s([bnde, s([s([num.real(w, F112)], 'a1i', '%s e. RR' % F112), yr], 'remulcld', '( %s x. y ) e. RR' % F112)], 'eqeltrd', '%s e. RR' % BND)
    absl = s([tabs, s([s([thr, gpr], 'resubcld', '( %s - %s ) e. RR' % (TH, GP)), bndr], 'absled', '( ( abs ` ( %s - %s ) ) <_ %s <-> ( -u %s <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s ) )' % (TH, GP, BND, BND, TH, GP, TH, GP, BND))], 'mpbid', '( -u %s <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s )' % (BND, TH, GP, TH, GP, BND))
    lo = s([absl], 'simpld', '-u %s <_ ( %s - %s )' % (BND, TH, GP))
    F1112 = '( ; 1 1 / ; 1 2 )'
    thlow = lin.linarith(w, C, [lo, gpe, bnde], '( %s x. y ) <_ %s' % (F1112, TH), leaves={TH: thr, GP: gpr, BND: bndr, 'y': yr}, atoms=[TH, GP, BND], fast=False)
    HALF = '( %s x. y )' % F1112
    halfr = s([s([num.real(w, F1112)], 'a1i', '%s e. RR' % F1112), yr], 'remulcld', '%s e. RR' % HALF)
    LG = '( log ` y )'
    pia = s([s([s([one_nn, one_z], 'jca', '( 1 e. NN /\\ 1 e. ZZ )'), s([yr, y1lt], 'jca', '( y e. RR /\\ 1 < y )'), s([halfr, thlow], 'jca', '( %s e. RR /\\ %s <_ %s )' % (HALF, HALF, TH))], '3jca', '( ( 1 e. NN /\\ 1 e. ZZ ) /\\ ( y e. RR /\\ 1 < y ) /\\ ( %s e. RR /\\ %s <_ %s ) )' % (HALF, HALF, TH)), w.inst('lepiap')], 'syl', '( %s / %s ) <_ ( 1 ( piAP ` 1 ) y )' % (HALF, LG))
    ple = s([one_nn, one_z, yr, w.inst('piapleppi')], 'syl3anc', '( 1 ( piAP ` 1 ) y ) <_ ( ppi ` y )')
    lgrp = s([yr, y1lt], 'rplogcld', '%s e. RR+' % LG)
    # y / ( ( 11 / 10 ) LG ) = ( ( 10 / 11 ) y ) / LG <_ HALF / LG
    F1011 = '( ; 1 0 / ; 1 1 )'
    B1 = '( %s x. %s )' % (F1110, LG)
    b1rp = s([s([num.rp(w, F1110)], 'a1i', '%s e. RR+' % F1110), lgrp], 'rpmulcld', '%s e. RR+' % B1)
    TY = '( %s x. y )' % F1011
    tyr = s([s([num.real(w, F1011)], 'a1i', '%s e. RR' % F1011), yr], 'remulcld', '%s e. RR' % TY)
    poly = lin.lineq(w, C, '( y x. %s )' % LG, '( %s x. %s )' % (TY, B1), leaves={'y': yr, LG: s([lgrp], 'rpred', '%s e. RR' % LG)}, products=True)
    dm = s([yc, s([b1rp], 'rpcnd', '%s e. CC' % B1), s([tyr], 'recnd', '%s e. CC' % TY), s([lgrp], 'rpcnd', '%s e. CC' % LG), s([b1rp], 'rpne0d', '%s =/= 0' % B1), s([lgrp], 'rpne0d', '%s =/= 0' % LG)], 'divmuleqd', '( ( y / %s ) = ( %s / %s ) <-> ( y x. %s ) = ( %s x. %s ) )' % (B1, TY, LG, LG, TY, B1))
    ident = s([poly, dm], 'mpbird', '( y / %s ) = ( %s / %s )' % (B1, TY, LG))
    tyle = lin.linarith(w, C, [yge0], '%s <_ %s' % (TY, HALF), leaves={'y': yr})
    q1 = s([tyle, s([tyr, halfr, lgrp], 'lediv1d', '( %s <_ %s <-> ( %s / %s ) <_ ( %s / %s ) )' % (TY, HALF, TY, LG, HALF, LG))], 'mpbid', '( %s / %s ) <_ ( %s / %s )' % (TY, LG, HALF, LG))
    q2 = s([ident, q1], 'eqbrtrd', '( y / %s ) <_ ( %s / %s )' % (B1, HALF, LG))
    pir = s([one_nn, one_z, yr, w.inst('piapcl')], 'syl3anc', '( 1 ( piAP ` 1 ) y ) e. NN0'); pir = s([pir], 'nn0red', '( 1 ( piAP ` 1 ) y ) e. RR')
    ppir = s([s([yr, w.inst('ppicl')], 'syl', '( ppi ` y ) e. NN0')], 'nn0red', '( ppi ` y ) e. RR')
    hlr = s([halfr, lgrp], 'rerpdivcld', '( %s / %s ) e. RR' % (HALF, LG))
    ylr = s([yr, b1rp], 'rerpdivcld', '( y / %s ) e. RR' % B1)
    q3 = s([ylr, hlr, pir, q2, pia], 'letrd', '( y / %s ) <_ ( 1 ( piAP ` 1 ) y )' % B1)
    fin = s([ylr, pir, ppir, q3, ple], 'letrd', '( y / %s ) <_ ( ppi ` y )' % B1)
    i1 = w.s([fin], 'ex', '( ( %s /\\ y e. NN0 ) -> ( %s <_ y -> ( y / %s ) <_ ( ppi ` y ) ) )' % (A0, UPB, B1))
    w.qed([i1], 'ralrimiva', S['bmpil'])
    return go(w)


ALL = {'bmlow': gen_low, 'bmpil': gen_pil}



def gen_21b():
    w = W('bmpig21b', 'AGP Theorem 3.1 at ` B = 21 / 100 ` at the witnesses of T2.1 (` j , b , f ` : the exceptional count, threshold and sets at ` 1 / 12 ` ), of Chebyshev (` s ` ) and of Brun-Titchmarsh (` t ` ) (Lean ` bMembership21 ` and ` pigeonhole_21 ` ): ~ bmlow and ~ bmpil supply the ` B ` -membership lower bound and the ` pi ` lower bound to ~ bmpig .')
    A0, concl = split_imp(S['bmpig21b'])
    u = unpack(w, A0)
    s = S_(w, A0)
    jn0, br, fmap, card, ge2, theta = u['j e. NN0'], u['b e. RR'], u[FMAP('f')], u[CARD('f', 'j')], u[GE2('f')], u[THETA('b', 'f')]
    sn, ppib, tn0, bt = u['s e. NN'], u[PPIB('s')], u['t e. NN0'], u[BTBODY('t')]
    low = ap(w, A0, [br, fmap, theta, sn, ppib], 'bmlow', LOWER(BP('b', 's'), 'f'), sub={'B': 'b', 'F': 'f', 'S': 's'})
    pil = ap(w, A0, [br, fmap, ge2, theta], 'bmpil', PIB(UP('b')), sub={'B': 'b', 'F': 'f'})
    babs = s([s([br], 'recnd', 'b e. CC')], 'abscld', '( abs ` b ) e. RR')
    s1r = s([s([sn], 'peano2nnd', '( s + 1 ) e. NN')], 'nnred', '( s + 1 ) e. RR')
    bpr = s([babs, s([s([s1r], 'resqcld', '( ( s + 1 ) ^ 2 ) e. RR'), s([num.real(w, '2')], 'a1i', '2 e. RR')], 'readdcld', '( ( ( s + 1 ) ^ 2 ) + 2 ) e. RR')], 'readdcld', '%s e. RR' % BP('b', 's'))
    upr = s([babs, s([num.real(w, '2')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % UP('b'))
    tr = s([tn0], 'nn0red', 't e. RR')
    w.qed([jn0, bpr, fmap, card, ge2, low, tr, bt, upr, pil], 'bmpig', S['bmpig21b'])
    return go(w)


def gen_21a():
    w = W('bmpig21a', 'AGP Theorem 3.1 at ` B = 21 / 100 ` (Lean ` pigeonhole_21 ` ), conditional on the two zone-density inputs ` DensityInputs = LogFreeDensity /\\ LoggedDensity ` : T2.1 (~ t21thm ) at ` 1 / 12 ` , Chebyshev (~ ppiubeps at ` 1 / 10 ` ) and Brun-Titchmarsh (~ bruntitex ) supply the witnesses of ~ bmpig21b .')
    LFLG = '( %s /\\ %s )' % (LOGFREE, LOGGED)
    T21 = tsub(stmt('t21thm'), {'E': F112})
    ta, tc = split_imp(T21)
    EH = '( %s e. RR /\\ 0 < %s /\\ %s < ( 1 / 3 ) )' % (F112, F112, F112)
    assert ta == '( %s /\\ %s )' % (LFLG, EH), ta[-200:]
    t21 = w.s([], 't21thm', T21)
    eh = w.s([num.real(w, F112), num.fact(w, F112, 'gt0'), num.le_lit(w, F112, '( 1 / 3 )', strict=True)], '3pm3.2i', EH)
    t21a = w.s([eh, t21], 'mpan2', '( %s -> %s )' % (LFLG, tc))
    # rename the x-letter l -> n in the three quantified conjuncts
    assert tc.startswith('E. j e. NN0 E. b e. RR E. f ')
    BL = tc[len('E. j e. NN0 E. b e. RR E. f '):]
    BN = BODY1('j', 'b', 'f')
    CARDl = CARD('f', 'j').replace('n', 'l'); GE2l = GE2('f').replace('A. n e. NN0 A. i e. ( f ` n )', 'A. l e. NN0 A. i e. ( f ` l )')
    THl = THETA('b', 'f', F112, 'l')
    assert BL == '( %s /\\ ( %s /\\ %s ) /\\ %s )' % (FMAP('f'), CARDl, GE2l, THl), (BL[:300],)
    c1, _ = wc(w, '( # ` ( f ` l ) ) <_ j', 'l', 'n')
    b1 = w.s([c1], 'cbvralvw', '( %s <-> %s )' % (CARDl, CARD('f', 'j')))
    c2, _ = wc(w, 'A. i e. ( f ` l ) 2 <_ i', 'l', 'n')
    b2 = w.s([c2], 'cbvralvw', '( %s <-> %s )' % (GE2l, GE2('f')))
    c3, _ = wc(w, THl[len('A. l e. NN0 '):], 'l', 'n')
    b3 = w.s([c3], 'cbvralvw', '( %s <-> %s )' % (THl, THETA('b', 'f')))
    b12 = w.s([b1, b2], 'anbi12i', '( ( %s /\\ %s ) <-> ( %s /\\ %s ) )' % (CARDl, GE2l, CARD('f', 'j'), GE2('f')))
    b0 = w.s([], 'biid', '( %s <-> %s )' % (FMAP('f'), FMAP('f')))
    bb = w.s([b0, b12, b3], '3anbi123i', '( %s <-> %s )' % (BL, BN))
    bex = w.s([w.s([w.s([bb], 'exbii', '( E. f %s <-> E. f %s )' % (BL, BN))], 'rexbii', '( E. b e. RR E. f %s <-> E. b e. RR E. f %s )' % (BL, BN))], 'rexbii', '( %s <-> E. j e. NN0 E. b e. RR E. f %s )' % (tc, BN))
    t21n = w.s([t21a, bex], 'sylib', '( %s -> E. j e. NN0 E. b e. RR E. f %s )' % (LFLG, BN))
    # the eliminations
    P1 = '( ( j e. NN0 /\\ b e. RR ) /\\ %s )' % BN; P2 = '( s e. NN /\\ %s )' % PPIB('s'); P3 = '( t e. NN0 /\\ %s )' % BTBODY('t')
    PIG_ = PIG(F793200)
    e0 = w.s([], 'bmpig21b', S['bmpig21b'])
    e1 = w.s([e0], '3exp', '( %s -> ( %s -> ( %s -> %s ) ) )' % (P1, P2, P3, PIG_))
    e2 = w.s([e1], 'imp', '( ( %s /\\ %s ) -> ( %s -> %s ) )' % (P1, P2, P3, PIG_))
    e3 = w.s([e2], 'expd', '( ( %s /\\ %s ) -> ( t e. NN0 -> ( %s -> %s ) ) )' % (P1, P2, BTBODY('t'), PIG_))
    R1 = '( E. t e. NN0 %s -> %s )' % (BTBODY('t'), PIG_)
    e4 = w.s([e3], 'rexlimdv', '( ( %s /\\ %s ) -> %s )' % (P1, P2, R1))
    e5 = w.s([e4], 'ex', '( %s -> ( %s -> %s ) )' % (P1, P2, R1))
    e6 = w.s([e5], 'expd', '( %s -> ( s e. NN -> ( %s -> %s ) ) )' % (P1, PPIB('s'), R1))
    R = '( E. s e. NN %s -> %s )' % (PPIB('s'), R1)
    e7 = w.s([e6], 'rexlimdv', '( %s -> %s )' % (P1, R))
    e8 = w.s([e7], 'ex', '( ( j e. NN0 /\\ b e. RR ) -> ( %s -> %s ) )' % (BN, R))
    e9 = w.s([e8], 'exlimdv', '( ( j e. NN0 /\\ b e. RR ) -> ( E. f %s -> %s ) )' % (BN, R))
    e10 = w.s([e9], 'ex', '( j e. NN0 -> ( b e. RR -> ( E. f %s -> %s ) ) )' % (BN, R))
    e11 = w.s([e10], 'rexlimdv', '( j e. NN0 -> ( E. b e. RR E. f %s -> %s ) )' % (BN, R))
    e12 = w.s([e11], 'rexlimiv', '( E. j e. NN0 E. b e. RR E. f %s -> %s )' % (BN, R))
    main = w.s([t21n, e12], 'syl', '( %s -> %s )' % (LFLG, R))
    # Chebyshev at 1 / 10 with the letters s , y
    PP = tsub(stmt('ppiubeps'), {'E': F110})
    pa, pc = split_imp(PP)
    pp1 = w.s([num.rp(w, F110), w.s([], 'ppiubeps', PP)], 'ax-mp', pc)
    INNER_m = lambda zz: '( ppi ` %s ) <_ ( ( ( ( log ` 4 ) + %s ) x. %s ) / ( log ` %s ) )' % (zz, F110, zz, zz)
    assert pc == 'E. m e. NN A. z e. ( ZZ>= ` m ) %s' % INNER_m('z'), pc
    cz, _ = wc(w, INNER_m('z'), 'z', 'y')
    r1 = w.s([cz], 'cbvralvw', '( A. z e. ( ZZ>= ` m ) %s <-> A. y e. ( ZZ>= ` m ) %s )' % (INNER_m('z'), INNER_m('y')))
    r2 = w.s([r1], 'rexbii', '( %s <-> E. m e. NN A. y e. ( ZZ>= ` m ) %s )' % (pc, INNER_m('y')))
    cm, ppb = wc(w, 'A. y e. ( ZZ>= ` m ) %s' % INNER_m('y'), 'm', 's')
    assert ppb == PPIB('s'), ppb
    r3 = w.s([cm], 'cbvrexvw', '( E. m e. NN A. y e. ( ZZ>= ` m ) %s <-> E. s e. NN %s )' % (INNER_m('y'), PPIB('s')))
    pp2 = w.s([pp1, w.s([r2, r3], 'bitri', '( %s <-> E. s e. NN %s )' % (pc, PPIB('s')))], 'mpbi', 'E. s e. NN %s' % PPIB('s'))
    m1 = w.s([pp2, main], 'mpi', '( %s -> %s )' % (LFLG, R1))
    bte = w.s([], 'bruntitex', stmt('bruntitex'))
    assert stmt('bruntitex') == 'E. t e. NN0 %s' % BTBODY('t')
    w.qed([bte, m1], 'mpi', S['bmpig21a'])
    return go(w)


def gen_21():
    w = W('bmpig21', "AGP Theorem 3.1 at ` B = 21 / 100 ` with the sum bound ` 3 / 160 ` of ~ carmsw (Lean ` pigeonhole_21' ` ): ~ bmpig21a and ` 3 / 160 <_ 79 / 3200 ` inside the matrix.  The matrix is that of carmsw.3 verbatim (` D := a ` , ` F := r ` ); F2 discharges carmsw.1-.3 from it.")
    LFLG = '( %s /\\ %s )' % (LOGFREE, LOGGED)
    A3 = ANTE('r', 'x', 'l', F3160); A79 = ANTE('r', 'x', 'l', F793200); CN = CONS('a', 'x', 'l')
    PFq = '{ p e. Prime | p || l }'
    SUMQ = 'sum_ q e. %s ( 1 / q )' % PFq
    # ( l e. NN -> SUMQ e. RR ), closed
    LN = 'l e. NN'
    pff = w.s([w.s([], 'id', '( %s -> %s )' % (LN, LN)), w.inst('prmdvdsfi')], 'syl', '( %s -> %s e. Fin )' % (LN, PFq))
    LQ = '( %s /\\ q e. %s )' % (LN, PFq)
    qp = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (LQ, PFq)), w.inst('elrabi')], 'syl', '( %s -> q e. Prime )' % LQ)
    qrp = w.s([w.s([qp, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % LQ)], 'nnrpd', '( %s -> q e. RR+ )' % LQ)
    iqr = w.s([qrp], 'rprecred', '( %s -> ( 1 / q ) e. RR )' % LQ)
    sumr = w.s([pff, iqr], 'fsumrecl', '( %s -> %s e. RR )' % (LN, SUMQ))
    C = '( l e. NN0 /\\ %s )' % A3
    s = S_(w, C)
    ln0 = s([], 'simpl', 'l e. NN0')
    an = s([], 'simpr', A3)
    au = unpack_step(w, C, an, A3)
    HQ = 'A. q e. Prime ( q || l -> q <_ %s )' % XH('x')
    rlt, l1, lsf, hq, hs = au['r < x'], au['1 < l'], au['( mmu ` l ) =/= 0'], au[HQ], au['%s <_ %s' % (SUMQ, F3160)]
    lnn = s([s([s([ln0], 'nn0zd', 'l e. ZZ'), lin.linarith(w, C, [l1], '0 < l', leaves={'l': s([ln0], 'nn0red', 'l e. RR')})], 'jca', '( l e. ZZ /\\ 0 < l )'), w.s([], 'elnnz', '( l e. NN <-> ( l e. ZZ /\\ 0 < l ) )')], 'sylibr', 'l e. NN')
    sr = s([lnn, sumr], 'syl', '%s e. RR' % SUMQ)
    hs79 = s([sr, s([num.real(w, F3160)], 'a1i', '%s e. RR' % F3160), s([num.real(w, F793200)], 'a1i', '%s e. RR' % F793200), hs, s([num.le_lit(w, F3160, F793200)], 'a1i', '%s <_ %s' % (F3160, F793200))], 'letrd', '%s <_ %s' % (SUMQ, F793200))
    a79 = s([s([rlt, l1, lsf], '3jca', '( r < x /\\ 1 < l /\\ ( mmu ` l ) =/= 0 )'), s([hq, hs79], 'jca', '( %s /\\ %s <_ %s )' % (HQ, SUMQ, F793200))], 'jca', A79)
    i1 = w.s([a79], 'ex', '( l e. NN0 -> ( %s -> %s ) )' % (A3, A79))
    i2 = w.s([i1], 'imim1d', '( l e. NN0 -> ( ( %s -> %s ) -> ( %s -> %s ) ) )' % (A79, CN, A3, CN))
    i3 = w.s([i2], 'adantl', '( ( x e. NN0 /\\ l e. NN0 ) -> ( ( %s -> %s ) -> ( %s -> %s ) ) )' % (A79, CN, A3, CN))
    i4 = w.s([i3], 'ralimdva', '( x e. NN0 -> ( A. l e. NN0 ( %s -> %s ) -> A. l e. NN0 ( %s -> %s ) ) )' % (A79, CN, A3, CN))
    M79 = MATRIX('a', 'r', F793200); M3 = MATRIX('a', 'r', F3160)
    i5 = w.s([i4], 'ralimia', '( %s -> %s )' % (M79, M3))
    i6 = w.s([i5], 'reximi', '( E. r e. NN0 %s -> E. r e. NN0 %s )' % (M79, M3))
    i7 = w.s([i6], 'reximi', '( %s -> %s )' % (PIG(F793200), PIG(F3160)))
    w.qed([w.s([], 'bmpig21a', S['bmpig21a']), i7], 'syl', S['bmpig21'])
    return go(w)


ALL.update({'bmpig21b': gen_21b, 'bmpig21a': gen_21a, 'bmpig21': gen_21})

if __name__ == '__main__':
    for n in (only or list(ALL)):
        ALL[n]()
