"""Sortie Z6a (agent z6ae), section 2 small lemmas: one_le_P1, sum_inv_mul_cube_le (DetectionShift.lean section 2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6alib import *
from cl import Closure, lift, split_imp
import lin
import num

RS = '( N RSet R )'
A0 = '( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) )'


def rsetctx(w, a):
    """common steps under A0: nn, rr, r1, fin, sub"""
    st = mkst(w, a)
    nn = st([], 'simpl', 'N e. NN')
    rr = st([], 'simprl', 'R e. RR')
    r1 = st([], 'simprr', '1 <_ R')
    fs = st([nn, rr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RS, RS))
    sub = st([fs], 'simpld', '%s C_ ( 1 ... ( |_ ` R ) )' % RS)
    fin = st([fs], 'simprd', '%s e. Fin' % RS)
    return st, nn, rr, r1, sub, fin


def body_nn(w, a, sub):
    """( ( a /\\ r e. RS ) -> r e. NN ) and r <_ |_ R"""
    b = '( %s /\\ r e. %s )' % (a, RS)
    sb = w.s([sub], 'adantr', '( %s -> %s C_ ( 1 ... ( |_ ` R ) ) )' % (b, RS))
    rin = w.s([], 'simpr', '( %s -> r e. %s )' % (b, RS))
    rfz = w.s([sb, rin], 'sseldd', '( %s -> r e. ( 1 ... ( |_ ` R ) ) )' % b)
    rnn = w.s([rfz, w.inst('elfznn')], 'syl', '( %s -> r e. NN )' % b)
    rle = w.s([rfz, w.inst('elfzle2')], 'syl', '( %s -> r <_ ( |_ ` R ) )' % b)
    return b, rnn, rle


def z6p1ge1():
    w = W('z6p1ge1', 'Lean one_le_P1: 1 <_ P1 ( N , R ) = sum over ( N RSet R ) of 1 / r, by the term r = 1.')
    a = ante('z6p1ge1')
    st, nn, rr, r1, sub, fin = rsetctx(w, a)
    b, rnn, rle = body_nn(w, a, sub)
    rre = w.s([rnn, w.inst('nnrecre')], 'syl', '( %s -> ( 1 / r ) e. RR )' % b)
    rgt = w.s([rnn, w.inst('nnrecgt0')], 'syl', '( %s -> 0 < ( 1 / r ) )' % b)
    rge = w.s([rre, rgt], 'ltled', '( %s -> 0 <_ ( 1 / r ) )' % b)
    fl = st([rr, r1, w.inst('flge1nn')], 'syl2anc', '( |_ ` R ) e. NN')
    fl1 = st([fl, w.inst('nnge1')], 'syl', '1 <_ ( |_ ` R )')
    one = st([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    j3 = st([one, fl, fl1], '3jca', '( 1 e. NN /\\ ( |_ ` R ) e. NN /\\ 1 <_ ( |_ ` R ) )')
    eb = st([w.s([], 'elfz1b', '( 1 e. ( 1 ... ( |_ ` R ) ) <-> ( 1 e. NN /\\ ( |_ ` R ) e. NN /\\ 1 <_ ( |_ ` R ) ) )')], 'a1i',
            '( 1 e. ( 1 ... ( |_ ` R ) ) <-> ( 1 e. NN /\\ ( |_ ` R ) e. NN /\\ 1 <_ ( |_ ` R ) ) )')
    e1 = st([j3, eb], 'mpbird', '1 e. ( 1 ... ( |_ ` R ) )')
    mu = st([w.s([], 'sqf1', '( mmu ` 1 ) =/= 0')], 'a1i', '( mmu ` 1 ) =/= 0')
    gc = st([st([nn], 'nnzd', 'N e. ZZ'), w.inst('1gcd')], 'syl', '( 1 gcd N ) = 1')
    cond = '( 1 e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` 1 ) =/= 0 /\\ ( 1 gcd N ) = 1 ) )'
    cj = st([e1, st([mu, gc], 'jca', '( ( mmu ` 1 ) =/= 0 /\\ ( 1 gcd N ) = 1 )')], 'jca', cond)
    el = st([nn, rr, w.inst('z5elrset')], 'syl2anc', '( 1 e. %s <-> %s )' % (RS, cond))
    m1 = st([cj, el], 'mpbird', '1 e. %s' % RS)
    eqk = w.s([], 'oveq2', '( r = 1 -> ( 1 / r ) = ( 1 / 1 ) )')
    ge = st([fin, rre, rge, eqk, m1], 'fsumge1', '( 1 / 1 ) <_ sum_ r e. %s ( 1 / r )' % RS)
    w.qed([w.s([], '1div1e1', '( 1 / 1 ) = 1'), ge], 'eqbrtrrid', STATEMENTS['z6p1ge1'])
    return w


def z6cube():
    w = W('z6cube', 'Lean sum_inv_mul_cube_le: sum over ( N RSet R ) of ( 1 / r ) r ^ 3 <_ R ^ 3 (each term is r ^ 2 <_ R ^ 2, at most |_ R <_ R terms).')
    a = ante('z6cube')
    st, nn, rr, r1, sub, fin = rsetctx(w, a)
    b, rnn, rle = body_nn(w, a, sub)
    sb = mkst(w, b)
    rc = sb([rnn], 'nncnd', 'r e. CC')
    rre = sb([rnn], 'nnred', 'r e. RR')
    rne = sb([rnn], 'nnne0d', 'r =/= 0')
    x1 = sb([rc, sb([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0'), w.inst('expp1')], 'syl2anc', '( r ^ ( 2 + 1 ) ) = ( ( r ^ 2 ) x. r )')
    x2 = w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq2i', '( r ^ ( 2 + 1 ) ) = ( r ^ 3 )')
    x3 = sb([x2, x1], 'eqtr3id', '( r ^ 3 ) = ( ( r ^ 2 ) x. r )')
    e2 = sb([x3], 'oveq2d', '( ( 1 / r ) x. ( r ^ 3 ) ) = ( ( 1 / r ) x. ( ( r ^ 2 ) x. r ) )')
    rinv = sb([rc, rne], 'reccld', '( 1 / r ) e. CC')
    r2 = sb([rc, sb([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'expcld', '( r ^ 2 ) e. CC')
    e3 = sb([rinv, r2, rc], 'mul12d', '( ( 1 / r ) x. ( ( r ^ 2 ) x. r ) ) = ( ( r ^ 2 ) x. ( ( 1 / r ) x. r ) )')
    e4 = sb([rc, rne, w.inst('recid2')], 'syl2anc', '( ( 1 / r ) x. r ) = 1')
    e5 = sb([e4], 'oveq2d', '( ( r ^ 2 ) x. ( ( 1 / r ) x. r ) ) = ( ( r ^ 2 ) x. 1 )')
    e6 = sb([r2], 'mulridd', '( ( r ^ 2 ) x. 1 ) = ( r ^ 2 )')
    q = sb([sb([sb([e2, e3], 'eqtrd', '( ( 1 / r ) x. ( r ^ 3 ) ) = ( ( r ^ 2 ) x. ( ( 1 / r ) x. r ) )'), e5], 'eqtrd',
               '( ( 1 / r ) x. ( r ^ 3 ) ) = ( ( r ^ 2 ) x. 1 )'), e6], 'eqtrd', '( ( 1 / r ) x. ( r ^ 3 ) ) = ( r ^ 2 )')
    rrb = w.s([rr], 'adantr', '( %s -> R e. RR )' % b)
    flb = sb([rrb, w.inst('flle')], 'syl', '( |_ ` R ) <_ R')
    rleR = sb([rre, sb([rrb, w.inst('reflcl')], 'syl', '( |_ ` R ) e. RR'), rrb, rle, flb], 'letrd', 'r <_ R')
    r0 = sb([rnn], 'nnnn0d', 'r e. NN0')
    rge0 = sb([r0], 'nn0ge0d', '0 <_ r')
    sq = sb([sb([rre, rge0], 'jca', '( r e. RR /\\ 0 <_ r )'), sb([rrb, rleR], 'jca', '( R e. RR /\\ r <_ R )'), w.inst('le2sq2')], 'syl2anc',
            '( r ^ 2 ) <_ ( R ^ 2 )')
    tle = sb([q, sq], 'eqbrtrd', '( ( 1 / r ) x. ( r ^ 3 ) ) <_ ( R ^ 2 )')
    rinvr = sb([rnn, w.inst('nnrecre')], 'syl', '( 1 / r ) e. RR')
    r3 = sb([rinvr, sb([rre, sb([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'reexpcld', '( r ^ 3 ) e. RR')], 'remulcld',
            '( ( 1 / r ) x. ( r ^ 3 ) ) e. RR')
    R2 = st([rr], 'resqcld', '( R ^ 2 ) e. RR')
    R2b = w.s([R2], 'adantr', '( %s -> ( R ^ 2 ) e. RR )' % b)
    s1 = st([fin, r3, R2b, tle], 'fsumle', 'sum_ r e. %s ( ( 1 / r ) x. ( r ^ 3 ) ) <_ sum_ r e. %s ( R ^ 2 )' % (RS, RS))
    s2 = st([fin, st([R2], 'recnd', '( R ^ 2 ) e. CC'), w.inst('fsumconst')], 'syl2anc',
            'sum_ r e. %s ( R ^ 2 ) = ( ( # ` %s ) x. ( R ^ 2 ) )' % (RS, RS))
    r0le = st([st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), r1], 'jca', '( 0 <_ 1 /\\ 1 <_ R )')
    rge0R = st([st([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), rr,
                st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), r1], 'letrd', '0 <_ R')
    card = st([nn, st([rr, rge0R], 'jca', '( R e. RR /\\ 0 <_ R )'), w.inst('z5rsetcard')], 'syl2anc', '( # ` %s ) <_ ( |_ ` R )' % RS)
    hc = st([st([fin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RS)], 'nn0red', '( # ` %s ) e. RR' % RS)
    cR = st([hc, st([rr, w.inst('reflcl')], 'syl', '( |_ ` R ) e. RR'), rr, card, st([rr, w.inst('flle')], 'syl', '( |_ ` R ) <_ R')], 'letrd', '( # ` %s ) <_ R' % RS)
    m = st([hc, rr, R2, st([rr], 'sqge0d', '0 <_ ( R ^ 2 )'), cR], 'lemul1ad', '( ( # ` %s ) x. ( R ^ 2 ) ) <_ ( R x. ( R ^ 2 ) )' % RS)
    rc = st([rr], 'recnd', 'R e. CC')
    y1 = st([rc, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0'), w.inst('expp1')], 'syl2anc', '( R ^ ( 2 + 1 ) ) = ( ( R ^ 2 ) x. R )')
    y2 = w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq2i', '( R ^ ( 2 + 1 ) ) = ( R ^ 3 )')
    y3 = st([y2, y1], 'eqtr3id', '( R ^ 3 ) = ( ( R ^ 2 ) x. R )')
    y4 = st([st([R2], 'recnd', '( R ^ 2 ) e. CC'), rc], 'mulcomd', '( ( R ^ 2 ) x. R ) = ( R x. ( R ^ 2 ) )')
    y5 = st([y3, y4], 'eqtrd', '( R ^ 3 ) = ( R x. ( R ^ 2 ) )')
    m2 = st([m, y5], 'breqtrrd', '( ( # ` %s ) x. ( R ^ 2 ) ) <_ ( R ^ 3 )' % RS)
    s3 = st([s2, m2], 'eqbrtrd', 'sum_ r e. %s ( R ^ 2 ) <_ ( R ^ 3 )' % RS)
    sr = st([fin, r3], 'fsumrecl', 'sum_ r e. %s ( ( 1 / r ) x. ( r ^ 3 ) ) e. RR' % RS)
    sR = st([fin, R2b], 'fsumrecl', 'sum_ r e. %s ( R ^ 2 ) e. RR' % RS)
    R3 = st([rr, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'reexpcld', '( R ^ 3 ) e. RR')
    w.qed([sr, sR, R3, s1, s3], 'letrd', STATEMENTS['z6cube'])
    return w


if __name__ == '__main__':
    for lab in sys.argv[1:]:
        w = globals()[lab]()
        run(w)
