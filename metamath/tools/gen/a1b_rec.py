#!/usr/bin/env python3
"""Sortie A1b: the recursion theory of ~ df-algrec and the disjoint-union
elimination ~ algdjun .  MM_DB=sorties/a1b.mm python3 tools/gen/a1b_rec.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import W, Cl, mptfv, mpoov
import tm

ALGREC = tm.defbody('df-algrec')


def FF(B):
    return '( k e. NN0 |-> if ( k = 0 , %s , ( k - 1 ) ) )' % B


def SQ(B):
    return 'seq 0 ( S , %s )' % FF(B)


LEV = '( B AlgRec S )'


def algrec0():
    ante = '( B e. _V /\\ S e. _V )'
    w = W('algrec0', 'The base of the recursion of ~ df-algrec : level ` 0 ` is '
                     'the given base function.  Lean: the ` | _, 0 => ` clause of '
                     'every recursion of Algorithm.lean is read off this.')
    b = w.s([], 'simpl', '( %s -> B e. _V )' % ante)
    s = w.s([], 'simpr', '( %s -> S e. _V )' % ante)
    cl = Cl(w, ante, {'B': ('_V', b), 'S': ('_V', s)})
    st1, val = mpoov(w, cl, ALGREC, 'B', 'S', astep=b, bstep=s, defref='df-algrec', F='AlgRec')
    assert val == SQ('B'), val
    st2 = w.s([st1], 'fveq1d', '( %s -> ( %s ` 0 ) = ( %s ` 0 ) )' % (ante, LEV, SQ('B')))
    z = w.s([], '0z', '0 e. ZZ')
    i = w.s([], 'seq1', '( 0 e. ZZ -> ( %s ` 0 ) = ( %s ` 0 ) )' % (SQ('B'), FF('B')))
    st3 = w.s([w.s([z, i], 'ax-mp', '( %s ` 0 ) = ( %s ` 0 )' % (SQ('B'), FF('B')))], 'a1i',
              '( %s -> ( %s ` 0 ) = ( %s ` 0 ) )' % (ante, SQ('B'), FF('B')))
    st4, v4 = mptfv(w, cl, FF('B'), '0')
    assert v4 == 'if ( 0 = 0 , B , ( 0 - 1 ) )', v4
    e = w.s([w.s([], 'eqid', '0 = 0')], 'a1i', '( %s -> 0 = 0 )' % ante)
    st5 = w.s([e], 'iftrued', '( %s -> %s = B )' % (ante, v4))
    a = w.s([st2, st3], 'eqtrd', '( %s -> ( %s ` 0 ) = ( %s ` 0 ) )' % (ante, LEV, FF('B')))
    b2 = w.s([a, st4], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ante, LEV, v4))
    w.qed([b2, st5], 'eqtrd', '( %s -> ( %s ` 0 ) = B )' % (ante, LEV))
    return w


def algrecp1():
    ante = '( B e. _V /\\ S e. _V /\\ N e. NN0 )'
    w = W('algrecp1', 'The step of the recursion of ~ df-algrec : level ` N + 1 ` is '
                      'the step operation applied to the index ` N ` and to level ` N `. '
                      'Lean: the ` | d, fuel + 1 => ` clause of every recursion of '
                      'Algorithm.lean is read off this.')
    b = w.s([], 'simp1', '( %s -> B e. _V )' % ante)
    s = w.s([], 'simp2', '( %s -> S e. _V )' % ante)
    n = w.s([], 'simp3', '( %s -> N e. NN0 )' % ante)
    cl = Cl(w, ante, {'B': ('_V', b), 'S': ('_V', s), 'N': ('NN0', n)})
    st1, val = mpoov(w, cl, ALGREC, 'B', 'S', astep=b, bstep=s, defref='df-algrec', F='AlgRec')
    sq, ff = SQ('B'), FF('B')
    # N e. ( ZZ>= ` 0 )
    uz = w.s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % ante)
    nu = w.s([n, uz], 'eleqtrd', '( %s -> N e. ( ZZ>= ` 0 ) )' % ante)
    i = w.s([], 'seqp1', '( N e. ( ZZ>= ` 0 ) -> ( %s ` ( N + 1 ) ) = ( ( %s ` N ) S ( %s ` ( N + 1 ) ) ) )'
             % (sq, sq, ff))
    st2 = w.s([nu, i], 'syl', '( %s -> ( %s ` ( N + 1 ) ) = ( ( %s ` N ) S ( %s ` ( N + 1 ) ) ) )'
              % (ante, sq, sq, ff))
    # ( FF ` ( N + 1 ) ) = N
    p1 = w.s([n, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ante)
    cl.have('( N + 1 )', 'NN0', p1)
    st3, v3 = mptfv(w, cl, ff, '( N + 1 )', argstep=p1)
    assert v3 == 'if ( ( N + 1 ) = 0 , B , ( ( N + 1 ) - 1 ) )', v3
    p1n = w.s([n, w.inst('nn0p1nn')], 'syl', '( %s -> ( N + 1 ) e. NN )' % ante)
    ne = w.s([p1n], 'nnne0d', '( %s -> ( N + 1 ) =/= 0 )' % ante)
    nq = w.s([ne], 'neneqd', '( %s -> -. ( N + 1 ) = 0 )' % ante)
    st4 = w.s([nq], 'iffalsed', '( %s -> %s = ( ( N + 1 ) - 1 ) )' % (ante, v3))
    ncn = w.s([n, w.inst('nn0cnd')], 'x', '') if False else w.s([n], 'nn0cnd', '( %s -> N e. CC )' % ante)
    one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ante)
    st5 = w.s([ncn, one], 'pncand', '( %s -> ( ( N + 1 ) - 1 ) = N )' % ante)
    f1 = w.s([w.s([st3, st4], 'eqtrd', '( %s -> ( %s ` ( N + 1 ) ) = ( ( N + 1 ) - 1 ) )' % (ante, ff)), st5],
             'eqtrd', '( %s -> ( %s ` ( N + 1 ) ) = N )' % (ante, ff))
    st6 = w.s([f1], 'oveq2d', '( %s -> ( ( %s ` N ) S ( %s ` ( N + 1 ) ) ) = ( ( %s ` N ) S N ) )'
              % (ante, sq, ff, sq))
    # back to ( B AlgRec S )
    lv = w.s([st1], 'eqcomd', '( %s -> %s = %s )' % (ante, sq, LEV))
    lvn = w.s([lv], 'fveq1d', '( %s -> ( %s ` N ) = ( %s ` N ) )' % (ante, sq, LEV))
    st8 = w.s([lvn], 'oveq1d', '( %s -> ( ( %s ` N ) S N ) = ( ( %s ` N ) S N ) )' % (ante, sq, LEV))
    lhs = w.s([st1], 'fveq1d', '( %s -> ( %s ` ( N + 1 ) ) = ( %s ` ( N + 1 ) ) )' % (ante, LEV, sq))
    c1 = w.s([lhs, st2], 'eqtrd', '( %s -> ( %s ` ( N + 1 ) ) = ( ( %s ` N ) S ( %s ` ( N + 1 ) ) ) )'
             % (ante, LEV, sq, ff))
    c2 = w.s([c1, st6], 'eqtrd', '( %s -> ( %s ` ( N + 1 ) ) = ( ( %s ` N ) S N ) )' % (ante, LEV, sq))
    w.qed([c2, st8], 'eqtrd', '( %s -> ( %s ` ( N + 1 ) ) = ( ( %s ` N ) S N ) )' % (ante, LEV, LEV))
    return w


ANT = '( C e. _V /\\ B e. C /\\ S : ( C X. NN0 ) --> C )'


def PH(x):
    return '( %s -> ( ( B AlgRec S ) ` %s ) e. C )' % (ANT, x)


def algrecmapl():
    w = W('algrecmapl', 'Every level of the recursion of ~ df-algrec maps the parameter '
                        'space into the codomain, by induction on the level.  Used at '
                        '` C = ( Cod ^m Dom ) `, where it says that the step may apply the '
                        'previous level to any parameter.  Deduction form: ~ algrecmap .')
    subs = []
    for tgt in ['0', 'y', '( y + 1 )', 'N']:
        idst = w.s([], 'id', '( x = %s -> x = %s )' % (tgt, tgt))
        st, new = w.wcongr(PH('x'), {'x': tgt}, 'x = %s' % tgt, {'x': idst})
        assert new == PH(tgt), (new, PH(tgt))
        subs.append(st)
    base = _base(w)
    step = _step(w)
    w.qed(subs + [base, step], 'nn0ind', '( N e. NN0 -> %s )' % PH('N'))
    return w


def _base(w):
    """|- ( ANT -> ( ( B AlgRec S ) ` 0 ) e. C )"""
    cv = w.s([], 'simp1', '( %s -> C e. _V )' % ANT)
    bc = w.s([], 'simp2', '( %s -> B e. C )' % ANT)
    sf = w.s([], 'simp3', '( %s -> S : ( C X. NN0 ) --> C )' % ANT)
    bv = w.s([bc, w.inst('elex')], 'syl', '( %s -> B e. _V )' % ANT)
    n0 = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'a1i', '( %s -> NN0 e. _V )' % ANT)
    xp = w.s([cv, n0, w.inst('xpexg')], 'syl2anc', '( %s -> ( C X. NN0 ) e. _V )' % ANT)
    sv = w.s([sf, xp, w.inst('fex')], 'syl2anc', '( %s -> S e. _V )' % ANT)
    a0 = w.s([bv, sv, w.inst('algrec0')], 'syl2anc', '( %s -> ( ( B AlgRec S ) ` 0 ) = B )' % ANT)
    return w.s([a0, bc], 'eqeltrd', PH('0'))


def _step(w):
    """|- ( y e. NN0 -> ( PH(y) -> PH(y+1) ) )"""
    a = '( ( y e. NN0 /\\ %s ) /\\ ( ( B AlgRec S ) ` y ) e. C )' % ANT
    yn = w.s([], 'simpll', '( %s -> y e. NN0 )' % a)
    an = w.s([], 'simplr', '( %s -> %s )' % (a, ANT))
    ih = w.s([], 'simpr', '( %s -> ( ( B AlgRec S ) ` y ) e. C )' % a)
    cv = w.s([an], 'simp1d', '( %s -> C e. _V )' % a)
    bc = w.s([an], 'simp2d', '( %s -> B e. C )' % a)
    sf = w.s([an], 'simp3d', '( %s -> S : ( C X. NN0 ) --> C )' % a)
    bv = w.s([bc, w.inst('elex')], 'syl', '( %s -> B e. _V )' % a)
    n0 = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'a1i', '( %s -> NN0 e. _V )' % a)
    xp = w.s([cv, n0, w.inst('xpexg')], 'syl2anc', '( %s -> ( C X. NN0 ) e. _V )' % a)
    sv = w.s([sf, xp, w.inst('fex')], 'syl2anc', '( %s -> S e. _V )' % a)
    ap = w.s([bv, sv, yn, w.inst('algrecp1')], 'syl3anc',
             '( %s -> ( ( B AlgRec S ) ` ( y + 1 ) ) = ( ( ( B AlgRec S ) ` y ) S y ) )' % a)
    ov = w.s([w.s([], 'df-ov', '( ( ( B AlgRec S ) ` y ) S y ) = ( S ` <. ( ( B AlgRec S ) ` y ) , y >. )')],
             'a1i', '( %s -> ( ( ( B AlgRec S ) ` y ) S y ) = ( S ` <. ( ( B AlgRec S ) ` y ) , y >. ) )' % a)
    op = w.s([ih, yn, w.inst('opelxpi')], 'syl2anc',
             '( %s -> <. ( ( B AlgRec S ) ` y ) , y >. e. ( C X. NN0 ) )' % a)
    fv = w.s([sf, op, w.inst('ffvelcdm')], 'syl2anc',
             '( %s -> ( S ` <. ( ( B AlgRec S ) ` y ) , y >. ) e. C )' % a)
    e1 = w.s([ap, ov], 'eqtrd',
             '( %s -> ( ( B AlgRec S ) ` ( y + 1 ) ) = ( S ` <. ( ( B AlgRec S ) ` y ) , y >. ) )' % a)
    r = w.s([e1, fv], 'eqeltrd', '( %s -> ( ( B AlgRec S ) ` ( y + 1 ) ) e. C )' % a)
    e2 = w.s([r], 'ex', '( ( y e. NN0 /\\ %s ) -> ( ( ( B AlgRec S ) ` y ) e. C -> ( ( B AlgRec S ) ` ( y + 1 ) ) e. C ) )' % ANT)
    ex = w.s([e2], 'ex', '( y e. NN0 -> ( %s -> ( ( ( B AlgRec S ) ` y ) e. C -> ( ( B AlgRec S ) ` ( y + 1 ) ) e. C ) ) )' % ANT)
    return w.s([ex], 'a2d', '( y e. NN0 -> ( %s -> %s ) )' % (PH('y'), PH('( y + 1 )')))


def algrecmap():
    w = W('algrecmap', 'Every level of the recursion of ~ df-algrec maps the parameter '
                       'space into the codomain (deduction form of ~ algrecmapl ).')
    i = w.s([], 'algrecmapl', '( N e. NN0 -> %s )' % PH('N'))
    w.qed([i], 'impcom', '( ( %s /\\ N e. NN0 ) -> ( ( B AlgRec S ) ` N ) e. C )' % ANT)
    return w


def algdjun():
    ante = '( X e. ( A |_| 1o ) /\\ X =/= ( inr ` (/) ) )'
    goal = '( ( 2nd ` X ) e. A /\\ X = ( inl ` ( 2nd ` X ) ) )'
    w = W('algdjun', 'Elimination of a disjoint union with a one-element right summand: '
                     'an element that is not ` none ` is ` some ` of its second '
                     'projection, and that projection lies in the left summand.  This is '
                     'what turns Lean\'s ` match t r with | some W => ... ` into '
                     '` ( 2nd ` ( t ` r ) ) ` in ~ df-dpgos and ~ df-extractgos .')
    h1 = w.s([], 'simpl', '( %s -> X e. ( A |_| 1o ) )' % ante)
    h2 = w.s([], 'simpr', '( %s -> X =/= ( inr ` (/) ) )' % ante)
    ss = w.s([w.s([], 'djuss', '( A |_| 1o ) C_ ( { (/) , 1o } X. ( A u. 1o ) )')], 'a1i',
             '( %s -> ( A |_| 1o ) C_ ( { (/) , 1o } X. ( A u. 1o ) ) )' % ante)
    xp = w.s([ss, h1], 'sseldd', '( %s -> X e. ( { (/) , 1o } X. ( A u. 1o ) ) )' % ante)
    pr = w.s([xp, w.inst('1st2nd2')], 'syl', '( %s -> X = <. ( 1st ` X ) , ( 2nd ` X ) >. )' % ante)
    dj = w.s([h1, w.inst('eldju1st')], 'syl', '( %s -> ( ( 1st ` X ) = (/) \\/ ( 1st ` X ) = 1o ) )' % ante)
    # left case
    al = '( %s /\\ ( 1st ` X ) = (/) )' % ante
    l1 = w.s([h1], 'adantr', '( %s -> X e. ( A |_| 1o ) )' % al)
    l2 = w.s([], 'simpr', '( %s -> ( 1st ` X ) = (/) )' % al)
    l3 = w.s([l1, l2, w.inst('eldju2ndl')], 'syl2anc', '( %s -> ( 2nd ` X ) e. A )' % al)
    l4 = w.s([pr], 'adantr', '( %s -> X = <. ( 1st ` X ) , ( 2nd ` X ) >. )' % al)
    l5 = w.s([l2], 'opeq1d', '( %s -> <. ( 1st ` X ) , ( 2nd ` X ) >. = <. (/) , ( 2nd ` X ) >. )' % al)
    l6 = w.s([w.s([], 'fvex', '( 2nd ` X ) e. _V')], 'a1i', '( %s -> ( 2nd ` X ) e. _V )' % al)
    l7 = w.s([l6, w.inst('inlval')], 'syl', '( %s -> ( inl ` ( 2nd ` X ) ) = <. (/) , ( 2nd ` X ) >. )' % al)
    l8 = w.s([w.s([l4, l5], 'eqtrd', '( %s -> X = <. (/) , ( 2nd ` X ) >. )' % al), l7], 'eqtr4d',
             '( %s -> X = ( inl ` ( 2nd ` X ) ) )' % al)
    lc = w.s([l3, l8], 'jca', '( %s -> %s )' % (al, goal))
    # right case
    ar = '( %s /\\ ( 1st ` X ) = 1o )' % ante
    r1 = w.s([h1], 'adantr', '( %s -> X e. ( A |_| 1o ) )' % ar)
    r2 = w.s([], 'simpr', '( %s -> ( 1st ` X ) = 1o )' % ar)
    r3 = w.s([w.s([], '1n0', '1o =/= (/)')], 'a1i', '( %s -> 1o =/= (/) )' % ar)
    r4 = w.s([r2, r3], 'eqnetrd', '( %s -> ( 1st ` X ) =/= (/) )' % ar)
    r5 = w.s([r1, r4, w.inst('eldju2ndr')], 'syl2anc', '( %s -> ( 2nd ` X ) e. 1o )' % ar)
    r6 = w.s([], 'el1o', '( ( 2nd ` X ) e. 1o <-> ( 2nd ` X ) = (/) )')
    r7 = w.s([r5, w.s([r6], 'a1i', '( %s -> ( ( 2nd ` X ) e. 1o <-> ( 2nd ` X ) = (/) ) )' % ar)],
             'mpbid', '( %s -> ( 2nd ` X ) = (/) )' % ar)
    r8 = w.s([pr], 'adantr', '( %s -> X = <. ( 1st ` X ) , ( 2nd ` X ) >. )' % ar)
    r9 = w.s([r2, r7], 'opeq12d', '( %s -> <. ( 1st ` X ) , ( 2nd ` X ) >. = <. 1o , (/) >. )' % ar)
    ra = w.s([w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % ar), w.inst('inrval')],
             'syl', '( %s -> ( inr ` (/) ) = <. 1o , (/) >. )' % ar)
    rb = w.s([w.s([r8, r9], 'eqtrd', '( %s -> X = <. 1o , (/) >. )' % ar), ra], 'eqtr4d',
             '( %s -> X = ( inr ` (/) ) )' % ar)
    rc = w.s([w.s([h2], 'adantr', '( %s -> X =/= ( inr ` (/) ) )' % ar)], 'neneqd',
             '( %s -> -. X = ( inr ` (/) ) )' % ar)
    rcs = w.s([rb, rc], 'pm2.21dd', '( %s -> %s )' % (ar, goal))
    w.qed([lc, rcs, dj], 'mpjaodan', '( %s -> %s )' % (ante, goal))
    return w


BUILD = {'algrec0': algrec0, 'algrecp1': algrecp1, 'algrecmapl': algrecmapl,
         'algrecmap': algrecmap, 'algdjun': algdjun}

def algwrdcs():
    ante = '( ( W e. Word S /\\ N e. NN0 ) /\\ ( # ` W ) = ( N + 1 ) )'
    goal = 'E. p e. S E. u e. Word S ( ( # ` u ) = N /\\ W = ( <" p "> ++ u ) )'
    w = W('algwrdcs', 'Every word of length ` N + 1 ` is a letter followed by a word of '
                      'length ` N `.  This is the step of an induction on the length of '
                      'a list, the form the cons equation lemmas of this block '
                      '(~ mulallcs , ~ prodlcs , ~ extractgocss , ...) are stated in; '
                      'set.mm\'s own ~ wrdind appends at the end instead, which those '
                      'equations do not match.')
    ww = w.s([], 'simpll', '( %s -> W e. Word S )' % ante)
    nn = w.s([], 'simplr', '( %s -> N e. NN0 )' % ante)
    ln = w.s([], 'simpr', '( %s -> ( # ` W ) = ( N + 1 ) )' % ante)
    p1 = w.s([nn, w.s([], 'nn0p1nn', '( N e. NN0 -> ( N + 1 ) e. NN )')], 'syl',
             '( %s -> ( N + 1 ) e. NN )' % ante)
    n0 = w.s([p1], 'nnne0d', '( %s -> ( N + 1 ) =/= 0 )' % ante)
    ne = w.s([ln, n0], 'eqnetrd', '( %s -> ( # ` W ) =/= 0 )' % ante)
    nq = w.s([ne], 'neneqd', '( %s -> -. ( # ` W ) = 0 )' % ante)
    wv = w.s([ww, w.s([], 'elex', '( W e. Word S -> W e. _V )')], 'syl', '( %s -> W e. _V )' % ante)
    hz = w.s([wv, w.s([], 'hasheq0', '( W e. _V -> ( ( # ` W ) = 0 <-> W = (/) ) )')], 'syl',
             '( %s -> ( ( # ` W ) = 0 <-> W = (/) ) )' % ante)
    w0 = w.s([nq, hz], 'mtbid', '( %s -> -. W = (/) )' % ante)
    wne = w.s([w0], 'neqned', '( %s -> W =/= (/) )' % ante)
    cj = w.s([ww, wne], 'jca', '( %s -> ( W e. Word S /\\ W =/= (/) ) )' % ante)
    hd = w.s([cj, w.s([], 'wrdfv0', '( ( W e. Word S /\\ W =/= (/) ) -> ( W ` 0 ) e. S )')], 'syl',
             '( %s -> ( W ` 0 ) e. S )' % ante)
    TL = '( W substr <. 1 , ( # ` W ) >. )'
    tw = w.s([ww, w.s([], 'swrdcl', '( W e. Word S -> %s e. Word S )' % TL)], 'syl',
             '( %s -> %s e. Word S )' % (ante, TL))
    tl = w.s([cj, w.s([], 'wrdtllen', '( ( W e. Word S /\\ W =/= (/) ) -> ( # ` %s ) = ( ( # ` W ) - 1 ) )' % TL)],
             'syl', '( %s -> ( # ` %s ) = ( ( # ` W ) - 1 ) )' % (ante, TL))
    o1 = w.s([ln], 'oveq1d', '( %s -> ( ( # ` W ) - 1 ) = ( ( N + 1 ) - 1 ) )' % ante)
    ncn = w.s([nn], 'nn0cnd', '( %s -> N e. CC )' % ante)
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % ante)
    pc = w.s([ncn, one], 'pncand', '( %s -> ( ( N + 1 ) - 1 ) = N )' % ante)
    tln = w.s([w.s([tl, o1], 'eqtrd', '( %s -> ( # ` %s ) = ( ( N + 1 ) - 1 ) )' % (ante, TL)), pc],
              'eqtrd', '( %s -> ( # ` %s ) = N )' % (ante, TL))
    dec = w.s([cj, w.s([], 'wrdhdtl', '( ( W e. Word S /\\ W =/= (/) ) -> W = ( <" ( W ` 0 ) "> ++ %s ) )' % TL)],
              'syl', '( %s -> W = ( <" ( W ` 0 ) "> ++ %s ) )' % (ante, TL))
    body = '( ( # ` u ) = N /\\ W = ( <" ( W ` 0 ) "> ++ u ) )'
    inner = '( ( # ` %s ) = N /\\ W = ( <" ( W ` 0 ) "> ++ %s ) )' % (TL, TL)
    ib = w.s([tln, dec], 'jca', '( %s -> %s )' % (ante, inner))
    au = '( %s /\\ u = %s )' % (ante, TL)
    idu = w.s([], 'simpr', '( %s -> u = %s )' % (au, TL))
    su, newu = w.wcongr(body, {'u': TL}, au, {'u': idu})
    assert newu == inner, (newu, inner)
    ex1 = w.s([tw, su, ib], 'rspcedvd', '( %s -> E. u e. Word S %s )' % (ante, body))
    outer = 'E. u e. Word S ( ( # ` u ) = N /\\ W = ( <" p "> ++ u ) )'
    ap = '( %s /\\ p = ( W ` 0 ) )' % ante
    idp = w.s([], 'simpr', '( %s -> p = ( W ` 0 ) )' % ap)
    sp, newp = w.wcongr(outer, {'p': '( W ` 0 )'}, ap, {'p': idp})
    assert newp == 'E. u e. Word S %s' % body, newp
    w.qed([hd, sp, ex1], 'rspcedvd', '( %s -> %s )' % (ante, goal))
    return w


BUILD['algwrdcs'] = algwrdcs


ANTI = '( (/) e. C /\\ A. a e. Word B A. b e. B ( a e. C -> ( <" b "> ++ a ) e. C ) )'


def PHI(t):
    return '( %s -> A. v e. Word B ( ( # ` v ) = %s -> v e. C ) )' % (ANTI, t)


def algwrdi():
    w = W('algwrdi', 'Induction on a list from the empty list by prepending a letter, '
                     'the form the cons equation lemmas of this block are stated in: a '
                     'class ` C ` that contains the empty word and is closed under '
                     '` v |-> ( <" b "> ++ v ) ` contains every word.  A consumer takes '
                     '` C = { x e. Word B | ph } ` and reads membership back with '
                     '~ elrab .  set.mm\'s own ~ wrdind appends at the end instead, '
                     'which the cons equations do not match.')
    subs = []
    for tgt in ['0', 'y', '( y + 1 )', '( # ` W )']:
        idst = w.s([], 'id', '( x = %s -> x = %s )' % (tgt, tgt))
        st, new = w.wcongr(PHI('x'), {'x': tgt}, 'x = %s' % tgt, {'x': idst})
        assert new == PHI(tgt), (new, PHI(tgt))
        subs.append(st)
    base = _wbase(w)
    step = _wstep(w)
    ind = w.s(subs + [base, step], 'nn0ind', '( ( # ` W ) e. NN0 -> %s )' % PHI('( # ` W )'))
    ante = '( %s /\\ W e. Word B )' % ANTI
    an = w.s([], 'simpl', '( %s -> %s )' % (ante, ANTI))
    ww = w.s([], 'simpr', '( %s -> W e. Word B )' % ante)
    ln = w.s([ww, w.s([], 'lencl', '( W e. Word B -> ( # ` W ) e. NN0 )')], 'syl',
             '( %s -> ( # ` W ) e. NN0 )' % ante)
    a2 = w.s([w.s([ind], 'a1i', '( %s -> ( ( # ` W ) e. NN0 -> %s ) )' % (ante, PHI('( # ` W )'))), ln],
             'mpd', '( %s -> %s )' % (ante, PHI('( # ` W )')))
    a3 = w.s([a2, an], 'mpd', '( %s -> A. v e. Word B ( ( # ` v ) = ( # ` W ) -> v e. C ) )' % ante)
    body = '( ( # ` v ) = ( # ` W ) -> v e. C )'
    tgtb = '( ( # ` W ) = ( # ` W ) -> W e. C )'
    idv = w.s([], 'id', '( v = W -> v = W )')
    sv, newb = w.wcongr(body, {'v': 'W'}, 'v = W', {'v': idv})
    assert newb == tgtb, (newb, tgtb)
    rs = w.s([sv], 'rspcv', '( W e. Word B -> ( A. v e. Word B %s -> %s ) )' % (body, tgtb))
    im = w.s([ww, rs], 'syl', '( %s -> ( A. v e. Word B %s -> %s ) )' % (ante, body, tgtb))
    fi = w.s([im, a3], 'mpd', '( %s -> %s )' % (ante, tgtb))
    eq = w.s([w.s([], 'eqid', '( # ` W ) = ( # ` W )')], 'a1i', '( %s -> ( # ` W ) = ( # ` W ) )' % ante)
    w.qed([fi, eq], 'mpd', '( %s -> W e. C )' % ante)
    return w


def _wbase(w):
    a = '( %s /\\ v e. Word B )' % ANTI
    e0 = w.s([], 'simpll', '( %s -> (/) e. C )' % a)
    vx = w.s([w.s([], 'vex', 'v e. _V')], 'a1i', '( %s -> v e. _V )' % a)
    hz = w.s([vx, w.s([], 'hasheq0', '( v e. _V -> ( ( # ` v ) = 0 <-> v = (/) ) )')], 'syl',
             '( %s -> ( ( # ` v ) = 0 <-> v = (/) ) )' % a)
    a2 = '( %s /\\ ( # ` v ) = 0 )' % a
    hz2 = w.s([hz], 'adantr', '( %s -> ( ( # ` v ) = 0 <-> v = (/) ) )' % a2)
    c0 = w.s([], 'simpr', '( %s -> ( # ` v ) = 0 )' % a2)
    we = w.s([c0, hz2], 'mpbid', '( %s -> v = (/) )' % a2)
    ec = w.s([e0], 'adantr', '( %s -> (/) e. C )' % a2)
    wc = w.s([we, ec], 'eqeltrd', '( %s -> v e. C )' % a2)
    ex = w.s([wc], 'ex', '( %s -> ( ( # ` v ) = 0 -> v e. C ) )' % a)
    return w.s([ex], 'ralrimiva', PHI('0'))


IHV = 'A. v e. Word B ( ( # ` v ) = y -> v e. C )'
IHT = 'A. t e. Word B ( ( # ` t ) = y -> t e. C )'


def _wstep(w):
    a = '( ( ( y e. NN0 /\\ %s ) /\\ %s ) /\\ v e. Word B )' % (ANTI, IHT)
    a2 = '( %s /\\ ( # ` v ) = ( y + 1 ) )' % a
    yn = w.s([], 'simplll', '( %s -> y e. NN0 )' % a)
    an = w.s([], 'simpllr', '( %s -> %s )' % (a, ANTI))
    ihs = w.s([], 'simplr', '( %s -> %s )' % (a, IHT))
    ww = w.s([], 'simpr', '( %s -> v e. Word B )' % a)
    cj = w.s([w.s([ww, yn], 'jca', '( %s -> ( v e. Word B /\\ y e. NN0 ) )' % a)], 'adantr',
             '( %s -> ( v e. Word B /\\ y e. NN0 ) )' % a2)
    ln = w.s([], 'simpr', '( %s -> ( # ` v ) = ( y + 1 ) )' % a2)
    dec = w.s([w.s([cj, ln], 'jca',
                   '( %s -> ( ( v e. Word B /\\ y e. NN0 ) /\\ ( # ` v ) = ( y + 1 ) ) )' % a2),
               w.s([], 'algwrdcs', '( ( ( v e. Word B /\\ y e. NN0 ) /\\ ( # ` v ) = ( y + 1 ) ) -> '
                                   'E. p e. B E. u e. Word B ( ( # ` u ) = y /\\ v = ( <" p "> ++ u ) ) )')],
              'syl', '( %s -> E. p e. B E. u e. Word B ( ( # ` u ) = y /\\ v = ( <" p "> ++ u ) ) )' % a2)
    b = '( %s /\\ ( p e. B /\\ u e. Word B ) )' % a2
    pr = w.s([], 'simpr', '( %s -> ( p e. B /\\ u e. Word B ) )' % b)
    pb = w.s([pr], 'simpld', '( %s -> p e. B )' % b)
    ub = w.s([pr], 'simprd', '( %s -> u e. Word B )' % b)
    ihb = w.s([w.s([ihs], 'adantr', '( %s -> %s )' % (a2, IHT))], 'adantr', '( %s -> %s )' % (b, IHT))
    anb = w.s([w.s([an], 'adantr', '( %s -> %s )' % (a2, ANTI))], 'adantr', '( %s -> %s )' % (b, ANTI))
    bodyt = '( ( # ` t ) = y -> t e. C )'
    tgtu = '( ( # ` u ) = y -> u e. C )'
    idt = w.s([], 'id', '( t = u -> t = u )')
    st1, nb = w.wcongr(bodyt, {'t': 'u'}, 't = u', {'t': idt})
    assert nb == tgtu, (nb, tgtu)
    ri = w.s([st1], 'rspcv', '( u e. Word B -> ( %s -> %s ) )' % (IHT, tgtu))
    iu = w.s([w.s([ub, ri], 'syl', '( %s -> ( %s -> %s ) )' % (b, IHT, tgtu)), ihb], 'mpd',
             '( %s -> %s )' % (b, tgtu))
    c = '( %s /\\ ( ( # ` u ) = y /\\ v = ( <" p "> ++ u ) ) )' % b
    cr = w.s([], 'simpr', '( %s -> ( ( # ` u ) = y /\\ v = ( <" p "> ++ u ) ) )' % c)
    uy = w.s([cr], 'simpld', '( %s -> ( # ` u ) = y )' % c)
    weq = w.s([cr], 'simprd', '( %s -> v = ( <" p "> ++ u ) )' % c)
    uc = w.s([w.s([iu], 'adantr', '( %s -> %s )' % (c, tgtu)), uy], 'mpd', '( %s -> u e. C )' % c)
    anc = w.s([anb], 'adantr', '( %s -> %s )' % (c, ANTI))
    cls = w.s([anc], 'simprd', '( %s -> A. a e. Word B A. b e. B ( a e. C -> ( <" b "> ++ a ) e. C ) )' % c)
    inner = 'A. b e. B ( a e. C -> ( <" b "> ++ a ) e. C )'
    inneru = 'A. b e. B ( u e. C -> ( <" b "> ++ u ) e. C )'
    ida = w.s([], 'id', '( a = u -> a = u )')
    sa, na = w.wcongr(inner, {'a': 'u'}, 'a = u', {'a': ida})
    assert na == inneru, (na, inneru)
    r1 = w.s([sa], 'rspcv', '( u e. Word B -> ( A. a e. Word B %s -> %s ) )' % (inner, inneru))
    ubc = w.s([ub], 'adantr', '( %s -> u e. Word B )' % c)
    s1 = w.s([w.s([ubc, r1], 'syl', '( %s -> ( A. a e. Word B %s -> %s ) )' % (c, inner, inneru)), cls],
             'mpd', '( %s -> %s )' % (c, inneru))
    bodyb = '( u e. C -> ( <" b "> ++ u ) e. C )'
    tgtp = '( u e. C -> ( <" p "> ++ u ) e. C )'
    idb = w.s([], 'id', '( b = p -> b = p )')
    sb, nbb = w.wcongr(bodyb, {'b': 'p'}, 'b = p', {'b': idb})
    assert nbb == tgtp, (nbb, tgtp)
    r2 = w.s([sb], 'rspcv', '( p e. B -> ( %s -> %s ) )' % (inneru, tgtp))
    pbc = w.s([pb], 'adantr', '( %s -> p e. B )' % c)
    s2 = w.s([w.s([pbc, r2], 'syl', '( %s -> ( %s -> %s ) )' % (c, inneru, tgtp)), s1], 'mpd',
             '( %s -> %s )' % (c, tgtp))
    pc = w.s([s2, uc], 'mpd', '( %s -> ( <" p "> ++ u ) e. C )' % c)
    wc = w.s([weq, pc], 'eqeltrd', '( %s -> v e. C )' % c)
    ex1 = w.s([wc], 'ex', '( %s -> ( ( ( # ` u ) = y /\\ v = ( <" p "> ++ u ) ) -> v e. C ) )' % b)
    rl = w.s([ex1], 'rexlimdvva',
             '( %s -> ( E. p e. B E. u e. Word B ( ( # ` u ) = y /\\ v = ( <" p "> ++ u ) ) -> v e. C ) )' % a2)
    wcf = w.s([rl, dec], 'mpd', '( %s -> v e. C )' % a2)
    ex2 = w.s([wcf], 'ex', '( %s -> ( ( # ` v ) = ( y + 1 ) -> v e. C ) )' % a)
    GOAL = 'A. v e. Word B ( ( # ` v ) = ( y + 1 ) -> v e. C )'
    r3 = w.s([ex2], 'ralrimiva', '( ( ( y e. NN0 /\\ %s ) /\\ %s ) -> %s )' % (ANTI, IHT, GOAL))
    idv2 = w.s([], 'id', '( v = t -> v = t )')
    sc, nc = w.wcongr('( ( # ` v ) = y -> v e. C )', {'v': 't'}, 'v = t', {'v': idv2})
    cb = w.s([sc], 'cbvralvw', '( %s <-> %s )' % (IHV, IHT))
    bi = w.s([cb], 'biimpi', '( %s -> %s )' % (IHV, IHT))
    r3v = w.s([bi, r3], 'sylan2', '( ( ( y e. NN0 /\\ %s ) /\\ %s ) -> %s )' % (ANTI, IHV, GOAL))
    e3 = w.s([r3v], 'ex', '( ( y e. NN0 /\\ %s ) -> ( %s -> %s ) )' % (ANTI, IHV, GOAL))
    e4 = w.s([e3], 'ex', '( y e. NN0 -> ( %s -> ( %s -> %s ) ) )' % (ANTI, IHV, GOAL))
    return w.s([e4], 'a2d', '( y e. NN0 -> ( %s -> %s ) )' % (PHI('y'), PHI('( y + 1 )')))


BUILD['algwrdi'] = algwrdi


if __name__ == '__main__':
    names = sys.argv[1:] or list(BUILD)
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
