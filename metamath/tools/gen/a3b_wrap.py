"""Sortie A3b, batch 5: the two frozen eventual wrappers, extraction_inputsW and
output_carmichaelW (A3b-blueprint.md section 2.5)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
import a3blib as LIB, a2lib
from a3blib import HC, HN, NS, IW, GW, PL, A, B
from a2lib import WH, EV
from tm import *
from lin import linarith
import num
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

SUB = {'N': 'n', 'Q': 'q', 'Z': 'z', 'K': 'k', 'W': 'w', 'Y': 'y', 'T': 't', 'S': 's'}
sv = lambda t: LIB.subvars(t, SUB)

an, bn = A('n'), B('n')
nn = NS('n')
HNn = HN('n')
IWn = sv(IW())
GWz = sv(GW)
PLq = sv(PL)
Lq = '( Lmod ` q )'
CARD = '( # ` q ) = t'
COP = '( k gcd %s ) = 1' % Lq
POOLB = '( ( log ` n ) ^c ( 6 / 5 ) ) <_ ( # ` %s )' % PLq
QPn = '( q e. ~P %s /\\ %s )' % (GWz, CARD)
N9 = '( ; ; 1 5 0 x. ( %s ^ 2 ) ) <_ ( exp ` %s )' % (an, an)
N10 = '( ( ; 7 5 / D ) x. ( %s ^ 2 ) ) <_ ( exp ` ( ( 9 / ; 1 0 ) x. %s ) )' % (an, an)


def evitems(w, extra):
    """the eight (ten) eventual scalar facts as steps under ph, and the bundle"""
    def cl(f, kind):
        return w.s([num.fact(w, f, kind)], 'a1i', '( ph -> %s e. %s )' % (f, kind) if kind in ('RR', 'RR+', 'NN0', 'CC') else '( ph -> %s )' % f)
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( ph -> %s )' % f)
    cre, c1k, ere, e0, eh = w.hyps[:5]
    # C in RR+, 4 C in RR+, log ( 4 C ) real
    c0 = linarith(w, 'ph', [c1k], '0 < C', leaves={'C': ('RR', cre)})
    c4re = st([w.s([num.fact(w, '4', 'RR')], 'a1i', '( ph -> 4 e. RR )'), cre], 'remulcld', '( 4 x. C ) e. RR')
    c40 = linarith(w, 'ph', [c1k], '0 < ( 4 x. C )', leaves={'C': ('RR', cre)})
    c4rp = st([c4re, c40], 'elrpd', '( 4 x. C ) e. RR+')
    lc4 = st([c4rp], 'relogcld', '( log ` ( 4 x. C ) ) e. RR')
    erp = st([ere, e0], 'elrpd', 'E e. RR+')
    i4rp = w.s([num.fact(w, '4', 'RR+')], 'a1i', '( ph -> 4 e. RR+ )')
    e4rp = st([erp, i4rp], 'rpdivcld', '( E / 4 ) e. RR+')
    i3rp = w.s([num.fact(w, '3', 'RR+')], 'a1i', '( ph -> 3 e. RR+ )')
    e34 = st([st([i3rp, erp], 'rpmulcld', '( 3 x. E ) e. RR+'), i4rp], 'rpdivcld', '( ( 3 x. E ) / 4 ) e. RR+')
    e4re = st([e4rp], 'rpred', '( E / 4 ) e. RR')
    ome = st([w.s([num.fact(w, '1', 'RR')], 'a1i', '( ph -> 1 e. RR )'), e4re], 'resubcld', '( 1 - ( E / 4 ) ) e. RR')
    ele1 = linarith(w, 'ph', [eh], 'E <_ 1', leaves={'E': ('RR', ere)})
    ome0 = linarith(w, 'ph', [ele1], '0 < ( 1 - ( E / 4 ) )', leaves={'E': ('RR', ere)})
    omerp = st([ome, ome0], 'elrpd', '( 1 - ( E / 4 ) ) e. RR+')
    c96 = st([st([w.s([num.fact(w, '; ; ; 9 6 0 0', 'RR')], 'a1i', '( ph -> ; ; ; 9 6 0 0 e. RR )'), cre], 'remulcld', '( ; ; ; 9 6 0 0 x. C ) e. RR'),
              linarith(w, 'ph', [c1k], '0 < ( ; ; ; 9 6 0 0 x. C )', leaves={'C': ('RR', cre)})], 'elrpd', '( ; ; ; 9 6 0 0 x. C ) e. RR+')
    # the items
    e1 = w.s([w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))], 'a1i', '( ph -> %s )' % EV('n e. ( ZZ>= ` 3 )'))
    e2 = st([w.s([num.fact(w, '; 5 0', 'RR')], 'a1i', '( ph -> ; 5 0 e. RR )'), w.inst('ell2ge')], 'syl', EV(nn[1]))
    e3 = st([w.s([num.fact(w, '1', 'RR')], 'a1i', '( ph -> 1 e. RR )'), w.inst('ell3ge')], 'syl', EV(nn[2]))
    e4 = st([lc4, w.inst('ell3ge')], 'syl', EV(nn[3]))
    e5 = st([e4rp, w.inst('ell3sqle')], 'syl', EV(nn[4]))
    e6 = st([c96, e34, w.inst('evcxpge')], 'syl2anc', EV(nn[5]))
    e7 = st([w.s([num.fact(w, '; ; ; 1 2 0 0', 'RR+')], 'a1i', '( ph -> ; ; ; 1 2 0 0 e. RR+ )'), omerp, w.inst('evcxpge')], 'syl2anc', EV(nn[6]))
    i3100 = w.s([num.fact(w, '( 3 / ; ; 1 0 0 )', 'RR+')], 'a1i', '( ph -> ( 3 / ; ; 1 0 0 ) e. RR+ )')
    e8 = st([w.s([num.fact(w, '; 1 6', 'RR')], 'a1i', '( ph -> ; 1 6 e. RR )'),
             w.s([num.fact(w, '; 1 6', 'ge0')], 'a1i', '( ph -> 0 <_ ; 1 6 )'), i3100, w.inst('quadexpe')], 'syl3anc', EV(nn[7]))
    b1 = LIB.evan3(w, 'ph', [e1, e2, e3], [nn[0], nn[1], nn[2]], EV)
    b2 = w.s([e4, e5], 'evan2', '( ph -> %s )' % EV('( %s /\\ %s )' % (nn[3], nn[4])))
    b3 = LIB.evan3(w, 'ph', [e6, e7, e8], [nn[5], nn[6], nn[7]], EV)
    T1 = '( %s /\\ %s /\\ %s )' % (nn[0], nn[1], nn[2])
    T2 = '( %s /\\ %s )' % (nn[3], nn[4])
    T3 = '( %s /\\ %s /\\ %s )' % (nn[5], nn[6], nn[7])
    hn = LIB.evan3(w, 'ph', [b1, b2, b3], [T1, T2, T3], EV)
    assert '( %s /\\ %s /\\ %s )' % (T1, T2, T3) == HNn, (T1, T2, T3, HNn)
    if not extra:
        return hn, HNn
    dre, d0 = w.hyps[5], w.hyps[6]
    are = st([dre, d0], 'elrpd', 'D e. RR+')
    k75 = st([w.s([num.fact(w, '; 7 5', 'RR')], 'a1i', '( ph -> ; 7 5 e. RR )'), dre,
              st([d0], 'gt0ne0d', 'D =/= 0')], 'redivcld', '( ; 7 5 / D ) e. RR')
    k750 = st([w.s([num.fact(w, '; 7 5', 'RR+')], 'a1i', '( ph -> ; 7 5 e. RR+ )'), are], 'rpdivcld', '( ; 7 5 / D ) e. RR+')
    e9 = st([w.s([num.fact(w, '; ; 1 5 0', 'RR')], 'a1i', '( ph -> ; ; 1 5 0 e. RR )'),
             w.s([num.fact(w, '; ; 1 5 0', 'ge0')], 'a1i', '( ph -> 0 <_ ; ; 1 5 0 )'), w.inst('evexpsq')], 'syl2anc', EV(N9))
    i910 = w.s([num.fact(w, '( 9 / ; 1 0 )', 'RR+')], 'a1i', '( ph -> ( 9 / ; 1 0 ) e. RR+ )')
    e10 = st([k75, st([k750], 'rpge0d', '0 <_ ( ; 7 5 / D )'), i910, w.inst('quadexpe')], 'syl3anc', EV(N10))
    ex = w.s([e9, e10], 'evan2', '( ph -> %s )' % EV('( %s /\\ %s )' % (N9, N10)))
    full = w.s([hn, ex], 'evan2', '( ph -> %s )' % EV('( %s /\\ ( %s /\\ %s ) )' % (HNn, N9, N10)))
    return full, '( %s /\\ ( %s /\\ %s ) )' % (HNn, N9, N10)


def levels(AQ):
    """the nested antecedents of the quantifier assembly"""
    B6 = '( %s /\\ z e. NN0 )' % AQ
    B5 = '( %s /\\ w e. NN0 )' % B6
    B4 = '( %s /\\ y e. NN0 )' % B5
    B3 = '( %s /\\ t e. NN0 )' % B4
    B2 = '( %s /\\ %s )' % (B3, IWn)
    B1 = '( %s /\\ q e. ~P %s )' % (B2, GWz)
    Bf = '( %s /\\ %s )' % (B1, CARD)
    Bk = '( %s /\\ k e. NN )' % Bf
    return B6, B5, B4, B3, B2, B1, Bf, Bk


def unpack(w, D0, Bk, tail, AQ, B6, B5, B4, B3, B2, B1, Bf):
    """simpld/simprd chain from D0 = ( Bk /\\ tailwff ) down to ph and the bundle"""
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (D0, f))
    bk = st([], 'simpl', Bk)
    tl = st([], 'simpr', tail)
    bf = st([bk], 'simpld', Bf); knn = st([bk], 'simprd', 'k e. NN')
    b1 = st([bf], 'simpld', B1); card = st([bf], 'simprd', CARD)
    b2 = st([b1], 'simpld', B2); qpw = st([b1], 'simprd', 'q e. ~P %s' % GWz)
    b3 = st([b2], 'simpld', B3); iw = st([b2], 'simprd', IWn)
    b4 = st([b3], 'simpld', B4); tn0 = st([b3], 'simprd', 't e. NN0')
    b5 = st([b4], 'simpld', B5); yn0 = st([b4], 'simprd', 'y e. NN0')
    b6 = st([b5], 'simpld', B6); wn0 = st([b5], 'simprd', 'w e. NN0')
    aq = st([b6], 'simpld', AQ); zn0 = st([b6], 'simprd', 'z e. NN0')
    phs = st([aq], 'simpld', 'ph'); bun = st([aq], 'simprd', AQ.split(' /\\ ', 1)[1][:-2].strip())
    return dict(st=st, tl=tl, knn=knn, card=card, qpw=qpw, iw=iw, phs=phs, bun=bun)


def hcstep(w, D0, phs, st):
    cre, c1k, ere, e0, eh = [st([phs, h], 'syl', f) for h, f in
                             zip(w.hyps[:5], ['C e. RR', '; ; ; 1 0 0 0 <_ C', 'E e. RR', '0 < E', 'E <_ ( 1 / 2 )'])]
    return st([st([cre, c1k], 'jca', '( C e. RR /\\ ; ; ; 1 0 0 0 <_ C )'),
               st([ere, e0, eh], '3jca', '( E e. RR /\\ 0 < E /\\ E <_ ( 1 / 2 ) )')], 'jca', HC)


# --------------------------------------------------------------- extrwinputs
CONCL4 = sv(LIB.dbconcl('extrwins'))
INNER = '( %s -> %s )' % (POOLB, CONCL4)
w = WH('extrwinputs', 'The five inputs of the extraction loop at windowed scales, for all large n (Lean: extraction_inputsW of ExtractionW.lean).')
w.h('C e. RR'); w.h('; ; ; 1 0 0 0 <_ C'); w.h('E e. RR'); w.h('0 < E'); w.h('E <_ ( 1 / 2 )')
bundle, BT = evitems(w, False)
AQ = '( ph /\\ %s )' % BT
B6, B5, B4, B3, B2, B1, Bf, Bk = levels(AQ)
TAIL = '( %s /\\ %s )' % (COP, POOLB)
D0 = '( %s /\\ %s )' % (Bk, TAIL)
u = unpack(w, D0, Bk, TAIL, AQ, B6, B5, B4, B3, B2, B1, Bf)
st = u['st']
cop = st([u['tl']], 'simpld', COP)
pool = st([u['tl']], 'simprd', POOLB)
hc = hcstep(w, D0, u['phs'], st)
ANTn = st([hc, u['bun'], u['iw']], '3jca', '( %s /\\ %s /\\ %s )' % (HC, HNn, IWn))
qp = st([u['qpw'], u['card']], 'jca', QPn)
kc = st([u['knn'], cop, pool], '3jca', '( k e. NN /\\ %s /\\ %s )' % (COP, POOLB))
az = st([ANTn, qp, kc], '3jca', '( ( %s /\\ %s /\\ %s ) /\\ %s /\\ ( k e. NN /\\ %s /\\ %s ) )' % (HC, HNn, IWn, QPn, COP, POOLB))
core = st([az, w.inst('extrwiw')], 'syl', CONCL4)
x1 = w.s([core], 'ex', '( %s -> ( %s -> %s ) )' % (Bk, TAIL, CONCL4))
x2 = w.s([x1], 'expd', '( %s -> ( %s -> %s ) )' % (Bk, COP, INNER))
Q1 = 'A. k e. NN ( %s -> %s )' % (COP, INNER)
r1 = w.s([x2], 'ralrimiva', '( %s -> %s )' % (Bf, Q1))
x3 = w.s([r1], 'ex', '( %s -> ( %s -> %s ) )' % (B1, CARD, Q1))
Q2 = 'A. q e. ~P %s ( %s -> %s )' % (GWz, CARD, Q1)
r2 = w.s([x3], 'ralrimiva', '( %s -> %s )' % (B2, Q2))
x4 = w.s([r2], 'ex', '( %s -> ( %s -> %s ) )' % (B3, IWn, Q2))
Q3 = 'A. t e. NN0 ( %s -> %s )' % (IWn, Q2)
r3 = w.s([x4], 'ralrimiva', '( %s -> %s )' % (B4, Q3))
Q4 = 'A. y e. NN0 %s' % Q3
r4 = w.s([r3], 'ralrimiva', '( %s -> %s )' % (B5, Q4))
Q5 = 'A. w e. NN0 %s' % Q4
r5 = w.s([r4], 'ralrimiva', '( %s -> %s )' % (B6, Q5))
Q6 = 'A. z e. NN0 %s' % Q5
r6 = w.s([r5], 'ralrimiva', '( %s -> %s )' % (AQ, Q6))
w.qed([bundle, r6], 'evimd', '( ph -> %s )' % EV(Q6))
assert run(w)


# ----------------------------------------------------------------- outwcarm
PRD = 'prod_ j e. s j'
SNE = '( s =/= (/) /\\ %s || ( %s - 1 ) )' % (Lq, PRD)
SBD = '( n < %s /\\ %s <_ ( n x. ( ( xceil ` q ) ^ ( Nstar ` q ) ) ) )' % (PRD, PRD)
SHYP = '( %s /\\ %s )' % (SNE, SBD)
CONCL5 = sv(LIB.dbconcl('outwins'))
w = WH('outwcarm', 'The output of the extraction is a Carmichael number in ( n , n ^ ( 1 + D ) ] at windowed scales, for all large n (Lean: output_carmichaelW of OutputW.lean).')
w.h('C e. RR'); w.h('; ; ; 1 0 0 0 <_ C'); w.h('E e. RR'); w.h('0 < E'); w.h('E <_ ( 1 / 2 )')
w.h('D e. RR'); w.h('0 < D')
bundle, BT = evitems(w, True)
AQ = '( ph /\\ %s )' % BT
B6, B5, B4, B3, B2, B1, Bf, Bk = levels(AQ)
BKC = '( %s /\\ %s )' % (Bk, COP)
Bs = '( %s /\\ s e. ~P %s )' % (BKC, PLq)
D0 = '( %s /\\ %s )' % (Bs, SHYP)
def st(hyps, ref, f):
    return w.s(hyps, ref, '( %s -> %s )' % (D0, f))
bs = st([], 'simpl', Bs)
sh = st([], 'simpr', SHYP)
bkc = st([bs], 'simpld', BKC); spw = st([bs], 'simprd', 's e. ~P %s' % PLq)
bk = st([bkc], 'simpld', Bk); cop = st([bkc], 'simprd', COP)
bf = st([bk], 'simpld', Bf); knn = st([bk], 'simprd', 'k e. NN')
b1 = st([bf], 'simpld', B1); card = st([bf], 'simprd', CARD)
b2 = st([b1], 'simpld', B2); qpw = st([b1], 'simprd', 'q e. ~P %s' % GWz)
b3 = st([b2], 'simpld', B3); iw = st([b2], 'simprd', IWn)
b4 = st([b3], 'simpld', B4)
b5 = st([b4], 'simpld', B5)
b6 = st([b5], 'simpld', B6)
aq = st([b6], 'simpld', AQ)
phs = st([aq], 'simpld', 'ph'); bun = st([aq], 'simprd', BT)
hnn = st([bun], 'simpld', HNn); nx = st([bun], 'simprd', '( %s /\\ %s )' % (N9, N10))
hc = hcstep(w, D0, phs, st)
dd = st([st([phs, w.hyps[5]], 'syl', 'D e. RR'), st([phs, w.hyps[6]], 'syl', '0 < D')], 'jca', '( D e. RR /\\ 0 < D )')
ANTn = '( %s /\\ %s /\\ %s )' % (HC, HNn, IWn)
ant = st([hc, hnn, iw], '3jca', ANTn)
ANTO = '( %s /\\ ( D e. RR /\\ 0 < D ) /\\ ( %s /\\ %s ) )' % (ANTn, N9, N10)
anto = st([ant, dd, nx], '3jca', ANTO)
qp = st([qpw, card], 'jca', QPn)
KC = '( k e. NN /\\ %s )' % COP
kc = st([knn, cop], 'jca', KC)
SH = '( s e. ~P %s /\\ %s /\\ %s )' % (PLq, SNE, SBD)
shh = st([spw, st([sh], 'simpld', SNE), st([sh], 'simprd', SBD)], '3jca', SH)
HS = '( %s /\\ %s /\\ %s )' % (QPn, KC, SH)
hs = st([qp, kc, shh], '3jca', HS)
core = st([st([anto, hs], 'jca', '( %s /\\ %s )' % (ANTO, HS)), w.inst('outwcw')], 'syl', CONCL5)
x1 = w.s([core], 'ex', '( %s -> ( %s -> %s ) )' % (Bs, SHYP, CONCL5))
QS = 'A. s e. ~P %s ( %s -> %s )' % (PLq, SHYP, CONCL5)
r0 = w.s([x1], 'ralrimiva', '( %s -> %s )' % (BKC, QS))
x2 = w.s([r0], 'ex', '( %s -> ( %s -> %s ) )' % (Bk, COP, QS))
Q1 = 'A. k e. NN ( %s -> %s )' % (COP, QS)
r1 = w.s([x2], 'ralrimiva', '( %s -> %s )' % (Bf, Q1))
x3 = w.s([r1], 'ex', '( %s -> ( %s -> %s ) )' % (B1, CARD, Q1))
Q2 = 'A. q e. ~P %s ( %s -> %s )' % (GWz, CARD, Q1)
r2 = w.s([x3], 'ralrimiva', '( %s -> %s )' % (B2, Q2))
x4 = w.s([r2], 'ex', '( %s -> ( %s -> %s ) )' % (B3, IWn, Q2))
Q3 = 'A. t e. NN0 ( %s -> %s )' % (IWn, Q2)
r3 = w.s([x4], 'ralrimiva', '( %s -> %s )' % (B4, Q3))
Q4 = 'A. y e. NN0 %s' % Q3
r4 = w.s([r3], 'ralrimiva', '( %s -> %s )' % (B5, Q4))
Q5 = 'A. w e. NN0 %s' % Q4
r5 = w.s([r4], 'ralrimiva', '( %s -> %s )' % (B6, Q5))
Q6 = 'A. z e. NN0 %s' % Q5
r6 = w.s([r5], 'ralrimiva', '( %s -> %s )' % (AQ, Q6))
w.qed([bundle, r6], 'evimd', '( ph -> %s )' % EV(Q6))
assert run(w)
