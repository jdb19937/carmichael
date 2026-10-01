"""Sortie C0b, batch 11: the five-piece grid decomposition of a rectangle
boundary integral around an interior point (rectintgrid)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

RA = RE('A'); RB = RE('B'); IA = IM('A'); IB = IM('B')
XB = '( ( X e. RR /\\ Y e. RR ) /\\ ( %s < X /\\ X <_ Y /\\ Y < %s ) )' % (RA, RB)
YB = '( ( S e. RR /\\ T e. RR ) /\\ ( %s < S /\\ S <_ T /\\ T < %s ) )' % (IA, IB)
A0 = '( %s /\\ %s /\\ %s )' % (PS, XB, YB)
L1 = ('A', PT('X', IB)); R1 = (PT('X', IA), 'B'); M = (PT('X', IA), PT('Y', IB)); R2 = (PT('Y', IA), 'B')
MB = (PT('X', IA), PT('Y', 'S')); MU = (PT('X', 'S'), PT('Y', IB))
MM = (PT('X', 'S'), PT('Y', 'T')); MT = (PT('X', 'T'), PT('Y', IB))
def RI_(P, Q): return '( F rectint <. %s , %s >. )' % (P, Q)

w = W('rectintgrid', 'A rectangle boundary integral decomposes into five pieces around an inner rectangle.')
d = ctx(w, A0)
xb = w.s([], 'simp2', '( %s -> %s )' % (A0, XB))
yb = w.s([], 'simp3', '( %s -> %s )' % (A0, YB))
xr = w.s([w.s([xb, w.inst('simpl')], 'syl', '( %s -> ( X e. RR /\\ Y e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> X e. RR )' % A0)
yr = w.s([w.s([xb, w.inst('simpl')], 'syl', '( %s -> ( X e. RR /\\ Y e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> Y e. RR )' % A0)
sr = w.s([w.s([yb, w.inst('simpl')], 'syl', '( %s -> ( S e. RR /\\ T e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
tr = w.s([w.s([yb, w.inst('simpl')], 'syl', '( %s -> ( S e. RR /\\ T e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> T e. RR )' % A0)
ax = w.s([w.s([xb, w.inst('simpr')], 'syl', '( %s -> ( %s < X /\\ X <_ Y /\\ Y < %s ) )' % (A0, RA, RB)), w.inst('simp1')], 'syl', '( %s -> %s < X )' % (A0, RA))
xy = w.s([w.s([xb, w.inst('simpr')], 'syl', '( %s -> ( %s < X /\\ X <_ Y /\\ Y < %s ) )' % (A0, RA, RB)), w.inst('simp2')], 'syl', '( %s -> X <_ Y )' % A0)
yB = w.s([w.s([xb, w.inst('simpr')], 'syl', '( %s -> ( %s < X /\\ X <_ Y /\\ Y < %s ) )' % (A0, RA, RB)), w.inst('simp3')], 'syl', '( %s -> Y < %s )' % (A0, RB))
as_ = w.s([w.s([yb, w.inst('simpr')], 'syl', '( %s -> ( %s < S /\\ S <_ T /\\ T < %s ) )' % (A0, IA, IB)), w.inst('simp1')], 'syl', '( %s -> %s < S )' % (A0, IA))
st = w.s([w.s([yb, w.inst('simpr')], 'syl', '( %s -> ( %s < S /\\ S <_ T /\\ T < %s ) )' % (A0, IA, IB)), w.inst('simp2')], 'syl', '( %s -> S <_ T )' % A0)
tB = w.s([w.s([yb, w.inst('simpr')], 'syl', '( %s -> ( %s < S /\\ S <_ T /\\ T < %s ) )' % (A0, IA, IB)), w.inst('simp3')], 'syl', '( %s -> T < %s )' % (A0, IB))
# the derived order facts
leax = w.s([d['ar'], xr, ax], 'ltled', '( %s -> %s <_ X )' % (A0, RA))
leyB = w.s([yr, d['br'], yB], 'ltled', '( %s -> Y <_ %s )' % (A0, RB))
leas = w.s([d['ai'], sr, as_], 'ltled', '( %s -> %s <_ S )' % (A0, IA))
letB = w.s([tr, d['bi'], tB], 'ltled', '( %s -> T <_ %s )' % (A0, IB))
xB = w.s([xr, yr, d['br'], xy, yB], 'lelttrd', '( %s -> X < %s )' % (A0, RB))
lexB = w.s([xr, d['br'], xB], 'ltled', '( %s -> X <_ %s )' % (A0, RB))
aY = w.s([d['ar'], xr, yr, ax, xy], 'ltletrd', '( %s -> %s < Y )' % (A0, RA))
leaY = w.s([d['ar'], yr, aY], 'ltled', '( %s -> %s <_ Y )' % (A0, RA))
aB = w.s([d['ar'], xr, d['br'], ax, xB], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))
sB = w.s([sr, tr, d['bi'], st, tB], 'lelttrd', '( %s -> S < %s )' % (A0, IB))
lesB = w.s([sr, d['bi'], sB], 'ltled', '( %s -> S <_ %s )' % (A0, IB))
aT = w.s([d['ai'], sr, tr, as_, st], 'ltletrd', '( %s -> %s < T )' % (A0, IA))
leaT = w.s([d['ai'], tr, aT], 'ltled', '( %s -> %s <_ T )' % (A0, IA))
aI = w.s([d['ai'], sr, d['bi'], as_, sB], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))
# closures of the corner points
ic = closed(w, A0, 'ax-icn', '_i e. CC')
def cnum(v, vr):
    return w.s([vr], 'recnd', '( %s -> %s e. CC )' % (A0, v))
cs = {RA: cnum(RA, d['ar']), RB: cnum(RB, d['br']), IA: cnum(IA, d['ai']), IB: cnum(IB, d['bi']),
      'X': cnum('X', xr), 'Y': cnum('Y', yr), 'S': cnum('S', sr), 'T': cnum('T', tr)}
rl = {RA: d['ar'], RB: d['br'], IA: d['ai'], IB: d['bi'], 'X': xr, 'Y': yr, 'S': sr, 'T': tr}
ptc = {}; ptre = {}; ptim = {}
for (u, v) in [('X', IA), ('X', IB), ('Y', IA), ('Y', IB), ('X', 'S'), ('X', 'T'), ('Y', 'S'), ('Y', 'T'), (RA, 'S'), (RB, 'S')]:
    p = PT(u, v)
    if p in ptc:
        continue
    ptc[p] = w.s([cs[u], w.s([ic, cs[v]], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, v))], 'addcld', '( %s -> %s e. CC )' % (A0, p))
    ptre[p] = w.s([rl[u], rl[v], w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, p, u))
    ptim[p] = w.s([rl[u], rl[v], w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, p, v))
eqid_ = {}
for v, ex in [('A', RA), ('B', RB)]:
    eqid_[(v, 'Re')] = w.s([], 'eqidd', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (A0, v, v))
    eqid_[(v, 'Im')] = w.s([], 'eqidd', '( %s -> ( Im ` %s ) = ( Im ` %s ) )' % (A0, v, v))
lid = {RA: w.s([d['ar']], 'leidd', '( %s -> %s <_ %s )' % (A0, RA, RA)), RB: w.s([d['br']], 'leidd', '( %s -> %s <_ %s )' % (A0, RB, RB)),
       IA: w.s([d['ai']], 'leidd', '( %s -> %s <_ %s )' % (A0, IA, IA)), IB: w.s([d['bi']], 'leidd', '( %s -> %s <_ %s )' % (A0, IB, IB))}
CCS = {'A': d['ac'], 'B': d['bc']}
CCS.update(ptc)
RS = {'A': (RA, IA), 'B': (RB, IB)}
for p in ptc:
    pass


def coords(P):
    if P == 'A':
        return eqid_[('A', 'Re')], eqid_[('A', 'Im')]
    if P == 'B':
        return eqid_[('B', 'Re')], eqid_[('B', 'Im')]
    return ptre[P], ptim[P]


def mkps(P, Q, leR, leI, loR, hiR, loI, hiI):
    sRP, sIP = coords(P); sRQ, sIQ = coords(Q)
    return psub(w, A0, d, P, Q, CCS[P], CCS[Q], sRP, sIP, sRQ, sIQ, leR, leI, loR, hiR, loI, hiI)
leaI = w.s([d['ai'], d['bi'], aI], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))
psAB = w.s([d['ab'], d['geo'], w.s([d['fcn'], d['rss']], 'jca', '( %s -> %s )' % (A0, FCN))], '3jca', '( %s -> %s )' % (A0, PS))
psR1 = mkps(R1[0], R1[1], lexB, leaI, leax, lid[RB], lid[IA], lid[IB])
psM = mkps(M[0], M[1], xy, leaI, leax, leyB, lid[IA], lid[IB])
psMU = mkps(MU[0], MU[1], xy, lesB, leax, leyB, leas, lid[IB])


def inicc(V, vr, lo, hi, lor, hir, lelo, lehi):
    """( A0 -> V e. ( lo [,] hi ) )"""
    return w.s([w.s([lor, hir, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, V, lo, hi, V, lo, V, V, hi)),
                w.s([vr, lelo, lehi], '3jca', '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (A0, V, lo, V, V, hi))], 'mpbird', '( %s -> %s e. ( %s [,] %s ) )' % (A0, V, lo, hi))


# --- split 1: the vertical cut at X
xicc = inicc('X', xr, RA, RB, d['ar'], d['br'], leax, lexB)
sp1 = w.s([psAB, aB, xicc, w.inst('rectinthspx')], 'syl3anc', '( %s -> %s = ( %s + %s ) )' % (A0, RI_('A', 'B'), RI_(*L1), RI_(*R1)))
# --- split 2: the vertical cut of the right part at Y
reR = ptre[R1[0]]; imR = ptim[R1[0]]
ltR = w.s([xB, reR, eqid_[('B', 'Re')]], '3brtr4d', '( %s -> ( Re ` %s ) < ( Re ` B ) )' % (A0, R1[0]))
yicc0 = inicc('Y', yr, RA, RB, d['ar'], d['br'], leaY, leyB)
yicc = w.s([w.s([w.s([reR, eqid_[('B', 'Re')]], 'oveq12d', '( %s -> ( ( Re ` %s ) [,] ( Re ` B ) ) = ( X [,] %s ) )' % (A0, R1[0], RB))], 'eqcomd', '( %s -> ( X [,] %s ) = ( ( Re ` %s ) [,] ( Re ` B ) ) )' % (A0, RB, R1[0])),
             inicc('Y', yr, 'X', RB, xr, d['br'], xy, leyB)], 'id' if False else 'id', 'x')
w.lines.pop()
yiX = inicc('Y', yr, 'X', RB, xr, d['br'], xy, leyB)
yicc = w.s([yiX, w.s([reR, eqid_[('B', 'Re')]], 'oveq12d', '( %s -> ( ( Re ` %s ) [,] ( Re ` B ) ) = ( X [,] %s ) )' % (A0, R1[0], RB))], 'eleqtrrd', '( %s -> Y e. ( ( Re ` %s ) [,] ( Re ` B ) ) )' % (A0, R1[0]))
RAW2 = '( ( F rectint <. %s , %s >. ) + ( F rectint <. %s , B >. ) )' % (R1[0], PT('Y', '( Im ` B )'), PT('Y', '( Im ` %s )' % R1[0]))
sp2r = w.s([psR1, ltR, yicc, w.inst('rectinthspx')], 'syl3anc', '( %s -> %s = %s )' % (A0, RI_(*R1), RAW2))
rw2a = w.s([w.s([imR], 'oveq2d', '( %s -> ( _i x. ( Im ` %s ) ) = ( _i x. %s ) )' % (A0, R1[0], IA))], 'oveq2d', '( %s -> %s = %s )' % (A0, PT('Y', '( Im ` %s )' % R1[0]), PT('Y', IA)))
rw2 = w.s([w.s([w.s([rw2a], 'opeq1d', '( %s -> <. %s , B >. = <. %s , B >. )' % (A0, PT('Y', '( Im ` %s )' % R1[0]), R2[0]))], 'oveq2d',
                '( %s -> ( F rectint <. %s , B >. ) = %s )' % (A0, PT('Y', '( Im ` %s )' % R1[0]), RI_(*R2)))], 'oveq2d',
           '( %s -> %s = ( %s + %s ) )' % (A0, RAW2, RI_(*M), RI_(*R2)))
sp2 = w.s([sp2r, rw2], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (A0, RI_(*R1), RI_(*M), RI_(*R2)))
# --- split 3: the horizontal cut of the middle column at S
ltM = w.s([aI, ptim[M[0]], ptim[M[1]]], '3brtr4d', '( %s -> ( Im ` %s ) < ( Im ` %s ) )' % (A0, M[0], M[1]))
sIA = inicc('S', sr, IA, IB, d['ai'], d['bi'], leas, lesB)
sicc = w.s([sIA, w.s([ptim[M[0]], ptim[M[1]]], 'oveq12d', '( %s -> ( ( Im ` %s ) [,] ( Im ` %s ) ) = ( %s [,] %s ) )' % (A0, M[0], M[1], IA, IB))], 'eleqtrrd', '( %s -> S e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A0, M[0], M[1]))
RAW3 = '( ( F rectint <. %s , %s >. ) + ( F rectint <. %s , %s >. ) )' % (M[0], PT('( Re ` %s )' % M[1], 'S'), PT('( Re ` %s )' % M[0], 'S'), M[1])
sp3r = w.s([psM, ltM, sicc, w.inst('rectintvspx')], 'syl3anc', '( %s -> %s = %s )' % (A0, RI_(*M), RAW3))
rw3a = w.s([ptre[M[1]]], 'oveq1d', '( %s -> %s = %s )' % (A0, PT('( Re ` %s )' % M[1], 'S'), PT('Y', 'S')))
rw3b = w.s([ptre[M[0]]], 'oveq1d', '( %s -> %s = %s )' % (A0, PT('( Re ` %s )' % M[0], 'S'), PT('X', 'S')))
rw3 = w.s([w.s([w.s([rw3a], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, M[0], PT('( Re ` %s )' % M[1], 'S'), MB[0], MB[1]))], 'oveq2d', '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (A0, M[0], PT('( Re ` %s )' % M[1], 'S'), RI_(*MB))),
           w.s([w.s([rw3b], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, PT('( Re ` %s )' % M[0], 'S'), M[1], MU[0], MU[1]))], 'oveq2d', '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (A0, PT('( Re ` %s )' % M[0], 'S'), M[1], RI_(*MU)))], 'oveq12d',
          '( %s -> %s = ( %s + %s ) )' % (A0, RAW3, RI_(*MB), RI_(*MU)))
sp3 = w.s([sp3r, rw3], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (A0, RI_(*M), RI_(*MB), RI_(*MU)))
# --- split 4: the horizontal cut of the upper middle at T
ltU = w.s([sB, ptim[MU[0]], ptim[MU[1]]], '3brtr4d', '( %s -> ( Im ` %s ) < ( Im ` %s ) )' % (A0, MU[0], MU[1]))
tIS = inicc('T', tr, 'S', IB, sr, d['bi'], st, letB)
ticc = w.s([tIS, w.s([ptim[MU[0]], ptim[MU[1]]], 'oveq12d', '( %s -> ( ( Im ` %s ) [,] ( Im ` %s ) ) = ( S [,] %s ) )' % (A0, MU[0], MU[1], IB))], 'eleqtrrd', '( %s -> T e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A0, MU[0], MU[1]))
RAW4 = '( ( F rectint <. %s , %s >. ) + ( F rectint <. %s , %s >. ) )' % (MU[0], PT('( Re ` %s )' % MU[1], 'T'), PT('( Re ` %s )' % MU[0], 'T'), MU[1])
sp4r = w.s([psMU, ltU, ticc, w.inst('rectintvspx')], 'syl3anc', '( %s -> %s = %s )' % (A0, RI_(*MU), RAW4))
rw4a = w.s([ptre[MU[1]]], 'oveq1d', '( %s -> %s = %s )' % (A0, PT('( Re ` %s )' % MU[1], 'T'), PT('Y', 'T')))
rw4b = w.s([ptre[MU[0]]], 'oveq1d', '( %s -> %s = %s )' % (A0, PT('( Re ` %s )' % MU[0], 'T'), PT('X', 'T')))
rw4 = w.s([w.s([w.s([rw4a], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, MU[0], PT('( Re ` %s )' % MU[1], 'T'), MM[0], MM[1]))], 'oveq2d', '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (A0, MU[0], PT('( Re ` %s )' % MU[1], 'T'), RI_(*MM))),
           w.s([w.s([rw4b], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, PT('( Re ` %s )' % MU[0], 'T'), MU[1], MT[0], MT[1]))], 'oveq2d', '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (A0, PT('( Re ` %s )' % MU[0], 'T'), MU[1], RI_(*MT)))], 'oveq12d',
          '( %s -> %s = ( %s + %s ) )' % (A0, RAW4, RI_(*MM), RI_(*MT)))
sp4 = w.s([sp4r, rw4], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (A0, RI_(*MU), RI_(*MM), RI_(*MT)))
# --- assemble
m3 = w.s([sp3, w.s([sp4], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + ( %s + %s ) ) )' % (A0, RI_(*MB), RI_(*MU), RI_(*MB), RI_(*MM), RI_(*MT)))], 'eqtrd',
         '( %s -> %s = ( %s + ( %s + %s ) ) )' % (A0, RI_(*M), RI_(*MB), RI_(*MM), RI_(*MT)))
r1e = w.s([sp2, w.s([m3], 'oveq1d', '( %s -> ( %s + %s ) = ( ( %s + ( %s + %s ) ) + %s ) )' % (A0, RI_(*M), RI_(*R2), RI_(*MB), RI_(*MM), RI_(*MT), RI_(*R2)))], 'eqtrd',
          '( %s -> %s = ( ( %s + ( %s + %s ) ) + %s ) )' % (A0, RI_(*R1), RI_(*MB), RI_(*MM), RI_(*MT), RI_(*R2)))
w.qed([sp1, w.s([r1e], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + ( ( %s + ( %s + %s ) ) + %s ) ) )' % (A0, RI_(*L1), RI_(*R1), RI_(*L1), RI_(*MB), RI_(*MM), RI_(*MT), RI_(*R2)))], 'eqtrd',
      '( %s -> %s = ( %s + ( ( %s + ( %s + %s ) ) + %s ) ) )' % (A0, RI_('A', 'B'), RI_(*L1), RI_(*MB), RI_(*MM), RI_(*MT), RI_(*R2)))
run(w)
