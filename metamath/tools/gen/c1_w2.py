"""Sortie C1 section 4: the second winding integral, the boundary integral of
( z - P ) ^ -2 around a rectangle with P strictly inside."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c1_lib import *

INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (
    RA, RE('P'), RE('P'), RB, IA, IM('P'), IM('P'), IB)
CP = '( CC \\ { P } )'
WP2 = '( z e. %s |-> ( 1 / ( ( z - P ) ^ 2 ) ) )' % CP
NWP = '( z e. %s |-> -u ( 1 / ( z - P ) ) )' % CP

# ---- rinvcl, rinv2cl -------------------------------------------------------
for lab, expr, desc in (('rinvcl', '( 1 / ( Z - P ) )', 'The reciprocal of Z - P is a complex number off P.'),
                        ('rinv2cl', '( 1 / ( ( Z - P ) ^ 2 ) )', 'The reciprocal of the square of Z - P is a complex number off P.')):
    w = W(lab, desc)
    A0 = '( P e. CC /\\ Z e. %s )' % CP
    pc = w.s([], 'simpl', '( %s -> P e. CC )' % A0)
    zd = w.s([], 'simpr', '( %s -> Z e. %s )' % (A0, CP))
    ed = w.s([zd, w.inst('eldifsn')], 'sylib', '( %s -> ( Z e. CC /\\ Z =/= P ) )' % A0)
    zc = w.s([ed, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
    zn = w.s([ed, w.inst('simpr')], 'syl', '( %s -> Z =/= P )' % A0)
    sc = w.s([zc, pc], 'subcld', '( %s -> ( Z - P ) e. CC )' % A0)
    sn = w.s([zc, pc, zn], 'subne0d', '( %s -> ( Z - P ) =/= 0 )' % A0)
    if lab == 'rinvcl':
        w.qed([sc, sn], 'reccld', '( %s -> %s e. CC )' % (A0, expr))
    else:
        qc = w.s([sc], 'sqcld', '( %s -> ( ( Z - P ) ^ 2 ) e. CC )' % A0)
        qn = w.s([w.s([sc, w.inst('sqne0')], 'syl', '( %s -> ( ( ( Z - P ) ^ 2 ) =/= 0 <-> ( Z - P ) =/= 0 ) )' % A0), sn],
                 'mpbird', '( %s -> ( ( Z - P ) ^ 2 ) =/= 0 )' % A0)
        w.qed([qc, qn], 'reccld', '( %s -> %s e. CC )' % (A0, expr))
    run1(w)

# ---- dvrinv2 ---------------------------------------------------------------
w = W('dvrinv2', 'The derivative of the negated reciprocal of z - P is the '
      'reciprocal of its square.')
A0 = 'P e. CC'
A1 = '( P e. CC /\\ z e. %s )' % CP
sp = closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
va = w.s([w.inst('rinvcl')], 'mpan2', '( %s -> ( 1 / ( z - P ) ) e. CC )' % A1) if False else \
    w.s([w.s([], 'id', '( %s -> %s )' % (A1, A1)), w.inst('rinvcl')], 'syl', '( %s -> ( 1 / ( z - P ) ) e. CC )' % A1)
vb = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A1, A1)), w.inst('rinv2cl')], 'syl', '( %s -> ( 1 / ( ( z - P ) ^ 2 ) ) e. CC )' % A1)],
         'negcld', '( %s -> -u ( 1 / ( ( z - P ) ^ 2 ) ) e. CC )' % A1)
dv = w.s([], 'dvrinv', '( %s -> ( CC _D ( z e. %s |-> ( 1 / ( z - P ) ) ) ) = ( z e. %s |-> -u ( 1 / ( ( z - P ) ^ 2 ) ) ) )' % (A0, CP, CP))
neg = w.s([sp, va, vb, dv], 'dvmptneg', '( %s -> ( CC _D %s ) = ( z e. %s |-> -u -u ( 1 / ( ( z - P ) ^ 2 ) ) ) )' % (A0, NWP, CP))
nn = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A1, A1)), w.inst('rinv2cl')], 'syl', '( %s -> ( 1 / ( ( z - P ) ^ 2 ) ) e. CC )' % A1)],
         'negnegd', '( %s -> -u -u ( 1 / ( ( z - P ) ^ 2 ) ) = ( 1 / ( ( z - P ) ^ 2 ) ) )' % A1)
mt = w.s([nn], 'mpteq2dva', '( %s -> ( z e. %s |-> -u -u ( 1 / ( ( z - P ) ^ 2 ) ) ) = %s )' % (A0, CP, WP2))
w.qed([neg, mt], 'eqtrd', '( %s -> ( CC _D %s ) = %s )' % (A0, NWP, WP2)); run1(w)

# ---- rinv2f ----------------------------------------------------------------
w = W('rinv2f', 'The negated reciprocal of z - P maps the punctured plane into CC.')
A0 = 'P e. CC'
A1 = '( P e. CC /\\ z e. %s )' % CP
vb = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (A1, A1)), w.inst('rinvcl')], 'syl', '( %s -> ( 1 / ( z - P ) ) e. CC )' % A1)],
         'negcld', '( %s -> -u ( 1 / ( z - P ) ) e. CC )' % A1)
w.qed([vb], 'fmptd', '( %s -> %s : %s --> CC )' % (A0, NWP, CP)); run1(w)

# ---- rinv2cn ---------------------------------------------------------------
w = W('rinv2cn', 'The reciprocal of the square of z - P is continuous off P.')
A0 = '( P e. CC /\\ E C_ %s )' % CP
A1 = '( %s /\\ z e. E )' % A0
pc = w.s([], 'simpl', '( %s -> P e. CC )' % A0)
ess = w.s([], 'simpr', '( %s -> E C_ %s )' % (A0, CP))
rc = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('rinvcnss')], 'syl', '( %s -> ( z e. E |-> ( 1 / ( z - P ) ) ) e. ( E -cn-> CC ) )' % A0)
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
mcn0 = w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))
mcn = w.s([mcn0], 'a1i', '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
prod = w.s([ej, mcn, rc, rc], 'cncfmpt2f', '( %s -> ( z e. E |-> ( ( 1 / ( z - P ) ) x. ( 1 / ( z - P ) ) ) ) e. ( E -cn-> CC ) )' % A0)
# the pointwise identity ( 1 / X ) x. ( 1 / X ) = 1 / ( X ^ 2 )
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
zm = w.s([w.s([ess], 'adantr', '( %s -> E C_ %s )' % (A1, CP)), w.s([], 'simpr', '( %s -> z e. E )' % A1)], 'sseldd', '( %s -> z e. %s )' % (A1, CP))
ed = w.s([zm, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= P ) )' % A1)
zc = w.s([ed, w.inst('simpl')], 'syl', '( %s -> z e. CC )' % A1)
zn = w.s([ed, w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
sc = w.s([zc, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
sn = w.s([zc, pc1, zn], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
one = closed(w, A1, 'ax-1cn', '1 e. CC')
dmd = w.s([one, sc, one, sc, sn, sn], 'divmuldivd', '( %s -> ( ( 1 / ( z - P ) ) x. ( 1 / ( z - P ) ) ) = ( ( 1 x. 1 ) / ( ( z - P ) x. ( z - P ) ) ) )' % A1)
t11 = closed(w, A1, '1t1e1', '( 1 x. 1 ) = 1')
sq = w.s([w.s([sc], 'sqvald', '( %s -> ( ( z - P ) ^ 2 ) = ( ( z - P ) x. ( z - P ) ) )' % A1)], 'eqcomd',
         '( %s -> ( ( z - P ) x. ( z - P ) ) = ( ( z - P ) ^ 2 ) )' % A1)
rw = w.s([dmd, w.s([t11, sq], 'oveq12d', '( %s -> ( ( 1 x. 1 ) / ( ( z - P ) x. ( z - P ) ) ) = ( 1 / ( ( z - P ) ^ 2 ) ) )' % A1)],
         'eqtrd', '( %s -> ( ( 1 / ( z - P ) ) x. ( 1 / ( z - P ) ) ) = ( 1 / ( ( z - P ) ^ 2 ) ) )' % A1)
mt = w.s([rw], 'mpteq2dva', '( %s -> ( z e. E |-> ( ( 1 / ( z - P ) ) x. ( 1 / ( z - P ) ) ) ) = ( z e. E |-> ( 1 / ( ( z - P ) ^ 2 ) ) ) )' % A0)
w.qed([mt, prod], 'eqeltrrd', '( %s -> ( z e. E |-> ( 1 / ( ( z - P ) ^ 2 ) ) ) e. ( E -cn-> CC ) )' % A0); run1(w)

# ---- rectintw2 -------------------------------------------------------------
w = W('rectintw2', 'The boundary integral of the reciprocal of the square of '
      'z - P around a rectangle with P strictly inside is zero: the integrand '
      'has the primitive -u ( 1 / ( z - P ) ) on the punctured plane and the '
      'four edge values telescope.')
A0 = '( %s /\\ %s )' % (AB, INT)
PU = '( ( A crect B ) \\ { P } )'
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
it = w.s([], 'simpr', '( %s -> %s )' % (A0, INT))
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
idst = w.s([], 'id', '( %s -> %s )' % (A0, A0))
frp = w.s([idst, w.inst('crectfrp')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, PU))
crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
pss = w.s([crss], 'ssdifd', '( %s -> %s C_ %s )' % (A0, PU, CP))
frc = w.s([frp, pss], 'sstrd', '( %s -> %s C_ %s )' % (A0, FR, CP))
se = edges4(w, A0, frc, T=CP)
nwpf = w.s([pc, w.inst('rinv2f')], 'syl', '( %s -> %s : %s --> CC )' % (A0, NWP, CP))
dvn = w.s([pc, w.inst('dvrinv2')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, NWP, WP2))
ssi = closed(w, A0, 'ssid', '%s C_ %s' % (CP, CP))
w2cn = w.s([pc, ssi, w.inst('rinv2cn')], 'syl2anc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, WP2, CP))
w2ex = w.s([w2cn, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, WP2))
mid = w.s([nwpf, dvn], 'jca', '( %s -> ( %s : %s --> CC /\\ ( CC _D %s ) = %s ) )' % (A0, NWP, CP, NWP, WP2))
# corner membership in the punctured plane
mem = {}
for i, (S, T) in enumerate(EDGES):
    if S not in mem:
        e1 = w.s([cc[S], cc[T], w.inst('csegid1')], 'syl2anc', '( %s -> %s e. %s )' % (A0, S, SEGS[i]))
        mem[S] = w.s([se[i], e1], 'sseldd', '( %s -> %s e. %s )' % (A0, S, CP))
    if T not in mem:
        e2 = w.s([cc[S], cc[T], w.inst('csegid2')], 'syl2anc', '( %s -> %s e. %s )' % (A0, T, SEGS[i]))
        mem[T] = w.s([se[i], e2], 'sseldd', '( %s -> %s e. %s )' % (A0, T, CP))
g = {}
for X in mem:
    g[X] = w.s([nwpf, mem[X]], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (A0, NWP, X))
ftc = []
for i, (S, T) in enumerate(EDGES):
    h1 = w.s([cc[S], cc[T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
    h3 = w.s([w2cn, se[i]], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, WP2, CP, SEGS[i], CP))
    hh = w.s([h1, mid, h3], '3jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s : %s --> CC /\\ ( CC _D %s ) = %s ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) )' % (
        A0, S, T, NWP, CP, NWP, WP2, WP2, CP, SEGS[i], CP))
    ftc.append(w.s([hh, w.inst('lintftc')], 'syl', '( %s -> %s = ( ( %s ` %s ) - ( %s ` %s ) ) )' % (A0, LINT(WP2, S, T), NWP, T, NWP, S)))
RAWW = '( ( %s + %s ) + ( %s + %s ) )' % tuple(LINT(WP2, s, t) for s, t in EDGES)
rv = w.s([w2ex, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT(WP2, 'A', 'B'), RAWW))
GV = {X: '( %s ` %s )' % (NWP, X) for X in mem}
DIF = ['( %s - %s )' % (GV[T], GV[S]) for S, T in EDGES]
p1 = w.s([ftc[0], ftc[1]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT(WP2, *EDGES[0]), LINT(WP2, *EDGES[1]), DIF[0], DIF[1]))
p2 = w.s([ftc[2], ftc[3]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT(WP2, *EDGES[2]), LINT(WP2, *EDGES[3]), DIF[2], DIF[3]))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, RAWW, DIF[0], DIF[1], DIF[2], DIF[3]))
t1 = w.s([g[P10], g['A'], g['B']], 'npncan3d', '( %s -> ( %s + %s ) = ( %s - %s ) )' % (A0, DIF[0], DIF[1], GV['B'], GV['A']))
t2 = w.s([g[P01], g['B'], g['A']], 'npncan3d', '( %s -> ( %s + %s ) = ( %s - %s ) )' % (A0, DIF[2], DIF[3], GV['A'], GV['B']))
t3 = w.s([t1, t2], 'oveq12d', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = ( ( %s - %s ) + ( %s - %s ) ) )' % (A0, DIF[0], DIF[1], DIF[2], DIF[3], GV['B'], GV['A'], GV['A'], GV['B']))
t4 = w.s([g['B'], g['A'], g['A']], 'npncan3d', '( %s -> ( ( %s - %s ) + ( %s - %s ) ) = ( %s - %s ) )' % (A0, GV['B'], GV['A'], GV['A'], GV['B'], GV['A'], GV['A']))
t5 = w.s([g['A']], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (A0, GV['A'], GV['A']))
w.qed([w.s([w.s([rv, p3], 'eqtrd', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, RINT(WP2, 'A', 'B'), DIF[0], DIF[1], DIF[2], DIF[3])), t3], 'eqtrd',
            '( %s -> %s = ( ( %s - %s ) + ( %s - %s ) ) )' % (A0, RINT(WP2, 'A', 'B'), GV['B'], GV['A'], GV['A'], GV['B'])),
       w.s([t4, t5], 'eqtrd', '( %s -> ( ( %s - %s ) + ( %s - %s ) ) = 0 )' % (A0, GV['B'], GV['A'], GV['A'], GV['B']))],
      'eqtrd', '( %s -> %s = 0 )' % (A0, RINT(WP2, 'A', 'B'))); run1(w)
