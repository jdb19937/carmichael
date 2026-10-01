"""Sortie A2, batch 5: step2wc (the pointwise core of Step2W), step2we (the
eventual package) and step2w (Lean: step2_succeedsW)."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

L2 = '( ell2 ` N )'; L3 = '( ell3 ` N )'
ZR = '( ( C x. %s ) x. %s )' % (L2, L3)
PB = '( ( 4 x. C ) x. %s )' % L3
Q99 = '( ; 9 9 / ; ; 1 0 0 )'
E99 = '( 1 / ; 9 9 )'
AE = '( %s ^c %s )' % (L2, E99)
GPW = '( ( Z goodPrimesW W ) ` Y )'
HG = '( # ` %s )' % GPW
PP = '( ppi ` Z )'
SSX = lambda x: '{ a e. ( 0 ... %s ) | ( a e. Prime /\\ A. q e. Prime ( q || ( a - 1 ) -> q <_ ( %s ^c ( 1 - E ) ) ) ) }' % (x, x)
SMOOTH = 'A. x e. ( ZZ>= ` X ) ( G x. ( ppi ` x ) ) <_ ( # ` %s )' % SSX('x')
CHEB = 'A. u e. ( ZZ>= ` K ) ( u / ( 3 x. ( log ` u ) ) ) <_ ( ppi ` u )'
WIN = '<. <. C , E >. , N >. InWindow <. <. Z , W >. , <. Y , T >. >.'

w = WH('step2wc', 'Step 2 succeeds at windowed scales, pointwise: the reservoir has at least T elements (Lean: the body of step2_succeedsW).')
cr = w.h('C e. RR'); gr = w.h('G e. RR'); er = w.h('E e. RR'); xn0 = w.h('X e. NN0')
g0 = w.h('0 < G'); c60 = w.h('; 6 0 <_ ( C x. G )'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
sm = w.h(SMOOTH)
n3 = w.h('N e. ( ZZ>= ` 3 )'); b16 = w.h('( ; 1 6 x. C ) <_ %s' % L3)
h99 = w.h('%s <_ %s' % (PB, AE))
kn = w.h('K e. NN'); ch = w.h(CHEB)
xk = w.h('( ( X + K ) + 2 ) <_ %s' % ZR)
win = w.h(WIN)
A = 'ph'
# types from the window
ty = w.s([win, w.inst('inwintyp')], 'syl',
         '( %s -> ( ( C e. RR /\\ E e. RR /\\ N e. NN0 ) /\\ ( Z e. NN0 /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) ) )' % A)
zn0 = w.s([w.s([ty], 'simp2d', '( %s -> ( Z e. NN0 /\\ W e. NN0 ) )' % A)], 'simpld', '( %s -> Z e. NN0 )' % A)
wn0 = w.s([w.s([ty], 'simp2d', '( %s -> ( Z e. NN0 /\\ W e. NN0 ) )' % A)], 'simprd', '( %s -> W e. NN0 )' % A)
yn0 = w.s([w.s([ty], 'simp3d', '( %s -> ( Y e. NN0 /\\ T e. NN0 ) )' % A)], 'simpld', '( %s -> Y e. NN0 )' % A)
tn0 = w.s([w.s([ty], 'simp3d', '( %s -> ( Y e. NN0 /\\ T e. NN0 ) )' % A)], 'simprd', '( %s -> T e. NN0 )' % A)
# basic reals
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % A)
ar = w.s([n2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (A, L2))
br = w.s([n3, w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (A, L3))
b3lt = w.s([n3, w.inst('ell3lt')], 'syl', '( %s -> %s < %s )' % (A, L3, L2))
zr = w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)
wr = w.s([wn0], 'nn0red', '( %s -> W e. RR )' % A)
tr = w.s([tn0], 'nn0red', '( %s -> T e. RR )' % A)
xr = w.s([xn0], 'nn0red', '( %s -> X e. RR )' % A)
xg0 = w.s([xn0], 'nn0ge0d', '( %s -> 0 <_ X )' % A)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A)
kg0 = w.s([w.s([kn], 'nnnn0d', '( %s -> K e. NN0 )' % A)], 'nn0ge0d', '( %s -> 0 <_ K )' % A)
crd = cr
LV = {'C': cr, L2: ar, L3: br, 'Z': zr, 'W': wr, 'T': tr, 'X': xr, 'K': kr, ZR: None}
c1 = linarith(w, A, [c1000], '1 <_ C', leaves={'C': cr})
a1 = linarith(w, A, [b16, b3lt, c1000], '1 <_ %s' % L2, leaves={'C': cr, L2: ar, L3: br})
a0 = linarith(w, A, [b16, b3lt, c1000], '0 <_ %s' % L2, leaves={'C': cr, L2: ar, L3: br})
b0 = linarith(w, A, [b16, c1000], '0 < %s' % L3, leaves={'C': cr, L3: br})
# window projections
zlo = w.s([win, w.inst('inwinzlo')], 'syl', '( %s -> %s <_ Z )' % (A, ZR))
zhi = w.s([win, w.inst('inwinzhi')], 'syl', '( %s -> Z <_ ( 4 x. %s ) )' % (A, ZR))
whi = w.s([win, w.inst('inwinwhi')], 'syl', '( %s -> W <_ ( 4 x. ( Z ^c %s ) ) )' % (A, Q99))
ylo = w.s([win, w.inst('inwinylo')], 'syl', '( %s -> ( Z ^c ( 1 - E ) ) <_ Y )' % A)
thi = w.s([win, w.inst('inwinthi')], 'syl', '( %s -> T <_ ( 5 x. %s ) )' % (A, L2))
zrr = w.s([w.s([cr, ar], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (A, L2)), br], 'remulcld', '( %s -> %s e. RR )' % (A, ZR))
LV2 = {'C': cr, L2: ar, L3: br, 'Z': zr, 'X': xr, 'K': kr, ZR: zrr}
xlez = linarith(w, A, [xk, zlo, kg0], 'X <_ Z', leaves=LV2)
klez = linarith(w, A, [xk, zlo, xg0], 'K <_ Z', leaves=LV2)
z1 = linarith(w, A, [xk, zlo, xg0, kg0], '1 < Z', leaves=LV2)
zge1 = linarith(w, A, [xk, zlo, xg0, kg0], '1 <_ Z', leaves=LV2)
zn = w.s([w.s([zn0, zge1], 'jca', '( %s -> ( Z e. NN0 /\\ 1 <_ Z ) )' % A), w.inst('elnnnn0c')], 'sylibr', '( %s -> Z e. NN )' % A)
# the three scale lemmas
logz = w.s([cr, c1, n3, b16, a1, zn, zhi], 's2logz', '( %s -> ( log ` Z ) <_ ( 2 x. %s ) )' % (A, L3))
rpz = w.s([cr, c1, n3, b16, a1, h99, zn0, zhi], 's2rpz', '( %s -> ( Z ^c %s ) <_ %s )' % (A, Q99, L2))
card = w.s([zn0, wn0, yn0, er, gr, ylo, xn0, xlez, sm], 's2card', '( %s -> ( G x. %s ) <_ ( %s + ( W + 1 ) ) )' % (A, PP, HG))
cheb = w.s([cr, gr, ar, br, g0, c60, a0, b0, zn, z1, zlo, logz, kn, klez, ch], 's2cheb',
           '( %s -> ( ; 1 0 x. %s ) <_ ( G x. %s ) )' % (A, L2, PP))
# w <_ 4 ell2 N
q99r = w.s([num.fact(w, Q99, 'RR')], 'a1i', '( %s -> %s e. RR )' % (A, Q99))
zge0 = w.s([zn0], 'nn0ge0d', '( %s -> 0 <_ Z )' % A)
cxr = w.s([zr, zge0, q99r], 'recxpcld', '( %s -> ( Z ^c %s ) e. RR )' % (A, Q99))
w4 = linarith(w, A, [whi, rpz], 'W <_ ( 4 x. %s )' % L2, leaves={'W': wr, L2: ar, '( Z ^c %s )' % Q99: cxr})
# assemble
gfi = w.s([w.s([zn0, wn0, yn0], '3jca', '( %s -> ( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 ) )' % A), w.inst('goodprimeswfi')], 'syl',
          '( %s -> %s e. ( ~P Prime i^i Fin ) )' % (A, GPW))
gfi2 = w.s([w.s([gfi, w.inst('elfpw')], 'sylib', '( %s -> ( %s C_ Prime /\\ %s e. Fin ) )' % (A, GPW, GPW))], 'simprd', '( %s -> %s e. Fin )' % (A, GPW))
hgr = w.s([w.s([gfi2, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (A, HG))], 'nn0red', '( %s -> %s e. RR )' % (A, HG))
ppr = w.s([w.s([zr, w.inst('ppicl')], 'syl', '( %s -> %s e. NN0 )' % (A, PP))], 'nn0red', '( %s -> %s e. RR )' % (A, PP))
gpp = w.s([gr, ppr], 'remulcld', '( %s -> ( G x. %s ) e. RR )' % (A, PP))
linarith(w, A, [cheb, card, w4, thi, a1], 'T <_ %s' % HG,
         leaves={L2: ar, 'T': tr, 'W': wr, HG: hgr, '( G x. %s )' % PP: gpp}, name='qed')
run(w)

# ------------------------------------------------------------------ step2we
l2n = '( ell2 ` n )'; l3n = '( ell3 ` n )'
P1 = 'n e. ( ZZ>= ` 3 )'
P2 = '( ; 1 6 x. C ) <_ %s' % l3n
P3 = '( ( 4 x. C ) x. %s ) <_ ( %s ^c %s )' % (l3n, l2n, E99)
P4 = lambda B: '%s <_ ( ( C x. %s ) x. %s )' % (B, l2n, l3n)
SC = lambda B: '( ( ( %s /\\ %s ) /\\ %s ) /\\ %s )' % (P1, P2, P3, P4(B))

w = W('step2we', 'The scale facts Step 2 needs hold eventually (Lean: the filter_upwards list of step2_succeedsW).')
PH = '( C e. RR /\\ 0 < C /\\ B e. RR )'
cr = w.s([], 'simp1', '( %s -> C e. RR )' % PH)
c0 = w.s([], 'simp2', '( %s -> 0 < C )' % PH)
brr = w.s([], 'simp3', '( %s -> B e. RR )' % PH)
s1 = w.s([w.s([], 'evge3', EV(P1))], 'a1i', '( %s -> %s )' % (PH, EV(P1)))
r16 = w.s([num.fact(w, '; 1 6', 'RR')], 'a1i', '( %s -> ; 1 6 e. RR )' % PH)
c16 = w.s([r16, cr], 'remulcld', '( %s -> ( ; 1 6 x. C ) e. RR )' % PH)
s2 = w.s([c16, w.inst('ell3ge')], 'syl', '( %s -> %s )' % (PH, EV(P2)))
r4 = w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % PH)
c4 = w.s([r4, cr], 'remulcld', '( %s -> ( 4 x. C ) e. RR )' % PH)
c40 = linarith(w, PH, [c0], '0 <_ ( 4 x. C )', leaves={'C': cr})
e99rp = w.s([num.fact(w, E99, 'RR+')], 'a1i', '( %s -> %s e. RR+ )' % (PH, E99))
s3 = w.s([w.s([c4, c40, e99rp], '3jca', '( %s -> ( ( 4 x. C ) e. RR /\\ 0 <_ ( 4 x. C ) /\\ %s e. RR+ ) )' % (PH, E99)),
          w.inst('ell3lecxp')], 'syl', '( %s -> %s )' % (PH, EV(P3)))
s4 = w.s([w.s([cr, c0, brr], '3jca', '( %s -> ( C e. RR /\\ 0 < C /\\ B e. RR ) )' % PH), w.inst('zrealge')], 'syl',
         '( %s -> %s )' % (PH, EV(P4('B'))))
st, tx = evand(w, PH, [s1, s2, s3, s4], [P1, P2, P3, P4('B')])
assert tx == SC('B'), (tx, SC('B'))
w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]
run(w)

# ------------------------------------------------------------------ step2wk
XK = '( ( X + K ) + 2 )'
WINn = '<. <. C , E >. , n >. InWindow <. <. z , w >. , <. y , t >. >.'
GPWn = '( ( z goodPrimesW w ) ` y )'
BODY = '( %s -> t <_ ( # ` %s ) )' % (WINn, GPWn)
Q4 = 'A. z e. NN0 A. w e. NN0 A. y e. NN0 A. t e. NN0 %s' % BODY

w = WH('step2wk', 'Step 2 succeeds at windowed scales, with the Chebyshev threshold K as a parameter.')
cr = w.h('C e. RR'); gr = w.h('G e. RR'); er = w.h('E e. RR'); xn0 = w.h('X e. NN0')
g0 = w.h('0 < G'); c60 = w.h('; 6 0 <_ ( C x. G )'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
sm = w.h(SMOOTH); kn = w.h('K e. NN'); ch = w.h(CHEB)
A = 'ph'
c0 = linarith(w, A, [c1000], '0 < C', leaves={'C': cr})
xr = w.s([xn0], 'nn0red', '( %s -> X e. RR )' % A)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A)
xkr = w.s([w.s([xr, kr], 'readdcld', '( %s -> ( X + K ) e. RR )' % A), w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A)], 'readdcld',
          '( %s -> %s e. RR )' % (A, XK))
src = w.s([w.s([cr, c0, xkr], '3jca', '( %s -> ( C e. RR /\\ 0 < C /\\ %s e. RR ) )' % (A, XK)), w.inst('step2we')], 'syl',
          '( %s -> %s )' % (A, EV(SC(XK))))
AA = '( ph /\\ %s )' % SC(XK)
ph_ = w.s([], 'simpl', '( %s -> ph )' % AA)
sc = w.s([], 'simpr', '( %s -> %s )' % (AA, SC(XK)))
l = w.s([sc], 'simpld', '( %s -> ( ( %s /\\ %s ) /\\ %s ) )' % (AA, P1, P2, P3))
p4 = w.s([sc], 'simprd', '( %s -> %s )' % (AA, P4(XK)))
ll = w.s([l], 'simpld', '( %s -> ( %s /\\ %s ) )' % (AA, P1, P2))
p3 = w.s([l], 'simprd', '( %s -> %s )' % (AA, P3))
p1 = w.s([ll], 'simpld', '( %s -> %s )' % (AA, P1))
p2 = w.s([ll], 'simprd', '( %s -> %s )' % (AA, P2))
BB = '( %s /\\ %s )' % (AA, WINn)
def up(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (BB, f))
hyps = [(cr, 'C e. RR'), (gr, 'G e. RR'), (er, 'E e. RR'), (xn0, 'X e. NN0'), (g0, '0 < G'),
        (c60, '; 6 0 <_ ( C x. G )'), (c1000, '; ; ; 1 0 0 0 <_ C'), (sm, SMOOTH), (kn, 'K e. NN'), (ch, CHEB)]
ups = []
for st, f in hyps:
    ups.append(up(w.s([ph_, st], 'syl', '( %s -> %s )' % (AA, f)) if True else st, f))
u1, u2, u3, u4, u5, u6, u7, u8, u9, u10 = ups
v1 = up(p1, P1); v2 = up(p2, P2); v3 = up(p3, P3); v4 = up(p4, P4(XK))
wn = w.s([], 'simpr', '( %s -> %s )' % (BB, WINn))
core = w.s([u1, u2, u3, u4, u5, u6, u7, u8, v1, v2, v3, u9, u10, v4, wn], 'step2wc',
           '( %s -> t <_ ( # ` %s ) )' % (BB, GPWn))
st_t = w.s([core], 'ex', '( %s -> %s )' % (AA, BODY))
cur = st_t; body = BODY
for v in ('t', 'y', 'w', 'z'):
    ad = w.s([cur], 'adantr', '( ( %s /\\ %s e. NN0 ) -> %s )' % (AA, v, body))
    body = 'A. %s e. NN0 %s' % (v, body)
    cur = w.s([ad], 'ralrimiva', '( %s -> %s )' % (AA, body))
assert body == Q4, (body, Q4)
w.qed([src, cur], 'evimd', '( ph -> %s )' % EV(Q4))
run(w)

# ------------------------------------------------------------------ step2w
CH = lambda v, t: 'A. %s e. ( ZZ>= ` %s ) ( %s / ( 3 x. ( log ` %s ) ) ) <_ ( ppi ` %s )' % (v, t, v, v, v)
w = WH('step2w', 'Lemma 4.1 (Step 2 succeeds) at windowed scales: for n large and any scales in the window, the reservoir of primes q in ( w , z ] with q - 1 smooth up to y has at least T elements (Lean: step2_succeedsW of Step2W.lean).')
cr = w.h('C e. RR'); gr = w.h('G e. RR'); er = w.h('E e. RR'); xn0 = w.h('X e. NN0')
e0 = w.h('0 < E'); eh = w.h('E <_ ( 1 / 2 )'); g0 = w.h('0 < G')
c60 = w.h('; 6 0 <_ ( C x. G )'); c1000 = w.h('; ; ; 1 0 0 0 <_ C'); sm = w.h(SMOOTH)
A = 'ph'
PHI = '( ph /\\ k e. NN /\\ %s )' % CH('u', 'k')
p1 = w.s([], 'simp1', '( %s -> ph )' % PHI)
p2 = w.s([], 'simp2', '( %s -> k e. NN )' % PHI)
p3 = w.s([], 'simp3', '( %s -> %s )' % (PHI, CH('u', 'k')))
def lift(st, f):
    return w.s([p1, st], 'syl', '( %s -> %s )' % (PHI, f))
k1 = lift(cr, 'C e. RR'); k2 = lift(gr, 'G e. RR'); k3 = lift(er, 'E e. RR'); k4 = lift(xn0, 'X e. NN0')
k5 = lift(g0, '0 < G'); k6 = lift(c60, '; 6 0 <_ ( C x. G )'); k7 = lift(c1000, '; ; ; 1 0 0 0 <_ C')
k8 = lift(sm, SMOOTH)
inner = w.s([k1, k2, k3, k4, k5, k6, k7, k8, p2, p3], 'step2wk', '( %s -> %s )' % (PHI, EV(Q4)))
ex = w.s([inner], '3expia', '( ( ph /\\ k e. NN ) -> ( %s -> %s ) )' % (CH('u', 'k'), EV(Q4)))
rl = w.s([ex], 'rexlimdva', '( ph -> ( E. k e. NN %s -> %s ) )' % (CH('u', 'k'), EV(Q4)))
# rename the bound variables of ppilb3: m -> k, z -> u
src = w.s([], 'ppilb3', 'E. m e. NN %s' % CH('z', 'm'))
idz = w.s([], 'id', '( z = u -> z = u )')
cb1, _r = w.wcongr('( z / ( 3 x. ( log ` z ) ) ) <_ ( ppi ` z )', {'z': 'u'}, 'z = u', {'z': idz})
b1 = w.s([cb1], 'cbvralvw', '( %s <-> %s )' % (CH('z', 'm'), CH('u', 'm')))
b1e = w.s([b1], 'rexbii', '( E. m e. NN %s <-> E. m e. NN %s )' % (CH('z', 'm'), CH('u', 'm')))
idm = w.s([], 'id', '( m = k -> m = k )')
cb2, _r2 = w.wcongr(CH('u', 'm'), {'m': 'k'}, 'm = k', {'m': idm})
b2 = w.s([cb2], 'cbvrexvw', '( E. m e. NN %s <-> E. k e. NN %s )' % (CH('u', 'm'), CH('u', 'k')))
src2 = w.s([w.s([src, b1e], 'mpbi', 'E. m e. NN %s' % CH('u', 'm')), b2], 'mpbi', 'E. k e. NN %s' % CH('u', 'k'))
src3 = w.s([src2], 'a1i', '( ph -> E. k e. NN %s )' % CH('u', 'k'))
w.qed([src3, rl], 'mpd', '( ph -> %s )' % EV(Q4))
run(w)
