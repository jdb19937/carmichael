"""Sortie C0c batch 5: the winding integral of 1 / ( z - P ) around a rectangle."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

WPZ = WP('P')
RP = RE('P'); IP = IM('P')
B1 = PT(RB, IA); A1 = PT(RA, IB)
EDGES = [('A', B1), (B1, 'B'), ('B', A1), (A1, 'A')]

# ---- sub4tel: a four-term regrouping of differences
w = W('sub4tel', 'Exchanging the subtrahends of two differences leaves their sum unchanged.')
A0 = '( ( W e. CC /\\ X e. CC ) /\\ ( Y e. CC /\\ Z e. CC ) )'
wc = w.s([], 'simpll', '( %s -> W e. CC )' % A0); xc = w.s([], 'simplr', '( %s -> X e. CC )' % A0)
yc = w.s([], 'simprl', '( %s -> Y e. CC )' % A0); zc = w.s([], 'simprr', '( %s -> Z e. CC )' % A0)
wy = w.s([wc, yc], 'jca', '( %s -> ( W e. CC /\\ Y e. CC ) )' % A0)
t1 = w.s([wy, w.s([xc, zc], 'jca', '( %s -> ( X e. CC /\\ Z e. CC ) )' % A0), w.inst('addsub4')], 'syl2anc',
         '( %s -> ( ( W + Y ) - ( X + Z ) ) = ( ( W - X ) + ( Y - Z ) ) )' % A0)
t2 = w.s([wy, w.s([zc, xc], 'jca', '( %s -> ( Z e. CC /\\ X e. CC ) )' % A0), w.inst('addsub4')], 'syl2anc',
         '( %s -> ( ( W + Y ) - ( Z + X ) ) = ( ( W - Z ) + ( Y - X ) ) )' % A0)
t3 = w.s([w.s([xc, zc], 'addcomd', '( %s -> ( X + Z ) = ( Z + X ) )' % A0)], 'oveq2d',
         '( %s -> ( ( W + Y ) - ( X + Z ) ) = ( ( W + Y ) - ( Z + X ) ) )' % A0)
w.qed([w.s([t1, t3], 'eqtr3d', '( %s -> ( ( W - X ) + ( Y - Z ) ) = ( ( W + Y ) - ( Z + X ) ) )' % A0), t2], 'eqtrd',
      '( %s -> ( ( W - X ) + ( Y - Z ) ) = ( ( W - Z ) + ( Y - X ) ) )' % A0); run(w)

# ---- rectintwind
INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RP, RP, RB, IA, IP, IP, IB)
w = W('rectintwind', 'The winding integral: the boundary integral of 1 / ( z - P ) around a rectangle with P strictly inside is 2 x. ( _i x. _pi ).')
A0 = '( %s /\\ %s )' % (AB, INT)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
it = w.s([], 'simpr', '( %s -> %s )' % (A0, INT))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lr = w.s([ineq, w.inst('simpll')], 'syl', '( %s -> %s < %s )' % (A0, RA, RP))
rr = w.s([ineq, w.inst('simplr')], 'syl', '( %s -> %s < %s )' % (A0, RP, RB))
li = w.s([ineq, w.inst('simprl')], 'syl', '( %s -> %s < %s )' % (A0, IA, IP))
ri = w.s([ineq, w.inst('simprr')], 'syl', '( %s -> %s < %s )' % (A0, IP, IB))
arr = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
brr = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
air = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
bir = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
prr = w.s([pc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RP))
pir = w.s([pc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IP))
# corner closures and coordinates
ic = closed(w, A0, 'ax-icn', '_i e. CC')
b1c = w.s([w.s([brr], 'recnd', '( %s -> %s e. CC )' % (A0, RB)),
           w.s([ic, w.s([air], 'recnd', '( %s -> %s e. CC )' % (A0, IA))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IA))],
          'addcld', '( %s -> %s e. CC )' % (A0, B1))
a1c = w.s([w.s([arr], 'recnd', '( %s -> %s e. CC )' % (A0, RA)),
           w.s([ic, w.s([bir], 'recnd', '( %s -> %s e. CC )' % (A0, IB))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IB))],
          'addcld', '( %s -> %s e. CC )' % (A0, A1))
reB1 = w.s([brr, air, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, B1, RB))
imB1 = w.s([brr, air, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, B1, IA))
reA1 = w.s([arr, bir, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A0, A1, RA))
imA1 = w.s([arr, bir, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A0, A1, IB))
CCL = {'A': ac, 'B': bc, B1: b1c, A1: a1c}
# the six slit-plane memberships and log closures
def ddim(X, cq, Q, qr, qne):
    """( A0 -> ( X - P ) e. DD ) with ( Im ` X ) = Q and Q =/= ( Im ` P )"""
    E = '( %s - P )' % X
    ec = w.s([CCL[X], pc], 'subcld', '( %s -> %s e. CC )' % (A0, E))
    i1 = w.s([CCL[X], pc, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` %s ) = ( ( Im ` %s ) - %s ) )' % (A0, E, X, IP))
    i2 = w.s([i1, w.s([cq], 'oveq1d', '( %s -> ( ( Im ` %s ) - %s ) = ( %s - %s ) )' % (A0, X, IP, Q, IP))], 'eqtrd',
             '( %s -> ( Im ` %s ) = ( %s - %s ) )' % (A0, E, Q, IP))
    ne = w.s([w.s([qr], 'recnd', '( %s -> %s e. CC )' % (A0, Q)), w.s([pir], 'recnd', '( %s -> %s e. CC )' % (A0, IP)), qne],
             'subne0d', '( %s -> ( %s - %s ) =/= 0 )' % (A0, Q, IP))
    ne2 = w.s([i2, ne], 'eqnetrd', '( %s -> ( Im ` %s ) =/= 0 )' % (A0, E))
    return ec, w.s([ec, ne2, w.inst('elslitim')], 'syl2anc', '( %s -> %s e. %s )' % (A0, E, DD))
def ddre(X, cq, Q, lt, rev):
    """( A0 -> ( X - P ) e. DD ) from ( Re ` P ) < Q, or ( P - X ) e. DD from Q < ( Re ` P )"""
    E = '( P - %s )' % X if rev else '( %s - P )' % X
    ec = w.s([pc, CCL[X]] if rev else [CCL[X], pc], 'subcld', '( %s -> %s e. CC )' % (A0, E))
    if rev:
        r1 = w.s([pc, CCL[X], w.inst('resub')], 'syl2anc', '( %s -> ( Re ` %s ) = ( %s - ( Re ` %s ) ) )' % (A0, E, RP, X))
        r2 = w.s([r1, w.s([cq], 'oveq2d', '( %s -> ( %s - ( Re ` %s ) ) = ( %s - %s ) )' % (A0, RP, X, RP, Q))], 'eqtrd',
                 '( %s -> ( Re ` %s ) = ( %s - %s ) )' % (A0, E, RP, Q))
        DIF = '( %s - %s )' % (RP, Q)
        pos = w.s([lt, w.s([w.s([arr if Q == RA else brr], 'id', '( %s -> %s e. RR )' % (A0, Q)) if False else (arr if Q == RA else brr), prr], 'posdifd',
                           '( %s -> ( %s < %s <-> 0 < %s ) )' % (A0, Q, RP, DIF))], 'mpbid', '( %s -> 0 < %s )' % (A0, DIF))
    else:
        r1 = w.s([CCL[X], pc, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( Re ` %s ) - %s ) )' % (A0, E, X, RP))
        r2 = w.s([r1, w.s([cq], 'oveq1d', '( %s -> ( ( Re ` %s ) - %s ) = ( %s - %s ) )' % (A0, X, RP, Q, RP))], 'eqtrd',
                 '( %s -> ( Re ` %s ) = ( %s - %s ) )' % (A0, E, Q, RP))
        DIF = '( %s - %s )' % (Q, RP)
        pos = w.s([lt, w.s([prr, brr if Q == RB else arr], 'posdifd', '( %s -> ( %s < %s <-> 0 < %s ) )' % (A0, RP, Q, DIF))], 'mpbid',
                  '( %s -> 0 < %s )' % (A0, DIF))
    pos2 = w.s([pos, r2], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A0, E))
    return ec, w.s([ec, pos2, w.inst('elslitre')], 'syl2anc', '( %s -> %s e. %s )' % (A0, E, DD))
ianeip = w.s([air, li], 'ltned', '( %s -> %s =/= %s )' % (A0, IA, IP))
ibneip = w.s([pir, ri], 'gtned', '( %s -> %s =/= %s )' % (A0, IB, IP))
idA = w.s([], 'eqidd', '( %s -> ( Im ` A ) = %s )' % (A0, IA))
idB = w.s([], 'eqidd', '( %s -> ( Im ` B ) = %s )' % (A0, IB))
eqRB = w.s([], 'eqidd', '( %s -> ( Re ` B ) = %s )' % (A0, RB))
eqRA = w.s([], 'eqidd', '( %s -> ( Re ` A ) = %s )' % (A0, RA))
cAP, dAP = ddim('A', idA, IA, air, ianeip)
cB1P, dB1P = ddim(B1, imB1, IA, air, ianeip)
cA1P, dA1P = ddim(A1, imA1, IB, bir, ibneip)
cBP, dBP = ddre('B', eqRB, RB, rr, False)
cPA, dPA = ddre('A', eqRA, RA, lr, True)
cPA1, dPA1 = ddre(A1, reA1, RA, lr, True)
e0 = w.s([], 'eqid', '%s = %s' % (DD, DD))
def logc(E, dst):
    ne = w.s([dst, w.s([e0], 'logdmn0', '( %s e. %s -> %s =/= 0 )' % (E, DD, E))], 'syl', '( %s -> %s =/= 0 )' % (A0, E))
    cl = w.s([w.s([dst, w.inst('eldifi')], 'syl', '( %s -> %s e. CC )' % (A0, E)), ne], 'logcld', '( %s -> %s e. CC )' % (A0, LOG(E)))
    return cl
LA = LOG('( A - P )'); LB1 = LOG('( %s - P )' % B1); LB = LOG('( B - P )'); LA1 = LOG('( %s - P )' % A1)
MA = LOG('( P - A )'); MA1 = LOG('( P - %s )' % A1)
cla = logc('( A - P )', dAP); clb1 = logc('( %s - P )' % B1, dB1P); clb = logc('( B - P )', dBP)
cla1 = logc('( %s - P )' % A1, dA1P); cma = logc('( P - A )', dPA); cma1 = logc('( P - %s )' % A1, dPA1)
# the four edge integrals
def edge1(S, T, geoeq, hypne):
    """csegdd1 + lintlog1 on the horizontal edge from S to T"""
    g = w.s([CCL[S], CCL[T], geoeq], '3jca', '( %s -> ( %s e. CC /\\ %s e. CC /\\ ( Im ` %s ) = ( Im ` %s ) ) )' % (A0, S, T, S, T))
    h = w.s([pc, hypne], 'jca', '( %s -> ( P e. CC /\\ ( Im ` %s ) =/= %s ) )' % (A0, S, IP))
    dd = w.s([g, h, w.inst('csegdd1')], 'syl2anc', '( %s -> A. u e. ( %s cseg %s ) ( u - P ) e. %s )' % (A0, S, T, DD))
    pst = w.s([pc, CCL[S], CCL[T]], '3jca', '( %s -> ( P e. CC /\\ %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
    return w.s([pst, dd, w.inst('lintlog1')], 'syl2anc',
               '( %s -> %s = ( %s - %s ) )' % (A0, LINT(WPZ, S, T), LOG('( %s - P )' % T), LOG('( %s - P )' % S)))
def edge2(S, T, geoeq, hyplt):
    g = w.s([CCL[S], CCL[T], geoeq], '3jca', '( %s -> ( %s e. CC /\\ %s e. CC /\\ ( Re ` %s ) = ( Re ` %s ) ) )' % (A0, S, T, S, T))
    h = w.s([pc, hyplt], 'jca', '( %s -> ( P e. CC /\\ %s < ( Re ` %s ) ) )' % (A0, RP, S))
    dd = w.s([g, h, w.inst('csegdd2')], 'syl2anc', '( %s -> A. u e. ( %s cseg %s ) ( u - P ) e. %s )' % (A0, S, T, DD))
    pst = w.s([pc, CCL[S], CCL[T]], '3jca', '( %s -> ( P e. CC /\\ %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
    return w.s([pst, dd, w.inst('lintlog1')], 'syl2anc',
               '( %s -> %s = ( %s - %s ) )' % (A0, LINT(WPZ, S, T), LOG('( %s - P )' % T), LOG('( %s - P )' % S)))
def edge3(S, T, geoeq, hyplt):
    g = w.s([CCL[S], CCL[T], geoeq], '3jca', '( %s -> ( %s e. CC /\\ %s e. CC /\\ ( Re ` %s ) = ( Re ` %s ) ) )' % (A0, S, T, S, T))
    h = w.s([pc, hyplt], 'jca', '( %s -> ( P e. CC /\\ ( Re ` %s ) < %s ) )' % (A0, S, RP))
    dd = w.s([g, h, w.inst('csegdd3')], 'syl2anc', '( %s -> A. u e. ( %s cseg %s ) ( P - u ) e. %s )' % (A0, S, T, DD))
    pst = w.s([pc, CCL[S], CCL[T]], '3jca', '( %s -> ( P e. CC /\\ %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
    return w.s([pst, dd, w.inst('lintlog2')], 'syl2anc',
               '( %s -> %s = ( %s - %s ) )' % (A0, LINT(WPZ, S, T), LOG('( P - %s )' % T), LOG('( P - %s )' % S)))
imAB1 = w.s([imB1], 'eqcomd', '( %s -> %s = ( Im ` %s ) )' % (A0, IA, B1))
imBA1 = w.s([imA1], 'eqcomd', '( %s -> %s = ( Im ` %s ) )' % (A0, IB, A1))
reB1B = w.s([reB1], 'eqtrd' if False else 'eqtrd', '') if False else None
v1 = edge1('A', B1, imAB1, ianeip)
rpb1 = w.s([rr, imB1], 'breqtrd' if False else 'breqtrrd', '( %s -> %s < ( Re ` %s ) )' % (A0, RP, B1)) if False else \
       w.s([rr, reB1], 'breqtrrd', '( %s -> %s < ( Re ` %s ) )' % (A0, RP, B1))
v2 = edge2(B1, 'B', w.s([reB1], 'eqtrd', '( %s -> ( Re ` %s ) = ( Re ` B ) )' % (A0, B1)) if False else
           w.s([reB1, eqRB], 'eqtr4d', '( %s -> ( Re ` %s ) = ( Re ` B ) )' % (A0, B1)), rpb1)
v3 = edge1('B', A1, imBA1, ibneip)
ra1p = w.s([reA1, lr], 'eqbrtrd', '( %s -> ( Re ` %s ) < %s )' % (A0, A1, RP))
v4 = edge3(A1, 'A', w.s([reA1, eqRA], 'eqtr4d', '( %s -> ( Re ` %s ) = ( Re ` A ) )' % (A0, A1)), ra1p)
# rectintval and the telescoping sum
cx = closed(w, A0, 'cnex', 'CC e. _V')
wpex = w.s([w.s([cx, w.inst('difexg')], 'syl', '( %s -> ( CC \\ { P } ) e. _V )' % A0)], 'mptexd', '( %s -> %s e. _V )' % (A0, WPZ))
rv = w.s([wpex, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT(WPZ, 'A', 'B'), RAW('A', 'B').replace('F lint', WPZ + ' lint')))
X1 = '( %s - %s )' % (LB1, LA); X2 = '( %s - %s )' % (LB, LB1); X3 = '( %s - %s )' % (LA1, LB); X4 = '( %s - %s )' % (MA, MA1)
p1 = w.s([v1, v2], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT(WPZ, *EDGES[0]), LINT(WPZ, *EDGES[1]), X1, X2))
p2 = w.s([v3, v4], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT(WPZ, *EDGES[2]), LINT(WPZ, *EDGES[3]), X3, X4))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, RAW('A', 'B').replace('F lint', WPZ + ' lint'), X1, X2, X3, X4))
tot = w.s([rv, p3], 'eqtrd', '( %s -> %s = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, RINT(WPZ, 'A', 'B'), X1, X2, X3, X4))
# ( X1 + X2 ) = ( LB - LA )
q1 = w.s([clb1, cla], 'addcomd' if False else 'addcomd', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, X1, X2, X2, X1)) if False else \
     w.s([w.s([clb1, cla], 'subcld', '( %s -> %s e. CC )' % (A0, X1)), w.s([clb, clb1], 'subcld', '( %s -> %s e. CC )' % (A0, X2))],
         'addcomd', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, X1, X2, X2, X1))
q2 = w.s([clb, clb1, cla, w.inst('npncan')], 'syl3anc', '( %s -> ( %s + %s ) = ( %s - %s ) )' % (A0, X2, X1, LB, LA))
q3 = w.s([q1, q2], 'eqtrd', '( %s -> ( %s + %s ) = ( %s - %s ) )' % (A0, X1, X2, LB, LA))
Y = '( %s - %s )' % (LB, LA)
r1 = w.s([w.s([q3], 'oveq1d', '( %s -> ( ( %s + %s ) + %s ) = ( %s + %s ) )' % (A0, X1, X2, X3, Y, X3)),
          w.s([w.s([clb, cla], 'subcld', '( %s -> %s e. CC )' % (A0, Y)), w.s([cla1, clb], 'subcld', '( %s -> %s e. CC )' % (A0, X3))],
              'addcomd', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, Y, X3, X3, Y))], 'eqtrd',
         '( %s -> ( ( %s + %s ) + %s ) = ( %s + %s ) )' % (A0, X1, X2, X3, X3, Y))
r2 = w.s([cla1, clb, cla, w.inst('npncan')], 'syl3anc', '( %s -> ( %s + %s ) = ( %s - %s ) )' % (A0, X3, Y, LA1, LA))
r3 = w.s([r1, r2], 'eqtrd', '( %s -> ( ( %s + %s ) + %s ) = ( %s - %s ) )' % (A0, X1, X2, X3, LA1, LA))
Z0 = '( %s - %s )' % (LA1, LA)
# ( ( X1 + X2 ) + ( X3 + X4 ) ) = ( ( ( X1 + X2 ) + X3 ) + X4 )
c12 = w.s([w.s([clb1, cla], 'subcld', '( %s -> %s e. CC )' % (A0, X1)), w.s([clb, clb1], 'subcld', '( %s -> %s e. CC )' % (A0, X2))],
          'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, X1, X2))
c3 = w.s([cla1, clb], 'subcld', '( %s -> %s e. CC )' % (A0, X3))
c4 = w.s([cma, cma1], 'subcld', '( %s -> %s e. CC )' % (A0, X4))
as1 = w.s([w.s([c12, c3, c4], 'addassd', '( %s -> ( ( ( %s + %s ) + %s ) + %s ) = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, X1, X2, X3, X4, X1, X2, X3, X4))],
          'eqcomd', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = ( ( ( %s + %s ) + %s ) + %s ) )' % (A0, X1, X2, X3, X4, X1, X2, X3, X4))
as2 = w.s([r3], 'oveq1d', '( %s -> ( ( ( %s + %s ) + %s ) + %s ) = ( %s + %s ) )' % (A0, X1, X2, X3, X4, Z0, X4))
sum0 = w.s([tot, w.s([as1, as2], 'eqtrd', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = ( %s + %s ) )' % (A0, X1, X2, X3, X4, Z0, X4))],
           'eqtrd', '( %s -> %s = ( %s + %s ) )' % (A0, RINT(WPZ, 'A', 'B'), Z0, X4))
# regroup by sub4tel and evaluate the two jumps
s4 = w.s([w.s([cla1, cla], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, LA1, LA)),
          w.s([cma, cma1], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, MA, MA1)), w.inst('sub4tel')], 'syl2anc',
         '( %s -> ( %s + %s ) = ( ( %s - %s ) + ( %s - %s ) ) )' % (A0, Z0, X4, LA1, MA1, MA, LA))
# ( LA1 - MA1 ) = IPI by clogdif1 at V = ( A1 - P )
na1 = w.s([a1c, pc, w.inst('negsubdi2')], 'syl2anc', '( %s -> -u ( %s - P ) = ( P - %s ) )' % (A0, A1, A1))
imA1P = w.s([a1c, pc, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` ( %s - P ) ) = ( ( Im ` %s ) - %s ) )' % (A0, A1, A1, IP))
imA1P2 = w.s([imA1P, w.s([imA1], 'oveq1d', '( %s -> ( ( Im ` %s ) - %s ) = ( %s - %s ) )' % (A0, A1, IP, IB, IP))], 'eqtrd',
             '( %s -> ( Im ` ( %s - P ) ) = ( %s - %s ) )' % (A0, A1, IB, IP))
posB = w.s([ri, w.s([pir, bir], 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A0, IP, IB, IB, IP))], 'mpbid',
           '( %s -> 0 < ( %s - %s ) )' % (A0, IB, IP))
posA1 = w.s([posB, imA1P2], 'breqtrrd', '( %s -> 0 < ( Im ` ( %s - P ) ) )' % (A0, A1))
j1 = w.s([w.s([dA1P, w.inst('eldifi')], 'syl', '( %s -> ( %s - P ) e. CC )' % (A0, A1)), posA1, w.inst('clogdif1')], 'syl2anc',
         '( %s -> ( %s - %s ) = %s )' % (A0, LA1, LOG('-u ( %s - P )' % A1), IPI))
j1b = w.s([j1, w.s([w.s([na1], 'fveq2d', '( %s -> %s = %s )' % (A0, LOG('-u ( %s - P )' % A1), MA1))], 'oveq2d',
                   '( %s -> ( %s - %s ) = ( %s - %s ) )' % (A0, LA1, LOG('-u ( %s - P )' % A1), LA1, MA1))], 'eqtr3d',
           '( %s -> ( %s - %s ) = %s )' % (A0, LA1, MA1, IPI))
# ( MA - LA ) = IPI by clogdif2 at V = ( A - P )
nna = w.s([ac, pc, w.inst('negsubdi2')], 'syl2anc', '( %s -> -u ( A - P ) = ( P - A ) )' % A0)
imAP = w.s([ac, pc, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` ( A - P ) ) = ( %s - %s ) )' % (A0, IA, IP))
negA = w.s([w.s([air, pir], 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A0, IA, IP, IP, IA)), li], 'mpbid',
           '( %s -> 0 < ( %s - %s ) )' % (A0, IP, IA)) if False else None
ltA = w.s([w.s([air, pir], 'lt0neg1d' if False else 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A0, IA, IP, IP, IA)), li], 'mpbid',
          '( %s -> 0 < ( %s - %s ) )' % (A0, IP, IA))
subneg = w.s([w.s([air, pir], 'sublt0d' if False else 'difrp', '') ] if False else [w.s([air, pir], 'posdifd', '')], 'a1i', '') if False else None
ltA2 = w.s([w.s([air, pir, w.inst('lt0d') if False else w.inst('subgt0')], 'syl2anc', '') ] if False else [], 'a1i', '') if False else None
neg0 = w.s([w.s([air, pir], 'suble0d' if False else 'sublt0d', '( %s -> ( ( %s - %s ) < 0 <-> %s < %s ) )' % (A0, IA, IP, IA, IP)), li], 'mpbird',
           '( %s -> ( %s - %s ) < 0 )' % (A0, IA, IP))
negAP = w.s([imAP, neg0], 'eqbrtrd', '( %s -> ( Im ` ( A - P ) ) < 0 )' % A0)
j2 = w.s([w.s([dAP, w.inst('eldifi')], 'syl', '( %s -> ( A - P ) e. CC )' % A0), negAP, w.inst('clogdif2')], 'syl2anc',
         '( %s -> ( %s - %s ) = %s )' % (A0, LOG('-u ( A - P )'), LA, IPI))
j2b = w.s([j2, w.s([w.s([nna], 'fveq2d', '( %s -> %s = %s )' % (A0, LOG('-u ( A - P )'), MA))], 'oveq1d',
                   '( %s -> ( %s - %s ) = ( %s - %s ) )' % (A0, LOG('-u ( A - P )'), LA, MA, LA))], 'eqtr3d',
           '( %s -> ( %s - %s ) = %s )' % (A0, MA, LA, IPI))
ipc = w.s([ic, closed(w, A0, 'picn', '_pi e. CC')], 'mulcld', '( %s -> %s e. CC )' % (A0, IPI))
fin = w.s([w.s([j1b, j2b], 'oveq12d', '( %s -> ( ( %s - %s ) + ( %s - %s ) ) = ( %s + %s ) )' % (A0, LA1, MA1, MA, LA, IPI, IPI)),
           w.s([w.s([ipc], '2timesd', '( %s -> %s = ( %s + %s ) )' % (A0, TWOPII, IPI, IPI))], 'eqcomd',
               '( %s -> ( %s + %s ) = %s )' % (A0, IPI, IPI, TWOPII))], 'eqtrd',
          '( %s -> ( ( %s - %s ) + ( %s - %s ) ) = %s )' % (A0, LA1, MA1, MA, LA, TWOPII))
w.qed([sum0, w.s([s4, fin], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A0, Z0, X4, TWOPII))], 'eqtrd',
      '( %s -> %s = %s )' % (A0, RINT(WPZ, 'A', 'B'), TWOPII)); run(w)
