"""C7, Gamma block 1: the polynomial-times-exponential bound and the affine
exponential integral on a general interval (efge1p2, pol2exp, cxpaffdv2,
cxpaffcn2, cxpaffibl2, cxpaffitg2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq, nlinarith

# ---------------------------------------------------------------- efge1p2
A0 = '( A e. RR /\\ 0 <_ A )'
G = '( ( 1 + A ) + ( ( A ^ 2 ) / 2 ) ) <_ ( exp ` A )'
G0 = '( ( 1 + 0 ) + ( ( 0 ^ 2 ) / 2 ) ) <_ ( exp ` 0 )'
w = W('efge1p2', 'The second-order Taylor lower bound on the exponential, nonstrict '
      'and at every nonnegative argument: ~ efgt1p2 with the case ` A = 0 ` added.')
ar = w.s([], 'simpl', '( %s -> A e. RR )' % A0)
a0 = w.s([], 'simpr', '( %s -> 0 <_ A )' % A0)
# the case 0 < A
A1 = '( A e. RR /\\ 0 < A )'
arp = w.s([w.s([], 'simpl', '( %s -> A e. RR )' % A1), w.s([], 'simpr', '( %s -> 0 < A )' % A1)], 'elrpd', '( %s -> A e. RR+ )' % A1)
lt = w.s([arp, w.inst('efgt1p2')], 'syl', '( %s -> ( ( 1 + A ) + ( ( A ^ 2 ) / 2 ) ) < ( exp ` A ) )' % A1)
ar1 = w.s([], 'simpl', '( %s -> A e. RR )' % A1)
lr = w.s([w.s([a1(w, A1, '1re', '1 e. RR'), ar1], 'readdcld', '( %s -> ( 1 + A ) e. RR )' % A1),
          w.s([w.s([ar1], 'resqcld', '( %s -> ( A ^ 2 ) e. RR )' % A1)], 'rehalfcld', '( %s -> ( ( A ^ 2 ) / 2 ) e. RR )' % A1)], 'readdcld',
         '( %s -> ( ( 1 + A ) + ( ( A ^ 2 ) / 2 ) ) e. RR )' % A1)
c1 = w.s([lr, w.s([ar1], 'reefcld', '( %s -> ( exp ` A ) e. RR )' % A1), lt], 'ltled', '( %s -> %s )' % (A1, G))
c1e = w.s([w.s([c1], 'ex', '( A e. RR -> ( 0 < A -> %s ) )' % G)], 'adantr', '( %s -> ( 0 < A -> %s ) )' % (A0, G))
# the case A = 0
s1 = w.s([], 'oveq2', '( A = 0 -> ( 1 + A ) = ( 1 + 0 ) )')
s2 = w.s([w.s([], 'oveq1', '( A = 0 -> ( A ^ 2 ) = ( 0 ^ 2 ) )')], 'oveq1d', '( A = 0 -> ( ( A ^ 2 ) / 2 ) = ( ( 0 ^ 2 ) / 2 ) )')
s3 = w.s([s1, s2], 'oveq12d', '( A = 0 -> ( ( 1 + A ) + ( ( A ^ 2 ) / 2 ) ) = ( ( 1 + 0 ) + ( ( 0 ^ 2 ) / 2 ) ) )')
s4 = w.s([], 'fveq2', '( A = 0 -> ( exp ` A ) = ( exp ` 0 ) )')
sb = w.s([s3, s4], 'breq12d', '( A = 0 -> ( %s <-> %s ) )' % (G, G0))
z1 = w.s([w.s([], 'sq0', '( 0 ^ 2 ) = 0')], 'oveq1i', '( ( 0 ^ 2 ) / 2 ) = ( 0 / 2 )')
z2 = w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0'), w.inst('div0')], 'mp2an', '( 0 / 2 ) = 0')
z3 = w.s([w.s([z1, z2], 'eqtri', '( ( 0 ^ 2 ) / 2 ) = 0')], 'oveq2i', '( ( 1 + 0 ) + ( ( 0 ^ 2 ) / 2 ) ) = ( ( 1 + 0 ) + 0 )')
p1 = w.s([], '1p0e1', '( 1 + 0 ) = 1')
z4 = w.s([w.s([p1], 'oveq1i', '( ( 1 + 0 ) + 0 ) = ( 1 + 0 )'), p1], 'eqtri', '( ( 1 + 0 ) + 0 ) = 1')
z5 = w.s([z3, z4], 'eqtri', '( ( 1 + 0 ) + ( ( 0 ^ 2 ) / 2 ) ) = 1')
e0 = w.s([], 'ef0', '( exp ` 0 ) = 1')
g0a = w.s([z5, w.s([], '1le1', '1 <_ 1')], 'eqbrtri', '( ( 1 + 0 ) + ( ( 0 ^ 2 ) / 2 ) ) <_ 1')
g0 = w.s([g0a, w.s([e0], 'eqcomi', '1 = ( exp ` 0 )')], 'breqtri', G0)
c2 = w.s([g0, sb], 'mpbiri', '( A = 0 -> %s )' % G)
c2e = w.s([w.s([c2], 'eqcoms', '( 0 = A -> %s )' % G)], 'a1i', '( %s -> ( 0 = A -> %s ) )' % (A0, G))
# the case split
bi = w.s([a1(w, A0, '0re', '0 e. RR'), ar, w.inst('leloe')], 'syl2anc', '( %s -> ( 0 <_ A <-> ( 0 < A \\/ 0 = A ) ) )' % A0)
cs = w.s([a0, bi], 'mpbid', '( %s -> ( 0 < A \\/ 0 = A ) )' % A0)
w.qed([cs, w.s([c1e, c2e], 'jaod', '( %s -> ( ( 0 < A \\/ 0 = A ) -> %s ) )' % (A0, G))], 'mpd', '( %s -> %s )' % (A0, G))
run7(w)

# ---------------------------------------------------------------- pol2exp
A0 = '( W e. RR /\\ 0 <_ W )'
L2 = '( log ` 2 )'
Y = '( ( W / 4 ) x. %s )' % L2
EX = '( exp ` %s )' % Y
E = '( 2 ^c ( W / 4 ) )'
F = '( 2 ^c -u ( W / 4 ) )'
Q = '( ( 1 + W ) ^ 2 )'
C128 = '; ; 1 2 8'
w = W('pol2exp', 'The quadratic weight against the exponential decay at half the rate: '
      '` ( 1 + W ) ^ 2 x. 2 ^c -u ( W / 2 ) <_ 128 x. 2 ^c -u ( W / 4 ) ` for ` W >_ 0 `, '
      'by ~ efge1p2 at ` ( W / 4 ) log 2 ` and ` 1 / 2 <_ log 2 ` ( ~ log2ge ).  The '
      'line-moment majorant of ~ gamlmom .')
wr = w.s([], 'simpl', '( %s -> W e. RR )' % A0)
w0 = w.s([], 'simpr', '( %s -> 0 <_ W )' % A0)
cl = Closure(w, A0, {'W': ('RR', wr)})
cl.have('W', 'ge0', w0)
l2r = w.s([a1(w, A0, '2rp', '2 e. RR+'), w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, L2))
cl.leaf(L2, 'RR', l2r)
l2ge = a1(w, A0, 'log2ge', '( 1 / 2 ) <_ %s' % L2)
yr = cl.mem(Y, 'RR')
yge = nlinarith(w, A0, [w0, l2ge], '( W / 8 ) <_ %s' % Y, closure=cl)
w4 = linarith(w, A0, [w0], '0 <_ ( W / 4 )', closure=cl)
l20 = linarith(w, A0, [l2ge], '0 <_ %s' % L2, closure=cl)
y0 = w.s([cl.mem('( W / 4 )', 'RR'), l2r, w4, l20], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, Y))
cl.atom(Y)
tay = w.s([w.s([yr, y0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A0, Y, Y)), w.inst('efge1p2')], 'syl',
          '( %s -> ( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ %s )' % (A0, Y, Y, EX))
exr = w.s([yr], 'reefcld', '( %s -> %s e. RR )' % (A0, EX))
cl.leaf(EX, 'RR', exr)
qle = nlinarith(w, A0, [yge, w0, tay], '%s <_ ( %s x. %s )' % (Q, C128, EX), closure=cl)
# exp Y = 2 ^c ( W / 4 )
c2 = a1(w, A0, '2cn', '2 e. CC'); n2 = a1(w, A0, '2ne0', '2 =/= 0')
w4c = w.s([cl.mem('( W / 4 )', 'RR')], 'recnd', '( %s -> ( W / 4 ) e. CC )' % A0)
cef = w.s([c2, n2, w4c, w.inst('cxpef')], 'syl3anc', '( %s -> %s = %s )' % (A0, E, EX))
qle2 = w.s([qle, w.s([w.s([cef], 'eqcomd', '( %s -> %s = %s )' % (A0, EX, E))], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, C128, EX, C128, E))],
           'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (A0, Q, C128, E))
erp = w.s([a1(w, A0, '2rp', '2 e. RR+'), cl.mem('( W / 4 )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, E))
frp = w.s([a1(w, A0, '2rp', '2 e. RR+'), w.s([cl.mem('( W / 4 )', 'RR')], 'renegcld', '( %s -> -u ( W / 4 ) e. RR )' % A0)], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, F))
fe = w.s([c2, n2, w4c, w.inst('cxpneg')], 'syl3anc', '( %s -> %s = ( 1 / %s ) )' % (A0, F, E))
# 2 ^c -u ( W / 2 ) = F x. F
nw = lineq(w, A0, '-u ( W / 2 )', '( -u ( W / 4 ) + -u ( W / 4 ) )', closure=cl)
nw4c = w.s([w4c], 'negcld', '( %s -> -u ( W / 4 ) e. CC )' % A0)
cad = w.s([w.s([c2, n2], 'jca', '( %s -> ( 2 e. CC /\\ 2 =/= 0 ) )' % A0), nw4c, nw4c, w.inst('cxpadd')], 'syl3anc',
          '( %s -> ( 2 ^c ( -u ( W / 4 ) + -u ( W / 4 ) ) ) = ( %s x. %s ) )' % (A0, F, F))
ff = w.s([w.s([nw], 'oveq2d', '( %s -> ( 2 ^c -u ( W / 2 ) ) = ( 2 ^c ( -u ( W / 4 ) + -u ( W / 4 ) ) ) )' % A0), cad], 'eqtrd',
         '( %s -> ( 2 ^c -u ( W / 2 ) ) = ( %s x. %s ) )' % (A0, F, F))
# ( Q x. F ) <_ 128
qr = cl.mem(Q, 'RR'); qc = w.s([qr], 'recnd', '( %s -> %s e. CC )' % (A0, Q))
ec = w.s([erp], 'rpcnd', '( %s -> %s e. CC )' % (A0, E)); ene = w.s([erp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, E))
qf = w.s([w.s([fe], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( 1 / %s ) ) )' % (A0, Q, F, Q, E)),
          w.s([w.s([qc, ec, ene], 'divrecd', '( %s -> ( %s / %s ) = ( %s x. ( 1 / %s ) ) )' % (A0, Q, E, Q, E))], 'eqcomd', '( %s -> ( %s x. ( 1 / %s ) ) = ( %s / %s ) )' % (A0, Q, E, Q, E))],
         'eqtrd', '( %s -> ( %s x. %s ) = ( %s / %s ) )' % (A0, Q, F, Q, E))
r128 = w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '%s e. NN0' % C128)
r128r = w.s([w.s([r128], 'nn0rei', '%s e. RR' % C128)], 'a1i', '( %s -> %s e. RR )' % (A0, C128))
ldm = w.s([qr, r128r, w.s([w.s([erp], 'rpred', '( %s -> %s e. RR )' % (A0, E)), w.s([erp], 'rpgt0d', '( %s -> 0 < %s )' % (A0, E))], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, E, E)), w.inst('ledivmul')], 'syl3anc',
          '( %s -> ( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) ) )' % (A0, Q, E, C128, Q, E, C128))
qle3 = w.s([qle2, w.s([ec, w.s([r128r], 'recnd', '( %s -> %s e. CC )' % (A0, C128))], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, E, C128, C128, E))], 'breqtrrd',
           '( %s -> %s <_ ( %s x. %s ) )' % (A0, Q, E, C128))
qle4 = w.s([qle3, ldm], 'mpbird', '( %s -> ( %s / %s ) <_ %s )' % (A0, Q, E, C128))
qfle = w.s([qf, qle4], 'eqbrtrd', '( %s -> ( %s x. %s ) <_ %s )' % (A0, Q, F, C128))
fr = w.s([frp], 'rpred', '( %s -> %s e. RR )' % (A0, F)); fc = w.s([fr], 'recnd', '( %s -> %s e. CC )' % (A0, F))
fin = w.s([w.s([qr, fr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, Q, F)), r128r, fr, w.s([frp], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, F)), qfle], 'lemul1ad',
          '( %s -> ( ( %s x. %s ) x. %s ) <_ ( %s x. %s ) )' % (A0, Q, F, F, C128, F))
lhs = w.s([w.s([ff], 'oveq2d', '( %s -> ( %s x. ( 2 ^c -u ( W / 2 ) ) ) = ( %s x. ( %s x. %s ) ) )' % (A0, Q, Q, F, F)),
           w.s([w.s([qc, fc, fc], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) ) )' % (A0, Q, F, F, Q, F, F))], 'eqcomd', '( %s -> ( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s ) )' % (A0, Q, F, F, Q, F, F))],
          'eqtrd', '( %s -> ( %s x. ( 2 ^c -u ( W / 2 ) ) ) = ( ( %s x. %s ) x. %s ) )' % (A0, Q, Q, F, F))
w.qed([lhs, fin], 'eqbrtrd', '( %s -> ( %s x. ( 2 ^c -u ( W / 2 ) ) ) <_ ( %s x. %s ) )' % (A0, Q, C128, F))
run7(w)

# ---------------------------------------------------------------- cxpaffdv2
X = '( A (,) B )'
XC = '( A [,] B )'
L = '( log ` U )'
KL = '( K x. %s )' % L
TOP = '( TopOpen ` CCfld )'
JR = '( %s |`t RR )' % TOP


def EK(u):
    return '( U ^c ( K x. %s ) )' % u


A0 = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( ( K e. RR /\\ K =/= 0 ) /\\ ( A e. RR /\\ B e. RR ) ) )'
w = W('cxpaffdv2', 'The derivative of ` ( U ^c ( K x. u ) ) / ( K log U ) ` on an open '
      'interval is ` U ^c ( K x. u ) `: ~ cxpaffdv with a slope and a general '
      'interval, by ~ dvcxp2 and ~ dvmptco .  The primitive of the line-moment tails.')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0)
une = w.s([], 'simplr', '( %s -> U =/= 1 )' % A0)
kr = w.s([], 'simprll', '( %s -> K e. RR )' % A0)
kne = w.s([], 'simprlr', '( %s -> K =/= 0 )' % A0)
kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
lr = w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, L))
lc = w.s([lr], 'recnd', '( %s -> %s e. CC )' % (A0, L))
lne = w.s([urp, une, w.inst('logne0')], 'syl2anc', '( %s -> %s =/= 0 )' % (A0, L))
klc = w.s([kc, lc], 'mulcld', '( %s -> %s e. CC )' % (A0, KL))
klne = w.s([kc, lc, kne, lne], 'mulne0d', '( %s -> %s =/= 0 )' % (A0, KL))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0)
jeq = w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)
xopn = w.s([w.s([w.s([], 'iooretop', '%s e. ( topGen ` ran (,) )' % X)], 'a1i', '( %s -> %s e. ( topGen ` ran (,) ) )' % (A0, X)),
            w.s([jeq], 'a1i', '( %s -> ( topGen ` ran (,) ) = %s )' % (A0, JR))], 'eleqtrd', '( %s -> %s e. %s )' % (A0, X, JR))
jform = w.s([], 'eqid', '%s = %s' % (JR, JR))
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
sr = w.s([w.s([], 'reelprrecn', 'RR e. { RR , CC }')], 'a1i', '( %s -> RR e. { RR , CC } )' % A0)
scc = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
xss = w.s([w.s([], 'ioossre', '%s C_ RR' % X)], 'a1i', '( %s -> %s C_ RR )' % (A0, X))
dvi = w.s([sr], 'dvmptid', '( %s -> ( RR _D ( u e. RR |-> u ) ) = ( u e. RR |-> 1 ) )' % A0)
ARR = '( %s /\\ u e. RR )' % A0
AT = '( %s /\\ u e. %s )' % (A0, X)
tcr = w.s([w.s([], 'simpr', '( %s -> u e. RR )' % ARR)], 'recnd', '( %s -> u e. CC )' % ARR)
oner = a1(w, ARR, 'ax-1cn', '1 e. CC')
dvi2 = w.s([sr, tcr, oner, dvi, xss, jform, keq, xopn], 'dvmptres', '( %s -> ( RR _D ( u e. %s |-> u ) ) = ( u e. %s |-> 1 ) )' % (A0, X, X))
tr = w.s([w.s([xss], 'adantr', '( %s -> %s C_ RR )' % (AT, X)), w.s([], 'simpr', '( %s -> u e. %s )' % (AT, X))], 'sseldd', '( %s -> u e. RR )' % AT)
tc = w.s([tr], 'recnd', '( %s -> u e. CC )' % AT)
one = a1(w, AT, 'ax-1cn', '1 e. CC')
dvk = w.s([sr, tc, one, dvi2, kc], 'dvmptcmul', '( %s -> ( RR _D ( u e. %s |-> ( K x. u ) ) ) = ( u e. %s |-> ( K x. 1 ) ) )' % (A0, X, X))
kcd = w.s([kc], 'adantr', '( %s -> K e. CC )' % AT)
dvk2 = w.s([dvk, w.s([w.s([kcd], 'mulridd', '( %s -> ( K x. 1 ) = K )' % AT)], 'mpteq2dva', '( %s -> ( u e. %s |-> ( K x. 1 ) ) = ( u e. %s |-> K ) )' % (A0, X, X))], 'eqtrd',
           '( %s -> ( RR _D ( u e. %s |-> ( K x. u ) ) ) = ( u e. %s |-> K ) )' % (A0, X, X))
# the outer function
AY = '( %s /\\ y e. CC )' % A0
dvc = w.s([urp, w.inst('dvcxp2')], 'syl', '( %s -> ( CC _D ( y e. CC |-> ( U ^c y ) ) ) = ( y e. CC |-> ( %s x. ( U ^c y ) ) ) )' % (A0, L))
kuc = w.s([kcd, tc], 'mulcld', '( %s -> ( K x. u ) e. CC )' % AT)
uyc = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % AY), w.s([], 'simpr', '( %s -> y e. CC )' % AY)], 'cxpcld', '( %s -> ( U ^c y ) e. CC )' % AY)
luyc = w.s([w.s([lc], 'adantr', '( %s -> %s e. CC )' % (AY, L)), uyc], 'mulcld', '( %s -> ( %s x. ( U ^c y ) ) e. CC )' % (AY, L))
se = w.s([], 'oveq2', '( y = ( K x. u ) -> ( U ^c y ) = %s )' % EK('u'))
sf = w.s([se], 'oveq2d', '( y = ( K x. u ) -> ( %s x. ( U ^c y ) ) = ( %s x. %s ) )' % (L, L, EK('u')))
co = w.s([sr, scc, kuc, kcd, uyc, luyc, dvk2, dvc, se, sf], 'dvmptco',
         '( %s -> ( RR _D ( u e. %s |-> %s ) ) = ( u e. %s |-> ( ( %s x. %s ) x. K ) ) )' % (A0, X, EK('u'), X, L, EK('u')))
# divide by K log U
ec = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % AT), kuc], 'cxpcld', '( %s -> %s e. CC )' % (AT, EK('u')))
lcd = w.s([lc], 'adantr', '( %s -> %s e. CC )' % (AT, L))
lec = w.s([lcd, ec], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (AT, L, EK('u')))
prc = w.s([lec, kcd], 'mulcld', '( %s -> ( ( %s x. %s ) x. K ) e. CC )' % (AT, L, EK('u')))
dc = w.s([sr, ec, prc, co, klc, klne], 'dvmptdivc',
         '( %s -> ( RR _D ( u e. %s |-> ( %s / %s ) ) ) = ( u e. %s |-> ( ( ( %s x. %s ) x. K ) / %s ) ) )' % (A0, X, EK('u'), KL, X, L, EK('u'), KL))
m1 = w.s([lcd, ec, kcd], 'mul32d', '( %s -> ( ( %s x. %s ) x. K ) = ( ( %s x. K ) x. %s ) )' % (AT, L, EK('u'), L, EK('u')))
m2 = w.s([w.s([lcd, kcd], 'mulcomd', '( %s -> ( %s x. K ) = %s )' % (AT, L, KL))], 'oveq1d', '( %s -> ( ( %s x. K ) x. %s ) = ( %s x. %s ) )' % (AT, L, EK('u'), KL, EK('u')))
m3 = w.s([w.s([m1, m2], 'eqtrd', '( %s -> ( ( %s x. %s ) x. K ) = ( %s x. %s ) )' % (AT, L, EK('u'), KL, EK('u')))], 'oveq1d',
         '( %s -> ( ( ( %s x. %s ) x. K ) / %s ) = ( ( %s x. %s ) / %s ) )' % (AT, L, EK('u'), KL, KL, EK('u'), KL))
m4 = w.s([ec, w.s([klc], 'adantr', '( %s -> %s e. CC )' % (AT, KL)), w.s([klne], 'adantr', '( %s -> %s =/= 0 )' % (AT, KL))], 'divcan3d',
         '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (AT, KL, EK('u'), KL, EK('u')))
bod = w.s([m3, m4], 'eqtrd', '( %s -> ( ( ( %s x. %s ) x. K ) / %s ) = %s )' % (AT, L, EK('u'), KL, EK('u')))
w.qed([dc, w.s([bod], 'mpteq2dva', '( %s -> ( u e. %s |-> ( ( ( %s x. %s ) x. K ) / %s ) ) = ( u e. %s |-> %s ) )' % (A0, X, L, EK('u'), KL, X, EK('u')))], 'eqtrd',
      '( %s -> ( RR _D ( u e. %s |-> ( %s / %s ) ) ) = ( u e. %s |-> %s ) )' % (A0, X, EK('u'), KL, X, EK('u')))
run7(w)

# ---------------------------------------------------------------- cxpaffcn2
A0C = '( U e. RR+ /\\ ( K e. RR /\\ ( A e. RR /\\ B e. RR ) ) )'
w = W('cxpaffcn2', 'The exponential ` U ^c ( K x. u ) ` is continuous on a closed interval '
      '( ~ cxpaffcnb with a slope and a general interval).')
urp = w.s([], 'simpl', '( %s -> U e. RR+ )' % A0C)
kr = w.s([], 'simprl', '( %s -> K e. RR )' % A0C)
ar = w.s([], 'simprrl', '( %s -> A e. RR )' % A0C)
br = w.s([], 'simprrr', '( %s -> B e. RR )' % A0C)
kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0C)
lc = w.s([w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0C, L))], 'recnd', '( %s -> %s e. CC )' % (A0C, L))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0C)
u0 = w.s([urp], 'rpne0d', '( %s -> U =/= 0 )' % A0C)
ussr = w.s([ar, br, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0C, XC))
usscn = w.s([ussr, a1(w, A0C, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0C, XC))
sscc = a1(w, A0C, 'ssid', 'CC C_ CC')
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( u e. %s |-> u ) e. ( %s -cn-> CC ) )' % (A0C, XC, XC))
kcst = w.s([kc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( u e. %s |-> K ) e. ( %s -cn-> CC ) )' % (A0C, XC, XC))
lcst = w.s([lc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, L, XC))
mul1 = w.s([kcst, idc], 'mulcncf', '( %s -> ( u e. %s |-> ( K x. u ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, XC))
mul2 = w.s([mul1, lcst], 'mulcncf', '( %s -> ( u e. %s |-> ( ( K x. u ) x. %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, L, XC))
efc = a1(w, A0C, 'efcn', 'exp e. ( CC -cn-> CC )')
cmp = w.s([efc, mul2], 'cncfmpt1f', '( %s -> ( u e. %s |-> ( exp ` ( ( K x. u ) x. %s ) ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, L, XC))
ATC = '( %s /\\ u e. %s )' % (A0C, XC)
tcc = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> u e. %s )' % (ATC, XC))], 'sseldd', '( %s -> u e. RR )' % ATC)
kuc = w.s([w.s([kc], 'adantr', '( %s -> K e. CC )' % ATC), w.s([tcc], 'recnd', '( %s -> u e. CC )' % ATC)], 'mulcld', '( %s -> ( K x. u ) e. CC )' % ATC)
cef = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % ATC), w.s([u0], 'adantr', '( %s -> U =/= 0 )' % ATC), kuc, w.inst('cxpef')], 'syl3anc',
          '( %s -> %s = ( exp ` ( ( K x. u ) x. %s ) ) )' % (ATC, EK('u'), L))
mpe = w.s([cef], 'mpteq2dva', '( %s -> ( u e. %s |-> %s ) = ( u e. %s |-> ( exp ` ( ( K x. u ) x. %s ) ) ) )' % (A0C, XC, EK('u'), XC, L))
w.qed([mpe, cmp], 'eqeltrd', '( %s -> ( u e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, EK('u'), XC))
run7(w)

# ---------------------------------------------------------------- cxpaffibl2
HC = '( u e. %s |-> %s )' % (XC, EK('u'))
HO = '( u e. %s |-> %s )' % (X, EK('u'))
w = W('cxpaffibl2', 'The exponential ` U ^c ( K x. u ) ` is continuous and integrable on an '
      'open interval ( ~ cxpaffibl with a slope and a general interval).')
urp = w.s([], 'simpl', '( %s -> U e. RR+ )' % A0C)
kr = w.s([], 'simprl', '( %s -> K e. RR )' % A0C)
ar = w.s([], 'simprrl', '( %s -> A e. RR )' % A0C)
br = w.s([], 'simprrr', '( %s -> B e. RR )' % A0C)
kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0C)
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0C)
ussr = w.s([ar, br, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0C, XC))
ATC = '( %s /\\ u e. %s )' % (A0C, XC)
tcc = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> u e. %s )' % (ATC, XC))], 'sseldd', '( %s -> u e. RR )' % ATC)
kuc = w.s([w.s([kc], 'adantr', '( %s -> K e. CC )' % ATC), w.s([tcc], 'recnd', '( %s -> u e. CC )' % ATC)], 'mulcld', '( %s -> ( K x. u ) e. CC )' % ATC)
hcc = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % ATC), kuc], 'cxpcld', '( %s -> %s e. CC )' % (ATC, EK('u')))
hccn = w.s([w.s([], 'id', '( %s -> %s )' % (A0C, A0C)), w.inst('cxpaffcn2')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, HC, XC))
ioss = a1(w, A0C, 'ioossicc', '%s C_ %s' % (X, XC))
rci = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HC, XC, HC, X, X))
hres = w.s([hccn, w.s([rci], 'a1i', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0C, HC, XC, HC, X, X))], 'mpd',
           '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0C, HC, X, X))
rsm = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (HC, X, HO))
hocn = w.s([w.s([w.s([rsm], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A0C, HC, X, HO))], 'eqcomd', '( %s -> %s = ( %s |` %s ) )' % (A0C, HO, HC, X)), hres], 'eqeltrd',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, HO, X))
hcibl = w.s([ar, br, hccn, w.inst('cniccibl')], 'syl3anc', '( %s -> %s e. L^1 )' % (A0C, HC))
hoibl = w.s([ioss, a1(w, A0C, 'ioombl', '%s e. dom vol' % X), hcc, hcibl], 'iblss', '( %s -> %s e. L^1 )' % (A0C, HO))
w.qed([hocn, hoibl], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 ) )' % (A0C, HO, X, HO))
run7(w)

# ---------------------------------------------------------------- cxpaffitg2
A0 = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( ( K e. RR /\\ K =/= 0 ) /\\ ( A e. RR /\\ B e. RR /\\ A <_ B ) ) )'
GPC = '( u e. %s |-> ( %s / %s ) )' % (XC, EK('u'), KL)
GPO = '( u e. %s |-> ( %s / %s ) )' % (X, EK('u'), KL)
GPCA = '( a e. %s |-> ( %s / %s ) )' % (XC, EK('a'), KL)
w = W('cxpaffitg2', 'The exponential integral on an interval: ` S. ( A (,) B ) U ^c ( K u ) _d u '
      '= ( U ^c ( K B ) - U ^c ( K A ) ) / ( K log U ) ` by ~ ftc2 on ~ cxpaffdv2 .  The '
      'exact value of the line-moment tails ( ~ exp4itg , ~ exp4itgn ).')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0)
une = w.s([], 'simplr', '( %s -> U =/= 1 )' % A0)
kr = w.s([], 'simprll', '( %s -> K e. RR )' % A0)
kne = w.s([], 'simprlr', '( %s -> K =/= 0 )' % A0)
b3 = w.s([], 'simprr', '( %s -> ( A e. RR /\\ B e. RR /\\ A <_ B ) )' % A0)
ar = w.s([b3, w.inst('simp1')], 'syl', '( %s -> A e. RR )' % A0)
br = w.s([b3, w.inst('simp2')], 'syl', '( %s -> B e. RR )' % A0)
le = w.s([b3, w.inst('simp3')], 'syl', '( %s -> A <_ B )' % A0)
kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
lr = w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, L))
lc = w.s([lr], 'recnd', '( %s -> %s e. CC )' % (A0, L))
lne = w.s([urp, une, w.inst('logne0')], 'syl2anc', '( %s -> %s =/= 0 )' % (A0, L))
klc = w.s([kc, lc], 'mulcld', '( %s -> %s e. CC )' % (A0, KL))
klne = w.s([kc, lc, kne, lne], 'mulne0d', '( %s -> %s =/= 0 )' % (A0, KL))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0)
ussr = w.s([ar, br, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, XC))
usscn = w.s([ussr, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, XC))
hyp0 = w.s([urp, w.s([kr, w.s([ar, br], 'jca', '( %s -> ( A e. RR /\\ B e. RR ) )' % A0)], 'jca', '( %s -> ( K e. RR /\\ ( A e. RR /\\ B e. RR ) ) )' % A0)], 'jca', '( %s -> %s )' % (A0, A0C))
hyp1 = w.s([w.s([urp, une], 'jca', '( %s -> ( U e. RR+ /\\ U =/= 1 ) )' % A0), w.s([w.s([kr, kne], 'jca', '( %s -> ( K e. RR /\\ K =/= 0 ) )' % A0), w.s([ar, br], 'jca', '( %s -> ( A e. RR /\\ B e. RR ) )' % A0)], 'jca',
               '( %s -> ( ( K e. RR /\\ K =/= 0 ) /\\ ( A e. RR /\\ B e. RR ) ) )' % A0)], 'jca',
          '( %s -> ( ( U e. RR+ /\\ U =/= 1 ) /\\ ( ( K e. RR /\\ K =/= 0 ) /\\ ( A e. RR /\\ B e. RR ) ) ) )' % A0)
# closures on the closed interval
ATC = '( %s /\\ u e. %s )' % (A0, XC)
tcc = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> u e. %s )' % (ATC, XC))], 'sseldd', '( %s -> u e. RR )' % ATC)
kuc = w.s([w.s([kc], 'adantr', '( %s -> K e. CC )' % ATC), w.s([tcc], 'recnd', '( %s -> u e. CC )' % ATC)], 'mulcld', '( %s -> ( K x. u ) e. CC )' % ATC)
cxcc = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % ATC), kuc], 'cxpcld', '( %s -> %s e. CC )' % (ATC, EK('u')))
klcd = w.s([klc], 'adantr', '( %s -> %s e. CC )' % (ATC, KL)); klned = w.s([klne], 'adantr', '( %s -> %s =/= 0 )' % (ATC, KL))
# the primitive is continuous on the closed interval
base = w.s([hyp0, w.inst('cxpaffcn2')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, HC, XC))
recl = w.s([w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), klc, klne], 'divcld', '( %s -> ( 1 / %s ) e. CC )' % (A0, KL)), usscn, a1(w, A0, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc',
           '( %s -> ( u e. %s |-> ( 1 / %s ) ) e. ( %s -cn-> CC ) )' % (A0, XC, KL, XC))
prodcn = w.s([base, recl], 'mulcncf', '( %s -> ( u e. %s |-> ( %s x. ( 1 / %s ) ) ) e. ( %s -cn-> CC ) )' % (A0, XC, EK('u'), KL, XC))
dvr = w.s([cxcc, klcd, klned], 'divrecd', '( %s -> ( %s / %s ) = ( %s x. ( 1 / %s ) ) )' % (ATC, EK('u'), KL, EK('u'), KL))
gpccn = w.s([w.s([dvr], 'mpteq2dva', '( %s -> %s = ( u e. %s |-> ( %s x. ( 1 / %s ) ) ) )' % (A0, GPC, XC, EK('u'), KL)), prodcn], 'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GPC, XC))
# the derivative on the closed interval is the one on the open interval
jform = w.s([], 'eqid', '%s = %s' % (JR, JR))
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
gcl = w.s([cxcc, klcd, klned], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (ATC, EK('u'), KL))
icc0 = w.s([ar, br, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` %s ) = %s )' % (A0, XC, X))
jeq2 = w.s([w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)], 'eqcomi', '%s = ( topGen ` ran (,) )' % JR)
icc = w.s([w.s([w.s([jeq2], 'a1i', '( %s -> %s = ( topGen ` ran (,) ) )' % (A0, JR))], 'fveq2d', '( %s -> ( int ` %s ) = ( int ` ( topGen ` ran (,) ) ) )' % (A0, JR))], 'fveq1d',
          '( %s -> ( ( int ` %s ) ` %s ) = ( ( int ` ( topGen ` ran (,) ) ) ` %s ) )' % (A0, JR, XC, XC))
icc2 = w.s([icc, icc0], 'eqtrd', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0, JR, XC, X))
ntr = w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), ussr, gcl, jform, keq, icc2], 'dvmptntr', '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0, GPC, GPO))
dvo = w.s([hyp1, w.inst('cxpaffdv2')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, GPO, HO))
dvf = w.s([ntr, dvo], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, GPC, HO))
cbvs = w.s([w.s([w.s([], 'oveq2', '( u = a -> ( K x. u ) = ( K x. a ) )')], 'oveq2d', '( u = a -> %s = %s )' % (EK('u'), EK('a')))], 'oveq1d',
           '( u = a -> ( %s / %s ) = ( %s / %s ) )' % (EK('u'), KL, EK('a'), KL))
cbvd = w.s([w.s([cbvs], 'cbvmptv', '%s = %s' % (GPC, GPCA))], 'a1i', '( %s -> %s = %s )' % (A0, GPC, GPCA))
dvfa = w.s([w.s([w.s([cbvd], 'eqcomd', '( %s -> %s = %s )' % (A0, GPCA, GPC))], 'oveq2d', '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0, GPCA, GPC)), dvf], 'eqtrd',
           '( %s -> ( RR _D %s ) = %s )' % (A0, GPCA, HO))
# the derivative is continuous and integrable on the open interval
ibl = w.s([hyp0, w.inst('cxpaffibl2')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 ) )' % (A0, HO, X, HO))
hocn = w.s([ibl, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, HO, X))
hoibl = w.s([ibl, w.inst('simpr')], 'syl', '( %s -> %s e. L^1 )' % (A0, HO))
dcn = w.s([w.s([dvfa], 'eqcomd', '( %s -> %s = ( RR _D %s ) )' % (A0, HO, GPCA)), hocn], 'eqeltrrd', '( %s -> ( RR _D %s ) e. ( %s -cn-> CC ) )' % (A0, GPCA, X))
dib = w.s([w.s([dvfa], 'eqcomd', '( %s -> %s = ( RR _D %s ) )' % (A0, HO, GPCA)), hoibl], 'eqeltrrd', '( %s -> ( RR _D %s ) e. L^1 )' % (A0, GPCA))
gpccna = w.s([w.s([cbvd], 'eqcomd', '( %s -> %s = %s )' % (A0, GPCA, GPC)), gpccn], 'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, GPCA, XC))
ftc = w.s([ar, br, le, dcn, dib, gpccna], 'ftc2', '( %s -> S. %s ( ( RR _D %s ) ` u ) _d u = ( ( %s ` B ) - ( %s ` A ) ) )' % (A0, X, GPCA, GPCA, GPCA))
# the integrand
ATO = '( %s /\\ u e. %s )' % (A0, X)
hval = w.s([w.s([w.s([], 'eqid', '%s = %s' % (HO, HO))], 'a1i', '( %s -> %s = %s )' % (A0, HO, HO)), w.s([w.s([], 'ovex', '%s e. _V' % EK('u'))], 'a1i', '( %s -> %s e. _V )' % (ATO, EK('u')))],
           'fvmpt2d', '( %s -> ( %s ` u ) = %s )' % (ATO, HO, EK('u')))
dval = w.s([w.s([w.s([dvfa], 'adantr', '( %s -> ( RR _D %s ) = %s )' % (ATO, GPCA, HO))], 'fveq1d', '( %s -> ( ( RR _D %s ) ` u ) = ( %s ` u ) )' % (ATO, GPCA, HO)), hval], 'eqtrd',
           '( %s -> ( ( RR _D %s ) ` u ) = %s )' % (ATO, GPCA, EK('u')))
itg = w.s([dval], 'itgeq2dv', '( %s -> S. %s ( ( RR _D %s ) ` u ) _d u = S. %s %s _d u )' % (A0, X, GPCA, X, EK('u')))
# the endpoint values
axr = w.s([ar], 'rexrd', '( %s -> A e. RR* )' % A0); bxr = w.s([br], 'rexrd', '( %s -> B e. RR* )' % A0)
bin = w.s([axr, bxr, le, w.inst('ubicc2')], 'syl3anc', '( %s -> B e. %s )' % (A0, XC))
ain = w.s([axr, bxr, le, w.inst('lbicc2')], 'syl3anc', '( %s -> A e. %s )' % (A0, XC))


def endval(P, mem):
    sub = w.s([w.s([w.s([], 'oveq2', '( a = %s -> ( K x. a ) = ( K x. %s ) )' % (P, P))], 'oveq2d', '( a = %s -> %s = %s )' % (P, EK('a'), EK(P)))], 'oveq1d',
              '( a = %s -> ( %s / %s ) = ( %s / %s ) )' % (P, EK('a'), KL, EK(P), KL))
    return w.s([mem, w.s([w.s([], 'ovex', '( %s / %s ) e. _V' % (EK(P), KL))], 'a1i', '( %s -> ( %s / %s ) e. _V )' % (A0, EK(P), KL)),
                w.s([sub, w.s([], 'eqid', '%s = %s' % (GPCA, GPCA))], 'fvmptg', '( ( %s e. %s /\\ ( %s / %s ) e. _V ) -> ( %s ` %s ) = ( %s / %s ) )' % (P, XC, EK(P), KL, GPCA, P, EK(P), KL))],
               'syl2anc', '( %s -> ( %s ` %s ) = ( %s / %s ) )' % (A0, GPCA, P, EK(P), KL))


vb = endval('B', bin); va = endval('A', ain)
cb = w.s([uc, w.s([kc, w.s([br], 'recnd', '( %s -> B e. CC )' % A0)], 'mulcld', '( %s -> ( K x. B ) e. CC )' % A0)], 'cxpcld', '( %s -> %s e. CC )' % (A0, EK('B')))
ca = w.s([uc, w.s([kc, w.s([ar], 'recnd', '( %s -> A e. CC )' % A0)], 'mulcld', '( %s -> ( K x. A ) e. CC )' % A0)], 'cxpcld', '( %s -> %s e. CC )' % (A0, EK('A')))
dsd = w.s([cb, ca, klc, klne], 'divsubdird', '( %s -> ( ( %s - %s ) / %s ) = ( ( %s / %s ) - ( %s / %s ) ) )' % (A0, EK('B'), EK('A'), KL, EK('B'), KL, EK('A'), KL))
w.qed([w.s([itg], 'eqcomd', '( %s -> S. %s %s _d u = S. %s ( ( RR _D %s ) ` u ) _d u )' % (A0, X, EK('u'), X, GPCA)),
       w.s([ftc, w.s([w.s([vb, va], 'oveq12d', '( %s -> ( ( %s ` B ) - ( %s ` A ) ) = ( ( %s / %s ) - ( %s / %s ) ) )' % (A0, GPCA, GPCA, EK('B'), KL, EK('A'), KL)),
                      w.s([dsd], 'eqcomd', '( %s -> ( ( %s / %s ) - ( %s / %s ) ) = ( ( %s - %s ) / %s ) )' % (A0, EK('B'), KL, EK('A'), KL, EK('B'), EK('A'), KL))], 'eqtrd',
                     '( %s -> ( ( %s ` B ) - ( %s ` A ) ) = ( ( %s - %s ) / %s ) )' % (A0, GPCA, GPCA, EK('B'), EK('A'), KL))], 'eqtrd',
           '( %s -> S. %s ( ( RR _D %s ) ` u ) _d u = ( ( %s - %s ) / %s ) )' % (A0, X, GPCA, EK('B'), EK('A'), KL))], 'eqtrd',
      '( %s -> S. %s %s _d u = ( ( %s - %s ) / %s ) )' % (A0, X, EK('u'), EK('B'), EK('A'), KL))
run7(w)
