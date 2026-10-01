"""Sortie V1, batch 6: the Mertens estimate with explicit constants
(chtle4, sqrtlogle, chple4, mertens1ge, mertens1le, mertens1)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
sys.path.insert(0, os.path.dirname(__file__)); from v1_lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

HX = '( X e. RR /\\ 1 <_ X )'
FZX = '( 1 ... ( |_ ` X ) )'
S = 'sum_ d e. %s ( ( Lam ` d ) / d )' % FZX
T1 = 'sum_ d e. %s ( ( Lam ` d ) x. ( X / d ) )' % FZX
T2 = 'sum_ d e. %s ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) )' % FZX
T2K = 'sum_ k e. %s ( ( Lam ` k ) x. ( |_ ` ( X / k ) ) )' % FZX
T3 = 'sum_ d e. %s ( ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) + ( Lam ` d ) )' % FZX
LAMS = 'sum_ d e. %s ( Lam ` d )' % FZX
LAMSN = 'sum_ n e. %s ( Lam ` n )' % FZX
LF = '( log ` ( ! ` ( |_ ` X ) ) )'
L4 = '( log ` 4 )'
B4 = '( %s + 4 )' % L4


def log4eq(w):
    """closed steps: ( log ` 4 ) e. RR , 0 <_ ( log ` 4 ) , ( log ` 4 ) = ( 2 x. ( log ` 2 ) )"""
    p4 = w.s([], '4rp', '4 e. RR+')
    l4r = w.s([p4, w.inst('relogcl')], 'ax-mp', '%s e. RR' % L4)
    r2 = w.s([], '2rp', '2 e. RR+')
    z2 = w.s([], '2z', '2 e. ZZ')
    re = w.s([r2, z2, w.inst('relogexp')], 'mp2an', '( log ` ( 2 ^ 2 ) ) = ( 2 x. ( log ` 2 ) )')
    sq = w.s([], 'sq2', '( 2 ^ 2 ) = 4')
    fv = w.s([sq], 'fveq2i', '( log ` ( 2 ^ 2 ) ) = %s' % L4)
    eq = w.s([fv, re], 'eqtr3i', '%s = ( 2 x. ( log ` 2 ) )' % L4)
    return l4r, eq


def xrp(w, ante, xr, x1):
    """( ante -> X e. RR+ ) and ( ante -> 0 <_ X )"""
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % ante)
    r1 = w.s([], '1red', '( %s -> 1 e. RR )' % ante)
    z1 = w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % ante)
    y0 = w.s([z0, r1, xr, z1, x1], 'ltletrd', '( %s -> 0 < X )' % ante)
    rp = w.s([xr, y0], 'elrpd', '( %s -> X e. RR+ )' % ante)
    ge = w.s([z0, xr, y0], 'ltled', '( %s -> 0 <_ X )' % ante)
    return rp, y0, ge


# ---- chtle4: theta ( X ) <_ ( log 4 ) X
w = W('chtle4', "Chebyshev's upper bound for theta with the explicit constant log 4.")
xr = w.s([], 'simpl', '( %s -> X e. RR )' % HX); x1 = w.s([], 'simpr', '( %s -> 1 <_ X )' % HX)
l4r, l4eq = log4eq(w)
l2rp = w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2'), w.inst('rplogcl')], 'mp2an', '( log ` 2 ) e. RR+')
l2r = w.s([l2rp, w.inst('rpre')], 'ax-mp', '( log ` 2 ) e. RR')
l2ge = w.s([l2rp, w.inst('rpge0')], 'ax-mp', '0 <_ ( log ` 2 )')
l4d = w.s([l4r], 'a1i', '( %s -> %s e. RR )' % (HX, L4))
l4g0 = w.s([w.s([w.s([], '4re', '4 e. RR'), w.s([], '1lt4', '1 < 4'), w.inst('rplogcl')], 'mp2an', '%s e. RR+' % L4), w.inst('rpge0')], 'ax-mp', '0 <_ %s' % L4)
l4g0d = w.s([l4g0], 'a1i', '( %s -> 0 <_ %s )' % (HX, L4))
# log 2 <_ log 4
lle = w.s([w.s([], '2rp', '2 e. RR+'), w.s([], '4rp', '4 e. RR+'), w.inst('logleb')], 'mp2an', '( 2 <_ 4 <-> ( log ` 2 ) <_ %s )' % L4)
l24 = w.s([w.s([], '2re', '2 e. RR'), w.s([], '4re', '4 e. RR'), w.s([], '2lt4', '2 < 4')], 'ltleii', '2 <_ 4')
l2le4 = w.s([l24, lle], 'mpbi', '( log ` 2 ) <_ %s' % L4)
# case X <_ 2
C1 = '( %s /\\ X <_ 2 )' % HX
xr1 = w.s([xr], 'adantr', '( %s -> X e. RR )' % C1); x11 = w.s([x1], 'adantr', '( %s -> 1 <_ X )' % C1)
le2 = w.s([], 'simpr', '( %s -> X <_ 2 )' % C1)
r2a = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % C1)
cw = w.s([xr1, r2a, le2, w.inst('chtwordi')], 'syl3anc', '( %s -> ( theta ` X ) <_ ( theta ` 2 ) )' % C1)
c2 = w.s([w.s([], 'cht2', '( theta ` 2 ) = ( log ` 2 )')], 'a1i', '( %s -> ( theta ` 2 ) = ( log ` 2 ) )' % C1)
cw2 = w.s([cw, c2], 'breqtrd', '( %s -> ( theta ` X ) <_ ( log ` 2 ) )' % C1)
l4c1 = w.s([l4r], 'a1i', '( %s -> %s e. RR )' % (C1, L4))
l4gc1 = w.s([l4g0], 'a1i', '( %s -> 0 <_ %s )' % (C1, L4))
r1c1 = w.s([], '1red', '( %s -> 1 e. RR )' % C1)
mu1 = w.s([w.s([r1c1, xr1, w.s([l4c1, l4gc1], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (C1, L4, L4))], '3jca', '( %s -> ( 1 e. RR /\\ X e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (C1, L4, L4)), x11, w.inst('lemul2a')], 'syl2anc', '( %s -> ( %s x. 1 ) <_ ( %s x. X ) )' % (C1, L4, L4))
mu2 = w.s([w.s([l4c1], 'recnd', '( %s -> %s e. CC )' % (C1, L4))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (C1, L4, L4))
mu3 = w.s([mu2, mu1], 'eqbrtrrd', '( %s -> %s <_ ( %s x. X ) )' % (C1, L4, L4))
l2c1 = w.s([l2r], 'a1i', '( %s -> ( log ` 2 ) e. RR )' % C1)
l24c1 = w.s([l2le4], 'a1i', '( %s -> ( log ` 2 ) <_ %s )' % (C1, L4))
prod1 = w.s([l4c1, xr1], 'remulcld', '( %s -> ( %s x. X ) e. RR )' % (C1, L4))
tc1 = w.s([xr1, w.inst('chtcl')], 'syl', '( %s -> ( theta ` X ) e. RR )' % C1)
ch1 = w.s([l2c1, l4c1, prod1, l24c1, mu3], 'letrd', '( %s -> ( log ` 2 ) <_ ( %s x. X ) )' % (C1, L4))
case1 = w.s([tc1, l2c1, prod1, cw2, ch1], 'letrd', '( %s -> ( theta ` X ) <_ ( %s x. X ) )' % (C1, L4))
# case 2 < X
C2 = '( %s /\\ 2 < X )' % HX
xr2 = w.s([xr], 'adantr', '( %s -> X e. RR )' % C2)
gt2 = w.s([], 'simpr', '( %s -> 2 < X )' % C2)
ub = w.s([xr2, gt2, w.inst('chtub')], 'syl2anc', '( %s -> ( theta ` X ) < ( ( log ` 2 ) x. ( ( 2 x. X ) - 3 ) ) )' % C2)
r2b = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % C2)
r3b = w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % C2)
tx = w.s([r2b, xr2], 'remulcld', '( %s -> ( 2 x. X ) e. RR )' % C2)
sub3 = w.s([tx, r3b], 'resubcld', '( %s -> ( ( 2 x. X ) - 3 ) e. RR )' % C2)
g3b = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % C2), r3b, w.s([w.s([], '3pos', '0 < 3')], 'a1i', '( %s -> 0 < 3 )' % C2)], 'ltled', '( %s -> 0 <_ 3 )' % C2)
sleb = w.s([tx, r3b, w.inst('subge02')], 'syl2anc', '( %s -> ( 0 <_ 3 <-> ( ( 2 x. X ) - 3 ) <_ ( 2 x. X ) ) )' % C2)
sle = w.s([g3b, sleb], 'mpbid', '( %s -> ( ( 2 x. X ) - 3 ) <_ ( 2 x. X ) )' % C2)
l2c2 = w.s([l2r], 'a1i', '( %s -> ( log ` 2 ) e. RR )' % C2)
l2gc2 = w.s([l2ge], 'a1i', '( %s -> 0 <_ ( log ` 2 ) )' % C2)
mm = w.s([w.s([sub3, tx, w.s([l2c2, l2gc2], 'jca', '( %s -> ( ( log ` 2 ) e. RR /\\ 0 <_ ( log ` 2 ) ) )' % C2)], '3jca', '( %s -> ( ( ( 2 x. X ) - 3 ) e. RR /\\ ( 2 x. X ) e. RR /\\ ( ( log ` 2 ) e. RR /\\ 0 <_ ( log ` 2 ) ) ) )' % C2), sle, w.inst('lemul2a')], 'syl2anc', '( %s -> ( ( log ` 2 ) x. ( ( 2 x. X ) - 3 ) ) <_ ( ( log ` 2 ) x. ( 2 x. X ) ) )' % C2)
l2cc = w.s([l2c2], 'recnd', '( %s -> ( log ` 2 ) e. CC )' % C2)
r2cc = w.s([r2b], 'recnd', '( %s -> 2 e. CC )' % C2)
xcc = w.s([xr2], 'recnd', '( %s -> X e. CC )' % C2)
as1 = w.s([l2cc, r2cc, xcc], 'mulassd', '( %s -> ( ( ( log ` 2 ) x. 2 ) x. X ) = ( ( log ` 2 ) x. ( 2 x. X ) ) )' % C2)
cm1 = w.s([l2cc, r2cc], 'mulcomd', '( %s -> ( ( log ` 2 ) x. 2 ) = ( 2 x. ( log ` 2 ) ) )' % C2)
cm2 = w.s([cm1], 'oveq1d', '( %s -> ( ( ( log ` 2 ) x. 2 ) x. X ) = ( ( 2 x. ( log ` 2 ) ) x. X ) )' % C2)
l4c2 = w.s([l4eq], 'a1i', '( %s -> %s = ( 2 x. ( log ` 2 ) ) )' % (C2, L4))
cm3 = w.s([l4c2], 'oveq1d', '( %s -> ( %s x. X ) = ( ( 2 x. ( log ` 2 ) ) x. X ) )' % (C2, L4))
eqp = w.s([cm2, cm3], 'eqtr4d', '( %s -> ( ( ( log ` 2 ) x. 2 ) x. X ) = ( %s x. X ) )' % (C2, L4))
eqp2 = w.s([as1, eqp], 'eqtr3d', '( %s -> ( ( log ` 2 ) x. ( 2 x. X ) ) = ( %s x. X ) )' % (C2, L4))
mm2 = w.s([mm, eqp2], 'breqtrd', '( %s -> ( ( log ` 2 ) x. ( ( 2 x. X ) - 3 ) ) <_ ( %s x. X ) )' % (C2, L4))
tc2 = w.s([xr2, w.inst('chtcl')], 'syl', '( %s -> ( theta ` X ) e. RR )' % C2)
pr2 = w.s([l2c2, sub3], 'remulcld', '( %s -> ( ( log ` 2 ) x. ( ( 2 x. X ) - 3 ) ) e. RR )' % C2)
pr3 = w.s([w.s([l4r], 'a1i', '( %s -> %s e. RR )' % (C2, L4)), xr2], 'remulcld', '( %s -> ( %s x. X ) e. RR )' % (C2, L4))
ubl = w.s([tc2, pr2, ub], 'ltled', '( %s -> ( theta ` X ) <_ ( ( log ` 2 ) x. ( ( 2 x. X ) - 3 ) ) )' % C2)
case2 = w.s([tc2, pr2, pr3, ubl, mm2], 'letrd', '( %s -> ( theta ` X ) <_ ( %s x. X ) )' % (C2, L4))
cas = w.s([xr, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % HX), w.inst('lelttric')], 'syl2anc', '( %s -> ( X <_ 2 \\/ 2 < X ) )' % HX)
w.qed([case1, case2, cas], 'mpjaodan', '( %s -> ( theta ` X ) <_ ( %s x. X ) )' % (HX, L4)); run(w)


# ---- sqrtlogle: ( sqrt X ) ( log X ) <_ X
w = W('sqrtlogle', 'The product of the square root and the logarithm is at most the argument, for arguments at least one.')
xr = w.s([], 'simpl', '( %s -> X e. RR )' % HX); x1 = w.s([], 'simpr', '( %s -> 1 <_ X )' % HX)
rp, x0, xge = xrp(w, HX, xr, x1)
r1 = w.s([], '1red', '( %s -> 1 e. RR )' % HX)
xm = w.s([xr, r1], 'resubcld', '( %s -> ( X - 1 ) e. RR )' % HX)
xm0 = w.s([x1, w.s([xr, r1, w.inst('subge0')], 'syl2anc', '( %s -> ( 0 <_ ( X - 1 ) <-> 1 <_ X ) )' % HX)], 'mpbird', '( %s -> 0 <_ ( X - 1 ) )' % HX)
ll = w.s([xm, xm0, w.inst('loglesqrt')], 'syl2anc', '( %s -> ( log ` ( ( X - 1 ) + 1 ) ) <_ ( sqrt ` ( X - 1 ) ) )' % HX)
np = w.s([w.s([xr], 'recnd', '( %s -> X e. CC )' % HX), w.s([], '1cnd', '( %s -> 1 e. CC )' % HX)], 'npcand', '( %s -> ( ( X - 1 ) + 1 ) = X )' % HX)
npf = w.s([np], 'fveq2d', '( %s -> ( log ` ( ( X - 1 ) + 1 ) ) = ( log ` X ) )' % HX)
ll2 = w.s([npf, ll], 'eqbrtrrd', '( %s -> ( log ` X ) <_ ( sqrt ` ( X - 1 ) ) )' % HX)
sl = w.s([w.s([xm, xm0], 'jca', '( %s -> ( ( X - 1 ) e. RR /\\ 0 <_ ( X - 1 ) ) )' % HX), w.s([xr, xge], 'jca', '( %s -> ( X e. RR /\\ 0 <_ X ) )' % HX), w.inst('sqrtle')], 'syl2anc', '( %s -> ( ( X - 1 ) <_ X <-> ( sqrt ` ( X - 1 ) ) <_ ( sqrt ` X ) ) )' % HX)
lt1 = w.s([xr], 'ltm1d', '( %s -> ( X - 1 ) < X )' % HX)
lt1l = w.s([xm, xr, lt1], 'ltled', '( %s -> ( X - 1 ) <_ X )' % HX)
sl2 = w.s([lt1l, sl], 'mpbid', '( %s -> ( sqrt ` ( X - 1 ) ) <_ ( sqrt ` X ) )' % HX)
srp = w.s([rp, w.inst('rpsqrtcl')], 'syl', '( %s -> ( sqrt ` X ) e. RR+ )' % HX)
sr = w.s([srp], 'rpred', '( %s -> ( sqrt ` X ) e. RR )' % HX); sge = w.s([srp], 'rpge0d', '( %s -> 0 <_ ( sqrt ` X ) )' % HX)
lx = w.s([rp, w.inst('relogcl')], 'syl', '( %s -> ( log ` X ) e. RR )' % HX)
sqmr = w.s([xm, xm0, w.inst('resqrtcl')], 'syl2anc', '( %s -> ( sqrt ` ( X - 1 ) ) e. RR )' % HX)
lxs = w.s([lx, sqmr, sr, ll2, sl2], 'letrd', '( %s -> ( log ` X ) <_ ( sqrt ` X ) )' % HX)
mul = w.s([w.s([lx, sr, w.s([sr, sge], 'jca', '( %s -> ( ( sqrt ` X ) e. RR /\\ 0 <_ ( sqrt ` X ) ) )' % HX)], '3jca', '( %s -> ( ( log ` X ) e. RR /\\ ( sqrt ` X ) e. RR /\\ ( ( sqrt ` X ) e. RR /\\ 0 <_ ( sqrt ` X ) ) ) )' % HX), lxs, w.inst('lemul2a')], 'syl2anc', '( %s -> ( ( sqrt ` X ) x. ( log ` X ) ) <_ ( ( sqrt ` X ) x. ( sqrt ` X ) ) )' % HX)
sv = w.s([w.s([sr], 'recnd', '( %s -> ( sqrt ` X ) e. CC )' % HX), w.inst('sqval')], 'syl', '( %s -> ( ( sqrt ` X ) ^ 2 ) = ( ( sqrt ` X ) x. ( sqrt ` X ) )  )' % HX)
th = w.s([xr, xge, w.inst('resqrtth')], 'syl2anc', '( %s -> ( ( sqrt ` X ) ^ 2 ) = X )' % HX)
sq2e = w.s([sv, th], 'eqtr3d', '( %s -> ( ( sqrt ` X ) x. ( sqrt ` X ) ) = X )' % HX)
w.qed([mul, sq2e], 'breqtrd', '( %s -> ( ( sqrt ` X ) x. ( log ` X ) ) <_ X )' % HX); run(w)


# ---- chple4: psi ( X ) <_ ( ( log 4 ) + 4 ) X
w = W('chple4', "Chebyshev's upper bound for psi with the explicit constant ( log 4 ) + 4.")
xr = w.s([], 'simpl', '( %s -> X e. RR )' % HX); x1 = w.s([], 'simpr', '( %s -> 1 <_ X )' % HX)
rp, x0, xge = xrp(w, HX, xr, x1)
l4r, l4eq = log4eq(w)
l4d = w.s([l4r], 'a1i', '( %s -> %s e. RR )' % (HX, L4))
pub = w.s([xr, x1, w.inst('chpub')], 'syl2anc', '( %s -> ( psi ` X ) <_ ( ( theta ` X ) + ( ( sqrt ` X ) x. ( log ` X ) ) ) )' % HX)
tle = w.s([xr, x1, w.inst('chtle4')], 'syl2anc', '( %s -> ( theta ` X ) <_ ( %s x. X ) )' % (HX, L4))
sle = w.s([xr, x1, w.inst('sqrtlogle')], 'syl2anc', '( %s -> ( ( sqrt ` X ) x. ( log ` X ) ) <_ X )' % HX)
tc = w.s([xr, w.inst('chtcl')], 'syl', '( %s -> ( theta ` X ) e. RR )' % HX)
pc = w.s([xr, w.inst('chpcl')], 'syl', '( %s -> ( psi ` X ) e. RR )' % HX)
sr = w.s([w.s([rp, w.inst('rpsqrtcl')], 'syl', '( %s -> ( sqrt ` X ) e. RR+ )' % HX)], 'rpred', '( %s -> ( sqrt ` X ) e. RR )' % HX)
lx = w.s([rp, w.inst('relogcl')], 'syl', '( %s -> ( log ` X ) e. RR )' % HX)
slr = w.s([sr, lx], 'remulcld', '( %s -> ( ( sqrt ` X ) x. ( log ` X ) ) e. RR )' % HX)
l4x = w.s([l4d, xr], 'remulcld', '( %s -> ( %s x. X ) e. RR )' % (HX, L4))
add1 = w.s([tc, slr, l4x, xr, tle, sle], 'le2addd', '( %s -> ( ( theta ` X ) + ( ( sqrt ` X ) x. ( log ` X ) ) ) <_ ( ( %s x. X ) + X ) )' % (HX, L4))
# ( ( log 4 ) x. X ) + X = ( ( ( log 4 ) + 1 ) x. X )
l4c = w.s([l4d], 'recnd', '( %s -> %s e. CC )' % (HX, L4))
xc = w.s([xr], 'recnd', '( %s -> X e. CC )' % HX)
c1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % HX)
dd = w.s([l4c, c1, xc], 'adddird', '( %s -> ( ( %s + 1 ) x. X ) = ( ( %s x. X ) + ( 1 x. X ) ) )' % (HX, L4, L4))
m1 = w.s([xc], 'mullidd', '( %s -> ( 1 x. X ) = X )' % HX)
dd2 = w.s([dd, w.s([m1], 'oveq2d', '( %s -> ( ( %s x. X ) + ( 1 x. X ) ) = ( ( %s x. X ) + X ) )' % (HX, L4, L4))], 'eqtrd', '( %s -> ( ( %s + 1 ) x. X ) = ( ( %s x. X ) + X ) )' % (HX, L4, L4))
r1 = w.s([], '1red', '( %s -> 1 e. RR )' % HX)
r4 = w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % HX)
l14 = w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([], '4re', '4 e. RR'), w.s([], '1lt4', '1 < 4')], 'ltleii', '1 <_ 4')], 'a1i', '( %s -> 1 <_ 4 )' % HX)
sum1 = w.s([l4d, r1], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (HX, L4))
sum4 = w.s([l4d, r4], 'readdcld', '( %s -> %s e. RR )' % (HX, B4))
ad = w.s([r1, r4, l4d, l14], 'leadd2dd', '( %s -> ( %s + 1 ) <_ %s )' % (HX, L4, B4))
mul2 = w.s([w.s([sum1, sum4, w.s([xr, xge], 'jca', '( %s -> ( X e. RR /\\ 0 <_ X ) )' % HX)], '3jca', '( %s -> ( ( %s + 1 ) e. RR /\\ %s e. RR /\\ ( X e. RR /\\ 0 <_ X ) ) )' % (HX, L4, B4)), ad, w.inst('lemul1a')], 'syl2anc', '( %s -> ( ( %s + 1 ) x. X ) <_ ( %s x. X ) )' % (HX, L4, B4))
mul3 = w.s([dd2, mul2], 'eqbrtrrd', '( %s -> ( ( %s x. X ) + X ) <_ ( %s x. X ) )' % (HX, L4, B4))
sumr = w.s([tc, slr], 'readdcld', '( %s -> ( ( theta ` X ) + ( ( sqrt ` X ) x. ( log ` X ) ) ) e. RR )' % HX)
addr = w.s([l4x, xr], 'readdcld', '( %s -> ( ( %s x. X ) + X ) e. RR )' % (HX, L4))
bigr = w.s([sum4, xr], 'remulcld', '( %s -> ( %s x. X ) e. RR )' % (HX, B4))
ch = w.s([sumr, addr, bigr, add1, mul3], 'letrd', '( %s -> ( ( theta ` X ) + ( ( sqrt ` X ) x. ( log ` X ) ) ) <_ ( %s x. X ) )' % (HX, B4))
w.qed([pc, sumr, bigr, pub, ch], 'letrd', '( %s -> ( psi ` X ) <_ ( %s x. X ) )' % (HX, B4)); run(w)


def mertcommon(w):
    """the shared setup of mertens1ge and mertens1le; returns a dict of steps"""
    g = {}
    g['xr'] = xr = w.s([], 'simpl', '( %s -> X e. RR )' % HX)
    g['x1'] = x1 = w.s([], 'simpr', '( %s -> 1 <_ X )' % HX)
    g['rp'], g['x0'], g['xge'] = xrp(w, HX, xr, x1)
    g['xc'] = w.s([xr], 'recnd', '( %s -> X e. CC )' % HX)
    g['fzfin'] = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (HX, FZX))
    A = '( %s /\\ d e. %s )' % (HX, FZX)
    g['A'] = A
    dfz = w.s([], 'simpr', '( %s -> d e. %s )' % (A, FZX))
    dnn = w.s([dfz, w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % A)
    g['dnn'] = dnn
    drp = w.s([dnn], 'nnrpd', '( %s -> d e. RR+ )' % A)
    g['dc'] = w.s([dnn], 'nncnd', '( %s -> d e. CC )' % A)
    g['dne0'] = w.s([dnn], 'nnne0d', '( %s -> d =/= 0 )' % A)
    g['lam'] = lam = w.s([dnn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` d ) e. RR )' % A)
    g['lam0'] = lam0 = w.s([dnn, w.inst('vmage0')], 'syl', '( %s -> 0 <_ ( Lam ` d ) )' % A)
    g['lamc'] = w.s([lam], 'recnd', '( %s -> ( Lam ` d ) e. CC )' % A)
    g['lamge'] = w.s([lam, lam0], 'jca', '( %s -> ( ( Lam ` d ) e. RR /\\ 0 <_ ( Lam ` d ) ) )' % A)
    xrA = w.s([xr], 'adantr', '( %s -> X e. RR )' % A)
    g['xrA'] = xrA
    g['rat'] = rat = w.s([xrA, drp], 'rerpdivcld', '( %s -> ( X / d ) e. RR )' % A)
    g['lamdiv'] = lamdiv = w.s([lam, drp], 'rerpdivcld', '( %s -> ( ( Lam ` d ) / d ) e. RR )' % A)
    g['lamdivc'] = w.s([lamdiv], 'recnd', '( %s -> ( ( Lam ` d ) / d ) e. CC )' % A)
    g['fl'] = fl = w.s([rat, w.inst('reflcl')], 'syl', '( %s -> ( |_ ` ( X / d ) ) e. RR )' % A)
    g['flc'] = w.s([fl], 'recnd', '( %s -> ( |_ ` ( X / d ) ) e. CC )' % A)
    g['t1r'] = t1r = w.s([lam, rat], 'remulcld', '( %s -> ( ( Lam ` d ) x. ( X / d ) ) e. RR )' % A)
    g['t1c'] = w.s([t1r], 'recnd', '( %s -> ( ( Lam ` d ) x. ( X / d ) ) e. CC )' % A)
    g['t2r'] = t2r = w.s([lam, fl], 'remulcld', '( %s -> ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) e. RR )' % A)
    g['t2c'] = w.s([t2r], 'recnd', '( %s -> ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) e. CC )' % A)
    # ( X x. ( ( Lam ` d ) / d ) ) = ( ( Lam ` d ) x. ( X / d ) )
    xcA = w.s([xrA], 'recnd', '( %s -> X e. CC )' % A)
    g['eqterm'] = w.s([xcA, g['lamc'], g['dc'], g['dne0'], w.inst('div12')], 'syl112anc', '( %s -> ( X x. ( ( Lam ` d ) / d ) ) = ( ( Lam ` d ) x. ( X / d ) ) )' % A)
    # ( X x. S ) = T1
    sm = w.s([g['fzfin'], g['xc'], g['lamdivc']], 'fsummulc2', '( %s -> ( X x. %s ) = sum_ d e. %s ( X x. ( ( Lam ` d ) / d ) ) )' % (HX, S, FZX))
    sq = w.s([g['eqterm']], 'sumeq2dv', '( %s -> sum_ d e. %s ( X x. ( ( Lam ` d ) / d ) ) = %s )' % (HX, FZX, T1))
    g['xS'] = w.s([sm, sq], 'eqtrd', '( %s -> ( X x. %s ) = %s )' % (HX, S, T1))
    # LF = T2
    lf2 = w.s([g['xr'], g['xge'], w.inst('logfac2')], 'syl2anc', '( %s -> %s = %s )' % (HX, LF, T2K))
    k1 = w.s([], 'fveq2', '( k = d -> ( Lam ` k ) = ( Lam ` d ) )')
    k2 = w.s([], 'oveq2', '( k = d -> ( X / k ) = ( X / d ) )')
    k3 = w.s([k2], 'fveq2d', '( k = d -> ( |_ ` ( X / k ) ) = ( |_ ` ( X / d ) ) )')
    k4 = w.s([k1, k3], 'oveq12d', '( k = d -> ( ( Lam ` k ) x. ( |_ ` ( X / k ) ) ) = ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) )')
    cb = w.s([k4], 'cbvsumv', '%s = %s' % (T2K, T2))
    g['lfT2'] = w.s([lf2, w.s([cb], 'a1i', '( %s -> %s = %s )' % (HX, T2K, T2))], 'eqtrd', '( %s -> %s = %s )' % (HX, LF, T2))
    # reals
    g['Sr'] = w.s([g['fzfin'], g['lamdiv']], 'fsumrecl', '( %s -> %s e. RR )' % (HX, S))
    g['T1r'] = w.s([g['fzfin'], t1r], 'fsumrecl', '( %s -> %s e. RR )' % (HX, T1))
    g['T2r'] = w.s([g['fzfin'], t2r], 'fsumrecl', '( %s -> %s e. RR )' % (HX, T2))
    g['lx'] = w.s([g['rp'], w.inst('relogcl')], 'syl', '( %s -> ( log ` X ) e. RR )' % HX)
    g['prodS'] = w.s([g['xr'], g['Sr']], 'remulcld', '( %s -> ( X x. %s ) e. RR )' % (HX, S))
    return g


# ---- mertens1ge
w = W('mertens1ge', 'Mertens estimate, lower half with an explicit constant: log X - 2 is at most the sum of ( Lam ` d ) / d over d up to X.')
g = mertcommon(w)
A = g['A']
fll = w.s([g['rat'], w.inst('flle')], 'syl', '( %s -> ( |_ ` ( X / d ) ) <_ ( X / d ) )' % A)
tle = w.s([w.s([g['fl'], g['rat'], g['lamge']], '3jca', '( %s -> ( ( |_ ` ( X / d ) ) e. RR /\\ ( X / d ) e. RR /\\ ( ( Lam ` d ) e. RR /\\ 0 <_ ( Lam ` d ) ) ) )' % A), fll, w.inst('lemul2a')], 'syl2anc', '( %s -> ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) <_ ( ( Lam ` d ) x. ( X / d ) ) )' % A)
le1 = w.s([g['fzfin'], g['t2r'], g['t1r'], tle], 'fsumle', '( %s -> %s <_ %s )' % (HX, T2, T1))
lb = w.s([g['rp'], w.inst('logfaclbnd')], 'syl', '( %s -> ( X x. ( ( log ` X ) - 2 ) ) <_ %s )' % (HX, LF))
r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % HX)
lx2 = w.s([g['lx'], r2], 'resubcld', '( %s -> ( ( log ` X ) - 2 ) e. RR )' % HX)
prod = w.s([g['xr'], lx2], 'remulcld', '( %s -> ( X x. ( ( log ` X ) - 2 ) ) e. RR )' % HX)
a = w.s([lb, g['lfT2']], 'breqtrd', '( %s -> ( X x. ( ( log ` X ) - 2 ) ) <_ %s )' % (HX, T2))
b = w.s([prod, g['T2r'], g['T1r'], a, le1], 'letrd', '( %s -> ( X x. ( ( log ` X ) - 2 ) ) <_ %s )' % (HX, T1))
c = w.s([b, g['xS']], 'breqtrrd', '( %s -> ( X x. ( ( log ` X ) - 2 ) ) <_ ( X x. %s ) )' % (HX, S))
bi = w.s([lx2, g['Sr'], g['xr'], g['x0'], w.inst('lemul2')], 'syl112anc', '( %s -> ( ( ( log ` X ) - 2 ) <_ %s <-> ( X x. ( ( log ` X ) - 2 ) ) <_ ( X x. %s ) ) )' % (HX, S, S))
w.qed([c, bi], 'mpbird', '( %s -> ( ( log ` X ) - 2 ) <_ %s )' % (HX, S)); run(w)


# ---- mertens1le
w = W('mertens1le', 'Mertens estimate, upper half with an explicit constant: the sum of ( Lam ` d ) / d over d up to X is at most log X + ( ( log 4 ) + 4 ).')
g = mertcommon(w)
A = g['A']
r1A = w.s([], '1red', '( %s -> 1 e. RR )' % A)
flt = w.s([g['rat'], w.inst('flltp1')], 'syl', '( %s -> ( X / d ) < ( ( |_ ` ( X / d ) ) + 1 ) )' % A)
p1r = w.s([g['fl'], r1A], 'readdcld', '( %s -> ( ( |_ ` ( X / d ) ) + 1 ) e. RR )' % A)
fltl = w.s([g['rat'], p1r, flt], 'ltled', '( %s -> ( X / d ) <_ ( ( |_ ` ( X / d ) ) + 1 ) )' % A)
tle2 = w.s([w.s([g['rat'], p1r, g['lamge']], '3jca', '( %s -> ( ( X / d ) e. RR /\\ ( ( |_ ` ( X / d ) ) + 1 ) e. RR /\\ ( ( Lam ` d ) e. RR /\\ 0 <_ ( Lam ` d ) ) ) )' % A), fltl, w.inst('lemul2a')], 'syl2anc', '( %s -> ( ( Lam ` d ) x. ( X / d ) ) <_ ( ( Lam ` d ) x. ( ( |_ ` ( X / d ) ) + 1 ) ) )' % A)
exp = w.s([g['lamc'], g['flc'], w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'adddid', '( %s -> ( ( Lam ` d ) x. ( ( |_ ` ( X / d ) ) + 1 ) ) = ( ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) + ( ( Lam ` d ) x. 1 ) ) )' % A)
m1 = w.s([g['lamc']], 'mulridd', '( %s -> ( ( Lam ` d ) x. 1 ) = ( Lam ` d ) )' % A)
exp2 = w.s([exp, w.s([m1], 'oveq2d', '( %s -> ( ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) + ( ( Lam ` d ) x. 1 ) ) = ( ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) + ( Lam ` d ) ) )' % A)], 'eqtrd', '( %s -> ( ( Lam ` d ) x. ( ( |_ ` ( X / d ) ) + 1 ) ) = ( ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) + ( Lam ` d ) ) )' % A)
tle3 = w.s([tle2, exp2], 'breqtrd', '( %s -> ( ( Lam ` d ) x. ( X / d ) ) <_ ( ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) + ( Lam ` d ) ) )' % A)
Cr = w.s([g['t2r'], g['lam']], 'readdcld', '( %s -> ( ( ( Lam ` d ) x. ( |_ ` ( X / d ) ) ) + ( Lam ` d ) ) e. RR )' % A)
le1 = w.s([g['fzfin'], g['t1r'], Cr, tle3], 'fsumle', '( %s -> %s <_ %s )' % (HX, T1, T3))
ad = w.s([g['fzfin'], g['t2c'], g['lamc']], 'fsumadd', '( %s -> %s = ( %s + %s ) )' % (HX, T3, T2, LAMS))
n1 = w.s([], 'fveq2', '( n = d -> ( Lam ` n ) = ( Lam ` d ) )')
cbn = w.s([n1], 'cbvsumv', '%s = %s' % (LAMSN, LAMS))
chp = w.s([w.s([g['xr'], w.inst('chpval')], 'syl', '( %s -> ( psi ` X ) = %s )' % (HX, LAMSN)), w.s([cbn], 'a1i', '( %s -> %s = %s )' % (HX, LAMSN, LAMS))], 'eqtrd', '( %s -> ( psi ` X ) = %s )' % (HX, LAMS))
chpr = w.s([chp], 'eqcomd', '( %s -> %s = ( psi ` X ) )' % (HX, LAMS))
t2lf = w.s([g['lfT2']], 'eqcomd', '( %s -> %s = %s )' % (HX, T2, LF))
ad2 = w.s([ad, w.s([t2lf, chpr], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + ( psi ` X ) ) )' % (HX, T2, LAMS, LF))], 'eqtrd', '( %s -> %s = ( %s + ( psi ` X ) ) )' % (HX, T3, LF))
ub = w.s([g['rp'], g['x1'], w.inst('logfacubnd')], 'syl2anc', '( %s -> %s <_ ( X x. ( log ` X ) ) )' % (HX, LF))
ple = w.s([g['xr'], g['x1'], w.inst('chple4')], 'syl2anc', '( %s -> ( psi ` X ) <_ ( %s x. X ) )' % (HX, B4))
l4r, l4eq = log4eq(w)
r4 = w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % HX)
b4r = w.s([w.s([l4r], 'a1i', '( %s -> %s e. RR )' % (HX, L4)), r4], 'readdcld', '( %s -> %s e. RR )' % (HX, B4))
LFr = w.s([g['lfT2'], g['T2r']], 'eqeltrd', '( %s -> %s e. RR )' % (HX, LF))
pcr = w.s([g['xr'], w.inst('chpcl')], 'syl', '( %s -> ( psi ` X ) e. RR )' % HX)
xlx = w.s([g['xr'], g['lx']], 'remulcld', '( %s -> ( X x. ( log ` X ) ) e. RR )' % HX)
b4x = w.s([b4r, g['xr']], 'remulcld', '( %s -> ( %s x. X ) e. RR )' % (HX, B4))
sum2 = w.s([LFr, pcr, xlx, b4x, ub, ple], 'le2addd', '( %s -> ( %s + ( psi ` X ) ) <_ ( ( X x. ( log ` X ) ) + ( %s x. X ) ) )' % (HX, LF, B4))
# ( ( X x. log X ) + ( B4 x. X ) ) = ( X x. ( log X + B4 ) )
b4c = w.s([b4r], 'recnd', '( %s -> %s e. CC )' % (HX, B4))
lxc = w.s([g['lx']], 'recnd', '( %s -> ( log ` X ) e. CC )' % HX)
dd = w.s([g['xc'], lxc, b4c], 'adddid', '( %s -> ( X x. ( ( log ` X ) + %s ) ) = ( ( X x. ( log ` X ) ) + ( X x. %s ) ) )' % (HX, B4, B4))
cm = w.s([g['xc'], b4c], 'mulcomd', '( %s -> ( X x. %s ) = ( %s x. X ) )' % (HX, B4, B4))
dd2 = w.s([dd, w.s([cm], 'oveq2d', '( %s -> ( ( X x. ( log ` X ) ) + ( X x. %s ) ) = ( ( X x. ( log ` X ) ) + ( %s x. X ) ) )' % (HX, B4, B4))], 'eqtrd', '( %s -> ( X x. ( ( log ` X ) + %s ) ) = ( ( X x. ( log ` X ) ) + ( %s x. X ) ) )' % (HX, B4, B4))
sumbig = w.s([w.s([g['lx'], b4r], 'readdcld', '( %s -> ( ( log ` X ) + %s ) e. RR )' % (HX, B4)), g['xr']], 'remulcld', '( %s -> ( X x. ( ( log ` X ) + %s ) ) e. RR )' % (HX, B4))
addr = w.s([xlx, b4x], 'readdcld', '( %s -> ( ( X x. ( log ` X ) ) + ( %s x. X ) ) e. RR )' % (HX, B4))
T3r = w.s([g['fzfin'], Cr], 'fsumrecl', '( %s -> %s e. RR )' % (HX, T3))
t3le = w.s([ad2, sum2], 'eqbrtrd', '( %s -> %s <_ ( ( X x. ( log ` X ) ) + ( %s x. X ) ) )' % (HX, T3, B4))
t3le2 = w.s([t3le, dd2], 'breqtrrd', '( %s -> %s <_ ( X x. ( ( log ` X ) + %s ) ) )' % (HX, T3, B4))
xsle = w.s([g['xS'], w.s([g['T1r'], T3r, sumbig, le1, t3le2], 'letrd', '( %s -> %s <_ ( X x. ( ( log ` X ) + %s ) ) )' % (HX, T1, B4))], 'eqbrtrd', '( %s -> ( X x. %s ) <_ ( X x. ( ( log ` X ) + %s ) ) )' % (HX, S, B4))
bi = w.s([g['Sr'], w.s([g['lx'], b4r], 'readdcld', '( %s -> ( ( log ` X ) + %s ) e. RR )' % (HX, B4)), g['xr'], g['x0'], w.inst('lemul2')], 'syl112anc', '( %s -> ( %s <_ ( ( log ` X ) + %s ) <-> ( X x. %s ) <_ ( X x. ( ( log ` X ) + %s ) ) ) )' % (HX, S, B4, S, B4))
w.qed([xsle, bi], 'mpbird', '( %s -> %s <_ ( ( log ` X ) + %s ) )' % (HX, S, B4)); run(w)


# ---- mertens1
w = W('mertens1', 'Mertens estimate with an explicit constant: the sum of ( Lam ` d ) / d over d up to X differs from log X by at most ( log 4 ) + 4 (Lean: Mertens.lean).')
xr = w.s([], 'simpl', '( %s -> X e. RR )' % HX); x1 = w.s([], 'simpr', '( %s -> 1 <_ X )' % HX)
rp, x0, xge = xrp(w, HX, xr, x1)
lx = w.s([rp, w.inst('relogcl')], 'syl', '( %s -> ( log ` X ) e. RR )' % HX)
fzfin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (HX, FZX))
A = '( %s /\\ d e. %s )' % (HX, FZX)
dnn = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (A, FZX)), w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % A)
lamdiv = w.s([w.s([dnn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` d ) e. RR )' % A), w.s([dnn], 'nnrpd', '( %s -> d e. RR+ )' % A)], 'rerpdivcld', '( %s -> ( ( Lam ` d ) / d ) e. RR )' % A)
Sr = w.s([fzfin, lamdiv], 'fsumrecl', '( %s -> %s e. RR )' % (HX, S))
l4r, l4eq = log4eq(w)
l4d = w.s([l4r], 'a1i', '( %s -> %s e. RR )' % (HX, L4))
r4 = w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % HX)
r1 = w.s([], '1red', '( %s -> 1 e. RR )' % HX)
r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % HX)
b4r = w.s([l4d, r4], 'readdcld', '( %s -> %s e. RR )' % (HX, B4))
ge = w.s([xr, x1, w.inst('mertens1ge')], 'syl2anc', '( %s -> ( ( log ` X ) - 2 ) <_ %s )' % (HX, S))
le = w.s([xr, x1, w.inst('mertens1le')], 'syl2anc', '( %s -> %s <_ ( ( log ` X ) + %s ) )' % (HX, S, B4))
sub = w.s([Sr, lx], 'resubcld', '( %s -> ( %s - ( log ` X ) ) e. RR )' % (HX, S))
# upper: S - log X <_ B4
up = w.s([Sr, lx, b4r, w.inst('lesubadd')], 'syl3anc', '( %s -> ( ( %s - ( log ` X ) ) <_ %s <-> %s <_ ( %s + ( log ` X ) ) ) )' % (HX, S, B4, S, B4))
cm = w.s([w.s([lx], 'recnd', '( %s -> ( log ` X ) e. CC )' % HX), w.s([b4r], 'recnd', '( %s -> %s e. CC )' % (HX, B4))], 'addcomd', '( %s -> ( ( log ` X ) + %s ) = ( %s + ( log ` X ) ) )' % (HX, B4, B4))
le2 = w.s([le, cm], 'breqtrd', '( %s -> %s <_ ( %s + ( log ` X ) ) )' % (HX, S, B4))
upper = w.s([le2, up], 'mpbird', '( %s -> ( %s - ( log ` X ) ) <_ %s )' % (HX, S, B4))
# 2 <_ B4
l41 = w.s([w.s([], 'ppiubepslem0', '1 < %s' % L4)], 'a1i', '( %s -> 1 < %s )' % (HX, L4))
l41l = w.s([r1, l4d, l41], 'ltled', '( %s -> 1 <_ %s )' % (HX, L4))
ad5 = w.s([r1, l4d, r4, l41l], 'leadd1dd', '( %s -> ( 1 + 4 ) <_ %s )' % (HX, B4))
e5 = w.s([w.s([], '1p4e5', '( 1 + 4 ) = 5')], 'a1i', '( %s -> ( 1 + 4 ) = 5 )' % HX)
ge5 = w.s([e5, ad5], 'eqbrtrrd', '( %s -> 5 <_ %s )' % (HX, B4))
r5 = w.s([w.s([], '5re', '5 e. RR')], 'a1i', '( %s -> 5 e. RR )' % HX)
l25 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], '5re', '5 e. RR'), w.s([], '2lt5', '2 < 5')], 'ltleii', '2 <_ 5')], 'a1i', '( %s -> 2 <_ 5 )' % HX)
b42 = w.s([r2, r5, b4r, l25, ge5], 'letrd', '( %s -> 2 <_ %s )' % (HX, B4))
# lower: -u B4 <_ S - log X
a2 = w.s([ge, w.s([lx, r2, Sr, w.inst('lesubadd')], 'syl3anc', '( %s -> ( ( ( log ` X ) - 2 ) <_ %s <-> ( log ` X ) <_ ( %s + 2 ) ) )' % (HX, S, S))], 'mpbid', '( %s -> ( log ` X ) <_ ( %s + 2 ) )' % (HX, S))
a4 = w.s([r2, b4r, Sr, b42], 'leadd2dd', '( %s -> ( %s + 2 ) <_ ( %s + %s ) )' % (HX, S, S, B4))
a5 = w.s([lx, w.s([Sr, r2], 'readdcld', '( %s -> ( %s + 2 ) e. RR )' % (HX, S)), w.s([Sr, b4r], 'readdcld', '( %s -> ( %s + %s ) e. RR )' % (HX, S, B4)), a2, a4], 'letrd', '( %s -> ( log ` X ) <_ ( %s + %s ) )' % (HX, S, B4))
a6 = w.s([a5, w.s([w.s([Sr], 'recnd', '( %s -> %s e. CC )' % (HX, S)), w.s([b4r], 'recnd', '( %s -> %s e. CC )' % (HX, B4))], 'addcomd', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (HX, S, B4, B4, S))], 'breqtrd', '( %s -> ( log ` X ) <_ ( %s + %s ) )' % (HX, B4, S))
a7 = w.s([a6, w.s([lx, Sr, b4r, w.inst('lesubadd')], 'syl3anc', '( %s -> ( ( ( log ` X ) - %s ) <_ %s <-> ( log ` X ) <_ ( %s + %s ) ) )' % (HX, S, B4, B4, S))], 'mpbird', '( %s -> ( ( log ` X ) - %s ) <_ %s )' % (HX, S, B4))
a8 = w.s([w.s([w.s([Sr], 'recnd', '( %s -> %s e. CC )' % (HX, S)), w.s([lx], 'recnd', '( %s -> ( log ` X ) e. CC )' % HX)], 'negsubdi2d', '( %s -> -u ( %s - ( log ` X ) ) = ( ( log ` X ) - %s ) )' % (HX, S, S)), a7], 'eqbrtrd', '( %s -> -u ( %s - ( log ` X ) ) <_ %s )' % (HX, S, B4))
a9 = w.s([a8, w.s([sub, b4r, w.inst('lenegcon1')], 'syl2anc', '( %s -> ( -u ( %s - ( log ` X ) ) <_ %s <-> -u %s <_ ( %s - ( log ` X ) ) ) )' % (HX, S, B4, B4, S))], 'mpbid', '( %s -> -u %s <_ ( %s - ( log ` X ) ) )' % (HX, B4, S))
ab = w.s([sub, b4r], 'absled', '( %s -> ( ( abs ` ( %s - ( log ` X ) ) ) <_ %s <-> ( -u %s <_ ( %s - ( log ` X ) ) /\\ ( %s - ( log ` X ) ) <_ %s ) ) )' % (HX, S, B4, B4, S, S, B4))
w.qed([w.s([a9, upper], 'jca', '( %s -> ( -u %s <_ ( %s - ( log ` X ) ) /\\ ( %s - ( log ` X ) ) <_ %s ) )' % (HX, B4, S, S, B4)), ab], 'mpbird', '( %s -> ( abs ` ( %s - ( log ` X ) ) ) <_ %s )' % (HX, S, B4)); run(w)
