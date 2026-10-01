"""Sortie C0, batch 6: reversal and splitting of the segment integral
(lintrev, lintsplit) from the affine reparametrisation ditgaff."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from c0lib import *
only = sys.argv[1:]
def run(w, h=False):
    if only and w.label not in only: return True
    return runh(w) if h else w.run()

def IG(x, X='A', Y='B'):
    """the integrand of the segment integral from X to Y at x"""
    return INTG('F', X, Y, x)
HH = '( w e. ( 0 [,] 1 ) |-> %s )' % IG('w')


def igsub(w, frm, to, X='A', Y='B'):
    """closed step ( frm = to -> IG ( frm ) = IG ( to ) )"""
    e = w.s([], 'oveq1', '( %s = %s -> ( %s x. ( %s - %s ) ) = ( %s x. ( %s - %s ) ) )' % (frm, to, frm, Y, X, to, Y, X))
    o = w.s([e], 'oveq2d', '( %s = %s -> %s = %s )' % (frm, to, LIN(X, Y, frm), LIN(X, Y, to)))
    f = w.s([o], 'fveq2d', '( %s = %s -> ( F ` %s ) = ( F ` %s ) )' % (frm, to, LIN(X, Y, frm), LIN(X, Y, to)))
    return w.s([f], 'oveq1d', '( %s = %s -> %s = %s )' % (frm, to, IG(frm, X, Y), IG(to, X, Y)))


def hhval(w, x):
    """closed step ( x e. ( 0 [,] 1 ) -> ( HH ` x ) = IG ( x ) )"""
    s = igsub(w, 'w', x)
    e = w.s([], 'eqid', '%s = %s' % (HH, HH))
    v = w.s([], 'ovex', '%s e. _V' % IG(x))
    return w.s([s, e, v], 'fvmpt', '( %s e. ( 0 [,] 1 ) -> ( %s ` %s ) = %s )' % (x, HH, x, IG(x)))


def hhcn(w, ante, a, b, f, g):
    """( ante -> HH e. ( ( 0 [,] 1 ) -cn-> CC ) )"""
    ab = w.s([a, b], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % ante)
    fg = w.s([f, g], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )' % ante)
    si = w.s([], 'ssidd', '( %s -> ( 0 [,] 1 ) C_ ( 0 [,] 1 ) )' % ante)
    cn = w.s([ab, fg, si, w.inst('lintcnlem')], 'syl3anc', '( %s -> ( t e. ( 0 [,] 1 ) |-> %s ) e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (ante, IG('t')))
    sb = igsub(w, 't', 'w')
    cb = w.s([sb], 'cbvmptv', '( t e. ( 0 [,] 1 ) |-> %s ) = %s' % (IG('t'), HH))
    cbd = w.s([cb], 'a1i', '( %s -> ( t e. ( 0 [,] 1 ) |-> %s ) = %s )' % (ante, IG('t'), HH))
    return w.s([cbd, cn], 'eqeltrrd', '( %s -> %s e. ( ( 0 [,] 1 ) -cn-> CC ) )' % (ante, HH))


def hhitg(w, ante, a, b, f, X='A', Y='B'):
    """( ante -> S. ( 0 (,) 1 ) ( HH ` s ) _d s = ( F lint <. X , Y >. ) )"""
    sb = w.s([], 'fveq2', '( s = t -> ( %s ` s ) = ( %s ` t ) )' % (HH, HH))
    cbi = w.s([sb], 'cbvitgv', 'S. ( 0 (,) 1 ) ( %s ` s ) _d s = S. ( 0 (,) 1 ) ( %s ` t ) _d t' % (HH, HH))
    cbid = w.s([cbi], 'a1i', '( %s -> S. ( 0 (,) 1 ) ( %s ` s ) _d s = S. ( 0 (,) 1 ) ( %s ` t ) _d t )' % (ante, HH, HH))
    AT = '( %s /\\ t e. ( 0 (,) 1 ) )' % ante
    to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AT)
    ss = closed(w, AT, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
    t01 = w.s([ss, to], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % AT)
    hv = hhval(w, 't')
    hvt = w.s([t01, hv], 'syl', '( %s -> ( %s ` t ) = %s )' % (AT, HH, IG('t')))
    ie = w.s([hvt], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) ( %s ` t ) _d t = S. ( 0 (,) 1 ) %s _d t )' % (ante, HH, IG('t')))
    c1 = w.s([cbid, ie], 'eqtrd', '( %s -> S. ( 0 (,) 1 ) ( %s ` s ) _d s = S. ( 0 (,) 1 ) %s _d t )' % (ante, HH, IG('t')))
    lv = w.s([f, a, b, w.inst('lintval')], 'syl3anc', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (ante, LINT('F', 'A', 'B'), IG('t')))
    return w.s([c1, lv], 'eqtr4d', '( %s -> S. ( 0 (,) 1 ) ( %s ` s ) _d s = %s )' % (ante, HH, LINT('F', 'A', 'B')))


# ---- lintrev
w = W('lintrev', 'Reversing the orientation of a segment negates the segment integral.')
a, b, f, g = phctx(w, PH)
hcn = hhcn(w, PH, a, b, f, g)
u1 = closed(w, PH, '1elunit', '1 e. ( 0 [,] 1 )'); u0 = closed(w, PH, '0elunit', '0 e. ( 0 [,] 1 )')
ARG = '( 1 + ( t x. ( 0 - 1 ) ) )'
RI = 'S. ( 0 (,) 1 ) ( ( %s ` %s ) x. ( 0 - 1 ) ) _d t' % (HH, ARG)
LD = 'S_ [ 1 -> 0 ] ( %s ` s ) _d s' % HH
da = w.s([hcn, u1, u0, w.inst('ditgaff')], 'syl3anc', '( %s -> %s = %s )' % (PH, LD, RI))
# the directed integral from 1 to 0 is the negative of the segment integral
r0 = w.s([], '0red', '( %s -> 0 e. RR )' % PH); r1 = w.s([], '1red', '( %s -> 1 e. RR )' % PH)
le = closed(w, PH, '0le1', '0 <_ 1')
dn = w.s([le, r0, r1], 'ditgneg', '( %s -> %s = -u S. ( 0 (,) 1 ) ( %s ` s ) _d s )' % (PH, LD, HH))
it = hhitg(w, PH, a, b, f)
ng = w.s([it], 'negeqd', '( %s -> -u S. ( 0 (,) 1 ) ( %s ` s ) _d s = -u %s )' % (PH, HH, LINT('F', 'A', 'B')))
lhs = w.s([dn, ng], 'eqtrd', '( %s -> %s = -u %s )' % (PH, LD, LINT('F', 'A', 'B')))
# the reparametrised integrand is the integrand of the reversed segment
AT = '( %s /\\ t e. ( 0 (,) 1 ) )' % PH
a2 = w.s([a], 'adantr', '( %s -> A e. CC )' % AT); b2 = w.s([b], 'adantr', '( %s -> B e. CC )' % AT)
f2 = w.s([f], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % AT); g2 = w.s([g], 'adantr', '( %s -> ( A cseg B ) C_ D )' % AT)
to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AT)
ss = closed(w, AT, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
t01 = w.s([ss, to], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % AT)
c1d = closed(w, AT, 'ax-1cn', '1 e. CC'); c0d = closed(w, AT, '0cn', '0 e. CC')
lseg = w.s([c1d, c0d, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( 1 cseg 0 ) )' % (AT, ARG))
j1 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % AT), w.s([], '1red', '( %s -> 1 e. RR )' % AT)], 'jca', '( %s -> ( 0 e. RR /\\ 1 e. RR ) )' % AT)
u1b = closed(w, AT, '1elunit', '1 e. ( 0 [,] 1 )'); u0b = closed(w, AT, '0elunit', '0 e. ( 0 [,] 1 )')
j2 = w.s([u1b, u0b], 'jca', '( %s -> ( 1 e. ( 0 [,] 1 ) /\\ 0 e. ( 0 [,] 1 ) ) )' % AT)
s10 = w.s([j1, j2, w.inst('csegicc')], 'syl2anc', '( %s -> ( 1 cseg 0 ) C_ ( 0 [,] 1 ) )' % AT)
arg01 = w.s([s10, lseg], 'sseldd', '( %s -> %s e. ( 0 [,] 1 ) )' % (AT, ARG))
hva = hhval(w, ARG)
hv = w.s([arg01, hva], 'syl', '( %s -> ( %s ` %s ) = %s )' % (AT, HH, ARG, IG(ARG)))
hvo = w.s([hv], 'oveq1d', '( %s -> ( ( %s ` %s ) x. ( 0 - 1 ) ) = ( %s x. ( 0 - 1 ) ) )' % (AT, HH, ARG, IG(ARG)))
# ARG = ( 1 - t )
dn1 = w.s([], 'df-neg', '-u 1 = ( 0 - 1 )'); dn2 = w.s([dn1], 'eqcomi', '( 0 - 1 ) = -u 1')
dn2d = w.s([dn2], 'a1i', '( %s -> ( 0 - 1 ) = -u 1 )' % AT)
tc = w.s([t01, w.inst('elunitcn')], 'syl', '( %s -> t e. CC )' % AT)
q1 = w.s([dn2d], 'oveq2d', '( %s -> ( t x. ( 0 - 1 ) ) = ( t x. -u 1 ) )' % AT)
q2 = w.s([tc, c1d], 'mulneg2d', '( %s -> ( t x. -u 1 ) = -u ( t x. 1 ) )' % AT)
q3 = w.s([tc], 'mulridd', '( %s -> ( t x. 1 ) = t )' % AT)
q4 = w.s([q3], 'negeqd', '( %s -> -u ( t x. 1 ) = -u t )' % AT)
q5 = w.s([w.s([q1, q2], 'eqtrd', '( %s -> ( t x. ( 0 - 1 ) ) = -u ( t x. 1 ) )' % AT), q4], 'eqtrd', '( %s -> ( t x. ( 0 - 1 ) ) = -u t )' % AT)
q6 = w.s([q5], 'oveq2d', '( %s -> %s = ( 1 + -u t ) )' % (AT, ARG))
q7 = w.s([c1d, tc], 'negsubd', '( %s -> ( 1 + -u t ) = ( 1 - t ) )' % AT)
arg = w.s([q6, q7], 'eqtrd', '( %s -> %s = ( 1 - t ) )' % (AT, ARG))
# the point of the segment is the point of the reversed segment
l1 = w.s([arg], 'oveq1d', '( %s -> ( %s x. ( B - A ) ) = ( ( 1 - t ) x. ( B - A ) ) )' % (AT, ARG))
l2 = w.s([l1], 'oveq2d', '( %s -> %s = ( A + ( ( 1 - t ) x. ( B - A ) ) ) )' % (AT, LIN('A', 'B', ARG)))
rev = w.s([a2, b2, tc, w.inst('cseglinrev')], 'syl3anc', '( %s -> ( A + ( ( 1 - t ) x. ( B - A ) ) ) = %s )' % (AT, LIN('B', 'A', 't')))
l3 = w.s([l2, rev], 'eqtrd', '( %s -> %s = %s )' % (AT, LIN('A', 'B', ARG), LIN('B', 'A', 't')))
fv = w.s([l3], 'fveq2d', '( %s -> ( F ` %s ) = ( F ` %s ) )' % (AT, LIN('A', 'B', ARG), LIN('B', 'A', 't')))
# the constant factor
X = '( F ` %s )' % LIN('A', 'B', ARG)
lsg2 = w.s([a2, b2, arg01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (AT, LIN('A', 'B', ARG)))
ld = w.s([g2, lsg2], 'sseldd', '( %s -> %s e. D )' % (AT, LIN('A', 'B', ARG)))
ff = w.s([f2, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % AT)
xc = w.s([ff, ld], 'ffvelcdmd', '( %s -> %s e. CC )' % (AT, X))
ba = w.s([b2, a2], 'subcld', '( %s -> ( B - A ) e. CC )' % AT)
m1c = w.s([c0d, c1d], 'subcld', '( %s -> ( 0 - 1 ) e. CC )' % AT)
mas = w.s([xc, ba, m1c], 'mulassd', '( %s -> ( %s x. ( 0 - 1 ) ) = ( %s x. ( ( B - A ) x. ( 0 - 1 ) ) ) )' % (AT, IG(ARG), X))
n1 = w.s([dn2d], 'oveq2d', '( %s -> ( ( B - A ) x. ( 0 - 1 ) ) = ( ( B - A ) x. -u 1 ) )' % AT)
n2 = w.s([ba, c1d], 'mulneg2d', '( %s -> ( ( B - A ) x. -u 1 ) = -u ( ( B - A ) x. 1 ) )' % AT)
n3 = w.s([ba], 'mulridd', '( %s -> ( ( B - A ) x. 1 ) = ( B - A ) )' % AT)
n4 = w.s([n3], 'negeqd', '( %s -> -u ( ( B - A ) x. 1 ) = -u ( B - A ) )' % AT)
n5 = w.s([b2, a2], 'negsubdi2d', '( %s -> -u ( B - A ) = ( A - B ) )' % AT)
n6 = w.s([w.s([w.s([n1, n2], 'eqtrd', '( %s -> ( ( B - A ) x. ( 0 - 1 ) ) = -u ( ( B - A ) x. 1 ) )' % AT), n4], 'eqtrd', '( %s -> ( ( B - A ) x. ( 0 - 1 ) ) = -u ( B - A ) )' % AT), n5], 'eqtrd', '( %s -> ( ( B - A ) x. ( 0 - 1 ) ) = ( A - B ) )' % AT)
mas2 = w.s([n6], 'oveq2d', '( %s -> ( %s x. ( ( B - A ) x. ( 0 - 1 ) ) ) = ( %s x. ( A - B ) ) )' % (AT, X, X))
mas3 = w.s([mas, mas2], 'eqtrd', '( %s -> ( %s x. ( 0 - 1 ) ) = ( %s x. ( A - B ) ) )' % (AT, IG(ARG), X))
fo = w.s([fv], 'oveq1d', '( %s -> ( %s x. ( A - B ) ) = %s )' % (AT, X, IG('t', 'B', 'A')))
pw = w.s([w.s([hvo, mas3], 'eqtrd', '( %s -> ( ( %s ` %s ) x. ( 0 - 1 ) ) = ( %s x. ( A - B ) ) )' % (AT, HH, ARG, X)), fo], 'eqtrd', '( %s -> ( ( %s ` %s ) x. ( 0 - 1 ) ) = %s )' % (AT, HH, ARG, IG('t', 'B', 'A')))
ie2 = w.s([pw], 'itgeq2dv', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (PH, RI, IG('t', 'B', 'A')))
lv2 = w.s([f, b, a, w.inst('lintval')], 'syl3anc', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (PH, LINT('F', 'B', 'A'), IG('t', 'B', 'A')))
rhs = w.s([ie2, lv2], 'eqtr4d', '( %s -> %s = %s )' % (PH, RI, LINT('F', 'B', 'A')))
x1 = w.s([da, lhs], 'eqtr3d', '( %s -> %s = -u %s )' % (PH, RI, LINT('F', 'A', 'B')))
w.qed([rhs, x1], 'eqtr3d', '( %s -> %s = -u %s )' % (PH, LINT('F', 'B', 'A'), LINT('F', 'A', 'B'))); run(w)

# ---- lintsplit
PS = '( %s /\\ S e. ( 0 [,] 1 ) /\\ C = %s )' % (PH, LIN('A', 'B', 'S'))
w = W('lintsplit', 'Splitting a segment integral at a point of the segment.')
p = w.s([], 'simp1', '( %s -> %s )' % (PS, PH))
s01 = w.s([], 'simp2', '( %s -> S e. ( 0 [,] 1 ) )' % PS)
ceq = w.s([], 'simp3', '( %s -> C = %s )' % (PS, LIN('A', 'B', 'S')))
a, b, f, g = phfrom(w, PS, p)
sc = w.s([s01, w.inst('elunitcn')], 'syl', '( %s -> S e. CC )' % PS)
ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % PS)
sba = w.s([sc, ba], 'mulcld', '( %s -> ( S x. ( B - A ) ) e. CC )' % PS)
cc = w.s([ceq, w.s([a, sba], 'addcld', '( %s -> %s e. CC )' % (PS, LIN('A', 'B', 'S')))], 'eqeltrd', '( %s -> C e. CC )' % PS)
ca = w.s([cc, a], 'subcld', '( %s -> ( C - A ) e. CC )' % PS)
bc = w.s([b, cc], 'subcld', '( %s -> ( B - C ) e. CC )' % PS)
# ( C - A ) = ( S x. ( B - A ) )
q1 = w.s([ceq], 'oveq1d', '( %s -> ( C - A ) = ( %s - A ) )' % (PS, LIN('A', 'B', 'S')))
q2 = w.s([a, sba], 'pncan2d', '( %s -> ( %s - A ) = ( S x. ( B - A ) ) )' % (PS, LIN('A', 'B', 'S')))
cma = w.s([q1, q2], 'eqtrd', '( %s -> ( C - A ) = ( S x. ( B - A ) ) )' % PS)
# ( ( 1 - S ) x. ( B - A ) ) = ( B - C )
c1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % PS)
r1 = w.s([c1, sc, ba], 'subdird', '( %s -> ( ( 1 - S ) x. ( B - A ) ) = ( ( 1 x. ( B - A ) ) - ( S x. ( B - A ) ) ) )' % PS)
r2 = w.s([ba], 'mullidd', '( %s -> ( 1 x. ( B - A ) ) = ( B - A ) )' % PS)
r3 = w.s([cma], 'eqcomd', '( %s -> ( S x. ( B - A ) ) = ( C - A ) )' % PS)
r4 = w.s([r2, r3], 'oveq12d', '( %s -> ( ( 1 x. ( B - A ) ) - ( S x. ( B - A ) ) ) = ( ( B - A ) - ( C - A ) ) )' % PS)
r5 = w.s([b, cc, a, w.inst('nnncan2')], 'syl3anc', '( %s -> ( ( B - A ) - ( C - A ) ) = ( B - C ) )' % PS)
bmc = w.s([w.s([r1, r4], 'eqtrd', '( %s -> ( ( 1 - S ) x. ( B - A ) ) = ( ( B - A ) - ( C - A ) ) )' % PS), r5], 'eqtrd', '( %s -> ( ( 1 - S ) x. ( B - A ) ) = ( B - C ) )' % PS)
# the integrand as a function on the closed unit interval
hcn = hhcn(w, PS, a, b, f, g)
u1 = closed(w, PS, '1elunit', '1 e. ( 0 [,] 1 )'); u0 = closed(w, PS, '0elunit', '0 e. ( 0 [,] 1 )')
r0d = w.s([], '0red', '( %s -> 0 e. RR )' % PS); r1d = w.s([], '1red', '( %s -> 1 e. RR )' % PS)
le = closed(w, PS, '0le1', '0 <_ 1')
D01 = 'S_ [ 0 -> 1 ] ( %s ` s ) _d s' % HH
D0S = 'S_ [ 0 -> S ] ( %s ` s ) _d s' % HH
DS1 = 'S_ [ S -> 1 ] ( %s ` s ) _d s' % HH
dp = w.s([le], 'ditgpos', '( %s -> %s = S. ( 0 (,) 1 ) ( %s ` s ) _d s )' % (PS, D01, HH))
it = hhitg(w, PS, a, b, f)
tot = w.s([dp, it], 'eqtrd', '( %s -> %s = %s )' % (PS, D01, LINT('F', 'A', 'B')))
# splitting at S
AS = '( %s /\\ s e. ( 0 (,) 1 ) )' % PS
so = w.s([], 'simpr', '( %s -> s e. ( 0 (,) 1 ) )' % AS)
sss = closed(w, AS, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
ss01 = w.s([sss, so], 'sseldd', '( %s -> s e. ( 0 [,] 1 ) )' % AS)
hf = w.s([w.s([hcn, w.inst('cncff')], 'syl', '( %s -> %s : ( 0 [,] 1 ) --> CC )' % (PS, HH))], 'adantr', '( %s -> %s : ( 0 [,] 1 ) --> CC )' % (AS, HH))
hsv = w.s([hf, ss01], 'ffvelcdmd', '( %s -> ( %s ` s ) e. CC )' % (AS, HH))
ibl = w.s([hcn, w.inst('iblcnunit')], 'syl', '( %s -> ( s e. ( 0 (,) 1 ) |-> ( %s ` s ) ) e. L^1 )' % (PS, HH))
spl = w.s([r0d, r1d, u0, s01, u1, hsv, ibl], 'ditgsplit', '( %s -> %s = ( %s + %s ) )' % (PS, D01, D0S, DS1))
# the first piece
AT = '( %s /\\ t e. ( 0 (,) 1 ) )' % PS
a2 = w.s([a], 'adantr', '( %s -> A e. CC )' % AT); b2 = w.s([b], 'adantr', '( %s -> B e. CC )' % AT)
c2 = w.s([cc], 'adantr', '( %s -> C e. CC )' % AT); s2 = w.s([sc], 'adantr', '( %s -> S e. CC )' % AT)
f2 = w.s([f], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % AT); g2 = w.s([g], 'adantr', '( %s -> ( A cseg B ) C_ D )' % AT)
ba2 = w.s([ba], 'adantr', '( %s -> ( B - A ) e. CC )' % AT); ca2 = w.s([ca], 'adantr', '( %s -> ( C - A ) e. CC )' % AT)
bc2 = w.s([bc], 'adantr', '( %s -> ( B - C ) e. CC )' % AT)
cma2 = w.s([cma], 'adantr', '( %s -> ( C - A ) = ( S x. ( B - A ) ) )' % AT)
bmc2 = w.s([bmc], 'adantr', '( %s -> ( ( 1 - S ) x. ( B - A ) ) = ( B - C ) )' % AT)
to = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % AT)
sst = closed(w, AT, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
t01 = w.s([sst, to], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % AT)
tc = w.s([t01, w.inst('elunitcn')], 'syl', '( %s -> t e. CC )' % AT)
ff = w.s([f2, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % AT)
s012 = w.s([s01], 'adantr', '( %s -> S e. ( 0 [,] 1 ) )' % AT)
u0b = closed(w, AT, '0elunit', '0 e. ( 0 [,] 1 )'); u1b = closed(w, AT, '1elunit', '1 e. ( 0 [,] 1 )')
r0b = w.s([], '0red', '( %s -> 0 e. RR )' % AT); r1b = w.s([], '1red', '( %s -> 1 e. RR )' % AT)
jr = w.s([r0b, r1b], 'jca', '( %s -> ( 0 e. RR /\\ 1 e. RR ) )' % AT)


def piece(w, P, Q, pcn, qcn, p01s, q01s, X, Y, fac, facid, argid):
    """( AT -> ( ( HH ` ARG ) x. fac ) = IG ( t , X , Y ) ) where ARG is the
    reparametrisation of ( P , Q ) at t; facid proves ( ( B - A ) x. fac ) = ( Y - X ),
    argid proves ( A + ( ARG x. ( B - A ) ) ) = LIN ( X , Y , t )"""
    ARG = LIN(P, Q, 't')
    lseg = w.s([pcn, qcn, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( %s cseg %s ) )' % (AT, ARG, P, Q))
    jj = w.s([p01s, q01s], 'jca', '( %s -> ( %s e. ( 0 [,] 1 ) /\\ %s e. ( 0 [,] 1 ) ) )' % (AT, P, Q))
    sg = w.s([jr, jj, w.inst('csegicc')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( 0 [,] 1 ) )' % (AT, P, Q))
    a01 = w.s([sg, lseg], 'sseldd', '( %s -> %s e. ( 0 [,] 1 ) )' % (AT, ARG))
    hv = w.s([a01, hhval(w, ARG)], 'syl', '( %s -> ( %s ` %s ) = %s )' % (AT, HH, ARG, IG(ARG)))
    hvo = w.s([hv], 'oveq1d', '( %s -> ( ( %s ` %s ) x. %s ) = ( %s x. %s ) )' % (AT, HH, ARG, fac, IG(ARG), fac))
    XX = '( F ` %s )' % LIN('A', 'B', ARG)
    ls2 = w.s([a2, b2, a01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (AT, LIN('A', 'B', ARG)))
    ld = w.s([g2, ls2], 'sseldd', '( %s -> %s e. D )' % (AT, LIN('A', 'B', ARG)))
    xc = w.s([ff, ld], 'ffvelcdmd', '( %s -> %s e. CC )' % (AT, XX))
    mas = w.s([xc, ba2, fac_cl[fac]], 'mulassd', '( %s -> ( %s x. %s ) = ( %s x. ( ( B - A ) x. %s ) ) )' % (AT, IG(ARG), fac, XX, fac))
    m2 = w.s([facid], 'oveq2d', '( %s -> ( %s x. ( ( B - A ) x. %s ) ) = ( %s x. ( %s - %s ) ) )' % (AT, XX, fac, XX, Y, X))
    m3 = w.s([mas, m2], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s x. ( %s - %s ) ) )' % (AT, IG(ARG), fac, XX, Y, X))
    fv = w.s([argid], 'fveq2d', '( %s -> %s = ( F ` %s ) )' % (AT, XX, LIN(X, Y, 't')))
    fo = w.s([fv], 'oveq1d', '( %s -> ( %s x. ( %s - %s ) ) = %s )' % (AT, XX, Y, X, IG('t', X, Y)))
    m4 = w.s([m3, fo], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (AT, IG(ARG), fac, IG('t', X, Y)))
    return w.s([hvo, m4], 'eqtrd', '( %s -> ( ( %s ` %s ) x. %s ) = %s )' % (AT, HH, ARG, fac, IG('t', X, Y)))


# closures of the two scalar factors
s0c = w.s([s2, w.s([], '0cnd', '( %s -> 0 e. CC )' % AT)], 'subcld', '( %s -> ( S - 0 ) e. CC )' % AT)
c1b = w.s([], '1cnd', '( %s -> 1 e. CC )' % AT)
s1c = w.s([c1b, s2], 'subcld', '( %s -> ( 1 - S ) e. CC )' % AT)
fac_cl = {'( S - 0 )': s0c, '( 1 - S )': s1c}
# first piece: ( 0 , S )
ARG1 = LIN('0', 'S', 't')
si0 = w.s([s2], 'subid1d', '( %s -> ( S - 0 ) = S )' % AT)
g1a = w.s([si0], 'oveq2d', '( %s -> ( t x. ( S - 0 ) ) = ( t x. S ) )' % AT)
g1b = w.s([g1a], 'oveq2d', '( %s -> %s = ( 0 + ( t x. S ) ) )' % (AT, ARG1))
tsc = w.s([tc, s2], 'mulcld', '( %s -> ( t x. S ) e. CC )' % AT)
g1c = w.s([tsc], 'addlidd', '( %s -> ( 0 + ( t x. S ) ) = ( t x. S ) )' % AT)
arg1 = w.s([g1b, g1c], 'eqtrd', '( %s -> %s = ( t x. S ) )' % (AT, ARG1))
h1a = w.s([arg1], 'oveq1d', '( %s -> ( %s x. ( B - A ) ) = ( ( t x. S ) x. ( B - A ) ) )' % (AT, ARG1))
h1b = w.s([tc, s2, ba2], 'mulassd', '( %s -> ( ( t x. S ) x. ( B - A ) ) = ( t x. ( S x. ( B - A ) ) ) )' % AT)
h1c = w.s([cma2], 'oveq2d', '( %s -> ( t x. ( C - A ) ) = ( t x. ( S x. ( B - A ) ) ) )' % AT)
h1d = w.s([w.s([h1a, h1b], 'eqtrd', '( %s -> ( %s x. ( B - A ) ) = ( t x. ( S x. ( B - A ) ) ) )' % (AT, ARG1)), h1c], 'eqtr4d', '( %s -> ( %s x. ( B - A ) ) = ( t x. ( C - A ) ) )' % (AT, ARG1))
argid1 = w.s([h1d], 'oveq2d', '( %s -> %s = %s )' % (AT, LIN('A', 'B', ARG1), LIN('A', 'C', 't')))
k1a = w.s([si0], 'oveq2d', '( %s -> ( ( B - A ) x. ( S - 0 ) ) = ( ( B - A ) x. S ) )' % AT)
k1b = w.s([ba2, s2], 'mulcomd', '( %s -> ( ( B - A ) x. S ) = ( S x. ( B - A ) ) )' % AT)
k1c = w.s([cma2], 'eqcomd', '( %s -> ( S x. ( B - A ) ) = ( C - A ) )' % AT)
facid1 = w.s([w.s([k1a, k1b], 'eqtrd', '( %s -> ( ( B - A ) x. ( S - 0 ) ) = ( S x. ( B - A ) ) )' % AT), k1c], 'eqtrd', '( %s -> ( ( B - A ) x. ( S - 0 ) ) = ( C - A ) )' % AT)
c0c = w.s([], '0cnd', '( %s -> 0 e. CC )' % AT)
pw1 = piece(w, '0', 'S', c0c, s2, u0b, s012, 'A', 'C', '( S - 0 )', facid1, argid1)
ie1 = w.s([pw1], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) ( ( %s ` %s ) x. ( S - 0 ) ) _d t = S. ( 0 (,) 1 ) %s _d t )' % (PS, HH, ARG1, IG('t', 'A', 'C')))
daf1 = w.s([hcn, u0, s01, w.inst('ditgaff')], 'syl3anc', '( %s -> %s = S. ( 0 (,) 1 ) ( ( %s ` %s ) x. ( S - 0 ) ) _d t )' % (PS, D0S, HH, ARG1))
lv1 = w.s([f, a, cc, w.inst('lintval')], 'syl3anc', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (PS, LINT('F', 'A', 'C'), IG('t', 'A', 'C')))
p1 = w.s([w.s([daf1, ie1], 'eqtrd', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (PS, D0S, IG('t', 'A', 'C'))), lv1], 'eqtr4d', '( %s -> %s = %s )' % (PS, D0S, LINT('F', 'A', 'C')))
# second piece: ( S , 1 )
ARG2 = LIN('S', '1', 't')
t1s = w.s([tc, s1c], 'mulcld', '( %s -> ( t x. ( 1 - S ) ) e. CC )' % AT)
j2a = w.s([s2, t1s, ba2], 'adddird', '( %s -> ( %s x. ( B - A ) ) = ( ( S x. ( B - A ) ) + ( ( t x. ( 1 - S ) ) x. ( B - A ) ) ) )' % (AT, ARG2))
j2b = w.s([tc, s1c, ba2], 'mulassd', '( %s -> ( ( t x. ( 1 - S ) ) x. ( B - A ) ) = ( t x. ( ( 1 - S ) x. ( B - A ) ) ) )' % AT)
j2c = w.s([bmc2], 'oveq2d', '( %s -> ( t x. ( ( 1 - S ) x. ( B - A ) ) ) = ( t x. ( B - C ) ) )' % AT)
j2d = w.s([j2b, j2c], 'eqtrd', '( %s -> ( ( t x. ( 1 - S ) ) x. ( B - A ) ) = ( t x. ( B - C ) ) )' % AT)
j2e = w.s([w.s([cma2], 'eqcomd', '( %s -> ( S x. ( B - A ) ) = ( C - A ) )' % AT), j2d], 'oveq12d', '( %s -> ( ( S x. ( B - A ) ) + ( ( t x. ( 1 - S ) ) x. ( B - A ) ) ) = ( ( C - A ) + ( t x. ( B - C ) ) ) )' % AT)
j2f = w.s([j2a, j2e], 'eqtrd', '( %s -> ( %s x. ( B - A ) ) = ( ( C - A ) + ( t x. ( B - C ) ) ) )' % (AT, ARG2))
j2g = w.s([j2f], 'oveq2d', '( %s -> %s = ( A + ( ( C - A ) + ( t x. ( B - C ) ) ) ) )' % (AT, LIN('A', 'B', ARG2)))
tbc = w.s([tc, bc2], 'mulcld', '( %s -> ( t x. ( B - C ) ) e. CC )' % AT)
j2h = w.s([a2, ca2, tbc], 'addassd', '( %s -> ( ( A + ( C - A ) ) + ( t x. ( B - C ) ) ) = ( A + ( ( C - A ) + ( t x. ( B - C ) ) ) ) )' % AT)
j2i = w.s([a2, c2, w.inst('pncan3')], 'syl2anc', '( %s -> ( A + ( C - A ) ) = C )' % AT)
j2j = w.s([j2i], 'oveq1d', '( %s -> ( ( A + ( C - A ) ) + ( t x. ( B - C ) ) ) = %s )' % (AT, LIN('C', 'B', 't')))
j2k = w.s([j2h, j2j], 'eqtr3d', '( %s -> ( A + ( ( C - A ) + ( t x. ( B - C ) ) ) ) = %s )' % (AT, LIN('C', 'B', 't')))
argid2 = w.s([j2g, j2k], 'eqtrd', '( %s -> %s = %s )' % (AT, LIN('A', 'B', ARG2), LIN('C', 'B', 't')))
facid2 = w.s([w.s([ba2, s1c], 'mulcomd', '( %s -> ( ( B - A ) x. ( 1 - S ) ) = ( ( 1 - S ) x. ( B - A ) ) )' % AT), bmc2], 'eqtrd', '( %s -> ( ( B - A ) x. ( 1 - S ) ) = ( B - C ) )' % AT)
pw2 = piece(w, 'S', '1', s2, c1b, s012, u1b, 'C', 'B', '( 1 - S )', facid2, argid2)
ie2 = w.s([pw2], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) ( ( %s ` %s ) x. ( 1 - S ) ) _d t = S. ( 0 (,) 1 ) %s _d t )' % (PS, HH, ARG2, IG('t', 'C', 'B')))
daf2 = w.s([hcn, s01, u1, w.inst('ditgaff')], 'syl3anc', '( %s -> %s = S. ( 0 (,) 1 ) ( ( %s ` %s ) x. ( 1 - S ) ) _d t )' % (PS, DS1, HH, ARG2))
lv2 = w.s([f, cc, b, w.inst('lintval')], 'syl3anc', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (PS, LINT('F', 'C', 'B'), IG('t', 'C', 'B')))
p2 = w.s([w.s([daf2, ie2], 'eqtrd', '( %s -> %s = S. ( 0 (,) 1 ) %s _d t )' % (PS, DS1, IG('t', 'C', 'B'))), lv2], 'eqtr4d', '( %s -> %s = %s )' % (PS, DS1, LINT('F', 'C', 'B')))
# combine
sp2 = w.s([p1, p2], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (PS, D0S, DS1, LINT('F', 'A', 'C'), LINT('F', 'C', 'B')))
sp3 = w.s([spl, sp2], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (PS, D01, LINT('F', 'A', 'C'), LINT('F', 'C', 'B')))
w.qed([tot, sp3], 'eqtr3d', '( %s -> %s = ( %s + %s ) )' % (PS, LINT('F', 'A', 'B'), LINT('F', 'A', 'C'), LINT('F', 'C', 'B'))); run(w)
