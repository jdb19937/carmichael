"""Sortie C0b, batch 2: the two half-splits of a rectangle boundary integral
(rectinthsp: a vertical cut; rectintvsp: a horizontal cut)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

# ===========================================================================
# rectinthsp: a vertical cut at the parameter S
# ===========================================================================
w = W('rectinthsp', 'A rectangle boundary integral splits at a vertical cut into the integrals over the left and right parts.')
XD = '%s = ( %s + ( S x. ( %s - %s ) ) )' % ('X', RA, RB, RA)
A0 = '( %s /\\ S e. ( 0 [,] 1 ) /\\ %s )' % (PS, XD)
M0 = PT('X', IA); M1 = PT('X', IB)
d = ctx(w, A0)
s01 = w.s([], 'simp2', '( %s -> S e. ( 0 [,] 1 ) )' % A0)
xd = w.s([], 'simp3', '( %s -> %s )' % (A0, XD))
# X in the real interval
tri = w.s([d['ar'], d['br'], d['ler']], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) )' % (A0, RA, RB, RA, RB))
cl = w.s([tri, s01, w.inst('crectlin')], 'syl2anc', '( %s -> ( %s + ( S x. ( %s - %s ) ) ) e. %s )' % (A0, RA, RB, RA, RI('A', 'B')))
xI = w.s([xd, cl], 'eqeltrd', '( %s -> X e. %s )' % (A0, RI('A', 'B')))
ssr = w.s([d['ar'], d['br'], w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, RI('A', 'B')))
xr = w.s([ssr, xI], 'sseldd', '( %s -> X e. RR )' % A0)
xc = w.s([xr], 'recnd', '( %s -> X e. CC )' % A0)
pM0 = mkpt(w, A0, d, 'X', IA, xI, d['iaI']); pM1 = mkpt(w, A0, d, 'X', IB, xI, d['ibI'])
pts = {'A': d['pA'], 'B': d['pB'], P10: d['pP10'], P01: d['pP01'], M0: pM0, M1: pM1}
pairs = [('A', P10), (P10, 'B'), ('B', P01), (P01, 'A'),
         ('A', M0), (M0, M1), (M1, P01), (M0, P10), ('B', M1), (M1, M0)]
L = lints(w, A0, d, pts, pairs)
cc = {LINT('F', P, Q): L[(P, Q)][1] for P, Q in pairs}
a = LINT('F', 'A', P10); b = LINT('F', P10, 'B'); c = LINT('F', 'B', P01); dd = LINT('F', P01, 'A')
e = LINT('F', 'A', M0); f = LINT('F', M0, M1); g = LINT('F', M1, P01)
h = LINT('F', M0, P10); i = LINT('F', 'B', M1); j = LINT('F', M1, M0)
# --- the closures of the coordinates, for the two cut-point identities
ic = closed(w, A0, 'ax-icn', '_i e. CC')
arc = w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A0, RA))
brc = w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A0, RB))
aic = w.s([d['ai']], 'recnd', '( %s -> %s e. CC )' % (A0, IA))
bic = w.s([d['bi']], 'recnd', '( %s -> %s e. CC )' % (A0, IB))
iia = w.s([ic, aic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IA))
iib = w.s([ic, bic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IB))
sc = w.s([s01, w.inst('elunitcn')], 'syl', '( %s -> S e. CC )' % A0)
# --- identity 1: M0 = ( A + ( S x. ( P10 - A ) ) )
repA = w.s([d['ac']], 'replimd', '( %s -> A = ( %s + ( _i x. %s ) ) )' % (A0, RA, IA))
r1 = w.s([repA], 'oveq2d', '( %s -> ( %s - A ) = ( %s - ( %s + ( _i x. %s ) ) ) )' % (A0, P10, P10, RA, IA))
r2 = w.s([brc, arc, iia], 'pnpcan2d', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = ( %s - %s ) )' % (A0, RB, IA, RA, IA, RB, RA))
r3 = w.s([r1, r2], 'eqtrd', '( %s -> ( %s - A ) = ( %s - %s ) )' % (A0, P10, RB, RA))
r4 = w.s([r3], 'oveq2d', '( %s -> ( S x. ( %s - A ) ) = ( S x. ( %s - %s ) ) )' % (A0, P10, RB, RA))
r5 = w.s([repA, r4], 'oveq12d', '( %s -> ( A + ( S x. ( %s - A ) ) ) = ( ( %s + ( _i x. %s ) ) + ( S x. ( %s - %s ) ) ) )' % (A0, P10, RA, IA, RB, RA))
sbc = w.s([sc, w.s([brc, arc], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, RB, RA))], 'mulcld', '( %s -> ( S x. ( %s - %s ) ) e. CC )' % (A0, RB, RA))
r6 = w.s([arc, iia, sbc], 'add32d', '( %s -> ( ( %s + ( _i x. %s ) ) + ( S x. ( %s - %s ) ) ) = ( ( %s + ( S x. ( %s - %s ) ) ) + ( _i x. %s ) ) )' % (A0, RA, IA, RB, RA, RA, RB, RA, IA))
r7 = w.s([w.s([xd], 'eqcomd', '( %s -> ( %s + ( S x. ( %s - %s ) ) ) = X )' % (A0, RA, RB, RA))], 'oveq1d',
         '( %s -> ( ( %s + ( S x. ( %s - %s ) ) ) + ( _i x. %s ) ) = %s )' % (A0, RA, RB, RA, IA, M0))
id1 = w.s([w.s([r5, r6], 'eqtrd', '( %s -> ( A + ( S x. ( %s - A ) ) ) = ( ( %s + ( S x. ( %s - %s ) ) ) + ( _i x. %s ) ) )' % (A0, P10, RA, RB, RA, IA)), r7], 'eqtrd',
          '( %s -> ( A + ( S x. ( %s - A ) ) ) = %s )' % (A0, P10, M0))
id1c = w.s([id1], 'eqcomd', '( %s -> %s = ( A + ( S x. ( %s - A ) ) ) )' % (A0, M0, P10))
sp1 = w.s([L[('A', P10)][0], s01, id1c, w.inst('lintsplit')], 'syl3anc',
          '( %s -> %s = ( %s + %s ) )' % (A0, a, e, h))
# --- identity 2: M1 = ( B + ( ( 1 - S ) x. ( P01 - B ) ) )
s1m = w.s([s01, w.inst('iirev')], 'syl', '( %s -> ( 1 - S ) e. ( 0 [,] 1 ) )' % A0)
repB = w.s([d['bc']], 'replimd', '( %s -> B = ( %s + ( _i x. %s ) ) )' % (A0, RB, IB))
q1 = w.s([repB], 'oveq2d', '( %s -> ( %s - B ) = ( %s - ( %s + ( _i x. %s ) ) ) )' % (A0, P01, P01, RB, IB))
q2 = w.s([arc, brc, iib], 'pnpcan2d', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = ( %s - %s ) )' % (A0, RA, IB, RB, IB, RA, RB))
q3 = w.s([q1, q2], 'eqtrd', '( %s -> ( %s - B ) = ( %s - %s ) )' % (A0, P01, RA, RB))
q4 = w.s([q3], 'oveq2d', '( %s -> ( ( 1 - S ) x. ( %s - B ) ) = ( ( 1 - S ) x. ( %s - %s ) ) )' % (A0, P01, RA, RB))
q5 = w.s([repB, q4], 'oveq12d', '( %s -> ( B + ( ( 1 - S ) x. ( %s - B ) ) ) = ( ( %s + ( _i x. %s ) ) + ( ( 1 - S ) x. ( %s - %s ) ) ) )' % (A0, P01, RB, IB, RA, RB))
smc = w.s([w.s([s1m, w.inst('elunitcn')], 'syl', '( %s -> ( 1 - S ) e. CC )' % A0), w.s([arc, brc], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, RA, RB))], 'mulcld', '( %s -> ( ( 1 - S ) x. ( %s - %s ) ) e. CC )' % (A0, RA, RB))
q6 = w.s([brc, iib, smc], 'add32d', '( %s -> ( ( %s + ( _i x. %s ) ) + ( ( 1 - S ) x. ( %s - %s ) ) ) = ( ( %s + ( ( 1 - S ) x. ( %s - %s ) ) ) + ( _i x. %s ) ) )' % (A0, RB, IB, RA, RB, RB, RA, RB, IB))
q7 = w.s([brc, arc, sc, w.inst('cseglinrev')], 'syl3anc', '( %s -> ( %s + ( ( 1 - S ) x. ( %s - %s ) ) ) = ( %s + ( S x. ( %s - %s ) ) ) )' % (A0, RB, RA, RB, RA, RB, RA))
q8 = w.s([w.s([q7, w.s([xd], 'eqcomd', '( %s -> ( %s + ( S x. ( %s - %s ) ) ) = X )' % (A0, RA, RB, RA))], 'eqtrd', '( %s -> ( %s + ( ( 1 - S ) x. ( %s - %s ) ) ) = X )' % (A0, RB, RA, RB))], 'oveq1d',
         '( %s -> ( ( %s + ( ( 1 - S ) x. ( %s - %s ) ) ) + ( _i x. %s ) ) = %s )' % (A0, RB, RA, RB, IB, M1))
id2 = w.s([w.s([q5, q6], 'eqtrd', '( %s -> ( B + ( ( 1 - S ) x. ( %s - B ) ) ) = ( ( %s + ( ( 1 - S ) x. ( %s - %s ) ) ) + ( _i x. %s ) ) )' % (A0, P01, RB, RA, RB, IB)), q8], 'eqtrd',
          '( %s -> ( B + ( ( 1 - S ) x. ( %s - B ) ) ) = %s )' % (A0, P01, M1))
id2c = w.s([id2], 'eqcomd', '( %s -> %s = ( B + ( ( 1 - S ) x. ( %s - B ) ) ) )' % (A0, M1, P01))
sp2 = w.s([L[('B', P01)][0], s1m, id2c, w.inst('lintsplit')], 'syl3anc',
          '( %s -> %s = ( %s + %s ) )' % (A0, c, i, g))
# --- the reversed interior edge
rev = w.s([L[(M0, M1)][0], w.inst('lintrev')], 'syl', '( %s -> %s = -u %s )' % (A0, j, f))
# --- the three rectangle integrals
lhs, lhstext = expand(w, A0, d, 'A', 'B', d['ac'], d['bc'], None)
reM1 = w.s([xr, d['bi'], w.inst('crre')], 'syl2anc', '( %s -> %s = X )' % (A0, RE(M1)))
imM1 = w.s([xr, d['bi'], w.inst('crim')], 'syl2anc', '( %s -> %s = %s )' % (A0, IM(M1), IB))
reM0 = w.s([xr, d['ai'], w.inst('crre')], 'syl2anc', '( %s -> %s = X )' % (A0, RE(M0)))
imM0 = w.s([xr, d['ai'], w.inst('crim')], 'syl2anc', '( %s -> %s = %s )' % (A0, IM(M0), IA))
m1c = w.s([xc, iib], 'addcld', '( %s -> %s e. CC )' % (A0, M1))
m0c = w.s([xc, iia], 'addcld', '( %s -> %s e. CC )' % (A0, M0))
r_c1 = w.s([reM1], 'oveq1d', '( %s -> %s = %s )' % (A0, PT(RE(M1), IA), M0))
r_c2i = w.s([imM1], 'oveq2d', '( %s -> ( _i x. %s ) = ( _i x. %s ) )' % (A0, IM(M1), IB))
r_c2 = w.s([r_c2i], 'oveq2d', '( %s -> %s = %s )' % (A0, PT(RA, IM(M1)), P01))
lrect, ltext = expand(w, A0, d, 'A', M1, d['ac'], m1c,
                      {PT(RE(M1), IA): (M0, r_c1), PT(RA, IM(M1)): (P01, r_c2)})
r_c3i = w.s([imM0], 'oveq2d', '( %s -> ( _i x. %s ) = ( _i x. %s ) )' % (A0, IM(M0), IA))
r_c3 = w.s([r_c3i], 'oveq2d', '( %s -> %s = %s )' % (A0, PT(RB, IM(M0)), P10))
r_c4 = w.s([reM0], 'oveq1d', '( %s -> %s = %s )' % (A0, PT(RE(M0), IB), M1))
rrect, rtext = expand(w, A0, d, M0, 'B', m0c, d['bc'],
                      {PT(RB, IM(M0)): (P10, r_c3), PT(RE(M0), IB): (M1, r_c4)})
# --- normalize
key = {e: 0, h: 1, b: 2, i: 3, g: 4, dd: 5, f: 6, j: 7}
cs = CxSum(w, A0, cc, key)
# LHS: ( ( a + b ) + ( c + d ) ) with a -> ( e + h ), c -> ( i + g )
l1 = w.s([sp1], 'oveq1d', '( %s -> ( %s + %s ) = ( ( %s + %s ) + %s ) )' % (A0, a, b, e, h, b))
l2 = w.s([sp2], 'oveq1d', '( %s -> ( %s + %s ) = ( ( %s + %s ) + %s ) )' % (A0, c, dd, i, g, dd))
lsub = w.s([l1, l2], 'oveq12d', '( %s -> %s = ( ( ( %s + %s ) + %s ) + ( ( %s + %s ) + %s ) ) )' % (A0, lhstext, e, h, b, i, g, dd))
treeL = ('+', ('+', ('+', e, h), b), ('+', ('+', i, g), dd))
nL, atL = cs.nf(treeL)
lhs2 = w.s([w.s([lhs, lsub], 'eqtrd', '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, tree_text(treeL))), nL], 'eqtrd',
           '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, rn(atL)))
# RHS
sumst = w.s([lrect, rrect], 'oveq12d',
            '( %s -> ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) = ( %s + %s ) )' % (A0, M1, M0, ltext, rtext))
treeR = ('+', ('+', ('+', e, f), ('+', g, dd)), ('+', ('+', h, b), ('+', i, j)))
nR, atR = cs.nf(treeR)
can = cancel(w, A0, cs, atR, f, j, rev, cc)
rhs2 = w.s([w.s([sumst, nR], 'eqtrd', '( %s -> ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) = %s )' % (A0, M1, M0, rn(atR))), can], 'eqtrd',
           '( %s -> ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) = %s )' % (A0, M1, M0, rn(atL)))
w.qed([lhs2, rhs2], 'eqtr4d', '( %s -> ( F rectint <. A , B >. ) = ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) )' % (A0, M1, M0))
run(w)


# ===========================================================================
# rectintvsp: a horizontal cut at the parameter T
# ===========================================================================
w = W('rectintvsp', 'A rectangle boundary integral splits at a horizontal cut into the integrals over the bottom and top parts.')
YD = 'Y = ( %s + ( T x. ( %s - %s ) ) )' % (IA, IB, IA)
A0 = '( %s /\\ T e. ( 0 [,] 1 ) /\\ %s )' % (PS, YD)
N0 = PT(RA, 'Y'); N1 = PT(RB, 'Y')
d = ctx(w, A0)
t01 = w.s([], 'simp2', '( %s -> T e. ( 0 [,] 1 ) )' % A0)
yd = w.s([], 'simp3', '( %s -> %s )' % (A0, YD))
tri = w.s([d['ai'], d['bi'], d['lei']], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) )' % (A0, IA, IB, IA, IB))
cl = w.s([tri, t01, w.inst('crectlin')], 'syl2anc', '( %s -> ( %s + ( T x. ( %s - %s ) ) ) e. %s )' % (A0, IA, IB, IA, II('A', 'B')))
yI = w.s([yd, cl], 'eqeltrd', '( %s -> Y e. %s )' % (A0, II('A', 'B')))
ssi = w.s([d['ai'], d['bi'], w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, II('A', 'B')))
yr = w.s([ssi, yI], 'sseldd', '( %s -> Y e. RR )' % A0)
yc = w.s([yr], 'recnd', '( %s -> Y e. CC )' % A0)
pN0 = mkpt(w, A0, d, RA, 'Y', d['raI'], yI); pN1 = mkpt(w, A0, d, RB, 'Y', d['rbI'], yI)
pts = {'A': d['pA'], 'B': d['pB'], P10: d['pP10'], P01: d['pP01'], N0: pN0, N1: pN1}
pairs = [('A', P10), (P10, N1), (N1, 'B'), ('B', P01), (P01, N0), (N0, 'A'),
         (N0, N1), (N1, N0), (P10, 'B'), (P01, 'A')]
L = lints(w, A0, d, pts, pairs)
cc = {LINT('F', P, Q): L[(P, Q)][1] for P, Q in pairs}
a = LINT('F', 'A', P10); k = LINT('F', P10, N1); m = LINT('F', N1, 'B'); c = LINT('F', 'B', P01)
n = LINT('F', P01, N0); o = LINT('F', N0, 'A'); q = LINT('F', N0, N1); pp = LINT('F', N1, N0)
b = LINT('F', P10, 'B'); dd = LINT('F', P01, 'A')
ic = closed(w, A0, 'ax-icn', '_i e. CC')
arc = w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A0, RA))
brc = w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A0, RB))
aic = w.s([d['ai']], 'recnd', '( %s -> %s e. CC )' % (A0, IA))
bic = w.s([d['bi']], 'recnd', '( %s -> %s e. CC )' % (A0, IB))
iia = w.s([ic, aic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IA))
iib = w.s([ic, bic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IB))
iy = w.s([ic, yc], 'mulcld', '( %s -> ( _i x. Y ) e. CC )' % A0)
tc = w.s([t01, w.inst('elunitcn')], 'syl', '( %s -> T e. CC )' % A0)
t1m = w.s([t01, w.inst('iirev')], 'syl', '( %s -> ( 1 - T ) e. ( 0 [,] 1 ) )' % A0)
tmc = w.s([t1m, w.inst('elunitcn')], 'syl', '( %s -> ( 1 - T ) e. CC )' % A0)
repA = w.s([d['ac']], 'replimd', '( %s -> A = ( %s + ( _i x. %s ) ) )' % (A0, RA, IA))
repB = w.s([d['bc']], 'replimd', '( %s -> B = ( %s + ( _i x. %s ) ) )' % (A0, RB, IB))
ydc = w.s([yd], 'eqcomd', '( %s -> ( %s + ( T x. ( %s - %s ) ) ) = Y )' % (A0, IA, IB, IA))



# --- identity 1: N1 = ( P10 + ( T x. ( B - P10 ) ) )
b1 = w.s([repB], 'oveq1d', '( %s -> ( B - %s ) = ( ( %s + ( _i x. %s ) ) - %s ) )' % (A0, P10, RB, IB, P10))
b2 = w.s([brc, iib, iia], 'pnpcand', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, RB, IB, RB, IA, IB, IA))
b3 = w.s([w.s([b1, b2], 'eqtrd', '( %s -> ( B - %s ) = ( ( _i x. %s ) - ( _i x. %s ) )' % (A0, P10, IB, IA) + ' )'),
          w.s([w.s([ic, bic, aic], 'subdid', '( %s -> ( _i x. ( %s - %s ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, IB, IA, IB, IA))], 'eqcomd', '( %s -> ( ( _i x. %s ) - ( _i x. %s ) ) = ( _i x. ( %s - %s ) ) )' % (A0, IB, IA, IB, IA))],
         'eqtrd', '( %s -> ( B - %s ) = ( _i x. ( %s - %s ) ) )' % (A0, P10, IB, IA))
b4 = w.s([b3], 'oveq2d', '( %s -> ( T x. ( B - %s ) ) = ( T x. ( _i x. ( %s - %s ) ) ) )' % (A0, P10, IB, IA))
b5 = w.s([tc, ic, w.s([bic, aic], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, IB, IA))], 'mul12d',
         '( %s -> ( T x. ( _i x. ( %s - %s ) ) ) = ( _i x. ( T x. ( %s - %s ) ) ) )' % (A0, IB, IA, IB, IA))
b6 = w.s([w.s([b4, b5], 'eqtrd', '( %s -> ( T x. ( B - %s ) ) = ( _i x. ( T x. ( %s - %s ) ) ) )' % (A0, P10, IB, IA))], 'oveq2d',
         '( %s -> ( %s + ( T x. ( B - %s ) ) ) = ( ( %s + ( _i x. %s ) ) + ( _i x. ( T x. ( %s - %s ) ) ) )' % (A0, P10, P10, RB, IA, IB, IA) + ' )')
itc = w.s([ic, w.s([tc, w.s([bic, aic], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, IB, IA))], 'mulcld', '( %s -> ( T x. ( %s - %s ) ) e. CC )' % (A0, IB, IA))], 'mulcld', '( %s -> ( _i x. ( T x. ( %s - %s ) ) ) e. CC )' % (A0, IB, IA))
b7 = w.s([brc, iia, itc], 'addassd', '( %s -> ( ( %s + ( _i x. %s ) ) + ( _i x. ( T x. ( %s - %s ) ) ) ) = ( %s + ( ( _i x. %s ) + ( _i x. ( T x. ( %s - %s ) ) ) ) ) )' % (A0, RB, IA, IB, IA, RB, IA, IB, IA))
b8 = w.s([w.s([ic, aic, w.s([tc, w.s([bic, aic], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, IB, IA))], 'mulcld', '( %s -> ( T x. ( %s - %s ) ) e. CC )' % (A0, IB, IA))], 'adddid', '( %s -> ( _i x. ( %s + ( T x. ( %s - %s ) ) ) ) = ( ( _i x. %s ) + ( _i x. ( T x. ( %s - %s ) ) ) ) )' % (A0, IA, IB, IA, IA, IB, IA))], 'eqcomd',
         '( %s -> ( ( _i x. %s ) + ( _i x. ( T x. ( %s - %s ) ) ) ) = ( _i x. ( %s + ( T x. ( %s - %s ) ) ) ) )' % (A0, IA, IB, IA, IA, IB, IA))
b8b = w.s([b8, w.s([ydc], 'oveq2d', '( %s -> ( _i x. ( %s + ( T x. ( %s - %s ) ) ) ) = ( _i x. Y ) )' % (A0, IA, IB, IA))], 'eqtrd',
          '( %s -> ( ( _i x. %s ) + ( _i x. ( T x. ( %s - %s ) ) ) ) = ( _i x. Y ) )' % (A0, IA, IB, IA))
b10 = w.s([b8b], 'oveq2d', '( %s -> ( %s + ( ( _i x. %s ) + ( _i x. ( T x. ( %s - %s ) ) ) ) ) = %s )' % (A0, RB, IA, IB, IA, N1))
vid1 = w.s([w.s([b6, b7], 'eqtrd', '( %s -> ( %s + ( T x. ( B - %s ) ) ) = ( %s + ( ( _i x. %s ) + ( _i x. ( T x. ( %s - %s ) ) ) ) ) )' % (A0, P10, P10, RB, IA, IB, IA)), b10], 'eqtrd',
           '( %s -> ( %s + ( T x. ( B - %s ) ) ) = %s )' % (A0, P10, P10, N1))
vid1c = w.s([vid1], 'eqcomd', '( %s -> %s = ( %s + ( T x. ( B - %s ) ) ) )' % (A0, N1, P10, P10))
vsp1 = w.s([L[(P10, 'B')][0], t01, vid1c, w.inst('lintsplit')], 'syl3anc', '( %s -> %s = ( %s + %s ) )' % (A0, b, k, m))
# --- identity 2: N0 = ( P01 + ( ( 1 - T ) x. ( A - P01 ) ) )
c1 = w.s([repA], 'oveq1d', '( %s -> ( A - %s ) = ( ( %s + ( _i x. %s ) ) - %s ) )' % (A0, P01, RA, IA, P01))
c2 = w.s([arc, iia, iib], 'pnpcand', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, RA, IA, RA, IB, IA, IB))
c3 = w.s([w.s([c1, c2], 'eqtrd', '( %s -> ( A - %s ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, P01, IA, IB)),
          w.s([w.s([ic, aic, bic], 'subdid', '( %s -> ( _i x. ( %s - %s ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, IA, IB, IA, IB))], 'eqcomd', '( %s -> ( ( _i x. %s ) - ( _i x. %s ) ) = ( _i x. ( %s - %s ) ) )' % (A0, IA, IB, IA, IB))],
         'eqtrd', '( %s -> ( A - %s ) = ( _i x. ( %s - %s ) ) )' % (A0, P01, IA, IB))
c4 = w.s([c3], 'oveq2d', '( %s -> ( ( 1 - T ) x. ( A - %s ) ) = ( ( 1 - T ) x. ( _i x. ( %s - %s ) ) ) )' % (A0, P01, IA, IB))
abc = w.s([aic, bic], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, IA, IB))
c5 = w.s([tmc, ic, abc], 'mul12d', '( %s -> ( ( 1 - T ) x. ( _i x. ( %s - %s ) ) ) = ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) )' % (A0, IA, IB, IA, IB))
c6 = w.s([w.s([c4, c5], 'eqtrd', '( %s -> ( ( 1 - T ) x. ( A - %s ) ) = ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) )' % (A0, P01, IA, IB))], 'oveq2d',
         '( %s -> ( %s + ( ( 1 - T ) x. ( A - %s ) ) ) = ( ( %s + ( _i x. %s ) ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) )' % (A0, P01, P01, RA, IB, IA, IB))
tmm = w.s([tmc, abc], 'mulcld', '( %s -> ( ( 1 - T ) x. ( %s - %s ) ) e. CC )' % (A0, IA, IB))
itm = w.s([ic, tmm], 'mulcld', '( %s -> ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) e. CC )' % (A0, IA, IB))
c7 = w.s([arc, iib, itm], 'addassd', '( %s -> ( ( %s + ( _i x. %s ) ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) = ( %s + ( ( _i x. %s ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) ) )' % (A0, RA, IB, IA, IB, RA, IB, IA, IB))
c8 = w.s([w.s([ic, bic, tmm], 'adddid', '( %s -> ( _i x. ( %s + ( ( 1 - T ) x. ( %s - %s ) ) ) ) = ( ( _i x. %s ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) )' % (A0, IB, IA, IB, IB, IA, IB))], 'eqcomd',
         '( %s -> ( ( _i x. %s ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) = ( _i x. ( %s + ( ( 1 - T ) x. ( %s - %s ) ) ) ) )' % (A0, IB, IA, IB, IB, IA, IB))
crev = w.s([bic, aic, tc, w.inst('cseglinrev')], 'syl3anc', '( %s -> ( %s + ( ( 1 - T ) x. ( %s - %s ) ) ) = ( %s + ( T x. ( %s - %s ) ) ) )' % (A0, IB, IA, IB, IA, IB, IA))
c9 = w.s([w.s([crev, ydc], 'eqtrd', '( %s -> ( %s + ( ( 1 - T ) x. ( %s - %s ) ) ) = Y )' % (A0, IB, IA, IB))], 'oveq2d',
         '( %s -> ( _i x. ( %s + ( ( 1 - T ) x. ( %s - %s ) ) ) ) = ( _i x. Y ) )' % (A0, IB, IA, IB))
c10 = w.s([w.s([c8, c9], 'eqtrd', '( %s -> ( ( _i x. %s ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) = ( _i x. Y ) )' % (A0, IB, IA, IB))], 'oveq2d',
          '( %s -> ( %s + ( ( _i x. %s ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) ) = %s )' % (A0, RA, IB, IA, IB, N0))
vid2 = w.s([w.s([c6, c7], 'eqtrd', '( %s -> ( %s + ( ( 1 - T ) x. ( A - %s ) ) ) = ( %s + ( ( _i x. %s ) + ( _i x. ( ( 1 - T ) x. ( %s - %s ) ) ) ) ) )' % (A0, P01, P01, RA, IB, IA, IB)), c10], 'eqtrd',
           '( %s -> ( %s + ( ( 1 - T ) x. ( A - %s ) ) ) = %s )' % (A0, P01, P01, N0))
vid2c = w.s([vid2], 'eqcomd', '( %s -> %s = ( %s + ( ( 1 - T ) x. ( A - %s ) ) ) )' % (A0, N0, P01, P01))
vsp2 = w.s([L[(P01, 'A')][0], t1m, vid2c, w.inst('lintsplit')], 'syl3anc', '( %s -> %s = ( %s + %s ) )' % (A0, dd, n, o))
# --- the reversed interior edge
rev = w.s([L[(N0, N1)][0], w.inst('lintrev')], 'syl', '( %s -> %s = -u %s )' % (A0, pp, q))
# --- the three rectangle integrals
lhs, lhstext = expand(w, A0, d, 'A', 'B', d['ac'], d['bc'], None)
reN1 = w.s([d['br'], yr, w.inst('crre')], 'syl2anc', '( %s -> %s = %s )' % (A0, RE(N1), RB))
imN1 = w.s([d['br'], yr, w.inst('crim')], 'syl2anc', '( %s -> %s = Y )' % (A0, IM(N1)))
reN0 = w.s([d['ar'], yr, w.inst('crre')], 'syl2anc', '( %s -> %s = %s )' % (A0, RE(N0), RA))
imN0 = w.s([d['ar'], yr, w.inst('crim')], 'syl2anc', '( %s -> %s = Y )' % (A0, IM(N0)))
n1c = w.s([brc, iy], 'addcld', '( %s -> %s e. CC )' % (A0, N1))
n0c = w.s([arc, iy], 'addcld', '( %s -> %s e. CC )' % (A0, N0))
u1 = w.s([reN1], 'oveq1d', '( %s -> %s = %s )' % (A0, PT(RE(N1), IA), P10))
u2 = w.s([w.s([imN1], 'oveq2d', '( %s -> ( _i x. %s ) = ( _i x. Y ) )' % (A0, IM(N1)))], 'oveq2d', '( %s -> %s = %s )' % (A0, PT(RA, IM(N1)), N0))
brect, btext = expand(w, A0, d, 'A', N1, d['ac'], n1c, {PT(RE(N1), IA): (P10, u1), PT(RA, IM(N1)): (N0, u2)})
u3 = w.s([w.s([imN0], 'oveq2d', '( %s -> ( _i x. %s ) = ( _i x. Y ) )' % (A0, IM(N0)))], 'oveq2d', '( %s -> %s = %s )' % (A0, PT(RB, IM(N0)), N1))
u4 = w.s([reN0], 'oveq1d', '( %s -> %s = %s )' % (A0, PT(RE(N0), IB), P01))
trect, ttext = expand(w, A0, d, N0, 'B', n0c, d['bc'], {PT(RB, IM(N0)): (N1, u3), PT(RE(N0), IB): (P01, u4)})
# --- normalize
key = {a: 0, k: 1, m: 2, c: 3, n: 4, o: 5, q: 6, pp: 7}
cs = CxSum(w, A0, cc, key)
l1 = w.s([vsp1], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + ( %s + %s ) ) )' % (A0, a, b, a, k, m))
l2 = w.s([vsp2], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + ( %s + %s ) ) )' % (A0, c, dd, c, n, o))
lsub = w.s([l1, l2], 'oveq12d', '( %s -> %s = ( ( %s + ( %s + %s ) ) + ( %s + ( %s + %s ) ) ) )' % (A0, lhstext, a, k, m, c, n, o))
treeL = ('+', ('+', a, ('+', k, m)), ('+', c, ('+', n, o)))
nL, atL = cs.nf(treeL)
lhs2 = w.s([w.s([lhs, lsub], 'eqtrd', '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, tree_text(treeL))), nL], 'eqtrd',
           '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, rn(atL)))
sumst = w.s([brect, trect], 'oveq12d',
            '( %s -> ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) = ( %s + %s ) )' % (A0, N1, N0, btext, ttext))
treeR = ('+', ('+', ('+', a, k), ('+', pp, o)), ('+', ('+', q, m), ('+', c, n)))
nR, atR = cs.nf(treeR)
can = cancel(w, A0, cs, atR, q, pp, rev, cc)
rhs2 = w.s([w.s([sumst, nR], 'eqtrd', '( %s -> ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) = %s )' % (A0, N1, N0, rn(atR))), can], 'eqtrd',
           '( %s -> ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) = %s )' % (A0, N1, N0, rn(atL)))
w.qed([lhs2, rhs2], 'eqtr4d', '( %s -> ( F rectint <. A , B >. ) = ( ( F rectint <. A , %s >. ) + ( F rectint <. %s , B >. ) ) )' % (A0, N1, N0))
run(w)
