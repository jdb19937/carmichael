"""Sortie C0, batch 1: the segment cseg (value, membership, closure, convexity identities)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from c0lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ---- csegval
w = W('csegval', 'Value of the segment: the set of the points A + t ( B - A ) for t in the unit interval.')
A = '( a = A /\\ b = B )'
la = w.s([], 'simpl', '( %s -> a = A )' % A); lb = w.s([], 'simpr', '( %s -> b = B )' % A)
body = 'ran ( t e. ( 0 [,] 1 ) |-> ( a + ( t x. ( b - a ) ) ) )'
c, new = w.congr(body, {'a': 'A', 'b': 'B'}, A, {'a': la, 'b': lb})
assert new == 'ran ( t e. ( 0 [,] 1 ) |-> %s )' % LIN('A', 'B'), new
d = w.s([], 'df-cseg', 'cseg = ( a e. CC , b e. CC |-> %s )' % body)
x = w.s([], 'ovex', '( 0 [,] 1 ) e. _V'); mi = w.inst('mptexg'); m = w.s([x, mi], 'ax-mp', '( t e. ( 0 [,] 1 ) |-> %s ) e. _V' % LIN('A', 'B'))
ri = w.inst('rnexg'); r = w.s([m, ri], 'ax-mp', '%s e. _V' % new)
o = w.s([c, d], 'ovmpoga', '( ( A e. CC /\\ B e. CC /\\ %s e. _V ) -> ( A cseg B ) = %s )' % (new, new))
w.qed([r, o], 'mp3an3', '( ( A e. CC /\\ B e. CC ) -> ( A cseg B ) = %s )' % new); run(w)

# ---- csegel
w = W('csegel', 'Membership in a segment.')
A = '( A e. CC /\\ B e. CC )'
v = w.s([], 'csegval', '( %s -> ( A cseg B ) = ran ( t e. ( 0 [,] 1 ) |-> %s ) )' % (A, LIN('A', 'B')))
e = w.s([v], 'eleq2d', '( %s -> ( X e. ( A cseg B ) <-> X e. ran ( t e. ( 0 [,] 1 ) |-> %s ) ) )' % (A, LIN('A', 'B')))
eq = w.s([], 'eqid', '( t e. ( 0 [,] 1 ) |-> %s ) = ( t e. ( 0 [,] 1 ) |-> %s )' % (LIN('A', 'B'), LIN('A', 'B')))
ov = w.s([], 'ovexd', '( ( %s /\\ t e. ( 0 [,] 1 ) ) -> %s e. _V )' % (A, LIN('A', 'B')))
ov2 = w.s([ov], 'ralrimiva', '( %s -> A. t e. ( 0 [,] 1 ) %s e. _V )' % (A, LIN('A', 'B')))
ri = w.s([eq], 'elrnmptg', '( A. t e. ( 0 [,] 1 ) %s e. _V -> ( X e. ran ( t e. ( 0 [,] 1 ) |-> %s ) <-> E. t e. ( 0 [,] 1 ) X = %s ) )' % (LIN('A', 'B'), LIN('A', 'B'), LIN('A', 'B')))
r = w.s([ov2, ri], 'syl', '( %s -> ( X e. ran ( t e. ( 0 [,] 1 ) |-> %s ) <-> E. t e. ( 0 [,] 1 ) X = %s ) )' % (A, LIN('A', 'B'), LIN('A', 'B')))
w.qed([e, r], 'bitrd', '( %s -> ( X e. ( A cseg B ) <-> E. t e. ( 0 [,] 1 ) X = %s ) )' % (A, LIN('A', 'B'))); run(w)

# ---- cseglin: A + T ( B - A ) is in the segment
w = W('cseglin', 'A point of the parametrisation lies in the segment.')
A = '( A e. CC /\\ B e. CC /\\ T e. ( 0 [,] 1 ) )'
a = w.s([], 'simp1', '( %s -> A e. CC )' % A); b = w.s([], 'simp2', '( %s -> B e. CC )' % A); t = w.s([], 'simp3', '( %s -> T e. ( 0 [,] 1 ) )' % A)
eqd = w.s([], 'eqidd', '( %s -> %s = %s )' % (A, LIN('A', 'B', 'T'), LIN('A', 'B', 'T')))
s1 = w.s([], 'oveq1', '( t = T -> ( t x. ( B - A ) ) = ( T x. ( B - A ) ) )')
s2 = w.s([s1], 'oveq2d', '( t = T -> %s = %s )' % (LIN('A', 'B'), LIN('A', 'B', 'T')))
s3 = w.s([s2], 'eqeq2d', '( t = T -> ( %s = %s <-> %s = %s ) )' % (LIN('A', 'B', 'T'), LIN('A', 'B'), LIN('A', 'B', 'T'), LIN('A', 'B', 'T')))
s3a = w.s([s3], 'adantl', '( ( %s /\\ t = T ) -> ( %s = %s <-> %s = %s ) )' % (A, LIN('A', 'B', 'T'), LIN('A', 'B'), LIN('A', 'B', 'T'), LIN('A', 'B', 'T')))
ex = w.s([t, s3a, eqd], 'rspcedvd', '( %s -> E. t e. ( 0 [,] 1 ) %s = %s )' % (A, LIN('A', 'B', 'T'), LIN('A', 'B')))
el = w.s([a, b, w.inst('csegel')], 'syl2anc', '( %s -> ( %s e. ( A cseg B ) <-> E. t e. ( 0 [,] 1 ) %s = %s ) )' % (A, LIN('A', 'B', 'T'), LIN('A', 'B', 'T'), LIN('A', 'B')))
w.qed([ex, el], 'mpbird', '( %s -> %s e. ( A cseg B ) )' % (A, LIN('A', 'B', 'T'))); run(w)

# ---- csegcl: subset of CC
w = W('csegcl', 'A segment is a set of complex numbers.')
A = '( A e. CC /\\ B e. CC )'; A2 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A
a = w.s([], 'simpll', '( %s -> A e. CC )' % A2); b = w.s([], 'simplr', '( %s -> B e. CC )' % A2)
tt = w.s([], 'simpr', '( %s -> t e. ( 0 [,] 1 ) )' % A2); tc = w.s([tt, w.inst('elunitcn')], 'syl', '( %s -> t e. CC )' % A2)
ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % A2); tba = w.s([tc, ba], 'mulcld', '( %s -> ( t x. ( B - A ) ) e. CC )' % A2)
l = w.s([a, tba], 'addcld', '( %s -> %s e. CC )' % (A2, LIN('A', 'B')))
f = w.s([l], 'fmptd', '( %s -> ( t e. ( 0 [,] 1 ) |-> %s ) : ( 0 [,] 1 ) --> CC )' % (A, LIN('A', 'B')))
r = w.s([f], 'frnd', '( %s -> ran ( t e. ( 0 [,] 1 ) |-> %s ) C_ CC )' % (A, LIN('A', 'B')))
v = w.s([], 'csegval', '( %s -> ( A cseg B ) = ran ( t e. ( 0 [,] 1 ) |-> %s ) )' % (A, LIN('A', 'B')))
w.qed([v, r], 'eqsstrd', '( %s -> ( A cseg B ) C_ CC )' % A); run(w)

# ---- csegid1, csegid2
w = W('csegid1', 'The first endpoint lies in the segment.')
A = '( A e. CC /\\ B e. CC )'
a = w.s([], 'simpl', '( %s -> A e. CC )' % A); b = w.s([], 'simpr', '( %s -> B e. CC )' % A)
z = closed(w, A, '0elunit', '0 e. ( 0 [,] 1 )')
l = w.s([a, b, z, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (A, LIN('A', 'B', '0')))
ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % A); m = w.s([ba], 'mul02d', '( %s -> ( 0 x. ( B - A ) ) = 0 )' % A)
m2 = w.s([m], 'oveq2d', '( %s -> %s = ( A + 0 ) )' % (A, LIN('A', 'B', '0'))); a0 = w.s([a], 'addridd', '( %s -> ( A + 0 ) = A )' % A)
m3 = w.s([m2, a0], 'eqtrd', '( %s -> %s = A )' % (A, LIN('A', 'B', '0')))
w.qed([m3, l], 'eqeltrrd', '( %s -> A e. ( A cseg B ) )' % A); run(w)

w = W('csegid2', 'The second endpoint lies in the segment.')
A = '( A e. CC /\\ B e. CC )'
a = w.s([], 'simpl', '( %s -> A e. CC )' % A); b = w.s([], 'simpr', '( %s -> B e. CC )' % A)
z = closed(w, A, '1elunit', '1 e. ( 0 [,] 1 )')
l = w.s([a, b, z, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (A, LIN('A', 'B', '1')))
ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % A); m = w.s([ba], 'mullidd', '( %s -> ( 1 x. ( B - A ) ) = ( B - A ) )' % A)
m2 = w.s([m], 'oveq2d', '( %s -> %s = ( A + ( B - A ) ) )' % (A, LIN('A', 'B', '1'))); p = w.s([a, b], 'pncan3d', '( %s -> ( A + ( B - A ) ) = B )' % A)
m3 = w.s([m2, p], 'eqtrd', '( %s -> %s = B )' % (A, LIN('A', 'B', '1')))
w.qed([m3, l], 'eqeltrrd', '( %s -> B e. ( A cseg B ) )' % A); run(w)

# ---- cvxid: A + T ( B - A ) = ( 1 - T ) A + T B
w = W('cvxid', 'The parametrisation of a segment as a convex combination.')
A = '( A e. CC /\\ B e. CC /\\ T e. CC )'
a = w.s([], 'simp1', '( %s -> A e. CC )' % A); b = w.s([], 'simp2', '( %s -> B e. CC )' % A); t = w.s([], 'simp3', '( %s -> T e. CC )' % A)
c1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % A)
ta = w.s([t, a], 'mulcld', '( %s -> ( T x. A ) e. CC )' % A); tb = w.s([t, b], 'mulcld', '( %s -> ( T x. B ) e. CC )' % A)
s1 = w.s([c1, t, a, w.inst('subdir')], 'syl3anc', '( %s -> ( ( 1 - T ) x. A ) = ( ( 1 x. A ) - ( T x. A ) ) )' % A)
m1 = w.s([a], 'mullidd', '( %s -> ( 1 x. A ) = A )' % A); m2 = w.s([m1], 'oveq1d', '( %s -> ( ( 1 x. A ) - ( T x. A ) ) = ( A - ( T x. A ) ) )' % A)
s2 = w.s([s1, m2], 'eqtrd', '( %s -> ( ( 1 - T ) x. A ) = ( A - ( T x. A ) ) )' % A)
s3 = w.s([s2], 'oveq1d', '( %s -> ( ( ( 1 - T ) x. A ) + ( T x. B ) ) = ( ( A - ( T x. A ) ) + ( T x. B ) ) )' % A)
s4 = w.s([a, ta, tb, w.inst('subadd23')], 'syl3anc', '( %s -> ( ( A - ( T x. A ) ) + ( T x. B ) ) = ( A + ( ( T x. B ) - ( T x. A ) ) ) )' % A)
d = w.s([t, b, a], 'subdid', '( %s -> ( T x. ( B - A ) ) = ( ( T x. B ) - ( T x. A ) ) )' % A)
d2 = w.s([d], 'oveq2d', '( %s -> %s = ( A + ( ( T x. B ) - ( T x. A ) ) ) )' % (A, LIN('A', 'B', 'T')))
s5 = w.s([s3, s4], 'eqtrd', '( %s -> ( ( ( 1 - T ) x. A ) + ( T x. B ) ) = ( A + ( ( T x. B ) - ( T x. A ) ) ) )' % A)
w.qed([d2, s5], 'eqtr4d', '( %s -> %s = ( ( ( 1 - T ) x. A ) + ( T x. B ) ) )' % (A, LIN('A', 'B', 'T'))); run(w)

# ---- cseglinrev: A + ( 1 - T ) ( B - A ) = B + T ( A - B )
w = W('cseglinrev', 'Reversing the parametrisation of a segment.')
A = '( A e. CC /\\ B e. CC /\\ T e. CC )'
a = w.s([], 'simp1', '( %s -> A e. CC )' % A); b = w.s([], 'simp2', '( %s -> B e. CC )' % A); t = w.s([], 'simp3', '( %s -> T e. CC )' % A)
c1 = w.s([], '1cnd', '( %s -> 1 e. CC )' % A); t1 = w.s([c1, t], 'subcld', '( %s -> ( 1 - T ) e. CC )' % A)
v = w.s([a, b, t1, w.inst('cvxid')], 'syl3anc', '( %s -> %s = ( ( ( 1 - ( 1 - T ) ) x. A ) + ( ( 1 - T ) x. B ) ) )' % (A, LIN('A', 'B', '( 1 - T )')))
n = w.s([c1, t], 'nncand', '( %s -> ( 1 - ( 1 - T ) ) = T )' % A); n2 = w.s([n], 'oveq1d', '( %s -> ( ( 1 - ( 1 - T ) ) x. A ) = ( T x. A ) )' % A)
n3 = w.s([n2], 'oveq1d', '( %s -> ( ( ( 1 - ( 1 - T ) ) x. A ) + ( ( 1 - T ) x. B ) ) = ( ( T x. A ) + ( ( 1 - T ) x. B ) ) )' % A)
ta = w.s([t, a], 'mulcld', '( %s -> ( T x. A ) e. CC )' % A); tb1 = w.s([t1, b], 'mulcld', '( %s -> ( ( 1 - T ) x. B ) e. CC )' % A)
cm = w.s([ta, tb1], 'addcomd', '( %s -> ( ( T x. A ) + ( ( 1 - T ) x. B ) ) = ( ( ( 1 - T ) x. B ) + ( T x. A ) ) )' % A)
v2 = w.s([b, a, t, w.inst('cvxid')], 'syl3anc', '( %s -> %s = ( ( ( 1 - T ) x. B ) + ( T x. A ) ) )' % (A, LIN('B', 'A', 'T')))
e1 = w.s([v, n3], 'eqtrd', '( %s -> %s = ( ( T x. A ) + ( ( 1 - T ) x. B ) ) )' % (A, LIN('A', 'B', '( 1 - T )')))
e2 = w.s([e1, cm], 'eqtrd', '( %s -> %s = ( ( ( 1 - T ) x. B ) + ( T x. A ) ) )' % (A, LIN('A', 'B', '( 1 - T )')))
w.qed([e2, v2], 'eqtr4d', '( %s -> %s = %s )' % (A, LIN('A', 'B', '( 1 - T )'), LIN('B', 'A', 'T'))); run(w)

# ---- csegcomlem, csegcom
w = W('csegcomlem', 'Lemma for csegcom: one inclusion.')
A = '( A e. CC /\\ B e. CC )'; A2 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A
a = w.s([], 'simpll', '( %s -> A e. CC )' % A2); b = w.s([], 'simplr', '( %s -> B e. CC )' % A2)
tt = w.s([], 'simpr', '( %s -> t e. ( 0 [,] 1 ) )' % A2); tc = w.s([tt, w.inst('elunitcn')], 'syl', '( %s -> t e. CC )' % A2)
rv = w.s([b, a, tc, w.inst('cseglinrev')], 'syl3anc', '( %s -> %s = %s )' % (A2, LIN('B', 'A', '( 1 - t )'), LIN('A', 'B')))
t1 = w.s([tt, w.inst('iirev')], 'syl', '( %s -> ( 1 - t ) e. ( 0 [,] 1 ) )' % A2)
el = w.s([b, a, t1, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( B cseg A ) )' % (A2, LIN('B', 'A', '( 1 - t )')))
el2 = w.s([rv, el], 'eqeltrrd', '( %s -> %s e. ( B cseg A ) )' % (A2, LIN('A', 'B')))
e1 = w.s([], 'eleq1', '( x = %s -> ( x e. ( B cseg A ) <-> %s e. ( B cseg A ) ) )' % (LIN('A', 'B'), LIN('A', 'B')))
i1 = w.s([el2, e1], 'syl5ibrcom', '( %s -> ( x = %s -> x e. ( B cseg A ) ) )' % (A2, LIN('A', 'B')))
r = w.s([i1], 'rexlimdva', '( %s -> ( E. t e. ( 0 [,] 1 ) x = %s -> x e. ( B cseg A ) ) )' % (A, LIN('A', 'B')))
m = w.s([], 'csegel', '( %s -> ( x e. ( A cseg B ) <-> E. t e. ( 0 [,] 1 ) x = %s ) )' % (A, LIN('A', 'B')))
s = w.s([m, r], 'sylbid', '( %s -> ( x e. ( A cseg B ) -> x e. ( B cseg A ) ) )' % A)
w.qed([s], 'ssrdv', '( %s -> ( A cseg B ) C_ ( B cseg A ) )' % A); run(w)

w = W('csegcom', 'A segment does not depend on the order of its endpoints.')
A = '( A e. CC /\\ B e. CC )'
l1 = w.s([], 'csegcomlem', '( %s -> ( A cseg B ) C_ ( B cseg A ) )' % A)
l2 = w.s([], 'csegcomlem', '( ( B e. CC /\\ A e. CC ) -> ( B cseg A ) C_ ( A cseg B ) )')
l3 = w.s([l2], 'ancoms', '( %s -> ( B cseg A ) C_ ( A cseg B ) )' % A)
w.qed([l1, l3], 'eqssd', '( %s -> ( A cseg B ) = ( B cseg A ) )' % A); run(w)

# ---- csegicc: a segment between points of a real interval stays in it
w = W('csegicc', 'A segment between two points of a closed real interval lies in the interval.')
A = '( ( M e. RR /\\ N e. RR ) /\\ ( P e. ( M [,] N ) /\\ Q e. ( M [,] N ) ) )'; A2 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A
mn = w.s([], 'simpl', '( %s -> ( M e. RR /\\ N e. RR ) )' % A)
p = w.s([], 'simprl', '( %s -> P e. ( M [,] N ) )' % A); q = w.s([], 'simprr', '( %s -> Q e. ( M [,] N ) )' % A)
ss = w.s([mn, w.inst('iccssre')], 'syl', '( %s -> ( M [,] N ) C_ RR )' % A)
pr = w.s([ss, p], 'sseldd', '( %s -> P e. RR )' % A); qr = w.s([ss, q], 'sseldd', '( %s -> Q e. RR )' % A)
pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A); qc = w.s([qr], 'recnd', '( %s -> Q e. CC )' % A)
pc2 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A2); qc2 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A2)
tt = w.s([], 'simpr', '( %s -> t e. ( 0 [,] 1 ) )' % A2); tc = w.s([tt, w.inst('elunitcn')], 'syl', '( %s -> t e. CC )' % A2)
cv = w.s([pc2, qc2, tc, w.inst('cvxid')], 'syl3anc', '( %s -> %s = ( ( ( 1 - t ) x. P ) + ( t x. Q ) ) )' % (A2, LIN('P', 'Q')))
mn2 = w.s([mn], 'adantr', '( %s -> ( M e. RR /\\ N e. RR ) )' % A2)
p2 = w.s([p], 'adantr', '( %s -> P e. ( M [,] N ) )' % A2); q2 = w.s([q], 'adantr', '( %s -> Q e. ( M [,] N ) )' % A2)
ci = w.inst('icccvx'); c1 = w.s([mn2, ci], 'syl', '( %s -> ( ( P e. ( M [,] N ) /\\ Q e. ( M [,] N ) /\\ t e. ( 0 [,] 1 ) ) -> ( ( ( 1 - t ) x. P ) + ( t x. Q ) ) e. ( M [,] N ) ) )' % A2)
c2 = w.s([p2, q2, tt, c1], 'mp3and', '( %s -> ( ( ( 1 - t ) x. P ) + ( t x. Q ) ) e. ( M [,] N ) )' % A2)
el = w.s([cv, c2], 'eqeltrd', '( %s -> %s e. ( M [,] N ) )' % (A2, LIN('P', 'Q')))
e1 = w.s([], 'eleq1', '( x = %s -> ( x e. ( M [,] N ) <-> %s e. ( M [,] N ) ) )' % (LIN('P', 'Q'), LIN('P', 'Q')))
i1 = w.s([el, e1], 'syl5ibrcom', '( %s -> ( x = %s -> x e. ( M [,] N ) ) )' % (A2, LIN('P', 'Q')))
r = w.s([i1], 'rexlimdva', '( %s -> ( E. t e. ( 0 [,] 1 ) x = %s -> x e. ( M [,] N ) ) )' % (A, LIN('P', 'Q')))
m = w.s([pc, qc, w.inst('csegel')], 'syl2anc', '( %s -> ( x e. ( P cseg Q ) <-> E. t e. ( 0 [,] 1 ) x = %s ) )' % (A, LIN('P', 'Q')))
s = w.s([m, r], 'sylbid', '( %s -> ( x e. ( P cseg Q ) -> x e. ( M [,] N ) ) )' % A)
w.qed([s], 'ssrdv', '( %s -> ( P cseg Q ) C_ ( M [,] N ) )' % A); run(w)

# ---- cseglinre, cseglinim
for part, lbl, addl, mull, subl in (('Re', 'cseglinre', 'readd', 'remul2', 'resub'), ('Im', 'cseglinim', 'imadd', 'immul2', 'imsub')):
    w = W(lbl, 'The %s part of a point of the parametrisation of a segment.' % ('real' if part == 'Re' else 'imaginary'))
    A = '( A e. CC /\\ B e. CC /\\ T e. RR )'
    a = w.s([], 'simp1', '( %s -> A e. CC )' % A); b = w.s([], 'simp2', '( %s -> B e. CC )' % A); t = w.s([], 'simp3', '( %s -> T e. RR )' % A)
    tc = w.s([t], 'recnd', '( %s -> T e. CC )' % A); ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % A); tba = w.s([tc, ba], 'mulcld', '( %s -> ( T x. ( B - A ) ) e. CC )' % A)
    s1 = w.s([a, tba, w.inst(addl)], 'syl2anc', '( %s -> ( %s ` %s ) = ( ( %s ` A ) + ( %s ` ( T x. ( B - A ) ) ) ) )' % (A, part, LIN('A', 'B', 'T'), part, part))
    s2 = w.s([t, ba, w.inst(mull)], 'syl2anc', '( %s -> ( %s ` ( T x. ( B - A ) ) ) = ( T x. ( %s ` ( B - A ) ) ) )' % (A, part, part))
    s3 = w.s([b, a, w.inst(subl)], 'syl2anc', '( %s -> ( %s ` ( B - A ) ) = ( ( %s ` B ) - ( %s ` A ) ) )' % (A, part, part, part))
    s4 = w.s([s3], 'oveq2d', '( %s -> ( T x. ( %s ` ( B - A ) ) ) = ( T x. ( ( %s ` B ) - ( %s ` A ) ) ) )' % (A, part, part, part))
    s5 = w.s([s2, s4], 'eqtrd', '( %s -> ( %s ` ( T x. ( B - A ) ) ) = ( T x. ( ( %s ` B ) - ( %s ` A ) ) ) )' % (A, part, part, part))
    s6 = w.s([s5], 'oveq2d', '( %s -> ( ( %s ` A ) + ( %s ` ( T x. ( B - A ) ) ) ) = ( ( %s ` A ) + ( T x. ( ( %s ` B ) - ( %s ` A ) ) ) ) )' % (A, part, part, part, part, part))
    w.qed([s1, s6], 'eqtrd', '( %s -> ( %s ` %s ) = ( ( %s ` A ) + ( T x. ( ( %s ` B ) - ( %s ` A ) ) ) ) )' % (A, part, LIN('A', 'B', 'T'), part, part, part)); run(w)

# ---- ioolin: the open-interval parametrisation
w = W('ioolin', 'A point of the open parametrisation of a real interval lies in the open interval.')
A = '( ( P e. RR /\\ Q e. RR /\\ P < Q ) /\\ T e. ( 0 (,) 1 ) )'
p = w.s([], 'simpl1', '( %s -> P e. RR )' % A); q = w.s([], 'simpl2', '( %s -> Q e. RR )' % A); lt = w.s([], 'simpl3', '( %s -> P < Q )' % A)
t = w.s([], 'simpr', '( %s -> T e. ( 0 (,) 1 ) )' % A); tr = w.s([t, w.inst('elioore')], 'syl', '( %s -> T e. RR )' % A)
to = w.s([t, w.inst('eliooord')], 'syl', '( %s -> ( 0 < T /\\ T < 1 ) )' % A); t0 = w.s([to], 'simpld', '( %s -> 0 < T )' % A); t1 = w.s([to], 'simprd', '( %s -> T < 1 )' % A)
qp = w.s([q, p], 'resubcld', '( %s -> ( Q - P ) e. RR )' % A)
pd = w.s([p, q, w.inst('posdif')], 'syl2anc', '( %s -> ( P < Q <-> 0 < ( Q - P ) ) )' % A); qp0 = w.s([lt, pd], 'mpbid', '( %s -> 0 < ( Q - P ) )' % A)
tqp = w.s([tr, qp], 'remulcld', '( %s -> ( T x. ( Q - P ) ) e. RR )' % A)
g0 = w.s([tr, t0, qp, qp0, w.inst('mulgt0')], 'syl22anc', '( %s -> 0 < ( T x. ( Q - P ) ) )' % A)
la = w.s([tqp, p, w.inst('ltaddpos')], 'syl2anc', '( %s -> ( 0 < ( T x. ( Q - P ) ) <-> P < %s ) )' % (A, LIN('P', 'Q', 'T')))
lo = w.s([g0, la], 'mpbid', '( %s -> P < %s )' % (A, LIN('P', 'Q', 'T')))
r1 = w.s([], '1red', '( %s -> 1 e. RR )' % A)
qpj = w.s([qp, qp0], 'jca', '( %s -> ( ( Q - P ) e. RR /\\ 0 < ( Q - P ) ) )' % A)
lm = w.s([tr, r1, qpj, t1, w.inst('ltmul1a')], 'syl31anc', '( %s -> ( T x. ( Q - P ) ) < ( 1 x. ( Q - P ) ) )' % A)
qpc = w.s([qp], 'recnd', '( %s -> ( Q - P ) e. CC )' % A); m1 = w.s([qpc], 'mullidd', '( %s -> ( 1 x. ( Q - P ) ) = ( Q - P ) )' % A)
lm2 = w.s([lm, m1], 'breqtrd', '( %s -> ( T x. ( Q - P ) ) < ( Q - P ) )' % A)
l2 = w.s([tqp, qp, p, w.inst('ltadd2')], 'syl3anc', '( %s -> ( ( T x. ( Q - P ) ) < ( Q - P ) <-> %s < ( P + ( Q - P ) ) ) )' % (A, LIN('P', 'Q', 'T')))
hi = w.s([lm2, l2], 'mpbid', '( %s -> %s < ( P + ( Q - P ) ) )' % (A, LIN('P', 'Q', 'T')))
pc = w.s([p], 'recnd', '( %s -> P e. CC )' % A); qc = w.s([q], 'recnd', '( %s -> Q e. CC )' % A)
pn = w.s([pc, qc], 'pncan3d', '( %s -> ( P + ( Q - P ) ) = Q )' % A); hi2 = w.s([hi, pn], 'breqtrd', '( %s -> %s < Q )' % (A, LIN('P', 'Q', 'T')))
v = w.s([p, tqp], 'readdcld', '( %s -> %s e. RR )' % (A, LIN('P', 'Q', 'T')))
px = w.s([p], 'rexrd', '( %s -> P e. RR* )' % A); qx = w.s([q], 'rexrd', '( %s -> Q e. RR* )' % A)
e = w.s([px, qx, w.inst('elioo2')], 'syl2anc', '( %s -> ( %s e. ( P (,) Q ) <-> ( %s e. RR /\\ P < %s /\\ %s < Q ) ) )' % (A, LIN('P', 'Q', 'T'), LIN('P', 'Q', 'T'), LIN('P', 'Q', 'T'), LIN('P', 'Q', 'T')))
w.qed([v, lo, hi2, e], 'mpbir3and', '( %s -> %s e. ( P (,) Q ) )' % (A, LIN('P', 'Q', 'T'))); run(w)
