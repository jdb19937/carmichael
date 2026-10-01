"""Sortie ZF2, batch 1: the induced character DChrInd (Mathlib changeLevel):
value lemma, membership, values at integers."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from zf2lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ---- dchrindval: the induced character unfolded
H = '( N e. NN /\\ M e. NN /\\ X e. %s )' % DB('N')
w = W('dchrindval', 'Value of the induced character (Mathlib changeLevel): the function on the residue classes mod M given by X at the class mod N of the representative in ( 0 ..^ M ) for units, and 0 otherwise.')
n = w.s([], 'simp1', '( %s -> N e. NN )' % H); m = w.s([], 'simp2', '( %s -> M e. NN )' % H); x = w.s([], 'simp3', '( %s -> X e. %s )' % (H, DB('N')))
d0 = w.s([], 'df-dchrind', 'DChrInd = ( n e. NN , m e. NN |-> %s )' % INDMPT('n', 'm'))
d1 = w.s([d0], 'a1i', '( %s -> DChrInd = ( n e. NN , m e. NN |-> %s ) )' % (H, INDMPT('n', 'm')))
A2 = '( %s /\\ ( n = N /\\ m = M ) )' % H
ln = w.s([], 'simprl', '( %s -> n = N )' % A2); lm = w.s([], 'simprr', '( %s -> m = M )' % A2)
c, new = w.congr(INDMPT('n', 'm'), {'n': 'N', 'm': 'M'}, A2, {'n': ln, 'm': lm})
assert new == INDMPT('N', 'M'), new
e0 = w.s([], 'fvex', '%s e. _V' % DB('N'))
e1 = w.s([e0], 'mptex', '%s e. _V' % INDMPT('N', 'M'))
e2 = w.s([e1], 'a1i', '( %s -> %s e. _V )' % (H, INDMPT('N', 'M')))
f = w.s([d1, c, n, m, e2], 'ovmpod', '( %s -> %s = %s )' % (H, INDOP('N', 'M'), INDMPT('N', 'M')))
A3 = '( %s /\\ x = X )' % H
lx = w.s([], 'simpr', '( %s -> x = X )' % A3)
c2, new2 = w.congr(INDBODY('N', 'M', 'x'), {'x': 'X'}, A3, {'x': lx})
assert new2 == INDBODY('N', 'M', 'X'), new2
g0 = w.s([], 'fvex', '%s e. _V' % BZ('M'))
g1 = w.s([g0], 'mptex', '%s e. _V' % INDBODY('N', 'M', 'X'))
g2 = w.s([g1], 'a1i', '( %s -> %s e. _V )' % (H, INDBODY('N', 'M', 'X')))
w.qed([f, c2, x, g2], 'fvmptd', '( %s -> %s = %s )' % (H, IND('N', 'M', 'X'), INDBODY('N', 'M', 'X'))); run(w)

ZM = '( Z/nZ ` M )'; ZN = '( Z/nZ ` N )'
def zring_hyps(w, n):
    return (w.s([], 'eqid', '( Z/nZ ` %s ) = ( Z/nZ ` %s )' % (n, n)),
            w.s([], 'eqid', '%s = %s' % (LZ(n), LZ(n))))
def dchr_hyps(w, n):
    """G Z D L eqid hypotheses of the dchr* lemmas at level n"""
    return (w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (n, n)),
            w.s([], 'eqid', '( Z/nZ ` %s ) = ( Z/nZ ` %s )' % (n, n)),
            w.s([], 'eqid', '%s = %s' % (DB(n), DB(n))),
            w.s([], 'eqid', '%s = %s' % (LZ(n), LZ(n))))

# ---- dchrindlem0: the representative map is a bijection ( 0 ..^ M ) --> BM
IFW = 'if ( M = 0 , ZZ , ( 0 ..^ M ) )'
w = W('dchrindlem0', 'Lemma for the induced character: the ring homomorphism ZRHom restricted to ( 0 ..^ M ) is a bijection onto the residue classes mod M (from znf1o).')
z1 = w.s([], 'eqid', '%s = %s' % (ZM, ZM)); z2 = w.s([], 'eqid', '%s = %s' % (BZ('M'), BZ('M')))
z3 = w.s([], 'eqid', '( %s |` %s ) = ( %s |` %s )' % (LZ('M'), IFW, LZ('M'), IFW)); z4 = w.s([], 'eqid', '%s = %s' % (IFW, IFW))
f0 = w.s([z1, z2, z3, z4], 'znf1o', '( M e. NN0 -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (LZ('M'), IFW, IFW, BZ('M')))
n0 = w.s([], 'nnnn0', '( M e. NN -> M e. NN0 )')
f1 = w.s([n0, f0], 'syl', '( M e. NN -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (LZ('M'), IFW, IFW, BZ('M')))
ne = w.s([], 'nnne0', '( M e. NN -> M =/= 0 )')
ifn = w.s([], 'ifnefalse', '( M =/= 0 -> %s = ( 0 ..^ M ) )' % IFW)
ifs = w.s([ne, ifn], 'syl', '( M e. NN -> %s = ( 0 ..^ M ) )' % IFW)
r1 = w.s([ifs], 'reseq2d', '( M e. NN -> ( %s |` %s ) = %s )' % (LZ('M'), IFW, REPF('M')))
e1 = w.s([], 'eqidd', '( M e. NN -> %s = %s )' % (BZ('M'), BZ('M')))
b1 = w.s([r1, ifs, e1], 'f1oeq123d', '( M e. NN -> ( ( %s |` %s ) : %s -1-1-onto-> %s <-> %s : ( 0 ..^ M ) -1-1-onto-> %s ) )' % (LZ('M'), IFW, IFW, BZ('M'), REPF('M'), BZ('M')))
w.qed([f1, b1], 'mpbid', '( M e. NN -> %s : ( 0 ..^ M ) -1-1-onto-> %s )' % (REPF('M'), BZ('M'))); run(w)

# ---- dchrindlem1: the representative is an integer
HK = '( M e. NN /\\ K e. %s )' % BZ('M')
w = W('dchrindlem1', 'Lemma for the induced character: the representative of a residue class mod M is an integer (in ( 0 ..^ M ) ).')
f = w.s([], 'dchrindlem0', '( M e. NN -> %s : ( 0 ..^ M ) -1-1-onto-> %s )' % (REPF('M'), BZ('M')))
f2 = w.s([f], 'adantr', '( %s -> %s : ( 0 ..^ M ) -1-1-onto-> %s )' % (HK, REPF('M'), BZ('M')))
k = w.s([], 'simpr', '( %s -> K e. %s )' % (HK, BZ('M')))
d = w.s([f2, k, w.inst('f1ocnvdm')], 'syl2anc', '( %s -> %s e. ( 0 ..^ M ) )' % (HK, REP('M', 'K')))
ez = w.s([], 'elfzoelz', '( %s e. ( 0 ..^ M ) -> %s e. ZZ )' % (REP('M', 'K'), REP('M', 'K')))
w.qed([d, ez], 'syl', '( %s -> %s e. ZZ )' % (HK, REP('M', 'K'))); run(w)

# ---- dchrindlem2: the representative maps back to the class
w = W('dchrindlem2', 'Lemma for the induced character: the class mod M of the representative of K is K.')
f = w.s([], 'dchrindlem0', '( M e. NN -> %s : ( 0 ..^ M ) -1-1-onto-> %s )' % (REPF('M'), BZ('M')))
f2 = w.s([f], 'adantr', '( %s -> %s : ( 0 ..^ M ) -1-1-onto-> %s )' % (HK, REPF('M'), BZ('M')))
k = w.s([], 'simpr', '( %s -> K e. %s )' % (HK, BZ('M')))
v = w.s([f2, k, w.inst('f1ocnvfv2')], 'syl2anc', '( %s -> ( %s ` %s ) = K )' % (HK, REPF('M'), REP('M', 'K')))
d = w.s([f2, k, w.inst('f1ocnvdm')], 'syl2anc', '( %s -> %s e. ( 0 ..^ M ) )' % (HK, REP('M', 'K')))
r = w.s([d, w.inst('fvres')], 'syl', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (HK, REPF('M'), REP('M', 'K'), LZ('M'), REP('M', 'K')))
w.qed([r, v], 'eqtr3d', '( %s -> ( %s ` %s ) = K )' % (HK, LZ('M'), REP('M', 'K'))); run(w)

# ---- dchrindlem4: equal classes mod M give equal classes mod N when N || M
H4 = '( %s /\\ ( A e. ZZ /\\ B e. ZZ ) /\\ ( %s ` A ) = ( %s ` B ) )' % (H3, LZ('M'), LZ('M'))
w = W('dchrindlem4', 'Lemma for the induced character: two integers in the same class mod M are in the same class mod N when N divides M.')
n = w.s([], 'simp11', '( %s -> N e. NN )' % H4); m = w.s([], 'simp12', '( %s -> M e. NN )' % H4); nm = w.s([], 'simp13', '( %s -> N || M )' % H4)
a = w.s([], 'simp2l', '( %s -> A e. ZZ )' % H4); b = w.s([], 'simp2r', '( %s -> B e. ZZ )' % H4); e = w.s([], 'simp3', '( %s -> ( %s ` A ) = ( %s ` B ) )' % (H4, LZ('M'), LZ('M')))
n0 = w.s([n], 'nnnn0d', '( %s -> N e. NN0 )' % H4); m0 = w.s([m], 'nnnn0d', '( %s -> M e. NN0 )' % H4)
zm1, zm2 = zring_hyps(w, 'M'); zn1, zn2 = zring_hyps(w, 'N')
dm = w.s([m0, a, b, w.s([zm1, zm2], 'zndvds', '( ( M e. NN0 /\\ A e. ZZ /\\ B e. ZZ ) -> ( ( %s ` A ) = ( %s ` B ) <-> M || ( A - B ) ) )' % (LZ('M'), LZ('M')))], 'syl3anc', '( %s -> ( ( %s ` A ) = ( %s ` B ) <-> M || ( A - B ) ) )' % (H4, LZ('M'), LZ('M')))
d1 = w.s([e, dm], 'mpbid', '( %s -> M || ( A - B ) )' % H4)
nz = w.s([n], 'nnzd', '( %s -> N e. ZZ )' % H4); mz = w.s([m], 'nnzd', '( %s -> M e. ZZ )' % H4)
abz = w.s([a, b], 'zsubcld', '( %s -> ( A - B ) e. ZZ )' % H4)
d2 = w.s([nz, mz, abz, nm, d1], 'dvdstrd', '( %s -> N || ( A - B ) )' % H4)
dn = w.s([n0, a, b, w.s([zn1, zn2], 'zndvds', '( ( N e. NN0 /\\ A e. ZZ /\\ B e. ZZ ) -> ( ( %s ` A ) = ( %s ` B ) <-> N || ( A - B ) ) )' % (LZ('N'), LZ('N')))], 'syl3anc', '( %s -> ( ( %s ` A ) = ( %s ` B ) <-> N || ( A - B ) ) )' % (H4, LZ('N'), LZ('N')))
w.qed([d2, dn], 'mpbird', '( %s -> ( %s ` A ) = ( %s ` B ) )' % (H4, LZ('N'), LZ('N'))); run(w)

# ---- dchrindlem5: the value through the representative is the value at any integer preimage
H5 = '( ( %s /\\ X e. %s /\\ K e. %s ) /\\ A e. ZZ /\\ ( %s ` A ) = K )' % (H3, DB('N'), BZ('M'), LZ('M'))
w = W('dchrindlem5', 'Lemma for the induced character: the value of X at the class mod N of the representative of K equals its value at any integer A in the class K.')
h3 = w.s([], 'simp11', '( %s -> %s )' % (H5, H3)); m = w.s([h3], 'simp2d', '( %s -> M e. NN )' % H5)
kk = w.s([], 'simp13', '( %s -> K e. %s )' % (H5, BZ('M'))); a = w.s([], 'simp2', '( %s -> A e. ZZ )' % H5); e = w.s([], 'simp3', '( %s -> ( %s ` A ) = K )' % (H5, LZ('M')))
r1 = w.s([m, kk, w.inst('dchrindlem1')], 'syl2anc', '( %s -> %s e. ZZ )' % (H5, REP('M', 'K')))
r2 = w.s([m, kk, w.inst('dchrindlem2')], 'syl2anc', '( %s -> ( %s ` %s ) = K )' % (H5, LZ('M'), REP('M', 'K')))
r3 = w.s([r2, e], 'eqtr4d', '( %s -> ( %s ` %s ) = ( %s ` A ) )' % (H5, LZ('M'), REP('M', 'K'), LZ('M')))
ra = w.s([r1, a], 'jca', '( %s -> ( %s e. ZZ /\\ A e. ZZ ) )' % (H5, REP('M', 'K')))
r4 = w.s([h3, ra, r3, w.inst('dchrindlem4')], 'syl3anc', '( %s -> ( %s ` %s ) = ( %s ` A ) )' % (H5, LZ('N'), REP('M', 'K'), LZ('N')))
w.qed([r4], 'fveq2d', '( %s -> %s = %s )' % (H5, INDV('N', 'M', 'X', 'K'), EV('X', 'N', 'A'))); run(w)

# ---- dchrindcl: the induced character is a character mod M
w = W('dchrindcl', 'The induced character is a Dirichlet character mod M (Mathlib changeLevel lands in DirichletCharacter R m). Proved through dchrelbasd: values in CC on units, multiplicative on units, 1 at the unit 1.')
g = w.s([], 'eqid', '( DChr ` M ) = ( DChr ` M )'); z = w.s([], 'eqid', '%s = %s' % (ZM, ZM))
b = w.s([], 'eqid', '%s = %s' % (BZ('M'), BZ('M'))); u = w.s([], 'eqid', '%s = %s' % (UZ('M'), UZ('M')))
h3 = w.s([], 'simpl', '( %s -> %s )' % (HX, H3)); n = w.s([h3], 'simp1d', '( %s -> N e. NN )' % HX); m = w.s([h3], 'simp2d', '( %s -> M e. NN )' % HX)
xx = w.s([], 'simpr', '( %s -> X e. %s )' % (HX, DB('N')))
d = w.s([], 'eqid', '%s = %s' % (DB('M'), DB('M')))
# substitution hypotheses .1 - .4
def subst(var, T):
    idx = w.s([], 'id', '( k = %s -> k = %s )' % (T, T))
    st, new = w.congr(INDV('N', 'M', 'X', 'k'), {'k': T}, 'k = %s' % T, {'k': idx})
    assert new == INDV('N', 'M', 'X', T), new
    return st
s1 = subst('x', 'x'); s2 = subst('y', 'y'); s3 = subst('xy', '( x ( .r ` %s ) y )' % ZM); s4 = subst('1', '( 1r ` %s )' % ZM)
# .5 values in CC on units
A5 = '( %s /\\ k e. %s )' % (HX, UZ('M'))
k5 = w.s([], 'simpr', '( %s -> k e. %s )' % (A5, UZ('M')))
kb = w.s([k5, w.s([b, u], 'unitcl', '( k e. %s -> k e. %s )' % (UZ('M'), BZ('M')))], 'syl', '( %s -> k e. %s )' % (A5, BZ('M')))
m5 = w.s([m], 'adantr', '( %s -> M e. NN )' % A5)
r5 = w.s([m5, kb, w.inst('dchrindlem1')], 'syl2anc', '( %s -> %s e. ZZ )' % (A5, REP('M', 'k')))
x5 = w.s([xx], 'adantr', '( %s -> X e. %s )' % (A5, DB('N')))
gn, zn, dn, ln = dchr_hyps(w, 'N')
c5 = w.s([gn, zn, dn, ln, x5, r5], 'dchrzrhcl', '( %s -> %s e. CC )' % (A5, INDV('N', 'M', 'X', 'k')))
# .6 multiplicative on units
A6 = '( %s /\\ ( x e. %s /\\ y e. %s ) )' % (HX, UZ('M'), UZ('M'))
XY = '( x ( .r ` %s ) y )' % ZM
m6 = w.s([m], 'adantr', '( %s -> M e. NN )' % A6); n6 = w.s([n], 'adantr', '( %s -> N e. NN )' % A6)
h36 = w.s([h3], 'adantr', '( %s -> %s )' % (A6, H3)); x6 = w.s([xx], 'adantr', '( %s -> X e. %s )' % (A6, DB('N')))
xu = w.s([], 'simprl', '( %s -> x e. %s )' % (A6, UZ('M'))); yu = w.s([], 'simprr', '( %s -> y e. %s )' % (A6, UZ('M')))
ucl = w.s([b, u], 'unitcl', '( x e. %s -> x e. %s )' % (UZ('M'), BZ('M'))); ucl2 = w.s([b, u], 'unitcl', '( y e. %s -> y e. %s )' % (UZ('M'), BZ('M')))
xb = w.s([xu, ucl], 'syl', '( %s -> x e. %s )' % (A6, BZ('M'))); yb = w.s([yu, ucl2], 'syl', '( %s -> y e. %s )' % (A6, BZ('M')))
m06 = w.s([m6], 'nnnn0d', '( %s -> M e. NN0 )' % A6)
cr = w.s([m06, w.s([z], 'zncrng', '( M e. NN0 -> %s e. CRing )' % ZM)], 'syl', '( %s -> %s e. CRing )' % (A6, ZM))
rg = w.s([cr], 'crngringd', '( %s -> %s e. Ring )' % (A6, ZM))
mr = w.s([], 'eqid', '( .r ` %s ) = ( .r ` %s )' % (ZM, ZM))
xyu = w.s([rg, xu, yu, w.s([u, mr], 'unitmulcl', '( ( %s e. Ring /\\ x e. %s /\\ y e. %s ) -> %s e. %s )' % (ZM, UZ('M'), UZ('M'), XY, UZ('M')))], 'syl3anc', '( %s -> %s e. %s )' % (A6, XY, UZ('M')))
xyb = w.s([xyu, w.s([b, u], 'unitcl', '( %s e. %s -> %s e. %s )' % (XY, UZ('M'), XY, BZ('M')))], 'syl', '( %s -> %s e. %s )' % (A6, XY, BZ('M')))
rx = w.s([m6, xb, w.inst('dchrindlem1')], 'syl2anc', '( %s -> %s e. ZZ )' % (A6, REP('M', 'x'))); ry = w.s([m6, yb, w.inst('dchrindlem1')], 'syl2anc', '( %s -> %s e. ZZ )' % (A6, REP('M', 'y')))
lx = w.s([m6, xb, w.inst('dchrindlem2')], 'syl2anc', '( %s -> ( %s ` %s ) = x )' % (A6, LZ('M'), REP('M', 'x'))); ly = w.s([m6, yb, w.inst('dchrindlem2')], 'syl2anc', '( %s -> ( %s ` %s ) = y )' % (A6, LZ('M'), REP('M', 'y')))
rxy = w.s([rx, ry], 'zmulcld', '( %s -> ( %s x. %s ) e. ZZ )' % (A6, REP('M', 'x'), REP('M', 'y')))
zl = w.s([], 'eqid', '%s = %s' % (LZ('M'), LZ('M')))
rhm = w.s([rg, w.s([zl], 'zrhrhm', '( %s e. Ring -> %s e. ( ZZring RingHom %s ) )' % (ZM, LZ('M'), ZM))], 'syl', '( %s -> %s e. ( ZZring RingHom %s ) )' % (A6, LZ('M'), ZM))
zb = w.s([], 'zringbas', 'ZZ = ( Base ` ZZring )'); zmu = w.s([], 'zringmulr', 'x. = ( .r ` ZZring )')
mul = w.s([rhm, rx, ry, w.s([zb, zmu, mr], 'rhmmul', '( ( %s e. ( ZZring RingHom %s ) /\\ %s e. ZZ /\\ %s e. ZZ ) -> ( %s ` ( %s x. %s ) ) = ( ( %s ` %s ) ( .r ` %s ) ( %s ` %s ) ) )' % (LZ('M'), ZM, REP('M', 'x'), REP('M', 'y'), LZ('M'), REP('M', 'x'), REP('M', 'y'), LZ('M'), REP('M', 'x'), ZM, LZ('M'), REP('M', 'y')))], 'syl3anc',
          '( %s -> ( %s ` ( %s x. %s ) ) = ( ( %s ` %s ) ( .r ` %s ) ( %s ` %s ) ) )' % (A6, LZ('M'), REP('M', 'x'), REP('M', 'y'), LZ('M'), REP('M', 'x'), ZM, LZ('M'), REP('M', 'y')))
mul2 = w.s([lx, ly], 'oveq12d', '( %s -> ( ( %s ` %s ) ( .r ` %s ) ( %s ` %s ) ) = %s )' % (A6, LZ('M'), REP('M', 'x'), ZM, LZ('M'), REP('M', 'y'), XY))
mul3 = w.s([mul, mul2], 'eqtrd', '( %s -> ( %s ` ( %s x. %s ) ) = %s )' % (A6, LZ('M'), REP('M', 'x'), REP('M', 'y'), XY))
t6 = w.s([h36, x6, xyb], '3jca', '( %s -> ( %s /\\ X e. %s /\\ %s e. %s ) )' % (A6, H3, DB('N'), XY, BZ('M')))
v6 = w.s([t6, rxy, mul3, w.inst('dchrindlem5')], 'syl3anc', '( %s -> %s = %s )' % (A6, INDV('N', 'M', 'X', XY), EV('X', 'N', '( %s x. %s )' % (REP('M', 'x'), REP('M', 'y')))))
zm6 = w.s([gn, zn, dn, ln, x6, rx, ry], 'dchrzrhmul', '( %s -> %s = ( %s x. %s ) )' % (A6, EV('X', 'N', '( %s x. %s )' % (REP('M', 'x'), REP('M', 'y'))), INDV('N', 'M', 'X', 'x'), INDV('N', 'M', 'X', 'y')))
c6 = w.s([v6, zm6], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A6, INDV('N', 'M', 'X', XY), INDV('N', 'M', 'X', 'x'), INDV('N', 'M', 'X', 'y')))
# .7 value 1 at the unit
ONEM = '( 1r ` %s )' % ZM
m0 = w.s([m], 'nnnn0d', '( %s -> M e. NN0 )' % HX)
cr7 = w.s([m0, w.s([z], 'zncrng', '( M e. NN0 -> %s e. CRing )' % ZM)], 'syl', '( %s -> %s e. CRing )' % (HX, ZM))
rg7 = w.s([cr7], 'crngringd', '( %s -> %s e. Ring )' % (HX, ZM))
o1 = w.s([], 'eqid', '%s = %s' % (ONEM, ONEM))
ob = w.s([rg7, w.s([b, o1], 'ringidcl', '( %s e. Ring -> %s e. %s )' % (ZM, ONEM, BZ('M')))], 'syl', '( %s -> %s e. %s )' % (HX, ONEM, BZ('M')))
l1 = w.s([rg7, w.s([zl, o1], 'zrh1', '( %s e. Ring -> ( %s ` 1 ) = %s )' % (ZM, LZ('M'), ONEM))], 'syl', '( %s -> ( %s ` 1 ) = %s )' % (HX, LZ('M'), ONEM))
oz = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % HX)
t7 = w.s([h3, xx, ob], '3jca', '( %s -> ( %s /\\ X e. %s /\\ %s e. %s ) )' % (HX, H3, DB('N'), ONEM, BZ('M')))
v7 = w.s([t7, oz, l1, w.inst('dchrindlem5')], 'syl3anc', '( %s -> %s = %s )' % (HX, INDV('N', 'M', 'X', ONEM), EV('X', 'N', '1')))
o7 = w.s([gn, zn, dn, ln, xx], 'dchrzrh1', '( %s -> %s = 1 )' % (HX, EV('X', 'N', '1')))
c7 = w.s([v7, o7], 'eqtrd', '( %s -> %s = 1 )' % (HX, INDV('N', 'M', 'X', ONEM)))
mem = w.s([g, z, b, u, m, d, s1, s2, s3, s4, c5, c6, c7], 'dchrelbasd', '( %s -> %s e. %s )' % (HX, INDBODY('N', 'M', 'X'), DB('M')))
val = w.s([n, m, xx, w.inst('dchrindval')], 'syl3anc', '( %s -> %s = %s )' % (HX, IND('N', 'M', 'X'), INDBODY('N', 'M', 'X')))
w.qed([val, mem], 'eqeltrd', '( %s -> %s e. %s )' % (HX, IND('N', 'M', 'X'), DB('M'))); run(w)

# ---- dchrindval2: the value at an integer, if-form
HA = '( %s /\\ A e. ZZ )' % HX
LMA = '( %s ` A )' % LZ('M')
w = W('dchrindval2', 'Value of the induced character at the class of an integer A: X at the class of A mod N when A is coprime to M, and 0 otherwise.')
h3 = w.s([], 'simpl', '( %s -> %s )' % (HX, H3)); n = w.s([h3], 'simp1d', '( %s -> N e. NN )' % HX); m = w.s([h3], 'simp2d', '( %s -> M e. NN )' % HX)
xx = w.s([], 'simpr', '( %s -> X e. %s )' % (HX, DB('N')))
val = w.s([n, m, xx, w.inst('dchrindval')], 'syl3anc', '( %s -> %s = %s )' % (HX, IND('N', 'M', 'X'), INDBODY('N', 'M', 'X')))
val2 = w.s([val], 'adantr', '( %s -> %s = %s )' % (HA, IND('N', 'M', 'X'), INDBODY('N', 'M', 'X')))
f1 = w.s([val2], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (HA, IND('N', 'M', 'X'), LMA, INDBODY('N', 'M', 'X'), LMA))
ma = w.s([m], 'adantr', '( %s -> M e. NN )' % HA); a = w.s([], 'simpr', '( %s -> A e. ZZ )' % HA)
m0 = w.s([ma], 'nnnn0d', '( %s -> M e. NN0 )' % HA)
z = w.s([], 'eqid', '%s = %s' % (ZM, ZM)); b = w.s([], 'eqid', '%s = %s' % (BZ('M'), BZ('M'))); zl = w.s([], 'eqid', '%s = %s' % (LZ('M'), LZ('M')))
fo = w.s([m0, w.s([z, b, zl], 'znzrhfo', '( M e. NN0 -> %s : ZZ -onto-> %s )' % (LZ('M'), BZ('M')))], 'syl', '( %s -> %s : ZZ -onto-> %s )' % (HA, LZ('M'), BZ('M')))
ff = w.s([fo, w.inst('fof')], 'syl', '( %s -> %s : ZZ --> %s )' % (HA, LZ('M'), BZ('M')))
lab = w.s([ff, a], 'ffvelcdmd', '( %s -> %s e. %s )' % (HA, LMA, BZ('M')))
IFV = 'if ( %s e. %s , %s , 0 )' % (LMA, UZ('M'), INDV('N', 'M', 'X', LMA))
e1 = w.s([], 'fvex', '%s e. _V' % INDV('N', 'M', 'X', LMA)); e2 = w.s([], 'c0ex', '0 e. _V')
ex = w.s([w.s([e1, e2], 'ifex', '%s e. _V' % IFV)], 'a1i', '( %s -> %s e. _V )' % (HA, IFV))
mv, valtxt = mptval(w, HA, 'k', BZ('M'), 'if ( k e. %s , %s , 0 )' % (UZ('M'), INDV('N', 'M', 'X', 'k')), LMA, lab, exs=ex)
assert valtxt == IFV, valtxt
u = w.s([], 'eqid', '%s = %s' % (UZ('M'), UZ('M')))
un = w.s([m0, a, w.s([z, u, zl], 'znunit', '( ( M e. NN0 /\\ A e. ZZ ) -> ( %s e. %s <-> %s ) )' % (LMA, UZ('M'), COP('A', 'M')))], 'syl2anc', '( %s -> ( %s e. %s <-> %s ) )' % (HA, LMA, UZ('M'), COP('A', 'M')))
h3a = w.s([h3], 'adantr', '( %s -> %s )' % (HA, H3)); xa = w.s([xx], 'adantr', '( %s -> X e. %s )' % (HA, DB('N')))
t = w.s([h3a, xa, lab], '3jca', '( %s -> ( %s /\\ X e. %s /\\ %s e. %s ) )' % (HA, H3, DB('N'), LMA, BZ('M')))
ee = w.s([], 'eqidd', '( %s -> %s = %s )' % (HA, LMA, LMA))
v5 = w.s([t, a, ee, w.inst('dchrindlem5')], 'syl3anc', '( %s -> %s = %s )' % (HA, INDV('N', 'M', 'X', LMA), EV('X', 'N', 'A')))
ifb = w.s([un, v5], 'ifbieq1d', '( %s -> %s = if ( %s , %s , 0 ) )' % (HA, IFV, COP('A', 'M'), EV('X', 'N', 'A')))
w.qed([f1, mv, ifb], '3eqtrd', '( %s -> ( %s ` %s ) = if ( %s , %s , 0 ) )' % (HA, IND('N', 'M', 'X'), LMA, COP('A', 'M'), EV('X', 'N', 'A'))); run(w)

# ---- dchrindval1: the coprime case (Mathlib changeLevel_eq_cast_of_dvd')
HA1 = '( %s /\\ A e. ZZ /\\ %s )' % (HX, COP('A', 'M'))
w = W('dchrindval1', 'The characterising property of the induced character (Mathlib changeLevel_eq_cast_of_dvd): at the class of an integer A coprime to M it agrees with X at the class of A mod N.')
v = w.s([w.s([], '3simpa', '( %s -> %s )' % (HA1, HA)), w.inst('dchrindval2')], 'syl', '( %s -> ( %s ` %s ) = if ( %s , %s , 0 ) )' % (HA1, IND('N', 'M', 'X'), LMA, COP('A', 'M'), EV('X', 'N', 'A')))
c = w.s([], 'simp3', '( %s -> %s )' % (HA1, COP('A', 'M')))
i = w.s([c], 'iftrued', '( %s -> if ( %s , %s , 0 ) = %s )' % (HA1, COP('A', 'M'), EV('X', 'N', 'A'), EV('X', 'N', 'A')))
w.qed([v, i], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (HA1, IND('N', 'M', 'X'), LMA, EV('X', 'N', 'A'))); run(w)

# ---- dchrindval0: the non-coprime case
HA0 = '( %s /\\ A e. ZZ /\\ -. %s )' % (HX, COP('A', 'M'))
w = W('dchrindval0', 'The induced character vanishes at the class of an integer not coprime to M.')
v = w.s([w.s([], '3simpa', '( %s -> %s )' % (HA0, HA)), w.inst('dchrindval2')], 'syl', '( %s -> ( %s ` %s ) = if ( %s , %s , 0 ) )' % (HA0, IND('N', 'M', 'X'), LMA, COP('A', 'M'), EV('X', 'N', 'A')))
c = w.s([], 'simp3', '( %s -> -. %s )' % (HA0, COP('A', 'M')))
i = w.s([c], 'iffalsed', '( %s -> if ( %s , %s , 0 ) = 0 )' % (HA0, COP('A', 'M'), EV('X', 'N', 'A')))
w.qed([v, i], 'eqtrd', '( %s -> ( %s ` %s ) = 0 )' % (HA0, IND('N', 'M', 'X'), LMA)); run(w)
