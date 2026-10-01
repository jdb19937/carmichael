"""Sortie A1, batch 5: the windowed reservoir goodPrimesW and the analysis
window relation InWindow (DefsW.lean)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a1lib; from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

SMOOTH = lambda Q, Y: 'A. p e. Prime ( p || ( %s - 1 ) -> p <_ %s )' % (Q, Y)
CONDW = lambda Q, W, Y: '( %s e. Prime /\\ %s < %s /\\ %s )' % (Q, W, Q, SMOOTH(Q, Y))
RABW = lambda Z, W, Y: '{ q e. ( 0 ... %s ) | %s }' % (Z, CONDW('q', W, Y))
GWM = lambda Z, W: '( y e. NN0 |-> %s )' % RABW(Z, W, 'y')
GW = lambda Z, W, Y: '( ( %s goodPrimesW %s ) ` %s )' % (Z, W, Y)
A2W = '( Z e. NN0 /\\ W e. NN0 )'
A3W = '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )'


def qedlast(w):
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]


# ------------------------------------------------------------- goodPrimesW
w = W('goodprimeswfval', 'The curried value of goodPrimesW: the mapping y |-> the windowed reservoir.')
A = '( z = Z /\\ w = W )'
l1 = w.s([], 'simpl', '( %s -> z = Z )' % A); l2 = w.s([], 'simpr', '( %s -> w = W )' % A)
cg, b = w.congr(GWM('z', 'w'), {'z': 'Z', 'w': 'W'}, A, {'z': l1, 'w': l2}); assert b == GWM('Z', 'W'), b
d0 = w.s([], 'df-goodprimesw', 'goodPrimesW = ( z e. NN0 , w e. NN0 |-> %s )' % GWM('z', 'w'))
r = w.s([], 'nn0ex', 'NN0 e. _V'); x0 = w.s([r], 'mptex', '%s e. _V' % GWM('Z', 'W'))
w.qed([cg, d0, x0], 'ovmpoa', '( %s -> ( Z goodPrimesW W ) = %s )' % (A2W, GWM('Z', 'W')))
run(w)

w = W('goodprimeswval', 'Value of goodPrimesW: the primes q <_ Z above W with q - 1 smooth up to Y (Lean: goodPrimesW).')
z0 = w.s([], 'simp1', '( %s -> Z e. NN0 )' % A3W)
w0 = w.s([], 'simp2', '( %s -> W e. NN0 )' % A3W)
y0 = w.s([], 'simp3', '( %s -> Y e. NN0 )' % A3W)
f = w.s([z0, w0, w.inst('goodprimeswfval')], 'syl2anc', '( %s -> ( Z goodPrimesW W ) = %s )' % (A3W, GWM('Z', 'W')))
A4 = '( %s /\\ y = Y )' % A3W
l1 = w.s([], 'simpr', '( %s -> y = Y )' % A4)
cg, b = w.congr(RABW('Z', 'W', 'y'), {'y': 'Y'}, A4, {'y': l1}); assert b == RABW('Z', 'W', 'Y'), b
o = w.s([], 'ovex', '( 0 ... Z ) e. _V'); x0 = w.s([o], 'rabex', '%s e. _V' % RABW('Z', 'W', 'Y'))
x0d = w.s([x0], 'a1i', '( %s -> %s e. _V )' % (A3W, RABW('Z', 'W', 'Y')))
w.qed([f, cg, y0, x0d], 'fvmptd', '( %s -> %s = %s )' % (A3W, GW('Z', 'W', 'Y'), RABW('Z', 'W', 'Y')))
run(w)

w = W('elgoodprimesw', 'Membership in the windowed reservoir (Lean: Finset.mem_filter).')
v = w.s([], 'goodprimeswval', '( %s -> %s = %s )' % (A3W, GW('Z', 'W', 'Y'), RABW('Z', 'W', 'Y')))
e1 = w.s([v], 'eleq2d', '( %s -> ( Q e. %s <-> Q e. %s ) )' % (A3W, GW('Z', 'W', 'Y'), RABW('Z', 'W', 'Y')))
idq = w.s([], 'id', '( q = Q -> q = Q )')
cgw, bw = w.wcongr(CONDW('q', 'W', 'Y'), {'q': 'Q'}, 'q = Q', {'q': idq}); assert bw == CONDW('Q', 'W', 'Y'), bw
er = w.s([cgw], 'elrab', '( Q e. %s <-> ( Q e. ( 0 ... Z ) /\\ %s ) )' % (RABW('Z', 'W', 'Y'), CONDW('Q', 'W', 'Y')))
erd = w.s([er], 'a1i', '( %s -> ( Q e. %s <-> ( Q e. ( 0 ... Z ) /\\ %s ) ) )' % (A3W, RABW('Z', 'W', 'Y'), CONDW('Q', 'W', 'Y')))
w.qed([e1, erd], 'bitrd', '( %s -> ( Q e. %s <-> ( Q e. ( 0 ... Z ) /\\ %s ) ) )' % (A3W, GW('Z', 'W', 'Y'), CONDW('Q', 'W', 'Y')))
run(w)

w = W('goodprimeswfi', 'The windowed reservoir is a finite set of primes.')
v = w.s([], 'goodprimeswval', '( %s -> %s = %s )' % (A3W, GW('Z', 'W', 'Y'), RABW('Z', 'W', 'Y')))
R = RABW('Z', 'W', 'Y'); D = '( 0 ... Z )'; inner = CONDW('q', 'W', 'Y')
s1 = w.s([], 'simp1', '( %s -> q e. Prime )' % inner)
s1i = w.s([s1], 'a1i', '( q e. %s -> ( %s -> q e. Prime ) )' % (D, inner))
rg = w.s([s1i], 'rgen', 'A. q e. %s ( %s -> q e. Prime )' % (D, inner))
ss = w.s([rg, w.inst('rabss')], 'mpbir', '%s C_ Prime' % R)
fz = w.s([], 'fzfi', '%s e. Fin' % D); fi = w.s([fz, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % R)
fp = w.s([ss, fi, w.inst('elfpw')], 'mpbir2an', '%s e. ( ~P Prime i^i Fin )' % R)
fpd = w.s([fp], 'a1i', '( %s -> %s e. ( ~P Prime i^i Fin ) )' % (A3W, R))
w.qed([v, fpd], 'eqeltrd', '( %s -> %s e. ( ~P Prime i^i Fin ) )' % (A3W, GW('Z', 'W', 'Y')))
run(w)

# --------------------------------------------------------------- InWindow
body = defbody('df-inwindow')
assert body.startswith('{ <. a , b >. |') and body.endswith('}'), body
wff = body[len('{ <. a , b >. |'):-1].strip()
WFF = lambda A, B: sub(wff, {'a': A, 'b': B})
node = parse_wff(wff); assert node.kind == 'and', node.kind
TYP, CONJ = [k.text() for k in node.kids]
TA = 'aa e. ( ( RR X. RR ) X. NN0 )'.replace('aa', 'a')
cn = parse_wff(CONJ); L, R2 = [k.text() for k in cn.kids]
ln = parse_wff(L); LL, LR = [k.text() for k in ln.kids]
rn = parse_wff(R2); RL, RR2 = [k.text() for k in rn.kids]
ZLO, ZHI = [k.text() for k in parse_wff(LL).kids]
WLO, WHI = [k.text() for k in parse_wff(LR).kids]
YLO, YHI = [k.text() for k in parse_wff(RL).kids]
TLO, THI = [k.text() for k in parse_wff(RR2).kids]

HH = '<. <. C , E >. , N >.'
BB = '<. <. Z , W >. , <. Y , T >. >.'
REL = '%s InWindow %s' % (HH, BB)
TYPE3 = '( ( C e. RR /\\ E e. RR /\\ N e. NN0 ) /\\ ( Z e. NN0 /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) )'
SUBST = {'C': 'C', 'E': 'E', 'N': 'N', 'Z': 'Z', 'W': 'W', 'Y': 'Y', 'T': 'T'}

w = W('inwinrel', 'InWindow is a relation.')
d = w.s([], 'df-inwindow', 'InWindow = %s' % body)
r = w.s([d], 'releqi', '( Rel InWindow <-> Rel %s )' % body)
ro = w.s([], 'relopab', 'Rel %s' % body)
w.qed([ro, r], 'mpbir', 'Rel InWindow')
run(w)

w = W('inwinbr', 'The relation InWindow unfolded: the scales b = <. <. z , w >. , <. y , T >. >. lie in the analysis window of the parameters a = <. <. C1 , E >. , n >. .')
A = '( a = A /\\ b = B )'
l1 = w.s([], 'simpl', '( %s -> a = A )' % A); l2 = w.s([], 'simpr', '( %s -> b = B )' % A)
c, wAB = w.wcongr(wff, {'a': 'A', 'b': 'B'}, A, {'a': l1, 'b': l2}); assert wAB == WFF('A', 'B'), wAB
d = w.s([], 'df-inwindow', 'InWindow = %s' % body)
w.qed([c, d], 'brabga', '( ( A e. V /\\ B e. W ) -> ( A InWindow B <-> %s ) )' % WFF('A', 'B'))
run(w)

w = W('inwinex', 'The arguments of InWindow are sets.')
rel = w.s([], 'inwinrel', 'Rel InWindow'); bi = w.inst('brrelex12')
w.qed([rel, bi], 'mpan', '( A InWindow B -> ( A e. _V /\\ B e. _V ) )')
run(w)


def relbody(w, ante):
    """( ante -> WFF(HH,BB) ) from the relation itself; ante has REL as a conjunct
    proved by relstep"""
    hx = w.s([], 'opex', '%s e. _V' % HH); hxd = w.s([hx], 'a1i', '( %s -> %s e. _V )' % (ante, HH))
    bx = w.s([], 'opex', '%s e. _V' % BB); bxd = w.s([bx], 'a1i', '( %s -> %s e. _V )' % (ante, BB))
    return w.s([hxd, bxd, w.inst('inwinbr')], 'syl2anc', '( %s -> ( %s <-> %s ) )' % (ante, REL, WFF(HH, BB)))


w = W('inwintyp', 'The arguments of InWindow at explicit tuples have their declared types.')
br = relbody(w, REL)
i = w.s([], 'id', '( %s -> %s )' % (REL, REL))
d = w.s([i, br], 'mpbid', '( %s -> %s )' % (REL, WFF(HH, BB)))
t = w.s([d], 'simpld', '( %s -> %s )' % (REL, sub(TYP, {'a': HH, 'b': BB})))
ta = w.s([t], 'simpld', '( %s -> %s e. ( ( RR X. RR ) X. NN0 ) )' % (REL, HH))
tb = w.s([t], 'simprd', '( %s -> %s e. ( ( NN0 X. NN0 ) X. ( NN0 X. NN0 ) ) )' % (REL, BB))
xa = w.s([ta, w.inst('opelxp')], 'sylib', '( %s -> ( <. C , E >. e. ( RR X. RR ) /\\ N e. NN0 ) )' % REL)
xa1 = w.s([xa], 'simpld', '( %s -> <. C , E >. e. ( RR X. RR ) )' % REL)
nn = w.s([xa], 'simprd', '( %s -> N e. NN0 )' % REL)
xa2 = w.s([xa1, w.inst('opelxp')], 'sylib', '( %s -> ( C e. RR /\\ E e. RR ) )' % REL)
cc = w.s([xa2], 'simpld', '( %s -> C e. RR )' % REL)
ee = w.s([xa2], 'simprd', '( %s -> E e. RR )' % REL)
g1 = w.s([cc, ee, nn], '3jca', '( %s -> ( C e. RR /\\ E e. RR /\\ N e. NN0 ) )' % REL)
xb = w.s([tb, w.inst('opelxp')], 'sylib', '( %s -> ( <. Z , W >. e. ( NN0 X. NN0 ) /\\ <. Y , T >. e. ( NN0 X. NN0 ) ) )' % REL)
xb1 = w.s([xb], 'simpld', '( %s -> <. Z , W >. e. ( NN0 X. NN0 ) )' % REL)
xb2 = w.s([xb], 'simprd', '( %s -> <. Y , T >. e. ( NN0 X. NN0 ) )' % REL)
g2 = w.s([xb1, w.inst('opelxp')], 'sylib', '( %s -> ( Z e. NN0 /\\ W e. NN0 ) )' % REL)
g3 = w.s([xb2, w.inst('opelxp')], 'sylib', '( %s -> ( Y e. NN0 /\\ T e. NN0 ) )' % REL)
w.qed([g1, g2, g3], '3jca', '( %s -> %s )' % (REL, TYPE3))
run(w)

# the eight conjuncts at explicit tuples
EZLO = sub(ZLO, {'a': HH, 'b': BB}); EZHI = sub(ZHI, {'a': HH, 'b': BB})
EWLO = sub(WLO, {'a': HH, 'b': BB}); EWHI = sub(WHI, {'a': HH, 'b': BB})
EYLO = sub(YLO, {'a': HH, 'b': BB}); EYHI = sub(YHI, {'a': HH, 'b': BB})
ETLO = sub(TLO, {'a': HH, 'b': BB}); ETHI = sub(THI, {'a': HH, 'b': BB})

ZR = '( ( C x. ( ell2 ` N ) ) x. ( ell3 ` N ) )'
Q99 = '( ; 9 9 / ; ; 1 0 0 )'
NZLO = '%s <_ Z' % ZR
NZHI = 'Z <_ ( 4 x. %s )' % ZR
NWLO = '( Z ^c %s ) <_ ( W + 1 )' % Q99
NWHI = 'W <_ ( 4 x. ( Z ^c %s ) )' % Q99
NYLO = '( Z ^c ( 1 - E ) ) <_ Y'
NYHI = 'Y <_ ( 4 x. ( Z ^c ( 1 - E ) ) )'
NTLO = '( 3 x. ( ell2 ` N ) ) <_ T'
NTHI = 'T <_ ( 5 x. ( ell2 ` N ) )'
WIN = '( ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (
    NZLO, NZHI, NWLO, NWHI, NYLO, NYHI, NTLO, NTHI)

w = W('elinwin', 'The analysis window at explicit tuples: the eight bounds of Lean\'s InWindow structure.')
A = TYPE3
g1 = w.s([], 'simp1', '( %s -> ( C e. RR /\\ E e. RR /\\ N e. NN0 ) )' % A)
g2 = w.s([], 'simp2', '( %s -> ( Z e. NN0 /\\ W e. NN0 ) )' % A)
g3 = w.s([], 'simp3', '( %s -> ( Y e. NN0 /\\ T e. NN0 ) )' % A)
cc = w.s([g1], 'simp1d', '( %s -> C e. RR )' % A)
ee = w.s([g1], 'simp2d', '( %s -> E e. RR )' % A)
nn = w.s([g1], 'simp3d', '( %s -> N e. NN0 )' % A)
zz = w.s([g2], 'simpld', '( %s -> Z e. NN0 )' % A)
ww = w.s([g2], 'simprd', '( %s -> W e. NN0 )' % A)
yy = w.s([g3], 'simpld', '( %s -> Y e. NN0 )' % A)
tt = w.s([g3], 'simprd', '( %s -> T e. NN0 )' % A)
setmap = {}
for nm, st in [('C', cc), ('E', ee), ('N', nn), ('Z', zz), ('W', ww), ('Y', yy), ('T', tt)]:
    setmap[nm] = w.s([st], 'elexd', '( %s -> %s e. _V )' % (A, nm))
br = relbody(w, A)
st, res = evaluate(w, A, WFF(HH, BB), setmap, wff=True)
br2 = w.s([br, st], 'bitrd', '( %s -> ( %s <-> %s ) )' % (A, REL, res))
nodeR = parse_wff(res); assert nodeR.kind == 'and', nodeR.kind
TYPR, CONJR = [k.text() for k in nodeR.kids]
assert CONJR == WIN, 'CONJ mismatch:\n%s\n%s' % (CONJR, WIN)
# the typing conjunct is true under A
oce = w.s([cc, ee, w.inst('opelxpi')], 'syl2anc', '( %s -> <. C , E >. e. ( RR X. RR ) )' % A)
oa = w.s([oce, nn, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( ( RR X. RR ) X. NN0 ) )' % (A, HH))
ozw = w.s([zz, ww, w.inst('opelxpi')], 'syl2anc', '( %s -> <. Z , W >. e. ( NN0 X. NN0 ) )' % A)
oyt = w.s([yy, tt, w.inst('opelxpi')], 'syl2anc', '( %s -> <. Y , T >. e. ( NN0 X. NN0 ) )' % A)
ob = w.s([ozw, oyt, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( ( NN0 X. NN0 ) X. ( NN0 X. NN0 ) ) )' % (A, BB))
ty = w.s([oa, ob], 'jca', '( %s -> %s )' % (A, TYPR))
bt = w.s([ty], 'biantrurd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (A, CONJR, TYPR, CONJR))
w.qed([br2, bt], 'bitr4d', '( %s -> ( %s <-> %s ) )' % (A, REL, CONJR))
run(w)

w = W('inwind', 'The eight bounds of the analysis window, from the relation itself.')
ty = w.s([], 'inwintyp', '( %s -> %s )' % (REL, TYPE3))
bi = w.s([ty, w.inst('elinwin')], 'syl', '( %s -> ( %s <-> %s ) )' % (REL, REL, WIN))
i = w.s([], 'id', '( %s -> %s )' % (REL, REL))
w.qed([i, bi], 'mpbid', '( %s -> %s )' % (REL, WIN))
run(w)

PROJ = [('inwinzlo', NZLO, ['simpld', 'simpld', 'simpld'], 'the scale z is at least C1 * ell2 n * ell3 n'),
        ('inwinzhi', NZHI, ['simpld', 'simpld', 'simprd'], 'the scale z is at most 4 times C1 * ell2 n * ell3 n'),
        ('inwinwlo', NWLO, ['simpld', 'simprd', 'simpld'], 'the cut w + 1 is at least z ^ ( 99 / 100 )'),
        ('inwinwhi', NWHI, ['simpld', 'simprd', 'simprd'], 'the cut w is at most 4 times z ^ ( 99 / 100 )'),
        ('inwinylo', NYLO, ['simprd', 'simpld', 'simpld'], 'the smoothness bound y is at least z ^ ( 1 - E )'),
        ('inwinyhi', NYHI, ['simprd', 'simpld', 'simprd'], 'the smoothness bound y is at most 4 times z ^ ( 1 - E )'),
        ('inwintlo', NTLO, ['simprd', 'simprd', 'simpld'], 'the reservoir size T is at least 3 * ell2 n'),
        ('inwinthi', NTHI, ['simprd', 'simprd', 'simprd'], 'the reservoir size T is at most 5 * ell2 n')]
LVL1 = ['( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (NZLO, NZHI, NWLO, NWHI),
        '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (NYLO, NYHI, NTLO, NTHI)]
LVL2 = ['( %s /\\ %s )' % (NZLO, NZHI), '( %s /\\ %s )' % (NWLO, NWHI),
        '( %s /\\ %s )' % (NYLO, NYHI), '( %s /\\ %s )' % (NTLO, NTHI)]
for k, (lab, concl, refs, desc) in enumerate(PROJ):
    w = W(lab, 'Projection of the analysis window: %s.' % desc)
    d = w.s([], 'inwind', '( %s -> %s )' % (REL, WIN))
    a = w.s([d], refs[0], '( %s -> %s )' % (REL, LVL1[k // 4]))
    b = w.s([a], refs[1], '( %s -> %s )' % (REL, LVL2[k // 2]))
    w.qed([b], refs[2], '( %s -> %s )' % (REL, concl))
    run(w)

# ------------------------------------------------------- inWindow_exact
from lin import linarith
import num

L2 = '( ell2 ` N )'
L3 = '( ell3 ` N )'
ZR2 = '( ( C x. %s ) x. %s )' % (L2, L3)
CL2 = '( C x. %s )' % L2
ZS = '( C zscale N )'
X99 = '( %s ^c %s )' % (ZS, Q99)
WF = '( Nfloor ` %s )' % X99
XE = '( %s ^c ( 1 - E ) )' % ZS
YEV = '( ( C yscaleE N ) ` E )'
TS = '( Tscale ` N )'
SUBW = {'Z': ZS, 'W': WF, 'Y': YEV, 'T': TS}
G = lambda s: sub(s, SUBW)
AX = ('( ( C e. RR /\\ 1 <_ C ) /\\ ( E e. RR /\\ 0 < E /\\ E <_ ( 1 / 2 ) ) /\\ '
      '( N e. ( ZZ>= ` 3 ) /\\ 1 <_ %s /\\ 1 <_ %s ) )' % (L2, L3))

w = W('inwinexact', 'The scales built by the algorithm lie in the analysis window (Lean: inWindow_exact).  The threshold N e. ( ZZ>= ` 3 ) replaces Lean\'s n : NN; Lean\'s hypothesis 1 <_ ell2 n forces it, and the only consumer sits under an eventual filter.')
p1 = w.s([], 'simp1', '( %s -> ( C e. RR /\\ 1 <_ C ) )' % AX)
p2 = w.s([], 'simp2', '( %s -> ( E e. RR /\\ 0 < E /\\ E <_ ( 1 / 2 ) ) )' % AX)
p3 = w.s([], 'simp3', '( %s -> ( N e. ( ZZ>= ` 3 ) /\\ 1 <_ %s /\\ 1 <_ %s ) )' % (AX, L2, L3))
cr = w.s([p1], 'simpld', '( %s -> C e. RR )' % AX)
c1 = w.s([p1], 'simprd', '( %s -> 1 <_ C )' % AX)
er = w.s([p2], 'simp1d', '( %s -> E e. RR )' % AX)
eh = w.s([p2], 'simp3d', '( %s -> E <_ ( 1 / 2 ) )' % AX)
n3 = w.s([p3], 'simp1d', '( %s -> N e. ( ZZ>= ` 3 ) )' % AX)
l21 = w.s([p3], 'simp2d', '( %s -> 1 <_ %s )' % (AX, L2))
l31 = w.s([p3], 'simp3d', '( %s -> 1 <_ %s )' % (AX, L3))
one = w.s([], '1red', '( %s -> 1 e. RR )' % AX)
zero = w.s([], '0red', '( %s -> 0 e. RR )' % AX)
le01 = w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % AX)


def letr(a, b, c, ar, br, cr_, hab, hbc):
    return w.s([ar, br, cr_, hab, hbc], 'letrd', '( %s -> %s <_ %s )' % (AX, a, c))


c0 = letr('0', '1', 'C', zero, one, cr, le01, c1)
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % AX)
nn = w.s([n2, w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % AX)
n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % AX)
l2r = w.s([n2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (AX, L2))
l3r = w.s([n3, w.inst('ell3cl')], 'syl', '( %s -> %s e. RR )' % (AX, L3))
cl2r = w.s([cr, l2r], 'remulcld', '( %s -> %s e. RR )' % (AX, CL2))
zrr = w.s([cl2r, l3r], 'remulcld', '( %s -> %s e. RR )' % (AX, ZR2))
m1 = w.s([cr, l2r, c0, l21], 'lemulge11d', '( %s -> C <_ %s )' % (AX, CL2))
g1 = letr('1', 'C', CL2, one, cr, cl2r, c1, m1)
g0 = letr('0', '1', CL2, zero, one, cl2r, le01, g1)
m2 = w.s([cl2r, l3r, g0, l31], 'lemulge11d', '( %s -> %s <_ %s )' % (AX, CL2, ZR2))
zr1 = letr('1', CL2, ZR2, one, cl2r, zrr, g1, m2)
zr0 = letr('0', '1', ZR2, zero, one, zrr, le01, zr1)
# z
zcl = w.s([cr, n3, w.inst('zscalecl')], 'syl2anc', '( %s -> %s e. NN0 )' % (AX, ZS))
zred = w.s([zcl], 'nn0red', '( %s -> %s e. RR )' % (AX, ZS))
zge0 = w.s([zcl], 'nn0ge0d', '( %s -> 0 <_ %s )' % (AX, ZS))
zlo = w.s([cr, n3, w.inst('zscalege')], 'syl2anc', '( %s -> %s )' % (AX, G(NZLO)))
z1 = letr('1', ZR2, ZS, one, zrr, zred, zr1, zlo)
zlt = w.s([cr, n3, zr0, w.inst('zscalelt')], 'syl3anc', '( %s -> %s < ( %s + 1 ) )' % (AX, ZS, ZR2))
zhi = linarith(w, AX, [zlt, zr1], G(NZHI), leaves={ZR2: zrr, ZS: zred})
# w
q99r = w.s([num.fact(w, Q99, 'RR')], 'a1i', '( %s -> %s e. RR )' % (AX, Q99))
x9r = w.s([zred, zge0, q99r], 'recxpcld', '( %s -> %s e. RR )' % (AX, X99))
x90 = w.s([zred, zge0, q99r], 'cxpge0d', '( %s -> 0 <_ %s )' % (AX, X99))
wcl = w.s([x9r, w.inst('nfloorcl')], 'syl', '( %s -> %s e. NN0 )' % (AX, WF))
wred = w.s([wcl], 'nn0red', '( %s -> %s e. RR )' % (AX, WF))
wlt = w.s([x9r, w.inst('nfloorlt')], 'syl', '( %s -> %s < ( %s + 1 ) )' % (AX, X99, WF))
wsum = w.s([wred, one], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (AX, WF))
wlo = w.s([x9r, wsum, wlt], 'ltled', '( %s -> %s )' % (AX, G(NWLO)))
wle = w.s([x9r, x90, w.inst('nfloorle')], 'syl2anc', '( %s -> %s <_ %s )' % (AX, WF, X99))
whi = linarith(w, AX, [wle, x90], G(NWHI), leaves={X99: x9r, WF: wred})
# y
esub = w.s([one, er], 'resubcld', '( %s -> ( 1 - E ) e. RR )' % AX)
me0 = linarith(w, AX, [eh], '0 <_ ( 1 - E )', leaves={'E': er})
xer = w.s([zred, zge0, esub], 'recxpcld', '( %s -> %s e. RR )' % (AX, XE))
z0c = w.s([], '0red', '( %s -> 0 e. RR )' % AX)
cx0 = w.s([zred, z1, z0c, esub, me0], 'cxplead', '( %s -> ( %s ^c 0 ) <_ %s )' % (AX, ZS, XE))
zcn = w.s([zcl], 'nn0cnd', '( %s -> %s e. CC )' % (AX, ZS))
cx0e = w.s([zcn, w.inst('cxp0')], 'syl', '( %s -> ( %s ^c 0 ) = 1 )' % (AX, ZS))
xe1 = w.s([cx0e, cx0], 'eqbrtrrd', '( %s -> 1 <_ %s )' % (AX, XE))
xe0 = letr('0', '1', XE, zero, one, xer, le01, xe1)
yv = w.s([cr, n0, er, w.inst('yscaleeval')], 'syl3anc', '( %s -> %s = ( Nceil ` %s ) )' % (AX, YEV, XE))
ycl = w.s([cr, n3, er, w.inst('yscaleecl')], 'syl3anc', '( %s -> %s e. NN0 )' % (AX, YEV))
yred = w.s([ycl], 'nn0red', '( %s -> %s e. RR )' % (AX, YEV))
yge = w.s([xer, w.inst('nceilge')], 'syl', '( %s -> %s <_ ( Nceil ` %s ) )' % (AX, XE, XE))
ylo = w.s([yge, yv], 'breqtrrd', '( %s -> %s )' % (AX, G(NYLO)))
ynlt = w.s([xer, xe0, w.inst('nceillt')], 'syl2anc', '( %s -> ( Nceil ` %s ) < ( %s + 1 ) )' % (AX, XE, XE))
ylt = w.s([yv, ynlt], 'eqbrtrd', '( %s -> %s < ( %s + 1 ) )' % (AX, YEV, XE))
yhi = linarith(w, AX, [ylt, xe1], G(NYHI), leaves={XE: xer, YEV: yred})
# T
r3 = w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % AX)
tb = w.s([r3, l2r], 'remulcld', '( %s -> ( 3 x. %s ) e. RR )' % (AX, L2))
l20 = letr('0', '1', L2, zero, one, l2r, le01, l21)
z0i = w.s([], '0re', '0 e. RR'); r3i = w.s([], '3re', '3 e. RR'); p3 = w.s([], '3pos', '0 < 3')
le3 = w.s([z0i, r3i, p3], 'ltleii', '0 <_ 3'); le3d = w.s([le3], 'a1i', '( %s -> 0 <_ 3 )' % AX)
tb0 = w.s([r3, l2r, le3d, l20], 'mulge0d', '( %s -> 0 <_ ( 3 x. %s ) )' % (AX, L2))
tv = w.s([n0, w.inst('tscaleval')], 'syl', '( %s -> %s = ( Nceil ` ( 3 x. %s ) ) )' % (AX, TS, L2))
tcl = w.s([n2, w.inst('tscalecl')], 'syl', '( %s -> %s e. NN0 )' % (AX, TS))
tred = w.s([tcl], 'nn0red', '( %s -> %s e. RR )' % (AX, TS))
tge = w.s([tb, w.inst('nceilge')], 'syl', '( %s -> ( 3 x. %s ) <_ ( Nceil ` ( 3 x. %s ) ) )' % (AX, L2, L2))
tlo = w.s([tge, tv], 'breqtrrd', '( %s -> %s )' % (AX, G(NTLO)))
tnlt = w.s([tb, tb0, w.inst('nceillt')], 'syl2anc', '( %s -> ( Nceil ` ( 3 x. %s ) ) < ( ( 3 x. %s ) + 1 ) )' % (AX, L2, L2))
tlt = w.s([tv, tnlt], 'eqbrtrd', '( %s -> %s < ( ( 3 x. %s ) + 1 ) )' % (AX, TS, L2))
thi = linarith(w, AX, [tlt, l21], G(NTHI), leaves={L2: l2r, TS: tred})
# assemble
t1 = w.s([cr, er, n0], '3jca', '( %s -> ( C e. RR /\\ E e. RR /\\ N e. NN0 ) )' % AX)
t2 = w.s([zcl, wcl], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (AX, ZS, WF))
t3 = w.s([ycl, tcl], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (AX, YEV, TS))
ty = w.s([t1, t2, t3], '3jca', '( %s -> %s )' % (AX, G(TYPE3)))
bi = w.s([ty, w.inst('elinwin')], 'syl', '( %s -> ( %s <-> %s ) )' % (AX, G(REL), G(WIN)))
cj1 = w.s([zlo, zhi], 'jca', '( %s -> ( %s /\\ %s ) )' % (AX, G(NZLO), G(NZHI)))
cj2 = w.s([wlo, whi], 'jca', '( %s -> ( %s /\\ %s ) )' % (AX, G(NWLO), G(NWHI)))
cj3 = w.s([ylo, yhi], 'jca', '( %s -> ( %s /\\ %s ) )' % (AX, G(NYLO), G(NYHI)))
cj4 = w.s([tlo, thi], 'jca', '( %s -> ( %s /\\ %s ) )' % (AX, G(NTLO), G(NTHI)))
cl = w.s([cj1, cj2], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (AX, G(NZLO), G(NZHI), G(NWLO), G(NWHI)))
cq = w.s([cj3, cj4], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (AX, G(NYLO), G(NYHI), G(NTLO), G(NTHI)))
cw = w.s([cl, cq], 'jca', '( %s -> %s )' % (AX, G(WIN)))
w.qed([cw, bi], 'mpbird', '( %s -> %s )' % (AX, G(REL)))
run(w)
