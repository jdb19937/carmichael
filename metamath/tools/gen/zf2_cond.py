"""Sortie ZF2, batch 4: the conductor (Mathlib conductor, conductorSet):
value, membership in the conductor set, the conductor is a member and a
lower bound, the conductor of the trivial character, characters mod 1."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from zf2lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

HC = '( N e. NN /\\ X e. %s )' % DB('N')
C = COND('N', 'X')
CS = CSET('N', 'X')
def BODY(d, n, x): return '( %s || %s /\\ E. y e. %s %s = %s )' % (d, n, DB(d), x, IND(d, n, 'y'))
def CSX(n, x): return CSET(n, x)

# ---- dchrcondval
w = W('dchrcondval', 'Value of the conductor (Mathlib conductor): the infimum of the positive divisors d of N through which X factors, i.e. such that X is induced from a character mod d.')
n = w.s([], 'simpl', '( %s -> N e. NN )' % HC); x = w.s([], 'simpr', '( %s -> X e. %s )' % (HC, DB('N')))
d0 = w.s([], 'df-dchrcond', 'DChrCond = ( n e. NN , x e. %s |-> %s )' % (DB('n'), CONDBODY('n', 'x')))
d1 = w.s([d0], 'a1i', '( %s -> DChrCond = ( n e. NN , x e. %s |-> %s ) )' % (HC, DB('n'), CONDBODY('n', 'x')))
A2 = '( %s /\\ ( n = N /\\ x = X ) )' % HC
ln = w.s([], 'simprl', '( %s -> n = N )' % A2); lx = w.s([], 'simprr', '( %s -> x = X )' % A2)
c, new = w.wcongr(BODY('d', 'n', 'x'), {'n': 'N', 'x': 'X'}, A2, {'n': ln, 'x': lx})
assert new == BODY('d', 'N', 'X'), new
rb = w.s([c], 'rabbidv', '( %s -> %s = %s )' % (A2, CSX('n', 'x'), CS))
ie = w.s([rb], 'infeq1d', '( %s -> %s = inf ( %s , RR , < ) )' % (A2, CONDBODY('n', 'x'), CS))
ex = w.s([w.s([w.s([], 'ltso', '< Or RR')], 'infex', 'inf ( %s , RR , < ) e. _V' % CS)], 'a1i', '( %s -> inf ( %s , RR , < ) e. _V )' % (HC, CS))
A1 = '( %s /\\ n = N )' % HC
dom = w.s([w.s([w.s([], 'simpr', '( %s -> n = N )' % A1)], 'fveq2d', '( %s -> ( DChr ` n ) = ( DChr ` N ) )' % A1)], 'fveq2d', '( %s -> %s = %s )' % (A1, DB('n'), DB('N')))
w.qed([d1, ie, dom, n, x, ex], 'ovmpodx', '( %s -> %s = inf ( %s , RR , < ) )' % (HC, C, CS)); run(w)

# ---- dchrcondel: membership in the conductor set
w = W('dchrcondel', 'Membership in the conductor set of X (Mathlib mem_conductorSet_iff, FactorsThrough): a positive integer D dividing N such that X is induced from some character mod D.')
idx = w.s([], 'id', '( d = D -> d = D )')
c, new = w.wcongr(BODY('d', 'N', 'X'), {'d': 'D'}, 'd = D', {'d': idx})
assert new == BODY('D', 'N', 'X'), new
w.qed([c], 'elrab', '( D e. %s <-> ( D e. NN /\\ %s ) )' % (CS, BODY('D', 'N', 'X'))); run(w)

# ---- dchrcondn: the level is in the conductor set
w = W('dchrcondn', 'The level N belongs to the conductor set of X (Mathlib level_mem_conductorSet).')
n = w.s([], 'simpl', '( %s -> N e. NN )' % HC); x = w.s([], 'simpr', '( %s -> X e. %s )' % (HC, DB('N')))
dv = w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % HC), w.inst('iddvds')], 'syl', '( %s -> N || N )' % HC)
idv = w.s([n, x, w.inst('dchrindid')], 'syl2anc', '( %s -> %s = X )' % (HC, IND('N', 'N', 'X')))
idv2 = w.s([idv], 'eqcomd', '( %s -> X = %s )' % (HC, IND('N', 'N', 'X')))
sb = w.s([w.s([w.s([], 'fveq2', '( y = X -> %s = %s )' % (IND('N', 'N', 'y'), IND('N', 'N', 'X')))], 'eqeq2d', '( y = X -> ( X = %s <-> X = %s ) )' % (IND('N', 'N', 'y'), IND('N', 'N', 'X')))], 'rspcev', '( ( X e. %s /\\ X = %s ) -> E. y e. %s X = %s )' % (DB('N'), IND('N', 'N', 'X'), DB('N'), IND('N', 'N', 'y')))
ex = w.s([x, idv2, sb], 'syl2anc', '( %s -> E. y e. %s X = %s )' % (HC, DB('N'), IND('N', 'N', 'y')))
bo = w.s([n, w.s([dv, ex], 'jca', '( %s -> %s )' % (HC, BODY('N', 'N', 'X')))], 'jca', '( %s -> ( N e. NN /\\ %s ) )' % (HC, BODY('N', 'N', 'X')))
w.qed([bo, w.s([], 'dchrcondel', '( N e. %s <-> ( N e. NN /\\ %s ) )' % (CS, BODY('N', 'N', 'X')))], 'sylibr', '( %s -> N e. %s )' % (HC, CS)); run(w)

# ---- dchrcondcs: the conductor is in the conductor set
w = W('dchrcondcs', 'The conductor belongs to the conductor set (Mathlib conductor_mem_conductorSet): the infimum of a nonempty set of positive integers is attained.')
ss = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % CS), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'sseqtri', '%s C_ ( ZZ>= ` 1 )' % CS)], 'a1i', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (HC, CS))
ne = w.s([w.s([], 'dchrcondn', '( %s -> N e. %s )' % (HC, CS)), w.inst('ne0i')], 'syl', '( %s -> %s =/= (/) )' % (HC, CS))
ic = w.s([ss, ne, w.inst('infssuzcl')], 'syl2anc', '( %s -> inf ( %s , RR , < ) e. %s )' % (HC, CS, CS))
w.qed([w.s([], 'dchrcondval', '( %s -> %s = inf ( %s , RR , < ) )' % (HC, C, CS)), ic], 'eqeltrd', '( %s -> %s e. %s )' % (HC, C, CS)); run(w)

# ---- dchrcondcl and its three parts
w = W('dchrcondcl', 'The conductor is a positive integer dividing the level, and X is induced from a character mod the conductor (Mathlib conductor_ne_zero, conductor_dvd_level, factorsThrough_conductor).')
cs = w.s([], 'dchrcondcs', '( %s -> %s e. %s )' % (HC, C, CS))
el = w.s([cs, w.s([], 'dchrcondel', '( %s e. %s <-> ( %s e. NN /\\ %s ) )' % (C, CS, C, BODY(C, 'N', 'X')))], 'sylib', '( %s -> ( %s e. NN /\\ %s ) )' % (HC, C, BODY(C, 'N', 'X')))
w.qed([el, w.s([], '3anass', '( ( %s e. NN /\\ %s || N /\\ E. y e. %s X = %s ) <-> ( %s e. NN /\\ %s ) )' % (C, C, DB(C), IND(C, 'N', 'y'), C, BODY(C, 'N', 'X')))], 'sylibr', '( %s -> ( %s e. NN /\\ %s || N /\\ E. y e. %s X = %s ) )' % (HC, C, C, DB(C), IND(C, 'N', 'y'))); run(w)
TRI = '( %s e. NN /\\ %s || N /\\ E. y e. %s X = %s )' % (C, C, DB(C), IND(C, 'N', 'y'))
w = W('dchrcondnn', 'The conductor is a positive integer (Mathlib conductor_ne_zero).')
w.qed([w.s([], 'dchrcondcl', '( %s -> %s )' % (HC, TRI))], 'simp1d', '( %s -> %s e. NN )' % (HC, C)); run(w)
w = W('dchrconddvdn', 'The conductor divides the level (Mathlib conductor_dvd_level).')
w.qed([w.s([], 'dchrcondcl', '( %s -> %s )' % (HC, TRI))], 'simp2d', '( %s -> %s || N )' % (HC, C)); run(w)
w = W('dchrcondex', 'X is induced from some character mod its conductor (Mathlib factorsThrough_conductor).')
w.qed([w.s([], 'dchrcondcl', '( %s -> %s )' % (HC, TRI))], 'simp3d', '( %s -> E. y e. %s X = %s )' % (HC, DB(C), IND(C, 'N', 'y'))); run(w)

# ---- dchrcondle: the conductor is a lower bound of the conductor set
HL = '( %s /\\ D e. %s )' % (HC, CS)
w = W('dchrcondle', 'The conductor is at most every member of the conductor set (Mathlib Nat.sInf_le).')
ss = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % CS), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'sseqtri', '%s C_ ( ZZ>= ` 1 )' % CS)], 'a1i', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (HL, CS))
le = w.s([ss, w.s([], 'simpr', '( %s -> D e. %s )' % (HL, CS)), w.inst('infssuzle')], 'syl2anc', '( %s -> inf ( %s , RR , < ) <_ D )' % (HL, CS))
w.qed([w.s([w.s([], 'dchrcondval', '( %s -> %s = inf ( %s , RR , < ) )' % (HC, C, CS))], 'adantr', '( %s -> %s = inf ( %s , RR , < ) )' % (HL, C, CS)), le], 'eqbrtrd', '( %s -> %s <_ D )' % (HL, C)); run(w)

# ---- dchrcond1: the conductor of the trivial character is 1
ONE1 = ONE('1'); C1 = COND('N', ONE('N')); CS1 = CSET('N', ONE('N'))
w = W('dchrcond1', 'The conductor of the trivial character is 1 (Mathlib conductor_one): the trivial character is induced from the (trivial) character mod 1.')
def one_cl(w, ante, nn, lev):
    g = w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (lev, lev))
    ab = w.s([nn, w.s([g], 'dchrabl', '( %s e. NN -> ( DChr ` %s ) e. Abel )' % (lev, lev))], 'syl', '( %s -> ( DChr ` %s ) e. Abel )' % (ante, lev))
    gr = w.s([ab], 'ablgrpd', '( %s -> ( DChr ` %s ) e. Grp )' % (ante, lev))
    return w.s([gr, w.s([w.s([], 'eqid', '%s = %s' % (DB(lev), DB(lev))), w.s([], 'eqid', '%s = %s' % (ONE(lev), ONE(lev)))], 'grpidcl', '( ( DChr ` %s ) e. Grp -> %s e. %s )' % (lev, ONE(lev), DB(lev)))], 'syl', '( %s -> %s e. %s )' % (ante, ONE(lev), DB(lev)))
n = w.s([], 'id', '( N e. NN -> N e. NN )')
on = one_cl(w, 'N e. NN', n, 'N'); o1 = one_cl(w, 'N e. NN', w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( N e. NN -> 1 e. NN )'), '1')
hc = w.s([n, on], 'jca', '( N e. NN -> ( N e. NN /\\ %s e. %s ) )' % (ONE('N'), DB('N')))
d1 = w.s([w.s([n], 'nnzd', '( N e. NN -> N e. ZZ )'), w.inst('1dvds')], 'syl', '( N e. NN -> 1 || N )')
i1 = w.s([w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( N e. NN -> 1 e. NN )'), n, d1, w.inst('dchrind1')], 'syl3anc', '( N e. NN -> %s = %s )' % (IND('1', 'N', ONE1), ONE('N')))
i2 = w.s([i1], 'eqcomd', '( N e. NN -> %s = %s )' % (ONE('N'), IND('1', 'N', ONE1)))
sb = w.s([w.s([w.s([], 'fveq2', '( y = %s -> %s = %s )' % (ONE1, IND('1', 'N', 'y'), IND('1', 'N', ONE1)))], 'eqeq2d', '( y = %s -> ( %s = %s <-> %s = %s ) )' % (ONE1, ONE('N'), IND('1', 'N', 'y'), ONE('N'), IND('1', 'N', ONE1)))], 'rspcev', '( ( %s e. %s /\\ %s = %s ) -> E. y e. %s %s = %s )' % (ONE1, DB('1'), ONE('N'), IND('1', 'N', ONE1), DB('1'), ONE('N'), IND('1', 'N', 'y')))
ex = w.s([o1, i2, sb], 'syl2anc', '( N e. NN -> E. y e. %s %s = %s )' % (DB('1'), ONE('N'), IND('1', 'N', 'y')))
bo = w.s([w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( N e. NN -> 1 e. NN )'), w.s([d1, ex], 'jca', '( N e. NN -> %s )' % BODY('1', 'N', ONE('N')))], 'jca', '( N e. NN -> ( 1 e. NN /\\ %s ) )' % BODY('1', 'N', ONE('N')))
mem = w.s([bo, w.s([], 'dchrcondel', '( 1 e. %s <-> ( 1 e. NN /\\ %s ) )' % (CS1, BODY('1', 'N', ONE('N'))))], 'sylibr', '( N e. NN -> 1 e. %s )' % CS1)
le = w.s([hc, mem, w.inst('dchrcondle')], 'syl2anc' if False else 'sylanc', '( N e. NN -> %s <_ 1 )' % C1)
w.lines.pop()
le = w.s([w.s([hc, mem], 'jca', '( N e. NN -> ( ( N e. NN /\\ %s e. %s ) /\\ 1 e. %s ) )' % (ONE('N'), DB('N'), CS1)), w.inst('dchrcondle')], 'syl', '( N e. NN -> %s <_ 1 )' % C1)
cn = w.s([hc, w.inst('dchrcondnn')], 'syl', '( N e. NN -> %s e. NN )' % C1)
ge = w.s([cn], 'nnge1d', '( N e. NN -> 1 <_ %s )' % C1)
tri = w.s([w.s([cn], 'nnred', '( N e. NN -> %s e. RR )' % C1), w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( N e. NN -> 1 e. RR )'), w.inst('letri3')], 'syl2anc', '( N e. NN -> ( %s = 1 <-> ( %s <_ 1 /\\ 1 <_ %s ) ) )' % (C1, C1, C1))
w.qed([w.s([le, ge], 'jca', '( N e. NN -> ( %s <_ 1 /\\ 1 <_ %s ) )' % (C1, C1)), tri], 'mpbird', '( N e. NN -> %s = 1 )' % C1); run(w)

# ---- dchr1lev: every character mod 1 is trivial
w = W('dchr1lev', 'Every Dirichlet character mod 1 is the trivial character (Mathlib level_one).')
H1 = 'X e. %s' % DB('1')
one = w.s([], '1nn', '1 e. NN'); n = w.s([one], 'a1i', '( %s -> 1 e. NN )' % H1); x = w.s([], 'id', '( %s -> %s )' % (H1, H1))
g = w.s([], 'eqid', '( DChr ` 1 ) = ( DChr ` 1 )')
ab = w.s([one, w.s([g], 'dchrabl', '( 1 e. NN -> ( DChr ` 1 ) e. Abel )')], 'ax-mp', '( DChr ` 1 ) e. Abel')
gr = w.s([ab], 'ablgrp' if False else 'ablgrpi', '( DChr ` 1 ) e. Grp')
w.lines.pop()
gr = w.s([ab, w.s([], 'ablgrp', '( ( DChr ` 1 ) e. Abel -> ( DChr ` 1 ) e. Grp )')], 'ax-mp', '( DChr ` 1 ) e. Grp')
o1 = w.s([gr, w.s([w.s([], 'eqid', '%s = %s' % (DB('1'), DB('1'))), w.s([], 'eqid', '%s = %s' % (ONE1, ONE1))], 'grpidcl', '( ( DChr ` 1 ) e. Grp -> %s e. %s )' % (ONE1, DB('1')))], 'ax-mp', '%s e. %s' % (ONE1, DB('1')))
o1d = w.s([o1], 'a1i', '( %s -> %s e. %s )' % (H1, ONE1, DB('1')))
eq = w.s([n, x, o1d, w.inst('dchreqz')], 'syl3anc', '( %s -> ( X = %s <-> A. a e. ZZ ( %s -> %s = %s ) ) )' % (H1, ONE1, COP('a', '1'), EV('X', '1', 'a'), EV(ONE1, '1', 'a')))
A2 = '( %s /\\ a e. ZZ )' % H1
az = w.s([], 'simpr', '( %s -> a e. ZZ )' % A2); x2 = w.s([x], 'adantr', '( %s -> %s )' % (A2, H1))
z = w.s([], 'eqid', '( Z/nZ ` 1 ) = ( Z/nZ ` 1 )'); l = w.s([], 'eqid', '%s = %s' % (LZ('1'), LZ('1'))); u = w.s([], 'eqid', '%s = %s' % (UZ('1'), UZ('1'))); d = w.s([], 'eqid', '%s = %s' % (DB('1'), DB('1')))
oz = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A2)
dv1 = w.s([w.s([az, oz], 'zsubcld', '( %s -> ( a - 1 ) e. ZZ )' % A2), w.inst('1dvds')], 'syl', '( %s -> 1 || ( a - 1 ) )' % A2)
zd = w.s([w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % A2), az, oz, w.s([z, l], 'zndvds', '( ( 1 e. NN0 /\\ a e. ZZ /\\ 1 e. ZZ ) -> ( ( %s ` a ) = ( %s ` 1 ) <-> 1 || ( a - 1 ) ) )' % (LZ('1'), LZ('1')))], 'syl3anc', '( %s -> ( ( %s ` a ) = ( %s ` 1 ) <-> 1 || ( a - 1 ) ) )' % (A2, LZ('1'), LZ('1')))
la = w.s([dv1, zd], 'mpbird', '( %s -> ( %s ` a ) = ( %s ` 1 ) )' % (A2, LZ('1'), LZ('1')))
v1 = w.s([la], 'fveq2d', '( %s -> %s = %s )' % (A2, EV('X', '1', 'a'), EV('X', '1', '1')))
v2 = w.s([g, z, d, l, x2], 'dchrzrh1', '( %s -> %s = 1 )' % (A2, EV('X', '1', '1')))
v3 = w.s([la], 'fveq2d', '( %s -> %s = %s )' % (A2, EV(ONE1, '1', 'a'), EV(ONE1, '1', '1')))
v4 = w.s([g, z, d, l, w.s([o1], 'a1i', '( %s -> %s e. %s )' % (A2, ONE1, DB('1')))], 'dchrzrh1', '( %s -> %s = 1 )' % (A2, EV(ONE1, '1', '1')))
v5 = w.s([w.s([v1, v2], 'eqtrd', '( %s -> %s = 1 )' % (A2, EV('X', '1', 'a'))), w.s([v3, v4], 'eqtrd', '( %s -> %s = 1 )' % (A2, EV(ONE1, '1', 'a')))], 'eqtr4d', '( %s -> %s = %s )' % (A2, EV('X', '1', 'a'), EV(ONE1, '1', 'a')))
v6 = w.s([v5], 'a1d', '( %s -> ( %s -> %s = %s ) )' % (A2, COP('a', '1'), EV('X', '1', 'a'), EV(ONE1, '1', 'a')))
v7 = w.s([v6], 'ralrimiva', '( %s -> A. a e. ZZ ( %s -> %s = %s ) )' % (H1, COP('a', '1'), EV('X', '1', 'a'), EV(ONE1, '1', 'a')))
w.qed([v7, eq], 'mpbird', '( %s -> X = %s )' % (H1, ONE1)); run(w)

# ---- dchrcondeq1: X is trivial iff its conductor is 1
w = W('dchrcondeq1', 'A Dirichlet character is trivial iff its conductor is 1 (Mathlib eq_one_iff_conductor_eq_one).')
n = w.s([], 'simpl', '( %s -> N e. NN )' % HC); x = w.s([], 'simpr', '( %s -> X e. %s )' % (HC, DB('N')))
f1 = w.s([w.s([], 'oveq2', '( X = %s -> %s = %s )' % (ONE('N'), C, C1)), w.s([], 'dchrcond1', '( N e. NN -> %s = 1 )' % C1)], 'sylan9eqr', '( ( N e. NN /\\ X = %s ) -> %s = 1 )' % (ONE('N'), C))
f2 = w.s([f1], 'ex', '( N e. NN -> ( X = %s -> %s = 1 ) )' % (ONE('N'), C))
f3 = w.s([n, f2], 'syl', '( %s -> ( X = %s -> %s = 1 ) )' % (HC, ONE('N'), C))
A2 = '( %s /\\ %s = 1 )' % (HC, C)
c2 = w.s([], 'simpr', '( %s -> %s = 1 )' % (A2, C))
ex = w.s([w.s([], 'dchrcondex', '( %s -> E. y e. %s X = %s )' % (HC, DB(C), IND(C, 'N', 'y')))], 'adantr', '( %s -> E. y e. %s X = %s )' % (A2, DB(C), IND(C, 'N', 'y')))
e1 = w.s([w.s([c2], 'fveq2d', '( %s -> ( DChr ` %s ) = ( DChr ` 1 ) )' % (A2, C))], 'fveq2d', '( %s -> %s = %s )' % (A2, DB(C), DB('1')))
e2 = w.s([w.s([w.s([c2], 'oveq1d', '( %s -> %s = %s )' % (A2, INDOP(C, 'N'), INDOP('1', 'N')))], 'fveq1d', '( %s -> %s = %s )' % (A2, IND(C, 'N', 'y'), IND('1', 'N', 'y')))], 'eqeq2d', '( %s -> ( X = %s <-> X = %s ) )' % (A2, IND(C, 'N', 'y'), IND('1', 'N', 'y')))
e3 = w.s([e1, e2], 'rexeqbidv', '( %s -> ( E. y e. %s X = %s <-> E. y e. %s X = %s ) )' % (A2, DB(C), IND(C, 'N', 'y'), DB('1'), IND('1', 'N', 'y')))
ex2 = w.s([ex, e3], 'mpbid', '( %s -> E. y e. %s X = %s )' % (A2, DB('1'), IND('1', 'N', 'y')))
A3 = '( %s /\\ ( y e. %s /\\ X = %s ) )' % (A2, DB('1'), IND('1', 'N', 'y'))
y1 = w.s([w.s([], 'simprl', '( %s -> y e. %s )' % (A3, DB('1'))), w.inst('dchr1lev')], 'syl', '( %s -> y = %s )' % (A3, ONE1))
xe = w.s([], 'simprr', '( %s -> X = %s )' % (A3, IND('1', 'N', 'y')))
y2 = w.s([y1], 'fveq2d', '( %s -> %s = %s )' % (A3, IND('1', 'N', 'y'), IND('1', 'N', ONE1)))
n3 = w.s([n], 'ad2antrr', '( %s -> N e. NN )' % A3)
i1 = w.s([w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % A3), n3, w.s([w.s([n3], 'nnzd', '( %s -> N e. ZZ )' % A3), w.inst('1dvds')], 'syl', '( %s -> 1 || N )' % A3), w.inst('dchrind1')], 'syl3anc', '( %s -> %s = %s )' % (A3, IND('1', 'N', ONE1), ONE('N')))
x1 = w.s([xe, y2, i1], '3eqtrd', '( %s -> X = %s )' % (A3, ONE('N')))
b1 = w.s([ex2, x1], 'rexlimddv', '( %s -> X = %s )' % (A2, ONE('N')))
b2 = w.s([b1], 'ex', '( %s -> ( %s = 1 -> X = %s ) )' % (HC, C, ONE('N')))
w.qed([f3, b2], 'impbid', '( %s -> ( X = %s <-> %s = 1 ) )' % (HC, ONE('N'), C)); run(w)

# ---- dchrprimne1: a primitive character mod N >= 2 is nontrivial
HP = '( ( N e. NN /\\ 2 <_ N ) /\\ ( X e. %s /\\ %s = N ) )' % (DB('N'), C)
w = W('dchrprimne1', 'A primitive character of level at least 2 is nontrivial (Census prim_ne_one, KDerivDetect ne_one_of_isPrimitive).')
n = w.s([], 'simpll', '( %s -> N e. NN )' % HP); two = w.s([], 'simplr', '( %s -> 2 <_ N )' % HP); x = w.s([], 'simprl', '( %s -> X e. %s )' % (HP, DB('N'))); cn = w.s([], 'simprr', '( %s -> %s = N )' % (HP, C))
eq = w.s([n, x, w.inst('dchrcondeq1')], 'syl2anc', '( %s -> ( X = %s <-> %s = 1 ) )' % (HP, ONE('N'), C))
eq2 = w.s([cn], 'eqeq1d', '( %s -> ( %s = 1 <-> N = 1 ) )' % (HP, C))
eq3 = w.s([eq, eq2], 'bitrd', '( %s -> ( X = %s <-> N = 1 ) )' % (HP, ONE('N')))
lt = w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % HP), w.s([n], 'nnred', '( %s -> N e. RR )' % HP), w.s([w.s([], '1lt2', '1 < 2')], 'a1i', '( %s -> 1 < 2 )' % HP), two], 'ltletrd', '( %s -> 1 < N )' % HP)
w.lines.pop()
lt = w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % HP), w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % HP), w.s([n], 'nnred', '( %s -> N e. RR )' % HP), w.s([w.s([], '1lt2', '1 < 2')], 'a1i', '( %s -> 1 < 2 )' % HP), two], 'ltletrd', '( %s -> 1 < N )' % HP)
ne = w.s([lt], 'gtned', '( %s -> N =/= 1 )' % HP)
ne2 = w.s([ne], 'neneqd', '( %s -> -. N = 1 )' % HP)
nx = w.s([ne2, eq3], 'mtbird', '( %s -> -. X = %s )' % (HP, ONE('N')))
w.qed([nx], 'neqned', '( %s -> X =/= %s )' % (HP, ONE('N'))); run(w)
