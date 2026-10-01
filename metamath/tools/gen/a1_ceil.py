"""Sortie A1, batch 1: Nat.ceil and Nat.floor (Nceil, Nfloor): value, closure, the Mathlib bounds."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a1lib; from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

CB = lambda X: 'if ( %s <_ 0 , 0 , ( |^ ` %s ) )' % (X, X)
FB = lambda X: 'if ( %s < 0 , 0 , ( |_ ` %s ) )' % (X, X)
NC = lambda X: '( Nceil ` %s )' % X
NF = lambda X: '( Nfloor ` %s )' % X
A = 'X e. RR'

def valthm(label, desc, df, name, BODY, fvname):
    w = W(label, desc)
    l1 = w.s([], 'id', '( x = X -> x = X )')
    c, bX = w.congr(BODY('x'), {'x': 'X'}, 'x = X', {'x': l1}); assert bX == BODY('X'), bX
    d = w.s([], df, '%s = ( x e. RR |-> %s )' % (name, BODY('x')))
    e0 = w.s([], 'c0ex', '0 e. _V'); e1 = w.s([], 'fvex', '( %s ` X ) e. _V' % fvname)
    ex = w.s([e0, e1], 'ifex', '%s e. _V' % BODY('X'))
    w.qed([c, d, ex], 'fvmpt', '( X e. RR -> ( %s ` X ) = %s )' % (name, BODY('X'))); run(w)

valthm('nceilval', "Value of Nceil (Mathlib's Nat.ceil): the integer ceiling for positive arguments, 0 otherwise.", 'df-nceil', 'Nceil', CB, '|^')
valthm('nfloorval', "Value of Nfloor (Mathlib's Nat.floor): the integer floor for nonnegative arguments, 0 otherwise.", 'df-nfloor', 'Nfloor', FB, '|_')

# ---- nceilcl
w = W('nceilcl', 'Closure of Nceil: a nonnegative integer (Lean: Nat.ceil a : Nat).')
A1 = '( X e. RR /\\ X <_ 0 )'; A2 = '( X e. RR /\\ -. X <_ 0 )'
v = w.s([], 'nceilval', '( %s -> %s = %s )' % (A, NC('X'), CB('X')))
s1 = w.s([], 'simpr', '( %s -> X <_ 0 )' % A1); i1 = w.s([s1], 'iftrued', '( %s -> %s = 0 )' % (A1, CB('X')))
z = w.s([], '0nn0', '0 e. NN0'); zd = w.s([z], 'a1i', '( %s -> 0 e. NN0 )' % A1)
c1 = w.s([i1, zd], 'eqeltrd', '( %s -> %s e. NN0 )' % (A1, CB('X')))
s2 = w.s([], 'simpr', '( %s -> -. X <_ 0 )' % A2); i2 = w.s([s2], 'iffalsed', '( %s -> %s = ( |^ ` X ) )' % (A2, CB('X')))
xr = w.s([], 'simpl', '( %s -> X e. RR )' % A2)
cz = w.s([xr, w.inst('ceilcl')], 'syl', '( %s -> ( |^ ` X ) e. ZZ )' % A2)
z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A2)
ln = w.s([z0, xr, w.inst('ltnle')], 'syl2anc', '( %s -> ( 0 < X <-> -. X <_ 0 ) )' % A2)
gt = w.s([s2, ln], 'mpbird', '( %s -> 0 < X )' % A2); ge = w.s([gt], 'ltled', '( %s -> 0 <_ X )' % A2)
cg = w.s([xr, w.inst('ceilge')], 'syl', '( %s -> X <_ ( |^ ` X ) )' % A2)
czr = w.s([cz], 'zred', '( %s -> ( |^ ` X ) e. RR )' % A2)
le = w.s([z0, xr, czr, ge, cg], 'letrd', '( %s -> 0 <_ ( |^ ` X ) )' % A2)
j = w.s([cz, le], 'jca', '( %s -> ( ( |^ ` X ) e. ZZ /\\ 0 <_ ( |^ ` X ) ) )' % A2)
n0 = w.s([j, w.inst('elnn0z')], 'sylibr', '( %s -> ( |^ ` X ) e. NN0 )' % A2)
c2 = w.s([i2, n0], 'eqeltrd', '( %s -> %s e. NN0 )' % (A2, CB('X')))
pm = w.s([c1, c2], 'pm2.61dan', '( %s -> %s e. NN0 )' % (A, CB('X')))
w.qed([v, pm], 'eqeltrd', '( %s -> %s e. NN0 )' % (A, NC('X'))); run(w)

# ---- nceilge
w = W('nceilge', 'A real number is at most its natural ceiling (Lean: Nat.le_ceil).')
v = w.s([], 'nceilval', '( %s -> %s = %s )' % (A, NC('X'), CB('X')))
s1 = w.s([], 'simpr', '( %s -> X <_ 0 )' % A1); i1 = w.s([s1], 'iftrued', '( %s -> %s = 0 )' % (A1, CB('X')))
c1 = w.s([s1, i1], 'breqtrrd', '( %s -> X <_ %s )' % (A1, CB('X')))
s2 = w.s([], 'simpr', '( %s -> -. X <_ 0 )' % A2); i2 = w.s([s2], 'iffalsed', '( %s -> %s = ( |^ ` X ) )' % (A2, CB('X')))
xr = w.s([], 'simpl', '( %s -> X e. RR )' % A2)
cg = w.s([xr, w.inst('ceilge')], 'syl', '( %s -> X <_ ( |^ ` X ) )' % A2)
c2 = w.s([cg, i2], 'breqtrrd', '( %s -> X <_ %s )' % (A2, CB('X')))
pm = w.s([c1, c2], 'pm2.61dan', '( %s -> X <_ %s )' % (A, CB('X')))
w.qed([pm, v], 'breqtrrd', '( %s -> X <_ %s )' % (A, NC('X'))); run(w)

# ---- nceillt
w = W('nceillt', 'The natural ceiling of a nonnegative real number is less than the number plus one (Lean: Nat.ceil_lt_add_one).')
B = '( X e. RR /\\ 0 <_ X )'; B1 = '( %s /\\ X <_ 0 )' % B; B2 = '( %s /\\ -. X <_ 0 )' % B
xr = w.s([], 'simpl', '( %s -> X e. RR )' % B)
v = w.s([xr, w.inst('nceilval')], 'syl', '( %s -> %s = %s )' % (B, NC('X'), CB('X')))
s1 = w.s([], 'simpr', '( %s -> X <_ 0 )' % B1); i1 = w.s([s1], 'iftrued', '( %s -> %s = 0 )' % (B1, CB('X')))
xr1 = w.s([], 'simpll', '( %s -> X e. RR )' % B1); ge1 = w.s([], 'simplr', '( %s -> 0 <_ X )' % B1)
z1 = w.s([], '0red', '( %s -> 0 e. RR )' % B1); p1 = w.s([xr1, w.inst('peano2re')], 'syl', '( %s -> ( X + 1 ) e. RR )' % B1)
lt1 = w.s([xr1, w.inst('ltp1')], 'syl', '( %s -> X < ( X + 1 ) )' % B1)
lt0 = w.s([z1, xr1, p1, ge1, lt1], 'lelttrd', '( %s -> 0 < ( X + 1 ) )' % B1)
c1 = w.s([i1, lt0], 'eqbrtrd', '( %s -> %s < ( X + 1 ) )' % (B1, CB('X')))
s2 = w.s([], 'simpr', '( %s -> -. X <_ 0 )' % B2); i2 = w.s([s2], 'iffalsed', '( %s -> %s = ( |^ ` X ) )' % (B2, CB('X')))
xr2 = w.s([], 'simpll', '( %s -> X e. RR )' % B2)
cm = w.s([xr2, w.inst('ceilm1lt')], 'syl', '( %s -> ( ( |^ ` X ) - 1 ) < X )' % B2)
cz = w.s([xr2, w.inst('ceilcl')], 'syl', '( %s -> ( |^ ` X ) e. ZZ )' % B2); czr = w.s([cz], 'zred', '( %s -> ( |^ ` X ) e. RR )' % B2)
one = w.s([], '1red', '( %s -> 1 e. RR )' % B2)
ls = w.s([czr, one, xr2, w.inst('ltsubadd')], 'syl3anc', '( %s -> ( ( ( |^ ` X ) - 1 ) < X <-> ( |^ ` X ) < ( X + 1 ) ) )' % B2)
lt2 = w.s([cm, ls], 'mpbid', '( %s -> ( |^ ` X ) < ( X + 1 ) )' % B2)
c2 = w.s([i2, lt2], 'eqbrtrd', '( %s -> %s < ( X + 1 ) )' % (B2, CB('X')))
pm = w.s([c1, c2], 'pm2.61dan', '( %s -> %s < ( X + 1 ) )' % (B, CB('X')))
w.qed([v, pm], 'eqbrtrd', '( %s -> %s < ( X + 1 ) )' % (B, NC('X'))); run(w)

# ---- nceilceil
w = W('nceilceil', 'For a nonnegative real number the natural ceiling is the integer ceiling (Lean: Nat.cast_ceil_eq_int_ceil).')
B = '( X e. RR /\\ 0 <_ X )'; B1 = '( %s /\\ X <_ 0 )' % B; B2 = '( %s /\\ -. X <_ 0 )' % B
xr = w.s([], 'simpl', '( %s -> X e. RR )' % B)
v = w.s([xr, w.inst('nceilval')], 'syl', '( %s -> %s = %s )' % (B, NC('X'), CB('X')))
s1 = w.s([], 'simpr', '( %s -> X <_ 0 )' % B1); i1 = w.s([s1], 'iftrued', '( %s -> %s = 0 )' % (B1, CB('X')))
xr1 = w.s([], 'simpll', '( %s -> X e. RR )' % B1); ge1 = w.s([], 'simplr', '( %s -> 0 <_ X )' % B1)
z1 = w.s([], '0red', '( %s -> 0 e. RR )' % B1)
j = w.s([s1, ge1], 'jca', '( %s -> ( X <_ 0 /\\ 0 <_ X ) )' % B1)
tri = w.s([xr1, z1, w.inst('letri3')], 'syl2anc', '( %s -> ( X = 0 <-> ( X <_ 0 /\\ 0 <_ X ) ) )' % B1)
e0 = w.s([j, tri], 'mpbird', '( %s -> X = 0 )' % B1)
f0 = w.s([e0], 'fveq2d', '( %s -> ( |^ ` X ) = ( |^ ` 0 ) )' % B1)
zz = w.s([], '0z', '0 e. ZZ'); ci = w.s([zz, w.inst('ceilid')], 'ax-mp', '( |^ ` 0 ) = 0'); cid = w.s([ci], 'a1i', '( %s -> ( |^ ` 0 ) = 0 )' % B1)
c0 = w.s([f0, cid], 'eqtrd', '( %s -> ( |^ ` X ) = 0 )' % B1)
c1 = w.s([i1, c0], 'eqtr4d', '( %s -> %s = ( |^ ` X ) )' % (B1, CB('X')))
s2 = w.s([], 'simpr', '( %s -> -. X <_ 0 )' % B2); c2 = w.s([s2], 'iffalsed', '( %s -> %s = ( |^ ` X ) )' % (B2, CB('X')))
pm = w.s([c1, c2], 'pm2.61dan', '( %s -> %s = ( |^ ` X ) )' % (B, CB('X')))
w.qed([v, pm], 'eqtrd', '( %s -> %s = ( |^ ` X ) )' % (B, NC('X'))); run(w)

# ---- nfloorcl
w = W('nfloorcl', 'Closure of Nfloor: a nonnegative integer (Lean: Nat.floor a : Nat).')
A1 = '( X e. RR /\\ X < 0 )'; A2 = '( X e. RR /\\ -. X < 0 )'
v = w.s([], 'nfloorval', '( %s -> %s = %s )' % (A, NF('X'), FB('X')))
s1 = w.s([], 'simpr', '( %s -> X < 0 )' % A1); i1 = w.s([s1], 'iftrued', '( %s -> %s = 0 )' % (A1, FB('X')))
z = w.s([], '0nn0', '0 e. NN0'); zd = w.s([z], 'a1i', '( %s -> 0 e. NN0 )' % A1)
c1 = w.s([i1, zd], 'eqeltrd', '( %s -> %s e. NN0 )' % (A1, FB('X')))
s2 = w.s([], 'simpr', '( %s -> -. X < 0 )' % A2); i2 = w.s([s2], 'iffalsed', '( %s -> %s = ( |_ ` X ) )' % (A2, FB('X')))
xr = w.s([], 'simpl', '( %s -> X e. RR )' % A2); z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A2)
ln = w.s([z0, xr, w.inst('lenlt')], 'syl2anc', '( %s -> ( 0 <_ X <-> -. X < 0 ) )' % A2)
ge = w.s([s2, ln], 'mpbird', '( %s -> 0 <_ X )' % A2)
n0 = w.s([xr, ge, w.inst('flge0nn0')], 'syl2anc', '( %s -> ( |_ ` X ) e. NN0 )' % A2)
c2 = w.s([i2, n0], 'eqeltrd', '( %s -> %s e. NN0 )' % (A2, FB('X')))
pm = w.s([c1, c2], 'pm2.61dan', '( %s -> %s e. NN0 )' % (A, FB('X')))
w.qed([v, pm], 'eqeltrd', '( %s -> %s e. NN0 )' % (A, NF('X'))); run(w)

# ---- nfloorfl, nfloorle
def nonneg_prefix(w, B):
    xr = w.s([], 'simpl', '( %s -> X e. RR )' % B); ge = w.s([], 'simpr', '( %s -> 0 <_ X )' % B)
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % B)
    ln = w.s([z0, xr, w.inst('lenlt')], 'syl2anc', '( %s -> ( 0 <_ X <-> -. X < 0 ) )' % B)
    nl = w.s([ge, ln], 'mpbid', '( %s -> -. X < 0 )' % B)
    v = w.s([xr, w.inst('nfloorval')], 'syl', '( %s -> %s = %s )' % (B, NF('X'), FB('X')))
    i2 = w.s([nl], 'iffalsed', '( %s -> %s = ( |_ ` X ) )' % (B, FB('X')))
    return xr, ge, v, i2

w = W('nfloorfl', 'For a nonnegative real number the natural floor is the integer floor (Lean: Nat.cast_floor_eq_int_floor).')
B = '( X e. RR /\\ 0 <_ X )'
xr, ge, v, i2 = nonneg_prefix(w, B)
w.qed([v, i2], 'eqtrd', '( %s -> %s = ( |_ ` X ) )' % (B, NF('X'))); run(w)

w = W('nfloorle', 'The natural floor of a nonnegative real number is at most the number (Lean: Nat.floor_le).')
B = '( X e. RR /\\ 0 <_ X )'
xr, ge, v, i2 = nonneg_prefix(w, B)
e = w.s([v, i2], 'eqtrd', '( %s -> %s = ( |_ ` X ) )' % (B, NF('X')))
fl = w.s([xr, w.inst('flle')], 'syl', '( %s -> ( |_ ` X ) <_ X )' % B)
w.qed([e, fl], 'eqbrtrd', '( %s -> %s <_ X )' % (B, NF('X'))); run(w)

# ---- nfloorlt
w = W('nfloorlt', 'A real number is less than its natural floor plus one (Lean: Nat.lt_floor_add_one).')
A1 = '( X e. RR /\\ X < 0 )'; A2 = '( X e. RR /\\ -. X < 0 )'
v = w.s([], 'nfloorval', '( %s -> %s = %s )' % (A, NF('X'), FB('X')))
s1 = w.s([], 'simpr', '( %s -> X < 0 )' % A1); i1 = w.s([s1], 'iftrued', '( %s -> %s = 0 )' % (A1, FB('X')))
xr1 = w.s([], 'simpl', '( %s -> X e. RR )' % A1); z1 = w.s([], '0red', '( %s -> 0 e. RR )' % A1); o1 = w.s([], '1red', '( %s -> 1 e. RR )' % A1)
l01 = w.s([], '0lt1', '0 < 1'); l01d = w.s([l01], 'a1i', '( %s -> 0 < 1 )' % A1)
lt1 = w.s([xr1, z1, o1, s1, l01d], 'lttrd', '( %s -> X < 1 )' % A1)
p1 = w.s([], '0p1e1', '( 0 + 1 ) = 1'); p1d = w.s([p1], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % A1)
lt1b = w.s([lt1, p1d], 'breqtrrd', '( %s -> X < ( 0 + 1 ) )' % A1)
o1e = w.s([i1], 'oveq1d', '( %s -> ( %s + 1 ) = ( 0 + 1 ) )' % (A1, FB('X')))
c1 = w.s([lt1b, o1e], 'breqtrrd', '( %s -> X < ( %s + 1 ) )' % (A1, FB('X')))
s2 = w.s([], 'simpr', '( %s -> -. X < 0 )' % A2); i2 = w.s([s2], 'iffalsed', '( %s -> %s = ( |_ ` X ) )' % (A2, FB('X')))
xr2 = w.s([], 'simpl', '( %s -> X e. RR )' % A2)
fl = w.s([xr2, w.inst('flltp1')], 'syl', '( %s -> X < ( ( |_ ` X ) + 1 ) )' % A2)
o2e = w.s([i2], 'oveq1d', '( %s -> ( %s + 1 ) = ( ( |_ ` X ) + 1 ) )' % (A2, FB('X')))
c2 = w.s([fl, o2e], 'breqtrrd', '( %s -> X < ( %s + 1 ) )' % (A2, FB('X')))
pm = w.s([c1, c2], 'pm2.61dan', '( %s -> X < ( %s + 1 ) )' % (A, FB('X')))
ve = w.s([v], 'oveq1d', '( %s -> ( %s + 1 ) = ( %s + 1 ) )' % (A, NF('X'), FB('X')))
w.qed([pm, ve], 'breqtrrd', '( %s -> X < ( %s + 1 ) )' % (A, NF('X'))); run(w)
