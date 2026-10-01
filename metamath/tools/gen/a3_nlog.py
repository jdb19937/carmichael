"""Sortie A3, batch 1: Nlog (Mathlib's Nat.log): value, closure and the two
characterising inequalities Nat.pow_log_le_self / Nat.lt_pow_succ_log_self."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a1lib; from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

LB = '( B logb N )'
FL = '( |_ ` %s )' % LB
IFB = 'if ( ( 2 <_ B /\\ 1 <_ N ) , %s , 0 )' % FL
NL = '( B Nlog N )'
P0 = '( B e. NN0 /\\ N e. NN0 )'
PU = '( B e. ( ZZ>= ` 2 ) /\\ N e. NN )'


def uzn(w, ante, bs=None, ns=None):
    """( ante -> B e. ( ZZ>= ` 2 ) ), ( ante -> N e. NN ) from NN0 memberships and the bounds"""
    b = w.s([], 'simpl' if bs is None else bs, '( %s -> B e. ( ZZ>= ` 2 ) )' % ante)
    n = w.s([], 'simpr' if ns is None else ns, '( %s -> N e. NN )' % ante)
    return b, n


def basics(w, ante, ub, nn):
    """closures for B e. ( ZZ>= ` 2 ), N e. NN: B e. RR+, N e. RR+, B =/= 1, ( B logb N ) e. RR"""
    bn = w.s([ub, w.inst('eluz2nn')], 'syl', '( %s -> B e. NN )' % ante)
    brp = w.s([bn], 'nnrpd', '( %s -> B e. RR+ )' % ante)
    nrp = w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % ante)
    b1 = w.s([ub, w.inst('eluz2gt1')], 'syl', '( %s -> 1 < B )' % ante)
    b1r = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % ante), b1], 'gtned', '( %s -> B =/= 1 )' % ante)
    lb = w.s([brp, nrp, b1r, w.inst('relogbcl')], 'syl3anc', '( %s -> %s e. RR )' % (ante, LB))
    n1 = w.s([nn], 'nnge1d', '( %s -> 1 <_ N )' % ante)
    ge0 = w.s([w.s([ub, nrp, w.inst('logbge0b')], 'syl2anc', '( %s -> ( 0 <_ %s <-> 1 <_ N ) )' % (ante, LB)), n1], 'mpbird', '( %s -> 0 <_ %s )' % (ante, LB))
    fl = w.s([lb, ge0, w.inst('flge0nn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ante, FL))
    return brp, nrp, b1r, lb, ge0, fl


# ------------------------------------------------------------- value
w = W('nlogval', 'Value of Nlog (Mathlib\'s Nat.log): the floor of the real logarithm to the base B for 2 <_ B and 1 <_ N, and 0 otherwise.')
A = '( ( b = B /\\ n = N ) '
s1 = w.s([], 'simpl', A + '-> b = B )')
s2 = w.s([], 'simpr', A + '-> n = N )')
c1 = w.s([s1], 'breq2d', A + '-> ( 2 <_ b <-> 2 <_ B ) )')
c2 = w.s([s2], 'breq2d', A + '-> ( 1 <_ n <-> 1 <_ N ) )')
c3 = w.s([c1, c2], 'anbi12d', A + '-> ( ( 2 <_ b /\\ 1 <_ n ) <-> ( 2 <_ B /\\ 1 <_ N ) ) )')
c4 = w.s([s1, s2], 'oveq12d', A + '-> ( b logb n ) = %s )' % LB)
c5 = w.s([c4], 'fveq2d', A + '-> ( |_ ` ( b logb n ) ) = %s )' % FL)
c6 = w.s([c3, c5], 'ifbieq1d', A + '-> if ( ( 2 <_ b /\\ 1 <_ n ) , ( |_ ` ( b logb n ) ) , 0 ) = %s )' % IFB)
d = w.s([], 'df-nlog', 'Nlog = ( b e. NN0 , n e. NN0 |-> if ( ( 2 <_ b /\\ 1 <_ n ) , ( |_ ` ( b logb n ) ) , 0 ) )')
ex = w.s([], 'ifex', '%s e. _V' % IFB)
w.qed([c6, d, ex], 'ovmpoa', '( %s -> %s = %s )' % (P0, NL, IFB))
run(w)

# ------------------------------------------------------------- closure
w = W('nlogcl', 'Closure of Nlog: a nonnegative integer (Lean: Nat.log b n : Nat).')
T = '( %s /\\ ( 2 <_ B /\\ 1 <_ N ) )' % P0
bz = w.s([w.s([], 'simpll', '( %s -> B e. NN0 )' % T)], 'nn0zd', '( %s -> B e. ZZ )' % T)
b2 = w.s([], 'simprl', '( %s -> 2 <_ B )' % T)
i2zd = w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % T)
ub = w.s([w.s([i2zd, bz, b2], '3jca', '( %s -> ( 2 e. ZZ /\\ B e. ZZ /\\ 2 <_ B ) )' % T), w.inst('eluz2')], 'sylibr', '( %s -> B e. ( ZZ>= ` 2 ) )' % T)
nz = w.s([w.s([], 'simplr', '( %s -> N e. NN0 )' % T)], 'nn0zd', '( %s -> N e. ZZ )' % T)
n1 = w.s([], 'simprr', '( %s -> 1 <_ N )' % T)
i1z = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % T)
nu1 = w.s([w.s([i1z, nz, n1], '3jca', '( %s -> ( 1 e. ZZ /\\ N e. ZZ /\\ 1 <_ N ) )' % T), w.inst('eluz2')], 'sylibr', '( %s -> N e. ( ZZ>= ` 1 ) )' % T)
nn = w.s([nu1, w.inst('elnnuz')], 'sylibr', '( %s -> N e. NN )' % T)
_, _, _, lb, ge0, fl = basics(w, T, ub, nn)
F = '( %s /\\ -. ( 2 <_ B /\\ 1 <_ N ) )' % P0
z0 = w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % F)
ic = w.s([fl, z0], 'ifclda', '( %s -> %s e. NN0 )' % (P0, IFB))
v = w.s([], 'nlogval', '( %s -> %s = %s )' % (P0, NL, IFB))
w.qed([v, ic], 'eqeltrd', '( %s -> %s e. NN0 )' % (P0, NL))
run(w)

# ------------------------------------------------------------- value for 2 <_ B, 1 <_ N
w = W('nlogvald', 'Value of Nlog in the main case: the floor of the logarithm to the base B.')
ub = w.s([], 'simpl', '( %s -> B e. ( ZZ>= ` 2 ) )' % PU)
nn = w.s([], 'simpr', '( %s -> N e. NN )' % PU)
b0 = w.s([w.s([ub, w.inst('eluz2nn')], 'syl', '( %s -> B e. NN )' % PU)], 'nnnn0d', '( %s -> B e. NN0 )' % PU)
n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % PU)
v = w.s([b0, n0, w.inst('nlogval')], 'syl2anc', '( %s -> %s = %s )' % (PU, NL, IFB))
b2 = w.s([ub, w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ B e. ZZ /\\ 2 <_ B ) )' % PU)
b2a = w.s([b2], 'simp3d', '( %s -> 2 <_ B )' % PU)
n1 = w.s([nn], 'nnge1d', '( %s -> 1 <_ N )' % PU)
tr = w.s([w.s([b2a, n1], 'jca', '( %s -> ( 2 <_ B /\\ 1 <_ N ) )' % PU)], 'iftrued', '( %s -> %s = %s )' % (PU, IFB, FL))
w.qed([v, tr], 'eqtrd', '( %s -> %s = %s )' % (PU, NL, FL))
run(w)

# ------------------------------------------------------------- B ^ ( B Nlog N ) <_ N
w = W('nlogle', 'B ^ ( B Nlog N ) <_ N (Lean: Nat.pow_log_le_self).')
ub, nn = uzn(w, PU)
brp, nrp, b1r, lb, ge0, fl = basics(w, PU, ub, nn)
flz = w.s([fl], 'nn0zd', '( %s -> %s e. ZZ )' % (PU, FL))
bfl = w.s([brp, flz, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( B ^ %s ) e. RR+ )' % (PU, FL))
eq = w.s([ub, flz, w.inst('nnlogbexp')], 'syl2anc', '( %s -> ( B logb ( B ^ %s ) ) = %s )' % (PU, FL, FL))
bi = w.s([ub, bfl, nrp, w.inst('logbleb')], 'syl3anc', '( %s -> ( ( B ^ %s ) <_ N <-> ( B logb ( B ^ %s ) ) <_ %s ) )' % (PU, FL, FL, LB))
fle = w.s([lb, w.inst('flle')], 'syl', '( %s -> %s <_ %s )' % (PU, FL, LB))
r = w.s([eq, fle], 'eqbrtrd', '( %s -> ( B logb ( B ^ %s ) ) <_ %s )' % (PU, FL, LB))
le = w.s([bi, r], 'mpbird', '( %s -> ( B ^ %s ) <_ N )' % (PU, FL))
v = w.s([], 'nlogvald', '( %s -> %s = %s )' % (PU, NL, FL))
w.qed([w.s([v], 'oveq2d', '( %s -> ( B ^ %s ) = ( B ^ %s ) )' % (PU, NL, FL)), le], 'eqbrtrd', '( %s -> ( B ^ %s ) <_ N )' % (PU, NL))
run(w)

# ------------------------------------------------------------- N < B ^ ( ( B Nlog N ) + 1 )
w = W('nloglt', 'N < B ^ ( ( B Nlog N ) + 1 ) (Lean: Nat.lt_pow_succ_log_self).')
ub, nn = uzn(w, PU)
brp, nrp, b1r, lb, ge0, fl = basics(w, PU, ub, nn)
F1 = '( %s + 1 )' % FL
f1z = w.s([w.s([fl], 'nn0zd', '( %s -> %s e. ZZ )' % (PU, FL)), w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % PU)], 'zaddcld', '( %s -> %s e. ZZ )' % (PU, F1))
bf1 = w.s([brp, f1z, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( B ^ %s ) e. RR+ )' % (PU, F1))
eq = w.s([ub, f1z, w.inst('nnlogbexp')], 'syl2anc', '( %s -> ( B logb ( B ^ %s ) ) = %s )' % (PU, F1, F1))
bi = w.s([ub, nrp, bf1, w.inst('logblt')], 'syl3anc', '( %s -> ( N < ( B ^ %s ) <-> %s < ( B logb ( B ^ %s ) ) ) )' % (PU, F1, LB, F1))
flt = w.s([lb, w.inst('flltp1')], 'syl', '( %s -> %s < %s )' % (PU, LB, F1))
r = w.s([flt, eq], 'breqtrrd', '( %s -> %s < ( B logb ( B ^ %s ) ) )' % (PU, LB, F1))
lt = w.s([bi, r], 'mpbird', '( %s -> N < ( B ^ %s ) )' % (PU, F1))
v = w.s([], 'nlogvald', '( %s -> %s = %s )' % (PU, NL, FL))
ve = w.s([w.s([v], 'oveq1d', '( %s -> ( %s + 1 ) = %s )' % (PU, NL, F1)), ], 'oveq2d', '( %s -> ( B ^ ( %s + 1 ) ) = ( B ^ %s ) )' % (PU, NL, F1))
w.qed([lt, ve], 'breqtrrd', '( %s -> N < ( B ^ ( %s + 1 ) ) )' % (PU, NL))
run(w)

# ------------------------------------------------------------- ( B ^ I ) <_ N -> I <_ ( B Nlog N )
w = W('nlogub', 'Nlog is the greatest exponent with B ^ I <_ N (Lean: Nat.le_log_iff_pow_le, the direction consumers use).')
PI = '( ( B e. ( ZZ>= ` 2 ) /\\ N e. NN ) /\\ ( I e. NN0 /\\ ( B ^ I ) <_ N ) )'
ub = w.s([], 'simpll', '( %s -> B e. ( ZZ>= ` 2 ) )' % PI)
nn = w.s([], 'simplr', '( %s -> N e. NN )' % PI)
brp, nrp, b1r, lb, ge0, fl = basics(w, PI, ub, nn)
iz = w.s([w.s([], 'simprl', '( %s -> I e. NN0 )' % PI)], 'nn0zd', '( %s -> I e. ZZ )' % PI)
bi0 = w.s([brp, iz, w.inst('rpexpcl')], 'syl2anc', '( %s -> ( B ^ I ) e. RR+ )' % PI)
hyp = w.s([], 'simprr', '( %s -> ( B ^ I ) <_ N )' % PI)
bi = w.s([ub, bi0, nrp, w.inst('logbleb')], 'syl3anc', '( %s -> ( ( B ^ I ) <_ N <-> ( B logb ( B ^ I ) ) <_ %s ) )' % (PI, LB))
r = w.s([bi, hyp], 'mpbid', '( %s -> ( B logb ( B ^ I ) ) <_ %s )' % (PI, LB))
eq = w.s([ub, iz, w.inst('nnlogbexp')], 'syl2anc', '( %s -> ( B logb ( B ^ I ) ) = I )' % PI)
r2 = w.s([r, eq], 'breqtrrd' if False else 'eqbrtrrd', '( %s -> I <_ %s )' % (PI, LB))
fg = w.s([lb, iz, w.inst('flge')], 'syl2anc', '( %s -> ( I <_ %s <-> I <_ %s ) )' % (PI, LB, FL))
le = w.s([fg, r2], 'mpbid', '( %s -> I <_ %s )' % (PI, FL))
v = w.s([w.s([], 'simpl', '( %s -> ( B e. ( ZZ>= ` 2 ) /\\ N e. NN ) )' % PI), w.inst('nlogvald')], 'syl', '( %s -> %s = %s )' % (PI, NL, FL))
w.qed([le, v], 'breqtrrd', '( %s -> I <_ %s )' % (PI, NL))
run(w)
