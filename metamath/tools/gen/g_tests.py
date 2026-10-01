"""Sortie G: tests of tools/lin.py (linarith) and tools/cl.py (closure and sign
discharge).  Every theorem here is generated; label arguments rerun a subset."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
from lin import linarith
from cl import Closure
from fsum import FSum
only = sys.argv[1:]
results = []


def run(w):
    if only and w.label not in only:
        return True
    ok = w.run()
    results.append((w.label, ok))
    return ok


def prem3(w, A, f1, f2, f3):
    """the three conjuncts of a triple-conjunction antecedent"""
    return (w.s([], 'simp1', '( %s -> %s )' % (A, f1)),
            w.s([], 'simp2', '( %s -> %s )' % (A, f2)),
            w.s([], 'simp3', '( %s -> %s )' % (A, f3)))


# ---- gtest1: two hypotheses, integer multipliers
w = W('gtest1', 'linarith test: a two-hypothesis linear goal with integer multipliers.')
A = '( A e. RR /\\ B e. RR /\\ ( A <_ B /\\ 0 <_ A ) )'
ra, rb, h = prem3(w, A, 'A e. RR', 'B e. RR', '( A <_ B /\\ 0 <_ A )')
h1 = w.s([h], 'simpld', '( %s -> A <_ B )' % A); h2 = w.s([h], 'simprd', '( %s -> 0 <_ A )' % A)
linarith(w, A, [h1, h2], '( 2 x. A ) <_ ( A + B )', leaves={'A': ra, 'B': rb}, name='qed'); run(w)

# ---- gtest2: strict goal from a strict hypothesis
w = W('gtest2', 'linarith test: a strict goal from a strict hypothesis.')
A = '( A e. RR /\\ B e. RR /\\ ( A < B /\\ 0 <_ A ) )'
ra, rb, h = prem3(w, A, 'A e. RR', 'B e. RR', '( A < B /\\ 0 <_ A )')
h1 = w.s([h], 'simpld', '( %s -> A < B )' % A); h2 = w.s([h], 'simprd', '( %s -> 0 <_ A )' % A)
linarith(w, A, [h1, h2], '( 2 x. A ) < ( A + B )', leaves={'A': ra, 'B': rb}, name='qed'); run(w)

# ---- gtest3: three hypotheses, multipliers 1/2
w = W('gtest3', 'linarith test: three hypotheses with the non-integer multiplier 1/2 each.')
A = '( ( A e. RR /\\ B e. RR /\\ C e. RR ) /\\ ( ( 2 x. A ) <_ ( B + C ) /\\ ( 2 x. B ) <_ ( A + C ) /\\ 0 <_ C ) )'
l = w.s([], 'simpl', '( %s -> ( A e. RR /\\ B e. RR /\\ C e. RR ) )' % A)
r = w.s([], 'simpr', '( %s -> ( ( 2 x. A ) <_ ( B + C ) /\\ ( 2 x. B ) <_ ( A + C ) /\\ 0 <_ C ) )' % A)
ra = w.s([l], 'simp1d', '( %s -> A e. RR )' % A); rb = w.s([l], 'simp2d', '( %s -> B e. RR )' % A); rc = w.s([l], 'simp3d', '( %s -> C e. RR )' % A)
h1 = w.s([r], 'simp1d', '( %s -> ( 2 x. A ) <_ ( B + C ) )' % A); h2 = w.s([r], 'simp2d', '( %s -> ( 2 x. B ) <_ ( A + C ) )' % A); h3 = w.s([r], 'simp3d', '( %s -> 0 <_ C )' % A)
linarith(w, A, [h1, h2, h3], '( ( A + B ) / 2 ) <_ ( ( 3 x. C ) / 2 )', leaves={'A': ra, 'B': rb, 'C': rc}, name='qed'); run(w)

# ---- gtest4: an atom that is a function value, closure from cl.py
w = W('gtest4', 'linarith test: the atom ( log ` N ) with its real closure supplied by the closure module.')
A = '( N e. NN /\\ X e. RR /\\ ( 2 x. ( log ` N ) ) <_ X )'
n, x, h = prem3(w, A, 'N e. NN', 'X e. RR', '( 2 x. ( log ` N ) ) <_ X')
linarith(w, A, [h], '( log ` N ) <_ ( ( X + 1 ) / 2 )', leaves={'N': n, 'X': x}, name='qed'); run(w)

# ---- gtest5: a numeric constant fact
w = W('gtest5', 'linarith test: a numeric constant fact (2 <_ A gives 1 < A).')
A = '( A e. RR /\\ 2 <_ A )'
ra = w.s([], 'simpl', '( %s -> A e. RR )' % A); h = w.s([], 'simpr', '( %s -> 2 <_ A )' % A)
linarith(w, A, [h], '1 < A', leaves={'A': ra}, name='qed'); run(w)

# ---- gtest6: closure of ( ( N ^ 2 ) x. ( log ` N ) ) in RR
w = W('gtest6', 'closure test: ( ( N ^ 2 ) x. ( log ` N ) ) is real for N e. NN.')
A = 'N e. NN'
c = Closure(w, A, {'N': ('NN', w.s([], 'id', '( %s -> N e. NN )' % A))})
st = c.mem('( ( N ^ 2 ) x. ( log ` N ) )', 'RR')
w.qed([st], 'idi', '( %s -> ( ( N ^ 2 ) x. ( log ` N ) ) e. RR )' % A); run(w)

# ---- gtest7: closure of ( ( |_ ` ( 2 logb N ) ) + 1 ) in NN0
w = W('gtest7', 'closure test: ( ( |_ ` ( 2 logb N ) ) + 1 ) is a nonnegative integer for N e. NN.')
A = 'N e. NN'
c = Closure(w, A, {'N': ('NN', w.s([], 'id', '( %s -> N e. NN )' % A))})
st = c.mem('( ( |_ ` ( 2 logb N ) ) + 1 )', 'NN0')
w.qed([st], 'idi', '( %s -> ( ( |_ ` ( 2 logb N ) ) + 1 ) e. NN0 )' % A); run(w)

# ---- gtest8: ( exp ` X ) e. RR+
w = W('gtest8', 'closure test: ( exp ` X ) is a positive real for X e. RR.')
A = 'X e. RR'
c = Closure(w, A, {'X': ('RR', w.s([], 'id', '( %s -> X e. RR )' % A))})
st = c.mem('( exp ` X )', 'RR+')
w.qed([st], 'idi', '( %s -> ( exp ` X ) e. RR+ )' % A); run(w)

# ---- gtest9: positivity of ( ( exp ` X ) x. ( N + 1 ) )
w = W('gtest9', 'sign test: ( ( exp ` X ) x. ( N + 1 ) ) is positive for X e. RR and N e. NN0.')
A = '( X e. RR /\\ N e. NN0 )'
c = Closure(w, A, {'X': ('RR', w.s([], 'simpl', '( %s -> X e. RR )' % A)), 'N': ('NN0', w.s([], 'simpr', '( %s -> N e. NN0 )' % A))})
st = c.gt0('( ( exp ` X ) x. ( N + 1 ) )')
w.qed([st], 'idi', '( %s -> 0 < ( ( exp ` X ) x. ( N + 1 ) ) )' % A); run(w)

# ---- gtest10: a finite sum
w = W('gtest10', 'closure test: the harmonic sum sum_ k e. ( 1 ... N ) ( 1 / k ) is real for N e. NN.')
A = 'N e. NN'
c = Closure(w, A, {'N': ('NN', w.s([], 'id', '( %s -> N e. NN )' % A))})
st = c.mem('sum_ k e. ( 1 ... N ) ( 1 / k )', 'RR')
w.qed([st], 'idi', '( %s -> sum_ k e. ( 1 ... N ) ( 1 / k ) e. RR )' % A); run(w)

# ---- gtest11: an equation among the hypotheses
w = W('gtest11', 'linarith test: an equation hypothesis A = ( 2 x. B ) used as an inequality.')
A = '( A e. RR /\\ B e. RR /\\ ( A = ( 2 x. B ) /\\ 0 <_ B ) )'
ra, rb, h = prem3(w, A, 'A e. RR', 'B e. RR', '( A = ( 2 x. B ) /\\ 0 <_ B )')
h1 = w.s([h], 'simpld', '( %s -> A = ( 2 x. B ) )' % A); h2 = w.s([h], 'simprd', '( %s -> 0 <_ B )' % A)
linarith(w, A, [h1, h2], 'B <_ A', leaves={'A': ra, 'B': rb}, name='qed'); run(w)

# ---- gtest12: subtraction and negation
w = W('gtest12', 'linarith test: subtraction and negation in hypotheses and goal.')
A = '( A e. RR /\\ B e. RR /\\ ( A - B ) <_ 1 )'
ra, rb, h = prem3(w, A, 'A e. RR', 'B e. RR', '( A - B ) <_ 1')
linarith(w, A, [h], '-u B <_ ( 1 - A )', leaves={'A': ra, 'B': rb}, name='qed'); run(w)

# ---- gtest13: decimal numerals
w = W('gtest13', 'linarith test: decimal numerals in hypotheses and goal (closed decimal arithmetic).')
A = '( A e. RR /\\ ; ; 1 2 3 <_ A )'
ra = w.s([], 'simpl', '( %s -> A e. RR )' % A); h = w.s([], 'simpr', '( %s -> ; ; 1 2 3 <_ A )' % A)
linarith(w, A, [h], '; ; 1 0 0 < ( A + ; 2 5 )', leaves={'A': ra}, name='qed'); run(w)

# ---- gtest14: right multiplication, division, fractional multiplier
w = W('gtest14', 'linarith test: ( A / 3 ) and ( A x. 2 ) with the fractional multiplier 5/3.')
A = '( A e. RR /\\ 0 <_ A )'
ra = w.s([], 'simpl', '( %s -> A e. RR )' % A); h = w.s([], 'simpr', '( %s -> 0 <_ A )' % A)
linarith(w, A, [h], '( A / 3 ) <_ ( A x. 2 )', leaves={'A': ra}, name='qed'); run(w)

# ---- gtest15..19: finite sums (tools/fsum.py)
def nnclosure(w):
    A = 'N e. NN'
    return A, Closure(w, A, {'N': ('NN', w.s([], 'id', '( %s -> N e. NN )' % A))})

w = W('gtest15', 'finite-sum test: fsumadd on ( k + 1 ) over ( 1 ... N ).')
A, c = nnclosure(w); FSum(w, c).add('k', '( 1 ... N )', 'k', '1', name='qed'); run(w)

w = W('gtest16', 'finite-sum test: fsumle with the termwise inequality k <_ ( 2 x. k ) proved by linarith under the child antecedent.')
A, c = nnclosure(w)
FSum(w, c).le('k', '( 1 ... N )', 'k', '( 2 x. k )', lambda ch: linarith(w, ch.ante, [ch.ge0('k')], 'k <_ ( 2 x. k )', closure=ch), name='qed'); run(w)

w = W('gtest17', 'finite-sum test: fsummulc2, a constant factor moved into the sum.')
A = '( N e. NN /\\ C e. CC )'
c = Closure(w, A, {'N': ('NN', w.s([], 'simpl', '( %s -> N e. NN )' % A)), 'C': ('CC', w.s([], 'simpr', '( %s -> C e. CC )' % A))})
FSum(w, c).mulc2('k', '( 1 ... N )', 'C', 'k', name='qed'); run(w)

w = W('gtest18', 'finite-sum test: fsump1, the last term split off with the substitution hypothesis generated by congr.py.')
A, c = nnclosure(w); FSum(w, c).p1('k', '1', 'N', '( k ^ 2 )', name='qed'); run(w)

w = W('gtest19', 'finite-sum test: fsumsplit over ( 1 ... ( N + 1 ) ) = ( 1 ... N ) u. { ( N + 1 ) } with fzsuc and fzp1disj.')
A, c = nnclosure(w)
d0 = w.s([], 'fzp1disj', '( ( 1 ... N ) i^i { ( N + 1 ) } ) = (/)'); disj = w.s([d0], 'a1i', '( %s -> ( ( 1 ... N ) i^i { ( N + 1 ) } ) = (/) )' % A)
i = w.inst('elnnuz'); uz = w.s([c.mem('N', 'NN'), i], 'sylib', '( %s -> N e. ( ZZ>= ` 1 ) )' % A)
union = w.s([uz, w.inst('fzsuc')], 'syl', '( %s -> ( 1 ... ( N + 1 ) ) = ( ( 1 ... N ) u. { ( N + 1 ) } ) )' % A)
FSum(w, c).split('k', '( 1 ... ( N + 1 ) )', '( 1 ... N )', '{ ( N + 1 ) }', 'k', disj, union, name='qed'); run(w)

print('\n'.join('%s %s' % ('OK  ' if ok else 'FAIL', l) for l, ok in results))
