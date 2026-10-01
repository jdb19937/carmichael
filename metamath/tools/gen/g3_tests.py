"""Test theorems for the shared automation repaired by sortie G3.

    MM_DB=sorties/g3.mm python3 tools/gen/g3_tests.py            # all of them
    MM_DB=sorties/g3.mm python3 tools/gen/g3_tests.py g3t2 g3t3  # a subset
    MM_DB=sorties/g3.mm python3 tools/gen/g3_tests.py -msg       # the failure
                                                                 # message of
                                                                 # tools/cl.py

Each test exercises one repair of tools/lin.py, tools/cl.py, tools/congr.py or
tools/fsum.py; the worksheet is written to MM_WS and added to MM_DB by
tools/mm.py.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from cl import Closure, ClosureError
from lin import linarith, nlinarith, lineq
from fsum import FSum
import num

TESTS = []


def test(fn):
    TESTS.append(fn)
    return fn


def qedify(w, step):
    """rename the last step, which already proves the theorem, to qed"""
    assert w.lines[-1].startswith(step + ':'), w.lines[-1]
    w.lines[-1] = 'qed' + w.lines[-1][len(step):]
    return 'qed'


# ------------------------------------------------------------------ lin.py

@test
def g3t1():
    """degree three in nlinarith: the certificate needs the product of a
    hypothesis with a degree-two monomial (A4b's reproduction)"""
    K = num.nat_text(1000); T = num.nat_text(12)
    ante = ('( ( ( A e. RR /\\ B e. RR ) /\\ ( C e. RR /\\ Z e. RR ) ) /\\ '
            '( ( %s <_ C /\\ 1 <_ A ) /\\ ( %s <_ B /\\ ( ( C x. A ) x. B ) <_ Z ) ) )' % (K, T))
    w = W('g3t1', 'A bound on a triple product bounds the product of two of its factors: '
                  'the certificate of tools/lin.py needs the product of the three '
                  'hypotheses ` %s <_ C ` , ` 1 <_ A ` and ` %s <_ B ` , which is degree '
                  'three, and the pairwise products of the earlier round do not reach it.' % (K, T))
    a = w.s([], 'simplll', '( %s -> A e. RR )' % ante)
    b = w.s([], 'simpllr', '( %s -> B e. RR )' % ante)
    c = w.s([], 'simplrl', '( %s -> C e. RR )' % ante)
    z = w.s([], 'simplrr', '( %s -> Z e. RR )' % ante)
    h1 = w.s([], 'simprll', '( %s -> %s <_ C )' % (ante, K))
    h2 = w.s([], 'simprlr', '( %s -> 1 <_ A )' % ante)
    h3 = w.s([], 'simprrl', '( %s -> %s <_ B )' % (ante, T))
    h4 = w.s([], 'simprrr', '( %s -> ( ( C x. A ) x. B ) <_ Z )' % ante)
    cl = Closure(w, ante, {'A': ('RR', a), 'B': ('RR', b), 'C': ('RR', c), 'Z': ('RR', z)})
    nlinarith(w, ante, [h1, h2, h3, h4], '( A x. B ) <_ Z', closure=cl, name='qed')
    return w


@test
def g3t2():
    """a declared atom stops the decomposition (C2's reproduction): the
    closure is never asked for a subterm of the atom"""
    A = '( 1 + ( ( L + ( abs ` G ) ) / E ) )'
    ante = '( Z e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (A, A)
    w = W('g3t2', 'A compound term declared atomic: the linear arithmetic of '
                  'tools/lin.py stops its decomposition there, so tools/cl.py is never '
                  'asked for ` L ` , ` E ` or ` ( abs ` G ) ` , for which it has no rule.')
    z = w.s([], 'simpl', '( %s -> Z e. RR )' % ante)
    ar = w.s([], 'simprl', '( %s -> %s e. RR )' % (ante, A))
    a0 = w.s([], 'simprr', '( %s -> 0 <_ %s )' % (ante, A))
    cl = Closure(w, ante, {'Z': ('RR', z), A: [('RR', ar), ('ge0', a0)]})
    cl.atom(A)
    linarith(w, ante, [a0], 'Z <_ ( Z + %s )' % A, closure=cl, name='qed')
    return w


@test
def g3t3():
    """lineq: an equality between two linear real expressions"""
    ante = '( ( A e. RR /\\ B e. RR ) /\\ ( A + B ) = 4 )'
    w = W('g3t3', 'An equality goal for the linear arithmetic of tools/lin.py: the two '
                  'inequalities and ` letri3d ` .')
    a = w.s([], 'simpll', '( %s -> A e. RR )' % ante)
    b = w.s([], 'simplr', '( %s -> B e. RR )' % ante)
    h = w.s([], 'simpr', '( %s -> ( A + B ) = 4 )' % ante)
    cl = Closure(w, ante, {'A': ('RR', a), 'B': ('RR', b)})
    lineq(w, ante, '( 2 x. A )', '( 8 - ( 2 x. B ) )', hyps=[h], closure=cl, name='qed')
    return w


# ------------------------------------------------------------------- cl.py

@test
def g3t4():
    """1 <_ ( exp ` E ) for a nonnegative real exponent"""
    ante = '( E e. RR /\\ 0 <_ E )'
    w = W('g3t4', 'The route of tools/cl.py to ` 1 <_ ( exp ` E ) ` from ` 0 <_ E ` , '
                  'through ` efle ` at 0 and ` ef0 ` .')
    e = w.s([], 'simpl', '( %s -> E e. RR )' % ante)
    e0 = w.s([], 'simpr', '( %s -> 0 <_ E )' % ante)
    cl = Closure(w, ante, {'E': [('RR', e), ('ge0', e0)]})
    st = cl.prove('( exp ` E )', 'ge1')
    return qedify(w, st) and w


# ---------------------------------------------------------------- congr.py

@test
def g3t5():
    """congruence inside a product, range and body both changed
    (prodeq12dv, whose body hypothesis is under the extended antecedent)"""
    R = '( <" P "> ++ W )'
    ante = 'f = %s' % R
    w = W('g3t5', 'A congruence reaching inside a finite product: tools/congr.py lifts '
                  'the body hypothesis of ` prodeq12dv ` to the extended antecedent '
                  '` ( ph /\\ i e. A ) ` with ` adantr ` .')
    idst = w.s([], 'id', '( %s -> f = %s )' % (ante, R))
    st, new = w.congr('prod_ i e. ( 0 ..^ ( # ` f ) ) ( f ` i )', {'f': R}, ante, {'f': idst})
    assert new == 'prod_ i e. ( 0 ..^ ( # ` %s ) ) ( %s ` i )' % (R, R), new
    return qedify(w, st) and w


@test
def g3t6():
    """a body-only change inside a sum and inside a product: the `s`
    variants, whose hypothesis is under the plain antecedent"""
    ante = 'f = C'
    w = W('g3t6', 'A congruence reaching the body of a finite sum and of a finite '
                  'product: tools/congr.py cites the ` s ` variants ` sumeq2sdv ` and '
                  '` prodeq2sdv ` , whose hypothesis is under the plain antecedent.')
    idst = w.s([], 'id', '( %s -> f = C )' % ante)
    s1, n1 = w.congr('sum_ k e. ( 1 ... N ) ( f x. k )', {'f': 'C'}, ante, {'f': idst})
    s2, n2 = w.congr('prod_ k e. ( 1 ... N ) ( f + k )', {'f': 'C'}, ante, {'f': idst})
    w.qed([s1, s2], 'jca', '( %s -> ( sum_ k e. ( 1 ... N ) ( f x. k ) = %s /\\ '
                           'prod_ k e. ( 1 ... N ) ( f + k ) = %s ) )' % (ante, n1, n2))
    return w


@test
def g3t7():
    """a substitution changing the range and the body of a sum, which has
    no `s` variant (V2c's reproduction)"""
    ante = 'f = N'
    w = W('g3t7', 'A substitution that changes both the range and the body of a finite '
                  'sum: ` sumeq12dv ` has no ` s ` variant, so tools/congr.py lifts its '
                  'body hypothesis with ` adantr ` .')
    idst = w.s([], 'id', '( %s -> f = N )' % ante)
    st, new = w.congr('sum_ j e. ( 1 ... f ) ( j x. f )', {'f': 'N'}, ante, {'f': idst})
    assert new == 'sum_ j e. ( 1 ... N ) ( j x. N )', new
    return qedify(w, st) and w


@test
def g3t8():
    """the bound variable of the product occurs in the antecedent: the
    congruence goes through the closed antecedent ( f = G ) and one syl"""
    ante = '( A. i e. NN 1 <_ i /\\ f = G )'
    w = W('g3t8', 'A congruence inside a finite product whose bound variable occurs in '
                  'the antecedent: every set.mm product congruence has a ` $d ` that '
                  'forbids it, so tools/congr.py proves the congruence under the closed '
                  'antecedent ` ( f = G ) ` and carries it back with one ` syl ` .')
    eq = w.s([], 'simpr', '( %s -> f = G )' % ante)
    st, new = w.congr('prod_ i e. ( 0 ..^ ( # ` f ) ) ( f ` i )', {'f': 'G'}, ante, {'f': eq})
    assert new == 'prod_ i e. ( 0 ..^ ( # ` G ) ) ( G ` i )', new
    return qedify(w, st) and w


# ----------------------------------------------------------------- fsum.py

@test
def g3t9():
    """fsum body closures from plain step names: one body fact proved by
    hand under the body's own antecedent, one proved above it and lifted"""
    ante = '( ( N e. NN /\\ C e. CC ) /\\ F : ( 1 ... N ) --> CC )'
    ante2 = '( %s /\\ k e. ( 1 ... N ) )' % ante
    w = W('g3t9', 'A finite sum whose body tools/cl.py has no rule for: the body '
                  'closures are handed to tools/fsum.py as plain worksheet step names, '
                  'one already under the body antecedent and one under the antecedent '
                  'above it, which the module lifts with ` adantr ` .')
    n = w.s([], 'simpll', '( %s -> N e. NN )' % ante)
    cst = w.s([], 'simplr', '( %s -> C e. CC )' % ante)
    fst = w.s([], 'simpr', '( %s -> F : ( 1 ... N ) --> CC )' % ante)
    cl = Closure(w, ante, {'N': ('NN', n), 'C': ('CC', cst)})
    f = FSum(w, cl)
    fl = w.s([fst], 'adantr', '( %s -> F : ( 1 ... N ) --> CC )' % ante2)
    el = w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % ante2)
    bst = w.s([fl, el, w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( F ` k ) e. CC )' % ante2)
    f.add('k', '( 1 ... N )', '( F ` k )', 'C', body=[bst, cst], name='qed')
    return w


@test
def g3t10():
    """fsumshft: an index shift, with the substituted body from congr.py"""
    ante = '( ( M e. ZZ /\\ N e. ZZ ) /\\ K e. ZZ )'
    w = W('g3t10', 'An index shift of a finite sum through tools/fsum.py: the module '
                   'writes the three integer closures, the body closure and the '
                   'substitution hypothesis ` ( j = ( k - K ) -> A = B ) ` .')
    m = w.s([], 'simpll', '( %s -> M e. ZZ )' % ante)
    n = w.s([], 'simplr', '( %s -> N e. ZZ )' % ante)
    k = w.s([], 'simpr', '( %s -> K e. ZZ )' % ante)
    cl = Closure(w, ante, {'M': ('ZZ', m), 'N': ('ZZ', n), 'K': ('ZZ', k)})
    FSum(w, cl).shft('j', 'M', 'N', 'K', '( j x. j )', 'k', name='qed')
    return w


@test
def g3t11():
    """fsumabs and fsumdivc"""
    ante = '( N e. NN /\\ C e. RR+ )'
    w = W('g3t11', 'The triangle inequality for a finite sum and division of one by a '
                   'constant, through tools/fsum.py.')
    n = w.s([], 'simpl', '( %s -> N e. NN )' % ante)
    c = w.s([], 'simpr', '( %s -> C e. RR+ )' % ante)
    cl = Closure(w, ante, {'N': ('NN', n), 'C': ('RR+', c)})
    f = FSum(w, cl)
    A = '( 1 ... N )'; B = '( 1 / k )'
    a = f.abs('k', A, B)
    d = f.divc('k', A, 'C', B)
    w.qed([a, d], 'jca', '( %s -> ( ( abs ` sum_ k e. %s %s ) <_ sum_ k e. %s ( abs ` %s ) '
                         '/\\ ( sum_ k e. %s %s / C ) = sum_ k e. %s ( %s / C ) ) )'
          % (ante, A, B, A, B, A, B, A, B))
    return w


@test
def g3t12():
    """fprodsplit over ( 1 ... ( N + 1 ) ) = ( ( 1 ... N ) u. { ( N + 1 ) } )"""
    ante = 'N e. NN'
    w = W('g3t12', 'A finite product split at its last index, through tools/fsum.py.')
    n = w.s([], 'id', '( %s -> N e. NN )' % ante)
    cl = Closure(w, ante, {'N': ('NN', n)})
    d0 = w.s([], 'fzp1disj', '( ( 1 ... N ) i^i { ( N + 1 ) } ) = (/)')
    disj = w.s([d0], 'a1i', '( %s -> ( ( 1 ... N ) i^i { ( N + 1 ) } ) = (/) )' % ante)
    uz = w.s([n, w.inst('elnnuz')], 'sylib', '( %s -> N e. ( ZZ>= ` 1 ) )' % ante)
    union = w.s([uz, w.inst('fzsuc')], 'syl',
                '( %s -> ( 1 ... ( N + 1 ) ) = ( ( 1 ... N ) u. { ( N + 1 ) } ) )' % ante)
    FSum(w, cl).prodsplit('k', '( 1 ... ( N + 1 ) )', '( 1 ... N )', '{ ( N + 1 ) }',
                          'k', disj, union, name='qed')
    return w


# ------------------------------------------ the failure message of cl.py

def msg():
    """print the ClosureError of A4b's reproduction: the missing fact is the
    positivity of Z, not the membership the last rule happened to try"""
    ante = 'Z e. RR'
    w = W('g3msg', 'not a theorem')
    z = w.s([], 'id', '( %s -> Z e. RR )' % ante)
    cl = Closure(w, ante, {'Z': ('RR', z)})
    try:
        cl.mem('( log ` Z )', 'RR')
        print('FAIL g3msg: no ClosureError')
        return False
    except ClosureError as e:
        print(e)
        ok = '0 < Z' in [f.strip() for f in e.wanted]
        print(('OK   ' if ok else 'FAIL ') + 'g3msg: the message names 0 < Z')
        return ok


def main():
    args = sys.argv[1:]
    if '-msg' in args:
        return msg()
    want = [a for a in args if not a.startswith('-')]
    ok = True
    for fn in TESTS:
        if want and fn.__name__ not in want:
            continue
        w = fn()
        ok = w.run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
