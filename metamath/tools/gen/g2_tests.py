"""Test theorems for the shared automation repaired by sortie G2.

    MM_DB=sorties/g2.mm python3 tools/gen/g2_tests.py            # all of them
    MM_DB=sorties/g2.mm python3 tools/gen/g2_tests.py g2t3 g2t4  # a subset

Each test exercises one addition to tools/lin.py, tools/cl.py, tools/num.py,
tools/fsum.py or tools/congr.py; the worksheet is written to MM_WS and added
to MM_DB by tools/mm.py.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from cl import Closure, lift
from lin import linarith, nlinarith
from fsum import FSum
import num

TESTS = []


def test(fn):
    TESTS.append(fn)
    return fn


# ------------------------------------------------------------------ lin.py

@test
def g2t1():
    """a finite sum on one side of an inequality (tools/lin.py term
    abstraction): `sum_ k e. ( 1 ... N ) ( 1 / k )` is one atom"""
    ante = '( N e. NN /\\ A e. RR )'
    w = W('g2t1', 'A finite sum as an atom of the linear arithmetic: the hypothesis and '
                  'the goal both contain ` sum_ k e. ( 1 ... N ) ( 1 / k ) ` , which '
                  'tools/lin.py treats as an opaque real atom.')
    n = w.s([], 'simpl', '( %s -> N e. NN )' % ante)
    a = w.s([], 'simpr', '( %s -> A e. RR )' % ante)
    c = Closure(w, ante, {'N': ('NN', n), 'A': ('RR', a)})
    S = 'sum_ k e. ( 1 ... N ) ( 1 / k )'
    h = c.ge0(S)
    linarith(w, ante, [h], 'A <_ ( A + %s )' % S, closure=c, name='qed')
    return w


@test
def g2t2():
    """an `if` term on one side of an inequality"""
    ante = '( ( X e. RR+ /\\ Y e. RR+ ) /\\ Z e. RR )'
    w = W('g2t2', 'A conditional term as an atom of the linear arithmetic: '
                  '` if ( X <_ Y , X , Y ) ` is closed by tools/cl.py from its two '
                  'branches and treated as an opaque real atom.')
    x = w.s([], 'simpll', '( %s -> X e. RR+ )' % ante)
    y = w.s([], 'simplr', '( %s -> Y e. RR+ )' % ante)
    z = w.s([], 'simpr', '( %s -> Z e. RR )' % ante)
    c = Closure(w, ante, {'X': ('RR+', x), 'Y': ('RR+', y), 'Z': ('RR', z)})
    I = 'if ( X <_ Y , X , Y )'
    h = c.ge0(I)
    linarith(w, ante, [h], 'Z <_ ( Z + %s )' % I, closure=c, name='qed')
    return w


@test
def g2t3():
    """nlinarith-lite: products of hypotheses"""
    ante = ('( ( ( A e. RR /\\ B e. RR ) /\\ ( C e. RR /\\ D e. RR ) ) /\\ '
            '( ( A <_ B /\\ C <_ D ) /\\ ( 0 <_ A /\\ 0 <_ C ) ) )')
    w = W('g2t3', 'Multiplication of inequalities, found by the products extension of '
                  'tools/lin.py: the certificate uses the three products ` ( B - A ) x. '
                  '( D - C ) ` , ` ( B - A ) x. ( C - 0 ) ` and ` ( D - C ) x. ( A - 0 ) ` .')
    a = w.s([], 'simplll', '( %s -> A e. RR )' % ante)
    b = w.s([], 'simpllr', '( %s -> B e. RR )' % ante)
    cr = w.s([], 'simplrl', '( %s -> C e. RR )' % ante)
    d = w.s([], 'simplrr', '( %s -> D e. RR )' % ante)
    h1 = w.s([], 'simprll', '( %s -> A <_ B )' % ante)
    h2 = w.s([], 'simprlr', '( %s -> C <_ D )' % ante)
    h3 = w.s([], 'simprrl', '( %s -> 0 <_ A )' % ante)
    h4 = w.s([], 'simprrr', '( %s -> 0 <_ C )' % ante)
    c = Closure(w, ante, {'A': ('RR', a), 'B': ('RR', b), 'C': ('RR', cr), 'D': ('RR', d)})
    nlinarith(w, ante, [h1, h2, h3, h4], '( A x. C ) <_ ( B x. D )', closure=c, name='qed')
    return w


@test
def g2t4():
    """nlinarith-lite with a numeric goal: 2 <_ A and 2 <_ B give 4 <_ A x. B"""
    ante = '( ( A e. RR /\\ B e. RR ) /\\ ( 2 <_ A /\\ 2 <_ B ) )'
    w = W('g2t4', 'A product bound found by the products extension of tools/lin.py: the '
                  'certificate is ` ( A - 2 ) x. ( B - 2 ) ` plus twice each factor.')
    a = w.s([], 'simpll', '( %s -> A e. RR )' % ante)
    b = w.s([], 'simplr', '( %s -> B e. RR )' % ante)
    h1 = w.s([], 'simprl', '( %s -> 2 <_ A )' % ante)
    h2 = w.s([], 'simprr', '( %s -> 2 <_ B )' % ante)
    c = Closure(w, ante, {'A': ('RR', a), 'B': ('RR', b)})
    nlinarith(w, ante, [h1, h2], '4 <_ ( A x. B )', closure=c, name='qed')
    return w


# ------------------------------------------------------------------- cl.py

@test
def g2t5():
    """closure rules for ` ^c ` , Nceil, Nfloor, Nlog and mmu"""
    ante = '( ( X e. RR+ /\\ Y e. RR ) /\\ N e. NN )'
    w = W('g2t5', 'Closure rules of tools/cl.py for complex exponentiation, the '
                  'natural-number ceiling and floor, the iterated logarithm and the '
                  'Moebius function.')
    x = w.s([], 'simpll', '( %s -> X e. RR+ )' % ante)
    y = w.s([], 'simplr', '( %s -> Y e. RR )' % ante)
    n = w.s([], 'simpr', '( %s -> N e. NN )' % ante)
    c = Closure(w, ante, {'X': ('RR+', x), 'Y': ('RR', y), 'N': ('NN', n)})
    E = ('( ( ( X ^c Y ) x. ( ( Nceil ` Y ) + ( Nfloor ` Y ) ) ) '
         '+ ( ( 2 Nlog N ) - ( mmu ` N ) ) )')
    st = c.mem(E, 'RR')
    w.qed([st], 'idi', '( %s -> %s e. RR )' % (ante, E))
    return w


@test
def g2t6():
    """the cardinality of a class abstraction: rab -> Fin -> hashcl"""
    ante = 'N e. NN'
    w = W('g2t6', 'Closure of the cardinality of a restricted class abstraction: '
                  'tools/cl.py proves the abstraction finite from ` ssrab2 ` and the '
                  'finiteness of its domain, then applies ` hashcl ` .')
    n = w.s([], 'id', '( %s -> N e. NN )' % ante)
    c = Closure(w, ante, {'N': ('NN', n)})
    E = '( # ` { x e. ( 1 ... N ) | x || N } )'
    st = c.mem(E, 'NN0')
    w.qed([st], 'idi', '( %s -> %s e. NN0 )' % (ante, E))
    return w


@test
def g2t7():
    """setness: -u A e. _V and ( A + B ) e. _V"""
    ante = 'A e. RR'
    w = W('g2t7', 'Setness closure in tools/cl.py: ` negex ` for a negation and '
                  '` ovex ` for an operation value.')
    a = w.s([], 'id', '( %s -> A e. RR )' % ante)
    c = Closure(w, ante, {'A': ('RR', a)})
    s1 = c.mem('-u A', '_V')
    s2 = c.mem('( A + A )', '_V')
    w.qed([s1, s2], 'jca', '( %s -> ( -u A e. _V /\\ ( A + A ) e. _V ) )' % ante)
    return w


@test
def g2t8():
    """1 <_ E for a product of two factors that are each at least 1"""
    ante = '( ( A e. RR+ /\\ B e. RR+ ) /\\ ( 1 <_ A /\\ 1 <_ B ) )'
    w = W('g2t8', 'A ` 1 <_ E ` route of tools/cl.py that goes through neither NN nor '
                  '` 1 < E ` : a product of two factors that are each at least 1.')
    a = w.s([], 'simpll', '( %s -> A e. RR+ )' % ante)
    b = w.s([], 'simplr', '( %s -> B e. RR+ )' % ante)
    h1 = w.s([], 'simprl', '( %s -> 1 <_ A )' % ante)
    h2 = w.s([], 'simprr', '( %s -> 1 <_ B )' % ante)
    c = Closure(w, ante, {'A': [('RR+', a), ('ge1', h1)], 'B': [('RR+', b), ('ge1', h2)]})
    st = c.prove('( A x. B )', 'ge1')
    w.qed([st], 'idi', '( %s -> 1 <_ ( A x. B ) )' % ante)
    return w


@test
def g2t9():
    """1 <_ E for a positive integer, and for its powers"""
    ante = '( Z e. ZZ /\\ 0 < Z )'
    w = W('g2t9', 'A ` 1 <_ E ` route of tools/cl.py through ` zgt0ge1 ` , and '
                  '` expge1 ` above it.')
    z = w.s([], 'simpl', '( %s -> Z e. ZZ )' % ante)
    p = w.s([], 'simpr', '( %s -> 0 < Z )' % ante)
    c = Closure(w, ante, {'Z': [('ZZ', z), ('gt0', p)]})
    st = c.prove('( Z ^ 3 )', 'ge1')
    w.qed([st], 'idi', '( %s -> 1 <_ ( Z ^ 3 ) )' % ante)
    return w


@test
def g2t10():
    """the antecedent-lifting helper: three levels at once"""
    to = ('( ( ( A e. RR /\\ B e. RR ) /\\ C e. RR /\\ D e. RR ) /\\ E e. RR )')
    w = W('g2t10', 'The antecedent-lifting helper of tools/cl.py: a step proved under '
                   'the innermost conjunct is lifted through a binary, a ternary and a '
                   'binary conjunction in one call.')
    sub = '( A e. RR /\\ B e. RR )'
    a = w.s([], 'simpl', '( %s -> A e. RR )' % sub)
    b = w.s([], 'simpr', '( %s -> B e. RR )' % sub)
    st = w.s([a, b], 'readdcld', '( %s -> ( A + B ) e. RR )' % sub)
    lift(w, st, to, name='qed')
    return w


# ----------------------------------------------------------------- fsum.py

@test
def g2t11():
    """the external-closure escape: a body closure the module cannot derive"""
    ante = '( N e. NN /\\ F : ( 1 ... N ) --> CC )'
    w = W('g2t11', 'The external-closure escape of tools/fsum.py: the caller records '
                   'the closure of ` ( F ` k ) ` on the child closure, which the module '
                   'then uses for ` fsumadd ` .')
    n = w.s([], 'simpl', '( %s -> N e. NN )' % ante)
    fn = w.s([], 'simpr', '( %s -> F : ( 1 ... N ) --> CC )' % ante)
    c = Closure(w, ante, {'N': ('NN', n)})
    f = FSum(w, c)
    A = '( 1 ... N )'
    ch = f.child('k', A)
    fn2 = w.s([fn], 'adantr', '( %s -> F : ( 1 ... N ) --> CC )' % ch.ante)
    el = w.s([], 'simpr', '( %s -> k e. %s )' % (ch.ante, A))
    i = w.inst('ffvelcdm')
    st = w.s([fn2, el, i], 'syl2anc', '( %s -> ( F ` k ) e. CC )' % ch.ante)
    f.have('k', A, '( F ` k )', 'CC', st)
    f.add('k', A, '( F ` k )', '1', name='qed')
    return w


@test
def g2t12():
    """the fsumss wrapper"""
    ante = 'N e. NN'
    w = W('g2t12', 'The ` fsumss ` wrapper of tools/fsum.py: a sum over a subset, with '
                   'the vanishing obligation on the difference discharged by the caller.')
    n = w.s([], 'id', '( %s -> N e. NN )' % ante)
    c = Closure(w, ante, {'N': ('NN', n)})
    f = FSum(w, c)
    uz = num.closed(w, [], '1nn0', '1 e. NN0')
    e0 = num.closed(w, [], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')
    m = num.closed(w, [uz, e0], 'eleqtri', '1 e. ( ZZ>= ` 0 )')
    m1 = w.s([m], 'a1i', '( %s -> 1 e. ( ZZ>= ` 0 ) )' % ante)
    i = w.inst('fzss1')
    sub = w.s([m1, i], 'syl', '( %s -> ( 1 ... N ) C_ ( 0 ... N ) )' % ante)
    f.ss('k', '( 1 ... N )', '( 0 ... N )', '0', sub,
         lambda chd: w.s([], 'eqidd', '( %s -> 0 = 0 )' % chd.ante), name='qed')
    return w


@test
def g2t13():
    """the fsumcom wrapper"""
    ante = '( M e. NN /\\ N e. NN )'
    w = W('g2t13', 'The ` fsumcom ` wrapper of tools/fsum.py: the body closure comes '
                   'from the two-variable child closure of tools/cl.py.')
    m = w.s([], 'simpl', '( %s -> M e. NN )' % ante)
    n = w.s([], 'simpr', '( %s -> N e. NN )' % ante)
    c = Closure(w, ante, {'M': ('NN', m), 'N': ('NN', n)})
    f = FSum(w, c)
    f.com('j', '( 1 ... M )', 'k', '( 1 ... N )', '( j x. k )', name='qed')
    return w


@test
def g2t14():
    """the fsumdvdsmul wrapper"""
    ante = '( ( M e. NN /\\ N e. NN ) /\\ ( M gcd N ) = 1 )'
    w = W('g2t14', 'The ` fsumdvdsmul ` wrapper of tools/fsum.py: multiplicativity of '
                   'the divisor count, with the six equation hypotheses and the '
                   'substitution hypothesis generated by the module.')
    m = w.s([], 'simpll', '( %s -> M e. NN )' % ante)
    n = w.s([], 'simplr', '( %s -> N e. NN )' % ante)
    g = w.s([], 'simpr', '( %s -> ( M gcd N ) = 1 )' % ante)
    c = Closure(w, ante, {'M': ('NN', m), 'N': ('NN', n)})
    f = FSum(w, c)

    def prod(ch, D):
        t = num.closed(w, [], '1t1e1', '( 1 x. 1 ) = 1')
        return w.s([t], 'a1i', '( %s -> ( 1 x. 1 ) = %s )' % (ch.ante, D))
    f.dvdsmul('M', 'N', m, n, g, 'j', 'k', 'i', '1', '1', '1', prod, name='qed')
    return w


# ------------------------------------------------------------------ num.py

@test
def g2t15():
    """main-body numeral routes: 4 e. RR+, 6 e. RR+, 6 =/= 0, ( 4 x. 5 )"""
    ante = '( A e. RR /\\ ; 2 4 <_ A )'
    w = W('g2t15', 'Main-body numeral routes of tools/num.py: the closure of the '
                   'divisors 4 and 6 and the digit product ` ( 4 x. 5 ) ` , none of '
                   'which now cites a set.mm mathbox.')
    a = w.s([], 'simpl', '( %s -> A e. RR )' % ante)
    h = w.s([], 'simpr', '( %s -> ; 2 4 <_ A )' % ante)
    c = Closure(w, ante, {'A': ('RR', a)})
    linarith(w, ante, [h], '; 1 0 <_ ( ( A / 4 ) + ( A / 6 ) )', closure=c, name='qed')
    return w


@test
def g2t16():
    """main-body numeral routes: 9 e. RR+, 9 =/= 0, ( 9 x. 5 ), ( 9 x. 4 )"""
    ante = '( A e. RR /\\ ; 4 5 <_ A )'
    w = W('g2t16', 'Main-body numeral routes of tools/num.py for the divisor 9 and the '
                   'digit products it needs.')
    a = w.s([], 'simpl', '( %s -> A e. RR )' % ante)
    h = w.s([], 'simpr', '( %s -> ; 4 5 <_ A )' % ante)
    c = Closure(w, ante, {'A': ('RR', a)})
    linarith(w, ante, [h], '5 <_ ( A / 9 )', closure=c, name='qed')
    return w


@test
def g2t17():
    """main-body numeral route for a digit sum in the flipped orientation"""
    ante = 'A e. RR'
    w = W('g2t17', 'A digit sum whose set.mm label exists only in a mathbox in the '
                   'orientation the normal form needs: tools/num.py flips it with '
                   '` addcomi ` and cites the main-body label.')
    a = w.s([], 'id', '( %s -> A e. RR )' % ante)
    c = Closure(w, ante, {'A': ('RR', a)})
    linarith(w, ante, [], '( ( A + 1 ) + 3 ) <_ ( A + 4 )', closure=c, name='qed')
    return w


def main():
    want = [a for a in sys.argv[1:] if not a.startswith('-')]
    ok = True
    for fn in TESTS:
        if want and fn.__name__ not in want:
            continue
        w = fn()
        ok = w.run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
