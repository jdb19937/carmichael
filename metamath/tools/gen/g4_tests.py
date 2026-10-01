"""Test theorems for the shared automation repaired by sortie G4.

    MM_DB=sorties/g4.mm python3 tools/gen/g4_tests.py             # all of them
    MM_DB=sorties/g4.mm python3 tools/gen/g4_tests.py g4t3 g4t5   # a subset
    MM_DB=sorties/g4.mm python3 tools/gen/g4_tests.py -dv         # the
                                                                  # distinct-variable
                                                                  # linter
Each test exercises one repair of tools/dv.py, tools/congr.py, tools/fsum.py or
tools/lin.py; the worksheet is written to MM_WS and added to MM_DB by
tools/mm.py.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W
from cl import Closure
from lin import nlinarith
from fsum import FSum
import congr, dv, num

TESTS = []


def test(fn):
    TESTS.append(fn)
    return fn


def qedify(w, step):
    """rename the last step, which already proves the theorem, to qed"""
    assert w.lines[-1].startswith(step + ':'), w.lines[-1]
    w.lines[-1] = 'qed' + w.lines[-1][len(step):]
    return 'qed'


# ---------------------------------------------------------------- congr.py

@test
def g4t1():
    """the value of a mapping at an argument (tools/congr.py `mptval`): the
    substitution hypothesis, `eqid`, `fvmptg` and the existence of the value"""
    MP = '( q e. NN |-> ( ( q + 1 ) x. 2 ) )'
    ante = 'N e. NN'
    w = W('g4t1', 'The value of a mapping at an argument, through ` fvmptg ` : the '
                  'pattern tools/congr.py writes, whose substitution hypothesis comes '
                  'from the congruence generator and whose side conditions come from '
                  'tools/cl.py.')
    n = w.s([], 'id', '( %s -> N e. NN )' % ante)
    cl = Closure(w, ante, {'N': ('NN', n)})
    st, val = congr.mptval(w, ante, 'q', 'NN', '( ( q + 1 ) x. 2 )', 'N', n,
                           mp=MP, closure=cl, name='qed')
    assert val == '( ( N + 1 ) x. 2 )', val
    return w


@test
def g4t2():
    """a mapping whose body is itself a binder: the congruence generator
    descends into the sum, which is what C1's four hand-written value lemmas
    did one `oveq` at a time"""
    B = 'sum_ t e. ( 1 ... q ) ( ( F ` t ) x. q )'
    MP = '( q e. NN |-> %s )' % B
    ante = 'N e. NN'
    w = W('g4t2', 'The value of a mapping whose body is a finite sum: tools/congr.py '
                  'descends into the sum with ` sumeq12dv ` and the value follows from '
                  '` fvmptg ` .')
    n = w.s([], 'id', '( %s -> N e. NN )' % ante)
    ex = w.s([w.s([], 'sumex', '%s e. _V' % B.replace(' q ', ' N ').replace('... q', '... N'))],
             'a1i', '( %s -> %s e. _V )' % (ante, 'sum_ t e. ( 1 ... N ) ( ( F ` t ) x. N )'))
    st, val = congr.mptval(w, ante, 'q', 'NN', B, 'N', n, mp=MP, exs=ex, name='qed')
    assert val == 'sum_ t e. ( 1 ... N ) ( ( F ` t ) x. N )', val
    return w


# ----------------------------------------------------------------- fsum.py

@test
def g4t3():
    """fsumless: a shorter sum of nonnegative terms is smaller"""
    ante = '( N e. NN /\\ M e. ( 1 ... N ) )'
    w = W('g4t3', 'A shorter sum of nonnegative terms is smaller, through tools/fsum.py '
                  'and ` fsumless ` .')
    n = w.s([], 'simpl', '( %s -> N e. NN )' % ante)
    m = w.s([], 'simpr', '( %s -> M e. ( 1 ... N ) )' % ante)
    uz = w.s([m, w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` M ) )' % ante)
    sub = w.s([uz, w.inst('fzss2')], 'syl',
              '( %s -> ( 1 ... M ) C_ ( 1 ... N ) )' % ante)
    cl = Closure(w, ante, {'N': ('NN', n)})
    FSum(w, cl).less('k', '( 1 ... N )', '( 1 ... M )', '( k ^ 2 )', sub, name='qed')
    return w


@test
def g4t4():
    """fsumf1o: a sum re-indexed by a bijection"""
    ante = ('( ( A e. Fin /\\ C e. Fin ) /\\ '
            '( F : C -1-1-onto-> A /\\ H : A --> CC ) )')
    w = W('g4t4', 'A finite sum re-indexed by a bijection, through tools/fsum.py and '
                  '` fsumf1o ` : the substituted body and the four hypothesis steps are '
                  'written by the module.')
    af = w.s([], 'simpll', '( %s -> A e. Fin )' % ante)
    cf = w.s([], 'simplr', '( %s -> C e. Fin )' % ante)
    bij = w.s([], 'simprl', '( %s -> F : C -1-1-onto-> A )' % ante)
    hf = w.s([], 'simprr', '( %s -> H : A --> CC )' % ante)
    ch = '( %s /\\ k e. A )' % ante
    hb = w.s([w.s([hf], 'adantr', '( %s -> H : A --> CC )' % ch),
              w.s([], 'simpr', '( %s -> k e. A )' % ch)], 'ffvelcdmd',
             '( %s -> ( H ` k ) e. CC )' % ch)
    cl = Closure(w, ante, {'A': ('Fin', af), 'C': ('Fin', cf)})
    f = FSum(w, cl)
    val = w.s([], 'eqidd', '( ( %s /\\ n e. C ) -> ( F ` n ) = ( F ` n ) )' % ante)
    f.f1o('k', 'A', '( H ` k )', 'n', 'C', 'F', '( F ` n )', bij, val, fin=cf,
          body=hb, name='qed')
    assert f.body == '( H ` ( F ` n ) )', f.body
    return w


@test
def g4t5():
    """fsumxp: two sums combined into one over the cartesian product"""
    ante = ('( ( A e. Fin /\\ B e. Fin ) /\\ '
            '( G : A --> CC /\\ H : B --> CC ) )')
    w = W('g4t5', 'A double sum as one sum over the cartesian product, through '
                  'tools/fsum.py and ` fsumxp ` : the substitution hypothesis comes from '
                  '` op1std ` , ` op2ndd ` and the congruence generator.')
    af = w.s([], 'simpll', '( %s -> A e. Fin )' % ante)
    bf = w.s([], 'simplr', '( %s -> B e. Fin )' % ante)
    gf = w.s([], 'simprl', '( %s -> G : A --> CC )' % ante)
    hf = w.s([], 'simprr', '( %s -> H : B --> CC )' % ante)
    pc = '( %s /\\ ( j e. A /\\ k e. B ) )' % ante
    gb = w.s([w.s([gf], 'adantr', '( %s -> G : A --> CC )' % pc),
              w.s([], 'simprl', '( %s -> j e. A )' % pc)], 'ffvelcdmd',
             '( %s -> ( G ` j ) e. CC )' % pc)
    hb = w.s([w.s([hf], 'adantr', '( %s -> H : B --> CC )' % pc),
              w.s([], 'simprr', '( %s -> k e. B )' % pc)], 'ffvelcdmd',
             '( %s -> ( H ` k ) e. CC )' % pc)
    body = w.s([gb, hb], 'mulcld', '( %s -> ( ( G ` j ) x. ( H ` k ) ) e. CC )' % pc)
    cl = Closure(w, ante, {'A': ('Fin', af), 'B': ('Fin', bf)})
    f = FSum(w, cl)
    f.xp('j', 'A', 'k', 'B', '( ( G ` j ) x. ( H ` k ) )', 'z', body=body, name='qed')
    assert f.body == '( ( G ` ( 1st ` z ) ) x. ( H ` ( 2nd ` z ) ) )', f.body
    return w


@test
def g4t6():
    """fsumrev: a sum over a reversed index"""
    ante = '( N e. NN /\\ F : ( 1 ... N ) --> CC )'
    w = W('g4t6', 'A finite sum with its index reversed, through tools/fsum.py and '
                  '` fsumrev ` .')
    n = w.s([], 'simpl', '( %s -> N e. NN )' % ante)
    ff = w.s([], 'simpr', '( %s -> F : ( 1 ... N ) --> CC )' % ante)
    ch = '( %s /\\ j e. ( 1 ... N ) )' % ante
    fb = w.s([w.s([ff], 'adantr', '( %s -> F : ( 1 ... N ) --> CC )' % ch),
              w.s([], 'simpr', '( %s -> j e. ( 1 ... N ) )' % ch)], 'ffvelcdmd',
             '( %s -> ( F ` j ) e. CC )' % ch)
    cl = Closure(w, ante, {'N': ('NN', n)})
    f = FSum(w, cl)
    f.rev('j', '1', 'N', '( N + 1 )', '( F ` j )', 'k', body=fb, name='qed')
    return w


# ------------------------------------------------------------------ lin.py

@test
def g4t7():
    """an integer power inside the nonlinear search (V3's reproduction):
    `3 <_ ( P ^ 2 )` has no certificate as written, and one after the power
    is expanded into a product"""
    ante = '( P e. RR /\\ 2 <_ P )'
    w = W('g4t7', 'A bound on a square: the certificate search of tools/lin.py sees an '
                  'integer power as an opaque atom, so it writes the power out as a '
                  'product with ` sqvald ` , finds the certificate there and carries the '
                  'result back with ` 3brtr4d ` .')
    r = w.s([], 'simpl', '( %s -> P e. RR )' % ante)
    h = w.s([], 'simpr', '( %s -> 2 <_ P )' % ante)
    cl = Closure(w, ante, {'P': ('RR', r)})
    nlinarith(w, ante, [h], '3 <_ ( P ^ 2 )', closure=cl, name='qed')
    return w


@test
def g4t8():
    """degree four in the certificate: a one-variable polynomial bound, the
    shape V3's Brun-Titchmarsh needs"""
    T = num.nat_text(3)
    ante = '( L e. RR /\\ %s <_ L )' % T
    w = W('g4t8', 'A polynomial bound of degree four: the certificate of tools/lin.py '
                  'needs the fourth power of the hypothesis ` %s <_ L ` , and both sides '
                  'of the goal are written out as products first.' % T)
    r = w.s([], 'simpl', '( %s -> L e. RR )' % ante)
    h = w.s([], 'simpr', '( %s -> %s <_ L )' % (ante, T))
    cl = Closure(w, ante, {'L': ('RR', r)})
    nlinarith(w, ante, [h], '( ( 1 + L ) ^ 3 ) <_ ( L ^ 4 )', closure=cl, name='qed')
    return w


@test
def g4t9():
    """the own-lemma route to `0 <_ ( 2 logb X )`: with cl.LOGB_GE0 set to
    `logb2ge0` the automation emits no mathbox citation at all"""
    import cl
    ante = '( X e. RR+ /\\ 1 <_ X )'
    w = W('g4t9', 'The route of tools/cl.py to ` 0 <_ ( 2 logb X ) ` through our own '
                  '` logb2ge0 ` instead of set.mm\'s mathbox theorem ` logbge0b ` .')
    rp = w.s([], 'simpl', '( %s -> X e. RR+ )' % ante)
    g1 = w.s([], 'simpr', '( %s -> 1 <_ X )' % ante)
    cl_ = Closure(w, ante, {'X': [('RR+', rp), ('ge1', g1)]})
    old = cl.LOGB_GE0
    cl.LOGB_GE0 = 'logb2ge0'
    try:
        st = cl_.prove('( 2 logb X )', 'ge0')
    finally:
        cl.LOGB_GE0 = old
    return qedify(w, st) and w


@test
def g4t10():
    """cl.py rules for the cartesian product and the greatest common divisor"""
    ante = '( ( A e. Fin /\\ B e. Fin ) /\\ ( M e. ZZ /\\ N e. NN ) )'
    w = W('g4t10', 'The rules of tools/cl.py for a cartesian product and a greatest '
                   'common divisor: ` xpfi ` , ` xpexg ` , ` gcdcld ` and ` gcdnncl ` .')
    af = w.s([], 'simpll', '( %s -> A e. Fin )' % ante)
    bf = w.s([], 'simplr', '( %s -> B e. Fin )' % ante)
    m = w.s([], 'simprl', '( %s -> M e. ZZ )' % ante)
    n = w.s([], 'simprr', '( %s -> N e. NN )' % ante)
    cl = Closure(w, ante, {'A': ('Fin', af), 'B': ('Fin', bf),
                           'M': ('ZZ', m), 'N': ('NN', n)})
    x = cl.mem('( A X. B )', 'Fin')
    v = cl.mem('( A X. B )', '_V')
    g = cl.mem('( M gcd N )', 'NN0')
    w.qed([x, v, g], '3jca',
          '( %s -> ( ( A X. B ) e. Fin /\\ ( A X. B ) e. _V /\\ ( M gcd N ) e. NN0 ) )' % ante)
    return w


# ------------------------------------------- the distinct-variable linter

C3_LEMMAS = ('cvgcmp abscvgcvg isumle isumrecl isumcl isum1p isummulc2 isumsplit '
             'isumclim2 iserex iserabs fsumser fsumparts fsumf1o dvfsumle mtest '
             'ulmdv ulmcn seqof').split()


def dvtest():
    """the linter against the four reproductions the sorties recorded"""
    ok = True
    print(dv.report(C3_LEMMAS, binds='m n q k d e'))
    free = dv.free_letters(C3_LEMMAS)
    want = list('abcdeghlopqt')
    good = free == want
    ok = ok and good
    print()
    print(('OK   ' if good else 'FAIL ') + 'C3 section 3 item 3: the letters that '
          'survive are %s (C3 computed %s by hand)' % (' '.join(free), ' '.join(want)))

    cases = [
        ('V2c trap 2: fvmptg forbids the mapping binder in the value', True,
         'fvmptg', {'x': 't', 'A': '( 1 ... N )',
                    'C': '( t e. ( 1 ... N ) |-> ( t + K ) )'}),
        ('the same with the inner binder renamed', False,
         'fvmptg', {'x': 't', 'A': '( 1 ... N )',
                    'C': '( v e. ( 1 ... N ) |-> ( v + K ) )'}),
        ('T1 trap 1: nn0ind forbids y in the induction property, bound or free', True,
         'nn0ind', {'y': 'y', 'ph': 'A. y e. Word B ( ( F ` y ) = Z )'}),
        ('the same with the quantifier renamed', False,
         'nn0ind', {'y': 'y', 'ph': 'A. s e. Word B ( ( F ` s ) = Z )'}),
        ("V3 trap 1: a lemma's own proof dummy blocks the instantiation", True,
         'fvmptg', {'x': 't', 'C': '( y e. ( 1 ... N ) |-> ( y + K ) )'}),
    ]
    print()
    for name, want_bad, lab, sub in cases:
        bad = dv.check(lab, sub)
        good = bool(bad) == want_bad
        ok = ok and good
        print(('OK   ' if good else 'FAIL ') + name)
        for b in bad:
            print('       ' + b)
    return ok


def main():
    args = sys.argv[1:]
    if '-dv' in args:
        return dvtest()
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
