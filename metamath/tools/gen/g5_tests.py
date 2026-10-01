"""Sortie G5: the test theorems of the fast path, the certificate mode and the
driver's $e renumbering.  MM_DB=sorties/g5.mm python3 tools/gen/g5_tests.py [LABEL...]

The modules under test are the staged copies in tools/next/ (put ahead of
tools/ on the path); once tools/next/ is swapped into tools/ the two entries
coincide and the generator runs unchanged."""
import sys, os
TOOLS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, TOOLS)
sys.path.insert(0, os.path.join(TOOLS, 'next'))
import mm, lin, num                  # from tools/next while it exists (tm.py
from lin import linarith, nlinarith, lineq   # would push tools/ ahead of it)
from tm import W

lin.FASTPATH = True

AL = '( L e. RR /\\ ; ; 1 0 0 <_ L )'
AB = '( A e. RR /\\ B e. RR /\\ A < B )'
AE = '( A e. RR /\\ B e. RR /\\ A = ( 2 x. B ) )'
A5 = '( L e. RR /\\ L <_ 5 )'
AT = ('( ( Q e. RR /\\ T e. RR /\\ S e. RR ) /\\ '
      '( 0 <_ Q /\\ S <_ ( ; 6 4 x. Q ) /\\ ( Q x. Q ) <_ T ) )')


def ctxL(w, ante=AL):
    return {'L': w.s([], 'simpl', '( %s -> L e. RR )' % ante)}, w.s([], 'simpr', '( %s -> %s )' % (ante, ante.split('/\\ ')[1][:-2]))


def ctxAB(w, ante, third):
    lv = {'A': w.s([], 'simp1', '( %s -> A e. RR )' % ante), 'B': w.s([], 'simp2', '( %s -> B e. RR )' % ante)}
    return lv, w.s([], 'simp3', '( %s -> %s )' % (ante, third))


def one(label, desc, ante, ctx, goal, **kw):
    w = W(label, desc)
    lv, h = ctx(w)
    linarith(w, ante, [h], goal, leaves=lv, name='qed', **kw)
    return w


def g5t1():
    return one('g5t1', 'Fast path of tools/lin.py: a literal against a sum (le2addd), the literal '
               'factor (lemul2ad), transitivity through the hypothesis, a closed numeral comparison.',
               AL, ctxL, '2 <_ ( 1 + ( ( 2 / 5 ) x. L ) )')


def g5t2():
    return one('g5t2', 'Fast path: a strict goal through ltmul2dd and ltletrd.',
               AL, ctxL, '0 < ( ( 2 / 5 ) x. L )')


def g5t3():
    return one('g5t3', 'Fast path: a literal against a quotient by a numeral (ltmuldivd).',
               AL, ctxL, '( 1 / 2 ) < ( L / 5 )')


def g5t4():
    return one('g5t4', 'Fast path: the same denominator and subtrahend on both sides (ltdiv1dd, ltsub1dd).',
               AB, lambda w: ctxAB(w, AB, 'A < B'), '( ( A - 3 ) / 2 ) < ( ( B - 3 ) / 2 )')


def g5t5():
    return one('g5t5', 'Fast path: a sum against a sum with a common minuend (le2addd, lesub2dd), '
               'the strict hypothesis weakened by ltled.',
               AB, lambda w: ctxAB(w, AB, 'A < B'), '( ( 5 - B ) + 1 ) <_ ( ( 5 - A ) + 2 )')


def g5t6():
    return one('g5t6', 'Fast path: an equation hypothesis used in the reverse orientation, then addge01d.',
               AE, lambda w: ctxAB(w, AE, 'A = ( 2 x. B )'), '( 2 x. B ) <_ ( A + 1 )')


def g5t7():
    return one('g5t7', 'Fast path: a sum against a literal, the literal split between the summands, '
               'and a literal factor against a literal.',
               A5, lambda w: ctxL(w, A5), '( ( 2 x. L ) + 3 ) <_ ; 1 3 ')


def g5t8():
    """a theorem with $e hypotheses: mm.py add renumbers the proof itself"""
    w = W('g5t8', 'A theorem with $e hypotheses added through tools/mm.py add, which now folds '
                  'the hypothesis renumbering of tools/c0lib.py in; the body is the fast path (addge02d).')
    w.s([], 'g5t8.1', '( ph -> A e. RR )', name='h1')
    w.s([], 'g5t8.2', '( ph -> 0 <_ A )', name='h2')
    linarith(w, 'ph', ['2'], '1 <_ ( A + 1 )', leaves={'A': '1'}, name='qed')
    return w


def g5t9():
    return one('g5t9', 'Fast path: negation on both sides (ltnegd) over a strict sum (ltleaddd).',
               AB, lambda w: ctxAB(w, AB, 'A < B'), '-u ( B + 1 ) < -u ( A + 1 )')


def g5t10():
    """the supplied-certificate mode on the twin-sieve inequality of V4a"""
    w = W('g5t10', 'The supplied-certificate mode of tools/lin.py: the twin-sieve inequality of '
                   'twinarc with the certificate ( 2 x. Q x. ( 64 Q - S ) ) + 128 x. ( T - Q Q ) named by the caller.')
    st = lambda h, r, g: w.s(h, r, '( %s -> %s )' % (AT, g))
    b1 = st([], 'simpl', '( Q e. RR /\\ T e. RR /\\ S e. RR )')
    b2 = st([], 'simpr', '( 0 <_ Q /\\ S <_ ( ; 6 4 x. Q ) /\\ ( Q x. Q ) <_ T )')
    q, t, s = st([b1], 'simp1d', 'Q e. RR'), st([b1], 'simp2d', 'T e. RR'), st([b1], 'simp3d', 'S e. RR')
    qge, h5, qqT = st([b2], 'simp1d', '0 <_ Q'), st([b2], 'simp2d', 'S <_ ( ; 6 4 x. Q )'), st([b2], 'simp3d', '( Q x. Q ) <_ T')
    nlinarith(w, AT, [qge, h5, qqT], '( ( 2 x. Q ) x. S ) <_ ( ; ; 1 2 8 x. T )',
              leaves={'Q': q, 'T': t, 'S': s}, cert={(qge, h5): 2, qqT: 128}, name='qed')
    return w


def g5t11():
    w = W('g5t11', 'lineq through the fast path: both inequalities of an equation from an equation hypothesis.')
    lv, h = ctxAB(w, AE, 'A = ( 2 x. B )')
    lineq(w, AE, '( A + 1 )', '( ( 2 x. B ) + 1 )', hyps=[h], leaves=lv, name='qed')
    return w


ALL = {f.__name__: f for f in (g5t1, g5t2, g5t3, g5t4, g5t5, g5t6, g5t7, g5t8, g5t9, g5t10, g5t11)}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        w = ALL[n]()
        path = w.write()
        print('%s: %d steps' % (n, sum(1 for l in w.lines if ':' in l)))
        ok = mm.cmd_add(path)
        print(('OK   ' if ok else 'FAIL ') + n)
        if not ok:
            sys.exit(1)
