"""T10: t10stk, the stack facts at the numerals: every index 0 ... 7 in ( 0 ..^ 8 ), every pair distinct.

    MM_DB=sorties/t10.mm python3 tools/gen/t10_c_stk.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *


def conj(w, tree, leaf):
    if isinstance(tree, str):
        return leaf(tree)
    sts = [conj(w, t, leaf) for t in tree]
    return w.s(sts, 'pm3.2i' if len(tree) == 2 else '3pm3.2i', cj(tree))


def t10stk():
    w = W('t10stk', 'The stack facts at the numerals ` 0 ... 7 ` (the concrete stacks of Steps23.lean): '
                    'each is a stack index and any two are distinct (Lean\'s ` by decide ` ).')
    memo = {}

    def re_(n):
        return w.s([], '%sre' % n, '%s e. RR' % n)

    def leaf(t):
        if t in memo:
            return memo[t]
        tk = t.split()
        if tk[1] == 'e.':
            n = tk[0]
            lt = w.s([], '%slt8' % n if n != '0' else '8pos', '%s < 8' % n)
            nn = w.s([], '%snn0' % n, '%s e. NN0' % n)
            e = w.s([], 'elfzo0', '( %s e. ( 0 ..^ 8 ) <-> ( %s e. NN0 /\\ 8 e. NN /\\ %s < 8 ) )' % (n, n, n))
            st = w.s([w.s([nn, w.s([], '8nn', '8 e. NN'), lt], '3pm3.2i', '( %s e. NN0 /\\ 8 e. NN /\\ %s < 8 )' % (n, n)), e],
                     'mpbir', t)
        else:
            a, b = tk[0], tk[2]
            lo, hi = sorted([a, b], key=int)
            ltl = ('%slt%s' % (lo, hi)) if lo != '0' else ('0lt1' if hi == '1' else '%spos' % hi)
            lt = w.s([], ltl, '%s < %s' % (lo, hi))
            st = w.s([re_(lo), lt], 'ltneii', '%s =/= %s' % (lo, hi))
            if a != lo:
                st = w.s([st], 'necomi', t)
        memo[t] = st
        return st
    top = conj(w, NUMS, leaf)
    w.lines[-1] = 'qed' + w.lines[-1][len(top):]
    return w.run()


if __name__ == '__main__':
    t10stk()
