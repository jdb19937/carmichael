"""T7b: the unfolding theorems ` tmiXXXu ` : an installation predicate gives the
fragment's own program equations and label typings (by its df- )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *

SEL = sys.argv[1:]


def unf(name):
    f = FRAGS[name]
    lab = 'tmi%su' % name
    w = W(lab, 'Unfolding the installation predicate of ` %s ` : its own program equations, '
               'callee predicates and label typings.' % name)
    d = w.s([], 'df-%s' % f.const.lower(), f.df())
    w.qed([d], 'biimpi', unfold_stmt(f))
    return w.run()


if __name__ == '__main__':
    for n in SEL:
        unf(n)
