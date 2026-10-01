"""Z6a (block D, the Mellin identity): shared step patterns."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_ghlib import *
from cl import Closure, lift, split_imp, formula_of
import lin
from lin import linarith, lineq, nlinarith
import num

GYM = GY()                                               # the Mellin integrand ( w e. DG |-> ( ( _G ` w ) x. ( Y ^c -u w ) ) )
STRIP = lambda A, B: "( `' Re \" ( %s (,) %s ) )" % (A, B)


def cbvm(w, ante, x, y, X, bx):
    """( ante -> ( x e. X |-> bx ) = ( y e. X |-> by ) ); returns (step, new mapping)"""
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, y, x, y))
    stp, by = w.congr(bx, {x: y}, '%s = %s' % (x, y), {x: idk})
    c = w.s([stp if stp else idk], 'cbvmptv', '( %s e. %s |-> %s ) = ( %s e. %s |-> %s )' % (x, X, bx, y, X, by))
    return w.s([c], 'a1i', '( %s -> ( %s e. %s |-> %s ) = ( %s e. %s |-> %s ) )' % (ante, x, X, bx, y, X, by)), '( %s e. %s |-> %s )' % (y, X, by)


def toqed(w, step, label=None):
    """rename the LAST worksheet step to qed and check its formula against the frozen statement"""
    last = w.lines[-1]
    assert last.startswith(step + ':'), (step, last[:80])
    w.lines[-1] = 'qed' + last[len(step):]
    if label:
        f = last.split('|-', 1)[1].strip()
        assert f == STATEMENTS[label], '\n%s\n%s' % (f, STATEMENTS[label])


def cnst(w, step):
    """the consequent of a step's formula"""
    return split_imp(formula_of(w, step))[1]


def mv(w, ante, x, X, body, T, mem):
    """( ante -> ( ( x e. X |-> body ) ` T ) = body[T/x] ) (fvmptd3); returns (step, value)"""
    return mpval(w, ante, x, X, body, T, mem)


def eqchain(w, ante, lhs, steps):
    """eqtrd along steps, each ( ante -> a_i = a_{i+1} ); returns ( ante -> lhs = last )"""
    acc = steps[0]
    for s_ in steps[1:]:
        r = split_imp(formula_of(w, s_))[1]
        rhs = r.split(' = ', 1)[1] if r.count(' = ') == 1 else None
        from congr import parse_wff
        n = parse_wff(r)
        rhs = n.kids[1].text()
        acc = w.s([acc, s_], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, rhs))
    return acc


def status(label, note=''):
    import re
    p = os.path.join(os.path.dirname(__file__), '..', '..', 'worksheets', label + '.mmp')
    n = sum(1 for l in open(p) if re.match(r'^[0-9a-z]+:', l))
    with open(os.path.join(os.path.dirname(__file__), '..', '..', 'scratch', 'z6am-status.md'), 'a') as f:
        f.write('- %s: done (%d steps)%s\n' % (label, n, note))
    return n
