"""Sortie KD1: the iterated derivatives of a holomorphic function are holomorphic (kdholdn)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def DN(k): return '( ( CC Dn F ) ` %s )' % k


def gen_holdn():
    w = W('kdholdn', 'The iterated derivatives ` ( ( CC Dn F ) ` K ) ` of a function holomorphic on ` D ` are holomorphic on ` D ` (EF2 ` ef2dvh ` by induction).')
    H = HOLF('F', 'D')
    e = {}
    for nm, t in (('0', '0'), ('y', 'y'), ('y1', '( y + 1 )'), ('K', 'K')):
        f = w.s([], 'fveq2', '( x = %s -> %s = %s )' % (t, DN('x'), DN(t)))
        e[nm] = holeq(w, 'x = %s' % t, f, DN('x'), DN(t), 'D')
    # base
    pm, ds = pmcc(w, H, w.s([], 'id', '( %s -> %s )' % (H, H)), 'F', 'D')
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % H)
    d0 = w.s([ccs, pm, w.inst('dvn0')], 'syl2anc', '( %s -> %s = F )' % (H, DN('0')))
    q0 = holeq(w, H, d0, DN('0'), 'F', 'D')
    b = w.s([w.s([], 'id', '( %s -> %s )' % (H, H)), q0], 'mpbird', '( %s -> %s )' % (H, HOLF(DN('0'), 'D')))
    # step
    A = '( ( %s /\\ y e. NN0 ) /\\ %s )' % (H, HOLF(DN('y'), 'D'))
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A, f))
    hf = s([], 'simpll', H)
    y = s([], 'simplr', 'y e. NN0')
    hy = s([], 'simpr', HOLF(DN('y'), 'D'))
    pmA, dsA = pmcc(w, A, hf, 'F', 'D')
    ccA = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A)
    d1 = s([ccA, pmA, y, w.inst('dvnp1')], 'syl3anc', '%s = ( CC _D %s )' % (DN('( y + 1 )'), DN('y')))
    hd = s([hy, w.inst('ef2dvh')], 'syl', HOLF('( CC _D %s )' % DN('y'), 'D'))
    q1 = holeq(w, A, d1, DN('( y + 1 )'), '( CC _D %s )' % DN('y'), 'D')
    st = s([hd, q1], 'mpbird', HOLF(DN('( y + 1 )'), 'D'))
    w.qed([e['0'], e['y'], e['y1'], e['K'], b, st], 'nn0indd', S['kdholdn'])
    return run(w)


if __name__ == '__main__':
    gen_holdn()
