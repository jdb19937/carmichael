"""Sortie C10: the union bound for a finite sum of nonnegative terms (fsumunle)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from c0lib import hyp
from c10_freeze import S as FS, FSUH


def gen_fsumunle():
    w = W('fsumunle', 'A finite sum of nonnegative terms over a subset of ` B u. C ` is at most the sum over ` B ` plus the sum over ` C ` .')
    h = [hyp(w, str(i + 1), 'fsumunle.%d' % (i + 1), f) for i, f in enumerate(FSUH)]
    ph = 'ph'
    s = lambda hs, r, f: w.s(hs, r, '( ph -> %s )' % f)
    U = '( B u. C )'
    D = '( C \\ B )'
    uf = s([h[0], h[1]], 'unfid', '%s e. Fin' % U)
    s1 = s([uf, h[3], h[4], h[2]], 'fsumless', 'sum_ k e. A X <_ sum_ k e. %s X' % U)
    un = s([w.s([], 'undif2', '( B u. %s ) = %s' % (D, U))], 'a1i', '( B u. %s ) = %s' % (D, U))
    un = s([un], 'eqcomd', '%s = ( B u. %s )' % (U, D))
    dj = s([w.s([], 'disjdif', '( B i^i %s ) = (/)' % D)], 'a1i', '( B i^i %s ) = (/)' % D)
    Ak = '( ph /\\ k e. %s )' % U
    xc = w.s([h[3]], 'recnd', '( %s -> X e. CC )' % Ak)
    sp = s([dj, un, uf, xc], 'fsumsplit', 'sum_ k e. %s X = ( sum_ k e. B X + sum_ k e. %s X )' % (U, D))
    ds = s([w.s([], 'difss', '%s C_ C' % D)], 'a1i', '%s C_ C' % D)
    # terms on C
    Ac = '( ph /\\ k e. C )'
    cu = w.s([w.s([w.s([], 'ssun2', 'C C_ %s' % U)], 'a1i', '( %s -> C C_ %s )' % (Ac, U)), w.s([], 'simpr', '( %s -> k e. C )' % Ac)], 'sseldd', '( %s -> k e. %s )' % (Ac, U))
    xr = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % Ac), cu], 'jca', '( %s -> ( ph /\\ k e. %s ) )' % (Ac, U)), h[3]], 'syl', '( %s -> X e. RR )' % Ac)
    x0 = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % Ac), cu], 'jca', '( %s -> ( ph /\\ k e. %s ) )' % (Ac, U)), h[4]], 'syl', '( %s -> 0 <_ X )' % Ac)
    s2 = s([h[1], xr, x0, ds], 'fsumless', 'sum_ k e. %s X <_ sum_ k e. C X' % D)
    def term(S_, ss):
        As = '( ph /\\ k e. %s )' % S_
        ku = w.s([w.s([ss], 'adantr', '( %s -> %s C_ %s )' % (As, S_, U)), w.s([], 'simpr', '( %s -> k e. %s )' % (As, S_))], 'sseldd', '( %s -> k e. %s )' % (As, U))
        pk = w.s([w.s([], 'simpl', '( %s -> ph )' % As), ku], 'jca', '( %s -> ( ph /\\ k e. %s ) )' % (As, U))
        return w.s([pk, h[3]], 'syl', '( %s -> X e. RR )' % As)
    af = s([uf, h[2]], 'ssfid', 'A e. Fin')
    df_ = s([h[1], ds], 'ssfid', '%s e. Fin' % D)
    sAr = s([af, term('A', h[2])], 'fsumrecl', 'sum_ k e. A X e. RR')
    bU = s([w.s([], 'ssun1', 'B C_ %s' % U)], 'a1i', 'B C_ %s' % U)
    sBr = s([h[0], term('B', bU)], 'fsumrecl', 'sum_ k e. B X e. RR')
    dU = s([ds, s([w.s([], 'ssun2', 'C C_ %s' % U)], 'a1i', 'C C_ %s' % U)], 'sstrd', '%s C_ %s' % (D, U))
    sDr = s([df_, term(D, dU)], 'fsumrecl', 'sum_ k e. %s X e. RR' % D)
    sCr = s([h[1], xr], 'fsumrecl', 'sum_ k e. C X e. RR')
    sUr = s([uf, h[3]], 'fsumrecl', 'sum_ k e. %s X e. RR' % U)
    lv = {'sum_ k e. A X': sAr, 'sum_ k e. B X': sBr, 'sum_ k e. %s X' % D: sDr, 'sum_ k e. C X': sCr, 'sum_ k e. %s X' % U: sUr}
    goal = FS['fsumunle']
    lin8(w, 'ph', [s1, sp, s2], goal[len('( ph -> '):-2], lv)
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]
    return run8(w)


if __name__ == '__main__':
    gen_fsumunle()
