"""Sortie TP: x ^ k <_ k! e ^ x (tppowfac) and N ^ N <_ N! e ^ N (tppowself)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tplib import *

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_powfac():
    w = W('tppowfac', 'Lean ` KDerivDetect.pow_le_factorial_mul_exp ` : ` x ^ k <_ k ! e ^ x ` for ` 0 <_ x ` (one term of the exponential series).')
    A = '( X e. RR /\\ 0 <_ X /\\ K e. NN0 )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A, f))
    x = s([], 'simp1', 'X e. RR'); x0 = s([], 'simp2', '0 <_ X'); kk = s([], 'simp3', 'K e. NN0')
    c = Closure(w, A, {'X': ('RR', x), 'K': ('NN0', kk)})
    c.have('X', 'ge0', x0)
    xc = c.mem('X', 'CC')
    F = '( n e. NN0 |-> ( ( X ^ n ) / ( ! ` n ) ) )'
    fe = w.s([], 'eqid', '%s = %s' % (F, F))
    cv0 = w.s([fe], 'efcvg', '( X e. CC -> seq 0 ( + , %s ) ~~> ( exp ` X ) )' % F)
    cv = w.s([xc, cv0], 'syl', '( %s -> seq 0 ( + , %s ) ~~> ( exp ` X ) )' % (A, F))
    rl = w.s([], 'climrel', 'Rel ~~>')
    dm0 = w.s([rl], 'releldmi', '( seq 0 ( + , %s ) ~~> ( exp ` X ) -> seq 0 ( + , %s ) e. dom ~~> )' % (F, F))
    dm = w.s([cv, dm0], 'syl', '( %s -> seq 0 ( + , %s ) e. dom ~~> )' % (A, F))
    B = '( ( X ^ k ) / ( ! ` k ) )'
    Ak = '( %s /\\ k e. NN0 )' % A
    ck = Closure(w, Ak, {'X': ('RR', w.s([x], 'adantr', '( %s -> X e. RR )' % Ak)),
                         'k': ('NN0', w.s([], 'simpr', '( %s -> k e. NN0 )' % Ak))})
    ck.have('X', 'ge0', w.s([x0], 'adantr', '( %s -> 0 <_ X )' % Ak))
    tv0 = w.s([fe], 'eftval', '( k e. NN0 -> ( %s ` k ) = %s )' % (F, B))
    tv = w.s([tv0], 'adantl', '( %s -> ( %s ` k ) = %s )' % (Ak, F, B))
    ck.have('( ! ` k )', 'NN', w.s([ck.mem('k', 'NN0'), w.inst('faccl')], 'syl', '( %s -> ( ! ` k ) e. NN )' % Ak))
    br = ck.mem(B, 'RR'); bg = ck.ge0(B)
    uz = w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')
    z0 = w.s([w.s([], '0z', '0 e. ZZ')], 'a1i', '( %s -> 0 e. ZZ )' % A)
    fi = w.s([w.s([], 'snfi', '{ K } e. Fin')], 'a1i', '( %s -> { K } e. Fin )' % A)
    ss = s([kk], 'snssd', '{ K } C_ NN0')
    le = s([uz, z0, fi, ss, tv, br, bg, dm], 'isumless', 'sum_ k e. { K } %s <_ sum_ k e. NN0 %s' % (B, B))
    BK = '( ( X ^ K ) / ( ! ` K ) )'
    # ( k = K -> B = BK )
    e1 = w.s([], 'oveq2', '( k = K -> ( X ^ k ) = ( X ^ K ) )')
    e2 = w.s([], 'fveq2', '( k = K -> ( ! ` k ) = ( ! ` K ) )')
    e3 = w.s([e1, e2], 'oveq12d', '( k = K -> %s = %s )' % (B, BK))
    c.have('( ! ` K )', 'NN', s([kk, w.inst('faccl')], 'syl', '( ! ` K ) e. NN'))
    bkc = c.mem(BK, 'CC')
    sn0 = w.s([e3], 'sumsn', '( ( K e. NN0 /\\ %s e. CC ) -> sum_ k e. { K } %s = %s )' % (BK, B, BK))
    sn = s([kk, bkc, sn0], 'syl2anc', 'sum_ k e. { K } %s = %s' % (B, BK))
    ev = s([xc, w.inst('efval')], 'syl', '( exp ` X ) = sum_ k e. NN0 %s' % B)
    le1 = s([sn, le], 'eqbrtrrd', '%s <_ sum_ k e. NN0 %s' % (BK, B))
    le2 = s([le1, ev], 'breqtrrd', '%s <_ ( exp ` X )' % BK)
    fr = c.mem('( ! ` K )', 'RR'); fp = c.gt0('( ! ` K )')
    xk = c.mem('( X ^ K )', 'RR'); er = c.mem('( exp ` X )', 'RR')
    bi = s([xk, er, fr, fp, w.inst('ledivmul')], 'syl112anc', '( %s <_ ( exp ` X ) <-> ( X ^ K ) <_ ( ( ! ` K ) x. ( exp ` X ) ) )' % BK)
    w.qed([le2, bi], 'mpbid', S['tppowfac'])
    return run(w)


def gen_powself():
    w = W('tppowself', 'Lean ` pow_self_le_factorial_mul_exp ` : ` N ^ N <_ N ! e ^ N ` .')
    A = 'N e. NN0'
    n = w.s([], 'id', '( N e. NN0 -> N e. NN0 )')
    nr = w.s([n], 'nn0red', '( N e. NN0 -> N e. RR )')
    n0 = w.s([n], 'nn0ge0d', '( N e. NN0 -> 0 <_ N )')
    w.qed([nr, n0, n, w.inst('tppowfac')], 'syl3anc', S['tppowself'])
    return run(w)


if __name__ == '__main__':
    gen_powfac()
    gen_powself()
