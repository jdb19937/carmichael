"""Sortie KD1: arithmetic of the frozen parameters Ndet, Mdet, Xone, Xtwo (kdndet, kdxlt)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from lin import linarith, nlinarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_ndet():
    w = W('kdndet', 'Lean ` six_le_Ndet ` , ` Ndet_pos ` , ` le_Ndet_cast ` , ` Ndet_cast_lt ` for ` Ndet = |^ ( 6 + 840000000 eta L ) ` (Lean ` 28800000 ` ; ZC1 ` sdzc ` : ` 70000000 . 6 . 2 ` ).')
    A0 = '( ( E e. RR /\\ 0 <_ E ) /\\ ( L e. RR /\\ 0 <_ L ) )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    er = s([], 'simpll', 'E e. RR'); e0 = s([], 'simplr', '0 <_ E'); lr = s([], 'simprl', 'L e. RR'); l0 = s([], 'simprr', '0 <_ L')
    X = '( 6 + ( ( %s x. E ) x. L ) )' % CNDET
    c = Closure(w, A0, {'E': ('RR', er), 'L': ('RR', lr)})
    xr = c.mem(X, 'RR')
    CE = '( %s x. E )' % CNDET
    ce0 = s([c.mem(CNDET, 'RR'), er, c.ge0(CNDET) if False else linarith(w, A0, [], '0 <_ %s' % CNDET, closure=c), e0], 'mulge0d', '0 <_ %s' % CE)
    cel0 = s([c.mem(CE, 'RR'), lr, ce0, l0], 'mulge0d', '0 <_ ( %s x. L )' % CE)
    c.leaf('( %s x. L )' % CE, 'RR', c.mem('( %s x. L )' % CE, 'RR')); c.atom('( %s x. L )' % CE)
    N = NDET()
    zz = s([xr, w.inst('ceilcl')], 'syl', '%s e. ZZ' % N)
    ge = s([xr, w.inst('ceilge')], 'syl', '%s <_ %s' % (X, N))
    lt = s([xr, w.inst('ceilm1lt')], 'syl', '( %s - 1 ) < %s' % (N, X))
    c.leaf(N, 'RR', s([zz], 'zred', '%s e. RR' % N)); c.atom(N)
    six = linarith(w, A0, [ge, cel0], '6 <_ %s' % N, closure=c)
    one = linarith(w, A0, [six], '1 <_ %s' % N, closure=c)
    nn = s([s([zz, one], 'jca', '( %s e. ZZ /\\ 1 <_ %s )' % (N, N)), w.s([], 'elnnz1', '( %s e. NN <-> ( %s e. ZZ /\\ 1 <_ %s ) )' % (N, N, N))], 'sylibr', '%s e. NN' % N)
    lt7 = linarith(w, A0, [lt], '%s < ( 7 + ( ( %s x. E ) x. L ) )' % (N, CNDET), closure=c)
    w.qed([nn, six, s([ge, lt7], 'jca', '( %s <_ %s /\\ %s < ( 7 + ( ( %s x. E ) x. L ) ) )' % (X, N, N, CNDET))], '3jca', S['kdndet'])
    return run(w)


def gen_xlt():
    w = W('kdxlt', 'Lean ` Mdet_pos ` , ` Xone_lt_Xtwo ` : ` Mdet = 6 Ndet e. NN ` and ` exp ( Mdet / ( 16 eta ) ) < exp ( 16 Mdet / eta ) ` .')
    A0 = '( E e. RR+ /\\ L e. RR /\\ 0 <_ L )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ep = s([], 'simp1', 'E e. RR+'); lr = s([], 'simp2', 'L e. RR'); l0 = s([], 'simp3', '0 <_ L')
    er = s([ep], 'rpred', 'E e. RR'); e0 = s([s([ep], 'rpgt0d', '0 < E'), er] and [w.s([], '0red', '( %s -> 0 e. RR )' % A0), er, s([ep], 'rpgt0d', '0 < E')], 'ltled', '0 <_ E')
    nd = s([s([s([er, e0], 'jca', '( E e. RR /\\ 0 <_ E )'), s([lr, l0], 'jca', '( L e. RR /\\ 0 <_ L )')], 'jca', '( ( E e. RR /\\ 0 <_ E ) /\\ ( L e. RR /\\ 0 <_ L ) )'), w.inst('kdndet')], 'syl',
           S['kdndet'].split(' -> ', 1)[1][:-2])
    N = NDET(); M = MDET()
    nn = s([nd], 'simp1d', '%s e. NN' % N)
    mn = s([w.s([w.s([], '6nn', '6 e. NN')], 'a1i', '( %s -> 6 e. NN )' % A0), nn], 'nnmulcld', '%s e. NN' % M)
    mp = s([mn], 'nnrpd', '%s e. RR+' % M)
    X1 = '( %s / ( ; 1 6 x. E ) )' % M; X2 = '( ( ; 1 6 x. %s ) / E )' % M
    c = Closure(w, A0, {'E': ('RR', er), M: ('RR', s([mp], 'rpred', '%s e. RR' % M))})
    c.have('E', 'gt0', s([ep], 'rpgt0d', '0 < E')); c.have(M, 'gt0', s([mp], 'rpgt0d', '0 < %s' % M))
    c.atom(M)
    # X1 < X2  <=>  M / ( 16 E ) < 16 M / E ; X1 = ( M / E ) / 16 , X2 = 16 ( M / E )
    ME = '( %s / E )' % M
    mep = s([mp, ep], 'rpdivcld', '%s e. RR+' % ME)
    x1a = s([s([mp], 'rpcnd', '%s e. CC' % M), s([ep], 'rpcnd', 'E e. CC'), c.mem('; 1 6', 'CC'), s([ep], 'rpne0d', 'E =/= 0'), c.ne0('; 1 6')], 'divdiv1d', '( ( %s / E ) / ; 1 6 ) = ( %s / ( E x. ; 1 6 ) )' % (M, M))
    x1b = s([x1a, s([s([s([ep], 'rpcnd', 'E e. CC'), c.mem('; 1 6', 'CC')], 'mulcomd', '( E x. ; 1 6 ) = ( ; 1 6 x. E )')], 'oveq2d', '( %s / ( E x. ; 1 6 ) ) = %s' % (M, X1))], 'eqtrd', '( ( %s / E ) / ; 1 6 ) = %s' % (M, X1))
    x2a = s([c.mem('; 1 6', 'CC'), s([mp], 'rpcnd', '%s e. CC' % M), s([ep], 'rpcnd', 'E e. CC'), s([ep], 'rpne0d', 'E =/= 0')], 'divassd', '%s = ( ; 1 6 x. ( %s / E ) )' % (X2, M))
    c.leaf(ME, 'RR', s([mep], 'rpred', '%s e. RR' % ME)); c.atom(ME); c.have(ME, 'gt0', s([mep], 'rpgt0d', '0 < %s' % ME))
    cmp = linarith(w, A0, [s([mep], 'rpgt0d', '0 < %s' % ME)], '( %s / ; 1 6 ) < ( ; 1 6 x. %s )' % (ME, ME), closure=c)
    lt = s([s([x1b, cmp], 'eqbrtrrd', '%s < ( ; 1 6 x. %s )' % (X1, ME)), x2a], 'breqtrrd', '%s < %s' % (X1, X2))
    x1r = s([s([mp], 'rpred', '%s e. RR' % M), c.mem('( ; 1 6 x. E )', 'RR+')], 'rerpdivcld', '%s e. RR' % X1)
    x2r = s([c.mem('( ; 1 6 x. %s )' % M, 'RR'), ep], 'rerpdivcld', '%s e. RR' % X2)
    ex = s([x1r, x2r, w.inst('eflt')], 'syl2anc', '( %s < %s <-> ( exp ` %s ) < ( exp ` %s ) )' % (X1, X2, X1, X2))
    w.qed([mn, s([lt, ex], 'mpbid', '( exp ` %s ) < ( exp ` %s )' % (X1, X2))], 'jca', S['kdxlt'])
    return run(w)


if __name__ == '__main__':
    gen_ndet()
    gen_xlt()
