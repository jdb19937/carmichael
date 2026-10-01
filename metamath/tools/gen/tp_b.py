"""Sortie TP: the endgame numerics (tpend, Lean endgame_bound with 1/8 in place of 4/7 after the 32/7)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tplib import *

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


K = '( N - 1 )'; SS = '( M + N )'; M1 = '( M + 1 )'; E1 = '( exp ` 1 )'
DEX = '( %s / %s )' % (K, SS)
S['tpend'] = ('( ( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ D = %s ) -> '
              '( ( ( ( 1 / ( 1 - D ) ) ^ %s ) x. ( ( 8 / D ) ^ %s ) ) x. %s ) <_ ( 1 / 8 ) )') % (DEX, M1, K, CN())


def gen_end():
    w = W('tpend', 'Lean ` endgame_bound ` in the form the square contour consumes: with ` D = ( N - 1 ) / ( M + N ) ` , '
               '` ( 1 / ( 1 - D ) ) ^ ( M + 1 ) ( 8 / D ) ^ ( N - 1 ) ( N / ( 8 e ( M + N ) ) ) ^ N <_ 1 / 8 ` .')
    A = '( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ D = %s )' % DEX
    s = lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)
    h3 = s([], 'simpl', '( N e. NN /\\ 2 <_ N /\\ M e. NN0 )')
    nn = s([h3], 'simp1d', 'N e. NN'); n2 = s([h3], 'simp2d', '2 <_ N'); mm = s([h3], 'simp3d', 'M e. NN0')
    dd = s([], 'simpr', 'D = %s' % DEX)
    c = Closure(w, A, {'N': ('NN', nn), 'M': ('NN0', mm)})
    nz = c.mem('N', 'ZZ')
    uz = s([w.s([], '2z', '2 e. ZZ') and s([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), nz, n2], '3jca', '( 2 e. ZZ /\\ N e. ZZ /\\ 2 <_ N )')
    uz2 = s([uz, w.inst('eluz2')], 'sylibr', 'N e. ( ZZ>= ` 2 )')
    kn = s([uz2, w.inst('uz2m1nn')], 'syl', '%s e. NN' % K)
    c.have(K, 'NN', kn)
    pass
    # identities
    sk = ringeq_(w, A, '( %s - %s )' % (SS, K), M1, c)
    e1a = s([dd], 'oveq2d', '( 1 - D ) = ( 1 - ( %s / %s ) )' % (K, SS))
    dv = ap(w, A, 'dividd', '( %s / %s ) = 1' % (SS, SS), c)
    e1b = s([dv], 'oveq1d', '( ( %s / %s ) - ( %s / %s ) ) = ( 1 - ( %s / %s ) )' % (SS, SS, K, SS, K, SS))
    e1c = ap(w, A, 'divsubdird', '( ( %s - %s ) / %s ) = ( ( %s / %s ) - ( %s / %s ) )' % (SS, K, SS, SS, SS, K, SS), c)
    e1d = s([sk], 'oveq1d', '( ( %s - %s ) / %s ) = ( %s / %s )' % (SS, K, SS, M1, SS))
    e1e = s([e1c, e1b], 'eqtrd', '( ( %s - %s ) / %s ) = ( 1 - ( %s / %s ) )' % (SS, K, SS, K, SS))
    e1f = s([e1a, e1e], 'eqtr4d', '( 1 - D ) = ( ( %s - %s ) / %s )' % (SS, K, SS))
    id1 = s([e1f, e1d], 'eqtrd', '( 1 - D ) = ( %s / %s )' % (M1, SS))
    e2a = s([id1], 'oveq2d', '( 1 / ( 1 - D ) ) = ( 1 / ( %s / %s ) )' % (M1, SS))
    e2b = ap(w, A, 'recdivd', '( 1 / ( %s / %s ) ) = ( %s / %s )' % (M1, SS, SS, M1), c)
    id2 = s([e2a, e2b], 'eqtrd', '( 1 / ( 1 - D ) ) = ( %s / %s )' % (SS, M1))
    sm = ringeq_(w, A, SS, '( %s + %s )' % (M1, K), c)
    e3a = s([sm], 'oveq1d', '( %s / %s ) = ( ( %s + %s ) / %s )' % (SS, M1, M1, K, M1))
    e3b = ap(w, A, 'divdird', '( ( %s + %s ) / %s ) = ( ( %s / %s ) + ( %s / %s ) )' % (M1, K, M1, M1, M1, K, M1), c)
    e3c = s([ap(w, A, 'dividd', '( %s / %s ) = 1' % (M1, M1), c)], 'oveq1d',
            '( ( %s / %s ) + ( %s / %s ) ) = ( 1 + ( %s / %s ) )' % (M1, M1, K, M1, K, M1))
    id3 = s([e3a, e3b, e3c], '3eqtrd', '( %s / %s ) = ( 1 + ( %s / %s ) )' % (SS, M1, K, M1))
    A1 = '( 1 + ( %s / %s ) )' % (K, M1)
    idA = s([id2, id3], 'eqtrd', '( 1 / ( 1 - D ) ) = %s' % A1)
    V = '( ( 8 x. %s ) / %s )' % (SS, K)
    e4a = s([dd], 'oveq2d', '( 8 / D ) = ( 8 / %s )' % DEX)
    e4b = ap(w, A, 'divdiv2d', '( 8 / %s ) = %s' % (DEX, V), c)
    id4 = s([e4a, e4b], 'eqtrd', '( 8 / D ) = %s' % V)
    U = '( N / ( ( 8 x. %s ) x. %s ) )' % (E1, SS)
    np1 = ap(w, A, 'npcand', '( %s + 1 ) = N' % K, c)
    e5a = s([np1], 'oveq2d', '( %s ^ ( %s + 1 ) ) = ( %s ^ N )' % (U, K, U))
    e5b = ap(w, A, 'expp1d', '( %s ^ ( %s + 1 ) ) = ( ( %s ^ %s ) x. %s )' % (U, K, U, K, U), c)
    id5 = s([e5a, e5b], 'eqtr3d', '%s = ( ( %s ^ %s ) x. %s )' % (CN(), U, K, U))
    BB = '( N / %s )' % K
    e6a = ap(w, A, 'divmuldivd', '( %s x. %s ) = ( ( N x. ( 8 x. %s ) ) / ( ( ( 8 x. %s ) x. %s ) x. %s ) )' % (U, V, SS, E1, SS, K), c)
    r1 = ringeq_(w, A, '( N x. ( 8 x. %s ) )' % SS, '( ( 8 x. %s ) x. N )' % SS, c)
    r2 = ringeq_(w, A, '( ( ( 8 x. %s ) x. %s ) x. %s )' % (E1, SS, K), '( ( 8 x. %s ) x. ( %s x. %s ) )' % (SS, K, E1), c)
    e6b = s([r1, r2], 'oveq12d', '( ( N x. ( 8 x. %s ) ) / ( ( ( 8 x. %s ) x. %s ) x. %s ) ) = ( ( ( 8 x. %s ) x. N ) / ( ( 8 x. %s ) x. ( %s x. %s ) ) )'
            % (SS, E1, SS, K, SS, SS, K, E1))
    e6c = ap(w, A, 'divcan5d', '( ( ( 8 x. %s ) x. N ) / ( ( 8 x. %s ) x. ( %s x. %s ) ) ) = ( N / ( %s x. %s ) )' % (SS, SS, K, E1, K, E1), c)
    e6d = ap(w, A, 'divdiv1d', '( %s / %s ) = ( N / ( %s x. %s ) )' % (BB, E1, K, E1), c)
    id6 = s([e6a, e6b, e6c], '3eqtrd', '( %s x. %s ) = ( N / ( %s x. %s ) )' % (U, V, K, E1))
    id6 = s([id6, e6d], 'eqtr4d', '( %s x. %s ) = ( %s / %s )' % (U, V, BB, E1))
    kz = c.mem(K, 'NN0')
    e7a = ap(w, A, 'mulexpd', '( ( %s x. %s ) ^ %s ) = ( ( %s ^ %s ) x. ( %s ^ %s ) )' % (V, U, K, V, K, U, K), c)
    e7b = s([s([ap(w, A, 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (V, U, U, V), c), id6], 'eqtrd',
                '( %s x. %s ) = ( %s / %s )' % (V, U, BB, E1))], 'oveq1d', '( ( %s x. %s ) ^ %s ) = ( ( %s / %s ) ^ %s )' % (V, U, K, BB, E1, K))
    e7c = ap(w, A, 'expdivd', '( ( %s / %s ) ^ %s ) = ( ( %s ^ %s ) / ( %s ^ %s ) )' % (BB, E1, K, BB, K, E1, K), c)
    EK = '( exp ` %s )' % K
    e8 = apc(w, A, 'efexp', '( exp ` ( %s x. 1 ) ) = ( %s ^ %s )' % (K, E1, K), c)
    e8b = s([ap(w, A, 'mulridd', '( %s x. 1 ) = %s' % (K, K), c)], 'fveq2d', '( exp ` ( %s x. 1 ) ) = %s' % (K, EK))
    id8 = s([e8, e8b], 'eqtr3d', '( %s ^ %s ) = %s' % (E1, K, EK))
    e7d = s([id8], 'oveq2d', '( ( %s ^ %s ) / ( %s ^ %s ) ) = ( ( %s ^ %s ) / %s )' % (BB, K, E1, K, BB, K, EK))
    id7 = s([e7a, e7b, e7c], '3eqtr3d', '( ( %s ^ %s ) x. ( %s ^ %s ) ) = ( ( %s ^ %s ) / ( %s ^ %s ) )' % (V, K, U, K, BB, K, E1, K))
    id7 = s([id7, e7d], 'eqtrd', '( ( %s ^ %s ) x. ( %s ^ %s ) ) = ( ( %s ^ %s ) / %s )' % (V, K, U, K, BB, K, EK))
    # N / K = 1 + 1 / K
    e9a = s([np1], 'oveq1d', '( ( %s + 1 ) / %s ) = ( N / %s )' % (K, K, K))
    e9b = ap(w, A, 'divdird', '( ( %s + 1 ) / %s ) = ( ( %s / %s ) + ( 1 / %s ) )' % (K, K, K, K, K), c)
    e9c = s([ap(w, A, 'dividd', '( %s / %s ) = 1' % (K, K), c)], 'oveq1d', '( ( %s / %s ) + ( 1 / %s ) ) = ( 1 + ( 1 / %s ) )' % (K, K, K, K))
    id9 = s([e9a, e9b, e9c], '3eqtr3d', '( N / %s ) = ( 1 + ( 1 / %s ) )' % (K, K))
    # inequalities (1 + x / m) ^ m <_ exp x
    def onep(x, m, target, prod_eq):
        """( 1 + ( x / m ) ) ^ m <_ exp target, where m ( x / m ) = target"""
        q = '( %s / %s )' % (x, m)
        g1 = apc(w, A, 'bvefge1p', '( 1 + %s ) <_ ( exp ` %s )' % (q, q), c)
        mz = c.mem(m, 'NN0')
        g2 = ap(w, A, 'leexp1ad', '( ( 1 + %s ) ^ %s ) <_ ( ( exp ` %s ) ^ %s )' % (q, m, q, m), c)
        g3 = apc(w, A, 'efexp', '( exp ` ( %s x. %s ) ) = ( ( exp ` %s ) ^ %s )' % (m, q, q, m), c)
        g4 = s([prod_eq], 'fveq2d', '( exp ` ( %s x. %s ) ) = ( exp ` %s )' % (m, q, target))
        g5 = s([g3, g4], 'eqtr3d', '( ( exp ` %s ) ^ %s ) = ( exp ` %s )' % (q, m, target))
        return s([g2, g5], 'breqtrd', '( ( 1 + %s ) ^ %s ) <_ ( exp ` %s )' % (q, m, target))
    c.have(M1, 'NN', c.mem(M1, 'NN'))
    ie1 = onep(K, M1, K, ap(w, A, 'divcan2d', '( %s x. ( %s / %s ) ) = %s' % (M1, K, M1, K), c))
    ie2 = onep('1', K, '1', ap(w, A, 'divcan2d', '( %s x. ( 1 / %s ) ) = 1' % (K, K), c))
    # assemble
    X1 = '( ( 1 / ( 1 - D ) ) ^ %s )' % M1; XV = '( ( 8 / D ) ^ %s )' % K
    a1 = '( %s ^ %s )' % (A1, M1); bK = '( ( 1 + ( 1 / %s ) ) ^ %s )' % (K, K)
    vK = '( %s ^ %s )' % (V, K); uK = '( %s ^ %s )' % (U, K)
    x1 = s([idA], 'oveq1d', '%s = %s' % (X1, a1))
    xv = s([id4], 'oveq1d', '%s = %s' % (XV, vK))
    L0 = '( ( %s x. %s ) x. %s )' % (X1, XV, CN())
    L1 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (a1, vK, uK, U)
    l01 = s([s([x1, xv], 'oveq12d', '( %s x. %s ) = ( %s x. %s )' % (X1, XV, a1, vK)), id5], 'oveq12d', '%s = %s' % (L0, L1))
    for t in (a1, vK, uK, U):
        c.atom(t)
    L2 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (U, a1, vK, uK)
    l12 = ringeq_(w, A, L1, L2, c)
    bKe = '( ( %s ^ %s ) / %s )' % (BB, K, EK)
    bK2 = s([s([id9], 'oveq1d', '( %s ^ %s ) = %s' % (BB, K, bK))], 'oveq1d', '%s = ( %s / %s )' % (bKe, bK, EK))
    L3 = '( ( %s x. %s ) x. ( %s / %s ) )' % (U, a1, bK, EK)
    l23 = s([id7, bK2], 'eqtrd', '( %s x. %s ) = ( %s / %s )' % (vK, uK, bK, EK))
    l23 = s([l23], 'oveq2d', '%s = %s' % (L2, L3))
    lchain = s([l01, l12, l23], '3eqtrd', '%s = %s' % (L0, L3))
    # L3 <_ ( U x. EK ) x. ( E1 / EK )
    c.atom(bK); c.atom(EK)
    ug = c.ge0(U)
    q1 = ap(w, A, 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (U, a1, U, EK), c, facts=[ie1])
    ekp = c.mem(EK, 'RR+')
    q2 = ap(w, A, 'lediv1dd', '( %s / %s ) <_ ( %s / %s )' % (bK, EK, E1, EK), c, facts=[ie2])
    q3 = ap(w, A, 'lemul12ad', '%s <_ ( ( %s x. %s ) x. ( %s / %s ) )' % (L3, U, EK, E1, EK), c, facts=[q1, q2])
    f1 = ap(w, A, 'mulassd', '( ( %s x. %s ) x. ( %s / %s ) ) = ( %s x. ( %s x. ( %s / %s ) ) )' % (U, EK, E1, EK, U, EK, E1, EK), c)
    f2 = s([ap(w, A, 'divcan2d', '( %s x. ( %s / %s ) ) = %s' % (EK, E1, EK, E1), c)], 'oveq2d',
           '( %s x. ( %s x. ( %s / %s ) ) ) = ( %s x. %s )' % (U, EK, E1, EK, U, E1))
    # U x. E1 = N / ( 8 x. S )
    NE = '( N / %s )' % E1
    f3a = s([ringeq_(w, A, '( ( 8 x. %s ) x. %s )' % (E1, SS), '( %s x. ( 8 x. %s ) )' % (E1, SS), c)], 'oveq2d',
            '%s = ( N / ( %s x. ( 8 x. %s ) ) )' % (U, E1, SS))
    f3b = ap(w, A, 'divdiv1d', '( %s / ( 8 x. %s ) ) = ( N / ( %s x. ( 8 x. %s ) ) )' % (NE, SS, E1, SS), c)
    f3c = s([f3a, f3b], 'eqtr4d', '%s = ( %s / ( 8 x. %s ) )' % (U, NE, SS))
    f3d = s([f3c], 'oveq1d', '( %s x. %s ) = ( ( %s / ( 8 x. %s ) ) x. %s )' % (U, E1, NE, SS, E1))
    f3e = ap(w, A, 'div23d', '( ( %s x. %s ) / ( 8 x. %s ) ) = ( ( %s / ( 8 x. %s ) ) x. %s )' % (NE, E1, SS, NE, SS, E1), c)
    f3f = s([ap(w, A, 'divcan1d', '( %s x. %s ) = N' % (NE, E1), c)], 'oveq1d',
            '( ( %s x. %s ) / ( 8 x. %s ) ) = ( N / ( 8 x. %s ) )' % (NE, E1, SS, SS))
    f3 = s([f3d, f3e], 'eqtr4d', '( %s x. %s ) = ( ( %s x. %s ) / ( 8 x. %s ) )' % (U, E1, NE, E1, SS))
    f3 = s([f3, f3f], 'eqtrd', '( %s x. %s ) = ( N / ( 8 x. %s ) )' % (U, E1, SS))
    fin = s([f1, f2, f3], '3eqtrd', '( ( %s x. %s ) x. ( %s / %s ) ) = ( N / ( 8 x. %s ) )' % (U, EK, E1, EK, SS))
    q4 = s([q3, fin], 'breqtrd', '%s <_ ( N / ( 8 x. %s ) )' % (L3, SS))
    # N / ( 8 S ) <_ 1 / 8
    n8 = lin.linarith(w, A, [c.ge0('M')], 'N <_ ( ( 1 / 8 ) x. ( 8 x. %s ) )' % SS, closure=c)
    q5 = ap(w, A, 'ledivmul2d', '( ( N / ( 8 x. %s ) ) <_ ( 1 / 8 ) <-> N <_ ( ( 1 / 8 ) x. ( 8 x. %s ) ) )' % (SS, SS), c)
    q5 = s([n8, q5], 'mpbird', '( N / ( 8 x. %s ) ) <_ ( 1 / 8 )' % SS)
    q6 = s([q4, q5], 'letrd', '%s <_ ( 1 / 8 )' % L3)
    w.qed([lchain, q6], 'eqbrtrd', S['tpend'])
    return run(w)


def ringeq_(w, A, lhs, rhs, c):
    import mvlib
    return mvlib.ringeq(w, A, lhs, rhs, c)


if __name__ == '__main__':
    gen_end()
