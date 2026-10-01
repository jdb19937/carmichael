"""Sortie v3: the prime-factor set of a coprime product.

pfmul   ( ( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 ) ->
            PF( ( A x. B ) ) = ( PF( A ) u. PF( B ) ) )
pfdisj  ( ( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 ) ->
            ( PF( A ) i^i PF( B ) ) = (/) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst
from cl import lift

ANTE = '( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 )'


def PQ(X):
    return '{ q e. Prime | q || %s }' % X


def pfmul():
    w = WS('pfmul', 'The prime divisors of a product of coprime positive integers are the '
                    'union of the prime divisors of the factors.')
    st = mkst(w, ANTE)
    az = st([st([], 'simp1', 'A e. NN')], 'nnzd', 'A e. ZZ')
    bz = st([st([], 'simp2', 'B e. NN')], 'nnzd', 'B e. ZZ')
    AQ = '( %s /\\ q e. Prime )' % ANTE
    sq = mkst(w, AQ)
    qp = sq([], 'simpr', 'q e. Prime')
    eu = sq([qp, lift(w, az, AQ), lift(w, bz, AQ), w.inst('euclemma')], 'syl3anc',
            '( q || ( A x. B ) <-> ( q || A \\/ q || B ) )')
    rb = st([eu], 'rabbidva', '%s = { q e. Prime | ( q || A \\/ q || B ) }' % PQ('( A x. B )'))
    ur = st([w.s([], 'unrab',
                 '( %s u. %s ) = { q e. Prime | ( q || A \\/ q || B ) }' % (PQ('A'), PQ('B')))],
            'a1i', '( %s u. %s ) = { q e. Prime | ( q || A \\/ q || B ) }' % (PQ('A'), PQ('B')))
    w.qed([rb, ur], 'eqtr4d',
          '( %s -> %s = ( %s u. %s ) )' % (ANTE, PQ('( A x. B )'), PQ('A'), PQ('B')))
    return w


def pfdisj():
    w = WS('pfdisj', 'Coprime positive integers have no common prime divisor.')
    st = mkst(w, ANTE)
    az = st([st([], 'simp1', 'A e. NN')], 'nnzd', 'A e. ZZ')
    bz = st([st([], 'simp2', 'B e. NN')], 'nnzd', 'B e. ZZ')
    gcd1 = st([], 'simp3', '( A gcd B ) = 1')
    AQ = '( %s /\\ q e. Prime )' % ANTE
    sq = mkst(w, AQ)
    qp = sq([], 'simpr', 'q e. Prime')
    qz = sq([sq([qp, w.inst('prmnn')], 'syl', 'q e. NN')], 'nnzd', 'q e. ZZ')
    dg = sq([qz, lift(w, az, AQ), lift(w, bz, AQ), w.inst('dvdsgcdb')], 'syl3anc',
            '( ( q || A /\\ q || B ) <-> q || ( A gcd B ) )')
    g1 = sq([lift(w, gcd1, AQ)], 'breq2d', '( q || ( A gcd B ) <-> q || 1 )')
    dg2 = sq([dg, g1], 'bitrd', '( ( q || A /\\ q || B ) <-> q || 1 )')
    nd = sq([qp, w.inst('nprmdvds1')], 'syl', '-. q || 1')
    neg = sq([dg2, nd], 'mtbird', '-. ( q || A /\\ q || B )')
    ral = st([neg], 'ralrimiva', 'A. q e. Prime -. ( q || A /\\ q || B )')
    re0 = st([st([w.s([], 'rabeq0',
                      '( { q e. Prime | ( q || A /\\ q || B ) } = (/) <-> '
                      'A. q e. Prime -. ( q || A /\\ q || B ) )')], 'a1i',
                 '( { q e. Prime | ( q || A /\\ q || B ) } = (/) <-> '
                 'A. q e. Prime -. ( q || A /\\ q || B ) )'), ral], 'mpbird',
             '{ q e. Prime | ( q || A /\\ q || B ) } = (/)')
    ir = st([w.s([], 'inrab',
                 '( %s i^i %s ) = { q e. Prime | ( q || A /\\ q || B ) }' % (PQ('A'), PQ('B')))],
            'a1i', '( %s i^i %s ) = { q e. Prime | ( q || A /\\ q || B ) }' % (PQ('A'), PQ('B')))
    w.qed([ir, re0], 'eqtrd',
          '( %s -> ( %s i^i %s ) = (/) )' % (ANTE, PQ('A'), PQ('B')))
    return w


ALL = {'pfmul': pfmul, 'pfdisj': pfdisj}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
