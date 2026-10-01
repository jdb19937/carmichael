"""Sortie v4b block 7a: the radical, and the Selberg term of the progression sieve.

radlem   ( J e. NN -> ( ( RAD( J ) e. NN /\\ ( mmu ` RAD( J ) ) =/= 0 ) /\\
             { q e. Prime | q || RAD( J ) } = { u e. Prime | u || J } /\\ RAD( J ) || J ) )
progvgt  ( ( L e. NN /\\ ( mmu ` L ) =/= 0 ) -> GTV( L ) = GTR( L ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import V, PF, RAD, GTV, GTR, mkst

TU = PF('J', 'u')
RJ = RAD('J')
RJP = 'prod_ p e. %s p' % TU
RJJ = 'prod_ j e. %s j' % TU


def radlem():
    w = W('radlem', 'The radical of a positive integer is a squarefree positive integer '
                    'with the same prime divisors, and it divides that integer.')
    ANT = 'J e. NN'
    st = mkst(w, ANT)
    jnn = st([], 'id', 'J e. NN')
    q = st([jnn, w.inst('pffinq')], 'syl', '{ q e. Prime | q || J } e. Fin')
    cb = w.s([w.s([], 'breq1', '( q = u -> ( q || J <-> u || J ) )')], 'cbvrabv',
             '{ q e. Prime | q || J } = %s' % TU)
    tfin = st([st([cb], 'a1i', '{ q e. Prime | q || J } = %s' % TU), q], 'eqeltrrd',
              '%s e. Fin' % TU)
    tss = st([w.s([], 'ssrab2', '%s C_ Prime' % TU)], 'a1i', '%s C_ Prime' % TU)
    sq = st([st([tfin, tss], 'jca', '( %s e. Fin /\\ %s C_ Prime )' % (TU, TU)),
             w.inst('sqfprod')], 'syl',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s )'
            % (RJP, RJP, RJP, TU))
    cbe = st([w.s([w.s([], 'id', '( p = e -> p = e )')], 'cbvprodv', '%s = %s' % (RJP, RJ))],
             'a1i', '%s = %s' % (RJP, RJ))
    p12 = st([sq], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (RJP, RJP))
    n2 = st([cbe, st([p12], 'simpld', '%s e. NN' % RJP)], 'eqeltrrd', '%s e. NN' % RJ)
    m2 = st([st([st([cbe], 'fveq2d', '( mmu ` %s ) = ( mmu ` %s )' % (RJP, RJ))], 'neeq1d',
                '( ( mmu ` %s ) =/= 0 <-> ( mmu ` %s ) =/= 0 )' % (RJP, RJ)),
             st([p12], 'simprd', '( mmu ` %s ) =/= 0' % RJP)], 'mpbid',
            '( mmu ` %s ) =/= 0' % RJ)
    part1 = st([n2, m2], 'jca', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (RJ, RJ))
    bq = st([cbe], 'breq2d', '( q || %s <-> q || %s )' % (RJP, RJ))
    rb = st([bq], 'rabbidv', '{ q e. Prime | q || %s } = { q e. Prime | q || %s }' % (RJP, RJ))
    part2 = st([rb, st([sq], 'simprd', '{ q e. Prime | q || %s } = %s' % (RJP, TU))],
               'eqtr3d', '{ q e. Prime | q || %s } = %s' % (RJ, TU))
    elj = w.s([w.s([], 'breq1', '( u = j -> ( u || J <-> j || J ) )')], 'elrab',
              '( j e. %s <-> ( j e. Prime /\\ j || J ) )' % TU)
    jdv = w.s([w.s([elj], 'biimpi', '( j e. %s -> ( j e. Prime /\\ j || J ) )' % TU)],
              'simprd', '( j e. %s -> j || J )' % TU)
    ral = st([w.s([jdv], 'rgen', 'A. j e. %s j || J' % TU)], 'a1i',
             'A. j e. %s j || J' % TU)
    exd = st([st([tfin, tss], 'jca', '( %s e. Fin /\\ %s C_ Prime )' % (TU, TU)),
              w.inst('extrwprmdvds')], 'syl',
             '( ( J e. ZZ /\\ A. j e. %s j || J ) -> %s || J )' % (TU, RJJ))
    jz = st([jnn], 'nnzd', 'J e. ZZ')
    dv0 = st([exd, st([jz, ral], 'jca',
                      '( J e. ZZ /\\ A. j e. %s j || J )' % TU)], 'mpd', '%s || J' % RJJ)
    cbj = st([w.s([w.s([], 'id', '( j = e -> j = e )')], 'cbvprodv', '%s = %s' % (RJJ, RJ))],
             'a1i', '%s = %s' % (RJJ, RJ))
    part3 = st([cbj, dv0], 'eqbrtrrd', '%s || J' % RJ)
    w.qed([part1, part2, part3], '3jca',
          '( %s -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s /\\ %s || J ) )'
          % (ANT, RJ, RJ, RJ, TU, RJ))
    return w


def progvgt():
    w = W('progvgt', 'The Selberg term of the progression sieve at a squarefree divisor.')
    ANT = '( L e. NN /\\ ( mmu ` L ) =/= 0 )'
    st = mkst(w, ANT)
    vl = st([], 'progvsqf', '( %s ` L ) = ( 1 / L )' % V)
    PFL = PF('L')
    AQ = '( %s /\\ q e. %s )' % (ANT, PFL)
    sq = mkst(w, AQ)
    qel = sq([], 'simpr', 'q e. %s' % PFL)
    qpr = sq([qel, w.inst('elrabi')], 'syl', 'q e. Prime')
    qnn = sq([qpr, w.inst('prmnn')], 'syl', 'q e. NN')
    qsq = sq([qpr, w.inst('sqfprm')], 'syl', '( mmu ` q ) =/= 0')
    vq = sq([qnn, qsq, w.inst('progvsqf')], 'syl2anc', '( %s ` q ) = ( 1 / q )' % V)
    e1 = sq([vq], 'oveq2d', '( 1 - ( %s ` q ) ) = ( 1 - ( 1 / q ) )' % V)
    e2 = sq([e1], 'oveq2d',
            '( 1 / ( 1 - ( %s ` q ) ) ) = ( 1 / ( 1 - ( 1 / q ) ) )' % V)
    pe = st([e2], 'prodeq2dv',
            'prod_ q e. %s ( 1 / ( 1 - ( %s ` q ) ) ) = prod_ q e. %s ( 1 / ( 1 - ( 1 / q ) ) )'
            % (PFL, V, PFL))
    w.qed([vl, pe], 'oveq12d', '( %s -> %s = %s )' % (ANT, GTV('L'), GTR('L')))
    return w


def main(names=None):
    fns = {'radlem': radlem, 'progvgt': progvgt}
    ok = True
    for nm in (names or ['radlem', 'progvgt']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
