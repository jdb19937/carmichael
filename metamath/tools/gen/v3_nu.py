"""Sortie v3: the prime-factor product over a coprime factorisation, and phi ( 2 M ).

pffinq     ( K e. NN -> PF( K ) e. Fin )
pfprodmul  ( ( ( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 ) /\\ G : Prime --> CC ) ->
               prod_ p e. PF( ( A x. B ) ) ( G ` p )
                 = ( prod_ p e. PF( A ) ( G ` p ) x. prod_ p e. PF( B ) ( G ` p ) ) )
phi2mule   ( M e. NN -> ( phi ` M ) <_ ( phi ` ( 2 x. M ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v3_lib import mkst
from cl import lift
from lin import linarith


def PQ(X):
    return '{ q e. Prime | q || %s }' % X


def pffinq():
    w = WS('pffinq', 'The set of prime divisors of a positive integer, as a restricted '
                     'abstraction over q, is finite.')
    A = 'K e. NN'
    st = mkst(w, A)
    cb = w.s([w.s([], 'breq1', '( p = q -> ( p || K <-> q || K ) )')], 'cbvrabv',
             '{ p e. Prime | p || K } = %s' % PQ('K'))
    fin0 = st([st([], 'id', 'K e. NN'), w.inst('prmdvdsfi')], 'syl',
              '{ p e. Prime | p || K } e. Fin')
    w.qed([st([cb], 'a1i', '{ p e. Prime | p || K } = %s' % PQ('K')), fin0], 'eqeltrrd',
          '( K e. NN -> %s e. Fin )' % PQ('K'))
    return w


AM = '( ( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 ) /\\ G : Prime --> CC )'


def pfprodmul():
    w = WS('pfprodmul', 'A product over the prime divisors of a product of coprime positive '
                        'integers splits as the product of the two factors.')
    st = mkst(w, AM)
    tri = st([], 'simpl', '( A e. NN /\\ B e. NN /\\ ( A gcd B ) = 1 )')
    ann = st([tri], 'simp1d', 'A e. NN')
    bnn = st([tri], 'simp2d', 'B e. NN')
    gf = st([], 'simpr', 'G : Prime --> CC')
    abnn = st([ann, bnn], 'nnmulcld', '( A x. B ) e. NN')
    fin = st([abnn, w.inst('pffinq')], 'syl', '%s e. Fin' % PQ('( A x. B )'))
    un = st([tri, w.inst('pfmul')], 'syl', '%s = ( %s u. %s )' % (PQ('( A x. B )'), PQ('A'), PQ('B')))
    dis = st([tri, w.inst('pfdisj')], 'syl', '( %s i^i %s ) = (/)' % (PQ('A'), PQ('B')))
    AP = '( %s /\\ p e. %s )' % (AM, PQ('( A x. B )'))
    sp = mkst(w, AP)
    pprm = sp([sp([], 'simpr', 'p e. %s' % PQ('( A x. B )')), w.inst('elrabi')], 'syl',
              'p e. Prime')
    gc = sp([lift(w, gf, AP), pprm, w.inst('ffvelcdm')], 'syl2anc', '( G ` p ) e. CC')
    w.qed([dis, un, fin, gc], 'fprodsplit',
          '( %s -> prod_ p e. %s ( G ` p ) = ( prod_ p e. %s ( G ` p ) x. prod_ p e. %s ( G ` p ) ) )'
          % (AM, PQ('( A x. B )'), PQ('A'), PQ('B')))
    return w


def phi2mule():
    w = WS('phi2mule', 'The totient of M is at most the totient of 2 M.')
    A = 'M e. NN'
    st = mkst(w, A)
    mnn = st([], 'id', 'M e. NN')
    mz = st([mnn], 'nnzd', 'M e. ZZ')
    twonn = st([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN')
    tmnn = st([twonn, mnn], 'nnmulcld', '( 2 x. M ) e. NN')
    phim = st([mnn], 'phicld', '( phi ` M ) e. NN')
    phimre = st([phim], 'nnred', '( phi ` M ) e. RR')
    phitm = st([tmnn], 'phicld', '( phi ` ( 2 x. M ) ) e. NN')
    phitmre = st([phitm], 'nnred', '( phi ` ( 2 x. M ) ) e. RR')
    # case 1: 2 does not divide M
    A1 = '( %s /\\ -. 2 || M )' % A
    s1 = mkst(w, A1)
    gcd1 = s1([s1([s1([w.s([], '2prm', '2 e. Prime')], 'a1i', '2 e. Prime'), lift(w, mz, A1)],
                  'jca', '( 2 e. Prime /\\ M e. ZZ )'), w.inst('coprm')], 'syl',
              '( -. 2 || M <-> ( 2 gcd M ) = 1 )')
    gcd1b = s1([gcd1, s1([], 'simpr', '-. 2 || M')], 'mpbid', '( 2 gcd M ) = 1')
    pm = s1([s1([lift(w, twonn, A1), lift(w, mnn, A1), gcd1b], '3jca',
                '( 2 e. NN /\\ M e. NN /\\ ( 2 gcd M ) = 1 )'), w.inst('phimul')], 'syl',
            '( phi ` ( 2 x. M ) ) = ( ( phi ` 2 ) x. ( phi ` M ) )')
    ph2 = w.s([w.s([], '2prm', '2 e. Prime'), w.inst('phiprm')], 'ax-mp',
              '( phi ` 2 ) = ( 2 - 1 )')
    ph2b = w.s([ph2, w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'eqtri', '( phi ` 2 ) = 1')
    pm2 = s1([pm, s1([s1([ph2b], 'a1i', '( phi ` 2 ) = 1')], 'oveq1d',
                     '( ( phi ` 2 ) x. ( phi ` M ) ) = ( 1 x. ( phi ` M ) )')], 'eqtrd',
              '( phi ` ( 2 x. M ) ) = ( 1 x. ( phi ` M ) )')
    pm3 = s1([pm2, s1([s1([lift(w, phimre, A1)], 'recnd', '( phi ` M ) e. CC')], 'mullidd',
                      '( 1 x. ( phi ` M ) ) = ( phi ` M )')], 'eqtrd',
              '( phi ` ( 2 x. M ) ) = ( phi ` M )')
    c1 = s1([s1([lift(w, phimre, A1)], 'leidd', '( phi ` M ) <_ ( phi ` M )'),
             s1([pm3], 'eqcomd', '( phi ` M ) = ( phi ` ( 2 x. M ) )')], 'breqtrd',
            '( phi ` M ) <_ ( phi ` ( 2 x. M ) )')
    # case 2: 2 divides M, so the prime divisors of 2 M are those of M
    A2 = '( %s /\\ 2 || M )' % A
    s2 = mkst(w, A2)
    tdm = s2([], 'simpr', '2 || M')
    AQ = '( %s /\\ q e. Prime )' % A2
    sq = mkst(w, AQ)
    qprm = sq([], 'simpr', 'q e. Prime')
    qz = sq([sq([qprm, w.inst('prmnn')], 'syl', 'q e. NN')], 'nnzd', 'q e. ZZ')
    twoz = sq([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    eu = sq([qprm, twoz, lift(w, mz, AQ), w.inst('euclemma')], 'syl3anc',
            '( q || ( 2 x. M ) <-> ( q || 2 \\/ q || M ) )')
    AQ2 = '( %s /\\ q || 2 )' % AQ
    sq2 = mkst(w, AQ2)
    q2eq = sq2([sq2([sq2([lift(w, qprm, AQ2), w.inst('prmuz2')], 'syl',
                              'q e. ( ZZ>= ` 2 )'),
                          sq2([w.s([], '2prm', '2 e. Prime')], 'a1i', '2 e. Prime'),
                          w.inst('dvdsprm')], 'syl2anc', '( q || 2 <-> q = 2 )'),
                     sq2([], 'simpr', 'q || 2')], 'mpbid', 'q = 2')
    qdm2 = sq2([sq2([q2eq], 'breq1d', '( q || M <-> 2 || M )'), lift(w, tdm, AQ2)], 'mpbird',
               'q || M')
    fwda = sq([qdm2], 'ex', '( q || 2 -> q || M )')
    fwdb = w.s([], 'id', '( q || M -> q || M )')
    fwd = sq([fwda, sq([fwdb], 'a1i', '( q || M -> q || M )')], 'jaod',
             '( ( q || 2 \\/ q || M ) -> q || M )')
    f1 = sq([eu, fwd], 'sylbid', '( q || ( 2 x. M ) -> q || M )')
    b1 = sq([qz, twoz, lift(w, mz, AQ), w.inst('dvdsmultr2')], 'syl3anc',
            '( q || M -> q || ( 2 x. M ) )')
    bic = sq([f1, b1], 'impbid', '( q || ( 2 x. M ) <-> q || M )')
    pfeq = s2([bic], 'rabbidva', '%s = %s' % (PQ('( 2 x. M )'), PQ('M')))
    pr1 = s2([lift(w, tmnn, A2), w.inst('phipfprod')], 'syl',
             'prod_ p e. %s ( 1 - ( 1 / p ) ) = ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) )'
             % PQ('( 2 x. M )'))
    pr2 = s2([lift(w, mnn, A2), w.inst('phipfprod')], 'syl',
             'prod_ p e. %s ( 1 - ( 1 / p ) ) = ( ( phi ` M ) / M )' % PQ('M'))
    pre = s2([s2([pfeq], 'prodeq1d',
                 'prod_ p e. %s ( 1 - ( 1 / p ) ) = prod_ p e. %s ( 1 - ( 1 / p ) )'
                 % (PQ('( 2 x. M )'), PQ('M'))), pr2], 'eqtrd',
             'prod_ p e. %s ( 1 - ( 1 / p ) ) = ( ( phi ` M ) / M )' % PQ('( 2 x. M )'))
    ratio = s2([s2([pr1], 'eqcomd',
                   '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) = prod_ p e. %s ( 1 - ( 1 / p ) )'
                   % PQ('( 2 x. M )')), pre], 'eqtrd',
               '( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) = ( ( phi ` M ) / M )')
    mrp = s2([lift(w, mnn, A2)], 'nnrpd', 'M e. RR+')
    tmrp = s2([lift(w, tmnn, A2)], 'nnrpd', '( 2 x. M ) e. RR+')
    phitmc = s2([lift(w, phitmre, A2)], 'recnd', '( phi ` ( 2 x. M ) ) e. CC')
    phimc = s2([lift(w, phimre, A2)], 'recnd', '( phi ` M ) e. CC')
    tmc = s2([tmrp], 'rpcnd', '( 2 x. M ) e. CC')
    tmne = s2([tmrp], 'rpne0d', '( 2 x. M ) =/= 0')
    mc = s2([mrp], 'rpcnd', 'M e. CC')
    mne = s2([mrp], 'rpne0d', 'M =/= 0')
    cross = s2([s2([phitmc, tmc, tmne], 'divcan2d',
                   '( ( 2 x. M ) x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) ) = ( phi ` ( 2 x. M ) )')],
               'eqcomd',
               '( phi ` ( 2 x. M ) ) = ( ( 2 x. M ) x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) )')
    two2 = s2([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')
    step = s2([cross, s2([ratio], 'oveq2d',
                         '( ( 2 x. M ) x. ( ( phi ` ( 2 x. M ) ) / ( 2 x. M ) ) ) = '
                         '( ( 2 x. M ) x. ( ( phi ` M ) / M ) )')], 'eqtrd',
              '( phi ` ( 2 x. M ) ) = ( ( 2 x. M ) x. ( ( phi ` M ) / M ) )')
    reassoc = s2([two2, mc, s2([phimc, mc, mne], 'divcld', '( ( phi ` M ) / M ) e. CC')],
                 'mulassd',
                 '( ( 2 x. M ) x. ( ( phi ` M ) / M ) ) = ( 2 x. ( M x. ( ( phi ` M ) / M ) ) )')
    mcan = s2([phimc, mc, mne], 'divcan2d', '( M x. ( ( phi ` M ) / M ) ) = ( phi ` M )')
    fin2 = s2([step, s2([reassoc, s2([mcan], 'oveq2d',
                                     '( 2 x. ( M x. ( ( phi ` M ) / M ) ) ) = ( 2 x. ( phi ` M ) )')],
                        'eqtrd',
                        '( ( 2 x. M ) x. ( ( phi ` M ) / M ) ) = ( 2 x. ( phi ` M ) )')], 'eqtrd',
              '( phi ` ( 2 x. M ) ) = ( 2 x. ( phi ` M ) )')
    phige = s2([s2([lift(w, phim, A2)], 'nnrpd', '( phi ` M ) e. RR+')], 'rpge0d',
               '0 <_ ( phi ` M )')
    le2 = linarith(w, A2, [phige], '( phi ` M ) <_ ( 2 x. ( phi ` M ) )',
                   leaves={'( phi ` M )': lift(w, phimre, A2)})
    c2 = s2([le2, s2([fin2], 'eqcomd', '( 2 x. ( phi ` M ) ) = ( phi ` ( 2 x. M ) )')],
            'breqtrd', '( phi ` M ) <_ ( phi ` ( 2 x. M ) )')
    w.qed([c2, c1], 'pm2.61dan', '( %s -> ( phi ` M ) <_ ( phi ` ( 2 x. M ) ) )' % A)
    return w


ALL = {'pffinq': pffinq, 'pfprodmul': pfprodmul, 'phi2mule': phi2mule}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
