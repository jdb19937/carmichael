"""Sortie v4a: the density function of the twin sieve."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import mkst
from cl import lift

PFG = '{ g e. Prime | g || %s }'
PFQ = '{ q e. Prime | q || %s }'


def PFP(X):
    return 'prod_ f e. %s ( 2 / f )' % (PFG % X)


VV = '( t e. NN |-> %s )' % PFP('t')
GMAP = '( g e. Prime |-> ( 2 / g ) )'


def vsub(w, N, v='t'):
    """closed step: ( t = N -> PFP( t ) = PFP( N ) )"""
    b = w.s([], 'breq2', '( %s = %s -> ( g || %s <-> g || %s ) )' % (v, N, v, N))
    rb = w.s([b], 'rabbidv', '( %s = %s -> %s = %s )' % (v, N, PFG % v, PFG % N))
    return w.s([rb], 'prodeq1d', '( %s = %s -> %s = %s )' % (v, N, PFP(v), PFP(N)))


def cbvpfg(w, X):
    """closed step: { q e. Prime | q || X } = { g e. Prime | g || X }"""
    b = w.s([], 'breq1', '( q = g -> ( q || %s <-> g || %s ) )' % (X, X))
    return w.s([b], 'cbvrabv', '%s = %s' % (PFQ % X, PFG % X))


def twinvval():
    w = WS('twinvval', 'The value of the twin-sieve density at a positive integer is the '
                       'product of 2 over its prime divisors.')
    st = mkst(w, 'N e. NN')
    sb = vsub(w, 'N')
    ex = w.s([], 'prodex', '%s e. _V' % PFP('N'))
    fv = w.s([sb, w.s([], 'eqid', '%s = %s' % (VV, VV))], 'fvmptg',
             '( ( N e. NN /\\ %s e. _V ) -> ( %s ` N ) = %s )' % (PFP('N'), VV, PFP('N')))
    w.qed([st([st([], 'id', 'N e. NN'), st([ex], 'a1i', '%s e. _V' % PFP('N'))], 'jca',
              '( N e. NN /\\ %s e. _V )' % PFP('N')),
           st([fv], 'a1i',
              '( ( N e. NN /\\ %s e. _V ) -> ( %s ` N ) = %s )' % (PFP('N'), VV, PFP('N')))],
          'mpd', '( N e. NN -> ( %s ` N ) = %s )' % (VV, PFP('N')))
    return w


def twinvf():
    w = WS('twinvf', 'The twin-sieve density is a real-valued function on the positive '
                     'integers.')
    AT = 't e. NN'
    st = mkst(w, AT)
    gfin = st([st([st([], 'id', 't e. NN'), w.inst('pffinq')], 'syl', '%s e. Fin' % (PFQ % 't')),
               st([cbvpfg(w, 't')], 'a1i', '%s = %s' % (PFQ % 't', PFG % 't'))], 'id',
              'z')
    w.lines.pop()
    gfin = st([st([cbvpfg(w, 't')], 'a1i', '%s = %s' % (PFQ % 't', PFG % 't')),
               st([st([], 'id', 't e. NN'), w.inst('pffinq')], 'syl',
                  '%s e. Fin' % (PFQ % 't'))], 'eqeltrrd', '%s e. Fin' % (PFG % 't'))
    AF = '( %s /\\ f e. %s )' % (AT, PFG % 't')
    sf = mkst(w, AF)
    elf = w.s([w.s([], 'breq1', '( g = f -> ( g || t <-> f || t ) )')], 'elrab',
              '( f e. %s <-> ( f e. Prime /\\ f || t ) )' % (PFG % 't'))
    fprm = sf([sf([sf([elf], 'a1i',
                      '( f e. %s <-> ( f e. Prime /\\ f || t ) )' % (PFG % 't')),
                   sf([], 'simpr', 'f e. %s' % (PFG % 't'))], 'mpbid',
                  '( f e. Prime /\\ f || t )')], 'simpld', 'f e. Prime')
    fre = sf([sf([sf([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
                  sf([sf([fprm, w.inst('prmnn')], 'syl', 'f e. NN')], 'nnrpd', 'f e. RR+')],
                 'rerpdivcld', '( 2 / f ) e. RR')], 'id', 'z')
    w.lines.pop()
    fre = sf([sf([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
              sf([sf([fprm, w.inst('prmnn')], 'syl', 'f e. NN')], 'nnrpd', 'f e. RR+')],
             'rerpdivcld', '( 2 / f ) e. RR')
    pre = st([gfin, fre], 'fprodrecl', '%s e. RR' % PFP('t'))
    ral = w.s([pre], 'rgen', 'A. t e. NN %s e. RR' % PFP('t'))
    bic = w.s([w.s([], 'eqid', '%s = %s' % (VV, VV))], 'fmpt',
              '( A. t e. NN %s e. RR <-> %s : NN --> RR )' % (PFP('t'), VV))
    w.qed([ral, bic], 'mpbi', '%s : NN --> RR' % VV)
    return w


def twinv1():
    w = WS('twinv1', 'The twin-sieve density at 1 is 1.')
    ral1 = w.s([w.s([], 'nprmdvds1', '( g e. Prime -> -. g || 1 )')], 'rgen',
               'A. g e. Prime -. g || 1')
    r0 = w.s([w.s([], 'rabeq0', '( %s = (/) <-> A. g e. Prime -. g || 1 )' % (PFG % '1')),
              ral1], 'mpbir', '%s = (/)' % (PFG % '1'))
    pv = w.s([r0, w.inst('prodeq1')], 'ax-mp', '%s = prod_ f e. (/) ( 2 / f )' % PFP('1'))
    p0 = w.s([], 'prod0', 'prod_ f e. (/) ( 2 / f ) = 1')
    pe1 = w.s([pv, p0], 'eqtri', '%s = 1' % PFP('1'))
    onenn = w.s([], '1nn', '1 e. NN')
    fv = w.s([onenn, w.inst('twinvval')], 'ax-mp', '( %s ` 1 ) = %s' % (VV, PFP('1')))
    w.qed([fv, pe1], 'eqtri', '( %s ` 1 ) = 1' % VV)
    return w


def twinvp():
    w = WS('twinvp', 'The twin-sieve density at a prime is 2 over that prime.')
    st = mkst(w, 'D e. Prime')
    dprm = st([], 'id', 'D e. Prime')
    dnn = st([dprm, w.inst('prmnn')], 'syl', 'D e. NN')
    AG = '( D e. Prime /\\ g e. Prime )'
    sg = mkst(w, AG)
    gprm = sg([], 'simpr', 'g e. Prime')
    guz = sg([gprm, w.inst('prmuz2')], 'syl', 'g e. ( ZZ>= ` 2 )')
    bic = sg([guz, lift(w, dprm, AG), w.inst('dvdsprm')], 'syl2anc', '( g || D <-> g = D )')
    rab1 = st([bic], 'rabbidva', '%s = { g e. Prime | g = D }' % (PFG % 'D'))
    rsn = st([dprm, w.inst('rabsn')], 'syl', '{ g e. Prime | g = D } = { D }')
    seteq = st([rab1, rsn], 'eqtrd', '%s = { D }' % (PFG % 'D'))
    pset = st([seteq, w.inst('prodeq1')], 'syl',
              '%s = prod_ f e. { D } ( 2 / f )' % PFP('D'))
    tdre = st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
               st([dnn], 'nnrpd', 'D e. RR+')], 'rerpdivcld', '( 2 / D ) e. RR')
    tdcc = st([tdre], 'recnd', '( 2 / D ) e. CC')
    dvv = st([st([dnn], 'nnred', 'D e. RR')], 'elexd', 'D e. _V')
    psn = st([st([dvv, tdcc], 'jca', '( D e. _V /\\ ( 2 / D ) e. CC )'),
              st([w.s([w.s([], 'oveq2', '( f = D -> ( 2 / f ) = ( 2 / D ) )')], 'prodsn',
                      '( ( D e. _V /\\ ( 2 / D ) e. CC ) -> '
                      'prod_ f e. { D } ( 2 / f ) = ( 2 / D ) )')], 'a1i',
                 '( ( D e. _V /\\ ( 2 / D ) e. CC ) -> '
                 'prod_ f e. { D } ( 2 / f ) = ( 2 / D ) )')], 'mpd',
             'prod_ f e. { D } ( 2 / f ) = ( 2 / D )')
    fv = st([dnn, w.inst('twinvval')], 'syl', '( %s ` D ) = %s' % (VV, PFP('D')))
    w.qed([fv, st([pset, psn], 'eqtrd', '%s = ( 2 / D )' % PFP('D'))], 'eqtrd',
          '( D e. Prime -> ( %s ` D ) = ( 2 / D ) )' % VV)
    return w


AM = '( A e. NN /\ B e. NN /\ ( A gcd B ) = 1 )'


def twinvmul():
    w = WS('twinvmul', 'The twin-sieve density is multiplicative on coprime arguments.')
    st = mkst(w, AM)
    ann = st([], 'simp1', 'A e. NN')
    bnn = st([], 'simp2', 'B e. NN')
    abnn = st([ann, bnn], 'nnmulcld', '( A x. B ) e. NN')
    # GMAP is a function into CC
    gcc = w.s([], 'id', 'z')
    w.lines.pop()
    AG = 'g e. Prime'
    sg = mkst(w, AG)
    gccs = sg([sg([sg([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
                   sg([sg([sg([], 'id', 'g e. Prime'), w.inst('prmnn')], 'syl', 'g e. NN')],
                      'nnrpd', 'g e. RR+')], 'rerpdivcld', '( 2 / g ) e. RR')], 'recnd',
              '( 2 / g ) e. CC')
    ralg = w.s([gccs], 'rgen', 'A. g e. Prime ( 2 / g ) e. CC')
    gbic = w.s([w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fmpt',
               '( A. g e. Prime ( 2 / g ) e. CC <-> %s : Prime --> CC )' % GMAP)
    gfn = w.s([ralg, gbic], 'mpbi', '%s : Prime --> CC' % GMAP)
    ppm = st([st([st([], 'id', AM), st([gfn], 'a1i', '%s : Prime --> CC' % GMAP)], 'jca',
                 '( %s /\ %s : Prime --> CC )' % (AM, GMAP)), w.inst('pfprodmul')], 'syl',
             'prod_ p e. %s ( %s ` p ) = ( prod_ p e. %s ( %s ` p ) x. prod_ p e. %s ( %s ` p ) )'
             % (PFQ % '( A x. B )', GMAP, PFQ % 'A', GMAP, PFQ % 'B', GMAP))

    def bridge(X):
        APP = '( %s /\ p e. %s )' % (AM, PFQ % X)
        sp = mkst(w, APP)
        elp = w.s([w.s([], 'breq1', '( q = p -> ( q || %s <-> p || %s ) )' % (X, X))], 'elrab',
                  '( p e. %s <-> ( p e. Prime /\ p || %s ) )' % (PFQ % X, X))
        pprm = sp([sp([sp([elp], 'a1i',
                          '( p e. %s <-> ( p e. Prime /\ p || %s ) )' % (PFQ % X, X)),
                       sp([], 'simpr', 'p e. %s' % (PFQ % X))], 'mpbid',
                      '( p e. Prime /\ p || %s )' % X)], 'simpld', 'p e. Prime')
        pcc = sp([sp([sp([sp([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
                          sp([sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')], 'nnrpd',
                             'p e. RR+')], 'rerpdivcld', '( 2 / p ) e. RR')], 'recnd',
                     '( 2 / p ) e. CC')], 'elexd', '( 2 / p ) e. _V')
        gv = sp([sp([pprm, pcc], 'jca', '( p e. Prime /\ ( 2 / p ) e. _V )'),
                 sp([w.s([w.s([], 'oveq2', '( g = p -> ( 2 / g ) = ( 2 / p ) )'),
                          w.s([], 'eqid', '%s = %s' % (GMAP, GMAP))], 'fvmptg',
                         '( ( p e. Prime /\ ( 2 / p ) e. _V ) -> ( %s ` p ) = ( 2 / p ) )'
                         % GMAP)], 'a1i',
                    '( ( p e. Prime /\ ( 2 / p ) e. _V ) -> ( %s ` p ) = ( 2 / p ) )'
                    % GMAP)], 'mpd', '( %s ` p ) = ( 2 / p )' % GMAP)
        e1 = st([gv], 'prodeq2dv',
                'prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( 2 / p )' % (PFQ % X, GMAP, PFQ % X))
        cb = w.s([w.s([], 'oveq2', '( p = f -> ( 2 / p ) = ( 2 / f ) )')], 'cbvprodv',
                 'prod_ p e. %s ( 2 / p ) = prod_ f e. %s ( 2 / f )' % (PFQ % X, PFQ % X))
        e2 = st([st([cbvpfg(w, X)], 'a1i', '%s = %s' % (PFQ % X, PFG % X)),
                 w.inst('prodeq1')], 'syl',
                'prod_ f e. %s ( 2 / f ) = %s' % (PFQ % X, PFP(X)))
        return st([st([e1, st([cb], 'a1i',
                              'prod_ p e. %s ( 2 / p ) = prod_ f e. %s ( 2 / f )'
                              % (PFQ % X, PFQ % X))], 'eqtrd',
                      'prod_ p e. %s ( %s ` p ) = prod_ f e. %s ( 2 / f )'
                      % (PFQ % X, GMAP, PFQ % X)), e2], 'eqtrd',
                  'prod_ p e. %s ( %s ` p ) = %s' % (PFQ % X, GMAP, PFP(X)))

    bAB = bridge('( A x. B )')
    bA = bridge('A')
    bB = bridge('B')
    vab = st([abnn, w.inst('twinvval')], 'syl', '( %s ` ( A x. B ) ) = %s' % (VV, PFP('( A x. B )')))
    va = st([ann, w.inst('twinvval')], 'syl', '( %s ` A ) = %s' % (VV, PFP('A')))
    vb = st([bnn, w.inst('twinvval')], 'syl', '( %s ` B ) = %s' % (VV, PFP('B')))
    left = st([vab, st([bAB], 'eqcomd',
                       '%s = prod_ p e. %s ( %s ` p )' % (PFP('( A x. B )'), PFQ % '( A x. B )', GMAP))],
              'eqtrd', '( %s ` ( A x. B ) ) = prod_ p e. %s ( %s ` p )'
              % (VV, PFQ % '( A x. B )', GMAP))
    right = st([st([bA, bB], 'oveq12d',
                   '( prod_ p e. %s ( %s ` p ) x. prod_ p e. %s ( %s ` p ) ) = ( %s x. %s )'
                   % (PFQ % 'A', GMAP, PFQ % 'B', GMAP, PFP('A'), PFP('B'))),
                st([st([va, vb], 'oveq12d',
                       '( ( %s ` A ) x. ( %s ` B ) ) = ( %s x. %s )'
                       % (VV, VV, PFP('A'), PFP('B')))], 'eqcomd',
                   '( %s x. %s ) = ( ( %s ` A ) x. ( %s ` B ) )'
                   % (PFP('A'), PFP('B'), VV, VV))], 'eqtrd',
               '( prod_ p e. %s ( %s ` p ) x. prod_ p e. %s ( %s ` p ) ) = '
               '( ( %s ` A ) x. ( %s ` B ) )' % (PFQ % 'A', GMAP, PFQ % 'B', GMAP, VV, VV))
    w.qed([st([left, ppm], 'eqtrd',
              '( %s ` ( A x. B ) ) = ( prod_ p e. %s ( %s ` p ) x. prod_ p e. %s ( %s ` p ) )'
              % (VV, PFQ % 'A', GMAP, PFQ % 'B', GMAP)), right], 'eqtrd',
          '( %s -> ( %s ` ( A x. B ) ) = ( ( %s ` A ) x. ( %s ` B ) ) )' % (AM, VV, VV, VV))
    return w


ALL = {'twinvval': twinvval, 'twinvf': twinvf, 'twinv1': twinv1, 'twinvp': twinvp,
       'twinvmul': twinvmul}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
