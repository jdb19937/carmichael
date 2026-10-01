"""Sortie v2c: the Lambda-squared main-term diagonalisation.

mpgex1  the main term as a triple sum with the lcm indicator
mpgex2  the triple sum collapses to a double sum over the lcm
mpggcd  the gcd expansion of the density at the lcm
mpgsw   the diagonalising index moves outermost
mpgsq   the inner double sum is a square
mpgen   Mathlib's mainSum_lambdaSquared_eq_sum_mul_sum_sq
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2c_lib import *
from cl import lift

B = '( %s /\\ L : NN --> RR )' % SH
DVP = DV('P', 'y')
LT = '( ( L ` u ) x. ( L ` e ) )'
IF3 = 'if ( d = ( u lcm e ) , %s , 0 )' % LT
G3 = 'if ( d = ( u lcm e ) , ( %s x. ( V ` d ) ) , 0 )' % LT
LSD = ('sum_ u e. %s sum_ e e. %s if ( d = ( u lcm e ) , %s , 0 )'
       % (DV('d', 'y'), DV('d', 'y'), LT))
LSP = 'sum_ u e. %s sum_ e e. %s %s' % (DVP, DVP, IF3)
TRIP = 'sum_ u e. %s sum_ e e. %s %s' % (DVP, DVP, G3)


def base(w):
    """the SH steps and the function hypothesis under B"""
    d = shsteps(w, B, (SH,))
    d['lf'] = w.s([], 'simpr', '( %s -> L : NN --> RR )' % B)
    d['finP'] = d['st']([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    return d


def lcc(w, ante, lf, vnn, v):
    """( ante -> ( L ` v ) e. CC )"""
    return w.s([w.s([lf, vnn, w.inst('ffvelcdm')], 'syl2anc',
                    '( %s -> ( L ` %s ) e. RR )' % (ante, v))], 'recnd',
               '( %s -> ( L ` %s ) e. CC )' % (ante, v))


def vcc(w, ante, vf, vnn, v):
    return w.s([w.s([vf, vnn, w.inst('ffvelcdm')], 'syl2anc',
                    '( %s -> ( V ` %s ) e. RR )' % (ante, v))], 'recnd',
               '( %s -> ( V ` %s ) e. CC )' % (ante, v))


def mpgex1():
    w = W('mpgex1', 'The Lambda squared main term as a triple sum with the lcm indicator.')
    d = base(w)
    st = d['st']
    BD = '( %s /\\ d e. %s )' % (B, DVP)
    dd = dvpel(w, BD, 'd', d['pnn'], 'y')
    sd = dd['st']
    vd = vcc(w, BD, lift(w, d['vf'], BD), dd['nn'], 'd')
    ext = sd([sd([lift(w, d['lf'], BD), lift(w, d['pnn'], BD),
                  sd([dd['nn'], dd['dP']], 'jca', '( d e. NN /\\ d || P )')], '3jca',
                 '( L : NN --> RR /\\ P e. NN /\\ ( d e. NN /\\ d || P ) )'),
               w.inst('lamsqex')], 'syl', '%s = %s' % (LSD, LSP))
    # ---- closures for the body
    BDU = '( %s /\\ u e. %s )' % (BD, DVP)
    du = dvpel(w, BDU, 'u', d['pnn'], 'y')
    su = du['st']
    lu = lcc(w, BDU, lift(w, d['lf'], BDU), du['nn'], 'u')
    BDUE = '( %s /\\ e e. %s )' % (BDU, DVP)
    de = dvpel(w, BDUE, 'e', d['pnn'], 'y')
    se = de['st']
    le = lcc(w, BDUE, lift(w, d['lf'], BDUE), de['nn'], 'e')
    ltc = se([lift(w, lu, BDUE), le], 'mulcld', '%s e. CC' % LT)
    if3c = se([ltc, w.s([], '0cnd', '( %s -> 0 e. CC )' % BDUE)], 'ifcld', '%s e. CC' % IF3)
    innc = su([lift(w, d['finP'], BDU), if3c], 'fsumcl', 'sum_ e e. %s %s e. CC' % (DVP, IF3))
    # ---- pull ( V ` d ) inside
    mul1 = sd([lift(w, d['finP'], BD), vd, innc], 'fsummulc1',
              '( %s x. ( V ` d ) ) = sum_ u e. %s ( sum_ e e. %s %s x. ( V ` d ) )'
              % (LSP, DVP, DVP, IF3))
    mul2 = su([lift(w, d['finP'], BDU), lift(w, vd, BDU), if3c], 'fsummulc1',
              '( sum_ e e. %s %s x. ( V ` d ) ) = sum_ e e. %s ( %s x. ( V ` d ) )'
              % (DVP, IF3, DVP, IF3))
    ifm = se([lift(w, vd, BDUE), w.inst('ifmulz')], 'syl',
             '( %s x. ( V ` d ) ) = %s' % (IF3, G3))
    inner = su([ifm], 'sumeq2dv',
               'sum_ e e. %s ( %s x. ( V ` d ) ) = sum_ e e. %s %s' % (DVP, IF3, DVP, G3))
    step = su([mul2, inner], 'eqtrd',
              '( sum_ e e. %s %s x. ( V ` d ) ) = sum_ e e. %s %s' % (DVP, IF3, DVP, G3))
    outer = sd([step], 'sumeq2dv',
               'sum_ u e. %s ( sum_ e e. %s %s x. ( V ` d ) ) = %s' % (DVP, DVP, IF3, TRIP))
    term = sd([sd([ext], 'oveq1d', '( %s x. ( V ` d ) ) = ( %s x. ( V ` d ) )' % (LSD, LSP)),
               sd([mul1, outer], 'eqtrd', '( %s x. ( V ` d ) ) = %s' % (LSP, TRIP))], 'eqtrd',
              '( %s x. ( V ` d ) ) = %s' % (LSD, TRIP))
    w.qed([term], 'sumeq2dv',
          '( %s -> sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ d e. %s %s )'
          % (B, DVP, LSD, DVP, TRIP))
    return w


LCMT = '( %s x. ( V ` ( u lcm e ) ) )' % LT
DBL = 'sum_ u e. %s sum_ e e. %s %s' % (DVP, DVP, LCMT)


def g3cc(w, ante, d, lf, vf, unn, enn, dnn):
    """( ante -> G3 e. CC )"""
    st = mkst(w, ante)
    lu = lcc(w, ante, lf, unn, 'u')
    le = lcc(w, ante, lf, enn, 'e')
    vd = vcc(w, ante, vf, dnn, 'd')
    return st([st([st([lu, le], 'mulcld', '%s e. CC' % LT), vd], 'mulcld',
                  '( %s x. ( V ` d ) ) e. CC' % LT),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % ante)], 'ifcld', '%s e. CC' % G3)


def mpgex2():
    w = W('mpgex2', 'The triple sum of the Lambda squared main term collapses along the lcm.')
    d = base(w)
    st = d['st']
    BU = '( %s /\\ u e. %s )' % (B, DVP)
    du = dvpel(w, BU, 'u', d['pnn'], 'y')
    su = du['st']
    BUE = '( %s /\\ e e. %s )' % (BU, DVP)
    de = dvpel(w, BUE, 'e', d['pnn'], 'y')
    se = de['st']
    # ---- the collapse of the d-sum at a pair ( u , e )
    lu = lcc(w, BUE, lift(w, d['lf'], BUE), lift(w, du['nn'], BUE), 'u')
    le = lcc(w, BUE, lift(w, d['lf'], BUE), de['nn'], 'e')
    ltc = se([lu, le], 'mulcld', '%s e. CC' % LT)
    lnn = lcmnn(w, BUE, 'u', 'e', lift(w, du['nn'], BUE), de['nn'])
    pz = se([lift(w, d['pnn'], BUE)], 'nnzd', 'P e. ZZ')
    uz = se([lift(w, du['nn'], BUE)], 'nnzd', 'u e. ZZ')
    ez = se([de['nn']], 'nnzd', 'e e. ZZ')
    ldvd = se([se([se([pz, uz, ez], '3jca', '( P e. ZZ /\\ u e. ZZ /\\ e e. ZZ )'),
                   w.inst('lcmdvds')], 'syl', '( ( u || P /\\ e || P ) -> ( u lcm e ) || P )'),
               se([lift(w, du['dP'], BUE), de['dP']], 'jca', '( u || P /\\ e || P )')], 'mpd',
              '( u lcm e ) || P')
    lmem = indvp(w, BUE, '( u lcm e )', lnn, ldvd, 'y')
    vlc = vcc(w, BUE, lift(w, d['vf'], BUE), lnn, '( u lcm e )')
    lcmtc = se([ltc, vlc], 'mulcld', '%s e. CC' % LCMT)
    hsub = w.s([w.s([], 'fveq2', '( d = ( u lcm e ) -> ( V ` d ) = ( V ` ( u lcm e ) ) )')],
               'oveq2d', '( d = ( u lcm e ) -> ( %s x. ( V ` d ) ) = %s )' % (LT, LCMT))
    coll = se([hsub, lift(w, d['finP'], BUE), lmem, lcmtc], 'sumite',
              'sum_ d e. %s %s = %s' % (DVP, G3, LCMT))
    # ---- the outer swap
    BDU = '( %s /\\ ( d e. %s /\\ u e. %s ) )' % (B, DVP, DVP)
    p1 = dvpel2(w, BDU, 'd', 'u', 'y')
    BDUE = '( %s /\\ e e. %s )' % (BDU, DVP)
    q1 = dvpel(w, BDUE, 'e', d['pnn'], 'y')
    g1 = g3cc(w, BDUE, 'd', lift(w, d['lf'], BDUE), lift(w, d['vf'], BDUE),
              lift(w, p1['u']['nn'], BDUE), q1['nn'], lift(w, p1['d']['nn'], BDUE))
    inn1 = p1['st']([lift(w, d['finP'], BDU), g1], 'fsumcl',
                    'sum_ e e. %s %s e. CC' % (DVP, G3))
    sw1 = st([d['finP'], d['finP'], inn1], 'fsumcom',
             'sum_ d e. %s sum_ u e. %s sum_ e e. %s %s = '
             'sum_ u e. %s sum_ d e. %s sum_ e e. %s %s' % (DVP, DVP, DVP, G3, DVP, DVP, DVP, G3))
    # ---- the inner swap, under BU
    BUDE = '( %s /\\ ( d e. %s /\\ e e. %s ) )' % (BU, DVP, DVP)
    p2 = dvpel2(w, BUDE, 'd', 'e', 'y')
    g2 = g3cc(w, BUDE, 'd', lift(w, d['lf'], BUDE), lift(w, d['vf'], BUDE),
              lift(w, du['nn'], BUDE), p2['e']['nn'], p2['d']['nn'])
    sw2 = su([lift(w, d['finP'], BU), lift(w, d['finP'], BU), g2], 'fsumcom',
             'sum_ d e. %s sum_ e e. %s %s = sum_ e e. %s sum_ d e. %s %s'
             % (DVP, DVP, G3, DVP, DVP, G3))
    sw2u = st([sw2], 'sumeq2dv',
              'sum_ u e. %s sum_ d e. %s sum_ e e. %s %s = '
              'sum_ u e. %s sum_ e e. %s sum_ d e. %s %s' % (DVP, DVP, DVP, G3, DVP, DVP, DVP, G3))
    # ---- the collapse lifted
    c1 = su([coll], 'sumeq2dv',
            'sum_ e e. %s sum_ d e. %s %s = sum_ e e. %s %s' % (DVP, DVP, G3, DVP, LCMT))
    c2 = st([c1], 'sumeq2dv',
            'sum_ u e. %s sum_ e e. %s sum_ d e. %s %s = %s' % (DVP, DVP, DVP, G3, DBL))
    w.qed([sw1, st([sw2u, c2], 'eqtrd',
                   'sum_ u e. %s sum_ d e. %s sum_ e e. %s %s = %s' % (DVP, DVP, DVP, G3, DBL))],
          'eqtrd', '( %s -> sum_ d e. %s %s = %s )' % (B, DVP, TRIP, DBL))
    return w



GCD = '( u gcd e )'
IGTN = IGT('n')


def AU(v):
    return '( ( V ` %s ) x. ( L ` %s ) )' % (v, v)


KK = '( %s x. %s )' % (AU('u'), AU('e'))
IFG = 'if ( n || %s , %s , 0 )' % (GCD, IGTN)
IFN = 'if ( ( n || u /\\ n || e ) , ( %s x. %s ) , 0 )' % (IGTN, KK)
TRN = 'sum_ u e. %s sum_ e e. %s sum_ n e. %s %s' % (DVP, DVP, DVP, IFN)


def mpggcd():
    w = W('mpggcd', 'The density at the lcm expands as a divisor sum of reciprocal Selberg '
                    'terms.')
    d = base(w)
    st = d['st']
    BU = '( %s /\\ u e. %s )' % (B, DVP)
    du = dvpel(w, BU, 'u', d['pnn'], 'y')
    su = du['st']
    BUE = '( %s /\\ e e. %s )' % (BU, DVP)
    de = dvpel(w, BUE, 'e', d['pnn'], 'y')
    se = de['st']
    unn = lift(w, du['nn'], BUE)
    udP = lift(w, du['dP'], BUE)
    enn = de['nn']
    edP = de['dP']
    uz = se([unn], 'nnzd', 'u e. ZZ')
    ez = se([enn], 'nnzd', 'e e. ZZ')
    pz = se([lift(w, d['pnn'], BUE)], 'nnzd', 'P e. ZZ')
    # ---- the gcd is a divisor of P
    gnn = se([se([unn, enn], 'jca', '( u e. NN /\\ e e. NN )'), w.inst('gcdnncl')], 'syl',
             '%s e. NN' % GCD)
    gz = se([gnn], 'nnzd', '%s e. ZZ' % GCD)
    gdu = se([se([se([uz, ez], 'jca', '( u e. ZZ /\\ e e. ZZ )'), w.inst('gcddvds')], 'syl',
                 '( %s || u /\\ %s || e )' % (GCD, GCD))], 'simpld', '%s || u' % GCD)
    gdP = se([se([se([gz, uz, pz], '3jca', '( %s e. ZZ /\\ u e. ZZ /\\ P e. ZZ )' % GCD),
                  w.inst('dvdstr')], 'syl', '( ( %s || u /\\ u || P ) -> %s || P )' % (GCD, GCD)),
              se([gdu, udP], 'jca', '( %s || u /\\ u || P )' % GCD)], 'mpd', '%s || P' % GCD)
    # ---- closures
    vu = vcc(w, BUE, lift(w, d['vf'], BUE), unn, 'u')
    ve = vcc(w, BUE, lift(w, d['vf'], BUE), enn, 'e')
    lu = lcc(w, BUE, lift(w, d['lf'], BUE), unn, 'u')
    le = lcc(w, BUE, lift(w, d['lf'], BUE), enn, 'e')
    grp = se([lift(w, d['sh'], BUE), se([gnn, gdP], 'jca', '( %s e. NN /\\ %s || P )' % (GCD, GCD)),
              w.inst('vdrp')], 'syl2anc', '( V ` %s ) e. RR+' % GCD)
    gvc = se([grp], 'rpcnd', '( V ` %s ) e. CC' % GCD)
    gvn = se([grp], 'rpne0d', '( V ` %s ) =/= 0' % GCD)
    kc = se([se([vu, lu], 'mulcld', '%s e. CC' % AU('u')),
             se([ve, le], 'mulcld', '%s e. CC' % AU('e'))], 'mulcld', '%s e. CC' % KK)
    # ---- the lcm value
    vl = se([se([lift(w, d['sh'], BUE), se([unn, udP], 'jca', '( u e. NN /\\ u || P )'),
                 se([enn, edP], 'jca', '( e e. NN /\\ e || P )')], '3jca',
                '( %s /\\ ( u e. NN /\\ u || P ) /\\ ( e e. NN /\\ e || P ) )' % SH),
             w.inst('vlcm')], 'syl',
            '( V ` ( u lcm e ) ) = ( ( ( V ` u ) x. ( V ` e ) ) / ( V ` %s ) )' % GCD)
    # ---- the algebra
    rec = se([se([vu, ve], 'mulcld', '( ( V ` u ) x. ( V ` e ) ) e. CC'), gvc, gvn], 'divrecd',
             '( ( ( V ` u ) x. ( V ` e ) ) / ( V ` %s ) ) = '
             '( ( ( V ` u ) x. ( V ` e ) ) x. ( 1 / ( V ` %s ) ) )' % (GCD, GCD))
    recc = se([se([grp], 'rpreccld', '( 1 / ( V ` %s ) ) e. RR+' % GCD)], 'rpcnd',
              '( 1 / ( V ` %s ) ) e. CC' % GCD)
    a1 = se([se([vl, rec], 'eqtrd',
                '( V ` ( u lcm e ) ) = '
                '( ( ( V ` u ) x. ( V ` e ) ) x. ( 1 / ( V ` %s ) ) )' % GCD)], 'oveq2d',
            '%s = ( %s x. ( ( ( V ` u ) x. ( V ` e ) ) x. ( 1 / ( V ` %s ) ) ) )' % (LCMT, LT, GCD))
    ltc = se([lu, le], 'mulcld', '%s e. CC' % LT)
    vuvec = se([vu, ve], 'mulcld', '( ( V ` u ) x. ( V ` e ) ) e. CC')
    a2 = se([se([ltc, vuvec, recc], 'mulassd',
                '( ( %s x. ( ( V ` u ) x. ( V ` e ) ) ) x. ( 1 / ( V ` %s ) ) ) = '
                '( %s x. ( ( ( V ` u ) x. ( V ` e ) ) x. ( 1 / ( V ` %s ) ) ) )'
                % (LT, GCD, LT, GCD))], 'eqcomd',
            '( %s x. ( ( ( V ` u ) x. ( V ` e ) ) x. ( 1 / ( V ` %s ) ) ) ) = '
            '( ( %s x. ( ( V ` u ) x. ( V ` e ) ) ) x. ( 1 / ( V ` %s ) ) )' % (LT, GCD, LT, GCD))
    a3 = se([se([se([lu, le, vu, ve], 'mul4d',
                    '( %s x. ( ( V ` u ) x. ( V ` e ) ) ) = '
                    '( ( ( L ` u ) x. ( V ` u ) ) x. ( ( L ` e ) x. ( V ` e ) ) )' % LT),
                 se([se([lu, vu], 'mulcomd',
                        '( ( L ` u ) x. ( V ` u ) ) = %s' % AU('u')),
                     se([le, ve], 'mulcomd',
                        '( ( L ` e ) x. ( V ` e ) ) = %s' % AU('e'))], 'oveq12d',
                    '( ( ( L ` u ) x. ( V ` u ) ) x. ( ( L ` e ) x. ( V ` e ) ) ) = %s' % KK)],
                'eqtrd', '( %s x. ( ( V ` u ) x. ( V ` e ) ) ) = %s' % (LT, KK))], 'oveq1d',
            '( ( %s x. ( ( V ` u ) x. ( V ` e ) ) ) x. ( 1 / ( V ` %s ) ) ) = '
            '( %s x. ( 1 / ( V ` %s ) ) )' % (LT, GCD, KK, GCD))
    alg = se([a1, se([a2, a3], 'eqtrd',
                     '( %s x. ( ( ( V ` u ) x. ( V ` e ) ) x. ( 1 / ( V ` %s ) ) ) ) = '
                     '( %s x. ( 1 / ( V ` %s ) ) )' % (LT, GCD, KK, GCD))], 'eqtrd',
             '%s = ( %s x. ( 1 / ( V ` %s ) ) )' % (LCMT, KK, GCD))
    # ---- the reciprocal density as a divisor sum
    gsum = se([lift(w, d['sh'], BUE), se([gnn, gdP], 'jca', '( %s e. NN /\\ %s || P )' % (GCD, GCD)),
               w.inst('gtsinv2')], 'syl2anc',
              'sum_ n e. %s %s = ( 1 / ( V ` %s ) )' % (DVP, IFG, GCD))
    # ---- closure of the indicator body
    BUEN = '( %s /\\ n e. %s )' % (BUE, DVP)
    dn = dvpel(w, BUEN, 'n', d['pnn'], 'y')
    sn = dn['st']
    gtn = sn([lift(w, d['sh'], BUEN), sn([dn['nn'], dn['dP']], 'jca', '( n e. NN /\\ n || P )'),
              w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('n'))
    igtc = sn([sn([gtn], 'rpreccld', '%s e. RR+' % IGTN)], 'rpcnd', '%s e. CC' % IGTN)
    ifgc = sn([igtc, w.s([], '0cnd', '( %s -> 0 e. CC )' % BUEN)], 'ifcld', '%s e. CC' % IFG)
    mulc = se([lift(w, d['finP'], BUE), kc, ifgc], 'fsummulc2',
              '( %s x. sum_ n e. %s %s ) = sum_ n e. %s ( %s x. %s )' % (KK, DVP, IFG, DVP, KK, IFG))
    # ---- the summand
    ifm = sn([lift(w, kc, BUEN), w.inst('ifmulz2')], 'syl',
             '( %s x. %s ) = if ( n || %s , ( %s x. %s ) , 0 )' % (KK, IFG, GCD, KK, IGTN))
    nz = sn([dn['nn']], 'nnzd', 'n e. ZZ')
    bicond = sn([sn([sn([nz, lift(w, uz, BUEN), lift(w, ez, BUEN)], '3jca',
                        '( n e. ZZ /\\ u e. ZZ /\\ e e. ZZ )'), w.inst('dvdsgcdb')], 'syl',
                     '( ( n || u /\\ n || e ) <-> n || %s )' % GCD)], 'bicomd',
                '( n || %s <-> ( n || u /\\ n || e ) )' % GCD)
    swapm = sn([lift(w, kc, BUEN), igtc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )'
               % (KK, IGTN, IGTN, KK))
    ifn = sn([bicond, swapm], 'ifbieq1d',
             'if ( n || %s , ( %s x. %s ) , 0 ) = %s' % (GCD, KK, IGTN, IFN))
    term = sn([ifm, ifn], 'eqtrd', '( %s x. %s ) = %s' % (KK, IFG, IFN))
    inner = se([term], 'sumeq2dv',
               'sum_ n e. %s ( %s x. %s ) = sum_ n e. %s %s' % (DVP, KK, IFG, DVP, IFN))
    final = se([se([se([gsum], 'oveq2d',
                       '( %s x. sum_ n e. %s %s ) = ( %s x. ( 1 / ( V ` %s ) ) )'
                       % (KK, DVP, IFG, KK, GCD))], 'eqcomd',
                   '( %s x. ( 1 / ( V ` %s ) ) ) = ( %s x. sum_ n e. %s %s )'
                   % (KK, GCD, KK, DVP, IFG)),
                se([mulc, inner], 'eqtrd',
                   '( %s x. sum_ n e. %s %s ) = sum_ n e. %s %s' % (KK, DVP, IFG, DVP, IFN))],
               'eqtrd', '( %s x. ( 1 / ( V ` %s ) ) ) = sum_ n e. %s %s' % (KK, GCD, DVP, IFN))
    per = se([alg, final], 'eqtrd', '%s = sum_ n e. %s %s' % (LCMT, DVP, IFN))
    lv1 = su([per], 'sumeq2dv',
             'sum_ e e. %s %s = sum_ e e. %s sum_ n e. %s %s' % (DVP, LCMT, DVP, DVP, IFN))
    w.qed([lv1], 'sumeq2dv', '( %s -> %s = %s )' % (B, DBL, TRN))
    return w



SWN = 'sum_ n e. %s sum_ u e. %s sum_ e e. %s %s' % (DVP, DVP, DVP, IFN)


def ifncc(w, ante, sh, lf, vf, unn, enn, nnn, ndP):
    """( ante -> IFN e. CC )"""
    st = mkst(w, ante)
    gtn = st([sh, st([nnn, ndP], 'jca', '( n e. NN /\\ n || P )'), w.inst('gtrp')], 'syl2anc',
             '%s e. RR+' % GT('n'))
    igtc = st([st([gtn], 'rpreccld', '%s e. RR+' % IGTN)], 'rpcnd', '%s e. CC' % IGTN)
    kc = st([st([vcc(w, ante, vf, unn, 'u'), lcc(w, ante, lf, unn, 'u')], 'mulcld',
                '%s e. CC' % AU('u')),
             st([vcc(w, ante, vf, enn, 'e'), lcc(w, ante, lf, enn, 'e')], 'mulcld',
                '%s e. CC' % AU('e'))], 'mulcld', '%s e. CC' % KK)
    return st([st([igtc, kc], 'mulcld', '( %s x. %s ) e. CC' % (IGTN, KK)),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % ante)], 'ifcld', '%s e. CC' % IFN)


def mpgsw():
    w = W('mpgsw', 'The diagonalising index moves to the outside of the triple sum.')
    d = base(w)
    st = d['st']
    BU = '( %s /\\ u e. %s )' % (B, DVP)
    du = dvpel(w, BU, 'u', d['pnn'], 'y')
    su = du['st']
    # ---- inner swap, under BU
    A1 = '( %s /\\ ( e e. %s /\\ n e. %s ) )' % (BU, DVP, DVP)
    p1 = dvpel2(w, A1, 'e', 'n', 'y')
    c1 = ifncc(w, A1, lift(w, d['sh'], A1), lift(w, d['lf'], A1), lift(w, d['vf'], A1),
               lift(w, du['nn'], A1), p1['e']['nn'], p1['n']['nn'], p1['n']['dP'])
    sw1 = su([lift(w, d['finP'], BU), lift(w, d['finP'], BU), c1], 'fsumcom',
             'sum_ e e. %s sum_ n e. %s %s = sum_ n e. %s sum_ e e. %s %s'
             % (DVP, DVP, IFN, DVP, DVP, IFN))
    sw1u = st([sw1], 'sumeq2dv',
              '%s = sum_ u e. %s sum_ n e. %s sum_ e e. %s %s' % (TRN, DVP, DVP, DVP, IFN))
    # ---- outer swap
    A2 = '( %s /\\ ( u e. %s /\\ n e. %s ) )' % (B, DVP, DVP)
    p2 = dvpel2(w, A2, 'u', 'n', 'y')
    A3 = '( %s /\\ e e. %s )' % (A2, DVP)
    q3 = dvpel(w, A3, 'e', d['pnn'], 'y')
    c2 = ifncc(w, A3, lift(w, d['sh'], A3), lift(w, d['lf'], A3), lift(w, d['vf'], A3),
               lift(w, p2['u']['nn'], A3), q3['nn'], lift(w, p2['n']['nn'], A3),
               lift(w, p2['n']['dP'], A3))
    inn2 = p2['st']([lift(w, d['finP'], A2), c2], 'fsumcl', 'sum_ e e. %s %s e. CC' % (DVP, IFN))
    sw2 = st([d['finP'], d['finP'], inn2], 'fsumcom',
             'sum_ u e. %s sum_ n e. %s sum_ e e. %s %s = %s' % (DVP, DVP, DVP, IFN, SWN))
    w.qed([sw1u, sw2], 'eqtrd', '( %s -> %s = %s )' % (B, TRN, SWN))
    return w



def XI(v):
    return 'if ( n || %s , %s , 0 )' % (v, AU(v))


TJ = 'sum_ j e. %s %s' % (DVP, XI('j'))
TU = 'sum_ u e. %s %s' % (DVP, XI('u'))
TE = 'sum_ e e. %s %s' % (DVP, XI('e'))
SQT = '( %s x. ( %s ^ 2 ) )' % (IGTN, TJ)


def mpgsq():
    w = W('mpgsq', 'The inner double sum of the diagonalised main term is a square.')
    d = base(w)
    st = d['st']
    BN = '( %s /\\ n e. %s )' % (B, DVP)
    dn = dvpel(w, BN, 'n', d['pnn'], 'y')
    sn = dn['st']
    gtn = sn([lift(w, d['sh'], BN), sn([dn['nn'], dn['dP']], 'jca', '( n e. NN /\\ n || P )'),
              w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('n'))
    igtc = sn([sn([gtn], 'rpreccld', '%s e. RR+' % IGTN)], 'rpcnd', '%s e. CC' % IGTN)
    # ---- the e-sum is a complex number, under BN
    BNE = '( %s /\\ e e. %s )' % (BN, DVP)
    de0 = dvpel(w, BNE, 'e', d['pnn'], 'y')
    xec0 = de0['st']([de0['st']([vcc(w, BNE, lift(w, d['vf'], BNE), de0['nn'], 'e'),
                                 lcc(w, BNE, lift(w, d['lf'], BNE), de0['nn'], 'e')], 'mulcld',
                                '%s e. CC' % AU('e')),
                      w.s([], '0cnd', '( %s -> 0 e. CC )' % BNE)], 'ifcld', '%s e. CC' % XI('e'))
    ecc = sn([lift(w, d['finP'], BN), xec0], 'fsumcl', '%s e. CC' % TE)
    # ---- the indicator closures under BNU and BNUE
    BNU = '( %s /\\ u e. %s )' % (BN, DVP)
    du = dvpel(w, BNU, 'u', d['pnn'], 'y')
    su = du['st']
    auu = su([vcc(w, BNU, lift(w, d['vf'], BNU), du['nn'], 'u'),
              lcc(w, BNU, lift(w, d['lf'], BNU), du['nn'], 'u')], 'mulcld', '%s e. CC' % AU('u'))
    xuc = su([auu, w.s([], '0cnd', '( %s -> 0 e. CC )' % BNU)], 'ifcld', '%s e. CC' % XI('u'))
    BNUE = '( %s /\\ e e. %s )' % (BNU, DVP)
    de = dvpel(w, BNUE, 'e', d['pnn'], 'y')
    se = de['st']
    aue = se([vcc(w, BNUE, lift(w, d['vf'], BNUE), de['nn'], 'e'),
              lcc(w, BNUE, lift(w, d['lf'], BNUE), de['nn'], 'e')], 'mulcld', '%s e. CC' % AU('e'))
    xec = se([aue, w.s([], '0cnd', '( %s -> 0 e. CC )' % BNUE)], 'ifcld', '%s e. CC' % XI('e'))
    # ---- the summand
    sp1 = se([se([lift(w, igtc, BNUE), w.inst('ifmulz2')], 'syl',
                 '( %s x. if ( ( n || u /\\ n || e ) , %s , 0 ) ) = %s' % (IGTN, KK, IFN))],
             'eqcomd', '%s = ( %s x. if ( ( n || u /\\ n || e ) , %s , 0 ) )' % (IFN, IGTN, KK))
    sp2 = se([se([se([lift(w, auu, BNUE), aue], 'jca',
                     '( %s e. CC /\\ %s e. CC )' % (AU('u'), AU('e'))), w.inst('ifmul2')], 'syl',
                 'if ( ( n || u /\\ n || e ) , %s , 0 ) = ( %s x. %s )'
                 % (KK, XI('u'), XI('e')))], 'oveq2d',
             '( %s x. if ( ( n || u /\\ n || e ) , %s , 0 ) ) = ( %s x. ( %s x. %s ) )'
             % (IGTN, KK, IGTN, XI('u'), XI('e')))
    sp3 = se([se([lift(w, igtc, BNUE), lift(w, xuc, BNUE), xec], 'mulassd',
                 '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )'
                 % (IGTN, XI('u'), XI('e'), IGTN, XI('u'), XI('e')))], 'eqcomd',
             '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )'
             % (IGTN, XI('u'), XI('e'), IGTN, XI('u'), XI('e')))
    term = se([sp1, se([sp2, sp3], 'eqtrd',
                       '( %s x. if ( ( n || u /\\ n || e ) , %s , 0 ) ) = '
                       '( ( %s x. %s ) x. %s )' % (IGTN, KK, IGTN, XI('u'), XI('e')))], 'eqtrd',
              '%s = ( ( %s x. %s ) x. %s )' % (IFN, IGTN, XI('u'), XI('e')))
    # ---- the e-sum
    igtxu = su([lift(w, igtc, BNU), xuc], 'mulcld', '( %s x. %s ) e. CC' % (IGTN, XI('u')))
    esum = su([su([lift(w, d['finP'], BNU), igtxu, xec], 'fsummulc2',
                  '( ( %s x. %s ) x. %s ) = sum_ e e. %s ( ( %s x. %s ) x. %s )'
                  % (IGTN, XI('u'), TE, DVP, IGTN, XI('u'), XI('e')))], 'eqcomd',
              'sum_ e e. %s ( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )'
              % (DVP, IGTN, XI('u'), XI('e'), IGTN, XI('u'), TE))
    ein = su([su([term], 'sumeq2dv',
                 'sum_ e e. %s %s = sum_ e e. %s ( ( %s x. %s ) x. %s )'
                 % (DVP, IFN, DVP, IGTN, XI('u'), XI('e'))), esum], 'eqtrd',
             'sum_ e e. %s %s = ( ( %s x. %s ) x. %s )' % (DVP, IFN, IGTN, XI('u'), TE))
    swap = su([lift(w, igtc, BNU), xuc, lift(w, ecc, BNU)], 'mul32d',
              '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )'
              % (IGTN, XI('u'), TE, IGTN, TE, XI('u')))
    ubody = su([ein, swap], 'eqtrd',
               'sum_ e e. %s %s = ( ( %s x. %s ) x. %s )' % (DVP, IFN, IGTN, TE, XI('u')))
    igtte = sn([igtc, ecc], 'mulcld', '( %s x. %s ) e. CC' % (IGTN, TE))
    usum = sn([sn([d['finP'] and lift(w, d['finP'], BN), igtte, xuc], 'fsummulc2',
                  '( ( %s x. %s ) x. %s ) = sum_ u e. %s ( ( %s x. %s ) x. %s )'
                  % (IGTN, TE, TU, DVP, IGTN, TE, XI('u')))], 'eqcomd',
              'sum_ u e. %s ( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )'
              % (DVP, IGTN, TE, XI('u'), IGTN, TE, TU))
    dbl = sn([sn([ubody], 'sumeq2dv',
                 'sum_ u e. %s sum_ e e. %s %s = sum_ u e. %s ( ( %s x. %s ) x. %s )'
                 % (DVP, DVP, IFN, DVP, IGTN, TE, XI('u'))), usum], 'eqtrd',
             'sum_ u e. %s sum_ e e. %s %s = ( ( %s x. %s ) x. %s )'
             % (DVP, DVP, IFN, IGTN, TE, TU))
    # ---- the two sums are the same
    hcbe = w.s([w.s([], 'breq2', '( e = j -> ( n || e <-> n || j ) )'),
                w.s([w.s([], 'fveq2', '( e = j -> ( V ` e ) = ( V ` j ) )'),
                     w.s([], 'fveq2', '( e = j -> ( L ` e ) = ( L ` j ) )')], 'oveq12d',
                    '( e = j -> %s = %s )' % (AU('e'), AU('j')))], 'ifbieq1d',
               '( e = j -> %s = %s )' % (XI('e'), XI('j')))
    cbe = sn([w.s([hcbe], 'cbvsumv', '%s = %s' % (TE, TJ))], 'a1i', '%s = %s' % (TE, TJ))
    hcbu = w.s([w.s([], 'breq2', '( u = j -> ( n || u <-> n || j ) )'),
                w.s([w.s([], 'fveq2', '( u = j -> ( V ` u ) = ( V ` j ) )'),
                     w.s([], 'fveq2', '( u = j -> ( L ` u ) = ( L ` j ) )')], 'oveq12d',
                    '( u = j -> %s = %s )' % (AU('u'), AU('j')))], 'ifbieq1d',
               '( u = j -> %s = %s )' % (XI('u'), XI('j')))
    cbu = sn([w.s([hcbu], 'cbvsumv', '%s = %s' % (TU, TJ))], 'a1i', '%s = %s' % (TU, TJ))
    jcc = sn([cbe, ecc], 'eqeltrrd', '%s e. CC' % TJ)
    conv = sn([sn([cbe], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (IGTN, TE, IGTN, TJ)), cbu],
              'oveq12d',
              '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (IGTN, TE, TU, IGTN, TJ, TJ))
    assoc = sn([igtc, jcc, jcc], 'mulassd',
               '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (IGTN, TJ, TJ, IGTN, TJ, TJ))
    sq = sn([sn([jcc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (TJ, TJ, TJ))], 'oveq2d',
            '( %s x. ( %s ^ 2 ) ) = ( %s x. ( %s x. %s ) )' % (IGTN, TJ, IGTN, TJ, TJ))
    w.qed([dbl, sn([sn([conv, assoc], 'eqtrd',
                       '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )'
                       % (IGTN, TE, TU, IGTN, TJ, TJ)),
                    sn([sq], 'eqcomd',
                       '( %s x. ( %s x. %s ) ) = %s' % (IGTN, TJ, TJ, SQT))], 'eqtrd',
                   '( ( %s x. %s ) x. %s ) = %s' % (IGTN, TE, TU, SQT))], 'eqtrd',
          '( %s -> sum_ u e. %s sum_ e e. %s %s = %s )' % (BN, DVP, DVP, IFN, SQT))
    return w



def mpgen():
    w = W('mpgen', 'The Lambda squared main term as a diagonalised quadratic form with the '
                   'reciprocal Selberg terms as eigenvalues (Mathlib '
                   'mainSum_lambdaSquared_eq_sum_mul_sum_sq).')
    d = base(w)
    st = d['st']
    e1 = st([], 'mpgex1', 'sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ d e. %s %s'
             % (DVP, LSD, DVP, TRIP))
    e2 = st([], 'mpgex2', 'sum_ d e. %s %s = %s' % (DVP, TRIP, DBL))
    e3 = st([], 'mpggcd', '%s = %s' % (DBL, TRN))
    e4 = st([], 'mpgsw', '%s = %s' % (TRN, SWN))
    BN = '( %s /\\ n e. %s )' % (B, DVP)
    e5 = st([w.s([], 'mpgsq',
                 '( %s -> sum_ u e. %s sum_ e e. %s %s = %s )' % (BN, DVP, DVP, IFN, SQT))],
            'sumeq2dv', '%s = sum_ n e. %s %s' % (SWN, DVP, SQT))
    c1 = st([e1, e2], 'eqtrd', 'sum_ d e. %s ( %s x. ( V ` d ) ) = %s' % (DVP, LSD, DBL))
    c2 = st([e3, e4], 'eqtrd', '%s = %s' % (DBL, SWN))
    w.qed([c1, st([c2, e5], 'eqtrd', '%s = sum_ n e. %s %s' % (DBL, DVP, SQT))], 'eqtrd',
          '( %s -> sum_ d e. %s ( %s x. ( V ` d ) ) = sum_ n e. %s %s )' % (B, DVP, LSD, DVP, SQT))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['mpgex1']:
        globals()[f]().run()
