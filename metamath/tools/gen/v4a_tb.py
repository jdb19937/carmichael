"""Sortie v4a: the twin-sieve hypothesis bundle and the lower bound for the bounding sum."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import CS, DEN, RS, mkst, csel, rsel
from cl import lift
from lin import linarith

SH1 = ('( ( A e. Fin /\\ A C_ NN /\\ W : NN --> RR ) /\\ '
       '( A. k e. NN 0 <_ ( W ` k ) /\\ X e. RR /\\ ( Y e. RR /\\ 1 <_ Y ) ) )')
SHP = '( P e. NN /\\ ( mmu ` P ) =/= 0 )'
SHVM = ('A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> '
        '( V ` ( a x. b ) ) = ( ( V ` a ) x. ( V ` b ) ) )')
SHVP = 'A. s e. Prime ( s || P -> ( 0 < ( V ` s ) /\\ ( V ` s ) < 1 ) )'
SHV3 = '( %s /\\ %s )' % (SHVM, SHVP)
SHV = '( V : NN --> RR /\\ ( V ` 1 ) = 1 /\\ %s )' % SHV3
SH2 = '( %s /\\ %s )' % (SHP, SHV)
SH = '( %s /\\ %s )' % (SH1, SH2)

TBODY = ('( ( y || P -> ( ( V ` y ) = ( 2 / y ) /\\ -. y || ( 2 x. M ) ) ) /\\ '
         '( ( y <_ Z /\\ -. y || ( 2 x. M ) ) -> y || P ) )')
TMR = '( M e. NN /\\ Z e. NN /\\ Y = ( Z ^ 2 ) )'
TRAL = 'A. y e. Prime %s' % TBODY
TB = '( %s /\\ %s /\\ %s )' % (SH, TMR, TRAL)


def shparts(w, st, l1):
    """extract the conjuncts of SH from a step proving ( ante -> SH )"""
    d = {}
    d['sh'] = l1
    b = st([l1], 'simprd', SH2)
    bp = st([b], 'simpld', SHP)
    d['pnn'] = st([bp], 'simpld', 'P e. NN')
    d['psqf'] = st([bp], 'simprd', '( mmu ` P ) =/= 0')
    bv = st([b], 'simprd', SHV)
    d['vf'] = st([bv], 'simp1d', 'V : NN --> RR')
    d['vlt'] = st([st([bv], 'simp3d', SHV3)], 'simprd', SHVP)
    return d


AP3 = '( %s /\\ ( D e. Prime /\\ D || P ) )' % TB


def twinp3():
    w = WS('twinp3', 'Every prime divisor of the sifting product is at least 3, has density '
                     '2 over itself, and does not divide twice the multiplier.')
    st = mkst(w, AP3)
    tmid = st([], 'simpl', '( %s /\\ %s /\\ %s )' % (SH, TMR, TRAL))
    sh = shparts(w, st, st([tmid], 'simp1d', SH))
    mnn = st([st([tmid], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    ral = st([tmid], 'simp3d', TRAL)
    dpair = st([], 'simpr', '( D e. Prime /\\ D || P )')
    dprm = st([dpair], 'simpld', 'D e. Prime')
    ddp = st([dpair], 'simprd', 'D || P')
    idy = w.s([], 'id', '( y = D -> y = D )')
    sbs, newb = w.wcongr(TBODY, {'y': 'D'}, 'y = D', {'y': idy})
    inst = st([sbs, ral, dprm], 'rspcdva', newb)
    c1 = st([st([inst], 'simpld',
                '( D || P -> ( ( V ` D ) = ( 2 / D ) /\\ -. D || ( 2 x. M ) ) )'), ddp],
            'mpd', '( ( V ` D ) = ( 2 / D ) /\\ -. D || ( 2 x. M ) )')
    vd = st([c1], 'simpld', '( V ` D ) = ( 2 / D )')
    ndm = st([c1], 'simprd', '-. D || ( 2 x. M )')
    ids = w.s([], 'id', '( s = D -> s = D )')
    sbs2, newb2 = w.wcongr('( s || P -> ( 0 < ( V ` s ) /\\ ( V ` s ) < 1 ) )', {'s': 'D'},
                           's = D', {'s': ids})
    inst2 = st([sbs2, sh['vlt'], dprm], 'rspcdva', newb2)
    vlt1 = st([st([inst2, ddp], 'mpd', '( 0 < ( V ` D ) /\\ ( V ` D ) < 1 )')], 'simprd',
              '( V ` D ) < 1')
    dnn = st([dprm, w.inst('prmnn')], 'syl', 'D e. NN')
    drp = st([dnn], 'nnrpd', 'D e. RR+')
    two = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    d2 = st([st([two, drp, w.inst('divlt1lt')], 'syl2anc', '( ( 2 / D ) < 1 <-> 2 < D )'),
             st([vd, vlt1], 'eqbrtrrd', '( 2 / D ) < 1')], 'mpbid', '2 < D')
    d3 = st([st([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'a1i', '( 2 + 1 ) = 3'),
             st([st([st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'),
                    st([dnn], 'nnzd', 'D e. ZZ'), w.inst('zltp1le')], 'syl2anc',
                   '( 2 < D <-> ( 2 + 1 ) <_ D )'), d2], 'mpbid', '( 2 + 1 ) <_ D')],
            'eqbrtrrd', '3 <_ D')
    w.qed([d3, vd, ndm], '3jca',
          '( %s -> ( 3 <_ D /\\ ( V ` D ) = ( 2 / D ) /\\ -. D || ( 2 x. M ) ) )' % AP3)
    return w


# ------------------------------------------------- the primes of J divide P
PFQ = '{ q e. Prime | q || %s }'
AJS = '( %s /\ ( J e. NN /\ J <_ Z /\ ( J gcd ( 2 x. M ) ) = 1 ) )' % TB


def twinps():
    w = WS('twinps', 'Every prime divisor of a positive integer at most Z coprime to twice '
                     'the multiplier divides the sifting product.')
    st = mkst(w, AJS)
    tmid = st([], 'simpl', '( %s /\ %s /\ %s )' % (SH, TMR, TRAL))
    sh = shparts(w, st, st([tmid], 'simp1d', SH))
    ral = st([tmid], 'simp3d', TRAL)
    jtr = st([], 'simpr', '( J e. NN /\ J <_ Z /\ ( J gcd ( 2 x. M ) ) = 1 )')
    jnn = st([jtr], 'simp1d', 'J e. NN')
    jlez = st([jtr], 'simp2d', 'J <_ Z')
    jcop = st([jtr], 'simp3d', '( J gcd ( 2 x. M ) ) = 1')
    mnn = st([st([tmid], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    znn = st([st([tmid], 'simp2d', TMR)], 'simp2d', 'Z e. NN')
    AD = '( %s /\ d e. %s )' % (AJS, PFQ % 'J')
    sd = mkst(w, AD)
    eld = w.s([w.s([], 'breq1', '( q = d -> ( q || J <-> d || J ) )')], 'elrab',
              '( d e. %s <-> ( d e. Prime /\ d || J ) )' % (PFQ % 'J'))
    dm = sd([sd([eld], 'a1i', '( d e. %s <-> ( d e. Prime /\ d || J ) )' % (PFQ % 'J')),
             sd([], 'simpr', 'd e. %s' % (PFQ % 'J'))], 'mpbid',
            '( d e. Prime /\ d || J )')
    dprm = sd([dm], 'simpld', 'd e. Prime')
    ddj = sd([dm], 'simprd', 'd || J')
    dnn = sd([dprm, w.inst('prmnn')], 'syl', 'd e. NN')
    dz = sd([dnn], 'nnzd', 'd e. ZZ')
    dlej = sd([sd([dz, lift(w, jnn, AD), w.inst('dvdsle')], 'syl2anc',
                  '( d || J -> d <_ J )'), ddj], 'mpd', 'd <_ J')
    dlez = sd([sd([dnn], 'nnred', 'd e. RR'), sd([lift(w, jnn, AD)], 'nnred', 'J e. RR'),
               sd([lift(w, znn, AD)], 'nnred', 'Z e. RR'), dlej, lift(w, jlez, AD)], 'letrd',
              'd <_ Z')
    # d does not divide 2 M
    ADM = '( %s /\ d || ( 2 x. M ) )' % AD
    sdm = mkst(w, ADM)
    dg = sdm([sdm([sdm([lift(w, dz, ADM), lift(w, sd([lift(w, jnn, AD)], 'nnzd', 'J e. ZZ'),
                                               ADM),
                        sdm([sdm([sdm([], '2red', '2 e. RR')], 'recnd', '2 e. CC')], 'id',
                            'z')], '3jca', 'z')], 'id', 'z')], 'id', 'z')
    for _ in range(6):
        w.lines.pop()
    twoz = sdm([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    mz2 = sdm([lift(w, mnn, ADM)], 'nnzd', 'M e. ZZ')
    tmz = sdm([twoz, mz2], 'zmulcld', '( 2 x. M ) e. ZZ')
    jz2 = sdm([lift(w, jnn, ADM)], 'nnzd', 'J e. ZZ')
    dgc = sdm([sdm([sdm([lift(w, dz, ADM), jz2, tmz], '3jca',
                        '( d e. ZZ /\ J e. ZZ /\ ( 2 x. M ) e. ZZ )'), w.inst('dvdsgcd')],
                   'syl', '( ( d || J /\ d || ( 2 x. M ) ) -> d || ( J gcd ( 2 x. M ) ) )'),
               sdm([lift(w, ddj, ADM), sdm([], 'simpr', 'd || ( 2 x. M )')], 'jca',
                   '( d || J /\ d || ( 2 x. M ) )')], 'mpd', 'd || ( J gcd ( 2 x. M ) )')
    dd1 = sdm([dgc, lift(w, jcop, ADM)], 'breqtrd', 'd || 1')
    nd1 = sd([dprm, w.inst('nprmdvds1')], 'syl', '-. d || 1')
    ndm = sd([nd1, dd1], 'mtand', '-. d || ( 2 x. M )')
    idd = w.s([], 'id', '( y = d -> y = d )')
    sbs, newb = w.wcongr(TBODY, {'y': 'd'}, 'y = d', {'y': idd})
    inst = sd([sbs, lift(w, ral, AD), dprm], 'rspcdva', newb)
    ddp = sd([sd([inst], 'simprd',
                 '( ( d <_ Z /\ -. d || ( 2 x. M ) ) -> d || P )'),
              sd([dlez, ndm], 'jca', '( d <_ Z /\ -. d || ( 2 x. M ) )')], 'mpd', 'd || P')
    elp = w.s([w.s([], 'breq1', '( q = d -> ( q || P <-> d || P ) )')], 'elrab',
              '( d e. %s <-> ( d e. Prime /\ d || P ) )' % (PFQ % 'P'))
    inp = sd([sd([dprm, ddp], 'jca', '( d e. Prime /\ d || P )'),
              sd([elp], 'a1i', '( d e. %s <-> ( d e. Prime /\ d || P ) )' % (PFQ % 'P'))],
             'mpbird', 'd e. %s' % (PFQ % 'P'))
    w.qed([st([inp], 'ex', '( d e. %s -> d e. %s )' % (PFQ % 'J', PFQ % 'P'))], 'ssrdv',
          '( %s -> %s C_ %s )' % (AJS, PFQ % 'J', PFQ % 'P'))
    return w


# ------------------------------------------- the primes of the gcd with P
AJG = '( %s /\ ( J e. NN /\ %s C_ %s ) )' % (TB, PFQ % 'J', PFQ % 'P')


def twinpg():
    w = WS('twinpg', 'The prime divisors of the greatest common divisor of the sifting '
                     'product and J are the prime divisors of J.')
    st = mkst(w, AJG)
    tmid = st([], 'simpl', '( %s /\ %s /\ %s )' % (SH, TMR, TRAL))
    sh = shparts(w, st, st([tmid], 'simp1d', SH))
    jpair = st([], 'simpr', '( J e. NN /\ %s C_ %s )' % (PFQ % 'J', PFQ % 'P'))
    jnn = st([jpair], 'simpld', 'J e. NN')
    pss = st([jpair], 'simprd', '%s C_ %s' % (PFQ % 'J', PFQ % 'P'))
    pnn = sh['pnn']
    pz = st([pnn], 'nnzd', 'P e. ZZ')
    jz = st([jnn], 'nnzd', 'J e. ZZ')
    gnn = st([pnn, jnn, w.inst('gcdnncl')], 'syl2anc', '( P gcd J ) e. NN')
    gz = st([gnn], 'nnzd', '( P gcd J ) e. ZZ')
    gdj = st([st([pz, jz, w.inst('gcddvds')], 'syl2anc',
                 '( ( P gcd J ) || P /\ ( P gcd J ) || J )')], 'simprd', '( P gcd J ) || J')
    elgd = w.s([w.s([], 'breq1',
                    '( q = d -> ( q || ( P gcd J ) <-> d || ( P gcd J ) ) )')], 'elrab',
               '( d e. %s <-> ( d e. Prime /\ d || ( P gcd J ) ) )' % (PFQ % '( P gcd J )'))
    eljd = w.s([w.s([], 'breq1', '( q = d -> ( q || J <-> d || J ) )')], 'elrab',
               '( d e. %s <-> ( d e. Prime /\ d || J ) )' % (PFQ % 'J'))
    elpd = w.s([w.s([], 'breq1', '( q = d -> ( q || P <-> d || P ) )')], 'elrab',
               '( d e. %s <-> ( d e. Prime /\ d || P ) )' % (PFQ % 'P'))
    # forward inclusion
    AD1 = '( %s /\ d e. %s )' % (AJG, PFQ % '( P gcd J )')
    s1 = mkst(w, AD1)
    m1 = s1([s1([elgd], 'a1i',
                '( d e. %s <-> ( d e. Prime /\ d || ( P gcd J ) ) )'
                % (PFQ % '( P gcd J )')),
             s1([], 'simpr', 'd e. %s' % (PFQ % '( P gcd J )'))], 'mpbid',
            '( d e. Prime /\ d || ( P gcd J ) )')
    d1p = s1([m1], 'simpld', 'd e. Prime')
    d1g = s1([m1], 'simprd', 'd || ( P gcd J )')
    d1z = s1([s1([d1p, w.inst('prmnn')], 'syl', 'd e. NN')], 'nnzd', 'd e. ZZ')
    d1j = s1([s1([s1([d1z, lift(w, gz, AD1), lift(w, jz, AD1)], '3jca',
                     '( d e. ZZ /\ ( P gcd J ) e. ZZ /\ J e. ZZ )'), w.inst('dvdstr')], 'syl',
                  '( ( d || ( P gcd J ) /\ ( P gcd J ) || J ) -> d || J )'),
              s1([d1g, lift(w, gdj, AD1)], 'jca',
                 '( d || ( P gcd J ) /\ ( P gcd J ) || J )')], 'mpd', 'd || J')
    in1 = s1([s1([d1p, d1j], 'jca', '( d e. Prime /\ d || J )'),
              s1([eljd], 'a1i', '( d e. %s <-> ( d e. Prime /\ d || J ) )' % (PFQ % 'J'))],
             'mpbird', 'd e. %s' % (PFQ % 'J'))
    ss1 = st([st([in1], 'ex', '( d e. %s -> d e. %s )' % (PFQ % '( P gcd J )', PFQ % 'J'))],
             'ssrdv', '%s C_ %s' % (PFQ % '( P gcd J )', PFQ % 'J'))
    # backward inclusion
    AD2 = '( %s /\ d e. %s )' % (AJG, PFQ % 'J')
    s2 = mkst(w, AD2)
    m2 = s2([s2([eljd], 'a1i', '( d e. %s <-> ( d e. Prime /\ d || J ) )' % (PFQ % 'J')),
             s2([], 'simpr', 'd e. %s' % (PFQ % 'J'))], 'mpbid',
            '( d e. Prime /\ d || J )')
    d2p = s2([m2], 'simpld', 'd e. Prime')
    d2j = s2([m2], 'simprd', 'd || J')
    d2z = s2([s2([d2p, w.inst('prmnn')], 'syl', 'd e. NN')], 'nnzd', 'd e. ZZ')
    inP = s2([lift(w, pss, AD2), s2([], 'simpr', 'd e. %s' % (PFQ % 'J'))], 'sseldd',
             'd e. %s' % (PFQ % 'P'))
    d2P = s2([s2([s2([elpd], 'a1i',
                     '( d e. %s <-> ( d e. Prime /\ d || P ) )' % (PFQ % 'P')), inP], 'mpbid',
                 '( d e. Prime /\ d || P )')], 'simprd', 'd || P')
    d2g = s2([s2([s2([d2z, lift(w, pz, AD2), lift(w, jz, AD2)], '3jca',
                     '( d e. ZZ /\ P e. ZZ /\ J e. ZZ )'), w.inst('dvdsgcd')], 'syl',
                 '( ( d || P /\ d || J ) -> d || ( P gcd J ) )'),
              s2([d2P, d2j], 'jca', '( d || P /\ d || J )')], 'mpd', 'd || ( P gcd J )')
    in2 = s2([s2([d2p, d2g], 'jca', '( d e. Prime /\ d || ( P gcd J ) )'),
              s2([elgd], 'a1i',
                 '( d e. %s <-> ( d e. Prime /\ d || ( P gcd J ) ) )'
                 % (PFQ % '( P gcd J )'))], 'mpbird', 'd e. %s' % (PFQ % '( P gcd J )'))
    ss2 = st([st([in2], 'ex', '( d e. %s -> d e. %s )' % (PFQ % 'J', PFQ % '( P gcd J )'))],
             'ssrdv', '%s C_ %s' % (PFQ % 'J', PFQ % '( P gcd J )'))
    w.qed([ss1, ss2], 'eqssd',
          '( %s -> %s = %s )' % (AJG, PFQ % '( P gcd J )', PFQ % 'J'))
    return w


# ---------------------------------------------- coprimality from the prime set
ALG = ('( %s /\ ( L e. NN /\ L || P ) /\ ( J e. NN /\ %s = %s ) )'
       % (TB, PFQ % 'J', PFQ % 'L'))


def twincop():
    w = WS('twincop', 'An integer whose prime divisors are those of a divisor of the sifting '
                      'product is coprime to twice the multiplier.')
    st = mkst(w, ALG)
    tmid = st([], 'simp1', '( %s /\ %s /\ %s )' % (SH, TMR, TRAL))
    sh = shparts(w, st, st([tmid], 'simp1d', SH))
    mnn = st([st([tmid], 'simp2d', TMR)], 'simp1d', 'M e. NN')
    lpair = st([], 'simp2', '( L e. NN /\ L || P )')
    lnn = st([lpair], 'simpld', 'L e. NN')
    ldp = st([lpair], 'simprd', 'L || P')
    jpair = st([], 'simp3', '( J e. NN /\ %s = %s )' % (PFQ % 'J', PFQ % 'L'))
    jnn = st([jpair], 'simpld', 'J e. NN')
    pfeq = st([jpair], 'simprd', '%s = %s' % (PFQ % 'J', PFQ % 'L'))
    tmnn = st([st([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN'), mnn], 'nnmulcld',
              '( 2 x. M ) e. NN')
    lz = st([lnn], 'nnzd', 'L e. ZZ')
    pz = st([sh['pnn']], 'nnzd', 'P e. ZZ')
    eljp = w.s([w.s([], 'breq1', '( q = p -> ( q || J <-> p || J ) )')], 'elrab',
               '( p e. %s <-> ( p e. Prime /\ p || J ) )' % (PFQ % 'J'))
    ellp = w.s([w.s([], 'breq1', '( q = p -> ( q || L <-> p || L ) )')], 'elrab',
               '( p e. %s <-> ( p e. Prime /\ p || L ) )' % (PFQ % 'L'))
    AP = '( %s /\ p e. Prime )' % ALG
    sp = mkst(w, AP)
    pprm = sp([], 'simpr', 'p e. Prime')
    pz2 = sp([sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')], 'nnzd', 'p e. ZZ')
    APJ = '( %s /\ p || J )' % AP
    spj = mkst(w, APJ)
    inj = spj([spj([lift(w, pprm, APJ), spj([], 'simpr', 'p || J')], 'jca',
                   '( p e. Prime /\ p || J )'),
               spj([eljp], 'a1i',
                   '( p e. %s <-> ( p e. Prime /\ p || J ) )' % (PFQ % 'J'))], 'mpbird',
              'p e. %s' % (PFQ % 'J'))
    inl = spj([inj, lift(w, pfeq, APJ)], 'eleqtrd', 'p e. %s' % (PFQ % 'L'))
    pdl = spj([spj([spj([ellp], 'a1i',
                        '( p e. %s <-> ( p e. Prime /\ p || L ) )' % (PFQ % 'L')), inl],
                   'mpbid', '( p e. Prime /\ p || L )')], 'simprd', 'p || L')
    pdP = spj([spj([spj([lift(w, pz2, APJ), lift(w, lz, APJ), lift(w, pz, APJ)], '3jca',
                        '( p e. ZZ /\ L e. ZZ /\ P e. ZZ )'), w.inst('dvdstr')], 'syl',
                   '( ( p || L /\ L || P ) -> p || P )'),
               spj([pdl, lift(w, ldp, APJ)], 'jca', '( p || L /\ L || P )')], 'mpd', 'p || P')
    p3 = spj([spj([spj([spj([lift(w, tmid, APJ)], 'id', 'z')], 'id', 'z')], 'id', 'z')],
             'id', 'z')
    for _ in range(4):
        w.lines.pop()
    tb3 = spj([lift(w, tmid, APJ), spj([lift(w, pprm, APJ), pdP], 'jca',
                                       '( p e. Prime /\ p || P )')], 'jca',
              '( ( %s /\ %s /\ %s ) /\ ( p e. Prime /\ p || P ) )' % (SH, TMR, TRAL))
    ndm = spj([spj([tb3, w.inst('twinp3')], 'syl',
                   '( 3 <_ p /\ ( V ` p ) = ( 2 / p ) /\ -. p || ( 2 x. M ) )')], 'simp3d',
              '-. p || ( 2 x. M )')
    imp = sp([ndm], 'ex', '( p || J -> -. p || ( 2 x. M ) )')
    nand = sp([sp([w.s([], 'imnan',
                       '( ( p || J -> -. p || ( 2 x. M ) ) <-> '
                       '-. ( p || J /\ p || ( 2 x. M ) ) )')], 'a1i',
                  '( ( p || J -> -. p || ( 2 x. M ) ) <-> '
                  '-. ( p || J /\ p || ( 2 x. M ) ) )'), imp], 'mpbid',
              '-. ( p || J /\ p || ( 2 x. M ) )')
    ral = st([nand], 'ralrimiva', 'A. p e. Prime -. ( p || J /\ p || ( 2 x. M ) )')
    nex = st([st([w.s([], 'ralnex',
                      '( A. p e. Prime -. ( p || J /\ p || ( 2 x. M ) ) <-> '
                      '-. E. p e. Prime ( p || J /\ p || ( 2 x. M ) ) )')], 'a1i',
                 '( A. p e. Prime -. ( p || J /\ p || ( 2 x. M ) ) <-> '
                 '-. E. p e. Prime ( p || J /\ p || ( 2 x. M ) ) )'), ral], 'mpbid',
              '-. E. p e. Prime ( p || J /\ p || ( 2 x. M ) )')
    bic = st([jnn, tmnn], 'prmdvdsncoprmbd',
             '( E. p e. Prime ( p || J /\ p || ( 2 x. M ) ) <-> ( J gcd ( 2 x. M ) ) =/= 1 )')
    w.qed([st([st([bic, nex], 'mtbid', '-. ( J gcd ( 2 x. M ) ) =/= 1')], 'neqned', 'z')],
          'id', 'z')
    for _ in range(2):
        w.lines.pop()
    nn = st([bic, nex], 'mtbid', '-. ( J gcd ( 2 x. M ) ) =/= 1')
    w.qed([nn, w.inst('nne')], 'sylib',
          '( %s -> ( J gcd ( 2 x. M ) ) = 1 )' % ALG)
    return w


# ------------------------------------------------- the fibre biconditional
AGF = ('( %s /\ ( L e. NN /\ L || P ) /\ '
       '( J e. NN /\ J <_ Z /\ ( J gcd ( 2 x. M ) ) = 1 ) )' % TB)


def twingf():
    w = WS('twingf', 'For J at most Z and coprime to twice the multiplier, the greatest '
                     'common divisor of the sifting product with J is a given divisor L of '
                     'the sifting product exactly when J and L have the same prime divisors.')
    st = mkst(w, AGF)
    tmid = st([], 'simp1', '( %s /\ %s /\ %s )' % (SH, TMR, TRAL))
    sh = shparts(w, st, st([tmid], 'simp1d', SH))
    pnn = sh['pnn']
    psqf = sh['psqf']
    lpair = st([], 'simp2', '( L e. NN /\ L || P )')
    lnn = st([lpair], 'simpld', 'L e. NN')
    ldp = st([lpair], 'simprd', 'L || P')
    jtr = st([], 'simp3', '( J e. NN /\ J <_ Z /\ ( J gcd ( 2 x. M ) ) = 1 )')
    jnn = st([jtr], 'simp1d', 'J e. NN')
    gnn = st([pnn, jnn, w.inst('gcdnncl')], 'syl2anc', '( P gcd J ) e. NN')
    gdp = st([st([st([pnn], 'nnzd', 'P e. ZZ'), st([jnn], 'nnzd', 'J e. ZZ'),
                  w.inst('gcddvds')], 'syl2anc',
                 '( ( P gcd J ) || P /\ ( P gcd J ) || J )')], 'simpld', '( P gcd J ) || P')
    # squarefreeness of both divisors
    gsqf = st([st([st([pnn, gnn, gdp], '3jca',
                      '( P e. NN /\ ( P gcd J ) e. NN /\ ( P gcd J ) || P )'),
                   w.inst('dvdssqf')], 'syl',
                  '( ( mmu ` P ) =/= 0 -> ( mmu ` ( P gcd J ) ) =/= 0 )'), psqf], 'mpd',
              '( mmu ` ( P gcd J ) ) =/= 0')
    lsqf = st([st([st([pnn, lnn, ldp], '3jca', '( P e. NN /\ L e. NN /\ L || P )'),
                   w.inst('dvdssqf')], 'syl',
                  '( ( mmu ` P ) =/= 0 -> ( mmu ` L ) =/= 0 )'), psqf], 'mpd',
              '( mmu ` L ) =/= 0')
    gid = st([st([gnn, gsqf], 'jca',
                 '( ( P gcd J ) e. NN /\ ( mmu ` ( P gcd J ) ) =/= 0 )'),
              w.inst('sqfprodid')], 'syl',
             'prod_ p e. %s p = ( P gcd J )' % (PFQ % '( P gcd J )'))
    lid = st([st([lnn, lsqf], 'jca', '( L e. NN /\ ( mmu ` L ) =/= 0 )'),
              w.inst('sqfprodid')], 'syl', 'prod_ p e. %s p = L' % (PFQ % 'L'))
    # the prime set of the gcd
    ps = st([st([tmid, jtr], 'jca',
                '( ( %s /\ %s /\ %s ) /\ '
                '( J e. NN /\ J <_ Z /\ ( J gcd ( 2 x. M ) ) = 1 ) )' % (SH, TMR, TRAL)),
             w.inst('twinps')], 'syl', '%s C_ %s' % (PFQ % 'J', PFQ % 'P'))
    pg = st([st([tmid, st([jnn, ps], 'jca',
                          '( J e. NN /\ %s C_ %s )' % (PFQ % 'J', PFQ % 'P'))], 'jca',
                '( ( %s /\ %s /\ %s ) /\ ( J e. NN /\ %s C_ %s ) )'
                % (SH, TMR, TRAL, PFQ % 'J', PFQ % 'P')), w.inst('twinpg')], 'syl',
            '%s = %s' % (PFQ % '( P gcd J )', PFQ % 'J'))
    # forward
    AF = '( %s /\ L = ( P gcd J ) )' % AGF
    sf = mkst(w, AF)
    leq = sf([], 'simpr', 'L = ( P gcd J )')
    fw0 = sf([sf([leq], 'fveq2d', 'z')], 'id', 'z')
    for _ in range(2):
        w.lines.pop()
    pfl = sf([sf([leq], 'breq2d', '( q || L <-> q || ( P gcd J ) )')], 'id', 'z')
    w.lines.pop(); w.lines.pop()
    # L = ( P gcd J ) gives the prime sets equal by substitution
    subl = w.s([w.s([], 'breq2',
                    '( L = ( P gcd J ) -> ( q || L <-> q || ( P gcd J ) ) )')], 'rabbidv',
               '( L = ( P gcd J ) -> %s = %s )' % (PFQ % 'L', PFQ % '( P gcd J )'))
    fw = sf([sf([sf([subl], 'a1i',
                    '( L = ( P gcd J ) -> %s = %s )' % (PFQ % 'L', PFQ % '( P gcd J )')),
                 leq], 'mpd', '%s = %s' % (PFQ % 'L', PFQ % '( P gcd J )')),
             lift(w, pg, AF)], 'eqtrd', '%s = %s' % (PFQ % 'L', PFQ % 'J'))
    fwd = st([sf([fw], 'eqcomd', '%s = %s' % (PFQ % 'J', PFQ % 'L'))], 'ex',
             '( L = ( P gcd J ) -> %s = %s )' % (PFQ % 'J', PFQ % 'L'))
    # backward
    AB = '( %s /\ %s = %s )' % (AGF, PFQ % 'J', PFQ % 'L')
    sb = mkst(w, AB)
    pfjl = sb([], 'simpr', '%s = %s' % (PFQ % 'J', PFQ % 'L'))
    gl = sb([sb([lift(w, gid, AB)], 'eqcomd',
                '( P gcd J ) = prod_ p e. %s p' % (PFQ % '( P gcd J )')),
             sb([sb([sb([lift(w, pg, AB), pfjl], 'eqtrd',
                        '%s = %s' % (PFQ % '( P gcd J )', PFQ % 'L'))], 'prodeq1d',
                    'prod_ p e. %s p = prod_ p e. %s p'
                    % (PFQ % '( P gcd J )', PFQ % 'L')), lift(w, lid, AB)], 'eqtrd',
                'prod_ p e. %s p = L' % (PFQ % '( P gcd J )'))], 'eqtrd',
            '( P gcd J ) = L')
    bwd = st([sb([gl], 'eqcomd', 'L = ( P gcd J )')], 'ex',
             '( %s = %s -> L = ( P gcd J ) )' % (PFQ % 'J', PFQ % 'L'))
    w.qed([fwd, bwd], 'impbid',
          '( %s -> ( L = ( P gcd J ) <-> %s = %s ) )' % (AGF, PFQ % 'J', PFQ % 'L'))
    return w


ALL = {'twinp3': twinp3, 'twinps': twinps, 'twinpg': twinpg, 'twincop': twincop,
       'twingf': twingf}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
