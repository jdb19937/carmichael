"""Sortie ZBV, BVL2 section 3.1: the elementary core (RZA Lemma 3.1's inputs).

bvmusum     ( K e. NN -> sum_ d e. { x e. NN | x || K } ( mmu ` d ) = if ( K = 1 , 1 , 0 ) )
bvida       ( N e. NN -> sum_ n e. ( 1 ... N ) ( ( mmu ` n ) x. ( |_ ` ( N / n ) ) ) = 1 )
bvidb       ( N e. NN -> sum_ n e. ( 1 ... N ) ( ( ( mmu ` n ) / n ) x. sum_ m e. ( 1 ... ( |_ ` ( N / n ) ) ) ( 1 / m ) ) = 1 )
bvmharmlem1 ( ( X e. RR /\\ 1 <_ X ) -> ( X x. MH ) = ( 1 + sum_ n e. ( 1 ... ( |_ ` X ) ) ( ( mmu ` n ) x. FR(n) ) ) )
bvmharmlem2 ( ( X e. RR /\\ 1 <_ X ) -> ( abs ` sum_ n e. ( 1 ... ( |_ ` X ) ) ( ( mmu ` n ) x. FR(n) ) ) <_ ( X - 1 ) )
bvmharm     ( ( X e. RR /\\ 1 <_ X ) -> ( abs ` sum_ n e. ( 1 ... ( |_ ` X ) ) ( ( mmu ` n ) / n ) ) <_ 1 )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbvlib import *
from lin import linarith, nlinarith, lineq

DV = lambda n: '{ x e. NN | x || %s }' % n
MU = lambda n: '( mmu ` %s )' % n
IF1 = lambda n: 'if ( %s = 1 , 1 , 0 )' % n
FL = lambda e: '( |_ ` %s )' % e


def mufacts(w, ante, nnstep, n):
    """( mmu ` n ) e. ZZ, RR, CC from n e. NN"""
    st = mkst(w, ante)
    z = sy(w, ante, nnstep, 'mucl', '%s e. ZZ' % MU(n))
    r = st([z], 'zred', '%s e. RR' % MU(n))
    return z, r, st([r], 'recnd', '%s e. CC' % MU(n))


def bvmusum():
    w = W('bvmusum', 'The Moebius function sums to the indicator of 1 over the divisors, with the '
                     'divisor set written as { x e. NN | x || K } (musum).')
    A = 'K e. NN'
    st = mkst(w, A)
    ms = st([], 'musum', 'sum_ k e. { n e. NN | n || K } %s = %s' % (MU('k'), IF1('K')))
    rb = w.s([w.s([], 'breq1', '( n = x -> ( n || K <-> x || K ) )')], 'cbvrabv', '{ n e. NN | n || K } = %s' % DV('K'))
    s1 = w.s([rb], 'sumeq1i', 'sum_ k e. { n e. NN | n || K } %s = sum_ k e. %s %s' % (MU('k'), DV('K'), MU('k')))
    s2 = w.s([w.s([], 'fveq2', '( k = d -> %s = %s )' % (MU('k'), MU('d')))], 'cbvsumv', 'sum_ k e. %s %s = sum_ d e. %s %s' % (DV('K'), MU('k'), DV('K'), MU('d')))
    eq = st([w.s([s1, s2], 'eqtri', 'sum_ k e. { n e. NN | n || K } %s = sum_ d e. %s %s' % (MU('k'), DV('K'), MU('d')))], 'a1i',
            'sum_ k e. { n e. NN | n || K } %s = sum_ d e. %s %s' % (MU('k'), DV('K'), MU('d')))
    w.qed([eq, ms], 'eqtr3d', '( %s -> sum_ d e. %s %s = %s )' % (A, DV('K'), MU('d'), IF1('K')))
    return w


def hyper(w, PH, nre, B, C, sub, bcl):
    """dvdsflsumcom at A := N with body B (in n, d) and C = B[n := d m]; sub proves the
    substitution hypothesis, bcl proves ( ( PH /\\ ( n e. ( 1 ... ( |_ ` N ) ) /\\ d e. DV(n) ) ) -> B e. CC )"""
    st = mkst(w, PH)
    return st([sub, nre, bcl], 'dvdsflsumcom',
              'sum_ n e. ( 1 ... %s ) sum_ d e. %s %s = sum_ d e. ( 1 ... %s ) sum_ m e. ( 1 ... %s ) %s'
              % (FL('N'), DV('n'), B, FL('N'), FL('( N / d )'), C))


def bvida():
    w = W('bvida', 'Identity (A): the Moebius function against the integer parts N / n sums to 1 '
                   '(Lean sum_moebius_mul_div_eq_one), by the hyperbola swap and musum.')
    PH = 'N e. NN'
    st = mkst(w, PH)
    nnn = st([], 'id', PH)
    nre = st([nnn], 'nnred', 'N e. RR'); nz = st([nnn], 'nnzd', 'N e. ZZ')
    fl = sy(w, PH, nz, 'flid', '%s = N' % FL('N'))
    RN = '( 1 ... %s )' % FL('N')
    A3 = '( %s /\\ ( n e. %s /\\ d e. %s ) )' % (PH, RN, DV('n'))
    s3 = mkst(w, A3)
    dnn = sy(w, A3, s3([], 'simprr', 'd e. %s' % DV('n')), 'elrabi', 'd e. NN')
    _, _, muc = mufacts(w, A3, dnn, 'd')
    sub = w.s([w.s([], 'eqid', '%s = %s' % (MU('d'), MU('d')))], 'a1i', '( n = ( d x. m ) -> %s = %s )' % (MU('d'), MU('d')))
    hy = hyper(w, PH, nre, MU('d'), MU('d'), sub, muc)
    # LHS = 1
    AN = '( %s /\\ n e. %s )' % (PH, RN)
    sn = mkst(w, AN)
    nn2 = sy(w, AN, sn([], 'simpr', 'n e. %s' % RN), 'elfznn', 'n e. NN')
    inner = sy(w, AN, nn2, 'bvmusum', 'sum_ d e. %s %s = %s' % (DV('n'), MU('d'), IF1('n')))
    lhs1 = st([inner], 'sumeq2dv', 'sum_ n e. %s sum_ d e. %s %s = sum_ n e. %s %s' % (RN, DV('n'), MU('d'), RN, IF1('n')))
    nuz = st([nnn, st([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', 'N e. ( ZZ>= ` 1 )')
    one1 = sy(w, PH, nuz, 'eluzfz1', '1 e. ( 1 ... N )')
    one1b = st([one1, st([fl], 'oveq2d', '%s = ( 1 ... N )' % RN)], 'eleqtrrd', '1 e. %s' % RN)
    site = st([w.s([], 'eqidd', '( n = 1 -> 1 = 1 )'), st([], 'fzfid', '%s e. Fin' % RN), one1b, st([], '1cnd', '1 e. CC')], 'sumite',
              'sum_ n e. %s %s = 1' % (RN, IF1('n')))
    lhs = st([lhs1, site], 'eqtrd', 'sum_ n e. %s sum_ d e. %s %s = 1' % (RN, DV('n'), MU('d')))
    # RHS inner sums
    AD = '( %s /\\ d e. %s )' % (PH, RN)
    sd = mkst(w, AD)
    dnn2 = sy(w, AD, sd([], 'simpr', 'd e. %s' % RN), 'elfznn', 'd e. NN')
    _, mur, muc2 = mufacts(w, AD, dnn2, 'd')
    RM = '( 1 ... %s )' % FL('( N / d )')
    qre = sd([lift(w, nre, AD), sd([dnn2], 'nnrpd', 'd e. RR+')], 'rerpdivcld', '( N / d ) e. RR')
    qge = sd([lift(w, nre, AD), sd([dnn2], 'nnrpd', 'd e. RR+'), sd([sd([lift(w, nnn, AD)], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')], 'divge0d', '0 <_ ( N / d )')
    fln0 = sy2(w, AD, qre, qge, 'flge0nn0', '%s e. NN0' % FL('( N / d )'))
    cst = sy2(w, AD, sd([], 'fzfid', '%s e. Fin' % RM), muc2, 'fsumconst', 'sum_ m e. %s %s = ( ( # ` %s ) x. %s )' % (RM, MU('d'), RM, MU('d')))
    hsh = sy(w, AD, fln0, 'hashfz1', '( # ` %s ) = %s' % (RM, FL('( N / d )')))
    inner2 = sd([cst, sd([sd([hsh], 'oveq1d', '( ( # ` %s ) x. %s ) = ( %s x. %s )' % (RM, MU('d'), FL('( N / d )'), MU('d'))),
                          sd([sd([fln0], 'nn0cnd', '%s e. CC' % FL('( N / d )')), muc2], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (FL('( N / d )'), MU('d'), MU('d'), FL('( N / d )')))],
                         'eqtrd', '( ( # ` %s ) x. %s ) = ( %s x. %s )' % (RM, MU('d'), MU('d'), FL('( N / d )')))], 'eqtrd',
                'sum_ m e. %s %s = ( %s x. %s )' % (RM, MU('d'), MU('d'), FL('( N / d )')))
    BODY = lambda v: '( %s x. %s )' % (MU(v), FL('( N / %s )' % v))
    rhs1 = st([inner2], 'sumeq2dv', 'sum_ d e. %s sum_ m e. %s %s = sum_ d e. %s %s' % (RN, RM, MU('d'), RN, BODY('d')))
    idd = w.s([], 'id', '( d = n -> d = n )')
    cs, _ = w.congr(BODY('d'), {'d': 'n'}, 'd = n', {'d': idd})
    cb = w.s([cs], 'cbvsumv', 'sum_ d e. %s %s = sum_ n e. %s %s' % (RN, BODY('d'), RN, BODY('n')))
    rng = st([st([fl], 'oveq2d', '%s = ( 1 ... N )' % RN)], 'sumeq1d', 'sum_ n e. %s %s = sum_ n e. ( 1 ... N ) %s' % (RN, BODY('n'), BODY('n')))
    rhs = st([st([rhs1, st([cb], 'a1i', 'sum_ d e. %s %s = sum_ n e. %s %s' % (RN, BODY('d'), RN, BODY('n')))], 'eqtrd',
                 'sum_ d e. %s sum_ m e. %s %s = sum_ n e. %s %s' % (RN, RM, MU('d'), RN, BODY('n'))), rng], 'eqtrd',
             'sum_ d e. %s sum_ m e. %s %s = sum_ n e. ( 1 ... N ) %s' % (RN, RM, MU('d'), BODY('n')))
    w.qed([st([hy, rhs], 'eqtrd', 'sum_ n e. %s sum_ d e. %s %s = sum_ n e. ( 1 ... N ) %s' % (RN, DV('n'), MU('d'), BODY('n'))), lhs], 'eqtr3d',
          '( %s -> sum_ n e. ( 1 ... N ) %s = 1 )' % (PH, BODY('n')))
    return w


def bvidb():
    w = W('bvidb', 'Identity (B): ( mmu ` n ) / n against the harmonic numbers of N / n sums to 1 '
                   '(Lean sum_moebius_div_mul_harmonic_eq_one).')
    PH = 'N e. NN'
    st = mkst(w, PH)
    nnn = st([], 'id', PH)
    nre = st([nnn], 'nnred', 'N e. RR'); nz = st([nnn], 'nnzd', 'N e. ZZ')
    fl = sy(w, PH, nz, 'flid', '%s = N' % FL('N'))
    RN = '( 1 ... %s )' % FL('N')
    B = '( %s / n )' % MU('d'); C = '( %s / ( d x. m ) )' % MU('d')
    A3 = '( %s /\\ ( n e. %s /\\ d e. %s ) )' % (PH, RN, DV('n'))
    s3 = mkst(w, A3)
    dnn = sy(w, A3, s3([], 'simprr', 'd e. %s' % DV('n')), 'elrabi', 'd e. NN')
    nnn3 = sy(w, A3, s3([], 'simprl', 'n e. %s' % RN), 'elfznn', 'n e. NN')
    _, _, muc = mufacts(w, A3, dnn, 'd')
    bcl = s3([muc, s3([nnn3], 'nncnd', 'n e. CC'), s3([nnn3], 'nnne0d', 'n =/= 0')], 'divcld', '%s e. CC' % B)
    sub = w.s([], 'oveq2', '( n = ( d x. m ) -> %s = %s )' % (B, C))
    hy = hyper(w, PH, nre, B, C, sub, bcl)
    # LHS = 1
    AN = '( %s /\\ n e. %s )' % (PH, RN)
    sn = mkst(w, AN)
    nn2 = sy(w, AN, sn([], 'simpr', 'n e. %s' % RN), 'elfznn', 'n e. NN')
    ncc = sn([nn2], 'nncnd', 'n e. CC'); nne = sn([nn2], 'nnne0d', 'n =/= 0')
    ADn = '( %s /\\ d e. %s )' % (AN, DV('n'))
    sdn = mkst(w, ADn)
    dnn2 = sy(w, ADn, sdn([], 'simpr', 'd e. %s' % DV('n')), 'elrabi', 'd e. NN')
    _, _, muc2 = mufacts(w, ADn, dnn2, 'd')
    dvc = sn([sy(w, AN, nn2, 'dvdsfi', '%s e. Fin' % DV('n')), ncc, muc2, nne], 'fsumdivc',
             '( sum_ d e. %s %s / n ) = sum_ d e. %s %s' % (DV('n'), MU('d'), DV('n'), B))
    ms = sy(w, AN, nn2, 'bvmusum', 'sum_ d e. %s %s = %s' % (DV('n'), MU('d'), IF1('n')))
    inner = sn([sn([dvc], 'eqcomd', 'sum_ d e. %s %s = ( sum_ d e. %s %s / n )' % (DV('n'), B, DV('n'), MU('d'))),
                sn([ms], 'oveq1d', '( sum_ d e. %s %s / n ) = ( %s / n )' % (DV('n'), MU('d'), IF1('n')))], 'eqtrd',
               'sum_ d e. %s %s = ( %s / n )' % (DV('n'), B, IF1('n')))
    # ( if ( n = 1 , 1 , 0 ) / n ) = if ( n = 1 , 1 , 0 )
    AT = '( %s /\\ n = 1 )' % AN
    stt = mkst(w, AT)
    n1 = stt([], 'simpr', 'n = 1')
    ct = stt([stt([stt([n1], 'iftrued', '%s = 1' % IF1('n')), n1], 'oveq12d', '( %s / n ) = ( 1 / 1 )' % IF1('n')),
              stt([stt([clo(w, '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1'), stt([n1], 'iftrued', '%s = 1' % IF1('n'))], 'eqtr4d', '( 1 / 1 ) = %s' % IF1('n'))],
             'eqtrd', '( %s / n ) = %s' % (IF1('n'), IF1('n')))
    AF = '( %s /\\ -. n = 1 )' % AN
    sf = mkst(w, AF)
    nn1 = sf([], 'simpr', '-. n = 1')
    cf = sf([sf([sf([nn1], 'iffalsed', '%s = 0' % IF1('n'))], 'oveq1d', '( %s / n ) = ( 0 / n )' % IF1('n')),
             sf([sf([lift(w, ncc, AF), lift(w, nne, AF)], 'div0d', '( 0 / n ) = 0'), sf([nn1], 'iffalsed', '%s = 0' % IF1('n'))], 'eqtr4d', '( 0 / n ) = %s' % IF1('n'))],
            'eqtrd', '( %s / n ) = %s' % (IF1('n'), IF1('n')))
    ifq = sn([ct, cf], 'pm2.61dan', '( %s / n ) = %s' % (IF1('n'), IF1('n')))
    lhs1 = st([sn([inner, ifq], 'eqtrd', 'sum_ d e. %s %s = %s' % (DV('n'), B, IF1('n')))], 'sumeq2dv',
              'sum_ n e. %s sum_ d e. %s %s = sum_ n e. %s %s' % (RN, DV('n'), B, RN, IF1('n')))
    nuz = st([nnn, st([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', 'N e. ( ZZ>= ` 1 )')
    one1 = sy(w, PH, nuz, 'eluzfz1', '1 e. ( 1 ... N )')
    one1b = st([one1, st([fl], 'oveq2d', '%s = ( 1 ... N )' % RN)], 'eleqtrrd', '1 e. %s' % RN)
    site = st([w.s([], 'eqidd', '( n = 1 -> 1 = 1 )'), st([], 'fzfid', '%s e. Fin' % RN), one1b, st([], '1cnd', '1 e. CC')], 'sumite',
              'sum_ n e. %s %s = 1' % (RN, IF1('n')))
    lhs = st([lhs1, site], 'eqtrd', 'sum_ n e. %s sum_ d e. %s %s = 1' % (RN, DV('n'), B))
    # RHS inner: sum_ m ( mu d / ( d m ) ) = ( mu d / d ) x. sum_ m ( 1 / m )
    AD = '( %s /\\ d e. %s )' % (PH, RN)
    sd = mkst(w, AD)
    dnn3 = sy(w, AD, sd([], 'simpr', 'd e. %s' % RN), 'elfznn', 'd e. NN')
    _, _, muc3 = mufacts(w, AD, dnn3, 'd')
    dcc = sd([dnn3], 'nncnd', 'd e. CC'); dne = sd([dnn3], 'nnne0d', 'd =/= 0')
    RM = '( 1 ... %s )' % FL('( N / d )')
    AM = '( %s /\\ m e. %s )' % (AD, RM)
    sm = mkst(w, AM)
    mnn = sy(w, AM, sm([], 'simpr', 'm e. %s' % RM), 'elfznn', 'm e. NN')
    mcc = sm([mnn], 'nncnd', 'm e. CC'); mne = sm([mnn], 'nnne0d', 'm =/= 0')
    Q = '( %s / d )' % MU('d')
    t1 = sm([lift(w, muc3, AM), lift(w, dcc, AM), mcc, lift(w, dne, AM), mne], 'divdiv1d', '( %s / m ) = %s' % (Q, C))
    t2 = sm([sm([lift(w, muc3, AM), lift(w, dcc, AM), lift(w, dne, AM)], 'divcld', '%s e. CC' % Q), mcc, mne], 'divrecd', '( %s / m ) = ( %s x. ( 1 / m ) )' % (Q, Q))
    term = sm([t1, t2], 'eqtr3d', '%s = ( %s x. ( 1 / m ) )' % (C, Q))
    HM = 'sum_ m e. %s ( 1 / m )' % RM
    mc2 = sd([sd([], 'fzfid', '%s e. Fin' % RM), sd([muc3, dcc, dne], 'divcld', '%s e. CC' % Q), sm([mcc, mne], 'reccld', '( 1 / m ) e. CC')], 'fsummulc2',
             '( %s x. %s ) = sum_ m e. %s ( %s x. ( 1 / m ) )' % (Q, HM, RM, Q))
    inner2 = sd([sd([term], 'sumeq2dv', 'sum_ m e. %s %s = sum_ m e. %s ( %s x. ( 1 / m ) )' % (RM, C, RM, Q)), mc2], 'eqtr4d',
                'sum_ m e. %s %s = ( %s x. %s )' % (RM, C, Q, HM))
    BODY = lambda v: '( ( %s / %s ) x. sum_ m e. ( 1 ... %s ) ( 1 / m ) )' % (MU(v), v, FL('( N / %s )' % v))
    rhs1 = st([inner2], 'sumeq2dv', 'sum_ d e. %s sum_ m e. %s %s = sum_ d e. %s %s' % (RN, RM, C, RN, BODY('d')))
    idd = w.s([], 'id', '( d = n -> d = n )')
    cs, _ = w.congr(BODY('d'), {'d': 'n'}, 'd = n', {'d': idd})
    cb = w.s([cs], 'cbvsumv', 'sum_ d e. %s %s = sum_ n e. %s %s' % (RN, BODY('d'), RN, BODY('n')))
    rng = st([st([fl], 'oveq2d', '%s = ( 1 ... N )' % RN)], 'sumeq1d', 'sum_ n e. %s %s = sum_ n e. ( 1 ... N ) %s' % (RN, BODY('n'), BODY('n')))
    rhs = st([st([rhs1, st([cb], 'a1i', 'sum_ d e. %s %s = sum_ n e. %s %s' % (RN, BODY('d'), RN, BODY('n')))], 'eqtrd',
                 'sum_ d e. %s sum_ m e. %s %s = sum_ n e. %s %s' % (RN, RM, C, RN, BODY('n'))), rng], 'eqtrd',
             'sum_ d e. %s sum_ m e. %s %s = sum_ n e. ( 1 ... N ) %s' % (RN, RM, C, BODY('n')))
    w.qed([st([hy, rhs], 'eqtrd', 'sum_ n e. %s sum_ d e. %s %s = sum_ n e. ( 1 ... N ) %s' % (RN, DV('n'), B, BODY('n'))), lhs], 'eqtr3d',
          '( %s -> sum_ n e. ( 1 ... N ) %s = 1 )' % (PH, BODY('n')))
    return w


HX = '( X e. RR /\\ 1 <_ X )'
NX = FL('X')
RX = '( 1 ... %s )' % NX
FR = lambda n: '( ( X / %s ) - %s )' % (n, FL('( X / %s )' % n))
MH = 'sum_ n e. %s ( %s / n )' % (RX, MU('n'))
FS = 'sum_ n e. %s ( %s x. %s )' % (RX, MU('n'), FR('n'))


def xfacts(w):
    """under HX: X e. RR, 1 <_ X, X e. RR+, N e. NN, N e. RR, N <_ X"""
    st = mkst(w, HX)
    xr = st([], 'simpl', 'X e. RR'); x1 = st([], 'simpr', '1 <_ X')
    xrp = st([xr, linarith(w, HX, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    nnn = sy2(w, HX, xr, x1, 'flge1nn', '%s e. NN' % NX)
    nre = st([nnn], 'nnred', '%s e. RR' % NX)
    nlex = sy(w, HX, xr, 'flle', '%s <_ X' % NX)
    return st, xr, x1, xrp, nnn, nre, nlex


def nfacts(w, ante, nel, n):
    """under ante with nel: n e. RX: n e. NN, RR+, CC, mu facts, FR real with 0 <_ FR < 1"""
    st = mkst(w, ante)
    nnn = sy(w, ante, nel, 'elfznn', '%s e. NN' % n)
    nrp = st([nnn], 'nnrpd', '%s e. RR+' % n)
    ncc = st([nnn], 'nncnd', '%s e. CC' % n)
    muz, mur, muc = mufacts(w, ante, nnn, n)
    return nnn, nrp, ncc, muz, mur, muc


def frfacts(w, ante, xr, nrp, n):
    """FR(n) e. RR, 0 <_ FR(n), FR(n) < 1 given X e. RR (xr) and n e. RR+ (nrp) under ante"""
    st = mkst(w, ante)
    Q = '( X / %s )' % n
    qre = st([xr, nrp], 'rerpdivcld', '%s e. RR' % Q)
    flr = sy(w, ante, qre, 'reflcl', '%s e. RR' % FL(Q))
    frr = st([qre, flr], 'resubcld', '%s e. RR' % FR(n))
    fle = sy(w, ante, qre, 'flle', '%s <_ %s' % (FL(Q), Q))
    flt = sy(w, ante, qre, 'flltp1', '%s < ( %s + 1 )' % (Q, FL(Q)))
    fr0 = linarith(w, ante, [fle], '0 <_ %s' % FR(n), leaves={Q: qre, FL(Q): flr})
    fr1 = linarith(w, ante, [flt], '%s < 1' % FR(n), leaves={Q: qre, FL(Q): flr})
    return qre, flr, frr, fr0, fr1


def bvmharmlem1():
    w = W('bvmharmlem1', 'X times the Moebius harmonic sum is 1 plus the sum of mmu against the '
                         'fractional parts of X / n (identity (A) plus the floor decomposition).')
    st, xr, x1, xrp, nnn, nre, nlex = xfacts(w)
    xc = st([xr], 'recnd', 'X e. CC')
    AN = '( %s /\\ n e. %s )' % (HX, RX)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % RX)
    nn, nrp, ncc, muz, mur, muc = nfacts(w, AN, nel, 'n')
    qre, flr, frr, fr0, fr1 = frfacts(w, AN, lift(w, xr, AN), nrp, 'n')
    Q = '( X / n )'
    # X x. ( mu / n ) = mu x. ( X / n )
    t1 = sn([lift(w, xc, AN), muc, ncc, sn([nn], 'nnne0d', 'n =/= 0')], 'div12d', '( X x. ( %s / n ) ) = ( %s x. %s )' % (MU('n'), MU('n'), Q))
    # mu x. ( X / n ) = mu x. fl + mu x. FR
    t2 = sn([muc, sn([flr], 'recnd', '%s e. CC' % FL(Q)), sn([frr], 'recnd', '%s e. CC' % FR('n'))], 'adddid',
            '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (MU('n'), FL(Q), FR('n'), MU('n'), FL(Q), MU('n'), FR('n')))
    t3 = sn([sn([flr], 'recnd', '%s e. CC' % FL(Q)), sn([qre], 'recnd', '%s e. CC' % Q)], 'pncan3d', '( %s + %s ) = %s' % (FL(Q), FR('n'), Q))
    t4 = sn([sn([sn([t3], 'oveq2d', '( %s x. ( %s + %s ) ) = ( %s x. %s )' % (MU('n'), FL(Q), FR('n'), MU('n'), Q)), t2], 'eqtr3d',
                '( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (MU('n'), Q, MU('n'), FL(Q), MU('n'), FR('n')))], 'id', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) ) )' % (AN, MU('n'), Q, MU('n'), FL(Q), MU('n'), FR('n'))) if False else \
        sn([sn([t3], 'oveq2d', '( %s x. ( %s + %s ) ) = ( %s x. %s )' % (MU('n'), FL(Q), FR('n'), MU('n'), Q)), t2], 'eqtr3d',
           '( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (MU('n'), Q, MU('n'), FL(Q), MU('n'), FR('n')))
    # fl ( X / n ) = fl ( N / n )
    fld = sy2(w, AN, lift(w, xr, AN), nn, 'fldiv', '%s = %s' % (FL('( %s / n )' % NX), FL(Q)))
    fl2 = sn([sn([fld], 'eqcomd', '%s = %s' % (FL(Q), FL('( %s / n )' % NX)))], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (MU('n'), FL(Q), MU('n'), FL('( %s / n )' % NX)))
    t5 = sn([t4, sn([fl2], 'oveq1d', '( ( %s x. %s ) + ( %s x. %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (MU('n'), FL(Q), MU('n'), FR('n'), MU('n'), FL('( %s / n )' % NX), MU('n'), FR('n')))], 'eqtrd',
            '( %s x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (MU('n'), Q, MU('n'), FL('( %s / n )' % NX), MU('n'), FR('n')))
    term = sn([t1, t5], 'eqtrd', '( X x. ( %s / n ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (MU('n'), MU('n'), FL('( %s / n )' % NX), MU('n'), FR('n')))
    fin = st([], 'fzfid', '%s e. Fin' % RX)
    muq = sn([muc, ncc, sn([nn], 'nnne0d', 'n =/= 0')], 'divcld', '( %s / n ) e. CC' % MU('n'))
    s1 = st([fin, xc, muq], 'fsummulc2', '( X x. %s ) = sum_ n e. %s ( X x. ( %s / n ) )' % (MH, RX, MU('n')))
    s2 = st([term], 'sumeq2dv', 'sum_ n e. %s ( X x. ( %s / n ) ) = sum_ n e. %s ( ( %s x. %s ) + ( %s x. %s ) )' % (RX, MU('n'), RX, MU('n'), FL('( %s / n )' % NX), MU('n'), FR('n')))
    SA = 'sum_ n e. %s ( %s x. %s )' % (RX, MU('n'), FL('( %s / n )' % NX))
    flnc = sn([sy2(w, AN, sn([lift(w, nnn, AN)], 'nnnn0d', '%s e. NN0' % NX), nn, 'fldivnn0', '%s e. NN0' % FL('( %s / n )' % NX))], 'nn0cnd', '%s e. CC' % FL('( %s / n )' % NX))
    s3 = st([fin, sn([muc, flnc], 'mulcld', '( %s x. %s ) e. CC' % (MU('n'), FL('( %s / n )' % NX))), sn([muc, sn([frr], 'recnd', '%s e. CC' % FR('n'))], 'mulcld', '( %s x. %s ) e. CC' % (MU('n'), FR('n')))],
            'fsumadd', 'sum_ n e. %s ( ( %s x. %s ) + ( %s x. %s ) ) = ( %s + %s )' % (RX, MU('n'), FL('( %s / n )' % NX), MU('n'), FR('n'), SA, FS))
    ida = sy(w, HX, nnn, 'bvida', '%s = 1' % SA)
    w.qed([st([st([s1, s2], 'eqtrd', '( X x. %s ) = sum_ n e. %s ( ( %s x. %s ) + ( %s x. %s ) )' % (MH, RX, MU('n'), FL('( %s / n )' % NX), MU('n'), FR('n'))), s3], 'eqtrd',
              '( X x. %s ) = ( %s + %s )' % (MH, SA, FS)), st([ida], 'oveq1d', '( %s + %s ) = ( 1 + %s )' % (SA, FS, FS))], 'eqtrd',
          '( %s -> ( X x. %s ) = ( 1 + %s ) )' % (HX, MH, FS))
    return w


def bvmharmlem2():
    w = W('bvmharmlem2', 'The Moebius sum against the fractional parts of X / n is at most X - 1 in '
                         'absolute value: the n = 1 term is X - |_ X and the others are each at most 1.')
    st, xr, x1, xrp, nnn, nre, nlex = xfacts(w)
    xc = st([xr], 'recnd', 'X e. CC')
    AN = '( %s /\\ n e. %s )' % (HX, RX)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % RX)
    nn, nrp, ncc, muz, mur, muc = nfacts(w, AN, nel, 'n')
    qre, flr, frr, fr0, fr1 = frfacts(w, AN, lift(w, xr, AN), nrp, 'n')
    TERM = lambda v: '( %s x. %s )' % (MU(v), FR(v))
    termc = sn([muc, sn([frr], 'recnd', '%s e. CC' % FR('n'))], 'mulcld', '%s e. CC' % TERM('n'))
    nuz = st([nnn, st([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', '%s e. ( ZZ>= ` 1 )' % NX)
    idn = w.s([], 'id', '( n = 1 -> n = 1 )')
    cs, T1 = w.congr(TERM('n'), {'n': '1'}, 'n = 1', {'n': idn})
    R2 = '( ( 1 + 1 ) ... %s )' % NX
    REST = 'sum_ n e. %s %s' % (R2, TERM('n'))
    peel = st([nuz, termc, cs], 'fsum1p', '%s = ( %s + %s )' % (FS, T1, REST))
    # T1 = X - N
    mu1 = st([clo(w, 'muone', '( mmu ` 1 ) = 1')], 'a1i', '( mmu ` 1 ) = 1')
    d1 = st([xc], 'div1d', '( X / 1 ) = X')
    fr1v = st([d1, st([d1], 'fveq2d', '%s = %s' % (FL('( X / 1 )'), NX))], 'oveq12d', '%s = ( X - %s )' % (FR('1'), NX))
    xmn = st([xr, nre], 'resubcld', '( X - %s ) e. RR' % NX)
    t1v = st([st([mu1, fr1v], 'oveq12d', '%s = ( 1 x. ( X - %s ) )' % (T1, NX)), st([st([xmn], 'recnd', '( X - %s ) e. CC' % NX)], 'mullidd', '( 1 x. ( X - %s ) ) = ( X - %s )' % (NX, NX))], 'eqtrd',
             '%s = ( X - %s )' % (T1, NX))
    xmn0 = linarith(w, HX, [nlex], '0 <_ ( X - %s )' % NX, leaves={'X': xr, NX: nre})
    # | REST | <_ N - 1
    A2 = '( %s /\\ n e. %s )' % (HX, R2)
    s2 = mkst(w, A2)
    nel2 = s2([], 'simpr', 'n e. %s' % R2)
    nn2 = sy(w, A2, sy(w, A2, nel2, 'elfzuz', 'n e. ( ZZ>= ` ( 1 + 1 ) )'), 'eluzelz', 'n e. ZZ')
    n2ge = sy(w, A2, nel2, 'elfzle1', '( 1 + 1 ) <_ n')
    nre2 = s2([nn2], 'zred', 'n e. RR')
    nrp2 = s2([nre2, linarith(w, A2, [n2ge], '0 < n', leaves={'n': nre2})], 'elrpd', 'n e. RR+')
    nnn2 = s2([s2([nn2, linarith(w, A2, [n2ge], '0 < n', leaves={'n': nre2})], 'jca', '( n e. ZZ /\\ 0 < n )'), s2([clo(w, 'elnnz', '( n e. NN <-> ( n e. ZZ /\\ 0 < n ) )')], 'a1i', '( n e. NN <-> ( n e. ZZ /\\ 0 < n ) )')], 'mpbird', 'n e. NN')
    muz2, mur2, muc2 = mufacts(w, A2, nnn2, 'n')
    qre2, flr2, frr2, fr02, fr12 = frfacts(w, A2, lift(w, xr, A2), nrp2, 'n')
    ab = s2([muc2, s2([frr2], 'recnd', '%s e. CC' % FR('n'))], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TERM('n'), MU('n'), FR('n')))
    abfr = s2([frr2, fr02], 'absidd', '( abs ` %s ) = %s' % (FR('n'), FR('n')))
    mule = sy(w, A2, nnn2, 'mule1', '( abs ` %s ) <_ 1' % MU('n'))
    frle1 = s2([frr2, s2([], '1red', '1 e. RR'), fr12], 'ltled', '%s <_ 1' % FR('n'))
    absmur = s2([s2([mur2], 'recnd', '%s e. CC' % MU('n'))], 'abscld', '( abs ` %s ) e. RR' % MU('n'))
    absmu0 = s2([s2([mur2], 'recnd', '%s e. CC' % MU('n'))], 'absge0d', '0 <_ ( abs ` %s )' % MU('n'))
    prodle = s2([absmur, s2([], '1red', '1 e. RR'), frr2, s2([], '1red', '1 e. RR'), absmu0, fr02, mule, frle1], 'lemul12ad',
                '( ( abs ` %s ) x. %s ) <_ ( 1 x. 1 )' % (MU('n'), FR('n')))
    one = w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('mullid')], 'ax-mp', '( 1 x. 1 ) = 1')
    tle = s2([s2([ab, s2([abfr], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. %s )' % (MU('n'), FR('n'), MU('n'), FR('n')))], 'eqtrd',
                 '( abs ` %s ) = ( ( abs ` %s ) x. %s )' % (TERM('n'), MU('n'), FR('n'))), s2([prodle, s2([one], 'a1i', '( 1 x. 1 ) = 1')], 'breqtrd', '( ( abs ` %s ) x. %s ) <_ 1' % (MU('n'), FR('n')))],
             'eqbrtrd', '( abs ` %s ) <_ 1' % TERM('n'))
    fin2 = st([], 'fzfid', '%s e. Fin' % R2)
    termc2 = s2([muc2, s2([frr2], 'recnd', '%s e. CC' % FR('n'))], 'mulcld', '%s e. CC' % TERM('n'))
    fa = st([fin2, termc2], 'fsumabs', '( abs ` %s ) <_ sum_ n e. %s ( abs ` %s )' % (REST, R2, TERM('n')))
    fle = st([fin2, s2([termc2], 'abscld', '( abs ` %s ) e. RR' % TERM('n')), s2([], '1red', '1 e. RR'), tle], 'fsumle',
             'sum_ n e. %s ( abs ` %s ) <_ sum_ n e. %s 1' % (R2, TERM('n'), R2))
    cst = sy2(w, HX, fin2, st([], '1cnd', '1 e. CC'), 'fsumconst', 'sum_ n e. %s 1 = ( ( # ` %s ) x. 1 )' % (R2, R2))
    hsh = sy(w, HX, nuz, 'hashfzp1', '( # ` %s ) = ( %s - 1 )' % (R2, NX))
    cst2 = st([cst, st([st([hsh], 'oveq1d', '( ( # ` %s ) x. 1 ) = ( ( %s - 1 ) x. 1 )' % (R2, NX)), st([st([st([nre, st([], '1red', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % NX)], 'recnd', '( %s - 1 ) e. CC' % NX)], 'mulridd', '( ( %s - 1 ) x. 1 ) = ( %s - 1 )' % (NX, NX))], 'eqtrd',
                        '( ( # ` %s ) x. 1 ) = ( %s - 1 )' % (R2, NX))], 'eqtrd', 'sum_ n e. %s 1 = ( %s - 1 )' % (R2, NX))
    restr = st([fin2, termc2], 'fsumcl', '%s e. CC' % REST)
    absr = st([restr], 'abscld', '( abs ` %s ) e. RR' % REST)
    sar = st([fin2, s2([termc2], 'abscld', '( abs ` %s ) e. RR' % TERM('n'))], 'fsumrecl', 'sum_ n e. %s ( abs ` %s ) e. RR' % (R2, TERM('n')))
    s1r = st([fin2, s2([], '1red', '1 e. RR')], 'fsumrecl', 'sum_ n e. %s 1 e. RR' % R2)
    nm1 = st([nre, st([], '1red', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % NX)
    restle = st([absr, sar, nm1, fa, st([fle, cst2], 'breqtrd', 'sum_ n e. %s ( abs ` %s ) <_ ( %s - 1 )' % (R2, TERM('n'), NX))], 'letrd',
                '( abs ` %s ) <_ ( %s - 1 )' % (REST, NX))
    # assemble
    tri = sy2(w, HX, st([xmn], 'recnd', '( X - %s ) e. CC' % NX), restr, 'abstri', '( abs ` ( ( X - %s ) + %s ) ) <_ ( ( abs ` ( X - %s ) ) + ( abs ` %s ) )' % (NX, REST, NX, REST))
    absx = st([xmn, xmn0], 'absidd', '( abs ` ( X - %s ) ) = ( X - %s )' % (NX, NX))
    fseq = st([peel, st([t1v], 'oveq1d', '( %s + %s ) = ( ( X - %s ) + %s )' % (T1, REST, NX, REST))], 'eqtrd', '%s = ( ( X - %s ) + %s )' % (FS, NX, REST))
    absfs = st([fseq], 'fveq2d', '( abs ` %s ) = ( abs ` ( ( X - %s ) + %s ) )' % (FS, NX, REST))
    tri2 = st([tri, st([absx], 'oveq1d', '( ( abs ` ( X - %s ) ) + ( abs ` %s ) ) = ( ( X - %s ) + ( abs ` %s ) )' % (NX, REST, NX, REST))], 'breqtrd',
               '( abs ` ( ( X - %s ) + %s ) ) <_ ( ( X - %s ) + ( abs ` %s ) )' % (NX, REST, NX, REST))
    fsc = st([st([], 'fzfid', '%s e. Fin' % RX), termc], 'fsumcl', '%s e. CC' % FS)
    absfsr = st([fsc], 'abscld', '( abs ` %s ) e. RR' % FS)
    bnd = st([absfs, tri2], 'eqbrtrd', '( abs ` %s ) <_ ( ( X - %s ) + ( abs ` %s ) )' % (FS, NX, REST))
    linarith(w, HX, [bnd, restle], '( abs ` %s ) <_ ( X - 1 )' % FS, leaves={'( abs ` %s )' % FS: absfsr, '( abs ` %s )' % REST: absr, 'X': xr, NX: nre}, name='qed')
    return w


def bvmharm():
    w = W('bvmharm', 'The Moebius harmonic sum up to X is at most 1 in absolute value '
                     '(Lean abs_mHarm_le_one).')
    st, xr, x1, xrp, nnn, nre, nlex = xfacts(w)
    l1 = st([], 'bvmharmlem1', '( X x. %s ) = ( 1 + %s )' % (MH, FS))
    l2 = st([], 'bvmharmlem2', '( abs ` %s ) <_ ( X - 1 )' % FS)
    AN = '( %s /\\ n e. %s )' % (HX, RX)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % RX)
    nn, nrp, ncc, muz, mur, muc = nfacts(w, AN, nel, 'n')
    qre, flr, frr, fr0, fr1 = frfacts(w, AN, lift(w, xr, AN), nrp, 'n')
    fin = st([], 'fzfid', '%s e. Fin' % RX)
    mhr = st([fin, sn([mur, nrp], 'rerpdivcld', '( %s / n ) e. RR' % MU('n'))], 'fsumrecl', '%s e. RR' % MH)
    fsr = st([fin, sn([mur, frr], 'remulcld', '%s e. RR' % '( %s x. %s )' % (MU('n'), FR('n')))], 'fsumrecl', '%s e. RR' % FS)
    fsc = st([fsr], 'recnd', '%s e. CC' % FS)
    tri = sy2(w, HX, st([], '1cnd', '1 e. CC'), fsc, 'abstri', '( abs ` ( 1 + %s ) ) <_ ( ( abs ` 1 ) + ( abs ` %s ) )' % (FS, FS))
    a1 = st([clo(w, 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')
    absfs = st([fsc], 'abscld', '( abs ` %s ) e. RR' % FS)
    tri2 = st([tri, st([a1], 'oveq1d', '( ( abs ` 1 ) + ( abs ` %s ) ) = ( 1 + ( abs ` %s ) )' % (FS, FS))], 'breqtrd', '( abs ` ( 1 + %s ) ) <_ ( 1 + ( abs ` %s ) )' % (FS, FS))
    absxm = st([st([xr], 'recnd', 'X e. CC'), st([mhr], 'recnd', '%s e. CC' % MH)], 'absmuld', '( abs ` ( X x. %s ) ) = ( ( abs ` X ) x. ( abs ` %s ) )' % (MH, MH))
    absx = st([xr, st([xrp], 'rpge0d', '0 <_ X')], 'absidd', '( abs ` X ) = X')
    xam = st([absxm, st([absx], 'oveq1d', '( ( abs ` X ) x. ( abs ` %s ) ) = ( X x. ( abs ` %s ) )' % (MH, MH))], 'eqtrd', '( abs ` ( X x. %s ) ) = ( X x. ( abs ` %s ) )' % (MH, MH))
    le1 = st([st([st([l1], 'fveq2d', '( abs ` ( X x. %s ) ) = ( abs ` ( 1 + %s ) )' % (MH, FS)), xam], 'eqtr3d', '( abs ` ( 1 + %s ) ) = ( X x. ( abs ` %s ) )' % (FS, MH)), tri2], 'eqbrtrrd',
              '( X x. ( abs ` %s ) ) <_ ( 1 + ( abs ` %s ) )' % (MH, FS))
    absmh = st([st([mhr], 'recnd', '%s e. CC' % MH)], 'abscld', '( abs ` %s ) e. RR' % MH)
    xle = linarith(w, HX, [le1, l2], '( X x. ( abs ` %s ) ) <_ ( X x. 1 )' % MH, leaves={'( X x. ( abs ` %s ) )' % MH: st([xr, absmh], 'remulcld', '( X x. ( abs ` %s ) ) e. RR' % MH), '( abs ` %s )' % FS: absfs, 'X': xr, '( X x. 1 )': st([xr, st([], '1red', '1 e. RR')], 'remulcld', '( X x. 1 ) e. RR')})
    bi = st([absmh, st([], '1red', '1 e. RR'), xrp], 'lemul2d', '( ( abs ` %s ) <_ 1 <-> ( X x. ( abs ` %s ) ) <_ ( X x. 1 ) )' % (MH, MH))
    w.qed([xle, bi], 'mpbird', '( %s -> ( abs ` %s ) <_ 1 )' % (HX, MH))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvmusum', 'bvida', 'bvidb', 'bvmharmlem1', 'bvmharmlem2', 'bvmharm']:
        globals()[f]().run()
