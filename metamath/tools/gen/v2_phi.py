"""Sortie v2: the totient over the radical (muprod, phiradlem, phirad, phisqf)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W

def PF(X, v='q'): return '{ %s e. Prime | %s || %s }' % (v, v, X)
def OM(X): return '( # ` %s )' % PF(X)
def PRD(X, b='p'): return 'prod_ %s e. %s %s' % (b, X, b)


def mkst(w, a):
    return lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g))


def muprod():
    w = W('muprod',
          'The Moebius function of a squarefree number divided by it, as a product over its '
          'prime divisors.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    T = PF('D')
    st = mkst(w, A)
    d = st([], 'simpl', 'D e. NN')
    sq = st([], 'simpr', '( mmu ` D ) =/= 0')
    finp = st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), T))], 'a1i',
             '%s = %s' % (PF('D', 'p'), T))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % T)
    ssp = st([w.s([], 'ssrab2', '%s C_ Prime' % T)], 'a1i', '%s C_ Prime' % T)
    # ( mmu ` D ) = ( -u 1 ^ ( # ` T ) )
    mv = st([d, sq, w.inst('muval2')], 'syl2anc',
            '( mmu ` D ) = ( -u 1 ^ ( # ` %s ) )' % PF('D', 'p'))
    hq = st([cbv], 'fveq2d', '( # ` %s ) = %s' % (PF('D', 'p'), OM('D')))
    mv2 = st([mv, st([hq], 'oveq2d',
             '( -u 1 ^ ( # ` %s ) ) = ( -u 1 ^ %s )' % (PF('D', 'p'), OM('D')))], 'eqtrd',
             '( mmu ` D ) = ( -u 1 ^ %s )' % OM('D'))
    # the constant product
    m1c = st([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '-u 1 e. CC')
    cst = st([fin, m1c, w.inst('fprodconst')], 'syl2anc',
             'prod_ p e. %s -u 1 = ( -u 1 ^ %s )' % (T, OM('D')))
    # the product of the primes is D
    pid = st([], 'sqfprodid', '%s = D' % PRD(T))
    # fproddiv
    BP = '( %s /\\ p e. %s )' % (A, T)
    fp = mkst(w, BP)
    pprm = fp([fp([], 'simpr', 'p e. %s' % T), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = fp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    pc = fp([pnn], 'nncnd', 'p e. CC')
    pne = fp([pnn], 'nnne0d', 'p =/= 0')
    m1cb = fp([m1c], 'adantr', '-u 1 e. CC')
    dv = st([fin, m1cb, pc, pne], 'fproddiv',
            'prod_ p e. %s ( -u 1 / p ) = ( prod_ p e. %s -u 1 / %s )' % (T, T, PRD(T)))
    rhs2 = st([cst, pid], 'oveq12d',
              '( prod_ p e. %s -u 1 / %s ) = ( ( -u 1 ^ %s ) / D )' % (T, PRD(T), OM('D')))
    lhs = st([mv2], 'oveq1d', '( ( mmu ` D ) / D ) = ( ( -u 1 ^ %s ) / D )' % OM('D'))
    w.qed([lhs, st([dv, rhs2], 'eqtrd',
          'prod_ p e. %s ( -u 1 / p ) = ( ( -u 1 ^ %s ) / D )' % (T, OM('D')))], 'eqtr4d',
          '( %s -> ( ( mmu ` D ) / D ) = prod_ p e. %s ( -u 1 / p ) )' % (A, T))
    return w


BODY = '( # ` { x e. ( 1 ... n ) | ( x gcd n ) = 1 } )'
GID = '( n e. NN |-> n )'
DVM = '{ x e. NN | x || M }'


def phif():
    w = W('phif', 'The totient is a function from the positive integers to the complex numbers.')
    dfp = w.s([], 'df-phi', 'phi = %s' % ('( n e. NN |-> %s )' % BODY))
    fzf = w.s([], 'fzfid', '( n e. NN -> ( 1 ... n ) e. Fin )')
    ssr = w.s([w.s([], 'ssrab2', '{ x e. ( 1 ... n ) | ( x gcd n ) = 1 } C_ ( 1 ... n )')], 'a1i',
              '( n e. NN -> { x e. ( 1 ... n ) | ( x gcd n ) = 1 } C_ ( 1 ... n ) )')
    fin = w.s([fzf, ssr], 'ssfid', '( n e. NN -> { x e. ( 1 ... n ) | ( x gcd n ) = 1 } e. Fin )')
    h0 = w.s([fin, w.inst('hashcl')], 'syl', '( n e. NN -> %s e. NN0 )' % BODY)
    hc = w.s([h0], 'nn0cnd', '( n e. NN -> %s e. CC )' % BODY)
    ral = w.s([hc], 'rgen', 'A. n e. NN %s e. CC' % BODY)
    bi = w.s([dfp], 'fmpt', '( A. n e. NN %s e. CC <-> phi : NN --> CC )' % BODY)
    w.qed([ral, bi], 'mpbi', 'phi : NN --> CC')
    return w


def phimuinv():
    w = W('phimuinv', 'Moebius inversion of the totient divisor sum.')
    SUM = 'sum_ j e. %s ( ( mmu ` j ) x. ( %s ` ( M / j ) ) )' % (DVM, GID)
    SUM2 = 'sum_ j e. %s ( ( mmu ` j ) x. ( M / j ) )' % DVM
    A = 'M e. NN'
    st = mkst(w, A)
    # the hypotheses of muinv
    pf = w.s([w.s([], 'phif', 'phi : NN --> CC')], 'a1i', '( %s -> phi : NN --> CC )' % A)
    ps = w.s([], 'phisum', '( n e. NN -> sum_ d e. { x e. NN | x || n } ( phi ` d ) = n )')
    cb = w.s([], 'cbvsumv', 'sum_ d e. { x e. NN | x || n } ( phi ` d ) = '
             'sum_ k e. { x e. NN | x || n } ( phi ` k )')
    eqn = w.s([cb], 'eqeq1i',
              '( sum_ d e. { x e. NN | x || n } ( phi ` d ) = n <-> '
              'sum_ k e. { x e. NN | x || n } ( phi ` k ) = n )')
    psk = w.s([ps, eqn], 'sylib', '( n e. NN -> sum_ k e. { x e. NN | x || n } ( phi ` k ) = n )')
    pskr = w.s([psk], 'eqcomd', '( n e. NN -> n = sum_ k e. { x e. NN | x || n } ( phi ` k ) )')
    mpt = w.s([pskr], 'mpteq2ia',
              '%s = ( n e. NN |-> sum_ k e. { x e. NN | x || n } ( phi ` k ) )' % GID)
    mpta = w.s([mpt], 'a1i',
               '( %s -> %s = ( n e. NN |-> sum_ k e. { x e. NN | x || n } ( phi ` k ) ) )' % (A, GID))
    inv = st([pf, mpta], 'muinv',
             'phi = ( m e. NN |-> sum_ j e. { x e. NN | x || m } ( ( mmu ` j ) x. ( %s ` ( m / j ) ) ) )'
             % GID)
    # evaluate at M
    sub1 = w.s([], 'breq2', '( m = M -> ( x || m <-> x || M ) )')
    sub2 = w.s([sub1], 'rabbidv', '( m = M -> { x e. NN | x || m } = %s )' % DVM)
    sub3 = w.s([], 'oveq1', '( m = M -> ( m / j ) = ( M / j ) )')
    sub4 = w.s([sub3], 'fveq2d', '( m = M -> ( %s ` ( m / j ) ) = ( %s ` ( M / j ) ) )' % (GID, GID))
    sub5 = w.s([sub4], 'oveq2d',
               '( m = M -> ( ( mmu ` j ) x. ( %s ` ( m / j ) ) ) = ( ( mmu ` j ) x. ( %s ` ( M / j ) ) ) )'
               % (GID, GID))
    sub5b = w.s([sub5], 'adantr',
                '( ( m = M /\\ j e. { x e. NN | x || m } ) -> '
                '( ( mmu ` j ) x. ( %s ` ( m / j ) ) ) = ( ( mmu ` j ) x. ( %s ` ( M / j ) ) ) )'
                % (GID, GID))
    sub = w.s([sub2, sub5b], 'sumeq12dv',
              '( m = M -> sum_ j e. { x e. NN | x || m } ( ( mmu ` j ) x. ( %s ` ( m / j ) ) ) = %s )'
              % (GID, SUM))
    # the sum is a set, so the function value is the body
    MPT = ('( m e. NN |-> sum_ j e. { x e. NN | x || m } ( ( mmu ` j ) x. ( %s ` ( m / j ) ) ) )'
           % GID)
    idm = w.s([], 'id', '( %s -> M e. NN )' % A)
    sumex = st([w.s([], 'sumex', '%s e. _V' % SUM)], 'a1i', '%s e. _V' % SUM)
    fvi = w.s([sub, w.s([], 'eqid', '%s = %s' % (MPT, MPT))], 'fvmptg',
              '( ( M e. NN /\\ %s e. _V ) -> ( %s ` M ) = %s )' % (SUM, MPT, SUM))
    fval = st([idm, sumex, fvi], 'syl2anc', '( %s ` M ) = %s' % (MPT, SUM))
    phv = st([inv], 'fveq1d', '( phi ` M ) = ( %s ` M )' % MPT)
    phs = st([phv, fval], 'eqtrd', '( phi ` M ) = %s' % SUM)
    # the identity function value
    BJ = '( %s /\\ j e. %s )' % (A, DVM)
    fj = mkst(w, BJ)
    jin = fj([], 'simpr', 'j e. %s' % DVM)
    mdv = fj([fj([idm], 'adantr', 'M e. NN'), jin, w.inst('dvdsdivcl')], 'syl2anc',
             '( M / j ) e. %s' % DVM)
    mdn = fj([mdv, w.inst('elrabi')], 'syl', '( M / j ) e. NN')
    mdex = fj([mdn, w.inst('elex')], 'syl', '( M / j ) e. _V')
    gvi = w.s([w.s([], 'id', '( n = ( M / j ) -> n = ( M / j ) )'),
               w.s([], 'eqid', '%s = %s' % (GID, GID))], 'fvmptg',
              '( ( ( M / j ) e. NN /\\ ( M / j ) e. _V ) -> ( %s ` ( M / j ) ) = ( M / j ) )' % GID)
    gval = fj([mdn, mdex, gvi], 'syl2anc', '( %s ` ( M / j ) ) = ( M / j )' % GID)
    term = fj([gval], 'oveq2d',
              '( ( mmu ` j ) x. ( %s ` ( M / j ) ) ) = ( ( mmu ` j ) x. ( M / j ) )' % GID)
    seq = st([term], 'sumeq2dv', '%s = %s' % (SUM, SUM2))
    w.qed([phs, seq], 'eqtrd', '( %s -> ( phi ` M ) = %s )' % (A, SUM2))
    return w


GNEG = '( t e. Prime |-> ( -u 1 / t ) )'
SDM = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || M ) }'


def phiradlem():
    w = W('phiradlem',
          'The totient over the argument, as a product of ( p - 1 ) / p over the prime divisors.')
    A = 'M e. NN'
    TM = PF('M')
    S1 = 'sum_ j e. %s ( ( mmu ` j ) x. ( M / j ) )' % DVM
    S2 = 'sum_ j e. %s ( ( ( mmu ` j ) x. ( M / j ) ) / M )' % DVM
    S3 = 'sum_ j e. %s ( ( mmu ` j ) / j )' % DVM
    S4 = 'sum_ d e. %s ( ( mmu ` d ) / d )' % DVM
    S5 = 'sum_ d e. %s ( ( mmu ` d ) / d )' % SDM
    S6 = 'sum_ d e. %s prod_ p e. %s ( %s ` p )' % (SDM, PF('d'), GNEG)
    P1 = 'prod_ p e. %s ( 1 + ( %s ` p ) )' % (TM, GNEG)
    P2 = 'prod_ p e. %s ( ( p - 1 ) / p )' % TM
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    mc = st([m], 'nncnd', 'M e. CC')
    mne = st([m], 'nnne0d', 'M =/= 0')
    fin = st([m, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVM)
    pm = st([], 'phimuinv', '( phi ` M ) = %s' % S1)
    # divide by M
    BJ = '( %s /\\ j e. %s )' % (A, DVM)
    fj = mkst(w, BJ)
    jin = fj([], 'simpr', 'j e. %s' % DVM)
    jnn = fj([jin, w.inst('elrabi')], 'syl', 'j e. NN')
    jc = fj([jnn], 'nncnd', 'j e. CC')
    jne = fj([jnn], 'nnne0d', 'j =/= 0')
    mcj = fj([mc], 'adantr', 'M e. CC')
    mnej = fj([mne], 'adantr', 'M =/= 0')
    muc = fj([fj([jnn, w.inst('mucl')], 'syl', '( mmu ` j ) e. ZZ')], 'zcnd', '( mmu ` j ) e. CC')
    mdj = fj([mcj, jc, jne], 'divcld', '( M / j ) e. CC')
    prod = fj([muc, mdj], 'mulcld', '( ( mmu ` j ) x. ( M / j ) ) e. CC')
    dvc = st([fin, mc, prod, mne], 'fsumdivc', '( %s / M ) = %s' % (S1, S2))
    # termwise ( ( mmu j x. ( M / j ) ) / M ) = ( mmu j / j )
    t1 = fj([muc, mdj, mcj, mnej], 'divassd',
            '( ( ( mmu ` j ) x. ( M / j ) ) / M ) = ( ( mmu ` j ) x. ( ( M / j ) / M ) )')
    t2 = fj([mcj, jc, mcj, jne, mnej], 'divdiv32d', '( ( M / j ) / M ) = ( ( M / M ) / j )')
    t3 = fj([mcj, mnej], 'dividd', '( M / M ) = 1')
    t4 = fj([t2, fj([t3], 'oveq1d', '( ( M / M ) / j ) = ( 1 / j )')], 'eqtrd',
            '( ( M / j ) / M ) = ( 1 / j )')
    t5 = fj([t1, fj([t4], 'oveq2d',
            '( ( mmu ` j ) x. ( ( M / j ) / M ) ) = ( ( mmu ` j ) x. ( 1 / j ) )')], 'eqtrd',
            '( ( ( mmu ` j ) x. ( M / j ) ) / M ) = ( ( mmu ` j ) x. ( 1 / j ) )')
    t6 = fj([muc, jc, jne], 'divrecd', '( ( mmu ` j ) / j ) = ( ( mmu ` j ) x. ( 1 / j ) )')
    term = fj([t5, fj([t6], 'eqcomd', '( ( mmu ` j ) x. ( 1 / j ) ) = ( ( mmu ` j ) / j )')],
              'eqtrd', '( ( ( mmu ` j ) x. ( M / j ) ) / M ) = ( ( mmu ` j ) / j )')
    e1 = st([term], 'sumeq2dv', '%s = %s' % (S2, S3))
    lhs = st([st([pm], 'oveq1d', '( ( phi ` M ) / M ) = ( %s / M )' % S1), dvc], 'eqtrd',
             '( ( phi ` M ) / M ) = %s' % S2)
    lhs2 = st([lhs, e1], 'eqtrd', '( ( phi ` M ) / M ) = %s' % S3)
    # rename j to d and restrict to the squarefree divisors
    cbj = w.s([w.s([], 'fveq2', '( j = d -> ( mmu ` j ) = ( mmu ` d ) )'),
               w.s([], 'id', '( j = d -> j = d )')], 'oveq12d',
              '( j = d -> ( ( mmu ` j ) / j ) = ( ( mmu ` d ) / d ) )')
    cbs = st([w.s([cbj], 'cbvsumv', '%s = %s' % (S3, S4))], 'a1i', '%s = %s' % (S3, S4))
    BD = '( %s /\\ d e. %s )' % (A, SDM)
    fd = mkst(w, BD)
    din = fd([], 'simpr', 'd e. %s' % SDM)
    dnn = fd([din, w.inst('elrabi')], 'syl', 'd e. NN')
    elsd = w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )'), ], 'neeq1d',
                    '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )'),
                w.s([], 'breq1', '( x = d -> ( x || M <-> d || M ) )')], 'anbi12d',
               '( x = d -> ( ( ( mmu ` x ) =/= 0 /\\ x || M ) <-> ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )')
    elsd2 = w.s([elsd], 'elrab',
                '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % SDM)
    dfacts = fd([fd([elsd2], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % SDM), din],
                'mpbid', '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) )')
    dsq = fd([fd([dfacts], 'simprd', '( ( mmu ` d ) =/= 0 /\\ d || M )')], 'simpld',
             '( mmu ` d ) =/= 0')
    # fsumss
    ssi = w.s([w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || M ) -> x || M )')], 'a1i',
              '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || M ) -> x || M ) )')
    sss = st([w.s([ssi], 'ss2rabi', '%s C_ %s' % (SDM, DVM))], 'a1i', '%s C_ %s' % (SDM, DVM))
    muclD = fd([fd([dnn, w.inst('mucl')], 'syl', '( mmu ` d ) e. ZZ')], 'zcnd', '( mmu ` d ) e. CC')
    dcD = fd([dnn], 'nncnd', 'd e. CC')
    dneD = fd([dnn], 'nnne0d', 'd =/= 0')
    clD = fd([muclD, dcD, dneD], 'divcld', '( ( mmu ` d ) / d ) e. CC')
    BDF = '( %s /\\ d e. ( %s \\ %s ) )' % (A, DVM, SDM)
    fdf = mkst(w, BDF)
    ddif = fdf([], 'simpr', 'd e. ( %s \\ %s )' % (DVM, SDM))
    ddv = fdf([ddif, w.inst('eldifi')], 'syl', 'd e. %s' % DVM)
    dnnf = fdf([ddv, w.inst('elrabi')], 'syl', 'd e. NN')
    dnsd = fdf([ddif, w.inst('eldifn')], 'syl', '-. d e. %s' % SDM)
    dvdf = fdf([fdf([w.s([w.s([], 'breq1', '( x = d -> ( x || M <-> d || M ) )')], 'elrab',
                        '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DVM)], 'a1i',
                    '( d e. %s <-> ( d e. NN /\\ d || M ) )' % DVM), ddv], 'mpbid',
               '( d e. NN /\\ d || M )')
    dvdf2 = fdf([dvdf], 'simprd', 'd || M')
    nsq = fdf([fdf([elsd2], 'a1i',
                   '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % SDM), dnsd],
              'mtbid', '-. ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) )')
    CJ = '( %s /\\ ( mmu ` d ) =/= 0 )' % BDF
    jcs = w.s([w.s([dnnf], 'adantr', '( %s -> d e. NN )' % CJ),
               w.s([w.s([], 'simpr', '( %s -> ( mmu ` d ) =/= 0 )' % CJ),
                    w.s([dvdf2], 'adantr', '( %s -> d || M )' % CJ)], 'jca',
                   '( %s -> ( ( mmu ` d ) =/= 0 /\\ d || M ) )' % CJ)], 'jca',
              '( %s -> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || M ) ) )' % CJ)
    mu0 = fdf([nsq, jcs], 'mtand', '-. ( mmu ` d ) =/= 0')
    mu0c = fdf([fdf([w.s([], 'nne', '( -. ( mmu ` d ) =/= 0 <-> ( mmu ` d ) = 0 )')], 'a1i',
                    '( -. ( mmu ` d ) =/= 0 <-> ( mmu ` d ) = 0 )'), mu0], 'mpbid',
               '( mmu ` d ) = 0')
    vanish = fdf([fdf([mu0c], 'oveq1d', '( ( mmu ` d ) / d ) = ( 0 / d )'),
                  fdf([fdf([dnnf], 'nncnd', 'd e. CC'), fdf([dnnf], 'nnne0d', 'd =/= 0')], 'div0d',
                      '( 0 / d ) = 0')], 'eqtrd', '( ( mmu ` d ) / d ) = 0')
    ss = st([sss, clD, vanish, fin], 'fsumss', '%s = %s' % (S5, S4))
    # muprod termwise, then the master identity
    gf1 = w.s([], 'eqid', '%s = %s' % (GNEG, GNEG))
    BT = '( %s /\\ t e. Prime )' % A
    ft = mkst(w, BT)
    tprm = ft([], 'simpr', 't e. Prime')
    tnn = ft([tprm, w.inst('prmnn')], 'syl', 't e. NN')
    tc = ft([tnn], 'nncnd', 't e. CC')
    tne = ft([tnn], 'nnne0d', 't =/= 0')
    m1ct = ft([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '-u 1 e. CC')
    gcl = ft([m1ct, tc, tne], 'divcld', '( -u 1 / t ) e. CC')
    gfn = st([gcl, gf1], 'fmptd', '%s : Prime --> CC' % GNEG)
    key = st([m, gfn, w.inst('sqfdvdsum')], 'syl2anc', '%s = %s' % (S6, P1))
    # ( G ` p ) = ( -u 1 / p ) on Prime
    gvi = w.s([w.s([], 'oveq2', '( t = p -> ( -u 1 / t ) = ( -u 1 / p ) )'), gf1], 'fvmptg',
              '( ( p e. Prime /\\ ( -u 1 / p ) e. _V ) -> ( %s ` p ) = ( -u 1 / p ) )' % GNEG)
    # inner products: rewrite muprod into the G-form
    BDP = '( %s /\\ p e. %s )' % (BD, PF('d'))
    fdp = mkst(w, BDP)
    pprm = fdp([fdp([], 'simpr', 'p e. %s' % PF('d')), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = fdp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    pcc = fdp([pnn], 'nncnd', 'p e. CC')
    pne = fdp([pnn], 'nnne0d', 'p =/= 0')
    m1cp = fdp([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '-u 1 e. CC')
    gclp = fdp([m1cp, pcc, pne], 'divcld', '( -u 1 / p ) e. CC')
    gexp = fdp([gclp, w.inst('elex')], 'syl', '( -u 1 / p ) e. _V')
    gvp = fdp([pprm, gexp, gvi], 'syl2anc', '( %s ` p ) = ( -u 1 / p )' % GNEG)
    prd = fd([gvp], 'prodeq2dv',
             'prod_ p e. %s ( %s ` p ) = prod_ p e. %s ( -u 1 / p )' % (PF('d'), GNEG, PF('d')))
    mup = fd([fd([dnn, dsq], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'), w.inst('muprod')],
             'syl', '( ( mmu ` d ) / d ) = prod_ p e. %s ( -u 1 / p )' % PF('d'))
    term2 = fd([mup, fd([prd], 'eqcomd',
               'prod_ p e. %s ( -u 1 / p ) = prod_ p e. %s ( %s ` p )' % (PF('d'), PF('d'), GNEG))],
               'eqtrd', '( ( mmu ` d ) / d ) = prod_ p e. %s ( %s ` p )' % (PF('d'), GNEG))
    e2 = st([term2], 'sumeq2dv', '%s = %s' % (S5, S6))
    # the outer product: 1 + ( -u 1 / p ) = ( p - 1 ) / p
    BTP = '( %s /\\ p e. %s )' % (A, TM)
    fq = mkst(w, BTP)
    qprm = fq([fq([], 'simpr', 'p e. %s' % TM), w.inst('elrabi')], 'syl', 'p e. Prime')
    qnn = fq([qprm, w.inst('prmnn')], 'syl', 'p e. NN')
    qc = fq([qnn], 'nncnd', 'p e. CC')
    qne = fq([qnn], 'nnne0d', 'p =/= 0')
    onec = fq([], '1cnd', '1 e. CC')
    gvq = fq([qprm, fq([fq([fq([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '-u 1 e. CC'), qc, qne],
                           'divcld', '( -u 1 / p ) e. CC'), w.inst('elex')], 'syl',
                       '( -u 1 / p ) e. _V'), gvi], 'syl2anc',
              '( %s ` p ) = ( -u 1 / p )' % GNEG)
    d1 = fq([qc, onec, qc, qne], 'divsubdird', '( ( p - 1 ) / p ) = ( ( p / p ) - ( 1 / p ) )')
    d2 = fq([qc, qne], 'dividd', '( p / p ) = 1')
    d3 = fq([d1, fq([d2], 'oveq1d', '( ( p / p ) - ( 1 / p ) ) = ( 1 - ( 1 / p ) )')], 'eqtrd',
            '( ( p - 1 ) / p ) = ( 1 - ( 1 / p ) )')
    d4 = fq([onec, fq([onec, qc, qne], 'divcld', '( 1 / p ) e. CC')], 'negsubd',
            '( 1 + -u ( 1 / p ) ) = ( 1 - ( 1 / p ) )')
    d5 = fq([onec, qc, qne], 'divnegd', '-u ( 1 / p ) = ( -u 1 / p )')
    d6 = fq([fq([d5], 'oveq2d', '( 1 + -u ( 1 / p ) ) = ( 1 + ( -u 1 / p ) )'), d4], 'eqtr3d',
            '( 1 + ( -u 1 / p ) ) = ( 1 - ( 1 / p ) )')
    d7 = fq([fq([gvq], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + ( -u 1 / p ) )' % GNEG), d6], 'eqtrd',
            '( 1 + ( %s ` p ) ) = ( 1 - ( 1 / p ) )' % GNEG)
    d8 = fq([d7, fq([d3], 'eqcomd', '( 1 - ( 1 / p ) ) = ( ( p - 1 ) / p )')], 'eqtrd',
            '( 1 + ( %s ` p ) ) = ( ( p - 1 ) / p )' % GNEG)
    e3 = st([d8], 'prodeq2dv', '%s = %s' % (P1, P2))
    # assemble
    a1 = st([lhs2, cbs], 'eqtrd', '( ( phi ` M ) / M ) = %s' % S4)
    a2 = st([a1, st([ss], 'eqcomd', '%s = %s' % (S4, S5))], 'eqtrd', '( ( phi ` M ) / M ) = %s' % S5)
    a3 = st([a2, e2], 'eqtrd', '( ( phi ` M ) / M ) = %s' % S6)
    a4 = st([a3, key], 'eqtrd', '( ( phi ` M ) / M ) = %s' % P1)
    w.qed([a4, e3], 'eqtrd', '( %s -> ( ( phi ` M ) / M ) = %s )' % (A, P2))
    return w


def prodctx(w, A, T, st):
    """closure steps for the products over T = the prime divisors: returns a dict"""
    B = '( %s /\\ p e. %s )' % (A, T)
    fp = mkst(w, B)
    pprm = fp([fp([], 'simpr', 'p e. %s' % T), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = fp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    pc = fp([pnn], 'nncnd', 'p e. CC')
    pne = fp([pnn], 'nnne0d', 'p =/= 0')
    puz = fp([pprm, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )')
    pm1rp = fp([puz, w.inst('uz2m1rp')], 'syl', '( p x. ( p - 1 ) ) e. RR+')
    onec = fp([], '1cnd', '1 e. CC')
    p1c = fp([pc, onec], 'subcld', '( p - 1 ) e. CC')
    mne = fp([pm1rp], 'rpne0d', '( p x. ( p - 1 ) ) =/= 0')
    p1ne = fp([pc, p1c, mne], 'mulne0bbd', '( p - 1 ) =/= 0')
    return dict(B=B, fp=fp, pc=pc, pne=pne, p1c=p1c, p1ne=p1ne)


def phirad():
    w = W('phirad',
          'The argument over its totient, as a product of p / ( p - 1 ) over the prime divisors.')
    A = 'M e. NN'
    T = PF('M')
    PP = PRD(T)
    PP1 = 'prod_ p e. %s ( p - 1 )' % T
    PA = 'prod_ p e. %s ( ( p - 1 ) / p )' % T
    PB = 'prod_ p e. %s ( p / ( p - 1 ) )' % T
    st = mkst(w, A)
    m = w.s([], 'id', '( %s -> M e. NN )' % A)
    mc = st([m], 'nncnd', 'M e. CC')
    mne = st([m], 'nnne0d', 'M =/= 0')
    phn = st([m, w.inst('phicl')], 'syl', '( phi ` M ) e. NN')
    phc = st([phn], 'nncnd', '( phi ` M ) e. CC')
    phne = st([phn], 'nnne0d', '( phi ` M ) =/= 0')
    finp = st([m, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('M', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('M', 'p'), T))], 'a1i',
             '%s = %s' % (PF('M', 'p'), T))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % T)
    c = prodctx(w, A, T, st)
    ppc = st([fin, c['pc']], 'fprodcl', '%s e. CC' % PP)
    ppne = st([fin, c['pc'], c['pne']], 'fprodn0', '%s =/= 0' % PP)
    pp1c = st([fin, c['p1c']], 'fprodcl', '%s e. CC' % PP1)
    pp1ne = st([fin, c['p1c'], c['p1ne']], 'fprodn0', '%s =/= 0' % PP1)
    fd1 = st([fin, c['p1c'], c['pc'], c['pne']], 'fproddiv', '%s = ( %s / %s )' % (PA, PP1, PP))
    fd2 = st([fin, c['pc'], c['p1c'], c['p1ne']], 'fproddiv', '%s = ( %s / %s )' % (PB, PP, PP1))
    pl = st([], 'phiradlem', '( ( phi ` M ) / M ) = %s' % PA)
    e1 = st([pl, fd1], 'eqtrd', '( ( phi ` M ) / M ) = ( %s / %s )' % (PP1, PP))
    rd1 = st([phc, mc, phne, mne], 'recdivd', '( 1 / ( ( phi ` M ) / M ) ) = ( M / ( phi ` M ) )')
    rd2 = st([pp1c, ppc, pp1ne, ppne], 'recdivd',
             '( 1 / ( %s / %s ) ) = ( %s / %s )' % (PP1, PP, PP, PP1))
    e2 = st([e1], 'oveq2d', '( 1 / ( ( phi ` M ) / M ) ) = ( 1 / ( %s / %s ) )' % (PP1, PP))
    e3 = st([st([rd1], 'eqcomd', '( M / ( phi ` M ) ) = ( 1 / ( ( phi ` M ) / M ) )'), e2], 'eqtrd',
            '( M / ( phi ` M ) ) = ( 1 / ( %s / %s ) )' % (PP1, PP))
    e4 = st([e3, rd2], 'eqtrd', '( M / ( phi ` M ) ) = ( %s / %s )' % (PP, PP1))
    w.qed([e4, st([fd2], 'eqcomd', '( %s / %s ) = %s' % (PP, PP1, PB))], 'eqtrd',
          '( %s -> ( M / ( phi ` M ) ) = %s )' % (A, PB))
    return w


def phisqf():
    w = W('phisqf',
          'The totient of a squarefree number is the product of p - 1 over its prime divisors.')
    A = '( D e. NN /\\ ( mmu ` D ) =/= 0 )'
    T = PF('D')
    PP = PRD(T)
    PP1 = 'prod_ p e. %s ( p - 1 )' % T
    PA = 'prod_ p e. %s ( ( p - 1 ) / p )' % T
    st = mkst(w, A)
    d = st([], 'simpl', 'D e. NN')
    dc = st([d], 'nncnd', 'D e. CC')
    dne = st([d], 'nnne0d', 'D =/= 0')
    phn = st([d, w.inst('phicl')], 'syl', '( phi ` D ) e. NN')
    phc = st([phn], 'nncnd', '( phi ` D ) e. CC')
    finp = st([d, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('D', 'p'))
    cbv = st([w.s([], 'cbvrabv', '%s = %s' % (PF('D', 'p'), T))], 'a1i',
             '%s = %s' % (PF('D', 'p'), T))
    fin = st([cbv, finp], 'eqeltrrd', '%s e. Fin' % T)
    c = prodctx(w, A, T, st)
    pp1c = st([fin, c['p1c']], 'fprodcl', '%s e. CC' % PP1)
    fd1 = st([fin, c['p1c'], c['pc'], c['pne']], 'fproddiv', '%s = ( %s / %s )' % (PA, PP1, PP))
    pid = st([], 'sqfprodid', '%s = D' % PP)
    pl = st([d, w.inst('phiradlem')], 'syl', '( ( phi ` D ) / D ) = %s' % PA)
    e1 = st([pl, fd1], 'eqtrd', '( ( phi ` D ) / D ) = ( %s / %s )' % (PP1, PP))
    e2 = st([e1, st([pid], 'oveq2d', '( %s / %s ) = ( %s / D )' % (PP1, PP, PP1))], 'eqtrd',
            '( ( phi ` D ) / D ) = ( %s / D )' % PP1)
    w.qed([phc, pp1c, dc, dne, e2], 'div11d', '( %s -> ( phi ` D ) = %s )' % (A, PP1))
    return w


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:] or ['muprod']:
        globals()[f]().run()
