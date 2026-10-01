"""Sortie v2b: the diagonalisation of the Selberg weights.

lwdterm   the summand of the diagonalisation as an inner sum over the divisors of P
lwkterm   the inner sum collapses by truncated Moebius inversion
lwdiag    diagonalisation of the Selberg weights
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2b_lib import *

SR = '( 1 / %s )' % SS()
FT = ('if ( ( L || d /\\ ( d || n /\\ ( n ^ 2 ) <_ Y ) ) , '
      '( ( %s x. %s ) x. ( mmu ` d ) ) , 0 )' % (GT('n'), SR))
KT = 'if ( ( d || n /\\ ( n ^ 2 ) <_ Y ) , %s , 0 )' % GT('n')
LT = 'if ( ( d || l /\\ ( l ^ 2 ) <_ Y ) , %s , 0 )' % GT('l')
GK = 'if ( ( n ^ 2 ) <_ Y , ( ( %s x. ( mmu ` L ) ) x. %s ) , 0 )' % (GT('n'), SR)
ANTE = '( %s /\\ ( L e. NN /\\ L || P ) )' % SH
DVP = DV('P')


def _base(w, A, chain):
    d = shsteps(w, A, chain)
    st = d['st']
    return d, st


def _elv(w, v, X, S=None):
    S = S or DV(X)
    return w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (v, X, v, X))],
               'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (v, S, v, v, X))


def lwdterm():
    w = W('lwdterm', 'The summand of the diagonalisation of the Selberg weights as a sum over the '
                     'divisors of the sifting product.')
    A = '( %s /\\ d e. %s )' % (ANTE, DVP)
    TD = 'if ( L || d , ( ( V ` d ) x. %s ) , 0 )' % LW('d')
    d = shsteps(w, A, (ANTE, SH))
    st = d['st']
    lnn = st([st([st([], 'simpl', ANTE)], 'simprd', '( L e. NN /\\ L || P )')], 'simpld',
             'L e. NN')
    dmem = w.s([], 'simpr', '( %s -> d e. %s )' % (A, DVP))
    dc = st([st([_elv(w, 'd', 'P')], 'a1i', '( d e. %s <-> ( d e. NN /\\ d || P ) )' % DVP),
             dmem], 'mpbid', '( d e. NN /\\ d || P )')
    dnn = st([dc], 'simpld', 'd e. NN')
    ddp = st([dc], 'simprd', 'd || P')
    muc = st([st([dnn, w.inst('mucl')], 'syl', '( mmu ` d ) e. ZZ')], 'zcnd',
             '( mmu ` d ) e. CC')
    src = st([st([st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())], 'rpreccld',
                 '%s e. RR+' % SR)], 'rpcnd', '%s e. CC' % SR)
    smc = st([src, muc], 'mulcld', '( %s x. ( mmu ` d ) ) e. CC' % SR)
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    # ---- the branch L || d , with n ranging over DV ( P )
    AD = '( %s /\ L || d )' % A
    sdl = mkst(w, AD)
    ADK = '( %s /\ n e. %s )' % (AD, DVP)
    sk = mkst(w, ADK)
    kc = sk([sk([_elv(w, 'n', 'P')], 'a1i', '( n e. %s <-> ( n e. NN /\ n || P ) )' % DVP),
             sk([], 'simpr', 'n e. %s' % DVP)], 'mpbid', '( n e. NN /\ n || P )')
    shk = sk([sdl([d['sh']], 'adantr', SH)], 'adantr', SH)
    gkc = sk([sk([sk([shk, kc, w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('n'))], 'rpred',
                 '%s e. RR' % GT('n'))], 'recnd', '%s e. CC' % GT('n'))
    ktc = sk([gkc, w.s([], '0cnd', '( %s -> 0 e. CC )' % ADK)], 'ifcld', '%s e. CC' % KT)
    srck = sk([sdl([src], 'adantr', '%s e. CC' % SR)], 'adantr', '%s e. CC' % SR)
    muck = sk([sdl([muc], 'adantr', '( mmu ` d ) e. CC')], 'adantr', '( mmu ` d ) e. CC')
    smck = sk([srck, muck], 'mulcld', '( %s x. ( mmu ` d ) ) e. CC' % SR)
    ldk = w.s([], 'simplr', '( %s -> L || d )' % ADK)
    ADKT = '( %s /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )' % ADK
    skdt = mkst(w, ADKT)
    srct = skdt([srck], 'adantr', '%s e. CC' % SR)
    muct = skdt([muck], 'adantr', '( mmu ` d ) e. CC')
    gkct = skdt([gkc], 'adantr', '%s e. CC' % GT('n'))
    t1 = skdt([skdt([], 'iftrued', '%s = %s' % (KT, GT('n')))], 'oveq2d',
              '( ( %s x. ( mmu ` d ) ) x. %s ) = ( ( %s x. ( mmu ` d ) ) x. %s )'
              % (SR, KT, SR, GT('n')))
    r1 = skdt([srct, muct, gkct], 'mulassd',
              '( ( %s x. ( mmu ` d ) ) x. %s ) = ( %s x. ( ( mmu ` d ) x. %s ) )'
              % (SR, GT('n'), SR, GT('n')))
    r2 = skdt([skdt([muct, gkct], 'mulcomd',
                    '( ( mmu ` d ) x. %s ) = ( %s x. ( mmu ` d ) )' % (GT('n'), GT('n')))],
              'oveq2d', '( %s x. ( ( mmu ` d ) x. %s ) ) = ( %s x. ( %s x. ( mmu ` d ) ) )'
              % (SR, GT('n'), SR, GT('n')))
    r3 = skdt([skdt([srct, gkct, muct], 'mulassd',
                    '( ( %s x. %s ) x. ( mmu ` d ) ) = ( %s x. ( %s x. ( mmu ` d ) ) )'
                    % (SR, GT('n'), SR, GT('n')))], 'eqcomd',
              '( %s x. ( %s x. ( mmu ` d ) ) ) = ( ( %s x. %s ) x. ( mmu ` d ) )'
              % (SR, GT('n'), SR, GT('n')))
    r4 = skdt([skdt([srct, gkct], 'mulcomd',
                    '( %s x. %s ) = ( %s x. %s )' % (SR, GT('n'), GT('n'), SR))], 'oveq1d',
              '( ( %s x. %s ) x. ( mmu ` d ) ) = ( ( %s x. %s ) x. ( mmu ` d ) )'
              % (SR, GT('n'), GT('n'), SR))
    rall = skdt([skdt([skdt([r1, r2], 'eqtrd',
                            '( ( %s x. ( mmu ` d ) ) x. %s ) = ( %s x. ( %s x. ( mmu ` d ) ) )'
                            % (SR, GT('n'), SR, GT('n'))), r3], 'eqtrd',
                      '( ( %s x. ( mmu ` d ) ) x. %s ) = ( ( %s x. %s ) x. ( mmu ` d ) )'
                      % (SR, GT('n'), SR, GT('n'))), r4], 'eqtrd',
                '( ( %s x. ( mmu ` d ) ) x. %s ) = ( ( %s x. %s ) x. ( mmu ` d ) )'
                % (SR, GT('n'), GT('n'), SR))
    ftv = skdt([skdt([skdt([ldk], 'adantr', 'L || d'),
                      skdt([], 'simpr', '( d || n /\ ( n ^ 2 ) <_ Y )')], 'jca',
                     '( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )')], 'iftrued',
               '%s = ( ( %s x. %s ) x. ( mmu ` d ) )' % (FT, GT('n'), SR))
    caseT = skdt([skdt([t1, rall], 'eqtrd',
                       '( ( %s x. ( mmu ` d ) ) x. %s ) = ( ( %s x. %s ) x. ( mmu ` d ) )'
                       % (SR, KT, GT('n'), SR)), ftv], 'eqtr4d',
                 '( ( %s x. ( mmu ` d ) ) x. %s ) = %s' % (SR, KT, FT))
    ADKF = '( %s /\ -. ( d || n /\ ( n ^ 2 ) <_ Y ) )' % ADK
    skdf = mkst(w, ADKF)
    caseF = skdf([skdf([skdf([skdf([], 'iffalsed', '%s = 0' % KT)], 'oveq2d',
                             '( ( %s x. ( mmu ` d ) ) x. %s ) = ( ( %s x. ( mmu ` d ) ) x. 0 )'
                             % (SR, KT, SR)),
                        skdf([skdf([smck], 'adantr',
                                   '( %s x. ( mmu ` d ) ) e. CC' % SR)], 'mul01d',
                             '( ( %s x. ( mmu ` d ) ) x. 0 ) = 0' % SR)], 'eqtrd',
                       '( ( %s x. ( mmu ` d ) ) x. %s ) = 0' % (SR, KT)),
                  skdf([skdf([skdf([], 'simpr', '-. ( d || n /\ ( n ^ 2 ) <_ Y )')], 'intnand',
                             '-. ( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )')], 'iffalsed',
                       '%s = 0' % FT)], 'eqtr4d',
                 '( ( %s x. ( mmu ` d ) ) x. %s ) = %s' % (SR, KT, FT))
    termD = sk([caseT, caseF], 'pm2.61dan',
               '( ( %s x. ( mmu ` d ) ) x. %s ) = %s' % (SR, KT, FT))
    lw = sdl([sdl([d['sh']], 'adantr', SH), sdl([dnn], 'adantr', 'd e. NN')], 'jca',
             '( %s /\ d e. NN )' % SH)
    lwd = sdl([lw, w.inst('lwdvds')], 'syl',
              '( ( V ` d ) x. %s ) = ( ( %s x. ( mmu ` d ) ) x. sum_ l e. %s %s )'
              % (LW('d'), SR, DVP, LT))
    cbv = sdl([w.s([], 'cbvsumv',
                   'sum_ l e. %s %s = sum_ n e. %s %s' % (DVP, LT, DVP, KT))], 'a1i',
              'sum_ l e. %s %s = sum_ n e. %s %s' % (DVP, LT, DVP, KT))
    lwd2 = sdl([lwd, sdl([cbv], 'oveq2d',
                         '( ( %s x. ( mmu ` d ) ) x. sum_ l e. %s %s ) = '
                         '( ( %s x. ( mmu ` d ) ) x. sum_ n e. %s %s )'
                         % (SR, DVP, LT, SR, DVP, KT))], 'eqtrd',
               '( ( V ` d ) x. %s ) = ( ( %s x. ( mmu ` d ) ) x. sum_ n e. %s %s )'
               % (LW('d'), SR, DVP, KT))
    pull = sdl([sdl([finP], 'adantr', '%s e. Fin' % DVP),
                sdl([smc], 'adantr', '( %s x. ( mmu ` d ) ) e. CC' % SR), ktc], 'fsummulc2',
               '( ( %s x. ( mmu ` d ) ) x. sum_ n e. %s %s ) = '
               'sum_ n e. %s ( ( %s x. ( mmu ` d ) ) x. %s )' % (SR, DVP, KT, DVP, SR, KT))
    sumeq = sdl([termD], 'sumeq2dv',
                'sum_ n e. %s ( ( %s x. ( mmu ` d ) ) x. %s ) = sum_ n e. %s %s'
                % (DVP, SR, KT, DVP, FT))
    tdv = sdl([sdl([], 'simpr', 'L || d')], 'iftrued', '%s = ( ( V ` d ) x. %s )' % (TD, LW('d')))
    case1 = sdl([tdv, sdl([sdl([lwd2, pull], 'eqtrd',
                               '( ( V ` d ) x. %s ) = '
                               'sum_ n e. %s ( ( %s x. ( mmu ` d ) ) x. %s )'
                               % (LW('d'), DVP, SR, KT)), sumeq], 'eqtrd',
                          '( ( V ` d ) x. %s ) = sum_ n e. %s %s' % (LW('d'), DVP, FT))], 'eqtrd',
                '%s = sum_ n e. %s %s' % (TD, DVP, FT))
    # case -. L || d
    ADF = '( %s /\\ -. L || d )' % A
    sdf2 = mkst(w, ADF)
    AKF = '( %s /\\ n e. %s )' % (ADF, DVP)
    skf = mkst(w, AKF)
    ftz = skf([skf([skf([sdf2([], 'simpr', '-. L || d')], 'adantr', '-. L || d')], 'intnanrd',
                   '-. ( L || d /\\ ( d || n /\\ ( n ^ 2 ) <_ Y ) )')], 'iffalsed', '%s = 0' % FT)
    case2 = sdf2([sdf2([], 'iffalsed', '%s = 0' % TD),
                  sdf2([sdf2([ftz], 'sumeq2dv',
                             'sum_ n e. %s %s = sum_ n e. %s 0' % (DVP, FT, DVP)),
                        sdf2([sdf2([sdf2([finP], 'adantr', '%s e. Fin' % DVP)], 'olcd',
                                   '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (DVP, DVP)),
                              w.inst('sumz')], 'syl', 'sum_ n e. %s 0 = 0' % DVP)], 'eqtrd',
                       'sum_ n e. %s %s = 0' % (DVP, FT))], 'eqtr4d',
                 '%s = sum_ n e. %s %s' % (TD, DVP, FT))
    w.qed([case1, case2], 'pm2.61dan',
          '( %s -> %s = sum_ n e. %s %s )' % (A, TD, DVP, FT))
    return w


MT = 'if ( ( L || d /\ d || n ) , ( mmu ` d ) , 0 )'


def lwkterm():
    w = W('lwkterm', 'The inner sum of the diagonalisation of the Selberg weights collapses by '
                     'truncated Moebius inversion.')
    A = '( %s /\ n e. %s )' % (ANTE, DVP)
    C = '( %s x. %s )' % (GT('n'), SR)
    d = shsteps(w, A, (ANTE, SH))
    st = d['st']
    lc = st([st([], 'simpl', ANTE)], 'simprd', '( L e. NN /\ L || P )')
    lnn = st([lc], 'simpld', 'L e. NN')
    mulc = st([st([lnn, w.inst('mucl')], 'syl', '( mmu ` L ) e. ZZ')], 'zcnd',
              '( mmu ` L ) e. CC')
    nmem = w.s([], 'simpr', '( %s -> n e. %s )' % (A, DVP))
    nc = st([st([_elv(w, 'n', 'P')], 'a1i', '( n e. %s <-> ( n e. NN /\ n || P ) )' % DVP),
             nmem], 'mpbid', '( n e. NN /\ n || P )')
    gnc = st([st([st([d['sh'], nc, w.inst('gtrp')], 'syl2anc', '%s e. RR+' % GT('n'))], 'rpred',
                 '%s e. RR' % GT('n'))], 'recnd', '%s e. CC' % GT('n'))
    src = st([st([st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())], 'rpreccld',
                 '%s e. RR+' % SR)], 'rpcnd', '%s e. CC' % SR)
    cc = st([gnc, src], 'mulcld', '%s e. CC' % C)
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    inv = st([st([st([d['pnn'], d['psqf']], 'jca', '( P e. NN /\ ( mmu ` P ) =/= 0 )'), nc, lnn],
                 '3jca',
                 '( ( P e. NN /\ ( mmu ` P ) =/= 0 ) /\ ( n e. NN /\ n || P ) /\ L e. NN )'),
              w.inst('muinvdvds2')], 'syl',
             'sum_ d e. %s %s = if ( L = n , ( mmu ` L ) , 0 )' % (DVP, MT))
    # ---------- case ( n ^ 2 ) <_ Y
    AT = '( %s /\ ( n ^ 2 ) <_ Y )' % A
    sat = mkst(w, AT)
    ATD = '( %s /\ d e. %s )' % (AT, DVP)
    satd = mkst(w, ATD)
    dc = satd([satd([_elv(w, 'd', 'P')], 'a1i',
                    '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP),
               satd([], 'simpr', 'd e. %s' % DVP)], 'mpbid', '( d e. NN /\ d || P )')
    mudc = satd([satd([satd([dc], 'simpld', 'd e. NN'), w.inst('mucl')], 'syl',
                      '( mmu ` d ) e. ZZ')], 'zcnd', '( mmu ` d ) e. CC')
    ccd = satd([sat([cc], 'adantr', '%s e. CC' % C)], 'adantr', '%s e. CC' % C)
    yat = satd([satd([], 'simpl', AT)], 'simprd', '( n ^ 2 ) <_ Y')
    ATDT = '( %s /\ ( L || d /\ d || n ) )' % ATD
    s1 = mkst(w, ATDT)
    cond1 = s1([s1([s1([s1([], 'simpr', '( L || d /\ d || n )')], 'simpld', 'L || d'),
                    s1([s1([s1([], 'simpr', '( L || d /\ d || n )')], 'simprd', 'd || n'),
                        s1([yat], 'adantr', '( n ^ 2 ) <_ Y')], 'jca',
                       '( d || n /\ ( n ^ 2 ) <_ Y )')], 'jca',
                   '( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )')], 'iftrued',
               '%s = ( %s x. ( mmu ` d ) )' % (FT, C))
    mt1 = s1([s1([], 'simpr', '( L || d /\ d || n )')], 'iftrued', '%s = ( mmu ` d )' % MT)
    rhs1 = s1([s1([mt1], 'oveq1d', '( %s x. %s ) = ( ( mmu ` d ) x. %s )' % (MT, C, C)),
               s1([s1([mudc], 'adantr', '( mmu ` d ) e. CC'),
                   s1([ccd], 'adantr', '%s e. CC' % C)], 'mulcomd',
                  '( ( mmu ` d ) x. %s ) = ( %s x. ( mmu ` d ) )' % (C, C))], 'eqtrd',
              '( %s x. %s ) = ( %s x. ( mmu ` d ) )' % (MT, C, C))
    case1 = s1([cond1, rhs1], 'eqtr4d', '%s = ( %s x. %s )' % (FT, MT, C))
    ATDF = '( %s /\ -. ( L || d /\ d || n ) )' % ATD
    s2 = mkst(w, ATDF)
    ATDFC = '( %s /\ ( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) ) )' % ATDF
    s3 = mkst(w, ATDFC)
    imp = s3([s3([s3([], 'simpr', '( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )')], 'simpld',
                     'L || d'),
                  s3([s3([s3([], 'simpr', '( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )')],
                         'simprd', '( d || n /\ ( n ^ 2 ) <_ Y )')], 'simpld', 'd || n')], 'jca',
                 '( L || d /\ d || n )')
    nocond = s2([s2([], 'simpr', '-. ( L || d /\ d || n )'), imp], 'mtand',
                '-. ( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )')
    case2 = s2([s2([nocond], 'iffalsed', '%s = 0' % FT),
                s2([s2([s2([s2([], 'simpr', '-. ( L || d /\ d || n )')], 'iffalsed',
                           '%s = 0' % MT)], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (MT, C, C)),
                    s2([s2([ccd], 'adantr', '%s e. CC' % C)], 'mul02d',
                       '( 0 x. %s ) = 0' % C)], 'eqtrd', '( %s x. %s ) = 0' % (MT, C))], 'eqtr4d',
               '%s = ( %s x. %s )' % (FT, MT, C))
    termT = satd([case1, case2], 'pm2.61dan', '%s = ( %s x. %s )' % (FT, MT, C))
    mtc = satd([mudc, w.s([], '0cnd', '( %s -> 0 e. CC )' % ATD)], 'ifcld', '%s e. CC' % MT)
    sumT = sat([sat([termT], 'sumeq2dv',
                    'sum_ d e. %s %s = sum_ d e. %s ( %s x. %s )' % (DVP, FT, DVP, MT, C)),
                sat([sat([sat([finP], 'adantr', '%s e. Fin' % DVP), mtc,
                          sat([cc], 'adantr', '%s e. CC' % C)], 'fsummulc1',
                         '( sum_ d e. %s %s x. %s ) = sum_ d e. %s ( %s x. %s )'
                         % (DVP, MT, C, DVP, MT, C))], 'eqcomd',
                     'sum_ d e. %s ( %s x. %s ) = ( sum_ d e. %s %s x. %s )'
                     % (DVP, MT, C, DVP, MT, C))], 'eqtrd',
               'sum_ d e. %s %s = ( sum_ d e. %s %s x. %s )' % (DVP, FT, DVP, MT, C))
    sumT2 = sat([sumT, sat([sat([inv], 'adantr',
                                'sum_ d e. %s %s = if ( L = n , ( mmu ` L ) , 0 )' % (DVP, MT))],
                           'oveq1d',
                           '( sum_ d e. %s %s x. %s ) = ( if ( L = n , ( mmu ` L ) , 0 ) x. %s )'
                           % (DVP, MT, C, C))], 'eqtrd',
                'sum_ d e. %s %s = ( if ( L = n , ( mmu ` L ) , 0 ) x. %s )' % (DVP, FT, C))
    # subcase n = L
    ATE = '( %s /\ n = L )' % AT
    s4 = mkst(w, ATE)
    lne = s4([s4([], 'simpr', 'n = L')], 'eqcomd', 'L = n')
    mulc4 = s4([sat([mulc], 'adantr', '( mmu ` L ) e. CC')], 'adantr', '( mmu ` L ) e. CC')
    gnc4 = s4([sat([gnc], 'adantr', '%s e. CC' % GT('n'))], 'adantr', '%s e. CC' % GT('n'))
    src4 = s4([sat([src], 'adantr', '%s e. CC' % SR)], 'adantr', '%s e. CC' % SR)
    alg = s4([s4([s4([mulc4, gnc4, src4], 'mulassd',
                     '( ( ( mmu ` L ) x. %s ) x. %s ) = ( ( mmu ` L ) x. ( %s x. %s ) )'
                     % (GT('n'), SR, GT('n'), SR))], 'eqcomd',
                  '( ( mmu ` L ) x. ( %s x. %s ) ) = ( ( ( mmu ` L ) x. %s ) x. %s )'
                  % (GT('n'), SR, GT('n'), SR)),
              s4([s4([mulc4, gnc4], 'mulcomd',
                     '( ( mmu ` L ) x. %s ) = ( %s x. ( mmu ` L ) )'
                     % (GT('n'), GT('n')))], 'oveq1d',
                 '( ( ( mmu ` L ) x. %s ) x. %s ) = ( ( %s x. ( mmu ` L ) ) x. %s )'
                 % (GT('n'), SR, GT('n'), SR))], 'eqtrd',
             '( ( mmu ` L ) x. %s ) = ( ( %s x. ( mmu ` L ) ) x. %s )' % (C, GT('n'), SR))
    lhs4 = s4([s4([sumT2], 'adantr',
                  'sum_ d e. %s %s = ( if ( L = n , ( mmu ` L ) , 0 ) x. %s )' % (DVP, FT, C)),
               s4([s4([lne], 'iftrued', 'if ( L = n , ( mmu ` L ) , 0 ) = ( mmu ` L )')],
                  'oveq1d',
                  '( if ( L = n , ( mmu ` L ) , 0 ) x. %s ) = ( ( mmu ` L ) x. %s )' % (C, C))],
              'eqtrd', 'sum_ d e. %s %s = ( ( mmu ` L ) x. %s )' % (DVP, FT, C))
    rhs4 = s4([s4([], 'iftrued', 'if ( n = L , %s , 0 ) = %s' % (GK, GK)),
               s4([s4([sat([], 'simpr', '( n ^ 2 ) <_ Y')], 'adantr', '( n ^ 2 ) <_ Y')],
                  'iftrued',
                  '%s = ( ( %s x. ( mmu ` L ) ) x. %s )' % (GK, GT('n'), SR))], 'eqtrd',
              'if ( n = L , %s , 0 ) = ( ( %s x. ( mmu ` L ) ) x. %s )' % (GK, GT('n'), SR))
    caseTE = s4([s4([lhs4, alg], 'eqtrd',
                    'sum_ d e. %s %s = ( ( %s x. ( mmu ` L ) ) x. %s )'
                    % (DVP, FT, GT('n'), SR)), rhs4], 'eqtr4d',
                'sum_ d e. %s %s = if ( n = L , %s , 0 )' % (DVP, FT, GK))
    # subcase -. n = L
    ATN = '( %s /\ -. n = L )' % AT
    s5 = mkst(w, ATN)
    nne = s5([s5([s5([], 'simpr', '-. n = L')], 'neqned', 'n =/= L')], 'necomd', 'L =/= n')
    lhs5 = s5([s5([s5([sumT2], 'adantr',
                      'sum_ d e. %s %s = ( if ( L = n , ( mmu ` L ) , 0 ) x. %s )'
                      % (DVP, FT, C)),
                   s5([s5([s5([nne], 'neneqd', '-. L = n')], 'iffalsed',
                          'if ( L = n , ( mmu ` L ) , 0 ) = 0')], 'oveq1d',
                      '( if ( L = n , ( mmu ` L ) , 0 ) x. %s ) = ( 0 x. %s )' % (C, C))],
                  'eqtrd', 'sum_ d e. %s %s = ( 0 x. %s )' % (DVP, FT, C)),
               s5([s5([sat([cc], 'adantr', '%s e. CC' % C)], 'adantr', '%s e. CC' % C)],
                  'mul02d', '( 0 x. %s ) = 0' % C)], 'eqtrd',
              'sum_ d e. %s %s = 0' % (DVP, FT))
    caseTN = s5([lhs5, s5([s5([], 'iffalsed', 'if ( n = L , %s , 0 ) = 0' % GK)], 'eqcomd',
                          '0 = if ( n = L , %s , 0 )' % GK)], 'eqtrd',
                'sum_ d e. %s %s = if ( n = L , %s , 0 )' % (DVP, FT, GK))
    caseT = sat([caseTE, caseTN], 'pm2.61dan',
                'sum_ d e. %s %s = if ( n = L , %s , 0 )' % (DVP, FT, GK))
    # ---------- case -. ( n ^ 2 ) <_ Y
    AF = '( %s /\ -. ( n ^ 2 ) <_ Y )' % A
    saf = mkst(w, AF)
    AFD = '( %s /\ d e. %s )' % (AF, DVP)
    safd = mkst(w, AFD)
    noy = safd([safd([safd([safd([], 'simpl', AF)], 'simprd', '-. ( n ^ 2 ) <_ Y')], 'intnand',
                     '-. ( d || n /\ ( n ^ 2 ) <_ Y )')], 'intnand',
               '-. ( L || d /\ ( d || n /\ ( n ^ 2 ) <_ Y ) )')
    zerd = safd([noy], 'iffalsed', '%s = 0' % FT)
    sumF = saf([saf([zerd], 'sumeq2dv',
                    'sum_ d e. %s %s = sum_ d e. %s 0' % (DVP, FT, DVP)),
                saf([saf([saf([finP], 'adantr', '%s e. Fin' % DVP)], 'olcd',
                         '( %s C_ ( ZZ>= ` 1 ) \/ %s e. Fin )' % (DVP, DVP)),
                     w.inst('sumz')], 'syl', 'sum_ d e. %s 0 = 0' % DVP)], 'eqtrd',
               'sum_ d e. %s %s = 0' % (DVP, FT))
    AFE = '( %s /\ n = L )' % AF
    s6 = mkst(w, AFE)
    gk0 = s6([s6([saf([], 'simpr', '-. ( n ^ 2 ) <_ Y')], 'adantr',
                 '-. ( n ^ 2 ) <_ Y')], 'iffalsed', '%s = 0' % GK)
    r6 = s6([s6([], 'iftrued', 'if ( n = L , %s , 0 ) = %s' % (GK, GK)), gk0], 'eqtrd',
            'if ( n = L , %s , 0 ) = 0' % GK)
    AFN = '( %s /\ -. n = L )' % AF
    s7 = mkst(w, AFN)
    r7 = s7([], 'iffalsed', 'if ( n = L , %s , 0 ) = 0' % GK)
    rhsF = saf([r6, r7], 'pm2.61dan', 'if ( n = L , %s , 0 ) = 0' % GK)
    caseF = saf([sumF, saf([rhsF], 'eqcomd', '0 = if ( n = L , %s , 0 )' % GK)], 'eqtrd',
                'sum_ d e. %s %s = if ( n = L , %s , 0 )' % (DVP, FT, GK))
    w.qed([caseT, caseF], 'pm2.61dan',
          '( %s -> sum_ d e. %s %s = if ( n = L , %s , 0 ) )' % (A, DVP, FT, GK))
    return w


def lwdiag():
    w = W('lwdiag', 'Diagonalisation of the Selberg weights.')
    A = ANTE
    TD = 'if ( L || d , ( ( V ` d ) x. %s ) , 0 )' % LW('d')
    GKL = 'if ( ( L ^ 2 ) <_ Y , ( ( %s x. ( mmu ` L ) ) x. %s ) , 0 )' % (GT('L'), SR)
    TN = 'if ( n = L , %s , 0 )' % GK
    d = shsteps(w, A, (SH,))
    st = d['st']
    lc = st([], 'simpr', '( L e. NN /\ L || P )')
    lnn = st([lc], 'simpld', 'L e. NN')
    ldp = st([lc], 'simprd', 'L || P')
    mulc = st([st([lnn, w.inst('mucl')], 'syl', '( mmu ` L ) e. ZZ')], 'zcnd',
              '( mmu ` L ) e. CC')
    src = st([st([st([d['sh'], w.inst('ssrp')], 'syl', '%s e. RR+' % SS())], 'rpreccld',
                 '%s e. RR+' % SR)], 'rpcnd', '%s e. CC' % SR)
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    # step 1 : each term becomes an inner sum
    AD = '( %s /\ d e. %s )' % (A, DVP)
    sd = mkst(w, AD)
    tdeq = w.s([], 'lwdterm',
               '( %s -> %s = sum_ n e. %s %s )' % (AD, TD, DVP, FT))
    step1 = st([tdeq], 'sumeq2dv',
               'sum_ d e. %s %s = sum_ d e. %s sum_ n e. %s %s' % (DVP, TD, DVP, DVP, FT))
    # step 2 : the swap
    APR = '( %s /\ ( d e. %s /\ n e. %s ) )' % (A, DVP, DVP)
    spr = mkst(w, APR)
    dmem = w.s([w.s([], 'simpr', '( %s -> ( d e. %s /\ n e. %s ) )' % (APR, DVP, DVP))],
               'simpld', '( %s -> d e. %s )' % (APR, DVP))
    nmem = w.s([w.s([], 'simpr', '( %s -> ( d e. %s /\ n e. %s ) )' % (APR, DVP, DVP))],
               'simprd', '( %s -> n e. %s )' % (APR, DVP))
    dcp = spr([spr([_elv(w, 'd', 'P')], 'a1i', '( d e. %s <-> ( d e. NN /\ d || P ) )' % DVP),
               dmem], 'mpbid', '( d e. NN /\ d || P )')
    ncp = spr([spr([_elv(w, 'n', 'P')], 'a1i', '( n e. %s <-> ( n e. NN /\ n || P ) )' % DVP),
               nmem], 'mpbid', '( n e. NN /\ n || P )')
    mudp = spr([spr([spr([dcp], 'simpld', 'd e. NN'), w.inst('mucl')], 'syl',
                    '( mmu ` d ) e. ZZ')], 'zcnd', '( mmu ` d ) e. CC')
    gnp = spr([spr([spr([spr([d['sh']], 'adantr', SH), ncp, w.inst('gtrp')], 'syl2anc',
                        '%s e. RR+' % GT('n'))], 'rpred', '%s e. RR' % GT('n'))], 'recnd',
              '%s e. CC' % GT('n'))
    ftc = spr([spr([spr([gnp, spr([src], 'adantr', '%s e. CC' % SR)], 'mulcld',
                        '( %s x. %s ) e. CC' % (GT('n'), SR)), mudp], 'mulcld',
                   '( ( %s x. %s ) x. ( mmu ` d ) ) e. CC' % (GT('n'), SR)),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % APR)], 'ifcld', '%s e. CC' % FT)
    swap = st([finP, finP, ftc], 'fsumcom',
              'sum_ d e. %s sum_ n e. %s %s = sum_ n e. %s sum_ d e. %s %s'
              % (DVP, DVP, FT, DVP, DVP, FT))
    # step 3 : the inner sum collapses
    AN = '( %s /\ n e. %s )' % (A, DVP)
    sn = mkst(w, AN)
    step3 = st([w.s([], 'lwkterm',
                    '( %s -> sum_ d e. %s %s = %s )' % (AN, DVP, FT, TN))], 'sumeq2dv',
               'sum_ n e. %s sum_ d e. %s %s = sum_ n e. %s %s' % (DVP, DVP, FT, DVP, TN))
    # step 4 : the singleton
    lin = st([w.s([w.s([], 'breq1', '( x = L -> ( x || P <-> L || P ) )')], 'elrab',
                  '( L e. %s <-> ( L e. NN /\ L || P ) )' % DVP), lc], 'sylibr',
             'L e. %s' % DVP)
    snss = st([lin], 'snssd', '{ L } C_ %s' % DVP)
    ASN = '( %s /\ n e. { L } )' % A
    ssn = mkst(w, ASN)
    neq = ssn([ssn([], 'simpr', 'n e. { L }'), w.inst('elsni')], 'syl', 'n = L')
    nin = ssn([neq, ssn([lin], 'adantr', 'L e. %s' % DVP)], 'eqeltrd', 'n e. %s' % DVP)
    ncs = ssn([ssn([_elv(w, 'n', 'P')], 'a1i',
                   '( n e. %s <-> ( n e. NN /\ n || P ) )' % DVP), nin], 'mpbid',
              '( n e. NN /\ n || P )')
    gns = ssn([ssn([ssn([ssn([d['sh']], 'adantr', SH), ncs, w.inst('gtrp')], 'syl2anc',
                        '%s e. RR+' % GT('n'))], 'rpred', '%s e. RR' % GT('n'))], 'recnd',
              '%s e. CC' % GT('n'))
    gkc = ssn([ssn([ssn([gns, ssn([mulc], 'adantr', '( mmu ` L ) e. CC')], 'mulcld',
                        '( %s x. ( mmu ` L ) ) e. CC' % GT('n')),
                    ssn([src], 'adantr', '%s e. CC' % SR)], 'mulcld',
                   '( ( %s x. ( mmu ` L ) ) x. %s ) e. CC' % (GT('n'), SR)),
               w.s([], '0cnd', '( %s -> 0 e. CC )' % ASN)], 'ifcld', '%s e. CC' % GK)
    tnc = ssn([gkc, w.s([], '0cnd', '( %s -> 0 e. CC )' % ASN)], 'ifcld', '%s e. CC' % TN)
    ADF = '( %s /\ n e. ( %s \ { L } ) )' % (A, DVP)
    sdf = mkst(w, ADF)
    zern = sdf([sdf([sdf([sdf([], 'simpr', 'n e. ( %s \ { L } )' % DVP), w.inst('eldifsni')],
                         'syl', 'n =/= L')], 'neneqd', '-. n = L')], 'iffalsed', '%s = 0' % TN)
    sss = st([snss, tnc, zern, finP], 'fsumss',
             'sum_ n e. { L } %s = sum_ n e. %s %s' % (TN, DVP, TN))
    # the substitution hypothesis
    gtsub = w.s([w.s([], 'fveq2', '( n = L -> ( V ` n ) = ( V ` L ) )'),
                 w.s([w.s([w.s([], 'breq2', '( n = L -> ( r || n <-> r || L ) )')], 'rabbidv',
                          '( n = L -> %s = %s )' % (PF('n'), PF('L')))], 'prodeq1d',
                     '( n = L -> prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) = '
                     'prod_ q e. %s ( 1 / ( 1 - ( V ` q ) ) ) )' % (PF('n'), PF('L')))],
                'oveq12d', '( n = L -> %s = %s )' % (GT('n'), GT('L')))
    gksub = w.s([w.s([w.s([], 'oveq1', '( n = L -> ( n ^ 2 ) = ( L ^ 2 ) )')], 'breq1d',
                     '( n = L -> ( ( n ^ 2 ) <_ Y <-> ( L ^ 2 ) <_ Y ) )'),
                 w.s([w.s([gtsub], 'oveq1d',
                          '( n = L -> ( %s x. ( mmu ` L ) ) = ( %s x. ( mmu ` L ) ) )'
                          % (GT('n'), GT('L')))], 'oveq1d',
                     '( n = L -> ( ( %s x. ( mmu ` L ) ) x. %s ) = '
                     '( ( %s x. ( mmu ` L ) ) x. %s ) )' % (GT('n'), SR, GT('L'), SR))],
                'ifbieq1d', '( n = L -> %s = %s )' % (GK, GKL))
    hsn = w.s([w.s([w.s([], 'id', '( n = L -> n = L )')], 'iftrued',
                   '( n = L -> %s = %s )' % (TN, GK)), gksub], 'eqtrd',
              '( n = L -> %s = %s )' % (TN, GKL))
    gklcc = st([st([st([st([st([d['sh'], lc, w.inst('gtrp')], 'syl2anc',
                              '%s e. RR+' % GT('L'))], 'rpred', '%s e. RR' % GT('L'))], 'recnd',
                       '%s e. CC' % GT('L')), mulc], 'mulcld',
                   '( %s x. ( mmu ` L ) ) e. CC' % GT('L')), src], 'mulcld',
               '( ( %s x. ( mmu ` L ) ) x. %s ) e. CC' % (GT('L'), SR))
    gklc = st([gklcc, w.s([], '0cnd', '( %s -> 0 e. CC )' % A)], 'ifcld', '%s e. CC' % GKL)
    instsn = w.s([hsn], 'sumsn',
                 '( ( L e. _V /\ %s e. CC ) -> sum_ n e. { L } %s = %s )' % (GKL, TN, GKL))
    snval = st([st([lnn], 'elexd', 'L e. _V'), gklc, instsn], 'syl2anc',
               'sum_ n e. { L } %s = %s' % (TN, GKL))
    step4 = st([st([sss], 'eqcomd',
                   'sum_ n e. %s %s = sum_ n e. { L } %s' % (DVP, TN, TN)), snval], 'eqtrd',
               'sum_ n e. %s %s = %s' % (DVP, TN, GKL))
    w.qed([st([st([step1, swap], 'eqtrd',
                  'sum_ d e. %s %s = sum_ n e. %s sum_ d e. %s %s' % (DVP, TD, DVP, DVP, FT)),
               step3], 'eqtrd', 'sum_ d e. %s %s = sum_ n e. %s %s' % (DVP, TD, DVP, TN)),
           step4], 'eqtrd', '( %s -> sum_ d e. %s %s = %s )' % (A, DVP, TD, GKL))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['lwdterm']:
        globals()[f]().run()
