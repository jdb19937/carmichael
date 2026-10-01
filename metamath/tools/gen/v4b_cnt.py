"""Sortie v4b block 5: the primes of the progression survive the sieve.

gcdnprm  ( ( C e. NN /\\ B e. NN /\\ A. q e. Prime ( q || C -> -. q || B ) ) ->
             ( C gcd B ) = 1 )
progcnt  ( PH -> ( # ` TT ) <_ ( SF + Z ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import A, P, PH, V, WF, SF, TT, T, mkst
from cl import lift

GA = '( C e. NN /\\ B e. NN /\\ A. o e. Prime ( o || C -> -. o || B ) )'
EXV = lambda v: 'E. %s e. Prime ( %s || C /\\ %s || B )' % (v, v, v)
TU = ('{ i e. ( 0 ... N ) | ( ( i e. Prime /\\ ( i mod M ) = ( 1 mod M ) ) /\\ Z < i ) }')
IFG = 'if ( ( %s gcd n ) = 1 , ( %s ` n ) , 0 )' % (P, WF)
IF1 = 'if ( ( %s gcd n ) = 1 , 1 , 0 )' % P
ELTT = lambda v: ('( %s e. %s <-> ( %s e. ( 0 ... N ) /\\ ( %s e. Prime /\\ ( %s mod M ) = ( 1 mod M ) ) ) )'
                  % (v, TT, v, v, v))
ELTU = lambda v: ('( %s e. %s <-> ( %s e. ( 0 ... N ) /\\ ( ( %s e. Prime /\\ ( %s mod M ) = ( 1 mod M ) ) /\\ Z < %s ) ) )'
                  % (v, TU, v, v, v, v))
ELA = lambda v: '( %s e. %s <-> ( %s e. ( 1 ... N ) /\\ ( %s mod M ) = ( 1 mod M ) ) )' % (v, A, v, v)


def _subtt(w, v):
    return w.s([w.s([w.s([], 'eleq1', '( i = %s -> ( i e. Prime <-> %s e. Prime ) )' % (v, v)),
                     w.s([w.s([], 'oveq1', '( i = %s -> ( i mod M ) = ( %s mod M ) )' % (v, v))],
                         'eqeq1d',
                         '( i = %s -> ( ( i mod M ) = ( 1 mod M ) <-> ( %s mod M ) = ( 1 mod M ) ) )' % (v, v))],
                    'anbi12d',
                    '( i = %s -> ( ( i e. Prime /\\ ( i mod M ) = ( 1 mod M ) ) <-> ( %s e. Prime /\\ ( %s mod M ) = ( 1 mod M ) ) ) )'
                    % (v, v, v))], 'elrab', ELTT(v))


def _subtu(w, v):
    inner = w.s([w.s([], 'eleq1', '( i = %s -> ( i e. Prime <-> %s e. Prime ) )' % (v, v)),
                 w.s([w.s([], 'oveq1', '( i = %s -> ( i mod M ) = ( %s mod M ) )' % (v, v))],
                     'eqeq1d',
                     '( i = %s -> ( ( i mod M ) = ( 1 mod M ) <-> ( %s mod M ) = ( 1 mod M ) ) )' % (v, v))],
                'anbi12d',
                '( i = %s -> ( ( i e. Prime /\\ ( i mod M ) = ( 1 mod M ) ) <-> ( %s e. Prime /\\ ( %s mod M ) = ( 1 mod M ) ) ) )'
                % (v, v, v))
    gt = w.s([], 'breq2', '( i = %s -> ( Z < i <-> Z < %s ) )' % (v, v))
    return w.s([w.s([inner, gt], 'anbi12d',
                    '( i = %s -> ( ( ( i e. Prime /\\ ( i mod M ) = ( 1 mod M ) ) /\\ Z < i ) <-> ( ( %s e. Prime /\\ ( %s mod M ) = ( 1 mod M ) ) /\\ Z < %s ) ) )'
                    % (v, v, v, v))], 'elrab', ELTU(v))


def _suba(w, v):
    return w.s([w.s([w.s([], 'oveq1', '( i = %s -> ( i mod M ) = ( %s mod M ) )' % (v, v))],
                    'eqeq1d',
                    '( i = %s -> ( ( i mod M ) = ( 1 mod M ) <-> ( %s mod M ) = ( 1 mod M ) ) )' % (v, v))],
               'elrab', ELA(v))


def gcdnprm():
    w = W('gcdnprm', 'Two positive integers no prime divisor of the first of which divides '
                     'the second are coprime.')
    st = mkst(w, GA)
    cnn = st([], 'simp1', 'C e. NN')
    bnn = st([], 'simp2', 'B e. NN')
    ral = st([], 'simp3', 'A. o e. Prime ( o || C -> -. o || B )')
    AQ = '( %s /\\ q e. Prime )' % GA
    sq = mkst(w, AQ)
    sb = w.s([w.s([], 'breq1', '( o = q -> ( o || C <-> q || C ) )'),
              w.s([w.s([], 'breq1', '( o = q -> ( o || B <-> q || B ) )')], 'notbid',
                  '( o = q -> ( -. o || B <-> -. q || B ) )')], 'imbi12d',
             '( o = q -> ( ( o || C -> -. o || B ) <-> ( q || C -> -. q || B ) ) )')
    rsp = w.s([sb], 'rspcv',
              '( q e. Prime -> ( A. o e. Prime ( o || C -> -. o || B ) -> ( q || C -> -. q || B ) ) )')
    rsp2 = sq([sq([], 'simpr', 'q e. Prime'), rsp], 'syl',
              '( A. o e. Prime ( o || C -> -. o || B ) -> ( q || C -> -. q || B ) )')
    imp = sq([lift(w, ral, AQ), rsp2], 'mpd', '( q || C -> -. q || B )')
    nan = sq([sq([w.s([], 'imnan',
                       '( ( q || C -> -. q || B ) <-> -. ( q || C /\\ q || B ) )')], 'a1i',
                 '( ( q || C -> -. q || B ) <-> -. ( q || C /\\ q || B ) )'), imp], 'mpbid',
             '-. ( q || C /\\ q || B )')
    ra2 = st([nan], 'ralrimiva', 'A. q e. Prime -. ( q || C /\\ q || B )')
    nex = st([st([w.s([], 'ralnex',
                       '( A. q e. Prime -. ( q || C /\\ q || B ) <-> -. %s )' % EXV('q'))],
                 'a1i', '( A. q e. Prime -. ( q || C /\\ q || B ) <-> -. %s )' % EXV('q')),
              ra2], 'mpbid', '-. %s' % EXV('q'))
    cbv = w.s([w.s([w.s([], 'breq1', '( q = p -> ( q || C <-> p || C ) )'),
                    w.s([], 'breq1', '( q = p -> ( q || B <-> p || B ) )')], 'anbi12d',
                   '( q = p -> ( ( q || C /\\ q || B ) <-> ( p || C /\\ p || B ) ) )')],
              'cbvrexvw', '( %s <-> %s )' % (EXV('q'), EXV('p')))
    nexp = st([nex, st([cbv], 'a1i', '( %s <-> %s )' % (EXV('q'), EXV('p')))], 'mtbid',
              '-. %s' % EXV('p'))
    AB = '( C e. NN /\\ B e. NN )'
    ncb = w.s([w.s([], 'simpl', '( %s -> C e. NN )' % AB),
               w.s([], 'simpr', '( %s -> B e. NN )' % AB)], 'prmdvdsncoprmbd',
              '( %s -> ( %s <-> ( C gcd B ) =/= 1 ) )' % (AB, EXV('p')))
    bic = st([cnn, bnn, ncb], 'syl2anc', '( %s <-> ( C gcd B ) =/= 1 )' % EXV('p'))
    w.qed([st([w.s([], 'nne', '( -. ( C gcd B ) =/= 1 <-> ( C gcd B ) = 1 )')], 'a1i',
               '( -. ( C gcd B ) =/= 1 <-> ( C gcd B ) = 1 )'),
           st([nexp, bic], 'mtbid', '-. ( C gcd B ) =/= 1')], 'mpbid',
          '( %s -> ( C gcd B ) = 1 )' % GA)
    return w


def progcnt():
    w = W('progcnt', 'The primes up to N in the progression are at most the sifted sum of '
                     'the progression sieve plus the sifting level.')
    st = mkst(w, PH)
    phs = st([], 'id', PH)
    znn = st([], 'simp2', 'Z e. NN')
    nn0 = st([], 'simp3', 'N e. NN0')
    zre = st([znn], 'nnred', 'Z e. RR')
    zz = st([znn], 'nnzd', 'Z e. ZZ')
    nz = st([nn0], 'nn0zd', 'N e. ZZ')
    fzf = st([], 'fzfid', '( 0 ... N ) e. Fin')
    ttfin = st([fzf, st([w.s([], 'ssrab2', '%s C_ ( 0 ... N )' % TT)], 'a1i',
                        '%s C_ ( 0 ... N )' % TT)], 'ssfid', '%s e. Fin' % TT)
    tufin = st([fzf, st([w.s([], 'ssrab2', '%s C_ ( 0 ... N )' % TU)], 'a1i',
                        '%s C_ ( 0 ... N )' % TU)], 'ssfid', '%s e. Fin' % TU)
    zfin = st([], 'fzfid', '( 1 ... Z ) e. Fin')
    fzf1 = st([], 'fzfid', '( 1 ... N ) e. Fin')
    afin = st([fzf1, st([w.s([], 'ssrab2', '%s C_ ( 1 ... N )' % A)], 'a1i',
                        '%s C_ ( 1 ... N )' % A)], 'ssfid', '%s e. Fin' % A)
    eltt = _subtt(w, 'w')
    eltu = _subtu(w, 'w')
    # ---- TT C_ ( TU u. ( 1 ... Z ) ) -----------------------------------
    AW = '( %s /\\ w e. %s )' % (PH, TT)
    sw = mkst(w, AW)
    pair = sw([sw([], 'simpr', 'w e. %s' % TT), sw([eltt], 'a1i', ELTT('w'))], 'mpbid',
              '( w e. ( 0 ... N ) /\\ ( w e. Prime /\\ ( w mod M ) = ( 1 mod M ) ) )')
    wfz = sw([pair], 'simpld', 'w e. ( 0 ... N )')
    winn = sw([pair], 'simprd', '( w e. Prime /\\ ( w mod M ) = ( 1 mod M ) )')
    wprm = sw([winn], 'simpld', 'w e. Prime')
    wnn = sw([wprm, w.inst('prmnn')], 'syl', 'w e. NN')
    wre = sw([wnn], 'nnred', 'w e. RR')
    AG = '( %s /\\ Z < w )' % AW
    sg = mkst(w, AG)
    gin = sg([lift(w, wfz, AG),
              sg([lift(w, winn, AG), sg([], 'simpr', 'Z < w')], 'jca',
                 '( ( w e. Prime /\\ ( w mod M ) = ( 1 mod M ) ) /\\ Z < w )')], 'jca',
             '( w e. ( 0 ... N ) /\\ ( ( w e. Prime /\\ ( w mod M ) = ( 1 mod M ) ) /\\ Z < w ) )')
    gtu = sg([sg([eltu], 'a1i', ELTU('w')), gin], 'mpbird', 'w e. %s' % TU)
    gun = sg([gtu, w.inst('elun1')], 'syl', 'w e. ( %s u. ( 1 ... Z ) )' % TU)
    AH = '( %s /\\ -. Z < w )' % AW
    sh = mkst(w, AH)
    hle = sh([lift(w, wre, AH), lift(w, zre, AH), w.inst('lenlt')], 'syl2anc',
             '( w <_ Z <-> -. Z < w )')
    hle2 = sh([hle, sh([], 'simpr', '-. Z < w')], 'mpbird', 'w <_ Z')
    hfz = sh([sh([lift(w, zz, AH), w.inst('fznn')], 'syl',
                 '( w e. ( 1 ... Z ) <-> ( w e. NN /\\ w <_ Z ) )'),
              sh([lift(w, wnn, AH), hle2], 'jca', '( w e. NN /\\ w <_ Z )')], 'mpbird',
             'w e. ( 1 ... Z )')
    hun = sh([hfz, w.inst('elun2')], 'syl', 'w e. ( %s u. ( 1 ... Z ) )' % TU)
    both = w.s([gun, hun], 'pm2.61dan', '( %s -> w e. ( %s u. ( 1 ... Z ) ) )' % (AW, TU))
    subs = w.s([w.s([both], 'ex',
                    '( %s -> ( w e. %s -> w e. ( %s u. ( 1 ... Z ) ) ) )' % (PH, TT, TU))],
               'ssrdv', '( %s -> %s C_ ( %s u. ( 1 ... Z ) ) )' % (PH, TT, TU))
    unf = st([w.s([], 'unex', '( %s u. ( 1 ... Z ) ) e. _V' % TU)], 'a1i',
             '( %s u. ( 1 ... Z ) ) e. _V' % TU)
    hss = st([unf, subs, w.inst('hashss')], 'syl2anc',
             '( # ` %s ) <_ ( # ` ( %s u. ( 1 ... Z ) ) )' % (TT, TU))
    hu2 = st([tufin, zfin, w.inst('hashun2')], 'syl2anc',
             '( # ` ( %s u. ( 1 ... Z ) ) ) <_ ( ( # ` %s ) + ( # ` ( 1 ... Z ) ) )' % (TU, TU))
    hfz1 = st([st([znn], 'nnnn0d', 'Z e. NN0'), w.inst('hashfz1')], 'syl',
              '( # ` ( 1 ... Z ) ) = Z')
    hu3 = st([hu2, st([hfz1], 'oveq2d',
                      '( ( # ` %s ) + ( # ` ( 1 ... Z ) ) ) = ( ( # ` %s ) + Z )' % (TU, TU))],
             'breqtrd', '( # ` ( %s u. ( 1 ... Z ) ) ) <_ ( ( # ` %s ) + Z )' % (TU, TU))
    # ---- TU C_ A -------------------------------------------------------
    eltun = _subtu(w, 'n')
    elan = _suba(w, 'n')
    AU = '( %s /\\ n e. %s )' % (PH, TU)
    su = mkst(w, AU)
    LU = lambda x: lift(w, x, AU)
    npair = su([su([], 'simpr', 'n e. %s' % TU), su([eltun], 'a1i', ELTU('n'))], 'mpbid',
               '( n e. ( 0 ... N ) /\\ ( ( n e. Prime /\\ ( n mod M ) = ( 1 mod M ) ) /\\ Z < n ) )')
    nfz0 = su([npair], 'simpld', 'n e. ( 0 ... N )')
    nrest = su([npair], 'simprd',
               '( ( n e. Prime /\\ ( n mod M ) = ( 1 mod M ) ) /\\ Z < n )')
    ninn = su([nrest], 'simpld', '( n e. Prime /\\ ( n mod M ) = ( 1 mod M ) )')
    ngt = su([nrest], 'simprd', 'Z < n')
    nprm = su([ninn], 'simpld', 'n e. Prime')
    nmod = su([ninn], 'simprd', '( n mod M ) = ( 1 mod M )')
    nnn = su([nprm, w.inst('prmnn')], 'syl', 'n e. NN')
    nre = su([nnn], 'nnred', 'n e. RR')
    nfzN = su([su([nfz0, w.s([], 'elfz2nn0',
                             '( n e. ( 0 ... N ) <-> ( n e. NN0 /\\ N e. NN0 /\\ n <_ N ) )')],
                  'sylib', '( n e. NN0 /\\ N e. NN0 /\\ n <_ N )')], 'simp3d', 'n <_ N')
    nin1 = su([su([LU(nz), w.inst('fznn')], 'syl',
                  '( n e. ( 1 ... N ) <-> ( n e. NN /\\ n <_ N ) )'),
               su([nnn, nfzN], 'jca', '( n e. NN /\\ n <_ N )')], 'mpbird', 'n e. ( 1 ... N )')
    nina = su([su([elan], 'a1i', ELA('n')),
               su([nin1, nmod], 'jca',
                  '( n e. ( 1 ... N ) /\\ ( n mod M ) = ( 1 mod M ) )')], 'mpbird',
              'n e. %s' % A)
    tuss = w.s([w.s([nina], 'ex', '( %s -> ( n e. %s -> n e. %s ) )' % (PH, TU, A))],
               'ssrdv', '( %s -> %s C_ %s )' % (PH, TU, A))
    # ---- the gcd on TU --------------------------------------------------
    AO = '( %s /\\ o e. Prime )' % AU
    so = mkst(w, AO)
    AO2 = '( %s /\\ o || %s )' % (AO, P)
    s2 = mkst(w, AO2)
    L2 = lambda x: lift(w, x, AO2)
    oprm = so([], 'simpr', 'o e. Prime')
    pel = s2([L2(phs), L2(oprm), w.inst('progpel')], 'syl2anc',
             '( o || %s <-> ( o <_ Z /\\ -. o || M ) )' % P)
    ole = s2([s2([pel, s2([], 'simpr', 'o || %s' % P)], 'mpbid',
                 '( o <_ Z /\\ -. o || M )')], 'simpld', 'o <_ Z')
    ore = s2([s2([L2(oprm), w.inst('prmnn')], 'syl', 'o e. NN')], 'nnred', 'o e. RR')
    olt = s2([ore, L2(zre), L2(nre), ole, L2(ngt)], 'lelttrd', 'o < n')
    oneq = s2([s2([ore, olt], 'ltned', 'o =/= n')], 'neneqd', '-. o = n')
    dvp = s2([s2([s2([L2(oprm), w.inst('prmuz2')], 'syl', 'o e. ( ZZ>= ` 2 )'),
                  L2(nprm)], 'jca', '( o e. ( ZZ>= ` 2 ) /\\ n e. Prime )'),
              w.inst('dvdsprm')], 'syl', '( o || n <-> o = n )')
    ndvd = s2([oneq, dvp], 'mtbird', '-. o || n')
    oral = su([so([ndvd], 'ex', '( o || %s -> -. o || n )' % P)], 'ralrimiva',
              'A. o e. Prime ( o || %s -> -. o || n )' % P)
    pn = st([], 'progpnn',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s )'
            % (P, P, P, T))
    pnn = st([st([pn], 'simpld', '( %s e. NN /\\ ( mmu ` %s ) =/= 0 )' % (P, P))], 'simpld',
             '%s e. NN' % P)
    gcdn = su([su([LU(pnn), nnn, oral], '3jca',
                  '( %s e. NN /\\ n e. NN /\\ A. o e. Prime ( o || %s -> -. o || n ) )'
                  % (P, P)), w.inst('gcdnprm')], 'syl', '( %s gcd n ) = 1' % P)
    # ---- the summand ----------------------------------------------------
    wv0 = w.s([w.s([], 'eqidd', '( c = n -> 1 = 1 )'),
               w.s([], 'eqid', '%s = %s' % (WF, WF))], 'fvmptg',
              '( ( n e. NN /\\ 1 e. _V ) -> ( %s ` n ) = 1 )' % WF)
    uwv = su([nnn, su([w.s([], '1ex', '1 e. _V')], 'a1i', '1 e. _V'), wv0], 'syl2anc',
             '( %s ` n ) = 1' % WF)
    uif = su([su([gcdn], 'iftrued', '%s = ( %s ` n )' % (IFG, WF)), uwv], 'eqtrd',
             '%s = 1' % IFG)
    stu = st([st([uif], 'sumeq2dv', 'sum_ n e. %s %s = sum_ n e. %s 1' % (TU, IFG, TU)),
              st([tufin, st([], '1cnd', '1 e. CC'), w.inst('fsumconst')], 'syl2anc',
                 'sum_ n e. %s 1 = ( ( # ` %s ) x. 1 )' % (TU, TU))], 'eqtrd',
             'sum_ n e. %s %s = ( ( # ` %s ) x. 1 )' % (TU, IFG, TU))
    hcl0 = st([tufin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TU)
    stu2 = st([stu, st([st([hcl0], 'nn0cnd', '( # ` %s ) e. CC' % TU)], 'mulridd',
                       '( ( # ` %s ) x. 1 ) = ( # ` %s )' % (TU, TU))], 'eqtrd',
              'sum_ n e. %s %s = ( # ` %s )' % (TU, IFG, TU))
    # the body on the support
    AA = '( %s /\\ n e. %s )' % (PH, A)
    sa = mkst(w, AA)
    anel = sa([], 'simpr', 'n e. %s' % A)
    anfz = sa([anel, w.inst('elrabi')], 'syl', 'n e. ( 1 ... N )')
    annn = sa([sa([w.s([], 'fz1ssnn', '( 1 ... N ) C_ NN')], 'a1i', '( 1 ... N ) C_ NN'),
               anfz], 'sseldd', 'n e. NN')
    awv = sa([annn, sa([w.s([], '1ex', '1 e. _V')], 'a1i', '1 e. _V'), wv0], 'syl2anc',
             '( %s ` n ) = 1' % WF)
    abody = sa([awv], 'ifeq1d', '%s = %s' % (IFG, IF1))
    are = sa([sa([awv, sa([], '1red', '1 e. RR')], 'eqeltrd', '( %s ` n ) e. RR' % WF),
              sa([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFG)
    AT2 = '( %s /\\ ( %s gcd n ) = 1 )' % (AA, P)
    sT2 = mkst(w, AT2)
    at1 = sT2([sT2([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'),
               sT2([sT2([], 'simpr', '( %s gcd n ) = 1' % P)], 'iftrued', '%s = 1' % IF1)],
              'breqtrrd', '0 <_ %s' % IF1)
    AF2 = '( %s /\\ -. ( %s gcd n ) = 1 )' % (AA, P)
    sF2 = mkst(w, AF2)
    af1 = sF2([sF2([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0'),
               sF2([sF2([], 'simpr', '-. ( %s gcd n ) = 1' % P)], 'iffalsed', '%s = 0' % IF1)],
              'breqtrrd', '0 <_ %s' % IF1)
    age1 = w.s([at1, af1], 'pm2.61dan', '( %s -> 0 <_ %s )' % (AA, IF1))
    age = sa([age1, abody], 'breqtrrd', '0 <_ %s' % IFG)
    less = st([afin, are, age, tuss], 'fsumless',
              'sum_ n e. %s %s <_ %s' % (TU, IFG, SF))
    hle3 = st([stu2, less], 'eqbrtrrd', '( # ` %s ) <_ %s' % (TU, SF))
    # ---- assembly --------------------------------------------------------
    sfre = st([afin, are], 'fsumrecl', '%s e. RR' % SF)
    hture = st([st([tufin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TU)], 'nn0red',
               '( # ` %s ) e. RR' % TU)
    httre = st([st([ttfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % TT)], 'nn0red',
               '( # ` %s ) e. RR' % TT)
    hunre = st([st([st([tufin, zfin, w.inst('unfi')], 'syl2anc',
                       '( %s u. ( 1 ... Z ) ) e. Fin' % TU), w.inst('hashcl')], 'syl',
                   '( # ` ( %s u. ( 1 ... Z ) ) ) e. NN0' % TU)], 'nn0red',
               '( # ` ( %s u. ( 1 ... Z ) ) ) e. RR' % TU)
    addre = st([hture, zre], 'readdcld', '( ( # ` %s ) + Z ) e. RR' % TU)
    sfzre = st([sfre, zre], 'readdcld', '( %s + Z ) e. RR' % SF)
    add = st([hture, sfre, zre, hle3], 'leadd1dd',
             '( ( # ` %s ) + Z ) <_ ( %s + Z )' % (TU, SF))
    t1 = st([httre, hunre, addre, hss, hu3], 'letrd',
            '( # ` %s ) <_ ( ( # ` %s ) + Z )' % (TT, TU))
    w.qed([httre, addre, sfzre, t1, add], 'letrd',
          '( %s -> ( # ` %s ) <_ ( %s + Z ) )' % (PH, TT, SF))
    return w


def main(names=None):
    fns = {'gcdnprm': gcdnprm, 'progcnt': progcnt}
    ok = True
    for nm in (names or ['gcdnprm', 'progcnt']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
