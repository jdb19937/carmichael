"""Sortie v2c: the error term of the Selberg sieve.

mpabs   | MP ( N ) | <_ 3 ^ omega ( N )
selberr the error sum is bounded by the truncated 3 ^ omega sum
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from v2c_lib import *
from cl import lift, Closure
from lin import nlinarith

DVP = DV('P')


def mpabs():
    w = W('mpabs', 'The Selberg Lambda squared coefficients are bounded by three to the number '
                   'of prime divisors.')
    A = '( %s /\\ ( N e. NN /\\ N || P ) )' % SH
    DVN = DV('N')
    IFT = 'if ( N = ( u lcm e ) , ( %s x. %s ) , 0 )' % (LW('u'), LW('e'))
    INU = 'sum_ e e. %s %s' % (DVN, IFT)
    ONE = 'if ( N = ( u lcm e ) , 1 , 0 )'
    d = shsteps(w, A, (SH,))
    st = d['st']
    nnn = st([], 'simprl', 'N e. NN')
    ndp = st([], 'simprr', 'N || P')
    finN = st([nnn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVN)
    # ---- facts for u e. DV ( N )
    AU = '( %s /\\ u e. %s )' % (A, DVN)
    su = mkst(w, AU)
    elu = w.s([w.s([], 'breq1', '( x = u -> ( x || N <-> u || N ) )')], 'elrab',
              '( u e. %s <-> ( u e. NN /\\ u || N ) )' % DVN)
    unn = su([su([su([elu], 'a1i', '( u e. %s <-> ( u e. NN /\\ u || N ) )' % DVN),
                  su([], 'simpr', 'u e. %s' % DVN)], 'mpbid', '( u e. NN /\\ u || N )')],
             'simpld', 'u e. NN')
    lwu = su([lift(w, d['sh'], AU), unn, w.inst('lwre')], 'syl2anc', '%s e. RR' % LW('u'))
    absu = su([su([lwu], 'recnd', '%s e. CC' % LW('u'))], 'abscld',
              '( abs ` %s ) e. RR' % LW('u'))
    absu0 = su([su([lwu], 'recnd', '%s e. CC' % LW('u'))], 'absge0d',
               '0 <_ ( abs ` %s )' % LW('u'))
    absu1 = su([lift(w, d['sh'], AU), unn, w.inst('lwabs')], 'syl2anc',
               '( abs ` %s ) <_ 1' % LW('u'))
    # ---- facts for ( u , e )
    AUE = '( %s /\\ e e. %s )' % (AU, DVN)
    se = mkst(w, AUE)
    ele = w.s([w.s([], 'breq1', '( x = e -> ( x || N <-> e || N ) )')], 'elrab',
              '( e e. %s <-> ( e e. NN /\\ e || N ) )' % DVN)
    enn = se([se([se([ele], 'a1i', '( e e. %s <-> ( e e. NN /\\ e || N ) )' % DVN),
                  se([], 'simpr', 'e e. %s' % DVN)], 'mpbid', '( e e. NN /\\ e || N )')],
             'simpld', 'e e. NN')
    lwe = se([lift(w, d['sh'], AUE), enn, w.inst('lwre')], 'syl2anc', '%s e. RR' % LW('e'))
    abse = se([se([lwe], 'recnd', '%s e. CC' % LW('e'))], 'abscld',
              '( abs ` %s ) e. RR' % LW('e'))
    abse0 = se([se([lwe], 'recnd', '%s e. CC' % LW('e'))], 'absge0d',
               '0 <_ ( abs ` %s )' % LW('e'))
    abse1 = se([lift(w, d['sh'], AUE), enn, w.inst('lwabs')], 'syl2anc',
               '( abs ` %s ) <_ 1' % LW('e'))
    prc = se([se([lift(w, lwu, AUE)], 'recnd', '%s e. CC' % LW('u')),
              se([lwe], 'recnd', '%s e. CC' % LW('e'))], 'mulcld',
             '( %s x. %s ) e. CC' % (LW('u'), LW('e')))
    ifc = se([prc, w.s([], '0cnd', '( %s -> 0 e. CC )' % AUE)], 'ifcld', '%s e. CC' % IFT)
    inuc = su([lift(w, finN, AU), ifc], 'fsumcl', '%s e. CC' % INU)
    # ---- the termwise bound
    AB = '( abs ` %s )' % LW('u')
    BB = '( abs ` %s )' % LW('e')
    cl = Closure(w, AUE, {AB: ('RR', lift(w, absu, AUE)), BB: ('RR', abse)})
    prod1 = nlinarith(w, AUE, [lift(w, absu1, AUE), abse1, lift(w, absu0, AUE), abse0],
                      '( %s x. %s ) <_ 1' % (AB, BB), closure=cl)
    amul = se([se([lift(w, lwu, AUE)], 'recnd', '%s e. CC' % LW('u')),
               se([lwe], 'recnd', '%s e. CC' % LW('e'))], 'absmuld',
              '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (LW('u'), LW('e'), AB, BB))
    absif = se([w.s([], 'ifabs',
                    '( abs ` %s ) = if ( N = ( u lcm e ) , ( abs ` ( %s x. %s ) ) , 0 )'
                    % (IFT, LW('u'), LW('e')))], 'a1i',
               '( abs ` %s ) = if ( N = ( u lcm e ) , ( abs ` ( %s x. %s ) ) , 0 )'
               % (IFT, LW('u'), LW('e')))
    IFA = 'if ( N = ( u lcm e ) , ( abs ` ( %s x. %s ) ) , 0 )' % (LW('u'), LW('e'))
    AUET = '( %s /\\ N = ( u lcm e ) )' % AUE
    sut = mkst(w, AUET)
    c1 = sut([sut([sut([], 'iftrued', '%s = ( abs ` ( %s x. %s ) )' % (IFA, LW('u'), LW('e'))),
                   lift(w, amul, AUET)], 'eqtrd', '%s = ( %s x. %s )' % (IFA, AB, BB)),
              sut([lift(w, prod1, AUET),
                   sut([sut([], 'iftrued', '%s = 1' % ONE)], 'eqcomd', '1 = %s' % ONE)],
                  'breqtrd', '( %s x. %s ) <_ %s' % (AB, BB, ONE))], 'eqbrtrd',
             '%s <_ %s' % (IFA, ONE))
    AUEF = '( %s /\\ -. N = ( u lcm e ) )' % AUE
    suf = mkst(w, AUEF)
    c2 = suf([suf([], 'iffalsed', '%s = 0' % IFA),
              suf([w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % AUEF),
                   suf([suf([], 'iffalsed', '%s = 0' % ONE)], 'eqcomd', '0 = %s' % ONE)],
                  'breqtrd', '0 <_ %s' % ONE)], 'eqbrtrd', '%s <_ %s' % (IFA, ONE))
    cmp = se([absif, se([c1, c2], 'pm2.61dan', '%s <_ %s' % (IFA, ONE))], 'eqbrtrd',
             '( abs ` %s ) <_ %s' % (IFT, ONE))
    # ---- the sums
    absifr = se([se([ifc], 'abscld', '( abs ` %s ) e. RR' % IFT)], 'id',
                '( abs ` %s ) e. RR' % IFT) if False else se([ifc], 'abscld',
                                                             '( abs ` %s ) e. RR' % IFT)
    oner = se([w.s([], '1red', '( %s -> 1 e. RR )' % AUE),
               w.s([], '0red', '( %s -> 0 e. RR )' % AUE)], 'ifcld', '%s e. RR' % ONE)
    s4 = su([lift(w, finN, AU), absifr, oner, cmp], 'fsumle',
            'sum_ e e. %s ( abs ` %s ) <_ sum_ e e. %s %s' % (DVN, IFT, DVN, ONE))
    s2 = su([lift(w, finN, AU), ifc], 'fsumabs',
            '( abs ` %s ) <_ sum_ e e. %s ( abs ` %s )' % (INU, DVN, IFT))
    absinu = su([inuc], 'abscld', '( abs ` %s ) e. RR' % INU)
    sumabsr = su([lift(w, finN, AU), absifr], 'fsumrecl',
                 'sum_ e e. %s ( abs ` %s ) e. RR' % (DVN, IFT))
    sumoner = su([lift(w, finN, AU), oner], 'fsumrecl', 'sum_ e e. %s %s e. RR' % (DVN, ONE))
    s5 = su([absinu, sumabsr, sumoner, s2, s4], 'letrd',
            '( abs ` %s ) <_ sum_ e e. %s %s' % (INU, DVN, ONE))
    s6 = st([finN, absinu, sumoner, s5], 'fsumle',
            'sum_ u e. %s ( abs ` %s ) <_ sum_ u e. %s sum_ e e. %s %s'
            % (DVN, INU, DVN, DVN, ONE))
    s1 = st([finN, inuc], 'fsumabs',
            '( abs ` sum_ u e. %s %s ) <_ sum_ u e. %s ( abs ` %s )' % (DVN, INU, DVN, INU))
    mpr = st([finN, su([lift(w, finN, AU), se([ifc], 'id', '%s e. CC' % IFT) if False else ifc],
                       'fsumrecl', '%s e. RR' % INU) if False else
              su([lift(w, finN, AU), se([lift(w, lwu, AUE), lwe], 'remulcld',
                                        '( %s x. %s ) e. RR' % (LW('u'), LW('e'))) and
                  se([se([lift(w, lwu, AUE), lwe], 'remulcld',
                         '( %s x. %s ) e. RR' % (LW('u'), LW('e'))),
                      w.s([], '0red', '( %s -> 0 e. RR )' % AUE)], 'ifcld',
                     '%s e. RR' % IFT)], 'fsumrecl', '%s e. RR' % INU)], 'fsumrecl',
             'sum_ u e. %s %s e. RR' % (DVN, INU))
    absmp = st([st([finN, inuc], 'fsumcl', 'sum_ u e. %s %s e. CC' % (DVN, INU))], 'abscld',
               '( abs ` sum_ u e. %s %s ) e. RR' % (DVN, INU))
    sumabsinu = st([finN, absinu], 'fsumrecl', 'sum_ u e. %s ( abs ` %s ) e. RR' % (DVN, INU))
    dblr = st([finN, sumoner], 'fsumrecl',
              'sum_ u e. %s sum_ e e. %s %s e. RR' % (DVN, DVN, ONE))
    tot = st([absmp, sumabsinu, dblr, s1, s6], 'letrd',
             '( abs ` sum_ u e. %s %s ) <_ sum_ u e. %s sum_ e e. %s %s'
             % (DVN, INU, DVN, DVN, ONE))
    nsqf = st([st([st([d['pnn'], nnn, ndp], '3jca', '( P e. NN /\\ N e. NN /\\ N || P )'),
                   w.inst('dvdssqf')], 'syl', '( ( mmu ` P ) =/= 0 -> ( mmu ` N ) =/= 0 )'),
               d['psqf']], 'mpd', '( mmu ` N ) =/= 0')
    cnt = st([st([nnn, nsqf], 'jca', '( N e. NN /\\ ( mmu ` N ) =/= 0 )'), w.inst('lcmcnt')],
             'syl', 'sum_ u e. %s sum_ e e. %s %s = ( 3 ^ %s )' % (DVN, DVN, ONE, OM('N')))
    w.qed([tot, cnt], 'breqtrd',
          '( %s -> ( abs ` sum_ u e. %s %s ) <_ ( 3 ^ %s ) )' % (A, DVN, INU, OM('N')))
    return w



def selberr():
    w = W('selberr', 'The error term of the Selberg sieve.')
    d = shsteps(w, SH, ())
    st = d['st']
    finP = st([d['pnn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DVP)
    AD = '( %s /\\ d e. %s )' % (SH, DVP)
    dd = dvpel(w, AD, 'd', d['pnn'])
    sd = dd['st']
    MPD = MP('d', d='u', e='e')
    IFT = 'if ( d = ( u lcm e ) , ( %s x. %s ) , 0 )' % (LW('u'), LW('e'))
    INU = 'sum_ e e. %s %s' % (DV('d'), IFT)
    finD = sd([dd['nn'], w.inst('dvdsfi')], 'syl', '%s e. Fin' % DV('d'))
    # ---- MP ( d ) is real
    ADU = '( %s /\\ u e. %s )' % (AD, DV('d'))
    su = mkst(w, ADU)
    elu = w.s([w.s([], 'breq1', '( x = u -> ( x || d <-> u || d ) )')], 'elrab',
              '( u e. %s <-> ( u e. NN /\\ u || d ) )' % DV('d'))
    unn = su([su([su([elu], 'a1i', '( u e. %s <-> ( u e. NN /\\ u || d ) )' % DV('d')),
                  su([], 'simpr', 'u e. %s' % DV('d'))], 'mpbid',
                 '( u e. NN /\\ u || d )')], 'simpld', 'u e. NN')
    ADUE = '( %s /\\ e e. %s )' % (ADU, DV('d'))
    se = mkst(w, ADUE)
    ele = w.s([w.s([], 'breq1', '( x = e -> ( x || d <-> e || d ) )')], 'elrab',
              '( e e. %s <-> ( e e. NN /\\ e || d ) )' % DV('d'))
    enn = se([se([se([ele], 'a1i', '( e e. %s <-> ( e e. NN /\\ e || d ) )' % DV('d')),
                  se([], 'simpr', 'e e. %s' % DV('d'))], 'mpbid',
                 '( e e. NN /\\ e || d )')], 'simpld', 'e e. NN')
    lwu = se([lift(w, d['sh'], ADUE), lift(w, unn, ADUE), w.inst('lwre')], 'syl2anc',
             '%s e. RR' % LW('u'))
    lwe = se([lift(w, d['sh'], ADUE), enn, w.inst('lwre')], 'syl2anc', '%s e. RR' % LW('e'))
    iftr = se([se([lwu, lwe], 'remulcld', '( %s x. %s ) e. RR' % (LW('u'), LW('e'))),
               w.s([], '0red', '( %s -> 0 e. RR )' % ADUE)], 'ifcld', '%s e. RR' % IFT)
    inur = su([lift(w, finD, ADU), iftr], 'fsumrecl', '%s e. RR' % INU)
    mpr = sd([finD, inur], 'fsumrecl', '%s e. RR' % MPD)
    absmp = sd([sd([mpr], 'recnd', '%s e. CC' % MPD)], 'abscld', '( abs ` %s ) e. RR' % MPD)
    # ---- RM ( d ) is real
    MSD = MS('d')
    RMD = RM('d')
    ADN = '( %s /\\ n e. A )' % AD
    sn = mkst(w, ADN)
    nnnn = w.s([lift(w, d['assnn'], AD)], 'sselda', '( %s -> n e. NN )' % ADN)
    wnr = sn([lift(w, d['wf'], ADN), nnnn, w.inst('ffvelcdm')], 'syl2anc', '( W ` n ) e. RR')
    ifwr = sn([wnr, w.s([], '0red', '( %s -> 0 e. RR )' % ADN)], 'ifcld',
              'if ( d || n , ( W ` n ) , 0 ) e. RR')
    msr = sd([lift(w, d['afin'], AD), ifwr], 'fsumrecl', '%s e. RR' % MSD)
    vdr = sd([lift(w, d['vf'], AD), dd['nn'], w.inst('ffvelcdm')], 'syl2anc', '( V ` d ) e. RR')
    rmr = sd([msr, sd([vdr, lift(w, d['xr'], AD)], 'remulcld', '( ( V ` d ) x. X ) e. RR')],
             'resubcld', '%s e. RR' % RMD)
    absrm = sd([sd([rmr], 'recnd', '%s e. CC' % RMD)], 'abscld', '( abs ` %s ) e. RR' % RMD)
    absrm0 = sd([sd([rmr], 'recnd', '%s e. CC' % RMD)], 'absge0d', '0 <_ ( abs ` %s )' % RMD)
    # ---- 3 ^ omega ( d ) is real
    finpf = sd([sd([w.s([], 'cbvrabv', '%s = %s' % (PF('d', 'p'), PF('d')))], 'a1i',
                   '%s = %s' % (PF('d', 'p'), PF('d'))),
               sd([dd['nn'], w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PF('d', 'p'))],
              'eqeltrrd', '%s e. Fin' % PF('d'))
    om0 = sd([finpf, w.inst('hashcl')], 'syl', '%s e. NN0' % OM('d'))
    thr = sd([w.s([w.s([], '3re', '3 e. RR')], 'a1i', '( %s -> 3 e. RR )' % AD), om0],
             'reexpcld', '( 3 ^ %s ) e. RR' % OM('d'))
    LT = '( ( abs ` %s ) x. ( abs ` %s ) )' % (MPD, RMD)
    RT = 'if ( d <_ Y , ( ( 3 ^ %s ) x. ( abs ` %s ) ) , 0 )' % (OM('d'), RMD)
    rtr = sd([sd([thr, absrm], 'remulcld', '( ( 3 ^ %s ) x. ( abs ` %s ) ) e. RR'
                 % (OM('d'), RMD)), w.s([], '0red', '( %s -> 0 e. RR )' % AD)], 'ifcld',
             '%s e. RR' % RT)
    # ---- case d <_ Y
    ADY = '( %s /\\ d <_ Y )' % AD
    sy = mkst(w, ADY)
    mab = sy([sy([lift(w, d['sh'], ADY),
                  sy([lift(w, dd['nn'], ADY), lift(w, dd['dP'], ADY)], 'jca',
                     '( d e. NN /\\ d || P )')], 'jca',
                 '( %s /\\ ( d e. NN /\\ d || P ) )' % SH), w.inst('mpabs')], 'syl',
             '( abs ` %s ) <_ ( 3 ^ %s )' % (MPD, OM('d')))
    le1 = sy([lift(w, absmp, ADY), lift(w, thr, ADY), lift(w, absrm, ADY),
              lift(w, absrm0, ADY), mab], 'lemul1ad',
             '%s <_ ( ( 3 ^ %s ) x. ( abs ` %s ) )' % (LT, OM('d'), RMD))
    case1 = sy([le1, sy([sy([], 'simpr', 'd <_ Y')], 'iftrued',
                        '%s = ( ( 3 ^ %s ) x. ( abs ` %s ) )' % (RT, OM('d'), RMD))],
               'breqtrrd', '%s <_ %s' % (LT, RT))
    # ---- case -. d <_ Y
    ADF = '( %s /\\ -. d <_ Y )' % AD
    sf = mkst(w, ADF)
    mz = sf([sf([lift(w, d['sh'], ADF), lift(w, dd['nn'], ADF),
                 sf([], 'simpr', '-. d <_ Y')], '3jca',
                '( %s /\\ d e. NN /\\ -. d <_ Y )' % SH), w.inst('mp0')], 'syl',
            '%s = 0' % MPD)
    az = sf([sf([mz], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % MPD),
             sf([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd',
            '( abs ` %s ) = 0' % MPD)
    ltz = sf([sf([az], 'oveq1d', '%s = ( 0 x. ( abs ` %s ) )' % (LT, RMD)),
              sf([lift(w, absrm, ADF)], 'recnd', '( abs ` %s ) e. CC' % RMD) and
              sf([sf([lift(w, absrm, ADF)], 'recnd', '( abs ` %s ) e. CC' % RMD)], 'mul02d',
                 '( 0 x. ( abs ` %s ) ) = 0' % RMD)], 'eqtrd', '%s = 0' % LT)
    case2 = sf([ltz, sf([w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % ADF),
                        sf([sf([sf([], 'simpr', '-. d <_ Y')], 'iffalsed', '%s = 0' % RT)],
                           'eqcomd', '0 = %s' % RT)], 'breqtrd', '0 <_ %s' % RT)], 'eqbrtrd',
               '%s <_ %s' % (LT, RT))
    cmp = sd([case1, case2], 'pm2.61dan', '%s <_ %s' % (LT, RT))
    ltr = sd([absmp, absrm], 'remulcld', '%s e. RR' % LT)
    w.qed([finP, ltr, rtr, cmp], 'fsumle',
          '( %s -> sum_ d e. %s %s <_ sum_ d e. %s %s )' % (SH, DVP, LT, DVP, RT))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['mpabs']:
        globals()[f]().run()
