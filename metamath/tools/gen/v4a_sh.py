"""Sortie v4a: the twin sieve as an instance of the Selberg hypothesis bundle."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import QF, mkst
from cl import lift
from v4a_v import VV, PFG, PFQ, PFP
from lin import linarith

TPS = '{ u e. ( 0 ... Z ) | ( u e. Prime /\\ -. u || ( 2 x. M ) ) }'
PP = 'prod_ p e. %s p' % TPS
FMAP = '( i e. ( 1 ... T ) |-> %s )' % QF('i')
AAS = 'ran %s' % FMAP
WWS = '( c e. NN |-> 1 )'


def tpsel(w, el):
    """closed step: ( el e. TPS <-> ( el e. ( 0 ... Z ) /\\ ( el e. Prime /\\ -. el || ( 2 x. M ) ) ) )"""
    a = w.s([], 'eleq1', '( u = %s -> ( u e. Prime <-> %s e. Prime ) )' % (el, el))
    b = w.s([w.s([], 'breq1',
                 '( u = %s -> ( u || ( 2 x. M ) <-> %s || ( 2 x. M ) ) )' % (el, el))],
            'notbid',
            '( u = %s -> ( -. u || ( 2 x. M ) <-> -. %s || ( 2 x. M ) ) )' % (el, el))
    c = w.s([a, b], 'anbi12d',
            '( u = %s -> ( ( u e. Prime /\\ -. u || ( 2 x. M ) ) <-> '
            '( %s e. Prime /\\ -. %s || ( 2 x. M ) ) ) )' % (el, el, el))
    return w.s([c], 'elrab',
               '( %s e. %s <-> ( %s e. ( 0 ... Z ) /\\ '
               '( %s e. Prime /\\ -. %s || ( 2 x. M ) ) ) )' % (el, TPS, el, el, el))


def twinpp():
    w = WS('twinpp', 'The sifting product of the twin sieve is a squarefree positive integer '
                     'whose prime divisors are the sifting primes.')
    st = mkst(w, 'Z e. NN0')
    fin = st([st([], 'fzfid', '( 0 ... Z ) e. Fin'),
              st([w.s([], 'ssrab2', '%s C_ ( 0 ... Z )' % TPS)], 'a1i',
                 '%s C_ ( 0 ... Z )' % TPS)], 'ssfid', '%s e. Fin' % TPS)
    AV = '( Z e. NN0 /\\ d e. %s )' % TPS
    sv = mkst(w, AV)
    umem = sv([sv([tpsel(w, 'd')], 'a1i',
                  '( d e. %s <-> ( d e. ( 0 ... Z ) /\\ '
                  '( d e. Prime /\\ -. d || ( 2 x. M ) ) ) )' % TPS),
               sv([], 'simpr', 'd e. %s' % TPS)], 'mpbid',
              '( d e. ( 0 ... Z ) /\\ ( d e. Prime /\\ -. d || ( 2 x. M ) ) )')
    uprm = sv([sv([umem], 'simprd', '( d e. Prime /\\ -. d || ( 2 x. M ) )')], 'simpld',
              'd e. Prime')
    tprm = st([st([uprm], 'ex', '( d e. %s -> d e. Prime )' % TPS)], 'ssrdv',
              '%s C_ Prime' % TPS)
    w.qed([st([fin, tprm], 'jca', '( %s e. Fin /\\ %s C_ Prime )' % (TPS, TPS)),
           w.inst('sqfprod')], 'syl',
          '( Z e. NN0 -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s ) )'
          % (PP, PP, PFQ % PP, TPS))
    return w


def twinsupp():
    w = WS('twinsupp', 'The support of the twin sieve is a finite set of positive integers.')
    A = '( M e. NN /\\ T e. NN0 )'
    st = mkst(w, A)
    mnn = st([], 'simpl', 'M e. NN')
    AI = '( %s /\\ i e. ( 1 ... T ) )' % A
    si = mkst(w, AI)
    inn = si([si([], 'simpr', 'i e. ( 1 ... T )'), w.inst('elfznn')], 'syl', 'i e. NN')
    qnn = si([inn, si([si([lift(w, mnn, AI), inn], 'nnmulcld', '( M x. i ) e. NN'),
                       si([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')], 'nnaddcld',
                      '( ( M x. i ) + 1 ) e. NN')], 'nnmulcld', '%s e. NN' % QF('i'))
    ff = st([qnn, w.s([], 'eqid', '%s = %s' % (FMAP, FMAP))], 'fmptd',
            '%s : ( 1 ... T ) --> NN' % FMAP)
    ssn = st([ff], 'frnd', '%s C_ NN' % AAS)
    fin = st([st([st([], 'fzfid', '( 1 ... T ) e. Fin'), w.inst('mptfi')], 'syl',
                 '%s e. Fin' % FMAP), w.inst('rnfi')], 'syl', '%s e. Fin' % AAS)
    w.qed([fin, ssn], 'jca', '( %s -> ( %s e. Fin /\\ %s C_ NN ) )' % (A, AAS, AAS))
    return w


def twinwt():
    w = WS('twinwt', 'The weights of the twin sieve are the constant function 1.')
    AC = 'c e. NN'
    sc = mkst(w, AC)
    onere = sc([], '1red', '1 e. RR')
    ral = w.s([onere], 'rgen', 'A. c e. NN 1 e. RR')
    bic = w.s([w.s([], 'eqid', '%s = %s' % (WWS, WWS))], 'fmpt',
              '( A. c e. NN 1 e. RR <-> %s : NN --> RR )' % WWS)
    fn = w.s([ral, bic], 'mpbi', '%s : NN --> RR' % WWS)
    AK = 'k e. NN'
    sk = mkst(w, AK)
    onec = w.s([], '1ex', '1 e. _V')
    wv = sk([sk([sk([], 'id', 'k e. NN'), sk([onec], 'a1i', '1 e. _V')], 'jca',
                '( k e. NN /\\ 1 e. _V )'),
             sk([w.s([w.s([], 'eqidd', '( c = k -> 1 = 1 )'),
                      w.s([], 'eqid', '%s = %s' % (WWS, WWS))],
                     'fvmptg', '( ( k e. NN /\\ 1 e. _V ) -> ( %s ` k ) = 1 )' % WWS)], 'a1i',
                '( ( k e. NN /\\ 1 e. _V ) -> ( %s ` k ) = 1 )' % WWS)], 'mpd',
            '( %s ` k ) = 1' % WWS)
    ge = sk([sk([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'),
             sk([wv], 'eqcomd', '1 = ( %s ` k )' % WWS)], 'breqtrd', '0 <_ ( %s ` k )' % WWS)
    ralk = w.s([ge], 'rgen', 'A. k e. NN 0 <_ ( %s ` k )' % WWS)
    w.qed([fn, ralk], 'pm3.2i',
          '( %s : NN --> RR /\\ A. k e. NN 0 <_ ( %s ` k ) )' % (WWS, WWS))
    return w


AS = '( M e. NN /\ T e. NN0 /\ Z e. NN )'
SH1I = ('( ( %s e. Fin /\ %s C_ NN /\ %s : NN --> RR ) /\ '
        '( A. k e. NN 0 <_ ( %s ` k ) /\ T e. RR /\ '
        '( ( Z ^ 2 ) e. RR /\ 1 <_ ( Z ^ 2 ) ) ) )' % (AAS, AAS, WWS, WWS))
SHPI = '( %s e. NN /\ ( mmu ` %s ) =/= 0 )' % (PP, PP)
SHVMI = ('A. a e. NN A. b e. NN ( ( a gcd b ) = 1 -> '
         '( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) ) )' % (VV, VV, VV))
SHVPI = 'A. s e. Prime ( s || %s -> ( 0 < ( %s ` s ) /\ ( %s ` s ) < 1 ) )' % (PP, VV, VV)
SHVI = '( %s : NN --> RR /\ ( %s ` 1 ) = 1 /\ ( %s /\ %s ) )' % (VV, VV, SHVMI, SHVPI)
SH2I = '( %s /\ %s )' % (SHPI, SHVI)
SHI = '( %s /\ %s )' % (SH1I, SH2I)
TMRI = '( M e. NN /\ Z e. NN /\ ( Z ^ 2 ) = ( Z ^ 2 ) )'
TBODYI = ('( ( y || %s -> ( ( %s ` y ) = ( 2 / y ) /\ -. y || ( 2 x. M ) ) ) /\ '
          '( ( y <_ Z /\ -. y || ( 2 x. M ) ) -> y || %s ) )' % (PP, VV, PP))
TRALI = 'A. y e. Prime %s' % TBODYI
TBI = '( %s /\ %s /\ %s )' % (SHI, TMRI, TRALI)


def twinsh():
    w = WS('twinsh', 'The twin sieve satisfies the hypothesis bundle of the Selberg sieve '
                     'together with the conditions on the sifting primes.')
    st = mkst(w, AS)
    mnn = st([], 'simp1', 'M e. NN')
    tn0 = st([], 'simp2', 'T e. NN0')
    znn = st([], 'simp3', 'Z e. NN')
    zn0 = st([znn], 'nnnn0d', 'Z e. NN0')
    # SH1
    supp = st([st([mnn, tn0], 'jca', '( M e. NN /\ T e. NN0 )'), w.inst('twinsupp')], 'syl',
              '( %s e. Fin /\ %s C_ NN )' % (AAS, AAS))
    wt = st([w.s([], 'twinwt',
                 '( %s : NN --> RR /\ A. k e. NN 0 <_ ( %s ` k ) )' % (WWS, WWS))], 'a1i',
            '( %s : NN --> RR /\ A. k e. NN 0 <_ ( %s ` k ) )' % (WWS, WWS))
    tre = st([tn0], 'nn0red', 'T e. RR')
    z2nn = st([znn, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'nnexpcld',
              '( Z ^ 2 ) e. NN')
    z2re = st([z2nn], 'nnred', '( Z ^ 2 ) e. RR')
    z2ge = st([z2nn, w.inst('nnge1')], 'syl', '1 <_ ( Z ^ 2 )')
    sh1 = st([st([st([supp], 'simpld', '%s e. Fin' % AAS),
                  st([supp], 'simprd', '%s C_ NN' % AAS),
                  st([wt], 'simpld', '%s : NN --> RR' % WWS)], '3jca',
                 '( %s e. Fin /\ %s C_ NN /\ %s : NN --> RR )' % (AAS, AAS, WWS)),
              st([st([wt], 'simprd', 'A. k e. NN 0 <_ ( %s ` k )' % WWS), tre,
                  st([z2re, z2ge], 'jca',
                     '( ( Z ^ 2 ) e. RR /\ 1 <_ ( Z ^ 2 ) )')], '3jca',
                 '( A. k e. NN 0 <_ ( %s ` k ) /\ T e. RR /\ '
                 '( ( Z ^ 2 ) e. RR /\ 1 <_ ( Z ^ 2 ) ) )' % WWS)], 'jca', SH1I)
    # the sifting product
    pp = st([zn0, w.inst('twinpp')], 'syl', '( %s /\ %s = %s )' % (SHPI, PFQ % PP, TPS))
    shp = st([pp], 'simpld', SHPI)
    pfeq = st([pp], 'simprd', '%s = %s' % (PFQ % PP, TPS))
    # the density
    vf = st([w.s([], 'twinvf', '%s : NN --> RR' % VV)], 'a1i', '%s : NN --> RR' % VV)
    v1 = st([w.s([], 'twinv1', '( %s ` 1 ) = 1' % VV)], 'a1i', '( %s ` 1 ) = 1' % VV)
    # multiplicativity
    AAB = '( ( %s /\ a e. NN ) /\ b e. NN )' % AS
    sab = mkst(w, AAB)
    ann = sab([sab([], 'simpl', '( %s /\ a e. NN )' % AS)], 'simprd', 'a e. NN')
    bnn = sab([], 'simpr', 'b e. NN')
    AABG = '( %s /\ ( a gcd b ) = 1 )' % AAB
    sabg = mkst(w, AABG)
    veq = sabg([sabg([lift(w, ann, AABG), lift(w, bnn, AABG),
                      sabg([], 'simpr', '( a gcd b ) = 1')], '3jca',
                     '( a e. NN /\ b e. NN /\ ( a gcd b ) = 1 )'), w.inst('twinvmul')], 'syl',
               '( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) )' % (VV, VV, VV))
    imp1 = sab([veq], 'ex',
               '( ( a gcd b ) = 1 -> ( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) ) )'
               % (VV, VV, VV))
    ralb = w.s([imp1], 'ralrimiva',
               '( ( %s /\ a e. NN ) -> A. b e. NN ( ( a gcd b ) = 1 -> '
               '( %s ` ( a x. b ) ) = ( ( %s ` a ) x. ( %s ` b ) ) ) )' % (AS, VV, VV, VV))
    shvm = st([ralb], 'ralrimiva', SHVMI)
    # positivity and the strict bound at the sifting primes
    ASP = '( %s /\ s e. Prime )' % AS
    sp = mkst(w, ASP)
    sprm = sp([], 'simpr', 's e. Prime')
    snn = sp([sprm, w.inst('prmnn')], 'syl', 's e. NN')
    sre = sp([snn], 'nnred', 's e. RR')
    srp = sp([snn], 'nnrpd', 's e. RR+')
    ASPD = '( %s /\ s || %s )' % (ASP, PP)
    spd = mkst(w, ASPD)
    elpq = w.s([w.s([], 'breq1', '( q = s -> ( q || %s <-> s || %s ) )' % (PP, PP))], 'elrab',
               '( s e. %s <-> ( s e. Prime /\ s || %s ) )' % (PFQ % PP, PP))
    sinq = spd([spd([lift(w, sprm, ASPD), spd([], 'simpr', 's || %s' % PP)], 'jca',
                    '( s e. Prime /\ s || %s )' % PP),
                spd([elpq], 'a1i',
                    '( s e. %s <-> ( s e. Prime /\ s || %s ) )' % (PFQ % PP, PP))], 'mpbird',
               's e. %s' % (PFQ % PP))
    stps = spd([sinq, lift(w, pfeq, ASPD)], 'eleqtrd', 's e. %s' % TPS)
    smem = spd([spd([tpsel(w, 's')], 'a1i',
                    '( s e. %s <-> ( s e. ( 0 ... Z ) /\ '
                    '( s e. Prime /\ -. s || ( 2 x. M ) ) ) )' % TPS), stps], 'mpbid',
               '( s e. ( 0 ... Z ) /\ ( s e. Prime /\ -. s || ( 2 x. M ) ) )')
    sfz = spd([smem], 'simpld', 's e. ( 0 ... Z )')
    snd = spd([spd([smem], 'simprd', '( s e. Prime /\ -. s || ( 2 x. M ) )')], 'simprd',
              '-. s || ( 2 x. M )')
    # 3 <_ s
    twoz = spd([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    dv2 = spd([twoz, spd([lift(w, mnn, ASPD)], 'nnzd', 'M e. ZZ'), w.inst('dvdsmul1')],
              'syl2anc', '2 || ( 2 x. M )')
    ASPE = '( %s /\ s = 2 )' % ASPD
    spe = mkst(w, ASPE)
    sd2 = spe([spe([], 'simpr', 's = 2'), lift(w, dv2, ASPE)], 'eqbrtrd', 's || ( 2 x. M )')
    sne2 = spd([snd, sd2], 'mtand', '-. s = 2')
    s2le = spd([spd([lift(w, sprm, ASPD), w.inst('prmuz2')], 'syl', 's e. ( ZZ>= ` 2 )'),
                w.inst('eluzle')], 'syl', '2 <_ s')
    tworE = spd([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    s2lt = spd([spd([tworE, lift(w, sre, ASPD), w.inst('ltlen')], 'syl2anc',
                    '( 2 < s <-> ( 2 <_ s /\ s =/= 2 ) )'),
                spd([s2le, spd([sne2], 'neqned', 's =/= 2')], 'jca',
                    '( 2 <_ s /\ s =/= 2 )')], 'mpbird', '2 < s')
    vs = spd([lift(w, sprm, ASPD), w.inst('twinvp')], 'syl', '( %s ` s ) = ( 2 / s )' % VV)
    tsrp = spd([spd([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), lift(w, srp, ASPD)],
               'rpdivcld', '( 2 / s ) e. RR+')
    pos = spd([spd([tsrp], 'rpgt0d', '0 < ( 2 / s )'),
               spd([vs], 'eqcomd', '( 2 / s ) = ( %s ` s )' % VV)], 'breqtrd',
              '0 < ( %s ` s )' % VV)
    lt1 = spd([vs, spd([s2lt, spd([tworE, lift(w, srp, ASPD), w.inst('divlt1lt')], 'syl2anc',
                                  '( ( 2 / s ) < 1 <-> 2 < s )')], 'mpbird',
                       '( 2 / s ) < 1')], 'eqbrtrd', '( %s ` s ) < 1' % VV)
    both = spd([pos, lt1], 'jca', '( 0 < ( %s ` s ) /\ ( %s ` s ) < 1 )' % (VV, VV))
    impv = sp([both], 'ex',
              '( s || %s -> ( 0 < ( %s ` s ) /\ ( %s ` s ) < 1 ) )' % (PP, VV, VV))
    shvp = st([impv], 'ralrimiva', SHVPI)
    shv = st([vf, v1, st([shvm, shvp], 'jca', '( %s /\ %s )' % (SHVMI, SHVPI))], '3jca', SHVI)
    shi = st([sh1, st([shp, shv], 'jca', SH2I)], 'jca', SHI)
    # TMR
    tmr = st([mnn, znn, st([], 'eqidd', '( Z ^ 2 ) = ( Z ^ 2 )')], '3jca', TMRI)
    # TRAL
    AY = '( %s /\ y e. Prime )' % AS
    sy = mkst(w, AY)
    yprm = sy([], 'simpr', 'y e. Prime')
    ynn = sy([yprm, w.inst('prmnn')], 'syl', 'y e. NN')
    AYD = '( %s /\ y || %s )' % (AY, PP)
    syd = mkst(w, AYD)
    elpy = w.s([w.s([], 'breq1', '( q = y -> ( q || %s <-> y || %s ) )' % (PP, PP))], 'elrab',
               '( y e. %s <-> ( y e. Prime /\ y || %s ) )' % (PFQ % PP, PP))
    yinq = syd([syd([lift(w, yprm, AYD), syd([], 'simpr', 'y || %s' % PP)], 'jca',
                    '( y e. Prime /\ y || %s )' % PP),
                syd([elpy], 'a1i',
                    '( y e. %s <-> ( y e. Prime /\ y || %s ) )' % (PFQ % PP, PP))], 'mpbird',
               'y e. %s' % (PFQ % PP))
    ytps = syd([yinq, lift(w, pfeq, AYD)], 'eleqtrd', 'y e. %s' % TPS)
    ymem = syd([syd([tpsel(w, 'y')], 'a1i',
                    '( y e. %s <-> ( y e. ( 0 ... Z ) /\ '
                    '( y e. Prime /\ -. y || ( 2 x. M ) ) ) )' % TPS), ytps], 'mpbid',
               '( y e. ( 0 ... Z ) /\ ( y e. Prime /\ -. y || ( 2 x. M ) ) )')
    ynd = syd([syd([ymem], 'simprd', '( y e. Prime /\ -. y || ( 2 x. M ) )')], 'simprd',
              '-. y || ( 2 x. M )')
    vy = syd([lift(w, yprm, AYD), w.inst('twinvp')], 'syl', '( %s ` y ) = ( 2 / y )' % VV)
    part1 = sy([syd([vy, ynd], 'jca',
                    '( ( %s ` y ) = ( 2 / y ) /\ -. y || ( 2 x. M ) )' % VV)], 'ex',
               '( y || %s -> ( ( %s ` y ) = ( 2 / y ) /\ -. y || ( 2 x. M ) ) )' % (PP, VV))
    AYB = '( %s /\ ( y <_ Z /\ -. y || ( 2 x. M ) ) )' % AY
    syb = mkst(w, AYB)
    ylez = syb([syb([], 'simpr', '( y <_ Z /\ -. y || ( 2 x. M ) )')], 'simpld', 'y <_ Z')
    yndb = syb([syb([], 'simpr', '( y <_ Z /\ -. y || ( 2 x. M ) )')], 'simprd',
               '-. y || ( 2 x. M )')
    yfz = syb([syb([lift(w, zn0, AYB), w.inst('fznn0')], 'syl',
                   '( y e. ( 0 ... Z ) <-> ( y e. NN0 /\ y <_ Z ) )'),
               syb([syb([lift(w, ynn, AYB)], 'nnnn0d', 'y e. NN0'), ylez], 'jca',
                   '( y e. NN0 /\ y <_ Z )')], 'mpbird', 'y e. ( 0 ... Z )')
    ytps2 = syb([syb([yfz, syb([lift(w, yprm, AYB), yndb], 'jca',
                               '( y e. Prime /\ -. y || ( 2 x. M ) )')], 'jca',
                     '( y e. ( 0 ... Z ) /\ ( y e. Prime /\ -. y || ( 2 x. M ) ) )'),
                 syb([tpsel(w, 'y')], 'a1i',
                     '( y e. %s <-> ( y e. ( 0 ... Z ) /\ '
                     '( y e. Prime /\ -. y || ( 2 x. M ) ) ) )' % TPS)], 'mpbird',
                'y e. %s' % TPS)
    yinq2 = syb([ytps2, syb([lift(w, pfeq, AYB)], 'eqcomd', '%s = %s' % (TPS, PFQ % PP))],
                'eleqtrd', 'y e. %s' % (PFQ % PP))
    ydp = syb([syb([syb([elpy], 'a1i',
                        '( y e. %s <-> ( y e. Prime /\ y || %s ) )' % (PFQ % PP, PP)),
                    yinq2], 'mpbid', '( y e. Prime /\ y || %s )' % PP)], 'simprd',
              'y || %s' % PP)
    part2 = sy([ydp], 'ex', '( ( y <_ Z /\ -. y || ( 2 x. M ) ) -> y || %s )' % PP)
    tral = st([sy([part1, part2], 'jca', TBODYI)], 'ralrimiva', TRALI)
    w.qed([shi, tmr, tral], '3jca', '( %s -> %s )' % (AS, TBI))
    return w


ALL = {'twinpp': twinpp, 'twinsupp': twinsupp, 'twinwt': twinwt, 'twinsh': twinsh}



def twinpz():
    w = WS('twinpz', 'Every prime divisor of the sifting product is at most the sifting '
                     'bound.')
    st = mkst(w, 'Z e. NN0')
    pp = st([st([], 'id', 'Z e. NN0'), w.inst('twinpp')], 'syl',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s )'
            % (PP, PP, PFQ % PP, TPS))
    pfeq = st([pp], 'simprd', '%s = %s' % (PFQ % PP, TPS))
    AY = '( Z e. NN0 /\\ y e. Prime )'
    sy = mkst(w, AY)
    yprm = sy([], 'simpr', 'y e. Prime')
    AYD = '( %s /\\ y || %s )' % (AY, PP)
    syd = mkst(w, AYD)
    elpy = w.s([w.s([], 'breq1', '( q = y -> ( q || %s <-> y || %s ) )' % (PP, PP))], 'elrab',
               '( y e. %s <-> ( y e. Prime /\\ y || %s ) )' % (PFQ % PP, PP))
    yinq = syd([syd([lift(w, yprm, AYD), syd([], 'simpr', 'y || %s' % PP)], 'jca',
                    '( y e. Prime /\\ y || %s )' % PP),
                syd([elpy], 'a1i',
                    '( y e. %s <-> ( y e. Prime /\\ y || %s ) )' % (PFQ % PP, PP))], 'mpbird',
               'y e. %s' % (PFQ % PP))
    ytps = syd([yinq, lift(w, pfeq, AYD)], 'eleqtrd', 'y e. %s' % TPS)
    yfz = syd([syd([syd([tpsel(w, 'y')], 'a1i',
                        '( y e. %s <-> ( y e. ( 0 ... Z ) /\\ '
                        '( y e. Prime /\\ -. y || ( 2 x. M ) ) ) )' % TPS), ytps], 'mpbid',
                   '( y e. ( 0 ... Z ) /\\ ( y e. Prime /\\ -. y || ( 2 x. M ) ) )')],
              'simpld', 'y e. ( 0 ... Z )')
    ylez = syd([yfz, w.inst('elfzle2')], 'syl', 'y <_ Z')
    w.qed([sy([ylez], 'ex', '( y || %s -> y <_ Z )' % PP)], 'ralrimiva',
          '( Z e. NN0 -> A. y e. Prime ( y || %s -> y <_ Z ) )' % PP)
    return w


ALL['twinpz'] = twinpz

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
