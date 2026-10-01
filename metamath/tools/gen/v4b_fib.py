"""Sortie v4b block 7b: the fibre bound of the progression sieve.

progfib  ( ( Z e. NN /\\ ( L e. NN /\\ ( mmu ` L ) =/= 0 ) ) ->
            sum_ w e. ( 1 ... Z ) if ( RAD( w ) = L , ( 1 / w ) , 0 ) <_ GTR( L ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import PF, RAD, GTR, mkst
from cl import lift

ANT = '( Z e. NN /\\ ( L e. NN /\\ ( mmu ` L ) =/= 0 ) )'
RD = lambda v: RAD(v)
IFW = 'if ( %s = L , ( 1 / w ) , 0 )' % RD('w')
FB = '{ i e. ( 1 ... Z ) | %s = L }' % RD('i')
QG = '{ g e. Prime | g || L }'
SMR = lambda v: '{ r e. Prime | r || %s }' % v
SM = '{ v e. ( 1 ... Z ) | %s C_ %s }' % (SMR('v'), QG)
FMAP = '( a e. %s |-> ( a / L ) )' % FB
PRODG = 'prod_ p e. %s ( 1 / ( 1 - ( 1 / p ) ) )' % QG
PRODQ = 'prod_ q e. %s ( 1 / ( 1 - ( 1 / q ) ) )' % PF('L')
ELFB = lambda v: '( %s e. %s <-> ( %s e. ( 1 ... Z ) /\\ %s = L ) )' % (v, FB, v, RD(v))


def radsub(w, v1, v2):
    b1 = w.s([], 'breq2', '( %s = %s -> ( u || %s <-> u || %s ) )' % (v1, v2, v1, v2))
    b2 = w.s([b1], 'rabbidv', '( %s = %s -> %s = %s )'
             % (v1, v2, PF(v1, 'u'), PF(v2, 'u')))
    return w.s([b2], 'prodeq1d', '( %s = %s -> %s = %s )' % (v1, v2, RD(v1), RD(v2)))


def elfb(w, v):
    return w.s([w.s([radsub(w, 'i', v)], 'eqeq1d',
                    '( i = %s -> ( %s = L <-> %s = L ) )' % (v, RD('i'), RD(v)))],
               'elrab', ELFB(v))


def progfib():
    w = W('progfib', 'The fibre of the radical over a squarefree L contributes at most the '
                     'Selberg term of the progression sieve.')
    st = mkst(w, ANT)
    znn = st([], 'simpl', 'Z e. NN')
    zz = st([znn], 'nnzd', 'Z e. ZZ')
    lsq = st([], 'simpr', '( L e. NN /\\ ( mmu ` L ) =/= 0 )')
    lnn = st([lsq], 'simpld', 'L e. NN')
    lre = st([lnn], 'nnred', 'L e. RR')
    lcc = st([lnn], 'nncnd', 'L e. CC')
    lne = st([lnn], 'nnne0d', 'L =/= 0')
    lrp = st([lnn, w.inst('nnrp')], 'syl', 'L e. RR+')
    lrec = st([lrp], 'rpreccld', '( 1 / L ) e. RR+')
    lrecre = st([lrec], 'rpred', '( 1 / L ) e. RR')
    lrec0 = st([lrec, w.inst('rpgt0')], 'syl', '0 < ( 1 / L )')
    fzf = st([], 'fzfid', '( 1 ... Z ) e. Fin')
    fbfin = st([fzf, st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % FB)], 'a1i',
                        '%s C_ ( 1 ... Z )' % FB)], 'ssfid', '%s e. Fin' % FB)
    smfin = st([fzf, st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % SM)], 'a1i',
                        '%s C_ ( 1 ... Z )' % SM)], 'ssfid', '%s e. Fin' % SM)
    elfa = elfb(w, 'a')
    elfw = elfb(w, 'w')
    elfn = elfb(w, 'n')
    elfo = elfb(w, 'o')
    # ---- the fibre element a --------------------------------------------
    AA = '( %s /\\ a e. %s )' % (ANT, FB)
    sa = mkst(w, AA)
    LA = lambda s: lift(w, s, AA)
    apair = sa([sa([], 'simpr', 'a e. %s' % FB), sa([elfa], 'a1i', ELFB('a'))], 'mpbid',
               '( a e. ( 1 ... Z ) /\\ %s = L )' % RD('a'))
    afz = sa([apair], 'simpld', 'a e. ( 1 ... Z )')
    arad = sa([apair], 'simprd', '%s = L' % RD('a'))
    ann = sa([afz, w.inst('elfznn')], 'syl', 'a e. NN')
    aleZ = sa([afz, w.inst('elfzle2')], 'syl', 'a <_ Z')
    rl = sa([ann, w.inst('radlem')], 'syl',
            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s /\\ %s || a )'
            % (RD('a'), RD('a'), RD('a'), PF('a', 'u'), RD('a')))
    ldvd = sa([arad, sa([rl], 'simp3d', '%s || a' % RD('a'))], 'eqbrtrrd', 'L || a')
    aLnn = sa([sa([ann, LA(lnn), w.inst('nndivdvds')], 'syl2anc',
                  '( L || a <-> ( a / L ) e. NN )'), ldvd], 'mpbid', '( a / L ) e. NN')
    aLdv = sa([sa([sa([LA(lnn)], 'nnzd', 'L e. ZZ'), sa([aLnn], 'nnzd', '( a / L ) e. ZZ'),
                   w.inst('dvdsmul2')], 'syl2anc', '( a / L ) || ( L x. ( a / L ) )'),
               sa([sa([ann], 'nncnd', 'a e. CC'), LA(lcc), LA(lne)], 'divcan2d',
                  '( L x. ( a / L ) ) = a')], 'breqtrd', '( a / L ) || a')
    aLle = sa([sa([sa([sa([aLnn], 'nnzd', '( a / L ) e. ZZ'), ann], 'jca',
                      '( ( a / L ) e. ZZ /\\ a e. NN )'), w.inst('dvdsle')], 'syl',
                  '( ( a / L ) || a -> ( a / L ) <_ a )'), aLdv], 'mpd', '( a / L ) <_ a')
    aLleZ = sa([sa([aLnn], 'nnred', '( a / L ) e. RR'), sa([ann], 'nnred', 'a e. RR'),
                LA(st([znn], 'nnred', 'Z e. RR')), aLle, aleZ], 'letrd', '( a / L ) <_ Z')
    aLfz = sa([sa([LA(zz), w.inst('fznn')], 'syl',
                  '( ( a / L ) e. ( 1 ... Z ) <-> ( ( a / L ) e. NN /\\ ( a / L ) <_ Z ) )'),
               sa([aLnn, aLleZ], 'jca', '( ( a / L ) e. NN /\\ ( a / L ) <_ Z )')], 'mpbird',
              '( a / L ) e. ( 1 ... Z )')
    # the prime-divisor equality and the smoothness of a / L
    bq = sa([arad], 'breq2d', '( q || %s <-> q || L )' % RD('a'))
    rb = sa([bq], 'rabbidv', '{ q e. Prime | q || %s } = { q e. Prime | q || L }' % RD('a'))
    pfeq = sa([rb, sa([rl], 'simp2d',
                      '{ q e. Prime | q || %s } = %s' % (RD('a'), PF('a', 'u')))], 'eqtr3d',
              '{ q e. Prime | q || L } = %s' % PF('a', 'u'))
    AF = '( %s /\\ f e. %s )' % (AA, SMR('( a / L )'))
    sf = mkst(w, AF)
    LF = lambda s: lift(w, s, AF)
    elf0 = w.s([w.s([], 'breq1', '( r = f -> ( r || ( a / L ) <-> f || ( a / L ) ) )')],
               'elrab', '( f e. %s <-> ( f e. Prime /\\ f || ( a / L ) ) )' % SMR('( a / L )'))
    fpair = sf([sf([], 'simpr', 'f e. %s' % SMR('( a / L )')),
                sf([elf0], 'a1i', '( f e. %s <-> ( f e. Prime /\\ f || ( a / L ) ) )'
                   % SMR('( a / L )'))], 'mpbid', '( f e. Prime /\\ f || ( a / L ) )')
    fprm = sf([fpair], 'simpld', 'f e. Prime')
    fdv = sf([fpair], 'simprd', 'f || ( a / L )')
    fdva = sf([sf([sf([sf([sf([fprm, w.inst('prmnn')], 'syl', 'f e. NN')], 'nnzd', 'f e. ZZ'),
                       LF(sa([aLnn], 'nnzd', '( a / L ) e. ZZ')),
                       LF(sa([ann], 'nnzd', 'a e. ZZ'))], '3jca',
                      '( f e. ZZ /\\ ( a / L ) e. ZZ /\\ a e. ZZ )'), w.inst('dvdstr')], 'syl',
                  '( ( f || ( a / L ) /\\ ( a / L ) || a ) -> f || a )'),
               fdv, LF(aLdv)], 'mp2and', 'f || a')
    elu = w.s([w.s([], 'breq1', '( u = f -> ( u || a <-> f || a ) )')], 'elrab',
              '( f e. %s <-> ( f e. Prime /\\ f || a ) )' % PF('a', 'u'))
    fu = sf([sf([elu], 'a1i', '( f e. %s <-> ( f e. Prime /\\ f || a ) )' % PF('a', 'u')),
             sf([fprm, fdva], 'jca', '( f e. Prime /\\ f || a )')], 'mpbird',
            'f e. %s' % PF('a', 'u'))
    elq = w.s([w.s([], 'breq1', '( q = f -> ( q || L <-> f || L ) )')], 'elrab',
              '( f e. { q e. Prime | q || L } <-> ( f e. Prime /\\ f || L ) )')
    fq = sf([fu, LF(pfeq)], 'eleqtrrd', 'f e. { q e. Prime | q || L }')
    fdvl = sf([sf([fq, sf([elq], 'a1i',
                          '( f e. { q e. Prime | q || L } <-> ( f e. Prime /\\ f || L ) )')],
                  'mpbid', '( f e. Prime /\\ f || L )')], 'simprd', 'f || L')
    elg = w.s([w.s([], 'breq1', '( g = f -> ( g || L <-> f || L ) )')], 'elrab',
              '( f e. %s <-> ( f e. Prime /\\ f || L ) )' % QG)
    fg = sf([sf([elg], 'a1i', '( f e. %s <-> ( f e. Prime /\\ f || L ) )' % QG),
             sf([fprm, fdvl], 'jca', '( f e. Prime /\\ f || L )')], 'mpbird', 'f e. %s' % QG)
    subs = sa([sa([fg], 'ex', '( f e. %s -> f e. %s )' % (SMR('( a / L )'), QG))], 'ssrdv',
              '%s C_ %s' % (SMR('( a / L )'), QG))
    elsm = w.s([w.s([w.s([w.s([], 'breq2',
                              '( v = ( a / L ) -> ( r || v <-> r || ( a / L ) ) )')],
                         'rabbidv', '( v = ( a / L ) -> %s = %s )' % (SMR('v'), SMR('( a / L )'))) ],
                    'sseq1d',
                    '( v = ( a / L ) -> ( %s C_ %s <-> %s C_ %s ) )'
                    % (SMR('v'), QG, SMR('( a / L )'), QG))], 'elrab',
               '( ( a / L ) e. %s <-> ( ( a / L ) e. ( 1 ... Z ) /\\ %s C_ %s ) )'
               % (SM, SMR('( a / L )'), QG))
    asm = sa([sa([elsm], 'a1i',
                 '( ( a / L ) e. %s <-> ( ( a / L ) e. ( 1 ... Z ) /\\ %s C_ %s ) )'
                 % (SM, SMR('( a / L )'), QG)),
              sa([aLfz, subs], 'jca',
                 '( ( a / L ) e. ( 1 ... Z ) /\\ %s C_ %s )' % (SMR('( a / L )'), QG))],
             'mpbird', '( a / L ) e. %s' % SM)
    ral1 = st([asm], 'ralrimiva', 'A. a e. %s ( a / L ) e. %s' % (FB, SM))
    # ---- injectivity ----------------------------------------------------
    AI = '( %s /\\ ( a e. %s /\\ n e. %s ) )' % (ANT, FB, FB)
    si = mkst(w, AI)
    LI = lambda s: lift(w, s, AI)
    iann = si([si([si([], 'simprl', 'a e. %s' % FB), si([elfa], 'a1i', ELFB('a'))], 'mpbid',
                  '( a e. ( 1 ... Z ) /\\ %s = L )' % RD('a'))], 'simpld',
              'a e. ( 1 ... Z )')
    inn = si([si([si([], 'simprr', 'n e. %s' % FB), si([elfn], 'a1i', ELFB('n'))], 'mpbid',
                 '( n e. ( 1 ... Z ) /\\ %s = L )' % RD('n'))], 'simpld', 'n e. ( 1 ... Z )')
    acc = si([si([iann, w.inst('elfznn')], 'syl', 'a e. NN')], 'nncnd', 'a e. CC')
    ncc = si([si([inn, w.inst('elfznn')], 'syl', 'n e. NN')], 'nncnd', 'n e. CC')
    d11 = si([acc, ncc, si([LI(lcc), LI(lne)], 'jca', '( L e. CC /\\ L =/= 0 )'),
              w.inst('div11')], 'syl3anc', '( ( a / L ) = ( n / L ) <-> a = n )')
    inj = si([d11], 'biimpd', '( ( a / L ) = ( n / L ) -> a = n )')
    ral2 = st([inj], 'ralrimivva',
              'A. a e. %s A. n e. %s ( ( a / L ) = ( n / L ) -> a = n )' % (FB, FB))
    fm = w.s([w.s([], 'eqid', '%s = %s' % (FMAP, FMAP)),
              w.s([], 'oveq1', '( a = n -> ( a / L ) = ( n / L ) )')], 'f1mpt',
             '( %s : %s -1-1-> %s <-> ( A. a e. %s ( a / L ) e. %s /\\ A. a e. %s A. n e. %s ( ( a / L ) = ( n / L ) -> a = n ) ) )'
             % (FMAP, FB, SM, FB, SM, FB, FB))
    f1 = st([ral1, ral2, st([fm], 'a1i',
             '( %s : %s -1-1-> %s <-> ( A. a e. %s ( a / L ) e. %s /\\ A. a e. %s A. n e. %s ( ( a / L ) = ( n / L ) -> a = n ) ) )'
             % (FMAP, FB, SM, FB, SM, FB, FB))], 'mpbir2and',
            '%s : %s -1-1-> %s' % (FMAP, FB, SM))
    f1o = st([f1, w.inst('f1f1orn')], 'syl', '%s : %s -1-1-onto-> ran %s' % (FMAP, FB, FMAP))
    rnss = st([st([f1, w.inst('f1f')], 'syl', '%s : %s --> %s' % (FMAP, FB, SM)),
               w.inst('frn')], 'syl', 'ran %s C_ %s' % (FMAP, SM))
    rnfin = st([smfin, rnss], 'ssfid', 'ran %s e. Fin' % FMAP)
    # ---- the SM body and the range body ----------------------------------
    AJ = '( %s /\\ j e. %s )' % (ANT, SM)
    sj = mkst(w, AJ)
    jfz = sj([sj([], 'simpr', 'j e. %s' % SM), w.inst('elrabi')], 'syl', 'j e. ( 1 ... Z )')
    jnn = sj([jfz, w.inst('elfznn')], 'syl', 'j e. NN')
    jrp = sj([sj([jnn, w.inst('nnrp')], 'syl', 'j e. RR+')], 'rpreccld', '( 1 / j ) e. RR+')
    jre = sj([jrp], 'rpred', '( 1 / j ) e. RR')
    jge = sj([jrp, w.inst('rpgt0')], 'syl', '0 < ( 1 / j )')
    jge2 = sj([sj([], '0red', '0 e. RR'), jre, jge], 'ltled', '0 <_ ( 1 / j )')
    AK = '( %s /\\ j e. ran %s )' % (ANT, FMAP)
    sk = mkst(w, AK)
    kjsm = sk([lift(w, rnss, AK), sk([], 'simpr', 'j e. ran %s' % FMAP)], 'sseldd',
              'j e. %s' % SM)
    kfz = sk([kjsm, w.inst('elrabi')], 'syl', 'j e. ( 1 ... Z )')
    kcc = sk([sk([kfz, w.inst('elfznn')], 'syl', 'j e. NN')], 'nnrecred',
             '( 1 / j ) e. RR')
    kccc = sk([kcc], 'recnd', '( 1 / j ) e. CC')
    # ---- fsumf1o ---------------------------------------------------------
    AO = '( %s /\\ o e. %s )' % (ANT, FB)
    so = mkst(w, AO)
    fv = so([so([], 'simpr', 'o e. %s' % FB),
             so([w.s([], 'ovex', '( o / L ) e. _V')], 'a1i', '( o / L ) e. _V'),
             w.s([w.s([], 'oveq1', '( a = o -> ( a / L ) = ( o / L ) )'),
                  w.s([], 'eqid', '%s = %s' % (FMAP, FMAP))], 'fvmptg',
                 '( ( o e. %s /\\ ( o / L ) e. _V ) -> ( %s ` o ) = ( o / L ) )' % (FB, FMAP))],
            'syl2anc', '( %s ` o ) = ( o / L )' % FMAP)
    f1oS = st([w.s([], 'oveq2', '( j = ( o / L ) -> ( 1 / j ) = ( 1 / ( o / L ) ) )'),
               fbfin, f1o, fv, kccc], 'fsumf1o',
              'sum_ j e. ran %s ( 1 / j ) = sum_ o e. %s ( 1 / ( o / L ) )' % (FMAP, FB))
    # ---- fsumless and smsum ----------------------------------------------
    less = st([smfin, jre, jge2, rnss], 'fsumless',
              'sum_ j e. ran %s ( 1 / j ) <_ sum_ j e. %s ( 1 / j )' % (FMAP, SM))
    qgfin = st([st([w.s([w.s([], 'breq1', '( q = g -> ( q || L <-> g || L ) )')], 'cbvrabv',
                        '{ q e. Prime | q || L } = %s' % QG)], 'a1i',
                   '{ q e. Prime | q || L } = %s' % QG),
                st([lnn, w.inst('pffinq')], 'syl', '{ q e. Prime | q || L } e. Fin')],
               'eqeltrrd', '%s e. Fin' % QG)
    qgss = st([w.s([], 'ssrab2', '%s C_ Prime' % QG)], 'a1i', '%s C_ Prime' % QG)
    sms = st([qgfin, qgss, znn, w.inst('smsum')], 'syl3anc',
             'sum_ j e. %s ( 1 / j ) <_ %s' % (SM, PRODG))
    # ---- the product bridge ----------------------------------------------
    cbp = st([w.s([w.s([w.s([w.s([], 'oveq2', '( p = q -> ( 1 / p ) = ( 1 / q ) )')],
                            'oveq2d', '( p = q -> ( 1 - ( 1 / p ) ) = ( 1 - ( 1 / q ) ) )')],
                       'oveq2d',
                       '( p = q -> ( 1 / ( 1 - ( 1 / p ) ) ) = ( 1 / ( 1 - ( 1 / q ) ) ) )')],
                  'cbvprodv',
                  '%s = prod_ q e. %s ( 1 / ( 1 - ( 1 / q ) ) )' % (PRODG, QG))], 'a1i',
             '%s = prod_ q e. %s ( 1 / ( 1 - ( 1 / q ) ) )' % (PRODG, QG))
    cbg = st([st([w.s([w.s([], 'breq1', '( g = r -> ( g || L <-> r || L ) )')], 'cbvrabv',
                      '%s = %s' % (QG, PF('L')))], 'a1i', '%s = %s' % (QG, PF('L')))],
             'prodeq1d',
             'prod_ q e. %s ( 1 / ( 1 - ( 1 / q ) ) ) = %s' % (QG, PRODQ))
    pbr = st([cbp, cbg], 'eqtrd', '%s = %s' % (PRODG, PRODQ))
    # PRODG e. RR
    AP = '( %s /\\ p e. %s )' % (ANT, QG)
    sp = mkst(w, AP)
    pprm = sp([sp([], 'simpr', 'p e. %s' % QG), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn = sp([pprm, w.inst('prmnn')], 'syl', 'p e. NN')
    prp = sp([pnn, w.inst('nnrp')], 'syl', 'p e. RR+')
    prec = sp([prp], 'rpreccld', '( 1 / p ) e. RR+')
    plt1 = sp([sp([sp([prp], 'rpred', 'p e. RR'), sp([prp, w.inst('rpgt0')], 'syl', '0 < p'),
                   w.inst('recgt1')], 'syl2anc', '( 1 < p <-> ( 1 / p ) < 1 )'),
               sp([pprm, w.inst('prmgt1')], 'syl', '1 < p')], 'mpbid', '( 1 / p ) < 1')
    onere = sp([], '1red', '1 e. RR')
    precre = sp([prec], 'rpred', '( 1 / p ) e. RR')
    pd = sp([precre, onere], 'posdifd', '( ( 1 / p ) < 1 <-> 0 < ( 1 - ( 1 / p ) ) )')
    ppos = sp([pd, plt1], 'mpbid', '0 < ( 1 - ( 1 / p ) )')
    psubre = sp([onere, precre], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    psubrp = sp([psubre, ppos], 'elrpd', '( 1 - ( 1 / p ) ) e. RR+')
    pinv = sp([sp([psubrp], 'rpreccld', '( 1 / ( 1 - ( 1 / p ) ) ) e. RR+')], 'rpred',
              '( 1 / ( 1 - ( 1 / p ) ) ) e. RR')
    prodgre = st([qgfin, pinv], 'fprodrecl', '%s e. RR' % PRODG)
    # ---- the left-hand side ---------------------------------------------
    AW = '( %s /\\ w e. %s )' % (ANT, FB)
    sww = mkst(w, AW)
    wrad = sww([sww([], 'simpr', 'w e. %s' % FB), sww([elfw], 'a1i', ELFB('w'))], 'mpbid',
               '( w e. ( 1 ... Z ) /\\ %s = L )' % RD('w'))
    wr2 = sww([wrad], 'simprd', '%s = L' % RD('w'))
    wfz = sww([wrad], 'simpld', 'w e. ( 1 ... Z )')
    wif = sww([wr2], 'iftrued', '%s = ( 1 / w )' % IFW)
    wrec = sww([sww([sww([sww([wfz, w.inst('elfznn')], 'syl', 'w e. NN'), w.inst('nnrp')],
                         'syl', 'w e. RR+')], 'rpreccld', '( 1 / w ) e. RR+')], 'rpcnd',
               '( 1 / w ) e. CC')
    wcc = sww([wif, wrec], 'eqeltrd', '%s e. CC' % IFW)
    ARR = '( %s /\\ w e. ( ( 1 ... Z ) \\ %s ) )' % (ANT, FB)
    sr = mkst(w, ARR)
    rfz = sr([sr([], 'simpr', 'w e. ( ( 1 ... Z ) \\ %s )' % FB), w.inst('eldifi')], 'syl',
             'w e. ( 1 ... Z )')
    rnin = sr([sr([], 'simpr', 'w e. ( ( 1 ... Z ) \\ %s )' % FB), w.inst('eldifn')], 'syl',
              '-. w e. %s' % FB)
    ARE = '( %s /\\ %s = L )' % (ARR, RD('w'))
    sre = mkst(w, ARE)
    rein = sre([sre([elfw], 'a1i', ELFB('w')),
                sre([lift(w, rfz, ARE), sre([], 'simpr', '%s = L' % RD('w'))], 'jca',
                    '( w e. ( 1 ... Z ) /\\ %s = L )' % RD('w'))], 'mpbird',
               'w e. %s' % FB)
    rimp = sr([rein], 'ex', '( %s = L -> w e. %s )' % (RD('w'), FB))
    rnrad = sr([rnin, rimp], 'mtod', '-. %s = L' % RD('w'))
    rz = sr([rnrad], 'iffalsed', '%s = 0' % IFW)
    fbss = st([w.s([], 'ssrab2', '%s C_ ( 1 ... Z )' % FB)], 'a1i',
              '%s C_ ( 1 ... Z )' % FB)
    LHS0 = 'sum_ w e. ( 1 ... Z ) %s' % IFW
    ss1 = st([fbss, wcc, rz, fzf], 'fsumss',
             'sum_ w e. %s %s = %s' % (FB, IFW, LHS0))
    eq1 = st([wif], 'sumeq2dv',
             'sum_ w e. %s %s = sum_ w e. %s ( 1 / w )' % (FB, IFW, FB))
    cbs = st([w.s([w.s([], 'oveq2', '( w = o -> ( 1 / w ) = ( 1 / o ) )')], 'cbvsumv',
                  'sum_ w e. %s ( 1 / w ) = sum_ o e. %s ( 1 / o )' % (FB, FB))], 'a1i',
             'sum_ w e. %s ( 1 / w ) = sum_ o e. %s ( 1 / o )' % (FB, FB))
    # ( 1 / o ) = ( 1 / L ) x. ( 1 / ( o / L ) )
    LO = lambda x: lift(w, x, AO)
    opair = so([so([], 'simpr', 'o e. %s' % FB), so([elfo], 'a1i', ELFB('o'))], 'mpbid',
               '( o e. ( 1 ... Z ) /\\ %s = L )' % RD('o'))
    ofz = so([opair], 'simpld', 'o e. ( 1 ... Z )')
    orad = so([opair], 'simprd', '%s = L' % RD('o'))
    onn = so([ofz, w.inst('elfznn')], 'syl', 'o e. NN')
    ocdv = so([orad, so([so([onn, w.inst('radlem')], 'syl',
                            '( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ { q e. Prime | q || %s } = %s /\\ %s || o )'
                            % (RD('o'), RD('o'), RD('o'), PF('o', 'u'), RD('o')))], 'simp3d',
                        '%s || o' % RD('o'))], 'eqbrtrrd', 'L || o')
    oLnn = so([so([onn, LO(lnn), w.inst('nndivdvds')], 'syl2anc',
                  '( L || o <-> ( o / L ) e. NN )'), ocdv], 'mpbid', '( o / L ) e. NN')
    dmd = so([so([so([], '1cnd', '1 e. CC'), so([], '1cnd', '1 e. CC')], 'jca',
                 '( 1 e. CC /\\ 1 e. CC )'),
              so([so([LO(lcc), LO(lne)], 'jca', '( L e. CC /\\ L =/= 0 )'),
                  so([so([oLnn], 'nncnd', '( o / L ) e. CC'),
                      so([oLnn], 'nnne0d', '( o / L ) =/= 0')], 'jca',
                     '( ( o / L ) e. CC /\\ ( o / L ) =/= 0 )')], 'jca',
                 '( ( L e. CC /\\ L =/= 0 ) /\\ ( ( o / L ) e. CC /\\ ( o / L ) =/= 0 ) )')],
             'jca',
             '( ( 1 e. CC /\\ 1 e. CC ) /\\ ( ( L e. CC /\\ L =/= 0 ) /\\ ( ( o / L ) e. CC /\\ ( o / L ) =/= 0 ) ) )')
    dm = so([dmd, w.inst('divmuldiv')], 'syl',
            '( ( 1 / L ) x. ( 1 / ( o / L ) ) ) = ( ( 1 x. 1 ) / ( L x. ( o / L ) ) )')
    dc = so([so([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'),
             so([so([onn], 'nncnd', 'o e. CC'), LO(lcc), LO(lne)], 'divcan2d',
                '( L x. ( o / L ) ) = o')], 'oveq12d',
            '( ( 1 x. 1 ) / ( L x. ( o / L ) ) ) = ( 1 / o )')
    obody = so([dm, dc], 'eqtrd', '( ( 1 / L ) x. ( 1 / ( o / L ) ) ) = ( 1 / o )')
    sm2 = st([obody], 'sumeq2dv',
             'sum_ o e. %s ( ( 1 / L ) x. ( 1 / ( o / L ) ) ) = sum_ o e. %s ( 1 / o )'
             % (FB, FB))
    oLcc = so([so([oLnn, w.inst('nnrp')], 'syl', '( o / L ) e. RR+')], 'rpreccld',
              '( 1 / ( o / L ) ) e. RR+')
    oLccc = so([oLcc], 'rpcnd', '( 1 / ( o / L ) ) e. CC')
    lreccc = st([lrec], 'rpcnd', '( 1 / L ) e. CC')
    SUMOL = 'sum_ o e. %s ( 1 / ( o / L ) )' % FB
    SUMO = 'sum_ o e. %s ( 1 / o )' % FB
    SUMR = 'sum_ j e. ran %s ( 1 / j )' % FMAP
    SUMS = 'sum_ j e. %s ( 1 / j )' % SM
    mulc = st([fbfin, lreccc, oLccc], 'fsummulc2',
              '( ( 1 / L ) x. %s ) = sum_ o e. %s ( ( 1 / L ) x. ( 1 / ( o / L ) ) )'
              % (SUMOL, FB))
    e2 = st([st([mulc, sm2], 'eqtrd', '( ( 1 / L ) x. %s ) = %s' % (SUMOL, SUMO))], 'eqcomd',
            '%s = ( ( 1 / L ) x. %s )' % (SUMO, SUMOL))
    e1 = st([st([st([ss1], 'eqcomd', '%s = sum_ w e. %s %s' % (LHS0, FB, IFW)), eq1], 'eqtrd',
                '%s = sum_ w e. %s ( 1 / w )' % (LHS0, FB)), cbs], 'eqtrd',
            '%s = %s' % (LHS0, SUMO))
    e3 = st([f1oS], 'eqcomd', '%s = %s' % (SUMOL, SUMR))
    lhsE = st([st([e1, e2], 'eqtrd', '%s = ( ( 1 / L ) x. %s )' % (LHS0, SUMOL)),
               st([e3], 'oveq2d',
                  '( ( 1 / L ) x. %s ) = ( ( 1 / L ) x. %s )' % (SUMOL, SUMR))], 'eqtrd',
              '%s = ( ( 1 / L ) x. %s )' % (LHS0, SUMR))
    lrge = st([st([], '0red', '0 e. RR'), lrecre, lrec0], 'ltled', '0 <_ ( 1 / L )')
    rnre = st([rnfin, kcc], 'fsumrecl', '%s e. RR' % SUMR)
    smre = st([smfin, jre], 'fsumrecl', '%s e. RR' % SUMS)
    t1 = st([rnre, smre, lrecre, lrge, less], 'lemul2ad',
            '( ( 1 / L ) x. %s ) <_ ( ( 1 / L ) x. %s )' % (SUMR, SUMS))
    t2 = st([smre, prodgre, lrecre, lrge, sms], 'lemul2ad',
            '( ( 1 / L ) x. %s ) <_ ( ( 1 / L ) x. %s )' % (SUMS, PRODG))
    t3 = st([pbr], 'oveq2d', '( ( 1 / L ) x. %s ) = %s' % (PRODG, GTR('L')))
    AZ = '( %s /\\ w e. ( 1 ... Z ) )' % ANT
    sz = mkst(w, AZ)
    zrec = sz([sz([sz([sz([], 'simpr', 'w e. ( 1 ... Z )'), w.inst('elfznn')], 'syl',
                      'w e. NN'), w.inst('nnrp')], 'syl', 'w e. RR+')], 'rpreccld',
              '( 1 / w ) e. RR+')
    zife = sz([sz([zrec], 'rpred', '( 1 / w ) e. RR'), sz([], '0red', '0 e. RR')], 'ifcld',
              '%s e. RR' % IFW)
    lhsre = st([fzf, zife], 'fsumrecl', '%s e. RR' % LHS0)
    stepA = st([lhsE, t1], 'eqbrtrd', '%s <_ ( ( 1 / L ) x. %s )' % (LHS0, SUMS))
    mul1 = st([lrecre, smre], 'remulcld', '( ( 1 / L ) x. %s ) e. RR' % SUMS)
    mul2 = st([lrecre, prodgre], 'remulcld', '( ( 1 / L ) x. %s ) e. RR' % PRODG)
    stepB = st([lhsre, mul1, mul2, stepA, t2], 'letrd',
               '%s <_ ( ( 1 / L ) x. %s )' % (LHS0, PRODG))
    w.qed([stepB, t3], 'breqtrd', '( %s -> %s <_ %s )' % (ANT, LHS0, GTR('L')))
    return w


def main(names=None):
    fns = {'progfib': progfib}
    ok = True
    for nm in (names or ['progfib']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
