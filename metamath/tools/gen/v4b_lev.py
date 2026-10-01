"""Sortie v4b: the sifting level as a function of L = log ( N / M ).

btlev  ( ( L e. RR /\\ 6400000 <_ L ) ->
           ( ( ZFL e. NN /\\ 2 <_ ZFL ) /\\
             ( ( ( 5 / 14 ) x. L ) <_ ( log ` ZFL ) /\\ ( log ` ZFL ) <_ ( ( 2 / 5 ) x. L ) ) /\\
             ZFL <_ E25L ) )
bterr  ( ( L e. RR /\\ 6400000 <_ L ) ->
           ( ( ( ZFL ^ 2 ) x. ( ( 1 + ( log ` ( ZFL ^ 2 ) ) ) ^ 2 ) ) + ZFL ) <_
             ( ( 1 / 5 ) x. ( ( exp ` L ) / L ) ) )
btmain the main-term division of the assembly
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v4b_lib import mkst
import num
from lin import linarith, nlinarith, lineq

C64 = num.nat_text(6400000)
C10 = num.nat_text(10)
K5 = '( 5 / %s )' % num.nat_text(14)
K14 = '( %s / 5 )' % num.nat_text(14)
AL = '( L e. RR /\\ %s <_ L )' % C64
EE = '( exp ` ( ( 2 / 5 ) x. L ) )'
ZZF = '( |_ ` %s )' % EE
LOGZ = '( log ` %s )' % ZZF
LOGZ2 = '( log ` ( %s ^ 2 ) )' % ZZF
CONCL = ('( ( %s e. NN /\\ 2 <_ %s ) /\\ ( ( %s x. L ) <_ %s /\\ %s <_ ( ( 2 / 5 ) x. L ) ) '
         '/\\ %s <_ %s )' % (ZZF, ZZF, K5, LOGZ, LOGZ, ZZF, EE))
ERB = '( ( %s ^ 2 ) x. ( ( 1 + L ) ^ 2 ) )' % EE
ETERM = '( ( %s ^ 2 ) x. ( ( 1 + %s ) ^ 2 ) )' % (ZZF, LOGZ2)
EGOAL = '( %s + %s ) <_ ( ( 1 / 5 ) x. ( ( exp ` L ) / L ) )' % (ETERM, ZZF)


def _base(w, st):
    """the common setup: L real, positive, and the level facts"""
    d = {}
    d['lre'] = st([], 'simpl', 'L e. RR')
    d['hL'] = st([], 'simpr', '%s <_ L' % C64)
    LV = {'L': d['lre']}
    d['LV'] = LV
    d['hL0'] = linarith(w, AL, [d['hL']], '0 <_ L', leaves=LV)
    d['hL1'] = linarith(w, AL, [d['hL']], '1 <_ L', leaves=LV)
    d['hLp'] = linarith(w, AL, [d['hL']], '0 < L', leaves=LV)
    d['lrp'] = st([d['lre'], d['hLp']], 'elrpd', 'L e. RR+')
    d['re2'] = st([num.re_nat(w, 2)], 'a1i', '2 e. RR')
    d['z2'] = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    d['n2'] = st([num.nn0(w, 2)], 'a1i', '2 e. NN0')
    d['e25re'] = st([st([num.real(w, '( 2 / 5 )')], 'a1i', '( 2 / 5 ) e. RR'), d['lre']],
                    'remulcld', '( ( 2 / 5 ) x. L ) e. RR')
    d['eerp'] = st([d['e25re'], w.inst('rpefcl')], 'syl', '%s e. RR+' % EE)
    d['eere'] = st([d['eerp']], 'rpred', '%s e. RR' % EE)
    d['eege'] = st([d['eerp'], w.inst('rpge0')], 'syl', '0 <_ %s' % EE)
    return d


def btlev():
    w = W('btlev', 'The sifting level of the Brun-Titchmarsh assembly: the floor of '
                   'exp ( ( 2 / 5 ) log ( N / M ) ) and the bounds on its logarithm.')
    st = mkst(w, AL)
    d = _base(w, st)
    LV = d['LV']
    e25gt = st([st([d['e25re'], linarith(w, AL, [d['hL']], '0 < ( ( 2 / 5 ) x. L )',
                                        leaves=LV)], 'elrpd',
                   '( ( 2 / 5 ) x. L ) e. RR+'), w.inst('efgt1p')], 'syl',
               '( 1 + ( ( 2 / 5 ) x. L ) ) < %s' % EE)
    onee = st([st([], '1red', '1 e. RR'), d['e25re']], 'readdcld',
              '( 1 + ( ( 2 / 5 ) x. L ) ) e. RR')
    e2 = st([d['re2'], onee, d['eere'],
             linarith(w, AL, [d['hL']], '2 <_ ( 1 + ( ( 2 / 5 ) x. L ) )', leaves=LV),
             e25gt], 'lelttrd', '2 < %s' % EE)
    e2le = st([d['re2'], d['eere'], e2], 'ltled', '2 <_ %s' % EE)
    zfz = st([d['eere'], w.inst('flcl')], 'syl', '%s e. ZZ' % ZZF)
    zfle = st([d['eere'], w.inst('flle')], 'syl', '%s <_ %s' % (ZZF, EE))
    zflt = st([d['eere'], w.inst('flltp1')], 'syl', '%s < ( %s + 1 )' % (EE, ZZF))
    zfre = st([zfz], 'zred', '%s e. RR' % ZZF)
    ZV = {ZZF: zfre, EE: d['eere']}
    z2le = st([st([d['eere'], d['z2'], w.inst('flge')], 'syl2anc',
                  '( 2 <_ %s <-> 2 <_ %s )' % (EE, ZZF)), e2le], 'mpbid', '2 <_ %s' % ZZF)
    zfnn = st([st([zfz, linarith(w, AL, [z2le], '0 < %s' % ZZF, leaves=ZV)], 'jca',
                  '( %s e. ZZ /\\ 0 < %s )' % (ZZF, ZZF)),
               st([w.s([], 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )'
                       % (ZZF, ZZF, ZZF))], 'a1i',
                  '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (ZZF, ZZF, ZZF))], 'mpbird',
              '%s e. NN' % ZZF)
    zfrp = st([zfnn, w.inst('nnrp')], 'syl', '%s e. RR+' % ZZF)
    zf1 = linarith(w, AL, [z2le], '1 <_ %s' % ZZF, leaves=ZV)
    e2half = linarith(w, AL, [zflt, zf1], '( %s / 2 ) <_ %s' % (EE, ZZF), leaves=dict(ZV))
    logzre = st([zfrp], 'relogcld', '%s e. RR' % LOGZ)
    logE = st([d['e25re'], w.inst('relogef')], 'syl',
              '( log ` %s ) = ( ( 2 / 5 ) x. L )' % EE)
    lzub = st([st([st([zfrp, d['eerp'], w.inst('logleb')], 'syl2anc',
                      '( %s <_ %s <-> %s <_ ( log ` %s ) )' % (ZZF, EE, LOGZ, EE)),
                   zfle], 'mpbid', '%s <_ ( log ` %s )' % (LOGZ, EE)), logE], 'breqtrd',
              '%s <_ ( ( 2 / 5 ) x. L )' % LOGZ)
    hrp = st([d['eerp'], st([num.rp_nat(w, 2)], 'a1i', '2 e. RR+')], 'rpdivcld',
             '( %s / 2 ) e. RR+' % EE)
    lzlb0 = st([st([hrp, zfrp, w.inst('logleb')], 'syl2anc',
                   '( ( %s / 2 ) <_ %s <-> ( log ` ( %s / 2 ) ) <_ %s )' % (EE, ZZF, EE, LOGZ)),
                e2half], 'mpbid', '( log ` ( %s / 2 ) ) <_ %s' % (EE, LOGZ))
    lgdiv = st([st([d['eerp'], st([num.rp_nat(w, 2)], 'a1i', '2 e. RR+'),
                    w.inst('relogdiv')], 'syl2anc',
                   '( log ` ( %s / 2 ) ) = ( ( log ` %s ) - ( log ` 2 ) )' % (EE, EE)),
                st([logE], 'oveq1d',
                   '( ( log ` %s ) - ( log ` 2 ) ) = ( ( ( 2 / 5 ) x. L ) - ( log ` 2 ) )' % EE)],
               'eqtrd',
               '( log ` ( %s / 2 ) ) = ( ( ( 2 / 5 ) x. L ) - ( log ` 2 ) )' % EE)
    log2le = st([st([st([num.rp_nat(w, 1)], 'a1i', '1 e. RR+'), w.inst('logp1le')], 'syl',
                    '( log ` ( 1 + 1 ) ) <_ 1'),
                 st([st([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2')],
                    'fveq2d', '( log ` ( 1 + 1 ) ) = ( log ` 2 )')], 'eqbrtrrd',
                '( log ` 2 ) <_ 1')
    log2re = st([st([num.rp_nat(w, 2)], 'a1i', '2 e. RR+')], 'relogcld', '( log ` 2 ) e. RR')
    lzlb1 = st([lgdiv, lzlb0], 'eqbrtrrd',
               '( ( ( 2 / 5 ) x. L ) - ( log ` 2 ) ) <_ %s' % LOGZ)
    lzlb = linarith(w, AL, [lzlb1, log2le, d['hL']], '( %s x. L ) <_ %s' % (K5, LOGZ),
                    leaves={'L': d['lre'], LOGZ: logzre, '( log ` 2 )': log2re})
    w.qed([st([zfnn, z2le], 'jca', '( %s e. NN /\\ 2 <_ %s )' % (ZZF, ZZF)),
           st([lzlb, lzub], 'jca',
              '( ( %s x. L ) <_ %s /\\ %s <_ ( ( 2 / 5 ) x. L ) )' % (K5, LOGZ, LOGZ)),
           zfle], '3jca', '( %s -> %s )' % (AL, CONCL))
    return w


def bterr():
    w = W('bterr', 'The error term of the Brun-Titchmarsh assembly is at most one fifth of '
                   'exp ( L ) / L.')
    st = mkst(w, AL)
    d = _base(w, st)
    LV = d['LV']
    lev = st([], 'btlev', CONCL)
    p1 = st([lev], 'simp1d', '( %s e. NN /\\ 2 <_ %s )' % (ZZF, ZZF))
    zfnn = st([p1], 'simpld', '%s e. NN' % ZZF)
    z2le = st([p1], 'simprd', '2 <_ %s' % ZZF)
    p2 = st([lev], 'simp2d',
            '( ( %s x. L ) <_ %s /\\ %s <_ ( ( 2 / 5 ) x. L ) )' % (K5, LOGZ, LOGZ))
    lzlb = st([p2], 'simpld', '( %s x. L ) <_ %s' % (K5, LOGZ))
    lzub = st([p2], 'simprd', '%s <_ ( ( 2 / 5 ) x. L )' % LOGZ)
    zfle = st([lev], 'simp3d', '%s <_ %s' % (ZZF, EE))
    zfrp = st([zfnn, w.inst('nnrp')], 'syl', '%s e. RR+' % ZZF)
    zfre = st([zfrp], 'rpred', '%s e. RR' % ZZF)
    zfge = st([zfrp, w.inst('rpge0')], 'syl', '0 <_ %s' % ZZF)
    logzre = st([zfrp], 'relogcld', '%s e. RR' % LOGZ)
    lzpos = linarith(w, AL, [lzlb, d['hL']], '0 < %s' % LOGZ,
                     leaves={'L': d['lre'], LOGZ: logzre})
    lz2 = st([zfrp, d['z2'], w.inst('relogexp')], 'syl2anc',
             '%s = ( 2 x. %s )' % (LOGZ2, LOGZ))
    lz2re = st([st([zfrp, d['z2']], 'rpexpcld', '( %s ^ 2 ) e. RR+' % ZZF)], 'relogcld',
               '%s e. RR' % LOGZ2)
    LZV = {LOGZ2: lz2re, LOGZ: logzre, 'L': d['lre']}
    lz2le = st([lz2, linarith(w, AL, [lzub, d['hL0']], '( 2 x. %s ) <_ L' % LOGZ,
                              leaves=LZV)], 'eqbrtrd', '%s <_ L' % LOGZ2)
    lz2ge = st([linarith(w, AL, [lzpos], '0 <_ ( 2 x. %s )' % LOGZ, leaves=LZV), lz2],
               'breqtrrd', '0 <_ %s' % LOGZ2)
    onez = st([st([], '1red', '1 e. RR'), lz2re], 'readdcld', '( 1 + %s ) e. RR' % LOGZ2)
    onel = st([st([], '1red', '1 e. RR'), d['lre']], 'readdcld', '( 1 + L ) e. RR')
    oz0 = linarith(w, AL, [lz2ge], '0 <_ ( 1 + %s )' % LOGZ2, leaves=LZV)
    ol0 = linarith(w, AL, [d['hL0']], '0 <_ ( 1 + L )', leaves=LV)
    sqa = st([st([st([onez, oz0], 'jca',
                     '( ( 1 + %s ) e. RR /\\ 0 <_ ( 1 + %s ) )' % (LOGZ2, LOGZ2)),
                  st([onel, ol0], 'jca', '( ( 1 + L ) e. RR /\\ 0 <_ ( 1 + L ) )'),
                  w.inst('le2sq')], 'syl2anc',
                 '( ( 1 + %s ) <_ ( 1 + L ) <-> ( ( 1 + %s ) ^ 2 ) <_ ( ( 1 + L ) ^ 2 ) )'
                 % (LOGZ2, LOGZ2)),
              linarith(w, AL, [lz2le], '( 1 + %s ) <_ ( 1 + L )' % LOGZ2, leaves=LZV)],
             'mpbid', '( ( 1 + %s ) ^ 2 ) <_ ( ( 1 + L ) ^ 2 )' % LOGZ2)
    sqb = st([st([st([zfre, zfge], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (ZZF, ZZF)),
                 st([d['eere'], d['eege']], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (EE, EE)),
                 w.inst('le2sq')], 'syl2anc',
                '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (ZZF, EE, ZZF, EE)), zfle],
             'mpbid', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (ZZF, EE))
    zf2re = st([zfre, d['n2']], 'reexpcld', '( %s ^ 2 ) e. RR' % ZZF)
    ee2re = st([d['eere'], d['n2']], 'reexpcld', '( %s ^ 2 ) e. RR' % EE)
    szre = st([onez, d['n2']], 'reexpcld', '( ( 1 + %s ) ^ 2 ) e. RR' % LOGZ2)
    slre = st([onel, d['n2']], 'reexpcld', '( ( 1 + L ) ^ 2 ) e. RR')
    zf2ge = st([zfre, d['n2'], zfge, w.inst('expge0')], 'syl3anc', '0 <_ ( %s ^ 2 )' % ZZF)
    ee2ge = st([d['eere'], d['n2'], d['eege'], w.inst('expge0')], 'syl3anc',
               '0 <_ ( %s ^ 2 )' % EE)
    szge = st([onez, d['n2'], oz0, w.inst('expge0')], 'syl3anc',
              '0 <_ ( ( 1 + %s ) ^ 2 )' % LOGZ2)
    prodle = st([st([st([st([zf2re, zf2ge], 'jca',
                            '( ( %s ^ 2 ) e. RR /\\ 0 <_ ( %s ^ 2 ) )' % (ZZF, ZZF)), ee2re],
                        'jca',
                        '( ( ( %s ^ 2 ) e. RR /\\ 0 <_ ( %s ^ 2 ) ) /\\ ( %s ^ 2 ) e. RR )'
                        % (ZZF, ZZF, EE)),
                    st([st([szre, szge], 'jca',
                           '( ( ( 1 + %s ) ^ 2 ) e. RR /\\ 0 <_ ( ( 1 + %s ) ^ 2 ) )'
                           % (LOGZ2, LOGZ2)), slre], 'jca',
                       '( ( ( ( 1 + %s ) ^ 2 ) e. RR /\\ 0 <_ ( ( 1 + %s ) ^ 2 ) ) /\\ ( ( 1 + L ) ^ 2 ) e. RR )'
                       % (LOGZ2, LOGZ2))], 'jca',
                   '( ( ( ( %s ^ 2 ) e. RR /\\ 0 <_ ( %s ^ 2 ) ) /\\ ( %s ^ 2 ) e. RR ) /\\ ( ( ( ( 1 + %s ) ^ 2 ) e. RR /\\ 0 <_ ( ( 1 + %s ) ^ 2 ) ) /\\ ( ( 1 + L ) ^ 2 ) e. RR ) )'
                   % (ZZF, ZZF, EE, LOGZ2, LOGZ2)), w.inst('lemul12a')], 'syl',
                '( ( ( %s ^ 2 ) <_ ( %s ^ 2 ) /\\ ( ( 1 + %s ) ^ 2 ) <_ ( ( 1 + L ) ^ 2 ) ) -> %s <_ %s )'
                % (ZZF, EE, LOGZ2, ETERM, ERB))
    prodle2 = st([prodle, sqb, sqa], 'mp2and', '%s <_ %s' % (ETERM, ERB))
    ee1 = linarith(w, AL, [zfle, z2le], '1 <_ %s' % EE,
                   leaves={EE: d['eere'], ZZF: zfre})
    esq = st([st([d['eere']], 'recnd', '%s e. CC' % EE)], 'sqvald',
             '( %s ^ 2 ) = ( %s x. %s )' % (EE, EE, EE))
    enl = nlinarith(w, AL, [ee1, d['eege']], '%s <_ ( %s x. %s )' % (EE, EE, EE),
                    leaves={EE: d['eere']})
    ele2 = st([enl, esq], 'breqtrrd', '%s <_ ( %s ^ 2 )' % (EE, EE))
    sl1 = st([st([st([st([], '1red', '1 e. RR'),
                      st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')], 'jca',
                     '( 1 e. RR /\\ 0 <_ 1 )'),
                  st([onel, ol0], 'jca', '( ( 1 + L ) e. RR /\\ 0 <_ ( 1 + L ) )'),
                  w.inst('le2sq')], 'syl2anc',
                 '( 1 <_ ( 1 + L ) <-> ( 1 ^ 2 ) <_ ( ( 1 + L ) ^ 2 ) )'),
              linarith(w, AL, [d['hL0']], '1 <_ ( 1 + L )', leaves=LV)], 'mpbid',
             '( 1 ^ 2 ) <_ ( ( 1 + L ) ^ 2 )')
    sl1b = st([st([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1'), sl1],
              'eqbrtrrd', '1 <_ ( ( 1 + L ) ^ 2 )')
    erbre = st([ee2re, slre], 'remulcld', '%s e. RR' % ERB)
    esqle = st([st([], '1red', '1 e. RR'), slre, ee2re, ee2ge, sl1b], 'lemul2ad',
               '( ( %s ^ 2 ) x. 1 ) <_ %s' % (EE, ERB))
    esqle2 = st([st([st([ee2re], 'recnd', '( %s ^ 2 ) e. CC' % EE)], 'mulridd',
                    '( ( %s ^ 2 ) x. 1 ) = ( %s ^ 2 )' % (EE, EE)), esqle], 'eqbrtrrd',
                '( %s ^ 2 ) <_ %s' % (EE, ERB))
    zferb = st([zfre, d['eere'], erbre, zfle,
                st([d['eere'], ee2re, erbre, ele2, esqle2], 'letrd', '%s <_ %s' % (EE, ERB))],
               'letrd', '%s <_ %s' % (ZZF, ERB))
    etre = st([zf2re, szre], 'remulcld', '%s e. RR' % ETERM)
    errsum = linarith(w, AL, [prodle2, zferb], '( %s + %s ) <_ ( 2 x. %s )' % (ETERM, ZZF, ERB),
                      leaves={ETERM: etre, ZZF: zfre, ERB: erbre}, atoms=[ETERM, ERB])
    poly = st([st([d['lre'], d['hL']], 'jca', AL), w.inst('poly4le')], 'syl',
              '( ( %s x. L ) x. ( ( 1 + L ) ^ 2 ) ) <_ ( exp ` ( L / 5 ) )' % C10)
    slrp = st([st([onel, linarith(w, AL, [d['hL0']], '0 < ( 1 + L )', leaves=LV)], 'elrpd',
                  '( 1 + L ) e. RR+'), d['z2']], 'rpexpcld', '( ( 1 + L ) ^ 2 ) e. RR+')
    l5re = st([d['lre'], st([num.re_nat(w, 5)], 'a1i', '5 e. RR'),
               st([num.fact(w, '5', 'ne0')], 'a1i', '5 =/= 0')], 'redivcld',
              '( L / 5 ) e. RR')
    ef5rp = st([l5re, w.inst('rpefcl')], 'syl', '( exp ` ( L / 5 ) ) e. RR+')
    ee2rp = st([d['eerp'], d['z2']], 'rpexpcld', '( %s ^ 2 ) e. RR+' % EE)
    eid = st([st([st([st([slrp, d['lrp']], 'jca',
                        '( ( ( 1 + L ) ^ 2 ) e. RR+ /\\ L e. RR+ )'),
                    st([ef5rp, ee2rp], 'jca',
                       '( ( exp ` ( L / 5 ) ) e. RR+ /\\ ( %s ^ 2 ) e. RR+ )' % EE)], 'jca',
                   '( ( ( ( 1 + L ) ^ 2 ) e. RR+ /\\ L e. RR+ ) /\\ ( ( exp ` ( L / 5 ) ) e. RR+ /\\ ( %s ^ 2 ) e. RR+ ) )'
                   % EE), poly], 'jca',
                 '( ( ( ( ( 1 + L ) ^ 2 ) e. RR+ /\\ L e. RR+ ) /\\ ( ( exp ` ( L / 5 ) ) e. RR+ /\\ ( %s ^ 2 ) e. RR+ ) ) /\\ ( ( %s x. L ) x. ( ( 1 + L ) ^ 2 ) ) <_ ( exp ` ( L / 5 ) ) )'
                 % (EE, C10)), w.inst('errid')], 'syl',
             '( 2 x. %s ) <_ ( ( 1 / 5 ) x. ( ( ( %s ^ 2 ) x. ( exp ` ( L / 5 ) ) ) / L ) )'
             % (ERB, EE))
    A1 = '( 2 x. ( ( 2 / 5 ) x. L ) )'
    A2 = '( L / 5 )'
    a1re = st([d['re2'], d['e25re']], 'remulcld', '%s e. RR' % A1)
    efx = st([st([d['e25re']], 'recnd', '( ( 2 / 5 ) x. L ) e. CC'), d['z2'],
              w.inst('efexp')], 'syl2anc',
             '( exp ` %s ) = ( %s ^ 2 )' % (A1, EE))
    efa = st([st([a1re], 'recnd', '%s e. CC' % A1), st([l5re], 'recnd', '%s e. CC' % A2),
              w.inst('efadd')], 'syl2anc',
             '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (A1, A2, A1, A2))
    lid = lineq(w, AL, '( %s + %s )' % (A1, A2), 'L', leaves=dict(LV))
    nmid = st([st([st([lid], 'fveq2d', '( exp ` ( %s + %s ) ) = ( exp ` L )' % (A1, A2))],
                  'eqcomd', '( exp ` L ) = ( exp ` ( %s + %s ) )' % (A1, A2)),
               st([efa, st([efx], 'oveq1d',
                           '( ( exp ` %s ) x. ( exp ` %s ) ) = ( ( %s ^ 2 ) x. ( exp ` %s ) )'
                           % (A1, A2, EE, A2))], 'eqtrd',
                  '( exp ` ( %s + %s ) ) = ( ( %s ^ 2 ) x. ( exp ` %s ) )' % (A1, A2, EE, A2))],
              'eqtrd', '( exp ` L ) = ( ( %s ^ 2 ) x. ( exp ` %s ) )' % (EE, A2))
    eid2 = st([eid, st([st([st([nmid], 'eqcomd',
                               '( ( %s ^ 2 ) x. ( exp ` %s ) ) = ( exp ` L )' % (EE, A2))],
                           'oveq1d',
                           '( ( ( %s ^ 2 ) x. ( exp ` %s ) ) / L ) = ( ( exp ` L ) / L )'
                           % (EE, A2))], 'oveq2d',
                       '( ( 1 / 5 ) x. ( ( ( %s ^ 2 ) x. ( exp ` %s ) ) / L ) ) = ( ( 1 / 5 ) x. ( ( exp ` L ) / L ) )'
                       % (EE, A2))], 'breqtrd',
              '( 2 x. %s ) <_ ( ( 1 / 5 ) x. ( ( exp ` L ) / L ) )' % ERB)
    rhsre = st([st([num.real(w, '( 1 / 5 )')], 'a1i', '( 1 / 5 ) e. RR'),
                st([st([d['lre']], 'reefcld', '( exp ` L ) e. RR'), d['lre'],
                    st([d['lrp']], 'rpne0d', 'L =/= 0')], 'redivcld',
                   '( ( exp ` L ) / L ) e. RR')], 'remulcld',
               '( ( 1 / 5 ) x. ( ( exp ` L ) / L ) ) e. RR')
    w.qed([st([etre, zfre], 'readdcld', '( %s + %s ) e. RR' % (ETERM, ZZF)),
           st([d['re2'], erbre], 'remulcld', '( 2 x. %s ) e. RR' % ERB), rhsre,
           errsum, eid2], 'letrd', '( %s -> %s )' % (AL, EGOAL))
    return w


def main(names=None):
    fns = {'btlev': btlev, 'bterr': bterr}
    ok = True
    for nm in (names or ['btlev', 'bterr']):
        ok = fns[nm]().run() and ok
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1:] or None) else 1)
