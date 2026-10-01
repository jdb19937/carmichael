"""Sortie v4a: the arithmetic of the twin-type sieve assembly."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import mkst
from cl import lift
from lin import nlinarith
import num

LT = '( log ` T )'
LTS = '( %s ^ 2 )' % LT
PH = '( ( phi ` M ) / M )'
PHS = '( %s ^ 2 )' % PH
RR_ = '( M / ( phi ` M ) )'
RSQ = '( %s ^ 2 )' % RR_
XX = '( %s x. %s )' % (PHS, LTS)
QT = '( T / S )'
C1 = '; ; ; ; ; ; 4 1 9 4 3 0 4'
C2 = '; ; ; ; ; ; 4 1 9 4 4 3 2'
K2048 = '; ; ; 2 0 4 8'
AA = ('( ( M e. NN /\\ T e. NN0 /\\ 2 <_ T ) /\\ '
      '( ( C e. RR /\\ S e. RR /\\ 0 < S ) /\\ '
      '( E e. RR /\\ G e. RR /\\ 0 <_ G ) /\\ ( Q e. RR /\\ 0 <_ Q ) ) /\\ '
      '( ( C <_ ( %s + E ) /\\ E <_ ( 2 x. Q ) ) /\\ '
      '( ( G ^ 2 ) <_ S /\\ ( %s x. %s ) <_ ( %s x. G ) ) /\\ '
      '( %s <_ ( ; 6 4 x. Q ) /\\ ( Q ^ 2 ) <_ T ) ) )'
      % (QT, PH, LT, K2048, LTS))


def twinarc():
    w = WS('twinarc', 'The arithmetic of the twin-type sieve assembly: the sieve bound, the '
                      'error bound and the bounding-sum lower bound combine into the '
                      'explicit upper bound.')
    st = mkst(w, AA)
    b1 = st([], 'simp1', '( M e. NN /\\ T e. NN0 /\\ 2 <_ T )')
    b2 = st([], 'simp2',
            '( ( C e. RR /\\ S e. RR /\\ 0 < S ) /\\ '
            '( E e. RR /\\ G e. RR /\\ 0 <_ G ) /\\ ( Q e. RR /\\ 0 <_ Q ) )')
    b3 = st([], 'simp3',
            '( ( C <_ ( %s + E ) /\\ E <_ ( 2 x. Q ) ) /\\ '
            '( ( G ^ 2 ) <_ S /\\ ( %s x. %s ) <_ ( %s x. G ) ) /\\ '
            '( %s <_ ( ; 6 4 x. Q ) /\\ ( Q ^ 2 ) <_ T ) )'
            % (QT, PH, LT, K2048, LTS))
    mnn = st([b1], 'simp1d', 'M e. NN')
    tn0 = st([b1], 'simp2d', 'T e. NN0')
    tge2 = st([b1], 'simp3d', '2 <_ T')
    p1 = st([b2], 'simp1d', '( C e. RR /\\ S e. RR /\\ 0 < S )')
    p2 = st([b2], 'simp2d', '( E e. RR /\\ G e. RR /\\ 0 <_ G )')
    p3 = st([b2], 'simp3d', '( Q e. RR /\\ 0 <_ Q )')
    cre = st([p1], 'simp1d', 'C e. RR')
    sre = st([p1], 'simp2d', 'S e. RR')
    spos = st([p1], 'simp3d', '0 < S')
    ere = st([p2], 'simp1d', 'E e. RR')
    gre = st([p2], 'simp2d', 'G e. RR')
    gge = st([p2], 'simp3d', '0 <_ G')
    qre = st([p3], 'simpld', 'Q e. RR')
    qge = st([p3], 'simprd', '0 <_ Q')
    h1 = st([st([b3], 'simp1d', '( C <_ ( %s + E ) /\\ E <_ ( 2 x. Q ) )' % QT)], 'simpld',
            'C <_ ( %s + E )' % QT)
    h2 = st([st([b3], 'simp1d', '( C <_ ( %s + E ) /\\ E <_ ( 2 x. Q ) )' % QT)], 'simprd',
            'E <_ ( 2 x. Q )')
    h3 = st([st([b3], 'simp2d',
                '( ( G ^ 2 ) <_ S /\\ ( %s x. %s ) <_ ( %s x. G ) )' % (PH, LT, K2048))],
            'simpld', '( G ^ 2 ) <_ S')
    h4 = st([st([b3], 'simp2d',
                '( ( G ^ 2 ) <_ S /\\ ( %s x. %s ) <_ ( %s x. G ) )' % (PH, LT, K2048))],
            'simprd', '( %s x. %s ) <_ ( %s x. G )' % (PH, LT, K2048))
    h5 = st([st([b3], 'simp3d',
                '( %s <_ ( ; 6 4 x. Q ) /\\ ( Q ^ 2 ) <_ T )' % LTS)], 'simpld',
            '%s <_ ( ; 6 4 x. Q )' % LTS)
    h6 = st([st([b3], 'simp3d',
                '( %s <_ ( ; 6 4 x. Q ) /\\ ( Q ^ 2 ) <_ T )' % LTS)], 'simprd',
            '( Q ^ 2 ) <_ T')
    # basic closures
    two0 = st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    twoz = st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    tre = st([tn0], 'nn0red', 'T e. RR')
    tge0 = st([tn0], 'nn0ge0d', '0 <_ T')
    tge1 = st([st([], '1red', '1 e. RR'), st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
               tre, st([w.s([], '1le2', '1 <_ 2')], 'a1i', '1 <_ 2'), tge2], 'letrd', '1 <_ T')
    tgt1 = st([st([], '1red', '1 e. RR'), st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'),
               tre, st([w.s([], '1lt2', '1 < 2')], 'a1i', '1 < 2'), tge2], 'ltletrd', '1 < T')
    tpos = st([st([], '0red', '0 e. RR'), st([], '1red', '1 e. RR'), tre,
               st([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1'), tgt1], 'lttrd', '0 < T')
    trp = st([tre, tpos], 'elrpd', 'T e. RR+')
    ltre = st([trp, w.inst('relogcl')], 'syl', '%s e. RR' % LT)
    ltpos = st([st([tre, tgt1], 'jca', '( T e. RR /\\ 1 < T )'), w.inst('rplogcl')], 'syl',
               '%s e. RR+' % LT)
    ltsrp = st([ltpos, twoz], 'rpexpcld', '%s e. RR+' % LTS)
    ltsre = st([ltsrp], 'rpred', '%s e. RR' % LTS)
    ltspos = st([ltsrp], 'rpgt0d', '0 < %s' % LTS)
    ltsge = st([ltsrp], 'rpge0d', '0 <_ %s' % LTS)
    ltge = st([st([tre, tge1], 'jca', '( T e. RR /\\ 1 <_ T )'), w.inst('logge0')], 'syl',
              '0 <_ %s' % LT)
    phinn = st([mnn, w.inst('phicl')], 'syl', '( phi ` M ) e. NN')
    phirp = st([phinn], 'nnrpd', '( phi ` M ) e. RR+')
    mrp = st([mnn], 'nnrpd', 'M e. RR+')
    phrp = st([phirp, mrp], 'rpdivcld', '%s e. RR+' % PH)
    phre = st([phrp], 'rpred', '%s e. RR' % PH)
    phge = st([phrp], 'rpge0d', '0 <_ %s' % PH)
    phile = st([st([mnn, w.inst('phicl2')], 'syl', '( phi ` M ) e. ( 1 ... M )'),
                w.inst('elfzle2')], 'syl', '( phi ` M ) <_ M')
    phle1 = st([st([st([phinn], 'nnred', '( phi ` M ) e. RR'), mrp, w.inst('ledivmul2')],
                   'syl2anc', 'z')], 'id', 'z')
    w.lines.pop(); w.lines.pop()
    phle1 = st([phile, st([st([phinn], 'nnred', '( phi ` M ) e. RR'), mrp,
                           w.inst('divle1le')], 'syl2anc',
                          '( %s <_ 1 <-> ( phi ` M ) <_ M )' % PH)], 'mpbird', '%s <_ 1' % PH)
    # ---- PHS x. LTS <_ C1 x. S
    phlt = st([phre, ltre], 'remulcld', '( %s x. %s ) e. RR' % (PH, LT))
    phltge = st([phre, ltre, phge, ltge], 'mulge0d', '0 <_ ( %s x. %s )' % (PH, LT))
    k2re = st([num.fact(w, K2048, 'RR')], 'a1i', '%s e. RR' % K2048)
    k2ge = st([num.fact(w, K2048, 'ge0')], 'a1i', '0 <_ %s' % K2048)
    kgre = st([k2re, gre], 'remulcld', '( %s x. G ) e. RR' % K2048)
    sq1 = st([st([st([phlt, phltge], 'jca',
                     '( ( %s x. %s ) e. RR /\ 0 <_ ( %s x. %s ) )' % (PH, LT, PH, LT)),
                  st([kgre, h4], 'jca',
                     '( ( %s x. G ) e. RR /\ ( %s x. %s ) <_ ( %s x. G ) )'
                     % (K2048, PH, LT, K2048))], 'jca',
                 '( ( ( %s x. %s ) e. RR /\ 0 <_ ( %s x. %s ) ) /\ '
                 '( ( %s x. G ) e. RR /\ ( %s x. %s ) <_ ( %s x. G ) ) )'
                 % (PH, LT, PH, LT, K2048, PH, LT, K2048)), w.inst('le2sq2')], 'syl',
             '( ( %s x. %s ) ^ 2 ) <_ ( ( %s x. G ) ^ 2 )' % (PH, LT, K2048))
    ml = st([st([phre], 'recnd', '%s e. CC' % PH), st([ltre], 'recnd', '%s e. CC' % LT),
             two0, w.inst('mulexp')], 'syl3anc',
            '( ( %s x. %s ) ^ 2 ) = %s' % (PH, LT, XX))
    mr = st([st([k2re], 'recnd', '%s e. CC' % K2048), st([gre], 'recnd', 'G e. CC'), two0,
             w.inst('mulexp')], 'syl3anc',
            '( ( %s x. G ) ^ 2 ) = ( ( %s ^ 2 ) x. ( G ^ 2 ) )' % (K2048, K2048))
    ksq = st([st([st([k2re], 'recnd', '%s e. CC' % K2048), w.inst('sqval')], 'syl',
                 '( %s ^ 2 ) = ( %s x. %s )' % (K2048, K2048, K2048)),
              st([num.mul_nat(w, 2048, 2048)], 'a1i',
                 '( %s x. %s ) = %s' % (K2048, K2048, C1))], 'eqtrd',
             '( %s ^ 2 ) = %s' % (K2048, C1))
    mr2 = st([mr, st([ksq], 'oveq1d',
                     '( ( %s ^ 2 ) x. ( G ^ 2 ) ) = ( %s x. ( G ^ 2 ) )' % (K2048, C1))],
             'eqtrd', '( ( %s x. G ) ^ 2 ) = ( %s x. ( G ^ 2 ) )' % (K2048, C1))
    c1re = st([num.fact(w, C1, 'RR')], 'a1i', '%s e. RR' % C1)
    c1ge = st([num.fact(w, C1, 'ge0')], 'a1i', '0 <_ %s' % C1)
    gsqre = st([gre, two0], 'reexpcld', '( G ^ 2 ) e. RR')
    m1 = st([st([st([gsqre, sre, st([c1re, c1ge], 'jca',
                                    '( %s e. RR /\ 0 <_ %s )' % (C1, C1))], '3jca',
                    '( ( G ^ 2 ) e. RR /\ S e. RR /\ ( %s e. RR /\ 0 <_ %s ) )' % (C1, C1)),
                 h3], 'jca',
                '( ( ( G ^ 2 ) e. RR /\ S e. RR /\ ( %s e. RR /\ 0 <_ %s ) ) /\ '
                '( G ^ 2 ) <_ S )' % (C1, C1)), w.inst('lemul2a')], 'syl',
            '( %s x. ( G ^ 2 ) ) <_ ( %s x. S )' % (C1, C1))
    xre = st([st([phre, two0], 'reexpcld', '%s e. RR' % PHS), ltsre], 'remulcld',
             '%s e. RR' % XX)
    key1 = st([xre, st([c1re, gsqre], 'remulcld', '( %s x. ( G ^ 2 ) ) e. RR' % C1),
               st([c1re, sre], 'remulcld', '( %s x. S ) e. RR' % C1),
               st([st([ml], 'eqcomd', '%s = ( ( %s x. %s ) ^ 2 )' % (XX, PH, LT)),
                   st([sq1, mr2], 'breqtrd',
                      '( ( %s x. %s ) ^ 2 ) <_ ( %s x. ( G ^ 2 ) )' % (PH, LT, C1))],
                  'eqbrtrd', '%s <_ ( %s x. ( G ^ 2 ) )' % (XX, C1)), m1], 'letrd',
              '%s <_ ( %s x. S )' % (XX, C1))
    # ---- ( T / S ) x. XX <_ C1 x. T
    srp = st([sre, spos], 'elrpd', 'S e. RR+')
    qtre = st([tre, srp], 'rerpdivcld', '%s e. RR' % QT)
    qtge = st([tre, srp, tge0], 'divge0d', '0 <_ %s' % QT)
    m2 = st([st([st([xre, st([c1re, sre], 'remulcld', '( %s x. S ) e. RR' % C1),
                     st([qtre, qtge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (QT, QT))], '3jca',
                    '( %s e. RR /\ ( %s x. S ) e. RR /\ ( %s e. RR /\ 0 <_ %s ) )'
                    % (XX, C1, QT, QT)), key1], 'jca',
                 '( ( %s e. RR /\ ( %s x. S ) e. RR /\ ( %s e. RR /\ 0 <_ %s ) ) /\ '
                 '%s <_ ( %s x. S ) )' % (XX, C1, QT, QT, XX, C1)), w.inst('lemul2a')], 'syl',
            '( %s x. %s ) <_ ( %s x. ( %s x. S ) )' % (QT, XX, QT, C1))
    canc = st([st([tre], 'recnd', 'T e. CC'), st([sre], 'recnd', 'S e. CC'),
               st([srp], 'rpne0d', 'S =/= 0'), w.inst('divcan1')], 'syl3anc',
              '( %s x. S ) = T' % QT)
    m12 = st([st([qtre], 'recnd', '%s e. CC' % QT), st([c1re], 'recnd', '%s e. CC' % C1),
              st([sre], 'recnd', 'S e. CC')], 'mul12d',
             '( %s x. ( %s x. S ) ) = ( %s x. ( %s x. S ) )' % (QT, C1, C1, QT))
    key2 = st([m2, st([m12, st([canc], 'oveq2d',
                               '( %s x. ( %s x. S ) ) = ( %s x. T )' % (C1, QT, C1))],
                      'eqtrd', '( %s x. ( %s x. S ) ) = ( %s x. T )' % (QT, C1, C1))],
              'breqtrd', '( %s x. %s ) <_ ( %s x. T )' % (QT, XX, C1))
    # ---- ( ( 2 x. Q ) x. LTS ) <_ ( ; ; 1 2 8 x. T )
    qq = st([st([qre], 'recnd', 'Q e. CC')], 'sqvald', '( Q ^ 2 ) = ( Q x. Q )')
    qqT = st([st([qq], 'eqcomd', '( Q x. Q ) = ( Q ^ 2 )'), h6], 'eqbrtrd', '( Q x. Q ) <_ T')
    k128 = '; ; 1 2 8'
    s64 = st([num.fact(w, '; 6 4', 'RR')], 'a1i', '; 6 4 e. RR')
    nl = nlinarith(w, AA, [h5, qqT, qge, ltsge],
                   '( ( 2 x. Q ) x. %s ) <_ ( %s x. T )' % (LTS, k128),
                   leaves={'Q': qre, LTS: ltsre, 'T': tre})
    # ---- ( ( 2 x. Q ) x. XX ) <_ ( ( 2 x. Q ) x. LTS )
    phsre = st([phre, two0], 'reexpcld', '%s e. RR' % PHS)
    phsge = st([phre, phge, two0], 'expge0d', '0 <_ %s' % PHS)
    onere = st([], '1red', '1 e. RR')
    phsle = st([st([st([phre, phge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (PH, PH)),
                     st([onere, phle1], 'jca', '( 1 e. RR /\ %s <_ 1 )' % PH)], 'jca',
                    '( ( %s e. RR /\ 0 <_ %s ) /\ ( 1 e. RR /\ %s <_ 1 ) )' % (PH, PH, PH)),
                 w.inst('le2sq2')], 'syl', '%s <_ ( 1 ^ 2 )' % PHS)
    sq1e = st([st([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1')], 'id', 'z')
    w.lines.pop()
    sq1e = st([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( 1 ^ 2 ) = 1')
    phsle1 = st([phsle, sq1e], 'breqtrd', '%s <_ 1' % PHS)
    twoq = '( 2 x. Q )'
    twore = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    tqre = st([twore, qre], 'remulcld', '%s e. RR' % twoq)
    tqge = st([twore, qre, st([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), qge], 'mulge0d',
              '0 <_ %s' % twoq)
    tqlre = st([tqre, ltsre], 'remulcld', '( %s x. %s ) e. RR' % (twoq, LTS))
    tqlge = st([tqre, ltsre, tqge, ltsge], 'mulge0d', '0 <_ ( %s x. %s )' % (twoq, LTS))
    m12b = st([st([tqre], 'recnd', '%s e. CC' % twoq), st([phsre], 'recnd', '%s e. CC' % PHS),
               st([ltsre], 'recnd', '%s e. CC' % LTS)], 'mul12d',
              '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (twoq, XX, PHS, twoq, LTS))
    lem = st([st([st([phsre, onere, st([tqlre, tqlge], 'jca',
                                       '( ( %s x. %s ) e. RR /\ 0 <_ ( %s x. %s ) )'
                                       % (twoq, LTS, twoq, LTS))], '3jca',
                      '( %s e. RR /\ 1 e. RR /\ ( ( %s x. %s ) e. RR /\ '
                      '0 <_ ( %s x. %s ) ) )' % (PHS, twoq, LTS, twoq, LTS)), phsle1], 'jca',
                  '( ( %s e. RR /\ 1 e. RR /\ ( ( %s x. %s ) e. RR /\ '
                  '0 <_ ( %s x. %s ) ) ) /\ %s <_ 1 )'
                  % (PHS, twoq, LTS, twoq, LTS, PHS)), w.inst('lemul1a')], 'syl',
             '( %s x. ( %s x. %s ) ) <_ ( 1 x. ( %s x. %s ) )' % (PHS, twoq, LTS, twoq, LTS))
    lem2 = st([lem, st([st([tqlre], 'recnd', '( %s x. %s ) e. CC' % (twoq, LTS))], 'mullidd',
                       '( 1 x. ( %s x. %s ) ) = ( %s x. %s )' % (twoq, LTS, twoq, LTS))],
              'breqtrd', '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (PHS, twoq, LTS, twoq, LTS))
    key3 = st([m12b, lem2], 'eqbrtrd', '( %s x. %s ) <_ ( %s x. %s )' % (twoq, XX, twoq, LTS))
    k128re = st([num.fact(w, k128, 'RR')], 'a1i', '%s e. RR' % k128)
    key4 = st([st([tqre, xre], 'remulcld', '( %s x. %s ) e. RR' % (twoq, XX)), tqlre,
               st([k128re, tre], 'remulcld', '( %s x. T ) e. RR' % k128), key3, nl], 'letrd',
              '( %s x. %s ) <_ ( %s x. T )' % (twoq, XX, k128))
    # ---- put the two halves together
    xge = st([phsre, ltsre, phsge, ltsge], 'mulge0d', '0 <_ %s' % XX)
    qere = st([qtre, ere], 'readdcld', '( %s + E ) e. RR' % QT)
    ml1 = st([st([st([cre, qere, st([xre, xge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (XX, XX))],
                     '3jca',
                     '( C e. RR /\ ( %s + E ) e. RR /\ ( %s e. RR /\ 0 <_ %s ) )'
                     % (QT, XX, XX)), h1], 'jca',
                  '( ( C e. RR /\ ( %s + E ) e. RR /\ ( %s e. RR /\ 0 <_ %s ) ) /\ '
                  'C <_ ( %s + E ) )' % (QT, XX, XX, QT)), w.inst('lemul1a')], 'syl',
              '( C x. %s ) <_ ( ( %s + E ) x. %s )' % (XX, QT, XX))
    dist = st([st([qtre], 'recnd', '%s e. CC' % QT), st([ere], 'recnd', 'E e. CC'),
               st([xre], 'recnd', '%s e. CC' % XX)], 'adddird',
              '( ( %s + E ) x. %s ) = ( ( %s x. %s ) + ( E x. %s ) )' % (QT, XX, QT, XX, XX))
    ml2 = st([st([st([ere, tqre, st([xre, xge], 'jca', '( %s e. RR /\ 0 <_ %s )' % (XX, XX))],
                     '3jca',
                     '( E e. RR /\ %s e. RR /\ ( %s e. RR /\ 0 <_ %s ) )' % (twoq, XX, XX)),
                  h2], 'jca',
                 '( ( E e. RR /\ %s e. RR /\ ( %s e. RR /\ 0 <_ %s ) ) /\ E <_ %s )'
                 % (twoq, XX, XX, twoq)), w.inst('lemul1a')], 'syl',
              '( E x. %s ) <_ ( %s x. %s )' % (XX, twoq, XX))
    sum1 = st([st([qtre, xre], 'remulcld', '( %s x. %s ) e. RR' % (QT, XX)),
               st([c1re, tre], 'remulcld', '( %s x. T ) e. RR' % C1),
               st([ere, xre], 'remulcld', '( E x. %s ) e. RR' % XX),
               st([k128re, tre], 'remulcld', '( %s x. T ) e. RR' % k128), key2,
               st([st([ere, xre], 'remulcld', '( E x. %s ) e. RR' % XX),
                   st([tqre, xre], 'remulcld', '( %s x. %s ) e. RR' % (twoq, XX)),
                   st([k128re, tre], 'remulcld', '( %s x. T ) e. RR' % k128), ml2, key4],
                  'letrd', '( E x. %s ) <_ ( %s x. T )' % (XX, k128))], 'le2addd',
              '( ( %s x. %s ) + ( E x. %s ) ) <_ ( ( %s x. T ) + ( %s x. T ) )'
              % (QT, XX, XX, C1, k128))
    addc = st([st([c1re], 'recnd', '%s e. CC' % C1), st([k128re], 'recnd', '%s e. CC' % k128),
               st([tre], 'recnd', 'T e. CC')], 'adddird',
              '( ( %s + %s ) x. T ) = ( ( %s x. T ) + ( %s x. T ) )' % (C1, k128, C1, k128))
    c2eq = st([st([num.add_nat(w, 4194304, 128)], 'a1i',
                  '( %s + %s ) = %s' % (C1, k128, C2))], 'oveq1d',
              '( ( %s + %s ) x. T ) = ( %s x. T )' % (C1, k128, C2))
    sumc = st([st([addc], 'eqcomd',
                  '( ( %s x. T ) + ( %s x. T ) ) = ( ( %s + %s ) x. T )'
                  % (C1, k128, C1, k128)), c2eq], 'eqtrd',
              '( ( %s x. T ) + ( %s x. T ) ) = ( %s x. T )' % (C1, k128, C2))
    c2re = st([num.fact(w, C2, 'RR')], 'a1i', '%s e. RR' % C2)
    main = st([st([cre, xre], 'remulcld', '( C x. %s ) e. RR' % XX),
               st([qere, xre], 'remulcld', '( ( %s + E ) x. %s ) e. RR' % (QT, XX)),
               st([c2re, tre], 'remulcld', '( %s x. T ) e. RR' % C2), ml1,
               st([st([dist, sum1], 'eqbrtrd',
                      '( ( %s + E ) x. %s ) <_ ( ( %s x. T ) + ( %s x. T ) )'
                      % (QT, XX, C1, k128)), sumc], 'breqtrd',
                  '( ( %s + E ) x. %s ) <_ ( %s x. T )' % (QT, XX, C2))], 'letrd',
              '( C x. %s ) <_ ( %s x. T )' % (XX, C2))
    # ---- divide out
    resh = st([st([st([cre], 'recnd', 'C e. CC'), st([phsre], 'recnd', '%s e. CC' % PHS),
                   st([ltsre], 'recnd', '%s e. CC' % LTS)], 'mul12d',
                  '( C x. %s ) = ( %s x. ( C x. %s ) )' % (XX, PHS, LTS)),
               st([st([phsre], 'recnd', '%s e. CC' % PHS),
                   st([st([cre, ltsre], 'remulcld', '( C x. %s ) e. RR' % LTS)], 'recnd',
                      '( C x. %s ) e. CC' % LTS)], 'mulcomd',
                  '( %s x. ( C x. %s ) ) = ( ( C x. %s ) x. %s )' % (PHS, LTS, LTS, PHS))],
              'eqtrd', '( C x. %s ) = ( ( C x. %s ) x. %s )' % (XX, LTS, PHS))
    phspos = st([phrp, twoz], 'rpexpcld', '%s e. RR+' % PHS)
    div1 = st([st([st([cre, ltsre], 'remulcld', '( C x. %s ) e. RR' % LTS),
                   st([c2re, tre], 'remulcld', '( %s x. T ) e. RR' % C2),
                   st([phsre, st([phspos], 'rpgt0d', '0 < %s' % PHS)], 'jca',
                      '( %s e. RR /\ 0 < %s )' % (PHS, PHS))], '3jca',
                  '( ( C x. %s ) e. RR /\ ( %s x. T ) e. RR /\ '
                  '( %s e. RR /\ 0 < %s ) )' % (LTS, C2, PHS, PHS)), w.inst('lemuldiv')],
               'syl',
               '( ( ( C x. %s ) x. %s ) <_ ( %s x. T ) <-> '
               '( C x. %s ) <_ ( ( %s x. T ) / %s ) )' % (LTS, PHS, C2, LTS, C2, PHS))
    div2 = st([div1, st([st([resh], 'eqcomd',
                            '( ( C x. %s ) x. %s ) = ( C x. %s )' % (LTS, PHS, XX)), main],
                        'eqbrtrd',
                        '( ( C x. %s ) x. %s ) <_ ( %s x. T )' % (LTS, PHS, C2))], 'mpbid',
              '( C x. %s ) <_ ( ( %s x. T ) / %s )' % (LTS, C2, PHS))
    # ( 1 / PHS ) = RSQ
    recp = st([st([st([phirp], 'rpcnd', '( phi ` M ) e. CC'),
                   st([phirp], 'rpne0d', '( phi ` M ) =/= 0')], 'jca',
                  '( ( phi ` M ) e. CC /\ ( phi ` M ) =/= 0 )'),
               st([st([mrp], 'rpcnd', 'M e. CC'), st([mrp], 'rpne0d', 'M =/= 0')], 'jca',
                  '( M e. CC /\ M =/= 0 )'), w.inst('recdiv')], 'syl2anc',
              '( 1 / %s ) = %s' % (PH, RR_))
    edv = st([st([st([], '1red', '1 e. RR')], 'recnd', '1 e. CC'),
              st([st([phrp], 'rpcnd', '%s e. CC' % PH), st([phrp], 'rpne0d', '%s =/= 0' % PH)],
                 'jca', '( %s e. CC /\ %s =/= 0 )' % (PH, PH)), two0, w.inst('expdiv')],
             'syl3anc', '( ( 1 / %s ) ^ 2 ) = ( ( 1 ^ 2 ) / %s )' % (PH, PHS))
    rsqeq = st([st([st([recp], 'eqcomd', '%s = ( 1 / %s )' % (RR_, PH))], 'oveq1d',
                   '%s = ( ( 1 / %s ) ^ 2 )' % (RSQ, PH)),
                st([edv, st([sq1e], 'oveq1d',
                            '( ( 1 ^ 2 ) / %s ) = ( 1 / %s )' % (PHS, PHS))], 'eqtrd',
                   '( ( 1 / %s ) ^ 2 ) = ( 1 / %s )' % (PH, PHS))], 'eqtrd',
               '%s = ( 1 / %s )' % (RSQ, PHS))
    dr = st([st([st([c2re, tre], 'remulcld', '( %s x. T ) e. RR' % C2)], 'recnd',
                '( %s x. T ) e. CC' % C2),
             st([phspos], 'rpcnd', '%s e. CC' % PHS), st([phspos], 'rpne0d', '%s =/= 0' % PHS),
             w.inst('divrec')], 'syl3anc',
            '( ( %s x. T ) / %s ) = ( ( %s x. T ) x. ( 1 / %s ) )' % (C2, PHS, C2, PHS))
    dr2 = st([dr, st([st([rsqeq], 'eqcomd', '( 1 / %s ) = %s' % (PHS, RSQ))], 'oveq2d',
                     '( ( %s x. T ) x. ( 1 / %s ) ) = ( ( %s x. T ) x. %s )'
                     % (C2, PHS, C2, RSQ))], 'eqtrd',
              '( ( %s x. T ) / %s ) = ( ( %s x. T ) x. %s )' % (C2, PHS, C2, RSQ))
    rsqre = st([st([mrp, phirp], 'rpdivcld', '%s e. RR+' % RR_), twoz], 'rpexpcld',
               '%s e. RR+' % RSQ)
    m32 = st([st([c2re], 'recnd', '%s e. CC' % C2), st([tre], 'recnd', 'T e. CC'),
              st([st([rsqre], 'rpred', '%s e. RR' % RSQ)], 'recnd', '%s e. CC' % RSQ)],
             'mul32d',
             '( ( %s x. T ) x. %s ) = ( ( %s x. %s ) x. T )' % (C2, RSQ, C2, RSQ))
    fin1 = st([div2, st([dr2, m32], 'eqtrd',
                        '( ( %s x. T ) / %s ) = ( ( %s x. %s ) x. T )'
                        % (C2, PHS, C2, RSQ))], 'breqtrd',
              '( C x. %s ) <_ ( ( %s x. %s ) x. T )' % (LTS, C2, RSQ))
    fin2 = st([st([cre, st([st([c2re, st([rsqre], 'rpred', '%s e. RR' % RSQ)], 'remulcld',
                               '( %s x. %s ) e. RR' % (C2, RSQ)), tre], 'remulcld',
                           '( ( %s x. %s ) x. T ) e. RR' % (C2, RSQ)),
                   st([ltsre, ltspos], 'jca', '( %s e. RR /\ 0 < %s )' % (LTS, LTS))], '3jca',
                  '( C e. RR /\ ( ( %s x. %s ) x. T ) e. RR /\ '
                  '( %s e. RR /\ 0 < %s ) )' % (C2, RSQ, LTS, LTS)), w.inst('lemuldiv')],
              'syl',
              '( ( C x. %s ) <_ ( ( %s x. %s ) x. T ) <-> '
              'C <_ ( ( ( %s x. %s ) x. T ) / %s ) )' % (LTS, C2, RSQ, C2, RSQ, LTS))
    w.qed([fin2, fin1], 'mpbid',
          '( %s -> C <_ ( ( ( %s x. %s ) x. T ) / %s ) )' % (AA, C2, RSQ, LTS))
    return w


ALL = {'twinarc': twinarc}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
