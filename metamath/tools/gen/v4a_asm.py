"""Sortie v4a: the iterated integer square root and the final assembly."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import mkst
from cl import lift
import num


def FL(X):
    return '( |_ ` ( sqrt ` %s ) )' % X


AG = '( A e. RR /\\ B e. NN0 /\\ ( B ^ 2 ) <_ A )'


def flsqge():
    w = WS('flsqge', 'A nonnegative integer whose square is at most a real is at most the '
                     'integer square root of that real.')
    st = mkst(w, AG)
    are = st([], 'simp1', 'A e. RR')
    bn0 = st([], 'simp2', 'B e. NN0')
    bsq = st([], 'simp3', '( B ^ 2 ) <_ A')
    bre = st([bn0], 'nn0red', 'B e. RR')
    bge = st([bn0], 'nn0ge0d', '0 <_ B')
    bsqre = st([bre, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'reexpcld',
               '( B ^ 2 ) e. RR')
    bsqge = st([bre, bge, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'expge0d',
               '0 <_ ( B ^ 2 )')
    age = st([st([], '0red', '0 e. RR'), bsqre, are, bsqge, bsq], 'letrd', '0 <_ A')
    aa = st([are, age], 'jca', '( A e. RR /\\ 0 <_ A )')
    sre = st([aa, w.inst('resqrtcl')], 'syl', '( sqrt ` A ) e. RR')
    sge = st([aa, w.inst('sqrtge0')], 'syl', '0 <_ ( sqrt ` A )')
    sth = st([aa, w.inst('resqrtth')], 'syl', '( ( sqrt ` A ) ^ 2 ) = A')
    bic = st([st([st([bre, bge], 'jca', '( B e. RR /\\ 0 <_ B )'),
                  st([sre, sge], 'jca', '( ( sqrt ` A ) e. RR /\\ 0 <_ ( sqrt ` A ) )')], 'jca',
                 '( ( B e. RR /\\ 0 <_ B ) /\\ '
                 '( ( sqrt ` A ) e. RR /\\ 0 <_ ( sqrt ` A ) ) )'), w.inst('le2sq')], 'syl',
             '( B <_ ( sqrt ` A ) <-> ( B ^ 2 ) <_ ( ( sqrt ` A ) ^ 2 ) )')
    bsq2 = st([bsq, st([sth], 'eqcomd', 'A = ( ( sqrt ` A ) ^ 2 )')], 'breqtrd',
              '( B ^ 2 ) <_ ( ( sqrt ` A ) ^ 2 )')
    bles = st([bic, bsq2], 'mpbird', 'B <_ ( sqrt ` A )')
    w.qed([st([sre, st([bn0], 'nn0zd', 'B e. ZZ'), w.inst('flge')], 'syl2anc',
              '( B <_ ( sqrt ` A ) <-> B <_ %s )' % FL('A')), bles], 'mpbid',
          '( %s -> B <_ %s )' % (AG, FL('A')))
    return w


AL = '( A e. RR /\\ 0 <_ A /\\ 1 <_ %s )' % FL('A')


def flsqle():
    w = WS('flsqle', 'The integer square root of a nonnegative real at least 1 is at most '
                     'that real.')
    st = mkst(w, AL)
    are = st([], 'simp1', 'A e. RR')
    age = st([], 'simp2', '0 <_ A')
    fge = st([], 'simp3', '1 <_ %s' % FL('A'))
    fl = st([st([are, age], 'jca', '( A e. RR /\\ 0 <_ A )'), w.inst('flsqrt2')], 'syl',
            '( %s e. NN0 /\\ ( %s ^ 2 ) <_ A /\\ A < ( ( %s + 1 ) ^ 2 ) )'
            % (FL('A'), FL('A'), FL('A')))
    fn0 = st([fl], 'simp1d', '%s e. NN0' % FL('A'))
    fsq = st([fl], 'simp2d', '( %s ^ 2 ) <_ A' % FL('A'))
    fre = st([fn0], 'nn0red', '%s e. RR' % FL('A'))
    fge0 = st([fn0], 'nn0ge0d', '0 <_ %s' % FL('A'))
    sqv = st([st([fre], 'recnd', '%s e. CC' % FL('A'))], 'sqvald',
             '( %s ^ 2 ) = ( %s x. %s )' % (FL('A'), FL('A'), FL('A')))
    mul = st([st([st([st([], '1red', '1 e. RR'), fre, st([fre, fge0], 'jca',
                                                         '( %s e. RR /\\ 0 <_ %s )'
                                                         % (FL('A'), FL('A')))], '3jca',
                      '( 1 e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) )'
                      % (FL('A'), FL('A'), FL('A'))), fge], 'jca',
                  '( ( 1 e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ 1 <_ %s )'
                  % (FL('A'), FL('A'), FL('A'), FL('A'))), w.inst('lemul1a')], 'syl',
              '( 1 x. %s ) <_ ( %s x. %s )' % (FL('A'), FL('A'), FL('A')))
    flesq = st([st([st([st([fre], 'recnd', '%s e. CC' % FL('A'))], 'mullidd',
                       '( 1 x. %s ) = %s' % (FL('A'), FL('A')))], 'eqcomd',
                   '%s = ( 1 x. %s )' % (FL('A'), FL('A'))), mul], 'eqbrtrd',
               '%s <_ ( %s x. %s )' % (FL('A'), FL('A'), FL('A')))
    flesq2 = st([flesq, st([sqv], 'eqcomd',
                           '( %s x. %s ) = ( %s ^ 2 )' % (FL('A'), FL('A'), FL('A')))],
                'breqtrd', '%s <_ ( %s ^ 2 )' % (FL('A'), FL('A')))
    fsqre = st([fre, st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'reexpcld',
               '( %s ^ 2 ) e. RR' % FL('A'))
    w.qed([fre, fsqre, are, flesq2, fsq], 'letrd', '( %s -> %s <_ A )' % (AL, FL('A')))
    return w


ALL = {'flsqge': flsqge, 'flsqle': flsqle}



# ------------------------------------------------ the iterated square roots
T1 = FL('T')
T2 = FL(T1)
T3 = FL(T2)
ZS = FL(T3)
US = FL(ZS)
B1 = '( 2 ^ 2 )'
B2 = '( %s ^ 2 )' % B1
B3 = '( %s ^ 2 )' % B2
B4 = '( %s ^ 2 )' % B3
B5 = '( %s ^ 2 )' % B4
AT = 'T e. ( ZZ>= ` %s )' % B5
LT = '( log ` T )'


def twinsqf():
    w = WS('twinsqf', 'The numerical facts about the fivefold iterated integer square root '
                      'of a threshold used by the twin-type sieve bound.')
    st = mkst(w, AT)
    two0 = st([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    BS = ['2', B1, B2, B3, B4, B5]
    bnn = {0: st([w.s([], '2nn', '2 e. NN')], 'a1i', '2 e. NN')}
    for k in range(1, 6):
        bnn[k] = st([bnn[k - 1], two0], 'nnexpcld', '%s e. NN' % BS[k])
    bn0 = {k: st([bnn[k]], 'nnnn0d', '%s e. NN0' % BS[k]) for k in range(6)}
    bge1 = {k: st([bnn[k], w.inst('nnge1')], 'syl', '1 <_ %s' % BS[k]) for k in range(6)}
    bre = {k: st([bnn[k]], 'nnred', '%s e. RR' % BS[k]) for k in range(6)}
    b5le = st([st([], 'id', AT), w.inst('eluzle')], 'syl', '%s <_ T' % B5)
    tn0 = st([bn0[5], st([], 'id', AT), w.inst('eluznn0')], 'syl2anc', 'T e. NN0')
    tre = st([tn0], 'nn0red', 'T e. RR')
    tge = st([tn0], 'nn0ge0d', '0 <_ T')
    # the five floors and their basic facts
    chain = [('T', T1, 4), (T1, T2, 3), (T2, T3, 2), (T3, ZS, 1), (ZS, US, 0)]
    inf = {'T': dict(n0=tn0, re=tre, ge=tge)}
    for A, F, k in chain:
        pack = st([st([inf[A]['re'], inf[A]['ge']], 'jca',
                      '( %s e. RR /\ 0 <_ %s )' % (A, A)), w.inst('flsqrt2')], 'syl',
                  '( %s e. NN0 /\ ( %s ^ 2 ) <_ %s /\ %s < ( ( %s + 1 ) ^ 2 ) )'
                  % (F, F, A, A, F))
        n0 = st([pack], 'simp1d', '%s e. NN0' % F)
        inf[F] = dict(n0=n0, sq=st([pack], 'simp2d', '( %s ^ 2 ) <_ %s' % (F, A)),
                      lt=st([pack], 'simp3d', '%s < ( ( %s + 1 ) ^ 2 )' % (A, F)),
                      re=st([n0], 'nn0red', '%s e. RR' % F),
                      ge=st([n0], 'nn0ge0d', '0 <_ %s' % F))
    # the lower bounds
    prevle = b5le
    for A, F, k in chain:
        B = BS[k]
        inf[F]['low'] = st([st([inf[A]['re'], bn0[k], prevle], '3jca',
                               '( %s e. RR /\ %s e. NN0 /\ ( %s ^ 2 ) <_ %s )' % (A, B, B, A)),
                            w.inst('flsqge')], 'syl', '%s <_ %s' % (B, F))
        prevle = inf[F]['low']
    # 1 <_ F for each floor, then the upper bounds F <_ A
    for A, F, k in chain:
        B = BS[k]
        inf[F]['ge1'] = st([st([], '1red', '1 e. RR'), bre[k], inf[F]['re'],
                            bge1[k], inf[F]['low']], 'letrd', '1 <_ %s' % F)
        inf[F]['le'] = st([st([inf[A]['re'], inf[A]['ge'], inf[F]['ge1']], '3jca',
                              '( %s e. RR /\ 0 <_ %s /\ 1 <_ %s )' % (A, A, F)),
                           w.inst('flsqle')], 'syl', '%s <_ %s' % (F, A))
    # 2 <_ US, and 2 <_ each bigger floor
    two = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    inf[US]['two'] = inf[US]['low']
    for A, F, k in reversed(chain):
        inf[A]['two'] = st([two, inf[F]['re'], inf[A]['re'], inf[F]['two'],
                            inf[F]['le']], 'letrd', '2 <_ %s' % A)
    # each floor is a positive integer
    for A, F, k in chain:
        inf[F]['nn'] = st([st([inf[F]['n0'], inf[F]['ge1']], 'jca',
                              '( %s e. NN0 /\ 1 <_ %s )' % (F, F)),
                           st([w.s([], 'elnnnn0c',
                                   '( %s e. NN <-> ( %s e. NN0 /\ 1 <_ %s ) )' % (F, F, F))],
                              'a1i',
                              '( %s e. NN <-> ( %s e. NN0 /\ 1 <_ %s ) )' % (F, F, F))],
                          'mpbird', '%s e. NN' % F)
    inf['T']['nn'] = st([st([tn0, st([st([], '1red', '1 e. RR'), two, tre, 
                                      st([w.s([], '1le2', '1 <_ 2')], 'a1i', '1 <_ 2'),
                                      inf['T']['two']], 'letrd', '1 <_ T')], 'jca',
                             '( T e. NN0 /\ 1 <_ T )'),
                         st([w.s([], 'elnnnn0c',
                                 '( T e. NN <-> ( T e. NN0 /\ 1 <_ T ) )')], 'a1i',
                            '( T e. NN <-> ( T e. NN0 /\ 1 <_ T ) )')], 'mpbird', 'T e. NN')
    inf['T']['uz2'] = st([st([st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'),
                              st([tn0], 'nn0zd', 'T e. ZZ'), inf['T']['two']], '3jca',
                             '( 2 e. ZZ /\ T e. ZZ /\ 2 <_ T )'),
                          st([w.s([], 'eluz2',
                                  '( T e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\ T e. ZZ /\ '
                                  '2 <_ T ) )')], 'a1i',
                             '( T e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\ T e. ZZ /\ '
                             '2 <_ T ) )')], 'mpbird', 'T e. ( ZZ>= ` 2 )')
    for A, F, k in chain:
        inf[F]['uz2'] = st([st([st([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'),
                                st([inf[F]['n0']], 'nn0zd', '%s e. ZZ' % F),
                                inf[F]['two']], '3jca',
                               '( 2 e. ZZ /\ %s e. ZZ /\ 2 <_ %s )' % (F, F)),
                            st([w.s([], 'eluz2',
                                    '( %s e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\ %s e. ZZ /\ '
                                    '2 <_ %s ) )' % (F, F, F))], 'a1i',
                               '( %s e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\ %s e. ZZ /\ '
                               '2 <_ %s ) )' % (F, F, F))], 'mpbird',
                           '%s e. ( ZZ>= ` 2 )' % F)
    # ---- the logarithm chain
    for A, F, k in chain:
        inf[F]['lrp'] = st([inf[F]['nn']], 'nnrpd', '%s e. RR+' % F)
        inf[F]['lre'] = st([inf[F]['lrp'], w.inst('relogcl')], 'syl',
                           '( log ` %s ) e. RR' % F)
    inf['T']['lrp'] = st([inf['T']['nn']], 'nnrpd', 'T e. RR+')
    inf['T']['lre'] = st([inf['T']['lrp'], w.inst('relogcl')], 'syl', '( log ` T ) e. RR')
    twore = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    twoge = st([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2')
    fourre = st([num.fact(w, '4', 'RR')], 'a1i', '4 e. RR')
    onerp = st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')
    for A, F, k in chain:
        lp1 = st([st([st([inf[A]['nn'], inf[F]['n0'], two0], '3jca',
                         '( %s e. NN /\ %s e. NN0 /\ 2 e. NN0 )' % (A, F)),
                      w.inst('logpwub')], 'syl',
                     '( %s < ( ( %s + 1 ) ^ 2 ) -> ( log ` %s ) <_ '
                     '( 2 x. ( log ` ( %s + 1 ) ) ) )' % (A, F, A, F)), inf[F]['lt']], 'mpd',
                 '( log ` %s ) <_ ( 2 x. ( log ` ( %s + 1 ) ) )' % (A, F))
        l2 = st([inf[F]['uz2'], w.inst('logp1le2')], 'syl',
                '( log ` ( %s + 1 ) ) <_ ( 2 x. ( log ` %s ) )' % (F, F))
        lp1re = st([st([inf[F]['lrp'], onerp], 'rpaddcld', '( %s + 1 ) e. RR+' % F),
                    w.inst('relogcl')], 'syl', '( log ` ( %s + 1 ) ) e. RR' % F)
        dblre = st([twore, inf[F]['lre']], 'remulcld', '( 2 x. ( log ` %s ) ) e. RR' % F)
        m = st([st([st([lp1re, dblre, st([twore, twoge], 'jca',
                                         '( 2 e. RR /\ 0 <_ 2 )')], '3jca',
                       '( ( log ` ( %s + 1 ) ) e. RR /\ ( 2 x. ( log ` %s ) ) e. RR /\ '
                       '( 2 e. RR /\ 0 <_ 2 ) )' % (F, F)), l2], 'jca',
                    '( ( ( log ` ( %s + 1 ) ) e. RR /\ ( 2 x. ( log ` %s ) ) e. RR /\ '
                    '( 2 e. RR /\ 0 <_ 2 ) ) /\ ( log ` ( %s + 1 ) ) <_ '
                    '( 2 x. ( log ` %s ) ) )' % (F, F, F, F)), w.inst('lemul2a')], 'syl',
                '( 2 x. ( log ` ( %s + 1 ) ) ) <_ ( 2 x. ( 2 x. ( log ` %s ) ) )' % (F, F))
        mas = st([st([twore], 'recnd', '2 e. CC'), st([twore], 'recnd', '2 e. CC'),
                  st([inf[F]['lre']], 'recnd', '( log ` %s ) e. CC' % F)], 'mulassd',
                 '( ( 2 x. 2 ) x. ( log ` %s ) ) = ( 2 x. ( 2 x. ( log ` %s ) ) )' % (F, F))
        t4 = st([st([w.s([], '2t2e4', '( 2 x. 2 ) = 4')], 'a1i', '( 2 x. 2 ) = 4')], 'oveq1d',
                '( ( 2 x. 2 ) x. ( log ` %s ) ) = ( 4 x. ( log ` %s ) )' % (F, F))
        d4 = st([st([mas], 'eqcomd',
                    '( 2 x. ( 2 x. ( log ` %s ) ) ) = ( ( 2 x. 2 ) x. ( log ` %s ) )'
                    % (F, F)), t4], 'eqtrd',
                '( 2 x. ( 2 x. ( log ` %s ) ) ) = ( 4 x. ( log ` %s ) )' % (F, F))
        chn = st([inf[A]['lre'], st([twore, lp1re], 'remulcld',
                                    '( 2 x. ( log ` ( %s + 1 ) ) ) e. RR' % F),
                  st([twore, dblre], 'remulcld',
                     '( 2 x. ( 2 x. ( log ` %s ) ) ) e. RR' % F), lp1, m], 'letrd',
                 '( log ` %s ) <_ ( 2 x. ( 2 x. ( log ` %s ) ) )' % (A, F))
        inf[F]['step'] = st([chn, d4], 'breqtrd',
                            '( log ` %s ) <_ ( 4 x. ( log ` %s ) )' % (A, F))
        inf[F]['lp1'] = lp1
        inf[F]['lp1re'] = lp1re
    # compose the five steps
    cst = 4
    cur = inf[T1]['step']
    curtxt = '4'
    for A, F, k in chain[1:]:
        prevF = A
        newc = cst * 4
        ctxt = num.nat_text(newc)
        cre = st([num.fact(w, curtxt, 'RR')], 'a1i', '%s e. RR' % curtxt)
        cge = st([num.fact(w, curtxt, 'ge0')], 'a1i', '0 <_ %s' % curtxt)
        stp = inf[F]['step']
        rhsre = st([fourre, inf[F]['lre']], 'remulcld', '( 4 x. ( log ` %s ) ) e. RR' % F)
        mm = st([st([st([inf[prevF]['lre'], rhsre, st([cre, cge], 'jca',
                                                      '( %s e. RR /\ 0 <_ %s )'
                                                      % (curtxt, curtxt))], '3jca',
                        '( ( log ` %s ) e. RR /\ ( 4 x. ( log ` %s ) ) e. RR /\ '
                        '( %s e. RR /\ 0 <_ %s ) )' % (prevF, F, curtxt, curtxt)), stp],
                     'jca',
                     '( ( ( log ` %s ) e. RR /\ ( 4 x. ( log ` %s ) ) e. RR /\ '
                     '( %s e. RR /\ 0 <_ %s ) ) /\ ( log ` %s ) <_ '
                     '( 4 x. ( log ` %s ) ) )'
                     % (prevF, F, curtxt, curtxt, prevF, F)), w.inst('lemul2a')], 'syl',
                '( %s x. ( log ` %s ) ) <_ ( %s x. ( 4 x. ( log ` %s ) ) )'
                % (curtxt, prevF, curtxt, F))
        masc = st([st([cre], 'recnd', '%s e. CC' % curtxt), st([fourre], 'recnd', '4 e. CC'),
                   st([inf[F]['lre']], 'recnd', '( log ` %s ) e. CC' % F)], 'mulassd',
                  '( ( %s x. 4 ) x. ( log ` %s ) ) = ( %s x. ( 4 x. ( log ` %s ) ) )'
                  % (curtxt, F, curtxt, F))
        prodn = num.mul_nat(w, cst, 4)
        newt = st([st([prodn], 'a1i', '( %s x. 4 ) = %s' % (curtxt, ctxt))], 'oveq1d',
                  '( ( %s x. 4 ) x. ( log ` %s ) ) = ( %s x. ( log ` %s ) )'
                  % (curtxt, F, ctxt, F))
        conv = st([st([masc], 'eqcomd',
                      '( %s x. ( 4 x. ( log ` %s ) ) ) = ( ( %s x. 4 ) x. ( log ` %s ) )'
                      % (curtxt, F, curtxt, F)), newt], 'eqtrd',
                  '( %s x. ( 4 x. ( log ` %s ) ) ) = ( %s x. ( log ` %s ) )'
                  % (curtxt, F, ctxt, F))
        cur = st([st([inf['T']['lre'], st([cre, inf[prevF]['lre']], 'remulcld',
                                          '( %s x. ( log ` %s ) ) e. RR' % (curtxt, prevF)),
                      st([cre, rhsre], 'remulcld',
                         '( %s x. ( 4 x. ( log ` %s ) ) ) e. RR' % (curtxt, F)), cur, mm],
                     'letrd',
                     '( log ` T ) <_ ( %s x. ( 4 x. ( log ` %s ) ) )' % (curtxt, F)), conv],
                 'breqtrd', '( log ` T ) <_ ( %s x. ( log ` %s ) )' % (ctxt, F))
        cst, curtxt = newc, ctxt
    logus = cur
    # ---- ( log ` T ) <_ ( 8 x. T2 )
    t2rp = inf[T2]['lrp']
    lpl = st([t2rp, w.inst('logp1le')], 'syl', '( log ` ( %s + 1 ) ) <_ %s' % (T2, T2))
    lp1re2 = inf[T2]['lp1re']
    t2re = inf[T2]['re']
    m2 = st([st([st([lp1re2, t2re, st([twore, twoge], 'jca', '( 2 e. RR /\ 0 <_ 2 )')],
                    '3jca',
                    '( ( log ` ( %s + 1 ) ) e. RR /\ %s e. RR /\ '
                    '( 2 e. RR /\ 0 <_ 2 ) )' % (T2, T2)), lpl], 'jca',
                 '( ( ( log ` ( %s + 1 ) ) e. RR /\ %s e. RR /\ '
                 '( 2 e. RR /\ 0 <_ 2 ) ) /\ ( log ` ( %s + 1 ) ) <_ %s )'
                 % (T2, T2, T2, T2)), w.inst('lemul2a')], 'syl',
             '( 2 x. ( log ` ( %s + 1 ) ) ) <_ ( 2 x. %s )' % (T2, T2))
    l1le = st([inf[T1]['lre'], st([twore, lp1re2], 'remulcld',
                                  '( 2 x. ( log ` ( %s + 1 ) ) ) e. RR' % T2),
               st([twore, t2re], 'remulcld', '( 2 x. %s ) e. RR' % T2),
               inf[T2]['lp1'], m2], 'letrd', '( log ` %s ) <_ ( 2 x. %s )' % (T1, T2))
    fourge = st([num.fact(w, '4', 'ge0')], 'a1i', '0 <_ 4')
    m3 = st([st([st([inf[T1]['lre'], st([twore, t2re], 'remulcld', '( 2 x. %s ) e. RR' % T2),
                     st([fourre, fourge], 'jca', '( 4 e. RR /\ 0 <_ 4 )')], '3jca',
                    '( ( log ` %s ) e. RR /\ ( 2 x. %s ) e. RR /\ '
                    '( 4 e. RR /\ 0 <_ 4 ) )' % (T1, T2)), l1le], 'jca',
                 '( ( ( log ` %s ) e. RR /\ ( 2 x. %s ) e. RR /\ '
                 '( 4 e. RR /\ 0 <_ 4 ) ) /\ ( log ` %s ) <_ ( 2 x. %s ) )'
                 % (T1, T2, T1, T2)), w.inst('lemul2a')], 'syl',
             '( 4 x. ( log ` %s ) ) <_ ( 4 x. ( 2 x. %s ) )' % (T1, T2))
    mas8 = st([st([fourre], 'recnd', '4 e. CC'), st([twore], 'recnd', '2 e. CC'),
               st([t2re], 'recnd', '%s e. CC' % T2)], 'mulassd',
              '( ( 4 x. 2 ) x. %s ) = ( 4 x. ( 2 x. %s ) )' % (T2, T2))
    t8 = st([st([w.s([], '4t2e8', '( 4 x. 2 ) = 8')], 'a1i', '( 4 x. 2 ) = 8')], 'oveq1d',
            '( ( 4 x. 2 ) x. %s ) = ( 8 x. %s )' % (T2, T2))
    conv8 = st([st([mas8], 'eqcomd',
                   '( 4 x. ( 2 x. %s ) ) = ( ( 4 x. 2 ) x. %s )' % (T2, T2)), t8], 'eqtrd',
               '( 4 x. ( 2 x. %s ) ) = ( 8 x. %s )' % (T2, T2))
    eight = st([num.fact(w, '8', 'RR')], 'a1i', '8 e. RR')
    lt8 = st([st([inf['T']['lre'], st([fourre, inf[T1]['lre']], 'remulcld',
                                      '( 4 x. ( log ` %s ) ) e. RR' % T1),
                  st([fourre, st([twore, t2re], 'remulcld', '( 2 x. %s ) e. RR' % T2)],
                     'remulcld', '( 4 x. ( 2 x. %s ) ) e. RR' % T2),
                  inf[T1]['step'], m3], 'letrd',
                 '( log ` T ) <_ ( 4 x. ( 2 x. %s ) )' % T2), conv8], 'breqtrd',
              '( log ` T ) <_ ( 8 x. %s )' % T2)
    # ---- ( ( log ` T ) ^ 2 ) <_ ( ; 6 4 x. T1 )
    tge1 = st([st([], '1red', '1 e. RR'), twore, tre,
               st([w.s([], '1le2', '1 <_ 2')], 'a1i', '1 <_ 2'), inf['T']['two']], 'letrd',
              '1 <_ T')
    logge = st([st([tre, tge1], 'jca', '( T e. RR /\ 1 <_ T )'), w.inst('logge0')], 'syl',
               '0 <_ ( log ` T )')
    e8re = st([eight, t2re], 'remulcld', '( 8 x. %s ) e. RR' % T2)
    sq1 = st([st([st([inf['T']['lre'], logge], 'jca',
                     '( ( log ` T ) e. RR /\ 0 <_ ( log ` T ) )'),
                  st([e8re, lt8], 'jca',
                     '( ( 8 x. %s ) e. RR /\ ( log ` T ) <_ ( 8 x. %s ) )' % (T2, T2))],
                 'jca',
                 '( ( ( log ` T ) e. RR /\ 0 <_ ( log ` T ) ) /\ '
                 '( ( 8 x. %s ) e. RR /\ ( log ` T ) <_ ( 8 x. %s ) ) )' % (T2, T2)),
              w.inst('le2sq2')], 'syl',
             '( ( log ` T ) ^ 2 ) <_ ( ( 8 x. %s ) ^ 2 )' % T2)
    mex = st([st([eight], 'recnd', '8 e. CC'), st([t2re], 'recnd', '%s e. CC' % T2), two0,
              w.inst('mulexp')], 'syl3anc',
             '( ( 8 x. %s ) ^ 2 ) = ( ( 8 ^ 2 ) x. ( %s ^ 2 ) )' % (T2, T2))
    sq8 = st([st([st([eight], 'recnd', '8 e. CC'), w.inst('sqval')], 'syl',
                 '( 8 ^ 2 ) = ( 8 x. 8 )'),
              st([w.s([], '8t8e64', '( 8 x. 8 ) = ; 6 4')], 'a1i', '( 8 x. 8 ) = ; 6 4')],
             'eqtrd', '( 8 ^ 2 ) = ; 6 4')
    mex2 = st([mex, st([sq8], 'oveq1d',
                       '( ( 8 ^ 2 ) x. ( %s ^ 2 ) ) = ( ; 6 4 x. ( %s ^ 2 ) )' % (T2, T2))],
              'eqtrd', '( ( 8 x. %s ) ^ 2 ) = ( ; 6 4 x. ( %s ^ 2 ) )' % (T2, T2))
    s64 = st([num.fact(w, '; 6 4', 'RR')], 'a1i', '; 6 4 e. RR')
    s64g = st([num.fact(w, '; 6 4', 'ge0')], 'a1i', '0 <_ ; 6 4')
    t2sqre = st([t2re, two0], 'reexpcld', '( %s ^ 2 ) e. RR' % T2)
    m64 = st([st([st([t2sqre, inf[T1]['re'], st([s64, s64g], 'jca',
                                                '( ; 6 4 e. RR /\ 0 <_ ; 6 4 )')], '3jca',
                      '( ( %s ^ 2 ) e. RR /\ %s e. RR /\ ( ; 6 4 e. RR /\ 0 <_ ; 6 4 ) )'
                      % (T2, T1)), inf[T2]['sq']], 'jca',
                  '( ( ( %s ^ 2 ) e. RR /\ %s e. RR /\ ( ; 6 4 e. RR /\ 0 <_ ; 6 4 ) ) /\ '
                  '( %s ^ 2 ) <_ %s )' % (T2, T1, T2, T1)), w.inst('lemul2a')], 'syl',
             '( ; 6 4 x. ( %s ^ 2 ) ) <_ ( ; 6 4 x. %s )' % (T2, T1))
    ltsq = st([st([st([inf['T']['lre'], two0], 'reexpcld', '( ( log ` T ) ^ 2 ) e. RR'),
                  st([s64, t2sqre], 'remulcld', '( ; 6 4 x. ( %s ^ 2 ) ) e. RR' % T2),
                  st([s64, inf[T1]['re']], 'remulcld', '( ; 6 4 x. %s ) e. RR' % T1),
                  st([sq1, mex2], 'breqtrd',
                     '( ( log ` T ) ^ 2 ) <_ ( ; 6 4 x. ( %s ^ 2 ) )' % T2), m64], 'letrd',
               '( ( log ` T ) ^ 2 ) <_ ( ; 6 4 x. %s )' % T1)], 'id', 'z')
    w.lines.pop()
    ltsq = st([st([inf['T']['lre'], two0], 'reexpcld', '( ( log ` T ) ^ 2 ) e. RR'),
               st([s64, t2sqre], 'remulcld', '( ; 6 4 x. ( %s ^ 2 ) ) e. RR' % T2),
               st([s64, inf[T1]['re']], 'remulcld', '( ; 6 4 x. %s ) e. RR' % T1),
               st([sq1, mex2], 'breqtrd',
                  '( ( log ` T ) ^ 2 ) <_ ( ; 6 4 x. ( %s ^ 2 ) )' % T2), m64], 'letrd',
              '( ( log ` T ) ^ 2 ) <_ ( ; 6 4 x. %s )' % T1)
    # ---- the error bound
    zsq = '( %s ^ 2 )' % ZS
    zsq2 = '( %s ^ 2 )' % zsq
    zsq4 = '( %s ^ 4 )' % zsq
    zsqre = st([inf[ZS]['re'], two0], 'reexpcld', '%s e. RR' % zsq)
    zsqge = st([inf[ZS]['re'], inf[ZS]['ge'], two0], 'expge0d', '0 <_ %s' % zsq)
    e1 = st([st([st([zsqre, inf[T3]['re'], two0], '3jca',
                    '( %s e. RR /\ %s e. RR /\ 2 e. NN0 )' % (zsq, T3)),
                 st([zsqge, inf[ZS]['sq']], 'jca',
                    '( 0 <_ %s /\ %s <_ %s )' % (zsq, zsq, T3))], 'jca',
                '( ( %s e. RR /\ %s e. RR /\ 2 e. NN0 ) /\ '
                '( 0 <_ %s /\ %s <_ %s ) )' % (zsq, T3, zsq, zsq, T3)),
             w.inst('leexp1a')], 'syl', '%s <_ ( %s ^ 2 )' % (zsq2, T3))
    t3sqre = st([inf[T3]['re'], two0], 'reexpcld', '( %s ^ 2 ) e. RR' % T3)
    zsq2re = st([zsqre, two0], 'reexpcld', '%s e. RR' % zsq2)
    e2 = st([zsq2re, t3sqre, inf[T2]['re'], e1, inf[T3]['sq']], 'letrd',
             '%s <_ %s' % (zsq2, T2))
    zsq2ge = st([zsqre, zsqge, two0], 'expge0d', '0 <_ %s' % zsq2)
    e3 = st([st([st([zsq2re, inf[T2]['re'], two0], '3jca',
                    '( %s e. RR /\ %s e. RR /\ 2 e. NN0 )' % (zsq2, T2)),
                 st([zsq2ge, e2], 'jca', '( 0 <_ %s /\ %s <_ %s )' % (zsq2, zsq2, T2))],
                'jca',
                '( ( %s e. RR /\ %s e. RR /\ 2 e. NN0 ) /\ '
                '( 0 <_ %s /\ %s <_ %s ) )' % (zsq2, T2, zsq2, zsq2, T2)),
             w.inst('leexp1a')], 'syl', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (zsq2, T2))
    zsq22re = st([zsq2re, two0], 'reexpcld', '( %s ^ 2 ) e. RR' % zsq2)
    e4 = st([zsq22re, t2sqre, inf[T1]['re'], e3, inf[T2]['sq']], 'letrd',
             '( %s ^ 2 ) <_ %s' % (zsq2, T1))
    em4 = st([st([zsqre], 'recnd', '%s e. CC' % zsq), two0, two0, w.inst('expmul')],
             'syl3anc', '( %s ^ ( 2 x. 2 ) ) = ( %s ^ 2 )' % (zsq, zsq2))
    em4b = st([st([st([w.s([], '2t2e4', '( 2 x. 2 ) = 4')], 'a1i', '( 2 x. 2 ) = 4')],
                  'oveq2d', '( %s ^ ( 2 x. 2 ) ) = %s' % (zsq, zsq4))], 'id', 'z')
    w.lines.pop()
    em4b = st([st([w.s([], '2t2e4', '( 2 x. 2 ) = 4')], 'a1i', '( 2 x. 2 ) = 4')], 'oveq2d',
              '( %s ^ ( 2 x. 2 ) ) = %s' % (zsq, zsq4))
    zeq = st([st([em4b], 'eqcomd', '%s = ( %s ^ ( 2 x. 2 ) )' % (zsq4, zsq)), em4], 'eqtrd',
             '%s = ( %s ^ 2 )' % (zsq4, zsq2))
    e5 = st([zeq, e4], 'eqbrtrd', '%s <_ %s' % (zsq4, T1))
    zlet1 = st([inf[ZS]['re'], inf[T3]['re'], inf[T1]['re'], inf[ZS]['le'],
                st([inf[T3]['re'], inf[T2]['re'], inf[T1]['re'], inf[T3]['le'],
                    inf[T2]['le']], 'letrd', '%s <_ %s' % (T3, T1))], 'letrd',
               '%s <_ %s' % (ZS, T1))
    zsq4re = st([zsqre, st([num.fact(w, '4', 'NN0')], 'a1i', '4 e. NN0')], 'reexpcld',
                '%s e. RR' % zsq4)
    addle = st([zsq4re, inf[T1]['re'], inf[ZS]['re'], inf[T1]['re'], e5, zlet1], 'le2addd',
               '( %s + %s ) <_ ( %s + %s )' % (zsq4, ZS, T1, T1))
    tw2 = st([st([inf[T1]['re']], 'recnd', '%s e. CC' % T1)], '2timesd',
             '( 2 x. %s ) = ( %s + %s )' % (T1, T1, T1))
    errle = st([addle, st([tw2], 'eqcomd', '( %s + %s ) = ( 2 x. %s )' % (T1, T1, T1))],
               'breqtrd', '( %s + %s ) <_ ( 2 x. %s )' % (zsq4, ZS, T1))
    # ---- the conclusion
    CONC = ('( ( %s e. NN /\ T e. NN0 /\ 2 <_ T ) /\ '
            '( ( log ` T ) <_ ( %s x. ( log ` %s ) ) /\ '
            '( ( log ` T ) ^ 2 ) <_ ( ; 6 4 x. %s ) ) /\ '
            '( ( %s + %s ) <_ ( 2 x. %s ) /\ ( %s ^ 2 ) <_ T /\ %s e. NN0 ) )'
            % (ZS, curtxt, US, T1, zsq4, ZS, T1, T1, T1))
    w.qed([st([inf[ZS]['nn'], tn0, inf['T']['two']], '3jca',
              '( %s e. NN /\ T e. NN0 /\ 2 <_ T )' % ZS),
           st([logus, ltsq], 'jca',
              '( ( log ` T ) <_ ( %s x. ( log ` %s ) ) /\ '
              '( ( log ` T ) ^ 2 ) <_ ( ; 6 4 x. %s ) )' % (curtxt, US, T1)),
           st([errle, inf[T1]['sq'], inf[T1]['n0']], '3jca',
              '( ( %s + %s ) <_ ( 2 x. %s ) /\ ( %s ^ 2 ) <_ T /\ %s e. NN0 )'
              % (zsq4, ZS, T1, T1, T1))], '3jca', '( %s -> %s )' % (AT, CONC))
    return w


ALL['twinsqf'] = twinsqf

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
