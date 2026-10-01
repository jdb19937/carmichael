"""Sortie v4a: the prime-power sum of the inflated density."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from v4a_lib import DEN, mkst
from cl import lift
from lin import linarith

AD = '( D e. Prime /\\ 3 <_ D /\\ C e. NN0 )'
DK = '( D ^ k )'
TD = '( 2 / D )'
FAC = '( %s / ( 1 - %s ) )' % (TD, TD)


def sgmpwle():
    w = WS('sgmpwle', 'The sum of the divisor count divided by the argument over the positive '
                      'powers of a prime at least 3 is at most 2 / ( D - 2 ) in Euler form.')
    st = mkst(w, AD)
    dprm = st([], 'simp1', 'D e. Prime')
    d3 = st([], 'simp2', '3 <_ D')
    cn0 = st([], 'simp3', 'C e. NN0')
    dnn = st([dprm, w.inst('prmnn')], 'syl', 'D e. NN')
    drp = st([dnn], 'nnrpd', 'D e. RR+')
    dre = st([drp], 'rpred', 'D e. RR')
    three = st([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR')
    two = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    lt23 = st([w.s([], '2lt3', '2 < 3')], 'a1i', '2 < 3')
    d2 = linarith(w, AD, [d3, lt23], '2 < D', leaves={'D': dre, '3': three, '2': two})
    tdrp = st([st([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), drp], 'rpdivcld',
               '%s e. RR+' % TD)
    tdre = st([tdrp], 'rpred', '%s e. RR' % TD)
    tdge = st([tdrp], 'rpge0d', '0 <_ %s' % TD)
    tdlt = st([st([two, drp, w.inst('divlt1lt')], 'syl2anc', '( %s < 1 <-> 2 < D )' % TD), d2],
              'mpbird', '%s < 1' % TD)
    # the body bound
    AK = '( %s /\\ k e. ( 1 ... C ) )' % AD
    sk = mkst(w, AK)
    knn = sk([sk([], 'simpr', 'k e. ( 1 ... C )'), w.inst('elfznn')], 'syl', 'k e. NN')
    kn0 = sk([knn], 'nnnn0d', 'k e. NN0')
    kre = sk([knn], 'nnred', 'k e. RR')
    sgv = sk([lift(w, dprm, AK), kn0, w.inst('0sgmppw')], 'syl2anc',
             '( 0 sigma %s ) = ( k + 1 )' % DK)
    ber = sk([sk([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), kn0, sk([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'),
              w.inst('bernneq2')], 'syl3anc', '( ( ( 2 - 1 ) x. k ) + 1 ) <_ ( 2 ^ k )')
    m21 = sk([w.s([], '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')
    r1 = sk([sk([m21], 'oveq1d', '( ( 2 - 1 ) x. k ) = ( 1 x. k )'),
             sk([sk([kre], 'recnd', 'k e. CC')], 'mullidd', '( 1 x. k ) = k')], 'eqtrd',
            '( ( 2 - 1 ) x. k ) = k')
    ber2 = sk([sk([r1], 'oveq1d', '( ( ( 2 - 1 ) x. k ) + 1 ) = ( k + 1 )'), ber], 'eqbrtrrd',
              '( k + 1 ) <_ ( 2 ^ k )')
    ber3 = sk([sgv, ber2], 'eqbrtrd', '( 0 sigma %s ) <_ ( 2 ^ k )' % DK)
    dkrp = sk([lift(w, drp, AK), sk([kn0], 'nn0zd', 'k e. ZZ'), w.inst('rpexpcl')], 'syl2anc',
              '%s e. RR+' % DK)
    dkre = sk([dkrp], 'rpred', '%s e. RR' % DK)
    sgre = sk([sk([sk([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'),
                   sk([lift(w, dnn, AK), kn0], 'nnexpcld', '%s e. NN' % DK),
                   w.inst('sgmnncl')], 'syl2anc', '( 0 sigma %s ) e. NN' % DK)], 'nnred',
              '( 0 sigma %s ) e. RR' % DK)
    twk = sk([sk([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), kn0], 'reexpcld',
              '( 2 ^ k ) e. RR')
    ledv = sk([sgre, twk, dkrp, ber3], 'lediv1dd',
              '%s <_ ( ( 2 ^ k ) / %s )' % (DEN(DK), DK))
    edv = sk([sk([], '2cnd', '2 e. CC'),
              sk([sk([lift(w, dre, AK)], 'recnd', 'D e. CC'), sk([lift(w, drp, AK)], 'rpne0d',
                                                                 'D =/= 0')], 'jca',
                 '( D e. CC /\\ D =/= 0 )'), kn0, w.inst('expdiv')], 'syl3anc',
             '( %s ^ k ) = ( ( 2 ^ k ) / %s )' % (TD, DK))
    body = sk([ledv, sk([edv], 'eqcomd', '( ( 2 ^ k ) / %s ) = ( %s ^ k )' % (DK, TD))],
              'breqtrd', '%s <_ ( %s ^ k )' % (DEN(DK), TD))
    denre = sk([sgre, dkrp], 'rerpdivcld', '%s e. RR' % DEN(DK))
    tdkre = sk([lift(w, tdre, AK), kn0], 'reexpcld', '( %s ^ k ) e. RR' % TD)
    fz = st([], 'fzfid', '( 1 ... C ) e. Fin')
    sle = st([fz, denre, tdkre, body], 'fsumle',
             'sum_ k e. ( 1 ... C ) %s <_ sum_ k e. ( 1 ... C ) ( %s ^ k )' % (DEN(DK), TD))
    geo = st([st([st([tdre, tdge, tdlt], '3jca',
                     '( %s e. RR /\\ 0 <_ %s /\\ %s < 1 )' % (TD, TD, TD)), cn0], 'jca',
                 '( ( %s e. RR /\\ 0 <_ %s /\\ %s < 1 ) /\\ C e. NN0 )' % (TD, TD, TD)),
              w.inst('geoslle')], 'syl',
             'sum_ k e. ( 1 ... C ) ( %s ^ k ) <_ %s' % (TD, FAC))
    lre = st([fz, denre], 'fsumrecl', 'sum_ k e. ( 1 ... C ) %s e. RR' % DEN(DK))
    mre = st([fz, tdkre], 'fsumrecl', 'sum_ k e. ( 1 ... C ) ( %s ^ k ) e. RR' % TD)
    one = st([], '1red', '1 e. RR')
    subr = st([one, tdre], 'resubcld', '( 1 - %s ) e. RR' % TD)
    sub0 = st([st([tdre, one], 'posdifd', '( %s < 1 <-> 0 < ( 1 - %s ) )' % (TD, TD)), tdlt],
              'mpbid', '0 < ( 1 - %s )' % TD)
    facre = st([tdre, st([subr, sub0], 'elrpd', '( 1 - %s ) e. RR+' % TD)], 'rerpdivcld',
               '%s e. RR' % FAC)
    w.qed([lre, mre, facre, sle, geo], 'letrd',
          '( %s -> sum_ k e. ( 1 ... C ) %s <_ %s )' % (AD, DEN(DK), FAC))
    return w


ALL = {'sgmpwle': sgmpwle}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
