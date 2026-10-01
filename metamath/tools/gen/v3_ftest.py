"""Sortie v3: the single retry of tools/fsum.py that the orders asked for.

Not a theorem of the sortie: `v3ftest` is a grammar-and-unification test that
exercises `FSum.le` (`fsumle`) and `FSum.mulc2` (`fsummulc2`) with their body
closures handed in as plain worksheet step names proved under a two-level
antecedent -- the one change V2c said would have helped it.  Run with

    MM_DB=sorties/v3.mm python3 tools/mm.py unify worksheets/v3ftest.mmp

after `MM_DB=sorties/v3.mm python3 tools/gen/v3_ftest.py`, and expect
`UNIFY OK`.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W as WS
from cl import Closure
from fsum import FSum

ANTE = '( N e. NN /\\ C e. RR+ )'
HS = 'sum_ k e. ( 1 ... N ) ( 1 / k )'
CS = 'sum_ k e. ( 1 ... N ) 1'


def v3ftest():
    w = WS('v3ftest', 'fsum.py retry: fsumle and fsummulc2 with plain-step body closures.')
    st = lambda h, r, g: w.s(h, r, '( %s -> %s )' % (ANTE, g))
    nnn = st([], 'simpl', 'N e. NN')
    crp = st([], 'simpr', 'C e. RR+')
    cl = Closure(w, ANTE, {'N': ('NN', nnn), 'C': ('RR+', crp)})
    f = FSum(w, cl)
    AK = '( %s /\\ k e. ( 1 ... N ) )' % ANTE
    sk = lambda h, r, g: w.s(h, r, '( %s -> %s )' % (AK, g))
    knn = sk([sk([], 'simpr', 'k e. ( 1 ... N )'), w.inst('elfznn')], 'syl', 'k e. NN')
    krp = sk([knn], 'nnrpd', 'k e. RR+')
    kre = sk([krp], 'rpred', 'k e. RR')
    krec = sk([krp], 'rpreccld', '( 1 / k ) e. RR+')
    krecre = sk([krec], 'rpred', '( 1 / k ) e. RR')
    kcn = sk([krecre], 'recnd', '( 1 / k ) e. CC')
    k1 = sk([knn, w.inst('nnge1')], 'syl', '1 <_ k')
    one = sk([], '1red', '1 e. RR')
    lr = sk([sk([sk([one, sk([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1')], 'jca',
                    '( 1 e. RR /\\ 0 < 1 )'),
                 sk([kre, sk([krp], 'rpgt0d', '0 < k')], 'jca', '( k e. RR /\\ 0 < k )')], 'jca',
                '( ( 1 e. RR /\\ 0 < 1 ) /\\ ( k e. RR /\\ 0 < k ) )'), w.inst('lerec')], 'syl',
            '( 1 <_ k <-> ( 1 / k ) <_ ( 1 / 1 ) )')
    rle1 = sk([sk([lr, k1], 'mpbid', '( 1 / k ) <_ ( 1 / 1 )'),
               sk([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')], 'breqtrd',
              '( 1 / k ) <_ 1')
    le = f.le('k', '( 1 ... N )', '( 1 / k )', '1', rle1,
              body=[krecre, sk([], '1red', '1 e. RR')])
    f.mulc2('k', '( 1 ... N )', 'C', '( 1 / k )', body=kcn)
    w.qed([le, le], 'jca',
          '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ANTE, HS, CS, HS, CS))
    return w


if __name__ == '__main__':
    v3ftest().write()
    print('wrote worksheets/v3ftest.mmp')
