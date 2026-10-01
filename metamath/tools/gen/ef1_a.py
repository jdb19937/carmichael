"""EF1 section 1: elementary estimates (ExplicitFormula 56-237).
`MM_DB=sorties/ef1.mm python3 tools/gen/ef1_a.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef1lib import *
from lin import linarith, nlinarith

only = sys.argv[1:]


def e1le3(w):
    """closed step: ( exp ` 1 ) <_ 3"""
    lt = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')
    le = w.s([w.s([], 'ere', '_e e. RR'), w.s([], '3re', '3 e. RR'), lt], 'ltleii', '_e <_ 3')
    return w.s([w.s([], 'df-e', '_e = ( exp ` 1 )'), le], 'eqbrtrri', '( exp ` 1 ) <_ 3')


# ---------------------------------------------------------------- ef1l4: 4 <_ log y for y >_ 100
if __name__ == '__main__' and (not only or 'ef1l4' in only):
    w = W('ef1l4', '` 4 <_ log y ` for ` 100 <_ y ` ( Lean ` four_le_log ` ; ` e ^ 4 <_ 81 ` is ~ zl2e4 ).')
    A = '( Y e. RR /\\ ; ; 1 0 0 <_ Y )'
    yr = D(w, A, 'simpl', [], 'Y e. RR')
    y100 = D(w, A, 'simpr', [], '; ; 1 0 0 <_ Y')
    e4 = a1(w, A, 'zl2e4', '( exp ` 4 ) <_ ; 8 1')
    r4 = a1(w, A, '4re', '4 e. RR')
    e4r = w.s([r4, w.inst('rpefcl')], 'syl', '( %s -> ( exp ` 4 ) e. RR+ )' % A)
    cl = Closure(w, A, {'Y': ('RR', yr), '( exp ` 4 )': ('RR+', e4r)})
    ey = linarith(w, A, [e4, y100], '( exp ` 4 ) <_ Y', closure=cl)
    ypos = linarith(w, A, [y100], '0 < Y', closure=cl)
    yrp = D(w, A, 'elrpd', [yr, ypos], 'Y e. RR+')
    bi = w.s([e4r, yrp, w.inst('logleb')], 'syl2anc', '( %s -> ( ( exp ` 4 ) <_ Y <-> ( log ` ( exp ` 4 ) ) <_ ( log ` Y ) ) )' % A)
    lg = D(w, A, 'mpbid', [ey, bi], '( log ` ( exp ` 4 ) ) <_ ( log ` Y )')
    re4 = w.s([r4, w.inst('relogef')], 'syl', '( %s -> ( log ` ( exp ` 4 ) ) = 4 )' % A)
    w.qed([re4, lg], 'eqbrtrrd', '( %s -> 4 <_ ( log ` Y ) )' % A)
    go(w, only)

# ---------------------------------------------------------------- ef1yc: y ^ ( 1 + 1 / log y ) = e y <_ 3 y
if __name__ == '__main__' and (not only or 'ef1yc' in only):
    w = W('ef1yc', '` y ^ ( 1 + 1 / log y ) = e y <_ 3 y ` for ` 1 < y ` ( Lean ` rpow_one_add_inv_log ` and the consumers\' '
          '` y ^ c <_ 3 y ` ).')
    A = '( Y e. RR /\\ 1 < Y )'
    yr = D(w, A, 'simpl', [], 'Y e. RR')
    y1 = D(w, A, 'simpr', [], '1 < Y')
    lrp = w.s([], 'rplogcl', '( %s -> ( log ` Y ) e. RR+ )' % A)
    one = a1(w, A, '1red', '1 e. RR') if False else a1(w, A, '1re', '1 e. RR')
    ypos = D(w, A, 'lttrd', [a1(w, A, '0re', '0 e. RR'), one, yr, a1(w, A, '0lt1', '0 < 1'), y1], '0 < Y')
    yrp = D(w, A, 'elrpd', [yr, ypos], 'Y e. RR+')
    yc = D(w, A, 'rpcnd', [yrp], 'Y e. CC')
    yne = D(w, A, 'rpne0d', [yrp], 'Y =/= 0')
    lc = D(w, A, 'rpcnd', [lrp], '( log ` Y ) e. CC')
    lne = D(w, A, 'rpne0d', [lrp], '( log ` Y ) =/= 0')
    IL = '( 1 / ( log ` Y ) )'
    ilc = D(w, A, 'reccld', [lc, lne], '%s e. CC' % IL)
    c1 = a1(w, A, 'ax-1cn', '1 e. CC')
    s1 = E(w, A, 'cxpaddd', [yc, yne, c1, ilc], '( Y ^c %s )' % C0, '( ( Y ^c 1 ) x. ( Y ^c %s ) )' % IL)
    s2 = E(w, A, 'cxp1d', [yc], '( Y ^c 1 )', 'Y')
    s3 = E(w, A, 'cxpefd', [yc, yne, ilc], '( Y ^c %s )' % IL, '( exp ` ( %s x. ( log ` Y ) ) )' % IL)
    s4 = w.s([lc, lne, w.inst('recid2')], 'syl2anc', '( %s -> ( %s x. ( log ` Y ) ) = 1 )' % (A, IL))
    s5 = E(w, A, 'fveq2d', [s4], '( exp ` ( %s x. ( log ` Y ) ) )' % IL, '( exp ` 1 )')
    s6 = w.s([s3, s5], 'eqtrd', '( %s -> ( Y ^c %s ) = ( exp ` 1 ) )' % (A, IL))
    s7 = E(w, A, 'oveq12d', [s2, s6], '( ( Y ^c 1 ) x. ( Y ^c %s ) )' % IL, '( Y x. ( exp ` 1 ) )')
    e1c = D(w, A, 'efcld', [c1], '( exp ` 1 ) e. CC')
    s8 = E(w, A, 'mulcomd', [yc, e1c], '( Y x. ( exp ` 1 ) )', '( ( exp ` 1 ) x. Y )')
    eq = chain(w, A, ['( Y ^c %s )' % C0, '( ( Y ^c 1 ) x. ( Y ^c %s ) )' % IL, '( Y x. ( exp ` 1 ) )', '( ( exp ` 1 ) x. Y )'], [s1, s7, s8])
    e1r = D(w, A, 'reefcld', [one], '( exp ` 1 ) e. RR')
    e13 = w.s([e1le3(w)], 'a1i', '( %s -> ( exp ` 1 ) <_ 3 )' % A)
    le = D(w, A, 'lemul1ad', [e1r, a1(w, A, '3re', '3 e. RR'), yr, D(w, A, 'rpge0d', [yrp], '0 <_ Y'), e13], '( ( exp ` 1 ) x. Y ) <_ ( 3 x. Y )')
    le2 = w.s([eq, le], 'eqbrtrd', '( %s -> ( Y ^c %s ) <_ ( 3 x. Y ) )' % (A, C0))
    w.qed([eq, le2], 'jca', '( %s -> ( ( Y ^c %s ) = ( ( exp ` 1 ) x. Y ) /\\ ( Y ^c %s ) <_ ( 3 x. Y ) ) )' % (A, C0, C0))
    go(w, only)
