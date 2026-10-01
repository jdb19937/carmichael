"""Sortie v3: the truncated geometric series bounds.

geosrle  ( ( ( X e. RR /\\ 0 <_ X /\\ X < 1 ) /\\ N e. NN0 ) ->
             sum_ k e. ( 0 ... N ) ( X ^ k ) <_ ( 1 / ( 1 - X ) ) )
geoslle  ( ( ( X e. RR /\\ 0 <_ X /\\ X < 1 ) /\\ N e. NN0 ) ->
             sum_ k e. ( 1 ... N ) ( X ^ k ) <_ ( X / ( 1 - X ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from v3_lib import mkst

A = '( ( X e. RR /\\ 0 <_ X /\\ X < 1 ) /\\ N e. NN0 )'
SUB = '( 1 - X )'


def _setup(w):
    st = mkst(w, A)
    xr = st([], 'simpl1', 'X e. RR')
    x0 = st([], 'simpl2', '0 <_ X')
    x1 = st([], 'simpl3', 'X < 1')
    n = st([], 'simpr', 'N e. NN0')
    xc = st([xr], 'recnd', 'X e. CC')
    xne = st([x1], 'ltned', 'X =/= 1')
    one = st([], '1red', '1 e. RR')
    pd = st([xr, one], 'posdifd', '( X < 1 <-> 0 < %s )' % SUB)
    sub0 = st([pd, x1], 'mpbid', '0 < %s' % SUB)
    subr = st([one, xr], 'resubcld', '%s e. RR' % SUB)
    subrp = st([subr, sub0], 'elrpd', '%s e. RR+' % SUB)
    nz = st([n], 'nn0zd', 'N e. ZZ')
    return dict(st=st, xr=xr, x0=x0, x1=x1, n=n, xc=xc, xne=xne, one=one,
                subr=subr, subrp=subrp, nz=nz)


def geosrle():
    w = W('geosrle', 'A truncated geometric series with ratio in [ 0 , 1 ) is at most '
                     '1 / ( 1 - X ).')
    d = _setup(w)
    st = d['st']
    n1 = st([d['n'], w.inst('nn0p1nn')], 'syl', '( N + 1 ) e. NN')
    n1n0 = st([n1], 'nnnn0d', '( N + 1 ) e. NN0')
    z0 = st([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0')
    nud = st([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', 'NN0 = ( ZZ>= ` 0 )')
    n1uz = st([n1n0, nud], 'eleqtrd', '( N + 1 ) e. ( ZZ>= ` 0 )')
    gs = st([d['xc'], d['xne'], z0, n1uz], 'geoserg',
            'sum_ k e. ( 0 ..^ ( N + 1 ) ) ( X ^ k ) = '
            '( ( ( X ^ 0 ) - ( X ^ ( N + 1 ) ) ) / %s )' % SUB)
    fz = st([d['nz'], w.inst('fzval3')], 'syl', '( 0 ... N ) = ( 0 ..^ ( N + 1 ) )')
    se = st([fz], 'sumeq1d',
            'sum_ k e. ( 0 ... N ) ( X ^ k ) = sum_ k e. ( 0 ..^ ( N + 1 ) ) ( X ^ k )')
    e0 = st([d['xc']], 'exp0d', '( X ^ 0 ) = 1')
    e0b = st([e0], 'oveq1d',
             '( ( X ^ 0 ) - ( X ^ ( N + 1 ) ) ) = ( 1 - ( X ^ ( N + 1 ) ) )')
    e0c = st([e0b], 'oveq1d',
             '( ( ( X ^ 0 ) - ( X ^ ( N + 1 ) ) ) / %s ) = ( ( 1 - ( X ^ ( N + 1 ) ) ) / %s )'
             % (SUB, SUB))
    val = st([se, st([gs, e0c], 'eqtrd',
                     'sum_ k e. ( 0 ..^ ( N + 1 ) ) ( X ^ k ) = ( ( 1 - ( X ^ ( N + 1 ) ) ) / %s )' % SUB)],
             'eqtrd', 'sum_ k e. ( 0 ... N ) ( X ^ k ) = ( ( 1 - ( X ^ ( N + 1 ) ) ) / %s )' % SUB)
    pge = st([d['xr'], n1n0, d['x0'], w.inst('expge0')], 'syl3anc', '0 <_ ( X ^ ( N + 1 ) )')
    pre = st([d['xr'], n1n0], 'reexpcld', '( X ^ ( N + 1 ) ) e. RR')
    from lin import linarith
    lem = linarith(w, A, [pge], '( 1 - ( X ^ ( N + 1 ) ) ) <_ 1',
                   leaves={'( X ^ ( N + 1 ) )': pre})
    dvi = st([lem, d['subrp']], 'lediv1dd',
             '( ( 1 - ( X ^ ( N + 1 ) ) ) / %s ) <_ ( 1 / %s )' % (SUB, SUB))
    w.qed([val, dvi], 'eqbrtrd',
          '( %s -> sum_ k e. ( 0 ... N ) ( X ^ k ) <_ ( 1 / %s ) )' % (A, SUB))
    return w


def geoslle():
    w = W('geoslle', 'A truncated geometric series from the first power with ratio in '
                     '[ 0 , 1 ) is at most X / ( 1 - X ).')
    d = _setup(w)
    st = d['st']
    n1 = st([d['n'], w.inst('nn0p1nn')], 'syl', '( N + 1 ) e. NN')
    n1n0 = st([n1], 'nnnn0d', '( N + 1 ) e. NN0')
    z1 = st([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0')
    nud = st([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', 'NN = ( ZZ>= ` 1 )')
    n1uz = st([n1, nud], 'eleqtrd', '( N + 1 ) e. ( ZZ>= ` 1 )')
    gs = st([d['xc'], d['xne'], z1, n1uz], 'geoserg',
            'sum_ k e. ( 1 ..^ ( N + 1 ) ) ( X ^ k ) = '
            '( ( ( X ^ 1 ) - ( X ^ ( N + 1 ) ) ) / %s )' % SUB)
    fz = st([d['nz'], w.inst('fzval3')], 'syl', '( 1 ... N ) = ( 1 ..^ ( N + 1 ) )')
    se = st([fz], 'sumeq1d',
            'sum_ k e. ( 1 ... N ) ( X ^ k ) = sum_ k e. ( 1 ..^ ( N + 1 ) ) ( X ^ k )')
    e1 = st([d['xc']], 'exp1d', '( X ^ 1 ) = X')
    e1b = st([e1], 'oveq1d',
             '( ( X ^ 1 ) - ( X ^ ( N + 1 ) ) ) = ( X - ( X ^ ( N + 1 ) ) )')
    e1c = st([e1b], 'oveq1d',
             '( ( ( X ^ 1 ) - ( X ^ ( N + 1 ) ) ) / %s ) = ( ( X - ( X ^ ( N + 1 ) ) ) / %s )'
             % (SUB, SUB))
    val = st([se, st([gs, e1c], 'eqtrd',
                     'sum_ k e. ( 1 ..^ ( N + 1 ) ) ( X ^ k ) = ( ( X - ( X ^ ( N + 1 ) ) ) / %s )' % SUB)],
             'eqtrd', 'sum_ k e. ( 1 ... N ) ( X ^ k ) = ( ( X - ( X ^ ( N + 1 ) ) ) / %s )' % SUB)
    pge = st([d['xr'], n1n0, d['x0'], w.inst('expge0')], 'syl3anc', '0 <_ ( X ^ ( N + 1 ) )')
    pre = st([d['xr'], n1n0], 'reexpcld', '( X ^ ( N + 1 ) ) e. RR')
    from lin import linarith
    lem = linarith(w, A, [pge], '( X - ( X ^ ( N + 1 ) ) ) <_ X',
                   leaves={'( X ^ ( N + 1 ) )': pre, 'X': d['xr']})
    dvi = st([lem, d['subrp']], 'lediv1dd',
             '( ( X - ( X ^ ( N + 1 ) ) ) / %s ) <_ ( X / %s )' % (SUB, SUB))
    w.qed([val, dvi], 'eqbrtrd',
          '( %s -> sum_ k e. ( 1 ... N ) ( X ^ k ) <_ ( X / %s ) )' % (A, SUB))
    return w


ALL = {'geosrle': geosrle, 'geoslle': geoslle}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
