"""Sortie A4b, batch 1: the exponential combinators of AlgBudget.lean.

Every bound of the cost budget has the form X <_ ( exp ` ( P x. M ) ) with a
rational literal P; these seven theorems are the only ways such bounds are
ever combined (Lean's local `mulE`, `expE`, `oneE`, `mono` and its `h8`).

    MM_DB=sorties/a4b.mm python3 tools/gen/a4b_exp.py [labels]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from a2lib import WH
from cl import Closure
from lin import linarith, nlinarith
import num

only = [a for a in sys.argv[1:] if not a.startswith('-')]
GENS = []
def gen(fn):
    GENS.append(fn); return fn

PH = 'ph'
def A(f): return '( ph -> %s )' % f


# ------------------------------------------------------------- cbege1
@gen
def cbege1():
    w = WH('cbege1', 'A power of the exponential at a nonnegative exponent is at least 1 '
                     '(Lean AlgBudget.lean, the local ` oneE ` of costPieces_bound).')
    mre = w.h('M e. RR'); m0 = w.h('0 <_ M'); pre = w.h('P e. RR'); p0 = w.h('0 <_ P')
    pm = w.s([pre, mre], 'remulcld', A('( P x. M ) e. RR'))
    pm0 = w.s([pre, mre, p0, m0], 'mulge0d', A('0 <_ ( P x. M )'))
    z = w.s([], '0red', A('0 e. RR'))
    bi = w.s([z, pm, w.inst('efle')], 'syl2anc',
             A('( 0 <_ ( P x. M ) <-> ( exp ` 0 ) <_ ( exp ` ( P x. M ) ) )'))
    st = w.s([pm0, bi], 'mpbid', A('( exp ` 0 ) <_ ( exp ` ( P x. M ) )'))
    e0 = w.s([w.s([], 'ef0', '( exp ` 0 ) = 1')], 'a1i', A('( exp ` 0 ) = 1'))
    w.qed([w.s([e0], 'eqcomd', A('1 = ( exp ` 0 )')), st], 'eqbrtrd', A('1 <_ ( exp ` ( P x. M ) )'))
    return w


# ------------------------------------------------------------- cbemo
@gen
def cbemo():
    w = WH('cbemo', 'The exponential bound is monotone in its rational coefficient '
                    '(Lean AlgBudget.lean, the locals ` expE ` and ` mono ` of costPieces_bound).')
    mre = w.h('M e. RR'); m0 = w.h('0 <_ M'); pre = w.h('P e. RR'); rre = w.h('R e. RR')
    pr = w.h('P <_ R')
    le = w.s([pre, rre, mre, m0, pr], 'lemul1ad', A('( P x. M ) <_ ( R x. M )'))
    pm = w.s([pre, mre], 'remulcld', A('( P x. M ) e. RR'))
    rm = w.s([rre, mre], 'remulcld', A('( R x. M ) e. RR'))
    bi = w.s([pm, rm, w.inst('efle')], 'syl2anc',
             A('( ( P x. M ) <_ ( R x. M ) <-> ( exp ` ( P x. M ) ) <_ ( exp ` ( R x. M ) ) )'))
    w.qed([bi, le], 'mpbid', A('( exp ` ( P x. M ) ) <_ ( exp ` ( R x. M ) )'))
    return w


# ------------------------------------------------------------- cbetr
@gen
def cbetr():
    w = WH('cbetr', 'Weakening an exponential bound to a larger rational coefficient.')
    mre = w.h('M e. RR'); m0 = w.h('0 <_ M'); pre = w.h('P e. RR'); rre = w.h('R e. RR')
    pr = w.h('P <_ R'); xre = w.h('X e. RR'); xb = w.h('X <_ ( exp ` ( P x. M ) )')
    mo = w.s([mre, m0, pre, rre, pr], 'cbemo', A('( exp ` ( P x. M ) ) <_ ( exp ` ( R x. M ) )'))
    c = Closure(w, PH, {'M': ('RR', mre), 'P': ('RR', pre), 'R': ('RR', rre)})
    pm = c.mem('( exp ` ( P x. M ) )', 'RR')
    rm = c.mem('( exp ` ( R x. M ) )', 'RR')
    w.qed([xre, pm, rm, xb, mo], 'letrd', A('X <_ ( exp ` ( R x. M ) )'))
    return w


# ------------------------------------------------------------- cbe8
@gen
def cbe8():
    w = WH('cbe8', 'Eight is below exp ( M / 4 ) once M is at least twelve: the constant '
                   'factors of the cost budget are all at most eight (Lean AlgBudget.lean, '
                   'the local ` h8 ` of costPieces_bound).')
    mre = w.h('M e. RR'); m12 = w.h('; 1 2 <_ M')
    # 2 < _e = ( exp ` 1 )
    e2 = w.s([w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e')], 'a1i', A('2 < _e'))
    de = w.s([w.s([], 'df-e', '_e = ( exp ` 1 )')], 'a1i', A('_e = ( exp ` 1 )'))
    e2b = w.s([e2, de], 'breqtrd', A('2 < ( exp ` 1 )'))
    e1re = w.s([w.s([], '1red', A('1 e. RR'))], 'reefcld', A('( exp ` 1 ) e. RR'))
    i2re = w.s([num.fact(w, '2', 'RR')], 'a1i', A('2 e. RR'))
    i20 = w.s([num.fact(w, '2', 'ge0')], 'a1i', A('0 <_ 2'))
    i3n0 = w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', A('3 e. NN0'))
    le = w.s([w.s([w.s([i2re, e1re, i3n0], '3jca', A('( 2 e. RR /\\ ( exp ` 1 ) e. RR /\\ 3 e. NN0 )')),
                   w.s([i20, w.s([e2b], 'ltled', A('2 <_ ( exp ` 1 )'))], 'jca',
                       A('( 0 <_ 2 /\\ 2 <_ ( exp ` 1 ) )'))], 'jca',
                  A('( ( 2 e. RR /\\ ( exp ` 1 ) e. RR /\\ 3 e. NN0 ) /\\ ( 0 <_ 2 /\\ 2 <_ ( exp ` 1 ) ) )')),
              w.inst('leexp1a')], 'syl', A('( 2 ^ 3 ) <_ ( ( exp ` 1 ) ^ 3 )'))
    cu = w.s([w.s([], 'cu2', '( 2 ^ 3 ) = 8')], 'a1i', A('( 2 ^ 3 ) = 8'))
    le8 = w.s([w.s([cu], 'eqcomd', A('8 = ( 2 ^ 3 )')), le], 'eqbrtrd', A('8 <_ ( ( exp ` 1 ) ^ 3 )'))
    # ( exp ` 1 ) ^ 3 = ( exp ` 3 )
    ee = w.s([w.s([w.s([], '1cnd', A('1 e. CC')), w.s([i3n0], 'nn0zd', A('3 e. ZZ'))], 'jca',
                  A('( 1 e. CC /\\ 3 e. ZZ )')), w.inst('efexp')], 'syl',
             A('( exp ` ( 3 x. 1 ) ) = ( ( exp ` 1 ) ^ 3 )'))
    m31 = w.s([w.s([num.closed(w, [], '3t1e3', '( 3 x. 1 ) = 3')], 'a1i', A('( 3 x. 1 ) = 3'))],
              'fveq2d', A('( exp ` ( 3 x. 1 ) ) = ( exp ` 3 )'))
    ee2 = w.s([w.s([m31], 'eqcomd', A('( exp ` 3 ) = ( exp ` ( 3 x. 1 ) )')), ee], 'eqtrd',
              A('( exp ` 3 ) = ( ( exp ` 1 ) ^ 3 )'))
    le83 = w.s([le8, w.s([ee2], 'eqcomd', A('( ( exp ` 1 ) ^ 3 ) = ( exp ` 3 )'))], 'breqtrd',
               A('8 <_ ( exp ` 3 )'))
    # exp 3 <_ exp ( M / 4 )
    c = Closure(w, PH, {'M': ('RR', mre)})
    qre = c.mem('( ( 1 / 4 ) x. M )', 'RR')
    i3re = w.s([num.fact(w, '3', 'RR')], 'a1i', A('3 e. RR'))
    hq = linarith(w, PH, [m12], '3 <_ ( ( 1 / 4 ) x. M )', closure=c)
    bi = w.s([i3re, qre, w.inst('efle')], 'syl2anc',
             A('( 3 <_ ( ( 1 / 4 ) x. M ) <-> ( exp ` 3 ) <_ ( exp ` ( ( 1 / 4 ) x. M ) ) )'))
    mono = w.s([bi, hq], 'mpbid', A('( exp ` 3 ) <_ ( exp ` ( ( 1 / 4 ) x. M ) )'))
    i8re = w.s([num.fact(w, '8', 'RR')], 'a1i', A('8 e. RR'))
    e3re = c.mem('( exp ` 3 )', 'RR')
    e4re = c.mem('( exp ` ( ( 1 / 4 ) x. M ) )', 'RR')
    w.qed([i8re, e3re, e4re, le83, mono], 'letrd', A('8 <_ ( exp ` ( ( 1 / 4 ) x. M ) )'))
    return w


# ------------------------------------------------------------- cbemul
@gen
def cbemul():
    w = WH('cbemul', 'The product of two quantities under exponential bounds is under the '
                     'exponential bound with the sum of the coefficients (Lean AlgBudget.lean, '
                     'the local ` mulE ` of costPieces_bound).')
    mre = w.h('M e. RR'); m0 = w.h('0 <_ M')
    pre = w.h('P e. RR'); qre = w.h('Q e. RR'); rre = w.h('R e. RR'); pqr = w.h('( P + Q ) <_ R')
    xre = w.h('X e. RR'); x0 = w.h('0 <_ X'); xb = w.h('X <_ ( exp ` ( P x. M ) )')
    yre = w.h('Y e. RR'); y0 = w.h('0 <_ Y'); yb = w.h('Y <_ ( exp ` ( Q x. M ) )')
    c = Closure(w, PH, {'M': ('RR', mre), 'P': ('RR', pre), 'Q': ('RR', qre), 'R': ('RR', rre),
                        'X': [('RR', xre), ('ge0', x0)], 'Y': [('RR', yre), ('ge0', y0)]})
    EP = '( exp ` ( P x. M ) )'; EQ = '( exp ` ( Q x. M ) )'
    prod = nlinarith(w, PH, [xb, yb, x0, y0], '( X x. Y ) <_ ( %s x. %s )' % (EP, EQ), closure=c)
    # ( exp ` ( P x. M ) ) x. ( exp ` ( Q x. M ) ) = ( exp ` ( ( P + Q ) x. M ) )
    pmc = c.mem('( P x. M )', 'CC'); qmc = c.mem('( Q x. M )', 'CC')
    ea = w.s([pmc, qmc, w.inst('efadd')], 'syl2anc', A('( exp ` ( ( P x. M ) + ( Q x. M ) ) ) = ( %s x. %s )' % (EP, EQ)))
    dd = w.s([c.mem('P', 'CC'), c.mem('Q', 'CC'), c.mem('M', 'CC')], 'adddird',
             A('( ( P + Q ) x. M ) = ( ( P x. M ) + ( Q x. M ) )'))
    eq = w.s([w.s([dd], 'fveq2d', A('( exp ` ( ( P + Q ) x. M ) ) = ( exp ` ( ( P x. M ) + ( Q x. M ) ) )')),
              ea], 'eqtrd', A('( exp ` ( ( P + Q ) x. M ) ) = ( %s x. %s )' % (EP, EQ)))
    st = w.s([prod, w.s([eq], 'eqcomd', A('( %s x. %s ) = ( exp ` ( ( P + Q ) x. M ) )' % (EP, EQ)))],
             'breqtrd', A('( X x. Y ) <_ ( exp ` ( ( P + Q ) x. M ) )'))
    pq = w.s([pre, qre], 'readdcld', A('( P + Q ) e. RR'))
    xy = w.s([xre, yre], 'remulcld', A('( X x. Y ) e. RR'))
    w.qed([mre, m0, pq, rre, pqr, xy, st], 'cbetr', A('( X x. Y ) <_ ( exp ` ( R x. M ) )'))
    return w


# ------------------------------------------------------------- cbesc
@gen
def cbesc():
    w = WH('cbesc', 'A constant factor of at most eight costs a quarter of M in the exponent '
                    '(the pattern Lean AlgBudget.lean writes with ` mulE ` and h2c, h4c, h5c, '
                    'h7c or h8 seven times).')
    mre = w.h('M e. RR'); m12 = w.h('; 1 2 <_ M')
    pre = w.h('P e. RR'); rre = w.h('R e. RR'); pr = w.h('( ( 1 / 4 ) + P ) <_ R')
    kre = w.h('K e. RR'); k0 = w.h('0 <_ K'); k8 = w.h('K <_ 8')
    xre = w.h('X e. RR'); x0 = w.h('0 <_ X'); xb = w.h('X <_ ( exp ` ( P x. M ) )')
    c = Closure(w, PH, {'M': ('RR', mre), 'P': ('RR', pre), 'R': ('RR', rre),
                        'K': [('RR', kre), ('ge0', k0)], 'X': [('RR', xre), ('ge0', x0)]})
    m0 = linarith(w, PH, [m12], '0 <_ M', closure=c)
    e8 = w.s([mre, m12], 'cbe8', A('8 <_ ( exp ` ( ( 1 / 4 ) x. M ) )'))
    i4re = w.s([num.fact(w, '( 1 / 4 )', 'RR')], 'a1i', A('( 1 / 4 ) e. RR'))
    i8re = w.s([num.fact(w, '8', 'RR')], 'a1i', A('8 e. RR'))
    e4re = c.mem('( exp ` ( ( 1 / 4 ) x. M ) )', 'RR')
    kb = w.s([kre, i8re, e4re, k8, e8], 'letrd', A('K <_ ( exp ` ( ( 1 / 4 ) x. M ) )'))
    w.qed([mre, m0, i4re, pre, rre, pr, kre, k0, kb, xre, x0, xb], 'cbemul',
          A('( K x. X ) <_ ( exp ` ( R x. M ) )'))
    return w


# ------------------------------------------------------------- cbelin
@gen
def cbelin():
    w = WH('cbelin', 'A quantity below 1 + P M is below exp ( P M ) : the route used for '
                     'the linear summand T + 2 of step 3 of the cost budget (Lean '
                     'AlgBudget.lean, ` hT2E ` , from Real.add_one_le_exp).')
    mre = w.h('M e. RR'); m0 = w.h('0 < M'); pre = w.h('P e. RR'); p0 = w.h('0 < P')
    xre = w.h('X e. RR'); xb = w.h('X <_ ( 1 + ( P x. M ) )')
    c = Closure(w, PH, {'M': [('RR', mre), ('gt0', m0)], 'P': [('RR', pre), ('gt0', p0)],
                        'X': ('RR', xre)})
    pm = c.mem('( P x. M )', 'RR+')
    gt = w.s([pm, w.inst('efgt1p')], 'syl', A('( 1 + ( P x. M ) ) < ( exp ` ( P x. M ) )'))
    one = w.s([], '1red', A('1 e. RR'))
    s1 = w.s([one, c.mem('( P x. M )', 'RR')], 'readdcld', A('( 1 + ( P x. M ) ) e. RR'))
    ef = c.mem('( exp ` ( P x. M ) )', 'RR')
    lt = w.s([xre, s1, ef, xb, gt], 'lelttrd', A('X < ( exp ` ( P x. M ) )'))
    w.qed([lt], 'ltled', A('X <_ ( exp ` ( P x. M ) )'))
    return w


def main():
    ok = True
    for fn in GENS:
        if only and fn.__name__ not in only:
            continue
        ok = fn().run() and ok
    return ok

if __name__ == '__main__':
    sys.exit(0 if main() else 1)
