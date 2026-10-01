"""Sortie A4b, batch 3: the six atoms of the cost budget under exponential bounds
(Lean AlgBudget.lean, the block "Atoms" of costPieces_bound).

    MM_DB=sorties/a4b.mm python3 tools/gen/a4b_atom.py [labels]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from a2lib import WH, sqrtle2
from a3lib import lineq
from cl import Closure
from lin import linarith, nlinarith
import num

only = [a for a in sys.argv[1:] if not a.startswith('-')]
GENS = []
def gen(fn):
    GENS.append(fn); return fn
PH = 'ph'
def A(f): return '( ph -> %s )' % f


@gen
def cbze():
    w = WH('cbze', 'The first scale is below exp ( 3 M ) (Lean AlgBudget.lean, ` hzE ` of '
                   'costPieces_bound).')
    mre = w.h('M e. RR'); bre = w.h('B e. RR'); bm = w.h('B <_ M')
    zre = w.h('Z e. RR'); z1 = w.h('1 <_ Z'); lz = w.h('( log ` Z ) <_ ( 3 x. B )')
    c = Closure(w, PH, {'M': ('RR', mre), 'B': ('RR', bre), 'Z': ('RR', zre)})
    z0 = linarith(w, PH, [z1], '0 < Z', closure=c)
    c.have('Z', 'gt0', z0)
    zrp = w.s([zre, z0], 'elrpd', A('Z e. RR+'))
    el = w.s([zrp, w.inst('reeflog')], 'syl', A('( exp ` ( log ` Z ) ) = Z'))
    hle = linarith(w, PH, [lz, bm], '( log ` Z ) <_ ( 3 x. M )', closure=c)
    bi = w.s([c.mem('( log ` Z )', 'RR'), c.mem('( 3 x. M )', 'RR'), w.inst('efle')], 'syl2anc',
             A('( ( log ` Z ) <_ ( 3 x. M ) <-> ( exp ` ( log ` Z ) ) <_ ( exp ` ( 3 x. M ) ) )'))
    st = w.s([hle, bi], 'mpbid', A('( exp ` ( log ` Z ) ) <_ ( exp ` ( 3 x. M ) )'))
    w.qed([w.s([el], 'eqcomd', A('Z = ( exp ` ( log ` Z ) )')), st], 'eqbrtrd',
          A('Z <_ ( exp ` ( 3 x. M ) )'))
    return w


@gen
def cbzte():
    w = WH('cbzte', 'The first scale to the power of the reservoir size is below exp ( 15 M ) '
                    '(Lean AlgBudget.lean, ` hzT ` of costPieces_bound).')
    mre = w.h('M e. RR'); zre = w.h('Z e. RR'); z1 = w.h('1 <_ Z')
    tre = w.h('T e. RR'); htl = w.h('( T x. ( log ` Z ) ) <_ ( ; 1 5 x. M )')
    c = Closure(w, PH, {'M': ('RR', mre), 'Z': ('RR', zre), 'T': ('RR', tre)})
    z0 = linarith(w, PH, [z1], '0 < Z', closure=c)
    c.have('Z', 'gt0', z0)
    zne = w.s([w.s([zre, z0], 'elrpd', A('Z e. RR+'))], 'rpne0d', A('Z =/= 0'))
    eq = w.s([c.mem('Z', 'CC'), zne, c.mem('T', 'CC'), w.inst('cxpef')], 'syl3anc',
             A('( Z ^c T ) = ( exp ` ( T x. ( log ` Z ) ) )'))
    bi = w.s([c.mem('( T x. ( log ` Z ) )', 'RR'), c.mem('( ; 1 5 x. M )', 'RR'), w.inst('efle')],
             'syl2anc', A('( ( T x. ( log ` Z ) ) <_ ( ; 1 5 x. M ) <-> ( exp ` ( T x. ( log ` Z ) ) ) <_ ( exp ` ( ; 1 5 x. M ) ) )'))
    st = w.s([htl, bi], 'mpbid', A('( exp ` ( T x. ( log ` Z ) ) ) <_ ( exp ` ( ; 1 5 x. M ) )'))
    w.qed([eq, st], 'eqbrtrd', A('( Z ^c T ) <_ ( exp ` ( ; 1 5 x. M ) )'))
    return w


@gen
def cbtwe():
    w = WH('cbtwe', 'Two to the power of the reservoir size is below exp ( 5 M / 12 ) '
                    '(Lean AlgBudget.lean, ` htwE ` of costPieces_bound; set.mm has '
                    '` log2le1 ` where Lean uses the nine-digit bound on log 2 , so the '
                    'coefficient is 5 / 12 rather than 1 / 3 ).')
    are = w.h('A e. RR'); mre = w.h('M e. RR'); ma = w.h('( ; 1 2 x. A ) <_ M')
    tre = w.h('T e. RR'); t0 = w.h('0 <_ T'); thi = w.h('T <_ ( 5 x. A )')
    c = Closure(w, PH, {'A': ('RR', are), 'M': ('RR', mre), 'T': [('RR', tre), ('ge0', t0)]})
    l2re = c.mem('( log ` 2 )', 'RR')
    l2le = w.s([w.s([], 'log2le1', '( log ` 2 ) < 1')], 'a1i', A('( log ` 2 ) < 1'))
    l2le2 = w.s([l2le], 'ltled', A('( log ` 2 ) <_ 1'))
    i2re = w.s([num.fact(w, '2', 'RR')], 'a1i', A('2 e. RR'))
    i2ge1 = w.s([num.fact(w, '2', 'ge1')], 'a1i', A('1 <_ 2'))
    l20 = w.s([i2re, i2ge1, w.inst('logge0')], 'syl2anc', A('0 <_ ( log ` 2 )'))
    c.have('( log ` 2 )', 'ge0', l20)
    hle = nlinarith(w, PH, [l2le2, l20, t0, thi, ma],
                    '( T x. ( log ` 2 ) ) <_ ( ( 5 / ; 1 2 ) x. M )', closure=c)
    i2cn = w.s([num.cc(w, '2')], 'a1i', A('2 e. CC'))
    i2ne = w.s([num.fact(w, '2', 'ne0')], 'a1i', A('2 =/= 0'))
    eq = w.s([i2cn, i2ne, c.mem('T', 'CC'), w.inst('cxpef')], 'syl3anc',
             A('( 2 ^c T ) = ( exp ` ( T x. ( log ` 2 ) ) )'))
    bi = w.s([c.mem('( T x. ( log ` 2 ) )', 'RR'), c.mem('( ( 5 / ; 1 2 ) x. M )', 'RR'),
              w.inst('efle')], 'syl2anc',
             A('( ( T x. ( log ` 2 ) ) <_ ( ( 5 / ; 1 2 ) x. M ) <-> ( exp ` ( T x. ( log ` 2 ) ) ) <_ ( exp ` ( ( 5 / ; 1 2 ) x. M ) ) )'))
    st = w.s([hle, bi], 'mpbid', A('( exp ` ( T x. ( log ` 2 ) ) ) <_ ( exp ` ( ( 5 / ; 1 2 ) x. M ) )'))
    w.qed([eq, st], 'eqbrtrd', A('( 2 ^c T ) <_ ( exp ` ( ( 5 / ; 1 2 ) x. M ) )'))
    return w


@gen
def cbxe():
    w = WH('cbxe', 'The scan bound X = L ^ 5 is below exp ( 75 M ) (Lean AlgBudget.lean, '
                   '` hxE ` of costPieces_bound).')
    mre = w.h('M e. RR'); lre = w.h('L e. RR'); l0 = w.h('0 <_ L')
    lb = w.h('L <_ ( exp ` ( ; 1 5 x. M ) )')
    xre = w.h('X e. RR'); xeq = w.h('X = ( L ^ 5 )')
    c = Closure(w, PH, {'M': ('RR', mre), 'L': [('RR', lre), ('ge0', l0)], 'X': ('RR', xre)})
    E = '( exp ` ( ; 1 5 x. M ) )'
    ere = c.mem(E, 'RR')
    i5n0 = w.s([num.nn0(w, 5)], 'a1i', A('5 e. NN0'))
    le = w.s([w.s([w.s([lre, ere, i5n0], '3jca', A('( L e. RR /\\ %s e. RR /\\ 5 e. NN0 )' % E)),
                   w.s([l0, lb], 'jca', A('( 0 <_ L /\\ L <_ %s )' % E))], 'jca',
                  A('( ( L e. RR /\\ %s e. RR /\\ 5 e. NN0 ) /\\ ( 0 <_ L /\\ L <_ %s ) )' % (E, E))),
              w.inst('leexp1a')], 'syl', A('( L ^ 5 ) <_ ( %s ^ 5 )' % E))
    ee = w.s([c.mem('( ; 1 5 x. M )', 'CC'), w.s([i5n0], 'nn0zd', A('5 e. ZZ')), w.inst('efexp')],
             'syl2anc', A('( exp ` ( 5 x. ( ; 1 5 x. M ) ) ) = ( %s ^ 5 )' % E))
    ex = lineq(w, PH, [], '( 5 x. ( ; 1 5 x. M ) )', '( ; 7 5 x. M )', {'M': ('RR', mre)},
               c.mem('( 5 x. ( ; 1 5 x. M ) )', 'RR'), c.mem('( ; 7 5 x. M )', 'RR'), linarith)
    ee2 = w.s([w.s([w.s([ex], 'eqcomd', A('( ; 7 5 x. M ) = ( 5 x. ( ; 1 5 x. M ) )'))], 'fveq2d',
                   A('( exp ` ( ; 7 5 x. M ) ) = ( exp ` ( 5 x. ( ; 1 5 x. M ) ) )')), ee], 'eqtrd',
              A('( exp ` ( ; 7 5 x. M ) ) = ( %s ^ 5 )' % E))
    st = w.s([le, w.s([ee2], 'eqcomd', A('( %s ^ 5 ) = ( exp ` ( ; 7 5 x. M ) )' % E))], 'breqtrd',
             A('( L ^ 5 ) <_ ( exp ` ( ; 7 5 x. M ) )'))
    w.qed([xeq, st], 'eqbrtrd', A('X <_ ( exp ` ( ; 7 5 x. M ) )'))
    return w


@gen
def cbke():
    w = WH('cbke', 'The scan index is below exp ( 237 M / 4 ) (Lean AlgBudget.lean, ` hkE ` '
                   'of costPieces_bound).')
    mre = w.h('M e. RR'); xre = w.h('X e. RR'); x0 = w.h('0 <_ X')
    xb = w.h('X <_ ( exp ` ( ; 7 5 x. M ) )')
    kre = w.h('K e. RR'); k0 = w.h('0 <_ K')
    kb = w.h('K <_ ( X ^c ( ; 7 9 / ; ; 1 0 0 ) )')
    c = Closure(w, PH, {'M': ('RR', mre), 'X': [('RR', xre), ('ge0', x0)],
                        'K': [('RR', kre), ('ge0', k0)]})
    E = '( exp ` ( ; 7 5 x. M ) )'
    R = '( ; 7 9 / ; ; 1 0 0 )'
    ere = c.mem(E, 'RR')
    rre = w.s([num.fact(w, R, 'RR')], 'a1i', A('%s e. RR' % R))
    r0 = w.s([num.fact(w, R, 'ge0')], 'a1i', A('0 <_ %s' % R))
    mono = w.s([w.s([w.s([xre, ere, rre], '3jca', A('( X e. RR /\\ %s e. RR /\\ %s e. RR )' % (E, R))),
                     w.s([x0, r0], 'jca', A('( 0 <_ X /\\ 0 <_ %s )' % R)), xb], '3jca',
                    A('( ( X e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ ( 0 <_ X /\\ 0 <_ %s ) /\\ X <_ %s )' % (E, R, R, E))),
                w.inst('cxple2a')], 'syl', A('( X ^c %s ) <_ ( %s ^c %s )' % (R, E, R)))
    ec = w.s([c.mem('( ; 7 5 x. M )', 'RR'), rre, w.inst('efcxp')], 'syl2anc',
             A('( %s ^c %s ) = ( exp ` ( %s x. ( ; 7 5 x. M ) ) )' % (E, R, R)))
    ex = lineq(w, PH, [], '( %s x. ( ; 7 5 x. M ) )' % R, '( ( ; ; 2 3 7 / 4 ) x. M )',
               {'M': ('RR', mre)}, c.mem('( %s x. ( ; 7 5 x. M ) )' % R, 'RR'),
               c.mem('( ( ; ; 2 3 7 / 4 ) x. M )', 'RR'), linarith)
    ec2 = w.s([ec, w.s([ex], 'fveq2d',
                       A('( exp ` ( %s x. ( ; 7 5 x. M ) ) ) = ( exp ` ( ( ; ; 2 3 7 / 4 ) x. M ) )' % R))],
              'eqtrd', A('( %s ^c %s ) = ( exp ` ( ( ; ; 2 3 7 / 4 ) x. M ) )' % (E, R)))
    st = w.s([mono, ec2], 'breqtrd', A('( X ^c %s ) <_ ( exp ` ( ( ; ; 2 3 7 / 4 ) x. M ) )' % R))
    w.qed([kre, c.mem('( X ^c %s )' % R, 'RR'), c.mem('( exp ` ( ( ; ; 2 3 7 / 4 ) x. M ) )', 'RR'),
           kb, st], 'letrd', A('K <_ ( exp ` ( ( ; ; 2 3 7 / 4 ) x. M ) )'))
    return w


@gen
def cbsxe():
    w = WH('cbsxe', 'The integer square root of the scan bound is below exp ( 75 M / 2 ) '
                    '(Lean AlgBudget.lean, ` hsxE ` of costPieces_bound).')
    mre = w.h('M e. RR'); xre = w.h('X e. RR'); x0 = w.h('0 <_ X')
    xb = w.h('X <_ ( exp ` ( ; 7 5 x. M ) )')
    ure = w.h('U e. RR'); u0 = w.h('0 <_ U'); ub = w.h('U <_ ( sqrt ` X )')
    c = Closure(w, PH, {'M': ('RR', mre), 'X': [('RR', xre), ('ge0', x0)],
                        'U': [('RR', ure), ('ge0', u0)]})
    E = '( exp ` ( ( ; 7 5 / 2 ) x. M ) )'
    ere = c.mem(E, 'RR')
    e0 = c.ge0(E)
    i2n0 = w.s([num.nn0(w, 2)], 'a1i', A('2 e. NN0'))
    ee = w.s([c.mem('( ( ; 7 5 / 2 ) x. M )', 'CC'), w.s([i2n0], 'nn0zd', A('2 e. ZZ')),
              w.inst('efexp')], 'syl2anc',
             A('( exp ` ( 2 x. ( ( ; 7 5 / 2 ) x. M ) ) ) = ( %s ^ 2 )' % E))
    ex = lineq(w, PH, [], '( 2 x. ( ( ; 7 5 / 2 ) x. M ) )', '( ; 7 5 x. M )', {'M': ('RR', mre)},
               c.mem('( 2 x. ( ( ; 7 5 / 2 ) x. M ) )', 'RR'), c.mem('( ; 7 5 x. M )', 'RR'), linarith)
    ee2 = w.s([w.s([w.s([ex], 'eqcomd', A('( ; 7 5 x. M ) = ( 2 x. ( ( ; 7 5 / 2 ) x. M ) )'))],
                   'fveq2d', A('( exp ` ( ; 7 5 x. M ) ) = ( exp ` ( 2 x. ( ( ; 7 5 / 2 ) x. M ) ) )')),
               ee], 'eqtrd', A('( exp ` ( ; 7 5 x. M ) ) = ( %s ^ 2 )' % E))
    hsq = w.s([xb, ee2], 'breqtrd', A('X <_ ( %s ^ 2 )' % E))
    sq = sqrtle2(w, PH, 'X', E, xre, x0, ere, e0, hsq)
    w.qed([ure, c.mem('( sqrt ` X )', 'RR'), ere, ub, sq], 'letrd', A('U <_ %s' % E))
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
