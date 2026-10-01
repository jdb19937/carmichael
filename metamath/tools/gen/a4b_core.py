"""Sortie A4b, batch 5: costPieces_bound itself, the real-number heart of the
cost budget (Lean AlgBudget.lean lines 41-267).

    MM_DB=sorties/a4b.mm python3 tools/gen/a4b_core.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from a2lib import WH
from a4blib import scale, emul, lit, EXP
from a4b_term import I1, I2, I4, TERM1, TERM2, TERM3, TERM4, BUDGET
from cl import Closure
from lin import linarith, nlinarith
import num

only = [a for a in sys.argv[1:] if not a.startswith('-')]
PH = 'ph'
def A(f): return '( ph -> %s )' % f


def cbcore():
    w = WH('cbcore', 'The real-number heart of the cost bound: with the second and third '
                     'iterated logarithms at least 1 and 12 , the scales in the window, and '
                     'the integer quantities of CostPieces replaced by reals under the bounds '
                     'the wrapper supplies, the budget is at most exp ( 100 M ) where M is '
                     'the product of the two iterated logarithms (Lean AlgBudget.lean, '
                     'costPieces_bound).')
    cre = w.h('C e. RR'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
    are = w.h('A e. RR'); a1 = w.h('1 <_ A')
    bre = w.h('B e. RR'); b12 = w.h('; 1 2 <_ B'); beq = w.h('B = ( log ` A )')
    hlc = w.h('( log ` ( 4 x. C ) ) <_ B')
    mre = w.h('M e. RR'); meq = w.h('M = ( A x. B )')
    zre = w.h('Z e. RR'); zlo = w.h('( C x. M ) <_ Z'); zhi = w.h('Z <_ ( ( 4 x. C ) x. M )')
    yre = w.h('Y e. RR'); yz = w.h('Y <_ ( 4 x. Z )')
    tre = w.h('T e. RR'); tlo = w.h('( 3 x. A ) <_ T'); thi = w.h('T <_ ( 5 x. A )')
    vre = w.h('V e. RR'); vz = w.h('V <_ Z')
    wre = w.h('W e. RR'); wz = w.h('W <_ Z')
    lre = w.h('L e. RR'); l0 = w.h('0 <_ L'); lzt = w.h('L <_ ( Z ^c T )')
    xre = w.h('X e. RR'); xeq = w.h('X = ( L ^ 5 )')
    ure = w.h('U e. RR'); u0 = w.h('0 <_ U'); usx = w.h('U <_ ( sqrt ` X )')
    kre = w.h('K e. RR'); k0 = w.h('0 <_ K'); kx = w.h('K <_ ( X ^c ( ; 7 9 / ; ; 1 0 0 ) )')
    dre = w.h('D e. RR'); d0 = w.h('0 <_ D'); dtw = w.h('D <_ ( 2 ^c T )')
    pre = w.h('P e. RR'); p0 = w.h('0 <_ P'); pd = w.h('P <_ D')
    sre = w.h('S e. RR'); s0 = w.h('0 <_ S'); sd = w.h('S <_ D')

    c = Closure(w, PH, {'C': ('RR', cre), 'A': ('RR', are), 'B': ('RR', bre), 'M': ('RR', mre),
                        'Z': ('RR', zre), 'Y': ('RR', yre), 'T': ('RR', tre), 'V': ('RR', vre),
                        'W': ('RR', wre), 'L': [('RR', lre), ('ge0', l0)], 'X': ('RR', xre),
                        'U': [('RR', ure), ('ge0', u0)], 'K': [('RR', kre), ('ge0', k0)],
                        'D': [('RR', dre), ('ge0', d0)], 'P': [('RR', pre), ('ge0', p0)],
                        'S': [('RR', sre), ('ge0', s0)]})
    # the M algebra
    m12 = w.s([are, a1, bre, b12, mre, meq], 'cbm12', A('; 1 2 <_ M'))
    m0 = linarith(w, PH, [m12], '0 <_ M', closure=c)
    c.have('M', 'ge0', m0)
    mb = w.s([are, a1, bre, b12, mre, meq], 'cbmb', A('B <_ M'))
    ma = w.s([are, a1, bre, b12, mre, meq], 'cbma', A('( ; 1 2 x. A ) <_ M'))
    z12 = w.s([cre, c1000, mre, m12, zre, zlo], 'cbz12', A('; ; ; ; 1 2 0 0 0 <_ Z'))
    mz = w.s([cre, c1000, mre, m12, zre, zlo], 'cbmz', A('M <_ Z'))
    z1 = linarith(w, PH, [z12], '1 <_ Z', closure=c)
    z0 = linarith(w, PH, [z12], '0 <_ Z', closure=c)
    c.have('Z', 'ge0', z0)
    # logarithms
    lz = w.s([cre, c1000, are, a1, bre, b12, beq, hlc, mre, meq, zre, z1, zhi], 'cblz',
             A('( log ` Z ) <_ ( 3 x. B )'))
    lz0 = w.s([zre, z1, w.inst('logge0')], 'syl2anc', A('0 <_ ( log ` Z )'))
    z0s = linarith(w, PH, [z12], '0 < Z', closure=c)
    lzre = w.s([zre, z0s], 'elrpd', A('Z e. RR+'))
    lzre = w.s([lzre], 'relogcld', A('( log ` Z ) e. RR'))
    c.have('( log ` Z )', 'RR', lzre)
    c.have('( log ` Z )', 'ge0', lz0)
    # the atoms
    ze = w.s([mre, bre, mb, zre, z1, lz], 'cbze', A('Z <_ %s' % EXP('3')))
    t0 = linarith(w, PH, [tlo, a1], '0 <_ T', closure=c)
    c.have('T', 'ge0', t0)
    tlzs = w.s([are, a1, bre, mre, meq, tre, thi, lzre, lz0, lz], 'cbtlz',
               A('( T x. ( log ` Z ) ) <_ ( ; 1 5 x. M )'))
    zte = w.s([mre, zre, z1, tre, tlzs], 'cbzte', A('( Z ^c T ) <_ %s' % EXP('; 1 5')))
    lb = w.s([lre, c.mem('( Z ^c T )', 'RR'), c.mem(EXP('; 1 5'), 'RR'), lzt, zte], 'letrd',
             A('L <_ %s' % EXP('; 1 5')))
    xe = w.s([mre, lre, l0, lb, xre, xeq], 'cbxe', A('X <_ %s' % EXP('; 7 5')))
    x0 = w.s([w.s([lre, w.s([num.nn0(w, 5)], 'a1i', A('5 e. NN0')), l0], 'expge0d',
                  A('0 <_ ( L ^ 5 )')), xeq], 'breqtrrd', A('0 <_ X'))
    c.have('X', 'ge0', x0)
    ke = w.s([mre, xre, x0, xe, kre, k0, kx], 'cbke', A('K <_ %s' % EXP('( ; ; 2 3 7 / 4 )')))
    sxe = w.s([mre, xre, x0, xe, ure, u0, usx], 'cbsxe', A('U <_ %s' % EXP('( ; 7 5 / 2 )')))
    twe = w.s([are, mre, ma, tre, t0, thi], 'cbtwe', A('( 2 ^c T ) <_ %s' % EXP('( 5 / ; 1 2 )')))
    E512 = EXP('( 5 / ; 1 2 )')
    de = w.s([dre, c.mem('( 2 ^c T )', 'RR'), c.mem(E512, 'RR'), dtw, twe], 'letrd',
             A('D <_ %s' % E512))
    pe = w.s([pre, dre, c.mem(E512, 'RR'), pd, de], 'letrd', A('P <_ %s' % E512))
    se = w.s([sre, dre, c.mem(E512, 'RR'), sd, de], 'letrd', A('S <_ %s' % E512))
    # the four summands
    tz = linarith(w, PH, [thi, ma, mz, z0], 'T <_ ( 5 x. Z )', closure=c)
    t1 = w.s([mre, m12, zre, z12, ze, vre, vz, yre, yz, wre, wz, tre, tz], 'cbt1',
             A('%s <_ %s' % (TERM1, EXP('( ; 2 5 / 4 )'))))
    t2 = w.s([mre, m12, ure, u0, sxe, dre, d0, de, tre, t0, thi, are, ma, kre, k0, ke], 'cbt2',
             A('%s <_ %s' % (TERM2, EXP('( ; ; 2 9 3 / 3 )'))))
    t3 = w.s([mre, m12, lre, l0, lb, pre, p0, pe], 'cbt3',
             A('%s <_ %s' % (TERM3, EXP('( ; ; 1 9 1 / ; 1 2 )'))))
    t4 = w.s([mre, m12, ure, u0, sxe, sre, s0, se], 'cbt4',
             A('%s <_ %s' % (TERM4, EXP('( ; ; 4 6 1 / ; 1 2 )'))))
    R = '( ; ; 2 9 3 / 3 )'
    def weaken(st, P, expr):
        return w.s([mre, m0, lit(w, c, P), lit(w, c, R),
                    linarith(w, PH, [], '%s <_ %s' % (P, R), closure=c),
                    c.mem(expr, 'RR'), st], 'cbetr', A('%s <_ %s' % (expr, EXP(R))))
    t1w = weaken(t1, '( ; 2 5 / 4 )', TERM1)
    t3w = weaken(t3, '( ; ; 1 9 1 / ; 1 2 )', TERM3)
    t4w = weaken(t4, '( ; ; 4 6 1 / ; 1 2 )', TERM4)
    hle = linarith(w, PH, [t1w, t2, t3w, t4w], '%s <_ ( 4 x. %s )' % (BUDGET, EXP(R)), closure=c)
    fin = scale(w, c, mre, m12, '4', R, '( ; ; ; 1 1 7 5 / ; 1 2 )', BUDGET,
                c.mem(BUDGET, 'RR'), hle)
    w.qed([mre, m0, lit(w, c, '( ; ; ; 1 1 7 5 / ; 1 2 )'), lit(w, c, '; ; 1 0 0'),
           linarith(w, PH, [], '( ; ; ; 1 1 7 5 / ; 1 2 ) <_ ; ; 1 0 0', closure=c),
           c.mem(BUDGET, 'RR'), fin], 'cbetr', A('%s <_ %s' % (BUDGET, EXP('; ; 1 0 0'))))
    return w


if __name__ == '__main__':
    sys.exit(0 if cbcore().run() else 1)
