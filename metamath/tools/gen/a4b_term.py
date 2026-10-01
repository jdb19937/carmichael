"""Sortie A4b, batch 4: the four summands of the cost budget and the real-number
heart costPieces_bound (Lean AlgBudget.lean lines 41-267).

    MM_DB=sorties/a4b.mm python3 tools/gen/a4b_term.py [labels]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from a2lib import WH
from a4blib import scale, emul, lit, EXP
from cl import Closure
from lin import linarith, nlinarith
import num

only = [a for a in sys.argv[1:] if not a.startswith('-')]
GENS = []
def gen(fn):
    GENS.append(fn); return fn
PH = 'ph'
def A(f): return '( ph -> %s )' % f

I1 = '( ( ( V + Y ) + W ) + 6 )'
I2 = '( ( T + 2 ) + ( D x. ( U + 3 ) ) )'
I4 = '( ( U + S ) + 6 )'
TERM1 = '( ( ( ( Z + 1 ) x. %s ) + ( 2 x. T ) ) + 2 )' % I1
TERM2 = '( K x. %s )' % I2
TERM3 = '( ( P x. ( L + 3 ) ) + 1 )'
TERM4 = '( ( S x. %s ) + 4 )' % I4
_e4 = '( %s + %s )' % (TERM1, TERM2)
_e5 = '( %s + ( P x. ( L + 3 ) ) )' % _e4
_e6 = '( %s + 1 )' % _e5
_e7 = '( %s + ( S x. %s ) )' % (_e6, I4)
BUDGET = '( %s + 4 )' % _e7


def ge1(w, c, mre, m0, P):
    """1 <_ ( exp ` ( P x. M ) ) for a nonnegative literal P"""
    return w.s([mre, m0, lit(w, c, P), lit(w, c, P, 'ge0')], 'cbege1', A('1 <_ %s' % EXP(P)))


@gen
def cbt1():
    w = WH('cbt1', 'Step 2 of the cost budget, the reservoir sieve, is below exp ( 25 M / 4 ) '
                   '(Lean AlgBudget.lean, ` term1 ` of costPieces_bound).')
    mre = w.h('M e. RR'); m12 = w.h('; 1 2 <_ M')
    zre = w.h('Z e. RR'); z12 = w.h('; ; ; ; 1 2 0 0 0 <_ Z'); zb = w.h('Z <_ %s' % EXP('3'))
    vre = w.h('V e. RR'); vz = w.h('V <_ Z')
    yre = w.h('Y e. RR'); yz = w.h('Y <_ ( 4 x. Z )')
    wre = w.h('W e. RR'); wz = w.h('W <_ Z')
    tre = w.h('T e. RR'); tz = w.h('T <_ ( 5 x. Z )')
    c = Closure(w, PH, {'M': ('RR', mre), 'Z': ('RR', zre), 'V': ('RR', vre), 'Y': ('RR', yre),
                        'W': ('RR', wre), 'T': ('RR', tre)})
    m0 = linarith(w, PH, [m12], '0 <_ M', closure=c)
    z0 = linarith(w, PH, [z12], '0 <_ Z', closure=c)
    sq = nlinarith(w, PH, [z12, vz, yz, wz, tz], '%s <_ ( 7 x. ( Z x. Z ) )' % TERM1, closure=c)
    zz = emul(w, c, mre, m0, '3', '3', '6', 'Z', 'Z', zre, z0, zb, zre, z0, zb)
    hle = linarith(w, PH, [sq, zz], '%s <_ ( 7 x. %s )' % (TERM1, EXP('6')), closure=c)
    scale(w, c, mre, m12, '7', '6', '( ; 2 5 / 4 )', TERM1, c.mem(TERM1, 'RR'), hle)
    w.qed([], 'idi', A('%s <_ %s' % (TERM1, EXP('( ; 2 5 / 4 )'))))
    return w


@gen
def cbt2():
    w = WH('cbt2', 'Step 3 of the cost budget, the scan, is below exp ( 293 M / 3 ) '
                   '(Lean AlgBudget.lean, ` hsx3 ` , ` htwsx ` , ` hT2E ` , ` hinner ` and '
                   '` term2 ` of costPieces_bound).')
    mre = w.h('M e. RR'); m12 = w.h('; 1 2 <_ M')
    ure = w.h('U e. RR'); u0 = w.h('0 <_ U'); ub = w.h('U <_ %s' % EXP('( ; 7 5 / 2 )'))
    dre = w.h('D e. RR'); d0 = w.h('0 <_ D'); db = w.h('D <_ %s' % EXP('( 5 / ; 1 2 )'))
    tre = w.h('T e. RR'); t0 = w.h('0 <_ T'); thi = w.h('T <_ ( 5 x. A )')
    are = w.h('A e. RR'); ma = w.h('( ; 1 2 x. A ) <_ M')
    kre = w.h('K e. RR'); k0 = w.h('0 <_ K'); kb = w.h('K <_ %s' % EXP('( ; ; 2 3 7 / 4 )'))
    c = Closure(w, PH, {'M': ('RR', mre), 'U': [('RR', ure), ('ge0', u0)],
                        'D': [('RR', dre), ('ge0', d0)], 'T': [('RR', tre), ('ge0', t0)],
                        'A': ('RR', are), 'K': [('RR', kre), ('ge0', k0)]})
    m0 = linarith(w, PH, [m12], '0 <_ M', closure=c)
    m0s = linarith(w, PH, [m12], '0 < M', closure=c)
    # U + 3
    e1 = ge1(w, c, mre, m0, '( ; 7 5 / 2 )')
    h1 = linarith(w, PH, [ub, e1], '( U + 3 ) <_ ( 4 x. %s )' % EXP('( ; 7 5 / 2 )'), closure=c)
    u3 = scale(w, c, mre, m12, '4', '( ; 7 5 / 2 )', '( ; ; 1 5 1 / 4 )', '( U + 3 )',
               c.mem('( U + 3 )', 'RR'), h1)
    u30 = linarith(w, PH, [u0], '0 <_ ( U + 3 )', closure=c)
    # D ( U + 3 )
    twsx = emul(w, c, mre, m0, '( 5 / ; 1 2 )', '( ; ; 1 5 1 / 4 )', '( ; ; 2 2 9 / 6 )',
                'D', '( U + 3 )', dre, d0, db, c.mem('( U + 3 )', 'RR'), u30, u3)
    # T + 2
    hlin = linarith(w, PH, [thi, ma, m12], '( T + 2 ) <_ ( 1 + ( ( ; ; 2 2 9 / 6 ) x. M ) )', closure=c)
    t2re = c.mem('( T + 2 )', 'RR')
    t2b = w.s([mre, m0s, lit(w, c, '( ; ; 2 2 9 / 6 )'),
               w.s([num.fact(w, '( ; ; 2 2 9 / 6 )', 'gt0')], 'a1i', A('0 < ( ; ; 2 2 9 / 6 )')),
               t2re, hlin], 'cbelin', A('( T + 2 ) <_ %s' % EXP('( ; ; 2 2 9 / 6 )')))
    # the inner sum
    h2 = linarith(w, PH, [t2b, twsx], '%s <_ ( 2 x. %s )' % (I2, EXP('( ; ; 2 2 9 / 6 )')), closure=c)
    inn = scale(w, c, mre, m12, '2', '( ; ; 2 2 9 / 6 )', '( ; ; 4 6 1 / ; 1 2 )', I2,
                c.mem(I2, 'RR'), h2)
    inn0 = c.ge0(I2)
    emul(w, c, mre, m0, '( ; ; 2 3 7 / 4 )', '( ; ; 4 6 1 / ; 1 2 )', '( ; ; 2 9 3 / 3 )',
         'K', I2, kre, k0, kb, c.mem(I2, 'RR'), inn0, inn)
    w.qed([], 'idi', A('%s <_ %s' % (TERM2, EXP('( ; ; 2 9 3 / 3 )'))))
    return w


@gen
def cbt3():
    w = WH('cbt3', 'Step 4 of the cost budget, the extraction, is below exp ( 191 M / 12 ) '
                   '(Lean AlgBudget.lean, ` hL3 ` , ` hPL ` and ` term3 ` of costPieces_bound).')
    mre = w.h('M e. RR'); m12 = w.h('; 1 2 <_ M')
    lre = w.h('L e. RR'); l0 = w.h('0 <_ L'); lb = w.h('L <_ %s' % EXP('; 1 5'))
    pre = w.h('P e. RR'); p0 = w.h('0 <_ P'); pb = w.h('P <_ %s' % EXP('( 5 / ; 1 2 )'))
    c = Closure(w, PH, {'M': ('RR', mre), 'L': [('RR', lre), ('ge0', l0)],
                        'P': [('RR', pre), ('ge0', p0)]})
    m0 = linarith(w, PH, [m12], '0 <_ M', closure=c)
    e1 = ge1(w, c, mre, m0, '; 1 5')
    h1 = linarith(w, PH, [lb, e1], '( L + 3 ) <_ ( 4 x. %s )' % EXP('; 1 5'), closure=c)
    l3 = scale(w, c, mre, m12, '4', '; 1 5', '( ; 6 1 / 4 )', '( L + 3 )',
               c.mem('( L + 3 )', 'RR'), h1)
    l30 = linarith(w, PH, [l0], '0 <_ ( L + 3 )', closure=c)
    pl = emul(w, c, mre, m0, '( 5 / ; 1 2 )', '( ; 6 1 / 4 )', '( ; 4 7 / 3 )',
              'P', '( L + 3 )', pre, p0, pb, c.mem('( L + 3 )', 'RR'), l30, l3)
    e2 = ge1(w, c, mre, m0, '( ; 4 7 / 3 )')
    h2 = linarith(w, PH, [pl, e2], '%s <_ ( 2 x. %s )' % (TERM3, EXP('( ; 4 7 / 3 )')), closure=c)
    scale(w, c, mre, m12, '2', '( ; 4 7 / 3 )', '( ; ; 1 9 1 / ; 1 2 )', TERM3,
          c.mem(TERM3, 'RR'), h2)
    w.qed([], 'idi', A('%s <_ %s' % (TERM3, EXP('( ; ; 1 9 1 / ; 1 2 )'))))
    return w


@gen
def cbt4():
    w = WH('cbt4', 'Step 5 of the cost budget, the verification, is below exp ( 461 M / 12 ) '
                   '(Lean AlgBudget.lean, ` hinner4 ` , ` hSin ` and ` term4 ` of '
                   'costPieces_bound).')
    mre = w.h('M e. RR'); m12 = w.h('; 1 2 <_ M')
    ure = w.h('U e. RR'); u0 = w.h('0 <_ U'); ub = w.h('U <_ %s' % EXP('( ; 7 5 / 2 )'))
    sre = w.h('S e. RR'); s0 = w.h('0 <_ S'); sb = w.h('S <_ %s' % EXP('( 5 / ; 1 2 )'))
    c = Closure(w, PH, {'M': ('RR', mre), 'U': [('RR', ure), ('ge0', u0)],
                        'S': [('RR', sre), ('ge0', s0)]})
    m0 = linarith(w, PH, [m12], '0 <_ M', closure=c)
    sb2 = w.s([mre, m0, lit(w, c, '( 5 / ; 1 2 )'), lit(w, c, '( ; 7 5 / 2 )'),
               linarith(w, PH, [], '( 5 / ; 1 2 ) <_ ( ; 7 5 / 2 )', closure=c), sre, sb],
              'cbetr', A('S <_ %s' % EXP('( ; 7 5 / 2 )')))
    e1 = ge1(w, c, mre, m0, '( ; 7 5 / 2 )')
    h1 = linarith(w, PH, [ub, sb2, e1], '%s <_ ( 8 x. %s )' % (I4, EXP('( ; 7 5 / 2 )')), closure=c)
    i4 = scale(w, c, mre, m12, '8', '( ; 7 5 / 2 )', '( ; ; 1 5 1 / 4 )', I4, c.mem(I4, 'RR'), h1)
    i40 = linarith(w, PH, [u0, s0], '0 <_ %s' % I4, closure=c)
    si = emul(w, c, mre, m0, '( 5 / ; 1 2 )', '( ; ; 1 5 1 / 4 )', '( ; ; 2 2 9 / 6 )',
              'S', I4, sre, s0, sb, c.mem(I4, 'RR'), i40, i4)
    e2 = ge1(w, c, mre, m0, '( ; ; 2 2 9 / 6 )')
    h2 = linarith(w, PH, [si, e2], '%s <_ ( 5 x. %s )' % (TERM4, EXP('( ; ; 2 2 9 / 6 )')), closure=c)
    scale(w, c, mre, m12, '5', '( ; ; 2 2 9 / 6 )', '( ; ; 4 6 1 / ; 1 2 )', TERM4,
          c.mem(TERM4, 'RR'), h2)
    w.qed([], 'idi', A('%s <_ %s' % (TERM4, EXP('( ; ; 4 6 1 / ; 1 2 )'))))
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
