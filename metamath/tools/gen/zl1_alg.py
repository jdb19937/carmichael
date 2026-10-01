"""ZL1: the closed complex ring identities of the zeta continuation
(zl1alg1 .. zl1alg5).  `MM_DB=sorties/zl1.mm python3 tools/gen/zl1_alg.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl1lib import *
from cl import Closure

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    return w.run()


def ctx(w, ante, atoms):
    """closure with the atoms read off the antecedent by position: atoms = [(name, ref)]"""
    lv = {}
    for a, ref in atoms:
        lv[a] = ('CC', w.s([], ref, '( %s -> %s e. CC )' % (ante, a)))
    return Closure(w, ante, lv)


def E(w, ante, ref, hyps, l, r):
    return w.s(hyps, ref, '( %s -> %s = %s )' % (ante, l, r))


# ---------------------------------------------------------------- zl1alg1
if not only or 'zl1alg1' in only:
    w = W('zl1alg1', 'The derivative of the primitive ` F ` of the zeta continuation in factored form '
          '(ring identity for ~ zl1fdv ).')
    A = '( ( Z e. CC /\\ K e. CC ) /\\ ( B e. CC /\\ P e. CC ) )'
    c = ctx(w, A, [('Z', 'simpll'), ('K', 'simplr'), ('B', 'simprl'), ('P', 'simprr')])
    m = lambda e: c.mem(e, 'CC')
    Z1 = '( Z - 1 )'; U = '( Z x. ( Z - 1 ) )'; ZK = '( ( Z - 1 ) x. K )'
    # T1 = ( ZK x. ( -u Z x. P ) ) = -u ( U x. ( K x. P ) )
    t1a = E(w, A, 'mulneg1d', [m('Z'), m('P')], '( -u Z x. P )', '-u ( Z x. P )')
    t1b = E(w, A, 'oveq2d', [t1a], '( %s x. ( -u Z x. P ) )' % ZK, '( %s x. -u ( Z x. P ) )' % ZK)
    t1c = E(w, A, 'mulneg2d', [m(ZK), m('( Z x. P )')], '( %s x. -u ( Z x. P ) )' % ZK, '-u ( %s x. ( Z x. P ) )' % ZK)
    t1d = E(w, A, 'mul4d', [m(Z1), m('K'), m('Z'), m('P')], '( %s x. ( Z x. P ) )' % ZK, '( ( %s x. Z ) x. ( K x. P ) )' % Z1)
    t1e = E(w, A, 'mulcomd', [m(Z1), m('Z')], '( %s x. Z )' % Z1, U)
    t1f = E(w, A, 'oveq1d', [t1e], '( ( %s x. Z ) x. ( K x. P ) )' % Z1, '( %s x. ( K x. P ) )' % U)
    t1g = chain(w, A, ['( %s x. ( Z x. P ) )' % ZK, '( ( %s x. Z ) x. ( K x. P ) )' % Z1, '( %s x. ( K x. P ) )' % U], [t1d, t1f])
    t1h = E(w, A, 'negeqd', [t1g], '-u ( %s x. ( Z x. P ) )' % ZK, '-u ( %s x. ( K x. P ) )' % U)
    T1 = chain(w, A, ['( %s x. ( -u Z x. P ) )' % ZK, '( %s x. -u ( Z x. P ) )' % ZK, '-u ( %s x. ( Z x. P ) )' % ZK,
                      '-u ( %s x. ( K x. P ) )' % U], [t1b, t1c, t1h])
    # T2 = ( Z x. ( ( 1 - Z ) x. ( P x. B ) ) ) = -u ( U x. ( B x. P ) )
    PB = '( P x. B )'
    t2a = w.s([E(w, A, 'negsubdi2d', [m('Z'), m('1')], '-u ( Z - 1 )', '( 1 - Z )')], 'eqcomd', '( %s -> ( 1 - Z ) = -u ( Z - 1 ) )' % A)
    t2b = E(w, A, 'oveq1d', [t2a], '( ( 1 - Z ) x. %s )' % PB, '( -u ( Z - 1 ) x. %s )' % PB)
    t2c = E(w, A, 'mulneg1d', [m(Z1), m(PB)], '( -u ( Z - 1 ) x. %s )' % PB, '-u ( ( Z - 1 ) x. %s )' % PB)
    t2d = chain(w, A, ['( ( 1 - Z ) x. %s )' % PB, '( -u ( Z - 1 ) x. %s )' % PB, '-u ( ( Z - 1 ) x. %s )' % PB], [t2b, t2c])
    t2e = E(w, A, 'oveq2d', [t2d], '( Z x. ( ( 1 - Z ) x. %s ) )' % PB, '( Z x. -u ( ( Z - 1 ) x. %s ) )' % PB)
    t2f = E(w, A, 'mulneg2d', [m('Z'), m('( ( Z - 1 ) x. %s )' % PB)], '( Z x. -u ( ( Z - 1 ) x. %s ) )' % PB, '-u ( Z x. ( ( Z - 1 ) x. %s ) )' % PB)
    t2g = E(w, A, 'mulassd', [m('Z'), m(Z1), m(PB)], '( %s x. %s )' % (U, PB), '( Z x. ( ( Z - 1 ) x. %s ) )' % PB)
    t2h = E(w, A, 'mulcomd', [m('P'), m('B')], PB, '( B x. P )')
    t2i = E(w, A, 'oveq2d', [t2h], '( %s x. %s )' % (U, PB), '( %s x. ( B x. P ) )' % U)
    t2j = chain(w, A, ['( Z x. ( ( Z - 1 ) x. %s ) )' % PB, '( %s x. %s )' % (U, PB), '( %s x. ( B x. P ) )' % U], [('r', t2g), t2i])
    t2k = E(w, A, 'negeqd', [t2j], '-u ( Z x. ( ( Z - 1 ) x. %s ) )' % PB, '-u ( %s x. ( B x. P ) )' % U)
    T2 = chain(w, A, ['( Z x. ( ( 1 - Z ) x. %s ) )' % PB, '( Z x. -u ( ( Z - 1 ) x. %s ) )' % PB,
                      '-u ( Z x. ( ( Z - 1 ) x. %s ) )' % PB, '-u ( %s x. ( B x. P ) )' % U], [t2e, t2f, t2k])
    LHS = '( ( %s x. ( -u Z x. P ) ) - ( Z x. ( ( 1 - Z ) x. %s ) ) )' % (ZK, PB)
    s1 = E(w, A, 'oveq12d', [T1, T2], LHS, '( -u ( %s x. ( K x. P ) ) - -u ( %s x. ( B x. P ) ) )' % (U, U))
    s2 = E(w, A, 'neg2subd', [m('( %s x. ( K x. P ) )' % U), m('( %s x. ( B x. P ) )' % U)],
           '( -u ( %s x. ( K x. P ) ) - -u ( %s x. ( B x. P ) ) )' % (U, U), '( ( %s x. ( B x. P ) ) - ( %s x. ( K x. P ) ) )' % (U, U))
    s3 = E(w, A, 'subdid', [m(U), m('( B x. P )'), m('( K x. P )')], '( %s x. ( ( B x. P ) - ( K x. P ) ) )' % U,
           '( ( %s x. ( B x. P ) ) - ( %s x. ( K x. P ) ) )' % (U, U))
    s4 = E(w, A, 'subdird', [m('B'), m('K'), m('P')], '( ( B - K ) x. P )', '( ( B x. P ) - ( K x. P ) )')
    s5 = E(w, A, 'oveq2d', [s4], '( %s x. ( ( B - K ) x. P ) )' % U, '( %s x. ( ( B x. P ) - ( K x. P ) ) )' % U)
    chain(w, A, [LHS, '( -u ( %s x. ( K x. P ) ) - -u ( %s x. ( B x. P ) ) )' % (U, U), '( ( %s x. ( B x. P ) ) - ( %s x. ( K x. P ) ) )' % (U, U),
                 '( %s x. ( ( B x. P ) - ( K x. P ) ) )' % U, '( %s x. ( ( B - K ) x. P ) )' % U], [s1, s2, ('r', s3), ('r', s5)], name='qed')
    go(w)


# ---------------------------------------------------------------- zl1alg2
if not only or 'zl1alg2' in only:
    w = W('zl1alg2', 'The values of the primitive ` F ` of the zeta continuation at ` K ` and ` K + 1 ` '
          '(ring identities for ~ zl1hvb ).')
    A = '( ( Z e. CC /\\ K e. CC ) /\\ ( P e. CC /\\ Q e. CC ) )'
    c = ctx(w, A, [('Z', 'simpll'), ('K', 'simplr'), ('P', 'simprl'), ('Q', 'simprr')])
    m = lambda e: c.mem(e, 'CC')
    Z1 = '( Z - 1 )'; ZK = '( ( Z - 1 ) x. K )'; KP = '( K x. P )'
    # first: ( ZK P ) - ( Z ( P K ) ) = -u ( K P )
    a1 = E(w, A, 'mulassd', [m(Z1), m('K'), m('P')], '( %s x. P )' % ZK, '( %s x. %s )' % (Z1, KP))
    a2 = E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [m('P'), m('K')], '( P x. K )', KP)], '( Z x. ( P x. K ) )', '( Z x. %s )' % KP)
    L1 = '( ( %s x. P ) - ( Z x. ( P x. K ) ) )' % ZK
    a3 = E(w, A, 'oveq12d', [a1, a2], L1, '( ( %s x. %s ) - ( Z x. %s ) )' % (Z1, KP, KP))
    a4 = E(w, A, 'subdird', [m(Z1), m('Z'), m(KP)], '( ( %s - Z ) x. %s )' % (Z1, KP), '( ( %s x. %s ) - ( Z x. %s ) )' % (Z1, KP, KP))
    b1 = E(w, A, 'negsubdi2d', [m('Z'), m(Z1)], '-u ( Z - %s )' % Z1, '( %s - Z )' % Z1)
    b2 = E(w, A, 'negeqd', [E(w, A, 'nncand', [m('Z'), m('1')], '( Z - %s )' % Z1, '1')], '-u ( Z - %s )' % Z1, '-u 1')
    b3 = chain(w, A, ['( %s - Z )' % Z1, '-u ( Z - %s )' % Z1, '-u 1'], [('r', b1), b2])
    a5 = E(w, A, 'oveq1d', [b3], '( ( %s - Z ) x. %s )' % (Z1, KP), '( -u 1 x. %s )' % KP)
    a6 = E(w, A, 'mulm1d', [m(KP)], '( -u 1 x. %s )' % KP, '-u %s' % KP)
    F1 = chain(w, A, [L1, '( ( %s x. %s ) - ( Z x. %s ) )' % (Z1, KP, KP), '( ( %s - Z ) x. %s )' % (Z1, KP), '( -u 1 x. %s )' % KP, '-u %s' % KP],
               [a3, ('r', a4), a5, a6])
    # second: ( ZK Q ) - ( Z ( Q ( K + 1 ) ) ) = -u ( ( K + Z ) Q )
    K1 = '( K + 1 )'; ZK1 = '( Z x. %s )' % K1
    c1 = E(w, A, 'mul12d', [m('Z'), m('Q'), m(K1)], '( Z x. ( Q x. %s ) )' % K1, '( Q x. %s )' % ZK1)
    c2 = E(w, A, 'mulcomd', [m('Q'), m(ZK1)], '( Q x. %s )' % ZK1, '( %s x. Q )' % ZK1)
    c3 = chain(w, A, ['( Z x. ( Q x. %s ) )' % K1, '( Q x. %s )' % ZK1, '( %s x. Q )' % ZK1], [c1, c2])
    L2 = '( ( %s x. Q ) - ( Z x. ( Q x. %s ) ) )' % (ZK, K1)
    c4 = E(w, A, 'oveq2d', [c3], L2, '( ( %s x. Q ) - ( %s x. Q ) )' % (ZK, ZK1))
    c5 = E(w, A, 'subdird', [m(ZK), m(ZK1), m('Q')], '( ( %s - %s ) x. Q )' % (ZK, ZK1), '( ( %s x. Q ) - ( %s x. Q ) )' % (ZK, ZK1))
    ZKK = '( Z x. K )'
    d1 = E(w, A, 'subdird', [m('Z'), m('1'), m('K')], ZK, '( %s - ( 1 x. K ) )' % ZKK)
    d2 = E(w, A, 'oveq2d', [E(w, A, 'mullidd', [m('K')], '( 1 x. K )', 'K')], '( %s - ( 1 x. K ) )' % ZKK, '( %s - K )' % ZKK)
    d3 = chain(w, A, [ZK, '( %s - ( 1 x. K ) )' % ZKK, '( %s - K )' % ZKK], [d1, d2])
    d4 = E(w, A, 'adddid', [m('Z'), m('K'), m('1')], ZK1, '( %s + ( Z x. 1 ) )' % ZKK)
    d5 = E(w, A, 'oveq2d', [E(w, A, 'mulridd', [m('Z')], '( Z x. 1 )', 'Z')], '( %s + ( Z x. 1 ) )' % ZKK, '( %s + Z )' % ZKK)
    d6 = chain(w, A, [ZK1, '( %s + ( Z x. 1 ) )' % ZKK, '( %s + Z )' % ZKK], [d4, d5])
    d7 = E(w, A, 'oveq12d', [d6, d3], '( %s - %s )' % (ZK1, ZK), '( ( %s + Z ) - ( %s - K ) )' % (ZKK, ZKK))
    d8 = E(w, A, 'pnncand', [m(ZKK), m('Z'), m('K')], '( ( %s + Z ) - ( %s - K ) )' % (ZKK, ZKK), '( Z + K )')
    d9 = E(w, A, 'addcomd', [m('Z'), m('K')], '( Z + K )', '( K + Z )')
    e1 = chain(w, A, ['( %s - %s )' % (ZK1, ZK), '( ( %s + Z ) - ( %s - K ) )' % (ZKK, ZKK), '( Z + K )', '( K + Z )'], [d7, d8, d9])
    e2 = E(w, A, 'negsubdi2d', [m(ZK1), m(ZK)], '-u ( %s - %s )' % (ZK1, ZK), '( %s - %s )' % (ZK, ZK1))
    e3 = chain(w, A, ['( %s - %s )' % (ZK, ZK1), '-u ( %s - %s )' % (ZK1, ZK), '-u ( K + Z )'], [('r', e2), E(w, A, 'negeqd', [e1], '-u ( %s - %s )' % (ZK1, ZK), '-u ( K + Z )')])
    e4 = E(w, A, 'oveq1d', [e3], '( ( %s - %s ) x. Q )' % (ZK, ZK1), '( -u ( K + Z ) x. Q )')
    e5 = E(w, A, 'mulneg1d', [m('( K + Z )'), m('Q')], '( -u ( K + Z ) x. Q )', '-u ( ( K + Z ) x. Q )')
    F2 = chain(w, A, [L2, '( ( %s x. Q ) - ( %s x. Q ) )' % (ZK, ZK1), '( ( %s - %s ) x. Q )' % (ZK, ZK1), '( -u ( K + Z ) x. Q )',
                      '-u ( ( K + Z ) x. Q )'], [c4, ('r', c5), e4, e5])
    w.qed([F1, F2], 'jca', '( %s -> ( %s = -u %s /\\ %s = -u ( ( K + Z ) x. Q ) ) )' % (A, L1, KP, L2))
    go(w)

# ---------------------------------------------------------------- zl1alg5
if not only or 'zl1alg5' in only:
    w = W('zl1alg5', 'The ` z ` -derivative of the zeta continuation term in normal form (ring identity for ~ zl1hdv ).')
    A = '( ( Z e. CC /\\ K e. CC ) /\\ ( ( P e. CC /\\ Q e. CC ) /\\ ( A e. CC /\\ G e. CC ) ) )'
    c = ctx(w, A, [('Z', 'simpll'), ('K', 'simplr'), ('P', 'simprll'), ('Q', 'simprlr'), ('A', 'simprrl'), ('G', 'simprrr')])
    m = lambda e: c.mem(e, 'CC')
    KZ = '( K + Z )'; GQ = '( G x. Q )'; AP = '( A x. P )'
    f1 = E(w, A, 'mullidd', [m('Q')], '( 1 x. Q )', 'Q')
    f2 = E(w, A, 'mulneg1d', [m(GQ), m(KZ)], '( -u %s x. %s )' % (GQ, KZ), '-u ( %s x. %s )' % (GQ, KZ))
    f3 = E(w, A, 'negeqd', [E(w, A, 'mulcomd', [m(GQ), m(KZ)], '( %s x. %s )' % (GQ, KZ), '( %s x. %s )' % (KZ, GQ))],
           '-u ( %s x. %s )' % (GQ, KZ), '-u ( %s x. %s )' % (KZ, GQ))
    f4 = chain(w, A, ['( -u %s x. %s )' % (GQ, KZ), '-u ( %s x. %s )' % (GQ, KZ), '-u ( %s x. %s )' % (KZ, GQ)], [f2, f3])
    X1 = '( ( 1 x. Q ) + ( -u %s x. %s ) )' % (GQ, KZ)
    f5 = E(w, A, 'oveq12d', [f1, f4], X1, '( Q + -u ( %s x. %s ) )' % (KZ, GQ))
    f6 = E(w, A, 'negsubd', [m('Q'), m('( %s x. %s )' % (KZ, GQ))], '( Q + -u ( %s x. %s ) )' % (KZ, GQ), '( Q - ( %s x. %s ) )' % (KZ, GQ))
    f7 = chain(w, A, [X1, '( Q + -u ( %s x. %s ) )' % (KZ, GQ), '( Q - ( %s x. %s ) )' % (KZ, GQ)], [f5, f6])
    g1 = E(w, A, 'mulneg2d', [m('K'), m(AP)], '( K x. -u %s )' % AP, '-u ( K x. %s )' % AP)
    L = '( %s - ( K x. -u %s ) )' % (X1, AP)
    h1 = E(w, A, 'oveq12d', [f7, g1], L, '( ( Q - ( %s x. %s ) ) - -u ( K x. %s ) )' % (KZ, GQ, AP))
    h2 = E(w, A, 'subnegd', [m('( Q - ( %s x. %s ) )' % (KZ, GQ)), m('( K x. %s )' % AP)],
           '( ( Q - ( %s x. %s ) ) - -u ( K x. %s ) )' % (KZ, GQ, AP), '( ( Q - ( %s x. %s ) ) + ( K x. %s ) )' % (KZ, GQ, AP))
    chain(w, A, [L, '( ( Q - ( %s x. %s ) ) - -u ( K x. %s ) )' % (KZ, GQ, AP), '( ( Q - ( %s x. %s ) ) + ( K x. %s ) )' % (KZ, GQ, AP)], [h1, h2], name='qed')
    go(w)

# ---------------------------------------------------------------- zl1alg4
if not only or 'zl1alg4' in only:
    w = W('zl1alg4', 'The values of the ` z ` -derivative primitive ` P ` of the zeta continuation at ` K ` and '
          '` K + 1 ` (ring identity for ~ zl1hdb ).')
    A = '( ( ( Z e. CC /\\ K e. CC ) /\\ ( P e. CC /\\ Q e. CC ) ) /\\ ( A e. CC /\\ G e. CC ) )'
    c = ctx(w, A, [('Z', 'simplll'), ('K', 'simpllr'), ('P', 'simplrl'), ('Q', 'simplrr'), ('A', 'simprl'), ('G', 'simprr')])
    m = lambda e: c.mem(e, 'CC')
    KP = '( K x. P )'; KZ = '( K + Z )'; KZQ = '( %s x. Q )' % KZ; GQ = '( G x. Q )'; AP = '( A x. P )'
    B1 = '( %s - ( P x. K ) )' % KP
    # PM ( K ) = K ( A P )
    p1 = E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [m('P'), m('K')], '( P x. K )', KP)], B1, '( %s - %s )' % (KP, KP))
    p2 = chain(w, A, [B1, '( %s - %s )' % (KP, KP), '0'], [p1, E(w, A, 'subidd', [m(KP)], '( %s - %s )' % (KP, KP), '0')])
    p3 = E(w, A, 'mulneg2d', [m('A'), m(KP)], '( A x. -u %s )' % KP, '-u ( A x. %s )' % KP)
    PK = '( %s - ( A x. -u %s ) )' % (B1, KP)
    p4 = E(w, A, 'oveq12d', [p2, p3], PK, '( 0 - -u ( A x. %s ) )' % KP)
    p5 = E(w, A, 'subnegd', [m('0'), m('( A x. %s )' % KP)], '( 0 - -u ( A x. %s ) )' % KP, '( 0 + ( A x. %s ) )' % KP)
    p6 = E(w, A, 'addlidd', [m('( A x. %s )' % KP)], '( 0 + ( A x. %s ) )' % KP, '( A x. %s )' % KP)
    p7 = E(w, A, 'mul12d', [m('A'), m('K'), m('P')], '( A x. %s )' % KP, '( K x. %s )' % AP)
    PKV = chain(w, A, [PK, '( 0 - -u ( A x. %s ) )' % KP, '( 0 + ( A x. %s ) )' % KP, '( A x. %s )' % KP, '( K x. %s )' % AP], [p4, p5, p6, p7])
    # PM ( K + 1 ) = ( ( K + Z ) ( G Q ) ) - Q
    K1 = '( K + 1 )'; KQ = '( K x. Q )'
    B2 = '( %s - ( Q x. %s ) )' % (KQ, K1)
    q1 = E(w, A, 'mulcomd', [m('Q'), m(K1)], '( Q x. %s )' % K1, '( %s x. Q )' % K1)
    q2 = E(w, A, 'adddird', [m('K'), m('1'), m('Q')], '( %s x. Q )' % K1, '( %s + ( 1 x. Q ) )' % KQ)
    q3 = E(w, A, 'oveq2d', [E(w, A, 'mullidd', [m('Q')], '( 1 x. Q )', 'Q')], '( %s + ( 1 x. Q ) )' % KQ, '( %s + Q )' % KQ)
    q4 = chain(w, A, ['( Q x. %s )' % K1, '( %s x. Q )' % K1, '( %s + ( 1 x. Q ) )' % KQ, '( %s + Q )' % KQ], [q1, q2, q3])
    q5 = E(w, A, 'oveq2d', [q4], B2, '( %s - ( %s + Q ) )' % (KQ, KQ))
    q6 = E(w, A, 'subsub4d', [m(KQ), m(KQ), m('Q')], '( ( %s - %s ) - Q )' % (KQ, KQ), '( %s - ( %s + Q ) )' % (KQ, KQ))
    q7 = E(w, A, 'oveq1d', [E(w, A, 'subidd', [m(KQ)], '( %s - %s )' % (KQ, KQ), '0')], '( ( %s - %s ) - Q )' % (KQ, KQ), '( 0 - Q )')
    q8 = w.s([w.s([], 'df-neg', '-u Q = ( 0 - Q )')], 'a1i', '( %s -> -u Q = ( 0 - Q ) )' % A)
    B2V = chain(w, A, [B2, '( %s - ( %s + Q ) )' % (KQ, KQ), '( ( %s - %s ) - Q )' % (KQ, KQ), '( 0 - Q )', '-u Q'], [q5, ('r', q6), q7, ('r', q8)])
    r1 = E(w, A, 'mulneg2d', [m('G'), m(KZQ)], '( G x. -u %s )' % KZQ, '-u ( G x. %s )' % KZQ)
    r2 = E(w, A, 'negeqd', [E(w, A, 'mul12d', [m('G'), m(KZ), m('Q')], '( G x. %s )' % KZQ, '( %s x. %s )' % (KZ, GQ))],
           '-u ( G x. %s )' % KZQ, '-u ( %s x. %s )' % (KZ, GQ))
    r3 = chain(w, A, ['( G x. -u %s )' % KZQ, '-u ( G x. %s )' % KZQ, '-u ( %s x. %s )' % (KZ, GQ)], [r1, r2])
    PK1 = '( %s - ( G x. -u %s ) )' % (B2, KZQ)
    r4 = E(w, A, 'oveq12d', [B2V, r3], PK1, '( -u Q - -u ( %s x. %s ) )' % (KZ, GQ))
    r5 = E(w, A, 'neg2subd', [m('Q'), m('( %s x. %s )' % (KZ, GQ))], '( -u Q - -u ( %s x. %s ) )' % (KZ, GQ), '( ( %s x. %s ) - Q )' % (KZ, GQ))
    PK1V = chain(w, A, [PK1, '( -u Q - -u ( %s x. %s ) )' % (KZ, GQ), '( ( %s x. %s ) - Q )' % (KZ, GQ)], [r4, r5])
    # the difference
    a_ = '( K x. %s )' % AP; b_ = '( %s x. %s )' % (KZ, GQ)
    LHS = '( %s - %s )' % (PK, PK1)
    t1 = E(w, A, 'oveq12d', [PKV, PK1V], LHS, '( %s - ( %s - Q ) )' % (a_, b_))
    t2 = E(w, A, 'subsubd', [m(a_), m(b_), m('Q')], '( %s - ( %s - Q ) )' % (a_, b_), '( ( %s - %s ) + Q )' % (a_, b_))
    t3 = E(w, A, 'addcomd', [m('( %s - %s )' % (a_, b_)), m('Q')], '( ( %s - %s ) + Q )' % (a_, b_), '( Q + ( %s - %s ) )' % (a_, b_))
    t4 = E(w, A, 'addsubassd', [m('Q'), m(a_), m(b_)], '( ( Q + %s ) - %s )' % (a_, b_), '( Q + ( %s - %s ) )' % (a_, b_))
    t5 = E(w, A, 'addsubd', [m('Q'), m(a_), m(b_)], '( ( Q + %s ) - %s )' % (a_, b_), '( ( Q - %s ) + %s )' % (b_, a_))
    chain(w, A, [LHS, '( %s - ( %s - Q ) )' % (a_, b_), '( ( %s - %s ) + Q )' % (a_, b_), '( Q + ( %s - %s ) )' % (a_, b_),
                 '( ( Q + %s ) - %s )' % (a_, b_), '( ( Q - %s ) + %s )' % (b_, a_)], [t1, t2, t3, ('r', t4), t5], name='qed')
    go(w)

# ---------------------------------------------------------------- zl1alg3
if not only or 'zl1alg3' in only:
    w = W('zl1alg3', 'The derivative of the ` z ` -derivative primitive ` P ` of the zeta continuation in factored '
          'form (ring identity for ~ zl1pdv ).')
    A = '( ( ( Z e. CC /\\ K e. CC ) /\\ ( B e. CC /\\ B =/= 0 ) ) /\\ ( P e. CC /\\ L e. CC ) )'
    lv = {}
    for a, ref in [('Z', 'simplll'), ('K', 'simpllr'), ('B', 'simplrl'), ('P', 'simprl'), ('L', 'simprr')]:
        lv[a] = ('CC', w.s([], ref, '( %s -> %s e. CC )' % (A, a)))
    bne = w.s([], 'simplrr', '( %s -> B =/= 0 )' % A)
    c = Closure(w, A, lv)
    c.have('B', 'ne0', bne)
    m = lambda e: c.mem(e, 'CC')
    ZK = '( ( Z - 1 ) x. K )'; U = '( Z x. ( Z - 1 ) )'; PB = '( P x. B )'; BP = '( B x. P )'; KP = '( K x. P )'
    D = '( ( B - K ) x. P )'; V = '( ( 2 x. Z ) - 1 )'
    FBP = '( ( %s x. %s ) - ( Z x. ( %s x. B ) ) )' % (ZK, PB, PB)
    X = '( ( %s x. P ) - ( Z x. %s ) )' % (ZK, PB)
    # (i) ( 1 / B ) FBP = X
    i1 = E(w, A, 'mulassd', [m(ZK), m('P'), m('B')], '( ( %s x. P ) x. B )' % ZK, '( %s x. %s )' % (ZK, PB))
    i2 = E(w, A, 'mulassd', [m('Z'), m(PB), m('B')], '( ( Z x. %s ) x. B )' % PB, '( Z x. ( %s x. B ) )' % PB)
    i3 = E(w, A, 'subdird', [m('( %s x. P )' % ZK), m('( Z x. %s )' % PB), m('B')], '( %s x. B )' % X,
           '( ( ( %s x. P ) x. B ) - ( ( Z x. %s ) x. B ) )' % (ZK, PB))
    i4 = E(w, A, 'oveq12d', [i1, i2], '( ( ( %s x. P ) x. B ) - ( ( Z x. %s ) x. B ) )' % (ZK, PB), FBP)
    i5 = chain(w, A, ['( %s x. B )' % X, '( ( ( %s x. P ) x. B ) - ( ( Z x. %s ) x. B ) )' % (ZK, PB), FBP], [i3, i4])
    i6 = E(w, A, 'oveq2d', [i5], '( ( 1 / B ) x. ( %s x. B ) )' % X, '( ( 1 / B ) x. %s )' % FBP)
    i7 = E(w, A, 'divrec2d', [m('( %s x. B )' % X), m('B'), bne], '( ( %s x. B ) / B )' % X, '( ( 1 / B ) x. ( %s x. B ) )' % X)
    i8 = E(w, A, 'divcan4d', [m(X), m('B'), bne], '( ( %s x. B ) / B )' % X, X)
    I = chain(w, A, ['( ( 1 / B ) x. %s )' % FBP, '( ( 1 / B ) x. ( %s x. B ) )' % X, '( ( %s x. B ) / B )' % X, X], [('r', i6), ('r', i7), i8])
    # (ii) ( U D ) L = D ( U L )
    j1 = E(w, A, 'oveq1d', [E(w, A, 'mulcomd', [m(U), m(D)], '( %s x. %s )' % (U, D), '( %s x. %s )' % (D, U))],
           '( ( %s x. %s ) x. L )' % (U, D), '( ( %s x. %s ) x. L )' % (D, U))
    j2 = E(w, A, 'mulassd', [m(D), m(U), m('L')], '( ( %s x. %s ) x. L )' % (D, U), '( %s x. ( %s x. L ) )' % (D, U))
    J = chain(w, A, ['( ( %s x. %s ) x. L )' % (U, D), '( ( %s x. %s ) x. L )' % (D, U), '( %s x. ( %s x. L ) )' % (D, U)], [j1, j2])
    # (iii) F1 - X = D V
    F1 = '( ( K x. ( -u Z x. P ) ) - ( ( 1 - Z ) x. %s ) )' % PB
    k1 = E(w, A, 'mul12d', [m('K'), m('-u Z'), m('P')], '( K x. ( -u Z x. P ) )', '( -u Z x. %s )' % KP)
    k2 = E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [m('P'), m('B')], PB, BP)], '( ( 1 - Z ) x. %s )' % PB, '( ( 1 - Z ) x. %s )' % BP)
    k3 = E(w, A, 'oveq12d', [k1, k2], F1, '( ( -u Z x. %s ) - ( ( 1 - Z ) x. %s ) )' % (KP, BP))
    k4 = E(w, A, 'mulassd', [m('( Z - 1 )'), m('K'), m('P')], '( %s x. P )' % ZK, '( ( Z - 1 ) x. %s )' % KP)
    k5 = E(w, A, 'oveq2d', [E(w, A, 'mulcomd', [m('P'), m('B')], PB, BP)], '( Z x. %s )' % PB, '( Z x. %s )' % BP)
    k6 = E(w, A, 'oveq12d', [k4, k5], X, '( ( ( Z - 1 ) x. %s ) - ( Z x. %s ) )' % (KP, BP))
    F1b = '( ( -u Z x. %s ) - ( ( 1 - Z ) x. %s ) )' % (KP, BP)
    Xb = '( ( ( Z - 1 ) x. %s ) - ( Z x. %s ) )' % (KP, BP)
    k7 = E(w, A, 'oveq12d', [k3, k6], '( %s - %s )' % (F1, X), '( %s - %s )' % (F1b, Xb))
    S4 = '( ( ( -u Z x. %s ) - ( ( Z - 1 ) x. %s ) ) - ( ( ( 1 - Z ) x. %s ) - ( Z x. %s ) ) )' % (KP, KP, BP, BP)
    k8 = E(w, A, 'sub4d', [m('( -u Z x. %s )' % KP), m('( ( 1 - Z ) x. %s )' % BP), m('( ( Z - 1 ) x. %s )' % KP), m('( Z x. %s )' % BP)],
           '( %s - %s )' % (F1b, Xb), S4)
    l1 = E(w, A, 'subdird', [m('-u Z'), m('( Z - 1 )'), m(KP)], '( ( -u Z - ( Z - 1 ) ) x. %s )' % KP, '( ( -u Z x. %s ) - ( ( Z - 1 ) x. %s ) )' % (KP, KP))
    l2 = E(w, A, 'subdird', [m('( 1 - Z )'), m('Z'), m(BP)], '( ( ( 1 - Z ) - Z ) x. %s )' % BP, '( ( ( 1 - Z ) x. %s ) - ( Z x. %s ) )' % (BP, BP))
    # scalars: -u Z - ( Z - 1 ) = -u V, ( 1 - Z ) - Z = -u V
    s1 = E(w, A, 'negdi2d', [m('Z'), m('( Z - 1 )')], '-u ( Z + ( Z - 1 ) )', '( -u Z - ( Z - 1 ) )')
    s2 = E(w, A, 'addsubassd', [m('Z'), m('Z'), m('1')], '( ( Z + Z ) - 1 )', '( Z + ( Z - 1 ) )')
    s3 = E(w, A, 'oveq1d', [E(w, A, '2timesd', [m('Z')], '( 2 x. Z )', '( Z + Z )')], V, '( ( Z + Z ) - 1 )')
    s4 = chain(w, A, [V, '( ( Z + Z ) - 1 )', '( Z + ( Z - 1 ) )'], [s3, s2])
    s5 = E(w, A, 'negeqd', [s4], '-u %s' % V, '-u ( Z + ( Z - 1 ) )')
    SA = chain(w, A, ['( -u Z - ( Z - 1 ) )', '-u ( Z + ( Z - 1 ) )', '-u %s' % V], [('r', s1), ('r', s5)])
    s6 = E(w, A, 'subsub4d', [m('1'), m('Z'), m('Z')], '( ( 1 - Z ) - Z )', '( 1 - ( Z + Z ) )')
    s7 = E(w, A, 'oveq2d', [E(w, A, '2timesd', [m('Z')], '( 2 x. Z )', '( Z + Z )')], '( 1 - ( 2 x. Z ) )', '( 1 - ( Z + Z ) )')
    s8 = E(w, A, 'negsubdi2d', [m('( 2 x. Z )'), m('1')], '-u %s' % V, '( 1 - ( 2 x. Z ) )')
    SB = chain(w, A, ['( ( 1 - Z ) - Z )', '( 1 - ( Z + Z ) )', '( 1 - ( 2 x. Z ) )', '-u %s' % V], [s6, ('r', s7), ('r', s8)])
    l3 = E(w, A, 'oveq1d', [SA], '( ( -u Z - ( Z - 1 ) ) x. %s )' % KP, '( -u %s x. %s )' % (V, KP))
    l4 = E(w, A, 'oveq1d', [SB], '( ( ( 1 - Z ) - Z ) x. %s )' % BP, '( -u %s x. %s )' % (V, BP))
    l5 = E(w, A, 'oveq12d', [chain(w, A, ['( ( -u Z x. %s ) - ( ( Z - 1 ) x. %s ) )' % (KP, KP), '( ( -u Z - ( Z - 1 ) ) x. %s )' % KP, '( -u %s x. %s )' % (V, KP)], [('r', l1), l3]),
                             chain(w, A, ['( ( ( 1 - Z ) x. %s ) - ( Z x. %s ) )' % (BP, BP), '( ( ( 1 - Z ) - Z ) x. %s )' % BP, '( -u %s x. %s )' % (V, BP)], [('r', l2), l4])],
           S4, '( ( -u %s x. %s ) - ( -u %s x. %s ) )' % (V, KP, V, BP))
    l6 = E(w, A, 'subdid', [m('-u %s' % V), m(KP), m(BP)], '( -u %s x. ( %s - %s ) )' % (V, KP, BP), '( ( -u %s x. %s ) - ( -u %s x. %s ) )' % (V, KP, V, BP))
    W_ = '( %s - %s )' % (KP, BP)
    l8a = E(w, A, 'mulneg1d', [m(V), m(W_)], '( -u %s x. %s )' % (V, W_), '-u ( %s x. %s )' % (V, W_))
    l8b = E(w, A, 'mulneg2d', [m(V), m(W_)], '( %s x. -u %s )' % (V, W_), '-u ( %s x. %s )' % (V, W_))
    l8 = chain(w, A, ['( -u %s x. %s )' % (V, W_), '-u ( %s x. %s )' % (V, W_), '( %s x. -u %s )' % (V, W_)], [l8a, ('r', l8b)])
    l9 = E(w, A, 'oveq2d', [E(w, A, 'negsubdi2d', [m(KP), m(BP)], '-u ( %s - %s )' % (KP, BP), '( %s - %s )' % (BP, KP))],
           '( %s x. -u ( %s - %s ) )' % (V, KP, BP), '( %s x. ( %s - %s ) )' % (V, BP, KP))
    l10 = E(w, A, 'oveq2d', [E(w, A, 'subdird', [m('B'), m('K'), m('P')], D, '( %s - %s )' % (BP, KP))], '( %s x. %s )' % (V, D), '( %s x. ( %s - %s ) )' % (V, BP, KP))
    l11 = E(w, A, 'mulcomd', [m(V), m(D)], '( %s x. %s )' % (V, D), '( %s x. %s )' % (D, V))
    K3 = chain(w, A, ['( %s - %s )' % (F1, X), '( %s - %s )' % (F1b, Xb), S4, '( ( -u %s x. %s ) - ( -u %s x. %s ) )' % (V, KP, V, BP),
                      '( -u %s x. ( %s - %s ) )' % (V, KP, BP), '( %s x. -u ( %s - %s ) )' % (V, KP, BP), '( %s x. ( %s - %s ) )' % (V, BP, KP),
                      '( %s x. %s )' % (V, D), '( %s x. %s )' % (D, V)],
               [k7, k8, l5, ('r', l6), l8, l9, ('r', l10), l11])
    # assemble
    LHS = '( %s - ( ( ( 1 / B ) x. %s ) + ( ( %s x. %s ) x. L ) ) )' % (F1, FBP, U, D)
    u1 = E(w, A, 'oveq12d', [I, J], '( ( ( 1 / B ) x. %s ) + ( ( %s x. %s ) x. L ) )' % (FBP, U, D), '( %s + ( %s x. ( %s x. L ) ) )' % (X, D, U))
    u2 = E(w, A, 'oveq2d', [u1], LHS, '( %s - ( %s + ( %s x. ( %s x. L ) ) ) )' % (F1, X, D, U))
    u3 = E(w, A, 'subsub4d', [m(F1), m(X), m('( %s x. ( %s x. L ) )' % (D, U))], '( ( %s - %s ) - ( %s x. ( %s x. L ) ) )' % (F1, X, D, U),
           '( %s - ( %s + ( %s x. ( %s x. L ) ) ) )' % (F1, X, D, U))
    u4 = E(w, A, 'oveq1d', [K3], '( ( %s - %s ) - ( %s x. ( %s x. L ) ) )' % (F1, X, D, U), '( ( %s x. %s ) - ( %s x. ( %s x. L ) ) )' % (D, V, D, U))
    u5 = E(w, A, 'subdid', [m(D), m(V), m('( %s x. L )' % U)], '( %s x. ( %s - ( %s x. L ) ) )' % (D, V, U), '( ( %s x. %s ) - ( %s x. ( %s x. L ) ) )' % (D, V, D, U))
    chain(w, A, [LHS, '( %s - ( %s + ( %s x. ( %s x. L ) ) ) )' % (F1, X, D, U), '( ( %s - %s ) - ( %s x. ( %s x. L ) ) )' % (F1, X, D, U),
                 '( ( %s x. %s ) - ( %s x. ( %s x. L ) ) )' % (D, V, D, U), '( %s x. ( %s - ( %s x. L ) ) )' % (D, V, U)],
          [u2, ('r', u3), u4, ('r', u5)], name='qed')
    go(w)
