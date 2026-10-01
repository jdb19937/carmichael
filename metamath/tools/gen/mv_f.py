"""Sortie MV, section F: the finite Fejer identity (mvtriabs, mvhq, mvfej)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from mvlib import *
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    bad = checkrefs(w)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, bad)); return False
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def absv(w, ante, c, X, sign_step, nonneg=True):
    """( ante -> ( abs ` X ) = X ) from 0 <_ X, or ( abs ` X ) = -u X from X <_ 0"""
    if nonneg:
        return w.s([c.mem(X, 'RR'), sign_step], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (ante, X, X))
    return w.s([c.mem(X, 'RR'), sign_step], 'absnidd', '( %s -> ( abs ` %s ) = -u %s )' % (ante, X, X))


def mvtriabs():
    w = W('mvtriabs', '| 2 A + H | + | 2 A - H | - 2 | H | = 2 max ( 0 , 2 A - | H | ) for A >_ 0 (the triangle as a combination of absolute values).')
    A0 = '( A e. RR /\\ 0 <_ A /\\ H e. RR )'
    P = parts(w, A0)
    ar, a0, hr = P['A e. RR'], P['0 <_ A'], P['H e. RR']
    D = '( 2 x. A )'; AH = '( abs ` H )'
    LHS = '( ( ( abs ` ( %s + H ) ) + ( abs ` ( %s - H ) ) ) - ( 2 x. %s ) )' % (D, D, AH)
    T = TRI(D, 'H')
    cond = '%s <_ %s' % (AH, D)

    def ctx(extra):
        """closure and facts under ( A0 /\\ extra )"""
        Ae = '( %s /\\ %s )' % (A0, extra)
        c = Closure(w, Ae, {'A': [('RR', lift(w, ar, Ae)), ('ge0', lift(w, a0, Ae))], 'H': ('RR', lift(w, hr, Ae))})
        return Ae, c
    # case 1: | H | <_ 2 A
    A1, c1 = ctx(cond)
    h1 = w.s([], 'simpr', '( %s -> %s )' % (A1, cond))
    ab = w.s([c1.mem('H', 'RR'), c1.mem(D, 'RR')], 'absled', '( %s -> ( %s <-> ( -u %s <_ H /\\ H <_ %s ) ) )' % (A1, cond, D, D))
    hb = w.s([h1, ab], 'mpbid', '( %s -> ( -u %s <_ H /\\ H <_ %s ) )' % (A1, D, D))
    hlo = dst(w, A1, [hb], 'simpld', '-u %s <_ H' % D); hhi = dst(w, A1, [hb], 'simprd', 'H <_ %s' % D)
    e1 = absv(w, A1, c1, '( %s + H )' % D, linarith(w, A1, [hlo], '0 <_ ( %s + H )' % D, closure=c1))
    e2 = absv(w, A1, c1, '( %s - H )' % D, linarith(w, A1, [hhi], '0 <_ ( %s - H )' % D, closure=c1))
    it = w.s([h1], 'iftrued' if False else 'id', 'x') if False else ap(w, A1, 'iftrue', [h1], '%s = ( %s - %s )' % (T, D, AH))
    c1.leaf(AH, 'RR', c1.mem(AH, 'RR'))
    for t_ in ['( abs ` ( %s + H ) )' % D, '( abs ` ( %s - H ) )' % D, T]:
        c1.leaf(t_, 'RR', c1.mem(t_, 'RR'))
    r1 = lineq(w, A1, LHS, '( 2 x. %s )' % T, hyps=[e1, e2, it], closure=c1)
    # case 2: not ( | H | <_ 2 A )
    A2, c2 = ctx('-. %s' % cond)
    n2 = w.s([], 'simpr', '( %s -> -. %s )' % (A2, cond))
    if_ = ap(w, A2, 'iffalse', [n2], '%s = 0' % T)
    c2.leaf(AH, 'RR', c2.mem(AH, 'RR'))
    lt = w.s([n2, w.s([c2.mem(AH, 'RR'), c2.mem(D, 'RR')], 'lenltd', '( %s -> ( %s <-> -. %s < %s ) )' % (A2, cond, D, AH))], 'mtbid' if False else 'id', 'x') if False else None
    nl = w.s([c2.mem(AH, 'RR'), c2.mem(D, 'RR')], 'ltnled', '( %s -> ( %s < %s <-> -. %s ) )' % (A2, D, AH, cond))
    dlt = w.s([n2, nl], 'mpbird', '( %s -> %s < %s )' % (A2, D, AH))
    # sub-cases on the sign of H
    sg = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A2), c2.mem('H', 'RR')], 'letrid', '( %s -> ( 0 <_ H \\/ H <_ 0 ) )' % A2)
    A3 = '( %s /\\ 0 <_ H )' % A2
    c3 = Closure(w, A3, {'A': [('RR', lift(w, ar, A3)), ('ge0', lift(w, a0, A3))], 'H': ('RR', lift(w, hr, A3))})
    h3 = w.s([], 'simpr', '( %s -> 0 <_ H )' % A3)
    ah3 = absv(w, A3, c3, 'H', h3)
    d3 = w.s([lift(w, dlt, A3), ah3], 'breqtrd', '( %s -> %s < H )' % (A3, D))
    f1 = absv(w, A3, c3, '( %s + H )' % D, linarith(w, A3, [h3, lift(w, a0, A3)], '0 <_ ( %s + H )' % D, closure=c3))
    f2 = absv(w, A3, c3, '( %s - H )' % D, linarith(w, A3, [d3], '( %s - H ) <_ 0' % D, closure=c3), nonneg=False)
    for t_ in [AH, '( abs ` ( %s + H ) )' % D, '( abs ` ( %s - H ) )' % D]:
        c3.leaf(t_, 'RR', c3.mem(t_, 'RR'))
    z3 = lineq(w, A3, LHS, '0', hyps=[f1, f2, ah3], closure=c3)
    A4 = '( %s /\\ H <_ 0 )' % A2
    c4 = Closure(w, A4, {'A': [('RR', lift(w, ar, A4)), ('ge0', lift(w, a0, A4))], 'H': ('RR', lift(w, hr, A4))})
    h4 = w.s([], 'simpr', '( %s -> H <_ 0 )' % A4)
    ah4 = absv(w, A4, c4, 'H', h4, nonneg=False)
    d4 = w.s([lift(w, dlt, A4), ah4], 'breqtrd', '( %s -> %s < -u H )' % (A4, D))
    g1 = absv(w, A4, c4, '( %s + H )' % D, linarith(w, A4, [d4], '( %s + H ) <_ 0' % D, closure=c4), nonneg=False)
    g2 = absv(w, A4, c4, '( %s - H )' % D, linarith(w, A4, [h4, lift(w, a0, A4)], '0 <_ ( %s - H )' % D, closure=c4))
    for t_ in [AH, '( abs ` ( %s + H ) )' % D, '( abs ` ( %s - H ) )' % D]:
        c4.leaf(t_, 'RR', c4.mem(t_, 'RR'))
    z4 = lineq(w, A4, LHS, '0', hyps=[g1, g2, ah4], closure=c4)
    z = w.s([z3, z4, sg], 'mpjaodan', '( %s -> %s = 0 )' % (A2, LHS))
    c2.leaf(T, 'RR', c2.mem(T, 'RR'))
    r2 = eqt(w, A2, z, eqc(w, A2, eqt(w, A2, dst(w, A2, [if_], 'oveq2d', '( 2 x. %s ) = ( 2 x. 0 )' % T), a1(w, A2, '2t0e0', '( 2 x. 0 ) = 0'))))
    em = w.s([], 'exmidd' if False else 'exmid', '( %s \\/ -. %s )' % (cond, cond))
    w.s([r1, r2, w.s([em], 'a1i', '( %s -> ( %s \\/ -. %s ) )' % (A0, cond, cond))], 'mpjaodan', '( %s -> %s = ( 2 x. %s ) )' % (A0, LHS, T))
    qedlast(w)
    go(w)



def sin2abs(w, ante, c, x):
    """( ante -> ( ( sin ` ( abs ` x ) ) ^ 2 ) = ( ( sin ` x ) ^ 2 ) ) for real x (closure c)"""
    ax = '( abs ` %s )' % x
    ao = ap(w, ante, 'absor', [c.mem(x, 'RR')], '( %s = %s \\/ %s = -u %s )' % (ax, x, ax, x))
    S = '( ( sin ` %s ) ^ 2 )'
    A1 = '( %s /\\ %s = %s )' % (ante, ax, x)
    k1 = dst(w, A1, [dst(w, A1, [w.s([], 'simpr', '( %s -> %s = %s )' % (A1, ax, x))], 'fveq2d', '( sin ` %s ) = ( sin ` %s )' % (ax, x))], 'oveq1d',
             '%s = %s' % (S % ax, S % x))
    A2 = '( %s /\\ %s = -u %s )' % (ante, ax, x)
    xc = lift(w, c.mem(x, 'CC'), A2)
    s2 = eqt(w, A2, dst(w, A2, [w.s([], 'simpr', '( %s -> %s = -u %s )' % (A2, ax, x))], 'fveq2d', '( sin ` %s ) = ( sin ` -u %s )' % (ax, x)),
             ap(w, A2, 'sinneg', [xc], '( sin ` -u %s ) = -u ( sin ` %s )' % (x, x)))
    k2 = eqt(w, A2, dst(w, A2, [s2], 'oveq1d', '%s = ( -u ( sin ` %s ) ^ 2 )' % (S % ax, x)),
             w.s([w.s([xc], 'sincld', '( %s -> ( sin ` %s ) e. CC )' % (A2, x))], 'sqnegd', '( %s -> ( -u ( sin ` %s ) ^ 2 ) = %s )' % (A2, x, S % x)))
    return w.s([k1, k2, ao], 'mpjaodan', '( %s -> %s = %s )' % (ante, S % ax, S % x))


def mvhq():
    w = W('mvhq', 'The integral of ( 1 - cos ( B t ) ) / t ^ 2 over ( 0 , R ) is ( pi / 2 ) | B | up to 2 / R (1 - cos B t = 2 sin ^ 2 ( | B | t / 2 ) and mvgr).')
    A0 = '( B e. RR /\\ R e. RR+ )'
    P = parts(w, A0)
    br, rp = P['B e. RR'], P['R e. RR+']
    cl = Closure(w, A0, {'B': ('RR', br), 'R': ('RR+', rp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    AB = '( abs ` B )'; a = '( %s / 2 )' % AB; I = IOO('0', 'R')
    a0 = w.s([cl.mem(AB, 'RR'), a1(w, A0, '2rp', '2 e. RR+'), w.s([cl.mem('B', 'CC')], 'absge0d', '( %s -> 0 <_ %s )' % (A0, AB))], 'divge0d', '( %s -> 0 <_ %s )' % (A0, a))
    cl.leaf(a, 'RR', cl.mem(a, 'RR'))
    # pointwise
    At = '( %s /\\ t e. %s )' % (A0, I)
    mt = w.s([], 'simpr', '( %s -> t e. %s )' % (At, I))
    tr = ap(w, At, 'elioore', [mt], 't e. RR')
    t0 = dst(w, At, [ap(w, At, 'eliooord', [mt], '( 0 < t /\\ t < R )')], 'simpld', '0 < t')
    ct = Closure(w, At, {'B': ('RR', lift(w, br, At)), 't': [('RR', tr), ('gt0', t0)], a: ('RR', lift(w, cl.mem(a, 'RR'), At))})
    x = '( ( B / 2 ) x. t )'
    c2 = ap(w, At, 'cos2tsin', [ct.mem(x, 'CC')], '( cos ` ( 2 x. %s ) ) = ( 1 - ( 2 x. ( ( sin ` %s ) ^ 2 ) ) )' % (x, x))
    cB = eqt(w, At, dst(w, At, [ringeq(w, At, 'B x. t'.join(['( ', ' )']), '( 2 x. %s )' % x, ct)], 'fveq2d', '( cos ` ( B x. t ) ) = ( cos ` ( 2 x. %s ) )' % x), c2)
    ax = '( abs ` %s )' % x
    am = w.s([ct.mem('( B / 2 )', 'CC'), ct.mem('t', 'CC')], 'absmuld', '( %s -> %s = ( ( abs ` ( B / 2 ) ) x. ( abs ` t ) ) )' % (At, ax))
    ad = w.s([ct.mem('B', 'CC'), a1(w, At, '2cn', '2 e. CC'), a1(w, At, '2ne0', '2 =/= 0')], 'absdivd', '( %s -> ( abs ` ( B / 2 ) ) = ( %s / ( abs ` 2 ) ) )' % (At, AB))
    a2 = w.s([a1(w, At, '2re', '2 e. RR'), a1(w, At, '0le2', '0 <_ 2')], 'absidd', '( %s -> ( abs ` 2 ) = 2 )' % At)
    ad2 = eqt(w, At, ad, dst(w, At, [a2], 'oveq2d', '( %s / ( abs ` 2 ) ) = %s' % (AB, a)))
    at_ = w.s([tr, ltle(w, At, ct, t0)], 'absidd', '( %s -> ( abs ` t ) = t )' % At)
    axe = eqt(w, At, am, dst(w, At, [ad2, at_], 'oveq12d', '( ( abs ` ( B / 2 ) ) x. ( abs ` t ) ) = ( %s x. t )' % a))
    sa = sin2abs(w, At, ct, x)
    sq = eqt(w, At, eqc(w, At, sa), dst(w, At, [dst(w, At, [axe], 'fveq2d', '( sin ` %s ) = ( sin ` ( %s x. t ) )' % (ax, a))], 'oveq1d',
                                            '( ( sin ` %s ) ^ 2 ) = %s' % (ax, KS(a))))       # sin^2 x = KS(a)
    one = dst(w, At, [dst(w, At, [dst(w, At, [sq], 'oveq2d', '( 2 x. ( ( sin ` %s ) ^ 2 ) ) = ( 2 x. %s )' % (x, KS(a)))], 'oveq2d',
                                  '( 1 - ( 2 x. ( ( sin ` %s ) ^ 2 ) ) ) = ( 1 - ( 2 x. %s ) )' % (x, KS(a)))], 'id', 'x') if False else \
        dst(w, At, [dst(w, At, [sq], 'oveq2d', '( 2 x. ( ( sin ` %s ) ^ 2 ) ) = ( 2 x. %s )' % (x, KS(a)))], 'oveq2d',
            '( 1 - ( 2 x. ( ( sin ` %s ) ^ 2 ) ) ) = ( 1 - ( 2 x. %s ) )' % (x, KS(a)))
    cB2 = eqt(w, At, cB, one)                    # cos ( B t ) = 1 - 2 KS(a)
    ct.leaf(KS(a), 'RR', ct.mem(KS(a), 'RR'))
    ct.leaf('( cos ` ( B x. t ) )', 'RR', ct.mem('( cos ` ( B x. t ) )', 'RR'))
    num = lineq(w, At, '( 1 - ( cos ` ( B x. t ) ) )', '( 2 x. %s )' % KS(a), hyps=[cB2], closure=ct)
    hq = eqt(w, At, dst(w, At, [num], 'oveq1d', '%s = ( ( 2 x. %s ) / ( t ^ 2 ) )' % (HQ('B'), KS(a))),
             w.s([a1(w, At, '2cn', '2 e. CC'), ct.mem(KS(a), 'CC'), ct.mem('( t ^ 2 )', 'CC'), w.s([w.s([tr, w.s([t0], 'gt0ne0d', '( %s -> t =/= 0 )' % At)], 'sqgt0d', '( %s -> 0 < ( t ^ 2 ) )' % At)], 'gt0ne0d', '( %s -> ( t ^ 2 ) =/= 0 )' % At)],
                 'divassd', '( %s -> ( ( 2 x. %s ) / ( t ^ 2 ) ) = ( 2 x. %s ) )' % (At, KS(a), KQ(a))))
    mq = dst(w, A0, [hq], 'mpteq2dva', '( t e. %s |-> %s ) = ( t e. %s |-> ( 2 x. %s ) )' % (I, HQ('B'), I, KQ(a)))
    kb = ap(w, A0, 'mvkibl', [J(w, A0, J(w, A0, cl.mem(a, 'RR'), cl.mem(a, 'RR')), J(w, A0, w.s([], '0red', '( %s -> 0 e. RR )' % A0), cl.mem('R', 'RR'), a1(w, A0, '0le0', '0 <_ 0')))],
            '( ( t e. %s |-> %s ) e. L^1 /\\ ( t e. %s |-> %s ) e. L^1 )' % (I, KC(a, a), I, KQ(a)))
    kq = dst(w, A0, [kb], 'simprd', '( t e. %s |-> %s ) e. L^1' % (I, KQ(a)))
    kqc = ct.mem(KQ(a), 'CC')
    ib2 = w.s([a1(w, A0, '2cn', '2 e. CC'), kqc, kq], 'iblmulc2', '( %s -> ( t e. %s |-> ( 2 x. %s ) ) e. L^1 )' % (A0, I, KQ(a)))
    ibH = w.s([mq, ib2], 'eqeltrd', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, I, HQ('B')))
    iv = eqt(w, A0, dst(w, A0, [hq], 'itgeq2dv', '%s = %s' % (ITG(I, HQ('B')), ITG(I, '( 2 x. %s )' % KQ(a)))),
             eqc(w, A0, w.s([a1(w, A0, '2cn', '2 e. CC'), kqc, kq], 'itgmulc2', '( %s -> ( 2 x. %s ) = %s )' % (A0, ITG(I, KQ(a)), ITG(I, '( 2 x. %s )' % KQ(a))))))
    # bounds on G(a, R), a >_ 0
    Gi = ITG(I, KQ(a))
    lo = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), cl.mem(a, 'RR')], 'leloed', '( %s -> ( 0 <_ %s <-> ( 0 < %s \\/ 0 = %s ) ) )' % (A0, a, a, a))
    lo2 = w.s([a0, lo], 'mpbid', '( %s -> ( 0 < %s \\/ 0 = %s ) )' % (A0, a, a))
    BND = '( ( %s - ( 1 / R ) ) <_ %s /\\ %s <_ %s )' % (GA(a), Gi, Gi, GA(a))
    Ap = '( %s /\\ 0 < %s )' % (A0, a)
    arp = w.s([lift(w, cl.mem(a, 'RR'), Ap), w.s([], 'simpr', '( %s -> 0 < %s )' % (Ap, a))], 'elrpd', '( %s -> %s e. RR+ )' % (Ap, a))
    bp = ap(w, Ap, 'mvgr', [arp, lift(w, rp, Ap)], BND)
    Az = '( %s /\\ 0 = %s )' % (A0, a)
    z = w.s([], 'simpr', '( %s -> 0 = %s )' % (Az, a))
    Azt = '( %s /\\ t e. %s )' % (Az, I)
    mzt = w.s([], 'simpr', '( %s -> t e. %s )' % (Azt, I))
    tzr = ap(w, Azt, 'elioore', [mzt], 't e. RR')
    tz0 = dst(w, Azt, [ap(w, Azt, 'eliooord', [mzt], '( 0 < t /\\ t < R )')], 'simpld', '0 < t')
    zt = lift(w, z, Azt)
    k0 = dst(w, Azt, [eqc(w, Azt, zt)], 'oveq1d', '( %s x. t ) = ( 0 x. t )' % a)
    k1 = eqt(w, Azt, k0, w.s([w.s([tzr], 'recnd', '( %s -> t e. CC )' % Azt)], 'mul02d', '( %s -> ( 0 x. t ) = 0 )' % Azt))
    k2 = eqt(w, Azt, dst(w, Azt, [k1], 'fveq2d', '( sin ` ( %s x. t ) ) = ( sin ` 0 )' % a), a1(w, Azt, 'sin0', '( sin ` 0 ) = 0'))
    k3 = eqt(w, Azt, dst(w, Azt, [k2], 'oveq1d', '%s = ( 0 ^ 2 )' % KS(a)), a1(w, Azt, 'sq0', '( 0 ^ 2 ) = 0'))
    t2n = w.s([w.s([tzr, w.s([tz0], 'gt0ne0d', '( %s -> t =/= 0 )' % Azt)], 'sqgt0d', '( %s -> 0 < ( t ^ 2 ) )' % Azt)], 'gt0ne0d', '( %s -> ( t ^ 2 ) =/= 0 )' % Azt)
    k4 = eqt(w, Azt, dst(w, Azt, [k3], 'oveq1d', '%s = ( 0 / ( t ^ 2 ) )' % KQ(a)),
             w.s([w.s([w.s([tzr], 'resqcld', '( %s -> ( t ^ 2 ) e. RR )' % Azt)], 'recnd', '( %s -> ( t ^ 2 ) e. CC )' % Azt), t2n], 'div0d', '( %s -> ( 0 / ( t ^ 2 ) ) = 0 )' % Azt))
    g0 = eqt(w, Az, dst(w, Az, [k4], 'itgeq2dv', '%s = %s' % (Gi, ITG(I, '0'))), a1(w, Az, 'itgz', '%s = 0' % ITG(I, '0')))
    ga0 = eqt(w, Az, dst(w, Az, [dst(w, Az, [eqc(w, Az, z)], 'oveq1d', '( %s x. _pi ) = ( 0 x. _pi )' % a)], 'oveq1d', '%s = ( ( 0 x. _pi ) / 2 )' % GA(a)),
              w.s([], 'id', 'x') if False else eqt(w, Az, dst(w, Az, [w.s([lift(w, cl.mem('_pi', 'CC'), Az)], 'mul02d', '( %s -> ( 0 x. _pi ) = 0 )' % Az)], 'oveq1d', '( ( 0 x. _pi ) / 2 ) = ( 0 / 2 )'),
                                                   a1(w, Az, '2div0' if False else 'div0i' if False else 'id', 'x') if False else
                                                   w.s([a1(w, Az, '2cn', '2 e. CC'), a1(w, Az, '2ne0', '2 =/= 0')], 'div0d', '( %s -> ( 0 / 2 ) = 0 )' % Az)))
    cz = Closure(w, Az, {'R': ('RR+', lift(w, rp, Az))})
    cz.leaf(Gi, 'RR', w.s([g0, w.s([], '0red', '( %s -> 0 e. RR )' % Az)], 'eqeltrd', '( %s -> %s e. RR )' % (Az, Gi)))
    cz.leaf(GA(a), 'RR', lift(w, cl.mem(GA(a), 'RR'), Az))
    cz.leaf('( 1 / R )', 'RR', cz.mem('( 1 / R )', 'RR'))
    bz = J(w, Az, linarith(w, Az, [g0, ga0, cz.gt0('( 1 / R )')], '( %s - ( 1 / R ) ) <_ %s' % (GA(a), Gi), closure=cz),
           linarith(w, Az, [g0, ga0], '%s <_ %s' % (Gi, GA(a)), closure=cz))
    bnd = w.s([bp, bz, lo2], 'mpjaodan', '( %s -> %s )' % (A0, BND))
    bl = dst(w, A0, [bnd], 'simpld', '( %s - ( 1 / R ) ) <_ %s' % (GA(a), Gi))
    bu = dst(w, A0, [bnd], 'simprd', '%s <_ %s' % (Gi, GA(a)))
    # assemble
    IH = ITG(I, HQ('B'))
    cq = Closure(w, At, {'t': [('RR', tr), ('gt0', t0)], a: ('RR', lift(w, cl.mem(a, 'RR'), At))})
    cl.leaf(Gi, 'RR', w.s([cq.mem(KQ(a), 'RR'), kq], 'itgrecl', '( %s -> %s e. RR )' % (A0, Gi)))
    cl.leaf(IH, 'RR', w.s([iv, cl.mem('( 2 x. %s )' % Gi, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A0, IH)))
    cl.leaf(AB, 'RR', cl.mem(AB, 'RR'))
    ca = Closure(w, A0, {AB: ('RR', cl.mem(AB, 'RR')), '_pi': ('RR', cl.mem('_pi', 'RR'))})
    ge = ringeq(w, A0, '( 2 x. %s )' % GA(a), '( %s x. %s )' % (PI2, AB), ca)
    cl.leaf(GA(a), 'RR', cl.mem(GA(a), 'RR'))
    cl.leaf('( %s x. %s )' % (PI2, AB), 'RR', cl.mem('( %s x. %s )' % (PI2, AB), 'RR'))
    cl.leaf('( 1 / R )', 'RR', cl.mem('( 1 / R )', 'RR'))
    DIFF = '( %s - ( %s x. %s ) )' % (IH, PI2, AB)
    r2 = w.s([a1(w, A0, '2cn', '2 e. CC'), cl.mem('R', 'CC'), cl.ne0('R')], 'divrecd', '( %s -> ( 2 / R ) = ( 2 x. ( 1 / R ) ) )' % A0)
    cl.leaf('( 2 / R )', 'RR', cl.mem('( 2 / R )', 'RR'))
    l1 = linarith(w, A0, [iv, bl, ge, r2], '-u ( 2 / R ) <_ %s' % DIFF, closure=cl)
    l2 = linarith(w, A0, [iv, bu, ge, cl.gt0('( 1 / R )'), r2], '%s <_ ( 2 / R )' % DIFF, closure=cl)
    ab = w.s([w.s([l1, l2], 'jca', '( %s -> ( -u ( 2 / R ) <_ %s /\\ %s <_ ( 2 / R ) ) )' % (A0, DIFF, DIFF)),
              w.s([cl.mem(DIFF, 'RR'), cl.mem('( 2 / R )', 'RR')], 'absled', '( %s -> ( ( abs ` %s ) <_ ( 2 / R ) <-> ( -u ( 2 / R ) <_ %s /\\ %s <_ ( 2 / R ) ) ) )' % (A0, DIFF, DIFF, DIFF))],
             'mpbird', '( %s -> ( abs ` %s ) <_ ( 2 / R ) )' % (A0, DIFF))
    J(w, A0, ibH, ab)
    qedlast(w)
    go(w)


def mvfej():
    w = W('mvfej', 'The Fejer identity in finite form: the integral of sin ^ 2 ( A t ) cos ( H t ) / t ^ 2 over ( 0 , R ) is ( pi / 4 ) max ( 0 , 2 A - | H | ) up to 2 / R (replaces MeanValue integral_fejer_mul_exp: no Fourier inversion).')
    A0 = '( ( A e. RR /\\ 0 <_ A ) /\\ ( H e. RR /\\ R e. RR+ ) )'
    P = parts(w, A0)
    ar, a0, hr, rp = P['A e. RR'], P['0 <_ A'], P['H e. RR'], P['R e. RR+']
    cl = Closure(w, A0, {'A': ('RR', ar), 'H': ('RR', hr), 'R': ('RR+', rp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    I = IOO('0', 'R')
    D = '( 2 x. A )'
    b1 = '( %s + H )' % D; b2 = '( %s - H )' % D; b3 = 'H'
    H1, H2, H3 = HQ(b1), HQ(b2), HQ(b3)
    # pointwise identity
    At = '( %s /\\ t e. %s )' % (A0, I)
    mt = w.s([], 'simpr', '( %s -> t e. %s )' % (At, I))
    tr = ap(w, At, 'elioore', [mt], 't e. RR')
    t0 = dst(w, At, [ap(w, At, 'eliooord', [mt], '( 0 < t /\\ t < R )')], 'simpld', '0 < t')
    t2 = '( t ^ 2 )'
    t2p = w.s([tr, w.s([t0], 'gt0ne0d', '( %s -> t =/= 0 )' % At)], 'sqgt0d', '( %s -> 0 < %s )' % (At, t2))
    ct = Closure(w, At, {'A': ('RR', lift(w, ar, At)), 'H': ('RR', lift(w, hr, At)), 't': [('RR', tr), ('gt0', t0)],
                         t2: [('RR', w.s([tr], 'resqcld', '( %s -> %s e. RR )' % (At, t2))), ('gt0', t2p), ('ne0', w.s([t2p], 'gt0ne0d', '( %s -> %s =/= 0 )' % (At, t2)))]})
    At_ = '( A x. t )'
    c2 = ap(w, At, 'cos2tsin', [ct.mem(At_, 'CC')], '( cos ` ( 2 x. %s ) ) = ( 1 - ( 2 x. %s ) )' % (At_, KS('A')))
    C2A = '( cos ` ( 2 x. %s ) )' % At_; CH = '( cos ` ( H x. t ) )'
    cm = ap(w, At, 'cosmul', [ct.mem('( 2 x. %s )' % At_, 'CC'), ct.mem('( H x. t )', 'CC')],
            '( %s x. %s ) = ( ( ( cos ` ( ( 2 x. %s ) - ( H x. t ) ) ) + ( cos ` ( ( 2 x. %s ) + ( H x. t ) ) ) ) / 2 )' % (C2A, CH, At_, At_))
    g1 = dst(w, At, [ringeq(w, At, '( ( 2 x. %s ) - ( H x. t ) )' % At_, '( %s x. t )' % b2, ct)], 'fveq2d',
             '( cos ` ( ( 2 x. %s ) - ( H x. t ) ) ) = ( cos ` ( %s x. t ) )' % (At_, b2))
    g2 = dst(w, At, [ringeq(w, At, '( ( 2 x. %s ) + ( H x. t ) )' % At_, '( %s x. t )' % b1, ct)], 'fveq2d',
             '( cos ` ( ( 2 x. %s ) + ( H x. t ) ) ) = ( cos ` ( %s x. t ) )' % (At_, b1))
    CB1 = '( cos ` ( %s x. t ) )' % b1; CB2 = '( cos ` ( %s x. t ) )' % b2
    cm2 = eqt(w, At, cm, dst(w, At, [dst(w, At, [g1, g2], 'oveq12d', '( ( cos ` ( ( 2 x. %s ) - ( H x. t ) ) ) + ( cos ` ( ( 2 x. %s ) + ( H x. t ) ) ) ) = ( %s + %s )' % (At_, At_, CB2, CB1))],
                                'oveq1d', '( ( ( cos ` ( ( 2 x. %s ) - ( H x. t ) ) ) + ( cos ` ( ( 2 x. %s ) + ( H x. t ) ) ) ) / 2 ) = ( ( %s + %s ) / 2 )' % (At_, At_, CB2, CB1)))
    for t_ in [KS('A'), C2A, CH, CB1, CB2]:
        ct.leaf(t_, 'RR', ct.mem(t_, 'RR'))
    ks = lineq(w, At, KS('A'), '( ( 1 - %s ) / 2 )' % C2A, hyps=[c2], closure=ct)
    p1 = dst(w, At, [ks], 'oveq1d', '( %s x. %s ) = ( ( ( 1 - %s ) / 2 ) x. %s )' % (KS('A'), CH, C2A, CH))
    p2 = ringeq(w, At, '( ( ( 1 - %s ) / 2 ) x. %s )' % (C2A, CH), '( ( %s / 2 ) - ( ( %s x. %s ) / 2 ) )' % (CH, C2A, CH), ct)
    ct.leaf('( %s x. %s )' % (C2A, CH), 'RR', ct.mem('( %s x. %s )' % (C2A, CH), 'RR'))
    NUM = '( ( 1 / 4 ) x. ( ( ( 1 - %s ) + ( 1 - %s ) ) - ( 2 x. ( 1 - %s ) ) ) )' % (CB1, CB2, CH)
    ct.leaf('( %s x. %s )' % (KS('A'), CH), 'RR', ct.mem('( %s x. %s )' % (KS('A'), CH), 'RR'))
    p3 = lineq(w, At, '( %s x. %s )' % (KS('A'), CH), NUM, hyps=[eqt(w, At, p1, p2), cm2], closure=ct)
    # divide by t ^ 2
    kc1 = dst(w, At, [p3], 'oveq1d', '%s = ( %s / %s )' % (KC('A', 'H'), NUM, t2))
    it2 = '( 1 / %s )' % t2
    def dr(X):
        return w.s([ct.mem(X, 'CC'), ct.mem(t2, 'CC'), ct.ne0(t2)], 'divrecd', '( %s -> ( %s / %s ) = ( %s x. %s ) )' % (At, X, t2, X, it2))
    F = '( ( 1 / 4 ) x. ( ( %s + %s ) - ( 2 x. %s ) ) )' % (H1, H2, H3)
    e0 = dr(NUM); e1 = dr('( 1 - %s )' % CB1); e2 = dr('( 1 - %s )' % CB2); e3 = dr('( 1 - %s )' % CH)
    rw_ = w.rewrite(F, {H1: ('( ( 1 - %s ) x. %s )' % (CB1, it2), e1), H2: ('( ( 1 - %s ) x. %s )' % (CB2, it2), e2), H3: ('( ( 1 - %s ) x. %s )' % (CH, it2), e3)}, At)
    rc = Closure(w, At, {CB1: ('RR', ct.mem(CB1, 'RR')), CB2: ('RR', ct.mem(CB2, 'RR')), CH: ('RR', ct.mem(CH, 'RR')), it2: ('RR', ct.mem(it2, 'RR'))})
    core = ringeq(w, At, '( %s x. %s )' % (NUM, it2), rw_[1], rc)
    kcF = eqt(w, At, eqt(w, At, eqt(w, At, kc1, e0), core), eqc(w, At, rw_[0]))        # KC = F
    # integrals
    hv = {}
    for b in (b1, b2, b3):
        hv[b] = ap(w, A0, 'mvhq', [cl.mem(b, 'RR'), rp], '( ( t e. %s |-> %s ) e. L^1 /\\ ( abs ` ( %s - ( %s x. ( abs ` %s ) ) ) ) <_ ( 2 / R ) )' % (I, HQ(b), ITG(I, HQ(b)), PI2, b))
    ib = {b: dst(w, A0, [hv[b]], 'simpld', '( t e. %s |-> %s ) e. L^1' % (I, HQ(b))) for b in (b1, b2, b3)}
    hc = {b: ct.mem(HQ(b), 'CC') for b in (b1, b2, b3)}
    i12 = w.s([hc[b1], ib[b1], hc[b2], ib[b2]], 'ibladd', '( %s -> ( t e. %s |-> ( %s + %s ) ) e. L^1 )' % (A0, I, H1, H2))
    two = a1(w, A0, '2cn', '2 e. CC')
    i3 = w.s([two, hc[b3], ib[b3]], 'iblmulc2', '( %s -> ( t e. %s |-> ( 2 x. %s ) ) e. L^1 )' % (A0, I, H3))
    S12 = '( ( %s + %s ) - ( 2 x. %s ) )' % (H1, H2, H3)
    i123 = w.s([ct.mem('( %s + %s )' % (H1, H2), 'CC'), i12, ct.mem('( 2 x. %s )' % H3, 'CC'), i3], 'iblsub', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, I, S12))
    q1 = w.s([a1(w, A0, '4cn', '4 e. CC') and cl.mem('( 1 / 4 )', 'CC'), ct.mem(S12, 'CC'), i123], 'itgmulc2', '( %s -> ( ( 1 / 4 ) x. %s ) = %s )' % (A0, ITG(I, S12), ITG(I, F)))
    q2 = w.s([ct.mem('( %s + %s )' % (H1, H2), 'CC'), i12, ct.mem('( 2 x. %s )' % H3, 'CC'), i3], 'itgsub', '( %s -> %s = ( %s - %s ) )' % (A0, ITG(I, S12), ITG(I, '( %s + %s )' % (H1, H2)), ITG(I, '( 2 x. %s )' % H3)))
    q3 = w.s([hc[b1], ib[b1], hc[b2], ib[b2]], 'itgadd', '( %s -> %s = ( %s + %s ) )' % (A0, ITG(I, '( %s + %s )' % (H1, H2)), ITG(I, H1), ITG(I, H2)))
    q4 = w.s([two, hc[b3], ib[b3]], 'itgmulc2', '( %s -> ( 2 x. %s ) = %s )' % (A0, ITG(I, H3), ITG(I, '( 2 x. %s )' % H3)))
    IK = ITG(I, KC('A', 'H'))
    ik = eqt(w, A0, dst(w, A0, [kcF], 'itgeq2dv', '%s = %s' % (IK, ITG(I, F))), eqc(w, A0, q1))
    cq = Closure(w, A0, {})
    for b in (b1, b2, b3):
        cl.leaf(ITG(I, HQ(b)), 'RR', w.s([ct.mem(HQ(b), 'RR'), ib[b]], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITG(I, HQ(b)))))
    kb = ap(w, A0, 'mvkibl', [J(w, A0, J(w, A0, ar, hr), J(w, A0, w.s([], '0red', '( %s -> 0 e. RR )' % A0), cl.mem('R', 'RR'), a1(w, A0, '0le0', '0 <_ 0')))],
            '( ( t e. %s |-> %s ) e. L^1 /\\ ( t e. %s |-> %s ) e. L^1 )' % (I, KC('A', 'H'), I, KQ('A')))
    kcib = dst(w, A0, [kb], 'simpld', '( t e. %s |-> %s ) e. L^1' % (I, KC('A', 'H')))
    cl.leaf(IK, 'RR', w.s([ct.mem(KC('A', 'H'), 'RR'), kcib], 'itgrecl', '( %s -> %s e. RR )' % (A0, IK)))
    for t_ in [ITG(I, S12), ITG(I, '( %s + %s )' % (H1, H2)), ITG(I, '( 2 x. %s )' % H3)]:
        pass
    ITS = ITG(I, S12)
    cl.leaf(ITS, 'RR', w.s([ct.mem(S12, 'RR'), i123], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITS)))
    cl.leaf(ITG(I, '( %s + %s )' % (H1, H2)), 'RR', w.s([ct.mem('( %s + %s )' % (H1, H2), 'RR'), i12], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITG(I, '( %s + %s )' % (H1, H2)))))
    cl.leaf(ITG(I, '( 2 x. %s )' % H3), 'RR', w.s([ct.mem('( 2 x. %s )' % H3, 'RR'), i3], 'itgrecl', '( %s -> %s e. RR )' % (A0, ITG(I, '( 2 x. %s )' % H3))))
    # the triangle
    tri = ap(w, A0, 'mvtriabs', [w.s([ar, a0, hr], '3jca', '( %s -> ( A e. RR /\\ 0 <_ A /\\ H e. RR ) )' % A0)],
             '( ( ( abs ` %s ) + ( abs ` %s ) ) - ( 2 x. ( abs ` H ) ) ) = ( 2 x. %s )' % (b1, b2, TRI(D, 'H')))
    T = TRI(D, 'H')
    AB1, AB2, AB3 = '( abs ` %s )' % b1, '( abs ` %s )' % b2, '( abs ` H )'
    ca = Closure(w, A0, {AB1: ('RR', cl.mem(AB1, 'RR')), AB2: ('RR', cl.mem(AB2, 'RR')), AB3: ('RR', cl.mem(AB3, 'RR')), '_pi': ('RR', cl.mem('_pi', 'RR')),
                         T: ('RR', cl.mem(T, 'RR'))})
    LIN = '( ( ( %s x. %s ) + ( %s x. %s ) ) - ( 2 x. ( %s x. %s ) ) )' % (PI2, AB1, PI2, AB2, PI2, AB3)
    t1 = ringeq(w, A0, LIN, '( %s x. ( ( %s + %s ) - ( 2 x. %s ) ) )' % (PI2, AB1, AB2, AB3), ca)
    t2_ = dst(w, A0, [tri], 'oveq2d', '( %s x. ( ( %s + %s ) - ( 2 x. %s ) ) ) = ( %s x. ( 2 x. %s ) )' % (PI2, AB1, AB2, AB3, PI2, T))
    t3 = ringeq(w, A0, '( %s x. ( 2 x. %s ) )' % (PI2, T), '( 4 x. ( ( _pi / 4 ) x. %s ) )' % T, ca)
    TT = eqt(w, A0, eqt(w, A0, t1, t2_), t3)
    # the three abs bounds as pairs of linear inequalities
    lins = []
    for b in (b1, b2, b3):
        DIF = '( %s - ( %s x. ( abs ` %s ) ) )' % (ITG(I, HQ(b)), PI2, b)
        bnd = dst(w, A0, [hv[b]], 'simprd', '( abs ` %s ) <_ ( 2 / R )' % DIF)
        bi = w.s([cl.mem(DIF, 'RR'), cl.mem('( 2 / R )', 'RR')], 'absled', '( %s -> ( ( abs ` %s ) <_ ( 2 / R ) <-> ( -u ( 2 / R ) <_ %s /\\ %s <_ ( 2 / R ) ) ) )' % (A0, DIF, DIF, DIF))
        pr = w.s([bnd, bi], 'mpbid', '( %s -> ( -u ( 2 / R ) <_ %s /\\ %s <_ ( 2 / R ) ) )' % (A0, DIF, DIF))
        lins += [dst(w, A0, [pr], 'simpld', '-u ( 2 / R ) <_ %s' % DIF), dst(w, A0, [pr], 'simprd', '%s <_ ( 2 / R )' % DIF)]
    for t_ in ['( %s x. %s )' % (PI2, x) for x in (AB1, AB2, AB3)] + ['( ( _pi / 4 ) x. %s )' % T, '( 2 / R )']:
        cl.leaf(t_, 'RR', cl.mem(t_, 'RR'))
    DF = '( %s - ( ( _pi / 4 ) x. %s ) )' % (IK, T)
    hy = [ik, q2, q3, q4, TT] + lins
    l1 = linarith(w, A0, hy, '-u ( 2 / R ) <_ %s' % DF, closure=cl)
    l2 = linarith(w, A0, hy, '%s <_ ( 2 / R )' % DF, closure=cl)
    ab = w.s([w.s([l1, l2], 'jca', '( %s -> ( -u ( 2 / R ) <_ %s /\\ %s <_ ( 2 / R ) ) )' % (A0, DF, DF)),
              w.s([cl.mem(DF, 'RR'), cl.mem('( 2 / R )', 'RR')], 'absled', '( %s -> ( ( abs ` %s ) <_ ( 2 / R ) <-> ( -u ( 2 / R ) <_ %s /\\ %s <_ ( 2 / R ) ) ) )' % (A0, DF, DF, DF))],
             'mpbird', '( %s -> ( abs ` %s ) <_ ( 2 / R ) )' % (A0, DF))
    J(w, A0, kcib, ab)
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvtriabs()
    mvhq()
    mvfej()
