"""Sortie Z4b, section D: the additive large sieve over separated points
(LargeSieve points_large_sieve): the disjoint-interval summation, AM-GM under the
integral, the generic Gallagher inequality for a differentiable F, and its
instance at a trigonometric polynomial."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from z4blib import *
from lin import linarith, nlinarith, lineq
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def YI(v): return '( Y ` %s )' % v
def JIv(v): return JI(YI(v))


def ioo3(w, ante, mem, v, lo, hi, lor, hir):
    """from mem: ( ante -> v e. ( lo (,) hi ) ): steps lo < v, v < hi, v e. RR"""
    e = ap(w, ante, 'elioo2', [st(w, ante, [lor], 'rexrd', '%s e. RR*' % lo), st(w, ante, [hir], 'rexrd', '%s e. RR*' % hi)],
           '( %s e. %s <-> ( %s e. RR /\\ %s < %s /\\ %s < %s ) )' % (v, IOO(lo, hi), v, lo, v, v, hi))
    t = st(w, ante, [mem, e], 'mpbid', '( %s e. RR /\\ %s < %s /\\ %s < %s )' % (v, lo, v, v, hi))
    return (st(w, ante, [t], 'simp2d', '%s < %s' % (lo, v)), st(w, ante, [t], 'simp3d', '%s < %s' % (v, hi)),
            st(w, ante, [t], 'simp1d', '%s e. RR' % v))


if __name__ == '__main__':
    # ---- lsdisjpt
    A0 = '( %s /\\ %s /\\ ( H e. RR /\\ 0 <_ H ) )' % (PTS, SEP)
    w = W('lsdisjpt', 'At every point, the indicator sum of the intervals of length D centred at D-separated points, weighted by H >_ 0, is at most H (LargeSieve points_large_sieve, hpair).')
    P = parts(w, A0)
    pf, yf, drp, sep, hr, h0 = P['P e. Fin'], P['Y : P --> RR'], P['D e. RR+'], P[SEP], P['H e. RR'], P['0 <_ H']
    SUMI = 'sum_ i e. P if ( t e. %s , H , 0 )' % JIv('i')
    # the key: two intervals containing t have the same centre index
    Ab = '( ( %s /\\ ( i e. P /\\ c e. P ) ) /\\ ( t e. %s /\\ t e. %s ) )' % (A0, JIv('i'), JIv('c'))
    L = lambda s_: lift(w, s_, Ab)
    ip = w.s([], 'simplrl', '( %s -> i e. P )' % Ab); cp = w.s([], 'simplrr', '( %s -> c e. P )' % Ab)
    yi = st(w, Ab, [L(yf), ip], 'ffvelcdmd', '%s e. RR' % YI('i')); yc = st(w, Ab, [L(yf), cp], 'ffvelcdmd', '%s e. RR' % YI('c'))
    cb = ctx(w, Ab, {'D': ('RR+', L(drp)), YI('i'): ('RR', yi), YI('c'): ('RR', yc)})
    def ends(v):
        return cb.mem('( %s - ( D / 2 ) )' % YI(v), 'RR'), cb.mem('( %s + ( D / 2 ) )' % YI(v), 'RR')
    li, hi_ = ends('i'); lc, hc = ends('c')
    ti = w.s([], 'simprl', '( %s -> t e. %s )' % (Ab, JIv('i'))); tc = w.s([], 'simprr', '( %s -> t e. %s )' % (Ab, JIv('c')))
    a1_, b1_, tr = ioo3(w, Ab, ti, 't', '( %s - ( D / 2 ) )' % YI('i'), '( %s + ( D / 2 ) )' % YI('i'), li, hi_)
    a2_, b2_, _ = ioo3(w, Ab, tc, 't', '( %s - ( D / 2 ) )' % YI('c'), '( %s + ( D / 2 ) )' % YI('c'), lc, hc)
    cb.leaf('t', 'RR', tr)
    DIF = '( %s - %s )' % (YI('i'), YI('c'))
    def gap(i, c, lo_lt, t_lt):
        Yi, Yc = YI(i), YI(c)
        lo = '( %s - ( D / 2 ) )' % Yi; hi = '( %s + ( D / 2 ) )' % Yc
        x1 = st(w, Ab, [cb.mem(lo, 'RR'), tr, cb.mem(hi, 'RR'), lo_lt, t_lt], 'lttrd', '%s < %s' % (lo, hi))
        x2 = st(w, Ab, [x1, st(w, Ab, [cb.mem(Yi, 'RR'), cb.mem('( D / 2 )', 'RR'), cb.mem(hi, 'RR')], 'ltsubaddd',
                                   '( %s < %s <-> %s < ( %s + ( D / 2 ) ) )' % (lo, hi, Yi, hi))], 'mpbid', '%s < ( %s + ( D / 2 ) )' % (Yi, hi))
        x3 = eqt(w, Ab, st(w, Ab, [cb.mem(Yc, 'CC'), cb.mem('( D / 2 )', 'CC'), cb.mem('( D / 2 )', 'CC')], 'addassd',
                           '( %s + ( D / 2 ) ) = ( %s + ( ( D / 2 ) + ( D / 2 ) ) )' % (hi, Yc)),
                 st(w, Ab, [st(w, Ab, [cb.mem('D', 'CC')], '2halvesd', '( ( D / 2 ) + ( D / 2 ) ) = D')], 'oveq2d', '( %s + ( ( D / 2 ) + ( D / 2 ) ) ) = ( %s + D )' % (Yc, Yc)))
        x4 = st(w, Ab, [x2, x3], 'breqtrd', '%s < ( %s + D )' % (Yi, Yc))
        return st(w, Ab, [x4, st(w, Ab, [cb.mem(Yi, 'RR'), cb.mem(Yc, 'RR'), cb.mem('D', 'RR')], 'ltsubadd2d', '( ( %s - %s ) < D <-> %s < ( %s + D ) )' % (Yi, Yc, Yi, Yc))],
                  'mpbird', '( %s - %s ) < D' % (Yi, Yc))
    u1 = gap('i', 'c', a1_, b2_)
    u2a = gap('c', 'i', a2_, b1_)
    DIF2 = '( %s - %s )' % (YI('c'), YI('i'))
    u2b = st(w, Ab, [st(w, Ab, [cb.mem(YI('i'), 'CC'), cb.mem(YI('c'), 'CC')], 'negsubdi2d', '-u %s = %s' % (DIF, DIF2)), u2a], 'eqbrtrd', '-u %s < D' % DIF)
    u2 = st(w, Ab, [cb.mem(DIF, 'RR'), cb.mem('D', 'RR'), u2b], 'ltnegcon1d', '-u D < %s' % DIF)
    dfr = cb.mem(DIF, 'RR'); dr = cb.mem('D', 'RR')
    alt = st(w, Ab, [J(w, Ab, u2, u1), ap(w, Ab, 'abslt', [dfr, dr], '( ( abs ` %s ) < D <-> ( -u D < %s /\\ %s < D ) )' % (DIF, DIF, DIF))], 'mpbird', '( abs ` %s ) < D' % DIF)
    abr = cb.mem('( abs ` %s )' % DIF, 'RR')
    nle = st(w, Ab, [alt, st(w, Ab, [abr, dr], 'ltnled', '( ( abs ` %s ) < D <-> -. D <_ ( abs ` %s ) )' % (DIF, DIF))], 'mpbid', '-. D <_ ( abs ` %s )' % DIF)
    s1, _ = w.wcongr('( a =/= b -> D <_ ( abs ` ( ( Y ` a ) - ( Y ` b ) ) ) )', {'a': 'i'}, 'a = i', {'a': w.s([], 'id', '( a = i -> a = i )')})
    s2, _ = w.wcongr('( i =/= b -> D <_ ( abs ` ( ( Y ` i ) - ( Y ` b ) ) ) )', {'b': 'c'}, 'b = c', {'b': w.s([], 'id', '( b = c -> b = c )')})
    inst = w.s([J(w, Ab, J(w, Ab, ip, cp), L(sep)), w.s([s1, s2], 'rspc2va', '( ( ( i e. P /\\ c e. P ) /\\ %s ) -> ( i =/= c -> D <_ ( abs ` %s ) ) )' % (SEP, DIF))],
               'syl', '( %s -> ( i =/= c -> D <_ ( abs ` %s ) ) )' % (Ab, DIF))
    nne_ = st(w, Ab, [nle, inst], 'mtod', '-. i =/= c')
    key = st(w, Ab, [nne_, w.s([], 'nne', '( -. i =/= c <-> i = c )')], 'sylib', 'i = c')
    # case A: some interval contains t
    Ac = '( %s /\\ ( c e. P /\\ t e. %s ) )' % (A0, JIv('c'))
    Aci = '( %s /\\ i e. P )' % Ac
    fw = w.s([key], 'expr' if False else 'ex', '( ( %s /\\ ( i e. P /\\ c e. P ) ) -> ( ( t e. %s /\\ t e. %s ) -> i = c ) )' % (A0, JIv('i'), JIv('c')))
    # re-associate: under Aci and t e. Ji -> i = c
    La = lambda s_: lift(w, s_, Aci)
    ipa = w.s([], 'simpr', '( %s -> i e. P )' % Aci); cpa = La(w.s([], 'simprl', '( %s -> c e. P )' % Ac)); tca = La(w.s([], 'simprr', '( %s -> t e. %s )' % (Ac, JIv('c'))))
    fw2 = st(w, Aci, [La(P[A0]) if A0 in P else lift(w, w.s([], 'simpl', '( %s -> %s )' % (Ac, A0)), Aci), J(w, Aci, ipa, cpa)], 'jca',
             '( %s /\\ ( i e. P /\\ c e. P ) )' % A0)
    fw3 = w.s([fw2, fw], 'syl', '( %s -> ( ( t e. %s /\\ t e. %s ) -> i = c ) )' % (Aci, JIv('i'), JIv('c')))
    imp1 = w.s([tca, fw3], 'mpan2d', '( %s -> ( t e. %s -> i = c ) )' % (Aci, JIv('i')))
    Aeq = '( %s /\\ i = c )' % Aci
    jeq, _ = w.wcongr('t e. %s' % JIv('i'), {'i': 'c'}, Aeq, {'i': w.s([], 'simpr', '( %s -> i = c )' % Aeq)})
    imp2 = w.s([st(w, Aeq, [lift(w, tca, Aeq), jeq], 'mpbird', 't e. %s' % JIv('i'))], 'ex', '( %s -> ( i = c -> t e. %s ) )' % (Aci, JIv('i')))
    bic = st(w, Aci, [imp1, imp2], 'impbid', '( t e. %s <-> i = c )' % JIv('i'))
    ifb = st(w, Aci, [bic], 'ifbid', 'if ( t e. %s , H , 0 ) = if ( i = c , H , 0 )' % JIv('i'))
    sm1 = st(w, Ac, [ifb], 'sumeq2dv', '%s = sum_ i e. P if ( i = c , H , 0 )' % SUMI)
    LA = lambda s_: lift(w, s_, Ac)
    sm2 = st(w, Ac, [w.s([], 'eqidd', '( i = c -> H = H )'), LA(pf), w.s([], 'simprl', '( %s -> c e. P )' % Ac), st(w, Ac, [LA(hr)], 'recnd', 'H e. CC')],
             'sumite', 'sum_ i e. P if ( i = c , H , 0 ) = H')
    cA = st(w, Ac, [eqt(w, Ac, sm1, sm2), st(w, Ac, [LA(hr)], 'leidd', 'H <_ H')], 'eqbrtrd', '%s <_ H' % SUMI)
    caseA = st(w, A0, [cA], 'rexlimdvaa', '( E. c e. P t e. %s -> %s <_ H )' % (JIv('c'), SUMI))
    # case B: no interval contains t
    An = '( %s /\\ -. E. c e. P t e. %s )' % (A0, JIv('c'))
    ral = st(w, An, [w.s([], 'simpr', '( %s -> -. E. c e. P t e. %s )' % (An, JIv('c'))),
                     w.s([], 'ralnex', '( A. c e. P -. t e. %s <-> -. E. c e. P t e. %s )' % (JIv('c'), JIv('c')))], 'sylibr', 'A. c e. P -. t e. %s' % JIv('c'))
    Ani = '( %s /\\ i e. P )' % An
    sb, _ = w.wcongr('-. t e. %s' % JIv('c'), {'c': 'i'}, 'c = i', {'c': w.s([], 'id', '( c = i -> c = i )')})
    nti = st(w, Ani, [sb, lift(w, ral, Ani), w.s([], 'simpr', '( %s -> i e. P )' % Ani)], 'rspcdva', '-. t e. %s' % JIv('i'))
    z = ap(w, Ani, 'iffalse', [nti], 'if ( t e. %s , H , 0 ) = 0' % JIv('i'))
    sz = st(w, An, [z], 'sumeq2dv', '%s = sum_ i e. P 0' % SUMI)
    s0 = ap(w, An, 'sumz', [st(w, An, [lift(w, pf, An)], 'olcd', '( P C_ ( ZZ>= ` 1 ) \\/ P e. Fin )')], 'sum_ i e. P 0 = 0')
    cB = st(w, An, [eqt(w, An, sz, s0), lift(w, h0, An)], 'eqbrtrd', '%s <_ H' % SUMI)
    caseB = w.s([cB], 'ex', '( %s -> ( -. E. c e. P t e. %s -> %s <_ H ) )' % (A0, JIv('c'), SUMI))
    w.qed([caseA, caseB], 'pm2.61d', STATEMENTS['lsdisjpt']); go(w)

    # ---- lsdisj
    w = W('lsdisj', 'The integrals of a nonnegative continuous function over the intervals of length D centred at D-separated points of [ 0 , 1 - D ] sum to at most its integral over ( -u ( D / 2 ) , -u ( D / 2 ) + 1 ) (LargeSieve points_large_sieve, hdisj).')
    hyps_of(w, 'lsdisj')
    A0 = 'ph'
    pf = st(w, A0, ['p'], 'simp1d', 'P e. Fin'); yf = st(w, A0, ['p'], 'simp2d', 'Y : P --> RR'); drp = st(w, A0, ['p'], 'simp3d', 'D e. RR+')
    K = KP(); kl = '-u ( D / 2 )'; kh = '( -u ( D / 2 ) + 1 )'
    c0 = ctx(w, A0, {'D': ('RR+', drp)})
    klr = c0.mem(kl, 'RR'); khr = c0.mem(kh, 'RR')
    IF_ = lambda v: 'if ( t e. %s , X , 0 )' % JIv(v)
    Ai = '( ph /\\ i e. P )'
    Li = lambda s_: lift(w, s_, Ai)
    ip = w.s([], 'simpr', '( %s -> i e. P )' % Ai)
    yi = st(w, Ai, [Li(yf), ip], 'ffvelcdmd', '%s e. RR' % YI('i'))
    rg, _ = w.wcongr('( 0 <_ ( Y ` a ) /\\ ( Y ` a ) <_ ( 1 - D ) )', {'a': 'i'}, 'a = i', {'a': w.s([], 'id', '( a = i -> a = i )')})
    rgi = st(w, Ai, [rg, Li('g'), ip], 'rspcdva', '( 0 <_ %s /\\ %s <_ ( 1 - D ) )' % (YI('i'), YI('i')))
    ci = ctx(w, Ai, {'D': ('RR+', Li(drp)), YI('i'): ('RR', yi)})
    lo = '( %s - ( D / 2 ) )' % YI('i'); hi = '( %s + ( D / 2 ) )' % YI('i')
    y0 = st(w, Ai, [rgi], 'simpld', '0 <_ %s' % YI('i')); y1 = st(w, Ai, [rgi], 'simprd', '%s <_ ( 1 - D )' % YI('i'))
    d2 = ci.mem('( D / 2 )', 'RR'); d2c = ci.mem('( D / 2 )', 'CC')
    l1a = st(w, Ai, [w.s([], '0red', '( %s -> 0 e. RR )' % Ai), yi, d2, y0], 'lesub1dd', '( 0 - ( D / 2 ) ) <_ %s' % lo)
    l1 = st(w, Ai, [a1(w, Ai, 'df-neg', '-u ( D / 2 ) = ( 0 - ( D / 2 ) )'), l1a], 'eqbrtrd', '%s <_ %s' % (kl, lo))
    l2a = st(w, Ai, [yi, ci.mem('( 1 - D )', 'RR'), d2, y1], 'leadd1dd', '%s <_ ( ( 1 - D ) + ( D / 2 ) )' % hi)
    dc = ci.mem('D', 'CC'); onec = w.s([], '1cnd', '( %s -> 1 e. CC )' % Ai)
    h1 = eqc(w, Ai, st(w, Ai, [onec, dc, d2c], 'subsubd', '( 1 - ( D - ( D / 2 ) ) ) = ( ( 1 - D ) + ( D / 2 ) )'))
    hh = eqt(w, Ai, st(w, Ai, [eqc(w, Ai, st(w, Ai, [dc], '2halvesd', '( ( D / 2 ) + ( D / 2 ) ) = D'))], 'oveq1d', '( D - ( D / 2 ) ) = ( ( ( D / 2 ) + ( D / 2 ) ) - ( D / 2 ) )'),
             st(w, Ai, [d2c, d2c], 'pncand', '( ( ( D / 2 ) + ( D / 2 ) ) - ( D / 2 ) ) = ( D / 2 )'))
    h2 = st(w, Ai, [hh], 'oveq2d', '( 1 - ( D - ( D / 2 ) ) ) = ( 1 - ( D / 2 ) )')
    h3 = eqt(w, Ai, st(w, Ai, [ci.mem(kl, 'CC'), onec], 'addcomd', '%s = ( 1 + -u ( D / 2 ) )' % kh), st(w, Ai, [onec, d2c], 'negsubd', '( 1 + -u ( D / 2 ) ) = ( 1 - ( D / 2 ) )'))
    l2e = eqt(w, Ai, eqt(w, Ai, h1, h2), eqc(w, Ai, h3))
    l2 = st(w, Ai, [l2a, l2e], 'breqtrd', '%s <_ %s' % (hi, kh))
    sub = ap(w, Ai, 'ioossioo', [J(w, Ai, st(w, Ai, [Li(klr)], 'rexrd', '%s e. RR*' % kl), st(w, Ai, [Li(khr)], 'rexrd', '%s e. RR*' % kh)), J(w, Ai, l1, l2)],
             '%s C_ %s' % (JIv('i'), K))
    # the integral over J_i as an integral over K of the truncated integrand
    Ait = '( %s /\\ t e. %s )' % (Ai, JIv('i'))
    tj = w.s([], 'simpr', '( %s -> t e. %s )' % (Ait, JIv('i')))
    ift = ap(w, Ait, 'iftrue', [tj], '%s = X' % IF_('i'))
    e1 = eqc(w, Ai, st(w, Ai, [ift], 'itgeq2dv', '%s = %s' % (ITG(JIv('i'), IF_('i')), ITG(JIv('i'), 'X'))))
    Aid = '( %s /\\ t e. ( %s \\ %s ) )' % (Ai, K, JIv('i'))
    nd = st(w, Aid, [w.s([], 'simpr', '( %s -> t e. ( %s \\ %s ) )' % (Aid, K, JIv('i')))], 'eldifbd', '-. t e. %s' % JIv('i'))
    iff = ap(w, Aid, 'iffalse', [nd], '%s = 0' % IF_('i'))
    e2 = st(w, Ai, [sub, iff], 'itgss', '%s = %s' % (ITG(JIv('i'), IF_('i')), ITG(K, IF_('i'))))
    e12 = eqt(w, Ai, e1, e2)     # S. J_i X = S. K IF
    # closures of the truncated integrand
    xr_ = lambda ante, a, b: w.s([w.inst('elioore'), 'r'], 'sylan2', '( ( ph /\\ t e. %s ) -> X e. RR )' % IOO(a, b))
    Aik = '( %s /\\ t e. %s )' % (Ai, K)
    xk = lift(w, xr_(A0, kl, kh), Aik) if False else None
    xrk = w.s([w.inst('elioore'), 'r'], 'sylan2', '( ( ph /\\ t e. %s ) -> X e. RR )' % K)
    Apk = '( ph /\\ t e. %s )' % K
    ifr = lambda ante, xst: st(w, ante, [xst, a1(w, ante, '0re', '0 e. RR')], 'ifcld', '%s e. RR' % IF_('i'))
    # ( ( ph /\\ ( t e. K /\\ i e. P ) ) -> IF e. CC )
    Atki = '( ph /\\ ( t e. %s /\\ i e. P ) )' % K
    xrtk = st(w, Atki, [lift(w, w.s([], 'simprl', '( %s -> t e. %s )' % (Atki, K)), Atki), ] and [w.s([], 'simpl', '( %s -> ph )' % Atki), w.s([], 'simprl', '( %s -> t e. %s )' % (Atki, K))], 'jca', '( ph /\\ t e. %s )' % K)
    xrtk2 = w.s([xrtk, xrk], 'syl', '( %s -> X e. RR )' % Atki)
    ifc = st(w, Atki, [ifr(Atki, xrtk2)], 'recnd', '%s e. CC' % IF_('i'))
    # integrability of IF over K (per i)
    Aij = '( %s /\\ t e. %s )' % (Ai, JIv('i'))
    ibj0 = w.s([Li(yf) and st(w, Ai, [yi, ci.mem('( D / 2 )', 'RR')], 'resubcld', '%s e. RR' % lo), st(w, Ai, [yi, ci.mem('( D / 2 )', 'RR')], 'readdcld', '%s e. RR' % hi), Li('c')],
               'lsibl', '( %s -> ( t e. %s |-> X ) e. L^1 )' % (Ai, JIv('i')))
    mq = st(w, Ai, [ift], 'mpteq2dva', '( t e. %s |-> %s ) = ( t e. %s |-> X )' % (JIv('i'), IF_('i'), JIv('i')))
    ibj = st(w, Ai, [mq, ibj0], 'eqeltrd', '( t e. %s |-> %s ) e. L^1' % (JIv('i'), IF_('i')))
    xrj = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Aij, Ai)), w.inst('simpl')], 'syl', '( %s -> ph )' % Aij),
               w.s([w.s([], 'simpr', '( %s -> t e. %s )' % (Aij, JIv('i'))), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % Aij), 'r'], 'syl2anc', '( %s -> X e. RR )' % Aij)
    ifcj = st(w, Aij, [ifr(Aij, xrj)], 'recnd', '%s e. CC' % IF_('i'))
    kdv = a1(w, Ai, 'ioombl', '%s e. dom vol' % K)
    ibk = st(w, Ai, [sub, kdv, ifcj, iff, ibj], 'iblss2', '( t e. %s |-> %s ) e. L^1' % (K, IF_('i')))
    # sum over i, integrate the sum
    fs = st(w, A0, [a1(w, A0, 'ioombl', '%s e. dom vol' % K), pf, ifc, ibk], 'itgfsum',
            '( ( t e. %s |-> sum_ i e. P %s ) e. L^1 /\\ %s = sum_ i e. P %s )' % (K, IF_('i'), ITG(K, 'sum_ i e. P %s' % IF_('i')), ITG(K, IF_('i'))))
    fs1 = st(w, A0, [fs], 'simpld', '( t e. %s |-> sum_ i e. P %s ) e. L^1' % (K, IF_('i')))
    fs2 = st(w, A0, [fs], 'simprd', '%s = sum_ i e. P %s' % (ITG(K, 'sum_ i e. P %s' % IF_('i')), ITG(K, IF_('i'))))
    se = st(w, A0, [e12], 'sumeq2dv', 'sum_ i e. P %s = sum_ i e. P %s' % (ITG(JIv('i'), 'X'), ITG(K, IF_('i'))))
    # pointwise bound
    Ak = '( ph /\\ t e. %s )' % K
    Lk = lambda s_: lift(w, s_, Ak)
    xk2 = xrk
    x0k = w.s([w.inst('elioore'), 'n'], 'sylan2', '( ( ph /\\ t e. %s ) -> 0 <_ X )' % K)
    pt = ap(w, Ak, 'lsdisjpt', [J(w, Ak, Lk('p'), Lk('s'), J(w, Ak, xk2, x0k))], 'sum_ i e. P %s <_ X' % IF_('i'))
    Akti = '( %s /\\ i e. P )' % Ak
    xk3 = lift(w, xk2, Akti)
    sr = st(w, Ak, [Lk(pf), st(w, Akti, [xk3, a1(w, Akti, '0re', '0 e. RR')], 'ifcld', '%s e. RR' % IF_('i'))], 'fsumrecl', 'sum_ i e. P %s e. RR' % IF_('i'))
    ibx = w.s([klr, khr, 'c'], 'lsibl', '( ph -> ( t e. %s |-> X ) e. L^1 )' % K)
    il = st(w, A0, [fs1, ibx, sr, xk2, pt], 'itgle', '%s <_ %s' % (ITG(K, 'sum_ i e. P %s' % IF_('i')), ITG(K, 'X')))
    fin = st(w, A0, [eqt(w, A0, se, eqc(w, A0, fs2)), il], 'eqbrtrd', STATEMENTS['lsdisj'].split(' -> ', 1)[1][:-2])
    qedlast(w); go(w)

    # ---- lsamgm
    A0 = '( ( X e. RR /\\ Y e. RR ) /\\ T e. RR+ )'
    w = W('lsamgm', 'AM-GM with a weight: 2 X Y <_ T X ^ 2 + Y ^ 2 / T for T > 0 (LargeSieve points_large_sieve, hAMGM).')
    P = parts(w, A0)
    c = ctx(w, A0, {'X': ('RR', P['X e. RR']), 'Y': ('RR', P['Y e. RR']), 'T': ('RR+', P['T e. RR+'])})
    TX = '( T x. X )'; P_ = '( %s ^ 2 )' % TX; R_ = '( 2 x. ( %s x. Y ) )' % TX; S_ = '( Y ^ 2 )'
    NUM = '( %s + %s )' % (P_, S_)
    sq = ap(w, A0, 'sqge0', [c.mem('( %s - Y )' % TX, 'RR')], '0 <_ ( ( %s - Y ) ^ 2 )' % TX)
    bn = ap(w, A0, 'binom2sub', [c.mem(TX, 'CC'), c.mem('Y', 'CC')], '( ( %s - Y ) ^ 2 ) = ( ( %s - %s ) + %s )' % (TX, P_, R_, S_))
    as_ = eqc(w, A0, st(w, A0, [c.mem(P_, 'CC'), c.mem(S_, 'CC'), c.mem(R_, 'CC')], 'addsubd', '( %s - %s ) = ( ( %s - %s ) + %s )' % (NUM, R_, P_, R_, S_)))
    z0 = st(w, A0, [sq, eqt(w, A0, bn, as_)], 'breqtrd', '0 <_ ( %s - %s )' % (NUM, R_))
    rle = st(w, A0, [z0, st(w, A0, [c.mem(NUM, 'RR'), c.mem(R_, 'RR')], 'subge0d', '( 0 <_ ( %s - %s ) <-> %s <_ %s )' % (NUM, R_, R_, NUM))], 'mpbid', '%s <_ %s' % (R_, NUM))
    L2 = '( ( 2 x. X ) x. Y )'
    tc = c.mem('T', 'CC'); xc = c.mem('X', 'CC'); ycc = c.mem('Y', 'CC'); tn = c.ne0('T')
    m1 = st(w, A0, [st(w, A0, [w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), xc, ycc], 'mulassd', '%s = ( 2 x. ( X x. Y ) )' % L2)], 'oveq2d', '( T x. %s ) = ( T x. ( 2 x. ( X x. Y ) ) )' % L2)
    m2 = st(w, A0, [tc, w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), c.mem('( X x. Y )', 'CC')], 'mul12d', '( T x. ( 2 x. ( X x. Y ) ) ) = ( 2 x. ( T x. ( X x. Y ) ) )')
    m3 = st(w, A0, [eqc(w, A0, st(w, A0, [tc, xc, ycc], 'mulassd', '( %s x. Y ) = ( T x. ( X x. Y ) )' % TX))], 'oveq2d', '( 2 x. ( T x. ( X x. Y ) ) ) = %s' % R_)
    lhs = eqt(w, A0, eqt(w, A0, m1, m2), m3)
    h = st(w, A0, [lhs, rle], 'eqbrtrd', '( T x. %s ) <_ %s' % (L2, NUM))
    q = st(w, A0, [h, st(w, A0, [c.mem(L2, 'RR'), c.mem(NUM, 'RR'), P['T e. RR+']], 'lemuldiv2d', '( ( T x. %s ) <_ %s <-> %s <_ ( %s / T ) )' % (L2, NUM, L2, NUM))], 'mpbid',
           '%s <_ ( %s / T )' % (L2, NUM))
    x2c = c.mem('( X ^ 2 )', 'CC'); yc = c.mem(S_, 'CC')
    r1 = st(w, A0, [c.mem(P_, 'CC'), yc, tc, tn], 'divdird', '( %s / T ) = ( ( %s / T ) + ( %s / T ) )' % (NUM, P_, S_))
    p1 = eqt(w, A0, st(w, A0, [tc, xc], 'sqmuld', '%s = ( ( T ^ 2 ) x. ( X ^ 2 ) )' % P_),
             st(w, A0, [st(w, A0, [tc], 'sqvald', '( T ^ 2 ) = ( T x. T )')], 'oveq1d', '( ( T ^ 2 ) x. ( X ^ 2 ) ) = ( ( T x. T ) x. ( X ^ 2 ) )'))
    p2 = eqt(w, A0, p1, st(w, A0, [tc, tc, x2c], 'mulassd', '( ( T x. T ) x. ( X ^ 2 ) ) = ( T x. ( T x. ( X ^ 2 ) ) )'))
    r2 = eqt(w, A0, st(w, A0, [p2], 'oveq1d', '( %s / T ) = ( ( T x. ( T x. ( X ^ 2 ) ) ) / T )' % P_),
             st(w, A0, [c.mem('( T x. ( X ^ 2 ) )', 'CC'), tc, tn], 'divcan3d', '( ( T x. ( T x. ( X ^ 2 ) ) ) / T ) = ( T x. ( X ^ 2 ) )'))
    r3 = st(w, A0, [yc, tc, tn], 'divrec2d', '( ( Y ^ 2 ) / T ) = ( ( 1 / T ) x. ( Y ^ 2 ) )')
    r = eqt(w, A0, r1, st(w, A0, [r2, r3], 'oveq12d', '( ( %s / T ) + ( ( Y ^ 2 ) / T ) ) = ( ( T x. ( X ^ 2 ) ) + ( ( 1 / T ) x. ( Y ^ 2 ) ) )' % P_))
    w.qed([q, r], 'breqtrd', STATEMENTS['lsamgm']); go(w)


def integ(w, A0, los, his, lo, hi, X, cnst, xrR, v='t'):
    """(L^1 step, real step, pointwise-real step on the interval) for S. ( lo (,) hi ) X _d v"""
    O = IOO(lo, hi)
    ib = w.s([los, his, cnst], 'lsibl', '( %s -> ( %s e. %s |-> %s ) e. L^1 )' % (A0, v, O, X))
    xo = w.s([w.inst('elioore'), xrR], 'sylan2', '( ( %s /\\ %s e. %s ) -> %s e. RR )' % (A0, v, O, X))
    return ib, st(w, A0, [xo, ib], 'itgrecl', '%s e. RR' % ITG(O, X, v)), xo


class HFC:
    """the facts about F, G under an antecedent containing HF"""
    def __init__(self, w, A0, P):
        self.w = w; self.A0 = A0
        ff, dfg, gcn = P['F : RR --> CC'], P['( RR _D F ) = G'], P['G e. %s' % CNR]
        gf = ap(w, A0, 'cncff', [gcn], 'G : RR --> CC')
        dm = eqt(w, A0, st(w, A0, [dfg], 'dmeqd', 'dom ( RR _D F ) = dom G'), ap(w, A0, 'fdm', [gf], 'dom G = RR'))
        j3 = J(w, A0, a1(w, A0, 'ax-resscn', 'RR C_ CC'), ff, a1(w, A0, 'ssid', 'RR C_ RR'))
        fcn = ap(w, A0, 'dvcn', [J(w, A0, j3, dm)], 'F e. %s' % CNR)
        self.ff, self.gf, self.fcn, self.gcn = ff, gf, fcn, gcn
        self.fm = fmap(w, A0, fcn, 'F', 't'); self.gm = fmap(w, A0, gcn, 'G', 't')
        At = '( %s /\\ t e. RR )' % A0; self.At = At
        tr = w.s([], 'simpr', '( %s -> t e. RR )' % At)
        self.ft = st(w, At, [lift(w, ff, At), tr], 'ffvelcdmd', '( F ` t ) e. CC')
        self.gt = st(w, At, [lift(w, gf, At), tr], 'ffvelcdmd', '( G ` t ) e. CC')
        self.c = ctx(w, At, {'( F ` t )': ('CC', self.ft), '( G ` t )': ('CC', self.gt)})
        self.fa2cn = cnsq(w, A0, self.fm, '( F ` t )', 't', self.ft)
        self.ga2cn = cnsq(w, A0, self.gm, '( G ` t )', 't', self.gt)
        self.fgcn = cnfg(w, A0, self.fm, self.gm, 't')
        self.fa2r = self.c.mem(FA2('F', 't'), 'RR'); self.ga2r = self.c.mem(FA2('G', 't'), 'RR'); self.fgr = self.c.mem(FG2('t'), 'RR')
        self.fa20 = self.c.ge0(FA2('F', 't')); self.fg0 = self.c.ge0(FG2('t'))


if __name__ == '__main__':
    # ---- lsptslem1: sum over the points of the Sobolev bounds, then the disjoint-interval summation
    A0 = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (HF, PTS, SEP, RNG)
    w = W('lsptslem1', 'The Sobolev bounds at D-separated points summed: sum_i | F ( Y_i ) | ^ 2 <_ 1 / D int_K | F | ^ 2 + int_K 2 | F | | G | (LargeSieve points_large_sieve, hsob, hsum1, hsum2).')
    P = parts(w, A0)
    H = HFC(w, A0, P)
    pf, yf, drp = P['P e. Fin'], P['Y : P --> RR'], P['D e. RR+']
    pts = P[PTS]; sep = P[SEP]; rng = P[RNG]
    K = KP(); kl = '-u ( D / 2 )'; kh = '( -u ( D / 2 ) + 1 )'
    c0 = ctx(w, A0, {'D': ('RR+', drp)})
    klr = c0.mem(kl, 'RR'); khr = c0.mem(kh, 'RR')
    Ai = '( %s /\\ i e. P )' % A0
    Li = lambda s_: lift(w, s_, Ai)
    ip = w.s([], 'simpr', '( %s -> i e. P )' % Ai)
    yi = st(w, Ai, [Li(yf), ip], 'ffvelcdmd', '%s e. RR' % YI('i'))
    JJ = JIv('i')
    sob = ap(w, Ai, 'lssob', [J(w, Ai, Li(P[HF]), J(w, Ai, Li(drp), yi))], '%s <_ ( ( ( 1 / D ) x. %s ) + %s )' % (FA2('F', YI('i')), ITG(JJ, FA2('F', 't')), ITG(JJ, FG2('t'))))
    ci = ctx(w, Ai, {'D': ('RR+', Li(drp)), YI('i'): ('RR', yi)})
    lo = '( %s - ( D / 2 ) )' % YI('i'); hi = '( %s + ( D / 2 ) )' % YI('i')
    lor = ci.mem(lo, 'RR'); hir = ci.mem(hi, 'RR')
    xrA = lift(w, H.fa2r, '( %s /\\ t e. RR )' % Ai) if False else w.s([H.fa2r], 'adantlr', '( ( %s /\\ t e. RR ) -> %s e. RR )' % (Ai, FA2('F', 't')))
    xrG = w.s([H.fgr], 'adantlr', '( ( %s /\\ t e. RR ) -> %s e. RR )' % (Ai, FG2('t')))
    _, i1r, _ = integ(w, Ai, lor, hir, lo, hi, FA2('F', 't'), Li(H.fa2cn), xrA)
    _, i2r, _ = integ(w, Ai, lor, hir, lo, hi, FG2('t'), Li(H.fgcn), xrG)
    fyi = st(w, Ai, [Li(P['F : RR --> CC']), yi], 'ffvelcdmd', '( F ` %s ) e. CC' % YI('i'))
    lhr = st(w, Ai, [st(w, Ai, [fyi], 'abscld', '( abs ` ( F ` %s ) ) e. RR' % YI('i'))], 'resqcld', '%s e. RR' % FA2('F', YI('i')))
    dinv = ci.mem('( 1 / D )', 'RR')
    t1r = st(w, Ai, [dinv, i1r], 'remulcld', '( ( 1 / D ) x. %s ) e. RR' % ITG(JJ, FA2('F', 't')))
    rhr = st(w, Ai, [t1r, i2r], 'readdcld', '( ( ( 1 / D ) x. %s ) + %s ) e. RR' % (ITG(JJ, FA2('F', 't')), ITG(JJ, FG2('t'))))
    S1 = 'sum_ i e. P %s' % FA2('F', YI('i'))
    S2 = 'sum_ i e. P ( ( ( 1 / D ) x. %s ) + %s )' % (ITG(JJ, FA2('F', 't')), ITG(JJ, FG2('t')))
    le1 = st(w, A0, [pf, lhr, rhr, sob], 'fsumle', '%s <_ %s' % (S1, S2))
    SA = 'sum_ i e. P %s' % ITG(JJ, FA2('F', 't')); SB = 'sum_ i e. P %s' % ITG(JJ, FG2('t'))
    t1c = st(w, Ai, [t1r], 'recnd', '( ( 1 / D ) x. %s ) e. CC' % ITG(JJ, FA2('F', 't'))); i2c = st(w, Ai, [i2r], 'recnd', '%s e. CC' % ITG(JJ, FG2('t')))
    ad = st(w, A0, [pf, t1c, i2c], 'fsumadd', '%s = ( sum_ i e. P ( ( 1 / D ) x. %s ) + %s )' % (S2, ITG(JJ, FA2('F', 't')), SB))
    mc = st(w, A0, [pf, c0.mem('( 1 / D )', 'CC'), st(w, Ai, [i1r], 'recnd', '%s e. CC' % ITG(JJ, FA2('F', 't')))], 'fsummulc2',
            '( ( 1 / D ) x. %s ) = sum_ i e. P ( ( 1 / D ) x. %s )' % (SA, ITG(JJ, FA2('F', 't'))))
    ad2 = eqt(w, A0, ad, st(w, A0, [eqc(w, A0, mc)], 'oveq1d', '( sum_ i e. P ( ( 1 / D ) x. %s ) + %s ) = ( ( ( 1 / D ) x. %s ) + %s )' % (ITG(JJ, FA2('F', 't')), SB, SA, SB)))
    # the disjoint-interval summation, twice
    At0 = '( %s /\\ t e. RR )' % A0
    dj1 = w.s([pts, sep, rng, H.fa2cn, H.fa2r, H.fa20], 'lsdisj', '( %s -> %s <_ %s )' % (A0, SA, ITG(K, FA2('F', 't'))))
    dj2 = w.s([pts, sep, rng, H.fgcn, H.fgr, H.fg0], 'lsdisj', '( %s -> %s <_ %s )' % (A0, SB, ITG(K, FG2('t'))))
    _, kFr, _ = integ(w, A0, klr, khr, kl, kh, FA2('F', 't'), H.fa2cn, H.fa2r)
    _, kGr, _ = integ(w, A0, klr, khr, kl, kh, FG2('t'), H.fgcn, H.fgr)
    sar = st(w, A0, [pf, i1r], 'fsumrecl', '%s e. RR' % SA); sbr = st(w, A0, [pf, i2r], 'fsumrecl', '%s e. RR' % SB)
    dr0 = c0.mem('( 1 / D )', 'RR'); dg0 = c0.ge0('( 1 / D )')
    m1 = st(w, A0, [sar, kFr, dr0, dg0, dj1], 'lemul2ad', '( ( 1 / D ) x. %s ) <_ ( ( 1 / D ) x. %s )' % (SA, ITG(K, FA2('F', 't'))))
    lv = {S1: st(w, A0, [pf, lhr], 'fsumrecl', '%s e. RR' % S1), S2: st(w, A0, [pf, rhr], 'fsumrecl', '%s e. RR' % S2),
          '( ( 1 / D ) x. %s )' % SA: st(w, A0, [dr0, sar], 'remulcld', '( ( 1 / D ) x. %s ) e. RR' % SA),
          '( ( 1 / D ) x. %s )' % ITG(K, FA2('F', 't')): st(w, A0, [dr0, kFr], 'remulcld', '( ( 1 / D ) x. %s ) e. RR' % ITG(K, FA2('F', 't'))),
          SB: sbr, ITG(K, FG2('t')): kGr}
    X1 = '( ( 1 / D ) x. %s )' % SA; X2 = '( ( 1 / D ) x. %s )' % ITG(K, FA2('F', 't'))
    x = st(w, A0, [lv[X1], sbr, lv[X2], kGr, m1, dj2], 'le2addd', '( %s + %s ) <_ ( %s + %s )' % (X1, SB, X2, ITG(K, FG2('t'))))
    y = st(w, A0, [le1, ad2], 'breqtrd', '%s <_ ( %s + %s )' % (S1, X1, SB))
    w.qed([lv[S1], st(w, A0, [lv[X1], sbr], 'readdcld', '( %s + %s ) e. RR' % (X1, SB)), st(w, A0, [lv[X2], kGr], 'readdcld', '( %s + %s ) e. RR' % (X2, ITG(K, FG2('t')))), y, x],
          'letrd', STATEMENTS['lsptslem1'])
    go(w)

    # ---- lsptslem2: AM-GM under the integral
    A0 = '( %s /\\ ( D e. RR+ /\\ T e. RR+ ) )' % HF
    w = W('lsptslem2', 'AM-GM under the integral: int_K 2 | F | | G | <_ T int_K | F | ^ 2 + 1 / T int_K | G | ^ 2 (LargeSieve points_large_sieve, hAMGM).')
    P = parts(w, A0)
    H = HFC(w, A0, P)
    drp, trp = P['D e. RR+'], P['T e. RR+']
    K = KP(); kl = '-u ( D / 2 )'; kh = '( -u ( D / 2 ) + 1 )'
    c0 = ctx(w, A0, {'D': ('RR+', drp), 'T': ('RR+', trp)})
    klr = c0.mem(kl, 'RR'); khr = c0.mem(kh, 'RR')
    At = H.At
    tc = ctx(w, At, {'( F ` t )': ('CC', H.ft), '( G ` t )': ('CC', H.gt), 'T': ('RR+', lift(w, trp, At))})
    aF = '( abs ` ( F ` t ) )'; aG = '( abs ` ( G ` t ) )'
    RHS = '( ( T x. %s ) + ( ( 1 / T ) x. %s ) )' % (FA2('F', 't'), FA2('G', 't'))
    am = ap(w, At, 'lsamgm', [J(w, At, J(w, At, tc.mem(aF, 'RR'), tc.mem(aG, 'RR')), lift(w, trp, At))], '%s <_ %s' % (FG2('t'), RHS))
    tcc = c0.mem('T', 'CC'); ticc = c0.mem('( 1 / T )', 'CC')
    cT = cnconst(w, A0, tcc, 'T', 't'); cTi = cnconst(w, A0, ticc, '( 1 / T )', 't')
    m1 = cnmul(w, A0, cT, 'T', H.fa2cn, FA2('F', 't'), 't'); m2 = cnmul(w, A0, cTi, '( 1 / T )', H.ga2cn, FA2('G', 't'), 't')
    rcn = cnadd(w, A0, m1, '( T x. %s )' % FA2('F', 't'), m2, '( ( 1 / T ) x. %s )' % FA2('G', 't'), 't')
    ibfg, fgr, xfg = integ(w, A0, klr, khr, kl, kh, FG2('t'), H.fgcn, H.fgr)
    ibr, rr_, xr_ = integ(w, A0, klr, khr, kl, kh, RHS, rcn, tc.mem(RHS, 'RR'))
    AtK = '( %s /\\ t e. %s )' % (A0, K)
    amK = w.s([w.inst('elioore'), am], 'sylan2', '( %s -> %s <_ %s )' % (AtK, FG2('t'), RHS))
    il = st(w, A0, [ibfg, ibr, xfg, xr_, amK], 'itgle', '%s <_ %s' % (ITG(K, FG2('t')), ITG(K, RHS)))
    ib1, _, x1 = integ(w, A0, klr, khr, kl, kh, '( T x. %s )' % FA2('F', 't'), m1, tc.mem('( T x. %s )' % FA2('F', 't'), 'RR'))
    ib2, _, x2 = integ(w, A0, klr, khr, kl, kh, '( ( 1 / T ) x. %s )' % FA2('G', 't'), m2, tc.mem('( ( 1 / T ) x. %s )' % FA2('G', 't'), 'RR'))
    x1c = st(w, AtK, [x1], 'recnd', '( T x. %s ) e. CC' % FA2('F', 't')); x2c = st(w, AtK, [x2], 'recnd', '( ( 1 / T ) x. %s ) e. CC' % FA2('G', 't'))
    ia = st(w, A0, [x1c, ib1, x2c, ib2], 'itgadd', '%s = ( %s + %s )' % (ITG(K, RHS), ITG(K, '( T x. %s )' % FA2('F', 't')), ITG(K, '( ( 1 / T ) x. %s )' % FA2('G', 't'))))
    ibF, _, xF = integ(w, A0, klr, khr, kl, kh, FA2('F', 't'), H.fa2cn, H.fa2r)
    ibG, _, xG = integ(w, A0, klr, khr, kl, kh, FA2('G', 't'), H.ga2cn, H.ga2r)
    xFc = st(w, AtK, [xF], 'recnd', '%s e. CC' % FA2('F', 't')); xGc = st(w, AtK, [xG], 'recnd', '%s e. CC' % FA2('G', 't'))
    mc1 = st(w, A0, [tcc, xFc, ibF], 'itgmulc2', '( T x. %s ) = %s' % (ITG(K, FA2('F', 't')), ITG(K, '( T x. %s )' % FA2('F', 't'))))
    mc2 = st(w, A0, [ticc, xGc, ibG], 'itgmulc2', '( ( 1 / T ) x. %s ) = %s' % (ITG(K, FA2('G', 't')), ITG(K, '( ( 1 / T ) x. %s )' % FA2('G', 't'))))
    ia2 = eqt(w, A0, ia, st(w, A0, [eqc(w, A0, mc1), eqc(w, A0, mc2)], 'oveq12d', '( %s + %s ) = ( ( T x. %s ) + ( ( 1 / T ) x. %s ) )' % (
        ITG(K, '( T x. %s )' % FA2('F', 't')), ITG(K, '( ( 1 / T ) x. %s )' % FA2('G', 't')), ITG(K, FA2('F', 't')), ITG(K, FA2('G', 't')))))
    w.qed([il, ia2], 'breqtrd', STATEMENTS['lsptslem2']); go(w)

    # ---- lsptsg: the Gallagher inequality at separated points for a differentiable F
    A0 = '( %s /\\ %s /\\ ( %s /\\ %s /\\ T e. RR+ ) )' % (HF, PTS, SEP, RNG)
    w = W('lsptsg', 'Gallagher inequality at D-separated points: sum_i | F ( Y_i ) | ^ 2 <_ ( 1 / D + T ) int_K | F | ^ 2 + 1 / T int_K | G | ^ 2 for G the derivative of F (LargeSieve points_large_sieve).')
    P = parts(w, A0)
    H = HFC(w, A0, P)
    drp, trp = P['D e. RR+'], P['T e. RR+']
    c0 = ctx(w, A0, {'D': ('RR+', drp), 'T': ('RR+', trp)})
    K = KP(); kl = '-u ( D / 2 )'; kh = '( -u ( D / 2 ) + 1 )'
    klr = c0.mem(kl, 'RR'); khr = c0.mem(kh, 'RR')
    l1 = ap(w, A0, 'lsptslem1', [J(w, A0, P[HF], P[PTS], J(w, A0, P[SEP], P[RNG]))], concl('lsptslem1'))
    l2 = ap(w, A0, 'lsptslem2', [J(w, A0, P[HF], J(w, A0, drp, trp))], concl('lsptslem2'))
    _, kF, _ = integ(w, A0, klr, khr, kl, kh, FA2('F', 't'), H.fa2cn, H.fa2r)
    _, kG, _ = integ(w, A0, klr, khr, kl, kh, FA2('G', 't'), H.ga2cn, H.ga2r)
    _, kFG, _ = integ(w, A0, klr, khr, kl, kh, FG2('t'), H.fgcn, H.fgr)
    IF = ITG(K, FA2('F', 't')); IG = ITG(K, FA2('G', 't'))
    dd = st(w, A0, [c0.mem('( 1 / D )', 'CC'), c0.mem('T', 'CC'), st(w, A0, [kF], 'recnd', '%s e. CC' % IF)], 'adddird',
            '( ( ( 1 / D ) + T ) x. %s ) = ( ( ( 1 / D ) x. %s ) + ( T x. %s ) )' % (IF, IF, IF))
    S1 = 'sum_ i e. P %s' % FA2('F', YI('i'))
    Ai = '( %s /\\ i e. P )' % A0
    fyi = st(w, Ai, [lift(w, P['F : RR --> CC'], Ai), st(w, Ai, [lift(w, P['Y : P --> RR'], Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai)], 'ffvelcdmd', '%s e. RR' % YI('i'))],
             'ffvelcdmd', '( F ` %s ) e. CC' % YI('i'))
    s1r = st(w, A0, [P['P e. Fin'], st(w, Ai, [st(w, Ai, [fyi], 'abscld', '( abs ` ( F ` %s ) ) e. RR' % YI('i'))], 'resqcld', '%s e. RR' % FA2('F', YI('i')))], 'fsumrecl', '%s e. RR' % S1)
    lv = {S1: s1r, ITG(K, FG2('t')): kFG,
          '( ( 1 / D ) x. %s )' % IF: st(w, A0, [c0.mem('( 1 / D )', 'RR'), kF], 'remulcld', '( ( 1 / D ) x. %s ) e. RR' % IF),
          '( T x. %s )' % IF: st(w, A0, [c0.mem('T', 'RR'), kF], 'remulcld', '( T x. %s ) e. RR' % IF),
          '( ( 1 / T ) x. %s )' % IG: st(w, A0, [c0.mem('( 1 / T )', 'RR'), kG], 'remulcld', '( ( 1 / T ) x. %s ) e. RR' % IG),
          '( ( ( 1 / D ) + T ) x. %s )' % IF: st(w, A0, [c0.mem('( ( 1 / D ) + T )', 'RR'), kF], 'remulcld', '( ( ( 1 / D ) + T ) x. %s ) e. RR' % IF)}
    IFG = ITG(K, FG2('t'))
    Y1 = '( ( 1 / D ) x. %s )' % IF; Y2 = '( T x. %s )' % IF; Y3 = '( ( 1 / T ) x. %s )' % IG; Y4 = '( ( ( 1 / D ) + T ) x. %s )' % IF
    x1 = st(w, A0, [l2, st(w, A0, [kFG, st(w, A0, [lv[Y2], lv[Y3]], 'readdcld', '( %s + %s ) e. RR' % (Y2, Y3)), lv[Y1]], 'leadd2d',
                            '( %s <_ ( %s + %s ) <-> ( %s + %s ) <_ ( %s + ( %s + %s ) ) )' % (IFG, Y2, Y3, Y1, IFG, Y1, Y2, Y3))], 'mpbid',
            '( %s + %s ) <_ ( %s + ( %s + %s ) )' % (Y1, IFG, Y1, Y2, Y3))
    x2 = eqt(w, A0, eqc(w, A0, st(w, A0, [c0.mem(Y1, 'CC') if False else st(w, A0, [lv[Y1]], 'recnd', '%s e. CC' % Y1), st(w, A0, [lv[Y2]], 'recnd', '%s e. CC' % Y2), st(w, A0, [lv[Y3]], 'recnd', '%s e. CC' % Y3)],
                                  'addassd', '( ( %s + %s ) + %s ) = ( %s + ( %s + %s ) )' % (Y1, Y2, Y3, Y1, Y2, Y3))),
             st(w, A0, [eqc(w, A0, dd)], 'oveq1d', '( ( %s + %s ) + %s ) = ( %s + %s )' % (Y1, Y2, Y3, Y4, Y3)))
    x3 = st(w, A0, [x1, x2], 'breqtrd', '( %s + %s ) <_ ( %s + %s )' % (Y1, IFG, Y4, Y3))
    w.qed([s1r, st(w, A0, [lv[Y1], kFG], 'readdcld', '( %s + %s ) e. RR' % (Y1, IFG)), st(w, A0, [lv[Y4], lv[Y3]], 'readdcld', '( %s + %s ) e. RR' % (Y4, Y3)), l1, x3],
          'letrd', STATEMENTS['lsptsg'])
    go(w)

    # ---- lsdwbnd: the derivative weights are at most 2 pi E times the weights
    A0 = '( %s /\\ ( E e. RR /\\ %s ) )' % (HWM, FRQ)
    w = W('lsdwbnd', 'The squared derivative weights of a trigonometric polynomial with frequencies within E of M sum to at most 4 pi ^ 2 E ^ 2 times the squared weights (LargeSieve points_large_sieve, hpars\').')
    P = parts(w, A0)
    hw = P[HW]; mz = P['M e. ZZ']; er = P['E e. RR']; frq = P[FRQ]
    wf = st(w, A0, [hw], 'simp1d', 'W e. Fin')
    An = '( %s /\\ n e. W )' % A0
    Ln = lambda s_: lift(w, s_, An)
    nmem = w.s([], 'simpr', '( %s -> n e. W )' % An)
    from z4alib import win
    nz, an = win(w, An, Ln(hw), nmem)
    nm = st(w, An, [nz, Ln(mz)], 'zsubcld', '( n - M ) e. ZZ'); nmr = st(w, An, [nm], 'zred', '( n - M ) e. RR'); nmc = st(w, An, [nm], 'zcnd', '( n - M ) e. CC')
    fq, _ = w.wcongr('( abs ` ( m - M ) ) <_ E', {'m': 'n'}, 'm = n', {'m': w.s([], 'id', '( m = n -> m = n )')})
    fqn = st(w, An, [fq, Ln(frq), nmem], 'rspcdva', '( abs ` ( n - M ) ) <_ E')
    c2 = lift(w, c2cl(w, A0), An)
    KN = '( %s x. ( n - M ) )' % C2
    knc = st(w, An, [c2, nmc], 'mulcld', '%s e. CC' % KN)
    WN = '( ( A ` n ) x. %s )' % KN
    fv = fvmd(w, An, 'j', 'W', '( ( A ` j ) x. ( %s x. ( j - M ) ) )' % C2, 'n', nmem, st(w, An, [an, knc], 'mulcld', '%s e. CC' % WN))
    e1 = st(w, An, [st(w, An, [fv], 'fveq2d', '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (AD, WN))], 'oveq1d', '%s = ( ( abs ` %s ) ^ 2 )' % (ABS2('( %s ` n )' % AD), WN))
    aA = '( abs ` ( A ` n ) )'; aK = '( abs ` %s )' % KN
    e2 = st(w, An, [st(w, An, [an, knc], 'absmuld', '( abs ` %s ) = ( %s x. %s )' % (WN, aA, aK))], 'oveq1d', '( ( abs ` %s ) ^ 2 ) = ( ( %s x. %s ) ^ 2 )' % (WN, aA, aK))
    aAc = st(w, An, [st(w, An, [an], 'abscld', '%s e. RR' % aA)], 'recnd', '%s e. CC' % aA)
    aKr = st(w, An, [knc], 'abscld', '%s e. RR' % aK)
    e3 = st(w, An, [aAc, st(w, An, [aKr], 'recnd', '%s e. CC' % aK)], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (aA, aK, aA, aK))
    lhs = eqt(w, An, eqt(w, An, e1, e2), e3)
    # | 2 pi i ( n - M ) | = 2 pi | n - M |
    TP = '( 2 x. _pi )'
    ic = a1(w, An, 'ax-icn', '_i e. CC'); pc = a1(w, An, 'picn', '_pi e. CC'); twoc = w.s([], '2cnd', '( %s -> 2 e. CC )' % An)
    ipc = st(w, An, [ic, pc], 'mulcld', '( _i x. _pi ) e. CC')
    g1 = st(w, An, [c2, nmc], 'absmuld', '%s = ( ( abs ` %s ) x. ( abs ` ( n - M ) ) )' % (aK, C2))
    g2 = st(w, An, [twoc, ipc], 'absmuld', '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % C2)
    g3 = st(w, An, [ic, pc], 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )')
    pr = a1(w, An, 'pire', '_pi e. RR'); p0 = st(w, An, [a1(w, An, 'pipos', '0 < _pi')], 'ltled', '0 <_ _pi') if False else None
    p0 = st(w, An, [pr, a1(w, An, 'pipos', '0 < _pi')], 'ltled', '0 <_ _pi')
    g4 = st(w, An, [a1(w, An, 'absi', '( abs ` _i ) = 1'), ap(w, An, 'absid', [pr, p0], '( abs ` _pi ) = _pi')], 'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')
    g5 = st(w, An, [pc], 'mullidd', '( 1 x. _pi ) = _pi')
    tr_ = a1(w, An, '2re', '2 e. RR'); t0 = st(w, An, [tr_, a1(w, An, '2pos', '0 < 2')], 'ltled', '0 <_ 2')
    g6 = st(w, An, [ap(w, An, 'absid', [tr_, t0], '( abs ` 2 ) = 2'), eqt(w, An, eqt(w, An, g3, g4), g5)], 'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = %s' % TP)
    ac2 = eqt(w, An, g2, g6)
    kabs = eqt(w, An, g1, st(w, An, [ac2], 'oveq1d', '( ( abs ` %s ) x. ( abs ` ( n - M ) ) ) = ( %s x. ( abs ` ( n - M ) ) )' % (C2, TP)))
    tpr = st(w, An, [tr_, pr], 'remulcld', '%s e. RR' % TP)
    tp0 = st(w, An, [tr_, pr, t0, p0], 'mulge0d', '0 <_ %s' % TP)
    anm = '( abs ` ( n - M ) )'
    anmr = st(w, An, [nmc], 'abscld', '%s e. RR' % anm)
    b1 = st(w, An, [anmr, Ln(er), tpr, tp0, fqn], 'lemul2ad', '( %s x. %s ) <_ ( %s x. E )' % (TP, anm, TP))
    b2 = st(w, An, [kabs, b1], 'eqbrtrd', '%s <_ ( %s x. E )' % (aK, TP))
    k0 = st(w, An, [knc], 'absge0d', '0 <_ %s' % aK)
    TE = '( %s x. E )' % TP
    ter = st(w, An, [tpr, Ln(er)], 'remulcld', '%s e. RR' % TE)
    b3 = ap(w, An, 'le2sq2', [J(w, An, J(w, An, aKr, k0), J(w, An, ter, b2))], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (aK, TE))
    K4 = '( ( 4 x. ( _pi ^ 2 ) ) x. ( E ^ 2 ) )'
    erc = st(w, An, [Ln(er)], 'recnd', 'E e. CC')
    s1 = st(w, An, [st(w, An, [twoc, pc], 'mulcld', '%s e. CC' % TP), erc], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( E ^ 2 ) )' % (TE, TP))
    s2 = eqt(w, An, st(w, An, [twoc, pc], 'sqmuld', '( %s ^ 2 ) = ( ( 2 ^ 2 ) x. ( _pi ^ 2 ) )' % TP),
             st(w, An, [a1(w, An, 'sq2', '( 2 ^ 2 ) = 4')], 'oveq1d', '( ( 2 ^ 2 ) x. ( _pi ^ 2 ) ) = ( 4 x. ( _pi ^ 2 ) )'))
    s3 = eqt(w, An, s1, st(w, An, [s2], 'oveq1d', '( ( %s ^ 2 ) x. ( E ^ 2 ) ) = %s' % (TP, K4)))
    b4 = st(w, An, [b3, s3], 'breqtrd', '( %s ^ 2 ) <_ %s' % (aK, K4))
    aA2r = st(w, An, [st(w, An, [an], 'abscld', '%s e. RR' % aA)], 'resqcld', '( %s ^ 2 ) e. RR' % aA)
    aA20 = st(w, An, [st(w, An, [an], 'abscld', '%s e. RR' % aA)], 'sqge0d', '0 <_ ( %s ^ 2 )' % aA)
    k4r = st(w, An, [st(w, An, [st(w, An, [a1(w, An, '4re', '4 e. RR'), st(w, An, [pr], 'resqcld', '( _pi ^ 2 ) e. RR')], 'remulcld', '( 4 x. ( _pi ^ 2 ) ) e. RR')], 'id', '( %s -> ( 4 x. ( _pi ^ 2 ) ) e. RR )' % An) if False else
                     st(w, An, [a1(w, An, '4re', '4 e. RR'), st(w, An, [pr], 'resqcld', '( _pi ^ 2 ) e. RR')], 'remulcld', '( 4 x. ( _pi ^ 2 ) ) e. RR'),
                     st(w, An, [Ln(er)], 'resqcld', '( E ^ 2 ) e. RR')], 'remulcld', '%s e. RR' % K4)
    b5 = st(w, An, [st(w, An, [aKr], 'resqcld', '( %s ^ 2 ) e. RR' % aK), k4r, aA2r, aA20, b4], 'lemul2ad', '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) <_ ( ( %s ^ 2 ) x. %s )' % (aA, aK, aA, K4))
    b6 = st(w, An, [st(w, An, [aA2r], 'recnd', '( %s ^ 2 ) e. CC' % aA), st(w, An, [k4r], 'recnd', '%s e. CC' % K4)], 'mulcomd', '( ( %s ^ 2 ) x. %s ) = ( %s x. ( %s ^ 2 ) )' % (aA, K4, K4, aA))
    pt = st(w, An, [st(w, An, [lhs, b5], 'eqbrtrd', '%s <_ ( ( %s ^ 2 ) x. %s )' % (ABS2('( %s ` n )' % AD), aA, K4)), b6], 'breqtrd', '%s <_ ( %s x. ( %s ^ 2 ) )' % (ABS2('( %s ` n )' % AD), K4, aA))
    adf = ap(w, A0, 'lsdw', [P[HWM]], '%s : W --> CC' % AD)
    adn = st(w, An, [Ln(adf), nmem], 'ffvelcdmd', '( %s ` n ) e. CC' % AD)
    lr = st(w, An, [st(w, An, [adn], 'abscld', '( abs ` ( %s ` n ) ) e. RR' % AD)], 'resqcld', '%s e. RR' % ABS2('( %s ` n )' % AD))
    rr2 = st(w, An, [k4r, aA2r], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (K4, aA))
    fl = st(w, A0, [wf, lr, rr2, pt], 'fsumle', '%s <_ sum_ n e. W ( %s x. ( %s ^ 2 ) )' % (SW(AD), K4, aA))
    k4c0 = lift(w, k4r, An)
    mc = st(w, A0, [wf, st(w, A0, [st(w, A0, [st(w, A0, [a1(w, A0, '4re', '4 e. RR'), st(w, A0, [a1(w, A0, 'pire', '_pi e. RR')], 'resqcld', '( _pi ^ 2 ) e. RR')], 'remulcld', '( 4 x. ( _pi ^ 2 ) ) e. RR'),
                                               st(w, A0, [er], 'resqcld', '( E ^ 2 ) e. RR')], 'remulcld', '%s e. RR' % K4)], 'recnd', '%s e. CC' % K4),
                    st(w, An, [aA2r], 'recnd', '( %s ^ 2 ) e. CC' % aA)], 'fsummulc2', '( %s x. %s ) = sum_ n e. W ( %s x. ( %s ^ 2 ) )' % (K4, SW('A'), K4, aA))
    w.qed([fl, mc], 'breqtrrd', STATEMENTS['lsdwbnd']); go(w)

    # ---- lspts: the additive large sieve over separated points
    A0 = '( %s /\\ %s /\\ ( %s /\\ %s /\\ ( E e. RR+ /\\ %s ) ) )' % (HWM, PTS, SEP, RNG, FRQ)
    w = W('lspts', 'Additive large sieve over D-separated points of [ 0 , 1 - D ]: sum_i | sum_n A ( n ) e ( ( n - M ) Y_i ) | ^ 2 <_ ( 1 / D + 4 pi E ) sum_n | A ( n ) | ^ 2 for frequencies within E of M (LargeSieve points_large_sieve).')
    P = parts(w, A0)
    hwm = P[HWM]; hw = P[HW]; mz = P['M e. ZZ']; erp = P['E e. RR+']; drp = P['D e. RR+']; frq = P[FRQ]
    FTA = FT('A', 'x'); FTD = FT(AD, 'x')
    HWD = '( W e. Fin /\\ W C_ ZZ /\\ %s : W --> CC )' % AD
    adf = ap(w, A0, 'lsdw', [hwm], '%s : W --> CC' % AD)
    hwd = J(w, A0, J(w, A0, st(w, A0, [hw], 'simp1d', 'W e. Fin'), st(w, A0, [hw], 'simp2d', 'W C_ ZZ'), adf), mz)
    dv = ap(w, A0, 'lstrigdv', [hwm], '( RR _D %s ) = %s' % (FTA, FTD))
    cnA = ap(w, A0, 'lstrigcn', [hwm], '%s e. %s' % (FTA, CNR))
    cnD = ap(w, A0, 'lstrigcn', [hwd], '%s e. %s' % (FTD, CNR))
    ffA = ap(w, A0, 'cncff', [cnA], '%s : RR --> CC' % FTA)
    TP = '( 2 x. _pi )'; T = '( %s x. E )' % TP
    c0 = ctx(w, A0, {'D': ('RR+', drp), 'E': ('RR+', erp)})
    trp = c0.mem(T, 'RR+')
    g = ap(w, A0, 'lsptsg', [J(w, A0, J(w, A0, ffA, dv, cnD), P[PTS], J(w, A0, P[SEP], P[RNG], trp))],
           'sum_ i e. P %s <_ ( ( ( ( 1 / D ) + %s ) x. %s ) + ( ( 1 / %s ) x. %s ) )' % (FA2(FTA, YI('i')), T, ITG(KP(), FA2(FTA, 't')), T, ITG(KP(), FA2(FTD, 't'))))
    # evaluations of the mappings
    def trigcl(Aname, fst, ante, tst, tv):
        """( ante -> TRIG(Aname, tv) e. CC ) given fst ( ante -> Aname : W --> CC ), tst ( ante -> tv e. RR )"""
        Atn = '( %s /\\ n e. W )' % ante
        nmem = w.s([], 'simpr', '( %s -> n e. W )' % Atn)
        nz = st(w, Atn, [lift(w, P['W C_ ZZ'], Atn), nmem], 'sseldd', 'n e. ZZ')
        an = st(w, Atn, [lift(w, fst, Atn), nmem], 'ffvelcdmd', '( %s ` n ) e. CC' % Aname)
        nmc = st(w, Atn, [st(w, Atn, [nz, lift(w, mz, Atn)], 'zsubcld', '( n - M ) e. ZZ')], 'zcnd', '( n - M ) e. CC')
        ec = ap(w, Atn, 'eatcl', [nmc, st(w, Atn, [lift(w, tst, Atn)], 'recnd', '%s e. CC' % tv)], '%s e. CC' % EAT('( n - M )', tv))
        return st(w, ante, [lift(w, st(w, A0, [hw], 'simp1d', 'W e. Fin'), ante), st(w, Atn, [an, ec], 'mulcld', '( ( %s ` n ) x. %s ) e. CC' % (Aname, EAT('( n - M )', tv)))],
                  'fsumcl', '%s e. CC' % TRIG(Aname, tv))
    # the points
    Ai = '( %s /\\ i e. P )' % A0
    yi = st(w, Ai, [lift(w, P['Y : P --> RR'], Ai), w.s([], 'simpr', '( %s -> i e. P )' % Ai)], 'ffvelcdmd', '%s e. RR' % YI('i'))
    fvi = fvmd(w, Ai, 'x', 'RR', TRIG('A', 'x'), YI('i'), yi, trigcl('A', lift(w, P['A : W --> CC'], Ai), Ai, yi, YI('i')))
    c1 = st(w, A0, [st(w, Ai, [st(w, Ai, [fvi], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (FTA, YI('i'), TRIG('A', YI('i'))))], 'oveq1d',
                           '%s = %s' % (FA2(FTA, YI('i')), ABS2(TRIG('A', YI('i')))))], 'sumeq2dv',
            'sum_ i e. P %s = sum_ i e. P %s' % (FA2(FTA, YI('i')), ABS2(TRIG('A', YI('i')))))
    # the two integrals are Parseval sums
    K = KP(); kl = '-u ( D / 2 )'
    klr = c0.mem(kl, 'RR')
    def parsv(Aname, hwmst, fst, FTX):
        AtK = '( %s /\\ t e. %s )' % (A0, K)
        tr = ioore(w, A0, kl, '( %s + 1 )' % kl)
        fv = fvmd(w, AtK, 'x', 'RR', TRIG(Aname, 'x'), 't', tr, trigcl(Aname, lift(w, fst, AtK), AtK, tr, 't'))
        e = st(w, AtK, [st(w, AtK, [fv], 'fveq2d', '( abs ` ( %s ` t ) ) = ( abs ` %s )' % (FTX, TRIG(Aname, 't')))], 'oveq1d', '%s = %s' % (FA2(FTX, 't'), ABS2(TRIG(Aname, 't'))))
        i1 = st(w, A0, [e], 'itgeq2dv', '%s = %s' % (ITG(K, FA2(FTX, 't')), ITG(K, ABS2(TRIG(Aname, 't')))))
        i2 = ap(w, A0, 'lsparper', [J(w, A0, hwmst, klr)], '%s = %s' % (ITG(K, ABS2(TRIG(Aname, 't'))), SW(Aname)))
        return eqt(w, A0, i1, i2)
    pA = parsv('A', hwm, P['A : W --> CC'], FTA)
    pD = parsv(AD, hwd, adf, FTD)
    bnd = ap(w, A0, 'lsdwbnd', [J(w, A0, hwm, J(w, A0, c0.mem('E', 'RR'), frq))], '%s <_ ( %s x. %s )' % (SW(AD), '( ( 4 x. ( _pi ^ 2 ) ) x. ( E ^ 2 ) )', SW('A')))
    K4 = '( ( 4 x. ( _pi ^ 2 ) ) x. ( E ^ 2 ) )'
    # SW closures
    def swr(Aname, fst):
        Anw = '( %s /\\ n e. W )' % A0
        an = st(w, Anw, [lift(w, fst, Anw), w.s([], 'simpr', '( %s -> n e. W )' % Anw)], 'ffvelcdmd', '( %s ` n ) e. CC' % Aname)
        return st(w, A0, [st(w, A0, [hw], 'simp1d', 'W e. Fin'), st(w, Anw, [st(w, Anw, [an], 'abscld', '( abs ` ( %s ` n ) ) e. RR' % Aname)], 'resqcld', '%s e. RR' % ABS2('( %s ` n )' % Aname))],
                  'fsumrecl', '%s e. RR' % SW(Aname))
    swA = swr('A', P['A : W --> CC']); swD = swr(AD, adf)
    c0.leaf(SW('A'), 'RR', swA); c0.leaf(SW(AD), 'RR', swD)
    # ( 1 / T ) x. SW(AD) <_ ( 1 / T ) x. ( K4 x. SW ) = T x. SW
    k4r = c0.mem(K4, 'RR')
    m1 = st(w, A0, [swD, st(w, A0, [k4r, swA], 'remulcld', '( %s x. %s ) e. RR' % (K4, SW('A'))), c0.mem('( 1 / %s )' % T, 'RR'), c0.ge0('( 1 / %s )' % T), bnd], 'lemul2ad',
            '( ( 1 / %s ) x. %s ) <_ ( ( 1 / %s ) x. ( %s x. %s ) )' % (T, SW(AD), T, K4, SW('A')))
    tc_ = c0.mem(T, 'CC'); tn = c0.ne0(T)
    q1 = st(w, A0, [c0.mem('( 1 / %s )' % T, 'CC'), c0.mem(K4, 'CC'), c0.mem(SW('A'), 'CC')], 'mulassd',
            '( ( ( 1 / %s ) x. %s ) x. %s ) = ( ( 1 / %s ) x. ( %s x. %s ) )' % (T, K4, SW('A'), T, K4, SW('A')))
    # ( 1 / T ) x. K4 = T
    tsq = eqt(w, A0, st(w, A0, [c0.mem(TP, 'CC'), c0.mem('E', 'CC')], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( E ^ 2 ) )' % (T, TP)),
              st(w, A0, [eqt(w, A0, st(w, A0, [w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), a1(w, A0, 'picn', '_pi e. CC')], 'sqmuld', '( %s ^ 2 ) = ( ( 2 ^ 2 ) x. ( _pi ^ 2 ) )' % TP),
                                 st(w, A0, [a1(w, A0, 'sq2', '( 2 ^ 2 ) = 4')], 'oveq1d', '( ( 2 ^ 2 ) x. ( _pi ^ 2 ) ) = ( 4 x. ( _pi ^ 2 ) )'))], 'oveq1d',
                 '( ( %s ^ 2 ) x. ( E ^ 2 ) ) = %s' % (TP, K4)))       # T ^ 2 = K4
    sqv = st(w, A0, [tc_], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (T, T, T))
    k4t = eqt(w, A0, eqc(w, A0, tsq), sqv)                              # K4 = T x. T
    r1 = st(w, A0, [k4t], 'oveq2d', '( ( 1 / %s ) x. %s ) = ( ( 1 / %s ) x. ( %s x. %s ) )' % (T, K4, T, T, T))
    r2 = eqc(w, A0, st(w, A0, [c0.mem('( 1 / %s )' % T, 'CC'), tc_, tc_], 'mulassd', '( ( ( 1 / %s ) x. %s ) x. %s ) = ( ( 1 / %s ) x. ( %s x. %s ) )' % (T, T, T, T, T, T)))
    r3 = st(w, A0, [st(w, A0, [tc_, tn], 'recid2d', '( ( 1 / %s ) x. %s ) = 1' % (T, T))], 'oveq1d', '( ( ( 1 / %s ) x. %s ) x. %s ) = ( 1 x. %s )' % (T, T, T, T))
    r4 = st(w, A0, [tc_], 'mullidd', '( 1 x. %s ) = %s' % (T, T))
    kt = eqt(w, A0, eqt(w, A0, eqt(w, A0, r1, r2), r3), r4)            # ( 1 / T ) x. K4 = T
    q2 = eqt(w, A0, eqc(w, A0, q1), st(w, A0, [kt], 'oveq1d', '( ( ( 1 / %s ) x. %s ) x. %s ) = ( %s x. %s )' % (T, K4, SW('A'), T, SW('A'))))
    # ( ( 1 / D ) + T ) + T = ( 1 / D ) + ( 4 pi ) E
    e1 = st(w, A0, [w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), a1(w, A0, 'picn', '_pi e. CC'), c0.mem('E', 'CC')], 'mulassd', '%s = ( 2 x. ( _pi x. E ) )' % T)
    e2 = st(w, A0, [a1(w, A0, '4cn', '4 e. CC'), a1(w, A0, 'picn', '_pi e. CC'), c0.mem('E', 'CC')], 'mulassd', '( ( 4 x. _pi ) x. E ) = ( 4 x. ( _pi x. E ) )')
    PE = '( _pi x. E )'
    c0.leaf(PE, 'RR', c0.mem(PE, 'RR')); c0.leaf(T, 'RR', c0.mem(T, 'RR')); c0.leaf('( ( 4 x. _pi ) x. E )', 'RR', c0.mem('( ( 4 x. _pi ) x. E )', 'RR'))
    tt1 = eqc(w, A0, st(w, A0, [tc_], '2timesd', '( 2 x. %s ) = ( %s + %s )' % (T, T, T)))
    tt2 = eqc(w, A0, st(w, A0, [w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), c0.mem(TP, 'CC'), c0.mem('E', 'CC')], 'mulassd', '( ( 2 x. %s ) x. E ) = ( 2 x. %s )' % (TP, T)))
    tt3 = eqt(w, A0, eqc(w, A0, st(w, A0, [w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), a1(w, A0, 'picn', '_pi e. CC')], 'mulassd',
                                  '( ( 2 x. 2 ) x. _pi ) = ( 2 x. %s )' % TP)), st(w, A0, [a1(w, A0, '2t2e4', '( 2 x. 2 ) = 4')], 'oveq1d', '( ( 2 x. 2 ) x. _pi ) = ( 4 x. _pi )'))
    tt4 = st(w, A0, [tt3], 'oveq1d', '( ( 2 x. %s ) x. E ) = ( ( 4 x. _pi ) x. E )' % TP)
    ttt = eqt(w, A0, eqt(w, A0, tt1, tt2), tt4)
    s = eqt(w, A0, st(w, A0, [c0.mem('( 1 / D )', 'CC'), tc_, tc_], 'addassd', '( ( ( 1 / D ) + %s ) + %s ) = ( ( 1 / D ) + ( %s + %s ) )' % (T, T, T, T)),
            st(w, A0, [ttt], 'oveq2d', '( ( 1 / D ) + ( %s + %s ) ) = ( ( 1 / D ) + ( ( 4 x. _pi ) x. E ) )' % (T, T)))
    ad = st(w, A0, [c0.mem('( ( 1 / D ) + %s )' % T, 'CC'), tc_, c0.mem(SW('A'), 'CC')], 'adddird',
            '( ( ( ( 1 / D ) + %s ) + %s ) x. %s ) = ( ( ( ( 1 / D ) + %s ) x. %s ) + ( %s x. %s ) )' % (T, T, SW('A'), T, SW('A'), T, SW('A')))
    fin_eq = eqt(w, A0, eqc(w, A0, ad), st(w, A0, [s], 'oveq1d', '( ( ( ( 1 / D ) + %s ) + %s ) x. %s ) = ( ( ( 1 / D ) + ( ( 4 x. _pi ) x. E ) ) x. %s )' % (T, T, SW('A'), SW('A'))))
    # assemble
    IA = ITG(K, FA2(FTA, 't')); ID = ITG(K, FA2(FTD, 't'))
    g2 = st(w, A0, [g, st(w, A0, [st(w, A0, [pA], 'oveq2d', '( ( ( 1 / D ) + %s ) x. %s ) = ( ( ( 1 / D ) + %s ) x. %s )' % (T, IA, T, SW('A'))),
                                  st(w, A0, [pD], 'oveq2d', '( ( 1 / %s ) x. %s ) = ( ( 1 / %s ) x. %s )' % (T, ID, T, SW(AD)))], 'oveq12d',
                             '( ( ( ( 1 / D ) + %s ) x. %s ) + ( ( 1 / %s ) x. %s ) ) = ( ( ( ( 1 / D ) + %s ) x. %s ) + ( ( 1 / %s ) x. %s ) )' % (T, IA, T, ID, T, SW('A'), T, SW(AD)))],
            'breqtrd', 'sum_ i e. P %s <_ ( ( ( ( 1 / D ) + %s ) x. %s ) + ( ( 1 / %s ) x. %s ) )' % (FA2(FTA, YI('i')), T, SW('A'), T, SW(AD)))
    g3 = st(w, A0, [eqc(w, A0, c1), g2], 'eqbrtrd', 'sum_ i e. P %s <_ ( ( ( ( 1 / D ) + %s ) x. %s ) + ( ( 1 / %s ) x. %s ) )' % (ABS2(TRIG('A', YI('i'))), T, SW('A'), T, SW(AD)))
    S0 = 'sum_ i e. P %s' % ABS2(TRIG('A', YI('i')))
    s0r = st(w, A0, [P['P e. Fin'], st(w, Ai, [st(w, Ai, [trigcl('A', lift(w, P['A : W --> CC'], Ai), Ai, yi, YI('i'))], 'abscld', '( abs ` %s ) e. RR' % TRIG('A', YI('i')))], 'resqcld',
                                             '%s e. RR' % ABS2(TRIG('A', YI('i'))))], 'fsumrecl', '%s e. RR' % S0)
    X1 = '( ( ( 1 / D ) + %s ) x. %s )' % (T, SW('A')); X2 = '( ( 1 / %s ) x. %s )' % (T, SW(AD)); X3 = '( ( 1 / %s ) x. ( %s x. %s ) )' % (T, K4, SW('A'))
    X4 = '( %s x. %s )' % (T, SW('A')); X5 = '( ( ( 1 / D ) + ( ( 4 x. _pi ) x. E ) ) x. %s )' % SW('A')
    lv = {S0: s0r}
    for X in (X1, X2, X3, X4, X5):
        lv[X] = c0.mem(X, 'RR')
    y1 = st(w, A0, [m1, st(w, A0, [lv[X2], lv[X3], lv[X1]], 'leadd2d', '( %s <_ %s <-> ( %s + %s ) <_ ( %s + %s ) )' % (X2, X3, X1, X2, X1, X3))], 'mpbid',
            '( %s + %s ) <_ ( %s + %s )' % (X1, X2, X1, X3))
    y2 = st(w, A0, [y1, st(w, A0, [q2], 'oveq2d', '( %s + %s ) = ( %s + %s )' % (X1, X3, X1, X4))], 'breqtrd', '( %s + %s ) <_ ( %s + %s )' % (X1, X2, X1, X4))
    y3 = st(w, A0, [y2, fin_eq], 'breqtrd', '( %s + %s ) <_ %s' % (X1, X2, X5))
    w.qed([lv[S0], st(w, A0, [lv[X1], lv[X2]], 'readdcld', '( %s + %s ) e. RR' % (X1, X2)), lv[X5], g3, y3], 'letrd', STATEMENTS['lspts'])
    go(w)
