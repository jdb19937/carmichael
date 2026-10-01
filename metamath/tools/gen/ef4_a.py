"""Sortie EF4: sum difference (ef4ssd, Lean sum_sub_sum_eq), generic edge bounds (ef4vz, ef4hz)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
from c0lib import hyp
from c8_o import numst
import lin
lin.FASTPATH = True


def gen_ssd():
    w = W('ef4ssd', 'Lean ` sum_sub_sum_eq ` : the difference of the sums over two finite sets is the difference of the sums over the two set differences.')
    h = [hyp(w, i, 'ef4ssd.%s' % i, f) for i, f in HSSD]
    s = lambda hy, r, f: w.s(hy, r, '( ph -> %s )' % f)
    C = 'C'

    def split(X, Y, hX):
        """sum_ X = sum_ ( X \\ Y ) + sum_ ( X i^i Y )"""
        d0 = w.s([], 'inindif', '( ( %s i^i %s ) i^i ( %s \\ %s ) ) = (/)' % (X, Y, X, Y))
        ic = w.s([], 'incom', '( ( %s \\ %s ) i^i ( %s i^i %s ) ) = ( ( %s i^i %s ) i^i ( %s \\ %s ) )' % (X, Y, X, Y, X, Y, X, Y))
        d1 = s([w.s([ic, d0], 'eqtri', '( ( %s \\ %s ) i^i ( %s i^i %s ) ) = (/)' % (X, Y, X, Y))], 'a1i', '( ( %s \\ %s ) i^i ( %s i^i %s ) ) = (/)' % (X, Y, X, Y))
        u0 = w.s([], 'inundif', '( ( %s i^i %s ) u. ( %s \\ %s ) ) = %s' % (X, Y, X, Y, X))
        uc = w.s([], 'uncom', '( ( %s \\ %s ) u. ( %s i^i %s ) ) = ( ( %s i^i %s ) u. ( %s \\ %s ) )' % (X, Y, X, Y, X, Y, X, Y))
        u1 = w.s([w.s([uc, u0], 'eqtri', '( ( %s \\ %s ) u. ( %s i^i %s ) ) = %s' % (X, Y, X, Y, X))], 'eqcomi', '%s = ( ( %s \\ %s ) u. ( %s i^i %s ) )' % (X, X, Y, X, Y))
        u2 = s([u1], 'a1i', '%s = ( ( %s \\ %s ) u. ( %s i^i %s ) )' % (X, X, Y, X, Y))
        Aq = '( ph /\\ q e. %s )' % X
        el = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, X)), w.inst('elun1' if X == 'A' else 'elun2')], 'syl', '( %s -> q e. ( A u. B ) )' % Aq)
        cc = w.s([w.s([], 'simpl', '( %s -> ph )' % Aq), el, 'h3'], 'syl2anc', '( %s -> C e. CC )' % Aq)
        return s([d1, u2, 'h%s' % hX, cc], 'fsumsplit', 'sum_ q e. %s C = ( sum_ q e. ( %s \\ %s ) C + sum_ q e. ( %s i^i %s ) C )' % (X, X, Y, X, Y))
    sa = split('A', 'B', '1')
    sb = split('B', 'A', '2')
    ic = w.s([w.s([], 'incom', '( B i^i A ) = ( A i^i B )')], 'sumeq1i', 'sum_ q e. ( B i^i A ) C = sum_ q e. ( A i^i B ) C')
    sb2 = s([sb, s([s([ic], 'a1i', 'sum_ q e. ( B i^i A ) C = sum_ q e. ( A i^i B ) C')], 'oveq2d', '( sum_ q e. ( B \\ A ) C + sum_ q e. ( B i^i A ) C ) = ( sum_ q e. ( B \\ A ) C + sum_ q e. ( A i^i B ) C )')],
            'eqtrd', 'sum_ q e. B C = ( sum_ q e. ( B \\ A ) C + sum_ q e. ( A i^i B ) C )')

    def fcl(X, sub):
        base = 'h1' if X.startswith('( A') else 'h2'
        ss = w.s([], 'difss' if '\\' in X else 'inss1', '%s C_ %s' % (X, X.split()[1]))
        fin = s([base, s([ss], 'a1i', '%s C_ %s' % (X, X.split()[1]))], 'ssfid', '%s e. Fin' % X)
        Aq = '( ph /\\ q e. %s )' % X
        qin = w.s([w.s([ss], 'a1i', '( %s -> %s C_ %s )' % (Aq, X, X.split()[1])), w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, X))], 'sseldd', '( %s -> q e. %s )' % (Aq, X.split()[1]))
        el2 = w.s([qin, w.inst('elun1' if X.split()[1] == 'A' else 'elun2')], 'syl', '( %s -> q e. ( A u. B ) )' % Aq)
        cc = w.s([w.s([], 'simpl', '( %s -> ph )' % Aq), el2, 'h3'], 'syl2anc', '( %s -> C e. CC )' % Aq)
        return s([fin, cc], 'fsumcl', 'sum_ q e. %s C e. CC' % X)
    ca, cb, ci = fcl('( A \\ B )', 0), fcl('( B \\ A )', 0), fcl('( A i^i B )', 0)
    SA, SB, SI = 'sum_ q e. ( A \\ B ) C', 'sum_ q e. ( B \\ A ) C', 'sum_ q e. ( A i^i B ) C'
    e1 = s([sa, sb2], 'oveq12d', '( sum_ q e. A C - sum_ q e. B C ) = ( ( %s + %s ) - ( %s + %s ) )' % (SA, SI, SB, SI))
    e2 = s([ca, cb, ci], 'pnpcan2d', '( ( %s + %s ) - ( %s + %s ) ) = ( %s - %s )' % (SA, SI, SB, SI, SA, SB))
    w.qed([e1, e2], 'eqtrd', S['ef4ssd'])
    return run8(w)


def ic_(c):
    return c.a1(c.w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')


def ptc(c, x, t, xr, tr):
    """( A -> ( x + ( _i x. t ) ) e. CC ) from reals"""
    return c([c([xr], 'recnd', '%s e. CC' % x), c([ic_(c), c([tr], 'recnd', '%s e. CC' % t)], 'mulcld', '( _i x. %s ) e. CC' % t)], 'addcld', '%s e. CC' % PTL(x, t))


def icc_in(c, x, lo, hi, xr, lor, hir, l1, l2):
    """( A -> x e. ( lo [,] hi ) ) from reals and the two bounds"""
    e = c([lor, hir, c.w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (x, lo, hi, x, lo, x, x, hi))
    return c([c([xr, l1, l2], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (x, lo, x, x, hi)), e], 'mpbird', '%s e. ( %s [,] %s )' % (x, lo, hi))


def icc_out(c, x, lo, hi, xin, lor, hir):
    """from ( A -> x e. ( lo [,] hi ) ): steps x e. RR, lo <_ x, x <_ hi"""
    e = c([lor, hir, c.w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (x, lo, hi, x, lo, x, x, hi))
    tri = c([xin, e], 'mpbid', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (x, lo, x, x, hi))
    return [c([tri, c.w.inst(k)], 'syl', f) for k, f in (('simp1', '%s e. RR' % x), ('simp2', '%s <_ %s' % (lo, x)), ('simp3', '%s <_ %s' % (x, hi)))]


def unit_t(w, A1):
    """under A1 = ( A /\\ t e. ( 0 (,) 1 ) ): t e. RR, 0 <_ t, t <_ 1, t e. ( 0 [,] 1 )"""
    c = Ctx(w, A1)
    tio = c([], 'simpr', 't e. ( 0 (,) 1 )')
    t01 = c([c.a1(w.s([], 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )'), '( 0 (,) 1 ) C_ ( 0 [,] 1 )'), tio], 'sseldd', 't e. ( 0 [,] 1 )')
    tri = c([t01, c.a1(w.s([], 'elicc01', '( t e. ( 0 [,] 1 ) <-> ( t e. RR /\\ 0 <_ t /\\ t <_ 1 ) )'), '( t e. ( 0 [,] 1 ) <-> ( t e. RR /\\ 0 <_ t /\\ t <_ 1 ) )')], 'mpbid', '( t e. RR /\\ 0 <_ t /\\ t <_ 1 )')
    return [c([tri, w.inst(k)], 'syl', f) for k, f in (('simp1', 't e. RR'), ('simp2', '0 <_ t'), ('simp3', 't <_ 1'))] + [t01]


def const_ibl(c, H, hc):
    """( A -> ( t e. ( 0 (,) 1 ) |-> H ) e. L^1 ) and ( A -> S. ( 0 (,) 1 ) H _d t = H ) for a t-free H e. CC"""
    w = c.w
    X = '( 0 (,) 1 )'
    mb = c.a1(w.s([], 'ioombl', '%s e. dom vol' % X), '%s e. dom vol' % X)
    vo = w.s([w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR'), w.s([], '0le1', '0 <_ 1'), w.inst('volioo')], 'mp3an', '( vol ` %s ) = ( 1 - 0 )' % X)
    v1 = w.s([vo, w.s([], '1m0e1', '( 1 - 0 ) = 1')], 'eqtri', '( vol ` %s ) = 1' % X)
    vr = c.a1(w.s([v1, w.s([], '1re', '1 e. RR')], 'eqeltri', '( vol ` %s ) e. RR' % X), '( vol ` %s ) e. RR' % X)
    ib = c([mb, vr, hc, w.inst('iblconst')], 'syl3anc', '( %s X. { %s } ) e. L^1' % (X, H))
    fc = c.a1(w.s([], 'fconstmpt', '( %s X. { %s } ) = ( t e. %s |-> %s )' % (X, H, X, H)), '( %s X. { %s } ) = ( t e. %s |-> %s )' % (X, H, X, H))
    ibl = c([fc, ib], 'eqeltrrd', '( t e. %s |-> %s ) e. L^1' % (X, H))
    it = c([mb, vr, hc, w.inst('itgconst')], 'syl3anc', 'S. %s %s _d t = ( %s x. ( vol ` %s ) )' % (X, H, H, X))
    it2 = c([it, c([c.a1(v1, '( vol ` %s ) = 1' % X)], 'oveq2d', '( %s x. ( vol ` %s ) ) = ( %s x. 1 )' % (H, X, H))], 'eqtrd', 'S. %s %s _d t = ( %s x. 1 )' % (X, H, H))
    return ibl, c([it2, c([hc], 'mulridd', '( %s x. 1 ) = %s' % (H, H))], 'eqtrd', 'S. %s %s _d t = %s' % (X, H, H))


def gen_vz():
    w = W('ef4vz', 'The vertical-edge ML bound: if ` abs G <_ B ` on the segment from ` C + i U ` to ` C + i V ` inside ` D ` , then ` abs ( G lint <. C + i U , C + i V >. ) <_ B ( V - U ) ` (Lean ` right_extra_le ` , ` intervalIntegral.norm_integral_le_of_norm_le_const ` ).')
    A0, G = ante_of(S['ef4vz'])
    PY = PTL('C', 'y')
    BODY = '( %s e. D /\\ ( abs ` ( G ` %s ) ) <_ B )' % (PY, PY)
    ALY = 'A. y e. ( U [,] V ) %s' % BODY
    parts = top_and(A0)
    Ap = '( %s /\\ %s /\\ %s )' % (parts[0], parts[1], ALY)
    c = Ctx(w, Ap)
    gcn = c.g('G e. ( D -cn-> CC )'); cr = c.g('C e. RR'); ur = c.g('U e. RR'); vr = c.g('V e. RR'); uv = c.g('U <_ V'); br = c.g('B e. RR')
    aly = c.g(ALY)
    Aa, Bb = PTL('C', 'U'), PTL('C', 'V')
    ac, bc = ptc(c, 'C', 'U', cr, ur), ptc(c, 'C', 'V', cr, vr)
    # the segment
    r26 = w.s([], 'r19.26', '( %s <-> ( A. y e. ( U [,] V ) %s e. D /\\ A. y e. ( U [,] V ) ( abs ` ( G ` %s ) ) <_ B ) )' % (ALY, PY, PY))
    ald = c([c([aly, c.a1(r26, r26 and '( %s <-> ( A. y e. ( U [,] V ) %s e. D /\\ A. y e. ( U [,] V ) ( abs ` ( G ` %s ) ) <_ B ) )' % (ALY, PY, PY))], 'mpbid',
               '( A. y e. ( U [,] V ) %s e. D /\\ A. y e. ( U [,] V ) ( abs ` ( G ` %s ) ) <_ B )' % (PY, PY)), w.inst('simpl')], 'syl', 'A. y e. ( U [,] V ) %s e. D' % PY)
    cb, _ = cbval = cbval_ = cbvral(w, '( U [,] V )', 'y', 't', '%s e. D' % PY)
    alt = c([ald, c.a1(cb, '( A. y e. ( U [,] V ) %s e. D <-> A. t e. ( U [,] V ) %s e. D )' % (PY, PTL('C', 't')))], 'mpbid', 'A. t e. ( U [,] V ) %s e. D' % PTL('C', 't'))
    ux, vx = c([ur], 'rexrd', 'U e. RR*'), c([vr], 'rexrd', 'V e. RR*')
    uin = c([ux, vx, uv, w.inst('lbicc2')], 'syl3anc', 'U e. ( U [,] V )')
    vin = c([ux, vx, uv, w.inst('ubicc2')], 'syl3anc', 'V e. ( U [,] V )')
    VS = tsub(stmt('ef3vseg'), {'P': 'C', 'L': 'U', 'H': 'V', 'E': 'U', 'K': 'V'})
    va, vcn = ante_of(VS)
    seg = c([c([c([cr, c([ur, vr], 'jca', '( U e. RR /\\ V e. RR )')], 'jca', top_and(va)[0]), c([c([uin, vin], 'jca', top_and(top_and(va)[1])[0]), alt], 'jca', top_and(va)[1])], 'jca', va),
             w.inst('ef3vseg')], 'syl', vcn)
    # pointwise
    A1 = '( %s /\\ t e. ( 0 (,) 1 ) )' % Ap
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    tr, t0, t1, t01 = unit_t(w, A1)
    cl = Closure(w, A1, {'C': ('RR', L1(cr)), 'U': ('RR', L1(ur)), 'V': ('RR', L1(vr)), 't': ('RR', tr), '_i': ('CC', ic_(c1))})
    for k in ('C', 'U', 'V', 't', '_i'):
        cl.atom(k)
    WW = '( %s + ( t x. ( %s - %s ) ) )' % (Aa, Bb, Aa)
    UU = '( U + ( t x. ( V - U ) ) )'
    e1 = ringeq(w, A1, WW, PTL('C', UU), cl)
    uur = cl.mem(UU, 'RR')
    lv = {'U': L1(ur), 'V': L1(vr), 't': tr}
    vu0 = lin8(w, A1, [L1(uv)], '0 <_ ( V - U )', lv)
    u1 = lin8(w, A1, [t0, t1, L1(uv)], 'U <_ %s' % UU, lv, products=True)
    u2 = lin8(w, A1, [t0, t1, L1(uv)], '%s <_ V' % UU, lv, products=True)
    uin1 = icc_in(c1, UU, 'U', 'V', uur, L1(ur), L1(vr), u1, u2)
    pv, _ = ral_at(w, A1, L1(aly), 'y', UU, BODY, uin1)
    PU = PTL('C', UU)
    pd = c1([pv, w.inst('simpl')], 'syl', '%s e. D' % PU)
    pb = c1([pv, w.inst('simpr')], 'syl', '( abs ` ( G ` %s ) ) <_ B' % PU)
    wd = c1([e1, pd], 'eqeltrd', '%s e. D' % WW)
    gv = c1([c1([L1(gcn), w.inst('cncff')], 'syl', 'G : D --> CC'), wd], 'ffvelcdmd', '( G ` %s ) e. CC' % WW)
    ge = c1([c1([e1], 'fveq2d', '( G ` %s ) = ( G ` %s )' % (WW, PU))], 'fveq2d', '( abs ` ( G ` %s ) ) = ( abs ` ( G ` %s ) )' % (WW, PU))
    gb = c1([ge, pb], 'eqbrtrd', '( abs ` ( G ` %s ) ) <_ B' % WW)
    DF = '( %s - %s )' % (Bb, Aa)
    d1 = ringeq(w, A1, DF, '( _i x. ( V - U ) )', cl)
    vur = cl.mem('( V - U )', 'RR')
    ad = c1([c1([d1], 'fveq2d', '( abs ` %s ) = ( abs ` ( _i x. ( V - U ) ) )' % DF),
             c1([c1([ic_(c1), c1([vur], 'recnd', '( V - U ) e. CC')], 'absmuld', '( abs ` ( _i x. ( V - U ) ) ) = ( ( abs ` _i ) x. ( abs ` ( V - U ) ) )'),
                 c1([c1.a1(w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1'), c1([vur, vu0], 'absidd', '( abs ` ( V - U ) ) = ( V - U )')], 'oveq12d',
                    '( ( abs ` _i ) x. ( abs ` ( V - U ) ) ) = ( 1 x. ( V - U ) )')], 'eqtrd', '( abs ` ( _i x. ( V - U ) ) ) = ( 1 x. ( V - U ) )')], 'eqtrd', '( abs ` %s ) = ( 1 x. ( V - U ) )' % DF)
    ad2 = c1([ad, c1([c1([vur], 'recnd', '( V - U ) e. CC')], 'mullidd', '( 1 x. ( V - U ) ) = ( V - U )')], 'eqtrd', '( abs ` %s ) = ( V - U )' % DF)
    dc = c1([L1(bc), L1(ac)], 'subcld', '%s e. CC' % DF)
    am = c1([gv, dc], 'absmuld', '( abs ` ( ( G ` %s ) x. %s ) ) = ( ( abs ` ( G ` %s ) ) x. ( abs ` %s ) )' % (WW, DF, WW, DF))
    am2 = c1([am, c1([ad2], 'oveq2d', '( ( abs ` ( G ` %s ) ) x. ( abs ` %s ) ) = ( ( abs ` ( G ` %s ) ) x. ( V - U ) )' % (WW, DF, WW))], 'eqtrd',
             '( abs ` ( ( G ` %s ) x. %s ) ) = ( ( abs ` ( G ` %s ) ) x. ( V - U ) )' % (WW, DF, WW))
    H = '( B x. ( V - U ) )'
    le = c1([c1([gv], 'abscld', '( abs ` ( G ` %s ) ) e. RR' % WW), L1(br), vur, vu0, gb], 'lemul1ad', '( ( abs ` ( G ` %s ) ) x. ( V - U ) ) <_ %s' % (WW, H))
    ptw = c1([am2, le], 'eqbrtrd', '( abs ` ( ( G ` %s ) x. %s ) ) <_ %s' % (WW, DF, H))
    hr = c([br, c([vr, ur], 'resubcld', '( V - U ) e. RR')], 'remulcld', '%s e. RR' % H)
    hc = c([hr], 'recnd', '%s e. CC' % H)
    ibl, itv = const_ibl(c, H, hc)
    le2 = c([ac, bc, gcn, seg, ibl, lift(w, hr, A1), ptw], 'lintle', '( abs ` ( G lint <. %s , %s >. ) ) <_ S. ( 0 (,) 1 ) %s _d t' % (Aa, Bb, H))
    fin = c([le2, itv], 'breqtrd', G)
    # back to the frozen antecedent
    cb2, _ = cbvral(w, '( U [,] V )', 't', 'y', '( %s e. D /\\ ( abs ` ( G ` %s ) ) <_ B )' % (PTL('C', 't'), PTL('C', 't')))
    c0 = Ctx(w, A0)
    alt0 = c0.g(parts[2])
    aly0 = c0([alt0, c0.a1(cb2, '( %s <-> %s )' % (parts[2], ALY))], 'mpbid', ALY)
    ap = c0([c0.g(parts[0]), c0.g(parts[1]), aly0], '3jca', Ap)
    w.qed([ap, fin], 'syl', S['ef4vz'])
    return run8(w)



def gen_hz():
    w = W('ef4hz', 'Lean ` horiz_edge_le ` (generic form): if ` abs G ( x + i S ) <_ B Y ^ x ` on the horizontal segment from ` P + i S ` to ` Q + i S ` inside ` D ` , then ` abs ( G lint ) <_ B ( Y ^ Q - Y ^ P ) / log Y ` ( ~ lintle , ~ cxpaffitg ).')
    A0, G = ante_of(S['ef4hz'])
    c = Ctx(w, A0)
    gcn = c.g('G e. ( D -cn-> CC )'); yp = c.g('Y e. RR+'); y1 = c.g('Y =/= 1'); pr = c.g('P e. RR'); qr = c.g('Q e. RR'); pq = c.g('P <_ Q')
    sr = c.g('S e. RR'); br = c.g('B e. RR')
    PX = PTL('x', 'S')
    BODY = '( %s e. D /\\ ( abs ` ( G ` %s ) ) <_ ( B x. ( Y ^c x ) ) )' % (PX, PX)
    alx = c.g('A. x e. ( P [,] Q ) %s' % BODY)
    Aa, Bb = PTL('P', 'S'), PTL('Q', 'S')
    ac, bc = ptc(c, 'P', 'S', pr, sr), ptc(c, 'Q', 'S', qr, sr)
    r26 = w.s([], 'r19.26', '( A. x e. ( P [,] Q ) %s <-> ( A. x e. ( P [,] Q ) %s e. D /\\ A. x e. ( P [,] Q ) ( abs ` ( G ` %s ) ) <_ ( B x. ( Y ^c x ) ) ) )' % (BODY, PX, PX))
    ald = c([c([alx, c.a1(r26, body_of_closed(w, r26))], 'mpbid', '( A. x e. ( P [,] Q ) %s e. D /\\ A. x e. ( P [,] Q ) ( abs ` ( G ` %s ) ) <_ ( B x. ( Y ^c x ) ) )' % (PX, PX)), w.inst('simpl')],
            'syl', 'A. x e. ( P [,] Q ) %s e. D' % PX)
    px, qx = c([pr], 'rexrd', 'P e. RR*'), c([qr], 'rexrd', 'Q e. RR*')
    pin = c([px, qx, pq, w.inst('lbicc2')], 'syl3anc', 'P e. ( P [,] Q )')
    qin = c([px, qx, pq, w.inst('ubicc2')], 'syl3anc', 'Q e. ( P [,] Q )')
    HS = tsub(stmt('ef3hseg'), {'M': 'S', 'E': 'P', 'K': 'Q'})
    ha, hcn = ante_of(HS)
    seg = c([c([c([sr, c([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )')], 'jca', top_and(ha)[0]), c([c([pin, qin], 'jca', top_and(top_and(ha)[1])[0]), ald], 'jca', top_and(ha)[1])], 'jca', ha),
             w.inst('ef3hseg')], 'syl', hcn)
    A1 = '( %s /\\ t e. ( 0 (,) 1 ) )' % A0
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    tr, t0, t1, t01 = unit_t(w, A1)
    cl = Closure(w, A1, {'P': ('RR', L1(pr)), 'Q': ('RR', L1(qr)), 'S': ('RR', L1(sr)), 't': ('RR', tr), '_i': ('CC', ic_(c1))})
    for k in ('P', 'Q', 'S', 't', '_i'):
        cl.atom(k)
    WW = '( %s + ( t x. ( %s - %s ) ) )' % (Aa, Bb, Aa)
    XX = '( P + ( t x. ( Q - P ) ) )'
    e1 = ringeq(w, A1, WW, PTL(XX, 'S'), cl)
    xr = cl.mem(XX, 'RR')
    lv = {'P': L1(pr), 'Q': L1(qr), 't': tr}
    qp0 = lin8(w, A1, [L1(pq)], '0 <_ ( Q - P )', lv)
    x1 = lin8(w, A1, [t0, t1, L1(pq)], 'P <_ %s' % XX, lv, products=True)
    x2 = lin8(w, A1, [t0, t1, L1(pq)], '%s <_ Q' % XX, lv, products=True)
    xin = icc_in(c1, XX, 'P', 'Q', xr, L1(pr), L1(qr), x1, x2)
    pv, _ = ral_at(w, A1, L1(alx), 'x', XX, BODY, xin)
    PU = PTL(XX, 'S')
    YX = '( Y ^c %s )' % XX
    pd = c1([pv, w.inst('simpl')], 'syl', '%s e. D' % PU)
    pb = c1([pv, w.inst('simpr')], 'syl', '( abs ` ( G ` %s ) ) <_ ( B x. %s )' % (PU, YX))
    wd = c1([e1, pd], 'eqeltrd', '%s e. D' % WW)
    gv = c1([c1([L1(gcn), w.inst('cncff')], 'syl', 'G : D --> CC'), wd], 'ffvelcdmd', '( G ` %s ) e. CC' % WW)
    ge = c1([c1([e1], 'fveq2d', '( G ` %s ) = ( G ` %s )' % (WW, PU))], 'fveq2d', '( abs ` ( G ` %s ) ) = ( abs ` ( G ` %s ) )' % (WW, PU))
    gb = c1([ge, pb], 'eqbrtrd', '( abs ` ( G ` %s ) ) <_ ( B x. %s )' % (WW, YX))
    DF = '( %s - %s )' % (Bb, Aa)
    d1 = ringeq(w, A1, DF, '( Q - P )', cl)
    qpr = cl.mem('( Q - P )', 'RR')
    ad2 = c1([c1([d1], 'fveq2d', '( abs ` %s ) = ( abs ` ( Q - P ) )' % DF), c1([qpr, qp0], 'absidd', '( abs ` ( Q - P ) ) = ( Q - P )')], 'eqtrd', '( abs ` %s ) = ( Q - P )' % DF)
    dc = c1([L1(bc), L1(ac)], 'subcld', '%s e. CC' % DF)
    am = c1([gv, dc], 'absmuld', '( abs ` ( ( G ` %s ) x. %s ) ) = ( ( abs ` ( G ` %s ) ) x. ( abs ` %s ) )' % (WW, DF, WW, DF))
    am2 = c1([am, c1([ad2], 'oveq2d', '( ( abs ` ( G ` %s ) ) x. ( abs ` %s ) ) = ( ( abs ` ( G ` %s ) ) x. ( Q - P ) )' % (WW, DF, WW))], 'eqtrd',
             '( abs ` ( ( G ` %s ) x. %s ) ) = ( ( abs ` ( G ` %s ) ) x. ( Q - P ) )' % (WW, DF, WW))
    yxr = c1([L1(yp), xr], 'rpcxpcld', '%s e. RR+' % YX)
    byr = c1([L1(br), c1([yxr], 'rpred', '%s e. RR' % YX)], 'remulcld', '( B x. %s ) e. RR' % YX)
    le = c1([c1([gv], 'abscld', '( abs ` ( G ` %s ) ) e. RR' % WW), byr, qpr, qp0, gb], 'lemul1ad', '( ( abs ` ( G ` %s ) ) x. ( Q - P ) ) <_ ( ( B x. %s ) x. ( Q - P ) )' % (WW, YX))
    FI = '( %s x. ( Q - P ) )' % YX
    H = '( B x. %s )' % FI
    ma = c1([L1(c([br], 'recnd', 'B e. CC')), c1([yxr], 'rpcnd', '%s e. CC' % YX), c1([qpr], 'recnd', '( Q - P ) e. CC')], 'mulassd', '( ( B x. %s ) x. ( Q - P ) ) = %s' % (YX, H))
    ptw = c1([c1([am2, le], 'eqbrtrd', '( abs ` ( ( G ` %s ) x. %s ) ) <_ ( ( B x. %s ) x. ( Q - P ) )' % (WW, DF, YX)), ma], 'breqtrd', '( abs ` ( ( G ` %s ) x. %s ) ) <_ %s' % (WW, DF, H))
    hr = c1([L1(br), c1([c1([yxr], 'rpred', '%s e. RR' % YX), qpr], 'remulcld', '%s e. RR' % FI)], 'remulcld', '%s e. RR' % H)
    AFF = tsub(stmt('cxpaffibl'), {'U': 'Y'})
    aa, acn = ante_of(AFF)
    ab = c([c([c([yp, y1], 'jca', top_and(aa)[0]), c([pr, qr], 'jca', top_and(aa)[1])], 'jca', aa), w.inst('cxpaffibl')], 'syl', acn)
    fibl = c([ab, w.inst('simpr')], 'syl', top_and(acn)[1])
    fcc = c1([c1([yxr], 'rpcnd', '%s e. CC' % YX), c1([qpr], 'recnd', '( Q - P ) e. CC')], 'mulcld', '%s e. CC' % FI)
    bcc = c([br], 'recnd', 'B e. CC')
    hibl = c([bcc, fcc, fibl], 'iblmulc2', '( t e. ( 0 (,) 1 ) |-> %s ) e. L^1' % H)
    le2 = c([ac, bc, gcn, seg, hibl, hr, ptw], 'lintle', '( abs ` ( G lint <. %s , %s >. ) ) <_ S. ( 0 (,) 1 ) %s _d t' % (Aa, Bb, H))
    im = c([bcc, fcc, fibl], 'itgmulc2', '( B x. S. ( 0 (,) 1 ) %s _d t ) = S. ( 0 (,) 1 ) %s _d t' % (FI, H))
    IT = tsub(stmt('cxpaffitg'), {'U': 'Y'})
    ia, icn = ante_of(IT)
    iv = c([c([c([yp, y1], 'jca', top_and(ia)[0]), c([pr, qr], 'jca', top_and(ia)[1])], 'jca', ia), w.inst('cxpaffitg')], 'syl', icn)
    RR_ = '( ( ( Y ^c Q ) - ( Y ^c P ) ) / ( log ` Y ) )'
    im2 = c([c([im], 'eqcomd', 'S. ( 0 (,) 1 ) %s _d t = ( B x. S. ( 0 (,) 1 ) %s _d t )' % (H, FI)), c([iv], 'oveq2d', '( B x. S. ( 0 (,) 1 ) %s _d t ) = ( B x. %s )' % (FI, RR_))], 'eqtrd',
             'S. ( 0 (,) 1 ) %s _d t = ( B x. %s )' % (H, RR_))
    w.qed([le2, im2], 'breqtrd', S['ef4hz'])
    return run8(w)


def body_of_closed(w, st):
    return [l for l in w.lines if l.startswith(st + ':')][0].split(' |- ', 1)[1]


GENS = {'ef4ssd': gen_ssd, 'ef4vz': gen_vz, 'ef4hz': gen_hz}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
