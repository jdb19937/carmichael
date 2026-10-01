"""Sortie MV, section B: the Fejer integral over a quarter period
(mvdvsin, mvcositg, mvfejint)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from mvlib import *
from z4blib import fvm2
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


def rrss(w, ante):
    return a1(w, ante, 'ax-resscn', 'RR C_ CC')


def cnrr(w, ante, cl0, clv, v='t'):
    """a CN builder for ( v e. RR |-> E ) under ANTE; clv: Closure under ( ante /\\ v e. RR )"""
    return CN(w, ante, v, 'RR', rrss(w, ante), cl0, clv)


def mvdvsin():
    w = W('mvdvsin', 'The derivative of t |-> sin ( B t ) on RR (chain rule, dvmptco with dvsin).')
    A0 = 'B e. RR'
    br = w.s([], 'id', '( B e. RR -> B e. RR )')
    bc = dst(w, A0, [br], 'recnd', 'B e. CC')
    At = '( %s /\\ t e. RR )' % A0
    tr = w.s([], 'simpr', '( %s -> t e. RR )' % At)
    ct = Closure(w, At, {'B': ('RR', lift(w, br, At)), 't': ('RR', tr)})
    Ay = '( %s /\\ y e. CC )' % A0
    yc = w.s([], 'simpr', '( %s -> y e. CC )' % Ay)
    cy = Closure(w, Ay, {'y': ('CC', yc)})
    rr = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }')
    cc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    # inner derivative
    did = w.s([rr], 'dvmptid', '( %s -> ( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 ) )' % A0)
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % At)
    dm = w.s([rr, ct.mem('t', 'CC'), one, did, bc], 'dvmptcmul',
             '( %s -> ( RR _D ( t e. RR |-> ( B x. t ) ) ) = ( t e. RR |-> ( B x. 1 ) ) )' % A0)
    m1 = dst(w, At, [ct.mem('B', 'CC')], 'mulridd', '( B x. 1 ) = B')
    m2 = dst(w, A0, [m1], 'mpteq2dva', '( t e. RR |-> ( B x. 1 ) ) = ( t e. RR |-> B )')
    da = eqt(w, A0, dm, m2)
    # outer derivative
    sf = a1(w, A0, 'sinf', 'sin : CC --> CC'); cf = a1(w, A0, 'cosf', 'cos : CC --> CC')
    se = dst(w, A0, [sf], 'feqmptd', 'sin = ( y e. CC |-> ( sin ` y ) )')
    ce = dst(w, A0, [cf], 'feqmptd', 'cos = ( y e. CC |-> ( cos ` y ) )')
    ds = a1(w, A0, 'dvsin', '( CC _D sin ) = cos')
    x1 = dst(w, A0, [se], 'oveq2d', '( CC _D sin ) = ( CC _D ( y e. CC |-> ( sin ` y ) ) )')
    dc = eqt(w, A0, eqt(w, A0, eqc(w, A0, x1), ds), ce)
    e = w.s([], 'fveq2', '( y = ( B x. t ) -> ( sin ` y ) = ( sin ` ( B x. t ) ) )')
    f = w.s([], 'fveq2', '( y = ( B x. t ) -> ( cos ` y ) = ( cos ` ( B x. t ) ) )')
    co = w.s([rr, cc, ct.mem('( B x. t )', 'CC'), ct.mem('B', 'CC'), cy.mem('( sin ` y )', 'CC'), cy.mem('( cos ` y )', 'CC'), da, dc, e, f],
             'dvmptco', '( %s -> ( RR _D ( t e. RR |-> ( sin ` ( B x. t ) ) ) ) = ( t e. RR |-> ( ( cos ` ( B x. t ) ) x. B ) ) )' % A0)
    mc = dst(w, At, [ct.mem('( cos ` ( B x. t ) )', 'CC'), ct.mem('B', 'CC')], 'mulcomd', '( ( cos ` ( B x. t ) ) x. B ) = ( B x. ( cos ` ( B x. t ) ) )')
    m3 = dst(w, A0, [mc], 'mpteq2dva', '( t e. RR |-> ( ( cos ` ( B x. t ) ) x. B ) ) = ( t e. RR |-> ( B x. ( cos ` ( B x. t ) ) ) )')
    eqt(w, A0, co, m3)
    qedlast(w)
    go(w)


YC = '( _pi / ( 2 x. C ) )'


def mvcositg():
    w = W('mvcositg', 'The integral of cos ( 2 K C t ) over ( 0 , pi / ( 2 C ) ) vanishes for K e. NN (FTC with the primitive sin ( 2 K C t ) / ( 2 K C )).')
    A0 = '( C e. RR+ /\\ K e. NN )'
    P = parts(w, A0)
    cp, kn = P['C e. RR+'], P['K e. NN']
    cl = Closure(w, A0, {'C': ('RR+', cp), 'K': ('NN', kn)})
    b = '( ( 2 x. K ) x. C )'
    cl.leaf('_pi', 'RR+', a1(w, A0, 'pirp', '_pi e. RR+'))
    br = cl.mem(b, 'RR'); bn = cl.ne0(b); bc = cl.mem(b, 'CC')
    ds = ap(w, A0, 'mvdvsin', [br], '( RR _D ( x e. RR |-> ( sin ` ( %s x. x ) ) ) ) = ( x e. RR |-> ( %s x. ( cos ` ( %s x. x ) ) ) )' % (b, b, b))
    At = '( %s /\\ x e. RR )' % A0
    tr = w.s([], 'simpr', '( %s -> x e. RR )' % At)
    ct = Closure(w, At, {'C': ('RR+', lift(w, cp, At)), 'K': ('NN', lift(w, kn, At)), 'x': ('RR', tr)})
    SB = '( sin ` ( %s x. x ) )' % b; CB = '( cos ` ( %s x. x ) )' % b
    rr = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }')
    dd = w.s([rr, ct.mem(SB, 'CC'), ct.mem('( %s x. %s )' % (b, CB), 'CC'), ds, bc, bn], 'dvmptdivc',
             '( %s -> ( RR _D ( x e. RR |-> ( %s / %s ) ) ) = ( x e. RR |-> ( ( %s x. %s ) / %s ) ) )' % (A0, SB, b, b, CB, b))
    dv = dst(w, At, [ct.mem(CB, 'CC'), ct.mem(b, 'CC'), ct.ne0(b)], 'divcan3d', '( ( %s x. %s ) / %s ) = %s' % (b, CB, b, CB))
    dm = dst(w, A0, [dv], 'mpteq2dva', '( x e. RR |-> ( ( %s x. %s ) / %s ) ) = ( x e. RR |-> %s )' % (b, CB, b, CB))
    F = '( x e. RR |-> ( %s / %s ) )' % (SB, b); G = '( x e. RR |-> %s )' % CB
    dF = eqt(w, A0, dd, dm)
    ff = dst(w, A0, [ct.mem('( %s / %s )' % (SB, b), 'CC')], 'fmptd', '%s : RR --> CC' % F)
    cn = cnrr(w, A0, cl, ct, 'x')
    gcn = cn(CB)
    Y = YC
    yr = cl.mem(Y, 'RR'); y0 = cl.ge0(Y)
    z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A0)
    ftc = ap(w, A0, 'lsftc', [J(w, A0, J(w, A0, z0, yr, y0), J(w, A0, ff, dF, gcn))],
             '%s = ( ( %s ` %s ) - ( %s ` 0 ) )' % (ITG(IOO('0', Y), '( %s ` t )' % G), F, Y, F))
    # the integrand
    Ai = '( %s /\\ t e. %s )' % (A0, IOO('0', Y))
    ti = ap(w, Ai, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Ai, IOO('0', Y)))], 't e. RR')
    ci = Closure(w, Ai, {'C': ('RR+', lift(w, cp, Ai)), 'K': ('NN', lift(w, kn, Ai)), 't': ('RR', ti)})
    CBt = CB.replace('x. x )', 'x. t )')
    gv = fvmd(w, Ai, 'x', 'RR', CB, 't', ti, ci.mem(CBt, 'CC'))
    ma = ci.mem('( 2 x. K )', 'CC')
    as_ = dst(w, Ai, [ma, ci.mem('C', 'CC'), ci.mem('t', 'CC')], 'mulassd', '( %s x. t ) = ( ( 2 x. K ) x. ( C x. t ) )' % b)
    ca = dst(w, Ai, [as_], 'fveq2d', '%s = ( cos ` ( ( 2 x. K ) x. ( C x. t ) ) )' % CBt)
    ig = dst(w, A0, [eqt(w, Ai, gv, ca)], 'itgeq2dv', '%s = %s' % (ITG(IOO('0', Y), '( %s ` t )' % G), ITG(IOO('0', Y), '( cos ` ( ( 2 x. K ) x. ( C x. t ) ) )')))
    # F at the ends
    fY = fvmd(w, A0, 'x', 'RR', '( %s / %s )' % (SB, b), Y, yr, cl.mem('( ( sin ` ( %s x. %s ) ) / %s )' % (b, Y, b), 'CC'))
    f0 = fvmd(w, A0, 'x', 'RR', '( %s / %s )' % (SB, b), '0', z0, cl.mem('( ( sin ` ( %s x. 0 ) ) / %s )' % (b, b), 'CC'))
    # b Y = K pi
    C2 = '( 2 x. C )'
    r1 = ringeq(w, A0, b, '( K x. %s )' % C2, cl)
    r2 = dst(w, A0, [r1], 'oveq1d', '( %s x. %s ) = ( ( K x. %s ) x. %s )' % (b, Y, C2, Y))
    r3 = dst(w, A0, [cl.mem('K', 'CC'), cl.mem(C2, 'CC'), cl.mem(Y, 'CC')], 'mulassd', '( ( K x. %s ) x. %s ) = ( K x. ( %s x. %s ) )' % (C2, Y, C2, Y))
    r4 = dst(w, A0, [cl.mem('_pi', 'CC'), cl.mem(C2, 'CC'), cl.ne0(C2)], 'divcan2d', '( %s x. %s ) = _pi' % (C2, Y))
    r5 = dst(w, A0, [r4], 'oveq2d', '( K x. ( %s x. %s ) ) = ( K x. _pi )' % (C2, Y))
    bY = eqt(w, A0, eqt(w, A0, r2, r3), r5)
    s1 = dst(w, A0, [bY], 'fveq2d', '( sin ` ( %s x. %s ) ) = ( sin ` ( K x. _pi ) )' % (b, Y))
    s2 = ap(w, A0, 'sinkpi', [cl.mem('K', 'ZZ')], '( sin ` ( K x. _pi ) ) = 0')
    s3 = dst(w, A0, [eqt(w, A0, s1, s2)], 'oveq1d', '( ( sin ` ( %s x. %s ) ) / %s ) = ( 0 / %s )' % (b, Y, b, b))
    s4 = eqt(w, A0, s3, dst(w, A0, [bc, bn], 'div0d', '( 0 / %s ) = 0' % b))
    v1 = eqt(w, A0, fY, s4)
    z1 = dst(w, A0, [bc], 'mul01d', '( %s x. 0 ) = 0' % b)
    z2 = eqt(w, A0, dst(w, A0, [z1], 'fveq2d', '( sin ` ( %s x. 0 ) ) = ( sin ` 0 )' % b), a1(w, A0, 'sin0', '( sin ` 0 ) = 0'))
    z3 = dst(w, A0, [z2], 'oveq1d', '( ( sin ` ( %s x. 0 ) ) / %s ) = ( 0 / %s )' % (b, b, b))
    v0 = eqt(w, A0, f0, eqt(w, A0, z3, dst(w, A0, [bc, bn], 'div0d', '( 0 / %s ) = 0' % b)))
    d = dst(w, A0, [v1, v0], 'oveq12d', '( ( %s ` %s ) - ( %s ` 0 ) ) = ( 0 - 0 )' % (F, Y, F))
    d2 = eqt(w, A0, d, a1(w, A0, '0m0e0', '( 0 - 0 ) = 0'))
    eqt(w, A0, eqc(w, A0, ig), eqt(w, A0, ftc, d2))
    qedlast(w)
    go(w)



def ioomem(w, ante, a, b, v='t'):
    """( ( ante /\\ v e. ( a (,) b ) ) -> v e. RR ) and the extended antecedent"""
    Av = '( %s /\\ %s e. %s )' % (ante, v, IOO(a, b))
    return Av, ap(w, Av, 'elioore', [w.s([], 'simpr', '( %s -> %s e. %s )' % (Av, v, IOO(a, b)))], '%s e. RR' % v)


def ibl_rr(w, ante, a_st, b_st, a, b, E, cn):
    """( ante -> ( t e. ( a (,) b ) |-> E ) e. L^1 ) from continuity on RR"""
    return w.s([a_st, b_st, cn(E)], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (ante, IOO(a, b), E))


def mvfejint():
    w = W('mvfejint', 'The Fejer integral over a quarter period: the integral of sum_ m < N ( 1 + 2 sum_ k <_ m cos ( 2 k C t ) ) over ( 0 , pi / ( 2 C ) ) is N pi / ( 2 C ).')
    A0 = '( C e. RR+ /\\ N e. NN0 )'
    P = parts(w, A0)
    cp, nn = P['C e. RR+'], P['N e. NN0']
    Y = YC; I = IOO('0', Y)
    cl = Closure(w, A0, {'C': ('RR+', cp), 'N': ('NN0', nn), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    yr = cl.mem(Y, 'RR'); z0 = w.s([], '0red', '( %s -> 0 e. RR )' % A0)
    SK = 'sum_ k e. ( 1 ... m ) ( cos ` ( ( 2 x. k ) x. ( C x. t ) ) )'
    Q = '( 1 + ( 2 x. %s ) )' % SK
    COS = '( cos ` ( ( 2 x. k ) x. ( C x. t ) ) )'
    Am = '( %s /\\ m e. ( 0 ..^ N ) )' % A0
    mn0 = ap(w, Am, 'elfzonn0', [w.s([], 'simpr', '( %s -> m e. ( 0 ..^ N ) )' % Am)], 'm e. NN0')
    cpm = lift(w, cp, Am)
    clm = Closure(w, Am, {'C': ('RR+', cpm), 'm': ('NN0', mn0), '_pi': ('RR+', a1(w, Am, 'pirp', '_pi e. RR+'))})
    Amk = '( %s /\\ k e. ( 1 ... m ) )' % Am
    kn = ap(w, Amk, 'elfznn', [w.s([], 'simpr', '( %s -> k e. ( 1 ... m ) )' % Amk)], 'k e. NN')
    cpk = lift(w, cp, Amk)
    clk = Closure(w, Amk, {'C': ('RR+', cpk), 'k': ('NN', kn), '_pi': ('RR+', a1(w, Amk, 'pirp', '_pi e. RR+'))})
    # integrability of each cosine, on ( 0 , Y )
    Amkt = '( %s /\\ t e. RR )' % Amk
    clkt = Closure(w, Amkt, {'C': ('RR+', lift(w, cp, Amkt)), 'k': ('NN', lift(w, kn, Amkt)), 't': ('RR', w.s([], 'simpr', '( %s -> t e. RR )' % Amkt))})
    cnk = CN(w, Amk, 't', 'RR', a1(w, Amk, 'ax-resscn', 'RR C_ CC'), clk, clkt)
    ibk = ibl_rr(w, Amk, lift(w, z0, Amk), clk.mem(Y, 'RR'), '0', Y, COS, cnk)
    Amkti, tri = ioomem(w, Amk, '0', Y)
    Amti = '( %s /\\ ( t e. %s /\\ k e. ( 1 ... m ) ) )' % (Am, I)
    # membership in the itgfsum form ( ( ph /\ ( t e. A /\ k e. B ) ) -> C e. V )
    t_i = ap(w, Amti, 'elioore', [w.s([], 'simprl', '( %s -> t e. %s )' % (Amti, I))], 't e. RR')
    k_i = ap(w, Amti, 'elfznn', [w.s([], 'simprr', '( %s -> k e. ( 1 ... m ) )' % Amti)], 'k e. NN')
    clti = Closure(w, Amti, {'C': ('RR+', lift(w, cp, Amti)), 'k': ('NN', k_i), 't': ('RR', t_i)})
    fin_m = w.s([], 'fzfid', '( %s -> ( 1 ... m ) e. Fin )' % Am)
    ioo = a1(w, Am, 'ioombl', '%s e. dom vol' % I)
    inner = w.s([ioo, fin_m, clti.mem(COS, 'CC'), ibk], 'itgfsum',
                '( %s -> ( ( t e. %s |-> %s ) e. L^1 /\\ %s = sum_ k e. ( 1 ... m ) %s ) )' % (Am, I, SK, ITG(I, SK), ITG(I, COS)))
    iblSK = dst(w, Am, [inner], 'simpld', '( t e. %s |-> %s ) e. L^1' % (I, SK))
    itgSK = dst(w, Am, [inner], 'simprd', '%s = sum_ k e. ( 1 ... m ) %s' % (ITG(I, SK), ITG(I, COS)))
    zk = ap(w, Amk, 'mvcositg', [cpk, kn], '%s = 0' % ITG(I, COS))
    s0 = dst(w, Am, [zk], 'sumeq2dv', 'sum_ k e. ( 1 ... m ) %s = sum_ k e. ( 1 ... m ) 0' % ITG(I, COS))
    sz = w.s([w.s([fin_m], 'olcd', '( %s -> ( ( 1 ... m ) C_ ( ZZ>= ` 1 ) \\/ ( 1 ... m ) e. Fin ) )' % Am), w.inst('sumz')], 'syl',
             '( %s -> sum_ k e. ( 1 ... m ) 0 = 0 )' % Am)
    ISK0 = eqt(w, Am, eqt(w, Am, itgSK, s0), sz)            # S. SK = 0
    # the constant and the combination
    Amt, trt = ioomem(w, Am, '0', Y)
    cmt = Closure(w, Amt, {'C': ('RR+', lift(w, cp, Amt)), 'm': ('NN0', lift(w, mn0, Amt)), 't': ('RR', trt)})
    skc = cmt.mem(SK, 'CC')
    two = w.s([], '2cnd', '( %s -> 2 e. CC )' % Am)
    ibl2 = w.s([two, skc, iblSK], 'iblmulc2', '( %s -> ( t e. %s |-> ( 2 x. %s ) ) e. L^1 )' % (Am, I, SK))
    it2 = w.s([two, skc, iblSK], 'itgmulc2', '( %s -> ( 2 x. %s ) = %s )' % (Am, ITG(I, SK), ITG(I, '( 2 x. %s )' % SK)))
    Amt2 = '( %s /\\ t e. RR )' % Am
    clmt2 = Closure(w, Amt2, {'C': ('RR+', lift(w, cp, Amt2)), 't': ('RR', w.s([], 'simpr', '( %s -> t e. RR )' % Amt2))})
    cnm = CN(w, Am, 't', 'RR', a1(w, Am, 'ax-resscn', 'RR C_ CC'), clm, clmt2)
    ibl1 = ibl_rr(w, Am, lift(w, z0, Am), clm.mem(Y, 'RR'), '0', Y, '1', cnm)
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % Amt)
    iad = w.s([one, ibl1, cmt.mem('( 2 x. %s )' % SK, 'CC'), ibl2], 'ibladd', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (Am, I, Q))
    itad = w.s([one, ibl1, cmt.mem('( 2 x. %s )' % SK, 'CC'), ibl2], 'itgadd', '( %s -> %s = ( %s + %s ) )' % (Am, ITG(I, Q), ITG(I, '1'), ITG(I, '( 2 x. %s )' % SK)))
    ymr = clm.mem(Y, 'RR'); y0 = clm.ge0(Y)
    vol = w.s([lift(w, z0, Am), ymr, y0, w.inst('volioo')], 'syl3anc', '( %s -> ( vol ` %s ) = ( %s - 0 ) )' % (Am, I, Y))
    vol2 = eqt(w, Am, vol, dst(w, Am, [clm.mem(Y, 'CC')], 'subid1d', '( %s - 0 ) = %s' % (Y, Y)))
    volr = w.s([vol2, ymr], 'eqeltrd', '( %s -> ( vol ` %s ) e. RR )' % (Am, I))
    ic = w.s([ioo, volr, w.s([], '1cnd', '( %s -> 1 e. CC )' % Am), w.inst('itgconst')], 'syl3anc',
             '( %s -> %s = ( 1 x. ( vol ` %s ) ) )' % (Am, ITG(I, '1'), I))
    ic2 = eqt(w, Am, ic, dst(w, Am, [w.s([vol2], 'id', '( %s -> ( vol ` %s ) = %s )' % (Am, I, Y)) if False else vol2], 'oveq2d', '( 1 x. ( vol ` %s ) ) = ( 1 x. %s )' % (I, Y)))
    ic3 = eqt(w, Am, ic2, dst(w, Am, [clm.mem(Y, 'CC')], 'mullidd', '( 1 x. %s ) = %s' % (Y, Y)))
    z2 = eqt(w, Am, eqc(w, Am, it2), dst(w, Am, [ISK0], 'oveq2d', '( 2 x. %s ) = ( 2 x. 0 )' % ITG(I, SK)))
    z3 = eqt(w, Am, z2, a1(w, Am, '2t0e0', '( 2 x. 0 ) = 0'))
    q1 = dst(w, Am, [ic3, z3], 'oveq12d', '( %s + %s ) = ( %s + 0 )' % (ITG(I, '1'), ITG(I, '( 2 x. %s )' % SK), Y))
    IQ = eqt(w, Am, eqt(w, Am, itad, q1), dst(w, Am, [clm.mem(Y, 'CC')], 'addridd', '( %s + 0 ) = %s' % (Y, Y)))
    # outer sum
    Ato = '( %s /\\ ( t e. %s /\\ m e. ( 0 ..^ N ) ) )' % (A0, I)
    t_o = ap(w, Ato, 'elioore', [w.s([], 'simprl', '( %s -> t e. %s )' % (Ato, I))], 't e. RR')
    m_o = ap(w, Ato, 'elfzonn0', [w.s([], 'simprr', '( %s -> m e. ( 0 ..^ N ) )' % Ato)], 'm e. NN0')
    clo = Closure(w, Ato, {'C': ('RR+', lift(w, cp, Ato)), 'm': ('NN0', m_o), 't': ('RR', t_o)})
    fzo = a1(w, A0, 'fzofi', '( 0 ..^ N ) e. Fin')
    outer = w.s([a1(w, A0, 'ioombl', '%s e. dom vol' % I), fzo, clo.mem(Q, 'CC'), iad], 'itgfsum',
                '( %s -> ( ( t e. %s |-> %s ) e. L^1 /\\ %s = sum_ m e. ( 0 ..^ N ) %s ) )' % (A0, I, PT('N', '( C x. t )'), ITG(I, PT('N', '( C x. t )')), ITG(I, Q)))
    o2 = dst(w, A0, [outer], 'simprd', '%s = sum_ m e. ( 0 ..^ N ) %s' % (ITG(I, PT('N', '( C x. t )')), ITG(I, Q)))
    o3 = dst(w, A0, [IQ], 'sumeq2dv', 'sum_ m e. ( 0 ..^ N ) %s = sum_ m e. ( 0 ..^ N ) %s' % (ITG(I, Q), Y))
    o4 = w.s([fzo, cl.mem(Y, 'CC'), w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ m e. ( 0 ..^ N ) %s = ( ( # ` ( 0 ..^ N ) ) x. %s ) )' % (A0, Y, Y))
    o5 = dst(w, A0, [ap(w, A0, 'hashfzo0', [nn], '( # ` ( 0 ..^ N ) ) = N')], 'oveq1d', '( ( # ` ( 0 ..^ N ) ) x. %s ) = ( N x. %s )' % (Y, Y))
    val = eqt(w, A0, eqt(w, A0, eqt(w, A0, o2, o3), o4), o5)
    o1 = dst(w, A0, [outer], 'simpld', '( t e. %s |-> %s ) e. L^1' % (I, PT('N', '( C x. t )')))
    J(w, A0, o1, val)
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvdvsin()
    mvcositg()
    mvfejint()
