"""Sortie T21b: eventual statements (t21evan, t21evl2, t21evll, t21evlg, t21thr)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *


def EVB(f, b='b', x='x'):
    return 'E. %s e. RR A. %s e. RR ( %s <_ %s -> %s )' % (b, x, b, x, f)


def rename_ev(w, f, b1, b2):
    """closed |- ( EVB(f,b1) <-> EVB(f,b2) )"""
    e = '%s = %s' % (b1, b2)
    c1 = w.s([], 'breq1', '( %s -> ( %s <_ x <-> %s <_ x ) )' % (e, b1, b2))
    c2 = w.s([c1], 'imbi1d', '( %s -> ( ( %s <_ x -> %s ) <-> ( %s <_ x -> %s ) ) )' % (e, b1, f, b2, f))
    c3 = w.s([c2], 'ralbidv', '( %s -> ( A. x e. RR ( %s <_ x -> %s ) <-> A. x e. RR ( %s <_ x -> %s ) ) )' % (e, b1, f, b2, f))
    return w.s([c3], 'cbvrexvw', '( %s <-> %s )' % (EVB(f, b1), EVB(f, b2)))


def gen_evan():
    w = W('t21evan', 'Two eventual statements hold together eventually (the threshold is the larger one; Lean ` Filter.Eventually.and ` ).')
    A0, concl = split_imp(SB['t21evan'])
    s = S_(w, A0)
    r1 = rename_ev(w, 'ph', 'b', 'd'); r2 = rename_ev(w, 'ps', 'b', 'c')
    h1 = s([s([], 'simpl', EVB('ph')), s([r1], 'a1i', '( %s <-> %s )' % (EVB('ph'), EVB('ph', 'd')))], 'mpbid', EVB('ph', 'd'))
    h2 = s([s([], 'simpr', EVB('ps')), s([r2], 'a1i', '( %s <-> %s )' % (EVB('ps'), EVB('ps', 'c')))], 'mpbid', EVB('ps', 'c'))
    AD = 'A. x e. RR ( d <_ x -> ph )'; AC = 'A. x e. RR ( c <_ x -> ps )'
    C = '( ( ( ( %s /\\ d e. RR ) /\\ %s ) /\\ c e. RR ) /\\ %s )' % (A0, AD, AC)
    sc = S_(w, C)
    dr = sc([], 'simp-4r' if False else 'x', 'x') if False else None
    dr = w.s([], 'simp-4r', '( %s -> d e. RR )' % C) if False else None
    ad = sc([], 'simplr', AC) if False else None
    ad_ = w.s([], 'simp-3r', '( %s -> %s )' % (C, AD)) if False else None
    t1 = w.s([], 'simpl', '( %s -> ( ( ( %s /\\ d e. RR ) /\\ %s ) /\\ c e. RR ) )' % (C, A0, AD))
    t2 = w.s([t1], 'simpld', '( %s -> ( ( %s /\\ d e. RR ) /\\ %s ) )' % (C, A0, AD))
    dr = w.s([w.s([t2], 'simpld', '( %s -> ( %s /\\ d e. RR ) )' % (C, A0))], 'simprd', '( %s -> d e. RR )' % C)
    ad = w.s([t2], 'simprd', '( %s -> %s )' % (C, AD))
    cr = w.s([t1], 'simprd', '( %s -> c e. RR )' % C)
    ac = sc([], 'simpr', AC)
    M = 'if ( d <_ c , c , d )'
    Cdc = '( d e. RR /\\ c e. RR )'
    P1 = '( d <_ x -> ph )'; P2 = '( c <_ x -> ps )'
    D = '( ( ( %s /\\ x e. RR ) /\\ ( %s /\\ %s ) ) /\\ %s <_ x )' % (Cdc, P1, P2, M)
    sD = S_(w, D)
    dr0 = w.s([], 'simpl', '( %s -> d e. RR )' % Cdc); cr0 = w.s([], 'simpr', '( %s -> c e. RR )' % Cdc)
    dr = lift(w, dr0, D); cr = lift(w, cr0, D)
    xr = sD([], 'simpllr' if False else 'x', 'x') if False else None
    xr = w.s([w.s([], 'simpl', '( %s -> ( ( %s /\\ x e. RR ) /\\ ( %s /\\ %s ) ) )' % (D, Cdc, P1, P2))], 'simpld', '( %s -> ( %s /\\ x e. RR ) )' % (D, Cdc))
    xr = sD([xr], 'simprd', 'x e. RR')
    pp = w.s([w.s([], 'simpl', '( %s -> ( ( %s /\\ x e. RR ) /\\ ( %s /\\ %s ) ) )' % (D, Cdc, P1, P2))], 'simprd', '( %s -> ( %s /\\ %s ) )' % (D, P1, P2))
    mx = sD([], 'simpr', '%s <_ x' % M)
    mr = sD([cr, dr], 'ifcld', '%s e. RR' % M)
    dm = ap(w, D, [dr, cr], 'max1', 'd <_ %s' % M)
    cm = ap(w, D, [dr, cr], 'max2', 'c <_ %s' % M)
    dx = sD([dr, mr, xr, dm, mx], 'letrd', 'd <_ x')
    cx = sD([cr, mr, xr, cm, mx], 'letrd', 'c <_ x')
    both = sD([sD([dx, sD([pp], 'simpld', P1)], 'mpd', 'ph'), sD([cx, sD([pp], 'simprd', P2)], 'mpd', 'ps')], 'jca', '( ph /\\ ps )')
    k1 = w.s([both], 'ex', '( ( ( %s /\\ x e. RR ) /\\ ( %s /\\ %s ) ) -> ( %s <_ x -> ( ph /\\ ps ) ) )' % (Cdc, P1, P2, M))
    k2 = w.s([k1], 'ex', '( ( %s /\\ x e. RR ) -> ( ( %s /\\ %s ) -> ( %s <_ x -> ( ph /\\ ps ) ) ) )' % (Cdc, P1, P2, M))
    k3 = w.s([k2], 'ralimdva', '( %s -> ( A. x e. RR ( %s /\\ %s ) -> A. x e. RR ( %s <_ x -> ( ph /\\ ps ) ) ) )' % (Cdc, P1, P2, M))
    dr = w.s([w.s([t2], 'simpld', '( %s -> ( %s /\\ d e. RR ) )' % (C, A0))], 'simprd', '( %s -> d e. RR )' % C)
    ad = w.s([t2], 'simprd', '( %s -> %s )' % (C, AD))
    cr = w.s([t1], 'simprd', '( %s -> c e. RR )' % C)
    ac = sc([], 'simpr', AC)
    r26 = sc([sc([ad, ac], 'jca', '( %s /\\ %s )' % (AD, AC)), sc([w.s([], 'r19.26', '( A. x e. RR ( %s /\\ %s ) <-> ( %s /\\ %s ) )' % (P1, P2, AD, AC))], 'a1i', '( A. x e. RR ( %s /\\ %s ) <-> ( %s /\\ %s ) )' % (P1, P2, AD, AC))],
             'mpbird', 'A. x e. RR ( %s /\\ %s )' % (P1, P2))
    al = sc([r26, sc([sc([dr, cr], 'jca', Cdc), k3], 'syl', '( A. x e. RR ( %s /\\ %s ) -> A. x e. RR ( %s <_ x -> ( ph /\\ ps ) ) )' % (P1, P2, M))], 'mpd', 'A. x e. RR ( %s <_ x -> ( ph /\\ ps ) )' % M)
    mr = sc([cr, dr], 'ifcld', '%s e. RR' % M)
    e = 'b = %s' % M
    c1 = w.s([], 'breq1', '( %s -> ( b <_ x <-> %s <_ x ) )' % (e, M))
    c2 = w.s([c1], 'imbi1d', '( %s -> ( ( b <_ x -> ( ph /\\ ps ) ) <-> ( %s <_ x -> ( ph /\\ ps ) ) ) )' % (e, M))
    c3 = w.s([c2], 'ralbidv', '( %s -> ( A. x e. RR ( b <_ x -> ( ph /\\ ps ) ) <-> A. x e. RR ( %s <_ x -> ( ph /\\ ps ) ) ) )' % (e, M))
    ev = sc([mr, al, c3], 'rspcedvd' if False else 'x', 'x') if False else None
    ev = sc([sc([mr, al], 'jca', '( %s e. RR /\\ A. x e. RR ( %s <_ x -> ( ph /\\ ps ) ) )' % (M, M)), w.s([c3], 'rspcev', '( ( %s e. RR /\\ A. x e. RR ( %s <_ x -> ( ph /\\ ps ) ) ) -> %s )' % (M, M, concl))], 'syl', concl)
    B = '( ( ( %s /\\ d e. RR ) /\\ %s ) /\\ c e. RR )' % (A0, AD)
    i1 = w.s([ev], 'ex', '( %s -> ( %s -> %s ) )' % (B, AC, concl))
    i2 = w.s([i1], 'rexlimdva', '( ( ( %s /\\ d e. RR ) /\\ %s ) -> ( %s -> %s ) )' % (A0, AD, EVB('ps', 'c'), concl))
    B2 = '( ( %s /\\ d e. RR ) /\\ %s )' % (A0, AD)
    i3 = w.s([lift(w, h2, B2), i2], 'mpd', '( %s -> %s )' % (B2, concl))
    i4 = w.s([i3], 'ex', '( ( %s /\\ d e. RR ) -> ( %s -> %s ) )' % (A0, AD, concl))
    i5 = w.s([i4], 'rexlimdva', '( %s -> ( %s -> %s ) )' % (A0, EVB('ph', 'd'), concl))
    w.qed([h1, i5], 'mpd', SB['t21evan'])
    return go(w)


if __name__ == '__main__':
    if not only or 't21evan' in only:
        gen_evan()


def ev_rlim(w, A0, F, lim, eps, epsr, exV, point, Q, logarg=False):
    """( A0 -> EVB(Q) ) from lim : ( A0 -> ( n e. RR+ |-> F ) ~~>r 0 ), eps : ( A0 -> EPS e. RR+ ) (text epsr),
    exV : ( A0 -> A. n e. RR+ F e. _V ); point(Cx, facts) -> step ( Cx -> Q ) where facts has
    'lt' : ( Cx -> F[n:=P] < EPS ), 'p' the point text, 'pp' : ( Cx -> P e. RR+ ), 'p1' : ( Cx -> 1 <_ P ),
    'xr', 'xp', 'x1' about x.  P = x, or log x when logarg (then 1 <_ log x)."""
    AB = 'E. y e. RR A. n e. RR+ ( y <_ n -> ( abs ` ( %s - 0 ) ) < %s )' % (F, epsr)
    r = w.s([exV, eps, lim], 'rlimi', '( %s -> %s )' % (A0, AB))
    AY = 'A. n e. RR+ ( y <_ n -> ( abs ` ( %s - 0 ) ) < %s )' % (F, epsr)
    Cy = '( ( %s /\\ y e. RR ) /\\ %s )' % (A0, AY)
    sy = S_(w, Cy)
    yr = sy([], 'simplr', 'y e. RR')
    one = sy([], '1red', '1 e. RR')
    M = 'if ( y <_ 1 , 1 , y )'
    mr = sy([one, yr], 'ifcld', '%s e. RR' % M)
    ym = ap(w, Cy, [yr, one], 'max1', 'y <_ %s' % M)
    m1 = ap(w, Cy, [yr, one], 'max2', '1 <_ %s' % M)
    B = '( exp ` %s )' % M if logarg else M
    br = sy([mr], 'reefcld', '%s e. RR' % B) if logarg else mr
    Cx = '( ( %s /\\ x e. RR ) /\\ %s <_ x )' % (Cy, B)
    sx = S_(w, Cx)
    Lx = lambda st: lift(w, st, Cx)
    xr = sx([], 'simplr', 'x e. RR'); bx = sx([], 'simpr', '%s <_ x' % B)
    if logarg:
        bp = Lx(sy([mr], 'rpefcld', '%s e. RR+' % B))
        xp = sx([xr, lin.linarith(w, Cx, [bx, sx([bp], 'rpgt0d', '0 < %s' % B)], '0 < x', leaves={'x': xr, B: Lx(br)})], 'elrpd', 'x e. RR+')
        lb = sx([bx, sx([bp, xp], 'logled', '( %s <_ x <-> ( log ` %s ) <_ ( log ` x ) )' % (B, B))], 'mpbid', '( log ` %s ) <_ ( log ` x )' % B)
        le = sx([Lx(mr), w.inst('relogef')], 'syl', '( log ` %s ) = %s' % (B, M))
        mlx = sx([sx([le], 'eqcomd', '%s = ( log ` %s )' % (M, B)), lb], 'eqbrtrd', '%s <_ ( log ` x )' % M)
        P = '( log ` x )'
        pr = sx([xp], 'relogcld', '%s e. RR' % P)
        yp_ = sx([Lx(yr), Lx(mr), pr, Lx(ym), mlx], 'letrd', 'y <_ %s' % P)
        p1 = sx([Lx(one), Lx(mr), pr, Lx(m1), mlx], 'letrd', '1 <_ %s' % P)
        pp = sx([pr, lin.linarith(w, Cx, [p1], '0 < %s' % P, leaves={P: pr})], 'elrpd', '%s e. RR+' % P)
        x1 = None
    else:
        P = 'x'
        yp_ = sx([Lx(yr), Lx(mr), xr, Lx(ym), bx], 'letrd', 'y <_ x')
        p1 = sx([Lx(one), Lx(mr), xr, Lx(m1), bx], 'letrd', '1 <_ x')
        pp = sx([xr, lin.linarith(w, Cx, [p1], '0 < x', leaves={'x': xr})], 'elrpd', 'x e. RR+')
        xp = pp
    body = '( y <_ n -> ( abs ` ( %s - 0 ) ) < %s )' % (F, epsr)
    cg, inst = w.wcongr(body, {'n': P}, 'n = %s' % P, {'n': w.s([], 'id', '( n = %s -> n = %s )' % (P, P))})
    FP = inst.split(' -> ( abs ` ( ', 1)[1].rsplit(' - 0 ) ) <', 1)[0]
    rs = sx([pp, Lx(sy([], 'simpr', AY)), w.s([cg], 'rspcv', '( %s e. RR+ -> ( %s -> %s ) )' % (P, AY, inst))], 'sylc', inst)
    ab = sx([yp_, rs], 'mpd', '( abs ` ( %s - 0 ) ) < %s' % (FP, epsr))
    facts = dict(ab=ab, FP=FP, p=P, pp=pp, p1=p1, xr=xr, xp=xp)
    q = point(Cx, facts)
    al = sy([w.s([q], 'ex', '( ( %s /\\ x e. RR ) -> ( %s <_ x -> %s ) )' % (Cy, B, Q))], 'ralrimiva', 'A. x e. RR ( %s <_ x -> %s )' % (B, Q))
    e = 'b = %s' % B
    c1 = w.s([], 'breq1', '( %s -> ( b <_ x <-> %s <_ x ) )' % (e, B))
    c2 = w.s([c1], 'imbi1d', '( %s -> ( ( b <_ x -> %s ) <-> ( %s <_ x -> %s ) ) )' % (e, Q, B, Q))
    c3 = w.s([c2], 'ralbidv', '( %s -> ( A. x e. RR ( b <_ x -> %s ) <-> A. x e. RR ( %s <_ x -> %s ) ) )' % (e, Q, B, Q))
    ev = sy([sy([br, al], 'jca', '( %s e. RR /\\ A. x e. RR ( %s <_ x -> %s ) )' % (B, B, Q)), w.s([c3], 'rspcev', '( ( %s e. RR /\\ A. x e. RR ( %s <_ x -> %s ) ) -> %s )' % (B, B, Q, EVB(Q)))], 'syl', EVB(Q))
    i1 = w.s([ev], 'ex', '( ( %s /\\ y e. RR ) -> ( %s -> %s ) )' % (A0, AY, EVB(Q)))
    i2 = w.s([i1], 'rexlimdva', '( %s -> ( %s -> %s ) )' % (A0, AB, EVB(Q)))
    return w.s([r, i2], 'mpd', '( %s -> %s )' % (A0, EVB(Q)))


def gen_evl2():
    w = W('t21evl2', 'Eventually ` A log ^ 2 x <_ B x ^ R ` for positive ` A , B , R ` (Lean ` eventually_log_pow_le ` at ` n = 2 ` ; ~ cxploglim2 ).')
    A0, concl = split_imp(SB['t21evl2'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    ap_, bp_, rp_ = u['A e. RR+'], u['B e. RR+'], u['R e. RR+']
    F = '( ( ( log ` n ) ^c 2 ) / ( n ^c R ) )'
    lim = ap(w, A0, [s([w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC'), rp_], 'cxploglim2', '( n e. RR+ |-> %s ) ~~>r 0' % F)
    EPS = '( B / A )'
    eps = s([bp_, ap_], 'rpdivcld', '%s e. RR+' % EPS)
    exV = s([w.s([w.s([], 'ovex', '( ( n e. RR+ ) -> %s e. _V )' % F) if False else w.s([w.s([], 'ovex', '%s e. _V' % F)], 'a1i', '( n e. RR+ -> %s e. _V )' % F)], 'rgen', 'A. n e. RR+ %s e. _V' % F)], 'a1i', 'A. n e. RR+ %s e. _V' % F)
    Q = '( A x. ( ( log ` x ) ^ 2 ) ) <_ ( B x. ( x ^c R ) )'

    def point(Cx, f):
        sx = S_(w, Cx)
        Lx = lambda st: lift(w, st, Cx)
        xp = f['xp']
        lx = sx([xp], 'relogcld', '( log ` x ) e. RR')
        l2c = ap(w, Cx, [sx([lx], 'recnd', '( log ` x ) e. CC'), sx([w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'cxpexp', '( ( log ` x ) ^c 2 ) = ( ( log ` x ) ^ 2 )')
        XR = '( x ^c R )'
        xrp = sx([xp, sx([Lx(rp_)], 'rpred', 'R e. RR')], 'rpcxpcld', '%s e. RR+' % XR)
        L2 = '( ( log ` x ) ^ 2 )'
        l2r = sx([lx], 'resqcld', '%s e. RR' % L2)
        FP = f['FP']
        fr = sx([sx([l2c, l2r], 'x', 'x') if False else sx([sx([l2c], 'eqcomd', '%s = ( ( log ` x ) ^c 2 )' % L2) if False else l2c, l2r], 'eqeltrd', '( ( log ` x ) ^c 2 ) e. RR'), xrp], 'rerpdivcld', '%s e. RR' % FP)
        s0 = sx([sx([fr], 'recnd', '%s e. CC' % FP)], 'subid1d', '( %s - 0 ) = %s' % (FP, FP))
        abl = sx([sx([s0], 'fveq2d', '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (FP, FP)), f['ab']], 'eqbrtrrd', '( abs ` %s ) < %s' % (FP, EPS))
        flt = sx([fr, sx([sx([fr], 'recnd', '%s e. CC' % FP)], 'abscld', '( abs ` %s ) e. RR' % FP), Lx(s([eps], 'rpred', '%s e. RR' % EPS)), sx([fr, w.inst('leabs')], 'syl', '%s <_ ( abs ` %s )' % (FP, FP)), abl], 'lelttrd', '%s < %s' % (FP, EPS))
        f2 = sx([sx([l2c], 'oveq1d', '%s = ( %s / %s )' % (FP, L2, XR)), flt], 'x', 'x') if False else None
        f2 = sx([sx([sx([l2c], 'oveq1d', '%s = ( %s / %s )' % (FP, L2, XR))], 'eqcomd', '( %s / %s ) = %s' % (L2, XR, FP)), flt], 'eqbrtrd', '( %s / %s ) < %s' % (L2, XR, EPS))
        f3 = sx([f2, sx([l2r, Lx(s([eps], 'rpred', '%s e. RR' % EPS)), xrp], 'ltdivmuld', '( ( %s / %s ) < %s <-> %s < ( %s x. %s ) )' % (L2, XR, EPS, L2, XR, EPS))], 'mpbid', '%s < ( %s x. %s )' % (L2, XR, EPS))
        # A L2 < A ( XR ( B / A ) ) = B XR
        f4 = sx([l2r, sx([sx([xrp], 'rpred', '%s e. RR' % XR), Lx(s([eps], 'rpred', '%s e. RR' % EPS))], 'remulcld', '( %s x. %s ) e. RR' % (XR, EPS)), Lx(ap_), f3], 'ltmul2dd', '( A x. %s ) < ( A x. ( %s x. %s ) )' % (L2, XR, EPS))
        ac = Lx(s([ap_], 'rpcnd', 'A e. CC')); bc = Lx(s([bp_], 'rpcnd', 'B e. CC')); an = Lx(s([ap_], 'rpne0d', 'A =/= 0')); xc = sx([xrp], 'rpcnd', '%s e. CC' % XR)
        e1 = sx([ac, xc, sx([bc, ac, an], 'divcld', '%s e. CC' % EPS)], 'mul12d', '( A x. ( %s x. %s ) ) = ( %s x. ( A x. %s ) )' % (XR, EPS, XR, EPS))
        e2 = sx([bc, ac, an], 'divcan2d', '( A x. %s ) = B' % EPS)
        e3 = sx([e1, sx([sx([e2], 'oveq2d', '( %s x. ( A x. %s ) ) = ( %s x. B )' % (XR, EPS, XR)), sx([xc, bc], 'mulcomd', '( %s x. B ) = ( B x. %s )' % (XR, XR))], 'eqtrd', '( %s x. ( A x. %s ) ) = ( B x. %s )' % (XR, EPS, XR))],
                'eqtrd', '( A x. ( %s x. %s ) ) = ( B x. %s )' % (XR, EPS, XR))
        return sx([sx([f4, e3], 'breqtrd', '( A x. %s ) < ( B x. %s )' % (L2, XR))], 'ltled', Q)
    fin = ev_rlim(w, A0, F, lim, eps, EPS, exV, point, Q)
    w.qed([fin], 'idi' if False else 'id', SB['t21evl2']) if False else w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21evl2']))
    return go(w)


if __name__ == '__main__':
    if not only or 't21evl2' in only:
        gen_evl2()


def gen_evll():
    w = W('t21evll', 'Eventually ` A log log x <_ log x ` (Lean ` eventually_loglog_le ` ; ~ cxploglim at ` log x ` ).')
    A0, concl = split_imp(SB['t21evll'])
    s = S_(w, A0)
    ap_ = s([], 'id', 'A e. RR+') if False else w.s([], 'id', '( %s -> A e. RR+ )' % A0)
    F = '( ( log ` n ) / ( n ^c 1 ) )'
    lim = s([s([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+'), w.inst('cxploglim')], 'syl', '( n e. RR+ |-> %s ) ~~>r 0' % F)
    EPS = '( 1 / A )'
    eps = s([ap_], 'rpreccld', '%s e. RR+' % EPS)
    exV = s([w.s([w.s([w.s([], 'ovex', '%s e. _V' % F)], 'a1i', '( n e. RR+ -> %s e. _V )' % F)], 'rgen', 'A. n e. RR+ %s e. _V' % F)], 'a1i', 'A. n e. RR+ %s e. _V' % F)
    Q = '( A x. ( log ` ( log ` x ) ) ) <_ ( log ` x )'

    def point(Cx, f):
        sx = S_(w, Cx)
        Lx = lambda st: lift(w, st, Cx)
        P = f['p']; pp = f['pp']
        pr = sx([pp], 'rpred', '%s e. RR' % P)
        LL = '( log ` %s )' % P
        llr = sx([pp], 'relogcld', '%s e. RR' % LL)
        p1c = sx([sx([pr], 'recnd', '%s e. CC' % P)], 'cxp1d', '( %s ^c 1 ) = %s' % (P, P))
        FP = f['FP']
        fe = sx([p1c], 'oveq2d', '%s = ( %s / %s )' % (FP, LL, P))
        fr = sx([fe, sx([llr, pp], 'rerpdivcld', '( %s / %s ) e. RR' % (LL, P))], 'eqeltrd', '%s e. RR' % FP)
        s0 = sx([sx([fr], 'recnd', '%s e. CC' % FP)], 'subid1d', '( %s - 0 ) = %s' % (FP, FP))
        abl = sx([sx([s0], 'fveq2d', '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (FP, FP)), f['ab']], 'eqbrtrrd', '( abs ` %s ) < %s' % (FP, EPS))
        epr = Lx(s([eps], 'rpred', '%s e. RR' % EPS))
        flt = sx([fr, sx([sx([fr], 'recnd', '%s e. CC' % FP)], 'abscld', '( abs ` %s ) e. RR' % FP), epr, sx([fr, w.inst('leabs')], 'syl', '%s <_ ( abs ` %s )' % (FP, FP)), abl], 'lelttrd', '%s < %s' % (FP, EPS))
        f2 = sx([sx([fe], 'eqcomd', '( %s / %s ) = %s' % (LL, P, FP)), flt], 'eqbrtrd', '( %s / %s ) < %s' % (LL, P, EPS))
        f3 = sx([f2, sx([llr, epr, pp], 'ltdivmuld', '( ( %s / %s ) < %s <-> %s < ( %s x. %s ) )' % (LL, P, EPS, LL, P, EPS))], 'mpbid', '%s < ( %s x. %s )' % (LL, P, EPS))
        f4 = sx([llr, sx([pr, epr], 'remulcld', '( %s x. %s ) e. RR' % (P, EPS)), Lx(ap_), f3], 'ltmul2dd', '( A x. %s ) < ( A x. ( %s x. %s ) )' % (LL, P, EPS))
        ac = Lx(s([ap_], 'rpcnd', 'A e. CC')); an = Lx(s([ap_], 'rpne0d', 'A =/= 0')); pc = sx([pr], 'recnd', '%s e. CC' % P)
        e1 = sx([ac, pc, sx([ac, an], 'reccld', '%s e. CC' % EPS)], 'mul12d', '( A x. ( %s x. %s ) ) = ( %s x. ( A x. %s ) )' % (P, EPS, P, EPS))
        e2 = sx([ac, an], 'recidd', '( A x. %s ) = 1' % EPS)
        e3 = sx([e1, sx([sx([e2], 'oveq2d', '( %s x. ( A x. %s ) ) = ( %s x. 1 )' % (P, EPS, P)), sx([pc], 'mulridd', '( %s x. 1 ) = %s' % (P, P))], 'eqtrd', '( %s x. ( A x. %s ) ) = %s' % (P, EPS, P))],
                'eqtrd', '( A x. ( %s x. %s ) ) = %s' % (P, EPS, P))
        return sx([sx([f4, e3], 'breqtrd', '( A x. %s ) < %s' % (LL, P))], 'ltled', Q)
    fin = ev_rlim(w, A0, F, lim, eps, EPS, exV, point, Q, logarg=True)
    w.lines.append('qed:%s:idi |- %s' % (fin, SB['t21evll']))
    return go(w)


if __name__ == '__main__':
    if not only or 't21evll' in only:
        gen_evll()


def gen_evlg():
    w = W('t21evlg', 'Eventually ` A <_ log x ` , ` A <_ log log x ` and ` A <_ ( log x ) ^ ( 9 / 2 ) ` (Lean ` eventually_le_loglog ` , ` eventually_le_log_rpow ` , ` tendsto_log_atTop ` ; threshold ` exp ( exp ( abs A + 1 ) ) ` ).')
    A0, concl = split_imp(SB['t21evlg'])
    s = S_(w, A0)
    ar = w.s([], 'id', '( %s -> A e. RR )' % A0)
    K = '( ( abs ` A ) + 1 )'
    kr = s([s([s([ar], 'recnd', 'A e. CC')], 'abscld', '( abs ` A ) e. RR'), s([], '1red', '1 e. RR')], 'readdcld', '%s e. RR' % K)
    k0 = lin.linarith(w, A0, [s([s([ar], 'recnd', 'A e. CC')], 'absge0d', '0 <_ ( abs ` A )')], '0 < %s' % K, leaves={'( abs ` A )': s([s([ar], 'recnd', 'A e. CC')], 'abscld', '( abs ` A ) e. RR')})
    kp = s([kr, k0], 'elrpd', '%s e. RR+' % K)
    EK = '( exp ` %s )' % K
    ekp = s([kr], 'rpefcld', '%s e. RR+' % EK)
    B = '( exp ` %s )' % EK
    bp = s([s([ekp], 'rpred', '%s e. RR' % EK)], 'rpefcld', '%s e. RR+' % B)
    Q = SB['t21evlg'].split('( b <_ x -> ', 1)[1][:-4]
    Cx = '( ( %s /\\ x e. RR ) /\\ %s <_ x )' % (A0, B)
    sx = S_(w, Cx)
    Lx = lambda st: lift(w, st, Cx)
    xr = sx([], 'simplr', 'x e. RR'); bx = sx([], 'simpr', '%s <_ x' % B)
    xp = sx([xr, lin.linarith(w, Cx, [bx, Lx(s([bp], 'rpgt0d', '0 < %s' % B))], '0 < x', leaves={'x': xr, B: Lx(s([bp], 'rpred', '%s e. RR' % B))})], 'elrpd', 'x e. RR+')
    LX_ = '( log ` x )'
    l1 = sx([bx, sx([Lx(bp), xp], 'logled', '( %s <_ x <-> ( log ` %s ) <_ %s )' % (B, B, LX_))], 'mpbid', '( log ` %s ) <_ %s' % (B, LX_))
    le = sx([Lx(s([ekp], 'rpred', '%s e. RR' % EK)), w.inst('relogef')], 'syl', '( log ` %s ) = %s' % (B, EK))
    ekl = sx([sx([le], 'eqcomd', '%s = ( log ` %s )' % (EK, B)), l1], 'eqbrtrd', '%s <_ %s' % (EK, LX_))
    gt = ap(w, Cx, [Lx(kp)], 'efgt1p', '( 1 + %s ) < %s' % (K, EK))
    lxr = sx([xp], 'relogcld', '%s e. RR' % LX_)
    ab = Lx(s([ar, w.inst('leabs')], 'syl', 'A <_ ( abs ` A )'))
    lv = {'A': Lx(ar), '( abs ` A )': Lx(s([s([ar], 'recnd', 'A e. CC')], 'abscld', '( abs ` A ) e. RR')), EK: Lx(s([ekp], 'rpred', '%s e. RR' % EK)), LX_: lxr}
    c1 = lin.linarith(w, Cx, [ab, gt, ekl], 'A <_ %s' % LX_, leaves=lv)
    lx1 = lin.linarith(w, Cx, [gt, ekl, Lx(s([s([ar], 'recnd', 'A e. CC')], 'absge0d', '0 <_ ( abs ` A )'))], '1 <_ %s' % LX_, leaves=lv)
    lxp = sx([lxr, lin.linarith(w, Cx, [lx1], '0 < %s' % LX_, leaves={LX_: lxr})], 'elrpd', '%s e. RR+' % LX_)
    l2 = sx([ekl, sx([Lx(ekp), lxp], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (EK, LX_, EK, LX_))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (EK, LX_))
    le2 = sx([Lx(kr), w.inst('relogef')], 'syl', '( log ` %s ) = %s' % (EK, K))
    kll = sx([sx([le2], 'eqcomd', '%s = ( log ` %s )' % (K, EK)), l2], 'eqbrtrd', '%s <_ ( log ` %s )' % (K, LX_))
    LL = '( log ` %s )' % LX_
    llr = sx([lxp], 'relogcld', '%s e. RR' % LL)
    lv[LL] = llr
    c2 = lin.linarith(w, Cx, [ab, kll], 'A <_ %s' % LL, leaves=lv)
    cp = sx([lxr, lx1, sx([], '1red', '1 e. RR'), sx([num.real(w, F92)], 'a1i', '%s e. RR' % F92), sx([num.le_lit(w, '1', F92)], 'a1i', '1 <_ %s' % F92)], 'cxplead', '( %s ^c 1 ) <_ ( %s ^c %s )' % (LX_, LX_, F92))
    c1x = sx([sx([lxr], 'recnd', '%s e. CC' % LX_)], 'cxp1d', '( %s ^c 1 ) = %s' % (LX_, LX_))
    P9 = '( %s ^c %s )' % (LX_, F92)
    lp9 = sx([sx([c1x], 'eqcomd', '%s = ( %s ^c 1 )' % (LX_, LX_)), cp], 'eqbrtrd', '%s <_ %s' % (LX_, P9))
    p9r = sx([lxp, sx([num.real(w, F92)], 'a1i', '%s e. RR' % F92)], 'rpcxpcld', '%s e. RR+' % P9)
    c3 = sx([Lx(ar), lxr, sx([p9r], 'rpred', '%s e. RR' % P9), c1, lp9], 'letrd', 'A <_ %s' % P9)
    q = sx([c1, c2, c3], '3jca', Q)
    al = s([w.s([q], 'ex', '( ( %s /\\ x e. RR ) -> ( %s <_ x -> %s ) )' % (A0, B, Q))], 'ralrimiva', 'A. x e. RR ( %s <_ x -> %s )' % (B, Q))
    e = 'b = %s' % B
    c1_ = w.s([], 'breq1', '( %s -> ( b <_ x <-> %s <_ x ) )' % (e, B))
    c2_ = w.s([c1_], 'imbi1d', '( %s -> ( ( b <_ x -> %s ) <-> ( %s <_ x -> %s ) ) )' % (e, Q, B, Q))
    c3_ = w.s([c2_], 'ralbidv', '( %s -> ( A. x e. RR ( b <_ x -> %s ) <-> A. x e. RR ( %s <_ x -> %s ) ) )' % (e, Q, B, Q))
    ev = s([s([s([bp], 'rpred', '%s e. RR' % B), al], 'jca', '( %s e. RR /\\ A. x e. RR ( %s <_ x -> %s ) )' % (B, B, Q)), w.s([c3_], 'rspcev', '( ( %s e. RR /\\ A. x e. RR ( %s <_ x -> %s ) ) -> %s )' % (B, B, Q, EVB(Q)))], 'syl', EVB(Q))
    w.lines.append('qed:%s:idi |- %s' % (ev, SB['t21evlg']))
    return go(w)


if __name__ == '__main__':
    if not only or 't21evlg' in only:
        gen_evlg()


def gen_evmo():
    w = W('t21evmo', 'An eventual statement implies every pointwise consequence eventually (Lean ` Filter.Eventually.mono ` ).')
    H = 'A. x e. RR ( ph -> ps )'
    i1 = w.s([w.s([], 'imim2', '( ( ph -> ps ) -> ( ( b <_ x -> ph ) -> ( b <_ x -> ps ) ) )')], 'ralimi', '( %s -> A. x e. RR ( ( b <_ x -> ph ) -> ( b <_ x -> ps ) ) )' % H)
    i2 = w.s([i1, w.s([], 'ralim', '( A. x e. RR ( ( b <_ x -> ph ) -> ( b <_ x -> ps ) ) -> ( A. x e. RR ( b <_ x -> ph ) -> A. x e. RR ( b <_ x -> ps ) ) )')], 'syl',
             '( %s -> ( A. x e. RR ( b <_ x -> ph ) -> A. x e. RR ( b <_ x -> ps ) ) )' % H)
    i3 = w.s([i2], 'adantr', '( ( %s /\\ b e. RR ) -> ( A. x e. RR ( b <_ x -> ph ) -> A. x e. RR ( b <_ x -> ps ) ) )' % H)
    w.qed([i3], 'reximdva', SB['t21evmo'])
    return go(w)


if __name__ == '__main__':
    if not only or 't21evmo' in only:
        gen_evmo()


def gen_thr():
    from mvlib import ringeq as ringeq_d
    import cl as _cl
    w = W('t21thr', 'The eight thresholds of ` theta_AP_T21 ` hold eventually (Lean ` hev ` ; ~ t21evl2 , ~ t21evll , ~ t21evlg , ~ t21evan , ~ t21evmo ).')
    A0, concl = split_imp(SB['t21thr'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    ep, kn, hr, rp_, ur, u1 = u['E e. RR+'], u['K e. NN0'], u['H e. RR'], u['R e. RR+'], u['U e. RR'], u['U < 1']
    L = '( log ` x )'; LL = '( log ` %s )' % L
    def l2b(a, r):
        return '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( x ^c %s ) )' % (a, L, r)
    def gb(a):
        return '( %s <_ %s /\\ %s <_ %s /\\ %s <_ ( %s ^c %s ) )' % (a, L, a, LL, a, L, F92)
    B1 = '( exp ` ; 1 0 ) <_ x'
    E10 = '( exp ` ; 1 0 )'
    e10r = s([s([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'reefcld', '%s e. RR' % E10)
    idr = s([w.s([w.s([w.s([], 'id', '( %s -> %s )' % (B1, B1))], 'a1i', '( x e. RR -> ( %s -> %s ) )' % (B1, B1))], 'rgen', 'A. x e. RR ( %s -> %s )' % (B1, B1))], 'a1i', 'A. x e. RR ( %s -> %s )' % (B1, B1))
    e = 'b = %s' % E10
    c1_ = w.s([], 'breq1', '( %s -> ( b <_ x <-> %s <_ x ) )' % (e, E10))
    c2_ = w.s([c1_], 'imbi1d', '( %s -> ( ( b <_ x -> %s ) <-> ( %s <_ x -> %s ) ) )' % (e, B1, E10, B1))
    c3_ = w.s([c2_], 'ralbidv', '( %s -> ( A. x e. RR ( b <_ x -> %s ) <-> A. x e. RR ( %s <_ x -> %s ) ) )' % (e, B1, E10, B1))
    ev1 = s([s([e10r, idr], 'jca', '( %s e. RR /\\ A. x e. RR ( %s -> %s ) )' % (E10, B1, B1)), w.s([c3_], 'rspcev', '( ( %s e. RR /\\ A. x e. RR ( %s <_ x -> %s ) ) -> %s )' % (E10, E10, B1, EVB(B1)))], 'syl', EVB(B1))
    def lit_rp(t, v):
        return s([num.rp(w, t)], 'a1i', '%s e. RR+' % t)
    ev2 = ap(w, A0, [lit_rp(C675, 0), ep, lit_rp(F2931800, 0)], 't21evl2', EVB(l2b(C675, F2931800)))
    ev3 = ap(w, A0, [lit_rp('; 8 1', 0), ep, lit_rp(F259900, 0)], 't21evl2', EVB(l2b('; 8 1', F259900)))
    ev4 = ap(w, A0, [lit_rp(N4320, 0), ep, lit_rp(F7900, 0)], 't21evl2', EVB(l2b(N4320, F7900)))
    er = s([ep], 'rpred', 'E e. RR')
    kr = s([kn], 'nn0red', 'K e. RR')
    k5 = s([s([s([w.s([], '5nn', '5 e. NN')], 'a1i', '5 e. NN'), kn], 'nnexpcld', '( 5 ^ K ) e. NN')], 'nnred', '( 5 ^ K ) e. RR')
    NUM5 = '( ( %s x. ( 5 ^ K ) ) x. H )' % N50112
    n5r = s([s([s([num.real(w, N50112)], 'a1i', '%s e. RR' % N50112), k5], 'remulcld', '( %s x. ( 5 ^ K ) ) e. RR' % N50112), hr], 'remulcld', '%s e. RR' % NUM5)
    A5 = '( %s / E )' % NUM5
    a5r = s([n5r, ep], 'rerpdivcld', '%s e. RR' % A5)
    K2 = '( K + 2 )'
    k2p = s([kr, lin.linarith(w, A0, [s([kn], 'nn0ge0d', '0 <_ K')], '0 < %s' % K2, leaves={'K': kr})], 'elrpd', '%s e. RR+' % K2) if False else None
    k2r = s([kr, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % K2)
    k2p = s([k2r, lin.linarith(w, A0, [s([kn], 'nn0ge0d', '0 <_ K')], '0 < %s' % K2, leaves={'K': kr})], 'elrpd', '%s e. RR+' % K2)
    CS = '( ; 5 0 x. %s )' % K2
    csp = s([lit_rp('; 5 0', 0), k2p], 'rpmulcld', '%s e. RR+' % CS)
    A6 = '( ; 1 8 x. %s )' % CS
    a6p = s([lit_rp('; 1 8', 0), csp], 'rpmulcld', '%s e. RR+' % A6)
    ev6 = ap(w, A0, [a6p], 't21evll', EVB('( %s x. %s ) <_ %s' % (A6, LL, L)))
    rr = s([rp_], 'rpred', 'R e. RR')
    A7 = '( R / %s )' % CS
    a7r = s([rr, csp], 'rerpdivcld', '%s e. RR' % A7)
    U1 = '( 1 - U )'
    u1p = s([s([s([], '1red', '1 e. RR'), ur], 'resubcld', '%s e. RR' % U1), lin.linarith(w, A0, [u1], '0 < %s' % U1, leaves={'U': ur})], 'elrpd', '%s e. RR+' % U1)
    A8 = '( R / %s )' % U1
    a8r = s([rr, u1p], 'rerpdivcld', '%s e. RR' % A8)
    A9 = '( ; 4 0 x. R )'
    a9r = s([s([num.real(w, '; 4 0')], 'a1i', '; 4 0 e. RR'), rr], 'remulcld', '%s e. RR' % A9)
    evs = [(ev1, B1), (ev2, l2b(C675, F2931800)), (ev3, l2b('; 8 1', F259900)), (ev4, l2b(N4320, F7900)), (ap(w, A0, [a5r], 't21evlg', EVB(gb(A5))), gb(A5)),
           (ev6, '( %s x. %s ) <_ %s' % (A6, LL, L)), (ap(w, A0, [a7r], 't21evlg', EVB(gb(A7))), gb(A7)), (ap(w, A0, [a8r], 't21evlg', EVB(gb(A8))), gb(A8)),
           (ap(w, A0, [a9r], 't21evlg', EVB(gb(A9))), gb(A9)), (ap(w, A0, [s([], '1red', '1 e. RR')], 't21evlg', EVB(gb('1'))), gb('1'))]
    acc, body = evs[0]
    for st_, b_ in evs[1:]:
        nb = '( %s /\\ %s )' % (body, b_)
        acc = ap(w, A0, [acc, st_], 't21evan', EVB(nb))
        body = nb
    RC = body
    Cx = '( %s /\\ x e. RR )' % A0
    D = '( %s /\\ %s )' % (Cx, RC)
    sD = S_(w, D)
    LD = lambda st: lift(w, st, D)
    rc = sD([], 'simpr', RC)
    parts = []
    cur = rc; cb = RC
    for _ in range(len(evs) - 1):
        l_, r_ = cb[2:-2].rsplit(' /\\ ', 1) if False else (None, None)
        break
    # peel the left-nested conjunction
    txts = [b_ for _, b_ in evs]
    steps = [None] * len(txts)
    cur = rc; cb = RC
    for i in range(len(txts) - 1, 0, -1):
        left = cb[2:len(cb) - len(txts[i]) - 6]
        steps[i] = sD([cur], 'simprd', txts[i])
        cur = sD([cur], 'simpld', left); cb = left
    steps[0] = cur
    xr = sD([], 'simplr' if False else 'x', 'x') if False else w.s([w.s([], 'simpl', '( %s -> %s )' % (D, Cx))], 'simprd', '( %s -> x e. RR )' % D)
    g1 = steps[9]
    l1 = sD([g1], 'simp1d', '1 <_ %s' % L)
    l0 = lin.linarith(w, D, [l1], '0 < %s' % L, leaves={L: None}) if False else None
    xp = None
    # x > 0 from exp 10 <_ x
    xpos = lin.linarith(w, D, [steps[0], LD(s([s([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'rpefcld', '%s e. RR+' % E10) and s([s([s([num.real(w, '; 1 0')], 'a1i', '; 1 0 e. RR')], 'rpefcld', '%s e. RR+' % E10)], 'rpgt0d', '0 < %s' % E10))],
                       '0 < x', leaves={'x': xr, E10: LD(e10r)})
    xp = sD([xr, xpos], 'elrpd', 'x e. RR+')
    lr = sD([xp], 'relogcld', '%s e. RR' % L)
    l0 = lin.linarith(w, D, [l1], '0 <_ %s' % L, leaves={L: lr})
    t1 = steps[0]; t2 = steps[1]; t4 = steps[3]
    lsq = sD([lr, lr, l0, l1], 'lemulge11d', '%s <_ ( %s x. %s )' % (L, L, L))
    sqv = sD([sD([lr], 'recnd', '%s e. CC' % L)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (L, L, L))
    lsq2 = sD([lsq, sD([sqv], 'eqcomd', '( %s x. %s ) = ( %s ^ 2 )' % (L, L, L))], 'breqtrd', '%s <_ ( %s ^ 2 )' % (L, L))
    XR3 = '( x ^c %s )' % F259900
    x3r = sD([xp, sD([num.real(w, F259900)], 'a1i', '%s e. RR' % F259900)], 'rpcxpcld', '%s e. RR+' % XR3)
    ex3 = sD([LD(er), sD([x3r], 'rpred', '%s e. RR' % XR3)], 'remulcld', '( E x. %s ) e. RR' % XR3)
    t3 = lin.linarith(w, D, [lsq2, steps[2]], '( ; 8 1 x. %s ) <_ ( E x. %s )' % (L, XR3), leaves={L: lr, '( %s ^ 2 )' % L: sD([lr], 'resqcld', '( %s ^ 2 ) e. RR' % L), '( E x. %s )' % XR3: ex3})
    # t5
    P9 = '( %s ^c %s )' % (L, F92)
    a5l = sD([steps[4]], 'simp3d', '%s <_ %s' % (A5, P9))
    lp = sD([lr, lin.linarith(w, D, [l1], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    p9r = sD([lp, sD([num.real(w, F92)], 'a1i', '%s e. RR' % F92)], 'rpcxpcld', '%s e. RR+' % P9)
    m5 = sD([LD(a5r), sD([p9r], 'rpred', '%s e. RR' % P9), LD(er), LD(s([ep], 'rpge0d', '0 <_ E')), a5l], 'lemul2ad', '( E x. %s ) <_ ( E x. %s )' % (A5, P9))
    d5 = sD([LD(s([n5r], 'recnd', '%s e. CC' % NUM5)), LD(s([ep], 'rpcnd', 'E e. CC')), LD(s([ep], 'rpne0d', 'E =/= 0'))], 'divcan2d', '( E x. %s ) = %s' % (A5, NUM5))
    t5 = sD([sD([d5], 'eqcomd', '%s = ( E x. %s )' % (NUM5, A5)), m5], 'eqbrtrd', '%s <_ ( E x. %s )' % (NUM5, P9))
    # t6, t7
    llr = sD([lp], 'relogcld', '%s e. RR' % LL)
    cl = _cl.Closure(w, D, {})
    for k_, st_ in (('K', LD(kr)), (LL, llr)):
        cl.leaf(k_, 'RR', st_); cl.atom(k_)
    CSLx = '( ; 5 0 x. ( %s x. %s ) )' % (K2, LL)
    r6 = ringeq_d(w, D, '( %s x. %s )' % (A6, LL), '( ; 1 8 x. %s )' % CSLx, cl)
    t6 = sD([sD([r6], 'eqcomd', '( ; 1 8 x. %s ) = ( %s x. %s )' % (CSLx, A6, LL)), steps[5]], 'eqbrtrd', '( ; 1 8 x. %s ) <_ %s' % (CSLx, L))
    a7l = sD([steps[6]], 'simp2d', '%s <_ %s' % (A7, LL))
    t7a = sD([a7l, sD([LD(rr), llr, LD(csp)], 'ledivmuld', '( %s <_ %s <-> R <_ ( %s x. %s ) )' % (A7, LL, CS, LL))], 'mpbid', 'R <_ ( %s x. %s )' % (CS, LL))
    r7 = ringeq_d(w, D, '( %s x. %s )' % (CS, LL), CSLx, cl)
    t7 = sD([t7a, r7], 'breqtrd', 'R <_ %s' % CSLx)
    a8l = sD([steps[7]], 'simp1d', '%s <_ %s' % (A8, L))
    t8a = sD([a8l, sD([LD(rr), lr, LD(u1p)], 'ledivmuld', '( %s <_ %s <-> R <_ ( %s x. %s ) )' % (A8, L, U1, L))], 'mpbid', 'R <_ ( %s x. %s )' % (U1, L))
    t8b = sD([steps[8]], 'simp1d', '%s <_ %s' % (A9, L))
    th = THR('x')
    parts = th
    g = sD([sD([t1, t2, t3], '3jca', '( %s /\\ %s /\\ %s )' % (B1, l2b(C675, F2931800), '( ; 8 1 x. %s ) <_ ( E x. %s )' % (L, XR3))),
            sD([t4, t5], 'jca', '( %s /\\ %s <_ ( E x. %s ) )' % (l2b(N4320, F7900), NUM5, P9)),
            sD([sD([t6, t7], 'jca', '( ( ; 1 8 x. %s ) <_ %s /\\ R <_ %s )' % (CSLx, L, CSLx)), sD([t8a, t8b], 'jca', '( R <_ ( %s x. %s ) /\\ %s <_ %s )' % (U1, L, A9, L))], 'jca',
               '( ( ( ; 1 8 x. %s ) <_ %s /\\ R <_ %s ) /\\ ( R <_ ( %s x. %s ) /\\ %s <_ %s ) )' % (CSLx, L, CSLx, U1, L, A9, L))], '3jca', th)
    im = w.s([g], 'ex', '( %s -> ( %s -> %s ) )' % (Cx, RC, th))
    al = s([im], 'ralrimiva', 'A. x e. RR ( %s -> %s )' % (RC, th))
    mo = s([al, w.inst('t21evmo')], 'syl', '( %s -> %s )' % (EVB(RC), EVB(th)))
    w.qed([acc, mo], 'mpd', SB['t21thr'])
    return go(w)


if __name__ == '__main__':
    if not only or 't21thr' in only:
        gen_thr()
