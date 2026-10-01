"""Sortie T21b: t21cor (theta_AP_T21 with the density constants as classes)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from c8lib import tsub

DBd = '( Base ` ( DChr ` d ) )'


def gen_cor():
    w = W('t21cor', 'T2.1 (Lean ` theta_AP_T21 ` ) with the constants of the two density inputs as classes: the pinned ` rho ` , ` nu ` (~ t21rv ), the zeta box (~ zrbox ), the thresholds (~ t21thr ), the exceptional sets (~ t21bf ) and the inequality at every point (~ t21pt ).')
    A0, concl = split_imp(SB['t21cor'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    LFm = 'A. m e. NN %s' % LFD_BODY('G', 'C', 'm')
    LGm = 'A. m e. NN %s' % LGD_BODY('H', 'P', 'B', 'K', 'm')
    gr, cr, g1, c1, c2, lfm = u['G e. RR'], u['C e. RR'], u['1 <_ G'], u['1 <_ C'], u['C <_ 2'], u[LFm]
    hr, pr, br_, kn, h1, p0, p72, b1, b54, lgm = u['H e. RR'], u['P e. RR'], u['B e. RR'], u['K e. NN0'], u['1 <_ H'], u['0 <_ P'], u['P <_ ( 7 / 2 )'], u['1 <_ B'], u['B <_ ( 5 / 4 )'], u[LGm]
    er, e0, e3 = u['E e. RR'], u['0 < E'], u['E < ( 1 / 3 )']
    RV = SB['t21rv'].split(' -> ', 1)[1][:-2]
    rv = ap(w, A0, [gr, g1, er, e0, e3], 't21rv', RV)
    rvu = unpack_step(w, A0, rv, RV)
    rpp = rvu['%s e. RR+' % RHO]; vpp = rvu['%s e. RR+' % VV]; v1 = rvu['1 <_ %s' % VV]
    EXZ = '( exp ` ( -u %s x. %s ) )' % (F9200, RHO)
    h3 = rvu['( %s x. ( G x. %s ) ) <_ E' % (N6912, EXZ)]; h4 = rvu['( ; 2 7 x. ( G x. %s ) ) <_ ( E x. %s )' % (E28R, VV)]
    ep = s([er, e0], 'elrpd', 'E e. RR+')
    # zeta box, renamed u -> t
    ZB = lambda uu: '( ( ( 1 / 2 ) <_ %s /\\ %s < 1 ) /\\ %s )' % (uu, uu, ZETA(uu, VV))
    zb = s([vpp, w.inst('zrbox')], 'syl', 'E. u e. RR %s' % ZB('u'))
    cz, _ = w.wcongr(ZB('u'), {'u': 't'}, 'u = t', {'u': w.s([], 'id', '( u = t -> u = t )')})
    zbt = s([zb, s([w.s([cz], 'cbvrexvw', '( E. u e. RR %s <-> E. t e. RR %s )' % (ZB('u'), ZB('t')))], 'a1i', '( E. u e. RR %s <-> E. t e. RR %s )' % (ZB('u'), ZB('t')))], 'mpbid', 'E. t e. RR %s' % ZB('t'))
    Ct = '( ( %s /\\ t e. RR ) /\\ %s )' % (A0, ZB('t'))
    st = S_(w, Ct)
    Lt = lambda x_: lift(w, x_, Ct)
    tr = st([], 'simplr', 't e. RR')
    zbb = st([], 'simpr', ZB('t'))
    t1 = st([st([zbb], 'simpld', '( ( 1 / 2 ) <_ t /\\ t < 1 )')], 'simprd', 't < 1')
    zeta = st([zbb], 'simprd', ZETA('t', VV))
    THRx = tsub(THR('x'), {'R': RHO, 'U': 't'})
    EVT = 'E. b e. RR A. x e. RR ( b <_ x -> %s )' % THRx
    thr = ap(w, Ct, [Lt(ep), Lt(kn), Lt(hr), Lt(rpp), tr, t1], 't21thr', EVT)
    # ---- fixed b
    AXT = 'A. x e. RR ( b <_ x -> %s )' % THRx
    Cb = '( ( %s /\\ b e. RR ) /\\ %s )' % (Ct, AXT)
    sb = S_(w, Cb)
    Lb = lambda x_: lift(w, x_, Cb)
    bR = sb([], 'simplr', 'b e. RR')
    axt = sb([], 'simpr', AXT)
    # A. x ( b <_ x -> ( t1 /\ t8b ) )
    T1 = '( exp ` ; 1 0 ) <_ x'; T8 = '( ; 4 0 x. %s ) <_ ( log ` x )' % RHO
    idq = w.s([], 'id', '( %s -> %s )' % (THRx, THRx))
    qq = unpack_step(w, THRx, idq, THRx)
    tq = w.s([qq[T1], qq[T8]], 'jca', '( %s -> ( %s /\\ %s ) )' % (THRx, T1, T8))
    im = w.s([tq, w.s([], 'imim2', '( ( %s -> ( %s /\\ %s ) ) -> ( ( b <_ x -> %s ) -> ( b <_ x -> ( %s /\\ %s ) ) ) )' % (THRx, T1, T8, THRx, T1, T8))], 'ax-mp',
             '( ( b <_ x -> %s ) -> ( b <_ x -> ( %s /\\ %s ) ) )' % (THRx, T1, T8))
    ax2 = sb([axt, w.s([im], 'ralimi', '( %s -> A. x e. RR ( b <_ x -> ( %s /\\ %s ) ) )' % (AXT, T1, T8))], 'syl', 'A. x e. RR ( b <_ x -> ( %s /\\ %s ) )' % (T1, T8))
    FFr = tsub(FF, {'R': RHO, 'V': VV})
    D0r = tsub(D0, {'R': RHO, 'V': VV})
    J = '( |^ ` %s )' % D0r
    BF = tsub(split_imp(SB['t21bf'])[1], {'R': RHO, 'V': VV})
    bf = ap(w, Cb, [Lb(rpp), Lb(s([vpp], 'rpred', '%s e. RR' % VV)), Lb(v1), bR, ax2], 't21bf', BF)
    jn0 = sb([bf], 'simp1d', '%s e. NN0' % J)
    fmap = sb([bf], 'simp2d', '%s : NN0 --> ( ~P NN i^i Fin )' % FFr)
    cards = sb([bf], 'simp3d', BF.rsplit(' /\\ ( A. l', 1)[1].join(['( A. l', '']).rstrip()[:-2] if False else '( A. l e. NN0 ( # ` ( %s ` l ) ) <_ %s /\\ A. l e. NN0 A. i e. ( %s ` l ) 2 <_ i )' % (FFr, J, FFr))
    # ---- the point
    L191 = '( l ^c %s )' % F191; L709 = '( l ^c %s )' % F709
    HYP = '( ( b <_ l /\\ ( a gcd d ) = 1 ) /\\ ( d <_ %s /\\ ( d x. %s ) <_ z /\\ z <_ l ) /\\ A. i e. ( %s ` l ) -. i || d )' % (L191, L709, FFr)
    C4 = '( ( %s /\\ ( l e. NN0 /\\ d e. NN ) ) /\\ ( a e. ZZ /\\ z e. RR ) )' % Cb
    C5 = '( %s /\\ %s )' % (C4, HYP)
    s5 = S_(w, C5)
    L5 = lambda x_: lift(w, x_, C5)
    ln0 = w.s([], 'simp-4l' if False else 'simpl', '( %s -> %s )' % (C5, C4))
    lnd = w.s([w.s([ln0], 'simpld', '( %s -> ( %s /\\ ( l e. NN0 /\\ d e. NN ) ) )' % (C5, Cb))], 'simprd', '( %s -> ( l e. NN0 /\\ d e. NN ) )' % C5)
    azr = w.s([ln0], 'simprd', '( %s -> ( a e. ZZ /\\ z e. RR ) )' % C5)
    l0 = s5([lnd], 'simpld', 'l e. NN0'); dn = s5([lnd], 'simprd', 'd e. NN')
    az = s5([azr], 'simpld', 'a e. ZZ'); zr = s5([azr], 'simprd', 'z e. RR')
    hy = s5([], 'simpr', HYP)
    hu = unpack_step(w, C5, hy, HYP)
    bl = hu['b <_ l']
    lr = s5([l0], 'nn0red', 'l e. RR')
    # THR at l
    body = '( b <_ x -> %s )' % THRx
    cg, inst = w.wcongr(body, {'x': 'l'}, 'x = l', {'x': w.s([], 'id', '( x = l -> x = l )')})
    THRl = inst.split(' -> ', 1)[1][:-2]
    thl = s5([bl, s5([lr, L5(axt), w.s([cg], 'rspcv', '( l e. RR -> ( %s -> %s ) )' % (AXT, inst))], 'sylc', inst)], 'mpd', THRl)
    thu = unpack_step(w, C5, thl, THRl)
    # f ` l = BAD
    BADl = tsub(BAD(L191, TAUl, 'V'), {'R': RHO, 'V': VV})
    IFV = 'if ( b <_ l , %s , (/) )' % BADl
    FZ = '( 2 ... ( |_ ` %s ) )' % L191
    bex = w.s([w.s([], 'ovex', '%s e. _V' % FZ)], 'rabex', '%s e. _V' % BADl)
    ifx = w.s([bex, w.s([], '0ex', '(/) e. _V')], 'ifex', '%s e. _V' % IFV)
    BODYk = FFr[len('( k e. NN0 |-> '):-2]
    ck, fval = w.congr(BODYk, {'k': 'l'}, 'k = l', {'k': w.s([], 'id', '( k = l -> k = l )')})
    assert fval == IFV, (fval[:200], IFV[:200])
    fv = w.s([w.s([], 'eqid', '%s = %s' % (FFr, FFr)), ck, l0, s5([ifx], 'a1i', '%s e. _V' % IFV)], 'fvmptd3', '( %s -> ( %s ` l ) = %s )' % (C5, FFr, IFV))
    ift = s5([bl, w.s([], 'iftrue', '( b <_ l -> %s = %s )' % (IFV, BADl))], 'syl', '%s = %s' % (IFV, BADl))
    fvb = s5([fv, ift], 'eqtrd', '( %s ` l ) = %s' % (FFr, BADl))
    HB0 = 'A. i e. ( %s ` l ) -. i || d' % FFr
    HB1 = 'A. i e. %s -. i || d' % BADl
    hb = s5([hu[HB0], s5([fvb, w.s([], 'raleq', '( ( %s ` l ) = %s -> ( %s <-> %s ) )' % (FFr, BADl, HB0, HB1))], 'syl', '( %s <-> %s )' % (HB0, HB1))], 'mpbid', HB1)
    # the density bodies at d
    def at_d(allst, bodym):
        cg_, bd = w.wcongr(bodym, {'m': 'd'}, 'm = d', {'m': w.s([], 'id', '( m = d -> m = d )')})
        return s5([dn, L5(allst), w.s([cg_], 'rspcv', '( d e. NN -> ( A. m e. NN %s -> %s ) )' % (bodym, bd))], 'sylc', bd), bd
    lfd, lfdt = at_d(lfm, LFD_BODY('G', 'C', 'm'))
    lgd, lgdt = at_d(lgm, LGD_BODY('H', 'P', 'B', 'K', 'm'))
    assert lfdt == LFD_BODY('G', 'C', 'd') and lgdt == LGD_BODY('H', 'P', 'B', 'K', 'd'), (lfdt[:80],)
    PT = tsub(SB['t21pt'], {'N': 'd', 'X': 'l', 'Y': 'z', 'A': 'a', 'U': 't', 'R': RHO, 'V': VV})
    pa, pc = split_imp(PT)
    pc_goal = pc
    thv = [thu[k] for k in _thr_leaves('l')]
    leaves = [L5(er), L5(e0), L5(gr), L5(g1), L5(cr), L5(c1), L5(c2), lfd, L5(hr), L5(h1), L5(pr), L5(p0), L5(p72), L5(br_), L5(b1), L5(b54), L5(kn), lgd,
              L5(rpp), L5(vpp), L5(h3), L5(h4), lr] + thv + [L5(tr), L5(zeta), dn, az, hu['( a gcd d ) = 1'], zr, hu['d <_ %s' % L191], hu['( d x. %s ) <_ z' % L709], hu['z <_ l'], hb]
    pt = ap(w, C5, leaves, 't21pt', pc)
    i1 = w.s([pt], 'ex', '( %s -> ( %s -> %s ) )' % (C4, HYP, pc))
    MAIN_in = 'A. a e. ZZ A. z e. RR ( %s -> %s )' % (HYP, pc)
    i2 = w.s([i1], 'ralrimivva', '( ( %s /\\ ( l e. NN0 /\\ d e. NN ) ) -> %s )' % (Cb, MAIN_in))
    MAIN = 'A. l e. NN0 A. d e. NN %s' % MAIN_in
    i3 = w.s([i2], 'ralrimivva', '( %s -> %s )' % (Cb, MAIN))
    # package
    GB = GOAL()
    Pj = GB[len('E. j e. NN0 E. b e. RR E. f '):]
    Pf = tsub(Pj, {'j': J})
    PF = Pf.replace(' f ', ' %s ' % FFr).replace('( f ` l )', '( %s ` l )' % FFr).replace('f : NN0', '%s : NN0' % FFr)
    assert ' f ' not in PF
    pP = sb([fmap, cards, i3], '3jca', PF)
    fpart = 'f : NN0 --> ( ~P NN i^i Fin )'
    PNt = '( ~P NN i^i Fin )'
    CARD = lambda f_, j_: '( A. l e. NN0 ( # ` ( %s ` l ) ) <_ %s /\\ A. l e. NN0 A. i e. ( %s ` l ) 2 <_ i )' % (f_, j_, f_, )
    MAINf = lambda f_: 'A. l e. NN0 A. d e. NN A. a e. ZZ A. z e. RR ( ( ( b <_ l /\\ ( a gcd d ) = 1 ) /\\ ( d <_ %s /\\ ( d x. %s ) <_ z /\\ z <_ l ) /\\ A. i e. ( %s ` l ) -. i || d ) -> %s )' % (L191, L709, f_, pc_goal)
    assert Pf == '( %s /\\ %s /\\ %s )' % (fpart, CARD('f', J), MAINf('f')), Pf[:300]
    eqf = 'f = %s' % FFr
    idf = w.s([], 'id', '( %s -> %s )' % (eqf, eqf))
    k1 = w.s([], 'feq1', '( %s -> ( %s <-> %s : NN0 --> %s ) )' % (eqf, fpart, FFr, PNt))
    k2, _ = w.wcongr(CARD('f', J), {'f': FFr}, eqf, {'f': idf})
    k3, _ = w.wcongr(MAINf('f'), {'f': FFr}, eqf, {'f': idf})
    cgf = w.s([k1, k2, k3], '3anbi123d', '( %s -> ( %s <-> %s ) )' % (eqf, Pf, PF))
    mex = w.s([w.s([], 'nn0ex', 'NN0 e. _V')], 'mptex', '%s e. _V' % FFr)
    EF_ = 'E. f %s' % Pf
    ef = sb([pP, w.s([mex, cgf], 'spcev', '( %s -> %s )' % (PF, EF_))], 'syl', EF_)
    ja = sb([jn0, ef], 'jca', '( %s e. NN0 /\\ %s )' % (J, EF_))
    r1 = w.s([ja], 'ex', '( ( %s /\\ b e. RR ) -> ( %s -> ( %s e. NN0 /\\ %s ) ) )' % (Ct, AXT, J, EF_))
    r2 = w.s([r1], 'reximdva', '( %s -> ( %s -> E. b e. RR ( %s e. NN0 /\\ %s ) ) )' % (Ct, EVT, J, EF_))
    r3 = st([thr, r2], 'mpd', 'E. b e. RR ( %s e. NN0 /\\ %s )' % (J, EF_))
    r4 = st([r3, w.s([], 'r19.42v', '( E. b e. RR ( %s e. NN0 /\\ %s ) <-> ( %s e. NN0 /\\ E. b e. RR %s ) )' % (J, EF_, J, EF_))], 'sylib', '( %s e. NN0 /\\ E. b e. RR %s )' % (J, EF_))
    EB = 'E. b e. RR E. f %s' % Pj
    eqj = 'j = %s' % J
    idj = w.s([], 'id', '( %s -> %s )' % (eqj, eqj))
    j2, _ = w.wcongr(CARD('f', 'j'), {'j': J}, eqj, {'j': idj})
    j3 = w.s([j2], '3anbi2d', '( %s -> ( %s <-> %s ) )' % (eqj, Pj, Pf))
    j4 = w.s([j3], 'exbidv', '( %s -> ( E. f %s <-> E. f %s ) )' % (eqj, Pj, Pf))
    cgj = w.s([j4], 'rexbidv', '( %s -> ( %s <-> E. b e. RR E. f %s ) )' % (eqj, EB, Pf))
    r5 = st([r4, w.s([cgj], 'rspcev', '( ( %s e. NN0 /\\ E. b e. RR %s ) -> %s )' % (J, EF_, GB))], 'syl', GB)
    r6 = w.s([r5], 'ex', '( ( %s /\\ t e. RR ) -> ( %s -> %s ) )' % (A0, ZB('t'), GB))
    r7 = w.s([r6], 'rexlimdva', '( %s -> ( E. t e. RR %s -> %s ) )' % (A0, ZB('t'), GB))
    w.qed([zbt, r7], 'mpd', SB['t21cor'])
    return go(w)


def _thr_leaves(X):
    lx = '( log ` %s )' % X
    csl = '( ; 5 0 x. ( ( K + 2 ) x. ( log ` %s ) ) )' % lx
    return ['( exp ` ; 1 0 ) <_ %s' % X,
            '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( %s ^c %s ) )' % (C675, lx, X, F2931800),
            '( ; 8 1 x. %s ) <_ ( E x. ( %s ^c %s ) )' % (lx, X, F259900),
            '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( %s ^c %s ) )' % (N4320, lx, X, F7900),
            '( ( %s x. ( 5 ^ K ) ) x. H ) <_ ( E x. ( %s ^c %s ) )' % (N50112, lx, F92),
            '( ; 1 8 x. %s ) <_ %s' % (csl, lx),
            '%s <_ %s' % (RHO, csl),
            '%s <_ ( ( 1 - t ) x. %s )' % (RHO, lx),
            '( ; 4 0 x. %s ) <_ %s' % (RHO, lx)]


if __name__ == '__main__':
    gen_cor()
