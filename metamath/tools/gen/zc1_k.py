"""Sortie ZC1: zeros in the right half-plane have order in NN (hp0ordnn); the zero set of a box is finite
(zffin, Lean finite_LZerosBox + one_le_analyticOrderNatAt_of_mem_zeroFinset); monotonicity (zcmono, Lean zeroCountBox_mono)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
from c9_b import decode
from c10_f import crfacts, clo
import zc1_i
from zc1_i import encode
import lin
lin.FASTPATH = True

H2 = '( %s /\\ ( F ` 2 ) =/= 0 )' % HOLF('F', HP0)
S['hp0ordnn'] = '( ( ( %s /\\ P e. %s ) /\\ ( F ` P ) = 0 ) -> ( F holord P ) e. NN )' % (H2, HP0)
ZFA = ZF('F', 'A', 'T')
S['zffin'] = '( ( %s /\\ ( ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ T e. RR ) ) -> ( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN ) )' % (H2, ZFA, ZFA)
S['zcmono'] = '( ( %s /\\ ( ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ ( B e. RR /\\ A <_ B ) /\\ T e. RR ) ) -> %s <_ %s )' % (H2, ZC('F', 'B', 'T'), ZC('F', 'A', 'T'))


def hp_mem(w, ante, xst, rpos):
    """( ante -> x e. HP0 ) from xst : ( ante -> x e. CC ) and rpos : ( ante -> 0 < ( Re ` x ) ), x read off rpos"""
    x = rpos.split('Re ` ', 1)[1] if False else None


def gen_hp0ordnn():
    w = W('hp0ordnn', 'A zero in the right half-plane of ` F ` holomorphic there with ` F ( 2 ) =/= 0 ` has order in ` NN ` (Lean ` one_le_analyticOrderNatAt_of_mem_zeroFinset ` ; ~ hp0ordf ).')
    A0, GC = ante_of(S['hp0ordnn'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    x1 = s([], 'simpl', '( %s /\\ P e. %s )' % (H2, HP0)); fp0 = s([], 'simpr', '( F ` P ) = 0')
    ph = s([x1, w.inst('simpr')], 'syl', 'P e. %s' % HP0)
    hf = s([x1, w.inst('hp0ordf')], 'syl', ante_of(S['hp0ordf'])[1])
    ON = '( F holord P )'
    n0 = s([hf, w.inst('simpl')], 'syl', '%s e. NN0' % ON)
    EXG = top_and(ante_of(S['hp0ordf'])[1])[1]
    INNER = EXG[len('E. g '):]
    AG = '( %s /\\ %s )' % (A0, INNER)
    sg = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (AG, f))
    I1, I2, I3 = top_and(INNER)
    gh = sg([sg([], 'simpr', INNER), w.inst('simp1')], 'syl', I1); gp = sg([sg([], 'simpr', INNER), w.inst('simp2')], 'syl', I2); gfac = sg([sg([], 'simpr', INNER), w.inst('simp3')], 'syl', I3)
    BZ = I3[len('A. z e. %s ' % HP0):]
    BP = tsub(BZ, {'z': 'P'})
    eqz = w.wcongr(BZ, {'z': 'P'}, 'z = P', {'z': w.s([], 'id', '( z = P -> z = P )')})[0]
    fpP = sg([eqz, gfac, lift(w, ph, AG)], 'rspcdva', BP)
    A00 = '( %s /\\ %s = 0 )' % (AG, ON)
    s0 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A00, f))
    pcc = s([s([ph, s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( P e. %s <-> ( P e. CC /\\ 0 < ( Re ` P ) ) )' % HP0)], 'mpbid',
                '( P e. CC /\\ 0 < ( Re ` P ) )'), w.inst('simpl')], 'syl', 'P e. CC')
    e1 = s0([s0([], 'simpr', '%s = 0' % ON)], 'oveq2d', '( ( P - P ) ^ %s ) = ( ( P - P ) ^ 0 )' % ON)
    pp = s0([lift(w, pcc, A00), lift(w, pcc, A00)], 'subcld', '( P - P ) e. CC')
    e2 = s0([e1, s0([pp], 'exp0d', '( ( P - P ) ^ 0 ) = 1')], 'eqtrd', '( ( P - P ) ^ %s ) = 1' % ON)
    gpc = s0([lift(w, sg([sg([sg([gh, w.inst('simpl')], 'syl', 'g e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'g : %s --> CC' % HP0), lift(w, ph, AG)], 'ffvelcdmd', '( g ` P ) e. CC'), A00)],
             'id' if False else 'mullidd', '( 1 x. ( g ` P ) ) = ( g ` P )')
    fg = s0([lift(w, fpP, A00), s0([s0([e2], 'oveq1d', '( ( ( P - P ) ^ %s ) x. ( g ` P ) ) = ( 1 x. ( g ` P ) )' % ON), gpc], 'eqtrd', '( ( ( P - P ) ^ %s ) x. ( g ` P ) ) = ( g ` P )' % ON)],
            'eqtrd', '( F ` P ) = ( g ` P )')
    fne = s0([fg, lift(w, gp, A00)], 'eqnetrd', '( F ` P ) =/= 0')
    nfz = s0([fne], 'neneqd', '-. ( F ` P ) = 0')
    ne = sg([w.s([lift(w, fp0, A00), nfz], 'pm2.65da', '( %s -> -. %s = 0 )' % (AG, ON)) if False else None], 'x', 'x') if False else None
    pm = w.s([w.s([lift(w, fp0, A00)], 'x', 'x') if False else lift(w, fp0, A00), nfz], 'pm2.65da', '( %s -> -. %s = 0 )' % (AG, ON))
    nn = sg([sg([lift(w, n0, AG), sg([pm], 'neqned', '%s =/= 0' % ON)], 'jca', '( %s e. NN0 /\\ %s =/= 0 )' % (ON, ON)), w.s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (ON, ON, ON))],
            'sylibr', '%s e. NN' % ON)
    el = s([w.s([nn], 'ex', '( %s -> ( %s -> %s e. NN ) )' % (A0, INNER, ON))], 'exlimdv', '( %s -> %s e. NN )' % (EXG, ON))
    w.qed([s([hf, w.inst('simpr')], 'syl', EXG), el], 'mpd', S['hp0ordnn'])
    return run8(w)


def gen_zffin():
    w = W('zffin', 'The zeros off ` 1 ` of ` F ` (holomorphic on the right half-plane, ` F ( 2 ) =/= 0 ` ) in the box ` [ A , 1 ] x. [ - T , T ] ` , ` 0 < A <_ 1 ` , are finitely many, each of order in ` NN ` (Lean ` finite_LZerosBox ` , ` one_le_analyticOrderNatAt_of_mem_zeroFinset ` ; ~ holzfi on ` [ A , 2 ] x. [ - abs T , abs T ] ` ).')
    A0, GC = ante_of(S['zffin'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    h2 = s([], 'simpl', H2); hol = s([h2, w.inst('simpl')], 'syl', HOLF('F', HP0)); f2 = s([h2, w.inst('simpr')], 'syl', '( F ` 2 ) =/= 0')
    X2 = top_and(A0)[1]
    x2 = s([], 'simpr', X2)
    a3 = s([x2, w.inst('simpl')], 'syl', '( A e. RR /\\ 0 < A /\\ A <_ 1 )'); tr = s([x2, w.inst('simpr')], 'syl', 'T e. RR')
    ar = s([a3, w.inst('simp1')], 'syl', 'A e. RR'); a0 = s([a3, w.inst('simp2')], 'syl', '0 < A'); a1 = s([a3, w.inst('simp3')], 'syl', 'A <_ 1')
    AT = '( abs ` T )'
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '%s e. RR' % AT)
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ %s' % AT)
    lt = s([tr], 'leabsd', 'T <_ %s' % AT)
    nt = s([s([s([tr], 'renegcld', '-u T e. RR')], 'leabsd', '-u T <_ ( abs ` -u T )'), s([s([tr], 'recnd', 'T e. CC')], 'absnegd', '( abs ` -u T ) = %s' % AT)], 'breqtrd', '-u T <_ %s' % AT)
    RA, RB = '( A + ( _i x. -u %s ) )' % AT, '( 2 + ( _i x. %s ) )' % AT
    ac, reA, imA = crfacts(w, A0, 'A', '-u %s' % AT, ar, s([atr], 'renegcld', '-u %s e. RR' % AT))
    bc, reB, imB = crfacts(w, A0, '2', AT, numst(w, A0, '2', 'RR'), atr)
    BA, BB = '( A + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
    bac, rbA, ibA = crfacts(w, A0, 'A', '-u T', ar, s([tr], 'renegcld', '-u T e. RR'))
    bbc, rbB, ibB = crfacts(w, A0, '1', 'T', numst(w, A0, '1', 'RR'), tr)
    lv = {'A': ar, 'T': tr, AT: atr}
    for e, st in (('( Re ` %s )' % RA, ac), ('( Im ` %s )' % RA, ac), ('( Re ` %s )' % RB, bc), ('( Im ` %s )' % RB, bc)):
        lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hy = [reA, imA, reB, imB, a0, a1, ag0, lt, nt]
    geo = s([lin8(w, A0, hy, '( Re ` %s ) <_ ( Re ` %s )' % (RA, RB), lv), lin8(w, A0, hy, '( Im ` %s ) <_ ( Im ` %s )' % (RA, RB), lv)], 'jca', GEOG(RA, RB))
    M_ = '( A / 2 )'
    mr = s([s([ar, a0], 'elrpd', 'A e. RR+'), w.inst('rphalfcld')], 'syl', '%s e. RR+' % M_)
    MM = '( %s + ( _i x. %s ) )' % (M_, M_)
    A2, B2 = '( %s - %s )' % (RA, MM), '( %s + %s )' % (RB, MM)
    mmc = s([s([mr], 'rpcnd', '%s e. CC' % M_), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([mr], 'rpcnd', '%s e. CC' % M_)], 'mulcld', '( _i x. %s ) e. CC' % M_)], 'addcld', '%s e. CC' % MM)
    a2c = s([ac, mmc], 'subcld', '%s e. CC' % A2); b2c = s([bc, mmc], 'addcld', '%s e. CC' % B2)
    ra2 = s([ac, mmc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (A2, RA, MM))
    rmm = s([s([mr], 'rpred', '%s e. RR' % M_), s([mr], 'rpred', '%s e. RR' % M_)], 'crred', '( Re ` %s ) = %s' % (MM, M_))
    RECT = '( %s crect %s )' % (A2, B2)
    Ax = '( %s /\\ x e. %s )' % (A0, RECT)
    L = lambda st: lift(w, st, Ax)
    dx = decode(w, Ax, w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, RECT)), L(a2c), L(b2c), A2, B2, RECT, U='x')
    xc = dx[0]
    lvx = {'( Re ` x )': w.s([xc], 'recld', '( %s -> ( Re ` x ) e. RR )' % Ax), '( Re ` %s )' % A2: w.s([L(a2c)], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, A2)),
           '( Re ` %s )' % RA: L(lv['( Re ` %s )' % RA]), '( Re ` %s )' % MM: w.s([L(mmc)], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (Ax, MM)), 'A': L(ar)}
    rx = lin8(w, Ax, [dx[1], L(ra2), L(rmm), L(reA), L(a0)], '0 < ( Re ` x )', lvx)
    elx = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Ax), w.inst('elhp2')], 'syl', '( %s -> ( x e. %s <-> ( x e. CC /\\ 0 < ( Re ` x ) ) ) )' % (Ax, HP0))
    xh = w.s([w.s([xc, rx], 'jca', '( %s -> ( x e. CC /\\ 0 < ( Re ` x ) ) )' % Ax), elx], 'mpbird', '( %s -> x e. %s )' % (Ax, HP0))
    sub = s([w.s([xh], 'ex', '( %s -> ( x e. %s -> x e. %s ) )' % (A0, RECT, HP0))], 'ssrdv', '%s C_ %s' % (RECT, HP0))
    two = s([], '2cnd', '2 e. CC')
    re2 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'rered', '( Re ` 2 ) = 2')
    im2 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'reim0d', '( Im ` 2 ) = 0')
    lv2 = dict(lv); lv2['( Re ` 2 )'] = s([two], 'recld', '( Re ` 2 ) e. RR'); lv2['( Im ` 2 )'] = s([two], 'imcld', '( Im ` 2 ) e. RR')
    hy2 = hy + [re2, im2]
    tin = encode(w, A0, two, ac, bc, RA, RB, '2', lin8(w, A0, hy2, '( Re ` %s ) <_ ( Re ` 2 )' % RA, lv2), lin8(w, A0, hy2, '( Re ` 2 ) <_ ( Re ` %s )' % RB, lv2),
                 lin8(w, A0, hy2, '( Im ` %s ) <_ ( Im ` 2 )' % RA, lv2), lin8(w, A0, hy2, '( Im ` 2 ) <_ ( Im ` %s )' % RB, lv2))
    HZ = tsub(stmt('holzfi'), {'A': RA, 'B': RB, 'R': M_, 'D': HP0})
    hza, hzc = ante_of(HZ)
    P1, P2 = top_and(hza)
    Q1, Q2, Q3 = top_and(P1)
    q1 = s([hol, s([s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (RA, RB)), geo], 'jca', Q2), s([mr, sub], 'jca', Q3)], '3jca', P1)
    subw = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ w = 2 ) -> w = 2 )' % A0)], 'fveq2d', '( ( %s /\\ w = 2 ) -> ( F ` w ) = ( F ` 2 ) )' % A0)], 'neeq1d',
               '( ( %s /\\ w = 2 ) -> ( ( F ` w ) =/= 0 <-> ( F ` 2 ) =/= 0 ) )' % A0)
    ex = s([f2, s([tin, subw], 'rspcedv', '( ( F ` 2 ) =/= 0 -> %s )' % P2)], 'mpd', P2)
    zfin = s([s([q1, ex], 'jca', hza), w.inst('holzfi')], 'syl', hzc)
    ZR = hzc.rsplit(' e. Fin', 1)[0]
    # ZFA C_ ZR
    Aq = '( %s /\\ q e. %s )' % (A0, ZFA)
    Lq = lambda st: lift(w, st, Aq)
    BOXA = BOX('A', 'T')
    subr = w.s([w.s([w.s([], 'neeq1', '( r = q -> ( r =/= 1 <-> q =/= 1 ) )'), w.s([w.s([], 'fveq2', '( r = q -> ( F ` r ) = ( F ` q ) )')], 'eqeq1d', '( r = q -> ( ( F ` r ) = 0 <-> ( F ` q ) = 0 ) )')],
                     'anbi12d', '( r = q -> ( ( r =/= 1 /\\ ( F ` r ) = 0 ) <-> ( q =/= 1 /\\ ( F ` q ) = 0 ) ) )')], 'x', 'x') if False else \
        w.s([w.s([], 'neeq1', '( r = q -> ( r =/= 1 <-> q =/= 1 ) )'), w.s([w.s([], 'fveq2', '( r = q -> ( F ` r ) = ( F ` q ) )')], 'eqeq1d', '( r = q -> ( ( F ` r ) = 0 <-> ( F ` q ) = 0 ) )')],
            'anbi12d', '( r = q -> ( ( r =/= 1 /\\ ( F ` r ) = 0 ) <-> ( q =/= 1 /\\ ( F ` q ) = 0 ) ) )')
    elq = w.s([subr], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( q =/= 1 /\\ ( F ` q ) = 0 ) ) )' % (ZFA, BOXA))
    qq = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, ZFA)), elq], 'sylib', '( %s -> ( q e. %s /\\ ( q =/= 1 /\\ ( F ` q ) = 0 ) ) )' % (Aq, BOXA))
    qb = w.s([qq, w.inst('simpl')], 'syl', '( %s -> q e. %s )' % (Aq, BOXA))
    fq0 = w.s([qq, w.inst('simprr')], 'syl', '( %s -> ( F ` q ) = 0 )' % Aq)
    dq = decode(w, Aq, qb, Lq(bac), Lq(bbc), BA, BB, BOXA, U='q')
    qc = dq[0]
    lvq = {'( Re ` q )': w.s([qc], 'recld', '( %s -> ( Re ` q ) e. RR )' % Aq), '( Im ` q )': w.s([qc], 'imcld', '( %s -> ( Im ` q ) e. RR )' % Aq)}
    for k_, v_ in lv.items():
        lvq[k_] = Lq(v_)
    for e, st in (('( Re ` %s )' % BA, bac), ('( Im ` %s )' % BA, bac), ('( Re ` %s )' % BB, bbc), ('( Im ` %s )' % BB, bbc)):
        lvq[e] = w.s([Lq(st)], 'recld' if e.startswith('( Re') else 'imcld', '( %s -> %s e. RR )' % (Aq, e))
    hyq = [Lq(x) for x in hy + [rbA, ibA, rbB, ibB]] + dq[1:]
    qin = encode(w, Aq, qc, Lq(ac), Lq(bc), RA, RB, 'q', lin8(w, Aq, hyq, '( Re ` %s ) <_ ( Re ` q )' % RA, lvq), lin8(w, Aq, hyq, '( Re ` q ) <_ ( Re ` %s )' % RB, lvq),
                 lin8(w, Aq, hyq, '( Im ` %s ) <_ ( Im ` q )' % RA, lvq), lin8(w, Aq, hyq, '( Im ` q ) <_ ( Im ` %s )' % RB, lvq))
    subz = w.s([w.s([], 'fveq2', '( r = q -> ( F ` r ) = ( F ` q ) )')], 'eqeq1d', '( r = q -> ( ( F ` r ) = 0 <-> ( F ` q ) = 0 ) )')
    qz = w.s([subz, qin, fq0], 'elrabd', '( %s -> q e. %s )' % (Aq, ZR))
    ss_ = s([w.s([qz], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, ZFA, ZR))], 'ssrdv', '%s C_ %s' % (ZFA, ZR))
    zff = s([zfin, ss_], 'ssfid', '%s e. Fin' % ZFA)
    # orders
    rq = lin8(w, Aq, hyq, '0 < ( Re ` q )', lvq)
    elq2 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % Aq), w.inst('elhp2')], 'syl', '( %s -> ( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) ) )' % (Aq, HP0))
    qh = w.s([w.s([qc, rq], 'jca', '( %s -> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % Aq), elq2], 'mpbird', '( %s -> q e. %s )' % (Aq, HP0))
    on = w.s([w.s([w.s([Lq(h2), qh], 'jca', '( %s -> ( %s /\\ q e. %s ) )' % (Aq, H2, HP0)), fq0], 'jca', '( %s -> ( ( %s /\\ q e. %s ) /\\ ( F ` q ) = 0 ) )' % (Aq, H2, HP0)),
              w.inst('hp0ordnn')], 'syl', '( %s -> ( F holord q ) e. NN )' % Aq)
    w.qed([zff, s([on], 'ralrimiva', 'A. q e. %s ( F holord q ) e. NN' % ZFA)], 'jca', S['zffin'])
    return run8(w)


def gen_zcmono():
    w = W('zcmono', 'The box count decreases in the abscissa (Lean ` zeroCountBox_mono ` ): for ` 0 < A <_ B ` , ` A <_ 1 ` , the mass of the zeros off ` 1 ` in ` [ B , 1 ] x. [ - T , T ] ` is at most that in ` [ A , 1 ] x. [ - T , T ] ` ( ~ zffin , ~ fsumless ).')
    A0, GC = ante_of(S['zcmono'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    h2 = s([], 'simpl', H2)
    X2 = top_and(A0)[1]
    x2 = s([], 'simpr', X2)
    P1, P2, P3 = top_and(X2)
    a3 = s([x2, w.inst('simp1')], 'syl', P1); bb = s([x2, w.inst('simp2')], 'syl', P2); tr = s([x2, w.inst('simp3')], 'syl', 'T e. RR')
    ar = s([a3, w.inst('simp1')], 'syl', 'A e. RR'); br = s([bb, w.inst('simpl')], 'syl', 'B e. RR'); ab = s([bb, w.inst('simpr')], 'syl', 'A <_ B')
    Z = tsub(S['zffin'], {})
    za, zc = ante_of(Z)
    zf = s([s([h2, s([a3, tr], 'jca', top_and(za)[1])], 'jca', za), w.inst('zffin')], 'syl', zc)
    zfin = s([zf, w.inst('simpl')], 'syl', '%s e. Fin' % ZFA); aln = s([zf, w.inst('simpr')], 'syl', 'A. q e. %s ( F holord q ) e. NN' % ZFA)
    BA, BB_, BBB = BOX('A', 'T'), BOX('B', 'T'), None
    A1, A2 = '( A + ( _i x. -u T ) )', '( B + ( _i x. -u T ) )'
    C1 = '( 1 + ( _i x. T ) )'
    nt = s([tr], 'renegcld', '-u T e. RR')
    a1c, ra1, ia1 = crfacts(w, A0, 'A', '-u T', ar, nt)
    a2c, ra2, ia2 = crfacts(w, A0, 'B', '-u T', br, nt)
    c1c, rc1, ic1 = crfacts(w, A0, '1', 'T', numst(w, A0, '1', 'RR'), tr)
    lv = {'A': ar, 'B': br, 'T': tr}
    for e, st in (('( Re ` %s )' % A1, a1c), ('( Im ` %s )' % A1, a1c), ('( Re ` %s )' % A2, a2c), ('( Im ` %s )' % A2, a2c), ('( Re ` %s )' % C1, c1c), ('( Im ` %s )' % C1, c1c)):
        lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hy = [ra1, ia1, ra2, ia2, rc1, ic1, ab]
    CS = tsub(stmt('crectss2'), {'A': A1, 'B': C1, 'C': A2, 'E': C1})
    csa, csc = ante_of(CS)
    Z1, Z2, Z3 = top_and(csa)
    ii = [lin8(w, A0, hy, g, lv) for g in ('( Re ` %s ) <_ ( Re ` %s )' % (A1, A2), '( Re ` %s ) <_ ( Re ` %s )' % (C1, C1),
                                              '( Im ` %s ) <_ ( Im ` %s )' % (A1, A2), '( Im ` %s ) <_ ( Im ` %s )' % (C1, C1))]
    sub = s([s([s([a1c, c1c], 'jca', Z1), s([a2c, c1c], 'jca', Z2), s([s([ii[0], ii[1]], 'jca', top_and(Z3)[0]), s([ii[2], ii[3]], 'jca', top_and(Z3)[1])], 'jca', Z3)], '3jca', csa),
               w.inst('crectss2')], 'syl', csc)
    ZFB = ZF('F', 'B', 'T')
    rs = s([sub, w.inst('rabss2')], 'syl', '%s C_ %s' % (ZFB, ZFA))
    Aq = '( %s /\\ q e. %s )' % (A0, ZFA)
    nq = w.s([aln], 'r19.21bi', '( %s -> ( F holord q ) e. NN )' % Aq)
    w.qed([zfin, w.s([nq], 'nnred', '( %s -> ( F holord q ) e. RR )' % Aq), w.s([w.s([nq], 'nnnn0d', '( %s -> ( F holord q ) e. NN0 )' % Aq)], 'nn0ge0d', '( %s -> 0 <_ ( F holord q ) )' % Aq), rs],
          'fsumless', S['zcmono'])
    return run8(w)


if __name__ == '__main__':
    gen_hp0ordnn()
    gen_zffin()
    gen_zcmono()
