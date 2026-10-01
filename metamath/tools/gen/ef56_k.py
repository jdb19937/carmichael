"""Sortie EF56: order 0 at a nonzero point (ef6o0), the residue bookkeeping of the zeta contour (ef6bk)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True


def gen_o0():
    w = W('ef6o0', 'A function holomorphic on the right half-plane has order ` 0 ` at a point where it does not vanish ( ~ holordeq with the cofactor ` F ` itself).')
    A0 = ante_of(S['ef6o0'])[0]
    c = Ctx(w, A0)
    fcn = c.g('F e. ( %s -cn-> CC )' % HP0); fdm = c.g('%s C_ dom ( CC _D F )' % HP0); ph = c.g('P e. %s' % HP0); fn = c.g('( F ` P ) =/= 0')
    pc, _ = hp_facts(w, A0, ph, 'P')
    Az = '( %s /\\ z e. %s )' % (A0, HP0)
    cz = Ctx(w, Az)
    zh = cz([], 'simpr', 'z e. %s' % HP0)
    zc, _ = hp_facts(w, Az, zh, 'z')
    fz = fcc(w, Az, cz([lift(w, fcn, Az), lift(w, fdm, Az)], 'jca', HOLF('F', HP0)), 'F', HP0, 'z', zh)
    e0 = cz([cz([zc, lift(w, pc, Az)], 'subcld', '( z - P ) e. CC')], 'exp0d', '( ( z - P ) ^ 0 ) = 1')
    e1 = cz([cz([e0], 'oveq1d', '( ( ( z - P ) ^ 0 ) x. ( F ` z ) ) = ( 1 x. ( F ` z ) )'), cz([fz], 'mullidd', '( 1 x. ( F ` z ) ) = ( F ` z )')], 'eqtrd', '( ( ( z - P ) ^ 0 ) x. ( F ` z ) ) = ( F ` z )')
    al = c([cz([e1], 'eqcomd', '( F ` z ) = ( ( ( z - P ) ^ 0 ) x. ( F ` z ) )')], 'ralrimiva', 'A. z e. %s ( F ` z ) = ( ( ( z - P ) ^ 0 ) x. ( F ` z ) )' % HP0)
    HE = tsub(stmt('holordeq'), {'V': '_V', 'E': HP0, 'G': 'F', 'N': '0'})
    ha, hc = ante_of(HE)
    K1, K2, K3 = top_and(ha)
    k1 = c([c([fcn], 'elexd', 'F e. _V'), c([c.a1(w.s([], 'hpopn', '%s e. ( TopOpen ` CCfld )' % HP0), '%s e. ( TopOpen ` CCfld )' % HP0), ph], 'jca', top_and(K1)[1])], 'jca', K1)
    k2 = c([c([fcn, fdm], 'jca', HOLF('F', HP0)), fn], 'jca', K2)
    k3 = c([c.a1(w.s([], '0nn0', '0 e. NN0'), '0 e. NN0'), al], 'jca', K3)
    w.qed([c([k1, k2, k3], '3jca', ha), w.inst('holordeq')], 'syl', S['ef6o0'])
    return run8(w)


def gen_bk():
    from zc1_m import e_h2
    from zc1_f import gval
    w = W('ef6bk', 'The residue bookkeeping of Lean ` contour_zeta ` ( ` hres ` ): over the zeros of ` eta ` and of ` g ` in the rectangle, ` sum ord eta y ^ q / q - sum ord g y ^ q / q = sum ord E1 y ^ q / q - y ` ; the pole of ` zeta ` at ` 1 ` is the zero of ` g ` there ( ~ ef5ez , ~ ef6o0 , ~ zc1ezt , ~ ef5e11 ).')
    A0 = ante_of(S['ef6bk'])[0]
    c = Ctx(w, A0)
    g = c.g
    yp = g('Y e. RR+'); sr = g('S e. RR'); s12 = g('( 1 / 2 ) <_ S'); s1 = g('S < 1')
    cr = g('C e. RR'); c1 = g('1 < C'); c32 = g('C <_ ( 3 / 2 )')
    ur = g('U e. RR'); vr = g('V e. RR'); u0 = g('0 < U'); v0 = g('0 < V')
    nur = c([ur], 'renegcld', '-u U e. RR')
    ZE, ZG = ZRC(ETA), ZRC(GF)
    Z = '( %s u. %s )' % (ZE, ZG)
    dd = {ETA: c.a1(w.s([], 'ef2dde', DD(ETA, '1')), DD(ETA, '1')), GF: c.a1(w.s([], 'ef2ddg', DD(GF, '1')), DD(GF, '1'))}
    def zrf(F):
        R = tsub(stmt('ef3zrf'), {'F': F, 'A': '1', 'L': '-u U', 'H': 'V'})
        ra, rc = ante_of(R)
        st = c([rebuild(w, c, ra, {DD(F, '1'): dd[F], '-u U e. RR': nur}), w.inst('ef3zrf')], 'syl', rc)
        return conj_split(w, A0, st)
    fE, oE = zrf(ETA); fG, oG = zrf(GF)
    zfin = c([fE, fG, w.inst('unfi')], 'syl2anc', '%s e. Fin' % Z)
    POS = lambda x: '( ( S < ( Re ` %s ) /\\ ( Re ` %s ) < C ) /\\ ( -u U < ( Im ` %s ) /\\ ( Im ` %s ) < V ) )' % (x, x, x, x)
    def zrm(F, x, ante):
        R = tsub(stmt('ef3zrm'), {'F': F, 'L': '-u U', 'H': 'V', 'X': x})
        ra, rc = ante_of(R)
        L_ = lambda st: lift(w, st, ante)
        cc = Ctx(w, ante)
        return cc([cc([cc([L_(sr), L_(cr)], 'jca', '( S e. RR /\\ C e. RR )'), cc([L_(nur), L_(vr)], 'jca', '( -u U e. RR /\\ V e. RR )')], 'jca', ra), w.inst('ef3zrm')], 'syl', rc)
    # position facts on Z
    Aq = '( %s /\\ q e. %s )' % (A0, Z)
    cq = Ctx(w, Aq)
    qZ = cq([], 'simpr', 'q e. %s' % Z)
    BOX = '( q e. CC /\\ %s )' % POS('q')
    def side(F, ZF):
        m = zrm(F, 'q', Aq)
        R3 = '( q e. CC /\\ ( ( %s ` q ) = 0 /\\ %s ) )' % (F, POS('q'))
        imp = w.s([w.s([], 'simpl', '( %s -> q e. CC )' % R3), w.s([w.s([], 'simpr', '( %s -> ( ( %s ` q ) = 0 /\\ %s ) )' % (R3, F, POS('q'))), w.inst('simpr')], 'syl', '( %s -> %s )' % (R3, POS('q')))], 'jca', '( %s -> %s )' % (R3, BOX))
        b = w.s([m], 'biimpd', '( %s -> ( q e. %s -> %s ) )' % (Aq, ZF, R3))
        return w.s([b, imp], 'syl6', '( %s -> ( q e. %s -> %s ) )' % (Aq, ZF, BOX))
    jo = w.s([side(ETA, ZE), side(GF, ZG)], 'jaod', '( %s -> ( ( q e. %s \\/ q e. %s ) -> %s ) )' % (Aq, ZE, ZG, BOX))
    box = cq([cq([qZ, cq.a1(w.s([], 'elun', '( q e. %s <-> ( q e. %s \\/ q e. %s ) )' % (Z, ZE, ZG)), '( q e. %s <-> ( q e. %s \\/ q e. %s ) )' % (Z, ZE, ZG))], 'mpbid', '( q e. %s \\/ q e. %s )' % (ZE, ZG)), jo], 'mpd', BOX)
    qc = cq([box, w.inst('simpl')], 'syl', 'q e. CC')
    pos = cq([box, w.inst('simpr')], 'syl', POS('q'))
    rq1 = cq([cq([pos, w.inst('simpl')], 'syl', '( S < ( Re ` q ) /\\ ( Re ` q ) < C )'), w.inst('simpl')], 'syl', 'S < ( Re ` q )')
    rqr = cq([qc], 'recld', '( Re ` q ) e. RR')
    r0 = lin8(w, Aq, [rq1, lift(w, s12, Aq)], '0 < ( Re ` q )', {'S': lift(w, sr, Aq), '( Re ` q )': rqr})
    qh = cq([cq([qc, r0], 'jca', '( q e. CC /\\ 0 < ( Re ` q ) )'), cq([cq.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbird', 'q e. %s' % HP0)
    qn0 = ne0_re(cq, 'q', qc, r0)
    FQ = '( ( Y ^c q ) / q )'
    fqc = cq([cq([cq([lift(w, yp, Aq)], 'rpcnd', 'Y e. CC'), qc], 'cxpcld', '( Y ^c q ) e. CC'), qc, qn0], 'divcld', '%s e. CC' % FQ)
    def memb(F, ZF):
        """( Aq -> ( q e. ZF <-> ( F ` q ) = 0 ) )"""
        m = zrm(F, 'q', Aq)
        e1 = cq([pos], 'biantrud', '( ( %s ` q ) = 0 <-> ( ( %s ` q ) = 0 /\\ %s ) )' % (F, F, POS('q')))
        e2 = cq([qc], 'biantrurd', '( ( ( %s ` q ) = 0 /\\ %s ) <-> ( q e. CC /\\ ( ( %s ` q ) = 0 /\\ %s ) ) )' % (F, POS('q'), F, POS('q')))
        return cq([m, cq([cq([e1, e2], 'bitrd', '( ( %s ` q ) = 0 <-> ( q e. CC /\\ ( ( %s ` q ) = 0 /\\ %s ) ) )' % (F, F, POS('q')))], 'bicomd',
                         '( ( q e. CC /\\ ( ( %s ` q ) = 0 /\\ %s ) ) <-> ( %s ` q ) = 0 )' % (F, POS('q'), F))], 'bitrd', '( q e. %s <-> ( %s ` q ) = 0 )' % (ZF, F))
    mE = memb(ETA, ZE); mG = memb(GF, ZG)
    hE = hol_eta(w, Aq); hG = hol_gf(w, Aq)
    he1 = e_h2(w, Aq, nx1(w, Aq), '1', U1)
    hE1 = cq([he1, w.inst('simpl')], 'syl', HOLF(E1, HP0))
    def ord0(ante, F, hol, fn):
        cc = Ctx(w, ante)
        return cc([cc([lift(w, hol, ante), cc([lift(w, qh, ante), fn], 'jca', '( q e. %s /\\ ( %s ` q ) =/= 0 )' % (HP0, F))], 'jca', tsub(ante_of(S['ef6o0'])[0], {'F': F, 'P': 'q'})), w.inst('ef6o0')], 'syl', '( %s holord q ) = 0' % F)
    # orders are complex numbers
    oEc = cq([cq([qh, w.inst('etaord')], 'syl', '( %s holord q ) e. NN0' % ETA)], 'nn0cnd', '( %s holord q ) e. CC' % ETA)
    HF1 = tsub(stmt('hp0ordf'), {'F': E1, 'P': 'q'})
    hfa, hfc = ante_of(HF1)
    oE1n = cq([cq([cq([he1, qh], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc), w.inst('simpl')], 'syl', '( %s holord q ) e. NN0' % E1)
    oE1c = cq([oE1n], 'nn0cnd', '( %s holord q ) e. CC' % E1)
    Ain = '( %s /\\ q e. %s )' % (Aq, ZG)
    cin = Ctx(w, Ain)
    ogi = cin([w.s([lift(w, oG, Aq)], 'r19.21bi', '( %s -> ( %s holord q ) e. NN )' % (Ain, GF))], 'nncnd', '( %s holord q ) e. CC' % GF)
    Aout = '( %s /\\ -. q e. %s )' % (Aq, ZG)
    cout = Ctx(w, Aout)
    gfn = cout([cout([cout([], 'simpr', '-. q e. %s' % ZG), cout([lift(w, mG, Aout)], 'notbid', '( -. q e. %s <-> -. ( %s ` q ) = 0 )' % (ZG, GF))], 'mpbid', '-. ( %s ` q ) = 0' % GF)], 'neqned', '( %s ` q ) =/= 0' % GF)
    ogo = cout([ord0(Aout, GF, hG, gfn), cout([], '0cnd', '0 e. CC')], 'eqeltrd', '( %s holord q ) e. CC' % GF)
    oGc = cq([ogi, ogo], 'pm2.61dan', '( %s holord q ) e. CC' % GF)
    TE, TG, TZ = TRM(ETA), TRM(GF), TRM(E1)
    tEc = cq([oEc, fqc], 'mulcld', '%s e. CC' % TE); tGc = cq([oGc, fqc], 'mulcld', '%s e. CC' % TG); tZc = cq([oE1c, fqc], 'mulcld', '%s e. CC' % TZ)
    IQ = ONE('q')
    iqc = cq([cq([], '1cnd', '1 e. CC'), cq([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IQ)
    IF = '( %s x. %s )' % (IQ, FQ)
    ifc = cq([iqc, fqc], 'mulcld', '%s e. CC' % IF)
    # contexts on subsets of Z and their link to Aq
    def ctx_sub(X, toZ):
        """context ( A0 /\\ q e. X ) with a step to Aq; toZ is a closed step ( q e. X -> q e. Z )"""
        A_ = '( %s /\\ q e. %s )' % (A0, X)
        cc = Ctx(w, A_)
        link = cc([cc([], 'simpl', A0), cc([cc([], 'simpr', 'q e. %s' % X), toZ], 'syl', 'q e. %s' % Z)], 'jca', Aq)
        return A_, cc, (lambda st, f: cc([link, st], 'syl', f))
    def dif_to_Z(X):
        return w.s([], 'eldifi', '( q e. ( %s \\ %s ) -> q e. %s )' % (Z, X, Z))
    # zero off ZE: ord eta = 0 and ord E1 = 0
    AdE, cdE, vE = ctx_sub('( %s \\ %s )' % (Z, ZE), dif_to_Z(ZE))
    nqE = cdE([cdE([], 'simpr', 'q e. ( %s \\ %s )' % (Z, ZE)), w.inst('eldifn')], 'syl', '-. q e. %s' % ZE)
    enz = cdE([cdE([nqE, cdE([vE(mE, '( q e. %s <-> ( %s ` q ) = 0 )' % (ZE, ETA))], 'notbid', '( -. q e. %s <-> -. ( %s ` q ) = 0 )' % (ZE, ETA))], 'mpbid', '-. ( %s ` q ) = 0' % ETA)], 'neqned', '( %s ` q ) =/= 0' % ETA)
    qhE = vE(qh, 'q e. %s' % HP0)
    oE0 = cdE([cdE([lift(w, hol_eta(w, A0), AdE), cdE([qhE, enz], 'jca', '( q e. %s /\\ ( %s ` q ) =/= 0 )' % (HP0, ETA))], 'jca', tsub(ante_of(S['ef6o0'])[0], {'F': ETA, 'P': 'q'})), w.inst('ef6o0')], 'syl', '( %s holord q ) = 0' % ETA)
    tE0 = cdE([cdE([oE0], 'oveq1d', '%s = ( 0 x. %s )' % (TE, FQ)), cdE([vE(fqc, '%s e. CC' % FQ)], 'mul02d', '( 0 x. %s ) = 0' % FQ)], 'eqtrd', '%s = 0' % TE)
    # E1 ( q ) =/= 0
    A11 = '( %s /\\ q = 1 )' % AdE
    c11 = Ctx(w, A11)
    e1a = c11([c11([c11([], 'simpr', 'q = 1'), w.inst('fveq2')], 'syl', '( %s ` q ) = ( %s ` 1 )' % (E1, E1)), c11.a1(w.s([], 'ef5e11', S['ef5e11']), S['ef5e11'])], 'eqtrd', '( %s ` q ) = 1' % E1)
    e1a2 = c11([e1a, c11.a1(w.s([], 'ax-1ne0', '1 =/= 0'), '1 =/= 0')], 'eqnetrd', '( %s ` q ) =/= 0' % E1)
    A12 = '( %s /\\ q =/= 1 )' % AdE
    c12 = Ctx(w, A12)
    EZT = tsub(stmt('zc1ezt'), {'P': 'q'})
    eza, ezc = ante_of(EZT)
    ezt = c12([c12([lift(w, qhE, A12), c12([], 'simpr', 'q =/= 1')], 'jca', eza), w.inst('zc1ezt')], 'syl', ezc)
    imp = c12([ezt, w.inst('simpr')], 'syl', top_and(ezc)[1])
    e1b = c12([lift(w, enz, A12), c12([imp], 'necon3d', '( ( %s ` q ) =/= 0 -> ( %s ` q ) =/= 0 )' % (ETA, E1))], 'mpd', '( %s ` q ) =/= 0' % E1)
    e1n = cdE([e1a2, e1b], 'pm2.61dane', '( %s ` q ) =/= 0' % E1)
    he1d = cdE([e_h2(w, AdE, nx1(w, AdE), '1', U1), w.inst('simpl')], 'syl', HOLF(E1, HP0))
    oZ0 = cdE([cdE([he1d, cdE([qhE, e1n], 'jca', '( q e. %s /\\ ( %s ` q ) =/= 0 )' % (HP0, E1))], 'jca', tsub(ante_of(S['ef6o0'])[0], {'F': E1, 'P': 'q'})), w.inst('ef6o0')], 'syl', '( %s holord q ) = 0' % E1)
    tZ0 = cdE([cdE([oZ0], 'oveq1d', '%s = ( 0 x. %s )' % (TZ, FQ)), cdE([vE(fqc, '%s e. CC' % FQ)], 'mul02d', '( 0 x. %s ) = 0' % FQ)], 'eqtrd', '%s = 0' % TZ)
    # zero off ZG: ord g = 0
    AdG, cdG, vG = ctx_sub('( %s \\ %s )' % (Z, ZG), dif_to_Z(ZG))
    nqG = cdG([cdG([], 'simpr', 'q e. ( %s \\ %s )' % (Z, ZG)), w.inst('eldifn')], 'syl', '-. q e. %s' % ZG)
    gnz = cdG([cdG([nqG, cdG([vG(mG, '( q e. %s <-> ( %s ` q ) = 0 )' % (ZG, GF))], 'notbid', '( -. q e. %s <-> -. ( %s ` q ) = 0 )' % (ZG, GF))], 'mpbid', '-. ( %s ` q ) = 0' % GF)], 'neqned', '( %s ` q ) =/= 0' % GF)
    oG0 = cdG([cdG([lift(w, hol_gf(w, A0), AdG), cdG([vG(qh, 'q e. %s' % HP0), gnz], 'jca', '( q e. %s /\\ ( %s ` q ) =/= 0 )' % (HP0, GF))], 'jca', tsub(ante_of(S['ef6o0'])[0], {'F': GF, 'P': 'q'})), w.inst('ef6o0')], 'syl', '( %s holord q ) = 0' % GF)
    tG0 = cdG([cdG([oG0], 'oveq1d', '%s = ( 0 x. %s )' % (TG, FQ)), cdG([vG(fqc, '%s e. CC' % FQ)], 'mul02d', '( 0 x. %s ) = 0' % FQ)], 'eqtrd', '%s = 0' % TG)
    # zero off { 1 }
    Ad1, cd1, v1 = ctx_sub('( %s \\ { 1 } )' % Z, dif_to_Z('{ 1 }'))
    q1n = cd1([cd1([cd1([], 'simpr', 'q e. ( %s \\ { 1 } )' % Z), cd1.a1(w.s([], 'eldifsn', '( q e. ( %s \\ { 1 } ) <-> ( q e. %s /\\ q =/= 1 ) )' % (Z, Z)), '( q e. ( %s \\ { 1 } ) <-> ( q e. %s /\\ q =/= 1 ) )' % (Z, Z))], 'mpbid', '( q e. %s /\\ q =/= 1 )' % Z), w.inst('simpr')], 'syl', 'q =/= 1')
    i0 = cd1([cd1([q1n], 'neneqd', '-. q = 1')], 'iffalsed', '%s = 0' % IQ)
    tI0 = cd1([cd1([i0], 'oveq1d', '%s = ( 0 x. %s )' % (IF, FQ)), cd1([v1(fqc, '%s e. CC' % FQ)], 'mul02d', '( 0 x. %s ) = 0' % FQ)], 'eqtrd', '%s = 0' % IF)
    # 1 e. ZG
    one = '1'
    m1 = zrm(GF, '1', A0)
    re1c = c.a1(w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
    r01 = c([lin8(w, A0, [], '0 < 1', {}), re1c], 'breqtrrd', '0 < ( Re ` 1 )')
    oneh = c([c([c([], '1cnd', '1 e. CC'), r01], 'jca', '( 1 e. CC /\\ 0 < ( Re ` 1 ) )'),
              c([c.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( 1 e. %s <-> ( 1 e. CC /\\ 0 < ( Re ` 1 ) ) )' % HP0)], 'mpbird', '1 e. %s' % HP0)
    gv, GV = gval(w, A0, oneh, '1')
    pw0 = c([c([c([c([], '1cnd', '1 e. CC')], 'subidd', '( 1 - 1 ) = 0')], 'oveq2d', '( 2 ^c ( 1 - 1 ) ) = ( 2 ^c 0 )'), c([c([], '2cnd', '2 e. CC')], 'cxp0d', '( 2 ^c 0 ) = 1')], 'eqtrd', '( 2 ^c ( 1 - 1 ) ) = 1')
    g1a = c([c([pw0], 'oveq2d', '( 1 - ( 2 ^c ( 1 - 1 ) ) ) = ( 1 - 1 )'), c([c([], '1cnd', '1 e. CC')], 'subidd', '( 1 - 1 ) = 0')], 'eqtrd', '( 1 - ( 2 ^c ( 1 - 1 ) ) ) = 0')
    g1 = c([gv, g1a], 'eqtrd', '( %s ` 1 ) = 0' % GF)
    lv1 = {'S': sr, 'C': cr, 'U': ur, 'V': vr}
    re1 = c.a1(w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1'); im1 = c.a1(w.s([], 'im1', '( Im ` 1 ) = 0'), '( Im ` 1 ) = 0')
    p1 = c([c([c([s1, c([re1], 'eqcomd', '1 = ( Re ` 1 )')], 'breqtrd', 'S < ( Re ` 1 )'), c([re1, c1], 'eqbrtrd', '( Re ` 1 ) < C')], 'jca', '( S < ( Re ` 1 ) /\\ ( Re ` 1 ) < C )'),
            c([c([lin8(w, A0, [u0], '-u U < 0', {'U': ur}), c([im1], 'eqcomd', '0 = ( Im ` 1 )')], 'breqtrd', '-u U < ( Im ` 1 )'), c([im1, v0], 'eqbrtrd', '( Im ` 1 ) < V')], 'jca', '( -u U < ( Im ` 1 ) /\\ ( Im ` 1 ) < V )')],
           'jca', POS('1'))
    oneG = c([c([c([], '1cnd', '1 e. CC'), c([g1, p1], 'jca', '( ( %s ` 1 ) = 0 /\\ %s )' % (GF, POS('1')))], 'jca', '( 1 e. CC /\\ ( ( %s ` 1 ) = 0 /\\ %s ) )' % (GF, POS('1'))), m1], 'mpbird', '1 e. %s' % ZG)
    oneZ = c([oneG, c.a1(w.s([], 'ssun2', '%s C_ %s' % (ZG, Z)), '%s C_ %s' % (ZG, Z))], 'x', 'x') if False else c([c.a1(w.s([], 'ssun2', '%s C_ %s' % (ZG, Z)), '%s C_ %s' % (ZG, Z)), oneG], 'sseldd', '1 e. %s' % Z)
    # the sums over the subsets equal the sums over Z
    def on_sub(X, toZ, st, f):
        A_, cc, via = ctx_sub(X, toZ)
        return via(st, f)
    inE = w.s([], 'elun1', '( q e. %s -> q e. %s )' % (ZE, Z))
    inG = w.s([], 'elun2', '( q e. %s -> q e. %s )' % (ZG, Z))
    def fss(X, ssst, cst, zst, T):
        return c([ssst, cst, zst, zfin], 'fsumss', 'sum_ q e. %s %s = sum_ q e. %s %s' % (X, T, Z, T))
    ssE = c.a1(w.s([], 'ssun1', '%s C_ %s' % (ZE, Z)), '%s C_ %s' % (ZE, Z))
    ssG = c.a1(w.s([], 'ssun2', '%s C_ %s' % (ZG, Z)), '%s C_ %s' % (ZG, Z))
    sE = fss(ZE, ssE, on_sub(ZE, inE, tEc, '%s e. CC' % TE), tE0, TE)
    sG = fss(ZG, ssG, on_sub(ZG, inG, tGc, '%s e. CC' % TG), tG0, TG)
    sZ = fss(ZE, ssE, on_sub(ZE, inE, tZc, '%s e. CC' % TZ), tZ0, TZ)
    ss1 = c([oneZ], 'snssd', '{ 1 } C_ %s' % Z)
    A1s = '( %s /\\ q e. { 1 } )' % A0
    c1s = Ctx(w, A1s)
    q1 = c1s([c1s([], 'simpr', 'q e. { 1 }'), w.inst('elsni')], 'syl', 'q = 1')
    qz1 = c1s([lift(w, oneZ, A1s), c1s([q1], 'eleq1d', '( q e. %s <-> 1 e. %s )' % (Z, Z))], 'mpbird', 'q e. %s' % Z)
    lk1 = c1s([c1s([], 'simpl', A0), qz1], 'jca', Aq)
    ic1 = c1s([lk1, ifc], 'syl', '%s e. CC' % IF)
    s1s = c([ss1, ic1, tI0, zfin], 'fsumss', 'sum_ q e. { 1 } %s = sum_ q e. %s %s' % (IF, Z, IF))
    IF1 = '( if ( 1 = 1 , 1 , 0 ) x. ( ( Y ^c 1 ) / 1 ) )'
    sb, _ = subst(w, IF, 'q', '1')
    ycc = c([yp], 'rpcnd', 'Y e. CC')
    if1 = c([c([c.a1(w.s([], 'eqid', '1 = 1'), '1 = 1')], 'iftrued', 'if ( 1 = 1 , 1 , 0 ) = 1'), c([c([ycc], 'cxp1d', '( Y ^c 1 ) = Y')], 'oveq1d', '( ( Y ^c 1 ) / 1 ) = ( Y / 1 )')], 'oveq12d', '%s = ( 1 x. ( Y / 1 ) )' % IF1)
    if2 = c([if1, c([c([c([ycc], 'div1d', '( Y / 1 ) = Y')], 'oveq2d', '( 1 x. ( Y / 1 ) ) = ( 1 x. Y )'), c([ycc], 'mullidd', '( 1 x. Y ) = Y')], 'eqtrd', '( 1 x. ( Y / 1 ) ) = Y')], 'eqtrd', '%s = Y' % IF1)
    if1c = c([if2, ycc], 'eqeltrd', '%s e. CC' % IF1)
    sn = c([c([], '1cnd', '1 e. CC'), if1c, w.s([sb], 'sumsn', '( ( 1 e. CC /\\ %s e. CC ) -> sum_ q e. { 1 } %s = %s )' % (IF1, IF, IF1))], 'syl2anc', 'sum_ q e. { 1 } %s = %s' % (IF, IF1))
    sI = c([c([c([s1s], 'eqcomd', 'sum_ q e. %s %s = sum_ q e. { 1 } %s' % (Z, IF, IF)), sn], 'eqtrd', 'sum_ q e. %s %s = %s' % (Z, IF, IF1)), if2], 'eqtrd', 'sum_ q e. %s %s = Y' % (Z, IF))
    # pointwise: tE - tG = tZ - IF
    OE, OG, OZ = '( %s holord q )' % ETA, '( %s holord q )' % GF, '( %s holord q )' % E1
    ez = cq([qh, w.inst('ef5ez')], 'syl', '( %s + %s ) = ( %s + %s )' % (OE, IQ, OG, OZ))
    oe = cq([cq([cq([oEc, iqc], 'pncand', '( ( %s + %s ) - %s ) = %s' % (OE, IQ, IQ, OE))], 'eqcomd', '%s = ( ( %s + %s ) - %s )' % (OE, OE, IQ, IQ)), cq([ez], 'oveq1d', '( ( %s + %s ) - %s ) = ( ( %s + %s ) - %s )' % (OE, IQ, IQ, OG, OZ, IQ))],
            'eqtrd', '%s = ( ( %s + %s ) - %s )' % (OE, OG, OZ, IQ))
    t1 = cq([cq([oe], 'oveq1d', '%s = ( ( ( %s + %s ) - %s ) x. %s )' % (TE, OG, OZ, IQ, FQ))], 'oveq1d', '( %s - %s ) = ( ( ( ( %s + %s ) - %s ) x. %s ) - %s )' % (TE, TG, OG, OZ, IQ, FQ, TG))
    clq = Closure(w, Aq, {OG: ('CC', oGc), OZ: ('CC', oE1c), IQ: ('CC', iqc), FQ: ('CC', fqc)})
    for k in (OG, OZ, IQ, FQ):
        clq.atom(k)
    t2 = ringeq(w, Aq, '( ( ( ( %s + %s ) - %s ) x. %s ) - %s )' % (OG, OZ, IQ, FQ, TG), '( %s - %s )' % (TZ, IF), clq)
    pwe = cq([t1, t2], 'eqtrd', '( %s - %s ) = ( %s - %s )' % (TE, TG, TZ, IF))
    d1 = c([zfin, tEc, tGc], 'fsumsub', 'sum_ q e. %s ( %s - %s ) = ( sum_ q e. %s %s - sum_ q e. %s %s )' % (Z, TE, TG, Z, TE, Z, TG))
    d2 = c([pwe], 'sumeq2dv', 'sum_ q e. %s ( %s - %s ) = sum_ q e. %s ( %s - %s )' % (Z, TE, TG, Z, TZ, IF))
    d3 = c([zfin, tZc, ifc], 'fsumsub', 'sum_ q e. %s ( %s - %s ) = ( sum_ q e. %s %s - sum_ q e. %s %s )' % (Z, TZ, IF, Z, TZ, Z, IF))
    SE_, SG_, SZ_ = 'sum_ q e. %s %s' % (Z, TE), 'sum_ q e. %s %s' % (Z, TG), 'sum_ q e. %s %s' % (Z, TZ)
    k1 = c([c([sE, sG], 'oveq12d', '( %s - %s ) = ( %s - %s )' % (SREc, SRGc, SE_, SG_)), c([d1], 'eqcomd', '( %s - %s ) = sum_ q e. %s ( %s - %s )' % (SE_, SG_, Z, TE, TG))], 'eqtrd',
           '( %s - %s ) = sum_ q e. %s ( %s - %s )' % (SREc, SRGc, Z, TE, TG))
    k2 = c([c([k1, d2], 'eqtrd', '( %s - %s ) = sum_ q e. %s ( %s - %s )' % (SREc, SRGc, Z, TZ, IF)), d3], 'eqtrd', '( %s - %s ) = ( %s - sum_ q e. %s %s )' % (SREc, SRGc, SZ_, Z, IF))
    k3 = c([k2, c([c([sZ], 'eqcomd', '%s = %s' % (SZ_, SRZc)), sI], 'oveq12d', '( %s - sum_ q e. %s %s ) = ( %s - Y )' % (SZ_, Z, IF, SRZc))], 'eqtrd', '( %s - %s ) = ( %s - Y )' % (SREc, SRGc, SRZc))
    # closures
    def fcl(X, toZ, st, T):
        A_, cc, via = ctx_sub(X, toZ)
        fin_ = fE if X == ZE else fG
        return c([fin_, via(st, '%s e. CC' % T)], 'fsumcl', 'sum_ q e. %s %s e. CC' % (X, T))
    cE = fcl(ZE, inE, tEc, TE); cG = fcl(ZG, inG, tGc, TG); cZ = fcl(ZE, inE, tZc, TZ)
    w.qed([k3, c([cE, cG, cZ], '3jca', '( %s e. CC /\\ %s e. CC /\\ %s e. CC )' % (SREc, SRGc, SRZc))], 'jca', S['ef6bk'])
    return run8(w)


GENS = {'ef6o0': gen_o0, 'ef6bk': gen_bk}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
