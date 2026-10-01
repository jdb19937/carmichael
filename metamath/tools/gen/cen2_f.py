"""Sortie CEN2: the positivity core (cen2n13; Lean Census no_thirteen_bad, evaluated at 1 + 3 delta)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure, lift
from c9lib import top_and
from lin import linarith, nlinarith
from congr import mptval

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


Q3 = '( 1 + ( 3 x. D ) )'
IMJ = '( Im ` ( P ` j ) )'; IML = '( Im ` ( P ` l ) )'
MJ_ = '( M ` j )'; ML_ = '( M ` l )'
VJ = lambda v: VT(MJ_, 'j', IMJ, v)
VL = lambda v: VT(ML_, 'l', IML, v)
BB = lambda v: '( Re ` ( %s x. %s ) )' % (AW(v), VJ(v))
CC_ = lambda v: '( %s x. %s )' % (AW(v), SQ(VJ(v)))
EE = lambda v: '( Re ` ( %s x. ( %s x. ( * ` %s ) ) ) )' % (AW(v), VJ(v), VL(v))
FA = '( n e. NN |-> %s )' % AW('n')
FB = '( n e. NN |-> %s )' % BB('n')
FC = '( n e. NN |-> %s )' % CC_('n')
FE = '( n e. NN |-> %s )' % EE('n')


def gen_n13():
    w = W('cen2n13', 'Landau-Page positivity core: there are no 13 distinct primitive characters ` a ` mod ` M ( a ) ` , ` 2 <_ M ( a ) <_ Z ` , each with a zero ` P ( a ) =/= 1 ` of ` ( M ( a ) DChrLF a ) ` in ` [ 1 - D , 1 ] x [ -V , V ] ` , once ` 0 < D <_ 1 / 40 ` , ` 1 <_ V ` , ` 2 <_ Z ` and ` D log ( Z ( V + 2 ) ) <_ 10 ^ -10 ` (Lean Census ` no_thirteen_bad ` with the threshold ` 10 ^ -10 ` ; the positivity of ` sum Lam ( k ) | 1 + sum_a a ( k ) k ^ -i Im P ( a ) | ^ 2 k ^ - ( 1 + 3 D ) ` is evaluated at ` 1 + 3 D ` , NUMERALS.md).')
    H = split_imp('( %s -> x )' % S['cen2n13'][3:])[0] if False else S['cen2n13'][3:]
    H = H.strip()
    s = lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (H, f))
    def c(ctx):
        return lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (ctx, f))
    FH = split_all(w, H, H, w.s([], 'id', '( %s -> %s )' % (H, H)))
    g = lambda f: FH[f]
    fin = g('J e. Fin'); card = g('( # ` J ) = %s' % N13); fam = g(FAM)
    pars = g(PARS)
    drp = g('D e. RR+'); dle = g('D <_ %s' % F140); vr = g('V e. RR'); v1 = g('1 <_ V'); zr = g('Z e. RR'); z2 = g('2 <_ Z')
    LL_ = LOGZ('Z', 'V')
    dl = g('( D x. %s ) <_ %s' % (LL_, THR))
    BA = BODY('( M ` a )', 'a', '( P ` a )')

    def body(ctx, x, xmem):
        """( ctx -> BODY(M x, x, P x) ) from x e. J"""
        eq = 'a = %s' % x
        idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
        st, bx = w.wcongr(BA, {'a': x}, eq, {'a': idx})
        rs = w.s([st], 'rspcv', '( %s e. J -> ( %s -> %s ) )' % (x, FAM, bx))
        return w.s([xmem, lift(w, fam, ctx), rs], 'sylc', '( %s -> %s )' % (ctx, bx)), bx

    def pt(ctx, N, X, T, v, facts):
        """cen2pt at the point v: returns (awr, aw0, vc)"""
        f = c(ctx)
        PT = tokrep(S['cen2pt'], {'N': N, 'X': X, 'T': T, 'k': v})
        pa_, pc_ = split_imp(PT)
        st = f([f([facts['nn'], facts['xd']], 'jca', top_and(pa_)[0]), f([facts['v'], facts['t'], facts['d']], '3jca', top_and(pa_)[1]), w.inst('cen2pt')], 'syl2anc', pc_)
        a1, vc = top_and(pc_)
        ar_, a0_ = top_and(a1)
        a1s = f([st], 'simpld', a1)
        return f([a1s], 'simpld', ar_), f([a1s], 'simprd', a0_), f([st], 'simprd', vc)

    def jfacts(ctx, x, bst, bx):
        """level, character, height facts of member x under ctx"""
        F = split_all(w, ctx, bx, bst)
        Mx = '( M ` %s )' % x; Px = '( P ` %s )' % x
        out = {'nn': F['%s e. NN' % Mx], 'xd': F['%s e. ( Base ` ( DChr ` %s ) )' % (x, Mx)], 'pc': F['%s e. CC' % Px]}
        out['t'] = w.s([out['pc']], 'imcld', '( %s -> ( Im ` %s ) e. RR )' % (ctx, Px))
        out['d'] = w.s([lift(w, drp, ctx)], 'rpred', '( %s -> D e. RR )' % ctx)
        return out

    PJ = '( %s /\\ j e. J )' % H
    pj = c(PJ)
    bj, BJ = body(PJ, 'j', pj([], 'simpr', 'j e. J'))
    fj = jfacts(PJ, 'j', bj, BJ)
    # ---- the functions on NN
    PN = '( %s /\\ n e. NN )' % H
    pn = c(PN)
    nn_ = pn([], 'simpr', 'n e. NN')
    cn = Closure(w, PN, {'n': ('NN', nn_), 'D': ('RR+', lift(w, drp, PN))})
    L_n = '( Lam ` n )'
    cn.have(L_n, 'RR', pn([nn_, w.inst('vmacl')], 'syl', '%s e. RR' % L_n))
    awn = cn.mem(AW('n'), 'RR')
    fa = s([awn, w.s([], 'eqid', '%s = %s' % (FA, FA))], 'fmptd', '%s : NN --> RR' % FA)
    PJN = '( %s /\\ n e. NN )' % PJ
    pjn = c(PJN)
    fjn = dict(fj); fjn = {k_: lift(w, v_, PJN) for k_, v_ in fj.items()}
    fjn['v'] = pjn([], 'simpr', 'n e. NN')
    awr_n, aw0_n, vj_n = pt(PJN, MJ_, 'j', IMJ, 'n', fjn)
    bbn = pjn([pjn([awr_n], 'recnd', '%s e. CC' % AW('n')) if False else pjn([pjn([awr_n], 'recnd', '%s e. CC' % AW('n')), vj_n], 'mulcld', '( %s x. %s ) e. CC' % (AW('n'), VJ('n')))], 'recld', '%s e. RR' % BB('n'))
    ccn = pjn([awr_n, pjn([pjn([vj_n], 'abscld', '( abs ` %s ) e. RR' % VJ('n'))], 'resqcld', '%s e. RR' % SQ(VJ('n')))], 'remulcld', '%s e. RR' % CC_('n'))
    fbf = pj([bbn, w.s([], 'eqid', '%s = %s' % (FB, FB))], 'fmptd', '%s : NN --> RR' % FB)
    fcf = pj([ccn, w.s([], 'eqid', '%s = %s' % (FC, FC))], 'fmptd', '%s : NN --> RR' % FC)
    JLm = '( J \\ { j } )'
    PJL = '( %s /\\ ( j e. J /\\ l e. %s ) )' % (H, JLm)
    pjl = c(PJL)
    lmem = pjl([pjl([], 'simprr', 'l e. %s' % JLm), w.inst('eldifi')], 'syl', 'l e. J')
    bj2, _ = body(PJL, 'j', pjl([], 'simprl', 'j e. J'))
    bl2, BL = body(PJL, 'l', lmem)
    fj2 = jfacts(PJL, 'j', bj2, BJ); fl2 = jfacts(PJL, 'l', bl2, BL)
    PJLN = '( %s /\\ n e. NN )' % PJL
    pjln = c(PJLN)
    fj2n = {k_: lift(w, v_, PJLN) for k_, v_ in fj2.items()}; fj2n['v'] = pjln([], 'simpr', 'n e. NN')
    fl2n = {k_: lift(w, v_, PJLN) for k_, v_ in fl2.items()}; fl2n['v'] = fj2n['v']
    awr2, aw02, vjn2 = pt(PJLN, MJ_, 'j', IMJ, 'n', fj2n)
    _, _, vln2 = pt(PJLN, ML_, 'l', IML, 'n', fl2n)
    een = pjln([pjln([pjln([awr2], 'recnd', '%s e. CC' % AW('n')), pjln([vjn2, pjln([vln2], 'cjcld', '( * ` %s ) e. CC' % VL('n'))], 'mulcld', '( %s x. ( * ` %s ) ) e. CC' % (VJ('n'), VL('n')))],
                      'mulcld', '( %s x. ( %s x. ( * ` %s ) ) ) e. CC' % (AW('n'), VJ('n'), VL('n')))], 'recld', '%s e. RR' % EE('n'))
    fef = pjl([een, w.s([], 'eqid', '%s = %s' % (FE, FE))], 'fmptd', '%s : NN --> RR' % FE)
    # ---- convergence and bounds per member (cen2one) and per pair (cen2two)
    ONE = tokrep(S['cen2one'], {'N': MJ_, 'X': 'j', 'R': '( P ` j )'})
    oa, oc = split_imp(ONE)
    one = pj([pj([bj, lift(w, pars, PJ)], 'jca', oa), w.inst('cen2one')], 'syl', oc)
    O = split_all(w, PJ, oc, one)
    (bpart, cpart) = top_and(oc)
    bcv, bsec = top_and(bpart); bre, ble = top_and(bsec)
    ccv, csec = top_and(cpart); cre, cle = top_and(csec)
    cvb, _, _ = cvn(w, PJ, BB('k'), O[bcv])
    cvc, _, _ = cvn(w, PJ, CC_('k'), O[ccv])
    TWO = tokrep(S['cen2two'], {'N': MJ_, 'X': 'j', 'R': '( P ` j )', 'M': ML_, 'Y': 'l', 'Q': '( P ` l )'})
    ta, tc = split_imp(TWO)
    jl = pjl([pjl([pjl([], 'simprr', 'l e. %s' % JLm), w.inst('eldifsni')], 'syl', 'l =/= j')], 'necomd', 'j =/= l')
    two = pjl([pjl([pjl([bj2, bl2, jl], '3jca', top_and(ta)[0]), lift(w, pars, PJL)], 'jca', ta), w.inst('cen2two')], 'syl', tc)
    T2 = split_all(w, PJL, tc, two)
    ecv, esec = top_and(tc); ere, ele = top_and(esec)
    cve, _, _ = cvn(w, PJL, EE('k'), T2[ecv])
    # the constant group
    qc = s([s([s([], '1red', '1 e. RR'), s([s([], '3re', '3 e. RR') if False else s([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), s([drp], 'rpred', 'D e. RR')], 'remulcld', '( 3 x. D ) e. RR')], 'readdcld', '%s e. RR' % Q3)], 'recnd', '%s e. CC' % Q3)
    c0 = Closure(w, H, {'D': ('RR+', drp), 'V': ('RR', vr), 'Z': ('RR', zr)})
    q1 = s([s([], '1red', '1 e. RR'), c0.mem('( 3 x. D )', 'RR+')], 'ltaddrpd', '1 < %s' % Q3)
    q1r = s([q1, s([c0.mem(Q3, 'RR')], 'rered', '( Re ` %s ) = %s' % (Q3, Q3))], 'breqtrrd', '1 < ( Re ` %s )' % Q3)
    cva = s([qc, q1r, w.inst('zrvmc')], 'syl2anc', 'seq 1 ( + , %s ) e. dom ~~>' % tokrep(FA, {}).replace(Q3, Q3))
    # ---- the pointwise positivity at k
    PK = '( %s /\\ k e. NN )' % H
    pk = c(PK)
    kn = pk([], 'simpr', 'k e. NN')
    PKJ = '( %s /\\ j e. J )' % PK
    pkj = c(PKJ)
    bjk, _ = body(PKJ, 'j', pkj([], 'simpr', 'j e. J'))
    fjk = jfacts(PKJ, 'j', bjk, BJ); fjk['v'] = pkj([pkj([], 'simpl', PK), kn], 'syl', 'k e. NN')
    awrk, aw0k, vjk = pt(PKJ, MJ_, 'j', IMJ, 'k', fjk)
    ck = Closure(w, PK, {'k': ('NN', kn), 'D': ('RR+', lift(w, drp, PK))})
    ck.have('( Lam ` k )', 'RR', pk([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR'))
    ck.have('( Lam ` k )', 'ge0', pk([kn, w.inst('vmage0')], 'syl', '0 <_ ( Lam ` k )'))
    awk = ck.mem(AW('k'), 'RR'); awk0 = ck.ge0(AW('k'))
    eqjl, vlk = ren(w, VJ('k'), 'j', 'l')
    assert vlk == VL('k'), vlk
    EXP = tokrep(stmt('cenexp'), {'ph': PK, 'V': VJ('k'), 'W': VL('k'), 'A': AW('k')})
    ex = w.s([lift(w, fin, PK), vjk, eqjl, awk], 'cenexp', EXP)
    lhs, rhs = split_imp(EXP)[1][2:-2].split(' ) = ', 1) if False else (None, None)
    LHS = '( %s x. ( ( abs ` ( 1 + sum_ j e. J %s ) ) ^ 2 ) )' % (AW('k'), VJ('k'))
    RHS = split_imp(EXP)[1][len('%s = ' % LHS):]
    sv = pk([lift(w, fin, PK), vjk], 'fsumcl', 'sum_ j e. J %s e. CC' % VJ('k'))
    ab = pk([pk([pk([], 'ax-1cn', '1 e. CC') if False else pk([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), sv], 'addcld', '( 1 + sum_ j e. J %s ) e. CC' % VJ('k'))], 'abscld',
            '( abs ` ( 1 + sum_ j e. J %s ) ) e. RR' % VJ('k'))
    SQ1 = '( ( abs ` ( 1 + sum_ j e. J %s ) ) ^ 2 )' % VJ('k')
    l0 = pk([awk, pk([ab], 'resqcld', '%s e. RR' % SQ1), awk0, pk([ab], 'sqge0d', '0 <_ %s' % SQ1)], 'mulge0d', '0 <_ %s' % LHS)
    r0 = pk([l0, ex], 'breqtrd', '0 <_ %s' % RHS)
    # TOT(k) = RHS
    def fv(ctx, body_n, body_k, rr):
        st, v = mptval(w, ctx, 'n', 'NN', body_n, 'k', w.s([lift(w, kn, ctx)], 'id', '( %s -> k e. NN )' % ctx) if False else lift(w, kn, ctx),
                       exs=w.s([rr], 'elexd', '( %s -> %s e. _V )' % (ctx, body_k)), gen=w.g)
        assert v == body_k, (v, body_k)
        return st
    fak = fv(PK, AW('n'), AW('k'), awk)
    bbk = pkj([pkj([pkj([awrk], 'recnd', '%s e. CC' % AW('k')), vjk], 'mulcld', '( %s x. %s ) e. CC' % (AW('k'), VJ('k')))], 'recld', '%s e. RR' % BB('k'))
    cck = pkj([awrk, pkj([pkj([vjk], 'abscld', '( abs ` %s ) e. RR' % VJ('k'))], 'resqcld', '%s e. RR' % SQ(VJ('k')))], 'remulcld', '%s e. RR' % CC_('k'))
    fbk = fv(PKJ, BB('n'), BB('k'), bbk)
    fck = fv(PKJ, CC_('n'), CC_('k'), cck)
    PKJL = '( %s /\\ l e. %s )' % (PKJ, JLm)
    pkjl = c(PKJL)
    lm2 = pkjl([pkjl([], 'simpr', 'l e. %s' % JLm), w.inst('eldifi')], 'syl', 'l e. J')
    blk, _ = body(PKJL, 'l', lm2)
    flk = jfacts(PKJL, 'l', blk, BL); flk['v'] = lift(w, kn, PKJL)
    _, _, vlk2 = pt(PKJL, ML_, 'l', IML, 'k', flk)
    eek = pkjl([pkjl([lift(w, pkj([awrk], 'recnd', '%s e. CC' % AW('k')), PKJL), pkjl([lift(w, vjk, PKJL), pkjl([vlk2], 'cjcld', '( * ` %s ) e. CC' % VL('k'))], 'mulcld',
                      '( %s x. ( * ` %s ) ) e. CC' % (VJ('k'), VL('k')))], 'mulcld', '( %s x. ( %s x. ( * ` %s ) ) ) e. CC' % (AW('k'), VJ('k'), VL('k')))], 'recld', '%s e. RR' % EE('k'))
    fek = fv(PKJL, EE('n'), EE('k'), eek)
    TOTK = TOT('k')
    TA = '( %s ` k )' % FA; TB = 'sum_ j e. J ( %s ` k )' % FB; TC = 'sum_ j e. J ( %s ` k )' % FC; TE = 'sum_ j e. J sum_ l e. %s ( %s ` k )' % (JLm, FE)
    RB = 'sum_ j e. J %s' % BB('k'); RC = 'sum_ j e. J %s' % CC_('k'); RE = 'sum_ j e. J sum_ l e. %s %s' % (JLm, EE('k'))
    eB = pk([fbk], 'sumeq2dv', '%s = %s' % (TB, RB))
    eC = pk([fck], 'sumeq2dv', '%s = %s' % (TC, RC))
    eE = pk([pkj([fek], 'sumeq2dv', 'sum_ l e. %s ( %s ` k ) = sum_ l e. %s %s' % (JLm, FE, JLm, EE('k')))], 'sumeq2dv', '%s = %s' % (TE, RE))
    e1 = pk([fak, pk([eB], 'oveq2d', '( 2 x. %s ) = ( 2 x. %s )' % (TB, RB))], 'oveq12d', '( %s + ( 2 x. %s ) ) = ( %s + ( 2 x. %s ) )' % (TA, TB, AW('k'), RB))
    e2 = pk([e1, eC], 'oveq12d', '( ( %s + ( 2 x. %s ) ) + %s ) = ( ( %s + ( 2 x. %s ) ) + %s )' % (TA, TB, TC, AW('k'), RB, RC))
    e3 = pk([e2, eE], 'oveq12d', '%s = %s' % (TOTK.replace('( A ` k )', TA).replace('( B ` k )', '( %s ` k )' % FB).replace('( C ` k )', '( %s ` k )' % FC).replace('( E ` k )', '( %s ` k )' % FE), RHS))
    TOTF = tokrep(TOTK, {}).replace('( A ` k )', TA).replace('( B ` k )', '( %s ` k )' % FB).replace('( C ` k )', '( %s ` k )' % FC).replace('( E ` k )', '( %s ` k )' % FE)
    h2 = pk([r0, e3], 'breqtrrd', '0 <_ %s' % TOTF)
    # ---- cen2lim
    LIM = S['cen2lim'].replace('( A ` k )', TA).replace('( B ` k )', '( %s ` k )' % FB).replace('( C ` k )', '( %s ` k )' % FC).replace('( E ` k )', '( %s ` k )' % FE)
    LIM = tokrep(LIM, {'ph': H})
    lim = w.s([fin, h2, fa, pj([fbf, fcf], 'jca', '( %s : NN --> RR /\\ %s : NN --> RR )' % (FB, FC)), fef, cva,
               pj([cvb, cvc], 'jca', '( seq 1 ( + , %s ) e. dom ~~> /\\ seq 1 ( + , %s ) e. dom ~~> )' % (FB, FC)), cve], 'cen2lim', LIM)
    TOTSUM = split_imp(LIM)[1].split(' <_ ', 1)[1][:-2]
    # ---- the bounds
    U3 = '( 3 x. D )'
    VB = tokrep(split_imp(stmt('cenvmb'))[1], {'U': U3})
    ule = linarith(w, H, [dle], '%s <_ 1' % U3, closure=c0)
    vmb = s([c0.mem(U3, 'RR+'), ule, w.inst('cenvmb')], 'syl2anc', VB)
    SA0 = 'sum_ k e. NN %s' % AW('k')
    sa0r = s([vmb], 'simpld', '%s e. RR' % SA0)
    sa0b = s([s([sa0r], 'rered', '( Re ` %s ) = %s' % (SA0, SA0)), s([vmb], 'simprd', '( Re ` %s ) <_ %s' % (SA0, BV))], 'eqbrtrrd', '%s <_ %s' % (SA0, BV))
    SAF = 'sum_ k e. NN %s' % TA
    eqa = s([fak], 'sumeq2dv', '%s = %s' % (SAF, SA0))
    safr = s([eqa, sa0r], 'eqeltrd', '%s e. RR' % SAF)
    sab = s([eqa, sa0b], 'eqbrtrd', '%s <_ %s' % (SAF, BV))
    # per member j: B and C
    PJK = '( %s /\\ k e. NN )' % PJ
    pjk = c(PJK)
    fjk2 = {k_: lift(w, v_, PJK) for k_, v_ in fj.items()}; fjk2['v'] = pjk([], 'simpr', 'k e. NN')
    awr3, aw03, vj3 = pt(PJK, MJ_, 'j', IMJ, 'k', fjk2)
    bb3 = pjk([pjk([pjk([awr3], 'recnd', '%s e. CC' % AW('k')), vj3], 'mulcld', '( %s x. %s ) e. CC' % (AW('k'), VJ('k')))], 'recld', '%s e. RR' % BB('k'))
    cc3 = pjk([awr3, pjk([pjk([vj3], 'abscld', '( abs ` %s ) e. RR' % VJ('k'))], 'resqcld', '%s e. RR' % SQ(VJ('k')))], 'remulcld', '%s e. RR' % CC_('k'))
    def fv2(ctx, body_n, body_k, rr, kst):
        st, v = mptval(w, ctx, 'n', 'NN', body_n, 'k', kst, exs=w.s([rr], 'elexd', '( %s -> %s e. _V )' % (ctx, body_k)), gen=w.g)
        return st
    fb3 = fv2(PJK, BB('n'), BB('k'), bb3, fjk2['v']); fc3 = fv2(PJK, CC_('n'), CC_('k'), cc3, fjk2['v'])
    SBF = 'sum_ k e. NN ( %s ` k )' % FB; SCF = 'sum_ k e. NN ( %s ` k )' % FC
    SB0 = bre.rsplit(' e. RR', 1)[0]; SC0 = cre.rsplit(' e. RR', 1)[0]
    eqb = pj([fb3], 'sumeq2dv', '%s = %s' % (SBF, SB0)); eqc = pj([fc3], 'sumeq2dv', '%s = %s' % (SCF, SC0))
    KLL = '( %s x. %s )' % (KLAN, LL_)
    CB = '( %s - ( 1 / ( 4 x. D ) ) )' % KLL
    sbr = pj([eqb, O[bre]], 'eqeltrd', '%s e. RR' % SBF); sbl = pj([eqb, O[ble]], 'eqbrtrd', '%s <_ %s' % (SBF, CB))
    scr = pj([eqc, O[cre]], 'eqeltrd', '%s e. RR' % SCF); scl = pj([eqc, O[cle]], 'eqbrtrd', '%s <_ %s' % (SCF, BV))
    zp = linarith(w, H, [z2], '0 < Z', closure=c0); c0.have('Z', 'gt0', zp)
    vp = linarith(w, H, [v1], '0 < ( V + 2 )', closure=c0); c0.have('( V + 2 )', 'gt0', vp)
    cbr = c0.mem(CB, 'RR'); bvr = c0.mem(BV, 'RR')
    def jsum(X, xr, xl, C, cr, name):
        le = s([fin, xr, lift(w, cr, PJ), xl], 'fsumle', 'sum_ j e. J %s <_ sum_ j e. J %s' % (X, C))
        fc = s([fin, s([cr], 'recnd', '%s e. CC' % C), w.inst('fsumconst')], 'syl2anc', 'sum_ j e. J %s = ( ( # ` J ) x. %s )' % (C, C))
        f13 = s([fc, s([card], 'oveq1d', '( ( # ` J ) x. %s ) = ( %s x. %s )' % (C, N13, C))], 'eqtrd', 'sum_ j e. J %s = ( %s x. %s )' % (C, N13, C))
        return s([le, f13], 'breqtrd', 'sum_ j e. J %s <_ ( %s x. %s )' % (X, N13, C))
    sB = jsum(SBF, sbr, sbl, CB, cbr, 'B'); sC = jsum(SCF, scr, scl, BV, bvr, 'C')
    # pairs
    PJLK = '( %s /\\ k e. NN )' % PJL
    pjlk = c(PJLK)
    fj4 = {k_: lift(w, v_, PJLK) for k_, v_ in fj2.items()}; fj4['v'] = pjlk([], 'simpr', 'k e. NN')
    fl4 = {k_: lift(w, v_, PJLK) for k_, v_ in fl2.items()}; fl4['v'] = fj4['v']
    awr4, _, vj4 = pt(PJLK, MJ_, 'j', IMJ, 'k', fj4)
    _, _, vl4 = pt(PJLK, ML_, 'l', IML, 'k', fl4)
    ee4 = pjlk([pjlk([pjlk([awr4], 'recnd', '%s e. CC' % AW('k')), pjlk([vj4, pjlk([vl4], 'cjcld', '( * ` %s ) e. CC' % VL('k'))], 'mulcld', '( %s x. ( * ` %s ) ) e. CC' % (VJ('k'), VL('k')))],
                        'mulcld', '( %s x. ( %s x. ( * ` %s ) ) ) e. CC' % (AW('k'), VJ('k'), VL('k')))], 'recld', '%s e. RR' % EE('k'))
    fe4 = fv2(PJLK, EE('n'), EE('k'), ee4, fj4['v'])
    SEF = 'sum_ k e. NN ( %s ` k )' % FE
    SE0 = ere.rsplit(' e. RR', 1)[0]
    eqe = pjl([fe4], 'sumeq2dv', '%s = %s' % (SEF, SE0))
    CE = '( %s x. ( 2 x. %s ) )' % (KLAN, LL_)
    ser = pjl([eqe, T2[ere]], 'eqeltrd', '%s e. RR' % SEF); sel = pjl([eqe, T2[ele]], 'eqbrtrd', '%s <_ %s' % (SEF, CE))
    PJ_L = '( %s /\\ l e. %s )' % (PJ, JLm)
    q = c(PJ_L)
    tr_ = q([q([], 'simpll', H), q([q([], 'simplr', 'j e. J'), q([], 'simpr', 'l e. %s' % JLm)], 'jca', '( j e. J /\\ l e. %s )' % JLm)], 'jca', PJL)
    ser2 = q([tr_, ser], 'syl', '%s e. RR' % SEF); sel2 = q([tr_, sel], 'syl', '%s <_ %s' % (SEF, CE))
    cer = c0.mem(CE, 'RR')
    finl = pj([lift(w, fin, PJ), w.inst('diffi')], 'syl', '%s e. Fin' % JLm)
    lel = pj([finl, ser2, lift(w, cer, PJ_L), sel2], 'fsumle', 'sum_ l e. %s %s <_ sum_ l e. %s %s' % (JLm, SEF, JLm, CE))
    fcl = pj([finl, lift(w, s([cer], 'recnd', '%s e. CC' % CE), PJ), w.inst('fsumconst')], 'syl2anc', 'sum_ l e. %s %s = ( ( # ` %s ) x. %s )' % (JLm, CE, JLm, CE))
    hd = pj([lift(w, fin, PJ), pj([], 'simpr', 'j e. J'), w.inst('hashdifsn')], 'syl2anc', '( # ` %s ) = ( ( # ` J ) - 1 )' % JLm)
    hd2 = pj([hd, pj([lift(w, card, PJ)], 'oveq1d', '( ( # ` J ) - 1 ) = ( %s - 1 )' % N13)], 'eqtrd', '( # ` %s ) = ( %s - 1 )' % (JLm, N13))
    C12 = '( ( %s - 1 ) x. %s )' % (N13, CE)
    fcl2 = pj([fcl, pj([hd2], 'oveq1d', '( ( # ` %s ) x. %s ) = %s' % (JLm, CE, C12))], 'eqtrd', 'sum_ l e. %s %s = %s' % (JLm, CE, C12))
    SLF = 'sum_ l e. %s %s' % (JLm, SEF)
    lel2 = pj([lel, fcl2], 'breqtrd', '%s <_ %s' % (SLF, C12))
    slr = pj([finl, ser2], 'fsumrecl', '%s e. RR' % SLF)
    c12r = c0.mem(C12, 'RR')
    sE = jsum(SLF, slr, lel2, C12, c12r, 'E')
    # ---- the arithmetic
    d0 = c0.mem('D', 'RR+')
    dn0 = s([drp], 'rpne0d', 'D =/= 0')
    dc = c0.mem('D', 'CC')
    F54 = '( 5 / 4 )'
    e54 = s([c0.mem(F54, 'CC'), c0.mem('3', 'CC'), dc, s([], '3ne0', '3 =/= 0') if False else s([w.s([], '3ne0', '3 =/= 0')], 'a1i', '3 =/= 0'), dn0], 'divdiv1d',
            '( ( %s / 3 ) / D ) = ( %s / ( 3 x. D ) )' % (F54, F54))
    e54b = s([c0.mem('( %s / 3 )' % F54, 'CC'), dc, dn0], 'divrecd', '( ( %s / 3 ) / D ) = ( ( %s / 3 ) x. ( 1 / D ) )' % (F54, F54))
    eq5 = s([e54, e54b], 'eqtr3d', '( %s / ( 3 x. D ) ) = ( ( %s / 3 ) x. ( 1 / D ) )' % (F54, F54))
    e14 = s([c0.mem('1', 'CC'), c0.mem('4', 'CC'), dc, s([w.s([], '4ne0', '4 =/= 0')], 'a1i', '4 =/= 0'), dn0], 'divdiv1d', '( ( 1 / 4 ) / D ) = ( 1 / ( 4 x. D ) )')
    e14b = s([c0.mem('( 1 / 4 )', 'CC'), dc, dn0], 'divrecd', '( ( 1 / 4 ) / D ) = ( ( 1 / 4 ) x. ( 1 / D ) )')
    eq1 = s([e14, e14b], 'eqtr3d', '( 1 / ( 4 x. D ) ) = ( ( 1 / 4 ) x. ( 1 / D ) )')
    for at in (SAF, 'sum_ j e. J %s' % SBF, 'sum_ j e. J %s' % SCF, 'sum_ j e. J %s' % SLF, LL_, '( 1 / D )', '( %s / ( 3 x. D ) )' % F54, '( 1 / ( 4 x. D ) )'):
        c0.atom(at)
    for at, st in (('sum_ j e. J %s' % SBF, s([fin, sbr], 'fsumrecl', 'sum_ j e. J %s e. RR' % SBF)), ('sum_ j e. J %s' % SCF, s([fin, scr], 'fsumrecl', 'sum_ j e. J %s e. RR' % SCF)),
                   ('sum_ j e. J %s' % SLF, s([fin, slr], 'fsumrecl', 'sum_ j e. J %s e. RR' % SLF)), (SAF, safr)):
        c0.have(at, 'RR', st)
    K338 = dec('5915000000')
    G1 = '( ( 2 / 3 ) x. ( 1 / D ) ) <_ ( ; 7 0 + ( %s x. %s ) )' % (K338, LL_)
    st1 = nlinarith(w, H, [lim, sab, sB, sC, sE, eq5, eq1], G1, closure=c0)
    # L >_ 1
    WZ = '( Z x. ( V + 2 ) )'
    six = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), zr, s([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), c0.mem('( V + 2 )', 'RR'),
             s([w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), c0.ge0('3'), z2, linarith(w, H, [v1], '3 <_ ( V + 2 )', closure=c0)], 'lemul12ad',
            '( 2 x. 3 ) <_ %s' % WZ)
    e3 = s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )'), w.inst('simpri')], 'ax-mp', '_e < 3') if False else w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')
    e3h = s([e3], 'a1i', '_e < 3')
    c0.have('_e', 'RR', s([w.s([], 'ere', '_e e. RR')], 'a1i', '_e e. RR'))
    c0.atom(WZ)
    c0.have(WZ, 'RR', c0.mem(WZ, 'RR'))
    ele = linarith(w, H, [six, e3h], '_e <_ %s' % WZ, closure=c0)
    lg = s([ele, s([s([w.s([], 'epr', '_e e. RR+')], 'a1i', '_e e. RR+'), c0.mem(WZ, 'RR+')], 'logled', '( _e <_ %s <-> ( log ` _e ) <_ %s )' % (WZ, LL_))], 'mpbid', '( log ` _e ) <_ %s' % LL_)
    l1 = s([s([w.s([], 'loge', '( log ` _e ) = 1')], 'a1i', '( log ` _e ) = 1'), lg], 'eqbrtrrd', '1 <_ %s' % LL_)
    dq = s([dc, dn0], 'recidd', '( D x. ( 1 / D ) ) = 1')
    d0s = s([d0], 'rpge0d', '0 <_ D')
    bad = nlinarith(w, H, [st1, d0s, dq, dl, l1], '1 <_ 0', closure=c0)
    nb = s([s([w.s([], '0lt1', '0 < 1')], 'a1i', '0 < 1'), s([c0.mem('0', 'RR'), c0.mem('1', 'RR')], 'ltnled', '( 0 < 1 <-> -. 1 <_ 0 )')], 'mpbid', '-. 1 <_ 0')
    w.qed([bad, nb], 'pm2.65i', S['cen2n13'])
    return run(w)


if __name__ == '__main__':
    gen_n13()
