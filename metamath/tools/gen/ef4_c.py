"""Sortie EF4: conjugation (ef4cjd, ef4cjh: the reflected function conj F conj is holomorphic with the conjugated
derivative; ef4ddc: Lean DiskData.conj; ef4ghb: exists_good_height below the axis)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
from c8_o import numst
import congr as _cg
import lin
lin.FASTPATH = True

K_ = '( TopOpen ` CCfld )'
WS = '( * ` W )'


def gen_cjd():
    w = W('ef4cjd', 'The derivative of the reflected function ` e |-> * F ( * e ) ` at ` W ` is ` * F \' ( * W ) ` (Lean ` deriv_conj_conj ` ; the difference quotient is the conjugate of that of ` F ` at ` * W ` , ~ limcco twice).')
    A0, G = ante_of(S['ef4cjd'])
    c = Ctx(w, A0)
    ff = c.g('F : %s --> CC' % HP0); win = c.g('W e. %s' % HP0); wd = c.g('%s e. dom ( CC _D F )' % WS)
    wc, w0, _ = hp0_facts(c, 'W', win)
    wsh = hp0_cj(c, 'W', win)
    wsc = c([wc], 'cjcld', '%s e. CC' % WS)
    # HP0 C_ CC
    Az = '( %s /\\ z e. %s )' % (A0, HP0)
    cz = Ctx(w, Az)
    zc_, _, _ = hp0_facts(cz, 'z', cz([], 'simpr', 'z e. %s' % HP0))
    hpc = c([w.s([zc_], 'ex', '( %s -> ( z e. %s -> z e. CC ) )' % (A0, HP0))], 'ssrdv', '%s C_ CC' % HP0)
    DF = '( ( CC _D F ) ` %s )' % WS
    # 1. F has derivative DF at W*
    fun = c.a1(w.s([w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D F )'), 'Fun ( CC _D F )')
    r1 = c([wd, c([fun, w.inst('funfvbrb')], 'syl', '( %s e. dom ( CC _D F ) <-> %s ( CC _D F ) %s )' % (WS, WS, DF))], 'mpbid', '%s ( CC _D F ) %s' % (WS, DF))
    dfc = c([c.a1(w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), '( CC _D F ) : dom ( CC _D F ) --> CC'), wd], 'ffvelcdmd', '%s e. CC' % DF)
    tk = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (K_, K_))], 'eqcomi', '%s = ( %s |`t CC )' % (K_, K_))
    kk = w.s([], 'eqid', '%s = %s' % (K_, K_))
    GFB = lambda y: '( ( ( F ` %s ) - ( F ` %s ) ) / ( %s - %s ) )' % (y, WS, y, WS)
    GF = '( y e. ( %s \\ { %s } ) |-> %s )' % (HP0, WS, GFB('y'))
    INT = '( ( int ` %s ) ` %s )' % (K_, HP0)
    e1 = c([tk, kk, w.s([], 'eqid', '%s = %s' % (GF, GF)), c([], 'ssidd', 'CC C_ CC'), ff, hpc], 'eldv',
           '( %s ( CC _D F ) %s <-> ( %s e. %s /\\ %s e. ( %s limCC %s ) ) )' % (WS, DF, WS, INT, DF, GF, WS))
    l1 = c([c([r1, e1], 'mpbid', '( %s e. %s /\\ %s e. ( %s limCC %s ) )' % (WS, INT, DF, GF, WS)), w.inst('simpr')], 'syl', '%s e. ( %s limCC %s )' % (DF, GF, WS))
    # 2. the conjugation map tends to W* at W
    HW = '( %s \\ { W } )' % HP0
    idc = c([c([hpc, c([], 'ssidd', 'CC C_ CC')], 'jca', '( %s C_ CC /\\ CC C_ CC )' % HP0), w.inst('cncfmptid')], 'syl', '( z e. %s |-> z ) e. ( %s -cn-> CC )' % (HP0, HP0))
    cjm = c([c.a1(w.s([], 'cjcncf', '* e. ( CC -cn-> CC )'), '* e. ( CC -cn-> CC )'), idc], 'cncfmpt1f', '( z e. %s |-> ( * ` z ) ) e. ( %s -cn-> CC )' % (HP0, HP0))
    fz = w.s([], 'fveq2', '( z = W -> ( * ` z ) = %s )' % WS)
    lc = c([cjm, win, fz], 'cnmptlimc', '%s e. ( ( z e. %s |-> ( * ` z ) ) limCC W )' % (WS, HP0))
    rs = w.s([w.s([], 'difss', '%s C_ %s' % (HW, HP0)), w.inst('resmpt')], 'ax-mp', '( ( z e. %s |-> ( * ` z ) ) |` %s ) = ( z e. %s |-> ( * ` z ) )' % (HP0, HW, HW))
    lr = c.a1(w.s([], 'limcresi', '( ( z e. %s |-> ( * ` z ) ) limCC W ) C_ ( ( ( z e. %s |-> ( * ` z ) ) |` %s ) limCC W )' % (HP0, HP0, HW)),
              '( ( z e. %s |-> ( * ` z ) ) limCC W ) C_ ( ( ( z e. %s |-> ( * ` z ) ) |` %s ) limCC W )' % (HP0, HP0, HW))
    lc2 = c([lr, lc], 'sseldd', '%s e. ( ( ( z e. %s |-> ( * ` z ) ) |` %s ) limCC W )' % (WS, HP0, HW))
    lc3 = c([lc2, c([c.a1(rs, '( ( z e. %s |-> ( * ` z ) ) |` %s ) = ( z e. %s |-> ( * ` z ) )' % (HP0, HW, HW))], 'oveq1d',
                     '( ( ( z e. %s |-> ( * ` z ) ) |` %s ) limCC W ) = ( ( z e. %s |-> ( * ` z ) ) limCC W )' % (HP0, HW, HW))], 'eleqtrd', '%s e. ( ( z e. %s |-> ( * ` z ) ) limCC W )' % (WS, HW))
    # 3. composition: GF ( * z ) -> DF
    ZS_ = '( * ` z )'
    A2 = '( %s /\\ ( z e. %s /\\ %s =/= %s ) )' % (A0, HW, ZS_, WS)
    c2 = Ctx(w, A2)
    zin2 = c2([c2([], 'simprl', 'z e. %s' % HW), w.inst('eldifi')], 'syl', 'z e. %s' % HP0)
    zs2 = hp0_cj(c2, 'z', zin2)
    rr = c2([zs2, c2([], 'simprr', '%s =/= %s' % (ZS_, WS))], 'eldifsnd', '%s e. ( %s \\ { %s } )' % (ZS_, HP0, WS))
    Ay = '( %s /\\ y e. ( %s \\ { %s } ) )' % (A0, HP0, WS)
    cy = Ctx(w, Ay)
    yd = cy([], 'simpr', 'y e. ( %s \\ { %s } )' % (HP0, WS))
    yh = cy([yd, w.inst('eldifi')], 'syl', 'y e. %s' % HP0)
    yne = cy([yd, w.inst('eldifsni')], 'syl', 'y =/= %s' % WS)
    yc_, _, _ = hp0_facts(cy, 'y', yh)
    ffy = lift(w, ff, Ay)
    sy = cy([cy([cy([ffy, yh], 'ffvelcdmd', '( F ` y ) e. CC'), cy([ffy, lift(w, wsh, Ay)], 'ffvelcdmd', '( F ` %s ) e. CC' % WS)], 'subcld', '( ( F ` y ) - ( F ` %s ) ) e. CC' % WS),
             cy([yc_, lift(w, wsc, Ay)], 'subcld', '( y - %s ) e. CC' % WS), cy([yc_, lift(w, wsc, Ay), yne], 'subne0d', '( y - %s ) =/= 0' % WS)], 'divcld', '%s e. CC' % GFB('y'))
    st1, T1 = subst(w, GFB('y'), 'y', ZS_)
    A3 = '( %s /\\ ( z e. %s /\\ %s = %s ) )' % (A0, HW, ZS_, WS)
    c3 = Ctx(w, A3)
    zd3 = c3([], 'simprl', 'z e. %s' % HW)
    zc3, _, _ = hp0_facts(c3, 'z', c3([zd3, w.inst('eldifi')], 'syl', 'z e. %s' % HP0))
    zw = c3([c3([], 'simprr', '%s = %s' % (ZS_, WS)), c3([zc3, lift(w, wc, A3), w.inst('cj11')], 'syl2anc', '( %s = %s <-> z = W )' % (ZS_, WS))], 'mpbid', 'z = W')
    znw = c3([zd3, w.inst('eldifsni')], 'syl', 'z =/= W')
    t2 = c3([zw, znw], 'pm2.21ddne', '%s = %s' % (T1, DF))
    co1 = c([rr, sy, lc3, l1, st1, t2], 'limcco', '%s e. ( ( z e. %s |-> %s ) limCC W )' % (DF, HW, T1))
    # 4. conjugate
    A4 = '( %s /\\ ( z e. %s /\\ %s =/= %s ) )' % (A0, HW, T1, DF)
    c4 = Ctx(w, A4)
    zd4 = c4([], 'simprl', 'z e. %s' % HW)
    zh4 = c4([zd4, w.inst('eldifi')], 'syl', 'z e. %s' % HP0)
    zc4, _, _ = hp0_facts(c4, 'z', zh4)
    zs4 = hp0_cj(c4, 'z', zh4)
    zsc4 = c4([zc4], 'cjcld', '%s e. CC' % ZS_)
    znw4 = c4([zd4, w.inst('eldifsni')], 'syl', 'z =/= W')
    cjne = c4([znw4, c4([c4([zc4, lift(w, wc, A4), w.inst('cj11')], 'syl2anc', '( %s = %s <-> z = W )' % (ZS_, WS))], 'necon3bid', '( %s =/= %s <-> z =/= W )' % (ZS_, WS))], 'mpbird', '%s =/= %s' % (ZS_, WS))
    ff4 = lift(w, ff, A4)
    r4 = c4([c4([c4([ff4, zs4], 'ffvelcdmd', '( F ` %s ) e. CC' % ZS_), c4([ff4, lift(w, wsh, A4)], 'ffvelcdmd', '( F ` %s ) e. CC' % WS)], 'subcld', '( ( F ` %s ) - ( F ` %s ) ) e. CC' % (ZS_, WS)),
             c4([zsc4, lift(w, wsc, A4)], 'subcld', '( %s - %s ) e. CC' % (ZS_, WS)), c4([zsc4, lift(w, wsc, A4), cjne], 'subne0d', '( %s - %s ) =/= 0' % (ZS_, WS))], 'divcld', '%s e. CC' % T1)
    Ay2 = '( %s /\\ y e. CC )' % A0
    sy2 = w.s([w.s([], 'simpr', '( %s -> y e. CC )' % Ay2)], 'cjcld', '( %s -> ( * ` y ) e. CC )' % Ay2)
    idc2 = c([c([c([], 'ssidd', 'CC C_ CC'), c([], 'ssidd', 'CC C_ CC')], 'jca', '( CC C_ CC /\\ CC C_ CC )'), w.inst('cncfmptid')], 'syl', '( y e. CC |-> y ) e. ( CC -cn-> CC )')
    cjm2 = c([c.a1(w.s([], 'cjcncf', '* e. ( CC -cn-> CC )'), '* e. ( CC -cn-> CC )'), idc2], 'cncfmpt1f', '( y e. CC |-> ( * ` y ) ) e. ( CC -cn-> CC )')
    ld2 = c([cjm2, dfc, w.s([], 'fveq2', '( y = %s -> ( * ` y ) = ( * ` %s ) )' % (DF, DF))], 'cnmptlimc', '( * ` %s ) e. ( ( y e. CC |-> ( * ` y ) ) limCC %s )' % (DF, DF))
    A5 = '( %s /\\ ( z e. %s /\\ %s = %s ) )' % (A0, HW, T1, DF)
    t5 = w.s([w.s([], 'simprr', '( %s -> %s = %s )' % (A5, T1, DF))], 'fveq2d', '( %s -> ( * ` %s ) = ( * ` %s ) )' % (A5, T1, DF))
    co2 = c([r4, sy2, co1, ld2, w.s([], 'fveq2', '( y = %s -> ( * ` y ) = ( * ` %s ) )' % (T1, T1)), t5], 'limcco',
            '( * ` %s ) e. ( ( z e. %s |-> ( * ` %s ) ) limCC W )' % (DF, HW, T1))
    # 5. the difference quotient of CJ
    CJF = CJ()
    GCB = '( ( ( %s ` z ) - ( %s ` W ) ) / ( z - W ) )' % (CJF, CJF)
    A6 = '( %s /\\ z e. %s )' % (A0, HW)
    c6 = Ctx(w, A6)
    zd6 = c6([], 'simpr', 'z e. %s' % HW)
    zh6 = c6([zd6, w.inst('eldifi')], 'syl', 'z e. %s' % HP0)
    zc6, _, _ = hp0_facts(c6, 'z', zh6)
    zs6 = hp0_cj(c6, 'z', zh6)
    zsc6 = c6([zc6], 'cjcld', '%s e. CC' % ZS_)
    znw6 = c6([zd6, w.inst('eldifsni')], 'syl', 'z =/= W')
    cjne6 = c6([znw6, c6([c6([zc6, lift(w, wc, A6), w.inst('cj11')], 'syl2anc', '( %s = %s <-> z = W )' % (ZS_, WS))], 'necon3bid', '( %s =/= %s <-> z =/= W )' % (ZS_, WS))], 'mpbird', '%s =/= %s' % (ZS_, WS))
    ff6 = lift(w, ff, A6)
    fz6 = c6([ff6, zs6], 'ffvelcdmd', '( F ` %s ) e. CC' % ZS_)
    fw6 = c6([ff6, lift(w, wsh, A6)], 'ffvelcdmd', '( F ` %s ) e. CC' % WS)
    NUM = '( ( F ` %s ) - ( F ` %s ) )' % (ZS_, WS)
    DEN = '( %s - %s )' % (ZS_, WS)
    numc = c6([fz6, fw6], 'subcld', '%s e. CC' % NUM)
    denc = c6([zsc6, lift(w, wsc, A6)], 'subcld', '%s e. CC' % DEN)
    den0 = c6([zsc6, lift(w, wsc, A6), cjne6], 'subne0d', '%s =/= 0' % DEN)
    q1 = c6([numc, denc, den0], 'cjdivd', '( * ` %s ) = ( ( * ` %s ) / ( * ` %s ) )' % (T1, NUM, DEN))
    q2 = c6([fz6, fw6, w.inst('cjsub')], 'syl2anc', '( * ` %s ) = ( ( * ` ( F ` %s ) ) - ( * ` ( F ` %s ) ) )' % (NUM, ZS_, WS))
    q3 = c6([c6([zsc6, lift(w, wsc, A6), w.inst('cjsub')], 'syl2anc', '( * ` %s ) = ( ( * ` %s ) - ( * ` %s ) )' % (DEN, ZS_, WS)),
             c6([c6([zc6], 'cjcjd', '( * ` %s ) = z' % ZS_), c6([lift(w, wc, A6)], 'cjcjd', '( * ` %s ) = W' % WS)], 'oveq12d', '( ( * ` %s ) - ( * ` %s ) ) = ( z - W )' % (ZS_, WS))], 'eqtrd',
            '( * ` %s ) = ( z - W )' % DEN)
    BODY = '( * ` ( F ` ( * ` e ) ) )'
    vz, vzv = _cg.mptval(w, A6, 'e', HP0, BODY, 'z', zh6, gen=w.g)
    vw, vwv = _cg.mptval(w, A6, 'e', HP0, BODY, 'W', lift(w, win, A6), gen=w.g)
    q4 = c6([vz, vw], 'oveq12d', '( ( %s ` z ) - ( %s ` W ) ) = ( %s - %s )' % (CJF, CJF, vzv, vwv))
    q5 = c6([q1, c6([q2, q3], 'oveq12d', '( ( * ` %s ) / ( * ` %s ) ) = ( ( ( * ` ( F ` %s ) ) - ( * ` ( F ` %s ) ) ) / ( z - W ) )' % (NUM, DEN, ZS_, WS))], 'eqtrd',
            '( * ` %s ) = ( ( ( * ` ( F ` %s ) ) - ( * ` ( F ` %s ) ) ) / ( z - W ) )' % (T1, ZS_, WS))
    q6 = c6([q5, c6([c6([q4], 'eqcomd', '( %s - %s ) = ( ( %s ` z ) - ( %s ` W ) )' % (vzv, vwv, CJF, CJF))], 'oveq1d',
                    '( ( %s - %s ) / ( z - W ) ) = %s' % (vzv, vwv, GCB))], 'eqtrd', '( * ` %s ) = %s' % (T1, GCB))
    meq = c([q6], 'mpteq2dva', '( z e. %s |-> ( * ` %s ) ) = ( z e. %s |-> %s )' % (HW, T1, HW, GCB))
    GC = '( z e. %s |-> %s )' % (HW, GCB)
    co3 = c([co2, c([meq], 'oveq1d', '( ( z e. %s |-> ( * ` %s ) ) limCC W ) = ( %s limCC W )' % (HW, T1, GC))], 'eleqtrd', '( * ` %s ) e. ( %s limCC W )' % (DF, GC))
    # 6. eldv for CJ
    Ae = '( %s /\\ e e. %s )' % (A0, HP0)
    ce = Ctx(w, Ae)
    eh = ce([], 'simpr', 'e e. %s' % HP0)
    esh = hp0_cj(ce, 'e', eh)
    fe = ce([ce([lift(w, ff, Ae), esh], 'ffvelcdmd', '( F ` ( * ` e ) ) e. CC')], 'cjcld', '%s e. CC' % BODY)
    cjf = c([fe, w.s([], 'eqid', '%s = %s' % (CJF, CJF))], 'fmptd', '%s : %s --> CC' % (CJF, HP0))
    e2 = c([tk, kk, w.s([], 'eqid', '%s = %s' % (GC, GC)), c([], 'ssidd', 'CC C_ CC'), cjf, hpc], 'eldv',
           '( W ( CC _D %s ) ( * ` %s ) <-> ( W e. %s /\\ ( * ` %s ) e. ( %s limCC W ) ) )' % (CJF, DF, INT, DF, GC))
    io = c.a1(w.s([w.s([w.s([], 'eqid', '%s = %s' % (K_, K_))], 'cnfldtop', '%s e. Top' % K_), w.s([], 'hpopn', '%s e. %s' % (HP0, K_)), w.inst('isopn3i')], 'mp2an', '%s = %s' % (INT, HP0)), '%s = %s' % (INT, HP0))
    wi = c([win, c([io], 'eqcomd', '%s = %s' % (HP0, INT))], 'eleqtrd', 'W e. %s' % INT)
    w.qed([c([wi, co3], 'jca', '( W e. %s /\\ ( * ` %s ) e. ( %s limCC W ) )' % (INT, DF, GC)), e2], 'mpbird', S['ef4cjd'])
    return run8(w)



def gen_cjh():
    w = W('ef4cjh', 'The reflected function ` e |-> * F ( * e ) ` of a function holomorphic on the right half-plane is holomorphic there, with derivative ` * F \' ( * b ) ` at ` b ` (Lean ` DiskData.conj ` , ` hf.diff ` part; ~ ef4cjd ).')
    A0, G = ante_of(S['ef4cjh'])
    c = Ctx(w, A0)
    fcn = c.g('F e. ( %s -cn-> CC )' % HP0); dom = c.g('%s C_ dom ( CC _D F )' % HP0)
    ff = c([fcn, w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0)
    CJF = CJ()
    Ae = '( %s /\\ e e. %s )' % (A0, HP0)
    ce = Ctx(w, Ae)
    eh = ce([], 'simpr', 'e e. %s' % HP0)
    esh = hp0_cj(ce, 'e', eh)
    Az = '( %s /\\ z e. %s )' % (A0, HP0)
    cz = Ctx(w, Az)
    zc_, _, _ = hp0_facts(cz, 'z', cz([], 'simpr', 'z e. %s' % HP0))
    hpc = c([w.s([zc_], 'ex', '( %s -> ( z e. %s -> z e. CC ) )' % (A0, HP0))], 'ssrdv', '%s C_ CC' % HP0)
    idc = c([c([hpc, c([], 'ssidd', 'CC C_ CC')], 'jca', '( %s C_ CC /\\ CC C_ CC )' % HP0), w.inst('cncfmptid')], 'syl', '( e e. %s |-> e ) e. ( %s -cn-> CC )' % (HP0, HP0))
    cje = c([c.a1(w.s([], 'cjcncf', '* e. ( CC -cn-> CC )'), '* e. ( CC -cn-> CC )'), idc], 'cncfmpt1f', '( e e. %s |-> ( * ` e ) ) e. ( %s -cn-> CC )' % (HP0, HP0))
    cjf = c([esh, w.s([], 'eqid', '( e e. %s |-> ( * ` e ) ) = ( e e. %s |-> ( * ` e ) )' % (HP0, HP0))], 'fmptd', '( e e. %s |-> ( * ` e ) ) : %s --> %s' % (HP0, HP0, HP0))
    cje2 = c([cjf, c([hpc, cje, w.inst('cncfcdm')], 'syl2anc', '( ( e e. %s |-> ( * ` e ) ) e. ( %s -cn-> %s ) <-> ( e e. %s |-> ( * ` e ) ) : %s --> %s )' % (HP0, HP0, HP0, HP0, HP0, HP0))],
             'mpbird', '( e e. %s |-> ( * ` e ) ) e. ( %s -cn-> %s )' % (HP0, HP0, HP0))
    fm = c([ff], 'feqmptd', 'F = ( y e. %s |-> ( F ` y ) )' % HP0)
    fcn2 = c([fm, fcn], 'eqeltrrd', '( y e. %s |-> ( F ` y ) ) e. ( %s -cn-> CC )' % (HP0, HP0))
    comp = c([w.s([], 'nfv', 'F/ e %s' % A0), cje2, fcn2, c([], 'ssidd', '%s C_ %s' % (HP0, HP0)), w.s([], 'fveq2', '( y = ( * ` e ) -> ( F ` y ) = ( F ` ( * ` e ) ) )')], 'cncfcompt2',
             '( e e. %s |-> ( F ` ( * ` e ) ) ) e. ( %s -cn-> CC )' % (HP0, HP0))
    cjcn = c([c.a1(w.s([], 'cjcncf', '* e. ( CC -cn-> CC )'), '* e. ( CC -cn-> CC )'), comp], 'cncfmpt1f', '%s e. ( %s -cn-> CC )' % (CJF, HP0))
    # derivative at each b
    Ab = '( %s /\\ b e. %s )' % (A0, HP0)
    cb = Ctx(w, Ab)
    bh = cb([], 'simpr', 'b e. %s' % HP0)
    bsh = hp0_cj(cb, 'b', bh)
    bsd = cb([lift(w, dom, Ab), bsh], 'sseldd', '( * ` b ) e. dom ( CC _D F )')
    CD = tsub(stmt('ef4cjd'), {'W': 'b'})
    cda, cdc = ante_of(CD)
    rel = cb([cb([cb([lift(w, ff, Ab), bh], 'jca', top_and(cda)[0]), bsd], 'jca', cda), w.inst('ef4cjd')], 'syl', cdc)
    DV = '( ( CC _D F ) ` ( * ` b ) )'
    bdm = cb([cb([cb.a1(w.s([], 'reldv', 'Rel ( CC _D %s )' % CJF), 'Rel ( CC _D %s )' % CJF), rel], 'jca', '( Rel ( CC _D %s ) /\\ b ( CC _D %s ) ( * ` %s ) )' % (CJF, CJF, DV)), w.inst('releldm')],
             'syl', 'b e. dom ( CC _D %s )' % CJF)
    domc = c([w.s([bdm], 'ex', '( %s -> ( b e. %s -> b e. dom ( CC _D %s ) ) )' % (A0, HP0, CJF))], 'ssrdv', '%s C_ dom ( CC _D %s )' % (HP0, CJF))
    fun = cb.a1(w.s([w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (CJF, CJF)), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D %s )' % CJF), 'Fun ( CC _D %s )' % CJF)
    val = cb([rel, cb([fun, w.inst('funbrfv')], 'syl', '( b ( CC _D %s ) ( * ` %s ) -> ( ( CC _D %s ) ` b ) = ( * ` %s ) )' % (CJF, DV, CJF, DV))], 'mpd', '( ( CC _D %s ) ` b ) = ( * ` %s )' % (CJF, DV))
    al = c([val], 'ralrimiva', 'A. b e. %s ( ( CC _D %s ) ` b ) = ( * ` %s )' % (HP0, CJF, DV))
    w.qed([c([c([cjcn, domc], 'jca', HOLF(CJF, HP0)), al], 'jca', G)], 'idi', S['ef4cjh'])
    return run8(w)



def RA(t):
    return '( ( 1 / 4 ) + ( _i x. ( %s - 3 ) ) )' % t


def RB(t):
    return '( ( ; 1 5 / 4 ) + ( _i x. ( %s + 3 ) ) )' % t


def cj_pt(c, x, y, xr, yr):
    """( A -> ( * ` ( x + ( _i x. y ) ) ) = ( x + ( _i x. -u y ) ) )"""
    w = c.w
    e1 = c([xr, yr, w.inst('cjreim')], 'syl2anc', '( * ` %s ) = ( %s - ( _i x. %s ) )' % (PTL(x, y), x, y))
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    yc = c([yr], 'recnd', '%s e. CC' % y)
    e2 = c([c([ic, yc], 'mulneg2d', '( _i x. -u %s ) = -u ( _i x. %s )' % (y, y))], 'oveq2d', '( %s + ( _i x. -u %s ) ) = ( %s + -u ( _i x. %s ) )' % (x, y, x, y))
    e3 = c([c([xr], 'recnd', '%s e. CC' % x), c([ic, yc], 'mulcld', '( _i x. %s ) e. CC' % y)], 'negsubd', '( %s + -u ( _i x. %s ) ) = ( %s - ( _i x. %s ) )' % (x, y, x, y))
    return c([e1, c([e2, e3], 'eqtrd', '( %s + ( _i x. -u %s ) ) = ( %s - ( _i x. %s ) )' % (x, y, x, y))], 'eqtr4d', '( * ` %s ) = %s' % (PTL(x, y), PTL(x, '-u ' + y)))


def gen_ddc():
    w = W('ef4ddc', 'Lean ` DiskData.conj ` : the reflected function ` e |-> * F ( * e ) ` satisfies ` DiskData ` with the same ` A ` (the rectangle ` RCT ( t ) ` reflects to ` RCT ( - t ) ` ; ~ ef4cjh ).')
    A00, G = ante_of(S['ef4ddc'])
    CJF = CJ()
    # the antecedent with its binders renamed ( t x w -> y o v )
    TB = lambda t, x: '( ( 1 / 4 ) <_ ( abs ` ( F ` %s ) ) /\\ A. %s e. %s ( abs ` ( F ` %s ) ) <_ ( ; 2 5 x. %s ) )' % (CT(t), x, RCT(t), x, XA(t))
    NZ = lambda v: 'A. %s e. %s ( 1 < ( Re ` %s ) -> ( F ` %s ) =/= 0 )' % (v, HP0, v, v)
    P3 = '( A. t e. RR %s /\\ %s )' % (TB('t', 'x'), NZ('w'))
    Q3 = '( A. y e. RR %s /\\ %s )' % (TB('y', 'o'), NZ('v'))
    A0 = '( %s /\\ ( A e. RR /\\ 1 <_ A ) /\\ %s )' % (HOLF('F', HP0), Q3)
    # equivalence P3 <-> Q3
    cb1, b1 = cbvral(w, 'RR', 't', 'y', TB('t', 'x'))
    AXI = 'A. x e. %s ( abs ` ( F ` x ) ) <_ ( ; 2 5 x. %s )' % (RCT('y'), XA('y'))
    cbo, _ = cbvral(w, RCT('y'), 'x', 'o', '( abs ` ( F ` x ) ) <_ ( ; 2 5 x. %s )' % XA('y'))
    i1 = w.s([cbo], 'anbi2i', '( ( ( 1 / 4 ) <_ ( abs ` ( F ` %s ) ) /\\ %s ) <-> %s )' % (CT('y'), AXI, TB('y', 'o')))
    i2 = w.s([i1], 'ralbii', '( A. y e. RR ( ( 1 / 4 ) <_ ( abs ` ( F ` %s ) ) /\\ %s ) <-> A. y e. RR %s )' % (CT('y'), AXI, TB('y', 'o')))
    i3 = w.s([cb1, i2], 'bitri', '( A. t e. RR %s <-> A. y e. RR %s )' % (TB('t', 'x'), TB('y', 'o')))
    cbw, _ = cbvral(w, HP0, 'w', 'v', '( 1 < ( Re ` w ) -> ( F ` w ) =/= 0 )')
    i4 = w.s([i3, cbw], 'anbi12i', '( %s <-> %s )' % (P3, Q3))
    c0 = Ctx(w, A00)
    a0 = c0([c0.g(HOLF('F', HP0)), c0.g('( A e. RR /\\ 1 <_ A )'), c0([c0.g(P3), c0.a1(i4, '( %s <-> %s )' % (P3, Q3))], 'mpbid', Q3)], '3jca', A0)
    c = Ctx(w, A0)
    hol = c.g(HOLF('F', HP0)); aa = c.g('( A e. RR /\\ 1 <_ A )')
    aly = c.g('A. y e. RR %s' % TB('y', 'o')); alv = c.g(NZ('v'))
    ch = c([hol, w.inst('ef4cjh')], 'syl', ante_of(stmt('ef4cjh'))[1])
    hcj = c([ch, w.inst('simpl')], 'syl', HOLF(CJF, HP0))
    ff = c([c([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0)
    BODY = '( * ` ( F ` ( * ` e ) ) )'
    # the t-clause
    At = '( %s /\\ t e. RR )' % A0
    ct = Ctx(w, At)
    L1 = lambda st: lift(w, st, At)
    tr = ct([], 'simpr', 't e. RR')
    ntr = ct([tr], 'renegcld', '-u t e. RR')
    fy, _ = ral_at(w, At, L1(aly), 'y', '-u t', TB('y', 'o'), ct([tr], 'renegcld', '-u t e. RR'))
    lo = ct([fy, w.inst('simpl')], 'syl', '( 1 / 4 ) <_ ( abs ` ( F ` %s ) )' % CT('-u t'))
    bd = ct([fy, w.inst('simpr')], 'syl', 'A. o e. %s ( abs ` ( F ` o ) ) <_ ( ; 2 5 x. %s )' % (RCT('-u t'), XA('-u t')))
    two = ct.a1(w.s([], '2re', '2 e. RR'), '2 e. RR')
    ctc = ptc_(ct, '2', 't', two, tr)
    cth = hp0_mem_re(ct, CT('t'), ctc, ct([two, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 2' % CT('t')), ct.a1(w.s([], '2pos', '0 < 2'), '0 < 2'))
    v1, v1v = _cg.mptval(w, At, 'e', HP0, BODY, CT('t'), cth, gen=w.g)
    cj1 = cj_pt(ct, '2', 't', two, tr)
    fcs = ct([cj1], 'fveq2d', '( F ` ( * ` %s ) ) = ( F ` %s )' % (CT('t'), CT('-u t')))
    fcc = ct([L1(ff), hp0_cj(ct, CT('t'), cth)], 'ffvelcdmd', '( F ` ( * ` %s ) ) e. CC' % CT('t'))
    ab1 = ct([ct([v1], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (CJF, CT('t'), v1v)),
              ct([ct([fcc, w.inst('abscj')], 'syl', '( abs ` %s ) = ( abs ` ( F ` ( * ` %s ) ) )' % (v1v, CT('t'))), ct([fcs], 'fveq2d', '( abs ` ( F ` ( * ` %s ) ) ) = ( abs ` ( F ` %s ) )' % (CT('t'), CT('-u t')))], 'eqtrd',
                 '( abs ` %s ) = ( abs ` ( F ` %s ) )' % (v1v, CT('-u t')))], 'eqtrd', '( abs ` ( %s ` %s ) ) = ( abs ` ( F ` %s ) )' % (CJF, CT('t'), CT('-u t')))
    low = ct([lo, ct([ab1], 'eqcomd', '( abs ` ( F ` %s ) ) = ( abs ` ( %s ` %s ) )' % (CT('-u t'), CJF, CT('t')))], 'breqtrd', '( 1 / 4 ) <_ ( abs ` ( %s ` %s ) )' % (CJF, CT('t')))
    # the rectangle clause
    Ax = '( %s /\\ x e. %s )' % (At, RCT('t'))
    cx = Ctx(w, Ax)
    L2 = lambda st: lift(w, st, Ax)
    xin = cx([], 'simpr', 'x e. %s' % RCT('t'))
    rc = cx([cx([L2(tr), xin], 'jca', '( t e. RR /\\ x e. %s )' % RCT('t')), w.inst('zc1rct')], 'syl', '( x e. %s /\\ ( 1 / 4 ) <_ ( Re ` x ) /\\ ( abs ` x ) <_ ( ( abs ` t ) + 7 ) )' % HP0)
    xh = cx([rc, w.inst('simp1')], 'syl', 'x e. %s' % HP0)
    xc, _, _ = hp0_facts(cx, 'x', xh)
    ra = ptc_(cx, '( 1 / 4 )', '( t - 3 )', numst(w, Ax, '( 1 / 4 )', 'RR'), cx([L2(tr), numst(w, Ax, '3', 'RR')], 'resubcld', '( t - 3 ) e. RR'))
    rb = ptc_(cx, '( ; 1 5 / 4 )', '( t + 3 )', numst(w, Ax, '( ; 1 5 / 4 )', 'RR'), cx([L2(tr), numst(w, Ax, '3', 'RR')], 'readdcld', '( t + 3 ) e. RR'))
    bnd = crect_bounds(w, Ax, ra, rb, xin, RA('t'), RB('t'), 'x')
    XS = '( * ` x )'
    xsc = cx([xc], 'cjcld', '%s e. CC' % XS)
    hy = list(bnd['le'])
    for x_, y_, st_x, st_y in (('( 1 / 4 )', '( t - 3 )', numst(w, Ax, '( 1 / 4 )', 'RR'), cx([L2(tr), numst(w, Ax, '3', 'RR')], 'resubcld', '( t - 3 ) e. RR')),
                               ('( ; 1 5 / 4 )', '( t + 3 )', numst(w, Ax, '( ; 1 5 / 4 )', 'RR'), cx([L2(tr), numst(w, Ax, '3', 'RR')], 'readdcld', '( t + 3 ) e. RR'))):
        hy.append(cx([st_x, st_y, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (PTL(x_, y_), x_)))
        hy.append(cx([st_x, st_y, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (PTL(x_, y_), y_)))
    hy.append(cx([xc, w.inst('recj')], 'syl', '( Re ` %s ) = ( Re ` x )' % XS))
    hy.append(cx([xc, w.inst('imcj')], 'syl', '( Im ` %s ) = -u ( Im ` x )' % XS))
    ntr2 = cx([L2(tr)], 'renegcld', '-u t e. RR')
    rna = ptc_(cx, '( 1 / 4 )', '( -u t - 3 )', numst(w, Ax, '( 1 / 4 )', 'RR'), cx([ntr2, numst(w, Ax, '3', 'RR')], 'resubcld', '( -u t - 3 ) e. RR'))
    rnb = ptc_(cx, '( ; 1 5 / 4 )', '( -u t + 3 )', numst(w, Ax, '( ; 1 5 / 4 )', 'RR'), cx([ntr2, numst(w, Ax, '3', 'RR')], 'readdcld', '( -u t + 3 ) e. RR'))
    for x_, y_, st_y in (('( 1 / 4 )', '( -u t - 3 )', cx([ntr2, numst(w, Ax, '3', 'RR')], 'resubcld', '( -u t - 3 ) e. RR')), ('( ; 1 5 / 4 )', '( -u t + 3 )', cx([ntr2, numst(w, Ax, '3', 'RR')], 'readdcld', '( -u t + 3 ) e. RR'))):
        hy.append(cx([numst(w, Ax, x_, 'RR'), st_y, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (PTL(x_, y_), x_)))
        hy.append(cx([numst(w, Ax, x_, 'RR'), st_y, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (PTL(x_, y_), y_)))
    lv = dict(bnd['cl']); lv['t'] = L2(tr)
    xsin = crect_in(w, Ax, RA('-u t'), RB('-u t'), rna, rnb, XS, xsc, hy, lv)
    fb, _ = ral_at(w, Ax, L2(bd), 'o', XS, '( abs ` ( F ` o ) ) <_ ( ; 2 5 x. %s )' % XA('-u t'), xsin)
    v2, v2v = _cg.mptval(w, Ax, 'e', HP0, BODY, 'x', xh, gen=w.g)
    fxc = cx([L2(ff), hp0_cj(cx, 'x', xh)], 'ffvelcdmd', '( F ` %s ) e. CC' % XS)
    ab2 = cx([cx([v2], 'fveq2d', '( abs ` ( %s ` x ) ) = ( abs ` %s )' % (CJF, v2v)), cx([fxc, w.inst('abscj')], 'syl', '( abs ` %s ) = ( abs ` ( F ` %s ) )' % (v2v, XS))], 'eqtrd',
             '( abs ` ( %s ` x ) ) = ( abs ` ( F ` %s ) )' % (CJF, XS))
    xa = cx([cx([cx([cx([L2(tr)], 'recnd', 't e. CC'), w.inst('absneg')], 'syl', '( abs ` -u t ) = ( abs ` t )')], 'oveq1d', '( ( abs ` -u t ) + 2 ) = ( ( abs ` t ) + 2 )')], 'oveq2d', '%s = %s' % (XA('-u t'), XA('t')))
    xa2 = cx([xa], 'oveq2d', '( ; 2 5 x. %s ) = ( ; 2 5 x. %s )' % (XA('-u t'), XA('t')))
    bx = cx([cx([ab2, fb], 'eqbrtrd', '( abs ` ( %s ` x ) ) <_ ( ; 2 5 x. %s )' % (CJF, XA('-u t'))), xa2], 'breqtrd', '( abs ` ( %s ` x ) ) <_ ( ; 2 5 x. %s )' % (CJF, XA('t')))
    alx = ct([bx], 'ralrimiva', 'A. x e. %s ( abs ` ( %s ` x ) ) <_ ( ; 2 5 x. %s )' % (RCT('t'), CJF, XA('t')))
    tb = ct([low, alx], 'jca', TB('t', 'x').replace('( F ` ', '( %s ` ' % CJF))
    alt = c([tb], 'ralrimiva', 'A. t e. RR %s' % TB('t', 'x').replace('( F ` ', '( %s ` ' % CJF))
    # the nonvanishing clause
    Aw = '( %s /\\ w e. %s )' % (A0, HP0)
    cw = Ctx(w, Aw)
    wh = cw([], 'simpr', 'w e. %s' % HP0)
    wcc, _, _ = hp0_facts(cw, 'w', wh)
    wsh = hp0_cj(cw, 'w', wh)
    Aw1 = '( %s /\\ 1 < ( Re ` w ) )' % Aw
    cw1 = Ctx(w, Aw1)
    r1 = cw1([cw1([], 'simpr', '1 < ( Re ` w )'), cw1([cw1([lift(w, wcc, Aw1), w.inst('recj')], 'syl', '( Re ` ( * ` w ) ) = ( Re ` w )')], 'eqcomd', '( Re ` w ) = ( Re ` ( * ` w ) )')], 'breqtrd', '1 < ( Re ` ( * ` w ) )')
    nzb, _ = ral_at(w, Aw1, lift(w, alv, Aw1), 'v', '( * ` w )', '( 1 < ( Re ` v ) -> ( F ` v ) =/= 0 )', lift(w, wsh, Aw1))
    fn0 = cw1([r1, nzb], 'mpd', '( F ` ( * ` w ) ) =/= 0')
    fwc = cw1([lift(w, ff, Aw1), lift(w, wsh, Aw1)], 'ffvelcdmd', '( F ` ( * ` w ) ) e. CC')
    v3, v3v = _cg.mptval(w, Aw1, 'e', HP0, BODY, 'w', lift(w, wh, Aw1), gen=w.g)
    cn0 = cw1([fwc, fn0], 'cjne0d', '( * ` ( F ` ( * ` w ) ) ) =/= 0')
    ne = cw1([v3, cn0], 'eqnetrd', '( %s ` w ) =/= 0' % CJF)
    alw = c([w.s([ne], 'ex', '( %s -> ( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 ) )' % (Aw, CJF))], 'ralrimiva', 'A. w e. %s ( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % (HP0, CJF))
    fin = c([hcj, aa, c([alt, alw], 'jca', top_and(G)[2])], '3jca', G)
    w.qed([a0, fin], 'syl', S['ef4ddc'])
    return run8(w)



def gen_ghb():
    w = W('ef4ghb', 'Lean ` exists_good_height hDD.conj ` (with ` norm_logDeriv_conjF ` ): a good height ` - u ` , ` u e. [ T , T + 1 ] ` , below the axis: ` F =/= 0 ` and ` abs ( F \' / F ) <_ 21000000 log ^ 2 ( A ( T + 4 ) ) ` on ` [ 1 / 2 , 3 ] - i u ` ( ~ ef2gh for the reflected function, ~ ef4ddc ).')
    A0, G = ante_of(S['ef4ghb'])
    c = Ctx(w, A0)
    CJF = CJ()
    dd = c.g(DD()); tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    hol = c([dd, w.inst('simp1')], 'syl', HOLF('F', HP0))
    ddc = c([dd, w.inst('ef4ddc')], 'syl', DD(CJF))
    ch = c([hol, w.inst('ef4cjh')], 'syl', ante_of(stmt('ef4cjh'))[1])
    dvv = c([ch, w.inst('simpr')], 'syl', top_and(ante_of(stmt('ef4cjh'))[1])[1])
    ff = c([c([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0)
    dom = c([hol, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D F )' % HP0)
    GH = tsub(stmt('ef2gh'), {'F': CJF})
    gha, ghc = ante_of(GH)
    gh = c([conj(w, A0, gha, {DD(CJF): ddc, 'T e. RR': tr, '2 <_ T': t2, top_and(gha)[1]: c.g(top_and(gha)[1])}), w.inst('ef2gh')], 'syl', ghc)
    SV, SVB = '( v + ( _i x. u ) )', '( v + ( _i x. -u u ) )'
    BC = GOOD(SV, CJF)
    BF = GOOD(SVB)
    Au = '( %s /\\ u e. ( T [,] ( T + 1 ) ) )' % A0
    Av = '( %s /\\ v e. ( ( 1 / 2 ) [,] 3 ) )' % Au
    Ab = '( %s /\\ %s )' % (Av, BC)
    cb = Ctx(w, Ab)
    L = lambda st: lift(w, st, Ab)
    uin = lift(w, w.s([], 'simpr', '( %s -> u e. ( T [,] ( T + 1 ) ) )' % Au), Ab)
    vin = lift(w, w.s([], 'simpr', '( %s -> v e. ( ( 1 / 2 ) [,] 3 ) )' % Av), Ab)
    t1r = cb([L(tr), numst(w, Ab, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    ur, _, _ = icc_out3(cb, 'u', 'T', '( T + 1 )', uin, L(tr), t1r)
    vr, v1, _ = icc_out3(cb, 'v', '( 1 / 2 )', '3', vin, numst(w, Ab, '( 1 / 2 )', 'RR'), numst(w, Ab, '3', 'RR'))
    svc = ptc_(cb, 'v', 'u', vr, ur)
    v0 = lin8(w, Ab, [v1], '0 < v', {'v': vr})
    svh = hp0_mem_re(cb, SV, svc, cb([vr, ur, w.inst('crre')], 'syl2anc', '( Re ` %s ) = v' % SV), v0)
    nur = cb([ur], 'renegcld', '-u u e. RR')
    svbc = ptc_(cb, 'v', '-u u', vr, nur)
    svbh = hp0_mem_re(cb, SVB, svbc, cb([vr, nur, w.inst('crre')], 'syl2anc', '( Re ` %s ) = v' % SVB), v0)
    cjs = cj_pt(cb, 'v', 'u', vr, ur)
    BODY = '( * ` ( F ` ( * ` e ) ) )'
    vl, vlv = _cg.mptval(w, Ab, 'e', HP0, BODY, SV, svh, gen=w.g)
    FB = '( F ` %s )' % SVB
    cv = cb([vl, cb([cb([cjs], 'fveq2d', '( F ` ( * ` %s ) ) = %s' % (SV, FB))], 'fveq2d', '%s = ( * ` %s )' % (vlv, FB))], 'eqtrd', '( %s ` %s ) = ( * ` %s )' % (CJF, SV, FB))
    dv, _ = ral_at(w, Ab, L(dvv), 'b', SV, '( ( CC _D %s ) ` b ) = ( * ` ( ( CC _D F ) ` ( * ` b ) ) )' % CJF, svh)
    DB = '( ( CC _D F ) ` %s )' % SVB
    dv2 = cb([dv, cb([cb([cjs], 'fveq2d', '( ( CC _D F ) ` ( * ` %s ) ) = %s' % (SV, DB))], 'fveq2d', '( * ` ( ( CC _D F ) ` ( * ` %s ) ) ) = ( * ` %s )' % (SV, DB))], 'eqtrd',
              '( ( CC _D %s ) ` %s ) = ( * ` %s )' % (CJF, SV, DB))
    bc = cb([], 'simpr', BC)
    cn0 = cb([bc, w.inst('simpl')], 'syl', '( %s ` %s ) =/= 0' % (CJF, SV))
    cb0 = cb([bc, w.inst('simpr')], 'syl', '( abs ` %s ) <_ ( %s x. ( %s ^ 2 ) )' % (LD(SV, CJF), KGH, LT4))
    fbc = cb([L(ff), svbh], 'ffvelcdmd', '%s e. CC' % FB)
    dbc = cb([cb.a1(w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), '( CC _D F ) : dom ( CC _D F ) --> CC'), cb([L(dom), svbh], 'sseldd', '%s e. dom ( CC _D F )' % SVB)], 'ffvelcdmd', '%s e. CC' % DB)
    sfn = cb([cn0, cb([cv], 'neeq1d', '( ( %s ` %s ) =/= 0 <-> ( * ` %s ) =/= 0 )' % (CJF, SV, FB))], 'mpbid', '( * ` %s ) =/= 0' % FB)
    fn0 = cb([sfn, cb([fbc, w.inst('cjne0')], 'syl', '( %s =/= 0 <-> ( * ` %s ) =/= 0 )' % (FB, FB))], 'mpbird', '%s =/= 0' % FB)
    Q = LD(SVB)
    qc = cb([dbc, fbc, fn0], 'divcld', '%s e. CC' % Q)
    q1 = cb([dbc, fbc, fn0], 'cjdivd', '( * ` %s ) = ( ( * ` %s ) / ( * ` %s ) )' % (Q, DB, FB))
    q2 = cb([dv2, cv], 'oveq12d', '%s = ( ( * ` %s ) / ( * ` %s ) )' % (LD(SV, CJF), DB, FB))
    q3 = cb([q1, q2], 'eqtr4d', '( * ` %s ) = %s' % (Q, LD(SV, CJF)))
    a1 = cb([cb([cb([qc, w.inst('abscj')], 'syl', '( abs ` ( * ` %s ) ) = ( abs ` %s )' % (Q, Q))], 'eqcomd', '( abs ` %s ) = ( abs ` ( * ` %s ) )' % (Q, Q)), cb([q3], 'fveq2d', '( abs ` ( * ` %s ) ) = ( abs ` %s )' % (Q, LD(SV, CJF)))], 'eqtrd',
            '( abs ` %s ) = ( abs ` %s )' % (Q, LD(SV, CJF)))
    b2 = cb([a1, cb0], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( %s ^ 2 ) )' % (Q, KGH, LT4))
    bf = cb([fn0, b2], 'jca', BF)
    im = w.s([bf], 'ex', '( %s -> ( %s -> %s ) )' % (Av, BC, BF))
    ri = w.s([im], 'ralimdva', '( %s -> ( A. v e. ( ( 1 / 2 ) [,] 3 ) %s -> A. v e. ( ( 1 / 2 ) [,] 3 ) %s ) )' % (Au, BC, BF))
    GAPF = 'A. g e. G ( 1 / ( %s x. %s ) ) <_ ( abs ` ( u - g ) )' % (GAP, LT4)
    an = w.s([ri], 'anim2d', '( %s -> ( ( %s /\\ A. v e. ( ( 1 / 2 ) [,] 3 ) %s ) -> ( %s /\\ A. v e. ( ( 1 / 2 ) [,] 3 ) %s ) ) )' % (Au, GAPF, BC, GAPF, BF))
    re_ = c([an], 'reximdva', '( E. u e. ( T [,] ( T + 1 ) ) ( %s /\\ A. v e. ( ( 1 / 2 ) [,] 3 ) %s ) -> %s )' % (GAPF, BC, G))
    w.qed([gh, re_], 'mpd', S['ef4ghb'])
    return run8(w)


def icc_out3(c, x, lo, hi, xin, lor, hir):
    w = c.w
    e = c([lor, hir, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (x, lo, hi, x, lo, x, x, hi))
    tri = c([xin, e], 'mpbid', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (x, lo, x, x, hi))
    return [c([tri, w.inst(k)], 'syl', f) for k, f in (('simp1', '%s e. RR' % x), ('simp2', '%s <_ %s' % (lo, x)), ('simp3', '%s <_ %s' % (x, hi)))]


def ptc_(c, x, y, xr, yr):
    return c([c([xr], 'recnd', '%s e. CC' % x), c([c.a1(c.w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c([yr], 'recnd', '%s e. CC' % y)], 'mulcld', '( _i x. %s ) e. CC' % y)], 'addcld', '%s e. CC' % PTL(x, y))


def hp0_mem_re(c, z, zc, rz, v0):
    """( A -> z e. HP0 ) from z e. CC, rz : Re z = v, v0 : 0 < v"""
    w = c.w
    v = body_of(w, rz).split(' = ', 1)[1]
    r0 = c([v0, c([rz], 'eqcomd', '%s = ( Re ` %s )' % (v, z))], 'breqtrd', '0 < ( Re ` %s )' % z)
    e = c([c.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (z, HP0, z, z))
    return c([c([zc, r0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (z, z)), e], 'mpbird', '%s e. %s' % (z, HP0))


GENS = {'ef4cjd': gen_cjd, 'ef4cjh': gen_cjh, 'ef4ddc': gen_ddc, 'ef4ghb': gen_ghb}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
