"""Sortie ZC1: E = ( s - 1 ) L ( s , chi ) for nonprincipal chi (zc1elf), same zeros and orders off 1 (zc1eord)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
import c9_h
patch(c9_h)
from c9_h import lf_hol
import zc1_i
import lin
lin.FASTPATH = True

Z1 = '( z e. %s |-> ( z - 1 ) )' % HP0
S['hsub1'] = HOLF(Z1, HP0)
S['zc1elf'] = '( ( %s /\\ S e. %s ) -> ( %s ` S ) = ( ( S - 1 ) x. ( %s ` S ) ) )' % (CHI, HP0, E, LFN)
S['zc1eord'] = '( ( %s /\\ ( P e. %s /\\ P =/= 1 ) ) -> ( ( %s holord P ) = ( %s holord P ) /\\ ( ( %s ` P ) = 0 <-> ( %s ` P ) = 0 ) ) )' % (CHI, HP0, E, LFN, E, LFN)
IFQ = 'if ( X = ( 0g ` ( DChr ` N ) ) , ( ( phi ` N ) / N ) , 0 )'


def gen_hsub1():
    w = W('hsub1', 'The mapping ` z |-> z - 1 ` is holomorphic on the right half-plane ( ~ dvmptid , ~ dvmptsub , ~ zl2hent ).')
    A0 = 'T.'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    Az = '( T. /\\ z e. CC )'
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    cc = s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', 'CC e. { RR , CC }')
    d2 = s([cc], 'dvmptid', '( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 )')
    d1 = s([cc, s([], '1cnd', '1 e. CC')], 'dvmptc', '( CC _D ( z e. CC |-> 1 ) ) = ( z e. CC |-> 0 )')
    zc = sz([], 'simpr', 'z e. CC'); one = sz([], '1cnd', '1 e. CC'); zero = sz([], '0cnd', '0 e. CC')
    dA = s([cc, zc, one, d2, one, zero, d1], 'dvmptsub', '( CC _D ( z e. CC |-> ( z - 1 ) ) ) = ( z e. CC |-> ( 1 - 0 ) )')
    dm = s([s([sz([one, zero], 'subcld', '( 1 - 0 ) e. CC')], 'ralrimiva', 'A. z e. CC ( 1 - 0 ) e. CC'), w.inst('dmmptg')], 'syl', 'dom ( z e. CC |-> ( 1 - 0 ) ) = CC')
    dmG = s([s([dA], 'dmeqd', 'dom ( CC _D ( z e. CC |-> ( z - 1 ) ) ) = dom ( z e. CC |-> ( 1 - 0 ) )'), dm], 'eqtrd', 'dom ( CC _D ( z e. CC |-> ( z - 1 ) ) ) = CC')
    gf = s([sz([zc, one], 'subcld', '( z - 1 ) e. CC')], 'fmptd', '( z e. CC |-> ( z - 1 ) ) : CC --> CC')
    ss = s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC')
    cn = s([s([ss, gf, ss], '3jca', '( CC C_ CC /\\ ( z e. CC |-> ( z - 1 ) ) : CC --> CC /\\ CC C_ CC )'), dmG, w.inst('dvcn')], 'syl2anc', '( z e. CC |-> ( z - 1 ) ) e. ( CC -cn-> CC )')
    dms = s([s([dmG], 'eqcomd', 'CC = dom ( CC _D ( z e. CC |-> ( z - 1 ) ) )')], 'eqimssd', 'CC C_ dom ( CC _D ( z e. CC |-> ( z - 1 ) ) )')
    hc = s([cn, dms], 'jca', HOLF('( z e. CC |-> ( z - 1 ) )', 'CC'))
    op = s([w.s([], 'hpopn', '%s e. ( TopOpen ` CCfld )' % HP0)], 'a1i', '%s e. ( TopOpen ` CCfld )' % HP0)
    h = s([s([hc, op], 'jca', ante_of(tsub(stmt('zl2hent'), {'A': '( z - 1 )', 'D': HP0}))[0]), w.inst('zl2hent')], 'syl', S['hsub1'])
    w.qed([h], 'mptru', S['hsub1'])
    return run8(w)


def gen_zc1elf():
    w = W('zc1elf', 'For ` chi ` nonprincipal, ` E = ( N DChrLF X ) ` is ` ( s - 1 ) L ( s , chi ) ` with C5\'s Abel series ` L ` ( ~ dchrlfval : the mean value is ` 0 ` ).')
    A0 = '( %s /\\ S e. %s )' % (CHI, HP0)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); sh = s([], 'simpr', 'S e. %s' % HP0)
    nx = s([chi, w.inst('simpl')], 'syl', NX); xne = s([chi, w.inst('simpr')], 'syl', 'X =/= ( 0g ` ( DChr ` N ) )')
    dv = s([nx, w.inst('dchrlfval')], 'syl', ante_of(stmt('dchrlfval'))[1])
    MAPE = ante_of(stmt('dchrlfval'))[1].split(' = ', 1)[1]
    BODY = MAPE[len('( s e. %s |-> ' % HP0):-2]
    VAL = tsub(BODY, {'s': 'S'})
    fv = s([dv], 'fveq1d', '( %s ` S ) = ( %s ` S )' % (E, MAPE))
    vx = s([w.s([], 'ovex', '%s e. _V' % VAL)], 'a1i', '%s e. _V' % VAL)
    mv, _ = _cg.mptval(w, A0, 's', HP0, BODY, 'S', sh, exs=vx, gen=w.g)
    iff = s([s([xne], 'neneqd', '-. X = ( 0g ` ( DChr ` N ) )')], 'iffalsed', '%s = 0' % IFQ)
    st, V0 = w.rewrite(VAL, {IFQ: ('0', iff)}, A0)
    el = ante_of(stmt('zl1zcl'))
    shc = s([sh, s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( S e. %s <-> ( S e. CC /\\ 0 < ( Re ` S ) ) )' % HP0)], 'mpbid', '( S e. CC /\\ 0 < ( Re ` S ) )')
    sc = s([shc, w.inst('simpl')], 'syl', 'S e. CC')
    HTS = tsub(el[1].rsplit(' e. CC', 1)[0], {'Z': 'S'})
    htc = s([shc, w.inst('zl1zcl')], 'syl', '%s e. CC' % HTS)
    Q = '( S + %s )' % HTS
    m0 = s([s([sc, htc], 'addcld', '%s e. CC' % Q)], 'mul02d', '( 0 x. %s ) = 0' % Q)
    # the Abel sums: ( X ( i ) - 0 ) = X ( i )
    Ak = '( %s /\\ k e. NN )' % A0
    Aki = '( %s /\\ i e. ( 1 ... k ) )' % Ak
    XI = '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` i ) )'
    CXm = '( a e. NN |-> ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` a ) ) )'
    iN = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... k ) )' % Aki), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Aki)
    CB = ante_of(stmt('zl1chrb'))[1]
    cb3 = w.s([lift(w, s([nx, w.inst('zl1chrb')], 'syl', CB), Aki), w.inst('simpl')], 'syl', '( %s -> %s )' % (Aki, top_and(CB)[0]))
    cxf = w.s([cb3, w.inst('simp1')], 'syl', '( %s -> %s : NN --> CC )' % (Aki, CXm))
    cxv = w.s([w.s([lift(w, nx, Aki), iN], 'jca', '( %s -> ( %s /\\ i e. NN ) )' % (Aki, NX)), w.inst('zl1cxv')], 'syl', '( %s -> ( %s ` i ) = %s )' % (Aki, CXm, XI))
    xic = w.s([cxv, w.s([cxf, iN], 'ffvelcdmd', '( %s -> ( %s ` i ) e. CC )' % (Aki, CXm))], 'eqeltrrd', '( %s -> %s e. CC )' % (Aki, XI))
    s0 = w.s([xic], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (Aki, XI, XI))
    SI0 = 'sum_ i e. ( 1 ... k ) ( %s - 0 )' % XI
    SI = 'sum_ i e. ( 1 ... k ) %s' % XI
    DK = '( ( k ^c -u S ) - ( ( k + 1 ) ^c -u S ) )'
    s1 = w.s([s0], 'sumeq2dv', '( %s -> %s = %s )' % (Ak, SI0, SI))
    s2 = w.s([s1], 'oveq1d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (Ak, SI0, DK, SI, DK))
    AB0 = 'sum_ k e. NN ( %s x. %s )' % (SI0, DK)
    LS = LSs('S')
    assert LS == 'sum_ k e. NN ( %s x. %s )' % (SI, DK), LS
    s3 = s([s2], 'sumeq2dv', '%s = %s' % (AB0, LS))
    assert V0 == '( ( 0 x. %s ) + ( ( S - 1 ) x. %s ) )' % (Q, AB0), V0
    lfv, _ = _cg.mptval(w, A0, 's', HP0, LSs('s'), 'S', sh, exs=s([w.s([], 'sumex', '%s e. _V' % LS)], 'a1i', '%s e. _V' % LS), gen=w.g)
    hol = lf_hol(w, A0, chi)
    lfc = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), sh], 'ffvelcdmd', '( %s ` S ) e. CC' % LFN)
    lsc = s([lfv, lfc], 'eqeltrrd', '%s e. CC' % LS)
    s1c = s([sc, s([], '1cnd', '1 e. CC')], 'subcld', '( S - 1 ) e. CC')
    e1 = s([m0, s([s3], 'oveq2d', '( ( S - 1 ) x. %s ) = ( ( S - 1 ) x. %s )' % (AB0, LS))], 'oveq12d', '%s = ( 0 + ( ( S - 1 ) x. %s ) )' % (V0, LS))
    e2 = s([e1, s([s([s1c, lsc], 'mulcld', '( ( S - 1 ) x. %s ) e. CC' % LS)], 'addlidd', '( 0 + ( ( S - 1 ) x. %s ) ) = ( ( S - 1 ) x. %s )' % (LS, LS))], 'eqtrd', '%s = ( ( S - 1 ) x. %s )' % (V0, LS))
    e3 = s([e2, s([s([lfv], 'eqcomd', '%s = ( %s ` S )' % (LS, LFN))], 'oveq2d', '( ( S - 1 ) x. %s ) = ( ( S - 1 ) x. ( %s ` S ) )' % (LS, LFN))], 'eqtrd',
           '%s = ( ( S - 1 ) x. ( %s ` S ) )' % (V0, LFN))
    w.qed([s([s([fv, mv], 'eqtrd', '( %s ` S ) = %s' % (E, VAL)), st], 'eqtrd', '( %s ` S ) = %s' % (E, V0)), e3], 'eqtrd', S['zc1elf'])
    return run8(w)


def two_nz(w, A0, F, ctr_step_fn):
    """( A0 -> ( F ` 2 ) =/= 0 ) from ctr_step : ( A0 -> ( 1 / 2 ) <_ ( abs ` ( F ` ( 2 + ( _i x. 0 ) ) ) ) ) (or 1 / 4)"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    st, M = ctr_step_fn()
    e20 = s([s([s([w.s([], 'it0e0', '( _i x. 0 ) = 0')], 'a1i', '( _i x. 0 ) = 0')], 'oveq2d', '( 2 + ( _i x. 0 ) ) = ( 2 + 0 )'), s([s([], '2cnd', '2 e. CC')], 'addridd', '( 2 + 0 ) = 2')],
            'eqtrd', '( 2 + ( _i x. 0 ) ) = 2')
    ab = s([s([e20], 'fveq2d', '( %s ` ( 2 + ( _i x. 0 ) ) ) = ( %s ` 2 )' % (F, F))], 'fveq2d', '( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) ) = ( abs ` ( %s ` 2 ) )' % (F, F))
    lb = s([st, ab], 'breqtrd', '%s <_ ( abs ` ( %s ` 2 ) )' % (M, F))
    return lb


def gen_zc1eord():
    w = W('zc1eord', 'For ` chi ` nonprincipal and ` P =/= 1 ` in the right half-plane, ` E = ( s - 1 ) L ( s , chi ) ` and ` L ` have the same zeros and the same orders at ` P ` ( ~ zc1elf , ~ hp0ordf , ~ holordml ).')
    A0 = ante_of(S['zc1eord'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); ph = s([], 'simprl', 'P e. %s' % HP0); pn1 = s([], 'simprr', 'P =/= 1')
    nx = s([chi, w.inst('simpl')], 'syl', NX)
    hol = lf_hol(w, A0, chi)
    def ctr():
        c = s([s([chi, s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR')], 'jca', '( %s /\\ 0 e. RR )' % CHI), w.inst('lchrctr')], 'syl',
              '( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % LFN)
        return c, '( 1 / 2 )'
    lb = two_nz(w, A0, LFN, ctr)
    L2 = '( %s ` 2 )' % LFN
    ch2 = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( 2 e. %s <-> ( 2 e. CC /\\ 0 < ( Re ` 2 ) ) )' % HP0)
    re2 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'rered', '( Re ` 2 ) = 2')
    h2 = s([s([s([], '2cnd', '2 e. CC'), s([lin8(w, A0, [], '0 < 2', {}), re2], 'breqtrrd', '0 < ( Re ` 2 )')], 'jca', '( 2 e. CC /\\ 0 < ( Re ` 2 ) )'), ch2], 'mpbird', '2 e. %s' % HP0)
    l2c = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), h2], 'ffvelcdmd', '%s e. CC' % L2)
    al2 = s([l2c], 'abscld', '( abs ` %s ) e. RR' % L2)
    l2n = s([lin8(w, A0, [lb], '0 < ( abs ` %s )' % L2, {'( abs ` %s )' % L2: al2}), s([l2c, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (L2, L2))], 'mpbird', '%s =/= 0' % L2)
    HF = tsub(S['hp0ordf'], {'F': LFN})
    hfa, hfc = ante_of(HF)
    hf = s([s([s([hol, l2n], 'jca', top_and(hfa)[0]), ph], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc)
    ON = '( %s holord P )' % LFN
    n0 = s([hf, w.inst('simpl')], 'syl', '%s e. NN0' % ON)
    EXG = top_and(hfc)[1]
    INNER = EXG[len('E. g '):]
    AG = '( %s /\\ %s )' % (A0, INNER)
    sg = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (AG, f))
    I1, I2, I3 = top_and(INNER)
    gh = sg([sg([], 'simpr', INNER), w.inst('simp1')], 'syl', I1); gp = sg([sg([], 'simpr', INNER), w.inst('simp2')], 'syl', I2); gfac = sg([sg([], 'simpr', INNER), w.inst('simp3')], 'syl', I3)
    Av = '( %s /\\ v e. %s )' % (AG, HP0)
    sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    vh = sv([], 'simpr', 'v e. %s' % HP0)
    BZ = I3[len('A. z e. %s ' % HP0):]
    BV = tsub(BZ, {'z': 'v'})
    eqz = w.wcongr(BZ, {'z': 'v'}, 'z = v', {'z': w.s([], 'id', '( z = v -> z = v )')})[0]
    fv_ = w.s([eqz, lift(w, gfac, Av), vh], 'rspcdva', '( %s -> %s )' % (Av, BV))
    ev = w.s([w.s([lift(w, chi, Av), vh], 'jca', '( %s -> ( %s /\\ v e. %s ) )' % (Av, CHI, HP0)), w.inst('zc1elf')], 'syl', '( %s -> ( %s ` v ) = ( ( v - 1 ) x. ( %s ` v ) ) )' % (Av, E, LFN))
    vcc = sv([sv([vh, sv([sv([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( v e. %s <-> ( v e. CC /\\ 0 < ( Re ` v ) ) )' % HP0)], 'mpbid', '( v e. CC /\\ 0 < ( Re ` v ) )'), w.inst('simpl')], 'syl', 'v e. CC')
    pcc = s([s([ph, s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( P e. %s <-> ( P e. CC /\\ 0 < ( Re ` P ) ) )' % HP0)], 'mpbid', '( P e. CC /\\ 0 < ( Re ` P ) )'), w.inst('simpl')], 'syl', 'P e. CC')
    vp = sv([vcc, lift(w, pcc, Av)], 'subcld', '( v - P ) e. CC')
    e0 = sv([vp], 'exp0d', '( ( v - P ) ^ 0 ) = 1')
    z1v, _ = _cg.mptval(w, Av, 'z', HP0, '( z - 1 )', 'v', vh, exs=sv([w.s([], 'ovex', '( v - 1 ) e. _V')], 'a1i', '( v - 1 ) e. _V'), gen=w.g)
    v1c = sv([vcc, sv([], '1cnd', '1 e. CC')], 'subcld', '( v - 1 ) e. CC')
    r0 = sv([sv([e0, z1v], 'oveq12d', '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( 1 x. ( v - 1 ) )' % Z1), sv([v1c], 'mullidd', '( 1 x. ( v - 1 ) ) = ( v - 1 )')], 'eqtrd',
            '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( v - 1 )' % Z1)
    FG = BV.split(' = ', 1)[1]
    lvc = \
        sv([lift(w, s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), Av), vh], 'ffvelcdmd', '( %s ` v ) e. CC' % LFN)
    c1 = sv([ev, sv([v1c, lvc], 'mulcomd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( v - 1 ) )' % (LFN, LFN))], 'eqtrd', '( %s ` v ) = ( ( %s ` v ) x. ( v - 1 ) )' % (E, LFN))
    c2 = sv([c1, sv([fv_, sv([r0], 'eqcomd', '( v - 1 ) = ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) )' % Z1)], 'oveq12d', '( ( %s ` v ) x. ( v - 1 ) ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (LFN, FG, Z1))],
            'eqtrd', '( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (E, FG, Z1))
    call = sg([c2], 'ralrimiva', 'A. v e. %s ( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (HP0, E, tsub(FG, {'v': 'v'}), Z1))
    HM = tsub(S['holordml'], {'F': E, 'D': HP0, 'M': ON, 'N': '0', 'G': 'g', 'H': Z1})
    hma, hmc = ante_of(HM)
    K1, K2, K3 = top_and(hma)
    ehol = sg([lift(w, s([nx, w.inst('zl1ehol')], 'syl', HOLF(E, HP0)), AG), w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (E, HP0))
    z1h = sg([w.s([], 'hsub1', S['hsub1'])], 'a1i', S['hsub1'])
    z1p, _ = _cg.mptval(w, AG, 'z', HP0, '( z - 1 )', 'P', lift(w, ph, AG), exs=sg([w.s([], 'ovex', '( P - 1 ) e. _V')], 'a1i', '( P - 1 ) e. _V'), gen=w.g)
    p1n = sg([lift(w, pcc, AG), sg([], '1cnd', '1 e. CC'), lift(w, pn1, AG)], 'subne0d', '( P - 1 ) =/= 0')
    z1n = sg([z1p, p1n], 'eqnetrd', '( %s ` P ) =/= 0' % Z1)
    k1 = sg([ehol, lift(w, ph, AG)], 'jca', K1)
    k2 = sg([sg([lift(w, n0, AG), gh, gp], '3jca', top_and(K2)[0]), sg([sg([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), z1h, z1n], '3jca', top_and(K2)[1])], 'jca', K2)
    hm = sg([sg([k1, k2, call], '3jca', hma), w.inst('holordml')], 'syl', hmc)
    oe = sg([hm, sg([lift(w, n0, AG)], 'nn0cnd', '%s e. CC' % ON) and sg([sg([lift(w, n0, AG)], 'nn0cnd', '%s e. CC' % ON)], 'addridd', '( %s + 0 ) = %s' % (ON, ON))], 'eqtrd', '( %s holord P ) = %s' % (E, ON))
    el = s([w.s([oe], 'ex', '( %s -> ( %s -> ( %s holord P ) = %s ) )' % (A0, INNER, E, ON))], 'exlimdv', '( %s -> ( %s holord P ) = %s )' % (EXG, E, ON))
    ord_ = s([s([hf, w.inst('simpr')], 'syl', EXG), el], 'mpd', '( %s holord P ) = %s' % (E, ON))
    # zeros
    ep = s([s([chi, ph], 'jca', '( %s /\\ P e. %s )' % (CHI, HP0)), w.inst('zc1elf')], 'syl', '( %s ` P ) = ( ( P - 1 ) x. ( %s ` P ) )' % (E, LFN))
    lpc = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), ph], 'ffvelcdmd', '( %s ` P ) e. CC' % LFN)
    p1c = s([pcc, s([], '1cnd', '1 e. CC')], 'subcld', '( P - 1 ) e. CC')
    mo = s([p1c, lpc], 'mul0ord', '( ( ( P - 1 ) x. ( %s ` P ) ) = 0 <-> ( ( P - 1 ) = 0 \\/ ( %s ` P ) = 0 ) )' % (LFN, LFN))
    p1n0 = s([pcc, s([], '1cnd', '1 e. CC'), pn1], 'subne0d', '( P - 1 ) =/= 0')
    bo = s([s([p1n0], 'neneqd', '-. ( P - 1 ) = 0'), w.inst('biorf')], 'syl', '( ( %s ` P ) = 0 <-> ( ( P - 1 ) = 0 \\/ ( %s ` P ) = 0 ) )' % (LFN, LFN))
    zeq = s([s([ep], 'eqeq1d', '( ( %s ` P ) = 0 <-> ( ( P - 1 ) x. ( %s ` P ) ) = 0 )' % (E, LFN)), s([mo, bo], 'bitr4d', '( ( ( P - 1 ) x. ( %s ` P ) ) = 0 <-> ( %s ` P ) = 0 )' % (LFN, LFN))],
            'bitrd', '( ( %s ` P ) = 0 <-> ( %s ` P ) = 0 )' % (E, LFN))
    w.qed([ord_, zeq], 'jca', S['zc1eord'])
    return run8(w)


if __name__ == '__main__':
    gen_hsub1()
    gen_zc1elf()
    gen_zc1eord()
