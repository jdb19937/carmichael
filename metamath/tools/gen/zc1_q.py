"""Sortie ZC1: principal character, orders and counts equal to those of E1 = ( s - 1 ) zeta ( s ):
pfmhol, zc1tord (Lean analyticOrderNatAt_trivChar_eq), zc1teq (zeroCountBox_trivChar_eq)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
from c9_b import decode
from c10_f import crfacts
import zc1_c, zc1_i, zc1_k, zc1_m, zc1_n, zc1_o, zc1_p
from zc1_c import u1base, U1
from zc1_m import e_h2
from zc1_o import EUF, PFP, DN
from zc1_p import PR, CY, PFX, pfx_is_pfp
import lin
lin.FASTPATH = True

PFM = '( j e. %s |-> %s )' % (HP0, PFX('j'))
S['pfmhol'] = '( %s -> ( %s /\\ A. z e. %s ( %s ` z ) = %s ) )' % (PR, HOLF(PFM, HP0), HP0, PFM, EUF('N', 'z'))
S['zc1tord'] = '( ( %s /\\ P e. %s ) -> ( ( %s holord P ) = ( %s holord P ) /\\ ( ( %s ` P ) = 0 <-> ( %s ` P ) = 0 ) ) )' % (PR, HP0, E, E1, E, E1)
S['zc1teq'] = '( ( %s /\\ ( ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ T e. RR ) ) -> %s = %s )' % (PR, ZC(E, 'A', 'T'), ZC(E1, 'A', 'T'))


def hp_cc(w, ante, xh, x):
    """( ante -> x e. CC ) and ( ante -> 0 < Re x ) from xh : ( ante -> x e. HP0 )"""
    el = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % ante), w.inst('elhp2')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (ante, x, HP0, x, x))
    b = w.s([xh, el], 'mpbid', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (ante, x, x))
    return w.s([b, w.inst('simpl')], 'syl', '( %s -> %s e. CC )' % (ante, x)), w.s([b, w.inst('simpr')], 'syl', '( %s -> 0 < ( Re ` %s ) )' % (ante, x))


def gen_pfmhol():
    w = W('pfmhol', 'For the principal character the Euler polynomial ` s |-> sum_ ( d || N ) mu ( d ) chi_1 ( d ) d ^ -s ` is holomorphic on the right half-plane and equals ` prod_ ( p || N ) ( 1 - p ^ -s ) ` ( ~ zl2dph , ~ prmcy1 , ~ euf1 ).')
    A0 = PR
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pr = s([], 'id', PR)
    nx = s([pr, w.inst('simpl')], 'syl', NX)
    PFW = '( w e. CC |-> %s )' % PFX('w')
    PFJ = '( j e. CC |-> %s )' % PFX('j')
    dph = s([nx, w.inst('zl2dph')], 'syl', HOLF(PFW, 'CC'))
    ng = w.s([], 'negeq', '( w = j -> -u w = -u j )')
    cj1 = w.s([ng], 'oveq2d', '( w = j -> ( d ^c -u w ) = ( d ^c -u j ) )')
    cj2 = w.s([cj1], 'oveq2d', '( w = j -> ( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u w ) ) = ( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u j ) ) )' % (CY, CY))
    cj3 = w.s([cj2], 'sumeq2sdv', '( w = j -> %s = %s )' % (PFX('w'), PFX('j')))
    cvj = s([w.s([cj3], 'cbvmptv', '%s = %s' % (PFW, PFJ))], 'a1i', '%s = %s' % (PFW, PFJ))
    cn1 = s([s([cvj], 'eqcomd', '%s = %s' % (PFJ, PFW)), s([dph, w.inst('simpl')], 'syl', '%s e. ( CC -cn-> CC )' % PFW)], 'eqeltrd', '%s e. ( CC -cn-> CC )' % PFJ)
    dm1 = s([s([dph, w.inst('simpr')], 'syl', 'CC C_ dom ( CC _D %s )' % PFW), s([s([cvj], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (PFW, PFJ))], 'dmeqd', 'dom ( CC _D %s ) = dom ( CC _D %s )' % (PFW, PFJ))],
            'sseqtrd', 'CC C_ dom ( CC _D %s )' % PFJ)
    op = s([w.s([], 'hpopn', '%s e. ( TopOpen ` CCfld )' % HP0)], 'a1i', '%s e. ( TopOpen ` CCfld )' % HP0)
    ZH = tsub(stmt('zl2hent'), {'z': 'j', 'A': PFX('j'), 'D': HP0})
    pfm = s([s([s([cn1, dm1], 'jca', HOLF(PFJ, 'CC')), op], 'jca', ante_of(ZH)[0]), w.inst('zl2hent')], 'syl', HOLF(PFM, HP0))
    Az = '( %s /\\ z e. %s )' % (A0, HP0)
    zh = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, HP0))
    zc, _ = hp_cc(w, Az, zh, 'z')
    pv, _ = _cg.mptval(w, Az, 'j', HP0, PFX('j'), 'z', zh, exs=w.s([w.s([], 'sumex', '%s e. _V' % PFX('z'))], 'a1i', '( %s -> %s e. _V )' % (Az, PFX('z'))), gen=w.g)
    pp = pfx_is_pfp(w, Az, lift(w, pr, Az), zc, 'z')
    eu = w.s([w.s([lift(w, s([nx, w.inst('simpl')], 'syl', 'N e. NN'), Az), zc], 'jca', '( %s -> ( N e. NN /\\ z e. CC ) )' % Az), w.inst('euf1')], 'syl', '( %s -> %s = %s )' % (Az, PFP('N', 'z'), EUF('N', 'z')))
    ez = w.s([w.s([pv, pp], 'eqtrd', '( %s -> ( %s ` z ) = %s )' % (Az, PFM, PFP('N', 'z'))), eu], 'eqtrd', '( %s -> ( %s ` z ) = %s )' % (Az, PFM, EUF('N', 'z')))
    w.qed([pfm, s([ez], 'ralrimiva', 'A. z e. %s ( %s ` z ) = %s' % (HP0, PFM, EUF('N', 'z')))], 'jca', S['pfmhol'])
    return run8(w)


def gen_zc1tord():
    w = W('zc1tord', 'For the principal character, ` E ` and ` E1 = ( s - 1 ) zeta ( s ) ` have the same zeros and the same orders on the right half-plane (Lean ` analyticOrderNatAt_trivChar_eq ` ; the Euler factor does not vanish there: ~ zc1prin , ~ eufne0 , ~ holordml ).')
    A0 = ante_of(S['zc1tord'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pr = s([], 'simpl', PR); ph = s([], 'simpr', 'P e. %s' % HP0)
    nx = s([pr, w.inst('simpl')], 'syl', NX)
    nn = s([nx, w.inst('simpl')], 'syl', 'N e. NN')
    ub = u1base(w, A0)
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), ub], 'jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    h2 = e_h2(w, A0, nx1, '1', U1)
    HF = tsub(S['hp0ordf'], {'F': E1})
    hfa, hfc = ante_of(HF)
    hf = s([s([h2, ph], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc)
    ON = '( %s holord P )' % E1
    n0 = s([hf, w.inst('simpl')], 'syl', '%s e. NN0' % ON)
    EXG = top_and(hfc)[1]
    INNER = EXG[len('E. g '):]
    pf = s([pr, w.inst('pfmhol')], 'syl', ante_of(S['pfmhol'])[1])
    pfh = s([pf, w.inst('simpl')], 'syl', HOLF(PFM, HP0)); pfv = s([pf, w.inst('simpr')], 'syl', 'A. z e. %s ( %s ` z ) = %s' % (HP0, PFM, EUF('N', 'z')))
    pc, prp = hp_cc(w, A0, ph, 'P')
    eqzP = w.wcongr('( %s ` z ) = %s' % (PFM, EUF('N', 'z')), {'z': 'P'}, 'z = P', {'z': w.s([], 'id', '( z = P -> z = P )')})[0]
    pfP = s([eqzP, pfv, ph], 'rspcdva', '( %s ` P ) = %s' % (PFM, EUF('N', 'P')))
    eun = s([s([nn, s([pc, prp], 'jca', '( P e. CC /\\ 0 < ( Re ` P ) )')], 'jca', '( N e. NN /\\ ( P e. CC /\\ 0 < ( Re ` P ) ) )'), w.inst('eufne0')], 'syl', '%s =/= 0' % EUF('N', 'P'))
    pfn = s([pfP, eun], 'eqnetrd', '( %s ` P ) =/= 0' % PFM)
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
    ep = sv([sv([lift(w, pr, Av), vh], 'jca', '( %s /\\ v e. %s )' % (PR, HP0)), w.inst('zc1prin')], 'syl', tsub(ante_of(S['zc1prin'])[1], {'S': 'v'}))
    eqzv = w.wcongr('( %s ` z ) = %s' % (PFM, EUF('N', 'z')), {'z': 'v'}, 'z = v', {'z': w.s([], 'id', '( z = v -> z = v )')})[0]
    pfvv = sv([eqzv, lift(w, pfv, Av), vh], 'rspcdva', '( %s ` v ) = %s' % (PFM, EUF('N', 'v')))
    vc, _ = hp_cc(w, Av, vh, 'v')
    vp = sv([vc, lift(w, pc, Av)], 'subcld', '( v - P ) e. CC')
    e0 = sv([vp], 'exp0d', '( ( v - P ) ^ 0 ) = 1')
    pvc = fcc(w, Av, lift(w, pfh, Av), PFM, HP0, 'v', vh)
    e1c = fcc(w, Av, lift(w, s([h2, w.inst('simpl')], 'syl', HOLF(E1, HP0)), Av), E1, HP0, 'v', vh)
    r0 = sv([sv([e0], 'oveq1d', '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( 1 x. ( %s ` v ) )' % (PFM, PFM)), sv([pvc], 'mullidd', '( 1 x. ( %s ` v ) ) = ( %s ` v )' % (PFM, PFM))], 'eqtrd',
            '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( %s ` v )' % (PFM, PFM))
    FG = BV.split(' = ', 1)[1]
    c1 = sv([ep, sv([sv([pfvv], 'eqcomd', '%s = ( %s ` v )' % (EUF('N', 'v'), PFM)), sv([], 'eqidd', '( %s ` v ) = ( %s ` v )' % (E1, E1))], 'oveq12d',
                    '( %s x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (EUF('N', 'v'), E1, PFM, E1))], 'eqtrd', '( %s ` v ) = ( ( %s ` v ) x. ( %s ` v ) )' % (E, PFM, E1))
    c2 = sv([c1, sv([pvc, e1c], 'mulcomd', '( ( %s ` v ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (PFM, E1, E1, PFM))], 'eqtrd', '( %s ` v ) = ( ( %s ` v ) x. ( %s ` v ) )' % (E, E1, PFM))
    c3 = sv([c2, sv([fv_, sv([r0], 'eqcomd', '( %s ` v ) = ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) )' % (PFM, PFM))], 'oveq12d',
                    '( ( %s ` v ) x. ( %s ` v ) ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (E1, PFM, FG, PFM))], 'eqtrd', '( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (E, FG, PFM))
    call = sg([c3], 'ralrimiva', 'A. v e. %s ( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (HP0, E, FG, PFM))
    HM = tsub(S['holordml'], {'F': E, 'D': HP0, 'M': ON, 'N': '0', 'G': 'g', 'H': PFM})
    hma, hmc = ante_of(HM)
    K1, K2, K3 = top_and(hma)
    ehol = sg([lift(w, s([nx, w.inst('zl1ehol')], 'syl', HOLF(E, HP0)), AG), w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (E, HP0))
    k1 = sg([ehol, lift(w, ph, AG)], 'jca', K1)
    k2 = sg([sg([lift(w, n0, AG), gh, gp], '3jca', top_and(K2)[0]), sg([sg([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), lift(w, pfh, AG), lift(w, pfn, AG)], '3jca', top_and(K2)[1])], 'jca', K2)
    hm = sg([sg([k1, k2, call], '3jca', hma), w.inst('holordml')], 'syl', hmc)
    oe = sg([hm, sg([sg([lift(w, n0, AG)], 'nn0cnd', '%s e. CC' % ON)], 'addridd', '( %s + 0 ) = %s' % (ON, ON))], 'eqtrd', '( %s holord P ) = %s' % (E, ON))
    el = s([w.s([oe], 'ex', '( %s -> ( %s -> ( %s holord P ) = %s ) )' % (A0, INNER, E, ON))], 'exlimdv', '( %s -> ( %s holord P ) = %s )' % (EXG, E, ON))
    ord_ = s([s([hf, w.inst('simpr')], 'syl', EXG), el], 'mpd', '( %s holord P ) = %s' % (E, ON))
    # zeros
    epP = s([s([pr, ph], 'jca', '( %s /\\ P e. %s )' % (PR, HP0)), w.inst('zc1prin')], 'syl', tsub(ante_of(S['zc1prin'])[1], {'S': 'P'}))
    eu = EUF('N', 'P')
    euc = s([pfP, fcc(w, A0, pfh, PFM, HP0, 'P', ph)], 'eqeltrrd', '%s e. CC' % eu)
    e1P = fcc(w, A0, s([h2, w.inst('simpl')], 'syl', HOLF(E1, HP0)), E1, HP0, 'P', ph)
    mo = s([euc, e1P], 'mul0ord', '( ( %s x. ( %s ` P ) ) = 0 <-> ( %s = 0 \\/ ( %s ` P ) = 0 ) )' % (eu, E1, eu, E1))
    bo = s([s([eun], 'neneqd', '-. %s = 0' % eu), w.inst('biorf')], 'syl', '( ( %s ` P ) = 0 <-> ( %s = 0 \\/ ( %s ` P ) = 0 ) )' % (E1, eu, E1))
    zeq = s([s([epP], 'eqeq1d', '( ( %s ` P ) = 0 <-> ( %s x. ( %s ` P ) ) = 0 )' % (E, eu, E1)), s([mo, bo], 'bitr4d', '( ( %s x. ( %s ` P ) ) = 0 <-> ( %s ` P ) = 0 )' % (eu, E1, E1))],
            'bitrd', '( ( %s ` P ) = 0 <-> ( %s ` P ) = 0 )' % (E, E1))
    w.qed([ord_, zeq], 'jca', S['zc1tord'])
    return run8(w)


def box_hp(w, ante, rin, r, ar, a0, tr):
    """( ante -> r e. HP0 ) from rin : ( ante -> r e. BOX(A, T) ), ar : ( ante -> A e. RR ), a0 : ( ante -> 0 < A ), tr : ( ante -> T e. RR )"""
    s = lambda h, rf, f: w.s(h, rf, '( %s -> %s )' % (ante, f))
    BA, BB = '( A + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
    bac, rbA, ibA = crfacts(w, ante, 'A', '-u T', ar, s([tr], 'renegcld', '-u T e. RR'))
    bbc, rbB, ibB = crfacts(w, ante, '1', 'T', numst(w, ante, '1', 'RR'), tr)
    d = decode(w, ante, rin, bac, bbc, BA, BB, BOX('A', 'T'), U=r)
    rc = d[0]
    lv = {'( Re ` %s )' % r: s([rc], 'recld', '( Re ` %s ) e. RR' % r), 'A': ar, '( Re ` %s )' % BA: s([bac], 'recld', '( Re ` %s ) e. RR' % BA)}
    rp = lin8(w, ante, [rbA, d[1], a0], '0 < ( Re ` %s )' % r, lv)
    el = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (r, HP0, r, r))
    return s([s([rc, rp], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (r, r)), el], 'mpbird', '%s e. %s' % (r, HP0))


def gen_zc1teq():
    w = W('zc1teq', 'The box count of the principal character mod ` N ` equals that of ` E1 = ( s - 1 ) zeta ( s ) ` (Lean ` zeroCountBox_trivChar_eq ` ; ~ zc1tord ).')
    A0 = ante_of(S['zc1teq'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    pr = s([], 'simpl', PR); x2 = s([], 'simpr', top_and(A0)[1])
    a3 = s([x2, w.inst('simpl')], 'syl', '( A e. RR /\\ 0 < A /\\ A <_ 1 )'); tr = s([x2, w.inst('simpr')], 'syl', 'T e. RR')
    ar = s([a3, w.inst('simp1')], 'syl', 'A e. RR'); a0 = s([a3, w.inst('simp2')], 'syl', '0 < A')
    BX = BOX('A', 'T')
    Ar = '( %s /\\ r e. %s )' % (A0, BX)
    Lr = lambda st: lift(w, st, Ar)
    rh = box_hp(w, Ar, w.s([], 'simpr', '( %s -> r e. %s )' % (Ar, BX)), 'r', Lr(ar), Lr(a0), Lr(tr))
    TO = tsub(S['zc1tord'], {'P': 'r'})
    toa, toc = ante_of(TO)
    to = w.s([w.s([Lr(pr), rh], 'jca', '( %s -> %s )' % (Ar, toa)), w.inst('zc1tord')], 'syl', '( %s -> %s )' % (Ar, toc))
    zq = w.s([w.s([to, w.inst('simpr')], 'syl', '( %s -> %s )' % (Ar, top_and(toc)[1]))], 'anbi2d', '( %s -> ( ( r =/= 1 /\\ ( %s ` r ) = 0 ) <-> ( r =/= 1 /\\ ( %s ` r ) = 0 ) ) )' % (Ar, E, E1))
    zfe = s([zq], 'rabbidva', '%s = %s' % (ZF(E, 'A', 'T'), ZF(E1, 'A', 'T')))
    se1 = s([zfe], 'sumeq1d', '%s = sum_ q e. %s ( %s holord q )' % (ZC(E, 'A', 'T'), ZF(E1, 'A', 'T'), E))
    Aq = '( %s /\\ q e. %s )' % (A0, ZF(E1, 'A', 'T'))
    Lq = lambda st: lift(w, st, Aq)
    qb = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, ZF(E1, 'A', 'T'))), w.inst('elrabi')], 'syl', '( %s -> q e. %s )' % (Aq, BX))
    qh = box_hp(w, Aq, qb, 'q', Lq(ar), Lq(a0), Lq(tr))
    TQ = tsub(S['zc1tord'], {'P': 'q'})
    tqa, tqc = ante_of(TQ)
    tq = w.s([w.s([Lq(pr), qh], 'jca', '( %s -> %s )' % (Aq, tqa)), w.inst('zc1tord')], 'syl', '( %s -> %s )' % (Aq, tqc))
    oq = w.s([tq, w.inst('simpl')], 'syl', '( %s -> %s )' % (Aq, top_and(tqc)[0]))
    se2 = s([oq], 'sumeq2dv', 'sum_ q e. %s ( %s holord q ) = %s' % (ZF(E1, 'A', 'T'), E, ZC(E1, 'A', 'T')))
    w.qed([se1, se2], 'eqtrd', S['zc1teq'])
    return run8(w)


if __name__ == '__main__':
    gen_pfmhol()
    gen_zc1tord()
    gen_zc1teq()
