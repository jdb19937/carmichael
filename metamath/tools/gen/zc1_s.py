"""Sortie ZC1: zeros of E1 = ( s - 1 ) zeta ( s ) off 1 are zeros of eta of at least the same order (zc1ezt,
Lean analyticOrderNatAt_zeta_le_etaFun)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import congr as _cg
import num
from c8_o import numst
import zc1_c, zc1_f, zc1_i, zc1_j, zc1_m, zc1_q, zc1_r
from zc1_r import ETAa, GFa, renamed_hol, EB
from zc1_c import u1base, U1
from zc1_j import Z1, two_nz
from zc1_m import e_h2
from zc1_q import hp_cc
import lin
lin.FASTPATH = True

S['zc1ezt'] = '( ( P e. %s /\\ P =/= 1 ) -> ( ( %s holord P ) <_ ( %s holord P ) /\\ ( ( %s ` P ) = 0 -> ( %s ` P ) = 0 ) ) )' % (HP0, E1, ETA, E1, ETA)


def h2of(w, A0, F, hol, ctr_fn):
    """( A0 -> ( HOL(F) /\\ ( F ` 2 ) =/= 0 ) )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    lb = two_nz(w, A0, F, ctr_fn)
    ch2 = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( 2 e. %s <-> ( 2 e. CC /\\ 0 < ( Re ` 2 ) ) )' % HP0)
    re2 = s([s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'rered', '( Re ` 2 ) = 2')
    h2 = s([s([s([], '2cnd', '2 e. CC'), s([lin8(w, A0, [], '0 < 2', {}), re2], 'breqtrrd', '0 < ( Re ` 2 )')], 'jca', '( 2 e. CC /\\ 0 < ( Re ` 2 ) )'), ch2], 'mpbird', '2 e. %s' % HP0)
    F2 = '( %s ` 2 )' % F
    f2c = fcc(w, A0, hol, F, HP0, '2', h2)
    af = s([f2c], 'abscld', '( abs ` %s ) e. RR' % F2)
    M = lb.split(' <_ ', 1)[0] if False else None
    f2n = s([lin8(w, A0, [lb], '0 < ( abs ` %s )' % F2, {'( abs ` %s )' % F2: af}), s([f2c, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (F2, F2))], 'mpbird', '%s =/= 0' % F2)
    return s([hol, f2n], 'jca', '( %s /\\ %s =/= 0 )' % (HOLF(F, HP0), F2))


def gen_zc1ezt():
    w = W('zc1ezt', 'A zero ` P =/= 1 ` of ` E1 = ( s - 1 ) zeta ( s ) ` in the right half-plane is a zero of the Abel-summed eta function of at least the same order (Lean ` analyticOrderNatAt_zeta_le_etaFun ` ; ~ etarel , ~ holordml ).')
    A0 = ante_of(S['zc1ezt'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ph = s([], 'simpl', 'P e. %s' % HP0); pn1 = s([], 'simpr', 'P =/= 1')
    ub = u1base(w, A0)
    nx1 = s([s([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN'), ub], 'jca', '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1)
    he1 = e_h2(w, A0, nx1, '1', U1)
    etah = s([s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0')], 'jca', '( 0 e. RR /\\ 0 <_ 0 )'), w.inst('etahol')], 'syl', HOLF(ETA, HP0))
    def ctr_eta():
        c0 = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('etactr')], 'syl', '( 1 / 4 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % ETA)
        cv = s([conv(A0, ETA, ETAa, eeq, '( 2 + ( _i x. 0 ) )')], 'fveq2d', '( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) ) = ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % (ETA, ETAa))
        return s([c0, cv], 'breqtrd', '( 1 / 4 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % ETAa), '( 1 / 4 )'
    gfh = s([w.s([], 'gfhol', S['gfhol'])], 'a1i', S['gfhol'])
    ce = w.s([w.s([w.s([w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( k ^c -u z ) = ( k ^c -u a ) )'),
                          w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( ( k + 1 ) ^c -u z ) = ( ( k + 1 ) ^c -u a ) )')], 'oveq12d',
                         '( z = a -> ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) = ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) )')], 'oveq2d',
                    '( z = a -> ( ( k mod 2 ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) ) = ( ( k mod 2 ) x. ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) ) )')], 'sumeq2sdv',
              '( z = a -> %s = %s )' % (EB % ('z', 'z'), EB % ('a', 'a')))
    etaa, eeq = renamed_hol(w, A0, etah, ETA, ETAa, ce)
    cg = w.s([w.s([w.s([], 'oveq2', '( z = a -> ( 1 - z ) = ( 1 - a ) )')], 'oveq2d', '( z = a -> ( 2 ^c ( 1 - z ) ) = ( 2 ^c ( 1 - a ) ) )')], 'oveq2d',
             '( z = a -> ( 1 - ( 2 ^c ( 1 - z ) ) ) = ( 1 - ( 2 ^c ( 1 - a ) ) ) )')
    gfa, geq = renamed_hol(w, A0, gfh, GF, GFa, cg)
    def conv(ante, M, Ma, eqst, x):
        """( ante -> ( M ` x ) = ( Ma ` x ) )"""
        return w.s([lift(w, eqst, ante)], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ante, M, x, Ma, x))
    heta = h2of(w, A0, ETAa, etaa, ctr_eta)
    def ctr_gf():
        phi = ante_of(stmt('gfctr'))[1]
        al = s([w.s([w.s([], 'gfctr', stmt('gfctr'))], 'rgen', 'A. t e. RR %s' % phi)], 'a1i', 'A. t e. RR %s' % phi)
        eq = w.wcongr(phi, {'t': '0'}, 't = 0', {'t': w.s([], 'id', '( t = 0 -> t = 0 )')})[0]
        g0 = w.s([eq, al, s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR')], 'rspcdva', '( %s -> %s )' % (A0, tsub(phi, {'t': '0'})))
        cv = s([conv(A0, GF, GFa, geq, '( 2 + ( _i x. 0 ) )')], 'fveq2d', '( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) ) = ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % (GF, GFa))
        return s([g0, cv], 'breqtrd', '( 1 / 2 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % GFa), '( 1 / 2 )'
    hgf = h2of(w, A0, GFa, gfa, ctr_gf)
    def fact(F, h2st, g):
        HF = tsub(S['hp0ordf'], {'F': F, 'g': g})
        hfa, hfc = ante_of(HF)
        hf = s([s([h2st, ph], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc)
        return hf, hfc
    hfe, hce = fact(E1, he1, 'e'); hfg, hcg = fact(ETAa, heta, 'g'); hfh, hch = fact(GFa, hgf, 'h')
    OE, OG, OH = '( %s holord P )' % E1, '( %s holord P )' % ETAa, '( %s holord P )' % GFa
    ne = s([hfe, w.inst('simpl')], 'syl', '%s e. NN0' % OE); ng = s([hfg, w.inst('simpl')], 'syl', '%s e. NN0' % OG); nh = s([hfh, w.inst('simpl')], 'syl', '%s e. NN0' % OH)
    XE, XG, XH = top_and(hce)[1], top_and(hcg)[1], top_and(hch)[1]
    IE, IG, IH = XE[len('E. e '):], XG[len('E. g '):], XH[len('E. h '):]
    A1 = '( %s /\\ %s )' % (A0, IE)
    A2 = '( %s /\\ %s )' % (A1, IG)
    A3 = '( %s /\\ %s )' % (A2, IH)
    s3 = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A3, f))
    L3 = lambda st: lift(w, st, A3)
    ie = s3([], 'simpllr' if False else 'simpllr', IE) if False else w.s([w.s([], 'simpll', '( %s -> %s )' % (A3, A1)), w.inst('simpr')], 'syl', '( %s -> %s )' % (A3, IE))
    ig = w.s([w.s([], 'simpl', '( %s -> %s )' % (A3, A2)), w.inst('simpr')], 'syl', '( %s -> %s )' % (A3, IG))
    ih = s3([], 'simpr', IH)
    def parts(ist, I):
        a, b, c = top_and(I)
        return s3([ist, w.inst('simp1')], 'syl', a), s3([ist, w.inst('simp2')], 'syl', b), s3([ist, w.inst('simp3')], 'syl', c), c
    eh, ep, ef, EFC = parts(ie, IE); gh, gp, gf_, GFC = parts(ig, IG); hh, hp, hf_, HFC = parts(ih, IH)
    Q1 = '( b e. %s |-> ( ( %s ` b ) x. ( %s ` b ) ) )' % (HP0, GFa, E1)
    q1h = s3([s3([L3(gfa), L3(s([he1, w.inst('simpl')], 'syl', HOLF(E1, HP0)))], 'jca', '( %s /\\ %s )' % (HOLF(GFa, HP0), HOLF(E1, HP0))), w.inst('holmul')], 'syl', HOLF(Q1, HP0))
    Av = '( %s /\\ v e. %s )' % (A3, HP0)
    sv = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    vh = sv([], 'simpr', 'v e. %s' % HP0)
    def fbody(F, ON, g, x):
        return '( %s ` %s ) = ( ( ( %s - P ) ^ %s ) x. ( %s ` %s ) )' % (F, x, x, ON, g, x)
    def at_v(fst, F, ON, g):
        e1 = w.s([], 'fveq2', '( z = v -> ( %s ` z ) = ( %s ` v ) )' % (F, F))
        e2 = w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z - P ) = ( v - P ) )')], 'oveq1d', '( z = v -> ( ( z - P ) ^ %s ) = ( ( v - P ) ^ %s ) )' % (ON, ON)),
                  w.s([], 'fveq2', '( z = v -> ( %s ` z ) = ( %s ` v ) )' % (g, g))], 'oveq12d',
                 '( z = v -> ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) = ( ( ( v - P ) ^ %s ) x. ( %s ` v ) ) )' % (ON, g, ON, g))
        eq = w.s([e1, e2], 'eqeq12d', '( z = v -> ( %s <-> %s ) )' % (fbody(F, ON, g, 'z'), fbody(F, ON, g, 'v')))
        return w.s([eq, lift(w, fst, Av), vh], 'rspcdva', '( %s -> %s )' % (Av, fbody(F, ON, g, 'v')))
    efv = at_v(ef, E1, OE, 'e'); gfv = at_v(gf_, ETAa, OG, 'g'); hfv = at_v(hf_, GFa, OH, 'h')
    qv, _ = _cg.mptval(w, Av, 'b', HP0, '( ( %s ` b ) x. ( %s ` b ) )' % (GFa, E1), 'v', vh,
                       exs=sv([w.s([], 'ovex', '( ( %s ` v ) x. ( %s ` v ) ) e. _V' % (GFa, E1))], 'a1i', '( ( %s ` v ) x. ( %s ` v ) ) e. _V' % (GFa, E1)), gen=w.g)
    FH = '( ( ( v - P ) ^ %s ) x. ( h ` v ) )' % OH
    FE = '( ( ( v - P ) ^ %s ) x. ( e ` v ) )' % OE
    FG = '( ( ( v - P ) ^ %s ) x. ( g ` v ) )' % OG
    q_a = sv([qv, sv([hfv, efv], 'oveq12d', '( ( %s ` v ) x. ( %s ` v ) ) = ( %s x. %s )' % (GFa, E1, FH, FE))], 'eqtrd', '( %s ` v ) = ( %s x. %s )' % (Q1, FH, FE))
    qa_all = s3([q_a], 'ralrimiva', 'A. v e. %s ( %s ` v ) = ( %s x. %s )' % (HP0, Q1, FH, FE))
    # second factorisation through etarel: Q1 v = ( v - 1 ) eta v = FG ( ( v - P ) ^ 0 ( Z1 ` v ) )
    er0 = sv([vh, w.inst('etarel')], 'syl', tsub(S['etarel'], {'S': 'v'}).split(' -> ', 1)[1][:-2])
    c1 = conv(Av, ETA, ETAa, eeq, 'v'); c2 = conv(Av, GF, GFa, geq, 'v')
    er = sv([sv([sv([c1], 'oveq2d', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( v - 1 ) x. ( %s ` v ) )' % (ETA, ETAa))], 'eqcomd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( v - 1 ) x. ( %s ` v ) )' % (ETAa, ETA)),
             sv([er0, sv([c2], 'oveq1d', '( ( %s ` v ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (GF, E1, GFa, E1))], 'eqtrd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (ETA, GFa, E1))],
            'eqtrd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (ETAa, GFa, E1))
    vc, _ = hp_cc(w, Av, vh, 'v')
    pc, _ = hp_cc(w, A0, ph, 'P')
    vp = sv([vc, lift(w, pc, Av)], 'subcld', '( v - P ) e. CC')
    e0 = sv([vp], 'exp0d', '( ( v - P ) ^ 0 ) = 1')
    z1v, _ = _cg.mptval(w, Av, 'z', HP0, '( z - 1 )', 'v', vh, exs=sv([w.s([], 'ovex', '( v - 1 ) e. _V')], 'a1i', '( v - 1 ) e. _V'), gen=w.g)
    v1c = sv([vc, sv([], '1cnd', '1 e. CC')], 'subcld', '( v - 1 ) e. CC')
    r0 = sv([sv([e0, z1v], 'oveq12d', '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( 1 x. ( v - 1 ) )' % Z1), sv([v1c], 'mullidd', '( 1 x. ( v - 1 ) ) = ( v - 1 )')], 'eqtrd',
            '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( v - 1 )' % Z1)
    etvc = fcc(w, Av, lift(w, etaa, Av), ETAa, HP0, 'v', vh)
    q_b0 = sv([qv, sv([er], 'eqcomd', '( ( %s ` v ) x. ( %s ` v ) ) = ( ( v - 1 ) x. ( %s ` v ) )' % (GFa, E1, ETAa))], 'eqtrd', '( %s ` v ) = ( ( v - 1 ) x. ( %s ` v ) )' % (Q1, ETAa))
    q_b1 = sv([q_b0, sv([v1c, etvc], 'mulcomd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( v - 1 ) )' % (ETAa, ETAa))], 'eqtrd', '( %s ` v ) = ( ( %s ` v ) x. ( v - 1 ) )' % (Q1, ETAa))
    q_b = sv([q_b1, sv([gfv, sv([r0], 'eqcomd', '( v - 1 ) = ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) )' % Z1)], 'oveq12d', '( ( %s ` v ) x. ( v - 1 ) ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (ETAa, FG, Z1))],
             'eqtrd', '( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (Q1, FG, Z1))
    qb_all = s3([q_b], 'ralrimiva', 'A. v e. %s ( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (HP0, Q1, FG, Z1))
    q1cn = s3([q1h, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (Q1, HP0))
    def hml(M_, g_, N_, h_, gst, gpst, hst, hpst, mst, nst, allst):
        HM = tsub(S['holordml'], {'F': Q1, 'D': HP0, 'M': M_, 'N': N_, 'G': g_, 'H': h_})
        hma, hmc = ante_of(HM)
        K1, K2, K3 = top_and(hma)
        k1 = s3([q1cn, L3(ph)], 'jca', K1)
        k2 = s3([s3([mst, gst, gpst], '3jca', top_and(K2)[0]), s3([nst, hst, hpst], '3jca', top_and(K2)[1])], 'jca', K2)
        return s3([s3([k1, k2, allst], '3jca', hma), w.inst('holordml')], 'syl', hmc)
    oa = hml(OH, 'h', OE, 'e', hh, hp, eh, ep, L3(nh), L3(ne), qa_all)
    z1n = s3([s3([], 'x', 'x') if False else None], 'x', 'x') if False else None
    z1p, _ = _cg.mptval(w, A3, 'z', HP0, '( z - 1 )', 'P', L3(ph), exs=s3([w.s([], 'ovex', '( P - 1 ) e. _V')], 'a1i', '( P - 1 ) e. _V'), gen=w.g)
    p1n = s3([L3(pc), s3([], '1cnd', '1 e. CC'), L3(pn1)], 'subne0d', '( P - 1 ) =/= 0')
    z1pn = s3([z1p, p1n], 'eqnetrd', '( %s ` P ) =/= 0' % Z1)
    z1hh = s3([w.s([], 'hsub1', S['hsub1'])], 'a1i', S['hsub1'])
    ob = hml(OG, 'g', '0', Z1, gh, gp, z1hh, z1pn, L3(ng), s3([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), qb_all)
    QO = '( %s holord P )' % Q1
    eqo = s3([s3([oa], 'eqcomd', '( %s + %s ) = %s' % (OH, OE, QO)), s3([ob, s3([s3([L3(ng)], 'nn0cnd', '%s e. CC' % OG)], 'addridd', '( %s + 0 ) = %s' % (OG, OG))], 'eqtrd', '%s = %s' % (QO, OG))],
             'eqtrd', '( %s + %s ) = %s' % (OH, OE, OG))
    lv = {OH: s3([L3(nh)], 'nn0red', '%s e. RR' % OH), OE: s3([L3(ne)], 'nn0red', '%s e. RR' % OE), OG: s3([L3(ng)], 'nn0red', '%s e. RR' % OG)}
    le = lin8(w, A3, [eqo, s3([L3(nh)], 'nn0ge0d', '0 <_ %s' % OH)], '%s <_ %s' % (OE, OG), lv)
    # exists-eliminations
    el3 = w.s([w.s([le], 'ex', '( %s -> ( %s -> %s <_ %s ) )' % (A2, IH, OE, OG))], 'exlimdv', '( %s -> ( %s -> %s <_ %s ) )' % (A2, XH, OE, OG))
    r3 = w.s([lift(w, s([hfh, w.inst('simpr')], 'syl', XH), A2), el3], 'mpd', '( %s -> %s <_ %s )' % (A2, OE, OG))
    el2 = w.s([w.s([r3], 'ex', '( %s -> ( %s -> %s <_ %s ) )' % (A1, IG, OE, OG))], 'exlimdv', '( %s -> ( %s -> %s <_ %s ) )' % (A1, XG, OE, OG))
    r2 = w.s([lift(w, s([hfg, w.inst('simpr')], 'syl', XG), A1), el2], 'mpd', '( %s -> %s <_ %s )' % (A1, OE, OG))
    el1 = s([w.s([r2], 'ex', '( %s -> ( %s -> %s <_ %s ) )' % (A0, IE, OE, OG))], 'exlimdv', '( %s -> %s <_ %s )' % (XE, OE, OG))
    ordle = s([s([hfe, w.inst('simpr')], 'syl', XE), el1], 'mpd', '%s <_ %s' % (OE, OG))
    # zeros
    Az = '( %s /\\ ( %s ` P ) = 0 )' % (A0, E1)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    erP0 = sz([lift(w, ph, Az), w.inst('etarel')], 'syl', tsub(S['etarel'], {'S': 'P'}).split(' -> ', 1)[1][:-2])
    d1 = conv(Az, ETA, ETAa, eeq, 'P'); d2 = conv(Az, GF, GFa, geq, 'P')
    erP = sz([sz([sz([d1], 'oveq2d', '( ( P - 1 ) x. ( %s ` P ) ) = ( ( P - 1 ) x. ( %s ` P ) )' % (ETA, ETAa))], 'eqcomd', '( ( P - 1 ) x. ( %s ` P ) ) = ( ( P - 1 ) x. ( %s ` P ) )' % (ETAa, ETA)),
              sz([erP0, sz([d2], 'oveq1d', '( ( %s ` P ) x. ( %s ` P ) ) = ( ( %s ` P ) x. ( %s ` P ) )' % (GF, E1, GFa, E1))], 'eqtrd', '( ( P - 1 ) x. ( %s ` P ) ) = ( ( %s ` P ) x. ( %s ` P ) )' % (ETA, GFa, E1))],
             'eqtrd', '( ( P - 1 ) x. ( %s ` P ) ) = ( ( %s ` P ) x. ( %s ` P ) )' % (ETAa, GFa, E1))
    gpc = fcc(w, Az, lift(w, gfa, Az), GFa, HP0, 'P', lift(w, ph, Az))
    z0 = sz([sz([sz([], 'simpr', '( %s ` P ) = 0' % E1)], 'oveq2d', '( ( %s ` P ) x. ( %s ` P ) ) = ( ( %s ` P ) x. 0 )' % (GFa, E1, GFa)), sz([gpc], 'mul01d', '( ( %s ` P ) x. 0 ) = 0' % GFa)], 'eqtrd',
            '( ( %s ` P ) x. ( %s ` P ) ) = 0' % (GFa, E1))
    pz = sz([erP, z0], 'eqtrd', '( ( P - 1 ) x. ( %s ` P ) ) = 0' % ETAa)
    epc = fcc(w, Az, lift(w, etaa, Az), ETAa, HP0, 'P', lift(w, ph, Az))
    mo = sz([sz([lift(w, pc, Az), sz([], '1cnd', '1 e. CC')], 'subcld', '( P - 1 ) e. CC'), epc], 'mul0ord', '( ( ( P - 1 ) x. ( %s ` P ) ) = 0 <-> ( ( P - 1 ) = 0 \\/ ( %s ` P ) = 0 ) )' % (ETAa, ETAa))
    orr = sz([pz, mo], 'mpbid', '( ( P - 1 ) = 0 \\/ ( %s ` P ) = 0 )' % ETAa)
    nz = sz([sz([lift(w, pc, Az), sz([], '1cnd', '1 e. CC'), lift(w, pn1, Az)], 'subne0d', '( P - 1 ) =/= 0')], 'neneqd', '-. ( P - 1 ) = 0')
    ez = sz([orr, nz], 'orcnd' if False else 'ord', '( %s ` P ) = 0' % ETAa) if False else sz([nz, orr], 'x', 'x') if False else None
    ez = sz([sz([orr], 'ord', '( -. ( P - 1 ) = 0 -> ( %s ` P ) = 0 )' % ETAa), nz], 'x', 'x') if False else sz([nz, sz([orr], 'ord', '( -. ( P - 1 ) = 0 -> ( %s ` P ) = 0 )' % ETAa)], 'mpd', '( %s ` P ) = 0' % ETAa)
    zimp = s([ez], 'ex', '( ( %s ` P ) = 0 -> ( %s ` P ) = 0 )' % (E1, ETAa))
    oeq = s([eeq], 'oveq1d', '( %s holord P ) = ( %s holord P )' % (ETA, ETAa))
    ordle2 = s([ordle, s([oeq], 'eqcomd', '( %s holord P ) = ( %s holord P )' % (ETAa, ETA))], 'breqtrd', '%s <_ ( %s holord P )' % (OE, ETA))
    zq = s([s([conv(A0, ETA, ETAa, eeq, 'P')], 'eqeq1d', '( ( %s ` P ) = 0 <-> ( %s ` P ) = 0 )' % (ETA, ETAa))], 'x', 'x') if False else s([conv(A0, ETA, ETAa, eeq, 'P')], 'eqeq1d', '( ( %s ` P ) = 0 <-> ( %s ` P ) = 0 )' % (ETA, ETAa))
    zimp2 = s([zimp, zq], 'sylibrd', '( ( %s ` P ) = 0 -> ( %s ` P ) = 0 )' % (E1, ETA))
    w.qed([ordle2, zimp2], 'jca', S['zc1ezt'])
    return run8(w)


S['etaord'] = '( P e. %s -> ( %s holord P ) e. NN0 )' % (HP0, ETA)


def gen_etaord():
    w = W('etaord', 'The Abel-summed eta function has finite order at every point of the right half-plane (Lean ` analyticOrderAt_etaFun_ne_top ` ; ~ hp0ordf ).')
    A0 = 'P e. %s' % HP0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ph = s([], 'id', A0)
    etah = s([s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0')], 'jca', '( 0 e. RR /\\ 0 <_ 0 )'), w.inst('etahol')], 'syl', HOLF(ETA, HP0))
    ce = w.s([w.s([w.s([w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( k ^c -u z ) = ( k ^c -u a ) )'),
                          w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( ( k + 1 ) ^c -u z ) = ( ( k + 1 ) ^c -u a ) )')], 'oveq12d',
                         '( z = a -> ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) = ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) )')], 'oveq2d',
                    '( z = a -> ( ( k mod 2 ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) ) = ( ( k mod 2 ) x. ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) ) )')], 'sumeq2sdv',
              '( z = a -> %s = %s )' % (EB % ('z', 'z'), EB % ('a', 'a')))
    etaa, eeq = renamed_hol(w, A0, etah, ETA, ETAa, ce)
    def ctr():
        c0 = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('etactr')], 'syl', '( 1 / 4 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % ETA)
        cv = s([s([eeq], 'fveq1d', '( %s ` ( 2 + ( _i x. 0 ) ) ) = ( %s ` ( 2 + ( _i x. 0 ) ) )' % (ETA, ETAa))], 'fveq2d',
               '( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) ) = ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % (ETA, ETAa))
        return s([c0, cv], 'breqtrd', '( 1 / 4 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % ETAa), '( 1 / 4 )'
    h2 = h2of(w, A0, ETAa, etaa, ctr)
    HF = tsub(S['hp0ordf'], {'F': ETAa})
    hfa, hfc = ante_of(HF)
    hf = s([s([h2, ph], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc)
    n0 = s([hf, w.inst('simpl')], 'syl', '( %s holord P ) e. NN0' % ETAa)
    w.qed([s([s([eeq], 'oveq1d', '( %s holord P ) = ( %s holord P )' % (ETA, ETAa)), n0], 'eqeltrd', '( %s holord P ) e. NN0' % ETA)], 'x', 'x') if False else \
        w.lines.append('qed:%s:idi |- %s' % (s([s([eeq], 'oveq1d', '( %s holord P ) = ( %s holord P )' % (ETA, ETAa)), n0], 'eqeltrd', '( %s holord P ) e. NN0' % ETA), S['etaord']))
    return run8(w)


if __name__ == '__main__':
    gen_zc1ezt()
    gen_etaord()
