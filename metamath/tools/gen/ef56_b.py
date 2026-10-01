"""Sortie EF56: the eta order decomposition on the right half-plane (ef5ez; Lean analyticOrderNatAt_eta_decomp,
ord_gFun_one), after ZC1's zc1ezt."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from cl import lift
import congr as _cg
from c8_o import numst
import zc1_c, zc1_f, zc1_i, zc1_j, zc1_m, zc1_q, zc1_r, zc1_s
from zc1_r import ETAa, GFa, renamed_hol, EB
from zc1_j import Z1, two_nz
from zc1_m import e_h2
from zc1_q import hp_cc
from zc1_s import h2of
import lin
lin.FASTPATH = True


def build(w, A0, case1):
    """( A0 -> ( ( ETA holord P ) + if ( P = 1 , 1 , 0 ) ) = ( ( GF holord P ) + ( E1 holord P ) ) ) where A0 is
    ( P e. HP0 /\\ P = 1 ) (case1) or ( P e. HP0 /\\ P =/= 1 )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ph = s([], 'simpl', 'P e. %s' % HP0)
    pq = s([], 'simpr', 'P = 1' if case1 else 'P =/= 1')
    he1 = e_h2(w, A0, nx1(w, A0), '1', U1)
    etah = hol_eta(w, A0)
    def conv(ante, M, Ma, eqst, x):
        return w.s([lift(w, eqst, ante)], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ante, M, x, Ma, x))
    def ctr_eta():
        c0 = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('etactr')], 'syl', '( 1 / 4 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % ETA)
        cv = s([conv(A0, ETA, ETAa, eeq, '( 2 + ( _i x. 0 ) )')], 'fveq2d', '( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) ) = ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % (ETA, ETAa))
        return s([c0, cv], 'breqtrd', '( 1 / 4 ) <_ ( abs ` ( %s ` ( 2 + ( _i x. 0 ) ) ) )' % ETAa), '( 1 / 4 )'
    gfh = hol_gf(w, A0)
    ce = w.s([w.s([w.s([w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( k ^c -u z ) = ( k ^c -u a ) )'),
                          w.s([w.s([], 'negeq', '( z = a -> -u z = -u a )')], 'oveq2d', '( z = a -> ( ( k + 1 ) ^c -u z ) = ( ( k + 1 ) ^c -u a ) )')], 'oveq12d',
                         '( z = a -> ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) = ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) )')], 'oveq2d',
                    '( z = a -> ( ( k mod 2 ) x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) ) = ( ( k mod 2 ) x. ( ( k ^c -u a ) - ( ( k + 1 ) ^c -u a ) ) ) )')], 'sumeq2sdv',
              '( z = a -> %s = %s )' % (EB % ('z', 'z'), EB % ('a', 'a')))
    etaa, eeq = renamed_hol(w, A0, etah, ETA, ETAa, ce)
    cg = w.s([w.s([w.s([], 'oveq2', '( z = a -> ( 1 - z ) = ( 1 - a ) )')], 'oveq2d', '( z = a -> ( 2 ^c ( 1 - z ) ) = ( 2 ^c ( 1 - a ) ) )')], 'oveq2d',
             '( z = a -> ( 1 - ( 2 ^c ( 1 - z ) ) ) = ( 1 - ( 2 ^c ( 1 - a ) ) ) )')
    gfa, geq = renamed_hol(w, A0, gfh, GF, GFa, cg)
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
        HF = tsub(stmt('hp0ordf'), {'F': F, 'g': g})
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
    ie = w.s([w.s([], 'simpll', '( %s -> %s )' % (A3, A1)), w.inst('simpr')], 'syl', '( %s -> %s )' % (A3, IE))
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
    er0 = sv([vh, w.inst('etarel')], 'syl', tsub(stmt('etarel'), {'S': 'v'}).split(' -> ', 1)[1][:-2])
    c1 = conv(Av, ETA, ETAa, eeq, 'v'); c2 = conv(Av, GF, GFa, geq, 'v')
    er = sv([sv([sv([c1], 'oveq2d', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( v - 1 ) x. ( %s ` v ) )' % (ETA, ETAa))], 'eqcomd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( v - 1 ) x. ( %s ` v ) )' % (ETAa, ETA)),
             sv([er0, sv([c2], 'oveq1d', '( ( %s ` v ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (GF, E1, GFa, E1))], 'eqtrd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (ETA, GFa, E1))],
            'eqtrd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( %s ` v ) )' % (ETAa, GFa, E1))
    vc, _ = hp_cc(w, Av, vh, 'v')
    pc, _ = hp_cc(w, A0, ph, 'P')
    vp = sv([vc, lift(w, pc, Av)], 'subcld', '( v - P ) e. CC')
    v1c = sv([vc, sv([], '1cnd', '1 e. CC')], 'subcld', '( v - 1 ) e. CC')
    etvc = fcc(w, Av, lift(w, etaa, Av), ETAa, HP0, 'v', vh)
    q_b0 = sv([qv, sv([er], 'eqcomd', '( ( %s ` v ) x. ( %s ` v ) ) = ( ( v - 1 ) x. ( %s ` v ) )' % (GFa, E1, ETAa))], 'eqtrd', '( %s ` v ) = ( ( v - 1 ) x. ( %s ` v ) )' % (Q1, ETAa))
    q1cn = s3([q1h, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (Q1, HP0))
    def hml(M_, g_, N_, h_, gst, gpst, hst, hpst, mst, nst, allst):
        HM = tsub(stmt('holordml'), {'F': Q1, 'D': HP0, 'M': M_, 'N': N_, 'G': g_, 'H': h_})
        hma, hmc = ante_of(HM)
        K1, K2, K3 = top_and(hma)
        k1 = s3([q1cn, L3(ph)], 'jca', K1)
        k2 = s3([s3([mst, gst, gpst], '3jca', top_and(K2)[0]), s3([nst, hst, hpst], '3jca', top_and(K2)[1])], 'jca', K2)
        return s3([s3([k1, k2, allst], '3jca', hma), w.inst('holordml')], 'syl', hmc)
    oa = hml(OH, 'h', OE, 'e', hh, hp, eh, ep, L3(nh), L3(ne), qa_all)
    QO = '( %s holord P )' % Q1
    ogc = s3([L3(ng)], 'nn0cnd', '%s e. CC' % OG)
    if case1:
        # ( v - 1 ) = ( v - P ): Q1 v = ( v - P ) ^ ( OG + 1 ) g v
        vpe = sv([sv([lift(w, pq, Av)], 'eqcomd', '1 = P')], 'oveq2d', '( v - 1 ) = ( v - P )')
        gvc = sv([sv([sv([gh, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % ('g', HP0)) if False else lift(w, s3([gh, w.inst('simpl')], 'syl', 'g e. ( %s -cn-> CC )' % HP0), Av), w.inst('cncff')], 'syl', 'g : %s --> CC' % HP0), vh], 'ffvelcdmd', '( g ` v ) e. CC')
        pwc = sv([vp, lift(w, ng, Av)], 'expcld', '( ( v - P ) ^ %s ) e. CC' % OG)
        OG1 = '( %s + 1 )' % OG
        t1 = sv([q_b0, sv([vpe, gfv], 'oveq12d', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( v - P ) x. %s )' % (ETAa, FG))], 'eqtrd', '( %s ` v ) = ( ( v - P ) x. %s )' % (Q1, FG))
        t2 = sv([vp, pwc, gvc], 'mul12d', '( ( v - P ) x. %s ) = ( ( ( v - P ) ^ %s ) x. ( ( v - P ) x. ( g ` v ) ) )' % (FG, OG))
        t3 = sv([sv([vp, pwc, gvc], 'mulassd', '( ( ( ( v - P ) ^ %s ) x. ( v - P ) ) x. ( g ` v ) ) = ( ( ( v - P ) ^ %s ) x. ( ( v - P ) x. ( g ` v ) ) )' % (OG, OG)) if False else
                sv([pwc, vp, gvc], 'mulassd', '( ( ( ( v - P ) ^ %s ) x. ( v - P ) ) x. ( g ` v ) ) = ( ( ( v - P ) ^ %s ) x. ( ( v - P ) x. ( g ` v ) ) )' % (OG, OG))], 'eqcomd',
                '( ( ( v - P ) ^ %s ) x. ( ( v - P ) x. ( g ` v ) ) ) = ( ( ( ( v - P ) ^ %s ) x. ( v - P ) ) x. ( g ` v ) )' % (OG, OG))
        t4 = sv([sv([sv([vp, lift(w, ng, Av)], 'expp1d', '( ( v - P ) ^ %s ) = ( ( ( v - P ) ^ %s ) x. ( v - P ) )' % (OG1, OG))], 'eqcomd',
                    '( ( ( v - P ) ^ %s ) x. ( v - P ) ) = ( ( v - P ) ^ %s )' % (OG, OG1))], 'oveq1d', '( ( ( ( v - P ) ^ %s ) x. ( v - P ) ) x. ( g ` v ) ) = ( ( ( v - P ) ^ %s ) x. ( g ` v ) )' % (OG, OG1))
        qc = sv([sv([sv([t1, t2], 'eqtrd', '( %s ` v ) = ( ( ( v - P ) ^ %s ) x. ( ( v - P ) x. ( g ` v ) ) )' % (Q1, OG)), t3], 'eqtrd', '( %s ` v ) = ( ( ( ( v - P ) ^ %s ) x. ( v - P ) ) x. ( g ` v ) )' % (Q1, OG)), t4],
                'eqtrd', '( %s ` v ) = ( ( ( v - P ) ^ %s ) x. ( g ` v ) )' % (Q1, OG1))
        qall_v = s3([qc], 'ralrimiva', 'A. v e. %s ( %s ` v ) = ( ( ( v - P ) ^ %s ) x. ( g ` v ) )' % (HP0, Q1, OG1))
        BZ_ = '( ( %s ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) )' % (Q1, OG1)
        cb, _ = cbvral(w, HP0, 'v', 'z', '( %s ` v ) = ( ( ( v - P ) ^ %s ) x. ( g ` v ) )' % (Q1, OG1))
        qall = s3([qall_v, s3([cb], 'a1i' if False else 'a1i', '( A. v e. %s ( %s ` v ) = ( ( ( v - P ) ^ %s ) x. ( g ` v ) ) <-> A. z e. %s ( %s ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) )' % (HP0, Q1, OG1, HP0, Q1, OG1))],
                  'mpbid', 'A. z e. %s ( %s ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) )' % (HP0, Q1, OG1))
        HE = tsub(stmt('holordeq'), {'F': Q1, 'V': '_V', 'E': HP0, 'G': 'g', 'N': OG1})
        hea, hec = ante_of(HE)
        K1, K2, K3 = top_and(hea)
        k1 = s3([s3([w.s([w.s([w.s([], 'hpopn', '%s e. ( TopOpen ` CCfld )' % HP0)], 'elexi', '%s e. _V' % HP0)], 'mptex', '%s e. _V' % Q1)], 'a1i', '%s e. _V' % Q1), s3([s3([w.s([], 'hpopn', '%s e. ( TopOpen ` CCfld )' % HP0)], 'a1i', '%s e. ( TopOpen ` CCfld )' % HP0), L3(ph)], 'jca',
                                                                                   '( %s e. ( TopOpen ` CCfld ) /\\ P e. %s )' % (HP0, HP0))], 'jca', K1)
        k2 = s3([gh, gp], 'jca', K2)
        k3 = s3([s3([L3(ng), s3([], '1nn0', '1 e. NN0') if False else s3([w.s([], '1nn0', '1 e. NN0')], 'a1i', '1 e. NN0')], 'nn0addcld', '%s e. NN0' % OG1), qall], 'jca', K3)
        ob = s3([s3([k1, k2, k3], '3jca', hea), w.inst('holordeq')], 'syl', hec)
        RH = OG1
    else:
        e0 = sv([vp], 'exp0d', '( ( v - P ) ^ 0 ) = 1')
        z1v, _ = _cg.mptval(w, Av, 'z', HP0, '( z - 1 )', 'v', vh, exs=sv([w.s([], 'ovex', '( v - 1 ) e. _V')], 'a1i', '( v - 1 ) e. _V'), gen=w.g)
        r0 = sv([sv([e0, z1v], 'oveq12d', '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( 1 x. ( v - 1 ) )' % Z1), sv([v1c], 'mullidd', '( 1 x. ( v - 1 ) ) = ( v - 1 )')], 'eqtrd',
                '( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) = ( v - 1 )' % Z1)
        q_b1 = sv([q_b0, sv([v1c, etvc], 'mulcomd', '( ( v - 1 ) x. ( %s ` v ) ) = ( ( %s ` v ) x. ( v - 1 ) )' % (ETAa, ETAa))], 'eqtrd', '( %s ` v ) = ( ( %s ` v ) x. ( v - 1 ) )' % (Q1, ETAa))
        q_b = sv([q_b1, sv([gfv, sv([r0], 'eqcomd', '( v - 1 ) = ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) )' % Z1)], 'oveq12d', '( ( %s ` v ) x. ( v - 1 ) ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (ETAa, FG, Z1))],
                 'eqtrd', '( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (Q1, FG, Z1))
        qb_all = s3([q_b], 'ralrimiva', 'A. v e. %s ( %s ` v ) = ( %s x. ( ( ( v - P ) ^ 0 ) x. ( %s ` v ) ) )' % (HP0, Q1, FG, Z1))
        z1p, _ = _cg.mptval(w, A3, 'z', HP0, '( z - 1 )', 'P', L3(ph), exs=s3([w.s([], 'ovex', '( P - 1 ) e. _V')], 'a1i', '( P - 1 ) e. _V'), gen=w.g)
        p1n = s3([L3(pc), s3([], '1cnd', '1 e. CC'), L3(pq)], 'subne0d', '( P - 1 ) =/= 0')
        z1pn = s3([z1p, p1n], 'eqnetrd', '( %s ` P ) =/= 0' % Z1)
        z1hh = s3([w.s([], 'hsub1', stmt('hsub1'))], 'a1i', stmt('hsub1'))
        ob = hml(OG, 'g', '0', Z1, gh, gp, z1hh, z1pn, L3(ng), s3([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0'), qb_all)
        RH = '( %s + 0 )' % OG
    # OH + OE = QO = RH
    eqo = s3([s3([oa], 'eqcomd', '( %s + %s ) = %s' % (OH, OE, QO)), ob], 'eqtrd', '( %s + %s ) = %s' % (OH, OE, RH))
    IFT = ONE('P')
    ifv = s([pq if case1 else s([pq], 'neneqd', '-. P = 1')], 'iftrued' if case1 else 'iffalsed', '%s = %s' % (IFT, '1' if case1 else '0'))
    lhs = s3([s3([L3(ifv)], 'oveq2d', '( %s + %s ) = ( %s + %s )' % (OG, IFT, OG, '1' if case1 else '0'))], 'idi', '( %s + %s ) = %s' % (OG, IFT, RH))
    fin3 = s3([lhs, s3([eqo], 'eqcomd', '%s = ( %s + %s )' % (RH, OH, OE))], 'eqtrd', '( %s + %s ) = ( %s + %s )' % (OG, IFT, OH, OE))
    GOAL = '( %s + %s ) = ( %s + %s )' % (OG, IFT, OH, OE)
    el3 = w.s([w.s([fin3], 'ex', '( %s -> ( %s -> %s ) )' % (A2, IH, GOAL))], 'exlimdv', '( %s -> ( %s -> %s ) )' % (A2, XH, GOAL))
    r3 = w.s([lift(w, s([hfh, w.inst('simpr')], 'syl', XH), A2), el3], 'mpd', '( %s -> %s )' % (A2, GOAL))
    el2 = w.s([w.s([r3], 'ex', '( %s -> ( %s -> %s ) )' % (A1, IG, GOAL))], 'exlimdv', '( %s -> ( %s -> %s ) )' % (A1, XG, GOAL))
    r2 = w.s([lift(w, s([hfg, w.inst('simpr')], 'syl', XG), A1), el2], 'mpd', '( %s -> %s )' % (A1, GOAL))
    el1 = s([w.s([r2], 'ex', '( %s -> ( %s -> %s ) )' % (A0, IE, GOAL))], 'exlimdv', '( %s -> %s )' % (XE, GOAL))
    g0 = s([s([hfe, w.inst('simpr')], 'syl', XE), el1], 'mpd', GOAL)
    # back to ETA, GF
    oe = s([eeq], 'oveq1d', '( %s holord P ) = %s' % (ETA, OG))
    og = s([geq], 'oveq1d', '( %s holord P ) = %s' % (GF, OH))
    l2 = s([oe], 'oveq1d', '( ( %s holord P ) + %s ) = ( %s + %s )' % (ETA, IFT, OG, IFT))
    r2_ = s([og], 'oveq1d', '( ( %s holord P ) + %s ) = ( %s + %s )' % (GF, OE, OH, OE))
    return s([s([l2, g0], 'eqtrd', '( ( %s holord P ) + %s ) = ( %s + %s )' % (ETA, IFT, OH, OE)), s([r2_], 'eqcomd', '( %s + %s ) = ( ( %s holord P ) + %s )' % (OH, OE, GF, OE))], 'eqtrd',
             ante_of(S['ef5ez'])[1] if False else '( ( %s holord P ) + %s ) = ( ( %s holord P ) + %s )' % (ETA, IFT, GF, OE))


def gen_ez():
    w = W('ef5ez', 'Lean ` analyticOrderNatAt_eta_decomp ` and ` ord_gFun_one ` in one statement: on the right half-plane ` ord eta + [ P = 1 ] = ord g + ord E1 ` , ` E1 = ( s - 1 ) zeta ( s ) ` ( ~ etarel , ~ holordml , ~ holordeq ).')
    a = build(w, '( P e. %s /\\ P = 1 )' % HP0, True)
    b = build(w, '( P e. %s /\\ P =/= 1 )' % HP0, False)
    w.qed([a, b], 'pm2.61dane', S['ef5ez'])
    return run8(w)


GENS = {'ef5ez': gen_ez}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
