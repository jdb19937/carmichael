"""Sortie T21a: the zone split t21split (Lean zeroSumTotal_split)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_
import num, lin
import cl as _cl
lin.FASTPATH = True
from tm import W


def gen_split():
    w = W('t21split', 'The four-zone split of the weighted zero sum: for ` 1 / 2 <_ A <_ B <_ C <_ 1 ` the sum over ` ZF ( 1 / 2 , T ) ` is the sum of the zones ` [ 1 / 2 , A ) ` , ` [ A , B ) ` , ` [ B , C ) ` and ` [ C , 1 ] ` (Lean ` zeroSumTotal_split ` ; ~ fsumsplit , ~ t21zfss ).')
    A0 = ante_of(S['t21split'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    nn, tr, yp, ar, br, cr, ha, ab, bc, c1 = [u[k] for k in ['N e. NN', 'T e. RR', 'Y e. RR+', 'A e. RR', 'B e. RR', 'C e. RR', '%s <_ A' % HALF, 'A <_ B', 'B <_ C', 'C <_ 1']]
    hr = st([num.real(w, HALF)], 'a1i', '%s e. RR' % HALF)
    Z = {k: ZFX(k, 'T') for k in [HALF, 'A', 'B', 'C']}
    C1 = '( %s /\\ x e. %s )' % (A0, DB)
    L = lambda s_, A_=C1: _cl.lift(w, s_, A_)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (C1, DB))
    h0 = st([num.lt_lit(w, '0', HALF) if hasattr(num, 'lt_lit') else num.le_lit(w, '0', HALF, strict=True)], 'a1i', '0 < %s' % HALF)
    h1 = lin.linarith(w, A0, [ab, bc, c1, ha], '%s <_ 1' % HALF, leaves={'A': ar, 'B': br, 'C': cr})
    ez = ap_(w, C1, [L(nn), xin, L(hr), L(h0), L(h1), L(tr)], 'ezf', '( %s e. Fin /\\ A. q e. %s %s e. NN )' % (Z[HALF], Z[HALF], ORD()))
    fin0 = w.s([ez], 'simpld', '( %s -> %s e. Fin )' % (C1, Z[HALF]))
    tle = st([tr], 'leidd', 'T <_ T')
    def ss(a, b, ar_, br_, ab_):
        return ap_(w, C1, [L(ar_), L(br_), L(ab_), L(tr), L(tr), L(tle)], 't21zfss', '%s C_ %s' % (Z[b], Z[a]))
    hA = ss(HALF, 'A', hr, ar, ha); AB = ss('A', 'B', ar, br, ab); BC = ss('B', 'C', br, cr, bc)
    sA = hA
    sB = w.s([AB, hA], 'sstrd', '( %s -> %s C_ %s )' % (C1, Z['B'], Z[HALF]))
    sC = w.s([BC, sB], 'sstrd', '( %s -> %s C_ %s )' % (C1, Z['C'], Z[HALF]))
    # the body on ZF(1/2)
    F = '( %s x. %s )' % (WT(), YR('Y'))
    C2 = '( %s /\\ q e. %s )' % (C1, Z[HALF])
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, Z[HALF]))
    qf = q_facts(w, C2, qin, L(hr, C2), L(tr, C2), HALF, 'T')
    ordn = w.s([L(w.s([ez], 'simprd', '( %s -> A. q e. %s %s e. NN )' % (C1, Z[HALF], ORD())), C2), qin, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (Z[HALF], ORD(), Z[HALF], ORD()))], 'sylc', '( %s -> %s e. NN )' % (C2, ORD()))
    wr, _, _ = wt_facts(w, C2, w.s([ordn], 'nnred', '( %s -> %s e. RR )' % (C2, ORD())), w.s([w.s([ordn], 'nnnn0d', '( %s -> %s e. NN0 )' % (C2, ORD()))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (C2, ORD())), qf)
    fr = w.s([wr, w.s([L(yp, C2), qf['re']], 'rpcxpcld', '( %s -> %s e. RR+ )' % (C2, YR('Y')))], 'x', 'x') if False else w.s([wr, w.s([w.s([L(yp, C2), qf['re']], 'rpcxpcld', '( %s -> %s e. RR+ )' % (C2, YR('Y')))], 'rpred', '( %s -> %s e. RR )' % (C2, YR('Y')))], 'remulcld', '( %s -> %s e. RR )' % (C2, F))
    fc = w.s([fr], 'recnd', '( %s -> %s e. CC )' % (C2, F))

    def sub_body(Vset, subst):
        """( ( C1 /\\ q e. Vset ) -> F e. RR ) from Vset C_ ZF(1/2)"""
        Cv = '( %s /\\ q e. %s )' % (C1, Vset)
        m = w.s([w.s([], 'simpl', '( %s -> %s )' % (Cv, C1)), w.s([L(subst, Cv), w.s([], 'simpr', '( %s -> q e. %s )' % (Cv, Vset))], 'sseldd', '( %s -> q e. %s )' % (Cv, Z[HALF]))], 'jca', '( %s -> %s )' % (Cv, C2))
        return w.s([m, fr], 'syl', '( %s -> %s e. RR )' % (Cv, F))

    def split(Uu, Vv, subV, finU):
        """( C1 -> sum_U F = ( sum_(U\\V) F + sum_V F ) ) for V C_ U (subV), U fin, F in CC on U (via ZF(1/2))"""
        D = '( %s \\ %s )' % (Uu, Vv)
        dj = w.s([w.s([], 'disjdifr', '( %s i^i %s ) = (/)' % (D, Vv))], 'a1i', '( %s -> ( %s i^i %s ) = (/) )' % (C1, D, Vv))
        un = w.s([w.s([subV, w.s([], 'undifr', '( %s C_ %s <-> ( %s u. %s ) = %s )' % (Vv, Uu, D, Vv, Uu))], 'sylib', '( %s -> ( %s u. %s ) = %s )' % (C1, D, Vv, Uu))], 'eqcomd', '( %s -> %s = ( %s u. %s ) )' % (C1, Uu, D, Vv))
        return un, dj, D
    SU = lambda X_: 'sum_ q e. %s %s' % (X_, F)
    # split 1: ZF(1/2) = ( ZF(1/2) \ ZF(A) ) u. ZF(A)
    un1, dj1, D1 = split(Z[HALF], Z['A'], sA, fin0)
    sp1 = w.s([dj1, un1, fin0, fc], 'fsumsplit', '( %s -> %s = ( %s + %s ) )' % (C1, SU(Z[HALF]), SU(D1), SU(Z['A'])))
    finA = ap_(w, C1, [fin0, sA], 'ssfi', '%s e. Fin' % Z['A'])
    CA = '( %s /\\ q e. %s )' % (C1, Z['A'])
    fcA = w.s([sub_body(Z['A'], sA)], 'recnd', '( %s -> %s e. CC )' % (CA, F))
    un2, dj2, D2 = split(Z['A'], Z['B'], AB, finA)
    sp2 = w.s([dj2, un2, finA, fcA], 'fsumsplit', '( %s -> %s = ( %s + %s ) )' % (C1, SU(Z['A']), SU(D2), SU(Z['B'])))
    finB = ap_(w, C1, [fin0, sB], 'ssfi', '%s e. Fin' % Z['B'])
    CB = '( %s /\\ q e. %s )' % (C1, Z['B'])
    fcB = w.s([sub_body(Z['B'], sB)], 'recnd', '( %s -> %s e. CC )' % (CB, F))
    un3, dj3, D3 = split(Z['B'], Z['C'], BC, finB)
    sp3 = w.s([dj3, un3, finB, fcB], 'fsumsplit', '( %s -> %s = ( %s + %s ) )' % (C1, SU(Z['B']), SU(D3), SU(Z['C'])))
    finC = ap_(w, C1, [fin0, sC], 'ssfi', '%s e. Fin' % Z['C'])
    # reals of the parts
    difss = lambda Uu, Vv, subU: w.s([w.s([w.s([], 'difss', '( %s \\ %s ) C_ %s' % (Uu, Vv, Uu))], 'a1i', '( %s -> ( %s \\ %s ) C_ %s )' % (C1, Uu, Vv, Uu)), subU], 'sstrd', '( %s -> ( %s \\ %s ) C_ %s )' % (C1, Uu, Vv, Z[HALF]))
    idss = w.s([w.s([], 'ssid', '%s C_ %s' % (Z[HALF], Z[HALF]))], 'a1i', '( %s -> %s C_ %s )' % (C1, Z[HALF], Z[HALF]))
    parts = [(D1, difss(Z[HALF], Z['A'], idss)), (D2, difss(Z['A'], Z['B'], sA)), (D3, difss(Z['B'], Z['C'], sB)), (Z['C'], sC), (Z['A'], sA), (Z['B'], sB)]
    c = _cl.Closure(w, C1, {})
    realst = {}
    for Xs, sub in parts:
        fin_ = ap_(w, C1, [fin0, sub], 'ssfi', '%s e. Fin' % Xs)
        r_ = w.s([fin_, sub_body(Xs, sub)], 'fsumrecl', '( %s -> %s e. RR )' % (C1, SU(Xs)))
        c.leaf(SU(Xs), 'RR', r_); realst[Xs] = r_
    c.leaf(SU(Z[HALF]), 'RR', w.s([fin0, fr], 'fsumrecl', '( %s -> %s e. RR )' % (C1, SU(Z[HALF]))))
    RHS1 = '( ( ( %s + %s ) + %s ) + %s )' % (SU(D1), SU(D2), SU(D3), SU(Z['C']))
    per = lin.lineq(w, C1, SU(Z[HALF]), RHS1, hyps=[sp1, sp2, sp3], closure=c)
    # outer sums
    DBfin = w.s([nn, w.s([w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'), w.s([], 'eqid', '%s = %s' % (DB, DB))], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB)], 'syl', '( %s -> %s e. Fin )' % (A0, DB))
    SX = lambda b: 'sum_ x e. %s %s' % (DB, b)
    o1 = st([per], 'sumeq2dv', '%s = %s' % (SX(SU(Z[HALF])), SX(RHS1)))
    cc = lambda X_: w.s([realst[X_]], 'recnd', '( %s -> %s e. CC )' % (C1, SU(X_)))
    ab_ = '( %s + %s )' % (SU(D1), SU(D2)); abc = '( %s + %s )' % (ab_, SU(D3))
    abr = w.s([realst[D1], realst[D2]], 'readdcld', '( %s -> %s e. RR )' % (C1, ab_))
    abcr = w.s([abr, realst[D3]], 'readdcld', '( %s -> %s e. RR )' % (C1, abc))
    o2 = st([DBfin, w.s([abcr], 'recnd', '( %s -> %s e. CC )' % (C1, abc)), cc(Z['C'])], 'fsumadd', '%s = ( %s + %s )' % (SX(RHS1), SX(abc), SX(SU(Z['C']))))
    o3 = st([DBfin, w.s([abr], 'recnd', '( %s -> %s e. CC )' % (C1, ab_)), cc(D3)], 'fsumadd', '%s = ( %s + %s )' % (SX(abc), SX(ab_), SX(SU(D3))))
    o4 = st([DBfin, cc(D1), cc(D2)], 'fsumadd', '%s = ( %s + %s )' % (SX(ab_), SX(SU(D1)), SX(SU(D2))))
    e34 = st([o3, st([o4], 'oveq1d', '( %s + %s ) = ( ( %s + %s ) + %s )' % (SX(ab_), SX(SU(D3)), SX(SU(D1)), SX(SU(D2)), SX(SU(D3))))], 'eqtrd', '%s = ( ( %s + %s ) + %s )' % (SX(abc), SX(SU(D1)), SX(SU(D2)), SX(SU(D3))))
    e2 = st([o2, st([e34], 'oveq1d', '( %s + %s ) = ( ( ( %s + %s ) + %s ) + %s )' % (SX(abc), SX(SU(Z['C'])), SX(SU(D1)), SX(SU(D2)), SX(SU(D3)), SX(SU(Z['C']))))], 'eqtrd',
            '%s = ( ( ( %s + %s ) + %s ) + %s )' % (SX(RHS1), SX(SU(D1)), SX(SU(D2)), SX(SU(D3)), SX(SU(Z['C']))))
    fin = st([o1, e2], 'eqtrd', '%s = ( ( ( %s + %s ) + %s ) + %s )' % (SX(SU(Z[HALF])), SX(SU(D1)), SX(SU(D2)), SX(SU(D3)), SX(SU(Z['C']))))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21split']))
    return run(w)


if __name__ == '__main__':
    gen_split()
