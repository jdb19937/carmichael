"""Sortie C10: the multiplicity count on SQ ( 2 + i T , 13 / 8 ) by four strips (lchrzc)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
import num
from c10_freeze import S as FS, ZSL, W0
from c8_n import sqparts, sqre_at, sqcc
from c8_o import numst
from c9_b import decode
import c9_h
patch_stmt(c9_h)
from c9_h import c0_facts
from c10_f import crfacts, clo
import lin
lin.FASTPATH = True

TS = ['( T - %s )' % R3932, '( T - %s )' % R1332, '( T + %s )' % R1332, '( T + %s )' % R3932]
ZK = [ZQ(t) for t in TS]
U12 = '( %s u. %s )' % (ZK[0], ZK[1])
U34 = '( %s u. %s )' % (ZK[2], ZK[3])
U4 = '( %s u. %s )' % (U12, U34)
HQ = '( %s holord q )' % LFN
SUMS = lambda Z: 'sum_ q e. %s %s' % (Z, HQ)
L80 = '( log ` %s )' % B80
L25 = '( log ` %s )' % R2524


def gen_lchrzc():
    w = W('lchrzc', 'The multiplicity mass of the zeros of ` L ( s , chi ) ` , ` chi ` nonprincipal, in the square of half-side ` 13 / 8 ` about ` 2 + i T ` is at most ` 4 log ( 80 N ( abs T + 2 ) ) / log ( 25 / 24 ) ` : four strips of height ` 13 / 16 ` ( ~ lchrzq , ~ fsumunle ).')
    A0 = '( %s /\\ T e. RR )' % CHI
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); tr = s([], 'simpr', 'T e. RR')
    c0, re0, im0 = c0_facts(w, A0, tr)
    m39 = numst(w, A0, R3932, 'RR'); m13 = numst(w, A0, R1332, 'RR')
    tks = [s([tr, m39], 'resubcld', '%s e. RR' % TS[0]), s([tr, m13], 'resubcld', '%s e. RR' % TS[1]),
           s([tr, m13], 'readdcld', '%s e. RR' % TS[2]), s([tr, m39], 'readdcld', '%s e. RR' % TS[3])]
    ZQ_ = tsub(FS['lchrzq'], {})
    zq = []
    for t, st in zip(TS, tks):
        f = tsub(FS['lchrzq'], {'T': t})
        a, c = ante_of(f)
        zq.append(s([s([chi, st], 'jca', a), w.inst('lchrzq')], 'syl', c))
    parts = [top_and(ante_of(tsub(FS['lchrzq'], {'T': t}))[1]) for t in TS]
    zf = [s([z, w.inst('simp1')], 'syl', p[0]) for z, p in zip(zq, parts)]
    al = [s([z, w.inst('simp2')], 'syl', p[1]) for z, p in zip(zq, parts)]
    iq = [s([z, w.inst('simp3')], 'syl', p[2]) for z, p in zip(zq, parts)]
    # the cover: ZSL C_ U4
    r138 = numst(w, A0, R138, 'RR')
    sa, sb = sqcc(w, A0, c0, r138, c=C0, r=R138)
    SA, SB = SQA(C0, R138), SQB(C0, R138)
    SQ13 = SQ(C0, R138)
    ps = sqparts(w, A0, sqre_at(w, A0, c0, r138, c=C0, r=R138), c=C0, r=R138)
    qk = []
    for k, tk in enumerate(TS):
        ta = s([tks[k], m13], 'resubcld', '( %s - %s ) e. RR' % (tk, R1332))
        tb = s([tks[k], m13], 'readdcld', '( %s + %s ) e. RR' % (tk, R1332))
        qk.append((crfacts(w, A0, '( 3 / 8 )', '( %s - %s )' % (tk, R1332), numst(w, A0, '( 3 / 8 )', 'RR'), ta),
                   crfacts(w, A0, '( ; 2 9 / 8 )', '( %s + %s )' % (tk, R1332), numst(w, A0, '( ; 2 9 / 8 )', 'RR'), tb)))
    Aq = '( %s /\\ q e. %s )' % (A0, ZSL)
    L = lambda st, a=Aq: lift(w, st, a)
    subr = w.s([w.s([], 'fveq2', '( r = q -> ( %s ` r ) = ( %s ` q ) )' % (LFN, LFN))], 'eqeq1d', '( r = q -> ( ( %s ` r ) = 0 <-> ( %s ` q ) = 0 ) )' % (LFN, LFN))
    el = w.s([subr], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( %s ` q ) = 0 ) )' % (ZSL, SQ13, LFN))
    qq = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, ZSL)), el], 'sylib', '( %s -> ( q e. %s /\\ ( %s ` q ) = 0 ) )' % (Aq, SQ13, LFN))
    qsq = w.s([qq, w.inst('simpl')], 'syl', '( %s -> q e. %s )' % (Aq, SQ13))
    lq0 = w.s([qq, w.inst('simpr')], 'syl', '( %s -> ( %s ` q ) = 0 )' % (Aq, LFN))
    d = decode(w, Aq, qsq, L(sa), L(sb), SA, SB, SQ13, U='q')
    qc = d[0]
    rq = w.s([qc], 'recld', '( %s -> ( Re ` q ) e. RR )' % Aq); iqr = w.s([qc], 'imcld', '( %s -> ( Im ` q ) e. RR )' % Aq)
    def memk(ante, k, cases):
        """( ante -> q e. U4 ) from the case hypotheses on Im q"""
        (qac, reA, imA), (qbc, reB, imB) = qk[k]
        QAt, QBt = QA(TS[k]), QB(TS[k])
        l = lambda st: lift(w, st, ante)
        lv = {'( Re ` q )': l(rq), '( Im ` q )': l(iqr), 'T': l(tr)}
        for e, st in (('( Re ` %s )' % C0, c0), ('( Im ` %s )' % C0, c0), ('( Re ` %s )' % SA, sa), ('( Im ` %s )' % SA, sa), ('( Re ` %s )' % SB, sb), ('( Im ` %s )' % SB, sb),
                      ('( Re ` %s )' % QAt, qac), ('( Im ` %s )' % QAt, qac), ('( Re ` %s )' % QBt, qbc), ('( Im ` %s )' % QBt, qbc)):
            lv[e] = w.s([l(st)], 'recld' if e.startswith('( Re') else 'imcld', '( %s -> %s e. RR )' % (ante, e))
        hy = [l(x) for x in [re0, im0, reA, imA, reB, imB] + ps + d[1:]] + cases
        ivs = []
        for part in ('Re', 'Im'):
            a_, b_, x_ = '( %s ` %s )' % (part, QAt), '( %s ` %s )' % (part, QBt), '( %s ` q )' % part
            lo = lin8(w, ante, hy, '%s <_ %s' % (a_, x_), lv); hi = lin8(w, ante, hy, '%s <_ %s' % (x_, b_), lv)
            e2 = w.s([lv[a_], lv[b_], w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (ante, x_, a_, b_, x_, a_, x_, x_, b_))
            ivs.append(w.s([w.s([lv[x_], lo, hi], '3jca', '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (ante, x_, a_, x_, x_, b_)), e2], 'mpbird',
                           '( %s -> %s e. ( %s [,] %s ) )' % (ante, x_, a_, b_)))
        Q = '( %s crect %s )' % (QAt, QBt)
        ELQ = '( q e. CC /\\ ( Re ` q ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` q ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (QAt, QBt, QAt, QBt)
        ec = w.s([w.s([l(qac), l(qbc)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ante, QAt, QBt)), w.inst('elcrect')], 'syl', '( %s -> ( q e. %s <-> %s ) )' % (ante, Q, ELQ))
        qQ = w.s([w.s([l(qc), ivs[0], ivs[1]], '3jca', '( %s -> %s )' % (ante, ELQ)), ec], 'mpbird', '( %s -> q e. %s )' % (ante, Q))
        qZ = w.s([subr, qQ, l(lq0)], 'elrabd', '( %s -> q e. %s )' % (ante, ZK[k]))
        if k < 2:
            u = w.s([qZ, w.inst('elun1' if k == 0 else 'elun2')], 'syl', '( %s -> q e. %s )' % (ante, U12))
            return w.s([u, w.inst('elun1')], 'syl', '( %s -> q e. %s )' % (ante, U4))
        u = w.s([qZ, w.inst('elun1' if k == 2 else 'elun2')], 'syl', '( %s -> q e. %s )' % (ante, U34))
        return w.s([u, w.inst('elun2')], 'syl', '( %s -> q e. %s )' % (ante, U4))
    M1, M2 = '( T - ( ; 1 3 / ; 1 6 ) )', '( T + ( ; 1 3 / ; 1 6 ) )'
    m1r = w.s([L(tr), L(numst(w, A0, '( ; 1 3 / ; 1 6 )', 'RR'))], 'resubcld', '( %s -> %s e. RR )' % (Aq, M1))
    m2r = w.s([L(tr), L(numst(w, A0, '( ; 1 3 / ; 1 6 )', 'RR'))], 'readdcld', '( %s -> %s e. RR )' % (Aq, M2))
    Alo = '( %s /\\ ( Im ` q ) <_ T )' % Aq
    Ahi = '( %s /\\ T <_ ( Im ` q ) )' % Aq
    def split(ante, c1, c2, k1, k2, a_, b_):
        A1_ = '( %s /\\ %s )' % (ante, c1); A2_ = '( %s /\\ %s )' % (ante, c2)
        m1 = memk(A1_, k1, [w.s([], 'simpr', '( %s -> %s )' % (A1_, c1)), lift(w, w.s([], 'simpr', '( %s -> %s )' % (ante, ante[len('( ' + Aq + ' /\\ '):-2])), A1_)])
        m2 = memk(A2_, k2, [w.s([], 'simpr', '( %s -> %s )' % (A2_, c2)), lift(w, w.s([], 'simpr', '( %s -> %s )' % (ante, ante[len('( ' + Aq + ' /\\ '):-2])), A2_)])
        tri = w.s([lift(w, a_, ante), lift(w, b_, ante)], 'letrid', '( %s -> ( %s \\/ %s ) )' % (ante, c1, c2))
        return w.s([m1, m2, tri], 'mpjaodan', '( %s -> q e. %s )' % (ante, U4))
    lo_ = split(Alo, '( Im ` q ) <_ %s' % M1, '%s <_ ( Im ` q )' % M1, 0, 1, iqr, m1r)
    hi_ = split(Ahi, '( Im ` q ) <_ %s' % M2, '%s <_ ( Im ` q )' % M2, 2, 3, iqr, m2r)
    tri = w.s([iqr, L(tr)], 'letrid', '( %s -> ( ( Im ` q ) <_ T \\/ T <_ ( Im ` q ) ) )' % Aq)
    qu = w.s([lo_, hi_, tri], 'mpjaodan', '( %s -> q e. %s )' % (Aq, U4))
    cov = s([w.s([qu], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, ZSL, U4))], 'ssrdv', '%s C_ %s' % (ZSL, U4))
    # finiteness
    u12f = s([zf[0], zf[1]], 'unfid', '%s e. Fin' % U12); u34f = s([zf[2], zf[3]], 'unfid', '%s e. Fin' % U34)
    u4f = s([u12f, u34f], 'unfid', '%s e. Fin' % U4)
    zslf = s([u4f, cov], 'ssfid', '%s e. Fin' % ZSL)
    # the terms are in NN on the union
    memo = {}
    def nnU(S_):
        if S_ in memo:
            return memo[S_]
        Au = '( %s /\\ q e. %s )' % (A0, S_)
        if S_ in ZK:
            r = w.s([al[ZK.index(S_)]], 'r19.21bi', '( %s -> %s e. NN )' % (Au, HQ))
        else:
            X_, Y_ = (ZK[0], ZK[1]) if S_ == U12 else (ZK[2], ZK[3]) if S_ == U34 else (U12, U34)
            ex = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Au, S_)), w.s([], 'elun', '( q e. %s <-> ( q e. %s \\/ q e. %s ) )' % (S_, X_, Y_))], 'sylib',
                     '( %s -> ( q e. %s \\/ q e. %s ) )' % (Au, X_, Y_))
            outs = []
            for Z_ in (X_, Y_):
                Ac = '( %s /\\ q e. %s )' % (Au, Z_)
                j = w.s([w.s([], 'simpll', '( %s -> %s )' % (Ac, A0)), w.s([], 'simpr', '( %s -> q e. %s )' % (Ac, Z_))], 'jca', '( %s -> ( %s /\\ q e. %s ) )' % (Ac, A0, Z_))
                outs.append(w.s([j, nnU(Z_)], 'syl', '( %s -> %s e. NN )' % (Ac, HQ)))
            r = w.s([outs[0], outs[1], ex], 'mpjaodan', '( %s -> %s e. NN )' % (Au, HQ))
        memo[S_] = r
        return r
    def rge(S_):
        Au = '( %s /\\ q e. %s )' % (A0, S_)
        n = nnU(S_)
        return (w.s([n], 'nnred', '( %s -> %s e. RR )' % (Au, HQ)), w.s([w.s([n], 'nnnn0d', '( %s -> %s e. NN0 )' % (Au, HQ))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (Au, HQ)))
    def fsu(A_, B_, C_, bf, cf, sub):
        r_, g_ = rge('( %s u. %s )' % (B_, C_))
        return s([bf, cf, sub, r_, g_], 'fsumunle', '%s <_ ( %s + %s )' % (SUMS(A_), SUMS(B_), SUMS(C_)))
    f1 = fsu(ZSL, U12, U34, u12f, u34f, cov)
    f2 = fsu(U12, ZK[0], ZK[1], zf[0], zf[1], s([], 'ssidd', '%s C_ %s' % (U12, U12)))
    f3 = fsu(U34, ZK[2], ZK[3], zf[2], zf[3], s([], 'ssidd', '%s C_ %s' % (U34, U34)))
    # each strip: S_k <_ L80 / L25
    l25p = s([s([numst(w, A0, R2524, 'RR+'), w.inst('loggt0b')], 'syl', '( 0 < %s <-> 1 < %s )' % (L25, R2524)), lin8(w, A0, [], '1 < %s' % R2524, {})], 'mpbird', '0 < %s' % L25)
    l25rp = s([s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25), l25p], 'elrpd', '%s e. RR+' % L25)
    nn = s([s([chi, w.inst('simpl')], 'syl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'), w.inst('simpl')], 'syl', 'N e. NN')
    nrp = s([nn], 'nnrpd', 'N e. RR+'); nr = s([nrp], 'rpred', 'N e. RR')
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    AT2 = '( ( abs ` T ) + 2 )'
    at2p = s([s([atr, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % AT2), lin8(w, A0, [ag0], '0 < %s' % AT2, {'( abs ` T )': atr})], 'elrpd', '%s e. RR+' % AT2)
    b80p = s([numst(w, A0, '; 8 0', 'RR+'), s([nrp, at2p], 'rpmulcld', '%s e. RR+' % XT)], 'rpmulcld', '%s e. RR+' % B80)
    l80r = s([b80p], 'relogcld', '%s e. RR' % L80)
    Q8 = '( %s / %s )' % (L80, L25)
    q8r = s([l80r, l25rp], 'rerpdivcld', '%s e. RR' % Q8)
    sk = []
    for k, tk in enumerate(TS):
        m = R3932 if k in (0, 3) else R1332
        mr = m39 if k in (0, 3) else m13
        tc = s([tr], 'recnd', 'T e. CC'); mc = s([mr], 'recnd', '%s e. CC' % m)
        am = s([mr, numst(w, A0, m, 'ge0')], 'absidd', '( abs ` %s ) = %s' % (m, m))
        tri = s([tc, mc], 'abs2dif2d' if k < 2 else 'abstrid', '( abs ` %s ) <_ ( ( abs ` T ) + ( abs ` %s ) )' % (tk, m))
        atk = s([s([tks[k]], 'recnd', '%s e. CC' % tk)], 'abscld', '( abs ` %s ) e. RR' % tk)
        AK2 = '( ( abs ` %s ) + 2 )' % tk
        lvk = {'( abs ` T )': atr, '( abs ` %s )' % tk: atk, '( abs ` %s )' % m: s([mc], 'abscld', '( abs ` %s ) e. RR' % m), 'N': nr}
        g = lin8(w, A0, [tri, am, ag0], '0 <_ ( ( 2 x. %s ) - %s )' % (AT2, AK2), lvk)
        c_ = clo(w, A0, lvk)
        hint = s([nr, c_.mem('( ( 2 x. %s ) - %s )' % (AT2, AK2), 'RR'), s([nrp], 'rpge0d', '0 <_ N'), g], 'mulge0d', '0 <_ ( N x. ( ( 2 x. %s ) - %s ) )' % (AT2, AK2))
        B40k = '( ; 4 0 x. ( N x. %s ) )' % AK2
        bl = lin.linarith(w, A0, [hint], '%s <_ %s' % (B40k, B80), closure=clo(w, A0, lvk), products=True)
        b40kp = s([numst(w, A0, '; 4 0', 'RR+'), s([nrp, s([s([atk, s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % AK2),
                                                          lin8(w, A0, [s([s([tks[k]], 'recnd', '%s e. CC' % tk)], 'absge0d', '0 <_ ( abs ` %s )' % tk)], '0 < %s' % AK2, lvk)], 'elrpd', '%s e. RR+' % AK2)],
                                                    'rpmulcld', '( N x. %s ) e. RR+' % AK2)], 'rpmulcld', '%s e. RR+' % B40k)
        ll = s([bl, s([b40kp, b80p], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ %s )' % (B40k, B80, B40k, L80))], 'mpbid', '( log ` %s ) <_ %s' % (B40k, L80))
        Sk = SUMS(ZK[k])
        skr = s([zf[k], rge(ZK[k])[0]], 'fsumrecl', '%s e. RR' % Sk)
        m1 = s([s([skr, s([l25rp], 'rpred', '%s e. RR' % L25)], 'remulcld', '( %s x. %s ) e. RR' % (Sk, L25)),
                s([b40kp], 'relogcld', '( log ` %s ) e. RR' % B40k), l80r, iq[k], ll], 'letrd', '( %s x. %s ) <_ %s' % (Sk, L25, L80))
        sk.append((skr, s([m1, s([skr, l80r, l25rp], 'lemuldivd', '( ( %s x. %s ) <_ %s <-> %s <_ %s )' % (Sk, L25, L80, Sk, Q8))], 'mpbid', '%s <_ %s' % (Sk, Q8))))
    Az = '( %s /\\ q e. %s )' % (A0, ZSL)
    qu4 = w.s([lift(w, cov, Az), w.s([], 'simpr', '( %s -> q e. %s )' % (Az, ZSL))], 'sseldd', '( %s -> q e. %s )' % (Az, U4))
    tz = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Az, A0)), qu4], 'jca', '( %s -> ( %s /\\ q e. %s ) )' % (Az, A0, U4)), rge(U4)[0]], 'syl', '( %s -> %s e. RR )' % (Az, HQ))
    lv = {SUMS(ZSL): s([zslf, tz], 'fsumrecl', '%s e. RR' % SUMS(ZSL)), SUMS(U12): s([u12f, rge(U12)[0]], 'fsumrecl', '%s e. RR' % SUMS(U12)),
          SUMS(U34): s([u34f, rge(U34)[0]], 'fsumrecl', '%s e. RR' % SUMS(U34)), Q8: q8r}
    for k in range(4):
        lv[SUMS(ZK[k])] = sk[k][0]
    W0_ = W0
    l80c = s([l80r], 'recnd', '%s e. CC' % L80)
    dv = s([numst(w, A0, '4', 'CC'), l80c, s([l25rp], 'rpcnd', '%s e. CC' % L25), s([l25rp], 'rpne0d', '%s =/= 0' % L25)], 'divassd', '%s = ( 4 x. %s )' % (W0_, Q8))
    lv[W0_] = s([s([numst(w, A0, '4', 'RR'), l80r], 'remulcld', '( 4 x. %s ) e. RR' % L80), l25rp], 'rerpdivcld', '%s e. RR' % W0_)
    fin = lin8(w, A0, [f1, f2, f3, dv] + [x[1] for x in sk], '%s <_ %s' % (SUMS(ZSL), W0_), lv)
    goal = FS['lchrzc']
    assert goal == '( %s -> ( %s e. Fin /\\ %s <_ %s ) )' % (A0, ZSL, SUMS(ZSL), W0_), goal
    w.qed([zslf, fin], 'jca', goal)
    return run8(w)


if __name__ == '__main__':
    gen_lchrzc()
