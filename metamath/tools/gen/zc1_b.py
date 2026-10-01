"""Sortie ZC1: the generic four-strip count on SQ ( 2 + i T , 13 / 8 ) (jensq13), C10's lchrzc for a generic F."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import num
from c8_n import sqparts, sqre_at, sqcc
from c8_o import numst
from c9_b import decode
import c9_h
patch(c9_h)
from c9_h import c0_facts
from c10_f import crfacts, clo
import lin
lin.FASTPATH = True

TS = ['( T - %s )' % R3932, '( T - %s )' % R1332, '( T + %s )' % R1332, '( T + %s )' % R3932]
ZK = [ZQ(t, 'F') for t in TS]
U12 = '( %s u. %s )' % (ZK[0], ZK[1])
U34 = '( %s u. %s )' % (ZK[2], ZK[3])
U4 = '( %s u. %s )' % (U12, U34)
HQ = '( F holord q )'
SUMS = lambda Z: 'sum_ q e. %s %s' % (Z, HQ)
RA, RB = '( ( 1 / 4 ) + ( _i x. ( T - 3 ) ) )', '( ( ; 1 5 / 4 ) + ( _i x. ( T + 3 ) ) )'
LBM = '( log ` ( B / M ) )'


def gen_jensq13():
    w = W('jensq13', 'Generic zero count on the square of half-side ` 13 / 8 ` about ` 2 + i T ` : for ` F ` holomorphic on the right half-plane, bounded by ` B ` on ` [ 1 / 4 , 15 / 4 ] x. [ T - 3 , T + 3 ] ` and with ` M <_ abs F ( 2 + i t ) ` for ` t e. [ T - 2 , T + 2 ] ` , the zeros are finitely many, of order in ` NN ` , with mass at most ` 4 log ( B / M ) / log ( 25 / 24 ) ` : four strips of height ` 13 / 16 ` ( ~ jenstrip , ~ fsumunle ; C10\'s ~ lchrzc for a generic ` F ` ).')
    A0 = JQH
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2, X3 = top_and(A0)
    x1 = s([], 'simp1', X1); x2 = s([], 'simp2', X2); x3 = s([], 'simp3', X3)
    hol = s([x1, w.inst('simpl')], 'syl', HOLF('F', HP0))
    tr = s([x1, w.inst('simpr')], 'syl', 'T e. RR')
    bre = s([x2, w.inst('simpl')], 'syl', 'B e. RR')
    fbx = s([x2, w.inst('simpr')], 'syl', top_and(X2)[1])
    mrp = s([x3, w.inst('simpl')], 'syl', 'M e. RR+')
    mall = s([x3, w.inst('simpr')], 'syl', top_and(X3)[1])
    c0, re0, im0 = c0_facts(w, A0, tr)
    m39 = numst(w, A0, R3932, 'RR'); m13 = numst(w, A0, R1332, 'RR')
    tks = [s([tr, m39], 'resubcld', '%s e. RR' % TS[0]), s([tr, m13], 'resubcld', '%s e. RR' % TS[1]),
           s([tr, m13], 'readdcld', '%s e. RR' % TS[2]), s([tr, m39], 'readdcld', '%s e. RR' % TS[3])]
    # the big rectangle
    t3a = s([tr, numst(w, A0, '3', 'RR')], 'resubcld', '( T - 3 ) e. RR')
    t3b = s([tr, numst(w, A0, '3', 'RR')], 'readdcld', '( T + 3 ) e. RR')
    rac, rreA, rimA = crfacts(w, A0, '( 1 / 4 )', '( T - 3 )', numst(w, A0, '( 1 / 4 )', 'RR'), t3a)
    rbc, rreB, rimB = crfacts(w, A0, '( ; 1 5 / 4 )', '( T + 3 )', numst(w, A0, '( ; 1 5 / 4 )', 'RR'), t3b)
    r74 = numst(w, A0, R74, 'RR')
    t2a = s([tr, numst(w, A0, '2', 'RR')], 'resubcld', '( T - 2 ) e. RR')
    t2b = s([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')
    js = []
    for k, tk in enumerate(TS):
        JK = tsub(S['jenstrip'], {'T': tk})
        ja, jc = ante_of(JK)
        Y1, Y2, Y3 = top_and(ja)
        ck = '( 2 + ( _i x. %s ) )' % tk
        cc_, re_k, im_k = crfacts(w, A0, '2', tk, numst(w, A0, '2', 'RR'), tks[k])
        SA, SB = SQA(ck, R74), SQB(ck, R74)
        sa, sb = sqcc(w, A0, cc_, r74, c=ck, r=R74)
        ps = sqparts(w, A0, sqre_at(w, A0, cc_, r74, c=ck, r=R74), c=ck, r=R74)
        lv = {'T': tr}
        for e, st in (('( Re ` %s )' % ck, cc_), ('( Im ` %s )' % ck, cc_), ('( Re ` %s )' % SA, sa), ('( Im ` %s )' % SA, sa), ('( Re ` %s )' % SB, sb), ('( Im ` %s )' % SB, sb),
                      ('( Re ` %s )' % RA, rac), ('( Im ` %s )' % RA, rac), ('( Re ` %s )' % RB, rbc), ('( Im ` %s )' % RB, rbc)):
            lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
        hy = [re_k, im_k, rreA, rimA, rreB, rimB] + ps
        CS = tsub(stmt('crectss2'), {'A': RA, 'B': RB, 'C': SA, 'E': SB})
        csa, csc = ante_of(CS)
        Z1, Z2, Z3 = top_and(csa)
        ii = [lin8(w, A0, hy, g, lv) for g in ('( Re ` %s ) <_ ( Re ` %s )' % (RA, SA), '( Re ` %s ) <_ ( Re ` %s )' % (SB, RB),
                                                  '( Im ` %s ) <_ ( Im ` %s )' % (RA, SA), '( Im ` %s ) <_ ( Im ` %s )' % (SB, RB))]
        sub = s([s([s([rac, rbc], 'jca', Z1), s([sa, sb], 'jca', Z2), s([s([ii[0], ii[1]], 'jca', top_and(Z3)[0]), s([ii[2], ii[3]], 'jca', top_and(Z3)[1])], 'jca', Z3)], '3jca', csa),
                   w.inst('crectss2')], 'syl', csc)
        fbk = s([sub, fbx, w.inst('ssralv')], 'sylc', top_and(Y2)[1])
        # t_k in [ T - 2 , T + 2 ]
        el = s([t2a, t2b, w.inst('elicc2')], 'syl2anc', '( %s e. ( ( T - 2 ) [,] ( T + 2 ) ) <-> ( %s e. RR /\\ ( T - 2 ) <_ %s /\\ %s <_ ( T + 2 ) ) )' % (tk, tk, tk, tk))
        lvt = {'T': tr}
        ink = s([s([tks[k], lin8(w, A0, [], '( T - 2 ) <_ %s' % tk, lvt), lin8(w, A0, [], '%s <_ ( T + 2 )' % tk, lvt)], '3jca',
                   '( %s e. RR /\\ ( T - 2 ) <_ %s /\\ %s <_ ( T + 2 ) )' % (tk, tk, tk)), el], 'mpbird', '%s e. ( ( T - 2 ) [,] ( T + 2 ) )' % tk)
        subt = w.s([w.s([w.s([w.s([], 'oveq2', '( t = %s -> ( _i x. t ) = ( _i x. %s ) )' % (tk, tk))], 'oveq2d', '( t = %s -> ( 2 + ( _i x. t ) ) = %s )' % (tk, ck))],
                        'fveq2d', '( t = %s -> ( F ` ( 2 + ( _i x. t ) ) ) = ( F ` %s ) )' % (tk, ck))], 'fveq2d',
                   '( t = %s -> ( abs ` ( F ` ( 2 + ( _i x. t ) ) ) ) = ( abs ` ( F ` %s ) ) )' % (tk, ck))
        subt2 = w.s([subt], 'breq2d', '( t = %s -> ( M <_ ( abs ` ( F ` ( 2 + ( _i x. t ) ) ) ) <-> M <_ ( abs ` ( F ` %s ) ) ) )' % (tk, ck))
        mk = w.s([subt2, mall, ink], 'rspcdva', '( %s -> M <_ ( abs ` ( F ` %s ) ) )' % (A0, ck))
        ante = s([s([hol, tks[k]], 'jca', Y1), s([bre, fbk], 'jca', Y2), s([mrp, mk], 'jca', Y3)], '3jca', ja)
        js.append(s([ante, w.inst('jenstrip')], 'syl', jc))
    parts = [top_and(ante_of(tsub(S['jenstrip'], {'T': t}))[1]) for t in TS]
    zf = [s([z, w.inst('simp1')], 'syl', p[0]) for z, p in zip(js, parts)]
    al = [s([z, w.inst('simp2')], 'syl', p[1]) for z, p in zip(js, parts)]
    iq = [s([z, w.inst('simp3')], 'syl', p[2]) for z, p in zip(js, parts)]
    # the cover: ZS13 C_ U4
    r138 = numst(w, A0, R138, 'RR')
    sa, sb = sqcc(w, A0, c0, r138, c=C0, r=R138)
    SA, SB = SQA(C0, R138), SQB(C0, R138)
    SQ13 = SQ(C0, R138)
    ZSL_ = ZS13
    ps = sqparts(w, A0, sqre_at(w, A0, c0, r138, c=C0, r=R138), c=C0, r=R138)
    qk = []
    for k, tk in enumerate(TS):
        ta = s([tks[k], m13], 'resubcld', '( %s - %s ) e. RR' % (tk, R1332))
        tb = s([tks[k], m13], 'readdcld', '( %s + %s ) e. RR' % (tk, R1332))
        qk.append((crfacts(w, A0, '( 3 / 8 )', '( %s - %s )' % (tk, R1332), numst(w, A0, '( 3 / 8 )', 'RR'), ta),
                   crfacts(w, A0, '( ; 2 9 / 8 )', '( %s + %s )' % (tk, R1332), numst(w, A0, '( ; 2 9 / 8 )', 'RR'), tb)))
    Aq = '( %s /\\ q e. %s )' % (A0, ZSL_)
    L = lambda st, a=Aq: lift(w, st, a)
    subr = w.s([w.s([], 'fveq2', '( r = q -> ( F ` r ) = ( F ` q ) )')], 'eqeq1d', '( r = q -> ( ( F ` r ) = 0 <-> ( F ` q ) = 0 ) )')
    el = w.s([subr], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( F ` q ) = 0 ) )' % (ZSL_, SQ13))
    qq = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, ZSL_)), el], 'sylib', '( %s -> ( q e. %s /\\ ( F ` q ) = 0 ) )' % (Aq, SQ13))
    qsq = w.s([qq, w.inst('simpl')], 'syl', '( %s -> q e. %s )' % (Aq, SQ13))
    lq0 = w.s([qq, w.inst('simpr')], 'syl', '( %s -> ( F ` q ) = 0 )' % Aq)
    d = decode(w, Aq, qsq, L(sa), L(sb), SA, SB, SQ13, U='q')
    qc = d[0]
    rq = w.s([qc], 'recld', '( %s -> ( Re ` q ) e. RR )' % Aq); iqr = w.s([qc], 'imcld', '( %s -> ( Im ` q ) e. RR )' % Aq)
    def memk(ante, k, cases):
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
    cov = s([w.s([qu], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, ZSL_, U4))], 'ssrdv', '%s C_ %s' % (ZSL_, U4))
    u12f = s([zf[0], zf[1]], 'unfid', '%s e. Fin' % U12); u34f = s([zf[2], zf[3]], 'unfid', '%s e. Fin' % U34)
    u4f = s([u12f, u34f], 'unfid', '%s e. Fin' % U4)
    zslf = s([u4f, cov], 'ssfid', '%s e. Fin' % ZSL_)
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
    f1 = fsu(ZSL_, U12, U34, u12f, u34f, cov)
    f2 = fsu(U12, ZK[0], ZK[1], zf[0], zf[1], s([], 'ssidd', '%s C_ %s' % (U12, U12)))
    f3 = fsu(U34, ZK[2], ZK[3], zf[2], zf[3], s([], 'ssidd', '%s C_ %s' % (U34, U34)))
    l25p = s([s([numst(w, A0, R2524, 'RR+'), w.inst('loggt0b')], 'syl', '( 0 < %s <-> 1 < %s )' % (L25, R2524)), lin8(w, A0, [], '1 < %s' % R2524, {})], 'mpbird', '0 < %s' % L25)
    l25rp = s([s([numst(w, A0, R2524, 'RR+')], 'relogcld', '%s e. RR' % L25), l25p], 'elrpd', '%s e. RR+' % L25)
    # log ( B / M ) is real: B > 0 from any strip (B >= abs F ( C_k ) >= M) -- take it from the first strip's bound
    # (0 <_ S_0 L25 <_ log ( B / M ) needs only B / M e. RR+); B e. RR+ : M <_ abs F ( C0 ) <_ B
    ck = C0
    c0h = s([s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C0)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C0, C0)),
             s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C0, HP0, C0, C0))], 'mpbird', '%s e. %s' % (C0, HP0))
    LC = '( F ` %s )' % C0; ALC = '( abs ` %s )' % LC
    lfc = s([s([s([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), c0h], 'ffvelcdmd', '%s e. CC' % LC)
    alr = s([lfc], 'abscld', '%s e. RR' % ALC)
    # C0 e. RCT
    lvc = {'T': tr, '( Re ` %s )' % RA: s([rac], 'recld', '( Re ` %s ) e. RR' % RA), '( Im ` %s )' % RA: s([rac], 'imcld', '( Im ` %s ) e. RR' % RA),
           '( Re ` %s )' % RB: s([rbc], 'recld', '( Re ` %s ) e. RR' % RB), '( Im ` %s )' % RB: s([rbc], 'imcld', '( Im ` %s ) e. RR' % RB),
           '( Re ` %s )' % C0: s([c0], 'recld', '( Re ` %s ) e. RR' % C0), '( Im ` %s )' % C0: s([c0], 'imcld', '( Im ` %s ) e. RR' % C0)}
    hc = [re0, im0, rreA, rimA, rreB, rimB]
    INS = INTG(RA, RB, C0)
    ins = s([c0, s([s([lin8(w, A0, hc, '( Re ` %s ) < ( Re ` %s )' % (RA, C0), lvc), lin8(w, A0, hc, '( Re ` %s ) < ( Re ` %s )' % (C0, RB), lvc)], 'jca',
                       '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (RA, C0, C0, RB)),
                     s([lin8(w, A0, hc, '( Im ` %s ) < ( Im ` %s )' % (RA, C0), lvc), lin8(w, A0, hc, '( Im ` %s ) < ( Im ` %s )' % (C0, RB), lvc)], 'jca',
                       '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (RA, C0, C0, RB))], 'jca', INS[len('( %s e. CC /\\ ' % C0):-2])], 'jca', INS)
    crc = w.s([s([rac, rbc], 'jca', '( %s e. CC /\\ %s e. CC )' % (RA, RB)), ins, w.inst('crectinp')], 'syl2anc', '( %s -> %s e. %s )' % (A0, C0, RCT('T')))
    subx = w.s([w.s([w.s([], 'fveq2', '( x = %s -> ( F ` x ) = %s )' % (C0, LC))], 'fveq2d', '( x = %s -> ( abs ` ( F ` x ) ) = %s )' % (C0, ALC))], 'breq1d',
               '( x = %s -> ( ( abs ` ( F ` x ) ) <_ B <-> %s <_ B ) )' % (C0, ALC))
    bge = w.s([subx, fbx, crc], 'rspcdva', '( %s -> %s <_ B )' % (A0, ALC))
    tT = s([s([s([tr], 'recnd', 'T e. CC')], 'subidd', '( T - T ) = 0')], 'eqcomd', '0 = ( T - T )') if False else None
    elT = s([t2a, t2b, w.inst('elicc2')], 'syl2anc', '( T e. ( ( T - 2 ) [,] ( T + 2 ) ) <-> ( T e. RR /\\ ( T - 2 ) <_ T /\\ T <_ ( T + 2 ) ) )')
    inT = s([s([tr, lin8(w, A0, [], '( T - 2 ) <_ T', {'T': tr}), lin8(w, A0, [], 'T <_ ( T + 2 )', {'T': tr})], '3jca', '( T e. RR /\\ ( T - 2 ) <_ T /\\ T <_ ( T + 2 ) )'), elT],
            'mpbird', 'T e. ( ( T - 2 ) [,] ( T + 2 ) )')
    subt = w.s([w.s([w.s([w.s([], 'oveq2', '( t = T -> ( _i x. t ) = ( _i x. T ) )')], 'oveq2d', '( t = T -> ( 2 + ( _i x. t ) ) = %s )' % C0)],
                    'fveq2d', '( t = T -> ( F ` ( 2 + ( _i x. t ) ) ) = %s )' % LC)], 'fveq2d', '( t = T -> ( abs ` ( F ` ( 2 + ( _i x. t ) ) ) ) = %s )' % ALC)
    m0 = w.s([w.s([subt], 'breq2d', '( t = T -> ( M <_ ( abs ` ( F ` ( 2 + ( _i x. t ) ) ) ) <-> M <_ %s ) )' % ALC), mall, inT], 'rspcdva', '( %s -> M <_ %s )' % (A0, ALC))
    mr = s([mrp], 'rpred', 'M e. RR')
    bpos = lin8(w, A0, [bge, m0, s([mrp], 'rpgt0d', '0 < M')], '0 < B', {ALC: alr, 'M': mr, 'B': bre})
    brp = s([bre, bpos], 'elrpd', 'B e. RR+')
    lbm = s([s([brp, mrp], 'rpdivcld', '( B / M ) e. RR+')], 'relogcld', '%s e. RR' % LBM)
    Q8 = '( %s / %s )' % (LBM, L25)
    q8r = s([lbm, l25rp], 'rerpdivcld', '%s e. RR' % Q8)
    sk = []
    for k in range(4):
        Sk = SUMS(ZK[k])
        skr = s([zf[k], rge(ZK[k])[0]], 'fsumrecl', '%s e. RR' % Sk)
        sk.append((skr, s([iq[k], s([skr, lbm, l25rp], 'lemuldivd', '( ( %s x. %s ) <_ %s <-> %s <_ %s )' % (Sk, L25, LBM, Sk, Q8))], 'mpbid', '%s <_ %s' % (Sk, Q8))))
    Az = '( %s /\\ q e. %s )' % (A0, ZSL_)
    qu4 = w.s([lift(w, cov, Az), w.s([], 'simpr', '( %s -> q e. %s )' % (Az, ZSL_))], 'sseldd', '( %s -> q e. %s )' % (Az, U4))
    nnz = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (Az, A0)), qu4], 'jca', '( %s -> ( %s /\\ q e. %s ) )' % (Az, A0, U4)), nnU(U4)], 'syl', '( %s -> %s e. NN )' % (Az, HQ))
    alz = s([nnz], 'ralrimiva', 'A. q e. %s %s e. NN' % (ZSL_, HQ))
    tz = w.s([nnz], 'nnred', '( %s -> %s e. RR )' % (Az, HQ))
    lv = {SUMS(ZSL_): s([zslf, tz], 'fsumrecl', '%s e. RR' % SUMS(ZSL_)), SUMS(U12): s([u12f, rge(U12)[0]], 'fsumrecl', '%s e. RR' % SUMS(U12)),
          SUMS(U34): s([u34f, rge(U34)[0]], 'fsumrecl', '%s e. RR' % SUMS(U34)), Q8: q8r}
    for k in range(4):
        lv[SUMS(ZK[k])] = sk[k][0]
    W_ = JW('B', 'M')
    dv = s([numst(w, A0, '4', 'CC'), s([lbm], 'recnd', '%s e. CC' % LBM), s([l25rp], 'rpcnd', '%s e. CC' % L25), s([l25rp], 'rpne0d', '%s =/= 0' % L25)], 'divassd', '%s = ( 4 x. %s )' % (W_, Q8))
    lv[W_] = s([s([numst(w, A0, '4', 'RR'), lbm], 'remulcld', '( 4 x. %s ) e. RR' % LBM), l25rp], 'rerpdivcld', '%s e. RR' % W_)
    fin = lin8(w, A0, [f1, f2, f3, dv] + [x[1] for x in sk], '%s <_ %s' % (SUMS(ZSL_), W_), lv)
    goal = S['jensq13']
    assert goal == '( %s -> ( %s e. Fin /\\ %s /\\ %s <_ %s ) )' % (A0, ZSL_, 'A. q e. %s %s e. NN' % (ZSL_, HQ), SUMS(ZSL_), W_), goal
    w.qed([zslf, alz, fin], '3jca', goal)
    return run8(w)


if __name__ == '__main__':
    gen_jensq13()
