"""Sortie ZD2: Theorem 8.3 (Lean card_paritySystem_le): zd2sig, zd2hb, zd2det, zd2dbl, zd2cpsh, zd2cps."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zd2_base import *
from zd2_gram import d_facts, row_re, crem_re, nyp_step, ri_fin, HSEL_BODY, G_
from zbvlib import mpv
lin.MAXDEG = 5
from fractions import Fraction
R160 = num.lit_text(Fraction(1, 160000))

XPD_ = XPD
P12 = '( %s ^c ( ; 1 2 / ; ; 5 0 0 ) )' % DSC
P13 = '( %s ^c ( ; 1 3 / ; ; 5 0 0 ) )' % DSC
P23 = '( %s ^c ( ; 2 3 / ; ; 5 0 0 ) )' % DSC
M23 = '( %s ^c -u ( ; 2 3 / ; ; 5 0 0 ) )' % DSC
P7 = '( %s ^c -u ( 7 / ; ; 1 0 0 ) )' % DSC
Q2 = '( %s ^ 2 )' % QRPD
L2 = '( %s ^ 2 )' % LD


def xbd_facts(w, A, c, f, sr):
    """XPD e. RR+, XBD e. RR+, XBD e. RR, 0 <_ XBD"""
    xp = c([f['drp'], numst(w, A, '( 6 / 5 )', 'RR')], 'rpcxpcld', '%s e. RR+' % XPD)
    e2 = c([numst(w, A, '2', 'RR'), c([numst(w, A, '2', 'RR'), sr], 'remulcld', '( 2 x. S ) e. RR')], 'resubcld', '( 2 - ( 2 x. S ) ) e. RR')
    xb = c([xp, e2], 'rpcxpcld', '%s e. RR+' % XBD)
    return xp, xb, c([xb], 'rpred', '%s e. RR' % XBD), c([xb], 'rpge0d', '0 <_ %s' % XBD)


def gen_sig():
    w = W('zd2sig', 'The diagonal of the parity system (Lean ` sigma_diag_le ` , ` hSig ` , ` hSig0 ` ): ` Sigma = sum_n c_n ^ 2 / b_n ` is real, nonnegative and at most ` C12 X ^ ( 2 - 2 S ) ` at ` D = N ( T + 2 ) ` ( ~ z5sigdiag , ~ z5cdt0 , ~ isumge0 ).')
    A0 = ante_of(S['zd2sig'])[0]
    c = Ctx(w, A0)
    nn_, sr, s99, s1, tr, t0, l200 = [c.g(x) for x in ('N e. NN', 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '; ; 2 0 0 <_ %s' % LD)]
    f = d_facts(w, A0, c, nn_, tr, t0)
    hzd = c([f['dr'], f['d1'], l200], '3jca', '( %s e. RR /\\ 1 < %s /\\ ; ; 2 0 0 <_ %s )' % (DSC, DSC, LD))
    ss = c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS)
    SD = tsub(stmt('z5sigdiag'), {'D': DSC, 'T': 'S', 'V': 'NN'})
    sda, sdc = ante_of(SD)
    sd = c([c([c([hzd, ss], 'jca', '( %s /\\ %s )' % (strip_ante(formula_of(w, hzd), A0), SS)), nn_], 'jca', sda), w.inst('z5sigdiag')], 'syl', sdc)
    F = '( k e. NN |-> %s )' % QTD('k')
    cvg = c([sd], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % F)
    bnd = c([sd], 'simprd', '%s <_ ( %s x. %s )' % (SIG, C12, XBD))
    An = '( %s /\\ n e. NN )' % A0
    cn = Ctx(w, An)
    fv, val = mpv(w, An, 'k', 'NN', QTD('k'), 'n', cn([], 'simpr', 'n e. NN'))
    assert val == QTD('n'), val
    hz2 = c([f['dr'], f['d1'], lin8(w, A0, [l200], '2 <_ %s' % LD, {LD: f['lr']})], '3jca', '( %s e. RR /\\ 1 < %s /\\ 2 <_ %s )' % (DSC, DSC, LD))
    CT = tsub(stmt('z5cdt0'), {'D': DSC, 'T': 'S', 'V': 'NN', 'K': 'n'})
    cta, ctc = ante_of(CT)
    ct = cn([cn([cn([lift(w, hz2, An), lift(w, nn_, An)], 'jca', top_and(cta)[0]), cn([lift(w, sr, An), cn([], 'simpr', 'n e. NN')], 'jca', '( S e. RR /\\ n e. NN )')], 'jca', cta), w.inst('z5cdt0')], 'syl', ctc)
    qr = cn([ct], 'simpld', '%s e. RR' % QTD('n')); q0 = cn([ct], 'simprd', '0 <_ %s' % QTD('n'))
    nz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = c([], '1zzd', '1 e. ZZ')
    sre = c([nz, one, fv, qr, cvg], 'isumrecl', '%s e. RR' % SIG)
    sg0 = c([nz, one, fv, qr, cvg, q0], 'isumge0', '0 <_ %s' % SIG)
    w.qed([c([sre, sg0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (SIG, SIG)), bnd], 'jca', S['zd2sig'])
    return go(w)


def gen_hb():
    w = W('zd2hb', 'The (T2) absorption of Theorem 8.3 (Lean ` card_paritySystem_le ` , ` hb ` ): ` C12 X ^ ( 2 - 2 S ) C11 L ^ 3 D ^ ( - 7 / 100 ) <_ V ^ 2 / 2 ` for ` V = ( 1 / 400 ) Q_R L ` , from ` X ^ ( 2 - 2 S ) <_ D ^ ( 12 / 500 ) ` ( ~ zdxrpow ), ` D ^ ( 13 / 500 ) <_ Q_R ^ 2 D ^ ( 23 / 500 ) ` ( ~ zdqrsq ) and (T2).')
    A0 = ante_of(S['zd2hb'])[0]
    c = Ctx(w, A0)
    nn_, sr, s99, s1, tr, t0, l200, t2 = [c.g(x) for x in ('N e. NN', 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '; ; 2 0 0 <_ %s' % LD, T2G)]
    f = d_facts(w, A0, c, nn_, tr, t0)
    k = closed_consts(w)
    xp, xbp, xbr, xb0 = xbd_facts(w, A0, c, f, sr)
    dd = c([f['dr'], f['d1']], 'jca', '( %s e. RR /\\ 1 < %s )' % (DSC, DSC))
    xr = c([c([dd, c([sr, s99], 'jca', '( S e. RR /\\ %s <_ S )' % F99)], 'jca', '( ( %s e. RR /\\ 1 < %s ) /\\ ( S e. RR /\\ %s <_ S ) )' % (DSC, DSC, F99)), w.inst('zdxrpow')], 'syl', '%s <_ %s' % (XBD, P12))
    qs = c([c([nn_, dd], 'jca', '( N e. NN /\\ ( %s e. RR /\\ 1 < %s ) )' % (DSC, DSC)), w.inst('zdqrsq')], 'syl', '%s <_ ( %s x. %s )' % (P13, Q2, P23))
    dcc = c([f['dr']], 'recnd', '%s e. CC' % DSC); dn0 = c([f['drp']], 'rpne0d', '%s =/= 0' % DSC)
    lit = lambda t: numst(w, A0, t, 'RR')
    def cx(e):
        return c([f['drp'], e], 'rpcxpcld', '( %s ^c %s ) e. RR+' % (DSC, strip_ante(formula_of(w, e), A0)[:-len(' e. RR')]))
    e7 = c([lit('( 7 / ; ; 1 0 0 )')], 'renegcld', '-u ( 7 / ; ; 1 0 0 ) e. RR')
    F12 = '( ; 1 2 / ; ; 5 0 0 )'
    e12 = c.a1(w.s([num.re_nat(w, 12), num.re_nat(w, 500), num.ne0_nat(w, 500)], 'redivcli', '%s e. RR' % F12), '%s e. RR' % F12); e23 = lit('( ; 2 3 / ; ; 5 0 0 )'); m23e = c([e23], 'renegcld', '-u ( ; 2 3 / ; ; 5 0 0 ) e. RR')
    p7 = cx(e7); p12 = cx(e12); p23 = cx(e23); m23 = cx(m23e)
    # P7 x. P12 = M23
    a1 = c([dcc, dn0, c([e7], 'recnd', '-u ( 7 / ; ; 1 0 0 ) e. CC'), c([e12], 'recnd', '( ; 1 2 / ; ; 5 0 0 ) e. CC')], 'cxpaddd', '( %s ^c ( -u ( 7 / ; ; 1 0 0 ) + ( ; 1 2 / ; ; 5 0 0 ) ) ) = ( %s x. %s )' % (DSC, P7, P12))
    red = c.a1(num._reduce_frac(w, 12, 500), '%s = ( 3 / ; ; 1 2 5 )' % F12)
    a2a = lin.lineq(w, A0, '( -u ( 7 / ; ; 1 0 0 ) + ( 3 / ; ; 1 2 5 ) )', '-u ( ; 2 3 / ; ; 5 0 0 )')
    a2 = c([c([red], 'oveq2d', '( -u ( 7 / ; ; 1 0 0 ) + %s ) = ( -u ( 7 / ; ; 1 0 0 ) + ( 3 / ; ; 1 2 5 ) )' % F12), a2a], 'eqtrd', '( -u ( 7 / ; ; 1 0 0 ) + %s ) = -u ( ; 2 3 / ; ; 5 0 0 )' % F12)
    pm = c([c([a2], 'oveq2d', '( %s ^c ( -u ( 7 / ; ; 1 0 0 ) + ( ; 1 2 / ; ; 5 0 0 ) ) ) = %s' % (DSC, M23)), a1], 'eqtr3d', '%s = ( %s x. %s )' % (M23, P7, P12))
    # P23 x. M23 = 1
    b1 = c([dcc, dn0, c([e23], 'recnd', '( ; 2 3 / ; ; 5 0 0 ) e. CC'), c([m23e], 'recnd', '-u ( ; 2 3 / ; ; 5 0 0 ) e. CC')], 'cxpaddd', '( %s ^c ( ( ; 2 3 / ; ; 5 0 0 ) + -u ( ; 2 3 / ; ; 5 0 0 ) ) ) = ( %s x. %s )' % (DSC, P23, M23))
    b2 = lin.lineq(w, A0, '( ( ; 2 3 / ; ; 5 0 0 ) + -u ( ; 2 3 / ; ; 5 0 0 ) )', '0')
    b3 = c([c([b2], 'oveq2d', '( %s ^c ( ( ; 2 3 / ; ; 5 0 0 ) + -u ( ; 2 3 / ; ; 5 0 0 ) ) ) = ( %s ^c 0 )' % (DSC, DSC)), c([dcc], 'cxp0d', '( %s ^c 0 ) = 1' % DSC)], 'eqtrd', '( %s ^c ( ( ; 2 3 / ; ; 5 0 0 ) + -u ( ; 2 3 / ; ; 5 0 0 ) ) ) = 1' % DSC)
    tm1 = c([b1, b3], 'eqtr3d', '( %s x. %s ) = 1' % (P23, M23))
    # atoms
    A_ = C11; ar = c.a1(k[C11][0], '%s e. RR' % A_); a0 = c.a1(k[C11][1], '0 <_ %s' % A_)
    lr, lp = f['lr'], f['lp']
    l2r = c([lr], 'resqcld', '%s e. RR' % L2); l20 = c([lr], 'sqge0d', '0 <_ %s' % L2)
    q2r = c([f['qr']], 'resqcld', '%s e. RR' % Q2)
    p7r, p12r, p23r, m23r = [c([x], 'rpred', '%s e. RR' % y) for x, y in ((p7, P7), (p12, P12), (p23, P23), (m23, M23))]
    L3 = '( %s ^ 3 )' % LD
    l3e = c([c([w.s([], 'df-3', '3 = ( 2 + 1 )')], 'a1i', '3 = ( 2 + 1 )')], 'oveq2d', '%s = ( %s ^ ( 2 + 1 ) )' % (L3, LD))
    l3e2 = c([l3e, c([c([lr], 'recnd', '%s e. CC' % LD), c.a1(w.s([], '2nn0', '2 e. NN0'), '2 e. NN0'), w.inst('expp1')], 'syl2anc', '( %s ^ ( 2 + 1 ) ) = ( %s x. %s )' % (LD, L2, LD))], 'eqtrd', '%s = ( %s x. %s )' % (L3, L2, LD))
    L3X = '( %s x. %s )' % (L2, LD)
    CREM2 = '( ( %s x. %s ) x. %s )' % (A_, L3X, P7)
    creme = c([c([c([l3e2], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (A_, L3, A_, L3X))], 'oveq1d', '%s = %s' % (CREM, CREM2))], 'oveq2d', '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (C12, XBD, CREM, C12, XBD, CREM2))
    lv = {XBD: xbr, A_: ar, L2: l2r, LD: lr, P7: p7r, M23: m23r, Q2: q2r, P12: p12r, P23: p23r}
    # h1: ( C12 X ) CREM2 = ( ( C12 A ) L3X ) ( P7 X ) <_ ( ( C12 A ) L3X ) M23
    e1 = lin.lineq(w, A0, '( ( %s x. %s ) x. %s )' % (C12, XBD, CREM2), '( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) )' % (C12, A_, L3X, P7, XBD), leaves=lv, products=True, atoms=list(lv))
    i1 = c([xbr, p12r, p7r, c([p7], 'rpge0d', '0 <_ %s' % P7), xr], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (P7, XBD, P7, P12))
    i2 = c([i1, pm], 'breqtrrd', '( %s x. %s ) <_ %s' % (P7, XBD, M23))
    CA = '( ( %s x. %s ) x. %s )' % (C12, A_, L3X)
    car = c([c([numst(w, A0, C12, 'RR'), ar], 'remulcld', '( %s x. %s ) e. RR' % (C12, A_)), c([l2r, lr], 'remulcld', '%s e. RR' % L3X)], 'remulcld', '%s e. RR' % CA)
    ca0 = c([c([numst(w, A0, C12, 'RR'), ar], 'remulcld', '( %s x. %s ) e. RR' % (C12, A_)), c([l2r, lr], 'remulcld', '%s e. RR' % L3X), c([numst(w, A0, C12, 'RR'), ar, numst(w, A0, C12, 'ge0'), a0], 'mulge0d', '0 <_ ( %s x. %s )' % (C12, A_)),
              c([l2r, lr, l20, lin8(w, A0, [lp], '0 <_ %s' % LD, {LD: lr})], 'mulge0d', '0 <_ %s' % L3X)], 'mulge0d', '0 <_ %s' % CA)
    h1 = c([c([p7r, xbr], 'remulcld', '( %s x. %s ) e. RR' % (P7, XBD)), m23r, car, ca0, i2], 'lemul2ad', '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (CA, P7, XBD, CA, M23))
    h1b = c([c([creme, e1], 'eqtrd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (C12, XBD, CREM, CA, P7, XBD)), h1], 'eqbrtrd', '( ( %s x. %s ) x. %s ) <_ ( %s x. %s )' % (C12, XBD, CREM, CA, M23))
    # h2: ( B2C L ) M23 <_ Q2
    BL = '( %s x. %s )' % (B2C, LD)
    blr = c([c.a1(k[B2C][0], '%s e. RR' % B2C), lr], 'remulcld', '%s e. RR' % BL)
    qt = c([q2r, p23r], 'remulcld', '( %s x. %s ) e. RR' % (Q2, P23))
    j1 = c([blr, c([p13 := cx(lit('( ; 1 3 / ; ; 5 0 0 )'))], 'rpred', '%s e. RR' % P13), qt, t2, qs], 'letrd', '%s <_ ( %s x. %s )' % (BL, Q2, P23))
    j2 = c([blr, qt, m23r, c([m23], 'rpge0d', '0 <_ %s' % M23), j1], 'lemul1ad', '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (BL, M23, Q2, P23, M23))
    j3 = c([c([c([q2r], 'recnd', '%s e. CC' % Q2), c([p23r], 'recnd', '%s e. CC' % P23), c([m23r], 'recnd', '%s e. CC' % M23)], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (Q2, P23, M23, Q2, P23, M23)),
            c([c([tm1], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. 1 )' % (Q2, P23, M23, Q2)), c([c([q2r], 'recnd', '%s e. CC' % Q2)], 'mulridd', '( %s x. 1 ) = %s' % (Q2, Q2))], 'eqtrd', '( %s x. ( %s x. %s ) ) = %s' % (Q2, P23, M23, Q2))], 'eqtrd',
           '( ( %s x. %s ) x. %s ) = %s' % (Q2, P23, M23, Q2))
    h2 = c([j2, j3], 'breqtrd', '( %s x. %s ) <_ %s' % (BL, M23, Q2))
    blm = c([blr, m23r], 'remulcld', '( %s x. %s ) e. RR' % (BL, M23))
    h2b = c([blm, q2r, l2r, l20, h2], 'lemul1ad', '( ( %s x. %s ) x. %s ) <_ ( %s x. %s )' % (BL, M23, L2, Q2, L2))
    # h3: 320000 ( CA M23 ) = ( ( BL M23 ) L2 )
    h3 = lin.lineq(w, A0, '( %s x. ( %s x. %s ) )' % (N320000, CA, M23), '( ( %s x. %s ) x. %s )' % (BL, M23, L2), leaves=lv, products=True, atoms=list(lv))
    # V ^ 2 = ( ( 1 / 160000 ) Q2 ) L2
    V1 = '( ( 1 / %s ) x. %s )' % (N400, QRPD)
    qc = c([f['qr']], 'recnd', '%s e. CC' % QRPD); lc = c([lr], 'recnd', '%s e. CC' % LD)
    v1c = c([numst(w, A0, '( 1 / %s )' % N400, 'CC'), qc], 'mulcld', '%s e. CC' % V1)
    v2 = c([v1c, lc], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. %s )' % (VDET, V1, L2))
    v3 = c([numst(w, A0, '( 1 / %s )' % N400, 'CC'), qc], 'sqmuld', '( %s ^ 2 ) = ( ( ( 1 / %s ) ^ 2 ) x. %s )' % (V1, N400, Q2))
    sq = c([numst(w, A0, '( 1 / %s )' % N400, 'CC')], 'sqvald', '( ( 1 / %s ) ^ 2 ) = ( ( 1 / %s ) x. ( 1 / %s ) )' % (N400, N400, N400))
    sq2 = c([sq, c.a1(num.mul_lits(w, '( 1 / %s )' % N400, '( 1 / %s )' % N400), '( ( 1 / %s ) x. ( 1 / %s ) ) = %s' % (N400, N400, R160))], 'eqtrd', '( ( 1 / %s ) ^ 2 ) = %s' % (N400, R160))
    v4 = c([v2, c([c([v3, c([sq2], 'oveq1d', '( ( ( 1 / %s ) ^ 2 ) x. %s ) = ( %s x. %s )' % (N400, Q2, R160, Q2))], 'eqtrd', '( %s ^ 2 ) = ( %s x. %s )' % (V1, R160, Q2))], 'oveq1d',
                    '( ( %s ^ 2 ) x. %s ) = ( ( %s x. %s ) x. %s )' % (V1, L2, R160, Q2, L2))], 'eqtrd', '( %s ^ 2 ) = ( ( %s x. %s ) x. %s )' % (VDET, R160, Q2, L2))
    v5 = c([v4], 'oveq1d', '( ( %s ^ 2 ) / 2 ) = ( ( ( %s x. %s ) x. %s ) / 2 )' % (VDET, R160, Q2, L2))
    LHS = '( ( %s x. %s ) x. %s )' % (C12, XBD, CREM)
    cremr, _ = crem_re(w, A0, c, f, k)
    lhr = c([c([numst(w, A0, C12, 'RR'), xbr], 'remulcld', '( %s x. %s ) e. RR' % (C12, XBD)), cremr], 'remulcld', '%s e. RR' % LHS)
    lv2 = dict(lv); lv2[LHS] = lhr; lv2[CA] = car
    fin = lin.linarith(w, A0, [h1b, h3, h2b], '%s <_ ( ( ( %s x. %s ) x. %s ) / 2 )' % (LHS, R160, Q2, L2), leaves=lv2, products=True, atoms=list(lv2))
    w.qed([fin, v5], 'breqtrrd', S['zd2hb'])
    return go(w)


def gen_det():
    w = W('zd2det', 'The detection at a representative (Lean ` card_paritySystem_le ` , ` hdet ` , with ` gramArg ` typing): the selected zero ` H J ` of an index ` J ` is complex with ` S <_ Re ` , and ` ( 1 / 400 ) Q_R L <_ abs F_det ( chi_J , H J ) ` ( ~ zrdetg , ~ z6fdvcl for the closure).')
    A0 = ante_of(S['zd2det'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0, l200, t1g, hg, pr, hsel, jin = [c.g(x) for x in ('N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '; ; 2 0 0 <_ %s' % LD, T1G, HGOOD, 'P e. RR', HSEL, 'J e. %s' % RI('P'))]
    f = d_facts(w, A0, c, nn_, tr, t0)
    hJ, _ = ral_at(w, A0, hsel, 'q', 'J', HSEL_BODY, jin)
    fa = cell_facts(w, A0, hJ, '( H ` J )', '( 1st ` J )', '( 2nd ` J )', sr, tr)
    _, _, _, _, j1, _ = ri_facts(w, A0, jin, 'J')
    xj = c([ys, j1], 'sseldd', '( 1st ` J ) e. %s' % DB_N)
    DG = tsub(stmt('zrdetg'), {'Q': 'J', 'A': '( H ` J )'})
    dga, dgc = ante_of(DG)
    Q = top_and(dga)
    dg = c([c([c([c([nn_, ys], 'jca', '( N e. NN /\\ Y C_ %s )' % DB_N), c([c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS), c([tr, t0], 'jca', TT)], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', Q[0]),
                c([c([l200, t1g], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (LD, T1G)), hg], 'jca', Q[1]), c([pr, jin, hJ], '3jca', Q[2])], '3jca', dga), w.inst('zrdetg')], 'syl', dgc)
    assert dgc == '%s <_ ( abs ` %s )' % (VDET, FDJ('J')), dgc
    # closure of FDet at ( H J )
    LI = tsub(stmt('zl1lif'), {'X': '( 1st ` J )'})
    lia, lic = ante_of(LI)
    li = c([c([nn_, xj], 'jca', lia), w.inst('zl1lif')], 'syl', lic)
    CH = CHJ('J')
    l1 = c([li], 'simpld', top_and(lic)[0])
    chf = c([c([l1], 'simpld', top_and(top_and(lic)[0])[0])], 'simp1d', '%s : NN --> CC' % CH)
    chb = c([l1], 'simprd', 'A. j e. NN ( abs ` ( %s ` j ) ) <_ 1' % CH)
    hzd = c([f['dr'], f['d1'], l200], '3jca', '( %s e. RR /\\ 1 < %s /\\ ; ; 2 0 0 <_ %s )' % (DSC, DSC, LD))
    re0 = c([numst(w, A0, '0', 'RR'), sr, fa['rer'], lin8(w, A0, [s99], '0 <_ S', {'S': sr}), fa['re1']], 'letrd', '0 <_ ( Re ` ( H ` J ) )')
    FC = tsub(stmt('z6fdvcl'), {'D': DSC, 'C': CH, 'S': '( H ` J )'})
    fca, fcc = ante_of(FC)
    fc = c([c([c([c([hzd, nn_], 'jca', top_and(top_and(fca)[0])[0]), c([chf, chb], 'jca', top_and(top_and(fca)[0])[1])], 'jca', top_and(fca)[0]), c([fa['cc'], re0], 'jca', top_and(fca)[1])], 'jca', fca), w.inst('z6fdvcl')], 'syl', fcc)
    assert fcc == '%s e. CC' % FDJ('J'), fcc
    w.qed([c([fa['cc'], fa['re1']], 'jca', '( ( H ` J ) e. CC /\\ S <_ ( Re ` ( H ` J ) ) )'), c([fc, dg], 'jca', '( %s e. CC /\\ %s )' % (FDJ('J'), dgc))], 'jca', S['zd2det'])
    return go(w)


def gen_dbl():
    w = W('zd2dbl', 'The Gram double sum of a parity system (Lean ` card_paritySystem_le ` , ` hG ` ): ` sum_j sum_k abs B ( chi_j chi_k ^ -1 , s_jk ) <_ J ( row + J crem ) ` ( ~ zd2gram row by row).')
    A0 = ante_of(S['zd2dbl'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0, l2, kr, mer, pr, hsel = [c.g(x) for x in (
        'N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '2 <_ %s' % LD, 'K e. RR',
        '%s <_ ( K x. ( log ` %s ) )' % (MERTD, RPD), 'P e. RR', HSEL)]
    f = d_facts(w, A0, c, nn_, tr, t0)
    k = closed_consts(w)
    rif, yf = ri_fin(w, A0, c, nn_, ys)
    nyp = nyp_step(w, A0, c, nn_, ys, sr, s99, s1, tr, t0, pr, hsel)
    RIP = RI('P')
    cremr, crem0 = crem_re(w, A0, c, f, k)
    row, c9 = row_re(w, A0, c, kr, f)
    RHS = '( %s + ( ( # ` %s ) x. %s ) )' % (ROW, RIP, CREM)
    hr = c([c([c([rif, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RIP)], 'nn0red', '( # ` %s ) e. RR' % RIP), cremr], 'remulcld', '( ( # ` %s ) x. %s ) e. RR' % (RIP, CREM))
    rhsr = c([row, hr], 'readdcld', '%s e. RR' % RHS)
    Aj = '( %s /\\ j e. %s )' % (A0, RIP)
    cj = Ctx(w, Aj)
    jin = cj([], 'simpr', 'j e. %s' % RIP)
    GRM = tsub(S['zd2gram'], {'J': 'j'})
    gra, grc = ante_of(GRM)
    gr = cj([cj([cj([], 'simpl', A0), jin], 'jca', gra), w.inst('zd2gram')], 'syl', grc)
    # the inner sum is real
    Ajk = '( %s /\\ k e. %s )' % (Aj, RIP)
    ck = Ctx(w, Ajk)
    kin = ck([], 'simpr', 'k e. %s' % RIP)
    SJ, XJ = SJK('j', 'k'), XJK('j', 'k')
    GA = tsub(S['zd2garg'], {'A': 'j', 'B': 'k'})
    gaa, gac = ante_of(GA)
    ga = ck([ck([lift(w, nyp, Ajk), ck([lift(w, jin, Ajk), kin], 'jca', '( j e. %s /\\ k e. %s )' % (RIP, RIP))], 'jca', gaa), w.inst('zd2garg')], 'syl', gac)
    p1 = ck([ga], 'simpld', top_and(gac)[0]); p23 = ck([ga], 'simprd', top_and(gac)[1])
    xj = ck([p1], 'simpld', '%s e. %s' % (XJ, DB_N))
    p2 = ck([p23], 'simpld', top_and(top_and(gac)[1])[0])
    sjc = ck([p2], 'simpld', '%s e. CC' % SJ); reb = ck([p2], 'simprd', '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (SJ, SJ))
    hz2 = ck([lift(w, f['dr'], Ajk), lift(w, f['d1'], Ajk), lift(w, l2, Ajk)], '3jca', '( %s e. RR /\\ 1 < %s /\\ 2 <_ %s )' % (DSC, DSC, LD))
    BGC = tsub(stmt('gf2bgc'), {'D': DSC, 'X': XJ, 'S': SJ})
    bga, bgc_ = ante_of(BGC)
    bgc = ck([ck([ck([hz2, lift(w, nn_, Ajk)], 'jca', top_and(bga)[0]), ck([xj, ck([sjc, ck([reb], 'simpld', '0 <_ ( Re ` %s )' % SJ)], 'jca', '( %s e. CC /\\ 0 <_ ( Re ` %s ) )' % (SJ, SJ))], 'jca', top_and(bga)[1])], 'jca', bga), w.inst('gf2bgc')], 'syl', bgc_)
    BG = BGXD(XJ, SJ)
    absbg = ck([bgc], 'abscld', '( abs ` %s ) e. RR' % BG)
    INN = 'sum_ k e. %s ( abs ` %s )' % (RIP, BG)
    innr = cj([lift(w, rif, Aj), absbg], 'fsumrecl', '%s e. RR' % INN)
    le = c([rif, innr, lift(w, rhsr, Aj), gr], 'fsumle', '%s <_ sum_ j e. %s %s' % (DBL, RIP, RHS))
    cst = c([rif, c([rhsr], 'recnd', '%s e. CC' % RHS), w.inst('fsumconst')], 'syl2anc', 'sum_ j e. %s %s = ( ( # ` %s ) x. %s )' % (RIP, RHS, RIP, RHS))
    w.qed([le, cst], 'breqtrd', S['zd2dbl'])
    return go(w)




def vdet_sq(w, A, c, f):
    """( A -> ( VDET ^ 2 ) = ( ( ( 1 / 160000 ) x. Q2 ) x. L2 ) )"""
    V1 = '( ( 1 / %s ) x. %s )' % (N400, QRPD)
    qc = c([f['qr']], 'recnd', '%s e. CC' % QRPD); lc = c([f['lr']], 'recnd', '%s e. CC' % LD)
    r4 = numst(w, A, '( 1 / %s )' % N400, 'CC')
    v1c = c([r4, qc], 'mulcld', '%s e. CC' % V1)
    v2 = c([v1c, lc], 'sqmuld', '( %s ^ 2 ) = ( ( %s ^ 2 ) x. %s )' % (VDET, V1, L2))
    v3 = c([r4, qc], 'sqmuld', '( %s ^ 2 ) = ( ( ( 1 / %s ) ^ 2 ) x. %s )' % (V1, N400, Q2))
    sq = c([r4], 'sqvald', '( ( 1 / %s ) ^ 2 ) = ( ( 1 / %s ) x. ( 1 / %s ) )' % (N400, N400, N400))
    sq2 = c([sq, c.a1(num.mul_lits(w, '( 1 / %s )' % N400, '( 1 / %s )' % N400), '( ( 1 / %s ) x. ( 1 / %s ) ) = %s' % (N400, N400, R160))], 'eqtrd', '( ( 1 / %s ) ^ 2 ) = %s' % (N400, R160))
    return c([v2, c([c([v3, c([sq2], 'oveq1d', '( ( ( 1 / %s ) ^ 2 ) x. %s ) = ( %s x. %s )' % (N400, Q2, R160, Q2))], 'eqtrd', '( %s ^ 2 ) = ( %s x. %s )' % (V1, R160, Q2))], 'oveq1d',
                   '( ( %s ^ 2 ) x. %s ) = ( ( %s x. %s ) x. %s )' % (V1, L2, R160, Q2, L2))], 'eqtrd', '( %s ^ 2 ) = ( ( %s x. %s ) x. %s )' % (VDET, R160, Q2, L2))


def gen_cpsh():
    w = W('zd2cpsh', 'Theorem 8.3 with a selector (Lean ` card_paritySystem_le ` ): a parity system with selected zeros ` H ` has ` J <_ CJ X ^ ( 2 - 2 S ) ` , ` CJ = 3200 C12 C9 ` , under ` 200 <_ L ` , (T1), (T2), the ` chi_0 ` height clause and Mertens ( ~ gf2hal , ~ zd2det , ~ zd2sig , ~ zd2dbl , ~ zd2hb , ~ zdpar ).')
    A0 = ante_of(S['zd2cpsh'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0, l200, t1g, t2g, hg, kr, k0, mer, pr, hsel = [c.g(x) for x in (
        'N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '; ; 2 0 0 <_ %s' % LD, T1G, T2G, HGOOD,
        'K e. RR', '0 <_ K', '%s <_ ( K x. ( log ` %s ) )' % (MERTD, RPD), 'P e. RR', HSEL)]
    f = d_facts(w, A0, c, nn_, tr, t0)
    k = closed_consts(w)
    rif, yf = ri_fin(w, A0, c, nn_, ys)
    xp, xbp, xbr, xb0 = xbd_facts(w, A0, c, f, sr)
    row, c9 = row_re(w, A0, c, kr, f)
    cremr, crem0 = crem_re(w, A0, c, f, k)
    RIP = RI('P')
    ss = c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS)
    tt = c([tr, t0], 'jca', TT)
    nst = c([nn_, c([ss, tt], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', '( N e. NN /\\ ( %s /\\ %s ) )' % (SS, TT))
    # the diagonal, (T2) absorption, the double sum
    sg = c([c([nst, l200], 'jca', ante_of(S['zd2sig'])[0]), w.inst('zd2sig')], 'syl', ante_of(S['zd2sig'])[1])
    sigr = c([c([sg], 'simpld', '( %s e. RR /\\ 0 <_ %s )' % (SIG, SIG))], 'simpld', '%s e. RR' % SIG)
    sig0 = c([c([sg], 'simpld', '( %s e. RR /\\ 0 <_ %s )' % (SIG, SIG))], 'simprd', '0 <_ %s' % SIG)
    sigle = c([sg], 'simprd', '%s <_ ( %s x. %s )' % (SIG, C12, XBD))
    hb = c([c([nst, c([l200, t2g], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (LD, T2G))], 'jca', ante_of(S['zd2hb'])[0]), w.inst('zd2hb')], 'syl', ante_of(S['zd2hb'])[1])
    nys = c([c([nn_, ys], 'jca', '( N e. NN /\\ Y C_ %s )' % DB_N), c([ss, tt], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', NYS)
    l2 = lin8(w, A0, [l200], '2 <_ %s' % LD, {LD: f['lr']})
    dbl = c([c([nys, c([c([l2, c([kr, mer], 'jca', MERTH)], 'jca', '( 2 <_ %s /\\ %s )' % (LD, MERTH)), c([pr, hsel], 'jca', '( P e. RR /\\ %s )' % HSEL)], 'jca', '( ( 2 <_ %s /\\ %s ) /\\ ( P e. RR /\\ %s ) )' % (LD, MERTH, HSEL))], 'jca', ante_of(S['zd2dbl'])[0]), w.inst('zd2dbl')], 'syl', ante_of(S['zd2dbl'])[1])
    # detection per index
    Aj = '( %s /\\ j e. %s )' % (A0, RIP)
    cj = Ctx(w, Aj)
    jin = cj([], 'simpr', 'j e. %s' % RIP)
    DT = tsub(S['zd2det'], {'J': 'j'})
    dta, dtc = ante_of(DT)
    dt = cj([cj([cj([lift(w, nys, Aj), cj([cj([lift(w, l200, Aj), lift(w, t1g, Aj)], 'jca', '( ; ; 2 0 0 <_ %s /\\ %s )' % (LD, T1G)), lift(w, hg, Aj)], 'jca', '( ( ; ; 2 0 0 <_ %s /\\ %s ) /\\ %s )' % (LD, T1G, HGOOD))], 'jca', top_and(dta)[0]),
                cj([cj([lift(w, pr, Aj), lift(w, hsel, Aj)], 'jca', '( P e. RR /\\ %s )' % HSEL), jin], 'jca', top_and(dta)[1])], 'jca', dta), w.inst('zd2det')], 'syl', dtc)
    hjc = cj([cj([dt], 'simpld', top_and(dtc)[0])], 'simpld', '( H ` j ) e. CC'); hjre = cj([cj([dt], 'simpld', top_and(dtc)[0])], 'simprd', 'S <_ ( Re ` ( H ` j ) )')
    fdc = cj([cj([dt], 'simprd', top_and(dtc)[1])], 'simpld', '%s e. CC' % FDJ('j')); fdle = cj([cj([dt], 'simprd', top_and(dtc)[1])], 'simprd', '%s <_ ( abs ` %s )' % (VDET, FDJ('j')))
    _, _, _, _, j1, _ = ri_facts(w, Aj, jin, 'j')
    xj = cj([lift(w, ys, Aj), j1], 'sseldd', '( 1st ` j ) e. %s' % DB_N)
    # Halasz duality
    hzd = c([f['dr'], f['d1'], l200], '3jca', '( %s e. RR /\\ 1 < %s /\\ ; ; 2 0 0 <_ %s )' % (DSC, DSC, LD))
    HAL = tsub(stmt('gf2hal'), {'D': DSC, 'T': 'S', 'J': RIP, 'Q': '1st', 'P': 'H'})
    hla, hlc = ante_of(HAL)
    alj = c([cj([xj, cj([hjc, hjre], 'jca', '( ( H ` j ) e. CC /\\ S <_ ( Re ` ( H ` j ) ) )')], 'jca', '( ( 1st ` j ) e. %s /\\ ( ( H ` j ) e. CC /\\ S <_ ( Re ` ( H ` j ) ) ) )' % DB_N)], 'ralrimiva',
              'A. j e. %s ( ( 1st ` j ) e. %s /\\ ( ( H ` j ) e. CC /\\ S <_ ( Re ` ( H ` j ) ) ) )' % (RIP, DB_N))
    hal = c([c([c([c([hzd, ss], 'jca', '( %s /\\ %s )' % (strip_ante(formula_of(w, hzd), A0), SS)), nn_], 'jca', top_and(hla)[0]), c([rif, alj], 'jca', top_and(hla)[1])], 'jca', hla), w.inst('gf2hal')], 'syl', hlc)
    SFD = 'sum_ j e. %s ( abs ` %s )' % (RIP, FDJ('j'))
    assert hlc == '( %s ^ 2 ) <_ ( %s x. %s )' % (SFD, SIG, DBL), hlc
    # J V <_ SFD
    JJ_ = '( # ` %s )' % RIP
    jr = c([c([rif, w.inst('hashcl')], 'syl', '%s e. NN0' % JJ_)], 'nn0red', '%s e. RR' % JJ_)
    j0 = c([c([rif, w.inst('hashcl')], 'syl', '%s e. NN0' % JJ_)], 'nn0ge0d', '0 <_ %s' % JJ_)
    vr = c([c([numst(w, A0, '( 1 / %s )' % N400, 'RR'), f['qr']], 'remulcld', '( ( 1 / %s ) x. %s ) e. RR' % (N400, QRPD)), f['lr']], 'remulcld', '%s e. RR' % VDET)
    two_rp = c([c([f['drp'], l200], 'jca', '( %s e. RR+ /\\ ; ; 2 0 0 <_ %s )' % (DSC, LD)), w.inst('zd2rpar')], 'syl', '2 <_ %s' % RPD)
    one_rp = lin8(w, A0, [two_rp], '1 <_ %s' % RPD, {RPD: f['rprr']})
    qlb = c([c([nn_, c([f['rprr'], one_rp], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (RPD, RPD))], 'jca', '( N e. NN /\\ ( %s e. RR /\\ 1 <_ %s ) )' % (RPD, RPD)), w.inst('zdinvqr')], 'syl', '( 1 / %s ) <_ %s' % (RPD, QRPD))
    rinv = c([c([f['rpr']], 'rpreccld', '( 1 / %s ) e. RR+' % RPD)], 'rpgt0d', '0 < ( 1 / %s )' % RPD)
    q0 = lin8(w, A0, [qlb, rinv], '0 < %s' % QRPD, {QRPD: f['qr'], '( 1 / %s )' % RPD: c([c([f['rpr']], 'rpreccld', '( 1 / %s ) e. RR+' % RPD)], 'rpred', '( 1 / %s ) e. RR' % RPD)})
    v0 = c([c([numst(w, A0, '( 1 / %s )' % N400, 'RR'), f['qr']], 'remulcld', '( ( 1 / %s ) x. %s ) e. RR' % (N400, QRPD)), f['lr'],
            lin8(w, A0, [q0], '0 < ( ( 1 / %s ) x. %s )' % (N400, QRPD), {QRPD: f['qr']}), f['lp']], 'mulgt0d', '0 < %s' % VDET)
    absfd = cj([fdc], 'abscld', '( abs ` %s ) e. RR' % FDJ('j'))
    sfdr = c([rif, absfd], 'fsumrecl', '%s e. RR' % SFD)
    le1 = c([rif, lift(w, vr, Aj), absfd, fdle], 'fsumle', 'sum_ j e. %s %s <_ %s' % (RIP, VDET, SFD))
    cst = c([rif, c([vr], 'recnd', '%s e. CC' % VDET), w.inst('fsumconst')], 'syl2anc', 'sum_ j e. %s %s = ( %s x. %s )' % (RIP, VDET, JJ_, VDET))
    jv = c([cst, le1], 'eqbrtrrd', '( %s x. %s ) <_ %s' % (JJ_, VDET, SFD))
    JV = '( %s x. %s )' % (JJ_, VDET)
    jvr = c([jr, vr], 'remulcld', '%s e. RR' % JV)
    jv0 = c([jr, vr, j0, lin8(w, A0, [v0], '0 <_ %s' % VDET, {VDET: vr})], 'mulge0d', '0 <_ %s' % JV)
    sq1 = c([c([c([jvr, jv0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (JV, JV)), c([sfdr, jv], 'jca', '( %s e. RR /\\ %s <_ %s )' % (SFD, JV, SFD))], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ %s <_ %s ) )' % (JV, JV, SFD, JV, SFD)), w.inst('le2sq2')], 'syl', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (JV, SFD))
    # SIG x. DBL <_ ( C12 XBD ) x. ( J ( ROW + J CREM ) )
    JRC = '( %s x. ( %s + ( %s x. %s ) ) )' % (JJ_, ROW, JJ_, CREM)
    l400 = c([numst(w, A0, '; ; 4 0 0', 'RR+')], 'relogcld', '( log ` ; ; 4 0 0 ) e. RR')
    l4000 = c([numst(w, A0, '; ; 4 0 0', 'RR'), lin8(w, A0, [], '1 <_ ; ; 4 0 0', {}), w.inst('logge0')], 'syl2anc', '0 <_ ( log ` ; ; 4 0 0 )')
    FAC = '( 5 + ( 2 x. ( log ` ; ; 4 0 0 ) ) )'
    facr = c([numst(w, A0, '5', 'RR'), c([numst(w, A0, '2', 'RR'), l400], 'remulcld', '( 2 x. ( log ` ; ; 4 0 0 ) ) e. RR')], 'readdcld', '%s e. RR' % FAC)
    fac0 = lin8(w, A0, [l4000], '0 <_ %s' % FAC, {'( log ` ; ; 4 0 0 )': l400})
    kc7r = c([kr, numst(w, A0, C7, 'RR')], 'remulcld', '( K x. %s ) e. RR' % C7)
    kc70 = c([kr, numst(w, A0, C7, 'RR'), k0, numst(w, A0, C7, 'ge0')], 'mulge0d', '0 <_ ( K x. %s )' % C7)
    c90 = c([kc7r, facr, kc70, fac0], 'mulge0d', '0 <_ %s' % C9K)
    q2r = c([f['qr']], 'resqcld', '%s e. RR' % Q2); q20 = c([f['qr']], 'sqge0d', '0 <_ %s' % Q2)
    l2r = c([f['lr']], 'resqcld', '%s e. RR' % L2); l20 = c([f['lr']], 'sqge0d', '0 <_ %s' % L2)
    cq = c([c9, q2r], 'remulcld', '( %s x. %s ) e. RR' % (C9K, Q2)); cq0 = c([c9, q2r, c90, q20], 'mulge0d', '0 <_ ( %s x. %s )' % (C9K, Q2))
    cqh = c([cq, numst(w, A0, '( 1 / ; ; 1 0 0 )', 'RR')], 'remulcld', '( ( %s x. %s ) x. ( 1 / ; ; 1 0 0 ) ) e. RR' % (C9K, Q2))
    cqh0 = c([cq, numst(w, A0, '( 1 / ; ; 1 0 0 )', 'RR'), cq0, numst(w, A0, '( 1 / ; ; 1 0 0 )', 'ge0')], 'mulge0d', '0 <_ ( ( %s x. %s ) x. ( 1 / ; ; 1 0 0 ) )' % (C9K, Q2))
    row0 = c([cqh, l2r, cqh0, l20], 'mulge0d', '0 <_ %s' % ROW)
    jc = c([jr, cremr], 'remulcld', '( %s x. %s ) e. RR' % (JJ_, CREM)); jc0 = c([jr, cremr, j0, crem0], 'mulge0d', '0 <_ ( %s x. %s )' % (JJ_, CREM))
    inr = c([row, jc], 'readdcld', '( %s + ( %s x. %s ) ) e. RR' % (ROW, JJ_, CREM))
    in0 = lin8(w, A0, [row0, jc0], '0 <_ ( %s + ( %s x. %s ) )' % (ROW, JJ_, CREM), {ROW: row, '( %s x. %s )' % (JJ_, CREM): jc})
    jrcr = c([jr, inr], 'remulcld', '%s e. RR' % JRC); jrc0 = c([jr, inr, j0, in0], 'mulge0d', '0 <_ %s' % JRC)
    # DBL e. RR from SIG DBL bound? no: DBL <_ JRC and DBL is a real double sum: take it from the inequality's left side via zd2dbl's typing? derive: use fsumrecl again
    # (the inner closure is heavy; instead bound with the real JRC directly: SIG x. DBL <_ SIG x. JRC needs DBL e. RR)
    # DBL e. RR
    Ajk = '( %s /\\ k e. %s )' % (Aj, RIP)
    ck = Ctx(w, Ajk)
    kin = ck([], 'simpr', 'k e. %s' % RIP)
    SJ, XJ = SJK('j', 'k'), XJK('j', 'k')
    nyp = nyp_step(w, A0, c, nn_, ys, sr, s99, s1, tr, t0, pr, hsel)
    GA = tsub(S['zd2garg'], {'A': 'j', 'B': 'k'})
    gaa, gac = ante_of(GA)
    ga = ck([ck([lift(w, nyp, Ajk), ck([lift(w, jin, Ajk), kin], 'jca', '( j e. %s /\\ k e. %s )' % (RIP, RIP))], 'jca', gaa), w.inst('zd2garg')], 'syl', gac)
    p1 = ck([ga], 'simpld', top_and(gac)[0]); p23 = ck([ga], 'simprd', top_and(gac)[1])
    xjk = ck([p1], 'simpld', '%s e. %s' % (XJ, DB_N))
    p2 = ck([p23], 'simpld', top_and(top_and(gac)[1])[0])
    sjc = ck([p2], 'simpld', '%s e. CC' % SJ); reb = ck([p2], 'simprd', '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (SJ, SJ))
    hz2 = ck([lift(w, f['dr'], Ajk), lift(w, f['d1'], Ajk), lift(w, l2, Ajk)], '3jca', '( %s e. RR /\\ 1 < %s /\\ 2 <_ %s )' % (DSC, DSC, LD))
    BGC = tsub(stmt('gf2bgc'), {'D': DSC, 'X': XJ, 'S': SJ})
    bga, bgc_ = ante_of(BGC)
    bgc = ck([ck([ck([hz2, lift(w, nn_, Ajk)], 'jca', top_and(bga)[0]), ck([xjk, ck([sjc, ck([reb], 'simpld', '0 <_ ( Re ` %s )' % SJ)], 'jca', '( %s e. CC /\\ 0 <_ ( Re ` %s ) )' % (SJ, SJ))], 'jca', top_and(bga)[1])], 'jca', bga), w.inst('gf2bgc')], 'syl', bgc_)
    BG = BGXD(XJ, SJ)
    absbg = ck([bgc], 'abscld', '( abs ` %s ) e. RR' % BG)
    INN = 'sum_ k e. %s ( abs ` %s )' % (RIP, BG)
    innr = cj([lift(w, rif, Aj), absbg], 'fsumrecl', '%s e. RR' % INN)
    dblr = c([rif, innr], 'fsumrecl', '%s e. RR' % DBL)
    m1 = c([dblr, jrcr, sigr, sig0, dbl], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (SIG, DBL, SIG, JRC))
    cx_ = c([numst(w, A0, C12, 'RR'), xbr], 'remulcld', '( %s x. %s ) e. RR' % (C12, XBD))
    m2 = c([sigr, cx_, jrcr, jrc0, sigle], 'lemul1ad', '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (SIG, JRC, C12, XBD, JRC))
    AA = '( ( %s x. %s ) x. %s )' % (C12, XBD, ROW); BB = '( ( %s x. %s ) x. %s )' % (C12, XBD, CREM)
    lv = {XBD: xbr, JJ_: jr, ROW: row, CREM: cremr}
    idn = lin.lineq(w, A0, '( ( %s x. %s ) x. %s )' % (C12, XBD, JRC), '( %s x. ( %s + ( %s x. %s ) ) )' % (JJ_, AA, JJ_, BB), leaves=lv, products=True, atoms=list(lv))
    sfd2 = c([sfdr], 'resqcld', '( %s ^ 2 ) e. RR' % SFD); jv2 = c([jvr], 'resqcld', '( %s ^ 2 ) e. RR' % JV)
    sd = c([sigr, dblr], 'remulcld', '( %s x. %s ) e. RR' % (SIG, DBL)); sj = c([sigr, jrcr], 'remulcld', '( %s x. %s ) e. RR' % (SIG, JRC)); cj_ = c([cx_, jrcr], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (C12, XBD, JRC))
    k1 = c([jv2, sfd2, sd, sq1, hal], 'letrd', '( %s ^ 2 ) <_ ( %s x. %s )' % (JV, SIG, DBL))
    k2 = c([jv2, sd, sj, k1, m1], 'letrd', '( %s ^ 2 ) <_ ( %s x. %s )' % (JV, SIG, JRC))
    k3 = c([jv2, sj, cj_, k2, m2], 'letrd', '( %s ^ 2 ) <_ ( ( %s x. %s ) x. %s )' % (JV, C12, XBD, JRC))
    k4 = c([k3, idn], 'breqtrd', '( %s ^ 2 ) <_ ( %s x. ( %s + ( %s x. %s ) ) )' % (JV, JJ_, AA, JJ_, BB))
    # zdpar
    aar = c([cx_, row], 'remulcld', '%s e. RR' % AA); aa0 = c([cx_, row, c([numst(w, A0, C12, 'RR'), xbr, numst(w, A0, C12, 'ge0'), xb0], 'mulge0d', '0 <_ ( %s x. %s )' % (C12, XBD)), row0], 'mulge0d', '0 <_ %s' % AA)
    bbr = c([cx_, cremr], 'remulcld', '%s e. RR' % BB)
    PAR = tsub(stmt('zdpar'), {'J': JJ_, 'V': VDET, 'A': AA, 'B': BB})
    paa, pac = ante_of(PAR)
    par = c([c([c([c([c([jr, j0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (JJ_, JJ_)), c([vr, v0], 'jca', '( %s e. RR /\\ 0 < %s )' % (VDET, VDET))], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ 0 < %s ) )' % (JJ_, JJ_, VDET, VDET)),
                      c([c([aar, aa0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (AA, AA)), bbr], 'jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR )' % (AA, AA, BB))], 'jca', top_and(paa)[0]), c([k4, hb], 'jca', top_and(paa)[1])], 'jca', paa), w.inst('zdpar')], 'syl', pac)
    # ( 2 A ) / V ^ 2 = CJK XBD
    vsq = vdet_sq(w, A0, c, f)
    V2 = '( %s ^ 2 )' % VDET
    v2c = c([c([vr], 'recnd', '%s e. CC' % VDET)], 'sqcld', '%s e. CC' % V2)
    v2n0 = c([c([c([vr, v0], 'elrpd', '%s e. RR+' % VDET), c.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '%s e. RR+' % V2)], 'rpne0d', '%s =/= 0' % V2)
    TA = '( 2 x. %s )' % AA
    tac = c([c([numst(w, A0, '2', 'RR'), aar], 'remulcld', '%s e. RR' % TA)], 'recnd', '%s e. CC' % TA)
    CX = '( %s x. %s )' % (CJK, XBD)
    cxc = c([c([c([c([numst(w, A0, N3200, 'RR'), numst(w, A0, C12, 'RR')], 'remulcld', '( %s x. %s ) e. RR' % (N3200, C12)), c9], 'remulcld', '%s e. RR' % CJK), xbr], 'remulcld', '%s e. RR' % CX)], 'recnd', '%s e. CC' % CX)
    lv2 = {XBD: xbr, C9K: c9, Q2: q2r, L2: l2r}
    idn2 = lin.lineq(w, A0, '( ( ( %s x. %s ) x. %s ) x. %s )' % (R160, Q2, L2, CX), TA, leaves=lv2, products=True, atoms=list(lv2))
    idn3 = c([c([vsq], 'oveq1d', '( %s x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (V2, CX, R160, Q2, L2, CX)), idn2], 'eqtrd', '( %s x. %s ) = %s' % (V2, CX, TA))
    dm = c([tac, v2c, cxc, v2n0], 'divmuld', '( ( %s / %s ) = %s <-> ( %s x. %s ) = %s )' % (TA, V2, CX, V2, CX, TA))
    eq = c([idn3, dm], 'mpbird', '( %s / %s ) = %s' % (TA, V2, CX))
    w.qed([par, eq], 'breqtrd', S['zd2cpsh'])
    return go(w)


def gen_cps():
    w = W('zd2cps', 'Theorem 8.3, the master count (Lean ` card_paritySystem_le ` ): each parity system of Construction 7.2 has ` J <_ CJ X ^ ( 2 - 2 S ) ` ; the representatives are chosen by finite choice ( ~ ac6sfi ) on the nonempty cells ( ~ zd2cpsh ).')
    A0 = ante_of(S['zd2cps'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, tr, t0, pr = [c.g(x) for x in ('N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', 'T e. RR', '0 <_ T', 'P e. RR')]
    rif, yf = ri_fin(w, A0, c, nn_, ys)
    RIP = RI('P')
    CQ = CELL('( 1st ` q )', '( 2nd ` q )')
    Aq = '( %s /\\ q e. %s )' % (A0, RIP)
    cq = Ctx(w, Aq)
    qin = cq([], 'simpr', 'q e. %s' % RIP)
    _, cne, _, _, _, _ = ri_facts(w, Aq, qin, 'q')
    rg = w.s([w.s([], 'id', '( e e. %s -> e e. %s )' % (CQ, CQ))], 'rgen', 'A. e e. %s e e. %s' % (CQ, CQ))
    ex1 = cq([cq([cne, cq.a1(rg, 'A. e e. %s e e. %s' % (CQ, CQ))], 'jca', '( %s =/= (/) /\\ A. e e. %s e e. %s )' % (CQ, CQ, CQ)), w.inst('r19.2z')], 'syl', 'E. e e. %s e e. %s' % (CQ, CQ))
    ic = cq.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    CA, CB = '( S + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
    cac = cq([cq([lift(w, sr, Aq)], 'recnd', 'S e. CC'), cq([ic, cq([cq([lift(w, tr, Aq)], 'renegcld', '-u T e. RR')], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = cq([cq([], '1cnd', '1 e. CC'), cq([ic, cq([lift(w, tr, Aq)], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CB)
    bss = cq([cac, cbc, w.inst('crectss')], 'syl2anc', '%s C_ CC' % BOXR)
    zss = cq([cq.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZFX('( 1st ` q )'), BOXR)), '%s C_ %s' % (ZFX('( 1st ` q )'), BOXR)), bss], 'sstrd', '%s C_ CC' % ZFX('( 1st ` q )'))
    css = cq([cq.a1(w.s([], 'ssrab2', '%s C_ %s' % (CQ, ZFX('( 1st ` q )'))), '%s C_ %s' % (CQ, ZFX('( 1st ` q )'))), zss], 'sstrd', '%s C_ CC' % CQ)
    ex2 = cq([css, ex1, w.s([], 'ssrexv', '( %s C_ CC -> ( E. e e. %s e e. %s -> E. e e. CC e e. %s ) )' % (CQ, CQ, CQ, CQ))], 'sylc', 'E. e e. CC e e. %s' % CQ)
    ral = c([ex2], 'ralrimiva', 'A. q e. %s E. e e. CC e e. %s' % (RIP, CQ))
    FSEL = 'A. q e. %s ( f ` q ) e. %s' % (RIP, CQ)
    FF = '( f : %s --> CC /\\ %s )' % (RIP, FSEL)
    ac = w.s([w.s([], 'eleq1', '( e = ( f ` q ) -> ( e e. %s <-> ( f ` q ) e. %s ) )' % (CQ, CQ))], 'ac6sfi', '( ( %s e. Fin /\\ A. q e. %s E. e e. CC e e. %s ) -> E. f %s )' % (RIP, RIP, CQ, FF))
    ef = c([rif, ral, ac], 'syl2anc', 'E. f %s' % FF)
    Af = '( %s /\\ %s )' % (A0, FF)
    cf = Ctx(w, Af)
    CH = tsub(S['zd2cpsh'], {'H': 'f'})
    cha, chc = ante_of(CH)
    ch = cf([cf([cf([], 'simpll', top_and(cha)[0]), cf([lift(w, pr, Af), cf([cf([], 'simpr', FF)], 'simprd', FSEL)], 'jca', top_and(cha)[1])], 'jca', cha), w.inst('zd2cpsh')], 'syl', chc)
    ex = w.s([w.s([ch], 'ex', '( %s -> ( %s -> %s ) )' % (A0, FF, chc))], 'exlimdv', '( %s -> ( E. f %s -> %s ) )' % (A0, FF, chc))
    w.qed([ef, ex], 'mpd', S['zd2cps'])
    return go(w)


GENS = {'zd2sig': gen_sig, 'zd2hb': gen_hb, 'zd2det': gen_det, 'zd2dbl': gen_dbl, 'zd2cpsh': gen_cpsh, 'zd2cps': gen_cps}

if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
