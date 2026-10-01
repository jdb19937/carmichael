"""Sortie CEN2: real parts of dominated Dirichlet series (cen2re), the linear group (cen2gs, cen2gb) and the cross group
(cen2gd); Lean Census hsum1, hsum2, hsum4, hbound1, hbound2, hbound4."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure, lift
from c9lib import top_and
from lin import linarith, nlinarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def icn(w, A):
    return w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A)


def gen_re():
    w = W('cen2re', 'A Dirichlet series ` sum B k ^ -S ` dominated by ` C Lam ( k ) ` on ` 1 < Re S ` : the series of real parts converges and sums to the real part (Lean Census ` summable_term_of_le ` , ` summable_re ` , ` Complex.re_tsum ` ; ZR ~ zrisre ).')
    h = {}
    for i in range(1, 6):
        h[i] = w.s([], 'cen2re.%d' % i, S['cen2re.%d' % i], name='h%d' % i)
    P = 'ph'; P1 = '( ph /\\ k e. NN )'
    s = lambda hh, r, f: w.s(hh, r, '( ph -> %s )' % f)
    a = lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (P1, f))
    sc = s([h[1]], 'simpld', 'S e. CC')
    cv = w.s([h[1], h[2], h[3], h[4]], 'cencvg', '( ph -> seq 1 ( + , ( k e. NN |-> ( B x. ( k ^c -u S ) ) ) ) e. dom ~~> )')
    BK = '( B x. ( k ^c -u S ) )'; BN = '( E x. ( n ^c -u S ) )'
    FK = '( k e. NN |-> %s )' % BK; FN = '( n e. NN |-> %s )' % BN
    eqkn = w.s([h[5], w.s([], 'oveq1', '( k = n -> ( k ^c -u S ) = ( n ^c -u S ) )')], 'oveq12d', '( k = n -> %s = %s )' % (BK, BN))
    me = w.s([eqkn], 'cbvmptv', '%s = %s' % (FK, FN))
    mea = s([me], 'a1i', '%s = %s' % (FK, FN))
    cvn = s([s([mea], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (FK, FN)), cv], 'eqeltrrd', 'seq 1 ( + , %s ) e. dom ~~>' % FN)
    kn = a([], 'simpr', 'k e. NN')
    sc1 = a([a([], 'simpl', 'ph'), sc], 'syl', 'S e. CC')
    bkc = a([h[3], a([a([kn], 'nncnd', 'k e. CC'), a([sc1], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')], 'mulcld', '%s e. CC' % BK)
    fk = s([bkc, w.s([], 'eqid', '%s = %s' % (FK, FK))], 'fmptd', '%s : NN --> CC' % FK)
    fn = s([fk, s([mea], 'feq1d', '( %s : NN --> CC <-> %s : NN --> CC )' % (FK, FN))], 'mpbid', '%s : NN --> CC' % FN)
    ZR = split_imp(stmt('zrisre'))[1].replace('F', FN)
    zr = s([fn, cvn, w.inst('zrisre')], 'syl2anc', ZR)
    z1, z2 = top_and(ZR)
    eqnk = w.s([w.s([eqkn], 'equcoms', '( n = k -> %s = %s )' % (BK, BN))], 'eqcomd', '( n = k -> %s = %s )' % (BN, BK))
    fv = a([a([], 'eqidd', '%s = %s' % (FN, FN)), w.s([eqnk], 'adantl', '( ( %s /\\ n = k ) -> %s = %s )' % (P1, BN, BK)), kn, bkc], 'fvmptd',
           '( %s ` k ) = %s' % (FN, BK))
    fn1 = a([a([], 'simpl', 'ph'), fn], 'syl', '%s : NN --> CC' % FN)
    RO = '( Re o. %s )' % FN
    c3 = a([fn1, kn, w.inst('fvco3')], 'syl2anc', '( %s ` k ) = ( Re ` ( %s ` k ) )' % (RO, FN))
    fvr = a([fv], 'fveq2d', '( Re ` ( %s ` k ) ) = ( Re ` %s )' % (FN, BK))
    c4 = a([c3, fvr], 'eqtrd', '( %s ` k ) = ( Re ` %s )' % (RO, BK))
    rbr = a([bkc], 'recld', '( Re ` %s ) e. RR' % BK)
    cvr = s([zr], 'simprd', z2)
    SR = 'sum_ k e. NN ( Re ` %s )' % BK
    sr = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([], '1zzd', '1 e. ZZ'), c4, rbr, cvr], 'isumrecl', '( ph -> %s e. RR )' % SR)
    s1 = s([fvr], 'sumeq2dv', 'sum_ k e. NN ( Re ` ( %s ` k ) ) = %s' % (FN, SR))
    s2 = s([fv], 'sumeq2dv', 'sum_ k e. NN ( %s ` k ) = sum_ k e. NN %s' % (FN, BK))
    s3 = s([s2], 'fveq2d', '( Re ` sum_ k e. NN ( %s ` k ) ) = ( Re ` sum_ k e. NN %s )' % (FN, BK))
    z1s = s([zr], 'simpld', z1)
    e1 = s([s([s1], 'eqcomd', '%s = sum_ k e. NN ( Re ` ( %s ` k ) ) ' % (SR, FN)), s([z1s], 'eqcomd', 'sum_ k e. NN ( Re ` ( %s ` k ) ) = ( Re ` sum_ k e. NN ( %s ` k ) )' % (FN, FN))],
           'eqtrd', '%s = ( Re ` sum_ k e. NN ( %s ` k ) )' % (SR, FN))
    e2 = s([e1, s3], 'eqtrd', '%s = ( Re ` sum_ k e. NN %s )' % (SR, BK))
    fc = s([s([w.s([], 'ref', 'Re : CC --> RR')], 'a1i', 'Re : CC --> RR'), fn, w.inst('fcompt')], 'syl2anc', '%s = ( k e. NN |-> ( Re ` ( %s ` k ) ) )' % (RO, FN))
    m2 = s([fvr], 'mpteq2dva', '( k e. NN |-> ( Re ` ( %s ` k ) ) ) = ( k e. NN |-> ( Re ` %s ) )' % (FN, BK))
    m3 = s([fc, m2], 'eqtrd', '%s = ( k e. NN |-> ( Re ` %s ) )' % (RO, BK))
    cvk = s([s([m3], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) )' % (RO, BK)), cvr], 'eqeltrrd',
            'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~>' % BK)
    w.qed([cvk, s([sr, e2], 'jca', '( %s e. RR /\\ %s = ( Re ` sum_ k e. NN %s ) )' % (SR, SR, BK))], 'jca', S['cen2re'])
    return run(w)


def series_rewrite(w, A0, body_old, body_new, eq1, cvold, sumold_r, sumold_eq, target_eq_rhs):
    """from ( A1 -> body_new = body_old ) (eq1), conv/RR/eq of the old series, the new ones"""
    A1 = '( %s /\\ k e. NN )' % A0
    s = lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (A0, f))
    m = s([w.s([eq1], 'fveq2d', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (A1, body_new, body_old))], 'mpteq2dva',
          '( k e. NN |-> ( Re ` %s ) ) = ( k e. NN |-> ( Re ` %s ) )' % (body_new, body_old))
    cv = s([s([m], 'seqeq3d', 'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) = seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) )' % (body_new, body_old)), cvold], 'eqeltrrd',
           'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~>' % body_new) if False else None
    sq = s([m], 'seqeq3d', 'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) = seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) )' % (body_new, body_old))
    cv = s([s([sq], 'eqcomd', 'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) = seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) )' % (body_old, body_new)), cvold],
           'eqeltrrd', 'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~>' % body_new)
    SN = 'sum_ k e. NN ( Re ` %s )' % body_new; SO = 'sum_ k e. NN ( Re ` %s )' % body_old
    se = s([w.s([eq1], 'fveq2d', '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (A1, body_new, body_old))], 'sumeq2dv', '%s = %s' % (SN, SO))
    snr = s([se, sumold_r], 'eqeltrd', '%s e. RR' % SN)
    sne = s([se, sumold_eq], 'eqtrd', '%s = %s' % (SN, target_eq_rhs))
    return cv, snr, sne


def gen_gs():
    w = W('cen2gs', 'The linear series ` sum Re ( Lam ( k ) k ^ - ( 1 + 3 D ) chi ( k ) k ^ - i T ) ` converges and is the real part of ` sum chi ( k ) Lam ( k ) k ^ - ( 1 + 3 D + i T ) ` (Lean Census ` hsum1 ` , ` hbound2 ` , ` LSeries_twist_vonMangoldt_eq ` in Dirichlet-series form).')
    A0, C0 = split_imp(S['cen2gs'])
    A1 = '( %s /\\ k e. NN )' % A0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    L1 = lambda st: lift(w, st, A1)
    nx = s([], 'simpl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )')
    tr = s([], 'simprl', 'T e. RR'); dd = s([], 'simprr', DDH)
    drp = s([dd], 'simpld', 'D e. RR+')
    ic = icn(w, A0)
    c0 = Closure(w, A0, {'D': ('RR+', drp), 'T': ('RR', tr), '_i': ('CC', ic)})
    P = PT3('T'); Q = '( 1 + ( 3 x. D ) )'
    pc = c0.mem(P, 'CC')
    pre = s([c0.mem(Q, 'RR'), tr], 'crred', '( Re ` %s ) = %s' % (P, Q))
    q1 = s([s([], '1red', '1 e. RR'), c0.mem('( 3 x. D )', 'RR+')], 'ltaddrpd', '1 < %s' % Q)
    h1 = s([pc, s([q1, pre], 'breqtrrd', '1 < ( Re ` %s )' % P)], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (P, P))
    kn = a([], 'simpr', 'k e. NN')
    L = '( Lam ` k )'; CH = CHV('k')
    lr = a([kn, w.inst('vmacl')], 'syl', '%s e. RR' % L); l0 = a([kn, w.inst('vmage0')], 'syl', '0 <_ %s' % L)
    ch = a([L1(nx), a([kn], 'nnzd', 'k e. ZZ'), w.inst('cen2chv')], 'syl2anc', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CH, CH))
    chc = a([ch], 'simpld', '%s e. CC' % CH); chl = a([ch], 'simprd', '( abs ` %s ) <_ 1' % CH)
    c1 = Closure(w, A1, {'k': ('NN', kn), 'D': ('RR+', L1(drp)), 'T': ('RR', L1(tr)), L: [('RR', lr), ('ge0', l0)], CH: ('CC', chc), '_i': ('CC', icn(w, A1))})
    B = '( %s x. %s )' % (CH, L)
    bc = c1.mem(B, 'CC')
    AC = '( abs ` %s )' % CH
    c1.have(AC, 'RR', a([chc], 'abscld', '%s e. RR' % AC)); a0 = a([chc], 'absge0d', '0 <_ %s' % AC); c1.have(AC, 'ge0', a0)
    ab = a([chc, c1.mem(L, 'CC')], 'absmuld', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (B, AC, L))
    ab2 = a([ab, a([a([lr, l0], 'absidd', '( abs ` %s ) = %s' % (L, L))], 'oveq2d', '( %s x. ( abs ` %s ) ) = ( %s x. %s )' % (AC, L, AC, L))], 'eqtrd',
            '( abs ` %s ) = ( %s x. %s )' % (B, AC, L))
    le = nlinarith(w, A1, [chl, l0], '( %s x. %s ) <_ ( 1 x. %s )' % (AC, L, L), closure=c1)
    h4 = a([ab2, le], 'eqbrtrd', '( abs ` %s ) <_ ( 1 x. %s )' % (B, L))
    BN = tokrep(B, {'k': 'n'})
    h5, bn = ren(w, B)
    assert bn == BN
    one = s([], '1red', '1 e. RR')
    RE = split_imp(S['cen2re'])[1] if False else None
    BK = '( %s x. ( k ^c -u %s ) )' % (B, P)
    SR = 'sum_ k e. NN ( Re ` %s )' % BK
    re = w.s([h1, one, bc, h4, h5], 'cen2re', '( %s -> ( seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s = ( Re ` sum_ k e. NN %s ) ) ) )' % (A0, BK, SR, SR, BK))
    cvo = s([re], 'simpld', 'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~>' % BK)
    re2 = s([re], 'simprd', '( %s e. RR /\\ %s = ( Re ` sum_ k e. NN %s ) )' % (SR, SR, BK))
    NEWB = '( %s x. %s )' % (AW(), VT('N', 'X', 'T'))
    t1 = a([a([kn, c1.mem('D', 'RR')], 'jca', '( k e. NN /\\ D e. RR )'), a([chc, L1(tr)], 'jca', '( %s e. CC /\\ T e. RR )' % CH), w.inst('cen2t1')], 'syl2anc',
           '%s = %s' % (NEWB, BK))
    cv, snr, sne = series_rewrite(w, A0, BK, NEWB, t1, cvo, s([re2], 'simpld', '%s e. RR' % SR), s([re2], 'simprd', '%s = ( Re ` sum_ k e. NN %s )' % (SR, BK)),
                                  '( Re ` sum_ k e. NN %s )' % BK)
    SN = 'sum_ k e. NN ( Re ` %s )' % NEWB
    w.qed([cv, s([snr, sne], 'jca', '( %s e. RR /\\ %s = ( Re ` sum_ k e. NN %s ) )' % (SN, SN, BK))], 'jca', S['cen2gs'])
    return run(w)


def gen_gb():
    w = W('cen2gb', 'The linear series at a zero: ` sum Re ( Lam ( k ) k ^ - ( 1 + 3 D ) chi ( k ) k ^ - i Im R ) <_ K log ( N ( | Im R | + 2 ) ) - 1 / ( 4 D ) ` (Lean Census ` hsum1 ` , ` hbound1 ` ; CEN1 ~ cenrelz at the point ` 1 + 3 D ` ).')
    A0, C0 = split_imp(S['cen2gb'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    nx = s([chi], 'simpld', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )')
    H2 = top_and(A0)[1]
    h2 = s([], 'simpr', H2)
    dd = s([h2], 'simpld', DDH)
    H3 = top_and(H2)[1]
    rc = s([s([h2], 'simprd', H3)], 'simp1d', 'R e. CC')
    IR = '( Im ` R )'
    ir = s([rc], 'imcld', '%s e. RR' % IR)
    GS = tokrep(split_imp(S['cen2gs'])[1], {'T': IR})
    gs = s([nx, s([ir, dd], 'jca', '( %s e. RR /\\ %s )' % (IR, DDH)), w.inst('cen2gs')], 'syl2anc', GS)
    g1, g2 = top_and(GS)
    ga, gb_ = top_and(g2)
    rz = w.s([], 'cenrelz', stmt('cenrelz'))
    BND = split_imp(stmt('cenrelz'))[1].split(' <_ ', 1)[1].rstrip(' )') if False else None
    RZ = split_imp(stmt('cenrelz'))[1]
    lhs = '( Re ` %s )' % gb_.split(' = ( Re ` ', 1)[1][:-2]
    SB = ga.rsplit(' e. RR', 1)[0]
    rhs = '( %s - ( 1 / ( 4 x. D ) ) )' % KLOG('( N x. ( ( abs ` ( Im ` R ) ) + 2 ) )')
    le = s([s([gs], 'simprd', g2)], 'simprd', gb_)
    fin = s([le, rz], 'eqbrtrd', '%s <_ %s' % (SB, rhs))
    w.qed([s([gs], 'simpld', g1), s([s([s([gs], 'simprd', g2)], 'simpld', ga), fin], 'jca', '( %s /\\ %s <_ %s )' % (ga, SB, rhs))], 'jca', S['cen2gb'])
    return run(w)


def gen_gd():
    w = W('cen2gd', 'The cross series of two distinct primitive characters ` X ` mod ` N ` , ` Y ` mod ` M ` at heights ` T ` , ` U ` : ` sum Re ( Lam ( k ) k ^ - ( 1 + 3 D ) chi ( k ) k ^ - i T * ( psi ( k ) k ^ - i U ) ) <_ K log ( N M ( | T - U | + 2 ) ) ` (Lean Census ` hsum4 ` , ` hbound4 ` ; the product character ` chi * conj psi ` mod ` N M ` is nonprincipal by ZF2 ~ dchrprodne1 , CEN1 ~ cenrele at ` A = 3 D ` ).')
    A0, C0 = split_imp(S['cen2gd'])
    A1 = '( %s /\\ k e. NN )' % A0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    L1 = lambda st: lift(w, st, A1)
    P1, P2 = top_and(A0)
    p1 = s([], 'simpl', P1); p2 = s([], 'simpr', P2)
    q1, q2, q3 = top_and(P1)
    nm = s([p1], 'simp1d', q1); cx = s([p1], 'simp2d', q2)
    nn = s([nm], 'simpld', 'N e. NN'); mn = s([nm], 'simprd', 'M e. NN')
    xc = s([cx], 'simpld', top_and(q2)[0]); yc = s([cx], 'simprd', top_and(q2)[1])
    DN = '( Base ` ( DChr ` N ) )'; DM = '( Base ` ( DChr ` M ) )'
    xd = s([xc], 'simpld', 'X e. %s' % DN); yd = s([yc], 'simpld', 'Y e. %s' % DM)
    tu = s([p2], 'simpld', '( T e. RR /\\ U e. RR )'); dd = s([p2], 'simprd', DDH)
    tr = s([tu], 'simpld', 'T e. RR'); ur = s([tu], 'simprd', 'U e. RR')
    drp = s([dd], 'simpld', 'D e. RR+'); dle = s([dd], 'simprd', 'D <_ %s' % F140)
    ic = icn(w, A0)
    c0 = Closure(w, A0, {'D': ('RR+', drp), 'T': ('RR', tr), 'U': ('RR', ur), 'N': ('NN', nn), 'M': ('NN', mn), '_i': ('CC', ic)})
    NM = '( N x. M )'
    nmn = c0.mem(NM, 'NN')
    GNM = '( DChr ` %s )' % NM; DNM = '( Base ` %s )' % GNM
    GM = '( DChr ` M )'; IM = '( invg ` %s )' % GM; IY = '( %s ` Y )' % IM
    IX = '( ( N DChrInd %s ) ` X )' % NM; IIY = '( ( M DChrInd %s ) ` %s )' % (NM, IY)
    PSI = '( %s ( +g ` %s ) %s )' % (IX, GNM, IIY)
    ne1 = s([p1, w.inst('dchrprodne1')], 'syl', '%s =/= ( 0g ` %s )' % (PSI, GNM))
    nz = c0.mem('N', 'ZZ'); mz = c0.mem('M', 'ZZ')
    dv1 = s([nz, mz, w.inst('dvdsmul1')], 'syl2anc', 'N || %s' % NM)
    dv2 = s([nz, mz, w.inst('dvdsmul2')], 'syl2anc', 'M || %s' % NM)
    ixd = s([s([nn, nmn, dv1], '3jca', '( N e. NN /\\ %s e. NN /\\ N || %s )' % (NM, NM)), xd, w.inst('dchrindcl')], 'syl2anc', '%s e. %s' % (IX, DNM))
    grp = s([s([mn, w.inst('dchrabl')], 'syl', '%s e. Abel' % GM), w.inst('ablgrp')], 'syl', '%s e. Grp' % GM)
    gi = w.s([w.s([], 'eqid', '%s = %s' % (DM, DM)), w.s([], 'eqid', '%s = %s' % (IM, IM))], 'grpinvcl', '( ( %s e. Grp /\\ Y e. %s ) -> %s e. %s )' % (GM, DM, IY, DM))
    iyd = s([grp, yd, gi], 'syl2anc', '%s e. %s' % (IY, DM))
    iiyd = s([s([mn, nmn, dv2], '3jca', '( M e. NN /\\ %s e. NN /\\ M || %s )' % (NM, NM)), iyd, w.inst('dchrindcl')], 'syl2anc', '%s e. %s' % (IIY, DNM))
    ZNM = '( Z/nZ ` %s )' % NM
    psd = s([w.s([], 'eqid', '%s = %s' % (GNM, GNM)), w.s([], 'eqid', '%s = %s' % (ZNM, ZNM)), w.s([], 'eqid', '%s = %s' % (DNM, DNM)),
             w.s([], 'eqid', '( +g ` %s ) = ( +g ` %s )' % (GNM, GNM)), ixd, iiyd], 'dchrmulcl', '%s e. %s' % (PSI, DNM))
    CHIP = '( ( %s e. NN /\\ %s e. %s ) /\\ %s =/= ( 0g ` %s ) )' % (NM, PSI, DNM, PSI, GNM)
    chip = s([s([nmn, psd], 'jca', '( %s e. NN /\\ %s e. %s )' % (NM, PSI, DNM)), ne1], 'jca', CHIP)
    TU = '( T - U )'; A3 = '( 3 x. D )'
    a3 = c0.mem(A3, 'RR+'); a3le = linarith(w, A0, [dle], '%s <_ ( 1 / 2 )' % A3, closure=c0)
    RLE = tokrep(stmt('cenrele'), {'N': NM, 'X': PSI, 'T': TU, 'A': A3})
    rle_a, rle_c = split_imp(RLE)
    rle = s([s([chip, s([c0.mem(TU, 'RR'), s([a3, a3le], 'jca', '( %s e. RR+ /\\ %s <_ ( 1 / 2 ) )' % (A3, A3))], 'jca',
                                                  '( %s e. RR /\\ ( %s e. RR+ /\\ %s <_ ( 1 / 2 ) ) )' % (TU, A3, A3))], 'jca', rle_a), w.inst('cenrele')], 'syl', rle_c)
    # the series by cen2re
    P = PT3(TU); Q = '( 1 + ( 3 x. D ) )'
    pc = c0.mem(P, 'CC')
    pre = s([c0.mem(Q, 'RR'), c0.mem(TU, 'RR')], 'crred', '( Re ` %s ) = %s' % (P, Q))
    q1r = s([s([], '1red', '1 e. RR'), a3], 'ltaddrpd', '1 < %s' % Q)
    h1 = s([pc, s([q1r, pre], 'breqtrrd', '1 < ( Re ` %s )' % P)], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (P, P))
    kn = a([], 'simpr', 'k e. NN')
    L = '( Lam ` k )'; CX = CHV('k', 'N', 'X'); CY = CHV('k', 'M', 'Y')
    lr = a([kn, w.inst('vmacl')], 'syl', '%s e. RR' % L); l0 = a([kn, w.inst('vmage0')], 'syl', '0 <_ %s' % L)
    kz = a([kn], 'nnzd', 'k e. ZZ')
    chx = a([a([L1(nn), L1(xd)], 'jca', '( N e. NN /\\ X e. %s )' % DN), kz, w.inst('cen2chv')], 'syl2anc', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CX, CX))
    chy = a([a([L1(mn), L1(yd)], 'jca', '( M e. NN /\\ Y e. %s )' % DM), kz, w.inst('cen2chv')], 'syl2anc', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CY, CY))
    cxc = a([chx], 'simpld', '%s e. CC' % CX); cyc = a([chy], 'simpld', '%s e. CC' % CY)
    c1 = Closure(w, A1, {'k': ('NN', kn), 'D': ('RR+', L1(drp)), 'T': ('RR', L1(tr)), 'U': ('RR', L1(ur)), L: [('RR', lr), ('ge0', l0)],
                         CX: ('CC', cxc), CY: ('CC', cyc), '_i': ('CC', icn(w, A1))})
    CCY = '( * ` %s )' % CY
    ccy = a([cyc], 'cjcld', '%s e. CC' % CCY); c1.have(CCY, 'CC', ccy)
    E = '( %s x. %s )' % (CX, CCY); B = '( %s x. %s )' % (E, L)
    AX = '( abs ` %s )' % CX; AY = '( abs ` %s )' % CY
    ax0 = a([cxc], 'absge0d', '0 <_ %s' % AX); ay0 = a([cyc], 'absge0d', '0 <_ %s' % AY)
    c1.have(AX, 'RR', a([cxc], 'abscld', '%s e. RR' % AX)); c1.have(AY, 'RR', a([cyc], 'abscld', '%s e. RR' % AY))
    ab1 = a([c1.mem(E, 'CC'), c1.mem(L, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (B, E, L))
    ab2 = a([cxc, ccy], 'absmuld', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (E, AX, CCY))
    ab3 = a([cyc], 'abscjd', '( abs ` %s ) = %s' % (CCY, AY))
    ab4 = a([ab2, a([ab3], 'oveq2d', '( %s x. ( abs ` %s ) ) = ( %s x. %s )' % (AX, CCY, AX, AY))], 'eqtrd', '( abs ` %s ) = ( %s x. %s )' % (E, AX, AY))
    ab5 = a([ab1, a([ab4, a([lr, l0], 'absidd', '( abs ` %s ) = %s' % (L, L))], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( %s x. %s ) x. %s )' % (E, L, AX, AY, L))],
            'eqtrd', '( abs ` %s ) = ( ( %s x. %s ) x. %s )' % (B, AX, AY, L))
    exy = nlinarith(w, A1, [a([chx], 'simprd', '%s <_ 1' % AX), a([chy], 'simprd', '%s <_ 1' % AY), ax0, ay0], '( %s x. %s ) <_ 1' % (AX, AY), closure=c1)
    XY = '( %s x. %s )' % (AX, AY)
    c1.have(XY, 'RR', c1.mem(XY, 'RR'))
    le = nlinarith(w, A1, [exy, l0], '( %s x. %s ) <_ ( 1 x. %s )' % (XY, L, L), closure=c1, atoms=[XY])
    h4 = a([ab5, le], 'eqbrtrd', '( abs ` %s ) <_ ( 1 x. %s )' % (B, L))
    h5, bn = ren(w, B)
    BK = '( %s x. ( k ^c -u %s ) )' % (B, P)
    SR = 'sum_ k e. NN ( Re ` %s )' % BK
    re = w.s([h1, s([], '1red', '1 e. RR'), c1.mem(B, 'CC'), h4, h5], 'cen2re',
             '( %s -> ( seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s = ( Re ` sum_ k e. NN %s ) ) ) )' % (A0, BK, SR, SR, BK))
    cvo = s([re], 'simpld', 'seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~>' % BK)
    re2 = s([re], 'simprd', '( %s e. RR /\\ %s = ( Re ` sum_ k e. NN %s ) )' % (SR, SR, BK))
    NEWB = '( %s x. ( %s x. ( * ` %s ) ) )' % (AW(), VT('N', 'X', 'T'), VT('M', 'Y', 'U'))
    t3 = a([a([kn, c1.mem('D', 'RR')], 'jca', '( k e. NN /\\ D e. RR )'),
            a([a([cxc, cyc], 'jca', '( %s e. CC /\\ %s e. CC )' % (CX, CY)), a([L1(tr), L1(ur)], 'jca', '( T e. RR /\\ U e. RR )')], 'jca',
              '( ( %s e. CC /\\ %s e. CC ) /\\ ( T e. RR /\\ U e. RR ) )' % (CX, CY)), w.inst('cen2t3')], 'syl2anc', '%s = %s' % (NEWB, BK))
    cv, snr, sne = series_rewrite(w, A0, BK, NEWB, t3, cvo, s([re2], 'simpld', '%s e. RR' % SR), s([re2], 'simprd', '%s = ( Re ` sum_ k e. NN %s )' % (SR, BK)),
                                  '( Re ` sum_ k e. NN %s )' % BK)
    # Re sum B pw = Re LAM_psi
    PV = '( %s ` ( ( ZRHom ` %s ) ` k ) )' % (PSI, ZNM)
    pv = a([a([L1(nm), a([L1(xd), L1(yd)], 'jca', '( X e. %s /\\ Y e. %s )' % (DN, DM)), kz], '3jca', '( ( N e. NN /\\ M e. NN ) /\\ ( X e. %s /\\ Y e. %s ) /\\ k e. ZZ )' % (DN, DM)),
            w.inst('cenprodv')], 'syl', '%s = %s' % (PV, E))
    PW = '( k ^c -u %s )' % P
    pv2 = a([a([pv], 'oveq1d', '( %s x. %s ) = %s' % (PV, L, B))], 'oveq1d', '( ( %s x. %s ) x. %s ) = %s' % (PV, L, PW, BK))
    LAMP = 'sum_ k e. NN ( ( %s x. %s ) x. %s )' % (PV, L, PW)
    se = s([s([pv2], 'sumeq2dv', '%s = sum_ k e. NN %s' % (LAMP, BK))], 'fveq2d', '( Re ` %s ) = ( Re ` sum_ k e. NN %s )' % (LAMP, BK))
    SN = 'sum_ k e. NN ( Re ` %s )' % NEWB
    e3 = s([sne, se], 'eqtr4d', '%s = ( Re ` %s )' % (SN, LAMP))
    fin = s([e3, rle], 'eqbrtrd', '%s <_ %s' % (SN, KLOG('( ( N x. M ) x. ( ( abs ` ( T - U ) ) + 2 ) )')))
    w.qed([cv, s([snr, fin], 'jca', top_and(split_imp(S['cen2gd'])[1])[1])], 'jca', S['cen2gd'])
    return run(w)


if __name__ == '__main__':
    gen_re()
    gen_gs()
    gen_gb()
    gen_gd()
