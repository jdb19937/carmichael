"""Sortie CEN1: Re ( -L'/L ) upper bound (cenrele) and the gain bound at a zero (cenrelz)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen1lib import *
from cl import split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def icc(w, A0):
    return w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)


def point(w, A0, Ae, ar, ap, a12, Te, tr):
    """S = ( ( 1 + Ae ) + ( _i x. Te ) ): steps S e. CC, abs ( S - CT ) <_ 3/2, 1 < Re S, Re S = 1 + Ae"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    SS = PT(Ae, Te)
    c = Closure(w, A0, {Ae: ('RR', ar), Te: ('RR', tr)}); c.atom(Ae); c.atom(Te)
    oe = c.mem('( 1 + %s )' % Ae, 'RR')
    tc = s([tr], 'recnd', '%s e. CC' % Te)
    sc = s([s([oe], 'recnd', '( 1 + %s ) e. CC' % Ae), s([icc(w, A0), tc], 'mulcld', '( _i x. %s ) e. CC' % Te)], 'addcld', '%s e. CC' % SS)
    rs = s([oe, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + %s )' % (SS, Ae))
    cd = Closure(w, A0, {Ae: ('CC', s([ar], 'recnd', '%s e. CC' % Ae)), Te: ('CC', tc)})
    cd.atom(Ae); cd.atom(Te)
    cd.leaf('_i', 'CC', icc(w, A0)); cd.atom('_i')
    dif = ringeq(w, A0, '( %s - %s )' % (SS, CT(Te)), '( %s - 1 )' % Ae, cd)
    a1 = linarith(w, A0, [a12], '%s <_ 1' % Ae, closure=c)
    ad = s([s([dif], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - 1 ) )' % (SS, CT(Te), Ae)), s([ar, s([], '1red', '1 e. RR'), a1], 'abssuble0d', '( abs ` ( %s - 1 ) ) = ( 1 - %s )' % (Ae, Ae))],
           'eqtrd', '( abs ` ( %s - %s ) ) = ( 1 - %s )' % (SS, CT(Te), Ae))
    d32 = s([ad, linarith(w, A0, [ap], '( 1 - %s ) <_ ( 3 / 2 )' % Ae, closure=c)], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( 3 / 2 )' % (SS, CT(Te)))
    s1 = s([s([], '1red', '1 e. RR'), s([ap, ar], 'x', 'x') if False else s([ar, ap], 'elrpd', '%s e. RR+' % Ae)], 'ltaddrpd', '1 < ( 1 + %s )' % Ae)
    s1 = s([s1, rs], 'breqtrrd', '1 < ( Re ` %s )' % SS)
    return SS, sc, d32, s1, rs


def lnd_at(w, A0, chi, SS, Te, tr, sc, d32, s1):
    LN = tsub(S['cenlnd'], {'S': SS, 'T': Te})
    la, lc = split_imp(LN)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    st = s([s([chi, tr], 'jca', top_and(la)[0]), s([sc, d32, s1], '3jca', top_and(la)[1]), w.inst('cenlnd')], 'syl2anc', lc)
    b1, b2 = top_and(lc)
    return s([st], 'simpld', b1), s([st], 'simprd', b2), b1, b2


def common(w, A0, chi, tr, Te):
    """zfin, KL(Te) e. RR"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    LZ = tsub(stmt('lchrzc8'), {'T': Te}); lza, lzc = split_imp(LZ)
    zfin = s([s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)], 'simp1d', top_and(lzc)[0])
    zord = s([s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)], 'simp2d', top_and(lzc)[1])
    nn_ = s([s([chi], 'simpld', NXH)], 'simpld', 'N e. NN')
    AT = '( abs ` %s )' % Te
    at = s([s([tr], 'recnd', '%s e. CC' % Te)], 'abscld', '%s e. RR' % AT)
    ca = Closure(w, A0, {AT: ('RR', at)}); ca.atom(AT)
    t2p = s([ca.mem('( %s + 2 )' % AT, 'RR'), linarith(w, A0, [s([s([tr], 'recnd', '%s e. CC' % Te)], 'absge0d', '0 <_ %s' % AT)], '0 < ( %s + 2 )' % AT, closure=ca)], 'elrpd', '( %s + 2 ) e. RR+' % AT)
    XT = '( N x. ( %s + 2 ) )' % AT
    lg = s([s([s([nn_], 'nnrpd', 'N e. RR+'), t2p], 'rpmulcld', '%s e. RR+' % XT)], 'relogcld', '( log ` %s ) e. RR' % XT)
    ck = Closure(w, A0, {'( log ` %s )' % XT: ('RR', lg)}); ck.atom('( log ` %s )' % XT)
    return zfin, zord, ck.mem(KL(Te), 'RR')


def xr_of_le(w, A0, st, a, b):
    """( A0 -> a e. RR* ) from st : ( A0 -> a <_ b )"""
    br = w.s([w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (a, b, a, b))
    return w.s([w.s([st, br], 'syl', '( %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (A0, a, b))], 'simpld', '( %s -> %s e. RR* )' % (A0, a))


def gen_rele():
    w = W('cenrele', 'Lean Census ` re_neg_logDeriv_le ` : ` Re ( -L\'/L ) ( ( 1 + A ) + i T ) <_ 17500000 log ( N ( abs T + 2 ) ) ` for ` chi ` nonprincipal, ` 0 < A <_ 1 / 2 ` ( ` -L\'/L ` written as its Dirichlet series, KD1 ~ kdlogdv ; Lean ` 520000 ` ).')
    A0, C0 = split_imp(S['cenrele'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    t2 = s([], 'simpr', '( T e. RR /\\ ( A e. RR+ /\\ A <_ ( 1 / 2 ) ) )')
    tr = s([t2], 'simpld', 'T e. RR'); ah = s([t2], 'simprd', '( A e. RR+ /\\ A <_ ( 1 / 2 ) )')
    ap = s([ah], 'simpld', 'A e. RR+'); a12 = s([ah], 'simprd', 'A <_ ( 1 / 2 )'); ar = s([ap], 'rpred', 'A e. RR')
    SS, sc, d32, s1, rs = point(w, A0, 'A', ar, s([ap], 'rpgt0d', '0 < A'), a12, 'T', tr)
    bd, al, b1, b2 = lnd_at(w, A0, chi, SS, 'T', tr, sc, d32, s1)
    zfin, zord, klr = common(w, A0, chi, tr, 'T')
    Aq = '( %s /\\ q e. %s )' % (A0, ZD())
    tq = w.s([al], 'r19.21bi', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (Aq, RQ(SS), RQ(SS)))
    SRe = 'sum_ q e. %s %s' % (ZD(), RQ(SS))
    tqr = w.s([tq], 'simpld', '( %s -> %s e. RR )' % (Aq, RQ(SS)))
    g0 = s([zfin, tqr, w.s([tq], 'simprd', '( %s -> 0 <_ %s )' % (Aq, RQ(SS)))], 'fsumge0', '0 <_ %s' % SRe)
    sre = s([zfin, tqr], 'fsumrecl', '%s e. RR' % SRe)
    le2 = linarith(w, A0, [g0], '( %s - %s ) <_ %s' % (KL(), SRe, KL()), closure=Closure(w, A0, {KL(): ('RR', klr), SRe: ('RR', sre)}))
    LM = '( Re ` %s )' % LAM(SS)
    lmx = xr_of_le(w, A0, bd, LM, '( %s - %s )' % (KL(), SRe))
    w.qed([lmx, s([s([klr, sre], 'resubcld', '( %s - %s ) e. RR' % (KL(), SRe))], 'rexrd', '( %s - %s ) e. RR*' % (KL(), SRe)), s([klr], 'rexrd', '%s e. RR*' % KL()), bd, le2], 'xrletrd', S['cenrele'])
    return run(w)


if __name__ == '__main__':
    gen_rele()


def gen_relz():
    w = W('cenrelz', 'Lean Census ` re_neg_logDeriv_le_of_zero ` , restated at the point ` ( 1 + 3 D ) + i Im R ` (Lean ` 1 + 2 delta ` ): a zero ` R ` of ` L ( s , chi ) ` with ` 1 - D <_ Re R <_ 1 ` gives ` Re ( -L\'/L ) <_ 17500000 log ( N ( abs Im R + 2 ) ) - 1 / ( 4 D ) ` (the ` 3 D ` point keeps ` no_thirteen_bad ` true at ZC1 ~ vmsharp ' "'" 's ` ( 5 / 4 ) / u + 5 ` : CEN1-blueprint section 3).')
    A0, C0 = split_imp(S['cenrelz'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    H2 = top_and(A0)[1]
    h2 = s([], 'simpr', H2)
    DH, RH = top_and(H2)
    dh = s([h2], 'simpld', DH); rh = s([h2], 'simprd', RH)
    dp = s([dh], 'simpld', 'D e. RR+'); d40 = s([dh], 'simprd', 'D <_ ( 1 / ; 4 0 )'); dr = s([dp], 'rpred', 'D e. RR'); d0 = s([dp], 'rpgt0d', '0 < D')
    RB = top_and(RH)[2]
    rc = s([rh], 'simp1d', 'R e. CC'); rz = s([rh], 'simp2d', '( %s ` R ) = 0' % LFN); rb = s([rh], 'simp3d', RB)
    r1 = s([rb], 'simpld', '( 1 - D ) <_ ( Re ` R )'); r2 = s([rb], 'simprd', '( Re ` R ) <_ 1')
    Te = '( Im ` R )'; tr = s([rc], 'imcld', '%s e. RR' % Te); rr = s([rc], 'recld', '( Re ` R ) e. RR')
    Ae = '( 3 x. D )'
    c = Closure(w, A0, {'D': ('RR', dr), '( Re ` R )': ('RR', rr), Te: ('RR', tr)}); c.atom('( Re ` R )'); c.atom(Te)
    ar = c.mem(Ae, 'RR')
    ap = linarith(w, A0, [d0], '0 < %s' % Ae, closure=c)
    a12 = linarith(w, A0, [d40], '%s <_ ( 1 / 2 )' % Ae, closure=c)
    SS, sc, d32, s1, rs = point(w, A0, Ae, ar, ap, a12, Te, tr)
    bd, al, b1, b2 = lnd_at(w, A0, chi, SS, Te, tr, sc, d32, s1)
    zfin, zord, klr = common(w, A0, chi, tr, Te)
    # R lies in ZD ( Im R )
    cd = Closure(w, A0, {'( Re ` R )': ('CC', s([rr], 'recnd', '( Re ` R ) e. CC')), Te: ('CC', s([tr], 'recnd', '%s e. CC' % Te)), 'D': ('CC', s([dr], 'recnd', 'D e. CC'))})
    cd.atom('( Re ` R )'); cd.atom(Te)
    cd.leaf('_i', 'CC', icc(w, A0)); cd.atom('_i')
    RP = '( ( Re ` R ) + ( _i x. %s ) )' % Te
    rp = s([rc, w.inst('replim')], 'syl', 'R = %s' % RP)
    ONE = '( 1 + ( _i x. %s ) )' % Te
    o1 = s([rp], 'oveq1d', '( R - %s ) = ( %s - %s )' % (ONE, RP, ONE))
    o2 = ringeq(w, A0, '( %s - %s )' % (RP, ONE), '( ( Re ` R ) - 1 )', cd)
    o3 = s([o1, o2], 'eqtrd', '( R - %s ) = ( ( Re ` R ) - 1 )' % ONE)
    ab = s([s([o3], 'fveq2d', '( abs ` ( R - %s ) ) = ( abs ` ( ( Re ` R ) - 1 ) )' % ONE), s([rr, s([], '1red', '1 e. RR'), r2], 'abssuble0d', '( abs ` ( ( Re ` R ) - 1 ) ) = ( 1 - ( Re ` R ) )')],
           'eqtrd', '( abs ` ( R - %s ) ) = ( 1 - ( Re ` R ) )' % ONE)
    abd = s([ab, linarith(w, A0, [r1], '( 1 - ( Re ` R ) ) <_ D', closure=c)], 'eqbrtrd', '( abs ` ( R - %s ) ) <_ D' % ONE)
    MZ = tsub(stmt('kdmemzd'), {'T': Te, 'Q': 'R', 'W': 'D'})
    mza, mzc = split_imp(MZ)
    M1, M2, M3 = top_and(mza)
    d12 = linarith(w, A0, [d40], 'D <_ ( 1 / 2 )', closure=c)
    rin = s([s([chi, tr], 'jca', M1), s([rc, rz], 'jca', M2), s([dr, d12, abd], '3jca', M3), w.inst('kdmemzd')], 'syl3anc', mzc)
    ZDR = ZD(Te)
    assert mzc == 'R e. %s' % ZDR, mzc[-200:]
    # the order at R
    MQ = MU('q'); MR = MU('R')
    ordc = w.s([w.s([], 'oveq2', '( q = R -> %s = %s )' % (MQ, MR))], 'eleq1d', '( q = R -> ( %s e. NN <-> %s e. NN ) )' % (MQ, MR))
    mn = s([rin, zord, w.s([ordc], 'rspcv', '( R e. %s -> ( A. q e. %s %s e. NN -> %s e. NN ) )' % (ZDR, ZDR, MQ, MR))], 'sylc', '%s e. NN' % MR)
    mr = s([mn], 'nnred', '%s e. RR' % MR); m1 = s([mn], 'nnge1d', '1 <_ %s' % MR)
    # S - R = x real
    XX = '( ( 1 + %s ) - ( Re ` R ) )' % Ae
    e1 = s([rp], 'oveq2d', '( %s - R ) = ( %s - %s )' % (SS, SS, RP))
    e2 = ringeq(w, A0, '( %s - %s )' % (SS, RP), XX, cd)
    sx = s([e1, e2], 'eqtrd', '( %s - R ) = %s' % (SS, XX))
    xr = c.mem(XX, 'RR')
    c.leaf(MR, 'RR', mr); c.atom(MR)
    x0 = linarith(w, A0, [r2, d0], '0 < %s' % XX, closure=c)
    x4 = linarith(w, A0, [r1], '%s <_ ( 4 x. D )' % XX, closure=c)
    xp = s([xr, x0], 'elrpd', '%s e. RR+' % XX)
    d4p = s([c.mem('( 4 x. D )', 'RR'), linarith(w, A0, [d0], '0 < ( 4 x. D )', closure=c)], 'elrpd', '( 4 x. D ) e. RR+')
    MX = '( %s / %s )' % (MR, XX)
    mxr = s([mr, xr, s([xp], 'rpne0d', '%s =/= 0' % XX)], 'redivcld', '%s e. RR' % MX)
    rq = s([s([s([sx], 'oveq2d', '( %s / ( %s - R ) ) = %s' % (MR, SS, MX))], 'fveq2d', '%s = ( Re ` %s )' % (RQ(SS, 'R'), MX)), s([mxr], 'rered', '( Re ` %s ) = %s' % (MX, MX))],
           'eqtrd', '%s = %s' % (RQ(SS, 'R'), MX))
    l1 = s([x4, s([xp, d4p], 'lerecd', '( %s <_ ( 4 x. D ) <-> ( 1 / ( 4 x. D ) ) <_ ( 1 / %s ) )' % (XX, XX))], 'mpbid', '( 1 / ( 4 x. D ) ) <_ ( 1 / %s )' % XX)
    l2 = s([s([], '1red', '1 e. RR'), mr, xp, m1], 'lediv1dd', '( 1 / %s ) <_ %s' % (XX, MX))
    # single term <_ sum
    Aq = '( %s /\\ q e. %s )' % (A0, ZDR)
    tq = w.s([al], 'r19.21bi', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (Aq, RQ(SS), RQ(SS)))
    tqr = w.s([tq], 'simpld', '( %s -> %s e. RR )' % (Aq, RQ(SS))); tq0 = w.s([tq], 'simprd', '( %s -> 0 <_ %s )' % (Aq, RQ(SS)))
    q1 = w.s([], 'oveq2', '( q = R -> %s = %s )' % (MQ, MR))
    q2 = w.s([], 'oveq2', '( q = R -> ( %s - q ) = ( %s - R ) )' % (SS, SS))
    q3 = w.s([q1, q2], 'oveq12d', '( q = R -> ( %s / ( %s - q ) ) = ( %s / ( %s - R ) ) )' % (MQ, SS, MR, SS))
    q4 = w.s([q3], 'fveq2d', '( q = R -> %s = %s )' % (RQ(SS), RQ(SS, 'R')))
    SRe = 'sum_ q e. %s %s' % (ZDR, RQ(SS))
    ge1 = s([zfin, tqr, tq0, q4, rin], 'fsumge1', '%s <_ %s' % (RQ(SS, 'R'), SRe))
    sre = s([zfin, tqr], 'fsumrecl', '%s e. RR' % SRe)
    IX = '( 1 / %s )' % XX; I4 = '( 1 / ( 4 x. D ) )'
    cf = Closure(w, A0, {KL(Te): ('RR', klr), SRe: ('RR', sre), RQ(SS, 'R'): ('RR', s([rq, mxr], 'eqeltrd', '%s e. RR' % RQ(SS, 'R'))), MX: ('RR', mxr),
                         IX: ('RR', s([xp], 'rprecred', '%s e. RR' % IX)), I4: ('RR', s([d4p], 'rprecred', '%s e. RR' % I4))})
    for k_ in (KL(Te), SRe, RQ(SS, 'R'), MX, IX, I4):
        cf.atom(k_)
    le2 = linarith(w, A0, [ge1, rq, l1, l2], '( %s - %s ) <_ ( %s - %s )' % (KL(Te), SRe, KL(Te), I4), closure=cf)
    LM = '( Re ` %s )' % LAM(SS)
    lmx = xr_of_le(w, A0, bd, LM, '( %s - %s )' % (KL(Te), SRe))
    w.qed([lmx, s([cf.mem('( %s - %s )' % (KL(Te), SRe), 'RR')], 'rexrd', '( %s - %s ) e. RR*' % (KL(Te), SRe)), s([cf.mem('( %s - %s )' % (KL(Te), I4), 'RR')], 'rexrd', '( %s - %s ) e. RR*' % (KL(Te), I4)), bd, le2],
          'xrletrd', S['cenrelz'])
    return run(w)


if __name__ == '__main__':
    gen_relz()
