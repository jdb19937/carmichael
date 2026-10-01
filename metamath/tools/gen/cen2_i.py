"""Sortie CEN2: the Z7 contract (cen2cc = census_contract) and its consumption form (cen2bad = card_badConductors_le)."""
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


def c_(w, ctx):
    return lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (ctx, f))


def gen_cc():
    w = W('cen2cc', 'THE Z7 CONTRACT: for ` 39 / 40 <_ S <_ 1 ` , ` 1 <_ V ` , ` 2 <_ Z ` the census up to ` Z ` is at most ` 10 ^ ( 10 ^ 10 ) ( V + 2 ) Z ^ ( 10 ^ 13 ( 1 - S ) ) ` , conditional on the middle-regime hypothesis (Lean Census ` census_contract ` ; constants ` censusC2 = 10 ^ ( 10 ^ 10 ) ( nu + 2 ) ` , ` censusC3 = 10 ^ 13 ` , threshold ` 10 ^ -10 ` , NUMERALS.md).')
    A0, C0 = split_imp(S['cen2cc'])
    s = c_(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    mch = g(MCH)
    sr = g('S e. RR'); vr = g('V e. RR'); zr = g('Z e. RR'); s39 = g('%s <_ S' % F3940); s1 = g('S <_ 1'); v1 = g('1 <_ V'); z2 = g('2 <_ Z')
    typ = g(TYP); rng = g(RNG)
    K = '( |_ ` Z )'
    kz = s([zr], 'flcld', '%s e. ZZ' % K)
    k2 = s([z2, s([zr, s([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), w.inst('flge')], 'syl2anc', '( 2 <_ Z <-> 2 <_ %s )' % K)], 'mpbid', '2 <_ %s' % K)
    kle = s([zr, w.inst('flle')], 'syl', '%s <_ Z' % K)
    c0 = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'Z': ('RR', zr), K: ('ZZ', kz)})
    E_ = '( %s x. ( 1 - S ) )' % C3
    ZE = '( Z ^c %s )' % E_
    e0 = linarith(w, A0, [s1], '0 <_ %s' % E_, closure=c0)
    z1 = linarith(w, A0, [z2], '1 <_ Z', closure=c0)
    ze1 = s([s([zr, z1], 'jca', '( Z e. RR /\\ 1 <_ Z )'), s([c0.mem('0', 'RR'), c0.mem(E_, 'RR')], 'jca', '( 0 e. RR /\\ %s e. RR )' % E_), e0, w.inst('cxplea')], 'syl3anc',
            '( Z ^c 0 ) <_ %s' % ZE)
    ze1 = s([s([c0.mem('Z', 'CC')], 'cxp0d', '( Z ^c 0 ) = 1'), ze1], 'eqbrtrrd', '1 <_ %s' % ZE)
    zp = linarith(w, A0, [z2], '0 < Z', closure=c0); c0.have('Z', 'gt0', zp)
    vp = linarith(w, A0, [v1], '0 < ( V + 2 )', closure=c0); c0.have('( V + 2 )', 'gt0', vp)
    zer = s([zr, c0.mem(E_, 'RR')], 'recxpcld', '%s e. RR' % ZE)
    c0.have(ZE, 'RR', zer); c0.atom(ZE)
    TEN10 = '( %s ^ %s )' % (TEN, TEN)
    P10 = '( %s ^ %s )' % (TEN, TEN10)
    t10n = w.s([w.s([], '10nn', '%s e. NN' % TEN), w.s([w.s([], '10nn', '%s e. NN' % TEN)], 'nnnn0i', '%s e. NN0' % TEN), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % TEN10)
    t10u = w.s([w.s([], '10re', '%s e. RR' % TEN), w.s([], '1le10', '1 <_ %s' % TEN) if False else w.s([w.s([], '1re', '1 e. RR'), w.s([], '10re', '%s e. RR' % TEN), w.s([], '1lt10', '1 < %s' % TEN)], 'ltleii', '1 <_ %s' % TEN)], 'id', 'x') if False else None
    one10 = w.s([w.s([], '1re', '1 e. RR'), w.s([], '10re', '%s e. RR' % TEN), w.s([], '1lt10', '1 < %s' % TEN)], 'ltleii', '1 <_ %s' % TEN)
    # 2 <_ 10 ^ 10 via 10 ^ 1 <_ 10 ^ 10
    u1 = w.s([w.s([], '10nn', '%s e. NN' % TEN), w.inst('nnuz')], 'eleqtri', '%s e. ( ZZ>= ` 1 )' % TEN) if False else None
    t1 = w.s([w.s([w.s([], '1z', '1 e. ZZ'), w.s([w.s([], '10nn', '%s e. NN' % TEN)], 'nnzi', '%s e. ZZ' % TEN), w.s([w.s([], '1re', '1 e. RR'), w.s([], '10re', '%s e. RR' % TEN), w.s([], '1lt10', '1 < %s' % TEN)], 'ltleii', '1 <_ %s' % TEN)], '3pm3.2i',
                    '( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s )' % (TEN, TEN)), w.s([], 'eluz2', '( %s e. ( ZZ>= ` 1 ) <-> ( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s ) )' % (TEN, TEN, TEN))], 'mpbir',
             '%s e. ( ZZ>= ` 1 )' % TEN)
    le1 = w.s([w.s([], '10re', '%s e. RR' % TEN), one10, t1, w.inst('leexp2a')], 'mp3an', '( %s ^ 1 ) <_ %s' % (TEN, TEN10))
    e1 = w.s([w.s([w.s([], '10re', '%s e. RR' % TEN)], 'recni', '%s e. CC' % TEN), w.inst('exp1')], 'ax-mp', '( %s ^ 1 ) = %s' % (TEN, TEN))
    le2 = w.s([e1, le1], 'eqbrtrri', '%s <_ %s' % (TEN, TEN10))
    t10r = w.s([t10n], 'nnrei', '%s e. RR' % TEN10)
    lt_ = w.s([w.s([], '2re', '2 e. RR'), w.s([], '10re', '%s e. RR' % TEN), t10r], 'letri', '( ( 2 <_ %s /\\ %s <_ %s ) -> 2 <_ %s )' % (TEN, TEN, TEN10, TEN10))
    two10 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], '10re', '%s e. RR' % TEN), w.s([], '2lt10', '2 < %s' % TEN)], 'ltleii', '2 <_ %s' % TEN), le2, lt_], 'mp2an', '2 <_ %s' % TEN10)
    t2u = w.s([w.s([w.s([], '2z', '2 e. ZZ'), w.s([t10n], 'nnzi', '%s e. ZZ' % TEN10), two10], '3pm3.2i', '( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s )' % (TEN10, TEN10)),
               w.s([], 'eluz2', '( %s e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s ) )' % (TEN10, TEN10, TEN10))], 'mpbir', '%s e. ( ZZ>= ` 2 )' % TEN10)
    lp = w.s([w.s([], '10re', '%s e. RR' % TEN), one10, t2u, w.inst('leexp2a')], 'mp3an', '( %s ^ 2 ) <_ %s' % (TEN, P10))
    p100 = w.s([w.s([], 'sq10', '( %s ^ 2 ) = ; ; 1 0 0' % TEN), lp], 'eqbrtrri', '; ; 1 0 0 <_ %s' % P10)
    p10r = w.s([w.s([], '10re', '%s e. RR' % TEN), w.s([w.s([t10n], 'nnnn0i', '%s e. NN0' % TEN10)], 'id', '%s e. NN0' % TEN10) if False else w.s([t10n], 'nnnn0i', '%s e. NN0' % TEN10), w.inst('reexpcl')],
               'mp2an', '%s e. RR' % P10)
    c0.have(P10, 'RR', s([p10r], 'a1i', '%s e. RR' % P10)); c0.atom(P10)
    C2V = C2('V')
    BNDT = BND('S', 'V', 'Z')
    b13 = nlinarith(w, A0, [s([p100], 'a1i', '; ; 1 0 0 <_ %s' % P10), v1, ze1], '%s <_ %s' % (N13, BNDT), closure=c0, atoms=[P10, ZE])
    CN = CNT('S', 'V', K)
    LL_ = LOGZ('Z', 'V')
    SM = '( ( 1 - S ) x. %s ) <_ %s' % (LL_, THR)
    # small regime
    A1 = '( %s /\\ %s )' % (A0, SM)
    a1 = c_(w, A1)
    sm = a1([lift(w, typ, A1), lift(w, rng, A1), a1([], 'simpr', SM), w.inst('cen2small')], 'syl3anc', '%s <_ %s' % (CN, N13))
    cnr = s([s([s([k2], 'id', 'x') if False else s([kz, linarith(w, A0, [k2], '0 <_ %s' % K, closure=c0)], 'jca', '( %s e. ZZ /\\ 0 <_ %s )' % (K, K)),
                 w.s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (K, K, K))], 'sylibr', '%s e. NN0' % K), w.inst('cen2sq')], 'syl', '%s <_ ( %s x. %s )' % (CN, K, K))
    kn0 = s([s([kz, linarith(w, A0, [k2], '0 <_ %s' % K, closure=c0)], 'jca', '( %s e. ZZ /\\ 0 <_ %s )' % (K, K)),
             w.s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (K, K, K))], 'sylibr', '%s e. NN0' % K)
    PZ = 'Z e. RR'
    fin_ = w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (PZ, K))
    A0m = '( %s /\\ m e. ( 1 ... %s ) )' % (PZ, K)
    am = c_(w, A0m)
    Bm = BC('S', 'V', 'm')
    bmr = am([am([am([am([am([], 'simpr', 'm e. ( 1 ... %s )' % K), w.inst('elfznn')], 'syl', 'm e. NN'), w.inst('cen2bcf')], 'syl', '( %s e. Fin /\\ ( # ` %s ) <_ m )' % (Bm, Bm))], 'simpld', '%s e. Fin' % Bm),
               w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % Bm)
    cnz = w.s([fin_, am([bmr], 'nn0red', '( # ` %s ) e. RR' % Bm)], 'fsumrecl', '( %s -> %s e. RR )' % (PZ, CN))
    cnr_ = s([zr, cnz], 'syl', '%s e. RR' % CN)
    c0.have(CN, 'RR', cnr_); c0.atom(CN)
    g1 = a1([sm, lift(w, b13, A1)], 'letrd', 'x') if False else linarith(w, A1, [sm, lift(w, b13, A1)], '%s <_ %s' % (CN, BNDT), closure=Closure(w, A1, {CN: ('RR', lift(w, cnr_, A1)), BNDT: ('RR', lift(w, c0.mem(BNDT, 'RR'), A1))}))
    # not small
    A2 = '( %s /\\ -. %s )' % (A0, SM)
    a2 = c_(w, A2)
    gt = a2([a2([], 'simpr', '-. %s' % SM), a2([lift(w, c0.mem(THR, 'RR'), A2), lift(w, c0.mem('( ( 1 - S ) x. %s )' % LL_, 'RR'), A2)], 'ltnled',
                                           '( %s < ( ( 1 - S ) x. %s ) <-> -. %s )' % (THR, LL_, SM))], 'mpbird', '%s < ( ( 1 - S ) x. %s )' % (THR, LL_))
    TR = '( 2 / %s ) <_ ( 1 - S )' % C3
    A21 = '( %s /\\ %s )' % (A2, TR)
    a21 = c_(w, A21)
    cA = Closure(w, A21, {'S': ('RR', lift(w, sr, A21)), 'V': ('RR', lift(w, vr, A21)), 'Z': ('RR', lift(w, zr, A21)), K: ('ZZ', lift(w, kz, A21))})
    cA.have('Z', 'gt0', lift(w, zp, A21))
    kk = a21([cA.mem(K, 'RR'), lift(w, zr, A21), cA.mem(K, 'RR'), lift(w, zr, A21), lift(w, linarith(w, A0, [k2], '0 <_ %s' % K, closure=c0), A21),
              lift(w, linarith(w, A0, [k2], '0 <_ %s' % K, closure=c0), A21), lift(w, kle, A21), lift(w, kle, A21)], 'lemul12ad', '( %s x. %s ) <_ ( Z x. Z )' % (K, K))
    zz = a21([a21([cA.mem('Z', 'CC'), cA.ne0('Z'), a21([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'cxpexpzd', '( Z ^c 2 ) = ( Z ^ 2 )'),
              a21([cA.mem('Z', 'CC')], 'sqvald', '( Z ^ 2 ) = ( Z x. Z )')], 'eqtrd', '( Z ^c 2 ) = ( Z x. Z )')
    Q2 = '( 2 / %s )' % C3
    c3r = cA.mem(C3, 'RR')
    q2r = a21([cA.mem('2', 'RR'), c3r, cA.ne0(C3)], 'redivcld', '%s e. RR' % Q2)
    m1 = a21([q2r, cA.mem('( 1 - S )', 'RR'), c3r, cA.ge0(C3), a21([], 'simpr', TR)], 'lemul2ad', '( %s x. %s ) <_ %s' % (C3, Q2, E_))
    dcn = a21([cA.mem('2', 'CC'), cA.mem(C3, 'CC'), cA.ne0(C3)], 'divcan2d', '( %s x. %s ) = 2' % (C3, Q2))
    e2 = a21([dcn, m1], 'eqbrtrrd', '2 <_ %s' % E_)
    zc2 = a21([a21([lift(w, zr, A21), lift(w, z1, A21)], 'jca', '( Z e. RR /\\ 1 <_ Z )'), a21([cA.mem('2', 'RR'), cA.mem(E_, 'RR')], 'jca', '( 2 e. RR /\\ %s e. RR )' % E_), e2,
               w.inst('cxplea')], 'syl3anc', '( Z ^c 2 ) <_ %s' % ZE)
    for at_ in (CN, ZE, P10, '( Z ^c 2 )', '( %s x. %s )' % (K, K), '( Z x. Z )'):
        cA.atom(at_)
    cA.have(CN, 'RR', lift(w, cnr_, A21)); cA.have(ZE, 'RR', lift(w, zer, A21)); cA.have(P10, 'RR', lift(w, s([p10r], 'a1i', '%s e. RR' % P10), A21))
    cA.have('( Z ^c 2 )', 'RR', a21([lift(w, zr, A21), cA.mem('2', 'RR')], 'recxpcld', '( Z ^c 2 ) e. RR'))
    cA.have('( %s x. %s )' % (K, K), 'RR', cA.mem('( %s x. %s )' % (K, K), 'RR')) if False else None
    zeb = nlinarith(w, A21, [lift(w, b13, A21), lift(w, ze1, A21), lift(w, s([p100], 'a1i', '; ; 1 0 0 <_ %s' % P10), A21), lift(w, v1, A21)], '%s <_ %s' % (ZE, BNDT), closure=cA, atoms=[P10, ZE])
    g21 = linarith(w, A21, [lift(w, cnr, A21), kk, zz, zc2, zeb], '%s <_ %s' % (CN, BNDT), closure=cA, atoms=['( %s x. %s )' % (K, K), '( Z x. Z )'])
    # middle
    A22 = '( %s /\\ -. %s )' % (A2, TR)
    a22 = c_(w, A22)
    lt2 = a22([a22([], 'simpr', '-. %s' % TR), a22([lift(w, c0.mem('( 1 - S )', 'RR'), A22), a22([lift(w, c0.mem('2', 'RR'), A22), lift(w, c0.mem(C3, 'RR'), A22), lift(w, c0.ne0(C3), A22)], 'redivcld', '( 2 / %s ) e. RR' % C3)], 'ltnled',
                                              '( ( 1 - S ) < ( 2 / %s ) <-> -. %s )' % (C3, TR))], 'mpbird', '( 1 - S ) < ( 2 / %s )' % C3)
    body_uvw = MCH.split(' A. w e. RR ', 1)[1]
    assert MCH.startswith('A. u e. RR A. v e. RR A. w e. RR ')
    eu = 'u = S'; ev = 'v = V'; ew = 'w = Z'
    iu = w.s([], 'id', '( %s -> %s )' % (eu, eu)); iv = w.s([], 'id', '( %s -> %s )' % (ev, ev)); iw = w.s([], 'id', '( %s -> %s )' % (ew, ew))
    su, b1_ = w.wcongr(body_uvw, {'u': 'S'}, eu, {'u': iu})
    sv, b2_ = w.wcongr(b1_, {'v': 'V'}, ev, {'v': iv})
    sw, b3_ = w.wcongr(b2_, {'w': 'Z'}, ew, {'w': iw})
    r3 = w.s([su, sv, sw], 'rspc3v', '( ( S e. RR /\\ V e. RR /\\ Z e. RR ) -> ( %s -> %s ) )' % (MCH, b3_))
    inst = s([typ, mch, r3], 'sylc', b3_)
    hyp_, con_ = split_imp(b3_)
    hh = a22([lift(w, s([s1], 'id', 'x'), A22) if False else a22([lift(w, s39, A22), lift(w, s1, A22)], 'jca', '( %s <_ S /\\ S <_ 1 )' % F3940),
              a22([lift(w, v1, A22), lift(w, z2, A22)], 'jca', '( 1 <_ V /\\ 2 <_ Z )'), a22([lt2, lift(w, gt, A22)], 'jca', top_and(hyp_)[2])], '3jca', hyp_)
    g22 = a22([hh, lift(w, inst, A22)], 'mpd', con_)
    g2 = w.s([a21 and w.s([g21], 'id', '( %s -> %s <_ %s )' % (A21, CN, BNDT)) if False else g21, g22], 'pm2.61dan', '( %s -> %s <_ %s )' % (A2, CN, BNDT))
    w.qed([g1, g2], 'pm2.61dan', S['cen2cc'])
    return run(w)


def gen_bad():
    w = W('cen2bad', 'The consumption form of the Z7 contract: a finite set of conductors in ` [ 2 , Z ] ` , each carrying a bad primitive character, has at most ` 10 ^ ( 10 ^ 10 ) ( V + 2 ) Z ^ ( 10 ^ 13 ( 1 - S ) ) ` elements (Lean Census ` card_badConductors_le ` ).')
    A0, C0 = split_imp(S['cen2bad'])
    s = c_(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    mch = g(MCH); typ = g(TYP); rng = g(RNG)
    sr = g('S e. RR'); vr = g('V e. RR'); zr = g('Z e. RR'); dfin = g('D e. Fin')
    ALLM = [f for f in F if f.startswith('A. m e. D ')][0]
    alm = F[ALLM]
    K = '( |_ ` Z )'
    kz = s([zr], 'flcld', '%s e. ZZ' % K)
    CN = CNT('S', 'V', K)
    BNDT = BND('S', 'V', 'Z')
    cc = s([mch, s([typ, rng], 'jca', '( %s /\\ %s )' % (TYP, RNG)), w.inst('cen2cc')], 'syl2anc', '%s <_ %s' % (CN, BNDT))
    Bm = BC('S', 'V', 'm'); Bd = BC('S', 'V', 'd')
    eqmd = 'm = d'
    idmd = w.s([], 'id', '( %s -> %s )' % (eqmd, eqmd))
    stmd, bd_ = w.congr('( # ` %s )' % Bm, {'m': 'd'}, eqmd, {'m': idmd})
    assert bd_ == '( # ` %s )' % Bd, bd_
    CND = 'sum_ d e. ( 1 ... %s ) ( # ` %s )' % (K, Bd)
    cbv = w.s([stmd], 'cbvsumv', '%s = %s' % (CN, CND))
    A1 = '( %s /\\ d e. D )' % A0
    a1 = c_(w, A1)
    dn_ = a1([], 'simpr', 'd e. D')
    BODYM = ALLM[len('A. m e. D '):]
    stb, bdy = w.wcongr(BODYM, {'m': 'd'}, eqmd, {'m': idmd})
    rs = w.s([stb], 'rspcv', '( d e. D -> ( %s -> %s ) )' % (ALLM, bdy))
    hd = a1([dn_, lift(w, alm, A1), rs], 'sylc', bdy)
    H = split_all(w, A1, bdy, hd)
    d0 = H['d e. NN0']; d2 = H['2 <_ d']; dz = H['d <_ Z']; dne = H['%s =/= (/)' % Bd]
    dzz = a1([d0], 'nn0zd', 'd e. ZZ')
    dnn = a1([a1([a1([a1([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), dzz, d2], '3jca', '( 2 e. ZZ /\\ d e. ZZ /\\ 2 <_ d )'),
                  w.s([], 'eluz2', '( d e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ d e. ZZ /\\ 2 <_ d ) )')], 'sylibr', 'd e. ( ZZ>= ` 2 )'), w.inst('eluz2nn')], 'syl', 'd e. NN')
    bf = a1([dnn, w.inst('cen2bcf')], 'syl', '( %s e. Fin /\\ ( # ` %s ) <_ d )' % (Bd, Bd))
    bfi = a1([bf], 'simpld', '%s e. Fin' % Bd)
    hn = a1([dne, a1([bfi, w.inst('hashnncl')], 'syl', '( ( # ` %s ) e. NN <-> %s =/= (/) )' % (Bd, Bd))], 'mpbird', '( # ` %s ) e. NN' % Bd)
    h1 = a1([hn], 'nnge1d', '1 <_ ( # ` %s )' % Bd)
    hr = a1([hn], 'nnred', '( # ` %s ) e. RR' % Bd)
    dk = a1([dz, a1([lift(w, zr, A1), dzz, w.inst('flge')], 'syl2anc', '( d <_ Z <-> d <_ %s )' % K)], 'mpbid', 'd <_ %s' % K)
    c1 = Closure(w, A1, {'d': ('ZZ', dzz)})
    d1 = linarith(w, A1, [d2], '1 <_ d', closure=c1)
    dfz = a1([a1([d1, dk], 'jca', '( 1 <_ d /\\ d <_ %s )' % K), a1([dzz, a1([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), lift(w, kz, A1), w.inst('elfz')], 'syl3anc',
                                                                     '( d e. ( 1 ... %s ) <-> ( 1 <_ d /\\ d <_ %s ) )' % (K, K))], 'mpbird', 'd e. ( 1 ... %s )' % K)
    ss = w.s([w.s([dfz], 'ex', '( %s -> ( d e. D -> d e. ( 1 ... %s ) ) )' % (A0, K))], 'ssrdv', '( %s -> D C_ ( 1 ... %s ) )' % (A0, K))
    le1 = s([dfin, a1([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), hr, h1], 'fsumle', 'sum_ d e. D 1 <_ sum_ d e. D ( # ` %s )' % Bd)
    fc = s([dfin, s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ d e. D 1 = ( ( # ` D ) x. 1 )')
    hdr = s([s([dfin, w.inst('hashcl')], 'syl', '( # ` D ) e. NN0')], 'nn0cnd', '( # ` D ) e. CC')
    fc2 = s([fc, s([hdr], 'mulridd', '( ( # ` D ) x. 1 ) = ( # ` D )')], 'eqtrd', 'sum_ d e. D 1 = ( # ` D )')
    A2 = '( %s /\\ d e. ( 1 ... %s ) )' % (A0, K)
    a2 = c_(w, A2)
    dn2 = a2([a2([], 'simpr', 'd e. ( 1 ... %s )' % K), w.inst('elfznn')], 'syl', 'd e. NN')
    b2 = a2([a2([a2([dn2, w.inst('cen2bcf')], 'syl', '( %s e. Fin /\\ ( # ` %s ) <_ d )' % (Bd, Bd))], 'simpld', '%s e. Fin' % Bd), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % Bd)
    fz = s([], 'fzfid', '( 1 ... %s ) e. Fin' % K)
    le2 = s([fz, a2([b2], 'nn0red', '( # ` %s ) e. RR' % Bd), a2([b2], 'nn0ge0d', '0 <_ ( # ` %s )' % Bd), ss], 'fsumless', 'sum_ d e. D ( # ` %s ) <_ %s' % (Bd, CND))
    cb = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'Z': ('RR', zr)})
    cb.have('Z', 'gt0', linarith(w, A0, [g('2 <_ Z')], '0 < Z', closure=cb))
    bndr = cb.mem(BNDT, 'RR')
    c0 = Closure(w, A0, {})
    c0.have(BNDT, 'RR', bndr)
    SD1 = 'sum_ d e. D 1'; SDB = 'sum_ d e. D ( # ` %s )' % Bd
    for at_ in (SD1, SDB, CND, CN, BNDT, '( # ` D )'):
        c0.atom(at_)
    c0.have('( # ` D )', 'RR', s([hdr], 'id', 'x') if False else s([s([dfin, w.inst('hashcl')], 'syl', '( # ` D ) e. NN0')], 'nn0red', '( # ` D ) e. RR'))
    c0.have(SDB, 'RR', s([dfin, hr], 'fsumrecl', '%s e. RR' % SDB))
    c0.have(CND, 'RR', s([fz, a2([b2], 'nn0red', '( # ` %s ) e. RR' % Bd)], 'fsumrecl', '%s e. RR' % CND))
    c0.have(SD1, 'RR', s([fc2, c0.mem('( # ` D )', 'RR')], 'eqeltrd', '%s e. RR' % SD1))
    c0.have(CN, 'RR', s([s([cbv], 'a1i', '%s = %s' % (CN, CND)), c0.mem(CND, 'RR')], 'eqeltrd', '%s e. RR' % CN))
    c0.have(BNDT, 'RR', s([s([], 'id', 'x') if False else cc], 'id', 'x') if False else None) if False else None
    w.qed([], 'id', 'x') if False else None
    fin = linarith(w, A0, [le1, fc2, le2, s([cbv], 'a1i', '%s = %s' % (CN, CND)), cc], '( # ` D ) <_ %s' % BNDT, closure=c0, name='qed')
    return run(w)


if __name__ == '__main__':
    gen_cc()
    gen_bad()
