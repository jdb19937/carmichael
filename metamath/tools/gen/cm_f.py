"""Sortie CM: the family bound (cmfam).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_f.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *
from lin import linarith, nlinarith, lineq

only = sys.argv[1:]


def gen_fam():
    from mvlib import ringeq
    w = W('cmfam', 'THE FAMILY BOUND: with ` R ` the number of bad characters of conductor ` d e. ( 2 ... K ) ` , ` 2 D R log W <_ 750 e ^ 2 c ( log X2 ) ^ 2 ( log X2 - log X1 ) ` , ` c = E ^ 3 M exp ( 6 M ) ` : the detection window of every bad character ( ~ cmdet ) swapped into ` du / u ` ( ~ cmswp ) against the sieve at each ` u ` ( ~ cmsvu ) (Lean ` family_bound ` ).')
    A0, C0 = split_imp(S['cmfam'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    sr = g('S e. RR'); vr = g('V e. RR'); wr = g('W e. RR'); s0 = g('0 < S'); s1 = g('S <_ 1'); v1 = g('1 <_ V'); w2 = g('2 <_ W')
    kz = g('K e. ZZ'); kw = g('K <_ W'); v3 = g('( V + 3 ) <_ W')
    ep = g('E e. RR+'); e5 = g('E <_ %s' % R5000); e12 = g('1 <_ ( ( ; 1 2 x. E ) x. %s )' % LW)
    dp = g('D e. RR+'); d1 = g('D <_ 1'); dist = g('( ( ( 1 - S ) ^ 2 ) + ( D ^ 2 ) ) <_ ( E ^ 2 )'); w5 = g('( W ^ 5 ) <_ %s' % X1)
    c0 = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), 'W': ('RR', wr), 'K': ('ZZ', kz), 'E': ('RR+', ep), 'D': ('RR+', dp)})
    wp = linarith(w, A0, [w2], '0 < W', closure=c0); c0.have('W', 'gt0', wp)
    lwp = d('syl2anc', [wr, linarith(w, A0, [w2], '1 < W', closure=c0), w.inst('rplogcl')], '%s e. RR+' % LW)
    lwr = d('rpred', [lwp], '%s e. RR' % LW)
    lw0 = d('rpge0d', [lwp], '0 <_ %s' % LW)
    kx = d('syl3anc', [ep, lwr, lw0, w.inst('kdxlt')], '( %s e. NN /\\ %s < %s )' % (MW, X1, X2))
    mn = d('simpld', [kx], '%s e. NN' % MW); x12 = d('simprd', [kx], '%s < %s' % (X1, X2))
    c0.have(MW, 'NN', mn)
    er = d('rpred', [ep], 'E e. RR')
    E1 = '( %s / ( ; 1 6 x. E ) )' % MW; E2 = '( ( ; 1 6 x. %s ) / E )' % MW
    x1p = d('rpefcld', [c0.mem(E1, 'RR')], '%s e. RR+' % X1); x1r = d('rpred', [x1p], '%s e. RR' % X1)
    x2r = d('reefcld', [c0.mem(E2, 'RR')], '%s e. RR' % X2)
    x12l = d('ltled', [x1r, x2r, x12], '%s <_ %s' % (X1, X2))
    # exp 20 <_ X2
    kn = d('syl', [d('jca', [d('jca', [er, d('rpge0d', [ep], '0 <_ E')], '( E e. RR /\\ 0 <_ E )'), d('jca', [lwr, lw0], '( %s e. RR /\\ 0 <_ %s )' % (LW, LW))],
                   '( ( E e. RR /\\ 0 <_ E ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (LW, LW)), w.inst('kdndet')], inst('kdndet', {'L': LW})[1])
    ND = NDET('E', LW)
    n6 = d('simp2d' if False else 'id', [], 'x') if False else None
    from c9lib import top_and
    kparts = top_and(inst('kdndet', {'L': LW})[1])
    n6 = d('simp2d' if len(kparts) == 3 else 'id', [kn], '6 <_ %s' % ND) if len(kparts) == 3 else None
    if n6 is None:
        allp = split_all(w, A0, inst('kdndet', {'L': LW})[1], kn)
        n6 = allp['6 <_ %s' % ND]
    c0.have(ND, 'RR', c0.mem(ND, 'RR') if False else d('nnred', [d('syl', [kn, w.inst('simp1')], '%s e. NN' % ND) if False else split_all(w, A0, inst('kdndet', {'L': LW})[1], kn)['%s e. NN' % ND]], '%s e. RR' % ND))
    c0.atom(ND)
    m16 = linarith(w, A0, [n6, e5], '( ; 2 0 x. E ) <_ ( ; 1 6 x. %s )' % MW, closure=c0)
    l20 = d('mpbid', [m16, d('syl3anc', [c0.mem('; 2 0', 'RR'), c0.mem('( ; 1 6 x. %s )' % MW, 'RR'), d('jca', [er, d('rpgt0d', [ep], '0 < E')], '( E e. RR /\\ 0 < E )'), w.inst('lemuldiv')],
                                     '( ( ; 2 0 x. E ) <_ ( ; 1 6 x. %s ) <-> ; 2 0 <_ %s )' % (MW, E2))], '; 2 0 <_ %s' % E2)
    ez = d('mpbid', [l20, d('syl2anc', [c0.mem('; 2 0', 'RR'), c0.mem(E2, 'RR'), w.inst('efle')], '( ; 2 0 <_ %s <-> ( exp ` ; 2 0 ) <_ %s )' % (E2, X2))], '( exp ` ; 2 0 ) <_ %s' % X2)
    # per character
    DR = '( 2 ... K )'
    TT = '( -u %s (,) %s )' % (V1, V1)
    YZ = '( %s (,) %s )' % (X1, X2)
    Cd = '( %s /\\ d e. %s )' % (A0, DR)
    cd = mk(w, Cd)
    din = w.s([], 'simpr', '( %s -> d e. %s )' % (Cd, DR))
    dz = cd('syl', [din, w.inst('elfzelz')], 'd e. ZZ'); d2 = cd('syl', [din, w.inst('elfzle1')], '2 <_ d'); dk = cd('syl', [din, w.inst('elfzle2')], 'd <_ K')
    ccd = Closure(w, Cd, {'d': ('ZZ', dz), 'W': ('RR', lift(w, wr, Cd)), 'K': ('ZZ', lift(w, kz, Cd))})
    dnn = cd('mpbird', [cd('jca', [dz, linarith(w, Cd, [d2], '0 < d', closure=ccd)], '( d e. ZZ /\\ 0 < d )'), a1(w, Cd, 'elnnz', '( d e. NN <-> ( d e. ZZ /\\ 0 < d ) )')], 'd e. NN')
    dw = linarith(w, Cd, [dk, lift(w, kw, Cd)], 'd <_ W', closure=ccd)
    BCd = BC('S', 'V', 'd')
    bcf2 = cd('syl', [dnn, w.inst('cen2bcf')], '( %s e. Fin /\\ ( # ` %s ) <_ d )' % (BCd, BCd))
    bcf = cd('simpld', [bcf2], '%s e. Fin' % BCd)
    Cx = '( %s /\\ x e. %s )' % (Cd, BCd)
    cx = mk(w, Cx)
    L = lambda s_: lift(w, s_, Cx)
    DH = inst('cmdet', {'N': 'd', 'X': 'x'})
    dh = cx('jca', [cx('jca', [cx('jca', [L(dnn), L(d2)], '( d e. NN /\\ 2 <_ d )'), w.s([], 'simpr', '( %s -> x e. %s )' % (Cx, BCd))], '( ( d e. NN /\\ 2 <_ d ) /\\ x e. %s )' % BCd),
                              cx('3jca', [L(d('3jca', [sr, vr, wr], '( S e. RR /\\ V e. RR /\\ W e. RR )')), L(d('jca', [s0, s1], '( 0 < S /\\ S <_ 1 )')), cx('jca', [lift(w, dw, Cx), L(v3)], '( d <_ W /\\ ( V + 3 ) <_ W )')],
                                     '( ( S e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( 0 < S /\\ S <_ 1 ) /\\ ( d <_ W /\\ ( V + 3 ) <_ W ) )')],
                    '( ( ( d e. NN /\\ 2 <_ d ) /\\ x e. %s ) /\\ ( ( S e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( 0 < S /\\ S <_ 1 ) /\\ ( d <_ W /\\ ( V + 3 ) <_ W ) ) )' % BCd)
    dh2 = cx('3jca', [L(d('jca', [ep, e5], '( E e. RR+ /\\ E <_ %s )' % R5000)), L(e12), L(d('jca', [d('jca', [dp, d1], '( D e. RR+ /\\ D <_ 1 )'), dist], '( ( D e. RR+ /\\ D <_ 1 ) /\\ ( ( ( 1 - S ) ^ 2 ) + ( D ^ 2 ) ) <_ ( E ^ 2 ) )'))],
                 '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) /\\ ( ( D e. RR+ /\\ D <_ 1 ) /\\ ( ( ( 1 - S ) ^ 2 ) + ( D ^ 2 ) ) <_ ( E ^ 2 ) ) )' % (R5000, LW))
    det = cx('syl', [cx('jca', [dh, dh2], DH[0]), w.inst('cmdet')], DH[1])
    # x is a character mod d
    BODY = '( ( d DChrCond y ) = d /\\ %s =/= (/) )' % __import__('cen2lib').ZFB('S', 'V', 'd', 'y')
    xbase = cx('sseldd', [a1(w, Cx, 'ssrab2', '%s C_ %s' % (BCd, BASE('d'))), w.s([], 'simpr', '( %s -> x e. %s )' % (Cx, BCd))], 'x e. %s' % BASE('d'))
    SW = inst('cmswp', {'N': 'd', 'X': 'x', 'H': V1, 'Y': X1, 'Z': X2})
    sw = cx('syl3anc', [cx('jca', [L(dnn), xbase], '( d e. NN /\\ x e. %s )' % BASE('d')), L(c0.mem(V1, 'RR')), L(d('3jca', [x1p, x2r, x12l], '( %s e. RR+ /\\ %s e. RR /\\ %s <_ %s )' % (X1, X2, X1, X2))), w.inst('cmswp')], SW[1])
    IIx = II('t', X1, X2, 'd', 'x'); JJu = JJ(V1, X1, 'u', 'd', 'x')
    ITI = 'S. %s %s _d t' % (TT, IIx); IUJ = 'S. %s ( %s / u ) _d u' % (YZ, JJu)
    sweq = cx('simp3d', [sw], '%s = %s' % (ITI, IUJ))
    swib = cx('simp2d', [sw], '( u e. %s |-> ( %s / u ) ) e. L^1' % (YZ, JJu))
    CD = CDET
    per = cx('breqtrd', [det, cx('oveq2d', [sweq], '( %s x. %s ) = ( %s x. %s )' % (CD, ITI, CD, IUJ))], '( 2 x. D ) <_ ( %s x. %s )' % (CD, IUJ))
    # IUJ is real
    Cxu = '( %s /\\ u e. %s )' % (Cx, YZ)
    cxu = mk(w, Cxu)
    ug = cxu('mpbid', [w.s([], 'simpr', '( %s -> u e. %s )' % (Cxu, YZ)), cxu('syl2anc', [cxu('rexrd', [lift(w, x1r, Cxu)], '%s e. RR*' % X1), cxu('rexrd', [lift(w, x2r, Cxu)], '%s e. RR*' % X2), w.inst('elioo2')],
                                                                               '( u e. %s <-> ( u e. RR /\\ %s < u /\\ u < %s ) )' % (YZ, X1, X2))], '( u e. RR /\\ %s < u /\\ u < %s )' % (X1, X2))
    ur = cxu('simp1d', [ug], 'u e. RR')
    up = cxu('lttrd', [a1(w, Cxu, '0re', '0 e. RR'), lift(w, x1r, Cxu), ur, cxu('rpgt0d', [lift(w, x1p, Cxu)], '0 < %s' % X1), cxu('simp2d', [ug], '%s < u' % X1)], '0 < u')
    PWT = inst('cmpwt', {'N': 'd', 'X': 'x', 'H': V1, 'Y': X1, 'U': 'u'})
    pwt = cxu('syl3anc', [cxu('jca', [lift(w, dnn, Cxu), lift(w, xbase, Cxu)], '( d e. NN /\\ x e. %s )' % BASE('d')), lift(w, c0.mem(V1, 'RR'), Cxu), cxu('jca', [lift(w, x1r, Cxu), ur], '( %s e. RR /\\ u e. RR )' % X1), w.inst('cmpwt')], PWT[1])
    jr = cxu('simp2d', [pwt], '%s e. RR' % JJu); j0 = cxu('simp3d', [pwt], '0 <_ %s' % JJu)
    jur = cxu('redivcld', [jr, ur, cxu('gt0ne0d', [up], 'u =/= 0')], '( %s / u ) e. RR' % JJu)
    iujr = cx('itgrecl', [jur, swib], '%s e. RR' % IUJ)
    cr = lift(w, c0.mem(CD, 'RR'), Cx)
    # sums over x and d
    SXL = 'sum_ x e. %s ( 2 x. D )' % BCd
    SXR = 'sum_ x e. %s ( %s x. %s )' % (BCd, CD, IUJ)
    le_x = cd('fsumle', [bcf, lift(w, c0.mem('( 2 x. D )', 'RR'), Cx), cx('remulcld', [cr, iujr], '( %s x. %s ) e. RR' % (CD, IUJ)), per], '%s <_ %s' % (SXL, SXR))
    fc = cd('syl2anc', [bcf, lift(w, d('recnd', [c0.mem('( 2 x. D )', 'RR')], '( 2 x. D ) e. CC'), Cd), w.inst('fsumconst')], '%s = ( ( # ` %s ) x. ( 2 x. D ) )' % (SXL, BCd))
    SIX = 'sum_ x e. %s %s' % (BCd, IUJ)
    fm = cd('fsummulc2', [bcf, lift(w, d('recnd', [c0.mem(CD, 'RR')], '%s e. CC' % CD), Cd), cx('recnd', [iujr], '%s e. CC' % IUJ)], '( %s x. %s ) = %s' % (CD, SIX, SXR))
    le_x2 = cd('eqbrtrrd', [fc, cd('breqtrrd', [le_x, fm], '%s <_ ( %s x. %s )' % (SXL, CD, SIX))], '( ( # ` %s ) x. ( 2 x. D ) ) <_ ( %s x. %s )' % (BCd, CD, SIX))
    DF = d('fzfid', [], '%s e. Fin' % DR)
    hr = cd('nn0red', [cd('syl', [bcf, w.inst('hashcl')], '( # ` %s ) e. NN0' % BCd)], '( # ` %s ) e. RR' % BCd)
    sixr = cd('fsumrecl', [bcf, iujr], '%s e. RR' % SIX)
    SDL = 'sum_ d e. %s ( ( # ` %s ) x. ( 2 x. D ) )' % (DR, BCd)
    SDR = 'sum_ d e. %s ( %s x. %s )' % (DR, CD, SIX)
    le_d = d('fsumle', [DF, cd('remulcld', [hr, lift(w, c0.mem('( 2 x. D )', 'RR'), Cd)], '( ( # ` %s ) x. ( 2 x. D ) ) e. RR' % BCd), cd('remulcld', [lift(w, c0.mem(CD, 'RR'), Cd), sixr], '( %s x. %s ) e. RR' % (CD, SIX)), le_x2],
             '%s <_ %s' % (SDL, SDR))
    R = RCNT
    lq = d('fsummulc1', [DF, d('recnd', [c0.mem('( 2 x. D )', 'RR')], '( 2 x. D ) e. CC'), cd('recnd', [hr], '( # ` %s ) e. CC' % BCd)], '( %s x. ( 2 x. D ) ) = %s' % (R, SDL))
    SDD = 'sum_ d e. %s %s' % (DR, SIX)
    rq = d('fsummulc2', [DF, d('recnd', [c0.mem(CD, 'RR')], '%s e. CC' % CD), cd('recnd', [sixr], '%s e. CC' % SIX)], '( %s x. %s ) = %s' % (CD, SDD, SDR))
    main1 = d('eqbrtrd', [lq, d('breqtrrd', [le_d, rq], '%s <_ ( %s x. %s )' % (SDL, CD, SDD))], '( %s x. ( 2 x. D ) ) <_ ( %s x. %s )' % (R, CD, SDD))
    # swap the finite sums with the u-integral
    Cdu = '( %s /\\ ( u e. %s /\\ x e. %s ) )' % (Cd, YZ, BCd)
    jurc = rean(w, cxu('recnd', [jur], '( %s / u ) e. CC' % JJu), Cdu)
    f1 = cd('itgfsum', [a1(w, Cd, 'ioombl', '%s e. dom vol' % YZ), bcf, jurc, swib], '( ( u e. %s |-> sum_ x e. %s ( %s / u ) ) e. L^1 /\\ S. %s sum_ x e. %s ( %s / u ) _d u = %s )' % (YZ, BCd, JJu, YZ, BCd, JJu, SIX))
    SXU = 'sum_ x e. %s ( %s / u )' % (BCd, JJu)
    Cdu2 = '( %s /\\ ( u e. %s /\\ d e. %s ) )' % (A0, YZ, DR)
    Cdu2x = '( ( %s /\\ ( u e. %s /\\ d e. %s ) ) /\\ x e. %s )' % (A0, YZ, DR, BCd)
    sxuc = D(w, Cdu2, 'fsumcl', [rean(w, bcf, Cdu2), rean(w, jurc, Cdu2x)], '%s e. CC' % SXU)
    f2 = d('itgfsum', [a1(w, A0, 'ioombl', '%s e. dom vol' % YZ), DF, sxuc, cd('simpld', [f1], '( u e. %s |-> %s ) e. L^1' % (YZ, SXU))],
           '( ( u e. %s |-> sum_ d e. %s %s ) e. L^1 /\\ S. %s sum_ d e. %s %s _d u = sum_ d e. %s S. %s %s _d u )' % (YZ, DR, SXU, YZ, DR, SXU, DR, YZ, SXU))
    s_in = d('sumeq2dv', [cd('simprd', [f1], 'S. %s %s _d u = %s' % (YZ, SXU, SIX))], 'sum_ d e. %s S. %s %s _d u = %s' % (DR, YZ, SXU, SDD))
    SDU = 'sum_ d e. %s %s' % (DR, SXU)
    ITU = 'S. %s %s _d u' % (YZ, SDU)
    iq = d('eqtrd', [d('simprd', [f2], '%s = sum_ d e. %s S. %s %s _d u' % (ITU, DR, YZ, SXU)), s_in], '%s = %s' % (ITU, SDD))
    # pointwise: SDU = FAMJ / u <_ ( B / L ) x. ( 1 / u )
    Au = '( %s /\\ u e. %s )' % (A0, YZ)
    au = mk(w, Au)
    ug2 = au('mpbid', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, YZ)), au('syl2anc', [au('rexrd', [lift(w, x1r, Au)], '%s e. RR*' % X1), au('rexrd', [lift(w, x2r, Au)], '%s e. RR*' % X2), w.inst('elioo2')],
                                                                             '( u e. %s <-> ( u e. RR /\\ %s < u /\\ u < %s ) )' % (YZ, X1, X2))], '( u e. RR /\\ %s < u /\\ u < %s )' % (X1, X2))
    ur2 = au('simp1d', [ug2], 'u e. RR'); x1u = au('simp2d', [ug2], '%s < u' % X1); ux2 = au('ltled', [ur2, lift(w, x2r, Au), au('simp3d', [ug2], 'u < %s' % X2)], 'u <_ %s' % X2)
    up2 = au('lttrd', [a1(w, Au, '0re', '0 e. RR'), lift(w, x1r, Au), ur2, au('rpgt0d', [lift(w, x1p, Au)], '0 < %s' % X1), x1u], '0 < u')
    SVU = inst('cmsvu', {'U': 'u', 'Y': X1, 'Z': X2})
    svh = au('jca', [lift(w, d('3jca', [d('3jca', [sr, vr, wr], '( S e. RR /\\ V e. RR /\\ W e. RR )'), d('jca', [v1, w2], '( 1 <_ V /\\ 2 <_ W )'), d('3jca', [kz, kw, v3], '( K e. ZZ /\\ K <_ W /\\ ( V + 3 ) <_ W )')],
                                      '( ( S e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( 1 <_ V /\\ 2 <_ W ) /\\ ( K e. ZZ /\\ K <_ W /\\ ( V + 3 ) <_ W ) )'), Au),
                     au('3jca', [lift(w, d('jca', [x1r, w5], '( %s e. RR /\\ ( W ^ 5 ) <_ %s )' % (X1, X1)), Au), lift(w, d('jca', [x2r, ez], '( %s e. RR /\\ ( exp ` ; 2 0 ) <_ %s )' % (X2, X2)), Au),
                                 au('3jca', [ur2, x1u, ux2], '( u e. RR /\\ %s < u /\\ u <_ %s )' % (X1, X2))],
                        '( ( %s e. RR /\\ ( W ^ 5 ) <_ %s ) /\\ ( %s e. RR /\\ ( exp ` ; 2 0 ) <_ %s ) /\\ ( u e. RR /\\ %s < u /\\ u <_ %s ) )' % (X1, X1, X2, X2, X1, X2))], SVU[0])
    sv = au('syl', [svh, w.inst('cmsvu')], SVU[1])
    FAM = FAMJ('u', X1)
    B = '( %s x. ( ( log ` %s ) ^ 2 ) )' % (C750, X2)
    uc = au('recnd', [ur2], 'u e. CC'); une = au('gt0ne0d', [up2], 'u =/= 0')
    # SDU = FAM / u
    Aud = '( %s /\\ d e. %s )' % (Au, DR)
    Audx = '( %s /\\ x e. %s )' % (Aud, BCd)
    jc3 = rean(w, cxu('recnd', [jr], '%s e. CC' % JJu), Audx)
    bcf3 = rean(w, bcf, Aud)
    SXJ = 'sum_ x e. %s %s' % (BCd, JJu)
    dv1 = D(w, Aud, 'fsumdivc', [bcf3, lift(w, uc, Aud), jc3, lift(w, une, Aud)], '( %s / u ) = %s' % (SXJ, SXU))
    sxjc = D(w, Aud, 'fsumcl', [bcf3, jc3], '%s e. CC' % SXJ)
    dv2 = au('fsumdivc', [lift(w, DF, Au), uc, sxjc, une], '( %s / u ) = sum_ d e. %s ( %s / u )' % (FAM, DR, SXJ))
    dv3 = au('eqtrd', [dv2, au('sumeq2dv', [dv1], 'sum_ d e. %s ( %s / u ) = %s' % (DR, SXJ, SDU))], '( %s / u ) = %s' % (FAM, SDU))
    famr = au('fsumrecl', [lift(w, DF, Au), D(w, Aud, 'fsumrecl', [bcf3, rean(w, jr, Audx)], '%s e. RR' % SXJ)], '%s e. RR' % FAM)
    Lp = lift(w, lwp, Au)
    fl = au('mpbid', [au('eqbrtrd', [au('mulcomd', [au('recnd', [famr], '%s e. CC' % FAM), au('rpcnd', [Lp], '%s e. CC' % LW)], '( %s x. %s ) = ( %s x. %s )' % (FAM, LW, LW, FAM)), sv], '( %s x. %s ) <_ %s' % (FAM, LW, B)),
                      au('syl3anc', [famr, lift(w, c0.mem(B, 'RR') if False else d('remulcld', [d('remulcld', [c0.mem('; ; 7 5 0', 'RR'), d('resqcld', [ere(w, A0)], '%s e. RR' % EE2)], '%s e. RR' % C750),
                                                                                              d('resqcld', [d('relogcld', [d('rpefcld', [c0.mem(E2, 'RR')], '%s e. RR+' % X2)], '( log ` %s ) e. RR' % X2)], '( ( log ` %s ) ^ 2 ) e. RR' % X2)], '%s e. RR' % B), Au),
                                     au('jca', [au('rpred', [Lp], '%s e. RR' % LW), au('rpgt0d', [Lp], '0 < %s' % LW)], '( %s e. RR /\\ 0 < %s )' % (LW, LW)), w.inst('lemuldiv')],
                         '( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) )' % (FAM, LW, B, FAM, B, LW))], '%s <_ ( %s / %s )' % (FAM, B, LW))
    br = d('remulcld', [d('remulcld', [c0.mem('; ; 7 5 0', 'RR'), d('resqcld', [ere(w, A0)], '%s e. RR' % EE2)], '%s e. RR' % C750),
                        d('resqcld', [d('relogcld', [d('rpefcld', [c0.mem(E2, 'RR')], '%s e. RR+' % X2)], '( log ` %s ) e. RR' % X2)], '( ( log ` %s ) ^ 2 ) e. RR' % X2)], '%s e. RR' % B)
    BL = '( %s / %s )' % (B, LW)
    blr = d('redivcld', [br, lwr, d('rpne0d', [lwp], '%s =/= 0' % LW)], '%s e. RR' % BL)
    iu = au('rereccld', [ur2, une], '( 1 / u ) e. RR')
    pt = au('lemul1ad', [famr, lift(w, blr, Au), iu, au('ltled', [a1(w, Au, '0re', '0 e. RR'), iu, au('recgt0d', [ur2, up2], '0 < ( 1 / u )') if False else au('recgt0d', [ur2, up2], '0 < ( 1 / u )')], '0 <_ ( 1 / u )'), fl],
             '( %s x. ( 1 / u ) ) <_ ( %s x. ( 1 / u ) )' % (FAM, BL))
    pt2 = au('eqbrtrd', [au('eqtr3d' if False else 'eqtrd', [au('eqcomd', [dv3], '%s = ( %s / u )' % (SDU, FAM)), au('divrecd', [au('recnd', [famr], '%s e. CC' % FAM), uc, une], '( %s / u ) = ( %s x. ( 1 / u ) )' % (FAM, FAM))],
                                 '%s = ( %s x. ( 1 / u ) )' % (SDU, FAM)), pt], '%s <_ ( %s x. ( 1 / u ) )' % (SDU, BL))
    sdur = au('eqeltrd', [au('eqcomd', [dv3], '%s = ( %s / u )' % (SDU, FAM)), au('redivcld', [famr, ur2, une], '( %s / u ) e. RR' % FAM)], '%s e. RR' % SDU)
    # the integral of ( B / L ) ( 1 / u )
    lg = d('syl3anc', [x1p, x2r, x12l, w.inst('kd2log')], '( ( u e. %s |-> ( 1 / u ) ) e. L^1 /\\ S. %s ( 1 / u ) _d u = ( ( log ` %s ) - ( log ` %s ) ) )' % (YZ, YZ, X2, X1))
    DL = '( ( log ` %s ) - ( log ` %s ) )' % (X2, X1)
    iuc = au('recnd', [iu], '( 1 / u ) e. CC')
    ibr = d('iblmulc2', [d('recnd', [blr], '%s e. CC' % BL), iuc, d('simpld', [lg], '( u e. %s |-> ( 1 / u ) ) e. L^1' % YZ)], '( u e. %s |-> ( %s x. ( 1 / u ) ) ) e. L^1' % (YZ, BL))
    ile = d('itgle', [d('simpld', [f2], '( u e. %s |-> %s ) e. L^1' % (YZ, SDU)), ibr, sdur, au('remulcld', [lift(w, blr, Au), iu], '( %s x. ( 1 / u ) ) e. RR' % BL), pt2],
            '%s <_ S. %s ( %s x. ( 1 / u ) ) _d u' % (ITU, YZ, BL))
    ival = d('eqtr3d', [d('itgmulc2', [d('recnd', [blr], '%s e. CC' % BL), iuc, d('simpld', [lg], '( u e. %s |-> ( 1 / u ) ) e. L^1' % YZ)], '( %s x. S. %s ( 1 / u ) _d u ) = S. %s ( %s x. ( 1 / u ) ) _d u' % (BL, YZ, YZ, BL)),
                        d('oveq2d', [d('simprd', [lg], 'S. %s ( 1 / u ) _d u = %s' % (YZ, DL))], '( %s x. S. %s ( 1 / u ) _d u ) = ( %s x. %s )' % (BL, YZ, BL, DL))], 'S. %s ( %s x. ( 1 / u ) ) _d u = ( %s x. %s )' % (YZ, BL, BL, DL))
    sdd_le = d('eqbrtrrd', [iq, d('breqtrd', [ile, ival], '%s <_ ( %s x. %s )' % (ITU, BL, DL))], '%s <_ ( %s x. %s )' % (SDD, BL, DL))
    # assemble
    sddr = d('fsumrecl', [DF, sixr], '%s e. RR' % SDD)
    dlr = c0.mem(DL, 'RR') if False else d('resubd' if False else 'resubcld', [d('relogcld', [d('rpefcld', [c0.mem(E2, 'RR')], '%s e. RR+' % X2)], '( log ` %s ) e. RR' % X2), d('relogcld', [x1p], '( log ` %s ) e. RR' % X1)], '%s e. RR' % DL)
    c1 = d('lemul2ad', [sddr, d('remulcld', [blr, dlr], '( %s x. %s ) e. RR' % (BL, DL)), c0.mem(CD, 'RR'), c0.ge0(CD), sdd_le], '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (CD, SDD, CD, BL, DL))
    rr_ = d('fsumrecl', [DF, cd('nn0red', [cd('syl', [bcf, w.inst('hashcl')], '( # ` %s ) e. NN0' % BCd)], '( # ` %s ) e. RR' % BCd)], '%s e. RR' % R)
    tdr = c0.mem('( 2 x. D )', 'RR')
    m2 = d('letrd', [d('remulcld', [rr_, tdr], '( %s x. ( 2 x. D ) ) e. RR' % R), d('remulcld', [c0.mem(CD, 'RR'), sddr], '( %s x. %s ) e. RR' % (CD, SDD)),
                     d('remulcld', [c0.mem(CD, 'RR'), d('remulcld', [blr, dlr], '( %s x. %s ) e. RR' % (BL, DL))], '( %s x. ( %s x. %s ) ) e. RR' % (CD, BL, DL)), main1, c1],
            '( %s x. ( 2 x. D ) ) <_ ( %s x. ( %s x. %s ) )' % (R, CD, BL, DL))
    m3 = d('lemul1ad', [d('remulcld', [rr_, tdr], '( %s x. ( 2 x. D ) ) e. RR' % R), d('remulcld', [c0.mem(CD, 'RR'), d('remulcld', [blr, dlr], '( %s x. %s ) e. RR' % (BL, DL))], '( %s x. ( %s x. %s ) ) e. RR' % (CD, BL, DL)), lwr, lw0, m2],
            '( ( %s x. ( 2 x. D ) ) x. %s ) <_ ( ( %s x. ( %s x. %s ) ) x. %s )' % (R, LW, CD, BL, DL, LW))
    # algebra
    ccl = Closure(w, A0, {R: ('CC', d('recnd', [rr_], '%s e. CC' % R)), 'D': ('CC', d('rpcnd', [dp], 'D e. CC')), LW: ('CC', d('rpcnd', [lwp], '%s e. CC' % LW)),
                          CD: ('CC', d('recnd', [c0.mem(CD, 'RR')], '%s e. CC' % CD)), BL: ('CC', d('recnd', [blr], '%s e. CC' % BL)), DL: ('CC', d('recnd', [dlr], '%s e. CC' % DL)),
                          B: ('CC', d('recnd', [br], '%s e. CC' % B))})
    for at_ in (R, LW, CD, BL, DL, B):
        ccl.atom(at_)
    l1 = ringeq(w, A0, '( ( %s x. ( 2 x. D ) ) x. %s )' % (R, LW), '( ( ( 2 x. D ) x. %s ) x. %s )' % (R, LW), ccl)
    r1 = ringeq(w, A0, '( ( %s x. ( %s x. %s ) ) x. %s )' % (CD, BL, DL, LW), '( %s x. ( ( %s x. %s ) x. %s ) )' % (CD, BL, LW, DL), ccl)
    bl = d('divcan1d', [d('recnd', [br], '%s e. CC' % B), d('rpcnd', [lwp], '%s e. CC' % LW), d('rpne0d', [lwp], '%s =/= 0' % LW)], '( %s x. %s ) = %s' % (BL, LW, B))
    r2 = d('oveq2d', [d('oveq1d', [bl], '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (BL, LW, DL, B, DL))], '( %s x. ( ( %s x. %s ) x. %s ) ) = ( %s x. ( %s x. %s ) )' % (CD, BL, LW, DL, CD, B, DL))
    L2X = '( log ` %s )' % X2
    ccl2 = Closure(w, A0, {CD: ('CC', d('recnd', [c0.mem(CD, 'RR')], '%s e. CC' % CD)), DL: ('CC', d('recnd', [dlr], '%s e. CC' % DL)), EE2: ('CC', d('recnd', [d('resqcld', [ere(w, A0)], '%s e. RR' % EE2)], '%s e. CC' % EE2)),
                           '( ( log ` %s ) ^ 2 )' % X2: ('CC', d('recnd', [d('resqcld', [d('relogcld', [d('rpefcld', [c0.mem(E2, 'RR')], '%s e. RR+' % X2)], '( log ` %s ) e. RR' % X2)], '( ( log ` %s ) ^ 2 ) e. RR' % X2)], '( ( log ` %s ) ^ 2 ) e. CC' % X2))})
    for at_ in (CD, DL, EE2, '( ( log ` %s ) ^ 2 )' % X2):
        ccl2.atom(at_)
    RHS = '( ( %s x. %s ) x. ( ( ( log ` %s ) ^ 2 ) x. %s ) )' % (C750, CD, X2, DL)
    r3 = ringeq(w, A0, '( %s x. ( %s x. %s ) )' % (CD, B, DL), RHS, ccl2)
    rch = chain(w, A0, ['( ( %s x. ( %s x. %s ) ) x. %s )' % (CD, BL, DL, LW), '( %s x. ( ( %s x. %s ) x. %s ) )' % (CD, BL, LW, DL), '( %s x. ( %s x. %s ) )' % (CD, B, DL), RHS], [r1, r2, r3])
    fin = d('breqtrd', [d('eqbrtrrd', [l1, m3], '( ( ( 2 x. D ) x. %s ) x. %s ) <_ ( ( %s x. ( %s x. %s ) ) x. %s )' % (R, LW, CD, BL, DL, LW)), rch], C0)
    w.qed([fin], 'idi', S['cmfam'])
    return run(w, only)


if __name__ == '__main__':
    gen_fam()
