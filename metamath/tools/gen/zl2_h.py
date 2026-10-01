"""ZL2 section H: the convexity bound, generic (LConvexity 950-1297: zl2cvxa, zl2cvxb, zl2cvxm,
zl2cvxr, zl2cvxl, zl2cvxu, zl2cvxpl, zl2cvxd, zl2cvx, zl2cvx1).
`MM_DB=sorties/zl2.mm python3 tools/gen/zl2_h.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl2lib import *
from lin import linarith, nlinarith
from zl2_g import inst_ral_t, cbv_yz
import num

only = sys.argv[1:]


def lediv_(w, ante, a, b, arp, brp, le):
    """( ante -> ( 1 / b ) <_ ( 1 / a ) ) from le: ( ante -> a <_ b ), a, b e. RR+"""
    bi = D(w, ante, 'lerecd', [arp, brp], '( %s <_ %s <-> ( 1 / %s ) <_ ( 1 / %s ) )' % (a, b, b, a))
    return w.s([le, bi], 'mpbid', '( %s -> ( 1 / %s ) <_ ( 1 / %s ) )' % (ante, b, a))


def subst(text, m):
    """token-level substitution of class variables"""
    return ' '.join(m.get(t, t) for t in text.split())


# ---------------------------------------------------------------- zl2cvxa
if __name__ == '__main__' and (not only or 'zl2cvxa' in only):
    w = W('zl2cvxa', 'The parameters of the convexity proof: for ` D = N ( T + 2 ) ` , ` M = N ( T + 3 ) ` and ` L = 1 + log M ` , '
          '` 1 <_ D <_ M ` , ` 3 <_ M ` , ` 1 <_ log M ` , ` 2 <_ L ` and ` log D <_ L ` ( LConvexity 968-994 ).')
    A0 = '( N e. NN /\\ T e. RR /\\ 0 <_ T )'
    nn = D(w, A0, 'simp1', [], 'N e. NN'); tr = D(w, A0, 'simp2', [], 'T e. RR'); t0 = D(w, A0, 'simp3', [], '0 <_ T')
    nr = D(w, A0, 'nnred', [nn], 'N e. RR'); n1 = D(w, A0, 'nnge1d', [nn], '1 <_ N'); nrp = D(w, A0, 'nnrpd', [nn], 'N e. RR+')
    cl = Closure(w, A0, {'N': ('RR', nr), 'T': ('RR', tr)})
    t2 = D(w, A0, 'readdcld', [tr, a1(w, A0, '2re', '2 e. RR')], '( T + 2 ) e. RR')
    t3 = D(w, A0, 'readdcld', [tr, a1(w, A0, '3re', '3 e. RR')], '( T + 3 ) e. RR')
    t2p = linarith(w, A0, [t0], '0 < ( T + 2 )', closure=cl)
    t3p = linarith(w, A0, [t0], '0 < ( T + 3 )', closure=cl)
    ddrp = D(w, A0, 'rpmulcld', [nrp, D(w, A0, 'elrpd', [t2, t2p], '( T + 2 ) e. RR+')], '%s e. RR+' % DDT)
    mmrp = D(w, A0, 'rpmulcld', [nrp, D(w, A0, 'elrpd', [t3, t3p], '( T + 3 ) e. RR+')], '%s e. RR+' % MMT)
    dd1 = nlinarith(w, A0, [n1, t0], '1 <_ %s' % DDT, closure=cl)
    mm3 = nlinarith(w, A0, [n1, t0], '3 <_ %s' % MMT, closure=cl)
    ddmm = nlinarith(w, A0, [n1, t0], '%s <_ %s' % (DDT, MMT), closure=cl)
    LM = '( log ` %s )' % MMT
    ele = w.s([ele3(w)], 'a1i', '( %s -> _e <_ 3 )' % A0)
    emm = D(w, A0, 'letrd', [a1(w, A0, 'ere', '_e e. RR'), a1(w, A0, '3re', '3 e. RR'), D(w, A0, 'rpred', [mmrp], '%s e. RR' % MMT), ele, mm3], '_e <_ %s' % MMT)
    lbi = D(w, A0, 'logled', [a1(w, A0, 'epr', '_e e. RR+'), mmrp], '( _e <_ %s <-> ( log ` _e ) <_ %s )' % (MMT, LM))
    lm1 = w.s([a1(w, A0, 'loge', '( log ` _e ) = 1'), w.s([emm, lbi], 'mpbid', '( %s -> ( log ` _e ) <_ %s )' % (A0, LM))], 'eqbrtrrd', '( %s -> 1 <_ %s )' % (A0, LM))
    lmr = D(w, A0, 'relogcld', [mmrp], '%s e. RR' % LM)
    llr = D(w, A0, 'readdcld', [a1(w, A0, '1re', '1 e. RR'), lmr], '%s e. RR' % LLT)
    cl.leaf(LM, 'RR', lmr)
    ll2 = linarith(w, A0, [lm1], '2 <_ %s' % LLT, closure=cl)
    llp = linarith(w, A0, [lm1], '0 < %s' % LLT, closure=cl)
    llrp = D(w, A0, 'elrpd', [llr, llp], '%s e. RR+' % LLT)
    LD = '( log ` %s )' % DDT
    ldm = w.s([ddmm, D(w, A0, 'logled', [ddrp, mmrp], '( %s <_ %s <-> %s <_ %s )' % (DDT, MMT, LD, LM))], 'mpbid', '( %s -> %s <_ %s )' % (A0, LD, LM))
    cl.leaf(LD, 'RR', D(w, A0, 'relogcld', [ddrp], '%s e. RR' % LD))
    ldl = linarith(w, A0, [ldm], '%s <_ %s' % (LD, LLT), closure=cl)
    c1 = w.s([w.s([ddrp, dd1], 'jca', '( %s -> ( %s e. RR+ /\\ 1 <_ %s ) )' % (A0, DDT, DDT)), w.s([mmrp, mm3], 'jca', '( %s -> ( %s e. RR+ /\\ 3 <_ %s ) )' % (A0, MMT, MMT)), ddmm], '3jca',
             '( %s -> ( ( %s e. RR+ /\\ 1 <_ %s ) /\\ ( %s e. RR+ /\\ 3 <_ %s ) /\\ %s <_ %s ) )' % (A0, DDT, DDT, MMT, MMT, DDT, MMT))
    c2 = w.s([w.s([lm1, w.s([llrp, ll2], 'jca', '( %s -> ( %s e. RR+ /\\ 2 <_ %s ) )' % (A0, LLT, LLT))], 'jca', '( %s -> ( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) )' % (A0, LM, LLT, LLT)), ldl], 'jca',
             '( %s -> ( ( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ %s <_ %s ) )' % (A0, LM, LLT, LLT, LD, LLT))
    w.qed([c1, c2], 'jca', STATEMENTS['zl2cvxa'])
    go(w, only)


# ---------------------------------------------------------------- zl2cvxb
if __name__ == '__main__' and (not only or 'zl2cvxb' in only):
    w = W('zl2cvxb', 'The normalizer parameters of the convexity proof: for ` 1 <_ D ` , ` 2 <_ L ` , ` log D <_ L ` , with ` sigma_R = 1 + 1 / L ` , '
          '` sigma_L = - 1 / L ` , ` W = sigma_R - sigma_L ` , ` b = 108 D ^ ( 1/2 ) ` and ` c = log b / W ` : ` D ^ ( 1 / L ) <_ 3 ` , ` 1 <_ b ` , '
          '` W <_ 2 ` , ` 0 <_ c ` and ` e ^ ( ( sigma_L - sigma_R ) c ) = 1 / b ` ( LConvexity 995-1067 ).')
    B0 = '( ( D e. RR+ /\\ 1 <_ D ) /\\ ( L e. RR+ /\\ 2 <_ L ) /\\ ( log ` D ) <_ L )'
    dl = D(w, B0, 'simp1', [], '( D e. RR+ /\\ 1 <_ D )'); ll = D(w, B0, 'simp2', [], '( L e. RR+ /\\ 2 <_ L )'); ld = D(w, B0, 'simp3', [], '( log ` D ) <_ L')
    drp = D(w, B0, 'simpld', [dl], 'D e. RR+'); d1 = D(w, B0, 'simprd', [dl], '1 <_ D')
    lrp = D(w, B0, 'simpld', [ll], 'L e. RR+'); l2 = D(w, B0, 'simprd', [ll], '2 <_ L')
    dr = D(w, B0, 'rpred', [drp], 'D e. RR'); dc = D(w, B0, 'rpcnd', [drp], 'D e. CC'); dne = D(w, B0, 'rpne0d', [drp], 'D =/= 0')
    d0 = D(w, B0, 'rpge0d', [drp], '0 <_ D')
    lr = D(w, B0, 'rpred', [lrp], 'L e. RR'); lc = D(w, B0, 'rpcnd', [lrp], 'L e. CC'); lne = D(w, B0, 'rpne0d', [lrp], 'L =/= 0')
    U = '( 1 / L )'
    urp = D(w, B0, 'rpreccld', [lrp], '%s e. RR+' % U); ur = D(w, B0, 'rpred', [urp], '%s e. RR' % U); uc = D(w, B0, 'rpcnd', [urp], '%s e. CC' % U)
    u0 = D(w, B0, 'rpge0d', [urp], '0 <_ %s' % U); ugt = D(w, B0, 'rpgt0d', [urp], '0 < %s' % U)
    LD = '( log ` D )'
    ldr = D(w, B0, 'relogcld', [drp], '%s e. RR' % LD)
    # D ^ ( 1 / L ) = e ^ ( ( 1 / L ) log D ) <_ e ^ 1 <_ 3
    e1 = D(w, B0, 'cxpefd', [dc, dne, uc], '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (U, U, LD))
    m1 = D(w, B0, 'lemul2ad', [ldr, lr, ur, u0, ld], '( %s x. %s ) <_ ( %s x. L )' % (U, LD, U))
    m2 = w.s([m1, D(w, B0, 'recid2d', [lc, lne], '( %s x. L ) = 1' % U)], 'breqtrd', '( %s -> ( %s x. %s ) <_ 1 )' % (B0, U, LD))
    ulr = D(w, B0, 'remulcld', [ur, ldr], '( %s x. %s ) e. RR' % (U, LD))
    e2 = efle_(w, B0, '( %s x. %s )' % (U, LD), '1', ulr, a1(w, B0, '1re', '1 e. RR'), m2)
    e3 = D(w, B0, 'letrd', [D(w, B0, 'reefcld', [ulr], '( exp ` ( %s x. %s ) ) e. RR' % (U, LD)), D(w, B0, 'reefcld', [a1(w, B0, '1re', '1 e. RR')], '( exp ` 1 ) e. RR'),
                            a1(w, B0, '3re', '3 e. RR'), e2, w.s([e1le3(w)], 'a1i', '( %s -> ( exp ` 1 ) <_ 3 )' % B0)], '( exp ` ( %s x. %s ) ) <_ 3' % (U, LD))
    d3 = w.s([e1, e3], 'eqbrtrd', '( %s -> ( D ^c %s ) <_ 3 )' % (B0, U))
    # 1 <_ D ^ ( 1 / 2 ) ; b = 108 D ^ ( 1 / 2 )
    half = a1(w, B0, 'halfre', '( 1 / 2 ) e. RR')
    h0 = w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], 'halfgt0', '0 < ( 1 / 2 )')], 'ltleii', '0 <_ ( 1 / 2 )')], 'a1i', '( %s -> 0 <_ ( 1 / 2 ) )' % B0)
    p1 = D(w, B0, 'cxplead', [dr, d1, a1(w, B0, '0re', '0 e. RR'), half, h0], '( D ^c 0 ) <_ ( D ^c ( 1 / 2 ) )')
    DH = '( D ^c ( 1 / 2 ) )'
    dh1 = w.s([D(w, B0, 'cxp0d', [dc], '( D ^c 0 ) = 1'), p1], 'eqbrtrrd', '( %s -> 1 <_ %s )' % (B0, DH))
    dhrp = D(w, B0, 'rpcxpcld', [drp, half], '%s e. RR+' % DH)
    dhr = D(w, B0, 'rpred', [dhrp], '%s e. RR' % DH)
    BBD = BB('D')
    n108 = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '8nn', '8 e. NN')], 'decnncl', '; ; 1 0 8 e. NN'),
                w.s([], 'nnrp', '( ; ; 1 0 8 e. NN -> ; ; 1 0 8 e. RR+ )')], 'ax-mp', '; ; 1 0 8 e. RR+')
    bbrp = D(w, B0, 'rpmulcld', [w.s([n108], 'a1i', '( %s -> ; ; 1 0 8 e. RR+ )' % B0), dhrp], '%s e. RR+' % BBD)
    bbr = D(w, B0, 'rpred', [bbrp], '%s e. RR' % BBD)
    bb1 = linarith(w, B0, [dh1], '1 <_ %s' % BBD, leaves={DH: dhr})
    # 1 / L <_ 1 / 2 ; W = sigma_R - sigma_L = 1 + 2 / L
    u12 = lediv_(w, B0, '2', 'L', a1(w, B0, '2rp', '2 e. RR+'), lrp, l2)
    srr = D(w, B0, 'readdcld', [a1(w, B0, '1re', '1 e. RR'), ur], '%s e. RR' % SRL)
    slr = D(w, B0, 'renegcld', [ur], '%s e. RR' % SLL)
    wwr = D(w, B0, 'resubcld', [srr, slr], '%s e. RR' % WWL)
    cl = Closure(w, B0, {U: ('RR', ur)})
    cl.atom(U)
    wwp = linarith(w, B0, [ugt], '0 < %s' % WWL, closure=cl)
    wwrp = D(w, B0, 'elrpd', [wwr, wwp], '%s e. RR+' % WWL)
    ww2 = linarith(w, B0, [u12], '%s <_ 2' % WWL, closure=cl)
    # c = log b / W
    LB = '( log ` %s )' % BBD
    lbr = D(w, B0, 'relogcld', [bbrp], '%s e. RR' % LB)
    lb0 = D(w, B0, 'logge0d', [bbr, bb1], '0 <_ %s' % LB)
    CCD = CCL('D')
    ccr = D(w, B0, 'redivcld', [lbr, wwr, D(w, B0, 'rpne0d', [wwrp], '%s =/= 0' % WWL)], '%s e. RR' % CCD)
    cc0 = D(w, B0, 'divge0d', [lbr, wwrp, lb0], '0 <_ %s' % CCD)
    # e ^ ( ( sigma_L - sigma_R ) c ) = 1 / b
    src = D(w, B0, 'recnd', [srr], '%s e. CC' % SRL); slc = D(w, B0, 'recnd', [slr], '%s e. CC' % SLL)
    wwc = D(w, B0, 'recnd', [wwr], '%s e. CC' % WWL); ccc = D(w, B0, 'recnd', [ccr], '%s e. CC' % CCD); lbc = D(w, B0, 'recnd', [lbr], '%s e. CC' % LB)
    x1 = w.s([D(w, B0, 'negsubdi2d', [src, slc], '-u %s = ( %s - %s )' % (WWL, SLL, SRL))], 'eqcomd', '( %s -> ( %s - %s ) = -u %s )' % (B0, SLL, SRL, WWL))
    x2 = E(w, B0, 'oveq1d', [x1], '( ( %s - %s ) x. %s )' % (SLL, SRL, CCD), '( -u %s x. %s )' % (WWL, CCD))
    x3 = D(w, B0, 'mulneg1d', [wwc, ccc], '( -u %s x. %s ) = -u ( %s x. %s )' % (WWL, CCD, WWL, CCD))
    x4 = E(w, B0, 'negeqd', [D(w, B0, 'divcan2d', [lbc, wwc, D(w, B0, 'rpne0d', [wwrp], '%s =/= 0' % WWL)], '( %s x. %s ) = %s' % (WWL, CCD, LB))], '-u ( %s x. %s )' % (WWL, CCD), '-u %s' % LB)
    arg = chain(w, B0, ['( ( %s - %s ) x. %s )' % (SLL, SRL, CCD), '( -u %s x. %s )' % (WWL, CCD), '-u ( %s x. %s )' % (WWL, CCD), '-u %s' % LB], [x2, x3, x4])
    y1 = E(w, B0, 'fveq2d', [arg], '( exp ` ( ( %s - %s ) x. %s ) )' % (SLL, SRL, CCD), '( exp ` -u %s )' % LB)
    y2 = w.s([lbc, w.inst('efneg')], 'syl', '( %s -> ( exp ` -u %s ) = ( 1 / ( exp ` %s ) ) )' % (B0, LB, LB))
    y3 = E(w, B0, 'oveq2d', [D(w, B0, 'reeflogd', [bbrp], '( exp ` %s ) = %s' % (LB, BBD))], '( 1 / ( exp ` %s ) )' % LB, '( 1 / %s )' % BBD)
    ex = chain(w, B0, ['( exp ` ( ( %s - %s ) x. %s ) )' % (SLL, SRL, CCD), '( exp ` -u %s )' % LB, '( 1 / ( exp ` %s ) )' % LB, '( 1 / %s )' % BBD], [y1, y2, y3])
    c1 = w.s([d3, w.s([dh1, w.s([bbrp, bb1], 'jca', '( %s -> ( %s e. RR+ /\\ 1 <_ %s ) )' % (B0, BBD, BBD))], 'jca', '( %s -> ( 1 <_ %s /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) )' % (B0, DH, BBD, BBD))], 'jca',
             '( %s -> ( ( D ^c %s ) <_ 3 /\\ ( 1 <_ %s /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) ) )' % (B0, U, DH, BBD, BBD))
    c2 = w.s([w.s([u12, w.s([wwrp, ww2], 'jca', '( %s -> ( %s e. RR+ /\\ %s <_ 2 ) )' % (B0, WWL, WWL))], 'jca', '( %s -> ( %s <_ ( 1 / 2 ) /\\ ( %s e. RR+ /\\ %s <_ 2 ) ) )' % (B0, U, WWL, WWL)),
              w.s([w.s([ccr, cc0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (B0, CCD, CCD)), ex], 'jca', '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( exp ` ( ( %s - %s ) x. %s ) ) = ( 1 / %s ) ) )' % (B0, CCD, CCD, SLL, SRL, CCD, BBD))],
             'jca', '( %s -> ( ( %s <_ ( 1 / 2 ) /\\ ( %s e. RR+ /\\ %s <_ 2 ) ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( exp ` ( ( %s - %s ) x. %s ) ) = ( 1 / %s ) ) ) )' % (B0, U, WWL, WWL, CCD, CCD, SLL, SRL, CCD, BBD))
    w.qed([c1, c2], 'jca', STATEMENTS['zl2cvxb'])
    go(w, only)


# ---------------------------------------------------------------- zl2cvxm
if __name__ == '__main__' and (not only or 'zl2cvxm' in only):
    w = W('zl2cvxm', 'The arithmetic of the left-edge bound: ` G ( X Y V ) ( 81 H ) P <_ ( 27 / 4 ) G ` when ` Y <_ 3 ` , ` V H <_ 3 ` and '
          '` 108 X P = 1 ` ( LConvexity 1068-1116, the ` calc ` block of ` hleft ` ; at ` G = 12 A ( 1 + L ) ` the bound is ` 81 A ( 1 + L ) ` ).')
    M0 = STATEMENTS['zl2cvxm'].split(' -> ( ( ( G x.')[0][2:]
    gg = D(w, M0, 'simpll', [], '( G e. RR /\\ 0 <_ G )')
    xy = D(w, M0, 'simplr', [], '( ( X e. RR /\\ 0 <_ X ) /\\ ( Y e. RR /\\ ( 0 <_ Y /\\ Y <_ 3 ) ) )')
    vh = D(w, M0, 'simprl', [], '( ( V e. RR /\\ 0 <_ V ) /\\ ( H e. RR /\\ ( 0 <_ H /\\ ( V x. H ) <_ 3 ) ) )')
    pp = D(w, M0, 'simprr', [], '( ( P e. RR /\\ 0 <_ P ) /\\ ( ; ; 1 0 8 x. ( X x. P ) ) = 1 )')
    gr = D(w, M0, 'simpld', [gg], 'G e. RR'); g0 = D(w, M0, 'simprd', [gg], '0 <_ G')
    xx = D(w, M0, 'simpld', [xy], '( X e. RR /\\ 0 <_ X )'); yy = D(w, M0, 'simprd', [xy], '( Y e. RR /\\ ( 0 <_ Y /\\ Y <_ 3 ) )')
    xr = D(w, M0, 'simpld', [xx], 'X e. RR'); x0 = D(w, M0, 'simprd', [xx], '0 <_ X')
    yr = D(w, M0, 'simpld', [yy], 'Y e. RR'); y03 = D(w, M0, 'simprd', [yy], '( 0 <_ Y /\\ Y <_ 3 )')
    y0 = D(w, M0, 'simpld', [y03], '0 <_ Y'); y3 = D(w, M0, 'simprd', [y03], 'Y <_ 3')
    vv = D(w, M0, 'simpld', [vh], '( V e. RR /\\ 0 <_ V )'); hh = D(w, M0, 'simprd', [vh], '( H e. RR /\\ ( 0 <_ H /\\ ( V x. H ) <_ 3 ) )')
    vr = D(w, M0, 'simpld', [vv], 'V e. RR'); v0 = D(w, M0, 'simprd', [vv], '0 <_ V')
    hr = D(w, M0, 'simpld', [hh], 'H e. RR'); h03 = D(w, M0, 'simprd', [hh], '( 0 <_ H /\\ ( V x. H ) <_ 3 )')
    h0 = D(w, M0, 'simpld', [h03], '0 <_ H'); vh3 = D(w, M0, 'simprd', [h03], '( V x. H ) <_ 3')
    p_ = D(w, M0, 'simpld', [pp], '( P e. RR /\\ 0 <_ P )'); xp1 = D(w, M0, 'simprd', [pp], '( ; ; 1 0 8 x. ( X x. P ) ) = 1')
    pr = D(w, M0, 'simpld', [p_], 'P e. RR'); p0 = D(w, M0, 'simprd', [p_], '0 <_ P')
    xc, yc, vc, hc, pc = [D(w, M0, 'recnd', [st], '%s e. CC' % v) for st, v in [(xr, 'X'), (yr, 'Y'), (vr, 'V'), (hr, 'H'), (pr, 'P')]]
    cl = Closure(w, M0, {'X': ('RR', xr), 'Y': ('RR', yr), 'V': ('RR', vr), 'H': ('RR', hr), 'P': ('RR', pr)})
    VH = '( V x. H )'
    vhr = D(w, M0, 'remulcld', [vr, hr], '%s e. RR' % VH)
    vh0 = D(w, M0, 'mulge0d', [vr, hr, v0, h0], '0 <_ %s' % VH)
    Q = '( Y x. %s )' % VH
    q9 = nlinarith(w, M0, [y3, vh3, y0, vh0], '%s <_ 9' % Q, closure=cl)
    qr = D(w, M0, 'remulcld', [yr, vhr], '%s e. RR' % Q)
    q0 = D(w, M0, 'mulge0d', [yr, vhr, y0, vh0], '0 <_ %s' % Q)
    XP = '( X x. P )'
    xpr = D(w, M0, 'remulcld', [xr, pr], '%s e. RR' % XP)
    xp0 = D(w, M0, 'mulge0d', [xr, pr, x0, p0], '0 <_ %s' % XP)
    cl2 = Closure(w, M0, {XP: ('RR', xpr), Q: ('RR', qr)})
    cl2.atom(XP); cl2.atom(Q)
    t2 = nlinarith(w, M0, [xp1, q9, xp0, q0], '( %s x. %s ) <_ ( 1 / ; 1 2 )' % (XP, Q), closure=cl2)
    # ( ( ( ( X Y ) V ) H ) P ) = ( X P ) ( Y ( V H ) )
    M2 = '( ( X x. Y ) x. V )'
    a1_ = D(w, M0, 'mulassd', [xc, yc, vc], '%s = ( X x. ( Y x. V ) )' % M2)
    a2 = E(w, M0, 'oveq1d', [a1_], '( %s x. H )' % M2, '( ( X x. ( Y x. V ) ) x. H )')
    a3 = D(w, M0, 'mulassd', [xc, D(w, M0, 'mulcld', [yc, vc], '( Y x. V ) e. CC'), hc], '( ( X x. ( Y x. V ) ) x. H ) = ( X x. ( ( Y x. V ) x. H ) )')
    a4 = E(w, M0, 'oveq2d', [D(w, M0, 'mulassd', [yc, vc, hc], '( ( Y x. V ) x. H ) = %s' % Q)], '( X x. ( ( Y x. V ) x. H ) )', '( X x. %s )' % Q)
    a5 = chain(w, M0, ['( %s x. H )' % M2, '( ( X x. ( Y x. V ) ) x. H )', '( X x. ( ( Y x. V ) x. H ) )', '( X x. %s )' % Q], [a2, a3, a4])
    a6 = E(w, M0, 'oveq1d', [a5], '( ( %s x. H ) x. P )' % M2, '( ( X x. %s ) x. P )' % Q)
    a7 = D(w, M0, 'mul32d', [xc, D(w, M0, 'recnd', [qr], '%s e. CC' % Q), pc], '( ( X x. %s ) x. P ) = ( %s x. %s )' % (Q, XP, Q))
    t1 = w.s([a6, a7], 'eqtrd', '( %s -> ( ( %s x. H ) x. P ) = ( %s x. %s ) )' % (M0, M2, XP, Q))
    t3 = w.s([t1, t2], 'eqbrtrd', '( %s -> ( ( %s x. H ) x. P ) <_ ( 1 / ; 1 2 ) )' % (M0, M2))
    m2r = D(w, M0, 'remulcld', [D(w, M0, 'remulcld', [xr, yr], '( X x. Y ) e. RR'), vr], '%s e. RR' % M2)
    cl3 = Closure(w, M0, {'G': ('RR', gr), M2: ('RR', m2r), 'H': ('RR', hr), 'P': ('RR', pr)})
    cl3.atom(M2)
    goal = STATEMENTS['zl2cvxm'].split(' -> ', 1)[1][:-2]
    assert goal.startswith('( ( ( G x.'), goal
    fin = nlinarith(w, M0, [t3, g0], goal, closure=cl3)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)


def uparts(w, A0, lrp, l2):
    """u = 1 / L: ( u e. RR+, u e. RR, u e. CC, 0 <_ u, 0 < u, u <_ 1 / 2 )"""
    U = '( 1 / L )'
    urp = D(w, A0, 'rpreccld', [lrp], '%s e. RR+' % U)
    ur = D(w, A0, 'rpred', [urp], '%s e. RR' % U)
    uc = D(w, A0, 'rpcnd', [urp], '%s e. CC' % U)
    u0 = D(w, A0, 'rpge0d', [urp], '0 <_ %s' % U)
    ugt = D(w, A0, 'rpgt0d', [urp], '0 < %s' % U)
    u12 = lediv_(w, A0, '2', 'L', a1(w, A0, '2rp', '2 e. RR+'), lrp, l2)
    return urp, ur, uc, u0, ugt, u12


def efpos(w, A0, X, xr):
    """( exp ` X ) e. RR and 0 <_ ( exp ` X ) from xr: X e. RR"""
    er = D(w, A0, 'reefcld', [xr], '( exp ` %s ) e. RR' % X)
    e0 = D(w, A0, 'ltled', [a1(w, A0, '0re', '0 e. RR'), er, w.s([xr, w.inst('efgt0')], 'syl', '( %s -> 0 < ( exp ` %s ) )' % (A0, X))], '0 <_ ( exp ` %s )' % X)
    return er, e0


def gauss81(w, A0, XG, VG, xgr, vgr, sq4):
    """( A0 -> ( exp ` ( ( XG ^ 2 ) - ( VG ^ 2 ) ) ) <_ ( ; 8 1 x. ( exp ` -u ( VG ^ 2 ) ) ) ) from sq4: ( XG ^ 2 ) <_ 4;
    returns (step, H e. RR, 0 <_ H) for H = ( exp ` -u ( VG ^ 2 ) )"""
    a = '( %s ^ 2 )' % XG; b = '( %s ^ 2 )' % VG
    ar = D(w, A0, 'resqcld', [xgr], '%s e. RR' % a); br = D(w, A0, 'resqcld', [vgr], '%s e. RR' % b)
    ac = D(w, A0, 'recnd', [ar], '%s e. CC' % a); bc = D(w, A0, 'recnd', [br], '%s e. CC' % b)
    e1 = w.s([D(w, A0, 'negsubd', [ac, bc], '( %s + -u %s ) = ( %s - %s )' % (a, b, a, b))], 'eqcomd', '( %s -> ( %s - %s ) = ( %s + -u %s ) )' % (A0, a, b, a, b))
    e2 = E(w, A0, 'fveq2d', [e1], '( exp ` ( %s - %s ) )' % (a, b), '( exp ` ( %s + -u %s ) )' % (a, b))
    e3 = efadd_(w, A0, a, '-u %s' % b, ac, D(w, A0, 'negcld', [bc], '-u %s e. CC' % b))
    eq = w.s([e2, e3], 'eqtrd', '( %s -> ( exp ` ( %s - %s ) ) = ( ( exp ` %s ) x. ( exp ` -u %s ) ) )' % (A0, a, b, a, b))
    four = a1(w, A0, '4re', '4 e. RR')
    le4 = efle_(w, A0, a, '4', ar, four, sq4)
    ea, _ = efpos(w, A0, a, ar)
    le81 = D(w, A0, 'letrd', [ea, D(w, A0, 'reefcld', [four], '( exp ` 4 ) e. RR'), rr81(w, A0), le4, w.s([w.s([], 'zl2e4', '( exp ` 4 ) <_ ; 8 1')], 'a1i', '( %s -> ( exp ` 4 ) <_ ; 8 1 )' % A0)],
              '( exp ` %s ) <_ ; 8 1' % a)
    nb = D(w, A0, 'renegcld', [br], '-u %s e. RR' % b)
    hr, h0 = efpos(w, A0, '-u %s' % b, nb)
    m = D(w, A0, 'lemul1ad', [ea, rr81(w, A0), hr, h0, le81], '( ( exp ` %s ) x. ( exp ` -u %s ) ) <_ ( ; 8 1 x. ( exp ` -u %s ) )' % (a, b, b))
    return w.s([eq, m], 'eqbrtrd', '( %s -> ( exp ` ( %s - %s ) ) <_ ( ; 8 1 x. ( exp ` -u %s ) ) )' % (A0, a, b, b)), hr, h0


def rr81(w, A0):
    return w.s([w.s([w.s([w.s([], '8nn0', '8 e. NN0'), w.s([], '1nn0', '1 e. NN0')], 'deccl', '; 8 1 e. NN0')], 'nn0rei', '; 8 1 e. RR')], 'a1i', '( %s -> ; 8 1 e. RR )' % A0)


def rr108(w, A0):
    return w.s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; ; 1 0 8 e. NN0')], 'nn0rei', '; ; 1 0 8 e. RR')],
               'a1i', '( %s -> ; ; 1 0 8 e. RR )' % A0)


def rp108(w, A0):
    n = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '8nn', '8 e. NN')], 'decnncl', '; ; 1 0 8 e. NN'),
             w.s([], 'nnrp', '( ; ; 1 0 8 e. NN -> ; ; 1 0 8 e. RR+ )')], 'ax-mp', '; ; 1 0 8 e. RR+')
    return w.s([n], 'a1i', '( %s -> ; ; 1 0 8 e. RR+ )' % A0)


# ---------------------------------------------------------------- zl2cvxr
if __name__ == '__main__' and (not only or 'zl2cvxr' in only):
    w = W('zl2cvxr', 'The right edge of the convexity strip: on ` Re z = sigma_R = 1 + 1 / L ` the normalized modulus is at most ` 81 A ( 1 + L ) ` '
          '( LConvexity 1039-1053, ` hright ` ; the right-edge bound RGT at ` z ` and ` e ^ 4 <_ 81 ` ).')
    R0 = STATEMENTS['zl2cvxr'].split(' -> ( ( ( abs ` ( F ` Z ) )')[0][2:]
    al = D(w, R0, 'simplll', [], '( A e. RR+ /\\ ( L e. RR+ /\\ 2 <_ L ) )')
    ss = D(w, R0, 'simpllr', [], '( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ %s ) )' % SRL)
    crg = D(w, R0, 'simplr', [], '( C e. RR /\\ %s )' % RGT())
    zz = D(w, R0, 'simpr', [], '( ( Z e. CC /\\ ( F ` Z ) e. CC ) /\\ ( Re ` Z ) = %s )' % SRL)
    arp = D(w, R0, 'simpld', [al], 'A e. RR+'); l_ = D(w, R0, 'simprd', [al], '( L e. RR+ /\\ 2 <_ L )')
    lrp = D(w, R0, 'simpld', [l_], 'L e. RR+'); l2 = D(w, R0, 'simprd', [l_], '2 <_ L')
    sc = D(w, R0, 'simpld', [ss], 'S e. CC'); sb = D(w, R0, 'simprd', [ss], '( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ %s )' % SRL)
    s0 = D(w, R0, 'simpld', [sb], '0 <_ ( Re ` S )'); ssr = D(w, R0, 'simprd', [sb], '( Re ` S ) <_ %s' % SRL)
    cr = D(w, R0, 'simpld', [crg], 'C e. RR'); rgt = D(w, R0, 'simprd', [crg], RGT())
    zf = D(w, R0, 'simpld', [zz], '( Z e. CC /\\ ( F ` Z ) e. CC )'); rz = D(w, R0, 'simprd', [zz], '( Re ` Z ) = %s' % SRL)
    zc = D(w, R0, 'simpld', [zf], 'Z e. CC'); fzc = D(w, R0, 'simprd', [zf], '( F ` Z ) e. CC')
    U = '( 1 / L )'
    urp, ur, uc, u0, ugt, u12 = uparts(w, R0, lrp, l2)
    lr = D(w, R0, 'rpred', [lrp], 'L e. RR'); lc = D(w, R0, 'rpcnd', [lrp], 'L e. CC'); lne = D(w, R0, 'rpne0d', [lrp], 'L =/= 0')
    ar = D(w, R0, 'rpred', [arp], 'A e. RR'); a0 = D(w, R0, 'rpge0d', [arp], '0 <_ A')
    srr = D(w, R0, 'readdcld', [a1(w, R0, '1re', '1 e. RR'), ur], '%s e. RR' % SRL)
    src = D(w, R0, 'recnd', [srr], '%s e. CC' % SRL)
    rsr = D(w, R0, 'recld', [sc], '( Re ` S ) e. RR')
    cl = Closure(w, R0, {U: ('RR', ur), '( Re ` S )': ('RR', rsr), 'A': ('RR', ar), 'L': ('RR', lr)})
    cl.atom(U)
    sr1 = linarith(w, R0, [ugt], '1 < %s' % SRL, closure=cl)
    sr2 = linarith(w, R0, [u12], '%s <_ 2' % SRL, closure=cl)
    rz1 = w.s([sr1, rz], 'breqtrrd', '( %s -> 1 < ( Re ` Z ) )' % R0)
    rz2 = w.s([rz, sr2], 'eqbrtrd', '( %s -> ( Re ` Z ) <_ 2 )' % R0)
    fb0, fbb = inst_ral_t(w, R0, rgt, 'CC', RGT()[len('A. z e. CC '):], 'Z', zc)
    GB = '( A x. ( 1 + ( 1 / ( ( Re ` Z ) - 1 ) ) ) )'
    fb = w.s([fb0, w.s([rz1, rz2], 'jca', '( %s -> ( 1 < ( Re ` Z ) /\\ ( Re ` Z ) <_ 2 ) )' % R0)], 'mpd', '( %s -> ( abs ` ( F ` Z ) ) <_ %s )' % (R0, GB))
    q1 = w.s([E(w, R0, 'oveq1d', [rz], '( ( Re ` Z ) - 1 )', '( %s - 1 )' % SRL), D(w, R0, 'pncan2d', [a1(w, R0, 'ax-1cn', '1 e. CC'), uc], '( %s - 1 ) = %s' % (SRL, U))], 'eqtrd',
             '( %s -> ( ( Re ` Z ) - 1 ) = %s )' % (R0, U))
    q2 = w.s([E(w, R0, 'oveq2d', [q1], '( 1 / ( ( Re ` Z ) - 1 ) )', '( 1 / %s )' % U), D(w, R0, 'recrecd', [lc, lne], '( 1 / %s ) = L' % U)], 'eqtrd',
             '( %s -> ( 1 / ( ( Re ` Z ) - 1 ) ) = L )' % R0)
    AL = '( A x. ( 1 + L ) )'
    q3 = E(w, R0, 'oveq2d', [E(w, R0, 'oveq2d', [q2], '( 1 + ( 1 / ( ( Re ` Z ) - 1 ) ) )', '( 1 + L )')], GB, AL)
    fb2 = w.s([fb, q3], 'breqtrd', '( %s -> ( abs ` ( F ` Z ) ) <_ %s )' % (R0, AL))
    # the Gaussian: ( sigma_R - Re S ) ^ 2 <_ 4
    XG = '( %s - ( Re ` S ) )' % SRL
    xgr = D(w, R0, 'resubcld', [srr, rsr], '%s e. RR' % XG)
    x0 = linarith(w, R0, [ssr], '0 <_ %s' % XG, closure=cl)
    x32 = linarith(w, R0, [s0, u12], '%s <_ ( 3 / 2 )' % XG, closure=cl)
    clx = Closure(w, R0, {XG: ('RR', xgr)}); clx.atom(XG)
    sq4 = nlinarith(w, R0, [x0, x32], '( %s ^ 2 ) <_ 4' % XG, closure=clx)
    VG = '( ( Im ` Z ) - ( Im ` S ) )'
    vgr = D(w, R0, 'resubcld', [D(w, R0, 'imcld', [zc], '( Im ` Z ) e. RR'), D(w, R0, 'imcld', [sc], '( Im ` S ) e. RR')], '%s e. RR' % VG)
    G = GAUS(SRL)
    ARG = '( ( %s ^ 2 ) - ( %s ^ 2 ) )' % (XG, VG)
    argr = D(w, R0, 'resubcld', [D(w, R0, 'resqcld', [xgr], '( %s ^ 2 ) e. RR' % XG), D(w, R0, 'resqcld', [vgr], '( %s ^ 2 ) e. RR' % VG)], '%s e. RR' % ARG)
    cla = Closure(w, R0, {'( %s ^ 2 )' % XG: ('RR', D(w, R0, 'resqcld', [xgr], '( %s ^ 2 ) e. RR' % XG)), '( %s ^ 2 )' % VG: ('RR', D(w, R0, 'resqcld', [vgr], '( %s ^ 2 ) e. RR' % VG))})
    cla.atom('( %s ^ 2 )' % XG); cla.atom('( %s ^ 2 )' % VG)
    arg4 = linarith(w, R0, [sq4, D(w, R0, 'sqge0d', [vgr], '0 <_ ( %s ^ 2 )' % VG)], '%s <_ 4' % ARG, closure=cla)
    ge4 = efle_(w, R0, ARG, '4', argr, a1(w, R0, '4re', '4 e. RR'), arg4)
    gr, g0 = efpos(w, R0, ARG, argr)
    g81 = D(w, R0, 'letrd', [gr, D(w, R0, 'reefcld', [a1(w, R0, '4re', '4 e. RR')], '( exp ` 4 ) e. RR'), rr81(w, R0), ge4, w.s([w.s([], 'zl2e4', '( exp ` 4 ) <_ ; 8 1')], 'a1i', '( %s -> ( exp ` 4 ) <_ ; 8 1 )' % R0)],
             '%s <_ ; 8 1' % G)
    # the power factor is 1
    P = '( exp ` ( ( %s - %s ) x. C ) )' % (SRL, SRL)
    p1 = E(w, R0, 'oveq1d', [D(w, R0, 'subidd', [src], '( %s - %s ) = 0' % (SRL, SRL))], '( ( %s - %s ) x. C )' % (SRL, SRL), '( 0 x. C )')
    p2 = w.s([p1, D(w, R0, 'mul02d', [D(w, R0, 'recnd', [cr], 'C e. CC')], '( 0 x. C ) = 0')], 'eqtrd', '( %s -> ( ( %s - %s ) x. C ) = 0 )' % (R0, SRL, SRL))
    p3 = w.s([E(w, R0, 'fveq2d', [p2], P, '( exp ` 0 )'), a1(w, R0, 'ef0', '( exp ` 0 ) = 1')], 'eqtrd', '( %s -> %s = 1 )' % (R0, P))
    afz = D(w, R0, 'abscld', [fzc], '( abs ` ( F ` Z ) ) e. RR'); afz0 = D(w, R0, 'absge0d', [fzc], '0 <_ ( abs ` ( F ` Z ) )')
    alr = D(w, R0, 'remulcld', [ar, D(w, R0, 'readdcld', [a1(w, R0, '1re', '1 e. RR'), lr], '( 1 + L ) e. RR')], '%s e. RR' % AL)
    m1 = D(w, R0, 'lemul12ad', [afz, alr, gr, rr81(w, R0), afz0, g0, fb2, g81], '( ( abs ` ( F ` Z ) ) x. %s ) <_ ( %s x. ; 8 1 )' % (G, AL))
    FG = '( ( abs ` ( F ` Z ) ) x. %s )' % G
    fgc = D(w, R0, 'recnd', [D(w, R0, 'remulcld', [afz, gr], '%s e. RR' % FG)], '%s e. CC' % FG)
    pe = w.s([E(w, R0, 'oveq2d', [p3], '( %s x. %s )' % (FG, P), '( %s x. 1 )' % FG), D(w, R0, 'mulridd', [fgc], '( %s x. 1 ) = %s' % (FG, FG))], 'eqtrd',
             '( %s -> ( %s x. %s ) = %s )' % (R0, FG, P, FG))
    m2 = w.s([pe, m1], 'eqbrtrd', '( %s -> ( %s x. %s ) <_ ( %s x. ; 8 1 ) )' % (R0, FG, P, AL))
    clf = Closure(w, R0, {'( %s x. %s )' % (FG, P): ('RR', D(w, R0, 'remulcld', [D(w, R0, 'remulcld', [afz, gr], '%s e. RR' % FG), D(w, R0, 'reefcld', [D(w, R0, 'remulcld', [D(w, R0, 'resubcld', [srr, srr], '( %s - %s ) e. RR' % (SRL, SRL)), cr], '( ( %s - %s ) x. C ) e. RR' % (SRL, SRL))], '%s e. RR' % P)], '( %s x. %s ) e. RR' % (FG, P))),
                          'A': ('RR', ar), 'L': ('RR', lr)})
    clf.atom('( %s x. %s )' % (FG, P))
    fin = linarith(w, R0, [m2], '( %s x. %s ) <_ %s' % (FG, P, Q81), closure=clf, products=True)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2cvxl
if __name__ == '__main__' and (not only or 'zl2cvxl' in only):
    w = W('zl2cvxl', 'The left edge of the convexity strip: on ` Re z = sigma_L = - 1 / L ` the normalized modulus is at most ` 81 A ( 1 + L ) ` '
          '( LConvexity 1054-1116, ` hleft ` : the left-edge bound LFT at ` z ` , ~ zl2tab , ~ zl2gau , ` e ^ 4 <_ 81 ` , ~ zl2cvxm ).')
    L0 = STATEMENTS['zl2cvxl'].split(' -> ( ( ( abs ` ( F ` Z ) )')[0][2:]
    DDS = QT('S'); BBS = BB(DDS); U = '( 1 / L )'
    EXPEQ = '( exp ` ( ( %s - %s ) x. C ) ) = ( 1 / %s )' % (SLL, SRL, BBS)
    D13 = '( %s ^c %s ) <_ 3' % (DDS, U)
    ZP = '( ( Z e. CC /\\ ( F ` Z ) e. CC ) /\\ ( Re ` Z ) = %s )' % SLL
    P1 = '( ( ( N e. NN /\\ A e. RR+ ) /\\ ( L e. RR+ /\\ 2 <_ L ) ) /\\ ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ ( 3 / 2 ) ) ) )'
    P2 = '( ( ( C e. RR /\\ %s ) /\\ %s ) /\\ ( %s /\\ %s ) )' % (EXPEQ, D13, LFT(), ZP)
    assert L0 == '( %s /\\ %s )' % (P1, P2), L0
    p1 = D(w, L0, 'simpl', [], P1); p2 = D(w, L0, 'simpr', [], P2)
    nal = D(w, L0, 'simpld', [p1], '( ( N e. NN /\\ A e. RR+ ) /\\ ( L e. RR+ /\\ 2 <_ L ) )')
    ss = D(w, L0, 'simprd', [p1], '( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ ( 3 / 2 ) ) )')
    na = D(w, L0, 'simpld', [nal], '( N e. NN /\\ A e. RR+ )'); ll = D(w, L0, 'simprd', [nal], '( L e. RR+ /\\ 2 <_ L )')
    nn = D(w, L0, 'simpld', [na], 'N e. NN'); arp = D(w, L0, 'simprd', [na], 'A e. RR+')
    lrp = D(w, L0, 'simpld', [ll], 'L e. RR+'); l2 = D(w, L0, 'simprd', [ll], '2 <_ L')
    sc = D(w, L0, 'simpld', [ss], 'S e. CC'); sb = D(w, L0, 'simprd', [ss], '( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ ( 3 / 2 ) )')
    s0 = D(w, L0, 'simpld', [sb], '0 <_ ( Re ` S )'); s32 = D(w, L0, 'simprd', [sb], '( Re ` S ) <_ ( 3 / 2 )')
    c13 = D(w, L0, 'simpld', [p2], '( ( C e. RR /\\ %s ) /\\ %s )' % (EXPEQ, D13)); lz = D(w, L0, 'simprd', [p2], '( %s /\\ %s )' % (LFT(), ZP))
    ce = D(w, L0, 'simpld', [c13], '( C e. RR /\\ %s )' % EXPEQ); d13 = D(w, L0, 'simprd', [c13], D13)
    cr = D(w, L0, 'simpld', [ce], 'C e. RR'); eq = D(w, L0, 'simprd', [ce], EXPEQ)
    lft = D(w, L0, 'simpld', [lz], LFT()); zz = D(w, L0, 'simprd', [lz], ZP)
    zf = D(w, L0, 'simpld', [zz], '( Z e. CC /\\ ( F ` Z ) e. CC )'); rz = D(w, L0, 'simprd', [zz], '( Re ` Z ) = %s' % SLL)
    zc = D(w, L0, 'simpld', [zf], 'Z e. CC'); fzc = D(w, L0, 'simprd', [zf], '( F ` Z ) e. CC')
    urp, ur, uc, u0, ugt, u12 = uparts(w, L0, lrp, l2)
    lr = D(w, L0, 'rpred', [lrp], 'L e. RR'); lc = D(w, L0, 'rpcnd', [lrp], 'L e. CC'); lne = D(w, L0, 'rpne0d', [lrp], 'L =/= 0')
    ar = D(w, L0, 'rpred', [arp], 'A e. RR'); a0 = D(w, L0, 'rpge0d', [arp], '0 <_ A')
    nrp = D(w, L0, 'nnrpd', [nn], 'N e. RR+'); nr = D(w, L0, 'rpred', [nrp], 'N e. RR'); n0 = D(w, L0, 'rpge0d', [nrp], '0 <_ N')
    slr = D(w, L0, 'renegcld', [ur], '%s e. RR' % SLL)
    rsr = D(w, L0, 'recld', [sc], '( Re ` S ) e. RR')
    cl = Closure(w, L0, {U: ('RR', ur), '( Re ` S )': ('RR', rsr), 'A': ('RR', ar), 'L': ('RR', lr)})
    cl.atom(U)
    sl12 = linarith(w, L0, [u12], '-u ( 1 / 2 ) <_ %s' % SLL, closure=cl)
    sl0 = linarith(w, L0, [ugt], '%s < 0' % SLL, closure=cl)
    rz1 = w.s([sl12, rz], 'breqtrrd', '( %s -> -u ( 1 / 2 ) <_ ( Re ` Z ) )' % L0)
    rz2 = w.s([rz, sl0], 'eqbrtrd', '( %s -> ( Re ` Z ) < 0 )' % L0)
    fb0, fbb = inst_ral_t(w, L0, lft, 'CC', LFT()[len('A. z e. CC '):], 'Z', zc)
    LB = LFTB('Z')
    fb = w.s([fb0, w.s([rz1, rz2], 'jca', '( %s -> ( -u ( 1 / 2 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) < 0 ) )' % L0)], 'mpd', '( %s -> ( abs ` ( F ` Z ) ) <_ %s )' % (L0, LB))
    # 1 + 1 / - Re Z = 1 + L ; 1 / 2 - Re Z = 1 / 2 + 1 / L
    n1 = w.s([E(w, L0, 'negeqd', [rz], '-u ( Re ` Z )', '-u %s' % SLL), D(w, L0, 'negnegd', [uc], '-u %s = %s' % (SLL, U))], 'eqtrd', '( %s -> -u ( Re ` Z ) = %s )' % (L0, U))
    n2 = w.s([E(w, L0, 'oveq2d', [n1], '( 1 / -u ( Re ` Z ) )', '( 1 / %s )' % U), D(w, L0, 'recrecd', [lc, lne], '( 1 / %s ) = L' % U)], 'eqtrd', '( %s -> ( 1 / -u ( Re ` Z ) ) = L )' % L0)
    K1 = '( ( ; 1 2 x. A ) x. ( 1 + L ) )'
    k1eq = E(w, L0, 'oveq2d', [E(w, L0, 'oveq2d', [n2], '( 1 + ( 1 / -u ( Re ` Z ) ) )', '( 1 + L )')], '( ( ; 1 2 x. A ) x. ( 1 + ( 1 / -u ( Re ` Z ) ) ) )', K1)
    EX = '( ( 1 / 2 ) + %s )' % U
    exeq = w.s([E(w, L0, 'oveq2d', [rz], '( ( 1 / 2 ) - ( Re ` Z ) )', '( ( 1 / 2 ) - %s )' % SLL), D(w, L0, 'subnegd', [a1(w, L0, 'halfcn', '( 1 / 2 ) e. CC'), uc], '( ( 1 / 2 ) - %s ) = %s' % (SLL, EX))],
               'eqtrd', '( %s -> ( ( 1 / 2 ) - ( Re ` Z ) ) = %s )' % (L0, EX))
    QTZ = QT('Z')
    fb2 = w.s([fb, E(w, L0, 'oveq12d', [k1eq, E(w, L0, 'oveq2d', [exeq], '( %s ^c ( ( 1 / 2 ) - ( Re ` Z ) ) )' % QTZ, '( %s ^c %s )' % (QTZ, EX))], LB, '( %s x. ( %s ^c %s ) )' % (K1, QTZ, EX))],
              'breqtrd', '( %s -> ( abs ` ( F ` Z ) ) <_ ( %s x. ( %s ^c %s ) ) )' % (L0, K1, QTZ, EX))
    # the base: N ( | Im Z | + 2 ) <_ D ( 1 + | Im Z - Im S | )
    izr = D(w, L0, 'imcld', [zc], '( Im ` Z ) e. RR'); isr = D(w, L0, 'imcld', [sc], '( Im ` S ) e. RR')
    aiz = D(w, L0, 'abscld', [D(w, L0, 'recnd', [izr], '( Im ` Z ) e. CC')], '( abs ` ( Im ` Z ) ) e. RR')
    aiz0 = D(w, L0, 'absge0d', [D(w, L0, 'recnd', [izr], '( Im ` Z ) e. CC')], '0 <_ ( abs ` ( Im ` Z ) )')
    ais = D(w, L0, 'abscld', [D(w, L0, 'recnd', [isr], '( Im ` S ) e. CC')], '( abs ` ( Im ` S ) ) e. RR')
    ais0 = D(w, L0, 'absge0d', [D(w, L0, 'recnd', [isr], '( Im ` S ) e. CC')], '0 <_ ( abs ` ( Im ` S ) )')
    VG = '( ( Im ` Z ) - ( Im ` S ) )'
    vgr = D(w, L0, 'resubcld', [izr, isr], '%s e. RR' % VG)
    avg = D(w, L0, 'abscld', [D(w, L0, 'recnd', [vgr], '%s e. CC' % VG)], '( abs ` %s ) e. RR' % VG)
    avg0 = D(w, L0, 'absge0d', [D(w, L0, 'recnd', [vgr], '%s e. CC' % VG)], '0 <_ ( abs ` %s )' % VG)
    V1 = '( 1 + ( abs ` %s ) )' % VG
    v1r = D(w, L0, 'readdcld', [a1(w, L0, '1re', '1 e. RR'), avg], '%s e. RR' % V1)
    clv = Closure(w, L0, {'( abs ` %s )' % VG: ('RR', avg), '( abs ` ( Im ` Z ) )': ('RR', aiz), '( abs ` ( Im ` S ) )': ('RR', ais)})
    v10 = linarith(w, L0, [avg0], '0 <_ %s' % V1, closure=clv)
    v11 = linarith(w, L0, [avg0], '1 <_ %s' % V1, closure=clv)
    tab = w.s([izr, isr, w.inst('zl2tab')], 'syl2anc', '( %s -> ( ( abs ` ( Im ` Z ) ) + 2 ) <_ ( ( ( abs ` ( Im ` S ) ) + 2 ) x. %s ) )' % (L0, V1))
    QZ = '( ( abs ` ( Im ` Z ) ) + 2 )'; QS = '( ( abs ` ( Im ` S ) ) + 2 )'
    qzr = D(w, L0, 'readdcld', [aiz, a1(w, L0, '2re', '2 e. RR')], '%s e. RR' % QZ)
    qsr = D(w, L0, 'readdcld', [ais, a1(w, L0, '2re', '2 e. RR')], '%s e. RR' % QS)
    qs0 = linarith(w, L0, [ais0], '0 < %s' % QS, closure=clv)
    qsrp = D(w, L0, 'elrpd', [qsr, qs0], '%s e. RR+' % QS)
    b1 = D(w, L0, 'lemul2ad', [qzr, D(w, L0, 'remulcld', [qsr, v1r], '( %s x. %s ) e. RR' % (QS, V1)), nr, n0, tab], '( N x. %s ) <_ ( N x. ( %s x. %s ) )' % (QZ, QS, V1))
    b2 = w.s([D(w, L0, 'mulassd', [D(w, L0, 'recnd', [nr], 'N e. CC'), D(w, L0, 'recnd', [qsr], '%s e. CC' % QS), D(w, L0, 'recnd', [v1r], '%s e. CC' % V1)],
                '( %s x. %s ) = ( N x. ( %s x. %s ) )' % (DDS, V1, QS, V1))], 'eqcomd', '( %s -> ( N x. ( %s x. %s ) ) = ( %s x. %s ) )' % (L0, QS, V1, DDS, V1))
    base = w.s([b1, b2], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (L0, QTZ, DDS, V1))
    qtzr = D(w, L0, 'remulcld', [nr, qzr], '%s e. RR' % QTZ)
    qtz0 = D(w, L0, 'mulge0d', [nr, qzr, n0, linarith(w, L0, [aiz0], '0 <_ %s' % QZ, closure=clv)], '0 <_ %s' % QTZ)
    ddsrp = D(w, L0, 'rpmulcld', [nrp, qsrp], '%s e. RR+' % DDS)
    ddsr = D(w, L0, 'rpred', [ddsrp], '%s e. RR' % DDS); dds0 = D(w, L0, 'rpge0d', [ddsrp], '0 <_ %s' % DDS)
    ddsc = D(w, L0, 'rpcnd', [ddsrp], '%s e. CC' % DDS); ddsne = D(w, L0, 'rpne0d', [ddsrp], '%s =/= 0' % DDS)
    dv1r = D(w, L0, 'remulcld', [ddsr, v1r], '( %s x. %s ) e. RR' % (DDS, V1))
    exr = D(w, L0, 'readdcld', [a1(w, L0, 'halfre', '( 1 / 2 ) e. RR'), ur], '%s e. RR' % EX)
    exc = D(w, L0, 'recnd', [exr], '%s e. CC' % EX)
    ex0 = linarith(w, L0, [u0], '0 <_ %s' % EX, closure=cl)
    ex1 = linarith(w, L0, [u12], '%s <_ 1' % EX, closure=cl)
    c1 = D(w, L0, 'cxple2ad', [qtzr, qtz0, dv1r, exr, ex0, base], '( %s ^c %s ) <_ ( ( %s x. %s ) ^c %s )' % (QTZ, EX, DDS, V1, EX))
    c2 = D(w, L0, 'mulcxpd', [ddsr, dds0, v1r, v10, exc], '( ( %s x. %s ) ^c %s ) = ( ( %s ^c %s ) x. ( %s ^c %s ) )' % (DDS, V1, EX, DDS, EX, V1, EX))
    c3 = D(w, L0, 'cxplead', [v1r, v11, exr, a1(w, L0, '1re', '1 e. RR'), ex1], '( %s ^c %s ) <_ ( %s ^c 1 )' % (V1, EX, V1))
    c34 = w.s([c3, D(w, L0, 'cxp1d', [D(w, L0, 'recnd', [v1r], '%s e. CC' % V1)], '( %s ^c 1 ) = %s' % (V1, V1))], 'breqtrd', '( %s -> ( %s ^c %s ) <_ %s )' % (L0, V1, EX, V1))
    DE = '( %s ^c %s )' % (DDS, EX)
    der = D(w, L0, 'recxpcld', [ddsr, dds0, exr], '%s e. RR' % DE); de0 = D(w, L0, 'cxpge0d', [ddsr, dds0, exr], '0 <_ %s' % DE)
    v1er = D(w, L0, 'recxpcld', [v1r, v10, exr], '( %s ^c %s ) e. RR' % (V1, EX))
    c5 = D(w, L0, 'lemul2ad', [v1er, v1r, der, de0, c34], '( %s x. ( %s ^c %s ) ) <_ ( %s x. %s )' % (DE, V1, EX, DE, V1))
    X = '( %s ^c ( 1 / 2 ) )' % DDS; Y = '( %s ^c %s )' % (DDS, U); XY = '( %s x. %s )' % (X, Y)
    c6 = D(w, L0, 'cxpaddd', [ddsc, ddsne, a1(w, L0, 'halfcn', '( 1 / 2 ) e. CC'), uc], '%s = %s' % (DE, XY))
    c7 = E(w, L0, 'oveq1d', [c6], '( %s x. %s )' % (DE, V1), '( %s x. %s )' % (XY, V1))
    r1 = w.s([c1, c2], 'breqtrd', '( %s -> ( %s ^c %s ) <_ ( %s x. ( %s ^c %s ) ) )' % (L0, QTZ, EX, DE, V1, EX))
    qer = D(w, L0, 'recxpcld', [qtzr, qtz0, exr], '( %s ^c %s ) e. RR' % (QTZ, EX))
    r2 = D(w, L0, 'letrd', [qer, D(w, L0, 'remulcld', [der, v1er], '( %s x. ( %s ^c %s ) ) e. RR' % (DE, V1, EX)), D(w, L0, 'remulcld', [der, v1r], '( %s x. %s ) e. RR' % (DE, V1)), r1, c5],
            '( %s ^c %s ) <_ ( %s x. %s )' % (QTZ, EX, DE, V1))
    r3 = w.s([r2, c7], 'breqtrd', '( %s -> ( %s ^c %s ) <_ ( %s x. %s ) )' % (L0, QTZ, EX, XY, V1))
    xrp = D(w, L0, 'rpcxpcld', [ddsrp, a1(w, L0, 'halfre', '( 1 / 2 ) e. RR')], '%s e. RR+' % X)
    xr = D(w, L0, 'rpred', [xrp], '%s e. RR' % X); x0 = D(w, L0, 'rpge0d', [xrp], '0 <_ %s' % X)
    yrp = D(w, L0, 'rpcxpcld', [ddsrp, ur], '%s e. RR+' % Y)
    yr = D(w, L0, 'rpred', [yrp], '%s e. RR' % Y); y0 = D(w, L0, 'rpge0d', [yrp], '0 <_ %s' % Y)
    xyv = D(w, L0, 'remulcld', [D(w, L0, 'remulcld', [xr, yr], '%s e. RR' % XY), v1r], '( %s x. %s ) e. RR' % (XY, V1))
    n12r = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0rei', '; 1 2 e. RR')], 'a1i', '( %s -> ; 1 2 e. RR )' % L0)
    n120 = w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0ge0i', '0 <_ ; 1 2')], 'a1i', '( %s -> 0 <_ ; 1 2 )' % L0)
    a12r = D(w, L0, 'remulcld', [n12r, ar], '( ; 1 2 x. A ) e. RR'); a120 = D(w, L0, 'mulge0d', [n12r, ar, n120, a0], '0 <_ ( ; 1 2 x. A )')
    l1r = D(w, L0, 'readdcld', [a1(w, L0, '1re', '1 e. RR'), lr], '( 1 + L ) e. RR'); l10 = linarith(w, L0, [D(w, L0, 'rpge0d', [lrp], '0 <_ L')], '0 <_ ( 1 + L )', closure=cl)
    k1r = D(w, L0, 'remulcld', [a12r, l1r], '%s e. RR' % K1); k10 = D(w, L0, 'mulge0d', [a12r, l1r, a120, l10], '0 <_ %s' % K1)
    fb3a = D(w, L0, 'lemul2ad', [qer, xyv, k1r, k10, r3], '( %s x. ( %s ^c %s ) ) <_ ( %s x. ( %s x. %s ) )' % (K1, QTZ, EX, K1, XY, V1))
    afz = D(w, L0, 'abscld', [fzc], '( abs ` ( F ` Z ) ) e. RR'); afz0 = D(w, L0, 'absge0d', [fzc], '0 <_ ( abs ` ( F ` Z ) )')
    B1 = '( %s x. ( %s x. %s ) )' % (K1, XY, V1)
    fb3 = D(w, L0, 'letrd', [afz, D(w, L0, 'remulcld', [k1r, qer], '( %s x. ( %s ^c %s ) ) e. RR' % (K1, QTZ, EX)), D(w, L0, 'remulcld', [k1r, xyv], '%s e. RR' % B1), fb2, fb3a],
             '( abs ` ( F ` Z ) ) <_ %s' % B1)
    # the Gaussian
    XG = '( %s - ( Re ` S ) )' % SLL
    xgr = D(w, L0, 'resubcld', [slr, rsr], '%s e. RR' % XG)
    xg2 = linarith(w, L0, [sl12, s32], '-u 2 <_ %s' % XG, closure=cl)
    xg0 = linarith(w, L0, [sl0, s0], '%s <_ 0' % XG, closure=cl)
    clx = Closure(w, L0, {XG: ('RR', xgr)}); clx.atom(XG)
    sq4 = nlinarith(w, L0, [xg2, xg0], '( %s ^ 2 ) <_ 4' % XG, closure=clx)
    gb, hr, h0 = gauss81(w, L0, XG, VG, xgr, vgr, sq4)
    G = GAUS(SLL)
    H = '( exp ` -u ( %s ^ 2 ) )' % VG
    gr, g0 = efpos(w, L0, '( ( %s ^ 2 ) - ( %s ^ 2 ) )' % (XG, VG), D(w, L0, 'resubcld', [D(w, L0, 'resqcld', [xgr], '( %s ^ 2 ) e. RR' % XG), D(w, L0, 'resqcld', [vgr], '( %s ^ 2 ) e. RR' % VG)],
                                                                          '( ( %s ^ 2 ) - ( %s ^ 2 ) ) e. RR' % (XG, VG)))
    vh3 = w.s([vgr, w.inst('zl2gau')], 'syl', '( %s -> ( %s x. %s ) <_ 3 )' % (L0, V1, H))
    # the power factor 1 / b and 108 X P = 1
    P = '( exp ` ( ( %s - %s ) x. C ) )' % (SLL, SRL)
    bbrp = D(w, L0, 'rpmulcld', [rp108(w, L0), xrp], '%s e. RR+' % BBS)
    rbrp = D(w, L0, 'rpreccld', [bbrp], '( 1 / %s ) e. RR+' % BBS)
    pr = w.s([eq, D(w, L0, 'rpred', [rbrp], '( 1 / %s ) e. RR' % BBS)], 'eqeltrd', '( %s -> %s e. RR )' % (L0, P))
    p0 = w.s([D(w, L0, 'rpge0d', [rbrp], '0 <_ ( 1 / %s )' % BBS), eq], 'breqtrrd', '( %s -> 0 <_ %s )' % (L0, P))
    pc = D(w, L0, 'recnd', [pr], '%s e. CC' % P)
    xp1 = w.s([D(w, L0, 'mulassd', [w.s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; ; 1 0 8 e. NN0')], 'nn0cni', '; ; 1 0 8 e. CC')], 'a1i', '( %s -> ; ; 1 0 8 e. CC )' % L0),
                                     D(w, L0, 'rpcnd', [xrp], '%s e. CC' % X), pc], '( ( ; ; 1 0 8 x. %s ) x. %s ) = ( ; ; 1 0 8 x. ( %s x. %s ) )' % (X, P, X, P))], 'eqcomd',
              '( %s -> ( ; ; 1 0 8 x. ( %s x. %s ) ) = ( %s x. %s ) )' % (L0, X, P, BBS, P))
    xp2 = E(w, L0, 'oveq2d', [eq], '( %s x. %s )' % (BBS, P), '( %s x. ( 1 / %s ) )' % (BBS, BBS))
    xp3 = D(w, L0, 'recidd', [D(w, L0, 'rpcnd', [bbrp], '%s e. CC' % BBS), D(w, L0, 'rpne0d', [bbrp], '%s =/= 0' % BBS)], '( %s x. ( 1 / %s ) ) = 1' % (BBS, BBS))
    xp = chain(w, L0, ['( ; ; 1 0 8 x. ( %s x. %s ) )' % (X, P), '( %s x. %s )' % (BBS, P), '( %s x. ( 1 / %s ) )' % (BBS, BBS), '1'], [xp1, xp2, xp3])
    # zl2cvxm at G = K1
    hm = w.s([w.s([w.s([k1r, k10], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (L0, K1, K1)),
                   w.s([w.s([xr, x0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (L0, X, X)), w.s([yr, w.s([y0, d13], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ 3 ) )' % (L0, Y, Y))], 'jca', '( %s -> ( %s e. RR /\\ ( 0 <_ %s /\\ %s <_ 3 ) ) )' % (L0, Y, Y, Y))], 'jca',
                       '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ ( 0 <_ %s /\\ %s <_ 3 ) ) ) )' % (L0, X, X, Y, Y, Y))], 'jca',
                  '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ ( 0 <_ %s /\\ %s <_ 3 ) ) ) ) )' % (L0, K1, K1, X, X, Y, Y, Y)),
              w.s([w.s([w.s([v1r, v10], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (L0, V1, V1)), w.s([hr, w.s([h0, vh3], 'jca', '( %s -> ( 0 <_ %s /\\ ( %s x. %s ) <_ 3 ) )' % (L0, H, V1, H))], 'jca',
                                                                                                        '( %s -> ( %s e. RR /\\ ( 0 <_ %s /\\ ( %s x. %s ) <_ 3 ) ) )' % (L0, H, H, V1, H))], 'jca',
                       '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ ( 0 <_ %s /\\ ( %s x. %s ) <_ 3 ) ) ) )' % (L0, V1, V1, H, H, V1, H)),
                   w.s([w.s([pr, p0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (L0, P, P)), xp], 'jca', '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( ; ; 1 0 8 x. ( %s x. %s ) ) = 1 ) )' % (L0, P, P, X, P))], 'jca',
                  '( %s -> ( ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. RR /\\ ( 0 <_ %s /\\ ( %s x. %s ) <_ 3 ) ) ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( ; ; 1 0 8 x. ( %s x. %s ) ) = 1 ) ) )' % (L0, V1, V1, H, H, V1, H, P, P, X, P))],
             'jca', '( %s -> %s )' % (L0, subst(STATEMENTS['zl2cvxm'].split(' -> ( ( ( G x.')[0][2:], {'G': K1, 'X': X, 'Y': Y, 'V': V1, 'H': H, 'P': P})))
    BIG = '( ( ( %s x. ( %s x. %s ) ) x. ( ; 8 1 x. %s ) ) x. %s )' % (K1, XY, V1, H, P)
    mres = w.s([hm, w.inst('zl2cvxm')], 'syl', '( %s -> %s <_ ( ( ; 2 7 / 4 ) x. %s ) )' % (L0, BIG, K1))
    h81r = D(w, L0, 'remulcld', [rr81(w, L0), hr], '( ; 8 1 x. %s ) e. RR' % H)
    m1 = D(w, L0, 'lemul12ad', [afz, D(w, L0, 'remulcld', [k1r, xyv], '%s e. RR' % B1), gr, h81r, afz0, g0, fb3, gb], '( ( abs ` ( F ` Z ) ) x. %s ) <_ ( %s x. ( ; 8 1 x. %s ) )' % (G, B1, H))
    FG = '( ( abs ` ( F ` Z ) ) x. %s )' % G
    fgr = D(w, L0, 'remulcld', [afz, gr], '%s e. RR' % FG)
    m2 = D(w, L0, 'lemul1ad', [fgr, D(w, L0, 'remulcld', [D(w, L0, 'remulcld', [k1r, xyv], '%s e. RR' % B1), h81r], '( %s x. ( ; 8 1 x. %s ) ) e. RR' % (B1, H)), pr, p0, m1],
           '( %s x. %s ) <_ %s' % (FG, P, BIG))
    FGP = '( %s x. %s )' % (FG, P)
    fgpr = D(w, L0, 'remulcld', [fgr, pr], '%s e. RR' % FGP)
    bigr = D(w, L0, 'remulcld', [D(w, L0, 'remulcld', [D(w, L0, 'remulcld', [k1r, xyv], '%s e. RR' % B1), h81r], '( %s x. ( ; 8 1 x. %s ) ) e. RR' % (B1, H)), pr], '%s e. RR' % BIG)
    r27 = w.s([w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '7nn0', '7 e. NN0')], 'deccl', '; 2 7 e. NN0')], 'nn0rei', '; 2 7 e. RR'), w.s([], '4re', '4 e. RR'), w.s([], '4ne0', '4 =/= 0')], 'redivcli', '( ; 2 7 / 4 ) e. RR')],
             'a1i', '( %s -> ( ; 2 7 / 4 ) e. RR )' % L0)
    m3 = D(w, L0, 'letrd', [fgpr, bigr, D(w, L0, 'remulcld', [r27, k1r], '( ( ; 2 7 / 4 ) x. %s ) e. RR' % K1), m2, mres], '%s <_ ( ( ; 2 7 / 4 ) x. %s )' % (FGP, K1))
    clf = Closure(w, L0, {FGP: ('RR', fgpr), 'A': ('RR', ar), 'L': ('RR', lr)}); clf.atom(FGP)
    fin = linarith(w, L0, [m3], '%s <_ %s' % (FGP, Q81), closure=clf, products=True)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2cvxu
if __name__ == '__main__' and (not only or 'zl2cvxu' in only):
    w = W('zl2cvxu', 'Unwinding the Phragmen-Lindeloef conclusion of the convexity proof: from ` V e ^ ( ( Re S - sigma_R ) c ) <_ 81 A ( 1 + L ) ` , '
          '` V <_ 26244 A ( 1 + L ) D ^ max ( ( 1 - Re S ) / 2 , 0 ) ` ( LConvexity 1178-1252: ` hLs ` , ` hbtheta ` , ` hthetahalf ` , ` hbthetale ` ).')
    U0 = STATEMENTS['zl2cvxu'].split(' -> V <_ ')[0][2:]
    U = '( 1 / L )'; D13 = '( D ^c %s ) <_ 3' % U; CCD = CCL('D'); BBD = BB('D'); RS = '( Re ` S )'
    EP = '( exp ` ( ( %s - %s ) x. %s ) )' % (RS, SRL, CCD)
    ad = D(w, U0, 'simpll', [], '( A e. RR+ /\\ ( D e. RR+ /\\ 1 <_ D ) )')
    ld = D(w, U0, 'simplr', [], '( ( L e. RR+ /\\ 2 <_ L ) /\\ %s )' % D13)
    sv = D(w, U0, 'simpr', [], '( ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) ) /\\ ( V e. RR /\\ ( V x. %s ) <_ %s ) )' % (RS, RS, SRL, EP, Q81))
    arp = D(w, U0, 'simpld', [ad], 'A e. RR+'); dd = D(w, U0, 'simprd', [ad], '( D e. RR+ /\\ 1 <_ D )')
    drp = D(w, U0, 'simpld', [dd], 'D e. RR+'); d1 = D(w, U0, 'simprd', [dd], '1 <_ D')
    l_ = D(w, U0, 'simpld', [ld], '( L e. RR+ /\\ 2 <_ L )'); d13 = D(w, U0, 'simprd', [ld], D13)
    lrp = D(w, U0, 'simpld', [l_], 'L e. RR+'); l2 = D(w, U0, 'simprd', [l_], '2 <_ L')
    ss = D(w, U0, 'simpld', [sv], '( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) )' % (RS, RS, SRL)); vv = D(w, U0, 'simprd', [sv], '( V e. RR /\\ ( V x. %s ) <_ %s )' % (EP, Q81))
    sc = D(w, U0, 'simpld', [ss], 'S e. CC'); sb = D(w, U0, 'simprd', [ss], '( 0 <_ %s /\\ %s <_ %s )' % (RS, RS, SRL))
    s0 = D(w, U0, 'simpld', [sb], '0 <_ %s' % RS); ssr = D(w, U0, 'simprd', [sb], '%s <_ %s' % (RS, SRL))
    vr = D(w, U0, 'simpld', [vv], 'V e. RR'); vb = D(w, U0, 'simprd', [vv], '( V x. %s ) <_ %s' % (EP, Q81))
    urp, ur, uc, u0, ugt, u12 = uparts(w, U0, lrp, l2)
    lr = D(w, U0, 'rpred', [lrp], 'L e. RR'); l0 = D(w, U0, 'rpge0d', [lrp], '0 <_ L')
    dr = D(w, U0, 'rpred', [drp], 'D e. RR'); dc = D(w, U0, 'rpcnd', [drp], 'D e. CC'); dne = D(w, U0, 'rpne0d', [drp], 'D =/= 0'); d0 = D(w, U0, 'rpge0d', [drp], '0 <_ D')
    ar = D(w, U0, 'rpred', [arp], 'A e. RR'); a0 = D(w, U0, 'rpge0d', [arp], '0 <_ A')
    rsr = D(w, U0, 'recld', [sc], '%s e. RR' % RS); rsc = D(w, U0, 'recnd', [rsr], '%s e. CC' % RS)
    cl = Closure(w, U0, {U: ('RR', ur), RS: ('RR', rsr), 'A': ('RR', ar), 'L': ('RR', lr)})
    cl.atom(U)
    srr = D(w, U0, 'readdcld', [a1(w, U0, '1re', '1 e. RR'), ur], '%s e. RR' % SRL); src = D(w, U0, 'recnd', [srr], '%s e. CC' % SRL)
    slr = D(w, U0, 'renegcld', [ur], '%s e. RR' % SLL)
    wwr = D(w, U0, 'resubcld', [srr, slr], '%s e. RR' % WWL)
    wwrp = D(w, U0, 'elrpd', [wwr, linarith(w, U0, [ugt], '0 < %s' % WWL, closure=cl)], '%s e. RR+' % WWL)
    wwc = D(w, U0, 'recnd', [wwr], '%s e. CC' % WWL); wwne = D(w, U0, 'rpne0d', [wwrp], '%s =/= 0' % WWL)
    DH = '( D ^c ( 1 / 2 ) )'
    half = a1(w, U0, 'halfre', '( 1 / 2 ) e. RR')
    h0 = w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], 'halfgt0', '0 < ( 1 / 2 )')], 'ltleii', '0 <_ ( 1 / 2 )')], 'a1i', '( %s -> 0 <_ ( 1 / 2 ) )' % U0)
    dhrp = D(w, U0, 'rpcxpcld', [drp, half], '%s e. RR+' % DH); dhr = D(w, U0, 'rpred', [dhrp], '%s e. RR' % DH); dh0 = D(w, U0, 'rpge0d', [dhrp], '0 <_ %s' % DH)
    dh1 = w.s([D(w, U0, 'cxp0d', [dc], '( D ^c 0 ) = 1'), D(w, U0, 'cxplead', [dr, d1, a1(w, U0, '0re', '0 e. RR'), half, h0], '( D ^c 0 ) <_ %s' % DH)], 'eqbrtrrd', '( %s -> 1 <_ %s )' % (U0, DH))
    bbrp = D(w, U0, 'rpmulcld', [rp108(w, U0), dhrp], '%s e. RR+' % BBD)
    bbr = D(w, U0, 'rpred', [bbrp], '%s e. RR' % BBD); bbc = D(w, U0, 'rpcnd', [bbrp], '%s e. CC' % BBD); bbne = D(w, U0, 'rpne0d', [bbrp], '%s =/= 0' % BBD)
    bb1 = linarith(w, U0, [dh1], '1 <_ %s' % BBD, leaves={DH: dhr})
    LB = '( log ` %s )' % BBD
    lbr = D(w, U0, 'relogcld', [bbrp], '%s e. RR' % LB); lbc = D(w, U0, 'recnd', [lbr], '%s e. CC' % LB); lb0 = D(w, U0, 'logge0d', [bbr, bb1], '0 <_ %s' % LB)
    ccr = D(w, U0, 'redivcld', [lbr, wwr, wwne], '%s e. RR' % CCD); ccc = D(w, U0, 'recnd', [ccr], '%s e. CC' % CCD)
    XS = '( %s - %s )' % (SRL, RS)
    xsr = D(w, U0, 'resubcld', [srr, rsr], '%s e. RR' % XS); xsc = D(w, U0, 'recnd', [xsr], '%s e. CC' % XS)
    xs0 = linarith(w, U0, [ssr], '0 <_ %s' % XS, closure=cl)
    TH = '( %s / %s )' % (XS, WWL)
    thr = D(w, U0, 'redivcld', [xsr, wwr, wwne], '%s e. RR' % TH); thc = D(w, U0, 'recnd', [thr], '%s e. CC' % TH)
    th0 = D(w, U0, 'divge0d', [xsr, wwrp, xs0], '0 <_ %s' % TH)
    xsww = linarith(w, U0, [s0, u0], '%s <_ %s' % (XS, WWL), closure=cl)
    th1 = w.s([xsww, w.s([xsr, wwrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> %s <_ %s ) )' % (U0, TH, XS, WWL))], 'mpbird', '( %s -> %s <_ 1 )' % (U0, TH))
    # V <_ e ^ ( ( sigma_R - Re S ) c ) 81 A ( 1 + L )
    EN = '( exp ` ( %s x. %s ) )' % (XS, CCD)
    xcr = D(w, U0, 'remulcld', [xsr, ccr], '( %s x. %s ) e. RR' % (XS, CCD)); xcc = D(w, U0, 'recnd', [xcr], '( %s x. %s ) e. CC' % (XS, CCD))
    enrp = D(w, U0, 'rpefcld', [xcr], '%s e. RR+' % EN); enr = D(w, U0, 'rpred', [enrp], '%s e. RR' % EN); enc = D(w, U0, 'rpcnd', [enrp], '%s e. CC' % EN); enne = D(w, U0, 'rpne0d', [enrp], '%s =/= 0' % EN)
    a1_ = w.s([D(w, U0, 'negsubdi2d', [src, rsc], '-u %s = ( %s - %s )' % (XS, RS, SRL))], 'eqcomd', '( %s -> ( %s - %s ) = -u %s )' % (U0, RS, SRL, XS))
    a2 = w.s([E(w, U0, 'oveq1d', [a1_], '( ( %s - %s ) x. %s )' % (RS, SRL, CCD), '( -u %s x. %s )' % (XS, CCD)), D(w, U0, 'mulneg1d', [xsc, ccc], '( -u %s x. %s ) = -u ( %s x. %s )' % (XS, CCD, XS, CCD))],
              'eqtrd', '( %s -> ( ( %s - %s ) x. %s ) = -u ( %s x. %s ) )' % (U0, RS, SRL, CCD, XS, CCD))
    a3 = w.s([E(w, U0, 'fveq2d', [a2], EP, '( exp ` -u ( %s x. %s ) )' % (XS, CCD)), w.s([xcc, w.inst('efneg')], 'syl', '( %s -> ( exp ` -u ( %s x. %s ) ) = ( 1 / %s ) )' % (U0, XS, CCD, EN))], 'eqtrd',
              '( %s -> %s = ( 1 / %s ) )' % (U0, EP, EN))
    vc = D(w, U0, 'recnd', [vr], 'V e. CC')
    a4 = w.s([E(w, U0, 'oveq2d', [a3], '( V x. %s )' % EP, '( V x. ( 1 / %s ) )' % EN), w.s([D(w, U0, 'divrecd', [vc, enc, enne], '( V / %s ) = ( V x. ( 1 / %s ) )' % (EN, EN))], 'eqcomd', '( %s -> ( V x. ( 1 / %s ) ) = ( V / %s ) )' % (U0, EN, EN))],
              'eqtrd', '( %s -> ( V x. %s ) = ( V / %s ) )' % (U0, EP, EN))
    a5 = w.s([a4, vb], 'eqbrtrrd', '( %s -> ( V / %s ) <_ %s )' % (U0, EN, Q81))
    l1r = D(w, U0, 'readdcld', [a1(w, U0, '1re', '1 e. RR'), lr], '( 1 + L ) e. RR'); l10 = linarith(w, U0, [l0], '0 <_ ( 1 + L )', closure=cl)
    a81r = D(w, U0, 'remulcld', [rr81(w, U0), ar], '( ; 8 1 x. A ) e. RR')
    a810 = D(w, U0, 'mulge0d', [rr81(w, U0), ar, w.s([w.s([w.s([w.s([], '8nn0', '8 e. NN0'), w.s([], '1nn0', '1 e. NN0')], 'deccl', '; 8 1 e. NN0')], 'nn0ge0i', '0 <_ ; 8 1')], 'a1i', '( %s -> 0 <_ ; 8 1 )' % U0), a0], '0 <_ ( ; 8 1 x. A )')
    q81r = D(w, U0, 'remulcld', [a81r, l1r], '%s e. RR' % Q81); q810 = D(w, U0, 'mulge0d', [a81r, l1r, a810, l10], '0 <_ %s' % Q81)
    a6 = w.s([a5, D(w, U0, 'ledivmuld', [vr, q81r, enrp], '( ( V / %s ) <_ %s <-> V <_ ( %s x. %s ) )' % (EN, Q81, EN, Q81))], 'mpbid', '( %s -> V <_ ( %s x. %s ) )' % (U0, EN, Q81))
    # EN = b ^ theta
    b1 = D(w, U0, 'cxpefd', [bbc, bbne, thc], '( %s ^c %s ) = ( exp ` ( %s x. %s ) )' % (BBD, TH, TH, LB))
    b2 = w.s([w.s([D(w, U0, 'div23d', [xsc, lbc, wwc, wwne], '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (XS, LB, WWL, TH, LB))], 'eqcomd', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) / %s ) )' % (U0, TH, LB, XS, LB, WWL)),
              D(w, U0, 'divassd', [xsc, lbc, wwc, wwne], '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (XS, LB, WWL, XS, CCD))], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (U0, TH, LB, XS, CCD))
    eneq = w.s([w.s([b1, E(w, U0, 'fveq2d', [b2], '( exp ` ( %s x. %s ) )' % (TH, LB), EN)], 'eqtrd', '( %s -> ( %s ^c %s ) = %s )' % (U0, BBD, TH, EN))], 'eqcomd', '( %s -> %s = ( %s ^c %s ) )' % (U0, EN, BBD, TH))
    # b ^ theta = 108 ^ theta ( D ^ ( 1 / 2 ) ) ^ theta
    n108r = rr108(w, U0)
    n1080 = w.s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; ; 1 0 8 e. NN0')], 'nn0ge0i', '0 <_ ; ; 1 0 8')], 'a1i', '( %s -> 0 <_ ; ; 1 0 8 )' % U0)
    c0 = D(w, U0, 'mulcxpd', [n108r, n1080, dhr, dh0, thc], '( %s ^c %s ) = ( ( ; ; 1 0 8 ^c %s ) x. ( %s ^c %s ) )' % (BBD, TH, TH, DH, TH))
    one108 = linarith(w, U0, [], '1 <_ ; ; 1 0 8', closure=cl)
    c108 = D(w, U0, 'cxplead', [n108r, one108, thr, a1(w, U0, '1re', '1 e. RR'), th1], '( ; ; 1 0 8 ^c %s ) <_ ( ; ; 1 0 8 ^c 1 )' % TH)
    n108c = w.s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '0nn0', '0 e. NN0')], 'deccl', '; 1 0 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; ; 1 0 8 e. NN0')], 'nn0cni', '; ; 1 0 8 e. CC')], 'a1i', '( %s -> ; ; 1 0 8 e. CC )' % U0)
    c108b = w.s([c108, D(w, U0, 'cxp1d', [n108c], '( ; ; 1 0 8 ^c 1 ) = ; ; 1 0 8')], 'breqtrd', '( %s -> ( ; ; 1 0 8 ^c %s ) <_ ; ; 1 0 8 )' % (U0, TH))
    HT = '( ( 1 / 2 ) x. %s )' % TH
    cdh = w.s([D(w, U0, 'cxpmuld', [drp, half, thc], '( D ^c %s ) = ( %s ^c %s )' % (HT, DH, TH))], 'eqcomd', '( %s -> ( %s ^c %s ) = ( D ^c %s ) )' % (U0, DH, TH, HT))
    # ( 1 / 2 ) theta <_ EXPO + 1 / L, by cases on 1 <_ Re S
    EXP = EXPO('S')
    omr = D(w, U0, 'resubcld', [a1(w, U0, '1re', '1 e. RR'), rsr], '( 1 - %s ) e. RR' % RS)
    hlf = D(w, U0, 'redivcld', [omr, a1(w, U0, '2re', '2 e. RR'), a1(w, U0, '2ne0', '2 =/= 0')], '( ( 1 - %s ) / 2 ) e. RR' % RS)
    expor = D(w, U0, 'ifcld', [a1(w, U0, '0re', '0 e. RR'), hlf], '%s e. RR' % EXP); expoc = D(w, U0, 'recnd', [expor], '%s e. CC' % EXP)
    RHS = lambda e: '( %s x. ( 2 x. ( %s + %s ) ) )' % (WWL, e, U)
    def case(neg):
        Ac = '( %s /\\ %s1 <_ %s )' % (U0, '-. ' if neg else '', RS)
        cc = D(w, Ac, 'simpr', [], '%s1 <_ %s' % ('-. ' if neg else '', RS))
        clc = Closure(w, Ac, {U: ('RR', w.s([ur], 'adantr', '( %s -> %s e. RR )' % (Ac, U))), RS: ('RR', w.s([rsr], 'adantr', '( %s -> %s e. RR )' % (Ac, RS)))})
        clc.atom(U)
        u0c = w.s([u0], 'adantr', '( %s -> 0 <_ %s )' % (Ac, U)); ugtc = w.s([ugt], 'adantr', '( %s -> 0 < %s )' % (Ac, U))
        if not neg:
            ie = D(w, Ac, 'iftrued', [cc], '%s = 0' % EXP)
            nl = nlinarith(w, Ac, [cc, u0c, ugtc], '%s <_ %s' % (XS, RHS('0')), closure=clc)
            e = '0'
        else:
            ie = D(w, Ac, 'iffalsed', [cc], '%s = ( ( 1 - %s ) / 2 )' % (EXP, RS))
            lt1 = w.s([cc, D(w, Ac, 'ltnled', [w.s([rsr], 'adantr', '( %s -> %s e. RR )' % (Ac, RS)), a1(w, Ac, '1re', '1 e. RR')], '( %s < 1 <-> -. 1 <_ %s )' % (RS, RS))], 'mpbird', '( %s -> %s < 1 )' % (Ac, RS))
            le1 = D(w, Ac, 'ltled', [w.s([rsr], 'adantr', '( %s -> %s e. RR )' % (Ac, RS)), a1(w, Ac, '1re', '1 e. RR'), lt1], '%s <_ 1' % RS)
            nl = nlinarith(w, Ac, [le1, u0c, ugtc], '%s <_ %s' % (XS, RHS('( ( 1 - %s ) / 2 )' % RS)), closure=clc)
            e = '( ( 1 - %s ) / 2 )' % RS
        rw = E(w, Ac, 'oveq2d', [E(w, Ac, 'oveq2d', [E(w, Ac, 'oveq1d', [ie], '( %s + %s )' % (EXP, U), '( %s + %s )' % (e, U))], '( 2 x. ( %s + %s ) )' % (EXP, U), '( 2 x. ( %s + %s ) )' % (e, U))], RHS(EXP), RHS(e))
        return w.s([nl, rw], 'breqtrrd', '( %s -> %s <_ %s )' % (Ac, XS, RHS(EXP)))
    d0_ = w.s([case(False), case(True)], 'pm2.61dan', '( %s -> %s <_ %s )' % (U0, XS, RHS(EXP)))
    eur = D(w, U0, 'readdcld', [expor, ur], '( %s + %s ) e. RR' % (EXP, U))
    e2r = D(w, U0, 'remulcld', [a1(w, U0, '2re', '2 e. RR'), eur], '( 2 x. ( %s + %s ) ) e. RR' % (EXP, U))
    d2 = w.s([d0_, D(w, U0, 'ledivmuld', [xsr, e2r, wwrp], '( %s <_ ( 2 x. ( %s + %s ) ) <-> %s <_ %s )' % (TH, EXP, U, XS, RHS(EXP)))], 'mpbird', '( %s -> %s <_ ( 2 x. ( %s + %s ) ) )' % (U0, TH, EXP, U))
    cld = Closure(w, U0, {TH: ('RR', thr), EXP: ('RR', expor), U: ('RR', ur)}); cld.atom(TH); cld.atom(EXP); cld.atom(U)
    d3 = linarith(w, U0, [d2], '%s <_ ( %s + %s )' % (HT, EXP, U), closure=cld)
    htr = D(w, U0, 'remulcld', [half, thr], '%s e. RR' % HT)
    e1 = D(w, U0, 'cxplead', [dr, d1, htr, eur, d3], '( D ^c %s ) <_ ( D ^c ( %s + %s ) )' % (HT, EXP, U))
    DEX = '( D ^c %s )' % EXP
    e2 = D(w, U0, 'cxpaddd', [dc, dne, expoc, uc], '( D ^c ( %s + %s ) ) = ( %s x. ( D ^c %s ) )' % (EXP, U, DEX, U))
    dexr = D(w, U0, 'recxpcld', [dr, d0, expor], '%s e. RR' % DEX); dex0 = D(w, U0, 'cxpge0d', [dr, d0, expor], '0 <_ %s' % DEX)
    dur = D(w, U0, 'recxpcld', [dr, d0, ur], '( D ^c %s ) e. RR' % U)
    e3 = D(w, U0, 'lemul2ad', [dur, a1(w, U0, '3re', '3 e. RR'), dexr, dex0, d13], '( %s x. ( D ^c %s ) ) <_ ( %s x. 3 )' % (DEX, U, DEX))
    e4a = w.s([w.s([cdh, e1], 'eqbrtrd', '( %s -> ( %s ^c %s ) <_ ( D ^c ( %s + %s ) ) )' % (U0, DH, TH, EXP, U)), e2], 'breqtrd', '( %s -> ( %s ^c %s ) <_ ( %s x. ( D ^c %s ) ) )' % (U0, DH, TH, DEX, U))
    dhtr = D(w, U0, 'recxpcld', [dhr, dh0, thr], '( %s ^c %s ) e. RR' % (DH, TH)); dht0 = D(w, U0, 'cxpge0d', [dhr, dh0, thr], '0 <_ ( %s ^c %s )' % (DH, TH))
    d3r = D(w, U0, 'remulcld', [dexr, a1(w, U0, '3re', '3 e. RR')], '( %s x. 3 ) e. RR' % DEX)
    e4 = D(w, U0, 'letrd', [dhtr, D(w, U0, 'remulcld', [dexr, dur], '( %s x. ( D ^c %s ) ) e. RR' % (DEX, U)), d3r, e4a, e3], '( %s ^c %s ) <_ ( %s x. 3 )' % (DH, TH, DEX))
    p108r = D(w, U0, 'recxpcld', [n108r, n1080, thr], '( ; ; 1 0 8 ^c %s ) e. RR' % TH); p1080 = D(w, U0, 'cxpge0d', [n108r, n1080, thr], '0 <_ ( ; ; 1 0 8 ^c %s )' % TH)
    f1 = D(w, U0, 'lemul12ad', [p108r, n108r, dhtr, d3r, p1080, dht0, c108b, e4], '( ( ; ; 1 0 8 ^c %s ) x. ( %s ^c %s ) ) <_ ( ; ; 1 0 8 x. ( %s x. 3 ) )' % (TH, DH, TH, DEX))
    f2 = w.s([w.s([eneq, c0], 'eqtrd', '( %s -> %s = ( ( ; ; 1 0 8 ^c %s ) x. ( %s ^c %s ) ) )' % (U0, EN, TH, DH, TH)), f1], 'eqbrtrd', '( %s -> %s <_ ( ; ; 1 0 8 x. ( %s x. 3 ) ) )' % (U0, EN, DEX))
    K3 = '( ; ; 1 0 8 x. ( %s x. 3 ) )' % DEX
    k3r = D(w, U0, 'remulcld', [n108r, d3r], '%s e. RR' % K3)
    f3 = D(w, U0, 'lemul1ad', [enr, k3r, q81r, q810, f2], '( %s x. %s ) <_ ( %s x. %s )' % (EN, Q81, K3, Q81))
    f4 = D(w, U0, 'letrd', [vr, D(w, U0, 'remulcld', [enr, q81r], '( %s x. %s ) e. RR' % (EN, Q81)), D(w, U0, 'remulcld', [k3r, q81r], '( %s x. %s ) e. RR' % (K3, Q81)), a6, f3], 'V <_ ( %s x. %s )' % (K3, Q81))
    clf = Closure(w, U0, {'V': ('RR', vr), DEX: ('RR', dexr), 'A': ('RR', ar), 'L': ('RR', lr)}); clf.atom(DEX)
    goal = STATEMENTS['zl2cvxu'].split(' -> V <_ ', 1)[1][:-2]
    fin = linarith(w, U0, [f4], 'V <_ %s' % goal, closure=clf, products=True)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)


def subst(text, m):
    """token-level substitution of class variables"""
    return ' '.join(m.get(t, t) for t in text.split())


from zl2_p import strip_mem


# ---------------------------------------------------------------- zl2cvxpl
if __name__ == '__main__' and (not only or 'zl2cvxpl' in only):
    w = W('zl2cvxpl', 'The convexity bound, Phragmen-Lindeloef branch ` 1 / 200 <_ Re S <_ sigma_R ` ( LConvexity 1035-1252: ~ zl2pln on the strip '
          '` sigma_L <_ Re z <_ sigma_R ` with the edges ~ zl2cvxr , ~ zl2cvxl and the unwinding ~ zl2cvxu ).')
    PL0 = STATEMENTS['zl2cvxpl'].split(' -> ( abs ` ( F ` S ) )')[0][2:]
    DDS = QT('S'); MMS = QL('S'); LG = '( log ` %s )' % MMS
    L_ = {'L': LLS}
    UL = '( 1 / %s )' % LLS; SR = subst(SRL, L_); SL = subst(SLL, L_); WW = subst(WWL, L_)
    BBS = BB(DDS); CCS = subst(CCL(DDS), L_); Q81S = subst(Q81, L_)
    assert SR == SRLS, (SR, SRLS)
    ST = STRIP(SL, SR)
    RS = '( Re ` S )'
    assert PL0 == '( ( %s /\\ %s ) /\\ %s <_ %s )' % (HCVX, SRNG2(), RS, SR), PL0
    hc = D(w, PL0, 'simpll', [], HCVX); sr_ = D(w, PL0, 'simplr', [], SRNG2()); case = D(w, PL0, 'simpr', [], '%s <_ %s' % (RS, SR))
    HOL3 = '( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U )' % STR
    h1 = D(w, PL0, 'simpld', [hc], '( ( N e. NN /\\ A e. RR+ ) /\\ %s )' % HOL3); h2 = D(w, PL0, 'simprd', [hc], '( %s /\\ ( %s /\\ %s ) )' % (GRWB('F', STR), RGT(), LFT()))
    na = D(w, PL0, 'simpld', [h1], '( N e. NN /\\ A e. RR+ )'); hol = D(w, PL0, 'simprd', [h1], HOL3)
    nn = D(w, PL0, 'simpld', [na], 'N e. NN'); arp = D(w, PL0, 'simprd', [na], 'A e. RR+')
    fcn = D(w, PL0, 'simp1d', [hol], 'F e. ( U -cn-> CC )'); fdm = D(w, PL0, 'simp2d', [hol], 'U C_ dom ( CC _D F )'); stru = D(w, PL0, 'simp3d', [hol], '%s C_ U' % STR)
    grw = D(w, PL0, 'simpld', [h2], GRWB('F', STR)); rl = D(w, PL0, 'simprd', [h2], '( %s /\\ %s )' % (RGT(), LFT()))
    rgt = D(w, PL0, 'simpld', [rl], RGT()); lft = D(w, PL0, 'simprd', [rl], LFT())
    kb = D(w, PL0, 'simpld', [grw], '( K e. RR+ /\\ B e. RR /\\ 0 <_ B )')
    GRB = '( abs ` ( F ` z ) ) <_ ( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) )'
    gral = D(w, PL0, 'simprd', [grw], 'A. z e. %s %s' % (STR, GRB))
    sc = D(w, PL0, 'simpld', [sr_], 'S e. CC'); sb = D(w, PL0, 'simprd', [sr_], '( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 )' % (RS, RS))
    s200 = D(w, PL0, 'simpld', [sb], '( 1 / ; ; 2 0 0 ) <_ %s' % RS); s2 = D(w, PL0, 'simprd', [sb], '%s <_ 2' % RS)
    rsr = D(w, PL0, 'recld', [sc], '%s e. RR' % RS)
    ar = D(w, PL0, 'rpred', [arp], 'A e. RR'); a0 = D(w, PL0, 'rpge0d', [arp], '0 <_ A')
    # the parameters (zl2cvxa at T = | Im S |, zl2cvxb at D, L)
    isc = D(w, PL0, 'recnd', [D(w, PL0, 'imcld', [sc], '( Im ` S ) e. RR')], '( Im ` S ) e. CC')
    T = '( abs ` ( Im ` S ) )'
    tr = D(w, PL0, 'abscld', [isc], '%s e. RR' % T); t0 = D(w, PL0, 'absge0d', [isc], '0 <_ %s' % T)
    CA = subst(STATEMENTS['zl2cvxa'].split(' -> ', 1)[1][:-2], {'T': T})
    ca = w.s([w.s([nn, tr, t0], '3jca', '( %s -> ( N e. NN /\\ %s e. RR /\\ 0 <_ %s ) )' % (PL0, T, T)), w.inst('zl2cvxa')], 'syl', '( %s -> %s )' % (PL0, CA))
    ca1 = D(w, PL0, 'simpld', [ca], '( ( %s e. RR+ /\\ 1 <_ %s ) /\\ ( %s e. RR+ /\\ 3 <_ %s ) /\\ %s <_ %s )' % (DDS, DDS, MMS, MMS, DDS, MMS))
    ca2 = D(w, PL0, 'simprd', [ca], '( ( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( log ` %s ) <_ %s )' % (LG, LLS, LLS, DDS, LLS))
    dd = D(w, PL0, 'simp1d', [ca1], '( %s e. RR+ /\\ 1 <_ %s )' % (DDS, DDS)); mm = D(w, PL0, 'simp2d', [ca1], '( %s e. RR+ /\\ 3 <_ %s )' % (MMS, MMS))
    ddsrp = D(w, PL0, 'simpld', [dd], '%s e. RR+' % DDS); dds1 = D(w, PL0, 'simprd', [dd], '1 <_ %s' % DDS)
    mmsrp = D(w, PL0, 'simpld', [mm], '%s e. RR+' % MMS)
    lml = D(w, PL0, 'simpld', [ca2], '( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) )' % (LG, LLS, LLS)); ldl = D(w, PL0, 'simprd', [ca2], '( log ` %s ) <_ %s' % (DDS, LLS))
    lm1 = D(w, PL0, 'simpld', [lml], '1 <_ %s' % LG); ll = D(w, PL0, 'simprd', [lml], '( %s e. RR+ /\\ 2 <_ %s )' % (LLS, LLS))
    llrp = D(w, PL0, 'simpld', [ll], '%s e. RR+' % LLS); ll2 = D(w, PL0, 'simprd', [ll], '2 <_ %s' % LLS)
    llr = D(w, PL0, 'rpred', [llrp], '%s e. RR' % LLS)
    lgr = D(w, PL0, 'relogcld', [mmsrp], '%s e. RR' % LG)
    CB = subst(STATEMENTS['zl2cvxb'].split(' -> ', 1)[1][:-2], {'D': DDS, 'L': LLS})
    cb = w.s([w.s([dd, ll, ldl], '3jca', '( %s -> ( ( %s e. RR+ /\\ 1 <_ %s ) /\\ ( %s e. RR+ /\\ 2 <_ %s ) /\\ ( log ` %s ) <_ %s ) )' % (PL0, DDS, DDS, LLS, LLS, DDS, LLS)), w.inst('zl2cvxb')], 'syl',
             '( %s -> %s )' % (PL0, CB))
    D13 = '( %s ^c %s ) <_ 3' % (DDS, UL)
    EXPEQ = '( exp ` ( ( %s - %s ) x. %s ) ) = ( 1 / %s )' % (SL, SR, CCS, BBS)
    cb1 = D(w, PL0, 'simpld', [cb], '( %s /\\ ( 1 <_ ( %s ^c ( 1 / 2 ) ) /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) )' % (D13, DDS, BBS, BBS))
    cb2 = D(w, PL0, 'simprd', [cb], '( ( %s <_ ( 1 / 2 ) /\\ ( %s e. RR+ /\\ %s <_ 2 ) ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s ) )' % (UL, WW, WW, CCS, CCS, EXPEQ))
    d13 = D(w, PL0, 'simpld', [cb1], D13)
    cb21 = D(w, PL0, 'simpld', [cb2], '( %s <_ ( 1 / 2 ) /\\ ( %s e. RR+ /\\ %s <_ 2 ) )' % (UL, WW, WW)); cb22 = D(w, PL0, 'simprd', [cb2], '( ( %s e. RR /\\ 0 <_ %s ) /\\ %s )' % (CCS, CCS, EXPEQ))
    u12 = D(w, PL0, 'simpld', [cb21], '%s <_ ( 1 / 2 )' % UL)
    cc_ = D(w, PL0, 'simpld', [cb22], '( %s e. RR /\\ 0 <_ %s )' % (CCS, CCS)); expeq = D(w, PL0, 'simprd', [cb22], EXPEQ)
    ccr = D(w, PL0, 'simpld', [cc_], '%s e. RR' % CCS)
    urp = D(w, PL0, 'rpreccld', [llrp], '%s e. RR+' % UL); ur = D(w, PL0, 'rpred', [urp], '%s e. RR' % UL); ugt = D(w, PL0, 'rpgt0d', [urp], '0 < %s' % UL)
    cl = Closure(w, PL0, {UL: ('RR', ur), RS: ('RR', rsr), 'A': ('RR', ar), LG: ('RR', lgr)}); cl.atom(UL); cl.atom(LG)
    srr = D(w, PL0, 'readdcld', [a1(w, PL0, '1re', '1 e. RR'), ur], '%s e. RR' % SR); slr = D(w, PL0, 'renegcld', [ur], '%s e. RR' % SL)
    nh = w.s([w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'renegcli', '-u ( 1 / 2 ) e. RR')], 'a1i', '( %s -> -u ( 1 / 2 ) e. RR )' % PL0)
    sl12 = linarith(w, PL0, [u12], '-u ( 1 / 2 ) <_ %s' % SL, closure=cl)
    sr2 = linarith(w, PL0, [u12], '%s <_ 2' % SR, closure=cl)
    sr32 = linarith(w, PL0, [u12], '%s <_ ( 3 / 2 )' % SR, closure=cl)
    s0 = linarith(w, PL0, [s200], '0 <_ %s' % RS, closure=cl)
    sls = linarith(w, PL0, [ugt, s200], '%s <_ %s' % (SL, RS), closure=cl)
    s32 = D(w, PL0, 'letrd', [rsr, srr, w.s([w.s([w.s([], '3re', '3 e. RR'), w.s([], '2re', '2 e. RR'), w.s([], '2ne0', '2 =/= 0')], 'redivcli', '( 3 / 2 ) e. RR')], 'a1i', '( %s -> ( 3 / 2 ) e. RR )' % PL0), case, sr32], '%s <_ ( 3 / 2 )' % RS)
    # the strip ST inside STR inside U
    ic = w.s([w.s([nh, a1(w, PL0, '2re', '2 e. RR')], 'jca', '( %s -> ( -u ( 1 / 2 ) e. RR /\\ 2 e. RR ) )' % PL0), w.s([sl12, sr2], 'jca', '( %s -> ( -u ( 1 / 2 ) <_ %s /\\ %s <_ 2 ) )' % (PL0, SL, SR)), w.inst('iccss')], 'syl2anc',
             '( %s -> ( %s [,] %s ) C_ ( -u ( 1 / 2 ) [,] 2 ) )' % (PL0, SL, SR))
    stss = w.s([ic, w.inst('imass2')], 'syl', '( %s -> %s C_ %s )' % (PL0, ST, STR))
    stu = D(w, PL0, 'sstrd', [stss, stru], '%s C_ U' % ST)
    # the growth hypothesis on ST, quantifier y
    gst = w.s([gral, w.s([stss, w.inst('ssralv')], 'syl', '( %s -> ( A. z e. %s %s -> A. z e. %s %s ) )' % (PL0, STR, GRB, ST, GRB))], 'mpd' if False else 'mpd', '( %s -> A. z e. %s %s )' % (PL0, ST, GRB))
    gsty, GRBY = cbv_yz(w, PL0, w.s([gst], 'idi', '( %s -> A. z e. %s %s )' % (PL0, ST, GRB)) if False else gst, ST, GRB) if False else (None, None)
    idx = w.s([], 'id', '( z = y -> z = y )')
    stg, GRBY = w.wcongr(GRB, {'z': 'y'}, 'z = y', {'z': idx})
    cbv = w.s([stg], 'cbvralvw', '( A. z e. %s %s <-> A. y e. %s %s )' % (ST, GRB, ST, GRBY))
    gsty = w.s([gst, cbv], 'sylib', '( %s -> A. y e. %s %s )' % (PL0, ST, GRBY))
    GRY = GRWB('F', ST, z='y')
    gry = w.s([kb, gsty], 'jca', '( %s -> %s )' % (PL0, GRY))
    # S e. ST
    ric = w.s([w.s([rsr, sls, case], '3jca', '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (PL0, RS, SL, RS, RS, SR)),
               w.s([slr, srr, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (PL0, RS, SL, SR, RS, SL, RS, RS, SR))],
              'mpbird', '( %s -> %s e. ( %s [,] %s ) )' % (PL0, RS, SL, SR))
    sst = w.s([w.s([sc, ric], 'jca', '( %s -> ( S e. CC /\\ %s e. ( %s [,] %s ) ) )' % (PL0, RS, SL, SR)), w.s([], 'elstr', '( S e. %s <-> ( S e. CC /\\ %s e. ( %s [,] %s ) ) )' % (ST, RS, SL, SR))], 'sylibr',
              '( %s -> S e. %s )' % (PL0, ST))
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : U --> CC )' % PL0)
    # the edges
    Ay = '( %s /\\ y e. %s )' % (PL0, ST)
    ys = D(w, Ay, 'simpr', [], 'y e. %s' % ST)
    yc, yre, sly, ysr = strip_mem(w, Ay, 'y', ys, w.s([slr], 'adantr', '( %s -> %s e. RR )' % (Ay, SL)), w.s([srr], 'adantr', '( %s -> %s e. RR )' % (Ay, SR)), X=SL, Y=SR)
    yu = w.s([w.s([stu], 'adantr', '( %s -> %s C_ U )' % (Ay, ST)), ys], 'sseldd', '( %s -> y e. U )' % Ay)
    fyc = w.s([w.s([ff], 'adantr', '( %s -> F : U --> CC )' % Ay), yu], 'ffvelcdmd', '( %s -> ( F ` y ) e. CC )' % Ay)
    yf = w.s([yc, fyc], 'jca', '( %s -> ( y e. CC /\\ ( F ` y ) e. CC ) )' % Ay)
    # right edge
    Ar = '( %s /\\ ( Re ` y ) = %s )' % (Ay, SR)
    LR_ = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Ar, f))
    hr1 = LR_(w.s([w.s([w.s([arp, ll], 'jca', '( %s -> ( A e. RR+ /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) )' % (PL0, LLS, LLS)), w.s([sc, w.s([s0, case], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ %s ) )' % (PL0, RS, RS, SR))], 'jca',
                                                                                                                                      '( %s -> ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) ) )' % (PL0, RS, RS, SR))], 'jca',
                       '( %s -> ( ( A e. RR+ /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) ) ) )' % (PL0, LLS, LLS, RS, RS, SR)),
                  w.s([ccr, rgt], 'jca', '( %s -> ( %s e. RR /\\ %s ) )' % (PL0, CCS, RGT()))], 'jca',
                 '( %s -> ( ( ( A e. RR+ /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) ) ) /\\ ( %s e. RR /\\ %s ) ) )' % (PL0, LLS, LLS, RS, RS, SR, CCS, RGT())),
              '( ( ( A e. RR+ /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) ) ) /\\ ( %s e. RR /\\ %s ) )' % (LLS, LLS, RS, RS, SR, CCS, RGT()))
    hr2 = w.s([w.s([yf], 'adantr', '( %s -> ( y e. CC /\\ ( F ` y ) e. CC ) )' % Ar), D(w, Ar, 'simpr', [], '( Re ` y ) = %s' % SR)], 'jca', '( %s -> ( ( y e. CC /\\ ( F ` y ) e. CC ) /\\ ( Re ` y ) = %s ) )' % (Ar, SR))
    RSTMT = subst(STATEMENTS['zl2cvxr'], {'L': LLS, 'C': CCS, 'Z': 'y'})
    RANT, RCON = RSTMT[2:].split(' -> ( ( ( abs ` ( F ` y ) )', 1)
    RCON = '( ( ( abs ` ( F ` y ) )' + RCON[:-2]
    er = w.s([w.s([hr1, hr2], 'jca', '( %s -> %s )' % (Ar, RANT)), w.inst('zl2cvxr')], 'syl', '( %s -> %s )' % (Ar, RCON))
    LY_ = 'A. y e. %s ( ( Re ` y ) = %s -> %s )' % (ST, SR, RCON)
    ry = w.s([w.s([er], 'ex', '( %s -> ( ( Re ` y ) = %s -> %s ) )' % (Ay, SR, RCON))], 'ralrimiva', '( %s -> %s )' % (PL0, LY_))
    # left edge
    Al = '( %s /\\ ( Re ` y ) = %s )' % (Ay, SL)
    LL_ = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Al, f))
    hl1 = LL_(w.s([w.s([na, ll], 'jca', '( %s -> ( ( N e. NN /\\ A e. RR+ ) /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) )' % (PL0, LLS, LLS)),
                   w.s([sc, w.s([s0, s32], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ ( 3 / 2 ) ) )' % (PL0, RS, RS))], 'jca', '( %s -> ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ ( 3 / 2 ) ) ) )' % (PL0, RS, RS))], 'jca',
                  '( %s -> ( ( ( N e. NN /\\ A e. RR+ ) /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ ( 3 / 2 ) ) ) ) )' % (PL0, LLS, LLS, RS, RS)),
              '( ( ( N e. NN /\\ A e. RR+ ) /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ ( 3 / 2 ) ) ) )' % (LLS, LLS, RS, RS))
    hl2a = LL_(w.s([w.s([ccr, expeq], 'jca', '( %s -> ( %s e. RR /\\ %s ) )' % (PL0, CCS, EXPEQ)), d13], 'jca', '( %s -> ( ( %s e. RR /\\ %s ) /\\ %s ) )' % (PL0, CCS, EXPEQ, D13)),
               '( ( %s e. RR /\\ %s ) /\\ %s )' % (CCS, EXPEQ, D13))
    hl2b = w.s([LL_(lft, LFT()), w.s([w.s([yf], 'adantr', '( %s -> ( y e. CC /\\ ( F ` y ) e. CC ) )' % Al), D(w, Al, 'simpr', [], '( Re ` y ) = %s' % SL)], 'jca',
                                     '( %s -> ( ( y e. CC /\\ ( F ` y ) e. CC ) /\\ ( Re ` y ) = %s ) )' % (Al, SL))], 'jca',
               '( %s -> ( %s /\\ ( ( y e. CC /\\ ( F ` y ) e. CC ) /\\ ( Re ` y ) = %s ) ) )' % (Al, LFT(), SL))
    LSTMT = subst(STATEMENTS['zl2cvxl'], {'L': LLS, 'C': CCS, 'Z': 'y'})
    LANT, LCON = LSTMT[2:].split(' -> ( ( ( abs ` ( F ` y ) )', 1)
    LCON = '( ( ( abs ` ( F ` y ) )' + LCON[:-2]
    hl2 = w.s([hl2a, hl2b], 'jca', '( %s -> ( ( ( %s e. RR /\\ %s ) /\\ %s ) /\\ ( %s /\\ ( ( y e. CC /\\ ( F ` y ) e. CC ) /\\ ( Re ` y ) = %s ) ) ) )' % (Al, CCS, EXPEQ, D13, LFT(), SL))
    el = w.s([w.s([hl1, hl2], 'jca', '( %s -> %s )' % (Al, LANT)), w.inst('zl2cvxl')], 'syl', '( %s -> %s )' % (Al, LCON))
    LX_ = 'A. y e. %s ( ( Re ` y ) = %s -> %s )' % (ST, SL, LCON)
    rx = w.s([w.s([el], 'ex', '( %s -> ( ( Re ` y ) = %s -> %s ) )' % (Ay, SL, LCON))], 'ralrimiva', '( %s -> %s )' % (PL0, LX_))
    # zl2pln at z := y, X := SL, Y := SR, D := U, W := S, P := SR, C := CCS, Q := Q81S
    PA = subst(PLNA, {'X': SL, 'Y': SR, 'D': 'U', 'W': 'S', 'P': SR, 'C': CCS, 'Q': Q81S, 'z': 'y'})
    assert LX_ in PA and LY_ in PA and GRY in PA, 'zl2pln instance'
    l1r = D(w, PL0, 'readdcld', [a1(w, PL0, '1re', '1 e. RR'), llr], '( 1 + %s ) e. RR' % LLS)
    l1rp = D(w, PL0, 'elrpd', [l1r, linarith(w, PL0, [D(w, PL0, 'rpge0d', [llrp], '0 <_ %s' % LLS)], '0 < ( 1 + %s )' % LLS, leaves={LLS: llr})], '( 1 + %s ) e. RR+' % LLS)
    rp81 = w.s([w.s([w.s([w.s([], '8nn0', '8 e. NN0'), w.s([], '1nn', '1 e. NN')], 'decnncl', '; 8 1 e. NN'), w.s([], 'nnrp', '( ; 8 1 e. NN -> ; 8 1 e. RR+ )')], 'ax-mp', '; 8 1 e. RR+')], 'a1i', '( %s -> ; 8 1 e. RR+ )' % PL0)
    q81rp = D(w, PL0, 'rpmulcld', [D(w, PL0, 'rpmulcld', [rp81, arp], '( ; 8 1 x. A ) e. RR+'), l1rp], '%s e. RR+' % Q81S)
    j1 = w.s([w.s([w.s([slr, srr], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (PL0, SL, SR)), w.s([fcn, fdm, stu], '3jca', '( %s -> ( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U ) )' % (PL0, ST))], 'jca',
                  '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U ) ) )' % (PL0, SL, SR, ST)), gry], 'jca',
             '( %s -> ( ( ( %s e. RR /\\ %s e. RR ) /\\ ( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U ) ) /\\ %s ) )' % (PL0, SL, SR, ST, GRY))
    j2 = w.s([w.s([sst, w.s([srr, ccr], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (PL0, SR, CCS)), q81rp], '3jca', '( %s -> ( S e. %s /\\ ( %s e. RR /\\ %s e. RR ) /\\ %s e. RR+ ) )' % (PL0, ST, SR, CCS, Q81S)),
              w.s([rx, ry], 'jca', '( %s -> ( %s /\\ %s ) )' % (PL0, LX_, LY_))], 'jca',
             '( %s -> ( ( S e. %s /\\ ( %s e. RR /\\ %s e. RR ) /\\ %s e. RR+ ) /\\ ( %s /\\ %s ) ) )' % (PL0, ST, SR, CCS, Q81S, LX_, LY_))
    PLC = '( ( abs ` ( F ` S ) ) x. ( exp ` ( ( %s - %s ) x. %s ) ) ) <_ %s' % (RS, SR, CCS, Q81S)
    pl = w.s([w.s([j1, j2], 'jca', '( %s -> %s )' % (PL0, PA)), w.inst('zl2pln')], 'syl', '( %s -> %s )' % (PL0, PLC))
    # unwind (zl2cvxu at D := DDS, L := LLS, V := | F S | )
    fsc = w.s([ff, w.s([stu, sst], 'sseldd', '( %s -> S e. U )' % PL0)], 'ffvelcdmd', '( %s -> ( F ` S ) e. CC )' % PL0)
    AFS = '( abs ` ( F ` S ) )'
    afs = D(w, PL0, 'abscld', [fsc], '%s e. RR' % AFS)
    USTMT = subst(STATEMENTS['zl2cvxu'], {'D': DDS, 'L': LLS, 'V': AFS})
    UANT, UCON = USTMT[2:].split(' -> %s <_ ' % AFS, 1)
    UCON = UCON[:-2]
    hu = w.s([w.s([w.s([arp, dd], 'jca', '( %s -> ( A e. RR+ /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) )' % (PL0, DDS, DDS)), w.s([ll, d13], 'jca', '( %s -> ( ( %s e. RR+ /\\ 2 <_ %s ) /\\ %s ) )' % (PL0, LLS, LLS, D13))], 'jca',
                  '( %s -> ( ( A e. RR+ /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) /\\ ( ( %s e. RR+ /\\ 2 <_ %s ) /\\ %s ) ) )' % (PL0, DDS, DDS, LLS, LLS, D13)),
              w.s([w.s([sc, w.s([s0, case], 'jca', '( %s -> ( 0 <_ %s /\\ %s <_ %s ) )' % (PL0, RS, RS, SR))], 'jca', '( %s -> ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) ) )' % (PL0, RS, RS, SR)),
                   w.s([afs, pl], 'jca', '( %s -> ( %s e. RR /\\ %s ) )' % (PL0, AFS, PLC))], 'jca',
                  '( %s -> ( ( S e. CC /\\ ( 0 <_ %s /\\ %s <_ %s ) ) /\\ ( %s e. RR /\\ %s ) ) )' % (PL0, RS, RS, SR, AFS, PLC))], 'jca', '( %s -> %s )' % (PL0, UANT))
    un = w.s([hu, w.inst('zl2cvxu')], 'syl', '( %s -> %s <_ %s )' % (PL0, AFS, UCON))
    DEX = '( %s ^c %s )' % (DDS, EXPO('S'))
    assert UCON == '( ( ; ; ; ; 2 6 2 4 4 x. A ) x. ( ( 1 + %s ) x. %s ) )' % (LLS, DEX), UCON
    # 1 + L <_ 3 log M and the constants
    ddsr = D(w, PL0, 'rpred', [ddsrp], '%s e. RR' % DDS); dds0 = D(w, PL0, 'rpge0d', [ddsrp], '0 <_ %s' % DDS)
    omr = D(w, PL0, 'resubcld', [a1(w, PL0, '1re', '1 e. RR'), rsr], '( 1 - %s ) e. RR' % RS)
    expor = D(w, PL0, 'ifcld', [a1(w, PL0, '0re', '0 e. RR'), D(w, PL0, 'redivcld', [omr, a1(w, PL0, '2re', '2 e. RR'), a1(w, PL0, '2ne0', '2 =/= 0')], '( ( 1 - %s ) / 2 ) e. RR' % RS)], '%s e. RR' % EXPO('S'))
    dexr = D(w, PL0, 'recxpcld', [ddsr, dds0, expor], '%s e. RR' % DEX); dex0 = D(w, PL0, 'cxpge0d', [ddsr, dds0, expor], '0 <_ %s' % DEX)
    lg0 = linarith(w, PL0, [lm1], '0 <_ %s' % LG, closure=cl)
    t1 = linarith(w, PL0, [lm1], '( 1 + %s ) <_ ( 3 x. %s )' % (LLS, LG), closure=cl)
    lg3r = D(w, PL0, 'remulcld', [a1(w, PL0, '3re', '3 e. RR'), lgr], '( 3 x. %s ) e. RR' % LG)
    t2 = D(w, PL0, 'lemul1ad', [l1r, lg3r, dexr, dex0, t1], '( ( 1 + %s ) x. %s ) <_ ( ( 3 x. %s ) x. %s )' % (LLS, DEX, LG, DEX))
    K26 = '( ; ; ; ; 2 6 2 4 4 x. A )'
    n26 = w.s([w.s([w.s([w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '6nn0', '6 e. NN0')], 'deccl', '; 2 6 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; ; 2 6 2 e. NN0'), w.s([], '4nn0', '4 e. NN0')], 'deccl', '; ; ; 2 6 2 4 e. NN0'),
                        w.s([], '4nn0', '4 e. NN0')], 'deccl', '; ; ; ; 2 6 2 4 4 e. NN0')], 'nn0rei', '; ; ; ; 2 6 2 4 4 e. RR')], 'a1i', '( %s -> ; ; ; ; 2 6 2 4 4 e. RR )' % PL0)
    n260 = w.s([w.s([w.s([w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '6nn0', '6 e. NN0')], 'deccl', '; 2 6 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; ; 2 6 2 e. NN0'), w.s([], '4nn0', '4 e. NN0')], 'deccl', '; ; ; 2 6 2 4 e. NN0'),
                         w.s([], '4nn0', '4 e. NN0')], 'deccl', '; ; ; ; 2 6 2 4 4 e. NN0')], 'nn0ge0i', '0 <_ ; ; ; ; 2 6 2 4 4')], 'a1i', '( %s -> 0 <_ ; ; ; ; 2 6 2 4 4 )' % PL0)
    k26r = D(w, PL0, 'remulcld', [n26, ar], '%s e. RR' % K26); k260 = D(w, PL0, 'mulge0d', [n26, ar, n260, a0], '0 <_ %s' % K26)
    t3 = D(w, PL0, 'lemul2ad', [D(w, PL0, 'remulcld', [l1r, dexr], '( ( 1 + %s ) x. %s ) e. RR' % (LLS, DEX)), D(w, PL0, 'remulcld', [lg3r, dexr], '( ( 3 x. %s ) x. %s ) e. RR' % (LG, DEX)), k26r, k260, t2],
           '( %s x. ( ( 1 + %s ) x. %s ) ) <_ ( %s x. ( ( 3 x. %s ) x. %s ) )' % (K26, LLS, DEX, K26, LG, DEX))
    pos = D(w, PL0, 'mulge0d', [ar, D(w, PL0, 'remulcld', [dexr, lgr], '( %s x. %s ) e. RR' % (DEX, LG)), a0, D(w, PL0, 'mulge0d', [dexr, lgr, dex0, lg0], '0 <_ ( %s x. %s )' % (DEX, LG))], '0 <_ ( A x. ( %s x. %s ) )' % (DEX, LG))
    clf = Closure(w, PL0, {AFS: ('RR', afs), 'A': ('RR', ar), DEX: ('RR', dexr), LG: ('RR', lgr), LLS: ('RR', llr)}); clf.atom(DEX); clf.atom(LG); clf.atom(LLS)
    goal = '%s <_ ( ( %s x. A ) x. %s )' % (AFS, C5E, CXB('S'))
    fin = linarith(w, PL0, [un, t3, pos], goal, closure=clf, products=True)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)


# ---------------------------------------------------------------- zl2cvxd
if __name__ == '__main__' and (not only or 'zl2cvxd' in only):
    w = W('zl2cvxd', 'The convexity bound, direct branch ` sigma_R < Re S <_ 2 ` ( LConvexity 1265-1280: the right-edge bound RGT at ` S ` , '
          '` 1 / ( Re S - 1 ) <_ L ` , ` 1 + L <_ 3 log M ` and ` max ( ( 1 - Re S ) / 2 , 0 ) = 0 ` ).')
    D0 = STATEMENTS['zl2cvxd'].split(' -> ( abs ` ( F ` S ) )')[0][2:]
    DDS = QT('S'); MMS = QL('S'); LG = '( log ` %s )' % MMS; RS = '( Re ` S )'
    UL = '( 1 / %s )' % LLS
    assert D0 == '( ( %s /\\ %s ) /\\ %s < %s )' % (HCVX, SRNG2(), SRLS, RS), D0
    hc = D(w, D0, 'simpll', [], HCVX); sr_ = D(w, D0, 'simplr', [], SRNG2()); case = D(w, D0, 'simpr', [], '%s < %s' % (SRLS, RS))
    HOL3 = '( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U )' % STR
    h1 = D(w, D0, 'simpld', [hc], '( ( N e. NN /\\ A e. RR+ ) /\\ %s )' % HOL3); h2 = D(w, D0, 'simprd', [hc], '( %s /\\ ( %s /\\ %s ) )' % (GRWB('F', STR), RGT(), LFT()))
    na = D(w, D0, 'simpld', [h1], '( N e. NN /\\ A e. RR+ )')
    nn = D(w, D0, 'simpld', [na], 'N e. NN'); arp = D(w, D0, 'simprd', [na], 'A e. RR+')
    rl = D(w, D0, 'simprd', [h2], '( %s /\\ %s )' % (RGT(), LFT()))
    rgt = D(w, D0, 'simpld', [rl], RGT())
    sc = D(w, D0, 'simpld', [sr_], 'S e. CC'); sb = D(w, D0, 'simprd', [sr_], '( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 )' % (RS, RS))
    s2 = D(w, D0, 'simprd', [sb], '%s <_ 2' % RS)
    rsr = D(w, D0, 'recld', [sc], '%s e. RR' % RS)
    ar = D(w, D0, 'rpred', [arp], 'A e. RR'); a0 = D(w, D0, 'rpge0d', [arp], '0 <_ A')
    # the parameters (zl2cvxa at T = | Im S |)
    isc = D(w, D0, 'recnd', [D(w, D0, 'imcld', [sc], '( Im ` S ) e. RR')], '( Im ` S ) e. CC')
    T = '( abs ` ( Im ` S ) )'
    tr = D(w, D0, 'abscld', [isc], '%s e. RR' % T); t0 = D(w, D0, 'absge0d', [isc], '0 <_ %s' % T)
    CA = subst(STATEMENTS['zl2cvxa'].split(' -> ', 1)[1][:-2], {'T': T})
    ca = w.s([w.s([nn, tr, t0], '3jca', '( %s -> ( N e. NN /\\ %s e. RR /\\ 0 <_ %s ) )' % (D0, T, T)), w.inst('zl2cvxa')], 'syl', '( %s -> %s )' % (D0, CA))
    ca1 = D(w, D0, 'simpld', [ca], '( ( %s e. RR+ /\\ 1 <_ %s ) /\\ ( %s e. RR+ /\\ 3 <_ %s ) /\\ %s <_ %s )' % (DDS, DDS, MMS, MMS, DDS, MMS))
    ca2 = D(w, D0, 'simprd', [ca], '( ( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( log ` %s ) <_ %s )' % (LG, LLS, LLS, DDS, LLS))
    dd = D(w, D0, 'simp1d', [ca1], '( %s e. RR+ /\\ 1 <_ %s )' % (DDS, DDS)); mm = D(w, D0, 'simp2d', [ca1], '( %s e. RR+ /\\ 3 <_ %s )' % (MMS, MMS))
    ddsrp = D(w, D0, 'simpld', [dd], '%s e. RR+' % DDS)
    mmsrp = D(w, D0, 'simpld', [mm], '%s e. RR+' % MMS)
    lml = D(w, D0, 'simpld', [ca2], '( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) )' % (LG, LLS, LLS))
    lm1 = D(w, D0, 'simpld', [lml], '1 <_ %s' % LG); ll = D(w, D0, 'simprd', [lml], '( %s e. RR+ /\\ 2 <_ %s )' % (LLS, LLS))
    llrp = D(w, D0, 'simpld', [ll], '%s e. RR+' % LLS)
    llr = D(w, D0, 'rpred', [llrp], '%s e. RR' % LLS); llc = D(w, D0, 'rpcnd', [llrp], '%s e. CC' % LLS); llne = D(w, D0, 'rpne0d', [llrp], '%s =/= 0' % LLS)
    lgr = D(w, D0, 'relogcld', [mmsrp], '%s e. RR' % LG)
    urp = D(w, D0, 'rpreccld', [llrp], '%s e. RR+' % UL); ur = D(w, D0, 'rpred', [urp], '%s e. RR' % UL); ugt = D(w, D0, 'rpgt0d', [urp], '0 < %s' % UL)
    cl = Closure(w, D0, {UL: ('RR', ur), RS: ('RR', rsr), 'A': ('RR', ar), LG: ('RR', lgr)}); cl.atom(UL); cl.atom(LG)
    s1 = linarith(w, D0, [case, ugt], '1 < %s' % RS, closure=cl)
    # the right-edge bound at S
    fb0, _ = inst_ral_t(w, D0, rgt, 'CC', RGT()[len('A. z e. CC '):], 'S', sc)
    RS1 = '( %s - 1 )' % RS
    GB = '( A x. ( 1 + ( 1 / %s ) ) )' % RS1
    fb = w.s([fb0, w.s([s1, s2], 'jca', '( %s -> ( 1 < %s /\\ %s <_ 2 ) )' % (D0, RS, RS))], 'mpd', '( %s -> ( abs ` ( F ` S ) ) <_ %s )' % (D0, GB))
    # 1 / ( Re S - 1 ) <_ L
    rs1r = D(w, D0, 'resubcld', [rsr, a1(w, D0, '1re', '1 e. RR')], '%s e. RR' % RS1)
    rs1p = linarith(w, D0, [s1], '0 < %s' % RS1, closure=cl)
    rs1rp = D(w, D0, 'elrpd', [rs1r, rs1p], '%s e. RR+' % RS1)
    ul1 = linarith(w, D0, [case], '%s <_ %s' % (UL, RS1), closure=cl)
    bi = D(w, D0, 'lerecd', [urp, rs1rp], '( %s <_ %s <-> ( 1 / %s ) <_ ( 1 / %s ) )' % (UL, RS1, RS1, UL))
    r1 = w.s([ul1, bi], 'mpbid', '( %s -> ( 1 / %s ) <_ ( 1 / %s ) )' % (D0, RS1, UL))
    rr = D(w, D0, 'recrecd', [llc, llne], '( 1 / %s ) = %s' % (UL, LLS))
    r2 = w.s([r1, rr], 'breqtrd', '( %s -> ( 1 / %s ) <_ %s )' % (D0, RS1, LLS))
    RC = '( 1 / %s )' % RS1
    rcr = D(w, D0, 'rpred', [D(w, D0, 'rpreccld', [rs1rp], '%s e. RR+' % RC)], '%s e. RR' % RC)
    cl.leaf(RC, 'RR', rcr); cl.atom(RC)
    q1 = linarith(w, D0, [r2], '( 1 + %s ) <_ ( 1 + %s )' % (RC, LLS), closure=cl)
    l1r = D(w, D0, 'readdcld', [a1(w, D0, '1re', '1 e. RR'), llr], '( 1 + %s ) e. RR' % LLS)
    rc1r = D(w, D0, 'readdcld', [a1(w, D0, '1re', '1 e. RR'), rcr], '( 1 + %s ) e. RR' % RC)
    q2 = D(w, D0, 'lemul2ad', [rc1r, l1r, ar, a0, q1], '%s <_ ( A x. ( 1 + %s ) )' % (GB, LLS))
    t1 = linarith(w, D0, [lm1], '( 1 + %s ) <_ ( 3 x. %s )' % (LLS, LG), closure=cl)
    lg3r = D(w, D0, 'remulcld', [a1(w, D0, '3re', '3 e. RR'), lgr], '( 3 x. %s ) e. RR' % LG)
    q3 = D(w, D0, 'lemul2ad', [l1r, lg3r, ar, a0, t1], '( A x. ( 1 + %s ) ) <_ ( A x. ( 3 x. %s ) )' % (LLS, LG))
    # the exponent is 0: D ^c EXPO = 1
    EXP = EXPO('S'); DEX = '( %s ^c %s )' % (DDS, EXP)
    s1le = D(w, D0, 'ltled', [a1(w, D0, '1re', '1 e. RR'), rsr, s1], '1 <_ %s' % RS)
    ie = D(w, D0, 'iftrued', [s1le], '%s = 0' % EXP)
    dex1 = w.s([E(w, D0, 'oveq2d', [ie], DEX, '( %s ^c 0 )' % DDS), D(w, D0, 'cxp0d', [D(w, D0, 'rpcnd', [ddsrp], '%s e. CC' % DDS)], '( %s ^c 0 ) = 1' % DDS)], 'eqtrd',
               '( %s -> %s = 1 )' % (D0, DEX))
    K10 = '( %s x. A )' % C5E
    e1 = E(w, D0, 'oveq1d', [dex1], '( %s x. %s )' % (DEX, LG), '( 1 x. %s )' % LG)
    e2 = w.s([e1, D(w, D0, 'mullidd', [D(w, D0, 'recnd', [lgr], '%s e. CC' % LG)], '( 1 x. %s ) = %s' % (LG, LG))], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (D0, DEX, LG, LG))
    e3 = E(w, D0, 'oveq2d', [e2], '( %s x. ( %s x. %s ) )' % (K10, DEX, LG), '( %s x. %s )' % (K10, LG))
    lg0 = linarith(w, D0, [lm1], '0 <_ %s' % LG, closure=cl)
    pos = D(w, D0, 'mulge0d', [ar, lgr, a0, lg0], '0 <_ ( A x. %s )' % LG)
    AFS = '( abs ` ( F ` S ) )'
    # ( abs ` ( F ` S ) ) e. RR from the bound is not available directly: F ` S e. CC via the strip
    ff = w.s([D(w, D0, 'simp1d', [D(w, D0, 'simprd', [h1], HOL3)], 'F e. ( U -cn-> CC )'), w.inst('cncff')], 'syl', '( %s -> F : U --> CC )' % D0)
    stru = D(w, D0, 'simp3d', [D(w, D0, 'simprd', [h1], HOL3)], '%s C_ U' % STR)
    nh = w.s([w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'renegcli', '-u ( 1 / 2 ) e. RR')], 'a1i', '( %s -> -u ( 1 / 2 ) e. RR )' % D0)
    sl12 = linarith(w, D0, [s1], '-u ( 1 / 2 ) <_ %s' % RS, closure=cl)
    ric = w.s([w.s([rsr, sl12, s2], '3jca', '( %s -> ( %s e. RR /\\ -u ( 1 / 2 ) <_ %s /\\ %s <_ 2 ) )' % (D0, RS, RS, RS)),
               w.s([nh, a1(w, D0, '2re', '2 e. RR'), w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( -u ( 1 / 2 ) [,] 2 ) <-> ( %s e. RR /\\ -u ( 1 / 2 ) <_ %s /\\ %s <_ 2 ) ) )' % (D0, RS, RS, RS, RS))],
              'mpbird', '( %s -> %s e. ( -u ( 1 / 2 ) [,] 2 ) )' % (D0, RS))
    sst = w.s([w.s([sc, ric], 'jca', '( %s -> ( S e. CC /\\ %s e. ( -u ( 1 / 2 ) [,] 2 ) ) )' % (D0, RS)), w.s([], 'elstr', '( S e. %s <-> ( S e. CC /\\ %s e. ( -u ( 1 / 2 ) [,] 2 ) ) )' % (STR, RS))], 'sylibr',
              '( %s -> S e. %s )' % (D0, STR))
    fsc = w.s([ff, w.s([stru, sst], 'sseldd', '( %s -> S e. U )' % D0)], 'ffvelcdmd', '( %s -> ( F ` S ) e. CC )' % D0)
    afs = D(w, D0, 'abscld', [fsc], '%s e. RR' % AFS)
    clf = Closure(w, D0, {AFS: ('RR', afs), 'A': ('RR', ar), LG: ('RR', lgr), LLS: ('RR', llr), RC: ('RR', rcr)}); clf.atom(LG); clf.atom(LLS); clf.atom(RC)
    fin = linarith(w, D0, [fb, q2, q3, pos], '%s <_ ( %s x. %s )' % (AFS, K10, LG), closure=clf, products=True)
    w.qed([fin, e3], 'breqtrrd', STATEMENTS['zl2cvxd'])
    go(w, only)


# ---------------------------------------------------------------- zl2cvx
if __name__ == '__main__' and (not only or 'zl2cvx' in only):
    w = W('zl2cvx', 'The convexity bound for a function holomorphic on the strip ` -1/2 <_ Re <_ 2 ` with the edge bounds RGT and LFT '
          '( LConvexity 959-1281, ` norm_LFunction_le_convexity\' ` : ~ zl2cvxpl and ~ zl2cvxd by cases on ` Re S <_ sigma_R ` ).')
    X0 = '( %s /\\ %s )' % (HCVX, SRNG2())
    CON = '( abs ` ( F ` S ) ) <_ ( ( %s x. A ) x. %s )' % (C5E, CXB('S'))
    assert STATEMENTS['zl2cvx'] == '( %s -> %s )' % (X0, CON)
    RS = '( Re ` S )'
    hc = D(w, X0, 'simpl', [], HCVX); sr_ = D(w, X0, 'simpr', [], SRNG2())
    HOL3 = '( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U )' % STR
    h1 = D(w, X0, 'simpld', [hc], '( ( N e. NN /\\ A e. RR+ ) /\\ %s )' % HOL3)
    nn = D(w, X0, 'simpld', [D(w, X0, 'simpld', [h1], '( N e. NN /\\ A e. RR+ )')], 'N e. NN')
    sc = D(w, X0, 'simpld', [sr_], 'S e. CC')
    isc = D(w, X0, 'recnd', [D(w, X0, 'imcld', [sc], '( Im ` S ) e. RR')], '( Im ` S ) e. CC')
    T = '( abs ` ( Im ` S ) )'
    tr = D(w, X0, 'abscld', [isc], '%s e. RR' % T); t0 = D(w, X0, 'absge0d', [isc], '0 <_ %s' % T)
    DDS = QT('S'); MMS = QL('S'); LG = '( log ` %s )' % MMS
    CA = subst(STATEMENTS['zl2cvxa'].split(' -> ', 1)[1][:-2], {'T': T})
    ca = w.s([w.s([nn, tr, t0], '3jca', '( %s -> ( N e. NN /\\ %s e. RR /\\ 0 <_ %s ) )' % (X0, T, T)), w.inst('zl2cvxa')], 'syl', '( %s -> %s )' % (X0, CA))
    ca2 = D(w, X0, 'simprd', [ca], '( ( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( log ` %s ) <_ %s )' % (LG, LLS, LLS, DDS, LLS))
    lml = D(w, X0, 'simpld', [ca2], '( 1 <_ %s /\\ ( %s e. RR+ /\\ 2 <_ %s ) )' % (LG, LLS, LLS))
    ll = D(w, X0, 'simprd', [lml], '( %s e. RR+ /\\ 2 <_ %s )' % (LLS, LLS))
    llrp = D(w, X0, 'simpld', [ll], '%s e. RR+' % LLS)
    UL = '( 1 / %s )' % LLS
    ur = D(w, X0, 'rpred', [D(w, X0, 'rpreccld', [llrp], '%s e. RR+' % UL)], '%s e. RR' % UL)
    srr = D(w, X0, 'readdcld', [a1(w, X0, '1re', '1 e. RR'), ur], '%s e. RR' % SRLS)
    rsr = D(w, X0, 'recld', [sc], '%s e. RR' % RS)
    tri = w.s([rsr, srr, w.inst('lelttric')], 'syl2anc', '( %s -> ( %s <_ %s \\/ %s < %s ) )' % (X0, RS, SRLS, SRLS, RS))
    c1 = w.s([], 'zl2cvxpl', STATEMENTS['zl2cvxpl'])
    c2 = w.s([], 'zl2cvxd', STATEMENTS['zl2cvxd'])
    w.qed([c1, c2, tri], 'mpjaodan', STATEMENTS['zl2cvx'])
    go(w, only)


# ---------------------------------------------------------------- zl2cvx1
if __name__ == '__main__' and (not only or 'zl2cvx1' in only):
    w = W('zl2cvx1', 'The convexity bound on ` 1 / 200 <_ Re S <_ 1 ` with the exponent ` ( 1 - Re S ) / 2 ` '
          '( LConvexity 1288, ` norm_LFunction_le_convexity ` : ~ zl2cvx with ` max ( ( 1 - Re S ) / 2 , 0 ) = ( 1 - Re S ) / 2 ` ).')
    RS = '( Re ` S )'
    Y0 = '( %s /\\ ( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 1 ) ) )' % (HCVX, RS, RS)
    HL = '( ( 1 - %s ) / 2 )' % RS
    DDS = QT('S'); MMS = QL('S'); LG = '( log ` %s )' % MMS
    CON1 = '( abs ` ( F ` S ) ) <_ ( ( %s x. A ) x. ( ( %s ^c %s ) x. %s ) )' % (C5E, DDS, HL, LG)
    assert STATEMENTS['zl2cvx1'] == '( %s -> %s )' % (Y0, CON1), STATEMENTS['zl2cvx1']
    X0 = '( %s /\\ %s )' % (HCVX, SRNG2())
    CON = '( abs ` ( F ` S ) ) <_ ( ( %s x. A ) x. %s )' % (C5E, CXB('S'))
    hc = D(w, Y0, 'simpl', [], HCVX); sr1 = D(w, Y0, 'simpr', [], '( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 1 ) )' % (RS, RS))
    sc = D(w, Y0, 'simpld', [sr1], 'S e. CC'); sb = D(w, Y0, 'simprd', [sr1], '( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 1 )' % (RS, RS))
    s200 = D(w, Y0, 'simpld', [sb], '( 1 / ; ; 2 0 0 ) <_ %s' % RS); s1 = D(w, Y0, 'simprd', [sb], '%s <_ 1' % RS)
    rsr = D(w, Y0, 'recld', [sc], '%s e. RR' % RS)
    s2 = D(w, Y0, 'letrd', [rsr, a1(w, Y0, '1re', '1 e. RR'), a1(w, Y0, '2re', '2 e. RR'), s1, a1(w, Y0, '1le2', '1 <_ 2')], '%s <_ 2' % RS)
    hx = w.s([hc, w.s([sc, w.s([s200, s2], 'jca', '( %s -> ( ( 1 / ; ; 2 0 0 ) <_ %s /\\ %s <_ 2 ) )' % (Y0, RS, RS))], 'jca', '( %s -> %s )' % (Y0, SRNG2()))], 'jca', '( %s -> %s )' % (Y0, X0))
    cv = w.s([hx, w.inst('zl2cvx')], 'syl', '( %s -> %s )' % (Y0, CON))
    EXP = EXPO('S')
    # EXPO = ( 1 - Re S ) / 2 by cases on 1 <_ Re S
    A1 = '( %s /\\ 1 <_ %s )' % (Y0, RS)
    cc1 = D(w, A1, 'simpr', [], '1 <_ %s' % RS)
    rsr1 = w.s([rsr], 'adantr', '( %s -> %s e. RR )' % (A1, RS))
    bi = D(w, A1, 'letri3d', [rsr1, a1(w, A1, '1re', '1 e. RR')], '( %s = 1 <-> ( %s <_ 1 /\\ 1 <_ %s ) )' % (RS, RS, RS))
    eq1 = w.s([w.s([w.s([s1], 'adantr', '( %s -> %s <_ 1 )' % (A1, RS)), cc1], 'jca', '( %s -> ( %s <_ 1 /\\ 1 <_ %s ) )' % (A1, RS, RS)), bi], 'mpbird', '( %s -> %s = 1 )' % (A1, RS))
    ie1 = D(w, A1, 'iftrued', [cc1], '%s = 0' % EXP)
    h1 = E(w, A1, 'oveq2d', [eq1], '( 1 - %s )' % RS, '( 1 - 1 )')
    h2 = w.s([h1, a1(w, A1, '1m1e0', '( 1 - 1 ) = 0')], 'eqtrd', '( %s -> ( 1 - %s ) = 0 )' % (A1, RS))
    h3 = E(w, A1, 'oveq1d', [h2], HL, '( 0 / 2 )')
    h4 = w.s([h3, w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0')], 'div0i', '( 0 / 2 ) = 0')], 'a1i', '( %s -> ( 0 / 2 ) = 0 )' % A1)], 'eqtrd',
              '( %s -> %s = 0 )' % (A1, HL))
    e1 = w.s([ie1, h4], 'eqtr4d', '( %s -> %s = %s )' % (A1, EXP, HL))
    A2 = '( %s /\\ -. 1 <_ %s )' % (Y0, RS)
    e2 = D(w, A2, 'iffalsed', [D(w, A2, 'simpr', [], '-. 1 <_ %s' % RS)], '%s = %s' % (EXP, HL))
    ex = w.s([e1, e2], 'pm2.61dan', '( %s -> %s = %s )' % (Y0, EXP, HL))
    r1 = E(w, Y0, 'oveq2d', [ex], '( %s ^c %s )' % (DDS, EXP), '( %s ^c %s )' % (DDS, HL))
    r2 = E(w, Y0, 'oveq1d', [r1], CXB('S'), '( ( %s ^c %s ) x. %s )' % (DDS, HL, LG))
    r3 = E(w, Y0, 'oveq2d', [r2], '( ( %s x. A ) x. %s )' % (C5E, CXB('S')), '( ( %s x. A ) x. ( ( %s ^c %s ) x. %s ) )' % (C5E, DDS, HL, LG))
    w.qed([cv, r3], 'breqtrd', STATEMENTS['zl2cvx1'])
    go(w, only)
