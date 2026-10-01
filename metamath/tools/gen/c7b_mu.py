"""C7b section 4: the chi mu instance and the nonvanishing of L ( chi ) on Re Z > 1."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
import congr as _cg
from c7b_lch import val, ex_, dchinst, conv_results, formula_of_rhs, NXZ, nxzctx
lin.FASTPATH = True

MUB = '( %s x. ( mmu ` q ) )' % CHV('q')


def chm(w, ante, K, nxk):
    """chi(K) e. CC, ( mmu ` K ) e. CC, ( abs ` ( chi(K) x. ( mmu ` K ) ) ) <_ 1"""
    cc = w.s([nxk, w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (ante, CHV(K)))
    kn = w.s([nxk, w.inst('simpr')], 'syl', '( %s -> %s e. NN )' % (ante, K))
    mz = w.s([kn, w.inst('mucl')], 'syl', '( %s -> ( mmu ` %s ) e. ZZ )' % (ante, K))
    mc = w.s([mz], 'zcnd', '( %s -> ( mmu ` %s ) e. CC )' % (ante, K))
    CM = '( %s x. ( mmu ` %s ) )' % (CHV(K), K)
    m = w.s([cc, mc], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( mmu ` %s ) ) ) )' % (ante, CM, CHV(K), K))
    a1 = w.s([nxk, w.inst('lchrabs')], 'syl', '( %s -> ( abs ` %s ) <_ 1 )' % (ante, CHV(K)))
    a2 = w.s([kn, w.inst('mule1')], 'syl', '( %s -> ( abs ` ( mmu ` %s ) ) <_ 1 )' % (ante, K))
    ar = w.s([mc], 'abscld', '( %s -> ( abs ` ( mmu ` %s ) ) e. RR )' % (ante, K))
    le = w.s([w.s([cc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (ante, CHV(K))), w.s([], '1red', '( %s -> 1 e. RR )' % ante), ar,
              w.s([mc], 'absge0d', '( %s -> 0 <_ ( abs ` ( mmu ` %s ) ) )' % (ante, K)), a1], 'lemul1ad',
             '( %s -> ( ( abs ` %s ) x. ( abs ` ( mmu ` %s ) ) ) <_ ( 1 x. ( abs ` ( mmu ` %s ) ) ) )' % (ante, CHV(K), K, K))
    l2 = w.s([le, w.s([w.s([ar], 'recnd', '( %s -> ( abs ` ( mmu ` %s ) ) e. CC )' % (ante, K))], 'mullidd',
                       '( %s -> ( 1 x. ( abs ` ( mmu ` %s ) ) ) = ( abs ` ( mmu ` %s ) ) )' % (ante, K, K))], 'breqtrd',
             '( %s -> ( ( abs ` %s ) x. ( abs ` ( mmu ` %s ) ) ) <_ ( abs ` ( mmu ` %s ) ) )' % (ante, CHV(K), K, K))
    cmc = w.s([cc, mc], 'mulcld', '( %s -> %s e. CC )' % (ante, CM))
    l3 = w.s([w.s([cmc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (ante, CM)), ar, w.s([], '1red', '( %s -> 1 e. RR )' % ante),
              w.s([m, l2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( abs ` ( mmu ` %s ) ) )' % (ante, CM, K)), a2], 'letrd', '( %s -> ( abs ` %s ) <_ 1 )' % (ante, CM))
    return cc, mc, cmc, l3, kn


if __name__ == '__main__' and (not only or 'lchmuval' in only):
    w = W('lchmuval', 'The value of the coefficient mapping ` chi mu ` .')
    _cg.mptval(w, 'K e. NN', 'q', 'NN', MUB, 'K', w.s([], 'id', '( K e. NN -> K e. NN )'), gen=w.g, name='qed')
    run7b(w)


if __name__ == '__main__' and (not only or 'lchmucfb' in only):
    w = W('lchmucfb', 'The coefficients ` chi mu ` are bounded by ` 1 ` (the ` CFB ` interface of C3).')
    Aq = '( %s /\\ q e. NN )' % NX
    cc, mc, cmc, l3, kn = chm(w, Aq, 'q', w.s([], 'id', '( %s -> %s )' % (Aq, Aq)))
    f = w.s([cmc, w.s([], 'eqid', '%s = %s' % (AXM, AXM))], 'fmptd', '( %s -> %s : NN --> CC )' % (NX, AXM))
    Am = '( %s /\\ m e. NN )' % NX
    cc2, mc2, cmc2, l32, kn2 = chm(w, Am, 'm', w.s([], 'id', '( %s -> %s )' % (Am, Am)))
    vm = w.s([kn2, w.inst('lchmuval')], 'syl', '( %s -> ( %s ` m ) = ( %s x. ( mmu ` m ) ) )' % (Am, AXM, CHV('m')))
    bm = w.s([w.s([vm], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` ( %s x. ( mmu ` m ) ) ) )' % (Am, AXM, CHV('m'))), l32], 'eqbrtrd',
             '( %s -> ( abs ` ( %s ` m ) ) <_ 1 )' % (Am, AXM))
    ral = w.s([bm], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (NX, AXM))
    w.qed([f, w.s([], '1red', '( %s -> 1 e. RR )' % NX), ral], '3jca', '( %s -> %s )' % (NX, CFBX(AXM, '1')))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchmulav' in only):
    w = W('lchmulav', 'The coefficients ` chi mu ` satisfy the log-average bound of ~ dconvlim with ` K = 1 ` (from ~ harmonicubnd ).')
    Ay = '( %s /\\ y e. RR )' % NX
    A1 = '( %s /\\ 1 <_ y )' % Ay
    RG = '( 1 ... ( |_ ` y ) )'
    Ad = '( %s /\\ d e. %s )' % (A1, RG)
    dn = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, RG)), w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % Ad)
    nxd = w.s([w.s([], 'simplll', '( %s -> %s )' % (Ad, NX)), dn], 'jca', '( %s -> ( %s /\\ d e. NN ) )' % (Ad, NX))
    cc, mc, cmc, l3, _ = chm(w, Ad, 'd', nxd)
    vv = w.s([dn, w.inst('lchmuval')], 'syl', '( %s -> ( %s ` d ) = ( %s x. ( mmu ` d ) ) )' % (Ad, AXM, CHV('d')))
    AA = '( abs ` ( %s ` d ) )' % AXM
    ab = w.s([w.s([vv], 'fveq2d', '( %s -> %s = ( abs ` ( %s x. ( mmu ` d ) ) ) )' % (Ad, AA, CHV('d'))), l3], 'eqbrtrd', '( %s -> %s <_ 1 )' % (Ad, AA))
    drp = w.s([dn], 'nnrpd', '( %s -> d e. RR+ )' % Ad)
    aar = w.s([w.s([vv, cmc], 'eqeltrd', '( %s -> ( %s ` d ) e. CC )' % (Ad, AXM))], 'abscld', '( %s -> %s e. RR )' % (Ad, AA))
    td = w.s([aar, w.s([], '1red', '( %s -> 1 e. RR )' % Ad), drp, ab], 'lediv1dd', '( %s -> ( %s / d ) <_ ( 1 / d ) )' % (Ad, AA))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A1, RG))
    adr = w.s([aar, drp], 'rerpdivcld', '( %s -> ( %s / d ) e. RR )' % (Ad, AA))
    odr = w.s([drp], 'rpreccld', '( %s -> ( 1 / d ) e. RR+ )' % Ad)
    odr = w.s([odr], 'rpred', '( %s -> ( 1 / d ) e. RR )' % Ad)
    s1 = w.s([fin, adr, odr, td], 'fsumle', '( %s -> sum_ d e. %s ( %s / d ) <_ sum_ d e. %s ( 1 / d ) )' % (A1, RG, AA, RG))
    yr = w.s([], 'simplr', '( %s -> y e. RR )' % A1)
    y1 = w.s([], 'simpr', '( %s -> 1 <_ y )' % A1)
    hb = w.s([yr, y1, w.inst('harmonicubnd')], 'syl2anc', '( %s -> sum_ m e. %s ( 1 / m ) <_ ( ( log ` y ) + 1 ) )' % (A1, RG))
    cbm = w.s([w.s([], 'oveq2', '( m = d -> ( 1 / m ) = ( 1 / d ) )')], 'cbvsumv', 'sum_ m e. %s ( 1 / m ) = sum_ d e. %s ( 1 / d )' % (RG, RG))
    hb2 = w.s([w.s([cbm], 'a1i', '( %s -> sum_ m e. %s ( 1 / m ) = sum_ d e. %s ( 1 / d ) )' % (A1, RG, RG)), hb], 'eqbrtrrd',
              '( %s -> sum_ d e. %s ( 1 / d ) <_ ( ( log ` y ) + 1 ) )' % (A1, RG))
    SA = 'sum_ d e. %s ( %s / d )' % (RG, AA)
    ypos = lin.linarith(w, A1, [y1], '0 < y', leaves={'y': yr})
    yrp = w.s([yr, ypos], 'elrpd', '( %s -> y e. RR+ )' % A1)
    RHS = '( ( log ` y ) + 1 )'
    rr = w.s([w.s([yrp], 'relogcld', '( %s -> ( log ` y ) e. RR )' % A1), w.s([], '1red', '( %s -> 1 e. RR )' % A1)], 'readdcld', '( %s -> %s e. RR )' % (A1, RHS))
    s2 = w.s([w.s([fin, adr], 'fsumrecl', '( %s -> %s e. RR )' % (A1, SA)), w.s([fin, odr], 'fsumrecl', '( %s -> sum_ d e. %s ( 1 / d ) e. RR )' % (A1, RG)),
              rr, s1, hb2], 'letrd', '( %s -> %s <_ %s )' % (A1, SA, RHS))
    im = w.s([s2], 'ex', '( %s -> ( 1 <_ y -> %s <_ %s ) )' % (Ay, SA, RHS))
    ral = w.s([im], 'ralrimiva', '( %s -> A. y e. RR ( 1 <_ y -> %s <_ %s ) )' % (NX, SA, RHS))
    f = w.s([w.s([], 'lchmucfb', '( %s -> %s )' % (NX, CFBX(AXM, '1'))), w.inst('simp1')], 'syl', '( %s -> %s : NN --> CC )' % (NX, AXM))
    w.qed([f, w.s([], '1red', '( %s -> 1 e. RR )' % NX), ral], '3jca', '( %s -> %s )' % (NX, LAV(AXM, '1')))
    run7b(w)

IF1 = 'if ( K = 1 , 1 , 0 )'

if __name__ == '__main__' and (not only or 'lchmucv' in only):
    w = W('lchmucv', 'The Dirichlet convolution of ` chi mu ` and ` chi ` is the unit ` if ( K = 1 , 1 , 0 ) ` (from ~ musum and ~ dchrzrhmul ).')
    A0 = '( %s /\\ K e. NN )' % NX
    DV = '{ x e. NN | x || K }'
    Ad = '( %s /\\ d e. %s )' % (A0, DV)
    nx0 = w.s([], 'simpl', '( %s -> %s )' % (A0, NX))
    kn0 = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
    dd = w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, DV))
    ss = w.s([w.s([], 'ssrab2', '%s C_ NN' % DV)], 'a1i', '( %s -> %s C_ NN )' % (Ad, DV))
    dn = w.s([ss, dd], 'sseldd', '( %s -> d e. NN )' % Ad)
    kd = w.s([kn0], 'adantr', '( %s -> K e. NN )' % Ad)
    nxa = w.s([nx0], 'adantr', '( %s -> %s )' % (Ad, NX))
    qn = w.s([ss, w.s([kd, dd, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( K / d ) e. %s )' % (Ad, DV))], 'sseldd', '( %s -> ( K / d ) e. NN )' % Ad)
    v1 = w.s([dn, w.inst('lchmuval')], 'syl', '( %s -> ( %s ` d ) = ( %s x. ( mmu ` d ) ) )' % (Ad, AXM, CHV('d')))
    nxq = w.s([nxa, qn], 'jca', '( %s -> ( %s /\\ ( K / d ) e. NN ) )' % (Ad, NX))
    v2 = w.s([nxq, w.inst('lchrval')], 'syl', '( %s -> ( %s ` ( K / d ) ) = %s )' % (Ad, AX, CHV('( K / d )')))
    Cd = CHV('d'); Cq = CHV('( K / d )'); Ck = CHV('K')
    t1 = w.s([v1, v2], 'oveq12d', '( %s -> ( ( %s ` d ) x. ( %s ` ( K / d ) ) ) = ( ( %s x. ( mmu ` d ) ) x. %s ) )' % (Ad, AXM, AX, Cd, Cq))
    nxdd = w.s([nxa, dn], 'jca', '( %s -> ( %s /\\ d e. NN ) )' % (Ad, NX))
    cdc = w.s([nxdd, w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (Ad, Cd))
    cqc = w.s([nxq, w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (Ad, Cq))
    mdc = w.s([w.s([dn, w.inst('mucl')], 'syl', '( %s -> ( mmu ` d ) e. ZZ )' % Ad)], 'zcnd', '( %s -> ( mmu ` d ) e. CC )' % Ad)
    t2 = w.s([cdc, mdc, cqc], 'mul32d', '( %s -> ( ( %s x. ( mmu ` d ) ) x. %s ) = ( ( %s x. %s ) x. ( mmu ` d ) ) )' % (Ad, Cd, Cq, Cd, Cq))
    g, zz, b, l = dchyp(w)
    xd = w.s([nxa, w.inst('simpr')], 'syl', '( %s -> X e. %s )' % (Ad, DC))
    mul = w.s([g, zz, b, l, xd, w.s([dn], 'nnzd', '( %s -> d e. ZZ )' % Ad), w.s([qn], 'nnzd', '( %s -> ( K / d ) e. ZZ )' % Ad)], 'dchrzrhmul',
              '( %s -> %s = ( %s x. %s ) )' % (Ad, CHV('( d x. ( K / d ) )'), Cd, Cq))
    dcc = w.s([dn], 'nncnd', '( %s -> d e. CC )' % Ad)
    can = w.s([w.s([kd], 'nncnd', '( %s -> K e. CC )' % Ad), dcc, w.s([dn], 'nnne0d', '( %s -> d =/= 0 )' % Ad)], 'divcan2d', '( %s -> ( d x. ( K / d ) ) = K )' % Ad)
    ck = w.s([w.s([can], 'fveq2d', '( %s -> ( %s ` ( d x. ( K / d ) ) ) = ( %s ` K ) )' % (Ad, LH, LH))], 'fveq2d', '( %s -> %s = %s )' % (Ad, CHV('( d x. ( K / d ) )'), Ck))
    cm = w.s([mul, ck], 'eqtr3d', '( %s -> ( %s x. %s ) = %s )' % (Ad, Cd, Cq, Ck))
    t3 = w.s([cm], 'oveq1d', '( %s -> ( ( %s x. %s ) x. ( mmu ` d ) ) = ( %s x. ( mmu ` d ) ) )' % (Ad, Cd, Cq, Ck))
    tt = w.s([w.s([t1, t2], 'eqtrd', '( %s -> ( ( %s ` d ) x. ( %s ` ( K / d ) ) ) = ( ( %s x. %s ) x. ( mmu ` d ) ) )' % (Ad, AXM, AX, Cd, Cq)), t3], 'eqtrd',
             '( %s -> ( ( %s ` d ) x. ( %s ` ( K / d ) ) ) = ( %s x. ( mmu ` d ) ) )' % (Ad, AXM, AX, Ck))
    s1 = w.s([tt], 'sumeq2dv', '( %s -> %s = sum_ d e. %s ( %s x. ( mmu ` d ) ) )' % (A0, CV('K', AXM, AX), DV, Ck))
    ckc = w.s([w.s([nx0, kn0], 'jca', '( %s -> ( %s /\\ K e. NN ) )' % (A0, NX)), w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (A0, Ck))
    fi = w.s([kn0, w.inst('dvdsfi')], 'syl', '( %s -> %s e. Fin )' % (A0, DV))
    s2 = w.s([fi, ckc, mdc], 'fsummulc2', '( %s -> ( %s x. sum_ d e. %s ( mmu ` d ) ) = sum_ d e. %s ( %s x. ( mmu ` d ) ) )' % (A0, Ck, DV, DV, Ck))
    DVN = '{ n e. NN | n || K }'
    ms = w.s([kn0, w.inst('musum')], 'syl', '( %s -> sum_ k e. %s ( mmu ` k ) = %s )' % (A0, DVN, IF1))
    rab = w.s([w.s([], 'breq1', '( n = x -> ( n || K <-> x || K ) )')], 'cbvrabv', '%s = %s' % (DVN, DV))
    sk = w.s([rab], 'sumeq1i', 'sum_ k e. %s ( mmu ` k ) = sum_ k e. %s ( mmu ` k )' % (DVN, DV))
    sd = w.s([w.s([], 'fveq2', '( k = d -> ( mmu ` k ) = ( mmu ` d ) )')], 'cbvsumv', 'sum_ k e. %s ( mmu ` k ) = sum_ d e. %s ( mmu ` d )' % (DV, DV))
    skd = w.s([sk, sd], 'eqtri', 'sum_ k e. %s ( mmu ` k ) = sum_ d e. %s ( mmu ` d )' % (DVN, DV))
    ms2 = w.s([w.s([skd], 'a1i', '( %s -> sum_ k e. %s ( mmu ` k ) = sum_ d e. %s ( mmu ` d ) )' % (A0, DVN, DV)), ms], 'eqtr3d',
              '( %s -> sum_ d e. %s ( mmu ` d ) = %s )' % (A0, DV, IF1))
    s3 = w.s([ms2], 'oveq2d', '( %s -> ( %s x. sum_ d e. %s ( mmu ` d ) ) = ( %s x. %s ) )' % (A0, Ck, DV, Ck, IF1))
    s123 = w.s([w.s([s1, s2], 'eqtr4d', '( %s -> %s = ( %s x. sum_ d e. %s ( mmu ` d ) ) )' % (A0, CV('K', AXM, AX), Ck, DV)), s3], 'eqtrd',
               '( %s -> %s = ( %s x. %s ) )' % (A0, CV('K', AXM, AX), Ck, IF1))
    # the case split
    Bt = '( %s /\\ K = 1 )' % A0
    it = w.s([w.s([], 'simpr', '( %s -> K = 1 )' % Bt)], 'iftrued', '( %s -> %s = 1 )' % (Bt, IF1))
    k1 = w.s([], 'simpr', '( %s -> K = 1 )' % Bt)
    c1 = w.s([w.s([k1], 'fveq2d', '( %s -> ( %s ` K ) = ( %s ` 1 ) )' % (Bt, LH, LH))], 'fveq2d', '( %s -> %s = %s )' % (Bt, Ck, CHV('1')))
    g2, zz2, b2, l2 = dchyp(w)
    xb = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, NX)), w.inst('simpr')], 'syl', '( %s -> X e. %s )' % (A0, DC))], 'adantr', '( %s -> X e. %s )' % (Bt, DC))
    c11 = w.s([g2, zz2, b2, l2, xb], 'dchrzrh1', '( %s -> %s = 1 )' % (Bt, CHV('1')))
    cK1 = w.s([c1, c11], 'eqtrd', '( %s -> %s = 1 )' % (Bt, Ck))
    lt = w.s([cK1, it], 'oveq12d', '( %s -> ( %s x. %s ) = ( 1 x. 1 ) )' % (Bt, Ck, IF1))
    lt2 = w.s([lt, w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % Bt)], 'eqtrd', '( %s -> ( %s x. %s ) = 1 )' % (Bt, Ck, IF1))
    case1 = w.s([lt2, it], 'eqtr4d', '( %s -> ( %s x. %s ) = %s )' % (Bt, Ck, IF1, IF1))
    Bf = '( %s /\\ -. K = 1 )' % A0
    iff = w.s([w.s([], 'simpr', '( %s -> -. K = 1 )' % Bf)], 'iffalsed', '( %s -> %s = 0 )' % (Bf, IF1))
    lf = w.s([iff], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. 0 ) )' % (Bf, Ck, IF1, Ck))
    lf2 = w.s([lf, w.s([w.s([ckc], 'adantr', '( %s -> %s e. CC )' % (Bf, Ck))], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (Bf, Ck))], 'eqtrd',
              '( %s -> ( %s x. %s ) = 0 )' % (Bf, Ck, IF1))
    case2 = w.s([lf2, iff], 'eqtr4d', '( %s -> ( %s x. %s ) = %s )' % (Bf, Ck, IF1, IF1))
    cs = w.s([case1, case2], 'pm2.61dan', '( %s -> ( %s x. %s ) = %s )' % (A0, Ck, IF1, IF1))
    w.qed([s123, cs], 'eqtrd', '( %s -> %s = %s )' % (A0, CV('K', AXM, AX), IF1))
    run7b(w)

IFK = 'if ( k = 1 , 1 , 0 )'
UT = '( %s x. ( k ^c -u Z ) )' % IFK

if __name__ == '__main__' and (not only or 'lchmuser' in only):
    w = W('lchmuser', 'The Dirichlet series of the unit ` if ( k = 1 , 1 , 0 ) ` is ` 1 ` .')
    ph = 'Z e. CC'
    zc = w.s([], 'id', '( Z e. CC -> Z e. CC )')
    one_nn = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % ph)
    sss = w.s([one_nn], 'snssd', '( %s -> { 1 } C_ NN )' % ph)

    def utcl(ante, kn, zca):
        ic = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % ante), w.s([], '0cnd', '( %s -> 0 e. CC )' % ante)], 'ifcld', '( %s -> %s e. CC )' % (ante, IFK))
        return w.s([ic, cxpz(w, ante, 'k', kn, zca)], 'mulcld', '( %s -> %s e. CC )' % (ante, UT))
    As = '( %s /\\ k e. { 1 } )' % ph
    ks = w.s([w.s([sss], 'adantr', '( %s -> { 1 } C_ NN )' % As), w.s([], 'simpr', '( %s -> k e. { 1 } )' % As)], 'sseldd', '( %s -> k e. NN )' % As)
    c2 = utcl(As, ks, w.s([zc], 'adantr', '( %s -> Z e. CC )' % As))
    Ad = '( %s /\\ k e. ( NN \\ { 1 } ) )' % ph
    kd = w.s([w.s([], 'simpr', '( %s -> k e. ( NN \\ { 1 } ) )' % Ad), w.inst('eldifsn')], 'sylib', '( %s -> ( k e. NN /\\ k =/= 1 ) )' % Ad)
    kn1 = w.s([w.s([kd], 'simprd', '( %s -> k =/= 1 )' % Ad)], 'neneqd', '( %s -> -. k = 1 )' % Ad)
    iff = w.s([kn1], 'iffalsed', '( %s -> %s = 0 )' % (Ad, IFK))
    kdn = w.s([kd], 'simpld', '( %s -> k e. NN )' % Ad)
    pc = cxpz(w, Ad, 'k', kdn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad))
    c3 = w.s([w.s([iff], 'oveq1d', '( %s -> %s = ( 0 x. ( k ^c -u Z ) ) )' % (Ad, UT)), w.s([pc], 'mul02d', '( %s -> ( 0 x. ( k ^c -u Z ) ) = 0 )' % Ad)],
             'eqtrd', '( %s -> %s = 0 )' % (Ad, UT))
    c4 = w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqimssi', 'NN C_ ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN C_ ( ZZ>= ` 1 ) )' % ph)
    ss = w.s([sss, c2, c3, c4], 'sumss', '( %s -> sum_ k e. { 1 } %s = sum_ k e. NN %s )' % (ph, UT, UT))
    B1 = '( if ( 1 = 1 , 1 , 0 ) x. ( 1 ^c -u Z ) )'
    sb = w.s([], 'eqeq1', '( k = 1 -> ( k = 1 <-> 1 = 1 ) )')
    sif = w.s([sb], 'ifbid', '( k = 1 -> %s = if ( 1 = 1 , 1 , 0 ) )' % IFK)
    sp = w.s([], 'oveq1', '( k = 1 -> ( k ^c -u Z ) = ( 1 ^c -u Z ) )')
    sub = w.s([sif, sp], 'oveq12d', '( k = 1 -> %s = %s )' % (UT, B1))
    e11 = w.s([w.s([], 'eqid', '1 = 1')], 'a1i', '( %s -> 1 = 1 )' % ph)
    it = w.s([e11], 'iftrued', '( %s -> if ( 1 = 1 , 1 , 0 ) = 1 )' % ph)
    c1 = w.s([w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % ph), w.inst('1cxp')], 'syl', '( %s -> ( 1 ^c -u Z ) = 1 )' % ph)
    b1 = w.s([w.s([it, c1], 'oveq12d', '( %s -> %s = ( 1 x. 1 ) )' % (ph, B1)), w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % ph)],
             'eqtrd', '( %s -> %s = 1 )' % (ph, B1))
    b1c = w.s([b1, w.s([], '1cnd', '( %s -> 1 e. CC )' % ph)], 'eqeltrd', '( %s -> %s e. CC )' % (ph, B1))
    sn = w.s([sub], 'sumsn', '( ( 1 e. NN /\\ %s e. CC ) -> sum_ k e. { 1 } %s = %s )' % (B1, UT, B1))
    sn2 = w.s([one_nn, b1c, sn], 'syl2anc', '( %s -> sum_ k e. { 1 } %s = %s )' % (ph, UT, B1))
    w.qed([w.s([ss, sn2], 'eqtr3d', '( %s -> sum_ k e. NN %s = %s )' % (ph, UT, B1)), b1], 'eqtrd', '( %s -> sum_ k e. NN %s = 1 )' % (ph, UT))
    run7b(w)


def sermu_eq(w, A0, nx):
    """( A0 -> SER(AXM) = sum_ k e. NN MUT(k) ) and ( A0 -> SER(AX) = sum_ k e. NN CHT(k) )"""
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nxk = w.s([w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX)), kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (Ak, NX))
    vk = w.s([kn, w.inst('lchmuval')], 'syl', '( %s -> ( %s ` k ) = ( %s x. ( mmu ` k ) ) )' % (Ak, AXM, CHV('k')))
    s2 = w.s([w.s([vk], 'oveq1d', '( %s -> %s = %s )' % (Ak, TRM(AXM, 'k'), MUT('k')))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (A0, SER(AXM), MUT('k')))
    ck = w.s([nxk, w.inst('lchrval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Ak, AX, CHV('k')))
    s3 = w.s([w.s([ck], 'oveq1d', '( %s -> %s = %s )' % (Ak, TRM(AX, 'k'), CHT('k')))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (A0, SER(AX), CHT('k')))
    return s2, s3, nxk, kn, Ak


if __name__ == '__main__' and (not only or 'lchrmu' in only):
    w = W('lchrmu', '` L ( chi mu ) L ( chi ) = 1 ` on ` Re Z > 1 ` , the instance of ~ dconvlim at ` A = chi mu ` , ` B = chi ` .')
    A0 = NXZ
    nx, zp = nxzctx(w, A0)
    z = zctx(w, A0, zp)
    lav = w.s([nx, w.inst('lchmulav')], 'syl', '( %s -> %s )' % (A0, LAV(AXM, '1')))
    cfb = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX(AX, '1')))
    cfbm = w.s([nx, w.inst('lchmucfb')], 'syl', '( %s -> %s )' % (A0, CFBX(AXM, '1')))
    cvg = w.s([w.s([cfbm, zp], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CFBX(AXM, '1'), ZP1)), w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAP(AXM)))
    meq = w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, MAP(AXM), MAP(AXM)))
    dch, D = dchinst(w, A0, AXM, AX, '1', '1', lav, cfb, zp, meq, cvg)
    dm, sm = conv_results(w, A0, AXM, AX, '1', '1', dch, D)
    s2, s3, nxk, kn, Ak = sermu_eq(w, A0, nx)
    cvk = w.s([nxk, w.inst('lchmucv')], 'syl', '( %s -> %s = %s )' % (Ak, CV('k', AXM, AX), IFK))
    s1 = w.s([w.s([cvk], 'oveq1d', '( %s -> %s = %s )' % (Ak, CTRM('k', A=AXM, B=AX), UT))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (A0, CSER(A=AXM, B=AX), UT))
    one = w.s([z['zc'], w.inst('lchmuser')], 'syl', '( %s -> sum_ k e. NN %s = 1 )' % (A0, UT))
    cs1 = w.s([s1, one], 'eqtrd', '( %s -> %s = 1 )' % (A0, CSER(A=AXM, B=AX)))
    s23 = w.s([s2, s3], 'oveq12d', '( %s -> ( %s x. %s ) = ( sum_ k e. NN %s x. sum_ k e. NN %s ) )' % (A0, SER(AXM), SER(AX), MUT('k'), CHT('k')))
    w.qed([w.s([sm, s23], 'eqtrd', '( %s -> %s = ( sum_ k e. NN %s x. sum_ k e. NN %s ) )' % (A0, CSER(A=AXM, B=AX), MUT('k'), CHT('k'))), cs1], 'eqtr3d',
          '( %s -> ( sum_ k e. NN %s x. sum_ k e. NN %s ) = 1 )' % (A0, MUT('k'), CHT('k')))
    run7b(w)

if __name__ == '__main__' and (not only or 'lchrne0' in only):
    w = W('lchrne0', '` L ( chi ) =/= 0 ` on ` Re Z > 1 ` (Mathlib ` LFunction_ne_zero_of_one_le_re ` on the open half-plane), from ~ lchrmu .')
    A0 = NXZ
    nx, zp = nxzctx(w, A0)
    s2, s3, nxk, kn, Ak = sermu_eq(w, A0, nx)
    cfb = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX(AX, '1')))
    cfbm = w.s([nx, w.inst('lchmucfb')], 'syl', '( %s -> %s )' % (A0, CFBX(AXM, '1')))
    c1 = w.s([w.s([cfbm, zp], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CFBX(AXM, '1'), ZP1)), w.inst('dsercl')], 'syl', '( %s -> %s e. CC )' % (A0, SER(AXM)))
    c2 = w.s([w.s([cfb, zp], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, CFBX(AX, '1'), ZP1)), w.inst('dsercl')], 'syl', '( %s -> %s e. CC )' % (A0, SER(AX)))
    SM = 'sum_ k e. NN %s' % MUT('k')
    SC = 'sum_ k e. NN %s' % CHT('k')
    m1 = w.s([s2, c1], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, SM))
    m2 = w.s([s3, c2], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, SC))
    pr = w.s([w.s([], 'lchrmu', '( %s -> ( %s x. %s ) = 1 )' % (A0, SM, SC)), w.s([w.s([], 'ax-1ne0', '1 =/= 0')], 'a1i', '( %s -> 1 =/= 0 )' % A0)], 'eqnetrd',
             '( %s -> ( %s x. %s ) =/= 0 )' % (A0, SM, SC))
    bi = w.s([m1, m2, w.inst('mulne0b')], 'syl2anc', '( %s -> ( ( %s =/= 0 /\\ %s =/= 0 ) <-> ( %s x. %s ) =/= 0 ) )' % (A0, SM, SC, SM, SC))
    both = w.s([pr, bi], 'mpbird', '( %s -> ( %s =/= 0 /\\ %s =/= 0 ) )' % (A0, SM, SC))
    w.qed([both], 'simprd', '( %s -> %s =/= 0 )' % (A0, SC))
    run7b(w)
