"""EF1 section 2: interval-integral helpers (ExplicitFormula 238-443).
`MM_DB=sorties/ef1.mm python3 tools/gen/ef1_b.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef1lib import *
from lin import linarith, nlinarith, lineq

only = sys.argv[1:]
X = '( P (,) Q )'
XC = '( P [,] Q )'
JR = '( ( TopOpen ` CCfld ) |`t RR )'
TOPC = '( TopOpen ` CCfld )'


def hyps(w, lab):
    for nm, f in HYPS[lab]:
        w.s([], '%s.%s' % (lab, nm), f, name='h' + nm)


# ---------------------------------------------------------------- ef1ftc: ftc2 with the derivative on the open interval
if __name__ == '__main__' and (not only or 'ef1ftc' in only):
    w = W('ef1ftc', 'The fundamental theorem of calculus in the form the interval helpers use: a primitive ` G ` '
          'continuous on ` [ P , Q ] ` whose derivative on ` ( P , Q ) ` is ` H ` , continuous on ` [ P , Q ] ` : '
          'then ` H ` is integrable on ` ( P , Q ) ` and ` S. ( P , Q ) H = G ( Q ) - G ( P ) ` ( ~ ftc2 with '
          '~ dvmptntr ; Lean ` integral_eq_sub_of_hasDerivAt ` ).')
    hyps(w, 'ef1ftc')
    ph = 'ph'
    FC = '( t e. %s |-> G )' % XC
    FO = '( t e. %s |-> G )' % X
    HC = '( t e. %s |-> H )' % XC
    HO = '( t e. %s |-> H )' % X
    pr = D(w, ph, 'simp1d', ['h1'], 'P e. RR')
    qr = D(w, ph, 'simp2d', ['h1'], 'Q e. RR')
    le = D(w, ph, 'simp3d', ['h1'], 'P <_ Q')
    ssr = w.s([pr, qr, w.inst('iccssre')], 'syl2anc', '( ph -> %s C_ RR )' % XC)
    # G, H are complex on the closed interval
    ffc = w.s(['h2', w.inst('cncff')], 'syl', '( ph -> %s : %s --> CC )' % (FC, XC))
    fmg = w.s([w.s([], 'eqid', '%s = %s' % (FC, FC))], 'fmpt', '( A. t e. %s G e. CC <-> %s : %s --> CC )' % (XC, FC, XC))
    ralg = w.s([ffc, w.s([fmg], 'a1i', '( ph -> ( A. t e. %s G e. CC <-> %s : %s --> CC ) )' % (XC, FC, XC))], 'mpbird', '( ph -> A. t e. %s G e. CC )' % XC)
    gcc = w.s([ralg], 'r19.21bi', '( ( ph /\\ t e. %s ) -> G e. CC )' % XC)
    fhc = w.s(['h4', w.inst('cncff')], 'syl', '( ph -> %s : %s --> CC )' % (HC, XC))
    fmh = w.s([w.s([], 'eqid', '%s = %s' % (HC, HC))], 'fmpt', '( A. t e. %s H e. CC <-> %s : %s --> CC )' % (XC, HC, XC))
    ralh = w.s([fhc, w.s([fmh], 'a1i', '( ph -> ( A. t e. %s H e. CC <-> %s : %s --> CC ) )' % (XC, HC, XC))], 'mpbird', '( ph -> A. t e. %s H e. CC )' % XC)
    hcc = w.s([ralh], 'r19.21bi', '( ( ph /\\ t e. %s ) -> H e. CC )' % XC)
    # the derivative of the closed-interval primitive
    icc0 = w.s([pr, qr, w.inst('iccntr')], 'syl2anc', '( ph -> ( ( int ` ( topGen ` ran (,) ) ) ` %s ) = %s )' % (XC, X))
    jeq2 = w.s([w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)], 'eqcomi', '%s = ( topGen ` ran (,) )' % JR)
    icc = w.s([w.s([w.s([jeq2], 'a1i', '( ph -> %s = ( topGen ` ran (,) ) )' % JR)], 'fveq2d', '( ph -> ( int ` %s ) = ( int ` ( topGen ` ran (,) ) ) )' % JR)], 'fveq1d',
              '( ph -> ( ( int ` %s ) ` %s ) = ( ( int ` ( topGen ` ran (,) ) ) ` %s ) )' % (JR, XC, XC))
    icc2 = w.s([icc, icc0], 'eqtrd', '( ph -> ( ( int ` %s ) ` %s ) = %s )' % (JR, XC, X))
    ntr = w.s([a1(w, ph, 'ax-resscn', 'RR C_ CC'), ssr, gcc, w.s([], 'eqid', '%s = %s' % (JR, JR)), w.s([], 'eqid', '%s = %s' % (TOPC, TOPC)), icc2], 'dvmptntr',
              '( ph -> ( RR _D %s ) = ( RR _D %s ) )' % (FC, FO))
    dvf = w.s([ntr, 'h3'], 'eqtrd', '( ph -> ( RR _D %s ) = %s )' % (FC, HO))
    # H on the open interval: continuous and integrable
    ioss = a1(w, ph, 'ioossicc', '%s C_ %s' % (X, XC))
    rci = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('rescncf')], 'ax-mp', '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HC, XC, HC, X, X))
    hres = w.s(['h4', rci], 'syl', '( ph -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HC, X, X))
    rsm = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (HC, X, HO))
    hocn = w.s([w.s([rsm], 'a1i', '( ph -> ( %s |` %s ) = %s )' % (HC, X, HO)), hres], 'eqeltrrd', '( ph -> %s e. ( %s -cn-> CC ) )' % (HO, X))
    hcibl = w.s([pr, qr, 'h4', w.inst('cniccibl')], 'syl3anc', '( ph -> %s e. L^1 )' % HC)
    hoibl = w.s([ioss, a1(w, ph, 'ioombl', '%s e. dom vol' % X), hcc, hcibl], 'iblss', '( ph -> %s e. L^1 )' % HO)
    dcn = w.s([dvf, hocn], 'eqeltrd', '( ph -> ( RR _D %s ) e. ( %s -cn-> CC ) )' % (FC, X))
    dib = w.s([dvf, hoibl], 'eqeltrd', '( ph -> ( RR _D %s ) e. L^1 )' % FC)
    ftc = w.s([pr, qr, le, dcn, dib, 'h2'], 'ftc2', '( ph -> S. %s ( ( RR _D %s ) ` x ) _d x = ( ( %s ` Q ) - ( %s ` P ) ) )' % (X, FC, FC, FC))
    # the integrand
    e2 = w.s([e1], 'itgeq2dv', '( ph -> S. %s ( ( RR _D %s ) ` x ) _d x = S. %s ( %s ` x ) _d x )' % (X, FC, X, HO))
    nf1 = w.s([w.s([], 'nfmpt1', 'F/_ t %s' % HO), w.s([], 'nfcv', 'F/_ t x')], 'nffv', 'F/_ t ( %s ` x )' % HO)
    nf2 = w.s([], 'nfcv', 'F/_ x ( %s ` t )' % HO)
    e3 = w.s([w.s([], 'fveq2', '( x = t -> ( %s ` x ) = ( %s ` t ) )' % (HO, HO)), nf1, nf2], 'cbvitg', 'S. %s ( %s ` x ) _d x = S. %s ( %s ` t ) _d t' % (X, HO, X, HO))
    AO = '( ph /\\ t e. %s )' % X
    tcc = w.s([w.s([ioss], 'adantr', '( %s -> %s C_ %s )' % (AO, X, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (AO, X))], 'sseldd', '( %s -> t e. %s )' % (AO, XC))
    hccO = w.s([w.s([], 'simpl', '( %s -> ph )' % AO), tcc, hcc], 'syl2anc', '( %s -> H e. CC )' % AO)
    e4 = w.s([w.s([w.s([], 'eqid', '%s = %s' % (HO, HO))], 'a1i', '( ph -> %s = %s )' % (HO, HO)), hccO], 'fvmpt2d', '( %s -> ( %s ` t ) = H )' % (AO, HO))
    e5 = w.s([e4], 'itgeq2dv', '( ph -> S. %s ( %s ` t ) _d t = S. %s H _d t )' % (X, HO, X))
    i1 = w.s([e2, w.s([e3], 'a1i', '( ph -> S. %s ( %s ` x ) _d x = S. %s ( %s ` t ) _d t )' % (X, HO, X, HO))], 'eqtrd', '( ph -> S. %s ( ( RR _D %s ) ` x ) _d x = S. %s ( %s ` t ) _d t )' % (X, FC, X, HO))
    i2 = w.s([i1, e5], 'eqtrd', '( ph -> S. %s ( ( RR _D %s ) ` x ) _d x = S. %s H _d t )' % (X, FC, X))
    # the endpoint values
    axr = D(w, ph, 'rexrd', [pr], 'P e. RR*'); bxr = D(w, ph, 'rexrd', [qr], 'Q e. RR*')
    qin = w.s([axr, bxr, le, w.inst('ubicc2')], 'syl3anc', '( ph -> Q e. %s )' % XC)
    pin = w.s([axr, bxr, le, w.inst('lbicc2')], 'syl3anc', '( ph -> P e. %s )' % XC)
    sbi = w.s(['h6'], 'eleq1d', '( t = Q -> ( G e. CC <-> S e. CC ) )')
    scc = w.s([sbi, ralg, qin], 'rspcdva', '( ph -> S e. CC )')
    rbi = w.s(['h5'], 'eleq1d', '( t = P -> ( G e. CC <-> R e. CC ) )')
    rcc = w.s([rbi, ralg, pin], 'rspcdva', '( ph -> R e. CC )')
    vq = w.s([w.s([w.s([], 'eqid', '%s = %s' % (FC, FC))], 'a1i', '( ph -> %s = %s )' % (FC, FC)), w.s(['h6'], 'adantl', '( ( ph /\\ t = Q ) -> G = S )'), qin, scc], 'fvmptd',
             '( ph -> ( %s ` Q ) = S )' % FC)
    vp = w.s([w.s([w.s([], 'eqid', '%s = %s' % (FC, FC))], 'a1i', '( ph -> %s = %s )' % (FC, FC)), w.s(['h5'], 'adantl', '( ( ph /\\ t = P ) -> G = R )'), pin, rcc], 'fvmptd',
             '( ph -> ( %s ` P ) = R )' % FC)
    val = w.s([vq, vp], 'oveq12d', '( ph -> ( ( %s ` Q ) - ( %s ` P ) ) = ( S - R ) )' % (FC, FC))
    res = w.s([w.s([i2], 'eqcomd', '( ph -> S. %s H _d t = S. %s ( ( RR _D %s ) ` x ) _d x )' % (X, X, FC)), w.s([ftc, val], 'eqtrd', '( ph -> S. %s ( ( RR _D %s ) ` x ) _d x = ( S - R ) )' % (X, FC))],
              'eqtrd', '( ph -> S. %s H _d t = ( S - R ) )' % X)
    w.qed([hoibl, res], 'jca', STATEMENTS['ef1ftc'])
    go(w, only)

# ---------------------------------------------------------------- ef1faf: FTC through an affine substitution
if __name__ == '__main__' and (not only or 'ef1faf' in only):
    w = W('ef1faf', 'The fundamental theorem of calculus through an affine substitution: if ` A ( y ) ` has the '
          'continuous derivative ` B ( y ) ` on ` RR+ ` and ` K t + H > 0 ` on ` [ P , Q ] ` , then '
          '` S. ( P , Q ) B ( K t + H ) _d t = ( A ( K Q + H ) - A ( K P + H ) ) / K ` ( ~ ef1ftc , ~ dvmptco , '
          '~ cncfcompt2 ).  Both interval helpers of ExplicitFormula are instances.')
    hyps(w, 'ef1faf')
    ph = 'ph'
    KH = '( ( K x. t ) + H )'
    c1 = D(w, ph, 'simpld', ['h1'], '( K e. RR /\\ K =/= 0 /\\ H e. RR )')
    c2 = D(w, ph, 'simprd', ['h1'], '( P e. RR /\\ Q e. RR /\\ P <_ Q )')
    kr = D(w, ph, 'simp1d', [c1], 'K e. RR'); kne = D(w, ph, 'simp2d', [c1], 'K =/= 0'); hr = D(w, ph, 'simp3d', [c1], 'H e. RR')
    pr = D(w, ph, 'simp1d', [c2], 'P e. RR'); qr = D(w, ph, 'simp2d', [c2], 'Q e. RR'); le = D(w, ph, 'simp3d', [c2], 'P <_ Q')
    kc = D(w, ph, 'recnd', [kr], 'K e. CC'); hc = D(w, ph, 'recnd', [hr], 'H e. CC')
    ssr = w.s([pr, qr, w.inst('iccssre')], 'syl2anc', '( ph -> %s C_ RR )' % XC)
    AC = '( ph /\\ t e. %s )' % XC
    tr = w.s([w.s([ssr], 'adantr', '( %s -> %s C_ RR )' % (AC, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (AC, XC))], 'sseldd', '( %s -> t e. RR )' % AC)
    khr = w.s([w.s([w.s([kr], 'adantr', '( %s -> K e. RR )' % AC), tr], 'remulcld', '( %s -> ( K x. t ) e. RR )' % AC), w.s([hr], 'adantr', '( %s -> H e. RR )' % AC)], 'readdcld',
              '( %s -> %s e. RR )' % (AC, KH))
    khp = w.s(['h2'], 'r19.21bi', '( %s -> 0 < %s )' % (AC, KH))
    khrp = w.s([khr, khp], 'elrpd', '( %s -> %s e. RR+ )' % (AC, KH))
    AO = '( ph /\\ t e. %s )' % X
    toc = w.s([w.s([a1(w, ph, 'ioossicc', '%s C_ %s' % (X, XC))], 'adantr', '( %s -> %s C_ %s )' % (AO, X, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (AO, X))], 'sseldd',
              '( %s -> t e. %s )' % (AO, XC))
    khrpo = w.s([w.s([], 'simpl', '( %s -> ph )' % AO), toc, w.s([khrp], 'ex', '( ph -> ( t e. %s -> %s e. RR+ ) )' % (XC, KH))], 'sylc', '( %s -> %s e. RR+ )' % (AO, KH))
    # B and A are complex on RR+; the values C, E are complex on [ P , Q ]
    BM = '( y e. RR+ |-> B )'; AM = '( y e. RR+ |-> A )'
    fb = w.s(['h5', w.inst('cncff')], 'syl', '( ph -> %s : RR+ --> CC )' % BM)
    fmb = w.s([w.s([], 'eqid', '%s = %s' % (BM, BM))], 'fmpt', '( A. y e. RR+ B e. CC <-> %s : RR+ --> CC )' % BM)
    ralb = w.s([fb, w.s([fmb], 'a1i', '( ph -> ( A. y e. RR+ B e. CC <-> %s : RR+ --> CC ) )' % BM)], 'mpbird', '( ph -> A. y e. RR+ B e. CC )')
    bcc = w.s([ralb], 'r19.21bi', '( ( ph /\\ y e. RR+ ) -> B e. CC )')
    rala = w.s(['h3'], 'ralrimiva', '( ph -> A. y e. RR+ A e. CC )')
    ecc = w.s([w.s(['h7'], 'eleq1d', '( y = %s -> ( B e. CC <-> E e. CC ) )' % KH), w.s([ralb], 'adantr', '( %s -> A. y e. RR+ B e. CC )' % AC), khrp], 'rspcdva', '( %s -> E e. CC )' % AC)
    ccc = w.s([w.s(['h6'], 'eleq1d', '( y = %s -> ( A e. CC <-> C e. CC ) )' % KH), w.s([rala], 'adantr', '( %s -> A. y e. RR+ A e. CC )' % AC), khrp], 'rspcdva', '( %s -> C e. CC )' % AC)
    ecco = w.s([w.s([], 'simpl', '( %s -> ph )' % AO), toc, w.s([ecc], 'ex', '( ph -> ( t e. %s -> E e. CC ) )' % XC)], 'sylc', '( %s -> E e. CC )' % AO)
    ccco = w.s([w.s([], 'simpl', '( %s -> ph )' % AO), toc, w.s([ccc], 'ex', '( ph -> ( t e. %s -> C e. CC ) )' % XC)], 'sylc', '( %s -> C e. CC )' % AO)
    # A is continuous on RR+ (it is differentiable there)
    fa = w.s(['h3', w.s([], 'eqid', '%s = %s' % (AM, AM))], 'fmptd', '( ph -> %s : RR+ --> CC )' % AM)
    dma = w.s([w.s([w.s(['h4'], 'dmeqd', '( ph -> dom ( RR _D %s ) = dom %s )' % (AM, BM)), w.s([ralb, w.inst('dmmptg')], 'syl', '( ph -> dom %s = RR+ )' % BM)], 'eqtrd',
                   '( ph -> dom ( RR _D %s ) = RR+ )' % AM)], 'idi', '( ph -> dom ( RR _D %s ) = RR+ )' % AM)
    acn = w.s([w.s([a1(w, ph, 'ax-resscn', 'RR C_ CC'), fa, a1(w, ph, 'rpssre', 'RR+ C_ RR')], '3jca', '( ph -> ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) )' % AM), dma, w.inst('dvcn')],
              'syl2anc', '( ph -> %s e. ( RR+ -cn-> CC ) )' % AM)
    # the affine map is continuous from [ P , Q ] into RR+
    usscn = w.s([ssr, a1(w, ph, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( ph -> %s C_ CC )' % XC)
    sscc = a1(w, ph, 'ssid', 'CC C_ CC')
    idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( ph -> ( t e. %s |-> t ) e. ( %s -cn-> CC ) )' % (XC, XC))
    kcn = w.s([kc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( ph -> ( t e. %s |-> K ) e. ( %s -cn-> CC ) )' % (XC, XC))
    hcn = w.s([hc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( ph -> ( t e. %s |-> H ) e. ( %s -cn-> CC ) )' % (XC, XC))
    ktc = w.s([kcn, idc], 'mulcncf', '( ph -> ( t e. %s |-> ( K x. t ) ) e. ( %s -cn-> CC ) )' % (XC, XC))
    affc = w.s([ktc, hcn], 'addcncf', '( ph -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (XC, KH, XC))
    AFM = '( t e. %s |-> %s )' % (XC, KH)
    faff = w.s([khrp, w.s([], 'eqid', '%s = %s' % (AFM, AFM))], 'fmptd', '( ph -> %s : %s --> RR+ )' % (AFM, XC))
    rpcc = w.s([a1(w, ph, 'rpssre', 'RR+ C_ RR'), a1(w, ph, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( ph -> RR+ C_ CC )')
    affb = w.s([faff, w.s([rpcc, affc, w.inst('cncfcdm')], 'syl2anc', '( ph -> ( %s e. ( %s -cn-> RR+ ) <-> %s : %s --> RR+ ) )' % (AFM, XC, AFM, XC))], 'mpbird',
               '( ph -> %s e. ( %s -cn-> RR+ ) )' % (AFM, XC))
    nfph = w.s([], 'nfv', 'F/ t ph')
    ccn = w.s([nfph, affb, acn, a1(w, ph, 'ssid', 'RR+ C_ RR+'), 'h6'], 'cncfcompt2', '( ph -> ( t e. %s |-> C ) e. ( %s -cn-> CC ) )' % (XC, XC))
    ecn = w.s([nfph, affb, 'h5', a1(w, ph, 'ssid', 'RR+ C_ RR+'), 'h7'], 'cncfcompt2', '( ph -> ( t e. %s |-> E ) e. ( %s -cn-> CC ) )' % (XC, XC))
    kn0 = w.s([w.s([kc, kne], 'jca', '( ph -> ( K e. CC /\\ K =/= 0 ) )'), w.inst('eldifsn')], 'sylibr', '( ph -> K e. ( CC \\ { 0 } ) )')
    kcn0 = w.s([kn0, usscn, a1(w, ph, 'difss', '( CC \\ { 0 } ) C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( ph -> ( t e. %s |-> K ) e. ( %s -cn-> ( CC \\ { 0 } ) ) )' % (XC, XC))
    gcn = w.s([ccn, kcn0], 'divcncf', '( ph -> ( t e. %s |-> ( C / K ) ) e. ( %s -cn-> CC ) )' % (XC, XC))
    # the derivative of the affine map on ( P , Q )
    sr = a1(w, ph, 'reelprrecn', 'RR e. { RR , CC }')
    ARR = '( ph /\\ t e. RR )'
    trr = w.s([], 'simpr', '( %s -> t e. RR )' % ARR)
    tcr = D(w, ARR, 'recnd', [trr], 't e. CC')
    kcr = w.s([kc], 'adantr', '( %s -> K e. CC )' % ARR); hcr = w.s([hc], 'adantr', '( %s -> H e. CC )' % ARR)
    oner = a1(w, ARR, 'ax-1cn', '1 e. CC'); zcr = a1(w, ARR, '0cn', '0 e. CC')
    dvi = w.s([sr], 'dvmptid', '( ph -> ( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 ) )')
    dvk = w.s([sr, tcr, oner, dvi, kc], 'dvmptcmul', '( ph -> ( RR _D ( t e. RR |-> ( K x. t ) ) ) = ( t e. RR |-> ( K x. 1 ) ) )')
    dvh = w.s([sr, hc], 'dvmptc', '( ph -> ( RR _D ( t e. RR |-> H ) ) = ( t e. RR |-> 0 ) )')
    ktr = D(w, ARR, 'mulcld', [kcr, tcr], '( K x. t ) e. CC')
    k1r = D(w, ARR, 'mulcld', [kcr, oner], '( K x. 1 ) e. CC')
    dva = w.s([sr, ktr, k1r, dvk, hcr, zcr, dvh], 'dvmptadd', '( ph -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( ( K x. 1 ) + 0 ) ) )' % KH)
    khc = D(w, ARR, 'addcld', [ktr, hcr], '%s e. CC' % KH)
    k10 = D(w, ARR, 'addcld', [k1r, zcr], '( ( K x. 1 ) + 0 ) e. CC')
    jeq = w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)
    xopn = w.s([a1(w, ph, 'iooretop', '%s e. ( topGen ` ran (,) )' % X), w.s([jeq], 'a1i', '( ph -> ( topGen ` ran (,) ) = %s )' % JR)], 'eleqtrd', '( ph -> %s e. %s )' % (X, JR))
    dvo = w.s([sr, khc, k10, dva, a1(w, ph, 'ioossre', '%s C_ RR' % X), w.s([], 'eqid', '%s = %s' % (JR, JR)), w.s([], 'eqid', '%s = %s' % (TOPC, TOPC)), xopn], 'dvmptres',
              '( ph -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> ( ( K x. 1 ) + 0 ) ) )' % (X, KH, X))
    kco = w.s([kc], 'adantr', '( %s -> K e. CC )' % AO)
    s1 = w.s([w.s([w.s([kco], 'mulridd', '( %s -> ( K x. 1 ) = K )' % AO)], 'oveq1d', '( %s -> ( ( K x. 1 ) + 0 ) = ( K + 0 ) )' % AO), w.s([kco], 'addridd', '( %s -> ( K + 0 ) = K )' % AO)],
             'eqtrd', '( %s -> ( ( K x. 1 ) + 0 ) = K )' % AO)
    dvo2 = w.s([dvo, w.s([s1], 'mpteq2dva', '( ph -> ( t e. %s |-> ( ( K x. 1 ) + 0 ) ) = ( t e. %s |-> K ) )' % (X, X))], 'eqtrd', '( ph -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> K ) )' % (X, KH, X))
    # the chain rule and the division by K
    co = w.s([sr, sr, khrpo, kco, 'h3', bcc, dvo2, 'h4', 'h6', 'h7'], 'dvmptco', '( ph -> ( RR _D ( t e. %s |-> C ) ) = ( t e. %s |-> ( E x. K ) ) )' % (X, X))
    ekc = D(w, AO, 'mulcld', [ecco, kco], '( E x. K ) e. CC')
    dq = w.s([sr, ccco, ekc, co, kc, kne], 'dvmptdivc', '( ph -> ( RR _D ( t e. %s |-> ( C / K ) ) ) = ( t e. %s |-> ( ( E x. K ) / K ) ) )' % (X, X))
    s2 = w.s([ecco, kco, w.s([kne], 'adantr', '( %s -> K =/= 0 )' % AO)], 'divcan4d', '( %s -> ( ( E x. K ) / K ) = E )' % AO)
    dq2 = w.s([dq, w.s([s2], 'mpteq2dva', '( ph -> ( t e. %s |-> ( ( E x. K ) / K ) ) = ( t e. %s |-> E ) )' % (X, X))], 'eqtrd', '( ph -> ( RR _D ( t e. %s |-> ( C / K ) ) ) = ( t e. %s |-> E ) )' % (X, X))
    # ef1ftc
    e5 = w.s(['h8'], 'oveq1d', '( t = P -> ( C / K ) = ( R / K ) )')
    e6 = w.s(['h9'], 'oveq1d', '( t = Q -> ( C / K ) = ( S / K ) )')
    ftc = w.s([c2, gcn, dq2, ecn, e5, e6], 'ef1ftc', '( ph -> ( ( t e. %s |-> E ) e. L^1 /\\ S. %s E _d t = ( ( S / K ) - ( R / K ) ) ) )' % (X, X))
    ralc = w.s([ccc], 'ralrimiva', '( ph -> A. t e. %s C e. CC )' % XC)
    axr = D(w, ph, 'rexrd', [pr], 'P e. RR*'); bxr = D(w, ph, 'rexrd', [qr], 'Q e. RR*')
    qin = w.s([axr, bxr, le, w.inst('ubicc2')], 'syl3anc', '( ph -> Q e. %s )' % XC)
    pin = w.s([axr, bxr, le, w.inst('lbicc2')], 'syl3anc', '( ph -> P e. %s )' % XC)
    scc = w.s([w.s(['h9'], 'eleq1d', '( t = Q -> ( C e. CC <-> S e. CC ) )'), ralc, qin], 'rspcdva', '( ph -> S e. CC )')
    rcc = w.s([w.s(['h8'], 'eleq1d', '( t = P -> ( C e. CC <-> R e. CC ) )'), ralc, pin], 'rspcdva', '( ph -> R e. CC )')
    dsd = w.s([scc, rcc, kc, kne], 'divsubdird', '( ph -> ( ( S - R ) / K ) = ( ( S / K ) - ( R / K ) ) )')
    ib = w.s([ftc], 'simpld', '( ph -> ( t e. %s |-> E ) e. L^1 )' % X)
    iv = w.s([w.s([ftc], 'simprd', '( ph -> S. %s E _d t = ( ( S / K ) - ( R / K ) ) )' % X), dsd], 'eqtr4d', '( ph -> S. %s E _d t = ( ( S - R ) / K ) )' % X)
    w.qed([ib, iv], 'jca', STATEMENTS['ef1faf'])
    go(w, only)


def affctx(w, A0):
    """facts under A0 = ( ( K e. RR /\\ K =/= 0 /\\ H e. RR ) /\\ ( ( P e. RR /\\ Q e. RR /\\ P <_ Q ) /\\ POS ) )"""
    d = {}
    d['c1'] = D(w, A0, 'simpl', [], '( K e. RR /\\ K =/= 0 /\\ H e. RR )')
    d['c2'] = D(w, A0, 'simprl', [], '( P e. RR /\\ Q e. RR /\\ P <_ Q )')
    posu = D(w, A0, 'simprr', [], 'A. u e. %s 0 < ( ( K x. u ) + H )' % XC)
    cb = w.s([w.s([w.s([], 'oveq2', '( u = t -> ( K x. u ) = ( K x. t ) )')], 'oveq1d', '( u = t -> ( ( K x. u ) + H ) = ( ( K x. t ) + H ) )')], 'breq2d',
             '( u = t -> ( 0 < ( ( K x. u ) + H ) <-> 0 < ( ( K x. t ) + H ) ) )')
    d['pos'] = w.s([posu, w.s([w.s([cb], 'cbvralvw', '( A. u e. %s 0 < ( ( K x. u ) + H ) <-> A. t e. %s 0 < ( ( K x. t ) + H ) )' % (XC, XC))], 'a1i',
                          '( %s -> ( A. u e. %s 0 < ( ( K x. u ) + H ) <-> A. t e. %s 0 < ( ( K x. t ) + H ) ) )' % (A0, XC, XC))], 'mpbid', '( %s -> A. t e. %s 0 < ( ( K x. t ) + H ) )' % (A0, XC))
    d['h1'] = D(w, A0, 'jca', [d['c1'], d['c2']], '( ( K e. RR /\\ K =/= 0 /\\ H e. RR ) /\\ ( P e. RR /\\ Q e. RR /\\ P <_ Q ) )')
    return d


def tsub(w, P, body):
    """( t = P -> body(t) = body(P) ) for body = f ( ( K x. t ) + H )"""
    a = w.s([], 'oveq2', '( t = %s -> ( K x. t ) = ( K x. %s ) )' % (P, P))
    b = w.s([a], 'oveq1d', '( t = %s -> ( ( K x. t ) + H ) = ( ( K x. %s ) + H ) )' % (P, P))
    return b


# ---------------------------------------------------------------- ef1ilaf: S. 1 / ( K t + H )
if __name__ == '__main__' and (not only or 'ef1ilaf' in only):
    w = W('ef1ilaf', 'The integral of ` 1 / ( K t + H ) ` on an interval where ` K t + H > 0 ` : '
          '` ( log ( K Q + H ) - log ( K P + H ) ) / K ` ( ~ ef1faf with ~ dvrelog ; the two pieces of Lean '
          '` integral_one_div_one_add_abs ` ).')
    A0 = STATEMENTS['ef1ilaf'].split(' -> ( ( t e.')[0][2:]
    d = affctx(w, A0)
    LR = '( log |` RR+ )'; LM = '( y e. RR+ |-> ( log ` y ) )'; RM = '( y e. RR+ |-> ( 1 / y ) )'
    lf = w.s([a1(w, A0, 'relogf1o', '%s : RR+ -1-1-onto-> RR' % LR), w.inst('f1of')], 'syl', '( %s -> %s : RR+ --> RR )' % (A0, LR))
    lfe = w.s([lf], 'feqmptd', '( %s -> %s = ( y e. RR+ |-> ( %s ` y ) ) )' % (A0, LR, LR))
    AY = '( %s /\\ y e. RR+ )' % A0
    yrp = w.s([], 'simpr', '( %s -> y e. RR+ )' % AY)
    fvr = w.s([yrp, w.inst('fvres')], 'syl', '( %s -> ( %s ` y ) = ( log ` y ) )' % (AY, LR))
    lfe2 = w.s([lfe, w.s([fvr], 'mpteq2dva', '( %s -> ( y e. RR+ |-> ( %s ` y ) ) = %s )' % (A0, LR, LM))], 'eqtrd', '( %s -> %s = %s )' % (A0, LR, LM))
    dvl = a1(w, A0, 'dvrelog', '( RR _D %s ) = ( x e. RR+ |-> ( 1 / x ) )' % LR)
    cbv = w.s([w.s([], 'oveq2', '( x = y -> ( 1 / x ) = ( 1 / y ) )')], 'cbvmptv', '( x e. RR+ |-> ( 1 / x ) ) = %s' % RM)
    dvl2 = w.s([w.s([w.s([lfe2], 'eqcomd', '( %s -> %s = %s )' % (A0, LM, LR))], 'oveq2d', '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0, LM, LR)),
                w.s([dvl, w.s([cbv], 'a1i', '( %s -> ( x e. RR+ |-> ( 1 / x ) ) = %s )' % (A0, RM))], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, LR, RM))], 'eqtrd',
               '( %s -> ( RR _D %s ) = %s )' % (A0, LM, RM))
    lyc = w.s([w.s([yrp, w.inst('relogcl')], 'syl', '( %s -> ( log ` y ) e. RR )' % AY)], 'recnd', '( %s -> ( log ` y ) e. CC )' % AY)
    # 1 / y is continuous on RR+
    rpcc = w.s([a1(w, A0, 'rpssre', 'RR+ C_ RR'), a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> RR+ C_ CC )' % A0)
    onec = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), rpcc, a1(w, A0, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( %s -> ( y e. RR+ |-> 1 ) e. ( RR+ -cn-> CC ) )' % A0)
    rpn0 = w.s([], 'rpcndif0', '( y e. RR+ -> y e. ( CC \\ { 0 } ) )')
    rpss = w.s([w.s([rpn0], 'ssriv', 'RR+ C_ ( CC \\ { 0 } )')], 'a1i', '( %s -> RR+ C_ ( CC \\ { 0 } ) )' % A0)
    idn = w.s([rpss, a1(w, A0, 'difss', '( CC \\ { 0 } ) C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( %s -> ( y e. RR+ |-> y ) e. ( RR+ -cn-> ( CC \\ { 0 } ) ) )' % A0)
    rcn = w.s([onec, idn], 'divcncf', '( %s -> %s e. ( RR+ -cn-> CC ) )' % (A0, RM))
    KH = '( ( K x. t ) + H )'
    s6 = w.s([], 'fveq2', '( y = %s -> ( log ` y ) = ( log ` %s ) )' % (KH, KH))
    s7 = w.s([], 'oveq2', '( y = %s -> ( 1 / y ) = ( 1 / %s ) )' % (KH, KH))
    s8 = w.s([tsub(w, 'P', None)], 'fveq2d', '( t = P -> ( log ` %s ) = ( log ` ( ( K x. P ) + H ) ) )' % KH)
    s9 = w.s([tsub(w, 'Q', None)], 'fveq2d', '( t = Q -> ( log ` %s ) = ( log ` ( ( K x. Q ) + H ) ) )' % KH)
    w.qed([d['h1'], d['pos'], lyc, dvl2, rcn, s6, s7, s8, s9], 'ef1faf', STATEMENTS['ef1ilaf'])
    go(w, only)

# ---------------------------------------------------------------- ef1ipaf: S. ( K t + H ) ^ -1/2
if __name__ == '__main__' and (not only or 'ef1ipaf' in only):
    w = W('ef1ipaf', 'The integral of ` ( K t + H ) ^ ( -1 / 2 ) ` on an interval where ` K t + H > 0 ` : '
          '` ( 2 ( K Q + H ) ^ ( 1 / 2 ) - 2 ( K P + H ) ^ ( 1 / 2 ) ) / K ` ( ~ ef1faf with ~ dvcxp1 ; Lean '
          '` integral_rpow ` in ` integral_abs_sub_rpow_le ` ).')
    A0 = STATEMENTS['ef1ipaf'].split(' -> ( ( t e.')[0][2:]
    d = affctx(w, A0)
    HF = '( 1 / 2 )'; NH = '-u ( 1 / 2 )'
    AM = '( y e. RR+ |-> ( 2 x. ( y ^c %s ) ) )' % HF
    BM = '( y e. RR+ |-> ( y ^c %s ) )' % NH
    AY = '( %s /\\ y e. RR+ )' % A0
    yrp = w.s([], 'simpr', '( %s -> y e. RR+ )' % AY)
    yc = D(w, AY, 'rpcnd', [yrp], 'y e. CC')
    hc = a1(w, A0, 'halfcn', '%s e. CC' % HF)
    hcy = a1(w, AY, 'halfcn', '%s e. CC' % HF)
    sr = a1(w, A0, 'reelprrecn', 'RR e. { RR , CC }')
    ypc = D(w, AY, 'cxpcld', [yc, hcy], '( y ^c %s ) e. CC' % HF)
    HM1 = '( %s - 1 )' % HF
    hm1c = D(w, AY, 'subcld', [hcy, a1(w, AY, 'ax-1cn', '1 e. CC')], '%s e. CC' % HM1)
    dpc = D(w, AY, 'mulcld', [hcy, D(w, AY, 'cxpcld', [yc, hm1c], '( y ^c %s ) e. CC' % HM1)], '( %s x. ( y ^c %s ) ) e. CC' % (HF, HM1))
    dvc = w.s([hc, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D ( y e. RR+ |-> ( y ^c %s ) ) ) = ( y e. RR+ |-> ( %s x. ( y ^c %s ) ) ) )' % (A0, HF, HF, HM1))
    dv2 = w.s([sr, ypc, dpc, dvc, a1(w, A0, '2cn', '2 e. CC')], 'dvmptcmul',
              '( %s -> ( RR _D %s ) = ( y e. RR+ |-> ( 2 x. ( %s x. ( y ^c %s ) ) ) ) )' % (A0, AM, HF, HM1))
    # 2 x. ( 1/2 x. y ^ ( 1/2 - 1 ) ) = y ^ -1/2
    # ( 1 / 2 ) - 1 = -u ( 1 / 2 ): 1 = ( 1 / 2 ) + ( 1 / 2 )
    h2 = w.s([], '1mhlfehlf', '( 1 - ( 1 / 2 ) ) = ( 1 / 2 )')
    h3 = w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], 'halfcn', '%s e. CC' % HF)], 'negsubdi2i', '-u ( 1 - %s ) = ( %s - 1 )' % (HF, HF))
    h4 = w.s([h2], 'negeqi', '-u ( 1 - %s ) = %s' % (HF, NH))
    h5 = w.s([h3, h4], 'eqtr3i', '%s = %s' % (HM1, NH))
    m2 = w.s([w.s([], 'ax-1cn', '1 e. CC'), w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0')], 'divcan2i', '( 2 x. ( 1 / 2 ) ) = 1')
    c1 = w.s([w.s([h5], 'oveq2i', '( y ^c %s ) = ( y ^c %s )' % (HM1, NH))], 'a1i', '( %s -> ( y ^c %s ) = ( y ^c %s ) )' % (AY, HM1, NH))
    ync = D(w, AY, 'cxpcld', [yc, D(w, AY, 'negcld', [hcy], '%s e. CC' % NH)], '( y ^c %s ) e. CC' % NH)
    c2 = w.s([a1(w, AY, '2cn', '2 e. CC'), hcy, D(w, AY, 'cxpcld', [yc, hm1c], '( y ^c %s ) e. CC' % HM1)], 'mulassd',
             '( %s -> ( ( 2 x. %s ) x. ( y ^c %s ) ) = ( 2 x. ( %s x. ( y ^c %s ) ) ) )' % (AY, HF, HM1, HF, HM1))
    c3 = w.s([w.s([m2], 'oveq1i', '( ( 2 x. %s ) x. ( y ^c %s ) ) = ( 1 x. ( y ^c %s ) )' % (HF, HM1, HM1))], 'a1i',
             '( %s -> ( ( 2 x. %s ) x. ( y ^c %s ) ) = ( 1 x. ( y ^c %s ) ) )' % (AY, HF, HM1, HM1))
    c4 = D(w, AY, 'mullidd', [D(w, AY, 'cxpcld', [yc, hm1c], '( y ^c %s ) e. CC' % HM1)], '( 1 x. ( y ^c %s ) ) = ( y ^c %s )' % (HM1, HM1))
    cc = chain(w, AY, ['( 2 x. ( %s x. ( y ^c %s ) ) )' % (HF, HM1), '( ( 2 x. %s ) x. ( y ^c %s ) )' % (HF, HM1), '( 1 x. ( y ^c %s ) )' % HM1,
                       '( y ^c %s )' % HM1, '( y ^c %s )' % NH], [('r', c2), c3, c4, c1])
    dv3 = w.s([dv2, w.s([cc], 'mpteq2dva', '( %s -> ( y e. RR+ |-> ( 2 x. ( %s x. ( y ^c %s ) ) ) ) = %s )' % (A0, HF, HM1, BM))], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, AM, BM))
    ac = D(w, AY, 'mulcld', [a1(w, AY, '2cn', '2 e. CC'), ypc], '( 2 x. ( y ^c %s ) ) e. CC' % HF)
    # y ^ -1/2 is continuous on RR+ (it is differentiable there)
    nhc2 = w.s([hc], 'negcld', '( %s -> %s e. CC )' % (A0, NH))
    NM1 = '( %s - 1 )' % NH
    dvb = w.s([nhc2, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D %s ) = ( y e. RR+ |-> ( %s x. ( y ^c %s ) ) ) )' % (A0, BM, NH, NM1))
    nm1c = D(w, AY, 'subcld', [D(w, AY, 'negcld', [hcy], '%s e. CC' % NH), a1(w, AY, 'ax-1cn', '1 e. CC')], '%s e. CC' % NM1)
    dbv = D(w, AY, 'mulcld', [D(w, AY, 'negcld', [hcy], '%s e. CC' % NH), D(w, AY, 'cxpcld', [yc, nm1c], '( y ^c %s ) e. CC' % NM1)], '( %s x. ( y ^c %s ) ) e. CC' % (NH, NM1))
    ralv = w.s([dbv], 'ralrimiva', '( %s -> A. y e. RR+ ( %s x. ( y ^c %s ) ) e. CC )' % (A0, NH, NM1))
    dmb = w.s([w.s([dvb], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom ( y e. RR+ |-> ( %s x. ( y ^c %s ) ) ) )' % (A0, BM, NH, NM1)),
               w.s([ralv, w.inst('dmmptg')], 'syl', '( %s -> dom ( y e. RR+ |-> ( %s x. ( y ^c %s ) ) ) = RR+ )' % (A0, NH, NM1))], 'eqtrd', '( %s -> dom ( RR _D %s ) = RR+ )' % (A0, BM))
    fbm = w.s([ync, w.s([], 'eqid', '%s = %s' % (BM, BM))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, BM))
    bcn = w.s([w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), fbm, a1(w, A0, 'rpssre', 'RR+ C_ RR')], '3jca', '( %s -> ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) )' % (A0, BM)), dmb, w.inst('dvcn')],
              'syl2anc', '( %s -> %s e. ( RR+ -cn-> CC ) )' % (A0, BM))
    KH = '( ( K x. t ) + H )'
    s6 = w.s([w.s([], 'oveq1', '( y = %s -> ( y ^c %s ) = ( %s ^c %s ) )' % (KH, HF, KH, HF))], 'oveq2d', '( y = %s -> ( 2 x. ( y ^c %s ) ) = ( 2 x. ( %s ^c %s ) ) )' % (KH, HF, KH, HF))
    s7 = w.s([], 'oveq1', '( y = %s -> ( y ^c %s ) = ( %s ^c %s ) )' % (KH, NH, KH, NH))
    KP = '( ( K x. P ) + H )'; KQ = '( ( K x. Q ) + H )'
    s8 = w.s([w.s([tsub(w, 'P', None)], 'oveq1d', '( t = P -> ( %s ^c %s ) = ( %s ^c %s ) )' % (KH, HF, KP, HF))], 'oveq2d', '( t = P -> ( 2 x. ( %s ^c %s ) ) = ( 2 x. ( %s ^c %s ) ) )' % (KH, HF, KP, HF))
    s9 = w.s([w.s([tsub(w, 'Q', None)], 'oveq1d', '( t = Q -> ( %s ^c %s ) = ( %s ^c %s ) )' % (KH, HF, KQ, HF))], 'oveq2d', '( t = Q -> ( 2 x. ( %s ^c %s ) ) = ( 2 x. ( %s ^c %s ) ) )' % (KH, HF, KQ, HF))
    w.qed([d['h1'], d['pos'], ac, dv3, bcn, s6, s7, s8, s9], 'ef1faf', STATEMENTS['ef1ipaf'])
    go(w, only)

ABT = '( 1 / ( 1 + ( abs ` t ) ) )'

# ---------------------------------------------------------------- ef1iac: 1 / ( 1 + | t | ) is integrable on every interval
if __name__ == '__main__' and (not only or 'ef1iac' in only):
    w = W('ef1iac', '` 1 / ( 1 + | t | ) ` is integrable on every bounded interval ( Lean ` continuous_one_div_one_add_abs ` '
          'with ` Continuous.intervalIntegrable ` ; ~ cniccibl ).')
    A0 = '( U e. RR /\\ V e. RR )'
    ur = D(w, A0, 'simpl', [], 'U e. RR'); vr = D(w, A0, 'simpr', [], 'V e. RR')
    XV = '( U [,] V )'; XO = '( U (,) V )'
    ssr = w.s([ur, vr, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, XV))
    usscn = w.s([ssr, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, XV))
    sscc = a1(w, A0, 'ssid', 'CC C_ CC')
    idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( t e. %s |-> t ) e. ( %s -cn-> CC ) )' % (A0, XV, XV))
    ssi = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an', '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
    absc = w.s([ssi, w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'sselii', 'abs e. ( CC -cn-> CC )')
    abm = w.s([w.s([absc], 'a1i', '( %s -> abs e. ( CC -cn-> CC ) )' % A0), idc], 'cncfmpt1f', '( %s -> ( t e. %s |-> ( abs ` t ) ) e. ( %s -cn-> CC ) )' % (A0, XV, XV))
    onec = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> 1 ) e. ( %s -cn-> CC ) )' % (A0, XV, XV))
    den = w.s([onec, abm], 'addcncf', '( %s -> ( t e. %s |-> ( 1 + ( abs ` t ) ) ) e. ( %s -cn-> CC ) )' % (A0, XV, XV))
    AT = '( %s /\\ t e. %s )' % (A0, XV)
    tr = w.s([w.s([ssr], 'adantr', '( %s -> %s C_ RR )' % (AT, XV)), w.s([], 'simpr', '( %s -> t e. %s )' % (AT, XV))], 'sseldd', '( %s -> t e. RR )' % AT)
    at = D(w, AT, 'recnd', [tr], 't e. CC')
    abr = D(w, AT, 'abscld', [at], '( abs ` t ) e. RR')
    ab0 = D(w, AT, 'absge0d', [at], '0 <_ ( abs ` t )')
    cl = Closure(w, AT, {'( abs ` t )': ('RR', abr)})
    dpos = linarith(w, AT, [ab0], '0 < ( 1 + ( abs ` t ) )', closure=cl)
    drp = D(w, AT, 'elrpd', [cl.mem('( 1 + ( abs ` t ) )', 'RR'), dpos], '( 1 + ( abs ` t ) ) e. RR+')
    dn0 = w.s([drp, w.inst('rpcndif0')], 'syl', '( %s -> ( 1 + ( abs ` t ) ) e. ( CC \\ { 0 } ) )' % AT)
    DM = '( t e. %s |-> ( 1 + ( abs ` t ) ) )' % XV
    fd = w.s([dn0, w.s([], 'eqid', '%s = %s' % (DM, DM))], 'fmptd', '( %s -> %s : %s --> ( CC \\ { 0 } ) )' % (A0, DM, XV))
    dnc = w.s([fd, w.s([a1(w, A0, 'difss', '( CC \\ { 0 } ) C_ CC'), den, w.inst('cncfcdm')], 'syl2anc',
                       '( %s -> ( %s e. ( %s -cn-> ( CC \\ { 0 } ) ) <-> %s : %s --> ( CC \\ { 0 } ) ) )' % (A0, DM, XV, DM, XV))], 'mpbird',
              '( %s -> %s e. ( %s -cn-> ( CC \\ { 0 } ) ) )' % (A0, DM, XV))
    fcn = w.s([onec, dnc], 'divcncf', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XV, ABT, XV))
    ibc = w.s([ur, vr, fcn, w.inst('cniccibl')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, XV, ABT))
    fv = D(w, AT, 'rpreccld', [drp], '%s e. RR+' % ABT)
    w.qed([a1(w, A0, 'ioossicc', '%s C_ %s' % (XO, XV)), a1(w, A0, 'ioombl', '%s e. dom vol' % XO), fv, ibc], 'iblss', STATEMENTS['ef1iac'])
    go(w, only)



def ilaf_piece(w, A0, P, Q, K, lep, posfact):
    """apply ef1ilaf at slope K, H = 1 on ( P , Q ): returns the ( L^1 /\\ value ) step.
    lep: ( A0 -> P <_ Q ); posfact(AU): step ( AU -> 0 < ( ( K x. u ) + 1 ) ) for AU = ( A0 /\\ u e. ( P [,] Q ) )"""
    kr = a1(w, A0, 'neg1rr' if K == '-u 1' else '1re', '%s e. RR' % K)
    kne = a1(w, A0, 'neg1ne0' if K == '-u 1' else 'ax-1ne0', '%s =/= 0' % K)
    k3 = D(w, A0, '3jca', [kr, kne, a1(w, A0, '1re', '1 e. RR')], '( %s e. RR /\\ %s =/= 0 /\\ 1 e. RR )' % (K, K))
    pq = D(w, A0, '3jca', [PR[P], PR[Q], lep], '( %s e. RR /\\ %s e. RR /\\ %s <_ %s )' % (P, Q, P, Q))
    AU = '( %s /\\ u e. ( %s [,] %s ) )' % (A0, P, Q)
    pos = w.s([posfact(AU)], 'ralrimiva', '( %s -> A. u e. ( %s [,] %s ) 0 < ( ( %s x. u ) + 1 ) )' % (A0, P, Q, K))
    hyp = D(w, A0, 'jca', [k3, D(w, A0, 'jca', [pq, pos], '( ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) /\\ A. u e. ( %s [,] %s ) 0 < ( ( %s x. u ) + 1 ) )' % (P, Q, P, Q, P, Q, K))],
            '( ( %s e. RR /\\ %s =/= 0 /\\ 1 e. RR ) /\\ ( ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) /\\ A. u e. ( %s [,] %s ) 0 < ( ( %s x. u ) + 1 ) ) )' % (K, K, P, Q, P, Q, P, Q, K))
    KT = '( ( %s x. t ) + 1 )' % K
    concl = ('( ( t e. ( %s (,) %s ) |-> ( 1 / %s ) ) e. L^1 /\\ S. ( %s (,) %s ) ( 1 / %s ) _d t = ( ( ( log ` ( ( %s x. %s ) + 1 ) ) - ( log ` ( ( %s x. %s ) + 1 ) ) ) / %s ) )'
             % (P, Q, KT, P, Q, KT, K, Q, K, P, K))
    return w.s([hyp, w.inst('ef1ilaf')], 'syl', '( %s -> %s )' % (A0, concl))


PR = {}

# ---------------------------------------------------------------- ef1ia: S. ( U , V ) 1 / ( 1 + | t | ) = log ( 1 - U ) + log ( 1 + V )
if __name__ == '__main__' and (not only or 'ef1ia' in only):
    w = W('ef1ia', '` S. ( U , V ) 1 / ( 1 + | t | ) = log ( 1 - U ) + log ( 1 + V ) ` for ` U <_ 0 <_ V ` '
          '( Lean ` integral_one_div_one_add_abs ` ; ~ ef1ilaf on each side of ` 0 ` ).')
    A0 = '( ( U e. RR /\\ U <_ 0 ) /\\ ( V e. RR /\\ 0 <_ V ) )'
    ur = D(w, A0, 'simpll', [], 'U e. RR'); u0 = D(w, A0, 'simplr', [], 'U <_ 0')
    vr = D(w, A0, 'simprl', [], 'V e. RR'); v0 = D(w, A0, 'simprr', [], '0 <_ V')
    zr = a1(w, A0, '0re', '0 e. RR')
    PR.update({'U': ur, 'V': vr, '0': zr})

    def posL(AU):
        uin = w.s([], 'simpr', '( %s -> u e. ( U [,] 0 ) )' % AU)
        el = w.s([w.s([w.s([ur], 'adantr', '( %s -> U e. RR )' % AU), a1(w, AU, '0re', '0 e. RR'), w.inst('elicc2')], 'syl2anc',
                      '( %s -> ( u e. ( U [,] 0 ) <-> ( u e. RR /\\ U <_ u /\\ u <_ 0 ) ) )' % AU), uin], 'mpbid',
                '( %s -> ( u e. RR /\\ U <_ u /\\ u <_ 0 ) )' % AU)
        urr = D(w, AU, 'simp1d', [el], 'u e. RR'); ule = D(w, AU, 'simp3d', [el], 'u <_ 0')
        return linarith(w, AU, [ule], '0 < ( ( -u 1 x. u ) + 1 )', closure=Closure(w, AU, {'u': ('RR', urr)}))

    def posR(AU):
        uin = w.s([], 'simpr', '( %s -> u e. ( 0 [,] V ) )' % AU)
        el = w.s([w.s([a1(w, AU, '0re', '0 e. RR'), w.s([vr], 'adantr', '( %s -> V e. RR )' % AU), w.inst('elicc2')], 'syl2anc',
                      '( %s -> ( u e. ( 0 [,] V ) <-> ( u e. RR /\\ 0 <_ u /\\ u <_ V ) ) )' % AU), uin], 'mpbid', '( %s -> ( u e. RR /\\ 0 <_ u /\\ u <_ V ) )' % AU)
        urr = D(w, AU, 'simp1d', [el], 'u e. RR'); uge = D(w, AU, 'simp2d', [el], '0 <_ u')
        return linarith(w, AU, [uge], '0 < ( ( 1 x. u ) + 1 )', closure=Closure(w, AU, {'u': ('RR', urr)}))

    pl = ilaf_piece(w, A0, 'U', '0', '-u 1', u0, posL)
    pr_ = ilaf_piece(w, A0, '0', 'V', '1', v0, posR)
    # the integrands agree with 1 / ( 1 + | t | )
    ATL = '( %s /\\ t e. ( U (,) 0 ) )' % A0
    tl = w.s([w.s([], 'simpr', '( %s -> t e. ( U (,) 0 ) )' % ATL), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % ATL)
    ioo = w.s([w.s([w.s([ur], 'rexrd', '( %s -> U e. RR* )' % A0), w.s([zr], 'rexrd', '( %s -> 0 e. RR* )' % A0), w.inst('elioo2')], 'syl2anc',
                   '( %s -> ( t e. ( U (,) 0 ) <-> ( t e. RR /\\ U < t /\\ t < 0 ) ) )' % A0)], 'biimpa', '( %s -> ( t e. RR /\\ U < t /\\ t < 0 ) )' % ATL)
    tneg = D(w, ATL, 'simp3d', [ioo], 't < 0')
    cll = Closure(w, ATL, {'t': ('RR', tl)})
    tle = D(w, ATL, 'ltled', [tl, a1(w, ATL, '0re', '0 e. RR'), tneg], 't <_ 0')
    abn = w.s([tl, tle, w.inst('absnid')], 'syl2anc', '( %s -> ( abs ` t ) = -u t )' % ATL)
    lin1 = lineq(w, ATL, '( 1 + -u t )', '( ( -u 1 x. t ) + 1 )', closure=cll)
    eqL = w.s([w.s([w.s([abn], 'oveq2d', '( %s -> ( 1 + ( abs ` t ) ) = ( 1 + -u t ) )' % ATL), lin1], 'eqtrd', '( %s -> ( 1 + ( abs ` t ) ) = ( ( -u 1 x. t ) + 1 ) )' % ATL)],
              'oveq2d', '( %s -> %s = ( 1 / ( ( -u 1 x. t ) + 1 ) ) )' % (ATL, ABT))
    ATR = '( %s /\\ t e. ( 0 (,) V ) )' % A0
    tr = w.s([w.s([], 'simpr', '( %s -> t e. ( 0 (,) V ) )' % ATR), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % ATR)
    ioor = w.s([w.s([w.s([zr], 'rexrd', '( %s -> 0 e. RR* )' % A0), w.s([vr], 'rexrd', '( %s -> V e. RR* )' % A0), w.inst('elioo2')], 'syl2anc',
                    '( %s -> ( t e. ( 0 (,) V ) <-> ( t e. RR /\\ 0 < t /\\ t < V ) ) )' % A0)], 'biimpa', '( %s -> ( t e. RR /\\ 0 < t /\\ t < V ) )' % ATR)
    tpos = D(w, ATR, 'simp2d', [ioor], '0 < t')
    tge = D(w, ATR, 'ltled', [a1(w, ATR, '0re', '0 e. RR'), tr, tpos], '0 <_ t')
    abp = w.s([tr, tge, w.inst('absid')], 'syl2anc', '( %s -> ( abs ` t ) = t )' % ATR)
    clr = Closure(w, ATR, {'t': ('RR', tr)})
    lin2 = lineq(w, ATR, '( 1 + t )', '( ( 1 x. t ) + 1 )', closure=clr)
    eqR = w.s([w.s([w.s([abp], 'oveq2d', '( %s -> ( 1 + ( abs ` t ) ) = ( 1 + t ) )' % ATR), lin2], 'eqtrd', '( %s -> ( 1 + ( abs ` t ) ) = ( ( 1 x. t ) + 1 ) )' % ATR)],
              'oveq2d', '( %s -> %s = ( 1 / ( ( 1 x. t ) + 1 ) ) )' % (ATR, ABT))
    KL_ = '( ( -u 1 x. t ) + 1 )'; KR_ = '( ( 1 x. t ) + 1 )'
    iblL = w.s([w.s([eqL], 'mpteq2dva', '( %s -> ( t e. ( U (,) 0 ) |-> %s ) = ( t e. ( U (,) 0 ) |-> ( 1 / %s ) ) )' % (A0, ABT, KL_)), w.s([pl], 'simpld', '( %s -> ( t e. ( U (,) 0 ) |-> ( 1 / %s ) ) e. L^1 )' % (A0, KL_))],
               'eqeltrd', '( %s -> ( t e. ( U (,) 0 ) |-> %s ) e. L^1 )' % (A0, ABT))
    iblR = w.s([w.s([eqR], 'mpteq2dva', '( %s -> ( t e. ( 0 (,) V ) |-> %s ) = ( t e. ( 0 (,) V ) |-> ( 1 / %s ) ) )' % (A0, ABT, KR_)), w.s([pr_], 'simpld', '( %s -> ( t e. ( 0 (,) V ) |-> ( 1 / %s ) ) e. L^1 )' % (A0, KR_))],
               'eqeltrd', '( %s -> ( t e. ( 0 (,) V ) |-> %s ) e. L^1 )' % (A0, ABT))
    itL = w.s([eqL], 'itgeq2dv', '( %s -> S. ( U (,) 0 ) %s _d t = S. ( U (,) 0 ) ( 1 / %s ) _d t )' % (A0, ABT, KL_))
    itR = w.s([eqR], 'itgeq2dv', '( %s -> S. ( 0 (,) V ) %s _d t = S. ( 0 (,) V ) ( 1 / %s ) _d t )' % (A0, ABT, KR_))
    # the split at 0
    ATV = '( %s /\\ t e. ( U (,) V ) )' % A0
    tv = w.s([w.s([], 'simpr', '( %s -> t e. ( U (,) V ) )' % ATV), w.inst('elioore')], 'syl', '( %s -> t e. RR )' % ATV)
    tvc = D(w, ATV, 'recnd', [tv], 't e. CC')
    clv = Closure(w, ATV, {'t': ('RR', tv)})
    dvr = D(w, ATV, 'readdcld', [a1(w, ATV, '1re', '1 e. RR'), D(w, ATV, 'abscld', [tvc], '( abs ` t ) e. RR')], '( 1 + ( abs ` t ) ) e. RR')
    dvp = linarith(w, ATV, [D(w, ATV, 'absge0d', [tvc], '0 <_ ( abs ` t )')], '0 < ( 1 + ( abs ` t ) )', closure=Closure(w, ATV, {'( abs ` t )': ('RR', D(w, ATV, 'abscld', [tvc], '( abs ` t ) e. RR'))}))
    fcc = D(w, ATV, 'rpcnd', [D(w, ATV, 'rpreccld', [D(w, ATV, 'elrpd', [dvr, dvp], '( 1 + ( abs ` t ) ) e. RR+')], '%s e. RR+' % ABT)], '%s e. CC' % ABT)
    zin = w.s([w.s([ur, vr, w.inst('elicc2')], 'syl2anc', '( %s -> ( 0 e. ( U [,] V ) <-> ( 0 e. RR /\\ U <_ 0 /\\ 0 <_ V ) ) )' % A0),
               D(w, A0, '3jca', [zr, u0, v0], '( 0 e. RR /\\ U <_ 0 /\\ 0 <_ V )')], 'mpbird', '( %s -> 0 e. ( U [,] V ) )' % A0)
    spl = w.s([ur, vr, zin, fcc, iblL, iblR], 'itgsplitioo', '( %s -> S. ( U (,) V ) %s _d t = ( S. ( U (,) 0 ) %s _d t + S. ( 0 (,) V ) %s _d t ) )' % (A0, ABT, ABT, ABT))
    # the values
    cl0 = Closure(w, A0, {'U': ('RR', ur), 'V': ('RR', vr)})
    vL = w.s([pl], 'simprd', '( %s -> S. ( U (,) 0 ) ( 1 / %s ) _d t = ( ( ( log ` ( ( -u 1 x. 0 ) + 1 ) ) - ( log ` ( ( -u 1 x. U ) + 1 ) ) ) / -u 1 ) )' % (A0, KL_))
    vR = w.s([pr_], 'simprd', '( %s -> S. ( 0 (,) V ) ( 1 / %s ) _d t = ( ( ( log ` ( ( 1 x. V ) + 1 ) ) - ( log ` ( ( 1 x. 0 ) + 1 ) ) ) / 1 ) )' % (A0, KR_))
    z1 = lineq(w, A0, '( ( -u 1 x. 0 ) + 1 )', '1', closure=cl0)
    z2 = lineq(w, A0, '( ( -u 1 x. U ) + 1 )', '( 1 - U )', closure=cl0)
    z3 = lineq(w, A0, '( ( 1 x. V ) + 1 )', '( 1 + V )', closure=cl0)
    z4 = lineq(w, A0, '( ( 1 x. 0 ) + 1 )', '1', closure=cl0)
    l1 = a1(w, A0, 'log1', '( log ` 1 ) = 0')
    LU = '( log ` ( 1 - U ) )'; LV = '( log ` ( 1 + V ) )'
    nL = w.s([w.s([z1], 'fveq2d', '( %s -> ( log ` ( ( -u 1 x. 0 ) + 1 ) ) = ( log ` 1 ) )' % A0), l1], 'eqtrd', '( %s -> ( log ` ( ( -u 1 x. 0 ) + 1 ) ) = 0 )' % A0)
    nL2 = w.s([nL, w.s([z2], 'fveq2d', '( %s -> ( log ` ( ( -u 1 x. U ) + 1 ) ) = %s )' % (A0, LU))], 'oveq12d',
              '( %s -> ( ( log ` ( ( -u 1 x. 0 ) + 1 ) ) - ( log ` ( ( -u 1 x. U ) + 1 ) ) ) = ( 0 - %s ) )' % (A0, LU))
    nL3 = w.s([nL2, w.s([w.s([], 'df-neg', '-u %s = ( 0 - %s )' % (LU, LU))], 'a1i', '( %s -> -u %s = ( 0 - %s ) )' % (A0, LU, LU))], 'eqtr4d',
              '( %s -> ( ( log ` ( ( -u 1 x. 0 ) + 1 ) ) - ( log ` ( ( -u 1 x. U ) + 1 ) ) ) = -u %s )' % (A0, LU))
    umr = linarith(w, A0, [u0], '0 < ( 1 - U )', closure=cl0)
    lur = D(w, A0, 'relogcld', [D(w, A0, 'elrpd', [cl0.mem('( 1 - U )', 'RR'), umr], '( 1 - U ) e. RR+')], '%s e. RR' % LU)
    luc = D(w, A0, 'recnd', [lur], '%s e. CC' % LU)
    vpr = linarith(w, A0, [v0], '0 < ( 1 + V )', closure=cl0)
    lvr = D(w, A0, 'relogcld', [D(w, A0, 'elrpd', [cl0.mem('( 1 + V )', 'RR'), vpr], '( 1 + V ) e. RR+')], '%s e. RR' % LV)
    lvc = D(w, A0, 'recnd', [lvr], '%s e. CC' % LV)
    c1_ = a1(w, A0, 'ax-1cn', '1 e. CC'); n10 = a1(w, A0, 'ax-1ne0', '1 =/= 0')
    dL = w.s([w.s([nL3], 'oveq1d', '( %s -> ( ( ( log ` ( ( -u 1 x. 0 ) + 1 ) ) - ( log ` ( ( -u 1 x. U ) + 1 ) ) ) / -u 1 ) = ( -u %s / -u 1 ) )' % (A0, LU)),
              w.s([w.s([luc, c1_, n10, w.inst('div2neg')], 'syl3anc', '( %s -> ( -u %s / -u 1 ) = ( %s / 1 ) )' % (A0, LU, LU)), w.s([luc, w.inst('div1')], 'syl', '( %s -> ( %s / 1 ) = %s )' % (A0, LU, LU))],
                  'eqtrd', '( %s -> ( -u %s / -u 1 ) = %s )' % (A0, LU, LU))], 'eqtrd',
             '( %s -> ( ( ( log ` ( ( -u 1 x. 0 ) + 1 ) ) - ( log ` ( ( -u 1 x. U ) + 1 ) ) ) / -u 1 ) = %s )' % (A0, LU))
    nR = w.s([w.s([z4], 'fveq2d', '( %s -> ( log ` ( ( 1 x. 0 ) + 1 ) ) = ( log ` 1 ) )' % A0), l1], 'eqtrd', '( %s -> ( log ` ( ( 1 x. 0 ) + 1 ) ) = 0 )' % A0)
    nR2 = w.s([w.s([z3], 'fveq2d', '( %s -> ( log ` ( ( 1 x. V ) + 1 ) ) = %s )' % (A0, LV)), nR], 'oveq12d',
              '( %s -> ( ( log ` ( ( 1 x. V ) + 1 ) ) - ( log ` ( ( 1 x. 0 ) + 1 ) ) ) = ( %s - 0 ) )' % (A0, LV))
    nR3 = w.s([nR2, w.s([lvc], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A0, LV, LV))], 'eqtrd', '( %s -> ( ( log ` ( ( 1 x. V ) + 1 ) ) - ( log ` ( ( 1 x. 0 ) + 1 ) ) ) = %s )' % (A0, LV))
    dR = w.s([w.s([nR3], 'oveq1d', '( %s -> ( ( ( log ` ( ( 1 x. V ) + 1 ) ) - ( log ` ( ( 1 x. 0 ) + 1 ) ) ) / 1 ) = ( %s / 1 ) )' % (A0, LV)), w.s([lvc, w.inst('div1')], 'syl', '( %s -> ( %s / 1 ) = %s )' % (A0, LV, LV))],
             'eqtrd', '( %s -> ( ( ( log ` ( ( 1 x. V ) + 1 ) ) - ( log ` ( ( 1 x. 0 ) + 1 ) ) ) / 1 ) = %s )' % (A0, LV))
    fL = w.s([w.s([itL, vL], 'eqtrd', '( %s -> S. ( U (,) 0 ) %s _d t = ( ( ( log ` ( ( -u 1 x. 0 ) + 1 ) ) - ( log ` ( ( -u 1 x. U ) + 1 ) ) ) / -u 1 ) )' % (A0, ABT)), dL], 'eqtrd',
             '( %s -> S. ( U (,) 0 ) %s _d t = %s )' % (A0, ABT, LU))
    fR = w.s([w.s([itR, vR], 'eqtrd', '( %s -> S. ( 0 (,) V ) %s _d t = ( ( ( log ` ( ( 1 x. V ) + 1 ) ) - ( log ` ( ( 1 x. 0 ) + 1 ) ) ) / 1 ) )' % (A0, ABT)), dR], 'eqtrd',
             '( %s -> S. ( 0 (,) V ) %s _d t = %s )' % (A0, ABT, LV))
    w.qed([spl, w.s([fL, fR], 'oveq12d', '( %s -> ( S. ( U (,) 0 ) %s _d t + S. ( 0 (,) V ) %s _d t ) = ( %s + %s ) )' % (A0, ABT, ABT, LU, LV))], 'eqtrd', STATEMENTS['ef1ia'])
    go(w, only)

# ---------------------------------------------------------------- ef1ial: the bound form
if __name__ == '__main__' and (not only or 'ef1ial' in only):
    w = W('ef1ial', '` S. ( U , V ) 1 / ( 1 + | t | ) <_ 2 log ( 1 + W ) ` for ` -u W <_ U <_ 0 <_ V <_ W ` '
          '( Lean ` integral_one_div_one_add_abs_le ` ).')
    A0 = STATEMENTS['ef1ial'].split(' -> S.')[0][2:]
    r3 = D(w, A0, 'simpl', [], '( U e. RR /\\ V e. RR /\\ W e. RR )')
    ur = D(w, A0, 'simp1d', [r3], 'U e. RR'); vr = D(w, A0, 'simp2d', [r3], 'V e. RR'); wr = D(w, A0, 'simp3d', [r3], 'W e. RR')
    u0 = D(w, A0, 'simprll', [], 'U <_ 0'); v0 = D(w, A0, 'simprlr', [], '0 <_ V')
    wu = D(w, A0, 'simprrl', [], '-u W <_ U'); vw = D(w, A0, 'simprrr', [], 'V <_ W')
    ia = w.s([D(w, A0, 'jca', [D(w, A0, 'jca', [ur, u0], '( U e. RR /\\ U <_ 0 )'), D(w, A0, 'jca', [vr, v0], '( V e. RR /\\ 0 <_ V )')],
                '( ( U e. RR /\\ U <_ 0 ) /\\ ( V e. RR /\\ 0 <_ V ) )'), w.inst('ef1ia')], 'syl',
             '( %s -> S. ( U (,) V ) %s _d t = ( ( log ` ( 1 - U ) ) + ( log ` ( 1 + V ) ) ) )' % (A0, ABT))
    cl = Closure(w, A0, {'U': ('RR', ur), 'V': ('RR', vr), 'W': ('RR', wr)})
    rp = {}
    for E_, fact in (('( 1 - U )', u0), ('( 1 + V )', v0), ('( 1 + W )', None)):
        pos = linarith(w, A0, [u0, v0, wu, vw] if fact is None else [fact], '0 < %s' % E_, closure=cl)
        rp[E_] = D(w, A0, 'elrpd', [cl.mem(E_, 'RR'), pos], '%s e. RR+' % E_)
    l1 = linarith(w, A0, [wu], '( 1 - U ) <_ ( 1 + W )', closure=cl)
    l2 = linarith(w, A0, [vw], '( 1 + V ) <_ ( 1 + W )', closure=cl)
    g1 = w.s([l1, w.s([rp['( 1 - U )'], rp['( 1 + W )']], 'logled', '( %s -> ( ( 1 - U ) <_ ( 1 + W ) <-> ( log ` ( 1 - U ) ) <_ ( log ` ( 1 + W ) ) ) )' % A0)], 'mpbid',
             '( %s -> ( log ` ( 1 - U ) ) <_ ( log ` ( 1 + W ) ) )' % A0)
    g2 = w.s([l2, w.s([rp['( 1 + V )'], rp['( 1 + W )']], 'logled', '( %s -> ( ( 1 + V ) <_ ( 1 + W ) <-> ( log ` ( 1 + V ) ) <_ ( log ` ( 1 + W ) ) ) )' % A0)], 'mpbid',
             '( %s -> ( log ` ( 1 + V ) ) <_ ( log ` ( 1 + W ) ) )' % A0)
    for E_ in ('( 1 - U )', '( 1 + V )', '( 1 + W )'):
        cl.leaf('( log ` %s )' % E_, 'RR', D(w, A0, 'relogcld', [rp[E_]], '( log ` %s ) e. RR' % E_))
    s = linarith(w, A0, [g1, g2], '( ( log ` ( 1 - U ) ) + ( log ` ( 1 + V ) ) ) <_ ( 2 x. ( log ` ( 1 + W ) ) )', closure=cl)
    w.qed([ia, s], 'eqbrtrd', STATEMENTS['ef1ial'])
    go(w, only)


def nhcn(w, A0):
    """( A0 -> ( y e. RR+ |-> ( y ^c -u ( 1 / 2 ) ) ) e. ( RR+ -cn-> CC ) ), by dvcn on dvcxp1"""
    HF = '( 1 / 2 )'; NH = '-u ( 1 / 2 )'; NM1 = '( %s - 1 )' % NH
    BM = '( y e. RR+ |-> ( y ^c %s ) )' % NH
    AY = '( %s /\\ y e. RR+ )' % A0
    yc = D(w, AY, 'rpcnd', [w.s([], 'simpr', '( %s -> y e. RR+ )' % AY)], 'y e. CC')
    nhy = D(w, AY, 'negcld', [a1(w, AY, 'halfcn', '%s e. CC' % HF)], '%s e. CC' % NH)
    nh0 = w.s([a1(w, A0, 'halfcn', '%s e. CC' % HF)], 'negcld', '( %s -> %s e. CC )' % (A0, NH))
    dvb = w.s([nh0, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D %s ) = ( y e. RR+ |-> ( %s x. ( y ^c %s ) ) ) )' % (A0, BM, NH, NM1))
    nm1c = D(w, AY, 'subcld', [nhy, a1(w, AY, 'ax-1cn', '1 e. CC')], '%s e. CC' % NM1)
    dbv = D(w, AY, 'mulcld', [nhy, D(w, AY, 'cxpcld', [yc, nm1c], '( y ^c %s ) e. CC' % NM1)], '( %s x. ( y ^c %s ) ) e. CC' % (NH, NM1))
    ralv = w.s([dbv], 'ralrimiva', '( %s -> A. y e. RR+ ( %s x. ( y ^c %s ) ) e. CC )' % (A0, NH, NM1))
    dmb = w.s([w.s([dvb], 'dmeqd', '( %s -> dom ( RR _D %s ) = dom ( y e. RR+ |-> ( %s x. ( y ^c %s ) ) ) )' % (A0, BM, NH, NM1)),
               w.s([ralv, w.inst('dmmptg')], 'syl', '( %s -> dom ( y e. RR+ |-> ( %s x. ( y ^c %s ) ) ) = RR+ )' % (A0, NH, NM1))], 'eqtrd', '( %s -> dom ( RR _D %s ) = RR+ )' % (A0, BM))
    fbm = w.s([D(w, AY, 'cxpcld', [yc, nhy], '( y ^c %s ) e. CC' % NH), w.s([], 'eqid', '%s = %s' % (BM, BM))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, BM))
    return w.s([w.s([a1(w, A0, 'ax-resscn', 'RR C_ CC'), fbm, a1(w, A0, 'rpssre', 'RR+ C_ RR')], '3jca', '( %s -> ( RR C_ CC /\\ %s : RR+ --> CC /\\ RR+ C_ RR ) )' % (A0, BM)), dmb, w.inst('dvcn')],
               'syl2anc', '( %s -> %s e. ( RR+ -cn-> CC ) )' % (A0, BM))


# ---------------------------------------------------------------- ef1ir: the regularised singular integral
if __name__ == '__main__' and (not only or 'ef1ir' in only):
    w = W('ef1ir', 'The regularised form of Lean ` integral_abs_sub_rpow_le ` : for ` E > 0 ` , '
          '` S. ( P , Q ) ( | t - B | + E ) ^ ( -1 / 2 ) _d t <_ 4 ( D + E ) ^ ( 1 / 2 ) ` when ` Q - B <_ D ` and '
          '` B - P <_ D ` .  The integrand is bounded and continuous (set.mm has no singular integral; EF1-blueprint '
          'deviation 1): extend to ` ( B - D , B + D ) ` and integrate each side of ` B ` by ~ ef1ipaf .')
    A0 = STATEMENTS['ef1ir'].split(' -> ( ( t e.')[0][2:]
    HF = '( 1 / 2 )'; NH = '-u ( 1 / 2 )'
    RGt = '( ( ( abs ` ( t - B ) ) + E ) ^c %s )' % NH
    br = D(w, A0, 'simpll', [], 'B e. RR'); erp = D(w, A0, 'simplr', [], 'E e. RR+')
    c3 = D(w, A0, 'simprl', [], '( P e. RR /\\ Q e. RR /\\ P <_ Q )')
    c4 = D(w, A0, 'simprr', [], '( D e. RR /\\ ( Q - B ) <_ D /\\ ( B - P ) <_ D )')
    pr = D(w, A0, 'simp1d', [c3], 'P e. RR'); qr = D(w, A0, 'simp2d', [c3], 'Q e. RR'); pq = D(w, A0, 'simp3d', [c3], 'P <_ Q')
    dr = D(w, A0, 'simp1d', [c4], 'D e. RR'); qb = D(w, A0, 'simp2d', [c4], '( Q - B ) <_ D'); bp = D(w, A0, 'simp3d', [c4], '( B - P ) <_ D')
    er = D(w, A0, 'rpred', [erp], 'E e. RR'); e0 = D(w, A0, 'rpgt0d', [erp], '0 < E')
    cl = Closure(w, A0, {'B': ('RR', br), 'E': ('RR+', erp), 'P': ('RR', pr), 'Q': ('RR', qr), 'D': ('RR', dr)})
    d0 = linarith(w, A0, [qb, bp, pq], '0 <_ D', closure=cl)
    LO = '( B - D )'; HI = '( B + D )'
    lor = cl.mem(LO, 'RR'); hir = cl.mem(HI, 'RR')
    lob = linarith(w, A0, [d0], '%s <_ B' % LO, closure=cl); bhi = linarith(w, A0, [d0], 'B <_ %s' % HI, closure=cl)
    lop = linarith(w, A0, [bp], '%s <_ P' % LO, closure=cl); qhi = linarith(w, A0, [qb], 'Q <_ %s' % HI, closure=cl)
    XLH = '( %s [,] %s )' % (LO, HI); OLH = '( %s (,) %s )' % (LO, HI); OPQ = '( P (,) Q )'
    # RG is continuous on [ LO , HI ]
    ssr = w.s([lor, hir, w.inst('iccssre')], 'syl2anc', '( %s -> %s C_ RR )' % (A0, XLH))
    usscn = w.s([ssr, a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> %s C_ CC )' % (A0, XLH))
    sscc = a1(w, A0, 'ssid', 'CC C_ CC')
    idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( t e. %s |-> t ) e. ( %s -cn-> CC ) )' % (A0, XLH, XLH))
    bcn = w.s([D(w, A0, 'recnd', [br], 'B e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> B ) e. ( %s -cn-> CC ) )' % (A0, XLH, XLH))
    ecn = w.s([D(w, A0, 'recnd', [er], 'E e. CC'), usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> E ) e. ( %s -cn-> CC ) )' % (A0, XLH, XLH))
    tbc = w.s([idc, bcn], 'subcncf', '( %s -> ( t e. %s |-> ( t - B ) ) e. ( %s -cn-> CC ) )' % (A0, XLH, XLH))
    ssi = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an', '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
    absc = w.s([ssi, w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'sselii', 'abs e. ( CC -cn-> CC )')
    abm = w.s([w.s([absc], 'a1i', '( %s -> abs e. ( CC -cn-> CC ) )' % A0), tbc], 'cncfmpt1f', '( %s -> ( t e. %s |-> ( abs ` ( t - B ) ) ) e. ( %s -cn-> CC ) )' % (A0, XLH, XLH))
    INN = '( ( abs ` ( t - B ) ) + E )'
    inc = w.s([abm, ecn], 'addcncf', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XLH, INN, XLH))
    AT = '( %s /\\ t e. %s )' % (A0, XLH)
    tr = w.s([w.s([ssr], 'adantr', '( %s -> %s C_ RR )' % (AT, XLH)), w.s([], 'simpr', '( %s -> t e. %s )' % (AT, XLH))], 'sseldd', '( %s -> t e. RR )' % AT)
    tbr = D(w, AT, 'resubcld', [tr, w.s([br], 'adantr', '( %s -> B e. RR )' % AT)], '( t - B ) e. RR')
    atb = D(w, AT, 'recnd', [tbr], '( t - B ) e. CC')
    clt = Closure(w, AT, {'( abs ` ( t - B ) )': ('RR', D(w, AT, 'abscld', [atb], '( abs ` ( t - B ) ) e. RR')), 'E': ('RR+', w.s([erp], 'adantr', '( %s -> E e. RR+ )' % AT))})
    inp = linarith(w, AT, [D(w, AT, 'absge0d', [atb], '0 <_ ( abs ` ( t - B ) )'), w.s([e0], 'adantr', '( %s -> 0 < E )' % AT)], '0 < %s' % INN, closure=clt)
    inrp = D(w, AT, 'elrpd', [clt.mem(INN, 'RR'), inp], '%s e. RR+' % INN)
    INM = '( t e. %s |-> %s )' % (XLH, INN)
    rpcc = w.s([a1(w, A0, 'rpssre', 'RR+ C_ RR'), a1(w, A0, 'ax-resscn', 'RR C_ CC')], 'sstrd', '( %s -> RR+ C_ CC )' % A0)
    inrpc = w.s([w.s([inrp, w.s([], 'eqid', '%s = %s' % (INM, INM))], 'fmptd', '( %s -> %s : %s --> RR+ )' % (A0, INM, XLH)),
                 w.s([rpcc, inc, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( %s e. ( %s -cn-> RR+ ) <-> %s : %s --> RR+ ) )' % (A0, INM, XLH, INM, XLH))], 'mpbird',
                '( %s -> %s e. ( %s -cn-> RR+ ) )' % (A0, INM, XLH))
    rgc = w.s([w.s([], 'nfv', 'F/ t %s' % A0), inrpc, nhcn(w, A0), a1(w, A0, 'ssid', 'RR+ C_ RR+'), w.s([], 'oveq1', '( y = %s -> ( y ^c %s ) = %s )' % (INN, NH, RGt))], 'cncfcompt2',
              '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0, XLH, RGt, XLH))
    rgibl = w.s([lor, hir, rgc, w.inst('cniccibl')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, XLH, RGt))
    nhr = w.s([a1(w, AT, 'halfre', '%s e. RR' % HF)], 'renegcld', '( %s -> %s e. RR )' % (AT, NH))
    rgrp = D(w, AT, 'rpcxpcld', [inrp, nhr], '%s e. RR+' % RGt)
    # integrable on ( P , Q ) and on ( LO , HI )
    iccpq = w.s([D(w, A0, 'jca', [lor, hir], '( %s e. RR /\\ %s e. RR )' % (LO, HI)), D(w, A0, 'jca', [lop, qhi], '( %s <_ P /\\ Q <_ %s )' % (LO, HI)), w.inst('iccss')], 'syl2anc',
                '( %s -> ( P [,] Q ) C_ %s )' % (A0, XLH))
    opqs = w.s([a1(w, A0, 'ioossicc', '%s C_ ( P [,] Q )' % OPQ), iccpq], 'sstrd', '( %s -> %s C_ %s )' % (A0, OPQ, XLH))
    iblpq = w.s([opqs, a1(w, A0, 'ioombl', '%s e. dom vol' % OPQ), D(w, AT, 'rpcnd', [rgrp], '%s e. CC' % RGt), rgibl], 'iblss', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, OPQ, RGt))
    # the two sides of B
    SL = '( %s (,) B )' % LO; SR = '( B (,) %s )' % HI
    ATL = '( %s /\\ t e. %s )' % (A0, SL)
    iol = w.s([w.s([w.s([lor], 'rexrd', '( %s -> %s e. RR* )' % (A0, LO)), w.s([br], 'rexrd', '( %s -> B e. RR* )' % A0), w.inst('elioo2')], 'syl2anc',
                   '( %s -> ( t e. %s <-> ( t e. RR /\\ %s < t /\\ t < B ) ) )' % (A0, SL, LO))], 'biimpa', '( %s -> ( t e. RR /\\ %s < t /\\ t < B ) )' % (ATL, LO))
    tl = D(w, ATL, 'simp1d', [iol], 't e. RR'); tlb = D(w, ATL, 'simp3d', [iol], 't < B')
    brl = w.s([br], 'adantr', '( %s -> B e. RR )' % ATL)
    abl = w.s([tl, brl, D(w, ATL, 'ltled', [tl, brl, tlb], 't <_ B'), w.inst('abssuble0')], 'syl3anc', '( %s -> ( abs ` ( t - B ) ) = ( B - t ) )' % ATL)
    cll = Closure(w, ATL, {'t': ('RR', tl), 'B': ('RR', brl), 'E': ('RR', w.s([er], 'adantr', '( %s -> E e. RR )' % ATL))})
    KHL = '( ( -u 1 x. t ) + ( B + E ) )'
    rwl = w.s([w.s([abl], 'oveq1d', '( %s -> %s = ( ( B - t ) + E ) )' % (ATL, INN)), lineq(w, ATL, '( ( B - t ) + E )', KHL, closure=cll)], 'eqtrd', '( %s -> %s = %s )' % (ATL, INN, KHL))
    rgl = w.s([rwl], 'oveq1d', '( %s -> %s = ( %s ^c %s ) )' % (ATL, RGt, KHL, NH))
    ATR = '( %s /\\ t e. %s )' % (A0, SR)
    ior = w.s([w.s([w.s([br], 'rexrd', '( %s -> B e. RR* )' % A0), w.s([hir], 'rexrd', '( %s -> %s e. RR* )' % (A0, HI)), w.inst('elioo2')], 'syl2anc',
                   '( %s -> ( t e. %s <-> ( t e. RR /\\ B < t /\\ t < %s ) ) )' % (A0, SR, HI))], 'biimpa', '( %s -> ( t e. RR /\\ B < t /\\ t < %s ) )' % (ATR, HI))
    trr = D(w, ATR, 'simp1d', [ior], 't e. RR'); tbr_ = D(w, ATR, 'simp2d', [ior], 'B < t')
    brr = w.s([br], 'adantr', '( %s -> B e. RR )' % ATR)
    abr_ = w.s([brr, trr, D(w, ATR, 'ltled', [brr, trr, tbr_], 'B <_ t'), w.inst('abssubge0')], 'syl3anc', '( %s -> ( abs ` ( t - B ) ) = ( t - B ) )' % ATR)
    clr = Closure(w, ATR, {'t': ('RR', trr), 'B': ('RR', brr), 'E': ('RR', w.s([er], 'adantr', '( %s -> E e. RR )' % ATR))})
    KHR = '( ( 1 x. t ) + ( E - B ) )'
    rwr = w.s([w.s([abr_], 'oveq1d', '( %s -> %s = ( ( t - B ) + E ) )' % (ATR, INN)), lineq(w, ATR, '( ( t - B ) + E )', KHR, closure=clr)], 'eqtrd', '( %s -> %s = %s )' % (ATR, INN, KHR))
    rgr = w.s([rwr], 'oveq1d', '( %s -> %s = ( %s ^c %s ) )' % (ATR, RGt, KHR, NH))

    def ipaf(P_, Q_, K_, H_, lep, posf):
        kr_ = a1(w, A0, 'neg1rr' if K_ == '-u 1' else '1re', '%s e. RR' % K_)
        kn_ = a1(w, A0, 'neg1ne0' if K_ == '-u 1' else 'ax-1ne0', '%s =/= 0' % K_)
        k3 = D(w, A0, '3jca', [kr_, kn_, cl.mem(H_, 'RR')], '( %s e. RR /\\ %s =/= 0 /\\ %s e. RR )' % (K_, K_, H_))
        p3 = D(w, A0, '3jca', [cl.mem(P_, 'RR'), cl.mem(Q_, 'RR'), lep], '( %s e. RR /\\ %s e. RR /\\ %s <_ %s )' % (P_, Q_, P_, Q_))
        AU = '( %s /\\ u e. ( %s [,] %s ) )' % (A0, P_, Q_)
        el = w.s([w.s([w.s([cl.mem(P_, 'RR')], 'adantr', '( %s -> %s e. RR )' % (AU, P_)), w.s([cl.mem(Q_, 'RR')], 'adantr', '( %s -> %s e. RR )' % (AU, Q_)), w.inst('elicc2')], 'syl2anc',
                      '( %s -> ( u e. ( %s [,] %s ) <-> ( u e. RR /\\ %s <_ u /\\ u <_ %s ) ) )' % (AU, P_, Q_, P_, Q_)), w.s([], 'simpr', '( %s -> u e. ( %s [,] %s ) )' % (AU, P_, Q_))],
                 'mpbid', '( %s -> ( u e. RR /\\ %s <_ u /\\ u <_ %s ) )' % (AU, P_, Q_))
        clu = Closure(w, AU, {'u': ('RR', D(w, AU, 'simp1d', [el], 'u e. RR')), 'B': ('RR', w.s([br], 'adantr', '( %s -> B e. RR )' % AU)),
                              'E': ('RR', w.s([er], 'adantr', '( %s -> E e. RR )' % AU)), 'D': ('RR', w.s([dr], 'adantr', '( %s -> D e. RR )' % AU))})
        g = linarith(w, AU, [D(w, AU, posf[0], [el], posf[1]), w.s([e0], 'adantr', '( %s -> 0 < E )' % AU)], '0 < ( ( %s x. u ) + %s )' % (K_, H_), closure=clu)
        pos = w.s([g], 'ralrimiva', '( %s -> A. u e. ( %s [,] %s ) 0 < ( ( %s x. u ) + %s ) )' % (A0, P_, Q_, K_, H_))
        hyp = D(w, A0, 'jca', [k3, D(w, A0, 'jca', [p3, pos], '( ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) /\\ A. u e. ( %s [,] %s ) 0 < ( ( %s x. u ) + %s ) )' % (P_, Q_, P_, Q_, P_, Q_, K_, H_))],
                '( ( %s e. RR /\\ %s =/= 0 /\\ %s e. RR ) /\\ ( ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) /\\ A. u e. ( %s [,] %s ) 0 < ( ( %s x. u ) + %s ) ) )' % (K_, K_, H_, P_, Q_, P_, Q_, P_, Q_, K_, H_))
        KT = '( ( ( %s x. t ) + %s ) ^c %s )' % (K_, H_, NH)
        V = '( ( ( 2 x. ( ( ( %s x. %s ) + %s ) ^c %s ) ) - ( 2 x. ( ( ( %s x. %s ) + %s ) ^c %s ) ) ) / %s )' % (K_, Q_, H_, HF, K_, P_, H_, HF, K_)
        return w.s([hyp, w.inst('ef1ipaf')], 'syl', '( %s -> ( ( t e. ( %s (,) %s ) |-> %s ) e. L^1 /\\ S. ( %s (,) %s ) %s _d t = %s ) )' % (A0, P_, Q_, KT, P_, Q_, KT, V)), KT, V

    pl, KTL, VL = ipaf(LO, 'B', '-u 1', '( B + E )', lob, ('simp3d', 'u <_ B'))
    pr2, KTR, VR = ipaf('B', HI, '1', '( E - B )', bhi, ('simp2d', 'B <_ u'))
    iblL = w.s([w.s([rgl], 'mpteq2dva', '( %s -> ( t e. %s |-> %s ) = ( t e. %s |-> %s ) )' % (A0, SL, RGt, SL, KTL)), w.s([pl], 'simpld', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, SL, KTL))],
               'eqeltrd', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, SL, RGt))
    iblR = w.s([w.s([rgr], 'mpteq2dva', '( %s -> ( t e. %s |-> %s ) = ( t e. %s |-> %s ) )' % (A0, SR, RGt, SR, KTR)), w.s([pr2], 'simpld', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, SR, KTR))],
               'eqeltrd', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, SR, RGt))
    ATV = '( %s /\\ t e. %s )' % (A0, OLH)
    tvx = w.s([w.s([a1(w, A0, 'ioossicc', '%s C_ %s' % (OLH, XLH))], 'adantr', '( %s -> %s C_ %s )' % (ATV, OLH, XLH)), w.s([], 'simpr', '( %s -> t e. %s )' % (ATV, OLH))], 'sseldd',
              '( %s -> t e. %s )' % (ATV, XLH))
    rgrpv = w.s([w.s([], 'simpl', '( %s -> %s )' % (ATV, A0)), tvx, w.s([rgrp], 'ex', '( %s -> ( t e. %s -> %s e. RR+ ) )' % (A0, XLH, RGt))], 'sylc', '( %s -> %s e. RR+ )' % (ATV, RGt))
    rgcv = D(w, ATV, 'rpcnd', [rgrpv], '%s e. CC' % RGt)
    bin_ = w.s([w.s([lor, hir, w.inst('elicc2')], 'syl2anc', '( %s -> ( B e. %s <-> ( B e. RR /\\ %s <_ B /\\ B <_ %s ) ) )' % (A0, XLH, LO, HI)),
                D(w, A0, '3jca', [br, lob, bhi], '( B e. RR /\\ %s <_ B /\\ B <_ %s )' % (LO, HI))], 'mpbird', '( %s -> B e. %s )' % (A0, XLH))
    spl = w.s([lor, hir, bin_, rgcv, iblL, iblR], 'itgsplitioo', '( %s -> S. %s %s _d t = ( S. %s %s _d t + S. %s %s _d t ) )' % (A0, OLH, RGt, SL, RGt, SR, RGt))
    itL = w.s([w.s([rgl], 'itgeq2dv', '( %s -> S. %s %s _d t = S. %s %s _d t )' % (A0, SL, RGt, SL, KTL)), w.s([pl], 'simprd', '( %s -> S. %s %s _d t = %s )' % (A0, SL, KTL, VL))],
              'eqtrd', '( %s -> S. %s %s _d t = %s )' % (A0, SL, RGt, VL))
    itR = w.s([w.s([rgr], 'itgeq2dv', '( %s -> S. %s %s _d t = S. %s %s _d t )' % (A0, SR, RGt, SR, KTR)), w.s([pr2], 'simprd', '( %s -> S. %s %s _d t = %s )' % (A0, SR, KTR, VR))],
              'eqtrd', '( %s -> S. %s %s _d t = %s )' % (A0, SR, RGt, VR))
    SD = '( ( D + E ) ^c %s )' % HF; SE = '( E ^c %s )' % HF
    DE = '( D + E )'
    derp = D(w, A0, 'elrpd', [cl.mem(DE, 'RR'), linarith(w, A0, [d0, e0], '0 < %s' % DE, closure=cl)], '%s e. RR+' % DE)
    hfr = a1(w, A0, 'halfre', '%s e. RR' % HF)
    sdr = D(w, A0, 'rpcxpcld', [derp, hfr], '%s e. RR+' % SD); ser = D(w, A0, 'rpcxpcld', [erp, hfr], '%s e. RR+' % SE)
    cl.leaf(SD, 'RR+', sdr); cl.leaf(SE, 'RR+', ser)

    def arg(lhs, rhs):
        e = lineq(w, A0, lhs, rhs, closure=cl)
        e2 = w.s([e], 'oveq1d', '( %s -> ( %s ^c %s ) = ( %s ^c %s ) )' % (A0, lhs, HF, rhs, HF))
        return w.s([e2], 'oveq2d', '( %s -> ( 2 x. ( %s ^c %s ) ) = ( 2 x. ( %s ^c %s ) ) )' % (A0, lhs, HF, rhs, HF))

    NUML = '( ( 2 x. ( ( ( -u 1 x. B ) + ( B + E ) ) ^c %s ) ) - ( 2 x. ( ( ( -u 1 x. %s ) + ( B + E ) ) ^c %s ) ) )' % (HF, LO, HF)
    NUMR = '( ( 2 x. ( ( ( 1 x. %s ) + ( E - B ) ) ^c %s ) ) - ( 2 x. ( ( ( 1 x. B ) + ( E - B ) ) ^c %s ) ) )' % (HI, HF, HF)
    T2D = '( 2 x. %s )' % SD; T2E = '( 2 x. %s )' % SE
    nl = w.s([arg('( ( -u 1 x. B ) + ( B + E ) )', 'E'), arg('( ( -u 1 x. %s ) + ( B + E ) )' % LO, DE)], 'oveq12d', '( %s -> %s = ( %s - %s ) )' % (A0, NUML, T2E, T2D))
    nr = w.s([arg('( ( 1 x. %s ) + ( E - B ) )' % HI, DE), arg('( ( 1 x. B ) + ( E - B ) )', 'E')], 'oveq12d', '( %s -> %s = ( %s - %s ) )' % (A0, NUMR, T2D, T2E))
    t2dc = D(w, A0, 'recnd', [cl.mem(T2D, 'RR')], '%s e. CC' % T2D); t2ec = D(w, A0, 'recnd', [cl.mem(T2E, 'RR')], '%s e. CC' % T2E)
    dfc = D(w, A0, 'subcld', [t2ec, t2dc], '( %s - %s ) e. CC' % (T2E, T2D))
    c1_ = a1(w, A0, 'ax-1cn', '1 e. CC'); n10 = a1(w, A0, 'ax-1ne0', '1 =/= 0')
    RES = '( %s - %s )' % (T2D, T2E)
    q1 = w.s([dfc, c1_, n10], 'divneg2d', '( %s -> -u ( ( %s - %s ) / 1 ) = ( ( %s - %s ) / -u 1 ) )' % (A0, T2E, T2D, T2E, T2D))
    q2 = w.s([w.s([dfc], 'div1d', '( %s -> ( ( %s - %s ) / 1 ) = ( %s - %s ) )' % (A0, T2E, T2D, T2E, T2D))], 'negeqd', '( %s -> -u ( ( %s - %s ) / 1 ) = -u ( %s - %s ) )' % (A0, T2E, T2D, T2E, T2D))
    q3 = w.s([t2ec, t2dc], 'negsubdi2d', '( %s -> -u ( %s - %s ) = %s )' % (A0, T2E, T2D, RES))
    vl = chain(w, A0, [VL, '( ( %s - %s ) / -u 1 )' % (T2E, T2D), '-u ( ( %s - %s ) / 1 )' % (T2E, T2D), '-u ( %s - %s )' % (T2E, T2D), RES],
               [w.s([nl], 'oveq1d', '( %s -> %s = ( ( %s - %s ) / -u 1 ) )' % (A0, VL, T2E, T2D)), ('r', q1), q2, q3])
    vr = w.s([w.s([nr], 'oveq1d', '( %s -> %s = ( %s / 1 ) )' % (A0, VR, RES)), w.s([D(w, A0, 'subcld', [t2dc, t2ec], '%s e. CC' % RES)], 'div1d', '( %s -> ( %s / 1 ) = %s )' % (A0, RES, RES))],
             'eqtrd', '( %s -> %s = %s )' % (A0, VR, RES))
    tot = w.s([spl, w.s([w.s([itL, vl], 'eqtrd', '( %s -> S. %s %s _d t = %s )' % (A0, SL, RGt, RES)), w.s([itR, vr], 'eqtrd', '( %s -> S. %s %s _d t = %s )' % (A0, SR, RGt, RES))],
                        'oveq12d', '( %s -> ( S. %s %s _d t + S. %s %s _d t ) = ( %s + %s ) )' % (A0, SL, RGt, SR, RGt, RES, RES))], 'eqtrd', '( %s -> S. %s %s _d t = ( %s + %s ) )' % (A0, OLH, RGt, RES, RES))
    # ( P , Q ) against ( LO , HI )
    IF = 'if ( t e. %s , %s , 0 )' % (OPQ, RGt)
    oss = w.s([D(w, A0, 'jca', [w.s([lor], 'rexrd', '( %s -> %s e. RR* )' % (A0, LO)), w.s([hir], 'rexrd', '( %s -> %s e. RR* )' % (A0, HI))], '( %s e. RR* /\\ %s e. RR* )' % (LO, HI)),
               D(w, A0, 'jca', [lop, qhi], '( %s <_ P /\\ Q <_ %s )' % (LO, HI)), w.inst('ioossioo')], 'syl2anc', '( %s -> %s C_ %s )' % (A0, OPQ, OLH))
    ATD = '( %s /\\ t e. ( %s \\ %s ) )' % (A0, OLH, OPQ)
    if0 = w.s([w.s([w.s([], 'simpr', '( %s -> t e. ( %s \\ %s ) )' % (ATD, OLH, OPQ)), w.inst('eldifn')], 'syl', '( %s -> -. t e. %s )' % (ATD, OPQ))], 'iffalsed', '( %s -> %s = 0 )' % (ATD, IF))
    ATP = '( %s /\\ t e. %s )' % (A0, OPQ)
    if1 = w.s([w.s([], 'simpr', '( %s -> t e. %s )' % (ATP, OPQ))], 'iftrued', '( %s -> %s = %s )' % (ATP, IF, RGt))
    iss = w.s([oss, if0], 'itgss', '( %s -> S. %s %s _d t = S. %s %s _d t )' % (A0, OPQ, IF, OLH, IF))
    ipq = w.s([if1], 'itgeq2dv', '( %s -> S. %s %s _d t = S. %s %s _d t )' % (A0, OPQ, IF, OPQ, RGt))
    ifpq = w.s([w.s([if1], 'mpteq2dva', '( %s -> ( t e. %s |-> %s ) = ( t e. %s |-> %s ) )' % (A0, OPQ, IF, OPQ, RGt)), iblpq], 'eqeltrd', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, OPQ, IF))
    ifvp = w.s([if1, w.s([w.s([], 'simpl', '( %s -> %s )' % (ATP, A0)), w.s([w.s([opqs], 'adantr', '( %s -> %s C_ %s )' % (ATP, OPQ, XLH)), w.s([], 'simpr', '( %s -> t e. %s )' % (ATP, OPQ))], 'sseldd',
                                                                                   '( %s -> t e. %s )' % (ATP, XLH)), w.s([D(w, AT, 'rpcnd', [rgrp], '%s e. CC' % RGt)], 'ex', '( %s -> ( t e. %s -> %s e. CC ) )' % (A0, XLH, RGt))],
                             'sylc', '( %s -> %s e. CC )' % (ATP, RGt))], 'eqeltrd', '( %s -> %s e. CC )' % (ATP, IF))
    iblif = w.s([oss, a1(w, A0, 'ioombl', '%s e. dom vol' % OLH), ifvp, if0, ifpq], 'iblss2', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, OLH, IF))
    iblrg = w.s([a1(w, A0, 'ioossicc', '%s C_ %s' % (OLH, XLH)), a1(w, A0, 'ioombl', '%s e. dom vol' % OLH), D(w, AT, 'rpcnd', [rgrp], '%s e. CC' % RGt), rgibl], 'iblss',
                '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, OLH, RGt))
    rgrv = D(w, ATV, 'rpred', [rgrpv], '%s e. RR' % RGt)
    ifr = w.s([rgrv, a1(w, ATV, '0re', '0 e. RR')], 'ifcld', '( %s -> %s e. RR )' % (ATV, IF))
    ifb1 = w.s([], 'breq1', '( %s = %s -> ( %s <_ %s <-> %s <_ %s ) )' % (RGt, IF, RGt, RGt, IF, RGt))
    ifb2 = w.s([], 'breq1', '( 0 = %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (IF, RGt, IF, RGt))
    ATV1 = '( %s /\\ t e. %s )' % (ATV, OPQ); ATV2 = '( %s /\\ -. t e. %s )' % (ATV, OPQ)
    le1 = w.s([w.s([rgrv], 'adantr', '( %s -> %s e. RR )' % (ATV1, RGt))], 'leidd', '( %s -> %s <_ %s )' % (ATV1, RGt, RGt))
    le2 = w.s([w.s([w.s([rgrpv], 'rpge0d', '( %s -> 0 <_ %s )' % (ATV, RGt))], 'adantr', '( %s -> 0 <_ %s )' % (ATV2, RGt))], 'idi', '( %s -> 0 <_ %s )' % (ATV2, RGt))
    ifle = w.s([ifb1, ifb2, le1, le2], 'ifbothda', '( %s -> %s <_ %s )' % (ATV, IF, RGt))
    cmp_ = w.s([iblif, iblrg, ifr, rgrv, ifle], 'itgle', '( %s -> S. %s %s _d t <_ S. %s %s _d t )' % (A0, OLH, IF, OLH, RGt))
    ch = w.s([w.s([w.s([ipq], 'eqcomd', '( %s -> S. %s %s _d t = S. %s %s _d t )' % (A0, OPQ, RGt, OPQ, IF)), iss], 'eqtrd', '( %s -> S. %s %s _d t = S. %s %s _d t )' % (A0, OPQ, RGt, OLH, IF)), cmp_],
             'eqbrtrd', '( %s -> S. %s %s _d t <_ S. %s %s _d t )' % (A0, OPQ, RGt, OLH, RGt))
    ch2 = w.s([ch, tot], 'breqtrd', '( %s -> S. %s %s _d t <_ ( %s + %s ) )' % (A0, OPQ, RGt, RES, RES))
    fin = linarith(w, A0, [D(w, A0, 'rpge0d', [ser], '0 <_ %s' % SE)], '( %s + %s ) <_ ( 4 x. %s )' % (RES, RES, SD), closure=cl)
    rgpq = w.s([w.s([], 'simpl', '( %s -> %s )' % (ATP, A0)), w.s([w.s([opqs], 'adantr', '( %s -> %s C_ %s )' % (ATP, OPQ, XLH)), w.s([], 'simpr', '( %s -> t e. %s )' % (ATP, OPQ))], 'sseldd',
                '( %s -> t e. %s )' % (ATP, XLH)), w.s([D(w, AT, 'rpred', [rgrp], '%s e. RR' % RGt)], 'ex', '( %s -> ( t e. %s -> %s e. RR ) )' % (A0, XLH, RGt))], 'sylc', '( %s -> %s e. RR )' % (ATP, RGt))
    itr = w.s([rgpq, iblpq], 'itgrecl', '( %s -> S. %s %s _d t e. RR )' % (A0, OPQ, RGt))
    fin2 = w.s([itr, cl.mem('( %s + %s )' % (RES, RES), 'RR'), cl.mem('( 4 x. %s )' % SD, 'RR'), ch2, fin], 'letrd', '( %s -> S. %s %s _d t <_ ( 4 x. %s ) )' % (A0, OPQ, RGt, SD))
    w.qed([iblpq, fin2], 'jca', STATEMENTS['ef1ir'])
    go(w, only)
