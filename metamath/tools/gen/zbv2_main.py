"""Sortie ZBV2, section 1 part D: bvmchks assembled from the chord facts, the C
sums and the generic Abel bound (ZBV2-blueprint.md section 1.2).

bvmchkslem1  TERM(K) = ( MQ(K) x. G(K) )
bvmchkslem3  ( SUM(N) - CX(N) CS(Y,N) ) = ( sum_ n < N MQ(n) ( G(n) - G(N) ) - CX(N) CS(N,N) )
bvmchkslem2  | the right side | <= ( 11 / 3 ) ( R(1) - CX(N) )        [bvabelin]
bvmchks2 / bvmchks1 / bvmchks
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *
from zbv2_chord import gcl

NE_C = NE


def ylift(w, ys, A):
    """the ysfacts dict lifted to the antecedent A (cl.lift; a no-op at the same antecedent)"""
    return {k: lift(w, v, A) for k, v in ys.items()}


def gfull(w, A, ys, knn, k):
    """kfacts + gcl for an index k e. NN (step knn) under A; ys is lifted to A"""
    kf = kfacts(w, A, knn, k)
    return kf, gcl(w, A, ylift(w, ys, A), kf['rp'], k)


def bvmchkslem1():
    w = W('bvmchkslem1', 'One term of the sigma sum as a coefficient times the kernel: '
                         'mmu K K ^c -u S log ( Y / K ) = ( mmu K / K ) ( K ^c -u ( S - 1 ) log ( Y / K ) ).')
    A = '( %s /\\ K e. NN )' % HYS
    st = mkst(w, A)
    ys = ysfacts(w, A, st([], 'simpl', HYS))
    knn = st([], 'simpr', 'K e. NN')
    kf = kfacts(w, A, knn, 'K'); mf = mqfacts(w, A, knn, 'K')
    c = cxfacts(w, A, kf['rp'], ys['ner'], 'K'); lg = lgfacts(w, A, ys['yrp'], kf['rp'], 'K')
    negS = lineq(w, A, '-u S', '( -u 1 + %s )' % NE, leaves={'S': ys['sr']})
    m1c = st([clo(w, 'neg1cn', '-u 1 e. CC')], 'a1i', '-u 1 e. CC')
    nec = st([ys['ner']], 'recnd', '%s e. CC' % NE)
    e1 = st([negS], 'oveq2d', '( K ^c -u S ) = ( K ^c ( -u 1 + %s ) )' % NE)
    e2 = st([kf['cc'], kf['ne'], m1c, nec], 'cxpaddd', '( K ^c ( -u 1 + %s ) ) = ( ( K ^c -u 1 ) x. %s )' % (NE, CX('K')))
    e3 = st([kf['cc'], kf['ne'], st([], '1cnd', '1 e. CC')], 'cxpnegd', '( K ^c -u 1 ) = ( 1 / ( K ^c 1 ) )')
    e4 = st([st([kf['cc']], 'cxp1d', '( K ^c 1 ) = K')], 'oveq2d', '( 1 / ( K ^c 1 ) ) = ( 1 / K )')
    e5 = st([st([e3, e4], 'eqtrd', '( K ^c -u 1 ) = ( 1 / K )')], 'oveq1d', '( ( K ^c -u 1 ) x. %s ) = ( ( 1 / K ) x. %s )' % (CX('K'), CX('K')))
    ks = eqtr(w, A, [e1, e2, e5], None)
    rkc = st([kf['cc'], kf['ne']], 'reccld', '( 1 / K ) e. CC')
    t1 = st([ks], 'oveq2d', '( %s x. ( K ^c -u S ) ) = ( %s x. ( ( 1 / K ) x. %s ) )' % (MU('K'), MU('K'), CX('K')))
    t2 = st([st([mf['muc'], rkc, c['cc']], 'mulassd', '( ( %s x. ( 1 / K ) ) x. %s ) = ( %s x. ( ( 1 / K ) x. %s ) )' % (MU('K'), CX('K'), MU('K'), CX('K')))], 'eqcomd',
            '( %s x. ( ( 1 / K ) x. %s ) ) = ( ( %s x. ( 1 / K ) ) x. %s )' % (MU('K'), CX('K'), MU('K'), CX('K')))
    t3 = st([st([st([mf['muc'], kf['cc'], kf['ne']], 'divrecd', '%s = ( %s x. ( 1 / K ) )' % (MQ('K'), MU('K')))], 'eqcomd', '( %s x. ( 1 / K ) ) = %s' % (MU('K'), MQ('K')))], 'oveq1d',
            '( ( %s x. ( 1 / K ) ) x. %s ) = ( %s x. %s )' % (MU('K'), CX('K'), MQ('K'), CX('K')))
    mus = eqtr(w, A, [t1, t2, t3], None)
    t4 = st([mus], 'oveq1d', '%s = ( ( %s x. %s ) x. %s )' % (TERM('K'), MQ('K'), CX('K'), LG('K')))
    t5 = st([mf['mqc'], c['cc'], lg['cc']], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (MQ('K'), CX('K'), LG('K'), MQ('K'), G('K')))
    w.qed([t4, t5], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A, TERM('K'), MQ('K'), G('K')))
    return w


def nfacts2(w, A, nu):
    """from nu: ( A -> N e. ( ZZ>= ` 2 ) ): NN, ZZ, RR, CC, RR+, 1 < N, 2 <_ N, N e. ( ZZ>= ` 1 )"""
    st = mkst(w, A)
    nnn = sy(w, A, nu, 'eluz2nn', 'N e. NN')
    d = dict(nn=nnn, z=st([nnn], 'nnzd', 'N e. ZZ'), re=st([nnn], 'nnred', 'N e. RR'), cc=st([nnn], 'nncnd', 'N e. CC'),
             rp=st([nnn], 'nnrpd', 'N e. RR+'), gt1=sy(w, A, nu, 'eluz2gt1', '1 < N'), ge2=sy(w, A, nu, 'eluzle', '2 <_ N'))
    d['uz1'] = st([nnn, st([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', 'N e. ( ZZ>= ` 1 )')
    return d


def csfacts(w, A, xrp, m, mnn=None):
    """( A -> CS(x,m) e. RR ), with x e. RR+ (step xrp) and the range ( 1 ... m ); returns (re, cc)"""
    st = mkst(w, A)
    from cl import formula_of, strip_ante
    X = strip_ante(formula_of(w, xrp), A).split(' e. RR+')[0]
    AN = '( %s /\\ n e. ( 1 ... %s ) )' % (A, m)
    sn = mkst(w, AN)
    nnn = sy(w, AN, sn([], 'simpr', 'n e. ( 1 ... %s )' % m), 'elfznn', 'n e. NN')
    mf = mqfacts(w, AN, nnn, 'n')
    lr = sn([sn([lift(w, xrp, AN), sn([nnn], 'nnrpd', 'n e. RR+')], 'rpdivcld', '( %s / n ) e. RR+' % X)], 'relogcld', '( log ` ( %s / n ) ) e. RR' % X)
    re = st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % m), sn([mf['mqr'], lr], 'remulcld', '( %s x. ( log ` ( %s / n ) ) ) e. RR' % (MQ('n'), X))], 'fsumrecl', '%s e. RR' % CS(X, m))
    return re, st([re], 'recnd', '%s e. CC' % CS(X, m))


def bvmchkslem3():
    w = W('bvmchkslem3', 'The sigma sum minus N ^c -u E C ( Y , N ) as the Abel form: the log shift of C '
                         '(bvcshift) and the vanishing term n = N.')
    PH = '( %s /\\ N e. ( ZZ>= ` 2 ) )' % HYS
    st = mkst(w, PH)
    hys = st([], 'simpl', HYS); ys = ysfacts(w, PH, hys)
    nu = st([], 'simpr', 'N e. ( ZZ>= ` 2 )'); nf = nfacts2(w, PH, nu)
    c = cxfacts(w, PH, nf['rp'], ys['ner'], 'N'); lg = lgfacts(w, PH, ys['yrp'], nf['rp'], 'N')
    gNr = st([c['re'], lg['re']], 'remulcld', '%s e. RR' % G('N')); gNc = st([gNr], 'recnd', '%s e. CC' % G('N'))
    AN = '( %s /\\ n e. ( 1 ... N ) )' % PH
    sn = mkst(w, AN)
    nnnn = sy(w, AN, sn([], 'simpr', 'n e. ( 1 ... N )'), 'elfznn', 'n e. NN')
    mfn = mqfacts(w, AN, nnnn, 'n')
    kfn = kfacts(w, AN, nnnn, 'n')
    cn = cxfacts(w, AN, kfn['rp'], lift(w, ys['ner'], AN), 'n'); lgn = lgfacts(w, AN, lift(w, ys['yrp'], AN), kfn['rp'], 'n')
    gnr = sn([cn['re'], lgn['re']], 'remulcld', '%s e. RR' % G('n')); gnc = sn([gnr], 'recnd', '%s e. CC' % G('n'))
    ant = bind(w, AN, lift(w, hys, AN), nnnn, HYS, 'n e. NN')
    l1 = sn([ant, w.inst('bvmchkslem1')], 'syl', '%s = ( %s x. %s )' % (TERM('n'), MQ('n'), G('n')))
    SMG = 'sum_ n e. ( 1 ... N ) ( %s x. %s )' % (MQ('n'), G('n'))
    s1 = st([l1], 'sumeq2dv', '%s = %s' % (SUMN('N'), SMG))
    fin = st([], 'fzfid', '( 1 ... N ) e. Fin')
    # closures of the sums
    nsr = sn([sn([kfn['rp'], sn([lift(w, ys['sr'], AN)], 'renegcld', '-u S e. RR')], 'rpcxpcld', '( n ^c -u S ) e. RR+')], 'rpred', '( n ^c -u S ) e. RR')
    termr = sn([sn([mfn['mur'], nsr], 'remulcld', '( %s x. ( n ^c -u S ) ) e. RR' % MU('n')), lgn['re']], 'remulcld', '%s e. RR' % TERM('n'))
    sumr = st([fin, termr], 'fsumrecl', '%s e. RR' % SUMN('N'))
    smgr = st([fin, sn([mfn['mqr'], gnr], 'remulcld', '( %s x. %s ) e. RR' % (MQ('n'), G('n')))], 'fsumrecl', '%s e. RR' % SMG)
    asr = st([fin, mfn['mqr']], 'fsumrecl', '%s e. RR' % AS('N')); asc = st([asr], 'recnd', '%s e. CC' % AS('N'))
    csyr, csyc = csfacts(w, PH, ys['yrp'], 'N'); csnr, csnc = csfacts(w, PH, nf['rp'], 'N')
    # the shift
    ant2 = bind(w, PH, bind(w, PH, ys['yrp'], nf['rp'], 'Y e. RR+', 'N e. RR+'), nf['nn'], '( Y e. RR+ /\\ N e. RR+ )', 'N e. NN')
    sh = st([ant2, w.inst('bvcshift')], 'syl', '%s = ( %s + ( %s x. %s ) )' % (CS('Y', 'N'), CS('N', 'N'), LG('N'), AS('N')))
    LA = '( %s x. %s )' % (LG('N'), AS('N')); lac = st([lg['cc'], asc], 'mulcld', '%s e. CC' % LA)
    GA = '( %s x. %s )' % (G('N'), AS('N'))
    s3 = eqtr(w, PH, [st([sh], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s + %s ) )' % (CX('N'), CS('Y', 'N'), CX('N'), CS('N', 'N'), LA)),
                      st([c['cc'], csnc, lac], 'adddid', '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (CX('N'), CS('N', 'N'), LA, CX('N'), CS('N', 'N'), CX('N'), LA)),
                      st([st([st([c['cc'], lg['cc'], asc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (CX('N'), LG('N'), AS('N'), CX('N'), LA))], 'eqcomd', '( %s x. %s ) = %s' % (CX('N'), LA, GA))], 'oveq2d',
                         '( ( %s x. %s ) + ( %s x. %s ) ) = ( ( %s x. %s ) + %s )' % (CX('N'), CS('N', 'N'), CX('N'), LA, CX('N'), CS('N', 'N'), GA))], None)
    # SD = SMG - G(N) AS(N)
    BODY = '( %s x. ( %s - %s ) )' % (MQ('n'), G('n'), G('N'))
    SD = 'sum_ n e. ( 1 ... N ) %s' % BODY
    T2 = '( %s x. %s )' % (MQ('n'), G('N'))
    gNn = lift(w, gNc, AN)
    bd = sn([mfn['mqc'], gnc, gNn], 'subdid', '%s = ( ( %s x. %s ) - %s )' % (BODY, MQ('n'), G('n'), T2))
    a_c = sn([mfn['mqc'], gnc], 'mulcld', '( %s x. %s ) e. CC' % (MQ('n'), G('n'))); b_c = sn([mfn['mqc'], gNn], 'mulcld', '%s e. CC' % T2)
    S2 = 'sum_ n e. ( 1 ... N ) %s' % T2
    s4 = eqtr(w, PH, [st([bd], 'sumeq2dv', '%s = sum_ n e. ( 1 ... N ) ( ( %s x. %s ) - %s )' % (SD, MQ('n'), G('n'), T2)),
                      st([fin, a_c, b_c], 'fsumsub', 'sum_ n e. ( 1 ... N ) ( ( %s x. %s ) - %s ) = ( %s - %s )' % (MQ('n'), G('n'), T2, SMG, S2)),
                      st([st([st([st([fin, gNc, mfn['mqc']], 'fsummulc1', '( %s x. %s ) = %s' % (AS('N'), G('N'), S2))], 'eqcomd', '%s = ( %s x. %s )' % (S2, AS('N'), G('N'))),
                              st([asc, gNc], 'mulcomd', '( %s x. %s ) = %s' % (AS('N'), G('N'), GA))], 'eqtrd', '%s = %s' % (S2, GA))], 'oveq2d', '( %s - %s ) = ( %s - %s )' % (SMG, S2, SMG, GA))], None)
    # peel n = N
    bodyc = sn([mfn['mqc'], sn([gnc, gNn], 'subcld', '( %s - %s ) e. CC' % (G('n'), G('N')))], 'mulcld', '%s e. CC' % BODY)
    idn = w.s([], 'id', '( n = N -> n = N )')
    subN, BN = w.congr(BODY, {'n': 'N'}, 'n = N', {'n': idn})
    SDp = 'sum_ n e. ( 1 ... ( N - 1 ) ) %s' % BODY
    m1 = st([nf['uz1'], bodyc, subN], 'fsumm1', '%s = ( %s + %s )' % (SD, SDp, BN))
    mfN = mqfacts(w, PH, nf['nn'], 'N')
    bn0 = st([st([st([gNc], 'subidd', '( %s - %s ) = 0' % (G('N'), G('N')))], 'oveq2d', '%s = ( %s x. 0 )' % (BN, MQ('N'))), st([mfN['mqc']], 'mul01d', '( %s x. 0 ) = 0' % MQ('N'))], 'eqtrd', '%s = 0' % BN)
    sdr = st([fin, sn([mfn['mqr'], sn([gnr, lift(w, gNr, AN)], 'resubcld', '( %s - %s ) e. RR' % (G('n'), G('N')))], 'remulcld', '%s e. RR' % BODY)], 'fsumrecl', '%s e. RR' % SD)
    sdc = st([sdr], 'recnd', '%s e. CC' % SD)
    # SD' e. CC from SD = SD' + BN, BN = 0: SD' = SD - BN
    m1b = st([m1, st([bn0], 'oveq2d', '( %s + %s ) = ( %s + 0 )' % (SDp, BN, SDp))], 'eqtrd', '%s = ( %s + 0 )' % (SD, SDp))
    # closure of SD' directly
    ANp = '( %s /\\ n e. ( 1 ... ( N - 1 ) ) )' % PH
    snp = mkst(w, ANp)
    nnp = sy(w, ANp, snp([], 'simpr', 'n e. ( 1 ... ( N - 1 ) )'), 'elfznn', 'n e. NN')
    mfp = mqfacts(w, ANp, nnp, 'n'); kfp = kfacts(w, ANp, nnp, 'n')
    cp = cxfacts(w, ANp, kfp['rp'], lift(w, ys['ner'], ANp), 'n'); lgp = lgfacts(w, ANp, lift(w, ys['yrp'], ANp), kfp['rp'], 'n')
    gpr = snp([cp['re'], lgp['re']], 'remulcld', '%s e. RR' % G('n'))
    sdpr = st([st([], 'fzfid', '( 1 ... ( N - 1 ) ) e. Fin'), snp([mfp['mqr'], snp([gpr, lift(w, gNr, ANp)], 'resubcld', '( %s - %s ) e. RR' % (G('n'), G('N')))], 'remulcld', '%s e. RR' % BODY)], 'fsumrecl', '%s e. RR' % SDp)
    s5 = st([m1b, st([st([sdpr], 'recnd', '%s e. CC' % SDp)], 'addridd', '( %s + 0 ) = %s' % (SDp, SDp))], 'eqtrd', '%s = %s' % (SD, SDp))
    LHS = '( %s - ( %s x. %s ) )' % (SUMN('N'), CX('N'), CS('Y', 'N')); RHS = '( %s - ( %s x. %s ) )' % (SDp, CX('N'), CS('N', 'N'))
    lineq(w, PH, LHS, RHS, hyps=[s1, s3, s4, s5],
          leaves={SUMN('N'): sumr, SMG: smgr, SD: sdr, SDp: sdpr, CX('N'): c['re'], CS('Y', 'N'): csyr, CS('N', 'N'): csnr, G('N'): gNr, AS('N'): asr}, name='qed')
    return w


# ---- the bvabelin instance
MA = '( t e. NN |-> %s )' % MQ('t'); MG = '( t e. NN |-> %s )' % G('t'); MR = '( t e. NN |-> %s )' % R('t')
ML = '( t e. NN |-> %s )' % ELL('t'); MF = '( t e. NN |-> %s )' % CS('t', 't')
PH2 = '( %s /\\ ( N e. ( ZZ>= ` 2 ) /\\ N <_ Y ) )' % HYS
NM = '( N - 1 )'; NM1 = '( ( N - 1 ) + 1 )'
FZ = '( 1 ... %s )' % NM; FZ1 = '( 1 ... %s )' % NM1; FZO = '( 1 ..^ %s )' % NM


def mval(w, ante, body, T, mem, sumbody=False):
    """( ante -> ( ( t e. NN |-> body ) ` T ) = body[T/t] ) ; returns (step, value)"""
    exs = None
    if sumbody:
        from congr import subst_toks
        val = ' '.join(subst_toks(body.split(), {'t': T}))
        exs = w.s([w.s([], 'sumex', '%s e. _V' % val)], 'a1i', '( %s -> %s e. _V )' % (ante, val))
    return mpv(w, ante, 't', 'NN', body, T, mem, exs=exs)


def bvmchkslem2():
    w = W('bvmchkslem2', 'The Abel bound for the sigma sum: bvabelin with A = mmu / n, G the kernel, R the chord '
                         'slopes, L the log gaps, F ( i ) = C ( i , i ), M = 11 / 3, P = N ^c -u E, on ( 1 ... ( N - 1 ) ).')
    st = mkst(w, PH2)
    hys = st([], 'simpl', HYS); ys = ysfacts(w, PH2, hys)
    nu = st([], 'simprl', 'N e. ( ZZ>= ` 2 )'); nley = st([], 'simprr', 'N <_ Y')
    nf = nfacts2(w, PH2, nu)
    nm1nn = sy(w, PH2, nu, 'uz2m1nn', '%s e. NN' % NM)
    npc = st([nf['cc'], st([], '1cnd', '1 e. CC')], 'npcand', '%s = N' % NM1)
    c = cxfacts(w, PH2, nf['rp'], ys['ner'], 'N')
    cl = Closure(w, PH2)
    m113r = cl.mem(M113, 'RR')
    hs = []
    hs.append(nm1nn); hs.append(m113r); hs.append(c['re'])
    # .4
    A4 = '( %s /\\ n e. %s )' % (PH2, FZ); s4 = mkst(w, A4)
    n4 = sy(w, A4, s4([], 'simpr', 'n e. %s' % FZ), 'elfznn', 'n e. NN')
    v4, _ = mval(w, A4, MQ('t'), 'n', n4)
    hs.append(s4([v4, mqfacts(w, A4, n4, 'n')['mqr']], 'eqeltrd', '( %s ` n ) e. RR' % MA))
    # .5
    A5 = '( %s /\\ i e. %s )' % (PH2, FZ1); s5 = mkst(w, A5)
    i5 = sy(w, A5, s5([], 'simpr', 'i e. %s' % FZ1), 'elfznn', 'i e. NN')
    v5, _ = mval(w, A5, G('t'), 'i', i5)
    kf5, g5 = gfull(w, A5, ys, i5, 'i')
    hs.append(s5([v5, g5['gr']], 'eqeltrd', '( %s ` i ) e. RR' % MG))
    # .6, .7, .9 under i e. FZ
    A6 = '( %s /\\ i e. %s )' % (PH2, FZ); s6 = mkst(w, A6)
    i6 = sy(w, A6, s6([], 'simpr', 'i e. %s' % FZ), 'elfznn', 'i e. NN')
    kf6, g6 = gfull(w, A6, ys, i6, 'i'); g6p = gcl(w, A6, ylift(w, ys, A6), kf6['p1rp'], P1('i'))
    el6 = ellfacts(w, A6, kf6, 'i')
    D6 = '( %s - %s )' % (G('i'), G(P1('i')))
    d6r = s6([g6['gr'], g6p['gr']], 'resubcld', '%s e. RR' % D6); d6c = s6([d6r], 'recnd', '%s e. CC' % D6)
    r6r = s6([d6r, el6['rp']], 'rerpdivcld', '%s e. RR' % R('i'))
    vR6, _ = mval(w, A6, R('t'), 'i', i6)
    hs.append(s6([vR6, r6r], 'eqeltrd', '( %s ` i ) e. RR' % MR))
    vL6, _ = mval(w, A6, ELL('t'), 'i', i6)
    h7 = s6([vL6, el6['re']], 'eqeltrd', '( %s ` i ) e. RR' % ML)
    hs.append(h7)
    # .8
    A8 = '( %s /\\ i e. %s )' % (PH2, FZ1); s8 = mkst(w, A8)
    i8 = sy(w, A8, s8([], 'simpr', 'i e. %s' % FZ1), 'elfznn', 'i e. NN')
    vF8, _ = mval(w, A8, CS('t', 't'), 'i', i8, sumbody=True)
    cs8r, _ = csfacts(w, A8, s8([i8], 'nnrpd', 'i e. RR+'), 'i')
    hs.append(s8([vF8, cs8r], 'eqeltrd', '( %s ` i ) e. RR' % MF))
    # .9
    vG6, _ = mval(w, A6, G('t'), 'i', i6); vG6p, _ = mval(w, A6, G('t'), P1('i'), kf6['p1nn'])
    lhs9 = s6([vG6, vG6p], 'oveq12d', '( ( %s ` i ) - ( %s ` %s ) ) = %s' % (MG, MG, P1('i'), D6))
    rhs9 = s6([vR6, vL6], 'oveq12d', '( ( %s ` i ) x. ( %s ` i ) ) = ( %s x. %s )' % (MR, ML, R('i'), ELL('i')))
    dc9 = s6([s6([d6c, el6['cc'], el6['ne']], 'divcan1d', '( %s x. %s ) = %s' % (R('i'), ELL('i'), D6))], 'eqcomd', '%s = ( %s x. %s )' % (D6, R('i'), ELL('i')))
    hs.append(s6([s6([lhs9, dc9], 'eqtrd', '( ( %s ` i ) - ( %s ` %s ) ) = ( %s x. %s )' % (MG, MG, P1('i'), R('i'), ELL('i'))), rhs9], 'eqtr4d',
                 '( ( %s ` i ) - ( %s ` %s ) ) = ( ( %s ` i ) x. ( %s ` i ) )' % (MG, MG, P1('i'), MR, ML)))
    # .10
    vF6p, _ = mval(w, A6, CS('t', 't'), P1('i'), kf6['p1nn'], sumbody=True)
    vF6, _ = mval(w, A6, CS('t', 't'), 'i', i6, sumbody=True)
    A6n = '( %s /\\ n e. ( 1 ... i ) )' % A6; s6n = mkst(w, A6n)
    n6 = sy(w, A6n, s6n([], 'simpr', 'n e. ( 1 ... i )'), 'elfznn', 'n e. NN')
    vA6n, _ = mval(w, A6n, MQ('t'), 'n', n6)
    SMA = 'sum_ n e. ( 1 ... i ) ( %s ` n )' % MA
    sma = s6([vA6n], 'sumeq2dv', '%s = %s' % (SMA, AS('i')))
    cp1 = sy(w, A6, i6, 'bvcp1', '%s = ( %s + ( %s x. %s ) )' % (CS(P1('i'), P1('i')), CS('i', 'i'), ELL('i'), AS('i')))
    rhs10 = s6([vF6, s6([vL6, sma], 'oveq12d', '( ( %s ` i ) x. %s ) = ( %s x. %s )' % (ML, SMA, ELL('i'), AS('i')))], 'oveq12d',
               '( ( %s ` i ) + ( ( %s ` i ) x. %s ) ) = ( %s + ( %s x. %s ) )' % (MF, ML, SMA, CS('i', 'i'), ELL('i'), AS('i')))
    hs.append(s6([s6([vF6p, cp1], 'eqtrd', '( %s ` %s ) = ( %s + ( %s x. %s ) )' % (MF, P1('i'), CS('i', 'i'), ELL('i'), AS('i'))), rhs10], 'eqtr4d',
                 '( %s ` %s ) = ( ( %s ` i ) + ( ( %s ` i ) x. %s ) )' % (MF, P1('i'), MF, ML, SMA)))
    # .11
    onenn = st([clo(w, '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    vF1, _ = mval(w, PH2, CS('t', 't'), '1', onenn, sumbody=True)
    hs.append(st([vF1, st([clo(w, 'bvc1', '%s = 0' % CS('1', '1'))], 'a1i', '%s = 0' % CS('1', '1'))], 'eqtrd', '( %s ` 1 ) = 0' % MF))
    # .12
    i8re = s8([i8], 'nnred', 'i e. RR'); i8ge1 = sy(w, A8, i8, 'nnge1', '1 <_ i')
    chk = sy2(w, A8, i8re, i8ge1, 'bvmchk1', '( abs ` sum_ n e. ( 1 ... ( |_ ` i ) ) ( %s x. ( log ` ( i / n ) ) ) ) <_ %s' % (MQ('n'), M113))
    fl = sy(w, A8, s8([i8], 'nnzd', 'i e. ZZ'), 'flid', '( |_ ` i ) = i')
    rng = s8([s8([s8([fl], 'oveq2d', '( 1 ... ( |_ ` i ) ) = ( 1 ... i )')], 'sumeq1d', 'sum_ n e. ( 1 ... ( |_ ` i ) ) ( %s x. ( log ` ( i / n ) ) ) = %s' % (MQ('n'), CS('i', 'i')))], 'fveq2d',
             '( abs ` sum_ n e. ( 1 ... ( |_ ` i ) ) ( %s x. ( log ` ( i / n ) ) ) ) = ( abs ` %s )' % (MQ('n'), CS('i', 'i')))
    hs.append(s8([s8([vF8], 'fveq2d', '( abs ` ( %s ` i ) ) = ( abs ` %s )' % (MF, CS('i', 'i'))), s8([rng, chk], 'eqbrtrrd', '( abs ` %s ) <_ %s' % (CS('i', 'i'), M113))], 'eqbrtrd',
                 '( abs ` ( %s ` i ) ) <_ %s' % (MF, M113)))
    # .13
    A13 = '( %s /\\ i e. %s )' % (PH2, FZO); s13 = mkst(w, A13)
    iel13 = s13([], 'simpr', 'i e. %s' % FZO)
    i13 = sy(w, A13, sy(w, A13, iel13, 'elfzofz', 'i e. %s' % FZ), 'elfznn', 'i e. NN')
    kf13 = kfacts(w, A13, i13, 'i')
    ilt = sy(w, A13, iel13, 'elfzolt2', 'i < %s' % NM)
    nmz = sy(w, A13, lift(w, nf['z'], A13), 'peano2zm', '%s e. ZZ' % NM)
    ile = s13([ilt, sy2(w, A13, s13([i13], 'nnzd', 'i e. ZZ'), nmz, 'zltp1le', '( i < %s <-> ( i + 1 ) <_ %s )' % (NM, NM))], 'mpbid', '( i + 1 ) <_ %s' % NM)
    k2y = linarith(w, A13, [ile, lift(w, nley, A13)], '( ( i + 1 ) + 1 ) <_ Y', leaves={'i': kf13['re'], 'N': lift(w, nf['re'], A13), 'Y': lift(w, ys['yr'], A13)})
    ant13 = bind(w, A13, lift(w, hys, A13), bind(w, A13, i13, k2y, 'i e. NN', '( ( i + 1 ) + 1 ) <_ Y'), HYS, HK2('i'))
    mono = s13([ant13, w.inst('bvrmono')], 'syl', '%s <_ %s' % (R(P1('i')), R('i')))
    vR13p, _ = mval(w, A13, R('t'), P1('i'), kf13['p1nn']); vR13, _ = mval(w, A13, R('t'), 'i', i13)
    hs.append(s13([mono, vR13p, vR13], '3brtr4d', '( %s ` %s ) <_ ( %s ` i )' % (MR, P1('i'), MR)))
    # .14
    ant14 = bind(w, PH2, hys, bind(w, PH2, nm1nn, st([npc, nley], 'eqbrtrd', '%s <_ Y' % NM1), '%s e. NN' % NM, '%s <_ Y' % NM1), HYS, HK(NM))
    last = st([ant14, w.inst('bvrlast')], 'syl', '%s <_ %s' % (CX(NM1), R(NM)))
    cxeq = st([st([npc], 'eqcomd', 'N = %s' % NM1)], 'oveq1d', '%s = %s' % (CX('N'), CX(NM1)))
    vRN, _ = mval(w, PH2, R('t'), NM, nm1nn)
    hs.append(st([st([cxeq, last], 'eqbrtrd', '%s <_ %s' % (CX('N'), R(NM))), vRN], 'breqtrrd', '%s <_ ( %s ` %s )' % (CX('N'), MR, NM)))
    assert len(hs) == 14
    SINST = 'sum_ n e. %s ( ( %s ` n ) x. ( ( %s ` n ) - ( %s ` %s ) ) )' % (FZ, MA, MG, MG, NM1)
    abel = st(hs, 'bvabelin', '( abs ` ( %s - ( %s x. ( %s ` %s ) ) ) ) <_ ( %s x. ( ( %s ` 1 ) - %s ) )' % (SINST, CX('N'), MF, NM1, M113, MR, CX('N')))
    # rewrite to the frozen form
    vGN, _ = mval(w, PH2, G('t'), 'N', nf['nn'])
    gN1eq = st([st([npc], 'fveq2d', '( %s ` %s ) = ( %s ` N )' % (MG, NM1, MG)), vGN], 'eqtrd', '( %s ` %s ) = %s' % (MG, NM1, G('N')))
    vG4, _ = mval(w, A4, G('t'), 'n', n4)
    body = s4([v4, s4([vG4, lift(w, gN1eq, A4)], 'oveq12d', '( ( %s ` n ) - ( %s ` %s ) ) = ( %s - %s )' % (MG, MG, NM1, G('n'), G('N')))], 'oveq12d',
              '( ( %s ` n ) x. ( ( %s ` n ) - ( %s ` %s ) ) ) = ( %s x. ( %s - %s ) )' % (MA, MG, MG, NM1, MQ('n'), G('n'), G('N')))
    SFR = 'sum_ n e. %s ( %s x. ( %s - %s ) )' % (FZ, MQ('n'), G('n'), G('N'))
    seq = st([body], 'sumeq2dv', '%s = %s' % (SINST, SFR))
    vFN, _ = mval(w, PH2, CS('t', 't'), 'N', nf['nn'], sumbody=True)
    fN1eq = st([st([npc], 'fveq2d', '( %s ` %s ) = ( %s ` N )' % (MF, NM1, MF)), vFN], 'eqtrd', '( %s ` %s ) = %s' % (MF, NM1, CS('N', 'N')))
    lhs = st([st([seq, st([fN1eq], 'oveq2d', '( %s x. ( %s ` %s ) ) = ( %s x. %s )' % (CX('N'), MF, NM1, CX('N'), CS('N', 'N')))], 'oveq12d',
                 '( %s - ( %s x. ( %s ` %s ) ) ) = ( %s - ( %s x. %s ) )' % (SINST, CX('N'), MF, NM1, SFR, CX('N'), CS('N', 'N')))], 'fveq2d',
             '( abs ` ( %s - ( %s x. ( %s ` %s ) ) ) ) = ( abs ` ( %s - ( %s x. %s ) ) )' % (SINST, CX('N'), MF, NM1, SFR, CX('N'), CS('N', 'N')))
    vR1, _ = mval(w, PH2, R('t'), '1', onenn)
    rhs = st([st([vR1], 'oveq1d', '( ( %s ` 1 ) - %s ) = ( %s - %s )' % (MR, CX('N'), R('1'), CX('N')))], 'oveq2d',
             '( %s x. ( ( %s ` 1 ) - %s ) ) = ( %s x. ( %s - %s ) )' % (M113, MR, CX('N'), M113, R('1'), CX('N')))
    w.qed([abel, lhs, rhs], '3brtr3d', STATEMENTS['bvmchkslem2'])
    return w


def bvmchks2():
    w = W('bvmchks2', 'The sigma extension of RZA Lemma 3.1 for |_ Y >= 2: the Abel bound (bvmchkslem2) plus '
                      'the boundary term N ^c -u E C ( Y , N ) (bvmchk1), with r ( 1 ) <= h ( 1 ) = 1 + E log Y.')
    PH3 = '( %s /\\ %s e. ( ZZ>= ` 2 ) )' % (HYS, NY)
    st = mkst(w, PH3)
    hys = st([], 'simpl', HYS); ys = ysfacts(w, PH3, hys)
    nu = st([], 'simpr', '%s e. ( ZZ>= ` 2 )' % NY)
    nnn = sy(w, PH3, nu, 'eluz2nn', '%s e. NN' % NY)
    nre = st([nnn], 'nnred', '%s e. RR' % NY); nrp = st([nnn], 'nnrpd', '%s e. RR+' % NY)
    n2 = sy(w, PH3, nu, 'eluzle', '2 <_ %s' % NY)
    nley = sy(w, PH3, ys['yr'], 'flle', '%s <_ Y' % NY)
    c = cxfacts(w, PH3, nrp, ys['ner'], NY)
    N = NY
    SDp = 'sum_ n e. ( 1 ... ( %s - 1 ) ) ( %s x. ( %s - %s ) )' % (N, MQ('n'), G('n'), G(N))
    CXCS = '( %s x. %s )' % (CX(N), CS('Y', N)); CXCN = '( %s x. %s )' % (CX(N), CS(N, N))
    lem3 = st([bind(w, PH3, hys, nu, HYS, '%s e. ( ZZ>= ` 2 )' % N), w.inst('bvmchkslem3')], 'syl', '( %s - %s ) = ( %s - %s )' % (SUMY, CXCS, SDp, CXCN))
    lem2 = st([bind(w, PH3, hys, bind(w, PH3, nu, nley, '%s e. ( ZZ>= ` 2 )' % N, '%s <_ Y' % N), HYS, '( %s e. ( ZZ>= ` 2 ) /\\ %s <_ Y )' % (N, N)), w.inst('bvmchkslem2')], 'syl',
              '( abs ` ( %s - %s ) ) <_ ( %s x. ( %s - %s ) )' % (SDp, CXCN, M113, R('1'), CX(N)))
    chk = sy2(w, PH3, ys['yr'], ys['y1'], 'bvmchk1', '( abs ` %s ) <_ %s' % (CS('Y', N), M113))
    # r(1) <= h(1) = 1 + E log Y
    two = st([st([clo(w, '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2'), linarith(w, PH3, [n2, nley], '2 <_ Y', leaves={NY: nre, 'Y': ys['yr']})], 'eqbrtrd', '( 1 + 1 ) <_ Y')
    onenn = st([clo(w, '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    rf = st([bind(w, PH3, hys, bind(w, PH3, onenn, two, '1 e. NN', '( 1 + 1 ) <_ Y'), HYS, HK('1')), w.inst('bvrfirst')], 'syl', '%s <_ %s' % (R('1'), H('1')))
    nec = st([ys['ner']], 'recnd', '%s e. CC' % NE)
    cx1 = sy(w, PH3, nec, '1cxp', '%s = 1' % CX('1'))
    yc = st([ys['yr']], 'recnd', 'Y e. CC')
    d1 = st([st([st([yc], 'div1d', '( Y / 1 ) = Y')], 'fveq2d', '( log ` ( Y / 1 ) ) = ( log ` Y )')], 'oveq2d', '( %s x. ( log ` ( Y / 1 ) ) ) = ( %s x. ( log ` Y ) )' % (E, E))
    ELY = '( %s x. ( log ` Y ) )' % E
    ly = st([ys['yrp']], 'relogcld', '( log ` Y ) e. RR')
    elyr = st([ys['er'], ly], 'remulcld', '%s e. RR' % ELY)
    p1r = st([st([], '1red', '1 e. RR'), elyr], 'readdcld', '( 1 + %s ) e. RR' % ELY)
    h1 = st([st([cx1, st([d1], 'oveq2d', '( 1 + ( %s x. ( log ` ( Y / 1 ) ) ) ) = ( 1 + %s )' % (E, ELY))], 'oveq12d', '%s = ( 1 x. ( 1 + %s ) )' % (H('1'), ELY)),
             st([st([p1r], 'recnd', '( 1 + %s ) e. CC' % ELY)], 'mullidd', '( 1 x. ( 1 + %s ) ) = ( 1 + %s )' % (ELY, ELY))], 'eqtrd', '%s = ( 1 + %s )' % (H('1'), ELY))
    r1le = st([rf, h1], 'breqtrd', '%s <_ ( 1 + %s )' % (R('1'), ELY))
    # closures
    AN = '( %s /\\ n e. ( 1 ... %s ) )' % (PH3, N); sn = mkst(w, AN)
    nnnn = sy(w, AN, sn([], 'simpr', 'n e. ( 1 ... %s )' % N), 'elfznn', 'n e. NN')
    mfn = mqfacts(w, AN, nnnn, 'n'); kfn = kfacts(w, AN, nnnn, 'n')
    lgn = lgfacts(w, AN, lift(w, ys['yrp'], AN), kfn['rp'], 'n')
    nsr = sn([sn([kfn['rp'], sn([lift(w, ys['sr'], AN)], 'renegcld', '-u S e. RR')], 'rpcxpcld', '( n ^c -u S ) e. RR+')], 'rpred', '( n ^c -u S ) e. RR')
    termr = sn([sn([mfn['mur'], nsr], 'remulcld', '( %s x. ( n ^c -u S ) ) e. RR' % MU('n')), lgn['re']], 'remulcld', '%s e. RR' % TERM('n'))
    sumr = st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % N), termr], 'fsumrecl', '%s e. RR' % SUMY); sumc = st([sumr], 'recnd', '%s e. CC' % SUMY)
    csyr, csyc = csfacts(w, PH3, ys['yrp'], N)
    cxcsr = st([c['re'], csyr], 'remulcld', '%s e. RR' % CXCS); cxcsc = st([cxcsr], 'recnd', '%s e. CC' % CXCS)
    D = '( %s - %s )' % (SUMY, CXCS)
    dr = st([sumr, cxcsr], 'resubcld', '%s e. RR' % D); dc = st([dr], 'recnd', '%s e. CC' % D)
    kf1 = kfacts(w, PH3, onenn, '1')
    g1 = gcl(w, PH3, ys, kf1['rp'], '1'); g2 = gcl(w, PH3, ys, kf1['p1rp'], '( 1 + 1 )'); el1 = ellfacts(w, PH3, kf1, '1')
    r1r = st([st([g1['gr'], g2['gr']], 'resubcld', '( %s - %s ) e. RR' % (G('1'), G('( 1 + 1 )'))), el1['rp']], 'rerpdivcld', '%s e. RR' % R('1'))
    # the triangle
    sumeq = st([st([sumc, cxcsc], 'npcand', '( %s + %s ) = %s' % (D, CXCS, SUMY))], 'eqcomd', '%s = ( %s + %s )' % (SUMY, D, CXCS))
    tri = st([st([sumeq], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s + %s ) )' % (SUMY, D, CXCS)), sy2(w, PH3, dc, cxcsc, 'abstri', '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (D, CXCS, D, CXCS))], 'eqbrtrd',
             '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (SUMY, D, CXCS))
    dle = st([st([st([lem3], 'eqcomd', '( %s - %s ) = %s' % (SDp, CXCN, D))], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (SDp, CXCN, D)), lem2], 'eqbrtrrd',
             '( abs ` %s ) <_ ( %s x. ( %s - %s ) )' % (D, M113, R('1'), CX(N)))
    acs = st([csyc], 'abscld', '( abs ` %s ) e. RR' % CS('Y', N))
    cl = Closure(w, PH3); m113r = cl.mem(M113, 'RR')
    cxle = st([st([st([c['cc'], csyc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CXCS, CX(N), CS('Y', N))),
                   st([st([c['re'], c['ge0']], 'absidd', '( abs ` %s ) = %s' % (CX(N), CX(N)))], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (CX(N), CS('Y', N), CX(N), CS('Y', N)))], 'eqtrd',
                  '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (CXCS, CX(N), CS('Y', N))),
               st([acs, m113r, c['re'], c['ge0'], chk], 'lemul2ad', '( %s x. ( abs ` %s ) ) <_ ( %s x. %s )' % (CX(N), CS('Y', N), CX(N), M113))], 'eqbrtrd',
              '( abs ` %s ) <_ ( %s x. %s )' % (CXCS, CX(N), M113))
    leaves = {'( abs ` %s )' % SUMY: st([sumc], 'abscld', '( abs ` %s ) e. RR' % SUMY), '( abs ` %s )' % D: st([dc], 'abscld', '( abs ` %s ) e. RR' % D),
              '( abs ` %s )' % CXCS: st([cxcsc], 'abscld', '( abs ` %s ) e. RR' % CXCS), CX(N): c['re'], R('1'): r1r, ELY: elyr}
    linarith(w, PH3, [tri, dle, cxle, r1le], '( abs ` %s ) <_ %s' % (SUMY, BOUND), leaves=leaves, name='qed')
    return w


def bvmchks1():
    w = W('bvmchks1', 'The sigma extension of RZA Lemma 3.1 for |_ Y = 1: the sum is log Y < 1.')
    PH4 = '( %s /\\ %s = 1 )' % (HYS, NY)
    st = mkst(w, PH4)
    hys = st([], 'simpl', HYS); ys = ysfacts(w, PH4, hys)
    n1 = st([], 'simpr', '%s = 1' % NY)
    rng = st([st([n1], 'oveq2d', '( 1 ... %s ) = ( 1 ... 1 )' % NY)], 'sumeq1d', '%s = sum_ n e. ( 1 ... 1 ) %s' % (SUMY, TERM('n')))
    idn = w.s([], 'id', '( n = 1 -> n = 1 )')
    sub, B = w.congr(TERM('n'), {'n': '1'}, 'n = 1', {'n': idn})
    f1 = w.s([sub], 'fsum1', '( ( 1 e. ZZ /\\ %s e. CC ) -> sum_ n e. ( 1 ... 1 ) %s = %s )' % (B, TERM('n'), B))
    yc = st([ys['yr']], 'recnd', 'Y e. CC')
    nsc = st([st([ys['sr']], 'renegcld', '-u S e. RR')], 'recnd', '-u S e. CC')
    e1 = st([st([clo(w, 'muone', '( mmu ` 1 ) = 1')], 'a1i', '( mmu ` 1 ) = 1'), sy(w, PH4, nsc, '1cxp', '( 1 ^c -u S ) = 1')], 'oveq12d', '( ( mmu ` 1 ) x. ( 1 ^c -u S ) ) = ( 1 x. 1 )')
    e2 = st([e1, st([clo(w, '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')], 'eqtrd', '( ( mmu ` 1 ) x. ( 1 ^c -u S ) ) = 1')
    e3 = st([st([yc], 'div1d', '( Y / 1 ) = Y')], 'fveq2d', '( log ` ( Y / 1 ) ) = ( log ` Y )')
    ly = st([ys['yrp']], 'relogcld', '( log ` Y ) e. RR'); lyc = st([ly], 'recnd', '( log ` Y ) e. CC')
    beq = st([st([e2, e3], 'oveq12d', '%s = ( 1 x. ( log ` Y ) )' % B), st([lyc], 'mullidd', '( 1 x. ( log ` Y ) ) = ( log ` Y )')], 'eqtrd', '%s = ( log ` Y )' % B)
    bc = st([beq, lyc], 'eqeltrd', '%s e. CC' % B)
    s1 = st([st([clo(w, '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), bc, f1], 'syl2anc',
            'sum_ n e. ( 1 ... 1 ) %s = %s' % (TERM('n'), B))
    sumeq = eqtr(w, PH4, [rng, s1, beq], None)
    lg0 = sy2(w, PH4, ys['yr'], ys['y1'], 'logge0', '0 <_ ( log ` Y )')
    abseq = st([st([sumeq], 'fveq2d', '( abs ` %s ) = ( abs ` ( log ` Y ) )' % SUMY), st([ly, lg0], 'absidd', '( abs ` ( log ` Y ) ) = ( log ` Y )')], 'eqtrd', '( abs ` %s ) = ( log ` Y )' % SUMY)
    lgle = sy2(w, PH4, ys['yr'], ys['y1'], 'extrwlogle', '( log ` Y ) <_ ( Y - 1 )')
    flt = sy(w, PH4, ys['yr'], 'flltp1', 'Y < ( %s + 1 )' % NY)
    ELY = '( %s x. ( log ` Y ) )' % E
    elyr = st([ys['er'], ly], 'remulcld', '%s e. RR' % ELY)
    ely0 = st([ys['er'], ly, ys['e0'], lg0], 'mulge0d', '0 <_ %s' % ELY)
    nyr = sy(w, PH4, ys['yr'], 'reflcl', '%s e. RR' % NY)
    bnd = linarith(w, PH4, [lgle, flt, n1, ely0], '( log ` Y ) <_ %s' % BOUND, leaves={'( log ` Y )': ly, 'Y': ys['yr'], NY: nyr, ELY: elyr})
    w.qed([abseq, bnd], 'eqbrtrd', STATEMENTS['bvmchks1'])
    return w


def bvmchks():
    w = W('bvmchks', 'The sigma extension of RZA Lemma 3.1 (Lean abs_mCheck_sigma_le): for Y >= 1 and S >= 1, '
                     '| sum_ n <= Y mmu n n ^c -u S log ( Y / n ) | <= ( 11 / 3 ) ( 1 + ( S - 1 ) log Y ). Proved by '
                     'discrete second-order Abel summation against C ( x , x ) with the chord bounds of the kernel; '
                     'no integral enters.')
    st = mkst(w, HYS)
    hy = st([], 'simpl', HY)
    yr = st([hy], 'simpld', 'Y e. RR'); y1 = st([hy], 'simprd', '1 <_ Y')
    nnn = sy2(w, HYS, yr, y1, 'flge1nn', '%s e. NN' % NY)
    bi = st([clo(w, 'elnn1uz2', '( %s e. NN <-> ( %s = 1 \\/ %s e. ( ZZ>= ` 2 ) ) )' % (NY, NY, NY))], 'a1i', '( %s e. NN <-> ( %s = 1 \\/ %s e. ( ZZ>= ` 2 ) ) )' % (NY, NY, NY))
    disj = st([nnn, bi], 'mpbid', '( %s = 1 \\/ %s e. ( ZZ>= ` 2 ) )' % (NY, NY))
    c1 = w.s([], 'bvmchks1', STATEMENTS['bvmchks1']); c2 = w.s([], 'bvmchks2', STATEMENTS['bvmchks2'])
    w.qed([c1, c2, disj], 'mpjaodan', STATEMENTS['bvmchks'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvmchkslem1', 'bvmchkslem3', 'bvmchkslem2', 'bvmchks2', 'bvmchks1', 'bvmchks']:
        globals()[f]().run()
