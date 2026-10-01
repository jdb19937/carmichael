"""Sortie Z5a, section D: the majorant, the coefficients, the detector, and the diagonal at the Detector summand
(Detector.lean 1360-1376, ZeroDensity.lean 119-176, 350-363, 385-487)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5alib import *
from cl import Closure, lift
import lin

BMB = lambda p, q: '( n e. NN |-> ( ( ( 1 / n ) x. ( ( %s ` n ) ^ 2 ) ) x. ( %s ` n ) ) )' % (p, q)
CDB = lambda u, v: ('( n e. NN |-> if ( ( 1st ` %s ) < n , ( ( ( ( ( ( 1st ` %s ) bvA ( 2nd ` %s ) ) ` n ) x. ( ( 1st ` ( 1st ` %s ) ) ` n ) ) x. '
                    '( exp ` ( -u n / ( 2nd ` ( 1st ` %s ) ) ) ) ) x. ( n ^c -u ( 2nd ` %s ) ) ) , 0 ) )' % (u, u, u, v, v, v))
FDB = lambda u, v: ('( s e. CC |-> sum_ n e. NN if ( ( 1st ` %s ) < n , ( ( ( ( ( ( ( 1st ` %s ) bvA ( 2nd ` %s ) ) ` n ) x. ( ( 1st ` ( 1st ` %s ) ) ` n ) ) x. '
                    '( exp ` ( -u n / ( 2nd ` ( 1st ` %s ) ) ) ) ) x. ( ( 2nd ` %s ) ` n ) ) x. ( n ^c -u s ) ) , 0 ) )' % (u, u, u, v, v, v))


def z5bmajval():
    w = W('z5bmajval', "Value of the Halasz majorant (Lean bMaj, Detector.lean 1361): ( ( P bMaj W ) ` K ) = K ^ -1 P ( K ) ^ 2 W ( K ).")
    ante = '( ( P e. V /\\ W e. U ) /\\ K e. NN )'
    st = mkst(w, ante)
    e1 = cg(w, BMB('p', 'w'), 'p', 'P')
    e2 = cg(w, BMB('P', 'w'), 'w', 'W')
    df = w.s([], 'df-bmaj', 'bMaj = ( p e. _V , w e. _V |-> %s )' % BMB('p', 'w'))
    ex = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % BMB('P', 'W'))
    ov = w.s([e1, e2, df, ex], 'ovmpo', '( ( P e. _V /\\ W e. _V ) -> ( P bMaj W ) = %s )' % BMB('P', 'W'))
    both = st([st([st([], 'simpll', 'P e. V')], 'elexd', 'P e. _V'), st([st([], 'simplr', 'W e. U')], 'elexd', 'W e. _V')], 'jca', '( P e. _V /\\ W e. _V )')
    pv = st([both, ov], 'syl', '( P bMaj W ) = %s' % BMB('P', 'W'))
    val, v = mpv(w, ante, 'n', 'NN', '( ( ( 1 / n ) x. ( ( P ` n ) ^ 2 ) ) x. ( W ` n ) )', 'K', st([], 'simpr', 'K e. NN'))
    w.qed([st([pv], 'fveq1d', '( ( P bMaj W ) ` K ) = ( %s ` K )' % BMB('P', 'W')), val], 'eqtrd', STATEMENTS['z5bmajval'])
    return w


def pairval(w, ante, dfl, OPN, B, U, V, A1, A2, mk, both):
    """( ante -> ( A1 OPN A2 ) = B(A1, A2) ) for an mpo over _V x _V (the `$d`-safe congruences of cg)"""
    e1 = cg(w, B('u', 'v'), 'u', A1)
    e2 = cg(w, B(A1, 'v'), 'v', A2)
    df = w.s([], dfl, '%s = ( u e. _V , v e. _V |-> %s )' % (OPN, B('u', 'v')))
    ov = w.s([e1, e2, df, mk], 'ovmpo', '( ( %s e. _V /\\ %s e. _V ) -> ( %s %s %s ) = %s )' % (A1, A2, A1, OPN, A2, B(A1, A2)))
    return w.s([both, ov], 'syl', '( %s -> ( %s %s %s ) = %s )' % (ante, A1, OPN, A2, B(A1, A2)))


def comprules(w, ante, sa, sb, sp, sx, s3, A, B, P, X, S):
    """rewrite rules for the components of <. A , B >. and <. P , X , S >."""
    st = mkst(w, ante)
    OP = '<. %s , %s >.' % (A, B); OT = '<. %s , %s , %s >.' % (P, X, S)
    r = {}
    r['( 1st ` %s )' % OP] = (A, st([sa, sb, w.inst('op1stg')], 'syl2anc', '( 1st ` %s ) = %s' % (OP, A)))
    r['( 2nd ` %s )' % OP] = (B, st([sa, sb, w.inst('op2ndg')], 'syl2anc', '( 2nd ` %s ) = %s' % (OP, B)))
    r['( 1st ` ( 1st ` %s ) )' % OT] = (P, st([sp, sx, s3, w.inst('ot1stg')], 'syl3anc', '( 1st ` ( 1st ` %s ) ) = %s' % (OT, P)))
    r['( 2nd ` ( 1st ` %s ) )' % OT] = (X, st([sp, sx, s3, w.inst('ot2ndg')], 'syl3anc', '( 2nd ` ( 1st ` %s ) ) = %s' % (OT, X)))
    r['( 2nd ` %s )' % OT] = (S, st([s3, w.inst('ot3rdg')], 'syl', '( 2nd ` %s ) = %s' % (OT, S)))
    return r


def z5cdetval():
    w = W('z5cdetval', "Value of the detector coefficients (Lean cDet, Detector.lean 1366): ( ( <. A , B >. cDet <. P , X , S >. ) ` K ) is "
                       "a ( K ) P ( K ) e ^ ( - K / X ) K ^c -u S for A < K, else 0 (a = ( A bvA B )).")
    ante = '( ( ( A e. U /\\ B e. V ) /\\ ( P e. W /\\ X e. T /\\ S e. Z ) ) /\\ K e. NN )'
    st = mkst(w, ante)
    sa = st([], 'simplll', 'A e. U'); sb = st([], 'simpllr', 'B e. V')
    h3 = st([], 'simplr', '( P e. W /\\ X e. T /\\ S e. Z )')
    sp = st([h3], 'simp1d', 'P e. W'); sx = st([h3], 'simp2d', 'X e. T'); s3 = st([h3], 'simp3d', 'S e. Z')
    OP = '<. A , B >.'; OT = '<. P , X , S >.'
    both = st([a1(w, ante, w.s([], 'opex', '%s e. _V' % OP), '%s e. _V' % OP),
               a1(w, ante, w.s([], 'otex', '%s e. _V' % OT), '%s e. _V' % OT)], 'jca', '( %s e. _V /\\ %s e. _V )' % (OP, OT))
    mk = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % CDB(OP, OT))
    pv = pairval(w, ante, 'df-cdet', 'cDet', CDB, None, None, OP, OT, mk, both)
    body = CDB(OP, OT)[len('( n e. NN |-> '):-2]
    val, v = mpv(w, ante, 'n', 'NN', body, 'K', st([], 'simpr', 'K e. NN'))
    rules = comprules(w, ante, sa, sb, sp, sx, s3, 'A', 'B', 'P', 'X', 'S')
    rw, new = w.rewrite(v, rules, ante)
    w.qed([eqtr(w, ante, [st([pv], 'fveq1d', '( ( %s cDet %s ) ` K ) = ( %s ` K )' % (OP, OT, CDB(OP, OT))), val], None), rw], 'eqtrd', STATEMENTS['z5cdetval'])
    return w


def z5fdetval():
    w = W('z5fdetval', "Value of the zero detector (Lean Fdet, Detector.lean 1373): ( ( <. A , B >. FDet <. P , X , C >. ) ` S ) is the series "
                       "sum_ ( n > A ) a ( n ) P ( n ) e ^ ( - n / X ) C ( n ) n ^c -u S (a = ( A bvA B ), C the character on NN).")
    ante = '( ( ( A e. U /\\ B e. V ) /\\ ( P e. W /\\ X e. T /\\ C e. Z ) ) /\\ S e. CC )'
    st = mkst(w, ante)
    sa = st([], 'simplll', 'A e. U'); sb = st([], 'simpllr', 'B e. V')
    h3 = st([], 'simplr', '( P e. W /\\ X e. T /\\ C e. Z )')
    sp = st([h3], 'simp1d', 'P e. W'); sx = st([h3], 'simp2d', 'X e. T'); s3 = st([h3], 'simp3d', 'C e. Z')
    OP = '<. A , B >.'; OT = '<. P , X , C >.'
    both = st([a1(w, ante, w.s([], 'opex', '%s e. _V' % OP), '%s e. _V' % OP), a1(w, ante, w.s([], 'otex', '%s e. _V' % OT), '%s e. _V' % OT)], 'jca',
              '( %s e. _V /\\ %s e. _V )' % (OP, OT))
    mk = w.s([w.s([], 'cnex', 'CC e. _V')], 'mptex', '%s e. _V' % FDB(OP, OT))
    pv = pairval(w, ante, 'df-fdet', 'FDet', FDB, None, None, OP, OT, mk, both)
    body = FDB(OP, OT)[len('( s e. CC |-> '):-2]
    bS = body.replace('-u s )', '-u S )')
    val, v = mpv(w, ante, 's', 'CC', body, 'S', st([], 'simpr', 'S e. CC'), exs=a1(w, ante, w.s([], 'sumex', '%s e. _V' % bS), '%s e. _V' % bS))
    rules = comprules(w, ante, sa, sb, sp, sx, s3, 'A', 'B', 'P', 'X', 'C')
    rw, new = w.rewrite(v, rules, ante)
    w.qed([eqtr(w, ante, [st([pv], 'fveq1d', '( ( %s FDet %s ) ` S ) = ( %s ` S )' % (OP, OT, FDB(OP, OT))), val], None), rw], 'eqtrd', STATEMENTS['z5fdetval'])
    return w


def detfacts(w, ante, hz, nv, knn):
    """the frozen-parameter facts under ante: hz ( ante -> HZ2 ), nv ( ante -> N e. V ), knn ( ante -> K e. NN )"""
    st = mkst(w, ante)
    fw = st([hz, w.inst('z5fwin')], 'syl', '( ( 1 <_ %s /\\ %s < %s ) /\\ ( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s ) )' % (Z1, Z1, Z2, M0, ELLD, Z1, Z1, XP))
    f1 = st([fw], 'simpld', '( 1 <_ %s /\\ %s < %s )' % (Z1, Z1, Z2)); f2 = st([fw], 'simprd', '( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s )' % (M0, ELLD, Z1, Z1, XP))
    z11 = st([f1], 'simpld', '1 <_ %s' % Z1); z12 = st([f1], 'simprd', '%s < %s' % (Z1, Z2))
    mz = st([f2], 'simpld', '( %s x. ( exp ` %s ) ) <_ %s' % (M0, ELLD, Z1)); zx = st([f2], 'simprd', '( 2 x. %s ) <_ %s' % (Z1, XP))
    dr = st([hz], 'simp1d', 'D e. RR'); d1 = st([hz], 'simp2d', '1 < D'); l2 = st([hz], 'simp3d', '2 <_ ( log ` D )')
    drp = st([dr, lin.linarith(w, ante, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1, Z2, Z1, Z2))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2)
    z1r = st([z1rp], 'rpred', '%s e. RR' % Z1)
    xprp = st([drp, litr(w, ante, '( 6 / 5 )')], 'rpcxpcld', '%s e. RR+' % XP); xpr = st([xprp], 'rpred', '%s e. RR' % XP)
    m0rp = st([drp, litr(w, ante, '( 3 / 5 )')], 'rpcxpcld', '%s e. RR+' % M0)
    lr = st([drp], 'relogcld', '( log ` D ) e. RR')
    lgt = lin.linarith(w, ante, [l2], '0 < ( log ` D )', leaves={'( log ` D )': lr})
    hrp = st([litr(w, ante, '( 1 / ; ; 1 0 0 )'), litle(w, ante, '0', '( 1 / ; ; 1 0 0 )', strict=True)], 'elrpd', '( 1 / ; ; 1 0 0 ) e. RR+')
    ellrp = st([hrp, st([lr, lgt], 'elrpd', '( log ` D ) e. RR+')], 'rpmulcld', '%s e. RR+' % ELLD)
    ML = '( %s x. ( exp ` %s ) )' % (M0, ELLD)
    mlr = st([st([m0rp, st([st([ellrp], 'rpred', '%s e. RR' % ELLD)], 'rpefcld', '( exp ` %s ) e. RR+' % ELLD)], 'rpmulcld', '%s e. RR+' % ML)], 'rpred', '%s e. RR' % ML)
    zlx = lin.linarith(w, ante, [zx, z11], '%s < %s' % (Z1, XP), leaves={Z1: z1r, XP: xpr})
    mlx = lin.linarith(w, ante, [mz, zlx], '%s < %s' % (ML, XP), leaves={ML: mlr, Z1: z1r, XP: xpr})
    rpv = w.s([], 'ovex', '%s e. _V' % RP)
    pkr = st([nv, a1(w, ante, rpv, '%s e. _V' % RP), knn, w.inst('z5pfunre')], 'syl21anc', '( %s ` K ) e. RR' % PF)
    wpos = st([st([m0rp, ellrp], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (M0, ELLD)), st([xpr, mlx], 'jca', '( %s e. RR /\\ %s < %s )' % (XP, ML, XP)), knn,
               w.inst('z5wpos')], 'syl21anc', '0 < ( %s ` K )' % WF)
    return dict(z11=z11, z12=z12, mz=mz, zx=zx, dr=dr, d1=d1, drp=drp, z1rp=z1rp, z2rp=z2rp, z1r=z1r, xprp=xprp, xpr=xpr, m0rp=m0rp, ellrp=ellrp, pkr=pkr,
                wpos=wpos, zlx=zlx, mlx=mlx)


def detvals(w, ante, f, nv, tr, knn):
    """values at K of the majorant and the coefficients at the frozen parameters, with their closures"""
    st = mkst(w, ante)
    pfv = a1(w, ante, w.s([], 'ovex', '%s e. _V' % PF), '%s e. _V' % PF)
    wfv = a1(w, ante, w.s([], 'fvex', '%s e. _V' % WF), '%s e. _V' % WF)
    PK = '( %s ` K )' % PF; WK = '( %s ` K )' % WF
    bv = st([pfv, wfv, knn, w.inst('z5bmajval')], 'syl21anc', '( %s ` K ) = %s' % (BM, BMV(PF, WF, 'K')))
    h = st([st([f['z1rp'], f['z2rp']], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (Z1, Z2)), st([pfv, f['xprp'], tr], '3jca', '( %s e. _V /\\ %s e. RR+ /\\ T e. RR )' % (PF, XP))],
           'jca', '( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ %s e. RR+ /\\ T e. RR ) )' % (Z1, Z2, PF, XP))
    cv = st([st([h, knn], 'jca', '( ( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ %s e. RR+ /\\ T e. RR ) ) /\\ K e. NN )' % (Z1, Z2, PF, XP)), w.inst('z5cdetval')], 'syl',
            '( %s ` K ) = %s' % (CD, CDV(Z1, Z2, PF, XP, 'T', 'K')))
    krp = st([knn], 'nnrpd', 'K e. RR+')
    E = '( exp ` ( -u K / %s ) )' % XP
    erp = st([st([st([st([krp], 'rpred', 'K e. RR')], 'renegcld', '-u K e. RR'), f['xprp']], 'rerpdivcld', '( -u K / %s ) e. RR' % XP)], 'rpefcld', '%s e. RR+' % E)
    bar = st([st([f['dr'], f['d1']], 'jca', '( D e. RR /\\ 1 < D )'), knn, w.inst('zdbvare')], 'syl2anc', '%s e. RR' % BA('K'))
    KT = '( K ^c -u T )'
    ktrp = st([krp, st([tr], 'renegcld', '-u T e. RR')], 'rpcxpcld', '%s e. RR+' % KT)
    CT = CDT(Z1, Z2, PF, XP, 'T', 'K')
    ctr = st([st([st([bar, f['pkr']], 'remulcld', '( %s x. %s ) e. RR' % (BA('K'), PK)), st([erp], 'rpred', '%s e. RR' % E)], 'remulcld',
                 '( ( %s x. %s ) x. %s ) e. RR' % (BA('K'), PK, E)), st([ktrp], 'rpred', '%s e. RR' % KT)], 'remulcld', '%s e. RR' % CT)
    return dict(bv=bv, cv=cv, krp=krp, E=E, erp=erp, bar=bar, ktrp=ktrp, CT=CT, ctr=ctr, PK=PK, WK=WK)



def avre2(w, ante, ar, lrp, kr, a, L, K):
    """( ante -> AV(a,L,K) e. RR ) from a e. RR (ar), L e. RR+, K e. RR"""
    st = mkst(w, ante)
    lr = st([lrp], 'rpred', '%s e. RR' % L)
    B = '( %s + %s )' % (a, L)
    br = st([ar, lr], 'readdcld', '%s e. RR' % B)
    ab = lin.linarith(w, ante, [st([lrp], 'rpgt0d', '0 < %s' % L)], '%s <_ %s' % (a, B), leaves={a: ar, L: lr})
    O = '( %s (,) %s )' % (a, B)
    I = 'S. %s %s _d t' % (O, WG(K))
    dp = st([ab], 'ditgpos', '%s = %s' % (DI(a, L, K), I))
    ir = st([st([ar, br, kr, w.inst('z5wibl')], 'syl21anc', '( ( t e. %s |-> %s ) e. L^1 /\\ %s e. RR )' % (O, WG(K), I))], 'simprd', '%s e. RR' % I)
    dr = st([dp, ir], 'eqeltrd', '%s e. RR' % DI(a, L, K))
    return st([st([st([lrp], 'rpreccld', '( 1 / %s ) e. RR+' % L)], 'rpred', '( 1 / %s ) e. RR' % L), dr], 'remulcld', '%s e. RR' % AV(a, L, K))


def wvre(w, ante, mrp, xrp, lrp, knn, M=M0, X=XP, L=ELLD, K='K'):
    """( ante -> ( ( WWin ` <. M , X , L >. ) ` K ) e. RR )"""
    st = mkst(w, ante)
    WVK = '( %s ` %s )' % (WW(M, X, L), K)
    wv = st([mrp, xrp, lrp, knn, w.inst('z5wwinval')], 'syl31anc', '%s = %s' % (WVK, WBODY(M, X, L, K)))
    kr = st([knn], 'nnred', '%s e. RR' % K)
    LX = '( log ` %s )' % X; LM = '( log ` %s )' % M
    ax = avre2(w, ante, st([xrp], 'relogcld', '%s e. RR' % LX), lrp, kr, LX, L, K)
    am = avre2(w, ante, st([mrp], 'relogcld', '%s e. RR' % LM), lrp, kr, LM, L, K)
    return st([wv, st([ax, am], 'resubcld', '%s e. RR' % WBODY(M, X, L, K))], 'eqeltrd', '%s e. RR' % WVK)


def wkfacts(w, ante, f, knn, WK):
    st = mkst(w, ante)
    return wvre(w, ante, f['m0rp'], f['xprp'], f['ellrp'], knn)


def z5bmaj0():
    w = W('z5bmaj0', "Lean bMaj_nonneg (ZeroDensity.lean 351): b_K >_ 0 at the frozen parameters (W ( K ) > 0, Lean Wwin_pos).")
    ante = '( ( %s /\\ N e. V ) /\\ K e. NN )' % HZ2
    st = mkst(w, ante)
    hz = st([], 'simpll', HZ2); nv = st([], 'simplr', 'N e. V'); knn = st([], 'simpr', 'K e. NN')
    f = detfacts(w, ante, hz, nv, knn)
    pfv = a1(w, ante, w.s([], 'ovex', '%s e. _V' % PF), '%s e. _V' % PF)
    wfv = a1(w, ante, w.s([], 'fvex', '%s e. _V' % WF), '%s e. _V' % WF)
    PK = '( %s ` K )' % PF; WK = '( %s ` K )' % WF
    bv = st([pfv, wfv, knn, w.inst('z5bmajval')], 'syl21anc', '( %s ` K ) = %s' % (BM, BMV(PF, WF, 'K')))
    wkr = wvre(w, ante, f['m0rp'], f['xprp'], f['ellrp'], knn)
    rk = st([knn], 'nnrecred', '( 1 / K ) e. RR')
    rk0 = st([st([st([knn], 'nnrpd', 'K e. RR+')], 'rpreccld', '( 1 / K ) e. RR+')], 'rpge0d', '0 <_ ( 1 / K )')
    p2 = st([f['pkr']], 'resqcld', '( %s ^ 2 ) e. RR' % PK); p20 = st([f['pkr']], 'sqge0d', '0 <_ ( %s ^ 2 )' % PK)
    X = '( ( 1 / K ) x. ( %s ^ 2 ) )' % PK
    x0 = st([rk, p2, rk0, p20], 'mulge0d', '0 <_ %s' % X)
    b0 = st([st([rk, p2], 'remulcld', '%s e. RR' % X), wkr, x0, st([f['wpos']], 'ltled', '0 <_ %s' % WK)], 'mulge0d', '0 <_ %s' % BMV(PF, WF, 'K'))
    w.qed([b0, bv], 'breqtrrd', STATEMENTS['z5bmaj0'])
    return w


def dsetup(w, ante):
    st = mkst(w, ante)
    hz = st([], 'simpll', HZ2); nv = st([], 'simplr', 'N e. V'); tr = st([], 'simprl', 'T e. RR'); knn = st([], 'simprr', 'K e. NN')
    f = detfacts(w, ante, hz, nv, knn)
    v = detvals(w, ante, f, nv, tr, knn)
    b0 = st([st([hz, nv], 'jca', '( %s /\\ N e. V )' % HZ2), knn, w.inst('z5bmaj0')], 'syl2anc', '0 <_ ( %s ` K )' % BM)
    wkr = wvre(w, ante, f['m0rp'], f['xprp'], f['ellrp'], knn)
    rk = st([knn], 'nnrecred', '( 1 / K ) e. RR')
    PK = v['PK']; WK = v['WK']
    bvr = st([st([rk, st([f['pkr']], 'resqcld', '( %s ^ 2 ) e. RR' % PK)], 'remulcld', '( ( 1 / K ) x. ( %s ^ 2 ) ) e. RR' % PK), wkr], 'remulcld',
             '%s e. RR' % BMV(PF, WF, 'K'))
    bmr = st([v['bv'], bvr], 'eqeltrd', '( %s ` K ) e. RR' % BM)
    cdr = st([v['cv'], st([v['ctr'], st([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % CDV(Z1, Z2, PF, XP, 'T', 'K'))], 'eqeltrd', '( %s ` K ) e. RR' % CD)
    return dict(hz=hz, nv=nv, tr=tr, knn=knn, f=f, v=v, b0=b0, wkr=wkr, bvr=bvr, bmr=bmr, cdr=cdr, rk=rk)


def z5cdt0():
    w = W('z5cdt0', "The Detector summand of Lemma 8.1, c_K ^ 2 / b_K with Lean's x / 0 = 0, is a nonnegative real (Lean hterm0 of sigma_diag_le).")
    ante = '( ( %s /\\ N e. V ) /\\ ( T e. RR /\\ K e. NN ) )' % HZ2
    st = mkst(w, ante)
    d = dsetup(w, ante)
    BK = '( %s ` K )' % BM; CK = '( %s ` K )' % CD
    phi = '%s = 0' % BK
    Q = '( ( %s ^ 2 ) / %s )' % (CK, BK)
    a = '( %s /\\ %s )' % (ante, phi); b = '( %s /\\ -. %s )' % (ante, phi)
    sa = mkst(w, a); sb = mkst(w, b)
    bne = sb([sb([], 'simpr', '-. %s' % phi)], 'neqned', '%s =/= 0' % BK)
    qr = sb([sb([lift(w, d['cdr'], b)], 'resqcld', '( %s ^ 2 ) e. RR' % CK), lift(w, d['bmr'], b), bne], 'redivcld', '%s e. RR' % Q)
    re = st([sa([], '0red', '0 e. RR'), qr], 'ifclda', '%s e. RR' % QT('K'))
    ga = sa([sa([sa([], '0red', '0 e. RR')], 'leidd', '0 <_ 0'), ift(w, a, phi, '0', Q)], 'breqtrrd', '0 <_ %s' % QT('K'))
    bgt = sb([sb([lift(w, d['b0'], b), bne], 'jca', '( 0 <_ %s /\\ %s =/= 0 )' % (BK, BK)),
              sb([sb([], '0red', '0 e. RR'), lift(w, d['bmr'], b)], 'ltlend', '( 0 < %s <-> ( 0 <_ %s /\\ %s =/= 0 ) )' % (BK, BK, BK))], 'mpbird', '0 < %s' % BK)
    q0 = sb([sb([lift(w, d['cdr'], b)], 'resqcld', '( %s ^ 2 ) e. RR' % CK), sb([lift(w, d['bmr'], b), bgt], 'elrpd', '%s e. RR+' % BK),
             sb([lift(w, d['cdr'], b)], 'sqge0d', '0 <_ ( %s ^ 2 )' % CK)], 'divge0d', '0 <_ %s' % Q)
    gb = sb([q0, iff_(w, b, phi, '0', Q)], 'breqtrrd', '0 <_ %s' % QT('K'))
    ge = cases(w, ante, phi, ga, gb, '0 <_ %s' % QT('K'))
    w.qed([re, ge], 'jca', STATEMENTS['z5cdt0'])
    return w


def z5cdterm():
    w = W('z5cdterm', "Lean cDet_sq_div_bMaj_le_term (ZeroDensity.lean 121): c_K ^ 2 / b_K <_ 3 K ^c ( 1 - 2 T ) a ( K ) ^ 2 e ^ ( - K / X ) at the "
                      "frozen parameters, with Lean's x / 0 = 0 (the algebra is zdcdet; W ( K ) >_ e ^ ( - K / X ) / 3 is Lean Wwin_ge_third).")
    ante = '( ( %s /\\ N e. V ) /\\ ( T e. RR /\\ K e. NN ) )' % HZ2
    st = mkst(w, ante)
    d = dsetup(w, ante); f = d['f']; v = d['v']
    BK = '( %s ` K )' % BM; CK = '( %s ` K )' % CD; PK = v['PK']; WK = v['WK']; E = v['E']; CT = v['CT']
    RHS = TERM3('K')
    NC = '( K ^c ( 1 - ( 2 x. T ) ) )'
    ncrp = st([v['krp'], st([st([], '1red', '1 e. RR'), st([a1c(w, ante, '2re', '2 e. RR'), d['tr']], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld',
                            '( 1 - ( 2 x. T ) ) e. RR')], 'rpcxpcld', '%s e. RR+' % NC)
    B2_ = '( %s ^ 2 )' % BA('K')
    inner = '( ( %s x. %s ) x. %s )' % (NC, B2_, E)
    in1 = st([st([ncrp], 'rpred', '%s e. RR' % NC), st([v['bar']], 'resqcld', '%s e. RR' % B2_)], 'remulcld', '( %s x. %s ) e. RR' % (NC, B2_))
    in0 = st([st([ncrp], 'rpred', '%s e. RR' % NC), st([v['bar']], 'resqcld', '%s e. RR' % B2_), st([ncrp], 'rpge0d', '0 <_ %s' % NC), st([v['bar']], 'sqge0d', '0 <_ %s' % B2_)],
             'mulge0d', '0 <_ ( %s x. %s )' % (NC, B2_))
    inr = st([in1, st([v['erp']], 'rpred', '%s e. RR' % E)], 'remulcld', '%s e. RR' % inner)
    i0 = st([in1, st([v['erp']], 'rpred', '%s e. RR' % E), in0, st([v['erp']], 'rpge0d', '0 <_ %s' % E)], 'mulge0d', '0 <_ %s' % inner)
    rhs0 = st([a1c(w, ante, '3re', '3 e. RR'), inr, litle(w, ante, '0', '3'), i0],
              'mulge0d', '0 <_ %s' % RHS)
    phi = '%s = 0' % BK
    Q = '( ( %s ^ 2 ) / %s )' % (CK, BK)
    a = '( %s /\\ %s )' % (ante, phi); b = '( %s /\\ -. %s )' % (ante, phi)
    sa = mkst(w, a); sb = mkst(w, b)
    ta = sa([ift(w, a, phi, '0', Q), lift(w, rhs0, a)], 'eqbrtrd', '%s <_ %s' % (QT('K'), RHS))
    bne = sb([sb([], 'simpr', '-. %s' % phi)], 'neqned', '%s =/= 0' % BK)
    itb = iff_(w, b, phi, '0', Q)
    # P ( K ) =/= 0
    X = '( ( 1 / K ) x. ( %s ^ 2 ) )' % PK
    bvne = sb([lift(w, v['bv'], b), bne], 'eqnetrrd', '%s =/= 0' % BMV(PF, WF, 'K'))
    xr = sb([lift(w, d['rk'], b), sb([lift(w, f['pkr'], b)], 'resqcld', '( %s ^ 2 ) e. RR' % PK)], 'remulcld', '%s e. RR' % X)
    m1 = sb([bvne, sb([sb([xr], 'recnd', '%s e. CC' % X), sb([lift(w, d['wkr'], b)], 'recnd', '%s e. CC' % WK)], 'mulne0bd',
                     '( ( %s =/= 0 /\\ %s =/= 0 ) <-> %s =/= 0 )' % (X, WK, BMV(PF, WF, 'K')))], 'mpbird', '( %s =/= 0 /\\ %s =/= 0 )' % (X, WK))
    xne = sb([m1], 'simpld', '%s =/= 0' % X)
    m2 = sb([xne, sb([sb([lift(w, d['rk'], b)], 'recnd', '( 1 / K ) e. CC'), sb([sb([lift(w, f['pkr'], b)], 'resqcld', '( %s ^ 2 ) e. RR' % PK)], 'recnd',
                                                                                 '( %s ^ 2 ) e. CC' % PK)], 'mulne0bd', '( ( ( 1 / K ) =/= 0 /\\ ( %s ^ 2 ) =/= 0 ) <-> %s =/= 0 )' % (PK, X))],
            'mpbird', '( ( 1 / K ) =/= 0 /\\ ( %s ^ 2 ) =/= 0 )' % PK)
    p2ne = sb([m2], 'simprd', '( %s ^ 2 ) =/= 0' % PK)
    pne = sb([p2ne, sy(w, b, sb([lift(w, f['pkr'], b)], 'recnd', '%s e. CC' % PK), 'sqne0', '( ( %s ^ 2 ) =/= 0 <-> %s =/= 0 )' % (PK, PK))], 'mpbid', '%s =/= 0' % PK)
    # sub-case z1 < K
    phi2 = '%s < K' % Z1
    c = '( %s /\\ %s )' % (b, phi2); e_ = '( %s /\\ -. %s )' % (b, phi2)
    sc = mkst(w, c); se = mkst(w, e_)
    cK = sc([lift(w, v['cv'], c), ift(w, c, phi2, CT, '0')], 'eqtrd', '%s = %s' % (CK, CT))
    H3 = '( ( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. RR+ /\\ %s e. RR ) ) /\\ ( ( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s ) /\\ ( K e. NN /\\ %s < K ) ) )' % (
        M0, ELLD, Z1, XP, M0, ELLD, Z1, Z1, XP, Z1)
    hl = sc([sc([lift(w, f['m0rp'], c), lift(w, f['ellrp'], c)], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (M0, ELLD)),
             sc([lift(w, f['z1rp'], c), lift(w, f['xpr'], c)], 'jca', '( %s e. RR+ /\\ %s e. RR )' % (Z1, XP))], 'jca',
            '( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. RR+ /\\ %s e. RR ) )' % (M0, ELLD, Z1, XP))
    hr = sc([sc([lift(w, f['mz'], c), lift(w, f['zx'], c)], 'jca', '( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s )' % (M0, ELLD, Z1, Z1, XP)),
             sc([lift(w, d['knn'], c), sc([], 'simpr', phi2)], 'jca', '( K e. NN /\\ %s < K )' % Z1)], 'jca',
            '( ( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s ) /\\ ( K e. NN /\\ %s < K ) )' % (M0, ELLD, Z1, Z1, XP, Z1))
    th = sc([sc([hl, hr], 'jca', H3), w.inst('z5wthird')], 'syl', '( ( 1 / 3 ) x. %s ) <_ %s' % (E, WK))
    er = st([v['erp']], 'rpred', '%s e. RR' % E)
    e3 = lin.linarith(w, c, [th], '%s <_ ( 3 x. %s )' % (E, WK), leaves={E: lift(w, er, c), WK: lift(w, d['wkr'], c)})
    wrp = sc([lift(w, d['wkr'], c), lin.linarith(w, c, [th, sc([lift(w, v['erp'], c)], 'rpgt0d', '0 < %s' % E)], '0 < %s' % WK,
                                                 leaves={E: lift(w, er, c), WK: lift(w, d['wkr'], c)})], 'elrpd', '%s e. RR+' % WK)
    HC = ('( ( K e. NN /\\ T e. RR ) /\\ ( ( %s e. RR /\\ ( %s e. RR /\\ %s =/= 0 ) ) /\\ ( %s e. RR+ /\\ ( %s e. RR+ /\\ %s <_ ( 3 x. %s ) ) ) ) )'
          % (BA('K'), PK, PK, E, WK, E, WK))
    hc = sc([sc([lift(w, d['knn'], c), lift(w, d['tr'], c)], 'jca', '( K e. NN /\\ T e. RR )'),
             sc([sc([lift(w, v['bar'], c), sc([lift(w, f['pkr'], c), lift(w, pne, c)], 'jca', '( %s e. RR /\\ %s =/= 0 )' % (PK, PK))], 'jca',
                    '( %s e. RR /\\ ( %s e. RR /\\ %s =/= 0 ) )' % (BA('K'), PK, PK)),
                 sc([lift(w, v['erp'], c), sc([wrp, e3], 'jca', '( %s e. RR+ /\\ %s <_ ( 3 x. %s ) )' % (WK, E, WK))], 'jca',
                    '( %s e. RR+ /\\ ( %s e. RR+ /\\ %s <_ ( 3 x. %s ) ) )' % (E, WK, E, WK))], 'jca',
                '( ( %s e. RR /\\ ( %s e. RR /\\ %s =/= 0 ) ) /\\ ( %s e. RR+ /\\ ( %s e. RR+ /\\ %s <_ ( 3 x. %s ) ) ) )' % (BA('K'), PK, PK, E, WK, E, WK))], 'jca', HC)
    zc = sc([hc, w.inst('zdcdet')], 'syl', '( ( %s ^ 2 ) / %s ) <_ %s' % (CT, BMV(PF, WF, 'K'), RHS))
    qe = sc([sc([cK], 'oveq1d', '( %s ^ 2 ) = ( %s ^ 2 )' % (CK, CT)), lift(w, v['bv'], c)], 'oveq12d', '%s = ( ( %s ^ 2 ) / %s )' % (Q, CT, BMV(PF, WF, 'K')))
    tc = sc([qe, zc], 'eqbrtrd', '%s <_ %s' % (Q, RHS))
    # sub-case -. z1 < K: c_K = 0
    c0 = se([lift(w, v['cv'], e_), iff_(w, e_, phi2, CT, '0')], 'eqtrd', '%s = 0' % CK)
    s0 = se([se([c0], 'oveq1d', '( %s ^ 2 ) = ( 0 ^ 2 )' % CK), a1c(w, e_, 'sq0', '( 0 ^ 2 ) = 0')], 'eqtrd', '( %s ^ 2 ) = 0' % CK)
    q0 = se([se([s0], 'oveq1d', '%s = ( 0 / %s )' % (Q, BK)), se([se([lift(w, d['bmr'], e_)], 'recnd', '%s e. CC' % BK), lift(w, bne, e_)], 'div0d', '( 0 / %s ) = 0' % BK)],
            'eqtrd', '%s = 0' % Q)
    te = se([q0, lift(w, rhs0, e_)], 'eqbrtrd', '%s <_ %s' % (Q, RHS))
    qb = cases(w, b, phi2, tc, te, '%s <_ %s' % (Q, RHS))
    tb = sb([itb, qb], 'eqbrtrd', '%s <_ %s' % (QT('K'), RHS))
    cases(w, ante, phi, ta, tb, '%s <_ %s' % (QT('K'), RHS), name='qed')
    return w


def z5sigdiag():
    w = W('z5sigdiag', "Lean sigma_diag_le (ZeroDensity.lean 385) at the Detector summand: for log D >_ 200 and 99 / 100 <_ T <_ 1 the series "
                       "sum_ n c_n ^ 2 / b_n (Lean's x / 0 = 0) converges and is at most 10 ^ 9 X ^ ( 2 - 2 T ) (zdsigdiag with z5cdt0, z5cdterm).")
    ante = '( %s /\\ N e. V )' % H0
    st = mkst(w, ante)
    h0 = st([], 'simpl', H0)
    hz = st([h0], 'simpld', HZD); ht = st([h0], 'simprd', HT); nv = st([], 'simpr', 'N e. V')
    dr = st([hz], 'simp1d', 'D e. RR'); d1 = st([hz], 'simp2d', '1 < D'); l200 = st([hz], 'simp3d', '; ; 2 0 0 <_ ( log ` D )')
    drp = st([dr, lin.linarith(w, ante, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    lr = st([drp], 'relogcld', '( log ` D ) e. RR')
    l2 = lin.linarith(w, ante, [l200], '2 <_ ( log ` D )', leaves={'( log ` D )': lr})
    hz2 = st([dr, d1, l2], '3jca', HZ2)
    tr = st([ht], 'simpld', 'T e. RR')
    FQ = '( k e. NN |-> %s )' % QT('k')
    a = '( %s /\\ n e. NN )' % ante
    sa = mkst(w, a)
    nn = sa([], 'simpr', 'n e. NN')
    fv, _v = mpv(w, a, 'k', 'NN', QT('k'), 'n', nn)
    HH = '( ( %s /\\ N e. V ) /\\ ( T e. RR /\\ n e. NN ) )' % HZ2
    hh = sa([sa([lift(w, hz2, a), lift(w, nv, a)], 'jca', '( %s /\\ N e. V )' % HZ2), sa([lift(w, tr, a), nn], 'jca', '( T e. RR /\\ n e. NN )')], 'jca', HH)
    c0 = sa([hh, w.inst('z5cdt0')], 'syl', '( %s e. RR /\\ 0 <_ %s )' % (QT('n'), QT('n')))
    ct = sa([hh, w.inst('z5cdterm')], 'syl', '%s <_ %s' % (QT('n'), TERM3('n')))
    h3 = sa([fv, sa([c0], 'simpld', '%s e. RR' % QT('n'))], 'eqeltrd', '( %s ` n ) e. RR' % FQ)
    h4 = sa([sa([c0], 'simprd', '0 <_ %s' % QT('n')), fv], 'breqtrrd', '0 <_ ( %s ` n )' % FQ)
    h5 = sa([fv, ct], 'eqbrtrd', '( %s ` n ) <_ %s' % (FQ, TERM3('n')))
    K = '( %s x. %s )' % (C12, XB)
    zs = st([hz, ht, h3, h4, h5], 'zdsigdiag', '( seq 1 ( + , %s ) e. dom ~~> /\\ sum_ n e. NN ( %s ` n ) <_ %s )' % (FQ, FQ, K))
    se = st([fv], 'sumeq2dv', 'sum_ n e. NN ( %s ` n ) = sum_ n e. NN %s' % (FQ, QT('n')))
    sl = st([se, st([zs], 'simprd', 'sum_ n e. NN ( %s ` n ) <_ %s' % (FQ, K))], 'eqbrtrrd', 'sum_ n e. NN %s <_ %s' % (QT('n'), K))
    w.qed([st([zs], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % FQ), sl], 'jca', STATEMENTS['z5sigdiag'])
    return w


if __name__ == '__main__':
    import z5alib
    for f in sys.argv[1:]:
        z5alib.run(globals()[f]())
