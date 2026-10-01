"""Sortie ZBV2, section 4 part A: the tsum of n^-S a(n)^2 as zeta times the lcm double sum
(Lean tsum_rpow_bvA_sq), for a generic weight L on ( 1 ... N ).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *
import num

PH = 'ph'
SEQ = lambda F: 'seq 1 ( + , %s )' % F
NNUZ_ = 'NN = ( ZZ>= ` 1 )'


def bvmultcvg():
    w = W('bvmultcvg', 'The zeta series restricted to the multiples of M converges (Lean summable_ite_multiples; '
                       'isumcollcvg along n = M k).')
    HS = HS1
    A = '( %s /\\ M e. NN )' % HS
    st = mkst(w, A)
    hs = st([], 'simpl', HS); mnn = st([], 'simpr', 'M e. NN')
    sre = st([hs], 'simpld', 'S e. RR')
    nsr = st([sre], 'renegcld', '-u S e. RR'); nsc = st([nsr], 'recnd', '-u S e. CC')
    MS = '( M ^c -u S )'
    IF = lambda v: 'if ( M || %s , ( %s ^c -u S ) , 0 )' % (v, v)
    F = '( t e. NN |-> %s )' % IF('t')
    G = '( t e. NN |-> ( M x. t ) )'
    H = '( t e. NN |-> ( %s x. ( t ^c -u S ) ) )' % MS
    msrp = st([st([mnn], 'nnrpd', 'M e. RR+'), nsr], 'rpcxpcld', '%s e. RR+' % MS)
    mscc = st([msrp], 'rpcnd', '%s e. CC' % MS)
    AT = '( %s /\\ t e. NN )' % A
    stt = mkst(w, AT)
    hg = st([stt([lift(w, mnn, AT), stt([], 'simpr', 't e. NN')], 'nnmulcld', '( M x. t ) e. NN')], 'fmpttd', '%s : NN --> NN' % G)
    AK = '( %s /\\ k e. NN )' % A
    sk = mkst(w, AK)
    knn = sk([], 'simpr', 'k e. NN')
    k1nn = sk([knn], 'peano2nnd', '( k + 1 ) e. NN')
    gk, _ = mpv(w, AK, 't', 'NN', '( M x. t )', 'k', knn)
    gk1, _ = mpv(w, AK, 't', 'NN', '( M x. t )', '( k + 1 )', k1nn)
    kre = sk([knn], 'nnred', 'k e. RR')
    lt = sk([kre, sk([k1nn], 'nnred', '( k + 1 ) e. RR'), sk([lift(w, mnn, AK)], 'nnrpd', 'M e. RR+'), sk([kre], 'ltp1d', 'k < ( k + 1 )')],
            'ltmul2dd', '( M x. k ) < ( M x. ( k + 1 ) )')
    hi = sk([gk, gk1, lt], '3brtr4d', '( %s ` k ) < ( %s ` ( k + 1 ) )' % (G, G))
    AN = '( %s /\\ n e. ( NN \\ ran %s ) )' % (A, G)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. ( NN \\ ran %s )' % G)
    nnn = sn([nel], 'eldifad', 'n e. NN')
    nrn = sn([nel], 'eldifbd', '-. n e. ran %s' % G)
    AD = '( %s /\\ M || n )' % AN
    sd = mkst(w, AD)
    dv = sd([], 'simpr', 'M || n')
    qnn = sd([dv, sd([lift(w, nnn, AD), lift(w, mnn, AD), w.inst('nndivdvds')], 'syl2anc', '( M || n <-> ( n / M ) e. NN )')], 'mpbid', '( n / M ) e. NN')
    gq, _ = mpv(w, AD, 't', 'NN', '( M x. t )', '( n / M )', qnn)
    canc = sd([sd([lift(w, nnn, AD)], 'nncnd', 'n e. CC'), sd([lift(w, mnn, AD)], 'nncnd', 'M e. CC'), sd([lift(w, mnn, AD)], 'nnne0d', 'M =/= 0')],
              'divcan2d', '( M x. ( n / M ) ) = n')
    gqn = sd([gq, canc], 'eqtrd', '( %s ` ( n / M ) ) = n' % G)
    gfn = sd([lift(w, hg, AD)], 'ffnd', '%s Fn NN' % G)
    inr = sd([gfn, qnn, w.inst('fnfvelrn')], 'syl2anc', '( %s ` ( n / M ) ) e. ran %s' % (G, G))
    ninr = sd([gqn, inr], 'eqeltrrd', 'n e. ran %s' % G)
    ndv = sn([nrn, ninr], 'mtand', '-. M || n')
    fn, _ = mpv(w, AN, 't', 'NN', IF('t'), 'n', nnn)
    h0 = sn([fn, sn([ndv], 'iffalsed', '%s = 0' % IF('n'))], 'eqtrd', '( %s ` n ) = 0' % F)
    AN2 = '( %s /\\ n e. NN )' % A
    sn2 = mkst(w, AN2)
    nnn2 = sn2([], 'simpr', 'n e. NN')
    fn2, _ = mpv(w, AN2, 't', 'NN', IF('t'), 'n', nnn2)
    ncx = sn2([sn2([nnn2], 'nncnd', 'n e. CC'), lift(w, nsc, AN2)], 'cxpcld', '( n ^c -u S ) e. CC')
    ifc = sn2([ncx, sn2([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF('n'))
    hf = sn2([fn2, ifc], 'eqeltrd', '( %s ` n ) e. CC' % F)
    hk, _ = mpv(w, AK, 't', 'NN', '( %s x. ( t ^c -u S ) )' % MS, 'k', knn)
    mk = sk([lift(w, mnn, AK), knn], 'nnmulcld', '( M x. k ) e. NN')
    fmk, _ = mpv(w, AK, 't', 'NN', IF('t'), '( M x. k )', mk)
    dvm = sk([sk([lift(w, mnn, AK)], 'nnzd', 'M e. ZZ'), sk([knn], 'nnzd', 'k e. ZZ'), w.inst('dvdsmul1')], 'syl2anc', 'M || ( M x. k )')
    ift = sk([dvm], 'iftrued', '%s = ( ( M x. k ) ^c -u S )' % IF('( M x. k )'))
    mre = sk([lift(w, mnn, AK)], 'nnred', 'M e. RR')
    mge = sk([sk([lift(w, mnn, AK)], 'nnrpd', 'M e. RR+')], 'rpge0d', '0 <_ M')
    kge = sk([sk([knn], 'nnrpd', 'k e. RR+')], 'rpge0d', '0 <_ k')
    mcx = sk([mre, mge, kre, kge, lift(w, nsc, AK)], 'mulcxpd', '( ( M x. k ) ^c -u S ) = ( %s x. ( k ^c -u S ) )' % MS)
    fgk = sk([gk], 'fveq2d', '( %s ` ( %s ` k ) ) = ( %s ` ( M x. k ) )' % (F, G, F))
    ch = sk([sk([fgk, fmk], 'eqtrd', '( %s ` ( %s ` k ) ) = %s' % (F, G, IF('( M x. k )'))),
             sk([ift, mcx], 'eqtrd', '%s = ( %s x. ( k ^c -u S ) )' % (IF('( M x. k )'), MS))], 'eqtrd',
            '( %s ` ( %s ` k ) ) = ( %s x. ( k ^c -u S ) )' % (F, G, MS))
    hh = sk([hk, ch], 'eqtr4d', '( %s ` k ) = ( %s ` ( %s ` k ) )' % (H, F, G))
    hc = st([hs, mscc, w.inst('zetacvgm')], 'syl2anc', '%s e. dom ~~>' % SEQ(H))
    bi = st([hg, hi, h0, hf, hh], 'isumcollcvg', '( %s e. dom ~~> <-> %s e. dom ~~> )' % (SEQ(H), SEQ(F)))
    w.qed([hc, bi], 'mpbid', STATEMENTS['bvmultcvg'])
    return w


def bvswap():
    w = W('bvswap', 'A finite sum of convergent series: the series of the finite sums converges to the finite sum of the '
                    'series (Lean Summable.tsum_finsetSum; climfsum).  The series is written twice, in j and in t, '
                    'linked by the substitution hypothesis.')
    h1, h2, h3, h4 = hyps_of(w, 'bvswap')
    st = mkst(w, PH)
    FK = SEQ('( t e. NN |-> D )')
    BK = 'sum_ j e. NN C'
    GT = '( t e. NN |-> sum_ k e. A D )'
    H = SEQ(GT)
    z = clo(w, 'nnuz', NNUZ_)
    one = st([], '1zzd', '1 e. ZZ')
    AK = '( ph /\\ k e. A )'; sk = mkst(w, AK)
    # fvmpt of ( t e. NN |-> D ) at j
    AKJ = '( %s /\\ j e. NN )' % AK; skj = mkst(w, AKJ)
    c1 = w.s([h4], 'eqcoms', '( t = j -> C = D )')
    c2 = w.s([c1], 'eqcomd', '( t = j -> D = C )')
    c3 = w.s([c2], 'adantl', '( ( %s /\\ t = j ) -> D = C )' % AKJ)
    ccj = w.s([lift(w, w.s([], 'simpl', '( ( ph /\\ k e. A ) -> ph )'), AKJ), skj([skj([], 'simplr', 'k e. A'), skj([], 'simpr', 'j e. NN')], 'jca', '( k e. A /\\ j e. NN )'), h2],
              'syl2anc', '( %s -> C e. CC )' % AKJ)
    fv = skj([skj([], 'eqidd', '( t e. NN |-> D ) = ( t e. NN |-> D )'), c3, skj([], 'simpr', 'j e. NN'), ccj], 'fvmptd', '( ( t e. NN |-> D ) ` j ) = C')
    lim = sk([z, sk([], '1zzd', '1 e. ZZ'), fv, ccj, h3], 'isumclim2', '%s ~~> %s' % (FK, BK))
    # partial sums of F are complex
    AKN = '( ph /\\ ( k e. A /\\ n e. NN ) )'; skn = mkst(w, AKN)
    AKN2 = '( %s /\\ j e. ( 1 ... n ) )' % AKN; skn2 = mkst(w, AKN2)
    jnn = sy(w, AKN2, skn2([], 'simpr', 'j e. ( 1 ... n )'), 'elfznn', 'j e. NN')
    ccj2 = w.s([lift(w, w.s([], 'simpl', '( %s -> ph )' % AKN), AKN2), skn2([lift(w, skn([], 'simprl', 'k e. A'), AKN2), jnn], 'jca', '( k e. A /\\ j e. NN )'), h2],
               'syl2anc', '( %s -> C e. CC )' % AKN2)
    c4 = w.s([c2], 'adantl', '( ( %s /\\ t = j ) -> D = C )' % AKN2)
    fv2 = skn2([skn2([], 'eqidd', '( t e. NN |-> D ) = ( t e. NN |-> D )'), c4, jnn, ccj2], 'fvmptd', '( ( t e. NN |-> D ) ` j ) = C')
    nuz = skn([skn([], 'simprr', 'n e. NN'), w.inst('elnnuz')], 'sylib', 'n e. ( ZZ>= ` 1 )')
    fs = skn([fv2, nuz, ccj2], 'fsumser', 'sum_ j e. ( 1 ... n ) C = ( %s ` n )' % FK)
    fcc = skn([fs, skn([skn([], 'fzfid', '( 1 ... n ) e. Fin'), ccj2], 'fsumcl', 'sum_ j e. ( 1 ... n ) C e. CC')], 'eqeltrrd', '( %s ` n ) e. CC' % FK)
    # H ` n = sum_ k e. A ( F ` n )
    AN = '( ph /\\ n e. NN )'; sn = mkst(w, AN)
    AN2 = '( %s /\\ j e. ( 1 ... n ) )' % AN; sn2 = mkst(w, AN2)
    jnn3 = sy(w, AN2, sn2([], 'simpr', 'j e. ( 1 ... n )'), 'elfznn', 'j e. NN')
    AN3 = '( %s /\\ k e. A )' % AN2; sn3 = mkst(w, AN3)
    cc3 = w.s([lift(w, w.s([], 'simpl', '( %s -> ph )' % AN), AN3), sn3([sn3([], 'simpr', 'k e. A'), lift(w, jnn3, AN3)], 'jca', '( k e. A /\\ j e. NN )'), h2],
              'syl2anc', '( %s -> C e. CC )' % AN3)
    sumc = sn2([lift(w, h1, AN2), cc3], 'fsumcl', 'sum_ k e. A C e. CC')
    c5a = w.s([w.s([c2], 'adantr', '( ( t = j /\\ k e. A ) -> D = C )')], 'sumeq2dv', '( t = j -> sum_ k e. A D = sum_ k e. A C )')
    c5 = w.s([c5a], 'adantl', '( ( %s /\\ t = j ) -> sum_ k e. A D = sum_ k e. A C )' % AN2)
    fvh = sn2([sn2([], 'eqidd', '%s = %s' % (GT, GT)), c5, jnn3, sumc], 'fvmptd', '( %s ` j ) = sum_ k e. A C' % GT)
    nuz2 = sn([sn([], 'simpr', 'n e. NN'), w.inst('elnnuz')], 'sylib', 'n e. ( ZZ>= ` 1 )')
    hs1 = sn([fvh, nuz2, sumc], 'fsumser', 'sum_ j e. ( 1 ... n ) sum_ k e. A C = ( %s ` n )' % H)
    ANJK = '( %s /\\ ( j e. ( 1 ... n ) /\\ k e. A ) )' % AN; snjk = mkst(w, ANJK)
    jnn4 = sy(w, ANJK, snjk([], 'simprl', 'j e. ( 1 ... n )'), 'elfznn', 'j e. NN')
    cc4 = w.s([lift(w, w.s([], 'simpl', '( %s -> ph )' % AN), ANJK), snjk([snjk([], 'simprr', 'k e. A'), jnn4], 'jca', '( k e. A /\\ j e. NN )'), h2],
              'syl2anc', '( %s -> C e. CC )' % ANJK)
    com = sn([sn([], 'fzfid', '( 1 ... n ) e. Fin'), lift(w, h1, AN), cc4], 'fsumcom', 'sum_ j e. ( 1 ... n ) sum_ k e. A C = sum_ k e. A sum_ j e. ( 1 ... n ) C')
    # per k: sum_ j e. ( 1 ... n ) C = ( F ` n ), under ( ( ph /\ n e. NN ) /\ k e. A )
    ANK = '( %s /\\ k e. A )' % AN; snk = mkst(w, ANK)
    # derive fs under ANK via the implication form
    fsimp = w.s([fs], 'ex', '( ph -> ( ( k e. A /\\ n e. NN ) -> sum_ j e. ( 1 ... n ) C = ( %s ` n ) ) )' % FK)
    imp = w.s([lift(w, w.s([], 'simpl', '( %s -> ph )' % AN), ANK), fsimp], 'syl', '( %s -> ( ( k e. A /\\ n e. NN ) -> sum_ j e. ( 1 ... n ) C = ( %s ` n ) ) )' % (ANK, FK))
    fsk = snk([snk([snk([], 'simpr', 'k e. A'), lift(w, sn([], 'simpr', 'n e. NN'), ANK)], 'jca', '( k e. A /\\ n e. NN )'), imp], 'mpd', 'sum_ j e. ( 1 ... n ) C = ( %s ` n )' % FK)
    per = sn([fsk], 'sumeq2dv', 'sum_ k e. A sum_ j e. ( 1 ... n ) C = sum_ k e. A ( %s ` n )' % FK)
    h8 = eqtr(w, AN, [sn([hs1], 'eqcomd', '( %s ` n ) = sum_ j e. ( 1 ... n ) sum_ k e. A C' % H), com, per], None)
    hex = st([w.s([], 'seqex', '%s e. _V' % H)], 'a1i', '%s e. _V' % H)
    w.qed([z, one, h1, lim, hex, fcc, h8], 'climfsum', STATEMENTS['bvswap'])
    return w


def lcmnn(w, ante, dnn, enn, d, e):
    """( ante -> ( d lcm e ) e. NN ) from d, e e. NN"""
    st = mkst(w, ante)
    dz = st([dnn], 'nnzd', '%s e. ZZ' % d); ez = st([enn], 'nnzd', '%s e. ZZ' % e)
    ne = st([st([dnn], 'nnne0d', '%s =/= 0' % d), st([enn], 'nnne0d', '%s =/= 0' % e)], 'jca', '( %s =/= 0 /\\ %s =/= 0 )' % (d, e))
    nor = st([ne, w.inst('neanior')], 'sylib', '-. ( %s = 0 \\/ %s = 0 )' % (d, e))
    return st([st([dz, ez], 'jca', '( %s e. ZZ /\\ %s e. ZZ )' % (d, e)), nor, w.inst('lcmn0cl')], 'syl2anc', '( %s lcm %s ) e. NN' % (d, e))


def bvtsumpt():
    w = W('bvtsumpt', 'Pointwise square expansion over lcm pairs: J^-S a(J)^2 = sum_ d sum_ e L_d L_e [ lcm | J ] J^-S '
                      '(Lean rpow_mul_bvA_sq; fsum2mul, ifmul2, lcmdvdsb).')
    h1, h2, h3 = hyps_of(w, 'bvtsumpt')
    st = mkst(w, PH)
    sr = st([h1], 'simpld', 'S e. RR'); jnn = st([h1], 'simprd', 'J e. NN')
    jz = st([jnn], 'nnzd', 'J e. ZZ')
    JS = '( J ^c -u S )'
    jsc = st([st([st([jnn], 'nnrpd', 'J e. RR+'), st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '%s e. RR+' % JS)], 'rpcnd', '%s e. CC' % JS)
    fin = st([], 'fzfid', '( 1 ... N ) e. Fin')
    XD = 'if ( d || J , ( L ` d ) , 0 )'; XE = 'if ( e || J , ( L ` e ) , 0 )'
    AD = '( ph /\\ d e. ( 1 ... N ) )'; sd = mkst(w, AD)
    ldc = sd([h3], 'recnd', '( L ` d ) e. CC')
    xdc = sd([ldc, sd([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % XD)
    h3e, _ = rename(w, PH, '( 1 ... N )', 'd', 'e', h3, '( L ` d ) e. RR')
    AE = '( ph /\\ e e. ( 1 ... N ) )'; se = mkst(w, AE)
    lec = se([h3e], 'recnd', '( L ` e ) e. CC')
    xec = se([lec, se([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % XE)
    AL = ALs('J'); ALE = 'sum_ e e. ( 1 ... N ) %s' % XE
    alc = st([fin, xdc], 'fsumcl', '%s e. CC' % AL)
    ide = w.s([], 'id', '( d = e -> d = e )')
    cg, _ = w.congr(XD, {'d': 'e'}, 'd = e', {'d': ide})
    cb = st([w.s([cg], 'cbvsumv', '%s = %s' % (AL, ALE))], 'a1i', '%s = %s' % (AL, ALE))
    sq = st([st([alc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (AL, AL, AL)), st([cb], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (AL, AL, AL, ALE))], 'eqtrd',
            '( %s ^ 2 ) = ( %s x. %s )' % (AL, AL, ALE))
    P = '( %s x. %s )' % (XD, XE)
    f2 = st([fin, fin, xdc, xec], 'fsum2mul', 'sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s = ( %s x. %s )' % (P, AL, ALE))
    sq2 = st([sq, st([f2], 'eqcomd', '( %s x. %s ) = sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s' % (AL, ALE, P))], 'eqtrd',
             '( %s ^ 2 ) = sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s' % (AL, P))
    ADE = '( %s /\\ e e. ( 1 ... N ) )' % AD; sde = mkst(w, ADE)
    h3e2 = hyp2(w, ADE, lift(w, w.s([], 'id', '( ph -> ph )'), ADE), sde([], 'simpr', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR')
    lec2 = sde([h3e2], 'recnd', '( L ` e ) e. CC')
    xec2 = sde([lec2, sde([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % XE)
    pc = sde([lift(w, xdc, ADE), xec2], 'mulcld', '%s e. CC' % P)
    innc = sd([sd([], 'fzfid', '( 1 ... N ) e. Fin'), pc], 'fsumcl', 'sum_ e e. ( 1 ... N ) %s e. CC' % P)
    m1 = st([fin, jsc, innc], 'fsummulc2', '( %s x. sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s ) = sum_ d e. ( 1 ... N ) ( %s x. sum_ e e. ( 1 ... N ) %s )' % (JS, P, JS, P))
    m2 = sd([sd([], 'fzfid', '( 1 ... N ) e. Fin'), lift(w, jsc, AD), pc], 'fsummulc2', '( %s x. sum_ e e. ( 1 ... N ) %s ) = sum_ e e. ( 1 ... N ) ( %s x. %s )' % (JS, P, JS, P))
    # the term
    LL = '( ( L ` d ) x. ( L ` e ) )'
    ldc2 = lift(w, ldc, ADE)
    im = w.s([sde([ldc2, lec2], 'jca', '( ( L ` d ) e. CC /\\ ( L ` e ) e. CC )'), w.inst('ifmul2')], 'syl',
             '( %s -> if ( ( d || J /\\ e || J ) , %s , 0 ) = %s )' % (ADE, LL, P))
    dz = sy(w, ADE, sde([], 'simpr', 'e e. ( 1 ... N )'), 'elfzelz', 'e e. ZZ')
    dzd = sy(w, ADE, lift(w, sd([], 'simpr', 'd e. ( 1 ... N )'), ADE), 'elfzelz', 'd e. ZZ')
    lb = w.s([bind3(w, ADE, lift(w, jz, ADE), dzd, dz, 'J e. ZZ', 'd e. ZZ', 'e e. ZZ'), w.inst('lcmdvdsb')], 'syl', '( %s -> ( ( d || J /\\ e || J ) <-> ( d lcm e ) || J ) )' % ADE)
    ib = sde([lb], 'ifbid', 'if ( ( d || J /\\ e || J ) , %s , 0 ) = if ( ( d lcm e ) || J , %s , 0 )' % (LL, LL))
    llc = sde([ldc2, lec2], 'mulcld', '%s e. CC' % LL)
    jsc2 = lift(w, jsc, ADE)
    z1 = w.s([jsc2, w.inst('ifmulz2')], 'syl', '( %s -> ( %s x. if ( ( d lcm e ) || J , %s , 0 ) ) = if ( ( d lcm e ) || J , ( %s x. %s ) , 0 ) )' % (ADE, JS, LL, JS, LL))
    z2 = w.s([llc, w.inst('ifmulz2')], 'syl', '( %s -> ( %s x. if ( ( d lcm e ) || J , %s , 0 ) ) = if ( ( d lcm e ) || J , ( %s x. %s ) , 0 ) )' % (ADE, LL, JS, LL, JS))
    cm = sde([sde([jsc2, llc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (JS, LL, LL, JS))], 'ifeq1d',
             'if ( ( d lcm e ) || J , ( %s x. %s ) , 0 ) = if ( ( d lcm e ) || J , ( %s x. %s ) , 0 )' % (JS, LL, LL, JS))
    t1 = sde([sde([im], 'eqcomd', '%s = if ( ( d || J /\\ e || J ) , %s , 0 )' % (P, LL)), ib], 'eqtrd', '%s = if ( ( d lcm e ) || J , %s , 0 )' % (P, LL))
    term = eqtr(w, ADE, [sde([t1], 'oveq2d', '( %s x. %s ) = ( %s x. if ( ( d lcm e ) || J , %s , 0 ) )' % (JS, P, JS, LL)), z1, cm, sde([z2], 'eqcomd',
                  'if ( ( d lcm e ) || J , ( %s x. %s ) , 0 ) = %s' % (LL, JS, TDE('J')))], None)
    s_in = sd([term], 'sumeq2dv', 'sum_ e e. ( 1 ... N ) ( %s x. %s ) = sum_ e e. ( 1 ... N ) %s' % (JS, P, TDE('J')))
    s_out = st([sd([m2, s_in], 'eqtrd', '( %s x. sum_ e e. ( 1 ... N ) %s ) = sum_ e e. ( 1 ... N ) %s' % (JS, P, TDE('J')))], 'sumeq2dv',
               'sum_ d e. ( 1 ... N ) ( %s x. sum_ e e. ( 1 ... N ) %s ) = sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s' % (JS, P, TDE('J')))
    full = eqtr(w, PH, [st([sq2], 'oveq2d', '( %s x. ( %s ^ 2 ) ) = ( %s x. sum_ d e. ( 1 ... N ) sum_ e e. ( 1 ... N ) %s )' % (JS, AL, JS, P)), m1, s_out], None)
    w.qed([full, w.inst('id')], 'syl', STATEMENTS['bvtsumpt'])
    return w


def bvtsumlem():
    w = W('bvtsumlem', 'One pair of the lcm double sum: sum_ j L_D L_E [ lcm | j ] j^-S = L_D L_E lcm^-S zeta ( S ), as a '
                       'limit (bvmult, bvmultcvg, isermulc2).')
    h1, h2, h3 = hyps_of(w, 'bvtsumlem')
    st = mkst(w, PH)
    sr = st([h1], 'simpld', 'S e. RR')
    dnn = st([h2], 'simpld', 'D e. NN'); enn = st([h2], 'simprd', 'E e. NN')
    M = '( D lcm E )'
    mnn = lcmnn(w, PH, dnn, enn, 'D', 'E')
    IF = lambda v: 'if ( %s || %s , ( %s ^c -u S ) , 0 )' % (M, v, v)
    FM = '( t e. NN |-> %s )' % IF('t')
    cv = sy(w, PH, bind(w, PH, h1, mnn, HS1, '%s e. NN' % M), 'bvmultcvg', '%s e. dom ~~>' % SEQ(FM))
    z = clo(w, 'nnuz', NNUZ_); one = st([], '1zzd', '1 e. ZZ')
    AN = '( ph /\\ n e. NN )'; sn = mkst(w, AN)
    nnn = sn([], 'simpr', 'n e. NN')
    vn, _ = mpv(w, AN, 't', 'NN', IF('t'), 'n', nnn)
    nsc = st([st([sr], 'renegcld', '-u S e. RR')], 'recnd', '-u S e. CC')
    ifc = sn([sn([sn([nnn], 'nncnd', 'n e. CC'), lift(w, nsc, AN)], 'cxpcld', '( n ^c -u S ) e. CC'), sn([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF('n'))
    lim = st([z, one, vn, ifc, cv], 'isumclim2', '%s ~~> sum_ n e. NN %s' % (SEQ(FM), IF('n')))
    bm = sy(w, PH, bind(w, PH, h1, mnn, HS1, '%s e. NN' % M), 'bvmult', 'sum_ n e. NN %s = ( ( %s ^c -u S ) x. %s )' % (IF('n'), M, ZS()))
    lim2 = st([lim, bm], 'breqtrd', '%s ~~> ( ( %s ^c -u S ) x. %s )' % (SEQ(FM), M, ZS()))
    LL = '( ( L ` D ) x. ( L ` E ) )'
    llc = st([st([st([h3], 'simpld', '( L ` D ) e. RR'), st([h3], 'simprd', '( L ` E ) e. RR')], 'remulcld', '%s e. RR' % LL)], 'recnd', '%s e. CC' % LL)
    AK = '( ph /\\ k e. NN )'; sk = mkst(w, AK)
    knn = sk([], 'simpr', 'k e. NN')
    vk, _ = mpv(w, AK, 't', 'NN', IF('t'), 'k', knn)
    ifk = sk([sk([sk([knn], 'nncnd', 'k e. CC'), lift(w, nsc, AK)], 'cxpcld', '( k ^c -u S ) e. CC'), sk([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF('k'))
    fkc = sk([vk, ifk], 'eqeltrd', '( %s ` k ) e. CC' % FM)
    G = '( t e. NN |-> %s )' % TDE('t', 'D', 'E')
    vg, _ = mpv(w, AK, 't', 'NN', TDE('t', 'D', 'E'), 'k', knn)
    gk = sk([vg, sk([sk([vk], 'eqcomd', '%s = ( %s ` k )' % (IF('k'), FM))], 'oveq2d', '%s = ( %s x. ( %s ` k ) )' % (TDE('k', 'D', 'E'), LL, FM))], 'eqtrd',
            '( %s ` k ) = ( %s x. ( %s ` k ) )' % (G, LL, FM))
    ml = st([z, one, llc, lim2, fkc, gk], 'isermulc2', '%s ~~> ( %s x. ( ( %s ^c -u S ) x. %s ) )' % (SEQ(G), LL, M, ZS()))
    msc = st([st([st([mnn], 'nnrpd', '%s e. RR+' % M), st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '( %s ^c -u S ) e. RR+' % M)], 'rpcnd', '( %s ^c -u S ) e. CC' % M)
    zsc = st([st([h1, w.inst('zetasumcl')], 'syl', '%s e. RR' % ZS())], 'recnd', '%s e. CC' % ZS())
    asc = st([llc, msc, zsc], 'mulassd', '( ( %s x. ( %s ^c -u S ) ) x. %s ) = ( %s x. ( ( %s ^c -u S ) x. %s ) )' % (LL, M, ZS(), LL, M, ZS()))
    w.qed([ml, st([asc], 'eqcomd', '( %s x. ( ( %s ^c -u S ) x. %s ) ) = ( ( %s x. ( %s ^c -u S ) ) x. %s )' % (LL, M, ZS(), LL, M, ZS()))], 'breqtrd', STATEMENTS['bvtsumlem'])
    return w


def bvtsum():
    w = W('bvtsum', 'Diagonalisation step 1 (Lean tsum_rpow_bvA_sq): the series of j^-S a(j)^2 converges to '
                    'zeta ( S ) times the lcm double sum (bvtsumpt, bvtsumlem, bvswap twice).')
    h1, h2, h3 = hyps_of(w, 'bvtsum')
    st = mkst(w, PH)
    sr = st([h1], 'simpld', 'S e. RR')
    nsc = st([st([sr], 'renegcld', '-u S e. RR')], 'recnd', '-u S e. CC')
    fin = st([], 'fzfid', '( 1 ... N ) e. Fin')
    zsc = st([st([h1, w.inst('zetasumcl')], 'syl', '%s e. RR' % ZS())], 'recnd', '%s e. CC' % ZS())
    AD = '( ph /\\ d e. ( 1 ... N ) )'; sd = mkst(w, AD)
    ADE = '( %s /\\ e e. ( 1 ... N ) )' % AD; sde = mkst(w, ADE)
    h3e, _ = rename(w, PH, '( 1 ... N )', 'd', 'e', h3, '( L ` d ) e. RR')
    phde = lift(w, w.s([], 'id', '( ph -> ph )'), ADE)
    lde = sde([lift(w, h3, ADE), hyp2(w, ADE, phde, sde([], 'simpr', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR')],
              'jca', '( ( L ` d ) e. RR /\\ ( L ` e ) e. RR )')
    dnn = sy(w, ADE, lift(w, sd([], 'simpr', 'd e. ( 1 ... N )'), ADE), 'elfznn', 'd e. NN')
    enn = sy(w, ADE, sde([], 'simpr', 'e e. ( 1 ... N )'), 'elfznn', 'e e. NN')
    tl = w.s([lift(w, h1, ADE), sde([dnn, enn], 'jca', '( d e. NN /\\ e e. NN )'), lde], 'bvtsumlem',
             '( %s -> %s ~~> ( %s x. %s ) )' % (ADE, SEQ('( t e. NN |-> %s )' % TDE('t')), LCMS(), ZS()))
    rel = w.s([], 'climrel', 'Rel ~~>')
    cvi = sde([sde([rel], 'a1i', 'Rel ~~>'), tl, w.inst('releldm')], 'syl2anc', '%s e. dom ~~>' % SEQ('( t e. NN |-> %s )' % TDE('t')))
    # closure of TDE(j)
    def tdecc(ante, jnn, j, dstep, estep):
        s_ = mkst(w, ante)
        llc = s_([s_([dstep, estep], 'remulcld', '( ( L ` d ) x. ( L ` e ) ) e. RR')], 'recnd', '( ( L ` d ) x. ( L ` e ) ) e. CC')
        jc = s_([s_([jnn], 'nncnd', '%s e. CC' % j), lift(w, nsc, ante)], 'cxpcld', '( %s ^c -u S ) e. CC' % j)
        ifc = s_([jc, s_([], '0cnd', '0 e. CC')], 'ifcld', 'if ( ( d lcm e ) || %s , ( %s ^c -u S ) , 0 ) e. CC' % (j, j))
        return s_([llc, ifc], 'mulcld', '%s e. CC' % TDE(j))
    AI = '( %s /\\ ( e e. ( 1 ... N ) /\\ j e. NN ) )' % AD; si = mkst(w, AI)
    ld_i = lift(w, h3, AI)
    le_i = hyp2(w, AI, lift(w, w.s([], 'id', '( ph -> ph )'), AI), si([], 'simprl', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR')
    tcc = tdecc(AI, si([], 'simprr', 'j e. NN'), 'j', ld_i, le_i)
    idjt = w.s([], 'id', '( j = t -> j = t )')
    cgt, _ = w.congr(TDE('j'), {'j': 't'}, 'j = t', {'j': idjt})
    SE = lambda j: 'sum_ e e. ( 1 ... N ) %s' % TDE(j)
    inner = w.s([sd([], 'fzfid', '( 1 ... N ) e. Fin'), tcc, cvi, cgt], 'bvswap',
                '( %s -> %s ~~> sum_ e e. ( 1 ... N ) sum_ j e. NN %s )' % (AD, SEQ('( t e. NN |-> %s )' % SE('t')), TDE('j')))
    # value of the inner series: sum_ j e. NN TDE(j) = LCMS x. ZS
    ADEJ = '( %s /\\ j e. NN )' % ADE; sdej = mkst(w, ADEJ)
    jnn2 = sdej([], 'simpr', 'j e. NN')
    tcc2 = tdecc(ADEJ, jnn2, 'j', lift(w, sde([lde], 'simpld', '( L ` d ) e. RR'), ADEJ), lift(w, sde([lde], 'simprd', '( L ` e ) e. RR'), ADEJ))
    vj, _ = mpv(w, ADEJ, 't', 'NN', TDE('t'), 'j', jnn2)
    z = clo(w, 'nnuz', NNUZ_)
    ival = sde([z, sde([], '1zzd', '1 e. ZZ'), vj, tcc2, tl], 'isumclim', 'sum_ j e. NN %s = ( %s x. %s )' % (TDE('j'), LCMS(), ZS()))
    inner2 = sd([inner, sd([ival], 'sumeq2dv', 'sum_ e e. ( 1 ... N ) sum_ j e. NN %s = sum_ e e. ( 1 ... N ) ( %s x. %s )' % (TDE('j'), LCMS(), ZS()))], 'breqtrd',
                '%s ~~> sum_ e e. ( 1 ... N ) ( %s x. %s )' % (SEQ('( t e. NN |-> %s )' % SE('t')), LCMS(), ZS()))
    cvo = sd([sd([rel], 'a1i', 'Rel ~~>'), inner2, w.inst('releldm')], 'syl2anc', '%s e. dom ~~>' % SEQ('( t e. NN |-> %s )' % SE('t')))
    # outer closure: ( ( ph /\ ( d e. ( 1 ... N ) /\ j e. NN ) ) -> SE(j) e. CC )
    AO = '( ph /\\ ( d e. ( 1 ... N ) /\\ j e. NN ) )'; so = mkst(w, AO)
    AOE = '( %s /\\ e e. ( 1 ... N ) )' % AO; soe = mkst(w, AOE)
    phoe = lift(w, w.s([], 'id', '( ph -> ph )'), AOE)
    ld_o = hyp2(w, AOE, phoe, lift(w, so([], 'simprl', 'd e. ( 1 ... N )'), AOE), h3, '( L ` d ) e. RR')
    le_o = hyp2(w, AOE, phoe, soe([], 'simpr', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR')
    tco = tdecc(AOE, lift(w, so([], 'simprr', 'j e. NN'), AOE), 'j', ld_o, le_o)
    seo = so([so([], 'fzfid', '( 1 ... N ) e. Fin'), tco], 'fsumcl', '%s e. CC' % SE('j'))
    cgo, _ = w.congr(SE('j'), {'j': 't'}, 'j = t', {'j': idjt})
    outer = w.s([fin, seo, cvo, cgo], 'bvswap',
                '( ph -> %s ~~> sum_ d e. ( 1 ... N ) sum_ j e. NN %s )' % (SEQ('( t e. NN |-> sum_ d e. ( 1 ... N ) %s )' % SE('t')), SE('j')))
    # value of the outer summands
    ADJ = '( %s /\\ j e. NN )' % AD; sdj = mkst(w, ADJ)
    jnn3 = sdj([], 'simpr', 'j e. NN')
    ADJE = '( %s /\\ e e. ( 1 ... N ) )' % ADJ; sdje = mkst(w, ADJE)
    phje = lift(w, w.s([], 'id', '( ph -> ph )'), ADJE)
    tc3 = tdecc(ADJE, lift(w, jnn3, ADJE), 'j', hyp2(w, ADJE, phje, lift(w, sd([], 'simpr', 'd e. ( 1 ... N )'), ADJE), h3, '( L ` d ) e. RR'),
                hyp2(w, ADJE, phje, sdje([], 'simpr', 'e e. ( 1 ... N )'), h3e, '( L ` e ) e. RR'))
    sec = sdj([sdj([], 'fzfid', '( 1 ... N ) e. Fin'), tc3], 'fsumcl', '%s e. CC' % SE('j'))
    vo, _ = mpv(w, ADJ, 't', 'NN', SE('t'), 'j', jnn3, exs=sdj([sec], 'elexd', '%s e. _V' % SE('j')))
    oval = sd([z, sd([], '1zzd', '1 e. ZZ'), vo, sec, inner2], 'isumclim', 'sum_ j e. NN %s = sum_ e e. ( 1 ... N ) ( %s x. %s )' % (SE('j'), LCMS(), ZS()))
    # the limit value
    lcc = sde([sde([sde([lde], 'simpld', '( L ` d ) e. RR'), sde([lde], 'simprd', '( L ` e ) e. RR')], 'remulcld', '( ( L ` d ) x. ( L ` e ) ) e. RR'),
               sde([sde([sde([lcmnn(w, ADE, dnn, enn, 'd', 'e')], 'nnrpd', '( d lcm e ) e. RR+'), lift(w, st([sr], 'renegcld', '-u S e. RR'), ADE)], 'rpcxpcld',
                        '( ( d lcm e ) ^c -u S ) e. RR+')], 'rpred', '( ( d lcm e ) ^c -u S ) e. RR')], 'remulcld', '%s e. RR' % LCMS())
    lccc = sde([lcc], 'recnd', '%s e. CC' % LCMS())
    fm1 = sd([sd([], 'fzfid', '( 1 ... N ) e. Fin'), lift(w, zsc, AD), lccc], 'fsummulc1', '( sum_ e e. ( 1 ... N ) %s x. %s ) = sum_ e e. ( 1 ... N ) ( %s x. %s )' % (LCMS(), ZS(), LCMS(), ZS()))
    in_c = sd([sd([], 'fzfid', '( 1 ... N ) e. Fin'), lccc], 'fsumcl', 'sum_ e e. ( 1 ... N ) %s e. CC' % LCMS())
    fm2 = st([fin, zsc, in_c], 'fsummulc1', '( %s x. %s ) = sum_ d e. ( 1 ... N ) ( sum_ e e. ( 1 ... N ) %s x. %s )' % (DSUM(), ZS(), LCMS(), ZS()))
    v1 = st([sd([oval, sd([fm1], 'eqcomd', 'sum_ e e. ( 1 ... N ) ( %s x. %s ) = ( sum_ e e. ( 1 ... N ) %s x. %s )' % (LCMS(), ZS(), LCMS(), ZS()))], 'eqtrd',
                 'sum_ j e. NN %s = ( sum_ e e. ( 1 ... N ) %s x. %s )' % (SE('j'), LCMS(), ZS()))], 'sumeq2dv',
            'sum_ d e. ( 1 ... N ) sum_ j e. NN %s = sum_ d e. ( 1 ... N ) ( sum_ e e. ( 1 ... N ) %s x. %s )' % (SE('j'), LCMS(), ZS()))
    dsc = st([fin, in_c], 'fsumcl', '%s e. CC' % DSUM())
    val = eqtr(w, PH, [v1, st([fm2], 'eqcomd', 'sum_ d e. ( 1 ... N ) ( sum_ e e. ( 1 ... N ) %s x. %s ) = ( %s x. %s )' % (LCMS(), ZS(), DSUM(), ZS())),
                       st([dsc, zsc], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (DSUM(), ZS(), ZS(), DSUM()))], None)
    lim = st([outer, val], 'breqtrd', '%s ~~> ( %s x. %s )' % (SEQ('( t e. NN |-> sum_ d e. ( 1 ... N ) %s )' % SE('t')), ZS(), DSUM()))
    # the mapping: bvtsumpt at J = t
    AT = '( ph /\\ t e. NN )'; stt = mkst(w, AT)
    ATD = '( %s /\\ d e. ( 1 ... N ) )' % AT
    h3t = hyp2(w, ATD, lift(w, w.s([], 'id', '( ph -> ph )'), ATD), mkst(w, ATD)([], 'simpr', 'd e. ( 1 ... N )'), h3, '( L ` d ) e. RR')
    pt = w.s([mkst(w, AT)([lift(w, sr, AT), stt([], 'simpr', 't e. NN')], 'jca', '( S e. RR /\\ t e. NN )'), lift(w, h2, AT), h3t], 'bvtsumpt',
             '( %s -> ( ( t ^c -u S ) x. ( %s ^ 2 ) ) = sum_ d e. ( 1 ... N ) %s )' % (AT, ALs('t'), SE('t')))
    mp = st([pt], 'mpteq2dva', '( t e. NN |-> ( ( t ^c -u S ) x. ( %s ^ 2 ) ) ) = ( t e. NN |-> sum_ d e. ( 1 ... N ) %s )' % (ALs('t'), SE('t')))
    sq = st([mp], 'seqeq3d', '%s = %s' % (SEQ('( t e. NN |-> ( ( t ^c -u S ) x. ( %s ^ 2 ) ) )' % ALs('t')), SEQ('( t e. NN |-> sum_ d e. ( 1 ... N ) %s )' % SE('t'))))
    w.qed([sq, lim], 'eqbrtrd', STATEMENTS['bvtsum'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvmultcvg', 'bvswap', 'bvtsumpt', 'bvtsumlem', 'bvtsum']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
