"""Sortie LD2, section 5 (L1.e): ld2exp ld2epb ld2fdv ld2trl ld2dlv ld2dlvx.
Run: MM_DB=sorties/ld2.mm MM_ENGINE=mmatch python3 tools/gen/ld2_a.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ld2lib import *
from ld1lib import TT, FZN, BLKSUM, TAYSUM, TSUMMAND, BLKC, BODY, NB
from ld1_d import setupx, hab, basefacts, liftcl, termcl

only = sys.argv[1:]
want = lambda l: not only or l in only
L = LOGD
RJ = '( 0 ..^ %s )' % JPAR
KJ = '( 0 ... %s )' % JPAR
IS = '( Im ` S )'
D2 = '( 2 x. D )'
PRNH = '( h e. NN |-> if ( ( h gcd N ) = 1 , 1 , 0 ) )'


def srngh(w, A, P, c):
    """SRNGH from S e. CC, 39/50 <_ T, T <_ Re S, Re S <_ 1 (SIG's parts)"""
    sc = P['S e. CC']; t39 = P['( ; 3 9 / ; 5 0 ) <_ T']; tre = P['T <_ ( Re ` S )']; re1 = P['( Re ` S ) <_ 1']
    c.leaf('T', 'RR', P['T e. RR'])
    lo = dst(w, A, [c.mem('( ; 3 9 / ; 5 0 )', 'RR'), c.mem('T', 'RR'), c.mem('( Re ` S )', 'RR'), t39, tre], 'letrd', '( ; 3 9 / ; 5 0 ) <_ ( Re ` S )')
    return J(w, A, sc, J(w, A, lo, re1)), lo


def a7h(w, A, P, c):
    """dshdih's antecedent A7H from the parts of HDLV"""
    hz = P[HZH]; nn = P['N e. NN']; chrb = P[CHRB]; sne = P['S =/= 1']; lif = P[LIF]; es0 = P['( E ` S ) = 0']
    sr, lo = srngh(w, A, P, c)
    return J(w, A, J(w, A, J(w, A, hz, nn), J(w, A, chrb, J(w, A, sr, sne))), J(w, A, lif, es0)), sr, lo


def ectrcl(w, A, P, c, sr):
    """( A -> ECTRH e. CC ) by dshvlc at R = 1 (needs HZH, N, CFN, S =/= 1, LIF, ( E ` S ) = 0 in P)"""
    hz = P[HZH]; nn = P['N e. NN']; cfn = J(w, A, P['C : NN --> CC'], P[CB]); sne = P['S =/= 1']; lif = P[LIF]; es0 = P['( E ` S ) = 0']
    one = a1(w, A, '1nn', '1 e. NN')
    mu = a1(w, A, 'sqf1', '( mmu ` 1 ) =/= 0')
    hyp = J(w, A, J(w, A, J(w, A, hz, nn), J(w, A, J(w, A, cfn, J(w, A, one, mu)), J(w, A, sr, sne))), J(w, A, lif, es0))
    vc = ap(w, A, 'dshvlc', [hyp], '%s e. CC' % VLH)
    ipc = w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')
    tpc = w.s([w.s([], '2cn', '2 e. CC'), ipc], 'mulcli', '%s e. CC' % TPI)
    ipn = w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], 'ine0', '_i =/= 0'), w.s([], 'pine0', '_pi =/= 0')], 'mulne0i', '( _i x. _pi ) =/= 0')
    tpn = w.s([w.s([], '2cn', '2 e. CC'), ipc, w.s([], '2ne0', '2 =/= 0'), ipn], 'mulne0i', '%s =/= 0' % TPI)
    rc = w.s([w.s([], 'ax-1cn', '1 e. CC'), tpc, tpn], 'divcli', '( 1 / %s ) e. CC' % TPI)
    return dst(w, A, [w.s([rc], 'a1i', '( %s -> ( 1 / %s ) e. CC )' % (A, TPI)), vc], 'mulcld', '%s e. CC' % ECTRH)


def ephcl(w, A, P, c, F, h0, sr):
    """( A -> EPH(C) e. CC ) and the value by dshep1 (needs C : NN --> CC, N e. NN, S e. CC, S =/= 1)"""
    cf = P['C : NN --> CC']; nn = P['N e. NN']; sc = P['S e. CC']; sne = P['S =/= 1']
    c.leaf('N', 'NN', nn)
    cv = ap(w, A, 'fex', [cf, a1(w, A, 'nnex', 'NN e. _V')], 'C e. _V')
    EPB1 = '( ( ( ( _G ` ( 1 - S ) ) x. ( %s ^c ( 1 - S ) ) ) x. ( ( phi ` N ) / N ) ) x. ( %s ` 1 ) )' % (YP, MRF)
    val = ap(w, A, 'dshep1', [J(w, A, J(w, A, h0, F['yrp']), J(w, A, cv, nn)), sc], '%s = if ( C = %s , %s , 0 )' % (EPH('C'), PRN, EPB1))
    pdg = ap(w, A, 'dshpdg', [J(w, A, sr, sne)], '( 1 - S ) e. %s' % DG)
    gc = ap(w, A, 'gamcl', [pdg], '( _G ` ( 1 - S ) ) e. CC')
    c.leaf('( _G ` ( 1 - S ) )', 'CC', gc)
    mrc = ap(w, A, 'z5mrcl', [J(w, A, h0, a1(w, A, '1nn', '1 e. NN')), J(w, A, cf, a1(w, A, 'ax-1cn', '1 e. CC'))], '( %s ` 1 ) e. CC' % MRF)
    c.leaf('( %s ` 1 )' % MRF, 'CC', mrc)
    c.leaf('( phi ` N )', 'NN', ap(w, A, 'phicl', [nn], '( phi ` N ) e. NN'))
    ec = dst(w, A, [c.mem(EPB1, 'CC'), w.s([], '0cnd', '( %s -> 0 e. CC )' % A)], 'ifcld', 'if ( C = %s , %s , 0 ) e. CC' % (PRN, EPB1))
    return dst(w, A, [val, ec], 'eqeltrd', '%s e. CC' % EPH('C')), val


def ld2exp():
    w = W('ld2exp', 'Lean ` hexp ` of ` detector_large_value ` : ` 3 / 4 <_ e ^ ( -1 / Ypar D ) ` from ` 4 <_ Ypar D ` and ` log ( 4 / 3 ) >_ 1 / 4 ` (~ ld1yp , ~ zdmlogl1 , ~ lerec , ~ efle ).')
    A = HZH; P = parts(w, A); c, F = basecl(w, A, P)
    Q = '( 4 / 3 )'; R = '( 3 / 4 )'
    q1 = dst(w, A, [c.mem(Q, 'RR'), w.s([num.le_lit(w, '1', Q, strict=True)], 'a1i', '( %s -> 1 < %s )' % (A, Q))], 'jca', '( %s e. RR /\\ 1 < %s )' % (Q, Q))
    zl = ap(w, A, 'zdmlogl1', [q1], '( 1 - ( 1 / %s ) ) <_ ( log ` %s )' % (Q, Q))
    LQ = '( log ` %s )' % Q; LR = '( log ` %s )' % R
    for e_ in (LQ, LR, '( log ` 3 )', '( log ` 4 )'):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    rq = dst(w, A, [c.mem('4', 'CC'), c.mem('3', 'CC'), c.ne0('4'), c.ne0('3')], 'recdivd', '( 1 / %s ) = %s' % (Q, R))
    e14 = eqt(w, A, dst(w, A, [rq], 'oveq2d', '( 1 - ( 1 / %s ) ) = ( 1 - %s )' % (Q, R)), ringeq(w, A, '( 1 - %s )' % R, '( 1 / 4 )', c))
    l14 = dst(w, A, [eqc(w, A, e14), zl], 'eqbrtrd', '( 1 / 4 ) <_ %s' % LQ)
    d1 = dst(w, A, [c.mem('4', 'RR+'), c.mem('3', 'RR+')], 'relogdivd', '%s = ( ( log ` 4 ) - ( log ` 3 ) )' % LQ)
    d2 = dst(w, A, [c.mem('3', 'RR+'), c.mem('4', 'RR+')], 'relogdivd', '%s = ( ( log ` 3 ) - ( log ` 4 ) )' % LR)
    RY = '( 1 / %s )' % YP
    c.leaf(RY, 'RR', c.mem(RY, 'RR'))
    lr = ap(w, A, 'lerec', [J(w, A, c.mem('4', 'RR'), c.gt0('4')), J(w, A, c.mem(YP, 'RR'), c.gt0(YP))], '( 4 <_ %s <-> %s <_ ( 1 / 4 ) )' % (YP, RY))
    ry4 = dst(w, A, [F['y4'], lr], 'mpbid', '%s <_ ( 1 / 4 )' % RY)
    dn = dst(w, A, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A), c.mem(YP, 'CC'), c.ne0(YP)], 'divnegd', '-u %s = ( -u 1 / %s )' % (RY, YP))
    ln = linarith(w, A, [l14, d1, d2, ry4], '%s <_ -u %s' % (LR, RY), closure=c)
    ln2 = dst(w, A, [ln, dn], 'breqtrd', '%s <_ ( -u 1 / %s )' % (LR, YP))
    NY = '( -u 1 / %s )' % YP
    c.leaf(NY, 'RR', dst(w, A, [eqc(w, A, dn), c.mem('-u %s' % RY, 'RR')], 'eqeltrd', '%s e. RR' % NY))
    ef = ap(w, A, 'efle', [c.mem(LR, 'RR'), c.mem(NY, 'RR')], '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (LR, NY, LR, NY))
    e1 = dst(w, A, [ln2, ef], 'mpbid', '( exp ` %s ) <_ ( exp ` %s )' % (LR, NY))
    rl = ap(w, A, 'reeflog', [c.mem(R, 'RR+')], '( exp ` %s ) = %s' % (LR, R))
    dst(w, A, [eqc(w, A, rl), e1], 'eqbrtrd', '%s <_ ( exp ` %s )' % (R, NY))
    return fin(w)


def ld2epb():
    w = W('ld2epb', 'Lean ` hpole ` of ` detector_large_value ` : ` abs Epole <_ 1 / 8 ` , by ~ dshepb for the principal character (the height clause) and ~ dshep1 otherwise ( ` Epole = 0 ` ).')
    A = ante('ld2epb'); P, c, F = setupx(w, A)
    h0, rp3 = hab(w, A, F)
    sr = P[SRNGH]
    # ( 1 - S ) e. DG needs S =/= 1, which ld2epb does not have: dshep1 gives the value only
    cf = P['C : NN --> CC']; nn = P['N e. NN']; sc = P['S e. CC']; htc = P[HTC]
    cv = ap(w, A, 'fex', [cf, a1(w, A, 'nnex', 'NN e. _V')], 'C e. _V')
    EPB1 = '( ( ( ( _G ` ( 1 - S ) ) x. ( %s ^c ( 1 - S ) ) ) x. ( ( phi ` N ) / N ) ) x. ( %s ` 1 ) )' % (YP, MRF)
    val = ap(w, A, 'dshep1', [J(w, A, J(w, A, h0, F['yrp']), J(w, A, cv, nn)), sc], '%s = if ( C = %s , %s , 0 )' % (EPH('C'), PRN, EPB1))
    # case C = PRN
    A1 = '( %s /\\ C = %s )' % (A, PRN)
    ceq = w.s([], 'simpr', '( %s -> C = %s )' % (A1, PRN))
    ht = dst(w, A1, [ceq, lift(w, htc, A1)], 'mpd', '%s <_ %s' % (L, AIS))
    eb = ap(w, A1, 'dshepb', [J(w, A1, lift(w, P[HZH], A1), lift(w, nn, A1)), J(w, A1, lift(w, sr, A1), ht)], '( abs ` %s ) <_ ( 1 / 8 )' % EPH(PRN))
    ot = dst(w, A1, [ceq], 'oteq1d', '<. C , N , 1 >. = <. %s , N , 1 >.' % PRN)
    ov = dst(w, A1, [ot], 'oveq2d', '( <. D , %s , %s >. EPole <. C , N , 1 >. ) = ( <. D , %s , %s >. EPole <. %s , N , 1 >. )' % (D2, YP, D2, YP, PRN))
    fv = dst(w, A1, [ov], 'fveq1d', '%s = %s' % (EPH('C'), EPH(PRN)))
    k1 = dst(w, A1, [dst(w, A1, [fv], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (EPH('C'), EPH(PRN))), eb], 'eqbrtrd', '( abs ` %s ) <_ ( 1 / 8 )' % EPH('C'))
    # case C =/= PRN
    A2 = '( %s /\\ C =/= %s )' % (A, PRN)
    cne = w.s([], 'simpr', '( %s -> C =/= %s )' % (A2, PRN))
    v0 = eqt(w, A2, lift(w, val, A2), dst(w, A2, [dst(w, A2, [cne], 'neneqd', '-. C = %s' % PRN)], 'iffalsed', 'if ( C = %s , %s , 0 ) = 0' % (PRN, EPB1)))
    a0 = eqt(w, A2, dst(w, A2, [v0], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % EPH('C')), a1(w, A2, 'abs0', '( abs ` 0 ) = 0'))
    k2 = dst(w, A2, [a0, w.s([num.fact(w, '( 1 / 8 )', 'ge0')], 'a1i', '( %s -> 0 <_ ( 1 / 8 ) )' % A2)], 'eqbrtrd', '( abs ` %s ) <_ ( 1 / 8 )' % EPH('C'))
    w.s([k1, k2], 'pm2.61dane', '( %s -> ( abs ` %s ) <_ ( 1 / 8 ) )' % (A, EPH('C')))
    return fin(w)


def fdvcl(w, A, P, c, F, rp3, lo):
    """( A -> FDVH e. CC ) by ~ ld1fdv , ~ ld1ttcvg , ~ isumcl , proved under LD1's clean antecedent HA (A binds n through PRN) and transported by syl"""
    hz = P[HZH]; nn = P['N e. NN']; cfn = J(w, A, P['C : NN --> CC'], P[CB]); sc = P['S e. CC']
    re0 = linarith(w, A, [lo], '0 <_ ( Re ` S )', closure=c)
    ha = J(w, A, J(w, A, hz, nn), J(w, A, cfn, J(w, A, sc, re0)))
    assert body(w, ha, A) == HA
    B = HA; Q, cB, FB = setupx(w, B); h0B, rp3B = hab(w, B, FB)
    idB = w.s([], 'id', '( %s -> %s )' % (B, B))
    fv = ap(w, B, 'ld1fdv', [idB], concl('ld1fdv'))
    cv = dst(w, B, [ap(w, B, 'ld1ttcvg', [idB], concl('ld1ttcvg'))], 'simprd', 'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % TT('n'))
    FMn = '( n e. NN |-> %s )' % TT('n'); FMm = '( m e. NN |-> %s )' % TT('m')
    cg, _ = w.congr(TT('n'), {'n': 'm'}, 'n = m', {'n': w.s([], 'id', '( n = m -> n = m )')})
    me = w.s([cg], 'cbvmptv', '%s = %s' % (FMn, FMm))
    se = w.s([me, w.inst('seqeq3')], 'ax-mp', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (FMn, FMm))
    cvm = dst(w, B, [w.s([se], 'a1i', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (B, FMn, FMm)), cv], 'eqeltrrd', 'seq 1 ( + , %s ) e. dom ~~>' % FMm)
    Bn = '( %s /\\ n e. NN )' % B
    nN = w.s([], 'simpr', '( %s -> n e. NN )' % Bn)
    cn = liftcl(w, None, Bn, basefacts(FB)); termcl(w, Bn, cn, 'n', nN, FB, rp3B)
    ttc = cn.mem(TT('n'), 'CC')
    fvn = fvmd(w, Bn, 'm', 'NN', TT('m'), 'n', nN, ttc)
    sm = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % B), fvn, ttc, cvm], 'isumcl', '( %s -> sum_ n e. NN %s e. CC )' % (B, TT('n')))
    fc = dst(w, B, [fv, sm], 'eqeltrd', '%s e. CC' % FDVH)
    return w.s([ha, fc], 'syl', '( %s -> %s e. CC )' % (A, FDVH))


def ld2fdv():
    w = W('ld2fdv', 'Lean ` hF ` of ` detector_large_value ` : when ` abs E_ctr < 1 / 4 ` , ` abs F >_ 3 / 8 ` from the identity ~ dshdih , ~ ld2epb and ~ ld2exp ( ` e ^ ( -1 / Y ) >_ 3 / 4 ` ).')
    A = ante('ld2fdv'); P, c, F = setupx(w, A)
    h0, rp3 = hab(w, A, F)
    ecs = P[ECS]
    a7, sr, lo = a7h(w, A, P, c)
    di = ap(w, A, 'dshdih', [a7], concl('dshdih'))
    epc, _ = ephcl(w, A, P, c, F, h0, sr)
    ecc = ectrcl(w, A, P, c, sr)
    fdc = fdvcl(w, A, P, c, F, rp3, lo)
    eb = ap(w, A, 'ld2epb', [J(w, A, J(w, A, P[HZH], P['N e. NN']), J(w, A, J(w, A, P['C : NN --> CC'], sr), P[HTC]))], '( abs ` %s ) <_ ( 1 / 8 )' % EPH('C'))
    ex = ap(w, A, 'ld2exp', [P[HZH]], concl('ld2exp'))
    NY = '( -u 1 / %s )' % YP
    nyr = dst(w, A, [a1(w, A, 'neg1rr', '-u 1 e. RR'), c.mem(YP, 'RR+')], 'rerpdivcld', '%s e. RR' % NY)
    exr = dst(w, A, [nyr], 'rpefcld', '%s e. RR+' % EXH)
    c.leaf(EXH, 'RR+', exr)
    c.leaf(ECTRH, 'CC', ecc); c.leaf(EPH('C'), 'CC', epc); c.leaf(FDVH, 'CC', fdc)
    X = '( %s + %s )' % (ECTRH, EPH('C'))
    sub = dst(w, A, [c.mem(FDVH, 'CC'), c.mem(EXH, 'CC'), eqc(w, A, di)], 'mvrraddd', '( %s - %s ) = %s' % (X, EXH, FDVH))
    d1 = dst(w, A, [c.mem(EXH, 'CC'), c.mem(X, 'CC')], 'abs2difd', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (EXH, X, EXH, X))
    d2 = eqt(w, A, dst(w, A, [c.mem(EXH, 'CC'), c.mem(X, 'CC')], 'abssubd', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (EXH, X, X, EXH)),
             dst(w, A, [sub], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` %s )' % (X, EXH, FDVH)))
    d3 = dst(w, A, [d1, d2], 'breqtrd', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` %s )' % (EXH, X, FDVH))
    ai = dst(w, A, [c.mem(EXH, 'RR'), c.ge0(EXH)], 'absidd', '( abs ` %s ) = %s' % (EXH, EXH))
    tri = dst(w, A, [c.mem(ECTRH, 'CC'), c.mem(EPH('C'), 'CC')], 'abstrid', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (X, ECTRH, EPH('C')))
    for e_ in ('( abs ` %s )' % FDVH, '( abs ` %s )' % X, '( abs ` %s )' % ECTRH, '( abs ` %s )' % EPH('C'), '( abs ` %s )' % EXH):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    linarith(w, A, [d3, ai, tri, ecs, eb, ex], '( 3 / 8 ) <_ ( abs ` %s )' % FDVH, closure=c)
    return fin(w)


def ld2trl():
    w = W('ld2trl', 'Lean ` hS ` of ` detector_large_value ` : ` abs S >_ 1 / 4 ` for the truncation ` S ` , from ~ ld2fdv and L1.c ~ ld1trunc ( ` abs ( F - S ) <_ 1 / 8 ` ).')
    A = ante('ld2trl'); P, c, F = setupx(w, A)
    h0, rp3 = hab(w, A, F)
    a7, sr, lo = a7h(w, A, P, c)
    fd = ap(w, A, 'ld2fdv', [w.s([], 'id', '( %s -> %s )' % (A, A))], concl('ld2fdv'))
    cfn = J(w, A, P['C : NN --> CC'], P[CB])
    tr = ap(w, A, 'ld1trunc', [J(w, A, J(w, A, P[HZH], P['N e. NN']), J(w, A, cfn, sr))], concl('ld1trunc'))
    fdc = fdvcl(w, A, P, c, F, rp3, lo)
    B = '( ( %s /\\ %s ) /\\ S e. CC )' % (HZH, CFN)
    hb = J(w, A, J(w, A, P[HZH], cfn), P['S e. CC'])
    assert body(w, hb, A) == B
    Q, cB, FB = setupx(w, B); h0B, rp3B = hab(w, B, FB)
    Bn = '( %s /\\ n e. %s )' % (B, FZN)
    nN = ap(w, Bn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Bn, FZN))], 'n e. NN')
    cn = liftcl(w, None, Bn, basefacts(FB)); termcl(w, Bn, cn, 'n', nN, FB, rp3B)
    trcB = dst(w, B, [dst(w, B, [], 'fzfid', '%s e. Fin' % FZN), cn.mem(TT('n'), 'CC')], 'fsumcl', '%s e. CC' % TRUNC)
    trc = w.s([hb, trcB], 'syl', '( %s -> %s e. CC )' % (A, TRUNC))
    c.leaf(FDVH, 'CC', fdc); c.leaf(TRUNC, 'CC', trc)
    d1 = dst(w, A, [c.mem(FDVH, 'CC'), c.mem(TRUNC, 'CC')], 'abs2difd', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (FDVH, TRUNC, FDVH, TRUNC))
    for e_ in ('( abs ` %s )' % FDVH, '( abs ` %s )' % TRUNC, '( abs ` ( %s - %s ) )' % (FDVH, TRUNC)):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    linarith(w, A, [d1, fd, tr], '( 1 / 4 ) <_ ( abs ` %s )' % TRUNC, closure=c)
    return fin(w)


def ld2dlv():
    w = W('ld2dlv', '**Lean ` detector_large_value ` ** (L1.e, Proposition 2.8, at the L-function interface): either ` abs E_ctr >_ 1 / 4 ` or some Taylor component ` T_jk ` over the block range has modulus ` >_ 1 / ( 8 J ( J + 1 ) ) ` (~ ld2trl , ~ ld1exblkl , ~ ld1extay , ~ ld1tayeq ). DSH deviation 1: ` S =/= 1 ` for every character.')
    A = ante('ld2dlv'); P, c, F = setupx(w, A)
    a7, sr, lo = a7h(w, A, P, c)
    ecc = ectrcl(w, A, P, c, sr)
    AE = '( abs ` %s )' % ECTRH
    aer = dst(w, A, [ecc], 'abscld', '%s e. RR' % AE)
    BIG = '( 1 / 4 ) <_ %s' % AE
    CON = split_imp(STATEMENTS['ld2dlv'])[1]
    EX2 = CON.split(' \\/ ', 1)[1][:-2]
    # case 1: the contour term is large
    A1 = '( %s /\\ %s )' % (A, BIG)
    k1 = dst(w, A1, [w.s([], 'simpr', '( %s -> %s )' % (A1, BIG))], 'orcd', CON)
    # case 2: abs E_ctr < 1/4
    A2 = '( %s /\\ -. %s )' % (A, BIG)
    nb = w.s([], 'simpr', '( %s -> -. %s )' % (A2, BIG))
    r14 = w.s([num.real(w, '( 1 / 4 )')], 'a1i', '( %s -> ( 1 / 4 ) e. RR )' % A2)
    lt = dst(w, A2, [nb, dst(w, A2, [lift(w, aer, A2), r14], 'ltnled', '( %s < ( 1 / 4 ) <-> -. ( 1 / 4 ) <_ %s )' % (AE, AE))], 'mpbird', '%s < ( 1 / 4 )' % AE)
    trl = ap(w, A2, 'ld2trl', [J(w, A2, w.s([], 'simpl', '( %s -> %s )' % (A2, A)), lt)], concl('ld2trl'))
    cfn = J(w, A2, lift(w, P['C : NN --> CC'], A2), lift(w, P[CB], A2))
    hz2 = lift(w, P[HZH], A2); sc2 = lift(w, P['S e. CC'], A2)
    eb = ap(w, A2, 'ld1exblkl', [J(w, A2, J(w, A2, J(w, A2, hz2, cfn), sc2), trl)], concl('ld1exblkl'))
    # inside: m e. RJ, V4 <_ abs BLKSUM(m)
    Pm = '%s <_ ( abs ` %s )' % (V4, BLKSUM('m'))
    A3 = '( %s /\\ ( m e. %s /\\ %s ) )' % (A2, RJ, Pm)
    min_ = w.s([], 'simprl', '( %s -> m e. %s )' % (A3, RJ)); pm = w.s([], 'simprr', '( %s -> %s )' % (A3, Pm))
    mn0 = ap(w, A3, 'elfzonn0', [min_], 'm e. NN0'); mlt = ap(w, A3, 'elfzolt2', [min_], 'm < %s' % JPAR)
    hb = J(w, A3, J(w, A3, lift(w, P[HZH], A3), lift(w, cfn, A3)), J(w, A3, J(w, A3, lift(w, sc2, A3), lift(w, P['T e. RR'], A3)), lift(w, P[SIG], A3)))
    et = ap(w, A3, 'ld1extay', [J(w, A3, J(w, A3, hb, J(w, A3, mn0, mlt)), pm)], 'E. k e. %s %s <_ ( abs ` %s )' % (KJ, V8, TAYSUM('m', 'k', IS)))
    # the antecedent binds k (DSER): work with the Taylor index q and rename at the end
    Pk = '%s <_ ( abs ` %s )' % (V8, TAYSUM('m', 'k', IS))
    cgk, Pq = w.wcongr(Pk, {'k': 'q'}, 'k = q', {'k': w.s([], 'id', '( k = q -> k = q )')})
    bik = w.s([cgk], 'cbvrexvw', '( E. k e. %s %s <-> E. q e. %s %s )' % (KJ, Pk, KJ, Pq))
    etq = w.s([et, bik], 'sylib', '( %s -> E. q e. %s %s )' % (A3, KJ, Pq))
    A4 = '( %s /\\ ( q e. %s /\\ %s ) )' % (A3, KJ, Pq)
    kin = w.s([], 'simprl', '( %s -> q e. %s )' % (A4, KJ)); pk = w.s([], 'simprr', '( %s -> %s )' % (A4, Pq))
    kn0 = ap(w, A4, 'elfznn0', [kin], 'q e. NN0')
    isr = dst(w, A4, [lift(w, sc2, A4)], 'imcld', '%s e. RR' % IS)
    teq = ap(w, A4, 'ld1tayeq', [J(w, A4, J(w, A4, lift(w, P[HZH], A4), lift(w, cfn, A4)), J(w, A4, J(w, A4, lift(w, mn0, A4), kn0), J(w, A4, isr, lift(w, P['T e. RR'], A4))))],
             '%s = %s' % (TAYSUM('m', 'q', IS), TWIST('m', 'q', IS)))
    Pq2 = '%s <_ ( abs ` %s )' % (V8, TWIST('m', 'q', IS))
    pk2 = dst(w, A4, [pk, dst(w, A4, [teq], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (TAYSUM('m', 'q', IS), TWIST('m', 'q', IS)))], 'breqtrd', Pq2)
    e1 = w.s([pk2, etq], 'reximddv', '( %s -> E. q e. %s %s )' % (A3, KJ, Pq2))
    EXQ = 'E. m e. %s E. q e. %s %s' % (RJ, KJ, Pq2)
    e2q = w.s([e1, eb], 'reximddv', '( %s -> %s )' % (A2, EXQ))
    Pk2 = '%s <_ ( abs ` %s )' % (V8, TWIST('m', 'k', IS))
    cgq, Pk2b = w.wcongr(Pq2, {'q': 'k'}, 'q = k', {'q': w.s([], 'id', '( q = k -> q = k )')})
    assert Pk2b == Pk2
    biq = w.s([cgq], 'cbvrexvw', '( E. q e. %s %s <-> E. k e. %s %s )' % (KJ, Pq2, KJ, Pk2))
    bim = w.s([biq], 'rexbii', '( %s <-> %s )' % (EXQ, EX2))
    e2 = w.s([e2q, bim], 'sylib', '( %s -> %s )' % (A2, EX2))
    k2 = dst(w, A2, [e2], 'olcd', CON)
    w.s([k1, k2], 'pm2.61dan', '( %s -> %s )' % (A, CON))
    return fin(w)


def ld2dlvx():
    w = W('ld2dlvx', '**Lean ` detector_large_value ` ** (L1.e) at a set.mm Dirichlet character ` X ` mod ` N ` : ~ ld2dlv with the character values ` CX ` and the L-function ` N DChrLF X ` (~ zl1lif , ~ zl3cvxh , ~ zl1prn ), the Taylor components written with ` X ( n ) ` (LoggedDensity ` twistSum ` ).')
    A = ante('ld2dlvx'); P = parts(w, A)
    nn = P['N e. NN']; xb = P['X e. %s' % DB()]
    nx = J(w, A, nn, xb)
    CXX = CX(); LF = LFX()
    lif1 = ap(w, A, 'zl1lif', [nx], concl('zl1lif'))
    cvx = ap(w, A, 'zl3cvxh', [nx], concl('zl3cvxh'))
    prn = ap(w, A, 'zl1prn', [nx], concl('zl1prn'))
    Q = parts(w, A, top=body(w, lif1, A), step=lif1)
    CHRBX = subst(CHRB, {'C': CXX})
    EHOLX = subst(EHOL, {'E': LF}); E1X = '( %s ` 1 ) = %s' % (LF, subst(RESV, {'C': CXX}))
    DSERX = subst(DSER, {'C': CXX, 'E': LF}); CVXHX = subst(CVXH, {'E': LF})
    LIFX = subst(LIF, {'C': CXX, 'E': LF})
    assert LIFX == '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (EHOLX, E1X, DSERX, CVXHX)
    chrb = Q[CHRBX]; ehol = Q[EHOLX]; e1 = Q[E1X]; dser = Q[DSERX]
    lif = J(w, A, J(w, A, ehol, e1), J(w, A, dser, cvx))
    # the height clause for CX
    HTCX = subst(HTC, {'C': CXX})
    ht = w.s([dst(w, A, [prn], 'biimpd', '( %s = %s -> X = %s )' % (CXX, PRN, ZG)), P[HTX]], 'syld', '( %s -> %s )' % (A, HTCX))
    hd = J(w, A, J(w, A, J(w, A, P[HZH], nn), J(w, A, chrb, J(w, A, J(w, A, P['S e. CC'], J(w, A, P['T e. RR'], P[SIG])), P['S =/= 1']))),
           J(w, A, ht, J(w, A, lif, P['( %s ` S ) = 0' % LF])))
    HDLVX_ = subst(HDLV, {'C': CXX, 'E': LF})
    assert body(w, hd, A) == HDLVX_, (body(w, hd, A)[:300], HDLVX_[:300])
    dl = ap(w, A, 'ld2dlv', [hd], subst(split_imp(STATEMENTS['ld2dlv'])[1], {'C': CXX, 'E': LF}))
    # rewrite the character value inside the Taylor components
    CON = split_imp(STATEMENTS['ld2dlvx'])[1]
    TW1 = subst(TWIST('m', 'k', IS), {'C': CXX}); TW2 = TWISTX('m', 'k', IS)
    Am = '( %s /\\ m e. %s )' % (A, RJ); Amk = '( %s /\\ k e. %s )' % (Am, KJ); Amkn = '( %s /\\ n e. %s )' % (Amk, BLK('m'))
    nN = ap(w, Amkn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Amkn, BLK('m')))], 'n e. NN')
    cxf = dst(w, Amkn, [lift(w, Q['%s : NN --> CC' % CXX], Amkn), nN], 'ffvelcdmd', '( %s ` n ) e. CC' % CXX)
    fv = cxval(w, Amkn, nN)
    t1 = dst(w, Amkn, [fv], 'oveq2d', '( %s x. ( %s ` n ) ) = ( %s x. %s )' % (COEFF('m', 'k', 'n'), CXX, COEFF('m', 'k', 'n'), CHV('X', 'n')))
    t2 = dst(w, Amkn, [t1], 'oveq1d', '%s = %s' % (TSUMMAND('m', 'k', 'n', IS).replace('( C ` n )', '( %s ` n )' % CXX), TSX('m', 'k', 'n', IS)))
    se = dst(w, Amk, [t2], 'sumeq2dv', '%s = %s' % (TW1, TW2))
    bi = dst(w, Amk, [dst(w, Amk, [se], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (TW1, TW2))], 'breq2d', '( %s <_ ( abs ` %s ) <-> %s <_ ( abs ` %s ) )' % (V8, TW1, V8, TW2))
    b2 = dst(w, Am, [bi], 'rexbidva', '( E. k e. %s %s <_ ( abs ` %s ) <-> E. k e. %s %s <_ ( abs ` %s ) )' % (KJ, V8, TW1, KJ, V8, TW2))
    b3 = dst(w, A, [b2], 'rexbidva', '( E. m e. %s E. k e. %s %s <_ ( abs ` %s ) <-> E. m e. %s E. k e. %s %s <_ ( abs ` %s ) )' % (RJ, KJ, V8, TW1, RJ, KJ, V8, TW2))
    b4 = dst(w, A, [b3], 'orbi2d', '( %s <-> %s )' % (subst(split_imp(STATEMENTS['ld2dlv'])[1], {'C': CXX, 'E': LF}), CON))
    dst(w, A, [dl, b4], 'mpbid', CON)
    return fin(w)


if __name__ == '__main__':
    for f in (ld2exp, ld2epb, ld2fdv, ld2trl, ld2dlv, ld2dlvx):
        if want(f.__name__):
            f()
