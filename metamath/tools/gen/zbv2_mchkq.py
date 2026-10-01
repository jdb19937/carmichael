"""Sortie ZBV2, section 2 part A: the restricted Moebius check sum mChkQ
(ZBV2-blueprint.md section 3.1): value, closure, the special cases, the
recursion bvmchkqrec and the totient ratio lemmas.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *

PS = '( P ^c -u S )'


def hsfacts(w, A, hs):
    """from hs: ( A -> HS ): S e. RR, 1 <_ S, E e. RR, 0 <_ E, -u E e. RR, -u S e. RR"""
    st = mkst(w, A)
    sr = st([hs], 'simpld', 'S e. RR'); s1 = st([hs], 'simprd', '1 <_ S')
    er = st([sr, st([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % E)
    e0 = linarith(w, A, [s1], '0 <_ %s' % E, leaves={'S': sr})
    return dict(sr=sr, s1=s1, er=er, e0=e0, ner=st([er], 'renegcld', '%s e. RR' % NE), nsr=st([sr], 'renegcld', '-u S e. RR'))


def hpqfacts(w, A, hpq):
    """from hpq: ( A -> HPQ ): the prime P, Q e. NN, ( P gcd Q ) = 1 and their closures"""
    st = mkst(w, A)
    pp = st([hpq], 'simp1d', 'P e. Prime'); qnn = st([hpq], 'simp2d', 'Q e. NN'); g1 = st([hpq], 'simp3d', '( P gcd Q ) = 1')
    pnn = sy(w, A, pp, 'prmnn', 'P e. NN')
    d = dict(pp=pp, qnn=qnn, g1=g1, pnn=pnn, pz=st([pnn], 'nnzd', 'P e. ZZ'), pre=st([pnn], 'nnred', 'P e. RR'), pcc=st([pnn], 'nncnd', 'P e. CC'),
             prp=st([pnn], 'nnrpd', 'P e. RR+'), p1=sy(w, A, pp, 'prmgt1', '1 < P'), puz=sy(w, A, pp, 'prmuz2', 'P e. ( ZZ>= ` 2 )'),
             qz=st([qnn], 'nnzd', 'Q e. ZZ'), qre=st([qnn], 'nnred', 'Q e. RR'), qcc=st([qnn], 'nncnd', 'Q e. CC'), qrp=st([qnn], 'nnrpd', 'Q e. RR+'))
    d['pne'] = st([d['prp']], 'rpne0d', 'P =/= 0'); d['p0'] = st([d['prp']], 'rpge0d', '0 <_ P')
    d['p2'] = sy(w, A, d['puz'], 'eluzle', '2 <_ P')
    d['pqnn'] = st([pnn, qnn], 'nnmulcld', '%s e. NN' % PQ)
    d['pqz'] = st([d['pqnn']], 'nnzd', '%s e. ZZ' % PQ); d['pqcc'] = st([d['pqnn']], 'nncnd', '%s e. CC' % PQ); d['pqre'] = st([d['pqnn']], 'nnred', '%s e. RR' % PQ)
    d['qne'] = st([d['qrp']], 'rpne0d', 'Q =/= 0')
    return d


def ifqfacts(w, ante, k, q, x, knn, sr, xrp):
    """IFQ(k,q,x) and its term real and complex, from k e. NN (knn), S e. RR (sr), x e. RR+ (xrp)"""
    st = mkst(w, ante)
    T = '( ( ( mmu ` %s ) x. ( %s ^c -u S ) ) x. ( log ` ( %s / %s ) ) )' % (k, k, x, k)
    mf = mqfacts(w, ante, knn, k)
    krp = st([knn], 'nnrpd', '%s e. RR+' % k)
    ks = st([st([krp, st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '( %s ^c -u S ) e. RR+' % k)], 'rpred', '( %s ^c -u S ) e. RR' % k)
    lr = st([st([xrp, krp], 'rpdivcld', '( %s / %s ) e. RR+' % (x, k))], 'relogcld', '( log ` ( %s / %s ) ) e. RR' % (x, k))
    tr = st([st([mf['mur'], ks], 'remulcld', '( ( mmu ` %s ) x. ( %s ^c -u S ) ) e. RR' % (k, k)), lr], 'remulcld', '%s e. RR' % T)
    ir = st([tr, st([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFQ(k, q, x))
    return dict(T=T, tr=tr, tc=st([tr], 'recnd', '%s e. CC' % T), re=ir, cc=st([ir], 'recnd', '%s e. CC' % IFQ(k, q, x)), mf=mf, krp=krp, ks=ks, lr=lr)


def xrp_from_range(w, ante, nel, xr, x='X', n='n'):
    """from nel: ( ante -> n e. ( 1 ... ( |_ ` x ) ) ) and xr: ( ante -> x e. RR ): ( ante -> x e. RR+ )"""
    st = mkst(w, ante)
    n1 = sy(w, ante, nel, 'elfzle1', '1 <_ %s' % n); nfl = sy(w, ante, nel, 'elfzle2', '%s <_ ( |_ ` %s )' % (n, x))
    nre = st([sy(w, ante, nel, 'elfzelz', '%s e. ZZ' % n)], 'zred', '%s e. RR' % n)
    flr = sy(w, ante, xr, 'reflcl', '( |_ ` %s ) e. RR' % x)
    fl1 = linarith(w, ante, [n1, nfl], '1 <_ ( |_ ` %s )' % x, leaves={n: nre, '( |_ ` %s )' % x: flr})
    bi = sy2(w, ante, xr, st([clo(w, '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), 'flge', '( 1 <_ %s <-> 1 <_ ( |_ ` %s ) )' % (x, x))
    x1 = st([fl1, bi], 'mpbird', '1 <_ %s' % x)
    return st([xr, linarith(w, ante, [x1], '0 < %s' % x, leaves={x: xr})], 'elrpd', '%s e. RR+' % x), x1


A3 = '( S e. RR /\\ Q e. NN /\\ X e. RR )'
BODY = lambda s, q, x: 'sum_ n e. ( 1 ... ( |_ ` %s ) ) %s' % (x, IFQ('n', q, x, s))
MPO = lambda s: '( q e. NN , x e. RR |-> %s )' % BODY(s, 'q', 'x')


def bvmchkqval():
    w = W('bvmchkqval', 'The value of the restricted Moebius check sum: ( Q ( mChkQ ` S ) X ) is the sum over '
                        'n <= X coprime to Q of mmu ( n ) n ^c -u S log ( X / n ).')
    st = mkst(w, A3)
    sr = st([], 'simp1', 'S e. RR'); qnn = st([], 'simp2', 'Q e. NN'); xr = st([], 'simp3', 'X e. RR')
    ids = w.s([], 'id', '( s = S -> s = S )')
    h1, mpoS = w.congr(MPO('s'), {'s': 'S'}, 's = S', {'s': ids})
    assert mpoS == MPO('S'), mpoS
    h2 = w.s([], 'df-mchkq', 'mChkQ = ( s e. RR |-> %s )' % MPO('s'))
    h3 = w.s([w.s([], 'nnex', 'NN e. _V'), w.s([], 'reex', 'RR e. _V'), w.inst('mpoexga')], 'mp2an', '%s e. _V' % mpoS)
    fv = w.s([h1, h2, h3], 'fvmpt', '( S e. RR -> ( mChkQ ` S ) = %s )' % mpoS)
    fvd = st([sr, fv], 'syl', '( mChkQ ` S ) = %s' % mpoS)
    ov1 = st([fvd], 'oveqd', '%s = ( Q %s X )' % (MCQ('Q', 'X'), mpoS))
    EQ = '( q = Q /\\ x = X )'
    lq = w.s([], 'simpl', '( %s -> q = Q )' % EQ); lx = w.s([], 'simpr', '( %s -> x = X )' % EQ)
    g1, val = w.congr(BODY('S', 'q', 'x'), {'q': 'Q', 'x': 'X'}, EQ, {'q': lq, 'x': lx})
    assert val == QSUM('Q', 'X'), val
    g2 = w.s([], 'eqid', '%s = %s' % (mpoS, mpoS))
    ovg = w.s([g1, g2], 'ovmpoga', '( ( Q e. NN /\\ X e. RR /\\ %s e. _V ) -> ( Q %s X ) = %s )' % (val, mpoS, val))
    ex = st([clo(w, 'sumex', '%s e. _V' % val)], 'a1i', '%s e. _V' % val)
    ov2 = st([qnn, xr, ex, ovg], 'syl3anc', '( Q %s X ) = %s' % (mpoS, val))
    w.qed([ov1, ov2], 'eqtrd', STATEMENTS['bvmchkqval'])
    return w


def bvmchkqcl():
    w = W('bvmchkqcl', 'The restricted Moebius check sum is a real number.')
    st = mkst(w, A3)
    sr = st([], 'simp1', 'S e. RR'); qnn = st([], 'simp2', 'Q e. NN'); xr = st([], 'simp3', 'X e. RR')
    v = st([], 'bvmchkqval', '%s = %s' % (MCQ('Q', 'X'), QSUM('Q', 'X')))
    AN = '( %s /\\ n e. ( 1 ... ( |_ ` X ) ) )' % A3
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. ( 1 ... ( |_ ` X ) )')
    nnn = sy(w, AN, nel, 'elfznn', 'n e. NN')
    xrp, _ = xrp_from_range(w, AN, nel, lift(w, xr, AN))
    f = ifqfacts(w, AN, 'n', 'Q', 'X', nnn, lift(w, sr, AN), xrp)
    sumr = st([st([], 'fzfid', '( 1 ... ( |_ ` X ) ) e. Fin'), f['re']], 'fsumrecl', '%s e. RR' % QSUM('Q', 'X'))
    w.qed([v, sumr], 'eqeltrd', STATEMENTS['bvmchkqcl'])
    return w


def bvmchkq1():
    w = W('bvmchkq1', 'The check sum at Q = 1 is the unrestricted sigma sum of bvmchks (Lean mCheckQ_one).')
    A = '( S e. RR /\\ X e. RR )'
    st = mkst(w, A)
    sr = st([], 'simpl', 'S e. RR'); xr = st([], 'simpr', 'X e. RR')
    onenn = st([clo(w, '1nn', '1 e. NN')], 'a1i', '1 e. NN')
    v = st([sr, onenn, xr, w.inst('bvmchkqval')], 'syl3anc', '%s = %s' % (MCQ('1', 'X'), QSUM('1', 'X')))
    AN = '( %s /\\ n e. ( 1 ... ( |_ ` X ) ) )' % A
    sn = mkst(w, AN)
    nz = sy(w, AN, sn([], 'simpr', 'n e. ( 1 ... ( |_ ` X ) )'), 'elfzelz', 'n e. ZZ')
    g = sy(w, AN, nz, 'gcd1', '( n gcd 1 ) = 1')
    it = sn([g], 'iftrued', '%s = %s' % (IFQ('n', '1', 'X'), TERMX('n', 'X')))
    s = st([it], 'sumeq2dv', '%s = sum_ n e. ( 1 ... ( |_ ` X ) ) %s' % (QSUM('1', 'X'), TERMX('n', 'X')))
    w.qed([v, s], 'eqtrd', STATEMENTS['bvmchkq1'])
    return w


def bvmchkq0():
    w = W('bvmchkq0', 'The check sum vanishes for X < 1: the range ( 1 ... |_ X ) is empty (Lean mCheckQ_of_lt_one).')
    A = '( S e. RR /\\ Q e. NN /\\ ( X e. RR /\\ X < 1 ) )'
    st = mkst(w, A)
    sr = st([], 'simp1', 'S e. RR'); qnn = st([], 'simp2', 'Q e. NN'); hx = st([], 'simp3', '( X e. RR /\\ X < 1 )')
    xr = st([hx], 'simpld', 'X e. RR'); x1 = st([hx], 'simprd', 'X < 1')
    v = st([sr, qnn, xr, w.inst('bvmchkqval')], 'syl3anc', '%s = %s' % (MCQ('Q', 'X'), QSUM('Q', 'X')))
    onez = st([clo(w, '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ')
    fl = st([x1, sy2(w, A, xr, onez, 'fllt', '( X < 1 <-> ( |_ ` X ) < 1 )')], 'mpbid', '( |_ ` X ) < 1')
    emp = st([fl, sy2(w, A, onez, sy(w, A, xr, 'flcl', '( |_ ` X ) e. ZZ'), 'fzn', '( ( |_ ` X ) < 1 <-> ( 1 ... ( |_ ` X ) ) = (/) )')], 'mpbid', '( 1 ... ( |_ ` X ) ) = (/)')
    s0 = st([st([emp], 'sumeq1d', '%s = sum_ n e. (/) %s' % (QSUM('Q', 'X'), IFQ('n', 'Q', 'X'))), st([clo(w, 'sum0', 'sum_ n e. (/) %s = 0' % IFQ('n', 'Q', 'X'))], 'a1i', 'sum_ n e. (/) %s = 0' % IFQ('n', 'Q', 'X'))], 'eqtrd',
            '%s = 0' % QSUM('Q', 'X'))
    w.qed([v, s0], 'eqtrd', STATEMENTS['bvmchkq0'])
    return w


def bvmuprm():
    w = W('bvmuprm', 'The Moebius function of a prime is -u 1 (muval: no prime square divides P, and the prime '
                     'divisors of P are { P }).')
    A = 'P e. Prime'
    st = mkst(w, A)
    pp = st([], 'id', A)
    pnn = sy(w, A, pp, 'prmnn', 'P e. NN')
    AP = '( %s /\\ p e. Prime )' % A
    sp = mkst(w, AP)
    ppp = sp([], 'simpr', 'p e. Prime'); ppz = sy(w, AP, ppp, 'prmz', 'p e. ZZ'); ppre = sp([ppz], 'zred', 'p e. RR')
    p2 = sy(w, AP, sy(w, AP, ppp, 'prmuz2', 'p e. ( ZZ>= ` 2 )'), 'eluzle', '2 <_ p')
    sqz = sy(w, AP, ppz, 'zsqcl', '( p ^ 2 ) e. ZZ')
    sqv = sp([sp([ppz], 'zcnd', 'p e. CC')], 'sqvald', '( p ^ 2 ) = ( p x. p )')
    pp1 = sp([sp([], '1red', '1 e. RR'), ppre, ppre, linarith(w, AP, [p2], '0 <_ p', leaves={'p': ppre}), linarith(w, AP, [p2], '1 <_ p', leaves={'p': ppre})], 'lemul2ad', '( p x. 1 ) <_ ( p x. p )')
    pp1b = sp([sp([sp([sp([ppz], 'zcnd', 'p e. CC')], 'mulridd', '( p x. 1 ) = p')], 'eqcomd', 'p = ( p x. 1 )'), pp1], 'eqbrtrd', 'p <_ ( p x. p )')
    sq2 = linarith(w, AP, [p2, sp([pp1b, sp([sqv], 'eqcomd', '( p x. p ) = ( p ^ 2 )')], 'breqtrd', 'p <_ ( p ^ 2 )')], '2 <_ ( p ^ 2 )', leaves={'p': ppre, '( p ^ 2 )': sp([sqz], 'zred', '( p ^ 2 ) e. RR')})
    squz = sp([bind3(w, AP, sp([clo(w, '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), sqz, sq2, '2 e. ZZ', '( p ^ 2 ) e. ZZ', '2 <_ ( p ^ 2 )'), sp([clo(w, 'eluz2', '( ( p ^ 2 ) e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ ( p ^ 2 ) e. ZZ /\\ 2 <_ ( p ^ 2 ) ) )')], 'a1i', '( ( p ^ 2 ) e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ ( p ^ 2 ) e. ZZ /\\ 2 <_ ( p ^ 2 ) ) )')], 'mpbird',
              '( p ^ 2 ) e. ( ZZ>= ` 2 )')
    dp = sy2(w, AP, squz, lift(w, pp, AP), 'dvdsprm', '( ( p ^ 2 ) || P <-> ( p ^ 2 ) = P )')
    np = sy(w, AP, ppz, 'sqnprm', '-. ( p ^ 2 ) e. Prime')
    imp = sy(w, AP, lift(w, pp, AP), 'eleq1a', '( ( p ^ 2 ) = P -> ( p ^ 2 ) e. Prime )')
    nsq = sp([np, imp], 'mtod', '-. ( p ^ 2 ) = P')
    ndv = sp([nsq, dp], 'mtbird', '-. ( p ^ 2 ) || P')
    ral = st([ndv], 'ralrimiva', 'A. p e. Prime -. ( p ^ 2 ) || P')
    nex = st([ral, w.inst('ralnex')], 'sylib', '-. E. p e. Prime ( p ^ 2 ) || P')
    RAB = '{ p e. Prime | p || P }'
    mv = sy(w, A, pnn, 'muval', '( mmu ` P ) = if ( E. p e. Prime ( p ^ 2 ) || P , 0 , ( -u 1 ^ ( # ` %s ) ) )' % RAB)
    iff = st([nex], 'iffalsed', 'if ( E. p e. Prime ( p ^ 2 ) || P , 0 , ( -u 1 ^ ( # ` %s ) ) ) = ( -u 1 ^ ( # ` %s ) )' % (RAB, RAB))
    dq = sy2(w, AP, sy(w, AP, ppp, 'prmuz2', 'p e. ( ZZ>= ` 2 )'), lift(w, pp, AP), 'dvdsprm', '( p || P <-> p = P )')
    rb = st([dq], 'rabbidva', '%s = { p e. Prime | p = P }' % RAB)
    rs = sy(w, A, pp, 'rabsn', '{ p e. Prime | p = P } = { P }')
    hs = sy(w, A, pp, 'hashsng', '( # ` { P } ) = 1')
    heq = st([st([st([rb, rs], 'eqtrd', '%s = { P }' % RAB)], 'fveq2d', '( # ` %s ) = ( # ` { P } )' % RAB), hs], 'eqtrd', '( # ` %s ) = 1' % RAB)
    e1 = st([heq], 'oveq2d', '( -u 1 ^ ( # ` %s ) ) = ( -u 1 ^ 1 )' % RAB)
    e2 = st([w.s([w.s([], 'neg1cn', '-u 1 e. CC'), w.inst('exp1')], 'ax-mp', '( -u 1 ^ 1 ) = -u 1')], 'a1i', '( -u 1 ^ 1 ) = -u 1')
    w.qed([eqtr(w, A, [mv, iff, e1], None), e2], 'eqtrd', STATEMENTS['bvmuprm'])
    return w


def gcdne1(w, A, f, K, kz, pdk):
    """under A with hpqfacts f: from pdk: ( A -> P || K ) and kz: ( A -> K e. ZZ ): ( A -> -. ( K gcd ( P x. Q ) ) = 1 )"""
    st = mkst(w, A)
    G = '( %s gcd %s )' % (K, PQ)
    pdpq = sy2(w, A, f['pz'], f['qz'], 'dvdsmul1', 'P || %s' % PQ)
    dg = st([bind3(w, A, f['pz'], kz, f['pqz'], 'P e. ZZ', '%s e. ZZ' % K, '%s e. ZZ' % PQ), w.inst('dvdsgcd')], 'syl', '( ( P || %s /\\ P || %s ) -> P || %s )' % (K, PQ, G))
    pdg = st([bind(w, A, pdk, pdpq, 'P || %s' % K, 'P || %s' % PQ), dg], 'mpd', 'P || %s' % G)
    b = w.s([], 'breq2', '( %s = 1 -> ( P || %s <-> P || 1 ) )' % (G, G))
    im = st([pdg, b], 'syl5ibcom', '( %s = 1 -> P || 1 )' % G)
    d1 = sy(w, A, st([f['pnn']], 'nnnn0d', 'P e. NN0'), 'dvds1', '( P || 1 <-> P = 1 )')
    im2 = st([im, d1], 'sylibd', '( %s = 1 -> P = 1 )' % G)
    np1 = st([sy2(w, A, st([], '1red', '1 e. RR'), f['p1'], 'ltne', 'P =/= 1')], 'neneqd', '-. P = 1')
    return st([np1, im2], 'mtod', '-. %s = 1' % G)


def bvmchkqrec1():
    w = W('bvmchkqrec1', 'The pointwise split of the coprimality indicator for the recursion: the terms coprime '
                         'to Q are those coprime to P Q plus those divisible by P (P prime, ( P gcd Q ) = 1).')
    A = '( %s /\\ ( K e. NN /\\ ( S e. RR /\\ X e. RR+ ) ) )' % HPQ
    st = mkst(w, A)
    f = hpqfacts(w, A, st([], 'simpl', HPQ))
    knn = st([], 'simprl', 'K e. NN'); sx = st([], 'simprr', '( S e. RR /\\ X e. RR+ )')
    sr = st([sx], 'simpld', 'S e. RR'); xrp = st([sx], 'simprd', 'X e. RR+')
    kz = st([knn], 'nnzd', 'K e. ZZ')
    IQ = IFQ('K', 'Q', 'X'); IPQ = IFQ('K', PQ, 'X'); IFP = 'if ( P || K , %s , 0 )' % IQ
    fq = ifqfacts(w, A, 'K', 'Q', 'X', knn, sr, xrp)
    # case P || K
    A1 = '( %s /\\ P || K )' % A
    s1 = mkst(w, A1)
    pdk = s1([], 'simpr', 'P || K')
    ng = gcdne1(w, A1, {k: lift(w, v, A1) for k, v in f.items()}, 'K', lift(w, kz, A1), pdk)
    e1 = s1([ng], 'iffalsed', '%s = 0' % IPQ)
    e2 = s1([pdk], 'iftrued', '%s = %s' % (IFP, IQ))
    r1 = s1([s1([e1, e2], 'oveq12d', '( %s + %s ) = ( 0 + %s )' % (IPQ, IFP, IQ)), s1([lift(w, fq['cc'], A1)], 'addlidd', '( 0 + %s ) = %s' % (IQ, IQ))], 'eqtr2d', '%s = ( %s + %s )' % (IQ, IPQ, IFP))
    # case -. P || K
    A2 = '( %s /\\ -. P || K )' % A
    s2 = mkst(w, A2)
    npk = s2([], 'simpr', '-. P || K')
    f2 = {k: lift(w, v, A2) for k, v in f.items()}
    cp = s2([npk, sy2(w, A2, f2['pp'], lift(w, kz, A2), 'coprm', '( -. P || K <-> ( P gcd K ) = 1 )')], 'mpbid', '( P gcd K ) = 1')
    kp1 = s2([s2([lift(w, kz, A2), f2['pz']], 'gcdcomd', '( K gcd P ) = ( P gcd K )'), cp], 'eqtrd', '( K gcd P ) = 1')
    rm = w.s([bind3(w, A2, lift(w, knn, A2), f2['pnn'], f2['qnn'], 'K e. NN', 'P e. NN', 'Q e. NN'), kp1, w.inst('rpmulgcd')], 'syl2anc', '( %s -> ( K gcd %s ) = ( K gcd Q ) )' % (A2, PQ))
    bi = s2([rm], 'eqeq1d', '( ( K gcd %s ) = 1 <-> ( K gcd Q ) = 1 )' % PQ)
    e3 = s2([bi], 'ifbid', '%s = %s' % (IPQ, IQ))
    e4 = s2([npk], 'iffalsed', '%s = 0' % IFP)
    r2 = s2([s2([e3, e4], 'oveq12d', '( %s + %s ) = ( %s + 0 )' % (IPQ, IFP, IQ)), s2([lift(w, fq['cc'], A2)], 'addridd', '( %s + 0 ) = %s' % (IQ, IQ))], 'eqtr2d', '%s = ( %s + %s )' % (IQ, IPQ, IFP))
    w.qed([r1, r2], 'pm2.61dan', STATEMENTS['bvmchkqrec1'])
    return w


def bvmchkqrec2():
    w = W('bvmchkqrec2', 'The term at a multiple P M in the recursion: it is -u P ^c -u S times the term at M of the '
                         'check sum for P Q at X / P (mmu ( P M ) = -u mmu ( M ) for P not dividing M, and both vanish otherwise).')
    A = '( %s /\\ ( M e. NN /\\ ( S e. RR /\\ X e. RR+ ) ) )' % HPQ
    st = mkst(w, A)
    f = hpqfacts(w, A, st([], 'simpl', HPQ))
    mnn = st([], 'simprl', 'M e. NN'); sx = st([], 'simprr', '( S e. RR /\\ X e. RR+ )')
    sr = st([sx], 'simpld', 'S e. RR'); xrp = st([sx], 'simprd', 'X e. RR+')
    mz = st([mnn], 'nnzd', 'M e. ZZ'); mre = st([mnn], 'nnred', 'M e. RR'); mcc = st([mnn], 'nncnd', 'M e. CC'); mrp = st([mnn], 'nnrpd', 'M e. RR+')
    mne = st([mrp], 'rpne0d', 'M =/= 0'); m0 = st([mrp], 'rpge0d', '0 <_ M')
    PM = '( P x. M )'; XP = '( X / P )'
    pmnn = st([f['pnn'], mnn], 'nnmulcld', '%s e. NN' % PM); pmz = st([pmnn], 'nnzd', '%s e. ZZ' % PM)
    xprp = st([xrp, f['prp']], 'rpdivcld', '%s e. RR+' % XP)
    xc = st([xrp], 'rpcnd', 'X e. CC')
    fpm = ifqfacts(w, A, PM, 'Q', 'X', pmnn, sr, xrp)        # T1 = fpm['T']
    fm = ifqfacts(w, A, 'M', PQ, XP, mnn, sr, xprp)          # T2 = fm['T']
    T1, T2 = fpm['T'], fm['T']
    C1 = '( %s gcd Q ) = 1' % PM; C2 = '( M gcd %s ) = 1' % PQ
    LHS = IFQ(PM, 'Q', 'X'); IF2 = IFQ('M', PQ, XP); RHS = '( -u %s x. %s )' % (PS, IF2)
    nsc = st([st([sr], 'renegcld', '-u S e. RR')], 'recnd', '-u S e. CC')
    psrp = st([f['prp'], st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '%s e. RR+' % PS)
    psr = st([psrp], 'rpred', '%s e. RR' % PS); psc = st([psr], 'recnd', '%s e. CC' % PS); npsc = st([psc], 'negcld', '-u %s e. CC' % PS)
    # case P || M
    A1 = '( %s /\\ P || M )' % A
    s1 = mkst(w, A1)
    pdm = s1([], 'simpr', 'P || M')
    f1 = {k: lift(w, v, A1) for k, v in f.items()}
    cm = w.s([bind3(w, A1, f1['pz'], lift(w, mz, A1), f1['pz'], 'P e. ZZ', 'M e. ZZ', 'P e. ZZ'), w.inst('dvdscmul')], 'syl', '( %s -> ( P || M -> ( P x. P ) || %s ) )' % (A1, PM))
    ppd = s1([pdm, cm], 'mpd', '( P x. P ) || %s' % PM)
    p2d = s1([s1([f1['pcc']], 'sqvald', '( P ^ 2 ) = ( P x. P )'), ppd], 'eqbrtrd', '( P ^ 2 ) || %s' % PM)
    mu0 = w.s([lift(w, pmnn, A1), f1['puz'], p2d, w.inst('muval1')], 'syl3anc', '( %s -> ( mmu ` %s ) = 0 )' % (A1, PM))
    PMS = '( %s ^c -u S )' % PM; LG1 = '( log ` ( X / %s ) )' % PM
    t10 = eqtr(w, A1, [s1([s1([mu0], 'oveq1d', '( ( mmu ` %s ) x. %s ) = ( 0 x. %s )' % (PM, PMS, PMS))], 'oveq1d', '%s = ( ( 0 x. %s ) x. %s )' % (T1, PMS, LG1)),
                        s1([s1([s1([lift(w, fpm['ks'], A1)], 'recnd', '%s e. CC' % PMS)], 'mul02d', '( 0 x. %s ) = 0' % PMS)], 'oveq1d', '( ( 0 x. %s ) x. %s ) = ( 0 x. %s )' % (PMS, LG1, LG1)),
                        s1([s1([lift(w, fpm['lr'], A1)], 'recnd', '%s e. CC' % LG1)], 'mul02d', '( 0 x. %s ) = 0' % LG1)], None)
    lhs0 = s1([s1([t10], 'ifeq1d', '%s = if ( %s , 0 , 0 )' % (LHS, C1)), s1([clo(w, 'ifid', 'if ( %s , 0 , 0 ) = 0' % C1)], 'a1i', 'if ( %s , 0 , 0 ) = 0' % C1)], 'eqtrd', '%s = 0' % LHS)
    ng = gcdne1(w, A1, f1, 'M', lift(w, mz, A1), pdm)
    rhs0 = s1([s1([s1([ng], 'iffalsed', '%s = 0' % IF2)], 'oveq2d', '%s = ( -u %s x. 0 )' % (RHS, PS)), s1([lift(w, npsc, A1)], 'mul01d', '( -u %s x. 0 ) = 0' % PS)], 'eqtrd', '%s = 0' % RHS)
    c1 = s1([lhs0, rhs0], 'eqtr4d', '%s = %s' % (LHS, RHS))
    # case -. P || M
    A2 = '( %s /\\ -. P || M )' % A
    s2 = mkst(w, A2)
    npm = s2([], 'simpr', '-. P || M')
    f2 = {k: lift(w, v, A2) for k, v in f.items()}
    mz2 = lift(w, mz, A2)
    gpm = s2([npm, sy2(w, A2, f2['pp'], mz2, 'coprm', '( -. P || M <-> ( P gcd M ) = 1 )')], 'mpbid', '( P gcd M ) = 1')
    gmp = s2([s2([mz2, f2['pz']], 'gcdcomd', '( M gcd P ) = ( P gcd M )'), gpm], 'eqtrd', '( M gcd P ) = 1')
    r2 = w.s([bind3(w, A2, f2['qz'], f2['pz'], mz2, 'Q e. ZZ', 'P e. ZZ', 'M e. ZZ'), gpm, w.inst('rpmulgcd2')], 'syl2anc',
            '( %s -> ( Q gcd %s ) = ( ( Q gcd P ) x. ( Q gcd M ) ) )' % (A2, PM))
    gqp = s2([s2([f2['qz'], f2['pz']], 'gcdcomd', '( Q gcd P ) = ( P gcd Q )'), f2['g1']], 'eqtrd', '( Q gcd P ) = 1')
    gqmc = s2([s2([f2['qz'], mz2], 'gcdcld', '( Q gcd M ) e. NN0')], 'nn0cnd', '( Q gcd M ) e. CC')
    c1eq = eqtr(w, A2, [s2([lift(w, pmz, A2), f2['qz']], 'gcdcomd', '( %s gcd Q ) = ( Q gcd %s )' % (PM, PM)), r2,
                        s2([gqp], 'oveq1d', '( ( Q gcd P ) x. ( Q gcd M ) ) = ( 1 x. ( Q gcd M ) )'), s2([gqmc], 'mullidd', '( 1 x. ( Q gcd M ) ) = ( Q gcd M )'),
                        s2([f2['qz'], mz2], 'gcdcomd', '( Q gcd M ) = ( M gcd Q )')], None)
    c2eq = w.s([bind3(w, A2, lift(w, mnn, A2), f2['pnn'], f2['qnn'], 'M e. NN', 'P e. NN', 'Q e. NN'), gmp, w.inst('rpmulgcd')], 'syl2anc', '( %s -> ( M gcd %s ) = ( M gcd Q ) )' % (A2, PQ))
    bi = s2([s2([c1eq], 'eqeq1d', '( %s <-> ( M gcd Q ) = 1 )' % C1), s2([c2eq], 'eqeq1d', '( %s <-> ( M gcd Q ) = 1 )' % C2)], 'bitr4d', '( %s <-> %s )' % (C1, C2))
    # the values
    MUM = '( mmu ` M )'; MS = '( M ^c -u S )'; LL = '( log ` ( %s / M ) )' % XP
    mum = w.s([f2['pnn'], lift(w, mnn, A2), gpm, w.inst('mumul')], 'syl3anc', '( %s -> ( mmu ` %s ) = ( ( mmu ` P ) x. %s ) )' % (A2, PM, MUM))
    mup = sy(w, A2, f2['pp'], 'bvmuprm', '( mmu ` P ) = -u 1')
    mumc = lift(w, fm['mf']['muc'], A2)
    mueq = eqtr(w, A2, [mum, s2([mup], 'oveq1d', '( ( mmu ` P ) x. %s ) = ( -u 1 x. %s )' % (MUM, MUM)), s2([mumc], 'mulm1d', '( -u 1 x. %s ) = -u %s' % (MUM, MUM))], None)
    cx = s2([f2['pre'], f2['p0'], lift(w, mre, A2), lift(w, m0, A2), lift(w, nsc, A2)], 'mulcxpd', '( %s ^c -u S ) = ( %s x. %s )' % (PM, PS, MS))
    dd = s2([lift(w, xc, A2), f2['pcc'], lift(w, mcc, A2), f2['pne'], lift(w, mne, A2)], 'divdiv1d', '( %s / M ) = ( X / %s )' % (XP, PM))
    lg = s2([s2([dd], 'eqcomd', '( X / %s ) = ( %s / M )' % (PM, XP))], 'fveq2d', '( log ` ( X / %s ) ) = %s' % (PM, LL))
    t1eq = s2([s2([mueq, cx], 'oveq12d', '( ( mmu ` %s ) x. ( %s ^c -u S ) ) = ( -u %s x. ( %s x. %s ) )' % (PM, PM, MUM, PS, MS)), lg], 'oveq12d',
               '%s = ( ( -u %s x. ( %s x. %s ) ) x. %s )' % (T1, MUM, PS, MS, LL))
    ring = lineq(w, A2, '( ( -u %s x. ( %s x. %s ) ) x. %s )' % (MUM, PS, MS, LL), '( -u %s x. %s )' % (PS, T2), products=True,
                 leaves={MUM: lift(w, fm['mf']['mur'], A2), PS: lift(w, psr, A2), MS: lift(w, fm['ks'], A2), LL: lift(w, fm['lr'], A2)})
    t1eq2 = s2([t1eq, ring], 'eqtrd', '%s = ( -u %s x. %s )' % (T1, PS, T2))
    lhs = s2([s2([bi], 'ifbid', '%s = if ( %s , %s , 0 )' % (LHS, C2, T1)), s2([t1eq2], 'ifeq1d', 'if ( %s , %s , 0 ) = if ( %s , ( -u %s x. %s ) , 0 )' % (C2, T1, C2, PS, T2))], 'eqtrd',
             '%s = if ( %s , ( -u %s x. %s ) , 0 )' % (LHS, C2, PS, T2))
    ov = s2([clo(w, 'ovif2', '%s = if ( %s , ( -u %s x. %s ) , ( -u %s x. 0 ) )' % (RHS, C2, PS, T2, PS))], 'a1i', '%s = if ( %s , ( -u %s x. %s ) , ( -u %s x. 0 ) )' % (RHS, C2, PS, T2, PS))
    rhs = s2([ov, s2([s2([lift(w, npsc, A2)], 'mul01d', '( -u %s x. 0 ) = 0' % PS)], 'ifeq2d', 'if ( %s , ( -u %s x. %s ) , ( -u %s x. 0 ) ) = if ( %s , ( -u %s x. %s ) , 0 )' % (C2, PS, T2, PS, C2, PS, T2))], 'eqtrd',
             '%s = if ( %s , ( -u %s x. %s ) , 0 )' % (RHS, C2, PS, T2))
    c2 = s2([lhs, rhs], 'eqtr4d', '%s = %s' % (LHS, RHS))
    w.qed([c1, c2], 'pm2.61dan', STATEMENTS['bvmchkqrec2'])
    return w


def bvmchkqrec():
    w = W('bvmchkqrec', 'The q-recursion of the restricted check sum (Lean mCheckQ_rec, at q = P Q with '
                        '( P gcd Q ) = 1): m_Q ( X ) = m_PQ ( X ) - P ^c -u S m_PQ ( X / P ). The multiples of P are '
                        'reindexed by dvdsflf1o.')
    A = '( ( S e. RR /\\ X e. RR ) /\\ %s )' % HPQ
    st = mkst(w, A)
    sx = st([], 'simpl', '( S e. RR /\\ X e. RR )'); sr = st([sx], 'simpld', 'S e. RR'); xr = st([sx], 'simprd', 'X e. RR')
    f = hpqfacts(w, A, st([], 'simpr', HPQ))
    XP = '( X / P )'
    xpr = st([xr, f['pre'], f['pne']], 'redivcld', '%s e. RR' % XP)
    v1 = st([sr, f['qnn'], xr, w.inst('bvmchkqval')], 'syl3anc', '%s = %s' % (MCQ('Q', 'X'), QSUM('Q', 'X')))
    v2 = st([sr, f['pqnn'], xr, w.inst('bvmchkqval')], 'syl3anc', '%s = %s' % (MCQ(PQ, 'X'), QSUM(PQ, 'X')))
    v3 = st([sr, f['pqnn'], xpr, w.inst('bvmchkqval')], 'syl3anc', '%s = %s' % (MCQ(PQ, XP), QSUM(PQ, XP)))
    R1 = '( 1 ... ( |_ ` X ) )'; R2 = '( 1 ... ( |_ ` %s ) )' % XP
    FS = '{ x e. %s | P || x }' % R1
    IQ = lambda n: IFQ(n, 'Q', 'X'); IPQ = lambda n: IFQ(n, PQ, 'X'); IFP = lambda n: 'if ( P || %s , %s , 0 )' % (n, IQ(n))
    fin1 = st([], 'fzfid', '%s e. Fin' % R1); fin2 = st([], 'fzfid', '%s e. Fin' % R2)
    # under n e. R1
    AN = '( %s /\\ n e. %s )' % (A, R1)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % R1); nnn = sy(w, AN, nel, 'elfznn', 'n e. NN')
    xrp, _ = xrp_from_range(w, AN, nel, lift(w, xr, AN))
    fq = ifqfacts(w, AN, 'n', 'Q', 'X', nnn, lift(w, sr, AN), xrp)
    fpq = ifqfacts(w, AN, 'n', PQ, 'X', nnn, lift(w, sr, AN), xrp)
    ifpc = sn([fq['cc'], sn([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFP('n'))
    hpqn = lift(w, st([], 'simpr', HPQ), AN)
    ant = bind(w, AN, hpqn, bind(w, AN, nnn, bind(w, AN, lift(w, sr, AN), xrp, 'S e. RR', 'X e. RR+'), 'n e. NN', '( S e. RR /\\ X e. RR+ )'), HPQ, '( n e. NN /\\ ( S e. RR /\\ X e. RR+ ) )')
    rec1 = sn([ant, w.inst('bvmchkqrec1')], 'syl', '%s = ( %s + %s )' % (IQ('n'), IPQ('n'), IFP('n')))
    SIFP = 'sum_ n e. %s %s' % (R1, IFP('n'))
    s1 = st([rec1], 'sumeq2dv', '%s = sum_ n e. %s ( %s + %s )' % (QSUM('Q', 'X'), R1, IPQ('n'), IFP('n')))
    s2 = st([fin1, fpq['cc'], ifpc], 'fsumadd', 'sum_ n e. %s ( %s + %s ) = ( %s + %s )' % (R1, IPQ('n'), IFP('n'), QSUM(PQ, 'X'), SIFP))
    # the filtered sum
    SFS = 'sum_ n e. %s %s' % (FS, IFP('n')); SQF = 'sum_ n e. %s %s' % (FS, IQ('n'))
    sub = st([clo(w, 'ssrab2', '%s C_ %s' % (FS, R1))], 'a1i', '%s C_ %s' % (FS, R1))
    elr = w.s([w.s([], 'breq2', '( x = n -> ( P || x <-> P || n ) )')], 'elrab', '( n e. %s <-> ( n e. %s /\\ P || n ) )' % (FS, R1))
    ADF = '( %s /\\ n e. ( %s \\ %s ) )' % (A, R1, FS)
    sd = mkst(w, ADF)
    eld = sd([sd([], 'simpr', 'n e. ( %s \\ %s )' % (R1, FS)), w.inst('eldif')], 'sylib', '( n e. %s /\\ -. n e. %s )' % (R1, FS))
    nr1 = sd([eld], 'simpld', 'n e. %s' % R1); nfs = sd([eld], 'simprd', '-. n e. %s' % FS)
    nconj = sd([nfs, elr], 'sylnib', '-. ( n e. %s /\\ P || n )' % R1)
    imn = sd([nconj, w.inst('imnan')], 'sylibr', '( n e. %s -> -. P || n )' % R1)
    npn = sd([nr1, imn], 'mpd', '-. P || n')
    zero = sd([npn], 'iffalsed', '%s = 0' % IFP('n'))
    AFS = '( %s /\\ n e. %s )' % (A, FS)
    sf = mkst(w, AFS)
    elf = sf([sf([], 'simpr', 'n e. %s' % FS), elr], 'sylib', '( n e. %s /\\ P || n )' % R1)
    nr1f = sf([elf], 'simpld', 'n e. %s' % R1); pdn = sf([elf], 'simprd', 'P || n')
    nnnf = sy(w, AFS, nr1f, 'elfznn', 'n e. NN')
    xrpf, _ = xrp_from_range(w, AFS, nr1f, lift(w, xr, AFS))
    fqf = ifqfacts(w, AFS, 'n', 'Q', 'X', nnnf, lift(w, sr, AFS), xrpf)
    ifpcf = sf([fqf['cc'], sf([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFP('n'))
    fss = st([sub, ifpcf, zero, fin1], 'fsumss', '%s = %s' % (SFS, SIFP))
    itf = sf([pdn], 'iftrued', '%s = %s' % (IFP('n'), IQ('n')))
    sfs = st([itf], 'sumeq2dv', '%s = %s' % (SFS, SQF))
    # the bijection m |-> P m
    F = '( t e. %s |-> ( P x. t ) )' % R2
    bij = st([xr, f['pnn'], w.s([], 'eqid', '%s = %s' % (F, F))], 'dvdsflf1o', '%s : %s -1-1-onto-> %s' % (F, R2, FS))
    idn = w.s([], 'id', '( n = ( P x. m ) -> n = ( P x. m ) )')
    sub1, D = w.congr(IQ('n'), {'n': '( P x. m )'}, 'n = ( P x. m )', {'n': idn})
    assert D == IFQ('( P x. m )', 'Q', 'X'), D
    AM = '( %s /\\ m e. %s )' % (A, R2)
    sm = mkst(w, AM)
    mel = sm([], 'simpr', 'm e. %s' % R2)
    valm, _ = mpv(w, AM, 't', R2, '( P x. t )', 'm', mel)
    f1o = st([sub1, fin2, bij, valm, fqf['cc']], 'fsumf1o', '%s = sum_ m e. %s %s' % (SQF, R2, D))
    # under m e. R2: rec2
    mnn = sy(w, AM, mel, 'elfznn', 'm e. NN')
    xprp, xp1 = xrp_from_range(w, AM, mel, lift(w, xpr, AM), x=XP, n='m')
    xeq = sm([lift(w, st([xr], 'recnd', 'X e. CC'), AM), lift(w, f['pcc'], AM), lift(w, f['pne'], AM)], 'divcan1d', '( %s x. P ) = X' % XP)
    xrpm = sm([xeq, sm([xprp, lift(w, f['prp'], AM)], 'rpmulcld', '( %s x. P ) e. RR+' % XP)], 'eqeltrrd', 'X e. RR+')
    antm = bind(w, AM, lift(w, st([], 'simpr', HPQ), AM), bind(w, AM, mnn, bind(w, AM, lift(w, sr, AM), xrpm, 'S e. RR', 'X e. RR+'), 'm e. NN', '( S e. RR /\\ X e. RR+ )'), HPQ, '( m e. NN /\\ ( S e. RR /\\ X e. RR+ ) )')
    rec2 = sm([antm, w.inst('bvmchkqrec2')], 'syl', '%s = ( -u %s x. %s )' % (D, PS, IFQ('m', PQ, XP)))
    fm = ifqfacts(w, AM, 'm', PQ, XP, mnn, lift(w, sr, AM), xprp)
    s3 = st([rec2], 'sumeq2dv', 'sum_ m e. %s %s = sum_ m e. %s ( -u %s x. %s )' % (R2, D, R2, PS, IFQ('m', PQ, XP)))
    psc = st([st([st([f['prp'], st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '%s e. RR+' % PS)], 'rpred', '%s e. RR' % PS)], 'recnd', '%s e. CC' % PS)
    npsc = st([psc], 'negcld', '-u %s e. CC' % PS)
    QSm = 'sum_ m e. %s %s' % (R2, IFQ('m', PQ, XP))
    s4 = st([st([fin2, npsc, fm['cc']], 'fsummulc2', '( -u %s x. %s ) = sum_ m e. %s ( -u %s x. %s )' % (PS, QSm, R2, PS, IFQ('m', PQ, XP)))], 'eqcomd',
            'sum_ m e. %s ( -u %s x. %s ) = ( -u %s x. %s )' % (R2, PS, IFQ('m', PQ, XP), PS, QSm))
    idm = w.s([], 'id', '( m = n -> m = n )')
    cbs, cbnew = w.congr(IFQ('m', PQ, XP), {'m': 'n'}, 'm = n', {'m': idm})
    assert cbnew == IFQ('n', PQ, XP), cbnew
    cbv = w.s([cbs], 'cbvsumv', '%s = %s' % (QSm, QSUM(PQ, XP)))
    s4b = st([st([cbv], 'a1i', '%s = %s' % (QSm, QSUM(PQ, XP)))], 'oveq2d', '( -u %s x. %s ) = ( -u %s x. %s )' % (PS, QSm, PS, QSUM(PQ, XP)))
    m3c = st([st([sr, f['pqnn'], xpr, w.inst('bvmchkqcl')], 'syl3anc', '%s e. RR' % MCQ(PQ, XP))], 'recnd', '%s e. CC' % MCQ(PQ, XP))
    m2c = st([st([sr, f['pqnn'], xr, w.inst('bvmchkqcl')], 'syl3anc', '%s e. RR' % MCQ(PQ, 'X'))], 'recnd', '%s e. CC' % MCQ(PQ, 'X'))
    sifp = eqtr(w, A, [st([fss], 'eqcomd', '%s = %s' % (SIFP, SFS)), sfs, f1o, s3, s4, s4b, st([st([v3], 'eqcomd', '%s = %s' % (QSUM(PQ, XP), MCQ(PQ, XP)))], 'oveq2d', '( -u %s x. %s ) = ( -u %s x. %s )' % (PS, QSUM(PQ, XP), PS, MCQ(PQ, XP)))], None)
    o1 = st([st([v2], 'eqcomd', '%s = %s' % (QSUM(PQ, 'X'), MCQ(PQ, 'X'))), sifp], 'oveq12d', '( %s + %s ) = ( %s + ( -u %s x. %s ) )' % (QSUM(PQ, 'X'), SIFP, MCQ(PQ, 'X'), PS, MCQ(PQ, XP)))
    o2 = st([st([psc, m3c], 'mulneg1d', '( -u %s x. %s ) = -u ( %s x. %s )' % (PS, MCQ(PQ, XP), PS, MCQ(PQ, XP)))], 'oveq2d', '( %s + ( -u %s x. %s ) ) = ( %s + -u ( %s x. %s ) )' % (MCQ(PQ, 'X'), PS, MCQ(PQ, XP), MCQ(PQ, 'X'), PS, MCQ(PQ, XP)))
    o3 = st([m2c, st([psc, m3c], 'mulcld', '( %s x. %s ) e. CC' % (PS, MCQ(PQ, XP)))], 'negsubd', '( %s + -u ( %s x. %s ) ) = ( %s - ( %s x. %s ) )' % (MCQ(PQ, 'X'), PS, MCQ(PQ, XP), MCQ(PQ, 'X'), PS, MCQ(PQ, XP)))
    w.qed([eqtr(w, A, [v1, s1, s2, o1, o2], None), o3], 'eqtrd', STATEMENTS['bvmchkqrec'])
    return w


def bvmchkqle1():
    w = W('bvmchkqle1', 'Q / phi ( Q ) is at least 1 (phibnd for Q >= 2, phi1).')
    A = 'Q e. NN'
    st = mkst(w, A)
    qnn = st([], 'id', A); qre = st([qnn], 'nnred', 'Q e. RR')
    phinn = sy(w, A, qnn, 'phicl', '( phi ` Q ) e. NN'); phirp = st([phinn], 'nnrpd', '( phi ` Q ) e. RR+')
    phire = st([phirp], 'rpred', '( phi ` Q ) e. RR'); phic = st([phire], 'recnd', '( phi ` Q ) e. CC'); phine = st([phirp], 'rpne0d', '( phi ` Q ) =/= 0')
    A1 = '( %s /\\ Q = 1 )' % A
    s1 = mkst(w, A1)
    q1 = s1([], 'simpr', 'Q = 1')
    req = eqtr(w, A1, [s1([q1, s1([q1], 'fveq2d', '( phi ` Q ) = ( phi ` 1 )')], 'oveq12d', '%s = ( 1 / ( phi ` 1 ) )' % RAT('Q')),
                       s1([s1([clo(w, 'phi1', '( phi ` 1 ) = 1')], 'a1i', '( phi ` 1 ) = 1')], 'oveq2d', '( 1 / ( phi ` 1 ) ) = ( 1 / 1 )'),
                       s1([clo(w, '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( 1 / 1 ) = 1')], None)
    c1 = s1([s1([clo(w, '1le1', '1 <_ 1')], 'a1i', '1 <_ 1'), req], 'breqtrrd', '1 <_ %s' % RAT('Q'))
    A2 = '( %s /\\ Q e. ( ZZ>= ` 2 ) )' % A
    s2 = mkst(w, A2)
    pb = sy(w, A2, s2([], 'simpr', 'Q e. ( ZZ>= ` 2 )'), 'phibnd', '( phi ` Q ) <_ ( Q - 1 )')
    ple = linarith(w, A2, [pb], '( phi ` Q ) <_ Q', leaves={'( phi ` Q )': lift(w, phire, A2), 'Q': lift(w, qre, A2)})
    ld = s2([lift(w, phire, A2), lift(w, qre, A2), lift(w, phirp, A2), ple], 'lediv1dd', '( ( phi ` Q ) / ( phi ` Q ) ) <_ %s' % RAT('Q'))
    c2 = s2([s2([lift(w, phic, A2), lift(w, phine, A2)], 'dividd', '( ( phi ` Q ) / ( phi ` Q ) ) = 1'), ld], 'eqbrtrrd', '1 <_ %s' % RAT('Q'))
    bi = st([clo(w, 'elnn1uz2', '( Q e. NN <-> ( Q = 1 \\/ Q e. ( ZZ>= ` 2 ) ) )')], 'a1i', '( Q e. NN <-> ( Q = 1 \\/ Q e. ( ZZ>= ` 2 ) ) )')
    w.qed([c1, c2, st([qnn, bi], 'mpbid', '( Q = 1 \\/ Q e. ( ZZ>= ` 2 ) )')], 'mpjaodan', STATEMENTS['bvmchkqle1'])
    return w


def dfacts_p(w, A, f):
    """( P - 1 ) e. RR, RR+, CC, =/= 0 from hpqfacts f"""
    st = mkst(w, A)
    D = '( P - 1 )'
    dre = st([f['pre'], st([], '1red', '1 e. RR')], 'resubcld', '%s e. RR' % D)
    d0 = st([f['p1'], st([st([], '1red', '1 e. RR'), f['pre']], 'posdifd', '( 1 < P <-> 0 < %s )' % D)], 'mpbid', '0 < %s' % D)
    drp = st([dre, d0], 'elrpd', '%s e. RR+' % D)
    return dict(re=dre, rp=drp, cc=st([dre], 'recnd', '%s e. CC' % D), ne=st([drp], 'rpne0d', '%s =/= 0' % D))


def bvmchkqrat():
    w = W('bvmchkqrat', 'The totient ratio of P Q splits: ( P Q ) / phi ( P Q ) = ( P / ( P - 1 ) ) ( Q / phi ( Q ) ) (phimul, phiprm).')
    A = HPQ
    st = mkst(w, A)
    f = hpqfacts(w, A, st([], 'id', A))
    d = dfacts_p(w, A, f)
    pm = st([f['pnn'], f['qnn'], f['g1'], w.inst('phimul')], 'syl3anc', '( phi ` %s ) = ( ( phi ` P ) x. ( phi ` Q ) )' % PQ)
    pp = sy(w, A, f['pp'], 'phiprm', '( phi ` P ) = ( P - 1 )')
    phieq = st([pm, st([pp], 'oveq1d', '( ( phi ` P ) x. ( phi ` Q ) ) = ( ( P - 1 ) x. ( phi ` Q ) )')], 'eqtrd', '( phi ` %s ) = ( ( P - 1 ) x. ( phi ` Q ) )' % PQ)
    phiq = sy(w, A, f['qnn'], 'phicl', '( phi ` Q ) e. NN'); phiqc = st([phiq], 'nncnd', '( phi ` Q ) e. CC'); phiqne = st([st([phiq], 'nnrpd', '( phi ` Q ) e. RR+')], 'rpne0d', '( phi ` Q ) =/= 0')
    dm = st([f['pcc'], d['cc'], f['qcc'], phiqc, d['ne'], phiqne], 'divmuldivd', '( ( P / ( P - 1 ) ) x. %s ) = ( %s / ( ( P - 1 ) x. ( phi ` Q ) ) )' % (RAT('Q'), PQ))
    lhs = st([phieq], 'oveq2d', '%s = ( %s / ( ( P - 1 ) x. ( phi ` Q ) ) )' % (RAT(PQ), PQ))
    w.qed([lhs, dm], 'eqtr4d', STATEMENTS['bvmchkqrat'])
    return w


def bvmchkqratlem():
    w = W('bvmchkqratlem', 'The field identity 1 + ( 1 / P ) ( P / ( P - 1 ) ) = P / ( P - 1 ) of the recursion assembly.')
    A = '( P e. RR /\\ 1 < P )'
    st = mkst(w, A)
    pre = st([], 'simpl', 'P e. RR'); p1 = st([], 'simpr', '1 < P')
    pc = st([pre], 'recnd', 'P e. CC'); pne = st([linarith(w, A, [p1], '0 < P', leaves={'P': pre})], 'gt0ne0d', 'P =/= 0')
    D = '( P - 1 )'; one = st([], '1red', '1 e. RR'); onec = st([], '1cnd', '1 e. CC')
    dre = st([pre, one], 'resubcld', '%s e. RR' % D)
    d0 = st([p1, st([one, pre], 'posdifd', '( 1 < P <-> 0 < %s )' % D)], 'mpbid', '0 < %s' % D)
    dc = st([dre], 'recnd', '%s e. CC' % D); dne = st([d0], 'gt0ne0d', '%s =/= 0' % D)
    rpc = st([pc, pne], 'reccld', '( 1 / P ) e. CC')
    e1 = eqtr(w, A, [st([st([rpc, pc, dc, dne], 'divassd', '( ( ( 1 / P ) x. P ) / %s ) = ( ( 1 / P ) x. ( P / %s ) )' % (D, D))], 'eqcomd', '( ( 1 / P ) x. ( P / %s ) ) = ( ( ( 1 / P ) x. P ) / %s )' % (D, D)),
                     st([st([pc, pne], 'recid2d', '( ( 1 / P ) x. P ) = 1')], 'oveq1d', '( ( ( 1 / P ) x. P ) / %s ) = ( 1 / %s )' % (D, D))], None)
    e2 = st([st([dc, onec, dc, dne], 'divdird', '( ( %s + 1 ) / %s ) = ( ( %s / %s ) + ( 1 / %s ) )' % (D, D, D, D, D)), st([st([dc, dne], 'dividd', '( %s / %s ) = 1' % (D, D))], 'oveq1d', '( ( %s / %s ) + ( 1 / %s ) ) = ( 1 + ( 1 / %s ) )' % (D, D, D, D))], 'eqtr2d',
            '( 1 + ( 1 / %s ) ) = ( ( %s + 1 ) / %s )' % (D, D, D))
    e3 = st([st([pc, onec], 'npcand', '( %s + 1 ) = P' % D)], 'oveq1d', '( ( %s + 1 ) / %s ) = ( P / %s )' % (D, D, D))
    w.qed([eqtr(w, A, [st([e1], 'oveq2d', '( 1 + ( ( 1 / P ) x. ( P / %s ) ) ) = ( 1 + ( 1 / %s ) )' % (D, D)), e2], None), e3], 'eqtrd', STATEMENTS['bvmchkqratlem'])
    return w


def bqfacts(w, A, hs, qnn, xr, x1, q='Q', x='X'):
    """under A: RAT(q) real and >= 1, ( RAT x. M113 ) real and >= 0, L = ( 1 + ( E x. log x ) ) real and >= 1, BQ(q,x) real"""
    st = mkst(w, A)
    h = hsfacts(w, A, hs)
    phinn = sy(w, A, qnn, 'phicl', '( phi ` %s ) e. NN' % q)
    ratre = st([st([qnn], 'nnred', '%s e. RR' % q), st([phinn], 'nnrpd', '( phi ` %s ) e. RR+' % q)], 'rerpdivcld', '%s e. RR' % RAT(q))
    rat1 = sy(w, A, qnn, 'bvmchkqle1', '1 <_ %s' % RAT(q))
    cl = Closure(w, A)
    m113r = cl.mem(M113, 'RR'); m113_0 = cl.ge0(M113)
    RM = '( %s x. %s )' % (RAT(q), M113)
    rmre = st([ratre, m113r], 'remulcld', '%s e. RR' % RM)
    rm0 = st([ratre, m113r, linarith(w, A, [rat1], '0 <_ %s' % RAT(q), leaves={RAT(q): ratre}), m113_0], 'mulge0d', '0 <_ %s' % RM)
    lgr = st([st([xr, linarith(w, A, [x1], '0 < %s' % x, leaves={x: xr})], 'elrpd', '%s e. RR+' % x)], 'relogcld', '( log ` %s ) e. RR' % x)
    lg0 = sy2(w, A, xr, x1, 'logge0', '0 <_ ( log ` %s )' % x)
    ELG = '( %s x. ( log ` %s ) )' % (E, x)
    elgr = st([h['er'], lgr], 'remulcld', '%s e. RR' % ELG)
    elg0 = st([h['er'], lgr, h['e0'], lg0], 'mulge0d', '0 <_ %s' % ELG)
    L = '( 1 + %s )' % ELG
    lre = st([st([], '1red', '1 e. RR'), elgr], 'readdcld', '%s e. RR' % L)
    l1 = linarith(w, A, [elg0], '1 <_ %s' % L, leaves={ELG: elgr})
    bqre = st([rmre, lre], 'remulcld', '%s e. RR' % BQ(q, x))
    return dict(h=h, ratre=ratre, rat1=rat1, RM=RM, rmre=rmre, rm0=rm0, L=L, lre=lre, l1=l1, ELG=ELG, elgr=elgr, lgr=lgr, m113r=m113r, bqre=bqre)


def bvmchkqbq0():
    w = W('bvmchkqbq0', 'The bound of bvmchkq is nonnegative.')
    A = '( %s /\\ ( Q e. NN /\\ ( X e. RR /\\ 1 <_ X ) ) )' % HS
    st = mkst(w, A)
    hs = st([], 'simpl', HS); qnn = st([], 'simprl', 'Q e. NN'); hx = st([], 'simprr', '( X e. RR /\\ 1 <_ X )')
    b = bqfacts(w, A, hs, qnn, st([hx], 'simpld', 'X e. RR'), st([hx], 'simprd', '1 <_ X'))
    w.qed([b['rmre'], b['lre'], b['rm0'], linarith(w, A, [b['l1']], '0 <_ %s' % b['L'], leaves={b['ELG']: b['elgr']})], 'mulge0d', STATEMENTS['bvmchkqbq0'])
    return w


def bvmchkqbqle():
    w = W('bvmchkqbqle', 'The bound of bvmchkq is monotone in X.')
    A = '( %s /\\ ( Q e. NN /\\ ( ( X e. RR /\\ 1 <_ X ) /\\ ( Z e. RR /\\ 1 <_ Z /\\ Z <_ X ) ) ) )' % HS
    st = mkst(w, A)
    hs = st([], 'simpl', HS); qnn = st([], 'simprl', 'Q e. NN'); hxz = st([], 'simprr', '( ( X e. RR /\\ 1 <_ X ) /\\ ( Z e. RR /\\ 1 <_ Z /\\ Z <_ X ) )')
    hx = st([hxz], 'simpld', '( X e. RR /\\ 1 <_ X )'); hz = st([hxz], 'simprd', '( Z e. RR /\\ 1 <_ Z /\\ Z <_ X )')
    xr = st([hx], 'simpld', 'X e. RR'); x1 = st([hx], 'simprd', '1 <_ X')
    zr = st([hz], 'simp1d', 'Z e. RR'); z1 = st([hz], 'simp2d', '1 <_ Z'); zx = st([hz], 'simp3d', 'Z <_ X')
    b = bqfacts(w, A, hs, qnn, xr, x1)
    zrp = st([zr, linarith(w, A, [z1], '0 < Z', leaves={'Z': zr})], 'elrpd', 'Z e. RR+'); xrp = st([xr, linarith(w, A, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    lzr = st([zrp], 'relogcld', '( log ` Z ) e. RR')
    ll = st([zx, sy2(w, A, zrp, xrp, 'logleb', '( Z <_ X <-> ( log ` Z ) <_ ( log ` X ) )')], 'mpbid', '( log ` Z ) <_ ( log ` X )')
    ELZ = '( %s x. ( log ` Z ) )' % E
    elz = st([lzr, b['lgr'], b['h']['er'], b['h']['e0'], ll], 'lemul2ad', '%s <_ %s' % (ELZ, b['ELG']))
    elzr = st([b['h']['er'], lzr], 'remulcld', '%s e. RR' % ELZ)
    LZ = '( 1 + %s )' % ELZ
    lzre = st([st([], '1red', '1 e. RR'), elzr], 'readdcld', '%s e. RR' % LZ)
    le2 = linarith(w, A, [elz], '%s <_ %s' % (LZ, b['L']), leaves={ELZ: elzr, b['ELG']: b['elgr']})
    w.qed([lzre, b['lre'], b['rmre'], b['rm0'], le2], 'lemul2ad', STATEMENTS['bvmchkqbqle'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvmchkqval', 'bvmchkqcl', 'bvmchkq1', 'bvmchkq0', 'bvmuprm', 'bvmchkqrec1', 'bvmchkqrec2', 'bvmchkqrec', 'bvmchkqle1', 'bvmchkqrat', 'bvmchkqratlem', 'bvmchkqbq0', 'bvmchkqbqle']:
        globals()[f]().run()
