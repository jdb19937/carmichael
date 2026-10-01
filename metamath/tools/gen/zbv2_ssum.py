"""Sortie ZBV2, section 4 part C1: the Barban-Vehov weight and S_delta in terms of mChkQ
(Lean Ssum_eq_mCheckQ, abs_Ssum_le), ZBV2-blueprint.md section 3.3.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zbv2lib import *
import num
import lin
lin.MAXDEG = 5


def bvmunc():
    w = W('bvmunc', 'The Moebius function vanishes on a product of two non-coprime numbers (a common prime p gives '
                    'p ^ 2 || M K; muval1).')
    A = '( ( M e. NN /\\ K e. NN ) /\\ -. ( K gcd M ) = 1 )'
    st = mkst(w, A)
    mnn = st([], 'simpll', 'M e. NN'); knn = st([], 'simplr', 'K e. NN'); ng = st([], 'simpr', '-. ( K gcd M ) = 1')
    G = '( K gcd M )'
    mz = st([mnn], 'nnzd', 'M e. ZZ'); kz = st([knn], 'nnzd', 'K e. ZZ')
    gnn = st([knn, mnn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % G)
    gne = st([ng], 'neqned', '%s =/= 1' % G)
    guz = st([st([gnn, gne], 'jca', '( %s e. NN /\\ %s =/= 1 )' % (G, G)), w.inst('eluz2b3')], 'sylibr', '%s e. ( ZZ>= ` 2 )' % G)
    ex = sy(w, A, guz, 'exprmfct', 'E. p e. Prime p || %s' % G)
    AP = '( %s /\\ p e. Prime )' % A
    AP2 = '( %s /\\ p || %s )' % (AP, G)
    s2 = mkst(w, AP2)
    pp = s2([], 'simplr', 'p e. Prime')
    pnn = sy(w, AP2, pp, 'prmnn', 'p e. NN')
    pz = s2([pnn], 'nnzd', 'p e. ZZ')
    pdg = s2([], 'simpr', 'p || %s' % G)
    mz2 = lift(w, mz, AP2); kz2 = lift(w, kz, AP2)
    gz = s2([lift(w, gnn, AP2)], 'nnzd', '%s e. ZZ' % G)
    gd = s2([kz2, mz2, w.inst('gcddvds')], 'syl2anc', '( %s || K /\\ %s || M )' % (G, G))
    pk = s2([s2([pdg, s2([gd], 'simpld', '%s || K' % G)], 'jca', '( p || %s /\\ %s || K )' % (G, G)),
             s2([pz, gz, kz2, w.inst('dvdstr')], 'syl3anc', '( ( p || %s /\\ %s || K ) -> p || K )' % (G, G))], 'mpd', 'p || K')
    pm = s2([s2([pdg, s2([gd], 'simprd', '%s || M' % G)], 'jca', '( p || %s /\\ %s || M )' % (G, G)),
             s2([pz, gz, mz2, w.inst('dvdstr')], 'syl3anc', '( ( p || %s /\\ %s || M ) -> p || M )' % (G, G))], 'mpd', 'p || M')
    pp2 = s2([s2([pz, pz], 'jca', '( p e. ZZ /\\ p e. ZZ )'), s2([mz2, kz2], 'jca', '( M e. ZZ /\\ K e. ZZ )'),
              s2([pm, pk], 'jca', '( p || M /\\ p || K )'), w.inst('dvdsmul12')], 'syl3anc', '( p x. p ) || ( M x. K )')
    sq = s2([s2([pnn], 'nncnd', 'p e. CC')], 'sqvald', '( p ^ 2 ) = ( p x. p )')
    psq = s2([sq, pp2], 'eqbrtrd', '( p ^ 2 ) || ( M x. K )')
    mk = s2([lift(w, mnn, AP2), lift(w, knn, AP2)], 'nnmulcld', '( M x. K ) e. NN')
    z = s2([mk, sy(w, AP2, pp, 'prmuz2', 'p e. ( ZZ>= ` 2 )'), psq, w.inst('muval1')], 'syl3anc', '( mmu ` ( M x. K ) ) = 0')
    im = w.s([z], 'ex', '( %s -> ( p || %s -> ( mmu ` ( M x. K ) ) = 0 ) )' % (AP, G))
    rl = w.s([im], 'rexlimdva', '( %s -> ( E. p e. Prime p || %s -> ( mmu ` ( M x. K ) ) = 0 ) )' % (A, G))
    w.qed([ex, rl], 'mpd', STATEMENTS['bvmunc'])
    return w


def plfacts(w, ante, xrp, x):
    """PL(x) e. RR from x e. RR+"""
    st = mkst(w, ante)
    lr = st([xrp], 'relogcld', '( log ` %s ) e. RR' % x)
    return st([lr, st([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % PL(x))


def ifpfacts(w, ante, knn, sr, xrp, k, q, x):
    """IFP(k,q,x): its value's pieces real, the if real and complex"""
    st = mkst(w, ante)
    mf = mqfacts(w, ante, knn, k)
    krp = st([knn], 'nnrpd', '%s e. RR+' % k)
    ks = st([st([krp, st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '( %s ^c -u S ) e. RR+' % k)], 'rpred', '( %s ^c -u S ) e. RR' % k)
    xk = st([xrp, krp], 'rpdivcld', '( %s / %s ) e. RR+' % (x, k))
    pl = plfacts(w, ante, xk, '( %s / %s )' % (x, k))
    mk = st([mf['mur'], ks], 'remulcld', '( ( mmu ` %s ) x. ( %s ^c -u S ) ) e. RR' % (k, k))
    T = '( ( ( mmu ` %s ) x. ( %s ^c -u S ) ) x. %s )' % (k, k, PL('( %s / %s )' % (x, k)))
    tr = st([mk, pl], 'remulcld', '%s e. RR' % T)
    ir = st([tr, st([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IFP(k, q, x))
    return dict(mf=mf, krp=krp, ks=ks, xk=xk, pl=pl, mk=mk, T=T, tr=tr, re=ir, cc=st([ir], 'recnd', '%s e. CC' % IFP(k, q, x)))


def bvsspl():
    w = W('bvsspl', 'The posLog form of the restricted check sum over any range ( 1 ... M ) with |_ X <= M: the terms '
                    'with n > X vanish (X / n < 1), the others have posLog = log (Lean hS1/hS2 of Ssum_eq_mCheckQ).')
    A = '( ( S e. RR /\\ Q e. NN ) /\\ ( X e. RR+ /\\ ( M e. NN0 /\\ ( |_ ` X ) <_ M ) ) )'
    st = mkst(w, A)
    sr = st([], 'simpll', 'S e. RR'); qnn = st([], 'simplr', 'Q e. NN')
    xrp = st([], 'simprl', 'X e. RR+'); hm = st([], 'simprr', '( M e. NN0 /\\ ( |_ ` X ) <_ M )')
    mn0 = st([hm], 'simpld', 'M e. NN0'); flm = st([hm], 'simprd', '( |_ ` X ) <_ M')
    xr = st([xrp], 'rpred', 'X e. RR')
    flz = sy(w, A, xr, 'flcl', '( |_ ` X ) e. ZZ'); mz = st([mn0], 'nn0zd', 'M e. ZZ')
    R1 = '( 1 ... ( |_ ` X ) )'; RM = '( 1 ... M )'
    v = st([sr, qnn, xr, w.inst('bvmchkqval')], 'syl3anc', '%s = %s' % (MCQ('Q', 'X'), QSUM('Q', 'X')))
    uz = st([st([flz, mz, flm], '3jca', '( ( |_ ` X ) e. ZZ /\\ M e. ZZ /\\ ( |_ ` X ) <_ M )'), w.inst('eluz2')], 'sylibr', 'M e. ( ZZ>= ` ( |_ ` X ) )')
    sub = sy(w, A, uz, 'fzss2', '%s C_ %s' % (R1, RM))
    # on R1: IFP = IFQ
    A1 = '( %s /\\ n e. %s )' % (A, R1); s1 = mkst(w, A1)
    nel = s1([], 'simpr', 'n e. %s' % R1); nnn = sy(w, A1, nel, 'elfznn', 'n e. NN')
    nrp = s1([nnn], 'nnrpd', 'n e. RR+'); nre = s1([nrp], 'rpred', 'n e. RR')
    nfl = sy(w, A1, nel, 'elfzle2', 'n <_ ( |_ ` X )')
    flx = sy(w, A1, lift(w, xr, A1), 'flle', '( |_ ` X ) <_ X')
    nx = s1([nre, sy(w, A1, lift(w, xr, A1), 'reflcl', '( |_ ` X ) e. RR'), lift(w, xr, A1), nfl, flx], 'letrd', 'n <_ X')
    ge1 = s1([nrp, lift(w, xr, A1), nx, w.inst('divge1')], 'syl3anc', '1 <_ ( X / n )')
    plv = s1([ge1], 'iftrued', '%s = ( log ` ( X / n ) )' % PL('( X / n )'))
    mk = '( ( mmu ` n ) x. ( n ^c -u S ) )'
    c1 = s1([plv], 'oveq2d', '( %s x. %s ) = ( %s x. ( log ` ( X / n ) ) )' % (mk, PL('( X / n )'), mk))
    e1 = s1([c1], 'ifeq1d', '%s = %s' % (IFP('n', 'Q', 'X'), IFQ('n', 'Q', 'X')))
    f1 = ifpfacts(w, A1, nnn, lift(w, sr, A1), lift(w, xrp, A1), 'n', 'Q', 'X')
    # on RM \ R1: IFP = 0
    A2 = '( %s /\\ n e. ( %s \\ %s ) )' % (A, RM, R1); s2 = mkst(w, A2)
    nd = s2([], 'simpr', 'n e. ( %s \\ %s )' % (RM, R1))
    nrm = sy(w, A2, nd, 'eldifi', 'n e. %s' % RM); nn1 = sy(w, A2, nd, 'eldifn', '-. n e. %s' % R1)
    nnn2 = sy(w, A2, nrm, 'elfznn', 'n e. NN'); nz2 = s2([nnn2], 'nnzd', 'n e. ZZ')
    nrp2 = s2([nnn2], 'nnrpd', 'n e. RR+'); nre2 = s2([nrp2], 'rpred', 'n e. RR')
    A3 = '( %s /\\ n <_ ( |_ ` X ) )' % A2; s3 = mkst(w, A3)
    inr = s3([s3([], '1zzd', '1 e. ZZ'), lift(w, flz, A3), lift(w, nz2, A3), sy(w, A3, lift(w, nrm, A3), 'elfzle1', '1 <_ n'), s3([], 'simpr', 'n <_ ( |_ ` X )')],
             'elfzd', 'n e. %s' % R1)
    nle = s2([nn1, inr], 'mtand', '-. n <_ ( |_ ` X )')
    flre2 = sy(w, A2, lift(w, xr, A2), 'reflcl', '( |_ ` X ) e. RR')
    fllt = s2([nle, s2([flre2, nre2], 'ltnled', '( ( |_ ` X ) < n <-> -. n <_ ( |_ ` X ) )')], 'mpbird', '( |_ ` X ) < n')
    xlt = s2([fllt, sy2(w, A2, lift(w, xr, A2), nz2, 'fllt', '( X < n <-> ( |_ ` X ) < n )')], 'mpbird', 'X < n')
    q1 = s2([xlt, sy2(w, A2, lift(w, xr, A2), nrp2, 'divlt1lt', '( ( X / n ) < 1 <-> X < n )')], 'mpbird', '( X / n ) < 1')
    xnr = s2([s2([lift(w, xrp, A2), nrp2], 'rpdivcld', '( X / n ) e. RR+')], 'rpred', '( X / n ) e. RR')
    n1 = s2([q1, s2([s2([], '1red', '1 e. RR'), xnr], 'ltnled', '( ( X / n ) < 1 <-> -. 1 <_ ( X / n ) )')], 'mpbid', '-. 1 <_ ( X / n )')
    pl0 = s2([n1], 'iffalsed', '%s = 0' % PL('( X / n )'))
    f2 = ifpfacts(w, A2, nnn2, lift(w, sr, A2), lift(w, xrp, A2), 'n', 'Q', 'X')
    m0 = eqtr(w, A2, [s2([pl0], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (mk, PL('( X / n )'), mk)),
                      s2([s2([f2['mk']], 'recnd', '%s e. CC' % mk)], 'mul01d', '( %s x. 0 ) = 0' % mk)], None)
    z = s2([s2([m0], 'ifeq1d', '%s = if ( ( n gcd Q ) = 1 , 0 , 0 )' % IFP('n', 'Q', 'X')),
            s2([clo(w, 'ifid', 'if ( ( n gcd Q ) = 1 , 0 , 0 ) = 0')], 'a1i', 'if ( ( n gcd Q ) = 1 , 0 , 0 ) = 0')], 'eqtrd', '%s = 0' % IFP('n', 'Q', 'X'))
    fss = st([sub, f1['cc'], z, st([], 'fzfid', '%s e. Fin' % RM)], 'fsumss',
             'sum_ n e. %s %s = sum_ n e. %s %s' % (R1, IFP('n', 'Q', 'X'), RM, IFP('n', 'Q', 'X')))
    se = st([e1], 'sumeq2dv', 'sum_ n e. %s %s = %s' % (R1, IFP('n', 'Q', 'X'), QSUM('Q', 'X')))
    w.qed([eqtr(w, A, [st([fss], 'eqcomd', 'sum_ n e. %s %s = sum_ n e. %s %s' % (RM, IFP('n', 'Q', 'X'), R1, IFP('n', 'Q', 'X'))), se,
                       st([v], 'eqcomd', '%s = %s' % (QSUM('Q', 'X'), MCQ('Q', 'X')))], None), w.inst('id')], 'syl', STATEMENTS['bvsspl'])
    return w



def habfacts(w, A, hab):
    """from hab: ( A -> HAB ): A, B real and positive, 1 <_ A, A < B, ( B / A ) > 1, g = log ( B / A ) in RR+"""
    st = mkst(w, A)
    ha = st([hab], 'simpld', '( A e. RR /\\ 1 <_ A )'); hb = st([hab], 'simprd', '( B e. RR /\\ A < B )')
    ar = st([ha], 'simpld', 'A e. RR'); a1 = st([ha], 'simprd', '1 <_ A')
    br = st([hb], 'simpld', 'B e. RR'); ab = st([hb], 'simprd', 'A < B')
    arp = st([ar, linarith(w, A, [a1], '0 < A', leaves={'A': ar})], 'elrpd', 'A e. RR+')
    b1 = linarith(w, A, [a1, ab], '1 <_ B', leaves={'A': ar, 'B': br})
    brp = st([br, linarith(w, A, [a1, ab], '0 < B', leaves={'A': ar, 'B': br})], 'elrpd', 'B e. RR+')
    bar = st([brp, arp], 'rpdivcld', '( B / A ) e. RR+')
    bi = st([st([], '1red', '1 e. RR'), br, arp], 'ltmuldivd', '( ( 1 x. A ) < B <-> 1 < ( B / A ) )')
    ab1 = st([st([st([arp], 'rpcnd', 'A e. CC')], 'mullidd', '( 1 x. A ) = A'), ab], 'eqbrtrd', '( 1 x. A ) < B')
    ba1 = st([ab1, bi], 'mpbid', '1 < ( B / A )')
    grp = sy2(w, A, st([bar], 'rpred', '( B / A ) e. RR'), ba1, 'rplogcl', '%s e. RR+' % LGAB)
    gre = st([grp], 'rpred', '%s e. RR' % LGAB)
    return dict(ar=ar, a1=a1, br=br, ab=ab, arp=arp, brp=brp, b1=b1, bar=bar, grp=grp, gre=gre,
                gcc=st([gre], 'recnd', '%s e. CC' % LGAB), gne=st([grp], 'rpne0d', '%s =/= 0' % LGAB),
                acc=st([ar], 'recnd', 'A e. CC'), bcc=st([br], 'recnd', 'B e. CC'))


def lvfacts(w, ante, h1, hf, dnn, d):
    """( L ` d ) = BVL(d) and BVL(d) e. RR, from the $e step h1 (HL), habfacts hf (under ante) and d e. NN"""
    st = mkst(w, ante)
    MP = '( z e. NN |-> %s )' % BVL('z')
    c1 = w.s([h1], 'fveq1i', '( L ` %s ) = ( %s ` %s )' % (d, MP, d))
    c2, _ = mpv(w, ante, 'z', 'NN', BVL('z'), d, dnn)
    val = st([st([c1], 'a1i', '( L ` %s ) = ( %s ` %s )' % (d, MP, d)), c2], 'eqtrd', '( L ` %s ) = %s' % (d, BVL(d)))
    drp = st([dnn], 'nnrpd', '%s e. RR+' % d)
    mf = mqfacts(w, ante, dnn, d)
    pb = plfacts(w, ante, st([hf['brp'], drp], 'rpdivcld', '( B / %s ) e. RR+' % d), '( B / %s )' % d)
    pa = plfacts(w, ante, st([hf['arp'], drp], 'rpdivcld', '( A / %s ) e. RR+' % d), '( A / %s )' % d)
    num_ = st([mf['mur'], st([pb, pa], 'resubcld', '( %s - %s ) e. RR' % (PL('( B / %s )' % d), PL('( A / %s )' % d)))], 'remulcld',
              '( ( mmu ` %s ) x. ( %s - %s ) ) e. RR' % (d, PL('( B / %s )' % d), PL('( A / %s )' % d)))
    bre = st([num_, hf['gre'], hf['gne']], 'redivcld', '%s e. RR' % BVL(d))
    lre = st([val, bre], 'eqeltrd', '( L ` %s ) e. RR' % d)
    return dict(val=val, bre=bre, lre=lre, mf=mf, drp=drp)


def pleq(w, ante, e, x, x2):
    """( ante -> PL(x) = PL(x2) ) from e: ( ante -> x = x2 )"""
    st = mkst(w, ante)
    b = st([e], 'breq2d', '( 1 <_ %s <-> 1 <_ %s )' % (x, x2))
    f = st([e], 'fveq2d', '( log ` %s ) = ( log ` %s )' % (x, x2))
    return st([b, f], 'ifbieq1d', '%s = %s' % (PL(x), PL(x2)))


def bvlamterm():
    w = W('bvlamterm', 'The Barban-Vehov weight at a multiple M K, times ( M K ) ^c -u S, splits into the M-factor and the '
                       'coprimality-restricted posLog difference at K (Lean hterm of Ssum_eq_mCheckQ; mumul, bvmunc, mulcxp).')
    h1, = hyps_of(w, 'bvlamterm')
    A = '( ( %s /\\ S e. RR ) /\\ ( M e. NN /\\ K e. NN ) )' % HAB
    st = mkst(w, A)
    hf = habfacts(w, A, st([], 'simpll', HAB))
    sr = st([], 'simplr', 'S e. RR'); mnn = st([], 'simprl', 'M e. NN'); knn = st([], 'simprr', 'K e. NN')
    MK = '( M x. K )'
    mknn = st([mnn, knn], 'nnmulcld', '%s e. NN' % MK)
    lv = lvfacts(w, A, h1, hf, mknn, MK)
    nsc = st([st([sr], 'renegcld', '-u S e. RR')], 'recnd', '-u S e. CC')
    mrp = st([mnn], 'nnrpd', 'M e. RR+'); krp = st([knn], 'nnrpd', 'K e. RR+')
    mcc = st([mrp], 'rpcnd', 'M e. CC'); kcc = st([krp], 'rpcnd', 'K e. CC'); mne = st([mrp], 'rpne0d', 'M =/= 0'); kne = st([krp], 'rpne0d', 'K =/= 0')
    CMK = '( %s ^c -u S )' % MK
    a = '( mmu ` M )'; b = '( mmu ` K )'; c = '( M ^c -u S )'; k = '( K ^c -u S )'; g = LGAB
    P2 = PL('( ( B / M ) / K )'); P1 = PL('( ( A / M ) / K )')
    PB = PL('( B / %s )' % MK); PA = PL('( A / %s )' % MK)
    IB = IFP('K', 'M', '( B / M )'); IA = IFP('K', 'M', '( A / M )')
    C0 = '( ( %s x. %s ) / %s )' % (a, c, g)
    RHS = '( %s x. ( %s - %s ) )' % (C0, IB, IA)
    fB = ifpfacts(w, A, knn, sr, st([hf['brp'], mrp], 'rpdivcld', '( B / M ) e. RR+'), 'K', 'M', '( B / M )')
    fA = ifpfacts(w, A, knn, sr, st([hf['arp'], mrp], 'rpdivcld', '( A / M ) e. RR+'), 'K', 'M', '( A / M )')
    mf = mqfacts(w, A, mnn, 'M')
    cre = st([st([mrp, st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '%s e. RR+' % c)], 'rpred', '%s e. RR' % c)
    cmkre = st([st([st([mknn], 'nnrpd', '%s e. RR+' % MK), st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '%s e. RR+' % CMK)], 'rpred', '%s e. RR' % CMK)
    c0c = st([st([st([mf['mur'], cre], 'remulcld', '( %s x. %s ) e. RR' % (a, c)), hf['gre'], hf['gne']], 'redivcld', '%s e. RR' % C0)], 'recnd', '%s e. CC' % C0)
    # case ( K gcd M ) = 1
    A1 = '( %s /\\ ( K gcd M ) = 1 )' % A; s1 = mkst(w, A1)
    g1 = s1([], 'simpr', '( K gcd M ) = 1')
    kz = lift(w, st([knn], 'nnzd', 'K e. ZZ'), A1); mz = lift(w, st([mnn], 'nnzd', 'M e. ZZ'), A1)
    gm = s1([s1([kz, mz], 'gcdcomd', '( K gcd M ) = ( M gcd K )'), g1], 'eqtr3d', '( M gcd K ) = 1')
    mm = s1([lift(w, mnn, A1), lift(w, knn, A1), gm, w.inst('mumul')], 'syl3anc', '( mmu ` %s ) = ( %s x. %s )' % (MK, a, b))
    ebm = s1([lift(w, hf['bcc'], A1), lift(w, mcc, A1), lift(w, kcc, A1), lift(w, mne, A1), lift(w, kne, A1)], 'divdiv1d', '( ( B / M ) / K ) = ( B / %s )' % MK)
    eam = s1([lift(w, hf['acc'], A1), lift(w, mcc, A1), lift(w, kcc, A1), lift(w, mne, A1), lift(w, kne, A1)], 'divdiv1d', '( ( A / M ) / K ) = ( A / %s )' % MK)
    pb = pleq(w, A1, s1([ebm], 'eqcomd', '( B / %s ) = ( ( B / M ) / K )' % MK), '( B / %s )' % MK, '( ( B / M ) / K )')
    pa = pleq(w, A1, s1([eam], 'eqcomd', '( A / %s ) = ( ( A / M ) / K )' % MK), '( A / %s )' % MK, '( ( A / M ) / K )')
    X = '( ( %s x. %s ) x. ( %s - %s ) )' % (a, b, P2, P1)
    Y = '( %s x. %s )' % (c, k)
    nume = s1([mm, s1([pb, pa], 'oveq12d', '( %s - %s ) = ( %s - %s )' % (PB, PA, P2, P1))], 'oveq12d',
              '( ( mmu ` %s ) x. ( %s - %s ) ) = %s' % (MK, PB, PA, X))
    bv = s1([nume], 'oveq1d', '%s = ( %s / %s )' % (BVL(MK), X, g))
    mre = lift(w, st([mrp], 'rpred', 'M e. RR'), A1); kre = lift(w, st([krp], 'rpred', 'K e. RR'), A1)
    cx = s1([mre, lift(w, st([mrp], 'rpge0d', '0 <_ M'), A1), kre, lift(w, st([krp], 'rpge0d', '0 <_ K'), A1), lift(w, nsc, A1)], 'mulcxpd', '%s = %s' % (CMK, Y))
    l1 = s1([bv, cx], 'oveq12d', '( %s x. %s ) = ( ( %s / %s ) x. %s )' % (BVL(MK), CMK, X, g, Y))
    fBm = fB['mf']; mur1 = lift(w, mf['mur'], A1); bre1 = lift(w, fBm['mur'], A1)
    p2r = lift(w, fB['pl'], A1); p1r = lift(w, fA['pl'], A1); kre1 = lift(w, fB['ks'], A1); cre1 = lift(w, cre, A1)
    xr = s1([s1([mur1, bre1], 'remulcld', '( %s x. %s ) e. RR' % (a, b)), s1([p2r, p1r], 'resubcld', '( %s - %s ) e. RR' % (P2, P1))], 'remulcld', '%s e. RR' % X)
    yr = s1([cre1, kre1], 'remulcld', '%s e. RR' % Y)
    l2 = s1([s1([xr], 'recnd', '%s e. CC' % X), s1([yr], 'recnd', '%s e. CC' % Y), lift(w, hf['gcc'], A1), lift(w, hf['gne'], A1)], 'div23d',
            '( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s )' % (X, Y, g, X, g, Y))
    BK = '( %s x. %s )' % (b, k)
    Z = '( ( %s x. %s ) - ( %s x. %s ) )' % (BK, P2, BK, P1)
    ib = s1([g1], 'iftrued', '%s = ( %s x. %s )' % (IB, BK, P2)); ia = s1([g1], 'iftrued', '%s = ( %s x. %s )' % (IA, BK, P1))
    r1 = s1([s1([ib, ia], 'oveq12d', '( %s - %s ) = %s' % (IB, IA, Z))], 'oveq2d', '%s = ( %s x. %s )' % (RHS, C0, Z))
    AC = '( %s x. %s )' % (a, c)
    acr = s1([mur1, cre1], 'remulcld', '%s e. RR' % AC)
    zr = s1([s1([s1([bre1, kre1], 'remulcld', '%s e. RR' % BK), p2r], 'remulcld', '( %s x. %s ) e. RR' % (BK, P2)),
             s1([s1([bre1, kre1], 'remulcld', '%s e. RR' % BK), p1r], 'remulcld', '( %s x. %s ) e. RR' % (BK, P1))], 'resubcld', '%s e. RR' % Z)
    r2 = s1([s1([acr], 'recnd', '%s e. CC' % AC), s1([zr], 'recnd', '%s e. CC' % Z), lift(w, hf['gcc'], A1), lift(w, hf['gne'], A1)], 'div23d',
            '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (AC, Z, g, C0, Z))
    ne = lineq(w, A1, '( %s x. %s )' % (X, Y), '( %s x. %s )' % (AC, Z), products=True,
               leaves={a: mur1, b: bre1, c: cre1, k: kre1, P2: p2r, P1: p1r}, atoms=[a, b, c, k, P2, P1])
    nq = s1([ne], 'oveq1d', '( ( %s x. %s ) / %s ) = ( ( %s x. %s ) / %s )' % (X, Y, g, AC, Z, g))
    case1 = eqtr(w, A1, [l1, s1([l2], 'eqcomd', '( ( %s / %s ) x. %s ) = ( ( %s x. %s ) / %s )' % (X, g, Y, X, Y, g)), nq, r2,
                         s1([r1], 'eqcomd', '( %s x. %s ) = %s' % (C0, Z, RHS))], None)
    # case -. ( K gcd M ) = 1
    A2 = '( %s /\\ -. ( K gcd M ) = 1 )' % A; s2 = mkst(w, A2)
    ng = s2([], 'simpr', '-. ( K gcd M ) = 1')
    m0 = s2([bind(w, A2, bind(w, A2, lift(w, mnn, A2), lift(w, knn, A2), 'M e. NN', 'K e. NN'), ng, '( M e. NN /\\ K e. NN )', '-. ( K gcd M ) = 1'),
             w.inst('bvmunc')], 'syl', '( mmu ` %s ) = 0' % MK)
    DP = '( %s - %s )' % (PB, PA)
    fmk = mqfacts(w, A2, lift(w, mknn, A2), MK)
    mkrp = s2([lift(w, mknn, A2)], 'nnrpd', '%s e. RR+' % MK)
    pbr = plfacts(w, A2, s2([lift(w, hf['brp'], A2), mkrp], 'rpdivcld', '( B / %s ) e. RR+' % MK), '( B / %s )' % MK)
    par = plfacts(w, A2, s2([lift(w, hf['arp'], A2), mkrp], 'rpdivcld', '( A / %s ) e. RR+' % MK), '( A / %s )' % MK)
    dpc = s2([s2([pbr, par], 'resubcld', '%s e. RR' % DP)], 'recnd', '%s e. CC' % DP)
    z1 = eqtr(w, A2, [s2([m0], 'oveq1d', '( ( mmu ` %s ) x. %s ) = ( 0 x. %s )' % (MK, DP, DP)), s2([dpc], 'mul02d', '( 0 x. %s ) = 0' % DP)], None)
    z2 = eqtr(w, A2, [s2([z1], 'oveq1d', '%s = ( 0 / %s )' % (BVL(MK), g)), s2([lift(w, hf['gcc'], A2), lift(w, hf['gne'], A2)], 'div0d', '( 0 / %s ) = 0' % g)], None)
    cmkc = lift(w, st([cmkre], 'recnd', '%s e. CC' % CMK), A2)
    lz = eqtr(w, A2, [s2([z2], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (BVL(MK), CMK, CMK)), s2([cmkc], 'mul02d', '( 0 x. %s ) = 0' % CMK)], None)
    ib0 = s2([ng], 'iffalsed', '%s = 0' % IB); ia0 = s2([ng], 'iffalsed', '%s = 0' % IA)
    rz = eqtr(w, A2, [s2([s2([ib0, ia0], 'oveq12d', '( %s - %s ) = ( 0 - 0 )' % (IB, IA))], 'oveq2d', '%s = ( %s x. ( 0 - 0 ) )' % (RHS, C0)),
                      s2([s2([clo(w, '0m0e0', '( 0 - 0 ) = 0')], 'a1i', '( 0 - 0 ) = 0')], 'oveq2d', '( %s x. ( 0 - 0 ) ) = ( %s x. 0 )' % (C0, C0)),
                      s2([lift(w, c0c, A2)], 'mul01d', '( %s x. 0 ) = 0' % C0)], None)
    case2 = s2([lz, rz], 'eqtr4d', '( %s x. %s ) = %s' % (BVL(MK), CMK, RHS))
    both = w.s([case1, case2], 'pm2.61dan', '( %s -> ( %s x. %s ) = %s )' % (A, BVL(MK), CMK, RHS))
    w.qed([st([lv['val']], 'oveq1d', '( ( L ` %s ) x. %s ) = ( %s x. %s )' % (MK, CMK, BVL(MK), CMK)), both], 'eqtrd', STATEMENTS['bvlamterm'])
    return w


def bvssumq():
    w = W('bvssumq', 'S_delta in terms of the restricted check sums (Lean Ssum_eq_mCheckQ, for every M e. NN): the multiples '
                     'd = M n are reindexed by dvdsflf1o, the weight split by bvlamterm, both posLog sums identified by bvsspl.')
    h1, = hyps_of(w, 'bvssumq')
    A = '( ( %s /\\ S e. RR ) /\\ M e. NN )' % HAB
    st = mkst(w, A)
    hs = st([], 'simpl', '( %s /\\ S e. RR )' % HAB)
    hf = habfacts(w, A, st([hs], 'simpld', HAB))
    sr = st([hs], 'simprd', 'S e. RR'); mnn = st([], 'simpr', 'M e. NN')
    mrp = st([mnn], 'nnrpd', 'M e. RR+')
    R1 = '( 1 ... %s )' % NB; FS = '{ x e. %s | M || x }' % R1
    BM = '( B / M )'; AM = '( A / M )'
    R2 = '( 1 ... ( |_ ` %s ) )' % BM
    T = lambda d: '( ( L ` %s ) x. ( %s ^c -u S ) )' % (d, d)
    IFD = lambda d: 'if ( M || %s , %s , 0 )' % (d, T(d))
    nsr = st([sr], 'renegcld', '-u S e. RR')

    def tcc(ante, dnn, d):
        s_ = mkst(w, ante)
        lv = lvfacts(w, ante, h1, {k_: lift(w, v_, ante) for k_, v_ in hf.items()}, dnn, d)
        cx = s_([s_([s_([dnn], 'nnrpd', '%s e. RR+' % d), lift(w, nsr, ante)], 'rpcxpcld', '( %s ^c -u S ) e. RR+' % d)], 'rpred', '( %s ^c -u S ) e. RR' % d)
        return s_([s_([lv['lre'], cx], 'remulcld', '%s e. RR' % T(d))], 'recnd', '%s e. CC' % T(d))
    elr = w.s([w.s([], 'breq2', '( x = d -> ( M || x <-> M || d ) )')], 'elrab', '( d e. %s <-> ( d e. %s /\\ M || d ) )' % (FS, R1))
    sub = st([clo(w, 'ssrab2', '%s C_ %s' % (FS, R1))], 'a1i', '%s C_ %s' % (FS, R1))
    AF = '( %s /\\ d e. %s )' % (A, FS); sf = mkst(w, AF)
    elf = sf([sf([], 'simpr', 'd e. %s' % FS), elr], 'sylib', '( d e. %s /\\ M || d )' % R1)
    dnnf = sy(w, AF, sf([elf], 'simpld', 'd e. %s' % R1), 'elfznn', 'd e. NN')
    tcf = tcc(AF, dnnf, 'd')
    ifc = sf([tcf, sf([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IFD('d'))
    itf = sf([sf([elf], 'simprd', 'M || d')], 'iftrued', '%s = %s' % (IFD('d'), T('d')))
    AD = '( %s /\\ d e. ( %s \\ %s ) )' % (A, R1, FS); sd = mkst(w, AD)
    eld = sd([sd([], 'simpr', 'd e. ( %s \\ %s )' % (R1, FS)), w.inst('eldif')], 'sylib', '( d e. %s /\\ -. d e. %s )' % (R1, FS))
    nconj = sd([sd([eld], 'simprd', '-. d e. %s' % FS), elr], 'sylnib', '-. ( d e. %s /\\ M || d )' % R1)
    npd = sd([sd([eld], 'simpld', 'd e. %s' % R1), sd([nconj, w.inst('imnan')], 'sylibr', '( d e. %s -> -. M || d )' % R1)], 'mpd', '-. M || d')
    zero = sd([npd], 'iffalsed', '%s = 0' % IFD('d'))
    fss = st([sub, ifc, zero, st([], 'fzfid', '%s e. Fin' % R1)], 'fsumss', 'sum_ d e. %s %s = %s' % (FS, IFD('d'), SGB('M')))
    s2 = st([itf], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (FS, IFD('d'), FS, T('d')))
    F = '( t e. %s |-> ( M x. t ) )' % R2
    bij = st([hf['br'], mnn, w.s([], 'eqid', '%s = %s' % (F, F))], 'dvdsflf1o', '%s : %s -1-1-onto-> %s' % (F, R2, FS))
    idn = w.s([], 'id', '( d = ( M x. n ) -> d = ( M x. n ) )')
    cg, TMn = w.congr(T('d'), {'d': '( M x. n )'}, 'd = ( M x. n )', {'d': idn})
    assert TMn == T('( M x. n )'), TMn
    AN = '( %s /\\ n e. %s )' % (A, R2); sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % R2)
    valn, _ = mpv(w, AN, 't', R2, '( M x. t )', 'n', nel)
    f1o = st([cg, st([], 'fzfid', '%s e. Fin' % R2), bij, valn, tcf], 'fsumf1o', 'sum_ d e. %s %s = sum_ n e. %s %s' % (FS, T('d'), R2, TMn))
    nnn = sy(w, AN, nel, 'elfznn', 'n e. NN')
    C0 = '( ( ( mmu ` M ) x. ( M ^c -u S ) ) / %s )' % LGAB
    IB = IFP('n', 'M', BM); IA = IFP('n', 'M', AM)
    ltc = w.s([h1], 'bvlamterm', '( ( ( %s /\\ S e. RR ) /\\ ( M e. NN /\\ n e. NN ) ) -> %s = ( %s x. ( %s - %s ) ) )' % (HAB, TMn, C0, IB, IA))
    lt = w.s([bind(w, AN, lift(w, hs, AN), bind(w, AN, lift(w, mnn, AN), nnn, 'M e. NN', 'n e. NN'), '( %s /\\ S e. RR )' % HAB, '( M e. NN /\\ n e. NN )'), ltc],
             'syl', '( %s -> %s = ( %s x. ( %s - %s ) ) )' % (AN, TMn, C0, IB, IA))
    s3 = st([lt], 'sumeq2dv', 'sum_ n e. %s %s = sum_ n e. %s ( %s x. ( %s - %s ) )' % (R2, TMn, R2, C0, IB, IA))
    bmrp = st([hf['brp'], mrp], 'rpdivcld', '%s e. RR+' % BM); amrp = st([hf['arp'], mrp], 'rpdivcld', '%s e. RR+' % AM)
    fB = ifpfacts(w, AN, nnn, lift(w, sr, AN), lift(w, bmrp, AN), 'n', 'M', BM)
    fA = ifpfacts(w, AN, nnn, lift(w, sr, AN), lift(w, amrp, AN), 'n', 'M', AM)
    mf = mqfacts(w, A, mnn, 'M')
    cre = st([st([mrp, nsr], 'rpcxpcld', '( M ^c -u S ) e. RR+')], 'rpred', '( M ^c -u S ) e. RR')
    c0c = st([st([st([mf['mur'], cre], 'remulcld', '( ( mmu ` M ) x. ( M ^c -u S ) ) e. RR'), hf['gre'], hf['gne']], 'redivcld', '%s e. RR' % C0)], 'recnd', '%s e. CC' % C0)
    difc = sn([fB['cc'], fA['cc']], 'subcld', '( %s - %s ) e. CC' % (IB, IA))
    fin2 = st([], 'fzfid', '%s e. Fin' % R2)
    SD = 'sum_ n e. %s ( %s - %s )' % (R2, IB, IA)
    s4 = st([st([fin2, c0c, difc], 'fsummulc2', '( %s x. %s ) = sum_ n e. %s ( %s x. ( %s - %s ) )' % (C0, SD, R2, C0, IB, IA))], 'eqcomd',
            'sum_ n e. %s ( %s x. ( %s - %s ) ) = ( %s x. %s )' % (R2, C0, IB, IA, C0, SD))
    SB = 'sum_ n e. %s %s' % (R2, IB); SA = 'sum_ n e. %s %s' % (R2, IA)
    s5 = st([st([fin2, fB['cc'], fA['cc']], 'fsumsub', '%s = ( %s - %s )' % (SD, SB, SA))], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s - %s ) )' % (C0, SD, C0, SB, SA))
    FLB = '( |_ ` %s )' % BM; FLA = '( |_ ` %s )' % AM
    bmr = st([bmrp], 'rpred', '%s e. RR' % BM); amr = st([amrp], 'rpred', '%s e. RR' % AM)
    fln0 = st([bmr, st([bmrp], 'rpge0d', '0 <_ %s' % BM), w.inst('flge0nn0')], 'syl2anc', '%s e. NN0' % FLB)
    le1 = st([sy(w, A, bmr, 'reflcl', '%s e. RR' % FLB)], 'leidd', '%s <_ %s' % (FLB, FLB))
    amle = st([hf['ar'], hf['br'], mrp, st([hf['ab']], 'ltled', 'A <_ B')], 'lediv1dd', '%s <_ %s' % (AM, BM))
    le2 = st([amr, bmr, amle, w.inst('flwordi')], 'syl3anc', '%s <_ %s' % (FLA, FLB))
    sm = bind(w, A, sr, mnn, 'S e. RR', 'M e. NN')
    spB = w.s([bind(w, A, sm, bind(w, A, bmrp, bind(w, A, fln0, le1, '%s e. NN0' % FLB, '%s <_ %s' % (FLB, FLB)), '%s e. RR+' % BM,
                                        '( %s e. NN0 /\\ %s <_ %s )' % (FLB, FLB, FLB)), '( S e. RR /\\ M e. NN )',
                   '( %s e. RR+ /\\ ( %s e. NN0 /\\ %s <_ %s ) )' % (BM, FLB, FLB, FLB)), w.inst('bvsspl')], 'syl', '( %s -> %s = %s )' % (A, SB, MCQ('M', BM)))
    spA = w.s([bind(w, A, sm, bind(w, A, amrp, bind(w, A, fln0, le2, '%s e. NN0' % FLB, '%s <_ %s' % (FLA, FLB)), '%s e. RR+' % AM,
                                        '( %s e. NN0 /\\ %s <_ %s )' % (FLB, FLA, FLB)), '( S e. RR /\\ M e. NN )',
                   '( %s e. RR+ /\\ ( %s e. NN0 /\\ %s <_ %s ) )' % (AM, FLB, FLA, FLB)), w.inst('bvsspl')], 'syl', '( %s -> %s = %s )' % (A, SA, MCQ('M', AM)))
    s6 = st([st([spB, spA], 'oveq12d', '( %s - %s ) = ( %s - %s )' % (SB, SA, MCQ('M', BM), MCQ('M', AM)))], 'oveq2d',
            '( %s x. ( %s - %s ) ) = ( %s x. ( %s - %s ) )' % (C0, SB, SA, C0, MCQ('M', BM), MCQ('M', AM)))
    w.qed([eqtr(w, A, [st([fss], 'eqcomd', '%s = sum_ d e. %s %s' % (SGB('M'), FS, IFD('d'))), s2, f1o, s3, s4, s5], None), s6], 'eqtrd', STATEMENTS['bvssumq'])
    return w



def bvssumle():
    w = W('bvssumle', 'The S_delta bound (Lean abs_Ssum_le): for squarefree M <= B, | S_M | <= M ^c -u S ( M / phi M ) '
                      '( 22 / 3 ) ( 1 + ( S - 1 ) log B ) / log ( B / A ) (bvssumq, bvmchkq, bvmchkq0, bvmchkqbqle).')
    h1, = hyps_of(w, 'bvssumle')
    HSS = '( S e. RR /\\ 1 <_ S )'
    A = '( ( %s /\\ %s ) /\\ ( M e. ( 1 ... %s ) /\\ ( mmu ` M ) =/= 0 ) )' % (HAB, HSS, NB)
    st = mkst(w, A)
    hab = st([], 'simpll', HAB); hs = st([], 'simplr', HSS)
    sr = st([hs], 'simpld', 'S e. RR'); s1 = st([hs], 'simprd', '1 <_ S')
    mel = st([], 'simprl', 'M e. ( 1 ... %s )' % NB); mu0 = st([], 'simprr', '( mmu ` M ) =/= 0')
    hf = habfacts(w, A, hab)
    mnn = sy(w, A, mel, 'elfznn', 'M e. NN'); mrp = st([mnn], 'nnrpd', 'M e. RR+'); mre = st([mrp], 'rpred', 'M e. RR')
    m1 = st([mnn], 'nnge1d', '1 <_ M')
    BM = '( B / M )'; AM = '( A / M )'
    MB = MCQ('M', BM); MA = MCQ('M', AM)
    D = '( %s - %s )' % (MB, MA)
    a = '( mmu ` M )'; c = '( M ^c -u S )'; g = LGAB
    C1 = '( %s x. %s )' % (a, c); C0 = '( %s / %s )' % (C1, g)
    q = w.s([h1], 'bvssumq', '( ( ( %s /\\ S e. RR ) /\\ M e. NN ) -> %s = ( %s x. %s ) )' % (HAB, SGB('M'), C0, D))
    qv = st([bind(w, A, bind(w, A, hab, sr, HAB, 'S e. RR'), mnn, '( %s /\\ S e. RR )' % HAB, 'M e. NN'), q], 'syl', '%s = ( %s x. %s )' % (SGB('M'), C0, D))
    bmr = st([hf['br'], mre, st([mrp], 'rpne0d', 'M =/= 0')], 'redivcld', '%s e. RR' % BM)
    amr = st([hf['ar'], mre, st([mrp], 'rpne0d', 'M =/= 0')], 'redivcld', '%s e. RR' % AM)
    mbr = st([sr, mnn, bmr, w.inst('bvmchkqcl')], 'syl3anc', '%s e. RR' % MB)
    mar = st([sr, mnn, amr, w.inst('bvmchkqcl')], 'syl3anc', '%s e. RR' % MA)
    dr = st([mbr, mar], 'resubcld', '%s e. RR' % D); dc = st([dr], 'recnd', '%s e. CC' % D)
    mf = mqfacts(w, A, mnn, 'M')
    crp = st([mrp, st([sr], 'renegcld', '-u S e. RR')], 'rpcxpcld', '%s e. RR+' % c)
    cre = st([crp], 'rpred', '%s e. RR' % c); cge = st([crp], 'rpge0d', '0 <_ %s' % c)
    c1r = st([mf['mur'], cre], 'remulcld', '%s e. RR' % C1); c1c = st([c1r], 'recnd', '%s e. CC' % C1)
    c0c = st([st([c1r, hf['gre'], hf['gne']], 'redivcld', '%s e. RR' % C0)], 'recnd', '%s e. CC' % C0)
    AU = '( abs ` %s )' % a; AD = '( abs ` %s )' % D
    e1 = st([c0c, dc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. %s )' % (C0, D, C0, AD))
    e2 = st([c1c, hf['gcc'], hf['gne']], 'absdivd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (C0, C1, g))
    e3 = st([hf['gre'], st([hf['grp']], 'rpge0d', '0 <_ %s' % g)], 'absidd', '( abs ` %s ) = %s' % (g, g))
    e4 = st([mf['muc'], st([cre], 'recnd', '%s e. CC' % c)], 'absmuld', '( abs ` %s ) = ( %s x. ( abs ` %s ) )' % (C1, AU, c))
    e5 = st([cre, cge], 'absidd', '( abs ` %s ) = %s' % (c, c))
    UC = '( %s x. %s )' % (AU, c)
    e45 = st([e4, st([e5], 'oveq2d', '( %s x. ( abs ` %s ) ) = %s' % (AU, c, UC))], 'eqtrd', '( abs ` %s ) = %s' % (C1, UC))
    e23 = st([e2, st([e45, e3], 'oveq12d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( %s / %s )' % (C1, g, UC, g))], 'eqtrd', '( abs ` %s ) = ( %s / %s )' % (C0, UC, g))
    aur = st([mf['muc']], 'abscld', '%s e. RR' % AU)
    ucr = st([aur, cre], 'remulcld', '%s e. RR' % UC)
    V = '( 1 / %s )' % g
    e6 = st([st([ucr], 'recnd', '%s e. CC' % UC), hf['gcc'], hf['gne']], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (UC, g, UC, V))
    UCV = '( %s x. %s )' % (UC, V)
    lhs = eqtr(w, A, [st([qv], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s x. %s ) )' % (SGB('M'), C0, D)), e1,
                      st([st([e23, e6], 'eqtrd', '( abs ` %s ) = %s' % (C0, UCV))], 'oveq1d', '( ( abs ` %s ) x. %s ) = ( %s x. %s )' % (C0, AD, UCV, AD))], None)
    # the check sum bounds
    hsx = hs
    mq = bind(w, A, mnn, mu0, 'M e. NN', '( mmu ` M ) =/= 0')
    flb = sy(w, A, hf['br'], 'flle', '%s <_ B' % NB)
    mleb = st([mre, sy(w, A, hf['br'], 'reflcl', '%s e. RR' % NB), hf['br'], sy(w, A, mel, 'elfzle2', 'M <_ %s' % NB), flb], 'letrd', 'M <_ B')
    bm1 = st([mrp, hf['br'], mleb, w.inst('divge1')], 'syl3anc', '1 <_ %s' % BM)
    bmle = st([st([hf['br'], hf['brp'], bind(w, A, mrp, m1, 'M e. RR+', '1 <_ M'), w.inst('ledivge1le')], 'syl3anc', '( B <_ B -> %s <_ B )' % BM),
               st([hf['br']], 'leidd', 'B <_ B')], 'mpd', '%s <_ B' % BM)
    BQB = BQ('M', 'B')
    kB = st([bind(w, A, bind(w, A, bind(w, A, bmr, bm1, '%s e. RR' % BM, '1 <_ %s' % BM), hsx, '( %s e. RR /\\ 1 <_ %s )' % (BM, BM), HSS), mq,
                  '( ( %s e. RR /\\ 1 <_ %s ) /\\ %s )' % (BM, BM, HSS), '( M e. NN /\\ ( mmu ` M ) =/= 0 )'), w.inst('bvmchkq')], 'syl',
             '( abs ` %s ) <_ %s' % (MB, BQ('M', BM)))
    hb1 = bind(w, A, hf['br'], hf['b1'], 'B e. RR', '1 <_ B')

    def bqle(ante, zr, z1, zle, Z):
        s_ = mkst(w, ante)
        zz = s_([zr, z1, zle], '3jca', '( %s e. RR /\\ 1 <_ %s /\\ %s <_ B )' % (Z, Z, Z))
        inner = bind(w, ante, lift(w, hb1, ante), zz, '( B e. RR /\\ 1 <_ B )', '( %s e. RR /\\ 1 <_ %s /\\ %s <_ B )' % (Z, Z, Z))
        full = bind(w, ante, lift(w, hsx, ante), bind(w, ante, lift(w, mnn, ante), inner, 'M e. NN',
                                                        '( ( B e. RR /\\ 1 <_ B ) /\\ ( %s e. RR /\\ 1 <_ %s /\\ %s <_ B ) )' % (Z, Z, Z)),
                    HSS, '( M e. NN /\\ ( ( B e. RR /\\ 1 <_ B ) /\\ ( %s e. RR /\\ 1 <_ %s /\\ %s <_ B ) ) )' % (Z, Z, Z))
        return s_([full, w.inst('bvmchkqbqle')], 'syl', '%s <_ %s' % (BQ('M', Z), BQB))
    bqB = bqle(A, bmr, bm1, bmle, BM)
    rat = RAT('M')
    phinn = sy(w, A, mnn, 'phicl', '( phi ` M ) e. NN')
    ratr = st([mre, st([phinn], 'nnred', '( phi ` M ) e. RR'), st([st([phinn], 'nnrpd', '( phi ` M ) e. RR+')], 'rpne0d', '( phi ` M ) =/= 0')], 'redivcld', '%s e. RR' % rat)
    WB = '( 1 + ( ( S - 1 ) x. ( log ` B ) ) )'
    lbr = st([hf['brp']], 'relogcld', '( log ` B ) e. RR')
    wr = st([st([], '1red', '1 e. RR'), st([st([sr, st([], '1red', '1 e. RR')], 'resubcld', '( S - 1 ) e. RR'), lbr], 'remulcld', '( ( S - 1 ) x. ( log ` B ) ) e. RR')],
            'readdcld', '%s e. RR' % WB)
    k113 = num.real(w, '( ; 1 1 / 3 )')
    bqbr = st([st([ratr, st([k113], 'a1i', '( ; 1 1 / 3 ) e. RR')], 'remulcld', '( %s x. ( ; 1 1 / 3 ) ) e. RR' % rat), wr], 'remulcld', '%s e. RR' % BQB)
    mBle = st([st([mbr], 'recnd', '%s e. CC' % MB)], 'abscld', '( abs ` %s ) e. RR' % MB)
    # need BQ(M,BM) real for letrd: from bvmchkqbq0
    bq0 = lambda ante, Zr, Z1, Z: w.s([bind(w, ante, lift(w, hsx, ante), bind(w, ante, lift(w, mnn, ante), bind(w, ante, Zr, Z1, '%s e. RR' % Z, '1 <_ %s' % Z), 'M e. NN',
                                                                          '( %s e. RR /\\ 1 <_ %s )' % (Z, Z)), HSS, '( M e. NN /\\ ( %s e. RR /\\ 1 <_ %s ) )' % (Z, Z)),
                                       w.inst('bvmchkqbq0')], 'syl', '( %s -> 0 <_ %s )' % (ante, BQ('M', Z)))
    bmrp = st([bmr, linarith(w, A, [bm1], '0 < %s' % BM, leaves={BM: bmr})], 'elrpd', '%s e. RR+' % BM)
    wbm = '( 1 + ( ( S - 1 ) x. ( log ` %s ) ) )' % BM
    wbmr = st([st([], '1red', '1 e. RR'), st([st([sr, st([], '1red', '1 e. RR')], 'resubcld', '( S - 1 ) e. RR'), st([bmrp], 'relogcld', '( log ` %s ) e. RR' % BM)], 'remulcld',
                                          '( ( S - 1 ) x. ( log ` %s ) ) e. RR' % BM)], 'readdcld', '%s e. RR' % wbm)
    bqbmr = st([st([ratr, st([k113], 'a1i', '( ; 1 1 / 3 ) e. RR')], 'remulcld', '( %s x. ( ; 1 1 / 3 ) ) e. RR' % rat), wbmr], 'remulcld', '%s e. RR' % BQ('M', BM))
    mbB = st([mBle, bqbmr, bqbr, kB, bqB], 'letrd', '( abs ` %s ) <_ %s' % (MB, BQB))
    # MA: two cases
    maa = st([st([mar], 'recnd', '%s e. CC' % MA)], 'abscld', '( abs ` %s ) e. RR' % MA)
    AL = '( %s /\\ %s < 1 )' % (A, AM); sl = mkst(w, AL)
    ma0 = sl([lift(w, sr, AL), lift(w, mnn, AL), sl([lift(w, amr, AL), sl([], 'simpr', '%s < 1' % AM)], 'jca', '( %s e. RR /\\ %s < 1 )' % (AM, AM)), w.inst('bvmchkq0')],
             'syl3anc', '%s = 0' % MA)
    ab0 = sl([sl([ma0], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % MA), sl([clo(w, 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % MA)
    bq0B = bq0(AL, lift(w, hf['br'], AL), lift(w, hf['b1'], AL), 'B')
    cL = sl([ab0, bq0B], 'eqbrtrd', '( abs ` %s ) <_ %s' % (MA, BQB))
    AG = '( %s /\\ 1 <_ %s )' % (A, AM); sg = mkst(w, AG)
    am1 = sg([], 'simpr', '1 <_ %s' % AM)
    kA = sg([bind(w, AG, bind(w, AG, bind(w, AG, lift(w, amr, AG), am1, '%s e. RR' % AM, '1 <_ %s' % AM), lift(w, hsx, AG), '( %s e. RR /\\ 1 <_ %s )' % (AM, AM), HSS),
                  lift(w, mq, AG), '( ( %s e. RR /\\ 1 <_ %s ) /\\ %s )' % (AM, AM, HSS), '( M e. NN /\\ ( mmu ` M ) =/= 0 )'), w.inst('bvmchkq')], 'syl',
             '( abs ` %s ) <_ %s' % (MA, BQ('M', AM)))
    amle = sg([lift(w, hf['ar'], AG), lift(w, hf['br'], AG), lift(w, mrp, AG), sg([lift(w, hf['ab'], AG)], 'ltled', 'A <_ B')], 'lediv1dd', '%s <_ %s' % (AM, BM))
    amleb = sg([lift(w, amr, AG), lift(w, bmr, AG), lift(w, hf['br'], AG), amle, lift(w, bmle, AG)], 'letrd', '%s <_ B' % AM)
    bqA = bqle(AG, lift(w, amr, AG), am1, amleb, AM)
    amrp = sg([lift(w, amr, AG), linarith(w, AG, [am1], '0 < %s' % AM, leaves={AM: lift(w, amr, AG)})], 'elrpd', '%s e. RR+' % AM)
    wam = '( 1 + ( ( S - 1 ) x. ( log ` %s ) ) )' % AM
    wamr = sg([sg([], '1red', '1 e. RR'), sg([sg([lift(w, sr, AG), sg([], '1red', '1 e. RR')], 'resubcld', '( S - 1 ) e. RR'), sg([amrp], 'relogcld', '( log ` %s ) e. RR' % AM)],
                                         'remulcld', '( ( S - 1 ) x. ( log ` %s ) ) e. RR' % AM)], 'readdcld', '%s e. RR' % wam)
    bqamr = sg([sg([lift(w, ratr, AG), sg([k113], 'a1i', '( ; 1 1 / 3 ) e. RR')], 'remulcld', '( %s x. ( ; 1 1 / 3 ) ) e. RR' % rat), wamr], 'remulcld', '%s e. RR' % BQ('M', AM))
    cG = sg([lift(w, maa, AG), bqamr, lift(w, bqbr, AG), kA, bqA], 'letrd', '( abs ` %s ) <_ %s' % (MA, BQB))
    tric = st([st([], '1red', '1 e. RR'), amr, w.inst('lelttric')], 'syl2anc', '( 1 <_ %s \\/ %s < 1 )' % (AM, AM))
    maB = w.s([cG, cL, tric], 'mpjaodan', '( %s -> ( abs ` %s ) <_ %s )' % (A, MA, BQB))
    dle = st([st([mbr], 'recnd', '%s e. CC' % MB), st([mar], 'recnd', '%s e. CC' % MA)], 'abs2dif2d', '%s <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (AD, MB, MA))
    TWO = '( %s + %s )' % (BQB, BQB)
    dle2 = st([mBle, maa, bqbr, bqbr, mbB, maB], 'le2addd', '( ( abs ` %s ) + ( abs ` %s ) ) <_ %s' % (MB, MA, TWO))
    adr = st([dc], 'abscld', '%s e. RR' % AD)
    twor = st([bqbr, bqbr], 'readdcld', '%s e. RR' % TWO)
    dB = st([adr, st([mBle, maa], 'readdcld', '( ( abs ` %s ) + ( abs ` %s ) ) e. RR' % (MB, MA)), twor, dle, dle2], 'letrd', '%s <_ %s' % (AD, TWO))
    # the product bound
    vr = st([st([hf['grp']], 'rpreccld', '%s e. RR+' % V)], 'rpred', '%s e. RR' % V)
    vge = st([st([hf['grp']], 'rpreccld', '%s e. RR+' % V)], 'rpge0d', '0 <_ %s' % V)
    ule = sy(w, A, mnn, 'mule1', '%s <_ 1' % AU)
    OC = '( 1 x. %s )' % c
    ocr = st([st([], '1red', '1 e. RR'), cre], 'remulcld', '%s e. RR' % OC)
    i1 = st([aur, st([], '1red', '1 e. RR'), cre, cge, ule], 'lemul1ad', '%s <_ %s' % (UC, OC))
    OCV = '( %s x. %s )' % (OC, V)
    i2 = st([ucr, ocr, vr, vge, i1], 'lemul1ad', '%s <_ %s' % (UCV, OCV))
    ucvr = st([ucr, vr], 'remulcld', '%s e. RR' % UCV)
    ocvr = st([ocr, vr], 'remulcld', '%s e. RR' % OCV)
    uc0 = st([aur, cre, st([mf['muc']], 'absge0d', '0 <_ %s' % AU), cge], 'mulge0d', '0 <_ %s' % UC)
    ucv0 = st([ucr, vr, uc0, vge], 'mulge0d', '0 <_ %s' % UCV)
    i3 = st([ucvr, ocvr, adr, twor, ucv0, st([dc], 'absge0d', '0 <_ %s' % AD), i2, dB], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (UCV, AD, OCV, TWO))
    K223 = '( ; 2 2 / 3 )'
    NW = '( %s x. %s )' % (K223, WB)
    T1 = '( ( %s x. %s ) x. ( %s x. %s ) )' % (c, rat, NW, V)
    eqn = lineq(w, A, '( %s x. %s )' % (OCV, TWO), T1, products=True, leaves={c: cre, V: vr, rat: ratr, WB: wr}, atoms=[c, V, rat, WB])
    nwc = st([st([st([num.real(w, K223)], 'a1i', '%s e. RR' % K223), wr], 'remulcld', '%s e. RR' % NW)], 'recnd', '%s e. CC' % NW)
    tq = st([st([nwc, hf['gcc'], hf['gne']], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (NW, g, NW, V))], 'oveq2d',
            '( ( %s x. %s ) x. ( %s / %s ) ) = %s' % (c, rat, NW, g, T1))
    rhs = st([eqn, st([tq], 'eqcomd', '%s = ( ( %s x. %s ) x. ( %s / %s ) )' % (T1, c, rat, NW, g))], 'eqtrd',
             '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (OCV, TWO, c, rat, KB))
    w.qed([lhs, st([i3, rhs], 'breqtrd', '( %s x. %s ) <_ ( ( %s x. %s ) x. %s )' % (UCV, AD, c, rat, KB))], 'eqbrtrd', STATEMENTS['bvssumle'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvmunc', 'bvsspl']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
