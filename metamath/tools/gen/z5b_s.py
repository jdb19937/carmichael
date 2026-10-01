"""Sortie Z5b, section S: summable_fdetTerm (Detector.lean 1396-1446)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5blib import *
from cl import Closure, lift
import lin

ANTE_T = '( %s /\\ ( ( ( C ` K ) e. CC /\\ ( abs ` ( C ` K ) ) <_ 1 ) /\\ ( ( S e. CC /\\ 0 <_ ( Re ` S ) ) /\\ K e. NN ) ) )' % HFD


def z5fdtabs():
    w = W('z5fdtabs', "The termwise bound of Lean summable_fdetTerm (h1, h2, h3): | a ( K ) P ( K ) e ^ ( - K / X ) C ( K ) K ^ -S | <_ "
                      "|_ R K q ^ K with q = e ^ ( - 1 / X ), for | C ( K ) | <_ 1 and 0 <_ Re S.")
    ante = ANTE_T
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0)
    xrp = st([], 'simplrl', 'X e. RR+')
    nrr = st([], 'simplrr', '( N e. V /\\ ( R e. RR /\\ 0 <_ R ) )')
    cK = st([], 'simprll', '( C ` K ) e. CC')
    cK1 = st([], 'simprlr', '( abs ` ( C ` K ) ) <_ 1')
    sS = st([], 'simprrl', '( S e. CC /\\ 0 <_ ( Re ` S ) )')
    sc = st([sS], 'simpld', 'S e. CC'); sre = st([sS], 'simprd', '0 <_ ( Re ` S )')
    knn = st([], 'simprrr', 'K e. NN')
    rr = st([st([nrr], 'simprd', '( R e. RR /\\ 0 <_ R )')], 'simpld', 'R e. RR')
    r0 = st([st([nrr], 'simprd', '( R e. RR /\\ 0 <_ R )')], 'simprd', '0 <_ R')
    kr = st([knn], 'nnred', 'K e. RR'); kc = st([knn], 'nncnd', 'K e. CC'); krp = st([knn], 'nnrpd', 'K e. RR+')
    xr = st([xrp], 'rpred', 'X e. RR'); xc = st([xrp], 'rpcnd', 'X e. CC'); x0 = st([xrp], 'rpne0d', 'X =/= 0')
    a = '( ( A bvA B ) ` K )'; P = '( ( N PFun R ) ` K )'; E = '( exp ` ( -u K / X ) )'; c = '( C ` K )'; Z = '( K ^c -u S )'
    q = QX; QK = '( %s ^ K )' % q
    FL = '( |_ ` R )'
    Q = '( %s x. ( K x. %s ) )' % (FL, QK)
    u1 = '( %s x. %s )' % (a, P); u2 = '( %s x. %s )' % (u1, E); u3 = '( %s x. %s )' % (u2, c); T = '( %s x. %s )' % (u3, Z)
    h1_ = st([hab], 'simpld', '( A e. RR /\\ 0 < A )'); h2_ = st([hab], 'simprd', '( B e. RR /\\ A < B )')
    Ar = st([h1_], 'simpld', 'A e. RR'); A0 = st([h1_], 'simprd', '0 < A'); Br = st([h2_], 'simpld', 'B e. RR'); AB_ = st([h2_], 'simprd', 'A < B')
    arp = st([Ar, A0], 'elrpd', 'A e. RR+')
    brp = st([Br, lin.linarith(w, ante, [A0, AB_], '0 < B', leaves={'A': ('RR', Ar), 'B': ('RR', Br)})], 'elrpd', 'B e. RR+')
    aR = st([st([arp, brp, AB_], '3jca', '( A e. RR+ /\\ B e. RR+ /\\ A < B )'), knn, w.inst('bvare')], 'syl2anc', '%s e. RR' % a)
    ab_ = st([hab, knn, w.inst('z5bvaabs')], 'syl2anc', '( abs ` %s ) <_ K' % a)
    pb_ = st([nrr, knn, w.inst('z5pfunabs')], 'syl2anc', '( abs ` %s ) <_ %s' % (P, FL))
    pre = st([st([nrr], 'simpld', 'N e. V'), rr, knn, w.inst('z5pfunre')], 'syl21anc', '%s e. RR' % P)
    cl = Closure(w, ante, {a: ('RR', aR), P: ('RR', pre), c: ('CC', cK), 'K': ('NN', knn), 'X': ('RR+', xrp), 'R': ('RR', rr), 'S': ('CC', sc)})
    Er = cl.mem(E, 'RR')
    nk = st([kr], 'renegcld', '-u K e. RR')
    kxr = st([nk, xrp], 'rerpdivcld', '( -u K / X ) e. RR')
    Egt = sy(w, ante, kxr, 'efgt0', '0 < %s' % E)
    u1c = cl.mem(u1, 'CC'); u2c = cl.mem(u2, 'CC'); u3c = cl.mem(u3, 'CC'); Zc = cl.mem(Z, 'CC')
    ac = cl.mem(a, 'CC'); pc = cl.mem(P, 'CC'); Ec = cl.mem(E, 'CC')
    AB = lambda x: '( abs ` %s )' % x
    V1 = '( %s x. %s )' % (AB(a), AB(P)); V2 = '( %s x. %s )' % (V1, AB(E)); V3 = '( %s x. %s )' % (V2, AB(c)); V4 = '( %s x. %s )' % (V3, AB(Z))
    e4 = st([ac, pc], 'absmuld', '%s = %s' % (AB(u1), V1))
    e3 = st([u1c, Ec], 'absmuld', '%s = ( %s x. %s )' % (AB(u2), AB(u1), AB(E)))
    e3 = st([e3, st([e4], 'oveq1d', '( %s x. %s ) = %s' % (AB(u1), AB(E), V2))], 'eqtrd', '%s = %s' % (AB(u2), V2))
    e2 = st([u2c, cK], 'absmuld', '%s = ( %s x. %s )' % (AB(u3), AB(u2), AB(c)))
    e2 = st([e2, st([e3], 'oveq1d', '( %s x. %s ) = %s' % (AB(u2), AB(c), V3))], 'eqtrd', '%s = %s' % (AB(u3), V3))
    e1 = st([u3c, Zc], 'absmuld', '%s = ( %s x. %s )' % (AB(T), AB(u3), AB(Z)))
    e1 = st([e1, st([e2], 'oveq1d', '( %s x. %s ) = %s' % (AB(u3), AB(Z), V4))], 'eqtrd', '%s = %s' % (AB(T), V4))
    # |E| = q ^ K
    n1c = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % ante)
    m1 = st([st([kc, n1c, xc, x0], 'divassd', '( ( K x. -u 1 ) / X ) = ( K x. ( -u 1 / X ) )')], 'eqcomd', '( K x. ( -u 1 / X ) ) = ( ( K x. -u 1 ) / X )')
    m2 = st([st([kc, st([], '1cnd', '1 e. CC')], 'mulneg2d', '( K x. -u 1 ) = -u ( K x. 1 )'), st([st([kc], 'mulridd', '( K x. 1 ) = K')], 'negeqd', '-u ( K x. 1 ) = -u K')],
            'eqtrd', '( K x. -u 1 ) = -u K')
    m = st([m1, st([m2], 'oveq1d', '( ( K x. -u 1 ) / X ) = ( -u K / X )')], 'eqtrd', '( K x. ( -u 1 / X ) ) = ( -u K / X )')
    ef = st([st([n1c, xc, x0], 'divcld', '( -u 1 / X ) e. CC'), st([knn], 'nnzd', 'K e. ZZ'), w.inst('efexp')], 'syl2anc', '( exp ` ( K x. ( -u 1 / X ) ) ) = %s' % QK)
    eq = st([st([st([m], 'fveq2d', '( exp ` ( K x. ( -u 1 / X ) ) ) = %s' % E)], 'eqcomd', '%s = ( exp ` ( K x. ( -u 1 / X ) ) )' % E), ef], 'eqtrd', '%s = %s' % (E, QK))
    aE = st([st([Er, st([Egt], 'ltled', '0 <_ %s' % E)], 'absidd', '%s = %s' % (AB(E), E)), eq], 'eqtrd', '%s = %s' % (AB(E), QK))
    # |Z| <_ 1
    ns = st([sc], 'negcld', '-u S e. CC')
    z1 = st([krp, ns, w.inst('abscxp')], 'syl2anc', '%s = ( K ^c ( Re ` -u S ) )' % AB(Z))
    z2 = st([st([sc, w.inst('reneg')], 'syl', '( Re ` -u S ) = -u ( Re ` S )')], 'oveq2d', '( K ^c ( Re ` -u S ) ) = ( K ^c -u ( Re ` S ) )')
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    nrs = st([rsr], 'renegcld', '-u ( Re ` S ) e. RR')
    le0 = lin.linarith(w, ante, [sre], '-u ( Re ` S ) <_ 0', leaves={'( Re ` S )': ('RR', rsr)}, atoms=['( Re ` S )'])
    k1 = st([kr, st([knn], 'nnge1d', '1 <_ K')], 'jca', '( K e. RR /\\ 1 <_ K )')
    bz = st([nrs, st([], '0red', '0 e. RR')], 'jca', '( -u ( Re ` S ) e. RR /\\ 0 e. RR )')
    z3 = st([k1, bz, le0, w.inst('cxplea')], 'syl3anc', '( K ^c -u ( Re ` S ) ) <_ ( K ^c 0 )')
    z4 = st([kc, w.inst('cxp0')], 'syl', '( K ^c 0 ) = 1')
    zz = st([st([z1, z2], 'eqtrd', '%s = ( K ^c -u ( Re ` S ) )' % AB(Z)), z3], 'eqbrtrd', '%s <_ ( K ^c 0 )' % AB(Z))
    zz = st([zz, z4], 'breqtrd', '%s <_ 1' % AB(Z))
    # the product of the bounds
    aa = cl.mem(AB(a), 'RR'); apr = cl.mem(AB(P), 'RR'); aer = cl.mem(AB(E), 'RR'); acr = cl.mem(AB(c), 'RR'); azr = cl.mem(AB(Z), 'RR')
    flr = cl.mem(FL, 'RR'); qkr = cl.mem(QK, 'RR')
    KF = '( K x. %s )' % FL
    kfr = st([kr, flr], 'remulcld', '%s e. RR' % KF)
    b1 = st([aa, kr, apr, flr, st([ac], 'absge0d', '0 <_ %s' % AB(a)), st([pc], 'absge0d', '0 <_ %s' % AB(P)), ab_, pb_], 'lemul12ad', '%s <_ %s' % (V1, KF))
    v1r = st([aa, apr], 'remulcld', '%s e. RR' % V1)
    v10 = st([aa, apr, st([ac], 'absge0d', '0 <_ %s' % AB(a)), st([pc], 'absge0d', '0 <_ %s' % AB(P))], 'mulge0d', '0 <_ %s' % V1)
    B2 = '( %s x. %s )' % (KF, QK)
    b2 = st([v1r, kfr, aer, qkr, v10, st([Ec], 'absge0d', '0 <_ %s' % AB(E)), b1, st([aer, aE], 'eqled', '%s <_ %s' % (AB(E), QK))], 'lemul12ad', '%s <_ %s' % (V2, B2))
    v2r = st([v1r, aer], 'remulcld', '%s e. RR' % V2)
    v20 = st([v1r, aer, v10, st([Ec], 'absge0d', '0 <_ %s' % AB(E))], 'mulge0d', '0 <_ %s' % V2)
    b2r = st([kfr, qkr], 'remulcld', '%s e. RR' % B2)
    B3 = '( %s x. 1 )' % B2
    b3 = st([v2r, b2r, acr, st([], '1red', '1 e. RR'), v20, st([cK], 'absge0d', '0 <_ %s' % AB(c)), b2, cK1], 'lemul12ad', '%s <_ %s' % (V3, B3))
    v3r = st([v2r, acr], 'remulcld', '%s e. RR' % V3)
    v30 = st([v2r, acr, v20, st([cK], 'absge0d', '0 <_ %s' % AB(c))], 'mulge0d', '0 <_ %s' % V3)
    b3r = st([b2r, st([], '1red', '1 e. RR')], 'remulcld', '%s e. RR' % B3)
    B4 = '( %s x. 1 )' % B3
    b4 = st([v3r, b3r, azr, st([], '1red', '1 e. RR'), v30, st([Zc], 'absge0d', '0 <_ %s' % AB(Z)), b3, zz], 'lemul12ad', '%s <_ %s' % (V4, B4))
    fe = lin.lineq(w, ante, B4, Q, leaves={'K': ('RR', kr), FL: ('RR', flr), QK: ('RR', qkr)}, atoms=[FL, QK], products=True)
    tb = st([st([e1, b4], 'eqbrtrd', '%s <_ %s' % (AB(T), B4)), fe], 'breqtrd', '%s <_ %s' % (AB(T), Q))
    # the if
    IFK = FDK('K')
    t3 = w.s([tb], 'adantr', '( ( %s /\\ A < K ) -> %s <_ %s )' % (ante, AB(T), Q))
    fl0 = st([st([rr, r0, w.inst('flge0nn0')], 'syl2anc', '%s e. NN0' % FL)], 'nn0ge0d', '0 <_ %s' % FL)
    n1r = w.s([w.s([], 'neg1rr', '-u 1 e. RR')], 'a1i', '( %s -> -u 1 e. RR )' % ante)
    qrp = st([st([n1r, xrp], 'rerpdivcld', '( -u 1 / X ) e. RR')], 'rpefcld', '%s e. RR+' % q)
    qkp = st([qrp, st([knn], 'nnzd', 'K e. ZZ')], 'rpexpcld', '%s e. RR+' % QK)
    kq0 = st([kr, st([qkp], 'rpred', '%s e. RR' % QK), st([st([knn], 'nnrpd', 'K e. RR+')], 'rpge0d', '0 <_ K'), st([qkp], 'rpge0d', '0 <_ %s' % QK)], 'mulge0d', '0 <_ ( K x. %s )' % QK)
    q0 = st([flr, st([kr, st([qkp], 'rpred', '%s e. RR' % QK)], 'remulcld', '( K x. %s ) e. RR' % QK), fl0, kq0], 'mulge0d', '0 <_ %s' % Q)
    f0 = st([w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % ante), q0], 'eqbrtrd', '( abs ` 0 ) <_ %s' % Q)
    t4 = w.s([f0], 'adantr', '( ( %s /\\ -. A < K ) -> ( abs ` 0 ) <_ %s )' % (ante, Q))
    h1 = w.s([w.s([], 'fveq2', '( %s = %s -> ( abs ` %s ) = ( abs ` %s ) )' % (T, IFK, T, IFK))], 'breq1d', '( %s = %s -> ( ( abs ` %s ) <_ %s <-> ( abs ` %s ) <_ %s ) )' % (T, IFK, T, Q, IFK, Q))
    h2 = w.s([w.s([], 'fveq2', '( 0 = %s -> ( abs ` 0 ) = ( abs ` %s ) )' % (IFK, IFK))], 'breq1d', '( 0 = %s -> ( ( abs ` 0 ) <_ %s <-> ( abs ` %s ) <_ %s ) )' % (IFK, Q, IFK, Q))
    w.qed([h1, h2, t3, t4], 'ifbothda', STATEMENTS['z5fdtabs'])
    return w


def z5fdetcvg():
    w = W('z5fdetcvg', "Lean summable_fdetTerm: the detector series sum_ n > z1 a ( n ) P ( n ) e ^ ( - n / X ) C ( n ) n ^ -S converges "
                       "absolutely for 0 <_ Re S and a character-type C ( | C | <_ 1 ): its terms are at most |_ R n q ^ n, q = e ^ ( - 1 / X ) < 1 "
                       "(geomulcvg, cvgcmpce).")
    ante = '( %s /\\ ( ( C : NN --> CC /\\ A. j e. NN ( abs ` ( C ` j ) ) <_ 1 ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) )' % HFD
    st = mkst(w, ante)
    hfd = st([], 'simpl', HFD)
    cf = st([], 'simprll', 'C : NN --> CC'); cb = st([], 'simprlr', 'A. j e. NN ( abs ` ( C ` j ) ) <_ 1'); sS = st([], 'simprr', '( S e. CC /\\ 0 <_ ( Re ` S ) )')
    xrp = st([st([hfd], 'simprd', '( X e. RR+ /\\ ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) )')], 'simpld', 'X e. RR+')
    nrr = st([st([hfd], 'simprd', '( X e. RR+ /\\ ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) )')], 'simprd', '( N e. V /\\ ( R e. RR /\\ 0 <_ R ) )')
    rr = st([st([nrr], 'simprd', '( R e. RR /\\ 0 <_ R )')], 'simpld', 'R e. RR')
    hab = st([hfd], 'simpld', HAB0)
    q = QX
    n1r = w.s([w.s([], 'neg1rr', '-u 1 e. RR')], 'a1i', '( %s -> -u 1 e. RR )' % ante)
    q1x = st([n1r, xrp], 'rerpdivcld', '( -u 1 / X ) e. RR')
    qrp = st([q1x], 'rpefcld', '%s e. RR+' % q)
    qr = st([qrp], 'rpred', '%s e. RR' % q); qc = st([qrp], 'rpcnd', '%s e. CC' % q)
    aq = st([qr, st([qrp], 'rpge0d', '0 <_ %s' % q)], 'absidd', '( abs ` %s ) = %s' % (q, q))
    xc = st([xrp], 'rpcnd', 'X e. CC'); x0 = st([xrp], 'rpne0d', 'X =/= 0')
    ng = st([st([st([], '1cnd', '1 e. CC'), xc, x0], 'divnegd', '-u ( 1 / X ) = ( -u 1 / X )')], 'eqcomd', '( -u 1 / X ) = -u ( 1 / X )')
    rx = st([xrp], 'rpreccld', '( 1 / X ) e. RR+')
    lt0 = lin.linarith(w, ante, [st([rx], 'rpgt0d', '0 < ( 1 / X )')], '-u ( 1 / X ) < 0', leaves={'( 1 / X )': ('RR', st([rx], 'rpred', '( 1 / X ) e. RR'))}, atoms=['( 1 / X )'])
    lt = st([ng, lt0], 'eqbrtrd', '( -u 1 / X ) < 0')
    el = st([lt, st([q1x, st([], '0red', '0 e. RR'), w.inst('eflt')], 'syl2anc', '( ( -u 1 / X ) < 0 <-> %s < ( exp ` 0 ) )' % q)], 'mpbid', '%s < ( exp ` 0 )' % q)
    ql1 = st([el, w.s([w.s([], 'ef0', '( exp ` 0 ) = 1')], 'a1i', '( %s -> ( exp ` 0 ) = 1 )' % ante)], 'breqtrd', '%s < 1' % q)
    aql = st([aq, ql1], 'eqbrtrd', '( abs ` %s ) < 1' % q)
    F0 = '( m e. NN0 |-> ( m x. ( %s ^ m ) ) )' % q
    gm = w.s([w.s([], 'eqid', '%s = %s' % (F0, F0))], 'geomulcvg', '( ( %s e. CC /\\ ( abs ` %s ) < 1 ) -> seq 0 ( + , %s ) e. dom ~~> )' % (q, q, F0))
    g0 = st([qc, aql, gm], 'syl2anc', 'seq 0 ( + , %s ) e. dom ~~>' % F0)
    # F0 ` k on NN0
    a0 = '( %s /\\ k e. NN0 )' % ante
    f0v, v0 = mpv(w, a0, 'm', 'NN0', '( m x. ( %s ^ m ) )' % q, 'k', w.s([], 'simpr', '( %s -> k e. NN0 )' % a0))
    kq = '( k x. ( %s ^ k ) )' % q
    s0 = mkst(w, a0)
    k0r = s0([s0([], 'simpr', 'k e. NN0')], 'nn0red', 'k e. RR')
    kqr = s0([k0r, s0([lift(w, qr, a0), s0([], 'simpr', 'k e. NN0')], 'reexpcld', '( %s ^ k ) e. RR' % q)], 'remulcld', '%s e. RR' % kq)
    f0c = s0([f0v, s0([kqr], 'recnd', '%s e. CC' % kq)], 'eqeltrd', '( %s ` k ) e. CC' % F0)
    ie = w.s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )'), w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % ante), f0c], 'iserex',
             '( %s -> ( seq 0 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> ) )' % (ante, F0, F0))
    g1 = st([g0, ie], 'mpbid', 'seq 1 ( + , %s ) e. dom ~~>' % F0)
    FL = '( |_ ` R )'
    flr = st([st([rr], 'flcld', '%s e. ZZ' % FL)], 'zred', '%s e. RR' % FL)
    # k in NN: values and the termwise bound
    a1 = '( %s /\\ k e. NN )' % ante
    s1 = mkst(w, a1)
    kn = s1([], 'simpr', 'k e. NN')
    kn0 = s1([kn], 'nnnn0d', 'k e. NN0')
    f0v1 = w.s([s1([], 'simpl', ante), kn0, w.s([f0v], 'ex', '( %s -> ( k e. NN0 -> ( %s ` k ) = %s ) )' % (ante, F0, kq))], 'sylc', '( %s -> ( %s ` k ) = %s )' % (a1, F0, kq))
    kr = s1([kn], 'nnred', 'k e. RR')
    kqr1 = s1([kr, s1([lift(w, qr, a1), kn0], 'reexpcld', '( %s ^ k ) e. RR' % q)], 'remulcld', '%s e. RR' % kq)
    f0r = s1([f0v1, kqr1], 'eqeltrd', '( %s ` k ) e. RR' % F0)
    FK = FDK('k')
    ck = s1([lift(w, cf, a1), kn], 'ffvelcdmd', '( C ` k ) e. CC')
    cjk = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( C ` j ) = ( C ` k ) )')], 'fveq2d', '( j = k -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` k ) ) )')], 'breq1d',
              '( j = k -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` k ) ) <_ 1 ) )')
    ck1 = s1([cjk, lift(w, cb, a1), kn], 'rspcdva', '( abs ` ( C ` k ) ) <_ 1')
    big = s1([lift(w, hfd, a1), s1([s1([ck, ck1], 'jca', '( ( C ` k ) e. CC /\\ ( abs ` ( C ` k ) ) <_ 1 )'), s1([lift(w, sS, a1), kn], 'jca', '( ( S e. CC /\\ 0 <_ ( Re ` S ) ) /\\ k e. NN )')],
                                         'jca', '( ( ( C ` k ) e. CC /\\ ( abs ` ( C ` k ) ) <_ 1 ) /\\ ( ( S e. CC /\\ 0 <_ ( Re ` S ) ) /\\ k e. NN ) )')],
             'jca', '( %s /\\ ( ( ( C ` k ) e. CC /\\ ( abs ` ( C ` k ) ) <_ 1 ) /\\ ( ( S e. CC /\\ 0 <_ ( Re ` S ) ) /\\ k e. NN ) ) )' % HFD)
    bnd = s1([big, w.inst('z5fdtabs')], 'syl', '( abs ` %s ) <_ ( %s x. %s )' % (FK, FL, kq))
    bnd2 = s1([bnd, s1([s1([f0v1], 'eqcomd', '%s = ( %s ` k )' % (kq, F0))], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s ` k ) )' % (FL, kq, FL, F0))], 'breqtrd',
              '( abs ` %s ) <_ ( %s x. ( %s ` k ) )' % (FK, FL, F0))
    # FK in CC
    h1_ = st([hab], 'simpld', '( A e. RR /\\ 0 < A )'); h2_ = st([hab], 'simprd', '( B e. RR /\\ A < B )')
    Ar = st([h1_], 'simpld', 'A e. RR'); A0 = st([h1_], 'simprd', '0 < A'); Br = st([h2_], 'simpld', 'B e. RR'); AB_ = st([h2_], 'simprd', 'A < B')
    arp = st([Ar, A0], 'elrpd', 'A e. RR+')
    brp = st([Br, lin.linarith(w, ante, [A0, AB_], '0 < B', leaves={'A': ('RR', Ar), 'B': ('RR', Br)})], 'elrpd', 'B e. RR+')
    a = '( ( A bvA B ) ` k )'; P = '( ( N PFun R ) ` k )'
    aR = s1([lift(w, st([arp, brp, AB_], '3jca', '( A e. RR+ /\\ B e. RR+ /\\ A < B )'), a1), kn, w.inst('bvare')], 'syl2anc', '%s e. RR' % a)
    pre = s1([lift(w, st([nrr], 'simpld', 'N e. V'), a1), lift(w, rr, a1), kn, w.inst('z5pfunre')], 'syl21anc', '%s e. RR' % P)
    cl = Closure(w, a1, {a: ('RR', aR), P: ('RR', pre), '( C ` k )': ('CC', ck), 'k': ('NN', kn), 'X': ('RR+', lift(w, xrp, a1)), 'S': ('CC', lift(w, st([sS], 'simpld', 'S e. CC'), a1)),
                         'A': ('RR', lift(w, Ar, a1))})
    fkc = cl.mem(FK, 'CC')
    nnz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % ante)
    res = []
    for absd in (True, False):
        body = '( abs ` %s )' % FDK('n') if absd else FDK('n')
        G = '( n e. NN |-> %s )' % body
        gv, val = mpv(w, a1, 'n', 'NN', body, 'k', kn)
        gc = s1([gv, s1([fkc], 'abscld', '( abs ` %s ) e. RR' % FK) if absd else fkc], 'eqeltrd', '( %s ` k ) e. %s' % (G, 'RR' if absd else 'CC'))
        if absd:
            gc = s1([gc], 'recnd', '( %s ` k ) e. CC' % G)
        a2 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % ante
        s2 = mkst(w, a2)
        kn2 = s2([s2([], 'simpr', 'k e. ( ZZ>= ` 1 )'), w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'sylibr', 'k e. NN')
        up = lambda stp, f: w.s([w.s([], 'simpl', '( %s -> %s )' % (a2, ante)), kn2, w.s([stp], 'ex', '( %s -> ( k e. NN -> %s ) )' % (ante, f))], 'sylc', '( %s -> %s )' % (a2, f))
        gva = up(gv, '( %s ` k ) = %s' % (G, val))
        e1 = s2([gva], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (G, val))
        if absd:
            e1 = s2([e1, s2([up(fkc, '%s e. CC' % FK), w.inst('absidm')], 'syl', '( abs ` ( abs ` %s ) ) = ( abs ` %s )' % (FK, FK))], 'eqtrd', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (G, FK))
        b7 = s2([e1, up(bnd2, '( abs ` %s ) <_ ( %s x. ( %s ` k ) )' % (FK, FL, F0))], 'eqbrtrd', '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) )' % (G, FL, F0))
        cv = w.s([nnz, one, f0r, gc, g1, flr, b7], 'cvgcmpce', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ante, G))
        res.append(cv)
    w.qed(res, 'jca', STATEMENTS['z5fdetcvg'])
    return w


if __name__ == '__main__':
    import z5blib
    for f in sys.argv[1:]:
        z5blib.run(globals()[f]())
