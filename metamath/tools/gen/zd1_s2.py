"""Sortie ZD1: ZeroDensity.lean sections 2-5, the real-variable content."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import Closure, lift

PR = lambda M: 'prod_ n e. ( 2 ... %s ) ( 1 - ( 1 / n ) )' % M
PM = lambda M: '( %s x. %s ) = 1' % (PR(M), M)


def wc(w, expr, v, V):
    idv = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, V, v, V))
    st, new = w.wcongr(expr, {v: V}, '%s = %s' % (v, V), {v: idv})
    return st


def zdprodtel():
    w = W('zdprodtel', "prod_ 1 < n <_ M ( 1 - 1 / n ) = 1 / M (Lean prod_Ioc_one_sub_inv), by induction on the cleared form "
                       "( prod x. M ) = 1.")
    # base: 2 e. ZZ -> P(2)
    a = '2 e. ZZ'
    st = mkst(w, a)
    H = '( 1 - ( 1 / 2 ) )'
    idn = w.s([], 'id', '( n = 2 -> n = 2 )')
    cn, _ = w.congr('( 1 - ( 1 / n ) )', {'n': '2'}, 'n = 2', {'n': idn})
    hc = Closure(w, a, {}).mem(H, 'CC')
    p2 = w.s([cn], 'fprod1', '( ( 2 e. ZZ /\\ %s e. CC ) -> %s = %s )' % (H, PR('2'), H))
    p2b = st([w.s([], 'id', '( 2 e. ZZ -> 2 e. ZZ )'), hc, p2], 'syl2anc', '%s = %s' % (PR('2'), H))
    m2 = st([p2b], 'oveq1d', '( %s x. 2 ) = ( %s x. 2 )' % (PR('2'), H))
    v2 = lineq(w, a, '( %s x. 2 )' % H, '1')
    base = st([m2, v2], 'eqtrd', PM('2'))
    # step: k e. ( ZZ>= ` 2 ) -> ( P(k) -> P(k+1) )
    a = 'k e. ( ZZ>= ` 2 )'
    st = mkst(w, a)
    ku = w.s([], 'id', '( %s -> %s )' % (a, a))
    kz = sy(w, a, ku, 'eluzelz', 'k e. ZZ')
    kn = sy(w, a, ku, 'eluz2nn', 'k e. NN')
    kr = st([kn], 'nnred', 'k e. RR'); kc = st([kn], 'nncnd', 'k e. CC')
    k1n = st([kn], 'peano2nnd', '( k + 1 ) e. NN')
    k1c = st([k1n], 'nncnd', '( k + 1 ) e. CC')
    idk = w.s([], 'id', '( n = ( k + 1 ) -> n = ( k + 1 ) )')
    ck, _ = w.congr('( 1 - ( 1 / n ) )', {'n': '( k + 1 )'}, 'n = ( k + 1 )', {'n': idk})
    b = '( %s /\\ n e. ( 2 ... ( k + 1 ) ) )' % a
    nnb = w.s([w.s([w.s([], 'simpr', '( %s -> n e. ( 2 ... ( k + 1 ) ) )' % b), w.inst('elfzuz')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % b), w.inst('eluz2nn')],
              'syl', '( %s -> n e. NN )' % b)
    c = Closure(w, b, {'n': ('NN', nnb)})
    bc = c.mem('( 1 - ( 1 / n ) )', 'CC')
    fp = st([ku, bc, ck], 'fprodp1', '%s = ( %s x. ( 1 - ( 1 / ( k + 1 ) ) ) )' % (PR('( k + 1 )'), PR('k')))
    # closures of the atoms
    bk = '( %s /\\ n e. ( 2 ... k ) )' % a
    nnk = w.s([w.s([w.s([], 'simpr', '( %s -> n e. ( 2 ... k ) )' % bk), w.inst('elfzuz')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % bk), w.inst('eluz2nn')],
              'syl', '( %s -> n e. NN )' % bk)
    ck2 = Closure(w, bk, {'n': ('NN', nnk)})
    pkr = st([st([], 'fzfid', '( 2 ... k ) e. Fin'), ck2.mem('( 1 - ( 1 / n ) )', 'RR')], 'fprodrecl', '%s e. RR' % PR('k'))
    r = '( 1 / ( k + 1 ) )'
    rr = st([k1n], 'nnrecred', '%s e. RR' % r)
    rid = st([k1c, st([k1n], 'nnne0d', '( k + 1 ) =/= 0')], 'recid2d', '( %s x. ( k + 1 ) ) = 1' % r)
    rid2 = st([rid], 'oveq2d', '( %s x. ( %s x. ( k + 1 ) ) ) = ( %s x. 1 )' % (PR('k'), r, PR('k')))
    aI = '( %s /\\ %s )' % (a, PM('k'))
    ih = w.s([], 'simpr', '( %s -> %s )' % (aI, PM('k')))
    L_ = lambda x: lift(w, x, aI)
    Q = '( ( %s x. ( 1 - %s ) ) x. ( k + 1 ) )' % (PR('k'), r)
    e = lineq(w, aI, Q, '1', hyps=[ih, L_(rid2)], products=True, leaves={PR('k'): L_(pkr), r: L_(rr), 'k': L_(kr)})
    e2 = w.s([w.s([L_(fp)], 'oveq1d', '( %s -> ( %s x. ( k + 1 ) ) = %s )' % (aI, PR('( k + 1 )'), Q)), e], 'eqtrd', '( %s -> %s )' % (aI, PM('( k + 1 )')))
    step = w.s([e2], 'ex', '( %s -> ( %s -> %s ) )' % (a, PM('k'), PM('( k + 1 )')))
    ui = w.s([wc(w, PM('i'), 'i', '2'), wc(w, PM('i'), 'i', 'k'), wc(w, PM('i'), 'i', '( k + 1 )'), wc(w, PM('i'), 'i', 'M'), base, step], 'uzind4',
             '( M e. ( ZZ>= ` 2 ) -> %s )' % PM('M'))
    # M = 1
    fz = w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2z', '2 e. ZZ'), w.s([], '1z', '1 e. ZZ'), w.inst('fzn')], 'mp2an', '( 1 < 2 <-> ( 2 ... 1 ) = (/) )')],
             'mpbi', '( 2 ... 1 ) = (/)')
    p1 = w.s([w.s([fz], 'prodeq1i', '%s = prod_ n e. (/) ( 1 - ( 1 / n ) )' % PR('1')), w.s([], 'prod0', 'prod_ n e. (/) ( 1 - ( 1 / n ) ) = 1')], 'eqtri',
             '%s = 1' % PR('1'))
    q1 = w.s([w.s([p1], 'oveq1i', '( %s x. 1 ) = ( 1 x. 1 )' % PR('1')), w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'eqtri', PM('1'))
    c1 = w.s([q1, wc(w, PM('M'), 'M', '1')], 'mpbiri', '( M = 1 -> %s )' % PM('M'))
    both = w.s([c1, ui], 'jaoi', '( ( M = 1 \\/ M e. ( ZZ>= ` 2 ) ) -> %s )' % PM('M'))
    pm = w.s([w.s([], 'elnn1uz2', '( M e. NN <-> ( M = 1 \\/ M e. ( ZZ>= ` 2 ) ) )'), both], 'sylbi', '( M e. NN -> %s )' % PM('M'))
    a = 'M e. NN'
    st = mkst(w, a)
    mn = w.s([], 'id', '( M e. NN -> M e. NN )')
    b2 = '( %s /\\ n e. ( 2 ... M ) )' % a
    nn2 = w.s([w.s([w.s([], 'simpr', '( %s -> n e. ( 2 ... M ) )' % b2), w.inst('elfzuz')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % b2), w.inst('eluz2nn')],
              'syl', '( %s -> n e. NN )' % b2)
    cm = Closure(w, b2, {'n': ('NN', nn2)})
    pmc = st([st([st([], 'fzfid', '( 2 ... M ) e. Fin'), cm.mem('( 1 - ( 1 / n ) )', 'RR')], 'fprodrecl', '%s e. RR' % PR('M'))], 'recnd', '%s e. CC' % PR('M'))
    bi = st([a1c(w, a, 'ax-1cn', '1 e. CC'), pmc, st([mn], 'nncnd', 'M e. CC'), st([mn], 'nnne0d', 'M =/= 0')], 'divmul3d',
            '( ( 1 / M ) = %s <-> 1 = ( %s x. M ) )' % (PR('M'), PR('M')))
    g = st([st([pm], 'eqcomd', '1 = ( %s x. M )' % PR('M')), bi], 'mpbird', '( 1 / M ) = %s' % PR('M'))
    w.qed([g], 'eqcomd', STATEMENTS['zdprodtel'])
    return w


def zdprodle():
    w = W('zdprodle', "A product of factors in [ 0 , 1 ] over a finite set is at most the product over a subset "
                      "(Lean prod_le_prod_subset_of_le_one').")
    hyps_of(w, 'zdprodle')
    st = mkst(w, 'ph')
    D = '( B \\ A )'
    un = st([w.s(['2', w.s([], 'undif', '( A C_ B <-> ( A u. %s ) = B )' % D)], 'sylib', '( ph -> ( A u. %s ) = B )' % D)], 'eqcomd', 'B = ( A u. %s )' % D)
    dj = a1c(w, 'ph', 'disjdif', '( A i^i %s ) = (/)' % D)
    kb = '( ph /\\ k e. B )'
    ka = '( ph /\\ k e. A )'
    kd = '( ph /\\ k e. %s )' % D
    a2b = w.s([w.s(['2'], 'sseld', '( ph -> ( k e. A -> k e. B ) )')], 'imp', '( %s -> k e. B )' % ka)
    d2b = w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (kd, D)), w.inst('eldifi')], 'syl', '( %s -> k e. B )' % kd)
    # restate hyps under the subsets via syl2anc with the membership (hyp is ( ( ph /\ k e. B ) -> ... ))
    def at(ante, mem, h, f):
        return w.s([w.s([], 'simpl', '( %s -> ph )' % ante), mem, h], 'syl2anc', '( %s -> %s )' % (ante, f))
    ca = at(ka, a2b, '3', 'C e. RR'); c0a = at(ka, a2b, '4', '0 <_ C')
    cd = at(kd, d2b, '3', 'C e. RR'); c0d = at(kd, d2b, '4', '0 <_ C'); c1d = at(kd, d2b, '5', 'C <_ 1')
    fa = st(['1', '2'], 'ssfid', 'A e. Fin')
    fd = st(['1', a1c(w, 'ph', 'difss', '%s C_ B' % D)], 'ssfid', '%s e. Fin' % D)
    sp = st([dj, un, '1', w.s(['3'], 'recnd', '( %s -> C e. CC )' % kb)], 'fprodsplit', 'prod_ k e. B C = ( prod_ k e. A C x. prod_ k e. %s C )' % D)
    nf = w.s([], 'nfv', 'F/ k ph')
    pa0 = st([nf, fa, ca, c0a], 'fprodge0', '0 <_ prod_ k e. A C')
    par = st([fa, ca], 'fprodrecl', 'prod_ k e. A C e. RR')
    pdr = st([fd, cd], 'fprodrecl', 'prod_ k e. %s C e. RR' % D)
    pd1 = st([nf, fd, cd, c0d, a1c(w, kd, '1re', '1 e. RR'), c1d], 'fprodle', 'prod_ k e. %s C <_ prod_ k e. %s 1' % (D, D))
    p1 = st([st([fd], 'olcd', '( %s C_ ( ZZ>= ` 0 ) \\/ %s e. Fin )' % (D, D)), w.inst('prod1')], 'syl', 'prod_ k e. %s 1 = 1' % D)
    pd = st([pd1, p1], 'breqtrd', 'prod_ k e. %s C <_ 1' % D)
    m = st([pdr, st([], '1red', '1 e. RR'), par, pa0, pd], 'lemul2ad', '( prod_ k e. A C x. prod_ k e. %s C ) <_ ( prod_ k e. A C x. 1 )' % D)
    m2 = st([m, st([st([par], 'recnd', 'prod_ k e. A C e. CC')], 'mulridd', '( prod_ k e. A C x. 1 ) = prod_ k e. A C')], 'breqtrd',
            '( prod_ k e. A C x. prod_ k e. %s C ) <_ prod_ k e. A C' % D)
    w.qed([sp, m2], 'eqbrtrd', STATEMENTS['zdprodle'])
    return w


def zdinvqr():
    w = W('zdinvqr', "Q_R >_ 1 / R (Lean inv_le_QR, Q_R in its product form): the product of ( 1 - 1 / p ) over the primes p | N, p <_ R "
                     "dominates the product over all 1 < n <_ |_ R, which telescopes to 1 / |_ R (zdprodtel, zdprodle).")
    ante = '( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) )'
    st = mkst(w, ante)
    rr = st([st([], 'simpr', '( R e. RR /\\ 1 <_ R )')], 'simpld', 'R e. RR')
    r1 = st([st([], 'simpr', '( R e. RR /\\ 1 <_ R )')], 'simprd', '1 <_ R')
    F = '( |_ ` R )'
    fn = st([rr, r1, w.inst('flge1nn')], 'syl2anc', '%s e. NN' % F)
    fz = st([fn], 'nnzd', '%s e. ZZ' % F)
    S = '{ q e. Prime | ( q || N /\\ q <_ R ) }'
    RB = '( 2 ... %s )' % F
    # S C_ RB
    a = '( ( %s /\\ q e. Prime ) /\\ ( q || N /\\ q <_ R ) )' % ante
    sa = mkst(w, a)
    qp = w.s([], 'simplr', '( %s -> q e. Prime )' % a)
    qu = sy(w, a, qp, 'prmuz2', 'q e. ( ZZ>= ` 2 )')
    qz = sy(w, a, qp, 'prmz', 'q e. ZZ')
    qr_ = w.s([], 'simprr', '( %s -> q <_ R )' % a)
    qf = sa([qr_, sa([lift(w, rr, a), qz, w.inst('flge')], 'syl2anc', '( q <_ R <-> q <_ %s )' % F)], 'mpbid', 'q <_ %s' % F)
    qin = sa([qf, sa([qu, lift(w, fz, a), w.inst('elfz5')], 'syl2anc', '( q e. %s <-> q <_ %s )' % (RB, F))], 'mpbird', 'q e. %s' % RB)
    imp = w.s([qin], 'ex', '( ( %s /\\ q e. Prime ) -> ( ( q || N /\\ q <_ R ) -> q e. %s ) )' % (ante, RB))
    ral = w.s([imp], 'ralrimiva', '( %s -> A. q e. Prime ( ( q || N /\\ q <_ R ) -> q e. %s ) )' % (ante, RB))
    ss = w.s([ral, w.s([], 'rabss', '( %s C_ %s <-> A. q e. Prime ( ( q || N /\\ q <_ R ) -> q e. %s ) )' % (S, RB, RB))], 'sylibr', '( %s -> %s C_ %s )' % (ante, S, RB))
    # factors in [ 0 , 1 ] on RB
    b = '( %s /\\ p e. %s )' % (ante, RB)
    pn = w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (b, RB)), w.inst('elfzuz')], 'syl', '( %s -> p e. ( ZZ>= ` 2 ) )' % b), w.inst('eluz2nn')],
             'syl', '( %s -> p e. NN )' % b)
    sb = mkst(w, b)
    pr_ = sb([pn], 'nnred', 'p e. RR')
    ipr = sb([pn], 'nnrecred', '( 1 / p ) e. RR')
    ip0 = sb([sb([pn], 'nnrpd', 'p e. RR+')], 'rpreccld', '( 1 / p ) e. RR+')
    p1 = w.s([pn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ p )' % b)
    bi = sb([a1c(w, b, '1rp', '1 e. RR+'), sb([pn], 'nnrpd', 'p e. RR+')], 'lerecd', '( 1 <_ p <-> ( 1 / p ) <_ ( 1 / 1 ) )')
    ile = sb([sb([p1, bi], 'mpbid', '( 1 / p ) <_ ( 1 / 1 )'), a1c(w, b, '1div1e1', '( 1 / 1 ) = 1')], 'breqtrd', '( 1 / p ) <_ 1')
    CC_ = '( 1 - ( 1 / p ) )'
    cr = sb([sb([], '1red', '1 e. RR'), ipr], 'resubcld', '%s e. RR' % CC_)
    c0 = linarith(w, b, [ile], '0 <_ %s' % CC_, leaves={'( 1 / p )': ipr})
    c1 = linarith(w, b, [sb([ip0], 'rpge0d', '0 <_ ( 1 / p )')], '%s <_ 1' % CC_, leaves={'( 1 / p )': ipr})
    pl = w.s([st([], 'fzfid', '%s e. Fin' % RB), ss, cr, c0, c1], 'zdprodle', '( %s -> prod_ p e. %s %s <_ prod_ p e. %s %s )' % (ante, RB, CC_, S, CC_))
    tel = sy(w, ante, fn, 'zdprodtel', '%s = ( 1 / %s )' % (PR(F), F))
    cb = w.s([cbvp(w, CC_)], 'cbvprodv', '%s = prod_ p e. %s %s' % (PR(F), RB, CC_))
    t2 = st([w.s([cb], 'a1i', '( %s -> %s = prod_ p e. %s %s )' % (ante, PR(F), RB, CC_)), tel],
            'eqtr3d', 'prod_ p e. %s %s = ( 1 / %s )' % (RB, CC_, F))
    frp = st([fn], 'nnrpd', '%s e. RR+' % F)
    rrp = st([rr, linarith(w, ante, [r1], '0 < R', leaves={'R': rr})], 'elrpd', 'R e. RR+')
    fl = sy(w, ante, rr, 'flle', '%s <_ R' % F)
    rec = st([fl, st([frp, rrp], 'lerecd', '( %s <_ R <-> ( 1 / R ) <_ ( 1 / %s ) )' % (F, F))], 'mpbid', '( 1 / R ) <_ ( 1 / %s )' % F)
    g = st([rec, st([t2], 'eqcomd', '( 1 / %s ) = prod_ p e. %s %s' % (F, RB, CC_))], 'breqtrd', '( 1 / R ) <_ prod_ p e. %s %s' % (RB, CC_))
    sfin = st([st([], 'fzfid', '%s e. Fin' % RB), ss], 'ssfid', '%s e. Fin' % S)
    bS = '( %s /\\ p e. %s )' % (ante, S)
    pnS = w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (bS, S)), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % bS), w.inst('prmnn')], 'syl', '( %s -> p e. NN )' % bS)
    crS = Closure(w, bS, {'p': ('NN', pnS)}).mem(CC_, 'RR')
    psr = st([sfin, crS], 'fprodrecl', 'prod_ p e. %s %s e. RR' % (S, CC_))
    pbr = st([st([], 'fzfid', '%s e. Fin' % RB), cr], 'fprodrecl', 'prod_ p e. %s %s e. RR' % (RB, CC_))
    w.qed([st([rrp], 'rpreccld', '( 1 / R ) e. RR+') and st([st([rrp], 'rpreccld', '( 1 / R ) e. RR+')], 'rpred', '( 1 / R ) e. RR'), pbr, psr, g, pl], 'letrd', STATEMENTS['zdinvqr'])
    return w


def dsimple(w, ante, dr, d1):
    """D e. RR+, CC, =/= 0 from D e. RR, 1 < D"""
    st = mkst(w, ante)
    drp = st([dr, linarith(w, ante, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    return dict(drp=drp, dc=st([dr], 'recnd', 'D e. CC'), dne=st([drp], 'rpne0d', 'D =/= 0'))


def zdqrsq():
    w = W('zdqrsq', "D ^c ( 13 / 500 ) <_ Q_R ^ 2 D ^c ( 23 / 500 ) at R = D ^c ( 1 / 100 ) (Lean QR_sq_mul_rpow_ge), from Q_R >_ 1 / R (zdinvqr).")
    ante = '( N e. NN /\\ ( D e. RR /\\ 1 < D ) )'
    st = mkst(w, ante)
    nn = st([], 'simpl', 'N e. NN')
    dr = st([st([], 'simpr', '( D e. RR /\\ 1 < D )')], 'simpld', 'D e. RR'); d1 = st([st([], 'simpr', '( D e. RR /\\ 1 < D )')], 'simprd', '1 < D')
    f = dsimple(w, ante, dr, d1)
    H = '( 1 / ; ; 1 0 0 )'
    hr = litr(w, ante, H)
    rrp = st([f['drp'], hr], 'rpcxpcld', '%s e. RR+' % RP); rr = st([rrp], 'rpred', '%s e. RR' % RP)
    c0 = st([f['dc']], 'cxp0d', '( D ^c 0 ) = 1')
    le0 = st([dr, st([d1], 'ltled', '1 <_ D'), st([], '0red', '0 e. RR'), hr, litle(w, ante, '0', H)], 'cxplead', '( D ^c 0 ) <_ %s' % RP)
    r1 = st([c0, le0], 'eqbrtrrd', '1 <_ %s' % RP)
    Q = QRP('N', RP)
    iq = st([nn, bind(w, ante, rr, r1, '%s e. RR' % RP, '1 <_ %s' % RP), w.inst('zdinvqr')], 'syl2anc', '( 1 / %s ) <_ %s' % (RP, Q))
    U = '( D ^c -u %s )' % H
    ue = st([f['dc'], f['dne'], st([hr], 'recnd', '%s e. CC' % H)], 'cxpnegd', '%s = ( 1 / %s )' % (U, RP))
    uq = st([ue, iq], 'eqbrtrd', '%s <_ %s' % (U, Q))
    nh = st([hr], 'renegcld', '-u %s e. RR' % H)
    urp = st([f['drp'], nh], 'rpcxpcld', '%s e. RR+' % U); ur = st([urp], 'rpred', '%s e. RR' % U)
    E23 = '( ; 2 3 / ; ; 5 0 0 )'; E13 = '( ; 1 3 / ; ; 5 0 0 )'
    ex = '( ( -u %s + -u %s ) + %s )' % (H, H, E23)
    ee = lineq(w, ante, ex, E13)
    c1 = st([ee], 'oveq2d', '( D ^c %s ) = ( D ^c %s )' % (ex, E13))
    nhc = st([nh], 'recnd', '-u %s e. CC' % H)
    e23c = st([litr(w, ante, E23)], 'recnd', '%s e. CC' % E23)
    a1 = st([f['dc'], f['dne'], st([nhc, nhc], 'addcld', '( -u %s + -u %s ) e. CC' % (H, H)), e23c], 'cxpaddd',
            '( D ^c %s ) = ( ( D ^c ( -u %s + -u %s ) ) x. ( D ^c %s ) )' % (ex, H, H, E23))
    a2 = st([f['dc'], f['dne'], nhc, nhc], 'cxpaddd', '( D ^c ( -u %s + -u %s ) ) = ( %s x. %s )' % (H, H, U, U))
    a3 = st([a2], 'oveq1d', '( ( D ^c ( -u %s + -u %s ) ) x. ( D ^c %s ) ) = ( ( %s x. %s ) x. ( D ^c %s ) )' % (H, H, E23, U, U, E23))
    lhs = eqtr(w, ante, [st([c1], 'eqcomd', '( D ^c %s ) = ( D ^c %s )' % (E13, ex)), a1, a3], None)
    # Q real (a product of reals over a finite set of primes)
    S = '{ q e. Prime | ( q || N /\\ q <_ %s ) }' % RP
    bS = '( %s /\\ p e. %s )' % (ante, S)
    pnS = w.s([w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (bS, S)), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % bS), w.inst('prmnn')], 'syl', '( %s -> p e. NN )' % bS)
    crS = Closure(w, bS, {'p': ('NN', pnS)}).mem('( 1 - ( 1 / p ) )', 'RR')
    FL = '( |_ ` %s )' % RP
    sfin = st([st([], 'fzfid', '( 2 ... %s ) e. Fin' % FL), qss(w, ante, rr, S)], 'ssfid', '%s e. Fin' % S)
    qrr = st([sfin, crS], 'fprodrecl', '%s e. RR' % Q)
    u0 = st([urp], 'rpge0d', '0 <_ %s' % U)
    m = st([ur, qrr, ur, qrr, u0, u0, uq, uq], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (U, U, Q, Q))
    sq = st([st([qrr], 'recnd', '%s e. CC' % Q)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (Q, Q, Q))
    m2 = st([m, st([sq], 'eqcomd', '( %s x. %s ) = ( %s ^ 2 )' % (Q, Q, Q))], 'breqtrd', '( %s x. %s ) <_ ( %s ^ 2 )' % (U, U, Q))
    d23 = st([f['drp'], litr(w, ante, E23)], 'rpcxpcld', '( D ^c %s ) e. RR+' % E23)
    m3 = st([st([ur, ur], 'remulcld', '( %s x. %s ) e. RR' % (U, U)), st([qrr], 'resqcld', '( %s ^ 2 ) e. RR' % Q), st([d23], 'rpred', '( D ^c %s ) e. RR' % E23),
             st([d23], 'rpge0d', '0 <_ ( D ^c %s )' % E23), m2], 'lemul1ad', '( ( %s x. %s ) x. ( D ^c %s ) ) <_ ( ( %s ^ 2 ) x. ( D ^c %s ) )' % (U, U, E23, Q, E23))
    w.qed([lhs, m3], 'eqbrtrd', STATEMENTS['zdqrsq'])
    return w


def qss(w, ante, rr, S):
    """( ante -> S C_ ( 2 ... ( |_ ` R ) ) ) for S = { q e. Prime | ( q || N /\\ q <_ R ) }, R from rr: ( ante -> R e. RR )"""
    from cl import formula_of, strip_ante
    R = strip_ante(formula_of(w, rr), ante).split(' e. RR')[0]
    F = '( |_ ` %s )' % R
    RB = '( 2 ... %s )' % F
    a = '( ( %s /\\ q e. Prime ) /\\ ( q || N /\\ q <_ %s ) )' % (ante, R)
    sa = mkst(w, a)
    qp = w.s([], 'simplr', '( %s -> q e. Prime )' % a)
    qu = sy(w, a, qp, 'prmuz2', 'q e. ( ZZ>= ` 2 )')
    qz = sy(w, a, qp, 'prmz', 'q e. ZZ')
    qr_ = w.s([], 'simprr', '( %s -> q <_ %s )' % (a, R))
    qf = sa([qr_, sa([lift(w, rr, a), qz, w.inst('flge')], 'syl2anc', '( q <_ %s <-> q <_ %s )' % (R, F))], 'mpbid', 'q <_ %s' % F)
    fz = sa([lift(w, rr, a)], 'flcld', '%s e. ZZ' % F)
    qin = sa([qf, sa([qu, fz, w.inst('elfz5')], 'syl2anc', '( q e. %s <-> q <_ %s )' % (RB, F))], 'mpbird', 'q e. %s' % RB)
    imp = w.s([qin], 'ex', '( ( %s /\\ q e. Prime ) -> ( ( q || N /\\ q <_ %s ) -> q e. %s ) )' % (ante, R, RB))
    ral = w.s([imp], 'ralrimiva', '( %s -> A. q e. Prime ( ( q || N /\\ q <_ %s ) -> q e. %s ) )' % (ante, R, RB))
    return w.s([ral, w.s([], 'rabss', '( %s C_ %s <-> A. q e. Prime ( ( q || N /\\ q <_ %s ) -> q e. %s ) )' % (S, RB, R, RB))], 'sylibr',
               '( %s -> %s C_ %s )' % (ante, S, RB))


def zdxrpow():
    w = W('zdxrpow', "X ^ ( 2 - 2 T ) <_ D ^c ( 12 / 500 ) for X = D ^c ( 6 / 5 ), T >_ 99 / 100 (Lean Xpar_rpow_le).")
    ante = '( ( D e. RR /\\ 1 < D ) /\\ ( T e. RR /\\ ( ; 9 9 / ; ; 1 0 0 ) <_ T ) )'
    st = mkst(w, ante)
    dr = st([st([], 'simpl', '( D e. RR /\\ 1 < D )')], 'simpld', 'D e. RR'); d1 = st([st([], 'simpl', '( D e. RR /\\ 1 < D )')], 'simprd', '1 < D')
    tr = st([st([], 'simpr', '( T e. RR /\\ ( ; 9 9 / ; ; 1 0 0 ) <_ T )')], 'simpld', 'T e. RR')
    t99 = st([st([], 'simpr', '( T e. RR /\\ ( ; 9 9 / ; ; 1 0 0 ) <_ T )')], 'simprd', '( ; 9 9 / ; ; 1 0 0 ) <_ T')
    f = dsimple(w, ante, dr, d1)
    br = st([a1c(w, ante, '2re', '2 e. RR'), st([a1c(w, ante, '2re', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B2)
    E = '( ( 6 / 5 ) x. %s )' % B2
    m = st([f['drp'], litr(w, ante, '( 6 / 5 )'), st([br], 'recnd', '%s e. CC' % B2)], 'cxpmuld', '( D ^c %s ) = %s' % (E, XB))
    er = st([litr(w, ante, '( 6 / 5 )'), br], 'remulcld', '%s e. RR' % E)
    le3 = linarith(w, ante, [t99], '%s <_ ( 3 / ; ; 1 2 5 )' % E, leaves={'T': tr})
    le = st([le3, w.s([num._reduce_frac(w, 12, 500)], 'a1i', '( %s -> ( ; 1 2 / ; ; 5 0 0 ) = ( 3 / ; ; 1 2 5 ) )' % ante)], 'breqtrrd', '%s <_ ( ; 1 2 / ; ; 5 0 0 )' % E)
    r12 = w.s([w.s([num.re_nat(w, 12), num.re_nat(w, 500), num.ne0_nat(w, 500)], 'redivcli', '( ; 1 2 / ; ; 5 0 0 ) e. RR')], 'a1i',
              '( %s -> ( ; 1 2 / ; ; 5 0 0 ) e. RR )' % ante)
    c = st([dr, st([d1], 'ltled', '1 <_ D'), er, r12, le], 'cxplead', '( D ^c %s ) <_ ( D ^c ( ; 1 2 / ; ; 5 0 0 ) )' % E)
    w.qed([m, c], 'eqbrtrrd', STATEMENTS['zdxrpow'])
    return w


def zd10exp():
    w = W('zd10exp', "1 + A <_ 10 e ^ ( A / 10 ) for A >_ 0 (Lean one_add_le_ten_exp).")
    ante = '( A e. RR /\\ 0 <_ A )'
    st = mkst(w, ante)
    ar = st([], 'simpl', 'A e. RR'); a0 = st([], 'simpr', '0 <_ A')
    q = st([ar, litr(w, ante, '; 1 0'), st([a1c(w, ante, '10nn', '; 1 0 e. NN')], 'nnne0d', '; 1 0 =/= 0')], 'redivcld', '( A / ; 1 0 ) e. RR')
    q0 = linarith(w, ante, [a0], '0 <_ ( A / ; 1 0 )', leaves={'A': ar})
    e = st([q, q0, w.inst('bvefge1p')], 'syl2anc', '( 1 + ( A / ; 1 0 ) ) <_ ( exp ` ( A / ; 1 0 ) )')
    E = '( exp ` ( A / ; 1 0 ) )'
    linarith(w, ante, [e, a0], '( 1 + A ) <_ ( ; 1 0 x. %s )' % E, leaves={'A': ar, E: st([q], 'reefcld', '%s e. RR' % E)}, name='qed')
    return w


def zdxexp():
    w = W('zdxexp', "X ^ ( 2 - 2 T ) e ^ ( ( 1 - T ) log D / 10 ) = D ^c ( ( 5 / 2 ) ( 1 - T ) ) for X = D ^c ( 6 / 5 ) (Lean Xpar_rpow_mul_exp).")
    ante = '( D e. RR+ /\\ T e. RR )'
    st = mkst(w, ante)
    drp = st([], 'simpl', 'D e. RR+'); tr = st([], 'simpr', 'T e. RR')
    dc = st([drp], 'rpcnd', 'D e. CC'); dne = st([drp], 'rpne0d', 'D =/= 0')
    L = '( log ` D )'; lr = st([drp], 'relogcld', '%s e. RR' % L)
    br = st([a1c(w, ante, '2re', '2 e. RR'), st([a1c(w, ante, '2re', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B2)
    E = '( ( 6 / 5 ) x. %s )' % B2
    er = st([litr(w, ante, '( 6 / 5 )'), br], 'remulcld', '%s e. RR' % E)
    m = st([drp, litr(w, ante, '( 6 / 5 )'), st([br], 'recnd', '%s e. CC' % B2)], 'cxpmuld', '( D ^c %s ) = %s' % (E, XB))
    c1 = st([dc, dne, st([er], 'recnd', '%s e. CC' % E)], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (E, E, L))
    xe = st([m, c1], 'eqtr3d', '%s = ( exp ` ( %s x. %s ) )' % (XB, E, L))
    U = '( %s x. %s )' % (E, L); V = '( ( ( 1 - T ) x. %s ) / ; 1 0 )' % L
    ur = st([er, lr], 'remulcld', '%s e. RR' % U)
    vr = Closure(w, ante, {'T': ('RR', tr), L: ('RR', lr)}).mem(V, 'RR')
    ad = st([st([ur], 'recnd', '%s e. CC' % U), st([vr], 'recnd', '%s e. CC' % V), w.inst('efadd')], 'syl2anc',
            '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (U, V, U, V))
    lhs = st([st([xe], 'oveq1d', '( %s x. ( exp ` %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (XB, V, U, V)), ad], 'eqtr4d',
             '( %s x. ( exp ` %s ) ) = ( exp ` ( %s + %s ) )' % (XB, V, U, V))
    F = '( ( 5 / 2 ) x. ( 1 - T ) )'
    fr = st([litr(w, ante, '( 5 / 2 )'), st([st([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR')], 'remulcld', '%s e. RR' % F)
    rhs = st([dc, dne, st([fr], 'recnd', '%s e. CC' % F)], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (F, F, L))
    ex = lineq(w, ante, '( %s + %s )' % (U, V), '( %s x. %s )' % (F, L), products=True, leaves={'T': tr, L: lr})
    w.qed([lhs, st([st([ex], 'fveq2d', '( exp ` ( %s + %s ) ) = ( exp ` ( %s x. %s ) )' % (U, V, F, L)), rhs], 'eqtr4d',
                   '( exp ` ( %s + %s ) ) = ( D ^c %s )' % (U, V, F))], 'eqtrd', STATEMENTS['zdxexp'])
    return w


def zd2rpar():
    w = W('zd2rpar', "R = D ^c ( 1 / 100 ) >_ 2 once log D >_ 200 (Lean two_le_Rpar).")
    ante = '( D e. RR+ /\\ ; ; 2 0 0 <_ ( log ` D ) )'
    st = mkst(w, ante)
    drp = st([], 'simpl', 'D e. RR+'); l200 = st([], 'simpr', '; ; 2 0 0 <_ ( log ` D )')
    L = '( log ` D )'; lr = st([drp], 'relogcld', '%s e. RR' % L)
    H = '( 1 / ; ; 1 0 0 )'
    e = st([st([drp], 'rpcnd', 'D e. CC'), st([drp], 'rpne0d', 'D =/= 0'), st([litr(w, ante, H)], 'recnd', '%s e. CC' % H)], 'cxpefd',
           '%s = ( exp ` ( %s x. %s ) )' % (RP, H, L))
    a = '( %s x. %s )' % (H, L)
    ar = st([litr(w, ante, H), lr], 'remulcld', '%s e. RR' % a)
    a0 = linarith(w, ante, [l200], '0 <_ %s' % a, leaves={L: lr})
    ef = st([ar, a0, w.inst('bvefge1p')], 'syl2anc', '( 1 + %s ) <_ ( exp ` %s )' % (a, a))
    g = linarith(w, ante, [ef, l200], '2 <_ ( exp ` %s )' % a, leaves={L: lr, '( exp ` %s )' % a: st([ar], 'reefcld', '( exp ` %s ) e. RR' % a)})
    w.qed([g, e], 'breqtrrd', STATEMENTS['zd2rpar'])
    return w


def zdpow4():
    w = W('zdpow4', "A ^ 4 <_ e ^ ( ( 5 / 2 ) A ) for A >_ 0 (Lean pow_four_le_exp): A <_ e ^ ( 5 A / 8 ) from 1 + t + t ^ 2 / 2 <_ e ^ t.")
    ante = '( A e. RR /\\ 0 <_ A )'
    st = mkst(w, ante)
    ar = st([], 'simpl', 'A e. RR'); a0 = st([], 'simpr', '0 <_ A')
    t = '( ( 5 / 8 ) x. A )'
    tr = st([litr(w, ante, '( 5 / 8 )'), ar], 'remulcld', '%s e. RR' % t)
    t0 = linarith(w, ante, [a0], '0 <_ %s' % t, leaves={'A': ar})
    e2 = st([tr, t0, w.inst('efge1p2')], 'syl2anc', '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ ( exp ` %s )' % (t, t, t))
    sq = st([st([tr, litr(w, ante, '( 3 / 5 )')], 'resubcld', '( %s - ( 3 / 5 ) ) e. RR' % t)], 'sqge0d', '0 <_ ( ( %s - ( 3 / 5 ) ) ^ 2 )' % t)
    E = '( exp ` %s )' % t
    er = st([tr], 'reefcld', '%s e. RR' % E)
    le = linarith(w, ante, [e2, sq], 'A <_ %s' % E, leaves={'A': ar, E: er}, products=True)
    p4 = w.s([bind3(w, ante, ar, er, a1c(w, ante, '4nn0', '4 e. NN0'), 'A e. RR', '%s e. RR' % E, '4 e. NN0'), bind(w, ante, a0, le, '0 <_ A', 'A <_ %s' % E),
             w.inst('leexp1a')], 'syl2anc', '( %s -> ( A ^ 4 ) <_ ( %s ^ 4 ) )' % (ante, E))
    ee = st([st([tr], 'recnd', '%s e. CC' % t), a1c(w, ante, '4z', '4 e. ZZ'), w.inst('efexp')], 'syl2anc', '( exp ` ( 4 x. %s ) ) = ( %s ^ 4 )' % (t, E))
    eq = lineq(w, ante, '( 4 x. %s )' % t, '( ( 5 / 2 ) x. A )', leaves={'A': ar})
    e3 = st([st([eq], 'fveq2d', '( exp ` ( 4 x. %s ) ) = ( exp ` ( ( 5 / 2 ) x. A ) )' % t), ee], 'eqtr3d', '( %s ^ 4 ) = ( exp ` ( ( 5 / 2 ) x. A ) )' % E)
    w.qed([p4, e3], 'breqtrd', STATEMENTS['zdpow4'])
    return w


def scalefacts(w, ante):
    st = mkst(w, ante)
    nn = st([], 'simp1', 'N e. NN'); ht = st([], 'simp2', '( T e. RR /\\ 2 <_ T )'); hc = st([], 'simp3', '( C e. RR /\\ 1 <_ C )')
    tr = st([ht], 'simpld', 'T e. RR'); t2 = st([ht], 'simprd', '2 <_ T')
    cr = st([hc], 'simpld', 'C e. RR'); c1 = st([hc], 'simprd', '1 <_ C')
    t1 = linarith(w, ante, [t2], '1 <_ T', leaves={'T': tr})
    t0 = linarith(w, ante, [t2], '0 <_ T', leaves={'T': tr})
    tc = st([tr, t1, st([], '1red', '1 e. RR'), cr, c1], 'cxplead', '( T ^c 1 ) <_ ( T ^c C )')
    tc2 = st([st([st([tr], 'recnd', 'T e. CC')], 'cxp1d', '( T ^c 1 ) = T'), tc], 'eqbrtrrd', 'T <_ ( T ^c C )')
    tcr = st([tr, t0, cr], 'recxpcld', '( T ^c C ) e. RR')
    nr = st([nn], 'nnred', 'N e. RR'); n0 = sy(w, ante, nn, 'nnge1', '1 <_ N')
    return dict(nn=nn, tr=tr, t2=t2, cr=cr, tc=tc2, tcr=tcr, nr=nr, n1=n0, n0=linarith(w, ante, [n0], '0 <_ N', leaves={'N': nr}))


def zdscale():
    w = W('zdscale', "d ( t + 2 ) <_ 2 d t ^ c0 for t >_ 2, c0 >_ 1 (Lean scale_le_two_mul).")
    ante = '( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) )'
    st = mkst(w, ante)
    f = scalefacts(w, ante)
    m1 = st([st([f['tr'], a1c(w, ante, '2re', '2 e. RR')], 'readdcld', '( T + 2 ) e. RR'), st([f['tr'], f['tr']], 'readdcld', '( T + T ) e. RR'), f['nr'], f['n0'],
             linarith(w, ante, [f['t2']], '( T + 2 ) <_ ( T + T )', leaves={'T': f['tr']})], 'lemul2ad', '( N x. ( T + 2 ) ) <_ ( N x. ( T + T ) )')
    m2 = st([f['tr'], f['tcr'], f['nr'], f['n0'], f['tc']], 'lemul2ad', '( N x. T ) <_ ( N x. ( T ^c C ) )')
    linarith(w, ante, [m1, m2], '( N x. ( T + 2 ) ) <_ ( 2 x. %s )' % EE, leaves={'N': f['nr'], 'T': f['tr'], '( T ^c C )': f['tcr']}, products=True, name='qed')
    return w


def zdscale2():
    w = W('zdscale2', "2 <_ d t ^ c0 for d >_ 1, t >_ 2, c0 >_ 1 (Lean two_le_scale').")
    ante = '( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) )'
    st = mkst(w, ante)
    f = scalefacts(w, ante)
    tc0 = linarith(w, ante, [f['t2'], f['tc']], '0 <_ ( T ^c C )', leaves={'T': f['tr'], '( T ^c C )': f['tcr']})
    m = st([st([], '1red', '1 e. RR'), f['nr'], f['tcr'], tc0, f['n1']], 'lemul1ad', '( 1 x. ( T ^c C ) ) <_ ( N x. ( T ^c C ) )')
    linarith(w, ante, [m, f['t2'], f['tc']], '2 <_ %s' % EE, leaves={'T': f['tr'], '( T ^c C )': f['tcr'], EE: st([f['nr'], f['tcr']], 'remulcld', '%s e. RR' % EE)},
             name='qed')
    return w


def cbvp(w, body):
    """( n = p -> ( 1 - ( 1 / n ) ) = body )"""
    idn = w.s([], 'id', '( n = p -> n = p )')
    st, new = w.congr('( 1 - ( 1 / n ) )', {'n': 'p'}, 'n = p', {'n': idn})
    return st


if __name__ == '__main__':
    for f in sys.argv[1:]:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
