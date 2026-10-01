"""Sortie Z5a, section A: posLog and the Barban-Vehov weight (Detector.lean 114-136, 204-279, 1378-1394)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5alib import *
from cl import Closure, lift
import lin


def z5plbnd():
    w = W('z5plbnd', "Lean Real.posLog (written if ( 1 <_ x , log x , 0 )) is nonnegative and at least log x for x > 0 "
                     "(the two facts behind posLog_of_one_le, posLog_mul_le, Detector.lean).")
    ante = 'X e. RR+'
    P = PL('X'); LX = '( log ` X )'; phi = '1 <_ X'
    a = '( %s /\\ %s )' % (ante, phi); b = '( %s /\\ -. %s )' % (ante, phi)
    sa = mkst(w, a); sb = mkst(w, b)
    # 1 <_ X
    xra = sa([w.s([], 'simpl', '( %s -> X e. RR+ )' % a)], 'rpred', 'X e. RR')
    it = ift(w, a, phi, LX, '0')
    l0 = w.s([xra, w.s([], 'simpr', '( %s -> %s )' % (a, phi)), w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (a, LX))
    c1 = sa([l0, it], 'breqtrrd', '0 <_ %s' % P)
    lr = sa([w.s([], 'simpl', '( %s -> X e. RR+ )' % a)], 'relogcld', '%s e. RR' % LX)
    c2 = sa([sa([lr], 'leidd', '%s <_ %s' % (LX, LX)), it], 'breqtrrd', '%s <_ %s' % (LX, P))
    ta = sa([c1, c2], 'jca', '( 0 <_ %s /\\ %s <_ %s )' % (P, LX, P))
    # -. 1 <_ X
    xrp = w.s([], 'simpl', '( %s -> X e. RR+ )' % b)
    xrb = sb([xrp], 'rpred', 'X e. RR')
    itf = iff_(w, b, phi, LX, '0')
    lt = sb([w.s([], 'simpr', '( %s -> -. %s )' % (b, phi)), sb([xrb, sb([], '1red', '1 e. RR')], 'ltnled', '( X < 1 <-> -. 1 <_ X )')], 'mpbird', 'X < 1')
    le = sb([lt], 'ltled', 'X <_ 1')
    lb = sb([xrp, a1c(w, b, '1rp', '1 e. RR+'), w.inst('logleb')], 'syl2anc', '( X <_ 1 <-> %s <_ ( log ` 1 ) )' % LX)
    l1 = sb([le, lb], 'mpbid', '%s <_ ( log ` 1 )' % LX)
    l2 = sb([l1, a1c(w, b, 'log1', '( log ` 1 ) = 0')], 'breqtrd', '%s <_ 0' % LX)
    d1 = sb([sb([], '0red', '0 e. RR')], 'leidd', '0 <_ 0')
    fb = sb([sb([d1, itf], 'breqtrrd', '0 <_ %s' % P), sb([l2, itf], 'breqtrrd', '%s <_ %s' % (LX, P))], 'jca', '( 0 <_ %s /\\ %s <_ %s )' % (P, LX, P))
    cases(w, ante, phi, ta, fb, '( 0 <_ %s /\\ %s <_ %s )' % (P, LX, P), name='qed')
    return w


def z5pl0():
    w = W('z5pl0', "Lean posLog_of_le_one: log+ x = 0 for x <_ 1 (log+ x written if ( 1 <_ x , log x , 0 )).")
    ante = '( X e. RR /\\ X <_ 1 )'
    P = PL('X'); LX = '( log ` X )'; phi = '1 <_ X'
    a = '( %s /\\ %s )' % (ante, phi); b = '( %s /\\ -. %s )' % (ante, phi)
    sa = mkst(w, a)
    xr = sa([], 'simpll', 'X e. RR')
    x1 = sa([xr, sa([], '1red', '1 e. RR')], 'letri3d', '( X = 1 <-> ( X <_ 1 /\\ 1 <_ X ) )')
    eq = sa([sa([sa([], 'simplr', 'X <_ 1'), sa([], 'simpr', phi)], 'jca', '( X <_ 1 /\\ 1 <_ X )'), x1], 'mpbird', 'X = 1')
    lg = sa([sa([eq], 'fveq2d', '%s = ( log ` 1 )' % LX), a1c(w, a, 'log1', '( log ` 1 ) = 0')], 'eqtrd', '%s = 0' % LX)
    ta = sa([ift(w, a, phi, LX, '0'), lg], 'eqtrd', '%s = 0' % P)
    fb = iff_(w, b, phi, LX, '0')
    cases(w, ante, phi, ta, fb, '%s = 0' % P, name='qed')
    return w


def z5plmul():
    w = W('z5plmul', "Lean posLog_mul_le: log+ ( x c ) <_ log+ x + log c for 0 <_ x, 1 <_ c (log+ x written if ( 1 <_ x , log x , 0 )).")
    ante = '( ( X e. RR /\\ 0 <_ X ) /\\ ( C e. RR /\\ 1 <_ C ) )'
    st = mkst(w, ante)
    Y = '( X x. C )'
    PY = PL(Y); PX = PL('X'); LC = '( log ` C )'
    phi = '1 <_ %s' % Y
    xr = st([], 'simpll', 'X e. RR'); cr = st([], 'simprl', 'C e. RR'); c1 = st([], 'simprr', '1 <_ C')
    lc0 = st([cr, c1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % LC)
    crp = st([cr, lin.linarith(w, ante, [c1], '0 < C', leaves={'C': cr})], 'elrpd', 'C e. RR+')
    lcr = st([crp], 'relogcld', '%s e. RR' % LC)
    # 0 <_ PX and PX e. RR, by cases on 1 <_ X
    pa = '( %s /\\ 1 <_ X )' % ante; pb = '( %s /\\ -. 1 <_ X )' % ante
    spa = mkst(w, pa); spb = mkst(w, pb)
    xpa = spa([lift(w, xr, pa), lin.linarith(w, pa, [spa([], 'simpr', '1 <_ X')], '0 < X', leaves={'X': lift(w, xr, pa)})], 'elrpd', 'X e. RR+')
    p0a = spa([spa([lift(w, xr, pa), spa([], 'simpr', '1 <_ X'), w.inst('logge0')], 'syl2anc', '0 <_ ( log ` X )'), ift(w, pa, '1 <_ X', '( log ` X )', '0')],
              'breqtrrd', '0 <_ %s' % PX)
    p0b = spb([spb([spb([], '0red', '0 e. RR')], 'leidd', '0 <_ 0'), iff_(w, pb, '1 <_ X', '( log ` X )', '0')], 'breqtrrd', '0 <_ %s' % PX)
    px0 = cases(w, ante, '1 <_ X', p0a, p0b, '0 <_ %s' % PX)
    pxr = st([spa([xpa], 'relogcld', '( log ` X ) e. RR'), spb([], '0red', '0 e. RR')], 'ifclda', '%s e. RR' % PX)
    a = '( %s /\\ %s )' % (ante, phi); b = '( %s /\\ -. %s )' % (ante, phi)
    sa = mkst(w, a); sb = mkst(w, b)
    xra = lift(w, xr, a); cra = lift(w, cr, a)
    yr = sa([xra, cra], 'remulcld', '%s e. RR' % Y)
    ygt = lin.linarith(w, a, [sa([], 'simpr', phi)], '0 < %s' % Y, leaves={Y: yr})
    c0 = lin.linarith(w, a, [lift(w, c1, a)], '0 <_ C', leaves={'C': cra})
    xgt = sa([xra, cra, c0, ygt, w.inst('prodgt02')], 'syl22anc', '0 < X')
    xrp = sa([xra, xgt], 'elrpd', 'X e. RR+')
    lm = sa([xrp, lift(w, crp, a)], 'relogmuld', '( log ` %s ) = ( ( log ` X ) + %s )' % (Y, LC))
    pl = sa([ift(w, a, phi, '( log ` %s )' % Y, '0'), lm], 'eqtrd', '%s = ( ( log ` X ) + %s )' % (PY, LC))
    bnd = sa([xrp, w.inst('z5plbnd')], 'syl', '( 0 <_ %s /\\ ( log ` X ) <_ %s )' % (PX, PX))
    lxp = sa([bnd], 'simprd', '( log ` X ) <_ %s' % PX)
    lxr = sa([xrp], 'relogcld', '( log ` X ) e. RR')
    ta = sa([pl, sa([lxr, lift(w, pxr, a), lift(w, lcr, a), lxp], 'leadd1dd', '( ( log ` X ) + %s ) <_ ( %s + %s )' % (LC, PX, LC))], 'eqbrtrd',
            '%s <_ ( %s + %s )' % (PY, PX, LC))
    itf = iff_(w, b, phi, '( log ` %s )' % Y, '0')
    s0 = sb([lift(w, pxr, b), lift(w, lcr, b), lift(w, px0, b), lift(w, lc0, b)], 'addge0d', '0 <_ ( %s + %s )' % (PX, LC))
    zle = sb([itf, s0], 'eqbrtrd', '%s <_ ( %s + %s )' % (PY, PX, LC))
    cases(w, ante, phi, ta, zle, '%s <_ ( %s + %s )' % (PY, PX, LC), name='qed')
    return w


def z5lamval():
    w = W('z5lamval', "The value of the Barban-Vehov weight at K: ( ( A bvLam B ) ` K ) = mmu ( K ) ( log+ ( B / K ) - log+ ( A / K ) ) / log ( B / A ) "
                      "(Lean bvLam, Detector.lean 198).")
    ante = '( ( A e. V /\\ B e. W ) /\\ K e. NN )'
    st = mkst(w, ante)
    MP = '( z e. NN |-> %s )' % BVL('z')
    lv = st([st([], 'simpll', 'A e. V'), st([], 'simplr', 'B e. W'), w.inst('bvlamval')], 'syl2anc', '( A bvLam B ) = %s' % MP)
    val, _v = mpv(w, ante, 'z', 'NN', BVL('z'), 'K', st([], 'simpr', 'K e. NN'))
    w.qed([st([lv], 'fveq1d', '( ( A bvLam B ) ` K ) = ( %s ` K )' % MP), val], 'eqtrd', STATEMENTS['z5lamval'])
    return w


def habfacts(w, ante, hab, strict1):
    """from hab: ( ante -> HAB1 ) (strict1 False) or HAB0: A, B reals, positivity, A < B, B / A, log ( B / A )"""
    st = mkst(w, ante)
    HA = '( A e. RR /\\ 1 <_ A )' if not strict1 else '( A e. RR /\\ 0 < A )'
    ha = st([hab], 'simpld', HA); hb = st([hab], 'simprd', '( B e. RR /\\ A < B )')
    ar = st([ha], 'simpld', 'A e. RR'); a1 = st([ha], 'simprd', HA.split(' /\\ ')[1][:-2])
    br = st([hb], 'simpld', 'B e. RR'); ab = st([hb], 'simprd', 'A < B')
    agt = lin.linarith(w, ante, [a1], '0 < A', leaves={'A': ar})
    arp = st([ar, agt], 'elrpd', 'A e. RR+')
    brp = st([br, lin.linarith(w, ante, [a1, ab], '0 < B', leaves={'A': ar, 'B': br})], 'elrpd', 'B e. RR+')
    qrp = st([brp, arp], 'rpdivcld', '( B / A ) e. RR+')
    q1 = st([st([], '1red', '1 e. RR'), br, arp], 'ltmuldivd', '( ( 1 x. A ) < B <-> 1 < ( B / A ) )')
    g1 = st([st([st([st([ar], 'recnd', 'A e. CC')], 'mullidd', '( 1 x. A ) = A'), ab], 'eqbrtrd', '( 1 x. A ) < B'), q1], 'mpbid', '1 < ( B / A )')
    L = '( log ` ( B / A ) )'
    lrp = sy2(w, ante, st([qrp], 'rpred', '( B / A ) e. RR'), g1, 'rplogcl', '%s e. RR+' % L)
    return dict(ar=ar, a1=a1, br=br, ab=ab, arp=arp, brp=brp, qrp=qrp, g1=g1, lrp=lrp, lr=st([lrp], 'rpred', '%s e. RR' % L),
                lc=st([lrp], 'rpcnd', '%s e. CC' % L), lne=st([lrp], 'rpne0d', '%s =/= 0' % L), ac=st([ar], 'recnd', 'A e. CC'),
                bc=st([br], 'recnd', 'B e. CC'), ane=st([arp], 'rpne0d', 'A =/= 0'))


def lamv(w, ante, f, knn):
    """( ante -> ( ( A bvLam B ) ` K ) = BVL(K) ) and the closures of K"""
    st = mkst(w, ante)
    ev = st([f['arp'], f['brp'], knn, w.inst('z5lamval')], 'syl21anc', '( ( A bvLam B ) ` K ) = %s' % BVL('K'))
    krp = st([knn], 'nnrpd', 'K e. RR+')
    return ev, krp


def z5lammu():
    w = W('z5lammu', "Lean bvLam_eq_moebius: the Barban-Vehov weight is mmu ( K ) for K <_ z1 (1 <_ z1 < z2).")
    ante = '( %s /\\ ( K e. NN /\\ K <_ A ) )' % HAB1
    st = mkst(w, ante)
    f = habfacts(w, ante, st([], 'simpl', HAB1), False)
    knn = st([], 'simprl', 'K e. NN'); ka = st([], 'simprr', 'K <_ A')
    ev, krp = lamv(w, ante, f, knn)
    kr = st([krp], 'rpred', 'K e. RR')
    kb = lin.linarith(w, ante, [ka, f['ab']], 'K <_ B', leaves={'K': kr, 'A': f['ar'], 'B': f['br']})
    pa = onele(w, ante, f['ar'], krp, ka, 'A', 'K'); pb = onele(w, ante, f['br'], krp, kb, 'B', 'K')
    LA = '( log ` ( A / K ) )'; LB = '( log ` ( B / K ) )'; L = '( log ` ( B / A ) )'
    ia = iftd(w, ante, pa, '1 <_ ( A / K )', LA, '0'); ib = iftd(w, ante, pb, '1 <_ ( B / K )', LB, '0')
    d1 = st([ib, ia], 'oveq12d', '( %s - %s ) = ( %s - %s )' % (PL('( B / K )'), PL('( A / K )'), LB, LA))
    lb = st([f['brp'], krp], 'relogdivd', '%s = ( ( log ` B ) - ( log ` K ) )' % LB)
    la = st([f['arp'], krp], 'relogdivd', '%s = ( ( log ` A ) - ( log ` K ) )' % LA)
    d2 = st([lb, la], 'oveq12d', '( %s - %s ) = ( ( ( log ` B ) - ( log ` K ) ) - ( ( log ` A ) - ( log ` K ) ) )' % (LB, LA))
    lv = {'( log ` A )': st([f['arp']], 'relogcld', '( log ` A ) e. RR'), '( log ` B )': st([f['brp']], 'relogcld', '( log ` B ) e. RR'),
          '( log ` K )': st([krp], 'relogcld', '( log ` K ) e. RR')}
    d3 = lin.lineq(w, ante, '( ( ( log ` B ) - ( log ` K ) ) - ( ( log ` A ) - ( log ` K ) ) )', '( ( log ` B ) - ( log ` A ) )', leaves=lv)
    d4 = st([st([f['brp'], f['arp']], 'relogdivd', '%s = ( ( log ` B ) - ( log ` A ) )' % L)], 'eqcomd', '( ( log ` B ) - ( log ` A ) ) = %s' % L)
    D = eqtr(w, ante, [d1, d2, d3, d4], None)
    MU = '( mmu ` K )'
    muc = st([sy(w, ante, knn, 'mucl', '%s e. ZZ' % MU)], 'zcnd', '%s e. CC' % MU)
    e2 = st([st([D], 'oveq2d', '( %s x. ( %s - %s ) ) = ( %s x. %s )' % (MU, PL('( B / K )'), PL('( A / K )'), MU, L))], 'oveq1d',
            '%s = ( ( %s x. %s ) / %s )' % (BVL('K'), MU, L, L))
    e3 = st([muc, f['lc'], f['lne']], 'divcan4d', '( ( %s x. %s ) / %s ) = %s' % (MU, L, L, MU))
    fin = eqtr(w, ante, [ev, e2], None)
    w.qed([fin, e3], 'eqtrd', STATEMENTS['z5lammu'])
    return w


def z5lam0():
    w = W('z5lam0', "Lean bvLam_eq_zero: the Barban-Vehov weight vanishes for K >_ z2 (0 < z1 < z2).")
    ante = '( %s /\\ ( K e. NN /\\ B <_ K ) )' % HAB0
    st = mkst(w, ante)
    f = habfacts(w, ante, st([], 'simpl', HAB0), True)
    knn = st([], 'simprl', 'K e. NN'); bk = st([], 'simprr', 'B <_ K')
    ev, krp = lamv(w, ante, f, knn)
    kr = st([krp], 'rpred', 'K e. RR')
    ak = lin.linarith(w, ante, [bk, f['ab']], 'A <_ K', leaves={'K': kr, 'A': f['ar'], 'B': f['br']})
    pa = lepone(w, ante, f['ar'], krp, ak, 'A', 'K'); pb = lepone(w, ante, f['br'], krp, bk, 'B', 'K')
    ia = st([st([st([f['arp'], krp], 'rpdivcld', '( A / K ) e. RR+')], 'rpred', '( A / K ) e. RR'), pa, w.inst('z5pl0')], 'syl2anc', '%s = 0' % PL('( A / K )'))
    ib = st([st([st([f['brp'], krp], 'rpdivcld', '( B / K ) e. RR+')], 'rpred', '( B / K ) e. RR'), pb, w.inst('z5pl0')], 'syl2anc', '%s = 0' % PL('( B / K )'))
    L = '( log ` ( B / A ) )'; MU = '( mmu ` K )'
    d1 = st([ib, ia], 'oveq12d', '( %s - %s ) = ( 0 - 0 )' % (PL('( B / K )'), PL('( A / K )')))
    d2 = st([d1, a1c(w, ante, '0m0e0', '( 0 - 0 ) = 0')], 'eqtrd', '( %s - %s ) = 0' % (PL('( B / K )'), PL('( A / K )')))
    muc = st([sy(w, ante, knn, 'mucl', '%s e. ZZ' % MU)], 'zcnd', '%s e. CC' % MU)
    m0 = st([st([d2], 'oveq2d', '( %s x. ( %s - %s ) ) = ( %s x. 0 )' % (MU, PL('( B / K )'), PL('( A / K )'), MU)), st([muc], 'mul01d', '( %s x. 0 ) = 0' % MU)],
            'eqtrd', '( %s x. ( %s - %s ) ) = 0' % (MU, PL('( B / K )'), PL('( A / K )')))
    e2 = st([m0], 'oveq1d', '%s = ( 0 / %s )' % (BVL('K'), L))
    e3 = st([f['lc'], f['lne']], 'div0d', '( 0 / %s ) = 0' % L)
    w.qed([eqtr(w, ante, [ev, e2], None), e3], 'eqtrd', STATEMENTS['z5lam0'])
    return w


def z5lamabs():
    w = W('z5lamabs', "Lean abs_bvLam_le_one: the Barban-Vehov weight has absolute value at most 1 (0 < z1 < z2), from "
                      "log+ ( z1 / K ) <_ log+ ( z2 / K ) <_ log+ ( z1 / K ) + log ( z2 / z1 ) (Lean posLog_mul_le) and | mmu | <_ 1.")
    ante = '( %s /\\ K e. NN )' % HAB0
    st = mkst(w, ante)
    f = habfacts(w, ante, st([], 'simpl', HAB0), True)
    knn = st([], 'simpr', 'K e. NN')
    ev, krp = lamv(w, ante, f, knn)
    L = '( log ` ( B / A ) )'; MU = '( mmu ` K )'
    PA = PL('( A / K )'); PB = PL('( B / K )')
    akrp = st([f['arp'], krp], 'rpdivcld', '( A / K ) e. RR+'); bkrp = st([f['brp'], krp], 'rpdivcld', '( B / K ) e. RR+')
    akr = st([akrp], 'rpred', '( A / K ) e. RR'); bkr = st([bkrp], 'rpred', '( B / K ) e. RR')
    ba = sy(w, ante, akrp, 'z5plbnd', '( 0 <_ %s /\\ ( log ` ( A / K ) ) <_ %s )' % (PA, PA))
    bb = sy(w, ante, bkrp, 'z5plbnd', '( 0 <_ %s /\\ ( log ` ( B / K ) ) <_ %s )' % (PB, PB))
    pa0 = st([ba], 'simpld', '0 <_ %s' % PA); pb0 = st([bb], 'simpld', '0 <_ %s' % PB)
    lar = st([akrp], 'relogcld', '( log ` ( A / K ) ) e. RR'); lbr = st([bkrp], 'relogcld', '( log ` ( B / K ) ) e. RR')
    par = st([lar, st([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % PA); pbr = st([lbr, st([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % PB)
    # upper: PB <_ PA + L, by z5plmul at X = A / K, C = B / A
    qr = st([f['qrp']], 'rpred', '( B / A ) e. RR')
    up0 = st([st([akr, st([akrp], 'rpge0d', '0 <_ ( A / K )')], 'jca', '( ( A / K ) e. RR /\\ 0 <_ ( A / K ) )'),
              st([qr, st([f['g1']], 'ltled', '1 <_ ( B / A )')], 'jca', '( ( B / A ) e. RR /\\ 1 <_ ( B / A ) )'), w.inst('z5plmul')], 'syl2anc',
             '%s <_ ( %s + %s )' % (PL('( ( A / K ) x. ( B / A ) )'), PA, L))
    kc = st([krp], 'rpcnd', 'K e. CC'); kne = st([krp], 'rpne0d', 'K =/= 0')
    dm = st([f['bc'], f['ac'], kc, f['ane'], kne], 'dmdcand', '( ( A / K ) x. ( B / A ) ) = ( B / K )')
    rw, _n = w.rewrite(PL('( ( A / K ) x. ( B / A ) )'), {'( ( A / K ) x. ( B / A ) )': ('( B / K )', dm)}, ante)
    up = st([rw, up0], 'eqbrtrrd', '%s <_ ( %s + %s )' % (PB, PA, L))
    # lower: PA <_ PB, by cases on 1 <_ ( A / K )
    phi = '1 <_ ( A / K )'
    a = '( %s /\\ %s )' % (ante, phi); b = '( %s /\\ -. %s )' % (ante, phi)
    sa = mkst(w, a); sb = mkst(w, b)
    akle = sa([lift(w, f['ar'], a), lift(w, f['br'], a), lift(w, krp, a), sa([lift(w, f['ab'], a)], 'ltled', 'A <_ B')], 'lediv1dd', '( A / K ) <_ ( B / K )')
    p1b = lin.linarith(w, a, [sa([], 'simpr', phi), akle], '1 <_ ( B / K )', leaves={'( A / K )': lift(w, akr, a), '( B / K )': lift(w, bkr, a)})
    ll = sa([akle, sa([lift(w, akrp, a), lift(w, bkrp, a)], 'logled', '( ( A / K ) <_ ( B / K ) <-> ( log ` ( A / K ) ) <_ ( log ` ( B / K ) ) )')], 'mpbid',
            '( log ` ( A / K ) ) <_ ( log ` ( B / K ) )')
    lo_a = sa([sa([ift(w, a, phi, '( log ` ( A / K ) )', '0'), ll], 'eqbrtrd', '%s <_ ( log ` ( B / K ) )' % PA),
               iftd(w, a, p1b, '1 <_ ( B / K )', '( log ` ( B / K ) )', '0')], 'breqtrrd', '%s <_ %s' % (PA, PB))
    lo_b = sb([iff_(w, b, phi, '( log ` ( A / K ) )', '0'), lift(w, pb0, b)], 'eqbrtrd', '%s <_ %s' % (PA, PB))
    lo = cases(w, ante, phi, lo_a, lo_b, '%s <_ %s' % (PA, PB))
    DD = '( %s - %s )' % (PB, PA)
    ddr = st([pbr, par], 'resubcld', '%s e. RR' % DD)
    lv = {PA: par, PB: pbr, L: f['lr']}
    d0 = lin.linarith(w, ante, [lo], '0 <_ %s' % DD, leaves=lv)
    dl = lin.linarith(w, ante, [up], '%s <_ %s' % (DD, L), leaves=lv)
    # | value | = ( | mu | D ) / L
    muz = sy(w, ante, knn, 'mucl', '%s e. ZZ' % MU); muc = st([muz], 'zcnd', '%s e. CC' % MU)
    ddc = st([ddr], 'recnd', '%s e. CC' % DD)
    AM = '( abs ` %s )' % MU
    a1 = st([st([muc, ddc], 'mulcld', '( %s x. %s ) e. CC' % (MU, DD)), f['lc'], f['lne']], 'absdivd',
            '( abs ` %s ) = ( ( abs ` ( %s x. %s ) ) / ( abs ` %s ) )' % (BVL('K'), MU, DD, L))
    a2 = st([muc, ddc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (MU, DD, AM, DD))
    a3 = st([ddr, d0], 'absidd', '( abs ` %s ) = %s' % (DD, DD))
    a4 = st([a2, st([a3], 'oveq2d', '( %s x. ( abs ` %s ) ) = ( %s x. %s )' % (AM, DD, AM, DD))], 'eqtrd', '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (MU, DD, AM, DD))
    a5 = st([f['lr'], st([f['lrp']], 'rpge0d', '0 <_ %s' % L)], 'absidd', '( abs ` %s ) = %s' % (L, L))
    a6 = st([a4, a5], 'oveq12d', '( ( abs ` ( %s x. %s ) ) / ( abs ` %s ) ) = ( ( %s x. %s ) / %s )' % (MU, DD, L, AM, DD, L))
    av = eqtr(w, ante, [st([ev], 'fveq2d', '( abs ` ( ( A bvLam B ) ` K ) ) = ( abs ` %s )' % BVL('K')), a1, a6], None)
    amr = st([muc], 'abscld', '%s e. RR' % AM)
    am1 = sy(w, ante, knn, 'mule1', '%s <_ 1' % AM)
    am0 = st([muc], 'absge0d', '0 <_ %s' % AM)
    X = '( %s x. %s )' % (AM, DD)
    xr = st([amr, ddr], 'remulcld', '%s e. RR' % X)
    lv2 = {AM: amr, PA: par, PB: pbr, L: f['lr']}
    core = lin.nlinarith(w, ante, [am1, am0, d0, dl], '%s <_ ( %s x. 1 )' % (X, L), leaves=lv2)
    le = st([core, st([xr, st([], '1red', '1 e. RR'), f['lrp']], 'ledivmuld', '( ( %s / %s ) <_ 1 <-> %s <_ ( %s x. 1 ) )' % (X, L, X, L))], 'mpbird',
            '( %s / %s ) <_ 1' % (X, L))
    w.qed([av, le], 'eqbrtrd', STATEMENTS['z5lamabs'])
    return w


SDV = DV('N')


def dvmem(w, a, S=None):
    """under a = ( ... /\\ d e. { x e. NN | x || N } ): d e. NN, d || N"""
    S = S or SDV
    elr = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || N ) )' % S)
    both = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (a, S)), elr], 'sylib', '( %s -> ( d e. NN /\\ d || N ) )' % a)
    return w.s([both], 'simpld', '( %s -> d e. NN )' % a), w.s([both], 'simprd', '( %s -> d || N )' % a)


def z5bvamu():
    w = W('z5bvamu', "Lean bvA_one and bvA_eq_zero in one: for N <_ z1 every divisor d of N has weight mmu ( d ) (bvLam_eq_moebius), "
                     "so ( ( z1 bvA z2 ) ` N ) = sum_ d | N mmu ( d ), which is 1 at N = 1 and 0 beyond (musum).")
    ante = '( %s /\\ ( N e. NN /\\ N <_ A ) )' % HAB1
    st = mkst(w, ante)
    hab = st([], 'simpl', HAB1)
    f = habfacts(w, ante, hab, False)
    nn = st([], 'simprl', 'N e. NN'); na = st([], 'simprr', 'N <_ A')
    SL = 'sum_ d e. %s ( ( A bvLam B ) ` d )' % SDV
    ev = st([f['arp'], f['brp'], nn, w.inst('bvaval')], 'syl21anc', '( ( A bvA B ) ` N ) = %s' % SL)
    a = '( %s /\\ d e. %s )' % (ante, SDV)
    sa = mkst(w, a)
    dnn, ddv = dvmem(w, a)
    dle = sa([sa([dnn], 'nnzd', 'd e. ZZ'), lift(w, nn, a), w.inst('dvdsle')], 'syl2anc', '( d || N -> d <_ N )')
    dn = sa([ddv, dle], 'mpd', 'd <_ N')
    da = lin.linarith(w, a, [dn, lift(w, na, a)], 'd <_ A', leaves={'d': sa([dnn], 'nnred', 'd e. RR'), 'N': lift(w, st([nn], 'nnred', 'N e. RR'), a),
                                                                     'A': lift(w, f['ar'], a)})
    lm = sa([lift(w, hab, a), dnn, da, w.inst('z5lammu')], 'syl12anc', '( ( A bvLam B ) ` d ) = ( mmu ` d )')
    s1 = st([lm], 'sumeq2dv', '%s = sum_ d e. %s ( mmu ` d )' % (SL, SDV))
    MS = '{ n e. NN | n || N }'
    cr = w.s([w.s([], 'breq1', '( x = n -> ( x || N <-> n || N ) )')], 'cbvrabv', '%s = %s' % (SDV, MS))
    s2 = st([a1(w, ante, cr, '%s = %s' % (SDV, MS))], 'sumeq1d', 'sum_ d e. %s ( mmu ` d ) = sum_ d e. %s ( mmu ` d )' % (SDV, MS))
    cb = w.s([w.s([], 'fveq2', '( d = k -> ( mmu ` d ) = ( mmu ` k ) )')], 'cbvsumv', 'sum_ d e. %s ( mmu ` d ) = sum_ k e. %s ( mmu ` k )' % (MS, MS))
    s3 = a1(w, ante, cb, 'sum_ d e. %s ( mmu ` d ) = sum_ k e. %s ( mmu ` k )' % (MS, MS))
    s4 = sy(w, ante, nn, 'musum', 'sum_ k e. %s ( mmu ` k ) = if ( N = 1 , 1 , 0 )' % MS)
    last = eqtr(w, ante, [ev, s1, s2, s3], None)
    w.qed([last, s4], 'eqtrd', STATEMENTS['z5bvamu'])
    return w


def z5bva1():
    w = W('z5bva1', "Lean bvA_one: ( ( z1 bvA z2 ) ` 1 ) = 1 for 1 <_ z1 < z2.")
    ante = HAB1
    st = mkst(w, ante)
    a1_ = st([st([], 'simpl', '( A e. RR /\\ 1 <_ A )')], 'simprd', '1 <_ A')
    one = a1c(w, ante, '1nn', '1 e. NN')
    m = st([st([], 'id', HAB1), one, a1_, w.inst('z5bvamu')], 'syl12anc', '( ( A bvA B ) ` 1 ) = if ( 1 = 1 , 1 , 0 )')
    it = st([a1c(w, ante, 'eqid', '1 = 1')], 'iftrued', 'if ( 1 = 1 , 1 , 0 ) = 1')
    w.qed([m, it], 'eqtrd', STATEMENTS['z5bva1'])
    return w


def z5bva0():
    w = W('z5bva0', "Lean bvA_eq_zero, the Barban-Vehov vanishing property: ( ( z1 bvA z2 ) ` N ) = 0 for 1 < N <_ z1.")
    ante = '( %s /\\ ( N e. NN /\\ ( 1 < N /\\ N <_ A ) ) )' % HAB1
    st = mkst(w, ante)
    nn = st([], 'simprl', 'N e. NN'); n1 = st([], 'simprr', '( 1 < N /\\ N <_ A )')
    lt = st([n1], 'simpld', '1 < N'); na = st([n1], 'simprd', 'N <_ A')
    m = st([st([], 'simpl', HAB1), nn, na, w.inst('z5bvamu')], 'syl12anc', '( ( A bvA B ) ` N ) = if ( N = 1 , 1 , 0 )')
    ne = st([st([st([lt], 'gtned', 'N =/= 1')], 'neneqd', '-. N = 1')], 'iffalsed', 'if ( N = 1 , 1 , 0 ) = 0')
    w.qed([m, ne], 'eqtrd', STATEMENTS['z5bva0'])
    return w


def z5bvaabs():
    w = W('z5bvaabs', "Lean abs_bvA_le: | ( ( z1 bvA z2 ) ` N ) | <_ N (each weight has absolute value at most 1, and N has at most N divisors).")
    ante = '( %s /\\ N e. NN )' % HAB0
    st = mkst(w, ante)
    hab = st([], 'simpl', HAB0)
    f = habfacts(w, ante, hab, True)
    nn = st([], 'simpr', 'N e. NN')
    SL = 'sum_ d e. %s ( ( A bvLam B ) ` d )' % SDV
    ev = st([f['arp'], f['brp'], nn, w.inst('bvaval')], 'syl21anc', '( ( A bvA B ) ` N ) = %s' % SL)
    fin = sy(w, ante, nn, 'dvdsfi', '%s e. Fin' % SDV)
    a = '( %s /\\ d e. %s )' % (ante, SDV)
    sa = mkst(w, a)
    dnn, _ddv = dvmem(w, a)
    H3 = '( A e. RR+ /\\ B e. RR+ /\\ A < B )'
    h3 = st([f['arp'], f['brp'], f['ab']], '3jca', H3)
    lr = sa([lift(w, h3, a), dnn, w.inst('bvlamre')], 'syl2anc', '( ( A bvLam B ) ` d ) e. RR')
    LD = '( ( A bvLam B ) ` d )'
    lab = sa([lift(w, hab, a), dnn, w.inst('z5lamabs')], 'syl2anc', '( abs ` %s ) <_ 1' % LD)
    s1 = st([fin, sa([lr], 'recnd', '%s e. CC' % LD)], 'fsumabs', '( abs ` %s ) <_ sum_ d e. %s ( abs ` %s )' % (SL, SDV, LD))
    alr = sa([sa([lr], 'recnd', '%s e. CC' % LD)], 'abscld', '( abs ` %s ) e. RR' % LD)
    s2 = st([fin, alr, sa([], '1red', '1 e. RR'), lab], 'fsumle', 'sum_ d e. %s ( abs ` %s ) <_ sum_ d e. %s 1' % (SDV, LD, SDV))
    HS = '( # ` %s )' % SDV
    s3 = sy2(w, ante, fin, st([], '1cnd', '1 e. CC'), 'fsumconst', 'sum_ d e. %s 1 = ( %s x. 1 )' % (SDV, HS))
    hr = st([sy(w, ante, fin, 'hashcl', '%s e. NN0' % HS)], 'nn0red', '%s e. RR' % HS)
    s4 = st([st([hr], 'recnd', '%s e. CC' % HS)], 'mulridd', '( %s x. 1 ) = %s' % (HS, HS))
    PS = '{ p e. NN | p || N }'
    cr = w.s([w.s([], 'breq1', '( x = p -> ( x || N <-> p || N ) )')], 'cbvrabv', '%s = %s' % (SDV, PS))
    ss = st([a1(w, ante, cr, '%s = %s' % (SDV, PS)), sy(w, ante, nn, 'dvdsssfz1', '%s C_ ( 1 ... N )' % PS)], 'eqsstrd', '%s C_ ( 1 ... N )' % SDV)
    hs = sy2(w, ante, st([], 'fzfid', '( 1 ... N ) e. Fin'), ss, 'hashssle', '%s <_ ( # ` ( 1 ... N ) )' % HS)
    hf = sy(w, ante, st([nn], 'nnnn0d', 'N e. NN0'), 'hashfz1', '( # ` ( 1 ... N ) ) = N')
    s5 = st([hs, hf], 'breqtrd', '%s <_ N' % HS)
    A1 = '( abs ` %s )' % SL
    S2 = 'sum_ d e. %s ( abs ` %s )' % (SDV, LD); S3 = 'sum_ d e. %s 1' % SDV
    s2r = st([fin, alr], 'fsumrecl', '%s e. RR' % S2)
    s3r = st([fin, sa([], '1red', '1 e. RR')], 'fsumrecl', '%s e. RR' % S3)
    a1r = st([st([fin, sa([lr], 'recnd', '%s e. CC' % LD)], 'fsumcl', '%s e. CC' % SL)], 'abscld', '%s e. RR' % A1)
    s34 = st([s3, s4], 'eqtrd', '%s = %s' % (S3, HS))
    c1 = st([a1r, s2r, s3r, s1, s2], 'letrd', '%s <_ %s' % (A1, S3))
    c2 = st([c1, s34], 'breqtrd', '%s <_ %s' % (A1, HS))
    c3 = st([a1r, hr, st([nn], 'nnred', 'N e. RR'), c2, s5], 'letrd', '%s <_ N' % A1)
    e = st([ev], 'fveq2d', '( abs ` ( ( A bvA B ) ` N ) ) = %s' % A1)
    w.qed([e, c3], 'eqbrtrd', STATEMENTS['z5bvaabs'])
    return w


if __name__ == '__main__':
    import z5alib
    for f in sys.argv[1:]:
        z5alib.run(globals()[f]())
