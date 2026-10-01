"""Sortie ZD1: sections 2-5 continued: Corollary 8.4 / Theorem 8.3 arithmetic, the thresholds, Theorem H."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import Closure, lift
import lin
lin.MAXDEG = 5


def zdlogcxp():
    w = W('zdlogcxp', "log X <_ X ^c E / E for X >_ 1, E > 0 (Mathlib Real.log_le_rpow_div, at X >_ 1): E log X = log X ^c E <_ X ^c E - 1.")
    ante = '( ( X e. RR /\\ 1 <_ X ) /\\ E e. RR+ )'
    st = mkst(w, ante)
    xr = st([st([], 'simpl', '( X e. RR /\\ 1 <_ X )')], 'simpld', 'X e. RR'); x1 = st([st([], 'simpl', '( X e. RR /\\ 1 <_ X )')], 'simprd', '1 <_ X')
    erp = st([], 'simpr', 'E e. RR+'); er = st([erp], 'rpred', 'E e. RR')
    xrp = st([xr, linarith(w, ante, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    Y = '( X ^c E )'
    yrp = st([xrp, er], 'rpcxpcld', '%s e. RR+' % Y); yr = st([yrp], 'rpred', '%s e. RR' % Y)
    c0 = st([st([xr], 'recnd', 'X e. CC')], 'cxp0d', '( X ^c 0 ) = 1')
    le = st([xr, x1, st([], '0red', '0 e. RR'), er, st([erp], 'rpge0d', '0 <_ E')], 'cxplead', '( X ^c 0 ) <_ %s' % Y)
    y1 = st([c0, le], 'eqbrtrrd', '1 <_ %s' % Y)
    ex = st([yr, y1, w.inst('extrwlogle')], 'syl2anc', '( log ` %s ) <_ ( %s - 1 )' % (Y, Y))
    lc = st([xrp, er], 'logcxpd', '( log ` %s ) = ( E x. ( log ` X ) )' % Y)
    L = '( log ` X )'; lr = st([xrp], 'relogcld', '%s e. RR' % L)
    g = linarith(w, ante, [st([lc, ex], 'eqbrtrrd', '( E x. %s ) <_ ( %s - 1 )' % (L, Y))], '( %s x. E ) <_ %s' % (L, Y),
                 leaves={L: lr, 'E': er, Y: yr}, products=True)
    bi = st([lr, yr, erp], 'lemuldivd', '( ( %s x. E ) <_ %s <-> %s <_ ( %s / E ) )' % (L, Y, L, Y))
    w.qed([g, bi], 'mpbid', STATEMENTS['zdlogcxp'])
    return w


def zdpar():
    w = W('zdpar', "The absorb-and-divide step of Theorem 8.3 (Lean card_paritySystem_le, hkey .. h5): from ( J V ) ^ 2 <_ J ( A + J B ) and "
                   "B <_ V ^ 2 / 2, J >_ 0, V > 0, A >_ 0: J <_ 2 A / V ^ 2.")
    ante = STATEMENTS['zdpar'].split(' -> J <_')[0][2:]
    st = mkst(w, ante)
    L1 = '( ( ( J e. RR /\\ 0 <_ J ) /\\ ( V e. RR /\\ 0 < V ) ) /\\ ( ( A e. RR /\\ 0 <_ A ) /\\ B e. RR ) )'
    L2 = '( ( ( J x. V ) ^ 2 ) <_ ( J x. ( A + ( J x. B ) ) ) /\\ B <_ ( ( V ^ 2 ) / 2 ) )'
    h1 = st([], 'simpl', L1); h2 = st([], 'simpr', L2)
    jj = st([st([h1], 'simpld', '( ( J e. RR /\\ 0 <_ J ) /\\ ( V e. RR /\\ 0 < V ) )')], 'simpld', '( J e. RR /\\ 0 <_ J )')
    vv = st([st([h1], 'simpld', '( ( J e. RR /\\ 0 <_ J ) /\\ ( V e. RR /\\ 0 < V ) )')], 'simprd', '( V e. RR /\\ 0 < V )')
    ab = st([h1], 'simprd', '( ( A e. RR /\\ 0 <_ A ) /\\ B e. RR )')
    jr = st([jj], 'simpld', 'J e. RR'); j0 = st([jj], 'simprd', '0 <_ J')
    vr = st([vv], 'simpld', 'V e. RR'); v0 = st([vv], 'simprd', '0 < V')
    ar = st([st([ab], 'simpld', '( A e. RR /\\ 0 <_ A )')], 'simpld', 'A e. RR'); a0 = st([st([ab], 'simpld', '( A e. RR /\\ 0 <_ A )')], 'simprd', '0 <_ A')
    br = st([ab], 'simprd', 'B e. RR')
    k1 = st([h2], 'simpld', '( ( J x. V ) ^ 2 ) <_ ( J x. ( A + ( J x. B ) ) )'); k2 = st([h2], 'simprd', 'B <_ ( ( V ^ 2 ) / 2 )')
    V2 = '( V ^ 2 )'
    v2r = st([vr], 'resqcld', '%s e. RR' % V2)
    v2rp = st([v2r, linarith(w, ante, [v0], '0 < %s' % V2, leaves={'V': vr}, products=True)], 'elrpd', '%s e. RR+' % V2)
    # J J B <_ J J ( V ^ 2 / 2 )
    jj0 = st([jr, jr, j0, j0], 'mulge0d', '0 <_ ( J x. J )')
    m = st([br, st([v2r, a1c(w, ante, '2re', '2 e. RR'), a1c(w, ante, '2ne0', '2 =/= 0')], 'redivcld', '( %s / 2 ) e. RR' % V2), st([jr, jr], 'remulcld', '( J x. J ) e. RR'), jj0, k2],
           'lemul2ad', '( ( J x. J ) x. B ) <_ ( ( J x. J ) x. ( %s / 2 ) )' % V2)
    # J ( J V ^ 2 / 2 ) <_ J A
    g1 = linarith(w, ante, [k1, m], '( J x. ( ( J x. %s ) / 2 ) ) <_ ( J x. A )' % V2, leaves={'J': jr, 'V': vr, 'A': ar, 'B': br}, products=True)
    # case split 0 = J \/ 0 < J
    G = '( ( 2 x. A ) / %s )' % V2
    bi = st([jr, st([a1c(w, ante, '2re', '2 e. RR'), ar], 'remulcld', '( 2 x. A ) e. RR'), v2rp], 'lemuldivd', '( ( J x. %s ) <_ ( 2 x. A ) <-> J <_ %s )' % (V2, G))
    a = '( %s /\\ 0 < J )' % ante
    sa = mkst(w, a)
    jrp = sa([lift(w, jr, a), w.s([], 'simpr', '( %s -> 0 < J )' % a)], 'elrpd', 'J e. RR+')
    c = sa([sa([sa([lift(w, jr, a), lift(w, v2r, a)], 'remulcld', '( J x. %s ) e. RR' % V2), a1c(w, a, '2re', '2 e. RR'), a1c(w, a, '2ne0', '2 =/= 0')],
                'redivcld', '( ( J x. %s ) / 2 ) e. RR' % V2), lift(w, ar, a), jrp], 'lemul2d', '( ( ( J x. %s ) / 2 ) <_ A <-> ( J x. ( ( J x. %s ) / 2 ) ) <_ ( J x. A ) )' % (V2, V2))
    c2 = sa([lift(w, g1, a), c], 'mpbird', '( ( J x. %s ) / 2 ) <_ A' % V2)
    c3 = linarith(w, a, [c2], '( J x. %s ) <_ ( 2 x. A )' % V2, leaves={'( J x. %s )' % V2: sa([lift(w, jr, a), lift(w, v2r, a)], 'remulcld', '( J x. %s ) e. RR' % V2), 'A': lift(w, ar, a)})
    b = '( %s /\\ 0 = J )' % ante
    sb = mkst(w, b)
    z = sb([sb([w.s([], 'simpr', '( %s -> 0 = J )' % b)], 'eqcomd', 'J = 0')], 'oveq1d', '( J x. %s ) = ( 0 x. %s )' % (V2, V2))
    z2 = sb([z, sb([sb([lift(w, v2r, b)], 'recnd', '%s e. CC' % V2)], 'mul02d', '( 0 x. %s ) = 0' % V2)], 'eqtrd', '( J x. %s ) = 0' % V2)
    d3 = sb([z2, linarith(w, b, [lift(w, a0, b)], '0 <_ ( 2 x. A )', leaves={'A': lift(w, ar, b)})], 'eqbrtrd', '( J x. %s ) <_ ( 2 x. A )' % V2)
    or_ = st([j0, st([st([], '0red', '0 e. RR'), jr], 'leloed', '( 0 <_ J <-> ( 0 < J \\/ 0 = J ) )')], 'mpbid', '( 0 < J \\/ 0 = J )')
    cs = st([c3, d3, or_], 'mpjaodan', '( J x. %s ) <_ ( 2 x. A )' % V2)
    w.qed([cs, bi], 'mpbid', STATEMENTS['zdpar'])
    return w


def zdgood():
    w = W('zdgood', "The arithmetic of Corollary 8.4 (Lean sum_good_le_density): with lambda = ( 1 - T ) log D, J, K <_ B X ^ ( 2 - 2 T ): "
                    "A ( 1 + lambda ) ( J + K ) <_ 20 A B D ^c ( ( 5 / 2 ) ( 1 - T ) ) ((1 + lambda) <_ 10 e ^ ( lambda / 10 ), zdxexp).")
    ante = STATEMENTS['zdgood'].split(' -> ( ( A x.')[0][2:]
    st = mkst(w, ante)
    P1 = '( ( ( D e. RR /\\ 1 < D ) /\\ ( T e. RR /\\ T <_ 1 ) ) /\\ ( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ 0 <_ B ) ) )'
    P2 = '( ( ( J e. RR /\\ 0 <_ J ) /\\ J <_ ( B x. %s ) ) /\\ ( ( K e. RR /\\ 0 <_ K ) /\\ K <_ ( B x. %s ) ) )' % (XB, XB)
    p1 = st([], 'simpl', P1); p2 = st([], 'simpr', P2)
    q1 = st([p1], 'simpld', '( ( D e. RR /\\ 1 < D ) /\\ ( T e. RR /\\ T <_ 1 ) )'); q2 = st([p1], 'simprd', '( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ 0 <_ B ) )')
    dd = st([q1], 'simpld', '( D e. RR /\\ 1 < D )'); tt = st([q1], 'simprd', '( T e. RR /\\ T <_ 1 )')
    dr = st([dd], 'simpld', 'D e. RR'); d1 = st([dd], 'simprd', '1 < D'); tr = st([tt], 'simpld', 'T e. RR'); t1 = st([tt], 'simprd', 'T <_ 1')
    aa = st([q2], 'simpld', '( A e. RR /\\ 0 <_ A )'); bb = st([q2], 'simprd', '( B e. RR /\\ 0 <_ B )')
    ar = st([aa], 'simpld', 'A e. RR'); a0 = st([aa], 'simprd', '0 <_ A'); br = st([bb], 'simpld', 'B e. RR'); b0 = st([bb], 'simprd', '0 <_ B')
    j2 = st([p2], 'simpld', '( ( J e. RR /\\ 0 <_ J ) /\\ J <_ ( B x. %s ) )' % XB); k2 = st([p2], 'simprd', '( ( K e. RR /\\ 0 <_ K ) /\\ K <_ ( B x. %s ) )' % XB)
    jr = st([st([j2], 'simpld', '( J e. RR /\\ 0 <_ J )')], 'simpld', 'J e. RR'); j0 = st([st([j2], 'simpld', '( J e. RR /\\ 0 <_ J )')], 'simprd', '0 <_ J')
    jl = st([j2], 'simprd', 'J <_ ( B x. %s )' % XB)
    kr = st([st([k2], 'simpld', '( K e. RR /\\ 0 <_ K )')], 'simpld', 'K e. RR'); k0 = st([st([k2], 'simpld', '( K e. RR /\\ 0 <_ K )')], 'simprd', '0 <_ K')
    kl = st([k2], 'simprd', 'K <_ ( B x. %s )' % XB)
    drp = st([dr, linarith(w, ante, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    L = '( log ` D )'; lr = st([drp], 'relogcld', '%s e. RR' % L)
    l0 = st([dr, st([d1], 'ltled', '1 <_ D'), w.inst('logge0')], 'syl2anc', '0 <_ %s' % L)
    LAM = '( ( 1 - T ) x. %s )' % L
    t0 = linarith(w, ante, [t1], '0 <_ ( 1 - T )', leaves={'T': tr})
    lamr = st([st([st([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR'), lr], 'remulcld', '%s e. RR' % LAM)
    lam0 = st([st([st([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR'), lr, t0, l0], 'mulge0d', '0 <_ %s' % LAM)
    E = '( exp ` ( %s / ; 1 0 ) )' % LAM
    te = st([lamr, lam0, w.inst('zd10exp')], 'syl2anc', '( 1 + %s ) <_ ( ; 1 0 x. %s )' % (LAM, E))
    er = st([st([lamr, litr(w, ante, '; 1 0'), st([a1c(w, ante, '10nn', '; 1 0 e. NN')], 'nnne0d', '; 1 0 =/= 0')], 'redivcld', '( %s / ; 1 0 ) e. RR' % LAM)],
            'reefcld', '%s e. RR' % E)
    xbr = st([st([st([drp, litr(w, ante, '( 6 / 5 )')], 'rpcxpcld', '%s e. RR+' % XP), st([a1c(w, ante, '2re', '2 e. RR'), st([a1c(w, ante, '2re', '2 e. RR'), tr], 'remulcld',
              '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B2)], 'rpcxpcld', '%s e. RR+' % XB)], 'rpred', '%s e. RR' % XB)
    # A ( 1 + lam ) <_ A ( 10 E ) ; J + K <_ 2 ( B XB )
    l1r = st([st([], '1red', '1 e. RR'), lamr], 'readdcld', '( 1 + %s ) e. RR' % LAM)
    ter = st([litr(w, ante, '; 1 0'), er], 'remulcld', '( ; 1 0 x. %s ) e. RR' % E)
    m1 = st([l1r, ter, ar, a0, te], 'lemul2ad', '( A x. ( 1 + %s ) ) <_ ( A x. ( ; 1 0 x. %s ) )' % (LAM, E))
    BX = '( B x. %s )' % XB
    bxr = st([br, xbr], 'remulcld', '%s e. RR' % BX)
    jk = linarith(w, ante, [jl, kl], '( J + K ) <_ ( 2 x. %s )' % BX, leaves={'J': jr, 'K': kr, BX: bxr})
    l10 = linarith(w, ante, [lam0], '0 <_ ( 1 + %s )' % LAM, leaves={LAM: lamr})
    m2 = st([st([ar, l1r], 'remulcld', '( A x. ( 1 + %s ) ) e. RR' % LAM), st([ar, ter], 'remulcld', '( A x. ( ; 1 0 x. %s ) ) e. RR' % E),
             st([jr, kr], 'readdcld', '( J + K ) e. RR'), st([litr(w, ante, '2'), bxr], 'remulcld', '( 2 x. %s ) e. RR' % BX),
             st([ar, l1r, a0, l10], 'mulge0d', '0 <_ ( A x. ( 1 + %s ) )' % LAM), linarith(w, ante, [j0, k0], '0 <_ ( J + K )', leaves={'J': jr, 'K': kr}), m1, jk],
            'lemul12ad', '( ( A x. ( 1 + %s ) ) x. ( J + K ) ) <_ ( ( A x. ( ; 1 0 x. %s ) ) x. ( 2 x. %s ) )' % (LAM, E, BX))
    eq = lineq(w, ante, '( ( A x. ( ; 1 0 x. %s ) ) x. ( 2 x. %s ) )' % (E, BX), '( ( ; 2 0 x. ( A x. B ) ) x. ( %s x. %s ) )' % (XB, E),
               products=True, leaves={'A': ar, 'B': br, E: er, XB: xbr})
    xe = st([drp, tr, w.inst('zdxexp')], 'syl2anc', '( %s x. %s ) = ( D ^c ( ( 5 / 2 ) x. ( 1 - T ) ) )' % (XB, E))
    eq2 = st([eq, st([xe], 'oveq2d', '( ( ; 2 0 x. ( A x. B ) ) x. ( %s x. %s ) ) = ( ( ; 2 0 x. ( A x. B ) ) x. ( D ^c ( ( 5 / 2 ) x. ( 1 - T ) ) ) )' % (XB, E))],
             'eqtrd', '( ( A x. ( ; 1 0 x. %s ) ) x. ( 2 x. %s ) ) = ( ( ; 2 0 x. ( A x. B ) ) x. ( D ^c ( ( 5 / 2 ) x. ( 1 - T ) ) ) )' % (E, BX))
    w.qed([m2, eq2], 'breqtrd', STATEMENTS['zdgood'])
    return w


def zdlogev():
    w = W('zdlogev', "A log x <_ x ^c B for all x >_ x0 ( A , B ), explicitly x0 = K ^c ( 1 / ( B / 2 ) ), K = A / ( B / 2 ) + 1 "
                     "(Lean log_le_rpow_eventually): log x <_ x ^c ( B / 2 ) / ( B / 2 ) (zdlogcxp) and K <_ x ^c ( B / 2 ).")
    ante = '( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ 0 < B ) )'
    st = mkst(w, ante)
    ar = st([st([], 'simpl', '( A e. RR /\\ 0 <_ A )')], 'simpld', 'A e. RR'); a0 = st([st([], 'simpl', '( A e. RR /\\ 0 <_ A )')], 'simprd', '0 <_ A')
    br = st([st([], 'simpr', '( B e. RR /\\ 0 < B )')], 'simpld', 'B e. RR'); b0 = st([st([], 'simpr', '( B e. RR /\\ 0 < B )')], 'simprd', '0 < B')
    H = '( B / 2 )'
    hrp = st([st([br, b0], 'elrpd', 'B e. RR+'), a1c(w, ante, '2rp', '2 e. RR+')], 'rpdivcld', '%s e. RR+' % H)
    hr = st([hrp], 'rpred', '%s e. RR' % H)
    G = '( A / %s )' % H
    gr = st([ar, hrp], 'rerpdivcld', '%s e. RR' % G)
    g0 = st([ar, hrp, a0], 'divge0d', '0 <_ %s' % G)
    K = '( %s + 1 )' % G
    kr = st([gr, st([], '1red', '1 e. RR')], 'readdcld', '%s e. RR' % K)
    k1 = linarith(w, ante, [g0], '1 <_ %s' % K, leaves={G: gr})
    krp = st([kr, linarith(w, ante, [g0], '0 < %s' % K, leaves={G: gr})], 'elrpd', '%s e. RR+' % K)
    R = '( 1 / %s )' % H
    rrp = st([hrp], 'rpreccld', '%s e. RR+' % R); rr = st([rrp], 'rpred', '%s e. RR' % R)
    U = '( %s ^c %s )' % (K, R)
    urp = st([krp, rr], 'rpcxpcld', '%s e. RR+' % U); ur = st([urp], 'rpred', '%s e. RR' % U)
    u1 = st([st([st([krp], 'rpcnd', '%s e. CC' % K)], 'cxp0d', '( %s ^c 0 ) = 1' % K),
             st([kr, k1, st([], '0red', '0 e. RR'), rr, st([rrp], 'rpge0d', '0 <_ %s' % R)], 'cxplead', '( %s ^c 0 ) <_ %s' % (K, U))], 'eqbrtrrd', '1 <_ %s' % U)
    # K = U ^c H
    ku = st([st([krp, rr, st([hr], 'recnd', '%s e. CC' % H)], 'cxpmuld', '( %s ^c ( %s x. %s ) ) = ( %s ^c %s )' % (K, R, H, U, H)),
             ], 'eqcomd', '( %s ^c %s ) = ( %s ^c ( %s x. %s ) )' % (U, H, K, R, H))
    ri = st([st([hrp], 'rpcnd', '%s e. CC' % H), st([hrp], 'rpne0d', '%s =/= 0' % H)], 'recid2d', '( %s x. %s ) = 1' % (R, H))
    ku2 = st([ku, st([ri], 'oveq2d', '( %s ^c ( %s x. %s ) ) = ( %s ^c 1 )' % (K, R, H, K))], 'eqtrd', '( %s ^c %s ) = ( %s ^c 1 )' % (U, H, K))
    ku3 = st([ku2, st([st([krp], 'rpcnd', '%s e. CC' % K)], 'cxp1d', '( %s ^c 1 ) = %s' % (K, K))], 'eqtrd', '( %s ^c %s ) = %s' % (U, H, K))
    # under ( ( ante /\ v e. RR ) /\ U <_ v )
    b = '( ( %s /\\ v e. RR ) /\\ %s <_ v )' % (ante, U)
    sb = mkst(w, b)
    L_ = lambda x: lift(w, x, b)
    vr = w.s([], 'simplr', '( %s -> v e. RR )' % b); uv = w.s([], 'simpr', '( %s -> %s <_ v )' % (b, U))
    v1 = linarith(w, b, [L_(u1), uv], '1 <_ v', leaves={U: L_(ur), 'v': vr})
    vrp = sb([vr, linarith(w, b, [v1], '0 < v', leaves={'v': vr})], 'elrpd', 'v e. RR+')
    Y = '( v ^c %s )' % H
    yrp = sb([vrp, L_(hr)], 'rpcxpcld', '%s e. RR+' % Y); yr = sb([yrp], 'rpred', '%s e. RR' % Y)
    lc = w.s([bind(w, b, vr, v1, 'v e. RR', '1 <_ v'), L_(hrp), w.inst('zdlogcxp')], 'syl2anc', '( %s -> ( log ` v ) <_ ( %s / %s ) )' % (b, Y, H))
    LV = '( log ` v )'; lvr = sb([vrp], 'relogcld', '%s e. RR' % LV)
    lc2 = sb([lc, sb([lvr, yr, L_(hrp)], 'lemuldivd', '( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) )' % (LV, H, Y, LV, Y, H))], 'mpbird', '( %s x. %s ) <_ %s' % (LV, H, Y))
    u0 = L_(st([urp], 'rpge0d', '0 <_ %s' % U)); h0 = L_(st([hrp], 'rpge0d', '0 <_ %s' % H))
    ky = sb([L_(ur), u0, vr, L_(hr), h0, uv], 'cxple2ad', '( %s ^c %s ) <_ %s' % (U, H, Y))
    ky2 = sb([L_(ku3), ky], 'eqbrtrrd', '%s <_ %s' % (K, Y))
    gh = L_(st([st([ar], 'recnd', 'A e. CC'), st([hrp], 'rpcnd', '%s e. CC' % H), st([hrp], 'rpne0d', '%s =/= 0' % H)], 'divcan1d', '( %s x. %s ) = A' % (G, H)))
    gh2 = sb([gh], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( A x. %s )' % (G, H, LV, LV))
    m1 = sb([sb([lvr, L_(hr)], 'remulcld', '( %s x. %s ) e. RR' % (LV, H)), yr, L_(gr), L_(g0), lc2], 'lemul2ad', '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (G, LV, H, G, Y))
    m2 = sb([L_(gr), L_(kr), yr, sb([yrp], 'rpge0d', '0 <_ %s' % Y), linarith(w, b, [], '%s <_ %s' % (G, K), leaves={G: L_(gr)})], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (G, Y, K, Y))
    m3 = sb([L_(kr), yr, yr, sb([yrp], 'rpge0d', '0 <_ %s' % Y), ky2], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (K, Y, Y, Y))
    ca = w.s([sb([vrp], 'rpcnd', 'v e. CC'), sb([vrp], 'rpne0d', 'v =/= 0'), L_(st([hr], 'recnd', '%s e. CC' % H)), L_(st([hr], 'recnd', '%s e. CC' % H))], 'cxpaddd',
             '( %s -> ( v ^c ( %s + %s ) ) = ( %s x. %s ) )' % (b, H, H, Y, Y))
    hh = lineq(w, b, '( %s + %s )' % (H, H), 'B', leaves={'B': L_(br)})
    vb = sb([sb([hh], 'oveq2d', '( v ^c ( %s + %s ) ) = ( v ^c B )' % (H, H)), ca], 'eqtr3d', '( v ^c B ) = ( %s x. %s )' % (Y, Y))
    g = linarith(w, b, [gh2, m1, m2, m3, vb], '( A x. %s ) <_ ( v ^c B )' % LV,
                 leaves={'A': L_(ar), LV: lvr, G: L_(gr), 'B': L_(br), Y: yr, K: L_(kr), '( v ^c B )': sb([sb([vrp, L_(br)], 'rpcxpcld', '( v ^c B ) e. RR+')], 'rpred', '( v ^c B ) e. RR')}, products=True)
    imp = w.s([g], 'ex', '( ( %s /\\ v e. RR ) -> ( %s <_ v -> ( A x. %s ) <_ ( v ^c B ) ) )' % (ante, U, LV))
    ral = w.s([imp], 'ralrimiva', '( %s -> A. v e. RR ( %s <_ v -> ( A x. %s ) <_ ( v ^c B ) ) )' % (ante, U, LV))
    P = lambda x: '( 1 <_ %s /\\ A. v e. RR ( %s <_ v -> ( A x. ( log ` v ) ) <_ ( v ^c B ) ) )' % (x, x)
    both = st([u1, ral], 'jca', P(U))
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (U, U))
    cu, _ = w.wcongr(P('u'), {'u': U}, 'u = %s' % U, {'u': idu})
    w.qed([ur, both, w.s([cu], 'rspcev', '( ( %s e. RR /\\ %s ) -> E. u e. RR %s )' % (U, P(U), P('u')))], 'syl2anc', STATEMENTS['zdlogev'])
    return w


def zdthresh():
    w = W('zdthresh', "The machine thresholds are eventually true (Lean thresholds_eventually, generic in the two threshold constants A, B >_ 0): "
                      "for v >_ u, 200 <_ log v, A log v <_ v ^c ( 79 / 4000 ), B log v <_ v ^c ( 13 / 500 ); u = max ( e ^ 200 , u1 , u2 ) (zdlogev).")
    ante = '( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ 0 <_ B ) )'
    st = mkst(w, ante)
    aa = st([], 'simpl', '( A e. RR /\\ 0 <_ A )'); bb = st([], 'simpr', '( B e. RR /\\ 0 <_ B )')
    C1 = '( ; 7 9 / ; ; ; 4 0 0 0 )'; C2 = '( ; 1 3 / ; ; 5 0 0 )'
    Q = lambda X, c, x: '( 1 <_ %s /\\ A. v e. RR ( %s <_ v -> ( %s x. ( log ` v ) ) <_ ( v ^c %s ) ) )' % (x, x, X, c)
    def ev(ab, X, c, x):
        cc_ = bind(w, ante, litr(w, ante, c), litle(w, ante, '0', c, strict=True), '%s e. RR' % c, '0 < %s' % c)
        e = st([ab, cc_, w.inst('zdlogev')], 'syl2anc', 'E. u e. RR %s' % Q(X, c, 'u'))
        idu = w.s([], 'id', '( u = %s -> u = %s )' % (x, x))
        cu, _ = w.wcongr(Q(X, c, 'u'), {'u': x}, 'u = %s' % x, {'u': idu})
        cb = w.s([cu], 'cbvrexvw', '( E. u e. RR %s <-> E. %s e. RR %s )' % (Q(X, c, 'u'), x, Q(X, c, x)))
        e2 = st([e, cb], 'sylib', 'E. %s e. RR %s' % (x, Q(X, c, x)))
        # rename the inner v to t
        Pv = '( %s <_ v -> ( %s x. ( log ` v ) ) <_ ( v ^c %s ) )' % (x, X, c)
        Pt = '( %s <_ t -> ( %s x. ( log ` t ) ) <_ ( t ^c %s ) )' % (x, X, c)
        idv = w.s([], 'id', '( v = t -> v = t )')
        cv_, _ = w.wcongr(Pv, {'v': 't'}, 'v = t', {'v': idv})
        r1 = w.s([cv_], 'cbvralvw', '( A. v e. RR %s <-> A. t e. RR %s )' % (Pv, Pt))
        r2 = w.s([r1], 'anbi2i', '( %s <-> ( 1 <_ %s /\\ A. t e. RR %s ) )' % (Q(X, c, x), x, Pt))
        r3 = w.s([r2], 'rexbii', '( E. %s e. RR %s <-> E. %s e. RR ( 1 <_ %s /\\ A. t e. RR %s ) )' % (x, Q(X, c, x), x, x, Pt))
        return st([e2, r3], 'sylib', 'E. %s e. RR ( 1 <_ %s /\\ A. t e. RR %s )' % (x, x, Pt))
    ex1 = ev(aa, 'A', C1, 'x'); ex2 = ev(bb, 'B', C2, 'y')
    Q = lambda X, c, x: '( 1 <_ %s /\\ A. t e. RR ( %s <_ t -> ( %s x. ( log ` t ) ) <_ ( t ^c %s ) ) )' % (x, x, X, c)
    GOALP = lambda u: '( 1 <_ %s /\\ A. v e. RR ( %s <_ v -> ( ; ; 2 0 0 <_ ( log ` v ) /\\ ( A x. ( log ` v ) ) <_ ( v ^c %s ) /\\ ( B x. ( log ` v ) ) <_ ( v ^c %s ) ) ) )' % (u, u, C1, C2)
    G = 'E. u e. RR %s' % GOALP('u')
    c1 = '( ( %s /\\ x e. RR ) /\\ %s )' % (ante, Q('A', C1, 'x'))
    c = '( ( %s /\\ y e. RR ) /\\ %s )' % (c1, Q('B', C2, 'y'))
    sc = mkst(w, c)
    L_ = lambda s_: lift(w, s_, c)
    xr = L_(w.s([], 'simplr', '( %s -> x e. RR )' % c1)); q1 = L_(w.s([], 'simpr', '( %s -> %s )' % (c1, Q('A', C1, 'x'))))
    yr = w.s([], 'simplr', '( %s -> y e. RR )' % c); q2 = w.s([], 'simpr', '( %s -> %s )' % (c, Q('B', C2, 'y')))
    x1 = sc([q1], 'simpld', '1 <_ x')
    ax = sc([q1], 'simprd', 'A. t e. RR ( x <_ t -> ( A x. ( log ` t ) ) <_ ( t ^c %s ) )' % C1)
    ay = sc([q2], 'simprd', 'A. t e. RR ( y <_ t -> ( B x. ( log ` t ) ) <_ ( t ^c %s ) )' % C2)
    M = 'if ( x <_ y , y , x )'
    E2 = '( exp ` ; ; 2 0 0 )'
    U = 'if ( %s <_ %s , %s , %s )' % (E2, M, M, E2)
    mr = sc([yr, xr], 'ifcld', '%s e. RR' % M)
    e2r = sc([litr(w, c, '; ; 2 0 0')], 'reefcld', '%s e. RR' % E2)
    ur = sc([mr, e2r], 'ifcld', '%s e. RR' % U)
    xm = sc([xr, yr, w.inst('max1')], 'syl2anc', 'x <_ %s' % M); ym = sc([xr, yr, w.inst('max2')], 'syl2anc', 'y <_ %s' % M)
    eu = sc([e2r, mr, w.inst('max1')], 'syl2anc', '%s <_ %s' % (E2, U)); mu = sc([e2r, mr, w.inst('max2')], 'syl2anc', '%s <_ %s' % (M, U))
    u1 = linarith(w, c, [x1, xm, mu], '1 <_ %s' % U, leaves={'x': xr, M: mr, U: ur})
    b = '( ( %s /\\ v e. RR ) /\\ %s <_ v )' % (c, U)
    sb = mkst(w, b)
    B_ = lambda s_: lift(w, s_, b)
    vr = w.s([], 'simplr', '( %s -> v e. RR )' % b); uv = w.s([], 'simpr', '( %s -> %s <_ v )' % (b, U))
    xv = linarith(w, b, [B_(xm), B_(mu), uv], 'x <_ v', leaves={'x': B_(xr), M: B_(mr), U: B_(ur), 'v': vr})
    yv = linarith(w, b, [B_(ym), B_(mu), uv], 'y <_ v', leaves={'y': B_(yr), M: B_(mr), U: B_(ur), 'v': vr})
    cv = '( %s /\\ v e. RR )' % c
    def inst_(al, xx, X, cc_):
        Pt = '( %s <_ t -> ( %s x. ( log ` t ) ) <_ ( t ^c %s ) )' % (xx, X, cc_)
        Pv = '( %s <_ v -> ( %s x. ( log ` v ) ) <_ ( v ^c %s ) )' % (xx, X, cc_)
        idt = w.s([], 'id', '( t = v -> t = v )')
        ct, _ = w.wcongr(Pt, {'t': 'v'}, 't = v', {'t': idt})
        rs = w.s([ct], 'rspcv', '( v e. RR -> ( A. t e. RR %s -> %s ) )' % (Pt, Pv))
        return w.s([w.s([], 'simpr', '( %s -> v e. RR )' % cv), lift(w, al, cv), rs], 'sylc', '( %s -> %s )' % (cv, Pv))
    ix = inst_(ax, 'x', 'A', C1)
    iy = inst_(ay, 'y', 'B', C2)
    ga = sb([xv, lift(w, ix, b)], 'mpd', '( A x. ( log ` v ) ) <_ ( v ^c %s )' % C1)
    gb = sb([yv, lift(w, iy, b)], 'mpd', '( B x. ( log ` v ) ) <_ ( v ^c %s )' % C2)
    ev_ = linarith(w, b, [B_(eu), uv], '%s <_ v' % E2, leaves={E2: B_(e2r), U: B_(ur), 'v': vr})
    e2p = sb([litr(w, b, '; ; 2 0 0')], 'rpefcld', '%s e. RR+' % E2)
    vrp = sb([vr, sb([sb([e2p], 'rpgt0d', '0 < %s' % E2), ev_], 'ltletrd', '0 < v')], 'elrpd', 'v e. RR+')
    lg = sb([ev_, sb([e2p, vrp], 'logled', '( %s <_ v <-> ( log ` %s ) <_ ( log ` v ) )' % (E2, E2))], 'mpbid', '( log ` %s ) <_ ( log ` v )' % E2)
    l200 = sb([sb([litr(w, b, '; ; 2 0 0'), w.inst('relogef')], 'syl', '( log ` %s ) = ; ; 2 0 0' % E2), lg], 'eqbrtrrd', '; ; 2 0 0 <_ ( log ` v )')
    tri = sb([l200, ga, gb], '3jca', '( ; ; 2 0 0 <_ ( log ` v ) /\\ ( A x. ( log ` v ) ) <_ ( v ^c %s ) /\\ ( B x. ( log ` v ) ) <_ ( v ^c %s ) )' % (C1, C2))
    imp = w.s([tri], 'ex', '( %s -> ( %s <_ v -> ( ; ; 2 0 0 <_ ( log ` v ) /\\ ( A x. ( log ` v ) ) <_ ( v ^c %s ) /\\ ( B x. ( log ` v ) ) <_ ( v ^c %s ) ) ) )' % (cv, U, C1, C2))
    ral = w.s([imp], 'ralrimiva', '( %s -> A. v e. RR ( %s <_ v -> ( ; ; 2 0 0 <_ ( log ` v ) /\\ ( A x. ( log ` v ) ) <_ ( v ^c %s ) /\\ ( B x. ( log ` v ) ) <_ ( v ^c %s ) ) ) )' % (c, U, C1, C2))
    both = sc([u1, ral], 'jca', GOALP(U))
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (U, U))
    cu, _ = w.wcongr(GOALP('u'), {'u': U}, 'u = %s' % U, {'u': idu})
    g = sc([ur, both, w.s([cu], 'rspcev', '( ( %s e. RR /\\ %s ) -> %s )' % (U, GOALP(U), G))], 'syl2anc', G)
    # eliminate y then x
    gy = w.s([w.s([g], 'ex', '( ( %s /\\ y e. RR ) -> ( %s -> %s ) )' % (c1, Q('B', C2, 'y'), G))], 'rexlimdva', '( %s -> ( E. y e. RR %s -> %s ) )' % (c1, Q('B', C2, 'y'), G))
    gy2 = w.s([lift(w, ex2, c1), gy], 'mpd', '( %s -> %s )' % (c1, G))
    gx = w.s([w.s([gy2], 'ex', '( ( %s /\\ x e. RR ) -> ( %s -> %s ) )' % (ante, Q('A', C1, 'x'), G))], 'rexlimdva', '( %s -> ( E. x e. RR %s -> %s ) )' % (ante, Q('A', C1, 'x'), G))
    w.qed([ex1, gx], 'mpd', STATEMENTS['zdthresh'])
    return w


def zdbandpt():
    w = W('zdbandpt', "The band thresholds at one point (Lean band_thresholds, the body): for V >_ 200, V >_ ( 16 / A ^ 2 ) ^ 2, V >_ 2 ( B + 3 ): "
                      "log V <_ V / 4, ( log V ) ^ 2 <_ A ^ 2 V, B + 3 <_ V / 2 (log V <_ 2 V ^c ( 1 / 2 ), log V <_ 4 V ^c ( 1 / 4 ), zdlogcxp).")
    ante = STATEMENTS['zdbandpt'].split(' ) -> ( ( log ` V )')[0][2:] + ' )'
    st = mkst(w, ante)
    P1 = '( A e. RR+ /\\ B e. RR )'
    P2 = '( V e. RR /\\ ( ; ; 2 0 0 <_ V /\\ ( ( ; 1 6 / ( A ^ 2 ) ) ^ 2 ) <_ V /\\ ( 2 x. ( B + 3 ) ) <_ V ) )'
    p1 = st([], 'simpl', P1); p2 = st([], 'simpr', P2)
    arp = st([p1], 'simpld', 'A e. RR+'); br = st([p1], 'simprd', 'B e. RR')
    vr = st([p2], 'simpld', 'V e. RR'); p3 = st([p2], 'simprd', '( ; ; 2 0 0 <_ V /\\ ( ( ; 1 6 / ( A ^ 2 ) ) ^ 2 ) <_ V /\\ ( 2 x. ( B + 3 ) ) <_ V )')
    v200 = st([p3], 'simp1d', '; ; 2 0 0 <_ V'); v16 = st([p3], 'simp2d', '( ( ; 1 6 / ( A ^ 2 ) ) ^ 2 ) <_ V'); vb = st([p3], 'simp3d', '( 2 x. ( B + 3 ) ) <_ V')
    v1 = linarith(w, ante, [v200], '1 <_ V', leaves={'V': vr})
    vrp = st([vr, linarith(w, ante, [v200], '0 < V', leaves={'V': vr})], 'elrpd', 'V e. RR+')
    vc = st([vrp], 'rpcnd', 'V e. CC')
    S = '( V ^c ( 1 / 2 ) )'; Q = '( V ^c ( 1 / 4 ) )'
    srp = st([vrp, litr(w, ante, '( 1 / 2 )')], 'rpcxpcld', '%s e. RR+' % S); sr = st([srp], 'rpred', '%s e. RR' % S); s0 = st([srp], 'rpge0d', '0 <_ %s' % S)
    qrp = st([vrp, litr(w, ante, '( 1 / 4 )')], 'rpcxpcld', '%s e. RR+' % Q); qr = st([qrp], 'rpred', '%s e. RR' % Q); q0 = st([qrp], 'rpge0d', '0 <_ %s' % Q)
    two = a1c(w, ante, '2nn0', '2 e. NN0')
    hc = lambda x: st([litr(w, ante, x)], 'recnd', '%s e. CC' % x)
    a2 = st([vc, hc('( 1 / 2 )'), two], 'cxpmul2d', '( V ^c ( ( 1 / 2 ) x. 2 ) ) = ( %s ^ 2 )' % S)
    e1 = lineq(w, ante, '( ( 1 / 2 ) x. 2 )', '1')
    a3 = st([st([e1], 'oveq2d', '( V ^c ( ( 1 / 2 ) x. 2 ) ) = ( V ^c 1 )'), st([vc], 'cxp1d', '( V ^c 1 ) = V')], 'eqtrd', '( V ^c ( ( 1 / 2 ) x. 2 ) ) = V')
    ss = st([a2, a3], 'eqtr3d', '( %s ^ 2 ) = V' % S)
    b2 = st([vc, hc('( 1 / 4 )'), two], 'cxpmul2d', '( V ^c ( ( 1 / 4 ) x. 2 ) ) = ( %s ^ 2 )' % Q)
    e2 = lineq(w, ante, '( ( 1 / 4 ) x. 2 )', '( 1 / 2 )')
    qq = st([b2, st([e2], 'oveq2d', '( V ^c ( ( 1 / 4 ) x. 2 ) ) = %s' % S)], 'eqtr3d', '( %s ^ 2 ) = %s' % (Q, S))
    LV = '( log ` V )'; lvr = st([vrp], 'relogcld', '%s e. RR' % LV)
    lv0 = st([vr, v1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % LV)
    vv = bind(w, ante, vr, v1, 'V e. RR', '1 <_ V')
    ls = st([vv, st([a1c(w, ante, '2rp', '2 e. RR+')], 'rpreccld', '( 1 / 2 ) e. RR+'), w.inst('zdlogcxp')], 'syl2anc', '%s <_ ( %s / ( 1 / 2 ) )' % (LV, S))
    lq = st([vv, w.s([num.rp(w, '( 1 / 4 )')], 'a1i', '( %s -> ( 1 / 4 ) e. RR+ )' % ante), w.inst('zdlogcxp')], 'syl2anc', '%s <_ ( %s / ( 1 / 4 ) )' % (LV, Q))
    def dd(X, n):
        Xr = sr if X == S else qr
        a_ = st([st([Xr], 'recnd', '%s e. CC' % X), a1c(w, ante, 'ax-1cn', '1 e. CC'), st([litr(w, ante, n)], 'recnd', '%s e. CC' % n),
                 a1c(w, ante, 'ax-1ne0', '1 =/= 0'), st([w.s([num.rp(w, n)], 'a1i', '( %s -> %s e. RR+ )' % (ante, n))], 'rpne0d', '%s =/= 0' % n)],
                'divdiv2d', '( %s / ( 1 / %s ) ) = ( ( %s x. %s ) / 1 )' % (X, n, X, n))
        b_ = st([st([st([Xr], 'recnd', '%s e. CC' % X), st([litr(w, ante, n)], 'recnd', '%s e. CC' % n)], 'mulcld', '( %s x. %s ) e. CC' % (X, n))], 'div1d',
                '( ( %s x. %s ) / 1 ) = ( %s x. %s )' % (X, n, X, n))
        return st([a_, b_], 'eqtrd', '( %s / ( 1 / %s ) ) = ( %s x. %s )' % (X, n, X, n))
    ls = st([ls, dd(S, '2')], 'breqtrd', '%s <_ ( %s x. 2 )' % (LV, S))
    lq = st([lq, dd(Q, '4')], 'breqtrd', '%s <_ ( %s x. 4 )' % (LV, Q))
    # 8 <_ S
    e64 = w.s([w.s([w.s([], '8cn', '8 e. CC')], 'sqvali', '( 8 ^ 2 ) = ( 8 x. 8 )'), num.mul_lits(w, '8', '8')], 'eqtri', '( 8 ^ 2 ) = ; 6 4')
    s64 = linarith(w, ante, [ss, v200], '; 6 4 <_ ( %s ^ 2 )' % S, leaves={S: sr, 'V': vr}, products=True)
    s64b = st([w.s([e64], 'a1i', '( %s -> ( 8 ^ 2 ) = ; 6 4 )' % ante), s64], 'eqbrtrd', '( 8 ^ 2 ) <_ ( %s ^ 2 )' % S)
    le8 = st([bind(w, ante, litr(w, ante, '8'), litle(w, ante, '0', '8'), '8 e. RR', '0 <_ 8'), bind(w, ante, sr, s0, '%s e. RR' % S, '0 <_ %s' % S), w.inst('le2sq')],
             'syl2anc', '( 8 <_ %s <-> ( 8 ^ 2 ) <_ ( %s ^ 2 ) )' % (S, S))
    s8 = st([s64b, le8], 'mpbird', '8 <_ %s' % S)
    # 16 / A ^ 2 <_ S
    A2 = '( A ^ 2 )'
    a2rp = st([arp, a1c(w, ante, '2z', '2 e. ZZ')], 'rpexpcld', '%s e. RR+' % A2)
    T = '( ; 1 6 / %s )' % A2
    trp = st([w.s([num.rp(w, '; 1 6')], 'a1i', '( %s -> ; 1 6 e. RR+ )' % ante), a2rp], 'rpdivcld', '%s e. RR+' % T)
    tr = st([trp], 'rpred', '%s e. RR' % T)
    lt = st([bind(w, ante, tr, st([trp], 'rpge0d', '0 <_ %s' % T), '%s e. RR' % T, '0 <_ %s' % T), bind(w, ante, sr, s0, '%s e. RR' % S, '0 <_ %s' % S), w.inst('le2sq')],
            'syl2anc', '( %s <_ %s <-> ( %s ^ 2 ) <_ ( %s ^ 2 ) )' % (T, S, T, S))
    ts = st([st([v16, st([ss], 'eqcomd', 'V = ( %s ^ 2 )' % S)], 'breqtrd', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (T, S)), lt], 'mpbird', '%s <_ %s' % (T, S))
    # (1)
    m8 = st([litr(w, ante, '8'), sr, sr, s0, s8], 'lemul1ad', '( 8 x. %s ) <_ ( %s x. %s )' % (S, S, S))
    g1 = linarith(w, ante, [ls, m8, ss], '%s <_ ( V / 4 )' % LV, leaves={LV: lvr, S: sr, 'V': vr}, products=True)
    # (2)
    g2a = st([bind(w, ante, lvr, lv0, '%s e. RR' % LV, '0 <_ %s' % LV), bind(w, ante, st([qr, litr(w, ante, '4')], 'remulcld', '( %s x. 4 ) e. RR' % Q), lq, '( %s x. 4 ) e. RR' % Q, '%s <_ ( %s x. 4 )' % (LV, Q)), w.inst('le2sq2')], 'syl2anc',
             '( %s ^ 2 ) <_ ( ( %s x. 4 ) ^ 2 )' % (LV, Q))
    m1 = st([tr, sr, st([a2rp], 'rpred', '%s e. RR' % A2), st([a2rp], 'rpge0d', '0 <_ %s' % A2), ts], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (A2, T, A2, S))
    dc = st([st([litr(w, ante, '; 1 6')], 'recnd', '; 1 6 e. CC'), st([a2rp], 'rpcnd', '%s e. CC' % A2),
             st([a2rp], 'rpne0d', '%s =/= 0' % A2)], 'divcan2d', '( %s x. %s ) = ; 1 6' % (A2, T))
    m16 = st([dc, m1], 'eqbrtrrd', '; 1 6 <_ ( %s x. %s )' % (A2, S))
    AS = '( %s x. %s )' % (A2, S)
    m2 = st([litr(w, ante, '; 1 6'), st([st([a2rp], 'rpred', '%s e. RR' % A2), sr], 'remulcld', '%s e. RR' % AS), sr, s0, m16], 'lemul1ad',
            '( ; 1 6 x. %s ) <_ ( %s x. %s )' % (S, AS, S))
    eqv = st([ss], 'oveq2d', '( %s x. ( %s ^ 2 ) ) = ( %s x. V )' % (A2, S, A2))
    g2 = linarith(w, ante, [g2a, qq, m2, eqv], '( %s ^ 2 ) <_ ( %s x. V )' % (LV, A2), leaves={LV: lvr, Q: qr, S: sr, 'A': st([arp], 'rpred', 'A e. RR'), 'V': vr}, products=True)
    g3 = linarith(w, ante, [vb], '( B + 3 ) <_ ( V / 2 )', leaves={'B': br, 'V': vr})
    w.qed([g1, g2, g3], '3jca', STATEMENTS['zdbandpt'])
    return w


def zdband():
    w = W('zdband', "The Theorem Z band thresholds (Lean band_thresholds): for v >_ L0 = max ( 200 , ( 16 / A ^ 2 ) ^ 2 , 2 ( B + 3 ) ), "
                    "log v <_ v / 4, ( log v ) ^ 2 <_ A ^ 2 v, B + 3 <_ v / 2 (zdbandpt).")
    ante = '( A e. RR+ /\\ B e. RR )'
    st = mkst(w, ante)
    arp = st([], 'simpl', 'A e. RR+'); br = st([], 'simpr', 'B e. RR')
    T2 = '( ( ; 1 6 / ( A ^ 2 ) ) ^ 2 )'; W_ = '( 2 x. ( B + 3 ) )'
    M = 'if ( %s <_ %s , %s , %s )' % (T2, W_, W_, T2)
    U = 'if ( ; ; 2 0 0 <_ %s , %s , ; ; 2 0 0 )' % (M, M)
    a2 = st([arp, a1c(w, ante, '2z', '2 e. ZZ')], 'rpexpcld', '( A ^ 2 ) e. RR+')
    t2r = st([st([litr(w, ante, '; 1 6'), a2], 'rerpdivcld', '( ; 1 6 / ( A ^ 2 ) ) e. RR')], 'resqcld', '%s e. RR' % T2)
    wr = st([litr(w, ante, '2'), st([br, litr(w, ante, '3')], 'readdcld', '( B + 3 ) e. RR')], 'remulcld', '%s e. RR' % W_)
    mr = st([wr, t2r], 'ifcld', '%s e. RR' % M)
    c200 = litr(w, ante, '; ; 2 0 0')
    ur = st([mr, c200], 'ifcld', '%s e. RR' % U)
    u200 = st([c200, mr, w.inst('max1')], 'syl2anc', '; ; 2 0 0 <_ %s' % U)
    mu = st([c200, mr, w.inst('max2')], 'syl2anc', '%s <_ %s' % (M, U))
    tm = st([t2r, wr, w.inst('max1')], 'syl2anc', '%s <_ %s' % (T2, M)); wm = st([t2r, wr, w.inst('max2')], 'syl2anc', '%s <_ %s' % (W_, M))
    b = '( ( %s /\\ v e. RR ) /\\ %s <_ v )' % (ante, U)
    sb = mkst(w, b)
    B_ = lambda x: lift(w, x, b)
    vr = w.s([], 'simplr', '( %s -> v e. RR )' % b); uv = w.s([], 'simpr', '( %s -> %s <_ v )' % (b, U))
    lv = {U: B_(ur), M: B_(mr), 'v': vr}
    v200 = linarith(w, b, [B_(u200), uv], '; ; 2 0 0 <_ v', leaves=lv)
    vt = linarith(w, b, [B_(tm), B_(mu), uv], '%s <_ v' % T2, leaves=dict(lv, **{T2: B_(t2r)}))
    vw = linarith(w, b, [B_(wm), B_(mu), uv], '%s <_ v' % W_, leaves=dict(lv, **{'B': B_(br)}))
    pt = sb([w.s([], 'simpll', '( %s -> %s )' % (b, ante)),
             bind(w, b, vr, sb([v200, vt, vw], '3jca', '( ; ; 2 0 0 <_ v /\\ %s <_ v /\\ %s <_ v )' % (T2, W_)), 'v e. RR', '( ; ; 2 0 0 <_ v /\\ %s <_ v /\\ %s <_ v )' % (T2, W_)),
             w.inst('zdbandpt')], 'syl2anc', BAND3('v'))
    imp = w.s([pt], 'ex', '( ( %s /\\ v e. RR ) -> ( %s <_ v -> %s ) )' % (ante, U, BAND3('v')))
    ral = w.s([imp], 'ralrimiva', '( %s -> A. v e. RR ( %s <_ v -> %s ) )' % (ante, U, BAND3('v')))
    P = lambda u: '( ; ; 2 0 0 <_ %s /\\ A. v e. RR ( %s <_ v -> %s ) )' % (u, u, BAND3('v'))
    both = st([u200, ral], 'jca', P(U))
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (U, U))
    cu, _ = w.wcongr(P('u'), {'u': U}, 'u = %s' % U, {'u': idu})
    w.qed([ur, both, w.s([cu], 'rspcev', '( ( %s e. RR /\\ %s ) -> E. u e. RR %s )' % (U, P(U), P('u')))], 'syl2anc', STATEMENTS['zdband'])
    return w


def zdthmh():
    w = W('zdthmh', "Theorem H for a generic left side (Lean theoremH): if Z <_ H E ^ ( P ( 1 - S ) ) log ( d ( t + 2 ) ) ^ K with E = d t ^ c0, "
                    "P <_ 7 / 2 and 9 / 10 <_ S <_ 99 / 100, then Z <_ H ( 400 ( K + 1 ) ) ^ K E ^ ( ( 9 / 2 ) ( 1 - S ) ): "
                    "log ( d ( t + 2 ) ) <_ 2 log E <_ 400 ( K + 1 ) E ^ eps with eps = 1 / ( 200 ( K + 1 ) ), and eps K <_ 1 / 200.")
    ante = STATEMENTS['zdthmh'].split(' ) -> Z <_')[0][2:] + ' )'
    st = mkst(w, ante)
    TR = '( N e. NN /\\ ( T e. RR /\\ 2 <_ T ) /\\ ( C e. RR /\\ 1 <_ C ) )'
    PS = '( ( P e. RR /\\ P <_ ( 7 / 2 ) ) /\\ ( S e. RR /\\ ( ( 9 / ; 1 0 ) <_ S /\\ S <_ ( ; 9 9 / ; ; 1 0 0 ) ) ) )'
    L1 = '( %s /\\ %s )' % (TR, PS)
    E = EE
    LD = '( log ` ( N x. ( T + 2 ) ) )'
    EP = '( %s ^c ( P x. ( 1 - S ) ) )' % E
    KZ = '( ( K e. NN0 /\\ ( H e. RR /\\ 0 <_ H ) ) /\\ ( Z e. RR /\\ Z <_ ( ( H x. %s ) x. ( %s ^ K ) ) ) )' % (EP, LD)
    l1 = st([], 'simpl', L1); kz = st([], 'simpr', KZ)
    tr3 = st([l1], 'simpld', TR); ps = st([l1], 'simprd', PS)
    pr = st([st([ps], 'simpld', '( P e. RR /\\ P <_ ( 7 / 2 ) )')], 'simpld', 'P e. RR'); p72 = st([st([ps], 'simpld', '( P e. RR /\\ P <_ ( 7 / 2 ) )')], 'simprd', 'P <_ ( 7 / 2 )')
    ss_ = st([ps], 'simprd', '( S e. RR /\\ ( ( 9 / ; 1 0 ) <_ S /\\ S <_ ( ; 9 9 / ; ; 1 0 0 ) ) )')
    sr = st([ss_], 'simpld', 'S e. RR'); s99 = st([st([ss_], 'simprd', '( ( 9 / ; 1 0 ) <_ S /\\ S <_ ( ; 9 9 / ; ; 1 0 0 ) )')], 'simprd', 'S <_ ( ; 9 9 / ; ; 1 0 0 )')
    kh = st([kz], 'simpld', '( K e. NN0 /\\ ( H e. RR /\\ 0 <_ H ) )'); zz = st([kz], 'simprd', '( Z e. RR /\\ Z <_ ( ( H x. %s ) x. ( %s ^ K ) ) )' % (EP, LD))
    kn = st([kh], 'simpld', 'K e. NN0'); hr = st([st([kh], 'simprd', '( H e. RR /\\ 0 <_ H )')], 'simpld', 'H e. RR')
    h0 = st([st([kh], 'simprd', '( H e. RR /\\ 0 <_ H )')], 'simprd', '0 <_ H')
    zr = st([zz], 'simpld', 'Z e. RR'); zle = st([zz], 'simprd', 'Z <_ ( ( H x. %s ) x. ( %s ^ K ) )' % (EP, LD))
    nn = st([tr3], 'simp1d', 'N e. NN'); tt = st([tr3], 'simp2d', '( T e. RR /\\ 2 <_ T )')
    t_r = st([tt], 'simpld', 'T e. RR'); t2 = st([tt], 'simprd', '2 <_ T')
    sc = st([tr3, w.inst('zdscale')], 'syl', '( N x. ( T + 2 ) ) <_ ( 2 x. %s )' % E)
    sc2 = st([tr3, w.inst('zdscale2')], 'syl', '2 <_ %s' % E)
    ccr = st([st([tr3], 'simp3d', '( C e. RR /\\ 1 <_ C )')], 'simpld', 'C e. RR')
    er = st([st([nn], 'nnred', 'N e. RR'), st([t_r, linarith(w, ante, [t2], '0 <_ T', leaves={'T': t_r}), ccr], 'recxpcld', '( T ^c C ) e. RR')], 'remulcld', '%s e. RR' % E)
    erp = st([er, linarith(w, ante, [sc2], '0 < %s' % E, leaves={E: er})], 'elrpd', '%s e. RR+' % E)
    e1 = linarith(w, ante, [sc2], '1 <_ %s' % E, leaves={E: er})
    NT = '( N x. ( T + 2 ) )'
    ntr = st([st([nn], 'nnred', 'N e. RR'), st([t_r, a1c(w, ante, '2re', '2 e. RR')], 'readdcld', '( T + 2 ) e. RR')], 'remulcld', '%s e. RR' % NT)
    m_ = st([st([], '1red', '1 e. RR'), st([t_r, a1c(w, ante, '2re', '2 e. RR')], 'readdcld', '( T + 2 ) e. RR'), st([nn], 'nnred', 'N e. RR'),
             linarith(w, ante, [sy(w, ante, nn, 'nnge1', '1 <_ N')], '0 <_ N', leaves={'N': st([nn], 'nnred', 'N e. RR')}),
             linarith(w, ante, [t2], '1 <_ ( T + 2 )', leaves={'T': t_r})], 'lemul2ad', '( N x. 1 ) <_ %s' % NT)
    nt1 = linarith(w, ante, [m_, sy(w, ante, nn, 'nnge1', '1 <_ N')], '1 <_ %s' % NT, leaves={'N': st([nn], 'nnred', 'N e. RR'), NT: ntr})
    ntrp = st([ntr, linarith(w, ante, [nt1], '0 < %s' % NT, leaves={NT: ntr})], 'elrpd', '%s e. RR+' % NT)
    ldr = st([ntrp], 'relogcld', '%s e. RR' % LD)
    ld0 = st([ntr, nt1, w.inst('logge0')], 'syl2anc', '0 <_ %s' % LD)
    TE = '( 2 x. %s )' % E
    terp = st([a1c(w, ante, '2rp', '2 e. RR+'), erp], 'rpmulcld', '%s e. RR+' % TE)
    l1_ = st([sc, st([ntrp, terp], 'logled', '( %s <_ %s <-> %s <_ ( log ` %s ) )' % (NT, TE, LD, TE))], 'mpbid', '%s <_ ( log ` %s )' % (LD, TE))
    lm = st([a1c(w, ante, '2rp', '2 e. RR+'), erp], 'relogmuld', '( log ` %s ) = ( ( log ` 2 ) + ( log ` %s ) )' % (TE, E))
    l2e = st([sc2, st([a1c(w, ante, '2rp', '2 e. RR+'), erp], 'logled', '( 2 <_ %s <-> ( log ` 2 ) <_ ( log ` %s ) )' % (E, E))], 'mpbid', '( log ` 2 ) <_ ( log ` %s )' % E)
    LE = '( log ` %s )' % E
    ler = st([erp], 'relogcld', '%s e. RR' % LE)
    l2r = st([a1c(w, ante, '2rp', '2 e. RR+')], 'relogcld', '( log ` 2 ) e. RR')
    ld2 = linarith(w, ante, [l1_, lm, l2e], '%s <_ ( 2 x. %s )' % (LD, LE), leaves={LD: ldr, '( log ` %s )' % TE: st([terp], 'relogcld', '( log ` %s ) e. RR' % TE), '( log ` 2 )': l2r, LE: ler})
    # eps
    Y = '( ; ; 2 0 0 x. ( K + 1 ) )'
    kr = st([kn], 'nn0red', 'K e. RR')
    k1rp = st([st([kr, st([], '1red', '1 e. RR')], 'readdcld', '( K + 1 ) e. RR'), linarith(w, ante, [st([kn], 'nn0ge0d', '0 <_ K')], '0 < ( K + 1 )', leaves={'K': kr})], 'elrpd', '( K + 1 ) e. RR+')
    yrp = st([w.s([num.rp(w, '; ; 2 0 0')], 'a1i', '( %s -> ; ; 2 0 0 e. RR+ )' % ante), k1rp], 'rpmulcld', '%s e. RR+' % Y)
    EPS = '( 1 / %s )' % Y
    epsrp = st([yrp], 'rpreccld', '%s e. RR+' % EPS); epsr = st([epsrp], 'rpred', '%s e. RR' % EPS)
    EE_ = '( %s ^c %s )' % (E, EPS)
    eerp = st([erp, epsr], 'rpcxpcld', '%s e. RR+' % EE_); eer = st([eerp], 'rpred', '%s e. RR' % EE_)
    lc = st([bind(w, ante, er, e1, '%s e. RR' % E, '1 <_ %s' % E), epsrp, w.inst('zdlogcxp')], 'syl2anc', '%s <_ ( %s / %s )' % (LE, EE_, EPS))
    yc = st([yrp], 'rpcnd', '%s e. CC' % Y)
    dv = st([st([eer], 'recnd', '%s e. CC' % EE_), a1c(w, ante, 'ax-1cn', '1 e. CC'), yc, a1c(w, ante, 'ax-1ne0', '1 =/= 0'), st([yrp], 'rpne0d', '%s =/= 0' % Y)],
            'divdiv2d', '( %s / %s ) = ( ( %s x. %s ) / 1 )' % (EE_, EPS, EE_, Y))
    dv2 = st([dv, st([st([st([eer], 'recnd', '%s e. CC' % EE_), yc], 'mulcld', '( %s x. %s ) e. CC' % (EE_, Y))], 'div1d', '( ( %s x. %s ) / 1 ) = ( %s x. %s )' % (EE_, Y, EE_, Y))],
             'eqtrd', '( %s / %s ) = ( %s x. %s )' % (EE_, EPS, EE_, Y))
    lc2 = st([lc, dv2], 'breqtrd', '%s <_ ( %s x. %s )' % (LE, EE_, Y))
    F4 = '( ; ; 4 0 0 x. ( K + 1 ) )'
    M1 = '( %s x. %s )' % (F4, EE_)
    ldm = linarith(w, ante, [ld2, lc2], '%s <_ %s' % (LD, M1), leaves={LD: ldr, LE: ler, EE_: eer, 'K': kr}, products=True)
    f4r = st([litr(w, ante, '; ; 4 0 0'), st([kr, st([], '1red', '1 e. RR')], 'readdcld', '( K + 1 ) e. RR')], 'remulcld', '%s e. RR' % F4)
    m1r = st([f4r, eer], 'remulcld', '%s e. RR' % M1)
    pk = w.s([bind3(w, ante, ldr, m1r, kn, '%s e. RR' % LD, '%s e. RR' % M1, 'K e. NN0'), bind(w, ante, ld0, ldm, '0 <_ %s' % LD, '%s <_ %s' % (LD, M1)), w.inst('leexp1a')],
             'syl2anc', '( %s -> ( %s ^ K ) <_ ( %s ^ K ) )' % (ante, LD, M1))
    W4 = '( %s ^ K )' % F4
    me = st([st([f4r], 'recnd', '%s e. CC' % F4), st([eer], 'recnd', '%s e. CC' % EE_), kn], 'mulexpd', '( %s ^ K ) = ( %s x. ( %s ^ K ) )' % (M1, W4, EE_))
    cm = st([st([erp], 'rpcnd', '%s e. CC' % E), st([epsr], 'recnd', '%s e. CC' % EPS), kn], 'cxpmul2d', '( %s ^c ( %s x. K ) ) = ( %s ^ K )' % (E, EPS, EE_))
    E200 = '( %s ^c ( 1 / ; ; 2 0 0 ) )' % E
    ri = st([yc, st([yrp], 'rpne0d', '%s =/= 0' % Y)], 'recid2d', '( %s x. %s ) = 1' % (EPS, Y))
    ek = linarith(w, ante, [ri, st([epsrp], 'rpge0d', '0 <_ %s' % EPS)], '( %s x. K ) <_ ( 1 / ; ; 2 0 0 )' % EPS, leaves={EPS: epsr, 'K': kr}, products=True)
    cl_ = st([er, e1, st([epsr, kr], 'remulcld', '( %s x. K ) e. RR' % EPS), litr(w, ante, '( 1 / ; ; 2 0 0 )'), ek], 'cxplead', '( %s ^c ( %s x. K ) ) <_ %s' % (E, EPS, E200))
    ekk = st([cm, cl_], 'eqbrtrrd', '( %s ^ K ) <_ %s' % (EE_, E200))
    w4r = st([f4r, kn], 'reexpcld', '%s e. RR' % W4)
    w40 = st([f4r, kn, linarith(w, ante, [st([kn], 'nn0ge0d', '0 <_ K')], '0 <_ %s' % F4, leaves={'K': kr})], 'expge0d', '0 <_ %s' % W4)
    e200r = st([st([erp, litr(w, ante, '( 1 / ; ; 2 0 0 )')], 'rpcxpcld', '%s e. RR+' % E200)], 'rpred', '%s e. RR' % E200)
    m2 = st([st([eer, kn], 'reexpcld', '( %s ^ K ) e. RR' % EE_), e200r, w4r, w40, ekk], 'lemul2ad', '( %s x. ( %s ^ K ) ) <_ ( %s x. %s )' % (W4, EE_, W4, E200))
    ldk = st([st([pk, me], 'breqtrd', '( %s ^ K ) <_ ( %s x. ( %s ^ K ) )' % (LD, W4, EE_)), m2], 'letrd', '( %s ^ K ) <_ ( %s x. %s )' % (LD, W4, E200))
    # the exponent gap
    E92 = '( %s ^c ( ( 9 / 2 ) x. ( 1 - S ) ) )' % E
    XP_ = '( P x. ( 1 - S ) )'
    xr_ = st([pr, st([st([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '%s e. RR' % XP_)
    pg = st([st([litr(w, ante, '( 7 / 2 )'), pr], 'resubcld', '( ( 7 / 2 ) - P ) e. RR'), st([st([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR'),
             linarith(w, ante, [p72], '0 <_ ( ( 7 / 2 ) - P )', leaves={'P': pr}), linarith(w, ante, [s99], '0 <_ ( 1 - S )', leaves={'S': sr})], 'mulge0d',
            '0 <_ ( ( ( 7 / 2 ) - P ) x. ( 1 - S ) )')
    gap = linarith(w, ante, [pg, s99], '( %s + ( 1 / ; ; 2 0 0 ) ) <_ ( ( 9 / 2 ) x. ( 1 - S ) )' % XP_, leaves={'P': pr, 'S': sr}, products=True)
    ca = st([st([erp], 'rpcnd', '%s e. CC' % E), st([erp], 'rpne0d', '%s =/= 0' % E), st([xr_], 'recnd', '%s e. CC' % XP_),
             st([litr(w, ante, '( 1 / ; ; 2 0 0 )')], 'recnd', '( 1 / ; ; 2 0 0 ) e. CC')], 'cxpaddd', '( %s ^c ( %s + ( 1 / ; ; 2 0 0 ) ) ) = ( %s x. %s )' % (E, XP_, EP, E200))
    g92 = st([er, e1, st([xr_, litr(w, ante, '( 1 / ; ; 2 0 0 )')], 'readdcld', '( %s + ( 1 / ; ; 2 0 0 ) ) e. RR' % XP_),
              st([litr(w, ante, '( 9 / 2 )'), st([st([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '( ( 9 / 2 ) x. ( 1 - S ) ) e. RR'), gap],
             'cxplead', '( %s ^c ( %s + ( 1 / ; ; 2 0 0 ) ) ) <_ %s' % (E, XP_, E92))
    g922 = st([ca, g92], 'eqbrtrrd', '( %s x. %s ) <_ %s' % (EP, E200, E92))
    # assemble
    epr = st([st([erp, xr_], 'rpcxpcld', '%s e. RR+' % EP)], 'rpred', '%s e. RR' % EP)
    ep0 = st([st([erp, xr_], 'rpcxpcld', '%s e. RR+' % EP)], 'rpge0d', '0 <_ %s' % EP)
    HE = '( H x. %s )' % EP
    her = st([hr, epr], 'remulcld', '%s e. RR' % HE); he0 = st([hr, epr, h0, ep0], 'mulge0d', '0 <_ %s' % HE)
    a1_ = st([st([ldr, kn], 'reexpcld', '( %s ^ K ) e. RR' % LD), st([w4r, e200r], 'remulcld', '( %s x. %s ) e. RR' % (W4, E200)), her, he0, ldk], 'lemul2ad',
             '( %s x. ( %s ^ K ) ) <_ ( %s x. ( %s x. %s ) )' % (HE, LD, HE, W4, E200))
    HW = '( H x. %s )' % W4
    hwr = st([hr, w4r], 'remulcld', '%s e. RR' % HW); hw0 = st([hr, w4r, h0, w40], 'mulge0d', '0 <_ %s' % HW)
    eq = lineq(w, ante, '( %s x. ( %s x. %s ) )' % (HE, W4, E200), '( %s x. ( %s x. %s ) )' % (HW, EP, E200), products=True, leaves={'H': hr, EP: epr, W4: w4r, E200: e200r})
    e92r = st([st([erp, st([litr(w, ante, '( 9 / 2 )'), st([st([], '1red', '1 e. RR'), sr], 'resubcld', '( 1 - S ) e. RR')], 'remulcld', '( ( 9 / 2 ) x. ( 1 - S ) ) e. RR')],
                  'rpcxpcld', '%s e. RR+' % E92)], 'rpred', '%s e. RR' % E92)
    a2_ = st([st([epr, e200r], 'remulcld', '( %s x. %s ) e. RR' % (EP, E200)), e92r, hwr, hw0, g922], 'lemul2ad', '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (HW, EP, E200, HW, E92))
    t1 = st([zle, a1_], 'letrd', 'Z <_ ( %s x. ( %s x. %s ) )' % (HE, W4, E200))
    t2_ = st([t1, eq], 'breqtrd', 'Z <_ ( %s x. ( %s x. %s ) )' % (HW, EP, E200))
    w.qed([t2_, a2_], 'letrd', STATEMENTS['zdthmh'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
