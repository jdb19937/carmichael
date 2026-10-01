"""Sortie Z5c, section P: the pole term, Lemma 4.3 (corrected form) and Proposition 4.4 (Detector.lean 1448-1753,
Detection.lean norm_Epole_le', sum_totient_div_sq_le_P1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5clib import *
from cl import Closure, lift, split_imp
import lin
import num

EPB0 = lambda u, v: ('( s e. CC |-> if ( ( 1st ` ( 1st ` %s ) ) = ( h e. NN |-> if ( ( h gcd ( 2nd ` ( 1st ` %s ) ) ) = 1 , 1 , 0 ) ) , '
                     '( ( ( ( _G ` ( 1 - s ) ) x. ( ( 2nd ` %s ) ^c ( 1 - s ) ) ) x. ( ( phi ` ( 2nd ` ( 1st ` %s ) ) ) / ( 2nd ` ( 1st ` %s ) ) ) ) x. '
                     'sum_ r e. ( ( 2nd ` ( 1st ` %s ) ) RSet ( 2nd ` %s ) ) ( ( 1 / r ) x. ( ( <. ( 1st ` ( 1st ` %s ) ) , ( 2nd ` ( 1st ` %s ) ) >. Mr '
                     '<. ( 1st ` ( 1st ` %s ) ) , r >. ) ` 1 ) ) ) , 0 ) )' % (v, v, u, v, v, v, v, u, u, v))


def z5epval():
    w = W('z5epval', "Value of the pole term (Lean Epole, Detector.lean 1453): ( ( <. A , B , X >. EPole <. C , N , R >. ) ` S ) is "
                     "Gamma ( 1 - S ) X ^ ( 1 - S ) ( phi ( N ) / N ) sum_ ( r e. RSet ) r ^ -1 M_r ( 1 , C ) if C is the principal "
                     "character mod N, else 0.")
    ante = split_imp(STATEMENTS['z5epval'])[0]
    st = mkst(w, ante)
    h1 = st([], 'simpll', '( A e. U /\\ B e. V /\\ X e. W )'); h2 = st([], 'simplr', '( C e. T /\\ N e. Y /\\ R e. Z )')
    sa = st([h1], 'simp1d', 'A e. U'); sb = st([h1], 'simp2d', 'B e. V'); sx = st([h1], 'simp3d', 'X e. W')
    sc = st([h2], 'simp1d', 'C e. T'); sn = st([h2], 'simp2d', 'N e. Y'); sr = st([h2], 'simp3d', 'R e. Z')
    OU = '<. A , B , X >.'; OV = '<. C , N , R >.'
    both = st([a1(w, ante, w.s([], 'otex', '%s e. _V' % OU), '%s e. _V' % OU), a1(w, ante, w.s([], 'otex', '%s e. _V' % OV), '%s e. _V' % OV)], 'jca',
              '( %s e. _V /\\ %s e. _V )' % (OU, OV))
    mk = w.s([w.s([], 'cnex', 'CC e. _V')], 'mptex', '%s e. _V' % EPB0(OU, OV))
    e1 = cg(w, EPB0('u', 'v'), 'u', OU)
    e2 = cg(w, EPB0(OU, 'v'), 'v', OV)
    df = w.s([], 'df-epole', 'EPole = ( u e. _V , v e. _V |-> %s )' % EPB0('u', 'v'))
    ov = w.s([e1, e2, df, mk], 'ovmpo', '( ( %s e. _V /\\ %s e. _V ) -> ( %s EPole %s ) = %s )' % (OU, OV, OU, OV, EPB0(OU, OV)))
    pv = st([both, ov], 'syl', '( %s EPole %s ) = %s' % (OU, OV, EPB0(OU, OV)))
    body = EPB0(OU, OV)[len('( s e. CC |-> '):-2]
    bS = body.replace('( 1 - s )', '( 1 - S )')
    from cl import split_sep
    inner = bS[len('if ( '):-2]
    cond, TB, FB = split_sep(inner.split(), (',',))
    exs = a1(w, ante, w.s([w.s([], 'ovex', '%s e. _V' % TB), w.s([], 'c0ex', '0 e. _V')], 'ifex', '%s e. _V' % bS), '%s e. _V' % bS)
    val, v = mpv(w, ante, 's', 'CC', body, 'S', st([], 'simpr', 'S e. CC'), exs=exs)
    r = {}
    r['( 1st ` ( 1st ` %s ) )' % OU] = ('A', st([sa, sb, sx, w.inst('ot1stg')], 'syl3anc', '( 1st ` ( 1st ` %s ) ) = A' % OU))
    r['( 2nd ` ( 1st ` %s ) )' % OU] = ('B', st([sa, sb, sx, w.inst('ot2ndg')], 'syl3anc', '( 2nd ` ( 1st ` %s ) ) = B' % OU))
    r['( 2nd ` %s )' % OU] = ('X', st([sx, w.inst('ot3rdg')], 'syl', '( 2nd ` %s ) = X' % OU))
    r['( 1st ` ( 1st ` %s ) )' % OV] = ('C', st([sc, sn, sr, w.inst('ot1stg')], 'syl3anc', '( 1st ` ( 1st ` %s ) ) = C' % OV))
    r['( 2nd ` ( 1st ` %s ) )' % OV] = ('N', st([sc, sn, sr, w.inst('ot2ndg')], 'syl3anc', '( 2nd ` ( 1st ` %s ) ) = N' % OV))
    r['( 2nd ` %s )' % OV] = ('R', st([sr, w.inst('ot3rdg')], 'syl', '( 2nd ` %s ) = R' % OV))
    rw, new = w.rewrite(v, r, ante)
    assert new == 'if ( C = %s , %s , 0 )' % (PRIN('N', 'h'), EPB()), new
    w.qed([st([st([pv], 'fveq1d', '( ( %s EPole %s ) ` S ) = ( %s ` S )' % (OU, OV, EPB0(OU, OV))), val], 'eqtrd', '( ( %s EPole %s ) ` S ) = %s' % (OU, OV, v)), rw],
          'eqtrd', STATEMENTS['z5epval'])
    return w


def z5ep0():
    w = W('z5ep0', "Lean Epole_eq_zero: the pole term vanishes for a non-principal character.")
    ante = split_imp(STATEMENTS['z5ep0'])[0]
    st = mkst(w, ante)
    PH = PRIN('N', 'h')
    v = st([st([], 'simpl', '( %s /\\ S e. CC )' % SETS6), w.inst('z5epval')], 'syl', '%s = if ( C = %s , %s , 0 )' % (EPV(), PH, EPB()))
    f = st([st([st([], 'simpr', 'C =/= %s' % PH)], 'neneqd', '-. C = %s' % PH)], 'iffalsed', 'if ( C = %s , %s , 0 ) = 0' % (PH, EPB()))
    w.qed([v, f], 'eqtrd', STATEMENTS['z5ep0'])
    return w


def z5dlb():
    w = W('z5dlb', "Blueprint Proposition 4.4's final assembly (Lean detector_lower_bound, the triangle inequality after hEp and hdet): "
                   "if | F + e ^ ( - 1 / X ) P ( 1 ) - E | <_ P ( 1 ) / 8 (Lemmas 4.1-4.2) and | E | <_ P ( 1 ) / 8 (Lemma 4.3), then "
                   "| F | >_ P ( 1 ) / 2 >_ ( 1 / 400 ) ( phi ( N ) / N ) log D, since e ^ ( - 1 / X ) >_ 3 / 4 for X = D ^ ( 6 / 5 ) >_ 4.")
    import num
    ante = split_imp(STATEMENTS['z5dlb'])[0]
    st = mkst(w, ante)
    hd = st([], 'simpll', '( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) )'); nn = st([], 'simplr', 'N e. NN')
    fc = st([], 'simprll', 'F e. CC'); ec = st([], 'simprlr', 'E e. CC')
    P = P1D; X = XPD
    Q = '( ( phi ` N ) / N )'; L = '( log ` D )'
    hp1 = st([], 'simprrl', '( ( ( 1 / ; ; 2 0 0 ) x. %s ) x. %s ) <_ %s' % (Q, L, P))
    EX = '( exp ` ( -u 1 / %s ) )' % X
    c = '( %s x. %s )' % (EX, P)
    G = '( ( F + %s ) - E )' % c
    hdet = st([], 'simprrr', '( ( abs ` %s ) <_ ( %s / 8 ) /\\ ( abs ` E ) <_ ( %s / 8 ) )' % (G, P, P))
    hg = st([hdet], 'simpld', '( abs ` %s ) <_ ( %s / 8 )' % (G, P))
    he = st([hdet], 'simprd', '( abs ` E ) <_ ( %s / 8 )' % P)
    df = dfacts(w, ante, hd)
    dr, d1, l200, drp, lr = df['dr'], df['d1'], df['l200'], df['drp'], df['lr']
    # D >_ 4
    r200 = num.rp(w, '; ; 2 0 0')
    e201 = w.s([r200, w.inst('efgt1p')], 'ax-mp', '( 1 + ; ; 2 0 0 ) < ( exp ` ; ; 2 0 0 )')
    e201d = w.s([e201], 'a1i', '( %s -> ( 1 + ; ; 2 0 0 ) < ( exp ` ; ; 2 0 0 ) )' % ante)
    c200 = litr(w, ante, '; ; 2 0 0')
    el = st([l200, st([c200, lr, w.inst('efle')], 'syl2anc', '( ; ; 2 0 0 <_ %s <-> ( exp ` ; ; 2 0 0 ) <_ ( exp ` %s ) )' % (L, L))], 'mpbid',
            '( exp ` ; ; 2 0 0 ) <_ ( exp ` %s )' % L)
    el2 = st([el, st([drp, w.inst('reeflog')], 'syl', '( exp ` %s ) = D' % L)], 'breqtrd', '( exp ` ; ; 2 0 0 ) <_ D')
    e2r = st([c200], 'reefcld', '( exp ` ; ; 2 0 0 ) e. RR')
    d4 = lin.linarith(w, ante, [e201d, el2], '4 <_ D', leaves={'( exp ` ; ; 2 0 0 )': ('RR', e2r), 'D': ('RR', dr)}, atoms=['( exp ` ; ; 2 0 0 )'])
    # X >_ 4
    d1le = lin.linarith(w, ante, [d1], '1 <_ D', leaves={'D': ('RR', dr)})
    cx = st([st([dr, d1le], 'jca', '( D e. RR /\\ 1 <_ D )'), st([st([], '1red', '1 e. RR'), litr(w, ante, '( 6 / 5 )')], 'jca', '( 1 e. RR /\\ ( 6 / 5 ) e. RR )'),
             litle(w, ante, '1', '( 6 / 5 )'), w.inst('cxplea')], 'syl3anc', '( D ^c 1 ) <_ %s' % X)
    cx1 = st([cx, st([df['dc'], w.inst('cxp1')], 'syl', '( D ^c 1 ) = D')], 'eqbrtrrd', 'D <_ %s' % X)
    xrp = st([drp, litr(w, ante, '( 6 / 5 )')], 'rpcxpcld', '%s e. RR+' % X)
    xr = st([xrp], 'rpred', '%s e. RR' % X)
    x4 = st([litr(w, ante, '4'), dr, xr, d4, cx1], 'letrd', '4 <_ %s' % X)
    # e ^ ( - 1 / X ) >_ 3 / 4
    rp4 = w.s([num.rp(w, '4')], 'a1i', '( %s -> 4 e. RR+ )' % ante)
    ix = st([rp4, xrp, st([], '1red', '1 e. RR'), w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % ante), x4], 'lediv2ad', '( 1 / %s ) <_ ( 1 / 4 )' % X)
    ixr = st([xrp], 'rpreccld', '( 1 / %s ) e. RR+' % X)
    bv = st([st([ixr], 'rpred', '( 1 / %s ) e. RR' % X), st([ixr], 'rpge0d', '0 <_ ( 1 / %s )' % X), w.inst('bvexpl1')], 'syl2anc',
            '( 1 - ( exp ` -u ( 1 / %s ) ) ) <_ ( 1 / %s )' % (X, X))
    xc = st([xrp], 'rpcnd', '%s e. CC' % X); x0 = st([xrp], 'rpne0d', '%s =/= 0' % X)
    dn_ = st([st([], '1cnd', '1 e. CC'), xc, x0], 'divnegd', '-u ( 1 / %s ) = ( -u 1 / %s )' % (X, X))
    eeq = st([dn_], 'fveq2d', '( exp ` -u ( 1 / %s ) ) = %s' % (X, EX))
    bv2 = st([st([st([eeq], 'oveq2d', '( 1 - ( exp ` -u ( 1 / %s ) ) ) = ( 1 - %s )' % (X, EX))], 'eqcomd', '( 1 - %s ) = ( 1 - ( exp ` -u ( 1 / %s ) ) )' % (EX, X)), bv],
             'eqbrtrd', '( 1 - %s ) <_ ( 1 / %s )' % (EX, X))
    exr = st([st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), xrp], 'rerpdivcld', '( -u 1 / %s ) e. RR' % X)], 'reefcld', '%s e. RR' % EX)
    e34 = lin.linarith(w, ante, [bv2, ix], '( 3 / 4 ) <_ %s' % EX, leaves={EX: ('RR', exr), '( 1 / %s )' % X: ('RR', st([ixr], 'rpred', '( 1 / %s ) e. RR' % X))},
                       atoms=[EX, '( 1 / %s )' % X])
    # P ( 1 ) >_ 0 and c = e P
    rpv = st([drp, litr(w, ante, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '( D ^c ( 1 / ; ; 1 0 0 ) ) e. RR+')
    p0 = st([nn, rpv, w.inst('z5p1ge0')], 'syl2anc', '0 <_ %s' % P)
    rsf = st([st([nn, st([rpv], 'rpred', '( D ^c ( 1 / ; ; 1 0 0 ) ) e. RR'), w.inst('z5rsetfi')], 'syl2anc',
                 '( ( N RSet ( D ^c ( 1 / ; ; 1 0 0 ) ) ) C_ ( 1 ... ( |_ ` ( D ^c ( 1 / ; ; 1 0 0 ) ) ) ) /\\ ( N RSet ( D ^c ( 1 / ; ; 1 0 0 ) ) ) e. Fin )')], 'simprd',
              '( N RSet ( D ^c ( 1 / ; ; 1 0 0 ) ) ) e. Fin')
    RS = '( N RSet ( D ^c ( 1 / ; ; 1 0 0 ) ) )'
    rss = st([st([nn, st([rpv], 'rpred', '( D ^c ( 1 / ; ; 1 0 0 ) ) e. RR'), w.inst('z5rsetfi')], 'syl2anc',
                 '( %s C_ ( 1 ... ( |_ ` ( D ^c ( 1 / ; ; 1 0 0 ) ) ) ) /\\ %s e. Fin )' % (RS, RS))], 'simpld', '%s C_ ( 1 ... ( |_ ` ( D ^c ( 1 / ; ; 1 0 0 ) ) ) )' % RS)
    ar = '( %s /\\ j e. %s )' % (ante, RS)
    rnn = w.s([w.s([w.s([rss], 'adantr', '( %s -> %s C_ ( 1 ... ( |_ ` ( D ^c ( 1 / ; ; 1 0 0 ) ) ) ) )' % (ar, RS)), w.s([], 'simpr', '( %s -> j e. %s )' % (ar, RS))], 'sseldd',
                   '( %s -> j e. ( 1 ... ( |_ ` ( D ^c ( 1 / ; ; 1 0 0 ) ) ) ) )' % ar), w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % ar)
    prj = st([rsf, w.s([rnn], 'nnrecred', '( %s -> ( 1 / j ) e. RR )' % ar)], 'fsumrecl', 'sum_ j e. %s ( 1 / j ) e. RR' % RS)
    cbs = w.s([w.s([], 'oveq2', '( j = r -> ( 1 / j ) = ( 1 / r ) )')], 'cbvsumv', 'sum_ j e. %s ( 1 / j ) = %s' % (RS, P))
    pr = st([w.s([cbs], 'a1i', '( %s -> sum_ j e. %s ( 1 / j ) = %s )' % (ante, RS, P)), prj], 'eqeltrrd', '%s e. RR' % P)
    ex0 = st([st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), xrp], 'rerpdivcld', '( -u 1 / %s ) e. RR' % X), w.inst('efgt0')], 'syl', '0 < %s' % EX)
    cr = st([exr, pr], 'remulcld', '%s e. RR' % c)
    c0 = st([exr, pr, st([ex0], 'ltled', '0 <_ %s' % EX), p0], 'mulge0d', '0 <_ %s' % c)
    c34 = st([litr(w, ante, '( 3 / 4 )'), exr, pr, p0, e34], 'lemul1ad', '( ( 3 / 4 ) x. %s ) <_ %s' % (P, c))
    ac = st([cr, c0], 'absidd', '( abs ` %s ) = %s' % (c, c))
    cle = st([cr, st([ac], 'eqcomd', '%s = ( abs ` %s )' % (c, c))], 'eqled', '%s <_ ( abs ` %s )' % (c, c))
    cc_ = st([cr], 'recnd', '%s e. CC' % c)
    ce = st([cc_, ec], 'subcld', '( %s - E ) e. CC' % c)
    ga = st([fc, cc_, ec], 'addsubassd', '%s = ( F + ( %s - E ) )' % (G, c))
    gb = st([fc, ce], 'pncan2d', '( ( F + ( %s - E ) ) - F ) = ( %s - E )' % (c, c))
    gf = st([st([ga], 'oveq1d', '( %s - F ) = ( ( F + ( %s - E ) ) - F )' % (G, c)), gb], 'eqtrd', '( %s - F ) = ( %s - E )' % (G, c))
    gfe = st([st([gf], 'oveq1d', '( ( %s - F ) + E ) = ( ( %s - E ) + E )' % (G, c)), st([cc_, ec], 'npcand', '( ( %s - E ) + E ) = %s' % (c, c))], 'eqtrd',
             '( ( %s - F ) + E ) = %s' % (G, c))
    gc = st([st([fc, cc_], 'addcld', '( F + %s ) e. CC' % c), ec], 'subcld', '%s e. CC' % G)
    gfc = st([gc, fc], 'subcld', '( %s - F ) e. CC' % G)
    t1 = st([gfc, ec], 'abstrid', '( abs ` ( ( %s - F ) + E ) ) <_ ( ( abs ` ( %s - F ) ) + ( abs ` E ) )' % (G, G))
    t1b = st([st([gfe], 'fveq2d', '( abs ` ( ( %s - F ) + E ) ) = ( abs ` %s )' % (G, c)), t1], 'eqbrtrrd', '( abs ` %s ) <_ ( ( abs ` ( %s - F ) ) + ( abs ` E ) )' % (c, G))
    t2 = st([gc, fc], 'abs2dif2d', '( abs ` ( %s - F ) ) <_ ( ( abs ` %s ) + ( abs ` F ) )' % (G, G))
    phn = st([nn, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')
    qr = st([st([phn], 'nnred', '( phi ` N ) e. RR'), st([nn], 'nnrpd', 'N e. RR+')], 'rerpdivcld', '%s e. RR' % Q)
    QL = '( %s x. %s )' % (Q, L)
    qc = st([qr], 'recnd', '%s e. CC' % Q); lc = st([lr], 'recnd', '%s e. CC' % L)
    k2 = litr(w, ante, '( 1 / ; ; 2 0 0 )'); k4 = litr(w, ante, '( 1 / ; ; 4 0 0 )')
    m2 = st([st([k2], 'recnd', '( 1 / ; ; 2 0 0 ) e. CC'), qc, lc], 'mulassd', '( ( ( 1 / ; ; 2 0 0 ) x. %s ) x. %s ) = ( ( 1 / ; ; 2 0 0 ) x. %s )' % (Q, L, QL))
    m4 = st([st([k4], 'recnd', '( 1 / ; ; 4 0 0 ) e. CC'), qc, lc], 'mulassd', '( ( ( 1 / ; ; 4 0 0 ) x. %s ) x. %s ) = ( ( 1 / ; ; 4 0 0 ) x. %s )' % (Q, L, QL))
    hp1b = st([st([m2], 'eqcomd', '( ( 1 / ; ; 2 0 0 ) x. %s ) = ( ( ( 1 / ; ; 2 0 0 ) x. %s ) x. %s )' % (QL, Q, L)), hp1], 'eqbrtrd', '( ( 1 / ; ; 2 0 0 ) x. %s ) <_ %s' % (QL, P))
    c3c = st([st([litr(w, ante, '( 3 / 4 )'), pr], 'remulcld', '( ( 3 / 4 ) x. %s ) e. RR' % P), cr, st([cc_], 'abscld', '( abs ` %s ) e. RR' % c), c34, cle], 'letrd',
             '( ( 3 / 4 ) x. %s ) <_ ( abs ` %s )' % (P, c))
    lv = {P: ('RR', pr), '( abs ` %s )' % c: ('RR', st([cc_], 'abscld', '( abs ` %s ) e. RR' % c)),
          '( abs ` ( %s - F ) )' % G: ('RR', st([gfc], 'abscld', '( abs ` ( %s - F ) ) e. RR' % G)), '( abs ` E )': ('RR', st([ec], 'abscld', '( abs ` E ) e. RR')),
          '( abs ` %s )' % G: ('RR', st([gc], 'abscld', '( abs ` %s ) e. RR' % G)), '( abs ` F )': ('RR', st([fc], 'abscld', '( abs ` F ) e. RR')),
          QL: ('RR', st([qr, lr], 'remulcld', '%s e. RR' % QL))}
    q = lin.linarith(w, ante, [t1b, t2, hg, he, c3c, hp1b], '( ( 1 / ; ; 4 0 0 ) x. %s ) <_ ( abs ` F )' % QL, leaves=lv, atoms=list(lv.keys()))
    q2 = st([m4, q], 'eqbrtrd', '( ( ( 1 / ; ; 4 0 0 ) x. %s ) x. %s ) <_ ( abs ` F )' % (Q, L))
    last = w.lines.pop()
    w.lines.append('qed:' + last.split(':', 1)[1])
    return w


def z5prin():
    w = W('z5prin', "The principal character mod N as a function on NN, n |-> if ( ( n , N ) = 1 , 1 , 0 ) (Lean (1 : DirichletCharacter CC N), "
                    "MulChar.one_apply): complex, of absolute value at most 1, and 1 at the primes coprime to N.")
    ante = 'N e. NN'
    st = mkst(w, ante)
    IFn = lambda v: 'if ( ( %s gcd N ) = 1 , 1 , 0 )' % v
    an = '( %s /\\ n e. NN )' % ante
    ifc = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % an), w.s([], '0cnd', '( %s -> 0 e. CC )' % an)], 'ifcld', '( %s -> %s e. CC )' % (an, IFn('n')))
    pf = st([ifc], 'fmpttd', '%s : NN --> CC' % PRN)
    aj = '( %s /\\ j e. NN )' % ante
    sj = mkst(w, aj)
    jv, _ = mpv(w, aj, 'n', 'NN', IFn('n'), 'j', sj([], 'simpr', 'j e. NN'))
    AB1 = '( abs ` 1 ) <_ 1'; AB0 = '( abs ` 0 ) <_ 1'
    t1 = w.s([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1'), w.s([], '1le1', '1 <_ 1')], 'eqbrtri', AB1)], 'a1i', '( ( %s /\\ ( j gcd N ) = 1 ) -> %s )' % (aj, AB1))
    t0 = w.s([w.s([w.s([], 'abs0', '( abs ` 0 ) = 0'), w.s([], '0le1', '0 <_ 1')], 'eqbrtri', AB0)], 'a1i', '( ( %s /\\ -. ( j gcd N ) = 1 ) -> %s )' % (aj, AB0))
    h1 = w.s([w.s([], 'fveq2', '( 1 = %s -> ( abs ` 1 ) = ( abs ` %s ) )' % (IFn('j'), IFn('j')))], 'breq1d', '( 1 = %s -> ( %s <-> ( abs ` %s ) <_ 1 ) )' % (IFn('j'), AB1, IFn('j')))
    h0 = w.s([w.s([], 'fveq2', '( 0 = %s -> ( abs ` 0 ) = ( abs ` %s ) )' % (IFn('j'), IFn('j')))], 'breq1d', '( 0 = %s -> ( %s <-> ( abs ` %s ) <_ 1 ) )' % (IFn('j'), AB0, IFn('j')))
    ib = w.s([h1, h0, t1, t0], 'ifbothda', '( %s -> ( abs ` %s ) <_ 1 )' % (aj, IFn('j')))
    jb = sj([sj([jv], 'fveq2d', '( abs ` ( %s ` j ) ) = ( abs ` %s )' % (PRN, IFn('j'))), ib], 'eqbrtrd', '( abs ` ( %s ` j ) ) <_ 1' % PRN)
    cb = st([jb], 'ralrimiva', 'A. j e. NN ( abs ` ( %s ` j ) ) <_ 1' % PRN)
    ac = '( ( %s /\\ c e. Prime ) /\\ ( c gcd N ) = 1 )' % ante
    sc = mkst(w, ac)
    cn = sy(w, ac, sc([], 'simplr', 'c e. Prime'), 'prmnn', 'c e. NN')
    cv, _ = mpv(w, ac, 'n', 'NN', IFn('n'), 'c', cn)
    c1 = sc([cv, sc([sc([], 'simpr', '( c gcd N ) = 1')], 'iftrued', '%s = 1' % IFn('c'))], 'eqtrd', '( %s ` c ) = 1' % PRN)
    hp = st([w.s([c1], 'ex', '( ( %s /\\ c e. Prime ) -> ( ( c gcd N ) = 1 -> ( %s ` c ) = 1 ) )' % (ante, PRN))], 'ralrimiva',
            'A. c e. Prime ( ( c gcd N ) = 1 -> ( %s ` c ) = 1 )' % PRN)
    w.qed([st([pf, cb], 'jca', '( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 )' % (PRN, PRN)), hp], 'jca', STATEMENTS['z5prin'])
    return w


def z5phip1():
    w = W('z5phip1', "Lean sum_totient_div_sq_le_P1 (Detection.lean, the true replacement of the false I9(c)): "
                     "sum_ ( r e. RSet ) phi ( r ) / r ^ 2 <_ sum_ ( r e. RSet ) 1 / r = P ( 1 ), from phi ( r ) <_ r.")
    ante = split_imp(STATEMENTS['z5phip1'])[0]
    st = mkst(w, ante)
    nv = st([], 'simpl', 'N e. V'); yr = st([], 'simpr', 'Y e. RR')
    RS = '( N RSet Y )'
    rf = st([nv, yr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` Y ) ) /\\ %s e. Fin )' % (RS, RS))
    a = '( %s /\\ r e. %s )' % (ante, RS)
    sa = mkst(w, a)
    rn = sa([sa([lift(w, st([rf], 'simpld', '%s C_ ( 1 ... ( |_ ` Y ) )' % RS), a), sa([], 'simpr', 'r e. %s' % RS)], 'sseldd', 'r e. ( 1 ... ( |_ ` Y ) )'),
             w.inst('elfznn')], 'syl', 'r e. NN')
    rr = sa([rn], 'nnred', 'r e. RR'); rc = sa([rn], 'nncnd', 'r e. CC'); r0 = sa([rn], 'nnne0d', 'r =/= 0')
    r2 = sa([sa([rn], 'nnrpd', 'r e. RR+'), w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % a)], 'rpexpcld', '( r ^ 2 ) e. RR+')
    phr = sa([sa([rn, w.inst('phicl')], 'syl', '( phi ` r ) e. NN')], 'nnred', '( phi ` r ) e. RR')
    le = sa([phr, rr, r2, sa([rn, w.inst('z5phile')], 'syl', '( phi ` r ) <_ r')], 'lediv1dd', '( ( phi ` r ) / ( r ^ 2 ) ) <_ ( r / ( r ^ 2 ) )')
    e1 = sa([sa([rc], 'sqvald', '( r ^ 2 ) = ( r x. r )')], 'oveq2d', '( r / ( r ^ 2 ) ) = ( r / ( r x. r ) )')
    e2 = sa([sa([sa([rc, rc, rc, r0, r0], 'divdiv1d', '( ( r / r ) / r ) = ( r / ( r x. r ) )')], 'eqcomd', '( r / ( r x. r ) ) = ( ( r / r ) / r )'),
             sa([sa([rc, r0], 'dividd', '( r / r ) = 1')], 'oveq1d', '( ( r / r ) / r ) = ( 1 / r )')], 'eqtrd', '( r / ( r x. r ) ) = ( 1 / r )')
    tb = sa([le, sa([e1, e2], 'eqtrd', '( r / ( r ^ 2 ) ) = ( 1 / r )')], 'breqtrd', '( ( phi ` r ) / ( r ^ 2 ) ) <_ ( 1 / r )')
    w.qed([st([rf], 'simprd', '%s e. Fin' % RS), sa([phr, r2], 'rerpdivcld', '( ( phi ` r ) / ( r ^ 2 ) ) e. RR'), sa([rn], 'nnrecred', '( 1 / r ) e. RR'), tb], 'fsumle',
          STATEMENTS['z5phip1'])
    return w


def z5mrsp():
    w = W('z5mrsp', "The M_r sum of Lemma 4.3 (Lean hMr of norm_Epole_le'): | sum_ ( r e. RSet ) r ^ -1 M_r ( 1 , chi_0 ) | <_ P ( 1 ) ( 1 + log z2 ) "
                    "for the principal character (z5mr1sum, z5phip1).")
    ante = split_imp(STATEMENTS['z5mrsp'])[0]
    st = mkst(w, ante)
    hab = st([], 'simpll', HAB0); b1 = st([], 'simplr', '1 <_ B'); nn = st([], 'simprl', 'N e. NN'); yr = st([], 'simprr', 'Y e. RR')
    import z5c_f as F_
    Ar, A0, Br, AB_, abr = F_.habfacts(w, ante, hab)
    pr = st([nn, w.inst('z5prin')], 'syl', cns('z5prin'))
    pcfn = st([pr], 'simpld', '( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 )' % (PRN, PRN))
    phpn = st([pr], 'simprd', 'A. c e. Prime ( ( c gcd N ) = 1 -> ( %s ` c ) = 1 )' % PRN)
    pf = st([pcfn], 'simpld', '%s : NN --> CC' % PRN)
    RS = '( N RSet Y )'
    rf = st([nn, yr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` Y ) ) /\\ %s e. Fin )' % (RS, RS))
    rsf = st([rf], 'simprd', '%s e. Fin' % RS)
    a = '( %s /\\ r e. %s )' % (ante, RS)
    sa = mkst(w, a)
    rn = sa([sa([lift(w, st([rf], 'simpld', '%s C_ ( 1 ... ( |_ ` Y ) )' % RS), a), sa([], 'simpr', 'r e. %s' % RS)], 'sseldd', 'r e. ( 1 ... ( |_ ` Y ) )'),
             w.inst('elfznn')], 'syl', 'r e. NN')
    M = MR1P('r')
    mc = sa([lift(w, hab, a), rn, lift(w, pf, a), sa([], '1cnd', '1 e. CC'), w.inst('z5mrcl')], 'syl22anc', '%s e. CC' % M)
    rrc = sa([sa([rn], 'nncnd', 'r e. CC'), sa([rn], 'nnne0d', 'r =/= 0')], 'reccld', '( 1 / r ) e. CC')
    tc = sa([rrc, mc], 'mulcld', '( ( 1 / r ) x. %s ) e. CC' % M)
    fa = st([rsf, tc], 'fsumabs', '( abs ` sum_ r e. %s ( ( 1 / r ) x. %s ) ) <_ sum_ r e. %s ( abs ` ( ( 1 / r ) x. %s ) )' % (RS, M, RS, M))
    rir = sa([rn], 'nnrecred', '( 1 / r ) e. RR')
    ri0 = sa([sa([sa([rn], 'nnrpd', 'r e. RR+')], 'rpreccld', '( 1 / r ) e. RR+')], 'rpge0d', '0 <_ ( 1 / r )')
    ae = sa([sa([rrc, mc], 'absmuld', '( abs ` ( ( 1 / r ) x. %s ) ) = ( ( abs ` ( 1 / r ) ) x. ( abs ` %s ) )' % (M, M)),
             sa([sa([rir, ri0], 'absidd', '( abs ` ( 1 / r ) ) = ( 1 / r )')], 'oveq1d', '( ( abs ` ( 1 / r ) ) x. ( abs ` %s ) ) = ( ( 1 / r ) x. ( abs ` %s ) )' % (M, M))],
            'eqtrd', '( abs ` ( ( 1 / r ) x. %s ) ) = ( ( 1 / r ) x. ( abs ` %s ) )' % (M, M))
    se = st([ae], 'sumeq2dv', 'sum_ r e. %s ( abs ` ( ( 1 / r ) x. %s ) ) = sum_ r e. %s ( ( 1 / r ) x. ( abs ` %s ) )' % (RS, M, RS, M))
    L = '( 1 + ( log ` B ) )'
    ms = st([st([hab, b1], 'jca', '( %s /\\ 1 <_ B )' % HAB0), st([st([nn, yr], 'jca', '( N e. NN /\\ Y e. RR )'), st([pcfn, phpn], 'jca',
             '( ( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 ) /\\ A. c e. Prime ( ( c gcd N ) = 1 -> ( %s ` c ) = 1 ) )' % (PRN, PRN, PRN))], 'jca',
                                                          '( ( N e. NN /\\ Y e. RR ) /\\ ( ( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 ) /\\ '
                                                          'A. c e. Prime ( ( c gcd N ) = 1 -> ( %s ` c ) = 1 ) ) )' % (PRN, PRN, PRN)),
             w.inst('z5mr1sum')], 'syl2anc', 'sum_ r e. %s ( ( 1 / r ) x. ( abs ` %s ) ) <_ ( sum_ r e. %s ( ( phi ` r ) / ( r ^ 2 ) ) x. %s )' % (RS, M, RS, L))
    ph = st([nn, yr, w.inst('z5phip1')], 'syl2anc', 'sum_ r e. %s ( ( phi ` r ) / ( r ^ 2 ) ) <_ sum_ r e. %s ( 1 / r )' % (RS, RS))
    brp = st([Br, lin.linarith(w, ante, [b1], '0 < B', leaves={'B': ('RR', Br)})], 'elrpd', 'B e. RR+')
    lgr = st([brp], 'relogcld', '( log ` B ) e. RR')
    lg0 = st([Br, b1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` B )')
    lr = st([st([], '1red', '1 e. RR'), lgr], 'readdcld', '%s e. RR' % L)
    l0 = lin.linarith(w, ante, [lg0], '0 <_ %s' % L, leaves={'( log ` B )': ('RR', lgr)}, atoms=['( log ` B )'])
    r2rp = sa([sa([rn], 'nnrpd', 'r e. RR+'), w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % a)], 'rpexpcld', '( r ^ 2 ) e. RR+')
    Sphi = 'sum_ r e. %s ( ( phi ` r ) / ( r ^ 2 ) )' % RS; S1 = 'sum_ r e. %s ( 1 / r )' % RS
    sphr = st([rsf, sa([sa([sa([rn, w.inst('phicl')], 'syl', '( phi ` r ) e. NN')], 'nnred', '( phi ` r ) e. RR'), r2rp], 'rerpdivcld', '( ( phi ` r ) / ( r ^ 2 ) ) e. RR')],
              'fsumrecl', '%s e. RR' % Sphi)
    s1r = st([rsf, rir], 'fsumrecl', '%s e. RR' % S1)
    lm = st([sphr, s1r, lr, l0, ph], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (Sphi, L, S1, L))
    SA = 'sum_ r e. %s ( ( 1 / r ) x. ( abs ` %s ) )' % (RS, M)
    ABS = '( abs ` sum_ r e. %s ( ( 1 / r ) x. %s ) )' % (RS, M)
    absr = st([st([rsf, tc], 'fsumcl', 'sum_ r e. %s ( ( 1 / r ) x. %s ) e. CC' % (RS, M))], 'abscld', '%s e. RR' % ABS)
    sar = st([rsf, sa([rir, sa([mc], 'abscld', '( abs ` %s ) e. RR' % M)], 'remulcld', '( ( 1 / r ) x. ( abs ` %s ) ) e. RR' % M)], 'fsumrecl', '%s e. RR' % SA)
    c1 = st([fa, se], 'breqtrd', '%s <_ %s' % (ABS, SA))
    c2 = st([absr, sar, st([sphr, lr], 'remulcld', '( %s x. %s ) e. RR' % (Sphi, L)), c1, ms], 'letrd', '%s <_ ( %s x. %s )' % (ABS, Sphi, L))
    w.qed([absr, st([sphr, lr], 'remulcld', '( %s x. %s ) e. RR' % (Sphi, L)), st([s1r, lr], 'remulcld', '( %s x. %s ) e. RR' % (S1, L)), c2, lm], 'letrd',
          STATEMENTS['z5mrsp'])
    return w


def z5gam1():
    w = W('z5gam1', "Lean hGamma-step of norm_Epole_le: | Gamma ( 1 - S ) | <_ K e ^ -| Im S | from the strip bound at z = 1 - S "
                    "(0 <_ Re ( 1 - S ) <_ 1, | Im ( 1 - S ) | = | Im S |).")
    ante = split_imp(STATEMENTS['z5gam1'])[0]
    st = mkst(w, ante)
    kr = st([], 'simpll', 'K e. RR'); gh = st([], 'simplr', GAMH); sc = st([], 'simprl', 'S e. CC')
    r0 = st([], 'simprrl', '( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 )'); ih = st([], 'simprrr', '( 1 / 2 ) <_ ( abs ` ( Im ` S ) )')
    Z = '( 1 - S )'
    zc = st([st([], '1cnd', '1 e. CC'), sc], 'subcld', '%s e. CC' % Z)
    rs = st([st([st([], '1cnd', '1 e. CC'), sc, w.inst('resub')], 'syl2anc', '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` S ) )' % Z),
             w.s([w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'oveq1i', '( ( Re ` 1 ) - ( Re ` S ) ) = ( 1 - ( Re ` S ) )')], 'a1i',
                 '( %s -> ( ( Re ` 1 ) - ( Re ` S ) ) = ( 1 - ( Re ` S ) ) )' % ante)], 'eqtrd', '( Re ` %s ) = ( 1 - ( Re ` S ) )' % Z)
    ims = st([st([st([], '1cnd', '1 e. CC'), sc, w.inst('imsub')], 'syl2anc', '( Im ` %s ) = ( ( Im ` 1 ) - ( Im ` S ) )' % Z),
              w.s([w.s([w.s([], 'im1', '( Im ` 1 ) = 0')], 'oveq1i', '( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) )')], 'a1i',
                  '( %s -> ( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) ) )' % ante)], 'eqtrd', '( Im ` %s ) = ( 0 - ( Im ` S ) )' % Z)
    isc = st([sc], 'imcld', '( Im ` S ) e. RR')
    ims2 = st([ims, w.s([w.s([w.s([], 'df-neg', '-u ( Im ` S ) = ( 0 - ( Im ` S ) )')], 'eqcomi', '( 0 - ( Im ` S ) ) = -u ( Im ` S )')], 'a1i', '( %s -> ( 0 - ( Im ` S ) ) = -u ( Im ` S ) )' % ante)], 'eqtrd', '( Im ` %s ) = -u ( Im ` S )' % Z)
    aim = st([st([ims2], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` -u ( Im ` S ) )' % Z), st([st([isc], 'recnd', '( Im ` S ) e. CC')], 'absnegd',
                                                                                                  '( abs ` -u ( Im ` S ) ) = ( abs ` ( Im ` S ) )')], 'eqtrd',
             '( abs ` ( Im ` %s ) ) = ( abs ` ( Im ` S ) )' % Z)
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    rz0 = st([lin.linarith(w, ante, [st([r0], 'simprd', '( Re ` S ) <_ 1')], '0 <_ ( 1 - ( Re ` S ) )', leaves={'( Re ` S )': ('RR', rsr)}, atoms=['( Re ` S )']),
              st([rs], 'eqcomd', '( 1 - ( Re ` S ) ) = ( Re ` %s )' % Z)], 'breqtrd', '0 <_ ( Re ` %s )' % Z)
    rz1 = st([rs, lin.linarith(w, ante, [st([r0], 'simpld', '0 <_ ( Re ` S )')], '( 1 - ( Re ` S ) ) <_ 1', leaves={'( Re ` S )': ('RR', rsr)}, atoms=['( Re ` S )'])],
             'eqbrtrd', '( Re ` %s ) <_ 1' % Z)
    iz = st([ih, st([aim], 'eqcomd', '( abs ` ( Im ` S ) ) = ( abs ` ( Im ` %s ) )' % Z)], 'breqtrd', '( 1 / 2 ) <_ ( abs ` ( Im ` %s ) )' % Z)
    idz = w.s([], 'id', '( z = %s -> z = %s )' % (Z, Z))
    body = '( ( 0 <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 /\\ ( 1 / 2 ) <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( _G ` z ) ) <_ ( K x. ( exp ` -u ( abs ` ( Im ` z ) ) ) ) )'
    cgz, newb = w.wcongr(body, {'z': Z}, 'z = %s' % Z, {'z': idz})
    gz = st([cgz, gh, zc], 'rspcdva', newb)
    g1 = st([st([rz0, rz1, iz], '3jca', split_imp(newb)[0]), gz], 'mpd', split_imp(newb)[1])
    e = st([st([st([aim], 'negeqd', '-u ( abs ` ( Im ` %s ) ) = -u ( abs ` ( Im ` S ) )' % Z)], 'fveq2d',
                '( exp ` -u ( abs ` ( Im ` %s ) ) ) = ( exp ` -u ( abs ` ( Im ` S ) ) )' % Z)], 'oveq2d',
           '( K x. ( exp ` -u ( abs ` ( Im ` %s ) ) ) ) = ( K x. ( exp ` -u ( abs ` ( Im ` S ) ) ) )' % Z)
    w.qed([g1, e], 'breqtrd', STATEMENTS['z5gam1'])
    return w


def z5xabs():
    w = W('z5xabs', "Lean hXnorm of norm_Epole_le: | X ^ ( 1 - S ) | = X ^ ( 1 - Re S ) <_ X ^ ( 1 - T ) for 1 <_ X and T <_ Re S.")
    ante = split_imp(STATEMENTS['z5xabs'])[0]
    st = mkst(w, ante)
    xr = st([], 'simpll', 'X e. RR'); x1 = st([], 'simplr', '1 <_ X'); tr = st([], 'simprl', 'T e. RR'); sc = st([], 'simprrl', 'S e. CC'); ts = st([], 'simprrr', 'T <_ ( Re ` S )')
    xpos = lin.linarith(w, ante, [x1], '0 < X', leaves={'X': ('RR', xr)})
    xrp = st([xr, xpos], 'elrpd', 'X e. RR+')
    Z = '( 1 - S )'
    zc = st([st([], '1cnd', '1 e. CC'), sc], 'subcld', '%s e. CC' % Z)
    a1_ = st([xrp, zc, w.inst('abscxp')], 'syl2anc', '( abs ` ( X ^c %s ) ) = ( X ^c ( Re ` %s ) )' % (Z, Z))
    rs = st([st([st([], '1cnd', '1 e. CC'), sc, w.inst('resub')], 'syl2anc', '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` S ) )' % Z),
             w.s([w.s([w.s([], 're1', '( Re ` 1 ) = 1')], 'oveq1i', '( ( Re ` 1 ) - ( Re ` S ) ) = ( 1 - ( Re ` S ) )')], 'a1i',
                 '( %s -> ( ( Re ` 1 ) - ( Re ` S ) ) = ( 1 - ( Re ` S ) ) )' % ante)], 'eqtrd', '( Re ` %s ) = ( 1 - ( Re ` S ) )' % Z)
    a2 = st([a1_, st([rs], 'oveq2d', '( X ^c ( Re ` %s ) ) = ( X ^c ( 1 - ( Re ` S ) ) )' % Z)], 'eqtrd', '( abs ` ( X ^c %s ) ) = ( X ^c ( 1 - ( Re ` S ) ) )' % Z)
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    le = lin.linarith(w, ante, [ts], '( 1 - ( Re ` S ) ) <_ ( 1 - T )', leaves={'( Re ` S )': ('RR', rsr), 'T': ('RR', tr)}, atoms=['( Re ` S )'])
    cx = st([st([xr, x1], 'jca', '( X e. RR /\\ 1 <_ X )'), st([st([st([], '1red', '1 e. RR'), rsr], 'resubcld', '( 1 - ( Re ` S ) ) e. RR'),
                                                             st([st([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR')], 'jca',
                                                            '( ( 1 - ( Re ` S ) ) e. RR /\\ ( 1 - T ) e. RR )'), le, w.inst('cxplea')], 'syl3anc',
            '( X ^c ( 1 - ( Re ` S ) ) ) <_ ( X ^c ( 1 - T ) )')
    w.qed([a2, cx], 'eqbrtrd', STATEMENTS['z5xabs'])
    return w


def z5epole():
    w = W('z5epole', "Blueprint Lemma 4.3 in the corrected form of Detection.lean (Lean norm_Epole_le', the statement of Detector.lean's "
                     "norm_Epole_le without its hypotheses hP1 and the false I9(c)): at height | Im S | >_ Lambda_0 the principal pole term "
                     "is at most P ( 1 ) / 8: | Gamma ( 1 - S ) | <_ K e ^ -| Im S |, | X ^ ( 1 - S ) | <_ e ^ ( ( 6 / 5 ) lambda ), "
                     "phi ( N ) / N <_ 1, | sum r ^ -1 M_r ( 1 ) | <_ P ( 1 ) ( 1 + ( 63 / 100 ) log D ), and e ^ | Im S | >_ log D e ^ ( ( 6 / 5 ) lambda ) 3200 e K.")
    ante = split_imp(STATEMENTS['z5epole'])[0]
    st = mkst(w, ante)
    hz = st([], 'simpll', '( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) )'); nn = st([], 'simplr', 'N e. NN')
    tt = st([], 'simprll', '( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) )'); kk = st([], 'simprlr', '( K e. RR /\\ 1 <_ K )')
    rr_ = st([], 'simprr', '( ( %s /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) /\\ %s <_ ( abs ` ( Im ` S ) ) )' % (GAMH, LAM0))
    gh = st([rr_], 'simplld', GAMH); ss = st([rr_], 'simplrd', '( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) )')
    hg = st([rr_], 'simprd', '%s <_ ( abs ` ( Im ` S ) )' % LAM0)
    tr = st([tt], 'simpld', 'T e. RR'); t0 = st([tt], 'simprld', '0 <_ T'); t1 = st([tt], 'simprrd', 'T <_ 1')
    kr = st([kk], 'simpld', 'K e. RR'); k1 = st([kk], 'simprd', '1 <_ K')
    sc = st([ss], 'simpld', 'S e. CC'); tsr = st([ss], 'simprld', 'T <_ ( Re ` S )'); sr1 = st([ss], 'simprrd', '( Re ` S ) <_ 1')
    df = dfacts(w, ante, hz)
    dr, d1, l200, drp, lr = df['dr'], df['d1'], df['l200'], df['drp'], df['lr']
    L = '( log ` D )'
    y = '( abs ` ( Im ` S ) )'
    yr = st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')
    yr = st([yr], 'abscld', '%s e. RR' % y)
    # e and its bounds
    ee = w.s([], 'df-e', '_e = ( exp ` 1 )')
    E1 = '( exp ` 1 )'
    e1r = w.s([ee, w.s([], 'ere', '_e e. RR')], 'eqeltrri', '%s e. RR' % E1)
    ge2 = w.s([w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e'), ee], 'breqtri', '2 < %s' % E1)
    le3 = w.s([ee, w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')], 'eqbrtrri', '%s < 3' % E1)
    e1rd = w.s([e1r], 'a1i', '( %s -> %s e. RR )' % (ante, E1))
    ge2d = w.s([ge2], 'a1i', '( %s -> 2 < %s )' % (ante, E1)); le3d = w.s([le3], 'a1i', '( %s -> %s < 3 )' % (ante, E1))
    # log log D >_ 1
    lpos = lin.linarith(w, ante, [l200], '0 < %s' % L, leaves={L: ('RR', lr)}, atoms=[L])
    lrp = st([lr, lpos], 'elrpd', '%s e. RR+' % L)
    e1rp = w.s([w.s([ee, w.s([], 'epr', '_e e. RR+')], 'eqeltrri', '%s e. RR+' % E1)], 'a1i', '( %s -> %s e. RR+ )' % (ante, E1))
    eL = lin.linarith(w, ante, [le3d, l200], '%s <_ %s' % (E1, L), leaves={E1: ('RR', e1rd), L: ('RR', lr)}, atoms=[E1, L])
    ll = st([eL, st([e1rp, lrp, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (E1, L, E1, L))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (E1, L))
    ll1 = st([w.s([w.s([w.s([], '1re', '1 e. RR'), w.inst('relogef')], 'ax-mp', '( log ` %s ) = 1' % E1)], 'a1i', '( %s -> ( log ` %s ) = 1 )' % (ante, E1)), ll], 'eqbrtrrd',
             '1 <_ ( log ` %s )' % L)
    # C = ( 3200 x. e ) x. K >_ 1, log C >_ 0
    C3 = '( ; ; ; 3 2 0 0 x. %s )' % E1
    CK = '( %s x. K )' % C3
    c3r = st([litr(w, ante, '; ; ; 3 2 0 0'), e1rd], 'remulcld', '%s e. RR' % C3)
    c3ge = lin.linarith(w, ante, [ge2d], '1 <_ %s' % C3, leaves={E1: ('RR', e1rd)}, atoms=[E1])
    c3p = lin.linarith(w, ante, [ge2d], '0 <_ %s' % C3, leaves={E1: ('RR', e1rd)}, atoms=[E1])
    ckm = st([st([], '1red', '1 e. RR'), c3r, st([], '1red', '1 e. RR'), kr, w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % ante),
              w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % ante), c3ge, k1], 'lemul12ad', '( 1 x. 1 ) <_ %s' % CK)
    ck1 = st([w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % ante), ckm], 'eqbrtrrd', '1 <_ %s' % CK)
    ckr = st([c3r, kr], 'remulcld', '%s e. RR' % CK)
    ckrp = st([ckr, lin.linarith(w, ante, [ck1], '0 < %s' % CK, leaves={CK: ('RR', ckr)}, atoms=[CK])], 'elrpd', '%s e. RR+' % CK)
    lc0 = st([ckr, ck1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` %s )' % CK)
    # lambda >_ 0
    LAM = '( ( 1 - T ) x. %s )' % L
    P6 = '( ( 6 / 5 ) x. %s )' % LAM
    omt = st([st([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR')
    omt0 = lin.linarith(w, ante, [t1], '0 <_ ( 1 - T )', leaves={'T': ('RR', tr)})
    lamr = st([omt, lr], 'remulcld', '%s e. RR' % LAM)
    lam0 = st([omt, lr, omt0, st([lpos], 'ltled', '0 <_ %s' % L)], 'mulge0d', '0 <_ %s' % LAM)
    p6r = st([litr(w, ante, '( 6 / 5 )'), lamr], 'remulcld', '%s e. RR' % P6)
    p60 = st([litr(w, ante, '( 6 / 5 )'), lamr, litle(w, ante, '0', '( 6 / 5 )'), lam0], 'mulge0d', '0 <_ %s' % P6)
    llr = st([lrp], 'relogcld', '( log ` %s ) e. RR' % L); lcr = st([ckrp], 'relogcld', '( log ` %s ) e. RR' % CK)
    # 1 / 2 <_ | Im S |
    yh = lin.linarith(w, ante, [hg, ll1, p60, lc0], '( 1 / 2 ) <_ %s' % y,
                      leaves={y: ('RR', yr), '( log ` %s )' % L: ('RR', llr), P6: ('RR', p6r), '( log ` %s )' % CK: ('RR', lcr)},
                      atoms=[y, '( log ` %s )' % L, P6, '( log ` %s )' % CK])
    # Gamma
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    rs0 = st([st([], '0red', '0 e. RR'), tr, rsr, t0, tsr], 'letrd', '0 <_ ( Re ` S )')
    W_ = '( exp ` -u %s )' % y
    gb = st([st([kr, gh], 'jca', '( K e. RR /\\ %s )' % GAMH), st([sc, st([st([rs0, sr1], 'jca', '( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 )'), yh], 'jca',
                                                                     '( ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) /\\ ( 1 / 2 ) <_ %s )' % y)], 'jca',
                                                                 '( S e. CC /\\ ( ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) /\\ ( 1 / 2 ) <_ %s ) )' % y), w.inst('z5gam1')],
            'syl2anc', '( abs ` ( _G ` ( 1 - S ) ) ) <_ ( K x. %s )' % W_)
    # X
    XP = XPD
    d1le = lin.linarith(w, ante, [d1], '1 <_ D', leaves={'D': ('RR', dr)})
    cx = st([st([dr, d1le], 'jca', '( D e. RR /\\ 1 <_ D )'), st([st([], '0red', '0 e. RR'), litr(w, ante, '( 6 / 5 )')], 'jca', '( 0 e. RR /\\ ( 6 / 5 ) e. RR )'),
             litle(w, ante, '0', '( 6 / 5 )'), w.inst('cxplea')], 'syl3anc', '( D ^c 0 ) <_ %s' % XP)
    x1 = st([st([df['dc'], w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1'), cx], 'eqbrtrrd', '1 <_ %s' % XP)
    xrp = st([drp, litr(w, ante, '( 6 / 5 )')], 'rpcxpcld', '%s e. RR+' % XP)
    xr = st([xrp], 'rpred', '%s e. RR' % XP)
    xb = st([st([xr, x1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (XP, XP)), st([tr, st([sc, tsr], 'jca', '( S e. CC /\\ T <_ ( Re ` S ) )')], 'jca',
                                                                          '( T e. RR /\\ ( S e. CC /\\ T <_ ( Re ` S ) ) )'), w.inst('z5xabs')], 'syl2anc',
            '( abs ` ( %s ^c ( 1 - S ) ) ) <_ ( %s ^c ( 1 - T ) )' % (XP, XP))
    E6 = '( exp ` %s )' % P6
    xm = st([drp, litr(w, ante, '( 6 / 5 )'), st([omt], 'recnd', '( 1 - T ) e. CC'), w.inst('cxpmul')], 'syl3anc',
            '( D ^c ( ( 6 / 5 ) x. ( 1 - T ) ) ) = ( %s ^c ( 1 - T ) )' % XP)
    xe = st([df['dc'], df['dne'], st([st([litr(w, ante, '( 6 / 5 )'), omt], 'remulcld', '( ( 6 / 5 ) x. ( 1 - T ) ) e. RR')], 'recnd', '( ( 6 / 5 ) x. ( 1 - T ) ) e. CC'),
             w.inst('cxpef')], 'syl3anc', '( D ^c ( ( 6 / 5 ) x. ( 1 - T ) ) ) = ( exp ` ( ( ( 6 / 5 ) x. ( 1 - T ) ) x. %s ) )' % L)
    ma = st([st([litr(w, ante, '( 6 / 5 )')], 'recnd', '( 6 / 5 ) e. CC'), st([omt], 'recnd', '( 1 - T ) e. CC'), st([lr], 'recnd', '%s e. CC' % L)], 'mulassd',
            '( ( ( 6 / 5 ) x. ( 1 - T ) ) x. %s ) = %s' % (L, P6))
    xE = st([st([st([xm], 'eqcomd', '( %s ^c ( 1 - T ) ) = ( D ^c ( ( 6 / 5 ) x. ( 1 - T ) ) )' % XP), xe], 'eqtrd',
                '( %s ^c ( 1 - T ) ) = ( exp ` ( ( ( 6 / 5 ) x. ( 1 - T ) ) x. %s ) )' % (XP, L)), st([ma], 'fveq2d', '( exp ` ( ( ( 6 / 5 ) x. ( 1 - T ) ) x. %s ) ) = %s' % (L, E6))],
            'eqtrd', '( %s ^c ( 1 - T ) ) = %s' % (XP, E6))
    xb2 = st([xb, xE], 'breqtrd', '( abs ` ( %s ^c ( 1 - S ) ) ) <_ %s' % (XP, E6))
    # phi ( N ) / N
    F_ = '( ( phi ` N ) / N )'
    phn = st([nn, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')
    phr = st([phn], 'nnred', '( phi ` N ) e. RR'); nrp = st([nn], 'nnrpd', 'N e. RR+')
    fr = st([phr, nrp], 'rerpdivcld', '%s e. RR' % F_)
    f0 = st([phr, nrp, st([st([phn], 'nnrpd', '( phi ` N ) e. RR+')], 'rpge0d', '0 <_ ( phi ` N )')], 'divge0d', '0 <_ %s' % F_)
    f1 = st([st([nn, w.inst('z5phile')], 'syl', '( phi ` N ) <_ N'), st([phr, nrp, w.inst('divle1le')], 'syl2anc', '( %s <_ 1 <-> ( phi ` N ) <_ N )' % F_)], 'mpbird',
            '%s <_ 1' % F_)
    af = st([fr, f0], 'absidd', '( abs ` %s ) = %s' % (F_, F_))
    # the M_r sum
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1D); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2D); z12 = st([zz], 'simp3d', '%s < %s' % (Z1D, Z2D))
    hab = st([st([st([z1rp], 'rpred', '%s e. RR' % Z1D), st([z1rp], 'rpgt0d', '0 < %s' % Z1D)], 'jca', '( %s e. RR /\\ 0 < %s )' % (Z1D, Z1D)),
              st([st([z2rp], 'rpred', '%s e. RR' % Z2D), z12], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca',
             '( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ %s < %s ) )' % (Z1D, Z1D, Z2D, Z1D, Z2D))
    cz = st([st([dr, d1le], 'jca', '( D e. RR /\\ 1 <_ D )'), st([st([], '0red', '0 e. RR'), litr(w, ante, '( ; 6 3 / ; ; 1 0 0 )')], 'jca',
                                                                '( 0 e. RR /\\ ( ; 6 3 / ; ; 1 0 0 ) e. RR )'), litle(w, ante, '0', '( ; 6 3 / ; ; 1 0 0 )'), w.inst('cxplea')],
            'syl3anc', '( D ^c 0 ) <_ %s' % Z2D)
    z21 = st([st([df['dc'], w.inst('cxp0')], 'syl', '( D ^c 0 ) = 1'), cz], 'eqbrtrrd', '1 <_ %s' % Z2D)
    rprp = st([drp, litr(w, ante, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % RPD)
    RS = '( N RSet %s )' % RPD
    SUMM = 'sum_ r e. %s ( ( 1 / r ) x. ( ( <. %s , %s >. Mr <. %s , r >. ) ` 1 ) )' % (RS, Z1D, Z2D, PRN)
    mrs = st([st([hab, z21], 'jca', '( ( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ %s < %s ) ) /\\ 1 <_ %s )' % (Z1D, Z1D, Z2D, Z1D, Z2D, Z2D)),
              st([nn, st([rprp], 'rpred', '%s e. RR' % RPD)], 'jca', '( N e. NN /\\ %s e. RR )' % RPD), w.inst('z5mrsp')], 'syl2anc',
             '( abs ` %s ) <_ ( %s x. ( 1 + ( log ` %s ) ) )' % (SUMM, P1D, Z2D))
    Y_ = '( 1 + ( ( ; 6 3 / ; ; 1 0 0 ) x. %s ) )' % L
    lz = st([drp, litr(w, ante, '( ; 6 3 / ; ; 1 0 0 )'), w.inst('logcxp')], 'syl2anc', '( log ` %s ) = ( ( ; 6 3 / ; ; 1 0 0 ) x. %s )' % (Z2D, L))
    mb = st([mrs, st([st([lz], 'oveq2d', '( 1 + ( log ` %s ) ) = %s' % (Z2D, Y_))], 'oveq2d', '( %s x. ( 1 + ( log ` %s ) ) ) = ( %s x. %s )' % (P1D, Z2D, P1D, Y_))],
            'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (SUMM, P1D, Y_))
    # P ( 1 ) facts
    p0 = st([nn, rprp, w.inst('z5p1ge0')], 'syl2anc', '0 <_ %s' % P1D)
    rsf = st([st([nn, st([rprp], 'rpred', '%s e. RR' % RPD), w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))], 'simprd',
             '%s e. Fin' % RS)
    rss = st([st([nn, st([rprp], 'rpred', '%s e. RR' % RPD), w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))], 'simpld',
             '%s C_ ( 1 ... ( |_ ` %s ) )' % (RS, RPD))
    ar = '( %s /\\ r e. %s )' % (ante, RS)
    rnn = w.s([w.s([w.s([rss], 'adantr', '( %s -> %s C_ ( 1 ... ( |_ ` %s ) ) )' % (ar, RS, RPD)), w.s([], 'simpr', '( %s -> r e. %s )' % (ar, RS))], 'sseldd',
                   '( %s -> r e. ( 1 ... ( |_ ` %s ) ) )' % (ar, RPD)), w.inst('elfznn')], 'syl', '( %s -> r e. NN )' % ar)
    p1r = st([rsf, w.s([rnn], 'nnrecred', '( %s -> ( 1 / r ) e. RR )' % ar)], 'fsumrecl', '%s e. RR' % P1D)
    yyr = st([st([], '1red', '1 e. RR'), st([litr(w, ante, '( ; 6 3 / ; ; 1 0 0 )'), lr], 'remulcld', '( ( ; 6 3 / ; ; 1 0 0 ) x. %s ) e. RR' % L)], 'readdcld', '%s e. RR' % Y_)
    yy0 = lin.linarith(w, ante, [l200], '0 <_ %s' % Y_, leaves={L: ('RR', lr)}, atoms=[L])
    py = '( %s x. %s )' % (P1D, Y_)
    pyr = st([p1r, yyr], 'remulcld', '%s e. RR' % py); py0 = st([p1r, yyr, p0, yy0], 'mulge0d', '0 <_ %s' % py)
    # the height condition
    LL = '( log ` %s )' % L; LC = '( log ` %s )' % CK
    Z_ = '( ( %s x. %s ) x. %s )' % (L, E6, CK)
    ey = '( exp ` %s )' % y
    lamc = st([st([llr, p6r], 'readdcld', '( %s + %s ) e. RR' % (LL, P6)), lcr], 'readdcld', '%s e. RR' % LAM0)
    el = st([hg, st([lamc, yr, w.inst('efle')], 'syl2anc', '( %s <_ %s <-> ( exp ` %s ) <_ %s )' % (LAM0, y, LAM0, ey))], 'mpbid', '( exp ` %s ) <_ %s' % (LAM0, ey))
    ea1 = st([st([st([llr, p6r], 'readdcld', '( %s + %s ) e. RR' % (LL, P6))], 'recnd', '( %s + %s ) e. CC' % (LL, P6)), st([lcr], 'recnd', '%s e. CC' % LC), w.inst('efadd')],
             'syl2anc', '( exp ` %s ) = ( ( exp ` ( %s + %s ) ) x. ( exp ` %s ) )' % (LAM0, LL, P6, LC))
    ea2 = st([st([llr], 'recnd', '%s e. CC' % LL), st([p6r], 'recnd', '%s e. CC' % P6), w.inst('efadd')], 'syl2anc',
             '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. %s )' % (LL, P6, LL, E6))
    ea3 = st([lrp, w.inst('reeflog')], 'syl', '( exp ` %s ) = %s' % (LL, L))
    ea4 = st([ckrp, w.inst('reeflog')], 'syl', '( exp ` %s ) = %s' % (LC, CK))
    ea23 = st([ea2, st([ea3], 'oveq1d', '( ( exp ` %s ) x. %s ) = ( %s x. %s )' % (LL, E6, L, E6))], 'eqtrd', '( exp ` ( %s + %s ) ) = ( %s x. %s )' % (LL, P6, L, E6))
    eaz = st([ea1, st([ea23, ea4], 'oveq12d', '( ( exp ` ( %s + %s ) ) x. ( exp ` %s ) ) = %s' % (LL, P6, LC, Z_))], 'eqtrd', '( exp ` %s ) = %s' % (LAM0, Z_))
    zle = st([st([eaz], 'eqcomd', '%s = ( exp ` %s )' % (Z_, LAM0)), el], 'eqbrtrd', '%s <_ %s' % (Z_, ey))
    e6rp = st([p6r], 'rpefcld', '%s e. RR+' % E6)
    zr = st([st([lr, st([e6rp], 'rpred', '%s e. RR' % E6)], 'remulcld', '( %s x. %s ) e. RR' % (L, E6)), ckr], 'remulcld', '%s e. RR' % Z_)
    eyrp = st([yr], 'rpefcld', '%s e. RR+' % ey)
    zd1 = st([zle, st([zr, eyrp, w.inst('divle1le')], 'syl2anc', '( ( %s / %s ) <_ 1 <-> %s <_ %s )' % (Z_, ey, Z_, ey))], 'mpbird', '( %s / %s ) <_ 1' % (Z_, ey))
    ycc = st([yr], 'recnd', '%s e. CC' % y)
    wv = st([ycc, w.inst('efneg')], 'syl', '%s = ( 1 / %s )' % (W_, ey))
    wz = st([st([wv], 'oveq1d', '( %s x. %s ) = ( ( 1 / %s ) x. %s )' % (W_, Z_, ey, Z_)),
             st([st([st([zr], 'recnd', '%s e. CC' % Z_), st([eyrp], 'rpcnd', '%s e. CC' % ey), st([eyrp], 'rpne0d', '%s =/= 0' % ey)], 'divrec2d',
                    '( %s / %s ) = ( ( 1 / %s ) x. %s )' % (Z_, ey, ey, Z_))], 'eqcomd', '( ( 1 / %s ) x. %s ) = ( %s / %s )' % (ey, Z_, Z_, ey))], 'eqtrd',
            '( %s x. %s ) = ( %s / %s )' % (W_, Z_, Z_, ey))
    hW = st([wz, zd1], 'eqbrtrd', '( %s x. %s ) <_ 1' % (W_, Z_))
    # the value and the absolute value of the pole term
    prx = w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % PRN)], 'a1i', '( %s -> %s e. _V )' % (ante, PRN))
    ev = st([st([st([z1rp, z2rp, xrp], '3jca', '( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ )' % (Z1D, Z2D, XP)), st([prx, nn, rprp], '3jca', '( %s e. _V /\\ N e. NN /\\ %s e. RR+ )' % (PRN, RPD))],
                'jca', '( ( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ N e. NN /\\ %s e. RR+ ) )' % (Z1D, Z2D, XP, PRN, RPD)), sc, w.inst('z5epval')], 'syl2anc',
            '%s = if ( %s = %s , ( ( ( ( _G ` ( 1 - S ) ) x. ( %s ^c ( 1 - S ) ) ) x. %s ) x. %s ) , 0 )' % (EPD, PRN, PRIN('N', 'h'), XP, F_, SUMM))
    GA = '( _G ` ( 1 - S ) )'; XA = '( %s ^c ( 1 - S ) )' % XP
    EPB_ = '( ( ( %s x. %s ) x. %s ) x. %s )' % (GA, XA, F_, SUMM)
    cbp = w.s([cg(w, 'if ( ( n gcd N ) = 1 , 1 , 0 )', 'n', 'h')], 'cbvmptv', '%s = %s' % (PRN, PRIN('N', 'h')))
    ev2 = st([ev, st([w.s([cbp], 'a1i', '( %s -> %s = %s )' % (ante, PRN, PRIN('N', 'h')))], 'iftrued', 'if ( %s = %s , %s , 0 ) = %s' % (PRN, PRIN('N', 'h'), EPB_, EPB_))],
             'eqtrd', '%s = %s' % (EPD, EPB_))
    # Gamma ( 1 - S ) is a complex number: 1 - S is not an integer
    zc = st([st([], '1cnd', '1 e. CC'), sc], 'subcld', '( 1 - S ) e. CC')
    az = '( %s /\\ ( 1 - S ) e. ZZ )' % ante
    saz = mkst(w, az)
    im0 = saz([saz([saz([], 'simpr', '( 1 - S ) e. ZZ')], 'zred', '( 1 - S ) e. RR'), w.inst('reim0')], 'syl', '( Im ` ( 1 - S ) ) = 0')
    ims = saz([saz([saz([], '1cnd', '1 e. CC'), lift(w, sc, az), w.inst('imsub')], 'syl2anc', '( Im ` ( 1 - S ) ) = ( ( Im ` 1 ) - ( Im ` S ) )'),
               w.s([w.s([w.s([], 'im1', '( Im ` 1 ) = 0')], 'oveq1i', '( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) )')], 'a1i',
                   '( %s -> ( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) ) )' % az)], 'eqtrd', '( Im ` ( 1 - S ) ) = ( 0 - ( Im ` S ) )')
    isr = saz([lift(w, sc, az)], 'imcld', '( Im ` S ) e. RR')
    im00 = saz([ims, im0], 'eqtr3d', '( 0 - ( Im ` S ) ) = 0')
    is0 = saz([im00, saz([saz([], '0cnd', '0 e. CC'), saz([isr], 'recnd', '( Im ` S ) e. CC')], 'subeq0ad', '( ( 0 - ( Im ` S ) ) = 0 <-> 0 = ( Im ` S ) )')], 'mpbid',
              '0 = ( Im ` S )')
    y0 = saz([saz([saz([is0], 'eqcomd', '( Im ` S ) = 0')], 'fveq2d', '%s = ( abs ` 0 )' % y), w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % az)],
             'eqtrd', '%s = 0' % y)
    hz_ = saz([lift(w, yh, az), y0], 'breqtrd', '( 1 / 2 ) <_ 0')
    nh = w.s([w.s([w.s([], 'halfgt0', '0 < ( 1 / 2 )'), w.s([w.s([], '0re', '0 e. RR'), w.s([], 'halfre', '( 1 / 2 ) e. RR'),
                                                              w.inst('ltnle')], 'mp2an', '( 0 < ( 1 / 2 ) <-> -. ( 1 / 2 ) <_ 0 )')], 'mpbi', '-. ( 1 / 2 ) <_ 0')],
             'a1i', '( %s -> -. ( 1 / 2 ) <_ 0 )' % az)
    nz = w.s([hz_, nh], 'pm2.65da', '( %s -> -. ( 1 - S ) e. ZZ )' % ante)
    nzn = st([w.s([w.s([], 'eldifi', '( ( 1 - S ) e. ( ZZ \\ NN ) -> ( 1 - S ) e. ZZ )')], 'a1i', '( %s -> ( ( 1 - S ) e. ( ZZ \\ NN ) -> ( 1 - S ) e. ZZ ) )' % ante), nz], 'mtod',
             '-. ( 1 - S ) e. ( ZZ \\ NN )')
    zdom = st([zc, nzn], 'eldifd', '( 1 - S ) e. ( CC \\ ( ZZ \\ NN ) )')
    gac = st([zdom, w.inst('gamcl')], 'syl', '%s e. CC' % GA)
    xac = st([st([xrp], 'rpcnd', '%s e. CC' % XP), zc], 'cxpcld', '%s e. CC' % XA)
    fc_ = st([fr], 'recnd', '%s e. CC' % F_)
    art = '( %s /\\ r e. %s )' % (ante, RS)
    pf = st([st([nn, w.inst('z5prin')], 'syl', cns('z5prin'))], 'simplld', '%s : NN --> CC' % PRN)
    MRr = '( ( <. %s , %s >. Mr <. %s , r >. ) ` 1 )' % (Z1D, Z2D, PRN)
    mcr = w.s([lift(w, hab, art), rnn, lift(w, pf, art), w.s([], '1cnd', '( %s -> 1 e. CC )' % art), w.inst('z5mrcl')], 'syl22anc', '( %s -> %s e. CC )' % (art, MRr))
    trc = w.s([w.s([w.s([rnn], 'nncnd', '( %s -> r e. CC )' % art), w.s([rnn], 'nnne0d', '( %s -> r =/= 0 )' % art)], 'reccld', '( %s -> ( 1 / r ) e. CC )' % art), mcr], 'mulcld',
              '( %s -> ( ( 1 / r ) x. %s ) e. CC )' % (art, MRr))
    smc = st([rsf, trc], 'fsumcl', '%s e. CC' % SUMM)
    A = lambda x: '( abs ` %s )' % x
    GX = '( %s x. %s )' % (GA, XA); GXF = '( %s x. %s )' % (GX, F_)
    gxc = st([gac, xac], 'mulcld', '%s e. CC' % GX); gxfc = st([gxc, fc_], 'mulcld', '%s e. CC' % GXF)
    a1_ = st([gxfc, smc], 'absmuld', '%s = ( %s x. %s )' % (A(EPB_), A(GXF), A(SUMM)))
    a2_ = st([gxc, fc_], 'absmuld', '%s = ( %s x. %s )' % (A(GXF), A(GX), A(F_)))
    a3_ = st([gac, xac], 'absmuld', '%s = ( %s x. %s )' % (A(GX), A(GA), A(XA)))
    V1 = '( %s x. %s )' % (A(GA), A(XA)); V2 = '( %s x. %s )' % (V1, A(F_)); V3 = '( %s x. %s )' % (V2, A(SUMM))
    aev = st([a1_, st([st([a2_, st([a3_], 'oveq1d', '( %s x. %s ) = %s' % (A(GX), A(F_), V2))], 'eqtrd', '%s = %s' % (A(GXF), V2))], 'oveq1d',
                      '( %s x. %s ) = %s' % (A(GXF), A(SUMM), V3))], 'eqtrd', '%s = %s' % (A(EPB_), V3))
    KW = '( K x. %s )' % W_
    wr = st([st([yr], 'renegcld', '-u %s e. RR' % y)], 'reefcld', '%s e. RR' % W_)
    w0 = st([st([st([yr], 'renegcld', '-u %s e. RR' % y)], 'rpefcld', '%s e. RR+' % W_)], 'rpge0d', '0 <_ %s' % W_)
    kwr = st([kr, wr], 'remulcld', '%s e. RR' % KW)
    e6r = st([e6rp], 'rpred', '%s e. RR' % E6)
    B1r = '( %s x. %s )' % (KW, E6); B2r = '( %s x. 1 )' % B1r; B3r = '( %s x. %s )' % (B2r, py)
    agr = st([gac], 'abscld', '%s e. RR' % A(GA)); axr = st([xac], 'abscld', '%s e. RR' % A(XA)); afr = st([fc_], 'abscld', '%s e. RR' % A(F_)); asr = st([smc], 'abscld', '%s e. RR' % A(SUMM))
    b1 = st([agr, kwr, axr, e6r, st([gac], 'absge0d', '0 <_ %s' % A(GA)), st([xac], 'absge0d', '0 <_ %s' % A(XA)), gb, xb2], 'lemul12ad', '%s <_ %s' % (V1, B1r))
    v1r = st([agr, axr], 'remulcld', '%s e. RR' % V1)
    v10 = st([agr, axr, st([gac], 'absge0d', '0 <_ %s' % A(GA)), st([xac], 'absge0d', '0 <_ %s' % A(XA))], 'mulge0d', '0 <_ %s' % V1)
    b1r = st([kwr, e6r], 'remulcld', '%s e. RR' % B1r)
    b2 = st([v1r, b1r, afr, st([], '1red', '1 e. RR'), v10, st([fc_], 'absge0d', '0 <_ %s' % A(F_)), b1, st([af, f1], 'eqbrtrd', '%s <_ 1' % A(F_))], 'lemul12ad',
            '%s <_ %s' % (V2, B2r))
    v2r = st([v1r, afr], 'remulcld', '%s e. RR' % V2)
    v20 = st([v1r, afr, v10, st([fc_], 'absge0d', '0 <_ %s' % A(F_))], 'mulge0d', '0 <_ %s' % V2)
    b2r = st([b1r, st([], '1red', '1 e. RR')], 'remulcld', '%s e. RR' % B2r)
    b3 = st([v2r, b2r, asr, pyr, v20, st([smc], 'absge0d', '0 <_ %s' % A(SUMM)), b2, mb], 'lemul12ad', '%s <_ %s' % (V3, B3r))
    # the numerics
    Q2 = '( %s x. %s )' % (C3, L)
    c3rp = st([c3r, lin.linarith(w, ante, [ge2d], '0 < %s' % C3, leaves={E1: ('RR', e1rd)}, atoms=[E1])], 'elrpd', '%s e. RR+' % C3)
    q2rp = st([c3rp, lrp], 'rpmulcld', '%s e. RR+' % Q2)
    q2r = st([q2rp], 'rpred', '%s e. RR' % Q2)
    WZ = '( %s x. %s )' % (W_, Z_)
    lin.MAXDEG = 6
    idt = lin.lineq(w, ante, '( %s x. %s )' % (B3r, Q2), '( %s x. %s )' % (py, WZ),
                    leaves={'K': ('RR', kr), W_: ('RR', wr), E6: ('RR', e6r), py: ('RR', pyr), C3: ('RR', c3r), L: ('RR', lr)},
                    atoms=['K', W_, E6, py, C3, L], products=True)
    wzr = st([wr, zr], 'remulcld', '%s e. RR' % WZ)
    m1 = st([wzr, st([], '1red', '1 e. RR'), pyr, py0, hW], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 1 )' % (py, WZ, py))
    m2 = st([st([pyr], 'recnd', '%s e. CC' % py)], 'mulridd', '( %s x. 1 ) = %s' % (py, py))
    q32 = st([litr(w, ante, '; ; ; 3 2 0 0'), c3r, lr, st([lpos], 'ltled', '0 <_ %s' % L),
              lin.linarith(w, ante, [ge2d], '; ; ; 3 2 0 0 <_ %s' % C3, leaves={E1: ('RR', e1rd)}, atoms=[E1])], 'lemul1ad', '( ; ; ; 3 2 0 0 x. %s ) <_ %s' % (L, Q2))
    yq = lin.linarith(w, ante, [q32, l200], '%s <_ ( %s / 8 )' % (Y_, Q2), leaves={L: ('RR', lr), Q2: ('RR', q2r)}, atoms=[L, Q2])
    q28 = st([q2r, w.s([num.rp(w, '8')], 'a1i', '( %s -> 8 e. RR+ )' % ante)], 'rerpdivcld', '( %s / 8 ) e. RR' % Q2)
    m3 = st([yyr, q28, p1r, p0, yq], 'lemul2ad', '%s <_ ( %s x. ( %s / 8 ) )' % (py, P1D, Q2))
    p1c = st([p1r], 'recnd', '%s e. CC' % P1D); q2c = st([q2r], 'recnd', '%s e. CC' % Q2)
    e8 = w.s([num.cc(w, '8')], 'a1i', '( %s -> 8 e. CC )' % ante); n8 = w.s([num.fact(w, '8', 'ne0')], 'a1i', '( %s -> 8 =/= 0 )' % ante)
    m4 = st([st([p1c, q2c, e8, n8], 'divassd', '( ( %s x. %s ) / 8 ) = ( %s x. ( %s / 8 ) )' % (P1D, Q2, P1D, Q2)),
             st([p1c, q2c, e8, n8], 'div23d', '( ( %s x. %s ) / 8 ) = ( ( %s / 8 ) x. %s )' % (P1D, Q2, P1D, Q2))], 'eqtr3d',
            '( %s x. ( %s / 8 ) ) = ( ( %s / 8 ) x. %s )' % (P1D, Q2, P1D, Q2))
    VQ = '( %s x. %s )' % (B3r, Q2)
    c1 = st([idt, m1], 'eqbrtrd', '%s <_ ( %s x. 1 )' % (VQ, py))
    c2 = st([c1, m2], 'breqtrd', '%s <_ %s' % (VQ, py))
    c3_ = st([st([st([b2r, pyr], 'remulcld', '%s e. RR' % B3r), q2r], 'remulcld', '%s e. RR' % VQ), pyr, st([p1r, q28], 'remulcld', '( %s x. ( %s / 8 ) ) e. RR' % (P1D, Q2)), c2, m3],
             'letrd', '%s <_ ( %s x. ( %s / 8 ) )' % (VQ, P1D, Q2))
    c4 = st([c3_, m4], 'breqtrd', '%s <_ ( ( %s / 8 ) x. %s )' % (VQ, P1D, Q2))
    p18 = st([p1r, w.s([num.rp(w, '8')], 'a1i', '( %s -> 8 e. RR+ )' % ante)], 'rerpdivcld', '( %s / 8 ) e. RR' % P1D)
    b3rr = st([b2r, pyr], 'remulcld', '%s e. RR' % B3r)
    vle = st([c4, st([b3rr, p18, q2rp], 'lemul1d', '( %s <_ ( %s / 8 ) <-> %s <_ ( ( %s / 8 ) x. %s ) )' % (B3r, P1D, VQ, P1D, Q2))], 'mpbird', '%s <_ ( %s / 8 )' % (B3r, P1D))
    v3r = st([v2r, asr], 'remulcld', '%s e. RR' % V3)
    fin = st([v3r, b3rr, p18, b3, vle], 'letrd', '%s <_ ( %s / 8 )' % (V3, P1D))
    fin2 = st([st([st([ev2], 'fveq2d', '%s = %s' % (A(EPD), A(EPB_))), aev], 'eqtrd', '%s = %s' % (A(EPD), V3)), fin], 'eqbrtrd', '%s <_ ( %s / 8 )' % (A(EPD), P1D))
    last = w.lines.pop()
    w.lines.append('qed:' + last.split(':', 1)[1])
    return w


def lam0half(w, ante, df, tr, t1, kr, k1):
    """( ante -> ( 1 / 2 ) <_ LAM0 ) and ( ante -> LAM0 e. RR ), from dfacts df, T e. RR, T <_ 1, K e. RR, 1 <_ K"""
    st = mkst(w, ante)
    lr, l200 = df['lr'], df['l200']
    L = '( log ` D )'; E1 = '( exp ` 1 )'
    ee = w.s([], 'df-e', '_e = ( exp ` 1 )')
    e1rd = w.s([w.s([ee, w.s([], 'ere', '_e e. RR')], 'eqeltrri', '%s e. RR' % E1)], 'a1i', '( %s -> %s e. RR )' % (ante, E1))
    ge2d = w.s([w.s([w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e'), ee], 'breqtri', '2 < %s' % E1)], 'a1i', '( %s -> 2 < %s )' % (ante, E1))
    le3d = w.s([w.s([ee, w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')], 'eqbrtrri', '%s < 3' % E1)], 'a1i', '( %s -> %s < 3 )' % (ante, E1))
    lpos = lin.linarith(w, ante, [l200], '0 < %s' % L, leaves={L: ('RR', lr)}, atoms=[L])
    lrp = st([lr, lpos], 'elrpd', '%s e. RR+' % L)
    e1rp = w.s([w.s([ee, w.s([], 'epr', '_e e. RR+')], 'eqeltrri', '%s e. RR+' % E1)], 'a1i', '( %s -> %s e. RR+ )' % (ante, E1))
    eL = lin.linarith(w, ante, [le3d, l200], '%s <_ %s' % (E1, L), leaves={E1: ('RR', e1rd), L: ('RR', lr)}, atoms=[E1, L])
    ll = st([eL, st([e1rp, lrp, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (E1, L, E1, L))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (E1, L))
    ll1 = st([w.s([w.s([w.s([], '1re', '1 e. RR'), w.inst('relogef')], 'ax-mp', '( log ` %s ) = 1' % E1)], 'a1i', '( %s -> ( log ` %s ) = 1 )' % (ante, E1)), ll], 'eqbrtrrd',
             '1 <_ ( log ` %s )' % L)
    C3 = '( ; ; ; 3 2 0 0 x. %s )' % E1; CK = '( %s x. K )' % C3
    c3r = st([litr(w, ante, '; ; ; 3 2 0 0'), e1rd], 'remulcld', '%s e. RR' % C3)
    c3ge = lin.linarith(w, ante, [ge2d], '1 <_ %s' % C3, leaves={E1: ('RR', e1rd)}, atoms=[E1])
    ckm = st([st([], '1red', '1 e. RR'), c3r, st([], '1red', '1 e. RR'), kr, w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % ante),
              w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % ante), c3ge, k1], 'lemul12ad', '( 1 x. 1 ) <_ %s' % CK)
    ck1 = st([w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % ante), ckm], 'eqbrtrrd', '1 <_ %s' % CK)
    ckr = st([c3r, kr], 'remulcld', '%s e. RR' % CK)
    ckrp = st([ckr, lin.linarith(w, ante, [ck1], '0 < %s' % CK, leaves={CK: ('RR', ckr)}, atoms=[CK])], 'elrpd', '%s e. RR+' % CK)
    lc0 = st([ckr, ck1, w.inst('logge0')], 'syl2anc', '0 <_ ( log ` %s )' % CK)
    LAM = '( ( 1 - T ) x. %s )' % L; P6 = '( ( 6 / 5 ) x. %s )' % LAM
    omt = st([st([], '1red', '1 e. RR'), tr], 'resubcld', '( 1 - T ) e. RR')
    omt0 = lin.linarith(w, ante, [t1], '0 <_ ( 1 - T )', leaves={'T': ('RR', tr)})
    lamr = st([omt, lr], 'remulcld', '%s e. RR' % LAM)
    lam0 = st([omt, lr, omt0, st([lpos], 'ltled', '0 <_ %s' % L)], 'mulge0d', '0 <_ %s' % LAM)
    p6r = st([litr(w, ante, '( 6 / 5 )'), lamr], 'remulcld', '%s e. RR' % P6)
    p60 = st([litr(w, ante, '( 6 / 5 )'), lamr, litle(w, ante, '0', '( 6 / 5 )'), lam0], 'mulge0d', '0 <_ %s' % P6)
    llr = st([lrp], 'relogcld', '( log ` %s ) e. RR' % L); lcr = st([ckrp], 'relogcld', '( log ` %s ) e. RR' % CK)
    l0r = st([st([llr, p6r], 'readdcld', '( ( log ` %s ) + %s ) e. RR' % (L, P6)), lcr], 'readdcld', '%s e. RR' % LAM0)
    h = lin.linarith(w, ante, [ll1, p60, lc0], '( 1 / 2 ) <_ %s' % LAM0,
                     leaves={'( log ` %s )' % L: ('RR', llr), P6: ('RR', p6r), '( log ` %s )' % CK: ('RR', lcr)}, atoms=['( log ` %s )' % L, P6, '( log ` %s )' % CK])
    return h, l0r


def gamcc(w, a, sc, yh):
    """( a -> ( _G ` ( 1 - S ) ) e. CC ) from sc: ( a -> S e. CC ), yh: ( a -> ( 1 / 2 ) <_ ( abs ` ( Im ` S ) ) )"""
    st = mkst(w, a)
    y = '( abs ` ( Im ` S ) )'
    zc = st([st([], '1cnd', '1 e. CC'), sc], 'subcld', '( 1 - S ) e. CC')
    az = '( %s /\\ ( 1 - S ) e. ZZ )' % a
    saz = mkst(w, az)
    im0 = saz([saz([saz([], 'simpr', '( 1 - S ) e. ZZ')], 'zred', '( 1 - S ) e. RR'), w.inst('reim0')], 'syl', '( Im ` ( 1 - S ) ) = 0')
    ims = saz([saz([saz([], '1cnd', '1 e. CC'), lift(w, sc, az), w.inst('imsub')], 'syl2anc', '( Im ` ( 1 - S ) ) = ( ( Im ` 1 ) - ( Im ` S ) )'),
               w.s([w.s([w.s([], 'im1', '( Im ` 1 ) = 0')], 'oveq1i', '( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) )')], 'a1i',
                   '( %s -> ( ( Im ` 1 ) - ( Im ` S ) ) = ( 0 - ( Im ` S ) ) )' % az)], 'eqtrd', '( Im ` ( 1 - S ) ) = ( 0 - ( Im ` S ) )')
    isr = saz([lift(w, sc, az)], 'imcld', '( Im ` S ) e. RR')
    im00 = saz([ims, im0], 'eqtr3d', '( 0 - ( Im ` S ) ) = 0')
    is0 = saz([im00, saz([saz([], '0cnd', '0 e. CC'), saz([isr], 'recnd', '( Im ` S ) e. CC')], 'subeq0ad', '( ( 0 - ( Im ` S ) ) = 0 <-> 0 = ( Im ` S ) )')], 'mpbid',
              '0 = ( Im ` S )')
    y0 = saz([saz([saz([is0], 'eqcomd', '( Im ` S ) = 0')], 'fveq2d', '%s = ( abs ` 0 )' % y), w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % az)],
             'eqtrd', '%s = 0' % y)
    hz_ = saz([lift(w, yh, az), y0], 'breqtrd', '( 1 / 2 ) <_ 0')
    nh = w.s([w.s([w.s([], 'halfgt0', '0 < ( 1 / 2 )'), w.s([w.s([], '0re', '0 e. RR'), w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.inst('ltnle')], 'mp2an',
                                                              '( 0 < ( 1 / 2 ) <-> -. ( 1 / 2 ) <_ 0 )')], 'mpbi', '-. ( 1 / 2 ) <_ 0')], 'a1i', '( %s -> -. ( 1 / 2 ) <_ 0 )' % az)
    nz = w.s([hz_, nh], 'pm2.65da', '( %s -> -. ( 1 - S ) e. ZZ )' % a)
    nzn = st([w.s([w.s([], 'eldifi', '( ( 1 - S ) e. ( ZZ \\ NN ) -> ( 1 - S ) e. ZZ )')], 'a1i', '( %s -> ( ( 1 - S ) e. ( ZZ \\ NN ) -> ( 1 - S ) e. ZZ ) )' % a), nz], 'mtod',
             '-. ( 1 - S ) e. ( ZZ \\ NN )')
    zdom = st([zc, nzn], 'eldifd', '( 1 - S ) e. ( CC \\ ( ZZ \\ NN ) )')
    return st([zdom, w.inst('gamcl')], 'syl', '( _G ` ( 1 - S ) ) e. CC')


def z5epcl():
    w = W('z5epcl', "The pole term is a complex number (for the principal character at | Im S | >_ 1 / 2, where 1 - S is not an integer and "
                    "Gamma ( 1 - S ) is defined; 0 otherwise).")
    ante = split_imp(STATEMENTS['z5epcl'])[0]
    st = mkst(w, ante)
    hz = st([], 'simpll', HZD3); nn = st([], 'simplr', 'N e. NN'); sc = st([], 'simprl', 'S e. CC'); cf = st([], 'simprrl', 'C : NN --> CC')
    hh = st([], 'simprrr', '( C = %s -> ( 1 / 2 ) <_ ( abs ` ( Im ` S ) ) )' % PRN)
    df = dfacts(w, ante, hz)
    dr, d1, drp = df['dr'], df['d1'], df['drp']
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1D); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2D); z12 = st([zz], 'simp3d', '%s < %s' % (Z1D, Z2D))
    hab = st([st([st([z1rp], 'rpred', '%s e. RR' % Z1D), st([z1rp], 'rpgt0d', '0 < %s' % Z1D)], 'jca', '( %s e. RR /\\ 0 < %s )' % (Z1D, Z1D)),
              st([st([z2rp], 'rpred', '%s e. RR' % Z2D), z12], 'jca', '( %s e. RR /\\ %s < %s )' % (Z2D, Z1D, Z2D))], 'jca',
             '( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ %s < %s ) )' % (Z1D, Z1D, Z2D, Z1D, Z2D))
    xrp = st([drp, litr(w, ante, '( 6 / 5 )')], 'rpcxpcld', '%s e. RR+' % XPD)
    rprp = st([drp, litr(w, ante, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % RPD)
    cvx = st([cf, w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ante), w.inst('fex')], 'syl2anc', 'C e. _V')
    RS = '( N RSet %s )' % RPD
    F_ = '( ( phi ` N ) / N )'
    SUMMC = 'sum_ r e. %s ( ( 1 / r ) x. ( ( <. %s , %s >. Mr <. C , r >. ) ` 1 ) )' % (RS, Z1D, Z2D)
    GA = '( _G ` ( 1 - S ) )'; XA = '( %s ^c ( 1 - S ) )' % XPD
    EPBC = '( ( ( %s x. %s ) x. %s ) x. %s )' % (GA, XA, F_, SUMMC)
    PH = PRIN('N', 'h')
    ev = st([st([st([z1rp, z2rp, xrp], '3jca', '( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ )' % (Z1D, Z2D, XPD)), st([cvx, nn, rprp], '3jca', '( C e. _V /\\ N e. NN /\\ %s e. RR+ )' % RPD)],
                'jca', '( ( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ ) /\\ ( C e. _V /\\ N e. NN /\\ %s e. RR+ ) )' % (Z1D, Z2D, XPD, RPD)), sc, w.inst('z5epval')], 'syl2anc',
            '%s = if ( C = %s , %s , 0 )' % (EPC, PH, EPBC))
    # the principal case
    t = '( %s /\\ C = %s )' % (ante, PH)
    stt = mkst(w, t)
    cbp = w.s([cg(w, 'if ( ( n gcd N ) = 1 , 1 , 0 )', 'n', 'h')], 'cbvmptv', '%s = %s' % (PRN, PH))
    cpr = stt([stt([], 'simpr', 'C = %s' % PH), w.s([cbp], 'a1i', '( %s -> %s = %s )' % (t, PRN, PH))], 'eqtr4d', 'C = %s' % PRN)
    yh = stt([cpr, lift(w, hh, t)], 'mpd', '( 1 / 2 ) <_ ( abs ` ( Im ` S ) )')
    gac = gamcc(w, t, lift(w, sc, t), yh)
    xac = stt([stt([lift(w, xrp, t)], 'rpcnd', '%s e. CC' % XPD), stt([stt([], '1cnd', '1 e. CC'), lift(w, sc, t)], 'subcld', '( 1 - S ) e. CC')], 'cxpcld', '%s e. CC' % XA)
    phn = stt([lift(w, nn, t), w.inst('phicl')], 'syl', '( phi ` N ) e. NN')
    fc_ = stt([stt([stt([phn], 'nnred', '( phi ` N ) e. RR'), stt([lift(w, nn, t)], 'nnrpd', 'N e. RR+')], 'rerpdivcld', '%s e. RR' % F_)], 'recnd', '%s e. CC' % F_)
    rsf = stt([stt([lift(w, nn, t), stt([lift(w, rprp, t)], 'rpred', '%s e. RR' % RPD), w.inst('z5rsetfi')], 'syl2anc',
                   '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))], 'simprd', '%s e. Fin' % RS)
    rss = stt([stt([lift(w, nn, t), stt([lift(w, rprp, t)], 'rpred', '%s e. RR' % RPD), w.inst('z5rsetfi')], 'syl2anc',
                   '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))], 'simpld', '%s C_ ( 1 ... ( |_ ` %s ) )' % (RS, RPD))
    ar = '( %s /\\ r e. %s )' % (t, RS)
    rnn = w.s([w.s([w.s([rss], 'adantr', '( %s -> %s C_ ( 1 ... ( |_ ` %s ) ) )' % (ar, RS, RPD)), w.s([], 'simpr', '( %s -> r e. %s )' % (ar, RS))], 'sseldd',
                   '( %s -> r e. ( 1 ... ( |_ ` %s ) ) )' % (ar, RPD)), w.inst('elfznn')], 'syl', '( %s -> r e. NN )' % ar)
    MRr = '( ( <. %s , %s >. Mr <. C , r >. ) ` 1 )' % (Z1D, Z2D)
    mcr = w.s([lift(w, hab, ar), rnn, lift(w, cf, ar), w.s([], '1cnd', '( %s -> 1 e. CC )' % ar), w.inst('z5mrcl')], 'syl22anc', '( %s -> %s e. CC )' % (ar, MRr))
    trc = w.s([w.s([w.s([rnn], 'nncnd', '( %s -> r e. CC )' % ar), w.s([rnn], 'nnne0d', '( %s -> r =/= 0 )' % ar)], 'reccld', '( %s -> ( 1 / r ) e. CC )' % ar), mcr], 'mulcld',
              '( %s -> ( ( 1 / r ) x. %s ) e. CC )' % (ar, MRr))
    smc = stt([rsf, trc], 'fsumcl', '%s e. CC' % SUMMC)
    ebc = stt([stt([stt([gac, xac], 'mulcld', '( %s x. %s ) e. CC' % (GA, XA)), fc_], 'mulcld', '( ( %s x. %s ) x. %s ) e. CC' % (GA, XA, F_)), smc], 'mulcld', '%s e. CC' % EPBC)
    ic = st([ebc, w.s([], '0cnd', '( ( %s /\\ -. C = %s ) -> 0 e. CC )' % (ante, PH))], 'ifclda', 'if ( C = %s , %s , 0 ) e. CC' % (PH, EPBC))
    w.qed([ev, ic], 'eqeltrd', STATEMENTS['z5epcl'])
    return w


def z5dlbe():
    w = W('z5dlbe', "Blueprint Proposition 4.4 (Lean detector_lower_bound, the frozen Z6c statement, without the false I9(c) hypothesis: "
                    "Detection.lean detector_lower_bound_of_P1 with the Gamma bound as a hypothesis): at a detected zero S with the "
                    "detection estimate (Lemmas 4.1-4.2) and, for the principal character, height >_ Lambda_0, "
                    "| F | >_ ( 1 / 400 ) ( phi ( N ) / N ) log D.")
    ante = split_imp(STATEMENTS['z5dlbe'])[0]
    st = mkst(w, ante)
    a1_ = st([], 'simpl', A1_); a2_ = st([], 'simpr', A2_)
    hz = st([a1_], 'simpld', '( %s /\\ N e. NN )' % HZD3)
    hzd = st([hz], 'simpld', HZD3); nn = st([hz], 'simprd', 'N e. NN')
    rest = st([a1_], 'simprd', '( ( ( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) ) /\\ ( K e. RR /\\ 1 <_ K ) ) /\\ ( %s /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) )' % GAMH)
    tk = st([rest], 'simpld', '( ( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) ) /\\ ( K e. RR /\\ 1 <_ K ) )')
    gs = st([rest], 'simprd', '( %s /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) )' % GAMH)
    tt = st([tk], 'simpld', '( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) )'); kk = st([tk], 'simprd', '( K e. RR /\\ 1 <_ K )')
    tr = st([tt], 'simpld', 'T e. RR'); t1 = st([tt], 'simprrd', 'T <_ 1')
    kr = st([kk], 'simpld', 'K e. RR'); k1 = st([kk], 'simprd', '1 <_ K')
    ss = st([gs], 'simprd', '( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) )'); sc = st([ss], 'simpld', 'S e. CC')
    cfh = st([a2_], 'simpld', '( C : NN --> CC /\\ ( C = %s -> %s <_ ( abs ` ( Im ` S ) ) ) )' % (PRN, LAM0))
    cf = st([cfh], 'simpld', 'C : NN --> CC'); hgt = st([cfh], 'simprd', '( C = %s -> %s <_ ( abs ` ( Im ` S ) ) )' % (PRN, LAM0))
    fr_ = st([a2_], 'simprd', '( F e. CC /\\ ( %s /\\ %s ) )' % (HP1_, HDET_))
    fc = st([fr_], 'simpld', 'F e. CC'); hp1 = st([fr_], 'simprld', HP1_); hdet = st([fr_], 'simprrd', HDET_)
    df = dfacts(w, ante, hzd)
    lh, l0r = lam0half(w, ante, df, tr, t1, kr, k1)
    y = '( abs ` ( Im ` S ) )'
    yr = st([st([st([sc], 'imcld', '( Im ` S ) e. RR')], 'recnd', '( Im ` S ) e. CC')], 'abscld', '%s e. RR' % y)
    # C = PRN -> 1 / 2 <_ | Im S |
    b = '( %s /\\ C = %s )' % (ante, PRN)
    sb = mkst(w, b)
    lb = sb([sb([], 'simpr', 'C = %s' % PRN), lift(w, hgt, b)], 'mpd', '%s <_ %s' % (LAM0, y))
    yhb = sb([w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % b), lift(w, l0r, b), lift(w, yr, b), lift(w, lh, b), lb], 'letrd',
             '( 1 / 2 ) <_ %s' % y)
    hh = w.s([yhb], 'ex', '( %s -> ( C = %s -> ( 1 / 2 ) <_ %s ) )' % (ante, PRN, y))
    ec = st([hz, st([sc, st([cf, hh], 'jca', '( C : NN --> CC /\\ ( C = %s -> ( 1 / 2 ) <_ %s ) )' % (PRN, y))], 'jca',
                    '( S e. CC /\\ ( C : NN --> CC /\\ ( C = %s -> ( 1 / 2 ) <_ %s ) ) )' % (PRN, y)), w.inst('z5epcl')], 'syl2anc', '%s e. CC' % EPC)
    # the pole bound in the principal case
    epo = sb([sb([lift(w, hz, b), sb([lift(w, tk, b), sb([lift(w, gs, b), lb], 'jca', '( ( %s /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) /\\ %s <_ %s )'
                                                         % (GAMH, LAM0, y))], 'jca',
                              '( ( ( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) ) /\\ ( K e. RR /\\ 1 <_ K ) ) /\\ ( ( %s /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) /\\ %s <_ %s ) )'
                              % (GAMH, LAM0, y))], 'jca', split_imp(STATEMENTS['z5epole'])[0]), w.inst('z5epole')], 'syl', '( abs ` %s ) <_ ( %s / 8 )' % (EPD, P1D))
    ce, _ = w.congr(EPC, {'C': PRN}, 'C = %s' % PRN, {'C': w.s([], 'id', '( C = %s -> C = %s )' % (PRN, PRN))})
    epc_t = sb([sb([sb([sb([], 'simpr', 'C = %s' % PRN), ce], 'syl', '%s = %s' % (EPC, EPD))], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (EPC, EPD)), epo], 'eqbrtrd',
               '( abs ` %s ) <_ ( %s / 8 )' % (EPC, P1D))
    # the non-principal case
    f = '( %s /\\ -. C = %s )' % (ante, PRN)
    sf = mkst(w, f)
    PH = PRIN('N', 'h')
    cbp = w.s([cg(w, 'if ( ( n gcd N ) = 1 , 1 , 0 )', 'n', 'h')], 'cbvmptv', '%s = %s' % (PRN, PH))
    nph = sf([sf([], 'simpr', '-. C = %s' % PRN), w.s([w.s([cbp], 'eqeq2i', '( C = %s <-> C = %s )' % (PRN, PH))], 'a1i', '( %s -> ( C = %s <-> C = %s ) )' % (f, PRN, PH))], 'mtbid',
             '-. C = %s' % PH)
    cne = sf([nph], 'neqned', 'C =/= %s' % PH)
    dr, d1, drp = df['dr'], df['d1'], df['drp']
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1D, Z2D, Z1D, Z2D))
    xrp = st([drp, litr(w, ante, '( 6 / 5 )')], 'rpcxpcld', '%s e. RR+' % XPD)
    rprp = st([drp, litr(w, ante, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % RPD)
    cvx = st([cf, w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ante), w.inst('fex')], 'syl2anc', 'C e. _V')
    sets = st([st([st([zz], 'simp1d', '%s e. RR+' % Z1D), st([zz], 'simp2d', '%s e. RR+' % Z2D), xrp], '3jca', '( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ )' % (Z1D, Z2D, XPD)),
               st([cvx, nn, rprp], '3jca', '( C e. _V /\\ N e. NN /\\ %s e. RR+ )' % RPD)], 'jca',
              '( ( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ ) /\\ ( C e. _V /\\ N e. NN /\\ %s e. RR+ ) )' % (Z1D, Z2D, XPD, RPD))
    e0 = sf([sf([lift(w, sets, f), lift(w, sc, f)], 'jca', '( ( ( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ ) /\\ ( C e. _V /\\ N e. NN /\\ %s e. RR+ ) ) /\\ S e. CC )'
                % (Z1D, Z2D, XPD, RPD)), cne, w.inst('z5ep0')], 'syl2anc', '%s = 0' % EPC)
    p0 = st([nn, rprp, w.inst('z5p1ge0')], 'syl2anc', '0 <_ %s' % P1D)
    RS = '( N RSet %s )' % RPD
    rsf = st([st([nn, st([rprp], 'rpred', '%s e. RR' % RPD), w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))], 'simprd',
             '%s e. Fin' % RS)
    rss = st([st([nn, st([rprp], 'rpred', '%s e. RR' % RPD), w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` %s ) ) /\\ %s e. Fin )' % (RS, RPD, RS))], 'simpld',
             '%s C_ ( 1 ... ( |_ ` %s ) )' % (RS, RPD))
    ar = '( %s /\\ j e. %s )' % (ante, RS)
    rnn = w.s([w.s([w.s([rss], 'adantr', '( %s -> %s C_ ( 1 ... ( |_ ` %s ) ) )' % (ar, RS, RPD)), w.s([], 'simpr', '( %s -> j e. %s )' % (ar, RS))], 'sseldd',
                   '( %s -> j e. ( 1 ... ( |_ ` %s ) ) )' % (ar, RPD)), w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % ar)
    prj = st([rsf, w.s([rnn], 'nnrecred', '( %s -> ( 1 / j ) e. RR )' % ar)], 'fsumrecl', 'sum_ j e. %s ( 1 / j ) e. RR' % RS)
    cbs = w.s([w.s([], 'oveq2', '( j = r -> ( 1 / j ) = ( 1 / r ) )')], 'cbvsumv', 'sum_ j e. %s ( 1 / j ) = %s' % (RS, P1D))
    pr = st([w.s([cbs], 'a1i', '( %s -> sum_ j e. %s ( 1 / j ) = %s )' % (ante, RS, P1D)), prj], 'eqeltrrd', '%s e. RR' % P1D)
    p8 = st([pr, w.s([num.rp(w, '8')], 'a1i', '( %s -> 8 e. RR+ )' % ante), p0], 'divge0d', '0 <_ ( %s / 8 )' % P1D)
    ab0 = sf([sf([e0], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % EPC), w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % f)], 'eqtrd',
             '( abs ` %s ) = 0' % EPC)
    epc_f = sf([ab0, lift(w, p8, f)], 'eqbrtrd', '( abs ` %s ) <_ ( %s / 8 )' % (EPC, P1D))
    epb = w.s([epc_t, epc_f], 'pm2.61dan', '( %s -> ( abs ` %s ) <_ ( %s / 8 ) )' % (ante, EPC, P1D))
    dl = st([hz, st([st([fc, ec], 'jca', '( F e. CC /\\ %s e. CC )' % EPC), st([hp1, st([hdet, epb], 'jca', '( %s /\\ ( abs ` %s ) <_ ( %s / 8 ) )' % (HDET_, EPC, P1D))], 'jca',
                                                                                  '( %s /\\ ( %s /\\ ( abs ` %s ) <_ ( %s / 8 ) ) )' % (HP1_, HDET_, EPC, P1D))], 'jca',
                    '( ( F e. CC /\\ %s e. CC ) /\\ ( %s /\\ ( %s /\\ ( abs ` %s ) <_ ( %s / 8 ) ) ) )' % (EPC, HP1_, HDET_, EPC, P1D)), w.inst('z5dlb')], 'syl2anc', cns('z5dlb'))
    last = w.lines.pop()
    w.lines.append('qed:' + last.split(':', 1)[1])
    return w


if __name__ == '__main__':
    import z5clib
    for f in sys.argv[1:]:
        z5clib.run(globals()[f]())
