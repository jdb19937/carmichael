"""ZL2 section G: the left edge, generic (LConvexity 738-948: zl2gcf, zl2left).
`MM_DB=sorties/zl2.mm python3 tools/gen/zl2_g.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl2lib import *
from lin import linarith, nlinarith
import num

only = sys.argv[1:]


def inst_ral_t(w, ante, ralst, S, body, T, mem):
    """( ante -> body[z:=T] ) from ralst: ( ante -> A. z e. S body ) and mem: ( ante -> T e. S );
    T carries no z (the antecedent binds z in its quantified hypotheses)"""
    idx = w.s([], 'id', '( z = %s -> z = %s )' % (T, T))
    st, val = w.wcongr(body, {'z': T}, 'z = %s' % T, {'z': idx})
    r = w.s([st], 'rspcv', '( %s e. %s -> ( A. z e. %s %s -> %s ) )' % (T, S, S, body, val))
    return w.s([mem, ralst, r], 'sylc', '( %s -> %s )' % (ante, val)), val


def cbv_yz(w, ante, raly, S, body_y):
    """( ante -> A. z e. S body_y[y:=z] ) from raly: ( ante -> A. y e. S body_y )"""
    idx = w.s([], 'id', '( y = z -> y = z )')
    st, val = w.wcongr(body_y, {'y': 'z'}, 'y = z', {'y': idx})
    bi = w.s([st], 'cbvralvw', '( A. y e. %s %s <-> A. z e. %s %s )' % (S, body_y, S, val))
    return w.s([raly, bi], 'sylib', '( %s -> A. z e. %s %s )' % (ante, S, val)), val


# ---------------------------------------------------------------- zl2gcf
if __name__ == '__main__' and (not only or 'zl2gcf' in only):
    w = W('zl2gcf', 'The Deligne factor ` 2 ( 2 pi ) ^ -( 1 - z ) ` times a value bounded by ` 34 ( | Im z | + 2 ) ^ ( 1/2 - Re z ) ` '
          'is bounded by ` 12 ( | Im z | + 2 ) ^ ( 1/2 - Re z ) ` on ` -1/2 <_ Re z <_ 0 ` ( ` 34 / pi <_ 12 ` ; ~ abscxp , ~ cxplead ; '
          'Lean ` norm_GammaC_mul_trig_interp ` ).')
    A = STATEMENTS['zl2gcf'].split(' -> ( abs ` ( ( 2 x.')[0][2:]
    GQZ = GQ('Z')
    assert A == '( ( Z e. CC /\\ ( -u ( 1 / 2 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 0 ) ) /\\ ( V e. CC /\\ ( abs ` V ) <_ ( ; 3 4 x. %s ) ) )' % GQZ, A
    zc = D(w, A, 'simpll', [], 'Z e. CC')
    zlo = D(w, A, 'simplr', [], '( -u ( 1 / 2 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 0 )')
    z2 = D(w, A, 'simprd', [zlo], '( Re ` Z ) <_ 0')
    vc = D(w, A, 'simprl', [], 'V e. CC')
    vb = D(w, A, 'simprr', [], '( abs ` V ) <_ ( ; 3 4 x. %s )' % GQZ)
    zr = D(w, A, 'recld', [zc], '( Re ` Z ) e. RR')
    izc = D(w, A, 'recnd', [D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR')], '( Im ` Z ) e. CC')
    aiz = D(w, A, 'abscld', [izc], '( abs ` ( Im ` Z ) ) e. RR')
    aiz0 = D(w, A, 'absge0d', [izc], '0 <_ ( abs ` ( Im ` Z ) )')
    Qd = '( ( abs ` ( Im ` Z ) ) + 2 )'
    qr = D(w, A, 'readdcld', [aiz, a1(w, A, '2re', '2 e. RR')], '%s e. RR' % Qd)
    qp = linarith(w, A, [aiz0], '0 < %s' % Qd, leaves={'( abs ` ( Im ` Z ) )': aiz})
    qrp = D(w, A, 'elrpd', [qr, qp], '%s e. RR+' % Qd)
    ex = D(w, A, 'resubcld', [a1(w, A, 'halfre', '( 1 / 2 ) e. RR'), zr], '( ( 1 / 2 ) - ( Re ` Z ) ) e. RR')
    gqrp = D(w, A, 'rpcxpcld', [qrp, ex], '%s e. RR+' % GQZ)
    gqr = D(w, A, 'rpred', [gqrp], '%s e. RR' % GQZ)
    gq0 = D(w, A, 'rpge0d', [gqrp], '0 <_ %s' % GQZ)
    av = D(w, A, 'abscld', [vc], '( abs ` V ) e. RR')
    av0 = D(w, A, 'absge0d', [vc], '0 <_ ( abs ` V )')
    # the power ( 2 pi ) ^c -( 1 - Z ): modulus ( 2 pi ) ^c ( Re Z - 1 ) <_ ( 2 pi ) ^c -1 = 1 / ( 2 pi ) <_ 1 / 6
    TP = '( 2 x. _pi )'
    tprp = w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.s([], 'pirp', '_pi e. RR+'), w.s([], 'rpmulcl', '( ( 2 e. RR+ /\\ _pi e. RR+ ) -> %s e. RR+ )' % TP)], 'mp2an', '%s e. RR+' % TP)],
               'a1i', '( %s -> %s e. RR+ )' % (A, TP))
    tpr = D(w, A, 'rpred', [tprp], '%s e. RR' % TP)
    tpc = D(w, A, 'rpcnd', [tprp], '%s e. CC' % TP)
    tpne = D(w, A, 'rpne0d', [tprp], '%s =/= 0' % TP)
    M = '-u ( 1 - Z )'
    omz = D(w, A, 'subcld', [a1(w, A, 'ax-1cn', '1 e. CC'), zc], '( 1 - Z ) e. CC')
    mc = D(w, A, 'negcld', [omz], '%s e. CC' % M)
    P = '( %s ^c %s )' % (TP, M)
    pc = D(w, A, 'cxpcld', [tpc, mc], '%s e. CC' % P)
    ap = w.s([tprp, mc, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( %s ^c ( Re ` %s ) ) )' % (A, P, TP, M))
    r1 = D(w, A, 'renegd', [omz], '( Re ` %s ) = -u ( Re ` ( 1 - Z ) )' % M)
    r2 = D(w, A, 'resubd', [a1(w, A, 'ax-1cn', '1 e. CC'), zc], '( Re ` ( 1 - Z ) ) = ( ( Re ` 1 ) - ( Re ` Z ) )')
    r3 = E(w, A, 'oveq1d', [a1(w, A, 're1', '( Re ` 1 ) = 1')], '( ( Re ` 1 ) - ( Re ` Z ) )', '( 1 - ( Re ` Z ) )')
    r4 = w.s([r2, r3], 'eqtrd', '( %s -> ( Re ` ( 1 - Z ) ) = ( 1 - ( Re ` Z ) ) )' % A)
    RM = '-u ( 1 - ( Re ` Z ) )'
    r5 = w.s([r1, E(w, A, 'negeqd', [r4], '-u ( Re ` ( 1 - Z ) )', RM)], 'eqtrd', '( %s -> ( Re ` %s ) = %s )' % (A, M, RM))
    rmr = D(w, A, 'renegcld', [D(w, A, 'resubcld', [a1(w, A, '1re', '1 e. RR'), zr], '( 1 - ( Re ` Z ) ) e. RR')], '%s e. RR' % RM)
    rmle = linarith(w, A, [z2], '%s <_ -u 1' % RM, leaves={'( Re ` Z )': zr})
    pi3 = a1(w, A, 'pigt3', '3 < _pi')
    tp1 = linarith(w, A, [pi3], '1 <_ %s' % TP, leaves={'_pi': a1(w, A, 'pire', '_pi e. RR')})
    tp6 = linarith(w, A, [pi3], '6 <_ %s' % TP, leaves={'_pi': a1(w, A, 'pire', '_pi e. RR')})
    n1r = D(w, A, 'renegcld', [a1(w, A, '1re', '1 e. RR')], '-u 1 e. RR')
    le1 = D(w, A, 'cxplead', [tpr, tp1, rmr, n1r, rmle], '( %s ^c %s ) <_ ( %s ^c -u 1 )' % (TP, RM, TP))
    e1 = D(w, A, 'cxpnegd', [tpc, tpne, a1(w, A, 'ax-1cn', '1 e. CC')], '( %s ^c -u 1 ) = ( 1 / ( %s ^c 1 ) )' % (TP, TP))
    e2 = E(w, A, 'oveq2d', [D(w, A, 'cxp1d', [tpc], '( %s ^c 1 ) = %s' % (TP, TP))], '( 1 / ( %s ^c 1 ) )' % TP, '( 1 / %s )' % TP)
    e12 = w.s([e1, e2], 'eqtrd', '( %s -> ( %s ^c -u 1 ) = ( 1 / %s ) )' % (A, TP, TP))
    six = D(w, A, 'elrpd', [a1(w, A, '6re', '6 e. RR'), a1(w, A, '6pos', '0 < 6')], '6 e. RR+')
    le6 = D(w, A, 'lediv2ad', [six, tprp, a1(w, A, '1re', '1 e. RR'), a1(w, A, '0le1', '0 <_ 1'), tp6], '( 1 / %s ) <_ ( 1 / 6 )' % TP)
    rec = D(w, A, 'rpred', [D(w, A, 'rpreccld', [tprp], '( 1 / %s ) e. RR+' % TP)], '( 1 / %s ) e. RR' % TP)
    pw1r = D(w, A, 'recxpcld', [tpr, D(w, A, 'rpge0d', [tprp], '0 <_ %s' % TP), rmr], '( %s ^c %s ) e. RR' % (TP, RM))
    pwn1r = D(w, A, 'recxpcld', [tpr, D(w, A, 'rpge0d', [tprp], '0 <_ %s' % TP), n1r], '( %s ^c -u 1 ) e. RR' % TP)
    r6 = w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([], '6re', '6 e. RR'), w.s([w.s([], '6re', '6 e. RR'), w.s([], '6pos', '0 < 6')], 'gt0ne0ii', '6 =/= 0')], 'redivcli', '( 1 / 6 ) e. RR')],
             'a1i', '( %s -> ( 1 / 6 ) e. RR )' % A)
    le16 = D(w, A, 'letrd', [pw1r, rec, r6, w.s([le1, e12], 'breqtrd', '( %s -> ( %s ^c %s ) <_ ( 1 / %s ) )' % (A, TP, RM, TP)), le6],
             '( %s ^c %s ) <_ ( 1 / 6 )' % (TP, RM))
    apr = w.s([ap, E(w, A, 'oveq2d', [r5], '( %s ^c ( Re ` %s ) )' % (TP, M), '( %s ^c %s )' % (TP, RM))], 'eqtrd',
              '( %s -> ( abs ` %s ) = ( %s ^c %s ) )' % (A, P, TP, RM))
    apb = w.s([apr, le16], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( 1 / 6 ) )' % (A, P))
    apR = D(w, A, 'abscld', [pc], '( abs ` %s ) e. RR' % P)
    ap0 = D(w, A, 'absge0d', [pc], '0 <_ ( abs ` %s )' % P)
    # | ( 2 P ) V | = ( 2 | P | ) | V |
    G2 = '( 2 x. %s )' % P
    g2c = D(w, A, 'mulcld', [a1(w, A, '2cn', '2 e. CC'), pc], '%s e. CC' % G2)
    m1 = D(w, A, 'absmuld', [g2c, vc], '( abs ` ( %s x. V ) ) = ( ( abs ` %s ) x. ( abs ` V ) )' % (G2, G2))
    m2 = D(w, A, 'absmuld', [a1(w, A, '2cn', '2 e. CC'), pc], '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` %s ) )' % (G2, P))
    m3 = E(w, A, 'oveq1d', [D(w, A, 'absidd', [a1(w, A, '2re', '2 e. RR'), a1(w, A, '0le2', '0 <_ 2')], '( abs ` 2 ) = 2')], '( ( abs ` 2 ) x. ( abs ` %s ) )' % P, '( 2 x. ( abs ` %s ) )' % P)
    m23 = w.s([m2, m3], 'eqtrd', '( %s -> ( abs ` %s ) = ( 2 x. ( abs ` %s ) ) )' % (A, G2, P))
    AP2 = '( 2 x. ( abs ` %s ) )' % P
    m4 = w.s([m1, E(w, A, 'oveq1d', [m23], '( ( abs ` %s ) x. ( abs ` V ) )' % G2, '( %s x. ( abs ` V ) )' % AP2)], 'eqtrd',
             '( %s -> ( abs ` ( %s x. V ) ) = ( %s x. ( abs ` V ) ) )' % (A, G2, AP2))
    ap2r = D(w, A, 'remulcld', [a1(w, A, '2re', '2 e. RR'), apR], '%s e. RR' % AP2)
    ap20 = D(w, A, 'mulge0d', [a1(w, A, '2re', '2 e. RR'), apR, a1(w, A, '0le2', '0 <_ 2'), ap0], '0 <_ %s' % AP2)
    ap2b = linarith(w, A, [apb], '%s <_ ( 1 / 3 )' % AP2, leaves={'( abs ` %s )' % P: apR})
    r3_ = w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([], '3re', '3 e. RR'), w.s([], '3ne0', '3 =/= 0')], 'redivcli', '( 1 / 3 ) e. RR')], 'a1i', '( %s -> ( 1 / 3 ) e. RR )' % A)
    q34 = D(w, A, 'remulcld', [w.s([w.s([w.s([w.s([], '3nn0', '3 e. NN0'), w.s([], '4nn0', '4 e. NN0')], 'deccl', '; 3 4 e. NN0')], 'nn0rei', '; 3 4 e. RR')], 'a1i', '( %s -> ; 3 4 e. RR )' % A), gqr],
            '( ; 3 4 x. %s ) e. RR' % GQZ)
    mm = D(w, A, 'lemul12ad', [ap2r, r3_, av, q34, ap20, av0, ap2b, vb], '( %s x. ( abs ` V ) ) <_ ( ( 1 / 3 ) x. ( ; 3 4 x. %s ) )' % (AP2, GQZ))
    cl = Closure(w, A, {GQZ: ('RR', gqr), '( %s x. ( abs ` V ) )' % AP2: ('RR', D(w, A, 'remulcld', [ap2r, av], '( %s x. ( abs ` V ) ) e. RR' % AP2))})
    cl.atom(GQZ); cl.atom('( %s x. ( abs ` V ) )' % AP2)
    fin = linarith(w, A, [mm, gq0], '( %s x. ( abs ` V ) ) <_ ( ; 1 2 x. %s )' % (AP2, GQZ), closure=cl)
    w.qed([m4, fin], 'eqbrtrd', '( %s -> ( abs ` ( %s x. V ) ) <_ ( ; 1 2 x. %s ) )' % (A, G2, GQZ))
    go(w, only)


# ---------------------------------------------------------------- zl2left
if __name__ == '__main__' and (not only or 'zl2left' in only):
    w = W('zl2left', 'The left edge, generic: a function satisfying the functional-equation form ` F ( z ) = N ^ ( 1/2 - z ) E Q ( z ) G ( 1 - z ) ` '
          'on ` -1/2 <_ Re z < 0 ` with ` | E | = 1 ` , the Gamma-factor bound ` | Q ( z ) | <_ 12 ( | Im z | + 2 ) ^ ( 1/2 - Re z ) ` and the '
          'right-edge bound ` | G ( z ) | <_ A ( 1 + 1 / ( Re z - 1 ) ) ` on ` 1 < Re z ` is bounded by ` 12 A ( 1 + 1 / -Re z ) ( N ( | Im z | + 2 ) ) ^ ( 1/2 - Re z ) ` there '
          '( ~ abscxp , ~ mulcxpd ; Lean ` norm_LFunction_le_left_edge ` with ` LFunction_left_even ` / ` _odd ` as the hypothesis ).')
    A0 = '( ( ( N e. NN /\\ A e. RR ) /\\ ( E e. CC /\\ ( abs ` E ) = 1 ) ) /\\ ( %s /\\ ( %s /\\ %s ) ) )' % (FEQ, QBND, GRGT)
    assert STATEMENTS['zl2left'] == '( %s -> %s )' % (A0, LFT()), STATEMENTS['zl2left']
    nn = D(w, A0, 'simplll', [], 'N e. NN')
    ar = D(w, A0, 'simpllr', [], 'A e. RR')
    ec = D(w, A0, 'simplrl', [], 'E e. CC')
    ae1 = D(w, A0, 'simplrr', [], '( abs ` E ) = 1')
    feq = D(w, A0, 'simprl', [], FEQ)
    qg = D(w, A0, 'simprr', [], '( %s /\\ %s )' % (QBND, GRGT))
    qbnd = D(w, A0, 'simpld', [qg], QBND)
    grgt = D(w, A0, 'simprd', [qg], GRGT)
    Ay = '( %s /\\ y e. CC )' % A0
    RNG = '( -u ( 1 / 2 ) <_ ( Re ` y ) /\\ ( Re ` y ) < 0 )'
    Al = '( %s /\\ %s )' % (Ay, RNG)
    yc = w.s([D(w, Ay, 'simpr', [], 'y e. CC')], 'adantr', '( %s -> y e. CC )' % Al)
    rng = D(w, Al, 'simpr', [], RNG)
    y1 = D(w, Al, 'simpld', [rng], '-u ( 1 / 2 ) <_ ( Re ` y )')
    y2 = D(w, Al, 'simprd', [rng], '( Re ` y ) < 0')
    yr = D(w, Al, 'recld', [yc], '( Re ` y ) e. RR')
    y2le = D(w, Al, 'ltled', [yr, a1(w, Al, '0re', '0 e. RR'), y2], '( Re ` y ) <_ 0')
    L2 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Al, f))
    # the functional equation at y
    fe0, feb = inst_ral_t(w, Al, L2(feq, FEQ), 'CC', FEQ[len('A. z e. CC '):], 'y', yc)
    RHS = '( ( ( N ^c ( ( 1 / 2 ) - y ) ) x. E ) x. ( ( Q ` y ) x. ( G ` ( 1 - y ) ) ) )'
    assert feb == '( %s -> ( F ` y ) = %s )' % (RNG, RHS), feb
    fe = w.s([fe0, rng], 'mpd', '( %s -> ( F ` y ) = %s )' % (Al, RHS))
    # the Gamma-factor bound at y
    qb0, qbb = inst_ral_t(w, Al, L2(qbnd, QBND), 'CC', QBND[len('A. z e. CC '):], 'y', yc)
    GQY = GQ('y')
    qb = w.s([qb0, w.s([y1, y2le], 'jca', '( %s -> ( -u ( 1 / 2 ) <_ ( Re ` y ) /\\ ( Re ` y ) <_ 0 ) )' % Al)], 'mpd',
             '( %s -> ( ( Q ` y ) e. CC /\\ ( abs ` ( Q ` y ) ) <_ ( ; 1 2 x. %s ) ) )' % (Al, GQY))
    qc = D(w, Al, 'simpld', [qb], '( Q ` y ) e. CC')
    qle = D(w, Al, 'simprd', [qb], '( abs ` ( Q ` y ) ) <_ ( ; 1 2 x. %s )' % GQY)
    # the right-edge bound at 1 - y
    OY = '( 1 - y )'
    oyc = D(w, Al, 'subcld', [a1(w, Al, 'ax-1cn', '1 e. CC'), yc], '%s e. CC' % OY)
    gb0, gbb = inst_ral_t(w, Al, L2(grgt, GRGT), 'CC', GRGT[len('A. z e. CC '):], OY, oyc)
    ro1 = D(w, Al, 'resubd', [a1(w, Al, 'ax-1cn', '1 e. CC'), yc], '( Re ` %s ) = ( ( Re ` 1 ) - ( Re ` y ) )' % OY)
    ro2 = E(w, Al, 'oveq1d', [a1(w, Al, 're1', '( Re ` 1 ) = 1')], '( ( Re ` 1 ) - ( Re ` y ) )', '( 1 - ( Re ` y ) )')
    ro = w.s([ro1, ro2], 'eqtrd', '( %s -> ( Re ` %s ) = ( 1 - ( Re ` y ) ) )' % (Al, OY))
    oyr = D(w, Al, 'resubcld', [a1(w, Al, '1re', '1 e. RR'), yr], '( 1 - ( Re ` y ) ) e. RR')
    gt1 = linarith(w, Al, [y2], '1 < ( 1 - ( Re ` y ) )', leaves={'( Re ` y )': yr})
    gt1b = w.s([gt1, w.s([ro], 'breq2d', '( %s -> ( 1 < ( Re ` %s ) <-> 1 < ( 1 - ( Re ` y ) ) ) )' % (Al, OY))], 'mpbird', '( %s -> 1 < ( Re ` %s ) )' % (Al, OY))
    GB = '( A x. ( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) )' % OY
    gb = w.s([gb0, gt1b], 'mpd', '( %s -> ( ( G ` %s ) e. CC /\\ ( abs ` ( G ` %s ) ) <_ %s ) )' % (Al, OY, OY, GB))
    gc = D(w, Al, 'simpld', [gb], '( G ` %s ) e. CC' % OY)
    gle = D(w, Al, 'simprd', [gb], '( abs ` ( G ` %s ) ) <_ %s' % (OY, GB))
    # ( Re ( 1 - y ) - 1 ) = -u Re y
    yrc = D(w, Al, 'recnd', [yr], '( Re ` y ) e. CC')
    s1 = E(w, Al, 'oveq1d', [ro], '( ( Re ` %s ) - 1 )' % OY, '( ( 1 - ( Re ` y ) ) - 1 )')
    s2 = D(w, Al, 'sub32d', [a1(w, Al, 'ax-1cn', '1 e. CC'), yrc, a1(w, Al, 'ax-1cn', '1 e. CC')], '( ( 1 - ( Re ` y ) ) - 1 ) = ( ( 1 - 1 ) - ( Re ` y ) )')
    s3 = E(w, Al, 'oveq1d', [a1(w, Al, '1m1e0', '( 1 - 1 ) = 0')], '( ( 1 - 1 ) - ( Re ` y ) )', '( 0 - ( Re ` y ) )')
    s4 = w.s([w.s([w.s([], 'df-neg', '-u ( Re ` y ) = ( 0 - ( Re ` y ) )')], 'eqcomi', '( 0 - ( Re ` y ) ) = -u ( Re ` y )')], 'a1i', '( %s -> ( 0 - ( Re ` y ) ) = -u ( Re ` y ) )' % Al)
    NR = '-u ( Re ` y )'
    sr = chain(w, Al, ['( ( Re ` %s ) - 1 )' % OY, '( ( 1 - ( Re ` y ) ) - 1 )', '( ( 1 - 1 ) - ( Re ` y ) )', '( 0 - ( Re ` y ) )', NR], [s1, s2, s3, s4])
    TT = '( 1 + ( 1 / %s ) )' % NR
    GB2 = '( A x. %s )' % TT
    gle2 = w.s([gle, E(w, Al, 'oveq2d', [E(w, Al, 'oveq2d', [E(w, Al, 'oveq2d', [sr], '( 1 / ( ( Re ` %s ) - 1 ) )' % OY, '( 1 / %s )' % NR)],
                                                            '( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) )' % OY, TT)], GB, GB2)], 'breqtrd',
               '( %s -> ( abs ` ( G ` %s ) ) <_ %s )' % (Al, OY, GB2))
    # the moduli
    nrp = D(w, Al, 'nnrpd', [L2(nn, 'N e. NN')], 'N e. RR+')
    nr = D(w, Al, 'rpred', [nrp], 'N e. RR')
    nc = D(w, Al, 'rpcnd', [nrp], 'N e. CC')
    HY = '( ( 1 / 2 ) - y )'
    hyc = D(w, Al, 'subcld', [a1(w, Al, 'halfcn', '( 1 / 2 ) e. CC'), yc], '%s e. CC' % HY)
    NP = '( N ^c %s )' % HY
    npc = D(w, Al, 'cxpcld', [nc, hyc], '%s e. CC' % NP)
    ecl = L2(ec, 'E e. CC')
    a1_ = D(w, Al, 'absmuld', [D(w, Al, 'mulcld', [npc, ecl], '( %s x. E ) e. CC' % NP), D(w, Al, 'mulcld', [qc, gc], '( ( Q ` y ) x. ( G ` %s ) ) e. CC' % OY)],
            '( abs ` %s ) = ( ( abs ` ( %s x. E ) ) x. ( abs ` ( ( Q ` y ) x. ( G ` %s ) ) ) )' % (RHS, NP, OY))
    a2 = D(w, Al, 'absmuld', [npc, ecl], '( abs ` ( %s x. E ) ) = ( ( abs ` %s ) x. ( abs ` E ) )' % (NP, NP))
    a3 = D(w, Al, 'absmuld', [qc, gc], '( abs ` ( ( Q ` y ) x. ( G ` %s ) ) ) = ( ( abs ` ( Q ` y ) ) x. ( abs ` ( G ` %s ) ) )' % (OY, OY))
    ax = w.s([nrp, hyc, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( N ^c ( Re ` %s ) ) )' % (Al, NP, HY))
    rh1 = D(w, Al, 'resubd', [a1(w, Al, 'halfcn', '( 1 / 2 ) e. CC'), yc], '( Re ` %s ) = ( ( Re ` ( 1 / 2 ) ) - ( Re ` y ) )' % HY)
    rh2 = E(w, Al, 'oveq1d', [D(w, Al, 'rered', [a1(w, Al, 'halfre', '( 1 / 2 ) e. RR')], '( Re ` ( 1 / 2 ) ) = ( 1 / 2 )')], '( ( Re ` ( 1 / 2 ) ) - ( Re ` y ) )', '( ( 1 / 2 ) - ( Re ` y ) )')
    EX = '( ( 1 / 2 ) - ( Re ` y ) )'
    rh = w.s([rh1, rh2], 'eqtrd', '( %s -> ( Re ` %s ) = %s )' % (Al, HY, EX))
    NE = '( N ^c %s )' % EX
    axe = w.s([ax, E(w, Al, 'oveq2d', [rh], '( N ^c ( Re ` %s ) )' % HY, NE)], 'eqtrd', '( %s -> ( abs ` %s ) = %s )' % (Al, NP, NE))
    exr = D(w, Al, 'resubcld', [a1(w, Al, 'halfre', '( 1 / 2 ) e. RR'), yr], '%s e. RR' % EX)
    nerp = D(w, Al, 'rpcxpcld', [nrp, exr], '%s e. RR+' % NE)
    ner = D(w, Al, 'rpred', [nerp], '%s e. RR' % NE)
    ne0 = D(w, Al, 'rpge0d', [nerp], '0 <_ %s' % NE)
    a2b = w.s([a2, E(w, Al, 'oveq12d', [axe, L2(ae1, '( abs ` E ) = 1')], '( ( abs ` %s ) x. ( abs ` E ) )' % NP, '( %s x. 1 )' % NE)], 'eqtrd',
              '( %s -> ( abs ` ( %s x. E ) ) = ( %s x. 1 ) )' % (Al, NP, NE))
    a2c = w.s([a2b, D(w, Al, 'mulridd', [D(w, Al, 'recnd', [ner], '%s e. CC' % NE)], '( %s x. 1 ) = %s' % (NE, NE))], 'eqtrd',
              '( %s -> ( abs ` ( %s x. E ) ) = %s )' % (Al, NP, NE))
    QG = '( ( abs ` ( Q ` y ) ) x. ( abs ` ( G ` %s ) ) )' % OY
    mod = w.s([a1_, E(w, Al, 'oveq12d', [a2c, a3], '( ( abs ` ( %s x. E ) ) x. ( abs ` ( ( Q ` y ) x. ( G ` %s ) ) ) )' % (NP, OY), '( %s x. %s )' % (NE, QG))], 'eqtrd',
              '( %s -> ( abs ` %s ) = ( %s x. %s ) )' % (Al, RHS, NE, QG))
    fmod = w.s([E(w, Al, 'fveq2d', [fe], '( abs ` ( F ` y ) )', '( abs ` %s )' % RHS), mod], 'eqtrd', '( %s -> ( abs ` ( F ` y ) ) = ( %s x. %s ) )' % (Al, NE, QG))
    # the bound
    aq = D(w, Al, 'abscld', [qc], '( abs ` ( Q ` y ) ) e. RR')
    aq0 = D(w, Al, 'absge0d', [qc], '0 <_ ( abs ` ( Q ` y ) )')
    ag = D(w, Al, 'abscld', [gc], '( abs ` ( G ` %s ) ) e. RR' % OY)
    ag0 = D(w, Al, 'absge0d', [gc], '0 <_ ( abs ` ( G ` %s ) )' % OY)
    iyc = D(w, Al, 'recnd', [D(w, Al, 'imcld', [yc], '( Im ` y ) e. RR')], '( Im ` y ) e. CC')
    aiy = D(w, Al, 'abscld', [iyc], '( abs ` ( Im ` y ) ) e. RR')
    aiy0 = D(w, Al, 'absge0d', [iyc], '0 <_ ( abs ` ( Im ` y ) )')
    Qd = '( ( abs ` ( Im ` y ) ) + 2 )'
    qdr = D(w, Al, 'readdcld', [aiy, a1(w, Al, '2re', '2 e. RR')], '%s e. RR' % Qd)
    qd0 = linarith(w, Al, [aiy0], '0 <_ %s' % Qd, leaves={'( abs ` ( Im ` y ) )': aiy})
    gqr = D(w, Al, 'recxpcld', [qdr, qd0, exr], '%s e. RR' % GQY)
    gq0 = D(w, Al, 'cxpge0d', [qdr, qd0, exr], '0 <_ %s' % GQY)
    Q12 = '( ; 1 2 x. %s )' % GQY
    q12r = D(w, Al, 'remulcld', [w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0rei', '; 1 2 e. RR')], 'a1i', '( %s -> ; 1 2 e. RR )' % Al), gqr],
             '%s e. RR' % Q12)
    q120 = D(w, Al, 'mulge0d', [w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0rei', '; 1 2 e. RR')], 'a1i', '( %s -> ; 1 2 e. RR )' % Al), gqr,
                                 w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '2nn0', '2 e. NN0')], 'deccl', '; 1 2 e. NN0')], 'nn0ge0i', '0 <_ ; 1 2')], 'a1i', '( %s -> 0 <_ ; 1 2 )' % Al), gq0],
              '0 <_ %s' % Q12)
    nrr = D(w, Al, 'renegcld', [yr], '%s e. RR' % NR)
    nrne = D(w, Al, 'negne0d', [yrc, D(w, Al, 'ltned', [yr, y2], '( Re ` y ) =/= 0')], '%s =/= 0' % NR)
    rcr = D(w, Al, 'rereccld', [nrr, nrne], '( 1 / %s ) e. RR' % NR)
    ttr = D(w, Al, 'readdcld', [a1(w, Al, '1re', '1 e. RR'), rcr], '%s e. RR' % TT)
    gb2r = D(w, Al, 'remulcld', [L2(ar, 'A e. RR'), ttr], '%s e. RR' % GB2)
    pr = D(w, Al, 'lemul12ad', [aq, q12r, ag, gb2r, aq0, ag0, qle, gle2], '%s <_ ( %s x. %s )' % (QG, Q12, GB2))
    qgr = D(w, Al, 'remulcld', [aq, ag], '%s e. RR' % QG)
    pr2 = D(w, Al, 'lemul2ad', [qgr, D(w, Al, 'remulcld', [q12r, gb2r], '( %s x. %s ) e. RR' % (Q12, GB2)), ner, ne0, pr],
            '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (NE, QG, NE, Q12, GB2))
    fb = w.s([fmod, pr2], 'eqbrtrd', '( %s -> ( abs ` ( F ` y ) ) <_ ( %s x. ( %s x. %s ) ) )' % (Al, NE, Q12, GB2))
    # rearrange: N ^c e ( 12 GQ ( A t ) ) = ( ( 12 A ) t ) ( N ^c e GQ )
    TGT = '( ( ( ; 1 2 x. A ) x. %s ) x. ( %s x. %s ) )' % (TT, NE, GQY)
    afy = D(w, Al, 'abscld', [D(w, Al, 'mulcld', [D(w, Al, 'mulcld', [npc, ecl], '( %s x. E ) e. CC' % NP), D(w, Al, 'mulcld', [qc, gc], '( ( Q ` y ) x. ( G ` %s ) ) e. CC' % OY)], '%s e. CC' % RHS)],
             '( abs ` %s ) e. RR' % RHS)
    afy2 = w.s([w.s([fe], 'fveq2d', '( %s -> ( abs ` ( F ` y ) ) = ( abs ` %s ) )' % (Al, RHS)), afy], 'eqeltrd', '( %s -> ( abs ` ( F ` y ) ) e. RR )' % Al)
    cl = Closure(w, Al, {'( abs ` ( F ` y ) )': ('RR', afy2), NE: ('RR', ner), GQY: ('RR', gqr), 'A': ('RR', L2(ar, 'A e. RR')), '( 1 / %s )' % NR: ('RR', rcr)})
    for t in [NE, GQY, '( 1 / %s )' % NR]:
        cl.atom(t)
    fb2 = linarith(w, Al, [fb], '( abs ` ( F ` y ) ) <_ %s' % TGT, closure=cl, products=True)
    QT_ = QT('y')
    mc = D(w, Al, 'mulcxpd', [nr, D(w, Al, 'rpge0d', [nrp], '0 <_ N'), qdr, qd0, D(w, Al, 'recnd', [exr], '%s e. CC' % EX)], '( %s ^c %s ) = ( %s x. %s )' % (QT_, EX, NE, GQY))
    LB = LFTB('y')
    assert LB == '( ( ( ; 1 2 x. A ) x. %s ) x. ( %s ^c %s ) )' % (TT, QT_, EX), LB
    fb3 = w.s([fb2, E(w, Al, 'oveq2d', [w.s([mc], 'eqcomd', '( %s -> ( %s x. %s ) = ( %s ^c %s ) )' % (Al, NE, GQY, QT_, EX))], TGT, LB)], 'breqtrd',
              '( %s -> ( abs ` ( F ` y ) ) <_ %s )' % (Al, LB))
    ex_ = w.s([fb3], 'ex', '( %s -> ( %s -> ( abs ` ( F ` y ) ) <_ %s ) )' % (Ay, RNG, LB))
    BODY = '( %s -> ( abs ` ( F ` y ) ) <_ %s )' % (RNG, LB)
    raly = w.s([ex_], 'ralrimiva', '( %s -> A. y e. CC %s )' % (A0, BODY))
    fin, val = cbv_yz(w, A0, raly, 'CC', BODY)
    assert 'A. z e. CC %s' % val == LFT(), (val, LFT())
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    go(w, only)
