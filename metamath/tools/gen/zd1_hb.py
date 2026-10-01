"""Sortie ZD1: the block-weighted I4* sum (Lean sigma_diag_le's hA and hbound)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zd1lib import *
from cl import lift

LXP = '( log ` %s )' % XP


def zdhterm():
    w = W('zdhterm', "One block of sigma_diag_le (Lean hA and the summand of hbound): e ^ -J sum_ n <_ 2 ^ J X f ( n ) <_ K e ^ ( - J / 4 ) with "
                     "K = 500000 X ^ ( 2 - 2 T ) ( log X + 3 ) / ell, by I4* at Y = 2 ^ J X (zdl2star) and the block weight (zdblkw).")
    ante = '( %s /\\ J e. NN0 )' % H0
    st = mkst(w, ante)
    h0 = st([], 'simpl', H0); jn = st([], 'simpr', 'J e. NN0')
    f = h0facts(w, ante, h0)
    jz = st([jn], 'nn0zd', 'J e. ZZ'); jr = st([jn], 'nn0red', 'J e. RR')
    P = '( 2 ^ J )'; Y = '( %s x. %s )' % (P, XP)
    prp = st([a1c(w, ante, '2rp', '2 e. RR+'), jz], 'rpexpcld', '%s e. RR+' % P); pr = st([prp], 'rpred', '%s e. RR' % P)
    yrp = st([prp, f['xprp']], 'rpmulcld', '%s e. RR+' % Y); yr = st([yrp], 'rpred', '%s e. RR' % Y)
    p1 = st([a1c(w, ante, '2re', '2 e. RR'), jn, a1c(w, ante, '1le2', '1 <_ 2')], 'expge1d', '1 <_ %s' % P)
    m = st([st([], '1red', '1 e. RR'), pr, f['xpr'], st([f['xprp']], 'rpge0d', '0 <_ %s' % XP), p1], 'lemul1ad', '( 1 x. %s ) <_ %s' % (XP, Y))
    xy = st([st([st([f['xpr']], 'recnd', '%s e. CC' % XP)], 'mullidd', '( 1 x. %s ) = %s' % (XP, XP)), m], 'eqbrtrrd', '%s <_ %s' % (XP, Y))
    zy = linarith(w, ante, [f['zx'], xy], '%s <_ %s' % (Z1, Y), leaves={Z1: f['z1r'], XP: f['xpr'], Y: yr})
    HDs = bind(w, ante, bind(w, ante, f['dr'], f['d1'], 'D e. RR', '1 < D'),
               bind(w, ante, f['z100'], bind(w, ante, yr, zy, '%s e. RR' % Y, '%s <_ %s' % (Z1, Y)), '; ; 1 0 0 <_ %s' % Z1, '( %s e. RR /\\ %s <_ %s )' % (Y, Z1, Y)),
               '( D e. RR /\\ 1 < D )', '( ; ; 1 0 0 <_ %s /\\ ( %s e. RR /\\ %s <_ %s ) )' % (Z1, Y, Z1, Y))
    HTs = bind(w, ante, f['tr'], bind(w, ante, f['th'], f['t1'], '( 1 / 2 ) <_ T', 'T <_ 1'), 'T e. RR', '( ( 1 / 2 ) <_ T /\\ T <_ 1 )')
    YB = '( %s ^c %s )' % (Y, B2)
    LY = '( log ` %s )' % Y
    RHSY = '( ( ( %s x. %s ) x. %s ) / %s )' % (C5, YB, LY, ELLD)
    l2 = st([HDs, HTs, w.inst('zdl2star')], 'syl2anc', '%s <_ %s' % (SJ('J'), RHSY))
    EJ = '( exp ` -u J )'
    ejr = st([st([jr], 'renegcld', '-u J e. RR')], 'reefcld', '%s e. RR' % EJ)
    ej0 = st([st([st([jr], 'renegcld', '-u J e. RR')], 'rpefcld', '%s e. RR+' % EJ)], 'rpge0d', '0 <_ %s' % EJ)
    # closures
    fin = st([], 'fzfid', '( 1 ... ( |_ ` %s ) ) e. Fin' % Y)
    AF = '( %s /\\ n e. ( 1 ... ( |_ ` %s ) ) )' % (ante, Y)
    sf = mkst(w, AF)
    nn = w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... ( |_ ` %s ) ) )' % (AF, Y)), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AF)
    DVn = '{ x e. NN | x || n }'
    sjr = st([fin, fnre(w, AF, nn, lift(w, f['dr'], AF), lift(w, f['d1'], AF), lift(w, f['tr'], AF))], 'fsumrecl', '%s e. RR' % SJ('J'))
    ellr = st([litr(w, ante, '( 1 / ; ; 1 0 0 )'), f['lr']], 'remulcld', '%s e. RR' % ELLD)
    ell0 = linarith(w, ante, [f['l200']], '0 < %s' % ELLD, leaves={'( log ` D )': f['lr']})
    ellrp = st([ellr, ell0], 'elrpd', '%s e. RR+' % ELLD)
    ybr = st([st([yrp, f['br']], 'rpcxpcld', '%s e. RR+' % YB)], 'rpred', '%s e. RR' % YB)
    lyr = st([yrp], 'relogcld', '%s e. RR' % LY)
    c5r = litr(w, ante, C5)
    Q = '( ( %s x. %s ) x. %s )' % (C5, YB, LY)
    qr = st([st([c5r, ybr], 'remulcld', '( %s x. %s ) e. RR' % (C5, YB)), lyr], 'remulcld', '%s e. RR' % Q)
    rhsr = st([qr, ellrp], 'rerpdivcld', '%s e. RR' % RHSY)
    s1 = st([sjr, rhsr, ejr, ej0, l2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (EJ, SJ('J'), EJ, RHSY))
    # e ^ -J ( Q / ell ) = ( C5 W1 ) / ell
    W1 = '( ( %s x. %s ) x. %s )' % (EJ, YB, LY)
    w1r = st([st([ejr, ybr], 'remulcld', '( %s x. %s ) e. RR' % (EJ, YB)), lyr], 'remulcld', '%s e. RR' % W1)
    e1 = st([st([ejr], 'recnd', '%s e. CC' % EJ), st([qr], 'recnd', '%s e. CC' % Q), st([ellrp], 'rpcnd', '%s e. CC' % ELLD), st([ellrp], 'rpne0d', '%s =/= 0' % ELLD)],
            'divassd', '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (EJ, Q, ELLD, EJ, RHSY))
    e2 = lineq(w, ante, '( %s x. %s )' % (EJ, Q), '( %s x. %s )' % (C5, W1), products=True, leaves={EJ: ejr, YB: ybr, LY: lyr})
    e3 = st([e2], 'oveq1d', '( ( %s x. %s ) / %s ) = ( ( %s x. %s ) / %s )' % (EJ, Q, ELLD, C5, W1, ELLD))
    eqa = st([e1, e3], 'eqtr3d', '( %s x. %s ) = ( ( %s x. %s ) / %s )' % (EJ, RHSY, C5, W1, ELLD))
    # zdblkw
    E4 = '( exp ` ( -u J / 4 ) )'
    W2 = '( ( %s x. %s ) x. ( %s + 3 ) )' % (E4, XB, LXP)
    bw = st([bind(w, ante, f['xpr'], f['x1'], '%s e. RR' % XP, '1 <_ %s' % XP),
             bind(w, ante, f['br'], bind(w, ante, f['b0'], f['b50'], '0 <_ %s' % B2, '%s <_ ( 1 / ; 5 0 )' % B2), '%s e. RR' % B2,
                  '( 0 <_ %s /\\ %s <_ ( 1 / ; 5 0 ) )' % (B2, B2)), jn, w.inst('zdblkw')], 'syl3anc', '%s <_ %s' % (W1, W2))
    q4r = st([st([jr], 'renegcld', '-u J e. RR'), a1c(w, ante, '4re', '4 e. RR'), a1c(w, ante, '4ne0', '4 =/= 0')], 'redivcld', '( -u J / 4 ) e. RR')
    e4r = st([q4r], 'reefcld', '%s e. RR' % E4)
    xbr = st([st([f['xprp'], f['br']], 'rpcxpcld', '%s e. RR+' % XB)], 'rpred', '%s e. RR' % XB)
    lxpr = st([f['xprp']], 'relogcld', '%s e. RR' % LXP)
    w2r = st([st([e4r, xbr], 'remulcld', '( %s x. %s ) e. RR' % (E4, XB)), st([lxpr, litr(w, ante, '3')], 'readdcld', '( %s + 3 ) e. RR' % LXP)], 'remulcld', '%s e. RR' % W2)
    m2 = st([w1r, w2r, c5r, litle(w, ante, '0', C5), bw], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (C5, W1, C5, W2))
    m3 = st([st([c5r, w1r], 'remulcld', '( %s x. %s ) e. RR' % (C5, W1)), st([c5r, w2r], 'remulcld', '( %s x. %s ) e. RR' % (C5, W2)), ellrp, m2], 'lediv1dd',
            '( ( %s x. %s ) / %s ) <_ ( ( %s x. %s ) / %s )' % (C5, W1, ELLD, C5, W2, ELLD))
    # ( C5 W2 ) / ell = KK E4
    NUMK = '( %s x. ( %s x. ( %s + 3 ) ) )' % (C5, XB, LXP)
    numr = st([c5r, st([xbr, st([lxpr, litr(w, ante, '3')], 'readdcld', '( %s + 3 ) e. RR' % LXP)], 'remulcld', '( %s x. ( %s + 3 ) ) e. RR' % (XB, LXP))], 'remulcld', '%s e. RR' % NUMK)
    e5 = lineq(w, ante, '( %s x. %s )' % (C5, W2), '( %s x. %s )' % (NUMK, E4), products=True, leaves={E4: e4r, XB: xbr, LXP: lxpr})
    e6 = st([e5], 'oveq1d', '( ( %s x. %s ) / %s ) = ( ( %s x. %s ) / %s )' % (C5, W2, ELLD, NUMK, E4, ELLD))
    e7 = st([st([numr], 'recnd', '%s e. CC' % NUMK), st([e4r], 'recnd', '%s e. CC' % E4), st([ellrp], 'rpcnd', '%s e. CC' % ELLD), st([ellrp], 'rpne0d', '%s =/= 0' % ELLD)],
            'div23d', '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (NUMK, E4, ELLD, KK, E4))
    eqb = st([e6, e7], 'eqtrd', '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (C5, W2, ELLD, KK, E4))
    t = st([st([s1, eqa], 'breqtrd', '( %s x. %s ) <_ ( ( %s x. %s ) / %s )' % (EJ, SJ('J'), C5, W1, ELLD)), m3], 'letrd',
           '( %s x. %s ) <_ ( ( %s x. %s ) / %s )' % (EJ, SJ('J'), C5, W2, ELLD))
    w.qed([t, eqb], 'breqtrd', STATEMENTS['zdhterm'])
    return w


def zdhnum():
    w = W('zdhnum', "The numerals of Lean hbound: 5 K <_ ( 10 ^ 9 / 3 ) X ^ ( 2 - 2 T ) for log D >_ 200, K = 500000 X ^ ( 2 - 2 T ) ( log X + 3 ) / ( log D / 100 ), "
                    "log X = ( 6 / 5 ) log D.")
    ante = H0
    st = mkst(w, ante)
    f = h0facts(w, ante, w.s([], 'id', '( %s -> %s )' % (ante, ante)))
    L = '( log ` D )'
    lx = st([f['drp'], litr(w, ante, '( 6 / 5 )')], 'logcxpd', '%s = ( ( 6 / 5 ) x. %s )' % (LXP, L))
    lxpr = st([f['xprp']], 'relogcld', '%s e. RR' % LXP)
    xbrp = st([f['xprp'], f['br']], 'rpcxpcld', '%s e. RR+' % XB); xbr = st([xbrp], 'rpred', '%s e. RR' % XB)
    CL = '( 5 x. ( %s x. ( %s + 3 ) ) )' % (C5, LXP)
    CR = '( %s x. %s )' % (C12T, ELLD)
    core = linarith(w, ante, [lx, f['l200']], '%s <_ %s' % (CL, CR), leaves={L: f['lr'], LXP: lxpr})
    clr = st([litr(w, ante, '5'), st([litr(w, ante, C5), st([lxpr, litr(w, ante, '3')], 'readdcld', '( %s + 3 ) e. RR' % LXP)], 'remulcld',
                                       '( %s x. ( %s + 3 ) ) e. RR' % (C5, LXP))], 'remulcld', '%s e. RR' % CL)
    ellr = st([litr(w, ante, '( 1 / ; ; 1 0 0 )'), f['lr']], 'remulcld', '%s e. RR' % ELLD)
    ell0 = linarith(w, ante, [f['l200']], '0 < %s' % ELLD, leaves={L: f['lr']})
    ellrp = st([ellr, ell0], 'elrpd', '%s e. RR+' % ELLD)
    crr = st([litr(w, ante, C12T), ellr], 'remulcld', '%s e. RR' % CR)
    m = st([clr, crr, xbr, st([xbrp], 'rpge0d', '0 <_ %s' % XB), core], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (CL, XB, CR, XB))
    NUM = '( %s x. ( %s x. ( %s + 3 ) ) )' % (C5, XB, LXP)
    N5 = '( 5 x. %s )' % NUM
    B_ = '( %s x. %s )' % (C12T, XB)
    eqL = lineq(w, ante, N5, '( %s x. %s )' % (CL, XB), products=True, leaves={XB: xbr, LXP: lxpr})
    eqR = lineq(w, ante, '( %s x. %s )' % (B_, ELLD), '( %s x. %s )' % (CR, XB), products=True, leaves={XB: xbr, L: f['lr']})
    n5 = st([st([eqL, m], 'eqbrtrd', '%s <_ ( %s x. %s )' % (N5, CR, XB)), eqR], 'breqtrrd', '%s <_ ( %s x. %s )' % (N5, B_, ELLD))
    numr = st([litr(w, ante, C5), st([xbr, st([lxpr, litr(w, ante, '3')], 'readdcld', '( %s + 3 ) e. RR' % LXP)], 'remulcld', '( %s x. ( %s + 3 ) ) e. RR' % (XB, LXP))],
              'remulcld', '%s e. RR' % NUM)
    n5r = st([litr(w, ante, '5'), numr], 'remulcld', '%s e. RR' % N5)
    br_ = st([litr(w, ante, C12T), xbr], 'remulcld', '%s e. RR' % B_)
    bi = st([n5r, br_, ellrp], 'ledivmul2d', '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (N5, ELLD, B_, N5, B_, ELLD))
    q = st([n5, bi], 'mpbird', '( %s / %s ) <_ %s' % (N5, ELLD, B_))
    e = st([a1c(w, ante, '5cn', '5 e. CC'), st([numr], 'recnd', '%s e. CC' % NUM), st([ellrp], 'rpcnd', '%s e. CC' % ELLD), st([ellrp], 'rpne0d', '%s =/= 0' % ELLD)],
           'divassd', '( %s / %s ) = ( 5 x. %s )' % (N5, ELLD, KK))
    w.qed([e, q], 'eqbrtrrd', STATEMENTS['zdhnum'])
    return w


def zdhbound():
    w = W('zdhbound', "The block-weighted I4* sum (Lean hbound of sigma_diag_le): sum_ j <_ J e ^ -j sum_ n <_ 2 ^ j X f ( n ) <_ ( 10 ^ 9 / 3 ) X ^ ( 2 - 2 T ) "
                      "(zdhterm, zdgeo4, zdhnum).")
    ante = '( %s /\\ J e. NN0 )' % H0
    st = mkst(w, ante)
    h0 = st([], 'simpl', H0); jn = st([], 'simpr', 'J e. NN0')
    f = h0facts(w, ante, h0)
    R = '( 0 ... J )'
    AJ = '( %s /\\ j e. %s )' % (ante, R)
    sj = mkst(w, AJ)
    jj = w.s([w.s([], 'simpr', '( %s -> j e. %s )' % (AJ, R)), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % AJ)
    h0j = lift(w, h0, AJ)
    E4 = '( exp ` ( -u j / 4 ) )'
    T_ = '( ( exp ` -u j ) x. %s )' % SJ('j')
    tb = w.s([h0j, jj, w.inst('zdhterm')], 'syl2anc', '( %s -> %s <_ ( %s x. %s ) )' % (AJ, T_, KK, E4))
    jr = sj([jj], 'nn0red', 'j e. RR')
    # SJ(j) real
    Y = '( ( 2 ^ j ) x. %s )' % XP
    AF = '( %s /\\ n e. ( 1 ... ( |_ ` %s ) ) )' % (AJ, Y)
    nn = w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... ( |_ ` %s ) ) )' % (AF, Y)), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AF)
    fr = fnre(w, AF, nn, lift(w, f['dr'], AF), lift(w, f['d1'], AF), lift(w, f['tr'], AF))
    sjr = sj([sj([], 'fzfid', '( 1 ... ( |_ ` %s ) ) e. Fin' % Y), fr], 'fsumrecl', '%s e. RR' % SJ('j'))
    tr_ = sj([sj([sj([jr], 'renegcld', '-u j e. RR')], 'reefcld', '( exp ` -u j ) e. RR'), sjr], 'remulcld', '%s e. RR' % T_)
    q4r = sj([sj([jr], 'renegcld', '-u j e. RR'), a1c(w, AJ, '4re', '4 e. RR'), a1c(w, AJ, '4ne0', '4 =/= 0')], 'redivcld', '( -u j / 4 ) e. RR')
    e4r = sj([q4r], 'reefcld', '%s e. RR' % E4)
    # KK real, >= 0
    L = '( log ` D )'
    lxpr = st([f['xprp']], 'relogcld', '%s e. RR' % LXP)
    lx = st([f['drp'], litr(w, ante, '( 6 / 5 )')], 'logcxpd', '%s = ( ( 6 / 5 ) x. %s )' % (LXP, L))
    lx0 = linarith(w, ante, [lx, f['l200']], '0 <_ ( %s + 3 )' % LXP, leaves={L: f['lr'], LXP: lxpr})
    xbrp = st([f['xprp'], f['br']], 'rpcxpcld', '%s e. RR+' % XB); xbr = st([xbrp], 'rpred', '%s e. RR' % XB)
    NUM = '( %s x. ( %s x. ( %s + 3 ) ) )' % (C5, XB, LXP)
    l3 = st([lxpr, litr(w, ante, '3')], 'readdcld', '( %s + 3 ) e. RR' % LXP)
    in_ = st([xbr, l3], 'remulcld', '( %s x. ( %s + 3 ) ) e. RR' % (XB, LXP))
    numr = st([litr(w, ante, C5), in_], 'remulcld', '%s e. RR' % NUM)
    num0 = st([litr(w, ante, C5), in_, litle(w, ante, '0', C5), st([xbr, l3, st([xbrp], 'rpge0d', '0 <_ %s' % XB), lx0], 'mulge0d',
                                                                  '0 <_ ( %s x. ( %s + 3 ) )' % (XB, LXP))], 'mulge0d', '0 <_ %s' % NUM)
    ellr = st([litr(w, ante, '( 1 / ; ; 1 0 0 )'), f['lr']], 'remulcld', '%s e. RR' % ELLD)
    ell0 = linarith(w, ante, [f['l200']], '0 < %s' % ELLD, leaves={L: f['lr']})
    ellrp = st([ellr, ell0], 'elrpd', '%s e. RR+' % ELLD)
    kkr = st([numr, ellrp], 'rerpdivcld', '%s e. RR' % KK)
    kk0 = st([numr, ellrp, num0], 'divge0d', '0 <_ %s' % KK)
    fin = st([], 'fzfid', '%s e. Fin' % R)
    s1 = st([fin, tr_, sj([lift(w, kkr, AJ), e4r], 'remulcld', '( %s x. %s ) e. RR' % (KK, E4)), tb], 'fsumle',
            'sum_ j e. %s %s <_ sum_ j e. %s ( %s x. %s )' % (R, T_, R, KK, E4))
    SE = 'sum_ j e. %s %s' % (R, E4)
    mc = st([fin, st([kkr], 'recnd', '%s e. CC' % KK), w.s([e4r], 'recnd', '( %s -> %s e. CC )' % (AJ, E4))], 'fsummulc2',
            '( %s x. %s ) = sum_ j e. %s ( %s x. %s )' % (KK, SE, R, KK, E4))
    g = st([jn, w.inst('zdgeo4')], 'syl', '%s <_ 5' % SE)
    ser = st([fin, e4r], 'fsumrecl', '%s e. RR' % SE)
    m = st([ser, litr(w, ante, '5'), kkr, kk0, g], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 5 )' % (KK, SE, KK))
    hn = st([h0, w.inst('zdhnum')], 'syl', '( 5 x. %s ) <_ ( %s x. %s )' % (KK, C12T, XB))
    S1 = 'sum_ j e. %s %s' % (R, T_)
    s1r = st([fin, tr_], 'fsumrecl', '%s e. RR' % S1)
    fin_ = linarith(w, ante, [st([s1, mc], 'breqtrrd', '%s <_ ( %s x. %s )' % (S1, KK, SE)), m, hn], '%s <_ ( %s x. %s )' % (S1, C12T, XB),
                    leaves={S1: s1r, '( %s x. %s )' % (KK, SE): st([kkr, ser], 'remulcld', '( %s x. %s ) e. RR' % (KK, SE)), KK: kkr, XB: xbr}, name='qed')
    return w


def zdsigfin():
    w = W('zdsigfin', "The finite form of Lemma 8.1 (Lean sigma_diag_le's final calc): sum_ n <_ M f ( n ) e ^ ( - n / X ) <_ ( 10 ^ 9 / 3 ) X ^ ( 2 - 2 T ) "
                      "for every M, by the blocks at J = M (zdblocks, M <_ 2 ^ M X) and zdhbound.")
    ante = '( %s /\\ M e. NN )' % H0
    st = mkst(w, ante)
    h0 = st([], 'simpl', H0); mn = st([], 'simpr', 'M e. NN')
    f = h0facts(w, ante, h0)
    AN = '( %s /\\ n e. NN )' % ante
    nn = w.s([], 'simpr', '( %s -> n e. NN )' % AN)
    sa = mkst(w, AN)
    fr = fnre(w, AN, nn, lift(w, f['dr'], AN), lift(w, f['d1'], AN), lift(w, f['tr'], AN))
    b1r = sa([sa([], '1red', '1 e. RR'), sa([a1c(w, AN, '2re', '2 e. RR'), lift(w, f['tr'], AN)], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B1)
    pwp = sa([sa([nn], 'nnrpd', 'n e. RR+'), b1r], 'rpcxpcld', '( n ^c %s ) e. RR+' % B1)
    bar = w.s([bind(w, AN, lift(w, f['dr'], AN), lift(w, f['d1'], AN), 'D e. RR', '1 < D'), nn, w.inst('zdbvare')], 'syl2anc', '( %s -> %s e. RR )' % (AN, BA('n')))
    f0 = sa([sa([pwp], 'rpred', '( n ^c %s ) e. RR' % B1), sa([bar], 'resqcld', '( %s ^ 2 ) e. RR' % BA('n')), sa([pwp], 'rpge0d', '0 <_ ( n ^c %s )' % B1),
             sa([bar], 'sqge0d', '0 <_ ( %s ^ 2 )' % BA('n'))], 'mulge0d', '0 <_ %s' % FN('n'))
    mn0 = st([mn], 'nnnn0d', 'M e. NN0')
    blk = w.s([f['xprp'], fr, f0], 'zdblocks', '( ( %s /\\ M e. NN0 ) -> %s <_ %s )' % (ante, BLK_L('M', XP, FN('n')), BLK_R('M', XP, FN('n'))))
    b1 = st([w.s([], 'id', '( %s -> %s )' % (ante, ante)), mn0, blk], 'syl2anc', '%s <_ %s' % (BLK_L('M', XP, FN('n')), BLK_R('M', XP, FN('n'))))
    hb = st([h0, mn0, w.inst('zdhbound')], 'syl2anc', '%s <_ ( %s x. %s )' % (BLK_R('M', XP, FN('n')), C12T, XB))
    # ( 1 ... M ) C_ ( 1 ... NM )
    P = '( 2 ^ M )'; Y = '( %s x. %s )' % (P, XP); NM = '( |_ ` %s )' % Y
    mr = st([mn], 'nnred', 'M e. RR'); mz = st([mn], 'nnzd', 'M e. ZZ')
    prp = st([a1c(w, ante, '2rp', '2 e. RR+'), mz], 'rpexpcld', '%s e. RR+' % P); pr = st([prp], 'rpred', '%s e. RR' % P)
    yrp = st([prp, f['xprp']], 'rpmulcld', '%s e. RR+' % Y); yr = st([yrp], 'rpred', '%s e. RR' % Y)
    tp = sy(w, ante, mn0, 'tpl2pow', '( M + 1 ) <_ %s' % P)
    m1 = st([st([], '1red', '1 e. RR'), f['xpr'], pr, st([prp], 'rpge0d', '0 <_ %s' % P), f['x1']], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (P, P, XP))
    my = linarith(w, ante, [tp, m1], 'M <_ %s' % Y, leaves={'M': mr, P: pr, Y: yr})
    fl = st([my, st([yr, mz, w.inst('flge')], 'syl2anc', '( M <_ %s <-> M <_ %s )' % (Y, NM))], 'mpbid', 'M <_ %s' % NM)
    nmz = st([yr], 'flcld', '%s e. ZZ' % NM)
    uz = st([st([mz, nmz, fl], '3jca', '( M e. ZZ /\\ %s e. ZZ /\\ M <_ %s )' % (NM, NM)), w.s([], 'eluz2', '( %s e. ( ZZ>= ` M ) <-> ( M e. ZZ /\\ %s e. ZZ /\\ M <_ %s ) )' % (NM, NM, NM))],
            'sylibr', '%s e. ( ZZ>= ` M )' % NM)
    ss = sy(w, ante, uz, 'fzss2', '( 1 ... M ) C_ ( 1 ... %s )' % NM)
    RB = '( 1 ... %s )' % NM
    AR = '( %s /\\ n e. %s )' % (ante, RB)
    sr = mkst(w, AR)
    nnr = w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (AR, RB)), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AR)
    frr = fnre(w, AR, nnr, lift(w, f['dr'], AR), lift(w, f['d1'], AR), lift(w, f['tr'], AR))
    xrp_r = lift(w, f['xprp'], AR)
    ndx = sr([sr([sr([nnr], 'nnred', 'n e. RR')], 'renegcld', '-u n e. RR'), xrp_r], 'rerpdivcld', '( -u n / %s ) e. RR' % XP)
    enr = sr([ndx], 'reefcld', '%s e. RR' % EN('n'))
    en0 = sr([sr([ndx], 'rpefcld', '%s e. RR+' % EN('n'))], 'rpge0d', '0 <_ %s' % EN('n'))
    b1r_ = sr([sr([], '1red', '1 e. RR'), sr([a1c(w, AR, '2re', '2 e. RR'), lift(w, f['tr'], AR)], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B1)
    pwp_ = sr([sr([nnr], 'nnrpd', 'n e. RR+'), b1r_], 'rpcxpcld', '( n ^c %s ) e. RR+' % B1)
    bar_ = w.s([bind(w, AR, lift(w, f['dr'], AR), lift(w, f['d1'], AR), 'D e. RR', '1 < D'), nnr, w.inst('zdbvare')], 'syl2anc', '( %s -> %s e. RR )' % (AR, BA('n')))
    f0r = sr([sr([pwp_], 'rpred', '( n ^c %s ) e. RR' % B1), sr([bar_], 'resqcld', '( %s ^ 2 ) e. RR' % BA('n')), sr([pwp_], 'rpge0d', '0 <_ ( n ^c %s )' % B1),
              sr([bar_], 'sqge0d', '0 <_ ( %s ^ 2 )' % BA('n'))], 'mulge0d', '0 <_ %s' % FN('n'))
    TT = '( %s x. %s )' % (FN('n'), EN('n'))
    ttr = sr([frr, enr], 'remulcld', '%s e. RR' % TT)
    tt0 = sr([frr, enr, f0r, en0], 'mulge0d', '0 <_ %s' % TT)
    sl = st([st([], 'fzfid', '%s e. Fin' % RB), ttr, tt0, ss], 'fsumless', 'sum_ n e. ( 1 ... M ) %s <_ %s' % (TT, BLK_L('M', XP, FN('n'))))
    L1 = 'sum_ n e. ( 1 ... M ) %s' % TT
    AM = '( %s /\\ n e. ( 1 ... M ) )' % ante
    nnm = w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... M ) )' % AM), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AM)
    frm = fnre(w, AM, nnm, lift(w, f['dr'], AM), lift(w, f['d1'], AM), lift(w, f['tr'], AM))
    sm = mkst(w, AM)
    ndxm = sm([sm([sm([nnm], 'nnred', 'n e. RR')], 'renegcld', '-u n e. RR'), lift(w, f['xprp'], AM)], 'rerpdivcld', '( -u n / %s ) e. RR' % XP)
    ttm = sm([frm, sm([ndxm], 'reefcld', '%s e. RR' % EN('n'))], 'remulcld', '%s e. RR' % TT)
    l1r = st([st([], 'fzfid', '( 1 ... M ) e. Fin'), ttm], 'fsumrecl', '%s e. RR' % L1)
    lbr = st([st([], 'fzfid', '%s e. Fin' % RB), ttr], 'fsumrecl', '%s e. RR' % BLK_L('M', XP, FN('n')))
    # BLK_R real
    AJ = '( %s /\\ j e. ( 0 ... M ) )' % ante
    jj = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... M ) )' % AJ), w.inst('elfznn0')], 'syl', '( %s -> j e. NN0 )' % AJ)
    sjj = mkst(w, AJ)
    Yj = '( ( 2 ^ j ) x. %s )' % XP
    AJF = '( %s /\\ n e. ( 1 ... ( |_ ` %s ) ) )' % (AJ, Yj)
    nnj = w.s([w.s([], 'simpr', '( %s -> n e. ( 1 ... ( |_ ` %s ) ) )' % (AJF, Yj)), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AJF)
    frj = fnre(w, AJF, nnj, lift(w, f['dr'], AJF), lift(w, f['d1'], AJF), lift(w, f['tr'], AJF))
    sjr = sjj([sjj([], 'fzfid', '( 1 ... ( |_ ` %s ) ) e. Fin' % Yj), frj], 'fsumrecl', '%s e. RR' % SJ('j'))
    bodr = sjj([sjj([sjj([sjj([jj], 'nn0red', 'j e. RR')], 'renegcld', '-u j e. RR')], 'reefcld', '( exp ` -u j ) e. RR'), sjr], 'remulcld',
               '( ( exp ` -u j ) x. %s ) e. RR' % SJ('j'))
    rbr = st([st([], 'fzfid', '( 0 ... M ) e. Fin'), bodr], 'fsumrecl', '%s e. RR' % BLK_R('M', XP, FN('n')))
    xbr = st([st([f['xprp'], f['br']], 'rpcxpcld', '%s e. RR+' % XB)], 'rpred', '%s e. RR' % XB)
    linarith(w, ante, [sl, b1, hb], STATEMENTS['zdsigfin'].split(' -> ', 1)[1][:-2],
             leaves={L1: l1r, BLK_L('M', XP, FN('n')): lbr, BLK_R('M', XP, FN('n')): rbr, XB: xbr}, name='qed')
    return w


def fnre(w, AF, nn, dr, d1, tr):
    """( AF -> FN(n) e. RR ) from n e. NN (the bvA value is a finite sum of reals)"""
    st = mkst(w, AF)
    b1r = st([st([], '1red', '1 e. RR'), st([a1c(w, AF, '2re', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B1)
    pw = st([st([st([nn], 'nnrpd', 'n e. RR+'), b1r], 'rpcxpcld', '( n ^c %s ) e. RR+' % B1)], 'rpred', '( n ^c %s ) e. RR' % B1)
    bar = w.s([bind(w, AF, dr, d1, 'D e. RR', '1 < D'), nn, w.inst('zdbvare')], 'syl2anc', '( %s -> %s e. RR )' % (AF, BA('n')))
    return st([pw, st([bar], 'resqcld', '( %s ^ 2 ) e. RR' % BA('n'))], 'remulcld', '%s e. RR' % FN('n'))


if __name__ == '__main__':
    for f in sys.argv[1:]:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
