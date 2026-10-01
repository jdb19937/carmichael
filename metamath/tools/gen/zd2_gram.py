"""Sortie ZD2: the Gram row (Lean gramArg*, gram_row_le): zd2garg, zd2gterm, zd2grow, zd2gram."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zd2_base import *

G_ = '( DChr ` N )'
PG = '( +g ` %s )' % G_
IG = '( invg ` %s )' % G_
MG = '( -g ` %s )' % G_
HSEL_BODY = '( H ` q ) e. %s' % CELL('( 1st ` q )', '( 2nd ` q )')


def group_eqids(w):
    return dict(g=w.s([], 'eqid', '%s = %s' % (G_, G_)), b=w.s([], 'eqid', '%s = %s' % (DB_N, DB_N)),
                p=w.s([], 'eqid', '%s = %s' % (PG, PG)), i=w.s([], 'eqid', '%s = %s' % (IG, IG)),
                m=w.s([], 'eqid', '%s = %s' % (MG, MG)), o=w.s([], 'eqid', '%s = %s' % (X0, X0)))


def grp_facts(w, A, nn_):
    """( A -> ( DChr N ) e. Grp ) with the eqid steps"""
    e = group_eqids(w)
    c = Ctx(w, A)
    abl = c([nn_, w.s([e['g']], 'dchrabl', '( N e. NN -> %s e. Abel )' % G_)], 'syl', '%s e. Abel' % G_)
    grp = c([abl, w.inst('ablgrp')], 'syl', '%s e. Grp' % G_)
    return grp, e


def pair_facts(w, A, c, nn_, ys, sr, tr, hsel, ain, bin_, Aidx='A', Bidx='B'):
    """the facts of two indices A, B of RI(P) with their selected zeros: characters in the base, cell facts"""
    _, _, _, _, a1, _ = ri_facts(w, A, ain, Aidx)
    _, _, _, _, b1, _ = ri_facts(w, A, bin_, Bidx)
    xa = c([ys, a1], 'sseldd', '( 1st ` %s ) e. %s' % (Aidx, DB_N))
    xb = c([ys, b1], 'sseldd', '( 1st ` %s ) e. %s' % (Bidx, DB_N))
    hA, _ = ral_at(w, A, hsel, 'q', Aidx, HSEL_BODY, ain)
    hB, _ = ral_at(w, A, hsel, 'q', Bidx, HSEL_BODY, bin_)
    fa = cell_facts(w, A, hA, '( H ` %s )' % Aidx, '( 1st ` %s )' % Aidx, '( 2nd ` %s )' % Aidx, sr, tr)
    fb = cell_facts(w, A, hB, '( H ` %s )' % Bidx, '( 1st ` %s )' % Bidx, '( 2nd ` %s )' % Bidx, sr, tr)
    return xa, xb, fa, fb


def gen_garg():
    w = W('zd2garg', 'The Gram argument of two indices ` A ` , ` B ` of a parity system with the selected zeros ` H A ` , ` H B ` (Lean ` gramArg_re_bounds ` , ` gramArg_height ` , ` gramArg_im ` ): '
             'the character ` chi_A chi_B ^ -1 ` is in the group and is principal exactly when ` chi_B = chi_A ` ; ` s = ( H A - S ) + conj ( H B - S ) ` has ` 0 <_ Re s <_ 1 / 50 ` , ` Im s = Im H A - Im H B ` and ` N ( abs Im s + 2 ) <_ 2 N ( T + 2 ) ` .')
    A0 = ante_of(S['zd2garg'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0 = [c.g(x) for x in ('N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T')]
    hsel, ain, bin_ = c.g(HSEL), c.g('A e. %s' % RI('P')), c.g('B e. %s' % RI('P'))
    xa, xb, fa, fb = pair_facts(w, A0, c, nn_, ys, sr, tr, hsel, ain, bin_)
    XA, XB = '( 1st ` A )', '( 1st ` B )'
    grp, e = grp_facts(w, A0, nn_)
    inv = c([grp, xb, w.s([e['b'], e['i']], 'grpinvcl', '( ( %s e. Grp /\\ %s e. %s ) -> ( %s ` %s ) e. %s )' % (G_, XB, DB_N, IG, XB, DB_N))], 'syl2anc', '( %s ` %s ) e. %s' % (IG, XB, DB_N))
    XJ = XJK('A', 'B')
    xj = c([grp, xa, inv, w.s([e['b'], e['p']], 'grpcl', '( ( %s e. Grp /\\ %s e. %s /\\ ( %s ` %s ) e. %s ) -> %s e. %s )' % (G_, XA, DB_N, IG, XB, DB_N, XJ, DB_N))], 'syl3anc', '%s e. %s' % (XJ, DB_N))
    SUB = '( %s %s %s )' % (XA, MG, XB)
    sv = c([xa, xb, w.s([e['b'], e['p'], e['i'], e['m']], 'grpsubval', '( ( %s e. %s /\\ %s e. %s ) -> %s = %s )' % (XA, DB_N, XB, DB_N, SUB, XJ))], 'syl2anc', '%s = %s' % (SUB, XJ))
    s0 = c([grp, xa, xb, w.s([e['b'], e['o'], e['m']], 'grpsubeq0', '( ( %s e. Grp /\\ %s e. %s /\\ %s e. %s ) -> ( %s = %s <-> %s = %s ) )' % (G_, XA, DB_N, XB, DB_N, SUB, X0, XA, XB))],
           'syl3anc', '( %s = %s <-> %s = %s )' % (SUB, X0, XA, XB))
    e1 = c([sv], 'eqeq1d', '( %s = %s <-> %s = %s )' % (SUB, X0, XJ, X0))
    bi = c([e1, s0], 'bitr3d', '( %s = %s <-> %s = %s )' % (XJ, X0, XA, XB))
    bi2 = c([bi, w.s([], 'eqcom', '( %s = %s <-> %s = %s )' % (XA, XB, XB, XA))], 'bitrdi', '( %s = %s <-> %s = %s )' % (XJ, X0, XB, XA))
    part1 = c([xj, bi2], 'jca', '( %s e. %s /\\ ( %s = %s <-> %s = %s ) )' % (XJ, DB_N, XJ, X0, XB, XA))
    # the argument
    HA, HB = '( H ` A )', '( H ` B )'
    SJ = SJK('A', 'B')
    sc = c([sr], 'recnd', 'S e. CC')
    da = c([fa['cc'], sc], 'subcld', '( %s - S ) e. CC' % HA)
    db = c([fb['cc'], sc], 'subcld', '( %s - S ) e. CC' % HB)
    cb = c([db], 'cjcld', '( * ` ( %s - S ) ) e. CC' % HB)
    sjc = c([da, cb], 'addcld', '%s e. CC' % SJ)
    RA, RB = '( Re ` %s )' % HA, '( Re ` %s )' % HB
    IA, IB = '( Im ` %s )' % HA, '( Im ` %s )' % HB
    res = c([sr], 'rered', '( Re ` S ) = S'); ims = c([sr], 'reim0d', '( Im ` S ) = 0')
    r1 = c([da, cb], 'readdd', '( Re ` %s ) = ( ( Re ` ( %s - S ) ) + ( Re ` ( * ` ( %s - S ) ) ) )' % (SJ, HA, HB))
    ra = c([c([fa['cc'], sc], 'resubd', '( Re ` ( %s - S ) ) = ( %s - ( Re ` S ) )' % (HA, RA)), c([res], 'oveq2d', '( %s - ( Re ` S ) ) = ( %s - S )' % (RA, RA))], 'eqtrd', '( Re ` ( %s - S ) ) = ( %s - S )' % (HA, RA))
    rb0 = c([c([fb['cc'], sc], 'resubd', '( Re ` ( %s - S ) ) = ( %s - ( Re ` S ) )' % (HB, RB)), c([res], 'oveq2d', '( %s - ( Re ` S ) ) = ( %s - S )' % (RB, RB))], 'eqtrd', '( Re ` ( %s - S ) ) = ( %s - S )' % (HB, RB))
    rb = c([c([db], 'recjd', '( Re ` ( * ` ( %s - S ) ) ) = ( Re ` ( %s - S ) )' % (HB, HB)), rb0], 'eqtrd', '( Re ` ( * ` ( %s - S ) ) ) = ( %s - S )' % (HB, RB))
    RE = '( ( %s - S ) + ( %s - S ) )' % (RA, RB)
    req = c([r1, c([ra, rb], 'oveq12d', '( ( Re ` ( %s - S ) ) + ( Re ` ( * ` ( %s - S ) ) ) ) = %s' % (HA, HB, RE))], 'eqtrd', '( Re ` %s ) = %s' % (SJ, RE))
    i1 = c([da, cb], 'imaddd', '( Im ` %s ) = ( ( Im ` ( %s - S ) ) + ( Im ` ( * ` ( %s - S ) ) ) )' % (SJ, HA, HB))
    ia = c([c([fa['cc'], sc], 'imsubd', '( Im ` ( %s - S ) ) = ( %s - ( Im ` S ) )' % (HA, IA)), c([ims], 'oveq2d', '( %s - ( Im ` S ) ) = ( %s - 0 )' % (IA, IA))], 'eqtrd', '( Im ` ( %s - S ) ) = ( %s - 0 )' % (HA, IA))
    ib0 = c([c([fb['cc'], sc], 'imsubd', '( Im ` ( %s - S ) ) = ( %s - ( Im ` S ) )' % (HB, IB)), c([ims], 'oveq2d', '( %s - ( Im ` S ) ) = ( %s - 0 )' % (IB, IB))], 'eqtrd', '( Im ` ( %s - S ) ) = ( %s - 0 )' % (HB, IB))
    ib = c([c([db], 'imcjd', '( Im ` ( * ` ( %s - S ) ) ) = -u ( Im ` ( %s - S ) )' % (HB, HB)), c([ib0], 'negeqd', '-u ( Im ` ( %s - S ) ) = -u ( %s - 0 )' % (HB, IB))], 'eqtrd', '( Im ` ( * ` ( %s - S ) ) ) = -u ( %s - 0 )' % (HB, IB))
    IM0 = '( ( %s - 0 ) + -u ( %s - 0 ) )' % (IA, IB)
    IM = '( %s - %s )' % (IA, IB)
    ieq0 = c([i1, c([ia, ib], 'oveq12d', '( ( Im ` ( %s - S ) ) + ( Im ` ( * ` ( %s - S ) ) ) ) = %s' % (HA, HB, IM0))], 'eqtrd', '( Im ` %s ) = %s' % (SJ, IM0))
    lv = {IA: fa['imr'], IB: fb['imr'], RA: fa['rer'], RB: fb['rer'], 'S': sr, 'T': tr}
    ieq = c([ieq0, lin.lineq(w, A0, IM0, IM, leaves=lv)], 'eqtrd', '( Im ` %s ) = %s' % (SJ, IM))
    # bounds on the real part
    rer = c([sjc], 'recld', '( Re ` %s ) e. RR' % SJ)
    ge0 = c([lin8(w, A0, [fa['re1'], fb['re1']], '0 <_ %s' % RE, lv), req], 'breqtrrd', '0 <_ ( Re ` %s )' % SJ)
    le50 = c([req, lin8(w, A0, [fa['re2'], fb['re2'], s99], '%s <_ ( 1 / ; 5 0 )' % RE, lv)], 'eqbrtrd', '( Re ` %s ) <_ ( 1 / ; 5 0 )' % SJ)
    part2 = c([sjc, c([ge0, le50], 'jca', '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (SJ, SJ))], 'jca', '( %s e. CC /\\ ( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) ) )' % (SJ, SJ, SJ))
    # the height
    ba = c([fa['im'], c([fa['imr'], tr], 'absled', '( ( abs ` %s ) <_ T <-> ( -u T <_ %s /\\ %s <_ T ) )' % (IA, IA, IA))], 'mpbid', '( -u T <_ %s /\\ %s <_ T )' % (IA, IA))
    bb = c([fb['im'], c([fb['imr'], tr], 'absled', '( ( abs ` %s ) <_ T <-> ( -u T <_ %s /\\ %s <_ T ) )' % (IB, IB, IB))], 'mpbid', '( -u T <_ %s /\\ %s <_ T )' % (IB, IB))
    a1_, a2_ = c([ba], 'simpld', '-u T <_ %s' % IA), c([ba], 'simprd', '%s <_ T' % IA)
    b1_, b2_ = c([bb], 'simpld', '-u T <_ %s' % IB), c([bb], 'simprd', '%s <_ T' % IB)
    T2 = '( 2 x. T )'
    lo = lin8(w, A0, [a1_, b2_], '-u %s <_ %s' % (T2, IM), lv)
    hi = lin8(w, A0, [a2_, b1_], '%s <_ %s' % (IM, T2), lv)
    imr = c([fa['imr'], fb['imr']], 'resubcld', '%s e. RR' % IM)
    t2r = c([numst(w, A0, '2', 'RR'), tr], 'remulcld', '%s e. RR' % T2)
    ab = c([c([lo, hi], 'jca', '( -u %s <_ %s /\\ %s <_ %s )' % (T2, IM, IM, T2)), c([imr, t2r], 'absled', '( ( abs ` %s ) <_ %s <-> ( -u %s <_ %s /\\ %s <_ %s ) )' % (IM, T2, T2, IM, IM, T2))], 'mpbird', '( abs ` %s ) <_ %s' % (IM, T2))
    ab2 = c([c([ieq], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` %s )' % (SJ, IM)), ab], 'eqbrtrd', '( abs ` ( Im ` %s ) ) <_ %s' % (SJ, T2))
    ABS = '( abs ` ( Im ` %s ) )' % SJ
    absr = c([c([sjc], 'imcld', '( Im ` %s ) e. RR' % SJ)], 'recnd', '( Im ` %s ) e. CC' % SJ)
    absr = c([absr], 'abscld', '%s e. RR' % ABS)
    abs0 = c([c([sjc], 'imcld', '( Im ` %s ) e. RR' % SJ)], 'recnd', '( Im ` %s ) e. CC' % SJ)
    abs0 = c([abs0], 'absge0d', '0 <_ %s' % ABS)
    nr = c([nn_], 'nnred', 'N e. RR'); n1 = c([nn_], 'nnge1d', '1 <_ N')
    lv2 = {ABS: absr, 'N': nr, 'T': tr}
    n0 = lin8(w, A0, [n1], '0 <_ N', lv2)
    ht = lin8(w, A0, [ab2, n0, abs0, t0], '( N x. ( %s + 2 ) ) <_ ( 2 x. %s )' % (ABS, DSC), lv2, products=True)
    part3 = c([ieq, ht], 'jca', '( ( Im ` %s ) = %s /\\ ( N x. ( %s + 2 ) ) <_ ( 2 x. %s ) )' % (SJ, IM, ABS, DSC))
    fin = c([part1, c([part2, part3], 'jca', '( %s /\\ %s )' % (strip_ante(formula_of(w, part2), A0), strip_ante(formula_of(w, part3), A0)))], 'jca', ante_of(S['zd2garg'])[1])
    w.qed([fin], 'idi', S['zd2garg'])
    return go(w)


def gen_phic():
    w = W('zd2phic', 'Detector\'s ` PhiR = sum_ r e. Rset ( phi r / r ^ 2 ) ` is a complex number (a closure lemma; the sum binds ` r ` , which the parity-system objects bind too, so it is proved under a clean antecedent).')
    A = ante_of(S['zd2phic'])[0]
    c = Ctx(w, A)
    nn_, rr = c.g('N e. NN'), c.g('R e. RR')
    RS = '( N RSet R )'
    rsf = c([nn_, rr, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin )' % (RS, RS))
    rss, rfin = c([rsf], 'simpld', '%s C_ ( 1 ... ( |_ ` R ) )' % RS), c([rsf], 'simprd', '%s e. Fin' % RS)
    Ar = '( %s /\\ r e. %s )' % (A, RS)
    cr = Ctx(w, Ar)
    rin = cr([lift(w, rss, Ar), cr([], 'simpr', 'r e. %s' % RS)], 'sseldd', 'r e. ( 1 ... ( |_ ` R ) )')
    rnn = cr([rin, w.inst('elfznn')], 'syl', 'r e. NN')
    term = cr([cr([cr([rnn, w.inst('phicl')], 'syl', '( phi ` r ) e. NN')], 'nncnd', '( phi ` r ) e. CC'), cr([cr([rnn], 'nncnd', 'r e. CC'), cr.a1(w.s([], '2nn0', '2 e. NN0'), '2 e. NN0')], 'expcld', '( r ^ 2 ) e. CC'),
               cr([cr([rnn], 'nncnd', 'r e. CC'), cr([rnn], 'nnne0d', 'r =/= 0'), cr.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'expne0d', '( r ^ 2 ) =/= 0')], 'divcld', '( ( phi ` r ) / ( r ^ 2 ) ) e. CC')
    w.qed([rfin, term], 'fsumcl', S['zd2phic'])
    return go(w)


GENS = {'zd2phic': gen_phic, 'zd2garg': gen_garg}


def maind_cc(w, A, c, nn_, dr, d1, lp, W, wc):
    """( A -> MAIND(W) e. CC ) from wc : ( A -> W e. CC ) and ( A -> ( Re W ) <_ ( 1 / 50 ) ) (rle);
    dr, d1, lp : DSC e. RR, 1 < DSC, 0 < LD"""
    def inner(rle):
        MW = '-u %s' % W
        mwc = c([wc], 'negcld', '%s e. CC' % MW)
        # phi N / N
        phn = c([c([c([nn_, w.inst('phicl')], 'syl', '( phi ` N ) e. NN')], 'nncnd', '( phi ` N ) e. CC'), c([nn_], 'nncnd', 'N e. CC'), c([nn_], 'nnne0d', 'N =/= 0')], 'divcld', '( ( phi ` N ) / N ) e. CC')
        # PHI = sum_ r e. RSet ( phi r / r ^ 2 ) (zd2phic: the sum binds r, which RI(P) binds too)
        drp = c([dr, lin8(w, A, [d1], '0 < %s' % DSC, {DSC: dr})], 'elrpd', '%s e. RR+' % DSC)
        rpr = c([drp, numst(w, A, '( 1 / ; ; 1 0 0 )', 'RR')], 'rpcxpcld', '%s e. RR+' % RPD)
        PHI_ = G2.PHI('N', RPD)
        phic = c([nn_, c([rpr], 'rpred', '%s e. RR' % RPD), w.inst('zd2phic')], 'syl2anc', '%s e. CC' % PHI_)
        pre = c([phn, phic], 'mulcld', '( ( ( phi ` N ) / N ) x. %s ) e. CC' % PHI_)
        # Gamma at -u W + 1
        Z1_ = '( %s + 1 )' % MW
        z1c = c([mwc, c([], '1cnd', '1 e. CC')], 'addcld', '%s e. CC' % Z1_)
        rez = c([mwc, c([], '1cnd', '1 e. CC')], 'readdd', '( Re ` %s ) = ( ( Re ` %s ) + ( Re ` 1 ) )' % (Z1_, MW))
        rneg = c([wc], 'renegd', '( Re ` %s ) = -u ( Re ` %s )' % (MW, W))
        re1 = c.a1(w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
        rez2 = c([rez, c([rneg, re1], 'oveq12d', '( ( Re ` %s ) + ( Re ` 1 ) ) = ( -u ( Re ` %s ) + 1 )' % (MW, W))], 'eqtrd', '( Re ` %s ) = ( -u ( Re ` %s ) + 1 )' % (Z1_, W))
        rwr = c([wc], 'recld', '( Re ` %s ) e. RR' % W)
        pos = c([lin8(w, A, [rle], '0 < ( -u ( Re ` %s ) + 1 )' % W, {'( Re ` %s )' % W: rwr}), rez2], 'breqtrrd', '0 < ( Re ` %s )' % Z1_)
        gdom = c([z1c, pos, w.inst('zrenn')], 'syl2anc', '%s e. ( CC \\ ( ZZ \\ NN ) )' % Z1_)
        gam = c([gdom, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % Z1_)
        # KQ
        LM0, LXP = '( log ` %s )' % M0D, '( log ` %s )' % XPD
        lm0r = c([c([drp, numst(w, A, '( 3 / 5 )', 'RR')], 'rpcxpcld', '%s e. RR+' % M0D)], 'relogcld', '%s e. RR' % LM0)
        lxpr = c([c([drp, numst(w, A, '( 6 / 5 )', 'RR')], 'rpcxpcld', '%s e. RR+' % XPD)], 'relogcld', '%s e. RR' % LXP)
        ellp = c([numst(w, A, '( 1 / ; ; 1 0 0 )', 'RR+'), c([c([drp], 'relogcld', '%s e. RR' % LD), lp], 'elrpd', '%s e. RR+' % LD)], 'rpmulcld', '%s e. RR+' % ELLD)
        KQI = tsub(stmt('gf1kq'), {'A': LM0, 'B': LXP, 'L': ELLD, 'W': MW})
        kqa, kqc = ante_of(KQI)
        kq = c([c([c([lm0r, lxpr], 'jca', '( %s e. RR /\\ %s e. RR )' % (LM0, LXP)), ellp, mwc], '3jca', kqa), w.inst('gf1kq')], 'syl', kqc)
        KQ_ = top_and(kqc)[0][:-len(' e. CC')]
        kqcc = c([kq], 'simpld', '%s e. CC' % KQ_)
        g1 = c([gam, kqcc], 'mulcld', '( ( _G ` %s ) x. %s ) e. CC' % (Z1_, KQ_))
        fin = c([pre, g1], 'mulcld', '%s e. CC' % MAIND(W))
        assert formula_of(w, fin) == '( %s -> %s e. CC )' % (A, MAIND(W)), formula_of(w, fin)
        return fin
    return inner


def gen_gterm():
    w = W('zd2gterm', 'One Gram term of a parity system (Lean ` gram_row_le ` , ` hterm ` ): ` abs B ( chi_A chi_B ^ -1 , s_AB ) <_ [ chi_B = chi_A ] abs MAIN ( s_AB ) + C11 L ^ 3 D ^ ( - 7 / 100 ) ` ( ~ gf2bt at the Gram argument, ~ zd2garg ).')
    A0 = ante_of(S['zd2gterm'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0, l2 = [c.g(x) for x in ('N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '2 <_ %s' % LD)]
    hsel, ain, bin_ = c.g(HSEL), c.g('A e. %s' % RI('P')), c.g('B e. %s' % RI('P'))
    GA = ante_of(S['zd2garg'])
    ga = c([c([c([c([c([nn_, ys], 'jca', '( N e. NN /\\ Y C_ %s )' % DB_N), c([c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS), c([tr, t0], 'jca', TT)], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', NYS),
                    c([c.g('P e. RR'), hsel], 'jca', '( P e. RR /\\ %s )' % HSEL)], 'jca', NYP), c([ain, bin_], 'jca', '( A e. %s /\\ B e. %s )' % (RI('P'), RI('P')))], 'jca', GA[0]), w.inst('zd2garg')], 'syl', GA[1])
    XJ, SJ = XJK('A', 'B'), SJK('A', 'B')
    p1 = c([ga], 'simpld', top_and(GA[1])[0]); p23 = c([ga], 'simprd', top_and(GA[1])[1])
    xj = c([p1], 'simpld', '%s e. %s' % (XJ, DB_N)); bi = c([p1], 'simprd', '( %s = %s <-> ( 1st ` B ) = ( 1st ` A ) )' % (XJ, X0))
    p2 = c([p23], 'simpld', top_and(top_and(GA[1])[1])[0]); p3 = c([p23], 'simprd', top_and(top_and(GA[1])[1])[1])
    sjc = c([p2], 'simpld', '%s e. CC' % SJ); reb = c([p2], 'simprd', '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (SJ, SJ))
    ht = c([p3], 'simprd', '( N x. ( ( abs ` ( Im ` %s ) ) + 2 ) ) <_ ( 2 x. %s )' % (SJ, DSC))
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    d1 = lin8(w, A0, [d2], '1 < %s' % DSC, {DSC: dr})
    hz2 = c([dr, d1, l2], '3jca', '( %s e. RR /\\ 1 < %s /\\ 2 <_ %s )' % (DSC, DSC, LD))
    BT = tsub(stmt('gf2bt'), {'D': DSC, 'X': XJ, 'S': SJ})
    bta, btc = ante_of(BT)
    bt = c([c([c([hz2, c([nn_, xj], 'jca', '( N e. NN /\\ %s e. %s )' % (XJ, DB_N))], 'jca', top_and(bta)[0]), c([sjc, c([reb, ht], 'jca', top_and(top_and(bta)[1])[1])], 'jca', top_and(bta)[1])], 'jca', bta), w.inst('gf2bt')], 'syl', btc)
    BG = BGXD(XJ, SJ)
    IF = 'if ( %s = %s , %s , 0 )' % (XJ, X0, MAIND(SJ))
    assert btc == '( abs ` ( %s - %s ) ) <_ %s' % (BG, IF, CREM), btc
    # closures
    BGC = tsub(stmt('gf2bgc'), {'D': DSC, 'X': XJ, 'S': SJ})
    bga, bgc_ = ante_of(BGC)
    bgc = c([c([c([hz2, nn_], 'jca', '( %s /\\ N e. NN )' % strip_ante(formula_of(w, hz2), A0)), c([xj, c([sjc, c([reb], 'simpld', '0 <_ ( Re ` %s )' % SJ)], 'jca', '( %s e. CC /\\ 0 <_ ( Re ` %s ) )' % (SJ, SJ))], 'jca', top_and(bga)[1])], 'jca', bga), w.inst('gf2bgc')], 'syl', bgc_)
    mc = maind_cc(w, A0, c, nn_, dr, d1, lp, SJ, sjc)(c([reb], 'simprd', '( Re ` %s ) <_ ( 1 / ; 5 0 )' % SJ))
    ifc = c([mc, c([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IF)
    # abs B <_ abs IF + CREM
    a2 = c([bgc, ifc, w.inst('abs2dif')], 'syl2anc', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (BG, IF, BG, IF))
    abg = c([bgc], 'abscld', '( abs ` %s ) e. RR' % BG); aif = c([ifc], 'abscld', '( abs ` %s ) e. RR' % IF)
    absub = c([c([bgc, ifc], 'subcld', '( %s - %s ) e. CC' % (BG, IF))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (BG, IF))
    k = closed_consts(w)
    l3r = c([lr, c.a1(w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '( %s ^ 3 ) e. RR' % LD)
    dpr = c([c([dr, lin8(w, A0, [d1], '0 < %s' % DSC, {DSC: dr})], 'elrpd', '%s e. RR+' % DSC), c([numst(w, A0, '( 7 / ; ; 1 0 0 )', 'RR')], 'renegcld', '-u ( 7 / ; ; 1 0 0 ) e. RR')], 'rpcxpcld', '( %s ^c -u ( 7 / ; ; 1 0 0 ) ) e. RR+' % DSC)
    cremr = c([c([c.a1(k[C11][0], '%s e. RR' % C11), l3r], 'remulcld', '( %s x. ( %s ^ 3 ) ) e. RR' % (C11, LD)), c([dpr], 'rpred', '( %s ^c -u ( 7 / ; ; 1 0 0 ) ) e. RR' % DSC)], 'remulcld', '%s e. RR' % CREM)
    lv = {'( abs ` %s )' % BG: abg, '( abs ` %s )' % IF: aif, '( abs ` ( %s - %s ) )' % (BG, IF): absub, CREM: cremr}
    le = lin8(w, A0, [a2, bt], '( abs ` %s ) <_ ( ( abs ` %s ) + %s )' % (BG, IF, CREM), lv)
    # abs IF = if ( cond , abs MAIN , 0 )
    fv = w.s([], 'fvif', '( abs ` %s ) = if ( %s = %s , ( abs ` %s ) , ( abs ` 0 ) )' % (IF, XJ, X0, MAIND(SJ)))
    e0 = w.s([w.s([], 'abs0', '( abs ` 0 ) = 0'), w.inst('ifeq2')], 'ax-mp', 'if ( %s = %s , ( abs ` %s ) , ( abs ` 0 ) ) = if ( %s = %s , ( abs ` %s ) , 0 )' % (XJ, X0, MAIND(SJ), XJ, X0, MAIND(SJ)))
    e1 = c.a1(w.s([fv, e0], 'eqtri', '( abs ` %s ) = if ( %s = %s , ( abs ` %s ) , 0 )' % (IF, XJ, X0, MAIND(SJ))), '( abs ` %s ) = if ( %s = %s , ( abs ` %s ) , 0 )' % (IF, XJ, X0, MAIND(SJ)))
    IF2 = 'if ( ( 1st ` B ) = ( 1st ` A ) , ( abs ` %s ) , 0 )' % MAIND(SJ)
    e2 = c([bi], 'ifbid', 'if ( %s = %s , ( abs ` %s ) , 0 ) = %s' % (XJ, X0, MAIND(SJ), IF2))
    e3 = c([e1, e2], 'eqtrd', '( abs ` %s ) = %s' % (IF, IF2))
    e4 = c([e3], 'oveq1d', '( ( abs ` %s ) + %s ) = ( %s + %s )' % (IF, CREM, IF2, CREM))
    w.qed([le, e4], 'breqtrd', S['zd2gterm'])
    return go(w)


GENS['zd2gterm'] = gen_gterm


def gen_rib():
    w = W('zd2rib', 'The parity system with its box binder renamed ` r -> b ` is the parity system (a closed identity: ` gf2row ` forbids ` r ` in its index set).')
    X1 = '( 1st ` p )'
    ZB = tsub(ZFX(X1), {'r': 'b'})
    body_b = '( b =/= 1 /\\ ( %s ` b ) = 0 )' % EX(X1)
    st, new = w.wcongr(body_b, {'b': 'r'}, 'b = r', {'b': w.s([], 'id', '( b = r -> b = r )')})
    e1 = w.s([st], 'cbvrabv', '%s = %s' % (ZB, ZFX(X1)))
    CB = tsub(CELL(X1, '( 2nd ` p )'), {'r': 'b'}); CE = CELL(X1, '( 2nd ` p )')
    e2 = w.s([e1], 'rabeqi', '%s = %s' % (CB, CE))
    e3 = w.s([e2], 'neeq1i', '( %s =/= (/) <-> %s =/= (/) )' % (CB, CE))
    PAR = '( ( 2nd ` p ) mod 2 ) = P'
    e4 = w.s([e3], 'anbi1i', '( ( %s =/= (/) /\\ %s ) <-> ( %s =/= (/) /\\ %s ) )' % (CB, PAR, CE, PAR))
    w.qed([e4], 'rabbii', S['zd2rib'])
    return go(w)


GENS['zd2rib'] = gen_rib


def ri_fin(w, A, c, nn_, ys):
    """( A -> RI(P) e. Fin ) and ( A -> Y e. Fin )"""
    g = w.s([], 'eqid', '%s = %s' % (G_, G_)); b = w.s([], 'eqid', '%s = %s' % (DB_N, DB_N))
    dbf = c([nn_, w.s([g, b], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB_N)], 'syl', '%s e. Fin' % DB_N)
    yf = c([dbf, ys, w.inst('ssfi')], 'syl2anc', 'Y e. Fin')
    FZ = '( 0 ... %s )' % QP
    xpf = c([yf, c([], 'fzfid', '%s e. Fin' % FZ), w.inst('xpfi')], 'syl2anc', '( Y X. %s ) e. Fin' % FZ)
    rif = c([xpf, w.inst('rabfi')], 'syl', '%s e. Fin' % RI('P'))
    return rif, yf


def gen_grow():
    from zbvlib import mpv
    w = W('zd2grow', 'The main-term row of a parity system (Lean ` gram_row_le ` , ` hrow ` ): over the indices with the character of ` J ` , ` sum_ k abs MAIN ( s_Jk ) <_ C9 Q_R ^ 2 ( 1 / 100 ) L ^ 2 ` ( ~ gf2row on the Gram arguments, with the spacing ~ zrsp and the band count ~ zrband of Construction 7.2(b)).')
    A0 = ante_of(S['zd2grow'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0, l2, kr, mer, pr, hsel, jin = [c.g(x) for x in (
        'N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '2 <_ %s' % LD, 'K e. RR',
        '%s <_ ( K x. ( log ` %s ) )' % (MERTD, RPD), 'P e. RR', HSEL, 'J e. %s' % RI('P'))]
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    d1 = lin8(w, A0, [d2], '1 < %s' % DSC, {DSC: dr})
    rif, yf = ri_fin(w, A0, c, nn_, ys)
    V = '( j e. _V |-> %s )' % SJK('J', 'j')
    FSJ, FSBJ = FS('J'), FSB('J')
    rib = w.s([], 'zd2rib', S['zd2rib'])
    fsb_eq = w.s([rib], 'rabeqi', '%s = %s' % (FSBJ, FSJ))
    # membership in FSB: k e. RI /\ ( 1st k ) = ( 1st J )
    eqk = 'j = k'
    stk, condk = w.wcongr('( 1st ` j ) = ( 1st ` J )', {'j': 'k'}, eqk, {'j': w.s([], 'id', '( %s -> %s )' % (eqk, eqk))})
    elb = w.s([stk], 'elrab', '( k e. %s <-> ( k e. %s /\\ %s ) )' % (FSBJ, RIB('P'), condk))
    elr = w.s([rib], 'eleq2i', '( k e. %s <-> k e. %s )' % (RIB('P'), RI('P')))
    elb2 = w.s([elb, w.s([elr], 'anbi1i', '( ( k e. %s /\\ %s ) <-> ( k e. %s /\\ %s ) )' % (RIB('P'), condk, RI('P'), condk))], 'bitri', '( k e. %s <-> ( k e. %s /\\ %s ) )' % (FSBJ, RI('P'), condk))
    Ak = '( %s /\\ k e. %s )' % (A0, FSBJ)
    ck = Ctx(w, Ak)
    kb = ck([ck([], 'simpr', 'k e. %s' % FSBJ), ck.a1(elb2, formula_of(w, elb2))], 'mpbid', '( k e. %s /\\ %s )' % (RI('P'), condk))
    kin = ck([kb], 'simpld', 'k e. %s' % RI('P')); kc = ck([kb], 'simprd', condk)
    # the Gram argument of ( J , k ): zd2garg
    GA = tsub(S['zd2garg'], {'A': 'J', 'B': 'k'})
    gaa, gac = ante_of(GA)
    nyp = c([c([c([nn_, ys], 'jca', '( N e. NN /\\ Y C_ %s )' % DB_N), c([c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS), c([tr, t0], 'jca', TT)], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', NYS),
             c([pr, hsel], 'jca', '( P e. RR /\\ %s )' % HSEL)], 'jca', NYP)
    ga = ck([ck([lift(w, nyp, Ak), ck([lift(w, jin, Ak), kin], 'jca', '( J e. %s /\\ k e. %s )' % (RI('P'), RI('P')))], 'jca', gaa), w.inst('zd2garg')], 'syl', gac)
    SJ = SJK('J', 'k')
    p23 = ck([ga], 'simprd', top_and(gac)[1])
    p2 = ck([p23], 'simpld', top_and(top_and(gac)[1])[0]); p3 = ck([p23], 'simprd', top_and(top_and(gac)[1])[1])
    sjc = ck([p2], 'simpld', '%s e. CC' % SJ); reb = ck([p2], 'simprd', '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (SJ, SJ))
    imeq = ck([p3], 'simpld', '( Im ` %s ) = ( ( Im ` ( H ` J ) ) - ( Im ` ( H ` k ) ) )' % SJ)
    # ( V ` k ) = SJK(J,k)
    vk, val = mpv(w, Ak, 'j', '_V', SJK('J', 'j'), 'k', ck.a1(w.s([], 'vex', 'k e. _V'), 'k e. _V'))
    assert val == SJ, val
    VK = '( %s ` k )' % V
    # (b): ( V k ) e. CC /\ ( 0 <_ Re /\ Re <_ 1/50 )
    vkc = ck([vk, sjc], 'eqeltrd', '%s e. CC' % VK)
    revk = ck([vk], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (VK, SJ))
    ge0 = ck([ck([reb], 'simpld', '0 <_ ( Re ` %s )' % SJ), ck([revk], 'breq2d', '( 0 <_ ( Re ` %s ) <-> 0 <_ ( Re ` %s ) )' % (VK, SJ))], 'mpbird', '0 <_ ( Re ` %s )' % VK)
    le50 = ck([ck([reb], 'simprd', '( Re ` %s ) <_ ( 1 / ; 5 0 )' % SJ), ck([revk], 'breq1d', '( ( Re ` %s ) <_ ( 1 / ; 5 0 ) <-> ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (VK, SJ))], 'mpbird', '( Re ` %s ) <_ ( 1 / ; 5 0 )' % VK)
    hb_k = ck([vkc, ck([ge0, le50], 'jca', '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (VK, VK))], 'jca', '( %s e. CC /\\ ( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) ) )' % (VK, VK, VK))
    hb = c([hb_k], 'ralrimiva', 'A. k e. %s ( %s e. CC /\\ ( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) ) )' % (FSBJ, VK, VK, VK))
    # (c): k =/= J -> ( 1 / LD ) <_ abs Im ( V k )   (zrsp with Q := J, R := k)
    IMV = '( Im ` %s )' % VK
    imvk = ck([ck([vk], 'fveq2d', '%s = ( Im ` %s )' % (IMV, SJ)), imeq], 'eqtrd', '%s = ( ( Im ` ( H ` J ) ) - ( Im ` ( H ` k ) ) )' % IMV)
    Akn = '( %s /\\ k =/= J )' % Ak
    cn = Ctx(w, Akn)
    HJB = '( H ` q ) e. %s' % CELL('( 1st ` q )', '( 2nd ` q )')
    hJ, _ = ral_at(w, A0, hsel, 'q', 'J', HSEL_BODY, jin)
    hk, _ = ral_at(w, Ak, lift(w, hsel, Ak), 'q', 'k', HSEL_BODY, kin)
    SP = tsub(stmt('zrsp'), {'Q': 'J', 'R': 'k', 'A': '( H ` J )', 'B': '( H ` k )'})
    spa, spc = ante_of(SP)
    ne = cn([cn([], 'simpr', 'k =/= J')], 'necomd', 'J =/= k')
    e1c = cn([lift(w, kc, Akn)], 'eqcomd', '( 1st ` J ) = ( 1st ` k )')
    sp = cn([cn([cn([cn([cn([lift(w, nn_, Akn), lift(w, sr, Akn)], 'jca', '( N e. NN /\\ S e. RR )'), cn([lift(w, tr, Akn), lift(w, t0, Akn)], 'jca', TT)], 'jca', '( ( N e. NN /\\ S e. RR ) /\\ %s )' % TT),
                        cn([lift(w, pr, Akn), lift(w, jin, Akn), lift(w, kin, Akn)], '3jca', '( P e. RR /\\ J e. %s /\\ k e. %s )' % (RI('P'), RI('P')))], 'jca', top_and(spa)[0]),
                cn([cn([e1c, ne], 'jca', '( ( 1st ` J ) = ( 1st ` k ) /\\ J =/= k )'), cn([lift(w, hJ, Akn), lift(w, hk, Akn)], 'jca', '( ( H ` J ) e. %s /\\ ( H ` k ) e. %s )' % (CELL('( 1st ` J )', '( 2nd ` J )'), CELL('( 1st ` k )', '( 2nd ` k )')))], 'jca', top_and(spa)[1])], 'jca', spa),
             w.inst('zrsp')], 'syl', spc)
    absv = cn([cn([lift(w, imvk, Akn)], 'fveq2d', '( abs ` %s ) = ( abs ` ( ( Im ` ( H ` J ) ) - ( Im ` ( H ` k ) ) ) )' % IMV), sp], 'breqtrrd', '( 1 / %s ) <_ ( abs ` %s )' % (LD, IMV))
    hc_k = w.s([absv], 'ex', '( %s -> ( k =/= J -> ( 1 / %s ) <_ ( abs ` %s ) ) )' % (Ak, LD, IMV))
    hc = c([hc_k], 'ralrimiva', 'A. k e. %s ( k =/= J -> ( 1 / %s ) <_ ( abs ` %s ) )' % (FSBJ, LD, IMV))
    # (d): the band count (zrband with Q := J, M := m)
    Am = '( %s /\\ m e. NN )' % A0
    cm = Ctx(w, Am)
    BSET = '{ k e. %s | ( ( m / %s ) <_ ( abs ` %s ) /\\ ( abs ` %s ) < ( ( m + 1 ) / %s ) ) }' % (FSBJ, LD, IMV, IMV, LD)
    BQ = tsub(BANDQ('M'), {'M': 'm', 'Q': 'J'})
    BD = tsub(stmt('zrband'), {'Q': 'J', 'M': 'm'})
    bda, bdc = ante_of(BD)
    mn0 = cm([cm([], 'simpr', 'm e. NN')], 'nnnn0d', 'm e. NN0')
    bd = cm([cm([cm([cm([cm([lift(w, nn_, Am), lift(w, sr, Am)], 'jca', '( N e. NN /\\ S e. RR )'), cm([lift(w, tr, Am), lift(w, t0, Am)], 'jca', TT)], 'jca', '( ( N e. NN /\\ S e. RR ) /\\ %s )' % TT),
                        cm([lift(w, pr, Am), lift(w, jin, Am)], 'jca', '( P e. RR /\\ J e. %s )' % RI('P'))], 'jca', top_and(bda)[0]),
                cm([lift(w, hsel, Am), mn0], 'jca', top_and(bda)[1])], 'jca', bda), w.inst('zrband')], 'syl', bdc)
    # BSET C_ BQ
    Amk = '( ( %s /\\ k e. %s ) /\\ ( ( m / %s ) <_ ( abs ` %s ) /\\ ( abs ` %s ) < ( ( m + 1 ) / %s ) ) )' % (Am, FSBJ, LD, IMV, IMV, LD)
    cmk = Ctx(w, Amk)
    Lk = lambda st: lift(w, st, Amk)
    kin2 = cmk([cmk([cmk([], 'simplr', 'k e. %s' % FSBJ), cmk.a1(elb2, formula_of(w, elb2))], 'mpbid', '( k e. %s /\\ %s )' % (RI('P'), condk))], 'simpld', 'k e. %s' % RI('P'))
    kc2 = cmk([cmk([cmk([], 'simplr', 'k e. %s' % FSBJ), cmk.a1(elb2, formula_of(w, elb2))], 'mpbid', '( k e. %s /\\ %s )' % (RI('P'), condk))], 'simprd', condk)
    # abs Im ( V k ) = abs ( Im ( H k ) - Im ( H J ) )
    A2 = '( %s /\\ k e. %s )' % (Am, FSBJ)
    imv_m = w.s([w.s([imvk], 'adantlr', '( ( %s /\\ k e. %s ) -> %s = ( ( Im ` ( H ` J ) ) - ( Im ` ( H ` k ) ) ) )' % (Am, FSBJ, IMV))], 'adantr', '( %s -> %s = ( ( Im ` ( H ` J ) ) - ( Im ` ( H ` k ) ) ) )' % (Amk, IMV))
    hJc = Lk(c([hJ, w.inst('elrabi')], 'syl', '( H ` J ) e. %s' % ZFX('( 1st ` J )')))
    hkc = w.s([w.s([w.s([hk, w.inst('elrabi')], 'syl', '( %s -> ( H ` k ) e. %s )' % (Ak, ZFX('( 1st ` k )')))], 'adantlr', '( ( %s /\\ k e. %s ) -> ( H ` k ) e. %s )' % (Am, FSBJ, ZFX('( 1st ` k )')))], 'adantr', '( %s -> ( H ` k ) e. %s )' % (Amk, ZFX('( 1st ` k )')))
    from zr_j import box_facts
    def cc_of(st, Z, X):
        zbx, _, _ = elrab_unpack(w, Amk, 'r', BOXR, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX(X), Z, st)
        vc, rvr, ivr, f1, f2, f3, f4 = box_facts(w, Amk, Lk(sr), Lk(tr), zbx, Z)
        return vc, ivr
    hJcc, imJr = cc_of(hJc, '( H ` J )', '( 1st ` J )')
    hkcc, imkr = cc_of(hkc, '( H ` k )', '( 1st ` k )')
    IJ, IK = '( Im ` ( H ` J ) )', '( Im ` ( H ` k ) )'
    abscomm = cmk([cmk([imJr], 'recnd', '%s e. CC' % IJ), cmk([imkr], 'recnd', '%s e. CC' % IK), w.inst('abssub')], 'syl2anc', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (IJ, IK, IK, IJ))
    abseq = cmk([cmk([imv_m], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IMV, IJ, IK)), abscomm], 'eqtrd', '( abs ` %s ) = ( abs ` ( %s - %s ) )' % (IMV, IK, IJ))
    # ( m / LD ) = ( m x. ( 1 / LD ) ), ( ( m + 1 ) / LD ) = ( ( m + 1 ) x. ( 1 / LD ) )
    mnn = w.s([w.s([w.s([], 'simpr', '( %s -> m e. NN )' % Am)], 'adantr', '( ( %s /\\ k e. %s ) -> m e. NN )' % (Am, FSBJ))], 'adantr', '( %s -> m e. NN )' % Amk)
    mcc = cmk([mnn], 'nncnd', 'm e. CC'); m1c = cmk([mcc, cmk([], '1cnd', '1 e. CC')], 'addcld', '( m + 1 ) e. CC')
    ldc = cmk([Lk(lr)], 'recnd', '%s e. CC' % LD); ldn0 = cmk([Lk(lp)], 'gt0ne0d', '%s =/= 0' % LD)
    d1e = cmk([mcc, ldc, ldn0], 'divrecd', '( m / %s ) = ( m x. ( 1 / %s ) )' % (LD, LD))
    d2e = cmk([m1c, ldc, ldn0], 'divrecd', '( ( m + 1 ) / %s ) = ( ( m + 1 ) x. ( 1 / %s ) )' % (LD, LD))
    lo = cmk([cmk([], 'simprl', '( m / %s ) <_ ( abs ` %s )' % (LD, IMV)), d1e, abseq], '3brtr3d', '( m x. ( 1 / %s ) ) <_ ( abs ` ( %s - %s ) )' % (LD, IK, IJ))
    hi = cmk([cmk([], 'simprr', '( abs ` %s ) < ( ( m + 1 ) / %s )' % (IMV, LD)), abseq, d2e], '3brtr3d', '( abs ` ( %s - %s ) ) < ( ( m + 1 ) x. ( 1 / %s ) )' % (IK, IJ, LD))
    BQBODY = '( ( 1st ` q ) = ( 1st ` J ) /\\ ( ( m x. ( 1 / %s ) ) <_ ( abs ` ( ( Im ` ( H ` q ) ) - ( Im ` ( H ` J ) ) ) ) /\\ ( abs ` ( ( Im ` ( H ` q ) ) - ( Im ` ( H ` J ) ) ) ) < ( ( m + 1 ) x. ( 1 / %s ) ) ) )' % (LD, LD)
    assert BQ == '{ q e. %s | %s }' % (RI('P'), BQBODY), BQ
    inb = elrab_pack(w, Amk, 'q', RI('P'), BQBODY, 'k', kin2, cmk([kc2, cmk([lo, hi], 'jca', '( ( m x. ( 1 / %s ) ) <_ ( abs ` ( %s - %s ) ) /\\ ( abs ` ( %s - %s ) ) < ( ( m + 1 ) x. ( 1 / %s ) ) )' % (LD, IK, IJ, IK, IJ, LD))], 'jca',
                   '( %s /\\ ( ( m x. ( 1 / %s ) ) <_ ( abs ` ( %s - %s ) ) /\\ ( abs ` ( %s - %s ) ) < ( ( m + 1 ) x. ( 1 / %s ) ) ) )' % (condk, LD, IK, IJ, IK, IJ, LD)))
    COND = '( ( m / %s ) <_ ( abs ` %s ) /\\ ( abs ` %s ) < ( ( m + 1 ) / %s ) )' % (LD, IMV, IMV, LD)
    ral = w.s([w.s([inb], 'ex', '( ( %s /\\ k e. %s ) -> ( %s -> k e. %s ) )' % (Am, FSBJ, COND, BQ))], 'ralrimiva', '( %s -> A. k e. %s ( %s -> k e. %s ) )' % (Am, FSBJ, COND, BQ))
    ss = cm([ral, w.s([], 'rabss', '( %s C_ %s <-> A. k e. %s ( %s -> k e. %s ) )' % (BSET, BQ, FSBJ, COND, BQ))], 'sylibr', '%s C_ %s' % (BSET, BQ))
    bqf = cm([lift(w, rif, Am), w.inst('rabfi')], 'syl', '%s e. Fin' % BQ)
    hle = cm([bqf, ss, w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` %s )' % (BSET, BQ))
    fsbf = cm([cm([lift(w, rif, Am), w.inst('rabfi')], 'syl', '%s e. Fin' % FSJ), cm.a1(fsb_eq, '%s = %s' % (FSBJ, FSJ))], 'eqeltrd', '%s e. Fin' % FSBJ)
    bsf = cm([fsbf, w.inst('rabfi')], 'syl', '%s e. Fin' % BSET)
    hr = lambda st, X: cm([cm([st, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % X)], 'nn0red', '( # ` %s ) e. RR' % X)
    hd_m = cm([hr(bsf, BSET), hr(bqf, BQ), numst(w, Am, '2', 'RR'), hle, bd], 'letrd', '( # ` %s ) <_ 2' % BSET)
    hd = c([hd_m], 'ralrimiva', 'A. m e. NN ( # ` %s ) <_ 2' % BSET)
    # gf2row
    RW = tsub(stmt('gf2row'), {'D': DSC, 'S': FSBJ, 'V': V})
    rwa, rwc = ante_of(RW)
    l1 = lin8(w, A0, [l2], '1 <_ %s' % LD, {LD: lr})
    fsbf0 = c([c([rif, w.inst('rabfi')], 'syl', '%s e. Fin' % FSJ), c.a1(fsb_eq, '%s = %s' % (FSBJ, FSJ))], 'eqeltrd', '%s e. Fin' % FSBJ)
    Q = top_and(rwa)
    Q1 = top_and(Q[1])
    rw = c([c([c([c([dr, d1, l1], '3jca', '( %s e. RR /\\ 1 < %s /\\ 1 <_ %s )' % (DSC, DSC, LD)), nn_], 'jca', Q[0]),
             c([c([fsbf0, hb], 'jca', Q1[0]), c([hc, hd], 'jca', Q1[1]), c([kr, mer], 'jca', Q1[2])], '3jca', Q[1])], 'jca', rwa), w.inst('gf2row')], 'syl', rwc)
    # rewrite the sum: FSB -> FS, ( V k ) -> SJK(J,k)
    Af = '( %s /\\ k e. %s )' % (A0, FSJ)
    cf = Ctx(w, Af)
    vk2, _ = mpv(w, Af, 'j', '_V', SJK('J', 'j'), 'k', cf.a1(w.s([], 'vex', 'k e. _V'), 'k e. _V'))
    MV = MAIND(VK)
    st_, newm = w.rewrite(MV, {VK: (SJ, vk2)}, Af)
    assert newm == MAIND(SJ), newm
    abse = cf([st_], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (MV, MAIND(SJ)))
    se2 = c([abse], 'sumeq2dv', 'sum_ k e. %s ( abs ` %s ) = sum_ k e. %s ( abs ` %s )' % (FSJ, MV, FSJ, MAIND(SJ)))
    se1 = w.s([fsb_eq], 'sumeq1i', 'sum_ k e. %s ( abs ` %s ) = sum_ k e. %s ( abs ` %s )' % (FSBJ, MV, FSJ, MV))
    fin = c([c([c.a1(se1, formula_of(w, se1)), se2], 'eqtr2d', 'sum_ k e. %s ( abs ` %s ) = sum_ k e. %s ( abs ` %s )' % (FSJ, MAIND(SJ), FSBJ, MV)), rw], 'eqbrtrd', ante_of(S['zd2grow'])[1])
    w.qed([fin], 'idi', S['zd2grow'])
    return go(w)


GENS['zd2grow'] = gen_grow



def d_facts(w, A, c, nn_, tr, t0):
    """DSC e. RR, 1 < DSC, DSC e. RR+, LD e. RR, 0 < LD, RPD e. RR+, RPD e. RR, QRPD e. RR, MERTD e. RR"""
    d2, lr, lp, dr = scale_facts(w, A, nn_, tr, t0)
    d1 = lin8(w, A, [d2], '1 < %s' % DSC, {DSC: dr})
    drp = c([dr, lin8(w, A, [d1], '0 < %s' % DSC, {DSC: dr})], 'elrpd', '%s e. RR+' % DSC)
    rpr = c([drp, numst(w, A, '( 1 / ; ; 1 0 0 )', 'RR')], 'rpcxpcld', '%s e. RR+' % RPD)
    rprr = c([rpr], 'rpred', '%s e. RR' % RPD)
    qm = c([nn_, rprr, w.inst('gf2qm')], 'syl2anc', '( %s e. RR /\\ %s e. RR )' % (QRPD, MERTD))
    return dict(d2=d2, d1=d1, dr=dr, drp=drp, lr=lr, lp=lp, rpr=rpr, rprr=rprr, qr=c([qm], 'simpld', '%s e. RR' % QRPD), mr=c([qm], 'simprd', '%s e. RR' % MERTD))


def row_re(w, A, c, kr, f):
    """( A -> ROW e. RR ), ( A -> C9K e. RR )"""
    l400 = c([numst(w, A, '; ; 4 0 0', 'RR+')], 'relogcld', '( log ` ; ; 4 0 0 ) e. RR')
    fac = c([numst(w, A, '5', 'RR'), c([numst(w, A, '2', 'RR'), l400], 'remulcld', '( 2 x. ( log ` ; ; 4 0 0 ) ) e. RR')], 'readdcld', '( 5 + ( 2 x. ( log ` ; ; 4 0 0 ) ) ) e. RR')
    c9 = c([c([kr, numst(w, A, C7, 'RR')], 'remulcld', '( K x. %s ) e. RR' % C7), fac], 'remulcld', '%s e. RR' % C9K)
    q2 = c([f['qr']], 'resqcld', '( %s ^ 2 ) e. RR' % QRPD)
    row = c([c([c([c9, q2], 'remulcld', '( %s x. ( %s ^ 2 ) ) e. RR' % (C9K, QRPD)), numst(w, A, '( 1 / ; ; 1 0 0 )', 'RR')], 'remulcld', '( ( %s x. ( %s ^ 2 ) ) x. ( 1 / ; ; 1 0 0 ) ) e. RR' % (C9K, QRPD)),
             c([f['lr']], 'resqcld', '( %s ^ 2 ) e. RR' % LD)], 'remulcld', '%s e. RR' % ROW)
    return row, c9


def crem_re(w, A, c, f, k):
    """( A -> CREM e. RR ), ( A -> 0 <_ CREM ); k = closed_consts(w)"""
    l3r = c([f['lr'], c.a1(w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '( %s ^ 3 ) e. RR' % LD)
    l30 = c([f['lr'], c.a1(w.s([], '3nn0', '3 e. NN0'), '3 e. NN0'), lin8(w, A, [f['lp']], '0 <_ %s' % LD, {LD: f['lr']})], 'expge0d', '0 <_ ( %s ^ 3 )' % LD)
    dpr = c([f['drp'], c([numst(w, A, '( 7 / ; ; 1 0 0 )', 'RR')], 'renegcld', '-u ( 7 / ; ; 1 0 0 ) e. RR')], 'rpcxpcld', '( %s ^c -u ( 7 / ; ; 1 0 0 ) ) e. RR+' % DSC)
    c11r = c.a1(k[C11][0], '%s e. RR' % C11); c110 = c.a1(k[C11][1], '0 <_ %s' % C11)
    p = c([c11r, l3r], 'remulcld', '( %s x. ( %s ^ 3 ) ) e. RR' % (C11, LD))
    p0 = c([c11r, l3r, c110, l30], 'mulge0d', '0 <_ ( %s x. ( %s ^ 3 ) )' % (C11, LD))
    cr = c([p, c([dpr], 'rpred', '( %s ^c -u ( 7 / ; ; 1 0 0 ) ) e. RR' % DSC)], 'remulcld', '%s e. RR' % CREM)
    c0 = c([p, c([dpr], 'rpred', '( %s ^c -u ( 7 / ; ; 1 0 0 ) ) e. RR' % DSC), p0, c([dpr], 'rpge0d', '0 <_ ( %s ^c -u ( 7 / ; ; 1 0 0 ) )' % DSC)], 'mulge0d', '0 <_ %s' % CREM)
    return cr, c0


def nyp_step(w, A, c, nn_, ys, sr, s99, s1, tr, t0, pr, hsel):
    """( A -> NYP )"""
    return c([c([c([nn_, ys], 'jca', '( N e. NN /\\ Y C_ %s )' % DB_N), c([c([sr, c([s99, s1], 'jca', '( %s <_ S /\\ S <_ 1 )' % F99)], 'jca', SS), c([tr, t0], 'jca', TT)], 'jca', '( %s /\\ %s )' % (SS, TT))], 'jca', NYS),
             c([pr, hsel], 'jca', '( P e. RR /\\ %s )' % HSEL)], 'jca', NYP)


def gen_gram():
    w = W('zd2gram', 'Lemma 8.2, one Gram row (Lean ` gram_row_le ` ): for an index ` J ` of a parity system, ` sum_k abs B ( chi_J chi_k ^ -1 , s_Jk ) <_ C9 Q_R ^ 2 ( 1 / 100 ) L ^ 2 + J C11 L ^ 3 D ^ ( - 7 / 100 ) ` ( ~ zd2gterm termwise, ~ zd2grow for the main-term row).')
    A0 = ante_of(S['zd2gram'])[0]
    c = Ctx(w, A0)
    nn_, ys, sr, s99, s1, tr, t0, l2, kr, mer, pr, hsel, jin = [c.g(x) for x in (
        'N e. NN', 'Y C_ %s' % DB_N, 'S e. RR', '%s <_ S' % F99, 'S <_ 1', 'T e. RR', '0 <_ T', '2 <_ %s' % LD, 'K e. RR',
        '%s <_ ( K x. ( log ` %s ) )' % (MERTD, RPD), 'P e. RR', HSEL, 'J e. %s' % RI('P'))]
    f = d_facts(w, A0, c, nn_, tr, t0)
    k = closed_consts(w)
    rif, yf = ri_fin(w, A0, c, nn_, ys)
    nyp = nyp_step(w, A0, c, nn_, ys, sr, s99, s1, tr, t0, pr, hsel)
    RIP, FSJ = RI('P'), FS('J')
    SJ, XJ = SJK('J', 'k'), XJK('J', 'k')
    BG = BGXD(XJ, SJ)
    IF2 = 'if ( ( 1st ` k ) = ( 1st ` J ) , ( abs ` %s ) , 0 )' % MAIND(SJ)
    cremr, crem0 = crem_re(w, A0, c, f, k)
    row, c9 = row_re(w, A0, c, kr, f)
    # per k in RI
    Ak = '( %s /\\ k e. %s )' % (A0, RIP)
    ck = Ctx(w, Ak)
    kin = ck([], 'simpr', 'k e. %s' % RIP)
    GT = tsub(S['zd2gterm'], {'A': 'J', 'B': 'k'})
    gta, gtc = ante_of(GT)
    gt = ck([ck([ck([lift(w, nyp, Ak), lift(w, l2, Ak)], 'jca', '( %s /\\ 2 <_ %s )' % (NYP, LD)), ck([lift(w, jin, Ak), kin], 'jca', '( J e. %s /\\ k e. %s )' % (RIP, RIP))], 'jca', gta), w.inst('zd2gterm')], 'syl', gtc)
    GA = tsub(S['zd2garg'], {'A': 'J', 'B': 'k'})
    gaa, gac = ante_of(GA)
    ga = ck([ck([lift(w, nyp, Ak), ck([lift(w, jin, Ak), kin], 'jca', '( J e. %s /\\ k e. %s )' % (RIP, RIP))], 'jca', gaa), w.inst('zd2garg')], 'syl', gac)
    p1 = ck([ga], 'simpld', top_and(gac)[0]); p23 = ck([ga], 'simprd', top_and(gac)[1])
    xj = ck([p1], 'simpld', '%s e. %s' % (XJ, DB_N))
    p2 = ck([p23], 'simpld', top_and(top_and(gac)[1])[0])
    sjc = ck([p2], 'simpld', '%s e. CC' % SJ); reb = ck([p2], 'simprd', '( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) )' % (SJ, SJ))
    hz2 = ck([lift(w, f['dr'], Ak), lift(w, f['d1'], Ak), lift(w, l2, Ak)], '3jca', '( %s e. RR /\\ 1 < %s /\\ 2 <_ %s )' % (DSC, DSC, LD))
    BGC = tsub(stmt('gf2bgc'), {'D': DSC, 'X': XJ, 'S': SJ})
    bga, bgc_ = ante_of(BGC)
    bgc = ck([ck([ck([hz2, lift(w, nn_, Ak)], 'jca', top_and(bga)[0]), ck([xj, ck([sjc, ck([reb], 'simpld', '0 <_ ( Re ` %s )' % SJ)], 'jca', '( %s e. CC /\\ 0 <_ ( Re ` %s ) )' % (SJ, SJ))], 'jca', top_and(bga)[1])], 'jca', bga), w.inst('gf2bgc')], 'syl', bgc_)
    absbg = ck([bgc], 'abscld', '( abs ` %s ) e. RR' % BG)
    mc = maind_cc(w, Ak, ck, lift(w, nn_, Ak), lift(w, f['dr'], Ak), lift(w, f['d1'], Ak), lift(w, f['lp'], Ak), SJ, sjc)(ck([reb], 'simprd', '( Re ` %s ) <_ ( 1 / ; 5 0 )' % SJ))
    absm = ck([mc], 'abscld', '( abs ` %s ) e. RR' % MAIND(SJ))
    if2r = ck([absm, ck([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % IF2)
    rhs_r = ck([if2r, lift(w, cremr, Ak)], 'readdcld', '( %s + %s ) e. RR' % (IF2, CREM))
    s1_ = c([rif, absbg, rhs_r, gt], 'fsumle', 'sum_ k e. %s ( abs ` %s ) <_ sum_ k e. %s ( %s + %s )' % (RIP, BG, RIP, IF2, CREM))
    s2_ = c([rif, ck([if2r], 'recnd', '%s e. CC' % IF2), ck([lift(w, cremr, Ak)], 'recnd', '%s e. CC' % CREM)], 'fsumadd', 'sum_ k e. %s ( %s + %s ) = ( sum_ k e. %s %s + sum_ k e. %s %s )' % (RIP, IF2, CREM, RIP, IF2, RIP, CREM))
    s3_ = c([rif, c([cremr], 'recnd', '%s e. CC' % CREM), w.inst('fsumconst')], 'syl2anc', 'sum_ k e. %s %s = ( ( # ` %s ) x. %s )' % (RIP, CREM, RIP, CREM))
    # sum_ k e. FS abs M = sum_ k e. RI IF2
    eqk = 'j = k'
    stk, condk = w.wcongr('( 1st ` j ) = ( 1st ` J )', {'j': 'k'}, eqk, {'j': w.s([], 'id', '( %s -> %s )' % (eqk, eqk))})
    el3 = w.s([stk], 'elrab3', '( k e. %s -> ( k e. %s <-> %s ) )' % (RIP, FSJ, condk))
    ifb = ck([ck([kin, ck.a1(el3, formula_of(w, el3))], 'mpd', '( k e. %s <-> %s )' % (FSJ, condk))], 'ifbid', 'if ( k e. %s , ( abs ` %s ) , 0 ) = %s' % (FSJ, MAIND(SJ), IF2))
    s4_ = c([ifb], 'sumeq2dv', 'sum_ k e. %s if ( k e. %s , ( abs ` %s ) , 0 ) = sum_ k e. %s %s' % (RIP, FSJ, MAIND(SJ), RIP, IF2))
    Af = '( %s /\\ k e. %s )' % (A0, FSJ)
    cf = Ctx(w, Af)
    kinf = cf([cf([], 'simpr', 'k e. %s' % FSJ), w.inst('elrabi')], 'syl', 'k e. %s' % RIP)
    absm_f = cf([kinf, lift(w, w.s([absm], 'ex', '( %s -> ( k e. %s -> ( abs ` %s ) e. RR ) )' % (A0, RIP, MAIND(SJ))), Af)], 'mpd', '( abs ` %s ) e. RR' % MAIND(SJ))
    ralc = c([cf([absm_f], 'recnd', '( abs ` %s ) e. CC' % MAIND(SJ))], 'ralrimiva', 'A. k e. %s ( abs ` %s ) e. CC' % (FSJ, MAIND(SJ)))
    fss = c.a1(w.s([], 'ssrab2', '%s C_ %s' % (FSJ, RIP)), '%s C_ %s' % (FSJ, RIP))
    s5_ = c([c([c([fss, ralc], 'jca', '( %s C_ %s /\\ A. k e. %s ( abs ` %s ) e. CC )' % (FSJ, RIP, FSJ, MAIND(SJ))), c([rif], 'olcd', '( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin )' % (RIP, RIP))], 'jca',
                '( ( %s C_ %s /\\ A. k e. %s ( abs ` %s ) e. CC ) /\\ ( %s C_ ( ZZ>= ` 1 ) \\/ %s e. Fin ) )' % (FSJ, RIP, FSJ, MAIND(SJ), RIP, RIP)), w.inst('sumss2')], 'syl',
             'sum_ k e. %s ( abs ` %s ) = sum_ k e. %s if ( k e. %s , ( abs ` %s ) , 0 )' % (FSJ, MAIND(SJ), RIP, FSJ, MAIND(SJ)))
    s6_ = c([s5_, s4_], 'eqtrd', 'sum_ k e. %s ( abs ` %s ) = sum_ k e. %s %s' % (FSJ, MAIND(SJ), RIP, IF2))
    GR = ante_of(S['zd2grow'])
    gr = c([c([], 'id', A0), w.inst('zd2grow')], 'syl', GR[1])
    # assemble
    S_BG = 'sum_ k e. %s ( abs ` %s )' % (RIP, BG); S_IF = 'sum_ k e. %s %s' % (RIP, IF2); S_CR = 'sum_ k e. %s %s' % (RIP, CREM); S_M = 'sum_ k e. %s ( abs ` %s )' % (FSJ, MAIND(SJ))
    S_RHS = 'sum_ k e. %s ( %s + %s )' % (RIP, IF2, CREM)
    sbgr = c([rif, absbg], 'fsumrecl', '%s e. RR' % S_BG); sifr = c([rif, if2r], 'fsumrecl', '%s e. RR' % S_IF); scrr = c([rif, lift(w, cremr, Ak)], 'fsumrecl', '%s e. RR' % S_CR)
    srhs = c([rif, rhs_r], 'fsumrecl', '%s e. RR' % S_RHS)
    smr = c([c([rif, w.inst('rabfi')], 'syl', '%s e. Fin' % FSJ), absm_f], 'fsumrecl', '%s e. RR' % S_M)
    hr = c([c([c([rif, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % RIP)], 'nn0red', '( # ` %s ) e. RR' % RIP), cremr], 'remulcld', '( ( # ` %s ) x. %s ) e. RR' % (RIP, CREM))
    lv = {S_BG: sbgr, S_IF: sifr, S_CR: scrr, S_RHS: srhs, S_M: smr, '( ( # ` %s ) x. %s )' % (RIP, CREM): hr, ROW: row}
    e1 = c([s6_], 'eqcomd', '%s = %s' % (S_IF, S_M))
    fin = lin8(w, A0, [s1_, s2_, s3_, e1, gr], '%s <_ ( %s + ( ( # ` %s ) x. %s ) )' % (S_BG, ROW, RIP, CREM), lv)
    w.qed([fin], 'idi', S['zd2gram'])
    return go(w)


GENS['zd2gram'] = gen_gram


if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
