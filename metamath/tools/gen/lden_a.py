"""Sortie LDEN, part a: the scale facts, the thinning arithmetic and the representative systems' REP side
(ldensc ldenhz ldenq1 ldenmod ldenc2 ldenthin ldenrio ldenfib).

    MM_DB=sorties/lden.mm MM_ENGINE=mmatch python3 tools/gen/lden_a.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ldenlib import *
import ldenlib as LL
from ef4_g import elrab_unpack, elrab_pack
from ef3lib import elrab_
from zr_i import scale_facts
from zr_k import ri_facts, cell_facts, idx_of

only = sys.argv[1:]
want = lambda l: not only or l in only
S = STATEMENTS


def num8(w, A, n, dom='RR'):
    return numst8(w, A, n, dom)


def sc_facts(w, A, nn_, tr, t2):
    """under A with N e. NN, T e. RR, 2 <_ T: dict of the ldensc facts (t0, dr, d4, lr, l1, nt, d2) + N real, N >= 1"""
    c = Ctx(w, A)
    pre = c([nn_, c([tr, t2], 'jca', '( T e. RR /\\ 2 <_ T )')], 'jca', HSCL)
    sc = c([pre, w.inst('ldensc')], 'syl', concl('ldensc'))
    P = top_and(concl('ldensc'))
    a, b = c([sc], 'simpld', P[0]), c([sc], 'simprd', P[1])
    a1, a2 = top_and(P[0]); b1, b2 = top_and(P[1])
    t0 = c([a], 'simpld', a1); dd = c([a], 'simprd', a2)
    ll = c([b], 'simpld', b1); nt = c([b], 'simprd', b2)
    F = dict(t0=t0, dr=c([dd], 'simpld', top_and(a2)[0]), d4=c([dd], 'simprd', top_and(a2)[1]),
             lr=c([ll], 'simpld', top_and(b1)[0]), l1=c([ll], 'simprd', top_and(b1)[1]),
             nt=c([nt], 'simpld', top_and(b2)[0]), d2=c([nt], 'simprd', top_and(b2)[1]))
    F['nr'] = c([nn_], 'nnred', 'N e. RR'); F['n1'] = c([nn_], 'nnge1d', '1 <_ N')
    F['tt'] = c([tr, t0], 'jca', TT)
    F['lp'] = lin8(w, A, [F['l1']], '0 < %s' % LD, {LD: F['lr']})
    return F


def gen_sc():
    w = W('ldensc', 'Lean ` one_le_d ` , ` four_le_scale ` , ` one_lt_log_four ` , ` one_lt_log_scale ` , ` mul_le_scale ` , ` scale_le_two_mul ` : the scale ` D = N ( T + 2 ) ` for ` T >_ 2 ` is at least ` 4 ` , its logarithm exceeds ` 1 ` , and ` N T <_ D <_ 2 N T ` .')
    A = ante('ldensc'); c = Ctx(w, A)
    nn_, tr, t2 = c.g('N e. NN'), c.g('T e. RR'), c.g('2 <_ T')
    nr = c([nn_], 'nnred', 'N e. RR'); n1 = c([nn_], 'nnge1d', '1 <_ N')
    t0 = lin8(w, A, [t2], '0 <_ T', {'T': tr})
    two = num8(w, A, '2')
    t2r = c([tr, two], 'readdcld', '( T + 2 ) e. RR')
    dr = c([nr, t2r], 'remulcld', '%s e. RR' % DSC)
    lv = {'N': nr, 'T': tr}
    h1 = c([c([nr, num8(w, A, '1')], 'resubcld', '( N - 1 ) e. RR'), t2r, lin8(w, A, [n1], '0 <_ ( N - 1 )', lv), lin8(w, A, [t2], '0 <_ ( T + 2 )', lv)], 'mulge0d', '0 <_ ( ( N - 1 ) x. ( T + 2 ) )')
    d4 = lin8(w, A, [h1, t2], '4 <_ %s' % DSC, lv, products=True)
    drp = c([dr, lin8(w, A, [d4], '0 < %s' % DSC, {DSC: dr})], 'elrpd', '%s e. RR+' % DSC)
    lr = c([drp], 'relogcld', '%s e. RR' % LD)
    # 1 < log 4 <_ LD
    e1 = c.a1(w.s([], 'df-e', '_e = ( exp ` 1 )'), '_e = ( exp ` 1 )')
    e3 = c.a1(w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3'), '_e < 3')
    er = c.a1(w.s([], 'ere', '_e e. RR'), '_e e. RR')
    e4 = lin8(w, A, [e3], '_e < 4', {'_e': er})
    ee4 = c([e1, e4], 'eqbrtrrd', '( exp ` 1 ) < 4')
    exrp = c([num8(w, A, '1')], 'rpefcld', '( exp ` 1 ) e. RR+')
    frp = num8(w, A, '4', 'RR+')
    l4 = c([ee4, c([exrp, frp, w.inst('logltb')], 'syl2anc', '( ( exp ` 1 ) < 4 <-> ( log ` ( exp ` 1 ) ) < ( log ` 4 ) )')], 'mpbid', '( log ` ( exp ` 1 ) ) < ( log ` 4 )')
    le1 = c([num8(w, A, '1')], 'relogefd', '( log ` ( exp ` 1 ) ) = 1')
    l4b = c([le1, l4], 'eqbrtrrd', '1 < ( log ` 4 )')
    l4d = c([d4, c([frp, drp], 'logled', '( 4 <_ %s <-> ( log ` 4 ) <_ %s )' % (DSC, LD))], 'mpbid', '( log ` 4 ) <_ %s' % LD)
    l4r = c([frp], 'relogcld', '( log ` 4 ) e. RR')
    l1 = c([num8(w, A, '1'), l4r, lr, l4b, l4d], 'ltletrd', '1 < %s' % LD)
    ntr = c([nr, tr], 'remulcld', '( N x. T ) e. RR')
    nt = lin8(w, A, [n1, t0], '( N x. T ) <_ %s' % DSC, lv, products=True)
    h2 = c([nr, c([tr, two], 'resubcld', '( T - 2 ) e. RR'), lin8(w, A, [n1], '0 <_ N', lv), lin8(w, A, [t2], '0 <_ ( T - 2 )', lv)], 'mulge0d', '0 <_ ( N x. ( T - 2 ) )')
    d2 = lin8(w, A, [h2], '%s <_ ( 2 x. ( N x. T ) )' % DSC, lv, products=True)
    P = top_and(concl('ldensc'))
    fin_ = c([c([t0, c([dr, d4], 'jca', top_and(P[0])[1])], 'jca', P[0]), c([c([lr, l1], 'jca', top_and(P[1])[0]), c([nt, d2], 'jca', top_and(P[1])[1])], 'jca', P[1])], 'jca', concl('ldensc'))
    return fin(w, fin_)


def gen_hz():
    w = W('ldenhz', 'The LoggedDetector hypotheses ` HZH ` at the scale ` D = N ( T + 2 ) ` from ` T >_ 2 ` and ` 40 <_ log ( N ( T + 2 ) ) ` (~ ldensc ).')
    A = ante('ldenhz'); c = Ctx(w, A)
    F = sc_facts(w, A, c.g('N e. NN'), c.g('T e. RR'), c.g('2 <_ T'))
    d1 = lin8(w, A, [F['d4']], '1 < %s' % DSC, {DSC: F['dr']})
    fin_ = c([F['dr'], d1, c.g(H40)], '3jca', HZD)
    return fin(w, fin_)


def gen_q1():
    w = W('ldenq1', 'Lean ` Q1_pos ` , ` log_add_one_le_Q1 ` , ` Q1_le_two_mul ` : the number of thinning classes ` Q1 = ceil L + 1 ` is a positive integer with ` L + 1 <_ Q1 <_ L + 2 ` .')
    A = ante('ldenq1'); c = Ctx(w, A)
    nn_, tr, t0 = c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T')
    d2, lr, lp, dr = scale_facts(w, A, nn_, tr, t0)
    cz = c([lr], 'ceilcld', '%s e. ZZ' % JP)
    cg = c([lr], 'ceilged', '%s <_ %s' % (LD, JP))
    cl = c([lr, w.inst('ceilm1lt')], 'syl', '( %s - 1 ) < %s' % (JP, LD))
    cr = c([cz], 'zred', '%s e. RR' % JP)
    lv = {LD: lr, JP: cr}
    c0 = lin8(w, A, [lp, cg], '0 < %s' % JP, lv)
    cn = c([cz, c0], 'jca', '( %s e. ZZ /\\ 0 < %s )' % (JP, JP))
    cnn = c([cn, w.inst('elnnz')], 'sylibr', '%s e. NN' % JP)
    q1n = c([cnn], 'peano2nnd', '%s e. NN' % Q1)
    lo = lin8(w, A, [cg], '( %s + 1 ) <_ %s' % (LD, Q1), lv)
    hi = lin8(w, A, [cl], '%s <_ ( %s + 2 )' % (Q1, LD), lv)
    fin_ = c([q1n, c([lo, hi], 'jca', top_and(concl('ldenq1'))[1])], 'jca', concl('ldenq1'))
    return fin(w, fin_)


def gen_mod():
    w = W('ldenmod', 'Lean ` two_mul_le_sub_of_cls_eq ` : two naturals ` A < B ` of the same parity and the same ` floor ( . / 2 ) mod Q ` differ by at least ` 2 Q ` .')
    A = ante('ldenmod'); c = Ctx(w, A)
    qn, an, bn, ab, par, cls = [c.g(x) for x in ('Q e. NN', 'A e. NN0', 'B e. NN0', 'A < B', '( A mod 2 ) = ( B mod 2 )',
                                                 '( ( |_ ` ( A / 2 ) ) mod Q ) = ( ( |_ ` ( B / 2 ) ) mod Q )')]
    ar, br = c([an], 'nn0red', 'A e. RR'), c([bn], 'nn0red', 'B e. RR')
    az, bz = c([an], 'nn0zd', 'A e. ZZ'), c([bn], 'nn0zd', 'B e. ZZ')
    two = num8(w, A, '2', 'RR+')
    FA, FB = '( |_ ` ( A / 2 ) )', '( |_ ` ( B / 2 ) )'
    faz = c([c([ar, num8(w, A, '2'), c.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0')], 'redivcld', '( A / 2 ) e. RR')], 'flcld', '%s e. ZZ' % FA)
    fbz = c([c([br, num8(w, A, '2'), c.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0')], 'redivcld', '( B / 2 ) e. RR')], 'flcld', '%s e. ZZ' % FB)
    fa = c([ar, two, w.inst('flpmodeq')], 'syl2anc', '( ( %s x. 2 ) + ( A mod 2 ) ) = A' % FA)
    fb = c([br, two, w.inst('flpmodeq')], 'syl2anc', '( ( %s x. 2 ) + ( B mod 2 ) ) = B' % FB)
    RA = '( A mod 2 )'
    rar = c([c([az, c.a1(w.s([], '2nn', '2 e. NN'), '2 e. NN'), w.inst('zmodcl')], 'syl2anc', '%s e. NN0' % RA)], 'nn0red', '%s e. RR' % RA)
    lv = {'A': ar, 'B': br, FA: c([faz], 'zred', '%s e. RR' % FA), FB: c([fbz], 'zred', '%s e. RR' % FB), RA: rar, 'Q': c([qn], 'nnred', 'Q e. RR')}
    # FA < FB from A < B and the parity
    lt = lin8(w, A, [fa, fb, par, ab], '%s < %s' % (FA, FB), lv)
    D = '( %s - %s )' % (FB, FA)
    dn = c([lt, c([faz, fbz, w.inst('znnsub')], 'syl2anc', '( %s < %s <-> %s e. NN )' % (FA, FB, D))], 'mpbid', '%s e. NN' % D)
    dv = c([cls, c([qn, fbz, faz, w.inst('moddvds')], 'syl3anc', '( ( %s mod Q ) = ( %s mod Q ) <-> Q || %s )' % (FB, FA, D))], 'mpbird', 'Q || %s' % D)
    dvc = c([c([cls], 'eqcomd', '( %s mod Q ) = ( %s mod Q )' % (FB, FA)), c([qn, fbz, faz, w.inst('moddvds')], 'syl3anc', '( ( %s mod Q ) = ( %s mod Q ) <-> Q || %s )' % (FB, FA, D))], 'mpbid', 'Q || %s' % D)
    le = c([dvc, c([c([qn], 'nnzd', 'Q e. ZZ'), dn, w.inst('dvdsle')], 'syl2anc', '( Q || %s -> Q <_ %s )' % (D, D))], 'mpd', 'Q <_ %s' % D)
    fin_ = lin8(w, A, [fa, fb, par, le], concl('ldenmod'), lv)
    return fin(w, fin_)


def gen_c2():
    w = W('ldenc2', 'Lean ` idx_add_le_imp ` at ` k = 2 Q1 ` with ` thin_spacing_lt ` \'s arithmetic: cell indices ` 2 Q1 ` apart force ordinates at least ` 1 ` apart ( ~ zridx , ~ ldenq1 ).')
    A = ante('ldenc2'); c = Ctx(w, A)
    nn_, tr, t0 = c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T')
    pre = c([nn_, c([tr, t0], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    d2, lr, lp, dr = scale_facts(w, A, nn_, tr, t0)
    ac, ai, bc, bi = c.g('A e. CC'), c.g('( abs ` ( Im ` A ) ) <_ T'), c.g('B e. CC'), c.g('( abs ` ( Im ` B ) ) <_ T')
    na, _, la, ua = idx_of(w, A, pre, 'A', ac, ai)
    nb, _, lb, ub = idx_of(w, A, pre, 'B', bc, bi)
    IA, IB = IDX('A'), IDX('B')
    q = c([pre, w.inst('ldenq1')], 'syl', concl('ldenq1'))
    Pq = top_and(concl('ldenq1'))
    q1n = c([q], 'simpld', Pq[0]); qlo = c([c([q], 'simprd', Pq[1])], 'simpld', top_and(Pq[1])[0])
    h = c.g('( %s + ( 2 x. %s ) ) <_ %s' % (IA, Q1, IB))
    ima, imb = c([ac], 'imcld', '( Im ` A ) e. RR'), c([bc], 'imcld', '( Im ` B ) e. RR')
    lv = {IA: c([na], 'nn0red', '%s e. RR' % IA), IB: c([nb], 'nn0red', '%s e. RR' % IB), '( Im ` A )': ima, '( Im ` B )': imb, 'T': tr, LD: lr,
          Q1: c([q1n], 'nnred', '%s e. RR' % Q1)}
    D = '( ( Im ` B ) - ( Im ` A ) )'
    dr_ = c([imb, ima], 'resubcld', '%s e. RR' % D)
    # ( 2 Q1 - 1 ) < D x. LD and 2 Q1 - 1 >= LD  (Q1 >= LD + 1, LD > 0)  =>  LD <_ D x. LD  =>  1 <_ D
    m = lin8(w, A, [h, ua, lb, qlo, lp], '%s <_ ( %s x. %s )' % (LD, D, LD), lv, products=True)
    lrp = c([lr, lp], 'elrpd', '%s e. RR+' % LD)
    one = num8(w, A, '1')
    # 1 x. LD = LD
    e1 = c([c([lr], 'recnd', '%s e. CC' % LD)], 'mullidd', '( 1 x. %s ) = %s' % (LD, LD))
    m2 = c([e1, m], 'eqbrtrd', '( 1 x. %s ) <_ ( %s x. %s )' % (LD, D, LD))
    fin_ = c([m2, c([one, dr_, lrp], 'lemul1d', '( 1 <_ %s <-> ( 1 x. %s ) <_ ( %s x. %s ) )' % (D, LD, D, LD))], 'mpbird', '1 <_ %s' % D)
    return fin(w, fin_)


def gen_thin():
    w = W('ldenthin', 'Lean ` thin_spacing ` (Lemma 3.3(b)): zeros ` A ` , ` B ` from the cells of two distinct indices of one parity system with the same character and the same thinning class have ordinates at least ` 1 ` apart ( ~ ldenmod , ~ ldenc2 ).')
    A0 = ante('ldenthin'); c = Ctx(w, A0)
    nn_, tr, t0, sr = c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T'), c.g('S e. RR')
    qin, rin = c.g('Q e. %s' % RI('P')), c.g('R e. %s' % RI('P'))
    e1, qr, cls = c.g('( 1st ` Q ) = ( 1st ` R )'), c.g('Q =/= R'), c.g('%s = %s' % (CLS('Q'), CLS('R')))
    ain, bin_ = c.g('A e. %s' % CELL('( 1st ` Q )', '( 2nd ` Q )')), c.g('B e. %s' % CELL('( 1st ` R )', '( 2nd ` R )'))
    qxp, _, qpar, q2z, _, q2f = ri_facts(w, A0, qin, 'Q')
    rxp, _, rpar, r2z, _, r2f = ri_facts(w, A0, rin, 'R')
    q2n = c([q2f, w.inst('elfznn0')], 'syl', '( 2nd ` Q ) e. NN0'); r2n = c([r2f, w.inst('elfznn0')], 'syl', '( 2nd ` R ) e. NN0')
    fa = cell_facts(w, A0, ain, 'A', '( 1st ` Q )', '( 2nd ` Q )', sr, tr)
    fb = cell_facts(w, A0, bin_, 'B', '( 1st ` R )', '( 2nd ` R )', sr, tr)
    MQ, MR = '( 2nd ` Q )', '( 2nd ` R )'
    xo = c([qxp, rxp, w.inst('xpopth')], 'syl2anc', '( ( ( 1st ` Q ) = ( 1st ` R ) /\\ %s = %s ) <-> Q = R )' % (MQ, MR))
    A1 = '( %s /\\ %s = %s )' % (A0, MQ, MR)
    qe = w.s([w.s([lift(w, e1, A1), w.s([], 'simpr', '( %s -> %s = %s )' % (A1, MQ, MR))], 'jca', '( %s -> ( ( 1st ` Q ) = ( 1st ` R ) /\\ %s = %s ) )' % (A1, MQ, MR)), lift(w, xo, A1)],
             'mpbid', '( %s -> Q = R )' % A1)
    mne = c([qr, c([w.s([qe], 'ex', '( %s -> ( %s = %s -> Q = R ) )' % (A0, MQ, MR))], 'necon3d', '( Q =/= R -> %s =/= %s )' % (MQ, MR))], 'mpd', '%s =/= %s' % (MQ, MR))
    q2r, r2r = c([q2z], 'zred', '%s e. RR' % MQ), c([r2z], 'zred', '%s e. RR' % MR)
    tri = c([mne, c([q2r, r2r, w.inst('lttri2')], 'syl2anc', '( %s =/= %s <-> ( %s < %s \\/ %s < %s ) )' % (MQ, MR, MQ, MR, MR, MQ))], 'mpbid', '( %s < %s \\/ %s < %s )' % (MQ, MR, MR, MQ))
    pe = c([qpar, c([rpar], 'eqcomd', 'P = ( %s mod 2 )' % MR)], 'eqtrd', '( %s mod 2 ) = ( %s mod 2 )' % (MQ, MR))
    pre = c([nn_, c([tr, t0], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    q1n = c([c([pre, w.inst('ldenq1')], 'syl', concl('ldenq1'))], 'simpld', '%s e. NN' % Q1)
    GOAL = concl('ldenthin')
    D = '( abs ` ( ( Im ` A ) - ( Im ` B ) ) )'
    ima, imb = fa['imr'], fb['imr']

    def side(lo, hi, flo, fhi, lon, hin, lopar, cls_eq, lox, hix):
        # 2nd lo < 2nd hi  ->  1 <_ Im hi - Im lo
        Al = '( %s /\\ ( 2nd ` %s ) < ( 2nd ` %s ) )' % (A0, lo, hi)
        cl = Ctx(w, Al)
        Lx = lambda st: lift(w, st, Al)
        lt = cl([], 'simpr', '( 2nd ` %s ) < ( 2nd ` %s )' % (lo, hi))
        MA = ante_of(tsub(S['ldenmod'], {'A': '( 2nd ` %s )' % lo, 'B': '( 2nd ` %s )' % hi, 'Q': Q1}))
        md = cl([cl([cl([Lx(q1n), cl([Lx(lon), Lx(hin)], 'jca', top_and(top_and(MA[0])[0])[1])], 'jca', top_and(MA[0])[0]),
                     cl([lt, cl([Lx(lopar), Lx(cls_eq)], 'jca', top_and(top_and(MA[0])[1])[1])], 'jca', top_and(MA[0])[1])], 'jca', MA[0]), w.inst('ldenmod')], 'syl', MA[1])
        il, ih = IDX(lox), IDX(hix)
        lvi = {il: cl([cl([Lx(flo['idx']), cl([Lx(lon)], 'nn0zd', '( 2nd ` %s ) e. ZZ' % lo)], 'eqeltrd', '%s e. ZZ' % il)], 'zred', '%s e. RR' % il),
               ih: cl([cl([Lx(fhi['idx']), cl([Lx(hin)], 'nn0zd', '( 2nd ` %s ) e. ZZ' % hi)], 'eqeltrd', '%s e. ZZ' % ih)], 'zred', '%s e. RR' % ih),
               '( 2nd ` %s )' % lo: cl([Lx(lon)], 'nn0red', '( 2nd ` %s ) e. RR' % lo), '( 2nd ` %s )' % hi: cl([Lx(hin)], 'nn0red', '( 2nd ` %s ) e. RR' % hi),
               Q1: cl([Lx(q1n)], 'nnred', '%s e. RR' % Q1)}
        i2 = lin8(w, Al, [md, Lx(flo['idx']), Lx(fhi['idx'])], '( %s + ( 2 x. %s ) ) <_ %s' % (il, Q1, ih), lvi)
        CA = ante_of(tsub(S['ldenc2'], {'A': lox, 'B': hix}))
        ptb = cl([cl([Lx(flo['cc']), Lx(flo['im'])], 'jca', PTB(lox)), cl([Lx(fhi['cc']), Lx(fhi['im'])], 'jca', PTB(hix))], 'jca', top_and(CA[0])[1])
        z2 = cl([cl([Lx(pre), ptb, i2], '3jca', CA[0]), w.inst('ldenc2')], 'syl', CA[1])
        return Al, cl, z2
    Al1, cl1, z1 = side('Q', 'R', fa, fb, q2n, r2n, pe, cls, 'A', 'B')
    DBA = '( ( Im ` B ) - ( Im ` A ) )'; DAB = '( ( Im ` A ) - ( Im ` B ) )'
    ab1 = cl1([cl1([lift(w, c([imb, ima], 'resubcld', '%s e. RR' % DBA), Al1)], 'leabsd', '%s <_ ( abs ` %s )' % (DBA, DBA)),
               cl1([lift(w, c([imb], 'recnd', '( Im ` B ) e. CC'), Al1), lift(w, c([ima], 'recnd', '( Im ` A ) e. CC'), Al1)], 'abssubd', '( abs ` %s ) = %s' % (DBA, D))], 'breqtrd', '%s <_ %s' % (DBA, D))
    def lvg(Al):
        return {DBA: lift(w, c([imb, ima], 'resubcld', '%s e. RR' % DBA), Al), DAB: lift(w, c([ima, imb], 'resubcld', '%s e. RR' % DAB), Al),
                D: lift(w, c([c([c([ima], 'recnd', '( Im ` A ) e. CC'), c([imb], 'recnd', '( Im ` B ) e. CC')], 'subcld', '%s e. CC' % DAB)], 'abscld', '%s e. RR' % D), Al)}
    g1 = lin8(w, Al1, [z1, ab1], GOAL, lvg(Al1))
    Al2, cl2, z2 = side('R', 'Q', fb, fa, r2n, q2n, c([pe], 'eqcomd', '( %s mod 2 ) = ( %s mod 2 )' % (MR, MQ)), c([cls], 'eqcomd', '%s = %s' % (CLS('R'), CLS('Q'))), 'B', 'A')
    ab2 = cl2([lift(w, c([ima, imb], 'resubcld', '%s e. RR' % DAB), Al2)], 'leabsd', '%s <_ %s' % (DAB, D))
    g2 = lin8(w, Al2, [z2, ab2], GOAL, lvg(Al2))
    fin_ = c([tri, c([w.s([g1], 'ex', '( %s -> ( %s < %s -> %s ) )' % (A0, MQ, MR, GOAL)), w.s([g2], 'ex', '( %s -> ( %s < %s -> %s ) )' % (A0, MR, MQ, GOAL))], 'jaod',
                      '( ( %s < %s \\/ %s < %s ) -> %s )' % (MQ, MR, MR, MQ, GOAL))], 'mpd', GOAL)
    return fin(w, fin_)


def gen_rio():
    w = W('ldenrio', 'The representative index set with its box binder ` r ` renamed ` o ` (closed; the family theorems carry ` $d F r ` from ~ ld2ssq ).')
    x = '( 1st ` p )'
    ZR_, ZO_ = ZFX(x), tsub(ZFX(x), {'r': 'o'})
    # ZFX(x) = ZFX_o(x) by cbvrabv
    bod = '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX(x)
    eq, nb = w.wcongr(bod, {'r': 'o'}, 'r = o', {'r': w.s([], 'id', '( r = o -> r = o )')})
    z = w.s([eq], 'cbvrabv', '%s = %s' % (ZR_, ZO_))
    CR, CO = CELL(x, '( 2nd ` p )'), tsub(CELL(x, '( 2nd ` p )'), {'r': 'o'})
    ce = w.s([z], 'rabeqi', '%s = %s' % (CR, CO))
    ne = w.s([ce], 'neeq1i', '( %s =/= (/) <-> %s =/= (/) )' % (CR, CO))
    bi = w.s([ne], 'anbi1i', '( ( %s =/= (/) /\\ ( ( 2nd ` p ) mod 2 ) = P ) <-> ( %s =/= (/) /\\ ( ( 2nd ` p ) mod 2 ) = P ) )' % (CR, CO))
    fin_ = w.s([bi], 'rabbii', S['ldenrio'])
    w.qed([fin_], 'idi', S['ldenrio'])
    return go(w)


def gen_fib():
    w = W('ldenfib', 'Lean ` card_repIndex_eq_sum_cls ` , ` cls_lt ` (Lemma 3.3(a)): a parity system is counted class by class, ` Q1 ` classes ( ~ hashrabrex ).')
    A = ante('ldenfib'); c = Ctx(w, A)
    yfin, nn_, tr, t0 = c.g('Y e. Fin'), c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T')
    pre = c([nn_, c([tr, t0], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    q1n = c([c([pre, w.inst('ldenq1')], 'syl', concl('ldenq1'))], 'simpld', '%s e. NN' % Q1)
    FZ = '( 0 ..^ %s )' % Q1
    XPY = '( Y X. ( 0 ... %s ) )' % QP
    xfin = c([yfin, c([], 'fzfid', '( 0 ... %s ) e. Fin' % QP), w.inst('xpfi')], 'syl2anc', '%s e. Fin' % XPY)
    rfin = c([xfin, c.a1(w.s([], 'ssrab2', '%s C_ %s' % (RI('P'), XPY)), '%s C_ %s' % (RI('P'), XPY))], 'ssfid', '%s e. Fin' % RI('P'))
    Ac = '( %s /\\ c e. %s )' % (A, FZ)
    ffin = w.s([w.s([rfin], 'adantr', '( %s -> %s e. Fin )' % (Ac, RI('P'))), w.s([w.s([], 'ssrab2', '%s C_ %s' % (FC('c'), RI('P')))], 'a1i', '( %s -> %s C_ %s )' % (Ac, FC('c'), RI('P')))], 'ssfid', '( %s -> %s e. Fin )' % (Ac, FC('c')))
    dj = c.a1(w.s([], 'invdisjrab', 'Disj_ c e. %s %s' % (FZ, FC('c'))), 'Disj_ c e. %s %s' % (FZ, FC('c')))
    PSI = 'E. c e. %s %s = c' % (FZ, CLS('e'))
    hr = w.s([c.a1(w.s([], 'fzofi', '%s e. Fin' % FZ), '%s e. Fin' % FZ), ffin, dj], 'hashrabrex', '( %s -> ( # ` { e e. %s | %s } ) = sum_ c e. %s ( # ` %s ) )' % (A, RI('P'), PSI, FZ, FC('c')))
    # RI(P) = { e e. RI(P) | PSI }
    Ae = '( %s /\\ e e. %s )' % (A, RI('P'))
    ce = Ctx(w, Ae)
    ein = ce([], 'simpr', 'e e. %s' % RI('P'))
    exp_, _, _, e2z, _, _ = ri_facts(w, Ae, ein, 'e')
    F2 = '( |_ ` ( ( 2nd ` e ) / 2 ) )'
    fz = ce([ce([ce([e2z], 'zred', '( 2nd ` e ) e. RR'), num8(w, Ae, '2'), ce.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0')], 'redivcld', '( ( 2nd ` e ) / 2 ) e. RR')], 'flcld', '%s e. ZZ' % F2)
    mz = ce([fz, lift(w, q1n, Ae), w.inst('zmodfzo')], 'syl2anc', '%s e. %s' % (CLS('e'), FZ))
    PSI2 = 'E. c e. %s c = %s' % (FZ, CLS('e'))
    ex_ = ce([mz, w.s([], 'risset', '( %s e. %s <-> %s )' % (CLS('e'), FZ, PSI2))], 'sylib', PSI2)
    pb = w.s([w.s([], 'eqcom', '( %s = c <-> c = %s )' % (CLS('e'), CLS('e')))], 'rexbii', '( %s <-> %s )' % (PSI, PSI2))
    ps = ce([ex_, pb], 'sylibr', PSI)
    al = c([ps], 'ralrimiva', 'A. e e. %s %s' % (RI('P'), PSI))
    ge = c([al, w.s([], 'rabid2', '( %s = { e e. %s | %s } <-> A. e e. %s %s )' % (RI('P'), RI('P'), PSI, RI('P'), PSI))], 'sylibr', '%s = { e e. %s | %s }' % (RI('P'), RI('P'), PSI))
    he = c([ge], 'fveq2d', '( # ` %s ) = ( # ` { e e. %s | %s } )' % (RI('P'), RI('P'), PSI))
    fin_ = c([he, hr], 'eqtrd', concl('ldenfib'))
    return fin(w, fin_)


GENS = {'ldensc': gen_sc, 'ldenhz': gen_hz, 'ldenq1': gen_q1, 'ldenmod': gen_mod, 'ldenc2': gen_c2, 'ldenthin': gen_thin, 'ldenrio': gen_rio, 'ldenfib': gen_fib}
if __name__ == '__main__':
    for lab in (only or list(GENS)):
        GENS[lab]()
