"""T12: nodupTDF at the machine (Step5.lean ` ndBody ` , ` nodupTDF ` ; blueprint D4).

  t12ndcost  ` ( 2nd ( NodupTD W ) ) = sum_ j ( # W - j ) ` (telescoped, ~ telfsumo )
  t12ndfst   the machine's nodup flag is ` ( 1st ( NodupTD W ) ) ` (~ noduptdfst : ` Fun `' W ` , ~ swrdrn3 , ~ fvelimab )
  tmindbi    one entry ( ` ndBody_runs ` ) along the family ` P' ` (~ tmime , ~ tmimlsb , ~ tmidropnb , the load, ~ tmiaca )
  tmindat    the frame
  tmindal    ` accLoopF ndBody ` at the family (~ tmiacl )
  tmind      ` nodupTDF_runs ` : ~ tmilcpyb then ~ tmindal

    MM_DB=sorties/t12.mm python3 tools/gen/t12_n_nd.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq, nlinarith
from cl import Closure
from t7_e_cmp import machine, togk, letgk
from t10_n_rgf import tmbn
from t10_d_dot import cls_to, load_nfl
from t10_e_doa import lift_from
from t10_u_s2s import expose, me_bound_n
from a4alib import projeq, paircl
import t8alib as A8
import t7c_h_lst as LST
from t12_j_acc import notif_fleq
from t12_k_ko import flag_if, acc_step, LG, NLG, DOM, EB, C5, PV
from t12_l_ap import linarith_eq
import num
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
TB = lambda x: '( TMB ` %s )' % x
NW = '( # ` W )'
SUB = lambda k: '( W substr <. %s , %s >. )' % (k, NW)
TAIL = lambda i: SUB('( %s + 1 )' % i)
NT = lambda i: '-. ( W ` %s ) e. ran %s' % (i, TAIL(i))           # the machine's test at entry i
ANDW = 'A. i e. ( 0 ..^ %s ) %s' % (NW, NT('i'))
SUMC = 'sum_ j e. ( 0 ..^ %s ) ( %s - j )' % (NW, NW)
ND2 = '( 2nd ` ( NodupTD ` W ) )'
ND1 = '( 1st ` ( NodupTD ` W ) )'
ST_NDCOST = '( W e. Word NN0 -> %s = %s )' % (ND2, SUMC)
ST_NDFST = '( W e. Word NN0 -> %s = if ( if ( %s , 1 , 0 ) = 0 , (/) , 1o ) )' % (ND1, ANDW)


def t12ndcost():
    lab = 't12ndcost'
    A = 'W e. Word NN0'
    w = W(lab, 'The cost of ` nodupTD ` is the sum of the tails\' lengths plus one each, ` sum_ j ( # W - j ) ` (Lean\'s '
               '` nodupTD_cons ` and ` notMemTD_snd ` at every suffix, telescoped by ~ telfsumo ).')
    s = w.s
    lw = s([], 'id', '( %s -> W e. Word NN0 )' % A)
    KF = lambda k: '( 2nd ` ( NodupTD ` %s ) )' % SUB(k)
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (A, NW)
    jj = s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NW))
    lwj = s([], 'simpl', '( %s -> W e. Word NN0 )' % pj)
    D_ = '( W ` j )'
    S1 = '<" %s ">' % D_
    J1 = '( j + 1 )'
    dn = s([lwj, jj, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pj, D_))
    dr = s([lwj, jj, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (pj, SUB('j'), S1, SUB(J1)))
    rw = s([lwj, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pj, SUB(J1)))
    NM = '( %s NotMemTD %s )' % (D_, SUB(J1))
    IFE = 'if ( ( 1st ` %s ) = 1o , ( 1st ` ( NodupTD ` %s ) ) , (/) )' % (NM, SUB(J1))
    SUM_ = '( ( ( 2nd ` %s ) + %s ) + 1 )' % (NM, KF(J1))
    cs = s([dn, rw, w.inst('noduptdcs')], 'syl2anc', '( %s -> ( NodupTD ` ( %s ++ %s ) ) = <. %s , %s >. )' % (pj, S1, SUB(J1), IFE, SUM_))
    e1 = s([s([dr], 'fveq2d', '( %s -> ( NodupTD ` %s ) = ( NodupTD ` ( %s ++ %s ) ) )' % (pj, SUB('j'), S1, SUB(J1))), cs], 'eqtrd',
           '( %s -> ( NodupTD ` %s ) = <. %s , %s >. )' % (pj, SUB('j'), IFE, SUM_))
    cl1 = s([rw, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` %s ) e. ( 2o X. NN0 ) )' % (pj, SUB(J1)))
    a1, b1 = paircl(w, pj, '( NodupTD ` %s )' % SUB(J1), cl1, '2o', 'NN0')
    nmc = s([dn, rw, w.inst('notmemtdcl')], 'syl2anc', '( %s -> %s e. ( 2o X. NN0 ) )' % (pj, NM))
    na, nb = paircl(w, pj, NM, nmc, '2o', 'NN0')
    xa = s([a1, s([s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % pj)], 'ifcld', '( %s -> %s e. 2o )' % (pj, IFE))
    xb = s([s([nb, b1], 'nn0addcld', '( %s -> ( ( 2nd ` %s ) + %s ) e. NN0 )' % (pj, NM, KF(J1))), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pj, SUM_))
    k2 = projeq(w, pj, '( NodupTD ` %s )' % SUB('j'), e1, IFE, SUM_, xa, xb, 2)
    # ( 2nd NotMemTD ) = # SUB( j + 1 ) = # W - ( j + 1 )
    nmcost = s([dn, rw, w.inst('notmemtdcost')], 'syl2anc', '( %s -> ( 2nd ` %s ) = ( # ` %s ) )' % (pj, NM, SUB(J1)))
    j1fz = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (pj, J1, NW))
    nwj = s([lwj, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pj, NW))
    nfz = s([nwj, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (pj, NW, NW))
    sl = s([lwj, j1fz, nfz, w.inst('swrdlen')], 'syl3anc', '( %s -> ( # ` %s ) = ( %s - %s ) )' % (pj, SUB(J1), NW, J1))
    cl = Closure(w, pj, {})
    cl.leaf(NW, 'NN0', nwj)
    cl.leaf('j', 'NN0', s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj))
    cl.leaf('( 2nd ` %s )' % NM, 'NN0', nb); cl.leaf(KF(J1), 'NN0', b1)
    cl.leaf(KF('j'), 'NN0', s([k2, xb], 'eqeltrd', '( %s -> %s e. NN0 )' % (pj, KF('j'))))
    cl.leaf('( # ` %s )' % SUB(J1), 'NN0', s([rw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pj, SUB(J1))))
    dif = linarith_eq(w, pj, '( %s - j )' % NW, '( %s - %s )' % (KF('j'), KF(J1)), [k2, nmcost, sl], cl)
    SUMD = 'sum_ j e. ( 0 ..^ %s ) ( %s - %s )' % (NW, KF('j'), KF(J1))
    se = s([dif], 'sumeq2dv', '( %s -> %s = %s )' % (A, SUMC, SUMD))

    def kcong(a_):
        e = s([], 'id', '( k = %s -> k = %s )' % (a_, a_))
        cg, new = w.congr(KF('k'), {'k': a_}, 'k = %s' % a_, {'k': e})
        assert new == KF(a_), new
        return cg
    nw = s([lw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (A, NW))
    huz = s([nw, s([s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % A)], 'eleqtrd', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (A, NW))
    pk = '( %s /\\ k e. ( 0 ... %s ) )' % (A, NW)
    lwk = s([], 'simpl', '( %s -> W e. Word NN0 )' % pk)
    rwk = s([lwk, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pk, SUB('k')))
    clk = s([rwk, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` %s ) e. ( 2o X. NN0 ) )' % (pk, SUB('k')))
    kac = s([s([clk, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pk, KF('k')))], 'nn0cnd', '( %s -> %s e. CC )' % (pk, KF('k')))
    tel = s([kcong('j'), kcong(J1), kcong('0'), kcong(NW), huz, kac], 'telfsumo', '( %s -> %s = ( %s - %s ) )' % (A, SUMD, KF('0'), KF(NW)))
    e_0 = s([s([s([lw, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = W )' % (A, SUB('0')))], 'fveq2d', '( %s -> ( NodupTD ` %s ) = ( NodupTD ` W ) )' % (A, SUB('0')))],
            'fveq2d', '( %s -> %s = %s )' % (A, KF('0'), ND2))
    z0 = s([s([s([s([], 'swrd00', '%s = (/)' % SUB(NW))], 'fveq2i', '( NodupTD ` %s ) = ( NodupTD ` (/) )' % SUB(NW)),
                s([], 'noduptd0', '( NodupTD ` (/) ) = <. 1o , 0 >.')], 'eqtri', '( NodupTD ` %s ) = <. 1o , 0 >.' % SUB(NW))], 'fveq2i',
            '%s = ( 2nd ` <. 1o , 0 >. )' % KF(NW))
    z1 = s([z0, s([s([], '1oex', '1o e. _V'), s([], 'c0ex', '0 e. _V')], 'op2nd', '( 2nd ` <. 1o , 0 >. ) = 0')], 'eqtri', '%s = 0' % KF(NW))
    ndn = s([s([lw, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. ( 2o X. NN0 ) )' % A), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (A, ND2))
    d2 = s([e_0, s([z1], 'a1i', '( %s -> %s = 0 )' % (A, KF(NW)))], 'oveq12d', '( %s -> ( %s - %s ) = ( %s - 0 ) )' % (A, KF('0'), KF(NW), ND2))
    d3 = s([s([ndn], 'nn0cnd', '( %s -> %s e. CC )' % (A, ND2))], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A, ND2, ND2))
    w.qed([s([s([s([se, tel], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (A, SUMC, KF('0'), KF(NW))), d2, d3], '3eqtrd', '( %s -> %s = %s )' % (A, SUMC, ND2))],
             'eqcomd', '( %s -> %s = %s )' % (A, ND2, SUMC)), w.inst('biid')], 'mpbi', ST_NDCOST)
    return w.run()


def t12ndfst():
    lab = 't12ndfst'
    A = 'W e. Word NN0'
    w = W(lab, 'The machine\'s nodup flag (no entry occurs in its tail) is A1b\'s ` ( 1st ( NodupTD S ) ) ` : ~ noduptdfst gives '
               '` Fun `\' W ` , which is ~ dff13 injectivity; an entry in its tail is a later equal entry (~ swrdrn3 , ~ fvelimab ).')
    s = w.s
    ww = s([], 'id', '( %s -> W e. Word NN0 )' % A)
    R_ = '( 0 ..^ %s )' % NW
    wf = s([ww, w.inst('wrdf')], 'syl', '( %s -> W : %s --> NN0 )' % (A, R_))
    wfn = s([ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn %s )' % (A, R_))
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (A, NW))
    nfz = s([nw, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (A, NW, NW))
    def tail_bi(pc, Ast, a, ain):
        """( pc -> ( ( W ` a ) e. ran TAIL( a ) <-> E. k e. ( ( a + 1 ) ..^ # W ) ( W ` k ) = ( W ` a ) ) ) from
        Ast : ( pc -> W e. Word NN0 ) , ain : ( pc -> a e. R_ )"""
        A1 = '( %s + 1 )' % a
        RA = '( %s ..^ %s )' % (A1, NW)
        nwc = s([Ast, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pc, NW))
        nfzc = s([nwc, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (pc, NW, NW))
        a1fz = s([ain, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (pc, A1, NW))
        rn_ = s([Ast, a1fz, nfzc, w.inst('swrdrn3')], 'syl3anc', '( %s -> ran %s = ( W " %s ) )' % (pc, TAIL(a), RA))
        a1n = s([s([ain, w.inst('elfzonn0')], 'syl', '( %s -> %s e. NN0 )' % (pc, a)), w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pc, A1))
        a1uz = s([a1n, w.inst('elnn0uz')], 'sylib', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (pc, A1))
        rss_ = s([a1uz, w.inst('fzoss1')], 'syl', '( %s -> %s C_ %s )' % (pc, RA, R_))
        wfn_ = s([Ast, w.inst('wrdfn')], 'syl', '( %s -> W Fn %s )' % (pc, R_))
        im_ = s([wfn_, rss_, w.inst('fvelimab')], 'syl2anc', '( %s -> ( ( W ` %s ) e. ( W " %s ) <-> E. k e. %s ( W ` k ) = ( W ` %s ) ) )' % (pc, a, RA, RA, a))
        bi_ = s([s([rn_], 'eleq2d', '( %s -> ( ( W ` %s ) e. ran %s <-> ( W ` %s ) e. ( W " %s ) ) )' % (pc, a, TAIL(a), a, RA)), im_], 'bitrd',
                '( %s -> ( ( W ` %s ) e. ran %s <-> E. k e. %s ( W ` k ) = ( W ` %s ) ) )' % (pc, a, TAIL(a), RA, a))
        return bi_, rss_
    # ( -> ) : injective -> no entry in its tail
    I1 = '( i + 1 )'
    RI = '( %s ..^ %s )' % (I1, NW)
    F1 = 'W : %s -1-1-> NN0' % R_
    pf = '( %s /\\ %s )' % (A, F1)
    pfi = '( %s /\\ i e. %s )' % (pf, R_)
    pk = '( %s /\\ k e. %s )' % (pfi, RI)
    kk = s([], 'simpr', '( %s -> k e. %s )' % (pk, RI))
    f1k = s([s([], 'simpr', '( %s -> %s )' % (pf, F1))], 'ad2antrr', '( %s -> %s )' % (pk, F1))
    ik = s([s([], 'simpr', '( %s -> i e. %s )' % (pfi, R_))], 'adantr', '( %s -> i e. %s )' % (pk, R_))
    Afi = s([], 'simpll', '( %s -> %s )' % (pfi, A))
    ifi = s([], 'simpr', '( %s -> i e. %s )' % (pfi, R_))
    bii, rssi = tail_bi(pfi, Afi, 'i', ifi)
    kin = s([rssi], 'adantr', '( %s -> %s C_ %s )' % (pk, RI, R_))
    kR = s([kin, kk], 'sseldd', '( %s -> k e. %s )' % (pk, R_))
    veq = s([f1k, s([kR, ik], 'jca', '( %s -> ( k e. %s /\\ i e. %s ) )' % (pk, R_, R_)), w.inst('f1veqaeq')], 'syl2anc',
            '( %s -> ( ( W ` k ) = ( W ` i ) -> k = i ) )' % pk)
    kge = s([kk, w.inst('elfzole1')], 'syl', '( %s -> %s <_ k )' % (pk, I1))
    kz = s([kk, w.inst('elfzoelz')], 'syl', '( %s -> k e. ZZ )' % pk)
    iz = s([ik, w.inst('elfzoelz')], 'syl', '( %s -> i e. ZZ )' % pk)
    ilt = s([s([iz, kz, w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < k <-> %s <_ k ) )' % (pk, I1)), kge], 'mpbird', '( %s -> i < k )' % pk)
    kne = s([s([iz], 'zred', '( %s -> i e. RR )' % pk), ilt], 'gtned', '( %s -> k =/= i )' % pk)
    nkeq = s([kne], 'neneqd', '( %s -> -. k = i )' % pk)
    nveq = s([nkeq, veq], 'mtod', '( %s -> -. ( W ` k ) = ( W ` i ) )' % pk)
    nrex = s([nveq], 'nrexdv', '( %s -> -. E. k e. %s ( W ` k ) = ( W ` i ) )' % (pfi, RI))
    nt = s([nrex, bii], 'mtbird', '( %s -> %s )' % (pfi, NT('i')))
    fwd = s([s([nt], 'ralrimiva', '( %s -> %s )' % (pf, ANDW))], 'ex', '( %s -> ( %s -> %s ) )' % (A, F1, ANDW))
    # ( <- ) : no entry in its tail -> injective (~ dff13 )
    pa = '( %s /\\ %s )' % (A, ANDW)
    pxy = '( %s /\\ ( x e. %s /\\ y e. %s ) )' % (pa, R_, R_)
    xin = s([s([], 'simpr', '( %s -> ( x e. %s /\\ y e. %s ) )' % (pxy, R_, R_))], 'simpld', '( %s -> x e. %s )' % (pxy, R_))
    yin = s([s([], 'simpr', '( %s -> ( x e. %s /\\ y e. %s ) )' % (pxy, R_, R_))], 'simprd', '( %s -> y e. %s )' % (pxy, R_))
    Aa = s([s([], 'simpl', '( %s -> %s )' % (pxy, pa))], 'simpld', '( %s -> %s )' % (pxy, A))
    ANDa = s([s([], 'simpl', '( %s -> %s )' % (pxy, pa))], 'simprd', '( %s -> %s )' % (pxy, ANDW))
    cgx, newx = w.wcongr(NT('i'), {'i': 'x'}, 'i = x', {'i': s([], 'id', '( i = x -> i = x )')})
    cgy, newy = w.wcongr(NT('i'), {'i': 'y'}, 'i = y', {'i': s([], 'id', '( i = y -> i = y )')})
    assert newx == NT('x') and newy == NT('y')
    ntx = s([cgx, ANDa, xin], 'rspcdva', '( %s -> %s )' % (pxy, NT('x')))
    nty = s([cgy, ANDa, yin], 'rspcdva', '( %s -> %s )' % (pxy, NT('y')))
    xz = s([xin, w.inst('elfzoelz')], 'syl', '( %s -> x e. ZZ )' % pxy)
    yz = s([yin, w.inst('elfzoelz')], 'syl', '( %s -> y e. ZZ )' % pxy)
    xr, yr = s([xz], 'zred', '( %s -> x e. RR )' % pxy), s([yz], 'zred', '( %s -> y e. RR )' % pxy)
    EQ = '( W ` x ) = ( W ` y )'

    def half(a, b, az, bz, ain, bin_, nta, eqab):
        """( ( pxy /\\ a < b ) -> -. EQ ) : ( W ` b ) = ( W ` a ) puts ( W ` a ) in its tail"""
        pl = '( %s /\\ %s < %s )' % (pxy, a, b)
        L = lambda st: s([st], 'adantr', '( %s -> %s )' % (pl, concl(w, pxy, st)))
        A1 = '( %s + 1 )' % a
        RA = '( %s ..^ %s )' % (A1, NW)
        ble = s([s([L(az), L(bz), w.inst('zltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> %s <_ %s ) )' % (pl, a, b, A1, b)), s([], 'simpr', '( %s -> %s < %s )' % (pl, a, b))],
                'mpbid', '( %s -> %s <_ %s )' % (pl, A1, b))
        blt = s([L(bin_), w.inst('elfzolt2')], 'syl', '( %s -> %s < %s )' % (pl, b, NW))
        a1z = s([L(az)], 'peano2zd', '( %s -> %s e. ZZ )' % (pl, A1))
        nwz = s([s([L(Aa), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pl, NW))], 'nn0zd', '( %s -> %s e. ZZ )' % (pl, NW))
        bR = s([s([s([L(bz), a1z, nwz], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s e. ZZ ) )' % (pl, b, A1, NW)), w.inst('elfzo')], 'syl',
                  '( %s -> ( %s e. %s <-> ( %s <_ %s /\\ %s < %s ) ) )' % (pl, b, RA, A1, b, b, NW)), s([ble, blt], 'jca', '( %s -> ( %s <_ %s /\\ %s < %s ) )' % (pl, A1, b, b, NW))],
                'mpbird', '( %s -> %s e. %s )' % (pl, b, RA))
        bia, _ = tail_bi(pl, L(Aa), a, L(ain))
        cgk, newk = w.wcongr('( W ` k ) = ( W ` %s )' % a, {'k': b}, 'k = %s' % b, {'k': s([], 'id', '( k = %s -> k = %s )' % (b, b))})
        assert newk == '( W ` %s ) = ( W ` %s )' % (b, a), newk
        pe = '( %s /\\ %s )' % (pl, EQ)
        eqba = s([], 'simpr', '( %s -> %s )' % (pe, EQ))
        if eqab == 'eqcomd':
            eqba = s([eqba], 'eqcomd', '( %s -> ( W ` %s ) = ( W ` %s ) )' % (pe, b, a))
        rex = s([s([bR], 'adantr', '( %s -> %s e. %s )' % (pe, b, RA)), eqba, s([cgk], 'rspcev', '( ( %s e. %s /\\ ( W ` %s ) = ( W ` %s ) ) -> E. k e. %s ( W ` k ) = ( W ` %s ) )' % (b, RA, b, a, RA, a))],
                'syl2anc', '( %s -> E. k e. %s ( W ` k ) = ( W ` %s ) )' % (pe, RA, a))
        inr = s([rex, s([bia], 'adantr', '( %s -> ( ( W ` %s ) e. ran %s <-> E. k e. %s ( W ` k ) = ( W ` %s ) ) )' % (pe, a, TAIL(a), RA, a))], 'mpbird',
                '( %s -> ( W ` %s ) e. ran %s )' % (pe, a, TAIL(a)))
        return s([s([inr], 'ex', '( %s -> ( %s -> ( W ` %s ) e. ran %s ) )' % (pl, EQ, a, TAIL(a))), L(nta)], 'mtod', '( %s -> -. %s )' % (pl, EQ))
    h1 = half('x', 'y', xz, yz, xin, yin, ntx, 'eqcomd')
    h2 = half('y', 'x', yz, xz, yin, xin, nty, 'id')
    c1 = s([s([h1], 'pm2.21d', '( ( %s /\\ x < y ) -> ( %s -> x = y ) )' % (pxy, EQ))], 'ex', '( %s -> ( x < y -> ( %s -> x = y ) ) )' % (pxy, EQ))
    c2 = s([s([], 'simpr', '( ( %s /\\ x = y ) -> x = y )' % pxy)], 'a1d', '( ( %s /\\ x = y ) -> ( %s -> x = y ) )' % (pxy, EQ))
    c2 = s([c2], 'ex', '( %s -> ( x = y -> ( %s -> x = y ) ) )' % (pxy, EQ))
    c3 = s([s([h2], 'pm2.21d', '( ( %s /\\ y < x ) -> ( %s -> x = y ) )' % (pxy, EQ))], 'ex', '( %s -> ( y < x -> ( %s -> x = y ) ) )' % (pxy, EQ))
    tri = s([xr, yr, w.inst('lttri4')], 'syl2anc', '( %s -> ( x < y \\/ x = y \\/ y < x ) )' % pxy)
    inj = s([c1, c2, c3, tri], 'mpjao3dan' if False else '3jaod', '( %s -> ( ( x < y \\/ x = y \\/ y < x ) -> ( %s -> x = y ) ) )' % (pxy, EQ)) if False else \
        s([s([c1, c2, c3], '3jaod', '( %s -> ( ( x < y \\/ x = y \\/ y < x ) -> ( %s -> x = y ) ) )' % (pxy, EQ)), tri], 'mpd', '( %s -> ( %s -> x = y ) )' % (pxy, EQ))
    ral = s([inj], 'ralrimivva', '( %s -> A. x e. %s A. y e. %s ( %s -> x = y ) )' % (pa, R_, R_, EQ))
    f1 = s([s([s([], 'simpl', '( %s -> %s )' % (pa, A)), wf], 'syl', '( %s -> W : %s --> NN0 )' % (pa, R_)), ral], 'jca',
            '( %s -> ( W : %s --> NN0 /\\ A. x e. %s A. y e. %s ( %s -> x = y ) ) )' % (pa, R_, R_, R_, EQ))
    f1b = s([f1, s([], 'dff13', '( %s <-> ( W : %s --> NN0 /\\ A. x e. %s A. y e. %s ( %s -> x = y ) ) )' % (F1, R_, R_, R_, EQ))], 'sylibr', '( %s -> %s )' % (pa, F1))
    bwd = s([f1b], 'ex', '( %s -> ( %s -> %s ) )' % (A, ANDW, F1))
    iff1 = s([fwd, bwd], 'impbid', '( %s -> ( %s <-> %s ) )' % (A, F1, ANDW))
    # Fun `' W <-> F1 (~ df-f1 with W : R_ --> NN0)
    df1 = s([], 'df-f1', "( %s <-> ( W : %s --> NN0 /\\ Fun `' W ) )" % (F1, R_))
    fb = s([wf], 'biantrurd', "( %s -> ( Fun `' W <-> ( W : %s --> NN0 /\\ Fun `' W ) ) )" % (A, R_))
    fb2 = s([fb, s([df1], 'a1i', "( %s -> ( %s <-> ( W : %s --> NN0 /\\ Fun `' W ) ) )" % (A, F1, R_))], 'bitr4d', "( %s -> ( Fun `' W <-> %s ) )" % (A, F1))
    fst = s([ww, w.inst('noduptdfst')], 'syl', "( %s -> ( %s = 1o <-> Fun `' W ) )" % (A, ND1))
    iff = s([fst, s([fb2, iff1], 'bitrd', "( %s -> ( Fun `' W <-> %s ) )" % (A, ANDW))], 'bitrd', '( %s -> ( %s = 1o <-> %s ) )' % (A, ND1, ANDW))
    n2 = s([s([ww, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. ( 2o X. NN0 ) )' % A), w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (A, ND1))
    w.qed([flag_if(w, A, ANDW, ND1, iff, n2), w.inst('biid')], 'mpbi', ST_NDFST)
    return w.run()



# ------------------------------------------------------------ the loop: nda = accLoopF ndBody at the family (bit bound B , 1 <_ B)
ACC = lambda k: 'if ( A. i e. ( 0 ..^ %s ) %s , 1 , 0 )' % (k, NT('i'))
E1 = lambda k: EWg(ACC(k), DK(1))
PB = lambda k: UPS('D', ('1', E1(k)), ('5', C5(k)))
PF = '( k e. %s |-> %s )' % (DOM, PB('k'))
DATA_NDL = ((STKD('D'), ('W e. Word NN0', 'B e. NN0', '1 <_ B')), (RALB('W', 'B'), 'A. a e. ran W 1 <_ a', WG('R')), DEQ(5, ENCL('W', 'R')))
TREE_NDA = TREE0('nda', DATA_NDL)
PSI_T = (TREE_NDA, '%s = %s' % (PV, PF))
PSI = cj(PSI_T)
TBB = TB('B')
KC = '( ( 4 x. %s ) + 2 )' % TBB
YJ = lambda j: '( ( ( 6 x. %s ) x. ( %s - %s ) ) + %s )' % (TBB, NW, j, KC)
YF = '( i e. NN0 |-> %s )' % YJ('i')
UC = '( ( ( 6 x. %s ) x. %s ) + ( %s x. ( %s + 2 ) ) )' % (TBB, ND2, NW, KC)
LMA = FRAGS['nda'].lmap()
GM_ND = {'A0': LMA['Z1'], 'P0': LMA['Z2'], 'P1': LMA['Z3'], 'A': LMA['Z4'], "A'": LMA['Y1'], 'A"': LMA['Z5'], "E'": LMA['Z6'], 'E"': LMA['Z7'],
         'Q': PL('P', 8), 'Q1': PL('P', 9), 'E': 'E', 'L': LG, 'R': 'R', 'D': 'D', 'P': PV, 'Y': YF, 'U': UC, 'G': ACC(NLG), 'B': 'B'}
_GA, _GC = split_imp(STMTS12['tmiacl'])
GTREE = tsub(parse_conj(_GA), GM_ND)
GCONCL = tsub_text(_GC, GM_ND)
_fl = flat(GTREE)
PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NLG):]
FTY = [t for t in _fl if t.startswith('%s : ' % PV)][0]
FCOL = [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
P0EQ = [t for t in _fl if t.startswith('( %s ` 0 ) = ' % PV)][0]
PNEQ = [t for t in _fl if t.startswith('( %s ` %s ) = ' % (PV, NLG))][0]
SUMLE = [t for t in _fl if t.startswith('sum_ ')][0]
HOARE_YJ = PERB.split(' /\\ ', 1)[1][:-2].rsplit(' , ', 1)[0] + ' , %s >.' % YJ('j')
add12('tmindbi', (PSI_T, 'j e. ( 0 ..^ %s )' % NLG), HOARE_YJ)
add12('tmindat', PSI_T, '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (FTY, FCOL, P0EQ, PNEQ))
NDFLAG = 'if ( if ( %s , 1 , 0 ) = 0 , (/) , 1o )' % ANDW
NDAC = '( %s + ( ( 2 x. %s ) + 6 ) )' % (UC, TBB)
CONCL_NDAL = TRI(CS('nda'), CLN('E', NFL(NDFLAG), UP('D', '5', 'R')), NDAC)
add12('tmindal', PSI_T, CONCL_NDAL)
DATA_ND = ((STKD('D'), ('W e. Word NN0', 'B e. NN0', '1 <_ B')), (RALB('W', 'B'), 'A. a e. ran W 1 <_ a', WG('X')), DEQ(4, ENCL('W', 'X')))
TREE_ND = TREE0('nd', DATA_ND)
CONCL_ND = TRI(CS('nd'), CLN('E', NFL(ND1), 'D'), '( ( %s + 1 ) x. ( ; 1 6 x. %s ) )' % (ND2, TBB))
add12('tmind', TREE_ND, CONCL_ND)


class Nda(Base):
    def __init__(self, w, ph, T, fname='nda'):
        c0 = Ctx(w, ph, T)
        ww, bn, rw = c0['W e. Word NN0'], c0['B e. NN0'], c0[WG('R')]
        Base.__init__(self, w, ph, T, N8, fname, {'5': (ENCL('W', 'R'), enclg(w, ph, 'W', ww, 'R', rw))})
        s = w.s
        self.ww, self.bn, self.rw = ww, bn, rw
        c = self.c
        self.b1 = c['1 <_ B']
        self.lgw = s([ww, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, LG, BITS))
        self.lg = s([ww, closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = %s )' % (ph, NLG, NW))
        self.nw = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
        self.nlg = s([self.lgw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLG))
        self.cl = Closure(w, ph, {'B': ('NN0', bn)})
        self.cl.leaf(NW, 'NN0', self.nw); self.cl.leaf(NLG, 'NN0', self.nlg)
        self.cl.leaf(TBB, 'NN0', tmbn(w, ph, 'B', bn))
        self.cl.atom('( 2 ^ B )')
        self.d1 = self.S0.vals['1'][2]
        u1 = s([s([closed(w, ph, '1z', '1 e. ZZ'), s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph), self.b1], '3jca', '( %s -> ( 1 e. ZZ /\\ B e. ZZ /\\ 1 <_ B ) )' % ph),
                w.inst('eluz2')], 'sylibr', '( %s -> B e. ( ZZ>= ` 1 ) )' % ph)
        p1 = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), u1, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ 1 ) <_ ( 2 ^ B ) )' % ph)
        e21 = s([s([s([], '2cn', '2 e. CC'), w.inst('exp1')], 'ax-mp', '( 2 ^ 1 ) = 2')], 'a1i', '( %s -> ( 2 ^ 1 ) = 2 )' % ph)
        self.two_le = s([e21, p1], 'eqbrtrrd', '( %s -> 2 <_ ( 2 ^ B ) )' % ph)
        self.tb1 = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TBB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TBB))

    def accn(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        a = s([closed(w, ph, '1nn0', '1 e. NN0'), closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, ACC(k)))
        cond = 'A. i e. ( 0 ..^ %s ) %s' % (k, NT('i'))
        pt, pn = '( %s /\\ %s )' % (ph, cond), '( %s /\\ -. %s )' % (ph, cond)
        l1 = s([s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = 1 )' % (pt, ACC(k))), closed(w, pt, '1le1', '1 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pt, ACC(k)))
        l2 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond))], 'iffalsed', '( %s -> %s = 0 )' % (pn, ACC(k))), closed(w, pn, '0le1', '0 <_ 1')],
               'eqbrtrd', '( %s -> %s <_ 1 )' % (pn, ACC(k)))
        return a, s([l1, l2], 'pm2.61dan', '( %s -> %s <_ 1 )' % (ph, ACC(k)))

    def acclt(self, k):
        an, le = self.accn(k)
        cl = Closure(self.w, self.ph, {'B': ('NN0', self.bn)})
        cl.leaf(ACC(k), 'NN0', an)
        cl.atom('( 2 ^ B )')
        return an, linarith(self.w, self.ph, [le, self.two_le], '%s < ( 2 ^ B )' % ACC(k), closure=cl)

    def pbst(self, k):
        w, ph, s = self.w, self.ph, self.w.s
        an, _ = self.accn(k)
        g1 = self.g(E1(k), ewg_(w, ph, ACC(k), an, DK(1), self.d1))
        sw = s([self.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, k, NLG, BITS))
        eb = s([sw, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(k)))
        g5 = self.g(C5(k), wgcat(w, ph, EB(k), 'R', eb, self.rw))
        return self.S0.upd('1', E1(k), g1).upd('5', C5(k), g5)


def ifn_bi(w, ph, m):
    """( ph -> ( if ( m , (/) , 1o ) = 1o <-> -. m ) )"""
    s = w.s
    O = 'if ( %s , (/) , 1o )' % m
    pt, pn = '( %s /\\ %s )' % (ph, m), '( %s /\\ -. %s )' % (ph, m)
    a = s([s([], 'simpr', '( %s -> %s )' % (pt, m))], 'iftrued', '( %s -> %s = (/) )' % (pt, O))
    n0 = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o'), s([], 'neneq', '( (/) =/= 1o -> -. (/) = 1o )')], 'ax-mp', '-. (/) = 1o')
    na = s([s([n0], 'a1i', '( %s -> -. (/) = 1o )' % pt), s([a], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (pt, O))], 'mtbird', '( %s -> -. %s = 1o )' % (pt, O))
    nm = s([s([], 'simpr', '( %s -> %s )' % (pt, m))], 'notnotd', '( %s -> -. -. %s )' % (pt, m))
    t1 = s([na, nm], '2falsed', '( %s -> ( %s = 1o <-> -. %s ) )' % (pt, O, m))
    b = s([s([], 'simpr', '( %s -> -. %s )' % (pn, m))], 'iffalsed', '( %s -> %s = 1o )' % (pn, O))
    t2 = s([b, s([], 'simpr', '( %s -> -. %s )' % (pn, m))], '2thd', '( %s -> ( %s = 1o <-> -. %s ) )' % (pn, O, m))
    return s([t1, t2], 'pm2.61dan', '( %s -> ( %s = 1o <-> -. %s ) )' % (ph, O, m))


def tmindbi():
    lab = 'tmindbi'
    T = numtree((PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    ph = cj(T)
    w = W(lab, 'One entry of Lean\'s ` nodupTDF ` loop at the machine ( ` ndBody_runs ` ): along the family of the accumulator, '
               '` moveEntry 5 1 2 ` (~ tmime ) lifts the entry above the accumulator, ` memList 5 1 2 3 6 ` (~ tmimlsb ) tests it '
               'against the tail, ` dropNum 1 ` (~ tmidropnb ), ` load\' ( flag := !flag ) ` , ` accAnd ` (~ tmiaca ).')
    s = w.s
    B = Nda(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    jj = c['j e. ( 0 ..^ %s )' % NLG]
    jW = s([jj, s([B.lg], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ %s ) )' % (ph, NLG, NW))], 'eleqtrd', '( %s -> j e. ( 0 ..^ %s ) )' % (ph, NW))
    jz = s([jj, w.inst('elfzofz')], 'syl', '( %s -> j e. %s )' % (ph, DOM))
    J1 = '( j + 1 )'
    j1 = s([jj, w.inst('fzofzp1')], 'syl', '( %s -> %s e. %s )' % (ph, J1, DOM))
    jn = s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % ph)
    fam = c['%s = %s' % (PV, PF)]
    pvj, SJ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, 'j', jz, B.pbst('j'))
    PTX = '( %s ` j )' % PV
    WJ = '( W ` j )'
    dr = s([B.lgw, jj, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, EB('j'), LG, EB(J1)))
    lgj = s([s([B.ww, w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ %s ) --> NN0 )' % (ph, NW)), jW, w.inst('fvco3')], 'syl2anc',
            '( %s -> ( %s ` j ) = ( encNatGam ` %s ) )' % (ph, LG, WJ))
    wjn = s([B.ww, jW, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, WJ))
    sw1 = s([B.lgw, w.inst('swrdcl')], 'syl', '( %s -> ( %s substr <. %s , %s >. ) e. Word Word %s )' % (ph, LG, J1, NLG, BITS))
    eb1 = s([sw1, w.inst('tm2lencbcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB(J1)))
    g4 = wg4(w, ph, EB(J1), eb1)
    egj = s([lgj, encw(w, ph, WJ, wjn)], 'eqeltrd', "( %s -> ( %s ` j ) e. Word Gamma' )" % (ph, LG))
    ca1 = s([egj, g4, B.rw, w.inst('ccatass')], 'syl3anc',
            '( %s -> ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (ph, LG, EB(J1), LG, EB(J1)))
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    ca2 = s([s4, eb1, B.rw, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ R ) = ( <" 4 "> ++ %s ) )' % (ph, EB(J1), C5(J1)))
    r1 = s([s([dr], 'oveq1d', '( %s -> %s = ( ( ( %s ` j ) ++ ( <" 4 "> ++ %s ) ) ++ R ) )' % (ph, C5('j'), LG, EB(J1))), ca1], 'eqtrd',
           '( %s -> %s = ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (ph, C5('j'), LG, EB(J1)))
    V5 = EWg(WJ, C5(J1))
    r2 = s([lgj, ca2], 'oveq12d', '( %s -> ( ( %s ` j ) ++ ( ( <" 4 "> ++ %s ) ++ R ) ) = %s )' % (ph, LG, EB(J1), V5))
    iv = s([SJ.vals['5'][1], s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, C5('j'), V5))], 'eqtrd', '( %s -> ( %s ` 5 ) = %s )' % (ph, PTX, V5))
    g51 = B.g(C5(J1), wgcat(w, ph, EB(J1), 'R', eb1, B.rw))
    wr = s([s([B.ww, w.inst('wrdfn')], 'syl', '( %s -> W Fn ( 0 ..^ %s ) )' % (ph, NW)), jW, w.inst('fnfvelrn')], 'syl2anc', '( %s -> %s e. ran W )' % (ph, WJ))
    wjlt = s([s([], 'breq1', '( a = %s -> ( a < ( 2 ^ B ) <-> %s < ( 2 ^ B ) ) )' % (WJ, WJ)), wr, c[RALB('W', 'B')]], 'rspcdva', '( %s -> %s < ( 2 ^ B ) )' % (ph, WJ))
    accj, acclt = B.acclt('j')
    cl.leaf(ACC('j'), 'NN0', accj)
    # the tail as a list of numbers: C5( j + 1 ) = ENCL( TL , R )
    TL = SUB(J1)
    j1W = s([jW, w.inst('fzofzp1')], 'syl', '( %s -> %s e. ( 0 ... %s ) )' % (ph, J1, NW))
    nfz = s([B.nw, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NW, NW))
    tlw = s([B.ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, TL))
    sco = s([B.ww, s([j1W, nfz], 'jca', '( %s -> ( %s e. ( 0 ... %s ) /\\ %s e. ( 0 ... %s ) ) )' % (ph, J1, NW, NW, NW)),
             closed(w, ph, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('swrdco')], 'syl3anc',
            '( %s -> ( encNatGam o. %s ) = ( %s substr <. %s , %s >. ) )' % (ph, TL, LG, J1, NW))
    ebw = s([s([B.lg], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, J1, NLG, J1, NW))], 'oveq2d',
            '( %s -> ( %s substr <. %s , %s >. ) = ( %s substr <. %s , %s >. ) )' % (ph, LG, J1, NLG, LG, J1, NW))
    tle = s([tlw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` ( encNatGam o. %s ) ) )' % (ph, TL, TL))
    c5e = s([s([s([tle, s([sco], 'fveq2d', '( %s -> ( encListB ` ( encNatGam o. %s ) ) = ( encListB ` ( %s substr <. %s , %s >. ) ) )' % (ph, TL, LG, J1, NW))], 'eqtrd',
                  '( %s -> ( encList ` %s ) = ( encListB ` ( %s substr <. %s , %s >. ) ) )' % (ph, TL, LG, J1, NW)),
                s([ebw], 'fveq2d', '( %s -> %s = ( encListB ` ( %s substr <. %s , %s >. ) ) )' % (ph, EB(J1), LG, J1, NW))], 'eqtr4d',
               '( %s -> ( encList ` %s ) = %s )' % (ph, TL, EB(J1)))], 'oveq1d', '( %s -> %s = %s )' % (ph, ENCL(TL, 'R'), C5(J1)))
    rnss = s([s([B.ww, j1W, nfz, w.inst('swrdrn3')], 'syl3anc', '( %s -> ran %s = ( W " ( %s ..^ %s ) ) )' % (ph, TL, J1, NW)),
              s([s([], 'imassrn', '( W " ( %s ..^ %s ) ) C_ ran W' % (J1, NW))], 'a1i', '( %s -> ( W " ( %s ..^ %s ) ) C_ ran W )' % (ph, J1, NW))], 'eqsstrd',
             '( %s -> ran %s C_ ran W )' % (ph, TL))
    rtl = s([rnss, c[RALB('W', 'B')], w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ph, RALB(TL, 'B')))
    # the Run
    B.deep('nda', 0)
    v2 = dict(SJ.vals)
    v2['5'] = (V5, iv, B.g(V5, ewg_(w, ph, WJ, wjn, C5(J1), g51)))
    SJ2 = Stacks(w, ph, mk, SJ.D, SJ.memb, SJ.ne, v2)
    R = B.run(SJ2)
    lm_ndb = FRAGS['ndb'].lmap(PL('P', 7), LMA['Z5'])
    P7 = PL('P', 7)
    # 1. moveEntry 5 1 2
    WWJ = '( encNatGam ` %s )' % WJ
    V1 = EWg(WJ, E1('j'))
    B.call(R, 'tmime', {'K': '5', 'J': '1', 'I': '2', 'W': WWJ, 'X': C5(J1), 'P': PL(P7, 1), 'E': lm_ndb['Y2']},
           {WRD(WWJ, BITS): engb(w, ph, WJ, wjn), WG(C5(J1)): g51}, [('5', C5(J1), g51), ('1', V1, B.g(V1, ewg_(w, ph, WJ, wjn, E1('j'), B.gam[E1('j')])))])
    # 2. memList 5 1 2 3 6 on the tail
    MEM = '( W ` j ) e. ran %s' % TL
    B.call(R, 'tmimlsb', {'L': TL, 'A': WJ, 'B': 'B', 'R': 'R', 'X': E1('j'), 'P': PL(P7, 2), 'E': lm_ndb['Y3']},
           {'%s e. Word NN0' % TL: tlw, '%s e. NN0' % WJ: wjn, '%s < ( 2 ^ B )' % WJ: wjlt, RALB(TL, 'B'): rtl, WG(E1('j')): B.gam[E1('j')],
            '( %s ` 5 ) = %s' % (R.S.D, ENCL(TL, 'R')): s([R.S.vals['5'][1], s([c5e], 'eqcomd', '( %s -> %s = %s )' % (ph, C5(J1), ENCL(TL, 'R')))], 'eqtrd',
                                                          '( %s -> ( %s ` 5 ) = %s )' % (ph, R.S.D, ENCL(TL, 'R')))}, [])
    V = 'if ( %s , 1o , (/) )' % MEM
    V2 = 'if ( %s , (/) , 1o )' % MEM
    # 3. dropNum 1
    Son, old = expose(w, ph, B, R, '1')
    B.call(R, 'tmidropnb', {'K': '1', 'F': WJ, 'N': 'B', 'X': E1('j'), 'O': V, 'P': PL(P7, 3), 'E': LMA['Y1'] if False else lm_ndb['Z1']},
           {'%s e. NN0' % WJ: wjn, '%s < ( 2 ^ B )' % WJ: wjlt, WG(E1('j')): B.gam[E1('j')]}, [('1', E1('j'), B.gam[E1('j')])], on=(Son, old))
    # 4. flag := !flag
    kw = lambda t: dict(fl='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t)
    B.call(R, 'tm2flg', {'A': lm_ndb['Z1'], 'E': lm_ndb['Y4'], 'F': L_NOTF, 'N': NFL(V), "N'": NFL(V2)},
           {LTY(L_NOTF): lset_ty2(w, ph, mk, L_NOTF, kw), SSS(NFL(V)): B.ss(NFL(V)), SSS(NFL(V2)): B.ss(NFL(V2)),
            'A. r e. %s ( %s ` r ) e. %s' % (NFL(V), L_NOTF, NFL(V2)): load_nfl(w, ph, mk, L_NOTF, kw, V, V2, notif_fleq(w, MEM))}, [])
    # 5. accAnd
    IFO = 'if ( %s = 1o , %s , 0 )' % (V2, ACC('j'))
    ifon = s([accj, closed(w, ph, '0nn0', '0 e. NN0'), w.inst('ifcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, IFO))
    EI = EWg(IFO, DK(1))
    B.call(R, 'tmiaca', {'A': ACC('j'), 'B': 'B', 'X': DK(1), 'O': V2, 'P': PL(P7, 4), 'E': LMA['Z5']},
           {'%s e. NN0' % ACC('j'): accj, '%s < ( 2 ^ B )' % ACC('j'): acclt, WG(DK(1)): B.d1}, [('1', EI, B.g(EI, ewg_(w, ph, IFO, ifon, DK(1), B.d1)))])
    e, nrm, out2 = renorm(w, ph, B, R, [('1', E1('j')), ('5', C5('j'))], N8, PT=PTX, pv=pvj)
    assert out2 == [('1', EI), ('5', C5(J1))], out2
    jn0 = s([jn, w.inst('elnn0uz')], 'sylib', '( %s -> j e. ( ZZ>= ` 0 ) )' % ph)
    ast = acc_step(w, ph, jn, jn0, NT, '%s = 1o' % V2, ifn_bi(w, ph, MEM))
    r_, nrm2 = w.rewrite(nrm, {IFO: (ACC(J1), ast)}, ph)
    assert nrm2 == PB(J1), '\n%s\n%s' % (nrm2, PB(J1))
    pv1, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, J1, j1, B.pbst(J1))
    D0 = triple_D(R.cur)
    deq = s([s([e, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D0, PB(J1))), pv1], 'eqtr4d', '( %s -> %s = ( %s ` %s ) )' % (ph, D0, PV, J1))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, LMA['Z5'], S, deq, D0, '( %s ` %s )' % (PV, J1)))
    # the bound: # TL = # W - ( j + 1 )
    sl = s([B.ww, j1W, nfz, w.inst('swrdlen')], 'syl3anc', '( %s -> ( # ` %s ) = ( %s - %s ) )' % (ph, TL, NW, J1))
    cl.leaf('( # ` %s )' % TL, 'NN0', s([tlw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, TL)))
    cl.leaf('j', 'NN0', jn)
    jlt = s([jW, w.inst('elfzolt2')], 'syl', '( %s -> j < %s )' % (ph, NW))
    dn = s([jn, B.nw, linarith(w, ph, [jlt], 'j <_ %s' % NW, closure=cl), w.inst('nn0sub2')], 'syl3anc', '( %s -> ( %s - j ) e. NN0 )' % (ph, NW))
    cl.leaf('( %s - j )' % NW, 'NN0', dn)
    mc = me_bound_n(w, ph, WJ, wjn, wjlt, 'B', B.bn, cl)
    # the tail length as ( # W - ( j + 1 ) ) inside the cost (a product: rewrite before the linear step)
    rn, n2 = w.rewrite(n, {'( # ` %s )' % TL: ('( %s - %s )' % (NW, J1), sl)}, ph)
    t, C, D, n = hrrw(w, ph, t, C, D, n, neq=rn)
    # ( ( # W - ( j + 1 ) ) + 1 ) = ( # W - j ) before the product meets the linear step
    NJ = '( %s - j )' % NW
    ss4 = s([cl.mem(NW, 'CC'), cl.mem('j', 'CC'), closed(w, ph, 'ax-1cn', '1 e. CC'), w.inst('subsub4')], 'syl3anc',
             '( %s -> ( %s - 1 ) = ( %s - %s ) )' % (ph, NJ, NW, J1))
    npc = s([cl.mem(NJ, 'CC'), closed(w, ph, 'ax-1cn', '1 e. CC'), w.inst('npcan')], 'syl2anc', '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (ph, NJ, NJ))
    e1 = s([s([ss4], 'oveq1d', '( %s -> ( ( %s - 1 ) + 1 ) = ( ( %s - %s ) + 1 ) )' % (ph, NJ, NW, J1)), npc], 'eqtr3d',
           '( %s -> ( ( %s - %s ) + 1 ) = %s )' % (ph, NW, J1, NJ))
    rn2, n3 = w.rewrite(n, {'( ( %s - %s ) + 1 )' % (NW, J1): ('( %s - j )' % NW, e1)}, ph)
    t, C, D, n = hrrw(w, ph, t, C, D, n, neq=rn2)
    print('NDBI n =', n, '\nNDBI goal =', YJ('j'), file=sys.stderr)
    le = linarith(w, ph, [mc, cl.ge0(TBB), cl.ge0('j'), cl.ge0(NW)], '%s <_ %s' % (n, YJ('j')), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, YJ('j'), cl.mem(YJ('j'), 'NN0'), le)
    assert TRI(C, D, YJ('j')) == HOARE_YJ, '\n%s\n%s' % (TRI(C, D, YJ('j')), HOARE_YJ)
    finish(w, st, lab)
    return w.run()


def tmindat():
    lab = 'tmindat'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'The frame of Lean\'s ` nodupTDF ` loop at the machine: the family of the accumulator is a stack family whose 5 '
               'column is the rest of the copied list, at 0 it is the stacks with the accumulator ` 1 ` pushed, at the end the '
               'accumulator is the conjunction of the tail tests and the list\'s ` bra ` remains.')
    s = w.s
    B = Nda(w, ph, T)
    c, mk = B.c, B.mk
    fam = c['%s = %s' % (PV, PF)]
    ph0t = (TREE_NDA, NUMS)
    ph0 = cj(ph0t)
    TK = (ph0t, 'k e. %s' % DOM)
    pk = cj(TK)
    Bk = Nda(w, pk, TK)
    Sk = Bk.pbst('k')
    fm = s([Sk.memb], 'fmptd', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph0, PF, DOM))
    j0 = s([c[cj(TREE_NDA)], c[cj(NUMS)]], 'jca', '( %s -> %s )' % (ph, ph0))
    fm2 = s([j0, fm], 'syl', '( %s -> %s : %s --> ( TM2Stk ` T ) )' % (ph, PF, DOM))
    fty = s([s([fam], 'feq1d', '( %s -> ( %s : %s --> ( TM2Stk ` T ) <-> %s : %s --> ( TM2Stk ` T ) ) )' % (ph, PV, DOM, PF, DOM)), fm2],
            'mpbird', '( %s -> %s )' % (ph, FTY))
    TJ = (T, 'j e. %s' % DOM)
    pj = cj(TJ)
    Bj = Nda(w, pj, TJ)
    jz = Bj.c['j e. %s' % DOM]
    _, SJ = fam_at(w, pj, Bj.mk, Bj.ne, Bj.c['%s = %s' % (PV, PF)], PV, 'k', DOM, PB, 'j', jz, Bj.pbst('j'))
    col = s([SJ.vals['5'][1]], 'ralrimiva', '( %s -> %s )' % (ph, FCOL))
    z0 = s([B.nlg, w.inst('0elfz')], 'syl', '( %s -> 0 e. %s )' % (ph, DOM))
    pv0, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, '0', z0, B.pbst('0'))
    a0 = s([s([s([], 'ral0', 'A. i e. (/) %s' % NT('i')), s([s([], 'fzo0', '( 0 ..^ 0 ) = (/)')], 'raleqi',
                                                          '( A. i e. ( 0 ..^ 0 ) %s <-> A. i e. (/) %s )' % (NT('i'), NT('i')))], 'mpbir',
              'A. i e. ( 0 ..^ 0 ) %s' % NT('i'))], 'iftruei', '%s = 1' % ACC('0'))
    e1 = s([s([s([a0], 'a1i', '( %s -> %s = 1 )' % (ph, ACC('0')))], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` 1 ) )' % (ph, ACC('0')))], 'oveq1d',
           '( %s -> %s = %s )' % (ph, E1('0'), EWg('1', DK(1))))
    d0 = s([B.lgw, w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , %s >. ) = %s )' % (ph, LG, NLG, LG))
    le_ = s([B.ww, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` W ) = ( encListB ` %s ) )' % (ph, LG))
    e5 = s([s([s([d0], 'fveq2d', '( %s -> %s = ( encListB ` %s ) )' % (ph, EB('0'), LG)), le_], 'eqtr4d', '( %s -> %s = ( encList ` W ) )' % (ph, EB('0')))],
           'oveq1d', '( %s -> %s = %s )' % (ph, C5('0'), ENCL('W', 'R')))
    e5b = s([e5, s([c[DEQ(5, ENCL('W', 'R'))]], 'eqcomd', '( %s -> %s = ( D ` 5 ) )' % (ph, ENCL('W', 'R')))], 'eqtrd', '( %s -> %s = ( D ` 5 ) )' % (ph, C5('0')))
    rr, xx = w.rewrite(PB('0'), {E1('0'): (EWg('1', DK(1)), e1), C5('0'): ('( D ` 5 )', e5b)}, ph)
    assert xx == UPS('D', ('1', EWg('1', DK(1))), ('5', DK(5))), xx
    B.g(EWg('1', DK(1)), ewg_(w, ph, '1', closed(w, ph, '1nn0', '1 e. NN0'), DK(1), B.d1))
    nst, outn = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, [('1', EWg('1', DK(1))), ('5', DK(5))], B.gam, N8)
    assert outn == [('1', EWg('1', DK(1)))], outn
    p0 = s([s([pv0, rr], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PV, xx)), nst], 'eqtrd', '( %s -> %s )' % (ph, P0EQ))
    nz = s([B.nlg, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. %s )' % (ph, NLG, DOM))
    pvN, _ = fam_at(w, ph, mk, B.ne, fam, PV, 'k', DOM, PB, NLG, nz, B.pbst(NLG))
    DR = '( %s substr <. %s , %s >. )' % (LG, NLG, NLG)
    e2 = s([s([closed(w, ph, 'swrd00', '%s = (/)' % DR)], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` (/) ) )' % (ph, DR)),
            closed(w, ph, 'tm2lencb0', '( encListB ` (/) ) = <" 2 ">')], 'eqtrd', '( %s -> ( encListB ` %s ) = <" 2 "> )' % (ph, DR))
    e5n = s([e2], 'oveq1d', '( %s -> %s = ( <" 2 "> ++ R ) )' % (ph, C5(NLG)))
    rN, xN = w.rewrite(PB(NLG), {C5(NLG): ('( <" 2 "> ++ R )', e5n)}, ph)
    pn = s([pvN, rN], 'eqtrd', '( %s -> %s )' % (ph, PNEQ))
    st = s([s([fty, col], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL)), s([p0, pn], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))],
           'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (ph, FTY, FCOL, P0EQ, PNEQ))
    finish(w, st, lab)
    return w.run()


def tmindal():
    lab = 'tmindal'
    T = numtree(PSI_T)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` accLoopF ndBody ` at the machine: ~ tmiacl at the family of the accumulator ( ` P\' ` a letter; the '
               'entries by ~ tmindbi , the frame by ~ tmindat , the entries\' budget summed by ~ t12ndcost ); the flag is the '
               'conjunction of the tail tests over the list, the list\'s ` bra ` is gone from 5.')
    s = w.s
    B = Nda(w, ph, T)
    c, mk, cl = B.c, B.mk, B.cl
    ex = dict(B.ex)
    B.deep('nda', 0)
    ex = dict(B.ex)
    fr = lift_from(w, PSI, ph, s([], 'tmindat', STMTS12['tmindat']))
    a1 = s([fr], 'simpld', '( %s -> ( %s /\\ %s ) )' % (ph, FTY, FCOL))
    a2 = s([fr], 'simprd', '( %s -> ( %s /\\ %s ) )' % (ph, P0EQ, PNEQ))
    ex[FTY] = s([a1], 'simpld', '( %s -> %s )' % (ph, FTY))
    ex[FCOL] = s([a1], 'simprd', '( %s -> %s )' % (ph, FCOL))
    ex[P0EQ] = s([a2], 'simpld', '( %s -> %s )' % (ph, P0EQ))
    ex[PNEQ] = s([a2], 'simprd', '( %s -> %s )' % (ph, PNEQ))

    def yjeq(pj, jn, ycn):
        return s([jn, ycn, s([w.congr(YJ('i'), {'i': 'j'}, 'i = j', {'i': s([], 'id', '( i = j -> i = j )')})[0], s([], 'eqid', '%s = %s' % (YF, YF))], 'fvmptg',
                             '( ( j e. NN0 /\\ %s e. NN0 ) -> ( %s ` j ) = %s )' % (YJ('j'), YF, YJ('j')))], 'syl2anc', '( %s -> ( %s ` j ) = %s )' % (pj, YF, YJ('j')))

    def clj_of(pj, T_):
        cj_ = Ctx(w, pj, T_)
        bnj, wwj, jj_ = cj_['B e. NN0'], cj_['W e. Word NN0'], cj_['j e. ( 0 ..^ %s )' % NLG]
        clj = Closure(w, pj, {'B': ('NN0', bnj)})
        clj.leaf(TBB, 'NN0', tmbn(w, pj, 'B', bnj))
        nwj = s([wwj, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pj, NW))
        clj.leaf(NW, 'NN0', nwj)
        jn = s([jj_, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj)
        clj.leaf('j', 'NN0', jn)
        # ( # W - j ) e. NN0 : j < # LG = # W
        lgj = s([wwj, closed(w, pj, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc', '( %s -> %s = %s )' % (pj, NLG, NW))
        jW = s([jj_, s([lgj], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ %s ) )' % (pj, NLG, NW))], 'eleqtrd', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NW))
        jlt = s([jW, w.inst('elfzolt2')], 'syl', '( %s -> j < %s )' % (pj, NW))
        dn = s([s([jn, nwj], 'jca', '( %s -> ( j e. NN0 /\\ %s e. NN0 ) )' % (pj, NW)), linarith(w, pj, [jlt], 'j <_ %s' % NW, closure=clj), w.inst('nn0sub')], 'sylc' if False else 'syl',
               '') if False else None
        dn = s([jn, nwj, linarith(w, pj, [jlt], 'j <_ %s' % NW, closure=clj), w.inst('nn0sub2')], 'syl3anc', '( %s -> ( %s - j ) e. NN0 )' % (pj, NW))
        clj.leaf('( %s - j )' % NW, 'NN0', dn)
        return clj, jn, nwj
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (PSI, NLG)
    bj = s([], 'tmindbi', STMTS12['tmindbi'])
    clj, jn, _ = clj_of(pj, (PSI_T, 'j e. ( 0 ..^ %s )' % NLG))
    ycn = clj.mem(YJ('j'), 'NN0')
    yj = yjeq(pj, jn, ycn)
    Cb, Db, nb = triple_parts(HOARE_YJ)
    tb, _, _, _ = hrrw(w, pj, bj, Cb, Db, nb, neq=s([yj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (pj, YJ('j'), YF)))
    yjn = s([yj, ycn], 'eqeltrd', '( %s -> ( %s ` j ) e. NN0 )' % (pj, YF))
    perb = s([yjn, tb], 'jca', '( %s -> %s )' % (pj, PERB))
    ex[PER] = lift_from(w, PSI, ph, s([perb], 'ralrimiva', '( %s -> %s )' % (PSI, PER)))
    # the sum
    pj2 = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NLG)
    clj2, jn2, nwj2 = clj_of(pj2, (T, 'j e. ( 0 ..^ %s )' % NLG))
    ycn2 = clj2.mem(YJ('j'), 'NN0')
    yj2 = yjeq(pj2, jn2, ycn2)
    DJ = '( %s - j )' % NW
    TERM = '( ( ( 6 x. %s ) x. %s ) + ( %s + 2 ) )' % (TBB, DJ, KC)
    te = s([s([yj2], 'oveq1d', '( %s -> ( ( %s ` j ) + 2 ) = ( %s + 2 ) )' % (pj2, YF, YJ('j'))), lineq(w, pj2, '( %s + 2 )' % YJ('j'), TERM, closure=clj2)], 'eqtrd',
           '( %s -> ( ( %s ` j ) + 2 ) = %s )' % (pj2, YF, TERM))
    SJ_ = 'sum_ j e. ( 0 ..^ %s ) ( ( %s ` j ) + 2 )' % (NLG, YF)
    A_ = '( 0 ..^ %s )' % NLG
    se = s([te], 'sumeq2dv', '( %s -> %s = sum_ j e. %s %s )' % (ph, SJ_, A_, TERM))
    fzf = s([s([], 'fzofi', '%s e. Fin' % A_)], 'a1i', '( %s -> %s e. Fin )' % (ph, A_))
    SIX = '( 6 x. %s )' % TBB
    pcc = s([s([cl.mem(SIX, 'CC')], 'adantr', '( %s -> %s e. CC )' % (pj2, SIX)), clj2.mem(DJ, 'CC')], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (pj2, SIX, DJ))
    kcc = s([cl.mem('( %s + 2 )' % KC, 'CC')], 'adantr', '( %s -> ( %s + 2 ) e. CC )' % (pj2, KC))
    SA = 'sum_ j e. %s ( %s x. %s )' % (A_, SIX, DJ)
    SB = 'sum_ j e. %s ( %s + 2 )' % (A_, KC)
    e3 = s([fzf, pcc, kcc], 'fsumadd', '( %s -> sum_ j e. %s %s = ( %s + %s ) )' % (ph, A_, TERM, SA, SB))
    SC = 'sum_ j e. %s %s' % (A_, DJ)
    e4 = s([fzf, clj2.mem(DJ, 'CC'), cl.mem(SIX, 'CC')], 'fsummulc2', '( %s -> ( %s x. %s ) = %s )' % (ph, SIX, SC, SA))
    e5 = s([fzf, cl.mem('( %s + 2 )' % KC, 'CC'), w.inst('fsumconst')], 'syl2anc', '( %s -> %s = ( ( # ` %s ) x. ( %s + 2 ) ) )' % (ph, SB, A_, KC))
    hf = s([s([B.nlg, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, A_, NLG))], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( %s + 2 ) ) = ( %s x. ( %s + 2 ) ) )' % (ph, A_, KC, NLG, KC))
    sce = s([s([B.lg], 'oveq2d', '( %s -> %s = ( 0 ..^ %s ) )' % (ph, A_, NW))], 'sumeq1d', '( %s -> %s = %s )' % (ph, SC, SUMC))
    ndc = s([B.ww, w.inst('t12ndcost')], 'syl', '( %s -> %s = %s )' % (ph, ND2, SUMC))
    sc2 = s([sce, s([ndc], 'eqcomd', '( %s -> %s = %s )' % (ph, SUMC, ND2))], 'eqtrd', '( %s -> %s = %s )' % (ph, SC, ND2))
    ea = s([s([e4], 'eqcomd', '( %s -> %s = ( %s x. %s ) )' % (ph, SA, SIX, SC)), s([sc2], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ph, SIX, SC, SIX, ND2))],
           'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (ph, SA, SIX, ND2))
    eb = s([e5, hf, s([B.lg], 'oveq1d', '( %s -> ( %s x. ( %s + 2 ) ) = ( %s x. ( %s + 2 ) ) )' % (ph, NLG, KC, NW, KC))], '3eqtrd',
           '( %s -> %s = ( %s x. ( %s + 2 ) ) )' % (ph, SB, NW, KC))
    seq_ = s([se, e3, s([ea, eb], 'oveq12d', '( %s -> ( %s + %s ) = %s )' % (ph, SA, SB, UC))], '3eqtrd', '( %s -> %s = %s )' % (ph, SJ_, UC))
    ndn = s([s([B.ww, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, ND2))
    cl.leaf(ND2, 'NN0', ndn)
    sumr = s([s([seq_, cl.mem(UC, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, SJ_))], 'nn0red', '( %s -> %s e. RR )' % (ph, SJ_))
    ex[SUMLE] = s([sumr, seq_], 'eqled', '( %s -> %s )' % (ph, SUMLE))
    accN, accltN = B.acclt(NLG)
    ex['%s e. NN0' % ACC(NLG)] = accN
    ex['%s < ( 2 ^ B )' % ACC(NLG)] = accltN
    ex['%s e. Word Word %s' % (LG, BITS)] = B.lgw
    ex['%s e. NN0' % UC] = cl.mem(UC, 'NN0')
    ex[WG('R')] = B.rw
    st = Bld(w, ph, c, ex)(GTREE)
    st2 = s([st, w.inst('tmiacl')], 'syl', '( %s -> %s )' % (ph, GCONCL))
    C0, D0, n0 = triple_parts(GCONCL)
    rd, D1 = w.rewrite(D0, {NLG: (NW, B.lg)}, ph)
    t, C, D, n = hrrw(w, ph, st2, C0, D0, n0, deq=rd)
    assert TRI(C, D, n) == CONCL_NDAL, '\n%s\n%s' % (TRI(C, D, n), CONCL_NDAL)
    finish(w, t, lab)
    return w.run()


def tmind():
    lab = 'tmind'
    T = numtree(TREE_ND)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` nodupTDF_runs ` at the machine: ` copyList 4 5 2 3 ` (~ tmilcpyb ) then the accumulator loop '
               '(~ tmindal ); every stack restored, the flag ` ( 1st ( NodupTD S ) ) ` (~ t12ndfst ), within '
               '` ( ( nodupTD S ).2 + 1 ) 16 B b ` steps (with ` 1 <_ b ` ; T12-blueprint section 3).')
    s = w.s
    c0 = Ctx(w, ph, T)
    ww, bn, xw = c0['W e. Word NN0'], c0['B e. NN0'], c0[WG('X')]
    B = Base(w, ph, T, N8, 'nd', {'4': (ENCL('W', 'X'), enclg(w, ph, 'W', ww, 'X', xw))})
    c, mk = B.c, B.mk
    g = lambda k: B.S0.vals[k][2]
    LM = FRAGS['nd'].lmap()
    R = B.run()
    V5 = ENCL('W', DK(5))
    B.call(R, 'tmilcpyb', {'K': '4', 'J': '5', 'I': '2', "I'": '3', 'L': 'W', 'R': 'X', 'B': 'B', 'P': PL('P', 0), 'E': LM['Y2']},
           {}, [('5', V5, B.g(V5, enclg(w, ph, 'W', ww, DK(5), g('5'))))])
    PFi = tsub_text(PF, {'D': R.S.D, 'R': DK(5)})
    B.call(R, 'tmindal', {'W': 'W', 'B': 'B', 'R': DK(5), PV: PFi, 'P': PL('P', 1), 'E': 'E'},
           {WG(DK(5)): g('5'), '%s = %s' % (PFi, PFi): s([s([], 'eqid', '%s = %s' % (PFi, PFi))], 'a1i', '( %s -> %s = %s )' % (ph, PFi, PFi))},
           [('5', DK(5), g('5'))])
    cur, out = R.normalize(N8)
    assert out == [], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    fl = s([ww, w.inst('t12ndfst')], 'syl', '( %s -> %s = %s )' % (ph, ND1, NDFLAG))
    t, C, D, n = cls_to(w, ph, (t, C, D, n), NDFLAG, ND1, s([fl], 'eqcomd', '( %s -> %s = %s )' % (ph, NDFLAG, ND1)))
    cl = Closure(w, ph, {'B': ('NN0', bn)})
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
    cl.leaf(NW, 'NN0', nw)
    cl.leaf(TBB, 'NN0', tmbn(w, ph, 'B', bn))
    ndn = s([s([ww, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. ( 2o X. NN0 ) )' % ph), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, ND2))
    cl.leaf(ND2, 'NN0', ndn)
    # # W <_ ND2 : every term ( # W - j ) of the sum is at least 1
    ndc = s([ww, w.inst('t12ndcost')], 'syl', '( %s -> %s = %s )' % (ph, ND2, SUMC))
    pj = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NW)
    jj = s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (pj, NW))
    clj = Closure(w, pj, {})
    clj.leaf(NW, 'NN0', s([nw], 'adantr', '( %s -> %s e. NN0 )' % (pj, NW)))
    clj.leaf('j', 'NN0', s([jj, w.inst('elfzonn0')], 'syl', '( %s -> j e. NN0 )' % pj))
    jlt_ = s([jj, w.inst('elfzolt2')], 'syl', '( %s -> j < %s )' % (pj, NW))
    jp1 = s([jlt_, s([s([clj.mem('j', 'NN0')], 'nn0zd', '( %s -> j e. ZZ )' % pj), s([clj.mem(NW, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (pj, NW)), w.inst('zltp1le')], 'syl2anc',
                    '( %s -> ( j < %s <-> ( j + 1 ) <_ %s ) )' % (pj, NW, NW))], 'mpbid', '( %s -> ( j + 1 ) <_ %s )' % (pj, NW))
    one = linarith(w, pj, [jp1], '1 <_ ( %s - j )' % NW, closure=clj)
    fzf = s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NW)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NW))
    S1 = 'sum_ j e. ( 0 ..^ %s ) 1' % NW
    ge = s([fzf, closed(w, pj, '1re', '1 e. RR'), clj.mem('( %s - j )' % NW, 'RR'), one], 'fsumle', '( %s -> %s <_ %s )' % (ph, S1, SUMC))
    s1 = s([s([fzf, closed(w, ph, 'ax-1cn', '1 e. CC'), w.inst('fsumconst')], 'syl2anc', '( %s -> %s = ( ( # ` ( 0 ..^ %s ) ) x. 1 ) )' % (ph, S1, NW)),
            s([s([nw, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` ( 0 ..^ %s ) ) = %s )' % (ph, NW, NW))], 'oveq1d', '( %s -> ( ( # ` ( 0 ..^ %s ) ) x. 1 ) = ( %s x. 1 ) )' % (ph, NW, NW)),
            s([cl.mem(NW, 'CC')], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (ph, NW, NW))], '3eqtrd', '( %s -> %s = %s )' % (ph, S1, NW))
    nwle = s([s([s1], 'eqcomd', '( %s -> %s = %s )' % (ph, NW, S1)), s([ge, s([ndc], 'eqcomd', '( %s -> %s = %s )' % (ph, SUMC, ND2))], 'breqtrd', '( %s -> %s <_ %s )' % (ph, S1, ND2))],
             'eqbrtrd', '( %s -> %s <_ %s )' % (ph, NW, ND2))
    tb8 = s([bn, closed(w, ph, '8nn0', '8 e. NN0'), s([num.le_lit(w, '8', '; 6 4')], 'a1i', '( %s -> 8 <_ ; 6 4 )' % ph), w.inst('tmblin')], 'syl3anc',
            '( %s -> ( 8 x. ( B + 2 ) ) <_ %s )' % (ph, TBB))
    BND = triple_parts(CONCL_ND)[2]
    # the product monotonicity ( # W ) TMB <_ ND2 TMB (~ lemul2a ) for the nonlinear step
    j_ = s([s([cl.mem(NW, 'RR'), cl.mem(ND2, 'RR'), s([cl.mem(TBB, 'RR'), cl.ge0(TBB)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, TBB, TBB))], '3jca',
              '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (ph, NW, ND2, TBB, TBB)), nwle], 'jca',
           '( %s -> ( ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ %s <_ %s ) )' % (ph, NW, ND2, TBB, TBB, NW, ND2))
    mono2 = s([j_, w.inst('lemul2a')], 'syl', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, TBB, NW, TBB, ND2))
    t16 = linarith(w, ph, [tb8, cl.ge0('B')], '; 1 6 <_ %s' % TBB, closure=cl)
    j16 = s([s([s([num.nn0(w, 16)], 'nn0red', '; 1 6 e. RR') if False else closed(w, ph, '16re' if False else 'id', '') if False else s([s([num.nn0(w, 16)], 'a1i', '( %s -> ; 1 6 e. NN0 )' % ph)], 'nn0red', '( %s -> ; 1 6 e. RR )' % ph),
                cl.mem(TBB, 'RR'), s([cl.mem(ND2, 'RR'), cl.ge0(ND2)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, ND2, ND2))], '3jca',
              '( %s -> ( ; 1 6 e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (ph, TBB, ND2, ND2)), t16], 'jca',
           '( %s -> ( ( ; 1 6 e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ ; 1 6 <_ %s ) )' % (ph, TBB, ND2, ND2, TBB))
    m16 = s([j16, w.inst('lemul1a')], 'syl', '( %s -> ( ; 1 6 x. %s ) <_ ( %s x. %s ) )' % (ph, ND2, TBB, ND2))
    le = linarith(w, ph, [tb8, nwle, mono2, m16, cl.ge0('B'), cl.ge0(NW), cl.ge0(ND2), cl.ge0(TBB), cl.ge0('( %s x. %s )' % (TBB, ND2))], '%s <_ %s' % (n, BND), closure=cl, products=True)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
