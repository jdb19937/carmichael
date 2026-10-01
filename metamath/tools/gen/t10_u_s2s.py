"""T10: step2Succ at the machine (Lean ` step2Succ_runs ` ): the last ` T ` reservoir entries' product ` L ` on 3, ` L ^ 5 `
pushed under ` theta ` on 0 and under ` z ` on 1, the step counter 1 on 2, ` flag := true ` .

    MM_DB=sorties/t10.mm python3 tools/gen/t10_u_s2s.py tmis2s
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t10_e_doa import lift_from
from t10_n_rgf import tmbn
from t10_p_s2p import me_bound
from t7_h_iz import lset_val, lset_ty
import t8alib as A8
import num

SEL = sys.argv[1:]
F_ = FRAGS['s2s']
LM = F_.lmap()


def cp(j):
    """the P and E of the call at child slot j"""
    fn, cks, en, exn = F_.children[j]
    return PL('P', F_.slot(j)), LM[exn]


def expose(w, ph, B, R, k):
    """declare stack k of the current stacks as an outer update (identity), for ~ tmidropb"""
    Sc = R.S
    v = Sc.vals[k][0]
    u = upidv(w, ph, Sc.D, k, v, Sc.vals[k][1], B.mk['tv'], Sc.memb, B.mk['k'][k]['kd'])
    ue = w.s([u], 'eqcomd', '( %s -> %s = %s )' % (ph, Sc.D, UP(Sc.D, k, v)))
    head = R.cur[:-len(' X. { %s } ) )' % Sc.D)]
    lab = head.split('( { ( inl ` ', 1)[1].split(' ) } X. ( ', 1)[0]
    ncls = head.split(' } X. ( ', 1)[1]
    e = clneq(w, ph, lab, ncls, ue, Sc.D, UP(Sc.D, k, v))
    R.tri, _, R.cur, _ = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=e)
    old = list(R.chain)
    R.S = Sc.upd(k, v, Sc.vals[k][2])
    R.chain = old + [(k, v)]
    return Sc, old


def me_bound_n(w, ph, t, tn, tlt, NB, nbn, cl):
    """( ph -> ( ( 2 x. ( # ` ( encNatGam ` t ) ) ) + 4 ) <_ ( TMB ` NB ) ) from t < 2 ^ NB"""
    s = w.s
    WT = '( encNatGam ` %s )' % t
    LW = '( # ` %s )' % WT
    cl.leaf(LW, 'NN0', s([encw(w, ph, t, tn), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW)))
    lw = s([s([tn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` %s ) ) )' % (ph, LW, t)),
            s([tn, nbn, tlt, w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` %s ) ) <_ %s )' % (ph, t, NB))],
           'eqbrtrd', '( %s -> %s <_ %s )' % (ph, LW, NB))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    TN = '( TMB ` %s )' % NB
    qd = s([nbn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( %s + 2 ) ^ 2 ) ) <_ %s )' % (ph, NB, TN))
    return nlinarith(w, ph, [lw, qd, cl.ge0(NB), cl.ge0(LW)], '( ( 2 x. %s ) + 4 ) <_ %s' % (LW, TN), closure=cl,
                     atoms=[NB, LW, TN])


def tmis2s():
    lab = 'tmis2s'
    T = numtree(TREE_S2S)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` step2Succ_runs ` at the machine: ` subCx ` (~ tmiscxb ) computes ` len - T ` , ` dropN ` (~ tmidnb ) '
               'keeps the last ` T ` reservoir entries ` Q ` , ` prodLF ` (~ tmiprlb ) pushes ` L = ( ProdL Q ).1 ` on 3, '
               '` pow5F ` (~ tmip5b ) computes ` L ^ 5 ` , the moves place it under ` theta ` on 0 and under ` z ` on 1, '
               '` pushNum 2 1 ` and ` flag := true ` .')
    s = w.s
    c0 = Ctx(w, ph, T)
    ww, zn, un = c0['W e. Word NN0'], c0['Z e. NN0'], c0['U e. NN0']
    on, bn = c0['O e. NN0'], c0['B e. NN0']
    rw_, r1w, r2w, yw = c0[WG('R')], c0[WG("R'")], c0[WG('R"')], c0[WG('Y')]
    NW = '( # ` W )'
    nwn = s([ww, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NW))
    EOR = EWg('O', 'R')
    gor = ewg_(w, ph, 'O', on, 'R', rw_)
    guo = ewg_(w, ph, 'U', un, EOR, gor)
    eqs = {'0': (EWUO, guo), '1': (EWg('Z', "R'"), ewg_(w, ph, 'Z', zn, "R'", r1w)),
           '2': (EWg(NW, 'R"'), ewg_(w, ph, NW, nwn, 'R"', r2w)), '4': (ENCL('W', 'Y'), enclg(w, ph, 'W', ww, 'Y', yw))}
    B = Base(w, ph, T, N8, 's2s', eqs)
    c, mk = B.c, B.mk
    B.g(EOR, gor)
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    p2 = '( 2 ^ B )'
    cl = Closure(w, ph, {'U': ('NN0', un), 'Z': ('NN0', zn), 'B': ('NN0', bn), 'O': ('NN0', on)})
    cl.leaf(NW, 'NN0', nwn)
    cl.atom(p2)
    # 1. dup 2 5 6 ; 2. dup 0 6 5
    P, E = cp(0)
    E5 = EWg(NW, DK(5))
    B.call(R, 'tmidupb', {'K': '2', 'J': '5', 'I': '6', 'F': NW, 'N': 'B', 'X': 'R"', 'P': P, 'E': E},
           {'%s e. NN0' % NW: nwn, '%s < %s' % (NW, p2): c['%s < %s' % (NW, p2)]}, [('5', E5, B.g(E5, ewg_(w, ph, NW, nwn, DK(5), g('5'))))])
    P, E = cp(1)
    E6 = EWg('U', DK(6))
    B.call(R, 'tmidupb', {'K': '0', 'J': '6', 'I': '5', 'F': 'U', 'N': 'B', 'X': EOR, 'P': P, 'E': E},
           {}, [('6', E6, B.g(E6, ewg_(w, ph, 'U', un, DK(6), g('6'))))])
    # 3. subCx 5 6 7
    P, E = cp(2)
    NWU = '( %s - U )' % NW
    ule = c['U <_ %s' % NW]
    nwun = s([un, nwn, ule, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, NWU))
    E5b = EWg(NWU, DK(5))
    B.call(R, 'tmiscxb', {'F': NW, 'G': 'U', 'N': 'B', 'X': DK(5), 'Y': DK(6), 'P': P, 'E': E},
           {'%s e. NN0' % NW: nwn, '%s < %s' % (NW, p2): c['%s < %s' % (NW, p2)], 'U <_ %s' % NW: ule},
           [('5', E5b, B.g(E5b, ewg_(w, ph, NWU, nwun, DK(5), g('5')))), ('6', DK(6), g('6'))])
    # 4. dropN 4 5 6
    P, E = cp(3)
    QS = QS_
    assert QS == '( W substr <. %s , %s >. )' % (NWU, NW)
    qsw = s([ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, QS))
    E4 = ENCL(QS, 'Y')
    nwult = linarith(w, ph, [c['%s < %s' % (NW, p2)], cl.ge0('U')], '%s < %s' % (NWU, p2), closure=cl)
    nwule = linarith(w, ph, [cl.ge0('U')], '%s <_ %s' % (NWU, NW), closure=cl)
    B.call(R, 'tmidnb', {'W': 'W', 'N': NWU, 'B': 'B', 'X': 'Y', 'Y': DK(5), 'P': P, 'E': E},
           {'%s e. NN0' % NWU: nwun, '%s < %s' % (NWU, p2): nwult, '%s <_ %s' % (NWU, NW): nwule},
           [('4', E4, B.g(E4, enclg(w, ph, QS, qsw, 'Y', yw))), ('5', DK(5), g('5'))])
    # 5. dropNum 2
    P, E = cp(4)
    Son, old = expose(w, ph, B, R, '2')
    B.call(R, 'tmidropb', {'K': '2', 'F': NW, 'N': 'B', 'X': 'R"', 'P': P, 'E': E},
           {'%s e. NN0' % NW: nwn, '%s < %s' % (NW, p2): c['%s < %s' % (NW, p2)]}, [('2', 'R"', r2w)], on=(Son, old))
    # 6. prodLF 4 3 5 6 7
    P, E = cp(5)
    nwuz = s([s([nwun, nwn, nwule], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, NWU, NW, NWU, NW)),
              w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NWU, NW))
    nwz = s([nwn, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NW, NW))
    rn3 = s([ww, nwuz, nwz, w.inst('swrdrn3')], 'syl3anc', '( %s -> ran %s = ( W " ( %s ..^ %s ) ) )' % (ph, QS, NWU, NW))
    rss = s([rn3, s([s([], 'imassrn', '( W " ( %s ..^ %s ) ) C_ ran W' % (NWU, NW))], 'a1i',
                    '( %s -> ( W " ( %s ..^ %s ) ) C_ ran W )' % (ph, NWU, NW))], 'eqsstrd', '( %s -> ran %s C_ ran W )' % (ph, QS))
    qral = s([rss, c[RALB('W')], w.inst('ssralv')], 'sylc', '( %s -> A. a e. ran %s a < %s )' % (ph, QS, p2))
    LS = LS_
    lsn = s([s([qsw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ph, QS)), w.inst('xp1st')], 'syl',
            '( %s -> %s e. NN0 )' % (ph, LS))
    E3 = EWg(LS, DK(3))
    B.call(R, 'tmiprlb', {'K': '4', 'J': '3', 'I': '5', "I'": '6', 'I"': '7', 'L': QS, 'R': 'Y', 'P': P, 'E': E},
           {'%s e. Word NN0' % QS: qsw, 'A. a e. ran %s a < %s' % (QS, p2): qral},
           [('3', E3, B.g(E3, ewg_(w, ph, LS, lsn, DK(3), g('3'))))])
    # 7. pow5F: L < 2 ^ ( U B + 1 )
    P, E = cp(6)
    LQ = '( # ` %s )' % QS
    lq = s([ww, nwuz, w.inst('swrdrlen')], 'syl2anc', '( %s -> %s = ( %s - %s ) )' % (ph, LQ, NW, NWU))
    lqu = s([lq, s([cl.mem(NW, 'CC'), cl.mem('U', 'CC')], 'nncand', '( %s -> ( %s - %s ) = U )' % (ph, NW, NWU))], 'eqtrd',
            '( %s -> %s = U )' % (ph, LQ))
    UB = '( U x. B )'
    N1 = '( %s + 1 )' % UB
    ubn = s([un, bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, UB))
    n1n = s([ubn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, N1))
    tpl = s([qsw, bn, qral, w.inst('tplprodle')], 'syl3anc', '( %s -> %s <_ ( 2 ^ ( %s x. B ) ) )' % (ph, LS, LQ))
    tpl2 = s([tpl, s([s([lqu], 'oveq1d', '( %s -> ( %s x. B ) = %s )' % (ph, LQ, UB))], 'oveq2d',
                     '( %s -> ( 2 ^ ( %s x. B ) ) = ( 2 ^ %s ) )' % (ph, LQ, UB))], 'breqtrd', '( %s -> %s <_ ( 2 ^ %s ) )' % (ph, LS, UB))
    P0, P1_ = '( 2 ^ %s )' % UB, '( 2 ^ %s )' % N1
    ep = s([closed(w, ph, '2cn', '2 e. CC'), ubn, w.inst('expp1')], 'syl2anc', '( %s -> %s = ( %s x. 2 ) )' % (ph, P1_, P0))
    p0p = s([closed(w, ph, '2rp', '2 e. RR+'), s([ubn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, UB)), w.inst('rpexpcl')], 'syl2anc',
            '( %s -> %s e. RR+ )' % (ph, P0))
    cl.atom(P0); cl.atom(P1_)
    cl.leaf(LS, 'NN0', lsn)
    llt = linarith(w, ph, [tpl2, ep, s([p0p], 'rpgt0d', '( %s -> 0 < %s )' % (ph, P0))], '%s < %s' % (LS, P1_), closure=cl)
    X5 = X5S_
    x5n = s([lsn, closed(w, ph, '5nn0', '5 e. NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, X5))
    E6b = EWg(X5, DK(6))
    B.call(R, 'tmip5b', {'L': LS, 'N': N1, 'X': DK(3), 'P': P, 'E': E},
           {'%s e. NN0' % LS: lsn, '%s e. NN0' % N1: n1n, '%s < %s' % (LS, P1_): llt},
           [('6', E6b, B.g(E6b, ewg_(w, ph, X5, x5n, DK(6), g('6'))))])
    # 8. dropNum 0
    P, E = cp(7)
    Son, old = expose(w, ph, B, R, '0')
    B.call(R, 'tmidropb', {'K': '0', 'F': 'U', 'N': 'B', 'X': EOR, 'P': P, 'E': E},
           {'U < %s' % p2: c['U < %s' % p2]}, [('0', EOR, gor)], on=(Son, old))
    # 9. moveEntry 1 5 7
    P, E = cp(8)
    WZ = '( encNatGam ` Z )'
    EZ5 = EWg('Z', DK(5))
    B.call(R, 'tmime', {'K': '1', 'J': '5', 'I': '7', 'W': WZ, 'X': "R'", 'P': P, 'E': E},
           {WRD(WZ, BITS): engb(w, ph, 'Z', zn)}, [('1', "R'", r1w), ('5', EZ5, B.g(EZ5, ewg_(w, ph, 'Z', zn, DK(5), g('5'))))])
    # 10. dup 6 1 7: L ^ 5 < 2 ^ ( ( U B + 1 ) x. 5 )
    P, E = cp(9)
    N5 = '( %s x. 5 )' % N1
    n5n = s([n1n, closed(w, ph, '5nn0', '5 e. NN0'), w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, N5))
    p1n = s([closed(w, ph, '2nn0', '2 e. NN0'), n1n, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, P1_))
    em = s([s([s([s([lsn], 'nn0red', '( %s -> %s e. RR )' % (ph, LS)), s([p1n], 'nn0red', '( %s -> %s e. RR )' % (ph, P1_))], 'jca',
                 '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (ph, LS, P1_)),
               s([s([lsn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, LS)), llt], 'jca', '( %s -> ( 0 <_ %s /\\ %s < %s ) )' % (ph, LS, LS, P1_)),
               closed(w, ph, '5nn', '5 e. NN')], '3jca',
              '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( 0 <_ %s /\\ %s < %s ) /\\ 5 e. NN ) )' % (ph, LS, P1_, LS, LS, P1_)),
            w.inst('expmordi')], 'syl', '( %s -> %s < ( %s ^ 5 ) )' % (ph, X5, P1_))
    emu = s([closed(w, ph, '2cn', '2 e. CC'), n1n, closed(w, ph, '5nn0', '5 e. NN0'), w.inst('expmul')], 'syl3anc',
            '( %s -> ( 2 ^ %s ) = ( %s ^ 5 ) )' % (ph, N5, P1_))
    x5lt = s([em, emu], 'breqtrrd', '( %s -> %s < ( 2 ^ %s ) )' % (ph, X5, N5))
    E1b = EWg(X5, "R'")
    B.call(R, 'tmidupb', {'K': '6', 'J': '1', 'I': '7', 'F': X5, 'N': N5, 'X': DK(6), 'P': P, 'E': E},
           {'%s e. NN0' % X5: x5n, '%s e. NN0' % N5: n5n, '%s < ( 2 ^ %s )' % (X5, N5): x5lt},
           [('1', E1b, B.g(E1b, ewg_(w, ph, X5, x5n, "R'", r1w)))])
    # 11. moveEntry 5 1 7
    P, E = cp(10)
    E1c = EWg('Z', E1b)
    B.call(R, 'tmime', {'K': '5', 'J': '1', 'I': '7', 'W': WZ, 'X': DK(5), 'P': P, 'E': E},
           {WRD(WZ, BITS): engb(w, ph, 'Z', zn)}, [('5', DK(5), g('5')), ('1', E1c, B.g(E1c, ewg_(w, ph, 'Z', zn, E1b, B.gam[E1b])))])
    # 12. moveEntry 6 0 5
    P, E = cp(11)
    WX = '( encNatGam ` %s )' % X5
    E0 = EWg(X5, EOR)
    B.call(R, 'tmime', {'K': '6', 'J': '0', 'I': '5', 'W': WX, 'X': DK(6), 'P': P, 'E': E},
           {WRD(WX, BITS): engb(w, ph, X5, x5n)}, [('6', DK(6), g('6')), ('0', E0, B.g(E0, ewg_(w, ph, X5, x5n, EOR, gor)))])
    # 13. pushNum 2 1
    K2 = '( <" 4 "> ++ R" )'
    g2 = B.g(K2, wg4(w, ph, 'R"', r2w))
    B.call(R, 'tm2fpshn', {'A': LM['Z1'], 'E': LM['Z2'], 'K': '2', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('2'): s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k']['2']['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX('2')))},
           [('2', K2, g2)])
    bg1 = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT1_))
    K21 = '( <" %s "> ++ %s )' % (BIT1_, K2)
    g21 = B.g(K21, wgcat(w, ph, '<" %s ">' % BIT1_, K2, s([bg1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT1_)), g2))
    B.call(R, 'tm2fpshn', {'A': LM['Z2'], 'E': LM['Z3'], 'K': '2', 'Z': BIT1_, 'N': S},
           {'%s e. %s' % (BIT1_, GX('2')): s([bg1, mk['k']['2']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, BIT1_, GX('2')))}, [('2', K21, g21)])
    # 14. load' ( flag := true )
    kw = lambda t: dict(fl='1o')
    ex = {LTY(L_T1): lset_ty(w, ph, mk, L_T1, kw)}
    pr = '( %s /\\ r e. %s )' % (ph, S)
    rs = s([s([], 'simpr', '( %s -> r e. %s )' % (pr, S)), lift_from(w, ph, pr, mk['seq'])], 'eleqtrd', '( %s -> r e. TMSt )' % pr)
    nv = lset_val(w, pr, kw, 'r', rs)
    NR = '( %s ` r )' % L_T1
    inm = A8.nfl_pack(w, pr, '1o', NR, nv['mem'], nv['fields']['fl'])
    ex['A. r e. %s ( %s ` r ) e. %s' % (S, L_T1, NFL('1o'))] = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, S, L_T1, NFL('1o')))
    ex['%s C_ %s' % (S, S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    ex['%s C_ %s' % (NFL('1o'), S)] = B.ss(NFL('1o'))
    B.call(R, 'tm2flg', {'A': LM['Z3'], 'E': 'E', 'F': L_T1, 'N': S, "N'": NFL('1o')}, ex, [])
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    print('FINAL CHAIN', of, file=sys.stderr)
    print('COST', n, file=sys.stderr)
    # stack 2: ( <" B1 "> ++ ( <" 4 "> ++ R" ) ) = EW( 1 , R" )
    e1 = s([s([r2w, w.inst('tmienc1')], 'syl', '( %s -> %s = %s )' % (ph, EWg('1', 'R"'), K21))], 'eqcomd',
           '( %s -> %s = %s )' % (ph, K21, EWg('1', 'R"')))
    Dc = triple_D(D)
    rf, xf = w.rewrite(Dc, {K21: (EWg('1', 'R"'), e1)}, ph)
    want = CONCL_S2S.split(' ( T TM2Hoare M ) <. ', 1)[1].rsplit(' , ', 1)[0]
    wantD = triple_D(want)
    assert xf == wantD, '\n%s\n%s' % (xf, wantD)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', NFL('1o'), rf, Dc, xf))
    # the bound
    TB = '( TMB ` B )'
    M_ = '( ( ( 5 x. ( U + 1 ) ) x. B ) + ; 1 4 )'
    TM = '( TMB ` %s )' % M_
    ub0 = s([cl.mem('U', 'RR'), cl.mem('B', 'RR'), cl.ge0('U'), cl.ge0('B')], 'mulge0d',
            '( %s -> 0 <_ %s )' % (ph, UB))
    u5 = s([closed(w, ph, '5nn0', '5 e. NN0'), s([un, w.inst('peano2nn0')], 'syl', '( %s -> ( U + 1 ) e. NN0 )' % ph), w.inst('nn0mulcl')],
           'syl2anc', '( %s -> ( 5 x. ( U + 1 ) ) e. NN0 )' % ph)
    u5b = s([u5, bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( ( 5 x. ( U + 1 ) ) x. B ) e. NN0 )' % ph)
    mnn = s([u5b, s([num.nn0(w, 14)], 'a1i', '( %s -> ; 1 4 e. NN0 )' % ph), w.inst('nn0addcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, M_))

    def mono(x, xn, le_hyps):
        le_ = linarith(w, ph, [ub0, cl.ge0('B'), cl.ge0('U')] + le_hyps, '%s <_ %s' % (x, M_), closure=cl, products=True)
        return s([xn, mnn, le_, w.inst('tmbmono')], 'syl3anc', '( %s -> ( TMB ` %s ) <_ %s )' % (ph, x, TM))
    tbn = tmbn(w, ph, 'B', bn)
    tmn = tmbn(w, ph, M_, mnn)
    cl.leaf(TB, 'NN0', tbn)
    cl.leaf(TM, 'NN0', tmn)
    B34 = '( ( 3 x. B ) + 4 )'
    b34n = s([s([closed(w, ph, '3nn0', '3 e. NN0'), bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 3 x. B ) e. NN0 )' % ph),
              closed(w, ph, '4nn0', '4 e. NN0'), w.inst('nn0addcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, B34))
    T34 = '( TMB ` %s )' % B34
    cl.leaf(T34, 'NN0', tmbn(w, ph, B34, b34n))
    tb3 = s([bn, w.inst('tplb34')], 'syl', '( %s -> %s = ( ; 2 7 x. %s ) )' % (ph, T34, TB))
    m34 = mono(B34, b34n, [])
    t1b = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, TB))
    tb27 = linarith(w, ph, [tb3, m34], '( ; 2 7 x. %s ) <_ %s' % (TB, TM), closure=cl)
    # prodLF: ( ( 2nd ` ( ProdL ` QS ) ) + 1 ) x. TMB ( ( 2 ( # QS + 1 ) ) B + 4 )
    P2L = '( 2nd ` ( ProdL ` %s ) )' % QS
    pc2 = s([s([qsw, w.inst('prodlcost')], 'syl', '( %s -> %s = %s )' % (ph, P2L, LQ)), lqu], 'eqtrd', '( %s -> %s = U )' % (ph, P2L))
    AP = '( ( ( 2 x. ( %s + 1 ) ) x. B ) + 4 )' % LQ
    cl.leaf(LQ, 'NN0', s([qsw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LQ)))
    apn = s([s([s([closed(w, ph, '2nn0', '2 e. NN0'), s([cl.mem(LQ, 'NN0'), w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, LQ)),
                   w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 2 x. ( %s + 1 ) ) e. NN0 )' % (ph, LQ)), bn, w.inst('nn0mulcl')], 'syl2anc',
               '( %s -> ( ( 2 x. ( %s + 1 ) ) x. B ) e. NN0 )' % (ph, LQ)), closed(w, ph, '4nn0', '4 e. NN0'), w.inst('nn0addcl')],
            'syl2anc', '( %s -> %s e. NN0 )' % (ph, AP))
    LQB = '( %s x. B )' % LQ
    lqb = s([lqu], 'oveq1d', '( %s -> %s = %s )' % (ph, LQB, UB))
    APE = lineq(w, ph, AP, '( ( ( 2 x. %s ) + ( 2 x. B ) ) + 4 )' % LQB, closure=cl, products=True)
    TAP = '( TMB ` %s )' % AP
    cl.leaf(TAP, 'NN0', tmbn(w, ph, AP, apn))
    mAP = mono(AP, apn, [APE, lqb])
    cl.leaf(P2L, 'NN0', s([s([qsw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ph, QS)), w.inst('xp2nd')], 'syl',
                          '( %s -> %s e. NN0 )' % (ph, P2L)))
    hp1 = s([pc2], 'oveq1d', '( %s -> ( %s x. %s ) = ( U x. %s ) )' % (ph, P2L, TAP, TAP))
    hp2 = s([cl.mem(TAP, 'RR'), cl.mem(TM, 'RR'), cl.mem('U', 'RR'), cl.ge0('U'), mAP], 'lemul2ad',
            '( %s -> ( U x. %s ) <_ ( U x. %s ) )' % (ph, TAP, TM))
    # dropN: ( ( NWU' ... ) ) the cost ( ( # W + 1 ) x. ( 4 x. TB ) )
    fourtb = linarith(w, ph, [tb27, cl.ge0(TB)], '( 4 x. %s ) <_ %s' % (TB, TM), closure=cl)
    hd1 = s([cl.mem('( 4 x. %s )' % TB, 'RR'), cl.mem(TM, 'RR'), cl.mem('( %s + 1 )' % NW, 'RR'), cl.ge0('( %s + 1 )' % NW), fourtb], 'lemul2ad',
            '( %s -> ( ( %s + 1 ) x. ( 4 x. %s ) ) <_ ( ( %s + 1 ) x. %s ) )' % (ph, NW, TB, NW, TM))
    # pow5F: 9 TMB ( 4 N1 ) ; dup: TMB N5 ; moveEntry of L ^ 5
    A4 = '( 4 x. %s )' % N1
    a4n = s([closed(w, ph, '4nn0', '4 e. NN0'), n1n, w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, A4))
    cl.leaf('( TMB ` %s )' % A4, 'NN0', tmbn(w, ph, A4, a4n))
    m4 = mono(A4, a4n, [])
    cl.leaf('( TMB ` %s )' % N5, 'NN0', tmbn(w, ph, N5, n5n))
    m5 = mono(N5, n5n, [])
    mzb = me_bound(w, ph, 'Z', zn, c['Z < %s' % p2], bn, cl)
    mx5 = me_bound_n(w, ph, X5, x5n, x5lt, N5, n5n, cl)
    hyps = [tb27, t1b, hp1, hp2, hd1, m4, m5, mzb, mx5, ub0, mAP]
    if os.environ.get('DBG'):
        import lin as _l
        for k in range(len(hyps)):
            try:
                linarith(w, ph, hyps[:k] + hyps[k+1:], '%s <_ %s' % (n, '( ( ( %s + U ) + ; 2 1 ) x. %s )' % (NW, TM)), closure=cl, products=True)
                print('OK without', k, file=sys.stderr)
            except Exception as e_:
                print('FAIL without', k, file=sys.stderr)
    le = linarith(w, ph, hyps, '%s <_ %s' % (n, '( ( ( %s + U ) + ; 2 1 ) x. %s )' % (NW, TM)),
                  closure=cl, products=True)
    BND = '( ( ( %s + U ) + ; 2 1 ) x. %s )' % (NW, TM)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
