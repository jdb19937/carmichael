"""Sortie A4c, batch 7: soundness of the DP table across one step
(Lean: AlgExtract.tblSound_dpStep)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4clib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

DS = '( ( L DpStep P ) ` T )'
DS1 = '( 1st ` %s )' % DS
T3 = '( L e. NN /\\ P e. NN0 /\\ T e. Tbl )'
CSE = '( <" P "> ++ E )'
TEG = '( 2nd ` ( %s ` g ) )' % DS1
def RBS(v, g):
    return '( ( ( T ` %s ) =/= %s /\\ %s = ( ( %s x. P ) mod L ) ) /\\ %s = ( <" P "> ++ ( 2nd ` ( T ` %s ) ) ) )' % (v, NONE, g, v, '( 2nd ` ( %s ` %s ) )' % (DS1, g), v)
def SB(x):
    return "( ( %s =/= (/) /\\ Fun `' %s ) /\\ ( ran %s C_ ran %s /\\ ( %s mod L ) = g ) )" % (x, x, x, CSE, PRD(x))

def paystep(w, A, ttst, cst, nnst, x):
    p = w.s([w.s([w.s([ttst, cst], 'jca', '( %s -> ( T e. Tbl /\\ %s e. NN0 ) )' % (A, x)), nnst], 'jca',
                 '( %s -> ( ( T e. Tbl /\\ %s e. NN0 ) /\\ ( T ` %s ) =/= %s ) )' % (A, x, x, NONE)), w.inst('tblpay')], 'syl',
             '( %s -> ( ( 2nd ` ( T ` %s ) ) e. Word NN0 /\\ ( T ` %s ) = ( inl ` ( 2nd ` ( T ` %s ) ) ) ) )' % (A, x, x, x))
    return w.s([p], 'simpld', '( %s -> ( 2nd ` ( T ` %s ) ) e. Word NN0 )' % (A, x))

if not only or 'tblsnds' in only:
    w = W('tblsnds', 'A DP step preserves soundness of the table (Lean: tblSound_dpStep).')
    TSE = TS('L', 'T', 'E')
    A = '( %s /\\ ( E e. Word NN0 /\\ -. P e. ran E ) /\\ %s )' % (T3, TSE)
    ll = w.s([w.s([], 'simp1', '( %s -> %s )' % (A, T3))], 'simp1d', '( %s -> L e. NN )' % A)
    pp = w.s([w.s([], 'simp1', '( %s -> %s )' % (A, T3))], 'simp2d', '( %s -> P e. NN0 )' % A)
    tt = w.s([w.s([], 'simp1', '( %s -> %s )' % (A, T3))], 'simp3d', '( %s -> T e. Tbl )' % A)
    dpo = w.s([w.s([ll, pp], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % A), tt], 'jca', '( %s -> %s )' % (A, DPO))
    ee = w.s([w.s([], 'simp2', '( %s -> ( E e. Word NN0 /\\ -. P e. ran E ) )' % A)], 'simpld', '( %s -> E e. Word NN0 )' % A)
    pne = w.s([w.s([], 'simp2', '( %s -> ( E e. Word NN0 /\\ -. P e. ran E ) )' % A)], 'simprd',
              '( %s -> -. P e. ran E )' % A)
    ts = w.s([], 'simp3', '( %s -> %s )' % (A, TSE))
    rncs = w.s([pp, ee, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran E ) )' % (A, CSE))
    B = '( %s /\\ g e. NN0 )' % A
    U = '( %s /\\ ( %s ` g ) =/= %s )' % (B, DS1, NONE)
    up = lambda st, f: w.s([w.s([st], 'adantr', '( %s -> %s )' % (B, f))], 'adantr', '( %s -> %s )' % (U, f))
    gg = w.s([w.s([], 'simpr', '( %s -> g e. NN0 )' % B)], 'adantr', '( %s -> g e. NN0 )' % U)
    hyp = w.s([], 'simpr', '( %s -> ( %s ` g ) =/= %s )' % (U, DS1, NONE))
    dpoU = up(dpo, DPO); ppU = up(pp, 'P e. NN0'); ttU = up(tt, 'T e. Tbl'); llU = up(ll, 'L e. NN')
    eeU = up(ee, 'E e. Word NN0'); pneU = up(pne, '-. P e. ran E'); tsU = up(ts, TSE)
    rncsU = up(rncs, 'ran %s = ( { P } u. ran E ) )' % CSE)
    w.lines[-2] = w.lines[-2].split('|-')[0] + '|- ( %s -> ran %s = ( { P } u. ran E ) )' % (B, CSE)
    w.lines[-1] = w.lines[-1].split('|-')[0] + '|- ( %s -> ran %s = ( { P } u. ran E ) )' % (U, CSE)
    ssE = w.s([w.s([w.s([], 'ssun2', 'ran E C_ ( { P } u. ran E )')], 'a1i', '( %s -> ran E C_ ( { P } u. ran E ) )' % U),
               w.s([rncsU], 'eqcomd', '( %s -> ( { P } u. ran E ) = ran %s )' % (U, CSE))], 'sseqtrd',
              '( %s -> ran E C_ ran %s )' % (U, CSE))
    ssP = w.s([w.s([w.s([], 'ssun1', '{ P } C_ ( { P } u. ran E )')], 'a1i', '( %s -> { P } C_ ( { P } u. ran E ) )' % U),
               w.s([rncsU], 'eqcomd', '( %s -> ( { P } u. ran E ) = ran %s )' % (U, CSE))], 'sseqtrd',
              '( %s -> { P } C_ ran %s )' % (U, CSE))
    GOAL = SB(TEG)
    NEW = '( g = ( P mod L ) /\\ %s = <" P "> )' % TEG
    CONC = '( ( T ` g ) = ( %s ` g ) \\/ ( %s \\/ E. r e. ( 0 ..^ L ) %s ) )' % (DS1, NEW, RBS('r', 'g'))
    cas = w.s([w.s([dpoU, w.s([gg, hyp], 'jca', '( %s -> ( g e. NN0 /\\ ( %s ` g ) =/= %s ) )' % (U, DS1, NONE))], 'jca',
                   '( %s -> ( %s /\\ ( g e. NN0 /\\ ( %s ` g ) =/= %s ) ) )' % (U, DPO, DS1, NONE)),
               w.inst('dpstepcases')], 'syl', '( %s -> %s )' % (U, CONC))
    # =============================================== case 1: the old entry
    L1 = '( %s /\\ ( T ` g ) = ( %s ` g ) )' % (U, DS1)
    l1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (L1, f))
    eq = w.s([], 'simpr', '( %s -> ( T ` g ) = ( %s ` g ) )' % (L1, DS1))
    tgnn = w.s([eq, l1(hyp, '( %s ` g ) =/= %s' % (DS1, NONE))], 'eqnetrd', '( %s -> ( T ` g ) =/= %s )' % (L1, NONE))
    WG = '( 2nd ` ( T ` g ) )'
    ihb, _ = inst1(w, L1, l1(tsU, TSE), 'd', 'NN0',
                   "( ( T ` d ) =/= %s -> ( ( ( 2nd ` ( T ` d ) ) =/= (/) /\\ Fun `' ( 2nd ` ( T ` d ) ) ) /\\ ( ran ( 2nd ` ( T ` d ) ) C_ ran E /\\ ( %s mod L ) = d ) ) )"
                   % (NONE, PRD('( 2nd ` ( T ` d ) )')), 'g', l1(gg, 'g e. NN0'))
    got = w.s([ihb, tgnn], 'mpd',
              "( %s -> ( ( %s =/= (/) /\\ Fun `' %s ) /\\ ( ran %s C_ ran E /\\ ( %s mod L ) = g ) ) )" % (L1, WG, WG, WG, PRD(WG)))
    #   upgrade ran W C_ ran E to ran W C_ ran CSE, then transport across the equation
    sub = w.s([w.s([w.s([got], 'simprd', '( %s -> ( ran %s C_ ran E /\\ ( %s mod L ) = g ) )' % (L1, WG, PRD(WG)))], 'simpld',
                   '( %s -> ran %s C_ ran E )' % (L1, WG)), l1(ssE, 'ran E C_ ran %s' % CSE)], 'sstrd',
              '( %s -> ran %s C_ ran %s )' % (L1, WG, CSE))
    sb1 = w.s([w.s([got], 'simpld', "( %s -> ( %s =/= (/) /\\ Fun `' %s ) )" % (L1, WG, WG)),
               w.s([sub, w.s([w.s([got], 'simprd', '( %s -> ( ran %s C_ ran E /\\ ( %s mod L ) = g ) )' % (L1, WG, PRD(WG)))], 'simprd',
                             '( %s -> ( %s mod L ) = g )' % (L1, PRD(WG)))], 'jca',
                   '( %s -> ( ran %s C_ ran %s /\\ ( %s mod L ) = g ) )' % (L1, WG, CSE, PRD(WG)))], 'jca',
              '( %s -> %s )' % (L1, SB(WG)))
    teq = w.s([w.s([eq], 'fveq2d', '( %s -> %s = %s )' % (L1, WG, TEG))], 'eqcomd', '( %s -> %s = %s )' % (L1, TEG, WG))
    tr, ne = rwbi2(w, L1, SB(TEG), TEG, WG, teq)
    assert ne == SB(WG), '\n%s\n%s' % (ne, SB(WG))
    c1 = w.s([sb1, tr], 'mpbird', '( %s -> %s )' % (L1, GOAL))
    # =============================================== case 2: the new prime
    L2 = '( %s /\\ %s )' % (U, NEW)
    l2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (L2, f))
    e2 = w.s([w.s([], 'simpr', '( %s -> %s )' % (L2, NEW))], 'simprd', '( %s -> %s = <" P "> )' % (L2, TEG))
    g2 = w.s([w.s([], 'simpr', '( %s -> %s )' % (L2, NEW))], 'simpld', '( %s -> g = ( P mod L ) )' % L2)
    s1nzs = w.s([w.s([], 's1nz', '<" P "> =/= (/)')], 'a1i', '( %s -> <" P "> =/= (/) )' % L2)
    fun2 = w.s([l2(ppU, 'P e. NN0'), w.inst('algndps1')], 'syl', "( %s -> Fun `' <\" P \"> )" % L2)
    rn2 = w.s([l2(ppU, 'P e. NN0'), w.inst('s1rn')], 'syl', '( %s -> ran <" P "> = { P } )' % L2)
    ss2 = w.s([rn2, l2(ssP, '{ P } C_ ran %s' % CSE)], 'eqsstrd', '( %s -> ran <" P "> C_ ran %s )' % (L2, CSE))
    pr2 = w.s([l2(ppU, 'P e. NN0'), w.inst('algprods1')], 'syl', '( %s -> %s = P )' % (L2, PRD('<" P ">')))
    mod2 = w.s([w.s([pr2], 'oveq1d', '( %s -> ( %s mod L ) = ( P mod L ) )' % (L2, PRD('<" P ">'))),
                w.s([g2], 'eqcomd', '( %s -> ( P mod L ) = g )' % L2)], 'eqtrd',
               '( %s -> ( %s mod L ) = g )' % (L2, PRD('<" P ">')))
    sb2 = w.s([w.s([s1nzs, fun2], 'jca', "( %s -> ( <\" P \"> =/= (/) /\\ Fun `' <\" P \"> ) )" % L2),
               w.s([ss2, mod2], 'jca', '( %s -> ( ran <" P "> C_ ran %s /\\ ( %s mod L ) = g ) )' % (L2, CSE, PRD('<" P ">')))],
              'jca', '( %s -> %s )' % (L2, SB('<" P ">')))
    tr2, ne2 = rwbi2(w, L2, SB(TEG), TEG, '<" P ">', e2)
    assert ne2 == SB('<" P ">'), '\n%s\n%s' % (ne2, SB('<" P ">'))
    c2 = w.s([sb2, tr2], 'mpbird', '( %s -> %s )' % (L2, GOAL))
    # =============================================== case 3: an extension
    V = '( %s /\\ r e. ( 0 ..^ L ) )' % U
    l3 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (V, f))
    L3 = '( %s /\\ %s )' % (V, RBS('r', 'g'))
    l4 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (L3, f))
    lv = lambda st, f: l4(l3(st, f), f)
    rn = w.s([w.s([], 'simpr', '( %s -> r e. ( 0 ..^ L ) )' % V), w.inst('elfzonn0')], 'syl', '( %s -> r e. NN0 )' % V)
    rb = w.s([], 'simpr', '( %s -> %s )' % (L3, RBS('r', 'g')))
    trnn = w.s([w.s([rb], 'simpld', '( %s -> ( ( T ` r ) =/= %s /\\ g = ( ( r x. P ) mod L ) ) )' % (L3, NONE))], 'simpld',
               '( %s -> ( T ` r ) =/= %s )' % (L3, NONE))
    geq = w.s([w.s([rb], 'simpld', '( %s -> ( ( T ` r ) =/= %s /\\ g = ( ( r x. P ) mod L ) ) )' % (L3, NONE))], 'simprd',
              '( %s -> g = ( ( r x. P ) mod L ) )' % L3)
    hcat = w.s([rb], 'simprd', '( %s -> %s = ( <" P "> ++ ( 2nd ` ( T ` r ) ) ) )' % (L3, TEG))
    WR = '( 2nd ` ( T ` r ) )'
    CSW = '( <" P "> ++ %s )' % WR
    wtr = paystep(w, L3, lv(ttU, 'T e. Tbl'), l4(rn, 'r e. NN0'), trnn, 'r')
    ihr, _ = inst1(w, L3, lv(tsU, TSE), 'd', 'NN0',
                   "( ( T ` d ) =/= %s -> ( ( ( 2nd ` ( T ` d ) ) =/= (/) /\\ Fun `' ( 2nd ` ( T ` d ) ) ) /\\ ( ran ( 2nd ` ( T ` d ) ) C_ ran E /\\ ( %s mod L ) = d ) ) )"
                   % (NONE, PRD('( 2nd ` ( T ` d ) )')), 'r', l4(rn, 'r e. NN0'))
    gr = w.s([ihr, trnn], 'mpd',
             "( %s -> ( ( %s =/= (/) /\\ Fun `' %s ) /\\ ( ran %s C_ ran E /\\ ( %s mod L ) = r ) ) )" % (L3, WR, WR, WR, PRD(WR)))
    funr = w.s([w.s([gr], 'simpld', "( %s -> ( %s =/= (/) /\\ Fun `' %s ) )" % (L3, WR, WR))], 'simprd',
               "( %s -> Fun `' %s )" % (L3, WR))
    ssr = w.s([w.s([gr], 'simprd', '( %s -> ( ran %s C_ ran E /\\ ( %s mod L ) = r ) )' % (L3, WR, PRD(WR)))], 'simpld',
              '( %s -> ran %s C_ ran E )' % (L3, WR))
    modr = w.s([w.s([gr], 'simprd', '( %s -> ( ran %s C_ ran E /\\ ( %s mod L ) = r ) )' % (L3, WR, PRD(WR)))], 'simprd',
               '( %s -> ( %s mod L ) = r )' % (L3, PRD(WR)))
    #   nonempty
    nz3 = w.s([w.s([lv(ppU, 'P e. NN0'), wtr], 'jca', '( %s -> ( P e. NN0 /\\ %s e. Word NN0 ) )' % (L3, WR)),
               w.inst('algcsnz')], 'syl', '( %s -> %s =/= (/) )' % (L3, CSW))
    #   duplicate-freeness
    pnr = w.s([w.s([ssr, w.inst('ssneld')], 'syl', '( %s -> ( -. P e. ran E -> -. P e. ran %s ) )' % (L3, WR)),
               lv(pneU, '-. P e. ran E')], 'mpd', '( %s -> -. P e. ran %s )' % (L3, WR))
    fun3 = w.s([w.s([w.s([lv(ppU, 'P e. NN0'), wtr], 'jca', '( %s -> ( P e. NN0 /\\ %s e. Word NN0 ) )' % (L3, WR)),
                     w.inst('algndpcs')], 'syl',
                    "( %s -> ( Fun `' %s <-> ( -. P e. ran %s /\\ Fun `' %s ) ) )" % (L3, CSW, WR, WR)),
                w.s([pnr, funr], 'jca', "( %s -> ( -. P e. ran %s /\\ Fun `' %s ) )" % (L3, WR, WR))], 'mpbird',
               "( %s -> Fun `' %s )" % (L3, CSW))
    #   the range
    rn3 = w.s([lv(ppU, 'P e. NN0'), wtr, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran %s ) )' % (L3, CSW, WR))
    ss3 = w.s([rn3, w.s([w.s([w.s([w.s([], 'ssid', '{ P } C_ { P }')], 'a1i', '( %s -> { P } C_ { P } )' % L3), ssr], 'jca',
                             '( %s -> ( { P } C_ { P } /\\ ran %s C_ ran E ) )' % (L3, WR)), w.inst('unss12')], 'syl',
                        '( %s -> ( { P } u. ran %s ) C_ ( { P } u. ran E ) )' % (L3, WR))], 'eqsstrd',
              '( %s -> ran %s C_ ( { P } u. ran E ) )' % (L3, CSW))
    ss3b = w.s([ss3, w.s([lv(rncsU, 'ran %s = ( { P } u. ran E )' % CSE)], 'eqcomd',
                         '( %s -> ( { P } u. ran E ) = ran %s )' % (L3, CSE))], 'sseqtrd',
               '( %s -> ran %s C_ ran %s )' % (L3, CSW, CSE))
    #   the residue
    prcl = w.s([wtr, w.inst('algprodcl')], 'syl', '( %s -> %s e. NN0 )' % (L3, PRD(WR)))
    pcs = w.s([lv(ppU, 'P e. NN0'), wtr, w.inst('algprodcs')], 'syl2anc', '( %s -> %s = ( P x. %s ) )' % (L3, PRD(CSW), PRD(WR)))
    comm = w.s([w.s([lv(ppU, 'P e. NN0')], 'nn0cnd', '( %s -> P e. CC )' % L3),
                w.s([prcl], 'nn0cnd', '( %s -> %s e. CC )' % (L3, PRD(WR)))], 'mulcomd',
               '( %s -> ( P x. %s ) = ( %s x. P ) )' % (L3, PRD(WR), PRD(WR)))
    mmr = w.s([w.s([prcl, lv(ppU, 'P e. NN0'), lv(llU, 'L e. NN')], '3jca',
                   '( %s -> ( %s e. NN0 /\\ P e. NN0 /\\ L e. NN ) )' % (L3, PRD(WR))), w.inst('modmulr')], 'syl',
              '( %s -> ( ( ( %s mod L ) x. P ) mod L ) = ( ( %s x. P ) mod L ) )' % (L3, PRD(WR), PRD(WR)))
    rw = w.s([modr], 'oveq1d', '( %s -> ( ( %s mod L ) x. P ) = ( r x. P ) )' % (L3, PRD(WR)))
    rw2 = w.s([rw], 'oveq1d', '( %s -> ( ( ( %s mod L ) x. P ) mod L ) = ( ( r x. P ) mod L ) )' % (L3, PRD(WR)))
    mod3 = w.s([w.s([w.s([pcs, comm], 'eqtrd', '( %s -> %s = ( %s x. P ) )' % (L3, PRD(CSW), PRD(WR)))], 'oveq1d',
                    '( %s -> ( %s mod L ) = ( ( %s x. P ) mod L ) )' % (L3, PRD(CSW), PRD(WR))),
                w.s([w.s([mmr], 'eqcomd', '( %s -> ( ( %s x. P ) mod L ) = ( ( ( %s mod L ) x. P ) mod L ) )' % (L3, PRD(WR), PRD(WR))),
                     w.s([rw2, w.s([geq], 'eqcomd', '( %s -> ( ( r x. P ) mod L ) = g )' % L3)], 'eqtrd',
                         '( %s -> ( ( ( %s mod L ) x. P ) mod L ) = g )' % (L3, PRD(WR)))], 'eqtrd',
                    '( %s -> ( ( %s x. P ) mod L ) = g )' % (L3, PRD(WR)))], 'eqtrd',
               '( %s -> ( %s mod L ) = g )' % (L3, PRD(CSW)))
    sb3 = w.s([w.s([nz3, fun3], 'jca', "( %s -> ( %s =/= (/) /\\ Fun `' %s ) )" % (L3, CSW, CSW)),
               w.s([ss3b, mod3], 'jca', '( %s -> ( ran %s C_ ran %s /\\ ( %s mod L ) = g ) )' % (L3, CSW, CSE, PRD(CSW)))],
              'jca', '( %s -> %s )' % (L3, SB(CSW)))
    tr3, ne3 = rwbi2(w, L3, SB(TEG), TEG, CSW, hcat)
    assert ne3 == SB(CSW), '\n%s\n%s' % (ne3, SB(CSW))
    c3 = w.s([sb3, tr3], 'mpbird', '( %s -> %s )' % (L3, GOAL))
    rex = w.s([w.s([c3], 'ex', '( %s -> ( %s -> %s ) )' % (V, RBS('r', 'g'), GOAL))], 'rexlimdva',
              '( %s -> ( E. r e. ( 0 ..^ L ) %s -> %s ) )' % (U, RBS('r', 'g'), GOAL))
    inner = w.s([w.s([c2], 'ex', '( %s -> ( %s -> %s ) )' % (U, NEW, GOAL)), rex], 'jaod',
                '( %s -> ( ( %s \\/ E. r e. ( 0 ..^ L ) %s ) -> %s ) )' % (U, NEW, RBS('r', 'g'), GOAL))
    fin = w.s([cas, w.s([c1], 'ex', '( %s -> ( ( T ` g ) = ( %s ` g ) -> %s ) )' % (U, DS1, GOAL)), inner], 'mpjaod',
              '( %s -> %s )' % (U, GOAL))
    imp = w.s([fin], 'ex', '( %s -> ( ( %s ` g ) =/= %s -> %s ) )' % (B, DS1, NONE, GOAL))
    gen = w.s([imp], 'ralrimiva', '( %s -> %s )' % (A, TS('L', DS1, CSE, 'g')))
    body = TS('L', DS1, CSE, 'd')
    cv = ralconv(w, 'NN0', 'd', 'g', body[len('A. d e. NN0 '):])
    w.qed([gen, w.s([cv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, TS('L', DS1, CSE, 'g'), body))], 'mpbid',
          '( %s -> %s )' % (A, body))
    run(w)
