"""T10: keepF at the machine (Lean ` keepF_runs ` ).

  tmikpa   the prefix ` dup 1 6 7 ; dup 2 7 6 ; cmpFrag 6 7 ` : ` cmp := compare z99 q ` , the stacks restored
  tmikp    keepF_runs: the prefix (~ tmikpa ), then by cases on ` z99 < q ` and on ` isPrimeTD q ` :
           ~ tmiptb , ` dup 2 6 7 ; predNum 6 7 ` , ~ tmistdb ; or ` skip ` ; or ` load' ( flag := false ) `

    MM_DB=sorties/t10.mm python3 tools/gen/t10_j_kp.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7lib import mval, not1o
from t7_h_iz import lset_val, lset_ty
from cl import Closure
from t10_e_doa import ex_, lift_from
from t10_d_dot import skip_ty, skip_in, cls_to

SEL = sys.argv[1:]
LM = FRAGS['kp'].lmap()
CQ = CMPC('G', 'Q')
IP1 = '( 1st ` ( IsPrimeTD ` Q ) )'
SMT1 = '( 1st ` ( Y SmoothTD ( Q - 1 ) ) )'
CONCL_KPA = TRI(CS('kp'), CLN(LM['Z1'], CQ, 'D'), '( 3 x. ( TMB ` B ) )')
add_stmt('tmikpa', TREE_KP, CONCL_KPA)
add_stmt('tmikp', TREE_KP, CONCL_KP)


class Kp(Base):
    def __init__(self, w, ph, T):
        c0 = Ctx(w, ph, T)
        gn, ynn, qnn = c0['G e. NN0'], c0['Y e. NN'], c0['Q e. NN']
        yn = w.s([ynn], 'nnnn0d', '( %s -> Y e. NN0 )' % ph)
        qn = w.s([qnn], 'nnnn0d', '( %s -> Q e. NN0 )' % ph)
        xw, x2w, zw = c0[WG('X')], c0[WG("X'")], c0[WG('Z')]
        eqs = {'0': (EWg('Y', 'X'), ewg_(w, ph, 'Y', yn, 'X', xw)), '1': (EWg('G', "X'"), ewg_(w, ph, 'G', gn, "X'", x2w)),
               '2': (EWg('Q', 'Z'), ewg_(w, ph, 'Q', qn, 'Z', zw))}
        Base.__init__(self, w, ph, T, N8, 'kp', eqs)
        self.gn, self.ynn, self.yn, self.qnn, self.qn, self.bn = gn, ynn, yn, qnn, qn, self.c['B e. NN0']
        self.xw, self.x2w, self.zw = xw, x2w, zw
        s = w.s
        self.tbn = s([s([self.bn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` B ) e. NN0 )' % ph)


def tmikpa():
    lab = 'tmikpa'
    T = numtree(TREE_KP)
    ph = cj(T)
    w = W(lab, 'The prefix of Lean\'s ` keepF ` at the machine: ` dup 1 6 7 ; dup 2 7 6 ; cmpFrag 6 7 ` sets ` cmp ` to the '
               'comparison of ` z99 ` with ` q ` and restores every stack, within ` 3 B b ` steps.')
    s = w.s
    B = Kp(w, ph, T)
    R = B.run()
    g = lambda k: B.S0.vals[k][2]
    E6 = EWg('G', DK(6))
    B.call(R, 'tmidupb', {'K': '1', 'J': '6', 'I': '7', 'F': 'G', 'N': 'B', 'X': "X'", 'P': PL('P', 4), 'E': LM['Y2']}, {},
           [('6', E6, B.g(E6, ewg_(w, ph, 'G', B.gn, DK(6), g('6'))))])
    E7 = EWg('Q', DK(7))
    B.call(R, 'tmidupb', {'K': '2', 'J': '7', 'I': '6', 'F': 'Q', 'N': 'B', 'X': 'Z', 'P': PL('P', 5), 'E': LM['Y3']}, {'Q e. NN0': B.qn},
           [('7', E7, B.g(E7, ewg_(w, ph, 'Q', B.qn, DK(7), g('7'))))])
    B.call(R, 'tmicmpb', {'K': '6', 'J': '7', 'F': 'G', 'G': 'Q', 'N': 'B', 'X': DK(6), 'Y': DK(7), 'P': PL('P', 6), 'E': LM['Z1']},
           {'Q e. NN0': B.qn}, [('6', DK(6), g('6')), ('7', DK(7), g('7'))])
    cur, out = R.normalize(N8)
    assert out == [], out
    cl = Closure(w, ph, {'B': ('NN0', B.bn)})
    cl.leaf('( TMB ` B )', 'NN0', B.tbn)
    B3 = '( 3 x. ( TMB ` B ) )'
    le = linarith(w, ph, [], '%s <_ %s' % (R.n, B3), closure=cl)
    st = hrle(w, ph, B.mk['phm'], R.tri, R.C0, R.cur, R.n, B3, cl.mem(B3, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def clt_test(w, pc, gn, qn, truth, cnd):
    """( pc -> A. m e. CQ ( CLT ` m ) = 1o ) (truth: G < Q) or ( ... -. ... ) (-. G < Q)"""
    s = w.s
    XL = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    pm = '( %s /\\ m e. %s )' % (pc, CQ)
    mi = s([], 'simpr', '( %s -> m e. %s )' % (pm, CQ))
    cond = lambda t: '( TMcmp ` %s ) = ( G Ncmp Q )' % t
    idh = s([], 'id', '( h = m -> h = m )')
    cg, new = w.wcongr(cond('h'), {'h': 'm'}, 'h = m', {'h': idh})
    both = s([mi, s([cg], 'elrab', '( m e. %s <-> ( m e. TMSt /\\ %s ) )' % (CQ, cond('m')))], 'sylib', '( %s -> ( m e. TMSt /\\ %s ) )' % (pm, cond('m')))
    mm = s([both], 'simpld', '( %s -> m e. TMSt )' % pm)
    mc = s([both], 'simprd', '( %s -> %s )' % (pm, cond('m')))
    xex = ifex_closed(w, pm, '( TMcmp ` m ) = (/)', '1o', '(/)', s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', XL, 'm', mm, xex)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pc, st)))
    nl = s([s([gn, qn], 'jca', '( %s -> ( G e. NN0 /\\ Q e. NN0 ) )' % pc), w.inst('ncmplt')], 'syl', '( %s -> ( ( G Ncmp Q ) = (/) <-> G < Q ) )' % pc)
    if truth:
        nc0 = s([cnd, nl], 'mpbird', '( %s -> ( G Ncmp Q ) = (/) )' % pc)
        cm0 = s([mc, Lm(nc0)], 'eqtrd', '( %s -> ( TMcmp ` m ) = (/) )' % pm)
        v = s([cv, s([cm0], 'iftrued', '( %s -> %s = 1o )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CLT))
        return s([v], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pc, CQ, CLT))
    nn0 = s([cnd, nl], 'mtbird', '( %s -> -. ( G Ncmp Q ) = (/) )' % pc)
    cm1 = s([Lm(nn0), s([mc], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = (/) <-> ( G Ncmp Q ) = (/) ) )' % pm)], 'mtbird',
            '( %s -> -. ( TMcmp ` m ) = (/) )' % pm)
    c0 = s([cv, s([cm1], 'iffalsed', '( %s -> %s = (/) )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CLT))
    return s([not1o(w, pm, c0, CLT, 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pc, CQ, CLT))


def tmikp():
    lab = 'tmikp'
    T0 = numtree(TREE_KP)
    ph = cj(T0)
    w = W(lab, 'Lean\'s ` keepF_runs ` at the machine: the flag ends up ` resKeep z99 y q ` (A1b\'s nested ` if ` of ` resGo ` ), '
               'every stack restored; by cases on ` z99 < q ` (the prefix ~ tmikpa , then ` load\' ( flag := false ) ` or '
               '~ tmiptb ) and on ` isPrimeTD q ` ( ` skip ` , or ` dup 2 6 7 ; predNum 6 7 ` and ~ tmistdb ).')
    s = w.s
    pre0 = s([], 'tmikpa', STMTS10['tmikpa'])
    pre = s([pre0], 'adantr', '( %s -> %s )' % (ph, CONCL_KPA))
    TB = '( TMB ` B )'
    outs = []
    for lt in (True, False):
        c1 = 'G < Q' if lt else '-. G < Q'
        inner = []
        for pr in ((True, False) if lt else (None,)):
            conds = [c1] + ([] if pr is None else ['%s = 1o' % IP1 if pr else '-. %s = 1o' % IP1])
            T = T0
            for cc in conds:
                T = (T, cc)
            pc = cj(T)
            B = Kp(w, pc, T)
            c, mk = B.c, B.mk
            tp = pre
            cur = ph
            for cc in conds:
                nxt = '( %s /\\ %s )' % (cur, cc)
                tp = s([tp], 'adantr', '( %s -> %s )' % (nxt, CONCL_KPA))
                cur = nxt
            C0_, D0_, n0_ = triple_parts(CONCL_KPA)
            R = B.run()
            cl = Closure(w, pc, {'B': ('NN0', B.bn), 'Q': ('NN', B.qnn), 'Y': ('NN', B.ynn)})
            cl.leaf(TB, 'NN0', B.tbn)
            p2 = '( 2 ^ B )'
            cl.atom(p2)
            if lt:
                ltc = c[c1]
                ex = {STMT(GT(LM['Z4'])): gotocl(w, pc, mk['tv'], LM['Z4'], B.ex[LAB(LM['Z4'])]), SSS(CQ): B.ss(CQ),
                      'A. m e. %s ( %s ` m ) = 1o' % (CQ, CLT): clt_test(w, pc, B.gn, B.qn, True, c[c1]),
                      CTY(CLT): lamty(w, pc, mk, CLT, lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t, '2o', s([], '2oex', '2o e. _V'),
                                      s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli', 'if ( ( TMcmp ` u ) = (/) , 1o , (/) ) e. 2o'))}
                B.call(R, 'tm2lbrt', {'A': LM['Z1'], 'C': CLT, 'E': LM['Y4'], 'Q': GT(LM['Z4']), 'N': CQ}, ex, [])
                B.call(R, 'tmiptb', {'K': '2', 'J': '4', 'I': '6', "I'": '7', 'I"': '3', 'I0': '1', 'F': 'Q', 'N': 'B', 'X': 'Z',
                                     'P': PL('P', 7), 'E': LM['Z2']}, {'Q e. NN0': B.qn}, [], pre=(CQ, B.ss(CQ)))
                NP1 = NFL(IP1)
                pm = '( %s /\\ m e. %s )' % (pc, NP1)
                mm, mf = A8.nfl_unpack(w, pm, IP1, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NP1)))
                prc = c[conds[1]]
                if pr:
                    fl1 = s([mf, lift_from(w, pc, pm, prc)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
                    ex2 = {STMT(GT(LM['Z3'])): gotocl(w, pc, mk['tv'], LM['Z3'], B.ex[LAB(LM['Z3'])]), SSS(NP1): B.ss(NP1),
                           'A. m e. %s ( TMfl ` m ) = 1o' % NP1: s([fl1], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (pc, NP1))}
                    B.call(R, 'tm2lbrt', {'A': LM['Z2'], 'C': 'TMfl', 'E': LM['Y5'], 'Q': GT(LM['Z3']), 'N': NP1}, ex2, [])
                    E6 = EWg('Q', DK(6))
                    B.call(R, 'tmidupb', {'K': '2', 'J': '6', 'I': '7', 'F': 'Q', 'N': 'B', 'X': 'Z', 'P': PL('P', 8), 'E': LM['Y6']},
                           {'Q e. NN0': B.qn}, [('6', E6, B.g(E6, ewg_(w, pc, 'Q', B.qn, DK(6), B.S0.vals['6'][2])))], pre=(NP1, B.ss(NP1)))
                    Q1 = '( Q - 1 )'
                    q1n = s([B.qnn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (pc, Q1))
                    E61 = EWg(Q1, DK(6))
                    qlt = c['Q < ( 2 ^ B )']
                    B.call(R, 'tmiprdbs', {'K': '6', 'J': '7', 'F': 'Q', 'N': 'B', 'X': DK(6), 'P': PL('P', 9), 'E': LM['Y7']},
                           {}, [('6', E61, B.g(E61, ewg_(w, pc, Q1, q1n, DK(6), B.S0.vals['6'][2])))])
                    q1lt = linarith(w, pc, [qlt], '%s < %s' % (Q1, p2), closure=cl)
                    B.call(R, 'tmistdb', {'Y': 'Y', 'F': Q1, 'X': 'X', "X'": DK(6), 'B': 'B', 'P': PL('P', 10), 'E': 'E'},
                           {'%s e. NN0' % Q1: q1n, '%s < %s' % (Q1, p2): q1lt}, [('6', DK(6), B.S0.vals['6'][2])])
                    cur, out = R.normalize(N8)
                    assert out == [], out
                    VF = SMT1
                    e_ = None and s([s([s([prc], 'iftrued', '( %s -> %s = %s )' % (pc, 'if ( %s = 1o , %s , (/) )' % (IP1, SMT1), SMT1)),
                               s([ltc], 'iftrued', '( %s -> %s = %s )' % (pc, RK_, 'if ( %s = 1o , %s , (/) )' % (IP1, SMT1)))], 'eqtr4d',
                              '( %s -> %s = %s )' % (pc, SMT1, RK_)) if False else None] if False else [], 'id', '') if False else None
                    ef = s([s([ltc], 'iftrued', '( %s -> %s = %s )' % (pc, RK_, 'if ( %s = 1o , %s , (/) )' % (IP1, SMT1))),
                            s([prc], 'iftrued', '( %s -> %s = %s )' % (pc, 'if ( %s = 1o , %s , (/) )' % (IP1, SMT1), SMT1))], 'eqtrd',
                           '( %s -> %s = %s )' % (pc, RK_, SMT1))
                else:
                    fne = s([mf, s([s([s([prc], 'neqned', '( %s -> %s =/= 1o )' % (pc, IP1))], 'id', '') if False else
                                   s([prc], 'neqned', '( %s -> %s =/= 1o )' % (pc, IP1))], 'adantr', '( %s -> %s =/= 1o )' % (pm, IP1))], 'eqnetrd',
                            '( %s -> ( TMfl ` m ) =/= 1o )' % pm)
                    nf = s([s([fne], 'neneqd', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)], 'ralrimiva', '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (pc, NP1))
                    ex2 = {STMT(GT(LM['Y5'])): gotocl(w, pc, mk['tv'], LM['Y5'], B.ex[LAB(LM['Y5'])]), SSS(NP1): B.ss(NP1),
                           'A. m e. %s -. ( TMfl ` m ) = 1o' % NP1: nf}
                    B.call(R, 'tm2fbrg', {'A': LM['Z2'], 'C': 'TMfl', 'E': LM['Z3'], 'Q': GT(LM['Y5']), 'N': NP1}, ex2, [])
                    B.call(R, 'tm2flg', {'A': LM['Z3'], 'E': 'E', 'F': LID, 'N': NP1, "N'": NP1},
                           {LTY(LID): skip_ty(w, pc, mk), SSS(NP1): B.ss(NP1), 'A. r e. %s ( %s ` r ) e. %s' % (NP1, LID, NP1): skip_in(w, pc, NP1)}, [])
                    VF = IP1
                    # IP1 = (/) : it is in 2o and not 1o
                    ipc = s([B.qn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` Q ) e. ( 2o X. NN0 ) )' % pc)
                    ip2 = s([s([ipc, w.inst('xp1st')], 'syl', '( %s -> %s e. 2o )' % (pc, IP1)), s([s([], 'df2o3', '2o = { (/) , 1o }')], 'a1i',
                                                                                                  '( %s -> 2o = { (/) , 1o } )' % pc)], 'eleqtrd',
                            '( %s -> %s e. { (/) , 1o } )' % (pc, IP1))
                    ipo = s([ip2, w.inst('elpri')], 'syl', '( %s -> ( %s = (/) \\/ %s = 1o ) )' % (pc, IP1, IP1))
                    ipn = s([s([ipo], 'orcomd', '( %s -> ( %s = 1o \\/ %s = (/) ) )' % (pc, IP1, IP1))], 'ord', '( %s -> ( -. %s = 1o -> %s = (/) ) )' % (pc, IP1, IP1))
                    ip0 = s([prc, ipn], 'mpd', '( %s -> %s = (/) )' % (pc, IP1))
                    ef = s([s([s([ltc], 'iftrued', '( %s -> %s = %s )' % (pc, RK_, 'if ( %s = 1o , %s , (/) )' % (IP1, SMT1))),
                               s([prc], 'iffalsed', '( %s -> %s = (/) )' % (pc, 'if ( %s = 1o , %s , (/) )' % (IP1, SMT1)))], 'eqtrd',
                              '( %s -> %s = (/) )' % (pc, RK_)), s([ip0], 'eqcomd', '( %s -> (/) = %s )' % (pc, IP1))], 'eqtrd',
                           '( %s -> %s = %s )' % (pc, RK_, IP1))
            else:
                nlc = c[c1]
                ex = {STMT(GT(LM['Y4'])): gotocl(w, pc, mk['tv'], LM['Y4'], B.ex[LAB(LM['Y4'])]), SSS(CQ): B.ss(CQ),
                      'A. m e. %s -. ( %s ` m ) = 1o' % (CQ, CLT): clt_test(w, pc, B.gn, B.qn, False, c[c1]),
                      CTY(CLT): lamty(w, pc, mk, CLT, lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t, '2o', s([], '2oex', '2o e. _V'),
                                      s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli', 'if ( ( TMcmp ` u ) = (/) , 1o , (/) ) e. 2o'))}
                B.call(R, 'tm2fbrg', {'A': LM['Z1'], 'C': CLT, 'E': LM['Z4'], 'Q': GT(LM['Y4']), 'N': CQ}, ex, [])
                kw = lambda t: dict(fl='(/)')
                pr_ = '( %s /\\ r e. %s )' % (pc, CQ)
                rin = s([], 'simpr', '( %s -> r e. %s )' % (pr_, CQ))
                rr = s([rin, w.inst('elrabi')], 'syl', '( %s -> r e. TMSt )' % pr_)
                nv = lset_val2(w, pr_, kw, 'r', rr)
                NR = '( %s ` r )' % L_F0
                inm = A8.nfl_pack(w, pr_, '(/)', NR, nv['mem'], nv['fields']['fl'])
                hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (pc, CQ, L_F0, NFL('(/)')))
                B.call(R, 'tm2flg', {'A': LM['Z4'], 'E': 'E', 'F': L_F0, 'N': CQ, "N'": NFL('(/)')},
                       {LTY(L_F0): lset_ty2(w, pc, mk, L_F0, kw), SSS(CQ): B.ss(CQ), SSS(NFL('(/)')): B.ss(NFL('(/)')),
                        'A. r e. %s ( %s ` r ) e. %s' % (CQ, L_F0, NFL('(/)')): hl}, [])
                VF = '(/)'
                ef = s([nlc], 'iffalsed', '( %s -> %s = (/) )' % (pc, RK_))
            t1, C1, D1, n1 = R.tri, R.C0, R.cur, R.n
            assert C1 == D0_, (C1, D0_)
            t2 = hrseq(w, pc, mk['phm'], tp, t1, C0_, D0_, D1, n0_, n1)
            n2 = '( %s + %s )' % (n0_, n1)
            t2, C2, D2, n2 = cls_to(w, pc, (t2, C0_, D1, n2), VF, RK_, s([ef], 'eqcomd', '( %s -> %s = %s )' % (pc, VF, RK_)))
            # the bound
            P1_ = '( ( ( 2nd ` ( IsPrimeTD ` Q ) ) + 1 ) x. %s )' % TMBx('( ( 3 x. B ) + 7 )')
            P2_ = '( ( ( 2nd ` ( Y SmoothTD ( Q - 1 ) ) ) + 1 ) x. %s )' % TMBx('( ( 4 x. B ) + ; 1 0 )')
            ipc = s([B.qn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` Q ) e. ( 2o X. NN0 ) )' % pc)
            q1n = s([B.qnn, w.inst('nnm1nn0')], 'syl', '( %s -> ( Q - 1 ) e. NN0 )' % pc)
            smc = s([B.ynn, q1n, w.inst('smoothtdcl')], 'syl2anc', '( %s -> ( Y SmoothTD ( Q - 1 ) ) e. ( 2o X. NN0 ) )' % pc)

            def tmbn(x):
                return s([s([cl.mem(x, 'NN0'), w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` %s ) e. NN )' % (pc, x))], 'nnnn0d',
                         '( %s -> ( TMB ` %s ) e. NN0 )' % (pc, x))
            p1n = s([s([s([ipc, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( IsPrimeTD ` Q ) ) e. NN0 )' % pc), w.inst('peano2nn0')], 'syl',
                       '( %s -> ( ( 2nd ` ( IsPrimeTD ` Q ) ) + 1 ) e. NN0 )' % pc), tmbn('( ( 3 x. B ) + 7 )'), w.inst('nn0mulcl')], 'syl2anc',
                    '( %s -> %s e. NN0 )' % (pc, P1_))
            p2n = s([s([s([smc, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( Y SmoothTD ( Q - 1 ) ) ) e. NN0 )' % pc), w.inst('peano2nn0')], 'syl',
                       '( %s -> ( ( 2nd ` ( Y SmoothTD ( Q - 1 ) ) ) + 1 ) e. NN0 )' % pc), tmbn('( ( 4 x. B ) + ; 1 0 )'), w.inst('nn0mulcl')],
                    'syl2anc', '( %s -> %s e. NN0 )' % (pc, P2_))
            cl.leaf(P1_, 'NN0', p1n)
            cl.leaf(P2_, 'NN0', p2n)
            tbp = s([s([B.bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pc, TB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pc, TB))
            le = linarith(w, pc, [tbp, cl.ge0(P1_), cl.ge0(P2_)], '%s <_ %s' % (n2, KPB), closure=cl)
            inner.append(hrle(w, pc, mk['phm'], t2, C2, D2, n2, KPB, cl.mem(KPB, 'NN0'), le))
        if lt:
            outs.append(s(inner, 'pm2.61dan', '( ( %s /\\ %s ) -> %s )' % (ph, c1, CONCL_KP)))
        else:
            outs.append(inner[0])
    st = s(outs, 'pm2.61dan', '( %s -> %s )' % (ph, CONCL_KP))
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
