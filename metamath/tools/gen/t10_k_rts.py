"""T10: resTestF at the machine (Lean ` resTestF_runs ` ): ~ tmikp , then ` ite flag ( dup 2 5 6 ) skip ` by cases.

    MM_DB=sorties/t10.mm python3 tools/gen/t10_k_rts.py tmirts
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith
from cl import Closure
from t10_e_doa import lift_from
from t10_d_dot import skip_ty, skip_in
from t10_j_kp import Kp
from t5lib import hrssd, cfgcl

SEL = sys.argv[1:]
LM = FRAGS['rts'].lmap()
KEEP = '%s = 1o' % RK_
V5 = IFV(KEEP, EWg('Q', DK(5)), DK(5))


def tmirts():
    lab = 'tmirts'
    T0 = numtree(TREE_RTS)
    ph = cj(T0)
    w = W(lab, 'Lean\'s ` resTestF_runs ` at the machine: ~ tmikp , then ` q ` is pushed on the open list (stack 5) exactly '
               'when ` resKeep z99 y q ` , every other stack restored (by cases on the flag).')
    s = w.s
    outs = []
    for keep in (True, False):
        cnd = KEEP if keep else '-. %s' % KEEP
        T = (T0, cnd)
        pc = cj(T)
        B = Kp.__new__(Kp)
        Kp.__init__(B, w, pc, T) if False else None
        # the Base of rts with the kp data
        c0 = Ctx(w, pc, T)
        gn, ynn, qnn = c0['G e. NN0'], c0['Y e. NN'], c0['Q e. NN']
        yn = s([ynn], 'nnnn0d', '( %s -> Y e. NN0 )' % pc)
        qn = s([qnn], 'nnnn0d', '( %s -> Q e. NN0 )' % pc)
        eqs = {'0': (EWg('Y', 'X'), ewg_(w, pc, 'Y', yn, 'X', c0[WG('X')])), '1': (EWg('G', "X'"), ewg_(w, pc, 'G', gn, "X'", c0[WG("X'")])),
               '2': (EWg('Q', 'Z'), ewg_(w, pc, 'Q', qn, 'Z', c0[WG('Z')]))}
        B = Base(w, pc, T, N8, 'rts', eqs)
        c, mk = B.c, B.mk
        bn = c['B e. NN0']
        R = B.run()
        B.call(R, 'tmikp', {'P': PL('P', 2), 'E': LM['Z1']}, {}, [])
        NK = NFL(RK_)
        pm = '( %s /\\ m e. %s )' % (pc, NK)
        mm, mf = A8.nfl_unpack(w, pm, RK_, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NK)))
        kc = c[cnd]
        TB = '( TMB ` B )'
        if keep:
            fl1 = s([mf, lift_from(w, pc, pm, kc)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
            B.call(R, 'tm2lbrt', {'A': LM['Z1'], 'C': 'TMfl', 'E': LM['Y2'], 'Q': GT(LM['Z2']), 'N': NK},
                   {STMT(GT(LM['Z2'])): gotocl(w, pc, mk['tv'], LM['Z2'], B.ex[LAB(LM['Z2'])]), SSS(NK): B.ss(NK),
                    'A. m e. %s ( TMfl ` m ) = 1o' % NK: s([fl1], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (pc, NK))}, [])
            E5 = EWg('Q', DK(5))
            B.call(R, 'tmidupb', {'K': '2', 'J': '5', 'I': '6', 'F': 'Q', 'N': 'B', 'X': 'Z', 'P': PL('P', 3), 'E': 'E'},
                   {'Q e. NN0': qn}, [('5', E5, B.g(E5, ewg_(w, pc, 'Q', qn, DK(5), B.S0.vals['5'][2])))], pre=(NK, B.ss(NK)))
            cur, out = R.normalize(N8)
            assert out == [('5', E5)], out
            ve = s([kc], 'iftrued', '( %s -> %s = %s )' % (pc, V5, E5))
            deq = upeq(w, pc, 'D', '5', s([ve], 'eqcomd', '( %s -> %s = %s )' % (pc, E5, V5)), E5, V5)
        else:
            f0 = s([mf, s([lift_from(w, pc, pm, s([kc], 'neqned', '( %s -> %s =/= 1o )' % (pc, RK_)))], 'id', '') if False else
                        lift_from(w, pc, pm, s([kc], 'neqned', '( %s -> %s =/= 1o )' % (pc, RK_)))], 'eqnetrd', '( %s -> ( TMfl ` m ) =/= 1o )' % pm)
            nf = s([s([f0], 'neneqd', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)], 'ralrimiva', '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (pc, NK))
            B.call(R, 'tm2fbrg', {'A': LM['Z1'], 'C': 'TMfl', 'E': LM['Z2'], 'Q': GT(LM['Y2']), 'N': NK},
                   {STMT(GT(LM['Y2'])): gotocl(w, pc, mk['tv'], LM['Y2'], B.ex[LAB(LM['Y2'])]), SSS(NK): B.ss(NK),
                    'A. m e. %s -. ( TMfl ` m ) = 1o' % NK: nf}, [])
            B.call(R, 'tm2flg', {'A': LM['Z2'], 'E': 'E', 'F': LID, 'N': NK, "N'": NK},
                   {LTY(LID): skip_ty(w, pc, mk), SSS(NK): B.ss(NK), 'A. r e. %s ( %s ` r ) e. %s' % (NK, LID, NK): skip_in(w, pc, NK)}, [])
            ve = s([kc], 'iffalsed', '( %s -> %s = %s )' % (pc, V5, DK(5)))
            u = upidv(w, pc, 'D', '5', V5, s([ve], 'eqcomd', '( %s -> %s = %s )' % (pc, DK(5), V5)), mk['tv'], B.dd, mk['k']['5']['kd'])
            deq = s([u], 'eqcomd', '( %s -> D = %s )' % (pc, UP('D', '5', V5)))
        t, C, D, n = R.tri, R.C0, R.cur, R.n
        Dc = triple_D(D)
        DF = UP('D', '5', V5)
        Ncl = D.split(' } X. ( ', 1)[1].rsplit(' X. { ', 1)[0]
        t, C, D, n = hrrw(w, pc, t, C, D, n, deq=clneq(w, pc, 'E', Ncl, deq, Dc, DF))
        # class to ( 2nd ` T )
        v5g = s([s([B.gam[EWg('Q', DK(5))] if keep else ewg_(w, pc, 'Q', qn, DK(5), B.S0.vals['5'][2]), B.S0.vals['5'][2]], 'ifcld',
                   "( %s -> %s e. Word Gamma' )" % (pc, V5))], 'id', '') if False else \
            s([ewg_(w, pc, 'Q', qn, DK(5), B.S0.vals['5'][2]), B.S0.vals['5'][2]], 'ifcld', "( %s -> %s e. Word Gamma' )" % (pc, V5))
        Sdf = B.S0.upd('5', V5, v5g)
        cfg = cfgcl(w, pc, 'E', S, DF, mk['tv'], B.ex[LAB('E')], closed(w, pc, 'ssid', '%s C_ %s' % (S, S)), Sdf.memb)
        if Ncl != S:
            t = hrssd(w, pc, mk['phm'], t, C, D, n, CLN('E', S, DF), clnss(w, pc, 'E', NK, S, DF, B.ss(NK)), cfg)
        D = CLN('E', S, DF)
        # the bound
        cl = Closure(w, pc, {'B': ('NN0', bn), 'Q': ('NN', qnn), 'Y': ('NN', ynn)})
        tbn = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pc, TB))], 'nnnn0d', '( %s -> %s e. NN0 )' % (pc, TB))
        cl.leaf(TB, 'NN0', tbn)
        tbp = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pc, TB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pc, TB))
        P1_ = '( ( ( 2nd ` ( IsPrimeTD ` Q ) ) + 1 ) x. %s )' % TMBx('( ( 3 x. B ) + 7 )')
        P2_ = '( ( ( 2nd ` ( Y SmoothTD ( Q - 1 ) ) ) + 1 ) x. %s )' % TMBx('( ( 4 x. B ) + ; 1 0 )')
        ipc = s([qn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` Q ) e. ( 2o X. NN0 ) )' % pc)
        q1n = s([qnn, w.inst('nnm1nn0')], 'syl', '( %s -> ( Q - 1 ) e. NN0 )' % pc)
        smc = s([ynn, q1n, w.inst('smoothtdcl')], 'syl2anc', '( %s -> ( Y SmoothTD ( Q - 1 ) ) e. ( 2o X. NN0 ) )' % pc)

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
        le = linarith(w, pc, [tbp, cl.ge0(P1_), cl.ge0(P2_)], '%s <_ %s' % (n, RTSB), closure=cl)
        outs.append(hrle(w, pc, mk['phm'], t, C, D, n, RTSB, cl.mem(RTSB, 'NN0'), le))
    st = s(outs, 'pm2.61dan', '( %s -> %s )' % (ph, CONCL_RTS))
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
