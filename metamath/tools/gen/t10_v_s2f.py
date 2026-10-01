"""T10: step2F at the machine (Lean ` step2F_le_B ` ): ` step2Pre ` (~ tmis2p ), then ` ite ( cmp = lt ) `
( ` load' ( flag := false ) ` or ` step2Succ ` (~ tmis2s ) ), the two cases through ` if ( len < T , _ , _ ) ` .

    MM_DB=sorties/t10.mm python3 tools/gen/t10_v_s2f.py tmis2fb
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, nlinarith, lineq
from t7lib import mval, not1o, ifex_closed
from cl import Closure, split_top
from t10_e_doa import lift_from
from t10_n_rgf import tmbn
from t10_p_s2p import RGZ
import t8alib as A8
import num

SEL = sys.argv[1:]
F_ = FRAGS['s2f']
LM = F_.lmap()
CQ = CMPC(LEN_, 'U')
XL = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t


def clt_test2(w, pc, a, b, an, bn, truth, cnd):
    """( pc -> A. m e. CMPC( a , b ) ( CLT ` m ) = 1o ) from cnd : a < b (truth), or the negation from -. a < b"""
    s = w.s
    C = CMPC(a, b)
    pm = '( %s /\\ m e. %s )' % (pc, C)
    mi = s([], 'simpr', '( %s -> m e. %s )' % (pm, C))
    cond = lambda t: '( TMcmp ` %s ) = ( %s Ncmp %s )' % (t, a, b)
    idh = s([], 'id', '( h = m -> h = m )')
    cg, new = w.wcongr(cond('h'), {'h': 'm'}, 'h = m', {'h': idh})
    both = s([mi, s([cg], 'elrab', '( m e. %s <-> ( m e. TMSt /\\ %s ) )' % (C, cond('m')))], 'sylib', '( %s -> ( m e. TMSt /\\ %s ) )' % (pm, cond('m')))
    mm = s([both], 'simpld', '( %s -> m e. TMSt )' % pm)
    mc = s([both], 'simprd', '( %s -> %s )' % (pm, cond('m')))
    xex = ifex_closed(w, pm, '( TMcmp ` m ) = (/)', '1o', '(/)', s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', XL, 'm', mm, xex)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pc, st)))
    nl = s([s([an, bn], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (pc, a, b)), w.inst('ncmplt')], 'syl',
           '( %s -> ( ( %s Ncmp %s ) = (/) <-> %s < %s ) )' % (pc, a, b, a, b))
    if truth:
        nc0 = s([cnd, nl], 'mpbird', '( %s -> ( %s Ncmp %s ) = (/) )' % (pc, a, b))
        cm0 = s([mc, Lm(nc0)], 'eqtrd', '( %s -> ( TMcmp ` m ) = (/) )' % pm)
        v = s([cv, s([cm0], 'iftrued', '( %s -> %s = 1o )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CLT))
        return s([v], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pc, C, CLT))
    nn0 = s([cnd, nl], 'mtbird', '( %s -> -. ( %s Ncmp %s ) = (/) )' % (pc, a, b))
    cm1 = s([Lm(nn0), s([mc], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = (/) <-> ( %s Ncmp %s ) = (/) ) )' % (pm, a, b))], 'mtbird',
            '( %s -> -. ( TMcmp ` m ) = (/) )' % pm)
    c0 = s([cv, s([cm1], 'iffalsed', '( %s -> %s = (/) )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CLT))
    return s([not1o(w, pm, c0, CLT, 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pc, C, CLT))


def res_facts(w, ph, c, znn, gn, ynn, bn):
    """the reservoir's typings and bounds (as in ~ tmis2p ): rlw, rsc, lenn, rcn, len < 2 ^ B , len <_ rc , entries < 2 ^ B"""
    s = w.s
    RSV, RL, LEN, RC = RSV_, RL_, LEN_, RC_
    p2 = '( 2 ^ B )'
    zn = s([znn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)
    rsc = s([s([s([znn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), ynn], 'jca', '( %s -> ( ( Z e. NN /\\ G e. NN0 ) /\\ Y e. NN ) )' % ph),
             w.inst('reservoircl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, RSV))
    rlw = s([rsc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, RL))
    rv = s([s([s([znn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), ynn], 'jca', '( %s -> ( ( Z e. NN /\\ G e. NN0 ) /\\ Y e. NN ) )' % ph),
            w.inst('reservoirval')], 'syl', '( %s -> %s = %s )' % (ph, RSV, RGZ))
    Z1 = '( Z - 1 )'
    z1n = s([znn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, Z1))
    rgl = s([s([s([gn, ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([closed(w, ph, '2nn', '2 e. NN'), z1n], 'jca',
                                                                                  '( %s -> ( 2 e. NN /\\ %s e. NN0 ) )' % (ph, Z1))],
               'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( 2 e. NN /\\ %s e. NN0 ) ) )' % (ph, Z1)),
             w.inst('rgln')], 'syl', '( %s -> ( ( # ` ( 1st ` %s ) ) <_ %s /\\ %s <_ ( 2nd ` %s ) ) )' % (ph, RGZ, Z1, Z1, RGZ))
    l1 = s([s([s([rv], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (ph, RL, RGZ))], 'fveq2d', '( %s -> %s = ( # ` ( 1st ` %s ) ) )' % (ph, LEN, RGZ)),
            s([rgl], 'simpld', '( %s -> ( # ` ( 1st ` %s ) ) <_ %s )' % (ph, RGZ, Z1))], 'eqbrtrd', '( %s -> %s <_ %s )' % (ph, LEN, Z1))
    l2 = s([s([rgl], 'simprd', '( %s -> %s <_ ( 2nd ` %s ) )' % (ph, Z1, RGZ)), s([s([rv], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (ph, RC, RGZ))], 'eqcomd',
                                                                              '( %s -> ( 2nd ` %s ) = %s )' % (ph, RGZ, RC))], 'breqtrd', '( %s -> %s <_ %s )' % (ph, Z1, RC))
    lenn = s([rlw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN))
    rcn = s([rsc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, RC))
    cl = Closure(w, ph, {'Z': ('NN', znn), 'B': ('NN0', bn)})
    cl.leaf(LEN, 'NN0', lenn)
    cl.leaf(RC, 'NN0', rcn)
    cl.atom(p2)
    lenlt = linarith(w, ph, [l1, c['Z < ( 2 ^ B )']], '%s < %s' % (LEN, p2), closure=cl)
    lr = linarith(w, ph, [l1, l2], '%s <_ %s' % (LEN, RC), closure=cl)
    pa = '( %s /\\ a e. ran %s )' % (ph, RL)
    ain0 = s([], 'simpr', '( %s -> a e. ran %s )' % (pa, RL))
    ain = s([ain0, s([lift_from(w, ph, pa, s([rv], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (ph, RL, RGZ)))], 'rneqd',
                     '( %s -> ran %s = ran ( 1st ` %s ) )' % (pa, RL, RGZ))], 'eleqtrd', '( %s -> a e. ran ( 1st ` %s ) )' % (pa, RGZ))
    frn = s([s([lift_from(w, ph, pa, rlw), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, RL, RL)), w.inst('frn')], 'syl',
            '( %s -> ran %s C_ NN0 )' % (pa, RL))
    ann = s([frn, ain0], 'sseldd', '( %s -> a e. NN0 )' % pa)
    gm = s([s([s([lift_from(w, ph, pa, gn), lift_from(w, ph, pa, ynn), closed(w, pa, '2nn', '2 e. NN')], '3jca',
                 '( %s -> ( G e. NN0 /\\ Y e. NN /\\ 2 e. NN ) )' % pa), s([lift_from(w, ph, pa, z1n), ann], 'jca', '( %s -> ( %s e. NN0 /\\ a e. NN0 ) )' % (pa, Z1))],
               'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN /\\ 2 e. NN ) /\\ ( %s e. NN0 /\\ a e. NN0 ) ) )' % (pa, Z1)), w.inst('resgomem')], 'syl',
           '( %s -> ( a e. ran ( 1st ` %s ) <-> ( ( 2 <_ a /\\ a < ( 2 + %s ) ) /\\ ( G < a /\\ a e. Prime /\\ A. p e. Prime ( p || ( a - 1 ) -> p <_ Y ) ) ) ) )'
           % (pa, RGZ, Z1))
    gm2 = s([ain, gm], 'mpbid', '( %s -> ( ( 2 <_ a /\\ a < ( 2 + %s ) ) /\\ ( G < a /\\ a e. Prime /\\ A. p e. Prime ( p || ( a - 1 ) -> p <_ Y ) ) ) )' % (pa, Z1))
    alt = s([s([gm2], 'simpld', '( %s -> ( 2 <_ a /\\ a < ( 2 + %s ) ) )' % (pa, Z1))], 'simprd', '( %s -> a < ( 2 + %s ) )' % (pa, Z1))
    clp = Closure(w, pa, {'a': ('NN0', ann), 'Z': ('NN', lift_from(w, ph, pa, znn)), 'B': ('NN0', lift_from(w, ph, pa, bn))})
    e2z = lineq(w, pa, '( 2 + %s )' % Z1, '( Z + 1 )', closure=clp)
    alz = s([alt, e2z], 'breqtrd', '( %s -> a < ( Z + 1 ) )' % pa)
    alez = s([alz, s([ann, lift_from(w, ph, pa, zn), w.inst('nn0leltp1')], 'syl2anc', '( %s -> ( a <_ Z <-> a < ( Z + 1 ) ) )' % pa)], 'mpbird',
             '( %s -> a <_ Z )' % pa)
    clp.atom(p2)
    a2 = linarith(w, pa, [alez, lift_from(w, ph, pa, c['Z < ( 2 ^ B )'])], 'a < %s' % p2, closure=clp)
    ral = s([a2], 'ralrimiva', '( %s -> A. a e. ran %s a < %s )' % (ph, RL, p2))
    return dict(rlw=rlw, rsc=rsc, lenn=lenn, rcn=rcn, lenlt=lenlt, lr=lr, ral=ral)


def tmis2fb():
    lab = 'tmis2fb'
    T0 = numtree(TREE_S2F)
    ph0 = cj(T0)
    w = W(lab, 'Lean\'s ` step2F_le_B ` at the machine: ` step2Pre ` (~ tmis2p ), then ` ite ( cmp = lt ) ` : for ` len < T ` '
               '` flag := false ` with the stacks of ` step2Pre ` , otherwise ` step2Succ ` (~ tmis2s ) at the reservoir; the two '
               'cases through ` if ( len < T , _ , _ ) ` , within ` ( step2Cost + 1 ) B ( 15 ( T + 1 ) b + 46 ) ` steps.')
    s = w.s
    outs = []
    DFIN = DFIN_S2F
    for fail in (True, False):
        cnd = FAIL_ if fail else '-. %s' % FAIL_
        T = (T0, cnd)
        pc = cj(T)
        c0 = Ctx(w, pc, T)
        znn, gn, ynn, un, on, bn = c0['Z e. NN'], c0['G e. NN0'], c0['Y e. NN'], c0['U e. NN0'], c0['O e. NN0'], c0['B e. NN0']
        zn = s([znn], 'nnnn0d', '( %s -> Z e. NN0 )' % pc)
        yn = s([ynn], 'nnnn0d', '( %s -> Y e. NN0 )' % pc)
        rw_ = c0[WG('R')]
        EOR = EWg('O', 'R')
        gor = ewg_(w, pc, 'O', on, 'R', rw_)
        guo = ewg_(w, pc, 'U', un, EOR, gor)
        E1 = EWg('Y', EWUO)
        gyu = ewg_(w, pc, 'Y', yn, EWUO, guo)
        E2 = EWg('G', E1)
        ggy = ewg_(w, pc, 'G', gn, E1, gyu)
        E3 = EWg('Z', E2)
        eqs = {'0': (E3, ewg_(w, pc, 'Z', zn, E2, ggy))}
        B = Base(w, pc, T, N8, 's2f', eqs)
        c, mk = B.c, B.mk
        for t_, st_ in ((EOR, gor), (EWUO, guo), (E1, gyu), (E2, ggy)):
            B.g(t_, st_)
        g = lambda k: B.S0.vals[k][2]
        R = B.run()
        rf = res_facts(w, pc, c, znn, gn, ynn, bn)
        RL, LEN, RC = RL_, LEN_, RC_
        # 1. step2Pre
        E4 = ENCL(RL, DK(4))
        EZ1, EL2 = EWg('Z', DK(1)), EWg(LEN, DK(2))
        B.call(R, 'tmis2p', {'P': PL('P', 2), 'E': LM['Z1']}, {},
               [('0', EWUO, guo), ('1', EZ1, B.g(EZ1, ewg_(w, pc, 'Z', zn, DK(1), g('1')))),
                ('2', EL2, B.g(EL2, ewg_(w, pc, LEN, rf['lenn'], DK(2), g('2')))), ('4', E4, B.g(E4, enclg(w, pc, RL, rf['rlw'], DK(4), g('4'))))],
               cls_rw=None)
        from t7blib import unfold_all
        S2 = FRAGS['s2s']
        P3 = PL('P', 3)
        sp = S2.pred([], 'T', 'M', P3, 'E')
        fn0, cks0, en0, exn0 = S2.children[0]
        l2 = S2.lmap(P3, 'E')
        cp0 = FRAGS[fn0].pred(cks0, 'T', 'M', PL(P3, S2.slot(0)), l2[exn0])
        if cp0 not in B.ex:
            B.ex.update(unfold_all(w, pc, B.ex[sp], 's2s', [], P3, 'E', rec=False))
        B.ex.update(unfold_all(w, pc, B.ex[cp0], fn0, cks0, PL(P3, S2.slot(0)), l2[exn0], rec=False))
        R.base.update(B.ex)
        # the class after step2Pre is CQ (the call's own post class)
        ctyl = lamty(w, pc, mk, CLT, XL, '2o', s([], '2oex', '2o e. _V'),
                     s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % XL('u')))
        if fail:
            ex = {STMT(GT(LM['Y2'])): gotocl(w, pc, mk['tv'], LM['Y2'], B.ex[LAB(LM['Y2'])]), SSS(CQ): B.ss(CQ),
                  'A. m e. %s ( %s ` m ) = 1o' % (CQ, CLT): clt_test2(w, pc, LEN, 'U', rf['lenn'], un, True, c[cnd]), CTY(CLT): ctyl}
            B.call(R, 'tm2lbrt', {'A': LM['Z1'], 'C': CLT, 'E': LM['Z2'], 'Q': GT(LM['Y2']), 'N': CQ}, ex, [])
            kw = lambda t: dict(fl='(/)')
            pr_ = '( %s /\\ r e. %s )' % (pc, CQ)
            rr = s([s([], 'simpr', '( %s -> r e. %s )' % (pr_, CQ)), w.inst('elrabi')], 'syl', '( %s -> r e. TMSt )' % pr_)
            nv = lset_val2(w, pr_, kw, 'r', rr)
            inm = A8.nfl_pack(w, pr_, '(/)', '( %s ` r )' % L_F0, nv['mem'], nv['fields']['fl'])
            hl = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (pc, CQ, L_F0, NFL('(/)')))
            B.call(R, 'tm2flg', {'A': LM['Z2'], 'E': 'E', 'F': L_F0, 'N': CQ, "N'": NFL('(/)')},
                   {LTY(L_F0): lset_ty2(w, pc, mk, L_F0, kw), SSS(CQ): B.ss(CQ), SSS(NFL('(/)')): B.ss(NFL('(/)')),
                    'A. r e. %s ( %s ` r ) e. %s' % (CQ, L_F0, NFL('(/)')): hl}, [])
            VF = '(/)'
        else:
            ex = {STMT(GT(LM['Z2'])): gotocl(w, pc, mk['tv'], LM['Z2'], B.ex[LAB(LM['Z2'])]), SSS(CQ): B.ss(CQ),
                  'A. m e. %s -. ( %s ` m ) = 1o' % (CQ, CLT): clt_test2(w, pc, LEN, 'U', rf['lenn'], un, False, c[cnd]), CTY(CLT): ctyl}
            B.call(R, 'tm2fbrg', {'A': LM['Z1'], 'C': CLT, 'E': LM['Y2'], 'Q': GT(LM['Z2']), 'N': CQ}, ex, [])
            cls = Closure(w, pc, {'U': ('NN0', un)})
            cls.leaf(LEN, 'NN0', rf['lenn'])
            ule = s([c[cnd], s([cls.mem('U', 'RR'), cls.mem(LEN, 'RR')], 'lenltd', '( %s -> ( U <_ %s <-> -. %s < U ) )' % (pc, LEN, LEN))], 'mpbird',
                    '( %s -> U <_ %s )' % (pc, LEN))
            X5, LL, QQ = X5_, LL_, QQ_
            qqw = s([rf['rlw'], w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, QQ))
            lln = s([s([qqw, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (pc, QQ)), w.inst('xp1st')], 'syl',
                    '( %s -> %s e. NN0 )' % (pc, LL))
            x5n = s([lln, closed(w, pc, '5nn0', '5 e. NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, X5))
            ex5r = ewg_(w, pc, X5, x5n, EOR, gor)
            E1x = EWg(X5, DK(1))
            g1x = B.g(E1x, ewg_(w, pc, X5, x5n, DK(1), g('1')))
            EOUT = [('0', EWg(X5, EOR), B.g(EWg(X5, EOR), ex5r)), ('1', EWg('Z', E1x), B.g(EWg('Z', E1x), ewg_(w, pc, 'Z', zn, E1x, g1x))),
                    ('2', EWg('1', DK(2)), B.g(EWg('1', DK(2)), ewg_(w, pc, '1', closed(w, pc, '1nn0', '1 e. NN0'), DK(2), g('2')))),
                    ('3', EWg(LL, DK(3)), B.g(EWg(LL, DK(3)), ewg_(w, pc, LL, lln, DK(3), g('3')))),
                    ('4', ENCL(QQ, DK(4)), B.g(ENCL(QQ, DK(4)), enclg(w, pc, QQ, qqw, DK(4), g('4'))))]
            B.call(R, 'tmis2s', {'W': RL, 'Z': 'Z', 'U': 'U', 'O': 'O', 'B': 'B', 'R': 'R', "R'": DK(1), 'R"': DK(2), 'Y': DK(4),
                                 'P': PL('P', 3), 'E': 'E'},
                   {'%s e. Word NN0' % RL: rf['rlw'], 'Z e. NN0': zn, 'A. a e. ran %s a < ( 2 ^ B )' % RL: rf['ral'],
                    '%s < ( 2 ^ B )' % LEN: rf['lenlt'], 'U <_ %s' % LEN: ule, WG(DK(1)): g('1'), WG(DK(2)): g('2'), WG(DK(4)): g('4')},
                   EOUT, pre=(CQ, B.ss(CQ)))
            VF = '1o'
        cur, of = R.normalize(N8)
        t, C, D, n = R.tri, R.C0, R.cur, R.n
        print('CASE', fail, 'CHAIN', of, file=sys.stderr)
        # the stacks: resolve the ifs of the frozen post
        IFF = 'if ( %s , ' % FAIL_
        rules = {}
        import re
        # every if ( FAIL , a , b ) subterm of DFIN
        toks = DFIN.split(' ')
        i = 0
        subs = []
        while True:
            k = DFIN.find('if ( %s , ' % FAIL_, i)
            if k < 0:
                break
            # find the matching close paren
            depth, j = 0, k + 3
            while True:
                if DFIN[j] == '(':
                    depth += 1
                elif DFIN[j] == ')':
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            subs.append(DFIN[k:j + 1])
            i = j + 1
        for sub in subs:
            inner = sub[len('if ( %s , ' % FAIL_):-2]
            a, b = split_top(inner.split(' '))[0], None
            parts = split_top(inner.split(' '))
            assert len(parts) == 3 and parts[1] == ',', parts
            a, b = parts[0], parts[2]
            val = a if fail else b
            ref = 'iftrued' if fail else 'iffalsed'
            rules[sub] = (val, s([c[cnd]], ref, '( %s -> %s = %s )' % (pc, sub, val)))
        rt, xt = w.rewrite(DFIN, rules, pc)
        Dc = triple_D(D)
        if fail:
            # xt has the identity update ( 3 , ( D ` 3 ) )
            Y3 = UPS('D', ('0', EWUO), ('1', EZ1), ('2', EL2))
            assert xt == UP(UP(Y3, '3', DK(3)), '4', E4), xt
            S3 = B.S0.upd('0', EWUO, guo).upd('1', EZ1, B.gam[EZ1]).upd('2', EL2, B.gam[EL2])
            u3 = upidv(w, pc, Y3, '3', DK(3), S3.vals['3'][1], mk['tv'], S3.memb, mk['k']['3']['kd'])
            r3, x3 = w.rewrite(xt, {UP(Y3, '3', DK(3)): (Y3, u3)}, pc)
            assert x3 == Dc, (x3, Dc)
            deq = s([s([rt, r3], 'eqtrd', '( %s -> %s = %s )' % (pc, DFIN, Dc))], 'eqcomd', '( %s -> %s = %s )' % (pc, Dc, DFIN))
        else:
            assert xt == Dc, (xt, Dc)
            deq = s([rt], 'eqcomd', '( %s -> %s = %s )' % (pc, Dc, DFIN))
        FV = 'if ( %s , (/) , 1o )' % FAIL_
        fv = s([c[cnd]], 'iftrued' if fail else 'iffalsed', '( %s -> %s = %s )' % (pc, FV, VF))
        cq = nfl_eq(w, pc, VF, FV, s([fv], 'eqcomd', '( %s -> %s = %s )' % (pc, VF, FV)))
        ceq = s([clnneq(w, pc, 'E', cq, NFL(VF), NFL(FV), Dc), clneq(w, pc, 'E', NFL(FV), deq, Dc, DFIN)], 'eqtrd',
                '( %s -> %s = %s )' % (pc, D, CLN('E', NFL(FV), DFIN)))
        t, C, D, n = hrrw(w, pc, t, C, D, n, deq=ceq)
        # the bound
        TB = '( TMB ` B )'
        M2 = '( ( ( 5 x. ( U + 1 ) ) x. B ) + ; 1 4 )'
        M = '( ( ( ; 1 5 x. ( U + 1 ) ) x. B ) + ; 4 6 )'
        TM2, TM = '( TMB ` %s )' % M2, '( TMB ` %s )' % M
        B4 = '( ( 4 x. B ) + ; 1 4 )'
        T4 = '( TMB ` %s )' % B4
        cl = Closure(w, pc, {'U': ('NN0', un), 'B': ('NN0', bn), 'Z': ('NN', znn)})
        cl.leaf(RC, 'NN0', rf['rcn'])
        cl.leaf(LEN, 'NN0', rf['lenn'])
        m2n = s([s([s([closed(w, pc, '5nn0', '5 e. NN0'), s([un, w.inst('peano2nn0')], 'syl', '( %s -> ( U + 1 ) e. NN0 )' % pc), w.inst('nn0mulcl')],
                       'syl2anc', '( %s -> ( 5 x. ( U + 1 ) ) e. NN0 )' % pc), bn, w.inst('nn0mulcl')], 'syl2anc',
                    '( %s -> ( ( 5 x. ( U + 1 ) ) x. B ) e. NN0 )' % pc), s([num.nn0(w, 14)], 'a1i', '( %s -> ; 1 4 e. NN0 )' % pc), w.inst('nn0addcl')],
                'syl2anc', '( %s -> %s e. NN0 )' % (pc, M2))
        b4n = s([s([closed(w, pc, '4nn0', '4 e. NN0'), bn, w.inst('nn0mulcl')], 'syl2anc', '( %s -> ( 4 x. B ) e. NN0 )' % pc),
                 s([num.nn0(w, 14)], 'a1i', '( %s -> ; 1 4 e. NN0 )' % pc), w.inst('nn0addcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, B4))
        M34 = '( ( 3 x. %s ) + 4 )' % M2
        me = lineq(w, pc, M, M34, closure=cl, products=True)
        tpl = s([m2n, w.inst('tplb34')], 'syl', '( %s -> ( TMB ` %s ) = ( ; 2 7 x. %s ) )' % (pc, M34, TM2))
        tme = s([s([me], 'fveq2d', '( %s -> %s = ( TMB ` %s ) )' % (pc, TM, M34)), tpl], 'eqtrd', '( %s -> %s = ( ; 2 7 x. %s ) )' % (pc, TM, TM2))
        ub0 = s([cl.mem('U', 'RR'), cl.mem('B', 'RR'), cl.ge0('U'), cl.ge0('B')], 'mulge0d', '( %s -> 0 <_ ( U x. B ) )' % pc)
        l4 = linarith(w, pc, [ub0, cl.ge0('U'), cl.ge0('B')], '%s <_ %s' % (B4, M2), closure=cl, products=True)
        m4 = s([b4n, m2n, l4, w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (pc, T4, TM2))
        cl.leaf(TM2, 'NN0', tmbn(w, pc, M2, m2n))
        cl.leaf(T4, 'NN0', tmbn(w, pc, B4, b4n))
        mn = cl.mem(M, 'NN0')
        cl.leaf(TM, 'NN0', tmbn(w, pc, M, mn))
        t1 = s([s([m2n, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pc, TM2)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pc, TM2))
        IFC = S2COST
        ifn = s([s([rf['rcn'], w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (pc, RC)),
                 cl.mem('( ( %s + ( 2 x. U ) ) + 2 )' % RC, 'NN0')], 'ifcld', '( %s -> %s e. NN0 )' % (pc, IFC))
        cl.leaf(IFC, 'NN0', ifn)
        VAL = '( %s + 1 )' % RC if fail else '( ( %s + ( 2 x. U ) ) + 2 )' % RC
        ifv = s([c[cnd]], 'iftrued' if fail else 'iffalsed', '( %s -> %s = %s )' % (pc, IFC, VAL))
        h1 = s([ifv], 'oveq1d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (pc, IFC, TM, VAL, TM))
        h2 = s([tme], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( ; 2 7 x. %s ) ) )' % (pc, RC, TM, RC, TM2))
        h3 = s([tme], 'oveq2d', '( %s -> ( U x. %s ) = ( U x. ( ; 2 7 x. %s ) ) )' % (pc, TM, TM2))
        h4 = s([cl.mem(T4, 'RR'), cl.mem(TM2, 'RR'), cl.mem(RC, 'RR'), cl.ge0(RC), m4], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (pc, RC, T4, RC, TM2))
        h5 = s([cl.mem(LEN, 'RR'), cl.mem(RC, 'RR'), cl.mem(TM2, 'RR'), cl.ge0(TM2), rf['lr']], 'lemul1ad',
               '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (pc, LEN, TM2, RC, TM2))
        h6 = s([cl.mem(RC, 'RR'), cl.mem(TM2, 'RR'), cl.ge0(RC), cl.ge0(TM2)], 'mulge0d', '( %s -> 0 <_ ( %s x. %s ) )' % (pc, RC, TM2))
        h7 = s([cl.mem('U', 'RR'), cl.mem(TM2, 'RR'), cl.ge0('U'), cl.ge0(TM2)], 'mulge0d', '( %s -> 0 <_ ( U x. %s ) )' % (pc, TM2))
        BND = '( ( %s + 1 ) x. %s )' % (IFC, TM)
        le = linarith(w, pc, [tme, m4, t1, h1, h2, h3, h4, h5, h6, h7], '%s <_ %s' % (n, BND), closure=cl, products=True)
        outs.append(hrle(w, pc, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le))
    st = s(outs, 'pm2.61dan', '( %s -> %s )' % (ph0, CONCL_S2F))
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
