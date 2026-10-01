"""T8a: moveSlot, copySlot, dropList at the machine (Lean ` moveSlot_runs ` , ` copySlot_runs ` ,
` dropList_correct ` ) on their installation predicates.

  tmimvsu tmicpsu tmidplu tmiwupu tmiwdnu tmietbu   the unfolding theorems
  tmimvs   moveSlot_runs: ~ tm2fmvs once per case of the slot (none: pop and push ket;
           some: ~ tmilrevn twice)
  tmicps   copySlot_runs: ~ tm2fcps (none: push ket; some: ~ tmilcpyn )
  tmidpl   dropList_correct: ~ tm2fdpl , the body ~ tmidrop

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_e_slot.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
from lin import linarith, lineq, nlinarith
from t6blib import _split_top

SEL = sys.argv[1:]
NONE_ = '( inr ` (/) )'
W_ = '( 2nd ` O )'
T1_MVS = '( ( N x. ( ( 4 x. B ) + ; 1 2 ) ) + 8 )'
T1_CPS = '( ( N x. ( ( 6 x. B ) + ; 1 7 ) ) + 9 )'
DF_MVS = UP(UP('D', 'K', 'R'), 'J', CC(ESL('O'), '( D ` J )'))
DF_CPS = UP('D', 'J', CC(ESL('O'), '( D ` J )'))


def disj_leaf(generic, m):
    """the ite disjunction of a generic, substituted, and its two disjuncts"""
    ante, _ = split_imp(stmt(generic))
    found = []
    def go(t):
        if isinstance(t, str):
            if ' \\/ ' in t:
                found.append(t)
            return
        for x in t:
            go(x)
    go(parse_conj(ante))
    assert len(found) == 1, found
    d = tsub_text(found[0], m)
    inner = d.split()[1:-1]
    parts_ = _split_top(inner, '\\/')
    assert len(parts_) == 2
    return d, parts_[0], parts_[1]


def stkcl(w, ph, mk, D, dd, chain, gam):
    """( ph -> chain_text( D , chain ) e. Stk ) by updcl"""
    st, cur = dd, D
    for k, v in chain:
        xk = w.s([gam[v], mk['k'][k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, v, GX(k)))
        st = updcl(w, ph, cur, k, v, mk['tv'], st, mk['k'][k]['kd'], xk)
        cur = UP(cur, k, v)
    return st


def slot_run(lab, fname, generic, TREEX, T1B, DF, dfchain, desc, some_triple, none_disj):
    ps = cj(TREEX)
    w = W(lab, desc)
    lm = FRAGS[fname].lmap()
    cases = []
    for cond in ('O = %s' % NONE_, 'O =/= %s' % NONE_):
        pc = '( %s /\\ %s )' % (ps, cond)
        c, mk, ne, ex = hsetup(w, pc, (TREEX, cond), K4, fname)
        oo, rw, dd = c['O e. %s' % SLOT], c[WRD('R', GAM)], c[STKD('D')]
        dk = c['( D ` K ) = ( %s ++ R )' % ESL('O')]
        cs = w.s([], 'simpr', '( %s -> %s )' % (pc, cond))
        sv = w.s([oo, w.inst('ttabslotv')], 'syl', '( %s -> %s = if ( O = %s , <" 3 "> , ( encList ` %s ) ) )' % (pc, ESL('O'), NONE_, W_))
        cl = Closure(w, pc, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0'])})
        ex['%s e. NN0' % T1B] = cl.mem(T1B, 'NN0')
        lo = '2' if generic == 'tm2fmvs' else '1'
        ex['%s <_ %s' % (lo, T1B)] = nlinarith(w, pc, [cl.ge0('N'), cl.ge0('B')], '%s <_ %s' % (lo, T1B), closure=cl)
        # the final stacks: typing
        ew = w.s([oo, w.s([w.s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi',
                          "( O e. %s -> %s e. Word Gamma' )" % (SLOT, ESL('O')))], 'syl', "( %s -> %s e. Word Gamma' )" % (pc, ESL('O')))
        djg = w.s([stkfv(w, pc, 'D', 'J', mk['tv'], dd, mk['k']['J']['kd']), mk['k']['J']['wge']], 'eleqtrd', "( %s -> ( D ` J ) e. Word Gamma' )" % pc)
        gam = {'R': rw, CC(ESL('O'), '( D ` J )'): w.s([ew, djg, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (pc, CC(ESL('O'), '( D ` J )')))}
        ex[STKD(DF)] = stkcl(w, pc, mk, 'D', dd, dfchain, gam)
        m = dict(lm)
        m.update({'K': 'K', 'J': 'J', 'F': RDK, "F'": PID, 'C': 'TMfl', 'Y': KET, 'D': 'D', "D'": DF, 'T1': T1B, 'N': S, "N'": S})
        if cond.startswith('O = '):
            N1 = NFL('1o')
            it = w.s([cs], 'iftrued', '( %s -> if ( O = %s , <" 3 "> , ( encList ` %s ) ) = <" 3 "> )' % (pc, NONE_, W_))
            e3 = w.s([sv, it], 'eqtrd', '( %s -> %s = <" 3 "> )' % (pc, ESL('O')))
            dk1 = w.s([dk, w.s([e3], 'oveq1d', '( %s -> ( %s ++ R ) = ( <" 3 "> ++ R ) )' % (pc, ESL('O')))], 'eqtrd',
                      '( %s -> ( D ` K ) = ( <" 3 "> ++ R ) )' % pc)
            m.update({'Z': KET, 'X': 'R', 'N1': N1})
            ex['( D ` K ) = ( <" 3 "> ++ R )'] = dk1
            ex[WRD('R', GAM)] = rw
            ifq = w.s([w.s([], 'eqidd', '( %s -> 3 = 3 )' % pc)], 'iftrued', '( %s -> if ( 3 = 3 , 1o , (/) ) = 1o )' % pc)
            ex['A. r e. %s ( %s ` <. r , ( inl ` 3 ) >. ) e. %s' % (S, RDK, N1)] = peek_iface(w, pc, mk, RDK, KET, ex["3 e. Gamma'"], ifq, '1o')
            nss = nfl_ss(w, pc, mk, '1o')
            ex[SSS(N1)] = nss
            d, d1, d2 = disj_leaf(generic, m)
            dj1 = none_disj(w, pc, mk, ex, nss, e3, d1)
            ex[d] = w.s([dj1], 'orcd', '( %s -> %s )' % (pc, d))
        else:
            N1 = NFL('(/)')
            V, ew2, vw, vn0 = slot_word(w, pc, oo, rw)
            eqV, hg, tg = word_split(w, pc, V, vw, vn0)
            Z, X = HD0(V), TL1(V)
            dk2 = w.s([dk, eqV], 'eqtrd', '( %s -> ( D ` K ) = ( <" %s "> ++ %s ) )' % (pc, Z, X))
            m.update({'Z': Z, 'X': X, 'N1': N1})
            ex['( D ` K ) = ( <" %s "> ++ %s )' % (Z, X)] = dk2
            ex["%s e. Gamma'" % Z] = hg
            ex["%s e. Word Gamma'" % X] = tg
            sk = w.s([oo, rw, w.inst('ttabslotk')], 'syl2anc', '( %s -> ( %s = 3 <-> O = %s ) )' % (pc, Z, NONE_))
            nn = w.s([cs], 'neneqd', '( %s -> -. O = %s )' % (pc, NONE_))
            nz = w.s([sk, nn], 'mtbird', '( %s -> -. %s = 3 )' % (pc, Z))
            ifq = w.s([nz], 'iffalsed', '( %s -> if ( %s = 3 , 1o , (/) ) = (/) )' % (pc, Z))
            ex['A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (S, RDK, Z, N1)] = peek_iface(w, pc, mk, RDK, Z, hg, ifq, '(/)')
            nss = nfl_ss(w, pc, mk, '(/)')
            ex[SSS(N1)] = nss
            d, d1, d2 = disj_leaf(generic, m)
            itf = w.s([nn], 'iffalsed', '( %s -> if ( O = %s , <" 3 "> , ( encList ` %s ) ) = ( encList ` %s ) )' % (pc, NONE_, W_, W_))
            enc = w.s([sv, itf], 'eqtrd', '( %s -> %s = ( encList ` %s ) )' % (pc, ESL('O'), W_))
            tri = some_triple(w, pc, c, mk, ne, ex, nss, enc, T1B)
            htf = ht_nfl(w, pc, '(/)')
            dj2 = w.s([htf, tri], 'jca', '( %s -> %s )' % (pc, d2))
            ex[d] = w.s([dj2], 'olcd', '( %s -> %s )' % (pc, d))
        t, cc = inst(w, pc, generic, m, Bld(w, pc, c, ex))
        cases.append((w.s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ps, cond, cc)), cc))
    assert cases[0][1] == cases[1][1]
    cc = cases[0][1]
    t = w.s([cases[0][0], cases[1][0]], 'pm2.61dne', '( %s -> %s )' % (ps, cc))
    return w, ps, t, cc


def slot_bounds(w, pc, c):
    """from SB( O ) and O =/= none : ( # ` W ) <_ N , A. a e. ran W a < ( 2 ^ B ) , W e. Word NN0"""
    sb = c[SB('O')]
    nn = w.s([], 'simpr', '( %s -> O =/= %s )' % (pc, NONE_))
    both = w.s([nn, sb], 'mpd', '( %s -> ( ( # ` %s ) <_ N /\\ A. a e. ran %s a < ( 2 ^ B ) ) )' % (pc, W_, W_))
    le = w.s([both], 'simpld', '( %s -> ( # ` %s ) <_ N )' % (pc, W_))
    ra = w.s([both], 'simprd', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (pc, W_))
    ow = w.s([c['O e. %s' % SLOT], w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, W_))
    return le, ra, ow


def base_stacks(w, ph, mk, ne, dd):
    vals = {s_: selfval(w, ph, mk, 'D', dd, s_) for s_ in K4}
    return Stacks(w, ph, mk, 'D', dd, ne, vals)


# ------------------------------------------------------------ moveSlot
def mvs_none(w, pc, mk, ex, nss, e3, d1):
    ht = ht_nfl(w, pc, '1o')
    pop = pop_iface(w, pc, mk, NFL('1o'), nss, KET, ex["3 e. Gamma'"])
    deq, new = w.rewrite(DF_MVS, {ESL('O'): ('<" 3 ">', e3)}, pc)
    assert new == UP(UP('D', 'K', 'R'), 'J', CC('<" 3 ">', '( D ` J )')), new
    return w.s([ht, pop, deq], '3jca', '( %s -> %s )' % (pc, d1))


def mvs_some(w, pc, c, mk, ne, ex, nss, enc, T1B):
    le, ra, ow = slot_bounds(w, pc, c)
    dd = c[STKD('D')]
    rw = c[WRD('R', GAM)]
    dkl = w.s([c['( D ` K ) = ( %s ++ R )' % ESL('O')], w.s([enc], 'oveq1d', '( %s -> ( %s ++ R ) = ( ( encList ` %s ) ++ R ) )' % (pc, ESL('O'), W_))],
              'eqtrd', '( %s -> ( D ` K ) = ( ( encList ` %s ) ++ R ) )' % (pc, W_))
    S0 = base_stacks(w, pc, mk, ne, dd)
    run = Run(w, pc, mk, S0, ex, c)
    RW = '( reverse ` %s )' % W_
    rvw = w.s([ow, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, RW))
    erv = w.s([rvw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pc, RW))
    dI = S0.vals["I'"]
    REVE = CC('( encList ` %s )' % RW, "( D ` I' )")
    reveg = w.s([erv, dI[2], w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (pc, REVE))
    run.call('tmilrevn', {'K': 'K', 'J': "I'", 'I': 'I', 'P': PL('P', 4), 'E': PL(PL('P', 5), 0), 'L': W_, 'R': 'R', 'B': 'B'},
             {'( D ` K ) = ( ( encList ` %s ) ++ R )' % W_: dkl, '%s e. Word NN0' % W_: ow, 'A. a e. ran %s a < ( 2 ^ B )' % W_: ra},
             [('K', 'R', rw), ("I'", REVE, reveg)], pre=(NFL('(/)'), nss))
    rs = w.s([ow, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran %s )' % (pc, RW, W_))
    rar = w.s([rs, ra, w.inst('ssralv')], 'sylc', '( %s -> A. a e. ran %s a < ( 2 ^ B ) )' % (pc, RW))
    S1 = run.S
    RRW = '( reverse ` %s )' % RW
    err = w.s([w.s([rvw, w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, RRW)), w.inst('tm2lenccl')], 'syl',
              "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pc, RRW))
    V2 = CC('( encList ` %s )' % RRW, '( D ` J )')
    g2 = w.s([err, S0.vals['J'][2], w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (pc, V2))
    run.call('tmilrevn', {'K': "I'", 'J': 'J', 'I': 'I', 'P': PL('P', 5), 'E': 'E', 'L': RW, 'R': "( D ` I' )", 'B': 'B'},
             {"( %s ` I' ) = ( ( encList ` %s ) ++ ( D ` I' ) )" % (S1.D, RW): S1.vals["I'"][1], '%s e. Word NN0' % RW: rvw,
              'A. a e. ran %s a < ( 2 ^ B )' % RW: rar, "( D ` I' ) e. Word Gamma'": dI[2]},
             [("I'", "( D ` I' )", dI[2]), ('J', V2, g2)])
    cur, out = run.normalize(K4)
    assert out == [('K', 'R'), ('J', V2)], out
    rr = w.s([ow, w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (pc, RRW, W_))
    e1 = w.s([rr], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` %s ) )' % (pc, RRW, W_))
    e2 = w.s([e1, enc], 'eqtr4d', '( %s -> ( encList ` %s ) = %s )' % (pc, RRW, ESL('O')))
    DN = UP(UP('D', 'K', 'R'), 'J', V2)
    deq, new = w.rewrite(DN, {'( encList ` %s )' % RRW: (ESL('O'), e2)}, pc)
    assert new == DF_MVS, new
    d = clneq(w, pc, 'E', S, deq, DN, DF_MVS)
    t2, C2, D2, n2 = hrrw(w, pc, run.tri, run.C0, run.cur, run.n, deq=d)
    # the bound
    cl = Closure(w, pc, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0'])})
    lw = w.s([ow, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, W_))
    cl.leaf('( # ` %s )' % W_, 'NN0', lw)
    rl = w.s([ow, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (pc, RW, W_))
    cl.leaf('( # ` %s )' % RW, 'NN0', w.s([rvw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, RW)))
    lr1 = w.s([rl], 'eqcomd', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (pc, W_, RW))
    rle = w.s([w.s([rl], 'eqcomd', '') if False else rl, le], 'eqbrtrd', '( %s -> ( # ` %s ) <_ N )' % (pc, RW))
    lt = nlinarith(w, pc, [le, rle, cl.ge0('B')], '%s <_ %s' % (n2, T1B), closure=cl)
    return hrle(w, pc, mk['phm'], t2, C2, D2, n2, T1B, cl.mem(T1B, 'NN0'), lt)


def tmimvs():
    w, ps, t, cc = slot_run('tmimvs', 'mvs', 'tm2fmvs', TREE_MVS, T1_MVS, DF_MVS, [('K', 'R'), ('J', CC(ESL('O'), '( D ` J )'))],
                            'Lean\'s ` moveSlot_runs ` at the machine: wherever ` moveSlot src dst s s\' ` is installed, the top '
                            'slot ` O ` of ` src ` (at most ` N ` entries below ` 2 ^ B ` ) moves onto ` dst ` exactly, every other '
                            'stack restored, within ` slotC N b = N ( 4 b + 12 ) + 10 ` steps (~ tm2fmvs ; an empty slot is '
                            'popped and ` ket ` pushed, a witness list is reversed onto ` s\' ` and back, ~ tmilrevn ).',
                            mvs_some, mvs_none)
    C, D, n = triple_parts(cc)
    cl = Closure(w, ps, {'N': ('NN0', Ctx(w, ps, TREE_MVS)['N e. NN0']), 'B': ('NN0', Ctx(w, ps, TREE_MVS)['B e. NN0'])})
    neq = lineq(w, ps, n, SLOTC, closure=cl)
    hrrw(w, ps, t, C, D, n, neq=neq, qed=True)
    return w.run()


# ------------------------------------------------------------ copySlot
def cps_none(w, pc, mk, ex, nss, e3, d1):
    ht = ht_nfl(w, pc, '1o')
    deq, new = w.rewrite(DF_CPS, {ESL('O'): ('<" 3 ">', e3)}, pc)
    assert new == UP('D', 'J', CC('<" 3 ">', '( D ` J )')), new
    return w.s([ht, nss, deq], '3jca', '( %s -> %s )' % (pc, d1))


def cps_some(w, pc, c, mk, ne, ex, nss, enc, T1B):
    le, ra, ow = slot_bounds(w, pc, c)
    dd = c[STKD('D')]
    rw = c[WRD('R', GAM)]
    dkl = w.s([c['( D ` K ) = ( %s ++ R )' % ESL('O')], w.s([enc], 'oveq1d', '( %s -> ( %s ++ R ) = ( ( encList ` %s ) ++ R ) )' % (pc, ESL('O'), W_))],
              'eqtrd', '( %s -> ( D ` K ) = ( ( encList ` %s ) ++ R ) )' % (pc, W_))
    S0 = base_stacks(w, pc, mk, ne, dd)
    run = Run(w, pc, mk, S0, ex, c)
    ew = w.s([ow, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pc, W_))
    V2 = CC('( encList ` %s )' % W_, '( D ` J )')
    g2 = w.s([ew, S0.vals['J'][2], w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (pc, V2))
    run.call('tmilcpyn', {'K': 'K', 'J': 'J', 'I': 'I', "I'": "I'", 'P': PL('P', 3), 'E': 'E', 'L': W_, 'R': 'R', 'B': 'B'},
             {'( D ` K ) = ( ( encList ` %s ) ++ R )' % W_: dkl, '%s e. Word NN0' % W_: ow, 'A. a e. ran %s a < ( 2 ^ B )' % W_: ra},
             [('J', V2, g2)], pre=(NFL('(/)'), nss))
    DN = UP('D', 'J', V2)
    e2 = w.s([enc], 'eqcomd', '( %s -> ( encList ` %s ) = %s )' % (pc, W_, ESL('O')))
    deq, new = w.rewrite(DN, {'( encList ` %s )' % W_: (ESL('O'), e2)}, pc)
    assert new == DF_CPS, new
    d = clneq(w, pc, 'E', S, deq, DN, DF_CPS)
    t2, C2, D2, n2 = hrrw(w, pc, run.tri, run.C0, run.cur, run.n, deq=d)
    cl = Closure(w, pc, {'N': ('NN0', c['N e. NN0']), 'B': ('NN0', c['B e. NN0'])})
    lw = w.s([ow, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, W_))
    cl.leaf('( # ` %s )' % W_, 'NN0', lw)
    lt = nlinarith(w, pc, [le, cl.ge0('B')], '%s <_ %s' % (n2, T1B), closure=cl)
    return hrle(w, pc, mk['phm'], t2, C2, D2, n2, T1B, cl.mem(T1B, 'NN0'), lt)


def tmicps():
    w, ps, t, cc = slot_run('tmicps', 'cps', 'tm2fcps', TREE_CPS, T1_CPS, DF_CPS, [('J', CC(ESL('O'), '( D ` J )'))],
                            'Lean\'s ` copySlot_runs ` at the machine: wherever ` copySlot src dst s s\' ` is installed, a copy '
                            'of the top slot ` O ` of ` src ` is pushed on ` dst ` , every other stack restored, within '
                            '` N ( 6 b + 17 ) + 11 ` steps (~ tm2fcps ; ` ket ` pushed for an empty slot, ~ tmilcpyn for a list).',
                            cps_some, cps_none)
    C, D, n = triple_parts(cc)
    cc_ = Ctx(w, ps, TREE_CPS)
    cl = Closure(w, ps, {'N': ('NN0', cc_['N e. NN0']), 'B': ('NN0', cc_['B e. NN0'])})
    neq = lineq(w, ps, n, CPSC, closure=cl)
    hrrw(w, ps, t, C, D, n, neq=neq, qed=True)
    return w.run()


# ------------------------------------------------------------ dropList
LB = '( encNatGam o. L )'
PFY = lambda t: UP('D', 'K', CC('( encListB ` %s )' % DROP(LB, t), 'R'))
PFD = '( y e. ( 0 ... ( # ` %s ) ) |-> %s )' % (LB, PFY('y'))


def setup1(w, ph, T, fname):
    """setup for a one-stack fragment (no distinctness)"""
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, ['K'])
    base = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], 'K e. %s' % DG: mk['k']['K']['kd']}
    base.update(unfold_all(w, ph, c[FRAGS[fname].pred()], fname, ['K'], 'P', 'E', rec=False))
    f = FRAGS[fname]
    lm = f.lmap()
    for j, (fn, cks, en, exn) in enumerate(f.children):
        P_ = PL('P', f.slot(j))
        pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
        base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
    ex = dict(base)
    ex.update(H.handler_extra(w, ph, mk, H.IFACE))
    ex[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    return c, mk, ex


def pfval(w, ph, t, tfz, lbw, rw, mk, dd):
    """( ph -> ( PFD ` t ) = PFY( t ) ) and the typing of the pushed word"""
    X_of = lambda s: PFY(s)
    EB = '( encListB ` %s )' % DROP(LB, t)
    ebw = w.s([w.s([lbw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word Word ( { 1 } X. 2o ) )' % (ph, DROP(LB, t))), w.inst('tm2lencbcl')],
              'syl', "( %s -> %s e. Word Gamma' )" % (ph, EB))
    vg = w.s([ebw, rw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, CC(EB, 'R')))
    xk = w.s([vg, mk['k']['K']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, CC(EB, 'R'), GX('K')))
    st = updcl(w, ph, 'D', 'K', CC(EB, 'R'), mk['tv'], dd, mk['k']['K']['kd'], xk)
    v = mval(w, ph, 'y', '( 0 ... ( # ` %s ) )' % LB, X_of, t, tfz, w.s([st], 'elexd', '( %s -> %s e. _V )' % (ph, PFY(t))))
    return v, st, vg


def tmidpl():
    lab = 'tmidpl'
    ps = cj(TREE_DPL)
    w = W(lab, 'Lean\'s ` dropList_correct ` at the machine: wherever ` dropList x ` is installed, the list of numbers '
               'below ` 2 ^ B ` on ` x ` is popped, every other stack kept, within ` L.length ( b + 3 ) + 3 ` steps '
               '(~ tm2fdpl , the body ` dropNum x ` by ~ tmidrop ).')
    c, mk, ex = setup1(w, ps, TREE_DPL, 'dpl')
    dd, rw = c[STKD('D')], c[WRD('R', GAM)]
    lw, bb, ha = c['L e. Word NN0'], c['B e. NN0'], c['A. a e. ran L a < ( 2 ^ B )']
    lbw = w.s([lw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word ( { 1 } X. 2o ) )' % (ps, LB))
    ex['%s e. Word Word ( { 1 } X. 2o )' % LB] = lbw
    cl = Closure(w, ps, {'B': ('NN0', bb)})
    ex['( B + 1 ) e. NN0'] = cl.mem('( B + 1 )', 'NN0')
    # the pop interface on the exit class
    SQ = '{ q e. %s | -. ( %s ` q ) = 1o }' % (S, CNFL)
    ssq = closed(w, ps, 'ssrab2', '%s C_ %s' % (SQ, S))
    ex['A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (SQ, PID, S)] = w.s([ssq, ex[H.POPI], w.inst('ssralv')], 'sylc',
                                                                               '( %s -> A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s )' % (ps, SQ, PID, S))
    # the family: typing
    NL = '( # ` %s )' % LB
    ay = '( %s /\\ y e. ( 0 ... %s ) )' % (ps, NL)
    Ly = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (ay, concl(w, ps, st)))
    EBy = '( encListB ` %s )' % DROP(LB, 'y')
    eby = w.s([w.s([Ly(lbw), w.inst('swrdcl')], 'syl', '( %s -> %s e. Word Word ( { 1 } X. 2o ) )' % (ay, DROP(LB, 'y'))), w.inst('tm2lencbcl')],
              'syl', "( %s -> %s e. Word Gamma' )" % (ay, EBy))
    vgy = w.s([eby, Ly(rw), w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ay, CC(EBy, 'R')))
    xky = w.s([vgy, Ly(mk['k']['K']['wge'])], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ay, CC(EBy, 'R'), GX('K')))
    sty = updcl(w, ay, 'D', 'K', CC(EBy, 'R'), Ly(mk['tv']), Ly(dd), Ly(mk['k']['K']['kd']), xky)
    ex['%s : ( 0 ... %s ) --> %s' % (PFD, NL, STK_T)] = w.s([sty, w.s([], 'eqid', '%s = %s' % (PFD, PFD))], 'fmptd',
                                                             '( %s -> %s : ( 0 ... %s ) --> %s )' % (ps, PFD, NL, STK_T))
    # the family: the stack K
    aj = '( %s /\\ j e. ( 0 ... %s ) )' % (ps, NL)
    Lj = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (aj, concl(w, ps, st)))
    jfz = w.s([], 'simpr', '( %s -> j e. ( 0 ... %s ) )' % (aj, NL))
    vj, stj, vgj = pfval(w, aj, 'j', jfz, Lj(lbw), Lj(rw), {'k': {'K': {k2: Lj(v2) for k2, v2 in mk['k']['K'].items() if k2 in ('kd', 'wge')}},
                                                            'tv': Lj(mk['tv'])}, Lj(dd))
    EBj = '( encListB ` %s )' % DROP(LB, 'j')
    kv = w.s([w.s([vj], 'fveq1d', '( %s -> ( ( %s ` j ) ` K ) = ( %s ` K ) )' % (aj, PFD, PFY('j'))),
              updkv(w, aj, 'D', 'K', CC(EBj, 'R'), Lj(mk['tv']), Lj(dd), Lj(mk['k']['K']['kd']), w.s([vgj], 'elexd', '( %s -> %s e. _V )' % (aj, CC(EBj, 'R'))))],
             'eqtrd', '( %s -> ( ( %s ` j ) ` K ) = %s )' % (aj, PFD, CC(EBj, 'R')))
    ex['A. j e. ( 0 ... %s ) ( ( %s ` j ) ` K ) = %s' % (NL, PFD, CC(EBj, 'R'))] = w.s([kv], 'ralrimiva',
                                                                                    '( %s -> A. j e. ( 0 ... %s ) ( ( %s ` j ) ` K ) = %s )' % (ps, NL, PFD, CC(EBj, 'R')))
    # the body
    ab = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ps, NL)
    Lb = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (ab, concl(w, ps, st)))
    jo = w.s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (ab, NL))
    jfz2 = w.s([jo, w.inst('elfzofz')], 'syl', '( %s -> j e. ( 0 ... %s ) )' % (ab, NL))
    j1fz = w.s([jo, w.inst('fzofzp1')], 'syl', '( %s -> ( j + 1 ) e. ( 0 ... %s ) )' % (ab, NL))
    mkb = {'k': {'K': {'kd': Lb(mk['k']['K']['kd']), 'wge': Lb(mk['k']['K']['wge'])}}, 'tv': Lb(mk['tv'])}
    v0, _, _ = pfval(w, ab, 'j', jfz2, Lb(lbw), Lb(rw), mkb, Lb(dd))
    v1, _, vg1 = pfval(w, ab, '( j + 1 )', j1fz, Lb(lbw), Lb(rw), mkb, Lb(dd))
    Wj = '( %s ` j )' % LB
    X1 = CC('( encListB ` %s )' % DROP(LB, '( j + 1 )'), 'R')
    wj = w.s([Lb(lbw), jo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. Word ( { 1 } X. 2o ) )' % (ab, Wj))
    bd = w.s([Lb(lbw), jo, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> ( encListB ` %s ) = ( %s ++ ( <" 4 "> ++ ( encListB ` %s ) ) ) )'
             % (ab, DROP(LB, 'j'), Wj, DROP(LB, '( j + 1 )')))
    wjg = w.s([wj, w.s([], 'tm2lwbss', "Word ( { 1 } X. 2o ) C_ Word Gamma'")], 'sselid' if False else 'id', '') if False else \
        w.s([w.s([], 'tm2lwbss', "Word ( { 1 } X. 2o ) C_ Word Gamma'"), wj], 'sseldi' if False else 'sselid', "( %s -> %s e. Word Gamma' )" % (ab, Wj))
    E1 = '( encListB ` %s )' % DROP(LB, '( j + 1 )')
    e1w = w.s([w.s([Lb(lbw), w.inst('swrdcl')], 'syl', '( %s -> %s e. Word Word ( { 1 } X. 2o ) )' % (ab, DROP(LB, '( j + 1 )'))), w.inst('tm2lencbcl')],
              'syl', "( %s -> %s e. Word Gamma' )" % (ab, E1))
    g4 = closed(w, ab, 'gamma4', "4 e. Gamma'")
    s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ab)
    s4e = w.s([s4, e1w, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ %s ) e. Word Gamma' )" % (ab, E1))
    a1 = w.s([bd], 'oveq1d', '( %s -> ( ( encListB ` %s ) ++ R ) = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ R ) )' % (ab, DROP(LB, 'j'), Wj, E1))
    a2 = w.s([wjg, s4e, Lb(rw), w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ R ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )'
             % (ab, Wj, E1, Wj, E1))
    a3 = w.s([s4, e1w, Lb(rw), w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ R ) = ( <" 4 "> ++ %s ) )' % (ab, E1, X1))
    a4 = w.s([a3], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ R ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (ab, Wj, E1, Wj, X1))
    WX = CC(Wj, '( <" 4 "> ++ %s )' % X1)
    aa = w.s([w.s([a1, a2], 'eqtrd', '( %s -> ( ( encListB ` %s ) ++ R ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ R ) ) )' % (ab, DROP(LB, 'j'), Wj, E1)), a4],
             'eqtrd', '( %s -> ( ( encListB ` %s ) ++ R ) = %s )' % (ab, DROP(LB, 'j'), WX))
    ue = upeq(w, ab, 'D', 'K', aa, CC('( encListB ` %s )' % DROP(LB, 'j'), 'R'), WX)
    pj = w.s([v0, ue], 'eqtrd', '( %s -> ( %s ` j ) = %s )' % (ab, PFD, UP('D', 'K', WX)))
    DPRED = 'TMIdrop K T M %s %s' % (PL('P', 4), PL('P', 2))
    exb = {DPRED: Lb(ex[DPRED]), "%s e. Word Gamma'" % X1: vg1, '%s e. Word ( { 1 } X. 2o )' % Wj: wj}
    cb = Ctx(w, ab, (TREE_DPL, 'j e. ( 0 ..^ %s )' % NL))
    t, cc = inst(w, ab, 'tmidrop', {'K': 'K', 'P': PL('P', 4), 'E': PL('P', 2), 'D': 'D', 'X': X1, 'W': Wj}, Bld(w, ab, cb, exb))
    Ca, Da, na = triple_parts(cc)
    A0 = PL(PL('P', 4), 0)
    ceq = clneq(w, ab, A0, S, w.s([pj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (ab, UP('D', 'K', WX), PFD)), UP('D', 'K', WX), '( %s ` j )' % PFD)
    deq = clneq(w, ab, PL('P', 2), S, w.s([v1], 'eqcomd', '( %s -> %s = ( %s ` ( j + 1 ) ) )' % (ab, UP('D', 'K', X1), PFD)),
                UP('D', 'K', X1), '( %s ` ( j + 1 ) )' % PFD)
    t2, C2, D2, n2 = hrrw(w, ab, t, Ca, Da, na, ceq=ceq, deq=deq)
    # # W <_ B
    rn = w.s([Lb(lw), Lb(bb), Lb(ha), w.inst('tm2lrnenc')], 'syl3anc', '( %s -> A. w e. ran %s ( # ` w ) <_ B )' % (ab, LB))
    wr = w.s([Lb(lbw), jo, w.inst('algranfv')], 'syl2anc', '( %s -> %s e. ran %s )' % (ab, Wj, LB))
    idw = w.s([], 'id', '( w = %s -> w = %s )' % (Wj, Wj))
    cg, new = w.wcongr('( # ` w ) <_ B', {'w': Wj}, 'w = %s' % Wj, {'w': idw})
    rsp = w.s([cg], 'rspcv', '( %s e. ran %s -> ( A. w e. ran %s ( # ` w ) <_ B -> ( # ` %s ) <_ B ) )' % (Wj, LB, LB, Wj))
    wle = w.s([wr, rn, rsp], 'sylc', '( %s -> ( # ` %s ) <_ B )' % (ab, Wj))
    clb = Closure(w, ab, {'B': ('NN0', Lb(bb))})
    clb.leaf('( # ` %s )' % Wj, 'NN0', w.s([wj, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ab, Wj)))
    le = linarith(w, ab, [wle], '%s <_ ( B + 1 )' % n2, closure=clb)
    t3 = hrle(w, ab, Lb(mk['phm']), t2, C2, D2, n2, '( B + 1 )', clb.mem('( B + 1 )', 'NN0'), le)
    BODY = TRI(CLN(A0, S, '( %s ` j )' % PFD), CLN(PL('P', 2), S, '( %s ` ( j + 1 ) )' % PFD), '( B + 1 )')
    ex['A. j e. ( 0 ..^ %s ) %s' % (NL, BODY)] = w.s([t3], 'ralrimiva', '( %s -> A. j e. ( 0 ..^ %s ) %s )' % (ps, NL, BODY))
    # instantiate tm2fdpl
    m = dict(FRAGS['dpl'].lmap())
    m.update({'K': 'K', 'F': 'TMrdBra', 'C': CNFL, 'F"': PID, 'N': S, "N'": S, 'L': LB, 'R': 'R', 'Y': '( B + 1 )', 'P': PFD})
    t, cc = inst(w, ps, 'tm2fdpl', m, Bld(w, ps, c, ex))
    Ca, Da, na = triple_parts(cc)
    # ( PFD ` 0 ) = D
    nl = w.s([lbw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NL))
    z0 = w.s([nl, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ps, NL))
    mk0 = {'k': {'K': {'kd': mk['k']['K']['kd'], 'wge': mk['k']['K']['wge']}}, 'tv': mk['tv']}
    p0, _, _ = pfval(w, ps, '0', z0, lbw, rw, mk0, dd)
    d0 = w.s([lbw, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = %s )' % (ps, DROP(LB, '0'), LB))
    eq = w.s([lw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` L ) = ( encListB ` %s ) )' % (ps, LB))
    e0 = w.s([w.s([d0], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` %s ) )' % (ps, DROP(LB, '0'), LB)), eq], 'eqtr4d',
             '( %s -> ( encListB ` %s ) = ( encList ` L ) )' % (ps, DROP(LB, '0')))
    e1 = w.s([e0], 'oveq1d', '( %s -> ( ( encListB ` %s ) ++ R ) = ( ( encList ` L ) ++ R ) )' % (ps, DROP(LB, '0')))
    dk = c['( D ` K ) = ( ( encList ` L ) ++ R )']
    e2 = w.s([e1, dk], 'eqtr4d', '( %s -> ( ( encListB ` %s ) ++ R ) = ( D ` K ) )' % (ps, DROP(LB, '0')))
    u0 = upidv(w, ps, 'D', 'K', CC('( encListB ` %s )' % DROP(LB, '0'), 'R'), w.s([e2], 'eqcomd', '( %s -> ( D ` K ) = %s )' % (ps, CC('( encListB ` %s )' % DROP(LB, '0'), 'R'))),
               mk['tv'], dd, mk['k']['K']['kd'])
    pd = w.s([p0, u0], 'eqtrd', '( %s -> ( %s ` 0 ) = D )' % (ps, PFD))
    ceq = clneq(w, ps, PL('P', 0), S, pd, '( %s ` 0 )' % PFD, 'D')
    # UPD( ( PFD ` # LB ) , K , R ) = UPD( D , K , R )
    nfz = w.s([nl, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ps, NL, NL))
    pn, _, vgn = pfval(w, ps, NL, nfz, lbw, rw, mk0, dd)
    QN = CC('( encListB ` %s )' % DROP(LB, NL), 'R')
    r1, x1 = w.rewrite(UP('( %s ` %s )' % (PFD, NL), 'K', 'R'), {'( %s ` %s )' % (PFD, NL): (UP('D', 'K', QN), pn)}, ps)
    togk = lambda X, g: w.s([g, mk['k']['K']['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX('K')))
    u2 = up2(w, ps, 'D', 'K', QN, 'R', mk['tv'], dd, mk['k']['K']['kd'], togk(QN, vgn), togk('R', rw))
    fe = w.s([r1, u2], 'eqtrd', '( %s -> %s = %s )' % (ps, UP('( %s ` %s )' % (PFD, NL), 'K', 'R'), UP('D', 'K', 'R')))
    deq = clneq(w, ps, 'E', S, fe, UP('( %s ` %s )' % (PFD, NL), 'K', 'R'), UP('D', 'K', 'R'))
    ln = w.s([lw, w.s([w.s([], 'tm2lbitf', 'encNatGam : NN0 --> Word ( { 1 } X. 2o )')], 'a1i', '( %s -> encNatGam : NN0 --> Word ( { 1 } X. 2o ) )' % ps),
              w.inst('lenco')], 'syl2anc', '( %s -> %s = ( # ` L ) )' % (ps, NL))
    cl.leaf(NL, 'NN0', nl)
    cl.leaf('( # ` L )', 'NN0', w.s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ps))
    n1eq, na1 = w.rewrite(na, {NL: ('( # ` L )', ln)}, ps)
    n2eq = lineq(w, ps, na1, '( ( ( # ` L ) x. ( B + 3 ) ) + 3 )', closure=cl, products=True)
    neq = w.s([n1eq, n2eq], 'eqtrd', '( %s -> %s = ( ( ( # ` L ) x. ( B + 3 ) ) + 3 ) )' % (ps, na))
    hrrw(w, ps, t, Ca, Da, na, ceq=ceq, deq=deq, neq=neq, qed=True)
    return w.run()


def unf(name):
    import t7b_b_unf as UF
    return UF.unf(name)


if __name__ == '__main__':
    for l in SEL:
        if l.startswith('tmi') and l.endswith('u') and l[3:-1] in PREDS:
            unf(l[3:-1])
        else:
            globals()[l]()
