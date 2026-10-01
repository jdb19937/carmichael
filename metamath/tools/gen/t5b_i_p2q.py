"""T5b: the loop of `pow2` (TM/Prims.lean) from its test label, the exit and
` dropNum x ` (~ tm2fp2q ): ~ tm2hitr over ` ( 0 ..^ R ) ` with ~ tm2fp2k at each
iteration (the four updates of the stacks collapsed by ~ tm2stkup4 ), then
~ tm2fbrg (the test fails) and ~ tm2fdrop .  Lean: ` Frag.loop_runs ` with
` P2Inv ` and stage 5 of ` pow2_correct ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_b_iter import brstep
from t5b_c_blk import leafsteps

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

IFP = '( j e. NN0 |-> %s )' % CLN('A', NF('j'), DP2('j'))
BODYP = CLN('A', NF('j'), DP2('j'))


def dp2facts(w, ph, X, tv, dd, kk, jj, nkj, xw, hw):
    a = updcl(w, ph, 'D', 'K', XF(X), tv, dd, kk, xw)
    d = updcl(w, ph, UP('D', 'K', XF(X)), 'J', HF(X), tv, a, jj, hw)
    xv, hv = elv(w, ph, xw, XF(X)), elv(w, ph, hw, HF(X))
    vk1 = updnv(w, ph, UP('D', 'K', XF(X)), 'J', HF(X), 'K', tv, a, jj, hv, kk, nkj)
    vk2 = updkv(w, ph, 'D', 'K', XF(X), tv, dd, kk, xv)
    vk = w.s([vk1, vk2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, DP2(X), XF(X)))
    vj = updkv(w, ph, UP('D', 'K', XF(X)), 'J', HF(X), tv, a, jj, hv)
    return d, vk, vj


def tm2fp2q():
    lab = 'tm2fp2q'
    tree, ph = TREE_P2Q, cj(TREE_P2Q)
    w = W(lab, 'The loop of ` pow2 ` (TM/Prims.lean) from its test label ` A ` , its exit '
               'and the final ` dropNum ` : ` R ` iterations of ~ tm2fp2k decrement the '
               'exponent on stack ` K ` and push a zero on ` J ` each, the families '
               '` ( X ` i ) ` , ` ( H ` i ) ` , ` ( N ` i ) ` giving the stacks and the state '
               'class after ` i ` iterations (blueprint D3, D4); the test then fails '
               '(~ tm2fbrg , T7: the exponent is zero) and the zero is dropped from ` K ` '
               '(~ tm2fdrop ).  Lean: ` Frag.loop_runs ` at ` P2Inv ` and stage 5 of '
               '` pow2_correct ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, a1, el, e1l = c[LAB('A')], c[LAB("A'")], c[LAB('E')], c[LAB('E1')]
    kk, jj = c['K e. %s' % DG], c['J e. %s' % DG]
    nkj = c['K =/= J']
    c0 = c[CTY('C0')]
    g2, d2 = c[RTY('G"', 'K')], c[CTY('D"')]
    bppk, yk, z1j, xpw2 = c['B" C_ %s' % GK], c['Y e. %s' % GK], c['Z1 e. %s' % GJ], c[WRD('X"', GK)]
    dd, init, rr, tt = c[STKD('D')], c[INIT_P], c['R e. NN0'], c["T' e. NN0"]
    hcdr, hedr = c[HCDR], c[HEDR]
    fam, hyps, fin = c[FAM_P], c[HYPS_P], c[FIN_P]
    meqA, meqE = c[MEQ('A', STM_TE)], c[MEQ('E', STM_DR)]
    x0e, h0e = w.s([init], 'simpld', '( %s -> %s )' % (ph, INIT_P_TREE[0])), w.s([init], 'simprd', '( %s -> %s )' % (ph, INIT_P_TREE[1]))
    xRe, htf = w.s([fin], 'simpld', '( %s -> %s )' % (ph, FIN_P_TREE[0])), w.s([fin], 'simprd', '( %s -> %s )' % (ph, FIN_P_TREE[1]))
    ge, ga1 = gotocl(w, ph, tv, 'E', el), gotocl(w, ph, tv, "A'", a1)
    T2 = "( T' + 2 )"
    rnn = w.s([rr, w.inst('nn0red')], 'syl', '( %s -> R e. RR )' % ph)

    def famat(ph2, X, xfz, Lf):
        st, _ = inst_v(w, ph2, Lf(fam, FAM_P), cj(FAMB_P('i')), 'i', X, xfz)
        cx = Ctx(w, ph2, FAMB_P(X), root=st)
        return dict(xw=cx[WRD(XF(X), GK)], hw=cx[WRD(HF(X), GJ)], nss=cx[SSS(NF(X))], wpw=cx[WRD(WPF(X), 'B"')])

    def L_(ph2, st, f):
        return st if ph2 == ph else w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))

    def fzmem(ph2, X, xnn, xle):
        return w.s([w.s([xnn, L_(ph2, rr, 'R e. NN0'), xle], '3jca', '( %s -> ( %s e. NN0 /\\ R e. NN0 /\\ %s <_ R ) )' % (ph2, X, X)),
                    w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... R ) )' % (ph2, X))

    # ---------------- the iteration at k
    pk = '( %s /\\ k e. ( 0 ..^ R ) )' % ph
    Lk = Lifter(w, pk)
    kin = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ R ) )' % pk)
    kfz = w.s([kin, w.inst('elfzofz')], 'syl', '( %s -> k e. ( 0 ... R ) )' % pk)
    k1fz = w.s([kin, w.inst('fzofzp1')], 'syl', '( %s -> ( k + 1 ) e. ( 0 ... R ) )' % pk)
    knn = w.s([kin, w.inst('elfzonn0')], 'syl', '( %s -> k e. NN0 )' % pk)
    k1nn = w.s([knn, w.inst('peano2nn0')], 'syl', '( %s -> ( k + 1 ) e. NN0 )' % pk)
    fk = famat(pk, 'k', kfz, Lk)
    fk1 = famat(pk, '( k + 1 )', k1fz, Lk)
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS_P), HYP_P('i'), 'i', 'k', kin)
    ck = Ctx(w, pk, HYP_P_TREE('k'), root=hyk)
    K1 = '( k + 1 )'
    tvk, ddk, kkk, jjk, nkjk = Lk(tv, 'T e. V'), Lk(dd, STKD('D')), Lk(kk, 'K e. %s' % DG), Lk(jj, 'J e. %s' % DG), Lk(nkj, 'K =/= J')
    dpk, vk, vj = dp2facts(w, pk, 'k', tvk, ddk, kkk, jjk, nkjk, fk['xw'], fk['hw'])
    CHAIN = CC(WF('k'), CC(S1(ZF('k')), XPF('k')))
    xeq1 = ck['%s = %s' % (XF('k'), CHAIN)]
    heq = ck['%s = %s' % (HF(K1), CC(S1('Z1'), HF('k')))]
    dpkK = w.s([vk, xeq1], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (pk, DP2('k'), CHAIN))
    MAPK = {'N': NF('k'), "N'": NF(K1), 'D': DP2('k'), 'W': WF('k'), 'Z': ZF('k'), 'X': XPF('k'), "Z'": ZPF('k'),
            "X'": UPF('k'), 'Z0': Z0F('k'), 'X0': XF(K1), "W'": WPF(K1), 'Q': GT('E')}
    instk = ren(TREE_P2K, MAPK)
    assert sub(DISJ_PRD1, MAPK) == DISJ_P('k')
    derived = {STKD(DP2('k')): dpk, '( %s ` K ) = %s' % (DP2('k'), CHAIN): dpkK,
               SSS(NF('k')): fk['nss'], SSS(NF(K1)): fk1['nss'], WRD(WPF(K1), 'B"'): fk1['wpw'],
               STMT(GT('E')): Lk(ge, STMT(GT('E')))}
    for t in flat(HYP_P_TREE('k')):
        derived.setdefault(t, ck[t])
    def look(t):
        if t in derived:
            return derived[t]
        return Lk(c[t], t)
    POSTK = sub(D2_P2, MAPK)
    trik = applylem(w, pk, 'tm2fp2k', leafsteps(instk, look), TRI(CLN('A', NF('k'), DP2('k')), CLN('A', NF(K1), POSTK), T2))
    heqc = w.s([heq], 'eqcomd', '( %s -> %s = %s )' % (pk, CC(S1('Z1'), HF('k')), HF(K1)))
    col = up4(w, pk, 'D', 'K', XF('k'), 'J', HF('k'), XF(K1), HF(K1), tvk, ddk, nkjk, kkk, fk['xw'], fk1['xw'], jjk, fk['hw'], fk1['hw'])
    tbl = {'( %s ` J )' % DP2('k'): (HF('k'), vj), CC(S1('Z1'), HF('k')): (HF(K1), heqc),
           UP(UP(DP2('k'), 'K', XF(K1)), 'J', HF(K1)): (DP2(K1), col)}
    ps, postn = evaluate(w, pk, POSTK, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert postn == DP2(K1), postn
    trik2, _, _, _ = hrrw(w, pk, trik, CLN('A', NF('k'), DP2('k')), CLN('A', NF(K1), POSTK), T2,
                          deq=clneq(w, pk, 'A', NF(K1), ps, POSTK, DP2(K1)))
    CLk, CLk1 = CLN('A', NF('k'), DP2('k')), CLN('A', NF(K1), DP2(K1))
    jvk = ifval(w, pk, IFP, BODYP, 'k', knn, CLk, clnex(w, pk, 'A', NF('k'), DP2('k')))
    jvk1 = ifval(w, pk, IFP, BODYP, K1, k1nn, CLk1, clnex(w, pk, 'A', NF(K1), DP2(K1)))
    trik3, _, _, _ = hrrw(w, pk, trik2, CLk, CLk1, T2,
                          ceq=w.s([jvk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (pk, CLk, IFP)),
                          deq=w.s([jvk1], 'eqcomd', '( %s -> %s = ( %s ` ( k + 1 ) ) )' % (pk, CLk1, IFP)))
    HYPI = 'A. k e. ( 0 ..^ R ) %s' % TRI('( %s ` k )' % IFP, '( %s ` ( k + 1 ) )' % IFP, T2)
    hypi = w.s([trik3], 'ralrimiva', '( %s -> %s )' % (ph, HYPI))
    # ---------------- tm2hitr
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ R )' % ph)
    z0fz = fzmem(ph, '0', z0a, ge0)
    rle = w.s([rnn, w.inst('leidd')], 'syl', '( %s -> R <_ R )' % ph)
    rfz = fzmem(ph, 'R', rr, rle)
    f0 = famat(ph, '0', z0fz, lambda st, f: st)
    fR = famat(ph, 'R', rfz, lambda st, f: st)
    dp0, _, _ = dp2facts(w, ph, '0', tv, dd, kk, jj, nkj, f0['xw'], f0['hw'])
    dpR, vkR, vjR = dp2facts(w, ph, 'R', tv, dd, kk, jj, nkj, fR['xw'], fR['hw'])
    CL0, CLR = CLN('A', NF('0'), DP2('0')), CLN('A', NF('R'), DP2('R'))
    jv0 = ifval(w, ph, IFP, BODYP, '0', z0a, CL0, clnex(w, ph, 'A', NF('0'), DP2('0')))
    jvR = ifval(w, ph, IFP, BODYP, 'R', rr, CLR, clnex(w, ph, 'A', NF('R'), DP2('R')))
    ss0 = cfgcl(w, ph, 'A', NF('0'), DP2('0'), tv, al, f0['nss'], dp0)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IFP, CFG_T))
    t2n = nn0cl(w, ph, T2, {"T'": tt})
    pj = w.s([ss0j, t2n], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) )' % (ph, IFP, CFG_T, T2))
    ant = w.s([phm, pj, hypi], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) )' % (ph, PHM, IFP, CFG_T, T2, HYPI))
    RUN = TRI('( %s ` 0 )' % IFP, '( %s ` R )' % IFP, '( R x. %s )' % T2)
    itr0 = w.s([rr, w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IFP, CFG_T, T2, HYPI, RUN))
    run = w.s([itr0, ant], 'mpd', '( %s -> %s )' % (ph, RUN))
    uk, uj = upid(w, ph, 'D', 'K', tv, dd, kk), upid(w, ph, 'D', 'J', tv, dd, jj)
    tbl0 = {XF('0'): ('( D ` K )', x0e), UP('D', 'K', '( D ` K )'): ('D', uk), HF('0'): ('( D ` J )', h0e), UP('D', 'J', '( D ` J )'): ('D', uj)}
    e0s, d0n = evaluate(w, ph, DP2('0'), {}, extra_rules=(lambda n: tbl0.get(n.text())))
    assert d0n == 'D', d0n
    cl0d = w.s([jv0, clneq(w, ph, 'A', NF('0'), e0s, DP2('0'), 'D')], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, IFP, CLN('A', NF('0'), 'D')))
    run2, _, _, _ = hrrw(w, ph, run, '( %s ` 0 )' % IFP, '( %s ` R )' % IFP, '( R x. %s )' % T2, ceq=cl0d, deq=jvR)
    # ---------------- the exit and the drop
    CE = CLN('E', NF('R'), DP2('R'))
    tex = brstep(w, ph, 'tm2fbrg', phm, meqA, al, el, dpR, c0, ga1, fR['nss'], htf, 'A', 'E', 'C0', GT("A'"), NF('R'), DP2('R'))
    run3 = hrseq(w, ph, phm, run2, tex, CLN('A', NF('0'), 'D'), CLR, CE, '( R x. %s )' % T2, '1')
    # DP2( R ) = UP( UP( D , J , H_R ) , K , ( W'_R ++ ( <" Y "> ++ X" ) ) )
    DJH = UP('D', 'J', HF('R'))
    WYX_R = CC(WPF('R'), CC(S1('Y'), 'X"'))
    cm = upc(w, ph, 'D', 'K', XF('R'), 'J', HF('R'), tv, dd, nkj, kk, fR['xw'], jj, fR['hw'])
    xRc = w.s([xRe], 'eqcomd', '( %s -> %s = %s )' % (ph, WYX_R, XF('R')))
    tblR = {DP2('R'): (UP(DJH, 'K', XF('R')), cm), XF('R'): (WYX_R, xRe)}
    psR, dRn = evaluate(w, ph, DP2('R'), {}, extra_rules=(lambda n: tblR.get(n.text())))
    assert dRn == UP(DJH, 'K', WYX_R), dRn
    PRED = CLN('E', NF('R'), UP(DJH, 'K', WYX_R))
    run4, _, _, _ = hrrw(w, ph, run3, CLN('A', NF('0'), 'D'), CE, '( ( R x. %s ) + 1 )' % T2, deq=clneq(w, ph, 'E', NF('R'), psR, DP2('R'), UP(DJH, 'K', WYX_R)))
    # tm2fdrop at D := DJH , W := W'_R , X := X"
    djhcl = updcl(w, ph, 'D', 'J', HF('R'), tv, dd, jj, fR['hw'])
    yxw = ccatw(w, ph, s1w(w, ph, yk, 'Y', GK), xpw2, S1('Y'), 'X"', GK)
    PREDS = CLN('E', SS, UP(DJH, 'K', WYX_R))
    POSTD = CLN('E1', SS, UP(DJH, 'K', 'X"'))
    ND = "( ( # ` %s ) + 1 )" % WPF('R')
    tdr = applylem(w, ph, 'tm2fdrop',
                   (((((phm, meqE), (el, e1l, kk), ((g2, d2), (bppk, yxw, djhcl), hcdr)), (yk, xpw2, hedr)), fR['wpw'])),
                   TRI(PREDS, POSTD, ND))
    ssr = clnss(w, ph, 'E', NF('R'), SS, UP(DJH, 'K', WYX_R), fR['nss'])
    tdr2 = hrssc(w, ph, phm, tdr, PREDS, POSTD, ND, PRED, ssr)
    w.qed([phm, run4, tdr2], 'syl3anc', '( %s -> %s )' % (ph, CONCL_P2Q))
    return w.run()


if __name__ == '__main__':
    if want('tm2fp2q'): tm2fp2q()
