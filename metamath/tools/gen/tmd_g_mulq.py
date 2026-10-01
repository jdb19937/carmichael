"""T-MD: the loop of ` mul ` (TM/MulDiv.lean) from its test label (~ tm2fmlq ):
~ tm2hitr over ` ( 0 ..^ R ) ` with the family of blueprint D4, each iteration
~ tm2fmlb at ` k ` (the per-iteration hypotheses instantiated at ` k ` , the six
updates of the stacks collapsed by ~ tm2stkup6 ).  Lean: ` Frag.loop_runs ` with
` MulInv ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

IFQ = '( j e. NN0 |-> %s )' % CLN('A', NF('j'), DPM('j'))
BODYQ = CLN('A', NF('j'), DPM('j'))
T4 = "( T' + 4 )"


def tm2fmlq():
    lab = 'tm2fmlq'
    tree, ph = TREE_MLQ, cj(TREE_MLQ)
    w = W(lab, 'The loop of ` mul ` (TM/MulDiv.lean) from its test label ` A ` : the multiplier '
               'on ` J ` is consumed bit by bit, the multiplicand on ` K ` doubled and the '
               'accumulator on ` I ` grown by the conditional adds given as hypothesis triples, '
               'the state class ` ( N ` i ) ` and the stack contents ` ( X ` i ) ` , ` ( Y ` i ) ` , '
               '` ( H ` i ) ` families with step equations (blueprint D4, D5); ~ tm2hitr over '
               '` ( 0 ..^ R ) ` with ~ tm2fmlb at each iteration.  Lean: ` Frag.loop_runs ` at '
               '` MulInv ` in ` mul_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, b0l, bpl, bql, e0l, a0l, el = [c[LAB(x)] for x in ('A', 'B0', "B'", 'B"', 'E0', 'A0', 'E')]
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    c0t, ct, lpt, ff, z0k = c[CTY('C0')], c[CTY('C')], c[LTY("L'")], c[RTY('F', 'J')], c['Z0 e. %s' % GK]
    dd, rr, tt, t1 = c[STKD('D')], c['R e. NN0'], c["T' e. NN0"], c["1 <_ T'"]
    fam, hyps = c[FAM_MQ], c[HYPS_MQ]
    meqA, meqB0, meqE0, meqBq, meqA0 = [c[MEQ(a, s)] for a, s in (('A', STM_MTE), ('B0', STM_MI), ('E0', STM_MSK), ('B"', STM_MPZ), ('A0', STM_MPB))]
    ge = gotocl(w, ph, tv, 'E', el)

    def famat(ph2, X, xfz, Lf):
        st, _ = inst_v(w, ph2, Lf(fam, FAM_MQ), cj(FAMB_MQ('i')), 'i', X, xfz)
        cx = Ctx(w, ph2, FAMB_MQ(X), root=st)
        return dict(xw=cx[WRD(XF(X), GK)], yw=cx[WRD(YF(X), GJ)], hw=cx[WRD(HF(X), GI)], nss=cx[SSS(NF(X))])

    def fzmem(ph2, X, xnn, xle, rr2):
        return w.s([w.s([xnn, rr2, xle], '3jca', '( %s -> ( %s e. NN0 /\\ R e. NN0 /\\ %s <_ R ) )' % (ph2, X, X)),
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
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS_MQ), cj(HYP_MQ_TREE('i')), 'i', 'k', kin)
    ck = Ctx(w, pk, HYP_MQ_TREE('k'), root=hyk)
    K1 = '( k + 1 )'
    ystep = ck['%s = %s' % (YF('k'), CC(S1(UF(K1)), YF(K1)))]
    xstep = ck['%s = %s' % (XF(K1), CC(S1('Z0'), XF('k')))]
    uk1 = ck['%s e. %s' % (UF(K1), GJ)]
    htk, hpbk, disjk = ck[HT(NF('k'))], ck[HPB(SS, UF(K1), NF(K1))], ck[DISJ_MQ('k')]
    tvk, ddk, kkk, jjk, iik = Lk(tv, 'T e. V'), Lk(dd, STKD('D')), Lk(kk, 'K e. %s' % DG), Lk(jj, 'J e. %s' % DG), Lk(ii, 'I e. %s' % DG)
    nkjk, nkik, njik = Lk(nkj, 'K =/= J'), Lk(nki, 'K =/= I'), Lk(nji, 'J =/= I')
    dpk, vi, vk, vj = dpmfacts(w, pk, 'k', tvk, ddk, kkk, jjk, iik, nkjk, nkik, njik, fk['hw'], fk['xw'], fk['yw'])
    dpkJ = w.s([vj, ystep], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (pk, DPM('k'), CC(S1(UF(K1)), YF(K1))))
    # the disjunction in tm2fmlb's form: H' = ( D ` I ) is H_{k+1} = ( DPM(k) ` I )
    vic = w.s([vi], 'eqcomd', '( %s -> %s = ( %s ` I ) )' % (pk, HF('k'), DPM('k')))
    e1 = w.s([vic], 'eqeq2d', '( %s -> ( %s = %s <-> %s = ( %s ` I ) ) )' % (pk, HF(K1), HF('k'), HF(K1), DPM('k')))
    e2 = w.s([e1], 'anbi2d', '( %s -> ( ( %s /\\ %s = %s ) <-> ( %s /\\ %s = ( %s ` I ) ) ) )'
             % (pk, HTCF(NF('k')), HF(K1), HF('k'), HTCF(NF('k')), HF(K1), DPM('k')))
    ADDK = '( %s /\\ %s )' % (HTC(NF('k')), TRI(CLN("B'", NF('k'), DPM('k')), CLN('B"', SS, UP(DPM('k'), 'I', HF(K1))), "T'"))
    e3 = w.s([e2], 'orbi2d', '( %s -> ( ( %s \\/ ( %s /\\ %s = %s ) ) <-> ( %s \\/ ( %s /\\ %s = ( %s ` I ) ) ) ) )'
             % (pk, ADDK, HTCF(NF('k')), HF(K1), HF('k'), ADDK, HTCF(NF('k')), HF(K1), DPM('k')))
    disjk2 = w.s([e3, disjk], 'mpbid', '( %s -> ( %s \\/ ( %s /\\ %s = ( %s ` I ) ) ) )' % (pk, ADDK, HTCF(NF('k')), HF(K1), DPM('k')))
    MAPK = {'N': NF('k'), "N'": NF(K1), 'D': DPM('k'), 'U': UF(K1), "Y'": YF(K1), "H'": HF(K1), 'Q': GT('E')}
    instk = ren(TREE_MLB, MAPK)
    assert sub(DISJ_ML, MAPK) == concl(w, pk, disjk2)
    derived = {STKD(DPM('k')): dpk, '( %s ` J ) = %s' % (DPM('k'), CC(S1(UF(K1)), YF(K1))): dpkJ,
               WRD(YF(K1), GJ): fk1['yw'], WRD(HF(K1), GI): fk1['hw'], '%s e. %s' % (UF(K1), GJ): uk1,
               SSS(NF('k')): fk['nss'], SSS(NF(K1)): fk1['nss'], HT(NF('k')): htk, HPB(SS, UF(K1), NF(K1)): hpbk,
               sub(DISJ_ML, MAPK): disjk2, STMT(GT('E')): Lk(ge, STMT(GT('E'))), MEQ('A', STM_MTE): Lk(meqA, MEQ('A', STM_MTE))}
    def look(t):
        if t in derived:
            return derived[t]
        return Lk(c[t], t)
    POSTK = sub(POST_MLB, MAPK)
    trik = applylem(w, pk, 'tm2fmlb', leafsteps(instk, look), TRI(CLN('A', NF('k'), DPM('k')), CLN('A', NF(K1), POSTK), T4))
    # the post stacks collapse to DPM( k + 1 )
    xstepc = w.s([xstep], 'eqcomd', '( %s -> %s = %s )' % (pk, CC(S1('Z0'), XF('k')), XF(K1)))
    col, RHS6 = up6g(w, pk, 'D', 'I', 'K', 'J', HF('k'), HF(K1), XF('k'), XF(K1), YF('k'), YF(K1), tvk, ddk,
                     w.s([nkik], 'necomd', '( %s -> I =/= K )' % pk), w.s([njik], 'necomd', '( %s -> I =/= J )' % pk), nkjk,
                     iik, kkk, jjk, fk['hw'], fk1['hw'], fk['xw'], fk1['xw'], fk['yw'], fk1['yw'])
    assert RHS6 == DPM(K1)
    tbl = {'( %s ` K )' % DPM('k'): (XF('k'), vk), CC(S1('Z0'), XF('k')): (XF(K1), xstepc),
           UP3(DPM('k'), 'I', HF(K1), 'K', XF(K1), 'J', YF(K1)): (DPM(K1), col)}
    ps, postn = evaluate(w, pk, POSTK, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert postn == DPM(K1), postn
    trik2, _, _, _ = hrrw(w, pk, trik, CLN('A', NF('k'), DPM('k')), CLN('A', NF(K1), POSTK), T4,
                          deq=clneq(w, pk, 'A', NF(K1), ps, POSTK, DPM(K1)))
    CLk, CLk1 = CLN('A', NF('k'), DPM('k')), CLN('A', NF(K1), DPM(K1))
    jvk = ifval(w, pk, IFQ, BODYQ, 'k', knn, CLk, clnex(w, pk, 'A', NF('k'), DPM('k')))
    jvk1 = ifval(w, pk, IFQ, BODYQ, K1, k1nn, CLk1, clnex(w, pk, 'A', NF(K1), DPM(K1)))
    trik3, _, _, _ = hrrw(w, pk, trik2, CLk, CLk1, T4,
                          ceq=w.s([jvk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (pk, CLk, IFQ)),
                          deq=w.s([jvk1], 'eqcomd', '( %s -> %s = ( %s ` ( k + 1 ) ) )' % (pk, CLk1, IFQ)))
    HYPI = 'A. k e. ( 0 ..^ R ) %s' % TRI('( %s ` k )' % IFQ, '( %s ` ( k + 1 ) )' % IFQ, T4)
    hypi = w.s([trik3], 'ralrimiva', '( %s -> %s )' % (ph, HYPI))
    # ---------------- tm2hitr
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ R )' % ph)
    z0fz = fzmem(ph, '0', z0a, ge0, rr)
    rnn = w.s([rr, w.inst('nn0red')], 'syl', '( %s -> R e. RR )' % ph)
    rle = w.s([rnn, w.inst('leidd')], 'syl', '( %s -> R <_ R )' % ph)
    rfz = fzmem(ph, 'R', rr, rle, rr)
    f0 = famat(ph, '0', z0fz, lambda st, f: st)
    fR = famat(ph, 'R', rfz, lambda st, f: st)
    dp0, _, _, _ = dpmfacts(w, ph, '0', tv, dd, kk, jj, ii, nkj, nki, nji, f0['hw'], f0['xw'], f0['yw'])
    CL0, CLR = CLN('A', NF('0'), DPM('0')), CLN('A', NF('R'), DPM('R'))
    jv0 = ifval(w, ph, IFQ, BODYQ, '0', z0a, CL0, clnex(w, ph, 'A', NF('0'), DPM('0')))
    jvR = ifval(w, ph, IFQ, BODYQ, 'R', rr, CLR, clnex(w, ph, 'A', NF('R'), DPM('R')))
    ss0 = cfgcl(w, ph, 'A', NF('0'), DPM('0'), tv, al, f0['nss'], dp0)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IFQ, CFG_T))
    t4n = nn0cl(w, ph, T4, {"T'": tt})
    pj = w.s([ss0j, t4n], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) )' % (ph, IFQ, CFG_T, T4))
    ant = w.s([phm, pj, hypi], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) )' % (ph, PHM, IFQ, CFG_T, T4, HYPI))
    RUN = TRI('( %s ` 0 )' % IFQ, '( %s ` R )' % IFQ, '( R x. %s )' % T4)
    itr0 = w.s([rr, w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IFQ, CFG_T, T4, HYPI, RUN))
    run = w.s([itr0, ant], 'mpd', '( %s -> %s )' % (ph, RUN))
    hrrw(w, ph, run, '( %s ` 0 )' % IFQ, '( %s ` R )' % IFQ, '( R x. %s )' % T4, ceq=jv0, deq=jvR, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fmlq'): tm2fmlq()
