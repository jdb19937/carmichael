"""T5b: the loop of `bitlen` (TM/Prims.lean) from its test label (~ tm2fblq ):
~ tm2hitr over ` ( 0 ..^ R ) ` with the family of blueprint D4, each iteration
~ tm2fblk at ` k ` (the per-iteration hypotheses instantiated at ` k ` , the six
updates of the stacks collapsed by ~ tm2stkup6 ), then the final iteration and
the exit ~ tm2fble .  Lean: ` Frag.loop_runs ` with ` BlInv ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_c_blk import leafsteps

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

IFQ = '( j e. NN0 |-> %s )' % CLN('A', NF('j'), DP('j'))
BODYQ = CLN('A', NF('j'), DP('j'))


def dpfacts(w, ph, X, tv, dd, kk, jj, ii, nkj, nki, nji, xw, hw, ww):
    """DP(X) e. Stk and its values at K , J , I"""
    a = updcl(w, ph, 'D', 'K', XF(X), tv, dd, kk, xw)
    b = updcl(w, ph, UP('D', 'K', XF(X)), 'J', HF(X), tv, a, jj, hw)
    d = updcl(w, ph, UP(UP('D', 'K', XF(X)), 'J', HF(X)), 'I', WF(X), tv, b, ii, ww)
    xv, hv, wv = elv(w, ph, xw, XF(X)), elv(w, ph, hw, HF(X)), elv(w, ph, ww, WF(X))
    U2 = UP(UP('D', 'K', XF(X)), 'J', HF(X))
    vk1 = updnv(w, ph, U2, 'I', WF(X), 'K', tv, b, ii, wv, kk, nki)
    vk2 = updnv(w, ph, UP('D', 'K', XF(X)), 'J', HF(X), 'K', tv, a, jj, hv, kk, nkj)
    vk3 = updkv(w, ph, 'D', 'K', XF(X), tv, dd, kk, xv)
    vk = w.s([w.s([vk1, vk2], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` K ) )' % (ph, DP(X), UP('D', 'K', XF(X)))), vk3], 'eqtrd',
             '( %s -> ( %s ` K ) = %s )' % (ph, DP(X), XF(X)))
    vj1 = updnv(w, ph, U2, 'I', WF(X), 'J', tv, b, ii, wv, jj, nji)
    vj2 = updkv(w, ph, UP('D', 'K', XF(X)), 'J', HF(X), tv, a, jj, hv)
    vj = w.s([vj1, vj2], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, DP(X), HF(X)))
    vi = updkv(w, ph, U2, 'I', WF(X), tv, b, ii, wv)
    return d, vk, vj, vi


def tm2fblq():
    lab = 'tm2fblq'
    tree, ph = TREE_BLQ, cj(TREE_BLQ)
    w = W(lab, 'The loop of ` bitlen ` (TM/Prims.lean) from its test label ` A ` : the '
               'reversed number on stack ` K ` is scanned most-significant bit first onto '
               'stack ` J ` , the counter on ` I ` incremented once a one has been seen, '
               'the state class ` ( N ` i ) ` , the post-scan class ` ( O ` i ) ` and the '
               'stack contents ` ( X ` i ) ` , ` ( H ` i ) ` , ` ( W ` i ) ` given as families '
               'with step equations, the increments by ~ tm2fincr \'s decomposition per '
               'iteration (blueprint D3, D4); ~ tm2hitr over ` ( 0 ..^ R ) ` with ~ tm2fblk '
               'at each iteration, then the terminator iteration and the exit ~ tm2fble .  '
               'Lean: ` Frag.loop_runs ` at ` BlInv ` in ` bitlen_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, a1, a2, e1, e2, e0, a0, h0, h1, el = [c[LAB(x)] for x in ('A', "A'", 'A"', "E'", 'E"', 'E0', 'A0', 'H0', "H'", 'E')]
    kk, jj, ii, ip = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG], c["I' e. %s" % DG]
    nkj, nki, nji, nii = c['K =/= J'], c['K =/= I'], c['J =/= I'], c["I =/= I'"]
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)
    nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    cc, c1, c2 = c[CTY('C')], c[CTY("C'")], c[CTY('C"')]
    ff, pp, ll, l0, l1 = c[RTY('F', 'K')], c[PTY('P', 'J')], c[LTY('L')], c[LTY('L0')], c[LTY("L'")]
    b0k, b0j, yk = c['B0 C_ %s' % GK], c['B0 C_ %s' % GJ], c['Y e. %s' % GK]
    dd, init, rr, tt, t1 = c[STKD('D')], c[INIT_Q], c['R e. NN0'], c["T' e. NN0"], c["1 <_ T'"]
    fam, famn, hyps, fin = c[FAM_Q], c[FAMN_Q], c[HYPS_Q], c[FIN_Q]
    meqA, meqA1, meqA2 = c[MEQ('A', STM_TQ)], c[MEQ("A'", STM_SQ)], c[MEQ('A"', STM_DAQ)]
    x0e, h0e, w0e = [w.s([init, w.inst(r)], 'syl', '( %s -> %s )' % (ph, f)) for r, f in
                     (('simp1', INIT_Q_TREE[0]), ('simp2', INIT_Q_TREE[1]), ('simp3', INIT_Q_TREE[2]))]
    ge, ge2 = gotocl(w, ph, tv, 'E', el), gotocl(w, ph, tv, 'E"', e2)
    ga2 = gotocl(w, ph, tv, 'A"', a2)
    ld0 = loadcl(w, ph, tv, 'L0', GT('A"'), l0, ga2)
    ldl = loadcl(w, ph, tv, 'L', GT('A"'), ll, ga2)
    pul = pushcl(w, ph, tv, 'J', 'P', LOAD('L', GT('A"')), jj, pp, ldl)
    ge1 = gotocl(w, ph, tv, "E'", e1)
    T4 = "( T' + 4 )"
    rnn = w.s([rr, w.inst('nn0red')], 'syl', '( %s -> R e. RR )' % ph)
    r1nn = w.s([rr, w.inst('peano2nn0')], 'syl', '( %s -> ( R + 1 ) e. NN0 )' % ph)

    def famat(ph2, X, xfz, Lf):
        st, _ = inst_v(w, ph2, Lf(fam, FAM_Q), cj(FAMB_Q('i')), 'i', X, xfz)
        cx = Ctx(w, ph2, FAMB_Q(X), root=st)
        return dict(xw=cx[WRD(XF(X), GK)], hw=cx[WRD(HF(X), GJ)], ww=cx[WRD(WF(X), GI)], nss=cx[SSS(NF(X))], oss=cx[SSS(OF(X))])

    def fzmem(ph2, X, xnn, xle):
        """X e. ( 0 ... R ) from X e. NN0 and X <_ R"""
        return w.s([w.s([xnn, L_(ph2, rr, 'R e. NN0'), xle], '3jca', '( %s -> ( %s e. NN0 /\\ R e. NN0 /\\ %s <_ R ) )' % (ph2, X, X)),
                    w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... R ) )' % (ph2, X))

    def L_(ph2, st, f):
        return st if ph2 == ph else w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))

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
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS_Q), HYP_Q('i'), 'i', 'k', kin)
    ck = Ctx(w, pk, HYP_Q_TREE('k'), root=hyk)
    K1 = '( k + 1 )'
    xstep = ck['%s = %s' % (XF('k'), CC(S1(UF('k')), XF(K1)))]
    hstep = ck['%s = %s' % (HF(K1), CC(S1(UF('k')), HF('k')))]
    ukb = ck['%s e. B0' % UF('k')]
    ukk = w.s([Lk(b0k, 'B0 C_ %s' % GK), ukb], 'sseldd', '( %s -> %s e. %s )' % (pk, UF('k'), GK))
    ukj = w.s([Lk(b0j, 'B0 C_ %s' % GJ), ukb], 'sseldd', '( %s -> %s e. %s )' % (pk, UF('k'), GJ))
    tvk, ddk, kkk, jjk, iik = Lk(tv, 'T e. V'), Lk(dd, STKD('D')), Lk(kk, 'K e. %s' % DG), Lk(jj, 'J e. %s' % DG), Lk(ii, 'I e. %s' % DG)
    nkjk, nkik, njik = Lk(nkj, 'K =/= J'), Lk(nki, 'K =/= I'), Lk(nji, 'J =/= I')
    dpk, vk, vj, vi = dpfacts(w, pk, 'k', tvk, ddk, kkk, jjk, iik, nkjk, nkik, njik, fk['xw'], fk['hw'], fk['ww'])
    dpk1, _, _, _ = dpfacts(w, pk, K1, tvk, ddk, kkk, jjk, iik, nkjk, nkik, njik, fk1['xw'], fk1['hw'], fk1['ww'])
    dpkK = w.s([vk, xstep], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (pk, DP('k'), CC(S1(UF('k')), XF(K1))))
    MAPK = {'X': XF(K1), 'Z': UF('k'), "Z'": UF('k'), 'Z"': ZF('k'), 'W': WPF('k'), "X'": XPF('k'), 'Z0': Z0F('k'),
            'W0': WF(K1), 'W1': WF('k'), 'N': NF('k'), "O'": OF('k'), "N'": NF(K1), 'D': DP('k'),
            'Q': GT('E'), "Q'": LOAD('L0', GT('A"')), 'Q"': GT('E"')}
    instk = ren(TREE_BLK, MAPK)
    assert sub(DISJ_BLK, MAPK) == DISJ_Q('k')
    derived = {STKD(DP('k')): dpk, '( %s ` K ) = %s' % (DP('k'), CC(S1(UF('k')), XF(K1))): dpkK,
               '( %s ` I ) = %s' % (DP('k'), WF('k')): vi,
               '%s e. %s' % (UF('k'), GK): ukk, '%s e. %s' % (UF('k'), GJ): ukj, WRD(XF(K1), GK): fk1['xw'],
               SSS(NF('k')): fk['nss'], SSS(OF('k')): fk['oss'], SSS(NF(K1)): fk1['nss'],
               STMT(GT('E')): Lk(ge, STMT(GT('E'))), STMT(LOAD('L0', GT('A"'))): Lk(ld0, STMT(LOAD('L0', GT('A"')))),
               STMT(GT('E"')): Lk(ge2, STMT(GT('E"')))}
    for t in flat(HYP_Q_TREE('k')):
        derived.setdefault(t, ck[t])
    def look(t):
        if t in derived:
            return derived[t]
        return Lk(c[t], t)
    POSTK = sub(UP(D2_BLS1, 'I', 'W0'), MAPK)
    trik = applylem(w, pk, 'tm2fblk', leafsteps(instk, look), TRI(CLN('A', NF('k'), DP('k')), CLN('A', NF(K1), POSTK), T4))
    # the post stacks collapse to DP( k + 1 )
    hstepc = w.s([hstep], 'eqcomd', '( %s -> %s = %s )' % (pk, CC(S1(UF('k')), HF('k')), HF(K1)))
    col, RHS6 = up6(w, pk, 'D', XF('k'), XF(K1), HF('k'), HF(K1), WF('k'), WF(K1), tvk, ddk, nkjk, nkik, njik, kkk, jjk, iik,
                    fk['xw'], fk1['xw'], fk['hw'], fk1['hw'], fk['ww'], fk1['ww'])
    assert RHS6 == DP(K1)
    tbl = {'( %s ` J )' % DP('k'): (HF('k'), vj), CC(S1(UF('k')), HF('k')): (HF(K1), hstepc),
           UP3(DP('k'), 'K', XF(K1), 'J', HF(K1), 'I', WF(K1)): (DP(K1), col)}
    ps, postn = evaluate(w, pk, POSTK, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert postn == DP(K1), postn
    trik2, _, _, _ = hrrw(w, pk, trik, CLN('A', NF('k'), DP('k')), CLN('A', NF(K1), POSTK), T4,
                          deq=clneq(w, pk, 'A', NF(K1), ps, POSTK, DP(K1)))
    # transport into the family
    CLk, CLk1 = CLN('A', NF('k'), DP('k')), CLN('A', NF(K1), DP(K1))
    jvk = ifval(w, pk, IFQ, BODYQ, 'k', knn, CLk, clnex(w, pk, 'A', NF('k'), DP('k')))
    jvk1 = ifval(w, pk, IFQ, BODYQ, K1, k1nn, CLk1, clnex(w, pk, 'A', NF(K1), DP(K1)))
    trik3, _, _, _ = hrrw(w, pk, trik2, CLk, CLk1, T4,
                          ceq=w.s([jvk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (pk, CLk, IFQ)),
                          deq=w.s([jvk1], 'eqcomd', '( %s -> %s = ( %s ` ( k + 1 ) ) )' % (pk, CLk1, IFQ)))
    HYPI = 'A. k e. ( 0 ..^ R ) %s' % TRI('( %s ` k )' % IFQ, '( %s ` ( k + 1 ) )' % IFQ, T4)
    hypi = w.s([trik3], 'ralrimiva', '( %s -> %s )' % (ph, HYPI))
    # ---------------- tm2hitr
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ R )' % ph)
    z0fz = fzmem(ph, '0', z0a, ge0)
    rle = w.s([rnn, w.inst('leidd')], 'syl', '( %s -> R <_ R )' % ph)
    rfz = fzmem(ph, 'R', rr, rle)
    f0 = famat(ph, '0', z0fz, lambda st, f: st)
    fR = famat(ph, 'R', rfz, lambda st, f: st)
    dp0, _, _, _ = dpfacts(w, ph, '0', tv, dd, kk, jj, ii, nkj, nki, nji, f0['xw'], f0['hw'], f0['ww'])
    dpR, vkR, vjR, viR = dpfacts(w, ph, 'R', tv, dd, kk, jj, ii, nkj, nki, nji, fR['xw'], fR['hw'], fR['ww'])
    CL0, CLR = CLN('A', NF('0'), DP('0')), CLN('A', NF('R'), DP('R'))
    jv0 = ifval(w, ph, IFQ, BODYQ, '0', z0a, CL0, clnex(w, ph, 'A', NF('0'), DP('0')))
    jvR = ifval(w, ph, IFQ, BODYQ, 'R', rr, CLR, clnex(w, ph, 'A', NF('R'), DP('R')))
    ss0 = cfgcl(w, ph, 'A', NF('0'), DP('0'), tv, al, f0['nss'], dp0)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IFQ, CFG_T))
    t4n = nn0cl(w, ph, T4, {"T'": tt})
    pj = w.s([ss0j, t4n], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) )' % (ph, IFQ, CFG_T, T4))
    ant = w.s([phm, pj, hypi], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) )' % (ph, PHM, IFQ, CFG_T, T4, HYPI))
    RUN = TRI('( %s ` 0 )' % IFQ, '( %s ` R )' % IFQ, '( R x. %s )' % T4)
    itr0 = w.s([rr, w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IFQ, CFG_T, T4, HYPI, RUN))
    run = w.s([itr0, ant], 'mpd', '( %s -> %s )' % (ph, RUN))
    # DP( 0 ) = D
    uk, uj, ui = upid(w, ph, 'D', 'K', tv, dd, kk), upid(w, ph, 'D', 'J', tv, dd, jj), upid(w, ph, 'D', 'I', tv, dd, ii)
    tbl0 = {XF('0'): ('( D ` K )', x0e), UP('D', 'K', '( D ` K )'): ('D', uk), HF('0'): ('( D ` J )', h0e),
            UP('D', 'J', '( D ` J )'): ('D', uj), WF('0'): ('( D ` I )', w0e), UP('D', 'I', '( D ` I )'): ('D', ui)}
    e0s, d0n = evaluate(w, ph, DP('0'), {}, extra_rules=(lambda n: tbl0.get(n.text())))
    assert d0n == 'D', d0n
    cl0d = w.s([jv0, clneq(w, ph, 'A', NF('0'), e0s, DP('0'), 'D')], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, IFQ, CLN('A', NF('0'), 'D')))
    run2, _, _, _ = hrrw(w, ph, run, '( %s ` 0 )' % IFQ, '( %s ` R )' % IFQ, '( R x. %s )' % T4, ceq=cl0d, deq=jvR)
    # ---------------- the final iteration at R
    cf = Ctx(w, ph, FIN_Q_TREE, root=fin)
    xRe, x0w = cf['%s = %s' % (XF('R'), CC(S1('Y'), 'X0'))], cf[WRD('X0', GK)]
    htR, hend, hdat, hsk, htf = cf[HT(NF('R'))], cf[HEND(NF('R'), 'Y', OF('R'), L='L0')], cf[HDAT(OF('R'))], cf[HLOAD(OF('R'), NF('( R + 1 )'))], cf[HTF(NF('( R + 1 )'))]
    dpRK = w.s([vkR, xRe], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, DP('R'), CC(S1('Y'), 'X0')))
    R1 = '( R + 1 )'
    MAPE = {'N': NF('R'), 'O': OF('R'), "N'": NF(R1), 'D': DP('R'), 'X': 'X0', 'L': 'L0', 'E0': 'E"',
            "Q'": PUSH('J', 'P', LOAD('L', GT('A"'))), 'Q"': GT("E'")}
    inste = ren(TREE_BLE, MAPE)
    derivede = {STKD(DP('R')): dpR, '( %s ` K ) = %s' % (DP('R'), CC(S1('Y'), 'X0')): dpRK, WRD('X0', GK): x0w,
                SSS(NF('R')): fR['nss'], SSS(OF('R')): fR['oss'], SSS(NF(R1)): famn,
                STMT(PUSH('J', 'P', LOAD('L', GT('A"')))): pul, STMT(GT("E'")): ge1,
                HT(NF('R')): htR, HEND(NF('R'), 'Y', OF('R'), L='L0'): hend, HDAT(OF('R')): hdat, HLOAD(OF('R'), NF(R1)): hsk, HTF(NF(R1)): htf}
    def looke(t):
        if t in derivede:
            return derivede[t]
        return c[t]
    trie = applylem(w, ph, 'tm2fble', leafsteps(inste, looke),
                    TRI(CLR, CLN('E', NF(R1), UP(DP('R'), 'K', 'X0')), '5'))
    colR, RHS3 = up3cK(w, ph, 'D', XF('R'), 'X0', HF('R'), WF('R'), tv, dd, njk, nji, nik, kk, jj, ii, fR['xw'], x0w, fR['hw'], fR['ww'])
    FIN = UP3('D', 'K', 'X0', 'J', HF('R'), 'I', WF('R'))
    assert RHS3 == FIN
    trie2, _, _, _ = hrrw(w, ph, trie, CLR, CLN('E', NF(R1), UP(DP('R'), 'K', 'X0')), '5',
                          deq=clneq(w, ph, 'E', NF(R1), colR, UP(DP('R'), 'K', 'X0'), FIN))
    w.qed([phm, run2, trie2], 'syl3anc', '( %s -> %s )' % (ph, CONCL_BLQ))
    return w.run()


if __name__ == '__main__':
    if want('tm2fblq'): tm2fblq()
