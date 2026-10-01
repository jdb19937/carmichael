"""T-PL: the loop rules at a test label (blueprint D4): ~ tm2floop (Lean
` Frag.loop_runs' ` , the body's cost a family ` ( U ` i ) ` , total
` sum_ i e. ( 0 ..^ R ) ( ( U ` i ) + 1 ) + 1 ` , by ~ tm2hitsum ) and
~ tm2floopu (Lean ` Frag.loop_runs ` , uniform ` T' ` , total
` ( R x. ( T' + 1 ) ) + 1 ` , by ~ tm2hitr ).  The test ~ tm2lbrt at every
iteration, the body a hypothesis triple from ` B0 ` back to ` A ` , the exit
~ tm2fbrg on ` ( N ` R ) ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

IFL = '( j e. NN0 |-> %s )' % CLN('A', NF('j'), PF('j'))
BODYL = CLN('A', NF('j'), PF('j'))
UPM = '( j e. NN0 |-> ( ( U ` j ) + 1 ) )'


def loop(sigma):
    lab = 'tm2floop' if sigma else 'tm2floopu'
    tree, concl = (TREE_LOOPS, CONCL_LOOPS) if sigma else (TREE_LOOPU, CONCL_LOOPU)
    ph = cj(tree)
    HYPS = HYPS_LS if sigma else HYPS_LU
    w = W(lab, ('The loop rule of the machine layer at a test label with a per-iteration cost family: the test '
                '` branch C0 ( goto B0 ) ( goto E ) ` at ` A ` succeeds on the class ` ( N ` i ) ` for ` i < R ` '
                '(~ tm2lbrt ), the body runs from ` B0 ` back to ` A ` within ` ( U ` i ) ` steps (a hypothesis '
                'triple over the stack family ` ( P ` i ) ` ), and the test fails on ` ( N ` R ) ` (~ tm2fbrg ); '
                'the run is ~ tm2hitsum over the family of test-label configurations.  Lean: ` Frag.loop_runs\' ` '
                '(PrimList.lean) and ` Frag.loop_runs_budget ` (PrimTD.lean) in the Sigma form.')
               if sigma else
               ('The loop rule of the machine layer at a test label with a uniform per-iteration cost ` T\' ` : '
                '~ tm2floop with ~ tm2hitr in place of ~ tm2hitsum .  Lean: ` Frag.loop_runs ` .'))
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    meqA = c[MEQ('A', STM_LT)]
    al, b0l, el = c[LAB('A')], c[LAB('B0')], c[LAB('E')]
    c0t, rr = c[CTY('C0')], c['R e. NN0']
    fam, hyps, htf = c[FAM_L], c[HYPS], c[HTF(NF('R'))]
    ge = gotocl(w, ph, tv, 'E', el)
    gb0 = gotocl(w, ph, tv, 'B0', b0l)
    # ---------------- the iteration at k
    pk = '( %s /\\ k e. ( 0 ..^ R ) )' % ph
    Lk = Lifter(w, pk)
    kin, kfz, k1fz, knn, k1nn = kfacts(w, pk)
    K1 = '( k + 1 )'
    fk = famat(w, pk, Lk(fam, FAM_L), 'k', kfz)
    fk1 = famat(w, pk, Lk(fam, FAM_L), K1, k1fz)
    if sigma:
        body_i = ((HT(NF('i')), '%s e. NN0' % UF('i')), BODY_L('i', UF('i')))
        body_k = ((HT(NF('k')), '%s e. NN0' % UF('k')), BODY_L('k', UF('k')))
    else:
        body_i = (HT(NF('i')), BODY_L('i', "T'"))
        body_k = (HT(NF('k')), BODY_L('k', "T'"))
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS), cj(body_i), 'i', 'k', kin)
    ck = Ctx(w, pk, body_k, root=hyk)
    htk = ck[HT(NF('k'))]
    UK = UF('k') if sigma else "T'"
    trk = ck[BODY_L('k', UK)]
    t1 = brstep(w, pk, 'tm2lbrt', Lk(phm, PHM), Lk(meqA, MEQ('A', STM_LT)), Lk(al, LAB('A')), Lk(b0l, LAB('B0')), fk['pst'],
                Lk(c0t, CTY('C0')), Lk(ge, STMT(GT('E'))), fk['nss'], htk, 'A', 'B0', NF('k'), PF('k'))
    CLk, CBk, CLk1 = CLN('A', NF('k'), PF('k')), CLN('B0', NF('k'), PF('k')), CLN('A', NF(K1), PF(K1))
    t12 = hrseq(w, pk, Lk(phm, PHM), t1, trk, CLk, CBk, CLk1, '1', UK)
    N12 = '( 1 + %s )' % UK
    # the bound as ( UK + 1 ), i.e. ( UPM ` k ) in the Sigma case
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % pk)
    if sigma:
        ukn = ck['%s e. NN0' % UF('k')]
        ukc = w.s([ukn], 'nn0cnd', '( %s -> %s e. CC )' % (pk, UK))
    else:
        ukn = Lk(c["T' e. NN0"], "T' e. NN0")
        ukc = w.s([ukn], 'nn0cnd', '( %s -> %s e. CC )' % (pk, UK))
    com = w.s([onea, ukc], 'addcomd', '( %s -> ( 1 + %s ) = ( %s + 1 ) )' % (pk, UK, UK))
    UK1 = '( %s + 1 )' % UK
    if sigma:
        vex = w.s([], 'ovex', '%s e. _V' % UK1); vexa = w.s([vex], 'a1i', '( %s -> %s e. _V )' % (pk, UK1))
        upk = ifval(w, pk, UPM, '( ( U ` j ) + 1 )', 'k', knn, UK1, vexa)
        upkc = w.s([upk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (pk, UK1, UPM))
        neq = w.s([com, upkc], 'eqtrd', '( %s -> ( 1 + %s ) = ( %s ` k ) )' % (pk, UK, UPM))
        BK = '( %s ` k )' % UPM
    else:
        neq = com
        BK = UK1
    jvk = ifval(w, pk, IFL, BODYL, 'k', knn, CLk, clnex(w, pk, 'A', NF('k'), PF('k')))
    jvk1 = ifval(w, pk, IFL, BODYL, K1, k1nn, CLk1, clnex(w, pk, 'A', NF(K1), PF(K1)))
    trik, _, _, _ = hrrw(w, pk, t12, CLk, CLk1, N12,
                         ceq=w.s([jvk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (pk, CLk, IFL)),
                         deq=w.s([jvk1], 'eqcomd', '( %s -> %s = ( %s ` ( k + 1 ) ) )' % (pk, CLk1, IFL)), neq=neq)
    TRIK = TRI('( %s ` k )' % IFL, '( %s ` ( k + 1 ) )' % IFL, BK)
    if sigma:
        uk1n = w.s([ukn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pk, UK1))
        bkn = w.s([upk, uk1n], 'eqeltrd', '( %s -> %s e. NN0 )' % (pk, BK))
        pair = w.s([bkn, trik], 'jca', '( %s -> ( %s e. NN0 /\\ %s ) )' % (pk, BK, TRIK))
        HYPI = 'A. k e. ( 0 ..^ R ) ( %s e. NN0 /\\ %s )' % (BK, TRIK)
        hypi = w.s([pair], 'ralrimiva', '( %s -> %s )' % (ph, HYPI))
    else:
        HYPI = 'A. k e. ( 0 ..^ R ) %s' % TRIK
        hypi = w.s([trik], 'ralrimiva', '( %s -> %s )' % (ph, HYPI))
    # ---------------- the iteration rule
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    f0 = famat(w, ph, fam, '0', zmem(w, ph, rr))
    fR = famat(w, ph, fam, 'R', rmem(w, ph, rr))
    CL0, CLR, CLE = CLN('A', NF('0'), PF('0')), CLN('A', NF('R'), PF('R')), CLN('E', NF('R'), PF('R'))
    jv0 = ifval(w, ph, IFL, BODYL, '0', z0a, CL0, clnex(w, ph, 'A', NF('0'), PF('0')))
    jvR = ifval(w, ph, IFL, BODYL, 'R', rr, CLR, clnex(w, ph, 'A', NF('R'), PF('R')))
    ss0 = cfgcl(w, ph, 'A', NF('0'), PF('0'), tv, al, f0['nss'], f0['pst'])
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IFL, CFG_T))
    if sigma:
        S_K = SUM('k', 'R', '( %s ` k )' % UPM)
        ant = w.s([phm, ss0j, hypi], '3jca', '( %s -> ( %s /\\ ( %s ` 0 ) C_ %s /\\ %s ) )' % (ph, PHM, IFL, CFG_T, HYPI))
        RUN = TRI('( %s ` 0 )' % IFL, '( %s ` R )' % IFL, S_K)
        itr0 = w.s([rr, w.inst('tm2hitsum')], 'syl', '( %s -> ( ( %s /\\ ( %s ` 0 ) C_ %s /\\ %s ) -> %s ) )' % (ph, PHM, IFL, CFG_T, HYPI, RUN))
        run = w.s([ant, itr0], 'mpd', '( %s -> %s )' % (ph, RUN))
        # the sum: sum_ k ( UPM ` k ) = sum_ k ( ( U ` k ) + 1 ) = sum_ i ( ( U ` i ) + 1 )
        f1 = w.s([], 'fveq2', '( j = k -> ( U ` j ) = ( U ` k ) )')
        f2 = w.s([f1], 'oveq1d', '( j = k -> ( ( U ` j ) + 1 ) = ( ( U ` k ) + 1 ) )')
        eqi = w.s([], 'eqid', '%s = %s' % (UPM, UPM))
        vx = w.s([], 'ovex', '( ( U ` k ) + 1 ) e. _V')
        fv = w.s([f2, eqi, vx], 'fvmpt', '( k e. NN0 -> ( %s ` k ) = ( ( U ` k ) + 1 ) )' % UPM)
        fv2 = w.s([w.inst('elfzonn0'), fv], 'syl', '( k e. ( 0 ..^ R ) -> ( %s ` k ) = ( ( U ` k ) + 1 ) )' % UPM)
        rg = w.s([fv2], 'rgen', 'A. k e. ( 0 ..^ R ) ( %s ` k ) = ( ( U ` k ) + 1 )' % UPM)
        S_K2 = SUM('k', 'R', '( ( U ` k ) + 1 )')
        se = w.s([rg, w.inst('sumeq2')], 'ax-mp', '%s = %s' % (S_K, S_K2))
        g1 = w.s([], 'fveq2', '( k = i -> ( U ` k ) = ( U ` i ) )')
        g2 = w.s([g1], 'oveq1d', '( k = i -> ( ( U ` k ) + 1 ) = ( ( U ` i ) + 1 ) )')
        S_I = SUM('i', 'R', '( ( U ` i ) + 1 )')
        cb = w.s([g2], 'cbvsumv', '%s = %s' % (S_K2, S_I))
        se2 = w.s([se, cb], 'eqtri', '%s = %s' % (S_K, S_I))
        se2a = w.s([se2], 'a1i', '( %s -> %s = %s )' % (ph, S_K, S_I))
        runr, _, _, _ = hrrw(w, ph, run, '( %s ` 0 )' % IFL, '( %s ` R )' % IFL, S_K, ceq=jv0, deq=jvR, neq=se2a)
        SB = S_I
    else:
        tn = w.s([c["T' e. NN0"], w.inst('peano2nn0')], 'syl', '( %s -> ( T\' + 1 ) e. NN0 )' % ph)
        pj = w.s([ss0j, tn], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ ( T\' + 1 ) e. NN0 ) )' % (ph, IFL, CFG_T))
        ant = w.s([phm, pj, hypi], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ ( T\' + 1 ) e. NN0 ) /\\ %s ) )' % (ph, PHM, IFL, CFG_T, HYPI))
        SB = "( R x. ( T' + 1 ) )"
        RUN = TRI('( %s ` 0 )' % IFL, '( %s ` R )' % IFL, SB)
        itr0 = w.s([rr, w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ ( T\' + 1 ) e. NN0 ) /\\ %s ) -> %s ) )' % (ph, PHM, IFL, CFG_T, HYPI, RUN))
        run = w.s([ant, itr0], 'mpd', '( %s -> %s )' % (ph, RUN))
        runr, _, _, _ = hrrw(w, ph, run, '( %s ` 0 )' % IFL, '( %s ` R )' % IFL, SB, ceq=jv0, deq=jvR)
    # ---------------- the exit
    ex = brstep(w, ph, 'tm2fbrg', phm, meqA, al, el, fR['pst'], c0t, gb0, fR['nss'], htf, 'A', 'E', NF('R'), PF('R'))
    fin = TRI(CL0, CLE, '( %s + 1 )' % SB)
    assert fin == concl, (fin, concl)
    w.qed([phm, runr, ex], 'syl3anc', '( %s -> %s )' % (ph, fin))
    return w.run()


if __name__ == '__main__':
    if want('tm2floop'): loop(True)
    if want('tm2floopu'): loop(False)
