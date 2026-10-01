"""T-MD: the shift-up loop of ` divmod ` (TM/MulDiv.lean, blueprint 6.1): one
iteration ~ tm2fdmub (the test ~ tm2lbrt , the push of a zero on the divisor
~ tm2fpshn , the composite ` incr j s ; dup y t s ; dup x s t ; cmpFrag t s `
as one hypothesis triple) and the loop ~ tm2fdmuq (~ tm2hitr over the family
` UPD( UPD( D , J , ( Y ` i ) ) , I' , ( Q ` i ) ) ` , the collapse by ~ tm2stkup4 )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
from tmd_f_mulb import brstep

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fdmub():
    lab = 'tm2fdmub'
    tree, ph = TREE_DMUB, cj(TREE_DMUB)
    D1 = UP('D', 'J', Z0DJ)
    w = W(lab, 'One iteration of the shift-up loop of ` divmod ` (` dmUpBody ` ): the loop test at '
               '` A ` succeeds (~ tm2lbrt ), a zero is pushed on the divisor ` J ` (~ tm2fpshn , '
               '` sh := 2 sh ` ), and ` incr j s ; dup y t s ; dup x s t ; cmpFrag t s ` --- a hypothesis '
               'triple from ` B\' ` back to ` A ` leaving the counter ` Q\' ` on ` I\' ` and the verdict '
               'in ` N\' ` (T7: ~ tm2fincr , ~ tm2fdup twice, ~ tm2fcmp ) --- completes it.  Lean: '
               '` dmUpBody_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, b0l, bpl = c[LAB('A')], c[LAB('B0')], c[LAB("B'")]
    jj, ip = c['J e. %s' % DG], c["I' e. %s" % DG]
    c0t, qq, z0j, qpw, tt = c[CTY('C0')], c[STMT('Q')], c['Z0 e. %s' % GJ], c[WRD("Q'", GIP)], c["T' e. NN0"]
    dd, nss, n2s, ht, trip = c[STKD('D')], c[SSS('N')], c[SSS("N'")], c[HT('N')], c[TRIP_UB]
    C0 = CLN('A', 'N', 'D'); C1 = CLN('B0', 'N', 'D'); C2 = CLN("B'", 'N', D1)
    t1 = brstep(w, ph, 'tm2lbrt', phm, c[MEQ('A', STM_UT)], al, b0l, dd, c0t, qq, nss, ht, 'A', 'B0', 'N', 'D')
    bld2 = bldr(w, ph, c, phm)
    s2, c2 = inst(w, ph, 'tm2fpshn', {'A': 'B0', 'E': "B'", 'K': 'J', 'Z': 'Z0'}, bld2)
    C2a, D2c, B2 = triple_parts(c2)
    assert C2a == C1 and D2c == C2, (C2a, D2c)
    t12 = hrseq(w, ph, phm, t1, s2, C0, C1, C2, '1', '1')
    POST = CLN('A', "N'", UP(D1, "I'", "Q'"))
    tall = hrseq(w, ph, phm, t12, trip, C0, C2, POST, '( 1 + 1 )', "T'")
    bound(w, ph, phm, tall, C0, POST, "( ( 1 + 1 ) + T' )", "( T' + 2 )", {"T'": tt}, qed=True)
    return w.run()


IFU = '( j e. NN0 |-> %s )' % CLN('A', NF('j'), DPU('j'))
BODYU = CLN('A', NF('j'), DPU('j'))
T2 = "( T' + 2 )"


def dpufacts(w, ph, X, tv, dd, jj, ip, njip, yw, qw):
    """DPU( X ) e. Stk, ( DPU( X ) ` J ) = ( Y ` X )"""
    a = updcl(w, ph, 'D', 'J', YF(X), tv, dd, jj, yw)
    d = updcl(w, ph, UP('D', 'J', YF(X)), "I'", QF(X), tv, a, ip, qw)
    v1 = updnv(w, ph, UP('D', 'J', YF(X)), "I'", QF(X), 'J', tv, a, ip, elv(w, ph, qw, QF(X)), jj, njip)
    v2 = updkv(w, ph, 'D', 'J', YF(X), tv, dd, jj, elv(w, ph, yw, YF(X)))
    vj = w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, DPU(X), YF(X)))
    return d, vj


def tm2fdmuq():
    lab = 'tm2fdmuq'
    tree, ph = TREE_DMUQ, cj(TREE_DMUQ)
    w = W(lab, 'The shift-up loop of ` divmod ` from its test label ` A ` : the divisor on ` J ` is '
               'doubled and the counter on ` I\' ` incremented until the comparison verdict in the '
               'state class ` ( N ` i ) ` stops the loop, the composite of each iteration a hypothesis '
               'triple (blueprint D4); ~ tm2hitr over ` ( 0 ..^ R ) ` with ~ tm2fdmub at each '
               'iteration and ~ tm2stkup4 for the seam.  Lean: ` Frag.loop_runs ` at ` DmUpInv ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, b0l, bpl, el = c[LAB('A')], c[LAB('B0')], c[LAB("B'")], c[LAB('E')]
    jj, ip, njip = c['J e. %s' % DG], c["I' e. %s" % DG], c["J =/= I'"]
    c0t, z0j, dd, rr, tt = c[CTY('C0')], c['Z0 e. %s' % GJ], c[STKD('D')], c['R e. NN0'], c["T' e. NN0"]
    fam, hyps = c[FAM_UQ], c[HYPS_UQ]
    ge = gotocl(w, ph, tv, 'E', el)

    def famat(ph2, X, xfz, Lf):
        st, _ = inst_v(w, ph2, Lf(fam, FAM_UQ), cj(FAMB_UQ('i')), 'i', X, xfz)
        cx = Ctx(w, ph2, FAMB_UQ(X), root=st)
        return dict(yw=cx[WRD(YF(X), GJ)], qw=cx[WRD(QF(X), GIP)], nss=cx[SSS(NF(X))])

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
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS_UQ), cj(HYP_UQ_TREE('i')), 'i', 'k', kin)
    ck = Ctx(w, pk, HYP_UQ_TREE('k'), root=hyk)
    K1 = '( k + 1 )'
    ystep, htk, tripk = ck['%s = %s' % (YF(K1), CC(S1('Z0'), YF('k')))], ck[HT(NF('k'))], ck[TRIP_UQ('k')]
    tvk, ddk, jjk, ipk, njipk = Lk(tv, 'T e. V'), Lk(dd, STKD('D')), Lk(jj, 'J e. %s' % DG), Lk(ip, "I' e. %s" % DG), Lk(njip, "J =/= I'")
    dpk, vj = dpufacts(w, pk, 'k', tvk, ddk, jjk, ipk, njipk, fk['yw'], fk['qw'])
    # the hypothesis triple in tm2fdmub's text: Z0 ++ ( DPU(k) ` J ) = Y_{k+1}
    ZDJ = CC(S1('Z0'), '( %s ` J )' % DPU('k'))
    zdj = w.s([w.s([vj], 'oveq2d', '( %s -> %s = %s )' % (pk, ZDJ, CC(S1('Z0'), YF('k')))), w.s([ystep], 'eqcomd', '( %s -> %s = %s )' % (pk, CC(S1('Z0'), YF('k')), YF(K1)))],
              'eqtrd', '( %s -> %s = %s )' % (pk, ZDJ, YF(K1)))
    zdjc = w.s([zdj], 'eqcomd', '( %s -> %s = %s )' % (pk, YF(K1), ZDJ))
    PRE_H = UP(DPU('k'), 'J', YF(K1)); PRE_B = UP(DPU('k'), 'J', ZDJ)
    eqp = upeq(w, pk, DPU('k'), 'J', zdjc, YF(K1), ZDJ)
    tripk2, _, _, _ = hrrw(w, pk, tripk, CLN("B'", NF('k'), PRE_H), CLN('A', NF(K1), UP(PRE_H, "I'", QF(K1))), "T'",
                           ceq=clneq(w, pk, "B'", NF('k'), eqp, PRE_H, PRE_B))
    # post rewrite: UP( PRE_H , I' , Q_{k+1} ) = UP( PRE_B , I' , Q_{k+1} )
    a1 = w.s([eqp], 'reseq1d', '( %s -> ( %s |` ( %s \\ { I\' } ) ) = ( %s |` ( %s \\ { I\' } ) ) )' % (pk, PRE_H, DG, PRE_B, DG))
    a2 = w.s([a1], 'uneq1d', '( %s -> %s = %s )' % (pk, UP(PRE_H, "I'", QF(K1)), UP(PRE_B, "I'", QF(K1))))
    tripk3, _, _, _ = hrrw(w, pk, tripk2, CLN("B'", NF('k'), PRE_B), CLN('A', NF(K1), UP(PRE_H, "I'", QF(K1))), "T'",
                           deq=clneq(w, pk, 'A', NF(K1), a2, UP(PRE_H, "I'", QF(K1)), UP(PRE_B, "I'", QF(K1))))
    MAPK = {'N': NF('k'), "N'": NF(K1), 'D': DPU('k'), "Q'": QF(K1), 'Q': GT('E')}
    instk = ren(TREE_DMUB, MAPK)
    assert sub(TRIP_UB, MAPK) == concl(w, pk, tripk3)
    derived = {STKD(DPU('k')): dpk, WRD(QF(K1), GIP): fk1['qw'], SSS(NF('k')): fk['nss'], SSS(NF(K1)): fk1['nss'],
               HT(NF('k')): htk, sub(TRIP_UB, MAPK): tripk3, STMT(GT('E')): Lk(ge, STMT(GT('E'))),
               MEQ('A', STM_UTE): Lk(c[MEQ('A', STM_UTE)], MEQ('A', STM_UTE))}
    def look(t):
        if t in derived:
            return derived[t]
        return Lk(c[t], t)
    POSTK = sub(UP(UP('D', 'J', Z0DJ), "I'", "Q'"), MAPK)
    trik = applylem(w, pk, 'tm2fdmub', leafsteps(instk, look), TRI(CLN('A', NF('k'), DPU('k')), CLN('A', NF(K1), POSTK), T2))
    # collapse: POSTK = UP( UP( DPU(k) , J , ZDJ ) , I' , Q_{k+1} ) -> UP( UP( DPU(k) , J , Y_{k+1} ) , I' , Q_{k+1} ) -> DPU( k + 1 )
    col = up4(w, pk, 'D', 'J', YF('k'), "I'", QF('k'), YF(K1), QF(K1), tvk, ddk, njipk, jjk, fk['yw'], fk1['yw'], ipk, fk['qw'], fk1['qw'])
    tbl = {ZDJ: (YF(K1), zdj), UP(UP(DPU('k'), 'J', YF(K1)), "I'", QF(K1)): (DPU(K1), col)}
    ps, postn = evaluate(w, pk, POSTK, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert postn == DPU(K1), postn
    trik2, _, _, _ = hrrw(w, pk, trik, CLN('A', NF('k'), DPU('k')), CLN('A', NF(K1), POSTK), T2, deq=clneq(w, pk, 'A', NF(K1), ps, POSTK, DPU(K1)))
    CLk, CLk1 = CLN('A', NF('k'), DPU('k')), CLN('A', NF(K1), DPU(K1))
    jvk = ifval(w, pk, IFU, BODYU, 'k', knn, CLk, clnex(w, pk, 'A', NF('k'), DPU('k')))
    jvk1 = ifval(w, pk, IFU, BODYU, K1, k1nn, CLk1, clnex(w, pk, 'A', NF(K1), DPU(K1)))
    trik3, _, _, _ = hrrw(w, pk, trik2, CLk, CLk1, T2,
                          ceq=w.s([jvk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (pk, CLk, IFU)),
                          deq=w.s([jvk1], 'eqcomd', '( %s -> %s = ( %s ` ( k + 1 ) ) )' % (pk, CLk1, IFU)))
    HYPI = 'A. k e. ( 0 ..^ R ) %s' % TRI('( %s ` k )' % IFU, '( %s ` ( k + 1 ) )' % IFU, T2)
    hypi = w.s([trik3], 'ralrimiva', '( %s -> %s )' % (ph, HYPI))
    # ---------------- tm2hitr
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ R )' % ph)
    z0fz = fzmem(ph, '0', z0a, ge0, rr)
    rnn = w.s([rr, w.inst('nn0red')], 'syl', '( %s -> R e. RR )' % ph)
    rle = w.s([rnn, w.inst('leidd')], 'syl', '( %s -> R <_ R )' % ph)
    rfz = fzmem(ph, 'R', rr, rle, rr)
    f0 = famat(ph, '0', z0fz, lambda st, f: st)
    dp0, _ = dpufacts(w, ph, '0', tv, dd, jj, ip, njip, f0['yw'], f0['qw'])
    CL0, CLR = CLN('A', NF('0'), DPU('0')), CLN('A', NF('R'), DPU('R'))
    jv0 = ifval(w, ph, IFU, BODYU, '0', z0a, CL0, clnex(w, ph, 'A', NF('0'), DPU('0')))
    jvR = ifval(w, ph, IFU, BODYU, 'R', rr, CLR, clnex(w, ph, 'A', NF('R'), DPU('R')))
    ss0 = cfgcl(w, ph, 'A', NF('0'), DPU('0'), tv, al, f0['nss'], dp0)
    ss0j = w.s([jv0, ss0], 'eqsstrd', '( %s -> ( %s ` 0 ) C_ %s )' % (ph, IFU, CFG_T))
    t2n = nn0cl(w, ph, T2, {"T'": tt})
    pj = w.s([ss0j, t2n], 'jca', '( %s -> ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) )' % (ph, IFU, CFG_T, T2))
    ant = w.s([phm, pj, hypi], '3jca', '( %s -> ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) )' % (ph, PHM, IFU, CFG_T, T2, HYPI))
    RUN = TRI('( %s ` 0 )' % IFU, '( %s ` R )' % IFU, '( R x. %s )' % T2)
    itr0 = w.s([rr, w.inst('tm2hitr')], 'syl', '( %s -> ( ( %s /\\ ( ( %s ` 0 ) C_ %s /\\ %s e. NN0 ) /\\ %s ) -> %s ) )'
               % (ph, PHM, IFU, CFG_T, T2, HYPI, RUN))
    run = w.s([itr0, ant], 'mpd', '( %s -> %s )' % (ph, RUN))
    hrrw(w, ph, run, '( %s ` 0 )' % IFU, '( %s ` R )' % IFU, '( R x. %s )' % T2, ceq=jv0, deq=jvR, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fdmub'): tm2fdmub()
    if want('tm2fdmuq'): tm2fdmuq()
