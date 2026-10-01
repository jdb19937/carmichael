"""T-TAB: the slot loop ~ tm2ftfs (Lean ` forSlots_runs `) and ~ tm2fwup
(` walkUp_runs `): the peek of the marker before the loop and after every
body, the loop by ~ tm2floopu over the class family ` ( N `` i ) ` and the
stack family ` ( P `` i ) ` (blueprint D3, D4); ` walkUp ` pops the marker."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ttablib import *
from tpl_c_prim import ralk2i

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2ftfs():
    lab = 'tm2ftfs'
    tree, ph = TREE_FS, cj(TREE_FS)
    w = W(lab, 'The slot loop ` forSlots x body ` of the DP table (TM/Table.lean): ` peekBlank x ` at ` P0 ` sets the '
               'loop test from the top letter ` ( Z ` 0 ) ` of stack ` K ` (~ tm2lpk ), and ~ tm2floopu runs the loop '
               'at ` A ` over the class family ` ( N ` i ) ` and the stack family ` ( P ` i ) ` , each iteration the '
               'body (a hypothesis triple from ` B0 ` into ` B\' ` at the stacks ` ( P ` ( i + 1 ) ) ` ) followed by '
               '` peekBlank x ` at ` B\' ` , which reads ` ( Z ` ( i + 1 ) ) ` into ` ( N ` ( i + 1 ) ) ` .  The peeked '
               'letters and rests are the families ` ( Z ` i ) ` , ` ( X ` i ) ` on ` ( 0 ... R ) ` (blueprint D4).  '
               'Lean: ` forSlots_runs ` , bound ` sl.length * ( t + 2 ) + 2 ` .')
    c = Ctx(w, ph, tree)
    forslots(w, ph, c, qed=True)
    return w.run()


def forslots(w, ph, c, ren_=None, qed=True):
    """prove ( ph -> CONCL_FS[ren_] ) from the antecedent context c (whose leaves are TREE_FS's under ren_);
    returns the step (None if qed)"""
    m = ren_ or {}
    R_ = lambda t: sub(t, m) if m else t
    phm, geq = c[PHM], c[GEQ]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    mt = w.s([phm, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, 'M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T )'))
    fam, pkd, hyps, rr = c[FAM_L], c[PKD], c[HYPS_FS], c['R e. NN0']
    tpn = c["T' e. NN0"]
    TP1 = "( T' + 1 )"
    # ---------------- the iteration at k: body triple, then the peek at B'
    pk = '( %s /\\ k e. ( 0 ..^ R ) )' % ph
    Lk = Lifter(w, pk)
    kin, kfz, k1fz, knn, k1nn = kfacts(w, pk)
    K1 = '( k + 1 )'
    fk = famat(w, pk, Lk(fam, FAM_L), 'k', kfz)
    fk1 = famat(w, pk, Lk(fam, FAM_L), K1, k1fz)
    hyk, _ = inst_v(w, pk, Lk(hyps, HYPS_FS), cj(HYPF_FS('i')), 'i', 'k', kin)
    ck = Ctx(w, pk, HYPF_FS('k'), root=hyk)
    pd1, _ = inst_v(w, pk, Lk(pkd, PKD), PKDF('i'), 'i', K1, k1fz)
    cp1 = Ctx(w, pk, PKDT(K1), root=pd1)

    class LC:
        def __getitem__(self, t):
            return Lk(c[t], t)
    ex = {'T e. V': Lk(tv, 'T e. V'), 'M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T )': Lk(mt, 'M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T )'),
          STKD(PF(K1)): fk1['pst'], SSS(N1F('k')): ck[SSS(N1F('k'))], SSS(NF(K1)): fk1['nss'],
          HPK(N1F('k'), 'F', ZF(K1), NF(K1)): ck[HPK(N1F('k'), 'F', ZF(K1), NF(K1))]}
    ex['( ( P ` %s ) ` K ) = %s' % (K1, CC(S1(ZF(K1)), XF(K1)))] = cp1['( ( P ` %s ) ` K ) = %s' % (K1, CC(S1(ZF(K1)), XF(K1)))]
    ex['%s e. %s' % (ZF(K1), GAM)] = cp1['%s e. %s' % (ZF(K1), GAM)]
    ex['%s e. %s' % (XF(K1), GAMW)] = cp1['%s e. %s' % (XF(K1), GAMW)]
    bld = Builder(w, pk, LC(), ex)
    pks, cc = inst(w, pk, 'tm2lpk', {'A': "B'", 'E': 'A', 'K': 'K', 'F': 'F', 'D': PF(K1), 'Z': ZF(K1), 'X': XF(K1),
                                     'N': N1F('k'), "N'": NF(K1)}, bld)
    CB0, CBp, CA1 = CLN('B0', NF('k'), PF('k')), CLN("B'", N1F('k'), PF(K1)), CLN('A', NF(K1), PF(K1))
    assert triple_parts(cc)[:2] == (CBp, CA1), cc
    trk = ck[BODY_FS('k')]
    t2 = hrseq(w, pk, Lk(phm, PHM), trk, pks, CB0, CBp, CA1, "T'", '1')
    htk = ck[HT(NF('k'))]
    body_k = '( %s /\\ %s )' % (HT(NF('k')), BODY_L('k', TP1))
    body_i = '( %s /\\ %s )' % (HT(NF('i')), BODY_L('i', TP1))
    pair = w.s([htk, t2], 'jca', '( %s -> %s )' % (pk, body_k))
    hypk = w.s([pair], 'ralrimiva', '( %s -> A. k e. ( 0 ..^ R ) %s )' % (ph, body_k))
    hypi = ralk2i(w, ph, hypk, body_k, body_i)
    # ---------------- the loop (tm2floopu at T' := ( T' + 1 ))
    tp1n = w.s([tpn, w.inst('peano2nn0')], 'syl', "( %s -> %s e. NN0 )" % (ph, TP1))
    HYPS_U = sub(HYPS_LU, {"T'": TP1})
    extra = {HYPS_U: hypi, '%s e. NN0' % TP1: tp1n}
    st, txt = jtree(w, ph, leafsteps(ren(TREE_LOOPU, {"T'": TP1}), lambda t: extra[t] if t in extra else c[t]))
    LOOPB = "( ( R x. ( %s + 1 ) ) + 1 )" % TP1
    lp = w.s([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ph, TRI(CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R')), LOOPB)))
    # ---------------- the prologue peek at P0
    f0 = famat(w, ph, fam, '0', zmem(w, ph, rr))
    z0 = w.s([], '0nn0', '0 e. NN0')
    pd0, _ = inst_v(w, ph, pkd, PKDF('i'), 'i', '0', zmem(w, ph, rr))
    cp0 = Ctx(w, ph, PKDT('0'), root=pd0)
    ex0 = {'T e. V': tv, 'M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T )': mt, STKD(PF('0')): f0['pst'], SSS(NF('0')): f0['nss']}
    for t in ('( ( P ` 0 ) ` K ) = %s' % CC(S1(ZF('0')), XF('0')), '%s e. %s' % (ZF('0'), GAM), '%s e. %s' % (XF('0'), GAMW)):
        ex0[t] = cp0[t]
    bld0 = Builder(w, ph, c, ex0)
    p0, cc0 = inst(w, ph, 'tm2lpk', {'A': 'P0', 'E': 'A', 'K': 'K', 'F': 'F', 'D': PF('0'), 'Z': ZF('0'), 'X': XF('0'),
                                      'N': 'O', "N'": NF('0')}, bld0)
    C0, CA0, CE = CLN('P0', 'O', PF('0')), CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R'))
    s = hrseq(w, ph, phm, p0, lp, C0, CA0, CE, '1', LOOPB)
    # ( R x. ( ( T' + 1 ) + 1 ) ) = ( R x. ( T' + 2 ) )
    tpc = w.s([tpn], 'nn0cnd', "( %s -> T' e. CC )" % ph)
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % ph)
    as_ = w.s([tpc, onea, onea], 'addassd', "( %s -> ( ( T' + 1 ) + 1 ) = ( T' + ( 1 + 1 ) ) )" % ph)
    t2e = w.s([], '1p1e2', '( 1 + 1 ) = 2'); t2ea = w.s([t2e], 'a1i', '( %s -> ( 1 + 1 ) = 2 )' % ph)
    as2 = w.s([t2ea], 'oveq2d', "( %s -> ( T' + ( 1 + 1 ) ) = ( T' + 2 ) )" % ph)
    as3 = w.s([as_, as2], 'eqtrd', "( %s -> ( ( T' + 1 ) + 1 ) = ( T' + 2 ) )" % ph)
    rq = w.s([as3], 'oveq2d', "( %s -> ( R x. ( ( T' + 1 ) + 1 ) ) = ( R x. ( T' + 2 ) ) )" % ph)
    n = '( 1 + %s )' % LOOPB
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    t2n = w.s([tpn, twoa], 'nn0addcld', "( %s -> ( T' + 2 ) e. NN0 )" % ph)
    rt2 = w.s([rr, t2n], 'nn0mulcld', "( %s -> ( R x. ( T' + 2 ) ) e. NN0 )" % ph)
    rt1 = w.s([rq, rt2], 'eqeltrd', "( %s -> ( R x. ( ( T' + 1 ) + 1 ) ) e. NN0 )" % ph)
    return bound(w, ph, phm, s, C0, CE, n, BND_FS,
                 {"( R x. ( T' + 2 ) )": rt2, "( R x. ( ( T' + 1 ) + 1 ) )": rt1},
                 hyps=[rq, w.s([rt2], 'nn0ge0d', "( %s -> 0 <_ ( R x. ( T' + 2 ) ) )" % ph)], qed=qed), tv, mt


def rtcl(w, ph, rr, tpn):
    """( ph -> ( R x. ( T' + 2 ) ) e. NN0 )"""
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    t2n = w.s([tpn, twoa], 'nn0addcld', "( %s -> ( T' + 2 ) e. NN0 )" % ph)
    return w.s([rr, t2n], 'nn0mulcld', "( %s -> ( R x. ( T' + 2 ) ) e. NN0 )" % ph)


def popat(w, ph, c, tv, mt, extra, A, E, K, F, D, Z, X, N, N2, ref='tm2lpop'):
    """tm2lpop / tm2lpk at label A, the antecedent's leaves from c and extra"""
    ex = {'T e. V': tv, 'M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T )': mt}
    ex.update(extra)
    bld = Builder(w, ph, c, ex)
    return inst(w, ph, ref, {'A': A, 'E': E, 'K': K, 'F': F, 'D': D, 'Z': Z, 'X': X, 'N': N, "N'": N2}, bld)


def walkup(w, ph, c, m=None, qed=False):
    """( ph -> CONCL_WUP[m] ) by tm2ftfs and the pop at E; c a Ctx containing TREE_WUP[m]'s leaves"""
    m = m or {}
    r = lambda t: sub(t, m) if m else t
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    mt = w.s([phm, w.inst('simpr')], 'syl', '( %s -> M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T ) )' % ph)
    fsst = c[cj(ren(TREE_FS, m))]
    fs = w.s([fsst, w.inst('tm2ftfs')], 'syl', '( %s -> %s )' % (ph, r(CONCL_FS)))
    rr, fam, pkd = c['R e. NN0'], c[FAM_L], c[PKD]
    fR = famat(w, ph, fam, 'R', rmem(w, ph, rr))
    pdR, _ = inst_v(w, ph, pkd, PKDF('i'), 'i', 'R', rmem(w, ph, rr))
    cpR = Ctx(w, ph, PKDT('R'), root=pdR)
    ex = {STKD(PF('R')): fR['pst'], SSS(NF('R')): fR['nss']}
    for t in PKDT('R'):
        ex[t] = cpR[t]
    pp, cc = popat(w, ph, c, tv, mt, ex, 'E', "E'", 'K', 'F"', PF('R'), ZF('R'), XF('R'), NF('R'), "N'")
    C0, CE, CEp = r(CLN('P0', 'O', PF('0'))), CLN('E', NF('R'), PF('R')), CLN("E'", "N'", UPR)
    assert triple_parts(cc)[:2] == (CE, CEp), cc
    s = hrseq(w, ph, phm, fs, pp, C0, CE, CEp, BND_FS, '1')
    rt2 = rtcl(w, ph, rr, c["T' e. NN0"])
    return bound(w, ph, phm, s, C0, CEp, '( %s + 1 )' % BND_FS, BND_WUP, {"( R x. ( T' + 2 ) )": rt2},
                 hyps=[w.s([rt2], 'nn0ge0d', "( %s -> 0 <_ ( R x. ( T' + 2 ) ) )" % ph)], qed=qed)


def tm2fwup():
    lab = 'tm2fwup'
    tree, ph = TREE_WUP, cj(TREE_WUP)
    w = W(lab, 'The walk back ` walkUp tbl j s scr ` of the DP table (TM/Table.lean): ` forSlots scr ( moveSlot scr '
               'tbl s j ) ` is ~ tm2ftfs (the body ` moveSlot ` one hypothesis triple per slot, blueprint D3), then '
               '` popTop scr ` removes the marker ` ( Z ` R ) ` (~ tm2lpop ).  Lean: ` walkUp_runs ` , bound '
               '` R.length * ( slotC N b + 2 ) + 3 ` at ` T\' := slotC N b ` .')
    c = Ctx(w, ph, tree)
    walkup(w, ph, c, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2ftfs'): tm2ftfs()
    if want('tm2fwup'): tm2fwup()
