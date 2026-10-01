"""T-TAB: ~ tm2fdpl (Lean ` dropList_runs `: T6's entry loop with the body
` dropNum ` one triple, then ` popTop `), ~ tm2fwdn (` walkDown_runs `: push the
marker, the counter's ` isZero ` triple, the counted loop by ~ tm2floopu , the
counter's ` dropNum ` triple) and ~ tm2fetb (` emptyTbl_runs ` : ~ tm2fwdn with
the body's push of ` ket ` executed, ` emptyBody_runs `)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ttablib import *
from tpl_c_prim import ralk2i
from tpl_f_list import poptopnl
from ttab_b_slot import LCtx, phmparts, instc, pushat, MTY

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fdpl():
    lab = 'tm2fdpl'
    tree, ph = TREE_DPL, cj(TREE_DPL)
    w = W(lab, 'Dropping a list, ` dropList x ` (TM/Table.lean): ` forEntries x ( dropNum x ) ` is ~ tm2lfe with the '
               'body ` dropNum x ` one hypothesis triple per entry (T7: ~ tm2fdrop ), and ` popTop x ` removes the '
               '` bra ` (~ tm2lpop ).  Lean: ` dropList_runs ` , bound ` L.length * ( m + 3 ) + 3 ` at ` Y := m + 1 ` .')
    c = Ctx(w, ph, tree)
    cf = Ctx(w, ph, T_PHF, root=c[fe.PHF])
    phm = cf[PHM]
    u = dict(phm=phm, pk=cf[fe.PK], pty=cf[fe.PTY], nss=cf['N C_ %s' % SS],
             nl=w.s([cf['L e. %s' % WWB], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL)))
    lfe, cc = inst(w, ph, 'tm2lfe', {}, Builder(w, ph, cf))
    LB = '( ( %s x. ( Y + 2 ) ) + 2 )' % NL
    C1, C2 = CL('P1', 'N', PF('0')), CL('E', NFIN, PF(NL))
    assert triple_parts(cc) == (C1, C2, LB), cc
    pop, Ca, Dc = poptopnl(w, ph, c, u, 'E', "E'", "N'")
    w.qed([phm, lfe, pop], 'syl3anc', '( %s -> %s )' % (ph, HR(C1, 'T', 'M', Dc, '( %s + 1 )' % LB)))
    return w.run()


def rt(w, ph, rr, tn, T):
    """( ph -> ( R x. T ) e. NN0 ) from tn : ( ph -> T e. NN0 )"""
    return w.s([rr, tn], 'nn0mulcld', '( %s -> ( R x. %s ) e. NN0 )' % (ph, T))


def walkdown(w, ph, c, tree, concl, qed):
    phm = c[PHM]
    tv, mt = phmparts(w, ph, phm)
    ps, pc = pushat(w, ph, c, tv, mt, {}, 'P0', 'P1', 'K', 'Y', 'O', 'D')
    C0, C1, C2, C3, C4 = (CLN('P0', 'O', 'D'), CLN('P1', 'O', YPUSH('D', 'K', 'Y')), CLN('A', NF('0'), PF('0')),
                          CLN('E', NF('R'), PF('R')), CLN("E'", "N'", "D'"))
    assert triple_parts(pc)[:2] == (C0, C1), pc
    lp = applylem(w, ph, 'tm2floopu', leafsteps(TREE_LOOPU, lambda t: c[t]), CONCL_LOOPU)
    LB = "( ( R x. ( T' + 1 ) ) + 1 )"
    q = hrseq(w, ph, phm, ps, c[TRIP_WD0], C0, C1, C2, '1', 'U')
    q = hrseq(w, ph, phm, q, lp, C0, C2, C3, '( 1 + U )', LB)
    q = hrseq(w, ph, phm, q, c[TRIP_WDX], C0, C3, C4, '( ( 1 + U ) + %s )' % LB, "U'")
    tp1 = w.s([c["T' e. NN0"], w.inst('peano2nn0')], 'syl', "( %s -> ( T' + 1 ) e. NN0 )" % ph)
    return bound0(w, ph, phm, q, C0, C4, "( ( ( 1 + U ) + %s ) + U' )" % LB, triple_parts(concl)[2],
                  {'U': c['U e. NN0'], "U'": c["U' e. NN0"], "( R x. ( T' + 1 ) )": rt(w, ph, c['R e. NN0'], tp1, "( T' + 1 )")},
                  qed=qed)


def tm2fwdn():
    lab = 'tm2fwdn'
    tree, ph = TREE_WDN, cj(TREE_WDN)
    w = W(lab, 'The counted walk ` walkDown tbl j s scr ` of the DP table (TM/Table.lean), alphabet-free: ` pushSym scr '
               'blank ` pushes the marker ` Y ` on ` K ` (~ tm2fpshn ), ` isZero j s ` is a hypothesis triple into the '
               'loop\'s family at ` 0 ` , the loop ~ tm2floopu runs ` R ` iterations of the body ` walkBody = moveSlot ; '
               'predNum ; isZero ` (one triple, blueprint D3), and ` dropNum j ` is a triple.  Lean: ` walkDown_runs ` .')
    c = Ctx(w, ph, tree)
    walkdown(w, ph, c, tree, CONCL_WDN, True)
    return w.run()


def tm2fetb():
    lab = 'tm2fetb'
    tree, ph = TREE_ETB, cj(TREE_ETB)
    w = W(lab, 'The empty table ` emptyTbl c tbl s ` (TM/Table.lean), alphabet-free: ~ tm2fwdn whose loop body '
               '` emptyBody = pushSym tbl ket ; predNum c s ; isZero c s ` pushes the letter ` Y\' ` on ` K ` '
               '(~ tm2fpshn , executed at every iteration) and runs ` predNum ; isZero ` as one hypothesis triple.  '
               'Lean: ` emptyTbl_runs ` with ` emptyBody_runs ` , bound ` L * ( 4 log L + 14 ) + 2 log L + 11 ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv, mt = phmparts(w, ph, phm)
    hyps, fam, rr, tpn = c[HYPS_ETB], c[FAM_L], c['R e. NN0'], c["T' e. NN0"]
    TP1 = "( T' + 1 )"
    pk = '( %s /\\ k e. ( 0 ..^ R ) )' % ph
    L = LCtx(w, pk, c)
    kin, kfz, k1fz, knn, k1nn = kfacts(w, pk)
    K1 = '( k + 1 )'
    fk = famat(w, pk, L[FAM_L], 'k', kfz)
    bodyi = '( %s /\\ %s )' % (HT(NF('i')), BODY_ETB('i'))
    hyk, _ = inst_v(w, pk, L[HYPS_ETB], bodyi, 'i', 'k', kin)
    ck = Ctx(w, pk, (HT(NF('k')), BODY_ETB('k')), root=hyk)
    ps, pc = pushat(w, pk, L, L.L(tv, 'T e. V'), L.L(mt, MTY), {STKD(PF('k')): fk['pst'], SSS(NF('k')): fk['nss']},
                    'B0', "B'", 'K', "Y'", NF('k'), PF('k'))
    CB0, CBp, CA1 = CLN('B0', NF('k'), PF('k')), CLN("B'", NF('k'), YPUSH(PF('k'), 'K', "Y'")), CLN('A', NF(K1), PF(K1))
    assert triple_parts(pc)[:2] == (CB0, CBp), pc
    t2 = hrseq(w, pk, L[PHM], ps, ck[BODY_ETB('k')], CB0, CBp, CA1, '1', "T'")
    tpc = w.s([L["T' e. NN0"]], 'nn0cnd', "( %s -> T' e. CC )" % pk)
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % pk)
    com = w.s([onea, tpc], 'addcomd', "( %s -> ( 1 + T' ) = ( T' + 1 ) )" % pk)
    t2r, _, _, _ = hrrw(w, pk, t2, CB0, CA1, "( 1 + T' )", neq=com)
    body_k = '( %s /\\ %s )' % (HT(NF('k')), BODY_L('k', TP1))
    body_i = '( %s /\\ %s )' % (HT(NF('i')), BODY_L('i', TP1))
    pair = w.s([ck[HT(NF('k'))], t2r], 'jca', '( %s -> %s )' % (pk, body_k))
    hypk = w.s([pair], 'ralrimiva', '( %s -> A. k e. ( 0 ..^ R ) %s )' % (ph, body_k))
    hypi = ralk2i(w, ph, hypk, body_k, body_i)
    tp1n = w.s([tpn, w.inst('peano2nn0')], 'syl', "( %s -> %s e. NN0 )" % (ph, TP1))
    extra = {sub(HYPS_LU, {"T'": TP1}): hypi, '%s e. NN0' % TP1: tp1n}
    CW = sub(CONCL_WDN, {"T'": TP1})
    wd = applylem(w, ph, 'tm2fwdn', leafsteps(ren(TREE_WDN, {"T'": TP1}), lambda t: extra[t] if t in extra else c[t]), CW)
    C0, C4, n = triple_parts(CW)
    # ( R x. ( ( T' + 1 ) + 1 ) ) = ( R x. ( T' + 2 ) )
    tpc0 = w.s([tpn], 'nn0cnd', "( %s -> T' e. CC )" % ph)
    one0 = w.s([one], 'a1i', '( %s -> 1 e. CC )' % ph)
    as_ = w.s([tpc0, one0, one0], 'addassd', "( %s -> ( ( T' + 1 ) + 1 ) = ( T' + ( 1 + 1 ) ) )" % ph)
    t2e = w.s([], '1p1e2', '( 1 + 1 ) = 2'); t2ea = w.s([t2e], 'a1i', '( %s -> ( 1 + 1 ) = 2 )' % ph)
    as2 = w.s([t2ea], 'oveq2d', "( %s -> ( T' + ( 1 + 1 ) ) = ( T' + 2 ) )" % ph)
    as3 = w.s([as_, as2], 'eqtrd', "( %s -> ( ( T' + 1 ) + 1 ) = ( T' + 2 ) )" % ph)
    rq = w.s([as3], 'oveq2d', "( %s -> ( R x. ( ( T' + 1 ) + 1 ) ) = ( R x. ( T' + 2 ) ) )" % ph)
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    t2n = w.s([tpn, twoa], 'nn0addcld', "( %s -> ( T' + 2 ) e. NN0 )" % ph)
    rt2 = rt(w, ph, rr, t2n, "( T' + 2 )")
    rt1 = w.s([rq, rt2], 'eqeltrd', "( %s -> ( R x. ( ( T' + 1 ) + 1 ) ) e. NN0 )" % ph)
    bound0(w, ph, phm, wd, C0, C4, n, triple_parts(CONCL_ETB)[2],
           {'U': c['U e. NN0'], "U'": c["U' e. NN0"], "( R x. ( T' + 2 ) )": rt2, "( R x. ( ( T' + 1 ) + 1 ) )": rt1},
           hyps=[rq], qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fdpl'): tm2fdpl()
    if want('tm2fwdn'): tm2fwdn()
    if want('tm2fetb'): tm2fetb()
