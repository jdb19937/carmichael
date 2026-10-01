"""T-MD: ` divmodCore ` , ` divmod ` , ` divFrag ` , ` modFrag ` of TM/MulDiv.lean assembled
(blueprint 6.1, the hypothesis-triple style of D4): ~ tm2fdmc1 (` pushNum j 0 ` ~ tm2fpshn ,
the ` dup ; dup ; cmpFrag ` triple, the shift-up loop ~ tm2fdmuq , its failed test ~ tm2fbrg ,
` pushSym q comma ` ~ tm2fpshn , the ` isZero ` triple), ~ tm2fdmc2 (the shift-down loop
~ tm2fdmdq , its failed test, ` dropNum j ` ~ tm2fdrop ), ~ tm2fdmc their sequence
(` divmodCore_runs `), ~ tm2fdm (` dropNum y ` , ` divmod_runs `), ~ tm2fdiv (` dropNum x ` ,
` divFrag_runs `), ~ tm2fmod (` dropNum q ` , ` modFrag_runs `)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

NP = lambda i: "( N' ` %s )" % i
YPF = lambda i: "( Y' ` %s )" % i
QPF = lambda i: "( Q' ` %s )" % i
FAMB_UQ_ = lambda i: ren(FAMB_UQ(i), UPMAP)


def fzmem(w, ph, X, xnn, xle, rr, R='R'):
    return w.s([w.s([xnn, rr, xle], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, X, R, X, R)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, X, R))


def rmem(w, ph, rr, R='R'):
    """( ph -> R e. ( 0 ... R ) )"""
    rnn = w.s([rr, w.inst('nn0red')], 'syl', '( %s -> %s e. RR )' % (ph, R))
    rle = w.s([rnn, w.inst('leidd')], 'syl', '( %s -> %s <_ %s )' % (ph, R, R))
    return fzmem(w, ph, R, rr, rle, rr, R)


def tm2fdmc1():
    lab = 'tm2fdmc1'
    tree, ph = TREE_DMC1, cj(TREE_DMC1)
    w = W(lab, 'The first half of ` divmodCore ` (TM/MulDiv.lean): ` pushNum j 0 ` pushes the terminator '
               'on the counter ` I\' ` (~ tm2fpshn ), ` dup y t s ; dup x s t ; cmpFrag t s ` is a hypothesis '
               'triple into the shift-up loop\'s family (T7: ~ tm2fdup twice, ~ tm2fcmp ), the loop '
               '~ tm2fdmuq runs ` R ` iterations, its test fails (~ tm2fbrg ), ` pushSym q comma ` starts '
               'the quotient on ` I ` (~ tm2fpshn ) and ` isZero j s ` is a triple into the shift-down '
               'loop\'s family ` ( P ` 0 ) ` (T7: ~ tm2fisz ).  Lean: the first four ` have ` of '
               '` divmodCore_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    p0l, p1l, al, b0l, bpl, el, e1l = [c[LAB(x)] for x in ('P0', 'P1', 'A', 'B0', "B'", 'E', 'E1')]
    kk, jj, ii, ip = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG], c["I' e. %s" % DG]
    nji, niip = c['J =/= I'], c["I =/= I'"]
    c0t, z0j, yip, yi = c[CTY('C0')], c['Z0 e. %s' % GJ], c['Y e. %s' % GIP], c['Y e. %s' % GI]
    dd, oss = c[STKD('D')], c[SSS('O')]
    rr, u1c, u2c, u0c = c['R e. NN0'], c["U' e. NN0"], c['U" e. NN0'], c['U0 e. NN0']
    fam, hyps, htf = c[FAM_UQ_], c[HYPS_UQ_], c[HTF(NP('R'))]
    tr1, tr2 = c[TRIP_C1], c[TRIP_C2]
    gb0 = gotocl(w, ph, tv, 'B0', b0l)
    # ---- stage 1: push Y on I' at P0
    C0 = CLN('P0', 'O', 'D')
    bld1 = bldr(w, ph, c, phm)
    s1, c1 = inst(w, ph, 'tm2fpshn', {'A': 'P0', 'E': 'P1', 'K': "I'", 'Z': 'Y', 'N': 'O'}, bld1)
    C1a, D1c, B1 = triple_parts(c1)
    C1 = CLN('P1', 'O', UP('D', "I'", YIP))
    assert C1a == C0 and D1c == C1, (C1a, D1c)
    # ---- stage 2: dup, dup, cmpFrag (the triple)
    C2 = CLN('A', NP('0'), DPU_('0'))
    s12 = hrseq(w, ph, phm, s1, tr1, C0, C1, C2, '1', 'U"')
    N2 = '( 1 + U" )'
    # ---- stage 3: the shift-up loop
    C3 = CLN('A', NP('R'), DPU_('R'))
    BU = "( R x. ( U' + 2 ) )"
    s3 = applylem(w, ph, 'tm2fdmuq', leafsteps(ren(TREE_DMUQ, UPMAP), lambda t: c[t]), TRI(C2, C3, BU))
    s123 = hrseq(w, ph, phm, s12, s3, C0, C2, C3, N2, BU)
    N3 = '( %s + %s )' % (N2, BU)
    # ---- stage 4: the failed test at A -> E on ( N' ` R )
    st, _ = inst_v(w, ph, fam, cj(FAMB_UQ_('i')), 'i', 'R', rmem(w, ph, rr))
    cx = Ctx(w, ph, FAMB_UQ_('R'), root=st)
    yrw, qrw, nrs = cx[WRD(YPF('R'), GJ)], cx[WRD(QPF('R'), GIP)], cx[SSS(NP('R'))]
    dj = updcl(w, ph, 'D', 'J', YPF('R'), tv, dd, jj, yrw)
    dpr = updcl(w, ph, UP('D', 'J', YPF('R')), "I'", QPF('R'), tv, dj, ip, qrw)
    s4 = applylem(w, ph, 'tm2fbrg', ((phm, c[MEQ('A', STM_UTE)]), (al, el, dpr), ((c0t, gb0), (nrs, htf))),
                  TRI(C3, CLN('E', NP('R'), DPU_('R')), '1'))
    C4 = CLN('E', NP('R'), DPU_('R'))
    s1234 = hrseq(w, ph, phm, s123, s4, C0, C3, C4, N3, '1')
    N4 = '( %s + 1 )' % N3
    # ---- stage 5: push Y on I at E
    bld5 = bldr(w, ph, c, phm, {STKD(DPU_('R')): dpr, SSS(NP('R')): nrs})
    s5, c5 = inst(w, ph, 'tm2fpshn', {'A': 'E', 'E': 'E1', 'K': 'I', 'Z': 'Y', 'N': NP('R'), 'D': DPU_('R')}, bld5)
    C5a, D5c, B5 = triple_parts(c5)
    D5x = UP(DPU_('R'), 'I', CC(S1('Y'), '( %s ` I )' % DPU_('R')))
    assert C5a == C4 and D5c == CLN('E1', NP('R'), D5x), (C5a, D5c)
    nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    v1 = updnv(w, ph, UP('D', 'J', YPF('R')), "I'", QPF('R'), 'I', tv, dj, ip, elv(w, ph, qrw, QPF('R')), ii, niip)
    v2 = updnv(w, ph, 'D', 'J', YPF('R'), 'I', tv, dd, jj, elv(w, ph, yrw, YPF('R')), ii, nij)
    v12 = w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` I ) = ( D ` I ) )' % (ph, DPU_('R')))
    r5, D5n = w.rewrite(D5x, {'( %s ` I )' % DPU_('R'): ('( D ` I )', v12)}, ph)
    D5 = UP(DPU_('R'), 'I', YDI)
    assert D5n == D5, D5n
    s5r, _, _, _ = hrrw(w, ph, s5, C5a, D5c, B5, deq=clneq(w, ph, 'E1', NP('R'), r5, D5x, D5))
    C5 = CLN('E1', NP('R'), D5)
    s15 = hrseq(w, ph, phm, s1234, s5r, C0, C4, C5, N4, '1')
    N5 = '( %s + 1 )' % N4
    # ---- stage 6: isZero (the triple)
    C6 = CLN("A'", NF('0'), PF('0'))
    s16 = hrseq(w, ph, phm, s15, tr2, C0, C5, C6, N5, 'U0')
    N6 = '( %s + U0 )' % N5
    bound(w, ph, phm, s16, C0, C6, N6, '( ( ( U" + U0 ) + ( R x. ( U\' + 2 ) ) ) + 3 )',
          {'R': rr, "U'": u1c, 'U"': u2c, 'U0': u0c}, qed=True)
    return w.run()


def dropstage(w, ph, c, phm, tv, A, E, k, Fh, Bc, Wd, Xr, D0, d0cl, dkeq, kk, yk, xrw, ww, Nc, ncs, hc, he):
    """the triple C( A , Nc , D0 ) ~~> C( E , S , UPD( D0 , k , Xr ) ) in ( ( # ` Wd ) + 1 ) by tm2fdrop at
    D := D0, given dkeq : ( ph -> ( D0 ` k ) = ( Wd ++ ( <" Y "> ++ Xr ) ) ), d0cl : D0 e. Stk,
    yk : Y e. Gk, xrw : Xr e. Word Gk, ww : Wd e. Word Bc, ncs : Nc C_ S, hc/he the handler interfaces"""
    YXR = CC(S1('Y'), Xr)
    yxw = ccatw(w, ph, s1w(w, ph, yk, 'Y', GX(k)), xrw, S1('Y'), Xr, GX(k))
    bld = bldr(w, ph, c, phm, {STKD(D0): d0cl, WRD(YXR, GX(k)): yxw, WRD(Xr, GX(k)): xrw, WRD(Wd, Bc): ww, hc[1]: hc[0], he[1]: he[0]})
    s, cc = inst(w, ph, 'tm2fdrop', {'A': A, 'E': E, 'K': k, 'F': Fh, 'C': "C'", 'B': Bc, 'X': Xr, 'W': Wd, 'D': D0}, bld)
    Ca, Dc, Bn = triple_parts(cc)
    PRE = UP(D0, k, CC(Wd, YXR))
    assert Ca == CLN(A, SS, PRE) and Dc == CLN(E, SS, UP(D0, k, Xr)), (Ca, Dc)
    u = upidv(w, ph, D0, k, CC(Wd, YXR), dkeq, tv, d0cl, kk)
    sr, _, _, _ = hrrw(w, ph, s, Ca, Dc, Bn, ceq=clneq(w, ph, A, SS, u, PRE, D0))
    if Nc != SS:
        sr = hrssc(w, ph, phm, sr, CLN(A, SS, D0), Dc, Bn, CLN(A, Nc, D0), clnss(w, ph, A, Nc, SS, D0, ncs))
    return sr, CLN(A, Nc, D0), Dc, Bn


def tm2fdmc2():
    lab = 'tm2fdmc2'
    tree, ph = TREE_DMC2, cj(TREE_DMC2)
    w = W(lab, 'The second half of ` divmodCore ` (TM/MulDiv.lean): the shift-down loop ~ tm2fdmdq runs '
               '` R\' ` iterations from its test label ` A\' ` , the test fails (~ tm2fbrg ) and ` dropNum j ` '
               'removes the exhausted counter ` W ` from ` I\' ` (~ tm2fdrop ).  Lean: the last ` have ` of '
               '` divmodCore_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    apl, aql, epl, gpl = c[LAB("A'")], c[LAB('A"')], c[LAB("E'")], c[LAB("G'")]
    ip = c["I' e. %s" % DG]
    cqt, fpt, yip, bip = c[CTY('C"')], c[RTY("F'", "I'")], c['Y e. %s' % GIP], c['B C_ %s' % GIP]
    rr = c["R' e. NN0"]
    fam, hyps, htf = c[FAM_DQ_], c[HYPS_DQ_], c[HTF("( N ` R' )", 'C"')]
    pje, ww, xqw, hc, he = c['( %s ` I\' ) = %s' % (PF("R'"), CC('W', CC(S1('Y'), 'X"')))], c[WRD('W', 'B')], c[WRD('X"', GIP)], c[HCDR_], c[HEDR_]
    gaq = gotocl(w, ph, tv, 'A"', aql)
    RP = "R'"
    # ---- stage 1: the shift-down loop
    C0 = CLN("A'", NF('0'), PF('0')); C1 = CLN("A'", NF(RP), PF(RP))
    BD = '( R\' x. %s )' % TD4
    s1 = applylem(w, ph, 'tm2fdmdq', leafsteps(ren(TREE_DMDQ, dict(DNMAP, R=RP)), lambda t: c[t]), TRI(C0, C1, BD))
    # ---- stage 2: the failed test at A' -> E' on ( N ` R' )
    st, _ = inst_v(w, ph, fam, cj(FAMB_DQ('i')), 'i', RP, rmem(w, ph, rr, RP))
    cx = Ctx(w, ph, FAMB_DQ(RP), root=st)
    prs, nrs = cx[STKD(PF(RP))], cx[SSS(NF(RP))]
    s2 = applylem(w, ph, 'tm2fbrg', ((phm, c[MEQ("A'", sub(STM_DTE, DNMAP))]), (apl, epl, prs), ((cqt, gaq), (nrs, htf))),
                  TRI(C1, CLN("E'", NF(RP), PF(RP)), '1'))
    C2 = CLN("E'", NF(RP), PF(RP))
    s12 = hrseq(w, ph, phm, s1, s2, C0, C1, C2, BD, '1')
    N2 = '( %s + 1 )' % BD
    # ---- stage 3: dropNum I' at E'
    s3, C3a, D3c, B3 = dropstage(w, ph, c, phm, tv, "E'", "G'", "I'", "F'", 'B', 'W', 'X"', PF(RP), prs, pje, ip, yip, xqw, ww,
                                NF(RP), nrs, (hc, HCDR_), (he, HEDR_))
    assert C3a == C2 and D3c == CLN("G'", SS, POST_C2), (C3a, D3c)
    s123 = hrseq(w, ph, phm, s12, s3, C0, C2, D3c, N2, B3)
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    t1c, t2c, t3c, t4c = c['T1 e. NN0'], c['T" e. NN0'], c['T0 e. NN0'], c["T' e. NN0"]
    bound(w, ph, phm, s123, C0, D3c, '( %s + %s )' % (N2, B3), '( ( R\' x. %s ) + ( ( # ` W ) + 2 ) )' % TD4,
          {"R'": rr, 'T1': t1c, 'T"': t2c, 'T0': t3c, "T'": t4c, '( # ` W )': nw}, qed=True)
    return w.run()


LEAVES_C = {'R': 'R e. NN0', "U'": "U' e. NN0", 'U"': 'U" e. NN0', 'U0': 'U0 e. NN0', "R'": "R' e. NN0",
            'T1': 'T1 e. NN0', 'T"': 'T" e. NN0', 'T0': 'T0 e. NN0', "T'": "T' e. NN0"}


def cleaves(w, ph, c, extra=()):
    d = {k: c[v] for k, v in LEAVES_C.items()}
    for Wd in extra:
        d['( # ` %s )' % Wd] = w.s([c[WRD(Wd, {'W': 'B', "W'": "B'", 'W"': 'B"'}[Wd])], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, Wd))
    return d


def tm2fdmc():
    lab = 'tm2fdmc'
    tree, ph = TREE_DMC, cj(TREE_DMC)
    w = W(lab, '` divmodCore ` of TM/MulDiv.lean: ~ tm2fdmc1 then ~ tm2fdmc2 .  From ` P0 ` in the class '
               '` O ` with the stacks ` D ` to ` G\' ` with the stacks ` ( P ` R\' ) ` of the shift-down '
               'loop\'s last iteration, the counter dropped from ` I\' ` : the composites of the two '
               'loops are hypothesis triples (blueprint D4), the stack families of the loops are '
               'class variables (D8).  Lean: ` divmodCore_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    C0 = CLN('P0', 'O', 'D'); C1 = CLN("A'", NF('0'), PF('0')); C2 = CLN("G'", SS, POST_C2)
    B1 = '( ( ( U" + U0 ) + ( R x. ( U\' + 2 ) ) ) + 3 )'
    B2 = '( ( R\' x. %s ) + ( ( # ` W ) + 2 ) )' % TD4
    s1 = applylem(w, ph, 'tm2fdmc1', leafsteps(TREE_DMC1, lambda t: c[t]), TRI(C0, C1, B1))
    s2 = applylem(w, ph, 'tm2fdmc2', leafsteps(TREE_DMC2, lambda t: c[t]), TRI(C1, C2, B2))
    s12 = hrseq(w, ph, phm, s1, s2, C0, C1, C2, B1, B2)
    bound(w, ph, phm, s12, C0, C2, '( %s + %s )' % (B1, B2), triple_parts(CONCL_DMC)[2], cleaves(w, ph, c, ('W',)), qed=True)
    return w.run()


def tm2fdm():
    lab = 'tm2fdm'
    tree, ph = TREE_DM, cj(TREE_DM)
    w = W(lab, '` divmod ` of TM/MulDiv.lean: ~ tm2fdmc then ` dropNum y ` (~ tm2fdrop ) removes the '
               'restored divisor ` W\' ` from ` J ` .  Lean: ` divmod_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    jj, ip, njip = c['J e. %s' % DG], c["I' e. %s" % DG], c["J =/= I'"]
    rr = c["R' e. NN0"]
    xqw = c[WRD('X"', GIP)]
    RP = "R'"
    st, _ = inst_v(w, ph, c[FAM_DQ_], cj(FAMB_DQ('i')), 'i', RP, rmem(w, ph, rr, RP))
    cx = Ctx(w, ph, FAMB_DQ(RP), root=st)
    prs = cx[STKD(PF(RP))]
    C0 = CLN('P0', 'O', 'D'); C1 = CLN("G'", SS, POST_C2)
    B1 = triple_parts(CONCL_DMC)[2]
    s1 = applylem(w, ph, 'tm2fdmc', leafsteps(TREE_DMC, lambda t: c[t]), TRI(C0, C1, B1))
    # ( POST_C2 ` J ) = ( ( P ` R' ) ` J ) = W' ++ ...
    WYX_J = CC("W'", CC(S1('Y'), "X'"))
    pje = c['( %s ` J ) = %s' % (PF(RP), WYX_J)]
    p2cl = updcl(w, ph, PF(RP), "I'", 'X"', tv, prs, ip, xqw)
    v1 = updnv(w, ph, PF(RP), "I'", 'X"', 'J', tv, prs, ip, elv(w, ph, xqw, 'X"'), jj, njip)
    dkeq = w.s([v1, pje], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, POST_C2, WYX_J))
    hc, he = c[HCDR_J], c[HEDR_J]
    s2, C2a, D2c, B2 = dropstage(w, ph, c, phm, tv, "G'", 'G"', 'J', 'F"', "B'", "W'", "X'", POST_C2, p2cl, dkeq, jj,
                                 c['Y e. %s' % GJ], c[WRD("X'", GJ)], c[WRD("W'", "B'")], SS, None, (hc, HCDR_J), (he, HEDR_J))
    assert C2a == C1 and D2c == CLN('G"', SS, POST_DM), (C2a, D2c)
    s12 = hrseq(w, ph, phm, s1, s2, C0, C1, D2c, B1, B2)
    bound(w, ph, phm, s12, C0, D2c, '( %s + %s )' % (B1, B2), triple_parts(CONCL_DM)[2], cleaves(w, ph, c, ('W', "W'")), qed=True)
    return w.run()


def tm2fdx(lab, k, tree, concl, desc):
    ph = cj(tree)
    w = W(lab, desc)
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, ip = c['%s e. %s' % (k, DG)], c['J e. %s' % DG], c["I' e. %s" % DG]
    nkj = c['%s =/= J' % k] if k == 'K' else w.s([c['J =/= I']], 'necomd', '( %s -> I =/= J )' % ph)
    nkip = c["%s =/= I'" % k]
    rr = c["R' e. NN0"]
    xqw, xpw = c[WRD('X"', GIP)], c[WRD("X'", GJ)]
    RP = "R'"
    st, _ = inst_v(w, ph, c[FAM_DQ_], cj(FAMB_DQ('i')), 'i', RP, rmem(w, ph, rr, RP))
    cx = Ctx(w, ph, FAMB_DQ(RP), root=st)
    prs = cx[STKD(PF(RP))]
    C0 = CLN('P0', 'O', 'D'); C1 = CLN('G"', SS, POST_DM)
    B1 = triple_parts(CONCL_DM)[2]
    s1 = applylem(w, ph, 'tm2fdm', leafsteps(TREE_DM, lambda t: c[t]), TRI(C0, C1, B1))
    WYX = CC('W"', CC(S1('Y'), 'X0'))
    pke = c['( %s ` %s ) = %s' % (PF(RP), k, WYX)]
    p2cl = updcl(w, ph, PF(RP), "I'", 'X"', tv, prs, ip, xqw)
    p3cl = updcl(w, ph, POST_C2, 'J', "X'", tv, p2cl, jj, xpw)
    v1 = updnv(w, ph, POST_C2, 'J', "X'", k, tv, p2cl, jj, elv(w, ph, xpw, "X'"), kk, nkj)
    v2 = updnv(w, ph, PF(RP), "I'", 'X"', k, tv, prs, ip, elv(w, ph, xqw, 'X"'), kk, nkip)
    dkeq = w.s([w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, POST_DM, k, PF(RP), k)), pke], 'eqtrd',
               '( %s -> ( %s ` %s ) = %s )' % (ph, POST_DM, k, WYX))
    hcx, hex = DROP_X(k)[2][1]
    hc, he = c[hcx], c[hex]
    s2, C2a, D2c, B2 = dropstage(w, ph, c, phm, tv, 'G"', "D'", k, 'F0', 'B"', 'W"', 'X0', POST_DM, p3cl, dkeq, kk,
                                 c['Y e. %s' % GX(k)], c[WRD('X0', GX(k))], c[WRD('W"', 'B"')], SS, None, (hc, hcx), (he, hex))
    assert C2a == C1 and D2c == CLN("D'", SS, UP(POST_DM, k, 'X0')), (C2a, D2c)
    s12 = hrseq(w, ph, phm, s1, s2, C0, C1, D2c, B1, B2)
    bound(w, ph, phm, s12, C0, D2c, '( %s + %s )' % (B1, B2), triple_parts(concl)[2], cleaves(w, ph, c, ('W', "W'", 'W"')), qed=True)
    return w.run()


def tm2fdiv():
    return tm2fdx('tm2fdiv', 'K', TREE_DIV, CONCL_DIV,
                  '` divFrag ` of TM/MulDiv.lean: ~ tm2fdm then ` dropNum x ` (~ tm2fdrop ) removes the remainder '
                  '` W" ` from ` K ` ; the quotient stays on ` I ` .  Lean: ` divFrag_runs ` .')


def tm2fmod():
    return tm2fdx('tm2fmod', 'I', TREE_MOD, CONCL_MOD,
                  '` modFrag ` of TM/MulDiv.lean: ~ tm2fdm then ` dropNum q ` (~ tm2fdrop ) removes the quotient '
                  '` W" ` from ` I ` ; the remainder stays on ` K ` .  Lean: ` modFrag_runs ` .')


if __name__ == '__main__':
    if want('tm2fdmc1'): tm2fdmc1()
    if want('tm2fdmc2'): tm2fdmc2()
    if want('tm2fdmc'): tm2fdmc()
    if want('tm2fdm'): tm2fdm()
    if want('tm2fdiv'): tm2fdiv()
    if want('tm2fmod'): tm2fmod()
