"""T-PL: the fragments of TM/PrimList.lean at the generic level over the Lists
layer's alphabet (blueprint D1-D6): ~ tm2fprl (` prodLF `), ~ tm2fcpb (` cpBody `),
~ tm2fcpq (its loop), ~ tm2fcpt (` coprimeToF `), ~ tm2fmla (` mulAllF `),
~ tm2fdvs (` divisorsOfF `).  The composite calls are hypothesis triples; the
theorems execute the pushes, peeks, pops, loads and the entry loops
(~ tm2lfe , ~ tm2lfes )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *
from t6lib import gamk, wgk, lgk, stkfvg, gamlet, s1g, ccatg, hrtransport
from t6lib import updcl as updcl6
from tpl_c_prim import ralk2i
from tpl_e_fes import prel, HBSF

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LB_LFE = '( ( %s x. ( Y + 2 ) ) + 2 )' % NL
S_J = SUM('j', NL, '( %s + 2 )' % YF('j'))


def tvof(w, ph, phm):
    return w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)


def pushsym(w, ph, c, phm, geq, A, E, K, Z, N, D, dcl, nss, kk8):
    """tm2fpshn at the concrete alphabet: push the letter Z (a numeral of Gamma') on stack K at label A"""
    kd, ge = gamk(w, ph, K, geq, kk8)
    zk = lgk(w, ph, Z, K, ge, gamlet(w, ph, Z))
    bld = bldr(w, ph, c, phm, {'%s e. %s' % (K, DG): kd, '%s e. %s' % (Z, GX(K)): zk, STKD(D): dcl, SSS(N): nss})
    s, cc = inst(w, ph, 'tm2fpshn', {'A': A, 'E': E, 'K': K, 'Z': Z, 'N': N, 'D': D}, bld)
    Ca, Dc, B = triple_parts(cc)
    assert Ca == CLN(A, N, D) and Dc == CLN(E, N, UPDT(D, K, CC(S1(Z), '( %s ` %s )' % (D, K)))), (Ca, Dc)
    return s, Ca, Dc, kd, ge


def popk(w, ph, c, phm, ref, A, E, K, F, D, Z, X, N, N2, extra):
    """tm2lpop / tm2lpk at label A: the head Z of stack K (hd : ( D ` K ) = ( <" Z "> ++ X )), from N into N2"""
    bld = bldr(w, ph, c, phm, extra)
    s, cc = inst(w, ph, ref, {'A': A, 'E': E, 'K': K, 'F': F, 'D': D, 'Z': Z, 'X': X, 'N': N, "N'": N2}, bld)
    Ca, Dc, B = triple_parts(cc)
    return s, Ca, Dc


def pknl(w, ph, u_pk, u_nl, u_pty, Kk='K'):
    """( ( P ` NL ) ` K ) = ( <" 2 "> ++ R ) and ( P ` NL ) e. Stk from PK, NL e. NN0, P : ... --> Stk"""
    nlfz = w.s([u_nl, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    cg, new = w.wcongr(fe.PKF('j'), {'j': NL}, 'j = %s' % NL, {'j': w.s([], 'id', '( j = %s -> j = %s )' % (NL, NL))})
    assert new == fe.PKF(NL), new
    pkj = w.s([cg, u_pk, nlfz], 'rspcdva', '( %s -> %s )' % (ph, fe.PKF(NL)))
    DR = DROP('L', NL)
    s0 = w.s([], 'swrd00', '%s = (/)' % DR)
    e1 = w.s([s0], 'fveq2i', '%s = %s' % (ENCB(DR), ENCB('(/)')))
    e2 = w.s([], 'tm2lencb0', '%s = <" 2 ">' % ENCB('(/)'))
    e3 = w.s([e1, e2], 'eqtri', '%s = <" 2 ">' % ENCB(DR))
    e4 = w.s([e3], 'oveq1i', '%s = ( <" 2 "> ++ R )' % LST(DR, 'R'))
    e4a = w.s([e4], 'a1i', '( %s -> %s = ( <" 2 "> ++ R ) )' % (ph, LST(DR, 'R')))
    hd = w.s([pkj, e4a], 'eqtrd', '( %s -> ( ( P ` %s ) ` K ) = ( <" 2 "> ++ R ) )' % (ph, NL))
    pst = w.s([u_pty, nlfz], 'ffvelcdmd', '( %s -> ( P ` %s ) e. %s )' % (ph, NL, STK_T))
    return hd, pst


def nfins(w, ph, nss):
    a = w.s([], 'ssrab2', '%s C_ N' % NFIN)
    aa = w.s([a], 'a1i', '( %s -> %s C_ N )' % (ph, NFIN))
    return w.s([aa, nss], 'sstrd', '( %s -> %s C_ %s )' % (ph, NFIN, SS))


def poptopnl(w, ph, c, u, E, E2, N2):
    """popTop at E on ( P ` NL ) from NFIN into N2 (the HPK leaf of the tree), exit E2"""
    hd, pst = pknl(w, ph, u['pk'], u['nl'], u['pty'])
    g2 = gamlet(w, ph, '2')
    extra = {STKD(PF(NL)): pst, '( ( P ` %s ) ` K ) = ( <" 2 "> ++ R )' % NL: hd, "2 e. Gamma'": g2, SSS(NFIN): nfins(w, ph, u['nss'])}
    s, Ca, Dc = popk(w, ph, c, u['phm'], 'tm2lpop', E, E2, 'K', 'F"', PF(NL), '2', 'R', NFIN, N2, extra)
    assert Ca == CL(E, NFIN, PF(NL)) and Dc == CL(E2, N2, UPDT(PF(NL), 'K', 'R')), (Ca, Dc)
    return s, Ca, Dc


def sumcl(w, ph, hb):
    """( ph -> S_J e. NN0 ) from hb : ( ph -> HBS )"""
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, NL)
    io = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, NL))
    cgi, newi = w.wcongr(HBSF('j'), {'j': 'i'}, 'j = i', {'j': w.s([], 'id', '( j = i -> j = i )')})
    assert newi == HBSF('i'), newi
    hba = w.s([hb], 'adantr', '( %s -> %s )' % (pi, HBS))
    hbi = w.s([cgi, hba, io], 'rspcdva', '( %s -> %s )' % (pi, HBSF('i')))
    yni = w.s([hbi], 'simpld', '( %s -> %s e. NN0 )' % (pi, YF('i')))
    two = w.s([], '2nn0', '2 e. NN0'); twoa = w.s([two], 'a1i', '( %s -> 2 e. NN0 )' % pi)
    y2n = w.s([yni, twoa], 'nn0addcld', '( %s -> ( %s + 2 ) e. NN0 )' % (pi, YF('i')))
    S_I = SUM('i', NL, '( %s + 2 )' % YF('i'))
    fia = w.s([w.s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NL)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NL))
    sni = w.s([fia, y2n], 'fsumnn0cl', '( %s -> %s e. NN0 )' % (ph, S_I))
    g1 = w.s([], 'fveq2', '( i = j -> ( Y ` i ) = ( Y ` j ) )')
    g2 = w.s([g1], 'oveq1d', '( i = j -> ( ( Y ` i ) + 2 ) = ( ( Y ` j ) + 2 ) )')
    cbs = w.s([g2], 'cbvsumv', '%s = %s' % (S_I, S_J))
    cbsa = w.s([cbs], 'a1i', '( %s -> %s = %s )' % (ph, S_I, S_J))
    return w.s([cbsa, sni], 'eqeltrrd', '( %s -> %s e. NN0 )' % (ph, S_J))


# ------------------------------------------------------------- prodLF

def tm2fprl():
    lab = 'tm2fprl'
    tree, ph = TREE_PRL, cj(TREE_PRL)
    w = W(lab, 'The list product ` prodLF ` of TM/PrimList.lean: ` copyList x c s t ; pushNum w 1 ` is a hypothesis '
               'triple from ` P0 ` into the entry loop\'s family at ` 0 ` (T7: ~ tm2lcpyb2 , ~ tm2fpshn ), '
               '` forEntries c prodBody ` is ~ tm2lfe with the body ` mulC c w x s t ; moveEntry x w s ` one '
               'triple per entry (blueprint D3; T7: ~ tm2fml + ~ tm2fcan , ~ tm2lme ), and ` popTop c ` removes '
               'the copied list\'s ` bra ` (~ tm2lpop ).  Lean: the generic core of ` prodLF_le_B ` .')
    c = Ctx(w, ph, tree)
    u = prel(w, ph, c[fe.PHF], False) if False else None
    cf = Ctx(w, ph, T_PHF, root=c[fe.PHF])
    phm = cf[PHM]
    u = dict(phm=phm, pk=cf[fe.PK], pty=cf[fe.PTY], nss=cf['N C_ %s' % SS], nl=w.s([cf['L e. %s' % WWB], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL)))
    trip = c[TRIP_PRL]
    bldf = Builder(w, ph, cf)
    lfe, cc = inst(w, ph, 'tm2lfe', {}, bldf)
    C0, C1, C2 = CL('P0', 'O', 'D'), CL('P1', 'N', PF('0')), CL('E', NFIN, PF(NL))
    assert triple_parts(cc)[0] == C1 and triple_parts(cc)[1] == C2 and triple_parts(cc)[2] == LB_LFE, cc
    pop, Ca, Dc = poptopnl(w, ph, c, u, 'E', "E'", "N'")
    s1 = hrseq(w, ph, phm, trip, lfe, C0, C1, C2, 'U', LB_LFE)
    w.qed([phm, s1, pop], 'syl3anc', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', Dc, '( ( U + %s ) + 1 )' % LB_LFE)))
    return w.run()


# ------------------------------------------------------------- coprimeTo: the body, the loop, the fragment

def tm2fcpb():
    lab = 'tm2fcpb'
    tree, ph = TREE_CPB, cj(TREE_CPB)
    w = W(lab, 'One test of ` coprimeToF ` (` cpBody ` of TM/PrimList.lean) from the body entry ` B0 ` back to the '
               'test ` A ` : ` dup x t s ; dup y u s ; modC ; isZero u s ` is a hypothesis triple into ` N1 ` (T7: '
               '~ tm2fdup , ~ tm2fmod + ~ tm2fcan , ~ tm2fisz ), ` load\' ( cmp := flag ? eq : lt ) ` records the '
               'verdict (~ tm2flg ), ` dropNum u ; moveEntry x z s ` is a triple into ` N0 ` (T7: ~ tm2fdrop , '
               '~ tm2lme ) and ` peekBraOr x ` at ` B1_ ` reads the list\'s next head ` Z ` into ` N\' ` (~ tm2lpk ).  '
               'Lean: ` cpBody_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tr1, tr2 = c[TRIP_CP1], c[TRIP_CP2]
    l = ldstep(w, ph, phm, c[MEQ("B'", LD('L', 'B"'))], c[LAB("B'")], c[LAB('B"')], c[STKD("D'")], c[LTY('L')], c[SSS('N1')], c[SSS('N"')],
               c[HLD('N1', 'N"', 'L')], "B'", 'B"', 'N1', 'N"', "D'")
    pk, Ca, Dc = popk(w, ph, c, phm, 'tm2lpk', 'B1_', 'A', 'K', 'F', 'D"', 'Z', 'X', 'N0', "N'", {})
    C0, C1, C2, C3, C4 = CLN('B0', 'N', 'D'), CLN("B'", 'N1', "D'"), CLN('B"', 'N"', "D'"), CLN('B1_', 'N0', 'D"'), CLN('A', "N'", 'D"')
    assert Ca == C3 and Dc == C4, (Ca, Dc)
    s1 = hrseq(w, ph, phm, tr1, l, C0, C1, C2, 'T1', '1')
    s2 = hrseq(w, ph, phm, s1, tr2, C0, C2, C3, '( T1 + 1 )', 'T"')
    s3 = hrseq(w, ph, phm, s2, pk, C0, C3, C4, '( ( T1 + 1 ) + T" )', '1')
    bound0(w, ph, phm, s3, C0, C4, '( ( ( T1 + 1 ) + T" ) + 1 )', TD_CP, {'T1': c['T1 e. NN0'], 'T"': c['T" e. NN0']}, qed=True)
    return w.run()


def tm2fcpq():
    lab = 'tm2fcpq'
    tree, ph = TREE_CPQ, cj(TREE_CPQ)
    w = W(lab, 'The loop of ` coprimeToF ` from its test label ` A ` to the exit ` E ` : ~ tm2floopu over the class '
               'family ` ( N ` i ) ` and the stack family ` ( P ` i ) ` , each iteration ~ tm2fcpb at ` i ` with the '
               'peeked head ` ( Z ` i ) ` (blueprint D4).  Lean: ` Frag.loop_runs ` at ` CpInv ` in ` coprimeToF_le_B ` , '
               '` R := cpIter Q k ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    fam, hyps, rr = c[FAM_L], c[HYPS_CPQ], c['R e. NN0']
    pk_ = '( %s /\\ k e. ( 0 ..^ R ) )' % ph
    Lk = Lifter(w, pk_)
    kin, kfz, k1fz, knn, k1nn = kfacts(w, pk_)
    K1 = '( k + 1 )'
    fk = famat(w, pk_, Lk(fam, FAM_L), 'k', kfz)
    fk1 = famat(w, pk_, Lk(fam, FAM_L), K1, k1fz)
    hyk, _ = inst_v(w, pk_, Lk(hyps, HYPS_CPQ), cj(HYP_CPQ_TREE('i')), 'i', 'k', kin)
    ck = Ctx(w, pk_, HYP_CPQ_TREE('k'), root=hyk)
    m = CPQ_MAP('k')
    derived = {SSS(NF('k')): fk['nss'], STKD(PF('k')): fk['pst'], SSS(NF(K1)): fk1['nss'], STKD(PF(K1)): fk1['pst']}
    for t in flat(HYP_CPQ_TREE('k')):
        derived[t] = ck[t]
    def look(t):
        return derived[t] if t in derived else Lk(c[t], t)
    trik = applylem(w, pk_, 'tm2fcpb', leafsteps(ren(TREE_CPB, m), look), BODY_L('k', TD_CP))
    htk = ck[HT(NF('k'))]
    body_k = '( %s /\\ %s )' % (HT(NF('k')), BODY_L('k', TD_CP))
    body_i = '( %s /\\ %s )' % (HT(NF('i')), BODY_L('i', TD_CP))
    pair = w.s([htk, trik], 'jca', '( %s -> %s )' % (pk_, body_k))
    hypk = w.s([pair], 'ralrimiva', '( %s -> A. k e. ( 0 ..^ R ) %s )' % (ph, body_k))
    hypi = ralk2i(w, ph, hypk, body_k, body_i)
    tdn = nn0cl(w, ph, TD_CP, {'T1': c['T1 e. NN0'], 'T"': c['T" e. NN0']})
    HYPS_U = sub(HYPS_LU, {"T'": TD_CP})
    extra = {HYPS_U: hypi, '%s e. NN0' % TD_CP: tdn}
    def look2(t):
        return extra[t] if t in extra else c[t]
    concl = sub(CONCL_LOOPU, {"T'": TD_CP})
    assert concl == CONCL_CPQ
    st, txt = jtree(w, ph, leafsteps(ren(TREE_LOOPU, {"T'": TD_CP}), look2))
    w.qed([st, w.inst('tm2floopu')], 'syl', '( %s -> %s )' % (ph, concl))
    return w.run()


def tm2fcpt():
    lab = 'tm2fcpt'
    tree, ph = TREE_CPT, cj(TREE_CPT)
    w = W(lab, 'The coprimality test ` coprimeToF ` of TM/PrimList.lean: ` pushSym z bra ` opens the processed-entries '
               'list (~ tm2fpshn ), ` load\' ( cmp := lt ) ` clears the verdict (~ tm2flg ), ` peekBra x ` sets the loop '
               'test from the list\'s head (~ tm2lpk ), the loop ~ tm2fcpq runs ` R ` tests, ` pushSym t comma ` and '
               '` pushBit t ( cmp =/= lt ) ` write the verdict as a number on ` t ` (~ tm2fpshn , ~ tm2fpshf ), and '
               '` moveEntries z x s ` , ` isZero t s ` , ` dropNum t ` are hypothesis triples (T7: ~ tm2lmes , ~ tm2fisz , '
               '~ tm2fdrop ).  Lean: the generic core of ` coprimeToF_le_B ` .')
    c = Ctx(w, ph, tree)
    phm, geq = c[PHM], c[GEQ]
    tv = tvof(w, ph, phm)
    fam, rr = c[FAM_L], c['R e. NN0']
    dd, init = c[STKD('D')], c['%s = %s' % (PF('0'), UPDT('D', 'I', CC(S1('2'), '( D ` I )')))]
    oss, ops = c[SSS('O')], c[SSS("O'")]
    f0 = famat(w, ph, fam, '0', zmem(w, ph, rr))
    fR = famat(w, ph, fam, 'R', rmem(w, ph, rr))
    # ---- 1. pushSym z bra at P0
    s1, C0, C1x, id_, ge_i = pushsym(w, ph, c, phm, geq, 'P0', 'P1', 'I', '2', 'O', 'D', dd, oss, c['I e. %s' % FZ8])
    initc = w.s([init], 'eqcomd', '( %s -> %s = %s )' % (ph, UPDT('D', 'I', CC(S1('2'), '( D ` I )')), PF('0')))
    C1 = CL('P1', 'O', PF('0'))
    s1r, _, _, _ = hrrw(w, ph, s1, C0, C1x, '1', deq=clneq(w, ph, 'P1', 'O', initc, UPDT('D', 'I', CC(S1('2'), '( D ` I )')), PF('0')))
    # ---- 2. load L0 at P1
    l2 = ldstep(w, ph, phm, c[MEQ('P1', LD('L0', 'Q0'))], c[LAB('P1')], c[LAB('Q0')], f0['pst'], c[LTY('L0')], oss, ops,
                c[HLD('O', "O'", 'L0')], 'P1', 'Q0', 'O', "O'", PF('0'))
    C2 = CL('Q0', "O'", PF('0'))
    # ---- 3. peekBra x at Q0
    s3, Ca, Dc = popk(w, ph, c, phm, 'tm2lpk', 'Q0', 'A', 'K', 'F0', PF('0'), 'Z0', 'X0', "O'", NF('0'),
                      {STKD(PF('0')): f0['pst'], SSS(NF('0')): f0['nss']})
    C3 = CL('A', NF('0'), PF('0'))
    assert Ca == C2 and Dc == C3, (Ca, Dc)
    # ---- 4. the loop
    lp = applylem(w, ph, 'tm2fcpq', leafsteps(TREE_CPQ, lambda t: c[t]), CONCL_CPQ)
    C4 = CL('E', NF('R'), PF('R'))
    # ---- 5. pushSym t comma at E
    s5, C4a, C5, ipd, ge_ip = pushsym(w, ph, c, phm, geq, 'E', "E'", "I'", '4', NF('R'), PF('R'), fR['pst'], fR['nss'], c["I' e. %s" % FZ8])
    assert C4a == C4
    D5 = UPDT(PF('R'), "I'", CC(S1('4'), "( %s ` I' )" % PF('R')))
    # ---- 6. pushBit t G at E'
    prw = stkfvg(w, ph, PF('R'), "I'", tv, fR['pst'], ipd, ge_ip)
    w4 = ccatg(w, ph, S1('4'), "( %s ` I' )" % PF('R'), s1g(w, ph, '4'), prw)
    d5cl = updcl6(w, ph, PF('R'), "I'", CC(S1('4'), "( %s ` I' )" % PF('R')), tv, fR['pst'], ipd, ge_ip, w4)
    gty = w.s([c[PTG('G')], w.s([ge_ip], 'oveq1d', "( %s -> ( %s ^m %s ) = ( Gamma' ^m %s ) )" % (ph, GX("I'"), SS, SS))], 'eleqtrrd',
              '( %s -> G e. ( %s ^m %s ) )' % (ph, GX("I'"), SS))
    zpk = lgk(w, ph, "Z'", "I'", ge_ip, c["Z' e. Gamma'"])
    bld6 = bldr(w, ph, c, phm, {"I' e. %s" % DG: ipd, "Z' e. %s" % GX("I'"): zpk, PTY('G', "I'"): gty, STKD(D5): d5cl, SSS(NF('R')): fR['nss']})
    s6, c6 = inst(w, ph, 'tm2fpshf', {'A': "E'", 'E': 'E"', 'K': "I'", 'P': 'G', 'Z': "Z'", 'N': NF('R'), 'D': D5}, bld6)
    C5a, D6c, B6 = triple_parts(c6)
    D6 = UPDT(D5, "I'", CC(S1("Z'"), "( %s ` I' )" % D5))
    assert C5a == C5 and D6c == CL('E"', NF('R'), D6), (C5a, D6c)
    # ( D5 ` I' ) = <" 4 "> ++ ( P_R ` I' ), then the two updates collapse
    v5 = updkv(w, ph, PF('R'), "I'", CC(S1('4'), "( %s ` I' )" % PF('R')), tv, fR['pst'], ipd, elv(w, ph, w4, CC(S1('4'), "( %s ` I' )" % PF('R'))))
    r6, D6b = w.rewrite(D6, {"( %s ` I' )" % D5: (CC(S1('4'), "( %s ` I' )" % PF('R')), v5)}, ph)
    W2 = CC(S1("Z'"), CC(S1('4'), "( %s ` I' )" % PF('R')))
    assert D6b == UPDT(D5, "I'", W2), D6b
    w2 = ccatg(w, ph, S1("Z'"), CC(S1('4'), "( %s ` I' )" % PF('R')), w.s([c["Z' e. Gamma'"]], 's1cld', '( %s -> <" Z\' "> e. %s )' % (ph, WG)), w4)
    col = up2(w, ph, PF('R'), "I'", CC(S1('4'), "( %s ` I' )" % PF('R')), W2, tv, fR['pst'], ipd,
              wgk(w, ph, CC(S1('4'), "( %s ` I' )" % PF('R')), "I'", ge_ip, w4), wgk(w, ph, W2, "I'", ge_ip, w2))
    assert concl(w, ph, col) == '%s = %s' % (UPDT(D5, "I'", W2), D2_CPT), concl(w, ph, col)
    r6c = w.s([r6, col], 'eqtrd', '( %s -> %s = %s )' % (ph, D6, D2_CPT))
    s6r, _, _, _ = hrrw(w, ph, s6, C5a, D6c, B6, deq=clneq(w, ph, 'E"', NF('R'), r6c, D6, D2_CPT))
    C6 = CL('E"', NF('R'), D2_CPT)
    # ---- 7. the three triples
    trm, trz, trd = c[TRIP_CPM], c[TRIP_CPZ], c[TRIP_CPD]
    C7, C8, C9 = CL('E0', 'N"', 'D"'), CL('E1', 'N0', 'D0'), CL("D'", "N'", 'D1_')
    q = hrseq(w, ph, phm, s1r, l2, C0, C1, C2, '1', '1'); n = '( 1 + 1 )'
    q = hrseq(w, ph, phm, q, s3, C0, C2, C3, n, '1'); n = '( %s + 1 )' % n
    q = hrseq(w, ph, phm, q, lp, C0, C3, C4, n, BND_CPQ); n = '( %s + %s )' % (n, BND_CPQ)
    q = hrseq(w, ph, phm, q, s5, C0, C4, C5, n, '1'); n = '( %s + 1 )' % n
    q = hrseq(w, ph, phm, q, s6r, C0, C5, C6, n, '1'); n = '( %s + 1 )' % n
    q = hrseq(w, ph, phm, q, trm, C0, C6, C7, n, 'U'); n = '( %s + U )' % n
    q = hrseq(w, ph, phm, q, trz, C0, C7, C8, n, "U'"); n = "( %s + U' )" % n
    q = hrseq(w, ph, phm, q, trd, C0, C8, C9, n, 'U"'); n = '( %s + U" )' % n
    bound0(w, ph, phm, q, C0, C9, n, triple_parts(CONCL_CPT)[2],
           {'R': rr, 'T1': c['T1 e. NN0'], 'T"': c['T" e. NN0'], 'U': c['U e. NN0'], "U'": c["U' e. NN0"], 'U"': c['U" e. NN0']}, qed=True)
    return w.run()


# ------------------------------------------------------------- mulAllF

def tm2fmla():
    lab = 'tm2fmla'
    tree, ph = TREE_MLA, cj(TREE_MLA)
    w = W(lab, 'The scaling ` mulAllF ` of TM/PrimList.lean: ` pushSym r bra ` opens the product list (~ tm2fpshn ), '
               '` forEntries x mulAllBody ` is ~ tm2lfe with the body ` dup y t s ; mulC x t r s y ` one triple per '
               'entry (blueprint D3; T7: ~ tm2fdup , ~ tm2fml + ~ tm2fcan ), ` popTop x ` removes the consumed list\'s '
               '` bra ` (~ tm2lpop ) and ` revList r x s ` is a hypothesis triple (T7: ~ tm2lrevb ).  Lean: the '
               'generic core of ` mulAllF_le_B ` .')
    c = Ctx(w, ph, tree)
    cf = Ctx(w, ph, T_PHF, root=c[fe.PHF])
    phm, geq = cf[PHM], cf[GEQ]
    u = dict(phm=phm, pk=cf[fe.PK], pty=cf[fe.PTY], nss=cf['N C_ %s' % SS], nl=w.s([cf['L e. %s' % WWB], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL)))
    dd, init = c[STKD('D')], c[INIT_MLA]
    DI2 = UPDT('D', 'I', CC(S1('2'), '( D ` I )'))
    s1, C0, C1x, _, _ = pushsym(w, ph, c, phm, geq, 'P0', 'P1', 'I', '2', 'N', 'D', dd, u['nss'], c['I e. %s' % FZ8])
    initc = w.s([init], 'eqcomd', '( %s -> %s = %s )' % (ph, DI2, PF('0')))
    C1 = CL('P1', 'N', PF('0'))
    s1r, _, _, _ = hrrw(w, ph, s1, C0, C1x, '1', deq=clneq(w, ph, 'P1', 'N', initc, DI2, PF('0')))
    lfe, cc = inst(w, ph, 'tm2lfe', {}, Builder(w, ph, cf))
    C2 = CL('E', NFIN, PF(NL))
    assert triple_parts(cc)[0] == C1 and triple_parts(cc)[1] == C2, cc
    pop, Ca, C3 = poptopnl(w, ph, c, u, 'E', "E'", "N'")
    trm = c[TRIP_MLA]
    C4 = CL('E"', 'N"', "D'")
    q = hrseq(w, ph, phm, s1r, lfe, C0, C1, C2, '1', LB_LFE); n = '( 1 + %s )' % LB_LFE
    q = hrseq(w, ph, phm, q, pop, C0, C2, C3, n, '1'); n = '( %s + 1 )' % n
    q = hrseq(w, ph, phm, q, trm, C0, C3, C4, n, 'U'); n = '( %s + U )' % n
    bound0(w, ph, phm, q, C0, C4, n, triple_parts(CONCL_MLA)[2], {NL: u['nl'], 'Y': cf['Y e. NN0'], 'U': c['U e. NN0']}, qed=True)
    return w.run()


# ------------------------------------------------------------- divisorsOfF

def tm2fdvs():
    lab = 'tm2fdvs'
    tree, ph = TREE_DVS, cj(TREE_DVS)
    w = W(lab, 'The subset products ` divisorsOfF ` of TM/PrimList.lean: ` revList x z s ` is a hypothesis triple (T7: '
               '~ tm2lrevn ), ` pushSym a bra ` and the ` pushNum a 1 ` triple start the accumulator ` [ 1 ] ` (~ tm2fpshn , '
               'T7: ~ tm2fpshn ), ` forEntries z divBody ` is the Sigma-cost loop ~ tm2lfes with the body ` copyList ; '
               'mulAllF ; appendList ; dropNum ` one triple per entry of cost ` ( Y ` j ) ` (blueprint D3, D4; T7: '
               '~ tm2lcpyb2 , ~ tm2fmla , ~ tm2lappb , ~ tm2fdrop ), ` popTop z ` removes the reversed list\'s ` bra ` '
               '(~ tm2lpop ) and ` revList a x s ` is a triple (T7: ~ tm2lrevb ).  Lean: the generic core of '
               '` divisorsOfF_le_B ` .')
    c = Ctx(w, ph, tree)
    cf = Ctx(w, ph, TREE_FES, root=c[PHFS])
    phm, geq = cf[PHM], cf[GEQ]
    u = dict(phm=phm, pk=cf[fe.PK], pty=cf[fe.PTY], nss=cf['N C_ %s' % SS], nl=w.s([cf['L e. %s' % WWB], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL)))
    tr1, tr2, tr3 = c[TRIP_DV1], c[TRIP_DV2], c[TRIP_DV3]
    C0, C1 = CL('P0', 'O', 'D'), CL('Q0', 'N', "D'")
    s2, C1a, C2, _, _ = pushsym(w, ph, c, phm, geq, 'Q0', "Q'", 'J', '2', 'N', "D'", c[STKD("D'")], u['nss'], c['J e. %s' % FZ8])
    assert C1a == C1
    C3 = CL('P1', 'N', PF('0'))
    lfes, cc = inst(w, ph, 'tm2lfes', {}, bldr(w, ph, cf, phm))
    C4 = CL('E', NFIN, PF(NL))
    assert triple_parts(cc)[0] == C3 and triple_parts(cc)[1] == C4 and triple_parts(cc)[2] == '( %s + 2 )' % S_J, cc
    pop, Ca, C5 = poptopnl(w, ph, c, u, 'E', "E'", "N'")
    C6 = CL('E"', 'N"', 'D"')
    q = hrseq(w, ph, phm, tr1, s2, C0, C1, C2, 'U', '1'); n = '( U + 1 )'
    q = hrseq(w, ph, phm, q, tr2, C0, C2, C3, n, "U'"); n = "( %s + U' )" % n
    q = hrseq(w, ph, phm, q, lfes, C0, C3, C4, n, '( %s + 2 )' % S_J); n = '( %s + ( %s + 2 ) )' % (n, S_J)
    q = hrseq(w, ph, phm, q, pop, C0, C4, C5, n, '1'); n = '( %s + 1 )' % n
    q = hrseq(w, ph, phm, q, tr3, C0, C5, C6, n, 'U"'); n = '( %s + U" )' % n
    sn = sumcl(w, ph, cf[HBS])
    bound0(w, ph, phm, q, C0, C6, n, triple_parts(CONCL_DVS)[2], {'U': c['U e. NN0'], "U'": c["U' e. NN0"], 'U"': c['U" e. NN0'], S_J: sn}, qed=True)
    return w.run()


if __name__ == '__main__':
    for f in [tm2fprl, tm2fcpb, tm2fcpq, tm2fcpt, tm2fmla, tm2fdvs]:
        if want(f.__name__): f()
