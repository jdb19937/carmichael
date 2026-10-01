"""T5: the two-operand loops, part 1 --- the update algebra ~ tm2stkup3c and
the read-phase discharge ~ tm2fadrd at one iteration (blueprint D4)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GJ, GI = GX('K'), GX('J'), GX('I')
HDL = lambda k: '( %s ^m ( %s X. ( %s |_| 1o ) ) )' % (SS, SS, GX(k))


def tm2stkup3c():
    lab = 'tm2stkup3c'
    tree = ((('T e. V', 'D e. %s' % STK_T), ('K =/= J', 'K =/= I', 'J =/= I')),
            ('I e. %s' % DG, ('C e. Word %s' % GI, "C' e. Word %s" % GI)),
            (('K e. %s' % DG, 'Y e. Word %s' % GK), ('J e. %s' % DG, 'Z e. Word %s' % GJ)))
    ph = cj(tree)
    w = W(lab, 'Four updates at three distinct indices, the outermost repeating the '
               'innermost, collapse to three: the update at ` I ` commutes inward past '
               '` J ` and ` K ` (~ tm2stkupc twice) and absorbs the first (~ tm2stkup2 ).  '
               'Every iteration of the two-operand loops pushes on the output stack '
               'under the two operand updates and uses this.')
    c = Ctx(w, ph, tree)
    tv, dd = c['T e. V'], c['D e. %s' % STK_T]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    ii, kk, jj = c['I e. %s' % DG], c['K e. %s' % DG], c['J e. %s' % DG]
    cw, cpw = c['C e. Word %s' % GI], c["C' e. Word %s" % GI]
    yw, zw = c['Y e. Word %s' % GK], c['Z e. Word %s' % GJ]
    D1 = UP('D', 'I', 'C'); D2 = UP(D1, 'K', 'Y')
    d1cl = updcl(w, ph, 'D', 'I', 'C', tv, dd, ii, cw)
    d2cl = updcl(w, ph, D1, 'K', 'Y', tv, d1cl, kk, yw)
    # U(U(D2,J,Z),I,C') = U(U(D2,I,C'),J,Z)
    s1 = upc(w, ph, D2, 'J', 'Z', 'I', "C'", tv, d2cl, nji, jj, zw, ii, cpw)
    # U(U(D1,K,Y),I,C') = U(U(D1,I,C'),K,Y)
    s2 = upc(w, ph, D1, 'K', 'Y', 'I', "C'", tv, d1cl, nki, kk, yw, ii, cpw)
    # U(U(D,I,C),I,C') = U(D,I,C')
    s3 = up2(w, ph, 'D', 'I', 'C', "C'", tv, dd, ii, cw, cpw)
    LHS = UP(UP(D2, 'J', 'Z'), 'I', "C'")
    r1, t1 = w.rewrite(LHS, {LHS: (UP(UP(D2, 'I', "C'"), 'J', 'Z'), s1)}, ph)
    r2, t2 = w.rewrite(t1, {UP(D2, 'I', "C'"): (UP(UP(D1, 'I', "C'"), 'K', 'Y'), s2)}, ph)
    r3, t3 = w.rewrite(t2, {UP(D1, 'I', "C'"): (UP('D', 'I', "C'"), s3)}, ph)
    RHS = UP(UP(UP('D', 'I', "C'"), 'K', 'Y'), 'J', 'Z')
    assert t3 == RHS, t3
    e12 = w.s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, LHS, t2))
    w.qed([e12, r3], 'eqtrd', '( %s -> %s = %s )' % (ph, LHS, RHS))
    return w.run()


# ---------------------------------------------------------------- tm2fadrd
RD = lambda Q: BRANCH("C'", Q, POP('J', "F'", Q))
BODY = lambda Q: BRANCH('C', RD(Q), POP('K', 'F', RD(Q)))
IDX = 'H'
XF = lambda x: '( X ` %s )' % x
YF = lambda x: '( Y ` %s )' % x
UF = lambda x: '( U ` %s )' % x
UPF = lambda x: "( U' ` %s )" % x
NF = lambda x: '( N ` %s )' % x
OF = lambda x: '( O ` %s )' % x
P1 = lambda x: '( %s + 1 )' % x
STEPX = lambda x: ('( ( %s e. R -> %s = ( <" %s "> ++ %s ) ) /\\ ( -. %s e. R -> %s = %s ) /\\ ( %s e. %s /\\ %s e. Word %s ) )'
                   % (x, XF(x), UF(x), XF(P1(x)), x, XF(P1(x)), XF(x), UF(x), GK, XF(P1(x)), GK))
STEPY = lambda x: ("( ( %s e. R' -> %s = ( <\" %s \"> ++ %s ) ) /\\ ( -. %s e. R' -> %s = %s ) /\\ ( %s e. %s /\\ %s e. Word %s ) )"
                   % (x, YF(x), UPF(x), YF(P1(x)), x, YF(P1(x)), YF(x), UPF(x), GJ, YF(P1(x)), GJ))
VA = lambda x, m: 'if ( %s e. R , %s , %s )' % (x, NVF('F', m, UF(x)), m)
VB = lambda x, m: "if ( %s e. R' , %s , %s )" % (x, NVF("F'", VA(x, m), UPF(x)), VA(x, m))
HAB = lambda x, m: ("( ( ( C ` %s ) = 1o <-> -. %s e. R ) /\\ ( ( C' ` %s ) = 1o <-> -. %s e. R' ) /\\ %s e. %s )"
                    % (m, x, VA(x, m), x, VB(x, m), OF(x)))
HA = lambda x: 'A. n e. %s %s' % (NF(x), HAB(x, 'n'))
DP2 = lambda x, D: UP(UP(D, 'K', XF(P1(x))), 'J', YF(P1(x)))
def TREE_RDX(x, D='D', Q='Q'):
    return (('T e. V', ('C e. ( 2o ^m %s )' % SS, "C' e. ( 2o ^m %s )" % SS), ('F e. %s' % HDL('K'), "F' e. %s" % HDL('J'))),
            (('K e. %s' % DG, 'J e. %s' % DG, 'K =/= J'), ('%s e. %s' % (Q, STMT_T), '%s e. %s' % (D, STK_T)), '( M ` A ) = %s' % BODY(Q)),
            (('( %s ` K ) = %s' % (D, XF(x)), '( %s ` J ) = %s' % (D, YF(x))), (STEPX(x), STEPY(x)), ('%s C_ %s' % (NF(x), SS), HA(x))))
CONCLX = lambda x, D2, D='D', Q='Q': ('A. r e. %s E. p e. %s ( ( M ` A ) %s <. r , %s >. ) = ( %s %s <. p , %s >. )'
                                    % (NF(x), OF(x), SA('T'), D, Q, SA('T'), D2))
# the theorem's own instance: index H
XI, XI1 = XF(IDX), XF(P1(IDX))
YI, YI1 = YF(IDX), YF(P1(IDX))
UI, UI1 = UF(IDX), UPF(IDX)
NI, OI = NF(IDX), OF(IDX)
STEPX_, STEPY_ = STEPX(IDX), STEPY(IDX)
HA_ = HA(IDX)
DP = DP2(IDX, 'D')
TREE_RD = TREE_RDX(IDX)
CONCL = lambda D2: CONCLX(IDX, D2)


def tm2fadrd():
    lab = 'tm2fadrd'
    ph = cj(TREE_RD)
    w = W(lab, 'The two-operand read phase at iteration ` H ` : the operand stacks '
               '` K ` , ` J ` hold ` ( X ` i ) ` , ` ( Y ` i ) ` , the iterations at which '
               'an operand is still read are the classes ` R ` , ` R\' ` , the letters popped '
               'are ` ( U ` i ) ` , ` ( U\' ` i ) ` , and the handler interface says that the '
               'exhaustion flags ` C ` , ` C\' ` are set exactly off ` R ` , ` R\' ` and that '
               'the two reads land in the post-read class ` ( O ` i ) ` .  Then the body at '
               '` A ` reduces to its rest ` Q ` at the post-read state with the operand '
               'stacks advanced --- the hypothesis ` H1 ` of ~ tm2fad1 , ~ tm2fad0c , '
               '~ tm2fad0n , ~ tm2fcm1 , ~ tm2fcm0 .  A case split on ` H e. R ` , '
               '` H e. R\' ` feeding ~ tm2frd2 , ~ tm2frd2a , ~ tm2frd2b , ~ tm2frd2c ; a '
               'skipped operand\'s update is ~ tm2stkupid .  Lean: the '
               '` obtain ... := hA.read ` , ` hB.read ` pair at the head of every case of '
               '` addLoop_loop ` , ` subLoop_loop ` , ` cmpFrag_loop ` ; the phantom operand '
               'of ` dec ` is ` R\' = (/) ` .')
    c = Ctx(w, ph, TREE_RD)
    tv = c['T e. V']; dd = c['D e. %s' % STK_T]
    kk, jj, ne = c['K e. %s' % DG], c['J e. %s' % DG], c['K =/= J']
    nej = w.s([ne], 'necomd', '( %s -> J =/= K )' % ph)
    dke, dje = c['( D ` K ) = %s' % XI], c['( D ` J ) = %s' % YI]
    stx, sty = c[STEPX_], c[STEPY_]
    x1 = w.s([stx, w.inst('simp1')], 'syl', '( %s -> ( %s e. R -> %s = ( <" %s "> ++ %s ) ) )' % (ph, IDX, XI, UI, XI1))
    x2 = w.s([stx, w.inst('simp2')], 'syl', '( %s -> ( -. %s e. R -> %s = %s ) )' % (ph, IDX, XI1, XI))
    x3 = w.s([stx, w.inst('simp3')], 'syl', '( %s -> ( %s e. %s /\\ %s e. Word %s ) )' % (ph, UI, GK, XI1, GK))
    ui = w.s([x3], 'simpld', '( %s -> %s e. %s )' % (ph, UI, GK))
    xi1w = w.s([x3], 'simprd', '( %s -> %s e. Word %s )' % (ph, XI1, GK))
    y1 = w.s([sty, w.inst('simp1')], 'syl', "( %s -> ( %s e. R' -> %s = ( <\" %s \"> ++ %s ) ) )" % (ph, IDX, YI, UI1, YI1))
    y2 = w.s([sty, w.inst('simp2')], 'syl', "( %s -> ( -. %s e. R' -> %s = %s ) )" % (ph, IDX, YI1, YI))
    y3 = w.s([sty, w.inst('simp3')], 'syl', '( %s -> ( %s e. %s /\\ %s e. Word %s ) )' % (ph, UI1, GJ, YI1, GJ))
    ui1 = w.s([y3], 'simpld', '( %s -> %s e. %s )' % (ph, UI1, GJ))
    yi1w = w.s([y3], 'simprd', '( %s -> %s e. Word %s )' % (ph, YI1, GJ))
    nss, ha = c['%s C_ %s' % (NI, SS)], c[HA_]
    head = (tv, (c['C e. ( 2o ^m %s )' % SS], c["C' e. ( 2o ^m %s )" % SS]), (c['F e. %s' % HDL('K')], c["F' e. %s" % HDL('J')]))
    meq = c['( M ` A ) = %s' % BODY('Q')]
    qq = c['Q e. %s' % STMT_T]
    # the words the uniform post-stack needs
    dkw = stkfv(w, ph, 'D', 'K', tv, dd, kk); djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)

    def case(inR, inRp):
        cR = '%s e. R' % IDX if inR else '-. %s e. R' % IDX
        cRp = "%s e. R'" % IDX if inRp else "-. %s e. R'" % IDX
        pha = '( ( %s /\\ %s ) /\\ %s )' % (ph, cR, cRp)
        L = Lifter(w, pha, 'ad2antrr')
        crs = w.s([], 'simplr', '( %s -> %s )' % (pha, cR))
        crps = w.s([], 'simpr', '( %s -> %s )' % (pha, cRp))
        # the per-state facts, generalised over m
        phm_ = '( %s /\\ m e. %s )' % (pha, NI)
        A_ = Lifter(w, phm_)
        mn = w.s([], 'simpr', '( %s -> m e. %s )' % (phm_, NI))
        cg, hab_m = W.wcongr(w, HAB(IDX, 'n'), {'n': 'm'}, 'n = m', {'n': w.s([], 'id', '( n = m -> n = m )')})
        assert hab_m == HAB(IDX, 'm'), hab_m
        hm = w.s([cg, A_(L(ha, HA_), HA_), mn], 'rspcdva', '( %s -> %s )' % (phm_, HAB(IDX, 'm')))
        b1 = w.s([hm, w.inst('simp1')], 'syl', '( %s -> ( ( C ` m ) = 1o <-> -. %s e. R ) )' % (phm_, IDX))
        b2 = w.s([hm, w.inst('simp2')], 'syl', "( %s -> ( ( C' ` %s ) = 1o <-> -. %s e. R' ) )" % (phm_, VA(IDX, 'm'), IDX))
        b3 = w.s([hm, w.inst('simp3')], 'syl', '( %s -> %s e. %s )' % (phm_, VB(IDX, 'm'), OI))
        crm = A_(crs, cR); crpm = A_(crps, cRp)
        if inR:
            nn = w.s([crm], 'notnotd', '( %s -> -. -. %s e. R )' % (phm_, IDX))
            f1 = w.s([nn, b1], 'mtbird', '( %s -> -. ( C ` m ) = 1o )' % phm_)
            va = NVF('F', 'm', UI)
            vae = w.s([crm], 'iftrued', '( %s -> %s = %s )' % (phm_, VA(IDX, 'm'), va))
        else:
            f1 = w.s([crm, b1], 'mpbird', '( %s -> ( C ` m ) = 1o )' % phm_)
            va = 'm'
            vae = w.s([crm], 'iffalsed', '( %s -> %s = %s )' % (phm_, VA(IDX, 'm'), va))
        v1 = w.s([vae], 'fveq2d', "( %s -> ( C' ` %s ) = ( C' ` %s ) )" % (phm_, VA(IDX, 'm'), va))
        v2 = w.s([v1], 'eqeq1d', "( %s -> ( ( C' ` %s ) = 1o <-> ( C' ` %s ) = 1o ) )" % (phm_, VA(IDX, 'm'), va))
        b2v = w.s([v2, b2], 'bitr3d', "( %s -> ( ( C' ` %s ) = 1o <-> -. %s e. R' ) )" % (phm_, va, IDX))
        if inRp:
            nn2 = w.s([crpm], 'notnotd', "( %s -> -. -. %s e. R' )" % (phm_, IDX))
            f2 = w.s([nn2, b2v], 'mtbird', "( %s -> -. ( C' ` %s ) = 1o )" % (phm_, va))
            vb = NVF("F'", va, UI1)
        else:
            f2 = w.s([crpm, b2v], 'mpbird', "( %s -> ( C' ` %s ) = 1o )" % (phm_, va))
            vb = va
        cg2, vbm = W.congr(w, VB(IDX, 'm'), {}, phm_, {}, rules={VA(IDX, 'm'): (va, vae)})
        VBv = "if ( %s e. R' , %s , %s )" % (IDX, NVF("F'", va, UI1), va)
        assert vbm == VBv, vbm
        vbe = w.s([crpm], 'iftrued' if inRp else 'iffalsed', '( %s -> %s = %s )' % (phm_, VBv, vb))
        vbe2 = w.s([cg2, vbe], 'eqtrd', '( %s -> %s = %s )' % (phm_, VB(IDX, 'm'), vb))
        f3a = w.s([vbe2], 'eleq1d', '( %s -> ( %s e. %s <-> %s e. %s ) )' % (phm_, VB(IDX, 'm'), OI, vb, OI))
        f3 = w.s([f3a, b3], 'mpbid', '( %s -> %s e. %s )' % (phm_, vb, OI))
        body = w.s([f1, f2, f3], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )'
                   % (phm_, concl(w, phm_, f1), concl(w, phm_, f2), concl(w, phm_, f3)))
        HYP = 'A. m e. %s %s' % (NI, concl(w, phm_, body))
        hyp = w.s([body], 'ralrimiva', '( %s -> %s )' % (pha, HYP))
        # the stacks and the lemma
        dka = L(dke, '( D ` K ) = %s' % XI); dja = L(dje, '( D ` J ) = %s' % YI)
        ka, ja, nea = L(kk, 'K e. %s' % DG), L(jj, 'J e. %s' % DG), L(ne, 'K =/= J')
        qa, da = L(qq, 'Q e. %s' % STMT_T), L(dd, 'D e. %s' % STK_T)
        meqa = L(meq, '( M ` A ) = %s' % BODY('Q'))
        heada = (L(tv, 'T e. V'), (L(head[1][0], 'C e. ( 2o ^m %s )' % SS), L(head[1][1], "C' e. ( 2o ^m %s )" % SS)),
                 (L(head[2][0], 'F e. %s' % HDL('K')), L(head[2][1], "F' e. %s" % HDL('J'))))
        nssa = L(nss, '%s C_ %s' % (NI, SS))
        if inR:
            xs = w.s([L(x1, concl(w, ph, x1)), crs], 'mpd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (pha, XI, UI, XI1))
            dkx = w.s([dka, xs], 'eqtrd', '( %s -> ( D ` K ) = ( <" %s "> ++ %s ) )' % (pha, UI, XI1))
            kfacts = (dkx, L(ui, '%s e. %s' % (UI, GK)), L(xi1w, '%s e. Word %s' % (XI1, GK)))
        else:
            xs = w.s([L(x2, concl(w, ph, x2)), crs], 'mpd', '( %s -> %s = %s )' % (pha, XI1, XI))
        if inRp:
            ys = w.s([L(y1, concl(w, ph, y1)), crps], 'mpd', "( %s -> %s = ( <\" %s \"> ++ %s ) )" % (pha, YI, UI1, YI1))
            djy = w.s([dja, ys], 'eqtrd', '( %s -> ( D ` J ) = ( <" %s "> ++ %s ) )' % (pha, UI1, YI1))
            jfacts = (djy, L(ui1, '%s e. %s' % (UI1, GJ)), L(yi1w, '%s e. Word %s' % (YI1, GJ)))
        else:
            ys = w.s([L(y2, concl(w, ph, y2)), crps], 'mpd', '( %s -> %s = %s )' % (pha, YI1, YI))
        if inR and inRp:
            ref = 'tm2frd2'; D2 = DP
            tree = (heada, ((ka, ja, nea), (qa, da), meqa), ((kfacts, jfacts), (nssa, hyp)))
        elif inR:
            ref = 'tm2frd2a'; D2 = UP('D', 'K', XI1)
            tree = (heada, ((ka, ja), (qa, da), meqa), (kfacts, (nssa, hyp)))
        elif inRp:
            ref = 'tm2frd2b'; D2 = UP('D', 'J', YI1)
            tree = (heada, ((ka, ja), (qa, da), meqa), (jfacts, (nssa, hyp)))
        else:
            ref = 'tm2frd2c'; D2 = 'D'
            tree = (heada, ((ka, ja), (qa, da), meqa), (nssa, hyp))
        res = applylem(w, pha, ref, tree, CONCL(D2))
        # uniformise the post-stack
        if D2 == DP:
            return res
        tva, xw, yw = L(tv, 'T e. V'), L(xi1w, '%s e. Word %s' % (XI1, GK)), L(yi1w, '%s e. Word %s' % (YI1, GJ))
        if inR:
            # DP = UP( UP(D,K,X1) , J , Y1 ) with Y1 = ( D ` J ) = ( UP(D,K,X1) ` J )
            dkcl = updcl(w, pha, 'D', 'K', XI1, tva, da, ka, xw)
            v = updnv(w, pha, 'D', 'K', XI1, 'J', tva, da, ka, elv(w, pha, xw, XI1), ja, L(nej, 'J =/= K'))
            yj = w.s([w.s([ys, dja], 'eqtr4d', '( %s -> %s = ( D ` J ) )' % (pha, YI1)), v], 'eqtr4d',
                     '( %s -> %s = ( %s ` J ) )' % (pha, YI1, UP('D', 'K', XI1)))
            eq = upidv(w, pha, UP('D', 'K', XI1), 'J', YI1, w.s([yj], 'eqcomd', '( %s -> ( %s ` J ) = %s )' % (pha, UP('D', 'K', XI1), YI1)), tva, dkcl, ja)
            eqc = w.s([eq], 'eqcomd', '( %s -> %s = %s )' % (pha, D2, DP))
        else:
            xk = w.s([xs, dka], 'eqtr4d', '( %s -> %s = ( D ` K ) )' % (pha, XI1))
            eqk = upidv(w, pha, 'D', 'K', XI1, w.s([xk], 'eqcomd', '( %s -> ( D ` K ) = %s )' % (pha, XI1)), tva, da, ka)
            eqkc = w.s([eqk], 'eqcomd', '( %s -> D = %s )' % (pha, UP('D', 'K', XI1)))
            if inRp:
                # D2 = UP(D,J,Y1) = UP( UP(D,K,X1) , J , Y1 )
                r, t = w.rewrite(D2, {'D': (UP('D', 'K', XI1), eqkc)}, pha)
                assert t == DP, t
                eqc = r
            else:
                yj = w.s([ys, dja], 'eqtr4d', '( %s -> %s = ( D ` J ) )' % (pha, YI1))
                eqj = upidv(w, pha, 'D', 'J', YI1, w.s([yj], 'eqcomd', '( %s -> ( D ` J ) = %s )' % (pha, YI1)), tva, da, ja)
                eqjc = w.s([eqj], 'eqcomd', '( %s -> D = %s )' % (pha, UP('D', 'J', YI1)))
                r, t = w.rewrite(UP('D', 'J', YI1), {'D': (UP('D', 'K', XI1), eqkc)}, pha)
                assert t == DP, t
                eqc = w.s([eqjc, r], 'eqtrd', '( %s -> D = %s )' % (pha, DP))
        o1 = w.s([eqc], 'opeq2d', '( %s -> <. p , %s >. = <. p , %s >. )' % (pha, D2, DP))
        o2 = w.s([o1], 'oveq2d', '( %s -> ( Q %s <. p , %s >. ) = ( Q %s <. p , %s >. ) )' % (pha, SA('T'), D2, SA('T'), DP))
        o3 = w.s([o2], 'eqeq2d', '( %s -> ( ( ( M ` A ) %s <. r , D >. ) = ( Q %s <. p , %s >. ) <-> ( ( M ` A ) %s <. r , D >. ) = ( Q %s <. p , %s >. ) ) )'
                 % (pha, SA('T'), SA('T'), D2, SA('T'), SA('T'), DP))
        o4 = w.s([o3], 'rexbidv', '( %s -> ( E. p e. %s ( ( M ` A ) %s <. r , D >. ) = ( Q %s <. p , %s >. ) <-> E. p e. %s ( ( M ` A ) %s <. r , D >. ) = ( Q %s <. p , %s >. ) ) )'
                 % (pha, OI, SA('T'), SA('T'), D2, OI, SA('T'), SA('T'), DP))
        o5 = w.s([o4], 'ralbidv', '( %s -> ( %s <-> %s ) )' % (pha, CONCL(D2), CONCL(DP)))
        return w.s([o5, res], 'mpbid', '( %s -> %s )' % (pha, CONCL(DP)))

    c11 = case(True, True); c10 = case(True, False)
    c01 = case(False, True); c00 = case(False, False)
    r1 = w.s([c11, c10], 'pm2.61dan', '( ( %s /\\ %s e. R ) -> %s )' % (ph, IDX, CONCL(DP)))
    r0 = w.s([c01, c00], 'pm2.61dan', '( ( %s /\\ -. %s e. R ) -> %s )' % (ph, IDX, CONCL(DP)))
    w.qed([r1, r0], 'pm2.61dan', '( %s -> %s )' % (ph, CONCL(DP)))
    return w.run()


if __name__ == '__main__':
    if want('tm2stkup3c'): tm2stkup3c()
    if want('tm2fadrd'): tm2fadrd()
