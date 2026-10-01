"""T-TAB: the assemblies on the slot loop: ~ tm2fctb (Lean ` copyTbl_runs `: two
marker pushes, ~ tm2ftfs with the body ` copySlot ; moveSlot ` one triple, the
` walkUp ` triple) and ~ tm2fdps (` dpStepF_runs `: a triple, the push of
` bra ` , a triple, ~ tm2fwup with the body ` dpBodyF ` one triple, a triple)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ttablib import *
from t6lib import gamk, lgk, wgk, ccatg, stkfvg
from t6lib import updcl as updcl6
from ttab_b_slot import LCtx, phmparts, instc, pushat6, MTY
from ttab_a_fs import rtcl

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fctb():
    lab = 'tm2fctb'
    tree, ph = TREE_CTB, cj(TREE_CTB)
    w = W(lab, 'Copying the DP table in reversed slot order, ` copyTbl src dst hold s s\' ` (TM/Table.lean): '
               '` pushSym dst blank ` and ` pushSym hold blank ` push the marker ` Y ` on ` J ` and ` I ` (~ tm2fpshn ), '
               '` forSlots src ( copySlot ; moveSlot ) ` is ~ tm2ftfs from ` Q0 ` with the body one hypothesis triple '
               'per slot (T7: ~ tm2fcps , ~ tm2fmvs ), and ` walkUp src s\' s hold ` is a triple (T7: ~ tm2fwup ).  '
               'Lean: ` copyTbl_runs ` , bound ` copyC L N b ` .')
    c = Ctx(w, ph, tree)
    phm, geq = c[PHM], c[GEQ]
    tv, mt = phmparts(w, ph, phm)
    ycl = c["Y e. %s" % GAM]
    # ---- the two pushes
    p1, pc1, jd, gej = pushat6(w, ph, c, tv, mt, geq, c[GAMK('J')], ycl, 'P0', 'P1', 'J', 'Y', 'O', 'D', c[STKD('D')], c[SSS('O')])
    D1 = YPUSH('D', 'J', 'Y')
    C0, C1 = CLN('P0', 'O', 'D'), CLN('P1', 'O', D1)
    assert triple_parts(pc1)[:2] == (C0, C1), pc1
    yw = w.s([ycl], 's1cld', '( %s -> <" Y "> e. %s )' % (ph, GAMW))
    djw = stkfvg(w, ph, 'D', 'J', tv, c[STKD('D')], jd, gej)
    x1 = ccatg(w, ph, '<" Y ">', '( D ` J )', yw, djw)
    d1cl = updcl6(w, ph, 'D', 'J', CC(S1('Y'), '( D ` J )'), tv, c[STKD('D')], jd, gej, x1)
    p2, pc2, idd, gei = pushat6(w, ph, c, tv, mt, geq, c[GAMK('I')], ycl, 'P1', 'Q0', 'I', 'Y', 'O', D1, d1cl, c[SSS('O')])
    D2x = YPUSH(D1, 'I', 'Y')
    C2x = CLN('Q0', 'O', D2x)
    assert triple_parts(pc2)[:2] == (C1, C2x), pc2
    xv = elv(w, ph, x1, CC(S1('Y'), '( D ` J )'))
    di = updnv(w, ph, 'D', 'J', CC(S1('Y'), '( D ` J )'), 'I', tv, c[STKD('D')], jd, xv, idd, c['I =/= J'])
    r1, new = w.rewrite(D2x, {'( %s ` I )' % D1: ('( D ` I )', di)}, ph)
    INITR = UP(D1, 'I', CC(S1('Y'), '( D ` I )'))
    assert new == INITR, new
    ie = w.s([c[INIT_CTB]], 'eqcomd', '( %s -> %s = %s )' % (ph, INITR, PF('0')))
    r2 = w.s([r1, ie], 'eqtrd', '( %s -> %s = %s )' % (ph, D2x, PF('0')))
    C2 = CLN('Q0', 'O', PF('0'))
    p2r, _, _, _ = hrrw(w, ph, p2, C1, C2x, '1', deq=clneq(w, ph, 'Q0', 'O', r2, D2x, PF('0')))
    # ---- the slot loop and the walk back
    fs = w.s([c[cj(TREE_FSQ)], w.inst('tm2ftfs')], 'syl', '( %s -> %s )' % (ph, sub(CONCL_FS, FS_Q0)))
    C3, C4 = CLN('E', NF('R'), PF('R')), CLN("E'", "N'", "D'")
    q = hrseq(w, ph, phm, p1, p2r, C0, C1, C2, '1', '1')
    q = hrseq(w, ph, phm, q, fs, C0, C2, C3, '( 1 + 1 )', BND_FS)
    q = hrseq(w, ph, phm, q, c[TRI(C3, C4, 'U')], C0, C3, C4, '( ( 1 + 1 ) + %s )' % BND_FS, 'U')
    rt2 = rtcl(w, ph, c['R e. NN0'], c["T' e. NN0"])
    bound0(w, ph, phm, q, C0, C4, '( ( ( 1 + 1 ) + %s ) + U )' % BND_FS, triple_parts(CONCL_CTB)[2],
           {'U': c['U e. NN0'], "( R x. ( T' + 2 ) )": rt2}, qed=True)
    return w.run()


def tm2fdps():
    lab = 'tm2fdps'
    tree, ph = TREE_DPS, cj(TREE_DPS)
    w = W(lab, 'One DP step on the stacks, ` dpStepF np nL snap acc s t ` (TM/Table.lean): ` dup nL t s ; dup np nL s ; '
               'modFrag ` is a hypothesis triple (T7: ~ tm2fdup , ~ tm2fmod + ~ tm2fcan ), ` pushSym snap bra ` pushes '
               'the letter ` Y ` on ` K ` (~ tm2fpshn ), ` dup np snap s ; dup nL np s ; setIfNoneF ; pushNum nL 0 ` '
               'is a triple (T7: ~ tm2fsin ), ` forSlots snap dpBodyF ; popTop snap ` is ~ tm2fwup from ` P1 ` with the '
               'body one triple per slot (T7: ~ tm2fdpb ), and the three ` dropNum ` s are a triple.  Lean: '
               '` dpStepF_runs ` , bound ` dpC L N b ` .')
    c = Ctx(w, ph, tree)
    phm, geq = c[PHM], c[GEQ]
    tv, mt = phmparts(w, ph, phm)
    C0, C1 = CLN('P0', 'O', 'D'), CLN('Q0', "O'", "D'")
    ps, pc, kd, gek = pushat6(w, ph, c, tv, mt, geq, c[GAMK('K')], c["Y e. %s" % GAM], 'Q0', "Q'", 'K', 'Y', "O'", "D'",
                              c[STKD("D'")], c[SSS("O'")])
    C2 = CLN("Q'", "O'", YPUSH("D'", 'K', 'Y'))
    assert triple_parts(pc)[:2] == (C1, C2), pc
    C3, C4, C5 = CLN('P1', 'O"', PF('0')), CLN("E'", "N'", UPR), CLN('E"', 'N0', 'D0')
    wu = w.s([c[cj(TREE_WUPP)], w.inst('tm2fwup')], 'syl', '( %s -> %s )' % (ph, sub(CONCL_WUP, WUP_P1)))
    assert sub(CONCL_WUP, WUP_P1) == TRI(C3, C4, BND_WUP)
    q = hrseq(w, ph, phm, c[TRIP_DPS1], ps, C0, C1, C2, 'U', '1')
    q = hrseq(w, ph, phm, q, c[TRIP_DPS2], C0, C2, C3, '( U + 1 )', "U'")
    q = hrseq(w, ph, phm, q, wu, C0, C3, C4, "( ( U + 1 ) + U' )", BND_WUP)
    q = hrseq(w, ph, phm, q, c[TRIP_DPS3], C0, C4, C5, "( ( ( U + 1 ) + U' ) + %s )" % BND_WUP, 'U"')
    rt2 = rtcl(w, ph, c['R e. NN0'], c["T' e. NN0"])
    bound0(w, ph, phm, q, C0, C5, "( ( ( ( U + 1 ) + U' ) + %s ) + U\" )" % BND_WUP, triple_parts(CONCL_DPS)[2],
           {'U': c['U e. NN0'], "U'": c["U' e. NN0"], 'U"': c['U" e. NN0'], "( R x. ( T' + 2 ) )": rt2}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fctb'): tm2fctb()
    if want('tm2fdps'): tm2fdps()
