"""T5b: the prologue of `pow2` (TM/Prims.lean) --- ` push comma y ; push 1 y ;
isZero x s ` as ~ tm2fpshn twice and ~ tm2fiz (~ tm2fp2p )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_c_blk import leafsteps
from t5b_d_blp import pushstep

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fp2p():
    lab = 'tm2fp2p'
    tree, ph = TREE_P2P, cj(TREE_P2P)
    DJ = '( D ` J )'
    YDJ = CC(S1('Y'), DJ)
    FW = "{ q e. %s | ( S' ` q ) = ( O ` W ) }" % SS
    w = W(lab, 'The prologue of ` pow2 ` (TM/Prims.lean): ` push comma y ; push 1 y ; '
               'isZero x s ` pushes the terminated one on stack ` J ` (= y) and tests the '
               'exponent on ` K ` (= x) for zero, leaving the state in the fold class of '
               '~ tm2fiz (T7: ` flag = decide ( e = 0 ) ` ), in ` ( 2 x. ( # ` W ) ) + 7 ` '
               'steps.  Lean: ` pow2_correct ` , stages 1-3.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, a1, a2 = c[LAB('A')], c[LAB("A'")], c[LAB('A"')]
    kk, jj = c['K e. %s' % DG], c['J e. %s' % DG]
    nkj = c['K =/= J']
    yj, ypj = c['Y e. %s' % GJ], c["Y' e. %s" % GJ]
    dd, dke, nss = c[STKD('D')], c['( D ` K ) = %s' % WYX], c[SSS('N')]
    ww, xx = c[WRD('W', 'B')], c[WRD('X', GK)]
    meqA, meqA1 = c[MEQ('A', ST_Q1)], c[MEQ("A'", ST_Q2)]
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    ydjw = ccatw(w, ph, s1w(w, ph, yj, 'Y', GJ), djw, S1('Y'), DJ, GJ)
    ypydjw = ccatw(w, ph, s1w(w, ph, ypj, "Y'", GJ), ydjw, S1("Y'"), YDJ, GJ)
    C0 = CLN('A', 'N', 'D')
    # ---- t1: push Y on J
    t1, D1 = pushstep(w, ph, phm, meqA, al, a1, jj, yj, dd, nss, 'A', "A'", 'J', 'N', 'D')
    d1cl = updcl(w, ph, 'D', 'J', YDJ, tv, dd, jj, ydjw)
    # ---- t2: push Y' on J
    D2 = UP(D1, 'J', CC(S1("Y'"), '( %s ` J )' % D1))
    t2 = applylem(w, ph, 'tm2fpshn', ((phm, meqA1), (a1, a2, (jj, ypj)), (d1cl, nss)),
                  TRI(CLN("A'", 'N', D1), CLN('A"', 'N', D2), '1'))
    d1j = updkv(w, ph, 'D', 'J', YDJ, tv, dd, jj, elv(w, ph, ydjw, YDJ))
    col = up2(w, ph, 'D', 'J', YDJ, YPYDJ, tv, dd, jj, ydjw, ypydjw)
    D2c = UP('D', 'J', YPYDJ)
    tbl = {'( %s ` J )' % D1: (YDJ, d1j), UP(D1, 'J', YPYDJ): (D2c, col)}
    r2, D2n = evaluate(w, ph, D2, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert D2n == D2c, D2n
    t2r, _, _, _ = hrrw(w, ph, t2, CLN("A'", 'N', D1), CLN('A"', 'N', D2), '1', deq=clneq(w, ph, 'A"', 'N', r2, D2, D2c))
    t12 = hrseq(w, ph, phm, t1, t2r, C0, CLN("A'", 'N', D1), CLN('A"', 'N', D2c), '1', '1')
    # ---- t3: isZero at D2c
    d2cl = updcl(w, ph, 'D', 'J', YPYDJ, tv, dd, jj, ypydjw)
    d2k = w.s([updnv(w, ph, 'D', 'J', YPYDJ, 'K', tv, dd, jj, elv(w, ph, ypydjw, YPYDJ), kk, nkj), dke], 'eqtrd',
               '( %s -> ( %s ` K ) = %s )' % (ph, D2c, WYX))
    inst = ren(IZP_TREE, {'D': D2c})
    derived = {STKD(D2c): d2cl, '( %s ` K ) = %s' % (D2c, WYX): d2k}
    def look(t):
        if t in derived:
            return derived[t]
        return c[t]
    NZ = '( ( 2 x. ( # ` W ) ) + 5 )'
    t3 = applylem(w, ph, 'tm2fiz', leafsteps(inst, look), TRI(CLN('A"', 'N', D2c), CLN('E', FW, D2c), NZ))
    tall = hrseq(w, ph, phm, t12, t3, C0, CLN('A"', 'N', D2c), CLN('E', FW, D2c), '( 1 + 1 )', NZ)
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    bound(w, ph, phm, tall, C0, CLN('E', FW, D2c), '( ( 1 + 1 ) + %s )' % NZ, '( ( 2 x. ( # ` W ) ) + 7 )', {'( # ` W )': nw}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fp2p'): tm2fp2p()
