"""T5b: `pow2` assembled (~ tm2fp2 ): the prologue ~ tm2fp2p followed by the loop
~ tm2fp2q .  Lean: ` pow2_correct ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_c_blk import leafsteps

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fp2():
    lab = 'tm2fp2'
    tree, ph = TREE_P2, cj(TREE_P2)
    D1 = UP('D', 'J', YPYDJ)
    w = W(lab, 'The fragment ` pow2 ` of TM/Prims.lean: the exponent on stack ` K ` (= x) '
               'is consumed and ` 2 ^ e ` --- a one under ` e ` zeros, terminated (T7: '
               '` encodeNatGamma\' ( 2 ^ e ) ` by ` encnat2pow ` ) --- is pushed on ` J ` '
               '(= y), the scratch stacks ` I ` (= s), ` I\' ` (= s\') restored; the '
               'prologue ~ tm2fp2p followed by the loop, exit and drop ~ tm2fp2q .  '
               'Lean: ` pow2_correct ` , whose bound ` ( e + 1 ) ( 4 log e + 14 ) ` is T7\'s '
               'instance of this sum.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al = c[LAB('A')]
    kk, jj = c['K e. %s' % DG], c['J e. %s' % DG]
    nkj = c['K =/= J']
    dd = c[STKD('D')]
    yj, ypj = c['Y e. %s' % GJ], c["Y' e. %s" % GJ]
    init = c[INIT_P2]
    fam = c[FAM_P]
    rr = c['R e. NN0']
    ci = Ctx(w, ph, INIT_P2_TREE, root=init)
    x0dk = ci['%s = ( D ` K )' % XF('0')]
    x0w = ci['%s = %s' % (XF('0'), CC(WPF('0'), CC(S1('Y'), 'X"')))]
    h0e = ci['%s = %s' % (HF('0'), YPYDJ)]
    f0n = ci['%s C_ %s' % (FOLD(WPF('0')), NF('0'))]
    dke = w.s([x0dk, x0w], 'eqtr3d', '( %s -> ( D ` K ) = %s )' % (ph, CC(WPF('0'), CC(S1('Y'), 'X"'))))
    # ( W' ` 0 ) e. Word B"
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ R )' % ph)
    z0fz = w.s([w.s([z0a, rr, ge0], '3jca', '( %s -> ( 0 e. NN0 /\\ R e. NN0 /\\ 0 <_ R ) )' % ph), w.inst('elfz2nn0')], 'sylibr',
                '( %s -> 0 e. ( 0 ... R ) )' % ph)
    f0, _ = inst_v(w, ph, fam, cj(FAMB_P('i')), 'i', '0', z0fz)
    cf = Ctx(w, ph, FAMB_P('0'), root=f0)
    w0w, n0s = cf[WRD(WPF('0'), 'B"')], cf[SSS(NF('0'))]
    # ---- the prologue
    CP = CLN('Q', 'N0', 'D')
    FW0 = FOLD(WPF('0'))
    NP = '( ( 2 x. ( # ` %s ) ) + 7 )' % WPF('0')
    derivedp = {'( D ` K ) = %s' % CC(WPF('0'), CC(S1('Y'), 'X"')): dke, WRD(WPF('0'), 'B"'): w0w}
    def lookp(t):
        if t in derivedp:
            return derivedp[t]
        return c[t]
    tp = applylem(w, ph, 'tm2fp2p', leafsteps(PRO2_TREE, lookp), TRI(CP, CLN('A', FW0, D1), NP))
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    ydjw = ccatw(w, ph, s1w(w, ph, yj, 'Y', GJ), djw, S1('Y'), '( D ` J )', GJ)
    ypydjw = ccatw(w, ph, s1w(w, ph, ypj, "Y'", GJ), ydjw, S1("Y'"), CC(S1('Y'), '( D ` J )'), GJ)
    d1cl = updcl(w, ph, 'D', 'J', YPYDJ, tv, dd, jj, ypydjw)
    CL0 = CLN('A', NF('0'), D1)
    ssd = clnss(w, ph, 'A', FW0, NF('0'), D1, f0n)
    pcfg = cfgcl(w, ph, 'A', NF('0'), D1, tv, al, n0s, d1cl)
    tp2 = hrssd(w, ph, phm, tp, CP, CLN('A', FW0, D1), NP, CL0, ssd, pcfg)
    # ---- the loop at D := D1
    d1k = updnv(w, ph, 'D', 'J', YPYDJ, 'K', tv, dd, jj, elv(w, ph, ypydjw, YPYDJ), kk, nkj)
    d1j = updkv(w, ph, 'D', 'J', YPYDJ, tv, dd, jj, elv(w, ph, ypydjw, YPYDJ))
    ix = w.s([x0dk, d1k], 'eqtr4d', '( %s -> %s = ( %s ` K ) )' % (ph, XF('0'), D1))
    ih = w.s([h0e, d1j], 'eqtr4d', '( %s -> %s = ( %s ` J ) )' % (ph, HF('0'), D1))
    initq = w.s([ix, ih], 'jca', '( %s -> %s )' % (ph, sub(INIT_P, {'D': D1})))
    instq = ren(TREE_P2Q, {'D': D1})
    derived = {STKD(D1): d1cl, sub(INIT_P, {'D': D1}): initq}
    def look(t):
        if t in derived:
            return derived[t]
        return c[t]
    FINQ = UP(UP(D1, 'J', HF('R')), 'K', 'X"')
    NQ = "( ( ( R x. ( T' + 2 ) ) + 1 ) + ( ( # ` %s ) + 1 ) )" % WPF('R')
    tq = applylem(w, ph, 'tm2fp2q', leafsteps(instq, look), TRI(CL0, CLN('E1', SS, FINQ), NQ))
    tall = hrseq(w, ph, phm, tp2, tq, CP, CL0, CLN('E1', SS, FINQ), NP, NQ)
    # ---- the stacks collapse
    rle = w.s([w.s([rr, w.inst('nn0red')], 'syl', '( %s -> R e. RR )' % ph), w.inst('leidd')], 'syl', '( %s -> R <_ R )' % ph)
    rfz = w.s([w.s([rr, rr, rle], '3jca', '( %s -> ( R e. NN0 /\\ R e. NN0 /\\ R <_ R ) )' % ph), w.inst('elfz2nn0')], 'sylibr',
               '( %s -> R e. ( 0 ... R ) )' % ph)
    fR, _ = inst_v(w, ph, fam, cj(FAMB_P('i')), 'i', 'R', rfz)
    cR = Ctx(w, ph, FAMB_P('R'), root=fR)
    hRw = cR[WRD(HF('R'), GJ)]
    col = up2(w, ph, 'D', 'J', YPYDJ, HF('R'), tv, dd, jj, ypydjw, hRw)
    FIN = UP(UP('D', 'J', HF('R')), 'K', 'X"')
    r, fn = w.rewrite(FINQ, {UP(D1, 'J', HF('R')): (UP('D', 'J', HF('R')), col)}, ph)
    assert fn == FIN, fn
    hrrw(w, ph, tall, CP, CLN('E1', SS, FINQ), '( %s + %s )' % (NP, NQ), deq=clneq(w, ph, 'E1', SS, r, FINQ, FIN), qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fp2'): tm2fp2()
