"""T5b: `bitlen` assembled (~ tm2fbll ): the prologue ~ tm2fblp followed by the
loop ~ tm2fblq , the stacks collapsing to one update of the counter stack.
Lean: ` bitlen_runs ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_c_blk import leafsteps

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fbll():
    lab = 'tm2fbll'
    tree, ph = TREE_BLL, cj(TREE_BLL)
    RW = '( reverse ` W0 )'
    YDK = CC(S1('Y'), '( D ` K )')
    RWYDK = CC(RW, YDK)
    YX0 = CC(S1('Y'), 'X0')
    D1 = UP3('D', 'K', RWYDK, 'J', YX0, 'I', YDI)
    n = NW0
    w = W(lab, 'The fragment ` bitlen ` of TM/Prims.lean: the number ` W0 ` on stack ` J ` '
               '(= x) is reversed onto the scratch stack ` K ` (= s), scanned back most-'
               'significant bit first while the counter on ` I ` (= y) is incremented '
               'from the first one on (scratch ` I\' ` = s\'), and everything but the '
               'counter is restored: ` J ` holds ` W0 ` again, ` K ` and ` I\' ` are as '
               'they were, ` I ` holds the final counter word ` ( W ` ( # ` W0 ) ) ` (T7: '
               'the bit length of the number, terminated, above what was there).  The '
               'prologue ~ tm2fblp followed by the loop ~ tm2fblq ; the per-iteration content '
               'is the families of blueprint D3, D4.  Lean: ` bitlen_runs ` , whose bound '
               '` ( |l| + 2 ) ( 2 log |l| + 10 ) ` is T7\'s instance of this sum.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    dd = c[STKD('D')]
    b0k, b0j, yk, yi = c['B0 C_ %s' % GK], c['B0 C_ %s' % GJ], c['Y e. %s' % GK], c['Y e. %s' % GI]
    w0w, x0w = c[WRD('W0', 'B0')], c[WRD('X0', GJ)]
    init = c[INIT_L]
    fin2 = c[FIN_L2]
    hne = w.s([fin2], 'simprd', '( %s -> %s = ( D ` J ) )' % (ph, HF(n)))
    finl = w.s([fin2], 'simpld', '( %s -> %s )' % (ph, FIN_L))
    fam = c[sub(FAM_Q, QMAP)]
    # ---- the prologue
    CP = CLN('R', 'N0', 'D')
    CL0 = CLN('A', NF('0'), D1)
    NP = '( %s + 5 )' % n
    tp = applylem(w, ph, 'tm2fblp', leafsteps(PRO_TREE, lambda t: c[t]), TRI(CP, CL0, NP))
    # ---- the loop at D := D1
    # words on the three stacks after the prologue
    dkw, djw, diw = stkfv(w, ph, 'D', 'K', tv, dd, kk), stkfv(w, ph, 'D', 'J', tv, dd, jj), stkfv(w, ph, 'D', 'I', tv, dd, ii)
    ysk, ysi = s1w(w, ph, yk, 'Y', GK), s1w(w, ph, yi, 'Y', GI)
    ydkw = ccatw(w, ph, ysk, dkw, S1('Y'), '( D ` K )', GK)
    rwb = revw(w, ph, w0w, 'W0', 'B0')
    rwk = sswordd(w, ph, rwb, RW, 'B0', GK, b0k)
    rwydkw = ccatw(w, ph, rwk, ydkw, RW, YDK, GK)
    ysj = s1w(w, ph, c['Y e. %s' % GJ], 'Y', GJ)
    yx0w = ccatw(w, ph, ysj, x0w, S1('Y'), 'X0', GJ)
    ydiw = ccatw(w, ph, ysi, diw, S1('Y'), '( D ` I )', GI)
    a = updcl(w, ph, 'D', 'K', RWYDK, tv, dd, kk, rwydkw)
    b = updcl(w, ph, UP('D', 'K', RWYDK), 'J', YX0, tv, a, jj, yx0w)
    d1cl = updcl(w, ph, UP(UP('D', 'K', RWYDK), 'J', YX0), 'I', YDI, tv, b, ii, ydiw)
    U2 = UP(UP('D', 'K', RWYDK), 'J', YX0)
    rv, yv, iv = elv(w, ph, rwydkw, RWYDK), elv(w, ph, yx0w, YX0), elv(w, ph, ydiw, YDI)
    vk1 = updnv(w, ph, U2, 'I', YDI, 'K', tv, b, ii, iv, kk, nki)
    vk2 = updnv(w, ph, UP('D', 'K', RWYDK), 'J', YX0, 'K', tv, a, jj, yv, kk, nkj)
    vk3 = updkv(w, ph, 'D', 'K', RWYDK, tv, dd, kk, rv)
    vk = w.s([w.s([vk1, vk2], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` K ) )' % (ph, D1, UP('D', 'K', RWYDK))), vk3], 'eqtrd',
             '( %s -> ( %s ` K ) = %s )' % (ph, D1, RWYDK))
    vj1 = updnv(w, ph, U2, 'I', YDI, 'J', tv, b, ii, iv, jj, nji)
    vj2 = updkv(w, ph, UP('D', 'K', RWYDK), 'J', YX0, tv, a, jj, yv)
    vj = w.s([vj1, vj2], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D1, YX0))
    vi = updkv(w, ph, U2, 'I', YDI, tv, b, ii, iv)
    x0e = w.s([init, w.inst('simp1')], 'syl', '( %s -> %s = %s )' % (ph, XF('0'), RWYDK))
    h0e = w.s([init, w.inst('simp2')], 'syl', '( %s -> %s = %s )' % (ph, HF('0'), YX0))
    w0e = w.s([init, w.inst('simp3')], 'syl', '( %s -> %s = %s )' % (ph, WF('0'), YDI))
    ix = w.s([x0e, vk], 'eqtr4d', '( %s -> %s = ( %s ` K ) )' % (ph, XF('0'), D1))
    ih = w.s([h0e, vj], 'eqtr4d', '( %s -> %s = ( %s ` J ) )' % (ph, HF('0'), D1))
    iw = w.s([w0e, vi], 'eqtr4d', '( %s -> %s = ( %s ` I ) )' % (ph, WF('0'), D1))
    initq = w.s([ix, ih, iw], '3jca', '( %s -> %s )' % (ph, sub(INIT_Q, {'D': D1})))
    nw = w.s([w0w, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, n))
    QMAPD = dict(QMAP); QMAPD['D'] = D1
    instq = ren(TREE_BLQ, QMAPD)
    derived = {STKD(D1): d1cl, sub(INIT_Q, {'D': D1}): initq, '%s e. NN0' % n: nw, FIN_L: finl}
    def look(t):
        if t in derived:
            return derived[t]
        return c[t]
    N1L = '( %s + 1 )' % n
    FINQ = UP3(D1, 'K', '( D ` K )', 'J', HF(n), 'I', WF(n))
    NQ = "( ( %s x. ( T' + 4 ) ) + 5 )" % n
    tq = applylem(w, ph, 'tm2fblq', leafsteps(instq, look), TRI(CL0, CLN('E', NF(N1L), FINQ), NQ))
    tall = hrseq(w, ph, phm, tp, tq, CP, CL0, CLN('E', NF(N1L), FINQ), NP, NQ)
    # ---- the stacks collapse
    nle = w.s([w.s([nw, w.inst('nn0red')], 'syl', '( %s -> %s e. RR )' % (ph, n)), w.inst('leidd')], 'syl', '( %s -> %s <_ %s )' % (ph, n, n))
    nfz = w.s([w.s([nw, nw, nle], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, n, n, n, n)),
               w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, n, n))
    fn, _ = inst_v(w, ph, fam, cj(FAMB_Q('i')), 'i', n, nfz)
    cf = Ctx(w, ph, FAMB_Q(n), root=fn)
    hnw, wnw = cf[WRD(HF(n), GJ)], cf[WRD(WF(n), GI)]
    col, RHS6 = up6(w, ph, 'D', RWYDK, '( D ` K )', YX0, HF(n), YDI, WF(n), tv, dd, nkj, nki, nji, kk, jj, ii,
                    rwydkw, dkw, yx0w, hnw, ydiw, wnw)
    uk = upid(w, ph, 'D', 'K', tv, dd, kk)
    hnec = w.s([hne], 'eqcomd', '( %s -> ( D ` J ) = %s )' % (ph, HF(n)))
    ujh = w.s([upeq(w, ph, 'D', 'J', hnec, '( D ` J )', HF(n)), upid(w, ph, 'D', 'J', tv, dd, jj)], 'eqtr3d',
              '( %s -> %s = D )' % (ph, UP('D', 'J', HF(n))))
    tbl = {FINQ: (RHS6, col), UP('D', 'K', '( D ` K )'): ('D', uk), UP('D', 'J', HF(n)): ('D', ujh)}
    ps, postn = evaluate(w, ph, FINQ, {}, extra_rules=(lambda n_: tbl.get(n_.text())))
    FIN = UP('D', 'I', WF(n))
    assert postn == FIN, postn
    hrrw(w, ph, tall, CP, CLN('E', NF(N1L), FINQ), '( %s + %s )' % (NP, NQ),
         deq=clneq(w, ph, 'E', NF(N1L), ps, FINQ, FIN), qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fbll'): tm2fbll()
