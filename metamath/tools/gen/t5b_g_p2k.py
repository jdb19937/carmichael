"""T5b: one iteration of the loop of `pow2` (TM/Prims.lean): ` predNum x s' ;
push 0 y ; isZero x s ` after the loop test, as ~ tm2lbrt , ~ tm2fprdn ,
~ tm2fpshn , ~ tm2fiz sequenced (~ tm2fp2k ); blueprint D2, D3."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
from t5b_b_iter import brstep
from t5b_c_blk import leafsteps
from t5b_d_blp import pushstep

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2fp2k():
    lab = 'tm2fp2k'
    tree, ph = TREE_P2K, cj(TREE_P2K)
    GWZ0 = CC(GW, 'Z0')
    D1 = UP('D', 'K', 'X0')
    D2 = D2_P2
    FW = FOLD("W'")
    w = W(lab, 'One iteration of the loop of ` pow2 ` (TM/Prims.lean): the test at ` A ` '
               'succeeds on the class ` N ` (T7: ` flag = false ` , the exponent not yet '
               'zero), ` predNum ` decrements the number on stack ` K ` (~ tm2fprdn at the '
               'running class ` N1 ` , the run ` W ` of zeros and the exit ` Z0 ` by its '
               'three-way disjunction), a zero bit ` Z1 ` is pushed on ` J ` (~ tm2fpshn ), '
               'and ` isZero ` tests the decremented number ` W\' ` (~ tm2fiz ), landing in '
               'the fold class, which the hypothesis puts in ` N\' ` (blueprint D3).  '
               'Lean: ` pow2Body_runs ` , with ` predNum_correct ` and ` isZero_correct ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, a1, e1, e2 = c[LAB('A')], c[LAB("A'")], c[LAB("E'")], c[LAB('E"')]
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki = c['K =/= J'], c['K =/= I']
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    c0, qq = c[CTY('C0')], c[STMT('Q')]
    dd, dke = c[STKD('D')], c['( D ` K ) = %s' % WZX]
    x0e1, x0e2 = c['X0 = %s' % CC(GW, 'Z0')], c['X0 = %s' % WPYX]
    ww, wpw, xpw2 = c[WRD('W', 'B')], c[WRD("W'", 'B"')], c[WRD('X"', GK)]
    bpk, bppk, gf = c["B' C_ %s" % GK], c['B" C_ %s' % GK], c["G : B --> B'"]
    yk, z1j = c['Y e. %s' % GK], c['Z1 e. %s' % GJ]
    nss, nn1, n1s, n2s = c[SSS('N')], c['N C_ N1'], c[SSS('N1')], c[SSS("N'")]
    htn1 = c[HT('N1')]
    fss, lte, tt = c["%s C_ N'" % FW], c["( ( ( 2 x. ( # ` W ) ) + 3 ) + ( ( 2 x. ( # ` W' ) ) + 5 ) ) <_ T'"], c["T' e. NN0"]
    meqA, meqE1 = c[MEQ('A', STM_T)], c[MEQ("E'", STM_PZ)]
    # words
    wpk = sswordd(w, ph, wpw, "W'", 'B"', GK, bppk)
    ysk = s1w(w, ph, yk, 'Y', GK)
    yxw = ccatw(w, ph, ysk, xpw2, S1('Y'), 'X"', GK)
    x0w = w.s([x0e2, ccatw(w, ph, wpk, yxw, "W'", CC(S1('Y'), 'X"'), GK)], 'eqeltrd', '( %s -> X0 e. Word %s )' % (ph, GK))
    d1cl = updcl(w, ph, 'D', 'K', 'X0', tv, dd, kk, x0w)
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    z1djw = ccatw(w, ph, s1w(w, ph, z1j, 'Z1', GJ), djw, S1('Z1'), '( D ` J )', GJ)
    d2cl = updcl(w, ph, D1, 'J', Z1DJ, tv, d1cl, jj, z1djw)
    # ---- t1: the test at A on N
    sr = w.s([nn1, w.inst('ssralv')], 'syl', '( %s -> ( %s -> %s ) )' % (ph, HT('N1'), HT('N')))
    htn = w.s([htn1, sr], 'mpd', '( %s -> %s )' % (ph, HT('N')))
    C0 = CLN('A', 'N', 'D'); C1 = CLN("A'", 'N', 'D')
    t1 = brstep(w, ph, 'tm2lbrt', phm, meqA, al, a1, dd, c0, qq, nss, htn, 'A', "A'", 'C0', 'Q', 'N', 'D')
    # ---- t2: predNum at N1, shrunk to N
    NP = '( ( 2 x. ( # ` W ) ) + 3 )'
    P2PRE, P2POST = CLN("A'", 'N1', 'D'), CLN("E'", 'N1', UP('D', 'K', GWZ0))
    t2 = applylem(w, ph, 'tm2fprdn', leafsteps(PRD_TREE, lambda t: c[t]), TRI(P2PRE, P2POST, NP))
    ssn = clnss(w, ph, "A'", 'N', 'N1', 'D', nn1)
    t2b = hrssc(w, ph, phm, t2, P2PRE, P2POST, NP, C1, ssn)
    x0c = w.s([x0e1], 'eqcomd', '( %s -> %s = X0 )' % (ph, GWZ0))
    C2 = CLN("E'", 'N1', D1)
    t2c, _, _, _ = hrrw(w, ph, t2b, C1, P2POST, NP, deq=clneq(w, ph, "E'", 'N1', upeq(w, ph, 'D', 'K', x0c, GWZ0, 'X0'), UP('D', 'K', GWZ0), D1))
    t12 = hrseq(w, ph, phm, t1, t2c, C0, C1, C2, '1', NP)
    N12 = '( 1 + %s )' % NP
    # ---- t3: push Z1 on J
    D3 = UP(D1, 'J', CC(S1('Z1'), '( %s ` J )' % D1))
    t3 = applylem(w, ph, 'tm2fpshn', ((phm, meqE1), (e1, e2, (jj, z1j)), (d1cl, n1s)),
                  TRI(C2, CLN('E"', 'N1', D3), '1'))
    d1j = updnv(w, ph, 'D', 'K', 'X0', 'J', tv, dd, kk, elv(w, ph, x0w, 'X0'), jj, njk)
    r3, D3p = w.rewrite(D3, {'( %s ` J )' % D1: ('( D ` J )', d1j)}, ph)
    assert D3p == D2, D3p
    C3 = CLN('E"', 'N1', D2)
    t3r, _, _, _ = hrrw(w, ph, t3, C2, CLN('E"', 'N1', D3), '1', deq=clneq(w, ph, 'E"', 'N1', r3, D3, D2))
    t123 = hrseq(w, ph, phm, t12, t3r, C0, C2, C3, N12, '1')
    N123 = '( %s + 1 )' % N12
    # ---- t4: isZero at D2 , N1 , into the fold class, widened to N'
    d2k1 = updnv(w, ph, D1, 'J', Z1DJ, 'K', tv, d1cl, jj, elv(w, ph, z1djw, Z1DJ), kk, nkj)
    d2k2 = updkv(w, ph, 'D', 'K', 'X0', tv, dd, kk, elv(w, ph, x0w, 'X0'))
    d2k = w.s([w.s([d2k1, d2k2], 'eqtrd', '( %s -> ( %s ` K ) = X0 )' % (ph, D2)), x0e2], 'eqtrd',
               '( %s -> ( %s ` K ) = %s )' % (ph, D2, WPYX))
    inst = ren(IZ_TREE, {'D': D2})
    derived = {STKD(D2): d2cl, '( %s ` K ) = %s' % (D2, WPYX): d2k}
    def look(t):
        if t in derived:
            return derived[t]
        return c[t]
    NZ = "( ( 2 x. ( # ` W' ) ) + 5 )"
    C4 = CLN('A', FW, D2)
    t4 = applylem(w, ph, 'tm2fiz', leafsteps(inst, look), TRI(C3, C4, NZ))
    C5 = CLN('A', "N'", D2)
    ssd = clnss(w, ph, 'A', FW, "N'", D2, fss)
    pcfg = cfgcl(w, ph, 'A', "N'", D2, tv, al, n2s, d2cl)
    t4b = hrssd(w, ph, phm, t4, C3, C4, NZ, C5, ssd, pcfg)
    tall = hrseq(w, ph, phm, t123, t4b, C0, C3, C5, N123, NZ)
    NALL = '( %s + %s )' % (N123, NZ)
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    npw = w.s([wpw, w.inst('lencl')], 'syl', "( %s -> ( # ` W' ) e. NN0 )" % ph)
    bound(w, ph, phm, tall, C0, C5, NALL, "( T' + 2 )", {'( # ` W )': nw, "( # ` W' )": npw, "T'": tt}, hyps=[lte], qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fp2k'): tm2fp2k()
