"""T-TAB: the slot primitives ~ tm2fmvs (Lean ` moveSlot_runs `) and ~ tm2fcps
(` copySlot_runs `): ` peekKet ` , the ` ite ` on ` flag ` as a disjunction
(blueprint D5), the ` ket ` case executed (pop and push, or push), the list
case one hypothesis triple (two ` revList ` s, or ` copyList `)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ttablib import *
from t6lib import gamk, lgk, wgk, s1g, ccatg, stkfvg
from t6lib import updcl as updcl6

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

MTY = 'M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T )'


class LCtx:
    """a context whose leaves are c's lifted to the antecedent pa (one adantr, or a chain of Lifters)"""
    def __init__(self, w, pa, c):
        self.c = c; self.L = Lifter(w, pa)

    def __getitem__(self, t):
        return self.L(self.c[t], t)


def phmparts(w, ph, phm):
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    mt = w.s([phm, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, MTY))
    return tv, mt


def instc(w, ph, look, tv, mt, label, m, extra):
    ex = {'T e. V': tv, MTY: mt}
    ex.update(extra)
    return inst(w, ph, label, m, Builder(w, ph, look, ex))


def peekat(w, ph, look, tv, mt, extra, A, E, K, F, D, Z, X, N, N2, ref='tm2lpk'):
    return instc(w, ph, look, tv, mt, ref, {'A': A, 'E': E, 'K': K, 'F': F, 'D': D, 'Z': Z, 'X': X, 'N': N, "N'": N2}, extra)


def pushat(w, ph, look, tv, mt, extra, A, E, K, Y, N, D):
    """tm2fpshn at label A: push the letter Y on stack K; extra must give K e. DG, Y e. GK, D e. Stk, N C_ S"""
    return instc(w, ph, look, tv, mt, 'tm2fpshn', {'A': A, 'E': E, 'K': K, 'Z': Y, 'N': N, 'D': D}, extra)


def pushat6(w, ph, look, tv, mt, geq, kk8, ycl, A, E, K, Y, N, D, dcl, nss):
    """tm2fpshn at TMGam: K e. ( 0 ..^ 8 ) (kk8), Y e. Gamma' (ycl)"""
    kd, ge = gamk(w, ph, K, geq, kk8)
    yk = lgk(w, ph, Y, K, ge, ycl)
    s, cc = pushat(w, ph, look, tv, mt, {'%s e. %s' % (K, DG): kd, '%s e. %s' % (Y, GX(K)): yk, STKD(D): dcl, SSS(N): nss},
                   A, E, K, Y, N, D)
    return s, cc, kd, ge


def brat(w, ph, look, tv, mt, ref, A, E, Q, C, N, D, extra):
    """tm2lbrt (ref, true branch to E, other goto Q) / tm2fbrg (false branch to E, other Q) at A on class N, stacks D;
    extra must hold the test on N, D e. Stk, N C_ S, and the statement typing of Q"""
    return instc(w, ph, look, tv, mt, ref, {'A': A, 'E': E, 'Q': Q, 'C': C, 'N': N, 'D': D}, extra)


def gotost(w, ph, tv, X, xl):
    return gotocl(w, ph, tv, X, xl)


def slot(kind):
    """kind 'mv' (moveSlot) or 'cp' (copySlot)"""
    mv = kind == 'mv'
    lab = 'tm2fmvs' if mv else 'tm2fcps'
    tree = TREE_MVS if mv else TREE_CPS
    ph = cj(tree)
    CASEA, CASEB, DISJ = (CASE_MVA, CASE_MVB, DISJ_MV) if mv else (CASE_CPA, CASE_CPB, DISJ_CP)
    if mv:
        desc = ('Moving the top slot of the DP table, ` moveSlot src dst s s\' ` (TM/Table.lean): ` peekKet src ` '
                '(~ tm2lpk ) reads the top letter ` Z ` into the class ` N1 ` ; ` Frag.ite ` on ` flag ` either pops '
                'the ` ket ` (~ tm2lpop ) and pushes the letter ` Y ` on ` J ` (~ tm2fpshn ), or runs '
                '` revList src s\' s ; revList s\' dst s ` as one hypothesis triple (T7: ~ tm2lrevn twice).  Lean: '
                '` moveSlot_runs ` , bound ` slotC N b ` at ` T1 := N ( 4 b + 12 ) + 8 ` .')
    else:
        desc = ('Copying the top slot of the DP table, ` copySlot src dst s s\' ` (TM/Table.lean): ` peekKet src ` '
                '(~ tm2lpk ) reads the top letter ` Z ` into ` N1 ` ; ` Frag.ite ` on ` flag ` either pushes the letter '
                '` Y ` on ` J ` (~ tm2fpshn ; the exit class contains ` N1 ` ) or runs ` copyList src dst s s\' ` as a '
                'hypothesis triple (T7: ~ tmilcpyn ).  Lean: ` copySlot_runs ` , bound ` N ( 6 b + 17 ) + 11 ` at '
                '` T1 := N ( 6 b + 17 ) + 9 ` .')
    w = W(lab, desc)
    c = Ctx(w, ph, tree)
    phm, geq = c[PHM], c[GEQ]
    tv, mt = phmparts(w, ph, phm)
    # ---- the peek at P0
    pk, cc = peekat(w, ph, c, tv, mt, {}, 'P0', "B'", 'K', 'F', 'D', 'Z', 'X', 'N', 'N1')
    C0, C1, CE = CLN('P0', 'N', 'D'), CLN("B'", 'N1', 'D'), CLN('E', "N'", "D'")
    assert triple_parts(cc)[:2] == (C0, C1), cc
    t1n = c['T1 e. NN0']
    MB = '( T1 + 1 )'
    ge0 = gotocl(w, ph, tv, 'E0', c[LAB('E0')])
    gbq = gotocl(w, ph, tv, 'B"', c[LAB('B"')])

    def caseA(pha, cs):
        L = LCtx(w, pha, c)
        tva, mta = L.L(tv, 'T e. V'), L.L(mt, MTY)
        if mv:
            cx = Ctx(w, pha, (HT('N1', 'C'), HPK('N1', "F'", 'Z', "N'"), "D' = %s" % D2_MVS), root=cs)
        else:
            cx = Ctx(w, pha, (HT('N1', 'C'), "N1 C_ N'", "D' = %s" % YPUSH('D', 'J', 'Y')), root=cs)
        b, bc = brat(w, pha, L, tva, mta, 'tm2lbrt', "B'", 'B"', GT('E0'), 'C', 'N1', 'D',
                     {HT('N1', 'C'): cx[HT('N1', 'C')], STMT(GT('E0')): L.L(ge0, STMT(GT('E0')))})
        CBq = CLN('B"', 'N1', 'D')
        assert triple_parts(bc)[:2] == (C1, CBq), bc
        kk8, jj8 = L[GAMK('K')], L[GAMK('J')]
        if mv:
            # pop at B" into N', then push Y on J at B1_
            pp, pc = peekat(w, pha, L, tva, mta, {HPK('N1', "F'", 'Z', "N'"): cx[HPK('N1', "F'", 'Z', "N'")]},
                            'B"', 'B1_', 'K', "F'", 'D', 'Z', 'X', 'N1', "N'", ref='tm2lpop')
            D1 = UP('D', 'K', 'X')
            CB1 = CLN('B1_', "N'", D1)
            assert triple_parts(pc)[:2] == (CBq, CB1), pc
            kd, gek = gamk(w, pha, 'K', L[GEQ], kk8)
            xg = wgk(w, pha, 'X', 'K', gek, L['X e. %s' % GAMW])
            d1cl = updcl(w, pha, 'D', 'K', 'X', tva, L[STKD('D')], kd, xg)
            ps, psc, jd, gej = pushat6(w, pha, L, tva, mta, L[GEQ], jj8, L['Y e. %s' % GAM], 'B1_', 'E', 'J', 'Y', "N'", D1,
                                       d1cl, L[SSS("N'")])
            D2x = YPUSH(D1, 'J', 'Y')
            assert triple_parts(psc)[:2] == (CB1, CLN('E', "N'", D2x)), psc
            # ( D1 ` J ) = ( D ` J ) : J =/= K
            nkj = L['K =/= J']
            njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % pha)
            xv = elv(w, pha, L['X e. %s' % GAMW], 'X')
            dj = updnv(w, pha, 'D', 'K', 'X', 'J', tva, L[STKD('D')], kd, xv, jd, njk)
            r1, new = w.rewrite(D2x, {'( %s ` J )' % D1: ('( D ` J )', dj)}, pha)
            assert new == D2_MVS, new
            de = w.s([cx["D' = %s" % D2_MVS]], 'eqcomd', "( %s -> %s = D' )" % (pha, D2_MVS))
            r2 = w.s([r1, de], 'eqtrd', "( %s -> %s = D' )" % (pha, D2x))
            psr, _, _, _ = hrrw(w, pha, ps, CB1, CLN('E', "N'", D2x), '1', deq=clneq(w, pha, 'E', "N'", r2, D2x, "D'"))
            q = hrseq(w, pha, L[PHM], b, pp, C1, CBq, CB1, '1', '1')
            q = hrseq(w, pha, L[PHM], q, psr, C1, CB1, CE, '( 1 + 1 )', '1')
            n = '( ( 1 + 1 ) + 1 )'
            hy = [L['2 <_ T1']]
        else:
            ps, psc, jd, gej = pushat6(w, pha, L, tva, mta, L[GEQ], jj8, L['Y e. %s' % GAM], 'B"', 'E', 'J', 'Y', 'N1', 'D',
                                       L[STKD('D')], L[SSS('N1')])
            D2x = YPUSH('D', 'J', 'Y')
            CEx = CLN('E', 'N1', D2x)
            assert triple_parts(psc)[:2] == (CBq, CEx), psc
            de = w.s([cx["D' = %s" % D2x]], 'eqcomd', "( %s -> %s = D' )" % (pha, D2x))
            psr, _, _, _ = hrrw(w, pha, ps, CBq, CEx, '1', deq=clneq(w, pha, 'E', 'N1', de, D2x, "D'"))
            # enlarge the class N1 to N'
            ss = clnss(w, pha, 'E', 'N1', "N'", "D'", cx["N1 C_ N'"])
            ecfg = cfgcl(w, pha, 'E', "N'", "D'", tva, L[LAB('E')], L[SSS("N'")], L[STKD("D'")])
            psr2 = hrssd(w, pha, L[PHM], psr, CBq, CLN('E', 'N1', "D'"), '1', CE, ss, ecfg)
            q = hrseq(w, pha, L[PHM], b, psr2, C1, CBq, CE, '1', '1')
            n = '( 1 + 1 )'
            hy = [L['1 <_ T1']]
        return bound0(w, pha, L[PHM], q, C1, CE, n, MB, {'T1': L['T1 e. NN0']}, hyps=hy)

    def caseB(phb, cs):
        L = LCtx(w, phb, c)
        tvb, mtb = L.L(tv, 'T e. V'), L.L(mt, MTY)
        cx = Ctx(w, phb, (HTF('N1', 'C'), TRIP_MVB), root=cs)
        b, bc = brat(w, phb, L, tvb, mtb, 'tm2fbrg', "B'", 'E0', GT('B"'), 'C', 'N1', 'D',
                     {HTF('N1', 'C'): cx[HTF('N1', 'C')], STMT(GT('B"')): L.L(gbq, STMT(GT('B"')))})
        CE0 = CLN('E0', 'N1', 'D')
        assert triple_parts(bc)[:2] == (C1, CE0), bc
        q = hrseq(w, phb, L[PHM], b, cx[TRIP_MVB], C1, CE0, CE, '1', 'T1')
        return bound0(w, phb, L[PHM], q, C1, CE, '( 1 + T1 )', MB, {'T1': L['T1 e. NN0']})

    s = casesplit(w, ph, c[DISJ], DISJ, CASEA, CASEB, caseA, caseB, TRI(C1, CE, MB))
    tot = hrseq(w, ph, phm, pk, s, C0, C1, CE, '1', MB)
    bound0(w, ph, phm, tot, C0, CE, '( 1 + %s )' % MB, '( T1 + 2 )', {'T1': t1n}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fmvs'): slot('mv')
    if want('tm2fcps'): slot('cp')
