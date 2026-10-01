"""T5b: one phase-1 iteration of the bit-length loop with its two continuations
abstract (~ tm2fblb ), and the final iteration with the loop exit (~ tm2fble );
blueprint D2."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def brstep(w, ph, ref, phm, meq, al, el, dd, cc, qcl, nss, test, A, E, C, Q, N, D):
    """tm2lbrt / tm2fbrg: the branch at A with test C to E (the other branch Q)"""
    return applylem(w, ph, ref, ((phm, meq), (al, el, dd), ((cc, qcl), (nss, test))),
                    TRI(CLN(A, N, D), CLN(E, N, D), '1'))


def ldstep(w, ph, phm, meq, al, el, dd, fty, nss, n2s, hld, A, E, N, N2, D):
    """tm2flg: load at A to E from N into N2"""
    return applylem(w, ph, 'tm2flg', ((phm, meq), (al, el, dd), (fty, (nss, n2s), hld)),
                    TRI(CLN(A, N, D), CLN(E, N2, D), '1'))


def tm2fblb():
    lab = 'tm2fblb'
    tree, ph = TREE_BLB, cj(TREE_BLB)
    D2 = D2_BLS1
    w = W(lab, 'One iteration of the bit-length loop ` blBody ` (TM/Prims.lean) on a bit, '
               'with the two continuations abstract: the loop test at ` A ` succeeds, '
               '` blScan ` at ` A\' ` pops the bit ` Z ` and pushes ` Z\' ` (~ tm2fbls1 ), the '
               '` da ` test at ` A" ` fails (~ tm2fbrg ), and the ` flag ` test at ` E\' ` '
               'dispatches to ` E" ` (~ tm2lbrt ) or ` E0 ` (~ tm2fbrg ), whence a triple '
               'given as a hypothesis under the disjunction returns to ` A ` in the class '
               '` N\' ` .  Lean: ` blBody_runs ` , the ` cons ` case, with ` incr_correct ` '
               'and ` skip_runs ` left abstract (they are discharged by ~ tm2fblk ).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, a1, a2, e1, e2, e0 = [c[LAB(x)] for x in ('A', "A'", 'A"', "E'", 'E"', 'E0')]
    kk, jj, ne = c['K e. %s' % DG], c['J e. %s' % DG], c['K =/= J']
    c0, cc, c1, c2 = [c[CTY(x)] for x in ('C0', 'C', "C'", 'C"')]
    ff, pp, ll = c[RTY('F', 'K')], c[PTY('P', 'J')], c[LTY('L')]
    qq, q1, q2 = [c[STMT(x)] for x in ('Q', "Q'", 'Q"')]
    dd, dke = c[STKD('D')], c['( D ` K ) = %s' % ZX]
    zz, zp, xx = c['Z e. %s' % GK], c["Z' e. %s" % GJ], c[WRD('X', GK)]
    nss, oss, n2s = c[SSS('N')], c[SSS('O')], c[SSS("N'")]
    ht, hs, hda = c[HT('N')], c[HSCAN('N', 'Z', "Z'", 'O')], c[HDA('O')]
    disj, rr = c[DISJ_BLB], c['R e. NN0']
    meqA, meqA1, meqA2, meqE1 = c[MEQ('A', STM_T)], c[MEQ("A'", STM_S)], c[MEQ('A"', STM_DA)], c[MEQ("E'", STM_FL)]
    # D2 e. Stk
    d1cl = updcl(w, ph, 'D', 'K', 'X', tv, dd, kk, xx)
    djw = stkfv(w, ph, 'D', 'J', tv, dd, jj)
    zpdjw = ccatw(w, ph, s1w(w, ph, zp, "Z'", GJ), djw, S1("Z'"), '( D ` J )', GJ)
    d2cl = updcl(w, ph, UP('D', 'K', 'X'), 'J', CC(S1("Z'"), '( D ` J )'), tv, d1cl, jj, zpdjw)
    # goto typings
    ge1, ge2, ge0 = gotocl(w, ph, tv, "E'", e1), gotocl(w, ph, tv, 'E"', e2), gotocl(w, ph, tv, 'E0', e0)
    # t1: the test at A
    C0 = CLN('A', 'N', 'D'); C1 = CLN("A'", 'N', 'D'); C2 = CLN('A"', 'O', D2); C3 = CLN("E'", 'O', D2)
    t1 = brstep(w, ph, 'tm2lbrt', phm, meqA, al, a1, dd, c0, qq, nss, ht, 'A', "A'", 'C0', 'Q', 'N', 'D')
    # t2: the scan at A'
    t2 = applylem(w, ph, 'tm2fbls1',
                  (((phm, meqA1), ((a1, a2), (kk, jj), ne), ((ff, cc), (pp, ll), q1)),
                   ((dd, dke, ((zz, zp), xx)), ((nss, oss), hs))),
                  TRI(C1, C2, '1'))
    # t3: the da test at A" fails
    t3 = brstep(w, ph, 'tm2fbrg', phm, meqA2, a2, e1, d2cl, c1, q2, oss, hda, 'A"', "E'", "C'", 'Q"', 'O', D2)
    t12 = hrseq(w, ph, phm, t1, t2, C0, C1, C2, '1', '1')
    t123 = hrseq(w, ph, phm, t12, t3, C0, C2, C3, '( 1 + 1 )', '1')
    N3 = '( ( 1 + 1 ) + 1 )'
    POST = CLN('A', "N'", "D'")
    TOT = '( ( %s + 1 ) + R )' % N3
    cases = []
    for cont, ref, tst, Qb, Eb in (('E"', 'tm2lbrt', HFT('O'), GT('E0'), 'E"'), ('E0', 'tm2fbrg', HFF('O'), GT('E"'), 'E0')):
        trip = TRI(CLN(cont, 'O', D2), POST, 'R')
        pha = '( %s /\\ ( %s /\\ %s ) )' % (ph, tst, trip)
        A_ = Lifter(w, pha)
        cs = w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (pha, tst, trip))
        tsa = w.s([cs], 'simpld', '( %s -> %s )' % (pha, tst))
        tra = w.s([cs], 'simprd', '( %s -> %s )' % (pha, trip))
        qcl = A_({'E"': ge0, 'E0': ge2}[cont], STMT(Qb))
        t4 = brstep(w, pha, ref, A_(phm, PHM), A_(meqE1, MEQ("E'", STM_FL)), A_(e1, LAB("E'")), A_({'E"': e2, 'E0': e0}[cont], LAB(Eb)),
                    A_(d2cl, STKD(D2)), A_(c2, CTY('C"')), qcl, A_(oss, SSS('O')), tsa, "E'", Eb, 'C"', Qb, 'O', D2)
        t45 = hrseq(w, pha, A_(phm, PHM), t4, tra, C3, CLN(cont, 'O', D2), POST, '1', 'R')
        tall = hrseq(w, pha, A_(phm, PHM), A_(t123, TRI(C0, C3, N3)), t45, C0, C3, POST, N3, '( 1 + R )')
        # ( N3 + ( 1 + R ) ) = TOT
        one = w.s([], '1cnd', '( %s -> 1 e. CC )' % pha)
        n3c = w.s([w.s([one, one], 'addcld', '( %s -> ( 1 + 1 ) e. CC )' % pha), one], 'addcld', '( %s -> %s e. CC )' % (pha, N3))
        rc = w.s([A_(rr, 'R e. NN0')], 'nn0cnd', '( %s -> R e. CC )' % pha)
        asso = w.s([n3c, one, rc, w.inst('addassd')], 'syl3anc', '( %s -> ( ( %s + 1 ) + R ) = ( %s + ( 1 + R ) ) )' % (pha, N3, N3))
        assoc = w.s([asso], 'eqcomd', '( %s -> ( %s + ( 1 + R ) ) = %s )' % (pha, N3, TOT))
        tr, _, _, _ = hrrw(w, pha, tall, C0, POST, '( %s + ( 1 + R ) )' % N3, neq=assoc)
        cases.append(tr)
    both = w.s(cases, 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ_BLB, TRI(C0, POST, TOT)))
    tri = w.s([disj, both], 'mpdan', '( %s -> %s )' % (ph, TRI(C0, POST, TOT)))
    bound(w, ph, phm, tri, C0, POST, TOT, '( R + 4 )', {'R': rr}, qed=True)
    return w.run()


def tm2fble():
    lab = 'tm2fble'
    tree, ph = TREE_BLE, cj(TREE_BLE)
    D1 = UP('D', 'K', 'X')
    w = W(lab, 'The final iteration of the bit-length loop and its exit: the loop test at '
               '` A ` succeeds, ` blScan ` at ` A\' ` pops the terminator ` Y ` (~ tm2fbls0 , '
               'T7: ` carry := true ` ), the ` da ` test at ` A" ` is taken (~ tm2lbrt ), '
               '` skip ` at ` E0 ` returns to ` A ` (~ tm2flg ), and the test now fails '
               '(~ tm2fbrg ), so the machine leaves for ` E ` in ` 5 ` steps with the '
               'terminator consumed.  Lean: ` blBody_runs ` , the ` nil ` case, and the '
               '` hn ` clause of ` Frag.loop_runs ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, a1, a2, e0, el = [c[LAB(x)] for x in ('A', "A'", 'A"', 'E0', 'E')]
    kk = c['K e. %s' % DG]
    c0, cc, c1 = [c[CTY(x)] for x in ('C0', 'C', "C'")]
    ff, ll, l1 = c[RTY('F', 'K')], c[LTY('L')], c[LTY("L'")]
    q1, q2 = c[STMT("Q'")], c[STMT('Q"')]
    dd, dke = c[STKD('D')], c['( D ` K ) = %s' % YX]
    yy, xx = c['Y e. %s' % GK], c[WRD('X', GK)]
    nss, oss, n2s = c[SSS('N')], c[SSS('O')], c[SSS("N'")]
    ht, he, hdat, hsk, htf = c[HT('N')], c[HEND('N', 'Y', 'O')], c[HDAT('O')], c[HLOAD('O', "N'")], c[HTF("N'")]
    meqA, meqA1, meqA2, meqE0 = c[MEQ('A', STM_TE)], c[MEQ("A'", STM_SE)], c[MEQ('A"', STM_DAE)], c[MEQ('E0', STM_SK)]
    d1cl = updcl(w, ph, 'D', 'K', 'X', tv, dd, kk, xx)
    ge, ga1 = gotocl(w, ph, tv, 'E', el), gotocl(w, ph, tv, "A'", a1)
    C0 = CLN('A', 'N', 'D'); C1 = CLN("A'", 'N', 'D'); C2 = CLN('A"', 'O', D1)
    C3 = CLN('E0', 'O', D1); C4 = CLN('A', "N'", D1); C5 = CLN('E', "N'", D1)
    t1 = brstep(w, ph, 'tm2lbrt', phm, meqA, al, a1, dd, c0, ge, nss, ht, 'A', "A'", 'C0', GT('E'), 'N', 'D')
    t2 = applylem(w, ph, 'tm2fbls0',
                  (((phm, meqA1), (a1, a2, kk), ((ff, cc), (ll, q1))),
                   ((dd, dke, (yy, xx)), ((nss, oss), he))),
                  TRI(C1, C2, '1'))
    t3 = brstep(w, ph, 'tm2lbrt', phm, meqA2, a2, e0, d1cl, c1, q2, oss, hdat, 'A"', 'E0', "C'", 'Q"', 'O', D1)
    t4 = ldstep(w, ph, phm, meqE0, e0, al, d1cl, l1, oss, n2s, hsk, 'E0', 'A', 'O', "N'", D1)
    t5 = brstep(w, ph, 'tm2fbrg', phm, meqA, al, el, d1cl, c0, ga1, n2s, htf, 'A', 'E', 'C0', GT("A'"), "N'", D1)
    t12 = hrseq(w, ph, phm, t1, t2, C0, C1, C2, '1', '1')
    t123 = hrseq(w, ph, phm, t12, t3, C0, C2, C3, '( 1 + 1 )', '1')
    t1234 = hrseq(w, ph, phm, t123, t4, C0, C3, C4, '( ( 1 + 1 ) + 1 )', '1')
    tall = hrseq(w, ph, phm, t1234, t5, C0, C4, C5, '( ( ( 1 + 1 ) + 1 ) + 1 )', '1')
    bound(w, ph, phm, tall, C0, C5, '( ( ( ( 1 + 1 ) + 1 ) + 1 ) + 1 )', '5', {}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fblb'): tm2fblb()
    if want('tm2fble'): tm2fble()
