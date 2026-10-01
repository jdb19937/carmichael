"""T-MD: one iteration of ` mul ` (TM/MulDiv.lean, blueprint D4): the loop test
(~ tm2lbrt ), ` Frag.ite ` on ` ra = some true ` dispatching to the conditional
add --- a hypothesis triple --- or to ` Frag.skip ` (~ tm2fbrg , ~ tm2flg ), the
push of a zero on the multiplicand (~ tm2fpshn ) and ` popBit ` of the next
multiplier symbol (~ tm2fpopn ).  Lean: ` mulBody_runs ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def brstep(w, ph, ref, phm, meq, al, el, dd, cc, qcl, nss, test, A, E, N, D):
    return applylem(w, ph, ref, ((phm, meq), (al, el, dd), ((cc, qcl), (nss, test))), TRI(CLN(A, N, D), CLN(E, N, D), '1'))


def loadcls(w, ph, Lf, lty, nss, Nc='N'):
    """( ph -> A. r e. Nc ( Lf ` r ) e. S ) from lty : Lf e. ( S ^m S ), nss : Nc C_ S"""
    ff = w.s([lty, w.inst('elmapi')], 'syl', '( %s -> %s : %s --> %s )' % (ph, Lf, SS, SS))
    ar = '( %s /\\ u e. %s )' % (ph, Nc)
    ffa = w.s([ff], 'adantr', '( %s -> %s : %s --> %s )' % (ar, Lf, SS, SS))
    un = w.s([], 'simpr', '( %s -> u e. %s )' % (ar, Nc))
    nsa = w.s([nss], 'adantr', '( %s -> %s C_ %s )' % (ar, Nc, SS))
    us = w.s([nsa, un], 'sseldd', '( %s -> u e. %s )' % (ar, SS))
    fv = w.s([ffa, us], 'ffvelcdmd', '( %s -> ( %s ` u ) e. %s )' % (ar, Lf, SS))
    ru = w.s([fv], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) e. %s )' % (ph, Nc, Lf, SS))
    cg, _ = W.wcongr(w, '( %s ` u ) e. %s' % (Lf, SS), {'u': 'r'}, 'u = r', {'u': w.s([], 'id', '( u = r -> u = r )')})
    cb = w.s([cg], 'cbvralvw', '( A. u e. %s ( %s ` u ) e. %s <-> A. r e. %s ( %s ` r ) e. %s )' % (Nc, Lf, SS, Nc, Lf, SS))
    return w.s([ru, cb], 'sylib', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (ph, Nc, Lf, SS))


def tm2fmlb():
    lab = 'tm2fmlb'
    tree, ph = TREE_MLB, cj(TREE_MLB)
    DI = UP('D', 'I', "H'")
    Z0DK = CC(S1('Z0'), '( D ` K )')
    DIK = UP(DI, 'K', Z0DK)
    UYP = CC(S1('U'), "Y'")
    w = W(lab, 'One iteration of the multiplication loop ` mulBody ` (TM/MulDiv.lean): the loop '
               'test at ` A ` succeeds (~ tm2lbrt ), ` Frag.ite ` at ` B0 ` tests the multiplier bit '
               'in ` ra ` --- set: ` dup x t s ; add w t s w ` , given as a hypothesis triple from '
               '` B\' ` to ` B" ` leaving ` H\' ` on the accumulator ` I ` (T7: ~ tm2fdup , ~ tm2faddx ); '
               'clear: ` skip ` at ` E0 ` (~ tm2fbrg , ~ tm2flg ) and ` H\' ` is the old accumulator --- '
               'then a zero is pushed on the multiplicand ` K ` (~ tm2fpshn ) and ` popBit ` at ` A0 ` '
               'reads the next multiplier symbol ` U ` from ` J ` into the class ` N\' ` (~ tm2fpopn ).  '
               'Lean: ` mulBody_runs ` ; the two cases are the disjunction (blueprint D4, D5).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    al, b0l, bpl, bql, e0l, a0l = [c[LAB(x)] for x in ('A', 'B0', "B'", 'B"', 'E0', 'A0')]
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    c0t, ct, lpt, ff, qq = c[CTY('C0')], c[CTY('C')], c[LTY("L'")], c[RTY('F', 'J')], c[STMT('Q')]
    z0k, uj = c['Z0 e. %s' % GK], c['U e. %s' % GJ]
    dd, dje = c[STKD('D')], c['( D ` J ) = %s' % UYP]
    ypw, hpw = c[WRD("Y'", GJ)], c[WRD("H'", GI)]
    tt, t1 = c["T' e. NN0"], c["1 <_ T'"]
    nss, n2s, ht, hpb, disj = c[SSS('N')], c[SSS("N'")], c[HT('N')], c[HPB(SS, 'U', "N'")], c[DISJ_ML]
    meqA, meqB0, meqE0, meqBq, meqA0 = [c[MEQ(a, s)] for a, s in (('A', STM_MT), ('B0', STM_MI), ('E0', STM_MSK), ('B"', STM_MPZ), ('A0', STM_MPB))]
    sss = w.s([], 'ssid', '%s C_ %s' % (SS, SS)); sssa = w.s([sss], 'a1i', '( %s -> %s C_ %s )' % (ph, SS, SS))
    gbp, ge0 = gotocl(w, ph, tv, "B'", bpl), gotocl(w, ph, tv, 'E0', e0l)
    dicl = updcl(w, ph, 'D', 'I', "H'", tv, dd, ii, hpw)
    # ---- stage 1: the loop test at A
    C0 = CLN('A', 'N', 'D'); C1 = CLN('B0', 'N', 'D'); C2 = CLN('B"', SS, DI)
    t1s = brstep(w, ph, 'tm2lbrt', phm, meqA, al, b0l, dd, c0t, qq, nss, ht, 'A', 'B0', 'N', 'D')
    # ---- stage 2: the ite, two cases
    hld = loadcls(w, ph, "L'", lpt, nss)
    cases = []
    # add case
    TRIP = TRI(CLN("B'", 'N', 'D'), C2, "T'")
    pha = '( %s /\\ ( %s /\\ %s ) )' % (ph, HTC('N'), TRIP)
    A_ = Lifter(w, pha)
    cs = w.s([], 'simpr', '( %s -> ( %s /\\ %s ) )' % (pha, HTC('N'), TRIP))
    tsa = w.s([cs], 'simpld', '( %s -> %s )' % (pha, HTC('N')))
    tra = w.s([cs], 'simprd', '( %s -> %s )' % (pha, TRIP))
    ta = brstep(w, pha, 'tm2lbrt', A_(phm, PHM), A_(meqB0, MEQ('B0', STM_MI)), A_(b0l, LAB('B0')), A_(bpl, LAB("B'")), A_(dd, STKD('D')),
                A_(ct, CTY('C')), A_(ge0, STMT(GT('E0'))), A_(nss, SSS('N')), tsa, 'B0', "B'", 'N', 'D')
    tab = hrseq(w, pha, A_(phm, PHM), ta, tra, C1, CLN("B'", 'N', 'D'), C2, '1', "T'")
    cases.append(tab)
    # skip case
    phb = '( %s /\\ ( %s /\\ H\' = ( D ` I ) ) )' % (ph, HTCF('N'))
    B_ = Lifter(w, phb)
    cs2 = w.s([], 'simpr', '( %s -> ( %s /\\ H\' = ( D ` I ) ) )' % (phb, HTCF('N')))
    tsb = w.s([cs2], 'simpld', '( %s -> %s )' % (phb, HTCF('N')))
    hie = w.s([cs2], 'simprd', "( %s -> H' = ( D ` I ) )" % phb)
    tb = brstep(w, phb, 'tm2fbrg', B_(phm, PHM), B_(meqB0, MEQ('B0', STM_MI)), B_(b0l, LAB('B0')), B_(e0l, LAB('E0')), B_(dd, STKD('D')),
                B_(ct, CTY('C')), B_(gbp, STMT(GT("B'"))), B_(nss, SSS('N')), tsb, 'B0', 'E0', 'N', 'D')
    tl = applylem(w, phb, 'tm2flg', ((B_(phm, PHM), B_(meqE0, MEQ('E0', STM_MSK))), (B_(e0l, LAB('E0')), B_(bql, LAB('B"')), B_(dd, STKD('D'))),
                                     (B_(lpt, LTY("L'")), (B_(nss, SSS('N')), B_(sssa, '%s C_ %s' % (SS, SS))), B_(hld, 'A. r e. N ( L\' ` r ) e. %s' % SS))),
                  TRI(CLN('E0', 'N', 'D'), CLN('B"', SS, 'D'), '1'))
    # D = UP( D , I , H' )
    hiec = w.s([hie], 'eqcomd', "( %s -> ( D ` I ) = H' )" % phb)
    ui = upidv(w, phb, 'D', 'I', "H'", hiec, B_(tv, 'T e. V'), B_(dd, STKD('D')), B_(ii, 'I e. %s' % DG))
    tl2, _, _, _ = hrrw(w, phb, tl, CLN('E0', 'N', 'D'), CLN('B"', SS, 'D'), '1',
                        deq=clneq(w, phb, 'B"', SS, w.s([ui], 'eqcomd', '( %s -> D = %s )' % (phb, DI)), 'D', DI))
    tbl = hrseq(w, phb, B_(phm, PHM), tb, tl2, C1, CLN('E0', 'N', 'D'), C2, '1', '1')
    tblr = bound(w, phb, B_(phm, PHM), tbl, C1, C2, '( 1 + 1 )', "( 1 + T' )", {"T'": B_(tt, "T' e. NN0")}, hyps=[B_(t1, "1 <_ T'")])
    cases.append(tblr)
    both = w.s(cases, 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ_ML, TRI(C1, C2, "( 1 + T' )")))
    t2s = w.s([disj, both], 'mpdan', '( %s -> %s )' % (ph, TRI(C1, C2, "( 1 + T' )")))
    t12 = hrseq(w, ph, phm, t1s, t2s, C0, C1, C2, '1', "( 1 + T' )")
    N12 = "( 1 + ( 1 + T' ) )"
    # ---- stage 3: push Z0 on K at S
    bld3 = bldr(w, ph, c, phm, {STKD(DI): dicl, '%s C_ %s' % (SS, SS): sssa})
    s3, c3 = inst(w, ph, 'tm2fpshn', {'A': 'B"', 'E': 'A0', 'Z': 'Z0', 'N': SS, 'D': DI}, bld3)
    C3a, D3c, B3 = triple_parts(c3)
    D3 = UP(DI, 'K', CC(S1('Z0'), '( %s ` K )' % DI))
    assert C3a == C2 and D3c == CLN('A0', SS, D3), (C3a, D3c)
    dik = updnv(w, ph, 'D', 'I', "H'", 'K', tv, dd, ii, elv(w, ph, hpw, "H'"), kk, nki)
    r3, D3p = w.rewrite(D3, {'( %s ` K )' % DI: ('( D ` K )', dik)}, ph)
    assert D3p == DIK, D3p
    s3r, _, _, _ = hrrw(w, ph, s3, C3a, D3c, B3, deq=clneq(w, ph, 'A0', SS, r3, D3, DIK))
    t123 = hrseq(w, ph, phm, t12, s3r, C0, C2, CLN('A0', SS, DIK), N12, '1')
    N123 = '( %s + 1 )' % N12
    # ---- stage 4: pop J at A0 from S into N'
    dkw = stkfv(w, ph, 'D', 'K', tv, dd, kk)
    z0dkw = ccatw(w, ph, s1w(w, ph, z0k, 'Z0', GK), dkw, S1('Z0'), '( D ` K )', GK)
    dikcl = updcl(w, ph, DI, 'K', Z0DK, tv, dicl, kk, z0dkw)
    j1 = updnv(w, ph, DI, 'K', Z0DK, 'J', tv, dicl, kk, elv(w, ph, z0dkw, Z0DK), jj, njk)
    j2 = updnv(w, ph, 'D', 'I', "H'", 'J', tv, dd, ii, elv(w, ph, hpw, "H'"), jj, nji)
    dikj = w.s([w.s([j1, j2], 'eqtrd', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph, DIK)), dje], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, DIK, UYP))
    bld4 = bldr(w, ph, c, phm, {STKD(DIK): dikcl, '( %s ` J ) = %s' % (DIK, UYP): dikj, '%s C_ %s' % (SS, SS): sssa})
    s4, c4 = inst(w, ph, 'tm2fpopn', {'A': 'A0', 'E': 'A', 'K': 'J', 'Z': 'U', 'X': "Y'", 'N': SS, 'D': DIK}, bld4)
    C4a, D4c, B4 = triple_parts(c4)
    assert C4a == CLN('A0', SS, DIK) and D4c == CLN('A', "N'", POST_MLB), (C4a, D4c)
    tall = hrseq(w, ph, phm, t123, s4, C0, CLN('A0', SS, DIK), D4c, N123, '1')
    bound(w, ph, phm, tall, C0, D4c, '( %s + 1 )' % N123, "( T' + 4 )", {"T'": tt}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fmlb'): tm2fmlb()
