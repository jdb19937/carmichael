"""T6b: `revList` restated with a fresh push label (` P0 `): T6's ~ tm2lrev
binds ` ( M ` A ) ` twice (the loop test and the push) and is vacuous
(T6b-blueprint section 0).  The proof is t6_g_rev.py's at ` P0 ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6blib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2lrev2():
    lab = 'tm2lrev2'
    ph = PHR2
    w = W(lab, 'The fragment ` revList ` of TM/Lists.lean: the list on stack ` K ` is '
               'consumed and its reversal is pushed as a list on stack ` J ` ; the scratch '
               'stack ` I ` is restored.  Lean: ` revList_runs ` .  Replaces ~ tm2lrev , '
               'whose antecedent binds ` ( M ` A ) ` to both the loop test and the entry '
               'push and is therefore unsatisfiable; here the push has its own label ` P0 ` .')
    phs = w.s([], 'simpl', '( %s -> %s )' % (ph, PHS))
    ah = w.s([], 'simpr', '( %s -> %s )' % (ph, AH2))
    al = w.s([ah], 'simpld', '( %s -> P0 e. %s )' % (ph, LT))
    ma = w.s([ah], 'simprd', '( %s -> ( M ` P0 ) = %s )' % (ph, PSH('J', '2', 'P1')))
    u = prelude(w, PHS)
    u = lift_all(w, PHS, u, ph)
    tv, dd = u['tv'], u['dd']
    # stage 1: push 2 on J
    g2 = gamlet(w, ph, '2')
    g2j = lgk(w, ph, '2', 'J', u['gj'], g2)
    a1 = w.s([u['phm'], ma], 'jca', '( %s -> ( %s /\\ ( M ` P0 ) = %s ) )' % (ph, PHM, PSH('J', '2', 'P1')))
    jz = w.s([u['jd'], g2j], 'jca', '( %s -> ( J e. %s /\\ 2 e. %s ) )' % (ph, DG, GT('J')))
    a2 = w.s([al, u['ls']['P1'], jz], '3jca', '( %s -> ( P0 e. %s /\\ P1 e. %s /\\ ( J e. %s /\\ 2 e. %s ) ) )' % (ph, LT, LT, DG, GT('J')))
    a3 = w.s([dd, u['nss']], 'jca', '( %s -> ( D e. %s /\\ N C_ %s )' % (ph, STK_T, SS) + ' )')
    ant = w.s([a1, a2, a3], '3jca', '( %s -> ( ( %s /\\ ( M ` P0 ) = %s ) /\\ ( P0 e. %s /\\ P1 e. %s /\\ ( J e. %s /\\ 2 e. %s ) ) /\\ ( D e. %s /\\ N C_ %s ) ) )'
              % (ph, PHM, PSH('J', '2', 'P1'), LT, LT, DG, GT('J'), STK_T, SS))
    Z2 = '( <" 2 "> ++ ( D ` J ) )'
    D1 = UPDT('D', 'J', Z2)
    s1 = w.s([ant, w.inst('tm2fpshn')], 'syl', '( %s -> %s )' % (ph, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('P1', 'N', D1), '1')))
    # stage 2: moveEntries from D1
    c2 = s1g(w, ph, '2')
    djw = stkfvg(w, ph, 'D', 'J', tv, dd, u['jd'], u['gj'])
    z2cl = ccatg(w, ph, '<" 2 ">', '( D ` J )', c2, djw)
    d1cl = updcl(w, ph, 'D', 'J', Z2, tv, dd, u['jd'], u['gj'], z2cl)
    z2v = w.s([z2cl], 'elexd', '( %s -> %s e. _V )' % (ph, Z2))
    d1k = updn(w, ph, 'D', 'J', Z2, 'K', tv, dd, u['jd'], z2v, u['kd'], u['nkj'])
    d1k2 = w.s([d1k, u['dk']], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1, LST('L', 'R')))
    DATA1 = DATA.replace('( D e. %s /\\ ( D ` K ) = %s )' % (STK_T, LST('L', 'R')), '( %s e. %s /\\ ( %s ` K ) = %s )' % (D1, STK_T, D1, LST('L', 'R')))
    dk1 = w.s([d1cl, d1k2], 'jca', '( %s -> ( %s e. %s /\\ ( %s ` K ) = %s ) )' % (ph, D1, STK_T, D1, LST('L', 'R')))
    lr = w.s([u['ll'], u['rr']], 'jca', '( %s -> ( L e. %s /\\ R e. %s ) )' % (ph, WWB, WG))
    bw = w.s([u['bb'], u['bw']], 'jca', '( %s -> ( B e. NN0 /\\ A. w e. ran L ( # ` w ) <_ B ) )' % ph)
    data1 = w.s([dk1, lr, bw], '3jca', '( %s -> %s )' % (ph, DATA1))
    p1 = w.s([phs, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, PHM6, PROG))
    p2 = w.s([phs, w.inst('simp2')], 'syl', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) )' % (ph, LAB, IDX, HNDS, NSS2, IFS))
    PHS1 = PHS.replace(DATA, DATA1)
    ant2 = w.s([p1, p2, data1], '3jca', '( %s -> %s )' % (ph, PHS1))
    DF1 = UPDT(UPDT(D1, 'K', 'R'), 'J', '( %s ++ ( %s ` J ) )' % (ENT(REVL), D1))
    BND = '( ( %s x. ( ( 2 x. B ) + 6 ) ) + 3 )' % NL
    s2 = w.s([ant2, w.inst('tm2lmes')], 'syl', '( %s -> %s )' % (ph, HR(CL('P1', 'N', D1), 'T', 'M', CL('E', "N'", DF1), BND)))
    # DF1 = RFIN
    ERL = '( %s ++ ( D ` J ) )' % ENCB(REVL)
    jv = updk(w, ph, 'D', 'J', Z2, tv, dd, u['jd'], z2v)
    jv2 = w.s([jv], 'oveq2d', '( %s -> ( %s ++ ( %s ` J ) ) = ( %s ++ %s ) )' % (ph, ENT(REVL), D1, ENT(REVL), Z2))
    rvl = w.s([u['ll'], w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REVL, WWB))
    cc = w.s([rvl, djw, w.inst('tm2lencbcc')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, ERL, ENT(REVL), Z2))
    jv3 = w.s([jv2, cc], 'eqtr4d', '( %s -> ( %s ++ ( %s ` J ) ) = %s )' % (ph, ENT(REVL), D1, ERL))
    st1, r1 = w.rewrite(DF1, {'( %s ++ ( %s ` J ) )' % (ENT(REVL), D1): (ERL, jv3)}, ph)
    DF2 = UPDT(UPDT(D1, 'K', 'R'), 'J', ERL)
    assert r1 == DF2, r1
    ebc = w.s([rvl, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(REVL), WG))
    erl = ccatg(w, ph, ENCB(REVL), '( D ` J )', ebc, djw)
    z2j = wgk(w, ph, Z2, 'J', u['gj'], z2cl)
    erj = wgk(w, ph, ERL, 'J', u['gj'], erl)
    rk = wgk(w, ph, 'R', 'K', u['gk'], u['rr'])
    njk = w.s([u['nkj']], 'necomd', '( %s -> J =/= K )' % ph)
    tvdd = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK_T))
    u3a = w.s([tvdd, njk], 'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ J =/= K ) )' % (ph, STK_T))
    u3b = w.s([u['jd'], w.s([z2j, erj], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Z2, GT('J'), ERL, GT('J')))], 'jca',
               '( %s -> ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, DG, Z2, GT('J'), ERL, GT('J')))
    u3c = w.s([u['kd'], rk], 'jca', '( %s -> ( K e. %s /\\ R e. Word %s ) )' % (ph, DG, GT('K')))
    up3 = w.s([u3a, u3b, u3c, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )' % (ph, DF2, UPDT(UPDT('D', 'J', ERL), 'K', 'R')))
    ucb = w.s([u['jd'], erj], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, ERL, GT('J')))
    ucc = w.s([u['kd'], rk], 'jca', '( %s -> ( K e. %s /\\ R e. Word %s ) )' % (ph, DG, GT('K')))
    upc = w.s([u3a, ucb, ucc, w.inst('tm2stkupc')], 'syl3anc', '( %s -> %s = %s )' % (ph, UPDT(UPDT('D', 'J', ERL), 'K', 'R'), RFIN))
    e1 = w.s([st1, up3], 'eqtrd', '( %s -> %s = %s )' % (ph, DF1, UPDT(UPDT('D', 'J', ERL), 'K', 'R')))
    e2 = w.s([e1, upc], 'eqtrd', '( %s -> %s = %s )' % (ph, DF1, RFIN))
    s2b = hrtransport(w, ph, s2, CL('P1', 'N', D1), CL('E', "N'", DF1), BND, None, CL('E', "N'", RFIN), eqd=cleq(w, ph, 'E', "N'", DF1, RFIN, e2))
    C0 = CL('P0', 'N', 'D'); C1 = CL('P1', 'N', D1); C2 = CL('E', "N'", RFIN)
    q = hseq(w, ph, u['phm'], C0, C1, C2, '1', BND, s1, s2b)
    TOT = '( 1 + %s )' % BND
    nlr = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    br = w.s([u['bb']], 'nn0red', '( %s -> B e. RR )' % ph)
    twoa = relit(w, ph, '2'); sixa = relit(w, ph, '6')
    tb = w.s([twoa, br], 'remulcld', '( %s -> ( 2 x. B ) e. RR )' % ph)
    b6 = w.s([tb, sixa], 'readdcld', '( %s -> ( ( 2 x. B ) + 6 ) e. RR )' % ph)
    PR = '( %s x. ( ( 2 x. B ) + 6 ) )' % NL
    prr = w.s([nlr, b6], 'remulcld', '( %s -> %s e. RR )' % (ph, PR))
    eq = lineq(w, ph, TOT, BREV, leaves={PR: prr}, atoms=[PR])
    o = w.s([eq], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C2, TOT, C2, BREV))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C2, TOT), HR(C0, 'T', 'M', C2, BREV)))
    w.qed([b, q], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BREV)))
    return w.run()


if __name__ == '__main__':
    if want('tm2lrev2'): tm2lrev2()
