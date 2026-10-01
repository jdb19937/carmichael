"""T6b: ` appendList ` (blueprint 2.1): ~ tm2lrev2 from ` K ` onto ` I' ` ,
then ~ tm2lmes from ` I' ` onto ` J ` ; and the range lemma ~ tm2lrnrev ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6blib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2lrnrev():
    lab = 'tm2lrnrev'
    ph = 'L e. Word A'
    NLx = '( # ` L )'
    IDXV = '( ( %s - 1 ) - x )' % NLx
    MPT = '( x e. ( 0 ..^ %s ) |-> ( L ` %s ) )' % (NLx, IDXV)
    w = W(lab, 'The range of the reversal of a word is within the range of the word '
               '(Lean: ` List.mem_reverse ` , used for the entry-size bound of a reversed list).')
    lv = w.s([], 'elex', '( %s -> L e. _V )' % ph)
    rv = w.s([lv, w.inst('revval')], 'syl', '( %s -> ( reverse ` L ) = %s )' % (ph, MPT))
    px = '( %s /\\ x e. ( 0 ..^ %s ) )' % (ph, NLx)
    la = w.s([], 'simpl', '( %s -> L e. Word A )' % px)
    xx = w.s([], 'simpr', '( %s -> x e. ( 0 ..^ %s ) )' % (px, NLx))
    fn = w.s([la, w.inst('wrdfn')], 'syl', '( %s -> L Fn ( 0 ..^ %s ) )' % (px, NLx))
    m1 = w.s([xx, w.inst('ubmelm1fzo')], 'syl', '( %s -> ( ( %s - x ) - 1 ) e. ( 0 ..^ %s ) )' % (px, NLx, NLx))
    nl = w.s([la, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (px, NLx))
    nlc = w.s([nl], 'nn0cnd', '( %s -> %s e. CC )' % (px, NLx))
    one = w.s([], 'ax-1cn', '1 e. CC'); onea = w.s([one], 'a1i', '( %s -> 1 e. CC )' % px)
    xn = w.s([xx, w.inst('elfzonn0')], 'syl', '( %s -> x e. NN0 )' % px)
    xc = w.s([xn], 'nn0cnd', '( %s -> x e. CC )' % px)
    s32 = w.s([nlc, onea, xc, w.inst('sub32')], 'syl3anc', '( %s -> %s = ( ( %s - x ) - 1 ) )' % (px, IDXV, NLx))
    m2 = w.s([s32, m1], 'eqeltrd', '( %s -> %s e. ( 0 ..^ %s ) )' % (px, IDXV, NLx))
    fv = w.s([fn, m2, w.inst('fnfvelrn')], 'syl2anc', '( %s -> ( L ` %s ) e. ran L )' % (px, IDXV))
    ral = w.s([fv], 'ralrimiva', '( %s -> A. x e. ( 0 ..^ %s ) ( L ` %s ) e. ran L )' % (ph, NLx, IDXV))
    eqi = w.s([], 'eqid', '%s = %s' % (MPT, MPT))
    rn = w.s([eqi], 'rnmptss', '( A. x e. ( 0 ..^ %s ) ( L ` %s ) e. ran L -> ran %s C_ ran L )' % (NLx, IDXV, MPT))
    ss = w.s([ral, rn], 'syl', '( %s -> ran %s C_ ran L )' % (ph, MPT))
    rne = w.s([rv], 'rneqd', '( %s -> ran ( reverse ` L ) = ran %s )' % (ph, MPT))
    w.qed([rne, ss], 'eqsstrd', '( %s -> ran ( reverse ` L ) C_ ran L )' % ph)
    return w.run()


def tm2lapp():
    lab = 'tm2lapp'
    ph = PHA
    w = W(lab, 'The fragment ` appendList ` of TM/Lists.lean: the list on stack ` K ` is '
               'consumed and prepended to the list on stack ` J ` ; the scratch stacks '
               '` I\' ` (the reversal) and ` I ` are restored.  Lean: ` appendList_runs ` ; '
               '~ tm2lrev2 from ` K ` onto ` I\' ` , then ~ tm2lmes from ` I\' ` onto ` J ` .')
    c = Ctx(w, ph, T_PHA)
    phm = c[PHM]; geq = c[GEQ]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    dd = c['D e. %s' % STK_T]
    kk, jj, ii, i2 = c['K e. %s' % FZ8], c['J e. %s' % FZ8], c['I e. %s' % FZ8], c["I' e. %s" % FZ8]
    kd, gk = gamk(w, ph, 'K', geq, kk)
    jd, gj = gamk(w, ph, 'J', geq, jj)
    idd, gi = gamk(w, ph, 'I', geq, ii)
    i2d, gi2 = gamk(w, ph, "I'", geq, i2)
    ll, uu = c['L e. %s' % WWB], c['U e. %s' % WWB]
    rr, r2 = c['R e. %s' % WG], c["R' e. %s" % WG]
    dk = c['( D ` K ) = %s' % LST('L', 'R')]
    dj = c['( D ` J ) = %s' % LST('U', "R'")]
    bb, bw = c['B e. NN0'], c[RALW('L')]
    nss = c[NSSA]
    ex = {}
    ex["I' =/= I"] = w.s([c["I =/= I'"]], 'necomd', "( %s -> I' =/= I )" % ph)
    ex["I' =/= J"] = w.s([c["J =/= I'"]], 'necomd', "( %s -> I' =/= J )" % ph)
    njk = w.s([c['K =/= J']], 'necomd', '( %s -> J =/= K )' % ph)
    bld = Builder(w, ph, c, ex)
    # ---- stage 1: revList K I' I
    m1 = {'J': "I'", 'E': 'H"', "N'": 'N'}
    s1, c1 = inst(w, ph, 'tm2lrev2', m1, bld)
    C0, D1, B1 = triple_parts(c1)
    assert C0 == CL('P0', 'N', 'D') and B1 == BREV, (C0, B1)
    ERI = '( %s ++ ( D ` I\' ) )' % ENCB(REVL)
    DKR = UPDT('D', 'K', 'R')
    D1x = UPDT(DKR, "I'", ERI)
    assert D1 == CL('H"', 'N', D1x), D1
    # ---- stage 2: moveEntries I' J I from D1x
    diw = stkfvg(w, ph, 'D', "I'", tv, dd, i2d, gi2)
    djw = stkfvg(w, ph, 'D', 'J', tv, dd, jd, gj)
    rvl = w.s([ll, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REVL, WWB))
    ebc = w.s([rvl, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(REVL), WG))
    eri = ccatg(w, ph, ENCB(REVL), "( D ` I' )", ebc, diw)
    eriv = w.s([eri], 'elexd', '( %s -> %s e. _V )' % (ph, ERI))
    dkrcl = updcl(w, ph, 'D', 'K', 'R', tv, dd, kd, gk, rr)
    d1cl = updcl(w, ph, DKR, "I'", ERI, tv, dkrcl, i2d, gi2, eri)
    d1i = updk(w, ph, DKR, "I'", ERI, tv, dkrcl, i2d, eriv)
    rnr = w.s([ll, w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran L )' % (ph, REVL))
    rnl = w.s([rnr, w.inst('ssralv')], 'syl', '( %s -> ( %s -> %s ) )' % (ph, RALW('L'), RALW(REVL)))
    bwr = w.s([rnl, bw], 'mpd', '( %s -> %s )' % (ph, RALW(REVL)))
    ex2 = dict(ex)
    ex2['%s e. %s' % (D1x, STK_T)] = d1cl
    ex2["( %s ` I' ) = %s" % (D1x, LST(REVL, "( D ` I' )"))] = d1i
    ex2['%s e. %s' % (REVL, WWB)] = rvl
    ex2["( D ` I' ) e. %s" % WG] = diw
    ex2[RALW(REVL)] = bwr
    bld2 = Builder(w, ph, c, ex2)
    m2 = {'P1': 'H"', 'A': 'A0', "A'": 'B0', 'A"': 'C0', "B'": 'D0', 'B"': 'E0', "Q'": 'F0', "E'": 'G0',
          'K': "I'", "N'": 'N', 'D': D1x, 'L': REVL, 'R': "( D ` I' )"}
    s2, c2 = inst(w, ph, 'tm2lmes', m2, bld2)
    C1b, D2, B2 = triple_parts(c2)
    assert C1b == D1, (C1b, D1)
    W2 = '( %s ++ ( %s ` J ) )' % (ENT('( reverse ` %s )' % REVL), D1x)
    D2x = UPDT(UPDT(D1x, "I'", "( D ` I' )"), 'J', W2)
    assert D2 == CL('E', 'N', D2x), D2
    # ---- the J word: W2 = LST( ( L ++ U ) , R' )
    rv = w.s([ll, w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = L )' % (ph, REVL))
    rv2 = w.s([rv], 'fveq2d', '( %s -> %s = %s )' % (ph, ENT('( reverse ` %s )' % REVL), ENT('L')))
    j1 = updn(w, ph, DKR, "I'", ERI, 'J', tv, dkrcl, i2d, eriv, jd, ex["I' =/= J"] if False else w.s([c["J =/= I'"]], 'id', '( %s -> %s )' % ("J =/= I'", "J =/= I'")) if False else c["J =/= I'"])
    rv_ = w.s([rr], 'elexd', '( %s -> R e. _V )' % ph)
    j2 = updn(w, ph, 'D', 'K', 'R', 'J', tv, dd, kd, rv_, jd, njk)
    j3 = w.s([j1, j2], 'eqtrd', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph, D1x))
    j4 = w.s([j3, dj], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, D1x, LST('U', "R'")))
    ucc = w.s([uu, r2, w.inst('tm2lencbcc')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 2 "> ++ R\' ) ) )' % (ph, LST('U', "R'"), ENT('U')))
    j5 = w.s([j4, ucc], 'eqtrd', '( %s -> ( %s ` J ) = ( %s ++ ( <" 2 "> ++ R\' ) ) )' % (ph, D1x, ENT('U')))
    w1 = w.s([rv2, j5], 'oveq12d', '( %s -> %s = ( %s ++ ( %s ++ ( <" 2 "> ++ R\' ) ) ) )' % (ph, W2, ENT('L'), ENT('U')))
    entl = w.s([ll, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENT('L'), WG))
    entu = w.s([uu, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENT('U'), WG))
    c2s = s1g(w, ph, '2')
    c2r = ccatg(w, ph, '<" 2 ">', "R'", c2s, r2)
    asc = w.s([entl, entu, c2r, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ ( <" 2 "> ++ R\' ) ) = ( %s ++ ( %s ++ ( <" 2 "> ++ R\' ) ) ) )' % (ph, ENT('L'), ENT('U'), ENT('L'), ENT('U')))
    w2 = w.s([w1, asc], 'eqtr4d', '( %s -> %s = ( ( %s ++ %s ) ++ ( <" 2 "> ++ R\' ) ) )' % (ph, W2, ENT('L'), ENT('U')))
    ecc = w.s([ll, uu, w.inst('tm2lentcc')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, ENT('( L ++ U )'), ENT('L'), ENT('U')))
    ecc2 = w.s([ecc], 'oveq1d', '( %s -> ( %s ++ ( <" 2 "> ++ R\' ) ) = ( ( %s ++ %s ) ++ ( <" 2 "> ++ R\' ) ) )' % (ph, ENT('( L ++ U )'), ENT('L'), ENT('U')))
    w3 = w.s([w2, ecc2], 'eqtr4d', '( %s -> %s = ( %s ++ ( <" 2 "> ++ R\' ) ) )' % (ph, W2, ENT('( L ++ U )')))
    lucl = w.s([ll, uu, w.inst('ccatcl')], 'syl2anc', '( %s -> ( L ++ U ) e. %s )' % (ph, WWB))
    lcc = w.s([lucl, r2, w.inst('tm2lencbcc')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 2 "> ++ R\' ) ) )' % (ph, LST('( L ++ U )', "R'"), ENT('( L ++ U )')))
    weq = w.s([w3, lcc], 'eqtr4d', '( %s -> %s = %s )' % (ph, W2, LST('( L ++ U )', "R'")))
    # ---- the I' updates vanish: UPD( UPD( DKR , I' , ERI ) , I' , ( D ` I' ) ) = DKR
    erik = wgk(w, ph, ERI, "I'", gi2, eri)
    dik = wgk(w, ph, "( D ` I' )", "I'", gi2, diw)
    u2a = w.s([tv, dkrcl], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, DKR, STK_T))
    u2b = w.s([erik, dik], 'jca', '( %s -> ( %s e. Word %s /\\ ( D ` I\' ) e. Word %s ) )' % (ph, ERI, GT("I'"), GT("I'")))
    up2 = w.s([u2a, i2d, u2b, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )' % (ph, UPDT(D1x, "I'", "( D ` I' )"), UPDT(DKR, "I'", "( D ` I' )")))
    i1 = updn(w, ph, 'D', 'K', 'R', "I'", tv, dd, kd, rv_, i2d, c["I' =/= K"] if False else w.s([c["K =/= I'"]], 'necomd', "( %s -> I' =/= K )" % ph))
    i1r = w.s([i1], 'eqcomd', '( %s -> ( D ` I\' ) = ( %s ` I\' ) )' % (ph, DKR))
    st1, r1 = w.rewrite(UPDT(DKR, "I'", "( D ` I' )"), {"( D ` I' )": ('( %s ` I\' )' % DKR, i1r)}, ph)
    assert r1 == UPDT(DKR, "I'", '( %s ` I\' )' % DKR), r1
    upid = w.s([tv, dkrcl, i2d, w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = %s )' % (ph, r1, DKR))
    e1 = w.s([up2, st1], 'eqtrd', '( %s -> %s = %s )' % (ph, UPDT(D1x, "I'", "( D ` I' )"), r1))
    e2 = w.s([e1, upid], 'eqtrd', '( %s -> %s = %s )' % (ph, UPDT(D1x, "I'", "( D ` I' )"), DKR))
    st2, r2x = w.rewrite(D2x, {UPDT(D1x, "I'", "( D ` I' )"): (DKR, e2), W2: (LST('( L ++ U )', "R'"), weq)}, ph)
    assert r2x == AFIN, r2x
    s2b = hrtransport(w, ph, s2, D1, D2, B2, None, CL('E', 'N', AFIN), eqd=cleq(w, ph, 'E', 'N', D2x, AFIN, st2))
    # ---- the chain and the bound
    C2 = CL('E', 'N', AFIN)
    q = hseq(w, ph, phm, C0, D1, C2, BREV, B2, s1, s2b)
    TOT = '( %s + %s )' % (BREV, B2)
    rl = w.s([ll, w.inst('revlen')], 'syl', '( %s -> %s = %s )' % (ph, NLR, NL))
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    nlr = w.s([nl], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    br = w.s([bb], 'nn0red', '( %s -> B e. RR )' % ph)
    twoa = relit(w, ph, '2'); sixa = relit(w, ph, '6')
    tb = w.s([twoa, br], 'remulcld', '( %s -> ( 2 x. B ) e. RR )' % ph)
    b6 = w.s([tb, sixa], 'readdcld', '( %s -> ( ( 2 x. B ) + 6 ) e. RR )' % ph)
    PR = '( %s x. ( ( 2 x. B ) + 6 ) )' % NL
    PRR = '( %s x. ( ( 2 x. B ) + 6 ) )' % NLR
    prr = w.s([nlr, b6], 'remulcld', '( %s -> %s e. RR )' % (ph, PR))
    pre = w.s([rl], 'oveq1d', '( %s -> %s = %s )' % (ph, PRR, PR))
    b2e = w.s([pre], 'oveq1d', '( %s -> %s = ( %s + 3 ) )' % (ph, B2, PR))
    tote = w.s([b2e], 'oveq2d', '( %s -> %s = ( %s + ( %s + 3 ) ) )' % (ph, TOT, BREV, PR))
    # ( NL x. ( 4B + 12 ) ) = ( PR + PR )
    foura = relit(w, ph, '4'); twelve = w.s([], '12nn0', '; 1 2 e. NN0'); twelven = w.s([twelve], 'a1i', '( %s -> ; 1 2 e. NN0 )' % ph); twelvea = w.s([twelven], 'nn0red', '( %s -> ; 1 2 e. RR )' % ph)
    fb = w.s([foura, br], 'remulcld', '( %s -> ( 4 x. B ) e. RR )' % ph)
    b12 = w.s([fb, twelvea], 'readdcld', '( %s -> ( ( 4 x. B ) + ; 1 2 ) e. RR )' % ph)
    i1e = lineq(w, ph, '( ( 4 x. B ) + ; 1 2 )', '( ( ( 2 x. B ) + 6 ) + ( ( 2 x. B ) + 6 ) )', leaves={'B': br})
    i2e = w.s([i1e], 'oveq2d', '( %s -> ( %s x. ( ( 4 x. B ) + ; 1 2 ) ) = ( %s x. ( ( ( 2 x. B ) + 6 ) + ( ( 2 x. B ) + 6 ) ) ) )' % (ph, NL, NL))
    nlc = w.s([nl], 'nn0cnd', '( %s -> %s e. CC )' % (ph, NL))
    b6c = w.s([b6], 'recnd', '( %s -> ( ( 2 x. B ) + 6 ) e. CC )' % ph)
    dis = w.s([nlc, b6c, b6c, w.inst('adddi')], 'syl3anc', '( %s -> ( %s x. ( ( ( 2 x. B ) + 6 ) + ( ( 2 x. B ) + 6 ) ) ) = ( %s + %s ) )' % (ph, NL, PR, PR))
    i3e = w.s([i2e, dis], 'eqtrd', '( %s -> ( %s x. ( ( 4 x. B ) + ; 1 2 ) ) = ( %s + %s ) )' % (ph, NL, PR, PR))
    P4 = '( %s x. ( ( 4 x. B ) + ; 1 2 ) )' % NL
    p4r = w.s([nlr, b12], 'remulcld', '( %s -> %s e. RR )' % (ph, P4))
    eq = lineq(w, ph, '( %s + ( %s + 3 ) )' % (BREV, PR), BAPP, hyps=[i3e], leaves={PR: prr, P4: p4r}, atoms=[PR, P4])
    eq2 = w.s([tote, eq], 'eqtrd', '( %s -> %s = %s )' % (ph, TOT, BAPP))
    o = w.s([eq2], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C2, TOT, C2, BAPP))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C2, TOT), HR(C0, 'T', 'M', C2, BAPP)))
    w.qed([b, q], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BAPP)))
    return w.run()


if __name__ == '__main__':
    if want('tm2lrnrev'): tm2lrnrev()
    if want('tm2lapp'): tm2lapp()
