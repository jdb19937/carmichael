"""T6b: the N-level and B forms (blueprint 2.2-2.3): the entry-size bound
from the value bound (~ tm2lrnenc ), Lean's ` list_le_B ` (~ tm2llistb ),
and ` revList_correct/le_B ` , ` appendList_correct/le_B ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6blib import *
from cl import Closure


def hleqed(w, ante, phm, C, D, N, P, tri, pcl, le):
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, PHM, HR(C, 'T', 'M', D, N)))
    b = w.s([pcl, le], 'jca', '( %s -> ( %s e. NN0 /\\ %s <_ %s ) )' % (ante, P, N, P))
    w.qed([a, b, w.inst('tm2hle')], 'syl2anc', '( %s -> %s )' % (ante, HR(C, 'T', 'M', D, P)))

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

EL = '( encNatGam o. L )'
EU = '( encNatGam o. U )'
B64 = '( ; 6 4 x. ( B + 2 ) )'


def tm2lrnenc():
    lab = 'tm2lrnenc'
    ph = '( L e. Word NN0 /\\ B e. NN0 /\\ %s )' % RALA('L')
    w = W(lab, 'The entry-size bound of an encoded list from the value bound: every entry '
               'of ` ( encNatGam o. L ) ` has at most ` B ` bits when every value of ` L ` '
               'is below ` 2 ^ B ` .  Lean: ` entry_length_le_of_lt_pow ` .')
    ll = w.s([], 'simp1', '( %s -> L e. Word NN0 )' % ph)
    bb = w.s([], 'simp2', '( %s -> B e. NN0 )' % ph)
    ha = w.s([], 'simp3', '( %s -> %s )' % (ph, RALA('L')))
    ef = w.s([], 'tm2lbitf', 'encNatGam : NN0 --> %s' % WB)
    efn = w.s([ef, w.inst('ffn')], 'ax-mp', 'encNatGam Fn NN0')
    efna = w.s([efn], 'a1i', '( %s -> encNatGam Fn NN0 )' % ph)
    lf = w.s([ll, w.inst('wrdf')], 'syl', '( %s -> L : ( 0 ..^ ( # ` L ) ) --> NN0 )' % ph)
    rn = w.s([lf, w.inst('frn')], 'syl', '( %s -> ran L C_ NN0 )' % ph)
    e1 = w.s([], 'fveq2', '( w = ( encNatGam ` a ) -> ( # ` w ) = ( # ` ( encNatGam ` a ) ) )')
    e2 = w.s([e1], 'breq1d', '( w = ( encNatGam ` a ) -> ( ( # ` w ) <_ B <-> ( # ` ( encNatGam ` a ) ) <_ B ) )')
    IMG = '( encNatGam " ran L )'
    RB = 'A. a e. ran L ( # ` ( encNatGam ` a ) ) <_ B'
    im = w.s([e2], 'ralima', '( ( encNatGam Fn NN0 /\\ ran L C_ NN0 ) -> ( A. w e. %s ( # ` w ) <_ B <-> %s ) )' % (IMG, RB))
    im2 = w.s([efna, rn, im], 'syl2anc', '( %s -> ( A. w e. %s ( # ` w ) <_ B <-> %s ) )' % (ph, IMG, RB))
    ph0 = '( L e. Word NN0 /\\ B e. NN0 )'
    pa = '( %s /\\ a e. ran L )' % ph0
    l0 = w.s([], 'simpl', '( %s -> L e. Word NN0 )' % ph0)
    b0 = w.s([], 'simpr', '( %s -> B e. NN0 )' % ph0)
    lf0 = w.s([l0, w.inst('wrdf')], 'syl', '( %s -> L : ( 0 ..^ ( # ` L ) ) --> NN0 )' % ph0)
    rn0 = w.s([lf0, w.inst('frn')], 'syl', '( %s -> ran L C_ NN0 )' % ph0)
    aa = w.s([], 'simpr', '( %s -> a e. ran L )' % pa)
    rna = w.s([rn0], 'adantr', '( %s -> ran L C_ NN0 )' % pa)
    an = w.s([rna, aa], 'sseldd', '( %s -> a e. NN0 )' % pa)
    ba = w.s([b0], 'adantr', '( %s -> B e. NN0 )' % pa)
    lt = w.s([w.inst('tm2lentlt')], '3expia', '( ( a e. NN0 /\\ B e. NN0 ) -> ( a < ( 2 ^ B ) -> ( # ` ( encNatGam ` a ) ) <_ B ) )')
    lt2 = w.s([an, ba, lt], 'syl2anc', '( %s -> ( a < ( 2 ^ B ) -> ( # ` ( encNatGam ` a ) ) <_ B ) )' % pa)
    rd = w.s([lt2], 'ralimdva', '( %s -> ( %s -> %s ) )' % (ph0, RALA('L'), RB))
    rb = w.s([rd], '3impia', '( %s -> %s )' % (ph, RB))
    wi = w.s([im2, rb], 'mpbird', '( %s -> A. w e. %s ( # ` w ) <_ B )' % (ph, IMG))
    rc = w.s([], 'rnco2', 'ran %s = %s' % (EL, IMG))
    re = w.s([rc], 'raleqi', '( %s <-> A. w e. %s ( # ` w ) <_ B )' % (RALW(EL), IMG))
    w.qed([wi, re], 'sylibr', '( %s -> %s )' % (ph, RALW(EL)))
    return w.run()


def tm2llistb():
    lab = 'tm2llistb'
    ph = ST_LISTB.split(' -> ', 1)[0][2:]
    assert ST_LISTB == '( %s -> ( ( N x. C ) + D ) <_ ( ( N + 1 ) x. %s ) )' % (ph, TMB)
    w = W(lab, 'A per-entry bound linear in the bit size with a linear overhead is within '
               '` ( N + 1 ) ` budgets ` ( TMB ` B ) ` .  Lean: ` list_le_B ` ; from ~ tmblin at 64.')
    nb = w.s([], 'simp1', '( %s -> ( N e. NN0 /\\ B e. NN0 ) )' % ph)
    cd = w.s([], 'simp2', '( %s -> ( C e. NN0 /\\ D e. NN0 ) )' % ph)
    le = w.s([], 'simp3', '( %s -> ( C <_ %s /\\ D <_ %s ) )' % (ph, B64, B64))
    nn = w.s([nb], 'simpld', '( %s -> N e. NN0 )' % ph)
    bb = w.s([nb], 'simprd', '( %s -> B e. NN0 )' % ph)
    cc = w.s([cd], 'simpld', '( %s -> C e. NN0 )' % ph)
    dd = w.s([cd], 'simprd', '( %s -> D e. NN0 )' % ph)
    lc = w.s([le], 'simpld', '( %s -> C <_ %s )' % (ph, B64))
    ld = w.s([le], 'simprd', '( %s -> D <_ %s )' % (ph, B64))
    six = w.s([], '6nn0', '6 e. NN0'); four = w.s([], '4nn0', '4 e. NN0')
    s64 = w.s([six, four], 'deccl', '; 6 4 e. NN0')
    s64a = w.s([s64], 'a1i', '( %s -> ; 6 4 e. NN0 )' % ph)
    r64 = w.s([s64], 'nn0rei', '; 6 4 e. RR')
    l64 = w.s([r64], 'leidi', '; 6 4 <_ ; 6 4')
    l64a = w.s([l64], 'a1i', '( %s -> ; 6 4 <_ ; 6 4 )' % ph)
    tl = w.s([bb, s64a, l64a, w.inst('tmblin')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, B64, TMB))
    tn = w.s([bb, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TMB))
    tr = w.s([tn], 'nnred', '( %s -> %s e. RR )' % (ph, TMB))
    nr = w.s([nn], 'nn0red', '( %s -> N e. RR )' % ph)
    cr = w.s([cc], 'nn0red', '( %s -> C e. RR )' % ph)
    dr = w.s([dd], 'nn0red', '( %s -> D e. RR )' % ph)
    br = w.s([bb], 'nn0red', '( %s -> B e. RR )' % ph)
    n0 = w.s([nn], 'nn0ge0d', '( %s -> 0 <_ N )' % ph)
    cl = Closure(w, ph, {'N': nr, 'C': cr, 'D': dr, 'B': br, TMB: tr})
    b64r = cl.mem(B64, 'RR')
    c1 = w.s([cr, b64r, tr, lc, tl], 'letrd', '( %s -> C <_ %s )' % (ph, TMB))
    d1 = w.s([dr, b64r, tr, ld, tl], 'letrd', '( %s -> D <_ %s )' % (ph, TMB))
    nc = w.s([cr, tr, nr, n0, c1], 'lemul2ad', '( %s -> ( N x. C ) <_ ( N x. %s ) )' % (ph, TMB))
    linarith(w, ph, [nc, d1], '( ( N x. C ) + D ) <_ ( ( N + 1 ) x. %s )' % TMB, closure=cl, products=True, name='qed')
    return w.run()


def nlevel_common(w, ph, c):
    """the facts every N-level form needs; returns a dict"""
    phm = c[PHM]; geq = c[GEQ]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    ll = c['L e. Word NN0']; bb = c['B e. NN0']; ha = c[RALA('L')]
    ef = w.s([], 'tm2lbitf', 'encNatGam : NN0 --> %s' % WB)
    efa = w.s([ef], 'a1i', '( %s -> encNatGam : NN0 --> %s )' % (ph, WB))
    elc = w.s([ll, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. %s )' % (ph, EL, WWB))
    eq = w.s([ll, w.inst('tm2lenceq')], 'syl', '( %s -> %s = %s )' % (ph, ENC('L'), ENCB(EL)))
    bw = w.s([ll, bb, ha, w.inst('tm2lrnenc')], 'syl3anc', '( %s -> %s )' % (ph, RALW(EL)))
    ln = w.s([ll, efa, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, EL, NL))
    return dict(phm=phm, geq=geq, tv=tv, ll=ll, bb=bb, ha=ha, efa=efa, elc=elc, eq=eq, bw=bw, ln=ln)


def rev_n(w, ph, c, u, dk):
    """the run of tm2lrev2 at L := EL with the postcondition and bound in N-level form"""
    eq2 = w.s([u['eq']], 'oveq1d', '( %s -> ( %s ++ R ) = %s )' % (ph, ENC('L'), LST(EL, 'R')))
    dk2 = w.s([dk, eq2], 'eqtrd', '( %s -> ( D ` K ) = %s )' % (ph, LST(EL, 'R')))
    ex = {'%s e. %s' % (EL, WWB): u['elc'], '( D ` K ) = %s' % LST(EL, 'R'): dk2, RALW(EL): u['bw']}
    bld = Builder(w, ph, c, ex)
    s1, c1 = inst(w, ph, 'tm2lrev2', {'L': EL}, bld)
    C0, D1, B1 = triple_parts(c1)
    REL = '( reverse ` %s )' % EL
    ERL = '( encNatGam o. %s )' % REVL
    D1x = UPDT(UPDT('D', 'K', 'R'), 'J', '( %s ++ ( D ` J ) )' % ENCB(REL))
    assert D1 == CL('E', "N'", D1x), D1
    rc = w.s([u['ll'], u['efa'], w.inst('revco')], 'syl2anc', '( %s -> %s = %s )' % (ph, ERL, REL))
    rl = w.s([u['ll'], w.inst('revcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, REVL))
    e1 = w.s([rl, w.inst('tm2lenceq')], 'syl', '( %s -> %s = %s )' % (ph, ENC(REVL), ENCB(ERL)))
    e2 = w.s([rc], 'fveq2d', '( %s -> %s = %s )' % (ph, ENCB(ERL), ENCB(REL)))
    e3 = w.s([e1, e2], 'eqtrd', '( %s -> %s = %s )' % (ph, ENC(REVL), ENCB(REL)))
    e3r = w.s([e3], 'eqcomd', '( %s -> %s = %s )' % (ph, ENCB(REL), ENC(REVL)))
    st, r = w.rewrite(D1x, {ENCB(REL): (ENC(REVL), e3r)}, ph)
    assert r == RFINN, r
    s2 = hrtransport(w, ph, s1, C0, D1, B1, None, CL('E', "N'", RFINN), eqd=cleq(w, ph, 'E', "N'", D1x, RFINN, st))
    # the bound: ( # ` EL ) = NL
    be = w.s([u['ln']], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( ( 2 x. B ) + 6 ) ) = ( %s x. ( ( 2 x. B ) + 6 ) ) )' % (ph, EL, NL))
    be2 = w.s([be], 'oveq1d', '( %s -> %s = %s )' % (ph, B1, BREV))
    C2 = CL('E', "N'", RFINN)
    o = w.s([be2], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C2, B1, C2, BREV))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C2, B1), HR(C0, 'T', 'M', C2, BREV)))
    return b, s2, C0, C2


def tm2lrevn():
    lab = 'tm2lrevn'
    ph = PHRN
    w = W(lab, 'The fragment ` revList ` at the N level: the list ` ( encList ` L ) ` of '
               'numbers below ` 2 ^ B ` .  Lean: ` revList_correct ` ; ~ tm2lrev2 at '
               '` ( encNatGam o. L ) ` with ~ tm2lenceq , ~ tm2lrnenc , ~ revco and ~ lenco .')
    c = Ctx(w, ph, T_PHRN)
    u = nlevel_common(w, ph, c)
    dk = c['( D ` K ) = ( %s ++ R )' % ENC('L')]
    b, s2, C0, C2 = rev_n(w, ph, c, u, dk)
    w.qed([b, s2], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BREV)))
    return w.run()


def bform(w, ph, phm, base, C0, C2, BND, nl, bb, Cc, Dc):
    """raise the bound of base : C0 ~~> C2 in BND = ( ( NL x. Cc ) + Dc ) to BLB"""
    nlr = w.s([nl], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    br = w.s([bb], 'nn0red', '( %s -> B e. RR )' % ph)
    tn = w.s([bb, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, TMB))
    tn0 = w.s([tn], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, TMB))
    cl = Closure(w, ph, {'B': bb, NL: nl})
    ccl = cl.mem(Cc, 'NN0'); dcl = cl.mem(Dc, 'NN0')
    bge = w.s([bb], 'nn0ge0d', '( %s -> 0 <_ B )' % ph)
    l1 = linarith(w, ph, [bge], '%s <_ %s' % (Cc, B64), closure=cl)
    l2 = linarith(w, ph, [bge], '%s <_ %s' % (Dc, B64), closure=cl)
    a1 = w.s([nl, bb], 'jca', '( %s -> ( %s e. NN0 /\\ B e. NN0 ) )' % (ph, NL))
    a2 = w.s([ccl, dcl], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, Cc, Dc))
    a3 = w.s([l1, l2], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ph, Cc, B64, Dc, B64))
    lb = w.s([a1, a2, a3, w.inst('tm2llistb')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, BND, BLB))
    one = nn0lit(w, ph, '1')
    n1 = w.s([nl, one], 'nn0addcld', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, NL))
    blb = w.s([n1, tn0], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, BLB))
    return hleqed(w, ph, phm, C0, C2, BND, BLB, base, blb, lb)


def tm2lrevb():
    lab = 'tm2lrevb'
    ph = PHRN
    w = W(lab, 'The fragment ` revList ` within the budget ` ( ( ( # ` L ) + 1 ) x. ( TMB ` B ) ) ` . '
               'Lean: ` revList_le_B ` ; ~ tm2lrevn and ~ tm2llistb .')
    c = Ctx(w, ph, T_PHRN)
    phm = c[PHM]
    ll = c['L e. Word NN0']; bb = c['B e. NN0']
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    C0 = CL('P0', 'N', 'D'); C2 = CL('E', "N'", RFINN)
    base = w.s([], 'tm2lrevn', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BREV)))
    bform(w, ph, phm, base, C0, C2, BREV, nl, bb, '( ( 2 x. B ) + 6 )', '4')
    return w.run()


def app_n(w, ph, c, u, dk, dj):
    uu = c['U e. Word NN0']
    eq2 = w.s([u['eq']], 'oveq1d', '( %s -> ( %s ++ R ) = %s )' % (ph, ENC('L'), LST(EL, 'R')))
    dk2 = w.s([dk, eq2], 'eqtrd', '( %s -> ( D ` K ) = %s )' % (ph, LST(EL, 'R')))
    euc = w.s([uu, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. %s )' % (ph, EU, WWB))
    equ = w.s([uu, w.inst('tm2lenceq')], 'syl', '( %s -> %s = %s )' % (ph, ENC('U'), ENCB(EU)))
    eq3 = w.s([equ], 'oveq1d', '( %s -> ( %s ++ R\' ) = %s )' % (ph, ENC('U'), LST(EU, "R'")))
    dj2 = w.s([dj, eq3], 'eqtrd', '( %s -> ( D ` J ) = %s )' % (ph, LST(EU, "R'")))
    ex = {'%s e. %s' % (EL, WWB): u['elc'], '%s e. %s' % (EU, WWB): euc,
          '( D ` K ) = %s' % LST(EL, 'R'): dk2, '( D ` J ) = %s' % LST(EU, "R'"): dj2, RALW(EL): u['bw']}
    bld = Builder(w, ph, c, ex)
    s1, c1 = inst(w, ph, 'tm2lapp', {'L': EL, 'U': EU}, bld)
    C0, D1, B1 = triple_parts(c1)
    LU = '( L ++ U )'
    ELU = '( encNatGam o. %s )' % LU
    D1x = UPDT(UPDT('D', 'K', 'R'), 'J', LST('( %s ++ %s )' % (EL, EU), "R'"))
    assert D1 == CL('E', 'N', D1x), D1
    cc = w.s([u['ll'], uu, u['efa'], w.inst('ccatco')], 'syl3anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, ELU, EL, EU))
    luc = w.s([u['ll'], uu, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word NN0 )' % (ph, LU))
    e1 = w.s([luc, w.inst('tm2lenceq')], 'syl', '( %s -> %s = %s )' % (ph, ENC(LU), ENCB(ELU)))
    e2 = w.s([cc], 'fveq2d', '( %s -> %s = %s )' % (ph, ENCB(ELU), ENCB('( %s ++ %s )' % (EL, EU))))
    e3 = w.s([e1, e2], 'eqtrd', '( %s -> %s = %s )' % (ph, ENC(LU), ENCB('( %s ++ %s )' % (EL, EU))))
    e3r = w.s([e3], 'eqcomd', '( %s -> %s = %s )' % (ph, ENCB('( %s ++ %s )' % (EL, EU)), ENC(LU)))
    st, r = w.rewrite(D1x, {ENCB('( %s ++ %s )' % (EL, EU)): (ENC(LU), e3r)}, ph)
    assert r == AFINN, r
    s2 = hrtransport(w, ph, s1, C0, D1, B1, None, CL('E', 'N', AFINN), eqd=cleq(w, ph, 'E', 'N', D1x, AFINN, st))
    be = w.s([u['ln']], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( ( 4 x. B ) + ; 1 2 ) ) = ( %s x. ( ( 4 x. B ) + ; 1 2 ) ) )' % (ph, EL, NL))
    be2 = w.s([be], 'oveq1d', '( %s -> %s = %s )' % (ph, B1, BAPP))
    C2 = CL('E', 'N', AFINN)
    o = w.s([be2], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C2, B1, C2, BAPP))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C2, B1), HR(C0, 'T', 'M', C2, BAPP)))
    return b, s2, C0, C2


def tm2lappn():
    lab = 'tm2lappn'
    ph = PHAN
    w = W(lab, 'The fragment ` appendList ` at the N level.  Lean: ` appendList_correct ` ; '
               '~ tm2lapp at ` ( encNatGam o. L ) ` , ` ( encNatGam o. U ) ` with ~ ccatco .')
    c = Ctx(w, ph, T_PHAN)
    u = nlevel_common(w, ph, c)
    dk = c['( D ` K ) = ( %s ++ R )' % ENC('L')]
    dj = c['( D ` J ) = ( %s ++ R\' )' % ENC('U')]
    b, s2, C0, C2 = app_n(w, ph, c, u, dk, dj)
    w.qed([b, s2], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BAPP)))
    return w.run()


def tm2lappb():
    lab = 'tm2lappb'
    ph = PHAN
    w = W(lab, 'The fragment ` appendList ` within the budget.  Lean: ` appendList_le_B ` ; '
               '~ tm2lappn and ~ tm2llistb .')
    c = Ctx(w, ph, T_PHAN)
    phm = c[PHM]
    ll = c['L e. Word NN0']; bb = c['B e. NN0']
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    C0 = CL('P0', 'N', 'D'); C2 = CL('E', 'N', AFINN)
    base = w.s([], 'tm2lappn', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BAPP)))
    bform(w, ph, phm, base, C0, C2, BAPP, nl, bb, '( ( 4 x. B ) + ; 1 2 )', '7')
    return w.run()


if __name__ == '__main__':
    if want('tm2lrnenc'): tm2lrnenc()
    if want('tm2llistb'): tm2llistb()
    if want('tm2lrevn'): tm2lrevn()
    if want('tm2lrevb'): tm2lrevb()
    if want('tm2lappn'): tm2lappn()
    if want('tm2lappb'): tm2lappb()
