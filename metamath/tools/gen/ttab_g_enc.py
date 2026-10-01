"""T-TAB: the table encodings consumed by Step4 / Step5 (blueprint D9):
~ ttabkethd (` head?_encList_ne_ket `), ~ ttabslotk (` decide_head?_encSlot_ket `),
~ ttabtbb0 (` tblBounded_emptyTbl `), ~ ttabtbbm (` TblBounded.mono `),
~ ttabtbll (` encTblAsc_length_le `), ~ ttabtbdp (` tblBounded_dpStep `), with the
helpers ~ ttabopt , ~ ttabslotf , ~ ttabslotv , ~ ttabslen , ~ ttabgsln , ~ ttabtbav ,
~ ttabtbdr ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ttablib import *
from tm import W
from cl import Closure
from lin import linarith

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DJ = '( Word NN0 |_| 1o )'
NONE = '( inr ` (/) )'
WG = "Word Gamma'"
GS = lambda X: "( ( freeMnd ` Gamma' ) gsum %s )" % X
SLV = lambda O: 'if ( %s = %s , <" 3 "> , ( encList ` ( 2nd ` %s ) ) )' % (O, NONE, O)
ES = lambda O: '( encSlot ` %s )' % O
TBBI = lambda X, N, B: ('( %s =/= %s -> ( ( # ` ( 2nd ` %s ) ) <_ %s /\\ A. q e. ran ( 2nd ` %s ) q < ( 2 ^ %s ) ) )'
                        % (X, NONE, X, N, X, B))
TBBL = lambda T, N: 'A. d e. NN0 ( ( %s ` d ) =/= %s -> ( # ` ( 2nd ` ( %s ` d ) ) ) <_ %s )' % (T, NONE, T, N)
RNG = lambda X, B='B', q='q': 'A. %s e. ran ( 2nd ` %s ) %s < ( 2 ^ %s )' % (q, X, q, B)
TBBR = lambda T, c='d': 'A. %s e. NN0 ( ( %s ` %s ) =/= %s -> %s )' % (c, T, c, NONE, RNG('( %s ` %s )' % (T, c)))
T2 = '( 1st ` ( ( L DpStep P ) ` T ) )'


def ttabopt():
    lab = 'ttabopt'
    w = W(lab, 'The second component of an element of ` Option ( List Nat ) ` (~ df-tbl ) is a list of '
               'numbers: ` ( inl `` W ) ` has ` W ` , ` none = ( inr `` (/) ) ` has ` (/) ` .')
    XP = '( { (/) , 1o } X. ( Word NN0 u. 1o ) )'
    a = w.s([], 'djuss', '%s C_ %s' % (DJ, XP))
    b = w.s([a], 'sseli', '( O e. %s -> O e. %s )' % (DJ, XP))
    c = w.s([], 'xp2nd', '( O e. %s -> ( 2nd ` O ) e. ( Word NN0 u. 1o ) )' % XP)
    bc = w.s([b, c], 'syl', '( O e. %s -> ( 2nd ` O ) e. ( Word NN0 u. 1o ) )' % DJ)
    d1 = w.s([], 'df1o2', '1o = { (/) }')
    d2 = w.s([w.s([], 'wrd0', '(/) e. Word NN0'), w.s([], 'snssi', '( (/) e. Word NN0 -> { (/) } C_ Word NN0 )')], 'ax-mp', '{ (/) } C_ Word NN0')
    d3 = w.s([d1, d2], 'eqsstri', '1o C_ Word NN0')
    e1 = w.s([], 'ssequn2', '( 1o C_ Word NN0 <-> ( Word NN0 u. 1o ) = Word NN0 )')
    e2 = w.s([d3, e1], 'mpbi', '( Word NN0 u. 1o ) = Word NN0')
    w.qed([bc, e2], 'eleqtrdi', '( O e. %s -> ( 2nd ` O ) e. Word NN0 )' % DJ)
    return w.run()


def slotcl(w, ph, ocl):
    """( ph -> SLV( O ) e. Word Gamma' ) from ocl : ( ph -> O e. DJ ), O the letter o or O"""
    O = w_last_letter(ocl)
    g3 = w.s([w.s([], 'gamma3', "3 e. Gamma'")], 'a1i', "( %s -> 3 e. Gamma' )" % ph)
    s3 = w.s([g3], 's1cld', '( %s -> <" 3 "> e. %s )' % (ph, WG))
    o2 = w.s([ocl, w.inst('ttabopt')], 'syl', '( %s -> ( 2nd ` %s ) e. Word NN0 )' % (ph, O))
    el = w.s([o2, w.inst('tm2lenccl')], 'syl', '( %s -> ( encList ` ( 2nd ` %s ) ) e. %s )' % (ph, O, WG))
    return w.s([s3, el, w.inst('ifcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, SLV(O), WG))


_LETTER = {}
def w_last_letter(step):
    return _LETTER[step]


def ttabslotf():
    lab = 'ttabslotf'
    w = W(lab, 'A slot of the DP table on a stack is a word over ` Gamma\' ` .')
    ph = 'o e. %s' % DJ
    oc = w.s([], 'id', '( %s -> %s )' % (ph, ph)); _LETTER[oc] = 'o'
    cl = slotcl(w, ph, oc)
    df = w.s([], 'df-tm2encslot', 'encSlot = ( o e. %s |-> %s )' % (DJ, SLV('o')))
    w.qed([df, cl], 'fmpti', 'encSlot : %s --> %s' % (DJ, WG))
    return w.run()


def ttabslotv():
    lab = 'ttabslotv'
    w = W(lab, 'Value of ~ df-tm2encslot .  Lean: ` encSlot ` .')
    ph = 'O e. %s' % DJ
    oc = w.s([], 'id', '( %s -> %s )' % (ph, ph)); _LETTER[oc] = 'O'
    cl = slotcl(w, ph, oc)
    h1 = w.s([], 'eqeq1', '( o = O -> ( o = %s <-> O = %s ) )' % (NONE, NONE))
    h2 = w.s([], 'eqidd', '( o = O -> <" 3 "> = <" 3 "> )')
    h3 = w.s([], '2fveq3', '( o = O -> ( encList ` ( 2nd ` o ) ) = ( encList ` ( 2nd ` O ) ) )')
    h = w.s([h1, h2, h3], 'ifbieq12d', '( o = O -> %s = %s )' % (SLV('o'), SLV('O')))
    df = w.s([], 'df-tm2encslot', 'encSlot = ( o e. %s |-> %s )' % (DJ, SLV('o')))
    fv = w.s([h, df], 'fvmptg', "( ( O e. %s /\\ %s e. %s ) -> %s = %s )" % (DJ, SLV('O'), WG, ES('O'), SLV('O')))
    w.qed([oc, cl, fv], 'syl2anc', '( %s -> %s = %s )' % (ph, ES('O'), SLV('O')))
    return w.run()


def ttabtbb0():
    lab = 'ttabtbb0'
    w = W(lab, 'The empty table is bounded, every slot being empty.  Lean: ` tblBounded_emptyTbl ` '
               '(over every residue, blueprint D9).')
    ph = '( N e. NN0 /\\ B e. NN0 )'
    X = '( EmptyTbl ` d )'
    a = w.s([], 'emptytblval', '( d e. NN0 -> %s = %s )' % (X, NONE))
    b = w.s([a, w.inst('nne')], 'sylibr', '( d e. NN0 -> -. %s =/= %s )' % (X, NONE))
    c = w.s([b], 'pm2.21d', '( d e. NN0 -> %s )' % TBBI(X, 'N', 'B'))
    r = w.s([c], 'rgen', 'A. d e. NN0 %s' % TBBI(X, 'N', 'B'))
    w.qed([r], 'a1i', '( %s -> A. d e. NN0 %s )' % (ph, TBBI(X, 'N', 'B')))
    return w.run()


def ttabtbbm():
    lab = 'ttabtbbm'
    w = W(lab, 'The table bound is monotone in the slot length bound.  Lean: ` TblBounded.mono ` .')
    ps = "( N e. NN0 /\\ N' e. NN0 /\\ N <_ N' )"
    X = '( T ` d )'
    H = '( # ` ( 2nd ` %s ) )' % X
    Q = RNG(X)
    hx = w.s([w.s([], 'fvex', '( 2nd ` %s ) e. _V' % X), w.s([], 'hashxrcl', '( ( 2nd ` %s ) e. _V -> %s e. RR* )' % (X, H))],
             'ax-mp', '%s e. RR*' % H)
    hxa = w.s([hx], 'a1i', '( %s -> %s e. RR* )' % (ps, H))
    n = w.s([w.s([w.s([], 'simp1', '( %s -> N e. NN0 )' % ps)], 'nn0red', '( %s -> N e. RR )' % ps)], 'rexrd', '( %s -> N e. RR* )' % ps)
    n2 = w.s([w.s([w.s([], 'simp2', "( %s -> N' e. NN0 )" % ps)], 'nn0red', "( %s -> N' e. RR )" % ps)], 'rexrd', "( %s -> N' e. RR* )" % ps)
    le = w.s([], 'simp3', "( %s -> N <_ N' )" % ps)
    tr = w.s([hxa, n, n2, w.inst('xrletr')], 'syl3anc', "( %s -> ( ( %s <_ N /\\ N <_ N' ) -> %s <_ N' ) )" % (ps, H, H))
    t2 = w.s([le, tr], 'mpan2d', "( %s -> ( %s <_ N -> %s <_ N' ) )" % (ps, H, H))
    t3 = w.s([t2], 'anim1d', "( %s -> ( ( %s <_ N /\\ %s ) -> ( %s <_ N' /\\ %s ) ) )" % (ps, H, Q, H, Q))
    t4 = w.s([t3], 'imim2d', "( %s -> ( %s -> %s ) )" % (ps, TBBI(X, 'N', 'B'), TBBI(X, "N'", 'B')))
    t5 = w.s([t4], 'ralimdv', "( %s -> ( A. d e. NN0 %s -> A. d e. NN0 %s ) )" % (ps, TBBI(X, 'N', 'B'), TBBI(X, "N'", 'B')))
    w.qed([t5], 'imp', "( ( %s /\\ A. d e. NN0 %s ) -> A. d e. NN0 %s )" % (ps, TBBI(X, 'N', 'B'), TBBI(X, "N'", 'B')))
    return w.run()


def not3(w):
    """closed step: -. 3 e. ( ( { 1 } X. 2o ) u. { 4 } ) (3 is neither a bit nor ` comma = 4 `)"""
    from tm import numne
    U = '( ( { 1 } X. 2o ) u. { 4 } )'
    r3 = w.s([], '3re', '3 e. RR')
    z1 = w.s([r3, w.s([], 'tmcnbits', '( 3 e. RR -> -. 3 e. ( { 1 } X. 2o ) )')], 'ax-mp', '-. 3 e. ( { 1 } X. 2o )')
    z2 = w.s([r3, w.s([], 'elsng', '( 3 e. RR -> ( 3 e. { 4 } <-> 3 = 4 ) )')], 'ax-mp', '( 3 e. { 4 } <-> 3 = 4 )')
    z3 = numne(w, '3', '4')
    z4 = w.s([z3, z2], 'mtbir', '-. 3 e. { 4 }')
    z5 = w.s([z1, z4], 'pm3.2ni', '-. ( 3 e. ( { 1 } X. 2o ) \\/ 3 e. { 4 } )')
    z6 = w.s([], 'elun', '( 3 e. %s <-> ( 3 e. ( { 1 } X. 2o ) \\/ 3 e. { 4 } ) )' % U)
    return w.s([z5, z6], 'mtbir', '-. 3 e. %s' % U)


def ttabkethd():
    lab = 'ttabkethd'
    w = W(lab, 'The first letter of a list of numbers on a stack (followed by anything) is not '
               '` ket = 3 ` : it is ` bra = 2 ` for the empty list, a bit or a comma otherwise.  Lean: '
               '` head?_encList_ne_ket ` .')
    ph = "( W e. Word NN0 /\\ R e. %s )" % WG
    E = '( encNatGam o. W )'
    U = '( ( { 1 } X. 2o ) u. { 4 } )'
    H = lambda X: '( ( ( encListB ` %s ) ++ R ) ` 0 )' % X
    wW = w.s([], 'simpl', '( %s -> W e. Word NN0 )' % ph)
    eq = w.s([wW, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` W ) = ( encListB ` %s ) )' % (ph, E))
    e1 = w.s([eq], 'oveq1d', '( %s -> ( ( encList ` W ) ++ R ) = ( ( encListB ` %s ) ++ R ) )' % (ph, E))
    e2 = w.s([e1], 'fveq1d', '( %s -> ( ( ( encList ` W ) ++ R ) ` 0 ) = %s )' % (ph, H(E)))
    # E = (/)
    p1 = '( %s /\\ %s = (/) )' % (ph, E)
    x1 = w.s([], 'simpr', '( %s -> %s = (/) )' % (p1, E))
    x2 = w.s([x1], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` (/) ) )' % (p1, E))
    x3 = w.s([x2], 'oveq1d', '( %s -> ( ( encListB ` %s ) ++ R ) = ( ( encListB ` (/) ) ++ R ) )' % (p1, E))
    x4 = w.s([x3], 'fveq1d', '( %s -> %s = %s )' % (p1, H(E), H('(/)')))
    x5 = w.s([], 'simplr', '( %s -> R e. %s )' % (p1, WG))
    x6 = w.s([x5, w.inst('tm2lencbhd0')], 'syl', '( %s -> %s = 2 )' % (p1, H('(/)')))
    x7 = w.s([x4, x6], 'eqtrd', '( %s -> %s = 2 )' % (p1, H(E)))
    from tm import numne
    n23 = w.s([numne(w, '2', '3')], 'neir', '2 =/= 3')
    x8 = w.s([n23], 'a1i', '( %s -> 2 =/= 3 )' % p1)
    x9 = w.s([x7, x8], 'eqnetrd', '( %s -> %s =/= 3 )' % (p1, H(E)))
    c1 = w.s([x9], 'ex', '( %s -> ( %s = (/) -> %s =/= 3 ) )' % (ph, E, H(E)))
    # E =/= (/)
    p2 = '( %s /\\ %s =/= (/) )' % (ph, E)
    y0 = w.s([], 'simpll', '( %s -> W e. Word NN0 )' % p2)
    y1 = w.s([y0, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word ( { 1 } X. 2o ) )' % (p2, E))
    y2 = w.s([], 'simplr', '( %s -> R e. %s )' % (p2, WG))
    y3 = w.s([], 'simpr', '( %s -> %s =/= (/) )' % (p2, E))
    y4 = w.s([y1, y2, y3, w.inst('tm2lencbhd1')], 'syl3anc', '( %s -> %s e. %s )' % (p2, H(E), U))
    y5 = w.s([not3(w)], 'a1i', '( %s -> -. 3 e. %s )' % (p2, U))
    y6 = w.s([y4, y5, w.inst('nelne2')], 'syl2anc', '( %s -> %s =/= 3 )' % (p2, H(E)))
    c2 = w.s([y6], 'ex', '( %s -> ( %s =/= (/) -> %s =/= 3 ) )' % (ph, E, H(E)))
    hE = w.s([c1, c2], 'pm2.61dne', '( %s -> %s =/= 3 )' % (ph, H(E)))
    w.qed([e2, hE], 'eqnetrd', '( %s -> ( ( ( encList ` W ) ++ R ) ` 0 ) =/= 3 )' % ph)
    return w.run()


def ttabslotk():
    lab = 'ttabslotk'
    w = W(lab, 'The first letter of a slot on a stack (followed by anything) is ` ket = 3 ` exactly when '
               'the slot is empty.  Lean: ` decide_head?_encSlot_ket ` .')
    ph = "( O e. %s /\\ R e. %s )" % (DJ, WG)
    HS = '( ( %s ++ R ) ` 0 )' % ES('O')
    S3 = '<" 3 ">'
    oc = w.s([], 'simpl', '( %s -> O e. %s )' % (ph, DJ))
    v = w.s([oc, w.inst('ttabslotv')], 'syl', '( %s -> %s = %s )' % (ph, ES('O'), SLV('O')))
    # O = none
    p1 = '( %s /\\ O = %s )' % (ph, NONE)
    a1 = w.s([], 'simpr', '( %s -> O = %s )' % (p1, NONE))
    a2 = w.s([a1], 'iftrued', '( %s -> %s = %s )' % (p1, SLV('O'), S3))
    a3 = w.s([w.s([v], 'adantr', '( %s -> %s = %s )' % (p1, ES('O'), SLV('O'))), a2], 'eqtrd', '( %s -> %s = %s )' % (p1, ES('O'), S3))
    a4 = w.s([a3], 'oveq1d', '( %s -> ( %s ++ R ) = ( %s ++ R ) )' % (p1, ES('O'), S3))
    a5 = w.s([a4], 'fveq1d', '( %s -> %s = ( ( %s ++ R ) ` 0 ) )' % (p1, HS, S3))
    g3 = w.s([w.s([], 'gamma3', "3 e. Gamma'")], 'a1i', "( %s -> 3 e. Gamma' )" % p1)
    s3 = w.s([g3], 's1cld', '( %s -> %s e. %s )' % (p1, S3, WG))
    rr = w.s([], 'simplr', '( %s -> R e. %s )' % (p1, WG))
    l1 = w.s([w.s([], '0lt1', '0 < 1'), w.s([], 's1len', '( # ` %s ) = 1' % S3)], 'breqtrri', '0 < ( # ` %s )' % S3)
    l1a = w.s([l1], 'a1i', '( %s -> 0 < ( # ` %s ) )' % (p1, S3))
    a6 = w.s([s3, rr, l1a, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( ( %s ++ R ) ` 0 ) = ( %s ` 0 ) )' % (p1, S3, S3))
    a7 = w.s([w.s([], 'gamma3', "3 e. Gamma'"), w.s([], 's1fv', "( 3 e. Gamma' -> ( %s ` 0 ) = 3 )" % S3)], 'ax-mp', '( %s ` 0 ) = 3' % S3)
    a7a = w.s([a7], 'a1i', '( %s -> ( %s ` 0 ) = 3 )' % (p1, S3))
    a8 = w.s([w.s([a5, a6], 'eqtrd', '( %s -> %s = ( %s ` 0 ) )' % (p1, HS, S3)), a7a], 'eqtrd', '( %s -> %s = 3 )' % (p1, HS))
    a9 = w.s([a8, a1], '2thd', '( %s -> ( %s = 3 <-> O = %s ) )' % (p1, HS, NONE))
    c1 = w.s([a9], 'ex', '( %s -> ( O = %s -> ( %s = 3 <-> O = %s ) ) )' % (ph, NONE, HS, NONE))
    # O =/= none
    p2 = '( %s /\\ O =/= %s )' % (ph, NONE)
    EL = '( encList ` ( 2nd ` O ) )'
    b0 = w.s([], 'simpr', '( %s -> O =/= %s )' % (p2, NONE))
    b1 = w.s([b0], 'neneqd', '( %s -> -. O = %s )' % (p2, NONE))
    b2 = w.s([b1], 'iffalsed', '( %s -> %s = %s )' % (p2, SLV('O'), EL))
    b3 = w.s([w.s([v], 'adantr', '( %s -> %s = %s )' % (p2, ES('O'), SLV('O'))), b2], 'eqtrd', '( %s -> %s = %s )' % (p2, ES('O'), EL))
    b4 = w.s([b3], 'oveq1d', '( %s -> ( %s ++ R ) = ( %s ++ R ) )' % (p2, ES('O'), EL))
    b5 = w.s([b4], 'fveq1d', '( %s -> %s = ( ( %s ++ R ) ` 0 ) )' % (p2, HS, EL))
    b6 = w.s([w.s([], 'simpll', '( %s -> O e. %s )' % (p2, DJ)), w.inst('ttabopt')], 'syl', '( %s -> ( 2nd ` O ) e. Word NN0 )' % p2)
    b7 = w.s([b6, w.s([], 'simplr', '( %s -> R e. %s )' % (p2, WG)), w.inst('ttabkethd')], 'syl2anc',
             '( %s -> ( ( %s ++ R ) ` 0 ) =/= 3 )' % (p2, EL))
    b8 = w.s([w.s([b5, b7], 'eqnetrd', '( %s -> %s =/= 3 )' % (p2, HS))], 'neneqd', '( %s -> -. %s = 3 )' % (p2, HS))
    b9 = w.s([b8, b1], '2falsed', '( %s -> ( %s = 3 <-> O = %s ) )' % (p2, HS, NONE))
    c2 = w.s([b9], 'ex', '( %s -> ( O =/= %s -> ( %s = 3 <-> O = %s ) ) )' % (ph, NONE, HS, NONE))
    w.qed([c1, c2], 'pm2.61dne', '( %s -> ( %s = 3 <-> O = %s ) )' % (ph, HS, NONE))
    return w.run()


KB = '( ( N x. ( B + 1 ) ) + 1 )'


def ttabslen():
    lab = 'ttabslen'
    w = W(lab, 'The length of a slot on a stack with at most ` N ` entries below ` 2 ^ B ` .  Lean: '
               '` encSlot_length_le ` .')
    ph = '( O e. %s /\\ ( N e. NN0 /\\ B e. NN0 ) /\\ %s )' % (DJ, TBBI('O', 'N', 'B'))
    oc = w.s([], 'simp1', '( %s -> O e. %s )' % (ph, DJ))
    nb = w.s([], 'simp2', '( %s -> ( N e. NN0 /\\ B e. NN0 ) )' % ph)
    nN = w.s([nb], 'simpld', '( %s -> N e. NN0 )' % ph)
    nB = w.s([nb], 'simprd', '( %s -> B e. NN0 )' % ph)
    hb = w.s([], 'simp3', '( %s -> %s )' % (ph, TBBI('O', 'N', 'B')))
    v = w.s([oc, w.inst('ttabslotv')], 'syl', '( %s -> %s = %s )' % (ph, ES('O'), SLV('O')))
    S3 = '<" 3 ">'
    L = '( # ` %s )' % ES('O')
    # O = none
    p1 = '( %s /\\ O = %s )' % (ph, NONE)
    a1 = w.s([], 'simpr', '( %s -> O = %s )' % (p1, NONE))
    a2 = w.s([a1], 'iftrued', '( %s -> %s = %s )' % (p1, SLV('O'), S3))
    a3 = w.s([w.s([v], 'adantr', '( %s -> %s = %s )' % (p1, ES('O'), SLV('O'))), a2], 'eqtrd', '( %s -> %s = %s )' % (p1, ES('O'), S3))
    a4 = w.s([a3], 'fveq2d', '( %s -> %s = ( # ` %s ) )' % (p1, L, S3))
    a5 = w.s([w.s([], 's1len', '( # ` %s ) = 1' % S3)], 'a1i', '( %s -> ( # ` %s ) = 1 )' % (p1, S3))
    a6 = w.s([a4, a5], 'eqtrd', '( %s -> %s = 1 )' % (p1, L))
    c1 = Closure(w, p1, {'N': w.s([nN], 'adantr', '( %s -> N e. NN0 )' % p1), 'B': w.s([nB], 'adantr', '( %s -> B e. NN0 )' % p1)})
    PR = '( N x. ( B + 1 ) )'
    g1 = w.s([c1.mem(PR, 'NN0')], 'nn0ge0d', '( %s -> 0 <_ %s )' % (p1, PR))
    c1.atom(PR)
    le1 = linarith(w, p1, [g1], '1 <_ %s' % KB, closure=c1)
    b1 = w.s([a6, le1], 'eqbrtrd', '( %s -> %s <_ %s )' % (p1, L, KB))
    k1 = w.s([b1], 'ex', '( %s -> ( O = %s -> %s <_ %s ) )' % (ph, NONE, L, KB))
    # O =/= none
    p2 = '( %s /\\ O =/= %s )' % (ph, NONE)
    EL = '( encList ` ( 2nd ` O ) )'
    X2 = '( 2nd ` O )'
    y0 = w.s([], 'simpr', '( %s -> O =/= %s )' % (p2, NONE))
    y1 = w.s([y0], 'neneqd', '( %s -> -. O = %s )' % (p2, NONE))
    y2 = w.s([y1], 'iffalsed', '( %s -> %s = %s )' % (p2, SLV('O'), EL))
    y3 = w.s([w.s([v], 'adantr', '( %s -> %s = %s )' % (p2, ES('O'), SLV('O'))), y2], 'eqtrd', '( %s -> %s = %s )' % (p2, ES('O'), EL))
    y4 = w.s([y3], 'fveq2d', '( %s -> %s = ( # ` %s ) )' % (p2, L, EL))
    hh = w.s([y0, w.s([hb], 'adantr', '( %s -> %s )' % (p2, TBBI('O', 'N', 'B')))], 'mpd',
             '( %s -> ( ( # ` %s ) <_ N /\\ %s ) )' % (p2, X2, RNG('O')))
    hl = w.s([hh], 'simpld', '( %s -> ( # ` %s ) <_ N )' % (p2, X2))
    hr = w.s([hh], 'simprd', '( %s -> %s )' % (p2, RNG('O')))
    cb = w.s([w.s([], 'breq1', '( q = a -> ( q < ( 2 ^ B ) <-> a < ( 2 ^ B ) ) )')], 'cbvralvw',
             '( %s <-> %s )' % (RNG('O'), RNG('O', q='a')))
    ha = w.s([hr, cb], 'sylib', '( %s -> %s )' % (p2, RNG('O', q='a')))
    o2 = w.s([w.s([], 'simpl1', '( %s -> O e. %s )' % (p2, DJ)), w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (p2, X2))
    nN2 = w.s([nN], 'adantr', '( %s -> N e. NN0 )' % p2)
    nB2 = w.s([nB], 'adantr', '( %s -> B e. NN0 )' % p2)
    ln = w.s([o2, nB2, ha, w.inst('tm2lenclen')], 'syl3anc',
             '( %s -> ( # ` %s ) <_ ( ( ( # ` %s ) x. ( B + 1 ) ) + 1 ) )' % (p2, EL, X2))
    hx = w.s([o2, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (p2, X2))
    he = w.s([w.s([o2, w.inst('tm2lenccl')], 'syl', '( %s -> %s e. %s )' % (p2, EL, WG)), w.inst('lencl')], 'syl',
             '( %s -> ( # ` %s ) e. NN0 )' % (p2, EL))
    c2 = Closure(w, p2, {'N': nN2, 'B': nB2, '( # ` %s )' % X2: hx, '( # ` %s )' % EL: he})
    B1 = '( B + 1 )'
    mul = w.s([c2.mem('( # ` %s )' % X2, 'RR'), c2.mem('N', 'RR'), c2.mem(B1, 'RR'),
               w.s([c2.mem(B1, 'NN0')], 'nn0ge0d', '( %s -> 0 <_ %s )' % (p2, B1)), hl], 'lemul1ad',
              '( %s -> ( ( # ` %s ) x. %s ) <_ ( N x. %s ) )' % (p2, X2, B1, B1))
    c2.atom('( ( # ` %s ) x. %s )' % (X2, B1)); c2.atom(PR)
    le2 = linarith(w, p2, [ln, mul], '( # ` %s ) <_ %s' % (EL, KB), closure=c2)
    b2 = w.s([y4, le2], 'eqbrtrd', '( %s -> %s <_ %s )' % (p2, L, KB))
    k2 = w.s([b2], 'ex', '( %s -> ( O =/= %s -> %s <_ %s ) )' % (ph, NONE, L, KB))
    w.qed([k1, k2], 'pm2.61dne', '( %s -> %s <_ %s )' % (ph, L, KB))
    return w.run()


def ttabgsln():
    lab = 'ttabgsln'
    WWG = "Word Word Gamma'"
    ph = '( W e. %s /\\ K e. NN0 /\\ A. w e. ran W ( # ` w ) <_ K )' % WWG
    w = W(lab, 'The length of a monoid sum of words over ` Gamma\' ` each of length at most ` K ` , by ~ wrdind .')
    RW = lambda X: 'A. w e. ran %s ( # ` w ) <_ K' % X
    PROP = lambda X: '( ( K e. NN0 /\\ %s ) -> ( # ` %s ) <_ ( ( # ` %s ) x. K ) )' % (RW(X), GS(X), X)
    YZ = '( y ++ <" z "> )'

    def cg(X):
        st, new = w.wcongr(PROP('x'), {'x': X}, 'x = %s' % X, {'x': w.s([], 'id', '( x = %s -> x = %s )' % (X, X))})
        assert new == PROP(X), new
        return st
    q1 = cg('(/)'); q2 = cg('y'); q3 = cg(YZ); q4 = cg('W')
    pb = '( K e. NN0 /\\ %s )' % RW('(/)')
    kb = w.s([], 'simpl', '( %s -> K e. NN0 )' % pb)
    h0 = w.s([w.s([], 'gsumgam0', '%s = (/)' % GS('(/)'))], 'fveq2i', '( # ` %s ) = ( # ` (/) )' % GS('(/)'))
    z0 = w.s([], 'hash0', '( # ` (/) ) = 0')
    h1 = w.s([h0, z0], 'eqtri', '( # ` %s ) = 0' % GS('(/)'))
    h1a = w.s([h1], 'a1i', '( %s -> ( # ` %s ) = 0 )' % (pb, GS('(/)')))
    kc = w.s([kb], 'nn0cnd', '( %s -> K e. CC )' % pb)
    mz = w.s([kc], 'mul02d', '( %s -> ( 0 x. K ) = 0 )' % pb)
    z1 = w.s([w.s([z0], 'oveq1i', '( ( # ` (/) ) x. K ) = ( 0 x. K )')], 'a1i', '( %s -> ( ( # ` (/) ) x. K ) = ( 0 x. K ) )' % pb)
    z2 = w.s([z1, mz], 'eqtrd', '( %s -> ( ( # ` (/) ) x. K ) = 0 )' % pb)
    le0 = w.s([w.s([], '0le0', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % pb)
    bs = w.s([h1a, z2, le0], '3brtr4d', '( %s -> ( # ` %s ) <_ ( ( # ` (/) ) x. K ) )' % (pb, GS('(/)')))
    yz = "( y e. %s /\\ z e. %s )" % (WWG, WG)
    big = '( ( %s /\\ %s ) /\\ ( K e. NN0 /\\ %s ) )' % (yz, PROP('y'), RW(YZ))
    yzs = w.s([], 'simpll', '( %s -> %s )' % (big, yz))
    yy = w.s([yzs], 'simpld', '( %s -> y e. %s )' % (big, WWG))
    zz = w.s([yzs], 'simprd', '( %s -> z e. %s )' % (big, WG))
    ih = w.s([], 'simplr', '( %s -> %s )' % (big, PROP('y')))
    kr = w.s([], 'simpr', '( %s -> ( K e. NN0 /\\ %s ) )' % (big, RW(YZ)))
    kk = w.s([kr], 'simpld', '( %s -> K e. NN0 )' % big)
    hb = w.s([kr], 'simprd', '( %s -> %s )' % (big, RW(YZ)))
    zs = w.s([zz], 's1cld', '( %s -> <" z "> e. %s )' % (big, WWG))
    rn = w.s([yy, zs, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran y u. ran <" z "> ) )' % (big, YZ))
    s1r = w.s([zz, w.inst('s1rn')], 'syl', '( %s -> ran <" z "> = { z } )' % big)
    rn2 = w.s([rn, w.s([s1r], 'uneq2d', '( %s -> ( ran y u. ran <" z "> ) = ( ran y u. { z } ) )' % big)], 'eqtrd',
              '( %s -> ran %s = ( ran y u. { z } ) )' % (big, YZ))
    u1b = w.s([w.s([w.s([], 'ssun1', 'ran y C_ ( ran y u. { z } )')], 'a1i', '( %s -> ran y C_ ( ran y u. { z } ) )' % big), rn2],
              'sseqtrrd', '( %s -> ran y C_ ran %s )' % (big, YZ))
    hyi = w.s([u1b, w.inst('ssralv')], 'syl', '( %s -> ( %s -> %s ) )' % (big, RW(YZ), RW('y')))
    hy2 = w.s([hyi, hb], 'mpd', '( %s -> %s )' % (big, RW('y')))
    mh = w.s([kk, hy2], 'jca', '( %s -> ( K e. NN0 /\\ %s ) )' % (big, RW('y')))
    ihc = w.s([ih, mh], 'mpd', '( %s -> ( # ` %s ) <_ ( ( # ` y ) x. K ) )' % (big, GS('y')))
    zv = w.s([zz], 'elexd', '( %s -> z e. _V )' % big)
    zsn = w.s([zv, w.inst('snidg')], 'syl', '( %s -> z e. { z } )' % big)
    zu2 = w.s([zsn, w.inst('elun2')], 'syl', '( %s -> z e. ( ran y u. { z } ) )' % big)
    zr = w.s([zu2, rn2], 'eleqtrrd', '( %s -> z e. ran %s )' % (big, YZ))
    cgw, _ = w.wcongr('( # ` w ) <_ K', {'w': 'z'}, 'w = z', {'w': w.s([], 'id', '( w = z -> w = z )')})
    lz = w.s([cgw, hb, zr], 'rspcdva', '( %s -> ( # ` z ) <_ K )' % big)
    g1 = w.s([yy, zs, w.inst('gsumgamccat')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (big, GS(YZ), GS('y'), GS('<" z ">')))
    g2 = w.s([zz, w.inst('gsumgams1')], 'syl', '( %s -> %s = z )' % (big, GS('<" z ">')))
    g3 = w.s([g2], 'oveq2d', '( %s -> ( %s ++ %s ) = ( %s ++ z ) )' % (big, GS('y'), GS('<" z ">'), GS('y')))
    g4 = w.s([g1, g3], 'eqtrd', '( %s -> %s = ( %s ++ z ) )' % (big, GS(YZ), GS('y')))
    g5 = w.s([g4], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` ( %s ++ z ) ) )' % (big, GS(YZ), GS('y')))
    gy = w.s([yy, w.inst('gsumgamcl')], 'syl', '( %s -> %s e. %s )' % (big, GS('y'), WG))
    g6 = w.s([gy, zz, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` ( %s ++ z ) ) = ( ( # ` %s ) + ( # ` z ) ) )' % (big, GS('y'), GS('y')))
    l6 = w.s([g5, g6], 'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` z ) ) )' % (big, GS(YZ), GS('y')))
    ly = w.s([yy, zs, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` y ) + ( # ` <" z "> ) ) )' % (big, YZ))
    szb = w.s([w.s([w.s([], 's1len', '( # ` <" z "> ) = 1')], 'oveq2i', '( ( # ` y ) + ( # ` <" z "> ) ) = ( ( # ` y ) + 1 )')],
              'a1i', '( %s -> ( ( # ` y ) + ( # ` <" z "> ) ) = ( ( # ` y ) + 1 ) )' % big)
    ly2 = w.s([ly, szb], 'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` y ) + 1 ) )' % (big, YZ))
    ly3 = w.s([ly2], 'oveq1d', '( %s -> ( ( # ` %s ) x. K ) = ( ( ( # ` y ) + 1 ) x. K ) )' % (big, YZ))
    ny = w.s([yy, w.inst('lencl')], 'syl', '( %s -> ( # ` y ) e. NN0 )' % big)
    nz = w.s([zz, w.inst('lencl')], 'syl', '( %s -> ( # ` z ) e. NN0 )' % big)
    ne = w.s([gy, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (big, GS('y')))
    cl = Closure(w, big, {'( # ` y )': ny, '( # ` z )': nz, '( # ` %s )' % GS('y'): ne, 'K': kk})
    y0 = w.s([ny], 'nn0ge0d', '( %s -> 0 <_ ( # ` y ) )' % big)
    ar = linarith(w, big, [ihc, lz, y0], '( ( # ` %s ) + ( # ` z ) ) <_ ( ( ( # ` y ) + 1 ) x. K )' % GS('y'), closure=cl, products=True)
    fin = w.s([l6, ly3, ar], '3brtr4d', '( %s -> ( # ` %s ) <_ ( ( # ` %s ) x. K ) )' % (big, GS(YZ), YZ))
    ex1 = w.s([fin], 'ex', '( ( %s /\\ %s ) -> %s )' % (yz, PROP('y'), PROP(YZ)))
    ex2 = w.s([ex1], 'ex', '( %s -> ( %s -> %s ) )' % (yz, PROP('y'), PROP(YZ)))
    ind = w.s([q1, q2, q3, q4, bs, ex2], 'wrdind', '( W e. %s -> %s )' % (WWG, PROP('W')))
    w.qed([ind], '3impib', '( %s -> ( # ` %s ) <_ ( ( # ` W ) x. K ) )' % (ph, GS('W')))
    return w.run()


SQ = lambda T, L: '( encSlot o. ( %s |` ( 0 ..^ %s ) ) )' % (T, L)


def ttabtbav():
    lab = 'ttabtbav'
    w = W(lab, 'Value of ~ df-tm2enctbla .  Lean: ` encTblAsc ` .')
    ph = '( L e. NN0 /\\ T e. Tbl )'
    R, G, S = GS(SQ('t', 'l')), GS(SQ('t', 'L')), GS(SQ('T', 'L'))
    h1, n1 = w.congr(R, {'l': 'L'}, 'l = L', {'l': w.s([], 'id', '( l = L -> l = L )')})
    assert n1 == G, n1
    h2, n2 = w.congr(G, {'t': 'T'}, 't = T', {'t': w.s([], 'id', '( t = T -> t = T )')})
    assert n2 == S, n2
    df = w.s([], 'df-tm2enctbla', 'encTblAsc = ( l e. NN0 , t e. Tbl |-> %s )' % R)
    ov = w.s([h1, h2, df], 'ovmpog', '( ( L e. NN0 /\\ T e. Tbl /\\ %s e. _V ) -> ( L encTblAsc T ) = %s )' % (S, S))
    sv = w.s([w.s([], 'ovex', '%s e. _V' % S)], 'a1i', '( %s -> %s e. _V )' % (ph, S))
    w.qed([w.s([], 'simpl', '( %s -> L e. NN0 )' % ph), w.s([], 'simpr', '( %s -> T e. Tbl )' % ph), sv, ov], 'syl3anc',
          '( %s -> ( L encTblAsc T ) = %s )' % (ph, S))
    return w.run()


def ttabtbll():
    lab = 'ttabtbll'
    w = W(lab, 'The length of the DP table on ` [ 0 , L ) ` on a stack, every slot bounded.  Lean: '
               '` encTblAsc_length_le ` (the bound over every residue, blueprint D9, used below ` L ` ).')
    TB = TBBI('( T ` d )', 'N', 'B')
    ph = '( ( L e. NN0 /\\ T e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 ) /\\ A. d e. NN0 %s )' % TB
    G = '( T |` ( 0 ..^ L ) )'
    S = SQ('T', 'L')
    IX = '( 0 ..^ L )'
    lt = w.s([], 'simp1', '( %s -> ( L e. NN0 /\\ T e. Tbl ) )' % ph)
    lL = w.s([lt], 'simpld', '( %s -> L e. NN0 )' % ph)
    tT = w.s([lt], 'simprd', '( %s -> T e. Tbl )' % ph)
    nb = w.s([], 'simp2', '( %s -> ( N e. NN0 /\\ B e. NN0 ) )' % ph)
    nN = w.s([nb], 'simpld', '( %s -> N e. NN0 )' % ph)
    nB = w.s([nb], 'simprd', '( %s -> B e. NN0 )' % ph)
    tb = w.s([], 'simp3', '( %s -> A. d e. NN0 %s )' % (ph, TB))
    tf = w.s([tT, w.inst('tblf')], 'syl', '( %s -> T : NN0 --> %s )' % (ph, DJ))
    ss0 = w.s([w.s([], '0nn0', '0 e. NN0'), w.s([], 'fzossnn0', '( 0 e. NN0 -> %s C_ NN0 )' % IX)], 'ax-mp', '%s C_ NN0' % IX)
    ss = w.s([ss0], 'a1i', '( %s -> %s C_ NN0 )' % (ph, IX))
    gf = w.s([tf, ss], 'fssresd', '( %s -> %s : %s --> %s )' % (ph, G, IX, DJ))
    sff = w.s([w.s([], 'ttabslotf', 'encSlot : %s --> %s' % (DJ, WG))], 'a1i', '( %s -> encSlot : %s --> %s )' % (ph, DJ, WG))
    sf = w.s([sff, gf, w.inst('fco')], 'syl2anc', '( %s -> %s : %s --> %s )' % (ph, S, IX, WG))
    sw = w.s([sf, w.inst('iswrdi')], 'syl', "( %s -> %s e. Word %s )" % (ph, S, WG))
    sl = w.s([lL, sf, w.inst('fnfzo0hash')], 'syl2anc', '( %s -> ( # ` %s ) = L )' % (ph, S))
    # the slots
    p = '( %s /\\ y e. %s )' % (ph, IX)
    yi = w.s([], 'simpr', '( %s -> y e. %s )' % (p, IX))
    y0 = w.s([yi, w.inst('elfzonn0')], 'syl', '( %s -> y e. NN0 )' % p)
    gfp = w.s([gf], 'adantr', '( %s -> %s : %s --> %s )' % (p, G, IX, DJ))
    sv = w.s([gfp, yi, w.inst('fvco3')], 'syl2anc', '( %s -> ( %s ` y ) = ( encSlot ` ( %s ` y ) ) )' % (p, S, G))
    gv = w.s([yi, w.inst('fvres')], 'syl', '( %s -> ( %s ` y ) = ( T ` y ) )' % (p, G))
    sv2 = w.s([sv, w.s([gv], 'fveq2d', '( %s -> ( encSlot ` ( %s ` y ) ) = ( encSlot ` ( T ` y ) ) )' % (p, G))], 'eqtrd',
              '( %s -> ( %s ` y ) = ( encSlot ` ( T ` y ) ) )' % (p, S))
    ty = w.s([w.s([tT], 'adantr', '( %s -> T e. Tbl )' % p), y0, w.inst('tblfv')], 'syl2anc', '( %s -> ( T ` y ) e. %s )' % (p, DJ))
    cgd, ny = w.wcongr(TB, {'d': 'y'}, 'd = y', {'d': w.s([], 'id', '( d = y -> d = y )')})
    TY = TBBI('( T ` y )', 'N', 'B')
    assert ny == TY, ny
    tbi = w.s([cgd, w.s([tb], 'adantr', '( %s -> A. d e. NN0 %s )' % (p, TB)), y0], 'rspcdva', '( %s -> %s )' % (p, TY))
    nbp = w.s([nb], 'adantr', '( %s -> ( N e. NN0 /\\ B e. NN0 ) )' % p)
    ln = w.s([ty, nbp, tbi, w.inst('ttabslen')], 'syl3anc', '( %s -> ( # ` ( encSlot ` ( T ` y ) ) ) <_ %s )' % (p, KB))
    lsy = w.s([w.s([sv2], 'fveq2d', '( %s -> ( # ` ( %s ` y ) ) = ( # ` ( encSlot ` ( T ` y ) ) ) )' % (p, S)), ln], 'eqbrtrd',
              '( %s -> ( # ` ( %s ` y ) ) <_ %s )' % (p, S, KB))
    ra = w.s([lsy], 'ralrimiva', '( %s -> A. y e. %s ( # ` ( %s ` y ) ) <_ %s )' % (ph, IX, S, KB))
    hw = w.s([w.s([], 'fveq2', '( w = ( %s ` y ) -> ( # ` w ) = ( # ` ( %s ` y ) ) )' % (S, S))], 'breq1d',
             '( w = ( %s ` y ) -> ( ( # ` w ) <_ %s <-> ( # ` ( %s ` y ) ) <_ %s ) )' % (S, KB, S, KB))
    rr = w.s([hw], 'ralrn', '( %s Fn %s -> ( A. w e. ran %s ( # ` w ) <_ %s <-> A. y e. %s ( # ` ( %s ` y ) ) <_ %s ) )'
             % (S, IX, S, KB, IX, S, KB))
    fn = w.s([sf], 'ffnd', '( %s -> %s Fn %s )' % (ph, S, IX))
    rw = w.s([ra, w.s([fn, rr], 'syl', '( %s -> ( A. w e. ran %s ( # ` w ) <_ %s <-> A. y e. %s ( # ` ( %s ` y ) ) <_ %s ) )'
                      % (ph, S, KB, IX, S, KB))], 'mpbird', '( %s -> A. w e. ran %s ( # ` w ) <_ %s )' % (ph, S, KB))
    c = Closure(w, ph, {'N': nN, 'B': nB, 'L': lL})
    kn = c.mem(KB, 'NN0')
    gb = w.s([sw, kn, rw, w.inst('ttabgsln')], 'syl3anc', '( %s -> ( # ` %s ) <_ ( ( # ` %s ) x. %s ) )' % (ph, GS(S), S, KB))
    gb2 = w.s([sl], 'oveq1d', '( %s -> ( ( # ` %s ) x. %s ) = ( L x. %s ) )' % (ph, S, KB, KB))
    gb3 = w.s([gb, gb2], 'breqtrd', '( %s -> ( # ` %s ) <_ ( L x. %s ) )' % (ph, GS(S), KB))
    val = w.s([lL, tT, w.inst('ttabtbav')], 'syl2anc', '( %s -> ( L encTblAsc T ) = %s )' % (ph, GS(S)))
    v2 = w.s([val], 'fveq2d', '( %s -> ( # ` ( L encTblAsc T ) ) = ( # ` %s ) )' % (ph, GS(S)))
    w.qed([v2, gb3], 'eqbrtrd', '( %s -> ( # ` ( L encTblAsc T ) ) <_ ( L x. %s ) )' % (ph, KB))
    return w.run()


LPT = '( L e. NN /\\ P e. NN0 /\\ T e. Tbl )'
PHR = '( %s /\\ ( B e. NN0 /\\ P < ( 2 ^ B ) ) /\\ %s )' % (LPT, TBBR('T', 'c'))
TD = lambda X: '( %s ` %s )' % (T2, X)
TBRI = lambda T, X: '( ( %s ` %s ) =/= %s -> %s )' % (T, X, NONE, RNG('( %s ` %s )' % (T, X)))


def ttabtbdr():
    lab = 'ttabtbdr'
    w = W(lab, 'The entries of a table after a DP step stay below ` 2 ^ B ` when the new prime and the old '
               'entries do (the entry half of Lean\'s ` tblBounded_dpStep ` , from ~ dpstepcases ).')
    a = '( %s /\\ D e. NN0 )' % PHR
    b = '( %s /\\ %s =/= %s )' % (a, TD('D'), NONE)
    G = RNG(TD('D'))
    X2 = '( 2nd ` %s )' % TD('D')
    Q = lambda X: 'A. q e. %s q < ( 2 ^ B )' % X
    a1 = w.s([], 'simpl', '( %s -> %s )' % (a, PHR))
    a2 = w.s([a1], 'simp1d', '( %s -> %s )' % (a, LPT))
    aL = w.s([a2], 'simp1d', '( %s -> L e. NN )' % a)
    aP = w.s([a2], 'simp2d', '( %s -> P e. NN0 )' % a)
    aT = w.s([a2], 'simp3d', '( %s -> T e. Tbl )' % a)
    aBP = w.s([a1], 'simp2d', '( %s -> ( B e. NN0 /\\ P < ( 2 ^ B ) ) )' % a)
    aPl = w.s([aBP], 'simprd', '( %s -> P < ( 2 ^ B ) )' % a)
    aTB = w.s([a1], 'simp3d', '( %s -> %s )' % (a, TBBR('T', 'c')))
    aD = w.s([], 'simpr', '( %s -> D e. NN0 )' % a)
    lift = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (b, f))
    bL, bP, bT = lift(aL, 'L e. NN'), lift(aP, 'P e. NN0'), lift(aT, 'T e. Tbl')
    bPl, bTB, bD = lift(aPl, 'P < ( 2 ^ B )'), lift(aTB, TBBR('T', 'c')), lift(aD, 'D e. NN0')
    bne = w.s([], 'simpr', '( %s -> %s =/= %s )' % (b, TD('D'), NONE))
    A1 = '( T ` D ) = %s' % TD('D')
    A2 = '( D = ( P mod L ) /\\ %s = <" P "> )' % X2
    Y = '( 2nd ` ( T ` r ) )'
    BODY = '( ( ( T ` r ) =/= %s /\\ D = ( ( r x. P ) mod L ) ) /\\ %s = ( <" P "> ++ %s ) )' % (NONE, X2, Y)
    A3 = 'E. r e. ( 0 ..^ L ) %s' % BODY
    DISJ = '( %s \\/ ( %s \\/ %s ) )' % (A1, A2, A3)
    h1 = w.s([w.s([bL, bP], 'jca', '( %s -> ( L e. NN /\\ P e. NN0 ) )' % b), bT], 'jca', '( %s -> ( ( L e. NN /\\ P e. NN0 ) /\\ T e. Tbl ) )' % b)
    h2 = w.s([bD, bne], 'jca', '( %s -> ( D e. NN0 /\\ %s =/= %s ) )' % (b, TD('D'), NONE))
    cs = w.s([h1, h2, w.inst('dpstepcases')], 'syl2anc', '( %s -> %s )' % (b, DISJ))

    def cinst(X):
        st, new = w.wcongr(TBRI('T', 'c'), {'c': X}, 'c = %s' % X, {'c': w.s([], 'id', '( c = %s -> c = %s )' % (X, X))})
        assert new == TBRI('T', X), new
        return st
    # case A1
    b1 = '( %s /\\ %s )' % (b, A1)
    e1 = w.s([], 'simpr', '( %s -> %s )' % (b1, A1))
    ne1 = w.s([e1, w.s([bne], 'adantr', '( %s -> %s =/= %s )' % (b1, TD('D'), NONE))], 'eqnetrd', '( %s -> ( T ` D ) =/= %s )' % (b1, NONE))
    tb1 = w.s([cinst('D'), w.s([bTB], 'adantr', '( %s -> %s )' % (b1, TBBR('T', 'c'))), w.s([bD], 'adantr', '( %s -> D e. NN0 )' % b1)],
              'rspcdva', '( %s -> %s )' % (b1, TBRI('T', 'D')))
    r1 = w.s([ne1, tb1], 'mpd', '( %s -> %s )' % (b1, RNG('( T ` D )')))
    eq1 = w.s([w.s([e1], 'fveq2d', '( %s -> ( 2nd ` ( T ` D ) ) = %s )' % (b1, X2))], 'rneqd', '( %s -> ran ( 2nd ` ( T ` D ) ) = ran %s )' % (b1, X2))
    rq1 = w.s([eq1], 'raleqdv', '( %s -> ( %s <-> %s ) )' % (b1, RNG('( T ` D )'), G))
    k1 = w.s([w.s([r1, rq1], 'mpbid', '( %s -> %s )' % (b1, G))], 'ex', '( %s -> ( %s -> %s ) )' % (b, A1, G))
    # case A2
    b2 = '( %s /\\ %s )' % (b, A2)
    e2 = w.s([w.s([], 'simpr', '( %s -> %s )' % (b2, A2))], 'simprd', '( %s -> %s = <" P "> )' % (b2, X2))
    bP2 = w.s([bP], 'adantr', '( %s -> P e. NN0 )' % b2)
    rr2 = w.s([w.s([e2], 'rneqd', '( %s -> ran %s = ran <" P "> )' % (b2, X2)),
               w.s([bP2, w.inst('s1rn')], 'syl', '( %s -> ran <" P "> = { P } )' % b2)], 'eqtrd', '( %s -> ran %s = { P } )' % (b2, X2))
    rq2 = w.s([rr2], 'raleqdv', '( %s -> ( %s <-> %s ) )' % (b2, G, Q('{ P }')))
    sng = w.s([w.s([], 'breq1', '( q = P -> ( q < ( 2 ^ B ) <-> P < ( 2 ^ B ) ) )')], 'ralsng',
              '( P e. NN0 -> ( %s <-> P < ( 2 ^ B ) ) )' % Q('{ P }'))
    rs2 = w.s([bP2, sng], 'syl', '( %s -> ( %s <-> P < ( 2 ^ B ) ) )' % (b2, Q('{ P }')))
    bi2 = w.s([rq2, rs2], 'bitrd', '( %s -> ( %s <-> P < ( 2 ^ B ) ) )' % (b2, G))
    k2 = w.s([w.s([w.s([bPl], 'adantr', '( %s -> P < ( 2 ^ B ) )' % b2), bi2], 'mpbird', '( %s -> %s )' % (b2, G))], 'ex',
             '( %s -> ( %s -> %s ) )' % (b, A2, G))
    # case A3
    br = '( %s /\\ r e. ( 0 ..^ L ) )' % b
    c3 = '( %s /\\ %s )' % (br, BODY)
    ll = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (c3, f))
    ri = w.s([], 'simplr', '( %s -> r e. ( 0 ..^ L ) )' % c3)
    r0 = w.s([ri, w.inst('elfzonn0')], 'syl', '( %s -> r e. NN0 )' % c3)
    bd = w.s([], 'simpr', '( %s -> %s )' % (c3, BODY))
    nr = w.s([w.s([bd], 'simpld', '( %s -> ( ( T ` r ) =/= %s /\\ D = ( ( r x. P ) mod L ) ) )' % (c3, NONE))], 'simpld',
             '( %s -> ( T ` r ) =/= %s )' % (c3, NONE))
    ex3 = w.s([bd], 'simprd', '( %s -> %s = ( <" P "> ++ %s ) )' % (c3, X2, Y))
    tbr = w.s([cinst('r'), ll(bTB, TBBR('T', 'c')), r0], 'rspcdva', '( %s -> %s )' % (c3, TBRI('T', 'r')))
    rY = w.s([nr, tbr], 'mpd', '( %s -> %s )' % (c3, RNG('( T ` r )')))
    cP = ll(bP, 'P e. NN0')
    tr = w.s([ll(bT, 'T e. Tbl'), r0, w.inst('tblfv')], 'syl2anc', '( %s -> ( T ` r ) e. %s )' % (c3, DJ))
    yw = w.s([tr, w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (c3, Y))
    ps1 = w.s([cP], 's1cld', '( %s -> <" P "> e. Word NN0 )' % c3)
    rn = w.s([ps1, yw, w.inst('ccatrn')], 'syl2anc', '( %s -> ran ( <" P "> ++ %s ) = ( ran <" P "> u. ran %s ) )' % (c3, Y, Y))
    rn2 = w.s([w.s([cP, w.inst('s1rn')], 'syl', '( %s -> ran <" P "> = { P } )' % c3)], 'uneq1d',
              '( %s -> ( ran <" P "> u. ran %s ) = ( { P } u. ran %s ) )' % (c3, Y, Y))
    rx = w.s([w.s([w.s([ex3], 'rneqd', '( %s -> ran %s = ran ( <" P "> ++ %s ) )' % (c3, X2, Y)), rn], 'eqtrd',
                  '( %s -> ran %s = ( ran <" P "> u. ran %s ) )' % (c3, X2, Y)), rn2], 'eqtrd',
             '( %s -> ran %s = ( { P } u. ran %s ) )' % (c3, X2, Y))
    U = '( { P } u. ran %s )' % Y
    rq3 = w.s([rx], 'raleqdv', '( %s -> ( %s <-> %s ) )' % (c3, G, Q(U)))
    ru = w.s([], 'ralunb', '( %s <-> ( %s /\\ %s ) )' % (Q(U), Q('{ P }'), Q('ran %s' % Y)))
    rs3 = w.s([cP, sng], 'syl', '( %s -> ( %s <-> P < ( 2 ^ B ) ) )' % (c3, Q('{ P }')))
    pp = w.s([ll(bPl, 'P < ( 2 ^ B )'), rs3], 'mpbird', '( %s -> %s )' % (c3, Q('{ P }')))
    cj3 = w.s([pp, rY], 'jca', '( %s -> ( %s /\\ %s ) )' % (c3, Q('{ P }'), Q('ran %s' % Y)))
    u3 = w.s([cj3, ru], 'sylibr', '( %s -> %s )' % (c3, Q(U)))
    g3 = w.s([u3, rq3], 'mpbird', '( %s -> %s )' % (c3, G))
    k3a = w.s([g3], 'ex', '( %s -> ( %s -> %s ) )' % (br, BODY, G))
    k3 = w.s([k3a], 'rexlimdva', '( %s -> ( %s -> %s ) )' % (b, A3, G))
    j23 = w.s([k2, k3], 'jaod', '( %s -> ( ( %s \\/ %s ) -> %s ) )' % (b, A2, A3, G))
    j = w.s([k1, j23], 'jaod', '( %s -> ( %s -> %s ) )' % (b, DISJ, G))
    fin = w.s([cs, j], 'mpd', '( %s -> %s )' % (b, G))
    w.qed([fin], 'ex', '( %s -> ( %s =/= %s -> %s ) )' % (a, TD('D'), NONE, G))
    return w.run()


def ttabtbdp():
    lab = 'ttabtbdp'
    w = W(lab, 'A DP step raises the slot length bound by one and keeps the entries below ` 2 ^ B ` .  Lean: '
               '` tblBounded_dpStep ` (over every residue, blueprint D9; the length half is ~ tblbnds ).')
    TB = 'A. d e. NN0 %s' % TBBI('( T ` d )', 'N', 'B')
    ph = '( %s /\\ ( N e. NN0 /\\ B e. NN0 /\\ P < ( 2 ^ B ) ) /\\ %s )' % (LPT, TB)
    X = '( T ` d )'
    H = '( # ` ( 2nd ` %s ) )' % X
    s1 = w.s([], 'simp3', '( %s -> %s )' % (ph, TB))
    il = w.s([w.s([], 'simpl', '( ( %s <_ N /\\ %s ) -> %s <_ N )' % (H, RNG(X), H))], 'imim2i',
             '( %s -> ( %s =/= %s -> %s <_ N ) )' % (TBBI(X, 'N', 'B'), X, NONE, H))
    len = w.s([il], 'ralimi', '( %s -> %s )' % (TB, TBBL('T', 'N')))
    ir = w.s([w.s([], 'simpr', '( ( %s <_ N /\\ %s ) -> %s )' % (H, RNG(X), RNG(X)))], 'imim2i',
             '( %s -> %s )' % (TBBI(X, 'N', 'B'), TBRI('T', 'd')))
    rng = w.s([ir], 'ralimi', '( %s -> %s )' % (TB, TBBR('T', 'd')))
    hc, nc = w.wcongr(TBRI('T', 'd'), {'d': 'c'}, 'd = c', {'d': w.s([], 'id', '( d = c -> d = c )')})
    assert nc == TBRI('T', 'c'), nc
    cbv = w.s([hc], 'cbvralvw', '( %s <-> %s )' % (TBBR('T', 'd'), TBBR('T', 'c')))
    p1 = w.s([], 'simp1', '( %s -> %s )' % (ph, LPT))
    p2 = w.s([], 'simp2', '( %s -> ( N e. NN0 /\\ B e. NN0 /\\ P < ( 2 ^ B ) ) )' % ph)
    nN = w.s([p2], 'simp1d', '( %s -> N e. NN0 )' % ph)
    lb = w.s([nN, w.s([s1, len], 'syl', '( %s -> %s )' % (ph, TBBL('T', 'N')))], 'jca', '( %s -> ( N e. NN0 /\\ %s ) )' % (ph, TBBL('T', 'N')))
    tl = w.s([p1, lb, w.inst('tblbnds')], 'syl2anc', '( %s -> %s )' % (ph, TBBL(T2, '( N + 1 )')))
    bp = w.s([p2, w.inst('3simpc')], 'syl', '( %s -> ( B e. NN0 /\\ P < ( 2 ^ B ) ) )' % ph)
    rc = w.s([w.s([s1, rng], 'syl', '( %s -> %s )' % (ph, TBBR('T', 'd'))), cbv], 'sylib', '( %s -> %s )' % (ph, TBBR('T', 'c')))
    pr = w.s([p1, bp, rc], '3jca', '( %s -> %s )' % (ph, PHR))
    hi = w.s([], 'ttabtbdr', '( ( %s /\\ d e. NN0 ) -> %s )' % (PHR, TBRI(T2, 'd')))
    ra = w.s([hi], 'ralrimiva', '( %s -> %s )' % (PHR, TBBR(T2, 'd')))
    tr = w.s([pr, ra], 'syl', '( %s -> %s )' % (ph, TBBR(T2, 'd')))
    both = w.s([tl, tr], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, TBBL(T2, '( N + 1 )'), TBBR(T2, 'd')))
    X2 = TD('d')
    XA = '%s =/= %s' % (X2, NONE)
    LN = '( # ` ( 2nd ` %s ) ) <_ ( N + 1 )' % X2
    RG = RNG(X2)
    r26 = w.s([], 'r19.26', '( A. d e. NN0 ( ( %s -> %s ) /\\ ( %s -> %s ) ) <-> ( %s /\\ %s ) )'
              % (XA, LN, XA, RG, TBBL(T2, '( N + 1 )'), TBBR(T2, 'd')))
    jc = w.s([w.s([], 'jcab', '( ( %s -> ( %s /\\ %s ) ) <-> ( ( %s -> %s ) /\\ ( %s -> %s ) ) )' % (XA, LN, RG, XA, LN, XA, RG))],
             'ralbii', '( A. d e. NN0 ( %s -> ( %s /\\ %s ) ) <-> A. d e. NN0 ( ( %s -> %s ) /\\ ( %s -> %s ) ) )'
             % (XA, LN, RG, XA, LN, XA, RG))
    bi = w.s([jc, r26], 'bitri', '( A. d e. NN0 ( %s -> ( %s /\\ %s ) ) <-> ( %s /\\ %s ) )'
             % (XA, LN, RG, TBBL(T2, '( N + 1 )'), TBBR(T2, 'd')))
    w.qed([both, bi], 'sylibr', '( %s -> A. d e. NN0 ( %s -> ( %s /\\ %s ) ) )' % (ph, XA, LN, RG))
    return w.run()


ALL = ['ttabopt', 'ttabslotf', 'ttabslotv', 'ttabtbb0', 'ttabtbbm', 'ttabkethd', 'ttabslotk',
       'ttabslen', 'ttabgsln', 'ttabtbav', 'ttabtbll', 'ttabtbdr', 'ttabtbdp']

if __name__ == '__main__':
    for l in ALL:
        if want(l):
            if not globals()[l]():
                sys.exit(1)
