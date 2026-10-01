"""T6: the head of a list segment, the drop/take algebra of lists, and
`encList` with its ℕ-level bridge (blueprint 3.1, second half)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2lencbhd0():
    w = W('tm2lencbhd0', 'The head of an empty list segment on a stack is ` bra ` .  One direction of Lean\'s ` head?_encListB_append ` .')
    A = 'R e. %s' % WG
    v = closedw(w, A, 'tm2lencb0', '%s = <" 2 ">' % ENCB('(/)'))
    o = w.s([v], 'oveq1d', '( %s -> ( %s ++ R ) = ( <" 2 "> ++ R ) )' % (A, ENCB('(/)')))
    f = w.s([o], 'fveq1d', '( %s -> ( ( %s ++ R ) ` 0 ) = ( ( <" 2 "> ++ R ) ` 0 ) )' % (A, ENCB('(/)')))
    g = gamlet(w, A, '2')
    i = w.s([], 'id', '( %s -> R e. %s )' % (A, WG))
    h = w.s([g, i, w.inst('ccats1fv0')], 'syl2anc', '( %s -> ( ( <" 2 "> ++ R ) ` 0 ) = 2 )' % A)
    w.qed([f, h], 'eqtrd', '( %s -> ( ( %s ++ R ) ` 0 ) = 2 )' % (A, ENCB('(/)')))
    return w.run()


def tm2lencbhd1():
    w = W('tm2lencbhd1', 'The head of a nonempty list segment on a stack is a bit or a comma, never ` bra ` .  The other direction of Lean\'s ` head?_encListB_append ` , stated without a letter comparison (blueprint decision 3).')
    A = '( L e. %s /\\ R e. %s /\\ L =/= (/) )' % (WWB, WG)
    l1 = w.s([], 'simp1', '( %s -> L e. %s )' % (A, WWB))
    r1 = w.s([], 'simp2', '( %s -> R e. %s )' % (A, WG))
    n1 = w.s([], 'simp3', '( %s -> L =/= (/) )' % A)
    HD = '( L ` 0 )'; TL = '( L substr <. 1 , ( # ` L ) >. )'
    e = w.s([l1, n1, w.inst('wrdhdtl')], 'syl2anc', '( %s -> L = ( <" %s "> ++ %s ) )' % (A, HD, TL))
    # the head entry and the tail list
    lv = w.s([l1], 'elexd', '( %s -> L e. _V )' % A)
    h0 = w.s([lv, w.inst('hashneq0')], 'syl', '( %s -> ( 0 < ( # ` L ) <-> L =/= (/) ) )' % A)
    hp = w.s([h0, n1], 'mpbird', '( %s -> 0 < ( # ` L ) )' % A)
    ln = w.s([l1, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % A)
    lnn = w.s([ln, hp, w.inst('elnnnn0b')], 'sylanbrc', '( %s -> ( # ` L ) e. NN )' % A)
    z0 = w.s([lnn, w.inst('lbfzo0')], 'sylibr', '( %s -> 0 e. ( 0 ..^ ( # ` L ) ) )' % A)
    hd = w.s([l1, z0, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (A, HD, WB))
    tl = w.s([l1, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (A, TL, WWB))
    c = w.s([hd, tl, w.inst('tm2lencbcons')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB('( <" %s "> ++ %s )' % (HD, TL)), HD, ENCB(TL)))
    e2 = w.s([e], 'fveq2d', '( %s -> %s = %s )' % (A, ENCB('L'), ENCB('( <" %s "> ++ %s )' % (HD, TL))))
    e3 = w.s([e2, c], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB('L'), HD, ENCB(TL)))
    # reassociate: ( ( HD ++ <" 4 "> ) ++ ( ENCB(TL) ++ R ) )
    hg = wbtog(w, A, HD, hd)
    c4 = s1g(w, A, '4')
    et = w.s([tl, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (A, ENCB(TL), WG))
    V = '( %s ++ <" 4 "> )' % HD
    Z = '( %s ++ R )' % ENCB(TL)
    a1 = w.s([hg, c4, et, w.inst('ccatass')], 'syl3anc', '( %s -> ( %s ++ %s ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (A, V, ENCB(TL), HD, ENCB(TL)))
    e4 = w.s([e3, a1], 'eqtr4d', '( %s -> %s = ( %s ++ %s ) )' % (A, ENCB('L'), V, ENCB(TL)))
    e5 = w.s([e4], 'oveq1d', '( %s -> ( %s ++ R ) = ( ( %s ++ %s ) ++ R ) )' % (A, ENCB('L'), V, ENCB(TL)))
    vg = ccatg(w, A, HD, '<" 4 ">', hg, c4)
    a2 = w.s([vg, et, r1, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ R ) = ( %s ++ %s ) )' % (A, V, ENCB(TL), V, Z))
    e6 = w.s([e5, a2], 'eqtrd', '( %s -> ( %s ++ R ) = ( %s ++ %s ) )' % (A, ENCB('L'), V, Z))
    f = w.s([e6], 'fveq1d', '( %s -> ( ( %s ++ R ) ` 0 ) = ( ( %s ++ %s ) ` 0 ) )' % (A, ENCB('L'), V, Z))
    # V is a word over B4 of positive length
    b1 = w.s([], 'ssun1', '%s C_ %s' % (BITS, B4))
    b1w = w.s([b1, w.inst('sswrd')], 'ax-mp', '%s C_ Word %s' % (WB, B4))
    hb = w.s([b1w, hd], 'sselid', '( %s -> %s e. Word %s )' % (A, HD, B4))
    f4 = w.s([], 'snidg', '( 4 e. _V -> 4 e. { 4 } )')
    f4v = w.s([], '4re', '4 e. RR'); f4x = w.s([f4v], 'elexi', '4 e. _V')
    f4s = w.s([f4x, f4], 'ax-mp', '4 e. { 4 }')
    f4b = w.s([f4s, w.inst('elun2')], 'ax-mp', '4 e. %s' % B4)
    f4a = w.s([f4b], 'a1i', '( %s -> 4 e. %s )' % (A, B4))
    vb = w.s([hb, f4a, w.inst('ccatws1cl')], 'syl2anc', '( %s -> %s e. Word %s )' % (A, V, B4))
    vl = w.s([hb, w.inst('ccatws1len')], 'syl', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (A, V, HD))
    hn = w.s([hd, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (A, HD))
    hn1 = w.s([hn, w.inst('nn0p1nn')], 'syl', '( %s -> ( ( # ` %s ) + 1 ) e. NN )' % (A, HD))
    vn = w.s([vl, hn1], 'eqeltrd', '( %s -> ( # ` %s ) e. NN )' % (A, V))
    vp = w.s([vn, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` %s ) )' % (A, V))
    zg = ccatg(w, A, ENCB(TL), 'R', et, r1)
    vgg = ccatg(w, A, HD, '<" 4 ">', hg, c4)
    f2 = w.s([vgg, zg, vp, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ` 0 ) = ( %s ` 0 ) )' % (A, V, Z, V))
    z0v = w.s([vn, w.inst('lbfzo0')], 'sylibr', '( %s -> 0 e. ( 0 ..^ ( # ` %s ) ) )' % (A, V))
    v0 = w.s([vb, z0v, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( %s ` 0 ) e. %s )' % (A, V, B4))
    f3 = w.s([f, f2], 'eqtrd', '( %s -> ( ( %s ++ R ) ` 0 ) = ( %s ` 0 ) )' % (A, ENCB('L'), V))
    w.qed([f3, v0], 'eqeltrd', '( %s -> ( ( %s ++ R ) ` 0 ) e. %s )' % (A, ENCB('L'), B4))
    return w.run()


def tm2ldrop():
    w = W('tm2ldrop', 'Dropping ` J ` letters of a word: the ` J ` -th letter, then the rest.  Lean: ` List.drop_eq_getElem_cons ` .')
    A = '( L e. Word V /\\ J e. ( 0 ..^ ( # ` L ) ) )'
    l1 = w.s([], 'simpl', '( %s -> L e. Word V )' % A)
    j1 = w.s([], 'simpr', '( %s -> J e. ( 0 ..^ ( # ` L ) ) )' % A)
    jn = w.s([j1, w.inst('elfzonn0')], 'syl', '( %s -> J e. NN0 )' % A)
    jj = w.s([jn, w.inst('nn0fz0')], 'sylib', '( %s -> J e. ( 0 ... J ) )' % A)
    jj1 = w.s([jj, w.inst('fzp1elp1')], 'syl', '( %s -> ( J + 1 ) e. ( 0 ... ( J + 1 ) ) )' % A)
    # J e. ( 0 ... ( J + 1 ) ) from J e. ( 0 ... J ) : fzelp1
    jjp = w.s([jj, w.inst('fzelp1')], 'syl', '( %s -> J e. ( 0 ... ( J + 1 ) ) )' % A)
    j1l = w.s([j1, w.inst('fzofzp1')], 'syl', '( %s -> ( J + 1 ) e. ( 0 ... ( # ` L ) ) )' % A)
    ln = w.s([l1, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % A)
    ll = w.s([ln, w.inst('nn0fz0')], 'sylib', '( %s -> ( # ` L ) e. ( 0 ... ( # ` L ) ) )' % A)
    t3 = w.s([jjp, j1l, ll], '3jca', '( %s -> ( J e. ( 0 ... ( J + 1 ) ) /\\ ( J + 1 ) e. ( 0 ... ( # ` L ) ) /\\ ( # ` L ) e. ( 0 ... ( # ` L ) ) ) )' % A)
    c = w.s([l1, t3, w.inst('ccatswrd')], 'syl2anc', '( %s -> ( ( L substr <. J , ( J + 1 ) >. ) ++ %s ) = %s )' % (A, DROP('L', '( J + 1 )'), DROP('L', 'J')))
    s = w.s([l1, j1, w.inst('swrds1')], 'syl2anc', '( %s -> ( L substr <. J , ( J + 1 ) >. ) = <" ( L ` J ) "> )' % A)
    o = w.s([s], 'oveq1d', '( %s -> ( ( L substr <. J , ( J + 1 ) >. ) ++ %s ) = ( <" ( L ` J ) "> ++ %s ) )' % (A, DROP('L', '( J + 1 )'), DROP('L', '( J + 1 )')))
    w.qed([c, o], 'eqtr3d', '( %s -> %s = ( <" ( L ` J ) "> ++ %s ) )' % (A, DROP('L', 'J'), DROP('L', '( J + 1 )')))
    return w.run()


def tm2lencbdrop():
    w = W('tm2lencbdrop', 'The list segment from the ` J ` -th entry on: the ` J ` -th entry, a comma, and the segment after it.  Lean: ` List.drop_eq_getElem_cons ` with ` encListB_cons ` , the shape the entry loop reads.')
    A = '( L e. %s /\\ J e. ( 0 ..^ ( # ` L ) ) )' % WWB
    l1 = w.s([], 'simpl', '( %s -> L e. %s )' % (A, WWB))
    j1 = w.s([], 'simpr', '( %s -> J e. ( 0 ..^ ( # ` L ) ) )' % A)
    d = w.s([l1, j1, w.inst('tm2ldrop')], 'syl2anc', '( %s -> %s = ( <" ( L ` J ) "> ++ %s ) )' % (A, DROP('L', 'J'), DROP('L', '( J + 1 )')))
    f = w.s([d], 'fveq2d', '( %s -> %s = %s )' % (A, ENCB(DROP('L', 'J')), ENCB('( <" ( L ` J ) "> ++ %s )' % DROP('L', '( J + 1 )'))))
    lj = w.s([l1, j1, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` J ) e. %s )' % (A, WB))
    dr = w.s([l1, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (A, DROP('L', '( J + 1 )'), WWB))
    c = w.s([lj, dr, w.inst('tm2lencbcons')], 'syl2anc', '( %s -> %s = ( ( L ` J ) ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB('( <" ( L ` J ) "> ++ %s )' % DROP('L', '( J + 1 )')), ENCB(DROP('L', '( J + 1 )'))))
    w.qed([f, c], 'eqtrd', '( %s -> %s = ( ( L ` J ) ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB(DROP('L', 'J')), ENCB(DROP('L', '( J + 1 )'))))
    return w.run()


def tm2ldrop0():
    w = W('tm2ldrop0', 'Dropping no letters.  Lean: ` List.drop_zero ` .')
    A = 'L e. Word V'
    lv = w.s([], 'elex', '( %s -> L e. _V )' % A)
    ln = w.s([], 'lencl', '( %s -> ( # ` L ) e. NN0 )' % A)
    p = w.s([lv, ln, w.inst('pfxval')], 'syl2anc', '( %s -> ( L prefix ( # ` L ) ) = %s )' % (A, DROP('L', '0')))
    i = w.s([], 'pfxid', '( %s -> ( L prefix ( # ` L ) ) = L )' % A)
    w.qed([p, i], 'eqtr3d', '( %s -> %s = L )' % (A, DROP('L', '0')))
    return w.run()


def tm2lpfxs1():
    w = W('tm2lpfxs1', 'The prefix of length ` J + 1 ` : the prefix of length ` J ` followed by the ` J ` -th letter.  Lean: ` take_succ_of_drop_eq_cons ` .')
    A = '( L e. Word V /\\ J e. ( 0 ..^ ( # ` L ) ) )'
    l1 = w.s([], 'simpl', '( %s -> L e. Word V )' % A)
    j1 = w.s([], 'simpr', '( %s -> J e. ( 0 ..^ ( # ` L ) ) )' % A)
    jn = w.s([j1, w.inst('elfzonn0')], 'syl', '( %s -> J e. NN0 )' % A)
    jj = w.s([jn, w.inst('nn0fz0')], 'sylib', '( %s -> J e. ( 0 ... J ) )' % A)
    jjp = w.s([jj, w.inst('fzelp1')], 'syl', '( %s -> J e. ( 0 ... ( J + 1 ) ) )' % A)
    j1l = w.s([j1, w.inst('fzofzp1')], 'syl', '( %s -> ( J + 1 ) e. ( 0 ... ( # ` L ) ) )' % A)
    c = w.s([l1, jjp, j1l, w.inst('ccatpfx')], 'syl3anc', '( %s -> ( %s ++ ( L substr <. J , ( J + 1 ) >. ) ) = %s )' % (A, PFX('L', 'J'), PFX('L', '( J + 1 )')))
    s = w.s([l1, j1, w.inst('swrds1')], 'syl2anc', '( %s -> ( L substr <. J , ( J + 1 ) >. ) = <" ( L ` J ) "> )' % A)
    o = w.s([s], 'oveq2d', '( %s -> ( %s ++ ( L substr <. J , ( J + 1 ) >. ) ) = ( %s ++ <" ( L ` J ) "> ) )' % (A, PFX('L', 'J'), PFX('L', 'J')))
    w.qed([c, o], 'eqtr3d', '( %s -> %s = ( %s ++ <" ( L ` J ) "> ) )' % (A, PFX('L', '( J + 1 )'), PFX('L', 'J')))
    return w.run()


# ---------------------------------------------------------------- encList

def tm2lencval():
    w = W('tm2lencval', 'Value of ` encList ` .  Lean: ` def encList ` (TM/Lists.lean).')
    c1 = w.s([], 'coeq2', '( l = L -> ( %s o. l ) = ( %s o. L ) )' % (PFN, PFN))
    c2 = w.s([c1], 'oveq2d', '( l = L -> %s = %s )' % (FLATN('l'), FLATN('L')))
    c = w.s([c2], 'oveq1d', '( l = L -> ( %s ++ <" 2 "> ) = ( %s ++ <" 2 "> ) )' % (FLATN('l'), FLATN('L')))
    e = w.s([], 'df-tm2lenc', 'encList = ( l e. Word NN0 |-> ( %s ++ <" 2 "> ) )' % FLATN('l'))
    x = w.s([], 'ovex', '( %s ++ <" 2 "> ) e. _V' % FLATN('L'))
    w.qed([c, e, x], 'fvmpt', '( L e. Word NN0 -> %s = ( %s ++ <" 2 "> ) )' % (ENC('L'), FLATN('L')))
    return w.run()


def tm2lenccl():
    w = W('tm2lenccl', "A list of numbers on a stack is a word over ` Gamma' ` .")
    A = 'L e. Word NN0'
    v = w.s([], 'tm2lencval', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENC('L'), FLATN('L')))
    f = w.s([], 'encoutflatcl', '( %s -> %s e. %s )' % (A, FLATN('L'), WG))
    g = gamlet(w, A, '2')
    c = w.s([f, g, w.inst('ccatws1cl')], 'syl2anc', '( %s -> ( %s ++ <" 2 "> ) e. %s )' % (A, FLATN('L'), WG))
    w.qed([v, c], 'eqeltrd', '( %s -> %s e. %s )' % (A, ENC('L'), WG))
    return w.run()


def tm2linclf():
    w = W('tm2linclf', "The inclusion of ` Bool ` in ` Gamma' ` maps into the bit letters.")
    e = w.s([], 'df-inclbool', 'inclBool = ( b e. 2o |-> <. 1 , b >. )')
    A = 'b e. 2o'
    o = w.s([], '1ex', '1 e. _V')
    s = w.s([o, w.inst('snidg')], 'ax-mp', '1 e. { 1 }')
    sa = w.s([s], 'a1i', '( %s -> 1 e. { 1 } )' % A)
    i = w.s([], 'id', '( %s -> b e. 2o )' % A)
    p = w.s([sa, i], 'opelxpd', '( %s -> <. 1 , b >. e. %s )' % (A, BITS))
    w.qed([e, p], 'fmpti', 'inclBool : 2o --> %s' % BITS)
    return w.run()


def tm2lbitf():
    w = W('tm2lbitf', 'The binary encoding of a number is a word of bit letters.')
    e = w.s([], 'df-encnatgam', 'encNatGam = ( n e. NN0 |-> ( inclBool o. ( encodeNat ` n ) ) )')
    A = 'n e. NN0'
    f = closedw(w, A, 'encnatf', 'encodeNat : NN0 --> Word 2o')
    i = w.s([], 'id', '( %s -> n e. NN0 )' % A)
    v = w.s([f, i, w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( encodeNat ` n ) e. Word 2o )' % A)
    g = closedw(w, A, 'tm2linclf', 'inclBool : 2o --> %s' % BITS)
    c = w.s([v, g, w.inst('wrdco')], 'syl2anc', '( %s -> ( inclBool o. ( encodeNat ` n ) ) e. %s )' % (A, WB))
    w.qed([e, c], 'fmpti', 'encNatGam : NN0 --> %s' % WB)
    return w.run()


def tm2lencgam():
    w = W('tm2lencgam', 'The encoded entries of a list of numbers form a list of bit words.  Lean: ` l.map encodeNat ` .')
    A = 'L e. Word NN0'
    i = w.s([], 'id', '( %s -> L e. Word NN0 )' % A)
    f = closedw(w, A, 'tm2lbitf', 'encNatGam : NN0 --> %s' % WB)
    w.qed([i, f, w.inst('wrdco')], 'syl2anc', '( %s -> ( encNatGam o. L ) e. %s )' % (A, WWB))
    return w.run()


def tm2lencpf():
    """( PFW o. encNatGam ) = PFN"""
    w = W('tm2lencpf', 'The entry mapping of ` encList ` is the entry mapping of ` entries ` after the binary encoding.')
    R = '( inclBool o. ( encodeNat ` n ) )'
    RP = '( inclBool o. ( encodeNat ` p ) )'
    A = 'T.'
    e0 = w.s([], 'df-encnatgam', 'encNatGam = ( n e. NN0 |-> %s )' % R)
    c1 = w.s([], 'fveq2', '( n = p -> ( encodeNat ` n ) = ( encodeNat ` p ) )')
    c2 = w.s([c1], 'coeq2d', '( n = p -> %s = %s )' % (R, RP))
    cb = w.s([c2], 'cbvmptv', '( n e. NN0 |-> %s ) = ( p e. NN0 |-> %s )' % (R, RP))
    e1 = w.s([e0, cb], 'eqtri', 'encNatGam = ( p e. NN0 |-> %s )' % RP)
    e1a = w.s([e1], 'a1i', '( %s -> encNatGam = ( p e. NN0 |-> %s ) )' % (A, RP))
    B = '( %s /\\ p e. NN0 )' % A
    p1 = w.s([], 'simpr', '( %s -> p e. NN0 )' % B)
    f = closedw(w, B, 'encnatf', 'encodeNat : NN0 --> Word 2o')
    v = w.s([f, p1, w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( encodeNat ` p ) e. Word 2o )' % B)
    g = closedw(w, B, 'tm2linclf', 'inclBool : 2o --> %s' % BITS)
    rcl = w.s([v, g, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. %s )' % (B, RP, WB))
    e2 = w.s([], 'eqid', '%s = %s' % (PFW, PFW))
    e2a = w.s([e2], 'a1i', '( %s -> %s = %s )' % (A, PFW, PFW))
    c3 = w.s([], 'oveq1', '( w = %s -> ( w ++ <" 4 "> ) = ( %s ++ <" 4 "> ) )' % (RP, RP))
    fc = w.s([rcl, e1a, e2a, c3], 'fmptco', '( %s -> ( %s o. encNatGam ) = ( p e. NN0 |-> ( %s ++ <" 4 "> ) ) )' % (A, PFW, RP))
    fc2 = w.s([fc], 'mptru', '( %s o. encNatGam ) = ( p e. NN0 |-> ( %s ++ <" 4 "> ) )' % (PFW, RP))
    vv = w.s([], 'encnatgamval', '( p e. NN0 -> ( encNatGam ` p ) = %s )' % RP)
    vv2 = w.s([vv], 'oveq1d', '( p e. NN0 -> ( ( encNatGam ` p ) ++ <" 4 "> ) = ( %s ++ <" 4 "> ) )' % RP)
    m = w.s([vv2], 'mpteq2ia', '%s = ( p e. NN0 |-> ( %s ++ <" 4 "> ) )' % (PFN, RP))
    w.qed([fc2, m], 'eqtr4i', '( %s o. encNatGam ) = %s' % (PFW, PFN))
    return w.run()


def tm2lenceq():
    w = W('tm2lenceq', 'A list of numbers on a stack is the list of their binary encodings.  Lean: ` encList_eq ` .')
    A = 'L e. Word NN0'
    v = w.s([], 'tm2lencval', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENC('L'), FLATN('L')))
    g = w.s([], 'tm2lencgam', '( %s -> ( encNatGam o. L ) e. %s )' % (A, WWB))
    vb = w.s([g, w.inst('tm2lencbval')], 'syl', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENCB('( encNatGam o. L )'), ENT('( encNatGam o. L )')))
    ve = w.s([g, w.inst('tm2lentval')], 'syl', '( %s -> %s = %s )' % (A, ENT('( encNatGam o. L )'), FLATW('( encNatGam o. L )')))
    ca = w.s([], 'coass', '( ( %s o. encNatGam ) o. L ) = ( %s o. ( encNatGam o. L ) )' % (PFW, PFW))
    pf = w.s([], 'tm2lencpf', '( %s o. encNatGam ) = %s' % (PFW, PFN))
    pf2 = w.s([pf], 'coeq1i', '( ( %s o. encNatGam ) o. L ) = ( %s o. L )' % (PFW, PFN))
    ce = w.s([ca, pf2], 'eqtr3i', '( %s o. ( encNatGam o. L ) ) = ( %s o. L )' % (PFW, PFN))
    ce2 = w.s([ce], 'oveq2i', '%s = %s' % (FLATW('( encNatGam o. L )'), FLATN('L')))
    ce3 = w.s([ce2], 'a1i', '( %s -> %s = %s )' % (A, FLATW('( encNatGam o. L )'), FLATN('L')))
    ve2 = w.s([ve, ce3], 'eqtrd', '( %s -> %s = %s )' % (A, ENT('( encNatGam o. L )'), FLATN('L')))
    o = w.s([ve2], 'oveq1d', '( %s -> ( %s ++ <" 2 "> ) = ( %s ++ <" 2 "> ) )' % (A, ENT('( encNatGam o. L )'), FLATN('L')))
    vb2 = w.s([vb, o], 'eqtrd', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENCB('( encNatGam o. L )'), FLATN('L')))
    w.qed([v, vb2], 'eqtr4d', '( %s -> %s = %s )' % (A, ENC('L'), ENCB('( encNatGam o. L )')))
    return w.run()


def tm2lenc0():
    w = W('tm2lenc0', 'The empty list of numbers on a stack.  Lean: ` encList_nil ` .')
    z = w.s([], 'wrd0', '(/) e. Word NN0')
    v = w.s([z, w.inst('tm2lencval')], 'ax-mp', '%s = ( %s ++ <" 2 "> )' % (ENC('(/)'), FLATN('(/)')))
    f = w.s([], 'encoutflat0', '%s = (/)' % FLATN('(/)'))
    o = w.s([f], 'oveq1i', '( %s ++ <" 2 "> ) = ( (/) ++ <" 2 "> )' % FLATN('(/)'))
    g = w.s([], 'gamma2', "2 e. Gamma'")
    s = w.s([g, w.inst('s1cl')], 'ax-mp', '<" 2 "> e. %s' % WG)
    l = w.s([s, w.inst('ccatlid')], 'ax-mp', '( (/) ++ <" 2 "> ) = <" 2 ">')
    t = w.s([o, l], 'eqtri', '( %s ++ <" 2 "> ) = <" 2 ">' % FLATN('(/)'))
    w.qed([v, t], 'eqtri', '%s = <" 2 ">' % ENC('(/)'))
    return w.run()


def tm2lenccons():
    w = W('tm2lenccons', 'A list of numbers with a new head on a stack.  Lean: ` encList_cons ` .')
    A = '( A e. NN0 /\\ L e. Word NN0 )'
    a1 = w.s([], 'simpl', '( %s -> A e. NN0 )' % A)
    l1 = w.s([], 'simpr', '( %s -> L e. Word NN0 )' % A)
    s1 = w.s([a1], 's1cld', '( %s -> <" A "> e. Word NN0 )' % A)
    al = w.s([s1, l1, w.inst('ccatcl')], 'syl2anc', '( %s -> ( <" A "> ++ L ) e. Word NN0 )' % A)
    e = w.s([al, w.inst('tm2lenceq')], 'syl', '( %s -> %s = %s )' % (A, ENC('( <" A "> ++ L )'), ENCB('( encNatGam o. ( <" A "> ++ L ) )')))
    f = closedw(w, A, 'tm2lbitf', 'encNatGam : NN0 --> %s' % WB)
    c = w.s([s1, l1, f, w.inst('ccatco')], 'syl3anc', '( %s -> ( encNatGam o. ( <" A "> ++ L ) ) = ( ( encNatGam o. <" A "> ) ++ ( encNatGam o. L ) ) )' % A)
    s = w.s([a1, f, w.inst('s1co')], 'syl2anc', '( %s -> ( encNatGam o. <" A "> ) = <" ( encNatGam ` A ) "> )' % A)
    o = w.s([s], 'oveq1d', '( %s -> ( ( encNatGam o. <" A "> ) ++ ( encNatGam o. L ) ) = ( <" ( encNatGam ` A ) "> ++ ( encNatGam o. L ) ) )' % A)
    c2 = w.s([c, o], 'eqtrd', '( %s -> ( encNatGam o. ( <" A "> ++ L ) ) = ( <" ( encNatGam ` A ) "> ++ ( encNatGam o. L ) ) )' % A)
    fe = w.s([c2], 'fveq2d', '( %s -> %s = %s )' % (A, ENCB('( encNatGam o. ( <" A "> ++ L ) )'), ENCB('( <" ( encNatGam ` A ) "> ++ ( encNatGam o. L ) )')))
    ea = w.s([f, a1, w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( encNatGam ` A ) e. %s )' % (A, WB))
    g = w.s([l1, w.inst('tm2lencgam')], 'syl', '( %s -> ( encNatGam o. L ) e. %s )' % (A, WWB))
    cc = w.s([ea, g, w.inst('tm2lencbcons')], 'syl2anc', '( %s -> %s = ( ( encNatGam ` A ) ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB('( <" ( encNatGam ` A ) "> ++ ( encNatGam o. L ) )'), ENCB('( encNatGam o. L )')))
    el = w.s([l1, w.inst('tm2lenceq')], 'syl', '( %s -> %s = %s )' % (A, ENC('L'), ENCB('( encNatGam o. L )')))
    el2 = w.s([el], 'oveq2d', '( %s -> ( <" 4 "> ++ %s ) = ( <" 4 "> ++ %s ) )' % (A, ENC('L'), ENCB('( encNatGam o. L )')))
    el3 = w.s([el2], 'oveq2d', '( %s -> ( ( encNatGam ` A ) ++ ( <" 4 "> ++ %s ) ) = ( ( encNatGam ` A ) ++ ( <" 4 "> ++ %s ) ) )' % (A, ENC('L'), ENCB('( encNatGam o. L )')))
    cc2 = w.s([cc, el3], 'eqtr4d', '( %s -> %s = ( ( encNatGam ` A ) ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB('( <" ( encNatGam ` A ) "> ++ ( encNatGam o. L ) )'), ENC('L')))
    t = w.s([fe, cc2], 'eqtrd', '( %s -> %s = ( ( encNatGam ` A ) ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB('( encNatGam o. ( <" A "> ++ L ) )'), ENC('L')))
    w.qed([e, t], 'eqtrd', '( %s -> %s = ( ( encNatGam ` A ) ++ ( <" 4 "> ++ %s ) ) )' % (A, ENC('( <" A "> ++ L )'), ENC('L')))
    return w.run()


def tm2lentlt():
    w = W('tm2lentlt', 'A number below ` 2 ^ B ` has an encoding of at most ` B ` bits.  Lean: ` encodeNat_length_le_of_lt_pow ` .')
    A = '( A e. NN0 /\\ B e. NN0 /\\ A < ( 2 ^ B ) )'
    a1 = w.s([], 'simp1', '( %s -> A e. NN0 )' % A)
    b1 = w.s([], 'simp2', '( %s -> B e. NN0 )' % A)
    lt = w.s([], 'simp3', '( %s -> A < ( 2 ^ B ) )' % A)
    H = '( # ` ( encodeNat ` A ) )'
    gl = w.s([a1, w.inst('encnatgamlen')], 'syl', '( %s -> ( # ` ( encNatGam ` A ) ) = %s )' % (A, H))
    # -. ( B + 1 ) <_ H
    B1 = '( B + 1 )'
    bn = w.s([b1, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (A, B1))
    C = '( %s /\\ %s <_ %s )' % (A, B1, H)
    a1c = w.s([a1], 'adantr', '( %s -> A e. NN0 )' % C)
    bnc = w.s([bn], 'adantr', '( %s -> %s e. NN )' % (C, B1))
    lec = w.s([], 'simpr', '( %s -> %s <_ %s )' % (C, B1, H))
    le = w.s([a1c, bnc, lec, w.inst('encnatlenle')], 'syl3anc', '( %s -> ( 2 ^ ( %s - 1 ) ) <_ A )' % (C, B1))
    bc = w.s([b1], 'nn0cnd', '( %s -> B e. CC )' % A)
    pc = w.s([bc, w.inst('pncan1')], 'syl', '( %s -> ( %s - 1 ) = B )' % (A, B1))
    pc2 = w.s([pc], 'oveq2d', '( %s -> ( 2 ^ ( %s - 1 ) ) = ( 2 ^ B ) )' % (A, B1))
    pc3 = w.s([pc2], 'adantr', '( %s -> ( 2 ^ ( %s - 1 ) ) = ( 2 ^ B ) )' % (C, B1))
    le2 = w.s([pc3, le], 'eqbrtrrd', '( %s -> ( 2 ^ B ) <_ A )' % C)
    ar = w.s([a1], 'nn0red', '( %s -> A e. RR )' % A)
    tr = w.s([], '2re', '2 e. RR'); tra = w.s([tr], 'a1i', '( %s -> 2 e. RR )' % A)
    pr = w.s([tra, b1], 'reexpcld', '( %s -> ( 2 ^ B ) e. RR )' % A)
    nl = w.s([ar, pr], 'ltnled', '( %s -> ( A < ( 2 ^ B ) <-> -. ( 2 ^ B ) <_ A ) )' % A)
    nle = w.s([nl, lt], 'mpbid', '( %s -> -. ( 2 ^ B ) <_ A )' % A)
    nlec = w.s([nle], 'adantr', '( %s -> -. ( 2 ^ B ) <_ A )' % C)
    ctr = w.s([le2, nlec], 'pm2.21dd', '( %s -> -. %s <_ %s )' % (C, B1, H))
    ctr2 = w.s([ctr], 'ex', '( %s -> ( %s <_ %s -> -. %s <_ %s ) )' % (A, B1, H, B1, H))
    ctr3 = w.s([ctr2], 'pm2.01d', '( %s -> -. %s <_ %s )' % (A, B1, H))
    hn = w.s([a1, w.inst('encnatf')], 'ffvelcdmi' if False else 'sylancr', '( %s -> ( encodeNat ` A ) e. Word 2o )' % A)
    return None if False else _tm2lentlt_tail(w, A, a1, b1, ctr3, gl, H, B1)


def _tm2lentlt_tail(w, A, a1, b1, ctr3, gl, H, B1):
    f = closedw(w, A, 'encnatf', 'encodeNat : NN0 --> Word 2o')
    hw = w.s([f, a1, w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( encodeNat ` A ) e. Word 2o )' % A)
    hn = w.s([hw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (A, H))
    hr = w.s([hn], 'nn0red', '( %s -> %s e. RR )' % (A, H))
    b1r = w.s([b1], 'peano2nn0' if False else 'nn0red', '( %s -> B e. RR )' % A)
    b1r2 = w.s([b1r, w.inst('peano2re')], 'syl', '( %s -> %s e. RR )' % (A, B1))
    nl2 = w.s([hr, b1r2], 'ltnled', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (A, H, B1, B1, H))
    lt2 = w.s([nl2, ctr3], 'mpbird', '( %s -> %s < %s )' % (A, H, B1))
    le3 = w.s([hn, b1, w.inst('nn0leltp1')], 'syl2anc', '( %s -> ( %s <_ B <-> %s < %s ) )' % (A, H, H, B1))
    le4 = w.s([le3, lt2], 'mpbird', '( %s -> %s <_ B )' % (A, H))
    w.qed([gl, le4], 'eqbrtrd', '( %s -> ( # ` ( encNatGam ` A ) ) <_ B )' % A)
    return w.run()


if __name__ == '__main__':
    for f in [tm2lencbhd0, tm2lencbhd1, tm2ldrop, tm2lencbdrop, tm2ldrop0, tm2lpfxs1,
              tm2lencval, tm2lenccl, tm2linclf, tm2lbitf, tm2lencgam, tm2lencpf, tm2lenceq,
              tm2lenc0, tm2lenccons, tm2lentlt]:
        if want(f.__name__): f()
