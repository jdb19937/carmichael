"""T8a: the word of a list of slots ( df-tm2encslots ) and the flags of the slot loop.

  ttsesv ttsescl ttses0 ttsesccat ttsess1   value, typing, empty, concatenation, one slot
  ttsesdrop   Lean's ` drop_eq_getElem_cons ` rewrite under encSlots
  ttsesrev    Lean's ` take_succ ` + ` reverse_append ` rewrite under encSlots
  ttslotn0    a slot's word is not empty
  ttslotblk   Lean ` head?_encSlot_ne_blank `
  ttseshd     Lean ` flag_encSlots_drop ` (via ` head?_encSlots_blank ` )

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_c_es.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
from tm import numne

SEL = sys.argv[1:]
GS = lambda x: "( ( freeMnd ` Gamma' ) gsum %s )" % x
ESF = '( l e. %s |-> %s )' % (WSLOT, GS('( encSlot o. l )'))
SLF = "encSlot : %s --> Word Gamma'" % SLOT
WWG = "Word Word Gamma'"


def ttsesv():
    w = W('ttsesv', 'Value of ~ df-tm2encslots . Lean: ` encSlots ` .')
    ph = 'L e. %s' % WSLOT
    idl = w.s([], 'id', '( l = L -> l = L )')
    cg, nb = w.congr(GS('( encSlot o. l )'), {'l': 'L'}, 'l = L', {'l': idl})
    assert nb == GS('( encSlot o. L )'), nb
    d = w.s([], 'df-tm2encslots', 'encSlots = %s' % ESF)
    g = w.s([cg, d], 'fvmptg', '( ( L e. %s /\\ %s e. _V ) -> %s = %s )' % (WSLOT, GS('( encSlot o. L )'), ES('L'), GS('( encSlot o. L )')))
    xv = closed(w, ph, 'ovex', '%s e. _V' % GS('( encSlot o. L )'))
    w.qed([w.s([], 'id', '( %s -> %s )' % (ph, ph)), xv, g], 'syl2anc', ST_ESV)
    return w.run()


def cow(w, ph, L, lw):
    """( ph -> ( encSlot o. L ) e. Word Word Gamma' ) from lw : L e. Word SLOT"""
    f = closed(w, ph, 'ttabslotf', SLF)
    return w.s([lw, f, w.inst('wrdco')], 'syl2anc', '( %s -> ( encSlot o. %s ) e. %s )' % (ph, L, WWG))


def ttsescl():
    w = W('ttsescl', 'The word of a list of slots is a word over ` Gamma\' ` .')
    ph = 'L e. %s' % WSLOT
    lw = w.s([], 'id', '( %s -> %s )' % (ph, ph))
    v = w.s([lw, w.inst('ttsesv')], 'syl', '( %s -> %s = %s )' % (ph, ES('L'), GS('( encSlot o. L )')))
    c = w.s([cow(w, ph, 'L', lw), w.inst('gsumgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, GS('( encSlot o. L )')))
    w.qed([v, c], 'eqeltrd', ST_ESCL)
    return w.run()


def ttses0():
    w = W('ttses0', 'The word of the empty list of slots is empty (Lean ` encSlots_nil ` ).')
    wz = w.s([], 'wrd0', '(/) e. %s' % WSLOT)
    v = w.s([wz, w.inst('ttsesv')], 'ax-mp', '%s = %s' % (ES('(/)'), GS('( encSlot o. (/) )')))
    c0 = w.s([], 'co02', '( encSlot o. (/) ) = (/)')
    g = w.s([c0], 'oveq2i', '%s = %s' % (GS('( encSlot o. (/) )'), GS('(/)')))
    z = w.s([], 'gsumgam0', '%s = (/)' % GS('(/)'))
    w.qed([v, w.s([g, z], 'eqtri', '%s = (/)' % GS('( encSlot o. (/) )'))], 'eqtri', ST_ES0)
    return w.run()


def ttsesccat():
    w = W('ttsesccat', 'The word of a concatenation of slot lists (Lean ` encSlots_append ` ).')
    ph = '( L e. %s /\\ U e. %s )' % (WSLOT, WSLOT)
    lw = w.s([], 'simpl', '( %s -> L e. %s )' % (ph, WSLOT))
    uw = w.s([], 'simpr', '( %s -> U e. %s )' % (ph, WSLOT))
    luw = w.s([lw, uw, w.inst('ccatcl')], 'syl2anc', '( %s -> ( L ++ U ) e. %s )' % (ph, WSLOT))
    v = w.s([luw, w.inst('ttsesv')], 'syl', '( %s -> %s = %s )' % (ph, ES('( L ++ U )'), GS('( encSlot o. ( L ++ U ) )')))
    f = closed(w, ph, 'ttabslotf', SLF)
    cc = w.s([lw, uw, f, w.inst('ccatco')], 'syl3anc', '( %s -> ( encSlot o. ( L ++ U ) ) = ( ( encSlot o. L ) ++ ( encSlot o. U ) ) )' % ph)
    g1 = w.s([cc], 'oveq2d', '( %s -> %s = %s )' % (ph, GS('( encSlot o. ( L ++ U ) )'), GS('( ( encSlot o. L ) ++ ( encSlot o. U ) )')))
    g2 = w.s([cow(w, ph, 'L', lw), cow(w, ph, 'U', uw), w.inst('gsumgamccat')], 'syl2anc',
             '( %s -> %s = ( %s ++ %s ) )' % (ph, GS('( ( encSlot o. L ) ++ ( encSlot o. U ) )'), GS('( encSlot o. L )'), GS('( encSlot o. U )')))
    vl = w.s([lw, w.inst('ttsesv')], 'syl', '( %s -> %s = %s )' % (ph, ES('L'), GS('( encSlot o. L )')))
    vu = w.s([uw, w.inst('ttsesv')], 'syl', '( %s -> %s = %s )' % (ph, ES('U'), GS('( encSlot o. U )')))
    r = w.s([vl, vu], 'oveq12d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (ph, ES('L'), ES('U'), GS('( encSlot o. L )'), GS('( encSlot o. U )')))
    a = w.s([v, g1], 'eqtrd', '( %s -> %s = %s )' % (ph, ES('( L ++ U )'), GS('( ( encSlot o. L ) ++ ( encSlot o. U ) )')))
    b = w.s([a, g2], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES('( L ++ U )'), GS('( encSlot o. L )'), GS('( encSlot o. U )')))
    w.qed([b, r], 'eqtr4d', ST_ESCC)
    return w.run()


def ttsess1():
    w = W('ttsess1', 'The word of a one-slot list is the slot\'s word (Lean ` encSlots_cons ` at ` [] ` ).')
    ph = 'O e. %s' % SLOT
    oo = w.s([], 'id', '( %s -> %s )' % (ph, ph))
    sw = w.s([oo, w.inst('s1cld')], 'syl', '( %s -> <" O "> e. %s )' % (ph, WSLOT))
    v = w.s([sw, w.inst('ttsesv')], 'syl', '( %s -> %s = %s )' % (ph, ES('<" O ">'), GS('( encSlot o. <" O "> )')))
    f = closed(w, ph, 'ttabslotf', SLF)
    sc = w.s([oo, f, w.inst('s1co')], 'syl2anc', '( %s -> ( encSlot o. <" O "> ) = <" %s "> )' % (ph, ESL('O')))
    g1 = w.s([sc], 'oveq2d', '( %s -> %s = %s )' % (ph, GS('( encSlot o. <" O "> )'), GS('<" %s ">' % ESL('O'))))
    ew = w.s([f, oo, w.inst('ffvelcdmd')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, ESL('O'))) if False else \
        w.s([w.s([], 'ttabslotf', SLF)], 'ffvelcdmi', "( %s -> %s e. Word Gamma' )" % (ph, ESL('O')))
    g2 = w.s([ew, w.inst('gsumgams1')], 'syl', '( %s -> %s = %s )' % (ph, GS('<" %s ">' % ESL('O')), ESL('O')))
    w.qed([w.s([v, g1], 'eqtrd', '( %s -> %s = %s )' % (ph, ES('<" O ">'), GS('<" %s ">' % ESL('O')))), g2], 'eqtrd', ST_ESS1)
    return w.run()


def idx_facts(w, ph, lw, ii):
    """from ii : ( ph -> I e. ( 0 ..^ ( # ` L ) ) ): I e. NN0, the interval memberships"""
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> I e. NN0 )' % ph)
    ifz = w.s([ii, w.inst('elfzofz')], 'syl', '( %s -> I e. ( 0 ... ( # ` L ) ) )' % ph)
    i1fz = w.s([ii, w.inst('fzofzp1')], 'syl', '( %s -> ( I + 1 ) e. ( 0 ... ( # ` L ) ) )' % ph)
    iuz = w.s([inn, w.inst('nn0uz')], 'syl', '( %s -> I e. ( ZZ>= ` 0 ) )' % ph) if False else None
    i0 = w.s([inn, w.inst('fzonn0p1')], 'syl', '( %s -> I e. ( 0 ..^ ( I + 1 ) ) )' % ph)
    i0b = w.s([i0, w.inst('elfzofz')], 'syl', '( %s -> I e. ( 0 ... ( I + 1 ) ) )' % ph)
    ln = w.s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    lfz = w.s([ln, w.inst('nn0fz0')], 'sylib', '( %s -> ( # ` L ) e. ( 0 ... ( # ` L ) ) )' % ph)
    li = w.s([lw, ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` I ) e. %s )' % (ph, SLOT))
    return dict(inn=inn, ifz=ifz, i1fz=i1fz, i0b=i0b, ln=ln, lfz=lfz, li=li)


def ttsesdrop():
    w = W('ttsesdrop', 'The slots from index ` I ` on are slot ` I ` followed by the slots from ` I + 1 ` on '
                       '(Lean ` List.drop_eq_getElem_cons ` and ` encSlots_cons ` ).')
    ph = '( L e. %s /\\ I e. ( 0 ..^ ( # ` L ) ) )' % WSLOT
    lw = w.s([], 'simpl', '( %s -> L e. %s )' % (ph, WSLOT))
    ii = w.s([], 'simpr', '( %s -> I e. ( 0 ..^ ( # ` L ) ) )' % ph)
    x = idx_facts(w, ph, lw, ii)
    A = '( L substr <. I , ( I + 1 ) >. )'
    B = DROP('L', '( I + 1 )')
    cs = w.s([lw, x['i0b'], x['i1fz'], x['lfz'], w.inst('ccatswrd')], 'syl13anc', '( %s -> ( %s ++ %s ) = %s )' % (ph, A, B, DROP('L', 'I')))
    s1 = w.s([lw, ii, w.inst('swrds1')], 'syl2anc', '( %s -> %s = <" ( L ` I ) "> )' % (ph, A))
    e1 = w.s([s1], 'oveq1d', '( %s -> ( %s ++ %s ) = ( <" ( L ` I ) "> ++ %s ) )' % (ph, A, B, B))
    e2 = w.s([cs, e1], 'eqtr3d', '( %s -> %s = ( <" ( L ` I ) "> ++ %s ) )' % (ph, DROP('L', 'I'), B))
    f = w.s([e2], 'fveq2d', '( %s -> %s = %s )' % (ph, ES(DROP('L', 'I')), ES('( <" ( L ` I ) "> ++ %s )' % B)))
    sw = w.s([x['li'], w.inst('s1cld')], 'syl', '( %s -> <" ( L ` I ) "> e. %s )' % (ph, WSLOT))
    bw = w.s([lw, w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, B, WSLOT))
    c = w.s([sw, bw, w.inst('ttsesccat')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES('( <" ( L ` I ) "> ++ %s )' % B), ES('<" ( L ` I ) ">'), ES(B)))
    s = w.s([x['li'], w.inst('ttsess1')], 'syl', '( %s -> %s = %s )' % (ph, ES('<" ( L ` I ) ">'), ESL('( L ` I )')))
    s2 = w.s([s], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (ph, ES('<" ( L ` I ) ">'), ES(B), ESL('( L ` I )'), ES(B)))
    w.qed([w.s([f, c], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES(DROP('L', 'I')), ES('<" ( L ` I ) ">'), ES(B))), s2], 'eqtrd', ST_ESDR)
    return w.run()


def ttsesrev():
    w = W('ttsesrev', 'The reversed first ` I + 1 ` slots are slot ` I ` followed by the reversed first ` I ` slots '
                      '(Lean ` List.take_succ_eq_append_getElem ` , ` List.reverse_append ` , ` encSlots_cons ` ).')
    ph = '( L e. %s /\\ I e. ( 0 ..^ ( # ` L ) ) )' % WSLOT
    lw = w.s([], 'simpl', '( %s -> L e. %s )' % (ph, WSLOT))
    ii = w.s([], 'simpr', '( %s -> I e. ( 0 ..^ ( # ` L ) ) )' % ph)
    x = idx_facts(w, ph, lw, ii)
    A = '( L substr <. I , ( I + 1 ) >. )'
    P0, P1_ = PFX('L', 'I'), PFX('L', '( I + 1 )')
    cp = w.s([lw, x['i0b'], x['i1fz'], w.inst('ccatpfx')], 'syl3anc', '( %s -> ( %s ++ %s ) = %s )' % (ph, P0, A, P1_))
    s1 = w.s([lw, ii, w.inst('swrds1')], 'syl2anc', '( %s -> %s = <" ( L ` I ) "> )' % (ph, A))
    e1 = w.s([s1], 'oveq2d', '( %s -> ( %s ++ %s ) = ( %s ++ <" ( L ` I ) "> ) )' % (ph, P0, A, P0))
    e2 = w.s([cp, e1], 'eqtr3d', '( %s -> %s = ( %s ++ <" ( L ` I ) "> ) )' % (ph, P1_, P0))
    r1 = w.s([e2], 'fveq2d', '( %s -> %s = %s )' % (ph, REV(P1_), REV('( %s ++ <" ( L ` I ) "> )' % P0)))
    p0w = w.s([lw, w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ph, P0, WSLOT))
    sw = w.s([x['li'], w.inst('s1cld')], 'syl', '( %s -> <" ( L ` I ) "> e. %s )' % (ph, WSLOT))
    rc = w.s([p0w, sw, w.inst('revccat')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, REV('( %s ++ <" ( L ` I ) "> )' % P0),
                                                                                     REV('<" ( L ` I ) ">'), REV(P0)))
    rs = closed(w, ph, 'revs1', '%s = <" ( L ` I ) ">' % REV('<" ( L ` I ) ">'))
    rs2 = w.s([rs], 'oveq1d', '( %s -> ( %s ++ %s ) = ( <" ( L ` I ) "> ++ %s ) )' % (ph, REV('<" ( L ` I ) ">'), REV(P0), REV(P0)))
    RR_ = '( <" ( L ` I ) "> ++ %s )' % REV(P0)
    r = w.s([w.s([r1, rc], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ph, REV(P1_), REV('<" ( L ` I ) ">'), REV(P0))), rs2], 'eqtrd',
            '( %s -> %s = %s )' % (ph, REV(P1_), RR_))
    f = w.s([r], 'fveq2d', '( %s -> %s = %s )' % (ph, ES(REV(P1_)), ES(RR_)))
    rpw = w.s([p0w, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REV(P0), WSLOT))
    c = w.s([sw, rpw, w.inst('ttsesccat')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES(RR_), ES('<" ( L ` I ) ">'), ES(REV(P0))))
    s = w.s([x['li'], w.inst('ttsess1')], 'syl', '( %s -> %s = %s )' % (ph, ES('<" ( L ` I ) ">'), ESL('( L ` I )')))
    s2 = w.s([s], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (ph, ES('<" ( L ` I ) ">'), ES(REV(P0)), ESL('( L ` I )'), ES(REV(P0))))
    w.qed([w.s([f, c], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (ph, ES(REV(P1_)), ES('<" ( L ` I ) ">'), ES(REV(P0)))), s2], 'eqtrd', ST_ESRV)
    return w.run()


def ttslotn0():
    w = W('ttslotn0', 'The word of a slot is not empty: ` ket ` or a list ending in ` bra ` .')
    ph = 'O e. %s' % SLOT
    oo = w.s([], 'id', '( %s -> %s )' % (ph, ph))
    NN = '( inr ` (/) )'
    IFS = 'if ( O = %s , <" 3 "> , ( encList ` ( 2nd ` O ) ) )' % NN
    v = w.s([oo, w.inst('ttabslotv')], 'syl', '( %s -> %s = %s )' % (ph, ESL('O'), IFS))
    # ifbothda: A = if -> ( A =/= (/) <-> if =/= (/) ) ; B = if -> ...
    e1 = w.s([], 'neeq1', '( <" 3 "> = %s -> ( <" 3 "> =/= (/) <-> %s =/= (/) ) )' % (IFS, IFS))
    e2 = w.s([], 'neeq1', '( ( encList ` ( 2nd ` O ) ) = %s -> ( ( encList ` ( 2nd ` O ) ) =/= (/) <-> %s =/= (/) ) )' % (IFS, IFS))
    c1 = w.s([w.s([], 's1nz', '<" 3 "> =/= (/)')], 'a1i', '( ( %s /\\ O = %s ) -> <" 3 "> =/= (/) )' % (ph, NN))
    a2 = '( %s /\\ -. O = %s )' % (ph, NN)
    ow = w.s([w.s([], 'simpl', '( %s -> %s )' % (a2, ph)), w.inst('ttabopt')], 'syl', '( %s -> ( 2nd ` O ) e. Word NN0 )' % a2)
    lv = w.s([ow, w.inst('tm2lencval')], 'syl', "( %s -> ( encList ` ( 2nd ` O ) ) = ( %s ++ <\" 2 \"> ) )"
             % (a2, GS("( ( p e. NN0 |-> ( ( encNatGam ` p ) ++ <\" 4 \"> ) ) o. ( 2nd ` O ) )")))
    G = GS("( ( p e. NN0 |-> ( ( encNatGam ` p ) ++ <\" 4 \"> ) ) o. ( 2nd ` O ) )")
    # the inner sum is a word: T6's map into Word Word Gamma' then gsumgamcl
    PF = "( p e. NN0 |-> ( ( encNatGam ` p ) ++ <\" 4 \"> ) )"
    bj = '( p e. NN0 -> ( ( encNatGam ` p ) ++ <" 4 "> ) e. Word Gamma\' )'
    b1 = w.s([w.s([], 'encnatgamcl', "( p e. NN0 -> ( encNatGam ` p ) e. Word Gamma' )"),
              w.s([w.s([w.s([], 'gamma4', "4 e. Gamma'"), w.inst('s1cl')], 'ax-mp', "<\" 4 \"> e. Word Gamma'")], 'a1i',
                  "( p e. NN0 -> <\" 4 \"> e. Word Gamma' )"), w.inst('ccatcl')], 'syl2anc', bj)
    pf = w.s([b1], 'fmpti', "%s : NN0 --> Word Gamma'" % PF)
    cw = w.s([ow, w.s([pf], 'a1i', "( %s -> %s : NN0 --> Word Gamma' )" % (a2, PF)), w.inst('wrdco')], 'syl2anc',
             "( %s -> ( %s o. ( 2nd ` O ) ) e. Word Word Gamma' )" % (a2, PF))
    gg = w.s([cw, w.inst('gsumgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (a2, G))
    ne = w.s([gg, w.inst('ccatws1n0')], 'syl', '( %s -> ( %s ++ <" 2 "> ) =/= (/) )' % (a2, G))
    c2 = w.s([lv, ne], 'eqnetrd', '( %s -> ( encList ` ( 2nd ` O ) ) =/= (/) )' % a2)
    ib = w.s([e1, e2, c1, c2], 'ifbothda', '( %s -> %s =/= (/) )' % (ph, IFS))
    w.qed([v, ib], 'eqnetrd', ST_SLN0)
    return w.run()


def not_in_bu(w, n):
    """closed step: -. n e. ( ( { 1 } X. 2o ) u. { 4 } ) for a numeral n =/= 4"""
    U = '( ( { 1 } X. 2o ) u. { 4 } )'
    rn = w.s([], '%sre' % n, '%s e. RR' % n)
    z1 = w.s([rn, w.s([], 'tmcnbits', '( %s e. RR -> -. %s e. ( { 1 } X. 2o ) )' % (n, n))], 'ax-mp', '-. %s e. ( { 1 } X. 2o )' % n)
    z2 = w.s([rn, w.s([], 'elsng', '( %s e. RR -> ( %s e. { 4 } <-> %s = 4 ) )' % (n, n, n))], 'ax-mp', '( %s e. { 4 } <-> %s = 4 )' % (n, n))
    z3 = numne(w, n, '4')
    z4 = w.s([z3, z2], 'mtbir', '-. %s e. { 4 }' % n)
    z5 = w.s([z1, z4], 'pm3.2ni', '-. ( %s e. ( { 1 } X. 2o ) \\/ %s e. { 4 } )' % (n, n))
    z6 = w.s([], 'elun', '( %s e. %s <-> ( %s e. ( { 1 } X. 2o ) \\/ %s e. { 4 } ) )' % (n, U, n, n))
    return w.s([z5, z6], 'mtbir', '-. %s e. %s' % (n, U))


def ttslotblk():
    w = W('ttslotblk', 'The first letter of a slot\'s word (followed by anything) is not ` blank = 0 ` : '
                       '` ket = 3 ` for an empty slot, ` bra = 2 ` , a bit or a comma for a list.  Lean: '
                       '` head?_encSlot_ne_blank ` .')
    ph = "( O e. %s /\\ R e. Word Gamma' )" % SLOT
    NN = '( inr ` (/) )'
    HD = lambda x: '( ( %s ++ R ) ` 0 )' % x
    oo = w.s([], 'simpl', '( %s -> O e. %s )' % (ph, SLOT))
    rw = w.s([], 'simpr', "( %s -> R e. Word Gamma' )" % ph)
    v = w.s([oo, w.inst('ttabslotv')], 'syl', '( %s -> %s = if ( O = %s , <" 3 "> , ( encList ` ( 2nd ` O ) ) ) )' % (ph, ESL('O'), NN))
    # O = none
    p1 = '( %s /\\ O = %s )' % (ph, NN)
    it = w.s([w.s([], 'simpr', '( %s -> O = %s )' % (p1, NN))], 'iftrued', '( %s -> if ( O = %s , <" 3 "> , ( encList ` ( 2nd ` O ) ) ) = <" 3 "> )' % (p1, NN))
    vv = w.s([w.s([v], 'adantr', '( %s -> %s = if ( O = %s , <" 3 "> , ( encList ` ( 2nd ` O ) ) ) )' % (p1, ESL('O'), NN)), it], 'eqtrd',
             '( %s -> %s = <" 3 "> )' % (p1, ESL('O')))
    h1 = w.s([w.s([vv], 'oveq1d', '( %s -> ( %s ++ R ) = ( <" 3 "> ++ R ) )' % (p1, ESL('O')))], 'fveq1d', '( %s -> %s = %s )' % (p1, HD(ESL('O')), HD('<" 3 ">')))
    g3 = closed(w, p1, 'gamma3', "3 e. Gamma'")
    s3 = w.s([g3], 's1cld', "( %s -> <\" 3 \"> e. Word Gamma' )" % p1)
    r1 = w.s([rw], 'adantr', "( %s -> R e. Word Gamma' )" % p1)
    ln = closed(w, p1, 's1len', '( # ` <" 3 "> ) = 1')
    lt = w.s([ln, closed(w, p1, '0lt1', '0 < 1')], 'breqtrrd', '( %s -> 0 < ( # ` <" 3 "> ) )' % p1)
    cf = w.s([s3, r1, lt, w.inst('ccatfv0')], 'syl3anc', '( %s -> %s = ( <" 3 "> ` 0 ) )' % (p1, HD('<" 3 ">')))
    sf = w.s([g3, w.inst('s1fv')], 'syl', '( %s -> ( <" 3 "> ` 0 ) = 3 )' % p1)
    h3 = w.s([w.s([h1, cf], 'eqtrd', '( %s -> %s = ( <" 3 "> ` 0 ) )' % (p1, HD(ESL('O')))), sf], 'eqtrd', '( %s -> %s = 3 )' % (p1, HD(ESL('O'))))
    n30 = w.s([numne(w, '3', '0')], 'neir', '3 =/= 0')
    x1 = w.s([h3, w.s([n30], 'a1i', '( %s -> 3 =/= 0 )' % p1)], 'eqnetrd', '( %s -> %s =/= 0 )' % (p1, HD(ESL('O'))))
    c1 = w.s([x1], 'ex', '( %s -> ( O = %s -> %s =/= 0 ) )' % (ph, NN, HD(ESL('O'))))
    # O =/= none : as ttabkethd with 0
    p2 = '( %s /\\ O =/= %s )' % (ph, NN)
    nn2 = w.s([w.s([], 'simpr', '( %s -> O =/= %s )' % (p2, NN))], 'neneqd', '( %s -> -. O = %s )' % (p2, NN))
    itf = w.s([nn2], 'iffalsed', '( %s -> if ( O = %s , <" 3 "> , ( encList ` ( 2nd ` O ) ) ) = ( encList ` ( 2nd ` O ) ) )' % (p2, NN))
    vv2 = w.s([w.s([v], 'adantr', '( %s -> %s = if ( O = %s , <" 3 "> , ( encList ` ( 2nd ` O ) ) ) )' % (p2, ESL('O'), NN)), itf], 'eqtrd',
              '( %s -> %s = ( encList ` ( 2nd ` O ) ) )' % (p2, ESL('O')))
    WW = '( 2nd ` O )'
    E = '( encNatGam o. %s )' % WW
    H = lambda X: '( ( ( encListB ` %s ) ++ R ) ` 0 )' % X
    ow = w.s([w.s([], 'simpll', '( %s -> O e. %s )' % (p2, SLOT)), w.inst('ttabopt')], 'syl', '( %s -> %s e. Word NN0 )' % (p2, WW))
    eq = w.s([ow, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (p2, WW, E))
    h2 = w.s([w.s([w.s([vv2, eq], 'eqtrd', '( %s -> %s = ( encListB ` %s ) )' % (p2, ESL('O'), E))], 'oveq1d',
                  '( %s -> ( %s ++ R ) = ( ( encListB ` %s ) ++ R ) )' % (p2, ESL('O'), E))], 'fveq1d', '( %s -> %s = %s )' % (p2, HD(ESL('O')), H(E)))
    r2 = w.s([], 'simplr', "( %s -> R e. Word Gamma' )" % p2)
    # E = (/)
    q1 = '( %s /\\ %s = (/) )' % (p2, E)
    y1 = w.s([w.s([w.s([], 'simpr', '( %s -> %s = (/) )' % (q1, E))], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` (/) ) )' % (q1, E))],
             'oveq1d', '( %s -> ( ( encListB ` %s ) ++ R ) = ( ( encListB ` (/) ) ++ R ) )' % (q1, E))
    y2 = w.s([y1], 'fveq1d', '( %s -> %s = %s )' % (q1, H(E), H('(/)')))
    y3 = w.s([w.s([r2], 'adantr', "( %s -> R e. Word Gamma' )" % q1), w.inst('tm2lencbhd0')], 'syl', '( %s -> %s = 2 )' % (q1, H('(/)')))
    n20 = w.s([numne(w, '2', '0')], 'neir', '2 =/= 0')
    y4 = w.s([w.s([y2, y3], 'eqtrd', '( %s -> %s = 2 )' % (q1, H(E))), w.s([n20], 'a1i', '( %s -> 2 =/= 0 )' % q1)], 'eqnetrd',
             '( %s -> %s =/= 0 )' % (q1, H(E)))
    d1 = w.s([y4], 'ex', '( %s -> ( %s = (/) -> %s =/= 0 ) )' % (p2, E, H(E)))
    q2 = '( %s /\\ %s =/= (/) )' % (p2, E)
    U = '( ( { 1 } X. 2o ) u. { 4 } )'
    z1 = w.s([w.s([ow], 'adantr', '( %s -> %s e. Word NN0 )' % (q2, WW)), w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word ( { 1 } X. 2o ) )' % (q2, E))
    z4 = w.s([z1, w.s([r2], 'adantr', "( %s -> R e. Word Gamma' )" % q2), w.s([], 'simpr', '( %s -> %s =/= (/) )' % (q2, E)), w.inst('tm2lencbhd1')],
             'syl3anc', '( %s -> %s e. %s )' % (q2, H(E), U))
    z5 = w.s([not_in_bu(w, '0')], 'a1i', '( %s -> -. 0 e. %s )' % (q2, U))
    z6 = w.s([z4, z5, w.inst('nelne2')], 'syl2anc', '( %s -> %s =/= 0 )' % (q2, H(E)))
    d2 = w.s([z6], 'ex', '( %s -> ( %s =/= (/) -> %s =/= 0 ) )' % (p2, E, H(E)))
    hE = w.s([d1, d2], 'pm2.61dne', '( %s -> %s =/= 0 )' % (p2, H(E)))
    x2 = w.s([h2, hE], 'eqnetrd', '( %s -> %s =/= 0 )' % (p2, HD(ESL('O'))))
    c2 = w.s([x2], 'ex', '( %s -> ( O =/= %s -> %s =/= 0 ) )' % (ph, NN, HD(ESL('O'))))
    w.qed([c1, c2], 'pm2.61dne', ST_SLBK)
    return w.run()


def ttseshd():
    w = W('ttseshd', 'The first letter of the slots from index ` I ` on, followed by the ` blank ` marker, is '
                     '` blank = 0 ` iff no slot is left.  Lean: ` flag_encSlots_drop ` , ` head?_encSlots_blank ` .')
    ph = "( L e. %s /\\ X e. Word Gamma' /\\ I e. ( 0 ... ( # ` L ) ) )" % WSLOT
    V = lambda i: '( %s ++ ( <" 0 "> ++ X ) )' % ES(DROP('L', i))
    lw = w.s([], 'simp1', '( %s -> L e. %s )' % (ph, WSLOT))
    xw = w.s([], 'simp2', "( %s -> X e. Word Gamma' )" % ph)
    ifz = w.s([], 'simp3', "( %s -> I e. ( 0 ... ( # ` L ) ) )" % ph)
    Z0X = '( <" 0 "> ++ X )'
    g0 = closed(w, ph, 'gamma0', "0 e. Gamma'")
    s0 = w.s([g0], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
    zx = w.s([s0, xw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Z0X))
    # I = # L
    p1 = '( %s /\\ I = ( # ` L ) )' % ph
    L1 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (p1, concl(w, ph, st)))
    ie = w.s([], 'simpr', '( %s -> I = ( # ` L ) )' % p1)
    d0 = w.s([ie], 'opeq1d', '( %s -> <. I , ( # ` L ) >. = <. ( # ` L ) , ( # ` L ) >. )' % p1)
    d1 = w.s([d0], 'oveq2d', '( %s -> %s = ( L substr <. ( # ` L ) , ( # ` L ) >. ) )' % (p1, DROP('L', 'I')))
    d2 = w.s([d1, closed(w, p1, 'swrd00', '( L substr <. ( # ` L ) , ( # ` L ) >. ) = (/)')], 'eqtrd', '( %s -> %s = (/) )' % (p1, DROP('L', 'I')))
    d3 = w.s([w.s([d2], 'fveq2d', '( %s -> %s = %s )' % (p1, ES(DROP('L', 'I')), ES('(/)'))), closed(w, p1, 'ttses0', ST_ES0)], 'eqtrd',
             '( %s -> %s = (/) )' % (p1, ES(DROP('L', 'I'))))
    d4 = w.s([d3], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (p1, V('I'), Z0X))
    d5 = w.s([L1(zx), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (p1, Z0X, Z0X))
    d6 = w.s([w.s([d4, d5], 'eqtrd', '( %s -> %s = %s )' % (p1, V('I'), Z0X))], 'fveq1d', '( %s -> ( %s ` 0 ) = ( %s ` 0 ) )' % (p1, V('I'), Z0X))
    ln = closed(w, p1, 's1len', '( # ` <" 0 "> ) = 1')
    lt = w.s([ln, closed(w, p1, '0lt1', '0 < 1')], 'breqtrrd', '( %s -> 0 < ( # ` <" 0 "> ) )' % p1)
    cf = w.s([L1(s0), L1(xw), lt, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = ( <" 0 "> ` 0 ) )' % (p1, Z0X))
    sf = w.s([L1(g0), w.inst('s1fv')], 'syl', '( %s -> ( <" 0 "> ` 0 ) = 0 )' % p1)
    hd = w.s([w.s([d6, cf], 'eqtrd', '( %s -> ( %s ` 0 ) = ( <" 0 "> ` 0 ) )' % (p1, V('I'))), sf], 'eqtrd', '( %s -> ( %s ` 0 ) = 0 )' % (p1, V('I')))
    b1 = w.s([hd, ie], '2thd', '( %s -> ( ( %s ` 0 ) = 0 <-> I = ( # ` L ) ) )' % (p1, V('I')))
    # I e. ( 0 ..^ # L )
    p2 = '( %s /\\ I e. ( 0 ..^ ( # ` L ) ) )' % ph
    L2 = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (p2, concl(w, ph, st)))
    io = w.s([], 'simpr', '( %s -> I e. ( 0 ..^ ( # ` L ) ) )' % p2)
    dr = w.s([L2(lw), io, w.inst('ttsesdrop')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (p2, ES(DROP('L', 'I')), ESL('( L ` I )'), ES(DROP('L', '( I + 1 )'))))
    li = w.s([L2(lw), io, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` I ) e. %s )' % (p2, SLOT))
    ew = w.s([w.s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi', "( ( L ` I ) e. %s -> %s e. Word Gamma' )" % (SLOT, ESL('( L ` I )')))
    ew2 = w.s([li, ew], 'syl', "( %s -> %s e. Word Gamma' )" % (p2, ESL('( L ` I )')))
    b1w = w.s([L2(lw), w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (p2, DROP('L', '( I + 1 )'), WSLOT))
    esw = w.s([b1w, w.inst('ttsescl')], 'syl', "( %s -> %s e. Word Gamma' )" % (p2, ES(DROP('L', '( I + 1 )'))))
    REST = '( %s ++ %s )' % (ES(DROP('L', '( I + 1 )')), Z0X)
    rw = w.s([esw, L2(zx), w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (p2, REST))
    e1 = w.s([dr], 'oveq1d', '( %s -> %s = ( ( %s ++ %s ) ++ %s ) )' % (p2, V('I'), ESL('( L ` I )'), ES(DROP('L', '( I + 1 )')), Z0X))
    e2 = w.s([ew2, esw, L2(zx), w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ %s ) )'
             % (p2, ESL('( L ` I )'), ES(DROP('L', '( I + 1 )')), Z0X, ESL('( L ` I )'), REST))
    e3 = w.s([w.s([e1, e2], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (p2, V('I'), ESL('( L ` I )'), REST))], 'fveq1d',
             '( %s -> ( %s ` 0 ) = ( ( %s ++ %s ) ` 0 ) )' % (p2, V('I'), ESL('( L ` I )'), REST))
    nb = w.s([li, rw, w.inst('ttslotblk')], 'syl2anc', '( %s -> ( ( %s ++ %s ) ` 0 ) =/= 0 )' % (p2, ESL('( L ` I )'), REST))
    hn = w.s([e3, nb], 'eqnetrd', '( %s -> ( %s ` 0 ) =/= 0 )' % (p2, V('I')))
    hn2 = w.s([hn], 'neneqd', '( %s -> -. ( %s ` 0 ) = 0 )' % (p2, V('I')))
    il = w.s([io, w.inst('elfzolt2')], 'syl', '( %s -> I < ( # ` L ) )' % p2)
    ir = w.s([w.s([io, w.inst('elfzoelz')], 'syl', '( %s -> I e. ZZ )' % p2)], 'zred', '( %s -> I e. RR )' % p2)
    ine = w.s([ir, il], 'ltned', '( %s -> I =/= ( # ` L ) )' % p2)
    ine2 = w.s([ine], 'neneqd', '( %s -> -. I = ( # ` L ) )' % p2)
    b2 = w.s([hn2, ine2], '2falsed', '( %s -> ( ( %s ` 0 ) = 0 <-> I = ( # ` L ) ) )' % (p2, V('I')))
    orr = w.s([ifz, w.inst('elfzr')], 'syl', '( %s -> ( I e. ( 0 ..^ ( # ` L ) ) \\/ I = ( # ` L ) ) )' % ph)
    w.qed([b2, b1, orr], 'mpjaodan', ST_ESHD)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
