"""T6: the list encodings `entries`, `encListB`, `encList` (TM/Lists.lean)
--- value, closure and equation lemmas (blueprint 3.1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2lbits():
    w = W('tm2lbits', "The bit letters of ` Gamma' ` .  Lean: ` Gamma'.bit b ` for ` b : Bool ` .")
    s = w.s([], 'ssun2', "%s C_ ( ( { 0 , 2 } u. { 3 , 4 } ) u. %s )" % (BITS, BITS))
    g = w.s([], 'df-gamma', "Gamma' = ( ( { 0 , 2 } u. { 3 , 4 } ) u. %s )" % BITS)
    w.qed([s, g], 'sseqtrri', "%s C_ Gamma'" % BITS)
    return w.run()


def tm2lwbss():
    w = W('tm2lwbss', "A word of bit letters is a word over ` Gamma' ` .")
    b = w.s([], 'tm2lbits', "%s C_ Gamma'" % BITS)
    i = w.inst('sswrd')
    w.qed([b, i], 'ax-mp', '%s C_ %s' % (WB, WG))
    return w.run()


def tm2lentpf():
    w = W('tm2lentpf', 'The entry mapping of ` entries ` (an entry followed by a comma) maps bit words to words over ` Gamma\' ` .')
    e = w.s([], 'eqid', '%s = %s' % (PFW, PFW))
    A = 'w e. %s' % WB
    ss = w.s([], 'tm2lwbss', '%s C_ %s' % (WB, WG))
    i = w.s([], 'id', '( %s -> w e. %s )' % (A, WB))
    wg = w.s([ss, i], 'sselid', '( %s -> w e. %s )' % (A, WG))
    g = gamlet(w, A, '4')
    c = w.s([wg, g, w.inst('ccatws1cl')], 'syl2anc', '( %s -> ( w ++ <" 4 "> ) e. %s )' % (A, WG))
    w.qed([e, c], 'fmpti', '%s : %s --> %s' % (PFW, WB, WG))
    return w.run()


def tm2lentpfv():
    w = W('tm2lentpfv', 'Value of the entry mapping of ` entries ` .')
    c = w.s([], 'oveq1', '( w = W -> ( w ++ <" 4 "> ) = ( W ++ <" 4 "> ) )')
    e = w.s([], 'eqid', '%s = %s' % (PFW, PFW))
    x = w.s([], 'ovex', '( W ++ <" 4 "> ) e. _V')
    w.qed([c, e, x], 'fvmpt', '( W e. %s -> ( %s ` W ) = ( W ++ <" 4 "> ) )' % (WB, PFW))
    return w.run()


def tm2lentval():
    w = W('tm2lentval', 'Value of ` entries ` : the monoid sum of the entries each followed by a comma.  Lean: ` def entries ` (TM/Lists.lean).')
    c1 = w.s([], 'coeq2', '( l = L -> ( %s o. l ) = ( %s o. L ) )' % (PFW, PFW))
    c = w.s([c1], 'oveq2d', '( l = L -> %s = %s )' % (FLATW('l'), FLATW('L')))
    e = w.s([], 'df-tm2lent', 'entries = ( l e. %s |-> %s )' % (WWB, FLATW('l')))
    x = w.s([], 'ovex', '%s e. _V' % FLATW('L'))
    w.qed([c, e, x], 'fvmpt', '( L e. %s -> %s = %s )' % (WWB, ENT('L'), FLATW('L')))
    return w.run()


def tm2lentcl():
    w = W('tm2lentcl', "The entries of a list of bit words form a word over ` Gamma' ` .")
    A = 'L e. %s' % WWB
    v = w.s([], 'tm2lentval', '( %s -> %s = %s )' % (A, ENT('L'), FLATW('L')))
    i = w.s([], 'id', '( %s -> L e. %s )' % (A, WWB))
    f = closedw(w, A, 'tm2lentpf', '%s : %s --> %s' % (PFW, WB, WG))
    c = w.s([i, f, w.inst('wrdco')], 'syl2anc', '( %s -> ( %s o. L ) e. %s )' % (A, PFW, WWG))
    g = w.s([c, w.inst('gsumgamcl')], 'syl', '( %s -> %s e. %s )' % (A, FLATW('L'), WG))
    w.qed([v, g], 'eqeltrd', '( %s -> %s e. %s )' % (A, ENT('L'), WG))
    return w.run()


def tm2lent0():
    w = W('tm2lent0', 'The entries of the empty list.  Lean: ` entries_nil ` .')
    z = w.s([], 'wrd0', '(/) e. %s' % WWB)
    v = w.s([z, w.inst('tm2lentval')], 'ax-mp', '%s = %s' % (ENT('(/)'), FLATW('(/)')))
    c = w.s([], 'co02', '( %s o. (/) ) = (/)' % PFW)
    o = w.s([c], 'oveq2i', '%s = ( %s gsum (/) )' % (FLATW('(/)'), FM))
    g = w.s([], 'gsumgam0', '( %s gsum (/) ) = (/)' % FM)
    e = w.s([o, g], 'eqtri', '%s = (/)' % FLATW('(/)'))
    w.qed([v, e], 'eqtri', '%s = (/)' % ENT('(/)'))
    return w.run()


def tm2lentcc():
    w = W('tm2lentcc', 'The entries of a concatenation of lists.  Lean: ` entries_append ` .')
    A = '( L e. %s /\\ U e. %s )' % (WWB, WWB)
    l1 = w.s([], 'simpl', '( %s -> L e. %s )' % (A, WWB))
    u1 = w.s([], 'simpr', '( %s -> U e. %s )' % (A, WWB))
    lu = w.s([l1, u1, w.inst('ccatcl')], 'syl2anc', '( %s -> ( L ++ U ) e. %s )' % (A, WWB))
    v = w.s([lu, w.inst('tm2lentval')], 'syl', '( %s -> %s = %s )' % (A, ENT('( L ++ U )'), FLATW('( L ++ U )')))
    f = closedw(w, A, 'tm2lentpf', '%s : %s --> %s' % (PFW, WB, WG))
    c = w.s([l1, u1, f, w.inst('ccatco')], 'syl3anc', '( %s -> ( %s o. ( L ++ U ) ) = ( ( %s o. L ) ++ ( %s o. U ) ) )' % (A, PFW, PFW, PFW))
    o = w.s([c], 'oveq2d', '( %s -> %s = ( %s gsum ( ( %s o. L ) ++ ( %s o. U ) ) ) )' % (A, FLATW('( L ++ U )'), FM, PFW, PFW))
    cl = w.s([l1, f, w.inst('wrdco')], 'syl2anc', '( %s -> ( %s o. L ) e. %s )' % (A, PFW, WWG))
    cu = w.s([u1, f, w.inst('wrdco')], 'syl2anc', '( %s -> ( %s o. U ) e. %s )' % (A, PFW, WWG))
    g = w.s([cl, cu, w.inst('gsumgamccat')], 'syl2anc', '( %s -> ( %s gsum ( ( %s o. L ) ++ ( %s o. U ) ) ) = ( %s ++ %s ) )' % (A, FM, PFW, PFW, FLATW('L'), FLATW('U')))
    t = w.s([o, g], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (A, FLATW('( L ++ U )'), FLATW('L'), FLATW('U')))
    vl = w.s([l1, w.inst('tm2lentval')], 'syl', '( %s -> %s = %s )' % (A, ENT('L'), FLATW('L')))
    vu = w.s([u1, w.inst('tm2lentval')], 'syl', '( %s -> %s = %s )' % (A, ENT('U'), FLATW('U')))
    o2 = w.s([vl, vu], 'oveq12d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (A, ENT('L'), ENT('U'), FLATW('L'), FLATW('U')))
    t2 = w.s([t, o2], 'eqtr4d', '( %s -> %s = ( %s ++ %s ) )' % (A, FLATW('( L ++ U )'), ENT('L'), ENT('U')))
    w.qed([v, t2], 'eqtrd', '( %s -> %s = ( %s ++ %s ) )' % (A, ENT('( L ++ U )'), ENT('L'), ENT('U')))
    return w.run()


def tm2lents1():
    w = W('tm2lents1', 'The entries of a one-element list: the entry followed by a comma.')
    A = 'W e. %s' % WB
    i = w.s([], 'id', '( %s -> W e. %s )' % (A, WB))
    s1 = w.s([i], 's1cld', '( %s -> <" W "> e. %s )' % (A, WWB))
    v = w.s([s1, w.inst('tm2lentval')], 'syl', '( %s -> %s = %s )' % (A, ENT('<" W ">'), FLATW('<" W ">')))
    f = closedw(w, A, 'tm2lentpf', '%s : %s --> %s' % (PFW, WB, WG))
    c = w.s([i, f, w.inst('s1co')], 'syl2anc', '( %s -> ( %s o. <" W "> ) = <" ( %s ` W ) "> )' % (A, PFW, PFW))
    o = w.s([c], 'oveq2d', '( %s -> %s = ( %s gsum <" ( %s ` W ) "> ) )' % (A, FLATW('<" W ">'), FM, PFW))
    fv = w.s([f, i, w.inst('ffvelcdm')], 'syl2anc', '( %s -> ( %s ` W ) e. %s )' % (A, PFW, WG))
    g = w.s([fv, w.inst('gsumgams1')], 'syl', '( %s -> ( %s gsum <" ( %s ` W ) "> ) = ( %s ` W ) )' % (A, FM, PFW, PFW))
    pv = w.s([], 'tm2lentpfv', '( %s -> ( %s ` W ) = ( W ++ <" 4 "> ) )' % (A, PFW))
    g2 = w.s([g, pv], 'eqtrd', '( %s -> ( %s gsum <" ( %s ` W ) "> ) = ( W ++ <" 4 "> ) )' % (A, FM, PFW))
    t = w.s([o, g2], 'eqtrd', '( %s -> %s = ( W ++ <" 4 "> ) )' % (A, FLATW('<" W ">')))
    w.qed([v, t], 'eqtrd', '( %s -> %s = ( W ++ <" 4 "> ) )' % (A, ENT('<" W ">')))
    return w.run()


def tm2lentcons():
    w = W('tm2lentcons', 'The entries of a list with a new head entry.  Lean: ` entries_cons ` .')
    A = '( W e. %s /\\ L e. %s )' % (WB, WWB)
    w1 = w.s([], 'simpl', '( %s -> W e. %s )' % (A, WB))
    l1 = w.s([], 'simpr', '( %s -> L e. %s )' % (A, WWB))
    s1 = w.s([w1], 's1cld', '( %s -> <" W "> e. %s )' % (A, WWB))
    cc = w.s([s1, l1, w.inst('tm2lentcc')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (A, ENT('( <" W "> ++ L )'), ENT('<" W ">'), ENT('L')))
    e1 = w.s([w1, w.inst('tm2lents1')], 'syl', '( %s -> %s = ( W ++ <" 4 "> ) )' % (A, ENT('<" W ">')))
    o = w.s([e1], 'oveq1d', '( %s -> ( %s ++ %s ) = ( ( W ++ <" 4 "> ) ++ %s ) )' % (A, ENT('<" W ">'), ENT('L'), ENT('L')))
    wg = wbtog(w, A, 'W', w1)
    c4 = s1g(w, A, '4')
    el = w.s([l1, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (A, ENT('L'), WG))
    a = w.s([wg, c4, el, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( W ++ <" 4 "> ) ++ %s ) = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENT('L'), ENT('L')))
    t = w.s([o, a], 'eqtrd', '( %s -> ( %s ++ %s ) = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENT('<" W ">'), ENT('L'), ENT('L')))
    w.qed([cc, t], 'eqtrd', '( %s -> %s = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENT('( <" W "> ++ L )'), ENT('L')))
    return w.run()


def tm2lentsnoc():
    w = W('tm2lentsnoc', 'The entries of a list with a new last entry.')
    A = '( L e. %s /\\ W e. %s )' % (WWB, WB)
    l1 = w.s([], 'simpl', '( %s -> L e. %s )' % (A, WWB))
    w1 = w.s([], 'simpr', '( %s -> W e. %s )' % (A, WB))
    s1 = w.s([w1], 's1cld', '( %s -> <" W "> e. %s )' % (A, WWB))
    cc = w.s([l1, s1, w.inst('tm2lentcc')], 'syl2anc', '( %s -> %s = ( %s ++ %s ) )' % (A, ENT('( L ++ <" W "> )'), ENT('L'), ENT('<" W ">')))
    e1 = w.s([w1, w.inst('tm2lents1')], 'syl', '( %s -> %s = ( W ++ <" 4 "> ) )' % (A, ENT('<" W ">')))
    o = w.s([e1], 'oveq2d', '( %s -> ( %s ++ %s ) = ( %s ++ ( W ++ <" 4 "> ) ) )' % (A, ENT('L'), ENT('<" W ">'), ENT('L')))
    w.qed([cc, o], 'eqtrd', '( %s -> %s = ( %s ++ ( W ++ <" 4 "> ) ) )' % (A, ENT('( L ++ <" W "> )'), ENT('L')))
    return w.run()


# ---------------------------------------------------------------- encListB

def tm2lencbval():
    w = W('tm2lencbval', 'Value of ` encListB ` : the entries, then ` bra = 2 ` .  Lean: ` def encListB ` .')
    c1 = w.s([], 'fveq2', '( l = L -> ( entries ` l ) = ( entries ` L ) )')
    c = w.s([c1], 'oveq1d', '( l = L -> ( ( entries ` l ) ++ <" 2 "> ) = ( %s ++ <" 2 "> ) )' % ENT('L'))
    e = w.s([], 'df-tm2lencb', 'encListB = ( l e. %s |-> ( ( entries ` l ) ++ <" 2 "> ) )' % WWB)
    x = w.s([], 'ovex', '( %s ++ <" 2 "> ) e. _V' % ENT('L'))
    w.qed([c, e, x], 'fvmpt', '( L e. %s -> %s = ( %s ++ <" 2 "> ) )' % (WWB, ENCB('L'), ENT('L')))
    return w.run()


def tm2lencbcl():
    w = W('tm2lencbcl', "A list of bit words on a stack is a word over ` Gamma' ` .")
    A = 'L e. %s' % WWB
    v = w.s([], 'tm2lencbval', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENCB('L'), ENT('L')))
    e = w.s([], 'tm2lentcl', '( %s -> %s e. %s )' % (A, ENT('L'), WG))
    g = gamlet(w, A, '2')
    c = w.s([e, g, w.inst('ccatws1cl')], 'syl2anc', '( %s -> ( %s ++ <" 2 "> ) e. %s )' % (A, ENT('L'), WG))
    w.qed([v, c], 'eqeltrd', '( %s -> %s e. %s )' % (A, ENCB('L'), WG))
    return w.run()


def tm2lencb0():
    w = W('tm2lencb0', 'The empty list on a stack is a single ` bra ` .  Lean: ` encListB_nil ` .')
    z = w.s([], 'wrd0', '(/) e. %s' % WWB)
    v = w.s([z, w.inst('tm2lencbval')], 'ax-mp', '%s = ( %s ++ <" 2 "> )' % (ENCB('(/)'), ENT('(/)')))
    e = w.s([], 'tm2lent0', '%s = (/)' % ENT('(/)'))
    o = w.s([e], 'oveq1i', '( %s ++ <" 2 "> ) = ( (/) ++ <" 2 "> )' % ENT('(/)'))
    g = w.s([], 'gamma2', "2 e. Gamma'")
    s = w.s([g, w.inst('s1cl')], 'ax-mp', '<" 2 "> e. %s' % WG)
    l = w.s([s, w.inst('ccatlid')], 'ax-mp', '( (/) ++ <" 2 "> ) = <" 2 ">')
    t = w.s([o, l], 'eqtri', '( %s ++ <" 2 "> ) = <" 2 ">' % ENT('(/)'))
    w.qed([v, t], 'eqtri', '%s = <" 2 ">' % ENCB('(/)'))
    return w.run()


def tm2lencbcons():
    w = W('tm2lencbcons', 'A list with a new head entry on a stack.  Lean: ` encListB_cons ` .')
    A = '( W e. %s /\\ L e. %s )' % (WB, WWB)
    w1 = w.s([], 'simpl', '( %s -> W e. %s )' % (A, WB))
    l1 = w.s([], 'simpr', '( %s -> L e. %s )' % (A, WWB))
    s1 = w.s([w1], 's1cld', '( %s -> <" W "> e. %s )' % (A, WWB))
    wl = w.s([s1, l1, w.inst('ccatcl')], 'syl2anc', '( %s -> ( <" W "> ++ L ) e. %s )' % (A, WWB))
    v = w.s([wl, w.inst('tm2lencbval')], 'syl', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENCB('( <" W "> ++ L )'), ENT('( <" W "> ++ L )')))
    c = w.s([], 'tm2lentcons', '( %s -> %s = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENT('( <" W "> ++ L )'), ENT('L')))
    o = w.s([c], 'oveq1d', '( %s -> ( %s ++ <" 2 "> ) = ( ( W ++ ( <" 4 "> ++ %s ) ) ++ <" 2 "> ) )' % (A, ENT('( <" W "> ++ L )'), ENT('L')))
    wg = wbtog(w, A, 'W', w1)
    c4 = s1g(w, A, '4'); c2 = s1g(w, A, '2')
    el = w.s([l1, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (A, ENT('L'), WG))
    c4e = ccatg(w, A, '<" 4 ">', ENT('L'), c4, el)
    a1 = w.s([wg, c4e, c2, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( W ++ ( <" 4 "> ++ %s ) ) ++ <" 2 "> ) = ( W ++ ( ( <" 4 "> ++ %s ) ++ <" 2 "> ) ) )' % (A, ENT('L'), ENT('L')))
    a2 = w.s([c4, el, c2, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ <" 2 "> ) = ( <" 4 "> ++ ( %s ++ <" 2 "> ) ) )' % (A, ENT('L'), ENT('L')))
    vl = w.s([l1, w.inst('tm2lencbval')], 'syl', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENCB('L'), ENT('L')))
    a3 = w.s([vl], 'oveq2d', '( %s -> ( <" 4 "> ++ %s ) = ( <" 4 "> ++ ( %s ++ <" 2 "> ) ) )' % (A, ENCB('L'), ENT('L')))
    a4 = w.s([a2, a3], 'eqtr4d', '( %s -> ( ( <" 4 "> ++ %s ) ++ <" 2 "> ) = ( <" 4 "> ++ %s ) )' % (A, ENT('L'), ENCB('L')))
    a5 = w.s([a4], 'oveq2d', '( %s -> ( W ++ ( ( <" 4 "> ++ %s ) ++ <" 2 "> ) ) = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENT('L'), ENCB('L')))
    t = w.s([a1, a5], 'eqtrd', '( %s -> ( ( W ++ ( <" 4 "> ++ %s ) ) ++ <" 2 "> ) = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENT('L'), ENCB('L')))
    t2 = w.s([o, t], 'eqtrd', '( %s -> ( %s ++ <" 2 "> ) = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENT('( <" W "> ++ L )'), ENCB('L')))
    w.qed([v, t2], 'eqtrd', '( %s -> %s = ( W ++ ( <" 4 "> ++ %s ) ) )' % (A, ENCB('( <" W "> ++ L )'), ENCB('L')))
    return w.run()


def tm2lencbcc():
    w = W('tm2lencbcc', 'A list on a stack followed by the rest of the stack: the entries, then ` bra ` , then the rest.  Lean: ` encListB_eq_entries_append ` .')
    A = '( L e. %s /\\ R e. %s )' % (WWB, WG)
    l1 = w.s([], 'simpl', '( %s -> L e. %s )' % (A, WWB))
    r1 = w.s([], 'simpr', '( %s -> R e. %s )' % (A, WG))
    v = w.s([l1, w.inst('tm2lencbval')], 'syl', '( %s -> %s = ( %s ++ <" 2 "> ) )' % (A, ENCB('L'), ENT('L')))
    o = w.s([v], 'oveq1d', '( %s -> ( %s ++ R ) = ( ( %s ++ <" 2 "> ) ++ R ) )' % (A, ENCB('L'), ENT('L')))
    el = w.s([l1, w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (A, ENT('L'), WG))
    c2 = s1g(w, A, '2')
    a = w.s([el, c2, r1, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ <" 2 "> ) ++ R ) = ( %s ++ ( <" 2 "> ++ R ) ) )' % (A, ENT('L'), ENT('L')))
    w.qed([o, a], 'eqtrd', '( %s -> ( %s ++ R ) = ( %s ++ ( <" 2 "> ++ R ) ) )' % (A, ENCB('L'), ENT('L')))
    return w.run()


if __name__ == '__main__':
    for f in [tm2lbits, tm2lwbss, tm2lentpf, tm2lentpfv, tm2lentval, tm2lentcl, tm2lent0,
              tm2lentcc, tm2lents1, tm2lentcons, tm2lentsnoc,
              tm2lencbval, tm2lencbcl, tm2lencb0, tm2lencbcons, tm2lencbcc]:
        if want(f.__name__): f()
