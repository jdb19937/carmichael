"""T6b: the length lemmas of TM/Lists.lean (blueprint 2.4): ` entries_length_le `
by ~ wrdind , ` encListB_length_le ` , ` encList_length_le_of_lt_pow ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6blib import *
from cl import Closure

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

EL = '( encNatGam o. L )'


def PROP(X):
    """the induction property at the word X"""
    return '( ( M e. NN0 /\\ A. w e. ran %s ( # ` w ) <_ M ) -> ( # ` ( entries ` %s ) ) <_ ( ( # ` %s ) x. ( M + 1 ) ) )' % (X, X, X)


def tm2lentlen():
    lab = 'tm2lentlen'
    ph = '( L e. %s /\\ M e. NN0 /\\ %s )' % (WWB, RALW('L', 'M'))
    w = W(lab, 'The length of the entries of a list is at most ` ( # ` L ) x. ( M + 1 ) ` when '
               'every entry has at most ` M ` bits.  Lean: ` entries_length_le ` , by ~ wrdind .')
    YZ = '( y ++ <" z "> )'
    # the four substitution instances of the property
    def cg(X):
        st, new = w.wcongr(PROP('x'), {'x': X}, 'x = %s' % X, {'x': w.s([], 'id', '( x = %s -> x = %s )' % (X, X))})
        assert new == PROP(X), new
        return st
    c1 = cg('(/)'); c2 = cg('y'); c3 = cg(YZ); c4 = cg('L')
    # the base: entries (/) = (/), # (/) = 0
    pb = '( M e. NN0 /\\ A. w e. ran (/) ( # ` w ) <_ M )'
    mb = w.s([], 'simpl', '( %s -> M e. NN0 )' % pb)
    e0 = w.s([], 'tm2lent0', '( entries ` (/) ) = (/)')
    h0 = w.s([e0], 'fveq2i', '( # ` ( entries ` (/) ) ) = ( # ` (/) )')
    z0 = w.s([], 'hash0', '( # ` (/) ) = 0')
    h1 = w.s([h0, z0], 'eqtri', '( # ` ( entries ` (/) ) ) = 0')
    h1a = w.s([h1], 'a1i', '( %s -> ( # ` ( entries ` (/) ) ) = 0 )' % pb)
    m1 = w.s([mb, w.inst('peano2nn0')], 'syl', '( %s -> ( M + 1 ) e. NN0 )' % pb)
    m1c = w.s([m1], 'nn0cnd', '( %s -> ( M + 1 ) e. CC )' % pb)
    mz = w.s([m1c], 'mul02d', '( %s -> ( 0 x. ( M + 1 ) ) = 0 )' % pb)
    z1 = w.s([z0], 'oveq1i', '( ( # ` (/) ) x. ( M + 1 ) ) = ( 0 x. ( M + 1 ) )')
    z1a = w.s([z1], 'a1i', '( %s -> ( ( # ` (/) ) x. ( M + 1 ) ) = ( 0 x. ( M + 1 ) ) )' % pb)
    z2 = w.s([z1a, mz], 'eqtrd', '( %s -> ( ( # ` (/) ) x. ( M + 1 ) ) = 0 )' % pb)
    le0 = w.s([], '0le0', '0 <_ 0'); le0a = w.s([le0], 'a1i', '( %s -> 0 <_ 0 )' % pb)
    bs = w.s([h1a, z2, le0a], '3brtr4d', '( %s -> ( # ` ( entries ` (/) ) ) <_ ( ( # ` (/) ) x. ( M + 1 ) ) )' % pb)
    # PROP((/)) as a closed statement: ( pb -> goal ) is exactly PROP((/))
    assert PROP('(/)') == '( %s -> ( # ` ( entries ` (/) ) ) <_ ( ( # ` (/) ) x. ( M + 1 ) ) )' % pb
    # the step: y e. WWB, z e. WB, PROP(y) -> PROP(y ++ <" z ">)
    yz = '( y e. %s /\\ z e. %s )' % (WWB, WB)
    big = '( ( %s /\\ %s ) /\\ ( M e. NN0 /\\ %s ) )' % (yz, PROP('y'), RALW(YZ, 'M'))
    yy = w.s([w.s([], 'simpll', '( %s -> %s )' % (big, yz))], 'simpld', '( %s -> y e. %s )' % (big, WWB))
    zz = w.s([w.s([], 'simpll', '( %s -> %s )' % (big, yz))], 'simprd', '( %s -> z e. %s )' % (big, WB))
    ih = w.s([], 'simplr', '( %s -> %s )' % (big, PROP('y')))
    mm = w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 /\\ %s ) )' % (big, RALW(YZ, 'M')))], 'simpld', '( %s -> M e. NN0 )' % big)
    hb = w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 /\\ %s ) )' % (big, RALW(YZ, 'M')))], 'simprd', '( %s -> %s )' % (big, RALW(YZ, 'M')))
    zs = w.s([zz], 's1cld', '( %s -> <" z "> e. %s )' % (big, WWB))
    rn = w.s([yy, zs, w.inst('ccatrn')], 'syl2anc', '( %s -> ran %s = ( ran y u. ran <" z "> ) )' % (big, YZ))
    s1r = w.s([zz, w.inst('s1rn')], 'syl', '( %s -> ran <" z "> = { z } )' % big)
    s1r2 = w.s([s1r], 'uneq2d', '( %s -> ( ran y u. ran <" z "> ) = ( ran y u. { z } ) )' % big)
    rn2 = w.s([rn, s1r2], 'eqtrd', '( %s -> ran %s = ( ran y u. { z } ) )' % (big, YZ))
    u1 = w.s([], 'ssun1', 'ran y C_ ( ran y u. { z } )')
    u1a = w.s([u1], 'a1i', '( %s -> ran y C_ ( ran y u. { z } ) )' % big)
    u1b = w.s([u1a, rn2], 'sseqtrrd', '( %s -> ran y C_ ran %s )' % (big, YZ))
    hyi = w.s([u1b, w.inst('ssralv')], 'syl', '( %s -> ( %s -> %s ) )' % (big, RALW(YZ, 'M'), RALW('y', 'M')))
    hy2 = w.s([hyi, hb], 'mpd', '( %s -> %s )' % (big, RALW('y', 'M')))
    mh = w.s([mm, hy2], 'jca', '( %s -> ( M e. NN0 /\\ %s ) )' % (big, RALW('y', 'M')))
    ihc = w.s([ih, mh], 'mpd', '( %s -> ( # ` ( entries ` y ) ) <_ ( ( # ` y ) x. ( M + 1 ) ) )' % big)
    # ( # ` z ) <_ M from z e. ran YZ
    zv = w.s([zz], 'elexd', '( %s -> z e. _V )' % big)
    zsn = w.s([zv, w.inst('snidg')], 'syl', '( %s -> z e. { z } )' % big)
    zu2 = w.s([zsn, w.inst('elun2')], 'syl', '( %s -> z e. ( ran y u. { z } ) )' % big)
    zr = w.s([zu2, rn2], 'eleqtrrd', '( %s -> z e. ran %s )' % (big, YZ))
    cgw, neww = w.wcongr('( # ` w ) <_ M', {'w': 'z'}, 'w = z', {'w': w.s([], 'id', '( w = z -> w = z )')})
    lz = w.s([cgw, hb, zr], 'rspcdva', '( %s -> ( # ` z ) <_ M )' % big)
    # the lengths
    es = w.s([yy, zz, w.inst('tm2lentsnoc')], 'syl2anc', '( %s -> ( entries ` %s ) = ( ( entries ` y ) ++ ( z ++ <" 4 "> ) ) )' % (big, YZ))
    es2 = w.s([es], 'fveq2d', '( %s -> ( # ` ( entries ` %s ) ) = ( # ` ( ( entries ` y ) ++ ( z ++ <" 4 "> ) ) ) )' % (big, YZ))
    ey = w.s([yy, w.inst('tm2lentcl')], 'syl', '( %s -> ( entries ` y ) e. %s )' % (big, WG))
    zg = wbtog(w, big, 'z', zz)
    c4s = s1g(w, big, '4')
    z4 = ccatg(w, big, 'z', '<" 4 ">', zg, c4s)
    l1 = w.s([ey, z4, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` ( ( entries ` y ) ++ ( z ++ <" 4 "> ) ) ) = ( ( # ` ( entries ` y ) ) + ( # ` ( z ++ <" 4 "> ) ) ) )' % big)
    l2 = w.s([zg, c4s, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` ( z ++ <" 4 "> ) ) = ( ( # ` z ) + ( # ` <" 4 "> ) ) )' % big)
    s4 = w.s([], 's1len', '( # ` <" 4 "> ) = 1')
    s4a = w.s([s4], 'oveq2i', '( ( # ` z ) + ( # ` <" 4 "> ) ) = ( ( # ` z ) + 1 )')
    s4b = w.s([s4a], 'a1i', '( %s -> ( ( # ` z ) + ( # ` <" 4 "> ) ) = ( ( # ` z ) + 1 ) )' % big)
    l3 = w.s([l2, s4b], 'eqtrd', '( %s -> ( # ` ( z ++ <" 4 "> ) ) = ( ( # ` z ) + 1 ) )' % big)
    l4 = w.s([l3], 'oveq2d', '( %s -> ( ( # ` ( entries ` y ) ) + ( # ` ( z ++ <" 4 "> ) ) ) = ( ( # ` ( entries ` y ) ) + ( ( # ` z ) + 1 ) ) )' % big)
    l5 = w.s([es2, l1], 'eqtrd', '( %s -> ( # ` ( entries ` %s ) ) = ( ( # ` ( entries ` y ) ) + ( # ` ( z ++ <" 4 "> ) ) ) )' % (big, YZ))
    l6 = w.s([l5, l4], 'eqtrd', '( %s -> ( # ` ( entries ` %s ) ) = ( ( # ` ( entries ` y ) ) + ( ( # ` z ) + 1 ) ) )' % (big, YZ))
    ly = w.s([yy, zs, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` y ) + ( # ` <" z "> ) ) )' % (big, YZ))
    sz = w.s([], 's1len', '( # ` <" z "> ) = 1')
    sza = w.s([sz], 'oveq2i', '( ( # ` y ) + ( # ` <" z "> ) ) = ( ( # ` y ) + 1 )')
    szb = w.s([sza], 'a1i', '( %s -> ( ( # ` y ) + ( # ` <" z "> ) ) = ( ( # ` y ) + 1 ) )' % big)
    ly2 = w.s([ly, szb], 'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` y ) + 1 ) )' % (big, YZ))
    ly3 = w.s([ly2], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( M + 1 ) ) = ( ( ( # ` y ) + 1 ) x. ( M + 1 ) ) )' % (big, YZ))
    # the arithmetic
    ny = w.s([yy, w.inst('lencl')], 'syl', '( %s -> ( # ` y ) e. NN0 )' % big)
    nz = w.s([zz, w.inst('lencl')], 'syl', '( %s -> ( # ` z ) e. NN0 )' % big)
    ne = w.s([ey, w.inst('lencl')], 'syl', '( %s -> ( # ` ( entries ` y ) ) e. NN0 )' % big)
    cl = Closure(w, big, {'( # ` y )': ny, '( # ` z )': nz, '( # ` ( entries ` y ) )': ne, 'M': mm})
    y0 = w.s([ny], 'nn0ge0d', '( %s -> 0 <_ ( # ` y ) )' % big)
    ar = linarith(w, big, [ihc, lz, y0], '( ( # ` ( entries ` y ) ) + ( ( # ` z ) + 1 ) ) <_ ( ( ( # ` y ) + 1 ) x. ( M + 1 ) )', closure=cl, products=True)
    fin = w.s([l6, ly3, ar], '3brtr4d', '( %s -> ( # ` ( entries ` %s ) ) <_ ( ( # ` %s ) x. ( M + 1 ) ) )' % (big, YZ, YZ))
    ex1 = w.s([fin], 'ex', '( ( %s /\\ %s ) -> %s )' % (yz, PROP('y'), PROP(YZ)))
    ex2 = w.s([ex1], 'ex', '( %s -> ( %s -> %s ) )' % (yz, PROP('y'), PROP(YZ)))
    ind = w.s([c1, c2, c3, c4, bs, ex2], 'wrdind', '( L e. %s -> %s )' % (WWB, PROP('L')))
    w.qed([ind], '3impib', '( %s -> ( # ` ( entries ` L ) ) <_ ( ( # ` L ) x. ( M + 1 ) ) )' % ph)
    return w.run()


def tm2lencblen():
    lab = 'tm2lencblen'
    ph = '( L e. %s /\\ M e. NN0 /\\ %s )' % (WWB, RALW('L', 'M'))
    w = W(lab, 'The length of an encoded list.  Lean: ` encListB_length_le ` .')
    ll = w.s([], 'simp1', '( %s -> L e. %s )' % (ph, WWB))
    mm = w.s([], 'simp2', '( %s -> M e. NN0 )' % ph)
    el = w.s([], 'tm2lentlen', '( %s -> ( # ` ( entries ` L ) ) <_ ( ( # ` L ) x. ( M + 1 ) ) )' % ph)
    ev = w.s([ll, w.inst('tm2lencbval')], 'syl', '( %s -> ( encListB ` L ) = ( ( entries ` L ) ++ <" 2 "> ) )' % ph)
    ev2 = w.s([ev], 'fveq2d', '( %s -> ( # ` ( encListB ` L ) ) = ( # ` ( ( entries ` L ) ++ <" 2 "> ) ) )' % ph)
    ec = w.s([ll, w.inst('tm2lentcl')], 'syl', '( %s -> ( entries ` L ) e. %s )' % (ph, WG))
    c2 = s1g(w, ph, '2')
    l1 = w.s([ec, c2, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` ( ( entries ` L ) ++ <" 2 "> ) ) = ( ( # ` ( entries ` L ) ) + ( # ` <" 2 "> ) ) )' % ph)
    s2 = w.s([], 's1len', '( # ` <" 2 "> ) = 1')
    s2a = w.s([s2], 'oveq2i', '( ( # ` ( entries ` L ) ) + ( # ` <" 2 "> ) ) = ( ( # ` ( entries ` L ) ) + 1 )')
    s2b = w.s([s2a], 'a1i', '( %s -> ( ( # ` ( entries ` L ) ) + ( # ` <" 2 "> ) ) = ( ( # ` ( entries ` L ) ) + 1 ) )' % ph)
    l2 = w.s([ev2, l1], 'eqtrd', '( %s -> ( # ` ( encListB ` L ) ) = ( ( # ` ( entries ` L ) ) + ( # ` <" 2 "> ) ) )' % ph)
    l3 = w.s([l2, s2b], 'eqtrd', '( %s -> ( # ` ( encListB ` L ) ) = ( ( # ` ( entries ` L ) ) + 1 ) )' % ph)
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    ne = w.s([ec, w.inst('lencl')], 'syl', '( %s -> ( # ` ( entries ` L ) ) e. NN0 )' % ph)
    cl = Closure(w, ph, {'( # ` L )': nl, '( # ` ( entries ` L ) )': ne, 'M': mm})
    PR = '( ( # ` L ) x. ( M + 1 ) )'
    cl.atom(PR)
    ar = linarith(w, ph, [el], '( ( # ` ( entries ` L ) ) + 1 ) <_ ( %s + 1 )' % PR, closure=cl)
    w.qed([l3, ar], 'eqbrtrd', '( %s -> ( # ` ( encListB ` L ) ) <_ ( %s + 1 ) )' % (ph, PR))
    return w.run()


def tm2lenclen():
    lab = 'tm2lenclen'
    ph = '( L e. Word NN0 /\\ B e. NN0 /\\ %s )' % RALA('L')
    w = W(lab, 'The length of an encoded list of numbers below ` 2 ^ B ` .  Lean: '
               '` encList_length_le_of_lt_pow ` ; ~ tm2lencblen at ` ( encNatGam o. L ) ` with ~ tm2lrnenc .')
    ll = w.s([], 'simp1', '( %s -> L e. Word NN0 )' % ph)
    bb = w.s([], 'simp2', '( %s -> B e. NN0 )' % ph)
    ha = w.s([], 'simp3', '( %s -> %s )' % (ph, RALA('L')))
    elc = w.s([ll, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. %s )' % (ph, EL, WWB))
    bw = w.s([ll, bb, ha, w.inst('tm2lrnenc')], 'syl3anc', '( %s -> %s )' % (ph, RALW(EL)))
    le = w.s([elc, bb, bw, w.inst('tm2lencblen')], 'syl3anc', '( %s -> ( # ` %s ) <_ ( ( ( # ` %s ) x. ( B + 1 ) ) + 1 ) )' % (ph, ENCB(EL), EL))
    eq = w.s([ll, w.inst('tm2lenceq')], 'syl', '( %s -> %s = %s )' % (ph, ENC('L'), ENCB(EL)))
    eq2a = w.s([eq], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENC('L'), ENCB(EL)))
    eq2 = w.s([eq2a], 'eqcomd', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ENCB(EL), ENC('L')))
    ef = w.s([], 'tm2lbitf', 'encNatGam : NN0 --> %s' % WB)
    efa = w.s([ef], 'a1i', '( %s -> encNatGam : NN0 --> %s )' % (ph, WB))
    ln = w.s([ll, efa, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` L ) )' % (ph, EL))
    ln2 = w.s([ln], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( B + 1 ) ) = ( ( # ` L ) x. ( B + 1 ) ) )' % (ph, EL))
    ln3 = w.s([ln2], 'oveq1d', '( %s -> ( ( ( # ` %s ) x. ( B + 1 ) ) + 1 ) = ( ( ( # ` L ) x. ( B + 1 ) ) + 1 ) )' % (ph, EL))
    w.qed([eq2, ln3, le], '3brtr3d', '( %s -> ( # ` %s ) <_ ( ( ( # ` L ) x. ( B + 1 ) ) + 1 ) )' % (ph, ENC('L')))
    return w.run()


if __name__ == '__main__':
    if want('tm2lentlen'): tm2lentlen()
    if want('tm2lencblen'): tm2lencblen()
    if want('tm2lenclen'): tm2lenclen()
