"""T-MD: the N-level content of TM/Canon.lean (blueprint D1): the canonical
word ` ( encodeNat ` ( toNat ` L ) ) ` is ` L ` without its high zeros, and
its reversal is what the strip loop sees."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LL_ = 'L e. Word 2o'
E = E_('L')
NZ_ = NZ('L')
REP = REP0(NZ_)
W2 = 'Word 2o'


def common(w, ph):
    ll = w.s([], 'id', '( %s -> %s )' % (ph, LL_))
    tn = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` L ) e. NN0 )' % ph)
    ec = w.s([tn, w.inst('encnatcl')], 'syl', '( %s -> %s e. %s )' % (ph, E, W2))
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    ne = w.s([ec, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, E))
    le = w.s([ll, w.inst('bwstriplen')], 'syl', '( %s -> ( # ` %s ) <_ ( # ` L ) )' % (ph, E))
    sb = w.s([ne, nl, w.inst('nn0sub')], 'syl2anc', '( %s -> ( ( # ` %s ) <_ ( # ` L ) <-> %s e. NN0 ) )' % (ph, E, NZ_))
    nz = w.s([sb, le], 'mpbid', '( %s -> %s e. NN0 )' % (ph, NZ_))
    r0 = w.s([nz, w.inst('bwrep0')], 'syl', '( %s -> %s = ( 0 bwrd %s ) )' % (ph, REP, NZ_))
    z = w.s([], '0z', '0 e. ZZ'); za = w.s([z], 'a1i', '( %s -> 0 e. ZZ )' % ph)
    bc = w.s([za, nz, w.inst('bwrdcl')], 'syl2anc', '( %s -> ( 0 bwrd %s ) e. %s )' % (ph, NZ_, W2))
    rc = w.s([r0, bc], 'eqeltrd', '( %s -> %s e. %s )' % (ph, REP, W2))
    return dict(ll=ll, tn=tn, ec=ec, nl=nl, ne=ne, nz=nz, rc=rc)


def bwstriplen():
    lab = 'bwstriplen'
    ph = LL_
    w = W(lab, 'The canonical form of a bit word is no longer than the word.  Lean: '
               '` stripHigh_length_le ` (blueprint D1: ` stripHigh l ` is ` encodeNat ( toNat l ) ` ).')
    ll = w.s([], 'id', '( %s -> %s )' % (ph, LL_))
    tn = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` L ) e. NN0 )' % ph)
    a = w.s([tn, w.inst('encnatlenbl')], 'syl', '( %s -> ( # ` %s ) = ( bl ` ( toNat ` L ) ) )' % (ph, E))
    b = w.s([ll, w.inst('bllelen')], 'syl', '( %s -> ( bl ` ( toNat ` L ) ) <_ ( # ` L ) )' % ph)
    w.qed([a, b], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( # ` L ) )' % (ph, E))
    return w.run()


def bwstriph():
    lab = 'bwstriph'
    ph = LL_
    RHS = '( %s ++ %s )' % (E, REP)
    w = W(lab, 'A bit word is its canonical form followed by its high zeros.  Lean: '
               '` stripHigh_append_replicate ` with ` stripHigh_eq_encodeNat ` ; by ~ bwuniq '
               'from ~ tonatrep0c and ~ tonatencnat .')
    u = common(w, ph)
    rhc = w.s([u['ec'], u['rc'], w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. %s )' % (ph, RHS, W2))
    bi = w.s([u['ll'], rhc, w.inst('bwuniq')], 'syl2anc',
             '( %s -> ( L = %s <-> ( ( # ` L ) = ( # ` %s ) /\\ ( toNat ` L ) = ( toNat ` %s ) ) ) )' % (ph, RHS, RHS, RHS))
    # the length
    cl = w.s([u['ec'], u['rc'], w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (ph, RHS, E, REP))
    ex0 = w.s([], '0ex', '(/) e. _V'); ex0a = w.s([ex0], 'a1i', '( %s -> (/) e. _V )' % ph)
    rl = w.s([ex0a, u['nz'], w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, REP, NZ_))
    cl2 = w.s([rl], 'oveq2d', '( %s -> ( ( # ` %s ) + ( # ` %s ) ) = ( ( # ` %s ) + %s ) )' % (ph, E, REP, E, NZ_))
    nec = w.s([u['ne']], 'nn0cnd', '( %s -> ( # ` %s ) e. CC )' % (ph, E))
    nlc = w.s([u['nl']], 'nn0cnd', '( %s -> ( # ` L ) e. CC )' % ph)
    pc = w.s([nec, nlc, w.inst('pncan3')], 'syl2anc', '( %s -> ( ( # ` %s ) + %s ) = ( # ` L ) )' % (ph, E, NZ_))
    l1 = w.s([cl, cl2], 'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` %s ) + %s ) )' % (ph, RHS, E, NZ_))
    l2 = w.s([l1, pc], 'eqtrd', '( %s -> ( # ` %s ) = ( # ` L ) )' % (ph, RHS))
    l3 = w.s([l2], 'eqcomd', '( %s -> ( # ` L ) = ( # ` %s ) )' % (ph, RHS))
    # the value
    t1 = w.s([u['ec'], u['nz'], w.inst('tonatrep0c')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( toNat ` %s ) )' % (ph, RHS, E))
    t2 = w.s([u['tn'], w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = ( toNat ` L ) )' % (ph, E))
    t3 = w.s([t1, t2], 'eqtrd', '( %s -> ( toNat ` %s ) = ( toNat ` L ) )' % (ph, RHS))
    t4 = w.s([t3], 'eqcomd', '( %s -> ( toNat ` L ) = ( toNat ` %s ) )' % (ph, RHS))
    j = w.s([l3, t4], 'jca', '( %s -> ( ( # ` L ) = ( # ` %s ) /\\ ( toNat ` L ) = ( toNat ` %s ) ) )' % (ph, RHS, RHS))
    w.qed([bi, j], 'mpbird', '( %s -> L = %s )' % (ph, RHS))
    return w.run()


def bwstriprev():
    lab = 'bwstriprev'
    ph = LL_
    RHS = '( %s ++ %s )' % (E, REP)
    RE = '( reverse ` %s )' % E
    w = W(lab, 'The reversal of a bit word is its high zeros followed by the reversal of its '
               'canonical form: what the strip loop of ` canonNum ` sees (blueprint D2).  '
               '~ bwstriph , ~ revccat , ~ repswrevw .')
    u = common(w, ph)
    h = w.s([u['ll'], w.inst('bwstriph')], 'syl', '( %s -> L = %s )' % (ph, RHS))
    r1 = w.s([h], 'fveq2d', '( %s -> ( reverse ` L ) = ( reverse ` %s ) )' % (ph, RHS))
    r2 = w.s([u['ec'], u['rc'], w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` %s ) = ( ( reverse ` %s ) ++ %s ) )' % (ph, RHS, REP, RE))
    ex0 = w.s([], '0ex', '(/) e. _V'); ex0a = w.s([ex0], 'a1i', '( %s -> (/) e. _V )' % ph)
    r3 = w.s([ex0a, u['nz'], w.inst('repswrevw')], 'syl2anc', '( %s -> ( reverse ` %s ) = %s )' % (ph, REP, REP))
    r4 = w.s([r3], 'oveq1d', '( %s -> ( ( reverse ` %s ) ++ %s ) = ( %s ++ %s ) )' % (ph, REP, RE, REP, RE))
    r5 = w.s([r2, r4], 'eqtrd', '( %s -> ( reverse ` %s ) = ( %s ++ %s ) )' % (ph, RHS, REP, RE))
    w.qed([r1, r5], 'eqtrd', '( %s -> ( reverse ` L ) = ( %s ++ %s ) )' % (ph, REP, RE))
    return w.run()


def bwstriprevg():
    lab = 'bwstriprevg'
    ph = LL_
    RE = '( reverse ` %s )' % E
    RHS = '( %s ++ %s )' % (REP, RE)
    IL = IB('L'); IRL = '( inclBool o. ( reverse ` L ) )'
    Z1 = '<. 1 , (/) >.'
    w = W(lab, 'The reversal of a bit list on the machine (` bits l ` , ~ bwmaprev ) is a run of '
               'zero letters followed by the reversal of the canonical form.  Lean: ` bits_stripHigh ` '
               'with ` dropZeros_eq ` ; ~ bwstriprev through ~ bwmapccat , ~ repsco and ~ inclboolfv .')
    u = common(w, ph)
    h = w.s([u['ll'], w.inst('bwstriprev')], 'syl', '( %s -> ( reverse ` L ) = %s )' % (ph, RHS))
    c1 = w.s([h], 'coeq2d', '( %s -> %s = ( inclBool o. %s ) )' % (ph, IRL, RHS))
    m1 = w.s([u['ll'], w.inst('bwmaprev')], 'syl', '( %s -> %s = ( reverse ` %s ) )' % (ph, IRL, IL))
    rec = w.s([u['ec'], w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, RE, W2))
    m2 = w.s([u['rc'], rec, w.inst('bwmapccat')], 'syl2anc',
             '( %s -> ( inclBool o. %s ) = ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) )' % (ph, RHS, REP, RE))
    z2 = w.s([], '0el2o', '(/) e. 2o'); z2a = w.s([z2], 'a1i', '( %s -> (/) e. 2o )' % ph)
    ibf = w.s([], 'inclboolf', "inclBool : 2o --> Gamma'"); ibfa = w.s([ibf], 'a1i', "( %s -> inclBool : 2o --> Gamma' )" % ph)
    m3 = w.s([z2a, u['nz'], ibfa, w.inst('repsco')], 'syl3anc', '( %s -> ( inclBool o. %s ) = ( ( inclBool ` (/) ) repeatS %s ) )' % (ph, REP, NZ_))
    fv = w.s([z2a, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ph, Z1))
    m4 = w.s([fv], 'oveq1d', '( %s -> ( ( inclBool ` (/) ) repeatS %s ) = ( %s repeatS %s ) )' % (ph, NZ_, Z1, NZ_))
    m5 = w.s([m3, m4], 'eqtrd', '( %s -> ( inclBool o. %s ) = ( %s repeatS %s ) )' % (ph, REP, Z1, NZ_))
    m6 = w.s([u['ec'], w.inst('bwmaprev')], 'syl', '( %s -> ( inclBool o. %s ) = ( reverse ` %s ) )' % (ph, RE, IB(E)))
    m7 = w.s([m5, m6], 'oveq12d', '( %s -> ( ( inclBool o. %s ) ++ ( inclBool o. %s ) ) = ( ( %s repeatS %s ) ++ ( reverse ` %s ) ) )'
             % (ph, REP, RE, Z1, NZ_, IB(E)))
    FIN = '( ( %s repeatS %s ) ++ ( reverse ` %s ) )' % (Z1, NZ_, IB(E))
    e1 = w.s([m2, m7], 'eqtrd', '( %s -> ( inclBool o. %s ) = %s )' % (ph, RHS, FIN))
    e2 = w.s([c1, e1], 'eqtrd', '( %s -> %s = %s )' % (ph, IRL, FIN))
    e3 = w.s([m1], 'eqcomd', '( %s -> ( reverse ` %s ) = %s )' % (ph, IL, IRL))
    w.qed([e3, e2], 'eqtrd', '( %s -> ( reverse ` %s ) = %s )' % (ph, IL, FIN))
    return w.run()


def bwstripfst():
    lab = 'bwstripfst'
    ph = 'N e. NN'
    EN = '( encodeNat ` N )'
    IE = IB(EN)
    RIE = '( reverse ` %s )' % IE
    w = W(lab, 'The top letter of the reversed canonical form of a positive number on the machine '
               'is the one bit: the strip loop stops there.  Lean: ` canon_stripHigh ` , '
               '` dropZeros_head? ` ; ~ encnatlsb through ~ lswco and ~ revfv .')
    nn = w.s([], 'id', '( %s -> N e. NN )' % ph)
    n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % ph)
    ec = w.s([n0, w.inst('encnatcl')], 'syl', '( %s -> %s e. %s )' % (ph, EN, W2))
    ibf = w.s([], 'inclboolf', "inclBool : 2o --> Gamma'"); ibfa = w.s([ibf], 'a1i', "( %s -> inclBool : 2o --> Gamma' )" % ph)
    iec = w.s([ec, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, IE))
    ln = w.s([nn, w.inst('encnatlenn')], 'syl', '( %s -> ( # ` %s ) = ( ( |_ ` ( 2 logb N ) ) + 1 ) )' % (ph, EN))
    fl = w.s([nn, w.inst('encnatlem3')], 'syl', '( %s -> ( |_ ` ( 2 logb N ) ) e. NN0 )' % ph)
    fl1 = w.s([fl, w.inst('nn0p1nn')], 'syl', '( %s -> ( ( |_ ` ( 2 logb N ) ) + 1 ) e. NN )' % ph)
    lnn = w.s([ln, fl1], 'eqeltrd', '( %s -> ( # ` %s ) e. NN )' % (ph, EN))
    lm = w.s([ec, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, IE, EN))
    lmn = w.s([lm, lnn], 'eqeltrd', '( %s -> ( # ` %s ) e. NN )' % (ph, IE))
    z0 = w.s([lmn, w.inst('lbfzo0')], 'sylibr', '( %s -> 0 e. ( 0 ..^ ( # ` %s ) ) )' % (ph, IE))
    rv = w.s([iec, z0, w.inst('revfv')], 'syl2anc', '( %s -> ( %s ` 0 ) = ( %s ` ( ( ( # ` %s ) - 1 ) - 0 ) ) )' % (ph, RIE, IE, IE))
    lc = w.s([lmn], 'nncnd', '( %s -> ( # ` %s ) e. CC )' % (ph, IE))
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % ph)
    m1c = w.s([lc, one], 'subcld', '( %s -> ( ( # ` %s ) - 1 ) e. CC )' % (ph, IE))
    s0 = w.s([m1c, w.inst('subid1')], 'syl', '( %s -> ( ( ( # ` %s ) - 1 ) - 0 ) = ( ( # ` %s ) - 1 ) )' % (ph, IE, IE))
    s1 = w.s([s0], 'fveq2d', '( %s -> ( %s ` ( ( ( # ` %s ) - 1 ) - 0 ) ) = ( %s ` ( ( # ` %s ) - 1 ) ) )' % (ph, IE, IE, IE, IE))
    ls = w.s([iec, w.inst('lsw')], 'syl', '( %s -> ( lastS ` %s ) = ( %s ` ( ( # ` %s ) - 1 ) ) )' % (ph, IE, IE, IE))
    lsc = w.s([ls], 'eqcomd', '( %s -> ( %s ` ( ( # ` %s ) - 1 ) ) = ( lastS ` %s ) )' % (ph, IE, IE, IE))
    gt = w.s([lnn, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` %s ) )' % (ph, EN))
    env = w.s([ec], 'elexd', '( %s -> %s e. _V )' % (ph, EN))
    hn = w.s([env, w.inst('hashneq0')], 'syl', '( %s -> ( 0 < ( # ` %s ) <-> %s =/= (/) ) )' % (ph, EN, EN))
    ne = w.s([hn, gt], 'mpbid', '( %s -> %s =/= (/) )' % (ph, EN))
    lco = w.s([ec, ne, ibfa, w.inst('lswco')], 'syl3anc', '( %s -> ( lastS ` %s ) = ( inclBool ` ( lastS ` %s ) ) )' % (ph, IE, EN))
    lsb = w.s([nn, w.inst('encnatlsb')], 'syl', '( %s -> ( lastS ` %s ) = 1o )' % (ph, EN))
    l1 = w.s([lsb], 'fveq2d', '( %s -> ( inclBool ` ( lastS ` %s ) ) = ( inclBool ` 1o ) )' % (ph, EN))
    o2 = w.s([], '1oel2o', '1o e. 2o'); o2a = w.s([o2], 'a1i', '( %s -> 1o e. 2o )' % ph)
    fv1 = w.s([o2a, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` 1o ) = <. 1 , 1o >. )' % ph)
    c1 = w.s([lco, l1], 'eqtrd', '( %s -> ( lastS ` %s ) = ( inclBool ` 1o ) )' % (ph, IE))
    c2 = w.s([c1, fv1], 'eqtrd', '( %s -> ( lastS ` %s ) = <. 1 , 1o >. )' % (ph, IE))
    d1 = w.s([rv, s1], 'eqtrd', '( %s -> ( %s ` 0 ) = ( %s ` ( ( # ` %s ) - 1 ) ) )' % (ph, RIE, IE, IE))
    d2 = w.s([d1, lsc], 'eqtrd', '( %s -> ( %s ` 0 ) = ( lastS ` %s ) )' % (ph, RIE, IE))
    w.qed([d2, c2], 'eqtrd', '( %s -> ( %s ` 0 ) = <. 1 , 1o >. )' % (ph, RIE))
    return w.run()


if __name__ == '__main__':
    if want('bwstriplen'): bwstriplen()
    if want('bwstriph'): bwstriph()
    if want('bwstriprev'): bwstriprev()
    if want('bwstriprevg'): bwstriprevg()
    if want('bwstripfst'): bwstripfst()
