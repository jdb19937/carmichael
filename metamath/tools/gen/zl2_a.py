"""ZL2 section A: the elementary helpers of LConvexity.lean (45-102).
`MM_DB=sorties/zl2.mm python3 tools/gen/zl2_a.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl2lib import *
from lin import linarith, nlinarith

only = sys.argv[1:]

# ---------------------------------------------------------------- zl2e4: exp 4 <_ 81
if __name__ == '__main__' and (not only or 'zl2e4' in only):
    w = W('zl2e4', '` e ^ 4 <_ 81 ` ( Lean ` exp_four_le ` ).')
    c1 = w.s([], 'ax-1cn', '1 e. CC')
    z4 = w.s([], '4z', '4 e. ZZ')
    ie = w.s([], 'efexp', '( ( 1 e. CC /\\ 4 e. ZZ ) -> ( exp ` ( 4 x. 1 ) ) = ( ( exp ` 1 ) ^ 4 ) )')
    x1 = w.s([c1, z4, ie], 'mp2an', '( exp ` ( 4 x. 1 ) ) = ( ( exp ` 1 ) ^ 4 )')
    m1 = w.s([w.s([], '4cn', '4 e. CC')], 'mulridi', '( 4 x. 1 ) = 4')
    f1 = w.s([m1], 'fveq2i', '( exp ` ( 4 x. 1 ) ) = ( exp ` 4 )')
    x2 = w.s([f1, x1], 'eqtr3i', '( exp ` 4 ) = ( ( exp ` 1 ) ^ 4 )')
    de = w.s([w.s([], 'df-e', '_e = ( exp ` 1 )')], 'eqcomi', '( exp ` 1 ) = _e')
    x3 = w.s([de], 'oveq1i', '( ( exp ` 1 ) ^ 4 ) = ( _e ^ 4 )')
    x4 = w.s([x2, x3], 'eqtri', '( exp ` 4 ) = ( _e ^ 4 )')
    ere = w.s([], 'ere', '_e e. RR')
    r3 = w.s([], '3re', '3 e. RR')
    n4 = w.s([], '4nn0', '4 e. NN0')
    e0 = w.s([w.s([], '0re', '0 e. RR'), ere, w.s([], 'epos', '0 < _e')], 'ltleii', '0 <_ _e')
    e3 = ele3(w)
    il = w.s([], 'leexp1a', '( ( ( _e e. RR /\\ 3 e. RR /\\ 4 e. NN0 ) /\\ ( 0 <_ _e /\\ _e <_ 3 ) ) -> ( _e ^ 4 ) <_ ( 3 ^ 4 ) )')
    a3 = w.s([ere, r3, n4], '3pm3.2i', '( _e e. RR /\\ 3 e. RR /\\ 4 e. NN0 )')
    a2 = w.s([e0, e3], 'pm3.2i', '( 0 <_ _e /\\ _e <_ 3 )')
    le = w.s([a3, a2, il], 'mp2an', '( _e ^ 4 ) <_ ( 3 ^ 4 )')
    # 3 ^ 4 = 81
    c3 = w.s([], '3cn', '3 e. CC')
    n2 = w.s([], '2nn0', '2 e. NN0')
    im = w.s([], 'expmul', '( ( 3 e. CC /\\ 2 e. NN0 /\\ 2 e. NN0 ) -> ( 3 ^ ( 2 x. 2 ) ) = ( ( 3 ^ 2 ) ^ 2 ) )')
    a3b = w.s([c3, n2, n2], '3pm3.2i', '( 3 e. CC /\\ 2 e. NN0 /\\ 2 e. NN0 )')
    p1 = w.s([a3b, im], 'ax-mp', '( 3 ^ ( 2 x. 2 ) ) = ( ( 3 ^ 2 ) ^ 2 )')
    t4 = w.s([w.s([], '2t2e4', '( 2 x. 2 ) = 4')], 'oveq2i', '( 3 ^ ( 2 x. 2 ) ) = ( 3 ^ 4 )')
    p2 = w.s([t4, p1], 'eqtr3i', '( 3 ^ 4 ) = ( ( 3 ^ 2 ) ^ 2 )')
    p3 = w.s([w.s([], 'sq3', '( 3 ^ 2 ) = 9')], 'oveq1i', '( ( 3 ^ 2 ) ^ 2 ) = ( 9 ^ 2 )')
    p4 = w.s([w.s([], '9cn', '9 e. CC')], 'sqvali', '( 9 ^ 2 ) = ( 9 x. 9 )')
    p5 = w.s([], '9t9e81', '( 9 x. 9 ) = ; 8 1')
    q1 = w.s([p2, p3], 'eqtri', '( 3 ^ 4 ) = ( 9 ^ 2 )')
    q2 = w.s([q1, p4], 'eqtri', '( 3 ^ 4 ) = ( 9 x. 9 )')
    q3 = w.s([q2, p5], 'eqtri', '( 3 ^ 4 ) = ; 8 1')
    l2 = w.s([le, q3], 'breqtri', '( _e ^ 4 ) <_ ; 8 1')
    w.qed([x4, l2], 'eqbrtri', '( exp ` 4 ) <_ ; 8 1')
    go(w, only)

# ---------------------------------------------------------------- zl2gau: ( 1 + | v | ) e ^ ( - v ^ 2 ) <_ 3
if __name__ == '__main__' and (not only or 'zl2gau' in only):
    w = W('zl2gau', '` ( 1 + | v | ) e ^ ( - v ^ 2 ) <_ 3 ` ( Lean ` one_add_abs_mul_exp_neg_sq_le ` ).')
    A = 'V e. RR'
    vr = w.s([], 'id', '( V e. RR -> V e. RR )')
    vc = D(w, A, 'recnd', [vr], 'V e. CC')
    av = D(w, A, 'abscld', [vc], '( abs ` V ) e. RR')
    av0 = D(w, A, 'absge0d', [vc], '0 <_ ( abs ` V )')
    sq = D(w, A, 'resqcld', [vr], '( V ^ 2 ) e. RR')
    nsq = D(w, A, 'renegcld', [sq], '-u ( V ^ 2 ) e. RR')
    one = a1(w, A, '1re', '1 e. RR')
    h1 = w.s([av, av0, w.inst('bvefge1p')], 'syl2anc', '( V e. RR -> ( 1 + ( abs ` V ) ) <_ ( exp ` ( abs ` V ) ) )')
    ex0 = D(w, A, 'reefcld', [nsq], '( exp ` -u ( V ^ 2 ) ) e. RR')
    exg = w.s([nsq, w.inst('efgt0')], 'syl', '( V e. RR -> 0 < ( exp ` -u ( V ^ 2 ) ) )')
    exge = D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), ex0, exg], '0 <_ ( exp ` -u ( V ^ 2 ) )')
    o1 = D(w, A, 'readdcld', [one, av], '( 1 + ( abs ` V ) ) e. RR')
    eav = D(w, A, 'reefcld', [av], '( exp ` ( abs ` V ) ) e. RR')
    h2 = D(w, A, 'lemul1ad', [o1, eav, ex0, exge, h1],
           '( ( 1 + ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) ) <_ ( ( exp ` ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) )')
    h3 = efadd_(w, A, '( abs ` V )', '-u ( V ^ 2 )', D(w, A, 'recnd', [av], '( abs ` V ) e. CC'), D(w, A, 'recnd', [nsq], '-u ( V ^ 2 ) e. CC'))
    # | v | - v ^ 2 <_ 1
    e2 = w.s([vr, w.inst('absresq')], 'syl', '( V e. RR -> ( ( abs ` V ) ^ 2 ) = ( V ^ 2 ) )')
    e3 = D(w, A, 'sqvald', [D(w, A, 'recnd', [av], '( abs ` V ) e. CC')], '( ( abs ` V ) ^ 2 ) = ( ( abs ` V ) x. ( abs ` V ) )')
    e4 = w.s([e2, e3], 'eqtr3d', '( V e. RR -> ( V ^ 2 ) = ( ( abs ` V ) x. ( abs ` V ) ) )')
    am1 = D(w, A, 'resubcld', [av, one], '( ( abs ` V ) - 1 ) e. RR')
    ms = D(w, A, 'msqge0d', [am1], '0 <_ ( ( ( abs ` V ) - 1 ) x. ( ( abs ` V ) - 1 ) )')
    cl = Closure(w, A, {'( abs ` V )': ('RR', av), '( V ^ 2 )': ('RR', sq)})
    h4 = nlinarith(w, A, [ms, e4, av0], '( ( abs ` V ) + -u ( V ^ 2 ) ) <_ 1', closure=cl)
    sr = D(w, A, 'readdcld', [av, nsq], '( ( abs ` V ) + -u ( V ^ 2 ) ) e. RR')
    h5 = efle_(w, A, '( ( abs ` V ) + -u ( V ^ 2 ) )', '1', sr, one, h4)
    e1r = e1le3(w)
    e1d = w.s([e1r], 'a1i', '( V e. RR -> ( exp ` 1 ) <_ 3 )')
    ch = w.s([h3, h5], 'eqbrtrrd', '( V e. RR -> ( ( exp ` ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) ) <_ ( exp ` 1 ) )')
    lhs = D(w, A, 'remulcld', [o1, ex0], '( ( 1 + ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) ) e. RR')
    mid = D(w, A, 'remulcld', [eav, ex0], '( ( exp ` ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) ) e. RR')
    e1c = D(w, A, 'reefcld', [one], '( exp ` 1 ) e. RR')
    h7 = w.s([lhs, mid, e1c, h2, ch], 'letrd', '( V e. RR -> ( ( 1 + ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) ) <_ ( exp ` 1 ) )')
    w.qed([lhs, e1c, a1(w, A, '3re', '3 e. RR'), h7, e1d], 'letrd', '( V e. RR -> ( ( 1 + ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) ) <_ 3 )')
    go(w, only)

# ---------------------------------------------------------------- zl2ngau: modulus of the Gaussian normalizer
if __name__ == '__main__' and (not only or 'zl2ngau' in only):
    w = W('zl2ngau', 'The modulus of the Gaussian normalizer: ` | e ^ ( ( Z - W ) ^ 2 ) | = e ^ ( ( Re Z - Re W ) ^ 2 - ( Im Z - Im W ) ^ 2 ) ` '
          '( Lean ` norm_exp_sq_sub ` ).')
    A = '( Z e. CC /\\ W e. CC )'
    zc = D(w, A, 'simpl', [], 'Z e. CC')
    wc = D(w, A, 'simpr', [], 'W e. CC')
    dm = '( Z - W )'
    dc = D(w, A, 'subcld', [zc, wc], '%s e. CC' % dm)
    d2 = D(w, A, 'sqcld', [dc], '( %s ^ 2 ) e. CC' % dm)
    e1 = w.s([d2, w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` ( %s ^ 2 ) ) ) = ( exp ` ( Re ` ( %s ^ 2 ) ) ) )' % (A, dm, dm))
    e2 = E(w, A, 'sqvald', [dc], '( %s ^ 2 )' % dm, '( %s x. %s )' % (dm, dm))
    e2r = E(w, A, 'fveq2d', [e2], '( Re ` ( %s ^ 2 ) )' % dm, '( Re ` ( %s x. %s ) )' % (dm, dm))
    RD, ID = '( Re ` %s )' % dm, '( Im ` %s )' % dm
    e3 = w.s([dc, dc, w.inst('remul')], 'syl2anc', '( %s -> ( Re ` ( %s x. %s ) ) = ( ( %s x. %s ) - ( %s x. %s ) ) )' % (A, dm, dm, RD, RD, ID, ID))
    RZW = '( ( Re ` Z ) - ( Re ` W ) )'; IZW = '( ( Im ` Z ) - ( Im ` W ) )'
    r1 = E(w, A, 'resubd', [zc, wc], RD, RZW)
    i1 = E(w, A, 'imsubd', [zc, wc], ID, IZW)
    rzc = D(w, A, 'recnd', [D(w, A, 'resubcld', [D(w, A, 'recld', [zc], '( Re ` Z ) e. RR'), D(w, A, 'recld', [wc], '( Re ` W ) e. RR')], '%s e. RR' % RZW)], '%s e. CC' % RZW)
    izc = D(w, A, 'recnd', [D(w, A, 'resubcld', [D(w, A, 'imcld', [zc], '( Im ` Z ) e. RR'), D(w, A, 'imcld', [wc], '( Im ` W ) e. RR')], '%s e. RR' % IZW)], '%s e. CC' % IZW)
    s1 = E(w, A, 'sqvald', [rzc], '( %s ^ 2 )' % RZW, '( %s x. %s )' % (RZW, RZW))
    s2 = E(w, A, 'sqvald', [izc], '( %s ^ 2 )' % IZW, '( %s x. %s )' % (IZW, IZW))
    m1 = E(w, A, 'oveq12d', [r1, r1], '( %s x. %s )' % (RD, RD), '( %s x. %s )' % (RZW, RZW))
    m2 = E(w, A, 'oveq12d', [i1, i1], '( %s x. %s )' % (ID, ID), '( %s x. %s )' % (IZW, IZW))
    m1b = w.s([m1, s1], 'eqtr4d', '( %s -> ( %s x. %s ) = ( %s ^ 2 ) )' % (A, RD, RD, RZW))
    m2b = w.s([m2, s2], 'eqtr4d', '( %s -> ( %s x. %s ) = ( %s ^ 2 ) )' % (A, ID, ID, IZW))
    m3 = E(w, A, 'oveq12d', [m1b, m2b], '( ( %s x. %s ) - ( %s x. %s ) )' % (RD, RD, ID, ID), '( ( %s ^ 2 ) - ( %s ^ 2 ) )' % (RZW, IZW))
    RE2 = '( ( %s ^ 2 ) - ( %s ^ 2 ) )' % (RZW, IZW)
    rq = chain(w, A, ['( Re ` ( %s ^ 2 ) )' % dm, '( Re ` ( %s x. %s ) )' % (dm, dm), '( ( %s x. %s ) - ( %s x. %s ) )' % (RD, RD, ID, ID), RE2], [e2r, e3, m3])
    fq = E(w, A, 'fveq2d', [rq], '( exp ` ( Re ` ( %s ^ 2 ) ) )' % dm, '( exp ` %s )' % RE2)
    w.qed([e1, fq], 'eqtrd', '( %s -> ( abs ` ( exp ` ( %s ^ 2 ) ) ) = ( exp ` %s ) )' % (A, dm, RE2))
    go(w, only)

# ---------------------------------------------------------------- zl2npow: modulus of the power normalizer
if __name__ == '__main__' and (not only or 'zl2npow' in only):
    w = W('zl2npow', 'The modulus of the power normalizer: ` | e ^ ( Z C ) | = e ^ ( Re Z C ) ` for real ` C ` ( Lean ` norm_exp_mul_ofReal ` ).')
    A = '( Z e. CC /\\ C e. RR )'
    zc = D(w, A, 'simpl', [], 'Z e. CC')
    cr = D(w, A, 'simpr', [], 'C e. RR')
    cc = D(w, A, 'recnd', [cr], 'C e. CC')
    pc = D(w, A, 'mulcld', [zc, cc], '( Z x. C ) e. CC')
    e1 = w.s([pc, w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` ( Z x. C ) ) ) = ( exp ` ( Re ` ( Z x. C ) ) ) )' % A)
    c1 = E(w, A, 'mulcomd', [zc, cc], '( Z x. C )', '( C x. Z )')
    c2 = E(w, A, 'fveq2d', [c1], '( Re ` ( Z x. C ) )', '( Re ` ( C x. Z ) )')
    c3 = w.s([cr, zc, w.inst('remul2')], 'syl2anc', '( %s -> ( Re ` ( C x. Z ) ) = ( C x. ( Re ` Z ) ) )' % A)
    c4 = E(w, A, 'mulcomd', [cc, D(w, A, 'recnd', [D(w, A, 'recld', [zc], '( Re ` Z ) e. RR')], '( Re ` Z ) e. CC')], '( C x. ( Re ` Z ) )', '( ( Re ` Z ) x. C )')
    rq = chain(w, A, ['( Re ` ( Z x. C ) )', '( Re ` ( C x. Z ) )', '( C x. ( Re ` Z ) )', '( ( Re ` Z ) x. C )'], [c2, c3, c4])
    fq = E(w, A, 'fveq2d', [rq], '( exp ` ( Re ` ( Z x. C ) ) )', '( exp ` ( ( Re ` Z ) x. C ) )')
    w.qed([e1, fq], 'eqtrd', '( %s -> ( abs ` ( exp ` ( Z x. C ) ) ) = ( exp ` ( ( Re ` Z ) x. C ) ) )' % A)
    go(w, only)

# ---------------------------------------------------------------- zl2tab: | Y | + 2 <_ ( | V | + 2 ) ( 1 + | Y - V | )
if __name__ == '__main__' and (not only or 'zl2tab' in only):
    w = W('zl2tab', '` | Y | + 2 <_ ( | V | + 2 ) ( 1 + | Y - V | ) ` ( Lean ` two_add_abs_le ` ).')
    A = '( Y e. RR /\\ V e. RR )'
    yc = D(w, A, 'recnd', [D(w, A, 'simpl', [], 'Y e. RR')], 'Y e. CC')
    vc = D(w, A, 'recnd', [D(w, A, 'simpr', [], 'V e. RR')], 'V e. CC')
    ay = D(w, A, 'abscld', [yc], '( abs ` Y ) e. RR')
    av = D(w, A, 'abscld', [vc], '( abs ` V ) e. RR')
    dd = D(w, A, 'subcld', [yc, vc], '( Y - V ) e. CC')
    ad = D(w, A, 'abscld', [dd], '( abs ` ( Y - V ) ) e. RR')
    av0 = D(w, A, 'absge0d', [vc], '0 <_ ( abs ` V )')
    ad0 = D(w, A, 'absge0d', [dd], '0 <_ ( abs ` ( Y - V ) )')
    tri = w.s([yc, vc, w.inst('abs2dif')], 'syl2anc', '( %s -> ( ( abs ` Y ) - ( abs ` V ) ) <_ ( abs ` ( Y - V ) ) )' % A)
    pr = D(w, A, 'mulge0d', [av, ad, av0, ad0], '0 <_ ( ( abs ` V ) x. ( abs ` ( Y - V ) ) )')
    cl = Closure(w, A, {'( abs ` Y )': ('RR', ay), '( abs ` V )': ('RR', av), '( abs ` ( Y - V ) )': ('RR', ad)})
    nlinarith(w, A, [tri, pr, ad0], '( ( abs ` Y ) + 2 ) <_ ( ( ( abs ` V ) + 2 ) x. ( 1 + ( abs ` ( Y - V ) ) ) )', closure=cl, name='qed')
    go(w, only)
