"""Sortie DSH, section A: the R = 1 collapse (Lean Rset_one, P1_one, psi_one_left, Pfun_one_eq_one).
Run: MM_DB=sorties/dsh.mm MM_ENGINE=mmatch python3 tools/gen/dsh_a.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dshlib import *
from tm import W
from z6a_e3 import unpack, c_

only = sys.argv[1:]
want = lambda l: not only or l in only
mk = lambda w, a: (lambda hyps, ref, g: w.s(hyps, ref, '( %s -> %s )' % (a, g)))
RS1 = '( N RSet 1 )'


def rs1(w, a, t, nn):
    """( a -> ( N RSet 1 ) = { 1 } ) from ( a -> N e. NN )"""
    return t([nn, w.inst('dshrs1')], 'syl', '%s = { 1 }' % RS1)


if want('dshrs1'):
    w = W('dshrs1', 'Lean ` Rset_one ` : at ` R = 1 ` the pseudocharacter moduli are ` { 1 } ` (~ z5rsetfi , ~ z5elrset , ~ muone , ~ 1gcd ).')
    a = 'N e. NN'; t = mk(w, a)
    nn = w.s([], 'id', '( N e. NN -> N e. NN )')
    one = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    fi = t([nn, one, w.inst('z5rsetfi')], 'syl2anc', '( %s C_ ( 1 ... ( |_ ` 1 ) ) /\\ %s e. Fin )' % (RS1, RS1))
    ss = t([fi], 'simpld', '%s C_ ( 1 ... ( |_ ` 1 ) )' % RS1)
    z1 = w.s([], '1z', '1 e. ZZ')
    fl = c_(w, a, w.s([z1, w.s([], 'flid', '( 1 e. ZZ -> ( |_ ` 1 ) = 1 )')], 'ax-mp', '( |_ ` 1 ) = 1'), '( |_ ` 1 ) = 1')
    fz = c_(w, a, w.s([z1, w.s([], 'fzsn', '( 1 e. ZZ -> ( 1 ... 1 ) = { 1 } )')], 'ax-mp', '( 1 ... 1 ) = { 1 }'), '( 1 ... 1 ) = { 1 }')
    fe = t([t([fl], 'oveq2d', '( 1 ... ( |_ ` 1 ) ) = ( 1 ... 1 )'), fz], 'eqtrd', '( 1 ... ( |_ ` 1 ) ) = { 1 }')
    s1 = t([ss, fe], 'sseqtrd', '%s C_ { 1 }' % RS1)
    in1 = t([c_(w, a, w.s([w.s([], '1ex', '1 e. _V')], 'snid', '1 e. { 1 }'), '1 e. { 1 }'), fe], 'eleqtrrd', '1 e. ( 1 ... ( |_ ` 1 ) )')
    mu = c_(w, a, w.s([w.s([], 'muone', '( mmu ` 1 ) = 1'), w.s([], 'ax-1ne0', '1 =/= 0')], 'eqnetri', '( mmu ` 1 ) =/= 0'), '( mmu ` 1 ) =/= 0')
    gc = t([t([nn], 'nnzd', 'N e. ZZ'), w.inst('1gcd')], 'syl', '( 1 gcd N ) = 1')
    el = t([nn, one, w.inst('z5elrset')], 'syl2anc', '( 1 e. %s <-> ( 1 e. ( 1 ... ( |_ ` 1 ) ) /\\ ( ( mmu ` 1 ) =/= 0 /\\ ( 1 gcd N ) = 1 ) ) )' % RS1)
    m1 = t([t([in1, t([mu, gc], 'jca', '( ( mmu ` 1 ) =/= 0 /\\ ( 1 gcd N ) = 1 )')], 'jca',
              '( 1 e. ( 1 ... ( |_ ` 1 ) ) /\\ ( ( mmu ` 1 ) =/= 0 /\\ ( 1 gcd N ) = 1 ) )'), el], 'mpbird', '1 e. %s' % RS1)
    s2 = t([m1], 'snssd', '{ 1 } C_ %s' % RS1)
    s = t([s1, s2], 'eqssd', '%s = { 1 }' % RS1)
    toqed(w, s, 'dshrs1'); w.run()

if want('dshp11'):
    w = W('dshp11', 'Lean ` P1_one ` : ` P1 N 1 = sum_ r e. { 1 } 1 / r = 1 ` (~ dshrs1 , ~ sumsn ).')
    a = 'N e. NN'; t = mk(w, a)
    nn = w.s([], 'id', '( N e. NN -> N e. NN )')
    e1 = t([rs1(w, a, t, nn)], 'sumeq1d', 'sum_ r e. %s ( 1 / r ) = sum_ r e. { 1 } ( 1 / r )' % RS1)
    cg = w.s([], 'oveq2', '( r = 1 -> ( 1 / r ) = ( 1 / 1 ) )')
    one = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    d1 = w.s([], '1div1e1', '( 1 / 1 ) = 1')
    c11 = c_(w, a, w.s([w.s([], 'ax-1cn', '1 e. CC'), d1], 'eqeltrri' if False else 'x', 'x'), 'x') if False else None
    c11 = c_(w, a, w.s([d1, w.s([], 'ax-1cn', '1 e. CC')], 'eqeltri', '( 1 / 1 ) e. CC'), '( 1 / 1 ) e. CC')
    sn = t([t([one, c11], 'jca', '( 1 e. NN /\\ ( 1 / 1 ) e. CC )'), w.s([cg], 'sumsn', '( ( 1 e. NN /\\ ( 1 / 1 ) e. CC ) -> sum_ r e. { 1 } ( 1 / r ) = ( 1 / 1 ) )')], 'syl', 'sum_ r e. { 1 } ( 1 / r ) = ( 1 / 1 )')

    s = t([t([e1, sn], 'eqtrd', 'sum_ r e. %s ( 1 / r ) = ( 1 / 1 )' % RS1), c_(w, a, d1, '( 1 / 1 ) = 1')], 'eqtrd', 'sum_ r e. %s ( 1 / r ) = 1' % RS1)
    toqed(w, s, 'dshp11'); w.run()

if want('dshpf1'):
    w = W('dshpf1', 'Lean ` Pfun_one_eq_one ` and ` psi_one_left ` : at ` R = 1 ` the pseudocharacter weight is ` 1 ` (~ z5pfunval , ~ dshrs1 , ~ 1gcd , ~ muone , ~ phi1 ).')
    a = '( N e. NN /\\ M e. NN )'; t = mk(w, a)
    nn = t([], 'simpl', 'N e. NN'); mn = t([], 'simpr', 'M e. NN')
    one = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    BODY = lambda r: '( ( ( mmu ` ( %s gcd M ) ) x. ( phi ` ( %s gcd M ) ) ) / %s )' % (r, r, r)
    pv = t([t([t([nn, one], 'jca', '( N e. NN /\\ 1 e. NN )'), mn], 'jca', '( ( N e. NN /\\ 1 e. NN ) /\\ M e. NN )'), w.inst('z5pfunval')], 'syl',
           '( ( N PFun 1 ) ` M ) = sum_ r e. %s %s' % (RS1, BODY('r')))
    e1 = t([rs1(w, a, t, nn)], 'sumeq1d', 'sum_ r e. %s %s = sum_ r e. { 1 } %s' % (RS1, BODY('r'), BODY('r')))
    cg, new = w.congr(BODY('r'), {'r': '1'}, 'r = 1', {'r': w.s([], 'id', '( r = 1 -> r = 1 )')})
    gc = t([t([mn], 'nnzd', 'M e. ZZ'), w.inst('1gcd')], 'syl', '( 1 gcd M ) = 1')
    B1 = BODY('1')
    r1, n1 = w.rewrite(B1, {'( 1 gcd M )': ('1', gc)}, a)
    assert n1 == '( ( ( mmu ` 1 ) x. ( phi ` 1 ) ) / 1 )', n1
    mu = c_(w, a, w.s([], 'muone', '( mmu ` 1 ) = 1'), '( mmu ` 1 ) = 1'); ph = c_(w, a, w.s([], 'phi1', '( phi ` 1 ) = 1'), '( phi ` 1 ) = 1')
    r2, n2 = w.rewrite(n1, {'( mmu ` 1 )': ('1', mu), '( phi ` 1 )': ('1', ph)}, a)
    assert n2 == '( ( 1 x. 1 ) / 1 )', n2
    t11 = c_(w, a, w.s([], '1t1e1', '( 1 x. 1 ) = 1'), '( 1 x. 1 ) = 1')
    r3 = t([t11], 'oveq1d', '( ( 1 x. 1 ) / 1 ) = ( 1 / 1 )')
    d1 = c_(w, a, w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')
    v1 = t([t([t([r1, r2], 'eqtrd', '%s = %s' % (B1, n2)), r3], 'eqtrd', '%s = ( 1 / 1 )' % B1), d1], 'eqtrd', '%s = 1' % B1)
    b1c = t([v1, c_(w, a, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')], 'eqeltrd', '%s e. CC' % B1)
    sn = t([t([one, b1c], 'jca', '( 1 e. NN /\\ %s e. CC )' % B1), w.s([cg], 'sumsn', '( ( 1 e. NN /\\ %s e. CC ) -> sum_ r e. { 1 } %s = %s )' % (B1, BODY('r'), B1))], 'syl', 'sum_ r e. { 1 } %s = %s' % (BODY('r'), B1))
    s = t([t([t([pv, e1], 'eqtrd', '( ( N PFun 1 ) ` M ) = sum_ r e. { 1 } %s' % BODY('r')), sn], 'eqtrd', '( ( N PFun 1 ) ` M ) = %s' % B1), v1], 'eqtrd',
          '( ( N PFun 1 ) ` M ) = 1')
    toqed(w, s, 'dshpf1'); w.run()

from z5clib import MRT, HAB0, MR, EPV

if want('dshmr1'):
    w = W('dshmr1', 'Lean ` Mr_one_eq ` (with ` tOf_one_right ` , ` eulerT_one ` ): at ` r = 1 ` the mollifier is ` sum_ ( d <_ B ) bvLam ( d ) C ( d ) d ^ -u S ` '
          '(~ z5mrval ; ` 1 gcd d = 1 ` , no prime divides 1, ~ prod0 ).')
    a = '( %s /\\ ( C : NN --> CC /\\ S e. CC ) )' % HAB0; t = mk(w, a); f = unpack(w, a)
    ar = f['A e. RR']; br = f['B e. RR']; a0 = f['0 < A']; ab = f['A < B']; cf = f['C : NN --> CC']; sc = f['S e. CC']
    cv = t([cf, c_(w, a, w.s([], 'nnex', 'NN e. _V'), 'NN e. _V')], 'fexd', 'C e. _V')
    one = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    MR1 = MR('S', '1')
    FZ = '( 1 ... ( |_ ` B ) )'
    mv = t([t([t([t([ar, br], 'jca', '( A e. RR /\\ B e. RR )'), t([cv, one], 'jca', '( C e. _V /\\ 1 e. NN )')], 'jca',
                 '( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ 1 e. NN ) )'), sc], 'jca', '( ( ( A e. RR /\\ B e. RR ) /\\ ( C e. _V /\\ 1 e. NN ) ) /\\ S e. CC )'),
            w.inst('z5mrval')], 'syl', '%s = sum_ d e. %s %s' % (MR1, FZ, MRT('d', '1')))
    ad = '( %s /\\ d e. %s )' % (a, FZ); u = mk(w, ad)
    dn = u([u([], 'simpr', 'd e. %s' % FZ), w.inst('elfznn')], 'syl', 'd e. NN')
    gc = u([u([dn], 'nnzd', 'd e. ZZ'), w.inst('1gcd')], 'syl', '( 1 gcd d ) = 1')
    T0 = MRT('d', '1')
    r1, n1 = w.rewrite(T0, {'( 1 gcd d )': ('1', gc)}, ad)
    mu = c_(w, ad, w.s([], 'muone', '( mmu ` 1 ) = 1'), '( mmu ` 1 ) = 1'); ph = c_(w, ad, w.s([], 'phi1', '( phi ` 1 ) = 1'), '( phi ` 1 ) = 1')
    r2, n2 = w.rewrite(n1, {'( mmu ` 1 )': ('1', mu), '( phi ` 1 )': ('1', ph)}, ad)
    t11 = c_(w, ad, w.s([], '1t1e1', '( 1 x. 1 ) = 1'), '( 1 x. 1 ) = 1')
    r3, n3 = w.rewrite(n2, {'( 1 x. 1 )': ('1', t11)}, ad)
    QS1 = '{ q e. Prime | ( q || 1 /\\ -. q || d ) }'
    q1 = w.s([], 'nprmdvds1', '( q e. Prime -> -. q || 1 )')
    q2 = w.s([q1], 'intnanrd', '( q e. Prime -> -. ( q || 1 /\\ -. q || d ) )')
    q3 = w.s([q2], 'rgen', 'A. q e. Prime -. ( q || 1 /\\ -. q || d )')
    q4 = w.s([q3, w.s([], 'rabeq0', '( %s = (/) <-> A. q e. Prime -. ( q || 1 /\\ -. q || d ) )' % QS1)], 'mpbir', '%s = (/)' % QS1)
    r4, n4 = w.rewrite(n3, {QS1: ('(/)', c_(w, ad, q4, '%s = (/)' % QS1))}, ad)
    PR = [x for x in [n4[n4.index('prod_ p e. (/)'):]]][0][:-2]
    p0 = c_(w, ad, w.s([], 'prod0', '%s = 1' % PR), '%s = 1' % PR)
    r5, n5 = w.rewrite(n4, {PR: ('1', p0)}, ad)
    LAM = '( ( A bvLam B ) ` d )'
    ar_, br_, a0_, ab_ = [w.s([x], 'adantr', '( %s -> %s )' % (ad, g)) for x, g in [(ar, 'A e. RR'), (br, 'B e. RR'), (a0, '0 < A'), (ab, 'A < B')]]
    lc = u([u([u([u([ar_, a0_], 'elrpd', 'A e. RR+'), u([br_, u([c_(w, ad, w.s([], '0re', '0 e. RR'), '0 e. RR'), ar_, br_, a0_, ab_], 'lttrd', '0 < B')], 'elrpd', 'B e. RR+'), ab_],
                  '3jca', '( A e. RR+ /\\ B e. RR+ /\\ A < B )'), dn], 'jca', '( ( A e. RR+ /\\ B e. RR+ /\\ A < B ) /\\ d e. NN )'), w.inst('bvlamre')], 'syl', '%s e. RR' % LAM)
    lcc = u([lc], 'recnd', '%s e. CC' % LAM)
    r6, n6 = w.rewrite(n5, {'( %s x. 1 )' % LAM: (LAM, u([lcc], 'mulridd', '( %s x. 1 ) = %s' % (LAM, LAM)))}, ad)
    TGT = '( ( %s x. ( C ` d ) ) x. ( d ^c -u S ) )' % LAM
    assert n6 == '( %s x. 1 )' % TGT, n6
    sc_ = w.s([sc], 'adantr', '( %s -> S e. CC )' % ad)
    tc = u([u([lcc, u([cf if False else w.s([cf], 'adantr', '( %s -> C : NN --> CC )' % ad), dn], 'ffvelcdmd', '( C ` d ) e. CC')], 'mulcld', '( %s x. ( C ` d ) ) e. CC' % LAM),
            u([u([dn], 'nncnd', 'd e. CC'), u([sc_], 'negcld', '-u S e. CC')], 'cxpcld', '( d ^c -u S ) e. CC')], 'mulcld', '%s e. CC' % TGT)
    r7 = u([tc], 'mulridd', '( %s x. 1 ) = %s' % (TGT, TGT))
    ch = r1
    for r_, nn_ in [(r2, n2), (r3, n3), (r4, n4), (r5, n5), (r6, n6)]:
        ch = u([ch, r_], 'eqtrd', '%s = %s' % (T0, nn_))
    ch = u([ch, r7], 'eqtrd', '%s = %s' % (T0, TGT))
    se = t([ch], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (FZ, T0, FZ, TGT))
    s = t([mv, se], 'eqtrd', '%s = sum_ d e. %s %s' % (MR1, FZ, TGT))
    toqed(w, s, 'dshmr1'); w.run()

if want('dshep1'):
    w = W('dshep1', 'Lean ` Epole_one_eq ` : at ` R = 1 ` the pole term is ` if ( chi = chi_0 , Gamma ( 1 - S ) X ^ ( 1 - S ) ( phi ( N ) / N ) M_1 ( 1 ) , 0 ) ` '
          '(~ z5epval , ~ dshrs1 , ~ sumsn ).')
    a = '( ( ( %s /\\ X e. W ) /\\ ( C e. T /\\ N e. NN ) ) /\\ S e. CC )' % HAB0; t = mk(w, a); f = unpack(w, a)
    ar = f['A e. RR']; br = f['B e. RR']; nn = f['N e. NN']
    one = c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    from z5clib import EPB
    PH = PRIN('N', 'h')
    EB = EPB().replace('( N RSet R )', '( N RSet 1 )')
    ev = t([t([t([t([ar, br, f['X e. W']], '3jca', '( A e. RR /\\ B e. RR /\\ X e. W )'), t([f['C e. T'], nn, one], '3jca', '( C e. T /\\ N e. NN /\\ 1 e. NN )')], 'jca',
                              '( ( A e. RR /\\ B e. RR /\\ X e. W ) /\\ ( C e. T /\\ N e. NN /\\ 1 e. NN ) )'), f['S e. CC']], 'jca',
                           '( ( ( A e. RR /\\ B e. RR /\\ X e. W ) /\\ ( C e. T /\\ N e. NN /\\ 1 e. NN ) ) /\\ S e. CC )'), w.inst('z5epval')], 'syl',
           '%s = if ( C = %s , %s , 0 )' % (EPV().replace('R >.', '1 >.'), PH, EB))
    # h -> n in the principal character
    cg, _ = w.congr('if ( ( h gcd N ) = 1 , 1 , 0 )', {'h': 'n'}, 'h = n', {'h': w.s([], 'id', '( h = n -> h = n )')})
    cbv = w.s([cg], 'cbvmptv', '%s = %s' % (PH, PRN))
    cb = t([c_(w, a, cbv, '%s = %s' % (PH, PRN))], 'eqeq2d', '( C = %s <-> C = %s )' % (PH, PRN))
    e2 = t([cb], 'ifbid', 'if ( C = %s , %s , 0 ) = if ( C = %s , %s , 0 )' % (PH, EB, PRN, EB))
    # the r-sum at R = 1
    ac = '( %s /\\ C = %s )' % (a, PRN); u = mk(w, ac)
    MRr = lambda r, s='1': '( ( <. A , B >. Mr <. C , %s >. ) ` %s )' % (r, s)
    SUMR = 'sum_ r e. ( N RSet 1 ) ( ( 1 / r ) x. %s )' % MRr('r')
    pr = w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % ac), w.inst('z5prin')], 'syl',
             '( %s -> ( ( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 ) /\\ A. c e. Prime ( ( c gcd N ) = 1 -> ( %s ` c ) = 1 ) ) )' % (ac, PRN, PRN, PRN))
    pf = u([u([pr], 'simpld', '( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 )' % (PRN, PRN))], 'simpld', '%s : NN --> CC' % PRN)
    cf = u([pf, u([u([], 'simpr', 'C = %s' % PRN), w.inst('feq1')], 'syl', '( C : NN --> CC <-> %s : NN --> CC )' % PRN)], 'mpbird', 'C : NN --> CC')
    hab = w.s([f[HAB0]], 'adantr', '( %s -> %s )' % (ac, HAB0))
    one_ = c_(w, ac, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    c1 = c_(w, ac, w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')
    mc = u([u([u([hab, one_], 'jca', '( %s /\\ 1 e. NN )' % HAB0), u([cf, c1], 'jca', '( C : NN --> CC /\\ 1 e. CC )')], 'jca',
              '( ( %s /\\ 1 e. NN ) /\\ ( C : NN --> CC /\\ 1 e. CC ) )' % HAB0), w.inst('z5mrcl')], 'syl', '%s e. CC' % MRr('1'))
    rs = u([w.s([nn], 'adantr', '( %s -> N e. NN )' % ac), w.inst('dshrs1')], 'syl', '( N RSet 1 ) = { 1 }')
    e3 = u([rs], 'sumeq1d', '%s = sum_ r e. { 1 } ( ( 1 / r ) x. %s )' % (SUMR, MRr('r')))
    cg2, B1 = w.congr('( ( 1 / r ) x. %s )' % MRr('r'), {'r': '1'}, 'r = 1', {'r': w.s([], 'id', '( r = 1 -> r = 1 )')})
    d1 = c_(w, ac, w.s([], '1div1e1', '( 1 / 1 ) = 1'), '( 1 / 1 ) = 1')
    v1 = u([u([d1], 'oveq1d', '%s = ( 1 x. %s )' % (B1, MRr('1'))), u([mc], 'mullidd', '( 1 x. %s ) = %s' % (MRr('1'), MRr('1')))], 'eqtrd', '%s = %s' % (B1, MRr('1')))
    b1c = u([v1, mc], 'eqeltrd', '%s e. CC' % B1)
    sn = u([u([one_, b1c], 'jca', '( 1 e. NN /\\ %s e. CC )' % B1),
            w.s([cg2], 'sumsn', '( ( 1 e. NN /\\ %s e. CC ) -> sum_ r e. { 1 } ( ( 1 / r ) x. %s ) = %s )' % (B1, MRr('r'), B1))], 'syl',
           'sum_ r e. { 1 } ( ( 1 / r ) x. %s ) = %s' % (MRr('r'), B1))
    sm = u([u([e3, sn], 'eqtrd', '%s = %s' % (SUMR, B1)), v1], 'eqtrd', '%s = %s' % (SUMR, MRr('1')))
    GX = EB[:EB.index(' x. sum_ r e.')][2:]
    eb2 = u([sm], 'oveq2d', '%s = ( %s x. %s )' % (EB, GX, MRr('1')))
    e4 = t([eb2], 'ifeq1da', 'if ( C = %s , %s , 0 ) = if ( C = %s , ( %s x. %s ) , 0 )' % (PRN, EB, PRN, GX, MRr('1')))
    s = t([t([ev, e2], 'eqtrd', '%s = if ( C = %s , %s , 0 )' % (EPV().replace('R >.', '1 >.'), PRN, EB)), e4], 'eqtrd',
          '%s = if ( C = %s , ( %s x. %s ) , 0 )' % (EPV().replace('R >.', '1 >.'), PRN, GX, MRr('1')))
    toqed(w, s, 'dshep1'); w.run()
