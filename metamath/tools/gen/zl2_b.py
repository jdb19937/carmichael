"""ZL2 sections B and E: the root number (LConvexity 253-276) and the growth
condition (LConvexity 478-516).  `MM_DB=sorties/zl2.mm python3 tools/gen/zl2_b.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl2lib import *
from lin import linarith, nlinarith
import num

only = sys.argv[1:]

# ---------------------------------------------------------------- zl2rtn: | root number | = 1
if __name__ == '__main__' and (not only or 'zl2rtn' in only):
    w = W('zl2rtn', 'The root number ` g ( X ) / ( _i ^ K N ^ ( 1 / 2 ) ) ` of a primitive character has modulus one '
          '( Lean ` norm_rootNumber_eq_one ` , from ~ dchrgsabs ).')
    NXd = '( N e. NN /\\ X e. %s )' % DCN
    A = '( %s /\\ ( ( N DChrCond X ) = N /\\ K e. NN0 ) )' % NXd
    T = '( N DChrGS X )'
    nx = D(w, A, 'simpl', [], NXd)
    nn = D(w, A, 'simpll', [], 'N e. NN')
    pr = D(w, A, 'simprl', [], '( N DChrCond X ) = N')
    kn = D(w, A, 'simprr', [], 'K e. NN0')
    tc = w.s([nx, w.inst('dchrgscl')], 'syl', '( %s -> %s e. CC )' % (A, T))
    sq = w.s([nx, pr, w.inst('dchrgsabs')], 'syl2anc', '( %s -> ( ( abs ` %s ) ^ 2 ) = N )' % (A, T))
    at = D(w, A, 'abscld', [tc], '( abs ` %s ) e. RR' % T)
    at0 = D(w, A, 'absge0d', [tc], '0 <_ ( abs ` %s )' % T)
    s1 = D(w, A, 'sqrtsqd', [at, at0], '( sqrt ` ( ( abs ` %s ) ^ 2 ) ) = ( abs ` %s )' % (T, T))
    s2 = E(w, A, 'fveq2d', [sq], '( sqrt ` ( ( abs ` %s ) ^ 2 ) )' % T, '( sqrt ` N )')
    s3 = w.s([s2, s1], 'eqtr3d', '( %s -> ( sqrt ` N ) = ( abs ` %s ) )' % (A, T))
    nr = D(w, A, 'nnred', [nn], 'N e. RR')
    ncc = D(w, A, 'nncnd', [nn], 'N e. CC')
    n0 = D(w, A, 'nnrpd', [nn], 'N e. RR+')
    c1 = w.s([ncc, w.inst('cxpsqrt')], 'syl', '( %s -> ( N ^c ( 1 / 2 ) ) = ( sqrt ` N ) )' % A)
    SQ = '( sqrt ` N )'
    sqr = D(w, A, 'resqrtcld', [nr, D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), nr, D(w, A, 'nngt0d', [nn], '0 < N')], '0 <_ N')], '%s e. RR' % SQ)
    sqge = D(w, A, 'sqrtge0d', [nr, D(w, A, 'ltled', [a1(w, A, '0re', '0 e. RR'), nr, D(w, A, 'nngt0d', [nn], '0 < N')], '0 <_ N')], '0 <_ %s' % SQ)
    sqgt = D(w, A, 'sqrtgt0d', [n0], '0 < %s' % SQ)
    sqc = D(w, A, 'recnd', [sqr], '%s e. CC' % SQ)
    ic = a1(w, A, 'ax-icn', '_i e. CC')
    ik = D(w, A, 'expcld', [ic, kn], '( _i ^ K ) e. CC')
    IK = '( _i ^ K )'
    DEN = '( %s x. ( N ^c ( 1 / 2 ) ) )' % IK
    d1 = E(w, A, 'oveq2d', [c1], DEN, '( %s x. %s )' % (IK, SQ))
    a_ik = D(w, A, 'absexpd', [ic, kn], '( abs ` %s ) = ( ( abs ` _i ) ^ K )' % IK)
    a_i = E(w, A, 'oveq1d', [a1(w, A, 'absi', '( abs ` _i ) = 1')], '( ( abs ` _i ) ^ K )', '( 1 ^ K )')
    a_1 = w.s([D(w, A, 'nn0zd', [kn], 'K e. ZZ'), w.inst('1exp')], 'syl', '( %s -> ( 1 ^ K ) = 1 )' % A)
    aik1 = chain(w, A, ['( abs ` %s )' % IK, '( ( abs ` _i ) ^ K )', '( 1 ^ K )', '1'], [a_ik, a_i, a_1])
    asq = D(w, A, 'absidd', [sqr, sqge], '( abs ` %s ) = %s' % (SQ, SQ))
    den2 = '( %s x. %s )' % (IK, SQ)
    am = D(w, A, 'absmuld', [ik, sqc], '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (den2, IK, SQ))
    am2 = E(w, A, 'oveq12d', [aik1, asq], '( ( abs ` %s ) x. ( abs ` %s ) )' % (IK, SQ), '( 1 x. %s )' % SQ)
    am3 = D(w, A, 'mullidd', [sqc], '( 1 x. %s ) = %s' % (SQ, SQ))
    aden = chain(w, A, ['( abs ` %s )' % DEN, '( abs ` %s )' % den2, '( ( abs ` %s ) x. ( abs ` %s ) )' % (IK, SQ), '( 1 x. %s )' % SQ, SQ],
                 [E(w, A, 'fveq2d', [d1], '( abs ` %s )' % DEN, '( abs ` %s )' % den2), am, am2, am3])
    denc = D(w, A, 'mulcld', [ik, D(w, A, 'cxpcld', [ncc, a1(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( N ^c ( 1 / 2 ) ) e. CC')], '%s e. CC' % DEN)
    dab0 = w.s([aden, D(w, A, 'gt0ne0d', [sqgt], '%s =/= 0' % SQ)], 'eqnetrd', '( %s -> ( abs ` %s ) =/= 0 )' % (A, DEN))
    # ( abs ` DEN ) =/= 0 -> DEN =/= 0
    ikn = D(w, A, 'expne0d', [ic, a1(w, A, 'ine0', '_i =/= 0'), D(w, A, 'nn0zd', [kn], 'K e. ZZ')], '%s =/= 0' % IK)
    cxc = D(w, A, 'cxpcld', [ncc, a1(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( N ^c ( 1 / 2 ) ) e. CC')
    cxn = D(w, A, 'cxpne0d', [ncc, D(w, A, 'nnne0d', [nn], 'N =/= 0'), a1(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( N ^c ( 1 / 2 ) ) =/= 0')
    dnz = D(w, A, 'mulne0d', [ik, ikn, cxc, cxn], '%s =/= 0' % DEN)
    q1 = D(w, A, 'absdivd', [tc, denc, dnz], '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (T, DEN, T, DEN))
    q2 = E(w, A, 'oveq12d', [w.s([s3], 'eqcomd', '( %s -> ( abs ` %s ) = %s )' % (A, T, SQ)), aden], '( ( abs ` %s ) / ( abs ` %s ) )' % (T, DEN), '( %s / %s )' % (SQ, SQ))
    q3 = D(w, A, 'dividd', [sqc, D(w, A, 'gt0ne0d', [sqgt], '%s =/= 0' % SQ)], '( %s / %s ) = 1' % (SQ, SQ))
    chain(w, A, ['( abs ` ( %s / %s ) )' % (T, DEN), '( ( abs ` %s ) / ( abs ` %s ) )' % (T, DEN), '( %s / %s )' % (SQ, SQ), '1'], [q1, q2, q3], name='qed')
    go(w, only)

# ---------------------------------------------------------------- zl2grw: P ( 4 + U ) ^ 3 <_ 64 P e ^ U
if __name__ == '__main__' and (not only or 'zl2grw' in only):
    w = W('zl2grw', 'A cubic bound is dominated by an exponential: ` P ( 4 + U ) ^ 3 <_ 64 P e ^ U ` ( the growth condition of '
          '~ rectintpl from a polynomial bound; Lean ` isBigO_double_exp ` ).')
    A = '( ( P e. RR /\\ 0 <_ P ) /\\ ( U e. RR /\\ 0 <_ U ) )'
    pr = D(w, A, 'simpll', [], 'P e. RR')
    p0 = D(w, A, 'simplr', [], '0 <_ P')
    ur = D(w, A, 'simprl', [], 'U e. RR')
    u0 = D(w, A, 'simprr', [], '0 <_ U')
    Q = '( U / 4 )'
    qr = D(w, A, 'redivcld', [ur, a1(w, A, '4re', '4 e. RR'), a1(w, A, '4ne0', '4 =/= 0')], '%s e. RR' % Q)
    # 0 <_ U / 4 by linarith
    cl = Closure(w, A, {'U': ('RR', ur), 'P': ('RR', pr)})
    q0 = linarith(w, A, [u0], '0 <_ %s' % Q, closure=cl)
    X = '( exp ` %s )' % Q
    h1 = w.s([qr, q0, w.inst('bvefge1p')], 'syl2anc', '( %s -> ( 1 + %s ) <_ %s )' % (A, Q, X))
    xr = D(w, A, 'reefcld', [qr], '%s e. RR' % X)
    cl.leaf(X, 'RR', xr)
    h2 = linarith(w, A, [h1], '( 4 + U ) <_ ( 4 x. %s )' % X, closure=cl)
    fu = D(w, A, 'readdcld', [a1(w, A, '4re', '4 e. RR'), ur], '( 4 + U ) e. RR')
    fu0 = linarith(w, A, [u0], '0 <_ ( 4 + U )', closure=cl)
    fx = D(w, A, 'remulcld', [a1(w, A, '4re', '4 e. RR'), xr], '( 4 x. %s ) e. RR' % X)
    n3 = a1(w, A, '3nn0', '3 e. NN0')
    h3 = D(w, A, 'leexp1ad', [fu, fx, n3, fu0, h2], '( ( 4 + U ) ^ 3 ) <_ ( ( 4 x. %s ) ^ 3 )' % X)
    xc = D(w, A, 'recnd', [xr], '%s e. CC' % X)
    h4 = D(w, A, 'mulexpd', [a1(w, A, '4cn', '4 e. CC'), xc, n3], '( ( 4 x. %s ) ^ 3 ) = ( ( 4 ^ 3 ) x. ( %s ^ 3 ) )' % (X, X))
    # 4 ^ 3 = 64
    ep = w.s([w.s([], '4cn', '4 e. CC'), w.s([], '2nn0', '2 e. NN0')], 'pm3.2i', '( 4 e. CC /\\ 2 e. NN0 )')
    ie = w.s([], 'expp1', '( ( 4 e. CC /\\ 2 e. NN0 ) -> ( 4 ^ ( 2 + 1 ) ) = ( ( 4 ^ 2 ) x. 4 ) )')
    e1 = w.s([ep, ie], 'ax-mp', '( 4 ^ ( 2 + 1 ) ) = ( ( 4 ^ 2 ) x. 4 )')
    e2 = w.s([w.s([], '2p1e3', '( 2 + 1 ) = 3')], 'oveq2i', '( 4 ^ ( 2 + 1 ) ) = ( 4 ^ 3 )')
    e3 = w.s([e2, e1], 'eqtr3i', '( 4 ^ 3 ) = ( ( 4 ^ 2 ) x. 4 )')
    s42 = w.s([w.s([w.s([], '4cn', '4 e. CC')], 'sqvali', '( 4 ^ 2 ) = ( 4 x. 4 )'), w.s([], '4t4e16', '( 4 x. 4 ) = ; 1 6')], 'eqtri', '( 4 ^ 2 ) = ; 1 6')
    e4 = w.s([s42], 'oveq1i', '( ( 4 ^ 2 ) x. 4 ) = ( ; 1 6 x. 4 )')
    e5 = num.mul_nat(w, 16, 4)
    e6 = w.s([e3, e4], 'eqtri', '( 4 ^ 3 ) = ( ; 1 6 x. 4 )')
    e7 = w.s([e6, e5], 'eqtri', '( 4 ^ 3 ) = ; 6 4')
    e7d = w.s([e7], 'a1i', '( %s -> ( 4 ^ 3 ) = ; 6 4 )' % A)
    # X ^ 3 = exp ( 3 x. ( U / 4 ) ) <_ exp U
    qc = D(w, A, 'recnd', [qr], '%s e. CC' % Q)
    x3 = w.s([qc, a1(w, A, '3z', '3 e. ZZ'), w.inst('efexp')], 'syl2anc', '( %s -> ( exp ` ( 3 x. %s ) ) = ( %s ^ 3 ) )' % (A, Q, X))
    tq = D(w, A, 'remulcld', [a1(w, A, '3re', '3 e. RR'), qr], '( 3 x. %s ) e. RR' % Q)
    tql = linarith(w, A, [u0], '( 3 x. %s ) <_ U' % Q, closure=cl)
    x4 = efle_(w, A, '( 3 x. %s )' % Q, 'U', tq, ur, tql)
    x5 = w.s([x3, x4], 'eqbrtrrd', '( %s -> ( %s ^ 3 ) <_ ( exp ` U ) )' % (A, X))
    h5 = E(w, A, 'oveq1d', [e7d], '( ( 4 ^ 3 ) x. ( %s ^ 3 ) )' % X, '( ; 6 4 x. ( %s ^ 3 ) )' % X)
    h6 = w.s([h4, h5], 'eqtrd', '( %s -> ( ( 4 x. %s ) ^ 3 ) = ( ; 6 4 x. ( %s ^ 3 ) ) )' % (A, X, X))
    h7 = w.s([h3, h6], 'breqtrd', '( %s -> ( ( 4 + U ) ^ 3 ) <_ ( ; 6 4 x. ( %s ^ 3 ) ) )' % (A, X))
    x3r = D(w, A, 'reexpcld', [xr, n3], '( %s ^ 3 ) e. RR' % X)
    eu = D(w, A, 'reefcld', [ur], '( exp ` U ) e. RR')
    cl.leaf('( %s ^ 3 )' % X, 'RR', x3r); cl.leaf('( exp ` U )', 'RR', eu)
    c4 = D(w, A, 'reexpcld', [fu, n3], '( ( 4 + U ) ^ 3 ) e. RR')
    cl.leaf('( ( 4 + U ) ^ 3 )', 'RR', c4)
    h8 = linarith(w, A, [h7, x5], '( ( 4 + U ) ^ 3 ) <_ ( ; 6 4 x. ( exp ` U ) )', closure=cl)
    sixf = w.s([w.s([w.s([], '6nn0', '6 e. NN0'), w.s([], '4nn0', '4 e. NN0')], 'deccl', '; 6 4 e. NN0')], 'nn0rei', '; 6 4 e. RR')
    sf = w.s([sixf], 'a1i', '( %s -> ; 6 4 e. RR )' % A)
    se = D(w, A, 'remulcld', [sf, eu], '( ; 6 4 x. ( exp ` U ) ) e. RR')
    h9 = D(w, A, 'lemul2ad', [c4, se, pr, p0, h8], '( P x. ( ( 4 + U ) ^ 3 ) ) <_ ( P x. ( ; 6 4 x. ( exp ` U ) ) )')
    pc = D(w, A, 'recnd', [pr], 'P e. CC')
    r1 = D(w, A, 'mul12d', [pc, D(w, A, 'recnd', [sf], '; 6 4 e. CC'), D(w, A, 'recnd', [eu], '( exp ` U ) e. CC')],
           '( P x. ( ; 6 4 x. ( exp ` U ) ) ) = ( ; 6 4 x. ( P x. ( exp ` U ) ) )')
    r2 = D(w, A, 'mulassd', [D(w, A, 'recnd', [sf], '; 6 4 e. CC'), pc, D(w, A, 'recnd', [eu], '( exp ` U ) e. CC')],
           '( ( ; 6 4 x. P ) x. ( exp ` U ) ) = ( ; 6 4 x. ( P x. ( exp ` U ) ) )')
    r3 = w.s([r1, r2], 'eqtr4d', '( %s -> ( P x. ( ; 6 4 x. ( exp ` U ) ) ) = ( ( ; 6 4 x. P ) x. ( exp ` U ) ) )' % A)
    w.qed([h9, r3], 'breqtrd', '( %s -> ( P x. ( ( 4 + U ) ^ 3 ) ) <_ ( ( ; 6 4 x. P ) x. ( exp ` U ) ) )' % A)
    go(w, only)
