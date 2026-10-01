"""Sortie EF4: L ( 1 , chi ) =/= 0 (ef4ab1: the Abel sum at 1 of a sequence with bounded partial sums is the sum of
A ( n ) / n; ef4l1: set.mm's dchrisumn0 through ef4ab1), the zero set of E as zeros of L (ef4zf)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
from c8_o import numst
import congr as _cg
import lin
lin.FASTPATH = True

SI = lambda k: 'sum_ i e. ( 1 ... %s ) ( A ` i )' % k
SQ_ = '( q e. NN |-> %s )' % SI('q')
DIF = lambda k: '( ( %s ^c -u 1 ) - ( ( %s + 1 ) ^c -u 1 ) )' % (k, k)
ABK = lambda k: '( %s x. %s )' % (SI(k), DIF(k))
DQ = '( n e. NN |-> ( ( A ` n ) / n ) )'
SEQD = 'seq 1 ( + , %s )' % DQ
FA = '( b e. NN |-> %s )' % ABK('b')
SEQA = 'seq 1 ( + , %s )' % FA
X = '( e e. NN |-> ( %s ` ( e + 1 ) ) )' % SEQD
YB = lambda n: '( ( %s ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u 1 ) )' % (SQ_, n, n)
Y = '( n e. NN |-> %s )' % YB('n')
AY = '( n e. NN |-> ( abs ` %s ) )' % YB('n')
BN = '( n e. NN |-> ( B / n ) )'


def recip(c, x, xn):
    """( A -> ( x ^c -u 1 ) = ( 1 / x ) ) for xn : ( A -> x e. NN )"""
    w = c.w
    xc = c([xn], 'nncnd', '%s e. CC' % x)
    e1 = c([xc, c([xn], 'nnne0d', '%s =/= 0' % x), c.a1(w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC'), w.inst('cxpneg')], 'syl3anc', '( %s ^c -u 1 ) = ( 1 / ( %s ^c 1 ) )' % (x, x))
    return c([e1, c([c([xc, w.inst('cxp1')], 'syl', '( %s ^c 1 ) = %s' % (x, x))], 'oveq2d', '( 1 / ( %s ^c 1 ) ) = ( 1 / %s )' % (x, x))], 'eqtrd', '( %s ^c -u 1 ) = ( 1 / %s )' % (x, x))


def gen_ab1():
    w = W('ef4ab1', 'The Abel sum at ` s = 1 ` : for ` A ` with bounded partial sums, ` sum_k S_k ( 1 / k - 1 / ( k + 1 ) ) ` is the sum of the convergent series ` A ( n ) / n ` (summation by parts ~ abagr2 ; the boundary term ` S_(n+1) / ( n + 1 ) ` tends to 0 by ~ climsqz2 ).')
    A00, G = ante_of(S['ef4ab1'])
    SO = lambda k: 'sum_ o e. ( 1 ... %s ) ( A ` o )' % k
    ALI, ALO = 'A. m e. NN ( abs ` %s ) <_ B' % SI('m'), 'A. m e. NN ( abs ` %s ) <_ B' % SO('m')
    A0 = A00.replace(ALI, ALO)
    c = Ctx(w, A0)
    af = c.g('A : NN --> CC'); br = c.g('B e. RR')
    alm = c.g(ALO)
    cv = c.g('%s ~~> L' % SEQD)
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = c([], '1zzd', '1 e. ZZ')
    nnex = w.s([], 'nnex', 'NN e. _V')
    mex = lambda M: c.a1(w.s([nnex], 'mptex', '%s e. _V' % M), '%s e. _V' % M)
    psf = c([af, w.inst('psff')], 'syl', '%s : NN --> CC' % SQ_)
    Ap = '( %s /\\ p e. NN )' % A0
    cp = Ctx(w, Ap)
    L = lambda st: lift(w, st, Ap)
    pn = cp([], 'simpr', 'p e. NN')
    # X ~~> L
    xp, _ = _cg.mptval(w, Ap, 'e', 'NN', '( %s ` ( e + 1 ) )' % SEQD, 'p', pn, gen=w.g)
    sh = c([nnuz, one, one, mex(X), c.a1(w.s([], 'seqex', '%s e. _V' % SEQD), '%s e. _V' % SEQD), cp([xp], 'eqcomd', '( %s ` ( p + 1 ) ) = ( %s ` p )' % (SEQD, X))],
           'climshft2', '( %s ~~> L <-> %s ~~> L )' % (X, SEQD))
    xl = c([cv, sh], 'mpbird', '%s ~~> L' % X)
    # Y ~~> 0
    p1 = cp([pn], 'peano2nnd', '( p + 1 ) e. NN')
    r1 = cp([p1], 'nnrpd', '( p + 1 ) e. RR+')
    rk1 = cp([r1], 'rpreccld', '( 1 / ( p + 1 ) ) e. RR+')
    ic2 = recip(cp, '( p + 1 )', p1)
    icc = cp([ic2, cp([rk1], 'rpcnd', '( 1 / ( p + 1 ) ) e. CC')], 'eqeltrd', '( ( p + 1 ) ^c -u 1 ) e. CC')
    sk1 = cp([L(psf), p1], 'ffvelcdmd', '( %s ` ( p + 1 ) ) e. CC' % SQ_)
    yk, _ = _cg.mptval(w, Ap, 'n', 'NN', YB('n'), 'p', pn, gen=w.g)
    ykc = cp([sk1, icc], 'mulcld', '%s e. CC' % YB('p'))
    ykc2 = cp([yk, ykc], 'eqeltrd', '( %s ` p ) e. CC' % Y)
    ay, _ = _cg.mptval(w, Ap, 'n', 'NN', '( abs ` %s )' % YB('n'), 'p', pn, gen=w.g)
    ay2 = cp([ay, cp([cp([yk], 'fveq2d', '( abs ` ( %s ` p ) ) = ( abs ` %s )' % (Y, YB('p')))], 'eqcomd', '( abs ` %s ) = ( abs ` ( %s ` p ) )' % (YB('p'), Y))], 'eqtrd',
             '( %s ` p ) = ( abs ` ( %s ` p ) )' % (AY, Y))
    ab0 = c([nnuz, one, mex(Y), mex(AY), ykc2, ay2], 'climabs0', '( %s ~~> 0 <-> %s ~~> 0 )' % (Y, AY))
    bn = c([c([br], 'recnd', 'B e. CC'), w.inst('divcnv')], 'syl', '%s ~~> 0' % BN)
    bk, _ = _cg.mptval(w, Ap, 'n', 'NN', '( B / n )', 'p', pn, gen=w.g)
    pr_ = cp([pn], 'nnrpd', 'p e. RR+')
    bkr = cp([bk, cp([L(br), pr_], 'rerpdivcld', '( B / p ) e. RR')], 'eqeltrd', '( %s ` p ) e. RR' % BN)
    ykr = cp([ay, cp([ykc], 'abscld', '( abs ` %s ) e. RR' % YB('p'))], 'eqeltrd', '( %s ` p ) e. RR' % AY)
    sb0, _ = ral_at(w, Ap, L(alm), 'm', '( p + 1 )', '( abs ` %s ) <_ B' % SO('m'), p1)
    cbo = w.s([w.s([], 'fveq2', '( o = i -> ( A ` o ) = ( A ` i ) )')], 'cbvsumv', '%s = %s' % (SO('( p + 1 )'), SI('( p + 1 )')))
    sb = cp([cp([cp([cp.a1(cbo, '%s = %s' % (SO('( p + 1 )'), SI('( p + 1 )')))], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (SO('( p + 1 )'), SI('( p + 1 )')))], 'eqcomd', '( abs ` %s ) = ( abs ` %s )' % (SI('( p + 1 )'), SO('( p + 1 )'))), sb0], 'eqbrtrd', '( abs ` %s ) <_ B' % SI('( p + 1 )'))
    sq1, _ = _cg.mptval(w, Ap, 'q', 'NN', SI('q'), '( p + 1 )', p1, exs=cp.a1(w.s([], 'sumex', '%s e. _V' % SI('( p + 1 )')), '%s e. _V' % SI('( p + 1 )')), gen=w.g)
    sb2 = cp([cp([sq1], 'fveq2d', '( abs ` ( %s ` ( p + 1 ) ) ) = ( abs ` %s )' % (SQ_, SI('( p + 1 )'))), sb], 'eqbrtrd', '( abs ` ( %s ` ( p + 1 ) ) ) <_ B' % SQ_)
    am = cp([sk1, icc], 'absmuld', '( abs ` %s ) = ( ( abs ` ( %s ` ( p + 1 ) ) ) x. ( abs ` ( ( p + 1 ) ^c -u 1 ) ) )' % (YB('p'), SQ_))
    ai = cp([cp([ic2], 'fveq2d', '( abs ` ( ( p + 1 ) ^c -u 1 ) ) = ( abs ` ( 1 / ( p + 1 ) ) )'),
             cp([cp([rk1], 'rpred', '( 1 / ( p + 1 ) ) e. RR'), cp([rk1], 'rpge0d', '0 <_ ( 1 / ( p + 1 ) )')], 'absidd', '( abs ` ( 1 / ( p + 1 ) ) ) = ( 1 / ( p + 1 ) )')], 'eqtrd',
            '( abs ` ( ( p + 1 ) ^c -u 1 ) ) = ( 1 / ( p + 1 ) )')
    am2 = cp([am, cp([ai], 'oveq2d', '( ( abs ` ( %s ` ( p + 1 ) ) ) x. ( abs ` ( ( p + 1 ) ^c -u 1 ) ) ) = ( ( abs ` ( %s ` ( p + 1 ) ) ) x. ( 1 / ( p + 1 ) ) )' % (SQ_, SQ_))], 'eqtrd',
             '( abs ` %s ) = ( ( abs ` ( %s ` ( p + 1 ) ) ) x. ( 1 / ( p + 1 ) ) )' % (YB('p'), SQ_))
    asr = cp([sk1], 'abscld', '( abs ` ( %s ` ( p + 1 ) ) ) e. RR' % SQ_)
    b0 = lin8(w, Ap, [cp([sk1], 'absge0d', '0 <_ ( abs ` ( %s ` ( p + 1 ) ) )' % SQ_), sb2], '0 <_ B', {'B': L(br), '( abs ` ( %s ` ( p + 1 ) ) )' % SQ_: asr})
    rr1 = cp([rk1], 'rpred', '( 1 / ( p + 1 ) ) e. RR')
    m1 = cp([asr, L(br), rr1, cp([rk1], 'rpge0d', '0 <_ ( 1 / ( p + 1 ) )'), sb2], 'lemul1ad', '( ( abs ` ( %s ` ( p + 1 ) ) ) x. ( 1 / ( p + 1 ) ) ) <_ ( B x. ( 1 / ( p + 1 ) ) )' % SQ_)
    prr = cp([pn], 'nnred', 'p e. RR')
    rle = cp([lin8(w, Ap, [], 'p <_ ( p + 1 )', {'p': prr}), cp([pr_, r1], 'lerecd', '( p <_ ( p + 1 ) <-> ( 1 / ( p + 1 ) ) <_ ( 1 / p ) )')], 'mpbid', '( 1 / ( p + 1 ) ) <_ ( 1 / p )')
    m2 = cp([rr1, cp([pn], 'nnrecred', '( 1 / p ) e. RR'), L(br), b0, rle], 'lemul2ad', '( B x. ( 1 / ( p + 1 ) ) ) <_ ( B x. ( 1 / p ) )')
    m3 = cp([cp([L(br)], 'recnd', 'B e. CC'), cp([pn], 'nncnd', 'p e. CC'), cp([pn], 'nnne0d', 'p =/= 0')], 'divrecd', '( B / p ) = ( B x. ( 1 / p ) )')
    lq = le_tr(w, Ap, cp([am2, m1], 'eqbrtrd', '( abs ` %s ) <_ ( B x. ( 1 / ( p + 1 ) ) )' % YB('p')), '( abs ` %s )' % YB('p'), '( B x. ( 1 / ( p + 1 ) ) )',
               cp([m2, cp([m3], 'eqcomd', '( B x. ( 1 / p ) ) = ( B / p )')], 'breqtrd', '( B x. ( 1 / ( p + 1 ) ) ) <_ ( B / p )'), '( B / p )')
    gle = cp([cp([ay, lq], 'eqbrtrd', '( %s ` p ) <_ ( B / p )' % AY), cp([bk], 'eqcomd', '( B / p ) = ( %s ` p )' % BN)], 'breqtrd', '( %s ` p ) <_ ( %s ` p )' % (AY, BN))
    g0 = cp([cp([ykc], 'absge0d', '0 <_ ( abs ` %s )' % YB('p')), cp([ay], 'eqcomd', '( abs ` %s ) = ( %s ` p )' % (YB('p'), AY))], 'breqtrd', '0 <_ ( %s ` p )' % AY)
    sq = c([nnuz, one, bn, mex(AY), bkr, ykr, gle, g0], 'climsqz2', '%s ~~> 0' % AY)
    y0 = c([sq, ab0], 'mpbird', '%s ~~> 0' % Y)
    # seq_A ( p ) = X ( p ) - Y ( p )
    fs = tsub(stmt('abagr2'), {'Z': '1', 'N': 'p'})
    fsa, fsc = ante_of(fs)
    ag = cp([cp([cp([L(af), cp.a1(w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')], 'jca', '( A : NN --> CC /\\ 1 e. CC )'), pn], 'jca', fsa), w.inst('abagr2')], 'syl', fsc)
    S1, rest = fsc.split(' = ', 1)
    S1 = S1
    SJ = 'sum_ j e. ( 1 ... p ) ( ( %s ` j ) x. %s )' % (SQ_, DIF('j'))
    # S1 = sum_ ( 1 ... ( p + 1 ) ) A_k / k = X ( p )
    Akk = '( %s /\\ k e. ( 1 ... ( p + 1 ) ) )' % Ap
    ckk = Ctx(w, Akk)
    kin = ckk([], 'simpr', 'k e. ( 1 ... ( p + 1 ) )')
    kn = ckk([kin, w.inst('elfznn')], 'syl', 'k e. NN')
    akc = ckk([lift(w, af, Akk), kn], 'ffvelcdmd', '( A ` k ) e. CC')
    dk, _ = _cg.mptval(w, Akk, 'n', 'NN', '( ( A ` n ) / n )', 'k', kn, gen=w.g)
    kre = recip(ckk, 'k', kn)
    dv = ckk([akc, ckk([kn], 'nncnd', 'k e. CC'), ckk([kn], 'nnne0d', 'k =/= 0')], 'divrecd', '( ( A ` k ) / k ) = ( ( A ` k ) x. ( 1 / k ) )')
    tk = ckk([dv, ckk([ckk([kre], 'eqcomd', '( 1 / k ) = ( k ^c -u 1 )')], 'oveq2d', '( ( A ` k ) x. ( 1 / k ) ) = ( ( A ` k ) x. ( k ^c -u 1 ) )')], 'eqtrd', '( ( A ` k ) / k ) = ( ( A ` k ) x. ( k ^c -u 1 ) )')
    dk2 = ckk([dk, tk], 'eqtrd', '( %s ` k ) = ( ( A ` k ) x. ( k ^c -u 1 ) )' % DQ)
    tkc = ckk([akc, ckk([kre, ckk([ckk([kn], 'nnrecred', '( 1 / k ) e. RR')], 'recnd', '( 1 / k ) e. CC')], 'eqeltrd', '( k ^c -u 1 ) e. CC')], 'mulcld', '( ( A ` k ) x. ( k ^c -u 1 ) ) e. CC')
    xs = cp([dk2, cp([p1, w.s([], 'elnnuz', '( ( p + 1 ) e. NN <-> ( p + 1 ) e. ( ZZ>= ` 1 ) )')], 'sylib', '( p + 1 ) e. ( ZZ>= ` 1 )'), tkc], 'fsumser', '%s = ( %s ` ( p + 1 ) )' % (S1, SEQD))
    xv = cp([xs, cp([xp], 'eqcomd', '( %s ` ( p + 1 ) ) = ( %s ` p )' % (SEQD, X))], 'eqtrd', '%s = ( %s ` p )' % (S1, X))
    # seq_A ( p ) = SJ
    Ajk = '( %s /\\ k e. ( 1 ... p ) )' % Ap
    cjk = Ctx(w, Ajk)
    kin2 = cjk([], 'simpr', 'k e. ( 1 ... p )')
    kn2 = cjk([kin2, w.inst('elfznn')], 'syl', 'k e. NN')
    fk, _ = _cg.mptval(w, Ajk, 'b', 'NN', ABK('b'), 'k', kn2, exs=cjk([], 'ovexd', '%s e. _V' % ABK('k')), gen=w.g)
    abc = ab_cc(cjk, 'k', kn2, lift(w, af, Ajk))
    sa = cp([fk, cp([pn, w.s([], 'elnnuz', '( p e. NN <-> p e. ( ZZ>= ` 1 ) )')], 'sylib', 'p e. ( ZZ>= ` 1 )'), abc], 'fsumser', 'sum_ k e. ( 1 ... p ) %s = ( %s ` p )' % (ABK('k'), SEQA))
    sqk, _ = _cg.mptval(w, Ajk, 'q', 'NN', SI('q'), 'k', kn2, exs=cjk.a1(w.s([], 'sumex', '%s e. _V' % SI('k')), '%s e. _V' % SI('k')), gen=w.g)
    e2 = cp([cjk([cjk([sqk], 'eqcomd', '%s = ( %s ` k )' % (SI('k'), SQ_))], 'oveq1d', '%s = ( ( %s ` k ) x. %s )' % (ABK('k'), SQ_, DIF('k')))], 'sumeq2dv',
            'sum_ k e. ( 1 ... p ) %s = sum_ k e. ( 1 ... p ) ( ( %s ` k ) x. %s )' % (ABK('k'), SQ_, DIF('k')))
    cb = w.s([w.s([w.s([], 'fveq2', '( k = j -> ( %s ` k ) = ( %s ` j ) )' % (SQ_, SQ_)), subst(w, DIF('k'), 'k', 'j')[0]], 'oveq12d', '( k = j -> ( ( %s ` k ) x. %s ) = ( ( %s ` j ) x. %s ) )' % (SQ_, DIF('k'), SQ_, DIF('j')))],
             'cbvsumv', 'sum_ k e. ( 1 ... p ) ( ( %s ` k ) x. %s ) = %s' % (SQ_, DIF('k'), SJ))
    sa2 = cp([cp([sa], 'eqcomd', '( %s ` p ) = sum_ k e. ( 1 ... p ) %s' % (SEQA, ABK('k'))), cp([e2, cp.a1(cb, 'sum_ k e. ( 1 ... p ) ( ( %s ` k ) x. %s ) = %s' % (SQ_, DIF('k'), SJ))], 'eqtrd', 'sum_ k e. ( 1 ... p ) %s = %s' % (ABK('k'), SJ))], 'eqtrd',
             '( %s ` p ) = %s' % (SEQA, SJ))
    # SJ = S1 - YB
    sjc = cp([cp([], 'fzfid', '( 1 ... p ) e. Fin'), sj_cc(w, Ap, psf)], 'fsumcl', '%s e. CC' % SJ)
    e3 = cp([cp([ag], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (S1, YB('p'), YB('p'), SJ, YB('p'))), cp([ykc, sjc], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (YB('p'), SJ, YB('p'), SJ))], 'eqtrd', '( %s - %s ) = %s' % (S1, YB('p'), SJ))
    hv = cp([sa2, cp([e3], 'eqcomd', '%s = ( %s - %s )' % (SJ, S1, YB('p')))], 'eqtrd', '( %s ` p ) = ( %s - %s )' % (SEQA, S1, YB('p')))
    hv2 = cp([hv, cp([xv, cp([yk], 'eqcomd', '%s = ( %s ` p )' % (YB('p'), Y))], 'oveq12d', '( %s - %s ) = ( ( %s ` p ) - ( %s ` p ) )' % (S1, YB('p'), X, Y))], 'eqtrd', '( %s ` p ) = ( ( %s ` p ) - ( %s ` p ) )' % (SEQA, X, Y))
    s1c = cp([cp([], 'fzfid', '( 1 ... ( p + 1 ) ) e. Fin'), tkc], 'fsumcl', '%s e. CC' % S1)
    xpc = cp([xv, s1c], 'eqeltrrd', '( %s ` p ) e. CC' % X)
    csub = c([nnuz, one, xl, c.a1(w.s([], 'seqex', '%s e. _V' % SEQA), '%s e. _V' % SEQA), y0, xpc, ykc2, hv2], 'climsub', '%s ~~> ( L - 0 )' % SEQA)
    lc = c([xl, w.inst('climcl')], 'syl', 'L e. CC')
    cl2 = c([csub, c([lc], 'subid1d', '( L - 0 ) = L')], 'breqtrd', '%s ~~> L' % SEQA)
    Ak2 = '( %s /\\ k e. NN )' % A0
    ck2 = Ctx(w, Ak2)
    kn3 = ck2([], 'simpr', 'k e. NN')
    fk3, _ = _cg.mptval(w, Ak2, 'b', 'NN', ABK('b'), 'k', kn3, exs=ck2([], 'ovexd', '%s e. _V' % ABK('k')), gen=w.g)
    abc3 = ab_cc(ck2, 'k', kn3, lift(w, af, Ak2))
    fin = c([nnuz, one, fk3, abc3, cl2], 'isumclim', G)
    cbm = w.s([w.s([], 'fveq2', '( i = o -> ( A ` i ) = ( A ` o ) )')], 'cbvsumv', '%s = %s' % (SI('m'), SO('m')))
    rb = w.s([w.s([w.s([cbm], 'fveq2i', '( abs ` %s ) = ( abs ` %s )' % (SI('m'), SO('m')))], 'breq1i', '( ( abs ` %s ) <_ B <-> ( abs ` %s ) <_ B )' % (SI('m'), SO('m')))], 'ralbii', '( %s <-> %s )' % (ALI, ALO))
    c0 = Ctx(w, A00)
    p0 = top_and(A00)
    q0 = top_and(p0[0])
    a0 = c0([c0([c0.g(q0[0]), c0.g(q0[1]), c0([c0.g(ALI), c0.a1(rb, '( %s <-> %s )' % (ALI, ALO))], 'mpbid', ALO)], '3jca', top_and(A0)[0]), c0.g(p0[1])], 'jca', A0)
    w.qed([a0, fin], 'syl', S['ef4ab1'])
    return run8(w)



CHX = lambda n: '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` %s ) )' % n
AM = '( q e. NN |-> %s )' % CHX('q')
FD = '( a e. NN |-> ( %s / a ) )' % CHX('a')
SEQF = 'seq 1 ( + , %s )' % FD
RG = 'A. y e. ( 1 [,) +oo ) ( abs ` ( ( %s ` ( |_ ` y ) ) - t ) ) <_ ( c / y )' % SEQF


def dirith_hyps(w, A, nn, xb, xn1):
    """the eight hypotheses of set.mm's dirith section at Z/nZ, ZRHom, DChr ( the eqid ones closed )"""
    Z, L_, G_ = '( Z/nZ ` N )', '( ZRHom ` ( Z/nZ ` N ) )', '( DChr ` N )'
    return [w.s([], 'eqid', '%s = %s' % (Z, Z)), w.s([], 'eqid', '%s = %s' % (L_, L_)), nn, w.s([], 'eqid', '%s = %s' % (G_, G_)),
            w.s([], 'eqid', '( Base ` %s ) = ( Base ` %s )' % (G_, G_)), w.s([], 'eqid', '( 0g ` %s ) = ( 0g ` %s )' % (G_, G_)), xb, xn1]


def gen_l1():
    w = W('ef4l1', 'Dirichlet: ` L ( 1 , chi ) =/= 0 ` for ` chi ` nonprincipal, in the Abel form of ` L ` ( Lean ` LFunction_ne_zero_of_one_le_re ` at ` s = 1 ` ; set.mm ~ dchrisumn0 through ~ ef4ab1 ).')
    A0, G = ante_of(S['ef4l1'])
    c = Ctx(w, A0)
    nx = c([], 'simpl', NX)
    nn = c([nx, w.inst('simpl')], 'syl', 'N e. NN')
    xb = c([nx, w.inst('simpr')], 'syl', 'X e. ( Base ` ( DChr ` N ) )')
    xn1 = c([], 'simpr', 'X =/= ( 0g ` ( DChr ` N ) )')
    EX = 'E. t E. c e. ( 0 [,) +oo ) ( %s ~~> t /\\ %s )' % (SEQF, RG)
    lem = c(dirith_hyps(w, A0, nn, xb, xn1) + [w.s([], 'eqid', '%s = %s' % (FD, FD))], 'dchrmusumlema', EX)
    A1 = '( ( %s /\\ c e. ( 0 [,) +oo ) ) /\\ ( %s ~~> t /\\ %s ) )' % (A0, SEQF, RG)
    c1 = Ctx(w, A1)
    L1 = lambda st: lift(w, st, A1)
    cin = c1([w.s([], 'simpr', '( ( %s /\\ c e. ( 0 [,) +oo ) ) -> c e. ( 0 [,) +oo ) )' % A0)], 'adantr', 'c e. ( 0 [,) +oo )')
    tv = c1([], 'simprl', '%s ~~> t' % SEQF)
    rg = c1([], 'simprr', RG)
    t0 = c1(dirith_hyps(w, A1, L1(nn), L1(xb), L1(xn1)) + [w.s([], 'eqid', '%s = %s' % (FD, FD)), cin, tv, rg], 'dchrisumn0', 't =/= 0')
    # LFN ( 1 ) = the Abel sum at 1
    one_hp = c1([c1.a1(w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC'), c1([c1.a1(w.s([], '0lt1', '0 < 1'), '0 < 1'), c1([c1.a1(w.s([], 're1', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'eqcomd', '1 = ( Re ` 1 )')], 'breqtrd', '0 < ( Re ` 1 )')], 'jca', '( 1 e. CC /\\ 0 < ( Re ` 1 ) )')
    hpe = c1([c1.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( 1 e. %s <-> ( 1 e. CC /\\ 0 < ( Re ` 1 ) ) )' % HP0)
    ohp = c1([one_hp, hpe], 'mpbird', '1 e. %s' % HP0)
    import c9lib as _c9
    lv, lvv = _cg.mptval(w, A1, 's', HP0, _c9.LSs('s'), '1', ohp, exs=c1.a1(w.s([], 'sumex', '%s e. _V' % _c9.LSs('1')), '%s e. _V' % _c9.LSs('1')), gen=w.g)
    # ef4ab1 at A = AM, B = N, L = t
    CF = tsub(stmt('lchrcfb'), {})
    cfa, cfc = ante_of(CF)
    cfb = c1([L1(nx), w.inst('lchrcfb')], 'syl', cfc)
    amf = c1([cfb, w.inst('simp1')], 'syl', '%s : NN --> CC' % AM)
    CS = stmt('lchrcsf')
    csa, csc = ante_of(CS)
    csf = c1([L1(c.g(CHI)), w.inst('lchrcsf')], 'syl', csc)
    nr = c1([csf, w.inst('simp2')], 'syl', 'N e. RR')
    SQX = '( q e. NN |-> sum_ i e. ( 1 ... q ) %s )' % CHX('i')
    alc = c1([csf, w.inst('simp3')], 'syl', 'A. m e. NN ( abs ` ( %s ` m ) ) <_ N' % SQX)
    Am = '( %s /\\ m e. NN )' % A1
    cm = Ctx(w, Am)
    mn = cm([], 'simpr', 'm e. NN')
    b1 = cm([mn, cm([lift(w, alc, Am), w.inst('rsp')], 'syl', '( m e. NN -> ( abs ` ( %s ` m ) ) <_ N )' % SQX)], 'mpd', '( abs ` ( %s ` m ) ) <_ N' % SQX)
    sqm, _ = _cg.mptval(w, Am, 'q', 'NN', 'sum_ i e. ( 1 ... q ) %s' % CHX('i'), 'm', mn, exs=cm.a1(w.s([], 'sumex', 'sum_ i e. ( 1 ... m ) %s e. _V' % CHX('i')), 'sum_ i e. ( 1 ... m ) %s e. _V' % CHX('i')), gen=w.g)
    Ai = '( %s /\\ i e. ( 1 ... m ) )' % Am
    ci = Ctx(w, Ai)
    iv = ci([ci([lift(w, nx, Ai), ci([ci([], 'simpr', 'i e. ( 1 ... m )'), w.inst('elfznn')], 'syl', 'i e. NN')], 'jca', '( %s /\\ i e. NN )' % NX), w.inst('lchrval')], 'syl', '( %s ` i ) = %s' % (AM, CHX('i')))
    se = cm([ci([iv], 'eqcomd', '%s = ( %s ` i )' % (CHX('i'), AM))], 'sumeq2dv', 'sum_ i e. ( 1 ... m ) %s = sum_ i e. ( 1 ... m ) ( %s ` i )' % (CHX('i'), AM))
    b2 = cm([cm([cm([cm([sqm, se], 'eqtrd', '( %s ` m ) = sum_ i e. ( 1 ... m ) ( %s ` i )' % (SQX, AM))], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) )' % (SQX, AM))], 'eqcomd',
               '( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) = ( abs ` ( %s ` m ) )' % (AM, SQX)), b1], 'eqbrtrd', '( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ N' % AM)
    alm = c1([b2], 'ralrimiva', 'A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ N' % AM)
    # the series of A ( n ) / n is the series F of set.mm
    An = '( %s /\\ n e. NN )' % A1
    cn = Ctx(w, An)
    nv = cn([cn([lift(w, nx, An), cn([], 'simpr', 'n e. NN')], 'jca', '( %s /\\ n e. NN )' % NX), w.inst('lchrval')], 'syl', '( %s ` n ) = %s' % (AM, CHX('n')))
    me = c1([cn([nv], 'oveq1d', '( ( %s ` n ) / n ) = ( %s / n )' % (AM, CHX('n')))], 'mpteq2dva', '( n e. NN |-> ( ( %s ` n ) / n ) ) = ( n e. NN |-> ( %s / n ) )' % (AM, CHX('n')))
    cbm = w.s([w.s([w.s([], 'fveq2', '( n = a -> ( ( ZRHom ` ( Z/nZ ` N ) ) ` n ) = ( ( ZRHom ` ( Z/nZ ` N ) ) ` a ) )')], 'fveq2d', '( n = a -> %s = %s )' % (CHX('n'), CHX('a'))), w.s([], 'id', '( n = a -> n = a )')], 'oveq12d',
              '( n = a -> ( %s / n ) = ( %s / a ) )' % (CHX('n'), CHX('a')))
    cb = w.s([cbm], 'cbvmptv', '( n e. NN |-> ( %s / n ) ) = %s' % (CHX('n'), FD))
    me2 = c1([me, c1.a1(cb, '( n e. NN |-> ( %s / n ) ) = %s' % (CHX('n'), FD))], 'eqtrd', '( n e. NN |-> ( ( %s ` n ) / n ) ) = %s' % (AM, FD))
    sq = c1([me2], 'seqeq3d', 'seq 1 ( + , ( n e. NN |-> ( ( %s ` n ) / n ) ) ) = %s' % (AM, SEQF))
    tv2 = c1([tv, c1([sq], 'breq1d', '( seq 1 ( + , ( n e. NN |-> ( ( %s ` n ) / n ) ) ) ~~> t <-> %s ~~> t )' % (AM, SEQF))], 'mpbird', 'seq 1 ( + , ( n e. NN |-> ( ( %s ` n ) / n ) ) ) ~~> t' % AM)
    AB = tsub(S['ef4ab1'], {'A': AM, 'B': 'N', 'L': 't'})
    aba, abc = ante_of(AB)
    ab = c1([conj(w, A1, aba, {'%s : NN --> CC' % AM: amf, 'N e. RR': nr, top_and(top_and(aba)[0])[2]: alm, top_and(aba)[1]: tv2}), w.inst('ef4ab1')], 'syl', abc)
    # LSs ( 1 ) = the ef4ab1 sum
    Ak = '( %s /\\ k e. NN )' % A1
    ck = Ctx(w, Ak)
    Aki = '( %s /\\ i e. ( 1 ... k ) )' % Ak
    cki = Ctx(w, Aki)
    ivk = cki([cki([lift(w, nx, Aki), cki([cki([], 'simpr', 'i e. ( 1 ... k )'), w.inst('elfznn')], 'syl', 'i e. NN')], 'jca', '( %s /\\ i e. NN )' % NX), w.inst('lchrval')], 'syl', '( %s ` i ) = %s' % (AM, CHX('i')))
    sek = ck([ivk], 'sumeq2dv', 'sum_ i e. ( 1 ... k ) ( %s ` i ) = sum_ i e. ( 1 ... k ) %s' % (AM, CHX('i')))
    DK = '( ( k ^c -u 1 ) - ( ( k + 1 ) ^c -u 1 ) )'
    tk = ck([sek], 'oveq1d', '( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s ) = ( sum_ i e. ( 1 ... k ) %s x. %s )' % (AM, DK, CHX('i'), DK))
    se2 = c1([tk], 'sumeq2dv', '%s = %s' % (abc.split(' = ')[0], lvv))
    l1t = c1([lv, c1([c1([se2], 'eqcomd', '%s = %s' % (lvv, abc.split(' = ')[0])), ab], 'eqtrd', '%s = t' % lvv)], 'eqtrd', '( %s ` 1 ) = t' % LFN)
    ne = c1([t0, c1([l1t], 'neeq1d', '( ( %s ` 1 ) =/= 0 <-> t =/= 0 )' % LFN)], 'mpbird', '( %s ` 1 ) =/= 0' % LFN)
    r1 = w.s([ne], 'ex', '( ( %s /\\ c e. ( 0 [,) +oo ) ) -> ( ( %s ~~> t /\\ %s ) -> %s ) )' % (A0, SEQF, RG, G))
    r2 = c([r1], 'rexlimdva', '( E. c e. ( 0 [,) +oo ) ( %s ~~> t /\\ %s ) -> %s )' % (SEQF, RG, G))
    r3 = c([r2], 'exlimdv', '( %s -> %s )' % (EX, G))
    w.qed([lem, r3], 'mpd', S['ef4l1'])
    return run8(w)



def box_hp(w, A, r, rin, ar, a0, tr, a='A'):
    """( A -> r e. HP0 ) for rin : ( A -> r e. BOX(a,T) ), 0 < a"""
    c = Ctx(w, A)
    Aa, Bb = '( %s + ( _i x. -u T ) )' % a, '( 1 + ( _i x. T ) )'
    ntr = c([tr], 'renegcld', '-u T e. RR')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    ac = c([c([ar], 'recnd', '%s e. CC' % a), c([ic, c([ntr], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % Aa)
    bc = c([c.a1(w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC'), c([ic, c([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % Bb)
    bd = crect_bounds(w, A, ac, bc, rin, Aa, Bb, r)
    ra = c([ar, ntr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (Aa, a))
    lvr = {'( Re ` %s )' % r: bd['cl']['( Re ` %s )' % r], '( Re ` %s )' % Aa: bd['cl']['( Re ` %s )' % Aa]}
    if a == 'A':
        lvr['A'] = ar
    r0 = lin8(w, A, [bd['le'][0], ra, a0], '0 < ( Re ` %s )' % r, lvr)
    e = c([c.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (r, HP0, r, r))
    return c([c([bd['cc'], r0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (r, r)), e], 'mpbird', '%s e. %s' % (r, HP0))


def gen_zf():
    w = W('ef4zf', 'The zero set ` ZF ` of ` E = ( s - 1 ) L ( s , chi ) ` off ` 1 ` in a box with ` 0 < A <_ 1 ` is the zero set of ` L ` there, with the same orders ( ~ zc1eord ; ` 1 ` is not a zero of ` L ` by ~ ef4l1 ).')
    A0, G = ante_of(S['ef4zf'])
    c = Ctx(w, A0)
    chi = c.g(CHI); ar = c.g('A e. RR'); a0 = c.g('0 < A'); tr = c.g('T e. RR')
    l1 = c([chi, w.inst('ef4l1')], 'syl', '( %s ` 1 ) =/= 0' % LFN)
    BX = BOX('A', 'T')
    Ar = '( %s /\\ r e. %s )' % (A0, BX)
    cr = Ctx(w, Ar)
    rh = box_hp(w, Ar, 'r', cr([], 'simpr', 'r e. %s' % BX), lift(w, ar, Ar), lift(w, a0, Ar), lift(w, tr, Ar))
    EO = lambda P: tsub(stmt('zc1eord'), {'P': P})
    # (i)
    A3 = '( %s /\\ ( r =/= 1 /\\ ( %s ` r ) = 0 ) )' % (Ar, E)
    c3 = Ctx(w, A3)
    eo3a, eo3c = ante_of(EO('r'))
    eo3 = c3([c3([lift(w, chi, A3), c3([lift(w, rh, A3), c3([], 'simprl', 'r =/= 1')], 'jca', top_and(eo3a)[1])], 'jca', eo3a), w.inst('zc1eord')], 'syl', eo3c)
    bi3 = c3([eo3, w.inst('simpr')], 'syl', top_and(eo3c)[1])
    i1 = c3([c3([], 'simprr', '( %s ` r ) = 0' % E), bi3], 'mpbid', '( %s ` r ) = 0' % LFN)
    im1 = w.s([i1], 'ex', '( %s -> ( ( r =/= 1 /\\ ( %s ` r ) = 0 ) -> ( %s ` r ) = 0 ) )' % (Ar, E, LFN))
    # (ii)
    A4 = '( %s /\\ ( %s ` r ) = 0 )' % (Ar, LFN)
    c4 = Ctx(w, A4)
    lz = c4([], 'simpr', '( %s ` r ) = 0' % LFN)
    lne = c4([lz, c4([lift(w, l1, A4)], 'necomd', '0 =/= ( %s ` 1 )' % LFN)], 'eqnetrd', '( %s ` r ) =/= ( %s ` 1 )' % (LFN, LFN))
    rn1 = c4([lne, c4.a1(w.s([w.s([], 'fveq2', '( r = 1 -> ( %s ` r ) = ( %s ` 1 ) )' % (LFN, LFN))], 'necon3i', '( ( %s ` r ) =/= ( %s ` 1 ) -> r =/= 1 )' % (LFN, LFN)), '( ( %s ` r ) =/= ( %s ` 1 ) -> r =/= 1 )' % (LFN, LFN))], 'mpd', 'r =/= 1')
    eo4 = c4([c4([lift(w, chi, A4), c4([lift(w, rh, A4), rn1], 'jca', top_and(eo3a)[1])], 'jca', eo3a), w.inst('zc1eord')], 'syl', eo3c)
    bi4 = c4([eo4, w.inst('simpr')], 'syl', top_and(eo3c)[1])
    ez = c4([lz, bi4], 'mpbird', '( %s ` r ) = 0' % E)
    im2 = w.s([c4([rn1, ez], 'jca', '( r =/= 1 /\\ ( %s ` r ) = 0 )' % E)], 'ex', '( %s -> ( ( %s ` r ) = 0 -> ( r =/= 1 /\\ ( %s ` r ) = 0 ) ) )' % (Ar, LFN, E))
    bi = cr([im1, im2], 'impbid', '( ( r =/= 1 /\\ ( %s ` r ) = 0 ) <-> ( %s ` r ) = 0 )' % (E, LFN))
    zeq = c([bi], 'rabbidva', '%s = { r e. %s | ( %s ` r ) = 0 }' % (ZF(E, 'A', 'T'), BX, LFN))
    # orders
    ZFE_ = ZF(E, 'A', 'T')
    Aq = '( %s /\\ q e. %s )' % (A0, ZFE_)
    cq = Ctx(w, Aq)
    e1 = w.s([w.s([], 'neeq1', '( r = q -> ( r =/= 1 <-> q =/= 1 ) )'), w.s([w.s([], 'fveq2', '( r = q -> ( %s ` r ) = ( %s ` q ) )' % (E, E))], 'eqeq1d', '( r = q -> ( ( %s ` r ) = 0 <-> ( %s ` q ) = 0 ) )' % (E, E))], 'anbi12d',
             '( r = q -> ( ( r =/= 1 /\\ ( %s ` r ) = 0 ) <-> ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (E, E))
    qq = cq([cq([], 'simpr', 'q e. %s' % ZFE_), cq.a1(w.s([e1], 'elrab', '( q e. %s <-> ( q e. %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (ZFE_, BX, E)), '( q e. %s <-> ( q e. %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (ZFE_, BX, E))],
            'mpbid', '( q e. %s /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (BX, E))
    qb = cq([qq, w.inst('simpl')], 'syl', 'q e. %s' % BX)
    qn1 = cq([qq, w.inst('simprl')], 'syl', 'q =/= 1')
    qh = box_hp(w, Aq, 'q', qb, lift(w, ar, Aq), lift(w, a0, Aq), lift(w, tr, Aq))
    eqa, eqc = ante_of(EO('q'))
    eoq = cq([cq([lift(w, chi, Aq), cq([qh, qn1], 'jca', top_and(eqa)[1])], 'jca', eqa), w.inst('zc1eord')], 'syl', eqc)
    oq = cq([eoq, w.inst('simpl')], 'syl', top_and(eqc)[0])
    alq = c([oq], 'ralrimiva', 'A. q e. %s %s' % (ZFE_, top_and(eqc)[0]))
    w.qed([zeq, alq], 'jca', S['ef4zf'])
    return run8(w)


def fvself(c, k, K, body, kin):
    """( A -> ( ( k e. K |-> body ) ` k ) = body ) for kin : ( A -> k e. K )"""
    w = c.w
    MP = '( %s e. %s |-> %s )' % (k, K, body)
    st = w.s([], 'fvmpt2', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (k, K, body, MP, k, body))
    return c([kin, c([], 'ovexd', '%s e. _V' % body), st], 'syl2anc', '( %s ` %s ) = %s' % (MP, k, body))


def ab_cc(c, k, kn, af):
    """( A -> ABK(k) e. CC )"""
    w = c.w
    Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (c.A, k)
    ci = Ctx(w, Ai)
    ic = ci([lift(w, af, Ai), ci([ci([], 'simpr', 'i e. ( 1 ... %s )' % k), w.inst('elfznn')], 'syl', 'i e. NN')], 'ffvelcdmd', '( A ` i ) e. CC')
    sc = c([c([], 'fzfid', '( 1 ... %s ) e. Fin' % k), ic], 'fsumcl', '%s e. CC' % SI(k))
    kc = c([kn], 'nncnd', '%s e. CC' % k)
    k1c = c([c([kn], 'peano2nnd', '( %s + 1 ) e. NN' % k)], 'nncnd', '( %s + 1 ) e. CC' % k)
    m1 = c([c.a1(w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')], 'negcld', '-u 1 e. CC')
    d = c([c([kc, m1], 'cxpcld', '( %s ^c -u 1 ) e. CC' % k), c([k1c, m1], 'cxpcld', '( ( %s + 1 ) ^c -u 1 ) e. CC' % k)], 'subcld', '%s e. CC' % DIF(k))
    return c([sc, d], 'mulcld', '%s e. CC' % ABK(k))


def sj_cc(w, Ap, psf):
    Aj = '( %s /\\ j e. ( 1 ... p ) )' % Ap
    cj = Ctx(w, Aj)
    jn = cj([cj([], 'simpr', 'j e. ( 1 ... p )'), w.inst('elfznn')], 'syl', 'j e. NN')
    jc = cj([jn], 'nncnd', 'j e. CC')
    j1c = cj([cj([jn], 'peano2nnd', '( j + 1 ) e. NN')], 'nncnd', '( j + 1 ) e. CC')
    m1 = cj([cj.a1(w.s([], 'ax-1cn', '1 e. CC'), '1 e. CC')], 'negcld', '-u 1 e. CC')
    d = cj([cj([jc, m1], 'cxpcld', '( j ^c -u 1 ) e. CC'), cj([j1c, m1], 'cxpcld', '( ( j + 1 ) ^c -u 1 ) e. CC')], 'subcld', '%s e. CC' % DIF('j'))
    return cj([cj([lift(w, psf, Aj), jn], 'ffvelcdmd', '( %s ` j ) e. CC' % SQ_), d], 'mulcld', '( ( %s ` j ) x. %s ) e. CC' % (SQ_, DIF('j')))


GENS = {'ef4ab1': gen_ab1, 'ef4l1': gen_l1, 'ef4zf': gen_zf}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
