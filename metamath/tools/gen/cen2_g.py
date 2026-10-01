"""Sortie CEN2: census helpers (cen2bcf, cen2sq, cen2zb, cen2tail, cen2sub, cen2fam; Lean card_filter_le,
card_eq_totient, censusCount_le_sq, mem_zeroFinset, the sigma packaging 1515-1560)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure, lift
from c9lib import top_and
from lin import linarith, nlinarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def c_(w, ctx):
    return lambda hh, r, f: w.s(hh, r, '( %s -> %s )' % (ctx, f))


def gen_bcf():
    w = W('cen2bcf', 'The bad characters mod ` M ` form a finite set of at most ` M ` elements (Lean Census ` card_filter_le ` with ` card_eq_totient ` , ` Nat.totient_le ` ).')
    A0 = 'M e. NN'
    s = c_(w, A0)
    G = '( DChr ` M )'; DM = '( Base ` %s )' % G
    B = BC('S', 'V', 'M')
    eg = w.s([], 'eqid', '%s = %s' % (G, G)); ed = w.s([], 'eqid', '%s = %s' % (DM, DM))
    ss = w.s([], 'ssrab2', '%s C_ %s' % (B, DM))
    dfi = w.s([eg, ed], 'dchrfi', '( M e. NN -> %s e. Fin )' % DM)
    fin = s([dfi, s([ss], 'a1i', '%s C_ %s' % (B, DM)), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % B)
    hs = s([dfi, s([ss], 'a1i', '%s C_ %s' % (B, DM)), w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` %s )' % (B, DM))
    dh = w.s([eg, ed], 'dchrhash', '( M e. NN -> ( # ` %s ) = ( phi ` M ) )' % DM)
    h2 = s([hs, dh], 'breqtrd', '( # ` %s ) <_ ( phi ` M )' % B)
    pl = w.s([], 'z5phile', '( M e. NN -> ( phi ` M ) <_ M )')
    br = s([s([fin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % B)], 'nn0red', '( # ` %s ) e. RR' % B)
    pr = s([s([w.inst('phicl')], 'id', 'x') if False else s([w.s([], 'phicl', '( M e. NN -> ( phi ` M ) e. NN )')], 'id', '( M e. NN -> ( phi ` M ) e. NN )') if False else
            w.s([], 'phicl', '( M e. NN -> ( phi ` M ) e. NN )')], 'nnred', '( phi ` M ) e. RR')
    le = s([br, pr, s([], 'nnred', 'M e. RR') if False else w.s([w.s([], 'id', '( M e. NN -> M e. NN )')], 'nnred', '( M e. NN -> M e. RR )'), h2, pl], 'letrd', '( # ` %s ) <_ M' % B)
    w.qed([fin, le], 'jca', S['cen2bcf'])
    return run(w)


def gen_sq():
    w = W('cen2sq', 'The trivial regime: the census up to ` K ` is at most ` K ^ 2 ` (Lean Census ` censusCount_le_sq ` ).')
    A0 = 'K e. NN0'
    s = c_(w, A0)
    A1 = '( %s /\\ m e. ( 1 ... K ) )' % A0
    a = c_(w, A1)
    mn = a([a([], 'simpr', 'm e. ( 1 ... K )'), w.inst('elfznn')], 'syl', 'm e. NN')
    Bm = BC('S', 'V', 'm')
    bf = a([mn, w.inst('cen2bcf')], 'syl', '( %s e. Fin /\\ ( # ` %s ) <_ m )' % (Bm, Bm))
    br = a([a([a([bf], 'simpld', '%s e. Fin' % Bm), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % Bm)], 'nn0red', '( # ` %s ) e. RR' % Bm)
    kr = s([], 'nn0red', 'K e. RR') if False else w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0))], 'nn0red', '( %s -> K e. RR )' % A0)
    kr1 = lift(w, kr, A1)
    mk = a([a([], 'simpr', 'm e. ( 1 ... K )'), w.inst('elfzle2')], 'syl', 'm <_ K')
    le = a([br, a([mn], 'nnred', 'm e. RR'), kr1, a([bf], 'simprd', '( # ` %s ) <_ m' % Bm), mk], 'letrd', '( # ` %s ) <_ K' % Bm)
    fz = s([], 'fzfid', '( 1 ... K ) e. Fin')
    sl = s([fz, br, kr1, le], 'fsumle', '%s <_ sum_ m e. ( 1 ... K ) K' % CNT('S', 'V', 'K'))
    fc = s([fz, s([kr], 'recnd', 'K e. CC'), w.inst('fsumconst')], 'syl2anc', 'sum_ m e. ( 1 ... K ) K = ( ( # ` ( 1 ... K ) ) x. K )')
    hf = w.s([], 'hashfz1', '( K e. NN0 -> ( # ` ( 1 ... K ) ) = K )')
    fc2 = s([fc, s([hf], 'oveq1d', '( ( # ` ( 1 ... K ) ) x. K ) = ( K x. K )')], 'eqtrd', 'sum_ m e. ( 1 ... K ) K = ( K x. K )')
    w.qed([sl, fc2], 'breqtrd', S['cen2sq'])
    return run(w)


def gen_zb():
    w = W('cen2zb', 'A point of the box ` [ S , 1 ] x [ -V , V ] ` (as a ` crect ` ) has real part in ` [ S , 1 ] ` and imaginary part of absolute value at most ` V ` (Lean ` mem_zeroFinset ` ).')
    A0, C0 = split_imp(S['cen2zb'])
    s = c_(w, A0)
    sr = s([], 'simpll', 'S e. RR'); vr = s([], 'simplr', 'V e. RR'); ob = s([], 'simpr', 'O e. %s' % BOX('S', 'V'))
    ic = s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC')
    c = Closure(w, A0, {'S': ('RR', sr), 'V': ('RR', vr), '_i': ('CC', ic)})
    P = '( S + ( _i x. -u V ) )'; Q = '( 1 + ( _i x. V ) )'
    EC = tokrep(stmt('elcrect'), {'A': P, 'B': Q, 'Z': 'O'})
    ea, ecn = split_imp(EC)
    ec = s([c.mem(P, 'CC'), c.mem(Q, 'CC'), w.inst('elcrect')], 'syl2anc', ecn)
    rhs = ecn.split(' <-> ', 1)[1][:]
    rhs = ecn[len('( O e. ( %s crect %s ) <-> ' % (P, Q)):-2]
    m = s([ob, ec], 'mpbid', rhs)
    oc_, re_, im_ = top_and(rhs)
    oc = s([m], 'simp1d', oc_); rei = s([m], 'simp2d', re_); imi = s([m], 'simp3d', im_)
    nv = c.mem('-u V', 'RR')
    rp = s([sr, nv], 'crred', '( Re ` %s ) = S' % P); rq = s([s([], '1red', '1 e. RR'), vr], 'crred', '( Re ` %s ) = 1' % Q)
    ip = s([sr, nv], 'crimd', '( Im ` %s ) = -u V' % P); iq = s([s([], '1red', '1 e. RR'), vr], 'crimd', '( Im ` %s ) = V' % Q)
    rei2 = s([rei, s([rp, rq], 'oveq12d', '( ( Re ` %s ) [,] ( Re ` %s ) ) = ( S [,] 1 )' % (P, Q))], 'eleqtrd', '( Re ` O ) e. ( S [,] 1 )')
    imi2 = s([imi, s([ip, iq], 'oveq12d', '( ( Im ` %s ) [,] ( Im ` %s ) ) = ( -u V [,] V )' % (P, Q))], 'eleqtrd', '( Im ` O ) e. ( -u V [,] V )')
    e1 = s([sr, s([], '1red', '1 e. RR'), w.inst('elicc2')], 'syl2anc', '( ( Re ` O ) e. ( S [,] 1 ) <-> ( ( Re ` O ) e. RR /\\ S <_ ( Re ` O ) /\\ ( Re ` O ) <_ 1 ) )')
    r3 = s([rei2, e1], 'mpbid', '( ( Re ` O ) e. RR /\\ S <_ ( Re ` O ) /\\ ( Re ` O ) <_ 1 )')
    e2 = s([nv, vr, w.inst('elicc2')], 'syl2anc', '( ( Im ` O ) e. ( -u V [,] V ) <-> ( ( Im ` O ) e. RR /\\ -u V <_ ( Im ` O ) /\\ ( Im ` O ) <_ V ) )')
    i3 = s([imi2, e2], 'mpbid', '( ( Im ` O ) e. RR /\\ -u V <_ ( Im ` O ) /\\ ( Im ` O ) <_ V )')
    ab = s([s([i3], 'simp1d', '( Im ` O ) e. RR'), vr], 'absled', '( ( abs ` ( Im ` O ) ) <_ V <-> ( -u V <_ ( Im ` O ) /\\ ( Im ` O ) <_ V ) )')
    abv = s([s([s([i3], 'simp2d', '-u V <_ ( Im ` O )'), s([i3], 'simp3d', '( Im ` O ) <_ V')], 'jca', '( -u V <_ ( Im ` O ) /\\ ( Im ` O ) <_ V )'), ab], 'mpbird',
            '( abs ` ( Im ` O ) ) <_ V')
    w.qed([oc, s([s([r3], 'simp2d', 'S <_ ( Re ` O )'), s([r3], 'simp3d', '( Re ` O ) <_ 1')], 'jca', '( S <_ ( Re ` O ) /\\ ( Re ` O ) <_ 1 )'), abv], '3jca', S['cen2zb'])
    return run(w)


def gen_tail():
    w = W('cen2tail', 'The bad characters of the moduli ` 2 ... K ` are pairwise distinct across moduli (a character determines its level), so their union is finite with size the sum of the counts (Lean Census 1515-1530, the sigma type).')
    A0 = 'K e. ZZ'
    s = c_(w, A0)
    A1 = '( %s /\\ m e. ( 2 ... K ) )' % A0
    a = c_(w, A1)
    mn = a([a([a([], 'simpr', 'm e. ( 2 ... K )'), w.inst('elfzuz')], 'syl', 'm e. ( ZZ>= ` 2 )'), w.inst('eluz2nn')], 'syl', 'm e. NN')
    Bm = BC('S', 'V', 'm')
    bfin = a([a([mn, w.inst('cen2bcf')], 'syl', '( %s e. Fin /\\ ( # ` %s ) <_ m )' % (Bm, Bm))], 'simpld', '%s e. Fin' % Bm)
    A2 = '( %s /\\ z e. %s )' % (A1, Bm)
    b = c_(w, A2)
    G = '( DChr ` m )'; DM = '( Base ` %s )' % G; ZM = '( Z/nZ ` m )'; BM = '( Base ` %s )' % ZM
    zd = b([b([], 'simpr', 'z e. %s' % Bm), w.inst('elrabi')], 'syl', 'z e. %s' % DM)
    zf = b([w.s([], 'eqid', '%s = %s' % (G, G)), w.s([], 'eqid', '%s = %s' % (ZM, ZM)), w.s([], 'eqid', '%s = %s' % (DM, DM)), w.s([], 'eqid', '%s = %s' % (BM, BM)), zd],
           'dchrf', 'z : %s --> CC' % BM)
    dm = b([zf, w.inst('fdm')], 'syl', 'dom z = %s' % BM)
    zh = w.s([w.s([], 'eqid', '%s = %s' % (ZM, ZM)), w.s([], 'eqid', '%s = %s' % (BM, BM))], 'znhash', '( m e. NN -> ( # ` %s ) = m )' % BM)
    hz = b([b([dm], 'fveq2d', '( # ` dom z ) = ( # ` %s )' % BM), b([lift(w, mn, A2), zh], 'syl', '( # ` %s ) = m' % BM)], 'eqtrd', '( # ` dom z ) = m')
    r1 = a([hz], 'ralrimiva', 'A. z e. %s ( # ` dom z ) = m' % Bm)
    r2 = s([r1], 'ralrimiva', 'A. m e. ( 2 ... K ) A. z e. %s ( # ` dom z ) = m' % Bm)
    UNK = UN('K')
    dj = s([r2, w.inst('invdisj')], 'syl', 'Disj_ m e. ( 2 ... K ) %s' % Bm)
    fz = s([], 'fzfid', '( 2 ... K ) e. Fin')
    ufi = s([fz, s([bfin], 'ralrimiva', 'A. m e. ( 2 ... K ) %s e. Fin' % Bm), w.inst('iunfi')], 'syl2anc', '%s e. Fin' % UNK)
    hi = s([fz, bfin, dj], 'hashiun', '( # ` %s ) = sum_ m e. ( 2 ... K ) ( # ` %s )' % (UNK, Bm))
    w.qed([ufi, hi], 'jca', S['cen2tail'])
    return run(w)


def gen_sub():
    w = W('cen2sub', 'A finite set has a subset of every size up to its own (Lean ` Finset.exists_subset_card_eq ` ; the image of ` 1 ... N ` under ~ fz1f1o ).')
    A0, C0 = split_imp(S['cen2sub'])
    s = c_(w, A0)
    af = s([], 'simp1', 'A e. Fin'); n0 = s([], 'simp2', 'N e. NN0'); nle = s([], 'simp3', 'N <_ ( # ` A )')
    PS = lambda X: '( %s C_ A /\\ ( # ` %s ) = N )' % (X, X)
    ES = 'E. s %s' % PS('s')
    def intro(ctx, X, xv, pst):
        """( ctx -> E. s PS(s) ) from ( ctx -> PS(X) ) and ( ctx -> X e. _V )"""
        e = w.s([w.s([], 'sseq1', '( s = %s -> ( s C_ A <-> %s C_ A ) )' % (X, X)),
                 w.s([w.s([], 'fveq2', '( s = %s -> ( # ` s ) = ( # ` %s ) )' % (X, X))], 'eqeq1d', '( s = %s -> ( ( # ` s ) = N <-> ( # ` %s ) = N ) )' % (X, X))],
                'anbi12d', '( s = %s -> ( %s <-> %s ) )' % (X, PS('s'), PS(X)))
        sp = w.s([e], 'spcegv', '( %s e. _V -> ( %s -> %s ) )' % (X, PS(X), ES))
        return w.s([xv, pst, sp], 'sylc', '( %s -> %s )' % (ctx, ES))
    # A empty
    C1 = '( %s /\\ A = (/) )' % A0
    a = c_(w, C1)
    ha = a([a([a([], 'simpr', 'A = (/)')], 'fveq2d', '( # ` A ) = ( # ` (/) )'), a([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( # ` (/) ) = 0')], 'eqtrd', '( # ` A ) = 0')
    nz = a([a([lift(w, nle, C1), ha], 'breqtrd', 'N <_ 0'), a([lift(w, n0, C1), w.inst('nn0le0eq0')], 'syl', '( N <_ 0 <-> N = 0 )')], 'mpbid', 'N = 0')
    h0 = a([a([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( # ` (/) ) = 0'), nz], 'eqtr4d', '( # ` (/) ) = N')
    p1 = a([a([w.s([], '0ss', '(/) C_ A')], 'a1i', '(/) C_ A'), h0], 'jca', PS('(/)'))
    e1 = intro(C1, '(/)', a([w.s([], '0ex', '(/) e. _V')], 'a1i', '(/) e. _V'), p1)
    k1 = w.s([e1], 'ex', '( %s -> ( A = (/) -> %s ) )' % (A0, ES))
    # a bijection f
    FF = 'f : ( 1 ... ( # ` A ) ) -1-1-onto-> A'
    C2 = '( %s /\\ %s )' % (A0, FF)
    b = c_(w, C2)
    ff = b([], 'simpr', FF)
    X = '( f " ( 1 ... N ) )'
    rn = b([b([ff, w.inst('f1ofo')], 'syl', 'f : ( 1 ... ( # ` A ) ) -onto-> A'), w.inst('forn')], 'syl', 'ran f = A')
    xs = b([b([w.s([], 'imassrn', '%s C_ ran f' % X)], 'a1i', '%s C_ ran f' % X), rn], 'sseqtrd', '%s C_ A' % X)
    nz2 = b([lift(w, n0, C2)], 'nn0zd', 'N e. ZZ')
    hz = b([b([lift(w, af, C2), w.inst('hashcl')], 'syl', '( # ` A ) e. NN0')], 'nn0zd', '( # ` A ) e. ZZ')
    uz = b([b([nz2, hz, lift(w, nle, C2)], '3jca', '( N e. ZZ /\\ ( # ` A ) e. ZZ /\\ N <_ ( # ` A ) )'), w.s([], 'eluz2', '( ( # ` A ) e. ( ZZ>= ` N ) <-> ( N e. ZZ /\\ ( # ` A ) e. ZZ /\\ N <_ ( # ` A ) ) )')],
           'sylibr', '( # ` A ) e. ( ZZ>= ` N )')
    ss = b([uz, w.inst('fzss2')], 'syl', '( 1 ... N ) C_ ( 1 ... ( # ` A ) )')
    f11 = b([ff, w.inst('f1of1')], 'syl', 'f : ( 1 ... ( # ` A ) ) -1-1-> A')
    RS = '( f |` ( 1 ... N ) )'
    fr = b([f11, ss, w.inst('f1ores')], 'syl2anc', '%s : ( 1 ... N ) -1-1-onto-> %s' % (RS, X))
    HH = 'h : ( 1 ... N ) -1-1-onto-> %s' % X
    eh = w.s([w.s([], 'f1oeq1', '( h = %s -> ( %s <-> %s : ( 1 ... N ) -1-1-onto-> %s ) )' % (RS, HH, RS, X))], 'id', 'x') if False else \
        w.s([], 'f1oeq1', '( h = %s -> ( %s <-> %s : ( 1 ... N ) -1-1-onto-> %s ) )' % (RS, HH, RS, X))
    sp = w.s([eh], 'spcegv', '( %s e. _V -> ( %s : ( 1 ... N ) -1-1-onto-> %s -> E. h %s ) )' % (RS, RS, X, HH))
    rv = b([w.s([w.s([], 'vex', 'f e. _V'), w.inst('resexg')], 'ax-mp', '%s e. _V' % RS)], 'a1i', '%s e. _V' % RS)
    ex = b([rv, fr, sp], 'sylc', 'E. h %s' % HH)
    hq = w.s([w.s([], 'ovex', '( 1 ... N ) e. _V'), w.inst('hasheqf1oi')], 'ax-mp', '( E. h %s -> ( # ` ( 1 ... N ) ) = ( # ` %s ) )' % (HH, X))
    hi = b([b([ex, hq], 'syl', '( # ` ( 1 ... N ) ) = ( # ` %s )' % X)], 'eqcomd', '( # ` %s ) = ( # ` ( 1 ... N ) )' % X)
    hn = b([hi, b([lift(w, n0, C2), w.inst('hashfz1')], 'syl', '( # ` ( 1 ... N ) ) = N')], 'eqtrd', '( # ` %s ) = N' % X)
    xv = b([w.s([w.s([], 'vex', 'f e. _V'), w.inst('imaexg')], 'ax-mp', '%s e. _V' % X)], 'a1i', '%s e. _V' % X)
    e2 = intro(C2, X, xv, b([xs, hn], 'jca', PS(X)))
    k2 = w.s([w.s([e2], 'ex', '( %s -> ( %s -> %s ) )' % (A0, FF, ES))], 'exlimdv', '( %s -> ( E. f %s -> %s ) )' % (A0, FF, ES))
    k3 = w.s([k2], 'adantld', '( %s -> ( ( ( # ` A ) e. NN /\\ E. f %s ) -> %s ) )' % (A0, FF, ES))
    fz = s([af, w.inst('fz1f1o')], 'syl', '( A = (/) \\/ ( ( # ` A ) e. NN /\\ E. f %s ) )' % FF)
    w.qed([fz, w.s([k1, k3], 'jaod', '( %s -> ( ( A = (/) \\/ ( ( # ` A ) e. NN /\\ E. f %s ) ) -> %s ) )' % (A0, FF, ES))], 'mpd', S['cen2sub'])
    return run(w)


def gen_fam():
    w = W('cen2fam', 'A bad character ` X ` mod ` N e. ( 2 ... K ) ` , ` K <_ Z ` , with a zero ` R ` in its zero set, meets the family condition of ~ cen2n13 at width ` D >_ 1 - S ` (Lean Census 1540-1600: ` hMf2 ` , ` hMfZ ` , ` hbad ` , ` hrho_prop ` ).')
    A0, C0 = split_imp(S['cen2fam'])
    s = c_(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    nk = g('N e. ( 2 ... K )'); kz = g('K <_ Z'); sr = g('S e. RR'); vr = g('V e. RR'); zr = g('Z e. RR'); sd = g('( 1 - S ) <_ D')
    B = BC('S', 'V', 'N'); ZB = ZFB('S', 'V', 'N', 'X')
    xb = g('X e. %s' % B); rz = g('R e. %s' % ZB)
    nn = s([s([nk, w.inst('elfzuz')], 'syl', 'N e. ( ZZ>= ` 2 )'), w.inst('eluz2nn')], 'syl', 'N e. NN')
    n2 = s([nk, w.inst('elfzle1')], 'syl', '2 <_ N')
    nkl = s([nk, w.inst('elfzle2')], 'syl', 'N <_ K')
    kr = s([s([nk, w.inst('elfzel2')], 'syl', 'K e. ZZ')], 'zred', 'K e. RR')
    nz_ = s([s([nn], 'nnred', 'N e. RR'), kr, zr, nkl, kz], 'letrd', 'N <_ Z')
    DN = '( Base ` ( DChr ` N ) )'
    PHY = lambda y: '( ( N DChrCond %s ) = N /\\ %s =/= (/) )' % (y, ZFB('S', 'V', 'N', y))
    eq = 'y = X'
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, px = w.wcongr(PHY('y'), {'y': 'X'}, eq, {'y': idx})
    assert px == PHY('X'), px
    er = w.s([st], 'elrab', '( X e. %s <-> ( X e. %s /\\ %s ) )' % (B, DN, PHY('X')))
    xm = s([xb, s([er], 'a1i', '( X e. %s <-> ( X e. %s /\\ %s ) )' % (B, DN, PHY('X')))], 'mpbid', '( X e. %s /\\ %s )' % (DN, PHY('X')))
    xd = s([xm], 'simpld', 'X e. %s' % DN)
    xc = s([s([xm], 'simprd', PHY('X'))], 'simpld', '( N DChrCond X ) = N')
    PHO = lambda o: '( %s =/= 1 /\\ ( ( N DChrLF X ) ` %s ) = 0 )' % (o, o)
    eq2 = 'o = R'
    idx2 = w.s([], 'id', '( %s -> %s )' % (eq2, eq2))
    st2, po = w.wcongr(PHO('o'), {'o': 'R'}, eq2, {'o': idx2})
    er2 = w.s([st2], 'elrab', '( R e. %s <-> ( R e. %s /\\ %s ) )' % (ZB, BOX('S', 'V'), PHO('R')))
    rm = s([rz, s([er2], 'a1i', '( R e. %s <-> ( R e. %s /\\ %s ) )' % (ZB, BOX('S', 'V'), PHO('R')))], 'mpbid', '( R e. %s /\\ %s )' % (BOX('S', 'V'), PHO('R')))
    ZBS = tokrep(S['cen2zb'], {'O': 'R'})
    za, zc = split_imp(ZBS)
    zb = s([s([s([sr, vr], 'jca', '( S e. RR /\\ V e. RR )'), s([rm], 'simpld', 'R e. %s' % BOX('S', 'V'))], 'jca', za), w.inst('cen2zb')], 'syl', zc)
    Z = split_all(w, A0, zc, zb)
    dr = g('D e. RR')
    c = Closure(w, A0, {'S': ('RR', sr), 'D': ('RR', dr)})
    rc = Z['R e. CC']
    c.have('( Re ` R )', 'RR', s([rc], 'recld', '( Re ` R ) e. RR'))
    lo = linarith(w, A0, [sd, Z['S <_ ( Re ` R )']], '( 1 - D ) <_ ( Re ` R )', closure=c)
    BODYT = BODY('N', 'X', 'R')
    p1 = s([s([nn, n2, nz_], '3jca', '( N e. NN /\\ 2 <_ N /\\ N <_ Z )'), s([xd, xc], 'jca', '( X e. %s /\\ ( N DChrCond X ) = N )' % DN)], 'jca', top_and(BODYT)[0])
    r1 = s([s([rm], 'simprd', PHO('R'))], 'simpld', 'R =/= 1'); r0 = s([s([rm], 'simprd', PHO('R'))], 'simprd', '( ( N DChrLF X ) ` R ) = 0')
    q2 = top_and(BODYT)[1]
    p2 = s([s([rc, r1, r0], '3jca', top_and(q2)[0]), s([lo, Z['( Re ` R ) <_ 1'], Z['( abs ` ( Im ` R ) ) <_ V']], '3jca', top_and(q2)[1])], 'jca', q2)
    w.qed([p1, p2], 'jca', S['cen2fam'])
    return run(w)


if __name__ == '__main__':
    gen_bcf()
    gen_sq()
    gen_zb()
    gen_tail()
    gen_sub()
    gen_fam()
