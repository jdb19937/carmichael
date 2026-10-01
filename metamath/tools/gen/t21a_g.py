"""Sortie T21a: the partial-summation lemma (L-gamma): t21lgr (pointwise), t21lg (abstract), t21lgs (Lgamma_sum)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_
import num, lin
import cl as _cl
lin.FASTPATH = True
from tm import W

CN = '( 1 / ( n x. ( n + 1 ) ) )'


def gen_lgr():
    w = W('t21lgr', 'The pointwise (L-gamma) inequality: for ` 0 <_ G <_ T ` , ` 1 <_ T ` , ` 1 / ( 1 + G ) <_ 1 / T + sum_ ( 1 <_ n <_ floor T ) [ G <_ n ] / ( n ( n + 1 ) ) ` : the terms ` n >_ floor G + 1 ` telescope to ` 1 / ( floor G + 1 ) - 1 / ( floor T + 1 ) ` (Lean ` one_div_telescope ` and the bucket step of ` Lgamma_char ` ).')
    A0 = ante_of(S['t21lgr'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    tr, t1, gr, g0, gt = u['T e. RR'], u['1 <_ T'], u['G e. RR'], u['0 <_ G'], u['G <_ T']
    one_z = lambda A_: w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % A_)
    FT, FG = '( |_ ` T )', '( |_ ` G )'
    AA = '( %s + 1 )' % FG; M1 = '( %s + 1 )' % FT
    fgn = ap_(w, A0, [gr, g0], 'flge0nn0', '%s e. NN0' % FG)
    ann = ap_(w, A0, [fgn], 'nn0p1nn', '%s e. NN' % AA)
    ftz = st([tr], 'flcld', '%s e. ZZ' % FT); fgz = st([fgn], 'nn0zd', '%s e. ZZ' % FG)
    ftr = st([ftz], 'zred', '%s e. RR' % FT); fgr = st([fgz], 'zred', '%s e. RR' % FG)
    ar = st([ann], 'nnred', '%s e. RR' % AA); az = st([ann], 'nnzd', '%s e. ZZ' % AA)
    fw = ap_(w, A0, [gr, tr, gt], 'flwordi', '%s <_ %s' % (FG, FT))
    fgl = ap_(w, A0, [gr], 'flle', '%s <_ G' % FG)
    gl = ap_(w, A0, [gr], 'flltp1', 'G < %s' % AA)
    tl = ap_(w, A0, [tr], 'flltp1', 'T < %s' % M1)
    m1z = st([ftz], 'peano2zd', '%s e. ZZ' % M1)
    m1r = st([m1z], 'zred', '%s e. RR' % M1)
    c = _cl.Closure(w, A0, {})
    for k_, s_ in [('T', tr), ('G', gr), (FT, ftr), (FG, fgr)]:
        c.leaf(k_, 'RR', s_)
    # uz facts
    aM = lin.linarith(w, A0, [fw], '%s <_ %s' % (AA, M1), closure=c)
    uz1 = w.s([st([az, m1z, aM], '3jca', '( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s )' % (AA, M1, AA, M1)),
               w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (M1, AA, AA, M1, AA, M1))], 'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (A0, M1, AA))
    a1 = st([ann], 'nnge1d', '1 <_ %s' % AA)
    uz2 = w.s([st([one_z(A0), az, a1], '3jca', '( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s )' % (AA, AA)),
               w.s([], 'eluz2', '( %s e. ( ZZ>= ` 1 ) <-> ( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s ) )' % (AA, AA, AA))], 'sylibr', '( %s -> %s e. ( ZZ>= ` 1 ) )' % (A0, AA))
    sub = ap_(w, A0, [uz2], 'fzss1', '( %s ... %s ) C_ ( 1 ... %s )' % (AA, FT, FT))
    # telescoping
    Ak = lambda k_: '( 1 / %s )' % k_
    A1 = '( %s /\\ k e. ( %s ... %s ) )' % (A0, AA, M1)
    kin = w.s([], 'simpr', '( %s -> k e. ( %s ... %s ) )' % (A1, AA, M1))
    kz = ap_(w, A1, [kin], 'elfzelz', 'k e. ZZ')
    kr = w.s([kz], 'zred', '( %s -> k e. RR )' % A1)
    kle = ap_(w, A1, [kin], 'elfzle1', '%s <_ k' % AA)
    kp = lin.linarith(w, A1, [kle, _cl.lift(w, a1, A1)], '0 < k', leaves={'k': kr, FG: _cl.lift(w, fgr, A1)})
    kc = w.s([w.s([kr, w.s([kp], 'gt0ne0d', '( %s -> k =/= 0 )' % A1)], 'rereccld', '( %s -> ( 1 / k ) e. RR )' % A1)], 'recnd', '( %s -> ( 1 / k ) e. CC )' % A1)
    TS = 'sum_ n e. ( %s ... %s ) ( ( 1 / n ) - ( 1 / ( n + 1 ) ) )' % (AA, FT)
    tel = st([w.s([], 'oveq2', '( k = n -> ( 1 / k ) = ( 1 / n ) )'), w.s([], 'oveq2', '( k = ( n + 1 ) -> ( 1 / k ) = ( 1 / ( n + 1 ) ) )'),
              w.s([], 'oveq2', '( k = %s -> ( 1 / k ) = ( 1 / %s ) )' % (AA, AA)), w.s([], 'oveq2', '( k = %s -> ( 1 / k ) = ( 1 / %s ) )' % (M1, M1)),
              ftz, uz1, kc], 'telfsum', '%s = ( ( 1 / %s ) - ( 1 / %s ) )' % (TS, AA, M1))
    # the if-terms on ( AA ... FT )
    A2 = '( %s /\\ n e. ( %s ... %s ) )' % (A0, AA, FT)
    nin = w.s([], 'simpr', '( %s -> n e. ( %s ... %s ) )' % (A2, AA, FT))
    nz = ap_(w, A2, [nin], 'elfzelz', 'n e. ZZ'); nr = w.s([nz], 'zred', '( %s -> n e. RR )' % A2)
    nle = ap_(w, A2, [nin], 'elfzle1', '%s <_ n' % AA)
    L2 = lambda s_: _cl.lift(w, s_, A2)
    gn = lin.linarith(w, A2, [L2(gl), nle], 'G <_ n', leaves={'n': nr, 'G': L2(gr), FG: L2(fgr)})
    npos = lin.linarith(w, A2, [nle, L2(a1)], '0 < n', leaves={'n': nr, FG: L2(fgr)})
    nc = w.s([nr], 'recnd', '( %s -> n e. CC )' % A2); nn0 = w.s([npos], 'gt0ne0d', '( %s -> n =/= 0 )' % A2)
    n1r = ap_(w, A2, [nr], 'peano2re', '( n + 1 ) e. RR')
    n1p = lin.linarith(w, A2, [npos], '0 < ( n + 1 )', leaves={'n': nr})
    n1c = w.s([n1r], 'recnd', '( %s -> ( n + 1 ) e. CC )' % A2); n1n = w.s([n1p], 'gt0ne0d', '( %s -> ( n + 1 ) =/= 0 )' % A2)
    sr = w.s([nc, nn0, n1c, n1n], 'subrecd', '( %s -> ( ( 1 / n ) - ( 1 / ( n + 1 ) ) ) = ( ( ( n + 1 ) - n ) / ( n x. ( n + 1 ) ) ) )' % A2)
    p2 = w.s([nc, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A2)], 'pncan2d', '( %s -> ( ( n + 1 ) - n ) = 1 )' % A2)
    sr2 = w.s([sr, w.s([p2], 'oveq1d', '( %s -> ( ( ( n + 1 ) - n ) / ( n x. ( n + 1 ) ) ) = ( 1 / ( n x. ( n + 1 ) ) ) )' % A2)], 'eqtrd', '( %s -> ( ( 1 / n ) - ( 1 / ( n + 1 ) ) ) = %s )' % (A2, CN))
    IFN = 'if ( G <_ n , %s , 0 )' % CN
    it = w.s([gn], 'iftrued', '( %s -> %s = %s )' % (A2, IFN, CN))
    te = w.s([it, sr2], 'eqtr4d', '( %s -> %s = ( ( 1 / n ) - ( 1 / ( n + 1 ) ) ) )' % (A2, IFN))
    SA = 'sum_ n e. ( %s ... %s ) %s' % (AA, FT, IFN)
    SF = 'sum_ n e. ( 1 ... %s ) %s' % (FT, IFN)
    sa = st([te], 'sumeq2dv', '%s = %s' % (SA, TS))
    # nonneg if-terms on ( 1 ... FT )
    A3 = '( %s /\\ n e. ( 1 ... %s ) )' % (A0, FT)
    n3 = ap_(w, A3, [w.s([], 'simpr', '( %s -> n e. ( 1 ... %s ) )' % (A3, FT))], 'elfznn', 'n e. NN')
    cnp = w.s([w.s([n3, w.s([n3], 'peano2nnd', '( %s -> ( n + 1 ) e. NN )' % A3)], 'nnmulcld', '( %s -> ( n x. ( n + 1 ) ) e. NN )' % A3)], 'nnrpd', '( %s -> ( n x. ( n + 1 ) ) e. RR+ )' % A3)
    cr = w.s([cnp], 'rpreccld', '( %s -> %s e. RR+ )' % (A3, CN))
    ir, i0 = ifnn(w, A3, 'G <_ n', CN, w.s([cr], 'rpred', '( %s -> %s e. RR )' % (A3, CN)), w.s([cr], 'rpge0d', '( %s -> 0 <_ %s )' % (A3, CN)))
    fin1 = st([], 'fzfid', '( 1 ... %s ) e. Fin' % FT)
    less = st([fin1, ir, i0, sub], 'fsumless', '%s <_ %s' % (SA, SF))
    sfr = st([fin1, ir], 'fsumrecl', '%s e. RR' % SF)
    # reciprocal bounds
    g1p = st([st([st([], '1red', '1 e. RR') if False else w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0), gr], 'readdcld', '( 1 + G ) e. RR'),
              lin.linarith(w, A0, [g0], '0 < ( 1 + G )', closure=c)], 'elrpd', '( 1 + G ) e. RR+')
    arp = st([ann], 'nnrpd', '%s e. RR+' % AA)
    aG = lin.linarith(w, A0, [fgl], '%s <_ ( 1 + G )' % AA, closure=c)
    r1 = st([aG, st([arp, g1p], 'lerecd', '( %s <_ ( 1 + G ) <-> ( 1 / ( 1 + G ) ) <_ ( 1 / %s ) )' % (AA, AA))], 'mpbid', '( 1 / ( 1 + G ) ) <_ ( 1 / %s )' % AA)
    tp = st([tr, lin.linarith(w, A0, [t1], '0 < T', closure=c)], 'elrpd', 'T e. RR+')
    m1p = st([m1r, lin.linarith(w, A0, [t1, tl], '0 < %s' % M1, closure=c)], 'elrpd', '%s e. RR+' % M1)
    tm1 = lin.linarith(w, A0, [tl], 'T <_ %s' % M1, closure=c)
    r2 = st([tm1, st([tp, m1p], 'lerecd', '( T <_ %s <-> ( 1 / %s ) <_ ( 1 / T ) )' % (M1, M1))], 'mpbid', '( 1 / %s ) <_ ( 1 / T )' % M1)
    for E_, s_ in [('( 1 / ( 1 + G ) )', st([g1p], 'rpreccld', '( 1 / ( 1 + G ) ) e. RR+')), ('( 1 / %s )' % AA, st([arp], 'rpreccld', '( 1 / %s ) e. RR+' % AA)),
                   ('( 1 / T )', st([tp], 'rpreccld', '( 1 / T ) e. RR+')), ('( 1 / %s )' % M1, st([m1p], 'rpreccld', '( 1 / %s ) e. RR+' % M1))]:
        c.leaf(E_, 'RR', st([s_], 'rpred', '%s e. RR' % E_))
    n2 = w.s([w.s([nz, npos], 'jca', '( %s -> ( n e. ZZ /\\ 0 < n ) )' % A2), w.s([], 'elnnz', '( n e. NN <-> ( n e. ZZ /\\ 0 < n ) )')], 'sylibr', '( %s -> n e. NN )' % A2)
    cnp2 = w.s([w.s([n2, w.s([n2], 'peano2nnd', '( %s -> ( n + 1 ) e. NN )' % A2)], 'nnmulcld', '( %s -> ( n x. ( n + 1 ) ) e. NN )' % A2)], 'nnrpd', '( %s -> ( n x. ( n + 1 ) ) e. RR+ )' % A2)
    cr2 = w.s([cnp2], 'rpreccld', '( %s -> %s e. RR+ )' % (A2, CN))
    ir2, _ = ifnn(w, A2, 'G <_ n', CN, w.s([cr2], 'rpred', '( %s -> %s e. RR )' % (A2, CN)), w.s([cr2], 'rpge0d', '( %s -> 0 <_ %s )' % (A2, CN)))
    c.leaf(SA, 'RR', st([st([], 'fzfid', '( %s ... %s ) e. Fin' % (AA, FT)), ir2], 'fsumrecl', '%s e. RR' % SA))
    c.leaf(SF, 'RR', sfr)
    dr_ = st([c.mem('( 1 / %s )' % AA, 'RR'), c.mem('( 1 / %s )' % M1, 'RR')], 'resubcld', '( ( 1 / %s ) - ( 1 / %s ) ) e. RR' % (AA, M1))
    c.leaf(TS, 'RR', st([tel, dr_], 'eqeltrd', '%s e. RR' % TS))
    fin = lin.linarith(w, A0, [less, sa, tel, r1, r2], '( 1 / ( 1 + G ) ) <_ ( ( 1 / T ) + %s )' % SF, closure=c, atoms=[TS])
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21lgr']))
    return run(w)

def gen_lg():
    w = W('t21lg', '(L-gamma), abstract: for finite families ` S ( x ) ` of points with weights ` W >_ 0 ` and ` abs Im q <_ T ` , and sets ` Z ( x , n ) C_ S ` containing every point of height at most ` n ` , ` sum sum W / ( 1 + abs Im q ) <_ ( sum sum W ) / T + sum_ ( 1 <_ n <_ floor T ) ( sum sum_ Z W ) / ( n ( n + 1 ) ) ` (Lean ` Lgamma_char ` , ` Lgamma_sum ` ; ~ t21lgr , ~ sumss2 , ~ fsumcom ).')
    for k in sorted(LGH):
        w.lines.append('h%d::t21lg.%d |- %s' % (k, k, LGH[k]))
    G = '( abs ` ( Im ` q ) )'; D = '( n x. ( n + 1 ) )'
    IFA = 'if ( %s <_ n , %s , 0 )' % (G, CN)
    WD = '( W / %s )' % D
    IFZ = 'if ( q e. Z , %s , 0 )' % WD
    C0 = 'ph'; C1 = '( ph /\\ x e. I )'; C2 = '( %s /\\ q e. S )' % C1; C3 = '( %s /\\ n e. %s )' % (C2, FLT); C1n = '( %s /\\ n e. %s )' % (C1, FLT)
    s = lambda A_, h, r, f: w.s(h, r, '( %s -> %s )' % (A_, f))
    L = lambda st_, A_: _cl.lift(w, st_, A_)
    # context ph
    h1a = s(C0, ['1'], 'simpld', 'T e. RR'); h1b = s(C0, ['1'], 'simprd', '1 <_ T')
    tp = s(C0, [h1a, lin.linarith(w, C0, [h1b], '0 < T', leaves={'T': h1a})], 'elrpd', 'T e. RR+')
    fz = s(C0, [], 'fzfid', '%s e. Fin' % FLT)
    # context C2
    qcc = s(C2, ['4'], 'simp1d', 'q e. CC'); wb = s(C2, ['4'], 'simp2d', '( W e. RR /\\ 0 <_ W )'); gT = s(C2, ['4'], 'simp3d', '%s <_ T' % G)
    wr = s(C2, [wb], 'simpld', 'W e. RR'); w0 = s(C2, [wb], 'simprd', '0 <_ W')
    gr = s(C2, [s(C2, [qcc], 'imcld', '( Im ` q ) e. RR')], 'x', 'x') if False else s(C2, [s(C2, [s(C2, [qcc], 'imcld', '( Im ` q ) e. RR')], 'recnd', '( Im ` q ) e. CC')], 'abscld', '%s e. RR' % G)
    g0 = s(C2, [s(C2, [s(C2, [qcc], 'imcld', '( Im ` q ) e. RR')], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ %s' % G)
    lgr_f = '( 1 / ( 1 + %s ) ) <_ ( ( 1 / T ) + sum_ n e. %s %s )' % (G, FLT, IFA)
    lg = ap_(w, C2, [L(h1a, C2), L(h1b, C2), gr, g0, gT], 't21lgr', lgr_f)
    # reals under C3
    q3 = L(qcc, C3)
    n3 = ap_(w, C3, [w.s([], 'simpr', '( %s -> n e. %s )' % (C3, FLT))], 'elfznn', 'n e. NN')
    dnn = s(C3, [n3, s(C3, [n3], 'peano2nnd', '( n + 1 ) e. NN')], 'nnmulcld', '%s e. NN' % D)
    dp = s(C3, [dnn], 'nnrpd', '%s e. RR+' % D)
    cnr = s(C3, [s(C3, [dp], 'rpreccld', '%s e. RR+' % CN)], 'rpred', '%s e. RR' % CN)
    cn0 = s(C3, [s(C3, [dp], 'rpreccld', '%s e. RR+' % CN)], 'rpge0d', '0 <_ %s' % CN)
    ifar, ifa0 = ifnn(w, C3, '%s <_ n' % G, CN, cnr, cn0)
    wr3, w03 = L(wr, C3), L(w0, C3)
    wdr = s(C3, [wr3, dp], 'rerpdivcld', '%s e. RR' % WD)
    wd0 = s(C3, [wr3, dp, w03], 'divge0d', '0 <_ %s' % WD)
    ifzr, ifz0 = ifnn(w, C3, 'q e. Z', WD, wdr, wd0)
    # case split
    Ct = '( %s /\\ %s <_ n )' % (C3, G); Cf = '( %s /\\ -. %s <_ n )' % (C3, G)
    it = w.s([w.s([], 'simpr', '( %s -> %s <_ n )' % (Ct, G))], 'iftrued', '( %s -> %s = %s )' % (Ct, IFA, CN))
    c1n = w.s([L(w.s([], 'simpll', '( %s -> %s )' % (C3, C1)) if False else None, Ct) if False else None], 'x', 'x') if False else None
    # hyp 5 at C3
    c3_1 = w.s([], 'simplll', '( %s -> %s )' % (C3, C1)) if False else None
    s31 = w.s([w.s([], 'simpl', '( %s -> %s )' % (C3, C2))], 'simpld', '( %s -> %s )' % (C3, C1))
    s3n = w.s([], 'simpr', '( %s -> n e. %s )' % (C3, FLT))
    H5 = '( Z C_ S /\\ A. q e. S ( %s <_ n -> q e. Z ) )' % G
    h5 = w.s([s31, s3n, '5'], 'syl2anc', '( %s -> %s )' % (C3, H5))
    al = s(C3, [h5], 'simprd', 'A. q e. S ( %s <_ n -> q e. Z )' % G)
    qS = w.s([w.s([], 'simpl', '( %s -> %s )' % (C3, C2))], 'simprd', '( %s -> q e. S )' % C3)
    imp = s(C3, [qS, al, w.inst('rsp')], 'x', 'x') if False else w.s([al, qS, w.s([], 'rsp', '( A. q e. S ( %s <_ n -> q e. Z ) -> ( q e. S -> ( %s <_ n -> q e. Z ) ) )' % (G, G))], 'sylc', '( %s -> ( %s <_ n -> q e. Z ) )' % (C3, G))
    qZ = w.s([L(imp, Ct), w.s([], 'simpr', '( %s -> %s <_ n )' % (Ct, G))], 'mpd', '( %s -> q e. Z )' % Ct)
    itz = w.s([qZ], 'iftrued', '( %s -> %s = %s )' % (Ct, IFZ, WD))
    dcc = L(s(C3, [dp], 'rpcnd', '%s e. CC' % D), Ct); dne = L(s(C3, [dp], 'rpne0d', '%s =/= 0' % D), Ct)
    wcc = L(s(C3, [wr3], 'recnd', 'W e. CC'), Ct)
    dr_ = w.s([wcc, dcc, dne], 'divrecd', '( %s -> %s = ( W x. %s ) )' % (Ct, WD, CN))
    et = w.s([w.s([it], 'oveq2d', '( %s -> ( W x. %s ) = ( W x. %s ) )' % (Ct, IFA, CN)), dr_], 'eqtr4d', '( %s -> ( W x. %s ) = %s )' % (Ct, IFA, WD))
    et2 = w.s([et, itz], 'eqtr4d', '( %s -> ( W x. %s ) = %s )' % (Ct, IFA, IFZ))
    WIFA = '( W x. %s )' % IFA
    wifar = s(C3, [wr3, ifar], 'remulcld', '%s e. RR' % WIFA)
    ct = w.s([L(wifar, Ct), et2], 'eqled', '( %s -> %s <_ %s )' % (Ct, WIFA, IFZ))
    fz_ = w.s([w.s([], 'simpr', '( %s -> -. %s <_ n )' % (Cf, G))], 'iffalsed', '( %s -> %s = 0 )' % (Cf, IFA))
    ef = w.s([w.s([fz_], 'oveq2d', '( %s -> ( W x. %s ) = ( W x. 0 ) )' % (Cf, IFA)), w.s([L(s(C3, [wr3], 'recnd', 'W e. CC'), Cf)], 'mul01d', '( %s -> ( W x. 0 ) = 0 )' % Cf)], 'eqtrd', '( %s -> %s = 0 )' % (Cf, WIFA))
    cf = w.s([ef, L(ifz0, Cf)], 'eqbrtrd', '( %s -> %s <_ %s )' % (Cf, WIFA, IFZ))
    pt = w.s([ct, cf], 'pm2.61dan', '( %s -> %s <_ %s )' % (C3, WIFA, IFZ))
    # context C2: W / ( 1 + G ) <_ W / T + sum_n IFZ
    fz2 = L(fz, C2)
    SA = 'sum_ n e. %s %s' % (FLT, IFA); SZ = 'sum_ n e. %s %s' % (FLT, IFZ); SWA = 'sum_ n e. %s %s' % (FLT, WIFA)
    sar = s(C2, [fz2, ifar], 'fsumrecl', '%s e. RR' % SA)
    szr = s(C2, [fz2, ifzr], 'fsumrecl', '%s e. RR' % SZ)
    swr = s(C2, [fz2, wifar], 'fsumrecl', '%s e. RR' % SWA)
    sle = s(C2, [fz2, wifar, ifzr, pt], 'fsumle', '%s <_ %s' % (SWA, SZ))
    g1 = '( 1 + %s )' % G
    g1p = s(C2, [s(C2, [w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % C2), gr], 'readdcld', '%s e. RR' % g1), lin.linarith(w, C2, [g0], '0 < %s' % g1, leaves={G: gr})], 'elrpd', '%s e. RR+' % g1)
    rg = s(C2, [s(C2, [g1p], 'rpreccld', '( 1 / %s ) e. RR+' % g1)], 'rpred', '( 1 / %s ) e. RR' % g1)
    rt = s(C2, [s(C2, [L(tp, C2)], 'rpreccld', '( 1 / T ) e. RR+')], 'rpred', '( 1 / T ) e. RR')
    rhs = s(C2, [rt, sar], 'readdcld', '( ( 1 / T ) + %s ) e. RR' % SA)
    m1 = s(C2, [rg, rhs, wr, w0, lg], 'lemul2ad', '( W x. ( 1 / %s ) ) <_ ( W x. ( ( 1 / T ) + %s ) )' % (g1, SA))
    wc = s(C2, [wr], 'recnd', 'W e. CC')
    e1 = s(C2, [wc, s(C2, [g1p], 'rpcnd', '%s e. CC' % g1), s(C2, [g1p], 'rpne0d', '%s =/= 0' % g1)], 'divrecd', '( W / %s ) = ( W x. ( 1 / %s ) )' % (g1, g1))
    e2 = s(C2, [wc, s(C2, [rt], 'recnd', '( 1 / T ) e. CC'), s(C2, [sar], 'recnd', '%s e. CC' % SA)], 'adddid', '( W x. ( ( 1 / T ) + %s ) ) = ( ( W x. ( 1 / T ) ) + ( W x. %s ) )' % (SA, SA))
    e3 = s(C2, [wc, s(C2, [L(tp, C2)], 'rpcnd', 'T e. CC'), s(C2, [L(tp, C2)], 'rpne0d', 'T =/= 0')], 'divrecd', '( W / T ) = ( W x. ( 1 / T ) )')
    e4 = s(C2, [fz2, wc, s(C3, [ifar], 'recnd', '%s e. CC' % IFA)], 'fsummulc2', '( W x. %s ) = %s' % (SA, SWA))
    c = _cl.Closure(w, C2, {})
    for E_, st_ in [('W', wr), ('( 1 / %s )' % g1, rg), ('( 1 / T )', rt), (SA, sar), (SZ, szr), (SWA, swr)]:
        c.leaf(E_, 'RR', st_)
    for E_ in ['( W / %s )' % g1, '( W x. ( 1 / %s ) )' % g1, '( W x. ( ( 1 / T ) + %s ) )' % SA, '( W x. ( 1 / T ) )', '( W x. %s )' % SA, '( W / T )']:
        c.atom(E_)
    c.leaf('( W x. ( 1 / %s ) )' % g1, 'RR', s(C2, [wr, rg], 'remulcld', '( W x. ( 1 / %s ) ) e. RR' % g1))
    c.leaf('( W / %s )' % g1, 'RR', s(C2, [wr, g1p], 'rerpdivcld', '( W / %s ) e. RR' % g1))
    c.leaf('( W x. ( ( 1 / T ) + %s ) )' % SA, 'RR', s(C2, [wr, rhs], 'remulcld', '( W x. ( ( 1 / T ) + %s ) ) e. RR' % SA))
    c.leaf('( W x. ( 1 / T ) )', 'RR', s(C2, [wr, rt], 'remulcld', '( W x. ( 1 / T ) ) e. RR'))
    c.leaf('( W x. %s )' % SA, 'RR', s(C2, [wr, sar], 'remulcld', '( W x. %s ) e. RR' % SA))
    c.leaf('( W / T )', 'RR', s(C2, [wr, L(tp, C2)], 'rerpdivcld', '( W / T ) e. RR'))
    BND = '( ( W / T ) + %s )' % SZ
    pw = lin.linarith(w, C2, [m1, e1, e2, e3, e4, sle], '( W / %s ) <_ %s' % (g1, BND), closure=c)
    bndr = s(C2, [c.mem('( W / T )', 'RR'), szr], 'readdcld', '%s e. RR' % BND)
    # ---- context C1: sums over q
    SQ = lambda b: 'sum_ q e. S %s' % b
    wg = '( W / %s )' % g1
    wgr = c.mem(wg, 'RR')
    a1 = s(C1, ['3', wgr, bndr, pw], 'fsumle', '%s <_ %s' % (SQ(wg), SQ(BND)))
    wtr = c.mem('( W / T )', 'RR')
    a2 = s(C1, ['3', s(C2, [wtr], 'recnd', '( W / T ) e. CC'), s(C2, [szr], 'recnd', '%s e. CC' % SZ)], 'fsumadd', '%s = ( %s + %s )' % (SQ(BND), SQ('( W / T )'), SQ(SZ)))
    tp1 = L(tp, C1)
    a3 = s(C1, ['3', s(C1, [tp1], 'rpcnd', 'T e. CC'), wc, s(C1, [tp1], 'rpne0d', 'T =/= 0')], 'fsumdivc', '( %s / T ) = %s' % (SQ('W'), SQ('( W / T )')))
    C4 = '( %s /\\ ( q e. S /\\ n e. %s ) )' % (C1, FLT)
    c43 = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (C4, C1)), w.s([w.s([], 'simpr', '( %s -> ( q e. S /\\ n e. %s ) )' % (C4, FLT))], 'simpld', '( %s -> q e. S )' % C4)], 'jca', '( %s -> %s )' % (C4, C2)),
               w.s([w.s([], 'simpr', '( %s -> ( q e. S /\\ n e. %s ) )' % (C4, FLT))], 'simprd', '( %s -> n e. %s )' % (C4, FLT))], 'jca', '( %s -> %s )' % (C4, C3))
    ifzc4 = w.s([c43, s(C3, [ifzr], 'recnd', '%s e. CC' % IFZ)], 'syl', '( %s -> %s e. CC )' % (C4, IFZ))
    SNQ = 'sum_ n e. %s sum_ q e. S %s' % (FLT, IFZ)
    a4 = s(C1, ['3', L(fz, C1), ifzc4], 'fsumcom', '%s = %s' % (SQ(SZ), SNQ))
    # per n at C1n
    h5n = '5'
    zs = s(C1n, [h5n], 'simpld', 'Z C_ S')
    s3n = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (C1n, C1))], 'simprd', '( %s -> x e. I )' % C1n)], 'x', 'x') if False else None
    fs1n = w.s([w.s([], 'simpl', '( %s -> %s )' % (C1n, C1)), '3'], 'syl', '( %s -> S e. Fin )' % C1n)
    zf = ap_(w, C1n, [fs1n, zs], 'ssfi', 'Z e. Fin')
    C5 = '( %s /\\ q e. Z )' % C1n
    c5q = w.s([L(zs, C5), w.s([], 'simpr', '( %s -> q e. Z )' % C5)], 'sseldd', '( %s -> q e. S )' % C5)
    c52 = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (C5, C1n))], 'simpld', '( %s -> %s )' % (C5, C1)), c5q], 'jca', '( %s -> %s )' % (C5, C2))
    wr5 = w.s([c52, wr], 'syl', '( %s -> W e. RR )' % C5)
    n1n = ap_(w, C1n, [w.s([], 'simpr', '( %s -> n e. %s )' % (C1n, FLT))], 'elfznn', 'n e. NN')
    dp1 = s(C1n, [s(C1n, [n1n, s(C1n, [n1n], 'peano2nnd', '( n + 1 ) e. NN')], 'nnmulcld', '%s e. NN' % D)], 'nnrpd', '%s e. RR+' % D)
    wd5 = w.s([wr5, L(dp1, C5)], 'rerpdivcld', '( %s -> %s e. RR )' % (C5, WD))
    ral = w.s([w.s([wd5], 'recnd', '( %s -> %s e. CC )' % (C5, WD))], 'ralrimiva', '( %s -> A. q e. Z %s e. CC )' % (C1n, WD))
    orf = w.s([fs1n], 'olcd', '( %s -> ( S C_ ( ZZ>= ` 1 ) \\/ S e. Fin ) )' % C1n)
    ss2 = ap_(w, C1n, [zs, ral, orf], 'sumss2', 'sum_ q e. Z %s = sum_ q e. S %s' % (WD, IFZ))
    dv = s(C1n, [zf, s(C1n, [dp1], 'rpcnd', '%s e. CC' % D), w.s([wr5], 'recnd', '( %s -> W e. CC )' % C5), s(C1n, [dp1], 'rpne0d', '%s =/= 0' % D)], 'fsumdivc', '( sum_ q e. Z W / %s ) = sum_ q e. Z %s' % (D, WD))
    pn = s(C1n, [ss2, dv], 'eqtr2d', 'sum_ q e. S %s = ( sum_ q e. Z W / %s )' % (IFZ, D))
    EZ = '( sum_ q e. Z W / %s )' % D
    a5 = s(C1, [pn], 'sumeq2dv', '%s = sum_ n e. %s %s' % (SNQ, FLT, EZ))
    # C1 bound
    SWq = SQ('W')
    swqr = s(C1, ['3', wr], 'fsumrecl', '%s e. RR' % SWq)
    ezr = s(C1n, [s(C1n, [zf, wr5], 'fsumrecl', 'sum_ q e. Z W e. RR'), dp1], 'rerpdivcld', '%s e. RR' % EZ)
    SNE = 'sum_ n e. %s %s' % (FLT, EZ)
    sner = s(C1, [L(fz, C1), ezr], 'fsumrecl', '%s e. RR' % SNE)
    c1 = _cl.Closure(w, C1, {})
    for E_, st_ in [(SQ(wg), s(C1, ['3', wgr], 'fsumrecl', '%s e. RR' % SQ(wg))), (SQ(BND), s(C1, ['3', bndr], 'fsumrecl', '%s e. RR' % SQ(BND))),
                    (SQ('( W / T )'), s(C1, ['3', wtr], 'fsumrecl', '%s e. RR' % SQ('( W / T )'))), (SQ(SZ), s(C1, ['3', szr], 'fsumrecl', '%s e. RR' % SQ(SZ))),
                    (SWq, swqr), (SNE, sner), ('T', L(h1a, C1))]:
        c1.leaf(E_, 'RR', st_)
    for E_ in [SNQ, '( %s / T )' % SWq]:
        c1.atom(E_)
    c1.leaf('( %s / T )' % SWq, 'RR', s(C1, [swqr, tp1], 'rerpdivcld', '( %s / T ) e. RR' % SWq))
    c1.leaf(SNQ, 'RR', s(C1, [a5, sner], 'eqeltrd', '%s e. RR' % SNQ))
    B1 = '( ( %s / T ) + %s )' % (SWq, SNE)
    pb1 = lin.linarith(w, C1, [a1, a2, a3, a4, a5], '%s <_ %s' % (SQ(wg), B1), closure=c1)
    # ---- context ph: sums over x
    SX = lambda b: 'sum_ x e. I %s' % b
    b1r = s(C1, [c1.mem('( %s / T )' % SWq, 'RR'), sner], 'readdcld', '%s e. RR' % B1)
    x1 = s(C0, ['2', c1.mem(SQ(wg), 'RR'), b1r, pb1], 'fsumle', '%s <_ %s' % (SX(SQ(wg)), SX(B1)))
    x2 = s(C0, ['2', s(C1, [c1.mem('( %s / T )' % SWq, 'RR')], 'recnd', '( %s / T ) e. CC' % SWq), s(C1, [sner], 'recnd', '%s e. CC' % SNE)], 'fsumadd',
           '%s = ( %s + %s )' % (SX(B1), SX('( %s / T )' % SWq), SX(SNE)))
    x3 = s(C0, ['2', s(C0, [tp], 'rpcnd', 'T e. CC'), s(C1, [swqr], 'recnd', '%s e. CC' % SWq), s(C0, [tp], 'rpne0d', 'T =/= 0')], 'fsumdivc', '( %s / T ) = %s' % (SX(SWq), SX('( %s / T )' % SWq)))
    C6 = '( ph /\\ ( x e. I /\\ n e. %s ) )' % FLT
    c61 = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % C6), w.s([w.s([], 'simpr', '( %s -> ( x e. I /\\ n e. %s ) )' % (C6, FLT))], 'simpld', '( %s -> x e. I )' % C6)], 'jca', '( %s -> %s )' % (C6, C1)),
               w.s([w.s([], 'simpr', '( %s -> ( x e. I /\\ n e. %s ) )' % (C6, FLT))], 'simprd', '( %s -> n e. %s )' % (C6, FLT))], 'jca', '( %s -> %s )' % (C6, C1n))
    ez6 = w.s([c61, s(C1n, [ezr], 'recnd', '%s e. CC' % EZ)], 'syl', '( %s -> %s e. CC )' % (C6, EZ))
    SNX = 'sum_ n e. %s %s' % (FLT, SX(EZ))
    x4 = s(C0, ['2', fz, ez6], 'fsumcom', '%s = %s' % (SX(SNE), SNX))
    C7 = '( ph /\\ n e. %s )' % FLT
    C8 = '( %s /\\ x e. I )' % C7
    c81 = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (C8, C7))], 'simpld', '( %s -> ph )' % C8), w.s([], 'simpr', '( %s -> x e. I )' % C8)], 'jca', '( %s -> %s )' % (C8, C1))
    c8n = w.s([w.s([c81, w.s([w.s([], 'simpl', '( %s -> %s )' % (C8, C7))], 'simprd', '( %s -> n e. %s )' % (C8, FLT))], 'jca', '( %s -> %s )' % (C8, C1n)),
               s(C1n, [zf, wr5], 'fsumrecl', 'sum_ q e. Z W e. RR')], 'syl', '( %s -> sum_ q e. Z W e. RR )' % C8)
    n7 = ap_(w, C7, [w.s([], 'simpr', '( %s -> n e. %s )' % (C7, FLT))], 'elfznn', 'n e. NN')
    dp7 = s(C7, [s(C7, [n7, s(C7, [n7], 'peano2nnd', '( n + 1 ) e. NN')], 'nnmulcld', '%s e. NN' % D)], 'nnrpd', '%s e. RR+' % D)
    i2 = w.s([w.s([], 'simpl', '( %s -> ph )' % C7), '2'], 'syl', '( %s -> I e. Fin )' % C7)
    x5a = s(C7, [i2, s(C7, [dp7], 'rpcnd', '%s e. CC' % D), w.s([c8n], 'recnd', '( %s -> sum_ q e. Z W e. CC )' % C8), s(C7, [dp7], 'rpne0d', '%s =/= 0' % D)], 'fsumdivc',
            '( %s / %s ) = %s' % (SX('sum_ q e. Z W'), D, SX(EZ)))
    FIN = '( %s / %s )' % (SX('sum_ q e. Z W'), D)
    x5 = s(C0, [s(C7, [x5a], 'eqcomd', '%s = %s' % (SX(EZ), FIN))], 'sumeq2dv', '%s = sum_ n e. %s %s' % (SNX, FLT, FIN))
    c0 = _cl.Closure(w, C0, {})
    SFIN = 'sum_ n e. %s %s' % (FLT, FIN)
    finr = s(C7, [s(C7, [i2, c8n], 'fsumrecl', '%s e. RR' % SX('sum_ q e. Z W')), dp7], 'rerpdivcld', '%s e. RR' % FIN)
    sfr = s(C0, [fz, finr], 'fsumrecl', '%s e. RR' % SFIN)
    sxw = s(C0, ['2', swqr], 'fsumrecl', '%s e. RR' % SX(SWq))
    for E_, st_ in [(SX(SQ(wg)), s(C0, ['2', c1.mem(SQ(wg), 'RR')], 'fsumrecl', '%s e. RR' % SX(SQ(wg)))), (SX(B1), s(C0, ['2', b1r], 'fsumrecl', '%s e. RR' % SX(B1))),
                    (SX('( %s / T )' % SWq), s(C0, ['2', c1.mem('( %s / T )' % SWq, 'RR')], 'fsumrecl', '%s e. RR' % SX('( %s / T )' % SWq))),
                    (SX(SNE), s(C0, ['2', sner], 'fsumrecl', '%s e. RR' % SX(SNE))), (SFIN, sfr), ('( %s / T )' % SX(SWq), s(C0, [sxw, tp], 'rerpdivcld', '( %s / T ) e. RR' % SX(SWq)))]:
        c0.leaf(E_, 'RR', st_)
    c0.leaf(SNX, 'RR', s(C0, [x5, sfr], 'eqeltrd', '%s e. RR' % SNX))
    fin = lin.linarith(w, C0, [x1, x2, x3, x4, x5], '%s <_ ( ( %s / T ) + %s )' % (SX(SQ(wg)), SX(SWq), SFIN), closure=c0)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21lg']))
    return run(w)

def dfin(w, A_, nn):
    """( A_ -> ( Base ` ( DChr ` N ) ) e. Fin ) from nn : ( A_ -> N e. NN )"""
    g = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); b = w.s([], 'eqid', '%s = %s' % (DB, DB))
    return w.s([nn, w.s([g, b], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB)], 'syl', '( %s -> %s e. Fin )' % (A_, DB))


def ezf_inst(w, A_, nn, xin, ar, a0, a1, tr, a='A', t='T'):
    """( A_ -> ( ZF e. Fin /\\ A. q e. ZF ord e. NN ) ) at abscissa a, height t"""
    Z = ZFX(a, t)
    f = '( %s e. Fin /\\ A. q e. %s %s e. NN )' % (Z, Z, ORD())
    return ap_(w, A_, [nn, xin, ar, a0, a1, tr], 'ezf', f)


def gen_lgs():
    w = W('t21lgs', '(L-gamma) summed over the characters mod ` N ` : ` sum_chi sum_rho ord / ( 1 + abs gamma ) <_ N ( sigma , T ) / T + sum_ ( 1 <_ n <_ floor T ) N ( sigma , n ) / ( n ( n + 1 ) ) ` (Lean ` Lgamma_sum ` ; ~ t21lg , ~ ezf ).')
    A0 = ante_of(S['t21lgs'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    nn, ar, a0, a1, tr, t1 = u['N e. NN'], u['A e. RR'], u['0 < A'], u['A <_ 1'], u['T e. RR'], u['1 <_ T']
    L = lambda st_, A_: _cl.lift(w, st_, A_)
    h1 = st([tr, t1], 'jca', '( T e. RR /\\ 1 <_ T )')
    h2 = dfin(w, A0, nn)
    C1 = '( %s /\\ x e. %s )' % (A0, DB)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (C1, DB))
    ez = ezf_inst(w, C1, L(nn, C1), xin, L(ar, C1), L(a0, C1), L(a1, C1), L(tr, C1))
    Z = ZFX('A', 'T')
    h3 = w.s([ez], 'simpld', '( %s -> %s e. Fin )' % (C1, Z))
    C2 = '( %s /\\ q e. %s )' % (C1, Z)
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, Z))
    el = ap_(w, C2, [L(ar, C2), L(tr, C2)], 't21zfel', '( q e. %s <-> ( q e. CC /\\ ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (Z, EX))
    cnd = w.s([qin, el], 'mpbid', '( %s -> ( q e. CC /\\ ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (C2, EX))
    qc = w.s([cnd], 'simp1d', '( %s -> q e. CC )' % C2)
    imt = w.s([w.s([cnd], 'simp2d', '( %s -> ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T ) )' % C2)], 'simprd', '( %s -> ( abs ` ( Im ` q ) ) <_ T )' % C2)
    ordn = w.s([L(w.s([ez], 'simprd', '( %s -> A. q e. %s %s e. NN )' % (C1, Z, ORD())), C2), qin, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (Z, ORD(), Z, ORD()))], 'sylc', '( %s -> %s e. NN )' % (C2, ORD()))
    orr = w.s([ordn], 'nnred', '( %s -> %s e. RR )' % (C2, ORD()))
    or0 = w.s([w.s([ordn], 'nnnn0d', '( %s -> %s e. NN0 )' % (C2, ORD()))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (C2, ORD()))
    h4 = w.s([qc, w.s([orr, or0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (C2, ORD(), ORD())), imt], '3jca',
             '( %s -> ( q e. CC /\\ ( %s e. RR /\\ 0 <_ %s ) /\\ ( abs ` ( Im ` q ) ) <_ T ) )' % (C2, ORD(), ORD()))
    C3 = '( %s /\\ n e. %s )' % (C1, FLT)
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (C3, FLT))
    nz = ap_(w, C3, [nin], 'elfzelz', 'n e. ZZ'); nr = w.s([nz], 'zred', '( %s -> n e. RR )' % C3)
    nle = ap_(w, C3, [nin], 'elfzle2', 'n <_ ( |_ ` T )')
    ntr = w.s([nr, w.s([L(tr, C3)], 'flcld', '( %s -> ( |_ ` T ) e. ZZ )' % C3) and w.s([w.s([L(tr, C3)], 'flcld', '( %s -> ( |_ ` T ) e. ZZ )' % C3)], 'zred', '( %s -> ( |_ ` T ) e. RR )' % C3), L(tr, C3), nle, ap_(w, C3, [L(tr, C3)], 'flle', '( |_ ` T ) <_ T')], 'letrd', '( %s -> n <_ T )' % C3)
    Zn = ZFX('A', 'n')
    ss = ap_(w, C3, [L(ar, C3), L(ar, C3), w.s([L(ar, C3)], 'leidd', '( %s -> A <_ A )' % C3), nr, L(tr, C3), ntr], 't21zfss', '%s C_ %s' % (Zn, Z))
    C4 = '( %s /\\ q e. %s )' % (C3, Z)
    C4i = '( %s /\\ ( abs ` ( Im ` q ) ) <_ n )' % C4
    q4 = w.s([w.s([], 'simpl', '( %s -> %s )' % (C4i, C4))], 'simprd', '( %s -> q e. %s )' % (C4i, Z))
    el4 = ap_(w, C4i, [L(ar, C4i), L(tr, C4i)], 't21zfel', '( q e. %s <-> ( q e. CC /\\ ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (Z, EX))
    cn4 = w.s([q4, el4], 'mpbid', '( %s -> ( q e. CC /\\ ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (C4i, EX))
    rr4 = w.s([w.s([cn4], 'simp2d', '( %s -> ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ T ) )' % C4i)], 'simpld', '( %s -> ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) )' % C4i)
    cn4n = w.s([w.s([cn4], 'simp1d', '( %s -> q e. CC )' % C4i), w.s([rr4, w.s([], 'simpr', '( %s -> ( abs ` ( Im ` q ) ) <_ n )' % C4i)], 'jca', '( %s -> ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ n ) )' % C4i),
                w.s([cn4], 'simp3d', '( %s -> ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (C4i, EX))], '3jca',
               '( %s -> ( q e. CC /\\ ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ n ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (C4i, EX))
    el4n = ap_(w, C4i, [L(ar, C4i), L(nr, C4i)], 't21zfel', '( q e. %s <-> ( q e. CC /\\ ( ( A <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ n ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) ) )' % (Zn, EX))
    qzn = w.s([cn4n, el4n], 'mpbird', '( %s -> q e. %s )' % (C4i, Zn))
    ral = w.s([w.s([qzn], 'ex', '( %s -> ( ( abs ` ( Im ` q ) ) <_ n -> q e. %s ) )' % (C4, Zn))], 'ralrimiva', '( %s -> A. q e. %s ( ( abs ` ( Im ` q ) ) <_ n -> q e. %s ) )' % (C3, Z, Zn))
    h5 = w.s([ss, ral], 'jca', '( %s -> ( %s C_ %s /\\ A. q e. %s ( ( abs ` ( Im ` q ) ) <_ n -> q e. %s ) ) )' % (C3, Zn, Z, Z, Zn))
    w.qed([h1, h2, h3, h4, h5], 't21lg', S['t21lgs'])
    return run(w)


if __name__ == '__main__':
    only = sys.argv[1:]
    for lab, f in [('t21lgr', gen_lgr), ('t21lg', gen_lg), ('t21lgs', gen_lgs)]:
        if not only or lab in only:
            f()
