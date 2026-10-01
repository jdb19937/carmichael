"""C7b section 1, the tail: dconvblk (a block of the B-series), dconvfl
(the floor), dconvtm (the two combined, one term of the difference)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin
lin.FASTPATH = True
lin.MAXDEG = 6

BZ = '( %s /\\ %s )' % (CFBB, ZP1)
N1 = '( 1 ... N )'


def ps_cl(w, ante, M, bfa, zca, fr=None):
    """( ante -> PS(B,M) e. CC ); range ( 1 ... M ) unless fr=(lo) given"""
    rng = '( 1 ... %s )' % M if fr is None else '( %s ... %s )' % (fr, M)
    Ai = '( %s /\\ i e. %s )' % (ante, rng)
    im = w.s([], 'simpr', '( %s -> i e. %s )' % (Ai, rng))
    inn = w.s([im, w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
    ti = trmcl(w, Ai, 'B', 'i', w.s([bfa], 'adantr', '( %s -> B : NN --> CC )' % Ai), inn, w.s([zca], 'adantr', '( %s -> Z e. CC )' % Ai))
    return w.s([fsumfin(w, ante, M), ti], 'fsumcl', '( %s -> %s e. CC )' % (ante, PS('B', M)))


if __name__ == '__main__' and (not only or 'dconvblk' in only):
    # ---------------------------------------------------------------- dconvblk
    w = W('dconvblk', 'A block ` ( M , N ] ` of the partial sums of a Dirichlet series with bounded coefficients: '
          'at most ` C M ^c ( 1 - Re Z ) / ( Re Z - 1 ) ` (the finite form of ~ dsertl ).')
    A0 = '( %s /\\ ( M e. NN /\\ N e. ( ZZ>= ` M ) ) )' % BZ
    cfb = w.s([], 'simpll', '( %s -> %s )' % (A0, CFBB))
    zp = w.s([], 'simplr', '( %s -> %s )' % (A0, ZP1))
    mnn = w.s([], 'simprl', '( %s -> M e. NN )' % A0)
    nuz = w.s([], 'simprr', '( %s -> N e. ( ZZ>= ` M ) )' % A0)
    z = zctx(w, A0, zp)
    c = cfbctx(w, A0, cfb)
    c0 = w.s([cfb, w.inst('cfb0')], 'syl', '( %s -> 0 <_ C )' % A0)
    M1 = '( M + 1 )'
    TR = '( %s ... N )' % M1
    TS = 'sum_ i e. %s %s' % (TR, TRM('B', 'i'))
    m1nn = w.s([mnn], 'peano2nnd', '( %s -> %s e. NN )' % (A0, M1))
    m1uz = w.s([m1nn, w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> %s e. ( ZZ>= ` 1 ) )' % (A0, M1))
    un = w.s([m1uz, nuz, w.inst('fzsplit2')], 'syl2anc', '( %s -> %s = ( ( 1 ... M ) u. %s ) )' % (A0, N1, TR))
    mr = w.s([mnn], 'nnred', '( %s -> M e. RR )' % A0)
    dj = w.s([w.s([mr], 'ltp1d', '( %s -> M < %s )' % (A0, M1)), w.inst('fzdisj')], 'syl', '( %s -> ( ( 1 ... M ) i^i %s ) = (/) )' % (A0, TR))
    # N e. NN
    nnn = w.s([mnn, nuz, w.inst('eluznn')], 'syl2anc', '( %s -> N e. NN )' % A0)
    An = '( %s /\\ i e. %s )' % (A0, N1)
    inn = w.s([w.s([], 'simpr', '( %s -> i e. %s )' % (An, N1)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % An)
    tin = trmcl(w, An, 'B', 'i', w.s([c['bf']], 'adantr', '( %s -> B : NN --> CC )' % An), inn, w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % An))
    spl = w.s([dj, un, fsumfin(w, A0, 'N'), tin], 'fsumsplit', '( %s -> %s = ( %s + %s ) )' % (A0, PS('B', 'N'), PS('B', 'M'), TS))
    At = '( %s /\\ i e. %s )' % (A0, TR)
    itr = w.s([], 'simpr', '( %s -> i e. %s )' % (At, TR))
    iuz = w.s([itr, w.inst('elfzuz')], 'syl', '( %s -> i e. ( ZZ>= ` %s ) )' % (At, M1))
    itn = w.s([w.s([m1nn], 'adantr', '( %s -> %s e. NN )' % (At, M1)), iuz, w.inst('eluznn')], 'syl2anc', '( %s -> i e. NN )' % At)
    zct = w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % At)
    tit = trmcl(w, At, 'B', 'i', w.s([c['bf']], 'adantr', '( %s -> B : NN --> CC )' % At), itn, zct)
    tsc = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, TR)), tit], 'fsumcl', '( %s -> %s e. CC )' % (A0, TS))
    pm = ps_cl(w, A0, 'M', c['bf'], z['zc'])
    dif = w.s([w.s([spl], 'oveq1d', '( %s -> ( %s - %s ) = ( ( %s + %s ) - %s ) )' % (A0, PS('B', 'N'), PS('B', 'M'), PS('B', 'M'), TS, PS('B', 'M'))),
               w.s([pm, tsc], 'pncan2d', '( %s -> ( ( %s + %s ) - %s ) = %s )' % (A0, PS('B', 'M'), TS, PS('B', 'M'), TS))],
              'eqtrd', '( %s -> ( %s - %s ) = %s )' % (A0, PS('B', 'N'), PS('B', 'M'), TS))
    adif = w.s([dif], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` %s ) )' % (A0, PS('B', 'N'), PS('B', 'M'), TS))
    trfin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, TR))
    ab1 = w.s([trfin, tit], 'fsumabs', '( %s -> ( abs ` %s ) <_ sum_ i e. %s ( abs ` %s ) )' % (A0, TS, TR, TRM('B', 'i')))
    PW = '( i ^c -u %s )' % RZ
    rzt = w.s([z['rz']], 'adantr', '( %s -> %s e. RR )' % (At, RZ))
    irp = w.s([itn], 'nnrpd', '( %s -> i e. RR+ )' % At)
    pwr = w.s([w.s([irp, w.s([rzt], 'renegcld', '( %s -> -u %s e. RR )' % (At, RZ))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (At, PW))], 'rpred', '( %s -> %s e. RR )' % (At, PW))
    crt = w.s([c['cr']], 'adantr', '( %s -> C e. RR )' % At)
    cpw = w.s([crt, pwr], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (At, PW))
    atr = w.s([tit], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, TRM('B', 'i')))
    hyp = w.s([w.s([cfb], 'adantr', '( %s -> %s )' % (At, CFBB)),
               w.s([w.s([itn, rzt, zct], '3jca', '( %s -> ( i e. NN /\\ %s e. RR /\\ Z e. CC ) )' % (At, RZ)), w.s([rzt], 'leidd', '( %s -> %s <_ %s )' % (At, RZ, RZ))],
                   'jca', '( %s -> ( ( i e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) )' % (At, RZ, RZ, RZ))],
              'jca', '( %s -> ( %s /\\ ( ( i e. NN /\\ %s e. RR /\\ Z e. CC ) /\\ %s <_ %s ) ) )' % (At, CFBB, RZ, RZ, RZ))
    dtm = w.s([hyp, w.inst('dtmabs')], 'syl', '( %s -> ( abs ` %s ) <_ ( C x. %s ) )' % (At, TRM('B', 'i'), PW))
    ab2 = w.s([trfin, atr, cpw, dtm], 'fsumle', '( %s -> sum_ i e. %s ( abs ` %s ) <_ sum_ i e. %s ( C x. %s ) )' % (A0, TR, TRM('B', 'i'), TR, PW))
    pwc = w.s([pwr], 'recnd', '( %s -> %s e. CC )' % (At, PW))
    ab3 = w.s([trfin, w.s([c['cr']], 'recnd', '( %s -> C e. CC )' % A0), pwc], 'fsummulc2',
              '( %s -> ( C x. sum_ i e. %s %s ) = sum_ i e. %s ( C x. %s ) )' % (A0, TR, PW, TR, PW))
    BD = '( ( M ^c ( 1 - %s ) ) / %s )' % (RZ, E1)
    zh = w.s([w.s([z['rz'], z['z1']], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)), w.s([mnn, nuz], 'jca', '( %s -> ( M e. NN /\\ N e. ( ZZ>= ` M ) ) )' % A0)],
             'jca', '( %s -> ( ( %s e. RR /\\ 1 < %s ) /\\ ( M e. NN /\\ N e. ( ZZ>= ` M ) ) ) )' % (A0, RZ, RZ))
    zf = w.s([zh, w.inst('zserfz2')], 'syl', '( %s -> sum_ k e. %s ( k ^c -u %s ) <_ %s )' % (A0, TR, RZ, BD))
    ki = w.s([], 'oveq1', '( k = i -> ( k ^c -u %s ) = %s )' % (RZ, PW))
    cbk = w.s([ki], 'cbvsumv', 'sum_ k e. %s ( k ^c -u %s ) = sum_ i e. %s %s' % (TR, RZ, TR, PW))
    ab4 = w.s([zf, w.s([cbk], 'a1i', '( %s -> sum_ k e. %s ( k ^c -u %s ) = sum_ i e. %s %s )' % (A0, TR, RZ, TR, PW))], 'eqbrtrrd',
              '( %s -> sum_ i e. %s %s <_ %s )' % (A0, TR, PW, BD))
    sr = w.s([trfin, pwr], 'fsumrecl', '( %s -> sum_ i e. %s %s e. RR )' % (A0, TR, PW))
    mrp = w.s([mnn], 'nnrpd', '( %s -> M e. RR+ )' % A0)
    bdr = w.s([w.s([w.s([mrp, w.s([z['r1'], z['rz']], 'resubcld', '( %s -> ( 1 - %s ) e. RR )' % (A0, RZ))], 'rpcxpcld', '( %s -> ( M ^c ( 1 - %s ) ) e. RR+ )' % (A0, RZ))],
                     'rpred', '( %s -> ( M ^c ( 1 - %s ) ) e. RR )' % (A0, RZ)), z['e1rp']], 'rerpdivcld', '( %s -> %s e. RR )' % (A0, BD))
    ab5 = w.s([sr, bdr, c['cr'], c0, ab4], 'lemul2ad', '( %s -> ( C x. sum_ i e. %s %s ) <_ ( C x. %s ) )' % (A0, TR, PW, BD))
    s2 = w.s([ab2, w.s([ab3, ab5], 'eqbrtrrd', '( %s -> sum_ i e. %s ( C x. %s ) <_ ( C x. %s ) )' % (A0, TR, PW, BD))], 'jca',
             '( %s -> ( sum_ i e. %s ( abs ` %s ) <_ sum_ i e. %s ( C x. %s ) /\\ sum_ i e. %s ( C x. %s ) <_ ( C x. %s ) ) )' % (A0, TR, TRM('B', 'i'), TR, PW, TR, PW, BD))
    satr = w.s([trfin, atr], 'fsumrecl', '( %s -> sum_ i e. %s ( abs ` %s ) e. RR )' % (A0, TR, TRM('B', 'i')))
    scpw = w.s([trfin, cpw], 'fsumrecl', '( %s -> sum_ i e. %s ( C x. %s ) e. RR )' % (A0, TR, PW))
    cbd = w.s([c['cr'], bdr], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (A0, BD))
    l1 = w.s([satr, scpw, cbd, ab2, w.s([ab3, ab5], 'eqbrtrrd', '( %s -> sum_ i e. %s ( C x. %s ) <_ ( C x. %s ) )' % (A0, TR, PW, BD))], 'letrd',
             '( %s -> sum_ i e. %s ( abs ` %s ) <_ ( C x. %s ) )' % (A0, TR, TRM('B', 'i'), BD))
    ats = w.s([tsc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, TS))
    l2 = w.s([ats, satr, cbd, ab1, l1], 'letrd', '( %s -> ( abs ` %s ) <_ ( C x. %s ) )' % (A0, TS, BD))
    w.qed([adif, l2], 'eqbrtrd', '( %s -> ( abs ` ( %s - %s ) ) <_ ( C x. %s ) )' % (A0, PS('B', 'N'), PS('B', 'M'), BD))
    run7b(w)


if __name__ == '__main__' and (not only or 'dconvfl' in only):
    # ---------------------------------------------------------------- dconvfl
    w = W('dconvfl', 'The floor of ` N / D ` for ` D <_ N ` is at least ` N / ( 2 D ) ` , so its ` -u E ` power is at most ` 2 ^c E D ^c E N ^c -u E ` .')
    A0 = '( ( N e. NN /\\ D e. ( 1 ... N ) ) /\\ E e. RR+ )'
    nn = w.s([], 'simpll', '( %s -> N e. NN )' % A0)
    dm = w.s([], 'simplr', '( %s -> D e. ( 1 ... N ) )' % A0)
    erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
    dnn = w.s([dm, w.inst('elfznn')], 'syl', '( %s -> D e. NN )' % A0)
    dle = w.s([dm, w.inst('elfzle2')], 'syl', '( %s -> D <_ N )' % A0)
    nrp = w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % A0)
    drp = w.s([dnn], 'nnrpd', '( %s -> D e. RR+ )' % A0)
    nr = w.s([nrp], 'rpred', '( %s -> N e. RR )' % A0)
    X = '( N / D )'
    xrp = w.s([nrp, drp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, X))
    xr = w.s([xrp], 'rpred', '( %s -> %s e. RR )' % (A0, X))
    x1 = w.s([drp, nr, dle, w.inst('divge1')], 'syl3anc', '( %s -> 1 <_ %s )' % (A0, X))
    F = FLD
    fnn = w.s([xr, x1, w.inst('flge1nn')], 'syl2anc', '( %s -> %s e. NN )' % (A0, F))
    flt = w.s([xr, w.inst('flltp1')], 'syl', '( %s -> %s < ( %s + 1 ) )' % (A0, X, F))
    f1 = w.s([fnn], 'nnge1d', '( %s -> 1 <_ %s )' % (A0, F))
    frp = w.s([fnn], 'nnrpd', '( %s -> %s e. RR+ )' % (A0, F))
    fr = w.s([frp], 'rpred', '( %s -> %s e. RR )' % (A0, F))
    X2 = '( %s / 2 )' % X
    x2le = lin.linarith(w, A0, [flt, f1], '%s <_ %s' % (X2, F), leaves={X: xr, F: fr})
    x2rp = w.s([xrp, w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0)], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, X2))
    er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
    e0 = w.s([erp], 'rpge0d', '( %s -> 0 <_ E )' % A0)
    cn = w.s([w.s([x2rp, frp, er], '3jca', '( %s -> ( %s e. RR+ /\\ %s e. RR+ /\\ E e. RR ) )' % (A0, X2, F)), w.s([e0, x2le], 'jca', '( %s -> ( 0 <_ E /\\ %s <_ %s ) )' % (A0, X2, F))],
             'jca', '( %s -> ( ( %s e. RR+ /\\ %s e. RR+ /\\ E e. RR ) /\\ ( 0 <_ E /\\ %s <_ %s ) ) )' % (A0, X2, F, X2, F))
    le1 = w.s([cn, w.inst('cxpnegle')], 'syl', '( %s -> ( %s ^c -u E ) <_ ( %s ^c -u E ) )' % (A0, F, X2))
    ec = w.s([erp], 'rpcnd', '( %s -> E e. CC )' % A0)
    e1 = w.s([w.s([x2rp], 'rpcnd', '( %s -> %s e. CC )' % (A0, X2)), w.s([x2rp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, X2)), ec], 'cxpnegd',
             '( %s -> ( %s ^c -u E ) = ( 1 / ( %s ^c E ) ) )' % (A0, X2, X2))
    e2 = w.s([x2rp, ec], 'cxprecd', '( %s -> ( ( 1 / %s ) ^c E ) = ( 1 / ( %s ^c E ) ) )' % (A0, X2, X2))
    two = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
    two0 = w.s([], '2ne0', '2 =/= 0')
    two0 = w.s([two0], 'a1i', '( %s -> 2 =/= 0 )' % A0)
    xc = w.s([xrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, X))
    e3 = w.s([xc, two, w.s([xrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, X)), two0], 'recdivd', '( %s -> ( 1 / %s ) = ( 2 / %s ) )' % (A0, X2, X))
    nc = w.s([nrp], 'rpcnd', '( %s -> N e. CC )' % A0)
    dc = w.s([drp], 'rpcnd', '( %s -> D e. CC )' % A0)
    e4 = w.s([two, nc, dc, w.s([nrp], 'rpne0d', '( %s -> N =/= 0 )' % A0), w.s([drp], 'rpne0d', '( %s -> D =/= 0 )' % A0)], 'divdiv2d',
             '( %s -> ( 2 / %s ) = ( ( 2 x. D ) / N ) )' % (A0, X))
    e5 = w.s([w.s([two, dc], 'mulcld', '( %s -> ( 2 x. D ) e. CC )' % A0), nc, w.s([nrp], 'rpne0d', '( %s -> N =/= 0 )' % A0)], 'divrecd',
             '( %s -> ( ( 2 x. D ) / N ) = ( ( 2 x. D ) x. ( 1 / N ) ) )' % A0)
    R = '( ( 2 x. D ) x. ( 1 / N ) )'
    e35 = w.s([w.s([e3, e4], 'eqtrd', '( %s -> ( 1 / %s ) = ( ( 2 x. D ) / N ) )' % (A0, X2)), e5], 'eqtrd', '( %s -> ( 1 / %s ) = %s )' % (A0, X2, R))
    e6a = w.s([e35], 'oveq1d', '( %s -> ( ( 1 / %s ) ^c E ) = ( %s ^c E ) )' % (A0, X2, R))
    twor = w.s([], '2re', '2 e. RR'); twor = w.s([twor], 'a1i', '( %s -> 2 e. RR )' % A0)
    two0l = w.s([], '0le2', '0 <_ 2'); two0l = w.s([two0l], 'a1i', '( %s -> 0 <_ 2 )' % A0)
    d2r = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), drp], 'rpmulcld', '( %s -> ( 2 x. D ) e. RR+ )' % A0)
    rn = w.s([nrp], 'rpreccld', '( %s -> ( 1 / N ) e. RR+ )' % A0)
    e6 = w.s([w.s([d2r], 'rpred', '( %s -> ( 2 x. D ) e. RR )' % A0), w.s([d2r], 'rpge0d', '( %s -> 0 <_ ( 2 x. D ) )' % A0),
              w.s([rn], 'rpred', '( %s -> ( 1 / N ) e. RR )' % A0), w.s([rn], 'rpge0d', '( %s -> 0 <_ ( 1 / N ) )' % A0), ec], 'mulcxpd',
             '( %s -> ( %s ^c E ) = ( ( ( 2 x. D ) ^c E ) x. ( ( 1 / N ) ^c E ) ) )' % (A0, R))
    e7 = w.s([twor, two0l, w.s([drp], 'rpred', '( %s -> D e. RR )' % A0), w.s([drp], 'rpge0d', '( %s -> 0 <_ D )' % A0), ec], 'mulcxpd',
             '( %s -> ( ( 2 x. D ) ^c E ) = ( ( 2 ^c E ) x. ( D ^c E ) ) )' % A0)
    e8 = w.s([nrp, ec], 'cxprecd', '( %s -> ( ( 1 / N ) ^c E ) = ( 1 / ( N ^c E ) ) )' % A0)
    e9 = w.s([nc, w.s([nrp], 'rpne0d', '( %s -> N =/= 0 )' % A0), ec], 'cxpnegd', '( %s -> ( N ^c -u E ) = ( 1 / ( N ^c E ) ) )' % A0)
    e89 = w.s([e8, e9], 'eqtr4d', '( %s -> ( ( 1 / N ) ^c E ) = ( N ^c -u E ) )' % A0)
    TGT = '( ( ( 2 ^c E ) x. ( D ^c E ) ) x. ( N ^c -u E ) )'
    e79 = w.s([e7, e89], 'oveq12d', '( %s -> ( ( ( 2 x. D ) ^c E ) x. ( ( 1 / N ) ^c E ) ) = %s )' % (A0, TGT))
    ch = w.s([w.s([e6a, e6], 'eqtrd', '( %s -> ( ( 1 / %s ) ^c E ) = ( ( ( 2 x. D ) ^c E ) x. ( ( 1 / N ) ^c E ) ) )' % (A0, X2)), e79], 'eqtrd',
             '( %s -> ( ( 1 / %s ) ^c E ) = %s )' % (A0, X2, TGT))
    eq = w.s([w.s([e1, e2], 'eqtr4d', '( %s -> ( %s ^c -u E ) = ( ( 1 / %s ) ^c E ) )' % (A0, X2, X2)), ch], 'eqtrd', '( %s -> ( %s ^c -u E ) = %s )' % (A0, X2, TGT))
    w.qed([le1, eq], 'breqtrd', '( %s -> ( %s ^c -u E ) <_ %s )' % (A0, F, TGT))
    run7b(w)


if __name__ == '__main__' and (not only or 'dconvtm' in only):
    # ---------------------------------------------------------------- dconvtm
    w = W('dconvtm', 'One term of the difference in ~ dconvdif : the tail of the ` B ` -series beyond ` N / D ` times ` D ^c -u Re Z ` '
          'is at most ` ( 2 ^c ( Re Z - 1 ) C / ( Re Z - 1 ) ) N ^c -u ( Re Z - 1 ) / D ` .')
    A0 = '( %s /\\ ( N e. NN /\\ D e. ( 1 ... N ) ) )' % BZ
    bz = w.s([], 'simpl', '( %s -> %s )' % (A0, BZ))
    cfb = w.s([], 'simpll', '( %s -> %s )' % (A0, CFBB))
    zp = w.s([], 'simplr', '( %s -> %s )' % (A0, ZP1))
    nd = w.s([], 'simpr', '( %s -> ( N e. NN /\\ D e. ( 1 ... N ) ) )' % A0)
    nn = w.s([], 'simprl', '( %s -> N e. NN )' % A0)
    dm = w.s([], 'simprr', '( %s -> D e. ( 1 ... N ) )' % A0)
    z = zctx(w, A0, zp)
    c = cfbctx(w, A0, cfb)
    c0 = w.s([cfb, w.inst('cfb0')], 'syl', '( %s -> 0 <_ C )' % A0)
    dnn = w.s([dm, w.inst('elfznn')], 'syl', '( %s -> D e. NN )' % A0)
    dle = w.s([dm, w.inst('elfzle2')], 'syl', '( %s -> D <_ N )' % A0)
    nrp = w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % A0)
    drp = w.s([dnn], 'nnrpd', '( %s -> D e. RR+ )' % A0)
    nr = w.s([nrp], 'rpred', '( %s -> N e. RR )' % A0)
    X = '( N / D )'
    xrp = w.s([nrp, drp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, X))
    xr = w.s([xrp], 'rpred', '( %s -> %s e. RR )' % (A0, X))
    x1 = w.s([drp, nr, dle, w.inst('divge1')], 'syl3anc', '( %s -> 1 <_ %s )' % (A0, X))
    F = FLD
    fnn = w.s([xr, x1, w.inst('flge1nn')], 'syl2anc', '( %s -> %s e. NN )' % (A0, F))
    fle = w.s([nr, drp, w.inst('fldivle')], 'syl2anc', '( %s -> %s <_ %s )' % (A0, F, X))
    xle = w.s([w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0), dnn, w.inst('nn0ledivnn')], 'syl2anc', '( %s -> %s <_ N )' % (A0, X))
    fr = w.s([fnn], 'nnred', '( %s -> %s e. RR )' % (A0, F))
    fleN = w.s([fr, xr, nr, fle, xle], 'letrd', '( %s -> %s <_ N )' % (A0, F))
    nuz = w.s([w.s([w.s([fnn], 'nnzd', '( %s -> %s e. ZZ )' % (A0, F)), w.s([nn], 'nnzd', '( %s -> N e. ZZ )' % A0), fleN], '3jca',
                   '( %s -> ( %s e. ZZ /\\ N e. ZZ /\\ %s <_ N ) )' % (A0, F, F)), w.inst('eluz2')], 'sylibr', '( %s -> N e. ( ZZ>= ` %s ) )' % (A0, F))
    blk = w.s([w.s([bz, w.s([fnn, nuz], 'jca', '( %s -> ( %s e. NN /\\ N e. ( ZZ>= ` %s ) ) )' % (A0, F, F))], 'jca',
                   '( %s -> ( %s /\\ ( %s e. NN /\\ N e. ( ZZ>= ` %s ) ) ) )' % (A0, BZ, F, F)), w.inst('dconvblk')], 'syl',
              '( %s -> ( abs ` ( %s - %s ) ) <_ ( C x. ( ( %s ^c ( 1 - %s ) ) / %s ) ) )' % (A0, PS('B', 'N'), PS('B', F), F, RZ, E1))
    pf = ps_cl(w, A0, F, c['bf'], z['zc'])
    pn = ps_cl(w, A0, 'N', c['bf'], z['zc'])
    S = '( abs ` ( %s - %s ) )' % (PS('B', F), PS('B', 'N'))
    asub = w.s([pf, pn], 'abssubd', '( %s -> %s = ( abs ` ( %s - %s ) ) )' % (A0, S, PS('B', 'N'), PS('B', F)))
    # exponent 1 - Re Z = -u E1
    rzc = w.s([z['rz']], 'recnd', '( %s -> %s e. CC )' % (A0, RZ))
    onec = w.s([], '1cnd', '( %s -> 1 e. CC )' % A0)
    ng = w.s([rzc, onec], 'negsubdi2d', '( %s -> -u %s = ( 1 - %s ) )' % (A0, E1, RZ))
    Fm = '( %s ^c -u %s )' % (F, E1)
    Q = '( 1 / %s )' % E1
    e1c = w.s([z['e1rp']], 'rpcnd', '( %s -> %s e. CC )' % (A0, E1))
    e1n0 = w.s([z['e1rp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, E1))
    fpw = w.s([w.s([ng], 'eqcomd', '( %s -> ( 1 - %s ) = -u %s )' % (A0, RZ, E1))], 'oveq2d', '( %s -> ( %s ^c ( 1 - %s ) ) = %s )' % (A0, F, RZ, Fm))
    frp = w.s([fnn], 'nnrpd', '( %s -> %s e. RR+ )' % (A0, F))
    e1r = z['e1re']
    fmrp = w.s([frp, w.s([e1r], 'renegcld', '( %s -> -u %s e. RR )' % (A0, E1))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, Fm))
    fmc = w.s([fmrp], 'rpcnd', '( %s -> %s e. CC )' % (A0, Fm))
    dv1 = w.s([w.s([fpw], 'oveq1d', '( %s -> ( ( %s ^c ( 1 - %s ) ) / %s ) = ( %s / %s ) )' % (A0, F, RZ, E1, Fm, E1)),
               w.s([fmc, e1c, e1n0], 'divrecd', '( %s -> ( %s / %s ) = ( %s x. %s ) )' % (A0, Fm, E1, Fm, Q))], 'eqtrd',
              '( %s -> ( ( %s ^c ( 1 - %s ) ) / %s ) = ( %s x. %s ) )' % (A0, F, RZ, E1, Fm, Q))
    h1r = w.s([dv1], 'oveq2d', '( %s -> ( C x. ( ( %s ^c ( 1 - %s ) ) / %s ) ) = ( C x. ( %s x. %s ) ) )' % (A0, F, RZ, E1, Fm, Q))
    h1 = w.s([w.s([asub, blk], 'eqbrtrd', '( %s -> %s <_ ( C x. ( ( %s ^c ( 1 - %s ) ) / %s ) ) )' % (A0, S, F, RZ, E1)), h1r], 'breqtrd',
             '( %s -> %s <_ ( C x. ( %s x. %s ) ) )' % (A0, S, Fm, Q))
    T2 = '( 2 ^c %s )' % E1
    De = '( D ^c %s )' % E1
    Nm = '( N ^c -u %s )' % E1
    P = '( D ^c -u %s )' % RZ
    iD = '( 1 / D )'
    h2 = w.s([w.s([nd, z['e1rp']], 'jca', '( %s -> ( ( N e. NN /\\ D e. ( 1 ... N ) ) /\\ %s e. RR+ ) )' % (A0, E1)), w.inst('dconvfl')], 'syl',
             '( %s -> %s <_ ( ( %s x. %s ) x. %s ) )' % (A0, Fm, T2, De, Nm))
    # D ^c E1 x. D ^c -u RZ = 1 / D
    dc = w.s([drp], 'rpcnd', '( %s -> D e. CC )' % A0)
    dn0 = w.s([drp], 'rpne0d', '( %s -> D =/= 0 )' % A0)
    ca = w.s([dc, dn0, e1c, w.s([rzc], 'negcld', '( %s -> -u %s e. CC )' % (A0, RZ))], 'cxpaddd',
             '( %s -> ( D ^c ( %s + -u %s ) ) = ( %s x. %s ) )' % (A0, E1, RZ, De, P))
    ex = lin.lineq(w, A0, '( %s + -u %s )' % (E1, RZ), '-u 1', leaves={RZ: z['rz']})
    dm1 = w.s([ex], 'oveq2d', '( %s -> ( D ^c ( %s + -u %s ) ) = ( D ^c -u 1 ) )' % (A0, E1, RZ))
    dn1 = w.s([dc, dn0, onec], 'cxpnegd', '( %s -> ( D ^c -u 1 ) = ( 1 / ( D ^c 1 ) ) )' % A0)
    d1 = w.s([w.s([dc], 'cxp1d', '( %s -> ( D ^c 1 ) = D )' % A0)], 'oveq2d', '( %s -> ( 1 / ( D ^c 1 ) ) = %s )' % (A0, iD))
    dp = w.s([w.s([w.s([ca], 'eqcomd', '( %s -> ( %s x. %s ) = ( D ^c ( %s + -u %s ) ) )' % (A0, De, P, E1, RZ)), dm1], 'eqtrd',
                  '( %s -> ( %s x. %s ) = ( D ^c -u 1 ) )' % (A0, De, P)), w.s([dn1, d1], 'eqtrd', '( %s -> ( D ^c -u 1 ) = %s )' % (A0, iD))],
             'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (A0, De, P, iD))
    # real facts
    rz = z['rz']
    pr = w.s([drp, w.s([rz], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, P))
    t2 = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), e1r], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, T2))
    der = w.s([drp, e1r], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, De))
    nmr = w.s([nrp, w.s([e1r], 'renegcld', '( %s -> -u %s e. RR )' % (A0, E1))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, Nm))
    qr = w.s([z['e1rp']], 'rpreccld', '( %s -> %s e. RR+ )' % (A0, Q))
    idr = w.s([drp], 'rpreccld', '( %s -> %s e. RR+ )' % (A0, iD))
    sr = w.s([w.s([pf, pn], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, PS('B', F), PS('B', 'N')))], 'abscld', '( %s -> %s e. RR )' % (A0, S))
    L = {S: sr, P: pr, 'C': c['cr'], Fm: fmrp, Q: qr, T2: t2, De: der, Nm: nmr, iD: idr}
    import cl
    clo = cl.Closure(w, A0, L)
    for k in (P, Fm, Q, T2, De, Nm, iD, S):
        clo.atom(k)
    clo.have('C', 'ge0', c0)
    A = w.s([sr, clo.mem('( C x. ( %s x. %s ) )' % (Fm, Q), 'RR'), w.s([pr], 'rpred', '( %s -> %s e. RR )' % (A0, P)), w.s([pr], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, P)), h1],
            'lemul1ad', '( %s -> ( %s x. %s ) <_ ( ( C x. ( %s x. %s ) ) x. %s ) )' % (A0, S, P, Fm, Q, P))
    CQP = '( ( C x. %s ) x. %s )' % (Q, P)
    B = w.s([w.s([fmrp], 'rpred', '( %s -> %s e. RR )' % (A0, Fm)), clo.mem('( ( %s x. %s ) x. %s )' % (T2, De, Nm), 'RR'), clo.mem(CQP, 'RR'), clo.ge0(CQP), h2],
            'lemul1ad', '( %s -> ( %s x. %s ) <_ ( ( ( %s x. %s ) x. %s ) x. %s ) )' % (A0, Fm, CQP, T2, De, Nm, CQP))
    K1 = '( ( %s x. C ) x. %s )' % (T2, Q)
    E = w.s([w.s([dp], 'oveq2d', '( %s -> ( %s x. ( %s x. %s ) ) = ( %s x. %s ) )' % (A0, Nm, De, P, Nm, iD))], 'oveq2d',
            '( %s -> ( %s x. ( %s x. ( %s x. %s ) ) ) = ( %s x. ( %s x. %s ) ) )' % (A0, K1, Nm, De, P, K1, Nm, iD))
    G = lin.linarith(w, A0, [A, B, E], '( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (S, P, K1, Nm, iD), closure=clo, products=True)
    t2c = w.s([t2], 'rpcnd', '( %s -> %s e. CC )' % (A0, T2))
    k1 = w.s([w.s([t2c, w.s([c['cr']], 'recnd', '( %s -> C e. CC )' % A0)], 'mulcld', '( %s -> ( %s x. C ) e. CC )' % (A0, T2)), e1c, e1n0], 'divrecd',
             '( %s -> %s = %s )' % (A0, DK, K1))
    k2 = w.s([w.s([nmr], 'rpcnd', '( %s -> %s e. CC )' % (A0, Nm)), dc, dn0], 'divrecd', '( %s -> ( %s / D ) = ( %s x. %s ) )' % (A0, Nm, Nm, iD))
    k12 = w.s([k1, k2], 'oveq12d', '( %s -> ( %s x. ( %s / D ) ) = ( %s x. ( %s x. %s ) ) )' % (A0, DK, Nm, K1, Nm, iD))
    w.qed([G, k12], 'breqtrrd', '( %s -> ( %s x. %s ) <_ ( %s x. ( %s / D ) ) )' % (A0, S, P, DK, Nm))
    run7b(w)
