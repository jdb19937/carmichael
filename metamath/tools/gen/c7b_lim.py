"""C7b section 1, the limits: cxpnegcvg, cxplogcvg, dconvmaj."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
import congr as _cg
lin.FASTPATH = True


def nnrpss(w):
    return w.s([w.s([], 'nnrp', '( x e. NN -> x e. RR+ )')], 'ssriv', 'NN C_ RR+')


def rlim2clim(w, ph, R, body, rl, clo_cc):
    """from rl: ( ph -> ( n e. RR+ |-> body ) ~~>r R ) and clo_cc: ( ( ph /\\ n e. NN ) -> body e. CC )
    derive ( ph -> ( n e. NN |-> body ) ~~> R )"""
    F = '( n e. RR+ |-> %s )' % body
    G = '( n e. NN |-> %s )' % body
    r1 = w.s([rl, w.inst('rlimres')], 'syl', '( %s -> ( %s |` NN ) ~~>r %s )' % (ph, F, R))
    rs = w.s([nnrpss(w), w.inst('resmpt')], 'ax-mp', '( %s |` NN ) = %s' % (F, G))
    r2 = w.s([w.s([rs], 'a1i', '( %s -> ( %s |` NN ) = %s )' % (ph, F, G)), r1], 'eqbrtrrd', '( %s -> %s ~~>r %s )' % (ph, G, R))
    gf = w.s([clo_cc, w.s([], 'eqid', '%s = %s' % (G, G))], 'fmptd', '( %s -> %s : NN --> CC )' % (ph, G))
    bi = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ph), gf], 'rlimclim', '( %s -> ( %s ~~>r %s <-> %s ~~> %s ) )' % (ph, G, R, G, R))
    return w.s([r2, bi], 'mpbid', '( %s -> %s ~~> %s )' % (ph, G, R))


if __name__ == '__main__' and (not only or 'cxpnegcvg' in only):
    w = W('cxpnegcvg', 'The sequence ` n ^c -u E ` tends to zero for ` E > 0 ` .')
    ph = 'E e. RR+'
    erp = w.s([], 'id', '( %s -> E e. RR+ )' % ph)
    ec = w.s([erp], 'rpcnd', '( %s -> E e. CC )' % ph)
    r0 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % ph), w.inst('divrcnv')], 'syl', '( %s -> ( n e. RR+ |-> ( 1 / n ) ) ~~>r 0 )' % ph)
    An = '( %s /\\ n e. RR+ )' % ph
    nrp = w.s([], 'simpr', '( %s -> n e. RR+ )' % An)
    rc = w.s([nrp], 'rpreccld', '( %s -> ( 1 / n ) e. RR+ )' % An)
    r1 = w.s([rc, r0, erp], 'rlimcxp', '( %s -> ( n e. RR+ |-> ( ( 1 / n ) ^c E ) ) ~~>r 0 )' % ph)
    ecn = w.s([ec], 'adantr', '( %s -> E e. CC )' % An)
    a = w.s([nrp, ecn], 'cxprecd', '( %s -> ( ( 1 / n ) ^c E ) = ( 1 / ( n ^c E ) ) )' % An)
    b = w.s([w.s([nrp], 'rpcnd', '( %s -> n e. CC )' % An), w.s([nrp], 'rpne0d', '( %s -> n =/= 0 )' % An), ecn], 'cxpnegd',
            '( %s -> ( n ^c -u E ) = ( 1 / ( n ^c E ) ) )' % An)
    eq = w.s([w.s([a, b], 'eqtr4d', '( %s -> ( ( 1 / n ) ^c E ) = ( n ^c -u E ) )' % An)], 'mpteq2dva',
             '( %s -> ( n e. RR+ |-> ( ( 1 / n ) ^c E ) ) = ( n e. RR+ |-> ( n ^c -u E ) ) )' % ph)
    r2 = w.s([eq, r1], 'eqbrtrrd', '( %s -> ( n e. RR+ |-> ( n ^c -u E ) ) ~~>r 0 )' % ph)
    Bn = '( %s /\\ n e. NN )' % ph
    cc = cxpz(w, Bn, 'n', w.s([], 'simpr', '( %s -> n e. NN )' % Bn), w.s([ec], 'adantr', '( %s -> E e. CC )' % Bn), Z='E')
    st = rlim2clim(w, ph, '0', '( n ^c -u E )', r2, cc)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    run7b(w)

if __name__ == '__main__' and (not only or 'cxplogcvg' in only):
    w = W('cxplogcvg', 'The sequence ` log n n ^c -u E ` tends to zero for ` E > 0 ` .')
    ph = 'E e. RR+'
    erp = w.s([], 'id', '( %s -> E e. RR+ )' % ph)
    ec = w.s([erp], 'rpcnd', '( %s -> E e. CC )' % ph)
    r1 = w.s([erp, w.inst('cxploglim')], 'syl', '( %s -> ( n e. RR+ |-> ( ( log ` n ) / ( n ^c E ) ) ) ~~>r 0 )' % ph)
    An = '( %s /\\ n e. RR+ )' % ph
    nrp = w.s([], 'simpr', '( %s -> n e. RR+ )' % An)
    ecn = w.s([ec], 'adantr', '( %s -> E e. CC )' % An)
    nc = w.s([nrp], 'rpcnd', '( %s -> n e. CC )' % An)
    n0 = w.s([nrp], 'rpne0d', '( %s -> n =/= 0 )' % An)
    lc = w.s([w.s([nrp], 'relogcld', '( %s -> ( log ` n ) e. RR )' % An)], 'recnd', '( %s -> ( log ` n ) e. CC )' % An)
    pe = w.s([nc, ecn], 'cxpcld', '( %s -> ( n ^c E ) e. CC )' % An)
    pe0 = w.s([nc, n0, ecn], 'cxpne0d', '( %s -> ( n ^c E ) =/= 0 )' % An)
    a = w.s([lc, pe, pe0], 'divrecd', '( %s -> ( ( log ` n ) / ( n ^c E ) ) = ( ( log ` n ) x. ( 1 / ( n ^c E ) ) ) )' % An)
    b = w.s([nc, n0, ecn], 'cxpnegd', '( %s -> ( n ^c -u E ) = ( 1 / ( n ^c E ) ) )' % An)
    b2 = w.s([b], 'oveq2d', '( %s -> ( ( log ` n ) x. ( n ^c -u E ) ) = ( ( log ` n ) x. ( 1 / ( n ^c E ) ) ) )' % An)
    eq = w.s([w.s([a, b2], 'eqtr4d', '( %s -> ( ( log ` n ) / ( n ^c E ) ) = ( ( log ` n ) x. ( n ^c -u E ) ) )' % An)], 'mpteq2dva',
             '( %s -> ( n e. RR+ |-> ( ( log ` n ) / ( n ^c E ) ) ) = ( n e. RR+ |-> ( ( log ` n ) x. ( n ^c -u E ) ) ) )' % ph)
    r2 = w.s([eq, r1], 'eqbrtrrd', '( %s -> ( n e. RR+ |-> ( ( log ` n ) x. ( n ^c -u E ) ) ) ~~>r 0 )' % ph)
    Bn = '( %s /\\ n e. NN )' % ph
    nn = w.s([], 'simpr', '( %s -> n e. NN )' % Bn)
    cc = cxpz(w, Bn, 'n', nn, w.s([ec], 'adantr', '( %s -> E e. CC )' % Bn), Z='E')
    lcn = w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % Bn)], 'relogcld', '( %s -> ( log ` n ) e. RR )' % Bn)], 'recnd', '( %s -> ( log ` n ) e. CC )' % Bn)
    cc2 = w.s([lcn, cc], 'mulcld', '( %s -> ( ( log ` n ) x. ( n ^c -u E ) ) e. CC )' % Bn)
    st = rlim2clim(w, ph, '0', '( ( log ` n ) x. ( n ^c -u E ) )', r2, cc2)
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    run7b(w)


def mex(w, ph, M):
    """( ph -> M e. _V ) for a mapping over NN"""
    return w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ph)], 'mptexd', '( %s -> %s e. _V )' % (ph, M))


def val(w, ante, body, k, mem, exs, x='n', dom='NN'):
    st, v = _cg.mptval(w, ante, x, dom, body, k, mem, exs=exs, gen=w.g)
    return st, v


if __name__ == '__main__' and (not only or 'dconvmaj' in only):
    w = W('dconvmaj', 'The majorant ` D n ^c -u E ( log n + K ) ` of ~ dconvdifb tends to zero.')
    ph = '( ( D e. RR /\\ K e. RR ) /\\ E e. RR+ )'
    dr = w.s([], 'simpll', '( %s -> D e. RR )' % ph)
    kr = w.s([], 'simplr', '( %s -> K e. RR )' % ph)
    erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % ph)
    dc = w.s([dr], 'recnd', '( %s -> D e. CC )' % ph)
    kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % ph)
    ec = w.s([erp], 'rpcnd', '( %s -> E e. CC )' % ph)
    P = '( n ^c -u E )'
    LG = '( ( log ` n ) x. %s )' % P
    F0 = '( n e. NN |-> %s )' % P
    F1 = '( n e. NN |-> %s )' % LG
    G1 = '( n e. NN |-> ( K x. %s ) )' % P
    HB = '( %s x. ( ( log ` n ) + K ) )' % P
    H = '( n e. NN |-> %s )' % HB
    MJB = '( D x. %s )' % HB
    M = '( n e. NN |-> %s )' % MJB
    c0 = w.s([erp, w.inst('cxpnegcvg')], 'syl', '( %s -> %s ~~> 0 )' % (ph, F0))
    c1 = w.s([erp, w.inst('cxplogcvg')], 'syl', '( %s -> %s ~~> 0 )' % (ph, F1))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ph)
    Ak = '( %s /\\ k e. NN )' % ph
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    kcc = w.s([krp], 'rpcnd', '( %s -> k e. CC )' % Ak)
    eck = w.s([ec], 'adantr', '( %s -> E e. CC )' % Ak)
    pk = w.s([kcc, w.s([eck], 'negcld', '( %s -> -u E e. CC )' % Ak)], 'cxpcld', '( %s -> ( k ^c -u E ) e. CC )' % Ak)
    lk = w.s([w.s([krp], 'relogcld', '( %s -> ( log ` k ) e. RR )' % Ak)], 'recnd', '( %s -> ( log ` k ) e. CC )' % Ak)
    kck = w.s([kc], 'adantr', '( %s -> K e. CC )' % Ak)
    dck = w.s([dc], 'adantr', '( %s -> D e. CC )' % Ak)
    v0, V0 = val(w, Ak, P, 'k', kn, w.s([pk], 'elexd', '( %s -> ( k ^c -u E ) e. _V )' % Ak))
    lkp = w.s([lk, pk], 'mulcld', '( %s -> ( ( log ` k ) x. ( k ^c -u E ) ) e. CC )' % Ak)
    v1, V1 = val(w, Ak, LG, 'k', kn, w.s([lkp], 'elexd', '( %s -> ( ( log ` k ) x. ( k ^c -u E ) ) e. _V )' % Ak))
    kp = w.s([kck, pk], 'mulcld', '( %s -> ( K x. ( k ^c -u E ) ) e. CC )' % Ak)
    vg, VG = val(w, Ak, '( K x. %s )' % P, 'k', kn, w.s([kp], 'elexd', '( %s -> ( K x. ( k ^c -u E ) ) e. _V )' % Ak))
    HK = '( ( k ^c -u E ) x. ( ( log ` k ) + K ) )'
    hk = w.s([pk, w.s([lk, kck], 'addcld', '( %s -> ( ( log ` k ) + K ) e. CC )' % Ak)], 'mulcld', '( %s -> %s e. CC )' % (Ak, HK))
    vh, VH = val(w, Ak, HB, 'k', kn, w.s([hk], 'elexd', '( %s -> %s e. _V )' % (Ak, HK)))
    mk = w.s([dck, hk], 'mulcld', '( %s -> ( D x. %s ) e. CC )' % (Ak, HK))
    vm, VM = val(w, Ak, MJB, 'k', kn, w.s([mk], 'elexd', '( %s -> ( D x. %s ) e. _V )' % (Ak, HK)))
    # G1 ` k = K x. ( F0 ` k )
    g1h = w.s([vg, w.s([v0], 'oveq2d', '( %s -> ( K x. ( %s ` k ) ) = ( K x. ( k ^c -u E ) ) )' % (Ak, F0))], 'eqtr4d',
              '( %s -> ( %s ` k ) = ( K x. ( %s ` k ) ) )' % (Ak, G1, F0))
    f0c = w.s([v0, pk], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, F0))
    cg = w.s([nnuz, one, c0, kc, mex(w, ph, G1), f0c, g1h], 'climmulc2', '( %s -> %s ~~> ( K x. 0 ) )' % (ph, G1))
    # H ` k = ( F1 ` k ) + ( G1 ` k )
    dist = w.s([pk, lk, kck], 'adddid', '( %s -> %s = ( ( ( k ^c -u E ) x. ( log ` k ) ) + ( ( k ^c -u E ) x. K ) ) )' % (Ak, HK))
    c1_ = w.s([pk, lk], 'mulcomd', '( %s -> ( ( k ^c -u E ) x. ( log ` k ) ) = ( ( log ` k ) x. ( k ^c -u E ) ) )' % Ak)
    c2_ = w.s([pk, kck], 'mulcomd', '( %s -> ( ( k ^c -u E ) x. K ) = ( K x. ( k ^c -u E ) ) )' % Ak)
    dist2 = w.s([dist, w.s([c1_, c2_], 'oveq12d', '( %s -> ( ( ( k ^c -u E ) x. ( log ` k ) ) + ( ( k ^c -u E ) x. K ) ) = ( ( ( log ` k ) x. ( k ^c -u E ) ) + ( K x. ( k ^c -u E ) ) ) )' % Ak)],
                'eqtrd', '( %s -> %s = ( ( ( log ` k ) x. ( k ^c -u E ) ) + ( K x. ( k ^c -u E ) ) ) )' % (Ak, HK))
    fg = w.s([v1, vg], 'oveq12d', '( %s -> ( ( %s ` k ) + ( %s ` k ) ) = ( ( ( log ` k ) x. ( k ^c -u E ) ) + ( K x. ( k ^c -u E ) ) ) )' % (Ak, F1, G1))
    hh = w.s([w.s([vh, dist2], 'eqtrd', '( %s -> ( %s ` k ) = ( ( ( log ` k ) x. ( k ^c -u E ) ) + ( K x. ( k ^c -u E ) ) ) )' % (Ak, H)), fg], 'eqtr4d',
             '( %s -> ( %s ` k ) = ( ( %s ` k ) + ( %s ` k ) ) )' % (Ak, H, F1, G1))
    f1c = w.s([v1, lkp], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, F1))
    g1c = w.s([vg, kp], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, G1))
    ch = w.s([nnuz, one, c1, mex(w, ph, H), cg, f1c, g1c, hh], 'climadd', '( %s -> %s ~~> ( 0 + ( K x. 0 ) ) )' % (ph, H))
    mh = w.s([vm, w.s([vh], 'oveq2d', '( %s -> ( D x. ( %s ` k ) ) = ( D x. %s ) )' % (Ak, H, HK))], 'eqtr4d', '( %s -> ( %s ` k ) = ( D x. ( %s ` k ) ) )' % (Ak, M, H))
    hc = w.s([vh, hk], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, H))
    cm = w.s([nnuz, one, ch, dc, mex(w, ph, M), hc, mh], 'climmulc2', '( %s -> %s ~~> ( D x. ( 0 + ( K x. 0 ) ) ) )' % (ph, M))
    z1 = w.s([kc], 'mul01d', '( %s -> ( K x. 0 ) = 0 )' % ph)
    z2 = w.s([z1], 'oveq2d', '( %s -> ( 0 + ( K x. 0 ) ) = ( 0 + 0 ) )' % ph)
    z3 = w.s([z2, w.s([w.s([], '00id', '( 0 + 0 ) = 0')], 'a1i', '( %s -> ( 0 + 0 ) = 0 )' % ph)], 'eqtrd', '( %s -> ( 0 + ( K x. 0 ) ) = 0 )' % ph)
    z4 = w.s([w.s([z3], 'oveq2d', '( %s -> ( D x. ( 0 + ( K x. 0 ) ) ) = ( D x. 0 ) )' % ph), w.s([dc], 'mul01d', '( %s -> ( D x. 0 ) = 0 )' % ph)], 'eqtrd',
             '( %s -> ( D x. ( 0 + ( K x. 0 ) ) ) = 0 )' % ph)
    w.qed([cm, z4], 'breqtrd', '( %s -> %s ~~> 0 )' % (ph, M))
    run7b(w)
