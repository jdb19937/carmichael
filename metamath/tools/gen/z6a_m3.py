"""Z6a (block D): the majorants of Gamma ( w ) Y ^ -w (z6gyr, z6gyl, z6gyline)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_mlib import *

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def absy(w, A, yrp, W, wc):
    """( A -> ( abs ` ( Y ^c -u W ) ) = ( Y ^c -u ( Re ` W ) ) ) and the value's CC step"""
    s = mkst(w, A)
    nw = s([wc], 'negcld', '-u %s e. CC' % W)
    a = s([yrp, nw, w.inst('abscxp')], 'syl2anc', '( abs ` ( Y ^c -u %s ) ) = ( Y ^c ( Re ` -u %s ) )' % (W, W))
    b = s([s([wc], 'renegd', '( Re ` -u %s ) = -u ( Re ` %s )' % (W, W))], 'oveq2d', '( Y ^c ( Re ` -u %s ) ) = ( Y ^c -u ( Re ` %s ) )' % (W, W))
    yc = s([s([yrp], 'rpcnd', 'Y e. CC'), nw], 'cxpcld', '( Y ^c -u %s ) e. CC' % W)
    return s([a, b], 'eqtrd', '( abs ` ( Y ^c -u %s ) ) = ( Y ^c -u ( Re ` %s ) )' % (W, W)), yc


def comb(w, A, GW, YW, E, P, gc, yc, hg, hy, er, pr):
    """( A -> ( abs ` ( GW x. YW ) ) <_ ( ( ; 6 4 x. P ) x. E ) ) from hg: |GW| <_ ( ; 6 4 x. E ), hy: |YW| <_ P"""
    s = mkst(w, A)
    aG = '( abs ` %s )' % GW; aY = '( abs ` %s )' % YW
    am = s([gc, yc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (GW, YW, aG, aY))
    r64 = w.s([num.real(w, '; 6 4')], 'a1i', '( %s -> ; 6 4 e. RR )' % A)
    e64 = s([r64, er], 'remulcld', '( ; 6 4 x. %s ) e. RR' % E)
    l = s([s([gc], 'abscld', '%s e. RR' % aG), e64, s([yc], 'abscld', '%s e. RR' % aY), pr, s([gc], 'absge0d', '0 <_ %s' % aG), s([yc], 'absge0d', '0 <_ %s' % aY), hg, hy],
          'lemul12ad', '( %s x. %s ) <_ ( ( ; 6 4 x. %s ) x. %s )' % (aG, aY, E, P))
    m = s([s([r64], 'recnd', '; 6 4 e. CC'), s([er], 'recnd', '%s e. CC' % E), s([pr], 'recnd', '%s e. CC' % P)], 'mul32d',
          '( ( ; 6 4 x. %s ) x. %s ) = ( ( ; 6 4 x. %s ) x. %s )' % (E, P, P, E))
    return s([s([am, l], 'eqbrtrd', '( abs ` ( %s x. %s ) ) <_ ( ( ; 6 4 x. %s ) x. %s )' % (GW, YW, E, P)), m], 'breqtrd',
             '( abs ` ( %s x. %s ) ) <_ ( ( ; 6 4 x. %s ) x. %s )' % (GW, YW, P, E))


def e4r(w, A, wc):
    s = mkst(w, A)
    AI = '( abs ` ( Im ` W ) )'
    air = s([s([s([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')], 'abscld', '%s e. RR' % AI)
    cl = Closure(w, A, {AI: ('RR', air)})
    return s([cl.mem('2', 'RR+'), cl.mem('-u ( %s / 4 )' % AI, 'RR')], 'rpcxpcld', '%s e. RR+' % E4(AI))


# ---------------------------------------------------------------- z6gyr
def z6gyr():
    w = W('z6gyr', 'The majorant of ` _G ( W ) Y ^ -u W ` on ` 1 / 2 <_ Re W <_ 3 ` : ~ z6mg64 and ` | Y ^ -u W | = Y ^ -u Re W <_ Y ^ -u ( 1 / 2 ) + Y ^ -u 3 ` ( ~ z6mycx ).')
    A = split_imp(STATEMENTS['z6gyr'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpl', '( %s -> Y e. RR+ )' % A)
    wc = w.s([], 'simprl', '( %s -> W e. CC )' % A)
    wcnd = w.s([], 'simpr', '( %s -> ( W e. CC /\\ ( ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 3 ) ) )' % A)
    lo = w.s([], 'simprrl', '( %s -> ( 1 / 2 ) <_ ( Re ` W ) )' % A)
    hi = w.s([], 'simprrr', '( %s -> ( Re ` W ) <_ 3 )' % A)
    AI = '( abs ` ( Im ` W ) )'
    g64 = s([wcnd, w.inst('z6mg64')], 'syl', '( abs ` ( _G ` W ) ) <_ ( ; 6 4 x. %s )' % E4(AI))
    ay, yc = absy(w, A, yrp, 'W', wc)
    rw = s([wc], 'recld', '( Re ` W ) e. RR')
    cl = Closure(w, A, {'( Re ` W )': ('RR', rw)})
    X = '-u ( Re ` W )'
    l1 = linarith(w, A, [hi], '-u 3 <_ %s' % X, closure=cl)
    l2 = linarith(w, A, [lo], '%s <_ -u ( 1 / 2 )' % X, closure=cl)
    P = '( ( Y ^c -u ( 1 / 2 ) ) + ( Y ^c -u 3 ) )'
    cx = s([yrp, s([cl.mem('-u 3', 'RR'), cl.mem('-u ( 1 / 2 )', 'RR'), cl.mem(X, 'RR')], '3jca', '( -u 3 e. RR /\\ -u ( 1 / 2 ) e. RR /\\ %s e. RR )' % X),
            s([l1, l2], 'jca', '( -u 3 <_ %s /\\ %s <_ -u ( 1 / 2 ) )' % (X, X)), w.inst('z6mycx')], 'syl3anc', '( Y ^c %s ) <_ %s' % (X, P))
    hy = s([ay, cx], 'eqbrtrd', '( abs ` ( Y ^c -u W ) ) <_ %s' % P)
    pr = s([s([s([yrp, cl.mem('-u ( 1 / 2 )', 'RR')], 'rpcxpcld', '( Y ^c -u ( 1 / 2 ) ) e. RR+'), s([yrp, cl.mem('-u 3', 'RR')], 'rpcxpcld', '( Y ^c -u 3 ) e. RR+')],
            'rpaddcld', '%s e. RR+' % P)], 'rpred', '%s e. RR' % P)
    wd = s([wc, linarith(w, A, [lo], '0 < ( Re ` W )', closure=cl), w.inst('zrenn')], 'syl2anc', 'W e. %s' % DG)
    gc = s([wd, w.inst('gamcl')], 'syl', '( _G ` W ) e. CC')
    fin = comb(w, A, '( _G ` W )', '( Y ^c -u W )', E4(AI), P, gc, yc, g64, hy, s([e4r(w, A, wc)], 'rpred', '%s e. RR' % E4(AI)), pr)
    toqed(w, fin, 'z6gyr')
    return w


# ---------------------------------------------------------------- z6gyl
def z6gyl():
    w = W('z6gyl', 'The majorant of ` _G ( W ) Y ^ -u W ` on the strip ` -u K - 1 / 2 <_ Re W <_ 1 / 2 - K ` , ` | Im W | >_ 1 ` : ~ z6mgstr and '
          '` | Y ^ -u W | <_ Y ^ ( K + 1 / 2 ) + Y ^ ( K - 1 / 2 ) ` ( ~ z6mycx ).')
    A = split_imp(STATEMENTS['z6gyl'])[0]
    s = mkst(w, A)
    yrp = w.s([], 'simpll', '( %s -> Y e. RR+ )' % A)
    kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % A)
    WC = split_imp(STATEMENTS['z6mgstr'])[0].split(' /\\ ', 1)[1][:-2]
    wcnd = w.s([], 'simpr', '( %s -> %s )' % (A, WC))
    wc = w.s([], 'simprl', '( %s -> W e. CC )' % A)
    rng = s([wcnd], 'simprd', '( ( ( -u K - ( 1 / 2 ) ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ ( ( 1 / 2 ) - K ) ) /\\ 1 <_ ( abs ` ( Im ` W ) ) )')
    lo = s([rng], 'simplld', '( -u K - ( 1 / 2 ) ) <_ ( Re ` W )')
    hi = s([rng], 'simplrd', '( Re ` W ) <_ ( ( 1 / 2 ) - K )')
    AI = '( abs ` ( Im ` W ) )'
    gs = s([s([kn, wcnd], 'jca', split_imp(STATEMENTS['z6mgstr'])[0]), w.inst('z6mgstr')], 'syl', '( abs ` ( _G ` W ) ) <_ ( ; 6 4 x. %s )' % E4(AI))
    ay, yc = absy(w, A, yrp, 'W', wc)
    rw = s([wc], 'recld', '( Re ` W ) e. RR')
    cl = Closure(w, A, {'( Re ` W )': ('RR', rw), 'K': ('RR', s([kn], 'nn0red', 'K e. RR'))})
    X = '-u ( Re ` W )'
    KL, KH = '( K - ( 1 / 2 ) )', '( K + ( 1 / 2 ) )'
    l1 = linarith(w, A, [hi], '%s <_ %s' % (KL, X), closure=cl)
    l2 = linarith(w, A, [lo], '%s <_ %s' % (X, KH), closure=cl)
    P = '( ( Y ^c %s ) + ( Y ^c %s ) )' % (KH, KL)
    cx = s([yrp, s([cl.mem(KL, 'RR'), cl.mem(KH, 'RR'), cl.mem(X, 'RR')], '3jca', '( %s e. RR /\\ %s e. RR /\\ %s e. RR )' % (KL, KH, X)),
            s([l1, l2], 'jca', '( %s <_ %s /\\ %s <_ %s )' % (KL, X, X, KH)), w.inst('z6mycx')], 'syl3anc', '( Y ^c %s ) <_ %s' % (X, P))
    hy = s([ay, cx], 'eqbrtrd', '( abs ` ( Y ^c -u W ) ) <_ %s' % P)
    pr = s([s([s([yrp, cl.mem(KH, 'RR')], 'rpcxpcld', '( Y ^c %s ) e. RR+' % KH), s([yrp, cl.mem(KL, 'RR')], 'rpcxpcld', '( Y ^c %s ) e. RR+' % KL)],
            'rpaddcld', '%s e. RR+' % P)], 'rpred', '%s e. RR' % P)
    gc = s([gs, w.inst('z6absle')], 'syl', '( _G ` W ) e. CC')
    fin = comb(w, A, '( _G ` W )', '( Y ^c -u W )', E4(AI), P, gc, yc, gs, hy, s([e4r(w, A, wc)], 'rpred', '%s e. RR' % E4(AI)), pr)
    toqed(w, fin, 'z6gyl')
    return w


# ---------------------------------------------------------------- z6gyline
def z6gyline():
    w = W('z6gyline', 'On the line ` Re w = -u K - 1 / 2 ` : ` | _G ( w ) Y ^ -u w | <_ ( 2 Y ^ ( K + 1 / 2 ) / K ! ) | _G ( 1 / 2 + i u ) | ` '
          '( ~ z6mgln ; ` | Y ^ -u w | = Y ^ ( K + 1 / 2 ) ` ).')
    A = split_imp(STATEMENTS['z6gyline'])[0]
    s = mkst(w, A)
    H = '( 1 / 2 )'
    yrp = w.s([], 'simpll', '( %s -> Y e. RR+ )' % A)
    kn = w.s([], 'simplr', '( %s -> K e. NN0 )' % A)
    ur = w.s([], 'simpr', '( %s -> U e. RR )' % A)
    L = '( -u K - %s )' % H
    LW = '( %s + ( _i x. U ) )' % L
    HL = '( %s + ( _i x. U ) )' % H
    g = '( abs ` ( _G ` %s ) )' % HL
    F = '( ! ` K )'
    gl = s([s([kn, ur], 'jca', '( K e. NN0 /\\ U e. RR )'), w.inst('z6mgln')], 'syl', '( abs ` ( _G ` %s ) ) <_ ( ( 2 / %s ) x. %s )' % (LW, F, g))
    kr = s([kn], 'nn0red', 'K e. RR')
    cl = Closure(w, A, {'K': ('RR', kr), 'U': ('RR', ur)})
    lr = cl.mem(L, 'RR')
    iuc = s([a1c(w, A, 'ax-icn', '_i e. CC'), s([ur], 'recnd', 'U e. CC')], 'mulcld', '( _i x. U ) e. CC')
    lwc = s([s([lr], 'recnd', '%s e. CC' % L), iuc], 'addcld', '%s e. CC' % LW)
    ay, yc = absy(w, A, yrp, LW, lwc)
    KH = '( K + %s )' % H
    re = s([lr, ur], 'crred', '( Re ` %s ) = %s' % (LW, L))
    ne = s([re], 'negeqd', '-u ( Re ` %s ) = -u %s' % (LW, L))
    le = lineq(w, A, '-u %s' % L, KH, closure=cl)
    ex = s([s([ne, le], 'eqtrd', '-u ( Re ` %s ) = %s' % (LW, KH))], 'oveq2d', '( Y ^c -u ( Re ` %s ) ) = ( Y ^c %s )' % (LW, KH))
    ay2 = s([ay, ex], 'eqtrd', '( abs ` ( Y ^c -u %s ) ) = ( Y ^c %s )' % (LW, KH))
    GW = '( _G ` %s )' % LW; YW = '( Y ^c -u %s )' % LW
    gc = s([gl, w.inst('z6absle')], 'syl', '%s e. CC' % GW)
    am = s([gc, yc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GW, YW, GW, YW))
    YP = '( Y ^c %s )' % KH
    am2 = s([am, s([ay2], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. %s )' % (GW, YW, GW, YP))], 'eqtrd',
            '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. %s )' % (GW, YW, GW, YP))
    ypp = s([yrp, cl.mem(KH, 'RR')], 'rpcxpcld', '%s e. RR+' % YP)
    # g real
    hr = a1c(w, A, 'halfre', '%s e. RR' % H)
    hc = s([a1c(w, A, 'halfcn', '%s e. CC' % H), iuc], 'addcld', '%s e. CC' % HL)
    rh = s([hr, ur], 'crred', '( Re ` %s ) = %s' % (HL, H))
    hdg = s([hc, s([a1c(w, A, 'halfgt0', '0 < %s' % H), rh], 'breqtrrd', '0 < ( Re ` %s )' % HL), w.inst('zrenn')], 'syl2anc', '%s e. %s' % (HL, DG))
    gr = s([s([hdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % HL)], 'abscld', '%s e. RR' % g)
    fn = s([kn, w.inst('faccl')], 'syl', '%s e. NN' % F)
    cl.leaf(g, 'RR', gr); cl.leaf(F, 'NN', fn)
    B = '( ( 2 / %s ) x. %s )' % (F, g)
    m = s([s([gc], 'abscld', '( abs ` %s ) e. RR' % GW), cl.mem(B, 'RR'), s([ypp], 'rpred', '%s e. RR' % YP), s([ypp], 'rpge0d', '0 <_ %s' % YP), gl], 'lemul1ad',
          '( ( abs ` %s ) x. %s ) <_ ( %s x. %s )' % (GW, YP, B, YP))
    tf = s([a1c(w, A, '2cn', '2 e. CC'), s([fn], 'nncnd', '%s e. CC' % F), s([fn], 'nnne0d', '%s =/= 0' % F)], 'divcld', '( 2 / %s ) e. CC' % F)
    gcc = s([gr], 'recnd', '%s e. CC' % g); ypc = s([ypp], 'rpcnd', '%s e. CC' % YP)
    e1 = s([tf, gcc, ypc], 'mul32d', '( %s x. %s ) = ( ( ( 2 / %s ) x. %s ) x. %s )' % (B, YP, F, YP, g))
    e2 = s([a1c(w, A, '2cn', '2 e. CC'), ypc, s([fn], 'nncnd', '%s e. CC' % F), s([fn], 'nnne0d', '%s =/= 0' % F)], 'div23d',
           '( ( 2 x. %s ) / %s ) = ( ( 2 / %s ) x. %s )' % (YP, F, F, YP))
    e3 = s([e1, s([s([e2], 'eqcomd', '( ( 2 / %s ) x. %s ) = ( ( 2 x. %s ) / %s )' % (F, YP, YP, F))], 'oveq1d',
                  '( ( ( 2 / %s ) x. %s ) x. %s ) = ( ( ( 2 x. %s ) / %s ) x. %s )' % (F, YP, g, YP, F, g))], 'eqtrd',
           '( %s x. %s ) = ( ( ( 2 x. %s ) / %s ) x. %s )' % (B, YP, YP, F, g))
    fin = s([s([am2, m], 'eqbrtrd', '( abs ` ( %s x. %s ) ) <_ ( %s x. %s )' % (GW, YW, B, YP)), e3], 'breqtrd',
            '( abs ` ( %s x. %s ) ) <_ ( ( ( 2 x. %s ) / %s ) x. %s )' % (GW, YW, YP, F, g))
    toqed(w, fin, 'z6gyline')
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6gyr, z6gyl, z6gyline]:
        if want(f.__name__):
            if run(f()):
                status(f.__name__)
            else:
                break
