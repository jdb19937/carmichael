"""Sortie z4d, section A (continued): lswifmul, lswsq (tri_bilinear_eq), lstint (t_integral_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
import lin
lin.FASTPATH = True
from lin import linarith, lineq
from z4dlib import STATEMENTS as S, HYPS, ICC, TRI, ITG, ABS2, WS, BIL, H8, C48, IOO
from z4d_a import mk, a1, hyps


def lswifmul():
    w = W('lswifmul', 'The product of an indicator value and the conjugate of another is the indicator '
          'of the conjunction (Lean tri_bilinear_eq hprod).')
    A = '( B e. CC /\\ C e. CC )'
    IB = 'if ( ph , B , 0 )'; IC = 'if ( ps , C , 0 )'
    L = '( %s x. ( * ` %s ) )' % (IB, IC)
    R = 'if ( ( ph /\\ ps ) , ( B x. ( * ` C ) ) , 0 )'
    BC = '( B x. ( * ` C ) )'
    E1 = '( ( %s /\\ ph ) /\\ ps )' % A
    e = mk(w, E1)
    i1 = e([e([], 'simplr', 'ph'), w.inst('iftrue')], 'syl', '%s = B' % IB)
    i2 = e([e([], 'simpr', 'ps'), w.inst('iftrue')], 'syl', '%s = C' % IC)
    l1 = e([i1, e([i2], 'fveq2d', '( * ` %s ) = ( * ` C )' % IC)], 'oveq12d', '%s = %s' % (L, BC))
    r1 = e([e([e([], 'simplr', 'ph'), e([], 'simpr', 'ps')], 'jca', '( ph /\\ ps )'), w.inst('iftrue')], 'syl',
           '%s = %s' % (R, BC))
    g1 = e([l1, r1], 'eqtr4d', '%s = %s' % (L, R))
    E2 = '( ( %s /\\ ph ) /\\ -. ps )' % A
    f = mk(w, E2)
    nps = f([], 'simpr', '-. ps')
    j2 = f([nps, w.inst('iffalse')], 'syl', '%s = 0' % IC)
    cj = f([f([j2], 'fveq2d', '( * ` %s ) = ( * ` 0 )' % IC), a1(w, E2, 'cj0', '( * ` 0 ) = 0')], 'eqtrd',
           '( * ` %s ) = 0' % IC)
    ibc = f([f([], 'simplll', 'B e. CC'), f([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IB)
    l2 = f([f([cj], 'oveq2d', '%s = ( %s x. 0 )' % (L, IB)), f([ibc], 'mul01d', '( %s x. 0 ) = 0' % IB)], 'eqtrd',
           '%s = 0' % L)
    r2 = f([f([nps], 'intnand', '-. ( ph /\\ ps )'), w.inst('iffalse')], 'syl', '%s = 0' % R)
    g2 = f([l2, r2], 'eqtr4d', '%s = %s' % (L, R))
    gp = w.s([g1, g2], 'pm2.61dan', '( ( %s /\\ ph ) -> %s = %s )' % (A, L, R))
    E3 = '( %s /\\ -. ph )' % A
    g = mk(w, E3)
    nph = g([], 'simpr', '-. ph')
    k1 = g([nph, w.inst('iffalse')], 'syl', '%s = 0' % IB)
    icc = g([g([g([], 'simplr', 'C e. CC'), g([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % IC)], 'cjcld',
            '( * ` %s ) e. CC' % IC)
    l3 = g([g([k1], 'oveq1d', '%s = ( 0 x. ( * ` %s ) )' % (L, IC)), g([icc], 'mul02d', '( 0 x. ( * ` %s ) ) = 0' % IC)],
           'eqtrd', '%s = 0' % L)
    r3 = g([g([nph], 'intnanrd', '-. ( ph /\\ ps )'), w.inst('iffalse')], 'syl', '%s = 0' % R)
    g3 = g([l3, r3], 'eqtr4d', '%s = %s' % (L, R))
    w.qed([gp, g3], 'pm2.61dan', S['lswifmul'])
    return w


HKQ = 'A. a e. P ( ( C ` a ) e. CC /\\ ( L ` a ) e. RR )'


def hkat(w, ante, x, allst, memst):
    """( ante -> ( C ` x ) e. CC ), ( ante -> ( L ` x ) e. RR )"""
    idst = w.s([], 'id', '( a = %s -> a = %s )' % (x, x))
    cst, new = w.wcongr('( ( C ` a ) e. CC /\\ ( L ` a ) e. RR )', {'a': x}, 'a = %s' % x, {'a': idst})
    both = w.s([cst, allst, memst], 'rspcdva', '( %s -> %s )' % (ante, new))
    return (w.s([both], 'simpld', '( %s -> ( C ` %s ) e. CC )' % (ante, x)),
            w.s([both], 'simprd', '( %s -> ( L ` %s ) e. RR )' % (ante, x)))


def WIFv(v, H='H', u='u'):
    return 'if ( ( abs ` ( ( L ` %s ) - %s ) ) <_ %s , ( C ` %s ) , 0 )' % (v, u, H, v)


def PIF(H='H', u='u'):
    return 'if ( ( ( abs ` ( ( L ` i ) - %s ) ) <_ %s /\\ ( abs ` ( ( L ` j ) - %s ) ) <_ %s ) , ( ( C ` i ) x. ( * ` ( C ` j ) ) ) , 0 )' % (u, H, u, H)


def lswsq():
    w = W('lswsq', 'The window mean square integrates over RR to the real part of the triangle bilinear form '
          '(Lean tri_bilinear_eq in the form delta tri_delta = TRI, and window_integrable).')
    A0 = '( ( P e. Fin /\\ %s ) /\\ H e. RR+ )' % HKQ
    s = mk(w, A0)
    fin = s([], 'simpll', 'P e. Fin')
    allq = s([], 'simplr', HKQ)
    hrp = s([], 'simpr', 'H e. RR+')
    WSu = WS('H')
    WIi = WIFv('i'); WIj = WIFv('j')
    PI = PIF()
    DD = 'sum_ i e. P sum_ j e. P %s' % PI
    SJ = 'sum_ j e. P %s' % PI
    TRIij = TRI('( 2 x. H )', '( ( L ` i ) - ( L ` j ) )')
    CCJ = '( ( C ` i ) x. ( * ` ( C ` j ) ) )'
    # pointwise
    B = '( %s /\\ u e. RR )' % A0
    b = mk(w, B)
    bfin = b([fin], 'adantr', 'P e. Fin')
    ball = b([allq], 'adantr', HKQ)
    BI = '( %s /\\ i e. P )' % B
    bi = mk(w, BI)
    ci, li = hkat(w, BI, 'i', bi([ball], 'adantr', HKQ), bi([], 'simpr', 'i e. P'))
    wic = bi([ci, bi([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % WIi)
    BJ = '( %s /\\ j e. P )' % B
    bj = mk(w, BJ)
    cj, lj = hkat(w, BJ, 'j', bj([ball], 'adantr', HKQ), bj([], 'simpr', 'j e. P'))
    wjc = bj([cj, bj([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % WIj)
    wsc = b([bfin, wic], 'fsumcl', '%s e. CC' % WSu)
    p1 = b([wsc, w.inst('absvalsq')], 'syl', '%s = ( %s x. ( * ` %s ) )' % (ABS2(WSu), WSu, WSu))
    p2 = b([bfin, wic], 'fsumcj', '( * ` %s ) = sum_ i e. P ( * ` %s )' % (WSu, WIi))
    idst = w.s([], 'id', '( i = j -> i = j )')
    cst, new = w.congr('( * ` %s )' % WIi, {'i': 'j'}, 'i = j', {'i': idst})
    p3 = b([w.s([cst], 'cbvsumv', 'sum_ i e. P ( * ` %s ) = sum_ j e. P ( * ` %s )' % (WIi, WIj))], 'a1i',
           'sum_ i e. P ( * ` %s ) = sum_ j e. P ( * ` %s )' % (WIi, WIj))
    SCJ = 'sum_ j e. P ( * ` %s )' % WIj
    p23 = b([p2, p3], 'eqtrd', '( * ` %s ) = %s' % (WSu, SCJ))
    p4 = b([bfin, bfin, wic, bj([wjc], 'cjcld', '( * ` %s ) e. CC' % WIj)], 'fsum2mul',
           'sum_ i e. P sum_ j e. P ( %s x. ( * ` %s ) ) = ( %s x. %s )' % (WIi, WIj, WSu, SCJ))
    BIJ = '( %s /\\ j e. P )' % BI
    bij = mk(w, BIJ)
    cj2, lj2 = hkat(w, BIJ, 'j', bij([bi([ball], 'adantr', HKQ)], 'adantr', HKQ), bij([], 'simpr', 'j e. P'))
    p5 = bij([bij([ci], 'adantr', '( C ` i ) e. CC'), cj2, w.inst('lswifmul')], 'syl2anc',
             '( %s x. ( * ` %s ) ) = %s' % (WIi, WIj, PI))
    p6 = b([bi([p5], 'sumeq2dv', 'sum_ j e. P ( %s x. ( * ` %s ) ) = %s' % (WIi, WIj, SJ))], 'sumeq2dv',
           'sum_ i e. P sum_ j e. P ( %s x. ( * ` %s ) ) = %s' % (WIi, WIj, DD))
    pt = b([b([p1, b([p23], 'oveq2d', '( %s x. ( * ` %s ) ) = ( %s x. %s )' % (WSu, WSu, WSu, SCJ))], 'eqtrd',
              '%s = ( %s x. %s )' % (ABS2(WSu), WSu, SCJ)), b([p4, p6], 'eqtr3d', '( %s x. %s ) = %s' % (WSu, SCJ, DD))],
           'eqtrd', '%s = %s' % (ABS2(WSu), DD))
    # integrals
    CI = '( %s /\\ i e. P )' % A0
    c = mk(w, CI)
    ci0, li0 = hkat(w, CI, 'i', c([allq], 'adantr', HKQ), c([], 'simpr', 'i e. P'))
    CIJ = '( %s /\\ j e. P )' % CI
    d = mk(w, CIJ)
    cj0, lj0 = hkat(w, CIJ, 'j', d([c([allq], 'adantr', HKQ)], 'adantr', HKQ), d([], 'simpr', 'j e. P'))
    ccj = d([d([ci0], 'adantr', '( C ` i ) e. CC'), d([cj0], 'cjcld', '( * ` ( C ` j ) ) e. CC')], 'mulcld', '%s e. CC' % CCJ)
    PC_ = '( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( %s x. %s ) )' % (PI, ITG('RR', PI, 'u'), CCJ, TRIij)
    pr = d([d([d([li0], 'adantr', '( L ` i ) e. RR'), lj0], 'jca', '( ( L ` i ) e. RR /\\ ( L ` j ) e. RR )'),
            d([d([hrp], 'adantr', 'H e. RR+')] if False else [w.s([c([hrp], 'adantr', 'H e. RR+')], 'adantr', '( %s -> H e. RR+ )' % CIJ), ccj], 'jca',
              '( H e. RR+ /\\ %s e. CC )' % CCJ), w.inst('lswpair')], 'syl2anc', PC_)
    E3 = '( %s /\\ ( u e. RR /\\ j e. P ) )' % CI
    e3 = w.s([w.s([ccj], 'adantrl', '( %s -> %s e. CC )' % (E3, CCJ)), w.s([], '0cnd', '( %s -> 0 e. CC )' % E3)], 'ifcld',
             '( %s -> %s e. CC )' % (E3, PI))
    rmb = lambda ante: w.s([w.s([], 'rembl', 'RR e. dom vol')], 'a1i', '( %s -> RR e. dom vol )' % ante)
    inner = c([rmb(CI), c([fin], 'adantr', 'P e. Fin'), e3, d([pr], 'simpld', '( u e. RR |-> %s ) e. L^1' % PI)], 'itgfsum',
              '( ( u e. RR |-> %s ) e. L^1 /\\ %s = sum_ j e. P %s )' % (SJ, ITG('RR', SJ, 'u'), ITG('RR', PI, 'u')))
    E2 = '( %s /\\ ( u e. RR /\\ i e. P ) )' % A0
    e = mk(w, E2)
    e2in = '( ( %s /\\ ( u e. RR /\\ i e. P ) ) /\\ j e. P )' % A0
    ci2, li2 = hkat(w, E2, 'i', e([allq], 'adantr', HKQ), e([], 'simprr', 'i e. P'))
    cj3, lj3 = hkat(w, e2in, 'j', w.s([e([allq], 'adantr', HKQ)], 'adantr', '( %s -> %s )' % (e2in, HKQ)),
                    w.s([], 'simpr', '( %s -> j e. P )' % e2in))
    pic = w.s([w.s([w.s([ci2], 'adantr', '( %s -> ( C ` i ) e. CC )' % e2in), w.s([cj3], 'cjcld', '( %s -> ( * ` ( C ` j ) ) e. CC )' % e2in)],
                   'mulcld', '( %s -> %s e. CC )' % (e2in, CCJ)), w.s([], '0cnd', '( %s -> 0 e. CC )' % e2in)], 'ifcld',
              '( %s -> %s e. CC )' % (e2in, PI))
    e2c = e([e([fin], 'adantr', 'P e. Fin'), pic], 'fsumcl', '%s e. CC' % SJ)
    outer = s([rmb(A0), fin, e2c, c([inner], 'simpld', '( u e. RR |-> %s ) e. L^1' % SJ)], 'itgfsum',
              '( ( u e. RR |-> %s ) e. L^1 /\\ %s = sum_ i e. P %s )' % (DD, ITG('RR', DD, 'u'), ITG('RR', SJ, 'u')))
    v4 = c([c([inner], 'simprd', '%s = sum_ j e. P %s' % (ITG('RR', SJ, 'u'), ITG('RR', PI, 'u'))),
            c([d([pr], 'simprd', '%s = ( %s x. %s )' % (ITG('RR', PI, 'u'), CCJ, TRIij))], 'sumeq2dv',
              'sum_ j e. P %s = sum_ j e. P ( %s x. %s )' % (ITG('RR', PI, 'u'), CCJ, TRIij))], 'eqtrd',
           '%s = sum_ j e. P ( %s x. %s )' % (ITG('RR', SJ, 'u'), CCJ, TRIij))
    BL = BIL('( 2 x. H )')
    v5 = s([s([outer], 'simprd', '%s = sum_ i e. P %s' % (ITG('RR', DD, 'u'), ITG('RR', SJ, 'u'))),
            s([v4], 'sumeq2dv', 'sum_ i e. P %s = %s' % (ITG('RR', SJ, 'u'), BL))], 'eqtrd', '%s = %s' % (ITG('RR', DD, 'u'), BL))
    mq = s([pt], 'mpteq2dva', '( u e. RR |-> %s ) = ( u e. RR |-> %s )' % (ABS2(WSu), DD))
    iq = s([pt], 'itgeq2dv', '%s = %s' % (ITG('RR', ABS2(WSu), 'u'), ITG('RR', DD, 'u')))
    ib = s([mq, s([outer], 'simpld', '( u e. RR |-> %s ) e. L^1' % DD)], 'eqeltrd', '( u e. RR |-> %s ) e. L^1' % ABS2(WSu))
    val = s([iq, v5], 'eqtrd', '%s = %s' % (ITG('RR', ABS2(WSu), 'u'), BL))
    wsr = b([b([wsc], 'abscld', '( abs ` %s ) e. RR' % WSu)], 'resqcld', '%s e. RR' % ABS2(WSu))
    ire = s([ib, wsr], 'itgrecl', '%s e. RR' % ITG('RR', ABS2(WSu), 'u'))
    re = s([ire, w.inst('rere')], 'syl', '( Re ` %s ) = %s' % (ITG('RR', ABS2(WSu), 'u'), ITG('RR', ABS2(WSu), 'u')))
    val2 = s([re, s([val], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (ITG('RR', ABS2(WSu), 'u'), BL))], 'eqtr3d',
             '%s = ( Re ` %s )' % (ITG('RR', ABS2(WSu), 'u'), BL))
    w.qed([ib, val2], 'jca', S['lswsq'])
    return w


def sxcl(w, ante, allst, finst, t='t'):
    """( ( ante /\\ t e. RR ) -> SX(t) e. CC )"""
    from mvlib import SX
    At = '( %s /\\ %s e. RR )' % (ante, t)
    a = mk(w, At)
    Ai = '( %s /\\ i e. P )' % At
    b = mk(w, Ai)
    ci, li = hkat(w, Ai, 'i', b([a([allst], 'adantr', HKQ)], 'adantr', HKQ), b([], 'simpr', 'i e. P'))
    tc = b([b([a([], 'simpr', '%s e. RR' % t)], 'adantr', '%s e. RR' % t)], 'recnd', '%s e. CC' % t)
    E = '( exp ` ( _i x. ( ( L ` i ) x. %s ) ) )' % t
    ec = b([b([b([], 'ax-icn', '_i e. CC') if False else w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Ai),
                 b([b([li], 'recnd', '( L ` i ) e. CC'), tc], 'mulcld', '( ( L ` i ) x. %s ) e. CC' % t)], 'mulcld',
               '( _i x. ( ( L ` i ) x. %s ) ) e. CC' % t)], 'efcld', '%s e. CC' % E)
    return a([a([finst], 'adantr', 'P e. Fin'), b([ci, ec], 'mulcld', '( ( C ` i ) x. %s ) e. CC' % E)], 'fsumcl',
             '%s e. CC' % SX(t))


def ioomem(w, ante, a, b_, v='t'):
    Av = '( %s /\\ %s e. %s )' % (ante, v, IOO(a, b_))
    return w.s([w.s([], 'simpr', '( %s -> %s e. %s )' % (Av, v, IOO(a, b_))), w.inst('elioore')], 'syl',
               '( %s -> %s e. RR )' % (Av, v))


def lstint():
    from mvlib import SX, ringeqp, ringeq
    from cl import Closure
    from z4blib import cnsq
    w = W('lstint', 'Gallagher smoothing: the t-integral over ( -T , T ) of the mean square is at most '
          '48 T^2 / pi times the window mean square integrated over RR (Lean t_integral_le).')
    A0 = '( T e. RR+ /\\ ( P e. Fin /\\ %s ) )' % HKQ
    s = mk(w, A0)
    trp = s([], 'simpl', 'T e. RR+')
    tre = s([trp], 'rpred', 'T e. RR')
    hk = s([], 'simpr', '( P e. Fin /\\ %s )' % HKQ)
    fin = s([hk], 'simpld', 'P e. Fin')
    allq = s([hk], 'simprd', HKQ)
    T2 = '( 2 x. T )'
    t2rp = s([s([], '2rp', '2 e. RR+') if False else w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), trp],
             'rpmulcld', '%s e. RR+' % T2)
    t2re = s([t2rp], 'rpred', '%s e. RR' % T2)
    X = ABS2(SX('t'))
    sxc = sxcl(w, A0, allq, fin)
    from mvlib import SXD
    DV = '( ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (SX('t'), SXD('t'), SX('t'), SXD('t'))
    dv = s([hk, w.inst('mvsxdv')], 'syl', DV)
    cn = s([dv], 'simp2d', '( t e. RR |-> %s ) e. ( RR -cn-> CC )' % SX('t'))
    xcn = cnsq(w, A0, cn, SX('t'), 't', sxc)
    At = '( %s /\\ t e. RR )' % A0
    xr = w.s([w.s([sxc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, SX('t')))], 'resqcld', '( %s -> %s e. RR )' % (At, X))
    xp = w.s([w.s([sxc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, SX('t')))], 'sqge0d', '( %s -> 0 <_ %s )' % (At, X))
    lv = {'T': tre}
    tpos = s([trp], 'rpge0d', '0 <_ T')
    nt = s([tre], 'renegcld', '-u T e. RR')
    nt2 = s([t2re], 'renegcld', '-u %s e. RR' % T2)
    o1 = linarith(w, A0, [tpos], '-u %s <_ -u T' % T2, leaves=lv)
    o2 = linarith(w, A0, [tpos], '-u T <_ T', leaves=lv)
    o3 = linarith(w, A0, [tpos], 'T <_ %s' % T2, leaves=lv)
    mono = s([nt2, t2re, nt, tre, o1, o2, o3, xcn, xr, xp], 'lsitgmono',
             '%s <_ %s' % (ITG(IOO('-u T', 'T'), X), ITG(IOO('-u ' + T2, T2), X)))
    from mvlib import BIL as MBIL
    D1 = '( _pi / ( 2 x. %s ) )' % T2
    K1 = '( ( ; 1 2 x. ( %s ^ 2 ) ) / _pi )' % T2
    ker = s([t2rp, hk, w.inst('mvkmvt')], 'syl2anc', '%s <_ ( %s x. ( Re ` %s ) )' % (ITG(IOO('-u ' + T2, T2), X), K1, MBIL(D1)))
    # constants
    cl = Closure(w, A0, {'T': tre})
    k12 = ringeqp(w, A0, '( ; 1 2 x. ( %s ^ 2 ) )' % T2, '( ; 4 8 x. ( T ^ 2 ) )', cl)
    kq = s([k12], 'oveq1d', '%s = %s' % (K1, C48))
    pic = s([], 'picnd', '_pi e. CC') if False else w.s([w.s([], 'picn', '_pi e. CC')], 'a1i', '( %s -> _pi e. CC )' % A0)
    F4 = '( 4 x. T )'
    f4 = ringeq(w, A0, '( 2 x. %s )' % T2, F4, cl)
    f8 = ringeq(w, A0, '( 8 x. T )', '( 2 x. %s )' % F4, cl)
    f4re = s([w.s([w.s([], '4re', '4 e. RR')], 'a1i', '( %s -> 4 e. RR )' % A0), tre], 'remulcld', '%s e. RR' % F4)
    f4c = s([f4re], 'recnd', '%s e. CC' % F4)
    f4ne = s([s([w.s([w.s([], '4rp', '4 e. RR+')], 'a1i', '( %s -> 4 e. RR+ )' % A0), trp], 'rpmulcld', '%s e. RR+' % F4)], 'rpne0d', '%s =/= 0' % F4)
    twoc = w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0)
    twone = w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % A0)
    d1a = s([f4], 'oveq2d', '%s = ( _pi / %s )' % (D1, F4))
    c5 = s([pic, f4c, twoc, f4ne, twone], 'divcan5d', '( ( 2 x. _pi ) / ( 2 x. %s ) ) = ( _pi / %s )' % (F4, F4))
    da = s([twoc, pic, s([twoc, f4c], 'mulcld', '( 2 x. %s ) e. CC' % F4), s([twoc, f4c, twone, f4ne], 'mulne0d', '( 2 x. %s ) =/= 0' % F4)],
           'divassd', '( ( 2 x. _pi ) / ( 2 x. %s ) ) = ( 2 x. ( _pi / ( 2 x. %s ) ) )' % (F4, F4))
    h8 = s([s([f8], 'oveq2d', '%s = ( _pi / ( 2 x. %s ) )' % (H8, F4))], 'oveq2d',
           '( 2 x. %s ) = ( 2 x. ( _pi / ( 2 x. %s ) ) )' % (H8, F4))
    d2 = s([h8, s([da, c5], 'eqtr3d', '( 2 x. ( _pi / ( 2 x. %s ) ) ) = ( _pi / %s )' % (F4, F4))], 'eqtrd',
           '( 2 x. %s ) = ( _pi / %s )' % (H8, F4))
    H2 = '( 2 x. %s )' % H8
    dq = s([d1a, d2], 'eqtr4d', '%s = %s' % (D1, H2))
    # BIL(D1) = BIL(H2)
    Y = '( ( L ` i ) - ( L ` j ) )'
    CIJ = '( ( %s /\\ i e. P ) /\\ j e. P )' % A0
    d = mk(w, CIJ)
    dqd = w.s([w.s([dq], 'adantr', '( ( %s /\\ i e. P ) -> %s = %s )' % (A0, D1, H2))], 'adantr', '( %s -> %s = %s )' % (CIJ, D1, H2))
    tq = d([d([dqd], 'breq2d', '( ( abs ` %s ) <_ %s <-> ( abs ` %s ) <_ %s )' % (Y, D1, Y, H2)),
            d([dqd], 'oveq1d', '( %s - ( abs ` %s ) ) = ( %s - ( abs ` %s ) )' % (D1, Y, H2, Y)), d([], 'eqidd', '0 = 0')],
           'ifbieq12d', '%s = %s' % (TRI(D1, Y), TRI(H2, Y)))
    CCJ = '( ( C ` i ) x. ( * ` ( C ` j ) ) )'
    t2 = d([tq], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (CCJ, TRI(D1, Y), CCJ, TRI(H2, Y)))
    t3 = w.s([t2], 'sumeq2dv', '( ( %s /\\ i e. P ) -> sum_ j e. P ( %s x. %s ) = sum_ j e. P ( %s x. %s ) )' % (A0, CCJ, TRI(D1, Y), CCJ, TRI(H2, Y)))
    t4 = s([t3], 'sumeq2dv', '%s = %s' % (MBIL(D1), BIL(H2)))
    bq = s([kq, s([t4], 'fveq2d', '( Re ` %s ) = ( Re ` %s )' % (MBIL(D1), BIL(H2)))], 'oveq12d',
           '( %s x. ( Re ` %s ) ) = ( %s x. ( Re ` %s ) )' % (K1, MBIL(D1), C48, BIL(H2)))
    h8rp = s([w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % A0),
              s([w.s([w.s([], '8re', '8 e. RR')], 'a1i', '( %s -> 8 e. RR )' % A0) if False else
                 w.s([w.s([w.s([], '8re', '8 e. RR'), w.s([], '8pos', '0 < 8')], 'elrpii', '8 e. RR+')], 'a1i', '( %s -> 8 e. RR+ )' % A0), trp], 'rpmulcld', '( 8 x. T ) e. RR+')],
             'rpdivcld', '%s e. RR+' % H8)
    WSH = WS(H8)
    sq = s([hk, h8rp, w.inst('lswsq')], 'syl2anc',
           '( ( u e. RR |-> %s ) e. L^1 /\\ %s = ( Re ` %s ) )' % (ABS2(WSH), ITG('RR', ABS2(WSH), 'u'), BIL(H2)))
    rq = s([s([sq], 'simprd', '%s = ( Re ` %s )' % (ITG('RR', ABS2(WSH), 'u'), BIL(H2)))], 'oveq2d',
           '( %s x. %s ) = ( %s x. ( Re ` %s ) )' % (C48, ITG('RR', ABS2(WSH), 'u'), C48, BIL(H2)))
    RHS = '( %s x. %s )' % (C48, ITG('RR', ABS2(WSH), 'u'))
    k2 = s([ker, s([bq, rq], 'eqtr4d', '( %s x. ( Re ` %s ) ) = %s' % (K1, MBIL(D1), RHS))], 'breqtrd',
           '%s <_ %s' % (ITG(IOO('-u ' + T2, T2), X), RHS))
    def ireal(a, b_):
        At2 = '( %s /\\ t e. %s )' % (A0, IOO(a, b_))
        tm = ioomem(w, A0, a, b_)
        xr2 = w.s([w.s([w.s([w.s([tm, w.s([], 'simpl', '( %s -> %s )' % (At2, A0))], 'jca', '( %s -> ( %s /\\ t e. RR ) )' % (At2, A0)) if False else
                             w.s([w.s([], 'simpl', '( %s -> %s )' % (At2, A0)), tm], 'jca', '( %s -> %s )' % (At2, At)), sxc], 'syl',
                            '( %s -> %s e. CC )' % (At2, SX('t')))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At2, SX('t')))],
                   'resqcld', '( %s -> %s e. RR )' % (At2, X))
        ib = s([(nt if a == '-u T' else nt2), (tre if b_ == 'T' else t2re), xcn], 'lsibl', '( t e. %s |-> %s ) e. L^1' % (IOO(a, b_), X))
        return s([xr2, ib], 'itgrecl', '%s e. RR' % ITG(IOO(a, b_), X))
    i1 = ireal('-u T', 'T')
    i2 = ireal('-u ' + T2, T2)
    wsr = w.s([w.s([w.s([], 'id', '( ( %s /\\ u e. RR ) -> ( %s /\\ u e. RR ) )' % (A0, A0))], 'id', '( ( %s /\\ u e. RR ) -> ( %s /\\ u e. RR ) )' % (A0, A0))], 'id', '( ( %s /\\ u e. RR ) -> ( %s /\\ u e. RR ) )' % (A0, A0)) if False else None
    Au = '( %s /\\ u e. RR )' % A0
    uc = mk(w, Au)
    Aui = '( %s /\\ i e. P )' % Au
    ui = mk(w, Aui)
    cu, lu = hkat(w, Aui, 'i', ui([uc([allq], 'adantr', HKQ)], 'adantr', HKQ), ui([], 'simpr', 'i e. P'))
    wic = ui([cu, ui([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % WIFv('i', H8))
    wsc = uc([uc([fin], 'adantr', 'P e. Fin'), wic], 'fsumcl', '%s e. CC' % WSH)
    wsq = uc([uc([wsc], 'abscld', '( abs ` %s ) e. RR' % WSH)], 'resqcld', '%s e. RR' % ABS2(WSH))
    iw = s([wsq, s([sq], 'simpld', '( u e. RR |-> %s ) e. L^1' % ABS2(WSH))], 'itgrecl', '%s e. RR' % ITG('RR', ABS2(WSH), 'u'))
    c48r = s([s([w.s([w.s([], '4nn0', '4 e. NN0'), w.s([], '8re', '8 e. RR')], 'decrecl' if False else 'deccl', '; 4 8 e. NN0') if False else
                  w.s([w.s([w.s([w.s([], '4nn0', '4 e. NN0'), w.s([], '8nn0', '8 e. NN0')], 'deccl', '; 4 8 e. NN0')], 'nn0rei', '; 4 8 e. RR')], 'a1i', '( %s -> ; 4 8 e. RR )' % A0),
                  s([tre], 'resqcld', '( T ^ 2 ) e. RR')], 'remulcld', '( ; 4 8 x. ( T ^ 2 ) ) e. RR'),
              w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A0),
              w.s([w.s([], 'pine0', '_pi =/= 0')], 'a1i', '( %s -> _pi =/= 0 )' % A0)], 'redivcld', '%s e. RR' % C48)
    rr = s([c48r, iw], 'remulcld', '%s e. RR' % RHS)
    w.qed([i1, i2, rr, mono, k2], 'letrd', S['lstint'])
    return w


ALL = {'lstint': lstint, 'lswsq': lswsq, 'lswifmul': lswifmul}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
