"""T10: the smoothGo arithmetic the smoothGoF loop reads (Lean ` SGInv ` with its witnesses explicit).

  sgsh    for ` i <_ h ` : ` smoothGo d r h = ( ( smoothGo ( d + i ) r_i ( h - i ) ).1 , ( .. ).2 + a_i ) ` with
          ` r_i = ( smoothGo d r i ).1 ` , ` a_i = ( smoothGo d r i ).2 `
  sgstep  ` r_( i + 1 ) = ( divOut ( d + i ) r_i r_i ).1 ` and ` a_( i + 1 ) = ( ( a_i + c_i ) + 1 ) ` ,
          ` c_i = ( divOut ( d + i ) r_i r_i ).2 `
  dofle   ` ( divOut d r f ).1 <_ r `
  sgfle   ` r_i <_ r `

    MM_DB=sorties/t10.mm python3 tools/gen/t10_g_sga.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, lineq
from cl import Closure
from t10_e_doa import DOX, P1, P2, RI, SHV, snd_of, fst_of, ex_, lift_from

SEL = sys.argv[1:]
SGX = lambda d, r, f: '( ( %s SmoothGo %s ) ` %s )' % (d, r, f)
DOG = lambda d, r, f: '( ( %s DivOut %s ) ` %s )' % (d, r, f)
RS = lambda i: P1(SGX('G', 'F', i))
AS = lambda i: P2(SGX('G', 'F', i))
GI = lambda i: '( G + %s )' % i
SGI = lambda i, h: SGX(GI(i), RS(i), '( %s - %s )' % (h, i))
SV = lambda i, h: '<. %s , ( %s + %s ) >.' % (P1(SGI(i, h)), P2(SGI(i, h)), AS(i))
QS = lambda i: P1(DOG(GI(i), RS(i), RS(i)))
CS = lambda i: P2(DOG(GI(i), RS(i), RS(i)))
PH2 = '( G e. NN /\\ F e. NN0 )'
ST_SGSH = '( ( %s /\\ ( H e. NN0 /\\ I e. NN0 /\\ I <_ H ) ) -> %s = %s )' % (PH2, SGX('G', 'F', 'H'), SV('I', 'H'))
ST_SGSTEP = ('( ( %s /\\ I e. NN0 ) -> ( %s = %s /\\ %s = ( ( %s + %s ) + 1 ) ) )'
             % (PH2, RS('( I + 1 )'), QS('I'), AS('( I + 1 )'), AS('I'), CS('I')))
ST_DOFLE = '( ( G e. NN /\\ F e. NN0 /\\ H e. NN0 ) -> %s <_ F )' % P1(DOX('F', 'H'))
ST_SGFLE = '( ( %s /\\ I e. NN0 ) -> %s <_ F )' % (PH2, RS('I'))


def sgcl(w, ph, d, r, f, dn, rn, fn):
    """( ph -> SGX( d , r , f ) e. ( NN0 X. NN0 ) )"""
    s = w.s
    return s([s([dn, rn], 'jca', '( %s -> ( %s e. NN /\\ %s e. NN0 ) )' % (ph, d, r)), fn, w.inst('smoothgocl')], 'syl2anc',
             '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, SGX(d, r, f)))


def docl(w, ph, d, r, f, dn, rn, fn):
    s = w.s
    return s([s([dn, rn], 'jca', '( %s -> ( %s e. NN /\\ %s e. NN0 ) )' % (ph, d, r)), fn, w.inst('divoutcl')], 'syl2anc',
             '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, DOG(d, r, f)))


def comp(w, ph, x, xcl, k):
    return w.s([xcl, w.inst('xp1st' if k == 1 else 'xp2nd')], 'syl', '( %s -> ( %s ` %s ) e. NN0 )' % (ph, '1st' if k == 1 else '2nd', x))


def sgp1(w, ph, d, r, f, dn, rn, fn):
    """( ph -> SGX( d , r , ( f + 1 ) ) = <. .. >. ) (smoothgop1) and the parts"""
    s = w.s
    q = P1(DOG(d, r, r))
    c = P2(DOG(d, r, r))
    S1 = SGX('( %s + 1 )' % d, q, f)
    V = '<. %s , ( ( %s + %s ) + 1 ) >.' % (P1(S1), P2(S1), c)
    st = s([s([dn, rn], 'jca', '( %s -> ( %s e. NN /\\ %s e. NN0 ) )' % (ph, d, r)), fn, w.inst('smoothgop1')], 'syl2anc',
           '( %s -> %s = %s )' % (ph, SGX(d, r, '( %s + 1 )' % f), V))
    return st, V, q, c, S1


def sgsh():
    lab = 'sgsh'
    w = W(lab, 'The shift of Lean\'s ` smoothGo ` (its loop invariant ` SGInv ` with the witnesses explicit): after ` i <_ h ` '
               'iterations the divisor is ` d + i ` , the number ` r_i = ( smoothGo d r i ).1 ` and the charge so far '
               '` ( smoothGo d r i ).2 ` .')
    s = w.s
    ph = PH2
    gnn = s([], 'simpl', '( %s -> G e. NN )' % ph)
    fn = s([], 'simpr', '( %s -> F e. NN0 )' % ph)
    PS = lambda n: 'A. k e. NN0 ( %s <_ k -> %s = %s )' % (n, SGX('G', 'F', 'k'), SV(n, 'k'))
    BODY = lambda n, v: '( %s <_ %s -> %s = %s )' % (n, v, SGX('G', 'F', v), SV(n, v))

    def cbv(ante, n):
        """( ante -> A. h e. NN0 BODY( n , h ) ) -> ( ante -> PS( n ) )"""
        e = s([], 'id', '( h = k -> h = k )')
        cg, new = w.wcongr(BODY(n, 'h'), {'h': 'k'}, 'h = k', {'h': e})
        assert new == BODY(n, 'k'), new
        return s([cg], 'cbvralvw', '( A. h e. NN0 %s <-> %s )' % (BODY(n, 'h'), PS(n)))

    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    # ---------------- base
    pb = '( %s /\\ h e. NN0 )' % ph
    hb = s([], 'simpr', '( %s -> h e. NN0 )' % pb)
    gb, fb = lift_from(w, ph, pb, gnn), lift_from(w, ph, pb, fn)
    s0 = s([gb, fb, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. F , 0 >. )' % (pb, SGX('G', 'F', '0')))
    fe = s([fb], 'elexd', '( %s -> F e. _V )' % pb)
    ze = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % pb)
    r0 = fst_of(w, pb, SGX('G', 'F', '0'), 'F', '0', s0, fe, ze)
    a0 = snd_of(w, pb, SGX('G', 'F', '0'), 'F', '0', s0, fe, ze)
    g0 = s([s([gb], 'nncnd', '( %s -> G e. CC )' % pb), w.inst('addrid')], 'syl', '( %s -> ( G + 0 ) = G )' % pb)
    h0 = s([s([hb], 'nn0cnd', '( %s -> h e. CC )' % pb), w.inst('subid1')], 'syl', '( %s -> ( h - 0 ) = h )' % pb)
    rw1, x1 = w.rewrite(SV('0', 'h'), {RS('0'): ('F', r0), AS('0'): ('0', a0), GI('0'): ('G', g0), '( h - 0 )': ('h', h0)}, pb)
    X = SGX('G', 'F', 'h')
    assert x1 == '<. %s , ( %s + 0 ) >.' % (P1(X), P2(X)), x1
    xc = sgcl(w, pb, 'G', 'F', 'h', gb, fb, hb)
    ad = s([s([comp(w, pb, X, xc, 2)], 'nn0cnd', '( %s -> %s e. CC )' % (pb, P2(X))), w.inst('addrid')], 'syl',
           '( %s -> ( %s + 0 ) = %s )' % (pb, P2(X), P2(X)))
    rw2, x2 = w.rewrite(x1, {'( %s + 0 )' % P2(X): (P2(X), ad)}, pb)
    e12 = s([s([s([rw1, rw2], 'eqtrd', '( %s -> %s = %s )' % (pb, SV('0', 'h'), x2)),
                s([s([xc, w.inst('1st2nd2')], 'syl', '( %s -> %s = %s )' % (pb, X, x2))], 'eqcomd', '( %s -> %s = %s )' % (pb, x2, X))],
               'eqtrd', '( %s -> %s = %s )' % (pb, SV('0', 'h'), X))], 'eqcomd', '( %s -> %s = %s )' % (pb, X, SV('0', 'h')))
    base0 = s([s([e12], 'a1d', '( %s -> ( 0 <_ h -> %s = %s ) )' % (pb, X, SV('0', 'h')))], 'ralrimiva',
              '( %s -> A. h e. NN0 %s )' % (ph, BODY('0', 'h')))
    base = s([base0, cbv(ph, '0')], 'sylib', '( %s -> %s )' % (ph, PS('0')))
    # ---------------- step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    b = '( ( %s /\\ h e. NN0 ) /\\ ( m + 1 ) <_ h )' % a
    mn = lift_from(w, '( %s /\\ m e. NN0 )' % ph, b, s([], 'simpr', '( ( %s /\\ m e. NN0 ) -> m e. NN0 )' % ph))
    ih = lift_from(w, a, b, s([], 'simpr', '( %s -> %s )' % (a, PS('m'))))
    hn = s([], 'simplr', '( %s -> h e. NN0 )' % b)
    hl = s([], 'simpr', '( %s -> ( m + 1 ) <_ h )' % b)
    gn2, fn2 = lift_from(w, ph, b, gnn), lift_from(w, ph, b, fn)
    cl = Closure(w, b, {'m': ('NN0', mn), 'h': ('NN0', hn), 'G': ('NN', gn2)})

    def ihat(t, tn, tle):
        """( b -> SGX( G , F , t ) = SV( m , t ) ) from the IH at h := t"""
        e = s([], 'id', '( k = %s -> k = %s )' % (t, t))
        cg, new = w.wcongr(BODY('m', 'k'), {'k': t}, 'k = %s' % t, {'k': e})
        r = s([cg], 'rspcv', '( %s e. NN0 -> ( %s -> %s ) )' % (t, PS('m'), new))
        imp = s([tn, ih, r], 'sylc', '( %s -> %s )' % (b, new))
        return s([tle, imp], 'mpd', '( %s -> %s = %s )' % (b, SGX('G', 'F', t), SV('m', t)))
    mh = linarith(w, b, [hl], 'm <_ h', closure=cl)
    ihh = ihat('h', hn, mh)
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % b)
    mm1 = linarith(w, b, [], 'm <_ ( m + 1 )', closure=cl)
    ih1 = ihat('( m + 1 )', m1n, mm1)
    # the numbers at m
    gm = GI('m')
    gmn = s([gn2, mn, w.inst('nnaddcl') if False else w.inst('nnnn0addcl')], 'syl2anc', '( %s -> %s e. NN )' % (b, gm))
    Xm = SGX('G', 'F', 'm')
    xmc = sgcl(w, b, 'G', 'F', 'm', gn2, fn2, mn)
    rmn = comp(w, b, Xm, xmc, 1)
    amn = comp(w, b, Xm, xmc, 2)
    # SG( gm , rm , ( h - ( m + 1 ) ) + 1 )
    HM1 = '( h - ( m + 1 ) )'
    hm1n = s([m1n, hn, hl, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (b, HM1))
    ehm = lineq(w, b, '( h - m )', '( %s + 1 )' % HM1, closure=cl)
    st1, V1, q, c, S1 = sgp1(w, b, gm, RS('m'), HM1, gmn, rmn, hm1n)
    # SG( gm , rm , ( 0 + 1 ) )
    z0 = closed(w, b, '0nn0', '0 e. NN0')
    st0, V0, q0, c0, S0 = sgp1(w, b, gm, RS('m'), '0', gmn, rmn, z0)
    assert q0 == q and c0 == c
    gm1 = '( %s + 1 )' % gm
    gm1n = s([gmn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (b, gm1))
    dcl = docl(w, b, gm, RS('m'), RS('m'), gmn, rmn, rmn)
    qn = comp(w, b, DOG(gm, RS('m'), RS('m')), dcl, 1)
    cn = comp(w, b, DOG(gm, RS('m'), RS('m')), dcl, 2)
    sz = s([gm1n, qn, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. %s , 0 >. )' % (b, SGX(gm1, q, '0'), q))
    qe = s([qn], 'elexd', '( %s -> %s e. _V )' % (b, q))
    zz = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % b)
    sz1 = fst_of(w, b, SGX(gm1, q, '0'), q, '0', sz, qe, zz)
    sz2 = snd_of(w, b, SGX(gm1, q, '0'), q, '0', sz, qe, zz)
    rv0, xv0 = w.rewrite(V0, {P1(SGX(gm1, q, '0')): (q, sz1), P2(SGX(gm1, q, '0')): ('0', sz2)}, b)
    V0s = '<. %s , ( ( 0 + %s ) + 1 ) >.' % (q, c)
    assert xv0 == V0s, xv0
    # ( m + 1 ) - m = ( 0 + 1 ) : SV( m , m + 1 ) = <. .. SG( gm , rm , ( 0 + 1 ) ) .. >.
    e01 = lineq(w, b, '( ( m + 1 ) - m )', '( 0 + 1 )', closure=cl)
    SGm1 = SGX(gm, RS('m'), '( 0 + 1 )')
    rv1, xv1 = w.rewrite(SV('m', '( m + 1 )'), {'( ( m + 1 ) - m )': ('( 0 + 1 )', e01)}, b)
    assert xv1 == '<. %s , ( %s + %s ) >.' % (P1(SGm1), P2(SGm1), AS('m')), xv1
    v0f = s([st0, rv0], 'eqtrd', '( %s -> %s = %s )' % (b, SGm1, V0s))
    rv2, xv2 = w.rewrite(xv1, {SGm1: (V0s, v0f)}, b)
    A1 = '( ( 0 + %s ) + 1 )' % c
    p1a = s([qe, ex_(w, b, A1, 'ovex'), w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (b, V0s, q))
    p2a = s([qe, ex_(w, b, A1, 'ovex'), w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (b, V0s, A1))
    rv3, xv3 = w.rewrite(xv2, {'( 1st ` %s )' % V0s: (q, p1a), '( 2nd ` %s )' % V0s: (A1, p2a)}, b)
    AM1 = '( %s + %s )' % (A1, AS('m'))
    assert xv3 == '<. %s , %s >.' % (q, AM1), xv3
    sm1 = s([s([s([ih1, rv1], 'eqtrd', '( %s -> %s = %s )' % (b, SGX('G', 'F', '( m + 1 )'), xv1)), rv2], 'eqtrd',
               '( %s -> %s = %s )' % (b, SGX('G', 'F', '( m + 1 )'), xv2)), rv3], 'eqtrd',
            '( %s -> %s = %s )' % (b, SGX('G', 'F', '( m + 1 )'), xv3))
    am1e = s([ex_(w, b, AM1, 'ovex')], 'id', '') if False else ex_(w, b, AM1, 'ovex')
    r1q = fst_of(w, b, SGX('G', 'F', '( m + 1 )'), q, AM1, sm1, qe, am1e)
    a1q = snd_of(w, b, SGX('G', 'F', '( m + 1 )'), q, AM1, sm1, qe, am1e)
    # the target SV( m + 1 , h )
    ga = s([cl.mem('G', 'CC'), cl.mem('m', 'CC'), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % b), w.inst('addassd') if False else
            w.inst('addass')], 'syl3anc', '( %s -> ( ( G + m ) + 1 ) = ( G + ( m + 1 ) ) )' % b)
    gae = s([ga], 'eqcomd', '( %s -> %s = %s )' % (b, GI('( m + 1 )'), gm1))
    rt, xt = w.rewrite(SV('( m + 1 )', 'h'), {RS('( m + 1 )'): (q, r1q), AS('( m + 1 )'): (AM1, a1q), GI('( m + 1 )'): (gm1, gae)}, b)
    TGT = '<. %s , ( %s + %s ) >.' % (P1(S1), P2(S1), AM1)
    assert xt == TGT, (xt, TGT)
    # SV( m , h ) through ( h - m ) = HM1 + 1 and smoothgop1
    rs1, xs1 = w.rewrite(SV('m', 'h'), {'( h - m )': ('( %s + 1 )' % HM1, ehm)}, b)
    SGmh = SGX(gm, RS('m'), '( %s + 1 )' % HM1)
    rs2, xs2 = w.rewrite(xs1, {SGmh: (V1, st1)}, b)
    B1 = '( ( %s + %s ) + 1 )' % (P2(S1), c)
    s1c = sgcl(w, b, gm1, q, HM1, gm1n, qn, hm1n)
    pe1 = s([ex_(w, b, P1(S1), 'fvex'), ex_(w, b, B1, 'ovex'), w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (b, V1, P1(S1)))
    pe2 = s([ex_(w, b, P1(S1), 'fvex'), ex_(w, b, B1, 'ovex'), w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (b, V1, B1))
    rs3, xs3 = w.rewrite(xs2, {'( 1st ` %s )' % V1: (P1(S1), pe1), '( 2nd ` %s )' % V1: (B1, pe2)}, b)
    assert xs3 == '<. %s , ( %s + %s ) >.' % (P1(S1), B1, AS('m')), xs3
    cl.leaf(P2(S1), 'NN0', comp(w, b, S1, s1c, 2))
    cl.leaf(c, 'NN0', cn)
    cl.leaf(AS('m'), 'NN0', amn)
    ar = lineq(w, b, '( %s + %s )' % (B1, AS('m')), '( %s + %s )' % (P2(S1), AM1), closure=cl)
    rs4, xs4 = w.rewrite(xs3, {'( %s + %s )' % (B1, AS('m')): ('( %s + %s )' % (P2(S1), AM1), ar)}, b)
    assert xs4 == TGT, xs4
    chain = s([ihh, rs1], 'eqtrd', '( %s -> %s = %s )' % (b, X, xs1))
    for r_, x_ in ((rs2, xs2), (rs3, xs3), (rs4, xs4)):
        chain = s([chain, r_], 'eqtrd', '( %s -> %s = %s )' % (b, X, x_))
    fin = s([chain, rt], 'eqtr4d', '( %s -> %s = %s )' % (b, X, SV('( m + 1 )', 'h')))
    st0 = s([s([fin], 'ex', '( ( %s /\\ h e. NN0 ) -> ( ( m + 1 ) <_ h -> %s = %s ) )' % (a, X, SV('( m + 1 )', 'h')))], 'ralrimiva',
            '( %s -> A. h e. NN0 %s )' % (a, BODY('( m + 1 )', 'h')))
    st = s([st0, cbv(a, '( m + 1 )')], 'sylib', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([h1, h2, h3, h4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    p = '( %s /\\ ( H e. NN0 /\\ I e. NN0 /\\ I <_ H ) )' % ph
    iin = s([], 'simpr2', '( %s -> I e. NN0 )' % p)
    ps = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph)), iin], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)), ind], 'syl',
           '( %s -> %s )' % (p, PS('I')))
    e = s([], 'id', '( k = H -> k = H )')
    cg, new = w.wcongr(BODY('I', 'k'), {'k': 'H'}, 'k = H', {'k': e})
    r = s([cg], 'rspcv', '( H e. NN0 -> ( %s -> %s ) )' % (PS('I'), new))
    imp = s([s([], 'simpr1', '( %s -> H e. NN0 )' % p), ps, r], 'sylc', '( %s -> %s )' % (p, new))
    w.qed([s([], 'simpr3', '( %s -> I <_ H )' % p), imp], 'mpd', ST_SGSH)
    return w.run()


def sgstep():
    lab = 'sgstep'
    w = W(lab, 'One step of Lean\'s ` smoothGo ` from the front: ` r_( i + 1 ) ` is the number ` divOut ( d + i ) r_i r_i ` leaves '
               'and the charge grows by its count plus one (~ sgsh at ` h = i + 1 ` , ~ smoothgop1 , ~ smoothgo0 ).')
    s = w.s
    b = '( %s /\\ I e. NN0 )' % PH2
    gn2 = s([], 'simpll', '( %s -> G e. NN )' % b) if False else s([s([], 'simpl', '( %s -> %s )' % (b, PH2))], 'simpld', '( %s -> G e. NN )' % b)
    fn2 = s([s([], 'simpl', '( %s -> %s )' % (b, PH2))], 'simprd', '( %s -> F e. NN0 )' % b)
    mn = s([], 'simpr', '( %s -> I e. NN0 )' % b)
    cl = Closure(w, b, {'I': ('NN0', mn), 'G': ('NN', gn2)})
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( I + 1 ) e. NN0 )' % b)
    mm1 = linarith(w, b, [], 'I <_ ( I + 1 )', closure=cl)
    ih1 = s([s([s([], 'simpl', '( %s -> %s )' % (b, PH2)), s([m1n, mn, mm1], '3jca', '( %s -> ( ( I + 1 ) e. NN0 /\\ I e. NN0 /\\ I <_ ( I + 1 ) ) )' % b)],
               'jca', '( %s -> ( %s /\\ ( ( I + 1 ) e. NN0 /\\ I e. NN0 /\\ I <_ ( I + 1 ) ) ) )' % (b, PH2)),
             w.inst('sgsh')], 'syl', '( %s -> %s = %s )' % (b, SGX('G', 'F', '( I + 1 )'), SV('I', '( I + 1 )')))
    gm = GI('I')
    gmn = s([gn2, mn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> %s e. NN )' % (b, gm))
    xmc = sgcl(w, b, 'G', 'F', 'I', gn2, fn2, mn)
    rmn = comp(w, b, SGX('G', 'F', 'I'), xmc, 1)
    amn = comp(w, b, SGX('G', 'F', 'I'), xmc, 2)
    z0 = closed(w, b, '0nn0', '0 e. NN0')
    st0, V0, q, c, S0 = sgp1(w, b, gm, RS('I'), '0', gmn, rmn, z0)
    gm1 = '( %s + 1 )' % gm
    gm1n = s([gmn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (b, gm1))
    dcl = docl(w, b, gm, RS('I'), RS('I'), gmn, rmn, rmn)
    qn = comp(w, b, DOG(gm, RS('I'), RS('I')), dcl, 1)
    cn = comp(w, b, DOG(gm, RS('I'), RS('I')), dcl, 2)
    sz = s([gm1n, qn, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. %s , 0 >. )' % (b, SGX(gm1, q, '0'), q))
    qe = s([qn], 'elexd', '( %s -> %s e. _V )' % (b, q))
    zz = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % b)
    sz1 = fst_of(w, b, SGX(gm1, q, '0'), q, '0', sz, qe, zz)
    sz2 = snd_of(w, b, SGX(gm1, q, '0'), q, '0', sz, qe, zz)
    rv0, xv0 = w.rewrite(V0, {P1(SGX(gm1, q, '0')): (q, sz1), P2(SGX(gm1, q, '0')): ('0', sz2)}, b)
    V0s = '<. %s , ( ( 0 + %s ) + 1 ) >.' % (q, c)
    assert xv0 == V0s, xv0
    e01 = lineq(w, b, '( ( I + 1 ) - I )', '( 0 + 1 )', closure=cl)
    SGm1 = SGX(gm, RS('I'), '( 0 + 1 )')
    rv1, xv1 = w.rewrite(SV('I', '( I + 1 )'), {'( ( I + 1 ) - I )': ('( 0 + 1 )', e01)}, b)
    v0f = s([st0, rv0], 'eqtrd', '( %s -> %s = %s )' % (b, SGm1, V0s))
    rv2, xv2 = w.rewrite(xv1, {SGm1: (V0s, v0f)}, b)
    A1 = '( ( 0 + %s ) + 1 )' % c
    p1a = s([qe, ex_(w, b, A1, 'ovex'), w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (b, V0s, q))
    p2a = s([qe, ex_(w, b, A1, 'ovex'), w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (b, V0s, A1))
    rv3, xv3 = w.rewrite(xv2, {'( 1st ` %s )' % V0s: (q, p1a), '( 2nd ` %s )' % V0s: (A1, p2a)}, b)
    AM1 = '( %s + %s )' % (A1, AS('I'))
    assert xv3 == '<. %s , %s >.' % (q, AM1), xv3
    sm1 = s([s([s([ih1, rv1], 'eqtrd', '( %s -> %s = %s )' % (b, SGX('G', 'F', '( I + 1 )'), xv1)), rv2], 'eqtrd',
               '( %s -> %s = %s )' % (b, SGX('G', 'F', '( I + 1 )'), xv2)), rv3], 'eqtrd',
            '( %s -> %s = %s )' % (b, SGX('G', 'F', '( I + 1 )'), xv3))
    am1e = ex_(w, b, AM1, 'ovex')
    r1q = fst_of(w, b, SGX('G', 'F', '( I + 1 )'), q, AM1, sm1, qe, am1e)
    a1q = snd_of(w, b, SGX('G', 'F', '( I + 1 )'), q, AM1, sm1, qe, am1e)
    cl.leaf(c, 'NN0', cn)
    cl.leaf(AS('I'), 'NN0', amn)
    ar = lineq(w, b, AM1, '( ( %s + %s ) + 1 )' % (AS('I'), c), closure=cl)
    a1 = s([a1q, ar], 'eqtrd', '( %s -> %s = ( ( %s + %s ) + 1 ) )' % (b, AS('( I + 1 )'), AS('I'), c))
    w.qed([r1q, a1], 'jca', ST_SGSTEP)
    return w.run()


def dofle():
    lab = 'dofle'
    w = W(lab, 'Lean\'s ` divOut_fst_le ` : ` divOut d r f ` never returns more than ` r ` (~ dosh at the count, ~ dofz ).')
    s = w.s
    ph = '( G e. NN /\\ F e. NN0 /\\ H e. NN0 )'
    gnn, fn, hn = s([], 'simp1', '( %s -> G e. NN )' % ph), s([], 'simp2', '( %s -> F e. NN0 )' % ph), s([], 'simp3', '( %s -> H e. NN0 )' % ph)
    R_ = P2(DOX('F', 'H'))
    dcl = s([s([gnn, fn], 'jca', '( %s -> ( G e. NN /\\ F e. NN0 ) )' % ph), hn, w.inst('divoutcl')], 'syl2anc',
            '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, DOX('F', 'H')))
    rn = s([dcl, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, R_))
    rle = s([s([rn], 'nn0red', '( %s -> %s e. RR )' % (ph, R_))], 'leidd', '( %s -> %s <_ %s )' % (ph, R_, R_))
    sh = s([s([s([gnn, fn, hn], '3jca', '( %s -> ( G e. NN /\\ F e. NN0 /\\ H e. NN0 ) )' % ph), s([rn, rle], 'jca', '( %s -> ( %s e. NN0 /\\ %s <_ %s ) )' % (ph, R_, R_, R_))],
              'jca', '( %s -> ( ( G e. NN /\\ F e. NN0 /\\ H e. NN0 ) /\\ ( %s e. NN0 /\\ %s <_ %s ) ) )' % (ph, R_, R_, R_)), w.inst('dosh')], 'syl',
           '( %s -> ( %s <_ H /\\ %s = %s ) )' % (ph, R_, DOX('F', 'H'), SHV(R_)))
    th = s([sh], 'simpld', '( %s -> %s <_ H )' % (ph, R_))
    dv = s([sh], 'simprd', '( %s -> %s = %s )' % (ph, DOX('F', 'H'), SHV(R_)))
    gt = s([gnn, rn, w.inst('nnexpcl')], 'syl2anc', '( %s -> ( G ^ %s ) e. NN )' % (ph, R_))
    RJ = RI(R_)
    HMR = '( H - %s )' % R_
    rjn = s([fn, gt, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, RJ))
    hmn = s([rn, hn, th, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, HMR))
    Dr = DOX(RJ, HMR)
    cm = P2(Dr)
    rr = snd_of(w, ph, DOX('F', 'H'), P1(Dr), '( %s + %s )' % (cm, R_), dv, ex_(w, ph, P1(Dr), 'fvex'), ex_(w, ph, '( %s + %s )' % (cm, R_), 'ovex'))
    dcr = s([s([gnn, rjn], 'jca', '( %s -> ( G e. NN /\\ %s e. NN0 ) )' % (ph, RJ)), hmn, w.inst('divoutcl')], 'syl2anc',
            '( %s -> %s e. ( NN0 X. NN0 ) )' % (ph, Dr))
    cmn = s([dcr, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, cm))
    cl = Closure(w, ph, {'F': ('NN0', fn)})
    cl.leaf(R_, 'NN0', rn)
    cl.leaf(cm, 'NN0', cmn)
    c0 = lineq(w, ph, cm, '0', closure=cl) if False else None
    c0le = linarith(w, ph, [rr], '%s <_ 0' % cm, closure=cl)
    c0 = s([s([c0le, s([cmn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, cm))], 'jca', '( %s -> ( %s <_ 0 /\\ 0 <_ %s ) )' % (ph, cm, cm)),
            s([cl.mem(cm, 'RR'), closed(w, ph, '0re', '0 e. RR'), w.inst('letri3')], 'syl2anc',
              '( %s -> ( %s = 0 <-> ( %s <_ 0 /\\ 0 <_ %s ) ) )' % (ph, cm, cm, cm))], 'mpbird', '( %s -> %s = 0 )' % (ph, cm))
    fzr = s([s([s([gnn, rjn, hmn], '3jca', '( %s -> ( G e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (ph, RJ, HMR)), c0], 'jca',
               '( %s -> ( ( G e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) /\\ %s = 0 ) )' % (ph, RJ, HMR, cm)), w.inst('dofz')], 'syl',
            '( %s -> %s = %s )' % (ph, P1(Dr), RJ))
    f1 = fst_of(w, ph, DOX('F', 'H'), P1(Dr), '( %s + %s )' % (cm, R_), dv, ex_(w, ph, P1(Dr), 'fvex'), ex_(w, ph, '( %s + %s )' % (cm, R_), 'ovex'))
    fe = s([f1, fzr], 'eqtrd', '( %s -> %s = %s )' % (ph, P1(DOX('F', 'H')), RJ))
    l1 = s([fn, gt, w.inst('fldivnn0le')], 'syl2anc', '( %s -> %s <_ ( F / ( G ^ %s ) ) )' % (ph, RJ, R_))
    l2 = s([fn, gt, w.inst('nn0ledivnn')], 'syl2anc', '( %s -> ( F / ( G ^ %s ) ) <_ F )' % (ph, R_))
    dvr = s([s([fn], 'nn0red', '( %s -> F e. RR )' % ph), s([gt], 'nnrpd', '( %s -> ( G ^ %s ) e. RR+ )' % (ph, R_))],
            'rerpdivcld', '( %s -> ( F / ( G ^ %s ) ) e. RR )' % (ph, R_))
    le = s([s([rjn], 'nn0red', '( %s -> %s e. RR )' % (ph, RJ)), dvr, s([fn], 'nn0red', '( %s -> F e. RR )' % ph), l1, l2], 'letrd',
           '( %s -> %s <_ F )' % (ph, RJ))
    w.qed([fe, le], 'eqbrtrd', ST_DOFLE)
    return w.run()


def sgfle():
    lab = 'sgfle'
    w = W(lab, 'Lean\'s ` smoothGo_fst_le ` along the iterations: the number ` r_i = ( smoothGo d r i ).1 ` never exceeds ` r ` '
               '(~ sgstep , ~ dofle ).')
    s = w.s
    ph = PH2
    gnn = s([], 'simpl', '( %s -> G e. NN )' % ph)
    fn = s([], 'simpr', '( %s -> F e. NN0 )' % ph)
    PS = lambda n: '%s <_ F' % RS(n)

    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    h1, h2, h3, h4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    s0 = s([gnn, fn, w.inst('smoothgo0')], 'syl2anc', '( %s -> %s = <. F , 0 >. )' % (ph, SGX('G', 'F', '0')))
    r0 = fst_of(w, ph, SGX('G', 'F', '0'), 'F', '0', s0, s([fn], 'elexd', '( %s -> F e. _V )' % ph),
                s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % ph))
    base = s([r0, s([s([fn], 'nn0red', '( %s -> F e. RR )' % ph)], 'leidd', '( %s -> F <_ F )' % ph)], 'eqbrtrd', '( %s -> %s )' % (ph, PS('0')))
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    mn = s([], 'simplr', '( %s -> m e. NN0 )' % a)
    ih = s([], 'simpr', '( %s -> %s )' % (a, PS('m')))
    gn2, fn2 = lift_from(w, ph, a, gnn), lift_from(w, ph, a, fn)
    stp = s([s([s([gn2, fn2], 'jca', '( %s -> %s )' % (a, PH2)), mn], 'jca', '( %s -> ( %s /\\ m e. NN0 ) )' % (a, PH2)),
             w.inst('sgstep')], 'syl', '( %s -> ( %s = %s /\\ %s = ( ( %s + %s ) + 1 ) ) )' % (a, RS('( m + 1 )'), QS('m'), AS('( m + 1 )'), AS('m'), CS('m')))
    rq = s([stp], 'simpld', '( %s -> %s = %s )' % (a, RS('( m + 1 )'), QS('m')))
    gmn = s([gn2, mn, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> %s e. NN )' % (a, GI('m')))
    xmc = sgcl(w, a, 'G', 'F', 'm', gn2, fn2, mn)
    rmn = comp(w, a, SGX('G', 'F', 'm'), xmc, 1)
    ql = s([s([gmn, rmn, rmn], '3jca', '( %s -> ( %s e. NN /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (a, GI('m'), RS('m'), RS('m'))),
            w.inst('dofle')], 'syl', '( %s -> %s <_ %s )' % (a, QS('m'), RS('m')))
    dcl = docl(w, a, GI('m'), RS('m'), RS('m'), gmn, rmn, rmn)
    qn = comp(w, a, DOG(GI('m'), RS('m'), RS('m')), dcl, 1)
    le = s([s([qn], 'nn0red', '( %s -> %s e. RR )' % (a, QS('m'))), s([rmn], 'nn0red', '( %s -> %s e. RR )' % (a, RS('m'))),
            s([fn2], 'nn0red', '( %s -> F e. RR )' % a), ql, ih], 'letrd', '( %s -> %s <_ F )' % (a, QS('m')))
    st = s([rq, le], 'eqbrtrd', '( %s -> %s )' % (a, PS('( m + 1 )')))
    w.qed([h1, h2, h3, h4, base, st], 'nn0indd', ST_SGFLE)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
