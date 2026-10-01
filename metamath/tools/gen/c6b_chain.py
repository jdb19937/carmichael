"""Sortie C6b, part 4: the identity theorem on a rectangle (holidstep,
holidchain, holidrect) and the consumer-facing local factorisation holnfac2."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *
import lin
from lin import linarith
lin.FASTPATH = True

RH = '( R / 2 )'


def halfzeq(w, E1, E2):
    """closed: ( E1 = E2 -> ( HALFZ(E1) <-> HALFZ(E2) ) )"""
    A = '%s = %s' % (E1, E2)
    s1 = w.s([], 'oveq2', '( %s -> ( w - %s ) = ( w - %s ) )' % (A, E1, E2))
    s2 = w.s([s1], 'fveq2d', '( %s -> ( abs ` ( w - %s ) ) = ( abs ` ( w - %s ) ) )' % (A, E1, E2))
    s3 = w.s([s2], 'breq1d', '( %s -> ( ( abs ` ( w - %s ) ) <_ %s <-> ( abs ` ( w - %s ) ) <_ %s ) )' % (A, E1, RH, E2, RH))
    s4 = w.s([s3], 'imbi1d', '( %s -> ( ( ( abs ` ( w - %s ) ) <_ %s -> ( F ` w ) = 0 ) <-> ( ( abs ` ( w - %s ) ) <_ %s -> ( F ` w ) = 0 ) ) )' % (A, E1, RH, E2, RH))
    return w.s([s4], 'ralbidv', '( %s -> ( %s <-> %s ) )' % (A, HALFZ(E1), HALFZ(E2)))


def halfzat(w, X, V):
    """closed: ( w = V -> ( ( |w - X| <_ R/2 -> F w = 0 ) <-> ( |V - X| <_ R/2 -> F V = 0 ) ) )"""
    A = 'w = %s' % V
    s1 = w.s([w.s([w.s([], 'oveq1', '( %s -> ( w - %s ) = ( %s - %s ) )' % (A, X, V, X))], 'fveq2d', '( %s -> ( abs ` ( w - %s ) ) = ( abs ` ( %s - %s ) ) )' % (A, X, V, X))], 'breq1d',
             '( %s -> ( ( abs ` ( w - %s ) ) <_ %s <-> ( abs ` ( %s - %s ) ) <_ %s ) )' % (A, X, RH, V, X, RH))
    s2 = w.s([w.s([], 'fveq2', '( %s -> ( F ` w ) = ( F ` %s ) )' % (A, V))], 'eqeq1d', '( %s -> ( ( F ` w ) = 0 <-> ( F ` %s ) = 0 ) )' % (A, V))
    return w.s([s1, s2], 'imbi12d', '( %s -> ( ( ( abs ` ( w - %s ) ) <_ %s -> ( F ` w ) = 0 ) <-> ( ( abs ` ( %s - %s ) ) <_ %s -> ( F ` %s ) = 0 ) ) )' % (A, X, RH, V, X, RH, V))


def PT(k, Y='Y', N='N'):
    return '( X + ( ( %s / %s ) x. ( %s - X ) ) )' % (k, N, Y)


def ptsub(w, var, val, Y='Y', N='N'):
    """closed: ( var = val -> ( HALFZ(PT var) <-> HALFZ(PT val) ) )"""
    e1 = w.s([], 'oveq1', '( %s = %s -> ( %s / %s ) = ( %s / %s ) )' % (var, val, var, N, val, N))
    e2 = w.s([e1], 'oveq1d', '( %s = %s -> ( ( %s / %s ) x. ( %s - X ) ) = ( ( %s / %s ) x. ( %s - X ) ) )' % (var, val, var, N, Y, val, N, Y))
    e3 = w.s([e2], 'oveq2d', '( %s = %s -> %s = %s )' % (var, val, PT(var, Y, N), PT(val, Y, N)))
    return w.s([e3, halfzeq(w, PT(var, Y, N), PT(val, Y, N))], 'syl', '( %s = %s -> ( %s <-> %s ) )' % (var, val, HALFZ(PT(var, Y, N)), HALFZ(PT(val, Y, N))))


if __name__ == '__main__':
    # ---- holidstep ------------------------------------------------------------------
    w = W('holidstep', 'One step of the chain: if a holomorphic function vanishes on the disc of radius R / 2 about a point X of the nested rectangle, it vanishes on the disc of radius R / 2 about every point Y of the rectangle within R / 2 of X.')
    AYX = '( abs ` ( Y - X ) )'
    TRIP = '( X e. ( A crect B ) /\\ Y e. ( A crect B ) /\\ %s < %s )' % (AYX, RH)
    A0 = '( %s /\\ %s /\\ %s )' % (HAN, TRIP, HALFZ('X'))
    han = w.s([], 'simp1', '( %s -> %s )' % (A0, HAN))
    trip = w.s([], 'simp2', '( %s -> %s )' % (A0, TRIP))
    hx = w.s([], 'simp3', '( %s -> %s )' % (A0, HALFZ('X')))
    xin = w.s([trip, w.inst('simp1')], 'syl', '( %s -> X e. ( A crect B ) )' % A0)
    yin = w.s([trip, w.inst('simp2')], 'syl', '( %s -> Y e. ( A crect B ) )' % A0)
    lt = w.s([trip, w.inst('simp3')], 'syl', '( %s -> %s < %s )' % (A0, AYX, RH))
    d = hanctx(w, A0, han)
    xc = w.s([d['crss'], xin], 'sseldd', '( %s -> X e. CC )' % A0)
    yc = w.s([d['crss'], yin], 'sseldd', '( %s -> Y e. CC )' % A0)
    ayx = w.s([w.s([yc, xc], 'subcld', '( %s -> ( Y - X ) e. CC )' % A0)], 'abscld', '( %s -> %s e. RR )' % (A0, AYX))
    hr = w.s([d['Rrp']], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, RH))
    hrr = w.s([hr], 'rpred', '( %s -> %s e. RR )' % (A0, RH))
    S = '( %s - %s )' % (RH, AYX)
    srp = w.s([lt, w.s([ayx, hrr, w.inst('difrp')], 'syl2anc', '( %s -> ( %s < %s <-> %s e. RR+ ) )' % (A0, AYX, RH, S))], 'mpbid', '( %s -> %s e. RR+ )' % (A0, S))
    A1 = '( %s /\\ v e. D )' % A0
    A2 = '( %s /\\ ( abs ` ( v - Y ) ) < %s )' % (A1, S)
    vd = w.s([w.s([], 'simpr', '( %s -> v e. D )' % A1)], 'adantr', '( %s -> v e. D )' % A2)
    vc = w.s([w.s([d['dss']], 'ad2antrr', '( %s -> D C_ CC )' % A2), vd], 'sseldd', '( %s -> v e. CC )' % A2)
    xc2 = w.s([xc], 'ad2antrr', '( %s -> X e. CC )' % A2); yc2 = w.s([yc], 'ad2antrr', '( %s -> Y e. CC )' % A2)
    tri = w.s([vc, xc2, yc2], 'abs3difd', '( %s -> ( abs ` ( v - X ) ) <_ ( ( abs ` ( v - Y ) ) + %s ) )' % (A2, AYX))
    lt2 = w.s([], 'simpr', '( %s -> ( abs ` ( v - Y ) ) < %s )' % (A2, S))
    leaves = {'( abs ` ( v - X ) )': ('RR', w.s([w.s([vc, xc2], 'subcld', '( %s -> ( v - X ) e. CC )' % A2)], 'abscld', '( %s -> ( abs ` ( v - X ) ) e. RR )' % A2)),
              '( abs ` ( v - Y ) )': ('RR', w.s([w.s([vc, yc2], 'subcld', '( %s -> ( v - Y ) e. CC )' % A2)], 'abscld', '( %s -> ( abs ` ( v - Y ) ) e. RR )' % A2)),
              AYX: ('RR', w.s([ayx], 'ad2antrr', '( %s -> %s e. RR )' % (A2, AYX))),
              'R': ('RR', w.s([d['rr']], 'ad2antrr', '( %s -> R e. RR )' % A2))}
    le = linarith(w, A2, [tri, lt2], '( abs ` ( v - X ) ) <_ %s' % RH, leaves=leaves)
    at = halfzat(w, 'X', 'v')
    imp_ = w.s([at, w.s([hx], 'ad2antrr', '( %s -> %s )' % (A2, HALFZ('X'))), vc], 'rspcdva', '( %s -> ( ( abs ` ( v - X ) ) <_ %s -> ( F ` v ) = 0 ) )' % (A2, RH))
    fv0 = w.s([le, imp_], 'mpd', '( %s -> ( F ` v ) = 0 )' % A2)
    VANV = 'A. v e. D ( ( abs ` ( v - Y ) ) < %s -> ( F ` v ) = 0 )' % S
    ralv = w.s([w.s([fv0], 'ex', '( %s -> ( ( abs ` ( v - Y ) ) < %s -> ( F ` v ) = 0 ) )' % (A1, S))], 'ralrimiva', '( %s -> %s )' % (A0, VANV))
    cb = w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( v = w -> ( v - Y ) = ( w - Y ) )')], 'fveq2d', '( v = w -> ( abs ` ( v - Y ) ) = ( abs ` ( w - Y ) ) )')], 'breq1d', '( v = w -> ( ( abs ` ( v - Y ) ) < %s <-> ( abs ` ( w - Y ) ) < %s ) )' % (S, S)),
                   w.s([w.s([], 'fveq2', '( v = w -> ( F ` v ) = ( F ` w ) )')], 'eqeq1d', '( v = w -> ( ( F ` v ) = 0 <-> ( F ` w ) = 0 ) )')], 'imbi12d',
                  '( v = w -> ( ( ( abs ` ( v - Y ) ) < %s -> ( F ` v ) = 0 ) <-> ( ( abs ` ( w - Y ) ) < %s -> ( F ` w ) = 0 ) ) )' % (S, S))], 'cbvralvw', '( %s <-> %s )' % (VANV, VAN('Y', S)))
    van = w.s([ralv, cb], 'sylib', '( %s -> %s )' % (A0, VAN('Y', S)))
    ssub = w.s([w.s([w.s([], 'breq2', '( s = %s -> ( ( abs ` ( w - Y ) ) < s <-> ( abs ` ( w - Y ) ) < %s ) )' % (S, S))], 'imbi1d', '( s = %s -> ( ( ( abs ` ( w - Y ) ) < s -> ( F ` w ) = 0 ) <-> ( ( abs ` ( w - Y ) ) < %s -> ( F ` w ) = 0 ) ) )' % (S, S))], 'ralbidv',
               '( s = %s -> ( %s <-> %s ) )' % (S, VAN('Y', 's'), VAN('Y', S)))
    exs = w.s([srp, van, w.s([ssub], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. s e. RR+ %s )' % (S, VAN('Y', S), VAN('Y', 's')))], 'syl2anc', '( %s -> E. s e. RR+ %s )' % (A0, VAN('Y', 's')))
    w.qed([w.s([han, yin], 'jca', '( %s -> ( %s /\\ Y e. ( A crect B ) ) )' % (A0, HAN)), exs, w.inst('holnid2')], 'syl2anc', '( %s -> %s )' % (A0, HALFZ('Y')))
    run1(w)

    # ---- holidchain -----------------------------------------------------------------
    w = W('holidchain', 'The chain from X to Y in N steps: a holomorphic function vanishing on the disc of radius R / 2 about a point X of the nested rectangle vanishes on the disc of radius R / 2 about every point X + ( k / N ) ( Y - X ) , 0 <_ k <_ N , when the step ( abs ` ( Y - X ) ) / N is less than R / 2.')
    AYX = '( abs ` ( Y - X ) )'
    TRIP = '( X e. ( A crect B ) /\\ Y e. ( A crect B ) /\\ N e. NN )'
    LAST = '( ( %s / N ) < %s /\\ %s )' % (AYX, RH, HALFZ('X'))
    A0 = '( %s /\\ %s /\\ %s )' % (HAN, TRIP, LAST)
    han = w.s([], 'simp1', '( %s -> %s )' % (A0, HAN))
    trip = w.s([], 'simp2', '( %s -> %s )' % (A0, TRIP))
    last = w.s([], 'simp3', '( %s -> %s )' % (A0, LAST))
    xin = w.s([trip, w.inst('simp1')], 'syl', '( %s -> X e. ( A crect B ) )' % A0)
    yin = w.s([trip, w.inst('simp2')], 'syl', '( %s -> Y e. ( A crect B ) )' % A0)
    nn = w.s([trip, w.inst('simp3')], 'syl', '( %s -> N e. NN )' % A0)
    ltn = w.s([last, w.inst('simpl')], 'syl', '( %s -> ( %s / N ) < %s )' % (A0, AYX, RH))
    hx = w.s([last, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, HALFZ('X')))
    d = hanctx(w, A0, han)
    xc = w.s([d['crss'], xin], 'sseldd', '( %s -> X e. CC )' % A0)
    yc = w.s([d['crss'], yin], 'sseldd', '( %s -> Y e. CC )' % A0)
    yx = w.s([yc, xc], 'subcld', '( %s -> ( Y - X ) e. CC )' % A0)
    nc = w.s([nn], 'nncnd', '( %s -> N e. CC )' % A0)
    nne = w.s([nn], 'nnne0d', '( %s -> N =/= 0 )' % A0)
    # the substitution hypotheses
    h1 = ptsub(w, 't', '0'); h2 = ptsub(w, 't', 'm'); h3 = ptsub(w, 't', '( m + 1 )'); h4 = ptsub(w, 't', 'k')
    # base
    z = w.s([nc, nne, w.inst('div0')], 'syl2anc', '( %s -> ( 0 / N ) = 0 )' % A0)
    b1 = w.s([w.s([w.s([z], 'oveq1d', '( %s -> ( ( 0 / N ) x. ( Y - X ) ) = ( 0 x. ( Y - X ) ) )' % A0), w.s([yx], 'mul02d', '( %s -> ( 0 x. ( Y - X ) ) = 0 )' % A0)], 'eqtrd', '( %s -> ( ( 0 / N ) x. ( Y - X ) ) = 0 )' % A0)], 'oveq2d',
             '( %s -> %s = ( X + 0 ) )' % (A0, PT('0')))
    b2 = w.s([b1, w.s([xc], 'addridd', '( %s -> ( X + 0 ) = X )' % A0)], 'eqtrd', '( %s -> %s = X )' % (A0, PT('0')))
    h5 = w.s([w.s([b2, halfzeq(w, PT('0'), 'X')], 'syl', '( %s -> ( %s <-> %s ) )' % (A0, HALFZ(PT('0')), HALFZ('X'))), hx], 'mpbird', '( %s -> %s )' % (A0, HALFZ(PT('0'))))
    # step
    MT = '( m e. ZZ /\\ 0 <_ m /\\ m < N )'
    B0 = '( %s /\\ %s /\\ %s )' % (A0, MT, HALFZ(PT('m')))
    a0 = w.s([], 'simp1', '( %s -> %s )' % (B0, A0))
    mt = w.s([], 'simp2', '( %s -> %s )' % (B0, MT))
    hm = w.s([], 'simp3', '( %s -> %s )' % (B0, HALFZ(PT('m'))))
    mz = w.s([mt, w.inst('simp1')], 'syl', '( %s -> m e. ZZ )' % B0)
    m0 = w.s([mt, w.inst('simp2')], 'syl', '( %s -> 0 <_ m )' % B0)
    mlt = w.s([mt, w.inst('simp3')], 'syl', '( %s -> m < N )' % B0)
    def L(st, f):
        return w.s([a0, st], 'syl', '( %s -> %s )' % (B0, f))
    xcb = L(xc, 'X e. CC'); ycb = L(yc, 'Y e. CC'); yxb = L(yx, '( Y - X ) e. CC'); ncb = L(nc, 'N e. CC'); nneb = L(nne, 'N =/= 0')
    nnb = L(nn, 'N e. NN'); xinb = L(xin, 'X e. ( A crect B )'); yinb = L(yin, 'Y e. ( A crect B )'); hanb = L(han, HAN); abb = L(d['ab'], AB); ltnb = L(ltn, '( %s / N ) < %s' % (AYX, RH))
    nr = w.s([nnb], 'nnred', '( %s -> N e. RR )' % B0)
    nrp = w.s([nnb], 'nnrpd', '( %s -> N e. RR+ )' % B0)
    n0 = w.s([nnb], 'nngt0d', '( %s -> 0 < N )' % B0)
    mr = w.s([mz], 'zred', '( %s -> m e. RR )' % B0)
    mc = w.s([mr], 'recnd', '( %s -> m e. CC )' % B0)
    m1r = w.s([mr, closed(w, B0, '1re', '1 e. RR')], 'readdcld', '( %s -> ( m + 1 ) e. RR )' % B0)
    m1c = w.s([m1r], 'recnd', '( %s -> ( m + 1 ) e. CC )' % B0)
    one = closed(w, B0, '1re', '1 e. RR'); zr = closed(w, B0, '0re', '0 e. RR')
    m10 = w.s([mr, one, m0, closed(w, B0, '0le1', '0 <_ 1')], 'addge0d', '( %s -> 0 <_ ( m + 1 ) )' % B0)
    mle = w.s([mr, nr, mlt], 'ltled', '( %s -> m <_ N )' % B0)
    m1le = w.s([w.s([mz, w.s([nnb], 'nnzd', '( %s -> N e. ZZ )' % B0), w.inst('zltp1le')], 'syl2anc', '( %s -> ( m < N <-> ( m + 1 ) <_ N ) )' % B0), mlt], 'mpbid', '( %s -> ( m + 1 ) <_ N )' % B0)
    def inrect(E, er, e0, ele):
        Q = '( %s / N )' % E
        qr = w.s([er, nr, nneb], 'redivcld', '( %s -> %s e. RR )' % (B0, Q))
        q0 = w.s([w.s([w.s([er, e0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (B0, E, E)), w.s([nr, n0], 'jca', '( %s -> ( N e. RR /\\ 0 < N ) )' % B0)], 'jca', '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( N e. RR /\\ 0 < N ) ) )' % (B0, E, E)), w.inst('divge0')], 'syl',
                 '( %s -> 0 <_ %s )' % (B0, Q))
        q1 = w.s([w.s([er, nrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> %s <_ N ) )' % (B0, Q, E)), ele], 'mpbird', '( %s -> %s <_ 1 )' % (B0, Q))
        q01 = w.s([w.s([qr, q0, q1], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (B0, Q, Q, Q)), w.s([zr, one, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) ) )' % (B0, Q, Q, Q, Q))], 'mpbird',
                  '( %s -> %s e. ( 0 [,] 1 ) )' % (B0, Q))
        seg = w.s([xcb, ycb, q01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( X cseg Y ) )' % (B0, PT(E)))
        cvx = w.s([abb, w.s([xinb, yinb], 'jca', '( %s -> ( X e. ( A crect B ) /\\ Y e. ( A crect B ) ) )' % B0), w.inst('crectcvx')], 'syl2anc', '( %s -> ( X cseg Y ) C_ ( A crect B ) )' % B0)
        return w.s([cvx, seg], 'sseldd', '( %s -> %s e. ( A crect B ) )' % (B0, PT(E))), qr
    pm, qr = inrect('m', mr, m0, mle)
    pm1, q1r = inrect('( m + 1 )', m1r, m10, m1le)
    QM = '( m / N )'; QM1 = '( ( m + 1 ) / N )'
    qmc = w.s([qr], 'recnd', '( %s -> %s e. CC )' % (B0, QM)); qm1c = w.s([q1r], 'recnd', '( %s -> %s e. CC )' % (B0, QM1))
    p1 = w.s([xcb, w.s([qm1c, yxb], 'mulcld', '( %s -> ( %s x. ( Y - X ) ) e. CC )' % (B0, QM1)), w.s([qmc, yxb], 'mulcld', '( %s -> ( %s x. ( Y - X ) ) e. CC )' % (B0, QM))], 'pnpcand',
             '( %s -> ( %s - %s ) = ( ( %s x. ( Y - X ) ) - ( %s x. ( Y - X ) ) ) )' % (B0, PT('( m + 1 )'), PT('m'), QM1, QM))
    p2 = w.s([w.s([qm1c, qmc, yxb], 'subdird', '( %s -> ( ( %s - %s ) x. ( Y - X ) ) = ( ( %s x. ( Y - X ) ) - ( %s x. ( Y - X ) ) ) )' % (B0, QM1, QM, QM1, QM))], 'eqcomd',
             '( %s -> ( ( %s x. ( Y - X ) ) - ( %s x. ( Y - X ) ) ) = ( ( %s - %s ) x. ( Y - X ) ) )' % (B0, QM1, QM, QM1, QM))
    p3 = w.s([w.s([m1c, mc, ncb, nneb], 'divsubdird', '( %s -> ( ( ( m + 1 ) - m ) / N ) = ( %s - %s ) )' % (B0, QM1, QM))], 'eqcomd', '( %s -> ( %s - %s ) = ( ( ( m + 1 ) - m ) / N ) )' % (B0, QM1, QM))
    p4 = w.s([w.s([mc, closed(w, B0, 'ax-1cn', '1 e. CC')], 'pncan2d', '( %s -> ( ( m + 1 ) - m ) = 1 )' % B0)], 'oveq1d', '( %s -> ( ( ( m + 1 ) - m ) / N ) = ( 1 / N ) )' % B0)
    p5 = w.s([w.s([p3, p4], 'eqtrd', '( %s -> ( %s - %s ) = ( 1 / N ) )' % (B0, QM1, QM))], 'oveq1d', '( %s -> ( ( %s - %s ) x. ( Y - X ) ) = ( ( 1 / N ) x. ( Y - X ) ) )' % (B0, QM1, QM))
    diff = w.s([p1, w.s([p2, p5], 'eqtrd', '( %s -> ( ( %s x. ( Y - X ) ) - ( %s x. ( Y - X ) ) ) = ( ( 1 / N ) x. ( Y - X ) ) )' % (B0, QM1, QM))], 'eqtrd',
               '( %s -> ( %s - %s ) = ( ( 1 / N ) x. ( Y - X ) ) )' % (B0, PT('( m + 1 )'), PT('m')))
    rn = w.s([nrp], 'rpreccld', '( %s -> ( 1 / N ) e. RR+ )' % B0)
    rnc = w.s([w.s([rn], 'rpred', '( %s -> ( 1 / N ) e. RR )' % B0)], 'recnd', '( %s -> ( 1 / N ) e. CC )' % B0)
    a1 = w.s([rnc, yxb], 'absmuld', '( %s -> ( abs ` ( ( 1 / N ) x. ( Y - X ) ) ) = ( ( abs ` ( 1 / N ) ) x. %s ) )' % (B0, AYX))
    a2 = w.s([w.s([w.s([rn], 'rpred', '( %s -> ( 1 / N ) e. RR )' % B0), w.s([rn], 'rpge0d', '( %s -> 0 <_ ( 1 / N ) )' % B0)], 'absidd', '( %s -> ( abs ` ( 1 / N ) ) = ( 1 / N ) )' % B0)], 'oveq1d',
             '( %s -> ( ( abs ` ( 1 / N ) ) x. %s ) = ( ( 1 / N ) x. %s ) )' % (B0, AYX, AYX))
    ayxc = w.s([w.s([yxb], 'abscld', '( %s -> %s e. RR )' % (B0, AYX))], 'recnd', '( %s -> %s e. CC )' % (B0, AYX))
    a3 = w.s([w.s([w.s([ayxc, ncb, nneb], 'divrecd', '( %s -> ( %s / N ) = ( %s x. ( 1 / N ) ) )' % (B0, AYX, AYX)), w.s([ayxc, rnc], 'mulcomd', '( %s -> ( %s x. ( 1 / N ) ) = ( ( 1 / N ) x. %s ) )' % (B0, AYX, AYX))], 'eqtrd',
                  '( %s -> ( %s / N ) = ( ( 1 / N ) x. %s ) )' % (B0, AYX, AYX))], 'eqcomd', '( %s -> ( ( 1 / N ) x. %s ) = ( %s / N ) )' % (B0, AYX, AYX))
    absd = w.s([w.s([diff], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( ( 1 / N ) x. ( Y - X ) ) ) )' % (B0, PT('( m + 1 )'), PT('m'))), w.s([a1, w.s([a2, a3], 'eqtrd', '( %s -> ( ( abs ` ( 1 / N ) ) x. %s ) = ( %s / N ) )' % (B0, AYX, AYX))], 'eqtrd',
                                                                                                                                                       '( %s -> ( abs ` ( ( 1 / N ) x. ( Y - X ) ) ) = ( %s / N ) )' % (B0, AYX))], 'eqtrd',
               '( %s -> ( abs ` ( %s - %s ) ) = ( %s / N ) )' % (B0, PT('( m + 1 )'), PT('m'), AYX))
    dlt = w.s([absd, ltnb], 'eqbrtrd', '( %s -> ( abs ` ( %s - %s ) ) < %s )' % (B0, PT('( m + 1 )'), PT('m'), RH))
    h6 = w.s([hanb, w.s([pm, pm1, dlt], '3jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) /\\ ( abs ` ( %s - %s ) ) < %s ) )' % (B0, PT('m'), PT('( m + 1 )'), PT('( m + 1 )'), PT('m'), RH)), hm, w.inst('holidstep')], 'syl3anc',
             '( %s -> %s )' % (B0, HALFZ(PT('( m + 1 )'))))
    h7 = closed(w, A0, '0z', '0 e. ZZ')
    h8 = w.s([nn], 'nnzd', '( %s -> N e. ZZ )' % A0)
    h9 = w.s([w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)], 'nn0ge0d', '( %s -> 0 <_ N )' % A0)
    KT = '( k e. ZZ /\\ 0 <_ k /\\ k <_ N )'
    ind = w.s([h1, h2, h3, h4, h5, h6, h7, h8, h9], 'fzindd', '( ( %s /\\ %s ) -> %s )' % (A0, KT, HALFZ(PT('k'))))
    kt = w.s([w.s([], 'elfzelz', '( k e. ( 0 ... N ) -> k e. ZZ )'), w.s([], 'elfzle1', '( k e. ( 0 ... N ) -> 0 <_ k )'), w.s([], 'elfzle2', '( k e. ( 0 ... N ) -> k <_ N )')], '3jca', '( k e. ( 0 ... N ) -> %s )' % KT)
    fin = w.s([kt, ind], 'sylan2', '( ( %s /\\ k e. ( 0 ... N ) ) -> %s )' % (A0, HALFZ(PT('k'))))
    w.qed([fin], 'ralrimiva', '( %s -> A. k e. ( 0 ... N ) %s )' % (A0, HALFZ(PT('k'))))
    run1(w)

    # ---- holidrect ------------------------------------------------------------------
    w = W('holidrect', 'The identity theorem on a rectangle: a holomorphic function on an open set containing the rectangle enlarged by R that vanishes on some disc about a point of the rectangle vanishes on the whole rectangle.')
    VANS = 'E. s e. RR+ %s' % VAN('X', 's')
    A0 = '( %s /\\ ( X e. ( A crect B ) /\\ %s ) )' % (ABGEO, VANS)
    abg = w.s([], 'simpl', '( %s -> %s )' % (A0, ABGEO))
    xv = w.s([], 'simpr', '( %s -> ( X e. ( A crect B ) /\\ %s ) )' % (A0, VANS))
    xin = w.s([xv, w.inst('simpl')], 'syl', '( %s -> X e. ( A crect B ) )' % A0)
    vans = w.s([xv, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, VANS))
    d = abgeoctx(w, A0, abg)
    hx = w.s([w.s([d['han'], xin], 'jca', '( %s -> ( %s /\\ X e. ( A crect B ) ) )' % (A0, HAN)), vans, w.inst('holnid2')], 'syl2anc', '( %s -> %s )' % (A0, HALFZ('X')))
    xc = w.s([d['crss'], xin], 'sseldd', '( %s -> X e. CC )' % A0)
    A1 = '( %s /\\ y e. ( A crect B ) )' % A0
    yin = w.s([], 'simpr', '( %s -> y e. ( A crect B ) )' % A1)
    yc = w.s([w.s([d['crss']], 'adantr', '( %s -> ( A crect B ) C_ CC )' % A1), yin], 'sseldd', '( %s -> y e. CC )' % A1)
    xc1 = w.s([xc], 'adantr', '( %s -> X e. CC )' % A1)
    AYX = '( abs ` ( y - X ) )'
    ayx = w.s([w.s([yc, xc1], 'subcld', '( %s -> ( y - X ) e. CC )' % A1)], 'abscld', '( %s -> %s e. RR )' % (A1, AYX))
    hr = w.s([w.s([d['Rrp']], 'adantr', '( %s -> R e. RR+ )' % A1)], 'rphalfcld', '( %s -> %s e. RR+ )' % (A1, RH))
    Q = '( %s / %s )' % (AYX, RH)
    qr = w.s([ayx, hr], 'rerpdivcld', '( %s -> %s e. RR )' % (A1, Q))
    ex = w.s([qr, w.inst('arch')], 'syl', '( %s -> E. n e. NN %s < n )' % (A1, Q))
    A2 = '( %s /\\ ( n e. NN /\\ %s < n ) )' % (A1, Q)
    nn = w.s([w.s([], 'simpr', '( %s -> ( n e. NN /\\ %s < n ) )' % (A2, Q)), w.inst('simpl')], 'syl', '( %s -> n e. NN )' % A2)
    qlt = w.s([w.s([], 'simpr', '( %s -> ( n e. NN /\\ %s < n ) )' % (A2, Q)), w.inst('simpr')], 'syl', '( %s -> %s < n )' % (A2, Q))
    nr = w.s([nn], 'nnred', '( %s -> n e. RR )' % A2); n0 = w.s([nn], 'nngt0d', '( %s -> 0 < n )' % A2)
    ayx2 = w.s([ayx], 'adantr', '( %s -> %s e. RR )' % (A2, AYX))
    hr2 = w.s([hr], 'adantr', '( %s -> %s e. RR+ )' % (A2, RH))
    ltn = w.s([qlt, w.s([ayx2, w.s([nr, n0], 'jca', '( %s -> ( n e. RR /\\ 0 < n ) )' % A2), w.s([w.s([hr2], 'rpred', '( %s -> %s e. RR )' % (A2, RH)), w.s([hr2], 'rpgt0d', '( %s -> 0 < %s )' % (A2, RH))], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A2, RH, RH)), w.inst('ltdiv23')], 'syl3anc',
                         '( %s -> ( ( %s / n ) < %s <-> %s < n ) )' % (A2, AYX, RH, Q))], 'mpbird', '( %s -> ( %s / n ) < %s )' % (A2, AYX, RH))
    han2 = w.s([d['han']], 'ad2antrr', '( %s -> %s )' % (A2, HAN))
    xin2 = w.s([xin], 'ad2antrr', '( %s -> X e. ( A crect B ) )' % A2)
    yin2 = w.s([yin], 'adantr', '( %s -> y e. ( A crect B ) )' % A2)
    hx2 = w.s([hx], 'ad2antrr', '( %s -> %s )' % (A2, HALFZ('X')))
    chain = w.s([han2, w.s([xin2, yin2, nn], '3jca', '( %s -> ( X e. ( A crect B ) /\\ y e. ( A crect B ) /\\ n e. NN ) )' % A2), w.s([ltn, hx2], 'jca', '( %s -> ( ( %s / n ) < %s /\\ %s ) )' % (A2, AYX, RH, HALFZ('X'))), w.inst('holidchain')], 'syl3anc',
                '( %s -> A. k e. ( 0 ... n ) %s )' % (A2, HALFZ(PT('k', 'y', 'n'))))
    nfz = w.s([w.s([nn], 'nnnn0d', '( %s -> n e. NN0 )' % A2), w.inst('nn0fz0')], 'sylib', '( %s -> n e. ( 0 ... n ) )' % A2)
    hn = w.s([ptsub(w, 'k', 'n', 'y', 'n'), chain, nfz], 'rspcdva', '( %s -> %s )' % (A2, HALFZ(PT('n', 'y', 'n'))))
    nc = w.s([nn], 'nncnd', '( %s -> n e. CC )' % A2); nne = w.s([nn], 'nnne0d', '( %s -> n =/= 0 )' % A2)
    yc2 = w.s([yc], 'adantr', '( %s -> y e. CC )' % A2); xc2 = w.s([xc], 'ad2antrr', '( %s -> X e. CC )' % A2)
    yx2 = w.s([yc2, xc2], 'subcld', '( %s -> ( y - X ) e. CC )' % A2)
    e1 = w.s([w.s([w.s([nc, nne], 'dividd', '( %s -> ( n / n ) = 1 )' % A2)], 'oveq1d', '( %s -> ( ( n / n ) x. ( y - X ) ) = ( 1 x. ( y - X ) ) )' % A2), w.s([yx2], 'mullidd', '( %s -> ( 1 x. ( y - X ) ) = ( y - X ) )' % A2)], 'eqtrd',
             '( %s -> ( ( n / n ) x. ( y - X ) ) = ( y - X ) )' % A2)
    e2 = w.s([w.s([e1], 'oveq2d', '( %s -> %s = ( X + ( y - X ) ) )' % (A2, PT('n', 'y', 'n'))), w.s([xc2, yc2], 'pncan3d', '( %s -> ( X + ( y - X ) ) = y )' % A2)], 'eqtrd', '( %s -> %s = y )' % (A2, PT('n', 'y', 'n')))
    hy = w.s([w.s([e2, halfzeq(w, PT('n', 'y', 'n'), 'y')], 'syl', '( %s -> ( %s <-> %s ) )' % (A2, HALFZ(PT('n', 'y', 'n')), HALFZ('y'))), hn], 'mpbid', '( %s -> %s )' % (A2, HALFZ('y')))
    imp_ = w.s([halfzat(w, 'y', 'y'), hy, yc2], 'rspcdva', '( %s -> ( ( abs ` ( y - y ) ) <_ %s -> ( F ` y ) = 0 ) )' % (A2, RH))
    z0 = w.s([w.s([w.s([yc2], 'subidd', '( %s -> ( y - y ) = 0 )' % A2)], 'fveq2d', '( %s -> ( abs ` ( y - y ) ) = ( abs ` 0 ) )' % A2), closed(w, A2, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( %s -> ( abs ` ( y - y ) ) = 0 )' % A2)
    le = w.s([z0, w.s([hr2], 'rpge0d', '( %s -> 0 <_ %s )' % (A2, RH))], 'eqbrtrd', '( %s -> ( abs ` ( y - y ) ) <_ %s )' % (A2, RH))
    fy0 = w.s([le, imp_], 'mpd', '( %s -> ( F ` y ) = 0 )' % A2)
    fy = w.s([ex, fy0], 'rexlimddv', '( %s -> ( F ` y ) = 0 )' % A1)
    w.qed([fy], 'ralrimiva', '( %s -> A. y e. ( A crect B ) ( F ` y ) = 0 )' % A0)
    run1(w)

    # ---- holnfac2 -------------------------------------------------------------------
    w = W('holnfac2', 'The local factorisation at every point of a rectangle on which a holomorphic function is not identically zero: F is ( z - X ) ^ n times a function holomorphic on the open set and nonzero at X, for some n.')
    A0 = '( %s /\\ X e. ( A crect B ) )' % ABNZ
    abnz = w.s([], 'simpl', '( %s -> %s )' % (A0, ABNZ))
    abg = w.s([abnz, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ABGEO))
    nz = w.s([abnz, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, NZ))
    xin = w.s([], 'simpr', '( %s -> X e. ( A crect B ) )' % A0)
    d = abgeoctx(w, A0, abg)
    A1 = '( %s /\\ %s )' % (A0, HALFZ('X'))
    A2 = '( %s /\\ v e. D )' % A1
    A3 = '( %s /\\ ( abs ` ( v - X ) ) < %s )' % (A2, RH)
    vd = w.s([w.s([], 'simpr', '( %s -> v e. D )' % A2)], 'adantr', '( %s -> v e. D )' % A3)
    vc = w.s([w.s([d['dss']], 'ad3antrrr', '( %s -> D C_ CC )' % A3), vd], 'sseldd', '( %s -> v e. CC )' % A3)
    xc3 = w.s([w.s([d['crss'], xin], 'sseldd', '( %s -> X e. CC )' % A0)], 'ad3antrrr', '( %s -> X e. CC )' % A3)
    avx = w.s([w.s([vc, xc3], 'subcld', '( %s -> ( v - X ) e. CC )' % A3)], 'abscld', '( %s -> ( abs ` ( v - X ) ) e. RR )' % A3)
    hr = w.s([d['Rrp']], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, RH))
    le = w.s([avx, w.s([w.s([hr], 'ad3antrrr', '( %s -> %s e. RR+ )' % (A3, RH))], 'rpred', '( %s -> %s e. RR )' % (A3, RH)), w.s([], 'simpr', '( %s -> ( abs ` ( v - X ) ) < %s )' % (A3, RH))], 'ltled', '( %s -> ( abs ` ( v - X ) ) <_ %s )' % (A3, RH))
    imp_ = w.s([halfzat(w, 'X', 'v'), w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, HALFZ('X')))], 'ad2antrr', '( %s -> %s )' % (A3, HALFZ('X'))), vc], 'rspcdva', '( %s -> ( ( abs ` ( v - X ) ) <_ %s -> ( F ` v ) = 0 ) )' % (A3, RH))
    fv0 = w.s([le, imp_], 'mpd', '( %s -> ( F ` v ) = 0 )' % A3)
    VANV = 'A. v e. D ( ( abs ` ( v - X ) ) < %s -> ( F ` v ) = 0 )' % RH
    ralv = w.s([w.s([fv0], 'ex', '( %s -> ( ( abs ` ( v - X ) ) < %s -> ( F ` v ) = 0 ) )' % (A2, RH))], 'ralrimiva', '( %s -> %s )' % (A1, VANV))
    cb = w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( v = w -> ( v - X ) = ( w - X ) )')], 'fveq2d', '( v = w -> ( abs ` ( v - X ) ) = ( abs ` ( w - X ) ) )')], 'breq1d', '( v = w -> ( ( abs ` ( v - X ) ) < %s <-> ( abs ` ( w - X ) ) < %s ) )' % (RH, RH)),
                   w.s([w.s([], 'fveq2', '( v = w -> ( F ` v ) = ( F ` w ) )')], 'eqeq1d', '( v = w -> ( ( F ` v ) = 0 <-> ( F ` w ) = 0 ) )')], 'imbi12d',
                  '( v = w -> ( ( ( abs ` ( v - X ) ) < %s -> ( F ` v ) = 0 ) <-> ( ( abs ` ( w - X ) ) < %s -> ( F ` w ) = 0 ) ) )' % (RH, RH))], 'cbvralvw', '( %s <-> %s )' % (VANV, VAN('X', RH)))
    van = w.s([ralv, cb], 'sylib', '( %s -> %s )' % (A1, VAN('X', RH)))
    ssub = w.s([w.s([w.s([], 'breq2', '( s = %s -> ( ( abs ` ( w - X ) ) < s <-> ( abs ` ( w - X ) ) < %s ) )' % (RH, RH))], 'imbi1d', '( s = %s -> ( ( ( abs ` ( w - X ) ) < s -> ( F ` w ) = 0 ) <-> ( ( abs ` ( w - X ) ) < %s -> ( F ` w ) = 0 ) ) )' % (RH, RH))], 'ralbidv',
               '( s = %s -> ( %s <-> %s ) )' % (RH, VAN('X', 's'), VAN('X', RH)))
    VANS = 'E. s e. RR+ %s' % VAN('X', 's')
    exs = w.s([w.s([hr], 'adantr', '( %s -> %s e. RR+ )' % (A1, RH)), van, w.s([ssub], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> %s )' % (RH, VAN('X', RH), VANS))], 'syl2anc', '( %s -> %s )' % (A1, VANS))
    all0 = w.s([w.s([abg], 'adantr', '( %s -> %s )' % (A1, ABGEO)), w.s([w.s([xin], 'adantr', '( %s -> X e. ( A crect B ) )' % A1), exs], 'jca', '( %s -> ( X e. ( A crect B ) /\\ %s ) )' % (A1, VANS)), w.inst('holidrect')], 'syl2anc',
               '( %s -> A. y e. ( A crect B ) ( F ` y ) = 0 )' % A1)
    cb2 = w.s([w.s([w.s([], 'fveq2', '( y = w -> ( F ` y ) = ( F ` w ) )')], 'eqeq1d', '( y = w -> ( ( F ` y ) = 0 <-> ( F ` w ) = 0 ) )')], 'cbvralvw', '( A. y e. ( A crect B ) ( F ` y ) = 0 <-> A. w e. ( A crect B ) ( F ` w ) = 0 )')
    allw = w.s([all0, cb2], 'sylib', '( %s -> A. w e. ( A crect B ) ( F ` w ) = 0 )' % A1)
    nn_ = w.s([w.s([], 'nne', '( -. ( F ` w ) =/= 0 <-> ( F ` w ) = 0 )')], 'ralbii', '( A. w e. ( A crect B ) -. ( F ` w ) =/= 0 <-> A. w e. ( A crect B ) ( F ` w ) = 0 )')
    alln = w.s([allw, nn_], 'sylibr', '( %s -> A. w e. ( A crect B ) -. ( F ` w ) =/= 0 )' % A1)
    nnz = w.s([alln, w.s([], 'ralnex', '( A. w e. ( A crect B ) -. ( F ` w ) =/= 0 <-> -. %s )' % NZ)], 'sylib', '( %s -> -. %s )' % (A1, NZ))
    nh = w.s([w.s([nz], 'adantr', '( %s -> %s )' % (A1, NZ)), nnz], 'pm2.65da', '( %s -> -. %s )' % (A0, HALFZ('X')))
    w.qed([w.s([d['han'], xin], 'jca', '( %s -> ( %s /\\ X e. ( A crect B ) ) )' % (A0, HAN)), nh, w.inst('holnfac')], 'syl2anc', '( %s -> %s )' % (A0, EXFAC('X')))
    run1(w)
