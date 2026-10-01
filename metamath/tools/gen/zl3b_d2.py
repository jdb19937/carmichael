"""ZL3b D2: the residue of H / E at a simple zero P of E on a rectangle (zl3qvp, zl3res),
and its instance at the poles i N of 1 / ( e ^ ( 2 pi w ) - 1 ) (zl3resn).
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_d2.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of, twopi, TP, MP

only = sys.argv[1:]
S = STATEMENTS

HOLF = '( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) )'
ABC = '( A e. CC /\\ B e. CC )'
PST = '( P e. CC /\\ %s )' % STRICT('A', 'B', 'P')
RECT = '( %s /\\ %s /\\ ( A crect B ) C_ D )' % (ABC, PST)
RRC = '( ( R e. RR /\\ %s ) /\\ 0 < R )' % RCOND('A', 'B', 'P', 'R')
MMC = '( M e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ M )' % FRAME('A', 'B')
assert HOLQCTX == '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (HOLF, RECT, RRC, MMC)
CDEF = HYPS['zl3qvp'][0][1][4:]
QDEF = HYPS['zl3qvp'][1][1][4:]
TWOPI_I = '( 2 x. ( _i x. _pi ) )'
TT = '( ( TopOpen ` CCfld ) |`t CC )'


def qvp_core(w, ph, ctx, fp0, cname, qname, crefs):
    """the body of zl3qvp; crefs = (hc, hq) hypothesis step names for the .c/.q of holqhol etc.
    returns (qhol, qval) steps"""
    hc, hq = crefs
    holf = w.s([ctx, w.inst('simpll')], 'syl', '( %s -> %s )' % (ph, HOLF))
    rect = w.s([ctx, w.inst('simplr')], 'syl', '( %s -> %s )' % (ph, RECT))
    fcn = w.s([holf, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % ph)
    dss = w.s([holf, w.inst('simpr')], 'syl', '( %s -> D C_ dom ( CC _D F ) )' % ph)
    ab = w.s([rect, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, ABC))
    pst = w.s([rect, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, PST))
    rss = w.s([rect, w.inst('simp3')], 'syl', '( %s -> ( A crect B ) C_ D )' % ph)
    crd = D(w, ph, 'sstrd', [rss, dss], '( A crect B ) C_ dom ( CC _D F )')
    h3 = w.s([ab, pst, D(w, ph, 'jca', [fcn, crd], '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) )')], '3jca',
             '( %s -> ( %s /\\ %s /\\ ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) ) ) )' % (ph, ABC, PST))
    H3 = '( %s /\\ %s /\\ ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) ) )' % (ABC, PST)
    c0i = w.s([hc], 'holc0', '( %s -> ( %s ` 0 ) = ( %s x. ( F ` P ) ) )' % (H3, cname, TWOPI_I))
    c0 = w.s([h3, c0i], 'syl', '( %s -> ( %s ` 0 ) = ( %s x. ( F ` P ) ) )' % (ph, cname, TWOPI_I))
    c01 = D(w, ph, 'oveq2d', [fp0], '( %s x. ( F ` P ) ) = ( %s x. 0 )' % (TWOPI_I, TWOPI_I))
    tpic = w.s([w.s([], '2cnd', '( %s -> 2 e. CC )' % ph), w.s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % ph),
                                                              w.s([w.s([], 'picn', '_pi e. CC')], 'a1i', '( %s -> _pi e. CC )' % ph)], 'mulcld', '( %s -> ( _i x. _pi ) e. CC )' % ph)],
               'mulcld', '( %s -> %s e. CC )' % (ph, TWOPI_I))
    c02 = D(w, ph, 'mul01d', [tpic], '( %s x. 0 ) = 0' % TWOPI_I)
    c00 = D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [c0, c01], '( %s ` 0 ) = ( %s x. 0 )' % (cname, TWOPI_I)), c02], '( %s ` 0 ) = 0' % cname)
    rq1 = w.s([w.s([], 'fzo01', '( 0 ..^ 1 ) = { 0 }')], 'raleqi', '( A. i e. ( 0 ..^ 1 ) ( %s ` i ) = 0 <-> A. i e. { 0 } ( %s ` i ) = 0 )' % (cname, cname))
    rq2 = w.s([w.s([], 'c0ex', '0 e. _V'), w.s([], 'fveqeq2', '( i = 0 -> ( ( %s ` i ) = 0 <-> ( %s ` 0 ) = 0 ) )' % (cname, cname))], 'ralsn',
              '( A. i e. { 0 } ( %s ` i ) = 0 <-> ( %s ` 0 ) = 0 )' % (cname, cname))
    rq = w.s([rq1, rq2], 'bitri', '( A. i e. ( 0 ..^ 1 ) ( %s ` i ) = 0 <-> ( %s ` 0 ) = 0 )' % (cname, cname))
    ral = w.s([c00, rq], 'sylibr', '( %s -> A. i e. ( 0 ..^ 1 ) ( %s ` i ) = 0 )' % (ph, cname))
    one = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % ph)
    hq_ante = D(w, ph, 'jca', [ctx, D(w, ph, 'jca', [one, ral], '( 1 e. NN /\\ A. i e. ( 0 ..^ 1 ) ( %s ` i ) = 0 )' % cname)],
                '( %s /\\ ( 1 e. NN /\\ A. i e. ( 0 ..^ 1 ) ( %s ` i ) = 0 ) )' % (HOLQCTX, cname))
    HQA = '( %s /\\ ( 1 e. NN /\\ A. i e. ( 0 ..^ 1 ) ( %s ` i ) = 0 ) )' % (HOLQCTX, cname)
    QH = '( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) )' % (qname, qname)
    QR = '( %s |` ( D \\ { P } ) ) = ( z e. ( D \\ { P } ) |-> ( ( F ` z ) / ( ( z - P ) ^ 1 ) ) )' % qname
    qhol = w.s([hq_ante, w.s([hc, hq], 'holqhol', '( %s -> %s )' % (HQA, QH))], 'syl', '( %s -> %s )' % (ph, QH))
    qres = w.s([hq_ante, w.s([hc, hq], 'holqres', '( %s -> %s )' % (HQA, QR))], 'syl', '( %s -> %s )' % (ph, QR))
    # the quotient map equals eldv's difference quotient
    A1 = '( %s /\\ z e. ( D \\ { P } ) )' % ph
    zD = w.s([w.s([], 'simpr', '( %s -> z e. ( D \\ { P } ) )' % A1), w.inst('eldifi')], 'syl', '( %s -> z e. D )' % A1)
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % ph)
    zc = D(w, A1, 'sseldd', [w.s([dcc], 'adantr', '( %s -> D C_ CC )' % A1), zD], 'z e. CC')
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % ph)
    fzc = D(w, A1, 'ffvelcdmd', [w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zD], '( F ` z ) e. CC')
    pc = w.s([pst, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % ph)
    zpc = D(w, A1, 'subcld', [zc, w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)], '( z - P ) e. CC')
    e1 = D(w, A1, 'exp1d', [zpc], '( ( z - P ) ^ 1 ) = ( z - P )')
    f0 = w.s([fp0], 'adantr', '( %s -> ( F ` P ) = 0 )' % A1)
    s1 = D(w, A1, 'oveq2d', [f0], '( ( F ` z ) - ( F ` P ) ) = ( ( F ` z ) - 0 )')
    s2 = D(w, A1, 'subid1d', [fzc], '( ( F ` z ) - 0 ) = ( F ` z )')
    s3 = D(w, A1, 'eqtr2d', [s1, s2], '( F ` z ) = ( ( F ` z ) - ( F ` P ) )')
    s4 = D(w, A1, 'oveq12d', [s3, e1], '( ( F ` z ) / ( ( z - P ) ^ 1 ) ) = ( ( ( F ` z ) - ( F ` P ) ) / ( z - P ) )')
    G = '( z e. ( D \\ { P } ) |-> ( ( ( F ` z ) - ( F ` P ) ) / ( z - P ) ) )'
    meq = w.s([s4], 'mpteq2dva', '( %s -> ( z e. ( D \\ { P } ) |-> ( ( F ` z ) / ( ( z - P ) ^ 1 ) ) ) = %s )' % (ph, G))
    req = D(w, ph, 'eqtrd', [qres, meq], '( %s |` ( D \\ { P } ) ) = %s' % (qname, G))
    # Q ( P ) is the limit of the difference quotient
    qcn = w.s([qhol, w.inst('simpl')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (ph, qname))
    pin = w.s([w.s([ab, pst], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, ABC, PST)), w.inst('crectinp')], 'syl', '( %s -> P e. ( A crect B ) )' % ph)
    pD = D(w, ph, 'sseldd', [rss, pin], 'P e. D')
    ql = w.s([qcn, pD], 'cnlimci', '( %s -> ( %s ` P ) e. ( %s limCC P ) )' % (ph, qname, qname))
    qf = w.s([qcn, w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (ph, qname))
    ld = w.s([qf], 'limcdif', '( %s -> ( %s limCC P ) = ( ( %s |` ( D \\ { P } ) ) limCC P ) )' % (ph, qname, qname))
    ld2 = D(w, ph, 'oveq1d', [req], '( ( %s |` ( D \\ { P } ) ) limCC P ) = ( %s limCC P )' % (qname, G))
    qlg = D(w, ph, 'eleqtrd', [ql, D(w, ph, 'eqtrd', [ld, ld2], '( %s limCC P ) = ( %s limCC P )' % (qname, G))], '( %s ` P ) e. ( %s limCC P )' % (qname, G))
    # eldv twice
    et = w.s([], 'eqid', '%s = %s' % (TT, TT))
    ek = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
    eg = w.s([], 'eqid', '%s = %s' % (G, G))
    scc = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % ph)
    INT = '( ( int ` %s ) ` D )' % TT
    DP = '( ( CC _D F ) ` P )'
    ev1 = w.s([et, ek, eg, scc, ff, dcc], 'eldv', '( %s -> ( P ( CC _D F ) %s <-> ( P e. %s /\\ %s e. ( %s limCC P ) ) ) )' % (ph, DP, INT, DP, G))
    ev2 = w.s([et, ek, eg, scc, ff, dcc], 'eldv', '( %s -> ( P ( CC _D F ) ( %s ` P ) <-> ( P e. %s /\\ ( %s ` P ) e. ( %s limCC P ) ) ) )' % (ph, qname, INT, qname, G))
    fun = w.s([w.s([w.s([], 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), w.inst('ffun')], 'ax-mp', 'Fun ( CC _D F )')], 'a1i', '( %s -> Fun ( CC _D F ) )' % ph)
    pdm = D(w, ph, 'sseldd', [dss, pD], 'P e. dom ( CC _D F )')
    fb = w.s([fun, w.inst('funfvbrb')], 'syl', '( %s -> ( P e. dom ( CC _D F ) <-> P ( CC _D F ) %s ) )' % (ph, DP))
    br1 = D(w, ph, 'mpbid', [pdm, fb], 'P ( CC _D F ) %s' % DP)
    int_ = w.s([D(w, ph, 'mpbid', [br1, ev1], '( P e. %s /\\ %s e. ( %s limCC P ) )' % (INT, DP, G)), w.inst('simpl')], 'syl', '( %s -> P e. %s )' % (ph, INT))
    br2 = D(w, ph, 'mpbird', [D(w, ph, 'jca', [int_, qlg], '( P e. %s /\\ ( %s ` P ) e. ( %s limCC P ) )' % (INT, qname, G)), ev2], 'P ( CC _D F ) ( %s ` P )' % qname)
    fv = w.s([fun, br2, w.inst('funbrfv')], 'sylc', '( %s -> %s = ( %s ` P ) )' % (ph, DP, qname))
    qval = D(w, ph, 'eqcomd', [fv], '( %s ` P ) = %s' % (qname, DP))
    return qhol, qval


# ---------------------------------------------------------------- zl3qvp
if __name__ == '__main__' and (not only or 'zl3qvp' in only):
    w = W('zl3qvp', 'The removable-singularity quotient ` F ( z ) / ( z - P ) ` of ~ holqhol at a zero ` P ` of ` F ` is holomorphic and takes the value ` F\' ( P ) ` at ` P `.')
    hc = hyp(w, 'c', 'zl3qvp.c', HYPS['zl3qvp'][0][1])
    hq = hyp(w, 'q', 'zl3qvp.q', HYPS['zl3qvp'][1][1])
    ph, concl = ante_of(S['zl3qvp'])
    ctx = w.s([], 'simpl', '( %s -> %s )' % (ph, HOLQCTX))
    fp0 = w.s([], 'simpr', '( %s -> ( F ` P ) = 0 )' % ph)
    qhol, qval = qvp_core(w, ph, ctx, fp0, 'C', 'Q', (hc, hq))
    w.qed([qhol, qval], 'jca', S['zl3qvp'])
    if not only or w.label in only: runh(w)


# ---------------------------------------------------------------- zl3res
def body_sub(w, ante, x, u, K, Fn='E'):
    """( ( ante /\\ x = u ) -> if ( x = P , K , ( ( E ` x ) / ( ( x - P ) ^ 1 ) ) ) = if ( u = P , K , ... u ... ) )"""
    A = '( %s /\\ %s = %s )' % (ante, x, u)
    eq = w.s([], 'simpr', '( %s -> %s = %s )' % (A, x, u))
    b1 = D(w, A, 'eqeq1d', [eq], '( %s = P <-> %s = P )' % (x, u))
    k = D(w, A, 'eqidd', [], '%s = %s' % (K, K))
    f1 = D(w, A, 'fveq2d', [eq], '( %s ` %s ) = ( %s ` %s )' % (Fn, x, Fn, u))
    d1 = D(w, A, 'oveq1d', [eq], '( %s - P ) = ( %s - P )' % (x, u))
    d2 = D(w, A, 'oveq1d', [d1], '( ( %s - P ) ^ 1 ) = ( ( %s - P ) ^ 1 )' % (x, u))
    q = D(w, A, 'oveq12d', [f1, d2], '( ( %s ` %s ) / ( ( %s - P ) ^ 1 ) ) = ( ( %s ` %s ) / ( ( %s - P ) ^ 1 ) )' % (Fn, x, x, Fn, u, u))
    return D(w, A, 'ifbieq12d', [b1, k, q], 'if ( %s = P , %s , ( ( %s ` %s ) / ( ( %s - P ) ^ 1 ) ) ) = if ( %s = P , %s , ( ( %s ` %s ) / ( ( %s - P ) ^ 1 ) ) )'
             % (x, K, Fn, x, x, u, K, Fn, u, u))


if __name__ == '__main__' and (not only or 'zl3res' in only):
    w = W('zl3res', 'The rectangle integral of ` H / E ` around a simple zero ` P ` of ` E ` is ` 2 pi i H ( P ) / E\' ( P ) ` (residue at a simple pole).')
    ph, concl = ante_of(S['zl3res'])
    HOLH = '( H e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D H ) )'
    HOLE = '( E e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D E ) )'
    RRCs = '( ( R e. RR /\\ %s ) /\\ 0 < R )' % RCOND('A', 'B', 'P', 'R')
    X1 = '( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (HOLH, HOLE, RECT, RRCs)
    ALLB = 'A. b e. D ( b =/= P -> ( E ` b ) =/= 0 )'
    PCD = '( ( CC _D E ) ` P )'
    ALLA = 'A. a e. ( ( A crect B ) \\ { P } ) ( G ` a ) = ( ( H ` a ) / ( E ` a ) )'
    X2 = '( ( ( E ` P ) = 0 /\\ %s =/= 0 ) /\\ ( %s /\\ ( G e. V /\\ %s ) ) )' % (PCD, ALLB, ALLA)
    assert ph == '( %s /\\ %s )' % (X1, X2)
    x1 = w.s([], 'simpl', '( %s -> %s )' % (ph, X1))
    x2 = w.s([], 'simpr', '( %s -> %s )' % (ph, X2))
    hh = w.s([x1, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, HOLH, HOLE))
    rr = w.s([x1, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RECT, RRCs))
    holh = w.s([hh, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, HOLH))
    hole = w.s([hh, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, HOLE))
    rect = w.s([rr, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, RECT))
    rrc = w.s([rr, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, RRCs))
    ecn = w.s([hole, w.inst('simpl')], 'syl', '( %s -> E e. ( D -cn-> CC ) )' % ph)
    ab = w.s([rect, w.inst('simp1')], 'syl', '( %s -> %s )' % (ph, ABC))
    pst = w.s([rect, w.inst('simp2')], 'syl', '( %s -> %s )' % (ph, PST))
    rss = w.s([rect, w.inst('simp3')], 'syl', '( %s -> ( A crect B ) C_ D )' % ph)
    y2a = w.s([x2, w.inst('simpl')], 'syl', '( %s -> ( ( E ` P ) = 0 /\\ %s =/= 0 ) )' % (ph, PCD))
    ep0 = w.s([y2a, w.inst('simpl')], 'syl', '( %s -> ( E ` P ) = 0 )' % ph)
    dne = w.s([y2a, w.inst('simpr')], 'syl', '( %s -> %s =/= 0 )' % (ph, PCD))
    y2b = w.s([x2, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ ( G e. V /\\ %s ) ) )' % (ph, ALLB, ALLA))
    allb = w.s([y2b, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, ALLB))
    y2c = w.s([y2b, w.inst('simpr')], 'syl', '( %s -> ( G e. V /\\ %s ) )' % (ph, ALLA))
    gv = w.s([y2c, w.inst('simpl')], 'syl', '( %s -> G e. V )' % ph)
    alla = w.s([y2c, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, ALLA))
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % ph)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % ph)
    pc = w.s([pst, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % ph)
    st = w.s([pst, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, STRICT('A', 'B', 'P')))
    sre = w.s([st, w.inst('simpl')], 'syl', '( %s -> ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` B ) ) )' % ph)
    sim = w.s([st, w.inst('simpr')], 'syl', '( %s -> ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` B ) ) )' % ph)
    rl = {}
    for X, xc in (('A', ac), ('B', bc), ('P', pc)):
        rl['r' + X] = D(w, ph, 'recld', [xc], '( Re ` %s ) e. RR' % X)
        rl['i' + X] = D(w, ph, 'imcld', [xc], '( Im ` %s ) e. RR' % X)
    le1 = D(w, ph, 'ltled', [rl['rA'], rl['rB'], D(w, ph, 'lttrd', [rl['rA'], rl['rP'], rl['rB'], w.s([sre, w.inst('simpl')], 'syl', '( %s -> ( Re ` A ) < ( Re ` P ) )' % ph),
                                                                   w.s([sre, w.inst('simpr')], 'syl', '( %s -> ( Re ` P ) < ( Re ` B ) )' % ph)], '( Re ` A ) < ( Re ` B )')],
            '( Re ` A ) <_ ( Re ` B )')
    le2 = D(w, ph, 'ltled', [rl['iA'], rl['iB'], D(w, ph, 'lttrd', [rl['iA'], rl['iP'], rl['iB'], w.s([sim, w.inst('simpl')], 'syl', '( %s -> ( Im ` A ) < ( Im ` P ) )' % ph),
                                                                   w.s([sim, w.inst('simpr')], 'syl', '( %s -> ( Im ` P ) < ( Im ` B ) )' % ph)], '( Im ` A ) < ( Im ` B )')],
            '( Im ` A ) <_ ( Im ` B )')
    GEO = '( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) )'
    geo = D(w, ph, 'jca', [le1, le2], GEO)
    fru = w.s([D(w, ph, 'jca', [ab, geo], '( %s /\\ %s )' % (ABC, GEO)), w.inst('crectfru')], 'syl', '( %s -> %s C_ ( A crect B ) )' % (ph, FRAME('A', 'B')))
    frs = D(w, ph, 'sstrd', [fru, rss], '%s C_ D' % FRAME('A', 'B'))
    BND = 'A. u e. %s ( abs ` ( E ` u ) ) <_ m' % FRAME('A', 'B')
    hfb = w.s([ab, geo, D(w, ph, 'jca', [ecn, frs], '( E e. ( D -cn-> CC ) /\\ %s C_ D )' % FRAME('A', 'B')), w.inst('holfrmbd')], 'syl3anc',
              '( %s -> E. m e. RR %s )' % (ph, BND))
    # zl3qvp at F := E, M := m, C := CT, Q := QTx
    CT = '( j e. NN0 |-> ( ( y e. ( ( A crect B ) \\ { P } ) |-> ( ( E ` y ) / ( ( y - P ) ^ ( j + 1 ) ) ) ) rectint <. A , B >. ) )'
    K = '( ( %s ` 1 ) / %s )' % (CT, TWOPI_I)
    QTx = '( x e. D |-> if ( x = P , %s , ( ( E ` x ) / ( ( x - P ) ^ 1 ) ) ) )' % K
    QTz = '( z e. D |-> if ( z = P , %s , ( ( E ` z ) / ( ( z - P ) ^ 1 ) ) ) )' % K
    hc = w.s([], 'eqid', '%s = %s' % (CT, CT))
    bs = body_sub(w, 'T.', 'x', 'z', K)   # ( ( T. /\ x = z ) -> ... )
    bs2 = w.s([bs], 'expcom', '( x = z -> ( T. -> if ( x = P , %s , ( ( E ` x ) / ( ( x - P ) ^ 1 ) ) ) = if ( z = P , %s , ( ( E ` z ) / ( ( z - P ) ^ 1 ) ) ) ) )' % (K, K))
    bs3 = w.s([w.s([], 'tru', 'T.'), bs2], 'mpi', '( x = z -> if ( x = P , %s , ( ( E ` x ) / ( ( x - P ) ^ 1 ) ) ) = if ( z = P , %s , ( ( E ` z ) / ( ( z - P ) ^ 1 ) ) ) )' % (K, K))
    hq = w.s([bs3], 'cbvmptv', '%s = %s' % (QTx, QTz))
    HQC = HOLQCTX.replace('( F ` u )', '( E ` u )').replace('<_ M )', '<_ m )').replace('M e. RR', 'm e. RR').replace('F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F )', 'E e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D E )')
    CHQ = '( ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) /\\ ( %s ` P ) = %s )' % (QTx, QTx, QTx, PCD)
    qvi = w.s([hc, hq], 'zl3qvp', '( ( %s /\\ ( E ` P ) = 0 ) -> %s )' % (HQC, CHQ))
    P3 = '( ( %s /\\ m e. RR ) /\\ %s )' % (ph, BND)
    p3a = w.s([], 'simpll', '( %s -> %s )' % (P3, ph))
    m1 = w.s([], 'simplr', '( %s -> m e. RR )' % P3)
    m2 = w.s([], 'simpr', '( %s -> %s )' % (P3, BND))
    cx = D(w, P3, 'jca', [D(w, P3, 'jca', [w.s([p3a, hole], 'syl', '( %s -> %s )' % (P3, HOLE)), w.s([p3a, rect], 'syl', '( %s -> %s )' % (P3, RECT))], '( %s /\\ %s )' % (HOLE, RECT)),
                         D(w, P3, 'jca', [w.s([p3a, rrc], 'syl', '( %s -> %s )' % (P3, RRCs)), D(w, P3, 'jca', [m1, m2], '( m e. RR /\\ %s )' % BND)], '( %s /\\ ( m e. RR /\\ %s ) )' % (RRCs, BND))],
          HQC)
    chq3 = w.s([D(w, P3, 'jca', [cx, w.s([p3a, ep0], 'syl', '( %s -> ( E ` P ) = 0 )' % P3)], '( %s /\\ ( E ` P ) = 0 )' % HQC), qvi], 'syl', '( %s -> %s )' % (P3, CHQ))
    chq4 = w.s([chq3], 'ex', '( ( %s /\\ m e. RR ) -> ( %s -> %s ) )' % (ph, BND, CHQ))
    chq5 = w.s([chq4], 'rexlimdva', '( %s -> ( E. m e. RR %s -> %s ) )' % (ph, BND, CHQ))
    chq = D(w, ph, 'mpd', [hfb, chq5], CHQ)
    QH = '( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) )' % (QTx, QTx)
    qh = w.s([chq, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, QH))
    qv = w.s([chq, w.inst('simpr')], 'syl', '( %s -> ( %s ` P ) = %s )' % (ph, QTx, PCD))
    qcn = w.s([qh, w.inst('simpl')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (ph, QTx))
    dcc = w.s([ecn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % ph)
    ef = w.s([ecn, w.inst('cncff')], 'syl', '( %s -> E : D --> CC )' % ph)
    # generic value of QTx at a point X =/= P of D
    def qval(A, X, xD, xne, lift='adantr'):
        xc = D(w, A, 'sseldd', [w.s([dcc], lift, '( %s -> D C_ CC )' % A), xD], '%s e. CC' % X)
        pcA = w.s([pc], lift, '( %s -> P e. CC )' % A)
        d1 = D(w, A, 'subcld', [xc, pcA], '( %s - P ) e. CC' % X)
        d0 = D(w, A, 'subne0d', [xc, pcA, xne], '( %s - P ) =/= 0' % X)
        e1 = D(w, A, 'exp1d', [d1], '( ( %s - P ) ^ 1 ) = ( %s - P )' % (X, X))
        exc = D(w, A, 'ffvelcdmd', [w.s([ef], lift, '( %s -> E : D --> CC )' % A), xD], '( E ` %s ) e. CC' % X)
        bsX = body_sub(w, A, 'x', X, K)
        V0 = '( ( E ` %s ) / ( ( %s - P ) ^ 1 ) )' % (X, X)
        vcl = D(w, A, 'divcld', [exc, D(w, A, 'eqeltrd', [e1, d1], '( ( %s - P ) ^ 1 ) e. CC' % X), D(w, A, 'eqnetrd', [e1, d0], '( ( %s - P ) ^ 1 ) =/= 0' % X)], '%s e. CC' % V0)
        ifc = D(w, A, 'ifcld', [w.s([w.s([], 'eqid', '%s = %s' % (K, K))], 'a1i', '( %s -> %s = %s )' % (A, K, K)) if False else None, vcl], 'x') if False else None
        nq = D(w, A, 'neneqd', [xne], '-. %s = P' % X)
        iff = w.s([nq, w.inst('iffalse')], 'syl', '( %s -> if ( %s = P , %s , %s ) = %s )' % (A, X, K, V0, V0))
        ifcl = D(w, A, 'eqeltrd', [iff, vcl], 'if ( %s = P , %s , %s ) e. CC' % (X, K, V0))
        fv = w.s([D(w, A, 'eqidd', [], '%s = %s' % (QTx, QTx)), bsX, xD, ifcl], 'fvmptd', '( %s -> ( %s ` %s ) = if ( %s = P , %s , %s ) )' % (A, QTx, X, X, K, V0))
        return D(w, A, 'eqtrd', [fv, iff], '( %s ` %s ) = %s' % (QTx, X, V0)), dict(xc=xc, d1=d1, d0=d0, e1=e1, exc=exc, V0=V0)
    # A. v e. D ( QTx ` v ) =/= 0
    A4 = '( %s /\\ v e. D )' % ph
    vD = w.s([], 'simpr', '( %s -> v e. D )' % A4)
    A4e = '( %s /\\ v = P )' % A4
    fq = D(w, A4e, 'fveq2d', [w.s([], 'simpr', '( %s -> v = P )' % A4e)], '( %s ` v ) = ( %s ` P )' % (QTx, QTx))
    ne1 = D(w, A4e, 'eqnetrd', [D(w, A4e, 'eqtrd', [fq, w.s([qv], 'adantr' if False else 'ad2antrr', '( %s -> ( %s ` P ) = %s )' % (A4e, QTx, PCD))], '( %s ` v ) = %s' % (QTx, PCD)),
                                w.s([dne], 'ad2antrr', '( %s -> %s =/= 0 )' % (A4e, PCD))], '( %s ` v ) =/= 0' % QTx)
    A4n = '( %s /\\ v =/= P )' % A4
    vne = w.s([], 'simpr', '( %s -> v =/= P )' % A4n)
    vD2 = w.s([vD], 'adantr', '( %s -> v e. D )' % A4n)
    qvv, dd = qval(A4n, 'v', vD2, vne, 'ad2antrr')
    rb = w.s([w.s([w.s([], 'neeq1', '( b = v -> ( b =/= P <-> v =/= P ) )'), w.s([w.s([], 'fveq2', '( b = v -> ( E ` b ) = ( E ` v ) )')], 'neeq1d', '( b = v -> ( ( E ` b ) =/= 0 <-> ( E ` v ) =/= 0 ) )')],
                   'imbi12d', '( b = v -> ( ( b =/= P -> ( E ` b ) =/= 0 ) <-> ( v =/= P -> ( E ` v ) =/= 0 ) ) )')], 'rspcv',
             '( v e. D -> ( %s -> ( v =/= P -> ( E ` v ) =/= 0 ) ) )' % ALLB)
    evn = w.s([vD2, w.s([allb], 'ad2antrr', '( %s -> %s )' % (A4n, ALLB)), vne, rb], 'syl3c', '( %s -> ( E ` v ) =/= 0 )' % A4n)
    ne2 = D(w, A4n, 'eqnetrd', [qvv, D(w, A4n, 'divne0d', [dd['exc'], D(w, A4n, 'eqeltrd', [dd['e1'], dd['d1']], '( ( v - P ) ^ 1 ) e. CC'), evn, D(w, A4n, 'eqnetrd', [dd['e1'], dd['d0']], '( ( v - P ) ^ 1 ) =/= 0')],
                                            '%s =/= 0' % dd['V0'])], '( %s ` v ) =/= 0' % QTx)
    ne = w.s([ne1, ne2], 'pm2.61dane', '( %s -> ( %s ` v ) =/= 0 )' % (A4, QTx))
    alln = w.s([ne], 'ralrimiva', '( %s -> A. v e. D ( %s ` v ) =/= 0 )' % (ph, QTx))
    PHz = '( z e. D |-> ( ( H ` z ) / ( %s ` z ) ) )' % QTx
    PHs = '( s e. D |-> ( ( H ` s ) / ( %s ` s ) ) )' % QTx
    hd = w.s([holh, qh, alln, w.inst('holdiv')], 'syl3anc', '( %s -> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) )' % (ph, PHz, PHz))
    cb = w.s([w.s([w.s([], 'fveq2', '( z = s -> ( H ` z ) = ( H ` s ) )'), w.s([], 'fveq2', '( z = s -> ( %s ` z ) = ( %s ` s ) )' % (QTx, QTx))], 'oveq12d',
                  '( z = s -> ( ( H ` z ) / ( %s ` z ) ) = ( ( H ` s ) / ( %s ` s ) ) )' % (QTx, QTx))], 'cbvmptv', '%s = %s' % (PHz, PHs))
    cbd = w.s([cb], 'a1i', '( %s -> %s = %s )' % (ph, PHz, PHs))
    hq1 = D(w, ph, 'eleq1d', [cbd], '( %s e. ( D -cn-> CC ) <-> %s e. ( D -cn-> CC ) )' % (PHz, PHs))
    hq2 = D(w, ph, 'sseq2d', [D(w, ph, 'dmeqd', [D(w, ph, 'oveq2d', [cbd], '( CC _D %s ) = ( CC _D %s )' % (PHz, PHs))], 'dom ( CC _D %s ) = dom ( CC _D %s )' % (PHz, PHs))],
            '( D C_ dom ( CC _D %s ) <-> D C_ dom ( CC _D %s ) )' % (PHz, PHs))
    hds = D(w, ph, 'mpbid', [hd, D(w, ph, 'anbi12d', [hq1, hq2], '( ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) <-> ( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) ) )' % (PHz, PHz, PHs, PHs))],
            '( %s e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D %s ) )' % (PHs, PHs))
    phcn = w.s([hds, w.inst('simpl')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (ph, PHs))
    phdd = w.s([hds, w.inst('simpr')], 'syl', '( %s -> D C_ dom ( CC _D %s ) )' % (ph, PHs))
    crd = D(w, ph, 'sstrd', [rss, phdd], '( A crect B ) C_ dom ( CC _D %s )' % PHs)
    KZ = '( z e. ( ( A crect B ) \\ { P } ) |-> ( ( %s ` z ) / ( z - P ) ) )' % PHs
    cau = w.s([ab, pst, D(w, ph, 'jca', [phcn, crd], '( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) )' % (PHs, PHs)), w.inst('rectintcau')], 'syl3anc',
              '( %s -> ( %s rectint <. A , B >. ) = ( %s x. ( %s ` P ) ) )' % (ph, KZ, TWOPI_I, PHs))
    # value of PHs at P
    pin = w.s([D(w, ph, 'jca', [ab, pst], '( %s /\\ %s )' % (ABC, PST)), w.inst('crectinp')], 'syl', '( %s -> P e. ( A crect B ) )' % ph)
    pD = D(w, ph, 'sseldd', [rss, pin], 'P e. D')
    hf = w.s([w.s([holh, w.inst('simpl')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % ph), w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % ph)
    hpc = D(w, ph, 'ffvelcdmd', [hf, pD], '( H ` P ) e. CC')
    qf = w.s([qcn, w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (ph, QTx))
    qpc = D(w, ph, 'ffvelcdmd', [qf, pD], '( %s ` P ) e. CC' % QTx)
    qpn = D(w, ph, 'eqnetrd', [qv, dne], '( %s ` P ) =/= 0' % QTx)
    def phsub(A, X):
        B = '( %s /\\ s = %s )' % (A, X)
        eq = w.s([], 'simpr', '( %s -> s = %s )' % (B, X))
        return D(w, B, 'oveq12d', [D(w, B, 'fveq2d', [eq], '( H ` s ) = ( H ` %s )' % X), D(w, B, 'fveq2d', [eq], '( %s ` s ) = ( %s ` %s )' % (QTx, QTx, X))],
                 '( ( H ` s ) / ( %s ` s ) ) = ( ( H ` %s ) / ( %s ` %s ) )' % (QTx, X, QTx, X))
    fvP = w.s([D(w, ph, 'eqidd', [], '%s = %s' % (PHs, PHs)), phsub(ph, 'P'), pD, D(w, ph, 'divcld', [hpc, qpc, qpn], '( ( H ` P ) / ( %s ` P ) ) e. CC' % QTx)], 'fvmptd',
              '( %s -> ( %s ` P ) = ( ( H ` P ) / ( %s ` P ) ) )' % (ph, PHs, QTx))
    fvP2 = D(w, ph, 'eqtrd', [fvP, D(w, ph, 'oveq2d', [qv], '( ( H ` P ) / ( %s ` P ) ) = ( ( H ` P ) / %s )' % (QTx, PCD))], '( %s ` P ) = ( ( H ` P ) / %s )' % (PHs, PCD))
    cau2 = D(w, ph, 'eqtrd', [cau, D(w, ph, 'oveq2d', [fvP2], '( %s x. ( %s ` P ) ) = ( %s x. ( ( H ` P ) / %s ) )' % (TWOPI_I, PHs, TWOPI_I, PCD))],
             '( %s rectint <. A , B >. ) = ( %s x. ( ( H ` P ) / %s ) )' % (KZ, TWOPI_I, PCD))
    # G = KZ on the punctured rectangle
    A5 = '( %s /\\ u e. ( ( A crect B ) \\ { P } ) )' % ph
    ud = w.s([], 'simpr', '( %s -> u e. ( ( A crect B ) \\ { P } ) )' % A5)
    ueq = w.s([ud, w.s([], 'eldifsn', '( u e. ( ( A crect B ) \\ { P } ) <-> ( u e. ( A crect B ) /\\ u =/= P ) )')], 'sylib',
              '( %s -> ( u e. ( A crect B ) /\\ u =/= P ) )' % A5)
    ucr = w.s([ueq, w.inst('simpl')], 'syl', '( %s -> u e. ( A crect B ) )' % A5)
    une = w.s([ueq, w.inst('simpr')], 'syl', '( %s -> u =/= P )' % A5)
    uD = D(w, A5, 'sseldd', [w.s([rss], 'adantr', '( %s -> ( A crect B ) C_ D )' % A5), ucr], 'u e. D')
    qvu, du = qval(A5, 'u', uD, une)
    ra = w.s([w.s([w.s([], 'fveq2', '( a = u -> ( G ` a ) = ( G ` u ) )'),
                   w.s([w.s([], 'fveq2', '( a = u -> ( H ` a ) = ( H ` u ) )'), w.s([], 'fveq2', '( a = u -> ( E ` a ) = ( E ` u ) )')], 'oveq12d',
                       '( a = u -> ( ( H ` a ) / ( E ` a ) ) = ( ( H ` u ) / ( E ` u ) ) )')], 'eqeq12d',
                  '( a = u -> ( ( G ` a ) = ( ( H ` a ) / ( E ` a ) ) <-> ( G ` u ) = ( ( H ` u ) / ( E ` u ) ) ) )')], 'rspcv',
             '( u e. ( ( A crect B ) \\ { P } ) -> ( %s -> ( G ` u ) = ( ( H ` u ) / ( E ` u ) ) ) )' % ALLA)
    gu = w.s([ud, w.s([alla], 'adantr', '( %s -> %s )' % (A5, ALLA)), ra], 'sylc', '( %s -> ( G ` u ) = ( ( H ` u ) / ( E ` u ) ) )' % A5)
    hu = D(w, A5, 'ffvelcdmd', [w.s([hf], 'adantr', '( %s -> H : D --> CC )' % A5), uD], '( H ` u ) e. CC')
    rbu = w.s([uD, w.s([allb], 'adantr', '( %s -> %s )' % (A5, ALLB)), une,
               w.s([w.s([w.s([], 'neeq1', '( b = u -> ( b =/= P <-> u =/= P ) )'), w.s([w.s([], 'fveq2', '( b = u -> ( E ` b ) = ( E ` u ) )')], 'neeq1d', '( b = u -> ( ( E ` b ) =/= 0 <-> ( E ` u ) =/= 0 ) )')],
                        'imbi12d', '( b = u -> ( ( b =/= P -> ( E ` b ) =/= 0 ) <-> ( u =/= P -> ( E ` u ) =/= 0 ) ) )')], 'rspcv',
                   '( u e. D -> ( %s -> ( u =/= P -> ( E ` u ) =/= 0 ) ) )' % ALLB)], 'syl3c', '( %s -> ( E ` u ) =/= 0 )' % A5)
    # QTx ` u = E u / ( u - P )
    qvu2 = D(w, A5, 'eqtrd', [qvu, D(w, A5, 'oveq2d', [du['e1']], '( ( E ` u ) / ( ( u - P ) ^ 1 ) ) = ( ( E ` u ) / ( u - P ) )')], '( %s ` u ) = ( ( E ` u ) / ( u - P ) )' % QTx)
    edc = D(w, A5, 'divcld', [du['exc'], du['d1'], du['d0']], '( ( E ` u ) / ( u - P ) ) e. CC')
    edn = D(w, A5, 'divne0d', [du['exc'], du['d1'], rbu, du['d0']], '( ( E ` u ) / ( u - P ) ) =/= 0')
    qun = D(w, A5, 'eqnetrd', [qvu2, edn], '( %s ` u ) =/= 0' % QTx)
    quc = D(w, A5, 'eqeltrd', [qvu2, edc], '( %s ` u ) e. CC' % QTx)
    phu = w.s([D(w, A5, 'eqidd', [], '%s = %s' % (PHs, PHs)), phsub(A5, 'u'), uD, D(w, A5, 'divcld', [hu, quc, qun], '( ( H ` u ) / ( %s ` u ) ) e. CC' % QTx)], 'fvmptd',
              '( %s -> ( %s ` u ) = ( ( H ` u ) / ( %s ` u ) ) )' % (A5, PHs, QTx))
    phu2 = D(w, A5, 'eqtrd', [phu, D(w, A5, 'oveq2d', [qvu2], '( ( H ` u ) / ( %s ` u ) ) = ( ( H ` u ) / ( ( E ` u ) / ( u - P ) ) )' % QTx)],
             '( %s ` u ) = ( ( H ` u ) / ( ( E ` u ) / ( u - P ) ) )' % PHs)
    VK = '( ( ( H ` u ) / ( ( E ` u ) / ( u - P ) ) ) / ( u - P ) )'
    B6 = '( %s /\\ z = u )' % A5
    zeq = w.s([], 'simpr', '( %s -> z = u )' % B6)
    ksub = D(w, B6, 'oveq12d', [D(w, B6, 'fveq2d', [zeq], '( %s ` z ) = ( %s ` u )' % (PHs, PHs)), D(w, B6, 'oveq1d', [zeq], '( z - P ) = ( u - P )')],
             '( ( %s ` z ) / ( z - P ) ) = ( ( %s ` u ) / ( u - P ) )' % (PHs, PHs))
    phuc = D(w, A5, 'eqeltrd', [phu2, D(w, A5, 'divcld', [hu, edc, edn], '( ( H ` u ) / ( ( E ` u ) / ( u - P ) ) ) e. CC')], '( %s ` u ) e. CC' % PHs)
    kzu = w.s([D(w, A5, 'eqidd', [], '%s = %s' % (KZ, KZ)), ksub, ud, D(w, A5, 'divcld', [phuc, du['d1'], du['d0']], '( ( %s ` u ) / ( u - P ) ) e. CC' % PHs)], 'fvmptd',
              '( %s -> ( %s ` u ) = ( ( %s ` u ) / ( u - P ) ) )' % (A5, KZ, PHs))
    k2 = D(w, A5, 'oveq1d', [phu2], '( ( %s ` u ) / ( u - P ) ) = %s' % (PHs, VK))
    k3 = D(w, A5, 'divdiv1d', [hu, edc, du['d1'], edn, du['d0']], '%s = ( ( H ` u ) / ( ( ( E ` u ) / ( u - P ) ) x. ( u - P ) ) )' % VK)
    k4 = D(w, A5, 'divcan1d', [du['exc'], du['d1'], du['d0']], '( ( ( E ` u ) / ( u - P ) ) x. ( u - P ) ) = ( E ` u )')
    k5 = D(w, A5, 'oveq2d', [k4], '( ( H ` u ) / ( ( ( E ` u ) / ( u - P ) ) x. ( u - P ) ) ) = ( ( H ` u ) / ( E ` u ) )')
    kz = D(w, A5, 'eqtrd', [D(w, A5, 'eqtrd', [D(w, A5, 'eqtrd', [kzu, k2], '( %s ` u ) = %s' % (KZ, VK)), k3], '( %s ` u ) = ( ( H ` u ) / ( ( ( E ` u ) / ( u - P ) ) x. ( u - P ) ) )' % KZ), k5],
           '( %s ` u ) = ( ( H ` u ) / ( E ` u ) )' % KZ)
    gk = D(w, A5, 'eqtr4d', [gu, kz], '( G ` u ) = ( %s ` u )' % KZ)
    allg = w.s([gk], 'ralrimiva', '( %s -> A. u e. ( ( A crect B ) \\ { P } ) ( G ` u ) = ( %s ` u ) )' % (ph, KZ))
    gvv = w.s([gv, w.inst('elex')], 'syl', '( %s -> G e. _V )' % ph)
    crv = w.s([w.s([w.s([], 'ovex', '( A crect B ) e. _V'), w.inst('difexg')], 'ax-mp', '( ( A crect B ) \\ { P } ) e. _V')], 'a1i', '( %s -> ( ( A crect B ) \\ { P } ) e. _V )' % ph)
    kzv = w.s([crv, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (ph, KZ))
    req = w.s([D(w, ph, 'jca', [ab, pst], '( %s /\\ %s )' % (ABC, PST)), D(w, ph, 'jca', [gvv, kzv], '( G e. _V /\\ %s e. _V )' % KZ), allg, w.inst('rectinteqp')], 'syl3anc',
              '( %s -> ( G rectint <. A , B >. ) = ( %s rectint <. A , B >. ) )' % (ph, KZ))
    w.qed([req, cau2], 'eqtrd', S['zl3res'])
    go(w, only)


# ---------------------------------------------------------------- zl3resn
def cst(w, A, lab, fact):
    return w.s([w.s([], lab, fact)], 'a1i', '( %s -> %s )' % (A, fact))


def reim_cp(w, A, x, y, xr, yr):
    """( A -> ( Re ` CP(x,y) ) = x ), ( A -> ( Im ` CP(x,y) ) = y )"""
    r = w.s([xr, yr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = %s )' % (A, CP(x, y), x))
    i = w.s([xr, yr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = %s )' % (A, CP(x, y), y))
    return r, i


def cpcl(w, A, x, y, xr, yr):
    return D(w, A, 'addcld', [D(w, A, 'recnd', [xr], '%s e. CC' % x),
                              D(w, A, 'mulcld', [cst(w, A, 'ax-icn', '_i e. CC'), D(w, A, 'recnd', [yr], '%s e. CC' % y)], '( _i x. %s ) e. CC' % y)],
             '%s e. CC' % CP(x, y))


DN = "( `' Im \" ( ( N - 1 ) (,) ( N + 1 ) ) )"


def strip_mem(w, A, b, bDN):
    """from ( A -> b e. DN ): ( A -> b e. CC ), ( A -> ( N - 1 ) < ( Im ` b ) ), ( A -> ( Im ` b ) < ( N + 1 ) )"""
    imfn = cst(w, A, 'imfn', 'Im Fn CC') if False else w.s([w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Im Fn CC')], 'a1i', '( %s -> Im Fn CC )' % A)
    ep = w.s([imfn, w.inst('elpreima')], 'syl', '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( Im ` %s ) e. ( ( N - 1 ) (,) ( N + 1 ) ) ) ) )' % (A, b, DN, b, b))
    both = D(w, A, 'mpbid', [bDN, ep], '( %s e. CC /\\ ( Im ` %s ) e. ( ( N - 1 ) (,) ( N + 1 ) ) )' % (b, b))
    bc = w.s([both, w.inst('simpl')], 'syl', '( %s -> %s e. CC )' % (A, b))
    io = w.s([both, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) e. ( ( N - 1 ) (,) ( N + 1 ) ) )' % (A, b))
    oo = w.s([io, w.inst('eliooord')], 'syl', '( %s -> ( ( N - 1 ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( N + 1 ) ) )' % (A, b, b))
    return bc, oo, imfn


if __name__ == '__main__' and (not only or 'zl3resn' in only):
    w = W('zl3resn', 'The rectangle integral of ` H ( w ) / ( e ^ ( 2 pi w ) - 1 ) ` around the unit rectangle of the pole ` i N ` is ` i H ( i N ) `.')
    ph, concl = ante_of(S['zl3resn'])
    hent = w.s([], 'simpl', '( %s -> %s )' % (ph, HENT))
    nz = w.s([], 'simpr', '( %s -> N e. ZZ )' % ph)
    nr = D(w, ph, 'zred', [nz], 'N e. RR'); nc = D(w, ph, 'zcnd', [nz], 'N e. CC')
    hr = cst(w, ph, 'halfre', '( 1 / 2 ) e. RR'); hcn = cst(w, ph, 'halfcn', '( 1 / 2 ) e. CC')
    hrp = D(w, ph, 'elrpd', [hr, cst(w, ph, 'halfgt0', '0 < ( 1 / 2 )')], '( 1 / 2 ) e. RR+')
    m1 = cst(w, ph, 'neg1rr', '-u 1 e. RR'); p1 = cst(w, ph, '1re', '1 e. RR'); z0 = cst(w, ph, '0re', '0 e. RR')
    YA = '( N - ( 1 / 2 ) )'; YB = '( N + ( 1 / 2 ) )'
    yar = D(w, ph, 'resubcld', [nr, hr], '%s e. RR' % YA); ybr = D(w, ph, 'readdcld', [nr, hr], '%s e. RR' % YB)
    A_, B_ = QN('N'); P_ = '( _i x. N )'
    ac = cpcl(w, ph, '-u 1', YA, m1, yar); bc = cpcl(w, ph, '1', YB, p1, ybr)
    reA, imA = reim_cp(w, ph, '-u 1', YA, m1, yar); reB, imB = reim_cp(w, ph, '1', YB, p1, ybr)
    ic = cst(w, ph, 'ax-icn', '_i e. CC')
    inc = D(w, ph, 'mulcld', [ic, nc], '%s e. CC' % P_)
    pe = D(w, ph, 'eqcomd', [D(w, ph, 'addlidd', [inc], '( 0 + %s ) = %s' % (P_, P_))], '%s = ( 0 + %s )' % (P_, P_))
    reP0, imP0 = reim_cp(w, ph, '0', 'N', z0, nr)
    reP = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [pe], '( Re ` %s ) = ( Re ` ( 0 + %s ) )' % (P_, P_)), reP0], '( Re ` %s ) = 0' % P_)
    imP = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [pe], '( Im ` %s ) = ( Im ` ( 0 + %s ) )' % (P_, P_)), imP0], '( Im ` %s ) = N' % P_)
    # strict interiority
    s1 = D(w, ph, '3brtr4d', [cst(w, ph, 'neg1lt0', '-u 1 < 0'), reA, reP], '( Re ` %s ) < ( Re ` %s )' % (A_, P_))
    s2 = D(w, ph, '3brtr4d', [cst(w, ph, '0lt1', '0 < 1'), reP, reB], '( Re ` %s ) < ( Re ` %s )' % (P_, B_))
    s3 = D(w, ph, '3brtr4d', [D(w, ph, 'ltsubrpd', [nr, hrp], '%s < N' % YA), imA, imP], '( Im ` %s ) < ( Im ` %s )' % (A_, P_))
    s4 = D(w, ph, '3brtr4d', [D(w, ph, 'ltaddrpd', [nr, hrp], 'N < %s' % YB), imP, imB], '( Im ` %s ) < ( Im ` %s )' % (P_, B_))
    STR = STRICT(A_, B_, P_)
    st = D(w, ph, 'jca', [D(w, ph, 'jca', [s1, s2], '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (A_, P_, P_, B_)),
                          D(w, ph, 'jca', [s3, s4], '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (A_, P_, P_, B_))], STR)
    abc = D(w, ph, 'jca', [ac, bc], '( %s e. CC /\\ %s e. CC )' % (A_, B_))
    pst = D(w, ph, 'jca', [inc, st], '( %s e. CC /\\ %s )' % (P_, STR))
    # the rectangle lies in the strip DN
    A1 = '( %s /\\ z e. ( %s crect %s ) )' % (ph, A_, B_)
    zin = w.s([], 'simpr', '( %s -> z e. ( %s crect %s ) )' % (A1, A_, B_))
    ec = w.s([w.s([abc], 'adantr', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A1, A_, B_)), w.inst('elcrect')], 'syl',
             '( %s -> ( z e. ( %s crect %s ) <-> ( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )' % (A1, A_, B_, A_, B_, A_, B_))
    e3 = D(w, A1, 'mpbid', [zin, ec], '( z e. CC /\\ ( Re ` z ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A_, B_, A_, B_))
    zc = w.s([e3, w.inst('simp1')], 'syl', '( %s -> z e. CC )' % A1)
    zim = w.s([e3, w.inst('simp3')], 'syl', '( %s -> ( Im ` z ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (A1, A_, B_))
    iab = D(w, A1, 'oveq12d', [w.s([imA], 'adantr', '( %s -> ( Im ` %s ) = %s )' % (A1, A_, YA)), w.s([imB], 'adantr', '( %s -> ( Im ` %s ) = %s )' % (A1, B_, YB))],
            '( ( Im ` %s ) [,] ( Im ` %s ) ) = ( %s [,] %s )' % (A_, B_, YA, YB))
    zim2 = D(w, A1, 'eleqtrd', [zim, iab], '( Im ` z ) e. ( %s [,] %s )' % (YA, YB))
    yar1 = w.s([yar], 'adantr', '( %s -> %s e. RR )' % (A1, YA)); ybr1 = w.s([ybr], 'adantr', '( %s -> %s e. RR )' % (A1, YB))
    ic3 = w.s([yar1, ybr1, w.inst('elicc2')], 'syl2anc', '( %s -> ( ( Im ` z ) e. ( %s [,] %s ) <-> ( ( Im ` z ) e. RR /\\ %s <_ ( Im ` z ) /\\ ( Im ` z ) <_ %s ) ) )' % (A1, YA, YB, YA, YB))
    i3 = D(w, A1, 'mpbid', [zim2, ic3], '( ( Im ` z ) e. RR /\\ %s <_ ( Im ` z ) /\\ ( Im ` z ) <_ %s )' % (YA, YB))
    imr = w.s([i3, w.inst('simp1')], 'syl', '( %s -> ( Im ` z ) e. RR )' % A1)
    nr1 = w.s([nr], 'adantr', '( %s -> N e. RR )' % A1); hrp1 = w.s([hrp], 'adantr', '( %s -> ( 1 / 2 ) e. RR+ )' % A1)
    o1 = cst(w, A1, '1re', '1 e. RR')
    # N - 1 < N - 1/2 <_ Im z <_ N + 1/2 < N + 1
    lt1 = D(w, A1, 'ltsub2dd', [cst(w, A1, 'halflt1', '( 1 / 2 ) < 1'), cst(w, A1, 'halfre', '( 1 / 2 ) e. RR'), o1, nr1], '( N - 1 ) < %s' % YA)
    lt2 = D(w, A1, 'ltadd2dd', [cst(w, A1, 'halflt1', '( 1 / 2 ) < 1'), cst(w, A1, 'halfre', '( 1 / 2 ) e. RR'), o1, nr1], '%s < ( N + 1 )' % YB)
    lo = D(w, A1, 'ltletrd', [D(w, A1, 'resubcld', [nr1, o1], '( N - 1 ) e. RR'), yar1, imr, lt1, w.s([i3, w.inst('simp2')], 'syl', '( %s -> %s <_ ( Im ` z ) )' % (A1, YA))],
           '( N - 1 ) < ( Im ` z )')
    hi = D(w, A1, 'lelttrd', [imr, ybr1, D(w, A1, 'readdcld', [nr1, o1], '( N + 1 ) e. RR'), w.s([i3, w.inst('simp3')], 'syl', '( %s -> ( Im ` z ) <_ %s )' % (A1, YB)), lt2],
           '( Im ` z ) < ( N + 1 )')
    rx1 = D(w, A1, 'rexrd', [D(w, A1, 'resubcld', [nr1, o1], '( N - 1 ) e. RR')], '( N - 1 ) e. RR*')
    rx2 = D(w, A1, 'rexrd', [D(w, A1, 'readdcld', [nr1, o1], '( N + 1 ) e. RR')], '( N + 1 ) e. RR*')
    eio = w.s([rx1, rx2, w.inst('elioo2')], 'syl2anc', '( %s -> ( ( Im ` z ) e. ( ( N - 1 ) (,) ( N + 1 ) ) <-> ( ( Im ` z ) e. RR /\\ ( N - 1 ) < ( Im ` z ) /\\ ( Im ` z ) < ( N + 1 ) ) ) )' % A1)
    zio = D(w, A1, 'mpbird', [w.s([imr, lo, hi], '3jca', '( %s -> ( ( Im ` z ) e. RR /\\ ( N - 1 ) < ( Im ` z ) /\\ ( Im ` z ) < ( N + 1 ) ) )' % A1), eio],
            '( Im ` z ) e. ( ( N - 1 ) (,) ( N + 1 ) )')
    imfn1 = w.s([w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('ffn')], 'ax-mp', 'Im Fn CC')], 'a1i', '( %s -> Im Fn CC )' % A1)
    ep1 = w.s([imfn1, w.inst('elpreima')], 'syl', '( %s -> ( z e. %s <-> ( z e. CC /\\ ( Im ` z ) e. ( ( N - 1 ) (,) ( N + 1 ) ) ) ) )' % (A1, DN))
    zdn = D(w, A1, 'mpbird', [D(w, A1, 'jca', [zc, zio], '( z e. CC /\\ ( Im ` z ) e. ( ( N - 1 ) (,) ( N + 1 ) ) )'), ep1], 'z e. %s' % DN)
    rss = w.s([w.s([zdn], 'ex', '( %s -> ( z e. ( %s crect %s ) -> z e. %s ) )' % (ph, A_, B_, DN))], 'ssrdv', '( %s -> ( %s crect %s ) C_ %s )' % (ph, A_, B_, DN))
    rect = w.s([abc, pst, rss], '3jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s ) /\\ ( %s crect %s ) C_ %s ) )' % (ph, A_, B_, P_, STR, A_, B_, DN))
    # R = 1/2
    RC = RCOND(A_, B_, P_, '( 1 / 2 )')
    c1 = cst(w, ph, 'ax-1cn', '1 e. CC'); c0 = cst(w, ph, '0cn', '0 e. CC')
    d1 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq12d', [reP, reA], '( ( Re ` %s ) - ( Re ` %s ) ) = ( 0 - -u 1 )' % (P_, A_)),
                           D(w, ph, 'eqtrd', [w.s([c0, c1, w.inst('subneg')], 'syl2anc', '( %s -> ( 0 - -u 1 ) = ( 0 + 1 ) )' % ph), D(w, ph, 'addlidd', [c1], '( 0 + 1 ) = 1')], '( 0 - -u 1 ) = 1')],
           '( ( Re ` %s ) - ( Re ` %s ) ) = 1' % (P_, A_))
    d2 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq12d', [reB, reP], '( ( Re ` %s ) - ( Re ` %s ) ) = ( 1 - 0 )' % (B_, P_)), D(w, ph, 'subid1d', [c1], '( 1 - 0 ) = 1')],
           '( ( Re ` %s ) - ( Re ` %s ) ) = 1' % (B_, P_))
    d3 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq12d', [imP, imA], '( ( Im ` %s ) - ( Im ` %s ) ) = ( N - %s )' % (P_, A_, YA)),
                           w.s([nc, hcn, w.inst('nncan')], 'syl2anc', '( %s -> ( N - %s ) = ( 1 / 2 ) )' % (ph, YA))], '( ( Im ` %s ) - ( Im ` %s ) ) = ( 1 / 2 )' % (P_, A_))
    d4 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq12d', [imB, imP], '( ( Im ` %s ) - ( Im ` %s ) ) = ( %s - N )' % (B_, P_, YB)),
                           w.s([nc, hcn, w.inst('pncan2')], 'syl2anc', '( %s -> ( %s - N ) = ( 1 / 2 ) )' % (ph, YB))], '( ( Im ` %s ) - ( Im ` %s ) ) = ( 1 / 2 )' % (B_, P_))
    h1 = D(w, ph, 'ltled', [hr, p1, cst(w, ph, 'halflt1', '( 1 / 2 ) < 1')], '( 1 / 2 ) <_ 1')
    hh = D(w, ph, 'leidd', [hr], '( 1 / 2 ) <_ ( 1 / 2 )')
    r1 = D(w, ph, 'breqtrrd', [h1, d1], '( 1 / 2 ) <_ ( ( Re ` %s ) - ( Re ` %s ) )' % (P_, A_))
    r2 = D(w, ph, 'breqtrrd', [h1, d2], '( 1 / 2 ) <_ ( ( Re ` %s ) - ( Re ` %s ) )' % (B_, P_))
    r3 = D(w, ph, 'breqtrrd', [hh, d3], '( 1 / 2 ) <_ ( ( Im ` %s ) - ( Im ` %s ) )' % (P_, A_))
    r4 = D(w, ph, 'breqtrrd', [hh, d4], '( 1 / 2 ) <_ ( ( Im ` %s ) - ( Im ` %s ) )' % (B_, P_))
    rc = D(w, ph, 'jca', [D(w, ph, 'jca', [r1, r2], '( ( 1 / 2 ) <_ ( ( Re ` %s ) - ( Re ` %s ) ) /\\ ( 1 / 2 ) <_ ( ( Re ` %s ) - ( Re ` %s ) ) )' % (P_, A_, B_, P_)),
                          D(w, ph, 'jca', [r3, r4], '( ( 1 / 2 ) <_ ( ( Im ` %s ) - ( Im ` %s ) ) /\\ ( 1 / 2 ) <_ ( ( Im ` %s ) - ( Im ` %s ) ) )' % (P_, A_, B_, P_))], RC)
    rrc = D(w, ph, 'jca', [D(w, ph, 'jca', [hr, rc], '( ( 1 / 2 ) e. RR /\\ %s )' % RC), cst(w, ph, 'halfgt0', '0 < ( 1 / 2 )')], '( ( ( 1 / 2 ) e. RR /\\ %s ) /\\ 0 < ( 1 / 2 ) )' % RC)
    # H and E on the strip
    dno = cst(w, ph, 'zl3imopn', "%s e. ( TopOpen ` CCfld )" % DN)
    dnc = w.s([w.s([], 'cnvimass', "( `' Im \" ( ( N - 1 ) (,) ( N + 1 ) ) ) C_ dom Im"), w.s([w.s([], 'imf', 'Im : CC --> RR'), w.inst('fdm')], 'ax-mp', 'dom Im = CC')], 'sseqtri',
              '%s C_ CC' % DN)
    dnc1 = w.s([dnc], 'a1i', '( %s -> %s C_ CC )' % (ph, DN))
    HD = '( z e. %s |-> ( H ` z ) )' % DN
    hd = w.s([hent, D(w, ph, 'jca', [dno, dnc1], "( %s e. ( TopOpen ` CCfld ) /\\ %s C_ CC )" % (DN, DN)), w.inst('zl2hres')], 'syl2anc',
             '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (ph, HD, DN, DN, HD))
    ED = '( w e. %s |-> ( %s - 1 ) )' % (DN, E2('w'))
    DVE = '( w e. %s |-> ( %s x. %s ) )' % (DN, TP, E2('w'))
    zdv = cst(w, ph, 'zl3dve', S['zl3dve'])
    dvc = w.s([zdv, w.inst('simpr')], 'syl', '( %s -> ( CC _D %s ) = ( w e. CC |-> ( %s x. %s ) ) )' % (ph, EF, TP, E2('w')))
    A2 = '( %s /\\ w e. CC )' % ph
    wc2 = w.s([], 'simpr', '( %s -> w e. CC )' % A2)
    tc2, tn2 = twopi(w, A2)
    ew2 = w.s([D(w, A2, 'mulcld', [tc2, wc2], '( %s x. w ) e. CC' % TP), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A2, E2('w')))
    vA = D(w, A2, 'subcld', [ew2, cst(w, A2, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % E2('w'))
    vB = D(w, A2, 'mulcld', [tc2, ew2], '( %s x. %s ) e. CC' % (TP, E2('w')))
    TOPS = '( TopOpen ` CCfld )'
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOPS, TOPS))], 'eqcomi', '%s = ( %s |`t CC )' % (TOPS, TOPS))
    dvd = w.s([cst(w, ph, 'cnelprrecn', 'CC e. { RR , CC }'), vA, vB, dvc, dnc1, jr, w.s([], 'eqid', '%s = %s' % (TOPS, TOPS)), dno], 'dvmptres',
              '( %s -> ( CC _D %s ) = %s )' % (ph, ED, DVE))
    A3 = '( %s /\\ w e. %s )' % (ph, DN)
    wc3 = D(w, A3, 'sseldd', [w.s([dnc1], 'adantr', '( %s -> %s C_ CC )' % (A3, DN)), w.s([], 'simpr', '( %s -> w e. %s )' % (A3, DN))], 'w e. CC')
    tc3, tn3 = twopi(w, A3)
    ew3 = w.s([D(w, A3, 'mulcld', [tc3, wc3], '( %s x. w ) e. CC' % TP), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A3, E2('w')))
    vA3 = D(w, A3, 'subcld', [ew3, cst(w, A3, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % E2('w'))
    vB3 = D(w, A3, 'mulcld', [tc3, ew3], '( %s x. %s ) e. CC' % (TP, E2('w')))
    dmd = D(w, ph, 'eqtrd', [D(w, ph, 'dmeqd', [dvd], 'dom ( CC _D %s ) = dom %s' % (ED, DVE)), w.s([w.s([], 'eqid', '%s = %s' % (DVE, DVE)), vB3], 'dmmptd', '( %s -> dom %s = %s )' % (ph, DVE, DN))],
            'dom ( CC _D %s ) = %s' % (ED, DN))
    edf = w.s([vA3, w.s([], 'eqid', '%s = %s' % (ED, ED))], 'fmptd', '( %s -> %s : %s --> CC )' % (ph, ED, DN))
    edcn = w.s([w.s([cst(w, ph, 'ssid', 'CC C_ CC'), edf, dnc1], '3jca', '( %s -> ( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC ) )' % (ph, ED, DN, DN)), dmd, w.inst('dvcn')], 'syl2anc',
               '( %s -> %s e. ( %s -cn-> CC ) )' % (ph, ED, DN))
    edhol = D(w, ph, 'jca', [edcn, D(w, ph, 'eqimssd', [D(w, ph, 'eqcomd', [dmd], '%s = dom ( CC _D %s )' % (DN, ED))], '%s C_ dom ( CC _D %s )' % (DN, ED))],
              '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (ED, DN, DN, ED))
    # values at P
    pin = w.s([D(w, ph, 'jca', [abc, pst], '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s ) )' % (A_, B_, P_, STR)), w.inst('crectinp')], 'syl', '( %s -> %s e. ( %s crect %s ) )' % (ph, P_, A_, B_))
    pdn = D(w, ph, 'sseldd', [rss, pin], '%s e. %s' % (P_, DN))
    tc, tn = twopi(w, ph)
    # e ^ ( 2 pi ( i N ) ) = 1
    q1 = D(w, ph, 'mulassd', [tc, ic, nc], '( ( %s x. _i ) x. N ) = ( %s x. ( _i x. N ) )' % (TP, TP))
    q2 = D(w, ph, 'oveq1d', [D(w, ph, 'mulcomd', [tc, ic], '( %s x. _i ) = ( _i x. %s )' % (TP, TP))], '( ( %s x. _i ) x. N ) = ( ( _i x. %s ) x. N )' % (TP, TP))
    q3 = D(w, ph, 'eqtr3d', [q1, q2], '( %s x. ( _i x. N ) ) = ( ( _i x. %s ) x. N )' % (TP, TP))
    e1 = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [q3], '%s = ( exp ` ( ( _i x. %s ) x. N ) )' % (E2(P_), TP)), w.s([nz, w.inst('ef2kpi')], 'syl', '( %s -> ( exp ` ( ( _i x. %s ) x. N ) ) = 1 )' % (ph, TP))],
           '%s = 1' % E2(P_))
    def edsub(A, X):
        B = '( %s /\\ w = %s )' % (A, X)
        eq = w.s([], 'simpr', '( %s -> w = %s )' % (B, X))
        return D(w, B, 'oveq1d', [D(w, B, 'fveq2d', [D(w, B, 'oveq2d', [eq], '( %s x. w ) = ( %s x. %s )' % (TP, TP, X))], '%s = %s' % (E2('w'), E2(X)))],
                 '( %s - 1 ) = ( %s - 1 )' % (E2('w'), E2(X)))
    epc = w.s([D(w, ph, 'mulcld', [tc, inc], '( %s x. %s ) e. CC' % (TP, P_)), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (ph, E2(P_)))
    edp = w.s([D(w, ph, 'eqidd', [], '%s = %s' % (ED, ED)), edsub(ph, P_), pdn, D(w, ph, 'subcld', [epc, cst(w, ph, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % E2(P_))], 'fvmptd',
              '( %s -> ( %s ` %s ) = ( %s - 1 ) )' % (ph, ED, P_, E2(P_)))
    edp0 = D(w, ph, 'eqtrd', [edp, D(w, ph, 'subeq0bd', [epc, e1], '( %s - 1 ) = 0' % E2(P_))], '( %s ` %s ) = 0' % (ED, P_))
    def dvsub(A, X):
        B = '( %s /\\ w = %s )' % (A, X)
        eq = w.s([], 'simpr', '( %s -> w = %s )' % (B, X))
        return D(w, B, 'oveq2d', [D(w, B, 'fveq2d', [D(w, B, 'oveq2d', [eq], '( %s x. w ) = ( %s x. %s )' % (TP, TP, X))], '%s = %s' % (E2('w'), E2(X)))],
                 '( %s x. %s ) = ( %s x. %s )' % (TP, E2('w'), TP, E2(X)))
    dvp = w.s([dvd, dvsub(ph, P_), pdn, D(w, ph, 'mulcld', [tc, epc], '( %s x. %s ) e. CC' % (TP, E2(P_)))], 'fvmptd', '( %s -> ( ( CC _D %s ) ` %s ) = ( %s x. %s ) )' % (ph, ED, P_, TP, E2(P_)))
    dvp2 = D(w, ph, 'eqtrd', [dvp, D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [e1], '( %s x. %s ) = ( %s x. 1 )' % (TP, E2(P_), TP)), D(w, ph, 'mulridd', [tc], '( %s x. 1 ) = %s' % (TP, TP))],
                                                      '( %s x. %s ) = %s' % (TP, E2(P_), TP))], '( ( CC _D %s ) ` %s ) = %s' % (ED, P_, TP))
    dvn = D(w, ph, 'eqnetrd', [dvp2, tn], '( ( CC _D %s ) ` %s ) =/= 0' % (ED, P_))
    # the zeros: E ( b ) = 0 in the strip only at P
    def zero_only(A, b, bDN, lift):
        bc_, oo, _ = strip_mem(w, A, b, bDN)
        B = '( %s /\\ %s = 1 )' % (A, E2(b))
        ez = w.s([w.s([nz], lift, '( %s -> N e. ZZ )' % B), D(w, B, 'jca', [w.s([bc_], 'adantr', '( %s -> %s e. CC )' % (B, b)), w.s([oo], 'adantr', '( %s -> ( ( N - 1 ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( N + 1 ) ) )' % (B, b, b))],
                                                                  '( %s e. CC /\\ ( ( N - 1 ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( N + 1 ) ) )' % (b, b, b)), w.s([], 'simpr', '( %s -> %s = 1 )' % (B, E2(b))), w.inst('zl3ezn')],
                 'syl3anc', '( %s -> %s = %s )' % (B, b, P_))
        return w.s([ez], 'ex', '( %s -> ( %s = 1 -> %s = %s ) )' % (A, E2(b), b, P_)), bc_
    A6 = '( %s /\\ b e. %s )' % (ph, DN)
    bdn = w.s([], 'simpr', '( %s -> b e. %s )' % (A6, DN))
    zo6, bc6 = zero_only(A6, 'b', bdn, 'ad2antrr')
    tc6, _ = twopi(w, A6)
    ebc = w.s([D(w, A6, 'mulcld', [tc6, bc6], '( %s x. b ) e. CC' % TP), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A6, E2('b')))
    edb = w.s([D(w, A6, 'eqidd', [], '%s = %s' % (ED, ED)), edsub(A6, 'b'), bdn, D(w, A6, 'subcld', [ebc, cst(w, A6, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % E2('b'))], 'fvmptd',
              '( %s -> ( %s ` b ) = ( %s - 1 ) )' % (A6, ED, E2('b')))
    sb = w.s([ebc, cst(w, A6, 'ax-1cn', '1 e. CC'), w.inst('subeq0ad')], 'syl2anc', '( %s -> ( ( %s - 1 ) = 0 <-> %s = 1 ) )' % (A6, E2('b'), E2('b')))
    b0 = D(w, A6, 'bitrd', [D(w, A6, 'eqeq1d', [edb], '( ( %s ` b ) = 0 <-> ( %s - 1 ) = 0 )' % (ED, E2('b'))), sb], '( ( %s ` b ) = 0 <-> %s = 1 )' % (ED, E2('b')))
    zb = D(w, A6, 'sylbid', [b0, zo6], '( ( %s ` b ) = 0 -> b = %s )' % (ED, P_))
    nb = D(w, A6, 'necon3d', [zb], '( b =/= %s -> ( %s ` b ) =/= 0 )' % (P_, ED))
    allb = w.s([nb], 'ralrimiva', '( %s -> A. b e. %s ( b =/= %s -> ( %s ` b ) =/= 0 ) )' % (ph, DN, P_, ED))
    # FK = HD / ED on the punctured rectangle
    A8 = '( %s /\\ a e. ( ( %s crect %s ) \\ { %s } ) )' % (ph, A_, B_, P_)
    ad = w.s([], 'simpr', '( %s -> a e. ( ( %s crect %s ) \\ { %s } ) )' % (A8, A_, B_, P_))
    ae = w.s([ad, w.s([], 'eldifsn', '( a e. ( ( %s crect %s ) \\ { %s } ) <-> ( a e. ( %s crect %s ) /\\ a =/= %s ) )' % (A_, B_, P_, A_, B_, P_))], 'sylib',
             '( %s -> ( a e. ( %s crect %s ) /\\ a =/= %s ) )' % (A8, A_, B_, P_))
    acr = w.s([ae, w.inst('simpl')], 'syl', '( %s -> a e. ( %s crect %s ) )' % (A8, A_, B_))
    ane = w.s([ae, w.inst('simpr')], 'syl', '( %s -> a =/= %s )' % (A8, P_))
    adn = D(w, A8, 'sseldd', [w.s([rss], 'adantr', '( %s -> ( %s crect %s ) C_ %s )' % (A8, A_, B_, DN)), acr], 'a e. %s' % DN)
    zo8, ac8 = zero_only(A8, 'a', adn, 'ad2antrr')
    ea1 = D(w, A8, 'necon3d', [zo8], '( a =/= %s -> %s =/= 1 )' % (P_, E2('a')))
    ea = D(w, A8, 'mpd', [ane, ea1], '%s =/= 1' % E2('a'))
    vsub = w.s([w.s([w.s([w.s([], 'id', '( v = a -> v = a )')], 'oveq2d', '( v = a -> ( %s x. v ) = ( %s x. a ) )' % (TP, TP))], 'fveq2d', '( v = a -> %s = %s )' % (E2('v'), E2('a')))],
               'neeq1d', '( v = a -> ( %s =/= 1 <-> %s =/= 1 ) )' % (E2('v'), E2('a')))
    elr = w.s([vsub], 'elrab', '( a e. %s <-> ( a e. CC /\\ %s =/= 1 ) )' % (D0, E2('a')))
    ad0 = w.s([D(w, A8, 'jca', [ac8, ea], '( a e. CC /\\ %s =/= 1 )' % E2('a')), elr], 'sylibr', '( %s -> a e. %s )' % (A8, D0))
    tc8, _ = twopi(w, A8)
    eac = w.s([D(w, A8, 'mulcld', [tc8, ac8], '( %s x. a ) e. CC' % TP), w.inst('efcl')], 'syl', '( %s -> %s e. CC )' % (A8, E2('a')))
    hf8 = w.s([w.s([w.s([hent, w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % ph), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % ph)], 'adantr', '( %s -> H : CC --> CC )' % A8)
    hac = D(w, A8, 'ffvelcdmd', [hf8, ac8], '( H ` a ) e. CC')
    ea1c = D(w, A8, 'subcld', [eac, cst(w, A8, 'ax-1cn', '1 e. CC')], '( %s - 1 ) e. CC' % E2('a'))
    ea1n = D(w, A8, 'subne0d', [eac, cst(w, A8, 'ax-1cn', '1 e. CC'), ea], '( %s - 1 ) =/= 0' % E2('a'))
    B9 = '( %s /\\ w = a )' % A8
    weq = w.s([], 'simpr', '( %s -> w = a )' % B9)
    fks = D(w, B9, 'oveq12d', [D(w, B9, 'fveq2d', [weq], '( H ` w ) = ( H ` a )'), edsub(A8, 'a')], '( ( H ` w ) / ( %s - 1 ) ) = ( ( H ` a ) / ( %s - 1 ) )' % (E2('w'), E2('a')))
    fka = w.s([D(w, A8, 'eqidd', [], '%s = %s' % (FK, FK)), fks, ad0, D(w, A8, 'divcld', [hac, ea1c, ea1n], '( ( H ` a ) / ( %s - 1 ) ) e. CC' % E2('a'))], 'fvmptd',
              '( %s -> ( %s ` a ) = ( ( H ` a ) / ( %s - 1 ) ) )' % (A8, FK, E2('a')))
    B10 = '( %s /\\ z = a )' % A8
    hda = w.s([D(w, A8, 'eqidd', [], '%s = %s' % (HD, HD)), D(w, B10, 'fveq2d', [w.s([], 'simpr', '( %s -> z = a )' % B10)], '( H ` z ) = ( H ` a )'), adn, hac], 'fvmptd',
              '( %s -> ( %s ` a ) = ( H ` a ) )' % (A8, HD))
    eda = w.s([D(w, A8, 'eqidd', [], '%s = %s' % (ED, ED)), edsub(A8, 'a'), adn, ea1c], 'fvmptd', '( %s -> ( %s ` a ) = ( %s - 1 ) )' % (A8, ED, E2('a')))
    fq = D(w, A8, 'eqtr4d', [fka, D(w, A8, 'oveq12d', [hda, eda], '( ( %s ` a ) / ( %s ` a ) ) = ( ( H ` a ) / ( %s - 1 ) )' % (HD, ED, E2('a')))],
           '( %s ` a ) = ( ( %s ` a ) / ( %s ` a ) )' % (FK, HD, ED))
    alla = w.s([fq], 'ralrimiva', '( %s -> A. a e. ( ( %s crect %s ) \\ { %s } ) ( %s ` a ) = ( ( %s ` a ) / ( %s ` a ) ) )' % (ph, A_, B_, P_, FK, HD, ED))
    fkv = cst(w, ph, 'mptex', '%s e. _V' % FK) if False else w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'rabex', '%s e. _V' % D0)], 'mptex', '%s e. _V' % FK)
    fkv1 = w.s([fkv], 'a1i', '( %s -> %s e. _V )' % (ph, FK))
    # assemble zl3res
    RES_A = '( ( ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) ) /\\ ( ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s ) /\\ ( %s crect %s ) C_ %s ) /\\ ( ( ( 1 / 2 ) e. RR /\\ %s ) /\\ 0 < ( 1 / 2 ) ) ) )' % (
        HD, DN, DN, HD, ED, DN, DN, ED, A_, B_, P_, STR, A_, B_, DN, RC)
    RES_B = '( ( ( %s ` %s ) = 0 /\\ ( ( CC _D %s ) ` %s ) =/= 0 ) /\\ ( A. b e. %s ( b =/= %s -> ( %s ` b ) =/= 0 ) /\\ ( %s e. _V /\\ A. a e. ( ( %s crect %s ) \\ { %s } ) ( %s ` a ) = ( ( %s ` a ) / ( %s ` a ) ) ) ) )' % (
        ED, P_, ED, P_, DN, P_, ED, FK, A_, B_, P_, FK, HD, ED)
    ra = D(w, ph, 'jca', [D(w, ph, 'jca', [hd, edhol], RES_A[4:RES_A.index(' /\\ ( ( ( %s e. CC' % A_)] if False else '( ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (HD, DN, DN, HD, ED, DN, DN, ED)),
                          D(w, ph, 'jca', [rect, rrc], '( ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s ) /\\ ( %s crect %s ) C_ %s ) /\\ ( ( ( 1 / 2 ) e. RR /\\ %s ) /\\ 0 < ( 1 / 2 ) ) )' % (A_, B_, P_, STR, A_, B_, DN, RC))],
           RES_A)
    rb = D(w, ph, 'jca', [D(w, ph, 'jca', [edp0, dvn], '( ( %s ` %s ) = 0 /\\ ( ( CC _D %s ) ` %s ) =/= 0 )' % (ED, P_, ED, P_)),
                          D(w, ph, 'jca', [allb, D(w, ph, 'jca', [fkv1, alla], '( %s e. _V /\\ A. a e. ( ( %s crect %s ) \\ { %s } ) ( %s ` a ) = ( ( %s ` a ) / ( %s ` a ) ) )' % (FK, A_, B_, P_, FK, HD, ED))],
                            '( A. b e. %s ( b =/= %s -> ( %s ` b ) =/= 0 ) /\\ ( %s e. _V /\\ A. a e. ( ( %s crect %s ) \\ { %s } ) ( %s ` a ) = ( ( %s ` a ) / ( %s ` a ) ) ) )' % (DN, P_, ED, FK, A_, B_, P_, FK, HD, ED))],
           RES_B)
    res = w.s([ra, rb, w.inst('zl3res')], 'syl2anc', '( %s -> %s = ( %s x. ( ( %s ` %s ) / ( ( CC _D %s ) ` %s ) ) ) )' % (ph, RI(FK, A_, B_), TWOPI_I, HD, P_, ED, P_))
    B11 = '( %s /\\ z = %s )' % (ph, P_)
    hpc = D(w, ph, 'ffvelcdmd', [w.s([w.s([hent, w.inst('simpl')], 'syl', '( %s -> H e. ( CC -cn-> CC ) )' % ph), w.inst('cncff')], 'syl', '( %s -> H : CC --> CC )' % ph), inc], '( H ` %s ) e. CC' % P_)
    hdp = w.s([D(w, ph, 'eqidd', [], '%s = %s' % (HD, HD)), D(w, B11, 'fveq2d', [w.s([], 'simpr', '( %s -> z = %s )' % (B11, P_))], '( H ` z ) = ( H ` %s )' % P_), pdn, hpc], 'fvmptd',
              '( %s -> ( %s ` %s ) = ( H ` %s ) )' % (ph, HD, P_, P_))
    v1 = D(w, ph, 'oveq12d', [hdp, dvp2], '( ( %s ` %s ) / ( ( CC _D %s ) ` %s ) ) = ( ( H ` %s ) / %s )' % (HD, P_, ED, P_, P_, TP))
    v2 = D(w, ph, 'oveq2d', [v1], '( %s x. ( ( %s ` %s ) / ( ( CC _D %s ) ` %s ) ) ) = ( %s x. ( ( H ` %s ) / %s ) )' % (TWOPI_I, HD, P_, ED, P_, TWOPI_I, P_, TP))
    pc_ = cst(w, ph, 'picn', '_pi e. CC'); c2 = cst(w, ph, '2cn', '2 e. CC')
    v3 = D(w, ph, 'mul12d', [c2, ic, pc_], '%s = ( _i x. ( 2 x. _pi ) )' % TWOPI_I)
    v4 = D(w, ph, 'oveq1d', [v3], '( %s x. ( ( H ` %s ) / %s ) ) = ( ( _i x. %s ) x. ( ( H ` %s ) / %s ) )' % (TWOPI_I, P_, TP, TP, P_, TP))
    hq = D(w, ph, 'divcld', [hpc, tc, tn], '( ( H ` %s ) / %s ) e. CC' % (P_, TP))
    v5 = D(w, ph, 'mulassd', [ic, tc, hq], '( ( _i x. %s ) x. ( ( H ` %s ) / %s ) ) = ( _i x. ( %s x. ( ( H ` %s ) / %s ) ) )' % (TP, P_, TP, TP, P_, TP))
    v6 = D(w, ph, 'oveq2d', [D(w, ph, 'divcan2d', [hpc, tc, tn], '( %s x. ( ( H ` %s ) / %s ) ) = ( H ` %s )' % (TP, P_, TP, P_))],
           '( _i x. ( %s x. ( ( H ` %s ) / %s ) ) ) = ( _i x. ( H ` %s ) )' % (TP, P_, TP, P_))
    chain_ = res
    for st_, rhs in ((v2, '( %s x. ( ( H ` %s ) / %s ) )' % (TWOPI_I, P_, TP)), (v4, '( ( _i x. %s ) x. ( ( H ` %s ) / %s ) )' % (TP, P_, TP)),
                     (v5, '( _i x. ( %s x. ( ( H ` %s ) / %s ) ) )' % (TP, P_, TP)), (v6, '( _i x. ( H ` %s ) )' % P_)):
        chain_ = D(w, ph, 'eqtrd', [chain_, st_], '%s = %s' % (RI(FK, A_, B_), rhs))
    w.qed([chain_], 'idi', S['zl3resn'])
    go(w, only)
