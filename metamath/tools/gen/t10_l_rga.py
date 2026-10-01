"""T10: the resGo arithmetic the resGoF loop reads (Lean ` resGo_shift ` at one step, from the front recursion).

  rgstep   ` resGo z99 y q ( i + 1 ) = ( ( resGo z99 y q i ).1 ++ keep ( q + i ) , ( resGo z99 y q i ).2 + cost ( q + i ) ) `

    MM_DB=sorties/t10.mm python3 tools/gen/t10_l_rga.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
from lin import linarith, lineq
from cl import Closure
from t10_e_doa import P1, P2, snd_of, fst_of, ex_, lift_from

SEL = sys.argv[1:]
RGX = lambda q, f: '( ( ( G ResGo Y ) ` %s ) ` %s )' % (q, f)
KC = lambda q: 'if ( G < %s , if ( ( 1st ` ( IsPrimeTD ` %s ) ) = 1o , ( 1st ` ( Y SmoothTD ( %s - 1 ) ) ) , (/) ) , (/) ) = 1o' % (q, q, q)
KEEPW = lambda q: 'if ( %s , <" %s "> , (/) )' % (KC(q), q)
IPC = lambda q: '( 2nd ` ( IsPrimeTD ` %s ) )' % q
SMC = lambda q: '( 2nd ` ( Y SmoothTD ( %s - 1 ) ) )' % q
CST = lambda q: '( ( %s + %s ) + 1 )' % (IPC(q), SMC(q))
STV = lambda q, i: '<. ( %s ++ %s ) , ( %s + %s ) >.' % (P1(RGX(q, i)), KEEPW('( %s + %s )' % (q, i)), P2(RGX(q, i)), CST('( %s + %s )' % (q, i)))
PH = '( G e. NN0 /\\ Y e. NN )'
ST_RGSTEP = '( ( %s /\\ ( Q e. NN /\\ I e. NN0 ) ) -> %s = %s )' % (PH, RGX('Q', '( I + 1 )'), STV('Q', 'I'))


def rgcl(w, ph, q, f, gn, ynn, qnn, fn):
    s = w.s
    return s([s([s([gn, ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), qnn], 'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ %s e. NN ) )' % (ph, q)),
              fn, w.inst('resgocl')], 'syl2anc', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, RGX(q, f)))


def rgp1(w, ph, q, f, gn, ynn, qnn, fn):
    """( ph -> RGX( q , ( f + 1 ) ) = <. if .. , .. >. ) (resgop1)"""
    s = w.s
    R1 = RGX('( %s + 1 )' % q, f)
    V = '<. if ( %s , ( <" %s "> ++ %s ) , %s ) , ( ( ( %s + %s ) + %s ) + 1 ) >.' % (KC(q), q, P1(R1), P1(R1), P2(R1), IPC(q), SMC(q))
    st = s([s([s([gn, ynn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), qnn], 'jca', '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ %s e. NN ) )' % (ph, q)),
            fn, w.inst('resgop1')], 'syl2anc', '( %s -> %s = %s )' % (ph, RGX(q, '( %s + 1 )' % f), V))
    return st, V, R1


def rgstep():
    lab = 'rgstep'
    w = W(lab, 'One step of Lean\'s ` resGo ` from the back ( ` resGo_shift ` at ` i + 1 ` ): the first ` i + 1 ` iterations are the '
               'first ` i ` followed by the test of ` q + i ` , which keeps it iff ` resKeep z99 y ( q + i ) ` and charges '
               '` isPrimeTD ` , ` smoothTD ` and one.')
    s = w.s
    ph = PH
    gn = s([], 'simpl', '( %s -> G e. NN0 )' % ph)
    ynn = s([], 'simpr', '( %s -> Y e. NN )' % ph)
    PS = lambda n: 'A. k e. NN %s = %s' % (RGX('k', '( %s + 1 )' % n), STV('k', n))
    BODY = lambda n, v: '%s = %s' % (RGX(v, '( %s + 1 )' % n), STV(v, n))

    def cbv(n):
        e = s([], 'id', '( h = k -> h = k )')
        cg, new = w.wcongr(BODY(n, 'h'), {'h': 'k'}, 'h = k', {'h': e})
        assert new == BODY(n, 'k'), new
        return s([cg], 'cbvralvw', '( A. h e. NN %s <-> %s )' % (BODY(n, 'h'), PS(n)))

    def sb(b):
        e = s([], 'id', '( n = %s -> n = %s )' % (b, b))
        st, new = w.wcongr(PS('n'), {'n': b}, 'n = %s' % b, {'n': e})
        assert new == PS(b), new
        return st
    hy1, hy2, hy3, hy4 = sb('0'), sb('m'), sb('( m + 1 )'), sb('I')
    # ---------------- base
    pb = '( %s /\\ h e. NN )' % ph
    hnn = s([], 'simpr', '( %s -> h e. NN )' % pb)
    gb, yb = lift_from(w, ph, pb, gn), lift_from(w, ph, pb, ynn)
    z0 = closed(w, pb, '0nn0', '0 e. NN0')
    st1, V1, R1 = rgp1(w, pb, 'h', '0', gb, yb, hnn, z0)
    h1n = s([hnn, w.inst('peano2nn')], 'syl', '( %s -> ( h + 1 ) e. NN )' % pb)
    r10 = s([s([s([gb, yb], 'jca', '( %s -> %s )' % (pb, PH)), h1n], 'jca', '( %s -> ( %s /\\ ( h + 1 ) e. NN ) )' % (pb, PH)), w.inst('resgo0')],
            'syl', '( %s -> %s = <. (/) , 0 >. )' % (pb, R1))
    ee = s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % pb)
    ze = s([s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % pb)
    f1 = fst_of(w, pb, R1, '(/)', '0', r10, ee, ze)
    f2 = snd_of(w, pb, R1, '(/)', '0', r10, ee, ze)
    rw1, x1 = w.rewrite(V1, {P1(R1): ('(/)', f1), P2(R1): ('0', f2)}, pb)
    hs1 = s([s([hnn], 'nnnn0d', '( %s -> h e. NN0 )' % pb), w.inst('s1cl') if False else w.inst('s1cld') if False else w.inst('s1cl')], 'syl',
            '( %s -> <" h "> e. Word NN0 )' % pb) if False else None
    hw = s([s([hnn], 'nnnn0d', '( %s -> h e. NN0 )' % pb)], 's1cld', '( %s -> <" h "> e. Word NN0 )' % pb)
    cr = s([hw, w.inst('ccatrid')], 'syl', '( %s -> ( <" h "> ++ (/) ) = <" h "> )' % pb)
    rw2, x2 = w.rewrite(x1, {'( <" h "> ++ (/) )': ('<" h ">', cr)}, pb)
    # RHS at 0
    R0 = RGX('h', '0')
    r0 = s([s([s([gb, yb], 'jca', '( %s -> %s )' % (pb, PH)), hnn], 'jca', '( %s -> ( %s /\\ h e. NN ) )' % (pb, PH)), w.inst('resgo0')],
           'syl', '( %s -> %s = <. (/) , 0 >. )' % (pb, R0))
    g1 = fst_of(w, pb, R0, '(/)', '0', r0, ee, ze)
    g2 = snd_of(w, pb, R0, '(/)', '0', r0, ee, ze)
    h0 = s([s([hnn], 'nncnd', '( %s -> h e. CC )' % pb), w.inst('addrid')], 'syl', '( %s -> ( h + 0 ) = h )' % pb)
    rw3, x3 = w.rewrite(STV('h', '0'), {P1(R0): ('(/)', g1), P2(R0): ('0', g2), '( h + 0 )': ('h', h0)}, pb)
    kw_ = s([hw, s([s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % pb)], 'ifcld', '( %s -> %s e. Word NN0 )' % (pb, KEEPW('h')))
    cl_ = s([kw_, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (pb, KEEPW('h'), KEEPW('h')))
    rw4, x4 = w.rewrite(x3, {'( (/) ++ %s )' % KEEPW('h'): (KEEPW('h'), cl_)}, pb)
    ipn = s([s([s([hnn], 'nnnn0d', '( %s -> h e. NN0 )' % pb), w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` h ) e. ( 2o X. NN0 ) )' % pb),
             w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pb, IPC('h')))
    smn = s([s([yb, s([hnn, w.inst('nnm1nn0')], 'syl', '( %s -> ( h - 1 ) e. NN0 )' % pb), w.inst('smoothtdcl')], 'syl2anc',
               '( %s -> ( Y SmoothTD ( h - 1 ) ) e. ( 2o X. NN0 ) )' % pb), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (pb, SMC('h')))
    cl = Closure(w, pb, {})
    cl.leaf(IPC('h'), 'NN0', ipn)
    cl.leaf(SMC('h'), 'NN0', smn)
    ar = lineq(w, pb, '( ( ( 0 + %s ) + %s ) + 1 )' % (IPC('h'), SMC('h')), '( 0 + %s )' % CST('h'), closure=cl)
    rw5, x5 = w.rewrite(x2, {'( ( ( 0 + %s ) + %s ) + 1 )' % (IPC('h'), SMC('h')): ('( 0 + %s )' % CST('h'), ar)}, pb)
    assert x5 == x4, (x5, x4)
    L_ = RGX('h', '( 0 + 1 )')
    chain = s([s([st1, rw1], 'eqtrd', '( %s -> %s = %s )' % (pb, L_, x1)), rw2], 'eqtrd', '( %s -> %s = %s )' % (pb, L_, x2))
    chain = s([chain, rw5], 'eqtrd', '( %s -> %s = %s )' % (pb, L_, x5))
    rr = s([rw3, rw4], 'eqtrd', '( %s -> %s = %s )' % (pb, STV('h', '0'), x4))
    e0 = s([chain, rr], 'eqtr4d', '( %s -> %s )' % (pb, BODY('0', 'h')))
    base0 = s([e0], 'ralrimiva', '( %s -> A. h e. NN %s )' % (ph, BODY('0', 'h')))
    base = s([base0, cbv('0')], 'sylib', '( %s -> %s )' % (ph, PS('0')))
    # ---------------- step
    a = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (ph, PS('m'))
    b = '( %s /\\ h e. NN )' % a
    mn = lift_from(w, '( %s /\\ m e. NN0 )' % ph, b, s([], 'simpr', '( ( %s /\\ m e. NN0 ) -> m e. NN0 )' % ph))
    ih = lift_from(w, a, b, s([], 'simpr', '( %s -> %s )' % (a, PS('m'))))
    hn = s([], 'simpr', '( %s -> h e. NN )' % b)
    g2_, y2 = lift_from(w, ph, b, gn), lift_from(w, ph, b, ynn)
    h1 = '( h + 1 )'
    h1nn = s([hn, w.inst('peano2nn')], 'syl', '( %s -> %s e. NN )' % (b, h1))
    e = s([], 'id', '( k = %s -> k = %s )' % (h1, h1))
    cg, new = w.wcongr(BODY('m', 'k'), {'k': h1}, 'k = %s' % h1, {'k': e})
    ihh = s([h1nn, ih, s([cg], 'rspcv', '( %s e. NN -> ( %s -> %s ) )' % (h1, PS('m'), new))], 'sylc', '( %s -> %s )' % (b, new))
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % b)
    stL, VL, RL = rgp1(w, b, 'h', '( m + 1 )', g2_, y2, hn, m1n)      # LHS: RG( h , ( m + 1 ) + 1 )
    stR, VR, RR_ = rgp1(w, b, 'h', 'm', g2_, y2, hn, mn)             # RG( h , m + 1 )
    assert RL == RGX(h1, '( m + 1 )') and RR_ == RGX(h1, 'm')
    A_, a_ = P1(RGX(h1, 'm')), P2(RGX(h1, 'm'))
    Wq = KEEPW('( %s + m )' % h1)
    Cq = CST('( %s + m )' % h1)
    ha = s([cl_mem(w, b, 'h', hn), cl_mem(w, b, 'm', mn), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % b), w.inst('add32')], 'syl3anc',
           '( %s -> ( ( h + 1 ) + m ) = ( ( h + m ) + 1 ) )' % b) if False else None
    hq = s([s([hn], 'nncnd', '( %s -> h e. CC )' % b), s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % b),
            s([mn], 'nn0cnd', '( %s -> m e. CC )' % b), w.inst('add32')], 'syl3anc', '( %s -> ( ( h + 1 ) + m ) = ( ( h + m ) + 1 ) )' % b)
    hq2 = s([s([hn], 'nncnd', '( %s -> h e. CC )' % b), s([mn], 'nn0cnd', '( %s -> m e. CC )' % b),
             s([s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % b), w.inst('addass')], 'syl3anc',
            '( %s -> ( ( h + m ) + 1 ) = ( h + ( m + 1 ) ) )' % b)
    hq3 = s([hq, hq2], 'eqtrd', '( %s -> ( %s + m ) = ( h + ( m + 1 ) ) )' % (b, h1))
    # LHS
    ihv = '<. ( %s ++ %s ) , ( %s + %s ) >.' % (A_, Wq, a_, Cq)
    aw = s([s([rgcl(w, b, h1, 'm', g2_, y2, h1nn, mn), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (b, A_))], 'id', '') if False else \
        s([rgcl(w, b, h1, 'm', g2_, y2, h1nn, mn), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (b, A_))
    an = s([rgcl(w, b, h1, 'm', g2_, y2, h1nn, mn), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (b, a_))
    wex = ex_(w, b, '( %s ++ %s )' % (A_, Wq), 'ovex')
    cex = ex_(w, b, '( %s + %s )' % (a_, Cq), 'ovex')
    p1 = fst_of(w, b, RL, '( %s ++ %s )' % (A_, Wq), '( %s + %s )' % (a_, Cq), ihh, wex, cex)
    p2 = snd_of(w, b, RL, '( %s ++ %s )' % (A_, Wq), '( %s + %s )' % (a_, Cq), ihh, wex, cex)
    rl1, xl1 = w.rewrite(VL, {P1(RL): ('( %s ++ %s )' % (A_, Wq), p1), P2(RL): ('( %s + %s )' % (a_, Cq), p2)}, b)
    Lh = RGX('h', '( ( m + 1 ) + 1 )')
    lhs = s([stL, rl1], 'eqtrd', '( %s -> %s = %s )' % (b, Lh, xl1))
    # RHS
    rr1, xr1 = w.rewrite(STV('h', '( m + 1 )'), {RGX('h', '( m + 1 )'): (VR, stR)}, b)
    Kh = KC('h')
    IFR = 'if ( %s , ( <" h "> ++ %s ) , %s )' % (Kh, A_, A_)
    CR = '( ( ( %s + %s ) + %s ) + 1 )' % (a_, IPC('h'), SMC('h'))
    ifx = ifex_closed(w, b, Kh, '( <" h "> ++ %s )' % A_, A_, s([], 'ovex', '( <" h "> ++ %s ) e. _V' % A_), s([], 'fvex', '%s e. _V' % A_))
    q1 = s([ifx, ex_(w, b, CR, 'ovex'), w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (b, VR, IFR))
    q2 = s([ifx, ex_(w, b, CR, 'ovex'), w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (b, VR, CR))
    rr2, xr2 = w.rewrite(xr1, {'( 1st ` %s )' % VR: (IFR, q1), '( 2nd ` %s )' % VR: (CR, q2)}, b)
    Wh = KEEPW('( h + ( m + 1 ) )')
    Ch = CST('( h + ( m + 1 ) )')
    rr3, xr3 = w.rewrite(xl1, {'( %s + m )' % h1: ('( h + ( m + 1 ) )', hq3)}, b)
    # 1st: if ( K , <" h "> ++ A , A ) ++ W = if ( K , <" h "> ++ ( A ++ W ) , A ++ W )
    ov = s([], 'ovif', '( %s ++ %s ) = if ( %s , ( ( <" h "> ++ %s ) ++ %s ) , ( %s ++ %s ) )' % (IFR, Wh, Kh, A_, Wh, A_, Wh))
    hw2 = s([s([hn], 'nnnn0d', '( %s -> h e. NN0 )' % b)], 's1cld', '( %s -> <" h "> e. Word NN0 )' % b)
    ww = s([s([s([s([hn, m1n, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( h + ( m + 1 ) ) e. NN )' % b)], 'nnnn0d',
                 '( %s -> ( h + ( m + 1 ) ) e. NN0 )' % b)], 's1cld', '( %s -> <" ( h + ( m + 1 ) ) "> e. Word NN0 )' % b),
            s([s([], 'wrd0', '(/) e. Word NN0')], 'a1i', '( %s -> (/) e. Word NN0 )' % b)], 'ifcld', '( %s -> %s e. Word NN0 )' % (b, Wh))
    ca = s([hw2, aw, ww, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" h "> ++ %s ) ++ %s ) = ( <" h "> ++ ( %s ++ %s ) ) )' % (b, A_, Wh, A_, Wh))
    IFL = 'if ( %s , ( <" h "> ++ ( %s ++ %s ) ) , ( %s ++ %s ) )' % (Kh, A_, Wh, A_, Wh)
    fe = s([s([ov], 'a1i', '( %s -> ( %s ++ %s ) = if ( %s , ( ( <" h "> ++ %s ) ++ %s ) , ( %s ++ %s ) ) )' % (b, IFR, Wh, Kh, A_, Wh, A_, Wh)),
            s([ca], 'ifeq1d', '( %s -> if ( %s , ( ( <" h "> ++ %s ) ++ %s ) , ( %s ++ %s ) ) = %s )' % (b, Kh, A_, Wh, A_, Wh, IFL))], 'eqtrd',
           '( %s -> ( %s ++ %s ) = %s )' % (b, IFR, Wh, IFL))
    rr4, xr4 = w.rewrite(xr2, {'( %s ++ %s )' % (IFR, Wh): (IFL, fe)}, b)
    # 2nd: arithmetic
    clb = Closure(w, b, {})
    ipq = s([s([s([s([hn, m1n, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( h + ( m + 1 ) ) e. NN )' % b)], 'nnnn0d',
                  '( %s -> ( h + ( m + 1 ) ) e. NN0 )' % b), w.inst('isprimetdcl')], 'syl',
               '( %s -> ( IsPrimeTD ` ( h + ( m + 1 ) ) ) e. ( 2o X. NN0 ) )' % b), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (b, IPC('( h + ( m + 1 ) )')))
    smq = s([s([y2, s([s([hn, m1n, w.inst('nnnn0addcl')], 'syl2anc', '( %s -> ( h + ( m + 1 ) ) e. NN )' % b), w.inst('nnm1nn0')], 'syl',
                         '( %s -> ( ( h + ( m + 1 ) ) - 1 ) e. NN0 )' % b), w.inst('smoothtdcl')], 'syl2anc',
               '( %s -> ( Y SmoothTD ( ( h + ( m + 1 ) ) - 1 ) ) e. ( 2o X. NN0 ) )' % b), w.inst('xp2nd')], 'syl',
            '( %s -> %s e. NN0 )' % (b, SMC('( h + ( m + 1 ) )')))
    iph = s([s([s([s([hn], 'nnnn0d', '( %s -> h e. NN0 )' % b), w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` h ) e. ( 2o X. NN0 ) )' % b),
               w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (b, IPC('h')))], 'id', '') if False else \
        s([s([s([hn], 'nnnn0d', '( %s -> h e. NN0 )' % b), w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` h ) e. ( 2o X. NN0 ) )' % b),
           w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (b, IPC('h')))
    smh = s([s([y2, s([hn, w.inst('nnm1nn0')], 'syl', '( %s -> ( h - 1 ) e. NN0 )' % b), w.inst('smoothtdcl')], 'syl2anc',
               '( %s -> ( Y SmoothTD ( h - 1 ) ) e. ( 2o X. NN0 ) )' % b), w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (b, SMC('h')))
    for x_, st_ in ((a_, an), (IPC('( h + ( m + 1 ) )'), ipq), (SMC('( h + ( m + 1 ) )'), smq), (IPC('h'), iph), (SMC('h'), smh)):
        clb.leaf(x_, 'NN0', st_)
    CL3 = '( ( ( ( %s + %s ) + %s ) + %s ) + 1 )' % (a_, Ch, IPC('h'), SMC('h'))
    CR3 = '( %s + %s )' % (CR, Ch)
    ar2 = lineq(w, b, CL3, CR3, closure=clb)
    rr5, xr5 = w.rewrite(xr3, {CL3: (CR3, ar2)}, b)
    assert xr5 == xr4, (xr5, xr4)
    fin = s([s([lhs, rr3], 'eqtrd', '( %s -> %s = %s )' % (b, Lh, xr3)), rr5], 'eqtrd', '( %s -> %s = %s )' % (b, Lh, xr5))
    rhs = s([rr1, rr2], 'eqtrd', '( %s -> %s = %s )' % (b, STV('h', '( m + 1 )'), xr2))
    rhs = s([rhs, rr4], 'eqtrd', '( %s -> %s = %s )' % (b, STV('h', '( m + 1 )'), xr4))
    e1 = s([fin, rhs], 'eqtr4d', '( %s -> %s )' % (b, BODY('( m + 1 )', 'h')))
    st0 = s([e1], 'ralrimiva', '( %s -> A. h e. NN %s )' % (a, BODY('( m + 1 )', 'h')))
    st = s([st0, cbv('( m + 1 )')], 'sylib', '( %s -> %s )' % (a, PS('( m + 1 )')))
    ind = s([hy1, hy2, hy3, hy4, base, st], 'nn0indd', '( ( %s /\\ I e. NN0 ) -> %s )' % (ph, PS('I')))
    p = '( %s /\\ ( Q e. NN /\\ I e. NN0 ) )' % ph
    ps = s([s([s([], 'simpl', '( %s -> %s )' % (p, ph)), s([], 'simprr', '( %s -> I e. NN0 )' % p)], 'jca', '( %s -> ( %s /\\ I e. NN0 ) )' % (p, ph)),
            ind], 'syl', '( %s -> %s )' % (p, PS('I')))
    e = s([], 'id', '( k = Q -> k = Q )')
    cg, new = w.wcongr(BODY('I', 'k'), {'k': 'Q'}, 'k = Q', {'k': e})
    r = s([cg], 'rspcv', '( Q e. NN -> ( %s -> %s ) )' % (PS('I'), new))
    w.qed([s([], 'simprl', '( %s -> Q e. NN )' % p), ps, r], 'sylc', ST_RGSTEP)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
