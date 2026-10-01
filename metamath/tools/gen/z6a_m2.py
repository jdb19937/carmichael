"""Z6a (block D): the Gamma majorants (z6mycx, z6mg64, z6mgdiv, z6mndg, z6mnhz, z6mre1, z6mgup, z6mgstr, z6mgln)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_mlib import *

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def rl(w, A, E, st):
    """leaf helper"""
    return (E, st)


# ---------------------------------------------------------------- z6mycx
def z6mycx():
    w = W('z6mycx', '` Y ^ X <_ Y ^ B + Y ^ A ` for ` A <_ X <_ B ` : for ` 1 <_ Y ` the power increases in the exponent ( ~ cxplea ), '
          'for ` Y < 1 ` it decreases ( ~ cxple3 ).')
    A0 = split_imp(STATEMENTS['z6mycx'])[0]
    s = mkst(w, A0)
    yrp = w.s([], 'simp1', '( %s -> Y e. RR+ )' % A0)
    abx = w.s([], 'simp2', '( %s -> ( A e. RR /\\ B e. RR /\\ X e. RR ) )' % A0)
    ax = w.s([], 'simp3', '( %s -> ( A <_ X /\\ X <_ B ) )' % A0)
    ar = s([abx], 'simp1d', 'A e. RR'); br = s([abx], 'simp2d', 'B e. RR'); xr = s([abx], 'simp3d', 'X e. RR')
    alx = s([ax], 'simpld', 'A <_ X'); xlb = s([ax], 'simprd', 'X <_ B')
    yr = s([yrp], 'rpred', 'Y e. RR')
    YX, YB, YA = '( Y ^c X )', '( Y ^c B )', '( Y ^c A )'
    def pw(E, er):
        return s([yrp, er], 'rpcxpcld', '( Y ^c %s ) e. RR+' % E)
    yxp, ybp, yap = pw('X', xr), pw('B', br), pw('A', ar)
    GOAL = '%s <_ ( %s + %s )' % (YX, YB, YA)
    # 1 <_ Y
    At = '( %s /\\ 1 <_ Y )' % A0
    t = mkst(w, At)
    c1_ = t([t([lift(w, yr, At), w.s([], 'simpr', '( %s -> 1 <_ Y )' % At)], 'jca', '( Y e. RR /\\ 1 <_ Y )'),
             t([lift(w, xr, At), lift(w, br, At)], 'jca', '( X e. RR /\\ B e. RR )'), lift(w, xlb, At), w.inst('cxplea')], 'syl3anc', '%s <_ %s' % (YX, YB))
    lv = {YX: ('RR', t([lift(w, yxp, At)], 'rpred', '%s e. RR' % YX)), YB: ('RR', t([lift(w, ybp, At)], 'rpred', '%s e. RR' % YB)),
          YA: ('RR', t([lift(w, yap, At)], 'rpred', '%s e. RR' % YA))}
    tt = linarith(w, At, [c1_, t([lift(w, yap, At)], 'rpge0d', '0 <_ %s' % YA)], GOAL, leaves=lv)
    # Y < 1
    Af = '( %s /\\ -. 1 <_ Y )' % A0
    f = mkst(w, Af)
    ylt = f([w.s([], 'simpr', '( %s -> -. 1 <_ Y )' % Af), f([lift(w, yr, Af), c1(w, Af, '1re', '1 e. RR'), w.inst('ltnle')], 'syl2anc', '( Y < 1 <-> -. 1 <_ Y )')],
            'mpbird', 'Y < 1')
    bi = f([f([lift(w, yrp, Af), ylt], 'jca', '( Y e. RR+ /\\ Y < 1 )'), f([lift(w, ar, Af), lift(w, xr, Af)], 'jca', '( A e. RR /\\ X e. RR )'), w.inst('cxple3')],
           'syl2anc', '( A <_ X <-> %s <_ %s )' % (YX, YA))
    c2_ = f([lift(w, alx, Af), bi], 'mpbid', '%s <_ %s' % (YX, YA))
    lv = {YX: ('RR', f([lift(w, yxp, Af)], 'rpred', '%s e. RR' % YX)), YB: ('RR', f([lift(w, ybp, Af)], 'rpred', '%s e. RR' % YB)),
          YA: ('RR', f([lift(w, yap, Af)], 'rpred', '%s e. RR' % YA))}
    ff = linarith(w, Af, [c2_, f([lift(w, ybp, Af)], 'rpge0d', '0 <_ %s' % YB)], GOAL, leaves=lv)
    w.qed([tt, ff], 'pm2.61dan', STATEMENTS['z6mycx'])
    return w


# ---------------------------------------------------------------- z6mg64
def z6mg64():
    w = W('z6mg64', 'The Gamma strip bound ` | _G ( W ) | <_ 64 2 ^ ( - | Im W | / 4 ) ` on ` 1 / 2 <_ Re W <_ 3 ` '
          '( ~ gamvb with ~ z6gamre : ` 16 ( 2 + 2 ) = 64 ` ; ` 2 ^ ( - x / 2 ) <_ 2 ^ ( - x / 4 ) ` ).')
    A0 = split_imp(STATEMENTS['z6mg64'])[0]
    s = mkst(w, A0)
    R = '( Re ` W )'
    wc = w.s([], 'simpl', '( %s -> W e. CC )' % A0)
    lo = w.s([], 'simprl', '( %s -> ( 1 / 2 ) <_ %s )' % (A0, R))
    hi = w.s([], 'simprr', '( %s -> %s <_ 3 )' % (A0, R))
    rr = s([wc], 'recld', '%s e. RR' % R)
    cl = Closure(w, A0, {})
    cl.leaf(R, 'RR', rr)
    rgt = linarith(w, A0, [lo], '0 < %s' % R, closure=cl)
    rrp = s([rr, rgt], 'elrpd', '%s e. RR+' % R)
    GR_ = '( _G ` %s )' % R
    gre = s([s([rr, rgt, hi], '3jca', '( %s e. RR /\\ 0 < %s /\\ %s <_ 3 )' % (R, R, R)), w.inst('z6gamre')], 'syl', '%s <_ ( ( 1 / %s ) + 2 )' % (GR_, R))
    H = '( 1 / 2 )'
    lr = s([s([cl.mem(H, 'RR'), cl.gt0(H)], 'jca', '( %s e. RR /\\ 0 < %s )' % (H, H)), s([rr, rgt], 'jca', '( %s e. RR /\\ 0 < %s )' % (R, R)), w.inst('lerec')], 'syl2anc',
           '( %s <_ %s <-> ( 1 / %s ) <_ ( 1 / %s ) )' % (H, R, R, H))
    r1 = s([lo, lr], 'mpbid', '( 1 / %s ) <_ ( 1 / %s )' % (R, H))
    rr1 = s([c1(w, A0, '2cn', '2 e. CC'), c1(w, A0, '2ne0', '2 =/= 0'), w.inst('recrec')], 'syl2anc', '( 1 / %s ) = 2' % H)
    r2 = s([r1, rr1], 'breqtrd', '( 1 / %s ) <_ 2' % R)
    cl.leaf(GR_, 'RR', s([sy2(w, A0, rr, rgt, 'gamrrp', '%s e. RR+' % GR_)], 'rpred', '%s e. RR' % GR_))
    cl.leaf('( 1 / %s )' % R, 'RR', s([s([rrp], 'rpreccld', '( 1 / %s ) e. RR+' % R)], 'rpred', '( 1 / %s ) e. RR' % R))
    A16 = '( ; 1 6 x. %s )' % GR_
    b16 = linarith(w, A0, [gre, r2], '%s <_ ; 6 4' % A16, closure=cl)
    AI = '( abs ` ( Im ` W ) )'
    air = s([s([s([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')], 'abscld', '%s e. RR' % AI)
    cl.leaf(AI, 'RR', air)
    e2, e4 = E2(AI), E4(AI)
    n2 = cl.mem('-u ( %s / 2 )' % AI, 'RR'); n4 = cl.mem('-u ( %s / 4 )' % AI, 'RR')
    e2p = s([cl.mem('2', 'RR+'), n2], 'rpcxpcld', '%s e. RR+' % e2)
    e4p = s([cl.mem('2', 'RR+'), n4], 'rpcxpcld', '%s e. RR+' % e4)
    e2r = s([e2p], 'rpred', '%s e. RR' % e2); e4r = s([e4p], 'rpred', '%s e. RR' % e4)
    aige = s([s([s([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')], 'absge0d', '0 <_ %s' % AI)
    nle = linarith(w, A0, [aige], '-u ( %s / 2 ) <_ -u ( %s / 4 )' % (AI, AI), closure=cl)
    e24 = s([s([cl.mem('2', 'RR'), num_le(w, A0, '1', '2')], 'jca', '( 2 e. RR /\\ 1 <_ 2 )'), s([n2, n4], 'jca', '( -u ( %s / 2 ) e. RR /\\ -u ( %s / 4 ) e. RR )' % (AI, AI)), nle,
             w.inst('cxplea')], 'syl3anc', '%s <_ %s' % (e2, e4))
    ddg = sy2(w, A0, wc, rgt, 'zrenn', 'W e. %s' % DG)
    gdr = s([s([ddg, w.inst('gamcl')], 'syl', '( _G ` W ) e. CC')], 'abscld', '( abs ` ( _G ` W ) ) e. RR')
    gv = s([s([wc, rgt, hi], '3jca', '( W e. CC /\\ 0 < %s /\\ %s <_ 3 )' % (R, R)), w.inst('gamvb')], 'syl', '( abs ` ( _G ` W ) ) <_ ( %s x. %s )' % (A16, e2))
    a16r = cl.mem(A16, 'RR'); r64 = cl.mem('; 6 4', 'RR')
    m1 = s([a16r, r64, e2r, s([e2p], 'rpge0d', '0 <_ %s' % e2), b16], 'lemul1ad', '( %s x. %s ) <_ ( ; 6 4 x. %s )' % (A16, e2, e2))
    m2 = s([e2r, e4r, r64, cl.ge0('; 6 4'), e24], 'lemul2ad', '( ; 6 4 x. %s ) <_ ( ; 6 4 x. %s )' % (e2, e4))
    p1 = s([a16r, e2r], 'remulcld', '( %s x. %s ) e. RR' % (A16, e2))
    p2 = s([r64, e2r], 'remulcld', '( ; 6 4 x. %s ) e. RR' % e2)
    p3 = s([r64, e4r], 'remulcld', '( ; 6 4 x. %s ) e. RR' % e4)
    t1 = s([gdr, p1, p2, gv, m1], 'letrd', '( abs ` ( _G ` W ) ) <_ ( ; 6 4 x. %s )' % e2)
    w.qed([gdr, p2, p3, t1, m2], 'letrd', STATEMENTS['z6mg64'])
    return w


def negh(w):
    """closed: ( -u 0 - ( 1 / 2 ) ) = -u ( 1 / 2 )"""
    a = w.s([w.s([], 'neg0', '-u 0 = 0')], 'oveq1i', '( -u 0 - ( 1 / 2 ) ) = ( 0 - ( 1 / 2 ) )')
    b = w.s([], 'df-neg', '-u ( 1 / 2 ) = ( 0 - ( 1 / 2 ) )')
    return w.s([a, b], 'eqtr4i', '( -u 0 - ( 1 / 2 ) ) = -u ( 1 / 2 )')


def negz(w, A, cl):
    """declare -u 0 atomic real in cl; return the step ( A -> -u 0 = 0 ) for linarith's hyps"""
    n0 = w.s([], 'neg0', '-u 0 = 0')
    r = w.s([n0, w.s([], '0re', '0 e. RR')], 'eqeltri', '-u 0 e. RR')
    cl.leaf('-u 0', 'RR', w.s([r], 'a1i', '( %s -> -u 0 e. RR )' % A))
    return w.s([n0], 'a1i', '( %s -> -u 0 = 0 )' % A)


def num_le(w, A0, a, b):
    return w.s([num.le_lit(w, a, b)], 'a1i', '( %s -> %s <_ %s )' % (A0, a, b))


# ---------------------------------------------------------------- z6mgdiv
def z6mgdiv():
    w = W('z6mgdiv', 'One step of the functional equation to the left: ` | _G ( W ) | <_ | _G ( W + 1 ) | / R ` when ` R <_ | W | ` ( ~ gamp1 ).')
    A0 = split_imp(STATEMENTS['z6mgdiv'])[0]
    s = mkst(w, A0)
    wd = w.s([], 'simpl', '( %s -> W e. %s )' % (A0, DG))
    rrp = w.s([], 'simprl', '( %s -> R e. RR+ )' % A0)
    rle = w.s([], 'simprr', '( %s -> R <_ ( abs ` W ) )' % A0)
    wc = s([wd], 'eldifad', 'W e. CC')
    g = s([wd, w.inst('gamp1')], 'syl', '( _G ` ( W + 1 ) ) = ( ( _G ` W ) x. W )')
    gwc = s([wd, w.inst('gamcl')], 'syl', '( _G ` W ) e. CC')
    AG = '( abs ` ( _G ` W ) )'; AG1 = '( abs ` ( _G ` ( W + 1 ) ) )'; AW = '( abs ` W )'
    am = s([s([g], 'fveq2d', '%s = ( abs ` ( ( _G ` W ) x. W ) )' % AG1), s([gwc, wc], 'absmuld', '( abs ` ( ( _G ` W ) x. W ) ) = ( %s x. %s )' % (AG, AW))], 'eqtrd',
           '%s = ( %s x. %s )' % (AG1, AG, AW))
    agr = s([gwc], 'abscld', '%s e. RR' % AG)
    awr = s([wc], 'abscld', '%s e. RR' % AW)
    rr = s([rrp], 'rpred', 'R e. RR')
    m = s([rr, awr, agr, s([gwc], 'absge0d', '0 <_ %s' % AG), rle], 'lemul2ad', '( %s x. R ) <_ ( %s x. %s )' % (AG, AG, AW))
    m2 = s([m, am], 'breqtrrd', '( %s x. R ) <_ %s' % (AG, AG1))
    ag1r = s([am, s([agr, awr], 'remulcld', '( %s x. %s ) e. RR' % (AG, AW))], 'eqeltrd', '%s e. RR' % AG1)
    bi = s([agr, ag1r, rrp], 'lemuldivd', '( ( %s x. R ) <_ %s <-> %s <_ ( %s / R ) )' % (AG, AG1, AG, AG1))
    w.qed([m2, bi], 'mpbid', STATEMENTS['z6mgdiv'])
    return w


# ---------------------------------------------------------------- z6mndg
def z6mndg():
    w = W('z6mndg', 'A point whose real part is not an integer, or whose imaginary part is not zero, lies in the domain of ` _G ` .')
    A0 = split_imp(STATEMENTS['z6mndg'])[0]
    DJ = '( -. ( Re ` W ) e. ZZ \\/ ( Im ` W ) =/= 0 )'
    wc = w.s([], 'simpl', '( %s -> W e. CC )' % A0)
    A1 = '( %s /\\ W e. ( ZZ \\ NN ) )' % A0
    t = mkst(w, A1)
    wz = t([w.s([], 'simpr', '( %s -> W e. ( ZZ \\ NN ) )' % A1)], 'eldifad', 'W e. ZZ')
    wr = t([wz], 'zred', 'W e. RR')
    rz = t([t([wr], 'rered', '( Re ` W ) = W'), wz], 'eqeltrd', '( Re ` W ) e. ZZ')
    im = t([wr, w.inst('reim0')], 'syl', '( Im ` W ) = 0')
    n1 = t([rz], 'notnotd', '-. -. ( Re ` W ) e. ZZ')
    n2 = t([im, w.inst('nne')], 'sylibr', '-. ( Im ` W ) =/= 0')
    nd = t([t([n1, n2], 'jca', '( -. -. ( Re ` W ) e. ZZ /\\ -. ( Im ` W ) =/= 0 )'), w.inst('ioran')], 'sylibr', '-. %s' % DJ)
    dj = lift(w, w.s([], 'simpr', '( %s -> %s )' % (A0, DJ)), A1)
    nw = w.s([dj, nd], 'pm2.65da', '( %s -> -. W e. ( ZZ \\ NN ) )' % A0)
    w.qed([wc, nw], 'eldifd', STATEMENTS['z6mndg'])
    return w


# ---------------------------------------------------------------- z6mnhz
def z6mnhz():
    w = W('z6mnhz', 'The lines ` Re w = -u K - 1 / 2 ` and ` Re w = 1 / 2 - K ` avoid the integers ( ~ halfnz ).')
    A0 = 'K e. NN0'
    s = mkst(w, A0)
    kz = s([w.s([], 'id', '( %s -> %s )' % (A0, A0))], 'nn0zd', 'K e. ZZ')
    H = '( 1 / 2 )'
    L1 = '( -u K - %s )' % H; L2 = '( %s - K )' % H
    A1 = '( %s /\\ %s e. ZZ )' % (A0, L1)
    t = mkst(w, A1)
    nkz = t([lift(w, kz, A1)], 'znegcld', '-u K e. ZZ')
    d = t([nkz, w.s([], 'simpr', '( %s -> %s e. ZZ )' % (A1, L1)), w.inst('zsubcl')], 'syl2anc', '( -u K - %s ) e. ZZ' % L1)
    kc = t([lift(w, kz, A1)], 'zcnd', 'K e. CC')
    e = t([t([kc], 'negcld', '-u K e. CC'), c1(w, A1, 'halfcn', '%s e. CC' % H)], 'nncand', '( -u K - %s ) = %s' % (L1, H))
    hz = t([e, d], 'eqeltrrd', '%s e. ZZ' % H)
    n1 = w.s([hz, c1(w, A1, 'halfnz', '-. %s e. ZZ' % H)], 'pm2.65da', '( %s -> -. %s e. ZZ )' % (A0, L1))
    A2 = '( %s /\\ %s e. ZZ )' % (A0, L2)
    t = mkst(w, A2)
    d2 = t([w.s([], 'simpr', '( %s -> %s e. ZZ )' % (A2, L2)), lift(w, kz, A2), w.inst('zaddcl')], 'syl2anc', '( %s + K ) e. ZZ' % L2)
    e2 = t([c1(w, A2, 'halfcn', '%s e. CC' % H), t([lift(w, kz, A2)], 'zcnd', 'K e. CC')], 'npcand', '( %s + K ) = %s' % (L2, H))
    hz2 = t([e2, d2], 'eqeltrrd', '%s e. ZZ' % H)
    n2 = w.s([hz2, c1(w, A2, 'halfnz', '-. %s e. ZZ' % H)], 'pm2.65da', '( %s -> -. %s e. ZZ )' % (A0, L2))
    w.qed([n1, n2], 'jca', STATEMENTS['z6mnhz'])
    return w


# ---------------------------------------------------------------- z6mre1
def z6mre1():
    w = W('z6mre1', 'The real and imaginary parts of ` W + 1 ` .')
    A0 = 'W e. CC'
    s = mkst(w, A0)
    wc = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    one = c1(w, A0, 'ax-1cn', '1 e. CC')
    r = s([s([wc, one], 'readdd', '( Re ` ( W + 1 ) ) = ( ( Re ` W ) + ( Re ` 1 ) )'), s([c1(w, A0, 're1', '( Re ` 1 ) = 1')], 'oveq2d', '( ( Re ` W ) + ( Re ` 1 ) ) = ( ( Re ` W ) + 1 )')],
          'eqtrd', '( Re ` ( W + 1 ) ) = ( ( Re ` W ) + 1 )')
    i = s([s([s([wc, one], 'imaddd', '( Im ` ( W + 1 ) ) = ( ( Im ` W ) + ( Im ` 1 ) )'), s([c1(w, A0, 'im1', '( Im ` 1 ) = 0')], 'oveq2d', '( ( Im ` W ) + ( Im ` 1 ) ) = ( ( Im ` W ) + 0 )')],
            'eqtrd', '( Im ` ( W + 1 ) ) = ( ( Im ` W ) + 0 )'), s([s([s([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')], 'addridd', '( ( Im ` W ) + 0 ) = ( Im ` W )')],
          'eqtrd', '( Im ` ( W + 1 ) ) = ( Im ` W )')
    w.qed([r, i], 'jca', STATEMENTS['z6mre1'])
    return w


def e4cong(w, A, eq, X, Y):
    """( A -> ( ; 6 4 x. E4(X) ) = ( ; 6 4 x. E4(Y) ) ) from eq: ( A -> X = Y )"""
    s = mkst(w, A)
    a = s([eq], 'oveq1d', '( %s / 4 ) = ( %s / 4 )' % (X, Y))
    b = s([a], 'negeqd', '-u ( %s / 4 ) = -u ( %s / 4 )' % (X, Y))
    c = s([b], 'oveq2d', '%s = %s' % (E4(X), E4(Y)))
    return s([c], 'oveq2d', '( ; 6 4 x. %s ) = ( ; 6 4 x. %s )' % (E4(X), E4(Y)))


# ---------------------------------------------------------------- z6mgup
def z6mgup():
    w = W('z6mgup', 'The strip bound ` 64 2 ^ ( - | Im | / 4 ) ` passes from ` W + 1 ` to ` W ` when ` | Im W | >_ 1 ` '
          '( ~ z6mgdiv at ` R = 1 ` ; ` | W | >_ | Im W | >_ 1 ` ).')
    A0 = split_imp(STATEMENTS['z6mgup'])[0]
    s = mkst(w, A0)
    AI = '( abs ` ( Im ` W ) )'; AI1 = '( abs ` ( Im ` ( W + 1 ) ) )'
    wc = w.s([], 'simp1', '( %s -> W e. CC )' % A0)
    ge1 = w.s([], 'simp2', '( %s -> 1 <_ %s )' % (A0, AI))
    hb = w.s([], 'simp3', '( %s -> ( abs ` ( _G ` ( W + 1 ) ) ) <_ ( ; 6 4 x. %s ) )' % (A0, E4(AI1)))
    im = s([s([wc, w.inst('z6mre1')], 'syl', '( ( Re ` ( W + 1 ) ) = ( ( Re ` W ) + 1 ) /\\ ( Im ` ( W + 1 ) ) = ( Im ` W ) )')], 'simprd', '( Im ` ( W + 1 ) ) = ( Im ` W )')
    ee = e4cong(w, A0, s([im], 'fveq2d', '%s = %s' % (AI1, AI)), AI1, AI)
    hb2 = s([hb, ee], 'breqtrd', '( abs ` ( _G ` ( W + 1 ) ) ) <_ ( ; 6 4 x. %s )' % E4(AI))
    imc = s([s([wc], 'imcld', '( Im ` W ) e. RR')], 'recnd', '( Im ` W ) e. CC')
    air = s([imc], 'abscld', '%s e. RR' % AI)
    cl = Closure(w, A0, {})
    cl.leaf(AI, 'RR', air)
    gt = linarith(w, A0, [ge1], '0 < %s' % AI, closure=cl)
    ine = s([gt, s([imc, w.inst('absgt0')], 'syl', '( ( Im ` W ) =/= 0 <-> 0 < %s )' % AI)], 'mpbird', '( Im ` W ) =/= 0')
    DJ = '( -. ( Re ` W ) e. ZZ \\/ ( Im ` W ) =/= 0 )'
    wd = s([wc, s([ine], 'olcd', DJ), w.inst('z6mndg')], 'syl2anc', 'W e. %s' % DG)
    awr = s([wc], 'abscld', '( abs ` W ) e. RR')
    w1 = s([cl.mem('1', 'RR'), air, awr, ge1, s([wc, w.inst('absimle')], 'syl', '%s <_ ( abs ` W )' % AI)], 'letrd', '1 <_ ( abs ` W )')
    gd = s([wd, s([cl.mem('1', 'RR+'), w1], 'jca', '( 1 e. RR+ /\\ 1 <_ ( abs ` W ) )'), w.inst('z6mgdiv')], 'syl2anc',
           '( abs ` ( _G ` W ) ) <_ ( ( abs ` ( _G ` ( W + 1 ) ) ) / 1 )')
    w1d = s([wd, c1(w, A0, '1nn0', '1 e. NN0')], 'dmgmaddnn0', '( W + 1 ) e. %s' % DG)
    g1c = s([s([w1d, w.inst('gamcl')], 'syl', '( _G ` ( W + 1 ) ) e. CC')], 'abscld', '( abs ` ( _G ` ( W + 1 ) ) ) e. RR')
    gd2 = s([gd, s([s([g1c], 'recnd', '( abs ` ( _G ` ( W + 1 ) ) ) e. CC')], 'div1d', '( ( abs ` ( _G ` ( W + 1 ) ) ) / 1 ) = ( abs ` ( _G ` ( W + 1 ) ) )')], 'breqtrd',
            '( abs ` ( _G ` W ) ) <_ ( abs ` ( _G ` ( W + 1 ) ) )')
    gwr = s([s([wd, w.inst('gamcl')], 'syl', '( _G ` W ) e. CC')], 'abscld', '( abs ` ( _G ` W ) ) e. RR')
    w.qed([gwr, g1c, cl.mem('( ; 6 4 x. %s )' % E4(AI), 'RR'), gd2, hb2], 'letrd', STATEMENTS['z6mgup'])
    return w


# ---------------------------------------------------------------- z6mgstr
def z6mgstr():
    w = W('z6mgstr', 'The Gamma strip bound on ` -u K - 1 / 2 <_ Re W <_ 1 / 2 - K ` , ` | Im W | >_ 1 ` : induction on ` K ` '
          '( ~ z6mg64 on ` [ 1 / 2 , 3 / 2 ] ` , ~ z6mgup ).')
    H = '( 1 / 2 )'
    AIv = lambda v: '( abs ` ( Im ` %s ) )' % v
    COND = lambda v, n: '( ( ( -u %s - %s ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( %s - %s ) ) /\\ 1 <_ %s )' % (n, H, v, v, H, n, AIv(v))
    BD = lambda v: '( abs ` ( _G ` %s ) ) <_ ( ; 6 4 x. %s )' % (v, E4(AIv(v)))
    BODY = lambda v, n: '( %s -> %s )' % (COND(v, n), BD(v))
    P = lambda n, v='x': 'A. %s e. CC %s' % (v, BODY(v, n))

    def sb(T):
        idk = w.s([], 'id', '( n = %s -> n = %s )' % (T, T))
        stp, new = w.wcongr(P('n'), {'n': T}, 'n = %s' % T, {'n': idk})
        assert new == P(T), new
        return stp
    h1 = sb('0'); h2 = sb('m'); h3 = sb('( m + 1 )'); h4 = sb('K')

    def re1(A, xc):
        s = mkst(w, A)
        r = s([xc, w.inst('z6mre1')], 'syl', '( ( Re ` ( x + 1 ) ) = ( ( Re ` x ) + 1 ) /\\ ( Im ` ( x + 1 ) ) = ( Im ` x ) )')
        return s([r], 'simpld', '( Re ` ( x + 1 ) ) = ( ( Re ` x ) + 1 )'), s([r], 'simprd', '( Im ` ( x + 1 ) ) = ( Im ` x )')
    # base
    Ax = '( x e. CC /\\ %s )' % COND('x', '0')
    s = mkst(w, Ax)
    xc = w.s([], 'simpl', '( %s -> x e. CC )' % Ax)
    lo = w.s([], 'simprll', '( %s -> ( -u 0 - %s ) <_ ( Re ` x ) )' % (Ax, H))
    hi = w.s([], 'simprlr', '( %s -> ( Re ` x ) <_ ( %s - 0 ) )' % (Ax, H))
    ge = w.s([], 'simprr', '( %s -> 1 <_ %s )' % (Ax, AIv('x')))
    r1, i1 = re1(Ax, xc)
    rx = s([xc], 'recld', '( Re ` x ) e. RR')
    clb = Closure(w, Ax, {'( Re ` x )': ('RR', rx)})
    lo = s([a1(w, Ax, negh(w), '( -u 0 - %s ) = -u %s' % (H, H)), lo], 'eqbrtrrd', '-u %s <_ ( Re ` x )' % H)
    l1 = s([linarith(w, Ax, [lo], '%s <_ ( ( Re ` x ) + 1 )' % H, closure=clb), r1], 'breqtrrd', '%s <_ ( Re ` ( x + 1 ) )' % H)
    u1 = s([r1, linarith(w, Ax, [hi], '( ( Re ` x ) + 1 ) <_ 3', closure=clb)], 'eqbrtrd', '( Re ` ( x + 1 ) ) <_ 3')
    x1c = s([xc, c1(w, Ax, 'ax-1cn', '1 e. CC')], 'addcld', '( x + 1 ) e. CC')
    g64 = s([s([x1c, s([l1, u1], 'jca', '( %s <_ ( Re ` ( x + 1 ) ) /\\ ( Re ` ( x + 1 ) ) <_ 3 )' % H)], 'jca',
               '( ( x + 1 ) e. CC /\\ ( %s <_ ( Re ` ( x + 1 ) ) /\\ ( Re ` ( x + 1 ) ) <_ 3 ) )' % H), w.inst('z6mg64')], 'syl', BD('( x + 1 )'))
    b0 = s([xc, ge, g64, w.inst('z6mgup')], 'syl3anc', BD('x'))
    base = w.s([w.s([b0], 'ex', '( x e. CC -> %s )' % BODY('x', '0'))], 'rgen', P('0'))
    # step: the hypothesis with its bound variable renamed to y
    idk = w.s([], 'id', '( x = y -> x = y )')
    sbx, by = w.wcongr(BODY('x', 'm'), {'x': 'y'}, 'x = y', {'x': idk})
    cbv = w.s([sbx], 'cbvralvw', '( %s <-> %s )' % (P('m'), P('m', 'y')))
    A = '( m e. NN0 /\\ %s )' % P('m', 'y')
    Ax = '( ( %s /\\ x e. CC ) /\\ %s )' % (A, COND('x', '( m + 1 )'))
    s = mkst(w, Ax)
    xc = w.s([], 'simplr', '( %s -> x e. CC )' % Ax)
    mr = s([w.s([], 'simplll', '( %s -> m e. NN0 )' % Ax)], 'nn0red', 'm e. RR')
    hyp_ = w.s([], 'simpllr', '( %s -> %s )' % (Ax, P('m', 'y')))
    lo = w.s([], 'simprll', '( %s -> ( -u ( m + 1 ) - %s ) <_ ( Re ` x ) )' % (Ax, H))
    hi = w.s([], 'simprlr', '( %s -> ( Re ` x ) <_ ( %s - ( m + 1 ) ) )' % (Ax, H))
    ge = w.s([], 'simprr', '( %s -> 1 <_ %s )' % (Ax, AIv('x')))
    r1, i1 = re1(Ax, xc)
    rx = s([xc], 'recld', '( Re ` x ) e. RR')
    lv = {'( Re ` x )': rx, 'm': mr}
    l1 = s([linarith(w, Ax, [lo], '( -u m - %s ) <_ ( ( Re ` x ) + 1 )' % H, leaves=lv), r1], 'breqtrrd', '( -u m - %s ) <_ ( Re ` ( x + 1 ) )' % H)
    u1 = s([r1, linarith(w, Ax, [hi], '( ( Re ` x ) + 1 ) <_ ( %s - m )' % H, leaves=lv)], 'eqbrtrd', '( Re ` ( x + 1 ) ) <_ ( %s - m )' % H)
    g1 = s([ge, s([s([i1], 'fveq2d', '%s = %s' % (AIv('( x + 1 )'), AIv('x')))], 'eqcomd', '%s = %s' % (AIv('x'), AIv('( x + 1 )')))], 'breqtrd', '1 <_ %s' % AIv('( x + 1 )'))
    cnd = s([s([l1, u1], 'jca', '( ( -u m - %s ) <_ ( Re ` ( x + 1 ) ) /\\ ( Re ` ( x + 1 ) ) <_ ( %s - m ) )' % (H, H)), g1], 'jca', COND('( x + 1 )', 'm'))
    x1c = s([xc, c1(w, Ax, 'ax-1cn', '1 e. CC')], 'addcld', '( x + 1 ) e. CC')
    idk2 = w.s([], 'id', '( y = ( x + 1 ) -> y = ( x + 1 ) )')
    sby, bx1 = w.wcongr(BODY('y', 'm'), {'y': '( x + 1 )'}, 'y = ( x + 1 )', {'y': idk2})
    assert bx1 == BODY('( x + 1 )', 'm'), bx1
    rs = w.s([sby], 'rspcv', '( ( x + 1 ) e. CC -> ( %s -> %s ) )' % (P('m', 'y'), bx1))
    ih = s([cnd, s([x1c, hyp_, rs], 'sylc', bx1)], 'mpd', BD('( x + 1 )'))
    b1 = s([xc, ge, ih, w.inst('z6mgup')], 'syl3anc', BD('x'))
    e1 = w.s([b1], 'ex', '( ( %s /\\ x e. CC ) -> %s )' % (A, BODY('x', '( m + 1 )')))
    ra = w.s([e1], 'ralrimiva', '( %s -> %s )' % (A, P('( m + 1 )')))
    e2 = w.s([ra], 'ex', '( m e. NN0 -> ( %s -> %s ) )' % (P('m', 'y'), P('( m + 1 )')))
    e3 = w.s([cbv, e2], 'biimtrid', '( m e. NN0 -> ( %s -> %s ) )' % (P('m'), P('( m + 1 )')))
    ind = w.s([h1, h2, h3, h4, base, e3], 'nn0ind', '( K e. NN0 -> %s )' % P('K'))
    # conclusion
    A0 = split_imp(STATEMENTS['z6mgstr'])[0]
    s = mkst(w, A0)
    pk = s([w.s([], 'simpl', '( %s -> K e. NN0 )' % A0), ind], 'syl', P('K'))
    wc = w.s([], 'simprl', '( %s -> W e. CC )' % A0)
    cw = w.s([], 'simprr', '( %s -> %s )' % (A0, COND('W', 'K')))
    idk3 = w.s([], 'id', '( x = W -> x = W )')
    sbw, bw = w.wcongr(BODY('x', 'K'), {'x': 'W'}, 'x = W', {'x': idk3})
    rs = w.s([sbw], 'rspcv', '( W e. CC -> ( %s -> %s ) )' % (P('K'), bw))
    w.qed([cw, s([wc, pk, rs], 'sylc', bw)], 'mpd', STATEMENTS['z6mgstr'])
    return w


# ---------------------------------------------------------------- z6mgln
def z6mgln():
    w = W('z6mgln', 'Gamma on the line ` Re w = -u K - 1 / 2 ` against Gamma on ` Re w = 1 / 2 ` : '
          '` | _G ( -u K - 1 / 2 + i U ) | <_ ( 2 / K ! ) | _G ( 1 / 2 + i U ) | ` , induction on ` K ` ( ~ z6mgdiv ; ` | w | >_ | Re w | = K + 1 / 2 ` ).')
    H = '( 1 / 2 )'
    IU = '( _i x. U )'
    LWn = lambda n: '( ( -u %s - %s ) + %s )' % (n, H, IU)
    HL = '( %s + %s )' % (H, IU)
    g = '( abs ` ( _G ` %s ) )' % HL
    BD = lambda n: '( abs ` ( _G ` %s ) ) <_ ( ( 2 / ( ! ` %s ) ) x. %s )' % (LWn(n), n, g)
    P = lambda n: '( U e. RR -> %s )' % BD(n)

    def sb(T):
        idk = w.s([], 'id', '( n = %s -> n = %s )' % (T, T))
        stp, new = w.wcongr(P('n'), {'n': T}, 'n = %s' % T, {'n': idk})
        assert new == P(T), new
        return stp
    h1 = sb('0'); h2 = sb('m'); h3 = sb('( m + 1 )'); h4 = sb('K')

    def ldiv(A, n, nn0, R, rrp, leaves, target, tgt_re):
        """( A -> |G(LW n)| <_ ( |G(target)| / R ) ); target = ( tgt_re + iU ) = LW n + 1"""
        s = mkst(w, A)
        ur = w.s([], 'id', '( U e. RR -> U e. RR )') if A == 'U e. RR' else w.s([], 'simpr', '( %s -> U e. RR )' % A)
        L = '( -u %s - %s )' % (n, H)
        lv = dict(leaves); lv['U'] = ('RR', ur)
        cl = Closure(w, A, lv)
        lr = cl.mem(L, 'RR') if n != '0' else s([a1(w, A, negh(w), '%s = -u %s' % (L, H)), s([c1(w, A, 'halfre', '%s e. RR' % H)], 'renegcld', '-u %s e. RR' % H)], 'eqeltrd', '%s e. RR' % L)
        Lp = L if n != '0' else '-u %s' % H
        eqL = a1(w, A, negh(w), '%s = %s' % (L, Lp)) if n == '0' else None
        iuc = s([c1(w, A, 'ax-icn', '_i e. CC'), s([ur], 'recnd', 'U e. CC')], 'mulcld', '%s e. CC' % IU)
        lwc = s([s([lr], 'recnd', '%s e. CC' % L), iuc], 'addcld', '%s e. CC' % LWn(n))
        re = s([lr, ur], 'crred', '( Re ` %s ) = %s' % (LWn(n), L))
        nz = s([s([nn0, w.inst('z6mnhz')], 'syl', '( -. %s e. ZZ /\\ -. ( %s - %s ) e. ZZ )' % (L, H, n))], 'simpld', '-. %s e. ZZ' % L)
        nre = s([nz, s([re], 'eleq1d', '( ( Re ` %s ) e. ZZ <-> %s e. ZZ )' % (LWn(n), L))], 'mtbird', '-. ( Re ` %s ) e. ZZ' % LWn(n))
        DJ = '( -. ( Re ` %s ) e. ZZ \\/ ( Im ` %s ) =/= 0 )' % (LWn(n), LWn(n))
        dg = s([lwc, s([nre], 'orcd', DJ), w.inst('z6mndg')], 'syl2anc', '%s e. %s' % (LWn(n), DG))
        n0 = s([nn0], 'nn0ge0d', '0 <_ %s' % n)
        llep = linarith(w, A, [n0], '%s <_ 0' % Lp, closure=cl)
        lle = llep if n != '0' else s([eqL, llep], 'eqbrtrd', '%s <_ 0' % L)
        ab = s([lr, lle, w.inst('absnid')], 'syl2anc', '( abs ` %s ) = -u %s' % (L, L))
        ar = s([s([re], 'fveq2d', '( abs ` ( Re ` %s ) ) = ( abs ` %s )' % (LWn(n), L)), ab], 'eqtrd', '( abs ` ( Re ` %s ) ) = -u %s' % (LWn(n), L))
        rle = s([lwc, w.inst('absrele')], 'syl', '( abs ` ( Re ` %s ) ) <_ ( abs ` %s )' % (LWn(n), LWn(n)))
        rle2 = s([ar, rle], 'eqbrtrrd', '-u %s <_ ( abs ` %s )' % (L, LWn(n)))
        if n == '0':
            rle2 = s([s([eqL], 'negeqd', '-u %s = -u %s' % (L, Lp)), rle2], 'eqbrtrrd', '-u %s <_ ( abs ` %s )' % (Lp, LWn(n)))
            nn_ = a1(w, A, w.s([w.s([], 'halfcn', '%s e. CC' % H)], 'negnegi', '-u -u %s = %s' % (H, H)), '-u -u %s = %s' % (H, H))
            rle2 = s([nn_, rle2], 'eqbrtrrd', '%s <_ ( abs ` %s )' % (H, LWn(n)))
        AW = '( abs ` %s )' % LWn(n)
        cl.leaf(AW, 'RR', s([lwc], 'abscld', '%s e. RR' % AW))
        rw = linarith(w, A, [rle2], '%s <_ %s' % (R, AW), closure=cl) if n != '0' else rle2
        gd = s([dg, s([rrp, rw], 'jca', '( %s e. RR+ /\\ %s <_ %s )' % (R, R, AW)), w.inst('z6mgdiv')], 'syl2anc',
               '( abs ` ( _G ` %s ) ) <_ ( ( abs ` ( _G ` ( %s + 1 ) ) ) / %s )' % (LWn(n), LWn(n), R))
        a32 = s([s([lr], 'recnd', '%s e. CC' % L), iuc, c1(w, A, 'ax-1cn', '1 e. CC')], 'add32d', '( %s + 1 ) = ( ( %s + 1 ) + %s )' % (LWn(n), L, IU))
        l1 = lineq(w, A, '( %s + 1 )' % Lp, tgt_re, closure=cl)
        if n == '0':
            l1 = s([s([eqL], 'oveq1d', '( %s + 1 ) = ( %s + 1 )' % (L, Lp)), l1], 'eqtrd', '( %s + 1 ) = %s' % (L, tgt_re))
        tq = s([a32, s([l1], 'oveq1d', '( ( %s + 1 ) + %s ) = %s' % (L, IU, target))], 'eqtrd', '( %s + 1 ) = %s' % (LWn(n), target))
        q = s([s([s([tq], 'fveq2d', '( _G ` ( %s + 1 ) ) = ( _G ` %s )' % (LWn(n), target))], 'fveq2d',
                 '( abs ` ( _G ` ( %s + 1 ) ) ) = ( abs ` ( _G ` %s ) )' % (LWn(n), target))], 'oveq1d',
              '( ( abs ` ( _G ` ( %s + 1 ) ) ) / %s ) = ( ( abs ` ( _G ` %s ) ) / %s )' % (LWn(n), R, target, R))
        agr = s([s([dg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % LWn(n))], 'abscld', '( abs ` ( _G ` %s ) ) e. RR' % LWn(n))
        return s([gd, q], 'breqtrd', '( abs ` ( _G ` %s ) ) <_ ( ( abs ` ( _G ` %s ) ) / %s )' % (LWn(n), target, R)), cl, ur, agr

    def gre(A, ur):
        """( A -> g e. RR )"""
        s = mkst(w, A)
        hr = c1(w, A, 'halfre', '%s e. RR' % H)
        iuc = s([c1(w, A, 'ax-icn', '_i e. CC'), s([ur], 'recnd', 'U e. CC')], 'mulcld', '%s e. CC' % IU)
        hc = s([c1(w, A, 'halfcn', '%s e. CC' % H), iuc], 'addcld', '%s e. CC' % HL)
        rh = s([hr, ur], 'crred', '( Re ` %s ) = %s' % (HL, H))
        hdg = s([hc, s([c1(w, A, 'halfgt0', '0 < %s' % H), rh], 'breqtrrd', '0 < ( Re ` %s )' % HL), w.inst('zrenn')], 'syl2anc', '%s e. %s' % (HL, DG))
        return s([s([hdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % HL)], 'abscld', '%s e. RR' % g)
    # base
    A0 = 'U e. RR'
    s = mkst(w, A0)
    n0 = c1(w, A0, '0nn0', '0 e. NN0')
    hrp = s([c1(w, A0, 'halfre', '%s e. RR' % H), c1(w, A0, 'halfgt0', '0 < %s' % H)], 'elrpd', '%s e. RR+' % H)
    b, cl, ur, agr = ldiv(A0, '0', n0, H, hrp, {'0': ('RR', c1(w, A0, '0re', '0 e. RR'))}, HL, H)
    cl.leaf(g, 'RR', gre(A0, ur))
    AG0 = '( abs ` ( _G ` %s ) )' % LWn('0')
    cl.leaf(AG0, 'RR', agr)
    gc0 = s([cl.mem(g, 'RR')], 'recnd', '%s e. CC' % g)
    hc0 = c1(w, A0, 'halfcn', '%s e. CC' % H)
    d1 = s([gc0, hc0, s([s([c1(w, A0, 'halfre', '%s e. RR' % H), c1(w, A0, 'halfgt0', '0 < %s' % H)], 'elrpd', '%s e. RR+' % H)], 'rpne0d', '%s =/= 0' % H)],
           'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (g, H, g, H))
    d2 = s([c1(w, A0, '2cn', '2 e. CC'), c1(w, A0, '2ne0', '2 =/= 0'), w.inst('recrec')], 'syl2anc', '( 1 / %s ) = 2' % H)
    d3 = s([s([d1, s([d2], 'oveq2d', '( %s x. ( 1 / %s ) ) = ( %s x. 2 )' % (g, H, g))], 'eqtrd', '( %s / %s ) = ( %s x. 2 )' % (g, H, g)),
            s([gc0, c1(w, A0, '2cn', '2 e. CC')], 'mulcomd', '( %s x. 2 ) = ( 2 x. %s )' % (g, g))], 'eqtrd', '( %s / %s ) = ( 2 x. %s )' % (g, H, g))
    b2 = s([b, d3], 'breqtrd', '%s <_ ( 2 x. %s )' % (AG0, g))
    f0 = w.s([w.s([w.s([], 'fac0', '( ! ` 0 ) = 1')], 'oveq2i', '( 2 / ( ! ` 0 ) ) = ( 2 / 1 )'), w.s([w.s([], '2cn', '2 e. CC')], 'div1i', '( 2 / 1 ) = 2')], 'eqtri',
             '( 2 / ( ! ` 0 ) ) = 2')
    f1 = w.s([f0], 'oveq1i', '( ( 2 / ( ! ` 0 ) ) x. %s ) = ( 2 x. %s )' % (g, g))
    base = s([b2, a1(w, A0, f1, '( ( 2 / ( ! ` 0 ) ) x. %s ) = ( 2 x. %s )' % (g, g))], 'breqtrrd', BD('0'))
    # step
    A = '( ( m e. NN0 /\\ %s ) /\\ U e. RR )' % P('m')
    s = mkst(w, A)
    mn = w.s([], 'simpll', '( %s -> m e. NN0 )' % A)
    ur = w.s([], 'simpr', '( %s -> U e. RR )' % A)
    ih = s([ur, w.s([], 'simplr', '( %s -> %s )' % (A, P('m')))], 'mpd', BD('m'))
    mr = s([mn], 'nn0red', 'm e. RR')
    M1 = '( m + 1 )'
    m1n = s([mn, w.inst('peano2nn0')], 'syl', '%s e. NN0' % M1)
    m1rp = s([s([mn, w.inst('nn0p1nn')], 'syl', '%s e. NN' % M1)], 'nnrpd', '%s e. RR+' % M1)
    b, cl, ur2, agr = ldiv(A, M1, m1n, M1, m1rp, {'m': ('RR', mr), M1: ('RR', s([m1rp], 'rpred', '%s e. RR' % M1))}, LWn('m'), '( -u m - %s )' % H)
    AGm = '( abs ` ( _G ` %s ) )' % LWn('m')
    F = '( ! ` m )'
    fn = s([mn, w.inst('faccl')], 'syl', '%s e. NN' % F)
    cl.leaf(F, 'NN', fn)
    gr = gre(A, ur)
    cl.leaf(g, 'RR', gr)
    agmr = s([s([ih, w.inst('z6absle')], 'syl', '( _G ` %s ) e. CC' % LWn('m'))], 'abscld', '%s e. RR' % AGm)
    Bm = '( ( 2 / %s ) x. %s )' % (F, g)
    bmr = cl.mem(Bm, 'RR')
    d1 = s([agmr, bmr, m1rp, ih], 'lediv1dd', '( %s / %s ) <_ ( %s / %s )' % (AGm, M1, Bm, M1))
    AG1 = '( abs ` ( _G ` %s ) )' % LWn(M1)
    t1 = s([agr, s([agmr, m1rp], 'rerpdivcld', '( %s / %s ) e. RR' % (AGm, M1)), s([bmr, m1rp], 'rerpdivcld', '( %s / %s ) e. RR' % (Bm, M1)), b, d1], 'letrd',
           '%s <_ ( %s / %s )' % (AG1, Bm, M1))
    fc = s([fn], 'nncnd', '%s e. CC' % F); fne = s([fn], 'nnne0d', '%s =/= 0' % F)
    m1c = s([m1rp], 'rpcnd', '%s e. CC' % M1); m1ne = s([m1rp], 'rpne0d', '%s =/= 0' % M1)
    tf = s([c1(w, A, '2cn', '2 e. CC'), fc, fne], 'divcld', '( 2 / %s ) e. CC' % F)
    gc = s([gr], 'recnd', '%s e. CC' % g)
    e1 = s([tf, gc, m1c, m1ne], 'div23d', '( %s / %s ) = ( ( ( 2 / %s ) / %s ) x. %s )' % (Bm, M1, F, M1, g))
    e2 = s([c1(w, A, '2cn', '2 e. CC'), fc, m1c, fne, m1ne], 'divdiv1d', '( ( 2 / %s ) / %s ) = ( 2 / ( %s x. %s ) )' % (F, M1, F, M1))
    e3 = s([s([mn, w.inst('facp1')], 'syl', '( ! ` %s ) = ( %s x. %s )' % (M1, F, M1))], 'oveq2d', '( 2 / ( ! ` %s ) ) = ( 2 / ( %s x. %s ) )' % (M1, F, M1))
    e4 = s([e2, e3], 'eqtr4d', '( ( 2 / %s ) / %s ) = ( 2 / ( ! ` %s ) )' % (F, M1, M1))
    e5 = s([e1, s([e4], 'oveq1d', '( ( ( 2 / %s ) / %s ) x. %s ) = ( ( 2 / ( ! ` %s ) ) x. %s )' % (F, M1, g, M1, g))], 'eqtrd',
           '( %s / %s ) = ( ( 2 / ( ! ` %s ) ) x. %s )' % (Bm, M1, M1, g))
    stp = s([t1, e5], 'breqtrd', BD(M1))
    e6 = w.s([stp], 'ex', '( ( m e. NN0 /\\ %s ) -> %s )' % (P('m'), P(M1)))
    e7 = w.s([e6], 'ex', '( m e. NN0 -> ( %s -> %s ) )' % (P('m'), P(M1)))
    ind = w.s([h1, h2, h3, h4, base, e7], 'nn0ind', '( K e. NN0 -> %s )' % P('K'))
    w.qed([ind], 'imp', STATEMENTS['z6mgln'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for f in [z6mycx, z6mg64, z6mgdiv, z6mndg, z6mnhz, z6mre1, z6mgup, z6mgstr, z6mgln]:
        if want(f.__name__):
            if run(f()):
                status(f.__name__)
            else:
                break
