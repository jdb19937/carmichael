"""Sortie C8, section 5: the log-derivative bound (holsubc, logdvbc,
logdvlip, logdvbnd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
from cl import lift
import num
import lin
import cl
from c8_freeze import S as FS

R51 = '( ; 5 1 / ; 3 2 )'
R49 = '( ; 4 9 / ; 3 2 )'
R64 = '( 1 / ; 6 4 )'
K6 = '( ; ; ; 6 2 7 2 x. M )'
HG = '( G e. ( E -cn-> CC ) /\\ E C_ dom ( CC _D G ) )'
REY = 'A. y e. E ( Re ` ( ( G ` y ) - ( G ` C ) ) ) <_ M'


def PHI(K):
    return '( z e. E |-> ( ( G ` z ) - %s ) )' % K


def numst(w, ante, text, kind):
    """( ante -> text <kind> ) for a literal: kind RR, RR+, gt0, ge0, CC"""
    c = num.fact(w, text, kind)
    f = {'gt0': '0 < %s', 'ge0': '0 <_ %s'}.get(kind, '%s e. ' + kind) % text
    return w.s([c], 'a1i', '( %s -> %s )' % (ante, f))


def gen_holsubc():
    w = W('holsubc', 'A holomorphic function minus a constant is holomorphic.')
    A0 = '( %s /\\ K e. CC )' % HG
    Az = '( %s /\\ z e. E )' % A0
    hg = w.s([], 'simpl', '( %s -> %s )' % (A0, HG))
    kc = w.s([], 'simpr', '( %s -> K e. CC )' % A0)
    gcn = w.s([hg, w.inst('simpl')], 'syl', '( %s -> G e. ( E -cn-> CC ) )' % A0)
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : E --> CC )' % A0)
    ecc = w.s([gcn, w.inst('cncfrss')], 'syl', '( %s -> E C_ CC )' % A0)
    eop = w.s([hg, w.inst('holopn')], 'syl', '( %s -> E e. %s )' % (A0, TOP))
    gm = w.s([gf], 'feqmptd', '( %s -> G = ( z e. E |-> ( G ` z ) ) )' % A0)
    gmc = w.s([gm, gcn], 'eqeltrrd', '( %s -> ( z e. E |-> ( G ` z ) ) e. ( E -cn-> CC ) )' % A0)
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    scn = closed(w, A0, 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP)) if False else w.s([w.s([ej], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
    ccs = closed(w, A0, 'ssid', 'CC C_ CC')
    kcn = w.s([kc, ecc, ccs, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. E |-> K ) e. ( E -cn-> CC ) )' % A0)
    pcn = w.s([ej, scn, gmc, kcn], 'cncfmpt2f', '( %s -> %s e. ( E -cn-> CC ) )' % (A0, PHI('K')))
    ce = closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    hdv = w.s([hg, w.inst('holdv')], 'syl', '( %s -> ( CC _D ( z e. E |-> ( G ` z ) ) ) = ( z e. E |-> ( ( CC _D G ) ` z ) ) )' % A0)
    dvf = w.s([hg, w.inst('holf')], 'syl', '( %s -> ( CC _D G ) : E --> CC )' % A0)
    zE = w.s([], 'simpr', '( %s -> z e. E )' % Az)
    gzc = w.s([lift(w, gf, Az), zE], 'ffvelcdmd', '( %s -> ( G ` z ) e. CC )' % Az)
    dgz = w.s([lift(w, dvf, Az), zE], 'ffvelcdmd', '( %s -> ( ( CC _D G ) ` z ) e. CC )' % Az)
    Ac = '( %s /\\ z e. CC )' % A0
    dvc0 = w.s([ce, kc, w.inst('dvmptc')], 'syl2anc', '( %s -> ( CC _D ( z e. CC |-> K ) ) = ( z e. CC |-> 0 ) )' % A0)
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    dvc = w.s([ce, lift(w, kc, Ac), w.s([], '0cnd', '( %s -> 0 e. CC )' % Ac), dvc0, ecc, jr, ej, eop], 'dvmptres', '( %s -> ( CC _D ( z e. E |-> K ) ) = ( z e. E |-> 0 ) )' % A0)
    RHS = '( ( ( CC _D G ) ` z ) - 0 )'
    dvp = w.s([ce, gzc, dgz, hdv, lift(w, kc, Az), w.s([], '0cnd', '( %s -> 0 e. CC )' % Az), dvc], 'dvmptsub', '( %s -> ( CC _D %s ) = ( z e. E |-> %s ) )' % (A0, PHI('K'), RHS))
    rc = w.s([dgz, w.s([], '0cnd', '( %s -> 0 e. CC )' % Az)], 'subcld', '( %s -> %s e. CC )' % (Az, RHS))
    dm = dvdom(w, A0, PHI('K'), 'z', 'E', RHS, dvp, rc)
    w.qed([pcn, dm], 'jca', '( %s -> %s )' % (A0, HOLG(PHI('K'), 'E')))
    return run8(w)


def sqint_at(w, ante, cst, rst, ust, ltst, c, r, U):
    """( ante -> INTG(SQA(c,r), SQB(c,r), U) ) from c e. CC, r e. RR, U e. CC, abs ( U - c ) < r"""
    f = '( ( %s e. CC /\\ %s e. RR ) /\\ ( %s e. CC /\\ ( abs ` ( %s - %s ) ) < %s ) )' % (c, r, U, U, c, r)
    j = w.s([w.s([cst, rst], 'jca', '( %s -> ( %s e. CC /\\ %s e. RR ) )' % (ante, c, r)), w.s([ust, ltst], 'jca', '( %s -> ( %s e. CC /\\ ( abs ` ( %s - %s ) ) < %s ) )' % (ante, U, U, c, r))],
            'jca', '( %s -> %s )' % (ante, f))
    return w.s([j, w.inst('sqint')], 'syl', '( %s -> %s )' % (ante, INTG(SQA(c, r), SQB(c, r), U)))


def abs0st(w, ante, cst, c):
    """( ante -> ( abs ` ( c - c ) ) = 0 )"""
    return w.s([w.s([w.s([cst], 'subidd', '( %s -> ( %s - %s ) = 0 )' % (ante, c, c))], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` 0 ) )' % (ante, c, c)),
                closed(w, ante, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( %s -> ( abs ` ( %s - %s ) ) = 0 )' % (ante, c, c))


def center_int(w, ante, cst, rst, rpos, c, r):
    """( ante -> INTG(SQA(c,r), SQB(c,r), c) ) for 0 < r"""
    lt = w.s([abs0st(w, ante, cst, c), rpos], 'eqbrtrd', '( %s -> ( abs ` ( %s - %s ) ) < %s )' % (ante, c, c, r))
    return sqint_at(w, ante, cst, rst, cst, lt, c, r, c)


def gen_logdvbc():
    w = W('logdvbc', 'Borel-Caratheodory for a holomorphic function with real part of its increments from the centre at most ` M ` on an open set containing the square of half-side ` 51 / 32 ` : the increment is at most ` 49 M ` within ` 49 / 32 ` of the centre ( ~ rectintbcx ).')
    C1 = '( %s /\\ ( C e. CC /\\ %s C_ E ) )' % (HG, SQ('C', R51))
    C2 = '( M e. RR+ /\\ %s )' % REY
    C3 = '( U e. CC /\\ ( abs ` ( U - C ) ) <_ %s )' % R49
    A0 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
    GD = '( ( G ` U ) - ( G ` C ) )'
    c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1)); c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2)); c3 = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
    hg = w.s([c1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HG))
    cs = w.s([c1, w.inst('simprl')], 'syl', '( %s -> C e. CC )' % A0)
    ke = w.s([c1, w.inst('simprr')], 'syl', '( %s -> %s C_ E )' % (A0, SQ('C', R51)))
    mrp = w.s([c2, w.inst('simpl')], 'syl', '( %s -> M e. RR+ )' % A0)
    rey = w.s([c2, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, REY))
    us = w.s([c3, w.inst('simpl')], 'syl', '( %s -> U e. CC )' % A0)
    ule = w.s([c3, w.inst('simpr')], 'syl', '( %s -> ( abs ` ( U - C ) ) <_ %s )' % (A0, R49))
    mr = w.s([mrp], 'rpred', '( %s -> M e. RR )' % A0)
    r51 = numst(w, A0, R51, 'RR'); r51p = numst(w, A0, R51, 'gt0')
    a, b = SQA('C', R51), SQB('C', R51)
    auc = w.s([w.s([us, cs], 'subcld', '( %s -> ( U - C ) e. CC )' % A0)], 'abscld', '( %s -> ( abs ` ( U - C ) ) e. RR )' % A0)
    ult = lin8(w, A0, [ule], '( abs ` ( U - C ) ) < %s' % R51, {'( abs ` ( U - C ) )': auc})
    iu = sqint_at(w, A0, cs, r51, us, ult, 'C', R51, 'U')
    ic = center_int(w, A0, cs, r51, r51p, 'C', R51)
    j0 = w.s([cs, r51], 'jca', '( %s -> ( C e. CC /\\ %s e. RR ) )' % (A0, R51))
    rbd = w.s([j0, w.inst('sqrbd')], 'syl', '( %s -> %s )' % (A0, RBDG(a, b, 'C', R51)))
    rc_ = w.s([r51], 'recnd', '( %s -> %s e. CC )' % (A0, R51))
    WW = '( %s + ( _i x. %s ) )' % (R51, R51)
    wc = w.s([rc_, w.s([closed(w, A0, 'ax-icn', '_i e. CC'), rc_], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, R51))], 'addcld', '( %s -> %s e. CC )' % (A0, WW))
    ab = w.s([w.s([cs, wc], 'subcld', '( %s -> %s e. CC )' % (A0, a)), w.s([cs, wc], 'addcld', '( %s -> %s e. CC )' % (A0, b))], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, a, b))
    cK = w.s([ab, ic, w.inst('crectinp')], 'syl2anc', '( %s -> C e. %s )' % (A0, SQ('C', R51)))
    ce = w.s([ke, cK], 'sseldd', '( %s -> C e. E )' % A0)
    gf = w.s([w.s([hg, w.inst('simpl')], 'syl', '( %s -> G e. ( E -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> G : E --> CC )' % A0)
    gc = w.s([gf, ce], 'ffvelcdmd', '( %s -> ( G ` C ) e. CC )' % A0)
    P = PHI('( G ` C )')
    hp = w.s([hg, gc, w.inst('holsubc')], 'syl2anc', '( %s -> %s )' % (A0, HOLG(P, 'E')))
    # Re bound on E
    Av = '( %s /\\ v e. E )' % A0
    ve = w.s([], 'simpr', '( %s -> v e. E )' % Av)
    sub = w.s([w.s([w.s([], 'fveq2', '( z = v -> ( G ` z ) = ( G ` v ) )')], 'oveq1d', '( z = v -> ( ( G ` z ) - ( G ` C ) ) = ( ( G ` v ) - ( G ` C ) ) )')], 'idi',
              '( z = v -> ( ( G ` z ) - ( G ` C ) ) = ( ( G ` v ) - ( G ` C ) ) )')
    pv = mptval(w, Av, 'z', 'E', P, 'v', '( ( G ` v ) - ( G ` C ) )', sub, ve)
    suby = w.s([w.s([w.s([w.s([], 'fveq2', '( y = v -> ( G ` y ) = ( G ` v ) )')], 'oveq1d', '( y = v -> ( ( G ` y ) - ( G ` C ) ) = ( ( G ` v ) - ( G ` C ) ) )')], 'fveq2d',
                    '( y = v -> ( Re ` ( ( G ` y ) - ( G ` C ) ) ) = ( Re ` ( ( G ` v ) - ( G ` C ) ) ) )')], 'breq1d',
               '( y = v -> ( ( Re ` ( ( G ` y ) - ( G ` C ) ) ) <_ M <-> ( Re ` ( ( G ` v ) - ( G ` C ) ) ) <_ M ) )')
    rv = w.s([suby, lift(w, rey, Av), ve], 'rspcdva', '( %s -> ( Re ` ( ( G ` v ) - ( G ` C ) ) ) <_ M )' % Av)
    rpv = w.s([w.s([pv], 'fveq2d', '( %s -> ( Re ` ( %s ` v ) ) = ( Re ` ( ( G ` v ) - ( G ` C ) ) ) )' % (Av, P)), rv], 'eqbrtrd', '( %s -> ( Re ` ( %s ` v ) ) <_ M )' % (Av, P))
    REV = 'A. v e. E ( Re ` ( %s ` v ) ) <_ M' % P
    REP = 'A. y e. E ( Re ` ( %s ` y ) ) <_ M' % P
    cbv = w.s([w.s([w.s([w.s([], 'fveq2', '( v = y -> ( %s ` v ) = ( %s ` y ) )' % (P, P))], 'fveq2d', '( v = y -> ( Re ` ( %s ` v ) ) = ( Re ` ( %s ` y ) ) )' % (P, P))], 'breq1d',
                    '( v = y -> ( ( Re ` ( %s ` v ) ) <_ M <-> ( Re ` ( %s ` y ) ) <_ M ) )' % (P, P))], 'cbvralvw', '( %s <-> %s )' % (REV, REP))
    rep = w.s([w.s([rpv], 'ralrimiva', '( %s -> %s )' % (A0, REV)), cbv], 'sylib', '( %s -> %s )' % (A0, REP))
    subc = w.s([w.s([w.s([], 'fveq2', '( z = C -> ( G ` z ) = ( G ` C ) )')], 'oveq1d', '( z = C -> ( ( G ` z ) - ( G ` C ) ) = ( ( G ` C ) - ( G ` C ) ) )')], 'idi',
               '( z = C -> ( ( G ` z ) - ( G ` C ) ) = ( ( G ` C ) - ( G ` C ) ) )')
    pc0 = w.s([mptval(w, A0, 'z', 'E', P, 'C', '( ( G ` C ) - ( G ` C ) )', subc, ce), w.s([gc], 'subidd', '( %s -> ( ( G ` C ) - ( G ` C ) ) = 0 )' % A0)], 'eqtrd',
              '( %s -> ( %s ` C ) = 0 )' % (A0, P))
    BC = tsub(FS['rectintbcx'], {'F': P, 'D': 'E', 'A': a, 'B': b, 'P': 'C', 'Q': 'U', 'R': R51})
    ba, bcc = ante_of(BC)
    B1 = '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s C_ E ) )' % (a, b, INTG(a, b, 'C'), INTG(a, b, 'U'), HOLG(P, 'E'), SQ('C', R51))
    B2 = '( ( M e. RR /\\ 0 < M /\\ %s ) /\\ ( %s ` C ) = 0 )' % (REP, P)
    B3 = '( ( %s /\\ 0 < %s ) /\\ ( abs ` ( U - C ) ) < %s )' % (RBDG(a, b, 'C', R51), R51, R51)
    assert ba == '( %s /\\ %s /\\ %s )' % (B1, B2, B3), ba
    bcx = w.s([w.s([ab, w.s([ic, iu], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, INTG(a, b, 'C'), INTG(a, b, 'U'))), w.s([hp, ke], 'jca', '( %s -> ( %s /\\ %s C_ E ) )' % (A0, HOLG(P, 'E'), SQ('C', R51)))],
                    '3jca', '( %s -> %s )' % (A0, B1)),
               w.s([w.s([mr, w.s([mrp], 'rpgt0d', '( %s -> 0 < M )' % A0), rep], '3jca', '( %s -> ( M e. RR /\\ 0 < M /\\ %s ) )' % (A0, REP)), pc0], 'jca', '( %s -> %s )' % (A0, B2)),
               w.s([w.s([rbd, r51p], 'jca', '( %s -> ( %s /\\ 0 < %s ) )' % (A0, RBDG(a, b, 'C', R51), R51)), ult], 'jca', '( %s -> %s )' % (A0, B3)), w.inst('rectintbcx')],
              'syl3anc', '( %s -> %s )' % (A0, bcc))
    subu = w.s([w.s([w.s([], 'fveq2', '( z = U -> ( G ` z ) = ( G ` U ) )')], 'oveq1d', '( z = U -> ( ( G ` z ) - ( G ` C ) ) = %s )' % GD)], 'idi', '( z = U -> ( ( G ` z ) - ( G ` C ) ) = %s )' % GD)
    ue = w.s([ke, w.s([ab, iu, w.inst('crectinp')], 'syl2anc', '( %s -> U e. %s )' % (A0, SQ('C', R51)))], 'sseldd', '( %s -> U e. E )' % A0)
    pu = mptval(w, A0, 'z', 'E', P, 'U', GD, subu, ue)
    X = '( abs ` ( U - C ) )'
    BND = '( ( ( 2 x. M ) x. %s ) / ( %s - %s ) )' % (X, R51, X)
    b1 = w.s([w.s([w.s([pu], 'fveq2d', '( %s -> ( abs ` ( %s ` U ) ) = ( abs ` %s ) )' % (A0, P, GD))], 'eqcomd', '( %s -> ( abs ` %s ) = ( abs ` ( %s ` U ) ) )' % (A0, GD, P)), bcx],
             'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, GD, BND))
    den = w.s([r51, auc], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, R51, X))
    denp = lin8(w, A0, [ult], '0 < ( %s - %s )' % (R51, X), {X: auc})
    numr = w.s([w.s([numst(w, A0, '2', 'RR'), mr], 'remulcld', '( %s -> ( 2 x. M ) e. RR )' % A0), auc], 'remulcld', '( %s -> ( ( 2 x. M ) x. %s ) e. RR )' % (A0, X))
    mk = w.s([numst(w, A0, '; 4 9', 'RR'), mr], 'remulcld', '( %s -> ( ; 4 9 x. M ) e. RR )' % A0)
    prod = w.s([auc, numst(w, A0, R49, 'RR'), mr, w.s([mrp], 'rpge0d', '( %s -> 0 <_ M )' % A0), ule], 'lemul2ad', '( %s -> ( M x. %s ) <_ ( M x. %s ) )' % (A0, X, R49))
    lv = {X: auc, 'M': mr}
    key = lin8(w, A0, [prod], '( ( 2 x. M ) x. %s ) <_ ( ( %s - %s ) x. ( ; 4 9 x. M ) )' % (X, R51, X), lv, products=True)
    b2 = w.s([key, w.s([numr, mk, w.s([den, denp], 'jca', '( %s -> ( ( %s - %s ) e. RR /\\ 0 < ( %s - %s ) ) )' % (A0, R51, X, R51, X)), w.inst('ledivmul')], 'syl3anc',
                       '( %s -> ( %s <_ ( ; 4 9 x. M ) <-> ( ( 2 x. M ) x. %s ) <_ ( ( %s - %s ) x. ( ; 4 9 x. M ) ) ) )' % (A0, BND, X, R51, X))], 'mpbird', '( %s -> %s <_ ( ; 4 9 x. M ) )' % (A0, BND))
    gdr = w.s([w.s([w.s([gf, ue], 'ffvelcdmd', '( %s -> ( G ` U ) e. CC )' % A0), gc], 'subcld', '( %s -> %s e. CC )' % (A0, GD))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, GD))
    bndr = w.s([numr, den, w.s([den, denp], 'gt0ne0d', '( %s -> ( %s - %s ) =/= 0 )' % (A0, R51, X)) if False else w.s([denp], 'gt0ne0d', '( %s -> ( %s - %s ) =/= 0 )' % (A0, R51, X))],
               'redivcld', '( %s -> %s e. RR )' % (A0, BND))
    w.qed([gdr, bndr, mk, b1, b2], 'letrd', '( %s -> ( abs ` %s ) <_ ( ; 4 9 x. M ) )' % (A0, GD))
    return run8(w)


def sqab_st(w, ante, cst, rst, c, r):
    """( ante -> ( SQA e. CC /\\ SQB e. CC ) )"""
    a, b = SQA(c, r), SQB(c, r)
    rc_ = w.s([rst], 'recnd', '( %s -> %s e. CC )' % (ante, r))
    WW = '( %s + ( _i x. %s ) )' % (r, r)
    wc = w.s([rc_, w.s([closed(w, ante, 'ax-icn', '_i e. CC'), rc_], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (ante, r))], 'addcld', '( %s -> %s e. CC )' % (ante, WW))
    return w.s([w.s([cst, wc], 'subcld', '( %s -> %s e. CC )' % (ante, a)), w.s([cst, wc], 'addcld', '( %s -> %s e. CC )' % (ante, b))], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ante, a, b))


def bc_at(w, ante, pre, U, ust, ule):
    """( ante -> ( abs ` ( ( G ` U ) - ( G ` C ) ) ) <_ ( ; 4 9 x. M ) ) from pre : ( ante -> ( C1 /\\ C2 ) ) of logdvbc"""
    C1 = '( %s /\\ ( C e. CC /\\ %s C_ E ) )' % (HG, SQ('C', R51))
    C2 = '( M e. RR+ /\\ %s )' % REY
    C3 = '( %s e. CC /\\ ( abs ` ( %s - C ) ) <_ %s )' % (U, U, R49)
    j = w.s([w.s([pre, w.inst('simpl')], 'syl', '( %s -> %s )' % (ante, C1)), w.s([pre, w.inst('simpr')], 'syl', '( %s -> %s )' % (ante, C2)),
             w.s([ust, ule], 'jca', '( %s -> %s )' % (ante, C3))], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ante, C1, C2, C3))
    return w.s([j, w.inst('logdvbc')], 'syl', '( %s -> ( abs ` ( ( G ` %s ) - ( G ` C ) ) ) <_ ( ; 4 9 x. M ) )' % (ante, U))


def gen_logdvlip():
    w = W('logdvlip', 'The Lipschitz estimate behind the log-derivative bound: near a point ` S ` within ` 3 / 2 ` of the centre, the increments of ` G ` are at most ` 6272 M ` times the distance ( ~ rectintschx on a square of half-side ` 1 / 64 ` , ~ logdvbc on its frame).')
    C1 = '( %s /\\ ( C e. CC /\\ %s C_ E ) )' % (HG, SQ('C', R51))
    C2 = '( M e. RR+ /\\ %s )' % REY
    C3 = '( ( S e. CC /\\ ( abs ` ( S - C ) ) <_ ( 3 / 2 ) ) /\\ %s C_ E )' % SQ('S', R64)
    C4 = '( Y e. E /\\ ( abs ` ( Y - S ) ) < %s )' % R64
    A0 = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (C1, C2, C3, C4)
    DY = '( abs ` ( Y - S ) )'
    GD = '( ( G ` Y ) - ( G ` S ) )'
    CONC = '( abs ` %s ) <_ ( %s x. %s )' % (GD, K6, DY)
    c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1)); c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2))
    c34 = w.s([], 'simp3', '( %s -> ( %s /\\ %s ) )' % (A0, C3, C4))
    pre = w.s([c1, c2], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, C1, C2))
    c3 = w.s([c34, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, C3)); c4 = w.s([c34, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, C4))
    hg = w.s([c1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HG))
    cs = w.s([c1, w.inst('simprl')], 'syl', '( %s -> C e. CC )' % A0)
    mrp = w.s([c2, w.inst('simpl')], 'syl', '( %s -> M e. RR+ )' % A0)
    mr = w.s([mrp], 'rpred', '( %s -> M e. RR )' % A0)
    ss = w.s([c3, w.inst('simpll')], 'syl', '( %s -> S e. CC )' % A0)
    sle = w.s([c3, w.inst('simplr')], 'syl', '( %s -> ( abs ` ( S - C ) ) <_ ( 3 / 2 ) )' % A0)
    ke = w.s([c3, w.inst('simpr')], 'syl', '( %s -> %s C_ E )' % (A0, SQ('S', R64)))
    ye = w.s([c4, w.inst('simpl')], 'syl', '( %s -> Y e. E )' % A0)
    ylt = w.s([c4, w.inst('simpr')], 'syl', '( %s -> %s < %s )' % (A0, DY, R64))
    gcn = w.s([hg, w.inst('simpl')], 'syl', '( %s -> G e. ( E -cn-> CC ) )' % A0)
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : E --> CC )' % A0)
    ecc = w.s([gcn, w.inst('cncfrss')], 'syl', '( %s -> E C_ CC )' % A0)
    yc = w.s([ecc, ye], 'sseldd', '( %s -> Y e. CC )' % A0)
    r64 = numst(w, A0, R64, 'RR'); r64p = numst(w, A0, R64, 'gt0')
    a, b = SQA('S', R64), SQB('S', R64)
    ab = sqab_st(w, A0, ss, r64, 'S', R64)
    ip = center_int(w, A0, ss, r64, r64p, 'S', R64)
    iq = sqint_at(w, A0, ss, r64, yc, ylt, 'S', R64, 'Y')
    rbd = w.s([w.s([ss, r64], 'jca', '( %s -> ( S e. CC /\\ %s e. RR ) )' % (A0, R64)), w.inst('sqrbd')], 'syl', '( %s -> %s )' % (A0, RBDG(a, b, 'S', R64)))
    se = w.s([ke, w.s([ab, ip, w.inst('crectinp')], 'syl2anc', '( %s -> S e. %s )' % (A0, SQ('S', R64)))], 'sseldd', '( %s -> S e. E )' % A0)
    gs = w.s([gf, se], 'ffvelcdmd', '( %s -> ( G ` S ) e. CC )' % A0)
    H = PHI('( G ` S )')
    hh = w.s([hg, gs, w.inst('holsubc')], 'syl2anc', '( %s -> %s )' % (A0, HOLG(H, 'E')))
    ascr = w.s([w.s([ss, cs], 'subcld', '( %s -> ( S - C ) e. CC )' % A0)], 'abscld', '( %s -> ( abs ` ( S - C ) ) e. RR )' % A0)
    s49 = lin8(w, A0, [sle], '( abs ` ( S - C ) ) <_ %s' % R49, {'( abs ` ( S - C ) )': ascr})
    bs = bc_at(w, A0, pre, 'S', ss, s49)
    # frame bound 98 M
    FRS = FRG(a, b)
    Av = '( %s /\\ v e. %s )' % (A0, FRS)
    L = lambda st: lift(w, st, Av)
    vf = w.s([], 'simpr', '( %s -> v e. %s )' % (Av, FRS))
    frk = w.s([w.s([ab, ip, w.inst('crectfrp')], 'syl2anc', '( %s -> %s C_ ( %s \\ { S } ) )' % (A0, FRS, SQ('S', R64))),
               w.s([w.s([], 'difss', '( %s \\ { S } ) C_ %s' % (SQ('S', R64), SQ('S', R64)))], 'a1i', '( %s -> ( %s \\ { S } ) C_ %s )' % (A0, SQ('S', R64), SQ('S', R64)))],
              'sstrd', '( %s -> %s C_ %s )' % (A0, FRS, SQ('S', R64)))
    vk = w.s([L(frk), vf], 'sseldd', '( %s -> v e. %s )' % (Av, SQ('S', R64)))
    ve = w.s([L(ke), vk], 'sseldd', '( %s -> v e. E )' % Av)
    vc = w.s([L(ecc), ve], 'sseldd', '( %s -> v e. CC )' % Av)
    vm = w.s([w.s([w.s([L(ss), L(r64)], 'jca', '( %s -> ( S e. CC /\\ %s e. RR ) )' % (Av, R64)), vk], 'jca', '( %s -> ( ( S e. CC /\\ %s e. RR ) /\\ v e. %s ) )' % (Av, R64, SQ('S', R64))),
              w.inst('sqmem')], 'syl', '( %s -> ( abs ` ( v - S ) ) <_ ( 2 x. %s ) )' % (Av, R64))
    t3 = w.s([vc, L(cs), L(ss)], 'abs3difd', '( %s -> ( abs ` ( v - C ) ) <_ ( ( abs ` ( v - S ) ) + ( abs ` ( S - C ) ) ) )' % Av)
    avs = w.s([w.s([vc, L(ss)], 'subcld', '( %s -> ( v - S ) e. CC )' % Av)], 'abscld', '( %s -> ( abs ` ( v - S ) ) e. RR )' % Av)
    avc = w.s([w.s([vc, L(cs)], 'subcld', '( %s -> ( v - C ) e. CC )' % Av)], 'abscld', '( %s -> ( abs ` ( v - C ) ) e. RR )' % Av)
    v49 = lin8(w, Av, [t3, vm, L(sle)], '( abs ` ( v - C ) ) <_ %s' % R49, {'( abs ` ( v - S ) )': avs, '( abs ` ( v - C ) )': avc, '( abs ` ( S - C ) )': L(ascr)})
    bv = bc_at(w, Av, L(pre), 'v', vc, v49)
    gv = w.s([L(gf), ve], 'ffvelcdmd', '( %s -> ( G ` v ) e. CC )' % Av)
    # G ` C e. CC: C is in the square about C inside E
    r51 = numst(w, A0, R51, 'RR'); r51p = numst(w, A0, R51, 'gt0')
    cK = w.s([sqab_st(w, A0, cs, r51, 'C', R51), center_int(w, A0, cs, r51, r51p, 'C', R51), w.inst('crectinp')], 'syl2anc', '( %s -> C e. %s )' % (A0, SQ('C', R51)))
    ce = w.s([w.s([c1, w.inst('simprr')], 'syl', '( %s -> %s C_ E )' % (A0, SQ('C', R51))), cK], 'sseldd', '( %s -> C e. E )' % A0)
    gcc = w.s([gf, ce], 'ffvelcdmd', '( %s -> ( G ` C ) e. CC )' % A0)
    t4 = w.s([gv, L(gs), L(gcc)], 'abs3difd', '( %s -> ( abs ` ( ( G ` v ) - ( G ` S ) ) ) <_ ( ( abs ` ( ( G ` v ) - ( G ` C ) ) ) + ( abs ` ( ( G ` C ) - ( G ` S ) ) ) ) )' % Av)
    t5 = w.s([t4, w.s([w.s([L(gcc), L(gs)], 'abssubd', '( %s -> ( abs ` ( ( G ` C ) - ( G ` S ) ) ) = ( abs ` ( ( G ` S ) - ( G ` C ) ) ) )' % Av)], 'oveq2d',
                      '( %s -> ( ( abs ` ( ( G ` v ) - ( G ` C ) ) ) + ( abs ` ( ( G ` C ) - ( G ` S ) ) ) ) = ( ( abs ` ( ( G ` v ) - ( G ` C ) ) ) + ( abs ` ( ( G ` S ) - ( G ` C ) ) ) ) )' % Av)],
             'breqtrd', '( %s -> ( abs ` ( ( G ` v ) - ( G ` S ) ) ) <_ ( ( abs ` ( ( G ` v ) - ( G ` C ) ) ) + ( abs ` ( ( G ` S ) - ( G ` C ) ) ) ) )' % Av)
    ab_ = lambda X, st: w.s([st], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Av, X))
    lv = {'( abs ` ( ( G ` v ) - ( G ` S ) ) )': ab_('( ( G ` v ) - ( G ` S ) )', w.s([gv, L(gs)], 'subcld', '( %s -> ( ( G ` v ) - ( G ` S ) ) e. CC )' % Av)),
          '( abs ` ( ( G ` v ) - ( G ` C ) ) )': ab_('( ( G ` v ) - ( G ` C ) )', w.s([gv, L(gcc)], 'subcld', '( %s -> ( ( G ` v ) - ( G ` C ) ) e. CC )' % Av)),
          '( abs ` ( ( G ` S ) - ( G ` C ) ) )': ab_('( ( G ` S ) - ( G ` C ) )', w.s([L(gs), L(gcc)], 'subcld', '( %s -> ( ( G ` S ) - ( G ` C ) ) e. CC )' % Av)),
          'M': L(mr)}
    b98 = lin8(w, Av, [t5, bv, L(bs)], '( abs ` ( ( G ` v ) - ( G ` S ) ) ) <_ ( ; 9 8 x. M )', lv)
    subv = w.s([w.s([w.s([], 'fveq2', '( z = v -> ( G ` z ) = ( G ` v ) )')], 'oveq1d', '( z = v -> ( ( G ` z ) - ( G ` S ) ) = ( ( G ` v ) - ( G ` S ) ) )')], 'idi',
               '( z = v -> ( ( G ` z ) - ( G ` S ) ) = ( ( G ` v ) - ( G ` S ) ) )')
    hv = mptval(w, Av, 'z', 'E', H, 'v', '( ( G ` v ) - ( G ` S ) )', subv, ve)
    hb = w.s([w.s([hv], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` ( ( G ` v ) - ( G ` S ) ) ) )' % (Av, H)), b98], 'eqbrtrd', '( %s -> ( abs ` ( %s ` v ) ) <_ ( ; 9 8 x. M ) )' % (Av, H))
    ALV = 'A. v e. %s ( abs ` ( %s ` v ) ) <_ ( ; 9 8 x. M )' % (FRS, H)
    ALU = 'A. u e. %s ( abs ` ( %s ` u ) ) <_ ( ; 9 8 x. M )' % (FRS, H)
    cbv = w.s([w.s([w.s([w.s([], 'fveq2', '( v = u -> ( %s ` v ) = ( %s ` u ) )' % (H, H))], 'fveq2d', '( v = u -> ( abs ` ( %s ` v ) ) = ( abs ` ( %s ` u ) ) )' % (H, H))], 'breq1d',
                    '( v = u -> ( ( abs ` ( %s ` v ) ) <_ ( ; 9 8 x. M ) <-> ( abs ` ( %s ` u ) ) <_ ( ; 9 8 x. M ) ) )' % (H, H))], 'cbvralvw', '( %s <-> %s )' % (ALV, ALU))
    alu = w.s([w.s([hb], 'ralrimiva', '( %s -> %s )' % (A0, ALV)), cbv], 'sylib', '( %s -> %s )' % (A0, ALU))
    subs = w.s([w.s([w.s([], 'fveq2', '( z = S -> ( G ` z ) = ( G ` S ) )')], 'oveq1d', '( z = S -> ( ( G ` z ) - ( G ` S ) ) = ( ( G ` S ) - ( G ` S ) ) )')], 'idi',
               '( z = S -> ( ( G ` z ) - ( G ` S ) ) = ( ( G ` S ) - ( G ` S ) ) )')
    hs0 = w.s([mptval(w, A0, 'z', 'E', H, 'S', '( ( G ` S ) - ( G ` S ) )', subs, se), w.s([gs], 'subidd', '( %s -> ( ( G ` S ) - ( G ` S ) ) = 0 )' % A0)], 'eqtrd', '( %s -> ( %s ` S ) = 0 )' % (A0, H))
    SCH = tsub(FS['rectintschx'], {'F': H, 'D': 'E', 'A': a, 'B': b, 'P': 'S', 'Q': 'Y', 'R': R64, 'M': '( ; 9 8 x. M )'})
    sa, sc = ante_of(SCH)
    S1 = '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s C_ E ) )' % (a, b, INTG(a, b, 'S'), INTG(a, b, 'Y'), HOLG(H, 'E'), SQ('S', R64))
    S2 = '( ( %s /\\ 0 < %s ) /\\ ( ( ( ; 9 8 x. M ) e. RR /\\ %s ) /\\ ( %s ` S ) = 0 ) )' % (RBDG(a, b, 'S', R64), R64, ALU, H)
    assert sa == '( %s /\\ %s )' % (S1, S2), sa
    m98 = w.s([numst(w, A0, '; 9 8', 'RR'), mr], 'remulcld', '( %s -> ( ; 9 8 x. M ) e. RR )' % A0)
    sch = w.s([w.s([w.s([ab, w.s([ip, iq], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, INTG(a, b, 'S'), INTG(a, b, 'Y'))), w.s([hh, ke], 'jca', '( %s -> ( %s /\\ %s C_ E ) )' % (A0, HOLG(H, 'E'), SQ('S', R64)))],
                        '3jca', '( %s -> %s )' % (A0, S1)),
                    w.s([w.s([rbd, r64p], 'jca', '( %s -> ( %s /\\ 0 < %s ) )' % (A0, RBDG(a, b, 'S', R64), R64)),
                         w.s([w.s([m98, alu], 'jca', '( %s -> ( ( ; 9 8 x. M ) e. RR /\\ %s ) )' % (A0, ALU)), hs0], 'jca', '( %s -> ( ( ( ; 9 8 x. M ) e. RR /\\ %s ) /\\ ( %s ` S ) = 0 ) )' % (A0, ALU, H))],
                        'jca', '( %s -> %s )' % (A0, S2))], 'jca', '( %s -> %s )' % (A0, sa)), w.inst('rectintschx')], 'syl', '( %s -> %s )' % (A0, sc))
    suby = w.s([w.s([w.s([], 'fveq2', '( z = Y -> ( G ` z ) = ( G ` Y ) )')], 'oveq1d', '( z = Y -> ( ( G ` z ) - ( G ` S ) ) = %s )' % GD)], 'idi', '( z = Y -> ( ( G ` z ) - ( G ` S ) ) = %s )' % GD)
    hy = mptval(w, A0, 'z', 'E', H, 'Y', GD, suby, ye)
    sch2 = w.s([w.s([w.s([w.s([hy], 'fveq2d', '( %s -> ( abs ` ( %s ` Y ) ) = ( abs ` %s ) )' % (A0, H, GD))], 'oveq1d',
                          '( %s -> ( ( abs ` ( %s ` Y ) ) x. %s ) = ( ( abs ` %s ) x. %s ) )' % (A0, H, R64, GD, R64))], 'eqcomd',
                    '( %s -> ( ( abs ` %s ) x. %s ) = ( ( abs ` ( %s ` Y ) ) x. %s ) )' % (A0, GD, R64, H, R64)), sch], 'eqbrtrd',
               '( %s -> ( ( abs ` %s ) x. %s ) <_ ( ( ; 9 8 x. M ) x. %s ) )' % (A0, GD, R64, DY))
    agd = w.s([w.s([w.s([gf, ye], 'ffvelcdmd', '( %s -> ( G ` Y ) e. CC )' % A0), gs], 'subcld', '( %s -> %s e. CC )' % (A0, GD))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, GD))
    ady = w.s([w.s([yc, ss], 'subcld', '( %s -> ( Y - S ) e. CC )' % A0)], 'abscld', '( %s -> %s e. RR )' % (A0, DY))
    lin8(w, A0, [sch2], CONC, {'( abs ` %s )' % GD: agd, DY: ady, 'M': mr}, products=True)
    w.lines[-1] = 'qed' + w.lines[-1][w.lines[-1].index(':'):]
    return run8(w)


def gen_logdvbnd():
    w = W('logdvbnd', 'The log-derivative bound: a function holomorphic on an open set containing the square of half-side 2 about ` C ` , zero-free on the square of half-side ` 13 / 8 ` , with ` log abs F - log abs F ( C ) <_ M ` there, has logarithmic derivative at most ` 6272 M ` within ` 3 / 2 ` of ` C ` ( Lean ` norm_logDeriv_le_of_log_norm_bound ` , constant ` 1600 ` there; ~ hollog , ~ logdvlip , ~ dvlipbnd ).')
    R138, R38 = '( ; 1 3 / 8 )', '( 3 / 8 )'
    a, b = SQA('C', R138), SQB('C', R138)
    E = ORECT(a, b)
    SQ2, SQ138 = SQ('C', '2'), SQ('C', R138)
    NZ = 'A. y e. %s ( F ` y ) =/= 0' % SQ138
    LG = lambda t: '( log ` ( abs ` ( F ` %s ) ) )' % t
    RE_ = 'A. y e. %s ( %s - %s ) <_ M' % (SQ138, LG('y'), LG('C'))
    C1 = '( %s /\\ ( C e. CC /\\ %s C_ D ) )' % (HOL, SQ2)
    C2 = '( %s /\\ ( M e. RR+ /\\ %s ) )' % (NZ, RE_)
    C3 = '( S e. CC /\\ ( abs ` ( S - C ) ) <_ ( 3 / 2 ) )'
    A0 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
    GOAL = '( abs ` ( ( ( CC _D F ) ` S ) / ( F ` S ) ) ) <_ %s' % K6
    assert '( %s -> %s )' % (A0, GOAL) == FS['logdvbnd']
    c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1)); c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2)); c3 = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
    hol = w.s([c1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    cs = w.s([c1, w.inst('simprl')], 'syl', '( %s -> C e. CC )' % A0)
    s2d = w.s([c1, w.inst('simprr')], 'syl', '( %s -> %s C_ D )' % (A0, SQ2))
    nz = w.s([c2, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, NZ))
    mrp = w.s([c2, w.inst('simprl')], 'syl', '( %s -> M e. RR+ )' % A0)
    re_ = w.s([c2, w.inst('simprr')], 'syl', '( %s -> %s )' % (A0, RE_))
    ss = w.s([c3, w.inst('simpl')], 'syl', '( %s -> S e. CC )' % A0)
    sle = w.s([c3, w.inst('simpr')], 'syl', '( %s -> ( abs ` ( S - C ) ) <_ ( 3 / 2 ) )' % A0)
    mr = w.s([mrp], 'rpred', '( %s -> M e. RR )' % A0)
    r138 = numst(w, A0, R138, 'RR')
    ab = sqab_st(w, A0, cs, r138, 'C', R138)
    # GEO
    sq = w.s([w.s([cs, r138], 'jca', '( %s -> ( C e. CC /\\ %s e. RR ) )' % (A0, R138)), w.inst('sqre')], 'syl', '( %s -> %s )' % (A0, tsub(stmt('sqre'), {'R': R138}).split(' -> ', 1)[1][:-2]))
    SQR = ante_of(tsub(stmt('sqre'), {'R': R138}))[1]
    rr_ = w.s([sq, w.inst('simpl')], 'syl', '( %s -> ( ( Re ` %s ) = ( ( Re ` C ) - %s ) /\\ ( Re ` %s ) = ( ( Re ` C ) + %s ) ) )' % (A0, a, R138, b, R138))
    ii_ = w.s([sq, w.inst('simpr')], 'syl', '( %s -> ( ( Im ` %s ) = ( ( Im ` C ) - %s ) /\\ ( Im ` %s ) = ( ( Im ` C ) + %s ) ) )' % (A0, a, R138, b, R138))
    pa = [w.s([rr_, w.inst('simpl')], 'syl', '( %s -> ( Re ` %s ) = ( ( Re ` C ) - %s ) )' % (A0, a, R138)), w.s([rr_, w.inst('simpr')], 'syl', '( %s -> ( Re ` %s ) = ( ( Re ` C ) + %s ) )' % (A0, b, R138)),
          w.s([ii_, w.inst('simpl')], 'syl', '( %s -> ( Im ` %s ) = ( ( Im ` C ) - %s ) )' % (A0, a, R138)), w.s([ii_, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) = ( ( Im ` C ) + %s ) )' % (A0, b, R138))]
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> %s e. CC )' % (A0, a)); bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (A0, b))
    lv = {}
    for x, st in ((a, ac), (b, bc), ('C', cs)):
        lv['( Re ` %s )' % x] = w.s([st], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, x))
        lv['( Im ` %s )' % x] = w.s([st], 'imcld', '( %s -> ( Im ` %s ) e. RR )' % (A0, x))
    geo = w.s([lin8(w, A0, [pa[0], pa[1]], '( Re ` %s ) <_ ( Re ` %s )' % (a, b), lv), lin8(w, A0, [pa[2], pa[3]], '( Im ` %s ) <_ ( Im ` %s )' % (a, b), lv)], 'jca',
              '( %s -> %s )' % (A0, GEOG(a, b)))
    # NEST
    W38 = '( %s + ( _i x. %s ) )' % (R38, R38)
    X = '( %s + %s )' % (R138, R38)
    nst = w.s([w.s([cs, w.s([numst(w, A0, R138, 'CC'), numst(w, A0, R38, 'CC')], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, R138, R38))], 'jca',
                   '( %s -> ( C e. CC /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, R138, R38)), w.inst('sqnest')], 'syl',
              '( %s -> ( ( %s - %s ) = %s /\\ ( %s + %s ) = %s ) )' % (A0, a, W38, SQA('C', X), b, W38, SQB('C', X)))
    x2 = lin.lineq(w, A0, X, '2', closure=cl.Closure(w, A0, {}))
    i2 = w.s([x2], 'oveq2d', '( %s -> ( _i x. %s ) = ( _i x. 2 ) )' % (A0, X))
    w2 = w.s([x2, i2], 'oveq12d', '( %s -> ( %s + ( _i x. %s ) ) = ( 2 + ( _i x. 2 ) ) )' % (A0, X, X))
    ea = w.s([w.s([nst, w.inst('simpl')], 'syl', '( %s -> ( %s - %s ) = %s )' % (A0, a, W38, SQA('C', X))), w.s([w2], 'oveq2d', '( %s -> %s = %s )' % (A0, SQA('C', X), SQA('C', '2')))],
             'eqtrd', '( %s -> ( %s - %s ) = %s )' % (A0, a, W38, SQA('C', '2')))
    eb = w.s([w.s([nst, w.inst('simpr')], 'syl', '( %s -> ( %s + %s ) = %s )' % (A0, b, W38, SQB('C', X))), w.s([w2], 'oveq2d', '( %s -> %s = %s )' % (A0, SQB('C', X), SQB('C', '2')))],
             'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A0, b, W38, SQB('C', '2')))
    NR = '( ( %s - %s ) crect ( %s + %s ) )' % (a, W38, b, W38)
    nd = w.s([w.s([ea, eb], 'oveq12d', '( %s -> %s = %s )' % (A0, NR, SQ2)), s2d], 'eqsstrd', '( %s -> %s C_ D )' % (A0, NR))
    nest = w.s([numst(w, A0, R38, 'RR+'), nd], 'jca', '( %s -> ( %s e. RR+ /\\ %s C_ D ) )' % (A0, R38, NR))
    eop = w.s([w.s([], 'orectopn', '%s e. %s' % (E, TOP))], 'a1i', '( %s -> %s e. %s )' % (A0, E, TOP))
    ek = w.s([ab, w.inst('orectss')], 'syl', '( %s -> %s C_ %s )' % (A0, E, SQ138))
    HL = tsub(stmt('hollog'), {'A': a, 'B': b, 'R': R38, 'E': E})
    ha, hc = ante_of(HL)
    H1 = '( %s /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ %s ) /\\ ( %s e. RR+ /\\ %s C_ D ) )' % (HOL, a, b, GEOG(a, b), R38, NR)
    H2 = '( %s /\\ ( %s e. %s /\\ %s C_ %s ) )' % (NZ, E, TOP, E, SQ138)
    assert ha == '( %s /\\ %s )' % (H1, H2), ha
    exg = w.s([w.s([w.s([hol, w.s([ab, geo], 'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ %s ) )' % (A0, a, b, GEOG(a, b))), nest], '3jca', '( %s -> %s )' % (A0, H1)),
                    w.s([nz, w.s([eop, ek], 'jca', '( %s -> ( %s e. %s /\\ %s C_ %s ) )' % (A0, E, TOP, E, SQ138))], 'jca', '( %s -> %s )' % (A0, H2))], 'jca', '( %s -> %s )' % (A0, ha)),
               w.inst('hollog')], 'syl', '( %s -> %s )' % (A0, hc))
    assert hc.startswith('E. g ( ')
    INNER = hc[len('E. g '):]
    HGE = HOLE('g', E)
    BOTH = INNER[len('( %s /\\ ' % HGE):-2]
    AG = '( %s /\\ %s )' % (A0, INNER)
    L = lambda st: lift(w, st, AG)
    hg = w.s([], 'simprl', '( %s -> %s )' % (AG, HGE))
    both = w.s([], 'simprr', '( %s -> %s )' % (AG, BOTH))
    # squares inside E
    r51 = numst(w, AG, R51, 'RR'); r64 = numst(w, AG, R64, 'RR')
    csg = L(cs); ssg = L(ss)
    a0c = abs0st(w, AG, csg, 'C')
    ac0r = w.s([w.s([csg, csg], 'subcld', '( %s -> ( C - C ) e. CC )' % AG)], 'abscld', '( %s -> ( abs ` ( C - C ) ) e. RR )' % AG)
    lt1 = lin8(w, AG, [a0c], '( ( abs ` ( C - C ) ) + %s ) < %s' % (R51, R138), {'( abs ` ( C - C ) )': ac0r})
    asc = w.s([w.s([ssg, csg], 'subcld', '( %s -> ( S - C ) e. CC )' % AG)], 'abscld', '( %s -> ( abs ` ( S - C ) ) e. RR )' % AG)
    lt2 = lin8(w, AG, [L(sle)], '( ( abs ` ( S - C ) ) + %s ) < %s' % (R64, R138), {'( abs ` ( S - C ) )': asc})
    r138g = L(r138)

    def sub_(U, T, ust, tst, ltst):
        f = '( ( C e. CC /\\ ( %s e. RR /\\ %s e. RR ) ) /\\ ( %s e. CC /\\ ( ( abs ` ( %s - C ) ) + %s ) < %s ) )' % (R138, T, U, U, T, R138)
        j = w.s([w.s([csg, w.s([r138g, tst], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (AG, R138, T))], 'jca', '( %s -> ( C e. CC /\\ ( %s e. RR /\\ %s e. RR ) ) )' % (AG, R138, T)),
                 w.s([ust, ltst], 'jca', '( %s -> ( %s e. CC /\\ ( ( abs ` ( %s - C ) ) + %s ) < %s ) )' % (AG, U, U, T, R138))], 'jca', '( %s -> %s )' % (AG, f))
        return w.s([j, w.inst('sqsub')], 'syl', '( %s -> %s C_ %s )' % (AG, SQ(U, T), E))
    k51 = sub_('C', R51, csg, r51, lt1)
    k64 = sub_('S', R64, ssg, r64, lt2)
    r64p = numst(w, AG, R64, 'gt0')
    se = w.s([k64, w.s([sqab_st(w, AG, ssg, r64, 'S', R64), center_int(w, AG, ssg, r64, r64p, 'S', R64), w.inst('crectinp')], 'syl2anc', '( %s -> S e. %s )' % (AG, SQ('S', R64)))],
             'sseldd', '( %s -> S e. %s )' % (AG, E))
    r51p = numst(w, AG, R51, 'gt0')
    ce = w.s([k51, w.s([sqab_st(w, AG, csg, r51, 'C', R51), center_int(w, AG, csg, r51, r51p, 'C', R51), w.inst('crectinp')], 'syl2anc', '( %s -> C e. %s )' % (AG, SQ('C', R51)))],
             'sseldd', '( %s -> C e. %s )' % (AG, E))
    gcn = w.s([hg, w.inst('simpl')], 'syl', '( %s -> g e. ( %s -cn-> CC ) )' % (AG, E))
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> g : %s --> CC )' % (AG, E))

    def both_at(ante, T, tst):
        """( ante -> body(T) ) from BOTH lifted"""
        B = lambda z: '( ( ( CC _D g ) ` %s ) = ( ( ( CC _D F ) ` %s ) / ( F ` %s ) ) /\\ ( exp ` ( g ` %s ) ) = ( F ` %s ) )' % (z, z, z, z, z)
        e1 = w.s([w.s([], 'fveq2', '( z = %s -> ( ( CC _D g ) ` z ) = ( ( CC _D g ) ` %s ) )' % (T, T)),
                  w.s([w.s([], 'fveq2', '( z = %s -> ( ( CC _D F ) ` z ) = ( ( CC _D F ) ` %s ) )' % (T, T)), w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (T, T))], 'oveq12d',
                      '( z = %s -> ( ( ( CC _D F ) ` z ) / ( F ` z ) ) = ( ( ( CC _D F ) ` %s ) / ( F ` %s ) ) )' % (T, T, T))], 'eqeq12d',
                 '( z = %s -> ( ( ( CC _D g ) ` z ) = ( ( ( CC _D F ) ` z ) / ( F ` z ) ) <-> ( ( CC _D g ) ` %s ) = ( ( ( CC _D F ) ` %s ) / ( F ` %s ) ) ) )' % (T, T, T, T))
        e2 = w.s([w.s([w.s([], 'fveq2', '( z = %s -> ( g ` z ) = ( g ` %s ) )' % (T, T))], 'fveq2d', '( z = %s -> ( exp ` ( g ` z ) ) = ( exp ` ( g ` %s ) ) )' % (T, T)),
                  w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (T, T))], 'eqeq12d', '( z = %s -> ( ( exp ` ( g ` z ) ) = ( F ` z ) <-> ( exp ` ( g ` %s ) ) = ( F ` %s ) ) )' % (T, T, T))
        sub = w.s([e1, e2], 'anbi12d', '( z = %s -> ( %s <-> %s ) )' % (T, B('z'), B(T)))
        return w.s([sub, lift(w, both, ante), tst], 'rspcdva', '( %s -> %s )' % (ante, B(T)))

    def relog(ante, T, tst):
        """( ante -> ( Re ` ( g ` T ) ) = LG(T) )"""
        bt = both_at(ante, T, tst)
        ex_ = w.s([bt, w.inst('simpr')], 'syl', '( %s -> ( exp ` ( g ` %s ) ) = ( F ` %s ) )' % (ante, T, T))
        gt = w.s([lift(w, gf, ante), tst], 'ffvelcdmd', '( %s -> ( g ` %s ) e. CC )' % (ante, T))
        e1 = w.s([w.s([w.s([ex_], 'eqcomd', '( %s -> ( F ` %s ) = ( exp ` ( g ` %s ) ) )' % (ante, T, T))], 'fveq2d', '( %s -> ( abs ` ( F ` %s ) ) = ( abs ` ( exp ` ( g ` %s ) ) ) )' % (ante, T, T))],
                 'fveq2d', '( %s -> %s = ( log ` ( abs ` ( exp ` ( g ` %s ) ) ) ) )' % (ante, LG(T), T))
        e2 = w.s([w.s([gt, w.inst('absef')], 'syl', '( %s -> ( abs ` ( exp ` ( g ` %s ) ) ) = ( exp ` ( Re ` ( g ` %s ) ) ) )' % (ante, T, T))], 'fveq2d',
                 '( %s -> ( log ` ( abs ` ( exp ` ( g ` %s ) ) ) ) = ( log ` ( exp ` ( Re ` ( g ` %s ) ) ) ) )' % (ante, T, T))
        e3 = w.s([w.s([gt], 'recld', '( %s -> ( Re ` ( g ` %s ) ) e. RR )' % (ante, T)), w.inst('relogef')], 'syl', '( %s -> ( log ` ( exp ` ( Re ` ( g ` %s ) ) ) ) = ( Re ` ( g ` %s ) ) )' % (ante, T, T))
        return w.s([w.s([w.s([e1, e2], 'eqtrd', '( %s -> %s = ( log ` ( exp ` ( Re ` ( g ` %s ) ) ) ) )' % (ante, LG(T), T)), e3], 'eqtrd', '( %s -> %s = ( Re ` ( g ` %s ) ) )' % (ante, LG(T), T))],
                   'eqcomd', '( %s -> ( Re ` ( g ` %s ) ) = %s )' % (ante, T, LG(T)))
    # the real-part bound on E
    Av = '( %s /\\ v e. %s )' % (AG, E)
    ve = w.s([], 'simpr', '( %s -> v e. %s )' % (Av, E))
    gv = w.s([lift(w, gf, Av), ve], 'ffvelcdmd', '( %s -> ( g ` v ) e. CC )' % Av)
    gc = w.s([lift(w, gf, Av), lift(w, ce, Av)], 'ffvelcdmd', '( %s -> ( g ` C ) e. CC )' % Av)
    rsub = w.s([gv, gc], 'resubd', '( %s -> ( Re ` ( ( g ` v ) - ( g ` C ) ) ) = ( ( Re ` ( g ` v ) ) - ( Re ` ( g ` C ) ) ) )' % Av)
    rl = w.s([rsub, w.s([relog(Av, 'v', ve), relog(Av, 'C', lift(w, ce, Av))], 'oveq12d', '( %s -> ( ( Re ` ( g ` v ) ) - ( Re ` ( g ` C ) ) ) = ( %s - %s ) )' % (Av, LG('v'), LG('C')))],
             'eqtrd', '( %s -> ( Re ` ( ( g ` v ) - ( g ` C ) ) ) = ( %s - %s ) )' % (Av, LG('v'), LG('C')))
    vk = w.s([lift(w, ek, Av), ve], 'sseldd', '( %s -> v e. %s )' % (Av, SQ138))
    suby = w.s([w.s([w.s([w.s([w.s([], 'fveq2', '( y = v -> ( F ` y ) = ( F ` v ) )')], 'fveq2d', '( y = v -> ( abs ` ( F ` y ) ) = ( abs ` ( F ` v ) ) )')], 'fveq2d',
                          '( y = v -> %s = %s )' % (LG('y'), LG('v')))], 'oveq1d', '( y = v -> ( %s - %s ) = ( %s - %s ) )' % (LG('y'), LG('C'), LG('v'), LG('C')))], 'breq1d',
               '( y = v -> ( ( %s - %s ) <_ M <-> ( %s - %s ) <_ M ) )' % (LG('y'), LG('C'), LG('v'), LG('C')))
    rev = w.s([suby, lift(w, re_, Av), vk], 'rspcdva', '( %s -> ( %s - %s ) <_ M )' % (Av, LG('v'), LG('C')))
    rgv = w.s([rl, rev], 'eqbrtrd', '( %s -> ( Re ` ( ( g ` v ) - ( g ` C ) ) ) <_ M )' % Av)
    REV = 'A. v e. %s ( Re ` ( ( g ` v ) - ( g ` C ) ) ) <_ M' % E
    REYg = 'A. y e. %s ( Re ` ( ( g ` y ) - ( g ` C ) ) ) <_ M' % E
    cbv = w.s([w.s([w.s([w.s([w.s([], 'fveq2', '( v = y -> ( g ` v ) = ( g ` y ) )')], 'oveq1d', '( v = y -> ( ( g ` v ) - ( g ` C ) ) = ( ( g ` y ) - ( g ` C ) ) )')], 'fveq2d',
                         '( v = y -> ( Re ` ( ( g ` v ) - ( g ` C ) ) ) = ( Re ` ( ( g ` y ) - ( g ` C ) ) ) )')], 'breq1d',
                    '( v = y -> ( ( Re ` ( ( g ` v ) - ( g ` C ) ) ) <_ M <-> ( Re ` ( ( g ` y ) - ( g ` C ) ) ) <_ M ) )')], 'cbvralvw', '( %s <-> %s )' % (REV, REYg))
    reyg = w.s([w.s([rgv], 'ralrimiva', '( %s -> %s )' % (AG, REV)), cbv], 'sylib', '( %s -> %s )' % (AG, REYg))
    # the Lipschitz hypothesis of dvlipbnd
    LD = lambda y: '( ( abs ` ( %s - S ) ) < %s -> ( abs ` ( ( g ` %s ) - ( g ` S ) ) ) <_ ( %s x. ( abs ` ( %s - S ) ) ) )' % (y, R64, y, K6, y)
    LP = tsub(stmt('logdvlip'), {'G': 'g', 'E': E, 'Y': 'v'})
    la, lc = ante_of(LP)
    Aw = '( %s /\\ ( abs ` ( v - S ) ) < %s )' % (Av, R64)
    L1 = '( %s /\\ ( C e. CC /\\ %s C_ %s ) )' % (HGE, SQ('C', R51), E)
    L2 = '( M e. RR+ /\\ %s )' % REYg
    L3 = '( ( S e. CC /\\ ( abs ` ( S - C ) ) <_ ( 3 / 2 ) ) /\\ %s C_ %s )' % (SQ('S', R64), E)
    L4 = '( v e. %s /\\ ( abs ` ( v - S ) ) < %s )' % (E, R64)
    assert la == '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (L1, L2, L3, L4), la
    Lw = lambda st: lift(w, st, Aw)
    lw = w.s([w.s([w.s([Lw(hg), w.s([Lw(cs), Lw(k51)], 'jca', '( %s -> ( C e. CC /\\ %s C_ %s ) )' % (Aw, SQ('C', R51), E))], 'jca', '( %s -> %s )' % (Aw, L1)),
                   w.s([Lw(mrp), Lw(reyg)], 'jca', '( %s -> %s )' % (Aw, L2)),
                   w.s([w.s([Lw(c3), Lw(k64)], 'jca', '( %s -> %s )' % (Aw, L3)), w.s([Lw(ve), w.s([], 'simpr', '( %s -> ( abs ` ( v - S ) ) < %s )' % (Aw, R64))], 'jca', '( %s -> %s )' % (Aw, L4))],
                       'jca', '( %s -> ( %s /\\ %s ) )' % (Aw, L3, L4))], '3jca', '( %s -> %s )' % (Aw, la)), w.inst('logdvlip')], 'syl', '( %s -> %s )' % (Aw, lc))
    lv_ = w.s([lw], 'ex', '( %s -> %s )' % (Av, LD('v')))
    LV = 'A. v e. %s %s' % (E, LD('v'))
    LY = 'A. y e. %s %s' % (E, LD('y'))
    cbl = w.s([w.s([w.s([w.s([w.s([], 'oveq1', '( v = y -> ( v - S ) = ( y - S ) )')], 'fveq2d', '( v = y -> ( abs ` ( v - S ) ) = ( abs ` ( y - S ) ) )')], 'breq1d',
                         '( v = y -> ( ( abs ` ( v - S ) ) < %s <-> ( abs ` ( y - S ) ) < %s ) )' % (R64, R64)),
                    w.s([w.s([w.s([w.s([], 'fveq2', '( v = y -> ( g ` v ) = ( g ` y ) )')], 'oveq1d', '( v = y -> ( ( g ` v ) - ( g ` S ) ) = ( ( g ` y ) - ( g ` S ) ) )')], 'fveq2d',
                              '( v = y -> ( abs ` ( ( g ` v ) - ( g ` S ) ) ) = ( abs ` ( ( g ` y ) - ( g ` S ) ) ) )'),
                         w.s([w.s([w.s([], 'oveq1', '( v = y -> ( v - S ) = ( y - S ) )')], 'fveq2d', '( v = y -> ( abs ` ( v - S ) ) = ( abs ` ( y - S ) ) )')], 'oveq2d',
                             '( v = y -> ( %s x. ( abs ` ( v - S ) ) ) = ( %s x. ( abs ` ( y - S ) ) ) )' % (K6, K6))], 'breq12d',
                        '( v = y -> ( ( abs ` ( ( g ` v ) - ( g ` S ) ) ) <_ ( %s x. ( abs ` ( v - S ) ) ) <-> ( abs ` ( ( g ` y ) - ( g ` S ) ) ) <_ ( %s x. ( abs ` ( y - S ) ) ) ) )' % (K6, K6))],
                   'imbi12d', '( v = y -> ( %s <-> %s ) )' % (LD('v'), LD('y')))], 'cbvralvw', '( %s <-> %s )' % (LV, LY))
    ly = w.s([w.s([lv_], 'ralrimiva', '( %s -> %s )' % (AG, LV)), cbl], 'sylib', '( %s -> %s )' % (AG, LY))
    DL = tsub(FS['dvlipbnd'], {'F': 'g', 'D': E, 'X': 'S', 'K': K6, 'S': R64})
    da, dc = ante_of(DL)
    k6 = w.s([numst(w, AG, '; ; ; 6 2 7 2', 'RR'), L(mr)], 'remulcld', '( %s -> %s e. RR )' % (AG, K6))
    D1 = '( S e. %s /\\ ( %s e. RR /\\ %s e. RR+ ) )' % (E, K6, R64)
    assert da == '( %s /\\ %s /\\ %s )' % (HGE, D1, LY), da
    dv = w.s([w.s([hg, w.s([se, w.s([k6, numst(w, AG, R64, 'RR+')], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR+ ) )' % (AG, K6, R64))], 'jca', '( %s -> %s )' % (AG, D1)), ly], '3jca',
                   '( %s -> %s )' % (AG, da)), w.inst('dvlipbnd')], 'syl', '( %s -> %s )' % (AG, dc))
    bs = w.s([both_at(AG, 'S', se), w.inst('simpl')], 'syl', '( %s -> ( ( CC _D g ) ` S ) = ( ( ( CC _D F ) ` S ) / ( F ` S ) ) )' % AG)
    fin = w.s([w.s([bs], 'fveq2d', '( %s -> ( abs ` ( ( CC _D g ) ` S ) ) = ( abs ` ( ( ( CC _D F ) ` S ) / ( F ` S ) ) ) )' % AG), dv], 'eqbrtrrd', '( %s -> %s )' % (AG, GOAL))
    w.qed([exg, w.s([w.s([fin], 'ex', '( %s -> ( %s -> %s ) )' % (A0, INNER, GOAL))], 'exlimdv', '( %s -> ( %s -> %s ) )' % (A0, hc, GOAL))], 'mpd', '( %s -> %s )' % (A0, GOAL))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_holsubc, gen_logdvbc, gen_logdvlip, gen_logdvbnd]:
        g()
