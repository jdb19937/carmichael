"""Sortie C6b, part 8: the order of vanishing, second half (holordex,
holordfin, holordfinr, holord0, holordge1, holordcf)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *
from c6b_x import gsub, TAY, FACX, ZERN, CTXN, NAL, A0F
from c6b_ord1 import HEQ, FACE

ORD = '( F holord P )'


def phisubn(w, n1, n2, g='a', X='P'):
    """closed: ( n1 = n2 -> ( PHI(X,n1,g) <-> PHI(X,n2,g) ) )"""
    A = '%s = %s' % (n1, n2)
    s = w.s([w.s([w.s([w.s([], 'oveq2', '( %s -> ( ( z - %s ) ^ %s ) = ( ( z - %s ) ^ %s ) )' % (A, X, n1, X, n2))], 'oveq1d', '( %s -> ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) )' % (A, X, n1, g, X, n2, g))], 'eqeq2d',
                  '( %s -> ( ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) <-> ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) ) )' % (A, X, n1, g, X, n2, g))], 'ralbidv',
             '( %s -> ( A. z e. D ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) <-> A. z e. D ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) ) )' % (A, X, n1, g, X, n2, g))
    return w.s([s], '3anbi3d', '( %s -> ( %s <-> %s ) )' % (A, PHI(X, n1, g), PHI(X, n2, g)))


def gsubx(w, GEXP, NEXP, X='P'):
    """closed: ( g = GEXP -> ( PHI(X,NEXP,g) <-> PHI(X,NEXP,GEXP) ) )"""
    e1 = w.s([], 'eleq1', '( g = %s -> ( g e. ( D -cn-> CC ) <-> %s e. ( D -cn-> CC ) ) )' % (GEXP, GEXP))
    e2 = w.s([w.s([w.s([], 'oveq2', '( g = %s -> ( CC _D g ) = ( CC _D %s ) )' % (GEXP, GEXP))], 'dmeqd', '( g = %s -> dom ( CC _D g ) = dom ( CC _D %s ) )' % (GEXP, GEXP))], 'sseq2d',
             '( g = %s -> ( D C_ dom ( CC _D g ) <-> D C_ dom ( CC _D %s ) ) )' % (GEXP, GEXP))
    e12 = w.s([e1, e2], 'anbi12d', '( g = %s -> ( %s <-> %s ) )' % (GEXP, HOLG('g'), HOLG(GEXP)))
    e3 = w.s([w.s([], 'fveq1', '( g = %s -> ( g ` %s ) = ( %s ` %s ) )' % (GEXP, X, GEXP, X))], 'neeq1d', '( g = %s -> ( ( g ` %s ) =/= 0 <-> ( %s ` %s ) =/= 0 ) )' % (GEXP, X, GEXP, X))
    e4 = w.s([w.s([w.s([w.s([], 'fveq1', '( g = %s -> ( g ` z ) = ( %s ` z ) )' % (GEXP, GEXP))], 'oveq2d', '( g = %s -> ( ( ( z - %s ) ^ %s ) x. ( g ` z ) ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) )' % (GEXP, X, NEXP, X, NEXP, GEXP))], 'eqeq2d',
                  '( g = %s -> ( ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( g ` z ) ) <-> ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) ) )' % (GEXP, X, NEXP, X, NEXP, GEXP))], 'ralbidv',
             '( g = %s -> ( A. z e. D ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( g ` z ) ) <-> A. z e. D ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) ) )' % (GEXP, X, NEXP, X, NEXP, GEXP))
    return w.s([e12, e3, e4], '3anbi123d', '( g = %s -> ( %s <-> %s ) )' % (GEXP, PHI(X, NEXP), PHI(X, NEXP, GEXP)))


def exga(w, NEXP, X='P'):
    """closed: ( E. g PHI(X,NEXP,g) <-> E. a PHI(X,NEXP,a) )"""
    return w.s([gsubx(w, 'a', NEXP, X)], 'cbvexv', '( E. g %s <-> E. a %s )' % (PHI(X, NEXP), PHI(X, NEXP, 'a')))


def facatp(w, g, n, X='P'):
    """closed: ( z = X -> ( ( F ` z ) = ... <-> ( F ` X ) = ( ( ( X - X ) ^ n ) x. ( g ` X ) ) ) )"""
    A = 'z = %s' % X
    return w.s([w.s([], 'fveq2', '( %s -> ( F ` z ) = ( F ` %s ) )' % (A, X)), w.s([w.s([w.s([], 'oveq1', '( %s -> ( z - %s ) = ( %s - %s ) )' % (A, X, X, X))], 'oveq1d', '( %s -> ( ( z - %s ) ^ %s ) = ( ( %s - %s ) ^ %s ) )' % (A, X, n, X, X, n)), w.s([], 'fveq2', '( %s -> ( %s ` z ) = ( %s ` %s ) )' % (A, g, g, X))], 'oveq12d',
                                                                             '( %s -> ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) = ( ( ( %s - %s ) ^ %s ) x. ( %s ` %s ) ) )' % (A, X, n, g, X, X, n, g, X))], 'eqeq12d',
               '( %s -> ( ( F ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) <-> ( F ` %s ) = ( ( ( %s - %s ) ^ %s ) x. ( %s ` %s ) ) ) )' % (A, X, n, g, X, X, X, n, g, X))


def CONC(X='P'):
    o = '( F holord %s )' % X
    return '( %s e. NN0 /\\ E. g %s )' % (o, PHI(X, o))


if __name__ == '__main__':
    # ---- holordex -------------------------------------------------------------------
    w = W('holordex', 'A holomorphic function with a local factorisation at P has a finite order of vanishing there, and the factorisation with the order as exponent.')
    A0 = '( ( %s /\\ P e. D ) /\\ %s )' % (HOL, EXFAC('P'))
    hp = w.s([], 'simpl', '( %s -> ( %s /\\ P e. D ) )' % (A0, HOL))
    hol = w.s([hp, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL)); pd = w.s([hp, w.inst('simpr')], 'syl', '( %s -> P e. D )' % A0)
    ex = w.s([], 'simpr', '( %s -> %s )' % (A0, EXFAC('P')))
    fcn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    fex = w.s([fcn], 'elexd', '( %s -> F e. _V )' % A0)
    dopn = w.s([hol, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
    ren1 = w.s([exga(w, 'n')], 'rexbii', '( %s <-> E. n e. NN0 E. a %s )' % (EXFAC('P'), PHI('P', 'n', 'a')))
    ren2 = w.s([w.s([phisubn(w, 'n', 'm')], 'exbidv', '( n = m -> ( E. a %s <-> E. a %s ) )' % (PHI('P', 'n', 'a'), PHI('P', 'm', 'a')))], 'cbvrexvw', '( E. n e. NN0 E. a %s <-> E. m e. NN0 E. a %s )' % (PHI('P', 'n', 'a'), PHI('P', 'm', 'a')))
    ren = w.s([ren1, ren2], 'bitri', '( %s <-> E. m e. NN0 E. a %s )' % (EXFAC('P'), PHI('P', 'm', 'a')))
    exa = w.s([ex, ren], 'sylib', '( %s -> E. m e. NN0 E. a %s )' % (A0, PHI('P', 'm', 'a')))
    B0 = '( ( %s /\\ m e. NN0 ) /\\ %s )' % (A0, PHI('P', 'm', 'a'))
    phi = w.s([], 'simpr', '( %s -> %s )' % (B0, PHI('P', 'm', 'a')))
    a0b = w.s([], 'simpll', '( %s -> %s )' % (B0, A0))
    nn0 = w.s([], 'simplr', '( %s -> m e. NN0 )' % B0)
    hga = w.s([phi, w.inst('simp1')], 'syl', '( %s -> %s )' % (B0, HOLG('a')))
    apne = w.s([phi, w.inst('simp2')], 'syl', '( %s -> ( a ` P ) =/= 0 )' % B0)
    fac = w.s([phi, w.inst('simp3')], 'syl', '( %s -> %s )' % (B0, FACE('D', 'a', 'm')))
    heq = w.s([w.s([w.s([a0b, fex], 'syl', '( %s -> F e. _V )' % B0), w.s([w.s([a0b, dopn], 'syl', '( %s -> D e. %s )' % (B0, TOP)), w.s([a0b, pd], 'syl', '( %s -> P e. D )' % B0)], 'jca', '( %s -> ( D e. %s /\\ P e. D ) )' % (B0, TOP))], 'jca', '( %s -> ( F e. _V /\\ ( D e. %s /\\ P e. D ) ) )' % (B0, TOP)),
               w.s([hga, apne], 'jca', '( %s -> ( %s /\\ ( a ` P ) =/= 0 ) )' % (B0, HOLG('a'))), w.s([nn0, fac], 'jca', '( %s -> ( m e. NN0 /\\ %s ) )' % (B0, FACE('D', 'a', 'm'))), w.inst('holordeq')], 'syl3anc',
              '( %s -> %s = m )' % (B0, ORD))
    ordn0 = w.s([heq, nn0], 'eqeltrd', '( %s -> %s e. NN0 )' % (B0, ORD))
    phio = w.s([w.s([w.s([heq], 'eqcomd', '( %s -> m = %s )' % (B0, ORD)), phisubn(w, 'm', ORD)], 'syl', '( %s -> ( %s <-> %s ) )' % (B0, PHI('P', 'm', 'a'), PHI('P', ORD, 'a'))), phi], 'mpbid', '( %s -> %s )' % (B0, PHI('P', ORD, 'a')))
    exg = w.s([w.s([], 'vex', 'a e. _V'), w.s([gsubx(w, 'a', ORD)], 'spcegv', '( a e. _V -> ( %s -> E. g %s ) )' % (PHI('P', ORD, 'a'), PHI('P', ORD)))], 'ax-mp', '( %s -> E. g %s )' % (PHI('P', ORD, 'a'), PHI('P', ORD)))
    conc = w.s([ordn0, w.s([phio, exg], 'syl', '( %s -> E. g %s )' % (B0, PHI('P', ORD)))], 'jca', '( %s -> %s )' % (B0, CONC()))
    e1 = w.s([w.s([conc], 'ex', '( ( %s /\\ m e. NN0 ) -> ( %s -> %s ) )' % (A0, PHI('P', 'm', 'a'), CONC()))], 'exlimdv', '( ( %s /\\ m e. NN0 ) -> ( E. a %s -> %s ) )' % (A0, PHI('P', 'm', 'a'), CONC()))
    w.qed([exa, w.s([e1], 'rexlimdva', '( %s -> ( E. m e. NN0 E. a %s -> %s ) )' % (A0, PHI('P', 'm', 'a'), CONC()))], 'mpd', '( %s -> %s )' % (A0, CONC()))
    run1(w)

    # ---- holordfin ------------------------------------------------------------------
    w = W('holordfin', 'The order of vanishing at a point where not all Taylor coefficients vanish is a natural number, and F factors with it as exponent.')
    hyp(w, '1', 'holordfin.c', CDEF)
    A0 = A0F
    hrm = w.s([], 'simpl', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    fx = w.s(['1'], 'holfacx', '( %s -> E. n e. NN0 %s )' % (A0, FACX('n')))
    strip = w.s([w.s([], 'simpr', '( %s -> E. g %s )' % (FACX('n'), PHI('P', 'n')))], 'reximi', '( E. n e. NN0 %s -> %s )' % (FACX('n'), EXFAC('P')))
    ex = w.s([fx, strip], 'syl', '( %s -> %s )' % (A0, EXFAC('P')))
    w.qed([w.s([d['hol'], d['pd']], 'jca', '( %s -> ( %s /\\ P e. D ) )' % (A0, HOL)), ex, w.inst('holordex')], 'syl2anc', '( %s -> %s )' % (A0, CONC()))
    run1(w)

    # ---- holordfinr -----------------------------------------------------------------
    w = W('holordfinr', 'At every point of a rectangle on which a holomorphic function is not identically zero, the order of vanishing is a natural number and the function factors with it as exponent.')
    A0 = '( %s /\\ X e. ( A crect B ) )' % ABNZ
    abnz = w.s([], 'simpl', '( %s -> %s )' % (A0, ABNZ))
    xin = w.s([], 'simpr', '( %s -> X e. ( A crect B ) )' % A0)
    d = abgeoctx(w, A0, w.s([abnz, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ABGEO)))
    xd = w.s([w.s([d['han'], w.inst('holnss')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0), xin], 'sseldd', '( %s -> X e. D )' % A0)
    ex = w.s([abnz, xin, w.inst('holnfac2')], 'syl2anc', '( %s -> %s )' % (A0, EXFAC('X')))
    w.qed([w.s([d['hol'], xd], 'jca', '( %s -> ( %s /\\ X e. D ) )' % (A0, HOL)), ex, w.inst('holordex')], 'syl2anc', '( %s -> %s )' % (A0, CONC('X')))
    run1(w)

    # ---- holord0 --------------------------------------------------------------------
    w = W('holord0', 'The order of vanishing is zero exactly when the function does not vanish at the point (at a point where not all Taylor coefficients vanish).')
    hyp(w, '1', 'holord0.c', CDEF)
    A0 = A0F
    hrm = w.s([], 'simpl', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    fin = w.s(['1'], 'holordfin', '( %s -> %s )' % (A0, CONC()))
    exg = w.s([fin, w.inst('simpr')], 'syl', '( %s -> E. g %s )' % (A0, PHI('P', ORD)))
    exa = w.s([exg, exga(w, ORD)], 'sylib', '( %s -> E. a %s )' % (A0, PHI('P', ORD, 'a')))
    # (->)
    A1 = '( %s /\\ %s = 0 )' % (A0, ORD)
    B1 = '( %s /\\ %s )' % (A1, PHI('P', ORD, 'a'))
    phi = w.s([], 'simpr', '( %s -> %s )' % (B1, PHI('P', ORD, 'a')))
    apne = w.s([phi, w.inst('simp2')], 'syl', '( %s -> ( a ` P ) =/= 0 )' % B1)
    fac = w.s([phi, w.inst('simp3')], 'syl', '( %s -> %s )' % (B1, FACE('D', 'a', ORD)))
    pd1 = w.s([d['pd']], 'ad2antrr', '( %s -> P e. D )' % B1)
    fp = w.s([facatp(w, 'a', ORD), fac, pd1], 'rspcdva', '( %s -> ( F ` P ) = ( ( ( P - P ) ^ %s ) x. ( a ` P ) ) )' % (B1, ORD))
    pp0 = w.s([w.s([d['pc']], 'ad2antrr', '( %s -> P e. CC )' % B1)], 'subidd', '( %s -> ( P - P ) = 0 )' % B1)
    o0 = w.s([w.s([], 'simpr', '( %s -> %s = 0 )' % (A1, ORD))], 'adantr', '( %s -> %s = 0 )' % (B1, ORD))
    e1 = w.s([w.s([pp0, o0], 'oveq12d', '( %s -> ( ( P - P ) ^ %s ) = ( 0 ^ 0 ) )' % (B1, ORD)), closed(w, B1, '0exp0e1', '( 0 ^ 0 ) = 1')], 'eqtrd', '( %s -> ( ( P - P ) ^ %s ) = 1 )' % (B1, ORD))
    apc = w.s([w.s([w.s([w.s([phi, w.inst('simp1')], 'syl', '( %s -> %s )' % (B1, HOLG('a'))), w.inst('simpl')], 'syl', '( %s -> a e. ( D -cn-> CC ) )' % B1), w.inst('cncff')], 'syl', '( %s -> a : D --> CC )' % B1), pd1], 'ffvelcdmd', '( %s -> ( a ` P ) e. CC )' % B1)
    fpa = w.s([fp, w.s([w.s([e1], 'oveq1d', '( %s -> ( ( ( P - P ) ^ %s ) x. ( a ` P ) ) = ( 1 x. ( a ` P ) ) )' % (B1, ORD)), w.s([apc], 'mullidd', '( %s -> ( 1 x. ( a ` P ) ) = ( a ` P ) )' % B1)], 'eqtrd', '( %s -> ( ( ( P - P ) ^ %s ) x. ( a ` P ) ) = ( a ` P ) )' % (B1, ORD))], 'eqtrd',
              '( %s -> ( F ` P ) = ( a ` P ) )' % B1)
    fpne = w.s([fpa, apne], 'eqnetrd', '( %s -> ( F ` P ) =/= 0 )' % B1)
    fwd = w.s([w.s([exa], 'adantr', '( %s -> E. a %s )' % (A1, PHI('P', ORD, 'a'))), fpne], 'exlimddv', '( %s -> ( F ` P ) =/= 0 )' % A1)
    # (<-)
    A2 = '( %s /\\ ( F ` P ) =/= 0 )' % A0
    A3 = '( %s /\\ z e. D )' % A2
    zc = w.s([w.s([d['dss']], 'ad2antrr', '( %s -> D C_ CC )' % A3), w.s([], 'simpr', '( %s -> z e. D )' % A3)], 'sseldd', '( %s -> z e. CC )' % A3)
    fz = w.s([w.s([d['ff']], 'ad2antrr', '( %s -> F : D --> CC )' % A3), w.s([], 'simpr', '( %s -> z e. D )' % A3)], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A3)
    zp = w.s([zc, w.s([d['pc']], 'ad2antrr', '( %s -> P e. CC )' % A3)], 'subcld', '( %s -> ( z - P ) e. CC )' % A3)
    e0 = w.s([w.s([w.s([w.s([zp], 'exp0d', '( %s -> ( ( z - P ) ^ 0 ) = 1 )' % A3)], 'oveq1d', '( %s -> ( ( ( z - P ) ^ 0 ) x. ( F ` z ) ) = ( 1 x. ( F ` z ) ) )' % A3), w.s([fz], 'mullidd', '( %s -> ( 1 x. ( F ` z ) ) = ( F ` z ) )' % A3)], 'eqtrd',
                  '( %s -> ( ( ( z - P ) ^ 0 ) x. ( F ` z ) ) = ( F ` z ) )' % A3)], 'eqcomd', '( %s -> ( F ` z ) = ( ( ( z - P ) ^ 0 ) x. ( F ` z ) ) )' % A3)
    ral0 = w.s([e0], 'ralrimiva', '( %s -> %s )' % (A2, FACE('D', 'F', '0')))
    def L2(st, f):
        return w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
    heq = w.s([w.s([L2(w.s([d['fcn']], 'elexd', '( %s -> F e. _V )' % A0), 'F e. _V'), w.s([L2(d['dopn'], 'D e. %s' % TOP), L2(d['pd'], 'P e. D')], 'jca', '( %s -> ( D e. %s /\\ P e. D ) )' % (A2, TOP))], 'jca', '( %s -> ( F e. _V /\\ ( D e. %s /\\ P e. D ) ) )' % (A2, TOP)),
               w.s([L2(d['hol'], HOL), w.s([], 'simpr', '( %s -> ( F ` P ) =/= 0 )' % A2)], 'jca', '( %s -> ( %s /\\ ( F ` P ) =/= 0 ) )' % (A2, HOL)), w.s([closed(w, A2, '0nn0', '0 e. NN0'), ral0], 'jca', '( %s -> ( 0 e. NN0 /\\ %s ) )' % (A2, FACE('D', 'F', '0'))), w.inst('holordeq')], 'syl3anc',
              '( %s -> %s = 0 )' % (A2, ORD))
    w.qed([w.s([fwd], 'ex', '( %s -> ( %s = 0 -> ( F ` P ) =/= 0 ) )' % (A0, ORD)), w.s([heq], 'ex', '( %s -> ( ( F ` P ) =/= 0 -> %s = 0 ) )' % (A0, ORD))], 'impbid', '( %s -> ( %s = 0 <-> ( F ` P ) =/= 0 ) )' % (A0, ORD))
    run1(w)

    # ---- holordge1 ------------------------------------------------------------------
    w = W('holordge1', 'The order of vanishing is at least one exactly when the function vanishes at the point (at a point where not all Taylor coefficients vanish).')
    hyp(w, '1', 'holordge1.c', CDEF)
    A0 = A0F
    fin = w.s(['1'], 'holordfin', '( %s -> %s )' % (A0, CONC()))
    on0 = w.s([fin, w.inst('simpl')], 'syl', '( %s -> %s e. NN0 )' % (A0, ORD))
    b1 = w.s([on0, w.s([w.s([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (ORD, ORD, ORD))], 'a1i', '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) ) )' % (A0, ORD, ORD, ORD))], 'baibd', '( ( %s /\\ %s e. NN0 ) -> ( %s e. NN <-> 1 <_ %s ) )' % (A0, ORD, ORD, ORD))], 'mpdan', '( %s -> ( %s e. NN <-> 1 <_ %s ) )' % (A0, ORD, ORD))
    b2 = w.s([on0, w.s([w.s([w.s([], 'elnnne0', '( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) )' % (ORD, ORD, ORD))], 'a1i', '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ %s =/= 0 ) ) )' % (A0, ORD, ORD, ORD))], 'baibd', '( ( %s /\\ %s e. NN0 ) -> ( %s e. NN <-> %s =/= 0 ) )' % (A0, ORD, ORD, ORD))], 'mpdan', '( %s -> ( %s e. NN <-> %s =/= 0 ) )' % (A0, ORD, ORD))
    b12 = w.s([b1, b2], 'bitr3d', '( %s -> ( 1 <_ %s <-> %s =/= 0 ) )' % (A0, ORD, ORD))
    o0 = w.s(['1'], 'holord0', '( %s -> ( %s = 0 <-> ( F ` P ) =/= 0 ) )' % (A0, ORD))
    nb1 = w.s([w.s([], 'df-ne', '( %s =/= 0 <-> -. %s = 0 )' % (ORD, ORD)), w.s([o0], 'notbid', '( %s -> ( -. %s = 0 <-> -. ( F ` P ) =/= 0 ) )' % (A0, ORD))], 'bitrid', '( %s -> ( %s =/= 0 <-> -. ( F ` P ) =/= 0 ) )' % (A0, ORD))
    nb2 = w.s([nb1, w.s([], 'nne', '( -. ( F ` P ) =/= 0 <-> ( F ` P ) = 0 )')], 'bitrdi', '( %s -> ( %s =/= 0 <-> ( F ` P ) = 0 ) )' % (A0, ORD))
    w.qed([b12, nb2], 'bitrd', '( %s -> ( 1 <_ %s <-> ( F ` P ) = 0 ) )' % (A0, ORD))
    run1(w)

    # ---- holordcf -------------------------------------------------------------------
    w = W('holordcf', 'The Taylor characterisation of the order of vanishing: the order is N exactly when the Taylor coefficients below N vanish and the N-th does not.')
    hyp(w, '1', 'holordcf.c', CDEF)
    A0 = '( %s /\\ N e. NN0 )' % A0F
    a0f = w.s([], 'simpl', '( %s -> %s )' % (A0, A0F))
    nn0 = w.s([], 'simpr', '( %s -> N e. NN0 )' % A0)
    hrm = w.s([a0f, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    tsub = w.s([w.s([w.s([], 'oveq2', '( n = N -> ( 0 ..^ n ) = ( 0 ..^ N ) )')], 'raleqdv', '( n = N -> ( %s <-> %s ) )' % (ZERN('n'), ZERN('N'))), w.s([w.s([], 'fveq2', '( n = N -> ( C ` n ) = ( C ` N ) )')], 'neeq1d', '( n = N -> ( ( C ` n ) =/= 0 <-> ( C ` N ) =/= 0 ) )')], 'anbi12d',
               '( n = N -> ( %s <-> %s ) )' % (TAY('n'), TAY('N')))
    # (->)
    A1 = '( %s /\\ %s = N )' % (A0, ORD)
    fx = w.s([w.s([a0f], 'adantr', '( %s -> %s )' % (A1, A0F)), w.s(['1'], 'holfacx', '( %s -> E. n e. NN0 %s )' % (A0F, FACX('n')))], 'syl', '( %s -> E. n e. NN0 %s )' % (A1, FACX('n')))
    B1 = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (A1, FACX('n'))
    fcx = w.s([], 'simpr', '( %s -> %s )' % (B1, FACX('n')))
    tay = w.s([fcx, w.inst('simpl')], 'syl', '( %s -> %s )' % (B1, TAY('n')))
    exg = w.s([fcx, w.inst('simpr')], 'syl', '( %s -> E. g %s )' % (B1, PHI('P', 'n')))
    exa = w.s([exg, exga(w, 'n')], 'sylib', '( %s -> E. a %s )' % (B1, PHI('P', 'n', 'a')))
    C1 = '( %s /\\ %s )' % (B1, PHI('P', 'n', 'a'))
    phi = w.s([], 'simpr', '( %s -> %s )' % (C1, PHI('P', 'n', 'a')))
    def L1(st, f):
        return w.s([st], 'ad4antr', '( %s -> %s )' % (C1, f))
    heq = w.s([w.s([L1(w.s([d['fcn']], 'elexd', '( %s -> F e. _V )' % A0), 'F e. _V'), w.s([L1(d['dopn'], 'D e. %s' % TOP), L1(d['pd'], 'P e. D')], 'jca', '( %s -> ( D e. %s /\\ P e. D ) )' % (C1, TOP))], 'jca', '( %s -> ( F e. _V /\\ ( D e. %s /\\ P e. D ) ) )' % (C1, TOP)),
               w.s([w.s([phi, w.inst('simp1')], 'syl', '( %s -> %s )' % (C1, HOLG('a'))), w.s([phi, w.inst('simp2')], 'syl', '( %s -> ( a ` P ) =/= 0 )' % C1)], 'jca', '( %s -> ( %s /\\ ( a ` P ) =/= 0 ) )' % (C1, HOLG('a'))),
               w.s([w.s([w.s([], 'simplr', '( %s -> n e. NN0 )' % B1)], 'adantr', '( %s -> n e. NN0 )' % C1), w.s([phi, w.inst('simp3')], 'syl', '( %s -> %s )' % (C1, FACE('D', 'a', 'n')))], 'jca', '( %s -> ( n e. NN0 /\\ %s ) )' % (C1, FACE('D', 'a', 'n'))), w.inst('holordeq')], 'syl3anc',
              '( %s -> %s = n )' % (C1, ORD))
    neqN = w.s([heq, w.s([w.s([], 'simpr', '( %s -> %s = N )' % (A1, ORD))], 'ad3antrrr', '( %s -> %s = N )' % (C1, ORD))], 'eqtr3d', '( %s -> n = N )' % C1)
    tayN = w.s([w.s([neqN, tsub], 'syl', '( %s -> ( %s <-> %s ) )' % (C1, TAY('n'), TAY('N'))), w.s([tay], 'adantr', '( %s -> %s )' % (C1, TAY('n')))], 'mpbid', '( %s -> %s )' % (C1, TAY('N')))
    t1 = w.s([exa, tayN], 'exlimddv', '( %s -> %s )' % (B1, TAY('N')))
    fwd = w.s([fx, w.s([w.s([t1], 'ex', '( ( %s /\\ n e. NN0 ) -> ( %s -> %s ) )' % (A1, FACX('n'), TAY('N')))], 'rexlimdva', '( %s -> ( E. n e. NN0 %s -> %s ) )' % (A1, FACX('n'), TAY('N')))], 'mpd', '( %s -> %s )' % (A1, TAY('N')))
    # (<-)
    A2 = '( %s /\\ %s )' % (A0, TAY('N'))
    zer = w.s([w.s([], 'simpr', '( %s -> %s )' % (A2, TAY('N'))), w.inst('simpl')], 'syl', '( %s -> %s )' % (A2, ZERN('N')))
    cne = w.s([w.s([], 'simpr', '( %s -> %s )' % (A2, TAY('N'))), w.inst('simpr')], 'syl', '( %s -> ( C ` N ) =/= 0 )' % A2)
    # case N = 0
    AZ = '( %s /\\ N = 0 )' % A2
    c0ne = w.s([w.s([w.s([], 'simpr', '( %s -> N = 0 )' % AZ)], 'fveq2d', '( %s -> ( C ` N ) = ( C ` 0 ) )' % AZ), w.s([cne], 'adantr', '( %s -> ( C ` N ) =/= 0 )' % AZ)], 'eqnetrrd', '( %s -> ( C ` 0 ) =/= 0 )' % AZ)
    hc0 = w.s([w.s([d['abih']], 'ad2antrr', '( %s -> ( %s /\\ %s /\\ %s ) )' % (AZ, AB, INTP, HOLO)), w.s(['1'], 'holc0', '( ( %s /\\ %s /\\ %s ) -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AB, INTP, HOLO, TPI))], 'syl', '( %s -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AZ, TPI))
    tfne = w.s([hc0, c0ne], 'eqnetrrd', '( %s -> ( %s x. ( F ` P ) ) =/= 0 )' % (AZ, TPI))
    tpic, tne = tpisteps(w, AZ)
    fp = w.s([w.s([d['ff']], 'ad2antrr', '( %s -> F : D --> CC )' % AZ), w.s([d['pd']], 'ad2antrr', '( %s -> P e. D )' % AZ)], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % AZ)
    fpne = w.s([w.s([tfne, w.s([tpic, fp, w.inst('mulne0b')], 'syl2anc', '( %s -> ( ( %s =/= 0 /\\ ( F ` P ) =/= 0 ) <-> ( %s x. ( F ` P ) ) =/= 0 ) )' % (AZ, TPI, TPI))], 'mpbird', '( %s -> ( %s =/= 0 /\\ ( F ` P ) =/= 0 ) )' % (AZ, TPI)), w.inst('simpr')], 'syl', '( %s -> ( F ` P ) =/= 0 )' % AZ)
    o0 = w.s([w.s([a0f], 'ad2antrr', '( %s -> %s )' % (AZ, A0F)), w.s(['1'], 'holord0', '( %s -> ( %s = 0 <-> ( F ` P ) =/= 0 ) )' % (A0F, ORD))], 'syl', '( %s -> ( %s = 0 <-> ( F ` P ) =/= 0 ) )' % (AZ, ORD))
    case2 = w.s([w.s([fpne, o0], 'mpbird', '( %s -> %s = 0 )' % (AZ, ORD)), w.s([], 'simpr', '( %s -> N = 0 )' % AZ)], 'eqtr4d', '( %s -> %s = N )' % (AZ, ORD))
    # case N e. NN
    AN = '( %s /\\ N e. NN )' % A2
    ctxn = w.s([w.s([hrm], 'ad2antrr', '( %s -> %s )' % (AN, HRM)), w.s([w.s([], 'simpr', '( %s -> N e. NN )' % AN), w.s([zer], 'adantr', '( %s -> %s )' % (AN, ZERN('N')))], 'jca', '( %s -> ( N e. NN /\\ %s ) )' % (AN, ZERN('N')))], 'jca', '( %s -> %s )' % (AN, CTXN('N')))
    fl = w.s([w.s([ctxn, w.s([cne], 'adantr', '( %s -> ( C ` N ) =/= 0 )' % AN)], 'jca', '( %s -> ( %s /\\ ( C ` N ) =/= 0 ) )' % (AN, CTXN('N'))), w.s(['1'], 'holfaclemx', '( ( %s /\\ ( C ` N ) =/= 0 ) -> E. g %s )' % (CTXN('N'), PHI('P', 'N')))], 'syl', '( %s -> E. g %s )' % (AN, PHI('P', 'N')))
    fla = w.s([fl, exga(w, 'N')], 'sylib', '( %s -> E. a %s )' % (AN, PHI('P', 'N', 'a')))
    CN = '( %s /\\ %s )' % (AN, PHI('P', 'N', 'a'))
    phi = w.s([], 'simpr', '( %s -> %s )' % (CN, PHI('P', 'N', 'a')))
    def LN(st, f):
        return w.s([st], 'ad3antrrr', '( %s -> %s )' % (CN, f))
    heqN = w.s([w.s([LN(w.s([d['fcn']], 'elexd', '( %s -> F e. _V )' % A0), 'F e. _V'), w.s([LN(d['dopn'], 'D e. %s' % TOP), LN(d['pd'], 'P e. D')], 'jca', '( %s -> ( D e. %s /\\ P e. D ) )' % (CN, TOP))], 'jca', '( %s -> ( F e. _V /\\ ( D e. %s /\\ P e. D ) ) )' % (CN, TOP)),
                w.s([w.s([phi, w.inst('simp1')], 'syl', '( %s -> %s )' % (CN, HOLG('a'))), w.s([phi, w.inst('simp2')], 'syl', '( %s -> ( a ` P ) =/= 0 )' % CN)], 'jca', '( %s -> ( %s /\\ ( a ` P ) =/= 0 ) )' % (CN, HOLG('a'))),
                w.s([LN(nn0, 'N e. NN0'), w.s([phi, w.inst('simp3')], 'syl', '( %s -> %s )' % (CN, FACE('D', 'a', 'N')))], 'jca', '( %s -> ( N e. NN0 /\\ %s ) )' % (CN, FACE('D', 'a', 'N'))), w.inst('holordeq')], 'syl3anc',
               '( %s -> %s = N )' % (CN, ORD))
    case1 = w.s([fla, heqN], 'exlimddv', '( %s -> %s = N )' % (AN, ORD))
    orx = w.s([w.s([nn0], 'adantr', '( %s -> N e. NN0 )' % A2), w.inst('elnn0')], 'sylib', '( %s -> ( N e. NN \\/ N = 0 ) )' % A2)
    bwd = w.s([case1, case2, orx], 'mpjaodan', '( %s -> %s = N )' % (A2, ORD))
    w.qed([w.s([fwd], 'ex', '( %s -> ( %s = N -> %s ) )' % (A0, ORD, TAY('N'))), w.s([bwd], 'ex', '( %s -> ( %s -> %s = N ) )' % (A0, TAY('N'), ORD))], 'impbid', '( %s -> ( %s = N <-> %s ) )' % (A0, ORD, TAY('N')))
    run1(w)
