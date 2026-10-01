"""Sortie C6 section B, part 1: the generic limit-from-a-bound lemma, the
interior lemma, and the quotient function's values and factorisation."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *

if __name__ == '__main__':
    # ---- limcbnd: a Lipschitz-type bound gives a limit --------------------------
    HYP = 'A. w e. X ( ( w =/= P /\\ ( abs ` ( w - P ) ) < S ) -> ( abs ` ( ( F ` w ) - L ) ) <_ ( K x. ( abs ` ( w - P ) ) ) )'
    A0 = '( ( F : X --> CC /\\ X C_ CC ) /\\ ( P e. CC /\\ L e. CC ) /\\ ( ( K e. RR /\\ 0 <_ K ) /\\ ( S e. RR+ /\\ %s ) ) )' % HYP
    w = W('limcbnd', 'A function whose distance from L near P is bounded by a constant times the distance to P has the limit L at P.')
    fx = w.s([], 'simp1', '( %s -> ( F : X --> CC /\\ X C_ CC ) )' % A0)
    ff = w.s([fx, w.inst('simpl')], 'syl', '( %s -> F : X --> CC )' % A0)
    xs = w.s([fx, w.inst('simpr')], 'syl', '( %s -> X C_ CC )' % A0)
    pl = w.s([], 'simp2', '( %s -> ( P e. CC /\\ L e. CC ) )' % A0)
    pc = w.s([pl, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    lc = w.s([pl, w.inst('simpr')], 'syl', '( %s -> L e. CC )' % A0)
    ks = w.s([], 'simp3', '( %s -> ( ( K e. RR /\\ 0 <_ K ) /\\ ( S e. RR+ /\\ %s ) ) )' % (A0, HYP))
    k0 = w.s([ks, w.inst('simpl')], 'syl', '( %s -> ( K e. RR /\\ 0 <_ K ) )' % A0)
    kr = w.s([k0, w.inst('simpl')], 'syl', '( %s -> K e. RR )' % A0)
    kge = w.s([k0, w.inst('simpr')], 'syl', '( %s -> 0 <_ K )' % A0)
    sh = w.s([ks, w.inst('simpr')], 'syl', '( %s -> ( S e. RR+ /\\ %s ) )' % (A0, HYP))
    srp = w.s([sh, w.inst('simpl')], 'syl', '( %s -> S e. RR+ )' % A0)
    hy = w.s([sh, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, HYP))
    EPS = 'A. z e. X ( ( z =/= P /\\ ( abs ` ( z - P ) ) < d ) -> ( abs ` ( ( F ` z ) - L ) ) < e )'
    bic = w.s([ff, xs, pc], 'ellimc3', '( %s -> ( L e. ( F limCC P ) <-> ( L e. CC /\\ A. e e. RR+ E. d e. RR+ %s ) ) )' % (A0, EPS))
    A1 = '( %s /\\ e e. RR+ )' % A0
    E1 = '( e / ( K + 1 ) )'
    SM = '( ( S x. %s ) / ( S + %s ) )' % (E1, E1)
    erp = w.s([], 'simpr', '( %s -> e e. RR+ )' % A1)
    kr1 = ad(w, kr, A1, 'K e. RR'); kge1 = ad(w, kge, A1, '0 <_ K'); srp1 = ad(w, srp, A1, 'S e. RR+')
    k1rp = w.s([kr1, kge1], 'ge0p1rpd', '( %s -> ( K + 1 ) e. RR+ )' % A1)
    e1rp = w.s([erp, k1rp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A1, E1))
    sm = w.s([srp1, e1rp, w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ S /\\ %s <_ %s ) ) )' % (A1, SM, SM, SM, E1))
    smrp = w.s([sm, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A1, SM))
    smle = w.s([sm, w.inst('simpr')], 'syl', '( %s -> ( %s <_ S /\\ %s <_ %s ) )' % (A1, SM, SM, E1))
    sms = w.s([smle, w.inst('simpl')], 'syl', '( %s -> %s <_ S )' % (A1, SM))
    sme = w.s([smle, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A1, SM, E1))
    A2 = '( %s /\\ z e. X )' % A1
    AZ = '( abs ` ( z - P ) )'
    CND = '( z =/= P /\\ %s < %s )' % (AZ, SM)
    A3 = '( %s /\\ %s )' % (A2, CND)
    zx = w.s([w.s([], 'simpr', '( %s -> z e. X )' % A2)], 'adantr', '( %s -> z e. X )' % A3)
    cnd = w.s([], 'simpr', '( %s -> %s )' % (A3, CND))
    zne = w.s([cnd, w.inst('simpl')], 'syl', '( %s -> z =/= P )' % A3)
    lt = w.s([cnd, w.inst('simpr')], 'syl', '( %s -> %s < %s )' % (A3, AZ, SM))
    def a3(st, f):
        return w.s([st], 'ad2antrr', '( %s -> %s )' % (A3, f))
    zc = w.s([w.s([xs], 'ad3antrrr', '( %s -> X C_ CC )' % A3), zx], 'sseldd', '( %s -> z e. CC )' % A3)
    pc3 = w.s([pc], 'ad3antrrr', '( %s -> P e. CC )' % A3)
    az = w.s([w.s([zc, pc3], 'subcld', '( %s -> ( z - P ) e. CC )' % A3)], 'abscld', '( %s -> %s e. RR )' % (A3, AZ))
    smr = w.s([a3(smrp, '%s e. RR+' % SM)], 'rpred', '( %s -> %s e. RR )' % (A3, SM))
    sr = w.s([w.s([srp], 'ad3antrrr', '( %s -> S e. RR+ )' % A3)], 'rpred', '( %s -> S e. RR )' % A3)
    lts = w.s([az, smr, sr, lt, a3(sms, '%s <_ S' % SM)], 'ltletrd', '( %s -> %s < S )' % (A3, AZ))
    # the hypothesis at z
    s1 = w.s([], 'neeq1', '( w = z -> ( w =/= P <-> z =/= P ) )')
    s2 = w.s([w.s([w.s([], 'oveq1', '( w = z -> ( w - P ) = ( z - P ) )')], 'fveq2d', '( w = z -> ( abs ` ( w - P ) ) = %s )' % AZ)], 'breq1d',
             '( w = z -> ( ( abs ` ( w - P ) ) < S <-> %s < S ) )' % AZ)
    s3 = w.s([s1, s2], 'anbi12d', '( w = z -> ( ( w =/= P /\\ ( abs ` ( w - P ) ) < S ) <-> ( z =/= P /\\ %s < S ) ) )' % AZ)
    s4 = w.s([w.s([w.s([], 'fveq2', '( w = z -> ( F ` w ) = ( F ` z ) )')], 'oveq1d', '( w = z -> ( ( F ` w ) - L ) = ( ( F ` z ) - L ) )')], 'fveq2d',
             '( w = z -> ( abs ` ( ( F ` w ) - L ) ) = ( abs ` ( ( F ` z ) - L ) ) )')
    s5 = w.s([w.s([w.s([], 'oveq1', '( w = z -> ( w - P ) = ( z - P ) )')], 'fveq2d', '( w = z -> ( abs ` ( w - P ) ) = %s )' % AZ)], 'oveq2d',
             '( w = z -> ( K x. ( abs ` ( w - P ) ) ) = ( K x. %s ) )' % AZ)
    s6 = w.s([s4, s5], 'breq12d', '( w = z -> ( ( abs ` ( ( F ` w ) - L ) ) <_ ( K x. ( abs ` ( w - P ) ) ) <-> ( abs ` ( ( F ` z ) - L ) ) <_ ( K x. %s ) ) )' % AZ)
    s7 = w.s([s3, s6], 'imbi12d', '( w = z -> ( ( ( w =/= P /\\ ( abs ` ( w - P ) ) < S ) -> ( abs ` ( ( F ` w ) - L ) ) <_ ( K x. ( abs ` ( w - P ) ) ) ) <-> ( ( z =/= P /\\ %s < S ) -> ( abs ` ( ( F ` z ) - L ) ) <_ ( K x. %s ) ) ) )' % (AZ, AZ))
    hz = w.s([s7, w.s([hy], 'ad3antrrr', '( %s -> %s )' % (A3, HYP)), zx], 'rspcdva', '( %s -> ( ( z =/= P /\\ %s < S ) -> ( abs ` ( ( F ` z ) - L ) ) <_ ( K x. %s ) ) )' % (A3, AZ, AZ))
    bnd = w.s([w.s([zne, lts], 'jca', '( %s -> ( z =/= P /\\ %s < S ) )' % (A3, AZ)), hz], 'mpd', '( %s -> ( abs ` ( ( F ` z ) - L ) ) <_ ( K x. %s ) )' % (A3, AZ))
    # K x. AZ <_ K x. E1 < e
    e1r = w.s([a3(e1rp, '%s e. RR+' % E1)], 'rpred', '( %s -> %s e. RR )' % (A3, E1))
    lte = w.s([az, smr, e1r, lt, a3(sme, '%s <_ %s' % (SM, E1))], 'ltletrd', '( %s -> %s < %s )' % (A3, AZ, E1))
    kr3 = w.s([kr], 'ad3antrrr', '( %s -> K e. RR )' % A3)
    kge3 = w.s([kge], 'ad3antrrr', '( %s -> 0 <_ K )' % A3)
    kle = w.s([w.s([az, e1r, w.s([kr3, kge3], 'jca', '( %s -> ( K e. RR /\\ 0 <_ K ) )' % A3)], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( K e. RR /\\ 0 <_ K ) ) )' % (A3, AZ, E1)),
              w.s([lte], 'ltled', '( %s -> %s <_ %s )' % (A3, AZ, E1)), w.inst('lemul2a')], 'syl2anc', '( %s -> ( K x. %s ) <_ ( K x. %s ) )' % (A3, AZ, E1))
    er3 = w.s([w.s([erp], 'ad2antrr', '( %s -> e e. RR+ )' % A3)], 'rpred', '( %s -> e e. RR )' % A3)
    erp3 = w.s([erp], 'ad2antrr', '( %s -> e e. RR+ )' % A3)
    k1rp3 = a3(k1rp, '( K + 1 ) e. RR+')
    k1r = w.s([k1rp3], 'rpred', '( %s -> ( K + 1 ) e. RR )' % A3)
    keq = w.s([w.s([w.s([kr3], 'recnd', '( %s -> K e. CC )' % A3), w.s([er3], 'recnd', '( %s -> e e. CC )' % A3), w.s([k1r], 'recnd', '( %s -> ( K + 1 ) e. CC )' % A3), w.s([k1rp3], 'rpne0d', '( %s -> ( K + 1 ) =/= 0 )' % A3)],
                   'divassd', '( %s -> ( ( K x. e ) / ( K + 1 ) ) = ( K x. %s ) )' % (A3, E1))], 'eqcomd', '( %s -> ( K x. %s ) = ( ( K x. e ) / ( K + 1 ) ) )' % (A3, E1))
    ltk = w.s([kr3], 'ltp1d', '( %s -> K < ( K + 1 ) )' % A3)
    ltm = w.s([ltk, w.s([kr3, k1r, erp3], 'ltmul1d', '( %s -> ( K < ( K + 1 ) <-> ( K x. e ) < ( ( K + 1 ) x. e ) ) )' % A3)], 'mpbid', '( %s -> ( K x. e ) < ( ( K + 1 ) x. e ) )' % A3)
    ltd = w.s([ltm, w.s([w.s([kr3, er3], 'remulcld', '( %s -> ( K x. e ) e. RR )' % A3), er3, w.s([k1r, w.s([k1rp3], 'rpgt0d', '( %s -> 0 < ( K + 1 ) )' % A3)], 'jca', '( %s -> ( ( K + 1 ) e. RR /\\ 0 < ( K + 1 ) ) )' % A3), w.inst('ltdivmul')], 'syl3anc',
                         '( %s -> ( ( ( K x. e ) / ( K + 1 ) ) < e <-> ( K x. e ) < ( ( K + 1 ) x. e ) ) )' % A3)], 'mpbird', '( %s -> ( ( K x. e ) / ( K + 1 ) ) < e )' % A3)
    lte2 = w.s([keq, ltd], 'eqbrtrd', '( %s -> ( K x. %s ) < e )' % (A3, E1))
    afl = w.s([w.s([w.s([w.s([ff], 'ad3antrrr', '( %s -> F : X --> CC )' % A3), zx], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A3), w.s([lc], 'ad3antrrr', '( %s -> L e. CC )' % A3)], 'subcld',
                   '( %s -> ( ( F ` z ) - L ) e. CC )' % A3)], 'abscld', '( %s -> ( abs ` ( ( F ` z ) - L ) ) e. RR )' % A3)
    fin = w.s([afl, w.s([kr3, az], 'remulcld', '( %s -> ( K x. %s ) e. RR )' % (A3, AZ)), er3, bnd,
               w.s([w.s([kr3, az], 'remulcld', '( %s -> ( K x. %s ) e. RR )' % (A3, AZ)), w.s([kr3, e1r], 'remulcld', '( %s -> ( K x. %s ) e. RR )' % (A3, E1)), er3, kle, lte2], 'lelttrd',
                   '( %s -> ( K x. %s ) < e )' % (A3, AZ))], 'lelttrd', '( %s -> ( abs ` ( ( F ` z ) - L ) ) < e )' % A3)
    imp_ = w.s([fin], 'ex', '( %s -> ( %s -> ( abs ` ( ( F ` z ) - L ) ) < e ) )' % (A2, CND))
    EPSM = 'A. z e. X ( %s -> ( abs ` ( ( F ` z ) - L ) ) < e )' % CND
    ral = w.s([imp_], 'ralrimiva', '( %s -> %s )' % (A1, EPSM))
    t1 = w.s([w.s([w.s([], 'breq2', '( d = %s -> ( %s < d <-> %s < %s ) )' % (SM, AZ, AZ, SM))], 'anbi2d', '( d = %s -> ( ( z =/= P /\\ %s < d ) <-> %s ) )' % (SM, AZ, CND))], 'imbi1d',
             '( d = %s -> ( ( ( z =/= P /\\ %s < d ) -> ( abs ` ( ( F ` z ) - L ) ) < e ) <-> ( %s -> ( abs ` ( ( F ` z ) - L ) ) < e ) ) )' % (SM, AZ, CND))
    t2 = w.s([t1], 'ralbidv', '( d = %s -> ( %s <-> %s ) )' % (SM, EPS, EPSM))
    ex = w.s([t2], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. d e. RR+ %s )' % (SM, EPSM, EPS))
    exd = w.s([smrp, ral, ex], 'syl2anc', '( %s -> E. d e. RR+ %s )' % (A1, EPS))
    all_ = w.s([exd], 'ralrimiva', '( %s -> A. e e. RR+ E. d e. RR+ %s )' % (A0, EPS))
    w.qed([w.s([lc, all_], 'jca', '( %s -> ( L e. CC /\\ A. e e. RR+ E. d e. RR+ %s ) )' % (A0, EPS)), bic], 'mpbird', '( %s -> L e. ( F limCC P ) )' % A0)
    run1(w)

    # ---- holdisint: a point within R of P is strictly interior --------------------
    from lin import linarith
    w = W('holdisint', 'A point closer to P than the distance R from P to the boundary frame is strictly interior to the rectangle.')
    RP = RE('P'); IP = IM('P'); RX = RE('X'); IX = IM('X')
    A0 = '( ( %s /\\ %s /\\ %s ) /\\ ( X e. CC /\\ ( abs ` ( X - P ) ) < R ) )' % (AB, INTP, RBDP)
    a3_ = w.s([], 'simpl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, RBDP))
    ab = w.s([a3_, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    it = w.s([a3_, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTP))
    rbd = w.s([a3_, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, RBDP))
    xr = w.s([], 'simpr', '( %s -> ( X e. CC /\\ ( abs ` ( X - P ) ) < R ) )' % A0)
    xc = w.s([xr, w.inst('simpl')], 'syl', '( %s -> X e. CC )' % A0)
    lt = w.s([xr, w.inst('simpr')], 'syl', '( %s -> ( abs ` ( X - P ) ) < R )' % A0)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    rr = w.s([rbd, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
    gaps = w.s([rbd, w.inst('simpr')], 'syl', '( %s -> ( ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) /\\ ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) ) )' % (A0, RP, RA, RB, RP, IP, IA, IB, IP))
    g1 = w.s([gaps, w.inst('simpll')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, RP, RA))
    g2 = w.s([gaps, w.inst('simplr')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, RB, RP))
    g3 = w.s([gaps, w.inst('simprl')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, IP, IA))
    g4 = w.s([gaps, w.inst('simprr')], 'syl', '( %s -> R <_ ( %s - %s ) )' % (A0, IB, IP))
    xp = w.s([xc, pc], 'subcld', '( %s -> ( X - P ) e. CC )' % A0)
    axp = w.s([xp], 'abscld', '( %s -> ( abs ` ( X - P ) ) e. RR )' % A0)
    rre = w.s([xp, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` ( X - P ) ) ) <_ ( abs ` ( X - P ) ) )' % A0)
    iim = w.s([xp, w.inst('absimle')], 'syl', '( %s -> ( abs ` ( Im ` ( X - P ) ) ) <_ ( abs ` ( X - P ) ) )' % A0)
    res = w.s([xc, pc, w.inst('resub')], 'syl2anc', '( %s -> ( Re ` ( X - P ) ) = ( %s - %s ) )' % (A0, RX, RP))
    ims = w.s([xc, pc, w.inst('imsub')], 'syl2anc', '( %s -> ( Im ` ( X - P ) ) = ( %s - %s ) )' % (A0, IX, IP))
    rxr = w.s([xc], 'recld', '( %s -> %s e. RR )' % (A0, RX)); ixr = w.s([xc], 'imcld', '( %s -> %s e. RR )' % (A0, IX))
    rpr = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP)); ipr = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
    rar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); iar = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA))
    rbr = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB)); ibr = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    dre = w.s([rxr, rpr], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RX, RP))
    dim = w.s([ixr, ipr], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IX, IP))
    ltre = w.s([w.s([dre], 'recnd', '( %s -> ( %s - %s ) e. CC )' % (A0, RX, RP))], 'abscld', '( %s -> ( abs ` ( %s - %s ) ) e. RR )' % (A0, RX, RP))
    are = ltre
    aim = w.s([w.s([dim], 'recnd', '( %s -> ( %s - %s ) e. CC )' % (A0, IX, IP))], 'abscld', '( %s -> ( abs ` ( %s - %s ) ) e. RR )' % (A0, IX, IP))
    lre = w.s([are, axp, rr, w.s([w.s([res], 'fveq2d', '( %s -> ( abs ` ( Re ` ( X - P ) ) ) = ( abs ` ( %s - %s ) ) )' % (A0, RX, RP)), rre], 'eqbrtrrd',
                                 '( %s -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( X - P ) ) )' % (A0, RX, RP)), lt], 'lelttrd', '( %s -> ( abs ` ( %s - %s ) ) < R )' % (A0, RX, RP))
    lim = w.s([aim, axp, rr, w.s([w.s([ims], 'fveq2d', '( %s -> ( abs ` ( Im ` ( X - P ) ) ) = ( abs ` ( %s - %s ) ) )' % (A0, IX, IP)), iim], 'eqbrtrrd',
                                 '( %s -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( X - P ) ) )' % (A0, IX, IP)), lt], 'lelttrd', '( %s -> ( abs ` ( %s - %s ) ) < R )' % (A0, IX, IP))
    bre = w.s([lre, w.s([dre, rr, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` ( %s - %s ) ) < R <-> ( -u R < ( %s - %s ) /\\ ( %s - %s ) < R ) ) )' % (A0, RX, RP, RX, RP, RX, RP))], 'mpbid',
              '( %s -> ( -u R < ( %s - %s ) /\\ ( %s - %s ) < R ) )' % (A0, RX, RP, RX, RP))
    bim = w.s([lim, w.s([dim, rr, w.inst('abslt')], 'syl2anc', '( %s -> ( ( abs ` ( %s - %s ) ) < R <-> ( -u R < ( %s - %s ) /\\ ( %s - %s ) < R ) ) )' % (A0, IX, IP, IX, IP, IX, IP))], 'mpbid',
              '( %s -> ( -u R < ( %s - %s ) /\\ ( %s - %s ) < R ) )' % (A0, IX, IP, IX, IP))
    bre1 = w.s([bre, w.inst('simpl')], 'syl', '( %s -> -u R < ( %s - %s ) )' % (A0, RX, RP))
    bre2 = w.s([bre, w.inst('simpr')], 'syl', '( %s -> ( %s - %s ) < R )' % (A0, RX, RP))
    bim1 = w.s([bim, w.inst('simpl')], 'syl', '( %s -> -u R < ( %s - %s ) )' % (A0, IX, IP))
    bim2 = w.s([bim, w.inst('simpr')], 'syl', '( %s -> ( %s - %s ) < R )' % (A0, IX, IP))
    leaves = {RX: rxr, RP: rpr, RA: rar, RB: rbr, IX: ixr, IP: ipr, IA: iar, IB: ibr, 'R': rr}
    l1 = linarith(w, A0, [g1, bre1], '%s < %s' % (RA, RX), leaves=leaves)
    l2 = linarith(w, A0, [g2, bre2], '%s < %s' % (RX, RB), leaves=leaves)
    l3 = linarith(w, A0, [g3, bim1], '%s < %s' % (IA, IX), leaves=leaves)
    l4 = linarith(w, A0, [g4, bim2], '%s < %s' % (IX, IB), leaves=leaves)
    w.qed([xc, w.s([w.s([l1, l2], 'jca', '( %s -> ( %s < %s /\\ %s < %s ) )' % (A0, RA, RX, RX, RB)), w.s([l3, l4], 'jca', '( %s -> ( %s < %s /\\ %s < %s ) )' % (A0, IA, IX, IX, IB))], 'jca',
                   '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RX, RX, RB, IA, IX, IX, IB))], 'jca',
          '( %s -> ( X e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) ) )' % (A0, RA, RX, RX, RB, IA, IX, IX, IB))
    run1(w)

    # ---- holqf: the quotient function maps D into CC --------------------------------
    w = W('holqf', 'The quotient function, the value of F over ( z - P ) ^ N extended at P by the N-th Taylor coefficient over 2 pi i, maps D into CC.')
    hyp(w, '1', 'holqf.c', CDEF)
    hyp(w, '2', 'holqf.q', QDEF)
    A0 = CTX
    d = ctxq(w)
    qp, cn, tpic, tne = qpcl(w, A0, d, '1')
    A1 = '( %s /\\ z e. D )' % A0
    A2 = '( %s /\\ -. z = P )' % A1
    zd = w.s([], 'simpr', '( %s -> z e. D )' % A1)
    zc = w.s([ad(w, d['dss'], A1, 'D C_ CC'), zd], 'sseldd', '( %s -> z e. CC )' % A1)
    fz = w.s([ad(w, d['ff'], A1, 'F : D --> CC'), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
    zp = w.s([zc, ad(w, d['pc'], A1, 'P e. CC')], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
    zpn = w.s([ad(w, zc, A2, 'z e. CC'), w.s([d['pc']], 'ad2antrr', '( %s -> P e. CC )' % A2), w.s([w.s([], 'simpr', '( %s -> -. z = P )' % A2)], 'neqned', '( %s -> z =/= P )' % A2)], 'subne0d',
              '( %s -> ( z - P ) =/= 0 )' % A2)
    zkn = w.s([ad(w, zp, A2, '( z - P ) e. CC'), zpn, w.s([w.s([d['hn']], 'ad2antrr', '( %s -> N e. NN0 )' % A2)], 'nn0zd', '( %s -> N e. ZZ )' % A2), w.inst('expne0i')], 'syl3anc',
              '( %s -> ( ( z - P ) ^ N ) =/= 0 )' % A2)
    zk = w.s([ad(w, zp, A2, '( z - P ) e. CC'), w.s([d['hn']], 'ad2antrr', '( %s -> N e. NN0 )' % A2)], 'expcld', '( %s -> ( ( z - P ) ^ N ) e. CC )' % A2)
    q2 = w.s([ad(w, fz, A2, '( F ` z ) e. CC'), zk, zkn], 'divcld', '( %s -> ( ( F ` z ) / ( ( z - P ) ^ N ) ) e. CC )' % A2)
    bcl = w.s([w.s([qp], 'ad2antrr', '( ( %s /\\ z = P ) -> %s e. CC )' % (A1, QP)), q2], 'ifclda', '( %s -> %s e. CC )' % (A1, QB('z')))
    w.qed([bcl, '2'], 'fmptd', '( %s -> Q : D --> CC )' % A0)
    run1(w, h=True)

    # ---- holqvp: the value at P ---------------------------------------------------
    w = W('holqvp', 'The value of the quotient function at the centre P is the N-th Taylor coefficient over 2 pi i.')
    hyp(w, '1', 'holqvp.c', CDEF)
    hyp(w, '2', 'holqvp.q', QDEF)
    A0 = CTX
    d = ctxq(w)
    qp, cn, tpic, tne = qpcl(w, A0, d, '1')
    sub = w.s([], 'iftrue', '( z = P -> %s = %s )' % (QB('z'), QP))
    fm = w.s([sub, '2'], 'fvmptg', '( ( P e. D /\\ %s e. _V ) -> ( Q ` P ) = %s )' % (QP, QP))
    w.qed([d['pd'], w.s([qp], 'elexd', '( %s -> %s e. _V )' % (A0, QP)), fm], 'syl2anc', '( %s -> ( Q ` P ) = %s )' % (A0, QP))
    run1(w, h=True)

    # ---- holqvz: the value off P ----------------------------------------------------
    w = W('holqvz', 'The value of the quotient function at a point X of D other than P is the value of F over ( X - P ) ^ N.')
    hyp(w, '1', 'holqvz.c', CDEF)
    hyp(w, '2', 'holqvz.q', QDEF)
    A0 = '( %s /\\ ( X e. D /\\ X =/= P ) )' % CTX
    QX = '( ( F ` X ) / ( ( X - P ) ^ N ) )'
    ctx = w.s([], 'simpl', '( %s -> %s )' % (A0, CTX))
    xd = w.s([w.s([], 'simpr', '( %s -> ( X e. D /\\ X =/= P ) )' % A0), w.inst('simpl')], 'syl', '( %s -> X e. D )' % A0)
    xne = w.s([w.s([], 'simpr', '( %s -> ( X e. D /\\ X =/= P ) )' % A0), w.inst('simpr')], 'syl', '( %s -> X =/= P )' % A0)
    s1 = w.s([], 'eqeq1', '( z = X -> ( z = P <-> X = P ) )')
    s2 = w.s([w.s([], 'fveq2', '( z = X -> ( F ` z ) = ( F ` X ) )'), w.s([w.s([], 'oveq1', '( z = X -> ( z - P ) = ( X - P ) )')], 'oveq1d', '( z = X -> ( ( z - P ) ^ N ) = ( ( X - P ) ^ N ) )')], 'oveq12d',
             '( z = X -> ( ( F ` z ) / ( ( z - P ) ^ N ) ) = %s )' % QX)
    s3 = w.s([s1, w.s([], 'eqidd', '( z = X -> %s = %s )' % (QP, QP)), s2], 'ifbieq12d', '( z = X -> %s = %s )' % (QB('z'), QB('X')))
    fm = w.s([s3, '2'], 'fvmptg', '( ( X e. D /\\ %s e. _V ) -> ( Q ` X ) = %s )' % (QB('X'), QB('X')))
    ex = w.s([w.s([], 'ifex', '%s e. _V' % QB('X'))], 'a1i', '( %s -> %s e. _V )' % (A0, QB('X')))
    v1 = w.s([xd, ex, fm], 'syl2anc', '( %s -> ( Q ` X ) = %s )' % (A0, QB('X')))
    v2 = w.s([w.s([xne], 'neneqd', '( %s -> -. X = P )' % A0)], 'iffalsed', '( %s -> %s = %s )' % (A0, QB('X'), QX))
    w.qed([v1, v2], 'eqtrd', '( %s -> ( Q ` X ) = %s )' % (A0, QX))
    run1(w, h=True)

    # ---- holqfac: the factorisation F = ( z - P ) ^ N x. Q --------------------------
    w = W('holqfac', 'The factorisation of F through the quotient function: at every point X of D, F X is ( X - P ) ^ N times Q X.')
    hyp(w, '1', 'holqfac.c', CDEF)
    hyp(w, '2', 'holqfac.q', QDEF)
    A0 = '( %s /\\ X e. D )' % CTX
    ctx = w.s([], 'simpl', '( %s -> %s )' % (A0, CTX))
    hrm = w.s([ctx, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    nz = w.s([ctx, w.inst('simpr')], 'syl', '( %s -> ( N e. NN /\\ %s ) )' % (A0, ZER))
    nn = w.s([nz, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    hn = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    zer = w.s([nz, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ZER))
    xd = w.s([], 'simpr', '( %s -> X e. D )' % A0)
    xc = w.s([d['dss'], xd], 'sseldd', '( %s -> X e. CC )' % A0)
    fx = w.s([d['ff'], xd], 'ffvelcdmd', '( %s -> ( F ` X ) e. CC )' % A0)
    # case X = P
    AE = '( %s /\\ X = P )' % A0
    z0 = w.s([nn, w.inst('lbfzo0')], 'sylibr', '( %s -> 0 e. ( 0 ..^ N ) )' % A0)
    c0z = w.s([w.s([], 'fveq2', '( i = 0 -> ( C ` i ) = ( C ` 0 ) )')], 'eqeq1d', '( i = 0 -> ( ( C ` i ) = 0 <-> ( C ` 0 ) = 0 ) )')
    c0 = w.s([c0z, zer, z0], 'rspcdva', '( %s -> ( C ` 0 ) = 0 )' % A0)
    hc0 = w.s(['1'], 'holc0', '( ( %s /\\ %s /\\ %s ) -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AB, INTP, HOLO, TPI))
    tf0 = w.s([w.s([d['abih'], hc0], 'syl', '( %s -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (A0, TPI)), c0], 'eqtr3d', '( %s -> ( %s x. ( F ` P ) ) = 0 )' % (A0, TPI))
    tpic, tne = tpisteps(w, A0)
    fp = w.s([d['ff'], d['pd']], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
    orx = w.s([w.s([tpic, fp, w.inst('mul0or')], 'syl2anc', '( %s -> ( ( %s x. ( F ` P ) ) = 0 <-> ( %s = 0 \\/ ( F ` P ) = 0 ) ) )' % (A0, TPI, TPI)), tf0], 'mpbid',
              '( %s -> ( %s = 0 \\/ ( F ` P ) = 0 ) )' % (A0, TPI))
    fp0 = w.s([w.s([w.s([tne], 'neneqd', '( %s -> -. %s = 0 )' % (A0, TPI)), w.inst('orel1')], 'syl', '( %s -> ( ( %s = 0 \\/ ( F ` P ) = 0 ) -> ( F ` P ) = 0 ) )' % (A0, TPI)), orx], 'mpd', '( %s -> ( F ` P ) = 0 )' % A0)
    xeqp = w.s([], 'simpr', '( %s -> X = P )' % AE)
    l1 = w.s([w.s([xeqp], 'fveq2d', '( %s -> ( F ` X ) = ( F ` P ) )' % AE), ad(w, fp0, AE, '( F ` P ) = 0')], 'eqtrd', '( %s -> ( F ` X ) = 0 )' % AE)
    xpp = w.s([w.s([xeqp], 'oveq1d', '( %s -> ( X - P ) = ( P - P ) )' % AE), w.s([ad(w, d['pc'], AE, 'P e. CC')], 'subidd', '( %s -> ( P - P ) = 0 )' % AE)], 'eqtrd', '( %s -> ( X - P ) = 0 )' % AE)
    zp0 = w.s([w.s([xpp], 'oveq1d', '( %s -> ( ( X - P ) ^ N ) = ( 0 ^ N ) )' % AE), w.s([ad(w, nn, AE, 'N e. NN'), w.inst('0exp')], 'syl', '( %s -> ( 0 ^ N ) = 0 )' % AE)], 'eqtrd', '( %s -> ( ( X - P ) ^ N ) = 0 )' % AE)
    qf0 = w.s(['1', '2'], 'holqf', '( %s -> Q : D --> CC )' % CTX)
    qx = w.s([w.s([ctx, qf0], 'syl', '( %s -> Q : D --> CC )' % A0), xd], 'ffvelcdmd', '( %s -> ( Q ` X ) e. CC )' % A0)
    r1 = w.s([w.s([zp0], 'oveq1d', '( %s -> ( ( ( X - P ) ^ N ) x. ( Q ` X ) ) = ( 0 x. ( Q ` X ) ) )' % AE), w.s([ad(w, qx, AE, '( Q ` X ) e. CC')], 'mul02d', '( %s -> ( 0 x. ( Q ` X ) ) = 0 )' % AE)], 'eqtrd',
             '( %s -> ( ( ( X - P ) ^ N ) x. ( Q ` X ) ) = 0 )' % AE)
    case1 = w.s([l1, r1], 'eqtr4d', '( %s -> ( F ` X ) = ( ( ( X - P ) ^ N ) x. ( Q ` X ) ) )' % AE)
    # case X =/= P
    AN = '( %s /\\ X =/= P )' % A0
    xne = w.s([], 'simpr', '( %s -> X =/= P )' % AN)
    qv0 = w.s(['1', '2'], 'holqvz', '( ( %s /\\ ( X e. D /\\ X =/= P ) ) -> ( Q ` X ) = ( ( F ` X ) / ( ( X - P ) ^ N ) ) )' % CTX)
    qv = w.s([w.s([ad(w, ctx, AN, CTX), w.s([ad(w, xd, AN, 'X e. D'), xne], 'jca', '( %s -> ( X e. D /\\ X =/= P ) )' % AN)], 'jca', '( %s -> ( %s /\\ ( X e. D /\\ X =/= P ) ) )' % (AN, CTX)), qv0], 'syl',
             '( %s -> ( Q ` X ) = ( ( F ` X ) / ( ( X - P ) ^ N ) ) )' % AN)
    xp = w.s([ad(w, xc, AN, 'X e. CC'), ad(w, d['pc'], AN, 'P e. CC')], 'subcld', '( %s -> ( X - P ) e. CC )' % AN)
    xpn = w.s([ad(w, xc, AN, 'X e. CC'), ad(w, d['pc'], AN, 'P e. CC'), xne], 'subne0d', '( %s -> ( X - P ) =/= 0 )' % AN)
    xk = w.s([xp, ad(w, hn, AN, 'N e. NN0')], 'expcld', '( %s -> ( ( X - P ) ^ N ) e. CC )' % AN)
    xkn = w.s([xp, xpn, w.s([ad(w, hn, AN, 'N e. NN0')], 'nn0zd', '( %s -> N e. ZZ )' % AN), w.inst('expne0i')], 'syl3anc', '( %s -> ( ( X - P ) ^ N ) =/= 0 )' % AN)
    case2 = w.s([w.s([w.s([qv], 'oveq2d', '( %s -> ( ( ( X - P ) ^ N ) x. ( Q ` X ) ) = ( ( ( X - P ) ^ N ) x. ( ( F ` X ) / ( ( X - P ) ^ N ) ) ) )' % AN),
                      w.s([ad(w, fx, AN, '( F ` X ) e. CC'), xk, xkn], 'divcan2d', '( %s -> ( ( ( X - P ) ^ N ) x. ( ( F ` X ) / ( ( X - P ) ^ N ) ) ) = ( F ` X ) )' % AN)], 'eqtrd',
                     '( %s -> ( ( ( X - P ) ^ N ) x. ( Q ` X ) ) = ( F ` X ) )' % AN)], 'eqcomd', '( %s -> ( F ` X ) = ( ( ( X - P ) ^ N ) x. ( Q ` X ) ) )' % AN)
    w.qed([case1, case2], 'pm2.61dane', '( %s -> ( F ` X ) = ( ( ( X - P ) ^ N ) x. ( Q ` X ) ) )' % A0)
    run1(w, h=True)
