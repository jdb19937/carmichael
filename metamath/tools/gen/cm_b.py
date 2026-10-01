"""Sortie CM: the swap of the t- and u-integrals (cmfub).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_b.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *

only = sys.argv[1:]

MX = 'if ( p <_ q , q , p )'
LG = '( ( log ` Z ) - ( log ` %s ) )' % MX
PHI = '( p <_ u /\\ q <_ u )'
FG = '( F x. ( * ` G ) )'


def dsum(X):
    return 'sum_ p e. P sum_ q e. P %s' % X


def divdist(w, C, pf, xcc, X, une, ucc):
    """( C -> ( dsum(if(PHI,X,0)) / u ) = dsum(if(PHI,( X / u ),0)) ); xcc proves X e. CC under ( ( C /\\ p e. P ) /\\ q e. P )"""
    Cp = '( %s /\\ p e. P )' % C
    Cpq = '( %s /\\ q e. P )' % Cp
    IF = 'if ( %s , %s , 0 )' % (PHI, X)
    IFU = 'if ( %s , ( %s / u ) , 0 )' % (PHI, X)
    ifc = D(w, Cpq, 'ifcld', [xcc, a1(w, Cpq, '0cn', '0 e. CC')], '%s e. CC' % IF)
    inner = D(w, Cp, 'fsumcl', [lift(w, pf, Cp), ifc], 'sum_ q e. P %s e. CC' % IF)
    o1 = D(w, C, 'fsumdivc', [pf, lift(w, ucc, C) if False else ucc, inner, une], '( %s / u ) = sum_ p e. P ( sum_ q e. P %s / u )' % (dsum(IF), IF))
    o2 = D(w, Cp, 'fsumdivc', [lift(w, pf, Cp), lift(w, ucc, Cp), ifc, lift(w, une, Cp)], '( sum_ q e. P %s / u ) = sum_ q e. P ( %s / u )' % (IF, IF))
    ov = a1(w, Cpq, 'ovif', '( %s / u ) = if ( %s , ( %s / u ) , ( 0 / u ) )' % (IF, PHI, X))
    z = D(w, Cpq, 'div0d', [lift(w, ucc, Cpq), lift(w, une, Cpq)], '( 0 / u ) = 0')
    ie = D(w, Cpq, 'ifeq2d', [z], 'if ( %s , ( %s / u ) , ( 0 / u ) ) = %s' % (PHI, X, IFU))
    t3 = D(w, Cpq, 'eqtrd', [ov, ie], '( %s / u ) = %s' % (IF, IFU))
    s3 = D(w, Cp, 'sumeq2dv', [t3], 'sum_ q e. P ( %s / u ) = sum_ q e. P %s' % (IF, IFU))
    s2 = D(w, Cp, 'eqtrd', [o2, s3], '( sum_ q e. P %s / u ) = sum_ q e. P %s' % (IF, IFU))
    s1 = D(w, C, 'sumeq2dv', [s2], 'sum_ p e. P ( sum_ q e. P %s / u ) = %s' % (IF, dsum(IFU)))
    return D(w, C, 'eqtrd', [o1, s1], '( %s / u ) = %s' % (dsum(IF), dsum(IFU)))


def gen_fub():
    w = W('cmfub', 'The swap of the ` t ` - and ` u ` -integrals of a step Dirichlet polynomial ` D ( t , u ) = sum_ p if ( p <_ u , F , 0 ) ` against ` dt du / u ` : both iterated integrals are ` sum_ p sum_ q ( S. A F x. * G ) ( log Z - log max ( p , q ) ) ` ( ~ cmsqx , ~ cmuint , ~ cmitgif , ~ itgfsum ; Lean ` integral_integral_swap ` ).')
    h1, h2, h3, h4, h5, h6 = ehyps(w, 'cmfub')
    A = 'ph'; d = mk(w, A)
    yp = d('simp1d', [h1], 'Y e. RR+'); zr = d('simp2d', [h1], 'Z e. RR')
    yr = d('rpred', [yp], 'Y e. RR'); yx = d('rexrd', [yr], 'Y e. RR*'); zx = d('rexrd', [zr], 'Z e. RR*')
    pf = d('simpld', [h2], 'P e. Fin')
    YZ = '( Y (,) Z )'
    DS = 'sum_ p e. P if ( p <_ u , F , 0 )'
    AD = ABS2(DS)

    def uprops(C):
        """( C -> u e. CC ), ( C -> u =/= 0 ) for u e. ( Y (,) Z ) a conjunct of C"""
        c = mk(w, C)
        uy = proj(w, C, 'u e. %s' % YZ)
        g = c('mpbid', [uy, c('syl2anc', [lift(w, yx, C), lift(w, zx, C), w.inst('elioo2')], '( u e. %s <-> ( u e. RR /\\ Y < u /\\ u < Z ) )' % YZ)], '( u e. RR /\\ Y < u /\\ u < Z )')
        ur = c('simp1d', [g], 'u e. RR')
        up = c('lttrd', [a1(w, C, '0re', '0 e. RR'), lift(w, yr, C), ur, c('rpgt0d', [lift(w, yp, C)], '0 < Y'), c('simp2d', [g], 'Y < u')], '0 < u')
        return c('recnd', [ur], 'u e. CC'), c('gt0ne0d', [up], 'u =/= 0')

    def gcc(C):
        """( ( ( C /\\ p e. P ) /\\ q e. P ) -> G e. CC ) for t e. A a conjunct of C"""
        Cq = '( %s /\\ q e. P )' % C
        f = rean(w, h4, '( %s /\\ ( p e. P /\\ t e. A ) )' % A) if False else None
        # A. p e. P F e. CC under ( C )
        Cp = '( %s /\\ p e. P )' % C
        fc = rean(w, h4, Cp)
        ral = w.s([fc], 'ralrimiva', '( %s -> A. p e. P F e. CC )' % C)
        e1 = w.s([h5], 'eleq1d', '( p = q -> ( F e. CC <-> G e. CC ) )')
        rs = w.s([e1], 'rspcv', '( q e. P -> ( A. p e. P F e. CC -> G e. CC ) )')
        g1 = w.s([w.s([], 'simpr', '( %s -> q e. P )' % Cq), lift(w, ral, Cq), rs], 'sylc', '( %s -> G e. CC )' % Cq)
        Cpq = '( %s /\\ q e. P )' % Cp
        return rean(w, g1, Cpq), lift(w, fc, Cpq)

    # ---- part 1: t fixed, the u-integral ----
    At = '( ph /\\ t e. A )'
    Atu = '( %s /\\ u e. %s )' % (At, YZ)
    ucc1, une1 = uprops(Atu)
    fcc1 = rean(w, h4, '( %s /\\ p e. P )' % Atu)
    sq1 = w.s([lift(w, pf, Atu), fcc1, h5], 'cmsqx', '( %s -> %s = %s )' % (Atu, AD, dsum('if ( %s , %s , 0 )' % (PHI, FG))))
    g1, f1 = gcc(Atu)
    Atupq = '( ( %s /\\ p e. P ) /\\ q e. P )' % Atu
    fg1 = D(w, Atupq, 'mulcld', [f1, D(w, Atupq, 'cjcld', [g1], '( * ` G ) e. CC')], '%s e. CC' % FG)
    dd1 = divdist(w, Atu, lift(w, pf, Atu), fg1, FG, une1, ucc1)
    q1 = D(w, Atu, 'oveq1d', [sq1], '( %s / u ) = ( %s / u )' % (AD, dsum('if ( %s , %s , 0 )' % (PHI, FG))))
    e1 = D(w, Atu, 'eqtrd', [q1, dd1], '( %s / u ) = %s' % (AD, dsum('if ( %s , ( %s / u ) , 0 )' % (PHI, FG))))
    # cmuint at K := FG under At
    Atpq = '( %s /\\ ( p e. P /\\ q e. P ) )' % At
    g1b, f1b = gcc(At)
    fgk = rean(w, D(w, '( ( %s /\\ p e. P ) /\\ q e. P )' % At, 'mulcld', [f1b, D(w, '( ( %s /\\ p e. P ) /\\ q e. P )' % At, 'cjcld', [g1b], '( * ` G ) e. CC')], '%s e. CC' % FG), Atpq)
    UIF = dsum('if ( %s , ( %s / u ) , 0 )' % (PHI, FG))
    cu1 = w.s([lift(w, h1, At), lift(w, h2, At), fgk], 'cmuint',
              '( %s -> ( ( u e. %s |-> %s ) e. L^1 /\\ S. %s %s _d u = %s ) )' % (At, YZ, UIF, YZ, UIF, dsum('( %s x. %s )' % (FG, LG))))
    at = mk(w, At)
    mq1 = at('mpteq2dva', [e1], '( u e. %s |-> ( %s / u ) ) = ( u e. %s |-> %s )' % (YZ, AD, YZ, UIF))
    ibu = at('eqeltrd', [mq1, at('simpld', [cu1], '( u e. %s |-> %s ) e. L^1' % (YZ, UIF))], '( u e. %s |-> ( %s / u ) ) e. L^1' % (YZ, AD))
    IU = 'S. %s ( %s / u ) _d u' % (YZ, AD)
    iu1 = at('eqtrd', [at('itgeq2dv', [e1], '%s = S. %s %s _d u' % (IU, YZ, UIF)), at('simprd', [cu1], 'S. %s %s _d u = %s' % (YZ, UIF, dsum('( %s x. %s )' % (FG, LG))))],
             '%s = %s' % (IU, dsum('( %s x. %s )' % (FG, LG))))
    # ---- part 2: the t-integral of the closed form ----
    ATP = '( ( ph /\\ p e. P ) /\\ q e. P )'
    atp = mk(w, ATP)
    # LG e. CC under ATP (p, q e. ( Y , Z ] gives max > 0)
    def lgc(C):
        c = mk(w, C)
        outs = {}
        for v in 'pq':
            vp = proj(w, C, '%s e. P' % v)
            vin = c('sseldd', [lift(w, d('simprd', [h2], 'P C_ ( Y (,] Z )'), C), vp], '%s e. ( Y (,] Z )' % v)
            g = c('mpbid', [vin, c('syl2anc', [lift(w, yx, C), lift(w, zr, C), w.inst('elioc2')], '( %s e. ( Y (,] Z ) <-> ( %s e. RR /\\ Y < %s /\\ %s <_ Z ) )' % (v, v, v, v))],
                  '( %s e. RR /\\ Y < %s /\\ %s <_ Z )' % (v, v, v))
            outs[v] = (c('simp1d', [g], '%s e. RR' % v), c('simp2d', [g], 'Y < %s' % v))
        mr = c('ifcld', [outs['q'][0], outs['p'][0]], '%s e. RR' % MX)
        pm = c('syl2anc', [outs['p'][0], outs['q'][0], w.inst('max1')], 'p <_ %s' % MX)
        m0 = c('lttrd', [a1(w, C, '0re', '0 e. RR'), lift(w, yr, C), mr, c('rpgt0d', [lift(w, yp, C)], '0 < Y'), c('ltletrd', [lift(w, yr, C), outs['p'][0], mr, outs['p'][1], pm], 'Y < %s' % MX)], '0 < %s' % MX)
        lgm = c('relogcld', [c('elrpd', [mr, m0], '%s e. RR+' % MX)], '( log ` %s ) e. RR' % MX)
        lgz0 = c('resubcld', [c('relogcld', [c('elrpd', [lift(w, zr, C), c('lttrd' if False else 'ltletrd', [a1(w, C, '0re', '0 e. RR'), mr, lift(w, zr, C), m0,
                                                                                                         c('mpbird', [c('jca', [c('simp3d', [c('mpbid', [c('sseldd', [lift(w, d('simprd', [h2], 'P C_ ( Y (,] Z )'), C), proj(w, C, 'p e. P')], 'p e. ( Y (,] Z )'), c('syl2anc', [lift(w, yx, C), lift(w, zr, C), w.inst('elioc2')], '( p e. ( Y (,] Z ) <-> ( p e. RR /\\ Y < p /\\ p <_ Z ) )')], '( p e. RR /\\ Y < p /\\ p <_ Z )')], 'p <_ Z'),
                                                                                                                              c('simp3d', [c('mpbid', [c('sseldd', [lift(w, d('simprd', [h2], 'P C_ ( Y (,] Z )'), C), proj(w, C, 'q e. P')], 'q e. ( Y (,] Z )'), c('syl2anc', [lift(w, yx, C), lift(w, zr, C), w.inst('elioc2')], '( q e. ( Y (,] Z ) <-> ( q e. RR /\\ Y < q /\\ q <_ Z ) )')], '( q e. RR /\\ Y < q /\\ q <_ Z )')], 'q <_ Z')],
                                                                                                                             '( p <_ Z /\\ q <_ Z )'),
                                                                                                                      c('syl3anc', [outs['p'][0], outs['q'][0], lift(w, zr, C), w.inst('maxle')], '( %s <_ Z <-> ( p <_ Z /\\ q <_ Z ) )' % MX)], '%s <_ Z' % MX)], '0 < Z')], 'Z e. RR+')], '( log ` Z ) e. RR'), lgm], '%s e. RR' % LG)
        return c('recnd', [lgz0], '%s e. CC' % LG)
    lgcc = lgc(ATP)
    # ( t e. A |-> ( LG x. FG ) ) e. L^1 and its integral
    h6r = rean(w, h6, ATP)
    fgt = rean(w, fgk, '( %s /\\ t e. A )' % ATP) if False else None
    ATPt = '( %s /\\ t e. A )' % ATP
    fgt = rean(w, fgk, ATPt)
    ibl_lf = atp('iblmulc2', [lgcc, fgt, h6r], '( t e. A |-> ( %s x. %s ) ) e. L^1' % (LG, FG))
    AP = '( ph /\\ p e. P )'
    ap = mk(w, AP)
    Ci = '( %s /\\ ( t e. A /\\ q e. P ) )' % AP
    lfc = rean(w, D(w, ATPt, 'mulcld', [lift(w, lgcc, ATPt), fgt], '( %s x. %s ) e. CC' % (LG, FG)), Ci)
    SQ2 = 'sum_ q e. P ( %s x. %s )' % (LG, FG)
    fi = ap('itgfsum', [lift(w, h3, AP), lift(w, pf, AP), lfc, ibl_lf], '( ( t e. A |-> %s ) e. L^1 /\\ S. A %s _d t = sum_ q e. P S. A ( %s x. %s ) _d t )' % (SQ2, SQ2, LG, FG))
    Co = '( ph /\\ ( t e. A /\\ p e. P ) )'
    sq2c = D(w, Co, 'fsumcl', [lift(w, pf, Co), rean(w, lfc, '( %s /\\ q e. P )' % Co)], '%s e. CC' % SQ2)
    fo = d('itgfsum', [h3, pf, sq2c, ap('simpld', [fi], '( t e. A |-> %s ) e. L^1' % SQ2)],
           '( ( t e. A |-> sum_ p e. P %s ) e. L^1 /\\ S. A sum_ p e. P %s _d t = sum_ p e. P S. A %s _d t )' % (SQ2, SQ2, SQ2))
    ITFG = 'S. A %s _d t' % FG
    im = atp('itgmulc2', [lgcc, fgt, h6r], '( %s x. %s ) = S. A ( %s x. %s ) _d t' % (LG, ITFG, LG, FG))
    si = ap('sumeq2dv', [atp('eqcomd', [im], 'S. A ( %s x. %s ) _d t = ( %s x. %s )' % (LG, FG, LG, ITFG))],
            'sum_ q e. P S. A ( %s x. %s ) _d t = sum_ q e. P ( %s x. %s )' % (LG, FG, LG, ITFG))
    so = d('sumeq2dv', [ap('eqtrd', [ap('simprd', [fi], 'S. A %s _d t = sum_ q e. P S. A ( %s x. %s ) _d t' % (SQ2, LG, FG)), si], 'S. A %s _d t = sum_ q e. P ( %s x. %s )' % (SQ2, LG, ITFG))],
           'sum_ p e. P S. A %s _d t = %s' % (SQ2, dsum('( %s x. %s )' % (LG, ITFG))))
    # I(t) = sum_p sum_q ( LG x. FG ) on A
    ATpq = '( ( %s /\\ p e. P ) /\\ q e. P )' % At
    cm = D(w, ATpq, 'mulcomd', [rean(w, fgk, ATpq), rean(w, lgcc, ATpq)], '( %s x. %s ) = ( %s x. %s )' % (FG, LG, LG, FG))
    cmi = D(w, '( %s /\\ p e. P )' % At, 'sumeq2dv', [cm], 'sum_ q e. P ( %s x. %s ) = %s' % (FG, LG, SQ2))
    cmo = at('sumeq2dv', [cmi], '%s = sum_ p e. P %s' % (dsum('( %s x. %s )' % (FG, LG)), SQ2))
    it_eq = at('eqtrd', [iu1, cmo], '%s = sum_ p e. P %s' % (IU, SQ2))
    mt = d('mpteq2dva', [it_eq], '( t e. A |-> %s ) = ( t e. A |-> sum_ p e. P %s )' % (IU, SQ2))
    ibl_t = d('eqeltrd', [mt, d('simpld', [fo], '( t e. A |-> sum_ p e. P %s ) e. L^1' % SQ2)], '( t e. A |-> %s ) e. L^1' % IU)
    LHS = 'S. A %s _d t' % IU
    lhs = chain(w, A, [LHS, 'S. A sum_ p e. P %s _d t' % SQ2, 'sum_ p e. P S. A %s _d t' % SQ2, dsum('( %s x. %s )' % (LG, ITFG))],
                [d('itgeq2dv', [it_eq], '%s = S. A sum_ p e. P %s _d t' % (LHS, SQ2)), d('simprd', [fo], 'S. A sum_ p e. P %s _d t = sum_ p e. P S. A %s _d t' % (SQ2, SQ2)), so])
    # ---- part 3: u fixed, the t-integral ----
    Au = '( ph /\\ u e. %s )' % YZ
    au = mk(w, Au)
    Aut = '( %s /\\ t e. A )' % Au
    sq3 = w.s([lift(w, pf, Aut), rean(w, h4, '( %s /\\ p e. P )' % Aut), h5], 'cmsqx', '( %s -> %s = %s )' % (Aut, AD, dsum('if ( %s , %s , 0 )' % (PHI, FG))))
    IFG = 'if ( %s , %s , 0 )' % (PHI, FG)
    Aup = '( %s /\\ p e. P )' % Au
    Aupq = '( %s /\\ q e. P )' % Aup
    # per (p, q): cmitgif at ps := PHI
    fgt3 = rean(w, fgk, '( %s /\\ t e. A )' % Aupq)
    ig = w.s([rean(w, h6, Aupq), fgt3], 'cmitgif', '( %s -> ( ( t e. A |-> %s ) e. L^1 /\\ S. A %s _d t = if ( %s , %s , 0 ) ) )' % (Aupq, IFG, IFG, PHI, ITFG))
    C3i = '( %s /\\ ( t e. A /\\ q e. P ) )' % Aup
    ifc3 = rean(w, D(w, '( %s /\\ t e. A )' % Aupq, 'ifcld', [fgt3, a1(w, '( %s /\\ t e. A )' % Aupq, '0cn', '0 e. CC')], '%s e. CC' % IFG), C3i)
    SQ3 = 'sum_ q e. P %s' % IFG
    fi3 = D(w, Aup, 'itgfsum', [lift(w, h3, Aup), lift(w, pf, Aup), ifc3, D(w, Aupq, 'simpld', [ig], '( t e. A |-> %s ) e. L^1' % IFG)],
            '( ( t e. A |-> %s ) e. L^1 /\\ S. A %s _d t = sum_ q e. P S. A %s _d t )' % (SQ3, SQ3, IFG))
    C3o = '( %s /\\ ( t e. A /\\ p e. P ) )' % Au
    sq3c = D(w, C3o, 'fsumcl', [lift(w, pf, C3o), rean(w, ifc3, '( %s /\\ q e. P )' % C3o)], '%s e. CC' % SQ3)
    fo3 = au('itgfsum', [lift(w, h3, Au), lift(w, pf, Au), sq3c, D(w, Aup, 'simpld', [fi3], '( t e. A |-> %s ) e. L^1' % SQ3)],
             '( ( t e. A |-> sum_ p e. P %s ) e. L^1 /\\ S. A sum_ p e. P %s _d t = sum_ p e. P S. A %s _d t )' % (SQ3, SQ3, SQ3))
    AIF = 'if ( %s , %s , 0 )' % (PHI, ITFG)
    si3 = D(w, Aup, 'sumeq2dv', [D(w, Aupq, 'simprd', [ig], 'S. A %s _d t = %s' % (IFG, AIF))], 'sum_ q e. P S. A %s _d t = sum_ q e. P %s' % (IFG, AIF))
    so3 = au('sumeq2dv', [D(w, Aup, 'eqtrd', [D(w, Aup, 'simprd', [fi3], 'S. A %s _d t = sum_ q e. P S. A %s _d t' % (SQ3, IFG)), si3], 'S. A %s _d t = sum_ q e. P %s' % (SQ3, AIF))],
             'sum_ p e. P S. A %s _d t = %s' % (SQ3, dsum(AIF)))
    JT = 'S. A %s _d t' % AD
    mt3 = au('mpteq2dva', [sq3], '( t e. A |-> %s ) = ( t e. A |-> %s )' % (AD, dsum(IFG)))
    jeq = chain(w, Au, [JT, 'S. A %s _d t' % dsum(IFG), 'sum_ p e. P S. A %s _d t' % SQ3, dsum(AIF)],
                [au('itgeq2dv', [sq3], '%s = S. A %s _d t' % (JT, dsum(IFG))), au('simprd', [fo3], 'S. A %s _d t = sum_ p e. P S. A %s _d t' % (dsum(IFG), SQ3)), so3])
    ucc3, une3 = uprops(Au)
    itfc = rean(w, D(w, ATP, 'itgcl', [fgt, h6r], '%s e. CC' % ITFG), Aupq)
    dd3 = divdist(w, Au, lift(w, pf, Au), itfc, ITFG, une3, ucc3)
    UIF3 = dsum('if ( %s , ( %s / u ) , 0 )' % (PHI, ITFG))
    e3 = au('eqtrd', [au('oveq1d', [jeq], '( %s / u ) = ( %s / u )' % (JT, dsum(AIF))), dd3], '( %s / u ) = %s' % (JT, UIF3))
    itfk = rean(w, D(w, ATP, 'itgcl', [fgt, h6r], '%s e. CC' % ITFG), '( ph /\\ ( p e. P /\\ q e. P ) )')
    cu3 = w.s([h1, h2, itfk], 'cmuint', '( ph -> ( ( u e. %s |-> %s ) e. L^1 /\\ S. %s %s _d u = %s ) )' % (YZ, UIF3, YZ, UIF3, dsum('( %s x. %s )' % (ITFG, LG))))
    mu3 = d('mpteq2dva', [e3], '( u e. %s |-> ( %s / u ) ) = ( u e. %s |-> %s )' % (YZ, JT, YZ, UIF3))
    ibl_u = d('eqeltrd', [mu3, d('simpld', [cu3], '( u e. %s |-> %s ) e. L^1' % (YZ, UIF3))], '( u e. %s |-> ( %s / u ) ) e. L^1' % (YZ, JT))
    RHS = 'S. %s ( %s / u ) _d u' % (YZ, JT)
    rhs = d('eqtrd', [d('itgeq2dv', [e3], '%s = S. %s %s _d u' % (RHS, YZ, UIF3)), d('simprd', [cu3], 'S. %s %s _d u = %s' % (YZ, UIF3, dsum('( %s x. %s )' % (ITFG, LG))))],
            '%s = %s' % (RHS, dsum('( %s x. %s )' % (ITFG, LG))))
    # ---- part 4 ----
    itfc2 = rean(w, D(w, ATP, 'itgcl', [fgt, h6r], '%s e. CC' % ITFG), ATP)
    cm4 = atp('mulcomd', [lgcc, itfc2], '( %s x. %s ) = ( %s x. %s )' % (LG, ITFG, ITFG, LG))
    s4 = d('sumeq2dv', [ap('sumeq2dv', [cm4], 'sum_ q e. P ( %s x. %s ) = sum_ q e. P ( %s x. %s )' % (LG, ITFG, ITFG, LG))],
           '%s = %s' % (dsum('( %s x. %s )' % (LG, ITFG)), dsum('( %s x. %s )' % (ITFG, LG))))
    eqf = chain(w, A, [LHS, dsum('( %s x. %s )' % (LG, ITFG)), dsum('( %s x. %s )' % (ITFG, LG)), RHS], [lhs, s4, ('r', rhs)])
    fin = d('3jca', [ibl_t, ibl_u, eqf], split_imp(S['cmfub'])[1])
    w.qed([fin], 'idi', S['cmfub'])
    return run(w, only)


if __name__ == '__main__':
    gen_fub()
