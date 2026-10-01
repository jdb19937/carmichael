"""Sortie CM: the prime window sum in t (cmcnt, cmpwt) and the swap at PWS (cmswp).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_c.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *

only = sys.argv[1:]
CNR = '( RR -cn-> CC )'


def cnc(w, C, cst, K, v='t'):
    """( C -> ( v e. RR |-> K ) e. CNR ) from cst ( C -> K e. CC )"""
    return D(w, C, 'syl3anc', [cst, a1(w, C, 'ax-resscn', 'RR C_ CC'), a1(w, C, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], '( %s e. RR |-> %s ) e. %s' % (v, K, CNR))


def cnm(w, C, s1, X1, s2, X2, v='t', op='x.', ref='mulcncf'):
    return D(w, C, ref, [s1, s2], '( %s e. RR |-> ( %s %s %s ) ) e. %s' % (v, X1, op, X2, CNR))


def psmem(w, C, p, Y, U):
    """steps under C (with p e. PSET(Y,U) a conjunct): p e. NN, p e. Prime, Y < p, p <_ ( |_ ` U )"""
    c = mk(w, C)
    PS = PSET(Y, U)
    pin = proj(w, C, '%s e. %s' % (p, PS))
    eqa = 'a = %s' % p
    ida = w.s([], 'id', '( %s -> %s )' % (eqa, eqa))
    st, body = w.wcongr('( a e. Prime /\\ %s < a )' % Y, {'a': p}, eqa, {'a': ida})
    er = w.s([st], 'elrab', '( %s e. %s <-> ( %s e. ( 1 ... ( |_ ` %s ) ) /\\ %s ) )' % (p, PS, p, U, body))
    g = c('sylib', [pin, er], '( %s e. ( 1 ... ( |_ ` %s ) ) /\\ %s )' % (p, U, body))
    fz = c('simpld', [g], '%s e. ( 1 ... ( |_ ` %s ) )' % (p, U))
    pr_ = c('simprd', [g], body)
    nn = c('syl', [fz, w.inst('elfznn')], '%s e. NN' % p)
    prm = c('simpld', [pr_], '%s e. Prime' % p)
    yp = c('simprd', [pr_], '%s < %s' % (Y, p))
    le = c('syl', [fz, w.inst('elfzle2')], '%s <_ ( |_ ` %s )' % (p, U))
    return nn, prm, yp, le


def cpcc(w, C, nx, pnn, T, p='P'):
    """( C -> CP(p,T) e. CC ) from nx ( C -> NX ), pnn ( C -> p e. NN ), T real step (C -> T e. RR)"""
    c = mk(w, C)
    chv = c('simpld', [c('syl2anc', [nx, c('nnzd', [pnn], '%s e. ZZ' % p), w.inst('cen2chv')], '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CHV(p), CHV(p)))], '%s e. CC' % CHV(p))
    lg = c('recnd', [c('relogcld', [c('nnrpd', [pnn], '%s e. RR+' % p)], '( log ` %s ) e. RR' % p)], '( log ` %s ) e. CC' % p)
    k = c('mulcld', [chv, lg], '( %s x. ( log ` %s ) ) e. CC' % (CHV(p), p))
    E = '( -u 1 - ( %s x. _i ) )' % T
    ec = c('subcld', [c('negcld', [a1(w, C, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), c('mulcld', [c('recnd', [T], '%s e. CC' % ('t' if False else split_imp(__import__('cl').formula_of(w, T))[1].split()[0])), a1(w, C, 'ax-icn', '_i e. CC')], '( %s x. _i ) e. CC' % split_imp(__import__('cl').formula_of(w, T))[1].split()[0])], '%s e. CC' % E) if False else None
    return k, chv, lg


def gen_cnt():
    w = W('cmcnt', 'The prime window summand ` t |-> chi ( P ) log P P ^ ( -u 1 - t i ) ` is continuous on the reals ( ~ cxpef , ~ efcn ; Lean ` measurable_uncurry_primeWindowSum ` ).')
    A0, C0 = split_imp(S['cmcnt'])
    d = mk(w, A0)
    nx = d('simpl', [], NX); pnn = d('simpr', [], 'P e. NN')
    k, chv, lg = cpcc(w, A0, nx, pnn, None)
    K = '( %s x. ( log ` P ) )' % CHV('P')
    pcc = d('nncnd', [pnn], 'P e. CC'); pne = d('nnne0d', [pnn], 'P =/= 0')
    idc = d('syl', [w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfmptid')], 'mp2an', '( t e. RR |-> t ) e. %s' % CNR)] if False else [a1(w, A0, 'mp2an', '( t e. RR |-> t ) e. %s' % CNR, [w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfmptid')])], 'id', 'x') if False else \
        a1(w, A0, 'mp2an', '( t e. RR |-> t ) e. %s' % CNR, [w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfmptid')])
    ic = cnc(w, A0, a1(w, A0, 'ax-icn', '_i e. CC'), '_i')
    ti = cnm(w, A0, idc, 't', ic, '_i')
    m1 = cnc(w, A0, d('negcld', [a1(w, A0, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), '-u 1')
    E = '( -u 1 - ( t x. _i ) )'
    sb = cnm(w, A0, m1, '-u 1', ti, '( t x. _i )', op='-', ref='subcncf')
    lgc = cnc(w, A0, lg, '( log ` P )')
    ml = cnm(w, A0, sb, E, lgc, '( log ` P )')
    EX = '( exp ` ( %s x. ( log ` P ) ) )' % E
    ex = d('cncfmpt1f', [a1(w, A0, 'efcn', 'exp e. ( CC -cn-> CC )'), ml], '( t e. RR |-> %s ) e. %s' % (EX, CNR))
    At = '( %s /\\ t e. RR )' % A0
    at = mk(w, At)
    tc = at('recnd', [w.s([], 'simpr', '( %s -> t e. RR )' % At)], 't e. CC')
    ec = at('subcld', [at('negcld', [a1(w, At, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), at('mulcld', [tc, a1(w, At, 'ax-icn', '_i e. CC')], '( t x. _i ) e. CC')], '%s e. CC' % E)
    CPW = '( P ^c %s )' % E
    ce = at('syl3anc', [lift(w, pcc, At), lift(w, pne, At), ec, w.inst('cxpef')], '%s = %s' % (CPW, EX))
    me = d('mpteq2dva', [ce], '( t e. RR |-> %s ) = ( t e. RR |-> %s )' % (CPW, EX))
    cp = d('eqeltrd', [me, ex], '( t e. RR |-> %s ) e. %s' % (CPW, CNR))
    kc = cnc(w, A0, k, K)
    fin = cnm(w, A0, kc, K, cp, CPW)
    w.qed([fin], 'idi', S['cmcnt'])
    return run(w, only)


def cpin(w, C, nx, p, pnn, tr, T='t'):
    """( C -> CP(p,T) e. CC ) from nx ( C -> NX ), pnn ( C -> p e. NN ), tr ( C -> T e. RR )"""
    c = mk(w, C)
    chv = c('simpld', [c('syl2anc', [nx, c('nnzd', [pnn], '%s e. ZZ' % p), w.inst('cen2chv')], '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CHV(p), CHV(p)))], '%s e. CC' % CHV(p))
    lg = c('recnd', [c('relogcld', [c('nnrpd', [pnn], '%s e. RR+' % p)], '( log ` %s ) e. RR' % p)], '( log ` %s ) e. CC' % p)
    k = c('mulcld', [chv, lg], '( %s x. ( log ` %s ) ) e. CC' % (CHV(p), p))
    E = '( -u 1 - ( %s x. _i ) )' % T
    ec = c('subcld', [c('negcld', [a1(w, C, 'ax-1cn', '1 e. CC')], '-u 1 e. CC'), c('mulcld', [c('recnd', [tr], '%s e. CC' % T), a1(w, C, 'ax-icn', '_i e. CC')], '( %s x. _i ) e. CC' % T)], '%s e. CC' % E)
    cp = c('cxpcld', [c('nncnd', [pnn], '%s e. CC' % p), ec], '( %s ^c %s ) e. CC' % (p, E))
    return c('mulcld', [k, cp], '%s e. CC' % CP(p, T))


def pscnt(w, C, nx, p='p', Y='Y', U='U'):
    """( ( C /\\ p e. PSET ) -> ( t e. RR |-> CP(p,t) ) e. CNR )"""
    Cp = '( %s /\\ %s e. %s )' % (C, p, PSET(Y, U))
    nn, prm, yp, le = psmem(w, Cp, p, Y, U)
    h = D(w, Cp, 'jca', [lift(w, nx, Cp), nn], '( %s /\\ %s e. NN )' % (NX, p))
    return use(w, Cp, 'cmcnt', {'P': p}, h), nn


def gen_pwt():
    from z4blib import cnsq
    w = W('cmpwt', 'The height integrand ` t |-> abs ( PWS ( t , Y , U ) ) ^ 2 ` is integrable on ` ( -u H , H ) ` with a real nonnegative integral ( ~ cmcnt , ~ fsumcncf , ~ lsibl ).')
    A0, C0 = split_imp(S['cmpwt'])
    d = mk(w, A0)
    nx = d('simp1', [], NX); hr = d('simp2', [], 'H e. RR'); yu = d('simp3', [], '( Y e. RR /\\ U e. RR )')
    PS = PSET('Y', 'U')
    pf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` U ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` U ) )' % PS)], '%s e. Fin' % PS)
    cn1, _ = pscnt(w, A0, nx)
    PW = PWS('t', 'Y', 'U')
    cn = d('zl3fsc', [a1(w, A0, 'ax-resscn', 'RR C_ CC'), pf, cn1], '( t e. RR |-> %s ) e. %s' % (PW, CNR))
    At = '( %s /\\ t e. RR )' % A0
    Atp = '( %s /\\ p e. %s )' % (At, PS)
    nn, _, _, _ = psmem(w, Atp, 'p', 'Y', 'U')
    cpc = cpin(w, Atp, lift(w, nx, Atp), 'p', nn, proj(w, Atp, 't e. RR'))
    pwc = D(w, At, 'fsumcl', [lift(w, pf, At), cpc], '%s e. CC' % PW)
    sq = cnsq(w, A0, cn, PW, 't', pwc)
    TT = '( -u H (,) H )'
    ib = d('lsibl', [d('renegcld', [hr], '-u H e. RR'), hr, sq], '( t e. %s |-> %s ) e. L^1' % (TT, ABS2(PW)))
    Ai = '( %s /\\ t e. %s )' % (A0, TT)
    ti = D(w, Ai, 'syl', [w.s([], 'simpr', '( %s -> t e. %s )' % (Ai, TT)), w.inst('elioore')], 't e. RR')
    pwc2 = D(w, Ai, 'syl', [D(w, Ai, 'jca', [w.s([], 'simpl', '( %s -> %s )' % (Ai, A0)), ti], At), w.s([pwc], 'idi', '( %s -> %s e. CC )' % (At, PW))], '%s e. CC' % PW)
    ar = D(w, Ai, 'abscld', [pwc2], '( abs ` %s ) e. RR' % PW)
    r2 = D(w, Ai, 'resqcld', [ar], '%s e. RR' % ABS2(PW))
    g0 = D(w, Ai, 'sqge0d', [ar], '0 <_ %s' % ABS2(PW))
    JT = JJ('H', 'Y', 'U')
    jr = d('itgrecl', [r2, ib], '%s e. RR' % JT)
    j0 = d('itgge0', [ib, r2, g0], '0 <_ %s' % JT)
    fin = d('3jca', [ib, jr, j0], C0)
    w.qed([fin], 'idi', S['cmpwt'])
    return run(w, only)


def gen_swp():
    w = W('cmswp', 'The swap at the prime window sum: ` S. ( -u H , H ) S. ( Y , Z ) abs ( PWS ( t , Y , u ) ) ^ 2 / u _d u _d t = S. ( Y , Z ) ( S. ( -u H , H ) abs ( PWS ( t , Y , u ) ) ^ 2 _d t ) / u _d u ` , both integrable ( ~ cmfub , ~ kd2pwsif ; Lean ` integral_integral_swap ` , ` integrable_normSq_div ` ).')
    A0, C0 = split_imp(S['cmswp'])
    d = mk(w, A0)
    nx = d('simp1', [], NX); hr = d('simp2', [], 'H e. RR'); yz = d('simp3', [], '( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z )')
    yp = d('simp1d', [yz], 'Y e. RR+'); zr = d('simp2d', [yz], 'Z e. RR')
    yr = d('rpred', [yp], 'Y e. RR'); yx = d('rexrd', [yr], 'Y e. RR*')
    PS = PSET('Y', 'Z')
    pf = d('ssfid', [d('fzfid', [], '( 1 ... ( |_ ` Z ) ) e. Fin'), a1(w, A0, 'ssrab2', '%s C_ ( 1 ... ( |_ ` Z ) )' % PS)], '%s e. Fin' % PS)
    Ap = '( %s /\\ p e. %s )' % (A0, PS)
    nn, _, ypl, le = psmem(w, Ap, 'p', 'Y', 'Z')
    ap_ = mk(w, Ap)
    pr = ap_('nnred', [nn], 'p e. RR')
    pz = ap_('letrd', [pr, ap_('flcld', [lift(w, zr, Ap)], '( |_ ` Z ) e. ZZ') if False else ap_('zred', [ap_('flcld', [lift(w, zr, Ap)], '( |_ ` Z ) e. ZZ')], '( |_ ` Z ) e. RR'), lift(w, zr, Ap), le,
                          ap_('syl', [lift(w, zr, Ap), w.inst('flle')], '( |_ ` Z ) <_ Z')], 'p <_ Z')
    pioc = ap_('mpbird', [ap_('3jca', [pr, ypl, pz], '( p e. RR /\\ Y < p /\\ p <_ Z )'),
                          ap_('syl2anc', [lift(w, yx, Ap), lift(w, zr, Ap), w.inst('elioc2')], '( p e. ( Y (,] Z ) <-> ( p e. RR /\\ Y < p /\\ p <_ Z ) )')], 'p e. ( Y (,] Z )')
    pss = d('ssrdv', [w.s([pioc], 'ex', '( %s -> ( p e. %s -> p e. ( Y (,] Z ) ) )' % (A0, PS))], '%s C_ ( Y (,] Z )' % PS)
    h2 = d('jca', [pf, pss], '( %s e. Fin /\\ %s C_ ( Y (,] Z ) )' % (PS, PS))
    TT = '( -u H (,) H )'
    h3 = a1(w, A0, 'ioombl', '%s e. dom vol' % TT)
    C4 = '( %s /\\ ( p e. %s /\\ t e. %s ) )' % (A0, PS, TT)
    nn4, _, _, _ = psmem(w, C4, 'p', 'Y', 'Z')
    t4 = D(w, C4, 'syl', [proj(w, C4, 't e. %s' % TT), w.inst('elioore')], 't e. RR')
    h4 = cpin(w, C4, lift(w, nx, C4), 'p', nn4, t4)
    eq = 'p = q'
    idp = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    h5, cq = w.congr(CP('p', 't'), {'p': 'q'}, eq, {'p': idp})
    assert cq == CP('q', 't')
    # h6: continuity of the product, lsibl
    C6 = '( %s /\\ ( p e. %s /\\ q e. %s ) )' % (A0, PS, PS)
    c6 = mk(w, C6)
    cnp = rean(w, pscnt(w, A0, nx, 'p', 'Y', 'Z')[0], C6)
    cnq = rean(w, pscnt(w, A0, nx, 'q', 'Y', 'Z')[0], C6)
    cjq = c6('cncfmpt1f', [a1(w, C6, 'cjcncf', '* e. ( CC -cn-> CC )'), cnq], '( t e. RR |-> ( * ` %s ) ) e. %s' % (CP('q', 't'), CNR))
    FG = '( %s x. ( * ` %s ) )' % (CP('p', 't'), CP('q', 't'))
    pr6 = c6('mulcncf', [cnp, cjq], '( t e. RR |-> %s ) e. %s' % (FG, CNR))
    h6 = c6('lsibl', [c6('renegcld', [lift(w, hr, C6)], '-u H e. RR'), lift(w, hr, C6), pr6], '( t e. %s |-> %s ) e. L^1' % (TT, FG))
    DS = 'sum_ p e. %s if ( p <_ u , %s , 0 )' % (PS, CP('p', 't'))
    IU = 'S. ( Y (,) Z ) ( %s / u ) _d u' % ABS2(DS)
    JT = 'S. %s %s _d t' % (TT, ABS2(DS))
    FUB = '( ( t e. %s |-> %s ) e. L^1 /\\ ( u e. ( Y (,) Z ) |-> ( %s / u ) ) e. L^1 /\\ S. %s %s _d t = S. ( Y (,) Z ) ( %s / u ) _d u )' % (TT, IU, JT, TT, IU, JT)
    fub = w.s([yz, h2, h3, h4, h5, h6], 'cmfub', '( %s -> %s )' % (A0, FUB))
    # PWS = D on the u-range
    Ctu = '( ( %s /\\ t e. %s ) /\\ u e. ( Y (,) Z ) )' % (A0, TT)
    ctu = mk(w, Ctu)
    ug = ctu('mpbid', [proj(w, Ctu, 'u e. ( Y (,) Z )'), ctu('syl2anc', [lift(w, yx, Ctu), ctu('rexrd', [lift(w, zr, Ctu)], 'Z e. RR*'), w.inst('elioo2')], '( u e. ( Y (,) Z ) <-> ( u e. RR /\\ Y < u /\\ u < Z ) )')],
              '( u e. RR /\\ Y < u /\\ u < Z )')
    ur = ctu('simp1d', [ug], 'u e. RR')
    uz = ctu('ltled', [ur, lift(w, zr, Ctu), ctu('simp3d', [ug], 'u < Z')], 'u <_ Z')
    tr = ctu('syl', [proj(w, Ctu, 't e. %s' % TT), w.inst('elioore')], 't e. RR')
    PW = PWS('t', 'Y', 'u')
    pe = ctu('syl3anc', [lift(w, nx, Ctu), ctu('jca', [tr, lift(w, yr, Ctu)], '( t e. RR /\\ Y e. RR )'), ctu('3jca', [lift(w, zr, Ctu), ur, uz], '( Z e. RR /\\ u e. RR /\\ u <_ Z )'), w.inst('kd2pwsif')],
             '%s = %s' % (PW, DS))
    pe2 = ctu('fveq2d', [pe], '( abs ` %s ) = ( abs ` %s )' % (PW, DS))
    pe3 = ctu('oveq1d', [pe2], '%s = %s' % (ABS2(PW), ABS2(DS)))
    pe4 = ctu('oveq1d', [pe3], '( %s / u ) = ( %s / u )' % (ABS2(PW), ABS2(DS)))
    Ct = '( %s /\\ t e. %s )' % (A0, TT)
    IUP = II('t', 'Y', 'Z')
    iu = D(w, Ct, 'itgeq2dv', [pe4], '%s = %s' % (IUP, IU))
    mt = d('mpteq2dva', [iu], '( t e. %s |-> %s ) = ( t e. %s |-> %s )' % (TT, IUP, TT, IU))
    Cut = '( ( %s /\\ u e. ( Y (,) Z ) ) /\\ t e. %s )' % (A0, TT)
    pe3b = rean(w, pe3, Cut)
    Cu = '( %s /\\ u e. ( Y (,) Z ) )' % A0
    JTP = JJ('H', 'Y', 'u')
    ju = D(w, Cu, 'itgeq2dv', [pe3b], '%s = %s' % (JTP, JT))
    ju2 = D(w, Cu, 'oveq1d', [ju], '( %s / u ) = ( %s / u )' % (JTP, JT))
    mu = d('mpteq2dva', [ju2], '( u e. ( Y (,) Z ) |-> ( %s / u ) ) = ( u e. ( Y (,) Z ) |-> ( %s / u ) )' % (JTP, JT))
    i1 = d('eqeltrd', [mt, d('simp1d', [fub], '( t e. %s |-> %s ) e. L^1' % (TT, IU))], '( t e. %s |-> %s ) e. L^1' % (TT, IUP))
    i2 = d('eqeltrd', [mu, d('simp2d', [fub], '( u e. ( Y (,) Z ) |-> ( %s / u ) ) e. L^1' % JT)], '( u e. ( Y (,) Z ) |-> ( %s / u ) ) e. L^1' % JTP)
    e3 = chain(w, A0, ['S. %s %s _d t' % (TT, IUP), 'S. %s %s _d t' % (TT, IU), 'S. ( Y (,) Z ) ( %s / u ) _d u' % JT, 'S. ( Y (,) Z ) ( %s / u ) _d u' % JTP],
               [d('itgeq2dv', [iu], 'S. %s %s _d t = S. %s %s _d t' % (TT, IUP, TT, IU)), d('simp3d', [fub], 'S. %s %s _d t = S. ( Y (,) Z ) ( %s / u ) _d u' % (TT, IU, JT)),
                ('r', d('itgeq2dv', [ju2], 'S. ( Y (,) Z ) ( %s / u ) _d u = S. ( Y (,) Z ) ( %s / u ) _d u' % (JTP, JT)))])
    fin = d('3jca', [i1, i2, e3], C0)
    w.qed([fin], 'idi', S['cmswp'])
    return run(w, only)


if __name__ == '__main__':
    gen_cnt()
    gen_pwt()
    gen_swp()
