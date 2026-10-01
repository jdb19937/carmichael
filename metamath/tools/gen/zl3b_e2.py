"""ZL3b E2: translation along a vertical line (zl3vtr), the complex shift (zl3csh), scaling (zl3scl).
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_e2.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of
from zl3b_d2 import cst
from zl3b_e1 import bl_at, m_nonneg, seg_pre
import lin

only = sys.argv[1:]
S = STATEMENTS
K8 = '( ( 8 x. M ) / ( log ` 2 ) )'


def mnn(w, A_, bl, C, cc, gf):
    """( A_ -> 0 <_ M )"""
    b0, one = m_nonneg(w, A_, bl, C, cc, gf)
    ic = cst(w, A_, 'ax-icn', '_i e. CC')
    G0 = '( G ` %s )' % CP(C, '0')
    g0c = D(w, A_, 'ffvelcdmd', [gf, D(w, A_, 'addcld', [cc, D(w, A_, 'mulcld', [ic, cst(w, A_, '0cn', '0 e. CC')], '( _i x. 0 ) e. CC')], '%s e. CC' % CP(C, '0'))], '%s e. CC' % G0)
    mr = None
    return b0, one, g0c


def m0_of(w, A_, bl, C, cc, gf, mr):
    b0, one, g0c = mnn(w, A_, bl, C, cc, gf)
    G0 = '( G ` %s )' % CP(C, '0')
    mc = D(w, A_, 'recnd', [mr], 'M e. CC')
    mm = D(w, A_, 'eqtrd', [D(w, A_, 'oveq2d', [one], '( M x. ( 2 ^c -u ( abs ` 0 ) ) ) = ( M x. 1 )'), D(w, A_, 'mulridd', [mc], '( M x. 1 ) = M')], '( M x. ( 2 ^c -u ( abs ` 0 ) ) ) = M')
    return D(w, A_, 'letrd', [cst(w, A_, '0re', '0 e. RR'), D(w, A_, 'abscld', [g0c], '( abs ` %s ) e. RR' % G0), mr, D(w, A_, 'absge0d', [g0c], '0 <_ ( abs ` %s )' % G0),
                              D(w, A_, 'breqtrd', [b0, mm], '( abs ` %s ) <_ M' % G0)], '0 <_ M')


VLH = lambda C: 'A. u e. RR ( 1 <_ ( abs ` u ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) )' % CP(C, 'u')


def z6ctx(w, A_, bl, C, cr, gc, mr, m0):
    """( A_ -> ( ( C e. RR /\\ ( G e. ( CC -cn-> CC ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. CC ) ) /\\ ( ( M e. RR /\\ 1 e. RR+ ) /\\ VLH ) ) )"""
    Au = '( %s /\\ u e. RR )' % A_
    ur = w.s([], 'simpr', '( %s -> u e. RR )' % Au)
    cc = D(w, A_, 'recnd', [cr], '%s e. CC' % C)
    ic = cst(w, Au, 'ax-icn', '_i e. CC')
    dm = w.s([D(w, Au, 'addcld', [w.s([cc], 'adantr', '( %s -> %s e. CC )' % (Au, C)), D(w, Au, 'mulcld', [ic, D(w, Au, 'recnd', [ur], 'u e. CC')], '( _i x. u ) e. CC')], '%s e. CC' % CP(C, 'u'))],
             'ralrimiva', '( %s -> A. u e. RR %s e. CC )' % (A_, CP(C, 'u')))
    bu = bl_at(w, Au, w.s([bl], 'adantr', '( %s -> %s )' % (Au, BLC(C))), C, 'u', ur)
    aur = D(w, Au, 'abscld', [D(w, Au, 'recnd', [ur], 'u e. CC')], '( abs ` u ) e. RR')
    au0 = D(w, Au, 'absge0d', [D(w, Au, 'recnd', [ur], 'u e. CC')], '0 <_ ( abs ` u )')
    au4 = D(w, Au, 'redivcld', [aur, cst(w, Au, '4re', '4 e. RR'), cst(w, Au, '4ne0', '4 =/= 0')], '( ( abs ` u ) / 4 ) e. RR')
    le = lin.linarith(w, Au, [au0], '-u ( abs ` u ) <_ -u ( ( abs ` u ) / 4 )', leaves={'( abs ` u )': aur})
    pl = D(w, Au, 'cxplead', [cst(w, Au, '2re', '2 e. RR'), cst(w, Au, '1le2', '1 <_ 2'), D(w, Au, 'renegcld', [aur], '-u ( abs ` u ) e. RR'), D(w, Au, 'renegcld', [au4], '-u ( ( abs ` u ) / 4 ) e. RR'), le],
            '( 2 ^c -u ( abs ` u ) ) <_ ( 2 ^c -u ( ( abs ` u ) / 4 ) )')
    p1 = D(w, Au, 'rpcxpcld', [cst(w, Au, '2rp', '2 e. RR+'), D(w, Au, 'renegcld', [aur], '-u ( abs ` u ) e. RR')], '( 2 ^c -u ( abs ` u ) ) e. RR+')
    p4 = D(w, Au, 'rpcxpcld', [cst(w, Au, '2rp', '2 e. RR+'), D(w, Au, 'renegcld', [au4], '-u ( ( abs ` u ) / 4 ) e. RR')], '( 2 ^c -u ( ( abs ` u ) / 4 ) ) e. RR+')
    mr1 = w.s([mr], 'adantr', '( %s -> M e. RR )' % Au)
    ml = D(w, Au, 'lemul2ad', [D(w, Au, 'rpred', [p1], '( 2 ^c -u ( abs ` u ) ) e. RR'), D(w, Au, 'rpred', [p4], '( 2 ^c -u ( ( abs ` u ) / 4 ) ) e. RR'), mr1, w.s([m0], 'adantr', '( %s -> 0 <_ M )' % Au), pl],
           '( M x. ( 2 ^c -u ( abs ` u ) ) ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) )')
    gf = w.s([w.s([gc], 'adantr', '( %s -> G e. ( CC -cn-> CC ) )' % Au), w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % Au)
    gv = '( G ` %s )' % CP(C, 'u')
    gvc = D(w, Au, 'ffvelcdmd', [gf, D(w, Au, 'addcld', [w.s([cc], 'adantr', '( %s -> %s e. CC )' % (Au, C)), D(w, Au, 'mulcld', [ic, D(w, Au, 'recnd', [ur], 'u e. CC')], '( _i x. u ) e. CC')], '%s e. CC' % CP(C, 'u'))], '%s e. CC' % gv)
    b2 = D(w, Au, 'letrd', [D(w, Au, 'abscld', [gvc], '( abs ` %s ) e. RR' % gv), D(w, Au, 'remulcld', [mr1, D(w, Au, 'rpred', [p1], '( 2 ^c -u ( abs ` u ) ) e. RR')], '( M x. ( 2 ^c -u ( abs ` u ) ) ) e. RR'),
                            D(w, Au, 'remulcld', [mr1, D(w, Au, 'rpred', [p4], '( 2 ^c -u ( ( abs ` u ) / 4 ) ) e. RR')], '( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) e. RR'), bu, ml],
           '( abs ` %s ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) )' % gv)
    vh = w.s([w.s([b2], 'a1d', '( %s -> ( 1 <_ ( abs ` u ) -> ( abs ` %s ) <_ ( M x. ( 2 ^c -u ( ( abs ` u ) / 4 ) ) ) ) )' % (Au, gv))], 'ralrimiva', '( %s -> %s )' % (A_, VLH(C)))
    L = '( %s e. RR /\\ ( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) )' % (C, CP(C, 'u'))
    R = '( ( M e. RR /\\ 1 e. RR+ ) /\\ %s )' % VLH(C)
    l = w.s([cr, w.s([gc, dm], 'jca', '( %s -> ( G e. ( CC -cn-> CC ) /\\ A. u e. RR %s e. CC ) )' % (A_, CP(C, 'u')))], 'jca', '( %s -> %s )' % (A_, L))
    r = w.s([w.s([mr, cst(w, A_, '1rp', '1 e. RR+')], 'jca', '( %s -> ( M e. RR /\\ 1 e. RR+ ) )' % A_), vh], 'jca', '( %s -> %s )' % (A_, R))
    return w.s([l, r], 'jca', '( %s -> ( %s /\\ %s ) )' % (A_, L, R)), '( %s /\\ %s )' % (L, R)


# ---------------------------------------------------------------- zl3vtr
if __name__ == '__main__' and (not only or 'zl3vtr' in only):
    w = W('zl3vtr', 'Translation along a vertical line does not change the limit of the symmetric segment integrals.')
    ph, concl = ante_of(S['zl3vtr'])
    cr = w.s([], 'simpll', '( %s -> C e. RR )' % ph); er = w.s([], 'simplr', '( %s -> E e. RR )' % ph)
    gc = w.s([], 'simprll', '( %s -> G e. ( CC -cn-> CC ) )' % ph); mr = w.s([], 'simprlr', '( %s -> M e. RR )' % ph)
    bl = w.s([], 'simprr', '( %s -> %s )' % (ph, BLC('C')))
    cc = D(w, ph, 'recnd', [cr], 'C e. CC'); ec = D(w, ph, 'recnd', [er], 'E e. CC'); ic = cst(w, ph, 'ax-icn', '_i e. CC')
    gf = w.s([gc, w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % ph)
    m0 = m0_of(w, ph, bl, 'C', cc, gf, mr)
    zc, ZC = z6ctx(w, ph, bl, 'C', cr, gc, mr, m0)
    V = VL('G', 'C')
    vex = D(w, ph, 'syl', [zc, w.inst('z6vlex')], '( t e. RR+ |-> %s ) ~~>r %s' % (LT('G', 'C', 't'), V))
    vc = D(w, ph, 'syl', [vex, w.inst('rlimcl')], '%s e. CC' % V)
    TR = TRN('G', '( _i x. E )')
    Fm = '( t e. RR+ |-> %s )' % LT(TR, 'C', 't')
    AE = '( abs ` E )'; Yv = '( %s + 1 )' % AE
    aer = D(w, ph, 'abscld', [ec], '%s e. RR' % AE); ae0 = D(w, ph, 'absge0d', [ec], '0 <_ %s' % AE)
    yvr = D(w, ph, 'syl', [aer, w.inst('peano2re')], '%s e. RR' % Yv)
    l2 = w.s([cst(w, ph, '2re', '2 e. RR'), cst(w, ph, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % ph)
    k8r = D(w, ph, 'rerpdivcld', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), mr], '( 8 x. M ) e. RR'), l2], '%s e. RR' % K8)
    EM = '( 2 x. ( %s x. M ) )' % AE
    emr = D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), D(w, ph, 'remulcld', [aer, mr], '( %s x. M ) e. RR' % AE)], '%s e. RR' % EM)
    E4 = '( 2 ^c ( %s / 4 ) )' % AE
    e4r = D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'redivcld', [aer, cst(w, ph, '4re', '4 e. RR'), cst(w, ph, '4ne0', '4 =/= 0')], '( %s / 4 ) e. RR' % AE)], '%s e. RR+' % E4)], '%s e. RR' % E4)
    Cc = '( ( %s + %s ) x. %s )' % (EM, K8, E4)
    ccr = D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [emr, k8r], '( %s + %s ) e. RR' % (EM, K8)), e4r], '%s e. RR' % Cc)
    # values: for t e. RR+, LT ( TR , C , t ) = lint G over the translated segment
    def ltr_at(A_, T, tr):
        """( A_ -> LT(TR, C, T) = lint G < C + i ( -u T + E ) , C + i ( T + E ) > ) and its value in CC"""
        lr = 'adantr' if A_.count('/\\') == ph.count('/\\') + 1 else 'ad2antrr'
        cc_ = w.s([cc], lr, '( %s -> C e. CC )' % A_)
        ec_ = w.s([ec], lr, '( %s -> E e. CC )' % A_)
        ic_ = cst(w, A_, 'ax-icn', '_i e. CC')
        tc_ = D(w, A_, 'recnd', [tr], '%s e. CC' % T)
        ntc = D(w, A_, 'negcld', [tc_], '-u %s e. CC' % T)
        P = CP('C', '-u %s' % T); Q = CP('C', T); IE = '( _i x. E )'
        pc = D(w, A_, 'addcld', [cc_, D(w, A_, 'mulcld', [ic_, ntc], '( _i x. -u %s ) e. CC' % T)], '%s e. CC' % P)
        qc = D(w, A_, 'addcld', [cc_, D(w, A_, 'mulcld', [ic_, tc_], '( _i x. %s ) e. CC' % T)], '%s e. CC' % Q)
        iec = D(w, A_, 'mulcld', [ic_, ec_], '%s e. CC' % IE)
        gf_ = w.s([gf], lr, '( %s -> G : CC --> CC )' % A_)
        l = D(w, A_, 'syl', [w.s([w.s([pc, qc, iec], '3jca', '( %s -> ( %s e. CC /\\ %s e. CC /\\ %s e. CC ) )' % (A_, P, Q, IE)), gf_], 'jca',
                                 '( %s -> ( ( %s e. CC /\\ %s e. CC /\\ %s e. CC ) /\\ G : CC --> CC ) )' % (A_, P, Q, IE)), w.inst('zl3ltr')],
              '%s = %s' % (LT(TR, 'C', T), LI('G', '( %s + %s )' % (P, IE), '( %s + %s )' % (Q, IE))))
        def pt(X):
            xc = D(w, A_, 'recnd', [D(w, A_, 'renegcld', [tr], '-u %s e. RR' % T)], '-u %s e. CC' % T) if X == '-u %s' % T else tc_
            a = D(w, A_, 'addassd', [cc_, D(w, A_, 'mulcld', [ic_, xc], '( _i x. %s ) e. CC' % X), iec], '( %s + %s ) = ( C + ( ( _i x. %s ) + %s ) )' % (CP('C', X), IE, X, IE))
            b = D(w, A_, 'oveq2d', [D(w, A_, 'eqcomd', [D(w, A_, 'adddid', [ic_, xc, ec_], '( _i x. ( %s + E ) ) = ( ( _i x. %s ) + %s )' % (X, X, IE))],
                                    '( ( _i x. %s ) + %s ) = ( _i x. ( %s + E ) )' % (X, IE, X))], '( C + ( ( _i x. %s ) + %s ) ) = %s' % (X, IE, CP('C', '( %s + E )' % X)))
            return D(w, A_, 'eqtrd', [a, b], '( %s + %s ) = %s' % (CP('C', X), IE, CP('C', '( %s + E )' % X)))
        pe, qe = pt('-u %s' % T), pt(T)
        U_, W_ = CP('C', '( -u %s + E )' % T), CP('C', '( %s + E )' % T)
        l2_ = D(w, A_, 'eqtrd', [l, D(w, A_, 'oveq2d', [D(w, A_, 'opeq12d', [pe, qe], '<. ( %s + %s ) , ( %s + %s ) >. = <. %s , %s >.' % (P, IE, Q, IE, U_, W_))],
                                                  '%s = %s' % (LI('G', '( %s + %s )' % (P, IE), '( %s + %s )' % (Q, IE)), LI('G', U_, W_)))], '%s = %s' % (LT(TR, 'C', T), LI('G', U_, W_)))
        uc = D(w, A_, 'addcld', [cc_, D(w, A_, 'mulcld', [ic_, D(w, A_, 'addcld', [ntc, ec_], '( -u %s + E ) e. CC' % T)], '( _i x. ( -u %s + E ) ) e. CC' % T)], '%s e. CC' % U_)
        wc_ = D(w, A_, 'addcld', [cc_, D(w, A_, 'mulcld', [ic_, D(w, A_, 'addcld', [tc_, ec_], '( %s + E ) e. CC' % T)], '( _i x. ( %s + E ) ) e. CC' % T)], '%s e. CC' % W_)
        gc_ = w.s([gc], lr, '( %s -> G e. ( CC -cn-> CC ) )' % A_)
        lc = D(w, A_, 'syl', [seg_pre(w, A_, U_, W_, uc, wc_, gc_), w.inst('lintcl')], '%s e. CC' % LI('G', U_, W_))
        return l2_, D(w, A_, 'eqeltrd', [l2_, lc], '%s e. CC' % LT(TR, 'C', T))
    At = '( %s /\\ t e. RR+ )' % ph
    _, ltc = ltr_at(At, 't', D(w, At, 'rpred', [w.s([], 'simpr', '( %s -> t e. RR+ )' % At)], 't e. RR'))
    fm = w.s([ltc], 'fmptd', '( %s -> %s : RR+ --> CC )' % (ph, Fm))
    # the bound for s >_ | E | + 1
    As = '( ( %s /\\ s e. RR+ ) /\\ %s <_ s )' % (ph, Yv)
    L1 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (As, f))
    sp = w.s([], 'simplr', '( %s -> s e. RR+ )' % As); sr = D(w, As, 'rpred', [sp], 's e. RR'); ys = w.s([], 'simpr', '( %s -> %s <_ s )' % (As, Yv))
    cr1, er1, mr1, m01, aer1, ae01, gc1, bl1 = [L1(x, f) for x, f in [(cr, 'C e. RR'), (er, 'E e. RR'), (mr, 'M e. RR'), (m0, '0 <_ M'), (aer, '%s e. RR' % AE), (ae0, '0 <_ %s' % AE),
                                                                        (gc, 'G e. ( CC -cn-> CC )'), (bl, BLC('C'))]]
    ec1 = D(w, As, 'recnd', [er1], 'E e. CC')
    ea = D(w, As, 'leabsd', [er1], 'E <_ %s' % AE)
    nea = D(w, As, 'breqtrd', [D(w, As, 'leabsd', [D(w, As, 'renegcld', [er1], '-u E e. RR')], '-u E <_ ( abs ` -u E )'), D(w, As, 'absnegd', [ec1], '( abs ` -u E ) = %s' % AE)], '-u E <_ %s' % AE)
    R_ = '( s - %s )' % AE; NR = '-u %s' % R_; U = '( -u s + E )'; Wt = '( s + E )'
    lv = {'s': sr, 'E': er1, AE: aer1}
    rr = D(w, As, 'resubcld', [sr, aer1], '%s e. RR' % R_)
    lv2 = dict(lv); lv2[R_] = rr
    r1 = lin.linarith(w, As, [ys], '1 <_ %s' % R_, leaves=lv)
    rp = D(w, As, 'elrpd', [rr, lin.linarith(w, As, [ys], '0 < %s' % R_, leaves=lv)], '%s e. RR+' % R_)
    nrr = D(w, As, 'renegcld', [rr], '%s e. RR' % NR)
    ur = D(w, As, 'readdcld', [D(w, As, 'renegcld', [sr], '-u s e. RR'), er1], '%s e. RR' % U); wr = D(w, As, 'readdcld', [sr, er1], '%s e. RR' % Wt)
    lv3 = {'s': sr, 'E': er1, AE: aer1}
    h1 = lin.linarith(w, As, [ea], '%s <_ -u ( s - %s )' % (U, AE), leaves=lv3)
    h2 = lin.linarith(w, As, [nea, ys], '-u ( s - %s ) <_ %s' % (AE, Wt), leaves=lv3)
    h3 = lin.linarith(w, As, [ys, ae01], '%s < %s' % (U, Wt), leaves=lv3)
    h4 = lin.linarith(w, As, [ys], '-u ( s - %s ) <_ ( s - %s )' % (AE, AE), leaves=lv3)
    h5 = lin.linarith(w, As, [nea], '( s - %s ) <_ %s' % (AE, Wt), leaves=lv3)
    h6 = lin.linarith(w, As, [nea, ys], '-u ( s - %s ) < %s' % (AE, Wt), leaves=lv3)
    PU, PN, PR, PW = CP('C', U), CP('C', NR), CP('C', R_), CP('C', Wt)
    v2 = lambda a, b, c, ar, br, cr_, hab, hbc, hac: D(w, As, 'syl', [w.s([w.s([cr1, gc1], 'jca', '( %s -> ( C e. RR /\\ G e. ( CC -cn-> CC ) ) )' % As),
                                                                      w.s([w.s([ar, br, cr_], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) )' % (As, a, b, c)),
                                                                           w.s([hab, hbc, hac], '3jca', '( %s -> ( %s <_ %s /\\ %s <_ %s /\\ %s < %s ) )' % (As, a, b, b, c, a, c))], 'jca',
                                                                          '( %s -> ( ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ ( %s <_ %s /\\ %s <_ %s /\\ %s < %s ) ) )' % (As, a, b, c, a, b, b, c, a, c))], 'jca',
                                                                     '( %s -> ( ( C e. RR /\\ G e. ( CC -cn-> CC ) ) /\\ ( ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ ( %s <_ %s /\\ %s <_ %s /\\ %s < %s ) ) ) )'
                                                                     % (As, a, b, c, a, b, b, c, a, c)), w.inst('zl3v2')],
                                                         '%s = ( %s + %s )' % (LI('G', CP('C', a), CP('C', c)), LI('G', CP('C', a), CP('C', b)), LI('G', CP('C', b), CP('C', c))))
    sa = v2(U, NR, Wt, ur, nrr, wr, h1, h2, h3)
    sb = v2(NR, R_, Wt, nrr, rr, wr, h4, h5, h6)
    E1, G1, E2 = LI('G', PU, PN), LI('G', PN, PR), LI('G', PR, PW)
    assert G1 == LT('G', 'C', R_)
    fv0, _ = ltr_at(As, 's', sr)
    FS = '( %s ` s )' % Fm
    # ( F ` s ) = LT ( TR , C , s )
    Et = 't = s'
    et = w.s([], 'id', '( %s -> %s )' % (Et, Et))
    sub = D(w, Et, 'oveq2d', [D(w, Et, 'opeq12d', [D(w, Et, 'oveq2d', [D(w, Et, 'oveq2d', [D(w, Et, 'negeqd', [et], '-u t = -u s')], '( _i x. -u t ) = ( _i x. -u s )')], '%s = %s' % (CP('C', '-u t'), CP('C', '-u s'))),
                                                   D(w, Et, 'oveq2d', [D(w, Et, 'oveq2d', [et], '( _i x. t ) = ( _i x. s )')], '%s = %s' % (CP('C', 't'), CP('C', 's')))],
                                       '<. %s , %s >. = <. %s , %s >.' % (CP('C', '-u t'), CP('C', 't'), CP('C', '-u s'), CP('C', 's')))], '%s = %s' % (LT(TR, 'C', 't'), LT(TR, 'C', 's')))
    fvs = w.s([sp, w.s([sub, w.s([], 'eqid', '%s = %s' % (Fm, Fm)), w.s([], 'ovex', '%s e. _V' % LT(TR, 'C', 's'))], 'fvmpt', '( s e. RR+ -> %s = %s )' % (FS, LT(TR, 'C', 's')))],
              'syl', '( %s -> %s = %s )' % (As, FS, LT(TR, 'C', 's')))
    fsplit = D(w, As, 'eqtrd', [D(w, As, 'eqtrd', [fvs, fv0], '%s = %s' % (FS, LI('G', PU, PW))), D(w, As, 'eqtrd', [sa, D(w, As, 'oveq2d', [sb], '( %s + %s ) = ( %s + ( %s + %s ) )' % (E1, LI('G', PN, PW), E1, G1, E2))],
                                                                                                             '%s = ( %s + ( %s + %s ) )' % (LI('G', PU, PW), E1, G1, E2))], '%s = ( %s + ( %s + %s ) )' % (FS, E1, G1, E2))
    # bounds
    def epc(Hh, Vv, Ww, hr, vr_, wr_, disj, dtxt):
        return D(w, As, 'syl', [w.s([w.s([w.s([cr1, gc1], 'jca', '( %s -> ( C e. RR /\\ G e. ( CC -cn-> CC ) ) )' % As), w.s([mr1, bl1], 'jca', '( %s -> ( M e. RR /\\ %s ) )' % (As, BLC('C')))], 'jca',
                                         '( %s -> ( ( C e. RR /\\ G e. ( CC -cn-> CC ) ) /\\ ( M e. RR /\\ %s ) ) )' % (As, BLC('C'))),
                                     w.s([w.s([hr, vr_, wr_], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) )' % (As, Hh, Vv, Ww)), disj], 'jca',
                                         '( %s -> ( ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ %s ) )' % (As, Hh, Vv, Ww, dtxt))], 'jca',
                                    '( %s -> ( ( ( C e. RR /\\ G e. ( CC -cn-> CC ) ) /\\ ( M e. RR /\\ %s ) ) /\\ ( ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ %s ) ) )' % (As, BLC('C'), Hh, Vv, Ww, dtxt)),
                                w.inst('zl3epc')], '( abs ` %s ) <_ ( ( M x. ( 2 ^c -u %s ) ) x. ( abs ` ( %s - %s ) ) )' % (LI('G', CP('C', Vv), CP('C', Ww)), Hh, Ww, Vv))
    DJ1 = '( ( %s <_ %s /\\ %s <_ %s ) \\/ ( %s <_ -u %s /\\ %s <_ -u %s ) )' % (R_, U, R_, NR, U, R_, NR, R_)
    d1 = w.s([w.s([h1, D(w, As, 'leidd', [nrr], '%s <_ %s' % (NR, NR))], 'jca', '( %s -> ( %s <_ -u %s /\\ %s <_ -u %s ) )' % (As, U, R_, NR, R_))], 'olcd', '( %s -> %s )' % (As, DJ1))
    b1 = epc(R_, U, NR, rr, ur, nrr, d1, DJ1)
    DJ2 = '( ( %s <_ %s /\\ %s <_ %s ) \\/ ( %s <_ -u %s /\\ %s <_ -u %s ) )' % (R_, R_, R_, Wt, R_, R_, Wt, R_)
    d2 = w.s([w.s([D(w, As, 'leidd', [rr], '%s <_ %s' % (R_, R_)), h5], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (As, R_, R_, R_, Wt))], 'orcd', '( %s -> %s )' % (As, DJ2))
    b2 = epc(R_, R_, Wt, rr, rr, wr, d2, DJ2)
    zcs = w.s([zc], 'ad2antrr', '( %s -> %s )' % (As, ZC))
    b3 = D(w, As, 'syl', [w.s([zcs, w.s([rp, r1], 'jca', '( %s -> ( %s e. RR+ /\\ 1 <_ %s ) )' % (As, R_, R_))], 'jca', '( %s -> ( %s /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) )' % (As, ZC, R_, R_)), w.inst('z6vlt')],
           '( abs ` ( %s - %s ) ) <_ ( %s x. ( 2 ^c -u ( %s / 4 ) ) )' % (V, G1, K8, R_))
    # abs values of the lengths
    n1 = lin.lineq(w, As, '( %s - %s )' % (NR, U), '( %s - E )' % AE, leaves=lv3)
    n1a = D(w, As, 'eqtrd', [D(w, As, 'fveq2d', [n1], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - E ) )' % (NR, U, AE)),
                             D(w, As, 'absidd', [D(w, As, 'resubcld', [aer1, er1], '( %s - E ) e. RR' % AE), D(w, As, 'mpbird', [ea, D(w, As, 'subge0d', [aer1, er1], '( 0 <_ ( %s - E ) <-> E <_ %s )' % (AE, AE))], '0 <_ ( %s - E )' % AE)],
                               '( abs ` ( %s - E ) ) = ( %s - E )' % (AE, AE))], '( abs ` ( %s - %s ) ) = ( %s - E )' % (NR, U, AE))
    n2 = lin.lineq(w, As, '( %s - %s )' % (Wt, R_), '( E + %s )' % AE, leaves=lv3)
    ep0 = lin.linarith(w, As, [nea], '0 <_ ( E + %s )' % AE, leaves=lv3)
    n2a = D(w, As, 'eqtrd', [D(w, As, 'fveq2d', [n2], '( abs ` ( %s - %s ) ) = ( abs ` ( E + %s ) )' % (Wt, R_, AE)),
                             D(w, As, 'absidd', [D(w, As, 'readdcld', [er1, aer1], '( E + %s ) e. RR' % AE), ep0], '( abs ` ( E + %s ) ) = ( E + %s )' % (AE, AE))], '( abs ` ( %s - %s ) ) = ( E + %s )' % (Wt, R_, AE))
    Q = '( 2 ^c -u %s )' % R_; P = '( 2 ^c -u ( %s / 4 ) )' % R_
    qr = D(w, As, 'rpred', [D(w, As, 'rpcxpcld', [cst(w, As, '2rp', '2 e. RR+'), nrr], '%s e. RR+' % Q)], '%s e. RR' % Q)
    r4 = D(w, As, 'redivcld', [rr, cst(w, As, '4re', '4 e. RR'), cst(w, As, '4ne0', '4 =/= 0')], '( %s / 4 ) e. RR' % R_)
    pr_ = D(w, As, 'rpred', [D(w, As, 'rpcxpcld', [cst(w, As, '2rp', '2 e. RR+'), D(w, As, 'renegcld', [r4], '-u ( %s / 4 ) e. RR' % R_)], '%s e. RR+' % P)], '%s e. RR' % P)
    q0 = D(w, As, 'rpge0d', [D(w, As, 'rpcxpcld', [cst(w, As, '2rp', '2 e. RR+'), nrr], '%s e. RR+' % Q)], '0 <_ %s' % Q)
    qp = D(w, As, 'cxplead', [cst(w, As, '2re', '2 e. RR'), cst(w, As, '1le2', '1 <_ 2'), nrr, D(w, As, 'renegcld', [r4], '-u ( %s / 4 ) e. RR' % R_),
                              lin.linarith(w, As, [r1], '%s <_ -u ( %s / 4 )' % (NR, R_), leaves=lv3)], '%s <_ %s' % (Q, P))
    emr1 = L1(emr, '%s e. RR' % EM); k8r1 = L1(k8r, '%s e. RR' % K8)
    em0 = D(w, As, 'mulge0d', [cst(w, As, '2re', '2 e. RR'), D(w, As, 'remulcld', [aer1, mr1], '( %s x. M ) e. RR' % AE), cst(w, As, '0le2', '0 <_ 2'),
                               D(w, As, 'mulge0d', [aer1, mr1, ae01, m01], '0 <_ ( %s x. M )' % AE)], '0 <_ %s' % EM)
    fq = D(w, As, 'lemul2ad', [qr, pr_, emr1, em0, qp], '( %s x. %s ) <_ ( %s x. %s )' % (EM, Q, EM, P))
    X1 = '( abs ` %s )' % E1; X3 = '( abs ` %s )' % E2; GV = '( %s - %s )' % (G1, V); X2 = '( abs ` %s )' % GV
    vc1 = L1(vc, '%s e. CC' % V)
    gc1c = D(w, As, 'syl', [seg_pre(w, As, PN, PR, D(w, As, 'addcld', [D(w, As, 'recnd', [cr1], 'C e. CC'), D(w, As, 'mulcld', [cst(w, As, 'ax-icn', '_i e. CC'), D(w, As, 'recnd', [nrr], '%s e. CC' % NR)], '( _i x. %s ) e. CC' % NR)], '%s e. CC' % PN),
                                         D(w, As, 'addcld', [D(w, As, 'recnd', [cr1], 'C e. CC'), D(w, As, 'mulcld', [cst(w, As, 'ax-icn', '_i e. CC'), D(w, As, 'recnd', [rr], '%s e. CC' % R_)], '( _i x. %s ) e. CC' % R_)], '%s e. CC' % PR), gc1),
                             w.inst('lintcl')], '%s e. CC' % G1)
    def lc_(Pp, Qq, pr1, qr1):
        pc_ = D(w, As, 'addcld', [D(w, As, 'recnd', [cr1], 'C e. CC'), D(w, As, 'mulcld', [cst(w, As, 'ax-icn', '_i e. CC'), D(w, As, 'recnd', [pr1], '%s e. CC' % Pp)], '( _i x. %s ) e. CC' % Pp)], '%s e. CC' % CP('C', Pp))
        qc_ = D(w, As, 'addcld', [D(w, As, 'recnd', [cr1], 'C e. CC'), D(w, As, 'mulcld', [cst(w, As, 'ax-icn', '_i e. CC'), D(w, As, 'recnd', [qr1], '%s e. CC' % Qq)], '( _i x. %s ) e. CC' % Qq)], '%s e. CC' % CP('C', Qq))
        return D(w, As, 'syl', [seg_pre(w, As, CP('C', Pp), CP('C', Qq), pc_, qc_, gc1), w.inst('lintcl')], '%s e. CC' % LI('G', CP('C', Pp), CP('C', Qq)))
    e1c = lc_(U, NR, ur, nrr); e2c = lc_(R_, Wt, rr, wr)
    gvc = D(w, As, 'subcld', [gc1c, vc1], '%s e. CC' % GV)
    x1r = D(w, As, 'abscld', [e1c], '%s e. RR' % X1); x2r = D(w, As, 'abscld', [gvc], '%s e. RR' % X2); x3r = D(w, As, 'abscld', [e2c], '%s e. RR' % X3)
    b1r = D(w, As, 'breqtrd', [b1, D(w, As, 'oveq2d', [n1a], '( ( M x. %s ) x. ( abs ` ( %s - %s ) ) ) = ( ( M x. %s ) x. ( %s - E ) )' % (Q, NR, U, Q, AE))], '%s <_ ( ( M x. %s ) x. ( %s - E ) )' % (X1, Q, AE))
    b2r = D(w, As, 'breqtrd', [b2, D(w, As, 'oveq2d', [n2a], '( ( M x. %s ) x. ( abs ` ( %s - %s ) ) ) = ( ( M x. %s ) x. ( E + %s ) )' % (Q, Wt, R_, Q, AE))], '%s <_ ( ( M x. %s ) x. ( E + %s ) )' % (X3, Q, AE))
    b3r = D(w, As, 'eqbrtrd', [D(w, As, 'abssubd', [gc1c, vc1], '%s = ( abs ` ( %s - %s ) )' % (X2, V, G1)), b3], '%s <_ ( %s x. %s )' % (X2, K8, P))
    tot = lin.linarith(w, As, [b1r, b2r, b3r, fq], '( %s + ( %s + %s ) ) <_ ( ( %s + %s ) x. %s )' % (X1, X2, X3, EM, K8, P),
                       leaves={X1: x1r, X2: x2r, X3: x3r, 'M': mr1, Q: qr, P: pr_, AE: aer1, 'E': er1, K8: k8r1}, products=True)
    # | F ` s - V | <_ X1 + ( X2 + X3 )
    FV = '( %s - %s )' % (FS, V)
    a1 = D(w, As, 'oveq1d', [fsplit], '%s = ( ( %s + ( %s + %s ) ) - %s )' % (FV, E1, G1, E2, V))
    a2 = D(w, As, 'addsubassd', [e1c, D(w, As, 'addcld', [gc1c, e2c], '( %s + %s ) e. CC' % (G1, E2)), vc1], '( ( %s + ( %s + %s ) ) - %s ) = ( %s + ( ( %s + %s ) - %s ) )' % (E1, G1, E2, V, E1, G1, E2, V))
    a3 = D(w, As, 'oveq2d', [D(w, As, 'addsubd', [gc1c, e2c, vc1], '( ( %s + %s ) - %s ) = ( %s + %s )' % (G1, E2, V, GV, E2))], '( %s + ( ( %s + %s ) - %s ) ) = ( %s + ( %s + %s ) )' % (E1, G1, E2, V, E1, GV, E2))
    fv_ = D(w, As, 'eqtrd', [D(w, As, 'eqtrd', [a1, a2], '%s = ( %s + ( ( %s + %s ) - %s ) )' % (FV, E1, G1, E2, V)), a3], '%s = ( %s + ( %s + %s ) )' % (FV, E1, GV, E2))
    t1 = D(w, As, 'abstrid', [e1c, D(w, As, 'addcld', [gvc, e2c], '( %s + %s ) e. CC' % (GV, E2))], '( abs ` ( %s + ( %s + %s ) ) ) <_ ( %s + ( abs ` ( %s + %s ) ) )' % (E1, GV, E2, X1, GV, E2))
    t2 = D(w, As, 'abstrid', [gvc, e2c], '( abs ` ( %s + %s ) ) <_ ( %s + %s )' % (GV, E2, X2, X3))
    t3 = D(w, As, 'mpbid', [t2, D(w, As, 'leadd2d', [D(w, As, 'abscld', [D(w, As, 'addcld', [gvc, e2c], '( %s + %s ) e. CC' % (GV, E2))], '( abs ` ( %s + %s ) ) e. RR' % (GV, E2)),
                                                      D(w, As, 'readdcld', [x2r, x3r], '( %s + %s ) e. RR' % (X2, X3)), x1r],
                                   '( ( abs ` ( %s + %s ) ) <_ ( %s + %s ) <-> ( %s + ( abs ` ( %s + %s ) ) ) <_ ( %s + ( %s + %s ) ) )' % (GV, E2, X2, X3, X1, GV, E2, X1, X2, X3))],
            '( %s + ( abs ` ( %s + %s ) ) ) <_ ( %s + ( %s + %s ) )' % (X1, GV, E2, X1, X2, X3))
    ab = D(w, As, 'eqbrtrd', [D(w, As, 'fveq2d', [fv_], '( abs ` %s ) = ( abs ` ( %s + ( %s + %s ) ) )' % (FV, E1, GV, E2)),
                              D(w, As, 'letrd', [D(w, As, 'abscld', [D(w, As, 'addcld', [e1c, D(w, As, 'addcld', [gvc, e2c], '( %s + %s ) e. CC' % (GV, E2))], '( %s + ( %s + %s ) ) e. CC' % (E1, GV, E2))], '( abs ` ( %s + ( %s + %s ) ) ) e. RR' % (E1, GV, E2)),
                                                 D(w, As, 'readdcld', [x1r, D(w, As, 'abscld', [D(w, As, 'addcld', [gvc, e2c], '( %s + %s ) e. CC' % (GV, E2))], '( abs ` ( %s + %s ) ) e. RR' % (GV, E2))], '( %s + ( abs ` ( %s + %s ) ) ) e. RR' % (X1, GV, E2)),
                                                 D(w, As, 'readdcld', [x1r, D(w, As, 'readdcld', [x2r, x3r], '( %s + %s ) e. RR' % (X2, X3))], '( %s + ( %s + %s ) ) e. RR' % (X1, X2, X3)), t1, t3],
                                '( abs ` ( %s + ( %s + %s ) ) ) <_ ( %s + ( %s + %s ) )' % (E1, GV, E2, X1, X2, X3))], '( abs ` %s ) <_ ( %s + ( %s + %s ) )' % (FV, X1, X2, X3))
    fin = D(w, As, 'letrd', [D(w, As, 'abscld', [D(w, As, 'subcld', [D(w, As, 'eqeltrd', [fvs, D(w, As, 'eqeltrd', [fv0, lc_(U, Wt, ur, wr)], '%s e. CC' % LT(TR, 'C', 's'))], '%s e. CC' % FS), vc1], '%s e. CC' % FV)], '( abs ` %s ) e. RR' % FV),
                             D(w, As, 'readdcld', [x1r, D(w, As, 'readdcld', [x2r, x3r], '( %s + %s ) e. RR' % (X2, X3))], '( %s + ( %s + %s ) ) e. RR' % (X1, X2, X3)),
                             D(w, As, 'remulcld', [D(w, As, 'readdcld', [emr1, k8r1], '( %s + %s ) e. RR' % (EM, K8)), pr_], '( ( %s + %s ) x. %s ) e. RR' % (EM, K8, P)), ab, tot],
            '( abs ` %s ) <_ ( ( %s + %s ) x. %s )' % (FV, EM, K8, P))
    # ( ( EM + K8 ) x. P ) = Cc x. ( ( 2 ^c -u ( s / 4 ) ) ^c 1 )
    S4 = '( 2 ^c -u ( s / 4 ) )'
    ae4 = '( %s / 4 )' % AE
    ae4r = D(w, As, 'redivcld', [aer1, cst(w, As, '4re', '4 e. RR'), cst(w, As, '4ne0', '4 =/= 0')], '%s e. RR' % ae4)
    s4r = D(w, As, 'redivcld', [sr, cst(w, As, '4re', '4 e. RR'), cst(w, As, '4ne0', '4 =/= 0')], '( s / 4 ) e. RR')
    ex_ = lin.lineq(w, As, '-u ( %s / 4 )' % R_, '( %s + -u ( s / 4 ) )' % ae4, leaves={'s': sr, AE: aer1})
    pe = D(w, As, 'eqtrd', [D(w, As, 'oveq2d', [ex_], '%s = ( 2 ^c ( %s + -u ( s / 4 ) ) )' % (P, ae4)),
                            D(w, As, 'cxpaddd', [cst(w, As, '2cn', '2 e. CC'), cst(w, As, '2ne0', '2 =/= 0'), D(w, As, 'recnd', [ae4r], '%s e. CC' % ae4), D(w, As, 'recnd', [D(w, As, 'renegcld', [s4r], '-u ( s / 4 ) e. RR')], '-u ( s / 4 ) e. CC')],
                              '( 2 ^c ( %s + -u ( s / 4 ) ) ) = ( %s x. %s )' % (ae4, E4, S4))], '%s = ( %s x. %s )' % (P, E4, S4))
    s4c = D(w, As, 'recnd', [D(w, As, 'rpred', [D(w, As, 'rpcxpcld', [cst(w, As, '2rp', '2 e. RR+'), D(w, As, 'renegcld', [s4r], '-u ( s / 4 ) e. RR')], '%s e. RR+' % S4)], '%s e. RR' % S4)], '%s e. CC' % S4)
    ekc = D(w, As, 'recnd', [D(w, As, 'readdcld', [emr1, k8r1], '( %s + %s ) e. RR' % (EM, K8))], '( %s + %s ) e. CC' % (EM, K8))
    e4c = D(w, As, 'recnd', [L1(e4r, '%s e. RR' % E4)], '%s e. CC' % E4)
    q1 = D(w, As, 'eqtrd', [D(w, As, 'oveq2d', [pe], '( ( %s + %s ) x. %s ) = ( ( %s + %s ) x. ( %s x. %s ) )' % (EM, K8, P, EM, K8, E4, S4)),
                            D(w, As, 'eqcomd', [D(w, As, 'mulassd', [ekc, e4c, s4c], '( %s x. %s ) = ( ( %s + %s ) x. ( %s x. %s ) )' % (Cc, S4, EM, K8, E4, S4))], '( ( %s + %s ) x. ( %s x. %s ) ) = ( %s x. %s )' % (EM, K8, E4, S4, Cc, S4))],
           '( ( %s + %s ) x. %s ) = ( %s x. %s )' % (EM, K8, P, Cc, S4))
    q2 = D(w, As, 'eqtr4d', [q1, D(w, As, 'oveq2d', [D(w, As, 'cxp1d', [s4c], '( %s ^c 1 ) = %s' % (S4, S4))], '( %s x. ( %s ^c 1 ) ) = ( %s x. %s )' % (Cc, S4, Cc, S4))],
           '( ( %s + %s ) x. %s ) = ( %s x. ( %s ^c 1 ) )' % (EM, K8, P, Cc, S4))
    bnd = D(w, As, 'breqtrd', [fin, q2], '( abs ` %s ) <_ ( %s x. ( %s ^c 1 ) )' % (FV, Cc, S4))
    Bs = '( %s <_ s -> ( abs ` %s ) <_ ( %s x. ( %s ^c 1 ) ) )' % (Yv, FV, Cc, S4)
    alls = w.s([w.s([bnd], 'ex', '( ( %s /\\ s e. RR+ ) -> %s )' % (ph, Bs))], 'ralrimiva', '( %s -> A. s e. RR+ %s )' % (ph, Bs))
    TLA = '( ( %s e. CC /\\ %s e. RR ) /\\ ( 1 e. RR+ /\\ %s e. RR ) /\\ ( %s : RR+ --> CC /\\ A. s e. RR+ %s ) )' % (V, Cc, Yv, Fm, Bs)
    w.qed([w.s([w.s([vc, ccr], 'jca', '( %s -> ( %s e. CC /\\ %s e. RR ) )' % (ph, V, Cc)), w.s([cst(w, ph, '1rp', '1 e. RR+'), yvr], 'jca', '( %s -> ( 1 e. RR+ /\\ %s e. RR ) )' % (ph, Yv)),
                w.s([fm, alls], 'jca', '( %s -> ( %s : RR+ --> CC /\\ A. s e. RR+ %s ) )' % (ph, Fm, Bs))], '3jca', '( %s -> %s )' % (ph, TLA)), w.inst('zl3tl')], 'syl', S['zl3vtr'])
    go(w, only)


# ---------------------------------------------------------------- zl3csh
SBc = lambda v: '( ( abs ` ( Re ` %s ) ) <_ ( abs ` A ) -> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) )' % (v, v, v)


def sb_at(w, A_, sb, Z, zc):
    """( A_ -> SBc(Z) ) from sb: ( A_ -> A. c e. CC SBc(c) )"""
    E = 'c = %s' % Z
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    sub = D(w, E, 'imbi12d', [D(w, E, 'breq1d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Re ` c ) = ( Re ` %s )' % Z)], '( abs ` ( Re ` c ) ) = ( abs ` ( Re ` %s ) )' % Z)],
                                 '( ( abs ` ( Re ` c ) ) <_ ( abs ` A ) <-> ( abs ` ( Re ` %s ) ) <_ ( abs ` A ) )' % Z),
                              D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( G ` c ) = ( G ` %s )' % Z)], '( abs ` ( G ` c ) ) = ( abs ` ( G ` %s ) )' % Z),
                                                  D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Im ` c ) = ( Im ` %s )' % Z)], '( abs ` ( Im ` c ) ) = ( abs ` ( Im ` %s ) )' % Z)],
                                                                                         '-u ( abs ` ( Im ` c ) ) = -u ( abs ` ( Im ` %s ) )' % Z)], '( 2 ^c -u ( abs ` ( Im ` c ) ) ) = ( 2 ^c -u ( abs ` ( Im ` %s ) ) )' % Z)],
                                                    '( M x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) = ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) )' % Z)],
                                '( ( abs ` ( G ` c ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) <-> ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) )' % (Z, Z))],
            '( %s <-> %s )' % (SBc('c'), SBc(Z)))
    return w.s([sub, sb, zc], 'rspcdva', '( %s -> %s )' % (A_, SBc(Z)))


if __name__ == '__main__' and (not only or 'zl3csh' in only):
    w = W('zl3csh', 'A complex shift of an entire function with strip decay does not change the limit of its integrals along the imaginary axis.')
    ph, concl = ante_of(S['zl3csh'])
    ar = w.s([], 'simpll', '( %s -> A e. RR )' % ph); er = w.s([], 'simplr', '( %s -> E e. RR )' % ph)
    gent = w.s([], 'simprl', '( %s -> %s )' % (ph, GENT)); gc = w.s([gent], 'simpld', '( %s -> G e. ( CC -cn-> CC ) )' % ph)
    mr = w.s([], 'simprrl', '( %s -> M e. RR )' % ph)
    SB = 'A. c e. CC %s' % SBc('c')
    sb = w.s([], 'simprrr', '( %s -> %s )' % (ph, SB))
    ac = D(w, ph, 'recnd', [ar], 'A e. CC'); ec = D(w, ph, 'recnd', [er], 'E e. CC'); ic = cst(w, ph, 'ax-icn', '_i e. CC')
    gf = w.s([gc, w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % ph)
    aar = D(w, ph, 'abscld', [ac], '( abs ` A ) e. RR')
    # BL ( A )
    Ab = '( %s /\\ b e. RR )' % ph
    br = w.s([], 'simpr', '( %s -> b e. RR )' % Ab)
    ar1 = w.s([ar], 'adantr', '( %s -> A e. RR )' % Ab)
    Z = CP('A', 'b')
    zc = D(w, Ab, 'addcld', [w.s([ac], 'adantr', '( %s -> A e. CC )' % Ab), D(w, Ab, 'mulcld', [cst(w, Ab, 'ax-icn', '_i e. CC'), D(w, Ab, 'recnd', [br], 'b e. CC')], '( _i x. b ) e. CC')], '%s e. CC' % Z)
    sz = sb_at(w, Ab, w.s([sb], 'adantr', '( %s -> %s )' % (Ab, SB)), Z, zc)
    rz = D(w, Ab, 'crred', [ar1, br], '( Re ` %s ) = A' % Z); iz = D(w, Ab, 'crimd', [ar1, br], '( Im ` %s ) = b' % Z)
    c1 = D(w, Ab, 'eqled', [D(w, Ab, 'fveq2d', [rz], '( abs ` ( Re ` %s ) ) = ( abs ` A )' % Z)], '( abs ` ( Re ` %s ) ) <_ ( abs ` A )' % Z)
    bz = D(w, Ab, 'mpd', [c1, sz], '( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) )' % (Z, Z))
    bz2 = D(w, Ab, 'breqtrd', [bz, D(w, Ab, 'oveq2d', [D(w, Ab, 'oveq2d', [D(w, Ab, 'negeqd', [D(w, Ab, 'fveq2d', [iz], '( abs ` ( Im ` %s ) ) = ( abs ` b )' % Z)], '-u ( abs ` ( Im ` %s ) ) = -u ( abs ` b )' % Z)],
                                                                        '( 2 ^c -u ( abs ` ( Im ` %s ) ) ) = ( 2 ^c -u ( abs ` b ) )' % Z)], '( M x. ( 2 ^c -u ( abs ` ( Im ` %s ) ) ) ) = ( M x. ( 2 ^c -u ( abs ` b ) ) )' % Z)],
             '( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` b ) ) )' % Z)
    bla = w.s([bz2], 'ralrimiva', '( %s -> %s )' % (ph, BLC('A')))
    TRA = TRN('G', '( _i x. E )')
    vt = D(w, ph, 'syl', [w.s([w.s([ar, er], 'jca', '( %s -> ( A e. RR /\\ E e. RR ) )' % ph), w.s([w.s([gc, mr], 'jca', '( %s -> ( G e. ( CC -cn-> CC ) /\\ M e. RR ) )' % ph), bla], 'jca',
                                                                                                  '( %s -> ( ( G e. ( CC -cn-> CC ) /\\ M e. RR ) /\\ %s ) )' % (ph, BLC('A')))], 'jca',
                               '( %s -> ( ( A e. RR /\\ E e. RR ) /\\ ( ( G e. ( CC -cn-> CC ) /\\ M e. RR ) /\\ %s ) ) )' % (ph, BLC('A'))), w.inst('zl3vtr')],
           '( t e. RR+ |-> %s ) ~~>r %s' % (LT(TRA, 'A', 't'), VL('G', 'A')))
    # the two mappings agree
    At = '( %s /\\ t e. RR+ )' % ph
    tc = D(w, At, 'rpcnd', [w.s([], 'simpr', '( %s -> t e. RR+ )' % At)], 't e. CC')
    ntc = D(w, At, 'negcld', [tc], '-u t e. CC')
    ac1 = w.s([ac], 'adantr', '( %s -> A e. CC )' % At); ec1 = w.s([ec], 'adantr', '( %s -> E e. CC )' % At); ic1 = cst(w, At, 'ax-icn', '_i e. CC')
    gf1 = w.s([gf], 'adantr', '( %s -> G : CC --> CC )' % At)
    AE_ = CP('A', 'E'); IE = '( _i x. E )'
    aec = D(w, At, 'addcld', [ac1, D(w, At, 'mulcld', [ic1, ec1], '%s e. CC' % IE)], '%s e. CC' % AE_)
    iec = D(w, At, 'mulcld', [ic1, ec1], '%s e. CC' % IE)
    def ltr(G_, C_, S_, sc_, ccx):
        P = CP(C_, '-u t'); Q = CP(C_, 't')
        pc = D(w, At, 'addcld', [ccx, D(w, At, 'mulcld', [ic1, ntc], '( _i x. -u t ) e. CC')], '%s e. CC' % P)
        qc = D(w, At, 'addcld', [ccx, D(w, At, 'mulcld', [ic1, tc], '( _i x. t ) e. CC')], '%s e. CC' % Q)
        return D(w, At, 'syl', [w.s([w.s([pc, qc, sc_], '3jca', '( %s -> ( %s e. CC /\\ %s e. CC /\\ %s e. CC ) )' % (At, P, Q, S_)), gf1], 'jca',
                                    '( %s -> ( ( %s e. CC /\\ %s e. CC /\\ %s e. CC ) /\\ G : CC --> CC ) )' % (At, P, Q, S_)), w.inst('zl3ltr')],
                 '%s = %s' % (LT(TRN('G', S_), C_, 't'), LI('G', '( %s + %s )' % (P, S_), '( %s + %s )' % (Q, S_))))
    l0 = ltr('G', '0', AE_, aec, cst(w, At, '0cn', '0 e. CC'))
    la = ltr('G', 'A', IE, iec, ac1)
    def ep(X, xc):
        IX = '( _i x. %s )' % X
        ixc = D(w, At, 'mulcld', [ic1, xc], '%s e. CC' % IX)
        l = D(w, At, 'eqtrd', [D(w, At, 'oveq1d', [D(w, At, 'addlidd', [ixc], '( 0 + %s ) = %s' % (IX, IX))], '( ( 0 + %s ) + %s ) = ( %s + %s )' % (IX, AE_, IX, AE_)),
                               D(w, At, 'add12d', [ixc, ac1, iec], '( %s + %s ) = ( A + ( %s + %s ) )' % (IX, AE_, IX, IE))], '( ( 0 + %s ) + %s ) = ( A + ( %s + %s ) )' % (IX, AE_, IX, IE))
        r = D(w, At, 'addassd', [ac1, ixc, iec], '( ( A + %s ) + %s ) = ( A + ( %s + %s ) )' % (IX, IE, IX, IE))
        return D(w, At, 'eqtr4d', [l, r], '( ( 0 + %s ) + %s ) = ( ( A + %s ) + %s )' % (IX, AE_, IX, IE))
    e1 = ep('-u t', ntc); e2 = ep('t', tc)
    P0, Q0 = '( %s + %s )' % (CP('0', '-u t'), AE_), '( %s + %s )' % (CP('0', 't'), AE_)
    PA, QA = '( %s + %s )' % (CP('A', '-u t'), IE), '( %s + %s )' % (CP('A', 't'), IE)
    li = D(w, At, 'oveq2d', [D(w, At, 'opeq12d', [e1, e2], '<. %s , %s >. = <. %s , %s >.' % (P0, Q0, PA, QA))], '%s = %s' % (LI('G', P0, Q0), LI('G', PA, QA)))
    eq_t = D(w, At, 'eqtr4d', [D(w, At, 'eqtrd', [l0, li], '%s = %s' % (LT(TRN('G', AE_), '0', 't'), LI('G', PA, QA))), la], '%s = %s' % (LT(TRN('G', AE_), '0', 't'), LT(TRA, 'A', 't')))
    meq = w.s([eq_t], 'mpteq2dva', '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s ) )' % (ph, LT(TRN('G', AE_), '0', 't'), LT(TRA, 'A', 't')))
    # VL ( G , A ) = VL ( G , 0 ): three cases
    def shv(Ac, lo, hi, lor, hir, lt_, lo_le, hi_le):
        """( Ac -> VL(G,hi) = VL(G,lo) ); lo_le, hi_le: functions giving, in the b-context, -u |A| <_ Re b and Re b <_ |A|"""
        Acb = '( %s /\\ b e. CC )' % Ac
        Ah = '( %s /\\ ( %s <_ ( Re ` b ) /\\ ( Re ` b ) <_ %s ) )' % (Acb, lo, hi)
        bc = w.s([], 'simpr', '( %s -> b e. CC )' % Acb)
        sbb = sb_at(w, Acb, w.s([sb], 'ad2antrr', '( %s -> %s )' % (Acb, SB)), 'b', bc)
        rb = D(w, Ah, 'recld', [w.s([bc], 'adantr', '( %s -> b e. CC )' % Ah)], '( Re ` b ) e. RR')
        aa = w.s([aar], 'ad3antrrr', '( %s -> ( abs ` A ) e. RR )' % Ah)
        l1 = lo_le(Ah, rb, aa); l2 = hi_le(Ah, rb, aa)
        ab = D(w, Ah, 'mpbird', [w.s([l1, l2], 'jca', '( %s -> ( -u ( abs ` A ) <_ ( Re ` b ) /\\ ( Re ` b ) <_ ( abs ` A ) ) )' % Ah),
                                 D(w, Ah, 'absled', [rb, aa], '( ( abs ` ( Re ` b ) ) <_ ( abs ` A ) <-> ( -u ( abs ` A ) <_ ( Re ` b ) /\\ ( Re ` b ) <_ ( abs ` A ) ) )')],
                '( abs ` ( Re ` b ) ) <_ ( abs ` A )')
        bnd = D(w, Ah, 'mpd', [ab, w.s([sbb], 'adantr', '( %s -> %s )' % (Ah, SBc('b')))], '( abs ` ( G ` b ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) )')
        HB = 'A. b e. CC ( ( %s <_ ( Re ` b ) /\\ ( Re ` b ) <_ %s ) -> ( abs ` ( G ` b ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) ) )' % (lo, hi)
        hb = w.s([w.s([bnd], 'ex', '( %s -> ( ( %s <_ ( Re ` b ) /\\ ( Re ` b ) <_ %s ) -> ( abs ` ( G ` b ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) ) ) )' % (Acb, lo, hi))], 'ralrimiva', '( %s -> %s )' % (Ac, HB))
        pre = w.s([w.s([w.s([lor, hir], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (Ac, lo, hi)), lt_], 'jca', '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ %s < %s ) )' % (Ac, lo, hi, lo, hi)),
                   w.s([w.s([gent], 'adantr', '( %s -> %s )' % (Ac, GENT)), w.s([w.s([mr], 'adantr', '( %s -> M e. RR )' % Ac), hb], 'jca', '( %s -> ( M e. RR /\\ %s ) )' % (Ac, HB))], 'jca',
                       '( %s -> ( %s /\\ ( M e. RR /\\ %s ) ) )' % (Ac, GENT, HB))], 'jca', '( %s -> ( ( ( %s e. RR /\\ %s e. RR ) /\\ %s < %s ) /\\ ( %s /\\ ( M e. RR /\\ %s ) ) ) )' % (Ac, lo, hi, lo, hi, GENT, HB))
        return w.s([w.s([pre, w.inst('zl3shv')], 'syl', '( %s -> ( %s = %s /\\ %s e. CC ) )' % (Ac, VL('G', hi), VL('G', lo), VL('G', lo)))], 'simpld', '( %s -> %s = %s )' % (Ac, VL('G', hi), VL('G', lo)))
    V0, VA = VL('G', '0'), VL('G', 'A')
    # case A < 0: lo = A, hi = 0
    A1 = '( %s /\\ A < 0 )' % ph
    def lo1(Ah, rb, aa):
        a_ = w.s([ar], 'ad3antrrr', '( %s -> A e. RR )' % Ah)
        na = D(w, Ah, 'breqtrd', [D(w, Ah, 'leabsd', [D(w, Ah, 'renegcld', [a_], '-u A e. RR')], '-u A <_ ( abs ` -u A )'),
                                  D(w, Ah, 'absnegd', [D(w, Ah, 'recnd', [a_], 'A e. CC')], '( abs ` -u A ) = ( abs ` A )')], '-u A <_ ( abs ` A )')
        return lin.linarith(w, Ah, [na, w.s([], 'simprl', '( %s -> A <_ ( Re ` b ) )' % Ah)], '-u ( abs ` A ) <_ ( Re ` b )', leaves={'A': a_, '( abs ` A )': aa, '( Re ` b )': rb})
    def hi1(Ah, rb, aa):
        a_ = w.s([ar], 'ad3antrrr', '( %s -> A e. RR )' % Ah)
        a0 = D(w, Ah, 'absge0d', [D(w, Ah, 'recnd', [a_], 'A e. CC')], '0 <_ ( abs ` A )')
        return lin.linarith(w, Ah, [a0, w.s([], 'simprr', '( %s -> ( Re ` b ) <_ 0 )' % Ah)], '( Re ` b ) <_ ( abs ` A )', leaves={'( abs ` A )': aa, '( Re ` b )': rb})
    c1 = D(w, A1, 'eqcomd', [shv(A1, 'A', '0', w.s([ar], 'adantr', '( %s -> A e. RR )' % A1), cst(w, A1, '0re', '0 e. RR'), w.s([], 'simpr', '( %s -> A < 0 )' % A1), lo1, hi1)], '%s = %s' % (VA, V0))
    A3 = '( %s /\\ 0 < A )' % ph
    def lo3(Ah, rb, aa):
        a_ = w.s([ar], 'ad3antrrr', '( %s -> A e. RR )' % Ah)
        a0 = D(w, Ah, 'absge0d', [D(w, Ah, 'recnd', [a_], 'A e. CC')], '0 <_ ( abs ` A )')
        return lin.linarith(w, Ah, [a0, w.s([], 'simprl', '( %s -> 0 <_ ( Re ` b ) )' % Ah)], '-u ( abs ` A ) <_ ( Re ` b )', leaves={'( abs ` A )': aa, '( Re ` b )': rb})
    def hi3(Ah, rb, aa):
        a_ = w.s([ar], 'ad3antrrr', '( %s -> A e. RR )' % Ah)
        la_ = D(w, Ah, 'leabsd', [a_], 'A <_ ( abs ` A )')
        return lin.linarith(w, Ah, [la_, w.s([], 'simprr', '( %s -> ( Re ` b ) <_ A )' % Ah)], '( Re ` b ) <_ ( abs ` A )', leaves={'A': a_, '( abs ` A )': aa, '( Re ` b )': rb})
    c3 = shv(A3, '0', 'A', cst(w, A3, '0re', '0 e. RR'), w.s([ar], 'adantr', '( %s -> A e. RR )' % A3), w.s([], 'simpr', '( %s -> 0 < A )' % A3), lo3, hi3)
    A2 = '( %s /\\ A = 0 )' % ph
    Ez = 'A = 0'
    e_ = w.s([], 'id', '( %s -> %s )' % (Ez, Ez))
    Ezt = '( %s /\\ t e. RR+ )' % Ez
    ez1 = w.s([e_], 'adantr', '( %s -> %s )' % (Ezt, Ez))
    lz = D(w, Ezt, 'oveq2d', [D(w, Ezt, 'opeq12d', [D(w, Ezt, 'oveq1d', [ez1], '%s = %s' % (CP('A', '-u t'), CP('0', '-u t'))), D(w, Ezt, 'oveq1d', [ez1], '%s = %s' % (CP('A', 't'), CP('0', 't')))],
                                        '<. %s , %s >. = <. %s , %s >.' % (CP('A', '-u t'), CP('A', 't'), CP('0', '-u t'), CP('0', 't')))], '%s = %s' % (LT('G', 'A', 't'), LT('G', '0', 't')))
    vz = D(w, Ez, 'fveq2d', [w.s([lz], 'mpteq2dva', '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s ) )' % (Ez, LT('G', 'A', 't'), LT('G', '0', 't')))], '%s = %s' % (VA, V0))
    c2 = w.s([vz], 'adantl', '( %s -> %s = %s )' % (A2, VA, V0))
    veq = w.s([c1, c2, c3, D(w, ph, 'syl2anc', [ar, cst(w, ph, '0re', '0 e. RR'), w.inst('lttri4')], '( A < 0 \\/ A = 0 \\/ 0 < A )')], 'mpjao3dan', '( %s -> %s = %s )' % (ph, VA, V0))
    w.qed([D(w, ph, 'eqbrtrd', [meq, vt], '( t e. RR+ |-> %s ) ~~>r %s' % (LT(TRN('G', AE_), '0', 't'), VA)), veq], 'breqtrd', S['zl3csh'])
    go(w, only)


# ---------------------------------------------------------------- zl3scl
if __name__ == '__main__' and (not only or 'zl3scl' in only):
    w = W('zl3scl', 'Scaling the variable by ` L > 0 ` divides the limit along the imaginary axis by ` L `.')
    ph, concl = ante_of(S['zl3scl'])
    lp = w.s([], 'simpl', '( %s -> L e. RR+ )' % ph); gc = w.s([], 'simprll', '( %s -> G e. ( CC -cn-> CC ) )' % ph)
    mr = w.s([], 'simprlr', '( %s -> M e. RR )' % ph); bl = w.s([], 'simprr', '( %s -> %s )' % (ph, BLC('0')))
    zr = cst(w, ph, '0re', '0 e. RR'); z0c = cst(w, ph, '0cn', '0 e. CC')
    gf = w.s([gc, w.inst('cncff')], 'syl', '( %s -> G : CC --> CC )' % ph)
    m0 = m0_of(w, ph, bl, '0', z0c, gf, mr)
    zc, ZC = z6ctx(w, ph, bl, '0', zr, gc, mr, m0)
    V = VL('G', '0')
    vex = D(w, ph, 'syl', [zc, w.inst('z6vlex')], '( t e. RR+ |-> %s ) ~~>r %s' % (LT('G', '0', 't'), V))
    vc = D(w, ph, 'syl', [vex, w.inst('rlimcl')], '%s e. CC' % V)
    lr = D(w, ph, 'rpred', [lp], 'L e. RR'); lc = D(w, ph, 'rpcnd', [lp], 'L e. CC'); ln = D(w, ph, 'rpne0d', [lp], 'L =/= 0')
    GLy = '( y e. CC |-> ( G ` ( L x. y ) ) )'
    Fm = '( t e. RR+ |-> %s )' % LT(GLy, '0', 't')
    def val(A_, T, tr, lift):
        tc = D(w, A_, 'recnd', [tr], '%s e. CC' % T)
        ic = cst(w, A_, 'ax-icn', '_i e. CC'); z0 = cst(w, A_, '0cn', '0 e. CC')
        lc_ = w.s([lc], lift, '( %s -> L e. CC )' % A_); ln_ = w.s([ln], lift, '( %s -> L =/= 0 )' % A_); gc_ = w.s([gc], lift, '( %s -> G e. ( CC -cn-> CC ) )' % A_)
        P, Q = CP('0', '-u %s' % T), CP('0', T)
        ntc = D(w, A_, 'negcld', [tc], '-u %s e. CC' % T)
        pc = D(w, A_, 'addcld', [z0, D(w, A_, 'mulcld', [ic, ntc], '( _i x. -u %s ) e. CC' % T)], '%s e. CC' % P)
        qc = D(w, A_, 'addcld', [z0, D(w, A_, 'mulcld', [ic, tc], '( _i x. %s ) e. CC' % T)], '%s e. CC' % Q)
        l = D(w, A_, 'syl', [w.s([w.s([pc, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A_, P, Q)), w.s([lc_, ln_], 'jca', '( %s -> ( L e. CC /\\ L =/= 0 ) )' % A_), gc_], '3jca',
                                 '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( L e. CC /\\ L =/= 0 ) /\\ G e. ( CC -cn-> CC ) ) )' % (A_, P, Q)), w.inst('zl3lsc')],
              '%s = ( %s / L )' % (LT(GLy, '0', T), LI('G', '( L x. %s )' % P, '( L x. %s )' % Q)))
        LT_ = '( L x. %s )' % T
        def lm(X, xc, Y):
            """( L x. ( 0 + ( _i x. X ) ) ) = ( 0 + ( _i x. Y ) ) where ( L x. X ) = Y"""
            ix = D(w, A_, 'mulcld', [ic, xc], '( _i x. %s ) e. CC' % X)
            a = D(w, A_, 'adddid', [lc_, z0, ix], '( L x. %s ) = ( ( L x. 0 ) + ( L x. ( _i x. %s ) ) )' % (CP('0', X), X))
            b = D(w, A_, 'oveq12d', [D(w, A_, 'mul01d', [lc_], '( L x. 0 ) = 0'), D(w, A_, 'mul12d', [lc_, ic, xc], '( L x. ( _i x. %s ) ) = ( _i x. ( L x. %s ) )' % (X, X))],
                  '( ( L x. 0 ) + ( L x. ( _i x. %s ) ) ) = %s' % (X, CP('0', '( L x. %s )' % X)))
            return D(w, A_, 'eqtrd', [a, b], '( L x. %s ) = %s' % (CP('0', X), CP('0', '( L x. %s )' % X)))
        e2 = lm(T, tc, None)
        e1a = lm('-u %s' % T, ntc, None)
        e1b = D(w, A_, 'oveq2d', [D(w, A_, 'oveq2d', [D(w, A_, 'mulneg2d', [lc_, tc], '( L x. -u %s ) = -u %s' % (T, LT_))], '( _i x. ( L x. -u %s ) ) = ( _i x. -u %s )' % (T, LT_))],
                '%s = %s' % (CP('0', '( L x. -u %s )' % T), CP('0', '-u %s' % LT_)))
        e1 = D(w, A_, 'eqtrd', [e1a, e1b], '( L x. %s ) = %s' % (P, CP('0', '-u %s' % LT_)))
        r = D(w, A_, 'oveq1d', [D(w, A_, 'oveq2d', [D(w, A_, 'opeq12d', [e1, e2], '<. ( L x. %s ) , ( L x. %s ) >. = <. %s , %s >.' % (P, Q, CP('0', '-u %s' % LT_), CP('0', LT_)))],
                                                    '%s = %s' % (LI('G', '( L x. %s )' % P, '( L x. %s )' % Q), LT('G', '0', LT_)))], '( %s / L ) = ( %s / L )' % (LI('G', '( L x. %s )' % P, '( L x. %s )' % Q), LT('G', '0', LT_)))
        v = D(w, A_, 'eqtrd', [l, r], '%s = ( %s / L )' % (LT(GLy, '0', T), LT('G', '0', LT_)))
        ltr_ = D(w, A_, 'remulcld', [w.s([lr], lift, '( %s -> L e. RR )' % A_), tr], '%s e. RR' % LT_)
        ltc = D(w, A_, 'recnd', [ltr_], '%s e. CC' % LT_)
        P2, Q2 = CP('0', '-u %s' % LT_), CP('0', LT_)
        p2c = D(w, A_, 'addcld', [z0, D(w, A_, 'mulcld', [ic, D(w, A_, 'negcld', [ltc], '-u %s e. CC' % LT_)], '( _i x. -u %s ) e. CC' % LT_)], '%s e. CC' % P2)
        q2c = D(w, A_, 'addcld', [z0, D(w, A_, 'mulcld', [ic, ltc], '( _i x. %s ) e. CC' % LT_)], '%s e. CC' % Q2)
        gcl = D(w, A_, 'syl', [seg_pre(w, A_, P2, Q2, p2c, q2c, gc_), w.inst('lintcl')], '%s e. CC' % LT('G', '0', LT_))
        return v, gcl, ltr_
    At = '( %s /\\ t e. RR+ )' % ph
    vt, gct, _ = val(At, 't', D(w, At, 'rpred', [w.s([], 'simpr', '( %s -> t e. RR+ )' % At)], 't e. RR'), 'adantr')
    fm = w.s([D(w, At, 'eqeltrd', [vt, D(w, At, 'divcld', [gct, w.s([lc], 'adantr', '( %s -> L e. CC )' % At), w.s([ln], 'adantr', '( %s -> L =/= 0 )' % At)], '( %s / L ) e. CC' % LT('G', '0', '( L x. t )'))],
                  '%s e. CC' % LT(GLy, '0', 't'))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (ph, Fm))
    IL = '( 1 / L )'
    As = '( ( %s /\\ s e. RR+ ) /\\ %s <_ s )' % (ph, IL)
    sp = w.s([], 'simplr', '( %s -> s e. RR+ )' % As); sr = D(w, As, 'rpred', [sp], 's e. RR')
    vs, gcs, lsr = val(As, 's', sr, 'ad2antrr')
    LS = '( L x. s )'
    lp1 = w.s([lp], 'ad2antrr', '( %s -> L e. RR+ )' % As); lr1 = D(w, As, 'rpred', [lp1], 'L e. RR'); lc1 = D(w, As, 'rpcnd', [lp1], 'L e. CC'); ln1 = D(w, As, 'rpne0d', [lp1], 'L =/= 0')
    ls1 = D(w, As, 'mpbid', [w.s([], 'simpr', '( %s -> %s <_ s )' % (As, IL)), D(w, As, 'ledivmuld', [cst(w, As, '1re', '1 e. RR'), sr, lp1], '( %s <_ s <-> 1 <_ %s )' % (IL, LS))], '1 <_ %s' % LS)
    lsp = D(w, As, 'rpmulcld', [lp1, sp], '%s e. RR+' % LS)
    zcs = w.s([zc], 'ad2antrr', '( %s -> %s )' % (As, ZC))
    GS = LT('G', '0', LS)
    b3 = D(w, As, 'syl', [w.s([zcs, w.s([lsp, ls1], 'jca', '( %s -> ( %s e. RR+ /\\ 1 <_ %s ) )' % (As, LS, LS))], 'jca', '( %s -> ( %s /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) )' % (As, ZC, LS, LS)), w.inst('z6vlt')],
           '( abs ` ( %s - %s ) ) <_ ( %s x. ( 2 ^c -u ( %s / 4 ) ) )' % (V, GS, K8, LS))
    vc1 = w.s([vc], 'ad2antrr', '( %s -> %s e. CC )' % (As, V))
    FS = '( %s ` s )' % Fm
    Et = 't = s'
    et = w.s([], 'id', '( %s -> %s )' % (Et, Et))
    sub = D(w, Et, 'oveq2d', [D(w, Et, 'opeq12d', [D(w, Et, 'oveq2d', [D(w, Et, 'oveq2d', [D(w, Et, 'negeqd', [et], '-u t = -u s')], '( _i x. -u t ) = ( _i x. -u s )')], '%s = %s' % (CP('0', '-u t'), CP('0', '-u s'))),
                                                   D(w, Et, 'oveq2d', [D(w, Et, 'oveq2d', [et], '( _i x. t ) = ( _i x. s )')], '%s = %s' % (CP('0', 't'), CP('0', 's')))],
                                       '<. %s , %s >. = <. %s , %s >.' % (CP('0', '-u t'), CP('0', 't'), CP('0', '-u s'), CP('0', 's')))], '%s = %s' % (LT(GLy, '0', 't'), LT(GLy, '0', 's')))
    fvs = w.s([sp, w.s([sub, w.s([], 'eqid', '%s = %s' % (Fm, Fm)), w.s([], 'ovex', '%s e. _V' % LT(GLy, '0', 's'))], 'fvmpt', '( s e. RR+ -> %s = %s )' % (FS, LT(GLy, '0', 's')))],
              'syl', '( %s -> %s = %s )' % (As, FS, LT(GLy, '0', 's')))
    VLd = '( %s / L )' % V
    fe = D(w, As, 'eqtrd', [fvs, vs], '%s = ( %s / L )' % (FS, GS))
    d1 = D(w, As, 'oveq1d', [fe], '( %s - %s ) = ( ( %s / L ) - %s )' % (FS, VLd, GS, VLd))
    d2 = D(w, As, 'eqcomd', [D(w, As, 'divsubdird', [gcs, vc1, lc1, ln1], '( ( %s - %s ) / L ) = ( ( %s / L ) - %s )' % (GS, V, GS, VLd))], '( ( %s / L ) - %s ) = ( ( %s - %s ) / L )' % (GS, VLd, GS, V))
    gvc = D(w, As, 'subcld', [gcs, vc1], '( %s - %s ) e. CC' % (GS, V))
    a1 = D(w, As, 'eqtrd', [D(w, As, 'fveq2d', [D(w, As, 'eqtrd', [d1, d2], '( %s - %s ) = ( ( %s - %s ) / L )' % (FS, VLd, GS, V))], '( abs ` ( %s - %s ) ) = ( abs ` ( ( %s - %s ) / L ) )' % (FS, VLd, GS, V)),
                            D(w, As, 'absdivd', [gvc, lc1, ln1], '( abs ` ( ( %s - %s ) / L ) ) = ( ( abs ` ( %s - %s ) ) / ( abs ` L ) )' % (GS, V, GS, V))],
           '( abs ` ( %s - %s ) ) = ( ( abs ` ( %s - %s ) ) / ( abs ` L ) )' % (FS, VLd, GS, V))
    a2 = D(w, As, 'oveq2d', [D(w, As, 'absidd', [lr1, D(w, As, 'rpge0d', [lp1], '0 <_ L')], '( abs ` L ) = L')], '( ( abs ` ( %s - %s ) ) / ( abs ` L ) ) = ( ( abs ` ( %s - %s ) ) / L )' % (GS, V, GS, V))
    a3 = D(w, As, 'oveq1d', [D(w, As, 'abssubd', [gcs, vc1], '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (GS, V, V, GS))], '( ( abs ` ( %s - %s ) ) / L ) = ( ( abs ` ( %s - %s ) ) / L )' % (GS, V, V, GS))
    aeq = D(w, As, 'eqtrd', [D(w, As, 'eqtrd', [a1, a2], '( abs ` ( %s - %s ) ) = ( ( abs ` ( %s - %s ) ) / L )' % (FS, VLd, GS, V)), a3], '( abs ` ( %s - %s ) ) = ( ( abs ` ( %s - %s ) ) / L )' % (FS, VLd, V, GS))
    l2 = w.s([cst(w, As, '2re', '2 e. RR'), cst(w, As, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % As)
    k8r = D(w, As, 'rerpdivcld', [D(w, As, 'remulcld', [cst(w, As, '8re', '8 e. RR'), w.s([mr], 'ad2antrr', '( %s -> M e. RR )' % As)], '( 8 x. M ) e. RR'), l2], '%s e. RR' % K8)
    ls4 = D(w, As, 'redivcld', [lsr, cst(w, As, '4re', '4 e. RR'), cst(w, As, '4ne0', '4 =/= 0')], '( %s / 4 ) e. RR' % LS)
    P = '( 2 ^c -u ( %s / 4 ) )' % LS
    pr_ = D(w, As, 'rpred', [D(w, As, 'rpcxpcld', [cst(w, As, '2rp', '2 e. RR+'), D(w, As, 'renegcld', [ls4], '-u ( %s / 4 ) e. RR' % LS)], '%s e. RR+' % P)], '%s e. RR' % P)
    kp = D(w, As, 'remulcld', [k8r, pr_], '( %s x. %s ) e. RR' % (K8, P))
    le1 = D(w, As, 'lediv1dd', [D(w, As, 'abscld', [D(w, As, 'subcld', [vc1, gcs], '( %s - %s ) e. CC' % (V, GS))], '( abs ` ( %s - %s ) ) e. RR' % (V, GS)), kp, lp1, b3],
            '( ( abs ` ( %s - %s ) ) / L ) <_ ( ( %s x. %s ) / L )' % (V, GS, K8, P))
    k8c = D(w, As, 'recnd', [k8r], '%s e. CC' % K8); pc_ = D(w, As, 'recnd', [pr_], '%s e. CC' % P)
    le2 = D(w, As, 'breqtrd', [le1, D(w, As, 'div23d', [k8c, pc_, lc1, ln1], '( ( %s x. %s ) / L ) = ( ( %s / L ) x. %s )' % (K8, P, K8, P))], '( ( abs ` ( %s - %s ) ) / L ) <_ ( ( %s / L ) x. %s )' % (V, GS, K8, P))
    S4 = '( 2 ^c -u ( s / 4 ) )'
    s4r = D(w, As, 'redivcld', [sr, cst(w, As, '4re', '4 e. RR'), cst(w, As, '4ne0', '4 =/= 0')], '( s / 4 ) e. RR')
    ex_ = lin.lineq(w, As, '-u ( %s / 4 )' % LS, '( -u ( s / 4 ) x. L )', leaves={'s': sr, 'L': lr1}, products=True)
    pe = D(w, As, 'eqtrd', [D(w, As, 'oveq2d', [ex_], '%s = ( 2 ^c ( -u ( s / 4 ) x. L ) )' % P),
                            D(w, As, 'cxpmuld', [cst(w, As, '2rp', '2 e. RR+'), D(w, As, 'renegcld', [s4r], '-u ( s / 4 ) e. RR'), lc1], '( 2 ^c ( -u ( s / 4 ) x. L ) ) = ( %s ^c L )' % S4)],
           '%s = ( %s ^c L )' % (P, S4))
    le3 = D(w, As, 'breqtrd', [le2, D(w, As, 'oveq2d', [pe], '( ( %s / L ) x. %s ) = ( ( %s / L ) x. ( %s ^c L ) )' % (K8, P, K8, S4))], '( ( abs ` ( %s - %s ) ) / L ) <_ ( ( %s / L ) x. ( %s ^c L ) )' % (V, GS, K8, S4))
    bnd = D(w, As, 'eqbrtrd', [aeq, le3], '( abs ` ( %s - %s ) ) <_ ( ( %s / L ) x. ( %s ^c L ) )' % (FS, VLd, K8, S4))
    Bs = '( %s <_ s -> ( abs ` ( %s - %s ) ) <_ ( ( %s / L ) x. ( %s ^c L ) ) )' % (IL, FS, VLd, K8, S4)
    alls = w.s([w.s([bnd], 'ex', '( ( %s /\\ s e. RR+ ) -> %s )' % (ph, Bs))], 'ralrimiva', '( %s -> A. s e. RR+ %s )' % (ph, Bs))
    l2p = w.s([cst(w, ph, '2re', '2 e. RR'), cst(w, ph, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % ph)
    k8l = D(w, ph, 'rerpdivcld', [D(w, ph, 'rerpdivcld', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), mr], '( 8 x. M ) e. RR'), l2p], '%s e. RR' % K8), lp], '( %s / L ) e. RR' % K8)
    vl = D(w, ph, 'divcld', [vc, lc, ln], '%s e. CC' % VLd)
    il = D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), lp], '%s e. RR' % IL)
    TLA = '( ( %s e. CC /\\ ( %s / L ) e. RR ) /\\ ( L e. RR+ /\\ %s e. RR ) /\\ ( %s : RR+ --> CC /\\ A. s e. RR+ %s ) )' % (VLd, K8, IL, Fm, Bs)
    tl = D(w, ph, 'syl', [w.s([w.s([vl, k8l], 'jca', '( %s -> ( %s e. CC /\\ ( %s / L ) e. RR ) )' % (ph, VLd, K8)), w.s([lp, il], 'jca', '( %s -> ( L e. RR+ /\\ %s e. RR ) )' % (ph, IL)),
                w.s([fm, alls], 'jca', '( %s -> ( %s : RR+ --> CC /\\ A. s e. RR+ %s ) )' % (ph, Fm, Bs))], '3jca', '( %s -> %s )' % (ph, TLA)), w.inst('zl3tl')], '%s ~~>r %s' % (Fm, VLd))
    w.qed([tl, vc], 'jca', S['zl3scl'])
    go(w, only)
