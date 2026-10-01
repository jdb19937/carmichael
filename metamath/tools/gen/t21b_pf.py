"""Sortie T21b: t21pfne (euler_factor_prim_ne_zero)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *
import congr as _cg

SQF = '{ x e. NN | ( ( mmu ` x ) =/= 0 /\\ x || N ) }'
PN = '{ q e. Prime | q || N }'
TD = '{ q e. Prime | q || d }'
M_ = COND
ZRM = '( ZRHom ` ( Z/nZ ` %s ) )' % M_
GJ = '( j e. Prime |-> -u ( ( %s ` j ) x. ( j ^c -u S ) ) )' % CY


def TT(d):
    return '( ( ( mmu ` %s ) x. ( %s ` %s ) ) x. ( %s ^c -u S ) )' % (d, CY, d, d)


def cyval(w, ante, k, kn):
    """( ante -> ( CY ` k ) = ( PRIM ` ( ZRM ` k ) ) ) from kn : ( ante -> k e. NN )"""
    val = '( %s ` ( %s ` %s ) )' % (PRIM, ZRM, k)
    ex = w.s([w.s([], 'fvex', '%s e. _V' % val)], 'a1i', '( %s -> %s e. _V )' % (ante, val))
    st, v = _cg.mptval(w, ante, 'a', 'NN', '( %s ` ( %s ` a ) )' % (PRIM, ZRM), k, kn, exs=ex, gen=w.g)
    assert v == val, v
    return st, val


def gen_pfne():
    w = W('t21pfne', 'The Euler factor ` sum_ ( d | N ) mu ( d ) chi* ( d ) d ^ -s = prod_ ( p | N ) ( 1 - chi* ( p ) p ^ -s ) ` of a character mod ` N ` at its primitive character does not vanish on ` 0 < Re s ` (Lean ` euler_factor_prim_ne_zero ` ; ~ sqfdvdsum , ~ eufsq , ~ vebklem7 , ~ fprodn0 ).')
    A0 = '( %s /\\ ( S e. CC /\\ 0 < ( Re ` S ) ) )' % NX
    s = S_(w, A0)
    nx = s([], 'simpl', NX)
    nn = s([nx], 'simpld', 'N e. NN')
    sc = s([], 'simprl', 'S e. CC')
    s0 = s([], 'simprr', '0 < ( Re ` S )')
    mnn = s([nx, w.inst('dchrcondnn')], 'syl', '%s e. NN' % M_)
    ypb = s([nx, w.inst('dchrprimcl')], 'syl', '%s e. ( Base ` ( DChr ` %s ) )' % (PRIM, M_))
    mx = s([mnn, ypb], 'jca', '( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) )' % (M_, PRIM, M_))
    nsc = s([sc], 'negcld', '-u S e. CC')
    # ---- the value facts of CY at k e. NN
    def cyfacts(ante, k, kn):
        mxa = lift(w, mx, ante)
        kz = w.s([kn], 'nnzd', '( %s -> %s e. ZZ )' % (ante, k))
        chv = w.s([w.s([mxa, kz], 'jca', '( %s -> ( ( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) ) /\\ %s e. ZZ ) )' % (ante, M_, PRIM, M_, k)), w.inst('cen2chv')], 'syl',
                  '( %s -> ( ( %s ` ( %s ` %s ) ) e. CC /\\ ( abs ` ( %s ` ( %s ` %s ) ) ) <_ 1 ) )' % (ante, PRIM, ZRM, k, PRIM, ZRM, k))
        ev, val = cyval(w, ante, k, kn)
        cc = w.s([ev, w.s([chv], 'simpld', '( %s -> %s e. CC )' % (ante, val))], 'eqeltrd', '( %s -> ( %s ` %s ) e. CC )' % (ante, CY, k))
        ab = w.s([w.s([ev], 'fveq2d', '( %s -> ( abs ` ( %s ` %s ) ) = ( abs ` %s ) )' % (ante, CY, k, val)), w.s([chv], 'simprd', '( %s -> ( abs ` %s ) <_ 1 )' % (ante, val))],
                 'eqbrtrd', '( %s -> ( abs ` ( %s ` %s ) ) <_ 1 )' % (ante, CY, k))
        return cc, ab, ev, val
    # ---- part 1: restrict to squarefree divisors
    dfin = s([nn, w.inst('dvdsfi')], 'syl', '%s e. Fin' % DN)
    s5 = w.s([], 'simpr', '( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N )')
    ss = s([w.s([w.s([s5], 'a1i', '( x e. NN -> ( ( ( mmu ` x ) =/= 0 /\\ x || N ) -> x || N ) )')], 'ss2rabi', '%s C_ %s' % (SQF, DN))], 'a1i', '%s C_ %s' % (SQF, DN))
    el_sqf = w.s([w.s([w.s([w.s([], 'fveq2', '( x = d -> ( mmu ` x ) = ( mmu ` d ) )')], 'neeq1d', '( x = d -> ( ( mmu ` x ) =/= 0 <-> ( mmu ` d ) =/= 0 ) )'),
                        w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'anbi12d', '( x = d -> ( ( ( mmu ` x ) =/= 0 /\\ x || N ) <-> ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )')],
                 'elrab', '( d e. %s <-> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )' % SQF)
    el_dn = w.s([w.s([], 'breq1', '( x = d -> ( x || N <-> d || N ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || N ) )' % DN)
    # terms in CC on DN
    Ab = '( %s /\\ d e. %s )' % (A0, DN)
    sb = S_(w, Ab)
    dnb = sb([sb([], 'simpr', 'd e. %s' % DN), el_dn], 'sylib', '( d e. NN /\\ d || N )')
    dnn_b = sb([dnb], 'simpld', 'd e. NN')
    def tcc(ante, dnn):
        sa = S_(w, ante)
        cc, ab, ev, val = cyfacts(ante, 'd', dnn)
        mu = sa([sa([dnn, w.inst('mucl')], 'syl', '( mmu ` d ) e. ZZ')], 'zcnd', '( mmu ` d ) e. CC')
        dp = sa([sa([dnn], 'nncnd', 'd e. CC'), lift(w, nsc, ante)], 'cxpcld', '( d ^c -u S ) e. CC')
        return sa([sa([mu, cc], 'mulcld', '( ( mmu ` d ) x. ( %s ` d ) ) e. CC' % CY), dp], 'mulcld', '%s e. CC' % TT('d')), mu, cc, dp, ab
    # zero on DN \ SQF
    Ac = '( %s /\\ d e. ( %s \\ %s ) )' % (A0, DN, SQF)
    sc_ = S_(w, Ac)
    din = sc_([sc_([], 'simpr', 'd e. ( %s \\ %s )' % (DN, SQF)), w.inst('eldifi')], 'syl', 'd e. %s' % DN)
    dno = sc_([sc_([], 'simpr', 'd e. ( %s \\ %s )' % (DN, SQF)), w.inst('eldifn')], 'syl', '-. d e. %s' % SQF)
    dd = sc_([din, el_dn], 'sylib', '( d e. NN /\\ d || N )')
    Acm = '( %s /\\ ( mmu ` d ) =/= 0 )' % Ac
    in_sq = w.s([w.s([lift(w, sc_([dd], 'simpld', 'd e. NN'), Acm), w.s([w.s([], 'simpr', '( %s -> ( mmu ` d ) =/= 0 )' % Acm), lift(w, sc_([dd], 'simprd', 'd || N'), Acm)], 'jca',
                 '( %s -> ( ( mmu ` d ) =/= 0 /\\ d || N ) )' % Acm)], 'jca', '( %s -> ( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) ) )' % Acm), el_sqf], 'sylibr', '( %s -> d e. %s )' % (Acm, SQF))
    mu0 = sc_([sc_([in_sq, lift(w, dno, Acm)], 'pm2.65da', '-. ( mmu ` d ) =/= 0'), w.s([], 'nne', '( -. ( mmu ` d ) =/= 0 <-> ( mmu ` d ) = 0 )')], 'sylib', '( mmu ` d ) = 0')
    tc_c, _, cc_c, dp_c, _ = tcc(Ac, sc_([dd], 'simpld', 'd e. NN'))
    z1 = sc_([sc_([mu0], 'oveq1d', '( ( mmu ` d ) x. ( %s ` d ) ) = ( 0 x. ( %s ` d ) )' % (CY, CY)), sc_([cc_c], 'mul02d', '( 0 x. ( %s ` d ) ) = 0' % CY)], 'eqtrd', '( ( mmu ` d ) x. ( %s ` d ) ) = 0' % CY)
    z2 = sc_([sc_([z1], 'oveq1d', '%s = ( 0 x. ( d ^c -u S ) )' % TT('d')), sc_([dp_c], 'mul02d', '( 0 x. ( d ^c -u S ) ) = 0')], 'eqtrd', '%s = 0' % TT('d'))
    # per d in SQF
    Ad = '( %s /\\ d e. %s )' % (A0, SQF)
    sd = S_(w, Ad)
    dq = sd([sd([], 'simpr', 'd e. %s' % SQF), el_sqf], 'sylib', '( d e. NN /\\ ( ( mmu ` d ) =/= 0 /\\ d || N ) )')
    dnn = sd([dq], 'simpld', 'd e. NN')
    mun = sd([dq], 'simprld', '( mmu ` d ) =/= 0')
    tc_d, mu_d, cc_d, dp_d, _ = tcc(Ad, dnn)
    sum1 = s([ss, tc_d, z2, dfin], 'fsumss', 'sum_ d e. %s %s = %s' % (SQF, TT('d'), PFX('S')))
    # ---- part 2: T ( d ) = prod_ p e. TD ( GJ ` p )
    ef = sd([sd([sd([dnn, mun], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'), lift(w, sc, Ad)], 'jca', '( ( d e. NN /\\ ( mmu ` d ) =/= 0 ) /\\ S e. CC )'), w.inst('eufsq')], 'syl',
            '( ( mmu ` d ) x. ( d ^c -u S ) ) = prod_ p e. %s -u ( p ^c -u S )' % TD)
    tdfin = sd([dnn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || d } e. Fin')
    tdfin = sd([sd([w.s([w.s([], 'breq1', '( p = q -> ( p || d <-> q || d ) )')], 'cbvrabv', '{ p e. Prime | p || d } = %s' % TD)], 'a1i', '{ p e. Prime | p || d } = %s' % TD), tdfin], 'eqeltrrd', '%s e. Fin' % TD)
    tdz = sd([w.s([w.s([w.s([w.s([], 'prmz', '( x e. Prime -> x e. ZZ )')], 'ssriv', 'Prime C_ ZZ'), w.s([], 'ssrab2', '%s C_ Prime' % TD)], 'x', 'x') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    przz = w.s([w.s([], 'prmz', '( x e. Prime -> x e. ZZ )')], 'ssriv', 'Prime C_ ZZ')
    tdz = sd([w.s([w.s([], 'ssrab2', '%s C_ Prime' % TD), przz], 'sstri', '%s C_ ZZ' % TD)], 'a1i', '%s C_ ZZ' % TD)
    IZ = '( _I |` ZZ )'
    fz = w.s([w.s([], 'f1oi', '%s : ZZ -1-1-onto-> ZZ' % IZ), w.s([], 'f1of', '( %s : ZZ -1-1-onto-> ZZ -> %s : ZZ --> ZZ )' % (IZ, IZ))], 'ax-mp', '%s : ZZ --> ZZ' % IZ)
    veb_h = sd([sd([lift(w, mx, Ad), sd([fz], 'a1i', '%s : ZZ --> ZZ' % IZ)], 'jca', '( ( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) ) /\\ %s : ZZ --> ZZ )' % (M_, PRIM, M_, IZ)), tdz], 'jca', 'x')
    # vebklem7 wants ( ( N e. NN /\ X e. B /\ F : A --> ZZ ) /\ T C_ A ): a 3-conjunction
    w.lines.pop()
    three = sd([lift(w, mnn, Ad), lift(w, ypb, Ad), sd([fz], 'a1i', '%s : ZZ --> ZZ' % IZ)], '3jca', '( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) /\\ %s : ZZ --> ZZ )' % (M_, PRIM, M_, IZ))
    vh = sd([three, tdz], 'jca', '( ( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) /\\ %s : ZZ --> ZZ ) /\\ %s C_ ZZ )' % (M_, PRIM, M_, IZ, TD))
    VL = '( %s ` ( %s ` prod_ k e. %s ( %s ` k ) ) )' % (PRIM, ZRM, TD, IZ)
    VR = 'prod_ k e. %s ( %s ` ( %s ` ( %s ` k ) ) )' % (TD, PRIM, ZRM, IZ)
    veb = sd([vh, sd([tdfin, w.inst('vebklem7')], 'syl', '( ( ( %s e. NN /\\ %s e. ( Base ` ( DChr ` %s ) ) /\\ %s : ZZ --> ZZ ) /\\ %s C_ ZZ ) -> %s = %s )' % (M_, PRIM, M_, IZ, TD, VL, VR))], 'mpd', '%s = %s' % (VL, VR))
    # rewrite ( IZ ` k ) = k on TD
    Adk = '( %s /\\ k e. %s )' % (Ad, TD)
    kz = w.s([w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Adk, TD)), w.inst('elrabi')], 'syl', '( %s -> k e. Prime )' % Adk), w.inst('prmz')], 'syl', '( %s -> k e. ZZ )' % Adk)
    fk = w.s([kz, w.inst('fvresi')], 'syl', '( %s -> ( %s ` k ) = k )' % (Adk, IZ))
    pl = sd([fk], 'prodeq2dv', 'prod_ k e. %s ( %s ` k ) = prod_ k e. %s k' % (TD, IZ, TD))
    pl2 = w.s([w.s([], 'id', '( k = p -> k = p )')], 'cbvprodv', 'prod_ k e. %s k = prod_ p e. %s p' % (TD, TD))
    sqp = sd([sd([dnn, mun], 'jca', '( d e. NN /\\ ( mmu ` d ) =/= 0 )'), w.inst('sqfprodid')], 'syl', 'prod_ p e. { q e. Prime | q || d } p = d')
    plall = sd([sd([pl, sd([pl2], 'a1i', 'prod_ k e. %s k = prod_ p e. %s p' % (TD, TD))], 'eqtrd', 'prod_ k e. %s ( %s ` k ) = prod_ p e. %s p' % (TD, IZ, TD)), sqp], 'eqtrd',
                'prod_ k e. %s ( %s ` k ) = d' % (TD, IZ))
    lhs = sd([sd([plall], 'fveq2d', '( %s ` prod_ k e. %s ( %s ` k ) ) = ( %s ` d )' % (ZRM, TD, IZ, ZRM))], 'fveq2d', '%s = ( %s ` ( %s ` d ) )' % (VL, PRIM, ZRM))
    ev_d, _ = cyval(w, Ad, 'd', dnn)
    # RHS: ( PRIM ` ( ZRM ` ( IZ ` k ) ) ) = ( CY ` k )
    knn = w.s([w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Adk, TD)), w.inst('elrabi')], 'syl', '( %s -> k e. Prime )' % Adk), w.inst('prmnn')], 'syl', '( %s -> k e. NN )' % Adk)
    evk, _ = cyval(w, Adk, 'k', knn)
    rk = w.s([w.s([w.s([fk], 'fveq2d', '( %s -> ( %s ` ( %s ` k ) ) = ( %s ` k ) )' % (Adk, ZRM, IZ, ZRM))], 'fveq2d', '( %s -> ( %s ` ( %s ` ( %s ` k ) ) ) = ( %s ` ( %s ` k ) ) )' % (Adk, PRIM, ZRM, IZ, PRIM, ZRM)),
              w.s([evk], 'eqcomd', '( %s -> ( %s ` ( %s ` k ) ) = ( %s ` k ) )' % (Adk, PRIM, ZRM, CY))], 'eqtrd', '( %s -> ( %s ` ( %s ` ( %s ` k ) ) ) = ( %s ` k ) )' % (Adk, PRIM, ZRM, IZ, CY))
    pr = sd([rk], 'prodeq2dv', '%s = prod_ k e. %s ( %s ` k )' % (VR, TD, CY))
    pr2 = sd([w.s([w.s([], 'fveq2', '( k = p -> ( %s ` k ) = ( %s ` p ) )' % (CY, CY))], 'cbvprodv', 'prod_ k e. %s ( %s ` k ) = prod_ p e. %s ( %s ` p )' % (TD, CY, TD, CY))], 'a1i',
             'prod_ k e. %s ( %s ` k ) = prod_ p e. %s ( %s ` p )' % (TD, CY, TD, CY))
    cyd = sd([sd([sd([ev_d, sd([lhs], 'eqcomd', '( %s ` ( %s ` d ) ) = %s' % (PRIM, ZRM, VL))], 'eqtrd', '( %s ` d ) = %s' % (CY, VL)), veb], 'eqtrd', '( %s ` d ) = %s' % (CY, VR)),
              sd([pr, pr2], 'eqtrd', '%s = prod_ p e. %s ( %s ` p )' % (VR, TD, CY))], 'eqtrd', '( %s ` d ) = prod_ p e. %s ( %s ` p )' % (CY, TD, CY))
    # T ( d ) = CY(d) ( mu d^-S ) = prod CY(p) prod -u p^-S = prod ( CY p x. -u p^-S ) = prod ( GJ ` p )
    e1 = sd([mu_d, cc_d, dp_d], 'mulassd', '%s = ( ( mmu ` d ) x. ( ( %s ` d ) x. ( d ^c -u S ) ) )' % (TT('d'), CY))
    e2 = sd([mu_d, cc_d, dp_d], 'mul12d', '( ( mmu ` d ) x. ( ( %s ` d ) x. ( d ^c -u S ) ) ) = ( ( %s ` d ) x. ( ( mmu ` d ) x. ( d ^c -u S ) ) )' % (CY, CY))
    PC = 'prod_ p e. %s ( %s ` p )' % (TD, CY)
    PM = 'prod_ p e. %s -u ( p ^c -u S )' % TD
    e3 = sd([cyd, ef], 'oveq12d', '( ( %s ` d ) x. ( ( mmu ` d ) x. ( d ^c -u S ) ) ) = ( %s x. %s )' % (CY, PC, PM))
    Adp = '( %s /\\ p e. %s )' % (Ad, TD)
    pin = w.s([w.s([], 'simpr', '( %s -> p e. %s )' % (Adp, TD)), w.inst('elrabi')], 'syl', '( %s -> p e. Prime )' % Adp)
    pnn = w.s([pin, w.inst('prmnn')], 'syl', '( %s -> p e. NN )' % Adp)
    cc_p, _, _, _ = cyfacts(Adp, 'p', pnn)
    pp = w.s([w.s([pnn], 'nncnd', '( %s -> p e. CC )' % Adp), lift(w, nsc, Adp)], 'cxpcld', '( %s -> ( p ^c -u S ) e. CC )' % Adp)
    npp = w.s([pp], 'negcld', '( %s -> -u ( p ^c -u S ) e. CC )' % Adp)
    fpm = sd([tdfin, cc_p, npp], 'fprodmul', 'prod_ p e. %s ( ( %s ` p ) x. -u ( p ^c -u S ) ) = ( %s x. %s )' % (TD, CY, PC, PM))
    GP = '-u ( ( %s ` p ) x. ( p ^c -u S ) )' % CY
    gv, gval = _cg.mptval(w, Adp, 'j', 'Prime', '-u ( ( %s ` j ) x. ( j ^c -u S ) )' % CY, 'p', pin, exs=w.s([w.s([], 'negex', '%s e. _V' % GP)], 'a1i', '( %s -> %s e. _V )' % (Adp, GP)), gen=w.g)
    assert gval == GP, gval
    t1 = w.s([cc_p, pp], 'mulneg2d', '( %s -> ( ( %s ` p ) x. -u ( p ^c -u S ) ) = %s )' % (Adp, CY, GP))
    t2 = w.s([t1, w.s([gv], 'eqcomd', '( %s -> %s = ( %s ` p ) )' % (Adp, GP, GJ))], 'eqtrd', '( %s -> ( ( %s ` p ) x. -u ( p ^c -u S ) ) = ( %s ` p ) )' % (Adp, CY, GJ))
    PG = 'prod_ p e. %s ( %s ` p )' % (TD, GJ)
    e4 = sd([t2], 'prodeq2dv', 'prod_ p e. %s ( ( %s ` p ) x. -u ( p ^c -u S ) ) = %s' % (TD, CY, PG))
    td_eq = sd([sd([e1, e2], 'eqtrd', '%s = ( ( %s ` d ) x. ( ( mmu ` d ) x. ( d ^c -u S ) ) )' % (TT('d'), CY)),
                sd([e3, sd([sd([fpm], 'eqcomd', '( %s x. %s ) = prod_ p e. %s ( ( %s ` p ) x. -u ( p ^c -u S ) )' % (PC, PM, TD, CY)), e4], 'eqtrd', '( %s x. %s ) = %s' % (PC, PM, PG))],
                   'eqtrd', '( ( %s ` d ) x. ( ( mmu ` d ) x. ( d ^c -u S ) ) ) = %s' % (CY, PG))], 'eqtrd', '%s = %s' % (TT('d'), PG))
    sum2 = s([td_eq], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (SQF, TT('d'), SQF, PG))
    # ---- part 3: sqfdvdsum
    Aj = '( %s /\\ j e. Prime )' % A0
    jn = w.s([w.s([], 'simpr', '( %s -> j e. Prime )' % Aj), w.inst('prmnn')], 'syl', '( %s -> j e. NN )' % Aj)
    cc_j, _, _, _ = cyfacts(Aj, 'j', jn)
    jp = w.s([w.s([jn], 'nncnd', '( %s -> j e. CC )' % Aj), lift(w, nsc, Aj)], 'cxpcld', '( %s -> ( j ^c -u S ) e. CC )' % Aj)
    gjc = w.s([w.s([cc_j, jp], 'mulcld', '( %s -> ( ( %s ` j ) x. ( j ^c -u S ) ) e. CC )' % (Aj, CY))], 'negcld', '( %s -> -u ( ( %s ` j ) x. ( j ^c -u S ) ) e. CC )' % (Aj, CY))
    gf = s([gjc], 'fmptd', '%s : Prime --> CC' % GJ)
    PP = 'prod_ p e. %s ( 1 + ( %s ` p ) )' % (PN, GJ)
    sq = s([s([nn, gf], 'jca', '( N e. NN /\\ %s : Prime --> CC )' % GJ), w.inst('sqfdvdsum')], 'syl', 'sum_ d e. %s %s = %s' % (SQF, PG, PP))
    tot = s([s([s([sum1], 'eqcomd', '%s = sum_ d e. %s %s' % (PFX('S'), SQF, TT('d'))), sum2], 'eqtrd', '%s = sum_ d e. %s %s' % (PFX('S'), SQF, PG)), sq], 'eqtrd', '%s = %s' % (PFX('S'), PP))
    # ---- part 4: the product does not vanish
    Ap = '( %s /\\ p e. %s )' % (A0, PN)
    sp = S_(w, Ap)
    pin2 = sp([sp([], 'simpr', 'p e. %s' % PN), w.inst('elrabi')], 'syl', 'p e. Prime')
    pnn2 = sp([pin2, w.inst('prmnn')], 'syl', 'p e. NN')
    cc2, ab2, _, _ = cyfacts(Ap, 'p', pnn2)
    prp = sp([pnn2], 'nnrpd', 'p e. RR+')
    pp2 = sp([sp([pnn2], 'nncnd', 'p e. CC'), lift(w, nsc, Ap)], 'cxpcld', '( p ^c -u S ) e. CC')
    Q = '( ( %s ` p ) x. ( p ^c -u S ) )' % CY
    qc = sp([cc2, pp2], 'mulcld', '%s e. CC' % Q)
    gv2, _ = _cg.mptval(w, Ap, 'j', 'Prime', '-u ( ( %s ` j ) x. ( j ^c -u S ) )' % CY, 'p', pin2, exs=sp([w.s([], 'negex', '%s e. _V' % GP)], 'a1i', '%s e. _V' % GP), gen=w.g)
    one_g = sp([sp([gv2], 'oveq2d', '( 1 + ( %s ` p ) ) = ( 1 + %s )' % (GJ, GP)), sp([sp([], '1cnd', '1 e. CC'), qc], 'negsubd', '( 1 + %s ) = ( 1 - %s )' % (GP, Q))], 'eqtrd', '( 1 + ( %s ` p ) ) = ( 1 - %s )' % (GJ, Q))
    fc = sp([one_g, sp([sp([], '1cnd', '1 e. CC'), qc], 'subcld', '( 1 - %s ) e. CC' % Q)], 'eqeltrd', '( 1 + ( %s ` p ) ) e. CC' % GJ)
    # abs Q < 1
    re_ = sp([lift(w, sc, Ap)], 'recld', '( Re ` S ) e. RR')
    ax = sp([prp, lift(w, nsc, Ap), w.inst('abscxp')], 'x', 'x') if False else None
    abp = sp([sp([prp, lift(w, nsc, Ap)], 'jca', '( p e. RR+ /\\ -u S e. CC )'), w.inst('abscxp')], 'syl', '( abs ` ( p ^c -u S ) ) = ( p ^c ( Re ` -u S ) )')
    ren = sp([lift(w, sc, Ap)], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')
    abp2 = sp([abp, sp([ren], 'oveq2d', '( p ^c ( Re ` -u S ) ) = ( p ^c -u ( Re ` S ) )')], 'eqtrd', '( abs ` ( p ^c -u S ) ) = ( p ^c -u ( Re ` S ) )')
    p1 = sp([sp([pin2, w.inst('prmgt1')], 'syl', '1 < p')], 'x', 'x') if False else sp([pin2, w.inst('prmgt1')], 'syl', '1 < p')
    lt0 = sp([sp([re_], 'renegcld', '-u ( Re ` S ) e. RR'), sp([], '0red', '0 e. RR'), lin.linarith(w, Ap, [lift(w, s0, Ap)], '-u ( Re ` S ) < 0', leaves={'( Re ` S )': re_})], 'x', 'x') if False else None
    ng = lin.linarith(w, Ap, [lift(w, s0, Ap)], '-u ( Re ` S ) < 0', leaves={'( Re ` S )': re_})
    cl_ = sp([sp([sp([pnn2], 'nnred', 'p e. RR'), p1, sp([re_], 'renegcld', '-u ( Re ` S ) e. RR'), sp([], '0red', '0 e. RR')], 'jca', 'x')], 'x', 'x') if False else None
    CXL = '( ( ( p e. RR /\\ 1 < p ) /\\ ( -u ( Re ` S ) e. RR /\\ 0 e. RR ) ) -> ( -u ( Re ` S ) < 0 <-> ( p ^c -u ( Re ` S ) ) < ( p ^c 0 ) ) )'
    cxl = sp([sp([sp([sp([pnn2], 'nnred', 'p e. RR'), p1], 'jca', '( p e. RR /\\ 1 < p )'), sp([sp([re_], 'renegcld', '-u ( Re ` S ) e. RR'), sp([], '0red', '0 e. RR')], 'jca', '( -u ( Re ` S ) e. RR /\\ 0 e. RR )')], 'jca',
                  '( ( p e. RR /\\ 1 < p ) /\\ ( -u ( Re ` S ) e. RR /\\ 0 e. RR ) )'), w.inst('cxplt')], 'syl', '( -u ( Re ` S ) < 0 <-> ( p ^c -u ( Re ` S ) ) < ( p ^c 0 ) )')
    lt = sp([ng, cxl], 'mpbid', '( p ^c -u ( Re ` S ) ) < ( p ^c 0 )')
    c0 = sp([sp([pnn2], 'nncnd', 'p e. CC'), w.inst('cxp0')], 'syl', '( p ^c 0 ) = 1')
    abl = sp([abp2, sp([lt, c0], 'breqtrd', '( p ^c -u ( Re ` S ) ) < 1')], 'eqbrtrd', '( abs ` ( p ^c -u S ) ) < 1')
    aq = sp([cc2, pp2], 'absmuld', '( abs ` %s ) = ( ( abs ` ( %s ` p ) ) x. ( abs ` ( p ^c -u S ) ) )' % (Q, CY))
    A1_ = '( abs ` ( %s ` p ) )' % CY
    A2_ = '( abs ` ( p ^c -u S ) )'
    a1r = sp([cc2], 'abscld', '%s e. RR' % A1_); a2r = sp([pp2], 'abscld', '%s e. RR' % A2_)
    a1z = sp([cc2], 'absge0d', '0 <_ %s' % A1_); a2z = sp([pp2], 'absge0d', '0 <_ %s' % A2_)
    le1 = sp([a1r, sp([], '1red', '1 e. RR'), a2r, a2z, ab2], 'lemul1ad', '( %s x. %s ) <_ ( 1 x. %s )' % (A1_, A2_, A2_))
    le2 = sp([le1, sp([sp([a2r], 'recnd', '%s e. CC' % A2_)], 'mullidd', '( 1 x. %s ) = %s' % (A2_, A2_))], 'breqtrd', '( %s x. %s ) <_ %s' % (A1_, A2_, A2_))
    aql = sp([sp([aq, le2], 'eqbrtrd', '( abs ` %s ) <_ %s' % (Q, A2_)), abl], 'lelttrd', '( abs ` %s ) < 1' % Q)
    # 1 - Q =/= 0
    Az = '( %s /\\ ( 1 - %s ) = 0 )' % (Ap, Q)
    q1 = w.s([lift(w, qc, Az), w.s([], 'simpr', '( %s -> ( 1 - %s ) = 0 )' % (Az, Q)), w.s([], '1cnd', '( %s -> 1 e. CC )' % Az)], 'x', 'x') if False else None
    qe = w.s([w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % Az), lift(w, qc, Az)], 'subeq0ad', '( %s -> ( ( 1 - %s ) = 0 <-> 1 = %s ) )' % (Az, Q, Q)), w.s([], 'simpr', '( %s -> ( 1 - %s ) = 0 )' % (Az, Q))], 'mpbird',
             '( %s -> 1 = %s )' % (Az, Q)) if False else None
    s_eq = w.s([w.s([], 'simpr', '( %s -> ( 1 - %s ) = 0 )' % (Az, Q)), w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % Az), lift(w, qc, Az)], 'subeq0ad', '( %s -> ( ( 1 - %s ) = 0 <-> 1 = %s ) )' % (Az, Q, Q))], 'mpbid', '( %s -> 1 = %s )' % (Az, Q))
    ab1 = w.s([w.s([w.s([s_eq], 'eqcomd', '( %s -> %s = 1 )' % (Az, Q))], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` 1 ) )' % (Az, Q)), w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % Az)], 'eqtrd', '( %s -> ( abs ` %s ) = 1 )' % (Az, Q))
    nlt = w.s([w.s([ab1], 'eqcomd', '( %s -> 1 = ( abs ` %s ) )' % (Az, Q)), w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Az), lift(w, sp([qc], 'abscld', '( abs ` %s ) e. RR' % Q), Az)], 'x', 'x') if False else None], 'x', 'x') if False else None
    ge = w.s([w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Az)], 'leidd', '( %s -> 1 <_ 1 )' % Az), w.s([ab1], 'eqcomd', '( %s -> 1 = ( abs ` %s ) )' % (Az, Q))], 'breqtrd', '( %s -> 1 <_ ( abs ` %s ) )' % (Az, Q))
    nl = w.s([ge, w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Az), lift(w, sp([qc], 'abscld', '( abs ` %s ) e. RR' % Q), Az)], 'lenltd', '( %s -> ( 1 <_ ( abs ` %s ) <-> -. ( abs ` %s ) < 1 ) )' % (Az, Q, Q))], 'mpbid', '( %s -> -. ( abs ` %s ) < 1 )' % (Az, Q))
    ne = sp([lift(w, aql, Az), nl], 'pm2.65da', '-. ( 1 - %s ) = 0' % Q)
    ne2 = sp([ne], 'neqned', '( 1 - %s ) =/= 0' % Q)
    fne = sp([one_g, ne2], 'x', 'x') if False else sp([sp([one_g], 'neeq1d', '( ( 1 + ( %s ` p ) ) =/= 0 <-> ( 1 - %s ) =/= 0 )' % (GJ, Q)), ne2], 'mpbird', '( 1 + ( %s ` p ) ) =/= 0' % GJ)
    pnfin = s([nn, w.inst('prmdvdsfi')], 'syl', '{ p e. Prime | p || N } e. Fin')
    pnfin = s([s([w.s([w.s([], 'breq1', '( p = q -> ( p || N <-> q || N ) )')], 'cbvrabv', '{ p e. Prime | p || N } = %s' % PN)], 'a1i', '{ p e. Prime | p || N } = %s' % PN), pnfin], 'eqeltrrd', '%s e. Fin' % PN)
    pne = s([pnfin, fc, fne], 'fprodn0', '%s =/= 0' % PP)
    w.qed([s([tot], 'neeq1d', '( %s =/= 0 <-> %s =/= 0 )' % (PFX('S'), PP)), pne], 'mpbird', SB['t21pfne'])
    w.lines = [l for l in w.lines if not l.split(':', 3)[-1].strip().endswith('|- x') and ' |- ( %s -> x )' % Ad not in l]
    return go(w)


if __name__ == '__main__':
    gen_pfne()
