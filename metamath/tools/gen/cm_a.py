"""Sortie CM: generic lemmas (cmsqx, cmitgif, cmuint).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_a.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *

only = sys.argv[1:]


def rsp_q(w, A, hstep, body, q='q', p='p', P='P', eqstep=None):
    """( ( A /\\ q e. P ) -> body[q] ) from hstep ( ( A /\\ p e. P ) -> body[p] ) and eqstep ( p = q -> ( body <-> body' ) )"""
    ral = w.s([hstep], 'ralrimiva', '( %s -> A. %s e. %s %s )' % (A, p, P, body[0]))
    rs = w.s([eqstep], 'rspcv', '( %s e. %s -> ( A. %s e. %s %s -> %s ) )' % (q, P, p, P, body[0], body[1]))
    Aq = '( %s /\\ %s e. %s )' % (A, q, P)
    return w.s([w.s([], 'simpr', '( %s -> %s e. %s )' % (Aq, q, P)), lift(w, ral, Aq), rs], 'sylc', '( %s -> %s )' % (Aq, body[1]))


def gen_sqx():
    w = W('cmsqx', 'The square of a guarded finite sum as a double sum: ` abs ( sum_ p if ( p <_ U , F , 0 ) ) ^ 2 = sum_ p sum_ q if ( ( p <_ U /\\ q <_ U ) , F x. * G , 0 ) ` ( ~ absvalsq , ~ fsumcj , ~ fsum2mul , ~ lswifmul ).')
    h1, h2, h3 = ehyps(w, 'cmsqx')
    A = 'ph'
    d = mk(w, A)
    Ap = '( ph /\\ p e. P )'
    IFP = 'if ( p <_ U , F , 0 )'; IFQ = 'if ( q <_ U , G , 0 )'
    ifp = D(w, Ap, 'ifcld', [h2, a1(w, Ap, '0cn', '0 e. CC')], '%s e. CC' % IFP)
    DS = 'sum_ p e. P %s' % IFP
    dcc = d('fsumcl', [h1, ifp], '%s e. CC' % DS)
    absq = d('syl', [dcc, w.inst('absvalsq')], '( ( abs ` %s ) ^ 2 ) = ( %s x. ( * ` %s ) )' % (DS, DS, DS))
    cj = d('fsumcj', [h1, ifp], '( * ` %s ) = sum_ p e. P ( * ` %s )' % (DS, IFP))
    eq = 'p = q'
    idp = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, new = w.congr('( * ` %s )' % IFP, {'p': 'q'}, eq, {'p': idp}, rules={'F': ('G', h3)})
    assert new == '( * ` %s )' % IFQ, new
    ren = w.s([st], 'cbvsumv', 'sum_ p e. P ( * ` %s ) = sum_ q e. P ( * ` %s )' % (IFP, IFQ))
    cj2 = d('eqtrd', [cj, a1(w, A, 'cbvsumv', 'sum_ p e. P ( * ` %s ) = sum_ q e. P ( * ` %s )' % (IFP, IFQ), [st])],
            '( * ` %s ) = sum_ q e. P ( * ` %s )' % (DS, IFQ))
    e1 = w.s([h3], 'eleq1d', '( %s -> ( F e. CC <-> G e. CC ) )' % eq)
    gq = rsp_q(w, A, h2, ('F e. CC', 'G e. CC'), eqstep=e1)
    Aq = '( ph /\\ q e. P )'
    ifq = D(w, Aq, 'ifcld', [gq, a1(w, Aq, '0cn', '0 e. CC')], '%s e. CC' % IFQ)
    cjq = D(w, Aq, 'cjcld', [ifq], '( * ` %s ) e. CC' % IFQ)
    SQ_ = 'sum_ q e. P ( * ` %s )' % IFQ
    m2 = d('fsum2mul', [h1, h1, ifp, cjq], 'sum_ p e. P sum_ q e. P ( %s x. ( * ` %s ) ) = ( %s x. %s )' % (IFP, IFQ, DS, SQ_))
    Apq = '( %s /\\ q e. P )' % Ap
    fq = lift(w, h2, Apq)
    gq2 = D(w, Apq, 'syl', [w.s([], 'simpr', '( %s -> q e. P )' % Apq),
                            w.s([gq], 'ex', '( ph -> ( q e. P -> G e. CC ) )')], 'G e. CC') if False else None
    gq2 = D(w, Apq, 'mpd', [w.s([], 'simpr', '( %s -> q e. P )' % Apq), lift(w, w.s([gq], 'ex', '( ph -> ( q e. P -> G e. CC ) )'), Apq)], 'G e. CC')
    TERM = 'if ( ( p <_ U /\\ q <_ U ) , ( F x. ( * ` G ) ) , 0 )'
    lw = D(w, Apq, 'syl2anc', [fq, gq2, w.inst('lswifmul')], '( %s x. ( * ` %s ) ) = %s' % (IFP, IFQ, TERM))
    s1 = D(w, Ap, 'sumeq2dv', [lw], 'sum_ q e. P ( %s x. ( * ` %s ) ) = sum_ q e. P %s' % (IFP, IFQ, TERM))
    s2 = d('sumeq2dv', [s1], 'sum_ p e. P sum_ q e. P ( %s x. ( * ` %s ) ) = sum_ p e. P sum_ q e. P %s' % (IFP, IFQ, TERM))
    m3 = d('oveq2d', [cj2], '( %s x. ( * ` %s ) ) = ( %s x. %s )' % (DS, DS, DS, SQ_))
    terms = ['( ( abs ` %s ) ^ 2 )' % DS, '( %s x. ( * ` %s ) )' % (DS, DS), '( %s x. %s )' % (DS, SQ_),
             'sum_ p e. P sum_ q e. P ( %s x. ( * ` %s ) )' % (IFP, IFQ), 'sum_ p e. P sum_ q e. P %s' % TERM]
    fin = chain(w, A, terms, [absq, m3, ('r', m2), s2])
    w.qed([fin], 'idi', S['cmsqx'])
    return run(w, only)


def ifmul(w, A, bcc, B, ps='ps'):
    """( A -> ( if ( ps , 1 , 0 ) x. B ) = if ( ps , B , 0 ) ) from bcc ( A -> B e. CC )"""
    d = mk(w, A)
    C1 = 'if ( %s , 1 , 0 )' % ps
    ov = a1(w, A, 'ovif', '( %s x. %s ) = if ( %s , ( 1 x. %s ) , ( 0 x. %s ) )' % (C1, B, ps, B, B))
    ie = d('ifeq12d', [d('mullidd', [bcc], '( 1 x. %s ) = %s' % (B, B)), d('mul02d', [bcc], '( 0 x. %s ) = 0' % B)],
           'if ( %s , ( 1 x. %s ) , ( 0 x. %s ) ) = if ( %s , %s , 0 )' % (ps, B, B, ps, B))
    return d('eqtrd', [ov, ie], '( %s x. %s ) = if ( %s , %s , 0 )' % (C1, B, ps, B))


def gen_itgif():
    w = W('cmitgif', 'The integral of a guarded integrand whose guard is free of the integration variable: ` S. A if ( ps , B , 0 ) = if ( ps , S. A B , 0 ) ` , with integrability ( ~ ovif , ~ iblmulc2 , ~ itgmulc2 ).')
    h1, h2 = ehyps(w, 'cmitgif')
    A = 'ph'; d = mk(w, A)
    C1 = 'if ( ps , 1 , 0 )'
    c1 = d('ifcld', [a1(w, A, 'ax-1cn', '1 e. CC'), a1(w, A, '0cn', '0 e. CC')], '%s e. CC' % C1)
    Ax = '( ph /\\ x e. A )'
    eqx = ifmul(w, Ax, h2, 'B')
    ib = d('iblmulc2', [c1, h2, h1], '( x e. A |-> ( %s x. B ) ) e. L^1' % C1)
    me = d('mpteq2dva', [eqx], '( x e. A |-> ( %s x. B ) ) = ( x e. A |-> if ( ps , B , 0 ) )' % C1)
    ib2 = d('eqeltrrd', [me, ib], '( x e. A |-> if ( ps , B , 0 ) ) e. L^1')
    IB = 'S. A B _d x'
    im = d('itgmulc2', [c1, h2, h1], '( %s x. %s ) = S. A ( %s x. B ) _d x' % (C1, IB, C1))
    ie = d('itgeq2dv', [eqx], 'S. A ( %s x. B ) _d x = S. A if ( ps , B , 0 ) _d x' % C1)
    icc = d('itgcl', [h2, h1], '%s e. CC' % IB)
    e3 = ifmul(w, A, icc, IB)
    it = chain(w, A, ['S. A if ( ps , B , 0 ) _d x', 'S. A ( %s x. B ) _d x' % C1, '( %s x. %s )' % (C1, IB), 'if ( ps , %s , 0 )' % IB],
               [('r', ie), ('r', im), e3])
    fin = d('jca', [ib2, it], split_imp(S['cmitgif'])[1])
    w.qed([fin], 'idi', S['cmitgif'])
    return run(w, only)


def gen_uint():
    w = W('cmuint', 'The ` du / u ` integral of a double step sum: for ` P C_ ( Y , Z ] ` , ` S. ( Y , Z ) sum_ p sum_ q if ( ( p <_ u /\\ q <_ u ) , K / u , 0 ) = sum_ p sum_ q K ( log Z - log max ( p , q ) ) ` ( ~ kd2ind , ~ kd2log , ~ itgfsum , ~ maxle ).')
    h1, h2, h3 = ehyps(w, 'cmuint')
    A = 'ph'; d = mk(w, A)
    yp = d('simp1d', [h1], 'Y e. RR+'); zr = d('simp2d', [h1], 'Z e. RR'); yz = d('simp3d', [h1], 'Y <_ Z')
    yr = d('rpred', [yp], 'Y e. RR'); yx = d('rexrd', [yr], 'Y e. RR*')
    pf = d('simpld', [h2], 'P e. Fin'); ps_ = d('simprd', [h2], 'P C_ ( Y (,] Z )')
    YZ = '( Y (,) Z )'
    def elt(ctx, v):
        """( ctx -> ( v e. RR /\\ Y < v /\\ v <_ Z ) ) for v e. P a conjunct of ctx"""
        vp = proj(w, ctx, '%s e. P' % v)
        vin = D(w, ctx, 'sseldd', [lift(w, ps_, ctx), vp], '%s e. ( Y (,] Z )' % v)
        el = D(w, ctx, 'syl2anc', [lift(w, yx, ctx), lift(w, zr, ctx), w.inst('elioc2')], '( %s e. ( Y (,] Z ) <-> ( %s e. RR /\\ Y < %s /\\ %s <_ Z ) )' % (v, v, v, v))
        return D(w, ctx, 'mpbid', [vin, el], '( %s e. RR /\\ Y < %s /\\ %s <_ Z )' % (v, v, v))
    MX = 'if ( p <_ q , q , p )'
    TRM = 'if ( ( p <_ u /\\ q <_ u ) , ( K / u ) , 0 )'
    TRM2 = 'if ( %s <_ u , ( K / u ) , 0 )' % MX
    LG = '( ( log ` Z ) - ( log ` %s ) )' % MX
    # per (p, q): context ( ( ph /\\ p e. P ) /\\ q e. P )
    Q = '( ( ph /\\ p e. P ) /\\ q e. P )'
    q_ = mk(w, Q)
    ep = elt(Q, 'p'); eq_ = elt(Q, 'q')
    pr = q_('simp1d', [ep], 'p e. RR'); yp_ = q_('simp2d', [ep], 'Y < p'); pz = q_('simp3d', [ep], 'p <_ Z')
    qr = q_('simp1d', [eq_], 'q e. RR'); qz = q_('simp3d', [eq_], 'q <_ Z')
    kc = rean(w, h3, Q)
    mr = q_('ifcld', [qr, pr], '%s e. RR' % MX)
    pm = q_('syl2anc', [pr, qr, w.inst('max1')], 'p <_ %s' % MX)
    ym = q_('ltletrd', [lift(w, yr, Q), pr, mr, yp_, pm], 'Y < %s' % MX)
    mz = q_('mpbird', [q_('jca', [pz, qz], '( p <_ Z /\\ q <_ Z )'), q_('syl3anc', [pr, qr, lift(w, zr, Q), w.inst('maxle')], '( %s <_ Z <-> ( p <_ Z /\\ q <_ Z ) )' % MX)], '%s <_ Z' % MX)
    mp = q_('rpgt0d' if False else 'elrpd', [mr, q_('lttrd' if False else 'ltletrd' if False else 'lttrd', [lift(w, w.s([yp], 'rpgt0d', '( ph -> 0 < Y )'), Q) if False else q_('rpgt0d', [lift(w, yp, Q)], '0 < Y'), ym], '0 < %s' % MX) if False else
              q_('lttrd', [q_('0red' if False else 'id', [], '0 e. RR') if False else a1(w, Q, '0re', '0 e. RR'), lift(w, yr, Q), mr, q_('rpgt0d', [lift(w, yp, Q)], '0 < Y'), ym], '0 < %s' % MX)], '%s e. RR+' % MX)
    lg = q_('syl3anc', [mp, lift(w, zr, Q), mz, w.inst('kd2log')], '( ( u e. ( %s (,) Z ) |-> ( 1 / u ) ) e. L^1 /\\ S. ( %s (,) Z ) ( 1 / u ) _d u = %s )' % (MX, MX, LG))
    lg1 = q_('simpld', [lg], '( u e. ( %s (,) Z ) |-> ( 1 / u ) ) e. L^1' % MX)
    lg2 = q_('simprd', [lg], 'S. ( %s (,) Z ) ( 1 / u ) _d u = %s' % (MX, LG))
    # on ( M , Z ): 1 / u in CC and K / u = K x. ( 1 / u )
    Qm = '( %s /\\ u e. ( %s (,) Z ) )' % (Q, MX)
    qm = mk(w, Qm)
    um = qm('simpr', [], 'u e. ( %s (,) Z )' % MX)
    ug = qm('mpbid', [um, qm('syl2anc', [qm('rexrd', [lift(w, mr, Qm)], '%s e. RR*' % MX), qm('rexrd', [lift(w, zr, Qm)], 'Z e. RR*'), w.inst('elioo2')],
                                  '( u e. ( %s (,) Z ) <-> ( u e. RR /\\ %s < u /\\ u < Z ) )' % (MX, MX))], '( u e. RR /\\ %s < u /\\ u < Z )' % MX)
    ur = qm('simp1d', [ug], 'u e. RR')
    upos = qm('lttrd', [a1(w, Qm, '0re', '0 e. RR'), lift(w, mr, Qm), ur, qm('rpgt0d', [lift(w, mp, Qm)], '0 < %s' % MX), qm('simp2d', [ug], '%s < u' % MX)], '0 < u')
    ucc = qm('recnd', [ur], 'u e. CC'); une = qm('gt0ne0d', [upos], 'u =/= 0')
    rc = qm('reccld', [ucc, une], '( 1 / u ) e. CC')
    dr = qm('divrecd', [lift(w, kc, Qm), ucc, une], '( K / u ) = ( K x. ( 1 / u ) )')
    ibk = q_('iblmulc2', [kc, rc, lg1], '( u e. ( %s (,) Z ) |-> ( K x. ( 1 / u ) ) ) e. L^1' % MX)
    me = q_('mpteq2dva', [dr], '( u e. ( %s (,) Z ) |-> ( K / u ) ) = ( u e. ( %s (,) Z ) |-> ( K x. ( 1 / u ) ) )' % (MX, MX))
    ibk2 = q_('eqeltrd', [me, ibk], '( u e. ( %s (,) Z ) |-> ( K / u ) ) e. L^1' % MX)
    itk = chain(w, Q, ['S. ( %s (,) Z ) ( K / u ) _d u' % MX, 'S. ( %s (,) Z ) ( K x. ( 1 / u ) ) _d u' % MX, '( K x. S. ( %s (,) Z ) ( 1 / u ) _d u )' % MX, '( K x. %s )' % LG],
                [q_('itgeq2dv', [dr], 'S. ( %s (,) Z ) ( K / u ) _d u = S. ( %s (,) Z ) ( K x. ( 1 / u ) ) _d u' % (MX, MX)),
                 ('r', q_('itgmulc2', [kc, rc, lg1], '( K x. S. ( %s (,) Z ) ( 1 / u ) _d u ) = S. ( %s (,) Z ) ( K x. ( 1 / u ) ) _d u' % (MX, MX))),
                 q_('oveq2d', [lg2], '( K x. S. ( %s (,) Z ) ( 1 / u ) _d u ) = ( K x. %s )' % (MX, LG))])
    # on ( Y , Z )
    Qy = '( %s /\\ u e. %s )' % (Q, YZ)
    qy = mk(w, Qy)
    uy = qy('simpr', [], 'u e. %s' % YZ)
    ugy = qy('mpbid', [uy, qy('syl2anc', [lift(w, yx, Qy), qy('rexrd', [lift(w, zr, Qy)], 'Z e. RR*'), w.inst('elioo2')], '( u e. %s <-> ( u e. RR /\\ Y < u /\\ u < Z ) )' % YZ)],
              '( u e. RR /\\ Y < u /\\ u < Z )')
    ury = qy('simp1d', [ugy], 'u e. RR')
    uposy = qy('lttrd', [a1(w, Qy, '0re', '0 e. RR'), lift(w, yr, Qy), ury, qy('rpgt0d', [lift(w, yp, Qy)], '0 < Y'), qy('simp2d', [ugy], 'Y < u')], '0 < u')
    kuy = qy('divcld', [lift(w, kc, Qy), qy('recnd', [ury], 'u e. CC'), qy('gt0ne0d', [uposy], 'u =/= 0')], '( K / u ) e. CC')
    kind = q_('kd2ind', [q_('jca', [lift(w, yr, Q), lift(w, zr, Q)], '( Y e. RR /\\ Z e. RR )'), q_('3jca', [mr, ym, mz], '( %s e. RR /\\ Y < %s /\\ %s <_ Z )' % (MX, MX, MX)), ibk2, kuy],
              '( ( u e. %s |-> %s ) e. L^1 /\\ S. %s %s _d u = S. ( %s (,) Z ) ( K / u ) _d u )' % (YZ, TRM2, YZ, TRM2, MX))
    mb = qy('bicomd', [qy('syl3anc', [lift(w, pr, Qy), lift(w, qr, Qy), ury, w.inst('maxle')], '( %s <_ u <-> ( p <_ u /\\ q <_ u ) )' % MX)], '( ( p <_ u /\\ q <_ u ) <-> %s <_ u )' % MX)
    tq = qy('ifbid', [mb], '%s = %s' % (TRM, TRM2))
    ib_t = q_('eqeltrd', [q_('mpteq2dva', [tq], '( u e. %s |-> %s ) = ( u e. %s |-> %s )' % (YZ, TRM, YZ, TRM2)), q_('simpld', [kind], '( u e. %s |-> %s ) e. L^1' % (YZ, TRM2))],
                  '( u e. %s |-> %s ) e. L^1' % (YZ, TRM))
    it_t = chain(w, Q, ['S. %s %s _d u' % (YZ, TRM), 'S. %s %s _d u' % (YZ, TRM2), 'S. ( %s (,) Z ) ( K / u ) _d u' % MX, '( K x. %s )' % LG],
                 [q_('itgeq2dv', [tq], 'S. %s %s _d u = S. %s %s _d u' % (YZ, TRM, YZ, TRM2)), q_('simprd', [kind], 'S. %s %s _d u = S. ( %s (,) Z ) ( K / u ) _d u' % (YZ, TRM2, MX)), itk])
    # inner itgfsum over q under ( ph /\\ p e. P )
    Ap = '( ph /\\ p e. P )'
    ap = mk(w, Ap)
    Ci = '( %s /\\ ( u e. %s /\\ q e. P ) )' % (Ap, YZ)
    tcc_i = rean(w, D(w, Qy, 'ifcld', [kuy, a1(w, Qy, '0cn', '0 e. CC')], '%s e. CC' % TRM), Ci)
    vol = a1(w, Ap, 'ioombl', '%s e. dom vol' % YZ)
    SQ = 'sum_ q e. P %s' % TRM
    f1 = ap('itgfsum', [vol, lift(w, pf, Ap), tcc_i, ib_t], '( ( u e. %s |-> %s ) e. L^1 /\\ S. %s %s _d u = sum_ q e. P S. %s %s _d u )' % (YZ, SQ, YZ, SQ, YZ, TRM))
    s_in = ap('sumeq2dv', [it_t], 'sum_ q e. P S. %s %s _d u = sum_ q e. P ( K x. %s )' % (YZ, TRM, LG))
    # outer itgfsum over p
    Co = '( ph /\\ ( u e. %s /\\ p e. P ) )' % YZ
    Cop = '( %s /\\ q e. P )' % Co
    tcc_o = rean(w, D(w, Qy, 'ifcld', [kuy, a1(w, Qy, '0cn', '0 e. CC')], '%s e. CC' % TRM), Cop)
    sqc = D(w, Co, 'fsumcl', [lift(w, pf, Co), tcc_o], '%s e. CC' % SQ)
    SP = 'sum_ p e. P %s' % SQ
    f2 = d('itgfsum', [a1(w, A, 'ioombl', '%s e. dom vol' % YZ), pf, sqc, ap('simpld', [f1], '( u e. %s |-> %s ) e. L^1' % (YZ, SQ))],
           '( ( u e. %s |-> %s ) e. L^1 /\\ S. %s %s _d u = sum_ p e. P S. %s %s _d u )' % (YZ, SP, YZ, SP, YZ, SQ))
    s_out = d('sumeq2dv', [ap('eqtrd', [ap('simprd', [f1], 'S. %s %s _d u = sum_ q e. P S. %s %s _d u' % (YZ, SQ, YZ, TRM)), s_in],
                                   'S. %s %s _d u = sum_ q e. P ( K x. %s )' % (YZ, SQ, LG))],
              'sum_ p e. P S. %s %s _d u = sum_ p e. P sum_ q e. P ( K x. %s )' % (YZ, SQ, LG))
    it = d('eqtrd', [d('simprd', [f2], 'S. %s %s _d u = sum_ p e. P S. %s %s _d u' % (YZ, SP, YZ, SQ)), s_out],
           'S. %s %s _d u = sum_ p e. P sum_ q e. P ( K x. %s )' % (YZ, SP, LG))
    fin = d('jca', [d('simpld', [f2], '( u e. %s |-> %s ) e. L^1' % (YZ, SP)), it], split_imp(S['cmuint'])[1])
    w.qed([fin], 'idi', S['cmuint'])
    return run(w, only)


if __name__ == '__main__':
    gen_sqx()
    gen_itgif()
    gen_uint()
