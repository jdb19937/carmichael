"""Sortie C6 section A: the sharper remainder bound (rectintrmb with the ratio
( abs ( Z - P ) ) / R in place of 1 / 2)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *
RPP = RE('P'); IPP = IM('P')
XV = '( ( Z - P ) / ( v - P ) )'
QN = '( ( ( abs ` ( Z - P ) ) / R ) ^ N )'

if __name__ == '__main__':
    w = W('holrmb', 'The Taylor remainder integral of order N is bounded by a constant times the N-th power of the ratio of the distance from the evaluation point to the centre and the distance R from the centre to the boundary frame.')
    A0 = '( ( %s /\\ N e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) )' % (BASE, RBDP, ALF)
    A1 = '( %s /\\ v e. %s )' % (A0, FR)
    bn = w.s([], 'simp1', '( %s -> ( %s /\\ N e. NN0 ) )' % (A0, BASE))
    bs = w.s([bn, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, BASE))
    hn = w.s([bn, w.inst('simpr')], 'syl', '( %s -> N e. NN0 )' % A0)
    rz = w.s([], 'simp2', '( %s -> ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) )' % (A0, RBDP))
    rb0 = w.s([rz, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
    zple = w.s([rz, w.inst('simpr')], 'syl', '( %s -> ( abs ` ( Z - P ) ) <_ ( R / 2 ) )' % A0)
    rbd = w.s([rb0, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP))
    rpos = w.s([rb0, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
    rr = w.s([rbd, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
    Rrp = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
    Hrp = w.s([Rrp], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % A0)
    mm = w.s([], 'simp3', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
    mr = w.s([mm, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
    alf = w.s([mm, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
    ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    tri = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (A0, INTP, INTZ))
    holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
    it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
    itz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTZ))
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    zc = w.s([itz, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
    ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RPP, RPP, RB, IA, IPP, IPP, IB))
    lr = w.s([ineq, w.inst('simpll')], 'syl', '( %s -> %s < %s )' % (A0, RA, RPP))
    rr_ = w.s([ineq, w.inst('simplr')], 'syl', '( %s -> %s < %s )' % (A0, RPP, RB))
    li = w.s([ineq, w.inst('simprl')], 'syl', '( %s -> %s < %s )' % (A0, IA, IPP))
    ri = w.s([ineq, w.inst('simprr')], 'syl', '( %s -> %s < %s )' % (A0, IPP, IB))
    ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA))
    br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
    ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA))
    bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    pr = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RPP))
    pi_ = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IPP))
    ler = w.s([ar, br, w.s([ar, pr, br, lr, rr_], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB))
    lei = w.s([ai, bi, w.s([ai, pi_, bi, li, ri], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))
    geo = w.s([ler, lei], 'jca', '( %s -> %s )' % (A0, GEO))
    fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    crd = w.s([hss, w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
    crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    e2d = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, E2))
    e2cp = w.s([crss, closed(w, A0, 'snsspr1', '{ P } C_ { P , Z }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CPP))
    e2cz = w.s([crss, closed(w, A0, 'snsspr2', '{ Z } C_ { P , Z }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CZZ))
    fr2 = w.s([w.s([ab, it, itz], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, INTZ)), w.inst('crectfrd')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, E2))
    cnR = w.s([w.s([w.s([fcn, e2d], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, E2)),
                    w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, E2, CPP)), w.s([zc, e2cz], 'jca', '( %s -> ( Z e. CC /\\ %s C_ %s ) )' % (A0, E2, CZZ))], 'jca',
                        '( %s -> ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) )' % (A0, E2, CPP, E2, CZZ)), hn], '3jca',
                   '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) /\\ N e. NN0 ) )' % (A0, E2, E2, CPP, E2, CZZ)), w.inst('rmcn')], 'syl',
               '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RM(E2, 'N'), E2))
    pse = w.s([ab, geo, w.s([cnR, closed(w, A0, 'ssid', '%s C_ %s' % (FR, FR)), fr2], '3jca',
                            '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s ) )' % (A0, RM(E2, 'N'), E2, FR, FR, FR, E2))], '3jca',
              '( %s -> ( %s /\\ %s /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s ) ) )' % (A0, AB, GEO, RM(E2, 'N'), E2, FR, FR, FR, E2))
    # per-point bound, in the fresh variable v
    dis = w.s([w.s([ab, it, rbd], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, RBDP)), w.inst('crectdis')], 'syl',
              '( %s -> A. u e. %s R <_ ( abs ` ( u - P ) ) )' % (A0, FR))
    cb1 = w.s([], 'oveq1', '( u = v -> ( u - P ) = ( v - P ) )')
    cb2 = w.s([cb1], 'fveq2d', '( u = v -> ( abs ` ( u - P ) ) = ( abs ` ( v - P ) ) )')
    cb3 = w.s([cb2], 'breq2d', '( u = v -> ( R <_ ( abs ` ( u - P ) ) <-> R <_ ( abs ` ( v - P ) ) ) )')
    disv = w.s([dis, w.s([cb3], 'cbvralvw', '( A. u e. %s R <_ ( abs ` ( u - P ) ) <-> A. v e. %s R <_ ( abs ` ( v - P ) ) )' % (FR, FR))],
               'sylib', '( %s -> A. v e. %s R <_ ( abs ` ( v - P ) ) )' % (A0, FR))
    cc1 = w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')
    cc2 = w.s([cc1], 'fveq2d', '( u = v -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` v ) ) )')
    cc3 = w.s([cc2], 'breq1d', '( u = v -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` v ) ) <_ M ) )')
    alfv = w.s([alf, w.s([cc3], 'cbvralvw', '( %s <-> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (ALF, FR))], 'sylib',
               '( %s -> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (A0, FR))
    vm = w.s([], 'simpr', '( %s -> v e. %s )' % (A1, FR))
    rle = w.s([w.s([disv], 'adantr', '( %s -> A. v e. %s R <_ ( abs ` ( v - P ) ) )' % (A1, FR)), vm, w.inst('rspa')], 'syl2anc', '( %s -> R <_ ( abs ` ( v - P ) ) )' % A1)
    fle = w.s([w.s([alfv], 'adantr', '( %s -> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (A1, FR)), vm, w.inst('rspa')], 'syl2anc', '( %s -> ( abs ` ( F ` v ) ) <_ M )' % A1)
    v2 = w.s([w.s([fr2], 'adantr', '( %s -> %s C_ %s )' % (A1, FR, E2)), vm], 'sseldd', '( %s -> v e. %s )' % (A1, E2))
    vd = w.s([w.s([e2d], 'adantr', '( %s -> %s C_ D )' % (A1, E2)), v2], 'sseldd', '( %s -> v e. D )' % A1)
    fv_ = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), vd], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A1)
    vcp = w.s([w.s([e2cp], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CPP)), v2], 'sseldd', '( %s -> v e. %s )' % (A1, CPP))
    vcz = w.s([w.s([e2cz], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CZZ)), v2], 'sseldd', '( %s -> v e. %s )' % (A1, CZZ))
    vc = w.s([w.s([vcp, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. CC /\\ v =/= P ) )' % A1), w.inst('simpl')], 'syl', '( %s -> v e. CC )' % A1)
    vnp = w.s([w.s([vcp, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. CC /\\ v =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> v =/= P )' % A1)
    vnz = w.s([w.s([vcz, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. CC /\\ v =/= Z ) )' % A1), w.inst('simpr')], 'syl', '( %s -> v =/= Z )' % A1)
    pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
    zc1 = w.s([zc], 'adantr', '( %s -> Z e. CC )' % A1)
    vp = w.s([vc, pc1], 'subcld', '( %s -> ( v - P ) e. CC )' % A1)
    vz = w.s([vc, zc1], 'subcld', '( %s -> ( v - Z ) e. CC )' % A1)
    vpn = w.s([vc, pc1, vnp], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % A1)
    vzn = w.s([vc, zc1, vnz], 'subne0d', '( %s -> ( v - Z ) =/= 0 )' % A1)
    zp1 = w.s([zc1, pc1], 'subcld', '( %s -> ( Z - P ) e. CC )' % A1)
    rr1 = w.s([rr], 'adantr', '( %s -> R e. RR )' % A1)
    Rrp1 = w.s([Rrp], 'adantr', '( %s -> R e. RR+ )' % A1)
    Hrp1 = w.s([Hrp], 'adantr', '( %s -> ( R / 2 ) e. RR+ )' % A1)
    mr1 = w.s([mr], 'adantr', '( %s -> M e. RR )' % A1)
    hn1 = w.s([hn], 'adantr', '( %s -> N e. NN0 )' % A1)
    zple1 = w.s([zple], 'adantr', '( %s -> ( abs ` ( Z - P ) ) <_ ( R / 2 ) )' % A1)
    avp = w.s([vp], 'abscld', '( %s -> ( abs ` ( v - P ) ) e. RR )' % A1)
    avz = w.s([vz], 'abscld', '( %s -> ( abs ` ( v - Z ) ) e. RR )' % A1)
    azp = w.s([zp1], 'abscld', '( %s -> ( abs ` ( Z - P ) ) e. RR )' % A1)
    hr1 = w.s([Hrp1], 'rpred', '( %s -> ( R / 2 ) e. RR )' % A1)
    # ( R / 2 ) <_ ( abs ` ( v - Z ) )
    tri1 = w.s([w.s([w.s([vz, zp1], 'abstrid', '( %s -> ( abs ` ( ( v - Z ) + ( Z - P ) ) ) <_ ( ( abs ` ( v - Z ) ) + ( abs ` ( Z - P ) ) ) )' % A1)],
                    'eqbrtrrd', '') if False else w.s([w.s([vc, zc1, pc1, w.inst('npncan')], 'syl3anc', '( %s -> ( ( v - Z ) + ( Z - P ) ) = ( v - P ) )' % A1)], 'fveq2d',
                                                      '( %s -> ( abs ` ( ( v - Z ) + ( Z - P ) ) ) = ( abs ` ( v - P ) ) )' % A1),
                w.s([vz, zp1], 'abstrid', '( %s -> ( abs ` ( ( v - Z ) + ( Z - P ) ) ) <_ ( ( abs ` ( v - Z ) ) + ( abs ` ( Z - P ) ) ) )' % A1)], 'eqbrtrrd',
               '( %s -> ( abs ` ( v - P ) ) <_ ( ( abs ` ( v - Z ) ) + ( abs ` ( Z - P ) ) ) )' % A1)
    tri2 = w.s([avz, azp, hr1, zple1], 'leadd2dd', '( %s -> ( ( abs ` ( v - Z ) ) + ( abs ` ( Z - P ) ) ) <_ ( ( abs ` ( v - Z ) ) + ( R / 2 ) ) )' % A1)
    rle2 = w.s([rr1, avp, w.s([avz, hr1], 'readdcld', '( %s -> ( ( abs ` ( v - Z ) ) + ( R / 2 ) ) e. RR )' % A1), rle,
                w.s([avp, w.s([avz, azp], 'readdcld', '( %s -> ( ( abs ` ( v - Z ) ) + ( abs ` ( Z - P ) ) ) e. RR )' % A1), w.s([avz, hr1], 'readdcld', '( %s -> ( ( abs ` ( v - Z ) ) + ( R / 2 ) ) e. RR )' % A1), tri1, tri2], 'letrd',
                    '( %s -> ( abs ` ( v - P ) ) <_ ( ( abs ` ( v - Z ) ) + ( R / 2 ) ) )' % A1)], 'letrd',
               '( %s -> R <_ ( ( abs ` ( v - Z ) ) + ( R / 2 ) ) )' % A1)
    rhalf = w.s([w.s([w.s([w.s([rr1], 'recnd', '( %s -> R e. CC )' % A1)], '2halvesd', '( %s -> ( ( R / 2 ) + ( R / 2 ) ) = R )' % A1)], 'oveq1d',
                     '( %s -> ( ( ( R / 2 ) + ( R / 2 ) ) - ( R / 2 ) ) = ( R - ( R / 2 ) ) )' % A1),
                 w.s([w.s([hr1], 'recnd', '( %s -> ( R / 2 ) e. CC )' % A1), w.s([hr1], 'recnd', '( %s -> ( R / 2 ) e. CC )' % A1)], 'pncand',
                     '( %s -> ( ( ( R / 2 ) + ( R / 2 ) ) - ( R / 2 ) ) = ( R / 2 ) )' % A1)], 'eqtr3d',
                '( %s -> ( R - ( R / 2 ) ) = ( R / 2 ) )' % A1)
    hle = w.s([rhalf, w.s([w.s([rr1, hr1, avz, w.inst('lesubadd')], 'syl3anc', '( %s -> ( ( R - ( R / 2 ) ) <_ ( abs ` ( v - Z ) ) <-> R <_ ( ( abs ` ( v - Z ) ) + ( R / 2 ) ) ) )' % A1), rle2], 'mpbird',
                          '( %s -> ( R - ( R / 2 ) ) <_ ( abs ` ( v - Z ) ) )' % A1)], 'eqbrtrrd', '( %s -> ( R / 2 ) <_ ( abs ` ( v - Z ) ) )' % A1)
    # ( abs ` XV ) <_ ( ( abs ` ( Z - P ) ) / R )
    axv = w.s([zp1, vp, vpn], 'absdivd', '( %s -> ( abs ` %s ) = ( ( abs ` ( Z - P ) ) / ( abs ` ( v - P ) ) ) )' % (A1, XV))
    xle = w.s([axv, w.s([w.s([w.s([rr1, w.s([rpos], 'adantr', '( %s -> 0 < R )' % A1)], 'jca', '( %s -> ( R e. RR /\\ 0 < R ) )' % A1),
                                  w.s([avp, w.s([rr1, avp, w.s([rpos], 'adantr', '( %s -> 0 < R )' % A1), rle], 'ltletrd', '( %s -> 0 < ( abs ` ( v - P ) ) )' % A1)], 'jca',
                                      '( %s -> ( ( abs ` ( v - P ) ) e. RR /\\ 0 < ( abs ` ( v - P ) ) ) )' % A1),
                                  w.s([azp, w.s([zp1], 'absge0d', '( %s -> 0 <_ ( abs ` ( Z - P ) ) )' % A1)], 'jca', '( %s -> ( ( abs ` ( Z - P ) ) e. RR /\\ 0 <_ ( abs ` ( Z - P ) ) ) )' % A1)], '3jca',
                             '( %s -> ( ( R e. RR /\\ 0 < R ) /\\ ( ( abs ` ( v - P ) ) e. RR /\\ 0 < ( abs ` ( v - P ) ) ) /\\ ( ( abs ` ( Z - P ) ) e. RR /\\ 0 <_ ( abs ` ( Z - P ) ) ) ) )' % A1),
                         rle, w.inst('lediv2a')], 'syl2anc', '( %s -> ( ( abs ` ( Z - P ) ) / ( abs ` ( v - P ) ) ) <_ ( ( abs ` ( Z - P ) ) / R ) )' % A1)], 'eqbrtrd',
               '( %s -> ( abs ` %s ) <_ ( ( abs ` ( Z - P ) ) / R ) )' % (A1, XV))
    axr = w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, XV))
    halfr = w.s([azp, Rrp1], 'rerpdivcld', '( %s -> ( ( abs ` ( Z - P ) ) / R ) e. RR )' % A1)
    xnle = w.s([axr, halfr, hn1, w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A1, XV)), xle], 'leexp1ad',
               '( %s -> ( ( abs ` %s ) ^ N ) <_ %s )' % (A1, XV, QN))
    # the value of the remainder kernel at v and its absolute value
    sv1 = w.s([], 'fveq2', '( y = v -> ( F ` y ) = ( F ` v ) )')
    sv2 = w.s([], 'oveq1', '( y = v -> ( y - P ) = ( v - P ) )')
    sv3 = w.s([sv2], 'oveq2d', '( y = v -> %s = %s )' % (XY, XV))
    sv4 = w.s([sv3], 'oveq1d', '( y = v -> ( %s ^ N ) = ( %s ^ N ) )' % (XY, XV))
    sv5 = w.s([sv1, sv4], 'oveq12d', '( y = v -> ( ( F ` y ) x. ( %s ^ N ) ) = ( ( F ` v ) x. ( %s ^ N ) ) )' % (XY, XV))
    sv6 = w.s([], 'oveq1', '( y = v -> ( y - Z ) = ( v - Z ) )')
    BV = '( ( ( F ` v ) x. ( %s ^ N ) ) / ( v - Z ) )' % XV
    sv7 = w.s([sv5, sv6], 'oveq12d', '( y = v -> ( ( ( F ` y ) x. ( %s ^ N ) ) / ( y - Z ) ) = %s )' % (XY, BV))
    emv = w.s([], 'eqid', '%s = %s' % (RM(E2, 'N'), RM(E2, 'N')))
    fmv = w.s([sv7, emv], 'fvmptg', '( ( v e. %s /\\ %s e. _V ) -> ( %s ` v ) = %s )' % (E2, BV, RM(E2, 'N'), BV))
    vval = w.s([v2, ovexd(w, A1, BV), fmv], 'syl2anc', '( %s -> ( %s ` v ) = %s )' % (A1, RM(E2, 'N'), BV))
    xnc = w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV)), hn1], 'expcld', '( %s -> ( %s ^ N ) e. CC )' % (A1, XV))
    absq = w.s([w.s([fv_, xnc], 'mulcld', '( %s -> ( ( F ` v ) x. ( %s ^ N ) ) e. CC )' % (A1, XV)), vz, vzn], 'absdivd',
               '( %s -> ( abs ` %s ) = ( ( abs ` ( ( F ` v ) x. ( %s ^ N ) ) ) / ( abs ` ( v - Z ) ) ) )' % (A1, BV, XV))
    absn = w.s([w.s([fv_, xnc], 'absmuld', '( %s -> ( abs ` ( ( F ` v ) x. ( %s ^ N ) ) ) = ( ( abs ` ( F ` v ) ) x. ( abs ` ( %s ^ N ) ) ) )' % (A1, XV, XV)),
                w.s([w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV)), hn1, w.inst('absexp')], 'syl2anc',
                         '( %s -> ( abs ` ( %s ^ N ) ) = ( ( abs ` %s ) ^ N ) )' % (A1, XV, XV))], 'oveq2d',
                    '( %s -> ( ( abs ` ( F ` v ) ) x. ( abs ` ( %s ^ N ) ) ) = ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) )' % (A1, XV, XV))], 'eqtrd',
               '( %s -> ( abs ` ( ( F ` v ) x. ( %s ^ N ) ) ) = ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) )' % (A1, XV, XV))
    afv = w.s([fv_], 'abscld', '( %s -> ( abs ` ( F ` v ) ) e. RR )' % A1)
    xnr = w.s([axr, hn1], 'reexpcld', '( %s -> ( ( abs ` %s ) ^ N ) e. RR )' % (A1, XV))
    halfn = w.s([halfr, hn1], 'reexpcld', '( %s -> %s e. RR )' % (A1, QN))
    num = w.s([w.s([afv, mr1, xnr, halfn, w.s([fv_], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A1),
                    w.s([axr, w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A1, XV)), hn1], 'expge0d', '( %s -> 0 <_ ( ( abs ` %s ) ^ N ) )' % (A1, XV)),
                    fle, xnle], 'lemul12ad', '( %s -> ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) <_ ( M x. %s ) )' % (A1, XV, QN))], 'id', '') if False else \
        w.s([afv, mr1, xnr, halfn, fle, xnle], 'lemul12ad', '( %s -> ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) <_ ( M x. %s ) )' % (A1, XV, QN))
    ptb = w.s([w.s([afv, xnr], 'remulcld', '( %s -> ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) e. RR )' % (A1, XV)),
               w.s([mr1, halfn], 'remulcld', '( %s -> ( M x. %s ) e. RR )' % (A1, QN)), Hrp1, avz,
               w.s([afv, xnr, w.s([fv_], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A1),
                    w.s([axr, w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A1, XV)), hn1], 'expge0d', '( %s -> 0 <_ ( ( abs ` %s ) ^ N ) )' % (A1, XV))], 'mulge0d',
                   '( %s -> 0 <_ ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) )' % (A1, XV)), num, hle], 'lediv12ad',
              '( %s -> ( ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) / ( abs ` ( v - Z ) ) ) <_ ( ( M x. %s ) / ( R / 2 ) ) )' % (A1, XV, QN))
    pw = w.s([w.s([w.s([w.s([vval], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` %s ) )' % (A1, RM(E2, 'N'), BV)), absq], 'eqtrd',
                        '( %s -> ( abs ` ( %s ` v ) ) = ( ( abs ` ( ( F ` v ) x. ( %s ^ N ) ) ) / ( abs ` ( v - Z ) ) ) )' % (A1, RM(E2, 'N'), XV)),
                   w.s([absn], 'oveq1d', '( %s -> ( ( abs ` ( ( F ` v ) x. ( %s ^ N ) ) ) / ( abs ` ( v - Z ) ) ) = ( ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) / ( abs ` ( v - Z ) ) ) )' % (A1, XV, XV))], 'eqtrd',
                  '( %s -> ( abs ` ( %s ` v ) ) = ( ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) / ( abs ` ( v - Z ) ) ) )' % (A1, RM(E2, 'N'), XV)), ptb], 'eqbrtrd',
             '( %s -> ( abs ` ( %s ` v ) ) <_ ( ( M x. %s ) / ( R / 2 ) ) )' % (A1, RM(E2, 'N'), QN))
    allv = w.s([pw], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ ( ( M x. %s ) / ( R / 2 ) ) )' % (A0, FR, RM(E2, 'N'), QN))
    halfr0 = w.s([w.s([w.s([zc, pc], 'subcld', '( %s -> ( Z - P ) e. CC )' % A0)], 'abscld', '( %s -> ( abs ` ( Z - P ) ) e. RR )' % A0), Rrp], 'rerpdivcld', '( %s -> ( ( abs ` ( Z - P ) ) / R ) e. RR )' % A0)
    halfn0 = w.s([halfr0, hn], 'reexpcld', '( %s -> %s e. RR )' % (A0, QN))
    bndr = w.s([w.s([mr, halfn0], 'remulcld', '( %s -> ( M x. %s ) e. RR )' % (A0, QN)), Hrp], 'rerpdivcld', '( %s -> ( ( M x. %s ) / ( R / 2 ) ) e. RR )' % (A0, QN))
    abse = w.s([pse, bndr, allv, w.inst('rectintabse')], 'syl3anc',
               '( %s -> ( abs ` %s ) <_ ( ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) x. %s ) )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'), QN, PER))
    # rearrange the bound into K x. ( ( 1 / 2 ) ^ N )
    perr = w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)), w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
    perc = w.s([perr], 'recnd', '( %s -> %s e. CC )' % (A0, PER))
    mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
    hc = w.s([w.s([Hrp], 'rpred', '( %s -> ( R / 2 ) e. RR )' % A0)], 'recnd', '( %s -> ( R / 2 ) e. CC )' % A0)
    hne = w.s([Hrp], 'rpne0d', '( %s -> ( R / 2 ) =/= 0 )' % A0)
    tc = w.s([halfn0], 'recnd', '( %s -> %s e. CC )' % (A0, QN))
    t2c = closed(w, A0, '2cn', '2 e. CC')
    mq = w.s([mc, hc, hne], 'divcld', '( %s -> ( M / ( R / 2 ) ) e. CC )' % A0)
    K = '( ( 2 x. ( M / ( R / 2 ) ) ) x. %s )' % PER
    r1 = w.s([mc, tc, hc, hne], 'div23d', '( %s -> ( ( M x. %s ) / ( R / 2 ) ) = ( ( M / ( R / 2 ) ) x. %s ) )' % (A0, QN, QN))
    r2 = w.s([w.s([r1], 'oveq2d', '( %s -> ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) = ( 2 x. ( ( M / ( R / 2 ) ) x. %s ) ) )' % (A0, QN, QN)),
              w.s([w.s([t2c, mq, tc], 'mulassd', '( %s -> ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) = ( 2 x. ( ( M / ( R / 2 ) ) x. %s ) ) )' % (A0, QN, QN))], 'eqcomd',
                  '( %s -> ( 2 x. ( ( M / ( R / 2 ) ) x. %s ) ) = ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) )' % (A0, QN, QN))], 'eqtrd',
             '( %s -> ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) = ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) )' % (A0, QN, QN))
    r3 = w.s([w.s([r2], 'oveq1d', '( %s -> ( ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) x. %s ) = ( ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) x. %s ) )' % (A0, QN, PER, QN, PER)),
              w.s([w.s([t2c, mq], 'mulcld', '( %s -> ( 2 x. ( M / ( R / 2 ) ) ) e. CC )' % A0), tc, perc], 'mul32d',
                  '( %s -> ( ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) x. %s ) = ( %s x. %s ) )' % (A0, QN, PER, K, QN))], 'eqtrd',
             '( %s -> ( ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) x. %s ) = ( %s x. %s ) )' % (A0, QN, PER, K, QN))
    w.qed([abse, r3], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'), K, QN)); run1(w)

