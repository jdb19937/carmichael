"""Sortie C8, section 1: bounds on a compact rectangle (crectbnd, crectlbd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *

TK = '( %s |`t ( A crect B ) )' % TOP
UTK = 'U. %s' % TK
TG = '( topGen ` ran (,) )'


def gen_crectbnd():
    w = W('crectbnd', 'A continuous function is bounded on a closed rectangle ( ~ bndth on the compact rectangle ~ crectcmp ).')
    A0 = '( ( A e. CC /\\ B e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )'
    ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
    gh = w.s([], 'simpr', '( %s -> ( G e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )' % A0)
    gcn = w.s([gh, w.inst('simpl')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
    kd = w.s([gh, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    GK = '( G |` ( A crect B ) )'
    gk = w.s([kd, gcn, w.inst('rescncf')], 'sylc', '( %s -> %s e. ( ( A crect B ) -cn-> CC ) )' % (A0, GK))
    absc = w.s([w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'a1i', '( %s -> abs e. ( CC -cn-> RR ) )' % A0)
    AG = '( abs o. %s )' % GK
    ag = w.s([gk, absc], 'cncfco', '( %s -> %s e. ( ( A crect B ) -cn-> RR ) )' % (A0, AG))
    crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    e1 = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    e2 = w.s([], 'eqid', '%s = %s' % (TK, TK))
    e3 = w.s([], 'tgioo4', '%s = ( %s |`t RR )' % (TG, TOP))
    cn = w.s([e1, e2, e3], 'cncfcn', '( ( ( A crect B ) C_ CC /\\ RR C_ CC ) -> ( ( A crect B ) -cn-> RR ) = ( %s Cn %s ) )' % (TK, TG))
    cn2 = w.s([crss, w.s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', '( %s -> RR C_ CC )' % A0), cn], 'syl2anc',
              '( %s -> ( ( A crect B ) -cn-> RR ) = ( %s Cn %s ) )' % (A0, TK, TG))
    agc = w.s([ag, cn2], 'eleqtrd', '( %s -> %s e. ( %s Cn %s ) )' % (A0, AG, TK, TG))
    cmp = w.s([ab, w.inst('crectcmp')], 'syl', '( %s -> %s e. Comp )' % (A0, TK))
    b0 = w.s([w.s([], 'eqid', '%s = %s' % (UTK, UTK)), w.s([], 'eqid', '%s = %s' % (TG, TG)), cmp, agc], 'bndth',
             '( %s -> E. m e. RR A. u e. %s ( %s ` u ) <_ m )' % (A0, UTK, AG))
    uni = w.s([w.s([w.s([e1], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP)), crss,
               w.s([w.s([], 'unicntop', 'CC = U. %s' % TOP)], 'restuni', '( ( %s e. Top /\\ ( A crect B ) C_ CC ) -> ( A crect B ) = %s )' % (TOP, UTK))],
              'syl2anc', '( %s -> ( A crect B ) = %s )' % (A0, UTK))
    uni2 = w.s([uni], 'eqcomd', '( %s -> %s = ( A crect B ) )' % (A0, UTK))
    b1 = w.s([uni2], 'raleqdv', '( %s -> ( A. u e. %s ( %s ` u ) <_ m <-> A. u e. ( A crect B ) ( %s ` u ) <_ m ) )' % (A0, UTK, AG, AG))
    # pointwise value
    A1 = '( %s /\\ u e. ( A crect B ) )' % A0
    uin = w.s([], 'simpr', '( %s -> u e. ( A crect B ) )' % A1)
    gkf = w.s([w.s([gk, w.inst('cncff')], 'syl', '( %s -> %s : ( A crect B ) --> CC )' % (A0, GK))], 'adantr', '( %s -> %s : ( A crect B ) --> CC )' % (A1, GK))
    v1 = w.s([gkf, uin, w.inst('fvco3')], 'syl2anc', '( %s -> ( %s ` u ) = ( abs ` ( %s ` u ) ) )' % (A1, AG, GK))
    v2 = w.s([w.s([uin, w.inst('fvres')], 'syl', '( %s -> ( %s ` u ) = ( G ` u ) )' % (A1, GK))], 'fveq2d',
             '( %s -> ( abs ` ( %s ` u ) ) = ( abs ` ( G ` u ) ) )' % (A1, GK))
    v3 = w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` u ) = ( abs ` ( G ` u ) ) )' % (A1, AG))
    v4 = w.s([v3], 'breq1d', '( %s -> ( ( %s ` u ) <_ m <-> ( abs ` ( G ` u ) ) <_ m ) )' % (A1, AG))
    b2 = w.s([v4], 'ralbidva', '( %s -> ( A. u e. ( A crect B ) ( %s ` u ) <_ m <-> A. u e. ( A crect B ) ( abs ` ( G ` u ) ) <_ m ) )' % (A0, AG))
    b3 = w.s([b1, b2], 'bitrd', '( %s -> ( A. u e. %s ( %s ` u ) <_ m <-> A. u e. ( A crect B ) ( abs ` ( G ` u ) ) <_ m ) )' % (A0, UTK, AG))
    b4 = w.s([b3], 'rexbidv', '( %s -> ( E. m e. RR A. u e. %s ( %s ` u ) <_ m <-> E. m e. RR A. u e. ( A crect B ) ( abs ` ( G ` u ) ) <_ m ) )' % (A0, UTK, AG))
    w.qed([b0, b4], 'mpbid', '( %s -> E. m e. RR A. u e. ( A crect B ) ( abs ` ( G ` u ) ) <_ m )' % A0)
    return run8(w)


def gen_crectlbd():
    w = W('crectlbd', 'A continuous function without zeros on a closed rectangle is bounded away from zero there.')
    NZG = 'A. y e. ( A crect B ) ( G ` y ) =/= 0'
    A0 = '( ( A e. CC /\\ B e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) /\\ %s )' % NZG
    ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
    gh = w.s([], 'simp2', '( %s -> ( G e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )' % A0)
    nz = w.s([], 'simp3', '( %s -> %s )' % (A0, NZG))
    gcn = w.s([gh, w.inst('simpl')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
    kd = w.s([gh, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    GK = '( G |` ( A crect B ) )'
    gk = w.s([kd, gcn, w.inst('rescncf')], 'sylc', '( %s -> %s e. ( ( A crect B ) -cn-> CC ) )' % (A0, GK))
    gkf = w.s([gk, w.inst('cncff')], 'syl', '( %s -> %s : ( A crect B ) --> CC )' % (A0, GK))
    MG = '( x e. ( A crect B ) |-> ( G ` x ) )'
    # the mapping form of G on the rectangle
    A1 = '( %s /\\ x e. ( A crect B ) )' % A0
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A0)
    feq = w.s([gf, kd], 'feqresmpt', '( %s -> %s = %s )' % (A0, GK, MG))
    mgc = w.s([gk, feq], 'eqeltrrd', '( %s -> %s e. ( ( A crect B ) -cn-> CC ) )' % (A0, MG))
    # values G x in CC \ { 0 }
    xin = w.s([], 'simpr', '( %s -> x e. ( A crect B ) )' % A1)
    gxc = w.s([w.s([gf], 'adantr', '( %s -> G : D --> CC )' % A1), w.s([w.s([kd], 'adantr', '( %s -> ( A crect B ) C_ D )' % A1), xin], 'sseldd', '( %s -> x e. D )' % A1)],
              'ffvelcdmd', '( %s -> ( G ` x ) e. CC )' % A1)
    sub = w.s([], 'fveq2', '( y = x -> ( G ` y ) = ( G ` x ) )')
    sub2 = w.s([sub], 'neeq1d', '( y = x -> ( ( G ` y ) =/= 0 <-> ( G ` x ) =/= 0 ) )')
    gx0 = w.s([sub2, xin, w.s([nz], 'adantr', '( %s -> %s )' % (A1, NZG))], 'rspcdva', '( %s -> ( G ` x ) =/= 0 )' % A1)
    gxn = w.s([w.s([gxc, gx0], 'jca', '( %s -> ( ( G ` x ) e. CC /\\ ( G ` x ) =/= 0 ) )' % A1),
               w.s([], 'eldifsn', '( ( G ` x ) e. ( CC \\ { 0 } ) <-> ( ( G ` x ) e. CC /\\ ( G ` x ) =/= 0 ) )')], 'sylibr',
              '( %s -> ( G ` x ) e. ( CC \\ { 0 } ) )' % A1)
    mgf = w.s([gxn], 'fmpttd', '( %s -> %s : ( A crect B ) --> ( CC \\ { 0 } ) )' % (A0, MG))
    difss = w.s([w.s([], 'difss', '( CC \\ { 0 } ) C_ CC')], 'a1i', '( %s -> ( CC \\ { 0 } ) C_ CC )' % A0)
    mgn = w.s([w.s([difss, mgc, w.inst('cncfcdm')], 'syl2anc', '( %s -> ( %s e. ( ( A crect B ) -cn-> ( CC \\ { 0 } ) ) <-> %s : ( A crect B ) --> ( CC \\ { 0 } ) ) )' % (A0, MG, MG)), mgf],
              'mpbird', '( %s -> %s e. ( ( A crect B ) -cn-> ( CC \\ { 0 } ) ) )' % (A0, MG))
    crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    onec = w.s([], '1cnd', '( %s -> 1 e. CC )' % A0)
    one = w.s([onec, crss, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), w.inst('cncfmptc')], 'syl3anc',
              '( %s -> ( x e. ( A crect B ) |-> 1 ) e. ( ( A crect B ) -cn-> CC ) )' % A0)
    INV = '( x e. ( A crect B ) |-> ( 1 / ( G ` x ) ) )'
    inv = w.s([one, mgn], 'divcncf', '( %s -> %s e. ( ( A crect B ) -cn-> CC ) )' % (A0, INV))
    kk = w.s([], 'ssidd', '( %s -> ( A crect B ) C_ ( A crect B ) )' % A0)
    bh = w.s([ab, w.s([inv, kk], 'jca', '( %s -> ( %s e. ( ( A crect B ) -cn-> CC ) /\\ ( A crect B ) C_ ( A crect B ) ) )' % (A0, INV)), w.inst('crectbnd')], 'syl2anc',
             '( %s -> E. n e. RR A. v e. ( A crect B ) ( abs ` ( %s ` v ) ) <_ n )' % (A0, INV))
    # from a bound n on abs ( 1 / G ) to the lower bound 1 / ( abs n + 1 )
    BV = 'A. v e. ( A crect B ) ( abs ` ( %s ` v ) ) <_ n' % INV
    A2 = '( ( %s /\\ n e. RR ) /\\ %s )' % (A0, BV)
    a0 = w.s([], 'simpll', '( %s -> %s )' % (A2, A0))
    nr = w.s([], 'simplr', '( %s -> n e. RR )' % A2)
    nb = w.s([], 'simpr', '( %s -> %s )' % (A2, BV))
    M1 = '( ( abs ` n ) + 1 )'
    nc = w.s([nr], 'recnd', '( %s -> n e. CC )' % A2)
    amr = w.s([nc], 'abscld', '( %s -> ( abs ` n ) e. RR )' % A2)
    am0 = w.s([nc], 'absge0d', '( %s -> 0 <_ ( abs ` n ) )' % A2)
    one2 = w.s([], '1red', '( %s -> 1 e. RR )' % A2)
    m1r = w.s([amr, one2], 'readdcld', '( %s -> %s e. RR )' % (A2, M1))
    m1p = w.s([amr, one2, am0, w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % A2)], 'addgegt0d', '( %s -> 0 < %s )' % (A2, M1))
    m1rp = w.s([m1r, m1p], 'elrpd', '( %s -> %s e. RR+ )' % (A2, M1))
    L = '( 1 / %s )' % M1
    lrp = w.s([m1rp], 'rpreccld', '( %s -> %s e. RR+ )' % (A2, L))
    A3 = '( %s /\\ u e. ( A crect B ) )' % A2
    uin = w.s([], 'simpr', '( %s -> u e. ( A crect B ) )' % A3)
    a0u = w.s([a0], 'adantr', '( %s -> %s )' % (A3, A0))
    gf3 = w.s([a0u, gf], 'syl', '( %s -> G : D --> CC )' % A3)
    ud = w.s([w.s([a0u, kd], 'syl', '( %s -> ( A crect B ) C_ D )' % A3), uin], 'sseldd', '( %s -> u e. D )' % A3)
    guc = w.s([gf3, ud], 'ffvelcdmd', '( %s -> ( G ` u ) e. CC )' % A3)
    subu = w.s([], 'fveq2', '( y = u -> ( G ` y ) = ( G ` u ) )')
    subu2 = w.s([subu], 'neeq1d', '( y = u -> ( ( G ` y ) =/= 0 <-> ( G ` u ) =/= 0 ) )')
    gu0 = w.s([subu2, uin, w.s([a0u, nz], 'syl', '( %s -> %s )' % (A3, NZG))], 'rspcdva', '( %s -> ( G ` u ) =/= 0 )' % A3)
    subv = w.s([w.s([w.s([], 'fveq2', '( v = u -> ( %s ` v ) = ( %s ` u ) )' % (INV, INV))], 'fveq2d',
                    '( v = u -> ( abs ` ( %s ` v ) ) = ( abs ` ( %s ` u ) ) )' % (INV, INV))], 'breq1d',
               '( v = u -> ( ( abs ` ( %s ` v ) ) <_ n <-> ( abs ` ( %s ` u ) ) <_ n ) )' % (INV, INV))
    bu = w.s([subv, uin, w.s([nb], 'adantr', '( %s -> %s )' % (A3, BV))], 'rspcdva', '( %s -> ( abs ` ( %s ` u ) ) <_ n )' % (A3, INV))
    sx = w.s([w.s([], 'fveq2', '( x = u -> ( G ` x ) = ( G ` u ) )')], 'oveq2d', '( x = u -> ( 1 / ( G ` x ) ) = ( 1 / ( G ` u ) ) )')
    one3 = w.s([], '1cnd', '( %s -> 1 e. CC )' % A3)
    ic = w.s([one3, guc, gu0], 'divcld', '( %s -> ( 1 / ( G ` u ) ) e. CC )' % A3)
    em = w.s([], 'eqid', '%s = %s' % (INV, INV))
    fvm = w.s([sx, em], 'fvmptg', '( ( u e. ( A crect B ) /\\ ( 1 / ( G ` u ) ) e. CC ) -> ( %s ` u ) = ( 1 / ( G ` u ) ) )' % INV)
    fv = w.s([uin, ic, fvm], 'syl2anc', '( %s -> ( %s ` u ) = ( 1 / ( G ` u ) ) )' % (A3, INV))
    ab1 = w.s([one3, guc, gu0], 'absdivd', '( %s -> ( abs ` ( 1 / ( G ` u ) ) ) = ( ( abs ` 1 ) / ( abs ` ( G ` u ) ) ) )' % A3)
    ab2 = w.s([w.s([w.s([], 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( %s -> ( abs ` 1 ) = 1 )' % A3)], 'oveq1d',
              '( %s -> ( ( abs ` 1 ) / ( abs ` ( G ` u ) ) ) = ( 1 / ( abs ` ( G ` u ) ) ) )' % A3)
    ab3 = w.s([w.s([w.s([fv], 'fveq2d', '( %s -> ( abs ` ( %s ` u ) ) = ( abs ` ( 1 / ( G ` u ) ) ) )' % (A3, INV)), ab1], 'eqtrd',
                   '( %s -> ( abs ` ( %s ` u ) ) = ( ( abs ` 1 ) / ( abs ` ( G ` u ) ) ) )' % (A3, INV)), ab2], 'eqtrd',
              '( %s -> ( abs ` ( %s ` u ) ) = ( 1 / ( abs ` ( G ` u ) ) ) )' % (A3, INV))
    b1 = w.s([ab3, bu], 'eqbrtrrd', '( %s -> ( 1 / ( abs ` ( G ` u ) ) ) <_ n )' % A3)
    n3r = w.s([nr], 'adantr', '( %s -> n e. RR )' % A3)
    nle = w.s([n3r, w.inst('leabs')], 'syl', '( %s -> n <_ ( abs ` n ) )' % A3)
    am3 = w.s([w.s([n3r], 'recnd', '( %s -> n e. CC )' % A3)], 'abscld', '( %s -> ( abs ` n ) e. RR )' % A3)
    m1lt = w.s([am3], 'ltp1d', '( %s -> ( abs ` n ) < %s )' % (A3, M1))
    m1r3 = w.s([am3, w.s([], '1red', '( %s -> 1 e. RR )' % A3)], 'readdcld', '( %s -> %s e. RR )' % (A3, M1))
    mm1 = w.s([n3r, am3, m1r3, nle, w.s([m1lt], 'ltled', '( %s -> ( abs ` n ) <_ %s )' % (A3, M1))], 'letrd', '( %s -> n <_ %s )' % (A3, M1))
    agrp = w.s([guc, gu0], 'absrpcld', '( %s -> ( abs ` ( G ` u ) ) e. RR+ )' % A3)
    b2 = w.s([w.s([agrp], 'rprecred', '( %s -> ( 1 / ( abs ` ( G ` u ) ) ) e. RR )' % A3), n3r, m1r3, b1, mm1], 'letrd',
             '( %s -> ( 1 / ( abs ` ( G ` u ) ) ) <_ %s )' % (A3, M1))
    m1rp3 = w.s([m1rp], 'adantr', '( %s -> %s e. RR+ )' % (A3, M1))
    b3 = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % A3), agrp, m1rp3, b2], 'lediv23d', '( %s -> %s <_ ( abs ` ( G ` u ) ) )' % (A3, L))
    ral = w.s([b3], 'ralrimiva', '( %s -> A. u e. ( A crect B ) %s <_ ( abs ` ( G ` u ) ) )' % (A2, L))
    subm = w.s([], 'breq1', '( m = %s -> ( m <_ ( abs ` ( G ` u ) ) <-> %s <_ ( abs ` ( G ` u ) ) ) )' % (L, L))
    subm2 = w.s([subm], 'ralbidv', '( m = %s -> ( A. u e. ( A crect B ) m <_ ( abs ` ( G ` u ) ) <-> A. u e. ( A crect B ) %s <_ ( abs ` ( G ` u ) ) ) )' % (L, L))
    CONC = 'E. m e. RR+ A. u e. ( A crect B ) m <_ ( abs ` ( G ` u ) )'
    ex = w.s([lrp, ral, w.s([subm2], 'rspcev', '( ( %s e. RR+ /\\ A. u e. ( A crect B ) %s <_ ( abs ` ( G ` u ) ) ) -> %s )' % (L, L, CONC))],
             'syl2anc', '( %s -> %s )' % (A2, CONC))
    ex2 = w.s([w.s([ex], 'ex', '( ( %s /\\ n e. RR ) -> ( %s -> %s ) )' % (A0, BV, CONC))],
              'rexlimdva', '( %s -> ( E. n e. RR %s -> %s ) )' % (A0, BV, CONC))
    w.qed([bh, ex2], 'mpd', '( %s -> %s )' % (A0, CONC))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_crectbnd, gen_crectlbd]:
        g()
