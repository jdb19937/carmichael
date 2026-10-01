"""Sortie C6: shared expressions and step patterns (the order of vanishing,
the local factorisation, finiteness of zeros).  Built on tools/gen/c2_lib.py
(sorties C0, C0b, C0c, C1, C2)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c2_lib import *

# ---- C1's Taylor apparatus, restated ---------------------------------------
CPP = '( CC \\ { P } )'; CZZ = '( CC \\ { Z } )'
PUP = '( ( A crect B ) \\ { P } )'
E2 = '( ( A crect B ) \\ { P , Z } )'
XY = '( ( Z - P ) / ( y - P ) )'
BASE = '( %s /\\ ( %s /\\ %s /\\ P =/= Z ) /\\ %s )' % (AB, INTP, INTZ, HOLO)
RBDP = RBD('P')
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
TPI = '( 2 x. ( _i x. _pi ) )'
KK = '( ( 2 x. ( M / ( R / 2 ) ) ) x. %s )' % PER
LHS = '( %s x. ( F ` Z ) )' % TPI
# the standing hypotheses of the analytic block: rectangle inside D, the
# distance R to the frame, the frame bound M
RECT = '( %s /\\ %s /\\ ( A crect B ) C_ D )' % (AB, INTP)
RADM = '( ( %s /\\ 0 < R ) /\\ ( M e. RR /\\ %s ) )' % (RBDP, ALF)
HRM = '( ( %s /\\ %s ) /\\ %s )' % (HOL, RECT, RADM)


def CFM(E, M):
    return '( y e. %s |-> ( ( F ` y ) / ( ( y - P ) ^ %s ) ) )' % (E, M)


def RM(E, M):
    return '( y e. %s |-> ( ( ( F ` y ) x. ( %s ^ %s ) ) / ( y - Z ) ) )' % (E, XY, M)


GDEF = 'G = ( n e. NN0 |-> %s )' % RINT(RM(E2, 'n'), 'A', 'B')
HDEF = 'H = ( j e. NN0 |-> ( ( ( Z - P ) ^ j ) x. %s ) )' % RINT(CFM(PUP, '( j + 1 )'), 'A', 'B')
CDEF = 'C = ( j e. NN0 |-> %s )' % RINT(CFM(PUP, '( j + 1 )'), 'A', 'B')


def CF(K):
    """the coefficient integral of index K (the value of C at K)"""
    return RINT(CFM(PUP, '( %s + 1 )' % K), 'A', 'B')


def HT(K):
    return '( ( ( Z - P ) ^ %s ) x. %s )' % (K, CF(K))


def gval(w, ante, K, kn, hG):
    """( ante -> ( G ` K ) = RM(K) rectint ) from kn: ( ante -> K e. NN0 ) and the $e step hG"""
    s1 = w.s([], 'oveq2', '( n = %s -> ( %s ^ n ) = ( %s ^ %s ) )' % (K, XY, XY, K))
    s2 = w.s([s1], 'oveq2d', '( n = %s -> ( ( F ` y ) x. ( %s ^ n ) ) = ( ( F ` y ) x. ( %s ^ %s ) ) )' % (K, XY, XY, K))
    s3 = w.s([s2], 'oveq1d', '( n = %s -> ( ( ( F ` y ) x. ( %s ^ n ) ) / ( y - Z ) ) = ( ( ( F ` y ) x. ( %s ^ %s ) ) / ( y - Z ) ) )' % (K, XY, XY, K))
    s4 = w.s([s3], 'mpteq2dv', '( n = %s -> %s = %s )' % (K, RM(E2, 'n'), RM(E2, K)))
    s5 = w.s([s4], 'oveq1d', '( n = %s -> %s = %s )' % (K, RINT(RM(E2, 'n'), 'A', 'B'), RINT(RM(E2, K), 'A', 'B')))
    fm = w.s([s5, hG], 'fvmptg', '( ( %s e. NN0 /\\ %s e. _V ) -> ( G ` %s ) = %s )' % (K, RINT(RM(E2, K), 'A', 'B'), K, RINT(RM(E2, K), 'A', 'B')))
    return w.s([kn, ovexd(w, ante, RINT(RM(E2, K), 'A', 'B')), fm], 'syl2anc', '( %s -> ( G ` %s ) = %s )' % (ante, K, RINT(RM(E2, K), 'A', 'B')))


def cfsub(w, K):
    """( j = K -> CF(j) = CF(K) )"""
    s2 = w.s([], 'oveq1', '( j = %s -> ( j + 1 ) = ( %s + 1 ) )' % (K, K))
    s3 = w.s([s2], 'oveq2d', '( j = %s -> ( ( y - P ) ^ ( j + 1 ) ) = ( ( y - P ) ^ ( %s + 1 ) ) )' % (K, K))
    s4 = w.s([s3], 'oveq2d', '( j = %s -> ( ( F ` y ) / ( ( y - P ) ^ ( j + 1 ) ) ) = ( ( F ` y ) / ( ( y - P ) ^ ( %s + 1 ) ) ) )' % (K, K))
    s5 = w.s([s4], 'mpteq2dv', '( j = %s -> %s = %s )' % (K, CFM(PUP, '( j + 1 )'), CFM(PUP, '( %s + 1 )' % K)))
    return w.s([s5], 'oveq1d', '( j = %s -> %s = %s )' % (K, CF('j'), CF(K)))


def cval(w, ante, K, kn, hC):
    """( ante -> ( C ` K ) = CF(K) )"""
    s6 = cfsub(w, K)
    fm = w.s([s6, hC], 'fvmptg', '( ( %s e. NN0 /\\ %s e. _V ) -> ( C ` %s ) = %s )' % (K, CF(K), K, CF(K)))
    return w.s([kn, ovexd(w, ante, CF(K)), fm], 'syl2anc', '( %s -> ( C ` %s ) = %s )' % (ante, K, CF(K)))


def hval(w, ante, K, kn, hH):
    """( ante -> ( H ` K ) = HT(K) )"""
    s1 = w.s([], 'oveq2', '( j = %s -> ( ( Z - P ) ^ j ) = ( ( Z - P ) ^ %s ) )' % (K, K))
    s6 = cfsub(w, K)
    s7 = w.s([s1, s6], 'oveq12d', '( j = %s -> ( ( ( Z - P ) ^ j ) x. %s ) = %s )' % (K, CF('j'), HT(K)))
    fm = w.s([s7, hH], 'fvmptg', '( ( %s e. NN0 /\\ %s e. _V ) -> ( H ` %s ) = %s )' % (K, HT(K), K, HT(K)))
    return w.s([kn, ovexd(w, ante, HT(K)), fm], 'syl2anc', '( %s -> ( H ` %s ) = %s )' % (ante, K, HT(K)))


def ad(w, st, ante, form):
    """( ante -> form ) by adantr from st: ( ante' -> form ), ante = ( ante' /\\ ... )"""
    return w.s([st], 'adantr', '( %s -> %s )' % (ante, form))


def basectx(w, A0, bs):
    """the standard closures under A0 from a step bs: ( A0 -> BASE )"""
    d = {}
    d['ab'] = ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    d['tri'] = tri = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (A0, INTP, INTZ))
    d['holo'] = holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
    d['it'] = it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
    d['itz'] = itz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTZ))
    d['pnz'] = w.s([tri, w.inst('simp3')], 'syl', '( %s -> P =/= Z )' % A0)
    d['ac'] = ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    d['bc'] = bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    d['pc'] = pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    d['zc'] = zc = w.s([itz, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
    d['fcn'] = fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    d['hss'] = hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
    d['ff'] = ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    d['dss'] = dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    d['crd'] = w.s([hss, w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
    d['crss'] = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    d['zp'] = w.s([zc, pc], 'subcld', '( %s -> ( Z - P ) e. CC )' % A0)
    d['zpne'] = w.s([zc, pc, w.s([d['pnz']], 'necomd', '( %s -> Z =/= P )' % A0)], 'subne0d', '( %s -> ( Z - P ) =/= 0 )' % A0)
    d['abih'] = w.s([ab, it, holo], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, HOLO))
    return d


def tpisteps(w, A0):
    """steps ( A0 -> TPI e. CC ), ( A0 -> TPI =/= 0 )"""
    t2c = closed(w, A0, '2cn', '2 e. CC')
    icn = closed(w, A0, 'ax-icn', '_i e. CC')
    picn_ = closed(w, A0, 'picn', '_pi e. CC')
    pine = w.s([closed(w, A0, 'pipos', '0 < _pi')], 'gt0ne0d', '( %s -> _pi =/= 0 )' % A0)
    ipin = w.s([icn, picn_, closed(w, A0, 'ine0', '_i =/= 0'), pine], 'mulne0d', '( %s -> ( _i x. _pi ) =/= 0 )' % A0)
    ipic = w.s([icn, picn_], 'mulcld', '( %s -> ( _i x. _pi ) e. CC )' % A0)
    tne = w.s([t2c, ipic, closed(w, A0, '2ne0', '2 =/= 0'), ipin], 'mulne0d', '( %s -> %s =/= 0 )' % (A0, TPI))
    tpic = w.s([t2c, ipic], 'mulcld', '( %s -> %s e. CC )' % (A0, TPI))
    return tpic, tne


def cfcl(w, ante, K, kn, abih):
    """( ante -> CF(K) e. CC ) from kn: K e. NN0 and abih: ( AB /\\ INTP /\\ HOLO )"""
    k1 = w.s([kn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ante, K))
    return w.s([w.s([abih, k1], 'jca', '( %s -> ( ( %s /\\ %s /\\ %s ) /\\ ( %s + 1 ) e. NN0 ) )' % (ante, AB, INTP, HOLO, K)), w.inst('rectintccl')], 'syl',
               '( %s -> %s e. CC )' % (ante, CF(K)))


def ccl(w, ante, K, kn, abih, hC):
    """( ante -> ( C ` K ) e. CC )"""
    return w.s([cval(w, ante, K, kn, hC), cfcl(w, ante, K, kn, abih)], 'eqeltrd', '( %s -> ( C ` %s ) e. CC )' % (ante, K))


def gcl(w, ante, K, kn, bs, hG):
    """( ante -> ( G ` K ) e. CC )"""
    v = gval(w, ante, K, kn, hG)
    r = w.s([w.s([bs, kn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (ante, BASE, K)), w.inst('rectintrcl')], 'syl',
            '( %s -> %s e. CC )' % (ante, RINT(RM(E2, K), 'A', 'B')))
    return w.s([v, r], 'eqeltrd', '( %s -> ( G ` %s ) e. CC )' % (ante, K))


# ---- section B: the quotient function ---------------------------------------
ZER = 'A. i e. ( 0 ..^ N ) ( C ` i ) = 0'
CTX = '( %s /\\ ( N e. NN /\\ %s ) )' % (HRM, ZER)
QP = '( ( C ` N ) / %s )' % TPI


def QB(X):
    return 'if ( %s = P , %s , ( ( F ` %s ) / ( ( %s - P ) ^ N ) ) )' % (X, QP, X, X)


QDEF = 'Q = ( z e. D |-> %s )' % QB('z')


def hrmctx(w, A0, hrm):
    """closures under A0 from a step hrm: ( A0 -> HRM )"""
    d = {}
    hr = w.s([hrm, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, HOL, RECT))
    d['hol'] = hol = w.s([hr, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    d['rect'] = rect = w.s([hr, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, RECT))
    d['radm'] = radm = w.s([hrm, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, RADM))
    d['ab'] = ab = w.s([rect, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    d['it'] = it = w.s([rect, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTP))
    d['rd'] = rd = w.s([rect, w.inst('simp3')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    d['holo'] = holo = w.s([hol, rd, w.inst('holcrect')], 'syl2anc', '( %s -> %s )' % (A0, HOLO))
    d['abih'] = w.s([ab, it, holo], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, HOLO))
    d['fcn'] = fcn = w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    d['dhol'] = w.s([hol, w.inst('simpr')], 'syl', '( %s -> D C_ dom ( CC _D F ) )' % A0)
    d['ff'] = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    d['dss'] = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    d['dopn'] = w.s([hol, w.inst('holopn')], 'syl', '( %s -> D e. %s )' % (A0, TOP))
    d['ac'] = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    d['bc'] = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    d['pc'] = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    d['pr'] = w.s([ab, it, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)
    d['pd'] = w.s([rd, d['pr']], 'sseldd', '( %s -> P e. D )' % A0)
    rb0 = w.s([radm, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
    d['rbd'] = rbd = w.s([rb0, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP))
    d['rpos'] = rpos = w.s([rb0, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
    d['rr'] = rr = w.s([rbd, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
    d['Rrp'] = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
    mm = w.s([radm, w.inst('simpr')], 'syl', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
    d['mr'] = w.s([mm, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
    d['alf'] = w.s([mm, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
    return d


def ctxq(w, A0=CTX):
    """closures under CTX"""
    hrm = w.s([], 'simpl', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    d['hrm'] = hrm
    nz = w.s([], 'simpr', '( %s -> ( N e. NN /\\ %s ) )' % (A0, ZER))
    d['nn'] = nn = w.s([nz, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    d['hn'] = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    d['zer'] = w.s([nz, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ZER))
    return d


def qpcl(w, A0, d, hC):
    """( A0 -> QP e. CC ) from ctx d under A0 (needs abih, hn) and the C step"""
    cn = ccl(w, A0, 'N', d['hn'], d['abih'], hC)
    tpic, tne = tpisteps(w, A0)
    return w.s([cn, tpic, tne], 'divcld', '( %s -> %s e. CC )' % (A0, QP)), cn, tpic, tne


# ---- the Taylor apparatus at the evaluation point V (Z := V) -----------------
def INTV(V):
    rv = RE(V); iv = IM(V)
    return '( %s e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (V, RA, rv, rv, RB, IA, iv, iv, IB)


def BASEV(V):
    return '( %s /\\ ( %s /\\ %s /\\ P =/= %s ) /\\ %s )' % (AB, INTP, INTV(V), V, HOLO)


def E2V(V):
    return '( ( A crect B ) \\ { P , %s } )' % V


def RMV(E, M, V):
    return '( y e. %s |-> ( ( ( F ` y ) x. ( ( ( %s - P ) / ( y - P ) ) ^ %s ) ) / ( y - %s ) ) )' % (E, V, M, V)


def GMAP(V):
    return '( n e. NN0 |-> %s )' % RINT(RMV(E2V(V), 'n', V), 'A', 'B')


def HMAP(V):
    return '( j e. NN0 |-> ( ( ( %s - P ) ^ j ) x. %s ) )' % (V, RINT(CFM(PUP, '( j + 1 )'), 'A', 'B'))


def famsteps(w, V):
    """the eqid steps discharging the G and H family hypotheses at Z := V"""
    return (w.s([], 'eqid', '%s = %s' % (GMAP(V), GMAP(V))), w.s([], 'eqid', '%s = %s' % (HMAP(V), HMAP(V))))


def geo_of_int(w, A0, d):
    """( A0 -> GEO ) from the closures d (ac, bc, pc, it)"""
    RP = RE('P'); IP = IM('P')
    ineq = w.s([d['it'], w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
    lt = [w.s([ineq, w.inst(r)], 'syl', '( %s -> %s )' % (A0, f)) for r, f in
          [('simpll', '%s < %s' % (RA, RP)), ('simplr', '%s < %s' % (RP, RB)), ('simprl', '%s < %s' % (IA, IP)), ('simprr', '%s < %s' % (IP, IB))]]
    ar = w.s([d['ac']], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([d['bc']], 'recld', '( %s -> %s e. RR )' % (A0, RB))
    ai = w.s([d['ac']], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([d['bc']], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    pr_ = w.s([d['pc']], 'recld', '( %s -> %s e. RR )' % (A0, RP)); pi_ = w.s([d['pc']], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
    geo = w.s([w.s([w.s([ar, pr_, br, lt[0], lt[1]], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB)),
               w.s([w.s([ai, pi_, bi, lt[2], lt[3]], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))],
              'jca', '( %s -> %s )' % (A0, GEO))
    return geo, (ar, br, ai, bi)


def kreal(w, A0, d, geo, reals):
    """( A0 -> K e. RR ), ( A0 -> 0 <_ K ) from mr, alf, Rrp, ac, bc, geo"""
    ar, br, ai, bi = reals
    perr = w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)), w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
    lr = w.s([geo, w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A0, RA, RB))
    li = w.s([geo, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A0, IA, IB))
    g1 = w.s([w.s([ar, br, w.inst('subge0')], 'syl2anc', '( %s -> ( 0 <_ ( %s - %s ) <-> %s <_ %s ) )' % (A0, RB, RA, RA, RB)), lr], 'mpbird', '( %s -> 0 <_ ( %s - %s ) )' % (A0, RB, RA))
    g2 = w.s([w.s([ai, bi, w.inst('subge0')], 'syl2anc', '( %s -> ( 0 <_ ( %s - %s ) <-> %s <_ %s ) )' % (A0, IB, IA, IA, IB)), li], 'mpbird', '( %s -> 0 <_ ( %s - %s ) )' % (A0, IB, IA))
    per0 = w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)), w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA)), g1, g2], 'addge0d', '( %s -> 0 <_ %s )' % (A0, PER))
    # M >= 0 from the frame bound at A
    afr = w.s([d['ab'], geo, w.inst('crectfra')], 'syl2anc', '( %s -> A e. %s )' % (A0, FR))
    sub = w.s([w.s([w.s([], 'fveq2', '( u = A -> ( F ` u ) = ( F ` A ) )')], 'fveq2d', '( u = A -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` A ) ) )')], 'breq1d',
              '( u = A -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` A ) ) <_ M ) )')
    fam = w.s([sub, d['alf'], afr], 'rspcdva', '( %s -> ( abs ` ( F ` A ) ) <_ M )' % A0)
    fru = w.s([d['ab'], geo, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( A crect B ) )' % (A0, FR))
    fa = w.s([d['ff'], w.s([d['rd'], w.s([fru, afr], 'sseldd', '( %s -> A e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> A e. D )' % A0)], 'ffvelcdmd',
             '( %s -> ( F ` A ) e. CC )' % A0)
    m0 = w.s([w.s([fa], 'abscld', '( %s -> ( abs ` ( F ` A ) ) e. RR )' % A0), d['mr'], w.s([fa], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` A ) ) )' % A0), fam], 'letrd', '( %s -> 0 <_ M )' % A0)
    hrp = w.s([d['Rrp']], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % A0)
    mq = w.s([d['mr'], hrp], 'rerpdivcld', '( %s -> ( M / ( R / 2 ) ) e. RR )' % A0)
    mq0 = w.s([d['mr'], hrp, m0], 'divge0d', '( %s -> 0 <_ ( M / ( R / 2 ) ) )' % A0)
    t2 = closed(w, A0, '2re', '2 e. RR')
    t20 = closed(w, A0, '0le2', '0 <_ 2')
    k1r = w.s([t2, mq], 'remulcld', '( %s -> ( 2 x. ( M / ( R / 2 ) ) ) e. RR )' % A0)
    k10 = w.s([t2, mq, t20, mq0], 'mulge0d', '( %s -> 0 <_ ( 2 x. ( M / ( R / 2 ) ) ) )' % A0)
    kr = w.s([k1r, perr], 'remulcld', '( %s -> %s e. RR )' % (A0, KK))
    k0 = w.s([k1r, perr, k10, per0], 'mulge0d', '( %s -> 0 <_ %s )' % (A0, KK))
    return kr, k0


def gvalv(w, ante, K, kn, hG, V):
    """( ante -> ( GMAP(V) ` K ) = RMV(K) rectint ) at the evaluation point V"""
    XYV = '( ( %s - P ) / ( y - P ) )' % V
    s1 = w.s([], 'oveq2', '( n = %s -> ( %s ^ n ) = ( %s ^ %s ) )' % (K, XYV, XYV, K))
    s2 = w.s([s1], 'oveq2d', '( n = %s -> ( ( F ` y ) x. ( %s ^ n ) ) = ( ( F ` y ) x. ( %s ^ %s ) ) )' % (K, XYV, XYV, K))
    s3 = w.s([s2], 'oveq1d', '( n = %s -> ( ( ( F ` y ) x. ( %s ^ n ) ) / ( y - %s ) ) = ( ( ( F ` y ) x. ( %s ^ %s ) ) / ( y - %s ) ) )' % (K, XYV, V, XYV, K, V))
    s4 = w.s([s3], 'mpteq2dv', '( n = %s -> %s = %s )' % (K, RMV(E2V(V), 'n', V), RMV(E2V(V), K, V)))
    RK = RINT(RMV(E2V(V), K, V), 'A', 'B')
    s5 = w.s([s4], 'oveq1d', '( n = %s -> %s = %s )' % (K, RINT(RMV(E2V(V), 'n', V), 'A', 'B'), RK))
    fm = w.s([s5, hG], 'fvmptg', '( ( %s e. NN0 /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (K, RK, GMAP(V), K, RK))
    return w.s([kn, ovexd(w, ante, RK), fm], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, GMAP(V), K, RK))


def gclv(w, ante, K, kn, basev, hG, V):
    """( ante -> ( GMAP(V) ` K ) e. CC )"""
    v = gvalv(w, ante, K, kn, hG, V)
    RK = RINT(RMV(E2V(V), K, V), 'A', 'B')
    r = w.s([w.s([basev, kn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (ante, BASEV(V), K)), w.inst('rectintrcl')], 'syl', '( %s -> %s e. CC )' % (ante, RK))
    return w.s([v, r], 'eqeltrd', '( %s -> ( %s ` %s ) e. CC )' % (ante, GMAP(V), K))
