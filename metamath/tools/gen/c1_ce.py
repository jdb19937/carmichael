"""Sortie C1 section 5.2: continuity of the Cauchy kernel and Cauchy's estimate
of order zero (the weak maximum modulus principle)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c1_lib import *

RP = RE('P'); IP = IM('P')
INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RP, RP, RB, IA, IP, IP, IB)
RBD = '( R e. RR /\\ ( ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) /\\ ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) ) )' % (
    RP, RA, RB, RP, IP, IA, IB, IP)
HOLO = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) )'
CP = '( CC \\ { P } )'
PU = '( ( A crect B ) \\ { P } )'
TPI = '( 2 x. ( _i x. _pi ) )'


def QF(E):
    return '( z e. %s |-> ( ( F ` z ) / ( z - P ) ) )' % E


# ---- qfcn ------------------------------------------------------------------
w = W('qfcn', 'The Cauchy kernel of a continuous function is continuous off the pole.')
A0 = '( F e. ( D -cn-> CC ) /\\ E C_ D /\\ ( P e. CC /\\ E C_ %s ) )' % CP
A1 = '( %s /\\ z e. E )' % A0
fcn = w.s([], 'simp1', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ed = w.s([], 'simp2', '( %s -> E C_ D )' % A0)
pp = w.s([], 'simp3', '( %s -> ( P e. CC /\\ E C_ %s ) )' % (A0, CP))
pc = w.s([pp, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ecp = w.s([pp, w.inst('simpr')], 'syl', '( %s -> E C_ %s )' % (A0, CP))
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
res = w.s([ed, fcn, w.inst('rescncf')], 'sylc', '( %s -> ( F |` E ) e. ( E -cn-> CC ) )' % A0)
req = w.s([ff, ed], 'feqresmpt', '( %s -> ( F |` E ) = ( z e. E |-> ( F ` z ) ) )' % A0)
fmp = w.s([req, res], 'eqeltrrd', '( %s -> ( z e. E |-> ( F ` z ) ) e. ( E -cn-> CC ) )' % A0)
rmp = w.s([pc, ecp, w.inst('rinvcnss')], 'syl2anc', '( %s -> ( z e. E |-> ( 1 / ( z - P ) ) ) e. ( E -cn-> CC ) )' % A0)
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
mcn = w.s([w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i',
          '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
prod = w.s([ej, mcn, fmp, rmp], 'cncfmpt2f', '( %s -> ( z e. E |-> ( ( F ` z ) x. ( 1 / ( z - P ) ) ) ) e. ( E -cn-> CC ) )' % A0)
zE = w.s([], 'simpr', '( %s -> z e. E )' % A1)
zd = w.s([w.s([ed], 'adantr', '( %s -> E C_ D )' % A1), zE], 'sseldd', '( %s -> z e. D )' % A1)
fz = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
zcp = w.s([w.s([ecp], 'adantr', '( %s -> E C_ %s )' % (A1, CP)), zE], 'sseldd', '( %s -> z e. %s )' % (A1, CP))
edf = w.s([zcp, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= P ) )' % A1)
zc = w.s([edf, w.inst('simpl')], 'syl', '( %s -> z e. CC )' % A1)
zn = w.s([edf, w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
sc = w.s([zc, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
sn = w.s([zc, pc1, zn], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
dr = w.s([fz, sc, sn], 'divrecd', '( %s -> ( ( F ` z ) / ( z - P ) ) = ( ( F ` z ) x. ( 1 / ( z - P ) ) ) )' % A1)
mt = w.s([dr], 'mpteq2dva', '( %s -> %s = ( z e. E |-> ( ( F ` z ) x. ( 1 / ( z - P ) ) ) ) )' % (A0, QF('E')))
w.qed([mt, prod], 'eqeltrd', '( %s -> %s e. ( E -cn-> CC ) )' % (A0, QF('E'))); run1(w)

# ---- rectintce0 ------------------------------------------------------------
w = W('rectintce0', 'Cauchy estimate of order zero: the value of a holomorphic '
      'function at a strictly interior point is bounded by the maximum of its '
      'absolute value on the boundary frame, times the half perimeter over pi R, '
      'where R is below each coordinate gap.  The weak maximum modulus principle.')
PER = '( ( %s - %s ) + ( %s - %s ) )' % (RB, RA, IB, IA)
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
AP = '( abs ` ( F ` P ) )'
A0 = '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ 0 < R ) /\\ ( M e. RR /\\ %s ) )' % (AB, INT, HOLO, RBD, ALF)
A1 = '( %s /\\ v e. %s )' % (A0, FR)
bs = w.s([], 'simp1', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INT, HOLO))
rb0 = w.s([], 'simp2', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBD))
mm = w.s([], 'simp3', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
rbd = w.s([rb0, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBD))
rpos = w.s([rb0, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
mr = w.s([mm, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
alf = w.s([mm, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
rr = w.s([rbd, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
Rrp = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
it = w.s([bs, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INT))
holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lr = w.s([ineq, w.inst('simpll')], 'syl', '( %s -> %s < %s )' % (A0, RA, RP))
rr_ = w.s([ineq, w.inst('simplr')], 'syl', '( %s -> %s < %s )' % (A0, RP, RB))
li = w.s([ineq, w.inst('simprl')], 'syl', '( %s -> %s < %s )' % (A0, IA, IP))
ri = w.s([ineq, w.inst('simprr')], 'syl', '( %s -> %s < %s )' % (A0, IP, IB))
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
pr = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP))
pi_ = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
ler = w.s([w.s([ar, pr, br, lr, rr_], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB))
lei = w.s([w.s([ai, pi_, bi, li, ri], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))
geo = w.s([ler, lei], 'jca', '( %s -> %s )' % (A0, GEO))
fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
cau = w.s([bs, w.inst('rectintcau')], 'syl', '( %s -> %s = ( %s x. ( F ` P ) ) )' % (A0, RINT(QF(PU), 'A', 'B'), TPI))
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ssc = closed(w, A0, 'ssid', 'CC C_ CC')
dvb = w.s([ssc, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
crd = w.s([hss, dvb], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
pud = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, PU))
crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
pcp = w.s([crss], 'ssdifd', '( %s -> %s C_ %s )' % (A0, PU, CP))
qcn = w.s([w.s([fcn, pud, w.s([pc, pcp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, PU, CP))], '3jca',
                '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D /\\ ( P e. CC /\\ %s C_ %s ) ) )' % (A0, PU, PU, CP)), w.inst('qfcn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, QF(PU), PU))
frp = w.s([w.s([ab, it], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INT)), w.inst('crectfrp')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, PU))
frfr = closed(w, A0, 'ssid', '%s C_ %s' % (FR, FR))
pse = w.s([ab, geo, w.s([qcn, frfr, frp], '3jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s ) )' % (A0, QF(PU), PU, FR, FR, FR, PU))],
          '3jca', '( %s -> ( %s /\\ %s /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s ) ) )' % (A0, AB, GEO, QF(PU), PU, FR, FR, FR, PU))
# the pointwise bound on the frame, in the fresh variable v
dis = w.s([w.s([ab, it, rbd], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INT, RBD)), w.inst('crectdis')], 'syl',
          '( %s -> A. u e. %s R <_ ( abs ` ( u - P ) ) )' % (A0, FR))
cb1 = w.s([], 'oveq1', '( u = v -> ( u - P ) = ( v - P ) )')
cb2 = w.s([cb1], 'fveq2d', '( u = v -> ( abs ` ( u - P ) ) = ( abs ` ( v - P ) ) )')
cb3 = w.s([cb2], 'breq2d', '( u = v -> ( R <_ ( abs ` ( u - P ) ) <-> R <_ ( abs ` ( v - P ) ) ) )')
disv = w.s([dis, w.s([cb3], 'cbvralvw', '( A. u e. %s R <_ ( abs ` ( u - P ) ) <-> A. v e. %s R <_ ( abs ` ( v - P ) ) )' % (FR, FR))],
           'sylib', '( %s -> A. v e. %s R <_ ( abs ` ( v - P ) ) )' % (A0, FR))
cc1 = w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')
cc2 = w.s([cc1], 'fveq2d', '( u = v -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` v ) ) )')
cc3 = w.s([cc2], 'breq1d', '( u = v -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` v ) ) <_ M ) )')
alfv = w.s([alf, w.s([cc3], 'cbvralvw', '( %s <-> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (ALF, FR))],
           'sylib', '( %s -> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (A0, FR))
vm = w.s([], 'simpr', '( %s -> v e. %s )' % (A1, FR))
rle = w.s([w.s([disv], 'adantr', '( %s -> A. v e. %s R <_ ( abs ` ( v - P ) ) )' % (A1, FR)), vm, w.inst('rspa')], 'syl2anc',
          '( %s -> R <_ ( abs ` ( v - P ) ) )' % A1)
fle = w.s([w.s([alfv], 'adantr', '( %s -> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (A1, FR)), vm, w.inst('rspa')], 'syl2anc',
          '( %s -> ( abs ` ( F ` v ) ) <_ M )' % A1)
vpu = w.s([w.s([frp], 'adantr', '( %s -> %s C_ %s )' % (A1, FR, PU)), vm], 'sseldd', '( %s -> v e. %s )' % (A1, PU))
vcp = w.s([w.s([pcp], 'adantr', '( %s -> %s C_ %s )' % (A1, PU, CP)), vpu], 'sseldd', '( %s -> v e. %s )' % (A1, CP))
vdf = w.s([vcp, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. CC /\\ v =/= P ) )' % A1)
vc = w.s([vdf, w.inst('simpl')], 'syl', '( %s -> v e. CC )' % A1)
vn = w.s([vdf, w.inst('simpr')], 'syl', '( %s -> v =/= P )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
vsc = w.s([vc, pc1], 'subcld', '( %s -> ( v - P ) e. CC )' % A1)
vsn = w.s([vc, pc1, vn], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % A1)
vd = w.s([w.s([pud], 'adantr', '( %s -> %s C_ D )' % (A1, PU)), vpu], 'sseldd', '( %s -> v e. D )' % A1)
fv_ = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), vd], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A1)
sb1 = w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )')
sb2 = w.s([], 'oveq1', '( z = v -> ( z - P ) = ( v - P ) )')
sb3 = w.s([sb1, sb2], 'oveq12d', '( z = v -> ( ( F ` z ) / ( z - P ) ) = ( ( F ` v ) / ( v - P ) ) )')
eqm = w.s([], 'eqid', '%s = %s' % (QF(PU), QF(PU)))
fvm = w.s([sb3, eqm], 'fvmptg', '( ( v e. %s /\\ ( ( F ` v ) / ( v - P ) ) e. _V ) -> ( %s ` v ) = ( ( F ` v ) / ( v - P ) ) )' % (PU, QF(PU)))
qval = w.s([vpu, ovexd(w, A1, '( ( F ` v ) / ( v - P ) )'), fvm], 'syl2anc', '( %s -> ( %s ` v ) = ( ( F ` v ) / ( v - P ) ) )' % (A1, QF(PU)))
absq = w.s([fv_, vsc, vsn], 'absdivd', '( %s -> ( abs ` ( ( F ` v ) / ( v - P ) ) ) = ( ( abs ` ( F ` v ) ) / ( abs ` ( v - P ) ) ) )' % A1)
afv = w.s([fv_], 'abscld', '( %s -> ( abs ` ( F ` v ) ) e. RR )' % A1)
avp = w.s([vsc], 'abscld', '( %s -> ( abs ` ( v - P ) ) e. RR )' % A1)
afv0 = w.s([fv_], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A1)
ld = w.s([afv, w.s([mr], 'adantr', '( %s -> M e. RR )' % A1), w.s([Rrp], 'adantr', '( %s -> R e. RR+ )' % A1), avp, afv0, fle, rle],
         'lediv12ad', '( %s -> ( ( abs ` ( F ` v ) ) / ( abs ` ( v - P ) ) ) <_ ( M / R ) )' % A1)
pw = w.s([w.s([w.s([qval], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` ( ( F ` v ) / ( v - P ) ) ) )' % (A1, QF(PU))), absq], 'eqtrd',
              '( %s -> ( abs ` ( %s ` v ) ) = ( ( abs ` ( F ` v ) ) / ( abs ` ( v - P ) ) ) )' % (A1, QF(PU))), ld], 'eqbrtrd',
         '( %s -> ( abs ` ( %s ` v ) ) <_ ( M / R ) )' % (A1, QF(PU)))
allv = w.s([pw], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ ( M / R ) )' % (A0, FR, QF(PU)))
mrp = w.s([mr, Rrp], 'rerpdivcld', '( %s -> ( M / R ) e. RR )' % A0)
abse = w.s([pse, mrp, allv, w.inst('rectintabse')], 'syl3anc',
           '( %s -> ( abs ` %s ) <_ ( ( 2 x. ( M / R ) ) x. %s ) )' % (A0, RINT(QF(PU), 'A', 'B'), PER))
# the value F ` P
prI = w.s([pr, w.s([ar, pr, lr], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RP)), w.s([pr, br, rr_], 'ltled', '( %s -> %s <_ %s )' % (A0, RP, RB)),
           w.s([ar, br, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, RP, RA, RB, RP, RA, RP, RP, RB))],
          'mpbir3and', '( %s -> %s e. ( %s [,] %s ) )' % (A0, RP, RA, RB))
piI = w.s([pi_, w.s([ai, pi_, li], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IP)), w.s([pi_, bi, ri], 'ltled', '( %s -> %s <_ %s )' % (A0, IP, IB)),
           w.s([ai, bi, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, IP, IA, IB, IP, IA, IP, IP, IB))],
          'mpbir3and', '( %s -> %s e. ( %s [,] %s ) )' % (A0, IP, IA, IB))
pmem = w.s([pc, prI, piI, w.s([ab, w.inst('elcrect')], 'syl',
                              '( %s -> ( P e. ( A crect B ) <-> ( P e. CC /\\ %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) ) ) )' % (A0, RP, RA, RB, IP, IA, IB))],
            'mpbir3and', '( %s -> P e. ( A crect B ) )' % A0)
pd = w.s([crd, pmem], 'sseldd', '( %s -> P e. D )' % A0)
fp = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
# ( abs ` TPI ) = ( 2 x. _pi )
t2c = closed(w, A0, '2cn', '2 e. CC')
t2r = closed(w, A0, '2re', '2 e. RR')
t2ge = closed(w, A0, '0le2', '0 <_ 2')
icn = closed(w, A0, 'ax-icn', '_i e. CC')
picn_ = closed(w, A0, 'picn', '_pi e. CC')
pirr = closed(w, A0, 'pire', '_pi e. RR')
pipos_ = closed(w, A0, 'pipos', '0 < _pi')
pige = w.s([closed(w, A0, '0re', '0 e. RR'), pirr, pipos_], 'ltled', '( %s -> 0 <_ _pi )' % A0)
ipic = w.s([icn, picn_], 'mulcld', '( %s -> ( _i x. _pi ) e. CC )' % A0)
tpic = w.s([t2c, ipic], 'mulcld', '( %s -> %s e. CC )' % (A0, TPI))
a1 = w.s([t2c, ipic], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) )' % (A0, TPI))
a2 = w.s([icn, picn_], 'absmuld', '( %s -> ( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) ) )' % A0)
a3 = w.s([t2r, t2ge], 'absidd', '( %s -> ( abs ` 2 ) = 2 )' % A0)
a4 = closed(w, A0, 'absi', '( abs ` _i ) = 1')
a5 = w.s([pirr, pige], 'absidd', '( %s -> ( abs ` _pi ) = _pi )' % A0)
a6 = w.s([a2, w.s([w.s([a4, a5], 'oveq12d', '( %s -> ( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi ) )' % A0), w.s([picn_], 'mullidd', '( %s -> ( 1 x. _pi ) = _pi )' % A0)], 'eqtrd', '( %s -> ( ( abs ` _i ) x. ( abs ` _pi ) ) = _pi )' % A0)], 'eqtrd', '( %s -> ( abs ` ( _i x. _pi ) ) = _pi )' % A0)
abstpi = w.s([a1, w.s([a3, a6], 'oveq12d', '( %s -> ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = ( 2 x. _pi ) )' % A0)], 'eqtrd', '( %s -> ( abs ` %s ) = ( 2 x. _pi ) )' % (A0, TPI))
absm = w.s([tpic, fp], 'absmuld', '( %s -> ( abs ` ( %s x. ( F ` P ) ) ) = ( ( abs ` %s ) x. %s ) )' % (A0, TPI, TPI, AP))
lhs = w.s([w.s([w.s([cau], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( %s x. ( F ` P ) ) ) )' % (A0, RINT(QF(PU), 'A', 'B'), TPI)), absm], 'eqtrd',
                '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. %s ) )' % (A0, RINT(QF(PU), 'A', 'B'), TPI, AP)),
               w.s([abstpi], 'oveq1d', '( %s -> ( ( abs ` %s ) x. %s ) = ( ( 2 x. _pi ) x. %s ) )' % (A0, TPI, AP, AP))], 'eqtrd',
             '( %s -> ( abs ` %s ) = ( ( 2 x. _pi ) x. %s ) )' % (A0, RINT(QF(PU), 'A', 'B'), AP))
s1 = w.s([lhs, abse], 'eqbrtrrd', '( %s -> ( ( 2 x. _pi ) x. %s ) <_ ( ( 2 x. ( M / R ) ) x. %s ) )' % (A0, AP, PER))
# the final rearrangement
apr = w.s([fp], 'abscld', '( %s -> %s e. RR )' % (A0, AP))
apc = w.s([apr], 'recnd', '( %s -> %s e. CC )' % (A0, AP))
perr = w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)), w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))],
           'readdcld', '( %s -> %s e. RR )' % (A0, PER))
perc = w.s([perr], 'recnd', '( %s -> %s e. CC )' % (A0, PER))
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
rc = w.s([rr], 'recnd', '( %s -> R e. CC )' % A0)
rne = w.s([Rrp], 'rpne0d', '( %s -> R =/= 0 )' % A0)
L1 = '( ( 2 x. _pi ) x. %s )' % AP
R1 = '( ( 2 x. ( M / R ) ) x. %s )' % PER
L1r = w.s([w.s([t2r, pirr], 'remulcld', '( %s -> ( 2 x. _pi ) e. RR )' % A0), apr], 'remulcld', '( %s -> %s e. RR )' % (A0, L1))
R1r = w.s([w.s([t2r, mrp], 'remulcld', '( %s -> ( 2 x. ( M / R ) ) e. RR )' % A0), perr], 'remulcld', '( %s -> %s e. RR )' % (A0, R1))
s2 = w.s([s1, w.s([L1r, R1r, Rrp], 'lemul2d', '( %s -> ( %s <_ %s <-> ( R x. %s ) <_ ( R x. %s ) ) )' % (A0, L1, R1, L1, R1))],
         'mpbid', '( %s -> ( R x. %s ) <_ ( R x. %s ) )' % (A0, L1, R1))
piap = '( _pi x. %s )' % AP
piapc = w.s([picn_, apc], 'mulcld', '( %s -> %s e. CC )' % (A0, piap))
e1a = w.s([w.s([t2c, picn_, apc], 'mulassd', '( %s -> %s = ( 2 x. %s ) )' % (A0, L1, piap))], 'oveq2d', '( %s -> ( R x. %s ) = ( R x. ( 2 x. %s ) ) )' % (A0, L1, piap))
e1b = w.s([rc, t2c, piapc], 'mul12d', '( %s -> ( R x. ( 2 x. %s ) ) = ( 2 x. ( R x. %s ) ) )' % (A0, piap, piap))
e1c = w.s([w.s([w.s([rc, picn_, apc], 'mulassd', '( %s -> ( ( R x. _pi ) x. %s ) = ( R x. %s ) )' % (A0, AP, piap))], 'eqcomd',
                '( %s -> ( R x. %s ) = ( ( R x. _pi ) x. %s ) )' % (A0, piap, AP)),
           w.s([w.s([rc, picn_], 'mulcomd', '( %s -> ( R x. _pi ) = ( _pi x. R ) )' % A0)], 'oveq1d', '( %s -> ( ( R x. _pi ) x. %s ) = ( ( _pi x. R ) x. %s ) )' % (A0, AP, AP))],
          'eqtrd', '( %s -> ( R x. %s ) = ( ( _pi x. R ) x. %s ) )' % (A0, piap, AP))
e1 = w.s([w.s([e1a, e1b], 'eqtrd', '( %s -> ( R x. %s ) = ( 2 x. ( R x. %s ) ) )' % (A0, L1, piap)),
          w.s([e1c], 'oveq2d', '( %s -> ( 2 x. ( R x. %s ) ) = ( 2 x. ( ( _pi x. R ) x. %s ) ) )' % (A0, piap, AP))], 'eqtrd',
         '( %s -> ( R x. %s ) = ( 2 x. ( ( _pi x. R ) x. %s ) ) )' % (A0, L1, AP))
t2m = w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0)
t2mp = w.s([t2m, perc], 'mulcld', '( %s -> ( ( 2 x. M ) x. %s ) e. CC )' % (A0, PER))
e2a = w.s([w.s([w.s([t2c, mc, rc, rne], 'divassd', '( %s -> ( ( 2 x. M ) / R ) = ( 2 x. ( M / R ) ) )' % A0)], 'eqcomd',
                '( %s -> ( 2 x. ( M / R ) ) = ( ( 2 x. M ) / R ) )' % A0)], 'oveq1d',
           '( %s -> %s = ( ( ( 2 x. M ) / R ) x. %s ) )' % (A0, R1, PER))
e2b = w.s([w.s([t2m, perc, rc, rne], 'div23d', '( %s -> ( ( ( 2 x. M ) x. %s ) / R ) = ( ( ( 2 x. M ) / R ) x. %s ) )' % (A0, PER, PER))], 'eqcomd',
          '( %s -> ( ( ( 2 x. M ) / R ) x. %s ) = ( ( ( 2 x. M ) x. %s ) / R ) )' % (A0, PER, PER))
e2c = w.s([w.s([e2a, e2b], 'eqtrd', '( %s -> %s = ( ( ( 2 x. M ) x. %s ) / R ) )' % (A0, R1, PER))], 'oveq2d',
          '( %s -> ( R x. %s ) = ( R x. ( ( ( 2 x. M ) x. %s ) / R ) ) )' % (A0, R1, PER))
e2 = w.s([w.s([e2c, w.s([t2mp, rc, rne], 'divcan2d', '( %s -> ( R x. ( ( ( 2 x. M ) x. %s ) / R ) ) = ( ( 2 x. M ) x. %s ) )' % (A0, PER, PER))], 'eqtrd',
               '( %s -> ( R x. %s ) = ( ( 2 x. M ) x. %s ) )' % (A0, R1, PER)),
          w.s([t2c, mc, perc], 'mulassd', '( %s -> ( ( 2 x. M ) x. %s ) = ( 2 x. ( M x. %s ) ) )' % (A0, PER, PER))], 'eqtrd',
         '( %s -> ( R x. %s ) = ( 2 x. ( M x. %s ) ) )' % (A0, R1, PER))
s3 = w.s([s2, e1, e2], '3brtr3d', '( %s -> ( 2 x. ( ( _pi x. R ) x. %s ) ) <_ ( 2 x. ( M x. %s ) ) )' % (A0, AP, PER))
t2rp = w.s([t2r, w.s([], '2pos', '0 < 2')], 'elrpd', '( %s -> 2 e. RR+ )' % A0) if False else w.s([t2r, w.s([w.s([], '2pos', '0 < 2')], 'a1i', '( %s -> 0 < 2 )' % A0)], 'elrpd', '( %s -> 2 e. RR+ )' % A0)
GL = '( ( _pi x. R ) x. %s )' % AP
GR = '( M x. %s )' % PER
GLr = w.s([w.s([pirr, rr], 'remulcld', '( %s -> ( _pi x. R ) e. RR )' % A0), apr], 'remulcld', '( %s -> %s e. RR )' % (A0, GL))
GRr = w.s([mr, perr], 'remulcld', '( %s -> %s e. RR )' % (A0, GR))
w.qed([s3, w.s([GLr, GRr, t2rp], 'lemul2d', '( %s -> ( %s <_ %s <-> ( 2 x. %s ) <_ ( 2 x. %s ) ) )' % (A0, GL, GR, GL, GR))],
      'mpbird', '( %s -> %s <_ %s )' % (A0, GL, GR)); run1(w)
