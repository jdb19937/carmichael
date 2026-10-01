"""Sortie C2 section 3.2: the strong maximum modulus principle."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c2_lib import *

# ---- expdomle --------------------------------------------------------------
w = W('expdomle', 'If every positive integer power of a nonnegative real is below a fixed multiple of the corresponding power of a second nonnegative real, the first is below the second.')
ALL = 'A. n e. NN ( A ^ n ) <_ ( K x. ( M ^ n ) )'
A0 = '( ( A e. RR /\\ 0 <_ A ) /\\ ( M e. RR /\\ 0 <_ M ) /\\ ( ( K e. RR /\\ 0 < K ) /\\ %s ) )' % ALL
P2 = '( %s /\\ M < A )' % A0
P3 = '( %s /\\ 0 < M )' % P2
P4 = '( %s /\\ -. 0 < M )' % P2
P5 = '( %s /\\ k e. NN )' % P3
P6 = '( %s /\\ K < ( ( A / M ) ^ k ) )' % P5
aa = w.s([], 'simp1', '( %s -> ( A e. RR /\\ 0 <_ A ) )' % A0)
mm = w.s([], 'simp2', '( %s -> ( M e. RR /\\ 0 <_ M ) )' % A0)
ka = w.s([], 'simp3', '( %s -> ( ( K e. RR /\\ 0 < K ) /\\ %s ) )' % (A0, ALL))
kk = w.s([ka, w.inst('simpl')], 'syl', '( %s -> ( K e. RR /\\ 0 < K ) )' % A0)
al = w.s([ka, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALL))
ar = w.s([aa, w.inst('simpl')], 'syl', '( %s -> A e. RR )' % A0)
mr = w.s([mm, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
kr = w.s([kk, w.inst('simpl')], 'syl', '( %s -> K e. RR )' % A0)
kp = w.s([kk, w.inst('simpr')], 'syl', '( %s -> 0 < K )' % A0)
m0 = w.s([mm, w.inst('simpr')], 'syl', '( %s -> 0 <_ M )' % A0)

# ---- case 0 < M
ar3 = w.s([w.s([ar], 'adantr', '( %s -> A e. RR )' % P2)], 'adantr', '( %s -> A e. RR )' % P3)
mr3 = w.s([w.s([mr], 'adantr', '( %s -> M e. RR )' % P2)], 'adantr', '( %s -> M e. RR )' % P3)
kr3 = w.s([w.s([kr], 'adantr', '( %s -> K e. RR )' % P2)], 'adantr', '( %s -> K e. RR )' % P3)
al3 = w.s([w.s([al], 'adantr', '( %s -> %s )' % (P2, ALL))], 'adantr', '( %s -> %s )' % (P3, ALL))
mlt3 = w.s([w.s([], 'simpr', '( %s -> M < A )' % P2)], 'adantr', '( %s -> M < A )' % P3)
mp3 = w.s([], 'simpr', '( %s -> 0 < M )' % P3)
mrp = w.s([mr3, mp3], 'elrpd', '( %s -> M e. RR+ )' % P3)
d1 = w.s([mlt3, w.s([mr3, ar3, mrp], 'ltdiv1d', '( %s -> ( M < A <-> ( M / M ) < ( A / M ) ) )' % P3)], 'mpbid',
         '( %s -> ( M / M ) < ( A / M ) )' % P3)
did = w.s([w.s([mr3], 'recnd', '( %s -> M e. CC )' % P3), w.s([mrp], 'rpne0d', '( %s -> M =/= 0 )' % P3), w.inst('divid')],
          'syl2anc', '( %s -> ( M / M ) = 1 )' % P3)
one = w.s([w.s([did], 'eqcomd', '( %s -> 1 = ( M / M ) )' % P3), d1], 'eqbrtrd', '( %s -> 1 < ( A / M ) )' % P3)
amr = w.s([ar3, mrp], 'rerpdivcld', '( %s -> ( A / M ) e. RR )' % P3)
exb = w.s([kr3, amr, one, w.inst('expnbnd')], 'syl3anc', '( %s -> E. k e. NN K < ( ( A / M ) ^ k ) )' % P3)
# inside the existential
knn = w.s([w.s([], 'simpr', '( %s -> k e. NN )' % P5)], 'adantr', '( %s -> k e. NN )' % P6)
kn0 = w.s([knn, w.inst('nnnn0')], 'syl', '( %s -> k e. NN0 )' % P6)
kz = w.s([knn, w.inst('nnzd')], 'syl', '( %s -> k e. ZZ )' % P6) if False else w.s([knn], 'nnzd', '( %s -> k e. ZZ )' % P6)
ar6 = w.s([w.s([ar3], 'adantr', '( %s -> A e. RR )' % P5)], 'adantr', '( %s -> A e. RR )' % P6)
mr6 = w.s([w.s([mr3], 'adantr', '( %s -> M e. RR )' % P5)], 'adantr', '( %s -> M e. RR )' % P6)
kr6 = w.s([w.s([kr3], 'adantr', '( %s -> K e. RR )' % P5)], 'adantr', '( %s -> K e. RR )' % P6)
mrp6 = w.s([w.s([mrp], 'adantr', '( %s -> M e. RR+ )' % P5)], 'adantr', '( %s -> M e. RR+ )' % P6)
al6 = w.s([w.s([al3], 'adantr', '( %s -> %s )' % (P5, ALL))], 'adantr', '( %s -> %s )' % (P6, ALL))
hyp = w.s([], 'simpr', '( %s -> K < ( ( A / M ) ^ k ) )' % P6)
sub = w.s([w.s([], 'oveq2', '( n = k -> ( A ^ n ) = ( A ^ k ) )'),
           w.s([w.s([], 'oveq2', '( n = k -> ( M ^ n ) = ( M ^ k ) )')], 'oveq2d', '( n = k -> ( K x. ( M ^ n ) ) = ( K x. ( M ^ k ) ) )')],
          'breq12d', '( n = k -> ( ( A ^ n ) <_ ( K x. ( M ^ n ) ) <-> ( A ^ k ) <_ ( K x. ( M ^ k ) ) ) )')
inst = w.s([sub, al6, knn], 'rspcdva', '( %s -> ( A ^ k ) <_ ( K x. ( M ^ k ) ) )' % P6)
mkrp = w.s([mrp6, kz], 'rpexpcld', '( %s -> ( M ^ k ) e. RR+ )' % P6)
mkr = w.s([mkrp], 'rpred', '( %s -> ( M ^ k ) e. RR )' % P6)
akr = w.s([ar6, kn0], 'reexpcld', '( %s -> ( A ^ k ) e. RR )' % P6)
cm = w.s([inst, w.s([w.s([w.s([kr6], 'recnd', '( %s -> K e. CC )' % P6), w.s([mkr], 'recnd', '( %s -> ( M ^ k ) e. CC )' % P6)],
                        'mulcomd', '( %s -> ( K x. ( M ^ k ) ) = ( ( M ^ k ) x. K ) )' % P6)], 'breq2d',
                    '( %s -> ( ( A ^ k ) <_ ( K x. ( M ^ k ) ) <-> ( A ^ k ) <_ ( ( M ^ k ) x. K ) ) )' % P6)],
          'mpbid', '( %s -> ( A ^ k ) <_ ( ( M ^ k ) x. K ) )' % P6)
ldm = w.s([cm, w.s([akr, kr6, w.s([mkr, w.s([mkrp], 'rpgt0d', '( %s -> 0 < ( M ^ k ) )' % P6)], 'jca',
                                  '( %s -> ( ( M ^ k ) e. RR /\\ 0 < ( M ^ k ) ) )' % P6), w.inst('ledivmul')], 'syl3anc',
                   '( %s -> ( ( ( A ^ k ) / ( M ^ k ) ) <_ K <-> ( A ^ k ) <_ ( ( M ^ k ) x. K ) ) )' % P6)],
          'mpbird', '( %s -> ( ( A ^ k ) / ( M ^ k ) ) <_ K )' % P6)
edv = w.s([w.s([ar6], 'recnd', '( %s -> A e. CC )' % P6),
           w.s([w.s([mr6], 'recnd', '( %s -> M e. CC )' % P6), w.s([mrp6], 'rpne0d', '( %s -> M =/= 0 )' % P6)], 'jca',
               '( %s -> ( M e. CC /\\ M =/= 0 ) )' % P6), kn0, w.inst('expdiv')], 'syl3anc',
          '( %s -> ( ( A / M ) ^ k ) = ( ( A ^ k ) / ( M ^ k ) ) )' % P6)
hyp2 = w.s([hyp, edv], 'breqtrd', '( %s -> K < ( ( A ^ k ) / ( M ^ k ) ) )' % P6)
akm = w.s([akr, mkrp], 'rerpdivcld', '( %s -> ( ( A ^ k ) / ( M ^ k ) ) e. RR )' % P6)
kk6 = w.s([kr6, akm, kr6, hyp2, ldm], 'ltletrd', '( %s -> K < K )' % P6)
nkk = w.s([kr6, w.inst('ltnr')], 'syl', '( %s -> -. K < K )' % P6)
res6 = w.s([kk6, w.s([nkk], 'pm2.21d', '( %s -> ( K < K -> A <_ M ) )' % P6)], 'mpd', '( %s -> A <_ M )' % P6)
res5 = w.s([res6], 'ex', '( %s -> ( K < ( ( A / M ) ^ k ) -> A <_ M ) )' % P5)
case1 = w.s([w.s([res5], 'rexlimdva', '( %s -> ( E. k e. NN K < ( ( A / M ) ^ k ) -> A <_ M ) )' % P3), exb], 'mpd', '( %s -> A <_ M )' % P3)

# ---- case -. 0 < M : then M = 0 and A <_ ( K x. M ) = 0
mr4 = w.s([w.s([mr], 'adantr', '( %s -> M e. RR )' % P2)], 'adantr', '( %s -> M e. RR )' % P4)
ar4 = w.s([w.s([ar], 'adantr', '( %s -> A e. RR )' % P2)], 'adantr', '( %s -> A e. RR )' % P4)
kr4 = w.s([w.s([kr], 'adantr', '( %s -> K e. RR )' % P2)], 'adantr', '( %s -> K e. RR )' % P4)
m04 = w.s([w.s([m0], 'adantr', '( %s -> 0 <_ M )' % P2)], 'adantr', '( %s -> 0 <_ M )' % P4)
al4 = w.s([w.s([al], 'adantr', '( %s -> %s )' % (P2, ALL))], 'adantr', '( %s -> %s )' % (P4, ALL))
nmp = w.s([], 'simpr', '( %s -> -. 0 < M )' % P4)
mle0 = w.s([nmp, w.s([w.s([], '0red', '( %s -> 0 e. RR )' % P4), mr4], 'ltnled',
                     '( %s -> ( 0 < M <-> -. M <_ 0 ) )' % P4)], 'mtbid', '( %s -> -. -. M <_ 0 )' % P4)
mle = w.s([mle0], 'notnotrd', '( %s -> M <_ 0 )' % P4)
z0r = w.s([], '0red', '( %s -> 0 e. RR )' % P4)
meq = w.s([w.s([m04, mle], 'jca', '( %s -> ( 0 <_ M /\\ M <_ 0 ) )' % P4), w.s([z0r, mr4], 'letri3d', '( %s -> ( 0 = M <-> ( 0 <_ M /\\ M <_ 0 ) ) )' % P4)], 'mpbird', '( %s -> 0 = M )' % P4)
sub1 = w.s([w.s([], 'oveq2', '( n = 1 -> ( A ^ n ) = ( A ^ 1 ) )'),
            w.s([w.s([], 'oveq2', '( n = 1 -> ( M ^ n ) = ( M ^ 1 ) )')], 'oveq2d', '( n = 1 -> ( K x. ( M ^ n ) ) = ( K x. ( M ^ 1 ) ) )')],
           'breq12d', '( n = 1 -> ( ( A ^ n ) <_ ( K x. ( M ^ n ) ) <-> ( A ^ 1 ) <_ ( K x. ( M ^ 1 ) ) ) )')
i1 = w.s([sub1, al4, w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % P4)], 'rspcdva',
         '( %s -> ( A ^ 1 ) <_ ( K x. ( M ^ 1 ) ) )' % P4)
e1a = w.s([w.s([ar4], 'recnd', '( %s -> A e. CC )' % P4), w.inst('exp1')], 'syl', '( %s -> ( A ^ 1 ) = A )' % P4)
e1b = w.s([w.s([mr4], 'recnd', '( %s -> M e. CC )' % P4), w.inst('exp1')], 'syl', '( %s -> ( M ^ 1 ) = M )' % P4)
i2 = w.s([i1, e1a, w.s([e1b], 'oveq2d', '( %s -> ( K x. ( M ^ 1 ) ) = ( K x. M ) )' % P4)], '3brtr3d', '( %s -> A <_ ( K x. M ) )' % P4)
km0 = w.s([w.s([w.s([meq], 'eqcomd', '( %s -> M = 0 )' % P4)], 'oveq2d', '( %s -> ( K x. M ) = ( K x. 0 ) )' % P4),
           w.s([w.s([kr4], 'recnd', '( %s -> K e. CC )' % P4)], 'mul01d', '( %s -> ( K x. 0 ) = 0 )' % P4)], 'eqtrd',
          '( %s -> ( K x. M ) = 0 )' % P4)
case2 = w.s([w.s([i2, km0], 'breqtrd', '( %s -> A <_ 0 )' % P4), meq], 'breqtrd', '( %s -> A <_ M )' % P4)

both = w.s([case1, case2], 'pm2.61dan', '( %s -> A <_ M )' % P2)
notle = w.s([w.s([], 'simpr', '( %s -> M < A )' % P2), w.s([w.s([mr], 'adantr', '( %s -> M e. RR )' % P2), w.s([ar], 'adantr', '( %s -> A e. RR )' % P2)],
                                                           'ltnled', '( %s -> ( M < A <-> -. A <_ M ) )' % P2)], 'mpbid', '( %s -> -. A <_ M )' % P2)
nlt = w.s([both, notle], 'pm2.65da', '( %s -> -. M < A )' % A0)
w.qed([nlt, w.s([ar, mr], 'lenltd', '( %s -> ( A <_ M <-> -. M < A ) )' % A0)], 'mpbird', '( %s -> A <_ M )' % A0); run1(w)

# ---- crectrbd --------------------------------------------------------------
G1 = '( %s - %s )' % (RP, RA); G2 = '( %s - %s )' % (RB, RP)
G3 = '( %s - %s )' % (IP, IA); G4 = '( %s - %s )' % (IB, IP)
GAPS = [G1, G2, G3, G4]


def BODY(t):
    return '( ( %s <_ %s /\\ %s <_ %s ) /\\ ( %s <_ %s /\\ %s <_ %s ) )' % (t, G1, t, G2, t, G3, t, G4)


def SM(a, b):
    return '( ( %s x. %s ) / ( %s + %s ) )' % (a, b, a, b)


w = W('crectrbd', 'A strictly interior point of a rectangle has a positive real below all four coordinate gaps.')
A0 = '( %s /\\ %s )' % (AB, INTP)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
it = w.s([], 'simpr', '( %s -> %s )' % (A0, INTP))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lt = [w.s([ineq, w.inst(r)], 'syl', '( %s -> %s )' % (A0, f)) for r, f in
      [('simpll', '%s < %s' % (RA, RP)), ('simplr', '%s < %s' % (RP, RB)),
       ('simprl', '%s < %s' % (IA, IP)), ('simprr', '%s < %s' % (IP, IB))]]
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
pr = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP)); pi_ = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
pairs = [(ar, pr), (pr, br), (ai, pi_), (pi_, bi)]
grp = []
for i, (x, y) in enumerate(pairs):
    pos = w.s([lt[i], w.s([x, y], 'posdifd', '( %s -> ( %s ) )' % (A0, ('%s < %s <-> 0 < %s' % (
        [RA, RP, IA, IP][i], [RP, RB, IP, IB][i], GAPS[i]))))], 'mpbid', '( %s -> 0 < %s )' % (A0, GAPS[i]))
    rl = w.s([y, x], 'resubcld', '( %s -> %s e. RR )' % (A0, GAPS[i]))
    grp.append(w.s([rl, pos], 'elrpd', '( %s -> %s e. RR+ )' % (A0, GAPS[i])))
S12 = SM(G1, G2); S34 = SM(G3, G4); WIT = SM(S12, S34)
sm12 = w.s([grp[0], grp[1], w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ %s /\\ %s <_ %s ) ) )' % (A0, S12, S12, G1, S12, G2))
sm34 = w.s([grp[2], grp[3], w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ %s /\\ %s <_ %s ) ) )' % (A0, S34, S34, G3, S34, G4))
p12 = w.s([sm12, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A0, S12))
p34 = w.s([sm34, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A0, S34))
l1 = w.s([sm12, w.inst('simprl')], 'syl', '( %s -> %s <_ %s )' % (A0, S12, G1))
l2 = w.s([sm12, w.inst('simprr')], 'syl', '( %s -> %s <_ %s )' % (A0, S12, G2))
l3 = w.s([sm34, w.inst('simprl')], 'syl', '( %s -> %s <_ %s )' % (A0, S34, G3))
l4 = w.s([sm34, w.inst('simprr')], 'syl', '( %s -> %s <_ %s )' % (A0, S34, G4))
smw = w.s([p12, p34, w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ %s /\\ %s <_ %s ) ) )' % (A0, WIT, WIT, S12, WIT, S34))
pw = w.s([smw, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A0, WIT))
w12 = w.s([smw, w.inst('simprl')], 'syl', '( %s -> %s <_ %s )' % (A0, WIT, S12))
w34 = w.s([smw, w.inst('simprr')], 'syl', '( %s -> %s <_ %s )' % (A0, WIT, S34))
wr = w.s([pw], 'rpred', '( %s -> %s e. RR )' % (A0, WIT))
r12 = w.s([p12], 'rpred', '( %s -> %s e. RR )' % (A0, S12))
r34 = w.s([p34], 'rpred', '( %s -> %s e. RR )' % (A0, S34))
gr = [w.s([grp[i]], 'rpred', '( %s -> %s e. RR )' % (A0, GAPS[i])) for i in range(4)]
tr = [w.s([wr, r12, gr[0], w12, l1], 'letrd', '( %s -> %s <_ %s )' % (A0, WIT, G1)),
      w.s([wr, r12, gr[1], w12, l2], 'letrd', '( %s -> %s <_ %s )' % (A0, WIT, G2)),
      w.s([wr, r34, gr[2], w34, l3], 'letrd', '( %s -> %s <_ %s )' % (A0, WIT, G3)),
      w.s([wr, r34, gr[3], w34, l4], 'letrd', '( %s -> %s <_ %s )' % (A0, WIT, G4))]
body = w.s([w.s([tr[0], tr[1]], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A0, WIT, G1, WIT, G2)),
            w.s([tr[2], tr[3]], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A0, WIT, G3, WIT, G4))], 'jca',
           '( %s -> %s )' % (A0, BODY(WIT)))
bq = [w.s([], 'breq1', '( r = %s -> ( r <_ %s <-> %s <_ %s ) )' % (WIT, GAPS[i], WIT, GAPS[i])) for i in range(4)]
sub = w.s([w.s([bq[0], bq[1]], 'anbi12d', '( r = %s -> ( ( r <_ %s /\\ r <_ %s ) <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (WIT, G1, G2, WIT, G1, WIT, G2)),
           w.s([bq[2], bq[3]], 'anbi12d', '( r = %s -> ( ( r <_ %s /\\ r <_ %s ) <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (WIT, G3, G4, WIT, G3, WIT, G4))],
          'anbi12d', '( r = %s -> ( %s <-> %s ) )' % (WIT, BODY('r'), BODY(WIT)))
w.qed([pw, body, w.s([sub], 'rspcev', '( ( %s e. RR+ /\\ %s ) -> E. r e. RR+ %s )' % (WIT, BODY(WIT), BODY('r')))],
      'syl2anc', '( %s -> E. r e. RR+ %s )' % (A0, BODY('r'))); run1(w)

# ---- crectfra --------------------------------------------------------------
w = W('crectfra', 'The lower left corner lies on the boundary frame of a rectangle.')
A0 = '( %s /\\ %s )' % (AB, GEO)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
s1 = w.s([ac, cc[P10], w.inst('csegid1')], 'syl2anc', '( %s -> A e. %s )' % (A0, SEGS[0]))
s2 = w.s([s1, w.inst('elun1')], 'syl', '( %s -> A e. ( %s u. %s ) )' % (A0, SEGS[0], SEGS[1]))
w.qed([s2, w.inst('elun1')], 'syl', '( %s -> A e. %s )' % (A0, FR)); run1(w)

# ---- rectintmmn ------------------------------------------------------------
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
HOLD = '( %s /\\ ( A crect B ) C_ D )' % HOL
BASE = '( %s /\\ %s /\\ %s )' % (AB, INTP, HOLD)
RBDP = RBD('P')
A1 = '( %s /\\ ( %s /\\ 0 < R ) /\\ ( M e. RR /\\ %s ) )' % (BASE, RBDP, ALF)
GN = MP('z', 'D', '( ( F ` z ) ^ N )')

w = W('rectintmmn', 'The Cauchy estimate of order zero applied to the N-th power of a holomorphic function.')
A0 = '( %s /\\ N e. NN )' % A1
A2 = '( %s /\\ v e. %s )' % (A0, FR)
a1 = w.s([], 'simpl', '( %s -> %s )' % (A0, A1))
nn = w.s([], 'simpr', '( %s -> N e. NN )' % A0)
nn0 = w.s([nn, w.inst('nnnn0')], 'syl', '( %s -> N e. NN0 )' % A0)
bs = w.s([a1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, BASE))
rb0 = w.s([a1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
mm_ = w.s([a1, w.inst('simp3')], 'syl', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
it = w.s([bs, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTP))
hd = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLD))
hl = w.s([hd, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
rdd = w.s([hd, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
mr = w.s([mm_, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
alf = w.s([mm_, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
fcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lt = [w.s([ineq, w.inst(r)], 'syl', '( %s -> %s )' % (A0, f)) for r, f in
      [('simpll', '%s < %s' % (RA, RP)), ('simplr', '%s < %s' % (RP, RB)),
       ('simprl', '%s < %s' % (IA, IP)), ('simprr', '%s < %s' % (IP, IB))]]
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
pr = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP)); pi_ = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
geo = w.s([w.s([w.s([ar, pr, br, lt[0], lt[1]], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB)),
           w.s([w.s([ai, pi_, bi, lt[2], lt[3]], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))],
          'jca', '( %s -> %s )' % (A0, GEO))
fru = w.s([ab, geo, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( A crect B ) )' % (A0, FR))
frd = w.s([fru, rdd], 'sstrd', '( %s -> %s C_ D )' % (A0, FR))
# holomorphy of the N-th power
hx = w.s([hl, nn, w.inst('holexp')], 'syl2anc', '( %s -> %s )' % (A0, HOLG(GN)))
gcn = w.s([hx, w.inst('simpl')], 'syl', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, GN))
ho = w.s([hx, rdd, w.inst('holcrect')], 'syl2anc', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) ) )' % (A0, GN, GN))
# the frame bound on the N-th power, in v
vf = w.s([], 'simpr', '( %s -> v e. %s )' % (A2, FR))
vd = w.s([w.s([frd], 'adantr', '( %s -> %s C_ D )' % (A2, FR)), vf], 'sseldd', '( %s -> v e. D )' % A2)
fv = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A2), vd], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A2)
subv = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )')], 'oveq1d', '( z = v -> ( ( F ` z ) ^ N ) = ( ( F ` v ) ^ N ) )')
gvv = mptval(w, A2, 'z', 'D', GN, 'v', '( ( F ` v ) ^ N )', subv, vd)
n0a = w.s([nn0], 'adantr', '( %s -> N e. NN0 )' % A2)
abv = w.s([fv, n0a, w.inst('absexp')], 'syl2anc', '( %s -> ( abs ` ( ( F ` v ) ^ N ) ) = ( ( abs ` ( F ` v ) ) ^ N ) )' % A2)
subu = w.s([w.s([w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')], 'fveq2d', '( u = v -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` v ) ) )')],
           'breq1d', '( u = v -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` v ) ) <_ M ) )')
bnd = w.s([subu, w.s([alf], 'adantr', '( %s -> %s )' % (A2, ALF)), vf], 'rspcdva', '( %s -> ( abs ` ( F ` v ) ) <_ M )' % A2)
afv = w.s([fv], 'abscld', '( %s -> ( abs ` ( F ` v ) ) e. RR )' % A2)
afv0 = w.s([fv], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A2)
lex = w.s([afv, w.s([mr], 'adantr', '( %s -> M e. RR )' % A2), n0a, afv0, bnd], 'leexp1ad',
          '( %s -> ( ( abs ` ( F ` v ) ) ^ N ) <_ ( M ^ N ) )' % A2)
step = w.s([w.s([w.s([gvv], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` ( ( F ` v ) ^ N ) ) )' % (A2, GN)), abv], 'eqtrd',
                '( %s -> ( abs ` ( %s ` v ) ) = ( ( abs ` ( F ` v ) ) ^ N ) )' % (A2, GN)), lex], 'eqbrtrd',
           '( %s -> ( abs ` ( %s ` v ) ) <_ ( M ^ N ) )' % (A2, GN))
allv = w.s([step], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ ( M ^ N ) )' % (A0, FR, GN))
cbv = w.s([w.s([w.s([w.s([], 'fveq2', '( v = u -> ( %s ` v ) = ( %s ` u ) )' % (GN, GN))], 'fveq2d',
                    '( v = u -> ( abs ` ( %s ` v ) ) = ( abs ` ( %s ` u ) ) )' % (GN, GN))], 'breq1d',
                '( v = u -> ( ( abs ` ( %s ` v ) ) <_ ( M ^ N ) <-> ( abs ` ( %s ` u ) ) <_ ( M ^ N ) ) )' % (GN, GN))], 'cbvralvw',
           '( A. v e. %s ( abs ` ( %s ` v ) ) <_ ( M ^ N ) <-> A. u e. %s ( abs ` ( %s ` u ) ) <_ ( M ^ N ) )' % (FR, GN, FR, GN))
allu = w.s([allv, cbv], 'sylib', '( %s -> A. u e. %s ( abs ` ( %s ` u ) ) <_ ( M ^ N ) )' % (A0, FR, GN))
mn = w.s([mr, nn0], 'reexpcld', '( %s -> ( M ^ N ) e. RR )' % A0)
ce = w.s([w.s([ab, it, ho], '3jca', '( %s -> ( %s /\\ %s /\\ ( %s e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) ) ) )' % (A0, AB, INTP, GN, GN)),
          rb0, w.s([mn, allu], 'jca', '( %s -> ( ( M ^ N ) e. RR /\\ A. u e. %s ( abs ` ( %s ` u ) ) <_ ( M ^ N ) ) )' % (A0, FR, GN)),
          w.inst('rectintce0')], 'syl3anc',
         '( %s -> ( ( _pi x. R ) x. ( abs ` ( %s ` P ) ) ) <_ ( ( M ^ N ) x. %s ) )' % (A0, GN, PER))
pcr = w.s([ab, it, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)
pd = w.s([rdd, pcr], 'sseldd', '( %s -> P e. D )' % A0)
fp = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
subp = w.s([w.s([], 'fveq2', '( z = P -> ( F ` z ) = ( F ` P ) )')], 'oveq1d', '( z = P -> ( ( F ` z ) ^ N ) = ( ( F ` P ) ^ N ) )')
gvp = mptval(w, A0, 'z', 'D', GN, 'P', '( ( F ` P ) ^ N )', subp, pd)
abp = w.s([fp, nn0, w.inst('absexp')], 'syl2anc', '( %s -> ( abs ` ( ( F ` P ) ^ N ) ) = ( ( abs ` ( F ` P ) ) ^ N ) )' % A0)
eqp = w.s([w.s([gvp], 'fveq2d', '( %s -> ( abs ` ( %s ` P ) ) = ( abs ` ( ( F ` P ) ^ N ) ) )' % (A0, GN)), abp], 'eqtrd',
          '( %s -> ( abs ` ( %s ` P ) ) = ( ( abs ` ( F ` P ) ) ^ N ) )' % (A0, GN))
oq = w.s([w.s([eqp], 'oveq2d', '( %s -> ( ( _pi x. R ) x. ( abs ` ( %s ` P ) ) ) = ( ( _pi x. R ) x. ( ( abs ` ( F ` P ) ) ^ N ) ) )' % (A0, GN))], 'eqcomd',
         '( %s -> ( ( _pi x. R ) x. ( ( abs ` ( F ` P ) ) ^ N ) ) = ( ( _pi x. R ) x. ( abs ` ( %s ` P ) ) ) )' % (A0, GN))
w.qed([oq, ce], 'eqbrtrd', '( %s -> ( ( _pi x. R ) x. ( ( abs ` ( F ` P ) ) ^ N ) ) <_ ( ( M ^ N ) x. %s ) )' % (A0, PER)); run1(w)

# ---- rectintmm -------------------------------------------------------------
w = W('rectintmm', 'The maximum modulus principle for a rectangle: a function holomorphic on an open set containing the rectangle is bounded at a strictly interior point by its bound on the boundary frame.')
A0 = '( %s /\\ ( M e. RR /\\ %s ) )' % (BASE, ALF)
Q1 = '( %s /\\ r e. RR+ )' % A0
Q0 = '( %s /\\ %s )' % (Q1, BODY('r'))
QN = '( %s /\\ n e. NN )' % Q0
AP = '( abs ` ( F ` P ) )'
KK = '( %s / ( _pi x. r ) )' % PER
bs = w.s([], 'simpl', '( %s -> %s )' % (A0, BASE))
mm_ = w.s([], 'simpr', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
it = w.s([bs, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTP))
hd = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLD))
hl = w.s([hd, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
rdd = w.s([hd, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
mr = w.s([mm_, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
alf = w.s([mm_, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
fcn = w.s([hl, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (A0, RA, RP, RP, RB, IA, IP, IP, IB))
lt = [w.s([ineq, w.inst(r)], 'syl', '( %s -> %s )' % (A0, f)) for r, f in
      [('simpll', '%s < %s' % (RA, RP)), ('simplr', '%s < %s' % (RP, RB)),
       ('simprl', '%s < %s' % (IA, IP)), ('simprr', '%s < %s' % (IP, IB))]]
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
pr = w.s([pc], 'recld', '( %s -> %s e. RR )' % (A0, RP)); pi_ = w.s([pc], 'imcld', '( %s -> %s e. RR )' % (A0, IP))
ltr = w.s([ar, pr, br, lt[0], lt[1]], 'lttrd', '( %s -> %s < %s )' % (A0, RA, RB))
lti = w.s([ai, pi_, bi, lt[2], lt[3]], 'lttrd', '( %s -> %s < %s )' % (A0, IA, IB))
geo = w.s([w.s([ltr], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RB)), w.s([lti], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IB))],
          'jca', '( %s -> %s )' % (A0, GEO))
# PER is a positive real
d1 = w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA))
d2 = w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))
perr = w.s([d1, d2], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
p1 = w.s([ltr, w.s([ar, br], 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A0, RA, RB, RB, RA))], 'mpbid', '( %s -> 0 < ( %s - %s ) )' % (A0, RB, RA))
p2 = w.s([lti, w.s([ai, bi], 'posdifd', '( %s -> ( %s < %s <-> 0 < ( %s - %s ) ) )' % (A0, IA, IB, IB, IA))], 'mpbid', '( %s -> 0 < ( %s - %s ) )' % (A0, IB, IA))
perp = w.s([w.s([d1, p1], 'elrpd', '( %s -> ( %s - %s ) e. RR+ )' % (A0, RB, RA)),
            w.s([d2, p2], 'elrpd', '( %s -> ( %s - %s ) e. RR+ )' % (A0, IB, IA))], 'rpaddcld', '( %s -> %s e. RR+ )' % (A0, PER))
# 0 <_ M from the frame bound at the lower left corner
fra = w.s([ab, geo, w.inst('crectfra')], 'syl2anc', '( %s -> A e. %s )' % (A0, FR))
fru = w.s([ab, geo, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ ( A crect B ) )' % (A0, FR))
frd = w.s([fru, rdd], 'sstrd', '( %s -> %s C_ D )' % (A0, FR))
adm = w.s([frd, fra], 'sseldd', '( %s -> A e. D )' % A0)
faC = w.s([ff, adm], 'ffvelcdmd', '( %s -> ( F ` A ) e. CC )' % A0)
suba = w.s([w.s([w.s([], 'fveq2', '( u = A -> ( F ` u ) = ( F ` A ) )')], 'fveq2d', '( u = A -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` A ) ) )')],
           'breq1d', '( u = A -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` A ) ) <_ M ) )')
bnda = w.s([suba, alf, fra], 'rspcdva', '( %s -> ( abs ` ( F ` A ) ) <_ M )' % A0)
m0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.s([faC], 'abscld', '( %s -> ( abs ` ( F ` A ) ) e. RR )' % A0), mr,
          w.s([faC], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` A ) ) )' % A0), bnda], 'letrd', '( %s -> 0 <_ M )' % A0)
pcr = w.s([ab, it, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)
pd = w.s([rdd, pcr], 'sseldd', '( %s -> P e. D )' % A0)
fp = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
apr = w.s([fp], 'abscld', '( %s -> %s e. RR )' % (A0, AP))
ap0 = w.s([fp], 'absge0d', '( %s -> 0 <_ %s )' % (A0, AP))
# ---- under ( A0 /\ r e. RR+ ) /\ BODY(r)
rrp = w.s([w.s([], 'simpr', '( %s -> r e. RR+ )' % Q1)], 'adantr', '( %s -> r e. RR+ )' % Q0)
body = w.s([], 'simpr', '( %s -> %s )' % (Q0, BODY('r')))
rre = w.s([rrp], 'rpred', '( %s -> r e. RR )' % Q0)
rpos = w.s([rrp], 'rpgt0d', '( %s -> 0 < r )' % Q0)
rbd = w.s([rre, body], 'jca', '( %s -> %s )' % (Q0, BODY('r').join(['( r e. RR /\\ ', ' )'])))
pirpd = w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % Q0)
pird = w.s([pirpd, rrp], 'rpmulcld', '( %s -> ( _pi x. r ) e. RR+ )' % Q0)


def lift0(st, form):
    return w.s([w.s([st], 'adantr', '( %s -> %s )' % (Q1, form))], 'adantr', '( %s -> %s )' % (Q0, form))


a1q = lift0(bs, BASE); mrq = lift0(mr, 'M e. RR'); alfq = lift0(alf, ALF)
perq = lift0(perp, '%s e. RR+' % PER); aprq = lift0(apr, '%s e. RR' % AP); ap0q = lift0(ap0, '0 <_ %s' % AP)
m0q = lift0(m0, '0 <_ M'); perrq = lift0(perr, '%s e. RR' % PER)
kkrp = w.s([perq, pird], 'rpdivcld', '( %s -> %s e. RR+ )' % (Q0, KK))
# the per-n inequality
nn = w.s([], 'simpr', '( %s -> n e. NN )' % QN)
nn0 = w.s([nn, w.inst('nnnn0')], 'syl', '( %s -> n e. NN0 )' % QN)
a1n = w.s([a1q], 'adantr', '( %s -> %s )' % (QN, BASE))
mrn = w.s([mrq], 'adantr', '( %s -> M e. RR )' % QN)
alfn = w.s([alfq], 'adantr', '( %s -> %s )' % (QN, ALF))
rbdn = w.s([rbd], 'adantr', '( %s -> %s )' % (QN, '( r e. RR /\\ %s )' % BODY('r')))
rposn = w.s([rpos], 'adantr', '( %s -> 0 < r )' % QN)
pirdn = w.s([pird], 'adantr', '( %s -> ( _pi x. r ) e. RR+ )' % QN)
perrn = w.s([perrq], 'adantr', '( %s -> %s e. RR )' % (QN, PER))
aprn = w.s([aprq], 'adantr', '( %s -> %s e. RR )' % (QN, AP))
mmn = w.s([a1n, w.s([rbdn, rposn], 'jca', '( %s -> ( %s /\\ 0 < r ) )' % (QN, '( r e. RR /\\ %s )' % BODY('r'))),
           w.s([mrn, alfn], 'jca', '( %s -> ( M e. RR /\\ %s ) )' % (QN, ALF)), nn, w.inst('rectintmmn')], 'syl31anc',
          '( %s -> ( ( _pi x. r ) x. ( %s ^ n ) ) <_ ( ( M ^ n ) x. %s ) )' % (QN, AP, PER))
apn = w.s([aprn, nn0], 'reexpcld', '( %s -> ( %s ^ n ) e. RR )' % (QN, AP))
mn = w.s([mrn, nn0], 'reexpcld', '( %s -> ( M ^ n ) e. RR )' % QN)
mpr = w.s([mn, perrn], 'remulcld', '( %s -> ( ( M ^ n ) x. %s ) e. RR )' % (QN, PER))
piC = w.s([pirdn], 'rpred', '( %s -> ( _pi x. r ) e. RR )' % QN)
piP = w.s([pirdn], 'rpgt0d', '( %s -> 0 < ( _pi x. r ) )' % QN)
div1 = w.s([mmn, w.s([apn, mpr, w.s([piC, piP], 'jca', '( %s -> ( ( _pi x. r ) e. RR /\\ 0 < ( _pi x. r ) ) )' % QN), w.inst('lemuldiv2')], 'syl3anc',
                     '( %s -> ( ( ( _pi x. r ) x. ( %s ^ n ) ) <_ ( ( M ^ n ) x. %s ) <-> ( %s ^ n ) <_ ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) ) )' % (QN, AP, PER, AP, PER))],
            'mpbid', '( %s -> ( %s ^ n ) <_ ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) )' % (QN, AP, PER))
mnc = w.s([mn], 'recnd', '( %s -> ( M ^ n ) e. CC )' % QN)
perc = w.s([perrn], 'recnd', '( %s -> %s e. CC )' % (QN, PER))
pic = w.s([piC], 'recnd', '( %s -> ( _pi x. r ) e. CC )' % QN)
pine = w.s([pirdn], 'rpne0d', '( %s -> ( _pi x. r ) =/= 0 )' % QN)
eq1 = w.s([w.s([mnc, perc], 'mulcomd', '( %s -> ( ( M ^ n ) x. %s ) = ( %s x. ( M ^ n ) ) )' % (QN, PER, PER))], 'oveq1d',
          '( %s -> ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) = ( ( %s x. ( M ^ n ) ) / ( _pi x. r ) ) )' % (QN, PER, PER))
eq2 = w.s([perc, mnc, pic, pine], 'div23d', '( %s -> ( ( %s x. ( M ^ n ) ) / ( _pi x. r ) ) = ( %s x. ( M ^ n ) ) )' % (QN, PER, KK))
stepn = w.s([div1, w.s([eq1, eq2], 'eqtrd', '( %s -> ( ( ( M ^ n ) x. %s ) / ( _pi x. r ) ) = ( %s x. ( M ^ n ) ) )' % (QN, PER, KK))],
            'breqtrd', '( %s -> ( %s ^ n ) <_ ( %s x. ( M ^ n ) ) )' % (QN, AP, KK))
alln = w.s([stepn], 'ralrimiva', '( %s -> A. n e. NN ( %s ^ n ) <_ ( %s x. ( M ^ n ) ) )' % (Q0, AP, KK))
edl = w.s([w.s([aprq, ap0q], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (Q0, AP, AP)),
           w.s([mrq, m0q], 'jca', '( %s -> ( M e. RR /\\ 0 <_ M ) )' % Q0),
           w.s([w.s([w.s([kkrp], 'rpred', '( %s -> %s e. RR )' % (Q0, KK)), w.s([kkrp], 'rpgt0d', '( %s -> 0 < %s )' % (Q0, KK))], 'jca',
                    '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (Q0, KK, KK)), alln], 'jca',
               '( %s -> ( ( %s e. RR /\\ 0 < %s ) /\\ A. n e. NN ( %s ^ n ) <_ ( %s x. ( M ^ n ) ) ) )' % (Q0, KK, KK, AP, KK)),
           w.inst('expdomle')], 'syl3anc', '( %s -> %s <_ M )' % (Q0, AP))
ex = w.s([edl], 'ex', '( %s -> ( %s -> %s <_ M ) )' % (Q1, BODY('r'), AP))
rex = w.s([ab, it, w.inst('crectrbd')], 'syl2anc', '( %s -> E. r e. RR+ %s )' % (A0, BODY('r')))
w.qed([w.s([ex], 'rexlimdva', '( %s -> ( E. r e. RR+ %s -> %s <_ M ) )' % (A0, BODY('r'), AP)), rex], 'mpd',
      '( %s -> %s <_ M )' % (A0, AP)); run1(w)
