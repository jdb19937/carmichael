"""Sortie C1 section 6: the two-pole calculus and Cauchy's formula as a
difference quotient over two strictly interior points."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c1_lib import *

RP = RE('P'); IP = IM('P'); RQ = RE('Q'); IQ = IM('Q')
INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RP, RP, RB, IA, IP, IP, IB)
INTQ = '( Q e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RQ, RQ, RB, IA, IQ, IQ, IB)
HOLO = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) )'
CP = '( CC \\ { P } )'; CQ = '( CC \\ { Q } )'
PUP = '( ( A crect B ) \\ { P } )'; PUQ = '( ( A crect B ) \\ { Q } )'
E2 = '( ( A crect B ) \\ { P , Q } )'
TPI = '( 2 x. ( _i x. _pi ) )'


def QFP(E, PP='P'):
    return '( z e. %s |-> ( ( F ` z ) / ( z - %s ) ) )' % (E, PP)


def KPQ(E):
    return '( z e. %s |-> ( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) ) )' % E


# ---- divsubpq --------------------------------------------------------------
w = W('divsubpq', 'Splitting the Cauchy kernel at P into the two-pole kernel and '
      'the Cauchy kernel at Q.')
A0 = '( ( V e. CC /\\ P e. CC /\\ Q e. CC ) /\\ ( Z e. CC /\\ ( Z - P ) =/= 0 /\\ ( Z - Q ) =/= 0 ) )'
DD2 = '( ( Z - P ) x. ( Z - Q ) )'
vc = w.s([w.s([], 'simpl', '( %s -> ( V e. CC /\\ P e. CC /\\ Q e. CC ) )' % A0), w.inst('simp1')], 'syl', '( %s -> V e. CC )' % A0)
pc = w.s([w.s([], 'simpl', '( %s -> ( V e. CC /\\ P e. CC /\\ Q e. CC ) )' % A0), w.inst('simp2')], 'syl', '( %s -> P e. CC )' % A0)
qc = w.s([w.s([], 'simpl', '( %s -> ( V e. CC /\\ P e. CC /\\ Q e. CC ) )' % A0), w.inst('simp3')], 'syl', '( %s -> Q e. CC )' % A0)
zc = w.s([w.s([], 'simpr', '( %s -> ( Z e. CC /\\ ( Z - P ) =/= 0 /\\ ( Z - Q ) =/= 0 ) )' % A0), w.inst('simp1')], 'syl', '( %s -> Z e. CC )' % A0)
zpn = w.s([w.s([], 'simpr', '( %s -> ( Z e. CC /\\ ( Z - P ) =/= 0 /\\ ( Z - Q ) =/= 0 ) )' % A0), w.inst('simp2')], 'syl', '( %s -> ( Z - P ) =/= 0 )' % A0)
zqn = w.s([w.s([], 'simpr', '( %s -> ( Z e. CC /\\ ( Z - P ) =/= 0 /\\ ( Z - Q ) =/= 0 ) )' % A0), w.inst('simp3')], 'syl', '( %s -> ( Z - Q ) =/= 0 )' % A0)
zp = w.s([zc, pc], 'subcld', '( %s -> ( Z - P ) e. CC )' % A0)
zq = w.s([zc, qc], 'subcld', '( %s -> ( Z - Q ) e. CC )' % A0)
pq = w.s([pc, qc], 'subcld', '( %s -> ( P - Q ) e. CC )' % A0)
dc = w.s([zp, zq], 'mulcld', '( %s -> %s e. CC )' % (A0, DD2))
dn = w.s([zp, zq, zpn, zqn], 'mulne0d', '( %s -> %s =/= 0 )' % (A0, DD2))
t1 = w.s([w.s([pq, vc, dc, dn], 'divassd', '( %s -> ( ( ( P - Q ) x. V ) / %s ) = ( ( P - Q ) x. ( V / %s ) ) )' % (A0, DD2, DD2))], 'eqcomd',
         '( %s -> ( ( P - Q ) x. ( V / %s ) ) = ( ( ( P - Q ) x. V ) / %s ) )' % (A0, DD2, DD2))
t2 = w.s([w.s([vc, zq, zp, zqn, zpn], 'divcan5d', '( %s -> ( ( ( Z - P ) x. V ) / ( ( Z - P ) x. ( Z - Q ) ) ) = ( V / ( Z - Q ) ) )' % A0)], 'eqcomd',
         '( %s -> ( V / ( Z - Q ) ) = ( ( ( Z - P ) x. V ) / %s ) )' % (A0, DD2))
sm = w.s([t1, t2], 'oveq12d', '( %s -> ( ( ( P - Q ) x. ( V / %s ) ) + ( V / ( Z - Q ) ) ) = ( ( ( ( P - Q ) x. V ) / %s ) + ( ( ( Z - P ) x. V ) / %s ) ) )' % (A0, DD2, DD2, DD2))
dd = w.s([w.s([w.s([pq, vc], 'mulcld', '( %s -> ( ( P - Q ) x. V ) e. CC )' % A0), w.s([zp, vc], 'mulcld', '( %s -> ( ( Z - P ) x. V ) e. CC )' % A0), dc, dn],
              'divdird', '( %s -> ( ( ( ( P - Q ) x. V ) + ( ( Z - P ) x. V ) ) / %s ) = ( ( ( ( P - Q ) x. V ) / %s ) + ( ( ( Z - P ) x. V ) / %s ) ) )' % (A0, DD2, DD2, DD2))], 'eqcomd',
         '( %s -> ( ( ( ( P - Q ) x. V ) / %s ) + ( ( ( Z - P ) x. V ) / %s ) ) = ( ( ( ( P - Q ) x. V ) + ( ( Z - P ) x. V ) ) / %s ) )' % (A0, DD2, DD2, DD2))
nm = w.s([w.s([w.s([pq, zp, vc], 'adddird', '( %s -> ( ( ( P - Q ) + ( Z - P ) ) x. V ) = ( ( ( P - Q ) x. V ) + ( ( Z - P ) x. V ) ) )' % A0)], 'eqcomd',
               '( %s -> ( ( ( P - Q ) x. V ) + ( ( Z - P ) x. V ) ) = ( ( ( P - Q ) + ( Z - P ) ) x. V ) )' % A0),
          w.s([w.s([pc, qc, zc, w.inst('npncan3')], 'syl3anc', '( %s -> ( ( P - Q ) + ( Z - P ) ) = ( Z - Q ) )' % A0)], 'oveq1d',
              '( %s -> ( ( ( P - Q ) + ( Z - P ) ) x. V ) = ( ( Z - Q ) x. V ) )' % A0)], 'eqtrd',
         '( %s -> ( ( ( P - Q ) x. V ) + ( ( Z - P ) x. V ) ) = ( ( Z - Q ) x. V ) )' % A0)
cm = w.s([w.s([zq, vc], 'mulcomd', '( %s -> ( ( Z - Q ) x. V ) = ( V x. ( Z - Q ) ) )' % A0)], 'oveq1d',
         '( %s -> ( ( ( Z - Q ) x. V ) / %s ) = ( ( V x. ( Z - Q ) ) / %s ) )' % (A0, DD2, DD2))
cn = w.s([vc, zp, zq, zpn, zqn], 'divcan5rd', '( %s -> ( ( V x. ( Z - Q ) ) / ( ( Z - P ) x. ( Z - Q ) ) ) = ( V / ( Z - P ) ) )' % A0)
w.qed([w.s([w.s([sm, dd], 'eqtrd', '( %s -> ( ( ( P - Q ) x. ( V / %s ) ) + ( V / ( Z - Q ) ) ) = ( ( ( ( P - Q ) x. V ) + ( ( Z - P ) x. V ) ) / %s ) )' % (A0, DD2, DD2)),
             w.s([nm], 'oveq1d', '( %s -> ( ( ( ( P - Q ) x. V ) + ( ( Z - P ) x. V ) ) / %s ) = ( ( ( Z - Q ) x. V ) / %s ) )' % (A0, DD2, DD2))], 'eqtrd',
            '( %s -> ( ( ( P - Q ) x. ( V / %s ) ) + ( V / ( Z - Q ) ) ) = ( ( ( Z - Q ) x. V ) / %s ) )' % (A0, DD2, DD2)),
       w.s([cm, cn], 'eqtrd', '( %s -> ( ( ( Z - Q ) x. V ) / %s ) = ( V / ( Z - P ) ) )' % (A0, DD2))], 'eqtr2d',
      '( %s -> ( V / ( Z - P ) ) = ( ( ( P - Q ) x. ( V / %s ) ) + ( V / ( Z - Q ) ) ) )' % (A0, DD2)); run1(w)

# ---- qf2cn -----------------------------------------------------------------
w = W('qf2cn', 'The two-pole Cauchy kernel of a continuous function is '
      'continuous off both poles.')
A0 = '( F e. ( D -cn-> CC ) /\\ E C_ D /\\ ( ( P e. CC /\\ E C_ %s ) /\\ ( Q e. CC /\\ E C_ %s ) ) )' % (CP, CQ)
A1 = '( %s /\\ z e. E )' % A0
fcn = w.s([], 'simp1', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ed = w.s([], 'simp2', '( %s -> E C_ D )' % A0)
pp = w.s([w.s([], 'simp3', '( %s -> ( ( P e. CC /\\ E C_ %s ) /\\ ( Q e. CC /\\ E C_ %s ) ) )' % (A0, CP, CQ)), w.inst('simpl')], 'syl',
         '( %s -> ( P e. CC /\\ E C_ %s ) )' % (A0, CP))
qq = w.s([w.s([], 'simp3', '( %s -> ( ( P e. CC /\\ E C_ %s ) /\\ ( Q e. CC /\\ E C_ %s ) ) )' % (A0, CP, CQ)), w.inst('simpr')], 'syl',
         '( %s -> ( Q e. CC /\\ E C_ %s ) )' % (A0, CQ))
pc = w.s([pp, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ecp = w.s([pp, w.inst('simpr')], 'syl', '( %s -> E C_ %s )' % (A0, CP))
qc = w.s([qq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
ecq = w.s([qq, w.inst('simpr')], 'syl', '( %s -> E C_ %s )' % (A0, CQ))
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
qp = w.s([w.s([fcn, ed, pp], '3jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ E C_ D /\\ ( P e. CC /\\ E C_ %s ) ) )' % (A0, CP)), w.inst('qfcn')], 'syl',
         '( %s -> %s e. ( E -cn-> CC ) )' % (A0, QFP('E')))
rq = w.s([qc, ecq, w.inst('rinvcnss')], 'syl2anc', '( %s -> ( z e. E |-> ( 1 / ( z - Q ) ) ) e. ( E -cn-> CC ) )' % A0)
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
mcn = w.s([w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
prod = w.s([ej, mcn, qp, rq], 'cncfmpt2f', '( %s -> ( z e. E |-> ( ( ( F ` z ) / ( z - P ) ) x. ( 1 / ( z - Q ) ) ) ) e. ( E -cn-> CC ) )' % A0)
zE = w.s([], 'simpr', '( %s -> z e. E )' % A1)
zd = w.s([w.s([ed], 'adantr', '( %s -> E C_ D )' % A1), zE], 'sseldd', '( %s -> z e. D )' % A1)
fz = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
zcp = w.s([w.s([ecp], 'adantr', '( %s -> E C_ %s )' % (A1, CP)), zE], 'sseldd', '( %s -> z e. %s )' % (A1, CP))
zcq = w.s([w.s([ecq], 'adantr', '( %s -> E C_ %s )' % (A1, CQ)), zE], 'sseldd', '( %s -> z e. %s )' % (A1, CQ))
zc = w.s([w.s([zcp, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= P ) )' % A1), w.inst('simpl')], 'syl', '( %s -> z e. CC )' % A1)
znp = w.s([w.s([zcp, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
znq = w.s([w.s([zcq, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= Q ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= Q )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
qc1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1)
zp = w.s([zc, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
zq = w.s([zc, qc1], 'subcld', '( %s -> ( z - Q ) e. CC )' % A1)
zpn = w.s([zc, pc1, znp], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
zqn = w.s([zc, qc1, znq], 'subne0d', '( %s -> ( z - Q ) =/= 0 )' % A1)
dv1 = w.s([fz, zp, zq, zpn, zqn], 'divdiv1d', '( %s -> ( ( ( F ` z ) / ( z - P ) ) / ( z - Q ) ) = ( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) ) )' % A1)
dv2 = w.s([w.s([fz, zp, zpn], 'divcld', '( %s -> ( ( F ` z ) / ( z - P ) ) e. CC )' % A1), zq, zqn], 'divrecd',
          '( %s -> ( ( ( F ` z ) / ( z - P ) ) / ( z - Q ) ) = ( ( ( F ` z ) / ( z - P ) ) x. ( 1 / ( z - Q ) ) ) )' % A1)
pt = w.s([w.s([dv1], 'eqcomd', '( %s -> ( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) ) = ( ( ( F ` z ) / ( z - P ) ) / ( z - Q ) ) )' % A1), dv2], 'eqtrd',
         '( %s -> ( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) ) = ( ( ( F ` z ) / ( z - P ) ) x. ( 1 / ( z - Q ) ) ) )' % A1)
mt = w.s([pt], 'mpteq2dva', '( %s -> %s = ( z e. E |-> ( ( ( F ` z ) / ( z - P ) ) x. ( 1 / ( z - Q ) ) ) ) )' % (A0, KPQ('E')))
w.qed([mt, prod], 'eqeltrd', '( %s -> %s e. ( E -cn-> CC ) )' % (A0, KPQ('E'))); run1(w)

# ---- crectinp: a strictly interior point lies in the rectangle -------------
w = W('crectinp', 'A strictly interior point lies in the closed rectangle.')
A0 = '( %s /\\ %s )' % (AB, INT)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
it = w.s([], 'simpr', '( %s -> %s )' % (A0, INT))
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
prI = w.s([pr, w.s([ar, pr, lr], 'ltled', '( %s -> %s <_ %s )' % (A0, RA, RP)), w.s([pr, br, rr_], 'ltled', '( %s -> %s <_ %s )' % (A0, RP, RB)),
           w.s([ar, br, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, RP, RA, RB, RP, RA, RP, RP, RB))],
          'mpbir3and', '( %s -> %s e. ( %s [,] %s ) )' % (A0, RP, RA, RB))
piI = w.s([pi_, w.s([ai, pi_, li], 'ltled', '( %s -> %s <_ %s )' % (A0, IA, IP)), w.s([pi_, bi, ri], 'ltled', '( %s -> %s <_ %s )' % (A0, IP, IB)),
           w.s([ai, bi, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, IP, IA, IB, IP, IA, IP, IP, IB))],
          'mpbir3and', '( %s -> %s e. ( %s [,] %s ) )' % (A0, IP, IA, IB))
w.qed([pc, prI, piI, w.s([ab, w.inst('elcrect')], 'syl',
                         '( %s -> ( P e. ( A crect B ) <-> ( P e. CC /\\ %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) ) ) )' % (A0, RP, RA, RB, IP, IA, IB))],
      'mpbir3and', '( %s -> P e. ( A crect B ) )' % A0); run1(w)


# ---- rectintcle: closure of a boundary integral from continuity on the frame
w = W('rectintcle', 'A rectangle boundary integral is a complex number when the '
      'integrand is continuous on a set containing the boundary frame.')
A0 = '( %s /\\ ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (AB, FR)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
fd = w.s([], 'simpr', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, FR))
fcn = w.s([fd, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
frd = w.s([fd, w.inst('simpr')], 'syl', '( %s -> %s C_ D )' % (A0, FR))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
sd = edges4(w, A0, frd, T='D')
fex = w.s([fcn, w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
cls = []
for i, (S, T) in enumerate(EDGES):
    ph = w.s([w.s([cc[S], cc[T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T)),
              w.s([fcn, sd[i]], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, SEGS[i]))], 'jca',
             '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ %s C_ D ) ) )' % (A0, S, T, SEGS[i]))
    cls.append(w.s([ph, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('F', S, T))))
rv = w.s([fex, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B')))
tot = w.s([w.s([cls[0], cls[1]], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, LINT('F', *EDGES[0]), LINT('F', *EDGES[1]))),
           w.s([cls[2], cls[3]], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, LINT('F', *EDGES[2]), LINT('F', *EDGES[3])))],
          'addcld', '( %s -> %s e. CC )' % (A0, RAW('A', 'B')))
w.qed([rv, tot], 'eqeltrd', '( %s -> %s e. CC )' % (A0, RINT('F', 'A', 'B'))); run1(w)

# ---- rectintcaud -----------------------------------------------------------
w = W('rectintcaud', 'The Cauchy integral formula as a difference over two '
      'strictly interior points: the difference quotient of F at P and Q is the '
      'boundary integral of the two-pole kernel.')
A0 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s )' % (AB, INT, INTQ, HOLO)
A1 = '( %s /\\ u e. %s )' % (A0, E2)
AFR = '( %s /\\ u e. %s )' % (A0, FR)
ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
tri = w.s([], 'simp2', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INT, INTQ))
holo = w.s([], 'simp3', '( %s -> %s )' % (A0, HOLO))
it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INT))
itq = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
qc = w.s([itq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
dvb = w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
crd = w.s([hss, dvb], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
e2d = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, E2))
pupd = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, PUP))
puqd = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, PUQ))
pupc = w.s([crss], 'ssdifd', '( %s -> %s C_ %s )' % (A0, PUP, CP))
puqc = w.s([crss], 'ssdifd', '( %s -> %s C_ %s )' % (A0, PUQ, CQ))
e2cp = w.s([crss, closed(w, A0, 'snsspr1', '{ P } C_ { P , Q }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CP))
e2cq = w.s([crss, closed(w, A0, 'snsspr2', '{ Q } C_ { P , Q }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CQ))
frp = w.s([w.s([ab, it], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INT)), w.inst('crectfrp')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, PUP))
frq = w.s([w.s([ab, itq], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTQ)), w.inst('crectfrp')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, PUQ))
fr2 = w.s([w.s([ab, it, itq], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INT, INTQ)), w.inst('crectfrd')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, E2))
# continuity of the four mappings
def qcn(E, PP, ssD, ssC):
    return w.s([w.s([fcn, ssD, w.s([pc if PP == 'P' else qc, ssC], 'jca', '( %s -> ( %s e. CC /\\ %s C_ %s ) )' % (A0, PP, E, CP if PP == 'P' else CQ))], '3jca',
                    '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D /\\ ( %s e. CC /\\ %s C_ %s ) ) )' % (A0, E, PP, E, CP if PP == 'P' else CQ)), w.inst('qfcn')], 'syl',
               '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, QFP(E, PP), E))
cnPUP = qcn(PUP, 'P', pupd, pupc)
cnPUQ = qcn(PUQ, 'Q', puqd, puqc)
cnE2P = qcn(E2, 'P', e2d, e2cp)
cnE2Q = qcn(E2, 'Q', e2d, e2cq)
cnK = w.s([w.s([fcn, e2d, w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, E2, CP)),
                               w.s([qc, e2cq], 'jca', '( %s -> ( Q e. CC /\\ %s C_ %s ) )' % (A0, E2, CQ))], 'jca',
                              '( %s -> ( ( P e. CC /\\ %s C_ %s ) /\\ ( Q e. CC /\\ %s C_ %s ) ) )' % (A0, E2, CP, E2, CQ))], '3jca',
                '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D /\\ ( ( P e. CC /\\ %s C_ %s ) /\\ ( Q e. CC /\\ %s C_ %s ) ) ) )' % (A0, E2, E2, CP, E2, CQ)), w.inst('qf2cn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, KPQ(E2), E2))
exPUP = w.s([cnPUP, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, QFP(PUP, 'P')))
exPUQ = w.s([cnPUQ, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, QFP(PUQ, 'Q')))
exE2P = w.s([cnE2P, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, QFP(E2, 'P')))
exE2Q = w.s([cnE2Q, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, QFP(E2, 'Q')))


def qval(ante, E, PP, umem):
    """( ante -> ( QFP(E,PP) ` u ) = ( ( F ` u ) / ( u - PP ) ) )"""
    s1 = w.s([], 'fveq2', '( z = u -> ( F ` z ) = ( F ` u ) )')
    s2 = w.s([], 'oveq1', '( z = u -> ( z - %s ) = ( u - %s ) )' % (PP, PP))
    s3 = w.s([s1, s2], 'oveq12d', '( z = u -> ( ( F ` z ) / ( z - %s ) ) = ( ( F ` u ) / ( u - %s ) ) )' % (PP, PP))
    em = w.s([], 'eqid', '%s = %s' % (QFP(E, PP), QFP(E, PP)))
    fm = w.s([s3, em], 'fvmptg', '( ( u e. %s /\\ ( ( F ` u ) / ( u - %s ) ) e. _V ) -> ( %s ` u ) = ( ( F ` u ) / ( u - %s ) ) )' % (E, PP, QFP(E, PP), PP))
    return w.s([umem, ovexd(w, ante, '( ( F ` u ) / ( u - %s ) )' % PP), fm], 'syl2anc',
               '( %s -> ( %s ` u ) = ( ( F ` u ) / ( u - %s ) ) )' % (ante, QFP(E, PP), PP))


def kval(ante, umem):
    s1 = w.s([], 'fveq2', '( z = u -> ( F ` z ) = ( F ` u ) )')
    s2 = w.s([], 'oveq1', '( z = u -> ( z - P ) = ( u - P ) )')
    s2b = w.s([], 'oveq1', '( z = u -> ( z - Q ) = ( u - Q ) )')
    sm = w.s([s2, s2b], 'oveq12d', '( z = u -> ( ( z - P ) x. ( z - Q ) ) = ( ( u - P ) x. ( u - Q ) ) )')
    s3 = w.s([s1, sm], 'oveq12d', '( z = u -> ( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) ) = ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) )')
    em = w.s([], 'eqid', '%s = %s' % (KPQ(E2), KPQ(E2)))
    fm = w.s([s3, em], 'fvmptg', '( ( u e. %s /\\ ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) e. _V ) -> ( %s ` u ) = ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) )' % (E2, KPQ(E2)))
    return w.s([umem, ovexd(w, ante, '( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) )'), fm], 'syl2anc',
               '( %s -> ( %s ` u ) = ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) )' % (ante, KPQ(E2)))


# the frame identities moving PUP and PUQ integrands to E2
def moveeq(E, PP, ssFR, exBig, exE2, cnBig):
    um = w.s([], 'simpr', '( %s -> u e. %s )' % (AFR, FR))
    ub = w.s([w.s([ssFR], 'adantr', '( %s -> %s C_ %s )' % (AFR, FR, PUP if PP == 'P' else PUQ)), um], 'sseldd', '( %s -> u e. %s )' % (AFR, PUP if PP == 'P' else PUQ))
    u2 = w.s([w.s([fr2], 'adantr', '( %s -> %s C_ %s )' % (AFR, FR, E2)), um], 'sseldd', '( %s -> u e. %s )' % (AFR, E2))
    v1 = qval(AFR, PUP if PP == 'P' else PUQ, PP, ub)
    v2 = qval(AFR, E2, PP, u2)
    al = w.s([w.s([v1, v2], 'eqtr4d', '( %s -> ( %s ` u ) = ( %s ` u ) )' % (AFR, QFP(PUP if PP == 'P' else PUQ, PP), QFP(E2, PP)))], 'ralrimiva',
             '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, FR, QFP(PUP if PP == 'P' else PUQ, PP), QFP(E2, PP)))
    h = w.s([w.s([ab, closed(w, A0, 'ssid', '%s C_ %s' % (FR, FR))], 'jca', '( %s -> ( %s /\\ %s C_ %s ) )' % (A0, AB, FR, FR)),
             w.s([exBig, exE2], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A0, QFP(PUP if PP == 'P' else PUQ, PP), QFP(E2, PP))), al], '3jca',
            '( %s -> ( ( %s /\\ %s C_ %s ) /\\ ( %s e. _V /\\ %s e. _V ) /\\ A. u e. %s ( %s ` u ) = ( %s ` u ) ) )' % (
                A0, AB, FR, FR, QFP(PUP if PP == 'P' else PUQ, PP), QFP(E2, PP), FR, QFP(PUP if PP == 'P' else PUQ, PP), QFP(E2, PP)))
    return w.s([h, w.inst('rectinteqe')], 'syl', '( %s -> %s = %s )' % (A0, RINT(QFP(PUP if PP == 'P' else PUQ, PP), 'A', 'B'), RINT(QFP(E2, PP), 'A', 'B')))


eqP = moveeq(PUP, 'P', frp, exPUP, exE2P, cnPUP)
eqQ = moveeq(PUQ, 'Q', frq, exPUQ, exE2Q, cnPUQ)
cauP = w.s([w.s([ab, it, holo], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INT, HOLO)), w.inst('rectintcau')], 'syl',
           '( %s -> %s = ( %s x. ( F ` P ) ) )' % (A0, RINT(QFP(PUP, 'P'), 'A', 'B'), TPI))
cauQ = w.s([w.s([ab, itq, holo], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTQ, HOLO)), w.inst('rectintcau')], 'syl',
           '( %s -> %s = ( %s x. ( F ` Q ) ) )' % (A0, RINT(QFP(PUQ, 'Q'), 'A', 'B'), TPI))
# the pointwise splitting on E2
um2 = w.s([], 'simpr', '( %s -> u e. %s )' % (A1, E2))
ud = w.s([w.s([e2d], 'adantr', '( %s -> %s C_ D )' % (A1, E2)), um2], 'sseldd', '( %s -> u e. D )' % A1)
fu = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), ud], 'ffvelcdmd', '( %s -> ( F ` u ) e. CC )' % A1)
ucp = w.s([w.s([e2cp], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CP)), um2], 'sseldd', '( %s -> u e. %s )' % (A1, CP))
ucq = w.s([w.s([e2cq], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CQ)), um2], 'sseldd', '( %s -> u e. %s )' % (A1, CQ))
uc = w.s([w.s([ucp, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= P ) )' % A1), w.inst('simpl')], 'syl', '( %s -> u e. CC )' % A1)
unp = w.s([w.s([ucp, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> u =/= P )' % A1)
unq = w.s([w.s([ucq, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= Q ) )' % A1), w.inst('simpr')], 'syl', '( %s -> u =/= Q )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
qc1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1)
upn = w.s([uc, pc1, unp], 'subne0d', '( %s -> ( u - P ) =/= 0 )' % A1)
uqn = w.s([uc, qc1, unq], 'subne0d', '( %s -> ( u - Q ) =/= 0 )' % A1)
dsp = w.s([w.s([w.s([fu, pc1, qc1], '3jca', '( %s -> ( ( F ` u ) e. CC /\\ P e. CC /\\ Q e. CC ) )' % A1),
                w.s([uc, upn, uqn], '3jca', '( %s -> ( u e. CC /\\ ( u - P ) =/= 0 /\\ ( u - Q ) =/= 0 ) )' % A1)], 'jca',
               '( %s -> ( ( ( F ` u ) e. CC /\\ P e. CC /\\ Q e. CC ) /\\ ( u e. CC /\\ ( u - P ) =/= 0 /\\ ( u - Q ) =/= 0 ) ) )' % A1), w.inst('divsubpq')], 'syl',
           '( %s -> ( ( F ` u ) / ( u - P ) ) = ( ( ( P - Q ) x. ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) ) + ( ( F ` u ) / ( u - Q ) ) ) )' % A1)
vP = qval(A1, E2, 'P', um2)
vQ = qval(A1, E2, 'Q', um2)
vK = kval(A1, um2)
ptw = w.s([w.s([vP, dsp], 'eqtrd', '( %s -> ( %s ` u ) = ( ( ( P - Q ) x. ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) ) + ( ( F ` u ) / ( u - Q ) ) ) )' % (A1, QFP(E2, 'P'))),
           w.s([w.s([vK], 'oveq2d', '( %s -> ( ( P - Q ) x. ( %s ` u ) ) = ( ( P - Q ) x. ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) ) )' % (A1, KPQ(E2))), vQ], 'oveq12d',
               '( %s -> ( ( ( P - Q ) x. ( %s ` u ) ) + ( %s ` u ) ) = ( ( ( P - Q ) x. ( ( F ` u ) / ( ( u - P ) x. ( u - Q ) ) ) ) + ( ( F ` u ) / ( u - Q ) ) ) )' % (A1, KPQ(E2), QFP(E2, 'Q')))],
          'eqtr4d', '( %s -> ( %s ` u ) = ( ( ( P - Q ) x. ( %s ` u ) ) + ( %s ` u ) ) )' % (A1, QFP(E2, 'P'), KPQ(E2), QFP(E2, 'Q')))
alw = w.s([ptw], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( ( ( P - Q ) x. ( %s ` u ) ) + ( %s ` u ) ) )' % (A0, E2, QFP(E2, 'P'), KPQ(E2), QFP(E2, 'Q')))
pqc = w.s([pc, qc], 'subcld', '( %s -> ( P - Q ) e. CC )' % A0)
lce = w.s([w.s([w.s([ab, fr2], 'jca', '( %s -> ( %s /\\ %s C_ %s ) )' % (A0, AB, FR, E2)),
                w.s([exE2P, pqc, w.s([cnK, cnE2Q, closed(w, A0, 'ssid', '%s C_ %s' % (E2, E2))], '3jca',
                                      '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, KPQ(E2), E2, QFP(E2, 'Q'), E2, E2, E2))], '3jca',
                     '( %s -> ( %s e. _V /\\ ( P - Q ) e. CC /\\ ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) )' % (A0, QFP(E2, 'P'), KPQ(E2), E2, QFP(E2, 'Q'), E2, E2, E2)), alw], '3jca',
               '( %s -> ( ( %s /\\ %s C_ %s ) /\\ ( %s e. _V /\\ ( P - Q ) e. CC /\\ ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) /\\ A. u e. %s ( %s ` u ) = ( ( ( P - Q ) x. ( %s ` u ) ) + ( %s ` u ) ) ) )' % (
                   A0, AB, FR, E2, QFP(E2, 'P'), KPQ(E2), E2, QFP(E2, 'Q'), E2, E2, E2, E2, QFP(E2, 'P'), KPQ(E2), QFP(E2, 'Q'))), w.inst('rectintlce')], 'syl',
           '( %s -> %s = ( ( ( P - Q ) x. %s ) + %s ) )' % (A0, RINT(QFP(E2, 'P'), 'A', 'B'), RINT(KPQ(E2), 'A', 'B'), RINT(QFP(E2, 'Q'), 'A', 'B')))
# assemble
lhs = w.s([w.s([cauP], 'eqcomd', '( %s -> ( %s x. ( F ` P ) ) = %s )' % (A0, TPI, RINT(QFP(PUP, 'P'), 'A', 'B'))),
           w.s([eqP, lce], 'eqtrd', '( %s -> %s = ( ( ( P - Q ) x. %s ) + %s ) )' % (A0, RINT(QFP(PUP, 'P'), 'A', 'B'), RINT(KPQ(E2), 'A', 'B'), RINT(QFP(E2, 'Q'), 'A', 'B')))], 'eqtrd',
          '( %s -> ( %s x. ( F ` P ) ) = ( ( ( P - Q ) x. %s ) + %s ) )' % (A0, TPI, RINT(KPQ(E2), 'A', 'B'), RINT(QFP(E2, 'Q'), 'A', 'B')))
rq2 = w.s([w.s([eqQ], 'eqcomd', '( %s -> %s = %s )' % (A0, RINT(QFP(E2, 'Q'), 'A', 'B'), RINT(QFP(PUQ, 'Q'), 'A', 'B'))), cauQ], 'eqtrd',
          '( %s -> %s = ( %s x. ( F ` Q ) ) )' % (A0, RINT(QFP(E2, 'Q'), 'A', 'B'), TPI))
step = w.s([lhs, w.s([rq2], 'oveq2d', '( %s -> ( ( ( P - Q ) x. %s ) + %s ) = ( ( ( P - Q ) x. %s ) + ( %s x. ( F ` P ) ) ) )' % (A0, RINT(KPQ(E2), 'A', 'B'), RINT(QFP(E2, 'Q'), 'A', 'B'), RINT(KPQ(E2), 'A', 'B'), TPI)) if False else
            w.s([rq2], 'oveq2d', '( %s -> ( ( ( P - Q ) x. %s ) + %s ) = ( ( ( P - Q ) x. %s ) + ( %s x. ( F ` Q ) ) ) )' % (A0, RINT(KPQ(E2), 'A', 'B'), RINT(QFP(E2, 'Q'), 'A', 'B'), RINT(KPQ(E2), 'A', 'B'), TPI))], 'eqtrd',
           '( %s -> ( %s x. ( F ` P ) ) = ( ( ( P - Q ) x. %s ) + ( %s x. ( F ` Q ) ) ) )' % (A0, TPI, RINT(KPQ(E2), 'A', 'B'), TPI))
pmem = w.s([w.s([ab, it], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INT)), w.inst('crectinp')], 'syl', '( %s -> P e. ( A crect B ) )' % A0)
qmem = w.s([w.s([ab, itq], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTQ)), w.inst('crectinp')], 'syl', '( %s -> Q e. ( A crect B ) )' % A0)
fpc = w.s([ff, w.s([crd, pmem], 'sseldd', '( %s -> P e. D )' % A0)], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
fqc = w.s([ff, w.s([crd, qmem], 'sseldd', '( %s -> Q e. D )' % A0)], 'ffvelcdmd', '( %s -> ( F ` Q ) e. CC )' % A0)
tpic = w.s([closed(w, A0, '2cn', '2 e. CC'), w.s([closed(w, A0, 'ax-icn', '_i e. CC'), closed(w, A0, 'picn', '_pi e. CC')], 'mulcld', '( %s -> ( _i x. _pi ) e. CC )' % A0)],
           'mulcld', '( %s -> %s e. CC )' % (A0, TPI))
kcl = w.s([w.s([ab, w.s([cnK, fr2], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, KPQ(E2), E2, FR, E2))], 'jca',
                '( %s -> ( %s /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) )' % (A0, AB, KPQ(E2), E2, FR, E2)), w.inst('rectintcle')], 'syl',
           '( %s -> %s e. CC )' % (A0, RINT(KPQ(E2), 'A', 'B')))
pqk = w.s([pqc, kcl], 'mulcld', '( %s -> ( ( P - Q ) x. %s ) e. CC )' % (A0, RINT(KPQ(E2), 'A', 'B')))
tfq = w.s([tpic, fqc], 'mulcld', '( %s -> ( %s x. ( F ` Q ) ) e. CC )' % (A0, TPI))
sub = w.s([w.s([step], 'oveq1d', '( %s -> ( ( %s x. ( F ` P ) ) - ( %s x. ( F ` Q ) ) ) = ( ( ( ( P - Q ) x. %s ) + ( %s x. ( F ` Q ) ) ) - ( %s x. ( F ` Q ) ) ) )' % (A0, TPI, TPI, RINT(KPQ(E2), 'A', 'B'), TPI, TPI)),
           w.s([pqk, tfq], 'pncand', '( %s -> ( ( ( ( P - Q ) x. %s ) + ( %s x. ( F ` Q ) ) ) - ( %s x. ( F ` Q ) ) ) = ( ( P - Q ) x. %s ) )' % (A0, RINT(KPQ(E2), 'A', 'B'), TPI, TPI, RINT(KPQ(E2), 'A', 'B')))],
          'eqtrd', '( %s -> ( ( %s x. ( F ` P ) ) - ( %s x. ( F ` Q ) ) ) = ( ( P - Q ) x. %s ) )' % (A0, TPI, TPI, RINT(KPQ(E2), 'A', 'B')))
w.qed([w.s([tpic, fpc, fqc], 'subdid', '( %s -> ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) = ( ( %s x. ( F ` P ) ) - ( %s x. ( F ` Q ) ) ) )' % (A0, TPI, TPI, TPI)), sub],
      'eqtrd', '( %s -> ( %s x. ( ( F ` P ) - ( F ` Q ) ) ) = ( ( P - Q ) x. %s ) )' % (A0, TPI, RINT(KPQ(E2), 'A', 'B'))); run1(w)

# ---- rectintce2: the ML bound on the two-pole kernel -----------------------
RBDP = '( R e. RR /\\ ( ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) /\\ ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) ) )' % (RP, RA, RB, RP, IP, IA, IB, IP)
RBDQ = '( S e. RR /\\ ( ( S <_ ( %s - %s ) /\\ S <_ ( %s - %s ) ) /\\ ( S <_ ( %s - %s ) /\\ S <_ ( %s - %s ) ) ) )' % (RQ, RA, RB, RQ, IQ, IA, IB, IQ)
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
PER = '( ( %s - %s ) + ( %s - %s ) )' % (RB, RA, IB, IA)
w = W('rectintce2', 'The ML bound on the two-pole Cauchy kernel over the '
      'boundary of a rectangle with both poles strictly inside.')
A0 = '( ( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s ) /\\ ( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < S ) ) /\\ ( M e. RR /\\ %s ) )' % (
    AB, INT, INTQ, HOLO, RBDP, RBDQ, ALF)
A1 = '( %s /\\ v e. %s )' % (A0, FR)
bs = w.s([], 'simp1', '( %s -> ( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s ) )' % (A0, AB, INT, INTQ, HOLO))
rs = w.s([], 'simp2', '( %s -> ( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < S ) ) )' % (A0, RBDP, RBDQ))
mm = w.s([], 'simp3', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
rbp = w.s([w.s([rs, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP)), w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP))
rpos = w.s([w.s([rs, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP)), w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
rbq = w.s([w.s([rs, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ 0 < S ) )' % (A0, RBDQ)), w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDQ))
spos = w.s([w.s([rs, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ 0 < S ) )' % (A0, RBDQ)), w.inst('simpr')], 'syl', '( %s -> 0 < S )' % A0)
rr = w.s([rbp, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
sr = w.s([rbq, w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
Rrp = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
Srp = w.s([sr, spos], 'elrpd', '( %s -> S e. RR+ )' % A0)
RSrp = w.s([Rrp, Srp], 'rpmulcld', '( %s -> ( R x. S ) e. RR+ )' % A0)
mr = w.s([mm, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
alf = w.s([mm, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ALF))
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
tri = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INT, INTQ))
holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INT))
itq = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
qc = w.s([itq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
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
e2cp = w.s([crss, closed(w, A0, 'snsspr1', '{ P } C_ { P , Q }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CP))
e2cq = w.s([crss, closed(w, A0, 'snsspr2', '{ Q } C_ { P , Q }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CQ))
fr2 = w.s([w.s([ab, it, itq], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INT, INTQ)), w.inst('crectfrd')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, E2))
cnK = w.s([w.s([fcn, e2d, w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, E2, CP)),
                               w.s([qc, e2cq], 'jca', '( %s -> ( Q e. CC /\\ %s C_ %s ) )' % (A0, E2, CQ))], 'jca',
                              '( %s -> ( ( P e. CC /\\ %s C_ %s ) /\\ ( Q e. CC /\\ %s C_ %s ) ) )' % (A0, E2, CP, E2, CQ))], '3jca',
                '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D /\\ ( ( P e. CC /\\ %s C_ %s ) /\\ ( Q e. CC /\\ %s C_ %s ) ) ) )' % (A0, E2, E2, CP, E2, CQ)), w.inst('qf2cn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, KPQ(E2), E2))
pse = w.s([ab, geo, w.s([cnK, closed(w, A0, 'ssid', '%s C_ %s' % (FR, FR)), fr2], '3jca',
                        '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s ) )' % (A0, KPQ(E2), E2, FR, FR, FR, E2))], '3jca',
          '( %s -> ( %s /\\ %s /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s /\\ %s C_ %s ) ) )' % (A0, AB, GEO, KPQ(E2), E2, FR, FR, FR, E2))


def disv(rbd, PP, RV):
    d0 = w.s([w.s([ab, it if PP == 'P' else itq, rbd], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INT if PP == 'P' else INTQ, RBDP if PP == 'P' else RBDQ)), w.inst('crectdis')], 'syl',
             '( %s -> A. u e. %s %s <_ ( abs ` ( u - %s ) ) )' % (A0, FR, RV, PP))
    c1 = w.s([], 'oveq1', '( u = v -> ( u - %s ) = ( v - %s ) )' % (PP, PP))
    c2 = w.s([c1], 'fveq2d', '( u = v -> ( abs ` ( u - %s ) ) = ( abs ` ( v - %s ) ) )' % (PP, PP))
    c3 = w.s([c2], 'breq2d', '( u = v -> ( %s <_ ( abs ` ( u - %s ) ) <-> %s <_ ( abs ` ( v - %s ) ) ) )' % (RV, PP, RV, PP))
    return w.s([d0, w.s([c3], 'cbvralvw', '( A. u e. %s %s <_ ( abs ` ( u - %s ) ) <-> A. v e. %s %s <_ ( abs ` ( v - %s ) ) )' % (FR, RV, PP, FR, RV, PP))], 'sylib',
               '( %s -> A. v e. %s %s <_ ( abs ` ( v - %s ) ) )' % (A0, FR, RV, PP))


dP = disv(rbp, 'P', 'R')
dQ = disv(rbq, 'Q', 'S')
cc1 = w.s([], 'fveq2', '( u = v -> ( F ` u ) = ( F ` v ) )')
cc2 = w.s([cc1], 'fveq2d', '( u = v -> ( abs ` ( F ` u ) ) = ( abs ` ( F ` v ) ) )')
cc3 = w.s([cc2], 'breq1d', '( u = v -> ( ( abs ` ( F ` u ) ) <_ M <-> ( abs ` ( F ` v ) ) <_ M ) )')
alfv = w.s([alf, w.s([cc3], 'cbvralvw', '( %s <-> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (ALF, FR))], 'sylib', '( %s -> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (A0, FR))
vm = w.s([], 'simpr', '( %s -> v e. %s )' % (A1, FR))
rle = w.s([w.s([dP], 'adantr', '( %s -> A. v e. %s R <_ ( abs ` ( v - P ) ) )' % (A1, FR)), vm, w.inst('rspa')], 'syl2anc', '( %s -> R <_ ( abs ` ( v - P ) ) )' % A1)
sle = w.s([w.s([dQ], 'adantr', '( %s -> A. v e. %s S <_ ( abs ` ( v - Q ) ) )' % (A1, FR)), vm, w.inst('rspa')], 'syl2anc', '( %s -> S <_ ( abs ` ( v - Q ) ) )' % A1)
fle = w.s([w.s([alfv], 'adantr', '( %s -> A. v e. %s ( abs ` ( F ` v ) ) <_ M )' % (A1, FR)), vm, w.inst('rspa')], 'syl2anc', '( %s -> ( abs ` ( F ` v ) ) <_ M )' % A1)
v2 = w.s([w.s([fr2], 'adantr', '( %s -> %s C_ %s )' % (A1, FR, E2)), vm], 'sseldd', '( %s -> v e. %s )' % (A1, E2))
vd = w.s([w.s([e2d], 'adantr', '( %s -> %s C_ D )' % (A1, E2)), v2], 'sseldd', '( %s -> v e. D )' % A1)
fv_ = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), vd], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A1)
vcp = w.s([w.s([e2cp], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CP)), v2], 'sseldd', '( %s -> v e. %s )' % (A1, CP))
vcq = w.s([w.s([e2cq], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CQ)), v2], 'sseldd', '( %s -> v e. %s )' % (A1, CQ))
vc = w.s([w.s([vcp, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. CC /\\ v =/= P ) )' % A1), w.inst('simpl')], 'syl', '( %s -> v e. CC )' % A1)
vnp = w.s([w.s([vcp, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. CC /\\ v =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> v =/= P )' % A1)
vnq = w.s([w.s([vcq, w.inst('eldifsn')], 'sylib', '( %s -> ( v e. CC /\\ v =/= Q ) )' % A1), w.inst('simpr')], 'syl', '( %s -> v =/= Q )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
qc1 = w.s([qc], 'adantr', '( %s -> Q e. CC )' % A1)
vp = w.s([vc, pc1], 'subcld', '( %s -> ( v - P ) e. CC )' % A1)
vq = w.s([vc, qc1], 'subcld', '( %s -> ( v - Q ) e. CC )' % A1)
vpn = w.s([vc, pc1, vnp], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % A1)
vqn = w.s([vc, qc1, vnq], 'subne0d', '( %s -> ( v - Q ) =/= 0 )' % A1)
s1 = w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )')
s2 = w.s([], 'oveq1', '( z = v -> ( z - P ) = ( v - P ) )')
s2b = w.s([], 'oveq1', '( z = v -> ( z - Q ) = ( v - Q ) )')
sm = w.s([s2, s2b], 'oveq12d', '( z = v -> ( ( z - P ) x. ( z - Q ) ) = ( ( v - P ) x. ( v - Q ) ) )')
BV2 = '( ( F ` v ) / ( ( v - P ) x. ( v - Q ) ) )'
s3 = w.s([s1, sm], 'oveq12d', '( z = v -> ( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) ) = %s )' % BV2)
em = w.s([], 'eqid', '%s = %s' % (KPQ(E2), KPQ(E2)))
fm = w.s([s3, em], 'fvmptg', '( ( v e. %s /\\ %s e. _V ) -> ( %s ` v ) = %s )' % (E2, BV2, KPQ(E2), BV2))
kval2 = w.s([v2, ovexd(w, A1, BV2), fm], 'syl2anc', '( %s -> ( %s ` v ) = %s )' % (A1, KPQ(E2), BV2))
absq = w.s([fv_, w.s([vp, vq], 'mulcld', '( %s -> ( ( v - P ) x. ( v - Q ) ) e. CC )' % A1), w.s([vp, vq, vpn, vqn], 'mulne0d', '( %s -> ( ( v - P ) x. ( v - Q ) ) =/= 0 )' % A1)], 'absdivd',
           '( %s -> ( abs ` %s ) = ( ( abs ` ( F ` v ) ) / ( abs ` ( ( v - P ) x. ( v - Q ) ) ) ) )' % (A1, BV2))
absm = w.s([vp, vq], 'absmuld', '( %s -> ( abs ` ( ( v - P ) x. ( v - Q ) ) ) = ( ( abs ` ( v - P ) ) x. ( abs ` ( v - Q ) ) ) )' % A1)
avp = w.s([vp], 'abscld', '( %s -> ( abs ` ( v - P ) ) e. RR )' % A1)
avq = w.s([vq], 'abscld', '( %s -> ( abs ` ( v - Q ) ) e. RR )' % A1)
rr1 = w.s([rr], 'adantr', '( %s -> R e. RR )' % A1)
sr1 = w.s([sr], 'adantr', '( %s -> S e. RR )' % A1)
rge = w.s([w.s([rr1], 'id', '( %s -> R e. RR )' % A1)], 'id', '') if False else w.s([w.s([rpos], 'adantr', '( %s -> 0 < R )' % A1)], 'ltled', '( %s -> 0 <_ R )' % A1)
sge = w.s([w.s([spos], 'adantr', '( %s -> 0 < S )' % A1)], 'ltled', '( %s -> 0 <_ S )' % A1)
prod = w.s([rr1, avp, sr1, avq, rle, sle], 'lemul12ad', '( %s -> ( R x. S ) <_ ( ( abs ` ( v - P ) ) x. ( abs ` ( v - Q ) ) ) )' % A1)
prod2 = w.s([prod, w.s([absm], 'eqcomd', '( %s -> ( ( abs ` ( v - P ) ) x. ( abs ` ( v - Q ) ) ) = ( abs ` ( ( v - P ) x. ( v - Q ) ) ) )' % A1)], 'breqtrd',
            '( %s -> ( R x. S ) <_ ( abs ` ( ( v - P ) x. ( v - Q ) ) ) )' % A1)
ld = w.s([w.s([fv_], 'abscld', '( %s -> ( abs ` ( F ` v ) ) e. RR )' % A1), w.s([mr], 'adantr', '( %s -> M e. RR )' % A1), w.s([RSrp], 'adantr', '( %s -> ( R x. S ) e. RR+ )' % A1),
          w.s([w.s([vp, vq], 'mulcld', '( %s -> ( ( v - P ) x. ( v - Q ) ) e. CC )' % A1)], 'abscld', '( %s -> ( abs ` ( ( v - P ) x. ( v - Q ) ) ) e. RR )' % A1),
          w.s([fv_], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A1), fle, prod2], 'lediv12ad',
         '( %s -> ( ( abs ` ( F ` v ) ) / ( abs ` ( ( v - P ) x. ( v - Q ) ) ) ) <_ ( M / ( R x. S ) ) )' % A1)
pw = w.s([w.s([w.s([kval2], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` %s ) )' % (A1, KPQ(E2), BV2)), absq], 'eqtrd',
               '( %s -> ( abs ` ( %s ` v ) ) = ( ( abs ` ( F ` v ) ) / ( abs ` ( ( v - P ) x. ( v - Q ) ) ) ) )' % (A1, KPQ(E2))), ld], 'eqbrtrd',
         '( %s -> ( abs ` ( %s ` v ) ) <_ ( M / ( R x. S ) ) )' % (A1, KPQ(E2)))
allv = w.s([pw], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ ( M / ( R x. S ) ) )' % (A0, FR, KPQ(E2)))
w.qed([pse, w.s([mr, RSrp], 'rerpdivcld', '( %s -> ( M / ( R x. S ) ) e. RR )' % A0), allv, w.inst('rectintabse')], 'syl3anc',
      '( %s -> ( abs ` %s ) <_ ( ( 2 x. ( M / ( R x. S ) ) ) x. %s ) )' % (A0, RINT(KPQ(E2), 'A', 'B'), PER)); run1(w)
