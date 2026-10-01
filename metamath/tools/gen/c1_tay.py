"""Sortie C1 section 7: the Taylor expansion of a holomorphic function on a
rectangle, and with it analyticity and the local identity theorem."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c1_lib import *

DDD = '( W - P )'; EEE = '( W - Z )'; ZP = '( Z - P )'
XX = '( %s / %s )' % (ZP, DDD)

# ---- divgeo1: one step of the finite geometric expansion -------------------
w = W('divgeo1', 'One step of the finite geometric expansion of the Cauchy '
      'kernel: the remainder of order N splits off the N-th Taylor term.')
A0 = '( ( V e. CC /\\ N e. NN0 ) /\\ ( W e. CC /\\ P e. CC /\\ Z e. CC ) /\\ ( %s =/= 0 /\\ %s =/= 0 ) )' % (DDD, EEE)
XN = '( %s ^ N )' % XX; XN1 = '( %s ^ ( N + 1 ) )' % XX
LHS = '( ( V x. %s ) / %s )' % (XN, EEE)
RHS2 = '( ( V x. %s ) / %s )' % (XN1, EEE)
TGT1 = '( ( %s ^ N ) x. ( V / ( %s ^ ( N + 1 ) ) ) )' % (ZP, DDD)
vc = w.s([w.s([], 'simp1', '( %s -> ( V e. CC /\\ N e. NN0 ) )' % A0), w.inst('simpl')], 'syl', '( %s -> V e. CC )' % A0)
nn = w.s([w.s([], 'simp1', '( %s -> ( V e. CC /\\ N e. NN0 ) )' % A0), w.inst('simpr')], 'syl', '( %s -> N e. NN0 )' % A0)
wc = w.s([w.s([], 'simp2', '( %s -> ( W e. CC /\\ P e. CC /\\ Z e. CC ) )' % A0), w.inst('simp1')], 'syl', '( %s -> W e. CC )' % A0)
pc = w.s([w.s([], 'simp2', '( %s -> ( W e. CC /\\ P e. CC /\\ Z e. CC ) )' % A0), w.inst('simp2')], 'syl', '( %s -> P e. CC )' % A0)
zc = w.s([w.s([], 'simp2', '( %s -> ( W e. CC /\\ P e. CC /\\ Z e. CC ) )' % A0), w.inst('simp3')], 'syl', '( %s -> Z e. CC )' % A0)
dn = w.s([w.s([], 'simp3', '( %s -> ( %s =/= 0 /\\ %s =/= 0 ) )' % (A0, DDD, EEE)), w.inst('simpl')], 'syl', '( %s -> %s =/= 0 )' % (A0, DDD))
en = w.s([w.s([], 'simp3', '( %s -> ( %s =/= 0 /\\ %s =/= 0 ) )' % (A0, DDD, EEE)), w.inst('simpr')], 'syl', '( %s -> %s =/= 0 )' % (A0, EEE))
dc = w.s([wc, pc], 'subcld', '( %s -> %s e. CC )' % (A0, DDD))
ec = w.s([wc, zc], 'subcld', '( %s -> %s e. CC )' % (A0, EEE))
zpc = w.s([zc, pc], 'subcld', '( %s -> %s e. CC )' % (A0, ZP))
xc = w.s([zpc, dc, dn], 'divcld', '( %s -> %s e. CC )' % (A0, XX))
xnc = w.s([xc, nn], 'expcld', '( %s -> %s e. CC )' % (A0, XN))
nz = w.s([nn], 'nn0zd', '( %s -> N e. ZZ )' % A0)
dnn = w.s([dc, dn, nz, w.inst('expne0i')], 'syl3anc', '( %s -> ( %s ^ N ) =/= 0 )' % (A0, DDD))
dnc = w.s([dc, nn], 'expcld', '( %s -> ( %s ^ N ) e. CC )' % (A0, DDD))
zpnc = w.s([zpc, nn], 'expcld', '( %s -> ( %s ^ N ) e. CC )' % (A0, ZP))
n1 = w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
d1c = w.s([dc, n1], 'expcld', '( %s -> ( %s ^ ( N + 1 ) ) e. CC )' % (A0, DDD))
d1e = w.s([dc, nn], 'expp1d', '( %s -> ( %s ^ ( N + 1 ) ) = ( ( %s ^ N ) x. %s ) )' % (A0, DDD, DDD, DDD))
d1n = w.s([d1e, w.s([dnc, dc, dnn, dn], 'mulne0d', '( %s -> ( ( %s ^ N ) x. %s ) =/= 0 )' % (A0, DDD, DDD))], 'eqnetrd', '( %s -> ( %s ^ ( N + 1 ) ) =/= 0 )' % (A0, DDD))
vxn = w.s([vc, xnc], 'mulcld', '( %s -> ( V x. %s ) e. CC )' % (A0, XN))
xn1c = w.s([xnc, xc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A0, XN, XX))
xp1 = w.s([xc, nn], 'expp1d', '( %s -> %s = ( %s x. %s ) )' % (A0, XN1, XN, XX))
vxn1 = w.s([vc, w.s([xc, n1], 'expcld', '( %s -> %s e. CC )' % (A0, XN1))], 'mulcld',
           '( %s -> ( V x. %s ) e. CC )' % (A0, XN1))
# LHS - RHS2 = ( num / E )
sd = w.s([w.s([vxn, vxn1, ec, en], 'divsubdird', '( %s -> ( ( ( V x. %s ) - ( V x. %s ) ) / %s ) = ( %s - %s ) )' % (A0, XN, XN1, EEE, LHS, RHS2))], 'eqcomd',
         '( %s -> ( %s - %s ) = ( ( ( V x. %s ) - ( V x. %s ) ) / %s ) )' % (A0, LHS, RHS2, XN, XN1, EEE))
nm1 = w.s([w.s([vc, xnc, w.s([xc, n1], 'expcld', '( %s -> %s e. CC )' % (A0, XN1))], 'subdid',
                '( %s -> ( V x. ( %s - %s ) ) = ( ( V x. %s ) - ( V x. %s ) ) )' % (A0, XN, XN1, XN, XN1))], 'eqcomd',
          '( %s -> ( ( V x. %s ) - ( V x. %s ) ) = ( V x. ( %s - %s ) ) )' % (A0, XN, XN1, XN, XN1))
oneX = w.s([w.s([w.s([dc, dn], 'dividd', '( %s -> ( %s / %s ) = 1 )' % (A0, DDD, DDD))], 'eqcomd', '( %s -> 1 = ( %s / %s ) )' % (A0, DDD, DDD))], 'oveq1d',
           '( %s -> ( 1 - %s ) = ( ( %s / %s ) - %s ) )' % (A0, XX, DDD, DDD, XX))
oneX2 = w.s([w.s([dc, zpc, dc, dn], 'divsubdird', '( %s -> ( ( %s - %s ) / %s ) = ( ( %s / %s ) - %s ) )' % (A0, DDD, ZP, DDD, DDD, DDD, XX))], 'eqcomd',
            '( %s -> ( ( %s / %s ) - %s ) = ( ( %s - %s ) / %s ) )' % (A0, DDD, DDD, XX, DDD, ZP, DDD))
oneX3 = w.s([w.s([wc, zc, pc], 'nnncan2d', '( %s -> ( %s - %s ) = %s )' % (A0, DDD, ZP, EEE))], 'oveq1d',
            '( %s -> ( ( %s - %s ) / %s ) = ( %s / %s ) )' % (A0, DDD, ZP, DDD, EEE, DDD))
oneXf = w.s([w.s([oneX, oneX2], 'eqtrd', '( %s -> ( 1 - %s ) = ( ( %s - %s ) / %s ) )' % (A0, XX, DDD, ZP, DDD)), oneX3], 'eqtrd',
            '( %s -> ( 1 - %s ) = ( %s / %s ) )' % (A0, XX, EEE, DDD))
sub1 = w.s([w.s([xnc, closed(w, A0, 'ax-1cn', '1 e. CC'), xc], 'subdid',
                '( %s -> ( %s x. ( 1 - %s ) ) = ( ( %s x. 1 ) - ( %s x. %s ) ) )' % (A0, XN, XX, XN, XN, XX)),
            w.s([w.s([xnc], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A0, XN, XN))], 'oveq1d',
                '( %s -> ( ( %s x. 1 ) - ( %s x. %s ) ) = ( %s - ( %s x. %s ) ) )' % (A0, XN, XN, XX, XN, XN, XX))], 'eqtrd',
           '( %s -> ( %s x. ( 1 - %s ) ) = ( %s - ( %s x. %s ) ) )' % (A0, XN, XX, XN, XN, XX))
diffx = w.s([w.s([w.s([xp1], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - ( %s x. %s ) ) )' % (A0, XN, XN1, XN, XN, XX))], 'eqcomd',
                 '( %s -> ( %s - ( %s x. %s ) ) = ( %s - %s ) )' % (A0, XN, XN, XX, XN, XN1))], 'id', '') if False else \
    w.s([xp1], 'oveq2d', '( %s -> ( %s - %s ) = ( %s - ( %s x. %s ) ) )' % (A0, XN, XN1, XN, XN, XX))
xdif = w.s([diffx, w.s([sub1], 'eqcomd', '( %s -> ( %s - ( %s x. %s ) ) = ( %s x. ( 1 - %s ) ) )' % (A0, XN, XN, XX, XN, XX))], 'eqtrd',
           '( %s -> ( %s - %s ) = ( %s x. ( 1 - %s ) ) )' % (A0, XN, XN1, XN, XX))
xdif2 = w.s([xdif, w.s([oneXf], 'oveq2d', '( %s -> ( %s x. ( 1 - %s ) ) = ( %s x. ( %s / %s ) ) )' % (A0, XN, XX, XN, EEE, DDD))], 'eqtrd',
            '( %s -> ( %s - %s ) = ( %s x. ( %s / %s ) ) )' % (A0, XN, XN1, XN, EEE, DDD))
num = w.s([nm1, w.s([xdif2], 'oveq2d', '( %s -> ( V x. ( %s - %s ) ) = ( V x. ( %s x. ( %s / %s ) ) ) )' % (A0, XN, XN1, XN, EEE, DDD))], 'eqtrd',
          '( %s -> ( ( V x. %s ) - ( V x. %s ) ) = ( V x. ( %s x. ( %s / %s ) ) ) )' % (A0, XN, XN1, XN, EEE, DDD))
edc = w.s([ec, dc, dn], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, EEE, DDD))
r1 = w.s([w.s([vc, xnc, edc], 'mulassd', '( %s -> ( ( V x. %s ) x. ( %s / %s ) ) = ( V x. ( %s x. ( %s / %s ) ) ) )' % (A0, XN, EEE, DDD, XN, EEE, DDD))], 'eqcomd',
         '( %s -> ( V x. ( %s x. ( %s / %s ) ) ) = ( ( V x. %s ) x. ( %s / %s ) ) )' % (A0, XN, EEE, DDD, XN, EEE, DDD))
r2 = w.s([w.s([vxn, ec, dc, dn], 'divassd', '( %s -> ( ( ( V x. %s ) x. %s ) / %s ) = ( ( V x. %s ) x. ( %s / %s ) ) )' % (A0, XN, EEE, DDD, XN, EEE, DDD))], 'eqcomd',
         '( %s -> ( ( V x. %s ) x. ( %s / %s ) ) = ( ( ( V x. %s ) x. %s ) / %s ) )' % (A0, XN, EEE, DDD, XN, EEE, DDD))
r3 = w.s([w.s([vxn, ec], 'mulcld', '( %s -> ( ( V x. %s ) x. %s ) e. CC )' % (A0, XN, EEE)), dc, ec, dn, en], 'divdiv1d',
         '( %s -> ( ( ( ( V x. %s ) x. %s ) / %s ) / %s ) = ( ( ( V x. %s ) x. %s ) / ( %s x. %s ) ) )' % (A0, XN, EEE, DDD, EEE, XN, EEE, DDD, EEE))
r4 = w.s([vxn, dc, ec, dn, en], 'divcan5rd', '( %s -> ( ( ( V x. %s ) x. %s ) / ( %s x. %s ) ) = ( ( V x. %s ) / %s ) )' % (A0, XN, EEE, DDD, EEE, XN, DDD))
chain1 = w.s([w.s([sd, w.s([num], 'oveq1d', '( %s -> ( ( ( V x. %s ) - ( V x. %s ) ) / %s ) = ( ( V x. ( %s x. ( %s / %s ) ) ) / %s ) )' % (A0, XN, XN1, EEE, XN, EEE, DDD, EEE))], 'eqtrd',
                  '( %s -> ( %s - %s ) = ( ( V x. ( %s x. ( %s / %s ) ) ) / %s ) )' % (A0, LHS, RHS2, XN, EEE, DDD, EEE)),
              w.s([w.s([w.s([r1, r2], 'eqtrd', '( %s -> ( V x. ( %s x. ( %s / %s ) ) ) = ( ( ( V x. %s ) x. %s ) / %s ) )' % (A0, XN, EEE, DDD, XN, EEE, DDD))], 'oveq1d',
                       '( %s -> ( ( V x. ( %s x. ( %s / %s ) ) ) / %s ) = ( ( ( ( V x. %s ) x. %s ) / %s ) / %s ) )' % (A0, XN, EEE, DDD, EEE, XN, EEE, DDD, EEE)),
                   w.s([r3, r4], 'eqtrd', '( %s -> ( ( ( ( V x. %s ) x. %s ) / %s ) / %s ) = ( ( V x. %s ) / %s ) )' % (A0, XN, EEE, DDD, EEE, XN, DDD))], 'eqtrd',
                  '( %s -> ( ( V x. ( %s x. ( %s / %s ) ) ) / %s ) = ( ( V x. %s ) / %s ) )' % (A0, XN, EEE, DDD, EEE, XN, DDD))], 'eqtrd',
             '( %s -> ( %s - %s ) = ( ( V x. %s ) / %s ) )' % (A0, LHS, RHS2, XN, DDD))
# ( V x. X^N ) / D = ( ZP^N ) x. ( V / D^(N+1) )
q1 = w.s([w.s([zpc, dc, nn, dn, w.inst('expdivd')], 'syl' if False else 'id', '')], 'id', '') if False else \
    w.s([zpc, dc, dn, nn], 'expdivd', '( %s -> %s = ( ( %s ^ N ) / ( %s ^ N ) ) )' % (A0, XN, ZP, DDD))
q2 = w.s([w.s([q1], 'oveq2d', '( %s -> ( V x. %s ) = ( V x. ( ( %s ^ N ) / ( %s ^ N ) ) ) )' % (A0, XN, ZP, DDD)),
          w.s([w.s([vc, zpnc, dnc, dnn], 'divassd', '( %s -> ( ( V x. ( %s ^ N ) ) / ( %s ^ N ) ) = ( V x. ( ( %s ^ N ) / ( %s ^ N ) ) ) )' % (A0, ZP, DDD, ZP, DDD))], 'eqcomd',
              '( %s -> ( V x. ( ( %s ^ N ) / ( %s ^ N ) ) ) = ( ( V x. ( %s ^ N ) ) / ( %s ^ N ) ) )' % (A0, ZP, DDD, ZP, DDD))], 'eqtrd',
         '( %s -> ( V x. %s ) = ( ( V x. ( %s ^ N ) ) / ( %s ^ N ) ) )' % (A0, XN, ZP, DDD))
q3 = w.s([w.s([vc, zpnc], 'mulcld', '( %s -> ( V x. ( %s ^ N ) ) e. CC )' % (A0, ZP)), dnc, dc, dnn, dn], 'divdiv1d',
         '( %s -> ( ( ( V x. ( %s ^ N ) ) / ( %s ^ N ) ) / %s ) = ( ( V x. ( %s ^ N ) ) / ( ( %s ^ N ) x. %s ) ) )' % (A0, ZP, DDD, DDD, ZP, DDD, DDD))
q4 = w.s([w.s([d1e], 'eqcomd', '( %s -> ( ( %s ^ N ) x. %s ) = ( %s ^ ( N + 1 ) ) )' % (A0, DDD, DDD, DDD))], 'oveq2d',
         '( %s -> ( ( V x. ( %s ^ N ) ) / ( ( %s ^ N ) x. %s ) ) = ( ( V x. ( %s ^ N ) ) / ( %s ^ ( N + 1 ) ) ) )' % (A0, ZP, DDD, DDD, ZP, DDD))
q5 = w.s([w.s([w.s([vc, zpnc], 'mulcomd', '( %s -> ( V x. ( %s ^ N ) ) = ( ( %s ^ N ) x. V ) )' % (A0, ZP, ZP))], 'oveq1d',
              '( %s -> ( ( V x. ( %s ^ N ) ) / ( %s ^ ( N + 1 ) ) ) = ( ( ( %s ^ N ) x. V ) / ( %s ^ ( N + 1 ) ) ) )' % (A0, ZP, DDD, ZP, DDD)),
          w.s([zpnc, vc, d1c, d1n], 'divassd', '( %s -> ( ( ( %s ^ N ) x. V ) / ( %s ^ ( N + 1 ) ) ) = %s )' % (A0, ZP, DDD, TGT1))], 'eqtrd',
         '( %s -> ( ( V x. ( %s ^ N ) ) / ( %s ^ ( N + 1 ) ) ) = %s )' % (A0, ZP, DDD, TGT1))
qf = w.s([w.s([w.s([q2], 'oveq1d', '( %s -> ( ( V x. %s ) / %s ) = ( ( ( V x. ( %s ^ N ) ) / ( %s ^ N ) ) / %s ) )' % (A0, XN, DDD, ZP, DDD, DDD)),
               w.s([q3, q4], 'eqtrd', '( %s -> ( ( ( V x. ( %s ^ N ) ) / ( %s ^ N ) ) / %s ) = ( ( V x. ( %s ^ N ) ) / ( %s ^ ( N + 1 ) ) ) )' % (A0, ZP, DDD, DDD, ZP, DDD))], 'eqtrd',
              '( %s -> ( ( V x. %s ) / %s ) = ( ( V x. ( %s ^ N ) ) / ( %s ^ ( N + 1 ) ) ) )' % (A0, XN, DDD, ZP, DDD)), q5], 'eqtrd',
         '( %s -> ( ( V x. %s ) / %s ) = %s )' % (A0, XN, DDD, TGT1))
fin = w.s([chain1, qf], 'eqtrd', '( %s -> ( %s - %s ) = %s )' % (A0, LHS, RHS2, TGT1))
lhsc = w.s([vxn, ec, en], 'divcld', '( %s -> %s e. CC )' % (A0, LHS))
r2c = w.s([vxn1, ec, en], 'divcld', '( %s -> %s e. CC )' % (A0, RHS2))
t1c = w.s([zpnc, w.s([vc, d1c, d1n], 'divcld', '( %s -> ( V / ( %s ^ ( N + 1 ) ) ) e. CC )' % (A0, DDD))], 'mulcld', '( %s -> %s e. CC )' % (A0, TGT1))
w.qed([w.s([fin, w.s([lhsc, r2c, t1c], 'subadd2d', '( %s -> ( ( %s - %s ) = %s <-> ( %s + %s ) = %s ) )' % (A0, LHS, RHS2, TGT1, TGT1, RHS2, LHS))], 'mpbid',
            '( %s -> ( %s + %s ) = %s )' % (A0, TGT1, RHS2, LHS))], 'eqcomd',
      '( %s -> %s = ( %s + %s ) )' % (A0, LHS, TGT1, RHS2)); run1(w)

# ---- cncfexpb: a power of a continuous mapping is continuous ---------------
w = W('cncfexpb', 'A nonnegative integer power of a continuous complex mapping '
      'is continuous.')
A0 = '( ( y e. E |-> S ) e. ( E -cn-> CC ) /\\ M e. NN0 )'
hab = w.s([], 'simpl', '( %s -> ( y e. E |-> S ) e. ( E -cn-> CC ) )' % A0)
hm = w.s([], 'simpr', '( %s -> M e. NN0 )' % A0)
n1 = w.s([], 'nfmpt1', 'F/_ y ( y e. E |-> S )')
n2 = w.s([], 'nfcv', 'F/_ y ( E -cn-> CC )')
n3 = w.s([n1, n2], 'nfel', 'F/ y ( y e. E |-> S ) e. ( E -cn-> CC )')
n4 = w.s([], 'nfv', 'F/ y M e. NN0')
nf = w.s([n3, n4], 'nfan', 'F/ y %s' % A0)
ex = w.s([hm, w.inst('expcncf')], 'syl', '( %s -> ( v e. CC |-> ( v ^ M ) ) e. ( CC -cn-> CC ) )' % A0)
bc = closed(w, A0, 'ssid', 'CC C_ CC')
st = w.s([], 'oveq1', '( v = S -> ( v ^ M ) = ( S ^ M ) )')
w.qed([nf, hab, ex, bc, st], 'cncfcompt2', '( %s -> ( y e. E |-> ( S ^ M ) ) e. ( E -cn-> CC ) )' % A0); run1(w)

# ---- cfcn: continuity of the Taylor coefficient integrand ------------------
w = W('cfcn', 'The N-th Cauchy coefficient kernel of a continuous function is '
      'continuous off the pole.')
CPP = '( CC \\ { P } )'
A0 = '( ( F e. ( D -cn-> CC ) /\\ E C_ D ) /\\ ( P e. CC /\\ E C_ %s ) /\\ M e. NN0 )' % CPP
A1 = '( %s /\\ y e. E )' % A0
fcn = w.s([w.s([], 'simp1', '( %s -> ( F e. ( D -cn-> CC ) /\\ E C_ D ) )' % A0), w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ed = w.s([w.s([], 'simp1', '( %s -> ( F e. ( D -cn-> CC ) /\\ E C_ D ) )' % A0), w.inst('simpr')], 'syl', '( %s -> E C_ D )' % A0)
pp = w.s([], 'simp2', '( %s -> ( P e. CC /\\ E C_ %s ) )' % (A0, CPP))
pc = w.s([pp, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ecp = w.s([pp, w.inst('simpr')], 'syl', '( %s -> E C_ %s )' % (A0, CPP))
hm = w.s([], 'simp3', '( %s -> M e. NN0 )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
res = w.s([ed, fcn, w.inst('rescncf')], 'sylc', '( %s -> ( F |` E ) e. ( E -cn-> CC ) )' % A0)
fmp = w.s([w.s([ff, ed], 'feqresmpt', '( %s -> ( F |` E ) = ( y e. E |-> ( F ` y ) ) )' % A0), res], 'eqeltrrd',
          '( %s -> ( y e. E |-> ( F ` y ) ) e. ( E -cn-> CC ) )' % A0)
rmp = w.s([pc, ecp, w.inst('rinvcnss')], 'syl2anc', '( %s -> ( z e. E |-> ( 1 / ( z - P ) ) ) e. ( E -cn-> CC ) )' % A0)
cb1 = w.s([], 'oveq1', '( z = y -> ( z - P ) = ( y - P ) )')
cb2 = w.s([cb1], 'oveq2d', '( z = y -> ( 1 / ( z - P ) ) = ( 1 / ( y - P ) ) )')
rmpy = w.s([rmp, w.s([cb2], 'cbvmptv', '( z e. E |-> ( 1 / ( z - P ) ) ) = ( y e. E |-> ( 1 / ( y - P ) ) )' )], 'eqeltrrd',
           '( %s -> ( y e. E |-> ( 1 / ( y - P ) ) ) e. ( E -cn-> CC ) )' % A0) if False else \
    w.s([w.s([w.s([cb2], 'cbvmptv', '( z e. E |-> ( 1 / ( z - P ) ) ) = ( y e. E |-> ( 1 / ( y - P ) ) )')], 'a1i',
             '( %s -> ( z e. E |-> ( 1 / ( z - P ) ) ) = ( y e. E |-> ( 1 / ( y - P ) ) ) )' % A0), rmp], 'eqeltrrd',
        '( %s -> ( y e. E |-> ( 1 / ( y - P ) ) ) e. ( E -cn-> CC ) )' % A0)
pw = w.s([rmpy, hm, w.inst('cncfexpb')], 'syl2anc', '( %s -> ( y e. E |-> ( ( 1 / ( y - P ) ) ^ M ) ) e. ( E -cn-> CC ) )' % A0)
prod = w.s([fmp, pw], 'mulcncf', '( %s -> ( y e. E |-> ( ( F ` y ) x. ( ( 1 / ( y - P ) ) ^ M ) ) ) e. ( E -cn-> CC ) )' % A0)
# the pointwise rewrite
yE = w.s([], 'simpr', '( %s -> y e. E )' % A1)
yd = w.s([w.s([ed], 'adantr', '( %s -> E C_ D )' % A1), yE], 'sseldd', '( %s -> y e. D )' % A1)
fy = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), yd], 'ffvelcdmd', '( %s -> ( F ` y ) e. CC )' % A1)
ycp = w.s([w.s([ecp], 'adantr', '( %s -> E C_ %s )' % (A1, CPP)), yE], 'sseldd', '( %s -> y e. %s )' % (A1, CPP))
ydf = w.s([ycp, w.inst('eldifsn')], 'sylib', '( %s -> ( y e. CC /\\ y =/= P ) )' % A1)
yc = w.s([ydf, w.inst('simpl')], 'syl', '( %s -> y e. CC )' % A1)
yn = w.s([ydf, w.inst('simpr')], 'syl', '( %s -> y =/= P )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
dcy = w.s([yc, pc1], 'subcld', '( %s -> ( y - P ) e. CC )' % A1)
dny = w.s([yc, pc1, yn], 'subne0d', '( %s -> ( y - P ) =/= 0 )' % A1)
hm1 = w.s([hm], 'adantr', '( %s -> M e. NN0 )' % A1)
dmc = w.s([dcy, hm1], 'expcld', '( %s -> ( ( y - P ) ^ M ) e. CC )' % A1)
dmn = w.s([dcy, dny, w.s([hm1], 'nn0zd', '( %s -> M e. ZZ )' % A1), w.inst('expne0i')], 'syl3anc', '( %s -> ( ( y - P ) ^ M ) =/= 0 )' % A1)
one = closed(w, A1, 'ax-1cn', '1 e. CC')
ed1 = w.s([one, dcy, dny, hm1], 'expdivd', '( %s -> ( ( 1 / ( y - P ) ) ^ M ) = ( ( 1 ^ M ) / ( ( y - P ) ^ M ) ) )' % A1)
e1x = w.s([w.s([w.s([hm1], 'nn0zd', '( %s -> M e. ZZ )' % A1), w.inst('1exp')], 'syl', '( %s -> ( 1 ^ M ) = 1 )' % A1)], 'oveq1d', '( %s -> ( ( 1 ^ M ) / ( ( y - P ) ^ M ) ) = ( 1 / ( ( y - P ) ^ M ) ) )' % A1)
rec = w.s([w.s([fy, dmc, dmn], 'divrecd', '( %s -> ( ( F ` y ) / ( ( y - P ) ^ M ) ) = ( ( F ` y ) x. ( 1 / ( ( y - P ) ^ M ) ) ) )' % A1)], 'eqcomd',
          '( %s -> ( ( F ` y ) x. ( 1 / ( ( y - P ) ^ M ) ) ) = ( ( F ` y ) / ( ( y - P ) ^ M ) ) )' % A1)
ptw = w.s([w.s([w.s([ed1, e1x], 'eqtrd', '( %s -> ( ( 1 / ( y - P ) ) ^ M ) = ( 1 / ( ( y - P ) ^ M ) ) )' % A1)], 'oveq2d',
                '( %s -> ( ( F ` y ) x. ( ( 1 / ( y - P ) ) ^ M ) ) = ( ( F ` y ) x. ( 1 / ( ( y - P ) ^ M ) ) ) )' % A1), rec], 'eqtrd',
          '( %s -> ( ( F ` y ) x. ( ( 1 / ( y - P ) ) ^ M ) ) = ( ( F ` y ) / ( ( y - P ) ^ M ) ) )' % A1)
mt = w.s([ptw], 'mpteq2dva', '( %s -> ( y e. E |-> ( ( F ` y ) x. ( ( 1 / ( y - P ) ) ^ M ) ) ) = ( y e. E |-> ( ( F ` y ) / ( ( y - P ) ^ M ) ) ) )' % A0)
w.qed([mt, prod], 'eqeltrrd', '( %s -> ( y e. E |-> ( ( F ` y ) / ( ( y - P ) ^ M ) ) ) e. ( E -cn-> CC ) )' % A0); run1(w)

# ---- rmcn: continuity of the Taylor remainder integrand --------------------
w = W('rmcn', 'The Taylor remainder kernel of a continuous function is '
      'continuous off the centre and the evaluation point.')
CPP = '( CC \\ { P } )'; CZZ = '( CC \\ { Z } )'
XY = '( ( Z - P ) / ( y - P ) )'
A0 = '( ( F e. ( D -cn-> CC ) /\\ E C_ D ) /\\ ( ( P e. CC /\\ E C_ %s ) /\\ ( Z e. CC /\\ E C_ %s ) ) /\\ N e. NN0 )' % (CPP, CZZ)
A1 = '( %s /\\ y e. E )' % A0
fcn = w.s([w.s([], 'simp1', '( %s -> ( F e. ( D -cn-> CC ) /\\ E C_ D ) )' % A0), w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
ed = w.s([w.s([], 'simp1', '( %s -> ( F e. ( D -cn-> CC ) /\\ E C_ D ) )' % A0), w.inst('simpr')], 'syl', '( %s -> E C_ D )' % A0)
two = w.s([], 'simp2', '( %s -> ( ( P e. CC /\\ E C_ %s ) /\\ ( Z e. CC /\\ E C_ %s ) ) )' % (A0, CPP, CZZ))
pp = w.s([two, w.inst('simpl')], 'syl', '( %s -> ( P e. CC /\\ E C_ %s ) )' % (A0, CPP))
zz = w.s([two, w.inst('simpr')], 'syl', '( %s -> ( Z e. CC /\\ E C_ %s ) )' % (A0, CZZ))
pc = w.s([pp, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ecp = w.s([pp, w.inst('simpr')], 'syl', '( %s -> E C_ %s )' % (A0, CPP))
zc = w.s([zz, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
ecz = w.s([zz, w.inst('simpr')], 'syl', '( %s -> E C_ %s )' % (A0, CZZ))
hn = w.s([], 'simp3', '( %s -> N e. NN0 )' % A0)
ecc = w.s([ecp, closed(w, A0, 'difss', '%s C_ CC' % CPP)], 'sstrd', '( %s -> E C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
res = w.s([ed, fcn, w.inst('rescncf')], 'sylc', '( %s -> ( F |` E ) e. ( E -cn-> CC ) )' % A0)
fmp = w.s([w.s([ff, ed], 'feqresmpt', '( %s -> ( F |` E ) = ( y e. E |-> ( F ` y ) ) )' % A0), res], 'eqeltrrd',
          '( %s -> ( y e. E |-> ( F ` y ) ) e. ( E -cn-> CC ) )' % A0)


def invcn(PP, ecx):
    r = w.s([pc if PP == 'P' else zc, ecx, w.inst('rinvcnss')], 'syl2anc', '( %s -> ( z e. E |-> ( 1 / ( z - %s ) ) ) e. ( E -cn-> CC ) )' % (A0, PP))
    b1 = w.s([], 'oveq1', '( z = y -> ( z - %s ) = ( y - %s ) )' % (PP, PP))
    b2 = w.s([b1], 'oveq2d', '( z = y -> ( 1 / ( z - %s ) ) = ( 1 / ( y - %s ) ) )' % (PP, PP))
    cb = w.s([w.s([b2], 'cbvmptv', '( z e. E |-> ( 1 / ( z - %s ) ) ) = ( y e. E |-> ( 1 / ( y - %s ) ) )' % (PP, PP))], 'a1i',
             '( %s -> ( z e. E |-> ( 1 / ( z - %s ) ) ) = ( y e. E |-> ( 1 / ( y - %s ) ) ) )' % (A0, PP, PP))
    return w.s([cb, r], 'eqeltrrd', '( %s -> ( y e. E |-> ( 1 / ( y - %s ) ) ) e. ( E -cn-> CC ) )' % (A0, PP))


rp = invcn('P', ecp)
rz = invcn('Z', ecz)
zpc = w.s([zc, pc], 'subcld', '( %s -> ( Z - P ) e. CC )' % A0)
cst = w.s([zpc, ecc, closed(w, A0, 'ssid', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( %s -> ( y e. E |-> ( Z - P ) ) e. ( E -cn-> CC ) )' % A0)
pr1 = w.s([cst, rp], 'mulcncf', '( %s -> ( y e. E |-> ( ( Z - P ) x. ( 1 / ( y - P ) ) ) ) e. ( E -cn-> CC ) )' % A0)
# pointwise facts
yE = w.s([], 'simpr', '( %s -> y e. E )' % A1)
yd = w.s([w.s([ed], 'adantr', '( %s -> E C_ D )' % A1), yE], 'sseldd', '( %s -> y e. D )' % A1)
fy = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), yd], 'ffvelcdmd', '( %s -> ( F ` y ) e. CC )' % A1)
ycp = w.s([w.s([ecp], 'adantr', '( %s -> E C_ %s )' % (A1, CPP)), yE], 'sseldd', '( %s -> y e. %s )' % (A1, CPP))
ycz = w.s([w.s([ecz], 'adantr', '( %s -> E C_ %s )' % (A1, CZZ)), yE], 'sseldd', '( %s -> y e. %s )' % (A1, CZZ))
yc = w.s([w.s([ycp, w.inst('eldifsn')], 'sylib', '( %s -> ( y e. CC /\\ y =/= P ) )' % A1), w.inst('simpl')], 'syl', '( %s -> y e. CC )' % A1)
ynp = w.s([w.s([ycp, w.inst('eldifsn')], 'sylib', '( %s -> ( y e. CC /\\ y =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> y =/= P )' % A1)
ynz = w.s([w.s([ycz, w.inst('eldifsn')], 'sylib', '( %s -> ( y e. CC /\\ y =/= Z ) )' % A1), w.inst('simpr')], 'syl', '( %s -> y =/= Z )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
zc1 = w.s([zc], 'adantr', '( %s -> Z e. CC )' % A1)
yp = w.s([yc, pc1], 'subcld', '( %s -> ( y - P ) e. CC )' % A1)
yz = w.s([yc, zc1], 'subcld', '( %s -> ( y - Z ) e. CC )' % A1)
ypn = w.s([yc, pc1, ynp], 'subne0d', '( %s -> ( y - P ) =/= 0 )' % A1)
yzn = w.s([yc, zc1, ynz], 'subne0d', '( %s -> ( y - Z ) =/= 0 )' % A1)
zpc1 = w.s([zpc], 'adantr', '( %s -> ( Z - P ) e. CC )' % A1)
dr1 = w.s([w.s([zpc1, yp, ypn], 'divrecd', '( %s -> %s = ( ( Z - P ) x. ( 1 / ( y - P ) ) ) )' % (A1, XY))], 'eqcomd',
          '( %s -> ( ( Z - P ) x. ( 1 / ( y - P ) ) ) = %s )' % (A1, XY))
xmp = w.s([w.s([dr1], 'mpteq2dva', '( %s -> ( y e. E |-> ( ( Z - P ) x. ( 1 / ( y - P ) ) ) ) = ( y e. E |-> %s ) )' % (A0, XY)), pr1], 'eqeltrrd',
          '( %s -> ( y e. E |-> %s ) e. ( E -cn-> CC ) )' % (A0, XY))
xpw = w.s([xmp, hn, w.inst('cncfexpb')], 'syl2anc', '( %s -> ( y e. E |-> ( %s ^ N ) ) e. ( E -cn-> CC ) )' % (A0, XY))
pr2 = w.s([fmp, xpw], 'mulcncf', '( %s -> ( y e. E |-> ( ( F ` y ) x. ( %s ^ N ) ) ) e. ( E -cn-> CC ) )' % (A0, XY))
pr3 = w.s([pr2, rz], 'mulcncf', '( %s -> ( y e. E |-> ( ( ( F ` y ) x. ( %s ^ N ) ) x. ( 1 / ( y - Z ) ) ) ) e. ( E -cn-> CC ) )' % (A0, XY))
xnc = w.s([w.s([zpc1, yp, ypn], 'divcld', '( %s -> %s e. CC )' % (A1, XY)), w.s([hn], 'adantr', '( %s -> N e. NN0 )' % A1)], 'expcld', '( %s -> ( %s ^ N ) e. CC )' % (A1, XY))
dr2 = w.s([w.s([fy, xnc], 'mulcld', '( %s -> ( ( F ` y ) x. ( %s ^ N ) ) e. CC )' % (A1, XY)), yz, yzn], 'divrecd',
          '( %s -> ( ( ( F ` y ) x. ( %s ^ N ) ) / ( y - Z ) ) = ( ( ( F ` y ) x. ( %s ^ N ) ) x. ( 1 / ( y - Z ) ) ) )' % (A1, XY, XY))
mt = w.s([dr2], 'mpteq2dva', '( %s -> ( y e. E |-> ( ( ( F ` y ) x. ( %s ^ N ) ) / ( y - Z ) ) ) = ( y e. E |-> ( ( ( F ` y ) x. ( %s ^ N ) ) x. ( 1 / ( y - Z ) ) ) ) )' % (A0, XY, XY))
w.qed([mt, pr3], 'eqeltrd', '( %s -> ( y e. E |-> ( ( ( F ` y ) x. ( %s ^ N ) ) / ( y - Z ) ) ) e. ( E -cn-> CC ) )' % (A0, XY)); run1(w)

# ---- rectintrm: one step of the Taylor recursion ---------------------------
RPP = RE('P'); IPP = IM('P'); RZZ = RE('Z'); IZZ = IM('Z')
INTP = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RPP, RPP, RB, IA, IPP, IPP, IB)
INTZ = '( Z e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RZZ, RZZ, RB, IA, IZZ, IZZ, IB)
HOLO = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) )'
CPP = '( CC \\ { P } )'; CZZ = '( CC \\ { Z } )'
PUP = '( ( A crect B ) \\ { P } )'
E2 = '( ( A crect B ) \\ { P , Z } )'
XY = '( ( Z - P ) / ( y - P ) )'
XU = '( ( Z - P ) / ( u - P ) )'
BASE = '( %s /\\ ( %s /\\ %s /\\ P =/= Z ) /\\ %s )' % (AB, INTP, INTZ, HOLO)


def CFM(E, M):
    return '( y e. %s |-> ( ( F ` y ) / ( ( y - P ) ^ %s ) ) )' % (E, M)


def RM(E, M):
    return '( y e. %s |-> ( ( ( F ` y ) x. ( %s ^ %s ) ) / ( y - Z ) ) )' % (E, XY, M)


w = W('rectintrm', 'One step of the Taylor recursion for a holomorphic function '
      'on a rectangle: the remainder of order N is the N-th term plus the '
      'remainder of order N + 1.')
A0 = '( %s /\\ N e. NN0 )' % BASE
A1 = '( %s /\\ u e. %s )' % (A0, E2)
AFR = '( %s /\\ u e. %s )' % (A0, FR)
NP1 = '( N + 1 )'
bs = w.s([], 'simpl', '( %s -> %s )' % (A0, BASE))
hn = w.s([], 'simpr', '( %s -> N e. NN0 )' % A0)
hn1 = w.s([hn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (A0, NP1))
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
tri = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (A0, INTP, INTZ))
holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
itz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTZ))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
zc = w.s([itz, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
dvb = w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
crd = w.s([hss, dvb], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
e2d = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, E2))
pupd = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, PUP))
pupc = w.s([crss], 'ssdifd', '( %s -> %s C_ %s )' % (A0, PUP, CPP))
e2cp = w.s([crss, closed(w, A0, 'snsspr1', '{ P } C_ { P , Z }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CPP))
e2cz = w.s([crss, closed(w, A0, 'snsspr2', '{ Z } C_ { P , Z }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CZZ))
frp = w.s([w.s([ab, it], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTP)), w.inst('crectfrp')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, PUP))
fr2 = w.s([w.s([ab, it, itz], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, INTZ)), w.inst('crectfrd')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, E2))
fd = w.s([fcn, e2d], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, E2))
ppz = w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, E2, CPP)),
           w.s([zc, e2cz], 'jca', '( %s -> ( Z e. CC /\\ %s C_ %s ) )' % (A0, E2, CZZ))], 'jca',
          '( %s -> ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) )' % (A0, E2, CPP, E2, CZZ))
cnR = w.s([w.s([fd, ppz, hn], '3jca', '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) /\\ N e. NN0 ) )' % (A0, E2, E2, CPP, E2, CZZ)), w.inst('rmcn')], 'syl',
          '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RM(E2, 'N'), E2))
cnR1 = w.s([w.s([fd, ppz, hn1], '3jca', '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) /\\ %s e. NN0 ) )' % (A0, E2, E2, CPP, E2, CZZ, NP1)), w.inst('rmcn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RM(E2, NP1), E2))
cnCE = w.s([w.s([fd, w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, E2, CPP)), hn1], '3jca',
                '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( P e. CC /\\ %s C_ %s ) /\\ %s e. NN0 ) )' % (A0, E2, E2, CPP, NP1)), w.inst('cfcn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, CFM(E2, NP1), E2))
cnCP = w.s([w.s([w.s([fcn, pupd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, PUP)), w.s([pc, pupc], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, PUP, CPP)), hn1], '3jca',
                '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( P e. CC /\\ %s C_ %s ) /\\ %s e. NN0 ) )' % (A0, PUP, PUP, CPP, NP1)), w.inst('cfcn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, CFM(PUP, NP1), PUP))


def fvR(ante, M, umem):
    body_u = '( ( ( F ` u ) x. ( %s ^ %s ) ) / ( u - Z ) )' % (XU, M)
    s1 = w.s([], 'fveq2', '( y = u -> ( F ` y ) = ( F ` u ) )')
    s2 = w.s([], 'oveq1', '( y = u -> ( y - P ) = ( u - P ) )')
    s3 = w.s([s2], 'oveq2d', '( y = u -> %s = %s )' % (XY, XU))
    s4 = w.s([s3], 'oveq1d', '( y = u -> ( %s ^ %s ) = ( %s ^ %s ) )' % (XY, M, XU, M))
    s5 = w.s([s1, s4], 'oveq12d', '( y = u -> ( ( F ` y ) x. ( %s ^ %s ) ) = ( ( F ` u ) x. ( %s ^ %s ) ) )' % (XY, M, XU, M))
    s6 = w.s([], 'oveq1', '( y = u -> ( y - Z ) = ( u - Z ) )')
    s7 = w.s([s5, s6], 'oveq12d', '( y = u -> ( ( ( F ` y ) x. ( %s ^ %s ) ) / ( y - Z ) ) = %s )' % (XY, M, body_u))
    em = w.s([], 'eqid', '%s = %s' % (RM(E2, M), RM(E2, M)))
    fm = w.s([s7, em], 'fvmptg', '( ( u e. %s /\\ %s e. _V ) -> ( %s ` u ) = %s )' % (E2, body_u, RM(E2, M), body_u))
    return w.s([umem, ovexd(w, ante, body_u), fm], 'syl2anc', '( %s -> ( %s ` u ) = %s )' % (ante, RM(E2, M), body_u))


def fvC(ante, E, M, umem):
    body_u = '( ( F ` u ) / ( ( u - P ) ^ %s ) )' % M
    s1 = w.s([], 'fveq2', '( y = u -> ( F ` y ) = ( F ` u ) )')
    s2 = w.s([], 'oveq1', '( y = u -> ( y - P ) = ( u - P ) )')
    s3 = w.s([s2], 'oveq1d', '( y = u -> ( ( y - P ) ^ %s ) = ( ( u - P ) ^ %s ) )' % (M, M))
    s4 = w.s([s1, s3], 'oveq12d', '( y = u -> ( ( F ` y ) / ( ( y - P ) ^ %s ) ) = %s )' % (M, body_u))
    em = w.s([], 'eqid', '%s = %s' % (CFM(E, M), CFM(E, M)))
    fm = w.s([s4, em], 'fvmptg', '( ( u e. %s /\\ %s e. _V ) -> ( %s ` u ) = %s )' % (E, body_u, CFM(E, M), body_u))
    return w.s([umem, ovexd(w, ante, body_u), fm], 'syl2anc', '( %s -> ( %s ` u ) = %s )' % (ante, CFM(E, M), body_u))


# the pointwise identity on E2
um2 = w.s([], 'simpr', '( %s -> u e. %s )' % (A1, E2))
ud = w.s([w.s([e2d], 'adantr', '( %s -> %s C_ D )' % (A1, E2)), um2], 'sseldd', '( %s -> u e. D )' % A1)
fu = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), ud], 'ffvelcdmd', '( %s -> ( F ` u ) e. CC )' % A1)
ucp = w.s([w.s([e2cp], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CPP)), um2], 'sseldd', '( %s -> u e. %s )' % (A1, CPP))
ucz = w.s([w.s([e2cz], 'adantr', '( %s -> %s C_ %s )' % (A1, E2, CZZ)), um2], 'sseldd', '( %s -> u e. %s )' % (A1, CZZ))
uc = w.s([w.s([ucp, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= P ) )' % A1), w.inst('simpl')], 'syl', '( %s -> u e. CC )' % A1)
unp = w.s([w.s([ucp, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> u =/= P )' % A1)
unz = w.s([w.s([ucz, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= Z ) )' % A1), w.inst('simpr')], 'syl', '( %s -> u =/= Z )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
zc1 = w.s([zc], 'adantr', '( %s -> Z e. CC )' % A1)
upn = w.s([uc, pc1, unp], 'subne0d', '( %s -> ( u - P ) =/= 0 )' % A1)
uzn = w.s([uc, zc1, unz], 'subne0d', '( %s -> ( u - Z ) =/= 0 )' % A1)
dg = w.s([w.s([w.s([fu, w.s([hn], 'adantr', '( %s -> N e. NN0 )' % A1)], 'jca', '( %s -> ( ( F ` u ) e. CC /\\ N e. NN0 ) )' % A1),
               w.s([uc, pc1, zc1], '3jca', '( %s -> ( u e. CC /\\ P e. CC /\\ Z e. CC ) )' % A1),
               w.s([upn, uzn], 'jca', '( %s -> ( ( u - P ) =/= 0 /\\ ( u - Z ) =/= 0 ) )' % A1)], '3jca',
              '( %s -> ( ( ( F ` u ) e. CC /\\ N e. NN0 ) /\\ ( u e. CC /\\ P e. CC /\\ Z e. CC ) /\\ ( ( u - P ) =/= 0 /\\ ( u - Z ) =/= 0 ) ) )' % A1), w.inst('divgeo1')], 'syl',
         '( %s -> ( ( ( F ` u ) x. ( %s ^ N ) ) / ( u - Z ) ) = ( ( ( ( Z - P ) ^ N ) x. ( ( F ` u ) / ( ( u - P ) ^ %s ) ) ) + ( ( ( F ` u ) x. ( %s ^ %s ) ) / ( u - Z ) ) ) )' % (A1, XU, NP1, XU, NP1))
vR = fvR(A1, 'N', um2)
vR1 = fvR(A1, NP1, um2)
vC = fvC(A1, E2, NP1, um2)
ptw = w.s([w.s([vR, dg], 'eqtrd', '( %s -> ( %s ` u ) = ( ( ( ( Z - P ) ^ N ) x. ( ( F ` u ) / ( ( u - P ) ^ %s ) ) ) + ( ( ( F ` u ) x. ( %s ^ %s ) ) / ( u - Z ) ) ) )' % (A1, RM(E2, 'N'), NP1, XU, NP1)),
           w.s([w.s([vC], 'oveq2d', '( %s -> ( ( ( Z - P ) ^ N ) x. ( %s ` u ) ) = ( ( ( Z - P ) ^ N ) x. ( ( F ` u ) / ( ( u - P ) ^ %s ) ) ) )' % (A1, CFM(E2, NP1), NP1)), vR1], 'oveq12d',
               '( %s -> ( ( ( ( Z - P ) ^ N ) x. ( %s ` u ) ) + ( %s ` u ) ) = ( ( ( ( Z - P ) ^ N ) x. ( ( F ` u ) / ( ( u - P ) ^ %s ) ) ) + ( ( ( F ` u ) x. ( %s ^ %s ) ) / ( u - Z ) ) ) )' % (A1, CFM(E2, NP1), RM(E2, NP1), NP1, XU, NP1))],
          'eqtr4d', '( %s -> ( %s ` u ) = ( ( ( ( Z - P ) ^ N ) x. ( %s ` u ) ) + ( %s ` u ) ) )' % (A1, RM(E2, 'N'), CFM(E2, NP1), RM(E2, NP1)))
alw = w.s([ptw], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( ( ( ( Z - P ) ^ N ) x. ( %s ` u ) ) + ( %s ` u ) ) )' % (A0, E2, RM(E2, 'N'), CFM(E2, NP1), RM(E2, NP1)))
exR = w.s([cnR, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, RM(E2, 'N')))
zpn = w.s([w.s([zc, pc], 'subcld', '( %s -> ( Z - P ) e. CC )' % A0), hn], 'expcld', '( %s -> ( ( Z - P ) ^ N ) e. CC )' % A0)
lce = w.s([w.s([w.s([ab, fr2], 'jca', '( %s -> ( %s /\\ %s C_ %s ) )' % (A0, AB, FR, E2)),
                w.s([exR, zpn, w.s([cnCE, cnR1, closed(w, A0, 'ssid', '%s C_ %s' % (E2, E2))], '3jca',
                                    '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, CFM(E2, NP1), E2, RM(E2, NP1), E2, E2, E2))], '3jca',
                     '( %s -> ( %s e. _V /\\ ( ( Z - P ) ^ N ) e. CC /\\ ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) )' % (A0, RM(E2, 'N'), CFM(E2, NP1), E2, RM(E2, NP1), E2, E2, E2)), alw], '3jca',
               '( %s -> ( ( %s /\\ %s C_ %s ) /\\ ( %s e. _V /\\ ( ( Z - P ) ^ N ) e. CC /\\ ( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) /\\ A. u e. %s ( %s ` u ) = ( ( ( ( Z - P ) ^ N ) x. ( %s ` u ) ) + ( %s ` u ) ) ) )' % (
                   A0, AB, FR, E2, RM(E2, 'N'), CFM(E2, NP1), E2, RM(E2, NP1), E2, E2, E2, E2, RM(E2, 'N'), CFM(E2, NP1), RM(E2, NP1))), w.inst('rectintlce')], 'syl',
           '( %s -> %s = ( ( ( ( Z - P ) ^ N ) x. %s ) + %s ) )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'), RINT(CFM(E2, NP1), 'A', 'B'), RINT(RM(E2, NP1), 'A', 'B')))
# move the coefficient integrand from E2 back to the singly punctured rectangle
umf = w.s([], 'simpr', '( %s -> u e. %s )' % (AFR, FR))
ufp = w.s([w.s([frp], 'adantr', '( %s -> %s C_ %s )' % (AFR, FR, PUP)), umf], 'sseldd', '( %s -> u e. %s )' % (AFR, PUP))
uf2 = w.s([w.s([fr2], 'adantr', '( %s -> %s C_ %s )' % (AFR, FR, E2)), umf], 'sseldd', '( %s -> u e. %s )' % (AFR, E2))
alC = w.s([w.s([fvC(AFR, E2, NP1, uf2), fvC(AFR, PUP, NP1, ufp)], 'eqtr4d', '( %s -> ( %s ` u ) = ( %s ` u ) )' % (AFR, CFM(E2, NP1), CFM(PUP, NP1)))], 'ralrimiva',
          '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, FR, CFM(E2, NP1), CFM(PUP, NP1)))
eqC = w.s([w.s([w.s([ab, closed(w, A0, 'ssid', '%s C_ %s' % (FR, FR))], 'jca', '( %s -> ( %s /\\ %s C_ %s ) )' % (A0, AB, FR, FR)),
                w.s([w.s([cnCE, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, CFM(E2, NP1))), w.s([cnCP, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, CFM(PUP, NP1)))], 'jca',
                    '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A0, CFM(E2, NP1), CFM(PUP, NP1))), alC], '3jca',
               '( %s -> ( ( %s /\\ %s C_ %s ) /\\ ( %s e. _V /\\ %s e. _V ) /\\ A. u e. %s ( %s ` u ) = ( %s ` u ) ) )' % (A0, AB, FR, FR, CFM(E2, NP1), CFM(PUP, NP1), FR, CFM(E2, NP1), CFM(PUP, NP1))), w.inst('rectinteqe')], 'syl',
          '( %s -> %s = %s )' % (A0, RINT(CFM(E2, NP1), 'A', 'B'), RINT(CFM(PUP, NP1), 'A', 'B')))
w.qed([lce, w.s([w.s([eqC], 'oveq2d', '( %s -> ( ( ( Z - P ) ^ N ) x. %s ) = ( ( ( Z - P ) ^ N ) x. %s ) )' % (A0, RINT(CFM(E2, NP1), 'A', 'B'), RINT(CFM(PUP, NP1), 'A', 'B')))], 'oveq1d',
                '( %s -> ( ( ( ( Z - P ) ^ N ) x. %s ) + %s ) = ( ( ( ( Z - P ) ^ N ) x. %s ) + %s ) )' % (A0, RINT(CFM(E2, NP1), 'A', 'B'), RINT(RM(E2, NP1), 'A', 'B'), RINT(CFM(PUP, NP1), 'A', 'B'), RINT(RM(E2, NP1), 'A', 'B')))],
      'eqtrd', '( %s -> %s = ( ( ( ( Z - P ) ^ N ) x. %s ) + %s ) )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'), RINT(CFM(PUP, NP1), 'A', 'B'), RINT(RM(E2, NP1), 'A', 'B'))); run1(w)

# ---- rectintw0: the remainder of order zero is the Cauchy integral ---------
PUZ = '( ( A crect B ) \\ { Z } )'
TPI = '( 2 x. ( _i x. _pi ) )'
QZ = '( y e. %s |-> ( ( F ` y ) / ( y - Z ) ) )' % PUZ
w = W('rectintw0', 'The Taylor remainder of order zero is the Cauchy integral, '
      'hence 2 pi i times the value at the evaluation point.')
A0 = BASE
AFR = '( %s /\\ u e. %s )' % (A0, FR)
ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
tri = w.s([], 'simp2', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (A0, INTP, INTZ))
holo = w.s([], 'simp3', '( %s -> %s )' % (A0, HOLO))
it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
itz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTZ))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
zc = w.s([itz, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
dvb = w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
crd = w.s([hss, dvb], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
e2d = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, E2))
puzd = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, PUZ))
puzc = w.s([crss], 'ssdifd', '( %s -> %s C_ %s )' % (A0, PUZ, CZZ))
e2cp = w.s([crss, closed(w, A0, 'snsspr1', '{ P } C_ { P , Z }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CPP))
e2cz = w.s([crss, closed(w, A0, 'snsspr2', '{ Z } C_ { P , Z }')], 'ssdif2d', '( %s -> %s C_ %s )' % (A0, E2, CZZ))
frz = w.s([w.s([ab, itz], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTZ)), w.inst('crectfrp')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, PUZ))
fr2 = w.s([w.s([ab, it, itz], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, INTZ)), w.inst('crectfrd')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, E2))
z0 = closed(w, A0, '0nn0', '0 e. NN0')
cnR0 = w.s([w.s([w.s([fcn, e2d], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, E2)),
                 w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, E2, CPP)), w.s([zc, e2cz], 'jca', '( %s -> ( Z e. CC /\\ %s C_ %s ) )' % (A0, E2, CZZ))], 'jca',
                     '( %s -> ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) )' % (A0, E2, CPP, E2, CZZ)), z0], '3jca',
                '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) /\\ 0 e. NN0 ) )' % (A0, E2, E2, CPP, E2, CZZ)), w.inst('rmcn')], 'syl',
            '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RM(E2, '0'), E2))
cnQZ = w.s([w.s([fcn, puzd, w.s([zc, puzc], 'jca', '( %s -> ( Z e. CC /\\ %s C_ %s ) )' % (A0, PUZ, CZZ))], '3jca',
                '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D /\\ ( Z e. CC /\\ %s C_ %s ) ) )' % (A0, PUZ, PUZ, CZZ)), w.inst('qfcn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, QZ, PUZ))
cau = w.s([w.s([ab, itz, holo], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTZ, HOLO)), w.inst('rectintcau')], 'syl',
          '( %s -> %s = ( %s x. ( F ` Z ) ) )' % (A0, RINT(QZ, 'A', 'B'), TPI))
umf = w.s([], 'simpr', '( %s -> u e. %s )' % (AFR, FR))
uz = w.s([w.s([frz], 'adantr', '( %s -> %s C_ %s )' % (AFR, FR, PUZ)), umf], 'sseldd', '( %s -> u e. %s )' % (AFR, PUZ))
u2 = w.s([w.s([fr2], 'adantr', '( %s -> %s C_ %s )' % (AFR, FR, E2)), umf], 'sseldd', '( %s -> u e. %s )' % (AFR, E2))
vR0 = fvR(AFR, '0', u2)
s1 = w.s([], 'fveq2', '( y = u -> ( F ` y ) = ( F ` u ) )')
s2 = w.s([], 'oveq1', '( y = u -> ( y - Z ) = ( u - Z ) )')
s3 = w.s([s1, s2], 'oveq12d', '( y = u -> ( ( F ` y ) / ( y - Z ) ) = ( ( F ` u ) / ( u - Z ) ) )')
emz = w.s([], 'eqid', '%s = %s' % (QZ, QZ))
fmz = w.s([s3, emz], 'fvmptg', '( ( u e. %s /\\ ( ( F ` u ) / ( u - Z ) ) e. _V ) -> ( %s ` u ) = ( ( F ` u ) / ( u - Z ) ) )' % (PUZ, QZ))
vQ = w.s([uz, ovexd(w, AFR, '( ( F ` u ) / ( u - Z ) )'), fmz], 'syl2anc', '( %s -> ( %s ` u ) = ( ( F ` u ) / ( u - Z ) ) )' % (AFR, QZ))
ufd = w.s([w.s([e2d], 'adantr', '( %s -> %s C_ D )' % (AFR, E2)), u2], 'sseldd', '( %s -> u e. D )' % AFR)
fuu = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % AFR), ufd], 'ffvelcdmd', '( %s -> ( F ` u ) e. CC )' % AFR)
ucp = w.s([w.s([e2cp], 'adantr', '( %s -> %s C_ %s )' % (AFR, E2, CPP)), u2], 'sseldd', '( %s -> u e. %s )' % (AFR, CPP))
uc = w.s([w.s([ucp, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= P ) )' % AFR), w.inst('simpl')], 'syl', '( %s -> u e. CC )' % AFR)
unp = w.s([w.s([ucp, w.inst('eldifsn')], 'sylib', '( %s -> ( u e. CC /\\ u =/= P ) )' % AFR), w.inst('simpr')], 'syl', '( %s -> u =/= P )' % AFR)
pcf = w.s([pc], 'adantr', '( %s -> P e. CC )' % AFR)
zcf = w.s([zc], 'adantr', '( %s -> Z e. CC )' % AFR)
upn = w.s([uc, pcf, unp], 'subne0d', '( %s -> ( u - P ) =/= 0 )' % AFR)
xuc = w.s([w.s([zcf, pcf], 'subcld', '( %s -> ( Z - P ) e. CC )' % AFR), w.s([uc, pcf], 'subcld', '( %s -> ( u - P ) e. CC )' % AFR), upn], 'divcld', '( %s -> %s e. CC )' % (AFR, XU))
x0 = w.s([xuc, w.inst('exp0')], 'syl', '( %s -> ( %s ^ 0 ) = 1 )' % (AFR, XU))
num = w.s([w.s([x0], 'oveq2d', '( %s -> ( ( F ` u ) x. ( %s ^ 0 ) ) = ( ( F ` u ) x. 1 ) )' % (AFR, XU)), w.s([fuu], 'mulridd', '( %s -> ( ( F ` u ) x. 1 ) = ( F ` u ) )' % AFR)], 'eqtrd',
          '( %s -> ( ( F ` u ) x. ( %s ^ 0 ) ) = ( F ` u ) )' % (AFR, XU))
alF = w.s([w.s([w.s([vR0, w.s([num], 'oveq1d', '( %s -> ( ( ( F ` u ) x. ( %s ^ 0 ) ) / ( u - Z ) ) = ( ( F ` u ) / ( u - Z ) ) )' % (AFR, XU))], 'eqtrd',
                    '( %s -> ( %s ` u ) = ( ( F ` u ) / ( u - Z ) ) )' % (AFR, RM(E2, '0'))), vQ], 'eqtr4d', '( %s -> ( %s ` u ) = ( %s ` u ) )' % (AFR, RM(E2, '0'), QZ))], 'ralrimiva',
          '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, FR, RM(E2, '0'), QZ))
eqW = w.s([w.s([w.s([ab, closed(w, A0, 'ssid', '%s C_ %s' % (FR, FR))], 'jca', '( %s -> ( %s /\\ %s C_ %s ) )' % (A0, AB, FR, FR)),
                w.s([w.s([cnR0, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, RM(E2, '0'))), w.s([cnQZ, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A0, QZ))], 'jca',
                    '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A0, RM(E2, '0'), QZ)), alF], '3jca',
               '( %s -> ( ( %s /\\ %s C_ %s ) /\\ ( %s e. _V /\\ %s e. _V ) /\\ A. u e. %s ( %s ` u ) = ( %s ` u ) ) )' % (A0, AB, FR, FR, RM(E2, '0'), QZ, FR, RM(E2, '0'), QZ)), w.inst('rectinteqe')], 'syl',
          '( %s -> %s = %s )' % (A0, RINT(RM(E2, '0'), 'A', 'B'), RINT(QZ, 'A', 'B')))
w.qed([eqW, cau], 'eqtrd', '( %s -> %s = ( %s x. ( F ` Z ) ) )' % (A0, RINT(RM(E2, '0'), 'A', 'B'), TPI)); run1(w)

# ---- closures of the two boundary integrals --------------------------------
w = W('rectintccl', 'The Cauchy coefficient integral of a holomorphic function '
      'on a rectangle is a complex number.')
A0 = '( ( %s /\\ %s /\\ %s ) /\\ M e. NN0 )' % (AB, INTP, HOLO)
bs = w.s([], 'simpl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, HOLO))
hm = w.s([], 'simpr', '( %s -> M e. NN0 )' % A0)
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
it = w.s([bs, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTP))
holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
crd = w.s([hss, w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
pupd = w.s([crd], 'ssdifssd', '( %s -> %s C_ D )' % (A0, PUP))
pupc = w.s([crss], 'ssdifd', '( %s -> %s C_ %s )' % (A0, PUP, CPP))
frp = w.s([w.s([ab, it], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTP)), w.inst('crectfrp')], 'syl', '( %s -> %s C_ %s )' % (A0, FR, PUP))
cn = w.s([w.s([w.s([fcn, pupd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, PUP)), w.s([pc, pupc], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, PUP, CPP)), hm], '3jca',
              '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( P e. CC /\\ %s C_ %s ) /\\ M e. NN0 ) )' % (A0, PUP, PUP, CPP)), w.inst('cfcn')], 'syl',
         '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, CFM(PUP, 'M'), PUP))
w.qed([w.s([ab, w.s([cn, frp], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, CFM(PUP, 'M'), PUP, FR, PUP))], 'jca',
           '( %s -> ( %s /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) )' % (A0, AB, CFM(PUP, 'M'), PUP, FR, PUP)), w.inst('rectintcle')], 'syl',
      '( %s -> %s e. CC )' % (A0, RINT(CFM(PUP, 'M'), 'A', 'B'))); run1(w)

w = W('rectintrcl', 'The Taylor remainder integral of a holomorphic function on '
      'a rectangle is a complex number.')
A0 = '( %s /\\ N e. NN0 )' % BASE
bs = w.s([], 'simpl', '( %s -> %s )' % (A0, BASE))
hn = w.s([], 'simpr', '( %s -> N e. NN0 )' % A0)
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
tri = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (A0, INTP, INTZ))
holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
itz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTZ))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
zc = w.s([itz, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
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
cn = w.s([w.s([w.s([fcn, e2d], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, E2)),
               w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ %s ) )' % (A0, E2, CPP)), w.s([zc, e2cz], 'jca', '( %s -> ( Z e. CC /\\ %s C_ %s ) )' % (A0, E2, CZZ))], 'jca',
                   '( %s -> ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) )' % (A0, E2, CPP, E2, CZZ)), hn], '3jca',
              '( %s -> ( ( F e. ( D -cn-> CC ) /\\ %s C_ D ) /\\ ( ( P e. CC /\\ %s C_ %s ) /\\ ( Z e. CC /\\ %s C_ %s ) ) /\\ N e. NN0 ) )' % (A0, E2, E2, CPP, E2, CZZ)), w.inst('rmcn')], 'syl',
         '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RM(E2, 'N'), E2))
w.qed([w.s([ab, w.s([cn, fr2], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, RM(E2, 'N'), E2, FR, E2))], 'jca',
           '( %s -> ( %s /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) )' % (A0, AB, RM(E2, 'N'), E2, FR, E2)), w.inst('rectintcle')], 'syl',
      '( %s -> %s e. CC )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'))); run1(w)

# ---- rectinttay: the finite Taylor expansion with remainder ----------------
GDEF = 'G = ( n e. NN0 |-> %s )' % RINT(RM(E2, 'n'), 'A', 'B')
HDEF = 'H = ( j e. NN0 |-> ( ( ( Z - P ) ^ j ) x. %s ) )' % RINT(CFM(PUP, '( j + 1 )'), 'A', 'B')
LHS = '( %s x. ( F ` Z ) )' % TPI


def SUM(s):
    return 'sum_ k e. ( 0 ..^ %s ) ( H ` k )' % s


def RHS(s):
    return '( %s + ( G ` %s ) )' % (SUM(s), s)


def PHI(s):
    return '( %s -> %s = %s )' % (BASE, LHS, RHS(s))


w = W('rectinttay', 'The Taylor expansion with remainder of a holomorphic '
      'function on a rectangle: 2 pi i times the value at a strictly interior '
      'point Z is the first N Taylor terms about a strictly interior centre P '
      'plus the remainder integral of order N.')
hyp(w, '1', 'rectinttay.g', GDEF)
hyp(w, '2', 'rectinttay.h', HDEF)


def isub(sub):
    o = w.s([], 'oveq2', '( v = %s -> ( 0 ..^ v ) = ( 0 ..^ %s ) )' % (sub, sub))
    s = w.s([o], 'sumeq1d', '( v = %s -> %s = %s )' % (sub, SUM('v'), SUM(sub)))
    g = w.s([], 'fveq2', '( v = %s -> ( G ` v ) = ( G ` %s ) )' % (sub, sub))
    p = w.s([s, g], 'oveq12d', '( v = %s -> %s = %s )' % (sub, RHS('v'), RHS(sub)))
    e = w.s([p], 'eqeq2d', '( v = %s -> ( %s = %s <-> %s = %s ) )' % (sub, LHS, RHS('v'), LHS, RHS(sub)))
    return w.s([e], 'imbi2d', '( v = %s -> ( %s <-> %s ) )' % (sub, PHI('v'), PHI(sub)))


def gval(ante, K, kn):
    s1 = w.s([], 'oveq2', '( n = %s -> ( %s ^ n ) = ( %s ^ %s ) )' % (K, XY, XY, K))
    s2 = w.s([s1], 'oveq2d', '( n = %s -> ( ( F ` y ) x. ( %s ^ n ) ) = ( ( F ` y ) x. ( %s ^ %s ) ) )' % (K, XY, XY, K))
    s3 = w.s([s2], 'oveq1d', '( n = %s -> ( ( ( F ` y ) x. ( %s ^ n ) ) / ( y - Z ) ) = ( ( ( F ` y ) x. ( %s ^ %s ) ) / ( y - Z ) ) )' % (K, XY, XY, K))
    s4 = w.s([s3], 'mpteq2dv', '( n = %s -> %s = %s )' % (K, RM(E2, 'n'), RM(E2, K)))
    s5 = w.s([s4], 'oveq1d', '( n = %s -> %s = %s )' % (K, RINT(RM(E2, 'n'), 'A', 'B'), RINT(RM(E2, K), 'A', 'B')))
    fm = w.s([s5, '1'], 'fvmptg', '( ( %s e. NN0 /\\ %s e. _V ) -> ( G ` %s ) = %s )' % (K, RINT(RM(E2, K), 'A', 'B'), K, RINT(RM(E2, K), 'A', 'B')))
    return w.s([kn, ovexd(w, ante, RINT(RM(E2, K), 'A', 'B')), fm], 'syl2anc', '( %s -> ( G ` %s ) = %s )' % (ante, K, RINT(RM(E2, K), 'A', 'B')))


def HT(K):
    return '( ( ( Z - P ) ^ %s ) x. %s )' % (K, RINT(CFM(PUP, '( %s + 1 )' % K), 'A', 'B'))


def hval(ante, K, kn):
    s1 = w.s([], 'oveq2', '( j = %s -> ( ( Z - P ) ^ j ) = ( ( Z - P ) ^ %s ) )' % (K, K))
    s2 = w.s([], 'oveq1', '( j = %s -> ( j + 1 ) = ( %s + 1 ) )' % (K, K))
    s3 = w.s([s2], 'oveq2d', '( j = %s -> ( ( y - P ) ^ ( j + 1 ) ) = ( ( y - P ) ^ ( %s + 1 ) ) )' % (K, K))
    s4 = w.s([s3], 'oveq2d', '( j = %s -> ( ( F ` y ) / ( ( y - P ) ^ ( j + 1 ) ) ) = ( ( F ` y ) / ( ( y - P ) ^ ( %s + 1 ) ) ) )' % (K, K))
    s5 = w.s([s4], 'mpteq2dv', '( j = %s -> %s = %s )' % (K, CFM(PUP, '( j + 1 )'), CFM(PUP, '( %s + 1 )' % K)))
    s6 = w.s([s5], 'oveq1d', '( j = %s -> %s = %s )' % (K, RINT(CFM(PUP, '( j + 1 )'), 'A', 'B'), RINT(CFM(PUP, '( %s + 1 )' % K), 'A', 'B')))
    s7 = w.s([s1, s6], 'oveq12d', '( j = %s -> ( ( ( Z - P ) ^ j ) x. %s ) = %s )' % (K, RINT(CFM(PUP, '( j + 1 )'), 'A', 'B'), HT(K)))
    fm = w.s([s7, '2'], 'fvmptg', '( ( %s e. NN0 /\\ %s e. _V ) -> ( H ` %s ) = %s )' % (K, HT(K), K, HT(K)))
    return w.s([kn, ovexd(w, ante, HT(K)), fm], 'syl2anc', '( %s -> ( H ` %s ) = %s )' % (ante, K, HT(K)))


def hcl(ante, K, kn, bs):
    """( ante -> ( H ` K ) e. CC ) from kn: K e. NN0 and bs: BASE"""
    v = hval(ante, K, kn)
    ab_ = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (ante, AB))
    tri_ = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (ante, INTP, INTZ))
    it_ = w.s([tri_, w.inst('simp1')], 'syl', '( %s -> %s )' % (ante, INTP))
    itz_ = w.s([tri_, w.inst('simp2')], 'syl', '( %s -> %s )' % (ante, INTZ))
    ho_ = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (ante, HOLO))
    k1 = w.s([kn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ante, K))
    ccl = w.s([w.s([w.s([ab_, it_, ho_], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ante, AB, INTP, HOLO)), k1], 'jca',
                   '( %s -> ( ( %s /\\ %s /\\ %s ) /\\ ( %s + 1 ) e. NN0 ) )' % (ante, AB, INTP, HOLO, K)), w.inst('rectintccl')], 'syl',
              '( %s -> %s e. CC )' % (ante, RINT(CFM(PUP, '( %s + 1 )' % K), 'A', 'B')))
    zpk = w.s([w.s([w.s([itz_, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % ante), w.s([it_, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % ante)], 'subcld',
                   '( %s -> ( Z - P ) e. CC )' % ante), kn], 'expcld', '( %s -> ( ( Z - P ) ^ %s ) e. CC )' % (ante, K))
    return w.s([v, w.s([zpk, ccl], 'mulcld', '( %s -> %s e. CC )' % (ante, HT(K)))], 'eqeltrd', '( %s -> ( H ` %s ) e. CC )' % (ante, K))


def gcl(ante, K, kn, bs):
    v = gval(ante, K, kn)
    r = w.s([w.s([bs, kn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (ante, BASE, K)), w.inst('rectintrcl')], 'syl',
            '( %s -> %s e. CC )' % (ante, RINT(RM(E2, K), 'A', 'B')))
    return w.s([v, r], 'eqeltrd', '( %s -> ( G ` %s ) e. CC )' % (ante, K))


h1 = isub('0'); h2 = isub('m'); h3 = isub('( m + 1 )'); h4 = isub('N')
# base case
z0 = closed(w, BASE, '0nn0', '0 e. NN0')
bid = w.s([], 'id', '( %s -> %s )' % (BASE, BASE))
gv0 = gval(BASE, '0', z0)
w0 = w.s([bid, w.inst('rectintw0')], 'syl', '( %s -> %s = %s )' % (BASE, RINT(RM(E2, '0'), 'A', 'B'), LHS))
g0L = w.s([gv0, w0], 'eqtrd', '( %s -> ( G ` 0 ) = %s )' % (BASE, LHS))
f0 = w.s([], 'fzo0', '( 0 ..^ 0 ) = (/)')
s0a = w.s([f0], 'sumeq1i', '%s = sum_ k e. (/) ( H ` k )' % SUM('0'))
s0b = w.s([], 'sum0', 'sum_ k e. (/) ( H ` k ) = 0')
s0 = w.s([w.s([s0a, s0b], 'eqtri', '%s = 0' % SUM('0'))], 'a1i', '( %s -> %s = 0 )' % (BASE, SUM('0')))
g0c = gcl(BASE, '0', z0, bid)
base = w.s([w.s([w.s([w.s([s0], 'oveq1d', '( %s -> %s = ( 0 + ( G ` 0 ) ) )' % (BASE, RHS('0'))),
                      w.s([g0c], 'addlidd', '( %s -> ( 0 + ( G ` 0 ) ) = ( G ` 0 ) )' % BASE)], 'eqtrd',
                     '( %s -> %s = ( G ` 0 ) )' % (BASE, RHS('0'))), g0L], 'eqtrd', '( %s -> %s = %s )' % (BASE, RHS('0'), LHS))], 'eqcomd', PHI('0'))
# induction step
SS = '( %s /\\ m e. NN0 )' % BASE
LS = '( ( m e. NN0 /\\ %s ) /\\ %s )' % (PHI('m'), BASE)
ssb = w.s([], 'simpl', '( %s -> %s )' % (SS, BASE))
ssm = w.s([], 'simpr', '( %s -> m e. NN0 )' % SS)
ssm1 = w.s([ssm, w.inst('peano2nn0')], 'syl', '( %s -> ( m + 1 ) e. NN0 )' % SS)
mz = w.s([ssm, w.s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % SS)], 'eleqtrd', '( %s -> m e. ( ZZ>= ` 0 ) )' % SS)
fzs = w.s([mz, w.inst('fzosplitsn')], 'syl', '( %s -> ( 0 ..^ ( m + 1 ) ) = ( ( 0 ..^ m ) u. { m } ) )' % SS)
sm1 = w.s([fzs], 'sumeq1d', '( %s -> %s = sum_ k e. ( ( 0 ..^ m ) u. { m } ) ( H ` k ) )' % (SS, SUM('( m + 1 )')))
nfp = w.s([], 'nfv', 'F/ k %s' % SS)
nfd = w.s([], 'nfcv', 'F/_ k ( H ` m )')
fin = closed(w, SS, 'fzofi', '( 0 ..^ m ) e. Fin')
nel = closed(w, SS, 'fzonel', '-. m e. ( 0 ..^ m )')
SK = '( %s /\\ k e. ( 0 ..^ m ) )' % SS
knn = w.s([w.s([closed(w, SK, 'fzo0ssnn0', '( 0 ..^ m ) C_ NN0')], 'id', '( %s -> ( 0 ..^ m ) C_ NN0 )' % SK) if False else closed(w, SK, 'fzo0ssnn0', '( 0 ..^ m ) C_ NN0'),
           w.s([], 'simpr', '( %s -> k e. ( 0 ..^ m ) )' % SK)], 'sseldd', '( %s -> k e. NN0 )' % SK)
hkc = hcl(SK, 'k', knn, w.s([ssb], 'adantr', '( %s -> %s )' % (SK, BASE)))
hmc = hcl(SS, 'm', ssm, ssb)
subk = w.s([], 'fveq2', '( k = m -> ( H ` k ) = ( H ` m ) )')
spl = w.s([sm1, w.s([nfp, nfd, fin, ssm, nel, hkc, subk, hmc], 'fsumsplitsn',
                    '( %s -> sum_ k e. ( ( 0 ..^ m ) u. { m } ) ( H ` k ) = ( %s + ( H ` m ) ) )' % (SS, SUM('m')))], 'eqtrd',
           '( %s -> %s = ( %s + ( H ` m ) ) )' % (SS, SUM('( m + 1 )'), SUM('m')))
sumc = w.s([fin, hkc], 'fsumcl', '( %s -> %s e. CC )' % (SS, SUM('m')))
gm1c = gcl(SS, '( m + 1 )', ssm1, ssb)
gvm = gval(SS, 'm', ssm)
gvm1 = gval(SS, '( m + 1 )', ssm1)
hvm = hval(SS, 'm', ssm)
rrm = w.s([ssb, ssm, w.inst('rectintrm')], 'syl2anc',
          '( %s -> %s = ( %s + %s ) )' % (SS, RINT(RM(E2, 'm'), 'A', 'B'), HT('m'), RINT(RM(E2, '( m + 1 )'), 'A', 'B')))
gmeq = w.s([w.s([gvm, rrm], 'eqtrd', '( %s -> ( G ` m ) = ( %s + %s ) )' % (SS, HT('m'), RINT(RM(E2, '( m + 1 )'), 'A', 'B'))),
            w.s([hvm, gvm1], 'oveq12d', '( %s -> ( ( H ` m ) + ( G ` ( m + 1 ) ) ) = ( %s + %s ) )' % (SS, HT('m'), RINT(RM(E2, '( m + 1 )'), 'A', 'B')))], 'eqtr4d',
           '( %s -> ( G ` m ) = ( ( H ` m ) + ( G ` ( m + 1 ) ) ) )' % SS)
rr1 = w.s([w.s([spl], 'oveq1d', '( %s -> %s = ( ( %s + ( H ` m ) ) + ( G ` ( m + 1 ) ) ) )' % (SS, RHS('( m + 1 )'), SUM('m'))),
           w.s([sumc, hmc, gm1c], 'addassd', '( %s -> ( ( %s + ( H ` m ) ) + ( G ` ( m + 1 ) ) ) = ( %s + ( ( H ` m ) + ( G ` ( m + 1 ) ) ) ) )' % (SS, SUM('m'), SUM('m')))], 'eqtrd',
          '( %s -> %s = ( %s + ( ( H ` m ) + ( G ` ( m + 1 ) ) ) ) )' % (SS, RHS('( m + 1 )'), SUM('m')))
rr2 = w.s([rr1, w.s([w.s([gmeq], 'eqcomd', '( %s -> ( ( H ` m ) + ( G ` ( m + 1 ) ) ) = ( G ` m ) )' % SS)], 'oveq2d',
                    '( %s -> ( %s + ( ( H ` m ) + ( G ` ( m + 1 ) ) ) ) = %s )' % (SS, SUM('m'), RHS('m')))], 'eqtrd',
          '( %s -> %s = %s )' % (SS, RHS('( m + 1 )'), RHS('m')))
lsb = w.s([], 'simpr', '( %s -> %s )' % (LS, BASE))
lsm = w.s([], 'simpll', '( %s -> m e. NN0 )' % LS)
lss = w.s([lsb, lsm], 'jca', '( %s -> %s )' % (LS, SS))
ih = w.s([lsb, w.s([], 'simplr', '( %s -> %s )' % (LS, PHI('m')))], 'mpd', '( %s -> %s = %s )' % (LS, LHS, RHS('m')))
stp = w.s([ih, w.s([w.s([lss, rr2], 'syl', '( %s -> %s = %s )' % (LS, RHS('( m + 1 )'), RHS('m')))], 'eqcomd',
                   '( %s -> %s = %s )' % (LS, RHS('m'), RHS('( m + 1 )')))], 'eqtrd', '( %s -> %s = %s )' % (LS, LHS, RHS('( m + 1 )')))
e1 = w.s([stp], 'ex', '( ( m e. NN0 /\\ %s ) -> %s )' % (PHI('m'), PHI('( m + 1 )')))
e2 = w.s([e1], 'ex', '( m e. NN0 -> ( %s -> %s ) )' % (PHI('m'), PHI('( m + 1 )')))
ind = w.s([h1, h2, h3, h4, base, e2], 'nn0ind', '( N e. NN0 -> %s )' % PHI('N'))
w.qed([w.s([ind], 'com12', '( %s -> ( N e. NN0 -> %s = %s ) )' % (BASE, LHS, RHS('N')))], 'imp',
      '( ( %s /\\ N e. NN0 ) -> %s = %s )' % (BASE, LHS, RHS('N')))
run1(w, h=True)

# ---- rectintrmb: the geometric bound on the Taylor remainder ---------------
RBDP = '( R e. RR /\\ ( ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) /\\ ( R <_ ( %s - %s ) /\\ R <_ ( %s - %s ) ) ) )' % (
    RPP, RA, RB, RPP, IPP, IA, IB, IPP)
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
PER = '( ( %s - %s ) + ( %s - %s ) )' % (RB, RA, IB, IA)
XV = '( ( Z - P ) / ( v - P ) )'
HALF = '( ( 1 / 2 ) ^ N )'
w = W('rectintrmb', 'The Taylor remainder integral of order N is bounded by a '
      'constant times two to the minus N, when the evaluation point is within '
      'half the distance R from the centre to the boundary frame.')
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
# ( abs ` XV ) <_ ( 1 / 2 )
axv = w.s([zp1, vp, vpn], 'absdivd', '( %s -> ( abs ` %s ) = ( ( abs ` ( Z - P ) ) / ( abs ` ( v - P ) ) ) )' % (A1, XV))
hq = w.s([w.s([w.s([rr1], 'recnd', '( %s -> R e. CC )' % A1), closed(w, A1, '2cn', '2 e. CC'), w.s([rr1], 'recnd', '( %s -> R e. CC )' % A1),
               closed(w, A1, '2ne0', '2 =/= 0'), w.s([Rrp1], 'rpne0d', '( %s -> R =/= 0 )' % A1)], 'divdiv32d', '( %s -> ( ( R / 2 ) / R ) = ( ( R / R ) / 2 ) )' % A1),
          w.s([w.s([w.s([rr1], 'recnd', '( %s -> R e. CC )' % A1), w.s([Rrp1], 'rpne0d', '( %s -> R =/= 0 )' % A1)], 'dividd', '( %s -> ( R / R ) = 1 )' % A1)], 'oveq1d',
              '( %s -> ( ( R / R ) / 2 ) = ( 1 / 2 ) )' % A1)], 'eqtrd', '( %s -> ( ( R / 2 ) / R ) = ( 1 / 2 ) )' % A1)
xle = w.s([w.s([axv, w.s([azp, hr1, Rrp1, avp, w.s([zp1], 'absge0d', '( %s -> 0 <_ ( abs ` ( Z - P ) ) )' % A1), zple1, rle], 'lediv12ad',
                         '( %s -> ( ( abs ` ( Z - P ) ) / ( abs ` ( v - P ) ) ) <_ ( ( R / 2 ) / R ) )' % A1)], 'eqbrtrd',
               '( %s -> ( abs ` %s ) <_ ( ( R / 2 ) / R ) )' % (A1, XV)), hq], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( 1 / 2 ) )' % (A1, XV))
axr = w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, XV))
halfr = closed(w, A1, 'halfre', '( 1 / 2 ) e. RR')
xnle = w.s([axr, halfr, hn1, w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A1, XV)), xle], 'leexp1ad',
           '( %s -> ( ( abs ` %s ) ^ N ) <_ %s )' % (A1, XV, HALF))
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
halfn = w.s([halfr, hn1], 'reexpcld', '( %s -> %s e. RR )' % (A1, HALF))
num = w.s([w.s([afv, mr1, xnr, halfn, w.s([fv_], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A1),
                w.s([axr, w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A1, XV)), hn1], 'expge0d', '( %s -> 0 <_ ( ( abs ` %s ) ^ N ) )' % (A1, XV)),
                fle, xnle], 'lemul12ad', '( %s -> ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) <_ ( M x. %s ) )' % (A1, XV, HALF))], 'id', '') if False else \
    w.s([afv, mr1, xnr, halfn, fle, xnle], 'lemul12ad', '( %s -> ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) <_ ( M x. %s ) )' % (A1, XV, HALF))
ptb = w.s([w.s([afv, xnr], 'remulcld', '( %s -> ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) e. RR )' % (A1, XV)),
           w.s([mr1, halfn], 'remulcld', '( %s -> ( M x. %s ) e. RR )' % (A1, HALF)), Hrp1, avz,
           w.s([afv, xnr, w.s([fv_], 'absge0d', '( %s -> 0 <_ ( abs ` ( F ` v ) ) )' % A1),
                w.s([axr, w.s([w.s([zp1, vp, vpn], 'divcld', '( %s -> %s e. CC )' % (A1, XV))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A1, XV)), hn1], 'expge0d', '( %s -> 0 <_ ( ( abs ` %s ) ^ N ) )' % (A1, XV))], 'mulge0d',
               '( %s -> 0 <_ ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) )' % (A1, XV)), num, hle], 'lediv12ad',
          '( %s -> ( ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) / ( abs ` ( v - Z ) ) ) <_ ( ( M x. %s ) / ( R / 2 ) ) )' % (A1, XV, HALF))
pw = w.s([w.s([w.s([w.s([vval], 'fveq2d', '( %s -> ( abs ` ( %s ` v ) ) = ( abs ` %s ) )' % (A1, RM(E2, 'N'), BV)), absq], 'eqtrd',
                    '( %s -> ( abs ` ( %s ` v ) ) = ( ( abs ` ( ( F ` v ) x. ( %s ^ N ) ) ) / ( abs ` ( v - Z ) ) ) )' % (A1, RM(E2, 'N'), XV)),
               w.s([absn], 'oveq1d', '( %s -> ( ( abs ` ( ( F ` v ) x. ( %s ^ N ) ) ) / ( abs ` ( v - Z ) ) ) = ( ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) / ( abs ` ( v - Z ) ) ) )' % (A1, XV, XV))], 'eqtrd',
              '( %s -> ( abs ` ( %s ` v ) ) = ( ( ( abs ` ( F ` v ) ) x. ( ( abs ` %s ) ^ N ) ) / ( abs ` ( v - Z ) ) ) )' % (A1, RM(E2, 'N'), XV)), ptb], 'eqbrtrd',
         '( %s -> ( abs ` ( %s ` v ) ) <_ ( ( M x. %s ) / ( R / 2 ) ) )' % (A1, RM(E2, 'N'), HALF))
allv = w.s([pw], 'ralrimiva', '( %s -> A. v e. %s ( abs ` ( %s ` v ) ) <_ ( ( M x. %s ) / ( R / 2 ) ) )' % (A0, FR, RM(E2, 'N'), HALF))
halfr0 = closed(w, A0, 'halfre', '( 1 / 2 ) e. RR')
halfn0 = w.s([halfr0, hn], 'reexpcld', '( %s -> %s e. RR )' % (A0, HALF))
bndr = w.s([w.s([mr, halfn0], 'remulcld', '( %s -> ( M x. %s ) e. RR )' % (A0, HALF)), Hrp], 'rerpdivcld', '( %s -> ( ( M x. %s ) / ( R / 2 ) ) e. RR )' % (A0, HALF))
abse = w.s([pse, bndr, allv, w.inst('rectintabse')], 'syl3anc',
           '( %s -> ( abs ` %s ) <_ ( ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) x. %s ) )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'), HALF, PER))
# rearrange the bound into K x. ( ( 1 / 2 ) ^ N )
perr = w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)), w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
perc = w.s([perr], 'recnd', '( %s -> %s e. CC )' % (A0, PER))
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
hc = w.s([w.s([Hrp], 'rpred', '( %s -> ( R / 2 ) e. RR )' % A0)], 'recnd', '( %s -> ( R / 2 ) e. CC )' % A0)
hne = w.s([Hrp], 'rpne0d', '( %s -> ( R / 2 ) =/= 0 )' % A0)
tc = w.s([halfn0], 'recnd', '( %s -> %s e. CC )' % (A0, HALF))
t2c = closed(w, A0, '2cn', '2 e. CC')
mq = w.s([mc, hc, hne], 'divcld', '( %s -> ( M / ( R / 2 ) ) e. CC )' % A0)
K = '( ( 2 x. ( M / ( R / 2 ) ) ) x. %s )' % PER
r1 = w.s([mc, tc, hc, hne], 'div23d', '( %s -> ( ( M x. %s ) / ( R / 2 ) ) = ( ( M / ( R / 2 ) ) x. %s ) )' % (A0, HALF, HALF))
r2 = w.s([w.s([r1], 'oveq2d', '( %s -> ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) = ( 2 x. ( ( M / ( R / 2 ) ) x. %s ) ) )' % (A0, HALF, HALF)),
          w.s([w.s([t2c, mq, tc], 'mulassd', '( %s -> ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) = ( 2 x. ( ( M / ( R / 2 ) ) x. %s ) ) )' % (A0, HALF, HALF))], 'eqcomd',
              '( %s -> ( 2 x. ( ( M / ( R / 2 ) ) x. %s ) ) = ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) )' % (A0, HALF, HALF))], 'eqtrd',
         '( %s -> ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) = ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) )' % (A0, HALF, HALF))
r3 = w.s([w.s([r2], 'oveq1d', '( %s -> ( ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) x. %s ) = ( ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) x. %s ) )' % (A0, HALF, PER, HALF, PER)),
          w.s([w.s([t2c, mq], 'mulcld', '( %s -> ( 2 x. ( M / ( R / 2 ) ) ) e. CC )' % A0), tc, perc], 'mul32d',
              '( %s -> ( ( ( 2 x. ( M / ( R / 2 ) ) ) x. %s ) x. %s ) = ( %s x. %s ) )' % (A0, HALF, PER, K, HALF))], 'eqtrd',
         '( %s -> ( ( 2 x. ( ( M x. %s ) / ( R / 2 ) ) ) x. %s ) = ( %s x. %s ) )' % (A0, HALF, PER, K, HALF))
w.qed([abse, r3], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( %s x. %s ) )' % (A0, RINT(RM(E2, 'N'), 'A', 'B'), K, HALF)); run1(w)

# ---- rectintana: the Taylor series converges to the value ------------------
KK = '( ( 2 x. ( M / ( R / 2 ) ) ) x. %s )' % PER
SEQ = '( n e. NN0 |-> ( ( 1 / 2 ) ^ n ) )'
KSEQ = '( n e. NN0 |-> ( %s x. ( ( 1 / 2 ) ^ n ) ) )' % KK
ABSG = '( n e. NN0 |-> ( abs ` ( G ` n ) ) )'
PSUM = '( n e. NN0 |-> sum_ k e. ( 0 ..^ n ) ( H ` k ) )'
w = W('rectintana', 'A holomorphic function on a rectangle is analytic: its '
      'Taylor partial sums about a strictly interior centre P converge to 2 pi i '
      'times its value at every strictly interior point Z within half the '
      'distance R from P to the boundary frame.')
hyp(w, '1', 'rectintana.g', GDEF)
hyp(w, '2', 'rectintana.h', HDEF)
A0 = '( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) )' % (BASE, RBDP, ALF)
AI = '( %s /\\ i e. NN0 )' % A0
bs = w.s([], 'simp1', '( %s -> %s )' % (A0, BASE))
rz = w.s([], 'simp2', '( %s -> ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) )' % (A0, RBDP))
mm = w.s([], 'simp3', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))
rbd = w.s([w.s([rz, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP)), w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP))
rpos = w.s([w.s([rz, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP)), w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
rr = w.s([rbd, w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
Rrp = w.s([rr, rpos], 'elrpd', '( %s -> R e. RR+ )' % A0)
Hrp = w.s([Rrp], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % A0)
mr = w.s([mm, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
tri = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (A0, INTP, INTZ))
holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
it = w.s([tri, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
itz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTZ))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
zc = w.s([itz, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
crd = w.s([hss, w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
zmem = w.s([w.s([ab, itz], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTZ)), w.inst('crectinp')], 'syl', '( %s -> Z e. ( A crect B ) )' % A0)
fz = w.s([ff, w.s([crd, zmem], 'sseldd', '( %s -> Z e. D )' % A0)], 'ffvelcdmd', '( %s -> ( F ` Z ) e. CC )' % A0)
tpic = w.s([closed(w, A0, '2cn', '2 e. CC'), w.s([closed(w, A0, 'ax-icn', '_i e. CC'), closed(w, A0, 'picn', '_pi e. CC')], 'mulcld', '( %s -> ( _i x. _pi ) e. CC )' % A0)],
           'mulcld', '( %s -> %s e. CC )' % (A0, TPI))
Lc = w.s([tpic, fz], 'mulcld', '( %s -> %s e. CC )' % (A0, LHS))
ar = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
perr = w.s([w.s([br, ar], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)), w.s([bi, ai], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
Kr = w.s([w.s([closed(w, A0, '2re', '2 e. RR'), w.s([mr, Hrp], 'rerpdivcld', '( %s -> ( M / ( R / 2 ) ) e. RR )' % A0)], 'remulcld', '( %s -> ( 2 x. ( M / ( R / 2 ) ) ) e. RR )' % A0), perr],
         'remulcld', '( %s -> %s e. RR )' % (A0, KK))
Kc = w.s([Kr], 'recnd', '( %s -> %s e. CC )' % (A0, KK))
zeq = w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')
mz = closed(w, A0, '0z', '0 e. ZZ')
hcn = closed(w, A0, 'halfcn', '( 1 / 2 ) e. CC')
habs = w.s([w.s([closed(w, A0, 'halfre', '( 1 / 2 ) e. RR'), closed(w, A0, 'halfge0', '0 <_ ( 1 / 2 )')], 'absidd', '( %s -> ( abs ` ( 1 / 2 ) ) = ( 1 / 2 ) )' % A0),
            closed(w, A0, 'halflt1', '( 1 / 2 ) < 1')], 'eqbrtrd', '( %s -> ( abs ` ( 1 / 2 ) ) < 1 )' % A0)
cnv = w.s([hcn, habs], 'expcnv', '( %s -> %s ~~> 0 )' % (A0, SEQ))
# ( KSEQ ` i ) and ( SEQ ` i )
inn = w.s([], 'simpr', '( %s -> i e. NN0 )' % AI)
sub1 = w.s([], 'oveq2', '( n = i -> ( ( 1 / 2 ) ^ n ) = ( ( 1 / 2 ) ^ i ) )')
eqs = w.s([], 'eqid', '%s = %s' % (SEQ, SEQ))
fseq = w.s([sub1, eqs], 'fvmptg', '( ( i e. NN0 /\\ ( ( 1 / 2 ) ^ i ) e. _V ) -> ( %s ` i ) = ( ( 1 / 2 ) ^ i ) )' % SEQ)
vseq = w.s([inn, ovexd(w, AI, '( ( 1 / 2 ) ^ i )'), fseq], 'syl2anc', '( %s -> ( %s ` i ) = ( ( 1 / 2 ) ^ i ) )' % (AI, SEQ))
hir = w.s([closed(w, AI, 'halfre', '( 1 / 2 ) e. RR'), inn], 'reexpcld', '( %s -> ( ( 1 / 2 ) ^ i ) e. RR )' % AI)
seqcl = w.s([vseq, w.s([hir], 'recnd', '( %s -> ( ( 1 / 2 ) ^ i ) e. CC )' % AI)], 'eqeltrd', '( %s -> ( %s ` i ) e. CC )' % (AI, SEQ))
sub2 = w.s([sub1], 'oveq2d', '( n = i -> ( %s x. ( ( 1 / 2 ) ^ n ) ) = ( %s x. ( ( 1 / 2 ) ^ i ) ) )' % (KK, KK))
eqk = w.s([], 'eqid', '%s = %s' % (KSEQ, KSEQ))
fk = w.s([sub2, eqk], 'fvmptg', '( ( i e. NN0 /\\ ( %s x. ( ( 1 / 2 ) ^ i ) ) e. _V ) -> ( %s ` i ) = ( %s x. ( ( 1 / 2 ) ^ i ) ) )' % (KK, KSEQ, KK))
vk = w.s([inn, ovexd(w, AI, '( %s x. ( ( 1 / 2 ) ^ i ) )' % KK), fk], 'syl2anc', '( %s -> ( %s ` i ) = ( %s x. ( ( 1 / 2 ) ^ i ) ) )' % (AI, KSEQ, KK))
vkc = w.s([vk, w.s([vseq], 'oveq2d', '( %s -> ( %s x. ( %s ` i ) ) = ( %s x. ( ( 1 / 2 ) ^ i ) ) )' % (AI, KK, SEQ, KK))], 'eqtr4d',
          '( %s -> ( %s ` i ) = ( %s x. ( %s ` i ) ) )' % (AI, KSEQ, KK, SEQ))
kex = w.s([closed(w, A0, 'nn0ex', 'NN0 e. _V'), w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, KSEQ))
kcnv0 = w.s([zeq, mz, cnv, Kc, kex, seqcl, vkc], 'climmulc2', '( %s -> %s ~~> ( %s x. 0 ) )' % (A0, KSEQ, KK))
kcnv = w.s([kcnv0, w.s([Kc], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (A0, KK))], 'breqtrd', '( %s -> %s ~~> 0 )' % (A0, KSEQ))
# the remainder function tends to zero
bsi = w.s([bs], 'adantr', '( %s -> %s )' % (AI, BASE))
bni = w.s([bsi, inn], 'jca', '( %s -> ( %s /\\ i e. NN0 ) )' % (AI, BASE))
rmbi = w.s([w.s([bni, w.s([rz], 'adantr', '( %s -> ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) )' % (AI, RBDP)),
                 w.s([mm], 'adantr', '( %s -> ( M e. RR /\\ %s ) )' % (AI, ALF))], '3jca',
                '( %s -> ( ( %s /\\ i e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) )' % (AI, BASE, RBDP, ALF)), w.inst('rectintrmb')], 'syl',
           '( %s -> ( abs ` %s ) <_ ( %s x. ( ( 1 / 2 ) ^ i ) ) )' % (AI, RINT(RM(E2, 'i'), 'A', 'B'), KK))
gvi = gval(AI, 'i', inn)
gicl = w.s([gvi, w.s([bni, w.inst('rectintrcl')], 'syl', '( %s -> %s e. CC )' % (AI, RINT(RM(E2, 'i'), 'A', 'B')))], 'eqeltrd', '( %s -> ( G ` i ) e. CC )' % AI)
suba = w.s([], 'fveq2', '( n = i -> ( G ` n ) = ( G ` i ) )')
subaa = w.s([suba], 'fveq2d', '( n = i -> ( abs ` ( G ` n ) ) = ( abs ` ( G ` i ) ) )')
eqa = w.s([], 'eqid', '%s = %s' % (ABSG, ABSG))
fa = w.s([subaa, eqa], 'fvmptg', '( ( i e. NN0 /\\ ( abs ` ( G ` i ) ) e. _V ) -> ( %s ` i ) = ( abs ` ( G ` i ) ) )' % ABSG)
absex = w.s([w.s([], 'fvex', '( abs ` ( G ` i ) ) e. _V')], 'a1i', '( %s -> ( abs ` ( G ` i ) ) e. _V )' % AI)
vabs = w.s([inn, absex, fa], 'syl2anc', '( %s -> ( %s ` i ) = ( abs ` ( G ` i ) ) )' % (AI, ABSG))
absr = w.s([vabs, w.s([gicl], 'abscld', '( %s -> ( abs ` ( G ` i ) ) e. RR )' % AI)], 'eqeltrd', '( %s -> ( %s ` i ) e. RR )' % (AI, ABSG))
kr = w.s([vk, w.s([w.s([Kr], 'adantr', '( %s -> %s e. RR )' % (AI, KK)), hir], 'remulcld', '( %s -> ( %s x. ( ( 1 / 2 ) ^ i ) ) e. RR )' % (AI, KK))], 'eqeltrd',
         '( %s -> ( %s ` i ) e. RR )' % (AI, KSEQ))
lek = w.s([w.s([w.s([vabs, w.s([gvi], 'fveq2d', '( %s -> ( abs ` ( G ` i ) ) = ( abs ` %s ) )' % (AI, RINT(RM(E2, 'i'), 'A', 'B')))], 'eqtrd',
                    '( %s -> ( %s ` i ) = ( abs ` %s ) )' % (AI, ABSG, RINT(RM(E2, 'i'), 'A', 'B'))), rmbi], 'eqbrtrd',
               '( %s -> ( %s ` i ) <_ ( %s x. ( ( 1 / 2 ) ^ i ) ) )' % (AI, ABSG, KK)),
           w.s([vk], 'eqcomd', '( %s -> ( %s x. ( ( 1 / 2 ) ^ i ) ) = ( %s ` i ) )' % (AI, KK, KSEQ))], 'breqtrd',
          '( %s -> ( %s ` i ) <_ ( %s ` i ) )' % (AI, ABSG, KSEQ))
ge0 = w.s([vabs, w.s([gicl], 'absge0d', '( %s -> 0 <_ ( abs ` ( G ` i ) ) )' % AI)], 'breqtrrd', '( %s -> 0 <_ ( %s ` i ) )' % (AI, ABSG))
aex = w.s([closed(w, A0, 'nn0ex', 'NN0 e. _V'), w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, ABSG))
acnv = w.s([zeq, mz, kcnv, aex, kr, absr, lek, ge0], 'climsqz2', '( %s -> %s ~~> 0 )' % (A0, ABSG))
GRHS = '( n e. NN0 |-> %s )' % RINT(RM(E2, 'n'), 'A', 'B')
gdd = w.s(['1'], 'a1i', '( %s -> G = %s )' % (A0, GRHS))
gex = w.s([gdd, w.s([closed(w, A0, 'nn0ex', 'NN0 e. _V'), w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, GRHS))], 'eqeltrd', '( %s -> G e. _V )' % A0)
gcnv = w.s([w.s([zeq, mz, gex, aex, gicl, vabs], 'climabs0', '( %s -> ( G ~~> 0 <-> %s ~~> 0 ) )' % (A0, ABSG)), acnv], 'mpbird', '( %s -> G ~~> 0 )' % A0)
# the partial sums
subs = w.s([], 'oveq2', '( n = i -> ( 0 ..^ n ) = ( 0 ..^ i ) )')
subs2 = w.s([subs], 'sumeq1d', '( n = i -> sum_ k e. ( 0 ..^ n ) ( H ` k ) = sum_ k e. ( 0 ..^ i ) ( H ` k ) )')
eqp = w.s([], 'eqid', '%s = %s' % (PSUM, PSUM))
fp = w.s([subs2, eqp], 'fvmptg', '( ( i e. NN0 /\\ sum_ k e. ( 0 ..^ i ) ( H ` k ) e. _V ) -> ( %s ` i ) = sum_ k e. ( 0 ..^ i ) ( H ` k ) )' % PSUM)
sex = w.s([w.s([], 'sumex', 'sum_ k e. ( 0 ..^ i ) ( H ` k ) e. _V')], 'a1i', '( %s -> sum_ k e. ( 0 ..^ i ) ( H ` k ) e. _V )' % AI)
vps = w.s([inn, sex, fp], 'syl2anc', '( %s -> ( %s ` i ) = sum_ k e. ( 0 ..^ i ) ( H ` k ) )' % (AI, PSUM))
tay0 = w.s(['1', '2'], 'rectinttay', '( ( %s /\\ i e. NN0 ) -> %s = ( sum_ k e. ( 0 ..^ i ) ( H ` k ) + ( G ` i ) ) )' % (BASE, LHS))
tayi = w.s([bni, tay0], 'syl', '( %s -> %s = ( sum_ k e. ( 0 ..^ i ) ( H ` k ) + ( G ` i ) ) )' % (AI, LHS))
sumc = w.s([w.s([vps], 'eqcomd', '( %s -> sum_ k e. ( 0 ..^ i ) ( H ` k ) = ( %s ` i ) )' % (AI, PSUM)), w.s([w.s([], 'fvex', '( %s ` i ) e. _V' % PSUM)], 'a1i', '( %s -> ( %s ` i ) e. _V )' % (AI, PSUM))], 'eqeltrd', '') if False else None
sc = w.s([w.s([Lc], 'adantr', '( %s -> %s e. CC )' % (AI, LHS)), gicl], 'subcld', '( %s -> ( %s - ( G ` i ) ) e. CC )' % (AI, LHS))
scl = w.s([tayi, w.s([Lc], 'adantr', '( %s -> %s e. CC )' % (AI, LHS)), gicl], 'id', '') if False else None
sumcl = w.s([closed(w, AI, 'fzofi', '( 0 ..^ i ) e. Fin'), hcl('( %s /\\ k e. ( 0 ..^ i ) )' % AI, 'k',
                                                               w.s([closed(w, '( %s /\\ k e. ( 0 ..^ i ) )' % AI, 'fzo0ssnn0', '( 0 ..^ i ) C_ NN0'),
                                                                    w.s([], 'simpr', '( ( %s /\\ k e. ( 0 ..^ i ) ) -> k e. ( 0 ..^ i ) )' % AI)], 'sseldd', '( ( %s /\\ k e. ( 0 ..^ i ) ) -> k e. NN0 )' % AI),
                                                               w.s([bsi], 'adantr', '( ( %s /\\ k e. ( 0 ..^ i ) ) -> %s )' % (AI, BASE)))], 'fsumcl',
            '( %s -> sum_ k e. ( 0 ..^ i ) ( H ` k ) e. CC )' % AI)
psd = w.s([vps, w.s([w.s([w.s([Lc], 'adantr', '( %s -> %s e. CC )' % (AI, LHS)), gicl, sumcl], 'subadd2d',
                          '( %s -> ( ( %s - ( G ` i ) ) = sum_ k e. ( 0 ..^ i ) ( H ` k ) <-> ( sum_ k e. ( 0 ..^ i ) ( H ` k ) + ( G ` i ) ) = %s ) )' % (AI, LHS, LHS)),
                    w.s([tayi], 'eqcomd', '( %s -> ( sum_ k e. ( 0 ..^ i ) ( H ` k ) + ( G ` i ) ) = %s )' % (AI, LHS))], 'mpbird',
                   '( %s -> ( %s - ( G ` i ) ) = sum_ k e. ( 0 ..^ i ) ( H ` k ) )' % (AI, LHS))], 'eqtr4d',
          '( %s -> ( %s ` i ) = ( %s - ( G ` i ) ) )' % (AI, PSUM, LHS))
pex = w.s([closed(w, A0, 'nn0ex', 'NN0 e. _V'), w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, PSUM))
fin = w.s([zeq, mz, gcnv, Lc, pex, gicl, psd], 'climsubc2', '( %s -> %s ~~> ( %s - 0 ) )' % (A0, PSUM, LHS))
w.qed([fin, w.s([Lc], 'subid1d', '( %s -> ( %s - 0 ) = %s )' % (A0, LHS, LHS))], 'breqtrd', '( %s -> %s ~~> %s )' % (A0, PSUM, LHS))
run1(w, h=True)

# ---- rectintid: the local identity theorem ---------------------------------
w = W('rectintid', 'The local identity theorem: a holomorphic function on a '
      'rectangle whose Taylor coefficients about a strictly interior centre P '
      'all vanish is zero at every strictly interior point within half the '
      'distance R from P to the boundary frame.')
hyp(w, '1', 'rectintid.g', GDEF)
hyp(w, '2', 'rectintid.h', HDEF)
CTXa = '( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( Z - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) )' % (BASE, RBDP, ALF)
ZER = 'A. i e. NN0 ( H ` i ) = 0'
A0 = '( %s /\\ %s )' % (CTXa, ZER)
AN = '( %s /\\ n e. NN0 )' % A0
ctx = w.s([], 'simpl', '( %s -> %s )' % (A0, CTXa))
zer = w.s([], 'simpr', '( %s -> %s )' % (A0, ZER))
cb = w.s([], 'fveq2', '( i = k -> ( H ` i ) = ( H ` k ) )')
cb2 = w.s([cb], 'eqeq1d', '( i = k -> ( ( H ` i ) = 0 <-> ( H ` k ) = 0 ) )')
zerk = w.s([zer, w.s([cb2], 'cbvralvw', '( %s <-> A. k e. NN0 ( H ` k ) = 0 )' % ZER)], 'sylib', '( %s -> A. k e. NN0 ( H ` k ) = 0 )' % A0)
AK = '( %s /\\ k e. ( 0 ..^ n ) )' % AN
knn = w.s([closed(w, AK, 'fzo0ssnn0', '( 0 ..^ n ) C_ NN0'), w.s([], 'simpr', '( %s -> k e. ( 0 ..^ n ) )' % AK)], 'sseldd', '( %s -> k e. NN0 )' % AK)
hk0 = w.s([w.s([w.s([zerk], 'adantr', '( %s -> A. k e. NN0 ( H ` k ) = 0 )' % AN)], 'adantr', '( %s -> A. k e. NN0 ( H ` k ) = 0 )' % AK), knn, w.inst('rspa')], 'syl2anc',
          '( %s -> ( H ` k ) = 0 )' % AK)
sz = w.s([w.s([hk0], 'sumeq2dv', '( %s -> sum_ k e. ( 0 ..^ n ) ( H ` k ) = sum_ k e. ( 0 ..^ n ) 0 )' % AN),
          w.s([w.s([closed(w, AN, 'fzofi', '( 0 ..^ n ) e. Fin')], 'olcd', '( %s -> ( ( 0 ..^ n ) C_ ( ZZ>= ` 0 ) \\/ ( 0 ..^ n ) e. Fin ) )' % AN), w.inst('sumz')], 'syl',
              '( %s -> sum_ k e. ( 0 ..^ n ) 0 = 0 )' % AN)], 'eqtrd', '( %s -> sum_ k e. ( 0 ..^ n ) ( H ` k ) = 0 )' % AN)
pmt = w.s([sz], 'mpteq2dva', '( %s -> %s = ( n e. NN0 |-> 0 ) )' % (A0, PSUM))
fcm = w.s([w.s([], 'fconstmpt', '( NN0 X. { 0 } ) = ( n e. NN0 |-> 0 )')], 'a1i', '( %s -> ( NN0 X. { 0 } ) = ( n e. NN0 |-> 0 ) )' % A0)
cc0 = w.s([w.s([w.s([], '0cn', '0 e. CC'), w.s([], '0z', '0 e. ZZ'), w.inst('climconst2')], 'mp2an', '( NN0 X. { 0 } ) ~~> 0') if False else
           w.s([closed(w, A0, '0cn', '0 e. CC'), closed(w, A0, '0z', '0 e. ZZ'), w.inst('climconst2')], 'syl2anc', '( %s -> ( ( ZZ>= ` 0 ) X. { 0 } ) ~~> 0 )' % A0)], 'id', '') if False else None
nn0z = w.s([w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'a1i', '( %s -> NN0 = ( ZZ>= ` 0 ) )' % A0)
ccn = w.s([closed(w, A0, '0cn', '0 e. CC'), closed(w, A0, '0z', '0 e. ZZ'), w.inst('climconst2')], 'syl2anc', '( %s -> ( ( ZZ>= ` 0 ) X. { 0 } ) ~~> 0 )' % A0)
ccn2 = w.s([w.s([nn0z], 'xpeq1d', '( %s -> ( NN0 X. { 0 } ) = ( ( ZZ>= ` 0 ) X. { 0 } ) )' % A0), ccn], 'eqbrtrd', '( %s -> ( NN0 X. { 0 } ) ~~> 0 )' % A0)
p0 = w.s([w.s([pmt, fcm], 'eqtr4d', '( %s -> %s = ( NN0 X. { 0 } ) )' % (A0, PSUM)), ccn2], 'eqbrtrd', '( %s -> %s ~~> 0 )' % (A0, PSUM))
ana0 = w.s(['1', '2'], 'rectintana', '( %s -> %s ~~> %s )' % (CTXa, PSUM, LHS))
ana = w.s([ctx, ana0], 'syl', '( %s -> %s ~~> %s )' % (A0, PSUM, LHS))
uni = w.s([ana, p0, w.inst('climuni')], 'syl2anc', '( %s -> %s = 0 )' % (A0, LHS))
# 2 pi i is nonzero
bs = w.s([ctx, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, BASE))
ab = w.s([bs, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
tri = w.s([bs, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Z ) )' % (A0, INTP, INTZ))
holo = w.s([bs, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
itz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTZ))
fcn = w.s([holo, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
hss = w.s([holo, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
crd = w.s([hss, w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
zmem = w.s([w.s([ab, itz], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTZ)), w.inst('crectinp')], 'syl', '( %s -> Z e. ( A crect B ) )' % A0)
fz = w.s([ff, w.s([crd, zmem], 'sseldd', '( %s -> Z e. D )' % A0)], 'ffvelcdmd', '( %s -> ( F ` Z ) e. CC )' % A0)
t2c = closed(w, A0, '2cn', '2 e. CC')
icn = closed(w, A0, 'ax-icn', '_i e. CC')
picn_ = closed(w, A0, 'picn', '_pi e. CC')
pine = w.s([closed(w, A0, 'pipos', '0 < _pi')], 'gt0ne0d', '( %s -> _pi =/= 0 )' % A0)
ipin = w.s([icn, picn_, closed(w, A0, 'ine0', '_i =/= 0'), pine], 'mulne0d', '( %s -> ( _i x. _pi ) =/= 0 )' % A0)
ipic = w.s([icn, picn_], 'mulcld', '( %s -> ( _i x. _pi ) e. CC )' % A0)
tne = w.s([t2c, ipic, closed(w, A0, '2ne0', '2 =/= 0'), ipin], 'mulne0d', '( %s -> %s =/= 0 )' % (A0, TPI))
tpic = w.s([t2c, ipic], 'mulcld', '( %s -> %s e. CC )' % (A0, TPI))
orx = w.s([w.s([tpic, fz, w.inst('mul0or')], 'syl2anc', '( %s -> ( %s = 0 <-> ( %s = 0 \\/ ( F ` Z ) = 0 ) ) )' % (A0, LHS, TPI)), uni], 'mpbid',
          '( %s -> ( %s = 0 \\/ ( F ` Z ) = 0 ) )' % (A0, TPI))
nots = w.s([tne], 'neneqd', '( %s -> -. %s = 0 )' % (A0, TPI))
oe = w.s([nots, w.inst('orel1')], 'syl', '( %s -> ( ( %s = 0 \\/ ( F ` Z ) = 0 ) -> ( F ` Z ) = 0 ) )' % (A0, TPI))
w.qed([oe, orx], 'mpd', '( %s -> ( F ` Z ) = 0 )' % A0)
run1(w, h=True)
