"""C7b section 1, the finite material: dconvfin (the rearrangement by
dvdsflsumcom), dconvdif (the difference of the convolution partial sum and
the product of partial sums as one sum)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *

ABZN = '( ( A : NN --> CC /\\ B : NN --> CC ) /\\ ( Z e. CC /\\ N e. NN ) )'
FLN = '( 1 ... ( |_ ` N ) )'
N1 = '( 1 ... N )'


def DVN(n):
    return '{ x e. NN | x || %s }' % n


def FLDV(d):
    return '( 1 ... ( |_ ` ( N / %s ) ) )' % d


def abzn(w, A0):
    af = w.s([], 'simpll', '( %s -> A : NN --> CC )' % A0)
    bf = w.s([], 'simplr', '( %s -> B : NN --> CC )' % A0)
    zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
    nn = w.s([], 'simprr', '( %s -> N e. NN )' % A0)
    return af, bf, zc, nn


def fln_eq(w, A0, nn):
    """( A0 -> ( 1 ... N ) = ( 1 ... ( |_ ` N ) ) )"""
    fl = w.s([w.s([nn], 'nnzd', '( %s -> N e. ZZ )' % A0), w.inst('flid')], 'syl', '( %s -> ( |_ ` N ) = N )' % A0)
    return w.s([w.s([fl], 'eqcomd', '( %s -> N = ( |_ ` N ) )' % A0)], 'oveq2d', '( %s -> %s = %s )' % (A0, N1, FLN))


# ---------------------------------------------------------------- dconvfin
w = W('dconvfin', 'The partial sum of the Dirichlet convolution series rearranged by ~ dvdsflsumcom : '
      '` sum_ i <_ N ( sum_ d | i a_d b_( i / d ) ) i ^c -u Z = sum_ e <_ N a_e e ^c -u Z sum_ i <_ N / e b_i i ^c -u Z ` .')
A0 = ABZN
af, bf, zc, nn = abzn(w, A0)
BB = '( ( ( A ` d ) x. ( B ` ( n / d ) ) ) x. ( n ^c -u Z ) )'
idn = w.s([], 'id', '( n = ( d x. m ) -> n = ( d x. m ) )')
hS, CC_ = w.congr(BB, {'n': '( d x. m )'}, 'n = ( d x. m )', {'n': idn})
assert CC_ == '( ( ( A ` d ) x. ( B ` ( ( d x. m ) / d ) ) ) x. ( ( d x. m ) ^c -u Z ) )', CC_
nr = w.s([nn], 'nnred', '( %s -> N e. RR )' % A0)
And = '( %s /\\ ( n e. %s /\\ d e. %s ) )' % (A0, FLN, DVN('n'))
nfl = w.s([], 'simprl', '( %s -> n e. %s )' % (And, FLN))
ddv = w.s([], 'simprr', '( %s -> d e. %s )' % (And, DVN('n')))
nnn = w.s([nfl, w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % And)
dss = w.s([w.s([], 'ssrab2', '%s C_ NN' % DVN('n'))], 'a1i', '( %s -> %s C_ NN )' % (And, DVN('n')))
dnn = w.s([dss, ddv], 'sseldd', '( %s -> d e. NN )' % And)
qdv = w.s([nnn, ddv, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( n / d ) e. %s )' % (And, DVN('n')))
qnn = w.s([dss, qdv], 'sseldd', '( %s -> ( n / d ) e. NN )' % And)
ad = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % And), dnn], 'ffvelcdmd', '( %s -> ( A ` d ) e. CC )' % And)
bq = w.s([w.s([bf], 'adantr', '( %s -> B : NN --> CC )' % And), qnn], 'ffvelcdmd', '( %s -> ( B ` ( n / d ) ) e. CC )' % And)
pn = cxpz(w, And, 'n', nnn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % And))
hC = w.s([w.s([ad, bq], 'mulcld', '( %s -> ( ( A ` d ) x. ( B ` ( n / d ) ) ) e. CC )' % And), pn], 'mulcld', '( %s -> %s e. CC )' % (And, BB))
com = w.s([hS, nr, hC], 'dvdsflsumcom',
          '( %s -> sum_ n e. %s sum_ d e. %s %s = sum_ d e. %s sum_ m e. %s %s )' % (A0, FLN, DVN('n'), BB, FLN, FLDV('d'), CC_))
# ---- the left side
idi = w.s([], 'id', '( i = n -> i = n )')
cgi, ctn = w.congr(CTRM('i'), {'i': 'n'}, 'i = n', {'i': idi})
assert ctn == CTRM('n'), ctn
cb1 = w.s([cgi], 'cbvsumv', '%s = sum_ n e. %s %s' % (CPS('N'), N1, CTRM('n')))
fleq = fln_eq(w, A0, nn)
l2 = w.s([fleq], 'sumeq1d', '( %s -> sum_ n e. %s %s = sum_ n e. %s %s )' % (A0, N1, CTRM('n'), FLN, CTRM('n')))
An = '( %s /\\ n e. %s )' % (A0, FLN)
nnA = w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (An, FLN)), w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % An)
dfin = w.s([nnA, w.inst('dvdsfi')], 'syl', '( %s -> %s e. Fin )' % (An, DVN('n')))
pnA = cxpz(w, An, 'n', nnA, w.s([zc], 'adantr', '( %s -> Z e. CC )' % An))
Anq = '( %s /\\ d e. %s )' % (An, DVN('n'))
ddv2 = w.s([], 'simpr', '( %s -> d e. %s )' % (Anq, DVN('n')))
dss2 = w.s([w.s([], 'ssrab2', '%s C_ NN' % DVN('n'))], 'a1i', '( %s -> %s C_ NN )' % (Anq, DVN('n')))
dnn2 = w.s([dss2, ddv2], 'sseldd', '( %s -> d e. NN )' % Anq)
nnn2 = w.s([nnA], 'adantr', '( %s -> n e. NN )' % Anq)
qnn2 = w.s([dss2, w.s([nnn2, ddv2, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( n / d ) e. %s )' % (Anq, DVN('n')))], 'sseldd', '( %s -> ( n / d ) e. NN )' % Anq)
ad2 = w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % An)], 'adantr', '( %s -> A : NN --> CC )' % Anq), dnn2], 'ffvelcdmd', '( %s -> ( A ` d ) e. CC )' % Anq)
bq2 = w.s([w.s([w.s([bf], 'adantr', '( %s -> B : NN --> CC )' % An)], 'adantr', '( %s -> B : NN --> CC )' % Anq), qnn2], 'ffvelcdmd', '( %s -> ( B ` ( n / d ) ) e. CC )' % Anq)
sm = w.s([ad2, bq2], 'mulcld', '( %s -> ( ( A ` d ) x. ( B ` ( n / d ) ) ) e. CC )' % Anq)
pull = w.s([dfin, pnA, sm], 'fsummulc1', '( %s -> %s = sum_ d e. %s %s )' % (An, CTRM('n'), DVN('n'), BB))
l3 = w.s([pull], 'sumeq2dv', '( %s -> sum_ n e. %s %s = sum_ n e. %s sum_ d e. %s %s )' % (A0, FLN, CTRM('n'), FLN, DVN('n'), BB))
LHS = w.s([w.s([w.s([cb1], 'a1i', '( %s -> %s = sum_ n e. %s %s )' % (A0, CPS('N'), N1, CTRM('n'))), l2], 'eqtrd',
               '( %s -> %s = sum_ n e. %s %s )' % (A0, CPS('N'), FLN, CTRM('n'))), l3], 'eqtrd',
          '( %s -> %s = sum_ n e. %s sum_ d e. %s %s )' % (A0, CPS('N'), FLN, DVN('n'), BB))
# ---- the right side
Ad = '( %s /\\ d e. %s )' % (A0, FLN)
Adm = '( %s /\\ m e. %s )' % (Ad, FLDV('d'))
dnn3 = w.s([w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, FLN)), w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % Ad)
mnn = w.s([w.s([], 'simpr', '( %s -> m e. %s )' % (Adm, FLDV('d'))), w.inst('elfznn')], 'syl', '( %s -> m e. NN )' % Adm)
dnn4 = w.s([dnn3], 'adantr', '( %s -> d e. NN )' % Adm)
dcc = w.s([dnn4], 'nncnd', '( %s -> d e. CC )' % Adm)
mcc = w.s([mnn], 'nncnd', '( %s -> m e. CC )' % Adm)
dne = w.s([dnn4], 'nnne0d', '( %s -> d =/= 0 )' % Adm)
can = w.s([mcc, dcc, dne, w.inst('divcan3')], 'syl3anc', '( %s -> ( ( d x. m ) / d ) = m )' % Adm)
zcm = w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad)], 'adantr', '( %s -> Z e. CC )' % Adm)], 'negcld', '( %s -> -u Z e. CC )' % Adm)
mcx = w.s([w.s([dnn4], 'nnred', '( %s -> d e. RR )' % Adm), w.s([w.s([dnn4], 'nnrpd', '( %s -> d e. RR+ )' % Adm)], 'rpge0d', '( %s -> 0 <_ d )' % Adm),
           w.s([mnn], 'nnred', '( %s -> m e. RR )' % Adm), w.s([w.s([mnn], 'nnrpd', '( %s -> m e. RR+ )' % Adm)], 'rpge0d', '( %s -> 0 <_ m )' % Adm), zcm],
          'mulcxpd', '( %s -> ( ( d x. m ) ^c -u Z ) = ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) )' % Adm)
c1 = w.s([w.s([w.s([can], 'fveq2d', '( %s -> ( B ` ( ( d x. m ) / d ) ) = ( B ` m ) )' % Adm)], 'oveq2d',
               '( %s -> ( ( A ` d ) x. ( B ` ( ( d x. m ) / d ) ) ) = ( ( A ` d ) x. ( B ` m ) ) )' % Adm), mcx], 'oveq12d',
         '( %s -> %s = ( ( ( A ` d ) x. ( B ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) )' % (Adm, CC_))
adm = w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ad)], 'adantr', '( %s -> A : NN --> CC )' % Adm), dnn4], 'ffvelcdmd', '( %s -> ( A ` d ) e. CC )' % Adm)
bmm = w.s([w.s([w.s([bf], 'adantr', '( %s -> B : NN --> CC )' % Ad)], 'adantr', '( %s -> B : NN --> CC )' % Adm), mnn], 'ffvelcdmd', '( %s -> ( B ` m ) e. CC )' % Adm)
pdm = w.s([dcc, zcm], 'cxpcld', '( %s -> ( d ^c -u Z ) e. CC )' % Adm)
pmm = w.s([mcc, zcm], 'cxpcld', '( %s -> ( m ^c -u Z ) e. CC )' % Adm)
m4 = w.s([adm, bmm, pdm, pmm], 'mul4d', '( %s -> ( ( ( A ` d ) x. ( B ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) = ( %s x. %s ) )' % (Adm, TRM('A', 'd'), TRM('B', 'm')))
cc2 = w.s([c1, m4], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (Adm, CC_, TRM('A', 'd'), TRM('B', 'm')))
inm = w.s([cc2], 'sumeq2dv', '( %s -> sum_ m e. %s %s = sum_ m e. %s ( %s x. %s ) )' % (Ad, FLDV('d'), CC_, FLDV('d'), TRM('A', 'd'), TRM('B', 'm')))
kdcl = trmcl(w, Ad, 'A', 'd', w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ad), dnn3, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad))
xmcl = w.s([bmm, pmm], 'mulcld', '( %s -> %s e. CC )' % (Adm, TRM('B', 'm')))
pull2 = w.s([fsumfin(w, Ad, '( |_ ` ( N / d ) )'), kdcl, xmcl], 'fsummulc2',
            '( %s -> ( %s x. sum_ m e. %s %s ) = sum_ m e. %s ( %s x. %s ) )' % (Ad, TRM('A', 'd'), FLDV('d'), TRM('B', 'm'), FLDV('d'), TRM('A', 'd'), TRM('B', 'm')))
cbm = w.s([w.s([trmsub(w, 'B', 'i', 'Z', 'm')], 'cbvsumv', 'sum_ m e. %s %s = %s' % (FLDV('d'), TRM('B', 'm'), PS('B', '( |_ ` ( N / d ) )')))], 'oveq2i',
          '( %s x. sum_ m e. %s %s ) = ( %s x. %s )' % (TRM('A', 'd'), FLDV('d'), TRM('B', 'm'), TRM('A', 'd'), PS('B', '( |_ ` ( N / d ) )')))
rhs = w.s([w.s([inm, w.s([pull2], 'eqcomd', '( %s -> sum_ m e. %s ( %s x. %s ) = ( %s x. sum_ m e. %s %s ) )' % (Ad, FLDV('d'), TRM('A', 'd'), TRM('B', 'm'), TRM('A', 'd'), FLDV('d'), TRM('B', 'm')))],
               'eqtrd', '( %s -> sum_ m e. %s %s = ( %s x. sum_ m e. %s %s ) )' % (Ad, FLDV('d'), CC_, TRM('A', 'd'), FLDV('d'), TRM('B', 'm'))),
           w.s([cbm], 'a1i', '( %s -> ( %s x. sum_ m e. %s %s ) = ( %s x. %s ) )' % (Ad, TRM('A', 'd'), FLDV('d'), TRM('B', 'm'), TRM('A', 'd'), PS('B', '( |_ ` ( N / d ) )')))],
          'eqtrd', '( %s -> sum_ m e. %s %s = ( %s x. %s ) )' % (Ad, FLDV('d'), CC_, TRM('A', 'd'), PS('B', '( |_ ` ( N / d ) )')))
RD = '( %s x. %s )' % (TRM('A', 'd'), PS('B', '( |_ ` ( N / d ) )'))
RE = '( %s x. %s )' % (TRM('A', 'e'), PS('B', '( |_ ` ( N / e ) )'))
r1 = w.s([rhs], 'sumeq2dv', '( %s -> sum_ d e. %s sum_ m e. %s %s = sum_ d e. %s %s )' % (A0, FLN, FLDV('d'), CC_, FLN, RD))
r2 = w.s([w.s([fleq], 'eqcomd', '( %s -> %s = %s )' % (A0, FLN, N1))], 'sumeq1d', '( %s -> sum_ d e. %s %s = sum_ d e. %s %s )' % (A0, FLN, RD, N1, RD))
idd = w.s([], 'id', '( d = e -> d = e )')
cgd, rde = w.congr(RD, {'d': 'e'}, 'd = e', {'d': idd})
assert rde == RE, rde
r3 = w.s([w.s([cgd], 'cbvsumv', 'sum_ d e. %s %s = sum_ e e. %s %s' % (N1, RD, N1, RE))], 'a1i', '( %s -> sum_ d e. %s %s = sum_ e e. %s %s )' % (A0, N1, RD, N1, RE))
RHS = w.s([w.s([r1, r2], 'eqtrd', '( %s -> sum_ d e. %s sum_ m e. %s %s = sum_ d e. %s %s )' % (A0, FLN, FLDV('d'), CC_, N1, RD)), r3], 'eqtrd',
          '( %s -> sum_ d e. %s sum_ m e. %s %s = sum_ e e. %s %s )' % (A0, FLN, FLDV('d'), CC_, N1, RE))
w.qed([w.s([LHS, com], 'eqtrd', '( %s -> %s = sum_ d e. %s sum_ m e. %s %s )' % (A0, CPS('N'), FLN, FLDV('d'), CC_)), RHS], 'eqtrd',
      '( %s -> %s = sum_ e e. %s %s )' % (A0, CPS('N'), N1, RE))
run7b(w)


# ---------------------------------------------------------------- dconvdif
w = W('dconvdif', 'The difference of the convolution partial sum and the product of the two partial sums as one sum: '
      '` sum_ e <_ N a_e e ^c -u Z ( sum_ i <_ N / e b_i i ^c -u Z - sum_ i <_ N b_i i ^c -u Z ) ` .')
A0 = ABZN
af, bf, zc, nn = abzn(w, A0)
PE = PS('B', '( |_ ` ( N / e ) )')
Q = PS('B', 'N')
TE = TRM('A', 'e')
fin = w.s([], 'dconvfin', '( %s -> %s = sum_ e e. %s ( %s x. %s ) )' % (A0, CPS('N'), N1, TE, PE))
Ae = '( %s /\\ e e. %s )' % (A0, N1)
enn = w.s([w.s([], 'simpr', '( %s -> e e. %s )' % (Ae, N1)), w.inst('elfznn')], 'syl', '( %s -> e e. NN )' % Ae)
te = trmcl(w, Ae, 'A', 'e', w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ae), enn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ae))


def pscl(ante, M, bfa, zca):
    """( ante -> PS(B,M) e. CC )"""
    Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (ante, M)
    inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (Ai, M)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
    ti = trmcl(w, Ai, 'B', 'i', w.s([bfa], 'adantr', '( %s -> B : NN --> CC )' % Ai), inn, w.s([zca], 'adantr', '( %s -> Z e. CC )' % Ai))
    return w.s([fsumfin(w, ante, M), ti], 'fsumcl', '( %s -> %s e. CC )' % (ante, PS('B', M)))


bfe = w.s([bf], 'adantr', '( %s -> B : NN --> CC )' % Ae)
zce = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ae)
pe = pscl(Ae, '( |_ ` ( N / e ) )', bfe, zce)
q0 = pscl(A0, 'N', bf, zc)
qe = w.s([q0], 'adantr', '( %s -> %s e. CC )' % (Ae, Q))
# the product of partial sums as a sum over e
cbA = w.s([trmsub(w, 'A', 'e', 'Z', 'i')], 'cbvsumv', '%s = sum_ e e. %s %s' % (PS('A', 'N'), N1, TE))
cbA2 = w.s([cbA], 'oveq1i', '( %s x. %s ) = ( sum_ e e. %s %s x. %s )' % (PS('A', 'N'), Q, N1, TE, Q))
m1 = w.s([fsumfin(w, A0, 'N'), q0, te], 'fsummulc1', '( %s -> ( sum_ e e. %s %s x. %s ) = sum_ e e. %s ( %s x. %s ) )' % (A0, N1, TE, Q, N1, TE, Q))
prod = w.s([w.s([cbA2], 'a1i', '( %s -> ( %s x. %s ) = ( sum_ e e. %s %s x. %s ) )' % (A0, PS('A', 'N'), Q, N1, TE, Q)), m1], 'eqtrd',
           '( %s -> ( %s x. %s ) = sum_ e e. %s ( %s x. %s ) )' % (A0, PS('A', 'N'), Q, N1, TE, Q))
lhs = w.s([fin, prod], 'oveq12d', '( %s -> ( %s - ( %s x. %s ) ) = ( sum_ e e. %s ( %s x. %s ) - sum_ e e. %s ( %s x. %s ) ) )' % (
    A0, CPS('N'), PS('A', 'N'), Q, N1, TE, PE, N1, TE, Q))
tp = w.s([te, pe], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Ae, TE, PE))
tq = w.s([te, qe], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Ae, TE, Q))
sub_ = w.s([fsumfin(w, A0, 'N'), tp, tq], 'fsumsub', '( %s -> sum_ e e. %s ( ( %s x. %s ) - ( %s x. %s ) ) = ( sum_ e e. %s ( %s x. %s ) - sum_ e e. %s ( %s x. %s ) ) )' % (
    A0, N1, TE, PE, TE, Q, N1, TE, PE, N1, TE, Q))
dis = w.s([te, pe, qe], 'subdid', '( %s -> ( %s x. ( %s - %s ) ) = ( ( %s x. %s ) - ( %s x. %s ) ) )' % (Ae, TE, PE, Q, TE, PE, TE, Q))
dsum = w.s([dis], 'sumeq2dv', '( %s -> sum_ e e. %s ( %s x. ( %s - %s ) ) = sum_ e e. %s ( ( %s x. %s ) - ( %s x. %s ) ) )' % (A0, N1, TE, PE, Q, N1, TE, PE, TE, Q))
rhs = w.s([dsum, sub_], 'eqtrd', '( %s -> sum_ e e. %s ( %s x. ( %s - %s ) ) = ( sum_ e e. %s ( %s x. %s ) - sum_ e e. %s ( %s x. %s ) ) )' % (
    A0, N1, TE, PE, Q, N1, TE, PE, N1, TE, Q))
w.qed([lhs, rhs], 'eqtr4d', '( %s -> ( %s - ( %s x. %s ) ) = sum_ e e. %s ( %s x. ( %s - %s ) ) )' % (A0, CPS('N'), PS('A', 'N'), Q, N1, TE, PE, Q))
run7b(w)
