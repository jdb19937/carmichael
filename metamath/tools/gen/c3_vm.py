"""Sortie C3 section 9: the truncated von Mangoldt convolution identity."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

GG = '( DChr ` N )'
ZN = '( Z/nZ ` N )'
LH = '( ZRHom ` %s )' % ZN
DC = '( Base ` %s )' % GG
FL = '( 1 ... ( |_ ` Y ) )'
DVN = '{ x e. NN | x || e }'
BB = '( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` ( e / d ) ) ) x. ( e ^c -u Z ) ) )' % (LH, LH)
CC_ = '( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` ( ( d x. m ) / d ) ) ) x. ( ( d x. m ) ^c -u Z ) ) )' % (LH, LH)
LHSN = '( ( X ` ( %s ` e ) ) x. ( ( log ` e ) x. ( e ^c -u Z ) ) )' % LH
RHSD = '( ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( d ^c -u Z ) ) x. sum_ m e. ( 1 ... ( |_ ` ( Y / d ) ) ) ( ( X ` ( %s ` m ) ) x. ( m ^c -u Z ) ) )' % (LH, LH)


def dchyp(w):
    return [w.s([], 'eqid', '%s = %s' % (GG, GG)), w.s([], 'eqid', '%s = %s' % (ZN, ZN)),
            w.s([], 'eqid', '%s = %s' % (DC, DC)), w.s([], 'eqid', '%s = %s' % (LH, LH))]


w = W('vmachfin', 'The truncated Dirichlet convolution identity for the logarithmically weighted L-series of a character.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ ( Z e. CC /\\ Y e. RR ) )' % DC
nn = w.s([], 'simpll', '( %s -> N e. NN )' % A0)
xd = w.s([], 'simplr', '( %s -> X e. %s )' % (A0, DC))
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
yr = w.s([], 'simprr', '( %s -> Y e. RR )' % A0)
g, z, b, l = dchyp(w)
# the substitution hypothesis of dvdsflsumcom
sub1 = w.s([], 'oveq1', '( e = ( d x. m ) -> ( e / d ) = ( ( d x. m ) / d ) )')
sub2 = w.s([sub1], 'fveq2d', '( e = ( d x. m ) -> ( %s ` ( e / d ) ) = ( %s ` ( ( d x. m ) / d ) ) )' % (LH, LH))
sub3 = w.s([sub2], 'fveq2d', '( e = ( d x. m ) -> ( X ` ( %s ` ( e / d ) ) ) = ( X ` ( %s ` ( ( d x. m ) / d ) ) ) )' % (LH, LH))
sub4 = w.s([], 'oveq1', '( e = ( d x. m ) -> ( e ^c -u Z ) = ( ( d x. m ) ^c -u Z ) )')
sub5 = w.s([sub3, sub4], 'oveq12d',
           '( e = ( d x. m ) -> ( ( X ` ( %s ` ( e / d ) ) ) x. ( e ^c -u Z ) ) = ( ( X ` ( %s ` ( ( d x. m ) / d ) ) ) x. ( ( d x. m ) ^c -u Z ) ) )' % (LH, LH))
hS = w.s([sub5], 'oveq2d', '( e = ( d x. m ) -> %s = %s )' % (BB, CC_))
# the closure hypothesis
And = '( %s /\\ ( e e. %s /\\ d e. %s ) )' % (A0, FL, DVN)
nfl = w.s([], 'simprl', '( %s -> e e. %s )' % (And, FL))
ddv = w.s([], 'simprr', '( %s -> d e. %s )' % (And, DVN))
nnn = w.s([nfl, w.inst('elfznn')], 'syl', '( %s -> e e. NN )' % And)
dnn = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % DVN)], 'a1i', '( %s -> %s C_ NN )' % (And, DVN)), ddv], 'sseldd',
          '( %s -> d e. NN )' % And)
qdv = w.s([nnn, ddv, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( e / d ) e. %s )' % (And, DVN))
qnn = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % DVN)], 'a1i', '( %s -> %s C_ NN )' % (And, DVN)), qdv], 'sseldd',
          '( %s -> ( e / d ) e. NN )' % And)
xdn = w.s([xd], 'adantr', '( %s -> X e. %s )' % (And, DC))
cd1 = w.s([g, z, b, l, xdn, w.s([dnn], 'nnzd', '( %s -> d e. ZZ )' % And)], 'dchrzrhcl',
          '( %s -> ( X ` ( %s ` d ) ) e. CC )' % (And, LH))
cq1 = w.s([g, z, b, l, xdn, w.s([qnn], 'nnzd', '( %s -> ( e / d ) e. ZZ )' % And)], 'dchrzrhcl',
          '( %s -> ( X ` ( %s ` ( e / d ) ) ) e. CC )' % (And, LH))
lam = w.s([w.s([dnn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` d ) e. RR )' % And)], 'recnd',
          '( %s -> ( Lam ` d ) e. CC )' % And)
pn = w.s([w.s([w.s([nnn], 'nnrpd', '( %s -> e e. RR+ )' % And)], 'rpcnd', '( %s -> e e. CC )' % And),
          w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % And)], 'negcld', '( %s -> -u Z e. CC )' % And),
          w.inst('cxpcl')], 'syl2anc', '( %s -> ( e ^c -u Z ) e. CC )' % And)
hC = w.s([w.s([cd1, lam], 'mulcld', '( %s -> ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) e. CC )' % (And, LH)),
          w.s([cq1, pn], 'mulcld', '( %s -> ( ( X ` ( %s ` ( e / d ) ) ) x. ( e ^c -u Z ) ) e. CC )' % (And, LH))],
         'mulcld', '( %s -> %s e. CC )' % (And, BB))
com = w.s([hS, yr, hC], 'dvdsflsumcom',
          '( %s -> sum_ e e. %s sum_ d e. %s %s = sum_ d e. %s sum_ m e. ( 1 ... ( |_ ` ( Y / d ) ) ) %s )' % (A0, FL, DVN, BB, FL, CC_))

# ---- the left side: the inner divisor sum collapses by vmachsum -------------
Ae = '( %s /\\ e e. %s )' % (A0, FL)
Aed = '( %s /\\ d e. %s )' % (Ae, DVN)
eflA = w.s([], 'simpr', '( %s -> e e. %s )' % (Ae, FL))
ennA = w.s([eflA, w.inst('elfznn')], 'syl', '( %s -> e e. NN )' % Ae)
dd2 = w.s([], 'simpr', '( %s -> d e. %s )' % (Aed, DVN))
dnn2 = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % DVN)], 'a1i', '( %s -> %s C_ NN )' % (Aed, DVN)), dd2], 'sseldd',
           '( %s -> d e. NN )' % Aed)
enn2 = w.s([ennA], 'adantr', '( %s -> e e. NN )' % Aed)
qdv2 = w.s([enn2, dd2, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( e / d ) e. %s )' % (Aed, DVN))
qnn2 = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % DVN)], 'a1i', '( %s -> %s C_ NN )' % (Aed, DVN)), qdv2], 'sseldd',
           '( %s -> ( e / d ) e. NN )' % Aed)
xd2 = w.s([w.s([xd], 'adantr', '( %s -> X e. %s )' % (Ae, DC))], 'adantr', '( %s -> X e. %s )' % (Aed, DC))
cd2 = w.s([g, z, b, l, xd2, w.s([dnn2], 'nnzd', '( %s -> d e. ZZ )' % Aed)], 'dchrzrhcl',
          '( %s -> ( X ` ( %s ` d ) ) e. CC )' % (Aed, LH))
cq2 = w.s([g, z, b, l, xd2, w.s([qnn2], 'nnzd', '( %s -> ( e / d ) e. ZZ )' % Aed)], 'dchrzrhcl',
          '( %s -> ( X ` ( %s ` ( e / d ) ) ) e. CC )' % (Aed, LH))
lam2 = w.s([w.s([dnn2, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` d ) e. RR )' % Aed)], 'recnd',
           '( %s -> ( Lam ` d ) e. CC )' % Aed)
ecc = w.s([w.s([ennA], 'nnrpd', '( %s -> e e. RR+ )' % Ae)], 'rpcnd', '( %s -> e e. CC )' % Ae)
nzc = w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ae)], 'negcld', '( %s -> -u Z e. CC )' % Ae)
pe = w.s([ecc, nzc, w.inst('cxpcl')], 'syl2anc', '( %s -> ( e ^c -u Z ) e. CC )' % Ae)
pe2 = w.s([pe], 'adantr', '( %s -> ( e ^c -u Z ) e. CC )' % Aed)
SUMD = '( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( X ` ( %s ` ( e / d ) ) ) )' % (LH, LH)
reass = w.s([w.s([cd2, lam2], 'mulcld', '( %s -> ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) e. CC )' % (Aed, LH)),
             cq2, pe2], 'mulassd', '( %s -> ( %s x. ( e ^c -u Z ) ) = %s )' % (Aed, SUMD, BB))
inner = w.s([reass], 'sumeq2dv',
            '( %s -> sum_ d e. %s ( %s x. ( e ^c -u Z ) ) = sum_ d e. %s %s )' % (Ae, DVN, SUMD, DVN, BB))
dvfin = w.s([ennA, w.inst('dvdsfi')], 'syl', '( %s -> %s e. Fin )' % (Ae, DVN))
sdc = w.s([w.s([cd2, lam2], 'mulcld', '( %s -> ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) e. CC )' % (Aed, LH)), cq2],
          'mulcld', '( %s -> %s e. CC )' % (Aed, SUMD))
pull = w.s([dvfin, pe, sdc], 'fsummulc1',
           '( %s -> ( sum_ d e. %s %s x. ( e ^c -u Z ) ) = sum_ d e. %s ( %s x. ( e ^c -u Z ) ) )' % (Ae, DVN, SUMD, DVN, SUMD))
vch = w.s([w.s([w.s([nn, xd], 'jca', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC))], 'adantr',
                '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ae, DC)), ennA], 'x', 'x')
w.lines.pop()
vch = w.s([w.s([w.s([w.s([nn, xd], 'jca', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC))], 'adantr',
                     '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ae, DC)), ennA], 'jca',
                '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ e e. NN ) )' % (Ae, DC)), w.inst('vmachsum')], 'syl',
           '( %s -> sum_ d e. %s %s = ( ( X ` ( %s ` e ) ) x. ( log ` e ) ) )' % (Ae, DVN, SUMD, LH))
cex = w.s([g, z, b, l, w.s([xd], 'adantr', '( %s -> X e. %s )' % (Ae, DC)),
           w.s([ennA], 'nnzd', '( %s -> e e. ZZ )' % Ae)], 'dchrzrhcl', '( %s -> ( X ` ( %s ` e ) ) e. CC )' % (Ae, LH))
lge = w.s([w.s([w.s([ennA], 'nnrpd', '( %s -> e e. RR+ )' % Ae), w.inst('relogcl')], 'syl',
                '( %s -> ( log ` e ) e. RR )' % Ae)], 'recnd', '( %s -> ( log ` e ) e. CC )' % Ae)
fass = w.s([cex, lge, pe], 'mulassd',
           '( %s -> ( ( ( X ` ( %s ` e ) ) x. ( log ` e ) ) x. ( e ^c -u Z ) ) = %s )' % (Ae, LH, LHSN))
lhs1 = w.s([w.s([w.s([vch], 'oveq1d',
                      '( %s -> ( sum_ d e. %s %s x. ( e ^c -u Z ) ) = ( ( ( X ` ( %s ` e ) ) x. ( log ` e ) ) x. ( e ^c -u Z ) ) )' % (Ae, DVN, SUMD, LH)),
                 fass], 'eqtrd',
                '( %s -> ( sum_ d e. %s %s x. ( e ^c -u Z ) ) = %s )' % (Ae, DVN, SUMD, LHSN))], 'idi',
           '( %s -> ( sum_ d e. %s %s x. ( e ^c -u Z ) ) = %s )' % (Ae, DVN, SUMD, LHSN))
lhs2 = w.s([w.s([w.s([pull], 'eqcomd',
                      '( %s -> sum_ d e. %s ( %s x. ( e ^c -u Z ) ) = ( sum_ d e. %s %s x. ( e ^c -u Z ) ) )' % (Ae, DVN, SUMD, DVN, SUMD)),
                 lhs1], 'eqtrd', '( %s -> sum_ d e. %s ( %s x. ( e ^c -u Z ) ) = %s )' % (Ae, DVN, SUMD, LHSN))], 'idi',
           '( %s -> sum_ d e. %s ( %s x. ( e ^c -u Z ) ) = %s )' % (Ae, DVN, SUMD, LHSN))
lhs3 = w.s([w.s([inner], 'eqcomd', '( %s -> sum_ d e. %s %s = sum_ d e. %s ( %s x. ( e ^c -u Z ) ) )' % (Ae, DVN, BB, DVN, SUMD)),
            lhs2], 'eqtrd', '( %s -> sum_ d e. %s %s = %s )' % (Ae, DVN, BB, LHSN))
LHS = w.s([lhs3], 'sumeq2dv', '( %s -> sum_ e e. %s sum_ d e. %s %s = sum_ e e. %s %s )' % (A0, FL, DVN, BB, FL, LHSN))

# ---- the right side --------------------------------------------------------
FLD = '( 1 ... ( |_ ` ( Y / d ) ) )'
Ad = '( %s /\\ d e. %s )' % (A0, FL)
Adm = '( %s /\\ m e. %s )' % (Ad, FLD)
XM = '( ( X ` ( %s ` m ) ) x. ( m ^c -u Z ) )' % LH
KD = '( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( d ^c -u Z ) )' % LH
dfl = w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, FL))
dnn3 = w.s([dfl, w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % Ad)
mfl = w.s([], 'simpr', '( %s -> m e. %s )' % (Adm, FLD))
mnn = w.s([mfl, w.inst('elfznn')], 'syl', '( %s -> m e. NN )' % Adm)
dnn4 = w.s([dnn3], 'adantr', '( %s -> d e. NN )' % Adm)
xdm = w.s([w.s([xd], 'adantr', '( %s -> X e. %s )' % (Ad, DC))], 'adantr', '( %s -> X e. %s )' % (Adm, DC))
dcc = w.s([dnn4], 'nncnd', '( %s -> d e. CC )' % Adm)
mcc = w.s([mnn], 'nncnd', '( %s -> m e. CC )' % Adm)
dne = w.s([dnn4], 'nnne0d', '( %s -> d =/= 0 )' % Adm)
can = w.s([mcc, dcc, dne, w.inst('divcan3')], 'syl3anc', '( %s -> ( ( d x. m ) / d ) = m )' % Adm)
zcm = w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad)], 'adantr', '( %s -> Z e. CC )' % Adm)], 'negcld',
          '( %s -> -u Z e. CC )' % Adm)
mcx = w.s([w.s([w.s([dnn4], 'nnred', '( %s -> d e. RR )' % Adm),
                w.s([w.s([dnn4], 'nnrpd', '( %s -> d e. RR+ )' % Adm)], 'rpge0d', '( %s -> 0 <_ d )' % Adm)], 'jca',
               '( %s -> ( d e. RR /\\ 0 <_ d ) )' % Adm),
           w.s([w.s([mnn], 'nnred', '( %s -> m e. RR )' % Adm),
                w.s([w.s([mnn], 'nnrpd', '( %s -> m e. RR+ )' % Adm)], 'rpge0d', '( %s -> 0 <_ m )' % Adm)], 'jca',
               '( %s -> ( m e. RR /\\ 0 <_ m ) )' % Adm), zcm, w.inst('mulcxp')], 'syl3anc',
          '( %s -> ( ( d x. m ) ^c -u Z ) = ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) )' % Adm)
cbody = w.s([w.s([can], 'fveq2d', '( %s -> ( %s ` ( ( d x. m ) / d ) ) = ( %s ` m ) )' % (Adm, LH, LH))], 'fveq2d',
            '( %s -> ( X ` ( %s ` ( ( d x. m ) / d ) ) ) = ( X ` ( %s ` m ) ) )' % (Adm, LH, LH))
c1 = w.s([cbody, mcx], 'oveq12d',
         '( %s -> ( ( X ` ( %s ` ( ( d x. m ) / d ) ) ) x. ( ( d x. m ) ^c -u Z ) ) = ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) )' % (Adm, LH, LH))
c2 = w.s([c1], 'oveq2d',
         '( %s -> %s = ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) )' % (Adm, CC_, LH, LH))
# regroup the four factors
cdm = w.s([g, z, b, l, xdm, w.s([dnn4], 'nnzd', '( %s -> d e. ZZ )' % Adm)], 'dchrzrhcl',
          '( %s -> ( X ` ( %s ` d ) ) e. CC )' % (Adm, LH))
cmm = w.s([g, z, b, l, xdm, w.s([mnn], 'nnzd', '( %s -> m e. ZZ )' % Adm)], 'dchrzrhcl',
          '( %s -> ( X ` ( %s ` m ) ) e. CC )' % (Adm, LH))
lamm = w.s([w.s([dnn4, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` d ) e. RR )' % Adm)], 'recnd',
           '( %s -> ( Lam ` d ) e. CC )' % Adm)
adm = w.s([cdm, lamm], 'mulcld', '( %s -> ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) e. CC )' % (Adm, LH))
pdm = w.s([dcc, zcm, w.inst('cxpcl')], 'syl2anc', '( %s -> ( d ^c -u Z ) e. CC )' % Adm)
pmm = w.s([mcc, zcm, w.inst('cxpcl')], 'syl2anc', '( %s -> ( m ^c -u Z ) e. CC )' % Adm)
as1 = w.s([adm, cmm, w.s([pdm, pmm], 'mulcld', '( %s -> ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) e. CC )' % Adm)],
          'mulassd',
          '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( X ` ( %s ` m ) ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) = ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) )' % (Adm, LH, LH, LH, LH))
w.lines.pop()
as1 = w.s([adm, cmm, w.s([pdm, pmm], 'mulcld', '( %s -> ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) e. CC )' % Adm)],
          'mulassd',
          '( %s -> ( ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( X ` ( %s ` m ) ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) = ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) )' % (Adm, LH, LH, LH, LH))
m4 = w.s([adm, cmm, pdm, pmm], 'mul4d',
         '( %s -> ( ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( X ` ( %s ` m ) ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) = ( ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( d ^c -u Z ) ) x. ( ( X ` ( %s ` m ) ) x. ( m ^c -u Z ) ) ) )' % (Adm, LH, LH, LH, LH))
c3 = w.s([w.s([c2], 'eqcomd',
               '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) = %s )' % (Adm, LH, LH, CC_))],
          'idi', '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) = %s )' % (Adm, LH, LH, CC_))
cfin = w.s([w.s([w.s([as1], 'eqcomd',
                      '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) = ( ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( X ` ( %s ` m ) ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) )' % (Adm, LH, LH, LH, LH)),
                 m4], 'eqtrd',
                '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) = ( %s x. %s ) )' % (Adm, LH, LH, KD, XM))], 'idi',
           '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( ( X ` ( %s ` m ) ) x. ( ( d ^c -u Z ) x. ( m ^c -u Z ) ) ) ) = ( %s x. %s ) )' % (Adm, LH, LH, KD, XM))
cc2 = w.s([c2, cfin], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (Adm, CC_, KD, XM))
inm = w.s([cc2], 'sumeq2dv', '( %s -> sum_ m e. %s %s = sum_ m e. %s ( %s x. %s ) )' % (Ad, FLD, CC_, FLD, KD, XM))
kdcl = w.s([w.s([w.s([g, z, b, l, w.s([xd], 'adantr', '( %s -> X e. %s )' % (Ad, DC)),
                      w.s([dnn3], 'nnzd', '( %s -> d e. ZZ )' % Ad)], 'dchrzrhcl',
                     '( %s -> ( X ` ( %s ` d ) ) e. CC )' % (Ad, LH)),
                 w.s([w.s([dnn3, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` d ) e. RR )' % Ad)], 'recnd',
                     '( %s -> ( Lam ` d ) e. CC )' % Ad)], 'mulcld',
                '( %s -> ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) e. CC )' % (Ad, LH)),
            w.s([w.s([dnn3], 'nncnd', '( %s -> d e. CC )' % Ad),
                 w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad)], 'negcld', '( %s -> -u Z e. CC )' % Ad),
                 w.inst('cxpcl')], 'syl2anc', '( %s -> ( d ^c -u Z ) e. CC )' % Ad)], 'mulcld',
           '( %s -> %s e. CC )' % (Ad, KD))
xmcl = w.s([cmm, pmm], 'mulcld', '( %s -> %s e. CC )' % (Adm, XM))
pull2 = w.s([w.s([], 'fzfid', '( %s -> %s e. Fin )' % (Ad, FLD)), kdcl, xmcl], 'fsummulc2',
            '( %s -> ( %s x. sum_ m e. %s %s ) = sum_ m e. %s ( %s x. %s ) )' % (Ad, KD, FLD, XM, FLD, KD, XM))
rhs = w.s([inm, w.s([pull2], 'eqcomd', '( %s -> sum_ m e. %s ( %s x. %s ) = %s )' % (Ad, FLD, KD, XM, RHSD))], 'eqtrd',
          '( %s -> sum_ m e. %s %s = %s )' % (Ad, FLD, CC_, RHSD))
RHS = w.s([rhs], 'sumeq2dv', '( %s -> sum_ d e. %s sum_ m e. %s %s = sum_ d e. %s %s )' % (A0, FL, FLD, CC_, FL, RHSD))
w.qed([w.s([w.s([LHS], 'eqcomd', '( %s -> sum_ e e. %s %s = sum_ e e. %s sum_ d e. %s %s )' % (A0, FL, LHSN, FL, DVN, BB)), com],
           'eqtrd', '( %s -> sum_ e e. %s %s = sum_ d e. %s sum_ m e. %s %s )' % (A0, FL, LHSN, FL, FLD, CC_)), RHS],
      'eqtrd', '( %s -> sum_ e e. %s %s = sum_ d e. %s %s )' % (A0, FL, LHSN, FL, RHSD)); run3(w)
