"""C4, Gamma block 5: the gamma function at a positive real, and the strip bound."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

RZ = '( Re ` Z )'
EZ = EUT('Z'); EX = EUT(RZ); ER = EUT('X')
SR = 'seq 1 ( x. , %s )' % ER
XP = '( X e. RR /\\ 0 < X )'

# ---------------------------------------------------------------- eutrrp
A0 = '( %s /\\ M e. NN )' % XP
w = W('eutrrp', 'Euler\'s term ( ~ eutval ) at a positive real argument is a '
      'positive real.')
xr = w.s([], 'simpll', '( %s -> X e. RR )' % A0)
x0 = w.s([], 'simplr', '( %s -> 0 < X )' % A0)
mn = w.s([], 'simpr', '( %s -> M e. NN )' % A0)
xrp = w.s([xr, x0], 'elrpd', '( %s -> X e. RR+ )' % A0)
mrp = w.s([mn], 'nnrpd', '( %s -> M e. RR+ )' % A0)
one = w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % A0)
qrp = w.s([w.s([mrp, one], 'rpaddcld', '( %s -> ( M + 1 ) e. RR+ )' % A0), mrp], 'rpdivcld',
          '( %s -> ( ( M + 1 ) / M ) e. RR+ )' % A0)
num = w.s([qrp, xr], 'rpcxpcld', '( %s -> ( ( ( M + 1 ) / M ) ^c X ) e. RR+ )' % A0)
den = w.s([w.s([xrp, mrp], 'rpdivcld', '( %s -> ( X / M ) e. RR+ )' % A0), one], 'rpaddcld',
          '( %s -> ( ( X / M ) + 1 ) e. RR+ )' % A0)
v = w.s([mn, w.inst('eutval')], 'syl', '( %s -> ( %s ` M ) = %s )' % (A0, ER, EUTB('X', 'M')))
w.qed([v, w.s([num, den], 'rpdivcld', '( %s -> %s e. RR+ )' % (A0, EUTB('X', 'M')))], 'eqeltrd',
      '( %s -> ( %s ` M ) e. RR+ )' % (A0, ER))
run4(w)

# ---------------------------------------------------------------- gamrre
w = W('gamrre', 'The gamma function at a positive real argument is real: its '
      'Euler product ( ~ gamcvg2 ) has real partial products.')
xr = w.s([], 'simpl', '( %s -> X e. RR )' % XP)
x0 = w.s([], 'simpr', '( %s -> 0 < X )' % XP)
xc = w.s([xr], 'recnd', '( %s -> X e. CC )' % XP)
xre = w.s([xr], 'rered', '( %s -> ( Re ` X ) = X )' % XP)
dx = w.s([w.s([xc, w.s([x0, xre], 'breqtrrd', '( %s -> 0 < ( Re ` X ) )' % XP)], 'jca',
               '( %s -> ( X e. CC /\\ 0 < ( Re ` X ) ) )' % XP), w.inst('zrenn')], 'syl',
         '( %s -> X e. ( CC \\ ( ZZ \\ NN ) ) )' % XP)
er = w.s([], 'eqid', '%s = %s' % (ER, ER))
cv = w.s([er, dx], 'gamcvg2', '( %s -> %s ~~> ( ( _G ` X ) x. X ) )' % (XP, SR))
PK = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % XP
ku1 = w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % PK)
PA = '( %s /\\ a e. ( 1 ... k ) )' % PK
ann = w.s([w.s([], 'simpr', '( %s -> a e. ( 1 ... k ) )' % PA), w.inst('elfznn')], 'syl',
          '( %s -> a e. NN )' % PA)
xra = w.s([], 'simplll', '( %s -> X e. RR )' % PA)
x0a = w.s([], 'simpllr', '( %s -> 0 < X )' % PA)
era = w.s([w.s([w.s([xra, x0a], 'jca', '( %s -> %s )' % (PA, XP)), ann], 'jca',
                '( %s -> ( %s /\\ a e. NN ) )' % (PA, XP)), w.inst('eutrrp')], 'syl',
          '( %s -> ( %s ` a ) e. RR+ )' % (PA, ER))
erar = w.s([era], 'rpred', '( %s -> ( %s ` a ) e. RR )' % (PA, ER))
PB = '( %s /\\ ( a e. RR /\\ b e. RR ) )' % PK
mulr = w.s([w.s([], 'simprl', '( %s -> a e. RR )' % PB), w.s([], 'simprr', '( %s -> b e. RR )' % PB)],
           'remulcld', '( %s -> ( a x. b ) e. RR )' % PB)
sr = w.s([ku1, erar, mulr], 'seqcl', '( %s -> ( %s ` k ) e. RR )' % (PK, SR))
uzeq = w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )')
z1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % XP)
lr = w.s([uzeq, z1, cv, sr], 'climrecl', '( %s -> ( ( _G ` X ) x. X ) e. RR )' % XP)
xne = w.s([x0], 'gt0ne0d', '( %s -> X =/= 0 )' % XP)
gc = w.s([dx, w.inst('gamcl')], 'syl', '( %s -> ( _G ` X ) e. CC )' % XP)
dv = w.s([gc, xc, xne], 'divcan4d', '( %s -> ( ( ( _G ` X ) x. X ) / X ) = ( _G ` X ) )' % XP)
w.qed([w.s([dv], 'eqcomd', '( %s -> ( _G ` X ) = ( ( ( _G ` X ) x. X ) / X ) )' % XP),
       w.s([lr, xr, xne], 'redivcld', '( %s -> ( ( ( _G ` X ) x. X ) / X ) e. RR )' % XP)], 'eqeltrd',
      '( %s -> ( _G ` X ) e. RR )' % XP)
run4(w)

# ---------------------------------------------------------------- gamrrp
w = W('gamrrp', 'The gamma function at a positive real argument is a positive real: '
      'its Euler product ( ~ gamcvg2 ) has positive partial products and the value '
      'is nonzero ( ~ gamne0 ).')
xr = w.s([], 'simpl', '( %s -> X e. RR )' % XP)
x0 = w.s([], 'simpr', '( %s -> 0 < X )' % XP)
xc = w.s([xr], 'recnd', '( %s -> X e. CC )' % XP)
xre = w.s([xr], 'rered', '( %s -> ( Re ` X ) = X )' % XP)
dx = w.s([w.s([xc, w.s([x0, xre], 'breqtrrd', '( %s -> 0 < ( Re ` X ) )' % XP)], 'jca',
               '( %s -> ( X e. CC /\\ 0 < ( Re ` X ) ) )' % XP), w.inst('zrenn')], 'syl',
         '( %s -> X e. ( CC \\ ( ZZ \\ NN ) ) )' % XP)
er = w.s([], 'eqid', '%s = %s' % (ER, ER))
cv = w.s([er, dx], 'gamcvg2', '( %s -> %s ~~> ( ( _G ` X ) x. X ) )' % (XP, SR))
PK = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % XP
ku1 = w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % PK)
PA = '( %s /\\ a e. ( 1 ... k ) )' % PK
ann = w.s([w.s([], 'simpr', '( %s -> a e. ( 1 ... k ) )' % PA), w.inst('elfznn')], 'syl',
          '( %s -> a e. NN )' % PA)
xra = w.s([], 'simplll', '( %s -> X e. RR )' % PA)
x0a = w.s([], 'simpllr', '( %s -> 0 < X )' % PA)
era = w.s([w.s([w.s([xra, x0a], 'jca', '( %s -> %s )' % (PA, XP)), ann], 'jca',
                '( %s -> ( %s /\\ a e. NN ) )' % (PA, XP)), w.inst('eutrrp')], 'syl',
          '( %s -> ( %s ` a ) e. RR+ )' % (PA, ER))
PB = '( %s /\\ ( a e. RR+ /\\ b e. RR+ ) )' % PK
mulr = w.s([w.s([], 'simprl', '( %s -> a e. RR+ )' % PB), w.s([], 'simprr', '( %s -> b e. RR+ )' % PB)],
           'rpmulcld', '( %s -> ( a x. b ) e. RR+ )' % PB)
srp = w.s([ku1, era, mulr], 'seqcl', '( %s -> ( %s ` k ) e. RR+ )' % (PK, SR))
uzeq = w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )')
z1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % XP)
ge0 = w.s([uzeq, z1, cv, w.s([srp], 'rpred', '( %s -> ( %s ` k ) e. RR )' % (PK, SR)),
           w.s([srp], 'rpge0d', '( %s -> 0 <_ ( %s ` k ) )' % (PK, SR))], 'climge0',
          '( %s -> 0 <_ ( ( _G ` X ) x. X ) )' % XP)
gr = w.s([w.s([xr, x0], 'jca', '( %s -> %s )' % (XP, XP)), w.inst('gamrre')], 'syl',
         '( %s -> ( _G ` X ) e. RR )' % XP)
gne = w.s([dx, w.inst('gamne0')], 'syl', '( %s -> ( _G ` X ) =/= 0 )' % XP)
# 0 <_ ( _G ` X ) x. X and 0 < X give 0 <_ ( _G ` X )
gxr = w.s([gr, xr], 'remulcld', '( %s -> ( ( _G ` X ) x. X ) e. RR )' % XP)
dge = w.s([gxr, ge0, xr, x0, w.inst('divge0')], 'syl22anc', '( %s -> 0 <_ ( ( ( _G ` X ) x. X ) / X ) )' % XP)
dcan = w.s([w.s([dx, w.inst('gamcl')], 'syl', '( %s -> ( _G ` X ) e. CC )' % XP), xc,
            w.s([x0], 'gt0ne0d', '( %s -> X =/= 0 )' % XP)], 'divcan4d',
           '( %s -> ( ( ( _G ` X ) x. X ) / X ) = ( _G ` X ) )' % XP)
pos = w.s([dge, dcan], 'breqtrd', '( %s -> 0 <_ ( _G ` X ) )' % XP)
w.qed([gr, w.s([w.s([gr, pos], 'jca', '( %s -> ( ( _G ` X ) e. RR /\\ 0 <_ ( _G ` X ) ) )' % XP), gne], 'jca',
               '( %s -> ( ( ( _G ` X ) e. RR /\\ 0 <_ ( _G ` X ) ) /\\ ( _G ` X ) =/= 0 ) )' % XP)],
      'jca', 'dummy')
w.lines.pop()
w.qed([gr, w.s([gr, pos, gne], 'ne0gt0d', '( %s -> 0 < ( _G ` X ) )' % XP)], 'elrpd',
      '( %s -> ( _G ` X ) e. RR+ )' % XP)
run4(w)

ZP = '( Z e. CC /\\ 0 < %s )' % RZ
HQ = 'A. j e. ( 1 ... M ) ( 2 x. ( %s + j ) ) <_ ( abs ` ( Im ` Z ) )' % RZ
PHM = '( %s /\\ ( M e. NN0 /\\ %s ) )' % (ZP, HQ)

# ---------------------------------------------------------------- gamvb0
w = W('gamvb0', 'The modulus of the gamma function at a complex argument with '
      'positive real part, against its value at the real part, with one factor of '
      'a half for every index at which the height dominates.  From ~ gamzx by '
      'dividing by the modulus of the argument.')
zp = w.s([], 'simpl', '( %s -> %s )' % (PHM, ZP))
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % PHM)
z0 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (PHM, RZ))
mh = w.s([], 'simpr', '( %s -> ( M e. NN0 /\\ %s ) )' % (PHM, HQ))
mn0 = w.s([mh, w.inst('simpl')], 'syl', '( %s -> M e. NN0 )' % PHM)
mz = w.s([mn0, w.inst('nn0z')], 'syl', '( %s -> M e. ZZ )' % PHM)
rzr = w.s([zc], 'recld', '( %s -> %s e. RR )' % (PHM, RZ))
grp = w.s([w.s([rzr, z0], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (PHM, RZ, RZ)), w.inst('gamrrp')],
          'syl', '( %s -> ( _G ` %s ) e. RR+ )' % (PHM, RZ))
gr = w.s([grp], 'rpred', '( %s -> ( _G ` %s ) e. RR )' % (PHM, RZ))
zx = w.s([w.s([], 'id', '( %s -> %s )' % (PHM, PHM)), w.inst('gamzx')], 'syl',
         '( %s -> ( abs ` ( ( _G ` Z ) x. Z ) ) <_ ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) )' % (PHM, RZ, RZ))
dz = w.s([w.s([zc, z0], 'jca', '( %s -> %s )' % (PHM, ZP)), w.inst('zrenn')], 'syl',
         '( %s -> Z e. ( CC \\ ( ZZ \\ NN ) ) )' % PHM)
gzc = w.s([dz, w.inst('gamcl')], 'syl', '( %s -> ( _G ` Z ) e. CC )' % PHM)
am = w.s([gzc, zc], 'absmuld', '( %s -> ( abs ` ( ( _G ` Z ) x. Z ) ) = ( ( abs ` ( _G ` Z ) ) x. ( abs ` Z ) ) )' % PHM)
agr = w.s([gzc], 'abscld', '( %s -> ( abs ` ( _G ` Z ) ) e. RR )' % PHM)
ag0 = w.s([gzc], 'absge0d', '( %s -> 0 <_ ( abs ` ( _G ` Z ) ) )' % PHM)
azr = w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % PHM)
rle = w.s([zc, w.inst('releabs')], 'syl', '( %s -> %s <_ ( abs ` Z ) )' % (PHM, RZ))
mle = w.s([rzr, azr, agr, ag0, rle], 'lemul2ad',
          '( %s -> ( ( abs ` ( _G ` Z ) ) x. %s ) <_ ( ( abs ` ( _G ` Z ) ) x. ( abs ` Z ) ) )' % (PHM, RZ))
pw = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % PHM), mz], 'rpexpcld',
         '( %s -> ( 2 ^ M ) e. RR+ )' % PHM)
lhsr = w.s([agr, rzr], 'remulcld', '( %s -> ( ( abs ` ( _G ` Z ) ) x. %s ) e. RR )' % (PHM, RZ))
mr = w.s([agr, azr], 'remulcld', '( %s -> ( ( abs ` ( _G ` Z ) ) x. ( abs ` Z ) ) e. RR )' % PHM)
rhsr = w.s([w.s([gr, rzr], 'remulcld', '( %s -> ( ( _G ` %s ) x. %s ) e. RR )' % (PHM, RZ, RZ)),
            w.s([pw], 'rpred', '( %s -> ( 2 ^ M ) e. RR )' % PHM),
            w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHM)], 'redivcld',
           '( %s -> ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) e. RR )' % (PHM, RZ, RZ))
ch = w.s([lhsr, mr, rhsr, mle, w.s([am, zx], 'eqbrtrrd',
                                   '( %s -> ( ( abs ` ( _G ` Z ) ) x. ( abs ` Z ) ) <_ ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) )' % (PHM, RZ, RZ))],
         'letrd', '( %s -> ( ( abs ` ( _G ` Z ) ) x. %s ) <_ ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) )' % (PHM, RZ, RZ, RZ))
d23 = w.s([w.s([gr], 'recnd', '( %s -> ( _G ` %s ) e. CC )' % (PHM, RZ)),
           w.s([rzr], 'recnd', '( %s -> %s e. CC )' % (PHM, RZ)),
           w.s([pw], 'rpcnd', '( %s -> ( 2 ^ M ) e. CC )' % PHM),
           w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHM)], 'div23d',
          '( %s -> ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) = ( ( ( _G ` %s ) / ( 2 ^ M ) ) x. %s ) )' % (PHM, RZ, RZ, RZ, RZ))
ch2 = w.s([ch, d23], 'breqtrd',
          '( %s -> ( ( abs ` ( _G ` Z ) ) x. %s ) <_ ( ( ( _G ` %s ) / ( 2 ^ M ) ) x. %s ) )' % (PHM, RZ, RZ, RZ))
qr = w.s([gr, w.s([pw], 'rpred', '( %s -> ( 2 ^ M ) e. RR )' % PHM),
          w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHM)], 'redivcld',
         '( %s -> ( ( _G ` %s ) / ( 2 ^ M ) ) e. RR )' % (PHM, RZ))
bi = w.s([agr, qr, w.s([rzr, z0], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (PHM, RZ, RZ)), w.inst('lemul1')], 'syl3anc',
         '( %s -> ( ( abs ` ( _G ` Z ) ) <_ ( ( _G ` %s ) / ( 2 ^ M ) ) <-> ( ( abs ` ( _G ` Z ) ) x. %s ) <_ ( ( ( _G ` %s ) / ( 2 ^ M ) ) x. %s ) ) )' % (PHM, RZ, RZ, RZ, RZ))
w.qed([ch2, bi], 'mpbird', '( %s -> ( abs ` ( _G ` Z ) ) <_ ( ( _G ` %s ) / ( 2 ^ M ) ) )' % (PHM, RZ))
run4(w)
