"""C4, Gamma block 4: from the finite products to the gamma function."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

RZ = '( Re ` Z )'
EZ = EUT('Z'); EX = EUT(RZ)
AZ = '( abs ` ( %s ` k ) )' % EZ
AX = '( %s ` k )' % EX
SZ = 'seq 1 ( x. , %s )' % EZ
SX = 'seq 1 ( x. , %s )' % EX
ZP = '( Z e. CC /\\ 0 < %s )' % RZ
HQ = 'A. j e. ( 1 ... M ) ( 2 x. ( %s + j ) ) <_ ( abs ` ( Im ` Z ) )' % RZ
PHM = '( %s /\\ ( M e. NN0 /\\ %s ) )' % (ZP, HQ)
PH3 = '( %s /\\ N e. ( ZZ>= ` ( M + 1 ) ) )' % PHM

# ---------------------------------------------------------------- gamseq
w = W('gamseq', 'The partial products of Euler\'s product ( ~ gamprod ) written with '
      '` seq `, the form ~ gamcvg2 uses.')
zp = w.s([], 'simpll', '( %s -> %s )' % (PH3, ZP))
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % PH3)
z0 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (PH3, RZ))
mh = w.s([], 'simplr', '( %s -> ( M e. NN0 /\\ %s ) )' % (PH3, HQ))
mn0 = w.s([mh, w.inst('simpl')], 'syl', '( %s -> M e. NN0 )' % PH3)
mz = w.s([mn0, w.inst('nn0z')], 'syl', '( %s -> M e. ZZ )' % PH3)
nu1 = w.s([], 'simpr', '( %s -> N e. ( ZZ>= ` ( M + 1 ) ) )' % PH3)
m1uz = w.s([w.s([mz, w.inst('uzid')], 'syl', '( %s -> M e. ( ZZ>= ` M ) )' % PH3), w.inst('peano2uz')],
           'syl', '( %s -> ( M + 1 ) e. ( ZZ>= ` M ) )' % PH3)
nu = w.s([w.s([m1uz, w.inst('uzss')], 'syl', '( %s -> ( ZZ>= ` ( M + 1 ) ) C_ ( ZZ>= ` M ) )' % PH3), nu1],
         'sseldd', '( %s -> N e. ( ZZ>= ` M ) )' % PH3)
m1n = w.s([mn0, w.inst('nn0p1nn')], 'syl', '( %s -> ( M + 1 ) e. NN )' % PH3)
nnuz = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % PH3)
nnu = w.s([w.s([w.s([m1n, nnuz], 'eleqtrd', '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % PH3), w.inst('uzss')],
               'syl', '( %s -> ( ZZ>= ` ( M + 1 ) ) C_ ( ZZ>= ` 1 ) )' % PH3), nu1], 'sseldd',
          '( %s -> N e. ( ZZ>= ` 1 ) )' % PH3)
phm = w.s([], 'simpl', '( %s -> %s )' % (PH3, PHM))
pr = w.s([w.s([phm, nu], 'jca', '( %s -> ( %s /\\ N e. ( ZZ>= ` M ) ) )' % (PH3, PHM)), w.inst('gamprod')],
         'syl', '( %s -> prod_ k e. ( 1 ... N ) %s <_ ( prod_ k e. ( 1 ... N ) %s / ( 2 ^ M ) ) )' % (PH3, AZ, AX))
# closures on ( ZZ>= ` 1 )
PN = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % PH3
knn = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % PN),
           w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % PN)],
          'eleqtrrd', '( %s -> k e. NN )' % PN)
basen = w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % PN), w.s([z0], 'adantr', '( %s -> 0 < %s )' % (PN, RZ))],
                 'jca', '( %s -> %s )' % (PN, ZP)), knn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (PN, ZP))
ezc = w.s([basen, w.inst('eutzcl')], 'syl', '( %s -> ( %s ` k ) e. CC )' % (PN, EZ))
axc = w.s([w.s([basen, w.inst('eutxrp')], 'syl', '( %s -> %s e. RR+ )' % (PN, AX))], 'rpcnd',
          '( %s -> %s e. CC )' % (PN, AX))
ez1 = w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )')
# ( abs ` prod_ k e. ( 1 ... N ) ( EZ ` k ) ) = prod_ k e. ( 1 ... N ) ( abs ` ( EZ ` k ) )
pabs = w.s([ez1, nnu, ezc], 'fprodabs',
           '( %s -> ( abs ` prod_ k e. ( 1 ... N ) ( %s ` k ) ) = prod_ k e. ( 1 ... N ) %s )' % (PH3, EZ, AZ))
# prod_ k e. ( 1 ... N ) ( F ` k ) = ( seq 1 ( x. , F ) ` N )
PF = '( %s /\\ k e. ( 1 ... N ) )' % PH3
kfz = w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % PF)
knn2 = w.s([kfz, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % PF)
basef = w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % PF), w.s([z0], 'adantr', '( %s -> 0 < %s )' % (PF, RZ))],
                 'jca', '( %s -> %s )' % (PF, ZP)), knn2], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (PF, ZP))
ezcf = w.s([basef, w.inst('eutzcl')], 'syl', '( %s -> ( %s ` k ) e. CC )' % (PF, EZ))
axcf = w.s([w.s([basef, w.inst('eutxrp')], 'syl', '( %s -> %s e. RR+ )' % (PF, AX))], 'rpcnd',
           '( %s -> %s e. CC )' % (PF, AX))
idz = w.s([], 'eqidd', '( %s -> ( %s ` k ) = ( %s ` k ) )' % (PF, EZ, EZ))
idx = w.s([], 'eqidd', '( %s -> %s = %s )' % (PF, AX, AX))
serz = w.s([idz, nnu, ezcf], 'fprodser',
           '( %s -> prod_ k e. ( 1 ... N ) ( %s ` k ) = ( %s ` N ) )' % (PH3, EZ, SZ))
serx = w.s([idx, nnu, axcf], 'fprodser',
           '( %s -> prod_ k e. ( 1 ... N ) %s = ( %s ` N ) )' % (PH3, AX, SX))
lhs = w.s([w.s([serz], 'fveq2d', '( %s -> ( abs ` prod_ k e. ( 1 ... N ) ( %s ` k ) ) = ( abs ` ( %s ` N ) ) )' % (PH3, EZ, SZ)),
           pabs], 'eqtr3d', '( %s -> ( abs ` ( %s ` N ) ) = prod_ k e. ( 1 ... N ) %s )' % (PH3, SZ, AZ))
rhs = w.s([serx], 'oveq1d',
          '( %s -> ( prod_ k e. ( 1 ... N ) %s / ( 2 ^ M ) ) = ( ( %s ` N ) / ( 2 ^ M ) ) )' % (PH3, AX, SX))
w.qed([lhs, w.s([pr, rhs], 'breqtrd',
                '( %s -> prod_ k e. ( 1 ... N ) %s <_ ( ( %s ` N ) / ( 2 ^ M ) ) )' % (PH3, AZ, SX))],
      'eqbrtrd', '( %s -> ( abs ` ( %s ` N ) ) <_ ( ( %s ` N ) / ( 2 ^ M ) ) )' % (PH3, SZ, SX))
run4(w)

# ---------------------------------------------------------------- gamzx
UZ = '( ZZ>= ` ( M + 1 ) )'
FA = '( n e. %s |-> ( abs ` ( %s ` n ) ) )' % (UZ, SZ)
GA = '( n e. %s |-> ( ( 1 / ( 2 ^ M ) ) x. ( %s ` n ) ) )' % (UZ, SX)
w = W('gamzx', 'The gamma function at a complex argument with positive real part, '
      'against its value at the real part: every index below ` M ` at which the '
      'height dominates contributes a factor of one half.  The limit of ~ gamseq '
      'through ~ gamcvg2 and ~ climle .')
zp = w.s([], 'simpl', '( %s -> %s )' % (PHM, ZP))
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % PHM)
z0 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (PHM, RZ))
mh = w.s([], 'simpr', '( %s -> ( M e. NN0 /\\ %s ) )' % (PHM, HQ))
mn0 = w.s([mh, w.inst('simpl')], 'syl', '( %s -> M e. NN0 )' % PHM)
mz = w.s([mn0, w.inst('nn0z')], 'syl', '( %s -> M e. ZZ )' % PHM)
m1z = w.s([mz, w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % PHM)], 'zaddcld',
          '( %s -> ( M + 1 ) e. ZZ )' % PHM)
rzr = w.s([zc], 'recld', '( %s -> %s e. RR )' % (PHM, RZ))
rzc = w.s([rzr], 'recnd', '( %s -> %s e. CC )' % (PHM, RZ))
rzre = w.s([rzr], 'rered', '( %s -> ( Re ` %s ) = %s )' % (PHM, RZ, RZ))
# the two domains
dz = w.s([w.s([zc, z0], 'jca', '( %s -> %s )' % (PHM, ZP)), w.inst('zrenn')], 'syl',
         '( %s -> Z e. ( CC \\ ( ZZ \\ NN ) ) )' % PHM)
dx = w.s([w.s([rzc, w.s([z0, rzre], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (PHM, RZ))], 'jca',
               '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (PHM, RZ, RZ)), w.inst('zrenn')], 'syl',
         '( %s -> %s e. ( CC \\ ( ZZ \\ NN ) ) )' % (PHM, RZ))
# the two Euler limits
ez = w.s([], 'eqid', '%s = %s' % (EZ, EZ))
ex = w.s([], 'eqid', '%s = %s' % (EX, EX))
cvz = w.s([ez, dz], 'gamcvg2', '( %s -> %s ~~> ( ( _G ` Z ) x. Z ) )' % (PHM, SZ))
cvx = w.s([ex, dx], 'gamcvg2', '( %s -> %s ~~> ( ( _G ` %s ) x. %s ) )' % (PHM, SX, RZ, RZ))
# closures of the partial products at an index of ( ZZ>= ` ( M + 1 ) )
PK = '( %s /\\ k e. %s )' % (PHM, UZ)
kuz = w.s([], 'simpr', '( %s -> k e. %s )' % (PK, UZ))
m1n = w.s([mn0, w.inst('nn0p1nn')], 'syl', '( %s -> ( M + 1 ) e. NN )' % PHM)
nnuz = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % PHM)
ssu = w.s([w.s([m1n, nnuz], 'eleqtrd', '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % PHM), w.inst('uzss')],
          'syl', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (PHM, UZ))
ku1 = w.s([w.s([ssu], 'adantr', '( %s -> %s C_ ( ZZ>= ` 1 ) )' % (PK, UZ)), kuz], 'sseldd',
          '( %s -> k e. ( ZZ>= ` 1 ) )' % PK)
PA = '( %s /\\ a e. ( 1 ... k ) )' % PK
ann = w.s([w.s([], 'simpr', '( %s -> a e. ( 1 ... k ) )' % PA), w.inst('elfznn')], 'syl',
          '( %s -> a e. NN )' % PA)
basea = w.s([w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % PK), w.s([z0], 'adantr', '( %s -> 0 < %s )' % (PK, RZ))],
                      'jca', '( %s -> %s )' % (PK, ZP))], 'adantr', '( %s -> %s )' % (PA, ZP)), ann], 'jca',
            '( %s -> ( %s /\\ a e. NN ) )' % (PA, ZP))
eza = w.s([basea, w.inst('eutzcl')], 'syl', '( %s -> ( %s ` a ) e. CC )' % (PA, EZ))
exa = w.s([w.s([basea, w.inst('eutxrp')], 'syl', '( %s -> ( %s ` a ) e. RR+ )' % (PA, EX))], 'rpred',
          '( %s -> ( %s ` a ) e. RR )' % (PA, EX))
PB = '( %s /\\ ( a e. CC /\\ b e. CC ) )' % PK
mulc = w.s([w.s([], 'simprl', '( %s -> a e. CC )' % PB), w.s([], 'simprr', '( %s -> b e. CC )' % PB)],
           'mulcld', '( %s -> ( a x. b ) e. CC )' % PB)
PBR = '( %s /\\ ( a e. RR /\\ b e. RR ) )' % PK
mulr = w.s([w.s([], 'simprl', '( %s -> a e. RR )' % PBR), w.s([], 'simprr', '( %s -> b e. RR )' % PBR)],
           'remulcld', '( %s -> ( a x. b ) e. RR )' % PBR)
szc = w.s([ku1, eza, mulc], 'seqcl', '( %s -> ( %s ` k ) e. CC )' % (PK, SZ))
sxr = w.s([ku1, exa, mulr], 'seqcl', '( %s -> ( %s ` k ) e. RR )' % (PK, SX))
# the two clim sequences
uzex = w.s([w.s([], 'fvex', '%s e. _V' % UZ), w.inst('mptexg')], 'ax-mp', '%s e. _V' % FA)
fav = w.s([uzex], 'a1i', '( %s -> %s e. _V )' % (PHM, FA))
uzex2 = w.s([w.s([], 'fvex', '%s e. _V' % UZ), w.inst('mptexg')], 'ax-mp', '%s e. _V' % GA)
gav = w.s([uzex2], 'a1i', '( %s -> %s e. _V )' % (PHM, GA))
uzeq = w.s([], 'eqid', '%s = %s' % (UZ, UZ))
# values
subf = w.s([w.s([], 'fveq2', '( n = k -> ( %s ` n ) = ( %s ` k ) )' % (SZ, SZ))], 'fveq2d',
           '( n = k -> ( abs ` ( %s ` n ) ) = ( abs ` ( %s ` k ) ) )' % (SZ, SZ))
emf = w.s([], 'eqid', '%s = %s' % (FA, FA))
fvf = w.s([subf, emf], 'fvmptg', '( ( k e. %s /\\ ( abs ` ( %s ` k ) ) e. _V ) -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (UZ, SZ, FA, SZ))
faval = w.s([kuz, w.s([w.s([], 'fvex', '( abs ` ( %s ` k ) ) e. _V' % SZ)], 'a1i',
                      '( %s -> ( abs ` ( %s ` k ) ) e. _V )' % (PK, SZ)), fvf], 'syl2anc',
            '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (PK, FA, SZ))
subg = w.s([w.s([], 'fveq2', '( n = k -> ( %s ` n ) = ( %s ` k ) )' % (SX, SX))], 'oveq2d',
           '( n = k -> ( ( 1 / ( 2 ^ M ) ) x. ( %s ` n ) ) = ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (SX, SX))
emg = w.s([], 'eqid', '%s = %s' % (GA, GA))
fvg = w.s([subg, emg], 'fvmptg', '( ( k e. %s /\\ ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) e. _V ) -> ( %s ` k ) = ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (UZ, SX, GA, SX))
gaval = w.s([kuz, w.s([w.s([], 'ovex', '( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) e. _V' % SX)], 'a1i',
                      '( %s -> ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) e. _V )' % (PK, SX)), fvg], 'syl2anc',
            '( %s -> ( %s ` k ) = ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (PK, GA, SX))
# 2 ^ M and its reciprocal
pw = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % PHM), mz], 'rpexpcld',
         '( %s -> ( 2 ^ M ) e. RR+ )' % PHM)
rec = w.s([w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % PHM), pw], 'rpdivcld',
          '( %s -> ( 1 / ( 2 ^ M ) ) e. RR+ )' % PHM)
recc = w.s([rec], 'rpcnd', '( %s -> ( 1 / ( 2 ^ M ) ) e. CC )' % PHM)
# the limits of the two sequences
cfa = w.s([uzeq, m1z, cvz, fav, szc, faval], 'climabs',
          '( %s -> %s ~~> ( abs ` ( ( _G ` Z ) x. Z ) ) )' % (PHM, FA))
cga = w.s([uzeq, m1z, cvx, recc, gav, w.s([sxr], 'recnd', '( %s -> ( %s ` k ) e. CC )' % (PK, SX)), gaval],
          'climmulc2', '( %s -> %s ~~> ( ( 1 / ( 2 ^ M ) ) x. ( ( _G ` %s ) x. %s ) ) )' % (PHM, GA, RZ, RZ))
# the termwise comparison
gs = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (PK, PHM)), kuz], 'jca', '( %s -> ( %s /\\ k e. %s ) )' % (PK, PHM, UZ)),
          w.inst('gamseq')], 'syl', '( %s -> ( abs ` ( %s ` k ) ) <_ ( ( %s ` k ) / ( 2 ^ M ) ) )' % (PK, SZ, SX))
dr = w.s([w.s([sxr], 'recnd', '( %s -> ( %s ` k ) e. CC )' % (PK, SX)),
          w.s([pw], 'rpcnd', '( %s -> ( 2 ^ M ) e. CC )' % PHM),
          w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHM)], 'divrec2d',
         '( %s -> ( ( %s ` k ) / ( 2 ^ M ) ) = ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (PK, SX, SX))
w.lines.pop()
dr = w.s([w.s([sxr], 'recnd', '( %s -> ( %s ` k ) e. CC )' % (PK, SX)),
          w.s([w.s([pw], 'rpcnd', '( %s -> ( 2 ^ M ) e. CC )' % PHM)], 'adantr', '( %s -> ( 2 ^ M ) e. CC )' % PK),
          w.s([w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHM)], 'adantr', '( %s -> ( 2 ^ M ) =/= 0 )' % PK)],
         'divrec2d', '( %s -> ( ( %s ` k ) / ( 2 ^ M ) ) = ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (PK, SX, SX))
cmp = w.s([w.s([gs, dr], 'breqtrd', '( %s -> ( abs ` ( %s ` k ) ) <_ ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (PK, SZ, SX)),
           faval, gaval], 'jca', 'dummy')
w.lines.pop()
cmp = w.s([w.s([faval, w.s([gs, dr], 'breqtrd',
                           '( %s -> ( abs ` ( %s ` k ) ) <_ ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (PK, SZ, SX))],
                'eqbrtrd', '( %s -> ( %s ` k ) <_ ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) )' % (PK, FA, SX)),
           w.s([gaval], 'eqcomd', '( %s -> ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) = ( %s ` k ) )' % (PK, SX, GA))],
          'breqtrd', '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (PK, FA, GA))
far = w.s([faval, w.s([szc], 'abscld', '( %s -> ( abs ` ( %s ` k ) ) e. RR )' % (PK, SZ))], 'eqeltrd',
          '( %s -> ( %s ` k ) e. RR )' % (PK, FA))
gar = w.s([gaval, w.s([w.s([w.s([rec], 'rpred', '( %s -> ( 1 / ( 2 ^ M ) ) e. RR )' % PHM)], 'adantr',
                            '( %s -> ( 1 / ( 2 ^ M ) ) e. RR )' % PK), sxr], 'remulcld',
                      '( %s -> ( ( 1 / ( 2 ^ M ) ) x. ( %s ` k ) ) e. RR )' % (PK, SX))], 'eqeltrd',
          '( %s -> ( %s ` k ) e. RR )' % (PK, GA))
le = w.s([uzeq, m1z, cfa, cga, far, gar, cmp], 'climle',
         '( %s -> ( abs ` ( ( _G ` Z ) x. Z ) ) <_ ( ( 1 / ( 2 ^ M ) ) x. ( ( _G ` %s ) x. %s ) ) )' % (PHM, RZ, RZ))
gxc = w.s([w.s([dx, w.inst('gamcl')], 'syl', '( %s -> ( _G ` %s ) e. CC )' % (PHM, RZ)), rzc], 'mulcld',
          '( %s -> ( ( _G ` %s ) x. %s ) e. CC )' % (PHM, RZ, RZ))
fin = w.s([gxc, w.s([pw], 'rpcnd', '( %s -> ( 2 ^ M ) e. CC )' % PHM),
           w.s([pw], 'rpne0d', '( %s -> ( 2 ^ M ) =/= 0 )' % PHM)], 'divrec2d',
          '( %s -> ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) = ( ( 1 / ( 2 ^ M ) ) x. ( ( _G ` %s ) x. %s ) ) )' % (PHM, RZ, RZ, RZ, RZ))
w.qed([le, w.s([fin], 'eqcomd',
               '( %s -> ( ( 1 / ( 2 ^ M ) ) x. ( ( _G ` %s ) x. %s ) ) = ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) )' % (PHM, RZ, RZ, RZ, RZ))],
      'breqtrd', '( %s -> ( abs ` ( ( _G ` Z ) x. Z ) ) <_ ( ( ( _G ` %s ) x. %s ) / ( 2 ^ M ) ) )' % (PHM, RZ, RZ))
run4(w)
