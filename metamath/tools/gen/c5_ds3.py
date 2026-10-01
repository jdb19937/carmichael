"""C5, Dirichlet instance 3: the consumer-facing forms (values, the derivative
value and its bound) and the character L-series instance."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

D = HP()
RZ = '( Re ` Z )'
E0 = EH
SHC = lambda E: '( q e. NN |-> ( ( ( A ` q ) x. ( log ` q ) ) x. ( q ^c -u %s ) ) )' % E


def LT(K, Z):
    return LTRM('A', K, Z)


# ---------------------------------------------------------------- dlogcvg
w = W('dlogcvg', 'The logarithmically weighted Dirichlet series converges to the right of the line one plus '
      'the shift ( ~ dsercvg at the shifted abscissa, ~ dlogcl ).')
A0 = '( ( %s /\\ E e. RR+ ) /\\ ( Z e. CC /\\ ( 1 + E ) < %s ) )' % (CFB, RZ)
SH = SHC('E')
CFBS = '( %s : NN --> CC /\\ ( C / E ) e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ ( C / E ) )' % (SH, SH)
cfbe = w.s([], 'simpl', '( %s -> ( %s /\\ E e. RR+ ) )' % (A0, CFB))
cfb = w.s([cfbe, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CFB))
erp = w.s([cfbe, w.inst('simpr')], 'syl', '( %s -> E e. RR+ )' % A0)
af = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
lt = w.s([], 'simprr', '( %s -> ( 1 + E ) < %s )' % (A0, RZ))
er = w.s([erp], 'rpred', '( %s -> E e. RR )' % A0)
ec = w.s([er], 'recnd', '( %s -> E e. CC )' % A0)
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
rsub = w.s([w.s([zc, ec], 'resubd', '( %s -> ( Re ` ( Z - E ) ) = ( %s - ( Re ` E ) ) )' % (A0, RZ)),
            w.s([w.s([er], 'rered', '( %s -> ( Re ` E ) = E )' % A0)], 'oveq2d', '( %s -> ( %s - ( Re ` E ) ) = ( %s - E ) )' % (A0, RZ, RZ))], 'eqtrd',
           '( %s -> ( Re ` ( Z - E ) ) = ( %s - E ) )' % (A0, RZ))
r1 = a1(w, A0, '1re', '1 e. RR')
gt = w.s([lt, w.s([r1, er, rz], 'ltaddsubd', '( %s -> ( ( 1 + E ) < %s <-> 1 < ( %s - E ) ) )' % (A0, RZ, RZ))], 'mpbid', '( %s -> 1 < ( %s - E ) )' % (A0, RZ))
gt2 = w.s([gt, w.s([rsub], 'eqcomd', '( %s -> ( %s - E ) = ( Re ` ( Z - E ) ) )' % (A0, RZ))], 'breqtrd', '( %s -> 1 < ( Re ` ( Z - E ) ) )' % A0)
cfbs = w.s([cfbe, w.inst('dlogcfb')], 'syl', '( %s -> %s )' % (A0, CFBS))
pack = w.s([cfbs, w.s([w.s([zc, ec], 'subcld', '( %s -> ( Z - E ) e. CC )' % A0), gt2], 'jca', '( %s -> ( ( Z - E ) e. CC /\\ 1 < ( Re ` ( Z - E ) ) ) )' % A0)],
           'jca', '( %s -> ( %s /\\ ( ( Z - E ) e. CC /\\ 1 < ( Re ` ( Z - E ) ) ) ) )' % (A0, CFBS))
GS = '( n e. NN |-> ( ( %s ` n ) x. ( n ^c -u ( Z - E ) ) ) )' % SH
cv = w.s([pack, w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, GS))
An = '( %s /\\ n e. NN )' % A0
nn = w.s([], 'simpr', '( %s -> n e. NN )' % An)
SHN = '( ( ( A ` n ) x. ( log ` n ) ) x. ( n ^c -u E ) )'
sv = w.s([nn, w.inst('dshcval')], 'syl', '( %s -> ( %s ` n ) = %s )' % (An, SH, SHN))
BN = '( ( A ` n ) x. ( log ` n ) )'
bnc = w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % An), nn], 'ffvelcdmd', '( %s -> ( A ` n ) e. CC )' % An),
           w.s([w.s([w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % An)], 'relogcld', '( %s -> ( log ` n ) e. RR )' % An)], 'recnd', '( %s -> ( log ` n ) e. CC )' % An)],
          'mulcld', '( %s -> %s e. CC )' % (An, BN))
tr = w.s([w.s([w.s([nn, w.s([ec], 'adantr', '( %s -> E e. CC )' % An), w.s([zc], 'adantr', '( %s -> Z e. CC )' % An)], '3jca',
                   '( %s -> ( n e. NN /\\ E e. CC /\\ Z e. CC ) )' % An), bnc], 'jca', '( %s -> ( ( n e. NN /\\ E e. CC /\\ Z e. CC ) /\\ %s e. CC ) )' % (An, BN)),
          w.inst('dlogtrm')], 'syl', '( %s -> ( %s x. ( n ^c -u ( Z - E ) ) ) = %s )' % (An, SHN, LT('n', 'Z')))
eq = w.s([w.s([sv], 'oveq1d', '( %s -> ( ( %s ` n ) x. ( n ^c -u ( Z - E ) ) ) = ( %s x. ( n ^c -u ( Z - E ) ) ) )' % (An, SH, SHN)), tr], 'eqtrd',
         '( %s -> ( ( %s ` n ) x. ( n ^c -u ( Z - E ) ) ) = %s )' % (An, SH, LT('n', 'Z')))
mp = w.s([eq], 'mpteq2dva', '( %s -> %s = ( n e. NN |-> %s ) )' % (A0, GS, LT('n', 'Z')))
w.qed([w.s([mp], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , ( n e. NN |-> %s ) ) )' % (A0, GS, LT('n', 'Z'))), cv], 'eqeltrrd',
      '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (A0, LT('n', 'Z')))
run5(w)

# ---------------------------------------------------------------- dserval
w = W('dserval', 'The value of the Dirichlet series function at a point of the half-plane.')
sub = w.s([w.s([w.s([w.s([], 'negeq', '( z = Z -> -u z = -u Z )')], 'oveq2d', '( z = Z -> ( k ^c -u z ) = ( k ^c -u Z ) )')], 'oveq2d',
               '( z = Z -> %s = %s )' % (TRM('A', 'k', 'z'), TRM('A', 'k', 'Z')))], 'sumeq2sdv',
          '( z = Z -> sum_ k e. NN %s = sum_ k e. NN %s )' % (TRM('A', 'k', 'z'), TRM('A', 'k', 'Z')))
w.qed([sub, w.s([], 'eqid', '%s = %s' % (LSF(), LSF())), w.s([], 'sumex', 'sum_ k e. NN %s e. _V' % TRM('A', 'k', 'Z'))], 'fvmpt',
      '( Z e. %s -> ( %s ` Z ) = sum_ k e. NN %s )' % (D, LSF(), TRM('A', 'k', 'Z')))
run5(w)

# ---------------------------------------------------------------- dserdvval
w = W('dserdvval', 'The derivative of a Dirichlet series at a point of the half-plane is minus the '
      'logarithmically weighted series ( ~ dserdv , ~ isummulc2 ).')
A0 = '( %s /\\ Z e. %s )' % (HYP, D)
hyp = w.s([], 'simpl', '( %s -> %s )' % (A0, HYP))
zh = w.s([], 'simpr', '( %s -> Z e. %s )' % (A0, D))
cfb = w.s([hyp, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CFB))
tt = w.s([hyp, w.inst('simpr')], 'syl', '( %s -> ( T e. RR /\\ 1 < T ) )' % A0)
af = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
tr = w.s([tt, w.inst('simpl')], 'syl', '( %s -> T e. RR )' % A0)
t1 = w.s([tt, w.inst('simpr')], 'syl', '( %s -> 1 < T )' % A0)
r1 = a1(w, A0, '1re', '1 e. RR')
tm1 = w.s([tr, r1], 'resubcld', '( %s -> ( T - 1 ) e. RR )' % A0)
tm1rp = w.s([tm1, w.s([t1, w.s([r1, tr], 'posdifd', '( %s -> ( 1 < T <-> 0 < ( T - 1 ) ) )' % A0)], 'mpbid', '( %s -> 0 < ( T - 1 ) )' % A0)], 'elrpd',
            '( %s -> ( T - 1 ) e. RR+ )' % A0)
erp = w.s([tm1rp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A0, E0))
er = w.s([erp], 'rpred', '( %s -> %s e. RR )' % (A0, E0))
bi = w.s([tr, w.inst('elhp2')], 'syl', '( %s -> ( Z e. %s <-> ( Z e. CC /\\ T < %s ) ) )' % (A0, D, RZ))
both = w.s([zh, bi], 'mpbid', '( %s -> ( Z e. CC /\\ T < %s ) )' % (A0, RZ))
zc = w.s([both], 'simpld', '( %s -> Z e. CC )' % A0)
ltz = w.s([both], 'simprd', '( %s -> T < %s )' % (A0, RZ))
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
# ( 1 + E ) < ( Re ` Z )
e1 = w.s([er, r1], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A0, E0))
lt1 = w.s([er, tm1, r1, w.s([tm1rp, w.inst('rphalflt')], 'syl', '( %s -> %s < ( T - 1 ) )' % (A0, E0))], 'ltadd2dd',
          '( %s -> ( 1 + %s ) < ( 1 + ( T - 1 ) ) )' % (A0, E0))
pc = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), w.s([tr], 'recnd', '( %s -> T e. CC )' % A0)], 'pncan3d', '( %s -> ( 1 + ( T - 1 ) ) = T )' % A0)
lt2 = w.s([e1, tr, rz, w.s([lt1, pc], 'breqtrd', '( %s -> ( 1 + %s ) < T )' % (A0, E0)), ltz], 'lttrd', '( %s -> ( 1 + %s ) < %s )' % (A0, E0, RZ))
pack = w.s([w.s([cfb, erp], 'jca', '( %s -> ( %s /\\ %s e. RR+ ) )' % (A0, CFB, E0)), w.s([zc, lt2], 'jca', '( %s -> ( Z e. CC /\\ ( 1 + %s ) < %s ) )' % (A0, E0, RZ))],
           'jca', '( %s -> ( ( %s /\\ %s e. RR+ ) /\\ ( Z e. CC /\\ ( 1 + %s ) < %s ) ) )' % (A0, CFB, E0, E0, RZ))
FN = '( n e. NN |-> %s )' % LT('n', 'Z')
cv = w.s([pack, w.inst('dlogcvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, FN))
scl = w.s([pack, w.inst('dlogcl')], 'syl', '( %s -> sum_ k e. NN %s e. CC )' % (A0, LT('k', 'Z')))
# the value of DSF at Z
dv = w.s([w.s([hyp, w.inst('dserdv')], 'syl', '( %s -> ( CC _D %s ) = %s )' % (A0, LSF(), DSF()))], 'fveq1d',
         '( %s -> ( ( CC _D %s ) ` Z ) = ( %s ` Z ) )' % (A0, LSF(), DSF()))
sub = w.s([w.s([w.s([w.s([w.s([], 'negeq', '( z = Z -> -u z = -u Z )')], 'oveq2d', '( z = Z -> ( k ^c -u z ) = ( k ^c -u Z ) )')], 'oveq2d',
                    '( z = Z -> %s = %s )' % (LT('k', 'z'), LT('k', 'Z')))], 'negeqd', '( z = Z -> -u %s = -u %s )' % (LT('k', 'z'), LT('k', 'Z')))],
          'sumeq2sdv', '( z = Z -> sum_ k e. NN -u %s = sum_ k e. NN -u %s )' % (LT('k', 'z'), LT('k', 'Z')))
val = mpv(w, A0, DSF(), 'Z', 'sum_ k e. NN -u %s' % LT('k', 'Z'), sub, zh, vexd(w, A0, 'sum_ k e. NN -u %s' % LT('k', 'Z'), 'sum'), D)
# sum_ -u = -u sum_
nu1, z1, n1 = nnuz(w, A0)
Ak = '( %s /\\ k e. NN )' % A0
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
subk = w.s([w.s([], 'fveq2', '( n = k -> ( A ` n ) = ( A ` k ) )'), w.s([], 'fveq2', '( n = k -> ( log ` n ) = ( log ` k ) )')], 'oveq12d',
           '( n = k -> ( ( A ` n ) x. ( log ` n ) ) = ( ( A ` k ) x. ( log ` k ) ) )')
subk2 = w.s([subk, w.s([], 'oveq1', '( n = k -> ( n ^c -u Z ) = ( k ^c -u Z ) )')], 'oveq12d', '( n = k -> %s = %s )' % (LT('n', 'Z'), LT('k', 'Z')))
fv = mpv(w, Ak, FN, 'k', LT('k', 'Z'), subk2, kn, vexd(w, Ak, LT('k', 'Z')))
lkc = w.s([w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ak), kn], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % Ak),
                w.s([w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)], 'relogcld', '( %s -> ( log ` k ) e. RR )' % Ak)], 'recnd', '( %s -> ( log ` k ) e. CC )' % Ak)],
               'mulcld', '( %s -> ( ( A ` k ) x. ( log ` k ) ) e. CC )' % Ak),
           w.s([w.s([kn], 'nncnd', '( %s -> k e. CC )' % Ak), w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)], 'negcld', '( %s -> -u Z e. CC )' % Ak),
                w.inst('cxpcl')], 'syl2anc', '( %s -> ( k ^c -u Z ) e. CC )' % Ak)], 'mulcld', '( %s -> %s e. CC )' % (Ak, LT('k', 'Z')))
m1 = a1(w, A0, 'neg1cn', '-u 1 e. CC')
mc = w.s([nu1, z1, fv, lkc, cv, m1], 'isummulc2', '( %s -> ( -u 1 x. sum_ k e. NN %s ) = sum_ k e. NN ( -u 1 x. %s ) )' % (A0, LT('k', 'Z'), LT('k', 'Z')))
sm = w.s([w.s([lkc], 'mulm1d', '( %s -> ( -u 1 x. %s ) = -u %s )' % (Ak, LT('k', 'Z'), LT('k', 'Z')))], 'sumeq2dv',
         '( %s -> sum_ k e. NN ( -u 1 x. %s ) = sum_ k e. NN -u %s )' % (A0, LT('k', 'Z'), LT('k', 'Z')))
neg = w.s([scl], 'mulm1d', '( %s -> ( -u 1 x. sum_ k e. NN %s ) = -u sum_ k e. NN %s )' % (A0, LT('k', 'Z'), LT('k', 'Z')))
eq = w.s([w.s([mc, sm], 'eqtr2d', '( %s -> sum_ k e. NN -u %s = ( -u 1 x. sum_ k e. NN %s ) )' % (A0, LT('k', 'Z'), LT('k', 'Z'))), neg], 'eqtrd',
         '( %s -> sum_ k e. NN -u %s = -u sum_ k e. NN %s )' % (A0, LT('k', 'Z'), LT('k', 'Z')))
w.qed([w.s([dv, val], 'eqtrd', '( %s -> ( ( CC _D %s ) ` Z ) = sum_ k e. NN -u %s )' % (A0, LSF(), LT('k', 'Z'))), eq], 'eqtrd',
      '( %s -> ( ( CC _D %s ) ` Z ) = -u sum_ k e. NN %s )' % (A0, LSF(), LT('k', 'Z')))
run5(w)

# ---------------------------------------------------------------- dserdvbnd
w = W('dserdvbnd', 'The bound on the derivative of a Dirichlet series at a point of the half-plane, '
      'through C3\'s shifted-abscissa bound ~ dlogbnd .')
A0 = '( %s /\\ ( Z e. %s /\\ E e. RR+ /\\ ( 1 + E ) < %s ) )' % (HYP, D, RZ)
hyp = w.s([], 'simpl', '( %s -> %s )' % (A0, HYP))
zh = w.s([], 'simpr1', '( %s -> Z e. %s )' % (A0, D))
erp = w.s([], 'simpr2', '( %s -> E e. RR+ )' % A0)
lt = w.s([], 'simpr3', '( %s -> ( 1 + E ) < %s )' % (A0, RZ))
cfb = w.s([hyp, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CFB))
zc = w.s([a1(w, A0, 'hpss', '%s C_ CC' % D), zh], 'sseldd', '( %s -> Z e. CC )' % A0)
pack = w.s([w.s([cfb, erp], 'jca', '( %s -> ( %s /\\ E e. RR+ ) )' % (A0, CFB)), w.s([zc, lt], 'jca', '( %s -> ( Z e. CC /\\ ( 1 + E ) < %s ) )' % (A0, RZ))],
           'jca', '( %s -> ( ( %s /\\ E e. RR+ ) /\\ ( Z e. CC /\\ ( 1 + E ) < %s ) ) )' % (A0, CFB, RZ))
BND = '( ( C / E ) x. ( 1 + ( 1 / ( ( %s - E ) - 1 ) ) ) )' % RZ
bd = w.s([pack, w.inst('dlogbnd')], 'syl', '( %s -> ( abs ` sum_ k e. NN %s ) <_ %s )' % (A0, LT('k', 'Z'), BND))
scl = w.s([pack, w.inst('dlogcl')], 'syl', '( %s -> sum_ k e. NN %s e. CC )' % (A0, LT('k', 'Z')))
dvv = w.s([w.s([hyp, zh], 'jca', '( %s -> ( %s /\\ Z e. %s ) )' % (A0, HYP, D)), w.inst('dserdvval')], 'syl',
          '( %s -> ( ( CC _D %s ) ` Z ) = -u sum_ k e. NN %s )' % (A0, LSF(), LT('k', 'Z')))
ab = w.s([w.s([dvv], 'fveq2d', '( %s -> ( abs ` ( ( CC _D %s ) ` Z ) ) = ( abs ` -u sum_ k e. NN %s ) )' % (A0, LSF(), LT('k', 'Z'))),
          w.s([scl], 'absnegd', '( %s -> ( abs ` -u sum_ k e. NN %s ) = ( abs ` sum_ k e. NN %s ) )' % (A0, LT('k', 'Z'), LT('k', 'Z')))], 'eqtrd',
         '( %s -> ( abs ` ( ( CC _D %s ) ` Z ) ) = ( abs ` sum_ k e. NN %s ) )' % (A0, LSF(), LT('k', 'Z')))
w.qed([ab, bd], 'eqbrtrd', '( %s -> ( abs ` ( ( CC _D %s ) ` Z ) ) <_ %s )' % (A0, LSF(), BND))
run5(w)

# ---------------------------------------------------------------- lchrhol
AX = '( q e. NN |-> %s )' % CHV('q')
LCH = '( z e. %s |-> sum_ k e. NN ( %s x. ( k ^c -u z ) ) )' % (D, CHV('k'))
LAX = LSF(AX)
w = W('lchrhol', 'The Dirichlet L-series of a character is holomorphic on every open half-plane '
      '` ( Re ` z ) > T ` with ` 1 < T ` ( ~ dserhol at C3\'s ~ lchrcfb ): Mathlib\'s '
      '` DirichletCharacter.differentiable_LFunction ` to the right of the line one.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ ( T e. RR /\\ 1 < T ) )' % DC
nx = w.s([], 'simpl', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC))
tt = w.s([], 'simpr', '( %s -> ( T e. RR /\\ 1 < T ) )' % A0)
CFBX = '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (AX, AX)
cfbx = w.s([nx, w.inst('lchrcfb')], 'syl', '( %s -> %s )' % (A0, CFBX))
hol = w.s([w.s([cfbx, tt], 'jca', '( %s -> ( %s /\\ ( T e. RR /\\ 1 < T ) ) )' % (A0, CFBX)), w.inst('dserhol')], 'syl',
          '( %s -> %s )' % (A0, HOLG2(LAX, D)))
Azk = '( ( %s /\\ z e. %s ) /\\ k e. NN )' % (A0, D)
lv = w.s([w.s([w.s([nx], 'ad2antrr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Azk, DC)), w.s([], 'simpr', '( %s -> k e. NN )' % Azk)], 'jca',
              '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Azk, DC)), w.inst('lchrval')], 'syl', '( %s -> ( %s ` k ) = %s )' % (Azk, AX, CHV('k')))
tv = w.s([lv], 'oveq1d', '( %s -> ( ( %s ` k ) x. ( k ^c -u z ) ) = ( %s x. ( k ^c -u z ) ) )' % (Azk, AX, CHV('k')))
sm = w.s([tv], 'sumeq2dv', '( ( %s /\\ z e. %s ) -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u z ) ) = sum_ k e. NN ( %s x. ( k ^c -u z ) ) )' % (A0, D, AX, CHV('k')))
eq = w.s([sm], 'mpteq2dva', '( %s -> %s = %s )' % (A0, LAX, LCH))
b1 = w.s([eq], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (A0, LAX, D, LCH, D))
b2 = w.s([w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, LAX, LCH))], 'dmeqd',
              '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, LAX, LCH))], 'sseq2d',
         '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (A0, D, LAX, D, LCH))
w.qed([hol, w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (A0, HOLG2(LAX, D), HOLG2(LCH, D)))], 'mpbid',
      '( %s -> %s )' % (A0, HOLG2(LCH, D)))
run5(w)
