"""Sortie C3 section 7: the Dirichlet L-series of a character on Re > 1."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c3_lib import *

GG = '( DChr ` N )'
ZN = '( Z/nZ ` N )'
LH = '( ZRHom ` %s )' % ZN
DC = '( Base ` %s )' % GG
BZ = '( Base ` %s )' % ZN
AX = '( q e. NN |-> ( X ` ( %s ` q ) ) )' % LH
RZ = '( Re ` Z )'


def dchyp(w):
    """the four defining equations of the DChr context, as steps"""
    return [w.s([], 'eqid', '%s = %s' % (GG, GG)), w.s([], 'eqid', '%s = %s' % (ZN, ZN)),
            w.s([], 'eqid', '%s = %s' % (DC, DC)), w.s([], 'eqid', '%s = %s' % (LH, LH))]


# ---- lchrcl ----------------------------------------------------------------
w = W('lchrcl', 'A Dirichlet character composed with the ring homomorphism is complex on the positive integers.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ K e. NN )' % DC
g, z, b, l = dchyp(w)
xd = w.s([], 'simplr', '( %s -> X e. %s )' % (A0, DC))
kz = w.s([w.s([], 'simpr', '( %s -> K e. NN )' % A0)], 'nnzd', '( %s -> K e. ZZ )' % A0)
w.qed([g, z, b, l, xd, kz], 'dchrzrhcl', '( %s -> ( X ` ( %s ` K ) ) e. CC )' % (A0, LH)); run3(w)

# ---- lchrabs ---------------------------------------------------------------
w = W('lchrabs', 'A Dirichlet character has modulus at most one.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ K e. NN )' % DC
g, z, b, l = dchyp(w)
bb = w.s([], 'eqid', '%s = %s' % (BZ, BZ))
xd = w.s([], 'simplr', '( %s -> X e. %s )' % (A0, DC))
nn0 = w.s([w.s([], 'simpll', '( %s -> N e. NN )' % A0)], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
kz = w.s([w.s([], 'simpr', '( %s -> K e. NN )' % A0)], 'nnzd', '( %s -> K e. ZZ )' % A0)
fo = w.s([nn0, w.s([z, l], 'znzrhfo', '( N e. NN0 -> %s : ZZ -onto-> %s )' % (LH, BZ))], 'mpd' if False else 'syl',
         '( %s -> %s : ZZ -onto-> %s )' % (A0, LH, BZ))
ff = w.s([fo, w.inst('fof')], 'syl', '( %s -> %s : ZZ --> %s )' % (A0, LH, BZ))
mem = w.s([ff, kz], 'ffvelcdmd', '( %s -> ( %s ` K ) e. %s )' % (A0, LH, BZ))
w.qed([g, b, z, bb, xd, mem], 'dchrabs2', '( %s -> ( abs ` ( X ` ( %s ` K ) ) ) <_ 1 )' % (A0, LH)); run3(w)

# ---- lchrval ---------------------------------------------------------------
w = W('lchrval', 'The value of the coefficient function of a Dirichlet L-series.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ K e. NN )' % DC
kn = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
sub = w.s([w.s([], 'fveq2', '( q = K -> ( %s ` q ) = ( %s ` K ) )' % (LH, LH))], 'fveq2d',
          '( q = K -> ( X ` ( %s ` q ) ) = ( X ` ( %s ` K ) ) )' % (LH, LH))
em = w.s([], 'eqid', '%s = %s' % (AX, AX))
fv = w.s([sub, em], 'fvmptg',
         '( ( K e. NN /\\ ( X ` ( %s ` K ) ) e. _V ) -> ( %s ` K ) = ( X ` ( %s ` K ) ) )' % (LH, AX, LH))
ex = w.s([w.s([], 'fvex', '( X ` ( %s ` K ) ) e. _V' % LH)], 'a1i', '( %s -> ( X ` ( %s ` K ) ) e. _V )' % (A0, LH))
w.qed([kn, ex, fv], 'syl2anc', '( %s -> ( %s ` K ) = ( X ` ( %s ` K ) ) )' % (A0, AX, LH)); run3(w)

# ---- lchrcfb ---------------------------------------------------------------
w = W('lchrcfb', 'The coefficient function of a Dirichlet L-series is bounded by one.')
A0 = '( N e. NN /\\ X e. %s )' % DC
Am = '( %s /\\ m e. NN )' % A0
A0k = '( %s /\\ q e. NN )' % A0
mn = w.s([], 'simpr', '( %s -> m e. NN )' % Am)
A0m = '( %s /\\ m e. NN )' % A0
cl = w.s([w.s([], 'lchrcl', '( ( %s /\\ m e. NN ) -> ( X ` ( %s ` m ) ) e. CC )' % (A0, LH))], 'idi',
         '( %s -> ( X ` ( %s ` m ) ) e. CC )' % (Am, LH))
vm = w.s([w.s([], 'lchrval', '( ( %s /\\ m e. NN ) -> ( %s ` m ) = ( X ` ( %s ` m ) ) )' % (A0, AX, LH))], 'idi',
         '( %s -> ( %s ` m ) = ( X ` ( %s ` m ) ) )' % (Am, AX, LH))
ab = w.s([w.s([], 'lchrabs', '( ( %s /\\ m e. NN ) -> ( abs ` ( X ` ( %s ` m ) ) ) <_ 1 )' % (A0, LH))], 'idi',
         '( %s -> ( abs ` ( X ` ( %s ` m ) ) ) <_ 1 )' % (Am, LH))
bnd = w.s([w.s([vm], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` ( X ` ( %s ` m ) ) ) )' % (Am, AX, LH)), ab],
          'eqbrtrd', '( %s -> ( abs ` ( %s ` m ) ) <_ 1 )' % (Am, AX))
ral = w.s([bnd], 'ralrimiva', '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (A0, AX))
clk = w.s([], 'lchrcl', '( %s -> ( X ` ( %s ` q ) ) e. CC )' % (A0k, LH))
eax = w.s([], 'eqid', '%s = %s' % (AX, AX))
ff = w.s([clk, eax], 'fmptd',
         '( %s -> %s : NN --> CC )' % (A0, AX))
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
w.qed([ff, r1, ral], '3jca',
      '( %s -> ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) )' % (A0, AX, AX)); run3(w)

# ---- lchrbnd ---------------------------------------------------------------
w = W('lchrbnd', 'The Dirichlet L-series of a character is bounded on the half-plane to the right of the line one.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ ( Z e. CC /\\ 1 < %s ) )' % (DC, RZ)
Ak = '( %s /\\ k e. NN )' % A0
nx = w.s([], 'simpl', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC))
zh = w.s([], 'simpr', '( %s -> ( Z e. CC /\\ 1 < %s ) )' % (A0, RZ))
cfb = w.s([nx, w.inst('lchrcfb')], 'syl',
          '( %s -> ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) )' % (A0, AX, AX))
pack = w.s([cfb, zh], 'jca',
           '( %s -> ( ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) /\\ ( Z e. CC /\\ 1 < %s ) ) )' % (A0, AX, AX, RZ))
bnd = w.s([pack, w.inst('dserbnd')], 'syl',
          '( %s -> ( abs ` sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) ) <_ ( 1 x. ( 1 + ( 1 / ( %s - 1 ) ) ) ) )' % (A0, AX, RZ))
# the coefficient values
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
vk = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ak, DC)), kn], 'jca',
              '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Ak, DC)), w.inst('lchrval')], 'syl',
         '( %s -> ( %s ` k ) = ( X ` ( %s ` k ) ) )' % (Ak, AX, LH))
seq = w.s([w.s([vk], 'oveq1d',
                '( %s -> ( ( %s ` k ) x. ( k ^c -u Z ) ) = ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) )' % (Ak, AX, LH))],
          'sumeq2dv',
          '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) = sum_ k e. NN ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) )' % (A0, AX, LH))
bnd2 = w.s([w.s([seq], 'fveq2d',
                 '( %s -> ( abs ` sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u Z ) ) ) = ( abs ` sum_ k e. NN ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) ) )' % (A0, AX, LH)),
            bnd], 'eqbrtrrd',
           '( %s -> ( abs ` sum_ k e. NN ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) ) <_ ( 1 x. ( 1 + ( 1 / ( %s - 1 ) ) ) ) )' % (A0, LH, RZ))
# drop the factor one
zc = w.s([zh, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
zgt = w.s([zh, w.inst('simpr')], 'syl', '( %s -> 1 < %s )' % (A0, RZ))
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RZ))
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)
tm1rp = w.s([w.s([rz, r1], 'resubcld', '( %s -> ( %s - 1 ) e. RR )' % (A0, RZ)),
             w.s([zgt, w.s([r1, rz], 'posdifd', '( %s -> ( 1 < %s <-> 0 < ( %s - 1 ) ) )' % (A0, RZ, RZ))], 'mpbid',
                 '( %s -> 0 < ( %s - 1 ) )' % (A0, RZ))], 'elrpd', '( %s -> ( %s - 1 ) e. RR+ )' % (A0, RZ))
bre = w.s([r1, w.s([w.s([tm1rp], 'rpreccld', '( %s -> ( 1 / ( %s - 1 ) ) e. RR+ )' % (A0, RZ))], 'rpred',
                   '( %s -> ( 1 / ( %s - 1 ) ) e. RR )' % (A0, RZ))], 'readdcld',
          '( %s -> ( 1 + ( 1 / ( %s - 1 ) ) ) e. RR )' % (A0, RZ))
one = w.s([w.s([bre], 'recnd', '( %s -> ( 1 + ( 1 / ( %s - 1 ) ) ) e. CC )' % (A0, RZ)), w.inst('mullid')], 'syl',
          '( %s -> ( 1 x. ( 1 + ( 1 / ( %s - 1 ) ) ) ) = ( 1 + ( 1 / ( %s - 1 ) ) ) )' % (A0, RZ, RZ))
w.qed([bnd2, one], 'breqtrd',
      '( %s -> ( abs ` sum_ k e. NN ( ( X ` ( %s ` k ) ) x. ( k ^c -u Z ) ) ) <_ ( 1 + ( 1 / ( %s - 1 ) ) ) )' % (A0, LH, RZ)); run3(w)

# ---- lchrdvb ---------------------------------------------------------------
import sys as _s, os as _o; _s.path.insert(0, _o.path.join(_o.path.dirname(__file__), '..'))
from lin import linarith
LAX = '( ( ( %s ` k ) x. ( log ` k ) ) x. ( k ^c -u Z ) )' % AX
LXX = '( ( ( X ` ( %s ` k ) ) x. ( log ` k ) ) x. ( k ^c -u Z ) )' % LH
HAF = '( 1 / 2 )'
DEN = '( ( %s - %s ) - 1 )' % (RZ, HAF)
w = W('lchrdvb', 'The logarithmically weighted Dirichlet L-series of a character is bounded by six on the half-plane to the right of the line two.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ ( Z e. CC /\\ 2 <_ %s ) )' % (DC, RZ)
Ak = '( %s /\\ k e. NN )' % A0
nx = w.s([], 'simpl', '( %s -> ( N e. NN /\\ X e. %s ) )' % (A0, DC))
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
z2 = w.s([], 'simprr', '( %s -> 2 <_ %s )' % (A0, RZ))
rz = w.s([zc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RZ))
cfbx = w.s([nx, w.inst('lchrcfb')], 'syl',
           '( %s -> ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) )' % (A0, AX, AX))
hrp = w.s([w.s([w.s([], '1rp', '1 e. RR+'), w.inst('rphalfcl')], 'ax-mp', '%s e. RR+' % HAF)], 'a1i',
          '( %s -> %s e. RR+ )' % (A0, HAF))
hre = w.s([w.s([], 'halfre', '%s e. RR' % HAF)], 'a1i', '( %s -> %s e. RR )' % (A0, HAF))
r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
lt = linarith(w, A0, [z2], '( 1 + %s ) < %s' % (HAF, RZ), leaves={RZ: rz})
pack = w.s([w.s([cfbx, hrp], 'jca',
                '( %s -> ( ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) /\\ %s e. RR+ ) )' % (A0, AX, AX, HAF)),
            w.s([zc, lt], 'jca', '( %s -> ( Z e. CC /\\ ( 1 + %s ) < %s ) )' % (A0, HAF, RZ))], 'jca',
           '( %s -> ( ( ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) /\\ %s e. RR+ ) /\\ ( Z e. CC /\\ ( 1 + %s ) < %s ) ) )' % (A0, AX, AX, HAF, HAF, RZ))
bnd = w.s([pack, w.inst('dlogbnd')], 'syl',
          '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( ( 1 / %s ) x. ( 1 + ( 1 / %s ) ) ) )' % (A0, LAX, HAF, DEN))
# rewrite the coefficients
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
vk = w.s([w.s([w.s([nx], 'adantr', '( %s -> ( N e. NN /\\ X e. %s ) )' % (Ak, DC)), kn], 'jca',
              '( %s -> ( ( N e. NN /\\ X e. %s ) /\\ k e. NN ) )' % (Ak, DC)), w.inst('lchrval')], 'syl',
         '( %s -> ( %s ` k ) = ( X ` ( %s ` k ) ) )' % (Ak, AX, LH))
body = w.s([w.s([vk], 'oveq1d',
                 '( %s -> ( ( %s ` k ) x. ( log ` k ) ) = ( ( X ` ( %s ` k ) ) x. ( log ` k ) ) )' % (Ak, AX, LH))],
           'oveq1d', '( %s -> %s = %s )' % (Ak, LAX, LXX))
ser = w.s([body], 'sumeq2dv', '( %s -> sum_ k e. NN %s = sum_ k e. NN %s )' % (A0, LAX, LXX))
b2 = w.s([w.s([ser], 'fveq2d', '( %s -> ( abs ` sum_ k e. NN %s ) = ( abs ` sum_ k e. NN %s ) )' % (A0, LAX, LXX)), bnd],
         'eqbrtrrd', '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( ( 1 / %s ) x. ( 1 + ( 1 / %s ) ) ) )' % (A0, LXX, HAF, DEN))
# the numeral bound
denre = w.s([w.s([rz, hre], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RZ, HAF)),
             w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0)], 'resubcld',
            '( %s -> %s e. RR )' % (A0, DEN))
denge = linarith(w, A0, [z2], '%s <_ %s' % (HAF, DEN), leaves={RZ: rz})
denpos = linarith(w, A0, [z2], '0 < %s' % DEN, leaves={RZ: rz})
lr = w.s([w.s([hre, w.s([w.s([], 'halfgt0', '0 < %s' % HAF)], 'a1i', '( %s -> 0 < %s )' % (A0, HAF))], 'jca',
              '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, HAF, HAF)),
          w.s([denre, denpos], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, DEN, DEN)), w.inst('lerec')],
         'syl2anc', '( %s -> ( %s <_ %s <-> ( 1 / %s ) <_ ( 1 / %s ) ) )' % (A0, HAF, DEN, DEN, HAF))
rle = w.s([denge, lr], 'mpbid', '( %s -> ( 1 / %s ) <_ ( 1 / %s ) )' % (A0, DEN, HAF))
rr = w.s([w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0')], 'pm3.2i', '( 2 e. CC /\\ 2 =/= 0 )'),
               w.inst('recrec')], 'ax-mp', '( 1 / %s ) = 2' % HAF)], 'a1i', '( %s -> ( 1 / %s ) = 2 )' % (A0, HAF))
rle2 = w.s([rle, rr], 'breqtrd', '( %s -> ( 1 / %s ) <_ 2 )' % (A0, DEN))
recre = w.s([w.s([w.s([denre, denpos], 'elrpd', '( %s -> %s e. RR+ )' % (A0, DEN))], 'rpreccld',
                 '( %s -> ( 1 / %s ) e. RR+ )' % (A0, DEN))], 'rpred', '( %s -> ( 1 / %s ) e. RR )' % (A0, DEN))
b3 = w.s([b2, w.s([rr], 'oveq1d',
                   '( %s -> ( ( 1 / %s ) x. ( 1 + ( 1 / %s ) ) ) = ( 2 x. ( 1 + ( 1 / %s ) ) ) )' % (A0, HAF, DEN, DEN))],
         'breqtrd', '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( 2 x. ( 1 + ( 1 / %s ) ) ) )' % (A0, LXX, DEN))
fin = linarith(w, A0, [rle2], '( 2 x. ( 1 + ( 1 / %s ) ) ) <_ 6' % DEN,
               leaves={'( 1 / %s )' % DEN: recre})
absre = w.s([w.s([w.s([w.s([cfbx, hrp], 'jca',
                            '( %s -> ( ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) /\\ %s e. RR+ ) )' % (A0, AX, AX, HAF)),
                       w.s([zc, lt], 'jca', '( %s -> ( Z e. CC /\\ ( 1 + %s ) < %s ) )' % (A0, HAF, RZ))], 'jca',
                      '( %s -> ( ( ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) /\\ %s e. RR+ ) /\\ ( Z e. CC /\\ ( 1 + %s ) < %s ) ) )' % (A0, AX, AX, HAF, HAF, RZ)),
                  w.inst('dlogcl')], 'syl', '( %s -> sum_ k e. NN %s e. CC )' % (A0, LAX))], 'idi',
            '( %s -> sum_ k e. NN %s e. CC )' % (A0, LAX))
sumx = w.s([w.s([ser], 'eqcomd', '( %s -> sum_ k e. NN %s = sum_ k e. NN %s )' % (A0, LXX, LAX)), absre], 'eqeltrd',
           '( %s -> sum_ k e. NN %s e. CC )' % (A0, LXX))
absr = w.s([sumx], 'abscld', '( %s -> ( abs ` sum_ k e. NN %s ) e. RR )' % (A0, LXX))
recc = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
bre = w.s([recc, w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0), recre], 'readdcld',
                     '( %s -> ( 1 + ( 1 / %s ) ) e. RR )' % (A0, DEN))], 'remulcld',
          '( %s -> ( 2 x. ( 1 + ( 1 / %s ) ) ) e. RR )' % (A0, DEN))
r6 = w.s([w.s([], '6re', '6 e. RR')], 'a1i', '( %s -> 6 e. RR )' % A0)
w.qed([absr, bre, r6, b3, fin], 'letrd',
      '( %s -> ( abs ` sum_ k e. NN %s ) <_ 6 )' % (A0, LXX)); run3(w)

# ---- dchrper ---------------------------------------------------------------
ONE = '( 0g ` %s )' % GG
WIF = '( 0 ..^ N )'
WI = 'if ( N = 0 , ZZ , %s )' % WIF
w = W('dchrper', 'A nonprincipal Dirichlet character sums to zero over a complete residue system.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ X =/= %s )' % (DC, ONE)
Ak = '( %s /\\ k e. %s )' % (A0, WI)
Aa = '( %s /\\ a e. %s )' % (A0, BZ)
nn = w.s([], 'simpll', '( %s -> N e. NN )' % A0)
xd = w.s([], 'simplr', '( %s -> X e. %s )' % (A0, DC))
xne = w.s([], 'simpr', '( %s -> X =/= %s )' % (A0, ONE))
g, z, b, l = dchyp(w)
bb = w.s([], 'eqid', '%s = %s' % (BZ, BZ))
o1 = w.s([], 'eqid', '%s = %s' % (ONE, ONE))
nn0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
nne = w.s([nn], 'nnne0d', '( %s -> N =/= 0 )' % A0)
# the sum over the base is zero
dsum = w.s([g, z, b, o1, xd, bb], 'dchrsum',
           '( %s -> sum_ a e. %s ( X ` a ) = if ( X = %s , ( phi ` N ) , 0 ) )' % (A0, BZ, ONE))
z0 = w.s([xne, w.inst('ifnefalse')], 'syl', '( %s -> if ( X = %s , ( phi ` N ) , 0 ) = 0 )' % (A0, ONE))
base0 = w.s([dsum, z0], 'eqtrd', '( %s -> sum_ a e. %s ( X ` a ) = 0 )' % (A0, BZ))
# the enumeration of the base by the residues below N
fr = w.s([], 'eqid', '( %s |` %s ) = ( %s |` %s )' % (LH, WI, LH, WI))
wq = w.s([], 'eqid', '%s = %s' % (WI, WI))
f1o = w.s([nn0, w.s([z, bb, fr, wq], 'znf1o', '( N e. NN0 -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (LH, WI, WI, BZ))],
          'syl', '( %s -> ( %s |` %s ) : %s -1-1-onto-> %s )' % (A0, LH, WI, WI, BZ))
weq = w.s([nne, w.inst('ifnefalse')], 'syl', '( %s -> %s = %s )' % (A0, WI, WIF))
wfin = w.s([weq, w.s([w.s([], 'fzofi', '%s e. Fin' % WIF)], 'a1i', '( %s -> %s e. Fin )' % (A0, WIF))], 'eqeltrd',
           '( %s -> %s e. Fin )' % (A0, WI))
fres = w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, WI)), w.inst('fvres')], 'syl',
           '( %s -> ( ( %s |` %s ) ` k ) = ( %s ` k ) )' % (Ak, LH, WI, LH))
xf = w.s([g, z, b, bb, w.s([xd], 'idi', '( %s -> X e. %s )' % (A0, DC))], 'dchrf', '( %s -> X : %s --> CC )' % (A0, BZ))
xacl = w.s([w.s([xf], 'adantr', '( %s -> X : %s --> CC )' % (Aa, BZ)), w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, BZ))],
           'ffvelcdmd', '( %s -> ( X ` a ) e. CC )' % Aa)
sub = w.s([], 'fveq2', '( a = ( %s ` k ) -> ( X ` a ) = ( X ` ( %s ` k ) ) )' % (LH, LH))
reix = w.s([sub, wfin, f1o, fres, xacl], 'fsumf1o',
           '( %s -> sum_ a e. %s ( X ` a ) = sum_ k e. %s ( X ` ( %s ` k ) ) )' % (A0, BZ, WI, LH))
z1 = w.s([w.s([reix], 'eqcomd', '( %s -> sum_ k e. %s ( X ` ( %s ` k ) ) = sum_ a e. %s ( X ` a ) )' % (A0, WI, LH, BZ)),
          base0], 'eqtrd', '( %s -> sum_ k e. %s ( X ` ( %s ` k ) ) = 0 )' % (A0, WI, LH))
w.qed([w.s([w.s([weq], 'eqcomd', '( %s -> %s = %s )' % (A0, WIF, WI))], 'sumeq1d',
           '( %s -> sum_ k e. %s ( X ` ( %s ` k ) ) = sum_ k e. %s ( X ` ( %s ` k ) ) )' % (A0, WIF, LH, WI, LH)), z1],
      'eqtrd', '( %s -> sum_ k e. %s ( X ` ( %s ` k ) ) = 0 )' % (A0, WIF, LH)); run3(w)

# ---- vmachsum --------------------------------------------------------------
DVS = '{ x e. NN | x || K }'
SUMD = '( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( X ` ( %s ` ( K / d ) ) ) )' % (LH, LH)
w = W('vmachsum', 'The Dirichlet convolution of the von Mangoldt function twisted by a character: the coefficient identity behind the logarithmic derivative.')
A0 = '( ( N e. NN /\\ X e. %s ) /\\ K e. NN )' % DC
Ad = '( %s /\\ d e. %s )' % (A0, DVS)
nn = w.s([], 'simpll', '( %s -> N e. NN )' % A0)
xd = w.s([], 'simplr', '( %s -> X e. %s )' % (A0, DC))
kn = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
g, z, b, l = dchyp(w)
dmem = w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, DVS))
knd = w.s([kn], 'adantr', '( %s -> K e. NN )' % Ad)
dnn = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % DVS)], 'a1i', '( %s -> %s C_ NN )' % (Ad, DVS)), dmem], 'sseldd',
          '( %s -> d e. NN )' % Ad)
qdv = w.s([knd, dmem, w.inst('dvdsdivcl')], 'syl2anc', '( %s -> ( K / d ) e. %s )' % (Ad, DVS))
qn = w.s([w.s([w.s([], 'ssrab2', '%s C_ NN' % DVS)], 'a1i', '( %s -> %s C_ NN )' % (Ad, DVS)), qdv], 'sseldd',
         '( %s -> ( K / d ) e. NN )' % Ad)
xdd = w.s([xd], 'adantr', '( %s -> X e. %s )' % (Ad, DC))
dz = w.s([dnn], 'nnzd', '( %s -> d e. ZZ )' % Ad)
qz = w.s([qn], 'nnzd', '( %s -> ( K / d ) e. ZZ )' % Ad)
mul = w.s([g, z, b, l, xdd, dz, qz], 'dchrzrhmul',
          '( %s -> ( X ` ( %s ` ( d x. ( K / d ) ) ) ) = ( ( X ` ( %s ` d ) ) x. ( X ` ( %s ` ( K / d ) ) ) ) )' % (Ad, LH, LH, LH))
can = w.s([w.s([knd], 'nncnd', '( %s -> K e. CC )' % Ad), w.s([dnn], 'nncnd', '( %s -> d e. CC )' % Ad),
           w.s([dnn], 'nnne0d', '( %s -> d =/= 0 )' % Ad), w.inst('divcan2')], 'syl3anc',
          '( %s -> ( d x. ( K / d ) ) = K )' % Ad)
mul2 = w.s([w.s([w.s([can], 'fveq2d', '( %s -> ( %s ` ( d x. ( K / d ) ) ) = ( %s ` K ) )' % (Ad, LH, LH))], 'fveq2d',
                '( %s -> ( X ` ( %s ` ( d x. ( K / d ) ) ) ) = ( X ` ( %s ` K ) ) )' % (Ad, LH, LH)), mul], 'eqtr3d',
           '( %s -> ( X ` ( %s ` K ) ) = ( ( X ` ( %s ` d ) ) x. ( X ` ( %s ` ( K / d ) ) ) ) )' % (Ad, LH, LH, LH))
# the summand equals chi(L K) times Lam d
cd1 = w.s([g, z, b, l, xdd, dz], 'dchrzrhcl', '( %s -> ( X ` ( %s ` d ) ) e. CC )' % (Ad, LH))
cq1 = w.s([g, z, b, l, xdd, qz], 'dchrzrhcl', '( %s -> ( X ` ( %s ` ( K / d ) ) ) e. CC )' % (Ad, LH))
lamc = w.s([w.s([dnn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` d ) e. RR )' % Ad)], 'recnd',
           '( %s -> ( Lam ` d ) e. CC )' % Ad)
sw = w.s([cd1, lamc, cq1], 'mul32d',
         '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( Lam ` d ) ) x. ( X ` ( %s ` ( K / d ) ) ) ) = ( ( ( X ` ( %s ` d ) ) x. ( X ` ( %s ` ( K / d ) ) ) ) x. ( Lam ` d ) ) )' % (Ad, LH, LH, LH, LH))
body = w.s([sw, w.s([w.s([mul2], 'eqcomd',
                          '( %s -> ( ( X ` ( %s ` d ) ) x. ( X ` ( %s ` ( K / d ) ) ) ) = ( X ` ( %s ` K ) ) )' % (Ad, LH, LH, LH))],
                    'oveq1d',
                    '( %s -> ( ( ( X ` ( %s ` d ) ) x. ( X ` ( %s ` ( K / d ) ) ) ) x. ( Lam ` d ) ) = ( ( X ` ( %s ` K ) ) x. ( Lam ` d ) ) )' % (Ad, LH, LH, LH))],
           'eqtrd', '( %s -> %s = ( ( X ` ( %s ` K ) ) x. ( Lam ` d ) ) )' % (Ad, SUMD, LH))
ser = w.s([body], 'sumeq2dv',
          '( %s -> sum_ d e. %s %s = sum_ d e. %s ( ( X ` ( %s ` K ) ) x. ( Lam ` d ) ) )' % (A0, DVS, SUMD, DVS, LH))
# pull the character out of the divisor sum
dfin = w.s([w.s([w.s([kn, w.inst('dvdsssfz1')], 'syl', '( %s -> { p e. NN | p || K } C_ ( 1 ... K ) )' % A0)], 'idi',
                '( %s -> { p e. NN | p || K } C_ ( 1 ... K ) )' % A0)], 'idi',
           '( %s -> { p e. NN | p || K } C_ ( 1 ... K ) )' % A0)
cabk = w.s([g, z, b, l, xd, w.s([kn], 'nnzd', '( %s -> K e. ZZ )' % A0)], 'dchrzrhcl',
           '( %s -> ( X ` ( %s ` K ) ) e. CC )' % (A0, LH))
dvfin = w.s([w.s([kn, w.inst('dvdsfi')], 'syl', '( %s -> %s e. Fin )' % (A0, DVS))], 'idi',
            '( %s -> %s e. Fin )' % (A0, DVS))
pull = w.s([dvfin, cabk, lamc], 'fsummulc2',
           '( %s -> ( ( X ` ( %s ` K ) ) x. sum_ d e. %s ( Lam ` d ) ) = sum_ d e. %s ( ( X ` ( %s ` K ) ) x. ( Lam ` d ) ) )' % (A0, LH, DVS, DVS, LH))
vms = w.s([w.s([kn, w.inst('vmasum')], 'syl', '( %s -> sum_ n e. { x e. NN | x || K } ( Lam ` n ) = ( log ` K ) )' % A0)],
          'idi', '( %s -> sum_ n e. { x e. NN | x || K } ( Lam ` n ) = ( log ` K ) )' % A0)
cbs = w.s([w.s([], 'fveq2', '( n = d -> ( Lam ` n ) = ( Lam ` d ) )')], 'cbvsumv',
          'sum_ n e. %s ( Lam ` n ) = sum_ d e. %s ( Lam ` d )' % (DVS, DVS))
vms2 = w.s([w.s([w.s([cbs], 'eqcomi', 'sum_ d e. %s ( Lam ` d ) = sum_ n e. %s ( Lam ` n )' % (DVS, DVS))], 'a1i',
                '( %s -> sum_ d e. %s ( Lam ` d ) = sum_ n e. %s ( Lam ` n ) )' % (A0, DVS, DVS)), vms], 'eqtrd',
           '( %s -> sum_ d e. %s ( Lam ` d ) = ( log ` K ) )' % (A0, DVS))
w.qed([ser, w.s([w.s([pull], 'eqcomd',
                      '( %s -> sum_ d e. %s ( ( X ` ( %s ` K ) ) x. ( Lam ` d ) ) = ( ( X ` ( %s ` K ) ) x. sum_ d e. %s ( Lam ` d ) ) )' % (A0, DVS, LH, LH, DVS)),
                 w.s([vms2], 'oveq2d',
                     '( %s -> ( ( X ` ( %s ` K ) ) x. sum_ d e. %s ( Lam ` d ) ) = ( ( X ` ( %s ` K ) ) x. ( log ` K ) ) )' % (A0, LH, DVS, LH))],
                'eqtrd',
                '( %s -> sum_ d e. %s ( ( X ` ( %s ` K ) ) x. ( Lam ` d ) ) = ( ( X ` ( %s ` K ) ) x. ( log ` K ) ) )' % (A0, DVS, LH, LH))],
      'eqtrd', '( %s -> sum_ d e. %s %s = ( ( X ` ( %s ` K ) ) x. ( log ` K ) ) )' % (A0, DVS, SUMD, LH)); run3(w)
