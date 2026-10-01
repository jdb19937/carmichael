"""C7, eta block 1: the parity lemma, the coefficient sequence ( k mod 2 ) as an
ABS instance, and the eta series through C4/C5's Abel block (mod2p1, mod2abs,
etacvg, etabnd, etabnd4, etahol)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq, nlinarith

# ---------------------------------------------------------------- mod2p1
A0 = 'K e. ZZ'
G = '( ( K + 1 ) mod 2 ) = ( 1 - ( K mod 2 ) )'
w = W('mod2p1', 'The parity of ` K + 1 ` from the parity of ` K `: ` ( K + 1 ) mod 2 = 1 - ( K mod 2 ) `. '
      'The one parity computation behind the alternating coefficients of the eta series.')
A1 = '( K e. ZZ /\\ 2 || K )'
kz1 = w.s([], 'simpl', '( %s -> K e. ZZ )' % A1)
ev1 = w.s([], 'simpr', '( %s -> 2 || K )' % A1)
m0 = w.s([ev1, w.s([kz1, w.inst('mod2eq0even')], 'syl', '( %s -> ( ( K mod 2 ) = 0 <-> 2 || K ) )' % A1)], 'mpbird', '( %s -> ( K mod 2 ) = 0 )' % A1)
odd1 = w.s([w.s([ev1], 'notnotd', '( %s -> -. -. 2 || K )' % A1), w.s([kz1, w.inst('oddp1even')], 'syl', '( %s -> ( -. 2 || K <-> 2 || ( K + 1 ) ) )' % A1)], 'mtbid', '( %s -> -. 2 || ( K + 1 ) )' % A1)
m1 = w.s([odd1, w.s([w.s([kz1], 'peano2zd', '( %s -> ( K + 1 ) e. ZZ )' % A1), w.inst('mod2eq1n2dvds')], 'syl', '( %s -> ( ( ( K + 1 ) mod 2 ) = 1 <-> -. 2 || ( K + 1 ) ) )' % A1)], 'mpbird',
         '( %s -> ( ( K + 1 ) mod 2 ) = 1 )' % A1)
r1 = w.s([w.s([m0], 'oveq2d', '( %s -> ( 1 - ( K mod 2 ) ) = ( 1 - 0 ) )' % A1), a1(w, A1, '1m0e1', '( 1 - 0 ) = 1')], 'eqtrd', '( %s -> ( 1 - ( K mod 2 ) ) = 1 )' % A1)
c1 = w.s([m1, r1], 'eqtr4d', '( %s -> %s )' % (A1, G))
A2 = '( K e. ZZ /\\ -. 2 || K )'
kz2 = w.s([], 'simpl', '( %s -> K e. ZZ )' % A2)
od2 = w.s([], 'simpr', '( %s -> -. 2 || K )' % A2)
m1b = w.s([od2, w.s([kz2, w.inst('mod2eq1n2dvds')], 'syl', '( %s -> ( ( K mod 2 ) = 1 <-> -. 2 || K ) )' % A2)], 'mpbird', '( %s -> ( K mod 2 ) = 1 )' % A2)
ev2 = w.s([od2, w.s([kz2, w.inst('oddp1even')], 'syl', '( %s -> ( -. 2 || K <-> 2 || ( K + 1 ) ) )' % A2)], 'mpbid', '( %s -> 2 || ( K + 1 ) )' % A2)
m0b = w.s([ev2, w.s([w.s([kz2], 'peano2zd', '( %s -> ( K + 1 ) e. ZZ )' % A2), w.inst('mod2eq0even')], 'syl', '( %s -> ( ( ( K + 1 ) mod 2 ) = 0 <-> 2 || ( K + 1 ) ) )' % A2)], 'mpbird',
          '( %s -> ( ( K + 1 ) mod 2 ) = 0 )' % A2)
r2 = w.s([w.s([m1b], 'oveq2d', '( %s -> ( 1 - ( K mod 2 ) ) = ( 1 - 1 ) )' % A2), a1(w, A2, '1m1e0', '( 1 - 1 ) = 0')], 'eqtrd', '( %s -> ( 1 - ( K mod 2 ) ) = 0 )' % A2)
c2 = w.s([m0b, r2], 'eqtr4d', '( %s -> %s )' % (A2, G))
w.qed([c1, c2], 'pm2.61dan', '( %s -> %s )' % (A0, G))
run7(w)

# ---------------------------------------------------------------- mod2abs
Am = 'm e. NN'
w = W('mod2abs', 'The coefficient sequence ` ( k mod 2 ) ` of the eta series is a complex '
      'sequence bounded by ` 1 `: the ABS package of C4\'s Abel block at ` B = 1 `.')
Aq = 'q e. NN'
mq = mod2facts(w, Aq, w.s([w.s([], 'id', '( %s -> q e. NN )' % Aq)], 'nnzd', '( %s -> q e. ZZ )' % Aq))
fn = w.s([w.s([], 'eqid', '%s = %s' % (SM2, SM2)), mq['cn']], 'fmpti', '%s : NN --> CC' % SM2)
mm = mod2facts(w, Am, w.s([w.s([], 'id', '( %s -> m e. NN )' % Am)], 'nnzd', '( %s -> m e. ZZ )' % Am))
val = sm2val(w, 'm')
ab = w.s([w.s([w.s([val], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` ( m mod 2 ) ) )' % (Am, SM2)), w.s([mm['re'], mm['ge0']], 'absidd', '( %s -> ( abs ` ( m mod 2 ) ) = ( m mod 2 ) )' % Am)], 'eqtrd',
              '( %s -> ( abs ` ( %s ` m ) ) = ( m mod 2 ) )' % (Am, SM2)), mm['le1']], 'eqbrtrd', '( %s -> ( abs ` ( %s ` m ) ) <_ 1 )' % (Am, SM2))
w.qed([fn, w.s([], '1re', '1 e. RR'), w.s([ab], 'rgen', 'A. m e. NN ( abs ` ( %s ` m ) ) <_ 1' % SM2)], '3pm3.2i', '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (SM2, SM2))
run7(w)

MABS = '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (SM2, SM2)


def SETT(K, Z):
    return '( ( %s ` %s ) x. %s )' % (SM2, K, DIF(K, Z))


# ---------------------------------------------------------------- etacvg
A0 = ZP0
w = W('etacvg', 'The Abel-summed eta series converges on ` Re z > 0 ` ( ~ abcvg at the '
      'coefficients ` ( k mod 2 ) `, ~ mod2abs ).')
cv = w.s([w.s([a1(w, A0, 'mod2abs', MABS), w.s([], 'id', '( %s -> %s )' % (A0, A0))], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, MABS, A0)), w.inst('abcvg')], 'syl',
         '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (A0, SETT('n', 'Z')))
An = '( %s /\\ n e. NN )' % A0
vn = w.s([w.s([], 'simpr', '( %s -> n e. NN )' % An), sm2val(w, 'n')], 'syl', '( %s -> ( %s ` n ) = ( n mod 2 ) )' % (An, SM2))
eq = w.s([w.s([w.s([vn], 'oveq1d', '( %s -> %s = %s )' % (An, SETT('n', 'Z'), ETT('n', 'Z')))], 'mpteq2dva', '( %s -> ( n e. NN |-> %s ) = ( n e. NN |-> %s ) )' % (A0, SETT('n', 'Z'), ETT('n', 'Z')))], 'seqeq3d',
         '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) = seq 1 ( + , ( n e. NN |-> %s ) ) )' % (A0, SETT('n', 'Z'), ETT('n', 'Z')))
w.qed([eq, cv], 'eqeltrrd', '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (A0, ETT('n', 'Z')))
run7(w)

# ---------------------------------------------------------------- etabnd
RZ = '( Re ` Z )'
AZ = '( abs ` Z )'
w = W('etabnd', 'The bound on the eta function on ` Re z > 0 `: ` |eta ( z )| <_ |z| ( 1 + 1 / Re z ) ` '
      '( ~ abbnd at ` B = 1 `).  Lean\'s ` norm_etaFun_le ` of Route Z\'s ZeroCount.lean.')
bd = w.s([w.s([a1(w, A0, 'mod2abs', MABS), w.s([], 'id', '( %s -> %s )' % (A0, A0))], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, MABS, A0)), w.inst('abbnd')], 'syl',
         '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( ( 1 x. %s ) x. ( 1 + ( 1 / %s ) ) ) )' % (A0, SETT('k', 'Z'), AZ, RZ))
Ak = '( %s /\\ k e. NN )' % A0
vk = w.s([w.s([], 'simpr', '( %s -> k e. NN )' % Ak), sm2val(w, 'k')], 'syl', '( %s -> ( %s ` k ) = ( k mod 2 ) )' % (Ak, SM2))
eq = w.s([w.s([w.s([vk], 'oveq1d', '( %s -> %s = %s )' % (Ak, SETT('k', 'Z'), ETT('k', 'Z')))], 'sumeq2dv', '( %s -> sum_ k e. NN %s = %s )' % (A0, SETT('k', 'Z'), ETA('Z')))], 'fveq2d',
         '( %s -> ( abs ` sum_ k e. NN %s ) = ( abs ` %s ) )' % (A0, SETT('k', 'Z'), ETA('Z')))
azc = w.s([w.s([w.s([], 'simpl', '( %s -> Z e. CC )' % A0)], 'abscld', '( %s -> %s e. RR )' % (A0, AZ))], 'recnd', '( %s -> %s e. CC )' % (A0, AZ))
one = w.s([w.s([azc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, AZ, AZ))], 'oveq1d', '( %s -> ( ( 1 x. %s ) x. ( 1 + ( 1 / %s ) ) ) = ( %s x. ( 1 + ( 1 / %s ) ) ) )' % (A0, AZ, RZ, AZ, RZ))
w.qed([w.s([eq, bd], 'eqbrtrrd', '( %s -> ( abs ` %s ) <_ ( ( 1 x. %s ) x. ( 1 + ( 1 / %s ) ) ) )' % (A0, ETA('Z'), AZ, RZ)), one], 'breqtrd',
      '( %s -> ( abs ` %s ) <_ ( %s x. ( 1 + ( 1 / %s ) ) ) )' % (A0, ETA('Z'), AZ, RZ))
run7(w)

# ---------------------------------------------------------------- etabnd4
A0 = '( Z e. CC /\\ ( 1 / 4 ) <_ %s )' % RZ
w = W('etabnd4', 'The numeral bound on the eta function for ` ( 1 / 4 ) <_ ( Re ` Z ) `: '
      '` |eta ( Z )| <_ 5 ( 2 + |Z| ) `.  Lean\'s ` norm_etaFun_le_of_one_quarter_le_re ` '
      'of Route Z\'s ZeroCount.lean.')
zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
q4 = w.s([], 'simpr', '( %s -> ( 1 / 4 ) <_ %s )' % (A0, RZ))
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
cl = Closure(w, A0, {})
cl.leaf(RZ, 'RR', rz)
z0 = linarith(w, A0, [q4], '0 < %s' % RZ, closure=cl)
cl.have(RZ, 'gt0', z0)
bd = w.s([w.s([zc, z0], 'jca', '( %s -> %s )' % (A0, ZP0)), w.inst('etabnd')], 'syl', '( %s -> ( abs ` %s ) <_ ( %s x. ( 1 + ( 1 / %s ) ) ) )' % (A0, ETA('Z'), AZ, RZ))
az = w.s([zc], 'abscld', '( %s -> %s e. RR )' % (A0, AZ)); az0 = w.s([zc], 'absge0d', '( %s -> 0 <_ %s )' % (A0, AZ))
cl.leaf(AZ, 'RR', az); cl.have(AZ, 'ge0', az0)
IR = '( 1 / %s )' % RZ
irr = w.s([w.s([w.s([rz, z0], 'elrpd', '( %s -> %s e. RR+ )' % (A0, RZ))], 'rpreccld', '( %s -> %s e. RR+ )' % (A0, IR))], 'rpred', '( %s -> %s e. RR )' % (A0, IR))
cl.leaf(IR, 'RR', irr)
ldm = w.s([a1(w, A0, '1re', '1 e. RR'), a1(w, A0, '4re', '4 e. RR'), w.s([rz, z0], 'jca', '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, RZ, RZ)), w.inst('ledivmul')], 'syl3anc',
          '( %s -> ( %s <_ 4 <-> 1 <_ ( %s x. 4 ) ) )' % (A0, IR, RZ))
ir4 = w.s([linarith(w, A0, [q4], '1 <_ ( %s x. 4 )' % RZ, closure=cl), ldm], 'mpbird', '( %s -> %s <_ 4 )' % (A0, IR))
# the sum is a complex number
Ak = '( %s /\\ k e. NN )' % A0
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
F = '( n e. NN |-> %s )' % ETT('n', 'Z')
fv = mpv(w, Ak, F, 'k', ETT('k', 'Z'), ettsub(w, 'k', 'Z'), kn, vexd(w, Ak, ETT('k', 'Z')))
ec = ettcl(w, Ak, 'k', kn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))
cv = w.s([w.s([zc, z0], 'jca', '( %s -> %s )' % (A0, ZP0)), w.inst('etacvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, F))
nz, oz, on = nnuz(w, A0)
sc = w.s([nz, oz, fv, ec, cv], 'isumcl', '( %s -> %s e. CC )' % (A0, ETA('Z')))
ae = w.s([sc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, ETA('Z')))
cl.leaf('( abs ` %s )' % ETA('Z'), 'RR', ae)
fin = nlinarith(w, A0, [bd, ir4, az0], '( abs ` %s ) <_ ( 5 x. ( 2 + %s ) )' % (ETA('Z'), AZ), closure=cl, name='qed')
run7(w)

# ---------------------------------------------------------------- etahol
A0 = '( T e. RR /\\ 0 <_ T )'
D = HP('T')
LCS = '( z e. %s |-> sum_ k e. NN %s )' % (D, SETT('k', 'z'))
LC = '( z e. %s |-> %s )' % (D, ETA('z'))
w = W('etahol', 'The eta function is holomorphic on every open half-plane ` Re z > T `, ` 0 <_ T ` '
      '( ~ abhol at the coefficients ` ( k mod 2 ) `).  Lean\'s ` differentiableOn_etaFun ` of '
      'Route Z\'s ZeroCount.lean.')
hol = w.s([w.s([a1(w, A0, 'mod2abs', MABS), w.s([], 'id', '( %s -> %s )' % (A0, A0))], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, MABS, A0)), w.inst('abhol')], 'syl', '( %s -> %s )' % (A0, HOLG2(LCS, D)))
Azk = '( ( %s /\\ z e. %s ) /\\ k e. NN )' % (A0, D)
vk = w.s([w.s([], 'simpr', '( %s -> k e. NN )' % Azk), sm2val(w, 'k')], 'syl', '( %s -> ( %s ` k ) = ( k mod 2 ) )' % (Azk, SM2))
sm = w.s([w.s([vk], 'oveq1d', '( %s -> %s = %s )' % (Azk, SETT('k', 'z'), ETT('k', 'z')))], 'sumeq2dv', '( ( %s /\\ z e. %s ) -> sum_ k e. NN %s = %s )' % (A0, D, SETT('k', 'z'), ETA('z')))
eq = w.s([sm], 'mpteq2dva', '( %s -> %s = %s )' % (A0, LCS, LC))
b1 = w.s([eq], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (A0, LCS, D, LC, D))
b2 = w.s([w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, LCS, LC))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (A0, LCS, LC))], 'sseq2d',
         '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (A0, D, LCS, D, LC))
w.qed([hol, w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (A0, HOLG2(LCS, D), HOLG2(LC, D)))], 'mpbid', '( %s -> %s )' % (A0, HOLG2(LC, D)))
run7(w)
