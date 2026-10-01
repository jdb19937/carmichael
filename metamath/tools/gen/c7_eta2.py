"""C7, eta block 2: the alternating coefficients, the even subseries by
isercoll, and eta = ( 1 - 2 ^c ( 1 - z ) ) zeta on Re z > 1 (zsercvgz, altps,
altabs, etaalt, zsereven, zseralt, etazser, gfunne0)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq, nlinarith

RZ = '( Re ` Z )'
NZ = '-u Z'


def ZT(n):
    return '( %s ^c -u Z )' % n


FZ = '( n e. NN |-> %s )' % ZT('n')
P = ZP1


def zctx(w, A0):
    """Z e. CC, 1 < Re Z, Re Z e. RR, -u Z e. CC under A0 = ZP1 (or an extension: pass the steps)"""
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
    z1 = w.s([], 'simpr', '( %s -> 1 < %s )' % (A0, RZ))
    rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0)
    return zc, z1, rz, nzc


def ztsub(w, K, n='n'):
    return w.s([], 'oveq1', '( %s = %s -> %s = %s )' % (n, K, ZT(n), ZT(K)))


def ztcl(w, ante, K, kn, zc):
    nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % ante)
    return w.s([w.s([kn], 'nncnd', '( %s -> %s e. CC )' % (ante, K)), nzc], 'cxpcld', '( %s -> %s e. CC )' % (ante, ZT(K)))


# ---------------------------------------------------------------- zsercvgz
w = W('zsercvgz', 'The zeta series ` sum_ n ^c -u Z ` converges for complex ` Z ` with ` 1 < Re Z ` '
      '( ~ zsercvg at ` Re Z ` and ~ abscvgcvg ).')
zc, z1, rz, nzc = zctx(w, P)
Ak = '( %s /\\ k e. NN )' % P
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
FR = '( n e. NN |-> ( n ^c -u %s ) )' % RZ
fv = mpv(w, Ak, FR, 'k', '( k ^c -u %s )' % RZ, w.s([], 'oveq1', '( n = k -> ( n ^c -u %s ) = ( k ^c -u %s ) )' % (RZ, RZ)), kn, vexd(w, Ak, '( k ^c -u %s )' % RZ))
gv = mpv(w, Ak, FZ, 'k', ZT('k'), ztsub(w, 'k'), kn, vexd(w, Ak, ZT('k')))
ab = w.s([kn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak), w.inst('cxpnnabs')], 'syl2anc', '( %s -> ( abs ` %s ) = ( k ^c -u %s ) )' % (Ak, ZT('k'), RZ))
h3 = w.s([fv, w.s([w.s([gv], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, FZ, ZT('k'))), ab], 'eqtrd', '( %s -> ( abs ` ( %s ` k ) ) = ( k ^c -u %s ) )' % (Ak, FZ, RZ))], 'eqtr4d',
         '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, FR, FZ))
h4 = w.s([gv, ztcl(w, Ak, 'k', kn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, FZ))
cv = w.s([w.s([rz, z1], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (P, RZ, RZ)), w.inst('zsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (P, FR))
nz, oz, on = nnuz(w, P)
w.qed([nz, oz, h3, h4, cv], 'abscvgcvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (P, FZ))
run7(w)

# ---------------------------------------------------------------- altps
A0 = 'K e. NN'
w = W('altps', 'The partial sums of the alternating coefficients ` 2 ( i mod 2 ) - 1 ` (that is '
      '` ( -u 1 ) ^ ( i + 1 ) `) are ` K mod 2 `: the telescoping sum ~ telfsum2 with ~ mod2p1 .')
kn = w.s([], 'id', '( %s -> K e. NN )' % A0)
kz = w.s([kn], 'nnzd', '( %s -> K e. ZZ )' % A0)
s1 = w.s([w.s([], 'oveq1', '( k = i -> ( k mod 2 ) = ( i mod 2 ) )')], 'negeqd', '( k = i -> -u ( k mod 2 ) = -u ( i mod 2 ) )')
s2 = w.s([w.s([], 'oveq1', '( k = ( i + 1 ) -> ( k mod 2 ) = ( ( i + 1 ) mod 2 ) )')], 'negeqd', '( k = ( i + 1 ) -> -u ( k mod 2 ) = -u ( ( i + 1 ) mod 2 ) )')
s3 = w.s([w.s([], 'oveq1', '( k = 1 -> ( k mod 2 ) = ( 1 mod 2 ) )')], 'negeqd', '( k = 1 -> -u ( k mod 2 ) = -u ( 1 mod 2 ) )')
s4 = w.s([w.s([], 'oveq1', '( k = ( K + 1 ) -> ( k mod 2 ) = ( ( K + 1 ) mod 2 ) )')], 'negeqd', '( k = ( K + 1 ) -> -u ( k mod 2 ) = -u ( ( K + 1 ) mod 2 ) )')
k1u = w.s([w.s([kn], 'peano2nnd', '( %s -> ( K + 1 ) e. NN )' % A0), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> ( K + 1 ) e. ( ZZ>= ` 1 ) )' % A0)
Akf = '( %s /\\ k e. ( 1 ... ( K + 1 ) ) )' % A0
kfz = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... ( K + 1 ) ) )' % Akf), w.inst('elfzelz')], 'syl', '( %s -> k e. ZZ )' % Akf)
mk = mod2facts(w, Akf, kfz)
h7 = w.s([mk['cn']], 'negcld', '( %s -> -u ( k mod 2 ) e. CC )' % Akf)
tel = w.s([s1, s2, s3, s4, kz, k1u, h7], 'telfsum2', '( %s -> sum_ i e. ( 1 ... K ) ( -u ( ( i + 1 ) mod 2 ) - -u ( i mod 2 ) ) = ( -u ( ( K + 1 ) mod 2 ) - -u ( 1 mod 2 ) ) )' % A0)
# the summand
Ai = '( %s /\\ i e. ( 1 ... K ) )' % A0
iz = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... K ) )' % Ai), w.inst('elfzelz')], 'syl', '( %s -> i e. ZZ )' % Ai)
mi = mod2facts(w, Ai, iz)
cli = Closure(w, Ai, {}); cli.leaf('( i mod 2 )', 'RR', mi['re'])
p1 = w.s([iz, w.inst('mod2p1')], 'syl', '( %s -> ( ( i + 1 ) mod 2 ) = ( 1 - ( i mod 2 ) ) )' % Ai)
t1 = w.s([w.s([w.s([p1], 'negeqd', '( %s -> -u ( ( i + 1 ) mod 2 ) = -u ( 1 - ( i mod 2 ) ) )' % Ai)], 'oveq1d', '( %s -> ( -u ( ( i + 1 ) mod 2 ) - -u ( i mod 2 ) ) = ( -u ( 1 - ( i mod 2 ) ) - -u ( i mod 2 ) ) )' % Ai),
          lineq(w, Ai, '( -u ( 1 - ( i mod 2 ) ) - -u ( i mod 2 ) )', ALTT('i'), closure=cli)], 'eqtrd', '( %s -> ( -u ( ( i + 1 ) mod 2 ) - -u ( i mod 2 ) ) = %s )' % (Ai, ALTT('i')))
lhs = w.s([t1], 'sumeq2dv', '( %s -> sum_ i e. ( 1 ... K ) ( -u ( ( i + 1 ) mod 2 ) - -u ( i mod 2 ) ) = sum_ i e. ( 1 ... K ) %s )' % (A0, ALTT('i')))
# the value of ALT
Ain = '( %s /\\ i e. ( 1 ... K ) )' % A0
inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... K ) )' % Ain), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ain)
av = mpv(w, Ain, ALT, 'i', ALTT('i'), w.s([w.s([w.s([], 'oveq1', '( q = i -> ( q mod 2 ) = ( i mod 2 ) )')], 'oveq2d', '( q = i -> ( 2 x. ( q mod 2 ) ) = ( 2 x. ( i mod 2 ) ) )')], 'oveq1d', '( q = i -> %s = %s )' % (ALTT('q'), ALTT('i'))),
         inn, vexd(w, Ain, ALTT('i')))
lhs2 = w.s([av], 'sumeq2dv', '( %s -> sum_ i e. ( 1 ... K ) ( %s ` i ) = sum_ i e. ( 1 ... K ) %s )' % (A0, ALT, ALTT('i')))
# the right side
mK = mod2facts(w, A0, kz)
clk = Closure(w, A0, {}); clk.leaf('( K mod 2 )', 'RR', mK['re'])
pK = w.s([kz, w.inst('mod2p1')], 'syl', '( %s -> ( ( K + 1 ) mod 2 ) = ( 1 - ( K mod 2 ) ) )' % A0)
m1 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2'), w.inst('1mod')], 'mp2an', '( 1 mod 2 ) = 1')], 'a1i', '( %s -> ( 1 mod 2 ) = 1 )' % A0)
rhs = w.s([w.s([w.s([pK], 'negeqd', '( %s -> -u ( ( K + 1 ) mod 2 ) = -u ( 1 - ( K mod 2 ) ) )' % A0), w.s([m1], 'negeqd', '( %s -> -u ( 1 mod 2 ) = -u 1 )' % A0)], 'oveq12d',
               '( %s -> ( -u ( ( K + 1 ) mod 2 ) - -u ( 1 mod 2 ) ) = ( -u ( 1 - ( K mod 2 ) ) - -u 1 ) )' % A0),
          lineq(w, A0, '( -u ( 1 - ( K mod 2 ) ) - -u 1 )', '( K mod 2 )', closure=clk)], 'eqtrd', '( %s -> ( -u ( ( K + 1 ) mod 2 ) - -u ( 1 mod 2 ) ) = ( K mod 2 ) )' % A0)
w.qed([lhs2, w.s([w.s([lhs], 'eqcomd', '( %s -> sum_ i e. ( 1 ... K ) %s = sum_ i e. ( 1 ... K ) ( -u ( ( i + 1 ) mod 2 ) - -u ( i mod 2 ) ) )' % (A0, ALTT('i'))), w.s([tel, rhs], 'eqtrd',
               '( %s -> sum_ i e. ( 1 ... K ) ( -u ( ( i + 1 ) mod 2 ) - -u ( i mod 2 ) ) = ( K mod 2 ) )' % A0)], 'eqtrd', '( %s -> sum_ i e. ( 1 ... K ) %s = ( K mod 2 ) )' % (A0, ALTT('i')))], 'eqtrd',
      '( %s -> sum_ i e. ( 1 ... K ) ( %s ` i ) = ( K mod 2 ) )' % (A0, ALT))
run7(w)

ALTABS = '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (ALT, ALT)
ALTPS = 'A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ 1' % ALT


def altsub(w, K):
    return w.s([w.s([w.s([], 'oveq1', '( q = %s -> ( q mod 2 ) = ( %s mod 2 ) )' % (K, K))], 'oveq2d', '( q = %s -> ( 2 x. ( q mod 2 ) ) = ( 2 x. ( %s mod 2 ) ) )' % (K, K))], 'oveq1d',
               '( q = %s -> %s = %s )' % (K, ALTT('q'), ALTT(K)))


# ---------------------------------------------------------------- altabs
w = W('altabs', 'The alternating coefficients ` 2 ( q mod 2 ) - 1 ` are a complex sequence bounded '
      'by ` 1 ` with partial sums bounded by ` 1 ` ( ~ altps ): the hypotheses of ~ abagr .')
Aq = 'q e. NN'
mq = mod2facts(w, Aq, w.s([w.s([], 'id', '( %s -> q e. NN )' % Aq)], 'nnzd', '( %s -> q e. ZZ )' % Aq))
qc = w.s([w.s([a1(w, Aq, '2cn', '2 e. CC'), mq['cn']], 'mulcld', '( %s -> ( 2 x. ( q mod 2 ) ) e. CC )' % Aq), a1(w, Aq, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> %s e. CC )' % (Aq, ALTT('q')))
fn = w.s([w.s([], 'eqid', '%s = %s' % (ALT, ALT)), qc], 'fmpti', '%s : NN --> CC' % ALT)
Am = 'm e. NN'
mn = w.s([], 'id', '( %s -> m e. NN )' % Am)
mm = mod2facts(w, Am, w.s([mn], 'nnzd', '( %s -> m e. ZZ )' % Am))
clm = Closure(w, Am, {}); clm.leaf('( m mod 2 )', 'RR', mm['re'])
av = mpv(w, Am, ALT, 'm', ALTT('m'), altsub(w, 'm'), mn, vexd(w, Am, ALTT('m')))
ar = clm.mem(ALTT('m'), 'RR')
lo = linarith(w, Am, [mm['ge0']], '-u 1 <_ %s' % ALTT('m'), closure=clm)
hi = linarith(w, Am, [mm['le1']], '%s <_ 1' % ALTT('m'), closure=clm)
ab1 = w.s([w.s([lo, hi], 'jca', '( %s -> ( -u 1 <_ %s /\\ %s <_ 1 ) )' % (Am, ALTT('m'), ALTT('m'))), w.s([ar, a1(w, Am, '1re', '1 e. RR')], 'absled', '( %s -> ( ( abs ` %s ) <_ 1 <-> ( -u 1 <_ %s /\\ %s <_ 1 ) ) )' % (Am, ALTT('m'), ALTT('m'), ALTT('m')))], 'mpbird',
          '( %s -> ( abs ` %s ) <_ 1 )' % (Am, ALTT('m')))
ab = w.s([w.s([av], 'fveq2d', '( %s -> ( abs ` ( %s ` m ) ) = ( abs ` %s ) )' % (Am, ALT, ALTT('m'))), ab1], 'eqbrtrd', '( %s -> ( abs ` ( %s ` m ) ) <_ 1 )' % (Am, ALT))
part1 = w.s([fn, w.s([], '1re', '1 e. RR'), w.s([ab], 'rgen', 'A. m e. NN ( abs ` ( %s ` m ) ) <_ 1' % ALT)], '3pm3.2i', ALTABS)
ps = w.s([mn, w.inst('altps')], 'syl', '( %s -> sum_ i e. ( 1 ... m ) ( %s ` i ) = ( m mod 2 ) )' % (Am, ALT))
ps2 = w.s([w.s([w.s([ps], 'fveq2d', '( %s -> ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) = ( abs ` ( m mod 2 ) ) )' % (Am, ALT)), w.s([mm['re'], mm['ge0']], 'absidd', '( %s -> ( abs ` ( m mod 2 ) ) = ( m mod 2 ) )' % Am)], 'eqtrd',
               '( %s -> ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) = ( m mod 2 ) )' % (Am, ALT)), mm['le1']], 'eqbrtrd', '( %s -> ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ 1 )' % (Am, ALT))
w.qed([part1, w.s([ps2], 'rgen', ALTPS)], 'pm3.2i', '( %s /\\ %s )' % (ALTABS, ALTPS))
run7(w)

# ---------------------------------------------------------------- etaalt
w = W('etaalt', 'The eta series regrouped: ` eta ( Z ) = sum_ ( 2 ( k mod 2 ) - 1 ) k ^c -u Z ` on '
      '` Re Z > 1 ` (Abel summation in reverse, ~ abagr at the alternating coefficients).')
zc, z1, rz, nzc = zctx(w, P)
aa = a1(w, P, 'altabs', '( %s /\\ %s )' % (ALTABS, ALTPS))
h1 = w.s([w.s([w.s([aa, w.inst('simpl')], 'syl', '( %s -> %s )' % (P, ALTABS)), w.s([], 'id', '( %s -> %s )' % (P, P))], 'jca', '( %s -> ( %s /\\ %s ) )' % (P, ALTABS, P)),
          w.s([a1(w, P, '1re', '1 e. RR'), w.s([aa, w.inst('simpr')], 'syl', '( %s -> %s )' % (P, ALTPS))], 'jca', '( %s -> ( 1 e. RR /\\ %s ) )' % (P, ALTPS))], 'jca',
         '( %s -> ( ( %s /\\ %s ) /\\ ( 1 e. RR /\\ %s ) ) )' % (P, ALTABS, P, ALTPS))
gr = w.s([h1, w.inst('abagr')], 'syl', '( %s -> sum_ k e. NN ( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s ) = sum_ k e. NN ( ( %s ` k ) x. %s ) )' % (P, ALT, DIF('k', 'Z'), ALT, ZT('k')))
Ak = '( %s /\\ k e. NN )' % P
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
ps = w.s([kn, w.inst('altps')], 'syl', '( %s -> sum_ i e. ( 1 ... k ) ( %s ` i ) = ( k mod 2 ) )' % (Ak, ALT))
lhs = w.s([w.s([w.s([ps], 'oveq1d', '( %s -> ( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s ) = %s )' % (Ak, ALT, DIF('k', 'Z'), ETT('k', 'Z')))], 'sumeq2dv',
               '( %s -> sum_ k e. NN ( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s ) = %s )' % (P, ALT, DIF('k', 'Z'), ETA('Z')))], 'eqcomd',
          '( %s -> %s = sum_ k e. NN ( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s ) )' % (P, ETA('Z'), ALT, DIF('k', 'Z')))
av = mpv(w, Ak, ALT, 'k', ALTT('k'), altsub(w, 'k'), kn, vexd(w, Ak, ALTT('k')))
rhs = w.s([w.s([av], 'oveq1d', '( %s -> ( ( %s ` k ) x. %s ) = ( %s x. %s ) )' % (Ak, ALT, ZT('k'), ALTT('k'), ZT('k')))], 'sumeq2dv',
          '( %s -> sum_ k e. NN ( ( %s ` k ) x. %s ) = sum_ k e. NN ( %s x. %s ) )' % (P, ALT, ZT('k'), ALTT('k'), ZT('k')))
w.qed([lhs, w.s([gr, rhs], 'eqtrd', '( %s -> sum_ k e. NN ( sum_ i e. ( 1 ... k ) ( %s ` i ) x. %s ) = sum_ k e. NN ( %s x. %s ) )' % (P, ALT, DIF('k', 'Z'), ALTT('k'), ZT('k')))], 'eqtrd',
      '( %s -> %s = sum_ k e. NN ( %s x. %s ) )' % (P, ETA('Z'), ALTT('k'), ZT('k')))
run7(w)

# ---------------------------------------------------------------- zsereven
EVK = lambda k: '( %s x. %s )' % (EVT(k), ZT(k))
FE = '( o e. NN |-> %s )' % EVK('o')
G2 = '( b e. NN |-> ( 2 x. b ) )'
H2 = '( c e. NN |-> ( ( 2 x. c ) ^c -u Z ) )'
P2 = '( 2 ^c -u Z )'
LIMR = '( %s x. %s )' % (P2, ZS('Z', 'r'))
LIM = '( %s x. %s )' % (P2, ZS('Z'))
EVS = 'sum_ k e. NN %s' % EVK('k')


def evsub(w, K, v='o'):
    a = w.s([w.s([], 'oveq1', '( %s = %s -> ( %s mod 2 ) = ( %s mod 2 ) )' % (v, K, v, K))], 'oveq2d', '( %s = %s -> %s = %s )' % (v, K, EVT(v), EVT(K)))
    return w.s([a, ztsub(w, K, v)], 'oveq12d', '( %s = %s -> %s = %s )' % (v, K, EVK(v), EVK(K)))


def gsub(w, K):
    return w.s([], 'oveq2', '( b = %s -> ( 2 x. b ) = ( 2 x. %s ) )' % (K, K))


w = W('zsereven', 'The even subseries of the zeta series converges and equals ` 2 ^c -u Z x. zeta ( Z ) ` '
      'on ` Re Z > 1 `: ` sum_ ( 1 - ( k mod 2 ) ) k ^c -u Z ` collected along ` k |-> 2 k ` '
      '( ~ isercoll , ~ mulcxp ).')
zc, z1, rz, nzc = zctx(w, P)
nz, oz, on = nnuz(w, P)
Ak = '( %s /\\ k e. NN )' % P
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
zck = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)
Ab = '( %s /\\ b e. NN )' % P
b2n = w.s([a1(w, Ab, '2nn', '2 e. NN'), w.s([], 'simpr', '( %s -> b e. NN )' % Ab)], 'nnmulcld', '( %s -> ( 2 x. b ) e. NN )' % Ab)
gfn = w.s([b2n, w.s([], 'eqid', '%s = %s' % (G2, G2))], 'fmptd', '( %s -> %s : NN --> NN )' % (P, G2))
gv = mpv(w, Ak, G2, 'k', '( 2 x. k )', gsub(w, 'k'), kn, vexd(w, Ak, '( 2 x. k )'))
k1n = w.s([kn], 'peano2nnd', '( %s -> ( k + 1 ) e. NN )' % Ak)
gv1 = mpv(w, Ak, G2, '( k + 1 )', '( 2 x. ( k + 1 ) )', gsub(w, '( k + 1 )'), k1n, vexd(w, Ak, '( 2 x. ( k + 1 ) )'))
clk = Closure(w, Ak, {'k': ('NN', kn)})
lt = linarith(w, Ak, [], '( 2 x. k ) < ( 2 x. ( k + 1 ) )', closure=clk)
inc = w.s([lt, w.s([gv, gv1], 'breq12d', '( %s -> ( ( %s ` k ) < ( %s ` ( k + 1 ) ) <-> ( 2 x. k ) < ( 2 x. ( k + 1 ) ) ) )' % (Ak, G2, G2))], 'mpbird', '( %s -> ( %s ` k ) < ( %s ` ( k + 1 ) ) )' % (Ak, G2, G2))
# F vanishes off the range of G
An = '( %s /\\ n e. ( NN \\ ran %s ) )' % (P, G2)
nn_ = w.s([w.s([], 'simpr', '( %s -> n e. ( NN \\ ran %s ) )' % (An, G2)), w.inst('eldifi')], 'syl', '( %s -> n e. NN )' % An)
nnr = w.s([w.s([], 'simpr', '( %s -> n e. ( NN \\ ran %s ) )' % (An, G2)), w.inst('eldifn')], 'syl', '( %s -> -. n e. ran %s )' % (An, G2))
An2 = '( %s /\\ 2 || n )' % An
nn2 = w.s([nn_], 'adantr', '( %s -> n e. NN )' % An2)
nz2 = w.s([nn2], 'nnzd', '( %s -> n e. ZZ )' % An2)
dv = w.s([], 'simpr', '( %s -> 2 || n )' % An2)
hz = w.s([dv, w.s([a1(w, An2, '2z', '2 e. ZZ'), a1(w, An2, '2ne0', '2 =/= 0'), nz2, w.inst('dvdsval2')], 'syl3anc', '( %s -> ( 2 || n <-> ( n / 2 ) e. ZZ ) )' % An2)], 'mpbid', '( %s -> ( n / 2 ) e. ZZ )' % An2)
nr2 = w.s([nn2], 'nnred', '( %s -> n e. RR )' % An2)
hgt = w.s([nr2, a1(w, An2, '2re', '2 e. RR'), w.s([nn2], 'nngt0d', '( %s -> 0 < n )' % An2), a1(w, An2, '2pos', '0 < 2')], 'divgt0d', '( %s -> 0 < ( n / 2 ) )' % An2)
hn = w.s([w.s([hz, hgt], 'jca', '( %s -> ( ( n / 2 ) e. ZZ /\\ 0 < ( n / 2 ) ) )' % An2), w.s([], 'elnnz', '( ( n / 2 ) e. NN <-> ( ( n / 2 ) e. ZZ /\\ 0 < ( n / 2 ) ) )')], 'sylibr', '( %s -> ( n / 2 ) e. NN )' % An2)
ghv = mpv(w, An2, G2, '( n / 2 )', '( 2 x. ( n / 2 ) )', gsub(w, '( n / 2 )'), hn, vexd(w, An2, '( 2 x. ( n / 2 ) )'))
ghv2 = w.s([ghv, w.s([w.s([nr2], 'recnd', '( %s -> n e. CC )' % An2), a1(w, An2, '2cn', '2 e. CC'), a1(w, An2, '2ne0', '2 =/= 0')], 'divcan2d', '( %s -> ( 2 x. ( n / 2 ) ) = n )' % An2)], 'eqtrd',
           '( %s -> ( %s ` ( n / 2 ) ) = n )' % (An2, G2))
gfn2 = w.s([w.s([gfn], 'ad2antrr', '( %s -> %s : NN --> NN )' % (An2, G2))], 'ffnd', '( %s -> %s Fn NN )' % (An2, G2))
inrn = w.s([gfn2, hn, w.inst('fnfvelrn')], 'syl2anc', '( %s -> ( %s ` ( n / 2 ) ) e. ran %s )' % (An2, G2, G2))
inrn2 = w.s([ghv2, inrn], 'eqeltrrd', '( %s -> n e. ran %s )' % (An2, G2))
nodd = w.s([inrn2, w.s([nnr], 'adantr', '( %s -> -. n e. ran %s )' % (An2, G2))], 'pm2.65da', '( %s -> -. 2 || n )' % An)
nnz = w.s([nn_], 'nnzd', '( %s -> n e. ZZ )' % An)
m1 = w.s([nodd, w.s([nnz, w.inst('mod2eq1n2dvds')], 'syl', '( %s -> ( ( n mod 2 ) = 1 <-> -. 2 || n ) )' % An)], 'mpbird', '( %s -> ( n mod 2 ) = 1 )' % An)
ev0 = w.s([w.s([m1], 'oveq2d', '( %s -> %s = ( 1 - 1 ) )' % (An, EVT('n'))), a1(w, An, '1m1e0', '( 1 - 1 ) = 0')], 'eqtrd', '( %s -> %s = 0 )' % (An, EVT('n')))
fvn = mpv(w, An, FE, 'n', EVK('n'), evsub(w, 'n'), nn_, vexd(w, An, EVK('n')))
h0 = w.s([fvn, w.s([w.s([ev0], 'oveq1d', '( %s -> %s = ( 0 x. %s ) )' % (An, EVK('n'), ZT('n'))), w.s([ztcl(w, An, 'n', nn_, w.s([zc], 'adantr', '( %s -> Z e. CC )' % An))], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (An, ZT('n')))], 'eqtrd',
                     '( %s -> %s = 0 )' % (An, EVK('n')))], 'eqtrd', '( %s -> ( %s ` n ) = 0 )' % (An, FE))
# F is complex-valued
Ann = '( %s /\\ n e. NN )' % P
nnn = w.s([], 'simpr', '( %s -> n e. NN )' % Ann)
mn = mod2facts(w, Ann, w.s([nnn], 'nnzd', '( %s -> n e. ZZ )' % Ann))
evc = w.s([a1(w, Ann, 'ax-1cn', '1 e. CC'), mn['cn']], 'subcld', '( %s -> %s e. CC )' % (Ann, EVT('n')))
fvnn = mpv(w, Ann, FE, 'n', EVK('n'), evsub(w, 'n'), nnn, vexd(w, Ann, EVK('n')))
fcl = w.s([fvnn, w.s([evc, ztcl(w, Ann, 'n', nnn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ann))], 'mulcld', '( %s -> %s e. CC )' % (Ann, EVK('n')))], 'eqeltrd', '( %s -> ( %s ` n ) e. CC )' % (Ann, FE))
# H ` k = F ` ( G ` k )
Z2K = '( ( 2 x. k ) ^c -u Z )'
hv = mpv(w, Ak, H2, 'k', Z2K, w.s([w.s([], 'oveq2', '( c = k -> ( 2 x. c ) = ( 2 x. k ) )')], 'oveq1d', '( c = k -> ( ( 2 x. c ) ^c -u Z ) = %s )' % Z2K), kn, vexd(w, Ak, Z2K))
k2n = w.s([a1(w, Ak, '2nn', '2 e. NN'), kn], 'nnmulcld', '( %s -> ( 2 x. k ) e. NN )' % Ak)
fgv = mpv(w, Ak, FE, '( 2 x. k )', EVK('( 2 x. k )'), evsub(w, '( 2 x. k )'), k2n, vexd(w, Ak, EVK('( 2 x. k )')))
kc = w.s([kn], 'nncnd', '( %s -> k e. CC )' % Ak)
m0 = w.s([w.s([w.s([a1(w, Ak, '2cn', '2 e. CC'), kc], 'mulcomd', '( %s -> ( 2 x. k ) = ( k x. 2 ) )' % Ak)], 'oveq1d', '( %s -> ( ( 2 x. k ) mod 2 ) = ( ( k x. 2 ) mod 2 ) )' % Ak),
          w.s([w.s([kn], 'nnzd', '( %s -> k e. ZZ )' % Ak), a1(w, Ak, '2rp', '2 e. RR+'), w.inst('mulmod0')], 'syl2anc', '( %s -> ( ( k x. 2 ) mod 2 ) = 0 )' % Ak)], 'eqtrd', '( %s -> ( ( 2 x. k ) mod 2 ) = 0 )' % Ak)
ev1 = w.s([w.s([m0], 'oveq2d', '( %s -> %s = ( 1 - 0 ) )' % (Ak, EVT('( 2 x. k )'))), a1(w, Ak, '1m0e1', '( 1 - 0 ) = 1')], 'eqtrd', '( %s -> %s = 1 )' % (Ak, EVT('( 2 x. k )')))
z2kc = ztcl(w, Ak, '( 2 x. k )', k2n, zck)
fg2 = w.s([fgv, w.s([w.s([ev1], 'oveq1d', '( %s -> %s = ( 1 x. %s ) )' % (Ak, EVK('( 2 x. k )'), Z2K)), w.s([z2kc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (Ak, Z2K, Z2K))], 'eqtrd',
                     '( %s -> %s = %s )' % (Ak, EVK('( 2 x. k )'), Z2K))], 'eqtrd', '( %s -> ( %s ` ( 2 x. k ) ) = %s )' % (Ak, FE, Z2K))
hh = w.s([hv, w.s([w.s([gv], 'fveq2d', '( %s -> ( %s ` ( %s ` k ) ) = ( %s ` ( 2 x. k ) ) )' % (Ak, FE, G2, FE)), fg2], 'eqtrd', '( %s -> ( %s ` ( %s ` k ) ) = %s )' % (Ak, FE, G2, Z2K))], 'eqtr4d',
         '( %s -> ( %s ` k ) = ( %s ` ( %s ` k ) ) )' % (Ak, H2, FE, G2))
coll = w.s([nz, oz, gfn, inc, h0, fcl, hh], 'isercoll', '( %s -> ( seq 1 ( + , %s ) ~~> %s <-> seq 1 ( + , %s ) ~~> %s ) )' % (P, H2, LIMR, FE, LIMR))
# seq H ~~> 2 ^c -u Z x. zeta
fzv = mpv(w, Ak, FZ, 'k', ZT('k'), ztsub(w, 'k'), kn, vexd(w, Ak, ZT('k')))
ztk = ztcl(w, Ak, 'k', kn, zck)
cvz = w.s([w.s([], 'id', '( %s -> %s )' % (P, P)), w.inst('zsercvgz')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (P, FZ))
zlim = w.s([nz, oz, fzv, ztk, cvz], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (P, FZ, ZS('Z')))
cbv = w.s([w.s([ztsub(w, 'r', 'k')], 'cbvsumv', '%s = %s' % (ZS('Z'), ZS('Z', 'r')))], 'a1i', '( %s -> %s = %s )' % (P, ZS('Z'), ZS('Z', 'r')))
zlimr = w.s([zlim, cbv], 'breqtrd', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (P, FZ, ZS('Z', 'r')))
p2c = w.s([a1(w, P, '2cn', '2 e. CC'), nzc], 'cxpcld', '( %s -> %s e. CC )' % (P, P2))
mc = w.s([w.s([a1(w, Ak, '2re', '2 e. RR'), a1(w, Ak, '0le2', '0 <_ 2')], 'jca', '( %s -> ( 2 e. RR /\\ 0 <_ 2 ) )' % Ak),
          w.s([w.s([kn], 'nnred', '( %s -> k e. RR )' % Ak), w.s([w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)], 'rpge0d', '( %s -> 0 <_ k )' % Ak)], 'jca', '( %s -> ( k e. RR /\\ 0 <_ k ) )' % Ak),
          w.s([nzc], 'adantr', '( %s -> -u Z e. CC )' % Ak), w.inst('mulcxp')], 'syl3anc', '( %s -> %s = ( %s x. %s ) )' % (Ak, Z2K, P2, ZT('k')))
hval = w.s([hv, w.s([mc, w.s([fzv], 'oveq2d', '( %s -> ( %s x. ( %s ` k ) ) = ( %s x. %s ) )' % (Ak, P2, FZ, P2, ZT('k')))], 'eqtr4d', '( %s -> %s = ( %s x. ( %s ` k ) ) )' % (Ak, Z2K, P2, FZ))], 'eqtrd',
           '( %s -> ( %s ` k ) = ( %s x. ( %s ` k ) ) )' % (Ak, H2, P2, FZ))
fzk = w.s([fzv, ztk], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, FZ))
hlim = w.s([nz, oz, p2c, zlimr, fzk, hval], 'isermulc2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (P, H2, LIMR))
flim = w.s([hlim, coll], 'mpbid', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (P, FE, LIMR))
# the sum and the convergence
fek = mpv(w, Ak, FE, 'k', EVK('k'), evsub(w, 'k'), kn, vexd(w, Ak, EVK('k')))
mk = mod2facts(w, Ak, w.s([kn], 'nnzd', '( %s -> k e. ZZ )' % Ak))
evkc = w.s([w.s([a1(w, Ak, 'ax-1cn', '1 e. CC'), mk['cn']], 'subcld', '( %s -> %s e. CC )' % (Ak, EVT('k'))), ztk], 'mulcld', '( %s -> %s e. CC )' % (Ak, EVK('k')))
sumv = w.s([nz, oz, fek, evkc, flim], 'isumclim', '( %s -> %s = %s )' % (P, EVS, LIMR))
sumv2 = w.s([sumv, w.s([cbv], 'oveq2d', '( %s -> %s = %s )' % (P, LIM, LIMR))], 'eqtr4d', '( %s -> %s = %s )' % (P, EVS, LIM))
zsc = w.s([nz, oz, fzv, ztk, cvz], 'isumcl', '( %s -> %s e. CC )' % (P, ZS('Z')))
limrc = w.s([p2c, w.s([zsc, cbv], 'eqeltrrd', '( %s -> %s e. CC )' % (P, ZS('Z', 'r')))], 'mulcld', '( %s -> %s e. CC )' % (P, LIMR))
dom = w.s([a1(w, P, 'seqex', 'seq 1 ( + , %s ) e. _V' % FE), limrc, flim, w.inst('breldmg')], 'syl3anc', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (P, FE))
w.qed([dom, sumv2], 'jca', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ %s = %s ) )' % (P, FE, EVS, LIM))
run7(w)

# ---------------------------------------------------------------- zseralt
ALS = 'sum_ k e. NN ( %s x. %s )' % (ALTT('k'), ZT('k'))
FM = '( o e. NN |-> ( -u 2 x. %s ) )' % EVK('o')
w = W('zseralt', 'The alternating zeta series: ` sum_ ( 2 ( k mod 2 ) - 1 ) k ^c -u Z = ( 1 - 2 ^c ( 1 - Z ) ) '
      'x. zeta ( Z ) ` on ` Re Z > 1 ` ( ~ isumadd , ~ zsereven ).')
zc, z1, rz, nzc = zctx(w, P)
nz, oz, on = nnuz(w, P)
Ak = '( %s /\\ k e. NN )' % P
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
zck = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)
ztk = ztcl(w, Ak, 'k', kn, zck)
mk = mod2facts(w, Ak, w.s([kn], 'nnzd', '( %s -> k e. ZZ )' % Ak))
clk = Closure(w, Ak, {}); clk.leaf('( k mod 2 )', 'RR', mk['re'])
evc = w.s([a1(w, Ak, 'ax-1cn', '1 e. CC'), mk['cn']], 'subcld', '( %s -> %s e. CC )' % (Ak, EVT('k')))
evkc = w.s([evc, ztk], 'mulcld', '( %s -> %s e. CC )' % (Ak, EVK('k')))
n2c = w.s([a1(w, Ak, '2cn', '2 e. CC')], 'negcld', '( %s -> -u 2 e. CC )' % Ak)
# the termwise identity
t1 = w.s([w.s([n2c, evc, ztk], 'mulassd', '( %s -> ( ( -u 2 x. %s ) x. %s ) = ( -u 2 x. %s ) )' % (Ak, EVT('k'), ZT('k'), EVK('k')))], 'eqcomd',
         '( %s -> ( -u 2 x. %s ) = ( ( -u 2 x. %s ) x. %s ) )' % (Ak, EVK('k'), EVT('k'), ZT('k')))
bc = w.s([n2c, evc], 'mulcld', '( %s -> ( -u 2 x. %s ) e. CC )' % (Ak, EVT('k')))
t2 = w.s([w.s([a1(w, Ak, 'ax-1cn', '1 e. CC'), bc, ztk], 'adddird', '( %s -> ( ( 1 + ( -u 2 x. %s ) ) x. %s ) = ( ( 1 x. %s ) + ( ( -u 2 x. %s ) x. %s ) ) )' % (Ak, EVT('k'), ZT('k'), ZT('k'), EVT('k'), ZT('k'))),
          w.s([w.s([ztk], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (Ak, ZT('k'), ZT('k')))], 'oveq1d', '( %s -> ( ( 1 x. %s ) + ( ( -u 2 x. %s ) x. %s ) ) = ( %s + ( ( -u 2 x. %s ) x. %s ) ) )' % (Ak, ZT('k'), EVT('k'), ZT('k'), ZT('k'), EVT('k'), ZT('k')))],
         'eqtrd', '( %s -> ( ( 1 + ( -u 2 x. %s ) ) x. %s ) = ( %s + ( ( -u 2 x. %s ) x. %s ) ) )' % (Ak, EVT('k'), ZT('k'), ZT('k'), EVT('k'), ZT('k')))
t3 = w.s([lineq(w, Ak, '( 1 + ( -u 2 x. %s ) )' % EVT('k'), ALTT('k'), closure=clk)], 'oveq1d', '( %s -> ( ( 1 + ( -u 2 x. %s ) ) x. %s ) = ( %s x. %s ) )' % (Ak, EVT('k'), ZT('k'), ALTT('k'), ZT('k')))
TK = '( %s x. %s )' % (ALTT('k'), ZT('k'))
SK = '( %s + ( -u 2 x. %s ) )' % (ZT('k'), EVK('k'))
tk = w.s([w.s([w.s([t1], 'oveq2d', '( %s -> %s = ( %s + ( ( -u 2 x. %s ) x. %s ) ) )' % (Ak, SK, ZT('k'), EVT('k'), ZT('k'))), w.s([t2], 'eqcomd', '( %s -> ( %s + ( ( -u 2 x. %s ) x. %s ) ) = ( ( 1 + ( -u 2 x. %s ) ) x. %s ) )' % (Ak, ZT('k'), EVT('k'), ZT('k'), EVT('k'), ZT('k')))],
              'eqtrd', '( %s -> %s = ( ( 1 + ( -u 2 x. %s ) ) x. %s ) )' % (Ak, SK, EVT('k'), ZT('k'))), t3], 'eqtrd', '( %s -> %s = %s )' % (Ak, SK, TK))
sums = w.s([w.s([tk], 'eqcomd', '( %s -> %s = %s )' % (Ak, TK, SK))], 'sumeq2dv', '( %s -> %s = sum_ k e. NN %s )' % (P, ALS, SK))
# the two series
fzv = mpv(w, Ak, FZ, 'k', ZT('k'), ztsub(w, 'k'), kn, vexd(w, Ak, ZT('k')))
cvz = w.s([w.s([], 'id', '( %s -> %s )' % (P, P)), w.inst('zsercvgz')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (P, FZ))
ev = w.s([w.s([], 'id', '( %s -> %s )' % (P, P)), w.inst('zsereven')], 'syl', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ %s = %s ) )' % (P, FE, EVS, LIM))
evdom = w.s([ev, w.inst('simpl')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (P, FE))
evsum = w.s([ev, w.inst('simpr')], 'syl', '( %s -> %s = %s )' % (P, EVS, LIM))
fek = mpv(w, Ak, FE, 'k', EVK('k'), evsub(w, 'k'), kn, vexd(w, Ak, EVK('k')))
fmk = mpv(w, Ak, FM, 'k', '( -u 2 x. %s )' % EVK('k'), w.s([evsub(w, 'k')], 'oveq2d', '( o = k -> ( -u 2 x. %s ) = ( -u 2 x. %s ) )' % (EVK('o'), EVK('k'))), kn, vexd(w, Ak, '( -u 2 x. %s )' % EVK('k')))
n2 = w.s([a1(w, P, '2cn', '2 e. CC')], 'negcld', '( %s -> -u 2 e. CC )' % P)
EVSR = 'sum_ r e. NN %s' % EVK('r')
evcbv = w.s([w.s([evsub(w, 'r', 'k')], 'cbvsumv', '%s = %s' % (EVS, EVSR))], 'a1i', '( %s -> %s = %s )' % (P, EVS, EVSR))
evlim = w.s([w.s([nz, oz, fek, evkc, evdom], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (P, FE, EVS)), evcbv], 'breqtrd', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (P, FE, EVSR))
fek2 = w.s([fek, evkc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, FE))
fmv = w.s([fmk, w.s([w.s([fek], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (Ak, EVK('k'), FE))], 'oveq2d', '( %s -> ( -u 2 x. %s ) = ( -u 2 x. ( %s ` k ) ) )' % (Ak, EVK('k'), FE))], 'eqtrd',
          '( %s -> ( %s ` k ) = ( -u 2 x. ( %s ` k ) ) )' % (Ak, FM, FE))
mlim = w.s([nz, oz, n2, evlim, fek2, fmv], 'isermulc2', '( %s -> seq 1 ( + , %s ) ~~> ( -u 2 x. %s ) )' % (P, FM, EVSR))
evsc = w.s([w.s([nz, oz, fek, evkc, evdom], 'isumcl', '( %s -> %s e. CC )' % (P, EVS)), evcbv], 'eqeltrrd', '( %s -> %s e. CC )' % (P, EVSR))
mdom = w.s([a1(w, P, 'seqex', 'seq 1 ( + , %s ) e. _V' % FM), w.s([n2, evsc], 'mulcld', '( %s -> ( -u 2 x. %s ) e. CC )' % (P, EVSR)), mlim, w.inst('breldmg')], 'syl3anc', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (P, FM))
n2evc = w.s([w.s([n2], 'adantr', '( %s -> -u 2 e. CC )' % Ak), evkc], 'mulcld', '( %s -> ( -u 2 x. %s ) e. CC )' % (Ak, EVK('k')))
add = w.s([nz, oz, fzv, ztk, fmk, n2evc, cvz, mdom], 'isumadd', '( %s -> sum_ k e. NN %s = ( %s + sum_ k e. NN ( -u 2 x. %s ) ) )' % (P, SK, ZS('Z'), EVK('k')))
mul = w.s([w.s([nz, oz, fek, evkc, evdom, n2], 'isummulc2', '( %s -> ( -u 2 x. %s ) = sum_ k e. NN ( -u 2 x. %s ) )' % (P, EVS, EVK('k')))], 'eqcomd', '( %s -> sum_ k e. NN ( -u 2 x. %s ) = ( -u 2 x. %s ) )' % (P, EVK('k'), EVS))
tot = w.s([w.s([sums, add], 'eqtrd', '( %s -> %s = ( %s + sum_ k e. NN ( -u 2 x. %s ) ) )' % (P, ALS, ZS('Z'), EVK('k'))),
           w.s([w.s([mul, w.s([evsum], 'oveq2d', '( %s -> ( -u 2 x. %s ) = ( -u 2 x. %s ) )' % (P, EVS, LIM))], 'eqtrd', '( %s -> sum_ k e. NN ( -u 2 x. %s ) = ( -u 2 x. %s ) )' % (P, EVK('k'), LIM))], 'oveq2d',
               '( %s -> ( %s + sum_ k e. NN ( -u 2 x. %s ) ) = ( %s + ( -u 2 x. %s ) ) )' % (P, ZS('Z'), EVK('k'), ZS('Z'), LIM))], 'eqtrd', '( %s -> %s = ( %s + ( -u 2 x. %s ) ) )' % (P, ALS, ZS('Z'), LIM))
# the algebra
zsc = w.s([nz, oz, fzv, ztk, cvz], 'isumcl', '( %s -> %s e. CC )' % (P, ZS('Z')))
p2c = w.s([a1(w, P, '2cn', '2 e. CC'), nzc], 'cxpcld', '( %s -> %s e. CC )' % (P, P2))
c2 = a1(w, P, '2cn', '2 e. CC')
a1_ = w.s([w.s([n2, p2c, zsc], 'mulassd', '( %s -> ( ( -u 2 x. %s ) x. %s ) = ( -u 2 x. %s ) )' % (P, P2, ZS('Z'), LIM))], 'eqcomd', '( %s -> ( -u 2 x. %s ) = ( ( -u 2 x. %s ) x. %s ) )' % (P, LIM, P2, ZS('Z')))
n2p = w.s([n2, p2c], 'mulcld', '( %s -> ( -u 2 x. %s ) e. CC )' % (P, P2))
a2_ = w.s([w.s([w.s([a1(w, P, 'ax-1cn', '1 e. CC'), n2p, zsc], 'adddird', '( %s -> ( ( 1 + ( -u 2 x. %s ) ) x. %s ) = ( ( 1 x. %s ) + ( ( -u 2 x. %s ) x. %s ) ) )' % (P, P2, ZS('Z'), ZS('Z'), P2, ZS('Z'))),
               w.s([w.s([zsc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (P, ZS('Z'), ZS('Z')))], 'oveq1d', '( %s -> ( ( 1 x. %s ) + ( ( -u 2 x. %s ) x. %s ) ) = ( %s + ( ( -u 2 x. %s ) x. %s ) ) )' % (P, ZS('Z'), P2, ZS('Z'), ZS('Z'), P2, ZS('Z')))],
              'eqtrd', '( %s -> ( ( 1 + ( -u 2 x. %s ) ) x. %s ) = ( %s + ( ( -u 2 x. %s ) x. %s ) ) )' % (P, P2, ZS('Z'), ZS('Z'), P2, ZS('Z')))], 'eqcomd',
          '( %s -> ( %s + ( ( -u 2 x. %s ) x. %s ) ) = ( ( 1 + ( -u 2 x. %s ) ) x. %s ) )' % (P, ZS('Z'), P2, ZS('Z'), P2, ZS('Z')))
a3_ = w.s([w.s([w.s([c2, p2c], 'mulneg1d', '( %s -> ( -u 2 x. %s ) = -u ( 2 x. %s ) )' % (P, P2, P2))], 'oveq2d', '( %s -> ( 1 + ( -u 2 x. %s ) ) = ( 1 + -u ( 2 x. %s ) ) )' % (P, P2, P2)),
           w.s([a1(w, P, 'ax-1cn', '1 e. CC'), w.s([c2, p2c], 'mulcld', '( %s -> ( 2 x. %s ) e. CC )' % (P, P2))], 'negsubd', '( %s -> ( 1 + -u ( 2 x. %s ) ) = ( 1 - ( 2 x. %s ) ) )' % (P, P2, P2))], 'eqtrd',
          '( %s -> ( 1 + ( -u 2 x. %s ) ) = ( 1 - ( 2 x. %s ) ) )' % (P, P2, P2))
# 2 ^c ( 1 - Z ) = 2 x. 2 ^c -u Z
ns = w.s([w.s([a1(w, P, 'ax-1cn', '1 e. CC'), zc], 'negsubd', '( %s -> ( 1 + -u Z ) = ( 1 - Z ) )' % P)], 'eqcomd', '( %s -> ( 1 - Z ) = ( 1 + -u Z ) )' % P)
cad = w.s([w.s([c2, a1(w, P, '2ne0', '2 =/= 0')], 'jca', '( %s -> ( 2 e. CC /\\ 2 =/= 0 ) )' % P), a1(w, P, 'ax-1cn', '1 e. CC'), nzc, w.inst('cxpadd')], 'syl3anc', '( %s -> ( 2 ^c ( 1 + -u Z ) ) = ( ( 2 ^c 1 ) x. %s ) )' % (P, P2))
c21 = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.inst('cxp1')], 'ax-mp', '( 2 ^c 1 ) = 2')], 'a1i', '( %s -> ( 2 ^c 1 ) = 2 )' % P)
e1z = w.s([w.s([w.s([ns], 'oveq2d', '( %s -> ( 2 ^c ( 1 - Z ) ) = ( 2 ^c ( 1 + -u Z ) ) )' % P), cad], 'eqtrd', '( %s -> ( 2 ^c ( 1 - Z ) ) = ( ( 2 ^c 1 ) x. %s ) )' % (P, P2)), w.s([c21], 'oveq1d', '( %s -> ( ( 2 ^c 1 ) x. %s ) = ( 2 x. %s ) )' % (P, P2, P2))], 'eqtrd',
          '( %s -> ( 2 ^c ( 1 - Z ) ) = ( 2 x. %s ) )' % (P, P2))
gf = w.s([w.s([e1z], 'oveq2d', '( %s -> %s = ( 1 - ( 2 x. %s ) ) )' % (P, GF, P2))], 'eqcomd', '( %s -> ( 1 - ( 2 x. %s ) ) = %s )' % (P, P2, GF))
alg = w.s([w.s([w.s([a1_], 'oveq2d', '( %s -> ( %s + ( -u 2 x. %s ) ) = ( %s + ( ( -u 2 x. %s ) x. %s ) ) )' % (P, ZS('Z'), LIM, ZS('Z'), P2, ZS('Z'))), a2_], 'eqtrd',
               '( %s -> ( %s + ( -u 2 x. %s ) ) = ( ( 1 + ( -u 2 x. %s ) ) x. %s ) )' % (P, ZS('Z'), LIM, P2, ZS('Z'))),
           w.s([w.s([a3_, gf], 'eqtrd', '( %s -> ( 1 + ( -u 2 x. %s ) ) = %s )' % (P, P2, GF))], 'oveq1d', '( %s -> ( ( 1 + ( -u 2 x. %s ) ) x. %s ) = ( %s x. %s ) )' % (P, P2, ZS('Z'), GF, ZS('Z')))], 'eqtrd',
          '( %s -> ( %s + ( -u 2 x. %s ) ) = ( %s x. %s ) )' % (P, ZS('Z'), LIM, GF, ZS('Z')))
w.qed([tot, alg], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (P, ALS, GF, ZS('Z')))
run7(w)

# ---------------------------------------------------------------- etazser
w = W('etazser', 'The eta function is ` ( 1 - 2 ^c ( 1 - Z ) ) zeta ( Z ) ` on ` Re Z > 1 ` '
      '( ~ etaalt , ~ zseralt ).  Lean\'s ` etaFun_eq_of_one_lt_re ` of Route Z\'s ZeroCount.lean.')
w.qed([w.s([w.s([], 'id', '( %s -> %s )' % (P, P)), w.inst('etaalt')], 'syl', '( %s -> %s = %s )' % (P, ETA('Z'), ALS)),
       w.s([w.s([], 'id', '( %s -> %s )' % (P, P)), w.inst('zseralt')], 'syl', '( %s -> %s = ( %s x. %s ) )' % (P, ALS, GF, ZS('Z')))], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (P, ETA('Z'), GF, ZS('Z')))
run7(w)

# ---------------------------------------------------------------- gfunne0
X2 = '( 2 ^c ( 1 - Z ) )'
w = W('gfunne0', 'The factor ` 1 - 2 ^c ( 1 - Z ) ` does not vanish on ` Re Z > 1 `: its modulus '
      '` 2 ^c ( 1 - Re Z ) ` is below ` 1 ` ( ~ abscxp , ~ cxpltd ).')
zc, z1, rz, nzc = zctx(w, P)
omz = w.s([a1(w, P, 'ax-1cn', '1 e. CC'), zc], 'subcld', '( %s -> ( 1 - Z ) e. CC )' % P)
ab = w.s([a1(w, P, '2rp', '2 e. RR+'), omz, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( 2 ^c ( Re ` ( 1 - Z ) ) ) )' % (P, X2))
re = w.s([w.s([a1(w, P, 'ax-1cn', '1 e. CC'), zc], 'resubd', '( %s -> ( Re ` ( 1 - Z ) ) = ( ( Re ` 1 ) - %s ) )' % (P, RZ)), w.s([a1(w, P, 're1', '( Re ` 1 ) = 1')], 'oveq1d', '( %s -> ( ( Re ` 1 ) - %s ) = ( 1 - %s ) )' % (P, RZ, RZ))], 'eqtrd',
         '( %s -> ( Re ` ( 1 - Z ) ) = ( 1 - %s ) )' % (P, RZ))
cl = Closure(w, P, {}); cl.leaf(RZ, 'RR', rz)
neg = linarith(w, P, [z1], '( 1 - %s ) < 0' % RZ, closure=cl)
ltb = w.s([a1(w, P, '2re', '2 e. RR'), a1(w, P, '1lt2', '1 < 2'), cl.mem('( 1 - %s )' % RZ, 'RR'), a1(w, P, '0re', '0 e. RR')], 'cxpltd', '( %s -> ( ( 1 - %s ) < 0 <-> ( 2 ^c ( 1 - %s ) ) < ( 2 ^c 0 ) ) )' % (P, RZ, RZ))
lt1 = w.s([w.s([neg, ltb], 'mpbid', '( %s -> ( 2 ^c ( 1 - %s ) ) < ( 2 ^c 0 ) )' % (P, RZ)), w.s([w.s([w.s([], '2cn', '2 e. CC'), w.inst('cxp0')], 'ax-mp', '( 2 ^c 0 ) = 1')], 'a1i', '( %s -> ( 2 ^c 0 ) = 1 )' % P)], 'breqtrd',
          '( %s -> ( 2 ^c ( 1 - %s ) ) < 1 )' % (P, RZ))
ablt = w.s([w.s([ab, w.s([re], 'oveq2d', '( %s -> ( 2 ^c ( Re ` ( 1 - Z ) ) ) = ( 2 ^c ( 1 - %s ) ) )' % (P, RZ))], 'eqtrd', '( %s -> ( abs ` %s ) = ( 2 ^c ( 1 - %s ) ) )' % (P, X2, RZ)), lt1], 'eqbrtrd', '( %s -> ( abs ` %s ) < 1 )' % (P, X2))
x2c = w.s([a1(w, P, '2cn', '2 e. CC'), omz], 'cxpcld', '( %s -> %s e. CC )' % (P, X2))
abne = w.s([w.s([x2c], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (P, X2)), ablt], 'ltned', '( %s -> ( abs ` %s ) =/= 1 )' % (P, X2))
imp_ = w.s([w.s([], 'fveq2', '( %s = 1 -> ( abs ` %s ) = ( abs ` 1 ) )' % (X2, X2)), w.s([], 'abs1', '( abs ` 1 ) = 1')], 'eqtrdi', '( %s = 1 -> ( abs ` %s ) = 1 )' % (X2, X2))
xne = w.s([abne, w.s([imp_], 'necon3i', '( ( abs ` %s ) =/= 1 -> %s =/= 1 )' % (X2, X2))], 'syl', '( %s -> %s =/= 1 )' % (P, X2))
w.qed([a1(w, P, 'ax-1cn', '1 e. CC'), x2c, w.s([xne], 'necomd', '( %s -> 1 =/= %s )' % (P, X2))], 'subne0d', '( %s -> %s =/= 0 )' % (P, GF))
run7(w)
