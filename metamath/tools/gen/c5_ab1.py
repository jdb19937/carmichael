"""C5, agreement block: the Abel series equals the Dirichlet series on Re > 1
(Lean LSeries_eq_Afun): the boundary term tends to zero, the finite identity
in sequence form, and the limit."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

RZ = '( Re ` Z )'
ZP1 = '( Z e. CC /\\ 1 < %s )' % RZ


def BT(S, n):
    return '( ( %s ` ( %s + 1 ) ) x. ( ( %s + 1 ) ^c -u Z ) )' % (S, n, n)


# ---------------------------------------------------------------- abagr1
w = W('abagr1', 'The boundary term of Abel summation for bounded partial sums tends to zero to the '
      'right of the line one ( ~ divcnvshft , ~ climsqz2 , ~ climabs0 ).')
A0 = '( %s /\\ %s )' % (ABS, ZP1)
FB = '( n e. NN |-> %s )' % BT('S', 'n')
GA = '( n e. NN |-> ( abs ` %s ) )' % BT('S', 'n')
FD = '( n e. NN |-> ( B / ( n + 1 ) ) )'
abs_ = w.s([], 'simpl', '( %s -> %s )' % (A0, ABS))
sf = w.s([abs_, w.inst('simp1')], 'syl', '( %s -> S : NN --> CC )' % A0)
br = w.s([abs_, w.inst('simp2')], 'syl', '( %s -> B e. RR )' % A0)
bq = w.s([abs_, w.inst('simp3')], 'syl', '( %s -> A. m e. NN ( abs ` ( S ` m ) ) <_ B )' % A0)
zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
z1 = w.s([], 'simprr', '( %s -> 1 < %s )' % (A0, RZ))
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
r1 = a1(w, A0, '1re', '1 e. RR')
le1 = w.s([r1, rz, z1], 'ltled', '( %s -> 1 <_ %s )' % (A0, RZ))
nu1, iz, n1 = nnuz(w, A0)
nnex = a1(w, A0, 'nnex', 'NN e. _V')
fdex = w.s([nnex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, FD))
gaex = w.s([nnex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, GA))
fbex = w.s([nnex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, FB))
Ak = '( %s /\\ k e. NN )' % A0
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( k + 1 ) e. NN )' % Ak)
k1c = w.s([k1n], 'nncnd', '( %s -> ( k + 1 ) e. CC )' % Ak)
k1rp = w.s([k1n], 'nnrpd', '( %s -> ( k + 1 ) e. RR+ )' % Ak)
# FD -> 0
subd = w.s([w.s([], 'oveq1', '( n = k -> ( n + 1 ) = ( k + 1 ) )')], 'oveq2d', '( n = k -> ( B / ( n + 1 ) ) = ( B / ( k + 1 ) ) )')
fdv = mpv(w, Ak, FD, 'k', '( B / ( k + 1 ) )', subd, kn, vexd(w, Ak, '( B / ( k + 1 ) )'))
fd0 = w.s([nu1, iz, w.s([br], 'recnd', '( %s -> B e. CC )' % A0), iz, fdex, fdv], 'divcnvshft', '( %s -> %s ~~> 0 )' % (A0, FD))
# the termwise bound
sk = w.s([w.s([sf], 'adantr', '( %s -> S : NN --> CC )' % Ak), k1n], 'ffvelcdmd', '( %s -> ( S ` ( k + 1 ) ) e. CC )' % Ak)
pw = w.s([k1c, w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)], 'negcld', '( %s -> -u Z e. CC )' % Ak), w.inst('cxpcl')], 'syl2anc',
         '( %s -> ( ( k + 1 ) ^c -u Z ) e. CC )' % Ak)
btc = w.s([sk, pw], 'mulcld', '( %s -> %s e. CC )' % (Ak, BT('S', 'k')))
subb = w.s([w.s([], 'fveq2', '( m = ( k + 1 ) -> ( S ` m ) = ( S ` ( k + 1 ) ) )')], 'fveq2d',
           '( m = ( k + 1 ) -> ( abs ` ( S ` m ) ) = ( abs ` ( S ` ( k + 1 ) ) ) )')
sbb = w.s([subb], 'breq1d', '( m = ( k + 1 ) -> ( ( abs ` ( S ` m ) ) <_ B <-> ( abs ` ( S ` ( k + 1 ) ) ) <_ B ) )')
sle = w.s([sbb, w.s([bq], 'adantr', '( %s -> A. m e. NN ( abs ` ( S ` m ) ) <_ B )' % Ak), k1n], 'rspcdva', '( %s -> ( abs ` ( S ` ( k + 1 ) ) ) <_ B )' % Ak)
pab = w.s([k1n, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak), w.inst('cxpnnabs')], 'syl2anc', '( %s -> ( abs ` ( ( k + 1 ) ^c -u Z ) ) = ( ( k + 1 ) ^c -u %s ) )' % (Ak, RZ))
ple = w.s([w.s([w.s([k1n, a1(w, Ak, '1re', '1 e. RR'), w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)], '3jca', '( %s -> ( ( k + 1 ) e. NN /\\ 1 e. RR /\\ Z e. CC ) )' % Ak),
                 w.s([le1], 'adantr', '( %s -> 1 <_ %s )' % (Ak, RZ))], 'jca', '( %s -> ( ( ( k + 1 ) e. NN /\\ 1 e. RR /\\ Z e. CC ) /\\ 1 <_ %s ) )' % (Ak, RZ)),
            w.inst('cxpnnle')], 'syl', '( %s -> ( ( k + 1 ) ^c -u %s ) <_ ( ( k + 1 ) ^c -u 1 ) )' % (Ak, RZ))
p1 = w.s([w.s([k1c, w.s([k1n], 'nnne0d', '( %s -> ( k + 1 ) =/= 0 )' % Ak), a1(w, Ak, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], 'syl3anc',
              '( %s -> ( ( k + 1 ) ^c -u 1 ) = ( 1 / ( ( k + 1 ) ^c 1 ) ) )' % Ak),
          w.s([w.s([k1c, w.inst('cxp1')], 'syl', '( %s -> ( ( k + 1 ) ^c 1 ) = ( k + 1 ) )' % Ak)], 'oveq2d', '( %s -> ( 1 / ( ( k + 1 ) ^c 1 ) ) = ( 1 / ( k + 1 ) ) )' % Ak)],
         'eqtrd', '( %s -> ( ( k + 1 ) ^c -u 1 ) = ( 1 / ( k + 1 ) ) )' % Ak)
ple2 = w.s([w.s([pab, ple], 'eqbrtrd', '( %s -> ( abs ` ( ( k + 1 ) ^c -u Z ) ) <_ ( ( k + 1 ) ^c -u 1 ) )' % Ak), p1], 'breqtrd',
           '( %s -> ( abs ` ( ( k + 1 ) ^c -u Z ) ) <_ ( 1 / ( k + 1 ) ) )' % Ak)
absk = w.s([sk], 'abscld', '( %s -> ( abs ` ( S ` ( k + 1 ) ) ) e. RR )' % Ak)
abpw = w.s([pw], 'abscld', '( %s -> ( abs ` ( ( k + 1 ) ^c -u Z ) ) e. RR )' % Ak)
rk1 = w.s([w.s([k1rp], 'rpreccld', '( %s -> ( 1 / ( k + 1 ) ) e. RR+ )' % Ak)], 'rpred', '( %s -> ( 1 / ( k + 1 ) ) e. RR )' % Ak)
brk = w.s([br], 'adantr', '( %s -> B e. RR )' % Ak)
mul = w.s([absk, brk, abpw, rk1, w.s([sk], 'absge0d', '( %s -> 0 <_ ( abs ` ( S ` ( k + 1 ) ) ) )' % Ak), w.s([pw], 'absge0d', '( %s -> 0 <_ ( abs ` ( ( k + 1 ) ^c -u Z ) ) )' % Ak),
           sle, ple2], 'lemul12ad', '( %s -> ( ( abs ` ( S ` ( k + 1 ) ) ) x. ( abs ` ( ( k + 1 ) ^c -u Z ) ) ) <_ ( B x. ( 1 / ( k + 1 ) ) ) )' % Ak)
bnd = w.s([w.s([sk, pw], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` ( S ` ( k + 1 ) ) ) x. ( abs ` ( ( k + 1 ) ^c -u Z ) ) ) )' % (Ak, BT('S', 'k'))), mul], 'eqbrtrd',
          '( %s -> ( abs ` %s ) <_ ( B x. ( 1 / ( k + 1 ) ) ) )' % (Ak, BT('S', 'k')))
bnd2 = w.s([bnd, w.s([w.s([brk], 'recnd', '( %s -> B e. CC )' % Ak), k1c, w.s([k1n], 'nnne0d', '( %s -> ( k + 1 ) =/= 0 )' % Ak)], 'divrecd',
                     '( %s -> ( B / ( k + 1 ) ) = ( B x. ( 1 / ( k + 1 ) ) ) )' % Ak)], 'breqtrrd', '( %s -> ( abs ` %s ) <_ ( B / ( k + 1 ) ) )' % (Ak, BT('S', 'k')))
# GA values and the squeeze
subg = w.s([w.s([w.s([], 'oveq1', '( n = k -> ( n + 1 ) = ( k + 1 ) )')], 'fveq2d', '( n = k -> ( S ` ( n + 1 ) ) = ( S ` ( k + 1 ) ) )'),
            w.s([w.s([], 'oveq1', '( n = k -> ( n + 1 ) = ( k + 1 ) )')], 'oveq1d', '( n = k -> ( ( n + 1 ) ^c -u Z ) = ( ( k + 1 ) ^c -u Z ) )')], 'oveq12d',
           '( n = k -> %s = %s )' % (BT('S', 'n'), BT('S', 'k')))
fbv = mpv(w, Ak, FB, 'k', BT('S', 'k'), subg, kn, vexd(w, Ak, BT('S', 'k')))
gav = mpv(w, Ak, GA, 'k', '( abs ` %s )' % BT('S', 'k'), w.s([subg], 'fveq2d', '( n = k -> ( abs ` %s ) = ( abs ` %s ) )' % (BT('S', 'n'), BT('S', 'k'))), kn,
          vexd(w, Ak, '( abs ` %s )' % BT('S', 'k'), 'fv'))
fdr = w.s([fdv, w.s([brk, k1rp], 'rerpdivcld', '( %s -> ( B / ( k + 1 ) ) e. RR )' % Ak)], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, FD))
gar = w.s([gav, w.s([btc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, BT('S', 'k')))], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, GA))
gle = w.s([w.s([gav, bnd2], 'eqbrtrd', '( %s -> ( %s ` k ) <_ ( B / ( k + 1 ) ) )' % (Ak, GA)), fdv], 'breqtrrd', '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Ak, GA, FD))
gge = w.s([w.s([btc], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Ak, BT('S', 'k'))), gav], 'breqtrrd', '( %s -> 0 <_ ( %s ` k ) )' % (Ak, GA))
ga0 = w.s([nu1, iz, fd0, gaex, fdr, gar, gle, gge], 'climsqz2', '( %s -> %s ~~> 0 )' % (A0, GA))
gaab = w.s([gav, w.s([fbv], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, FB, BT('S', 'k')))], 'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, GA, FB))
fbc = w.s([fbv, btc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, FB))
bi = w.s([nu1, iz, fbex, gaex, fbc, gaab], 'climabs0', '( %s -> ( %s ~~> 0 <-> %s ~~> 0 ) )' % (A0, FB, GA))
w.qed([ga0, bi], 'mpbird', '( %s -> %s ~~> 0 )' % (A0, FB))
run5(w)

# ---------------------------------------------------------------- abagr2
PSFA = PSF()
w = W('abagr2', 'Abel summation for a Dirichlet series in sequence form: the partial sum to ` N + 1 ` is the '
      'boundary term plus the partial Abel series to ` N ` ( ~ abelid at ` N + 1 ` ).')
A0 = '( ( A : NN --> CC /\\ Z e. CC ) /\\ N e. NN )'
af = w.s([], 'simpll', '( %s -> A : NN --> CC )' % A0)
zc = w.s([], 'simplr', '( %s -> Z e. CC )' % A0)
nn = w.s([], 'simpr', '( %s -> N e. NN )' % A0)
n1n = w.s([nn, w.inst('peano2nn')], 'syl', '( %s -> ( N + 1 ) e. NN )' % A0)
ab = w.s([w.s([af, zc, n1n], '3jca', '( %s -> ( A : NN --> CC /\\ Z e. CC /\\ ( N + 1 ) e. NN ) )' % A0), w.inst('abelid')], 'syl',
         '( %s -> sum_ k e. ( 1 ... ( N + 1 ) ) %s = ( ( %s x. ( ( N + 1 ) ^c -u Z ) ) + sum_ j e. ( 1 ..^ ( N + 1 ) ) %s ) )' % (
             A0, TRM('A', 'k', 'Z'), PSUM('A', '( N + 1 )'), ATMS('A', 'j', 'Z')))
subq = lambda t: w.s([w.s([], 'oveq2', '( q = %s -> ( 1 ... q ) = ( 1 ... %s ) )' % (t, t))], 'sumeq1d', '( q = %s -> %s = %s )' % (t, PSUM('A', 'q'), PSUM('A', t)))
pv1 = mpv(w, A0, PSFA, '( N + 1 )', PSUM('A', '( N + 1 )'), subq('( N + 1 )'), n1n, vexd(w, A0, PSUM('A', '( N + 1 )'), 'sum'))
t1 = w.s([w.s([pv1], 'eqcomd', '( %s -> %s = ( %s ` ( N + 1 ) ) )' % (A0, PSUM('A', '( N + 1 )'), PSFA))], 'oveq1d',
         '( %s -> ( %s x. ( ( N + 1 ) ^c -u Z ) ) = ( ( %s ` ( N + 1 ) ) x. ( ( N + 1 ) ^c -u Z ) ) )' % (A0, PSUM('A', '( N + 1 )'), PSFA))
fz = w.s([w.s([w.s([nn], 'nnzd', '( %s -> N e. ZZ )' % A0), w.inst('fzval3')], 'syl', '( %s -> ( 1 ... N ) = ( 1 ..^ ( N + 1 ) ) )' % A0)], 'eqcomd',
         '( %s -> ( 1 ..^ ( N + 1 ) ) = ( 1 ... N ) )' % A0)
s2 = w.s([fz], 'sumeq1d', '( %s -> sum_ j e. ( 1 ..^ ( N + 1 ) ) %s = sum_ j e. ( 1 ... N ) %s )' % (A0, ATMS('A', 'j', 'Z'), ATMS('A', 'j', 'Z')))
Aj = '( %s /\\ j e. ( 1 ... N ) )' % A0
jn = w.s([w.s([], 'simpr', '( %s -> j e. ( 1 ... N ) )' % Aj), w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % Aj)
pvj = mpv(w, Aj, PSFA, 'j', PSUM('A', 'j'), subq('j'), jn, vexd(w, Aj, PSUM('A', 'j'), 'sum'))
s3 = w.s([w.s([w.s([pvj], 'eqcomd', '( %s -> %s = ( %s ` j ) )' % (Aj, PSUM('A', 'j'), PSFA))], 'oveq1d', '( %s -> %s = %s )' % (Aj, ATMS('A', 'j', 'Z'), ATM(PSFA, 'j', 'Z')))],
         'sumeq2dv', '( %s -> sum_ j e. ( 1 ... N ) %s = sum_ j e. ( 1 ... N ) %s )' % (A0, ATMS('A', 'j', 'Z'), ATM(PSFA, 'j', 'Z')))
w.qed([ab, w.s([t1, w.s([s2, s3], 'eqtrd', '( %s -> sum_ j e. ( 1 ..^ ( N + 1 ) ) %s = sum_ j e. ( 1 ... N ) %s )' % (A0, ATMS('A', 'j', 'Z'), ATM(PSFA, 'j', 'Z')))],
                'oveq12d', '( %s -> ( ( %s x. ( ( N + 1 ) ^c -u Z ) ) + sum_ j e. ( 1 ..^ ( N + 1 ) ) %s ) = ( %s + sum_ j e. ( 1 ... N ) %s ) )' % (
                    A0, PSUM('A', '( N + 1 )'), ATMS('A', 'j', 'Z'), BT(PSFA, 'N'), ATM(PSFA, 'j', 'Z')))],
      'eqtrd', '( %s -> sum_ k e. ( 1 ... ( N + 1 ) ) %s = ( %s + sum_ j e. ( 1 ... N ) %s ) )' % (A0, TRM('A', 'k', 'Z'), BT(PSFA, 'N'), ATM(PSFA, 'j', 'Z')))
run5(w)

# ---------------------------------------------------------------- psff
w = W('psff', 'The partial sums of a complex sequence form a complex sequence.')
A0 = 'A : NN --> CC'
Aq = '( %s /\\ q e. NN )' % A0
Aqi = '( %s /\\ i e. ( 1 ... q ) )' % Aq
aic = w.s([w.s([], 'ad2antrr', '( %s -> A : NN --> CC )' % Aqi), w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... q ) )' % Aqi), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Aqi)],
          'ffvelcdmd', '( %s -> ( A ` i ) e. CC )' % Aqi)
pscl = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... q ) e. Fin )' % Aq), aic], 'fsumcl', '( %s -> %s e. CC )' % (Aq, PSUM('A', 'q')))
w.qed([pscl, w.s([], 'eqid', '%s = %s' % (PSFA, PSFA))], 'fmptd', '( %s -> %s : NN --> CC )' % (A0, PSFA))
run5(w)

# ---------------------------------------------------------------- abagr
w = W('abagr', 'The Abel series of a Dirichlet series with bounded coefficients and bounded partial sums '
      'agrees with the Dirichlet series to the right of the line one: Lean\'s ` LSeries_eq_Afun ` '
      'of LGrowth.lean, with no identity theorem ( ~ abagr2 , ~ abagr1 , ~ climadd , ~ climuni ).')
ABSP = '( B e. RR /\\ A. m e. NN ( abs ` %s ) <_ B )' % PSUM('A', 'm')
A0 = '( ( %s /\\ %s ) /\\ %s )' % (CFB, ZP1, ABSP)
DSER = 'sum_ k e. NN %s' % TRM('A', 'k', 'Z')
ABSR = 'sum_ j e. NN %s' % ATM(PSFA, 'j', 'Z')
GN = '( n e. NN |-> %s )' % TRM('A', 'n', 'Z')
F1 = 'seq 1 ( + , %s )' % GN
F2 = '( e e. NN |-> ( %s ` ( e + 1 ) ) )' % F1
F3 = '( n e. NN |-> %s )' % BT(PSFA, 'n')
ATMN = '( n e. NN |-> %s )' % ATM(PSFA, 'n', 'Z')
F4 = '( n e. NN |-> sum_ j e. ( 1 ... n ) %s )' % ATM(PSFA, 'j', 'Z')
SQ4 = 'seq 1 ( + , %s )' % ATMN
dsh = w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (A0, CFB, ZP1))
cfb = w.s([dsh, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, CFB))
zp = w.s([dsh, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ZP1))
af = w.s([cfb, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A0)
z1 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 1 < %s )' % (A0, RZ))
absp = w.s([], 'simpr', '( %s -> %s )' % (A0, ABSP))
br = w.s([absp, w.inst('simpl')], 'syl', '( %s -> B e. RR )' % A0)
bq = w.s([absp, w.inst('simpr')], 'syl', '( %s -> A. m e. NN ( abs ` %s ) <_ B )' % (A0, PSUM('A', 'm')))
nu1, iz, n1 = nnuz(w, A0)
nnex = a1(w, A0, 'nnex', 'NN e. _V')
rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
z0 = w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), rz, a1(w, A0, '0lt1', '0 < 1'), z1], 'lttrd', '( %s -> 0 < %s )' % (A0, RZ))
# ABS for PSF
psf = w.s([af, w.inst('psff')], 'syl', '( %s -> %s : NN --> CC )' % (A0, PSFA))
subq = lambda t: w.s([w.s([], 'oveq2', '( q = %s -> ( 1 ... q ) = ( 1 ... %s ) )' % (t, t))], 'sumeq1d', '( q = %s -> %s = %s )' % (t, PSUM('A', 'q'), PSUM('A', t)))
mv = mpv(w, 'm e. NN', PSFA, 'm', PSUM('A', 'm'), subq('m'), w.s([], 'id', '( m e. NN -> m e. NN )'), vexd(w, 'm e. NN', PSUM('A', 'm'), 'sum'))
mb = w.s([w.s([w.s([mv], 'fveq2d', '( m e. NN -> ( abs ` ( %s ` m ) ) = ( abs ` %s ) )' % (PSFA, PSUM('A', 'm')))], 'breq1d',
              '( m e. NN -> ( ( abs ` ( %s ` m ) ) <_ B <-> ( abs ` %s ) <_ B ) )' % (PSFA, PSUM('A', 'm')))], 'ralbiia',
         '( A. m e. NN ( abs ` ( %s ` m ) ) <_ B <-> A. m e. NN ( abs ` %s ) <_ B )' % (PSFA, PSUM('A', 'm')))
bq2 = w.s([bq, w.s([mb], 'a1i', '( %s -> ( A. m e. NN ( abs ` ( %s ` m ) ) <_ B <-> A. m e. NN ( abs ` %s ) <_ B ) )' % (A0, PSFA, PSUM('A', 'm')))], 'mpbird',
          '( %s -> A. m e. NN ( abs ` ( %s ` m ) ) <_ B )' % (A0, PSFA))
ABSF = '( %s : NN --> CC /\\ B e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ B )' % (PSFA, PSFA)
absf = w.s([psf, br, bq2], '3jca', '( %s -> %s )' % (A0, ABSF))
# F1 -> DSER, F2 -> DSER
Ad = '( %s /\\ d e. NN )' % A0
dn = w.s([], 'simpr', '( %s -> d e. NN )' % Ad)
subn = lambda t: w.s([w.s([], 'fveq2', '( n = %s -> ( A ` n ) = ( A ` %s ) )' % (t, t)), w.s([], 'oveq1', '( n = %s -> ( n ^c -u Z ) = ( %s ^c -u Z ) )' % (t, t))], 'oveq12d',
                     '( n = %s -> %s = %s )' % (t, TRM('A', 'n', 'Z'), TRM('A', t, 'Z')))
gv = mpv(w, Ad, GN, 'd', TRM('A', 'd', 'Z'), subn('d'), dn, vexd(w, Ad, TRM('A', 'd', 'Z')))
tc = w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ad), dn], 'ffvelcdmd', '( %s -> ( A ` d ) e. CC )' % Ad),
          w.s([w.s([dn], 'nncnd', '( %s -> d e. CC )' % Ad), w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad)], 'negcld', '( %s -> -u Z e. CC )' % Ad), w.inst('cxpcl')], 'syl2anc',
              '( %s -> ( d ^c -u Z ) e. CC )' % Ad)], 'mulcld', '( %s -> %s e. CC )' % (Ad, TRM('A', 'd', 'Z')))
cv1 = w.s([dsh, w.inst('dsercvg')], 'syl', '( %s -> %s e. dom ~~> )' % (A0, F1))
Akk = '( %s /\\ k e. NN )' % A0
knk = w.s([], 'simpr', '( %s -> k e. NN )' % Akk)
gvk0 = mpv(w, Akk, GN, 'k', TRM('A', 'k', 'Z'), subn('k'), knk, vexd(w, Akk, TRM('A', 'k', 'Z')))
tck0 = w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Akk), knk], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % Akk),
            w.s([w.s([knk], 'nncnd', '( %s -> k e. CC )' % Akk), w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Akk)], 'negcld', '( %s -> -u Z e. CC )' % Akk), w.inst('cxpcl')], 'syl2anc',
                '( %s -> ( k ^c -u Z ) e. CC )' % Akk)], 'mulcld', '( %s -> %s e. CC )' % (Akk, TRM('A', 'k', 'Z')))
l1 = w.s([nu1, iz, gvk0, tck0, cv1], 'isumclim2', '( %s -> %s ~~> %s )' % (A0, F1, DSER))
f1ex = a1(w, A0, 'seqex', '%s e. _V' % F1)
f2ex = w.s([nnex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, F2))
sub2 = w.s([w.s([], 'oveq1', '( e = d -> ( e + 1 ) = ( d + 1 ) )')], 'fveq2d', '( e = d -> ( %s ` ( e + 1 ) ) = ( %s ` ( d + 1 ) ) )' % (F1, F1))
f2v = mpv(w, Ad, F2, 'd', '( %s ` ( d + 1 ) )' % F1, sub2, dn, vexd(w, Ad, '( %s ` ( d + 1 ) )' % F1, 'fv'))
sh = w.s([nu1, iz, iz, f2ex, f1ex, w.s([f2v], 'eqcomd', '( %s -> ( %s ` ( d + 1 ) ) = ( %s ` d ) )' % (Ad, F1, F2))], 'climshft2',
         '( %s -> ( %s ~~> %s <-> %s ~~> %s ) )' % (A0, F2, DSER, F1, DSER))
l2 = w.s([l1, sh], 'mpbird', '( %s -> %s ~~> %s )' % (A0, F2, DSER))
# the value of F2 at d through abagr2
d1n = w.s([dn, w.inst('peano2nn')], 'syl', '( %s -> ( d + 1 ) e. NN )' % Ad)
Adk = '( %s /\\ k e. ( 1 ... ( d + 1 ) ) )' % Ad
kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... ( d + 1 ) ) )' % Adk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Adk)
gvk = mpv(w, Adk, GN, 'k', TRM('A', 'k', 'Z'), subn('k'), kn, vexd(w, Adk, TRM('A', 'k', 'Z')))
tck = w.s([w.s([w.s([af], 'ad2antrr', '( %s -> A : NN --> CC )' % Adk), kn], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % Adk),
           w.s([w.s([kn], 'nncnd', '( %s -> k e. CC )' % Adk), w.s([w.s([zc], 'ad2antrr', '( %s -> Z e. CC )' % Adk)], 'negcld', '( %s -> -u Z e. CC )' % Adk), w.inst('cxpcl')], 'syl2anc',
               '( %s -> ( k ^c -u Z ) e. CC )' % Adk)], 'mulcld', '( %s -> %s e. CC )' % (Adk, TRM('A', 'k', 'Z')))
fs1 = w.s([gvk, w.s([d1n, nu1], 'eleqtrdi', '( %s -> ( d + 1 ) e. ( ZZ>= ` 1 ) )' % Ad), tck], 'fsumser',
          '( %s -> sum_ k e. ( 1 ... ( d + 1 ) ) %s = ( %s ` ( d + 1 ) ) )' % (Ad, TRM('A', 'k', 'Z'), F1))
ab2 = w.s([w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % Ad), w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad)], 'jca', '( %s -> ( A : NN --> CC /\\ Z e. CC ) )' % Ad), dn], 'jca',
               '( %s -> ( ( A : NN --> CC /\\ Z e. CC ) /\\ d e. NN ) )' % Ad), w.inst('abagr2')], 'syl',
          '( %s -> sum_ k e. ( 1 ... ( d + 1 ) ) %s = ( %s + sum_ j e. ( 1 ... d ) %s ) )' % (Ad, TRM('A', 'k', 'Z'), BT(PSFA, 'd'), ATM(PSFA, 'j', 'Z')))
# F3 and F4 values
sub3 = w.s([w.s([w.s([], 'oveq1', '( n = d -> ( n + 1 ) = ( d + 1 ) )')], 'fveq2d', '( n = d -> ( %s ` ( n + 1 ) ) = ( %s ` ( d + 1 ) ) )' % (PSFA, PSFA)),
            w.s([w.s([], 'oveq1', '( n = d -> ( n + 1 ) = ( d + 1 ) )')], 'oveq1d', '( n = d -> ( ( n + 1 ) ^c -u Z ) = ( ( d + 1 ) ^c -u Z ) )')], 'oveq12d',
           '( n = d -> %s = %s )' % (BT(PSFA, 'n'), BT(PSFA, 'd')))
f3v = mpv(w, Ad, F3, 'd', BT(PSFA, 'd'), sub3, dn, vexd(w, Ad, BT(PSFA, 'd')))
sub4 = w.s([w.s([], 'oveq2', '( n = d -> ( 1 ... n ) = ( 1 ... d ) )')], 'sumeq1d', '( n = d -> sum_ j e. ( 1 ... n ) %s = sum_ j e. ( 1 ... d ) %s )' % (ATM(PSFA, 'j', 'Z'), ATM(PSFA, 'j', 'Z')))
f4v = mpv(w, Ad, F4, 'd', 'sum_ j e. ( 1 ... d ) %s' % ATM(PSFA, 'j', 'Z'), sub4, dn, vexd(w, Ad, 'sum_ j e. ( 1 ... d ) %s' % ATM(PSFA, 'j', 'Z'), 'sum'))
hval = w.s([w.s([f2v, w.s([w.s([fs1], 'eqcomd', '( %s -> ( %s ` ( d + 1 ) ) = sum_ k e. ( 1 ... ( d + 1 ) ) %s )' % (Ad, F1, TRM('A', 'k', 'Z'))), ab2], 'eqtrd',
                          '( %s -> ( %s ` ( d + 1 ) ) = ( %s + sum_ j e. ( 1 ... d ) %s ) )' % (Ad, F1, BT(PSFA, 'd'), ATM(PSFA, 'j', 'Z')))], 'eqtrd',
                '( %s -> ( %s ` d ) = ( %s + sum_ j e. ( 1 ... d ) %s ) )' % (Ad, F2, BT(PSFA, 'd'), ATM(PSFA, 'j', 'Z'))),
            w.s([f3v, f4v], 'oveq12d', '( %s -> ( ( %s ` d ) + ( %s ` d ) ) = ( %s + sum_ j e. ( 1 ... d ) %s ) )' % (Ad, F3, F4, BT(PSFA, 'd'), ATM(PSFA, 'j', 'Z')))],
           'eqtr4d', '( %s -> ( %s ` d ) = ( ( %s ` d ) + ( %s ` d ) ) )' % (Ad, F2, F3, F4))
# F3 -> 0
l3 = w.s([w.s([absf, w.s([zc, z1], 'jca', '( %s -> %s )' % (A0, ZP1))], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, ABSF, ZP1)), w.inst('abagr1')], 'syl',
         '( %s -> %s ~~> 0 )' % (A0, F3))
# F4 -> ABSR
absz = w.s([absf, w.s([zc, z0], 'jca', '( %s -> ( Z e. CC /\\ 0 < %s ) )' % (A0, RZ))], 'jca', '( %s -> ( %s /\\ ( Z e. CC /\\ 0 < %s ) ) )' % (A0, ABSF, RZ))
cv4 = w.s([absz, w.inst('abcvg')], 'syl', '( %s -> %s e. dom ~~> )' % (A0, SQ4))
Aj = '( %s /\\ j e. NN )' % A0
jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
suba = lambda t: w.s([w.s([], 'fveq2', '( n = %s -> ( %s ` n ) = ( %s ` %s ) )' % (t, PSFA, PSFA, t)),
                      w.s([w.s([], 'oveq1', '( n = %s -> ( n ^c -u Z ) = ( %s ^c -u Z ) )' % (t, t)),
                           w.s([w.s([], 'oveq1', '( n = %s -> ( n + 1 ) = ( %s + 1 ) )' % (t, t))], 'oveq1d', '( n = %s -> ( ( n + 1 ) ^c -u Z ) = ( ( %s + 1 ) ^c -u Z ) )' % (t, t))],
                          'oveq12d', '( n = %s -> ( ( n ^c -u Z ) - ( ( n + 1 ) ^c -u Z ) ) = ( ( %s ^c -u Z ) - ( ( %s + 1 ) ^c -u Z ) ) )' % (t, t, t))], 'oveq12d',
                     '( n = %s -> %s = %s )' % (t, ATM(PSFA, 'n', 'Z'), ATM(PSFA, t, 'Z')))
av = mpv(w, Aj, ATMN, 'j', ATM(PSFA, 'j', 'Z'), suba('j'), jn, vexd(w, Aj, ATM(PSFA, 'j', 'Z')))


def atmcl(w, ante, t, jn_, psf_, zc_):
    j1c = w.s([w.s([jn_, w.inst('peano2nn')], 'syl', '( %s -> ( %s + 1 ) e. NN )' % (ante, t))], 'nncnd', '( %s -> ( %s + 1 ) e. CC )' % (ante, t))
    nz = w.s([zc_], 'negcld', '( %s -> -u Z e. CC )' % ante)
    return w.s([w.s([psf_, jn_], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (ante, PSFA, t)),
                w.s([w.s([w.s([jn_], 'nncnd', '( %s -> %s e. CC )' % (ante, t)), nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( %s ^c -u Z ) e. CC )' % (ante, t)),
                     w.s([j1c, nz, w.inst('cxpcl')], 'syl2anc', '( %s -> ( ( %s + 1 ) ^c -u Z ) e. CC )' % (ante, t))], 'subcld',
                    '( %s -> ( ( %s ^c -u Z ) - ( ( %s + 1 ) ^c -u Z ) ) e. CC )' % (ante, t, t))], 'mulcld', '( %s -> %s e. CC )' % (ante, ATM(PSFA, t, 'Z')))


acj = atmcl(w, Aj, 'j', jn, w.s([psf], 'adantr', '( %s -> %s : NN --> CC )' % (Aj, PSFA)), w.s([zc], 'adantr', '( %s -> Z e. CC )' % Aj))
l4s = w.s([nu1, iz, av, acj, cv4], 'isumclim2', '( %s -> %s ~~> %s )' % (A0, SQ4, ABSR))
Adj = '( %s /\\ j e. ( 1 ... d ) )' % Ad
jnd = w.s([w.s([], 'simpr', '( %s -> j e. ( 1 ... d ) )' % Adj), w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % Adj)
avd = mpv(w, Adj, ATMN, 'j', ATM(PSFA, 'j', 'Z'), suba('j'), jnd, vexd(w, Adj, ATM(PSFA, 'j', 'Z')))
acd = atmcl(w, Adj, 'j', jnd, w.s([psf], 'ad2antrr', '( %s -> %s : NN --> CC )' % (Adj, PSFA)), w.s([zc], 'ad2antrr', '( %s -> Z e. CC )' % Adj))
fs4 = w.s([avd, w.s([dn, nu1], 'eleqtrdi', '( %s -> d e. ( ZZ>= ` 1 ) )' % Ad), acd], 'fsumser',
          '( %s -> sum_ j e. ( 1 ... d ) %s = ( %s ` d ) )' % (Ad, ATM(PSFA, 'j', 'Z'), SQ4))
f4ex = w.s([nnex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A0, F4))
eq4 = w.s([nu1, f4ex, a1(w, A0, 'seqex', '%s e. _V' % SQ4), iz, w.s([f4v, fs4], 'eqtrd', '( %s -> ( %s ` d ) = ( %s ` d ) )' % (Ad, F4, SQ4))], 'climeq',
          '( %s -> ( %s ~~> %s <-> %s ~~> %s ) )' % (A0, F4, ABSR, SQ4, ABSR))
l4 = w.s([l4s, eq4], 'mpbird', '( %s -> %s ~~> %s )' % (A0, F4, ABSR))
# climadd and climuni
btc = w.s([w.s([w.s([psf], 'adantr', '( %s -> %s : NN --> CC )' % (Ad, PSFA)), d1n], 'ffvelcdmd', '( %s -> ( %s ` ( d + 1 ) ) e. CC )' % (Ad, PSFA)),
           w.s([w.s([d1n], 'nncnd', '( %s -> ( d + 1 ) e. CC )' % Ad), w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ad)], 'negcld', '( %s -> -u Z e. CC )' % Ad), w.inst('cxpcl')], 'syl2anc',
               '( %s -> ( ( d + 1 ) ^c -u Z ) e. CC )' % Ad)], 'mulcld', '( %s -> %s e. CC )' % (Ad, BT(PSFA, 'd')))
f3c = w.s([f3v, btc], 'eqeltrd', '( %s -> ( %s ` d ) e. CC )' % (Ad, F3))
f4c = w.s([f4v, w.s([w.s([], 'fzfid', '( %s -> ( 1 ... d ) e. Fin )' % Ad), acd], 'fsumcl', '( %s -> sum_ j e. ( 1 ... d ) %s e. CC )' % (Ad, ATM(PSFA, 'j', 'Z')))], 'eqeltrd',
          '( %s -> ( %s ` d ) e. CC )' % (Ad, F4))
ladd = w.s([nu1, iz, l3, f2ex, l4, f3c, f4c, hval], 'climadd', '( %s -> %s ~~> ( 0 + %s ) )' % (A0, F2, ABSR))
uni = w.s([w.s([l2, ladd], 'jca', '( %s -> ( %s ~~> %s /\\ %s ~~> ( 0 + %s ) ) )' % (A0, F2, DSER, F2, ABSR)), w.inst('climuni')], 'syl',
          '( %s -> %s = ( 0 + %s ) )' % (A0, DSER, ABSR))
abcl_ = w.s([absz, w.inst('abcl')], 'syl', '( %s -> sum_ k e. NN %s e. CC )' % (A0, ATM(PSFA, 'k', 'Z')))
cbv0 = w.s([w.s([w.s([], 'fveq2', '( k = j -> ( %s ` k ) = ( %s ` j ) )' % (PSFA, PSFA)),
                                                                w.s([w.s([], 'oveq1', '( k = j -> ( k ^c -u Z ) = ( j ^c -u Z ) )'),
                                                                     w.s([w.s([], 'oveq1', '( k = j -> ( k + 1 ) = ( j + 1 ) )')], 'oveq1d', '( k = j -> ( ( k + 1 ) ^c -u Z ) = ( ( j + 1 ) ^c -u Z ) )')],
                                                                    'oveq12d', '( k = j -> ( ( k ^c -u Z ) - ( ( k + 1 ) ^c -u Z ) ) = ( ( j ^c -u Z ) - ( ( j + 1 ) ^c -u Z ) ) )')], 'oveq12d',
                                                               '( k = j -> %s = %s )' % (ATM(PSFA, 'k', 'Z'), ATM(PSFA, 'j', 'Z')))], 'cbvsumv',
           'sum_ k e. NN %s = sum_ j e. NN %s' % (ATM(PSFA, 'k', 'Z'), ATM(PSFA, 'j', 'Z')))
abcl2 = w.s([w.s([cbv0], 'a1i', '( %s -> sum_ k e. NN %s = sum_ j e. NN %s )' % (A0, ATM(PSFA, 'k', 'Z'), ATM(PSFA, 'j', 'Z'))), abcl_], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, ABSR))
uni2 = w.s([uni, w.s([abcl2], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (A0, ABSR, ABSR))], 'eqtrd', '( %s -> %s = %s )' % (A0, DSER, ABSR))
# the Abel series with the partial sums written out
Ak = '( %s /\\ k e. NN )' % A0
knn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
pvk = mpv(w, Ak, PSFA, 'k', PSUM('A', 'k'), subq('k'), knn, vexd(w, Ak, PSUM('A', 'k'), 'sum'))
rw = w.s([w.s([w.s([pvk], 'eqcomd', '( %s -> %s = ( %s ` k ) )' % (Ak, PSUM('A', 'k'), PSFA))], 'oveq1d', '( %s -> %s = %s )' % (Ak, ATMS('A', 'k', 'Z'), ATM(PSFA, 'k', 'Z')))],
         'sumeq2dv', '( %s -> sum_ k e. NN %s = sum_ k e. NN %s )' % (A0, ATMS('A', 'k', 'Z'), ATM(PSFA, 'k', 'Z')))
w.qed([w.s([rw, w.s([cbv0], 'a1i', '( %s -> sum_ k e. NN %s = sum_ j e. NN %s )' % (A0, ATM(PSFA, 'k', 'Z'), ATM(PSFA, 'j', 'Z')))], 'eqtrd',
           '( %s -> sum_ k e. NN %s = %s )' % (A0, ATMS('A', 'k', 'Z'), ABSR)), w.s([uni2], 'eqcomd', '( %s -> %s = %s )' % (A0, ABSR, DSER))], 'eqtrd',
      '( %s -> sum_ k e. NN %s = %s )' % (A0, ATMS('A', 'k', 'Z'), DSER))
run5(w)
