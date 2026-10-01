"""C7, Gamma block 3: continuity of Gamma on subsets of the right half-plane
inside lgamgulm's disc (hp0logdm, hp0divp1, lgamtcn, lgamscn, lgamseqv,
lgamcnu, lgamcns, gamcns)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
from cl import Closure, lift
from lin import linarith, lineq, nlinarith

D = LOGDM
J = '( %s |`t S )' % TOP

# ---------------------------------------------------------------- hp0logdm
A0 = 'A e. %s' % HP0
w = W('hp0logdm', 'The open right half-plane lies in the domain of continuity of the logarithm, '
      'the plane slit along the nonpositive reals.')
bi = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( A e. %s <-> ( A e. CC /\\ 0 < ( Re ` A ) ) )' % HP0)], 'a1i',
         '( %s -> ( A e. %s <-> ( A e. CC /\\ 0 < ( Re ` A ) ) ) )' % (A0, HP0))
both = w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), bi], 'mpbid', '( %s -> ( A e. CC /\\ 0 < ( Re ` A ) ) )' % A0)
ac = w.s([both, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
gt = w.s([both, w.inst('simpr')], 'syl', '( %s -> 0 < ( Re ` A ) )' % A0)
Ar = '( %s /\\ A e. RR )' % A0
ar = w.s([], 'simpr', '( %s -> A e. RR )' % Ar)
re = w.s([ar, w.inst('rere')], 'syl', '( %s -> ( Re ` A ) = A )' % Ar)
gt2 = w.s([w.s([gt], 'adantr', '( %s -> 0 < ( Re ` A ) )' % Ar), re], 'breqtrd', '( %s -> 0 < A )' % Ar)
rp = w.s([w.s([ar, gt2], 'elrpd', '( %s -> A e. RR+ )' % Ar)], 'ex', '( %s -> ( A e. RR -> A e. RR+ ) )' % A0)
eld = w.s([w.s([w.s([], 'eqid', '%s = %s' % (D, D))], 'ellogdm', '( A e. %s <-> ( A e. CC /\\ ( A e. RR -> A e. RR+ ) ) )' % D)], 'a1i',
          '( %s -> ( A e. %s <-> ( A e. CC /\\ ( A e. RR -> A e. RR+ ) ) ) )' % (A0, D))
w.qed([w.s([ac, rp], 'jca', '( %s -> ( A e. CC /\\ ( A e. RR -> A e. RR+ ) ) )' % A0), eld], 'mpbird', '( %s -> A e. %s )' % (A0, D))
run7(w)

# ---------------------------------------------------------------- hp0divp1
A0 = '( A e. %s /\\ K e. NN )' % HP0
Q = '( ( A / K ) + 1 )'
w = W('hp0divp1', 'For ` A ` in the open right half-plane and ` K e. NN `, ` ( A / K ) + 1 ` is in the '
      'open right half-plane: the argument of the logarithm in the log-Gamma series.')
ahp = w.s([], 'simpl', '( %s -> A e. %s )' % (A0, HP0))
kn = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
bi = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( A e. %s <-> ( A e. CC /\\ 0 < ( Re ` A ) ) )' % HP0)], 'a1i',
         '( %s -> ( A e. %s <-> ( A e. CC /\\ 0 < ( Re ` A ) ) ) )' % (A0, HP0))
both = w.s([ahp, bi], 'mpbid', '( %s -> ( A e. CC /\\ 0 < ( Re ` A ) ) )' % A0)
ac = w.s([both, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
gt = w.s([both, w.inst('simpr')], 'syl', '( %s -> 0 < ( Re ` A ) )' % A0)
kr = w.s([kn], 'nnred', '( %s -> K e. RR )' % A0); kne = w.s([kn], 'nnne0d', '( %s -> K =/= 0 )' % A0); kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
akc = w.s([ac, kc, kne], 'divcld', '( %s -> ( A / K ) e. CC )' % A0)
qc = w.s([akc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'addcld', '( %s -> %s e. CC )' % (A0, Q))
re1 = w.s([ac, kr, kne, w.inst('rediv')], 'syl3anc', '( %s -> ( Re ` ( A / K ) ) = ( ( Re ` A ) / K ) )' % A0)
re2 = w.s([w.s([akc, a1(w, A0, 'ax-1cn', '1 e. CC'), w.inst('readd')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( Re ` ( A / K ) ) + ( Re ` 1 ) ) )' % (A0, Q)),
           w.s([re1, a1(w, A0, 're1', '( Re ` 1 ) = 1')], 'oveq12d', '( %s -> ( ( Re ` ( A / K ) ) + ( Re ` 1 ) ) = ( ( ( Re ` A ) / K ) + 1 ) )' % A0)], 'eqtrd',
          '( %s -> ( Re ` %s ) = ( ( ( Re ` A ) / K ) + 1 ) )' % (A0, Q))
rar = w.s([ac], 'recld', '( %s -> ( Re ` A ) e. RR )' % A0)
dg = w.s([rar, kr, gt, w.s([kn], 'nngt0d', '( %s -> 0 < K )' % A0)], 'divgt0d', '( %s -> 0 < ( ( Re ` A ) / K ) )' % A0)
cl = Closure(w, A0, {})
cl.leaf('( ( Re ` A ) / K )', 'RR', w.s([rar, kr, kne], 'redivcld', '( %s -> ( ( Re ` A ) / K ) e. RR )' % A0))
pos = linarith(w, A0, [dg], '0 < ( ( ( Re ` A ) / K ) + 1 )', closure=cl)
pos2 = w.s([pos, re2], 'breqtrrd', '( %s -> 0 < ( Re ` %s ) )' % (A0, Q))
bi2 = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (Q, HP0, Q, Q))], 'a1i',
          '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (A0, Q, HP0, Q, Q))
w.qed([w.s([qc, pos2], 'jca', '( %s -> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (A0, Q, Q)), bi2], 'mpbird', '( %s -> %s e. %s )' % (A0, Q, HP0))
run7(w)

# ---------------------------------------------------------------- lgamtcn
A0 = '( S C_ %s /\\ K e. NN )' % HP0
LK = '( log ` ( ( K + 1 ) / K ) )'
QZ = '( ( z / K ) + 1 )'
w = W('lgamtcn', 'Each term of the log-Gamma series is continuous on a subset of the open right '
      'half-plane.')
sshp = w.s([], 'simpl', '( %s -> S C_ %s )' % (A0, HP0))
kn = w.s([], 'simpr', '( %s -> K e. NN )' % A0)
ssc = w.s([sshp, hp0cc(w, A0)], 'sstrd', '( %s -> S C_ CC )' % A0)
sscc = a1(w, A0, 'ssid', 'CC C_ CC')
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
idc = w.s([ssc, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( z e. S |-> z ) e. ( S -cn-> CC ) )' % A0)
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
lkc = w.s([w.s([w.s([w.s([w.s([kn], 'peano2nnd', '( %s -> ( K + 1 ) e. NN )' % A0)], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0), krp], 'rpdivcld', '( %s -> ( ( K + 1 ) / K ) e. RR+ )' % A0), w.inst('relogcl')], 'syl',
               '( %s -> %s e. RR )' % (A0, LK))], 'recnd', '( %s -> %s e. CC )' % (A0, LK))
lkm = w.s([lkc, ssc, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. S |-> %s ) e. ( S -cn-> CC ) )' % (A0, LK))
mul1 = w.s([idc, lkm], 'mulcncf', '( %s -> ( z e. S |-> ( z x. %s ) ) e. ( S -cn-> CC ) )' % (A0, LK))
# z / K
FK = '( x e. CC |-> ( x / K ) )'
kc = w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A0); kne = w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)
fkcn = w.s([kc, kne, w.s([w.s([], 'eqid', '%s = %s' % (FK, FK))], 'divccncf', '( ( K e. CC /\\ K =/= 0 ) -> %s e. ( CC -cn-> CC ) )' % FK)], 'syl2anc', '( %s -> %s e. ( CC -cn-> CC ) )' % (A0, FK))
dm1 = w.s([fkcn, idc], 'cncfmpt1f', '( %s -> ( z e. S |-> ( %s ` z ) ) e. ( S -cn-> CC ) )' % (A0, FK))
Az = '( %s /\\ z e. S )' % A0
zs = w.s([], 'simpr', '( %s -> z e. S )' % Az)
zhp = w.s([w.s([sshp], 'adantr', '( %s -> S C_ %s )' % (Az, HP0)), zs], 'sseldd', '( %s -> z e. %s )' % (Az, HP0))
zf = hp0facts(w, Az, zhp, 'z')
fkv = w.s([zf['zc'], w.s([w.s([], 'oveq1', '( x = z -> ( x / K ) = ( z / K ) )'), w.s([], 'eqid', '%s = %s' % (FK, FK)), w.s([], 'ovex', '( z / K ) e. _V')], 'fvmpt', '( z e. CC -> ( %s ` z ) = ( z / K ) )' % FK)], 'syl',
          '( %s -> ( %s ` z ) = ( z / K ) )' % (Az, FK))
dm2 = w.s([w.s([fkv], 'mpteq2dva', '( %s -> ( z e. S |-> ( %s ` z ) ) = ( z e. S |-> ( z / K ) ) )' % (A0, FK)), dm1], 'eqeltrrd', '( %s -> ( z e. S |-> ( z / K ) ) e. ( S -cn-> CC ) )' % A0)
one = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), ssc, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. S |-> 1 ) e. ( S -cn-> CC ) )' % A0)
adc = w.s([w.s([keq], 'addcn', '+ e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> + e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
qm = w.s([keq, adc, dm2, one], 'cncfmpt2f', '( %s -> ( z e. S |-> %s ) e. ( S -cn-> CC ) )' % (A0, QZ))
qd = hp0facts(w, Az, w.s([zhp, w.s([kn], 'adantr', '( %s -> K e. NN )' % Az), w.inst('hp0divp1')], 'syl2anc', '( %s -> %s e. %s )' % (Az, QZ, HP0)), QZ)['ld']
lg = logmapcn(w, A0, 'S', sshp, qm, QZ, qd)
sbc = w.s([w.s([keq], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
w.qed([keq, sbc, mul1, lg], 'cncfmpt2f', '( %s -> ( z e. S |-> %s ) e. ( S -cn-> CC ) )' % (A0, TERM('K', 'z')))
run7(w)

# ---------------------------------------------------------------- lgamscn
A0 = '( S C_ %s /\\ N e. NN )' % HP0
SUMN = 'sum_ k e. ( 1 ... N ) %s' % TERM('k', 'z')
w = W('lgamscn', 'Each partial sum of the log-Gamma series is continuous on a subset of the open '
      'right half-plane ( ~ fsumcn ).')
sshp = w.s([], 'simpl', '( %s -> S C_ %s )' % (A0, HP0))
ssc = w.s([sshp, hp0cc(w, A0)], 'sstrd', '( %s -> S C_ CC )' % A0)
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
jeq = w.s([], 'eqid', '%s = %s' % (J, J))
ton = w.s([w.s([keq], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOP)], 'a1i', '( %s -> %s e. ( TopOn ` CC ) )' % (A0, TOP))
jon = w.s([ton, ssc, w.inst('resttopon')], 'syl2anc', '( %s -> %s e. ( TopOn ` S ) )' % (A0, J))
# ( S -cn-> CC ) = ( J Cn TOP )
rid = w.s([w.s([w.s([keq], 'cnfldtop', '%s e. Top' % TOP), w.s([w.s([], 'unicntop', 'CC = U. %s' % TOP)], 'restid', '( %s e. Top -> ( %s |`t CC ) = %s )' % (TOP, TOP, TOP))], 'ax-mp', '( %s |`t CC ) = %s' % (TOP, TOP))], 'oveq2i',
          '( %s Cn ( %s |`t CC ) ) = ( %s Cn %s )' % (J, TOP, J, TOP))
cni = w.s([keq, jeq, w.s([], 'eqid', '( %s |`t CC ) = ( %s |`t CC )' % (TOP, TOP))], 'cncfcn', '( ( S C_ CC /\\ CC C_ CC ) -> ( S -cn-> CC ) = ( %s Cn ( %s |`t CC ) ) )' % (J, TOP))
cnc = w.s([w.s([ssc, a1(w, A0, 'ssid', 'CC C_ CC'), cni], 'syl2anc', '( %s -> ( S -cn-> CC ) = ( %s Cn ( %s |`t CC ) ) )' % (A0, J, TOP)), w.s([rid], 'a1i', '( %s -> ( %s Cn ( %s |`t CC ) ) = ( %s Cn %s ) )' % (A0, J, TOP, J, TOP))], 'eqtrd',
          '( %s -> ( S -cn-> CC ) = ( %s Cn %s ) )' % (A0, J, TOP))
Ak = '( %s /\\ k e. ( 1 ... N ) )' % A0
kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % Ak), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ak)
tk = w.s([w.s([w.s([sshp], 'adantr', '( %s -> S C_ %s )' % (Ak, HP0)), kn], 'jca', '( %s -> ( S C_ %s /\\ k e. NN ) )' % (Ak, HP0)), w.inst('lgamtcn')], 'syl', '( %s -> ( z e. S |-> %s ) e. ( S -cn-> CC ) )' % (Ak, TERM('k', 'z')))
tk2 = w.s([tk, w.s([cnc], 'adantr', '( %s -> ( S -cn-> CC ) = ( %s Cn %s ) )' % (Ak, J, TOP))], 'eleqtrd', '( %s -> ( z e. S |-> %s ) e. ( %s Cn %s ) )' % (Ak, TERM('k', 'z'), J, TOP))
fs = w.s([keq, jon, w.s([], 'fzfid', '( %s -> ( 1 ... N ) e. Fin )' % A0), tk2], 'fsumcn', '( %s -> ( z e. S |-> %s ) e. ( %s Cn %s ) )' % (A0, SUMN, J, TOP))
w.qed([fs, cnc], 'eleqtrrd', '( %s -> ( z e. S |-> %s ) e. ( S -cn-> CC ) )' % (A0, SUMN))
run7(w)

# ---------------------------------------------------------------- lgamseqv
A0 = '( ( R e. NN /\\ N e. NN ) /\\ ( S C_ %s /\\ S C_ %s ) )' % (UR(), HP0)
SQ = 'seq 1 ( oF + , %s )' % GR()
FM = '( m e. NN |-> %s )' % TERM('m', 'z')
INNER = '( seq 1 ( + , %s ) ` N )' % FM
w = W('lgamseqv', 'The ` N `-th partial sum of the log-Gamma series, restricted to a subset of the '
      'right half-plane inside lgamgulm\'s disc, is the mapping to the finite sum ( ~ seqof2 , '
      '~ fsumser ).')
rn = w.s([], 'simpll', '( %s -> R e. NN )' % A0)
nn = w.s([], 'simplr', '( %s -> N e. NN )' % A0)
ssu = w.s([], 'simprl', '( %s -> S C_ %s )' % (A0, UR()))
sshp = w.s([], 'simprr', '( %s -> S C_ %s )' % (A0, HP0))
uex = w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'rabex', '%s e. _V' % UR())], 'a1i', '( %s -> %s e. _V )' % (A0, UR()))
nuz = w.s([nn, w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> N e. ( ZZ>= ` 1 ) )' % A0)
fzss = a1(w, A0, 'fz1ssnn', '( 1 ... N ) C_ NN')
Amz = '( %s /\\ ( m e. NN /\\ z e. %s ) )' % (A0, UR())
tv = w.s([w.s([], 'ovex', '%s e. _V' % TERM('m', 'z'))], 'a1i', '( %s -> %s e. _V )' % (Amz, TERM('m', 'z')))
so = w.s([uex, nuz, fzss, tv], 'seqof2', '( %s -> ( %s ` N ) = ( z e. %s |-> %s ) )' % (A0, SQ, UR(), INNER))
res = w.s([w.s([so], 'reseq1d', '( %s -> ( ( %s ` N ) |` S ) = ( ( z e. %s |-> %s ) |` S ) )' % (A0, SQ, UR(), INNER)), w.s([ssu, w.inst('resmpt')], 'syl', '( %s -> ( ( z e. %s |-> %s ) |` S ) = ( z e. S |-> %s ) )' % (A0, UR(), INNER, INNER))], 'eqtrd',
          '( %s -> ( ( %s ` N ) |` S ) = ( z e. S |-> %s ) )' % (A0, SQ, INNER))
Az = '( %s /\\ z e. S )' % A0
zhp = w.s([w.s([sshp], 'adantr', '( %s -> S C_ %s )' % (Az, HP0)), w.s([], 'simpr', '( %s -> z e. S )' % Az)], 'sseldd', '( %s -> z e. %s )' % (Az, HP0))
Azk = '( %s /\\ k e. ( 1 ... N ) )' % Az
kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % Azk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Azk)
fv = mpv(w, Azk, FM, 'k', TERM('k', 'z'), termsub(w, 'k', 'z'), kn, vexd(w, Azk, TERM('k', 'z')))
tc = termcl(w, Azk, 'k', 'z', w.s([zhp], 'adantr', '( %s -> z e. %s )' % (Azk, HP0)), kn)
fss = w.s([fv, w.s([nuz], 'adantr', '( %s -> N e. ( ZZ>= ` 1 ) )' % Az), tc], 'fsumser', '( %s -> sum_ k e. ( 1 ... N ) %s = %s )' % (Az, TERM('k', 'z'), INNER))
w.qed([res, w.s([w.s([fss], 'eqcomd', '( %s -> %s = sum_ k e. ( 1 ... N ) %s )' % (Az, INNER, TERM('k', 'z')))], 'mpteq2dva', '( %s -> ( z e. S |-> %s ) = ( z e. S |-> sum_ k e. ( 1 ... N ) %s ) )' % (A0, INNER, TERM('k', 'z')))], 'eqtrd',
      '( %s -> ( ( %s ` N ) |` S ) = ( z e. S |-> sum_ k e. ( 1 ... N ) %s ) )' % (A0, SQ, TERM('k', 'z')))
run7(w)

# ---------------------------------------------------------------- lgamcnu
# deduction form: the disc U is a class variable fixed by a $e hypothesis, as in
# set.mm's lgamgulm2/lgambdd, so that the antecedent never spells the disc out
# (lgamgulm2 has $d ph x on the disc's bound variable).
P = 'ph'
GRU = '( m e. NN |-> ( z e. U |-> %s ) )' % TERM('m', 'z')
SQU = 'seq 1 ( oF + , %s )' % GRU
SQ = 'seq 1 ( oF + , %s )' % GR()
GFB = '( ( log_G ` z ) + ( log ` z ) )'
GF = '( z e. U |-> %s )' % GFB
GS = '( z e. S |-> %s )' % GFB


def hyps4(w, name):
    hyp(w, '1', name + '.r', '( ph -> R e. NN )')
    hyp(w, '2', name + '.u', 'U = %s' % UR())
    hyp(w, '3', name + '.s', '( ph -> S C_ U )')
    hyp(w, '4', name + '.h', '( ph -> S C_ %s )' % HP0)


w = W('lgamcnu', 'The function ` log_G + log ` is continuous on a subset of the open right '
      'half-plane inside lgamgulm\'s disc ` U `: the uniform limit ( ~ lgamgulm2 ) of the continuous '
      'partial sums ( ~ lgamscn ), restricted by ~ ulmss and passed to the limit by ~ ulmcn .')
hyps4(w, 'lgamcnu')
rn, ueq, ssu, sshp = '1', '2', '3', '4'
ssur = w.s([ssu, w.s([ueq], 'a1i', '( ph -> U = %s )' % UR())], 'sseqtrd', '( ph -> S C_ %s )' % UR())
g2 = w.s([w.s([rn, ueq, w.s([], 'eqid', '%s = %s' % (GRU, GRU))], 'lgamgulm2', '( ph -> ( A. z e. U ( log_G ` z ) e. CC /\\ %s ( ~~>u ` U ) %s ) )' % (SQU, GF)), w.inst('simpr')], 'syl',
          '( ph -> %s ( ~~>u ` U ) %s )' % (SQU, GF))
fn = w.s([w.s([w.s([w.s([], '1z', '1 e. ZZ'), w.inst('seqfn')], 'ax-mp', '%s Fn ( ZZ>= ` 1 )' % SQU), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'fneq2i', '( %s Fn ( ZZ>= ` 1 ) <-> %s Fn NN )' % (SQU, SQU))], 'mpbi', '%s Fn NN' % SQU)], 'a1i',
         '( ph -> %s Fn NN )' % SQU)
ff = w.s([fn, g2, w.inst('ulmf2')], 'syl2anc', '( ph -> %s : NN --> ( CC ^m U ) )' % SQU)
fm = w.s([ff], 'feqmptd', '( ph -> %s = ( o e. NN |-> ( %s ` o ) ) )' % (SQU, SQU))
g3 = w.s([g2, w.s([fm], 'breq1d', '( ph -> ( %s ( ~~>u ` U ) %s <-> ( o e. NN |-> ( %s ` o ) ) ( ~~>u ` U ) %s ) )' % (SQU, GF, SQU, GF))], 'mpbid',
          '( ph -> ( o e. NN |-> ( %s ` o ) ) ( ~~>u ` U ) %s )' % (SQU, GF))
Ax = '( ph /\\ o e. NN )'
nz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
ul = w.s([nz, ssu, w.s([], 'fvexd', '( %s -> ( %s ` o ) e. _V )' % (Ax, SQU)), g3], 'ulmss', '( ph -> ( o e. NN |-> ( ( %s ` o ) |` S ) ) ( ~~>u ` S ) ( %s |` S ) )' % (SQU, GF))
ul2 = w.s([ul, w.s([ssu, w.inst('resmpt')], 'syl', '( ph -> ( %s |` S ) = %s )' % (GF, GS))], 'breqtrd', '( ph -> ( o e. NN |-> ( ( %s ` o ) |` S ) ) ( ~~>u ` S ) %s )' % (SQU, GS))
xn = w.s([], 'simpr', '( %s -> o e. NN )' % Ax)
hyp_ = w.s([w.s([w.s([rn], 'adantr', '( %s -> R e. NN )' % Ax), xn], 'jca', '( %s -> ( R e. NN /\\ o e. NN ) )' % Ax), w.s([w.s([ssur, sshp], 'jca', '( ph -> ( S C_ %s /\\ S C_ %s ) )' % (UR(), HP0))], 'adantr', '( %s -> ( S C_ %s /\\ S C_ %s ) )' % (Ax, UR(), HP0))], 'jca',
           '( %s -> ( ( R e. NN /\\ o e. NN ) /\\ ( S C_ %s /\\ S C_ %s ) ) )' % (Ax, UR(), HP0))
SUMX = 'sum_ k e. ( 1 ... o ) %s' % TERM('k', 'z')
sv = w.s([hyp_, w.inst('lgamseqv')], 'syl', '( %s -> ( ( %s ` o ) |` S ) = ( z e. S |-> %s ) )' % (Ax, SQ, SUMX))
# SQU = SQ from U = UR
sqe = w.s([w.s([w.s([w.s([ueq, w.inst('mpteq1')], 'ax-mp', '( z e. U |-> %s ) = ( z e. %s |-> %s )' % (TERM('m', 'z'), UR(), TERM('m', 'z')))], 'mpteq2i', '%s = %s' % (GRU, GR())), w.inst('seqeq3')], 'ax-mp', '%s = %s' % (SQU, SQ))], 'a1i', '( %s -> %s = %s )' % (Ax, SQU, SQ))
sv2 = w.s([w.s([w.s([sqe], 'fveq1d', '( %s -> ( %s ` o ) = ( %s ` o ) )' % (Ax, SQU, SQ))], 'reseq1d', '( %s -> ( ( %s ` o ) |` S ) = ( ( %s ` o ) |` S ) )' % (Ax, SQU, SQ)), sv], 'eqtrd',
           '( %s -> ( ( %s ` o ) |` S ) = ( z e. S |-> %s ) )' % (Ax, SQU, SUMX))
scn = w.s([w.s([w.s([sshp], 'adantr', '( %s -> S C_ %s )' % (Ax, HP0)), xn], 'jca', '( %s -> ( S C_ %s /\\ o e. NN ) )' % (Ax, HP0)), w.inst('lgamscn')], 'syl', '( %s -> ( z e. S |-> %s ) e. ( S -cn-> CC ) )' % (Ax, SUMX))
fcn = w.s([sv2, scn], 'eqeltrd', '( %s -> ( ( %s ` o ) |` S ) e. ( S -cn-> CC ) )' % (Ax, SQU))
FX = '( o e. NN |-> ( ( %s ` o ) |` S ) )' % SQU
fmap = w.s([fcn, w.s([], 'eqid', '%s = %s' % (FX, FX))], 'fmptd', '( ph -> %s : NN --> ( S -cn-> CC ) )' % FX)
w.qed([nz, a1(w, P, '1z', '1 e. ZZ'), fmap, ul2], 'ulmcn', '( ph -> %s e. ( S -cn-> CC ) )' % GS)
run7(w, h=True)

# ---------------------------------------------------------------- lgamcns
w = W('lgamcns', 'The log-Gamma function is continuous on a subset of the open right half-plane '
      'inside lgamgulm\'s disc ( ~ lgamcnu minus the continuous logarithm).')
hyps4(w, 'lgamcns')
rn, ueq, ssu, sshp = '1', '2', '3', '4'
ssc = w.s([sshp, hp0cc(w, P)], 'sstrd', '( ph -> S C_ CC )')
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
idc = w.s([ssc, a1(w, P, 'ssid', 'CC C_ CC'), w.inst('cncfmptid')], 'syl2anc', '( ph -> ( z e. S |-> z ) e. ( S -cn-> CC ) )')
Az = '( ph /\\ z e. S )'
zhp = w.s([w.s([sshp], 'adantr', '( %s -> S C_ %s )' % (Az, HP0)), w.s([], 'simpr', '( %s -> z e. S )' % Az)], 'sseldd', '( %s -> z e. %s )' % (Az, HP0))
zf = hp0facts(w, Az, zhp, 'z')
lg = logmapcn(w, P, 'S', sshp, idc, 'z', zf['ld'])
gu = w.s([rn, ueq, ssu, sshp], 'lgamcnu', '( ph -> %s e. ( S -cn-> CC ) )' % GS)
sbc = w.s([w.s([keq], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( ph -> - e. ( ( %s tX %s ) Cn %s ) )' % (TOP, TOP, TOP))
dif = w.s([keq, sbc, gu, lg], 'cncfmpt2f', '( ph -> ( z e. S |-> ( %s - ( log ` z ) ) ) e. ( S -cn-> CC ) )' % GFB)
lgc = w.s([zf['dm'], w.inst('lgamcl')], 'syl', '( %s -> ( log_G ` z ) e. CC )' % Az)
lc = w.s([zf['zc'], zf['ne0'], w.inst('logcl')], 'syl2anc', '( %s -> ( log ` z ) e. CC )' % Az)
pc = w.s([lgc, lc], 'pncand', '( %s -> ( %s - ( log ` z ) ) = ( log_G ` z ) )' % (Az, GFB))
w.qed([w.s([pc], 'mpteq2dva', '( ph -> ( z e. S |-> ( %s - ( log ` z ) ) ) = ( z e. S |-> ( log_G ` z ) ) )' % GFB), dif], 'eqeltrrd', '( ph -> ( z e. S |-> ( log_G ` z ) ) e. ( S -cn-> CC ) )')
run7(w, h=True)

# ---------------------------------------------------------------- gamcns
w = W('gamcns', 'The Gamma function is continuous on a subset of the open right half-plane inside '
      'lgamgulm\'s disc: ` exp o. log_G ` ( ~ eflgam , ~ lgamcns ).')
hyps4(w, 'gamcns')
rn, ueq, ssu, sshp = '1', '2', '3', '4'
efc = a1(w, P, 'efcn', 'exp e. ( CC -cn-> CC )')
lg = w.s([rn, ueq, ssu, sshp], 'lgamcns', '( ph -> ( z e. S |-> ( log_G ` z ) ) e. ( S -cn-> CC ) )')
cmp = w.s([efc, lg], 'cncfmpt1f', '( ph -> ( z e. S |-> ( exp ` ( log_G ` z ) ) ) e. ( S -cn-> CC ) )')
Az = '( ph /\\ z e. S )'
zhp = w.s([w.s([sshp], 'adantr', '( %s -> S C_ %s )' % (Az, HP0)), w.s([], 'simpr', '( %s -> z e. S )' % Az)], 'sseldd', '( %s -> z e. %s )' % (Az, HP0))
zf = hp0facts(w, Az, zhp, 'z')
ef = w.s([zf['dm'], w.inst('eflgam')], 'syl', '( %s -> ( exp ` ( log_G ` z ) ) = ( _G ` z ) )' % Az)
w.qed([w.s([ef], 'mpteq2dva', '( ph -> ( z e. S |-> ( exp ` ( log_G ` z ) ) ) = ( z e. S |-> ( _G ` z ) ) )'), cmp], 'eqeltrrd', '( ph -> ( z e. S |-> ( _G ` z ) ) e. ( S -cn-> CC ) )')
run7(w, h=True)
