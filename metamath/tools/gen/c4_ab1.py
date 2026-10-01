"""C4, Abel block 1: the partial-summation identity."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import num


def PS(k):
    return 'sum_ i e. ( 1 ... %s ) ( A ` i )' % k


def CP(k):
    return '( %s ^c -u Z )' % k


def TRM(k):
    return '( ( A ` %s ) x. %s )' % (k, CP(k))


AF = '( A : NN --> CC /\\ Z e. CC /\\ N e. NN )'

# ---------------------------------------------------------------- abelpd
w = W('abelpd', 'A partial sum grows by the next coefficient ( ~ fsump1 ).')
A0 = '( A : NN --> CC /\\ J e. NN )'
af = w.s([], 'simpl', '( %s -> A : NN --> CC )' % A0)
jn = w.s([], 'simpr', '( %s -> J e. NN )' % A0)
juz = w.s([jn, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % A0)],
          'eleqtrd', '( %s -> J e. ( ZZ>= ` 1 ) )' % A0)
AI = '( %s /\\ i e. ( 1 ... ( J + 1 ) ) )' % A0
icl = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % AI),
           w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... ( J + 1 ) ) )' % AI), w.inst('elfznn')], 'syl',
               '( %s -> i e. NN )' % AI)], 'ffvelcdmd', '( %s -> ( A ` i ) e. CC )' % AI)
sub = w.s([], 'fveq2', '( i = ( J + 1 ) -> ( A ` i ) = ( A ` ( J + 1 ) ) )')
p1 = w.s([juz, icl, sub], 'fsump1', '( %s -> %s = ( %s + ( A ` ( J + 1 ) ) ) )' % (A0, PS('( J + 1 )'), PS('J')))
AJ = '( %s /\\ i e. ( 1 ... J ) )' % A0
jcl = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % AJ),
           w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... J ) )' % AJ), w.inst('elfznn')], 'syl',
               '( %s -> i e. NN )' % AJ)], 'ffvelcdmd', '( %s -> ( A ` i ) e. CC )' % AJ)
fin = w.s([], 'fzfid', '( %s -> ( 1 ... J ) e. Fin )' % A0)
scl = w.s([fin, jcl], 'fsumcl', '( %s -> %s e. CC )' % (A0, PS('J')))
j1n = w.s([jn, w.inst('peano2nn')], 'syl', '( %s -> ( J + 1 ) e. NN )' % A0)
acl = w.s([af, j1n], 'ffvelcdmd', '( %s -> ( A ` ( J + 1 ) ) e. CC )' % A0)
w.qed([w.s([p1], 'oveq1d', '( %s -> ( %s - %s ) = ( ( %s + ( A ` ( J + 1 ) ) ) - %s ) )' % (A0, PS('( J + 1 )'), PS('J'), PS('J'), PS('J'))),
       w.s([acl, scl], 'pncan2d', '( %s -> ( ( %s + ( A ` ( J + 1 ) ) ) - %s ) = ( A ` ( J + 1 ) ) )' % (A0, PS('J'), PS('J')))],
      'eqtrd', '( %s -> ( %s - %s ) = ( A ` ( J + 1 ) ) )' % (A0, PS('( J + 1 )'), PS('J')))
run4(w)

# ---------------------------------------------------------------- abelrx
w = W('abelrx', 'Reindexing the shifted Dirichlet-series sum: the terms at '
      '` j + 1 ` over ` ( 1 ..^ N ) ` are the terms at ` k ` over ` ( 2 ... N ) `.')
af = w.s([], 'simp1', '( %s -> A : NN --> CC )' % AF)
zc = w.s([], 'simp2', '( %s -> Z e. CC )' % AF)
nn = w.s([], 'simp3', '( %s -> N e. NN )' % AF)
nz = w.s([nn, w.inst('nnz')], 'syl', '( %s -> N e. ZZ )' % AF)
z1 = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % AF)
nm1 = w.s([nz, z1], 'zsubcld', '( %s -> ( N - 1 ) e. ZZ )' % AF)
fzo = w.s([nz, w.inst('fzoval')], 'syl', '( %s -> ( 1 ..^ N ) = ( 1 ... ( N - 1 ) ) )' % AF)
LHS = 'sum_ j e. ( 1 ..^ N ) ( ( A ` ( j + 1 ) ) x. ( ( j + 1 ) ^c -u Z ) )'
MID = 'sum_ j e. ( 1 ... ( N - 1 ) ) ( ( A ` ( j + 1 ) ) x. ( ( j + 1 ) ^c -u Z ) )'
e1 = w.s([fzo], 'sumeq1d', '( %s -> %s = %s )' % (AF, LHS, MID))
# the closure of the shifted term
AJ = '( %s /\\ j e. ( 1 ... ( N - 1 ) ) )' % AF
jfz = w.s([], 'simpr', '( %s -> j e. ( 1 ... ( N - 1 ) ) )' % AJ)
jn = w.s([jfz, w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % AJ)
j1n = w.s([jn, w.inst('peano2nn')], 'syl', '( %s -> ( j + 1 ) e. NN )' % AJ)
acl = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % AJ), j1n], 'ffvelcdmd',
          '( %s -> ( A ` ( j + 1 ) ) e. CC )' % AJ)
j1c = w.s([w.s([j1n], 'nnrpd', '( %s -> ( j + 1 ) e. RR+ )' % AJ)], 'rpcnd', '( %s -> ( j + 1 ) e. CC )' % AJ)
nzc = w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % AJ)], 'negcld', '( %s -> -u Z e. CC )' % AJ)
ccl = w.s([j1c, nzc], 'cxpcld', '( %s -> ( ( j + 1 ) ^c -u Z ) e. CC )' % AJ)
tcl = w.s([acl, ccl], 'mulcld', '( %s -> ( ( A ` ( j + 1 ) ) x. ( ( j + 1 ) ^c -u Z ) ) e. CC )' % AJ)
# the shift
KB = '( ( A ` ( ( k - 1 ) + 1 ) ) x. ( ( ( k - 1 ) + 1 ) ^c -u Z ) )'
sub = w.s([w.s([w.s([], 'oveq1', '( j = ( k - 1 ) -> ( j + 1 ) = ( ( k - 1 ) + 1 ) )')], 'fveq2d',
               '( j = ( k - 1 ) -> ( A ` ( j + 1 ) ) = ( A ` ( ( k - 1 ) + 1 ) ) )'),
           w.s([w.s([], 'oveq1', '( j = ( k - 1 ) -> ( j + 1 ) = ( ( k - 1 ) + 1 ) )')], 'oveq1d',
               '( j = ( k - 1 ) -> ( ( j + 1 ) ^c -u Z ) = ( ( ( k - 1 ) + 1 ) ^c -u Z ) )')],
          'oveq12d', '( j = ( k - 1 ) -> ( ( A ` ( j + 1 ) ) x. ( ( j + 1 ) ^c -u Z ) ) = %s )' % KB)
sh = w.s([z1, z1, nm1, tcl, sub], 'fsumshft',
         '( %s -> %s = sum_ k e. ( ( 1 + 1 ) ... ( ( N - 1 ) + 1 ) ) %s )' % (AF, MID, KB))
# the range
r1 = w.s([w.s([num.add_nat(w, 1, 1)], 'a1i', '( %s -> ( 1 + 1 ) = 2 )' % AF),
          w.s([w.s([nz], 'zcnd', '( %s -> N e. CC )' % AF),
               w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % AF)], 'npcand',
              '( %s -> ( ( N - 1 ) + 1 ) = N )' % AF)], 'oveq12d',
         '( %s -> ( ( 1 + 1 ) ... ( ( N - 1 ) + 1 ) ) = ( 2 ... N ) )' % AF)
e2 = w.s([r1], 'sumeq1d', '( %s -> sum_ k e. ( ( 1 + 1 ) ... ( ( N - 1 ) + 1 ) ) %s = sum_ k e. ( 2 ... N ) %s )' % (AF, KB, KB))
# ( ( k - 1 ) + 1 ) = k on the range
AK = '( %s /\\ k e. ( 2 ... N ) )' % AF
kc = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> k e. ( 2 ... N ) )' % AK), w.inst('elfzelz')], 'syl',
                   '( %s -> k e. ZZ )' % AK)], 'zred', '( %s -> k e. RR )' % AK)], 'recnd',
         '( %s -> k e. CC )' % AK)
kk = w.s([kc, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % AK)], 'npcand',
         '( %s -> ( ( k - 1 ) + 1 ) = k )' % AK)
bd = w.s([w.s([kk], 'fveq2d', '( %s -> ( A ` ( ( k - 1 ) + 1 ) ) = ( A ` k ) )' % AK),
          w.s([kk], 'oveq1d', '( %s -> ( ( ( k - 1 ) + 1 ) ^c -u Z ) = ( k ^c -u Z ) )' % AK)], 'oveq12d',
         '( %s -> %s = %s )' % (AK, KB, TRM('k')))
e3 = w.s([bd], 'sumeq2dv', '( %s -> sum_ k e. ( 2 ... N ) %s = sum_ k e. ( 2 ... N ) %s )' % (AF, KB, TRM('k')))
w.qed([w.s([w.s([e1, sh], 'eqtrd', '( %s -> %s = sum_ k e. ( ( 1 + 1 ) ... ( ( N - 1 ) + 1 ) ) %s )' % (AF, LHS, KB)),
            e2], 'eqtrd', '( %s -> %s = sum_ k e. ( 2 ... N ) %s )' % (AF, LHS, KB)), e3], 'eqtrd',
      '( %s -> %s = sum_ k e. ( 2 ... N ) %s )' % (AF, LHS, TRM('k')))
run4(w)

# ---------------------------------------------------------------- abelid
def ATM(j):
    return '( %s x. ( %s - %s ) )' % (PS(j), CP(j), CP('( %s + 1 )' % j))


W1 = '( %s x. %s )' % (PS('N'), CP('N'))
A1 = '( A ` 1 )'
R2 = 'sum_ k e. ( 2 ... N ) %s' % TRM('k')
LS = 'sum_ j e. ( 1 ..^ N ) ( %s x. ( %s - %s ) )' % (PS('j'), CP('( j + 1 )'), CP('j'))
RS = 'sum_ j e. ( 1 ..^ N ) ( ( %s - %s ) x. %s )' % (PS('( j + 1 )'), PS('j'), CP('( j + 1 )'))
AS = 'sum_ j e. ( 1 ..^ N ) %s' % ATM('j')
w = W('abelid0', 'The raw output of ~ fsumparts for a Dirichlet-series partial '
      'sum: the sum of ` ( A ` k ) k ^c -u Z ` over ` ( 1 ... N ) ` is the boundary '
      'term plus the sum of the partial sums against the differences of ` k ^c -u Z '
      '` ( ~ fsumparts ).')
af = w.s([], 'simp1', '( %s -> A : NN --> CC )' % AF)
zc = w.s([], 'simp2', '( %s -> Z e. CC )' % AF)
nn = w.s([], 'simp3', '( %s -> N e. NN )' % AF)
nuz = w.s([nn, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % AF)],
          'eleqtrd', '( %s -> N e. ( ZZ>= ` 1 ) )' % AF)
nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % AF)


def fzcl(ante, idx, mem):
    """steps for PS(idx) e. CC and CP(idx) e. CC under ante with mem: ( ante -> idx e. NN )"""
    AI = '( %s /\\ i e. ( 1 ... %s ) )' % (ante, idx)
    afa = af if ante == AF else w.s([af], 'adantr', '( %s -> A : NN --> CC )' % ante)
    icl = w.s([w.s([afa], 'adantr', '( %s -> A : NN --> CC )' % AI),
               w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (AI, idx)), w.inst('elfznn')], 'syl',
                   '( %s -> i e. NN )' % AI)], 'ffvelcdmd', '( %s -> ( A ` i ) e. CC )' % AI)
    fin = w.s([], 'fzfid', '( %s -> ( 1 ... %s ) e. Fin )' % (ante, idx))
    ps = w.s([fin, icl], 'fsumcl', '( %s -> %s e. CC )' % (ante, PS(idx)))
    xc = w.s([w.s([mem], 'nnrpd', '( %s -> %s e. RR+ )' % (ante, idx))], 'rpcnd', '( %s -> %s e. CC )' % (ante, idx))
    zca = zc if ante == AF else w.s([zc], 'adantr', '( %s -> Z e. CC )' % ante)
    cp = w.s([xc, w.s([zca], 'negcld', '( %s -> -u Z e. CC )' % ante)],
             'cxpcld', '( %s -> %s e. CC )' % (ante, CP(idx)))
    return ps, cp


AKF = '( %s /\\ k e. ( 1 ... N ) )' % AF
kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % AKF), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % AKF)
psk, cpk = fzcl(AKF, 'k', kn)
# the four substitution hypotheses of fsumparts
def subpair(src, dst):
    a = w.s([w.s([], 'oveq2', '( k = %s -> ( 1 ... k ) = ( 1 ... %s ) )' % (dst, dst))], 'sumeq1d',
            '( k = %s -> %s = %s )' % (dst, PS('k'), PS(dst)))
    b = w.s([], 'oveq1', '( k = %s -> %s = %s )' % (dst, CP('k'), CP(dst)))
    return w.s([a, b], 'jca', '( k = %s -> ( %s = %s /\\ %s = %s ) )' % (dst, PS('k'), PS(dst), CP('k'), CP(dst)))


hb = subpair('k', 'j')
hc = subpair('k', '( j + 1 )')
hd = subpair('k', '1')
he = subpair('k', 'N')
w.qed([hb, hc, hd, he, nuz, psk, cpk], 'fsumparts',
      '( %s -> %s = ( ( %s - ( %s x. %s ) ) - %s ) )' % (AF, LS, W1, PS('1'), CP('1'), RS))
run4(w)

# ---------------------------------------------------------------- abelid
w = W('abelid', 'Abel summation (partial summation) for a Dirichlet-series partial '
      'sum: the sum of ` ( ( A ` k ) x. ( k ^c -u Z ) ) ` over ` ( 1 ... N ) ` is '
      'the boundary term plus the sum of the partial sums against the differences '
      'of ` ( k ^c -u Z ) `.  This is ` abel_identity ` of Route Z\'s LGrowth.lean, '
      'from ~ abelid0 with the telescoping ( ~ abelpd ) and the reindexing '
      '( ~ abelrx ) carried out.')
af = w.s([], 'simp1', '( %s -> A : NN --> CC )' % AF)
zc = w.s([], 'simp2', '( %s -> Z e. CC )' % AF)
nn = w.s([], 'simp3', '( %s -> N e. NN )' % AF)
nuz = w.s([nn, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % AF)],
          'eleqtrd', '( %s -> N e. ( ZZ>= ` 1 ) )' % AF)
nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % AF)
onec = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % AF)
n1 = w.s([w.s([], '1nn', '1 e. NN')], 'a1i', '( %s -> 1 e. NN )' % AF)
a1c = w.s([af, n1], 'ffvelcdmd', '( %s -> %s e. CC )' % (AF, A1))
raw = w.s([w.s([], 'id', '( %s -> %s )' % (AF, AF)), w.inst('abelid0')], 'syl',
          '( %s -> %s = ( ( %s - ( %s x. %s ) ) - %s ) )' % (AF, LS, W1, PS('1'), CP('1'), RS))
# the boundary term at 1
ps1 = w.s([w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % AF), a1c,
           w.s([], 'fveq2', '( i = 1 -> ( A ` i ) = %s )' % A1), w.inst('fsum1')], 'dummy', 'x')
w.lines.pop()
sb1 = w.s([], 'fveq2', '( i = 1 -> ( A ` i ) = %s )' % A1)
ps1 = w.s([w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % AF), a1c,
           w.s([sb1], 'fsum1', '( ( 1 e. ZZ /\\ %s e. CC ) -> %s = %s )' % (A1, PS('1'), A1))], 'syl2anc',
          '( %s -> %s = %s )' % (AF, PS('1'), A1))
cp1 = w.s([nzc, w.inst('1cxp')], 'syl', '( %s -> %s = 1 )' % (AF, CP('1')))
bd1 = w.s([w.s([ps1, cp1], 'oveq12d', '( %s -> ( %s x. %s ) = ( %s x. 1 ) )' % (AF, PS('1'), CP('1'), A1)),
           w.s([a1c], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AF, A1, A1))], 'eqtrd',
          '( %s -> ( %s x. %s ) = %s )' % (AF, PS('1'), CP('1'), A1))
# the telescoping sum equals the reindexed Dirichlet sum
AJ = '( %s /\\ j e. ( 1 ..^ N ) )' % AF
jn = w.s([w.s([], 'simpr', '( %s -> j e. ( 1 ..^ N ) )' % AJ), w.inst('elfzonn0')], 'syl', 'dummy')
w.lines.pop()
jn = w.s([w.s([w.s([], 'simpr', '( %s -> j e. ( 1 ..^ N ) )' % AJ), w.inst('elfzofz')], 'syl',
              '( %s -> j e. ( 1 ... N ) )' % AJ), w.inst('elfznn')], 'syl', '( %s -> j e. NN )' % AJ)
j1n = w.s([jn, w.inst('peano2nn')], 'syl', '( %s -> ( j + 1 ) e. NN )' % AJ)
pdif = w.s([w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % AJ), jn], 'jca',
                '( %s -> ( A : NN --> CC /\\ j e. NN ) )' % AJ), w.inst('abelpd')], 'syl',
           '( %s -> ( %s - %s ) = ( A ` ( j + 1 ) ) )' % (AJ, PS('( j + 1 )'), PS('j')))
tel = w.s([w.s([pdif], 'oveq1d',
               '( %s -> ( ( %s - %s ) x. %s ) = ( ( A ` ( j + 1 ) ) x. %s ) )' % (AJ, PS('( j + 1 )'), PS('j'), CP('( j + 1 )'), CP('( j + 1 )')))],
          'sumeq2dv', '( %s -> %s = sum_ j e. ( 1 ..^ N ) ( ( A ` ( j + 1 ) ) x. %s ) )' % (AF, RS, CP('( j + 1 )')))
rx = w.s([w.s([], 'id', '( %s -> %s )' % (AF, AF)), w.inst('abelrx')], 'syl',
         '( %s -> sum_ j e. ( 1 ..^ N ) ( ( A ` ( j + 1 ) ) x. %s ) = %s )' % (AF, CP('( j + 1 )'), R2))
telr = w.s([tel, rx], 'eqtrd', '( %s -> %s = %s )' % (AF, RS, R2))
# fsumparts rewritten
bdi = w.s([bd1], 'oveq2d', '( %s -> ( %s - ( %s x. %s ) ) = ( %s - %s ) )' % (AF, W1, PS('1'), CP('1'), W1, A1))
fpr = w.s([raw, w.s([bdi, telr], 'oveq12d',
                    '( %s -> ( ( %s - ( %s x. %s ) ) - %s ) = ( ( %s - %s ) - %s ) )' % (AF, W1, PS('1'), CP('1'), RS, W1, A1, R2))],
          'eqtrd', '( %s -> %s = ( ( %s - %s ) - %s ) )' % (AF, LS, W1, A1, R2))
# closures
psn, cpn = fzcl(AF, 'N', nn)
w1c = w.s([psn, cpn], 'mulcld', '( %s -> %s e. CC )' % (AF, W1))
finj = w.s([w.s([], 'fzofi', '( 1 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 1 ..^ N ) e. Fin )' % AF)
psj, cpj = fzcl(AJ, 'j', jn)
psj1, cpj1 = fzcl(AJ, '( j + 1 )', j1n)
lstm = w.s([psj, w.s([cpj1, cpj], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (AJ, CP('( j + 1 )'), CP('j')))],
           'mulcld', '( %s -> ( %s x. ( %s - %s ) ) e. CC )' % (AJ, PS('j'), CP('( j + 1 )'), CP('j')))
lsc = w.s([finj, lstm], 'fsumcl', '( %s -> %s e. CC )' % (AF, LS))
AK2 = "( %s /\\ k e. ( 2 ... N ) )" % AF
kn2 = w.s([w.s([w.s([], 'simpr', '( %s -> k e. ( 2 ... N ) )' % AK2), w.inst('elfzelz')], 'syl',
               '( %s -> k e. ZZ )' % AK2)], 'zcnd', '( %s -> k e. CC )' % AK2)
kn2n = w.s([w.s([], 'simpr', '( %s -> k e. ( 2 ... N ) )' % AK2), w.inst('elfznn')], 'syl', 'dummy')
w.lines.pop()
kn2n = w.s([w.s([w.s([], 'simpr', '( %s -> k e. ( 2 ... N ) )' % AK2), w.inst('elfzuz')], 'syl',
                '( %s -> k e. ( ZZ>= ` 2 ) )' % AK2), w.inst('eluz2nn')], 'syl', '( %s -> k e. NN )' % AK2)
ackl = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % AK2), kn2n], 'ffvelcdmd',
           '( %s -> ( A ` k ) e. CC )' % AK2)
ckcl = w.s([w.s([w.s([kn2n], 'nnrpd', '( %s -> k e. RR+ )' % AK2)], 'rpcnd', '( %s -> k e. CC )' % AK2),
            w.s([nzc], 'adantr', '( %s -> -u Z e. CC )' % AK2)], 'cxpcld', '( %s -> %s e. CC )' % (AK2, CP('k')))
tkc = w.s([ackl, ckcl], 'mulcld', '( %s -> %s e. CC )' % (AK2, TRM('k')))
r2c = w.s([w.s([], 'fzfid', '( %s -> ( 2 ... N ) e. Fin )' % AF), tkc], 'fsumcl', '( %s -> %s e. CC )' % (AF, R2))
# the sum of the ATM terms is -u LS
ngt = w.s([psj, cpj1, cpj], 'mulsubfacd' if False else 'dummy', 'x')
w.lines.pop()
nsd = w.s([cpj1, cpj], 'negsubdi2d', '( %s -> -u ( %s - %s ) = ( %s - %s ) )' % (AJ, CP('( j + 1 )'), CP('j'), CP('j'), CP('( j + 1 )')))
mn = w.s([psj, w.s([cpj1, cpj], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (AJ, CP('( j + 1 )'), CP('j')))],
         'mulneg2d', '( %s -> ( %s x. -u ( %s - %s ) ) = -u ( %s x. ( %s - %s ) ) )' % (AJ, PS('j'), CP('( j + 1 )'), CP('j'), PS('j'), CP('( j + 1 )'), CP('j')))
atmeq = w.s([w.s([w.s([nsd], 'oveq2d', '( %s -> ( %s x. -u ( %s - %s ) ) = %s )' % (AJ, PS('j'), CP('( j + 1 )'), CP('j'), ATM('j')))], 'eqcomd',
                 '( %s -> %s = ( %s x. -u ( %s - %s ) ) )' % (AJ, ATM('j'), PS('j'), CP('( j + 1 )'), CP('j'))), mn],
            'eqtrd', '( %s -> %s = -u ( %s x. ( %s - %s ) ) )' % (AJ, ATM('j'), PS('j'), CP('( j + 1 )'), CP('j')))
sneg = w.s([finj, lstm], 'fsumneg', '( %s -> sum_ j e. ( 1 ..^ N ) -u ( %s x. ( %s - %s ) ) = -u %s )' % (AF, PS('j'), CP('( j + 1 )'), CP('j'), LS))
asum = w.s([w.s([atmeq], 'sumeq2dv', '( %s -> %s = sum_ j e. ( 1 ..^ N ) -u ( %s x. ( %s - %s ) ) )' % (AF, AS, PS('j'), CP('( j + 1 )'), CP('j'))),
            sneg], 'eqtrd', '( %s -> %s = -u %s )' % (AF, AS, LS))
# the left-hand side split at k = 1
LHS = 'sum_ k e. ( 1 ... N ) %s' % TRM('k')
AKN = "( %s /\\ k e. ( 1 ... N ) )" % AF
knn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % AKN), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % AKN)
acn = w.s([w.s([af], 'adantr', '( %s -> A : NN --> CC )' % AKN), knn], 'ffvelcdmd', '( %s -> ( A ` k ) e. CC )' % AKN)
ccn = w.s([w.s([w.s([knn], 'nnrpd', '( %s -> k e. RR+ )' % AKN)], 'rpcnd', '( %s -> k e. CC )' % AKN),
           w.s([nzc], 'adantr', '( %s -> -u Z e. CC )' % AKN)], 'cxpcld', '( %s -> %s e. CC )' % (AKN, CP('k')))
tcn = w.s([acn, ccn], 'mulcld', '( %s -> %s e. CC )' % (AKN, TRM('k')))
sub1 = w.s([w.s([], 'fveq2', '( k = 1 -> ( A ` k ) = %s )' % A1), w.s([], 'oveq1', '( k = 1 -> %s = %s )' % (CP('k'), CP('1')))],
           'oveq12d', '( k = 1 -> %s = ( %s x. %s ) )' % (TRM('k'), A1, CP('1')))
sp = w.s([nuz, tcn, sub1], 'fsum1p', '( %s -> %s = ( ( %s x. %s ) + sum_ k e. ( ( 1 + 1 ) ... N ) %s ) )' % (AF, LHS, A1, CP('1'), TRM('k')))
r1e = w.s([w.s([num.add_nat(w, 1, 1)], 'a1i', '( %s -> ( 1 + 1 ) = 2 )' % AF)], 'oveq1d',
          '( %s -> ( ( 1 + 1 ) ... N ) = ( 2 ... N ) )' % AF)
r1s = w.s([r1e], 'sumeq1d', '( %s -> sum_ k e. ( ( 1 + 1 ) ... N ) %s = %s )' % (AF, TRM('k'), R2))
t1e = w.s([w.s([cp1], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. 1 ) )' % (AF, A1, CP('1'), A1)),
           w.s([a1c], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (AF, A1, A1))], 'eqtrd',
          '( %s -> ( %s x. %s ) = %s )' % (AF, A1, CP('1'), A1))
lhs = w.s([sp, w.s([t1e, r1s], 'oveq12d', '( %s -> ( ( %s x. %s ) + sum_ k e. ( ( 1 + 1 ) ... N ) %s ) = ( %s + %s ) )' % (AF, A1, CP('1'), TRM('k'), A1, R2))],
          'eqtrd', '( %s -> %s = ( %s + %s ) )' % (AF, LHS, A1, R2))
# -u LS = ( ( R2 + A1 ) - W1 )
n1s = w.s([w.s([w1c, a1c], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (AF, W1, A1)), r2c], 'negsubdi2d',
          '( %s -> -u ( ( %s - %s ) - %s ) = ( %s - ( %s - %s ) ) )' % (AF, W1, A1, R2, R2, W1, A1))
n2s = w.s([r2c, w1c, a1c], 'subsub3d', '( %s -> ( %s - ( %s - %s ) ) = ( ( %s + %s ) - %s ) )' % (AF, R2, W1, A1, R2, A1, W1))
nls = w.s([w.s([w.s([fpr], 'negeqd', '( %s -> -u %s = -u ( ( %s - %s ) - %s ) )' % (AF, LS, W1, A1, R2)), n1s], 'eqtrd',
               '( %s -> -u %s = ( %s - ( %s - %s ) ) )' % (AF, LS, R2, W1, A1)), n2s], 'eqtrd',
          '( %s -> -u %s = ( ( %s + %s ) - %s ) )' % (AF, LS, R2, A1, W1))
rhs = w.s([w.s([w.s([asum, nls], 'eqtrd', '( %s -> %s = ( ( %s + %s ) - %s ) )' % (AF, AS, R2, A1, W1))], 'oveq2d',
               '( %s -> ( %s + %s ) = ( %s + ( ( %s + %s ) - %s ) ) )' % (AF, W1, AS, W1, R2, A1, W1)),
           w.s([w1c, w.s([r2c, a1c], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (AF, R2, A1))], 'pncan3d',
               '( %s -> ( %s + ( ( %s + %s ) - %s ) ) = ( %s + %s ) )' % (AF, W1, R2, A1, W1, R2, A1))],
          'eqtrd', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (AF, W1, AS, R2, A1))
cm = w.s([r2c, a1c], 'addcomd', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (AF, R2, A1, A1, R2))
w.qed([lhs, w.s([w.s([rhs, cm], 'eqtrd', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (AF, W1, AS, A1, R2))], 'eqcomd',
                '( %s -> ( %s + %s ) = ( %s + %s ) )' % (AF, A1, R2, W1, AS))], 'eqtrd',
      '( %s -> %s = ( %s + %s ) )' % (AF, LHS, W1, AS))
run4(w)
