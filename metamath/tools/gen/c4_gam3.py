"""C4, Gamma block 3: the finite-product comparison."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

RZ = '( Re ` Z )'
EZ = EUT('Z'); EX = EUT(RZ)
AZ = '( abs ` ( %s ` k ) )' % EZ
AX = '( %s ` k )' % EX

# ---------------------------------------------------------------- fzprsp
w = W('fzprsp', 'Split a finite product over ` ( 1 ... N ) ` at an index ` M ` in '
      '` NN0 ` below ` N `.  The case ` M = 0 ` is allowed, where the first factor '
      'is the empty product.')
hyp(w, '1', 'fzprsp.k', '( ( ph /\\ k e. ( 1 ... N ) ) -> B e. CC )')
hyp(w, '2', 'fzprsp.m', '( ph -> M e. NN0 )')
hyp(w, '3', 'fzprsp.n', '( ph -> N e. ( ZZ>= ` M ) )')
mr = w.s(['2', w.inst('nn0re')], 'syl', '( ph -> M e. RR )')
lt = w.s([mr], 'ltp1d', '( ph -> M < ( M + 1 ) )')
dis = w.s([lt, w.inst('fzdisj')], 'syl', '( ph -> ( ( 1 ... M ) i^i ( ( M + 1 ) ... N ) ) = (/) )')
m1n = w.s(['2', w.inst('nn0p1nn')], 'syl', '( ph -> ( M + 1 ) e. NN )')
m1u = w.s([m1n, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( ph -> NN = ( ZZ>= ` 1 ) )')],
          'eleqtrd', '( ph -> ( M + 1 ) e. ( ZZ>= ` 1 ) )')
spl = w.s([m1u, '3', w.inst('fzsplit2')], 'syl2anc',
          '( ph -> ( 1 ... N ) = ( ( 1 ... M ) u. ( ( M + 1 ) ... N ) ) )')
fin = w.s([], 'fzfid', '( ph -> ( 1 ... N ) e. Fin )')
w.qed([dis, spl, fin, '1'], 'fprodsplit',
      '( ph -> prod_ k e. ( 1 ... N ) B = ( prod_ k e. ( 1 ... M ) B x. prod_ k e. ( ( M + 1 ) ... N ) B ) )')
run4(w, h=True)

HQ = 'A. j e. ( 1 ... M ) ( 2 x. ( %s + j ) ) <_ ( abs ` ( Im ` Z ) )' % RZ
PHM = '( ( Z e. CC /\\ 0 < %s ) /\\ ( M e. NN0 /\\ %s ) )' % (RZ, HQ)


def basec(w, A, zc='simpll', z0='simplr'):
    """Z e. CC and 0 < Re Z under an antecedent whose first conjunct is the pair"""
    return (w.s([], zc, '( %s -> Z e. CC )' % A), w.s([], z0, '( %s -> 0 < %s )' % (A, RZ)))


# ---------------------------------------------------------------- gamprh
w = W('gamprh', 'The head block of Euler\'s product loses a factor of two at every '
      'index below ` M `.')
ZP = '( Z e. CC /\\ 0 < %s )' % RZ
zc = w.s([w.s([], 'simpl', '( %s -> %s )' % (PHM, ZP)), w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % PHM)
z0 = w.s([w.s([], 'simpl', '( %s -> %s )' % (PHM, ZP)), w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (PHM, RZ))
mn0 = w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 /\\ %s ) )' % (PHM, HQ)), w.inst('simpl')], 'syl',
          '( %s -> M e. NN0 )' % PHM)
hq = w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 /\\ %s ) )' % (PHM, HQ)), w.inst('simpr')], 'syl',
         '( %s -> %s )' % (PHM, HQ))
# rename the quantifier from j to k
sb = w.s([w.s([w.s([], 'oveq2', '( j = k -> ( %s + j ) = ( %s + k ) )' % (RZ, RZ))], 'oveq2d',
              '( j = k -> ( 2 x. ( %s + j ) ) = ( 2 x. ( %s + k ) ) )' % (RZ, RZ))], 'breq1d',
         '( j = k -> ( ( 2 x. ( %s + j ) ) <_ ( abs ` ( Im ` Z ) ) <-> ( 2 x. ( %s + k ) ) <_ ( abs ` ( Im ` Z ) ) ) )' % (RZ, RZ))
cbv = w.s([sb], 'cbvralvw', '( %s <-> A. k e. ( 1 ... M ) ( 2 x. ( %s + k ) ) <_ ( abs ` ( Im ` Z ) ) )' % (HQ, RZ))
hqk = w.s([hq, w.s([cbv], 'a1i', '( %s -> ( %s <-> A. k e. ( 1 ... M ) ( 2 x. ( %s + k ) ) <_ ( abs ` ( Im ` Z ) ) ) )' % (PHM, HQ, RZ))],
          'mpbid', '( %s -> A. k e. ( 1 ... M ) ( 2 x. ( %s + k ) ) <_ ( abs ` ( Im ` Z ) ) )' % (PHM, RZ))
PS = '( %s /\\ k e. ( 1 ... M ) )' % PHM
kfz = w.s([], 'simpr', '( %s -> k e. ( 1 ... M ) )' % PS)
kn = w.s([kfz, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % PS)
zcr = w.s([zc], 'adantr', '( %s -> Z e. CC )' % PS)
z0r = w.s([z0], 'adantr', '( %s -> 0 < %s )' % (PS, RZ))
hk = w.s([w.s([hqk], 'adantr', '( %s -> A. k e. ( 1 ... M ) ( 2 x. ( %s + k ) ) <_ ( abs ` ( Im ` Z ) ) )' % (PS, RZ)),
          kfz, w.inst('rspa')], 'syl2anc', '( %s -> ( 2 x. ( %s + k ) ) <_ ( abs ` ( Im ` Z ) ) )' % (PS, RZ))
A0k = '( ( ( Z e. CC /\\ 0 < %s ) /\\ k e. NN ) /\\ ( 2 x. ( %s + k ) ) <_ ( abs ` ( Im ` Z ) ) )' % (RZ, RZ)
base = w.s([w.s([zcr, z0r], 'jca', '( %s -> %s )' % (PS, ZP)), kn], 'jca',
           '( %s -> ( %s /\\ k e. NN ) )' % (PS, ZP))
lh = w.s([w.s([base, hk], 'jca', '( %s -> %s )' % (PS, A0k)), w.inst('eutlehv')], 'syl',
         '( %s -> %s <_ ( %s / 2 ) )' % (PS, AZ, AX))
zrp = w.s([base, w.inst('eutzrp')], 'syl', '( %s -> %s e. RR+ )' % (PS, AZ))
zre = w.s([zrp], 'rpred', '( %s -> %s e. RR )' % (PS, AZ))
z0e = w.s([zrp], 'rpge0d', '( %s -> 0 <_ %s )' % (PS, AZ))
xrp = w.s([base, w.inst('eutxrp')], 'syl', '( %s -> %s e. RR+ )' % (PS, AX))
xre = w.s([xrp], 'rpred', '( %s -> %s e. RR )' % (PS, AX))
xhr = w.s([xre, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % PS),
           w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % PS)], 'redivcld',
          '( %s -> ( %s / 2 ) e. RR )' % (PS, AX))
nfk = w.s([], 'nfv', 'F/ k %s' % PHM)
fin = w.s([], 'fzfid', '( %s -> ( 1 ... M ) e. Fin )' % PHM)
ple = w.s([nfk, fin, zre, z0e, xhr, lh], 'fprodle',
          '( %s -> prod_ k e. ( 1 ... M ) %s <_ prod_ k e. ( 1 ... M ) ( %s / 2 ) )' % (PHM, AZ, AX))
# prod ( EX / 2 ) = ( prod EX ) / ( 2 ^ M )
xcn = w.s([xrp], 'rpcnd', '( %s -> %s e. CC )' % (PS, AX))
t2c = w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % PS)
t2n = w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % PS)
dv = w.s([fin, xcn, t2c, t2n], 'fproddiv',
         '( %s -> prod_ k e. ( 1 ... M ) ( %s / 2 ) = ( prod_ k e. ( 1 ... M ) %s / prod_ k e. ( 1 ... M ) 2 ) )' % (PHM, AX, AX))
cst = w.s([fin, w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % PHM), w.inst('fprodconst')],
          'syl2anc', '( %s -> prod_ k e. ( 1 ... M ) 2 = ( 2 ^ ( # ` ( 1 ... M ) ) ) )' % PHM)
hf = w.s([mn0, w.inst('hashfz1')], 'syl', '( %s -> ( # ` ( 1 ... M ) ) = M )' % PHM)
cst2 = w.s([cst, w.s([hf], 'oveq2d', '( %s -> ( 2 ^ ( # ` ( 1 ... M ) ) ) = ( 2 ^ M ) )' % PHM)],
           'eqtrd', '( %s -> prod_ k e. ( 1 ... M ) 2 = ( 2 ^ M ) )' % PHM)
dv2 = w.s([dv, w.s([cst2], 'oveq2d',
                   '( %s -> ( prod_ k e. ( 1 ... M ) %s / prod_ k e. ( 1 ... M ) 2 ) = ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) )' % (PHM, AX, AX))],
          'eqtrd', '( %s -> prod_ k e. ( 1 ... M ) ( %s / 2 ) = ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) )' % (PHM, AX, AX))
w.qed([ple, dv2], 'breqtrd',
      '( %s -> prod_ k e. ( 1 ... M ) %s <_ ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) )' % (PHM, AZ, AX))
run4(w)

PHT = '( ( Z e. CC /\\ 0 < %s ) /\\ ( M e. NN0 /\\ N e. ( ZZ>= ` M ) ) )' % RZ

# ---------------------------------------------------------------- gamprt
w = W('gamprt', 'The tail block of Euler\'s product: the modulus at a complex '
      'argument never exceeds the value at the real part.')
zc = w.s([w.s([], 'simpl', '( %s -> %s )' % (PHT, ZP)), w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % PHT)
z0 = w.s([w.s([], 'simpl', '( %s -> %s )' % (PHT, ZP)), w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (PHT, RZ))
mn0 = w.s([w.s([], 'simpr', '( %s -> ( M e. NN0 /\\ N e. ( ZZ>= ` M ) ) )' % PHT), w.inst('simpl')], 'syl',
          '( %s -> M e. NN0 )' % PHT)
m1n = w.s([mn0, w.inst('nn0p1nn')], 'syl', '( %s -> ( M + 1 ) e. NN )' % PHT)
m1u = w.s([m1n, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % PHT)],
          'eleqtrd', '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % PHT)
ss = w.s([m1u, w.inst('fzss1')], 'syl', '( %s -> ( ( M + 1 ) ... N ) C_ ( 1 ... N ) )' % PHT)
PT = '( %s /\\ k e. ( ( M + 1 ) ... N ) )' % PHT
kn = w.s([w.s([w.s([ss], 'adantr', '( %s -> ( ( M + 1 ) ... N ) C_ ( 1 ... N ) )' % PT),
               w.s([], 'simpr', '( %s -> k e. ( ( M + 1 ) ... N ) )' % PT)], 'sseldd',
              '( %s -> k e. ( 1 ... N ) )' % PT), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % PT)
base = w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % PT), w.s([z0], 'adantr', '( %s -> 0 < %s )' % (PT, RZ))],
                'jca', '( %s -> %s )' % (PT, ZP)), kn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (PT, ZP))
lev = w.s([base, w.inst('eutlev')], 'syl', '( %s -> %s <_ %s )' % (PT, AZ, AX))
zrp = w.s([base, w.inst('eutzrp')], 'syl', '( %s -> %s e. RR+ )' % (PT, AZ))
xrp = w.s([base, w.inst('eutxrp')], 'syl', '( %s -> %s e. RR+ )' % (PT, AX))
nfk = w.s([], 'nfv', 'F/ k %s' % PHT)
fin = w.s([], 'fzfid', '( %s -> ( ( M + 1 ) ... N ) e. Fin )' % PHT)
w.qed([nfk, fin, w.s([zrp], 'rpred', '( %s -> %s e. RR )' % (PT, AZ)),
       w.s([zrp], 'rpge0d', '( %s -> 0 <_ %s )' % (PT, AZ)),
       w.s([xrp], 'rpred', '( %s -> %s e. RR )' % (PT, AX)), lev], 'fprodle',
      '( %s -> prod_ k e. ( ( M + 1 ) ... N ) %s <_ prod_ k e. ( ( M + 1 ) ... N ) %s )' % (PHT, AZ, AX))
run4(w)

# ---------------------------------------------------------------- gamprod
PH2 = '( %s /\\ N e. ( ZZ>= ` M ) )' % PHM
w = W('gamprod', 'The partial product of the moduli of Euler\'s terms at a complex '
      'argument, against the partial product at the real part: every index below '
      '` M ` contributes a factor of one half.')
zc = w.s([w.s([w.s([], 'simpll', '( %s -> %s )' % (PH2, ZP)), w.inst('simpl')], 'syl',
              '( %s -> Z e. CC )' % PH2)], 'id', '( %s -> Z e. CC )' % PH2)
w.lines.pop()
zp = w.s([], 'simpll', '( %s -> %s )' % (PH2, ZP))
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % PH2)
z0 = w.s([zp, w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (PH2, RZ))
mh = w.s([], 'simplr', '( %s -> ( M e. NN0 /\\ %s ) )' % (PH2, HQ))
mn0 = w.s([mh, w.inst('simpl')], 'syl', '( %s -> M e. NN0 )' % PH2)
nu = w.s([], 'simpr', '( %s -> N e. ( ZZ>= ` M ) )' % PH2)
phm = w.s([], 'simpl', '( %s -> %s )' % (PH2, PHM))
pht = w.s([w.s([zc, z0], 'jca', '( %s -> %s )' % (PH2, ZP)), w.s([mn0, nu], 'jca',
           '( %s -> ( M e. NN0 /\\ N e. ( ZZ>= ` M ) ) )' % PH2)], 'jca', '( %s -> %s )' % (PH2, PHT))
# the two splits
PN = '( %s /\\ k e. ( 1 ... N ) )' % PH2
knn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % PN), w.inst('elfznn')], 'syl',
          '( %s -> k e. NN )' % PN)
basen = w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % PN), w.s([z0], 'adantr', '( %s -> 0 < %s )' % (PN, RZ))],
                 'jca', '( %s -> %s )' % (PN, ZP)), knn], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (PN, ZP))
azc = w.s([w.s([basen, w.inst('eutzrp')], 'syl', '( %s -> %s e. RR+ )' % (PN, AZ))], 'rpcnd',
          '( %s -> %s e. CC )' % (PN, AZ))
axc = w.s([w.s([basen, w.inst('eutxrp')], 'syl', '( %s -> %s e. RR+ )' % (PN, AX))], 'rpcnd',
          '( %s -> %s e. CC )' % (PN, AX))
s1 = w.s([azc, mn0, nu], 'fzprsp',
         '( %s -> prod_ k e. ( 1 ... N ) %s = ( prod_ k e. ( 1 ... M ) %s x. prod_ k e. ( ( M + 1 ) ... N ) %s ) )' % (PH2, AZ, AZ, AZ))
s2 = w.s([axc, mn0, nu], 'fzprsp',
         '( %s -> prod_ k e. ( 1 ... N ) %s = ( prod_ k e. ( 1 ... M ) %s x. prod_ k e. ( ( M + 1 ) ... N ) %s ) )' % (PH2, AX, AX, AX))
h = w.s([phm, w.inst('gamprh')], 'syl',
        '( %s -> prod_ k e. ( 1 ... M ) %s <_ ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) )' % (PH2, AZ, AX))
t = w.s([pht, w.inst('gamprt')], 'syl',
        '( %s -> prod_ k e. ( ( M + 1 ) ... N ) %s <_ prod_ k e. ( ( M + 1 ) ... N ) %s )' % (PH2, AZ, AX))
# closures of the four partial products
nfk = w.s([], 'nfv', 'F/ k %s' % PH2)


def prcl(A, S):
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (PH2, S))
    zr = w.s([basen, w.inst('eutzrp')], 'syl', '( %s -> %s e. RR+ )' % (PN, AZ))
    return fin


finM = w.s([], 'fzfid', '( %s -> ( 1 ... M ) e. Fin )' % PH2)
finT = w.s([], 'fzfid', '( %s -> ( ( M + 1 ) ... N ) e. Fin )' % PH2)
finN = w.s([], 'fzfid', '( %s -> ( 1 ... N ) e. Fin )' % PH2)
PM = '( %s /\\ k e. ( 1 ... M ) )' % PH2
PT2 = '( %s /\\ k e. ( ( M + 1 ) ... N ) )' % PH2
# reality/nonnegativity on the two blocks, obtained from the ( 1 ... N ) versions by subset
m1n = w.s([mn0, w.inst('nn0p1nn')], 'syl', '( %s -> ( M + 1 ) e. NN )' % PH2)
m1u = w.s([m1n, w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'a1i', '( %s -> NN = ( ZZ>= ` 1 ) )' % PH2)],
          'eleqtrd', '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % PH2)
ssT = w.s([m1u, w.inst('fzss1')], 'syl', '( %s -> ( ( M + 1 ) ... N ) C_ ( 1 ... N ) )' % PH2)
ssM = w.s([nu, w.inst('fzss2')], 'syl', '( %s -> ( 1 ... M ) C_ ( 1 ... N ) )' % PH2)


def blk(S, ssst, PB):
    kmem = w.s([w.s([ssst], 'adantr', '( %s -> %s C_ ( 1 ... N ) )' % (PB, S)),
                w.s([], 'simpr', '( %s -> k e. %s )' % (PB, S))], 'sseldd', '( %s -> k e. ( 1 ... N ) )' % PB)
    kn2 = w.s([kmem, w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % PB)
    bs = w.s([w.s([w.s([zc], 'adantr', '( %s -> Z e. CC )' % PB), w.s([z0], 'adantr', '( %s -> 0 < %s )' % (PB, RZ))],
                  'jca', '( %s -> %s )' % (PB, ZP)), kn2], 'jca', '( %s -> ( %s /\\ k e. NN ) )' % (PB, ZP))
    zrp = w.s([bs, w.inst('eutzrp')], 'syl', '( %s -> %s e. RR+ )' % (PB, AZ))
    xrp = w.s([bs, w.inst('eutxrp')], 'syl', '( %s -> %s e. RR+ )' % (PB, AX))
    return (w.s([zrp], 'rpred', '( %s -> %s e. RR )' % (PB, AZ)),
            w.s([zrp], 'rpge0d', '( %s -> 0 <_ %s )' % (PB, AZ)),
            w.s([xrp], 'rpred', '( %s -> %s e. RR )' % (PB, AX)))


zrM, z0M, xrM = blk('( 1 ... M )', ssM, PM)
zrT, z0T, xrT = blk('( ( M + 1 ) ... N )', ssT, PT2)
PZM = w.s([nfk, finM, zrM], 'fprodrecl', '( %s -> prod_ k e. ( 1 ... M ) %s e. RR )' % (PH2, AZ))
w.lines.pop()
PZM = w.s([finM, zrM], 'fprodrecl', '( %s -> prod_ k e. ( 1 ... M ) %s e. RR )' % (PH2, AZ))
PZM0 = w.s([nfk, finM, zrM, z0M], 'fprodge0', '( %s -> 0 <_ prod_ k e. ( 1 ... M ) %s )' % (PH2, AZ))
PXM = w.s([finM, xrM], 'fprodrecl', '( %s -> prod_ k e. ( 1 ... M ) %s e. RR )' % (PH2, AX))
PZT = w.s([finT, zrT], 'fprodrecl', '( %s -> prod_ k e. ( ( M + 1 ) ... N ) %s e. RR )' % (PH2, AZ))
PZT0 = w.s([nfk, finT, zrT, z0T], 'fprodge0', '( %s -> 0 <_ prod_ k e. ( ( M + 1 ) ... N ) %s )' % (PH2, AZ))
PXT = w.s([finT, xrT], 'fprodrecl', '( %s -> prod_ k e. ( ( M + 1 ) ... N ) %s e. RR )' % (PH2, AX))
pw = w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % PH2), mn0], 'reexpcld',
         '( %s -> ( 2 ^ M ) e. RR )' % PH2)
pwne = w.s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % PH2),
            w.s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '( %s -> 2 =/= 0 )' % PH2),
            w.s([mn0, w.inst('nn0z')], 'syl', '( %s -> M e. ZZ )' % PH2)], 'expne0d',
           '( %s -> ( 2 ^ M ) =/= 0 )' % PH2)
PXMd = w.s([PXM, pw, pwne], 'redivcld', '( %s -> ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) e. RR )' % (PH2, AX))
mul = w.s([PZM, PXMd, PZT, PXT, PZM0, PZT0, h, t], 'lemul12ad',
          '( %s -> ( prod_ k e. ( 1 ... M ) %s x. prod_ k e. ( ( M + 1 ) ... N ) %s ) <_ ( ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) x. prod_ k e. ( ( M + 1 ) ... N ) %s ) )' % (PH2, AZ, AZ, AX, AX))
# ( Q1 / 2 ^ M ) x. Q2 = ( Q1 x. Q2 ) / 2 ^ M
d23 = w.s([w.s([PXM], 'recnd', '( %s -> prod_ k e. ( 1 ... M ) %s e. CC )' % (PH2, AX)),
           w.s([PXT], 'recnd', '( %s -> prod_ k e. ( ( M + 1 ) ... N ) %s e. CC )' % (PH2, AX)),
           w.s([pw], 'recnd', '( %s -> ( 2 ^ M ) e. CC )' % PH2), pwne], 'div23d',
          '( %s -> ( ( prod_ k e. ( 1 ... M ) %s x. prod_ k e. ( ( M + 1 ) ... N ) %s ) / ( 2 ^ M ) ) = ( ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) x. prod_ k e. ( ( M + 1 ) ... N ) %s ) )' % (PH2, AX, AX, AX, AX))
rhs = w.s([w.s([s2], 'oveq1d',
               '( %s -> ( prod_ k e. ( 1 ... N ) %s / ( 2 ^ M ) ) = ( ( prod_ k e. ( 1 ... M ) %s x. prod_ k e. ( ( M + 1 ) ... N ) %s ) / ( 2 ^ M ) ) )' % (PH2, AX, AX, AX)),
           d23], 'eqtrd',
          '( %s -> ( prod_ k e. ( 1 ... N ) %s / ( 2 ^ M ) ) = ( ( prod_ k e. ( 1 ... M ) %s / ( 2 ^ M ) ) x. prod_ k e. ( ( M + 1 ) ... N ) %s ) )' % (PH2, AX, AX, AX))
w.qed([w.s([mul, rhs], 'breqtrrd',
           '( %s -> ( prod_ k e. ( 1 ... M ) %s x. prod_ k e. ( ( M + 1 ) ... N ) %s ) <_ ( prod_ k e. ( 1 ... N ) %s / ( 2 ^ M ) ) )' % (PH2, AZ, AZ, AX)), s1],
      'jca', 'dummy')
w.lines.pop()
w.qed([s1, w.s([mul, rhs], 'breqtrrd',
               '( %s -> ( prod_ k e. ( 1 ... M ) %s x. prod_ k e. ( ( M + 1 ) ... N ) %s ) <_ ( prod_ k e. ( 1 ... N ) %s / ( 2 ^ M ) ) )' % (PH2, AZ, AZ, AX))],
      'eqbrtrd', '( %s -> prod_ k e. ( 1 ... N ) %s <_ ( prod_ k e. ( 1 ... N ) %s / ( 2 ^ M ) ) )' % (PH2, AZ, AX))
run4(w)
