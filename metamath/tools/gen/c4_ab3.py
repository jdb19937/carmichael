"""C4, Abel block 3: the Abel series bound on the right half-plane."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import num

RZ = '( Re ` Z )'
T1 = '( %s + 1 )' % RZ


def ATMV(k):
    return '( ( S ` %s ) x. ( ( %s ^c -u Z ) - ( ( %s + 1 ) ^c -u Z ) ) )' % (k, k, k)


AA = '( q e. NN |-> ( %s x. ( q ^c %s ) ) )' % (ATMV('q'), T1)
ABS = '( S : NN --> CC /\\ B e. RR /\\ A. m e. NN ( abs ` ( S ` m ) ) <_ B )'
ZPP = '( Z e. CC /\\ 0 < %s )' % RZ
A1 = '( %s /\\ %s )' % (ABS, ZPP)
BZ = '( B x. ( abs ` Z ) )'
SF = '( S : NN --> CC /\\ Z e. CC /\\ 0 < %s )' % RZ
A2 = '( %s /\\ K e. NN )' % SF

# ---------------------------------------------------------------- abmul
w = W('abmul', 'The normalised Abel coefficient ( ~ abcfb ) against the power '
      '` ( K ^c -u ( ( Re ` Z ) + 1 ) ) ` recovers the Abel term.')
sf = w.s([], 'simpl1', '( %s -> S : NN --> CC )' % A2)
zc = w.s([], 'simpl2', '( %s -> Z e. CC )' % A2)
z0 = w.s([], 'simpl3', '( %s -> 0 < %s )' % (A2, RZ))
kn = w.s([], 'simpr', '( %s -> K e. NN )' % A2)
krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A2)
kc = w.s([krp], 'rpcnd', '( %s -> K e. CC )' % A2)
kne = w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A2)
rzr = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A2, RZ))
one = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A2)
t1r = w.s([rzr, one], 'readdcld', '( %s -> %s e. RR )' % (A2, T1))
t1c = w.s([t1r], 'recnd', '( %s -> %s e. CC )' % (A2, T1))
nt1c = w.s([t1c], 'negcld', '( %s -> -u %s e. CC )' % (A2, T1))
nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A2)
scl = w.s([sf, kn], 'ffvelcdmd', '( %s -> ( S ` K ) e. CC )' % A2)
k1c = w.s([w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A2)], 'nncnd',
          '( %s -> ( K + 1 ) e. CC )' % A2)
difc = w.s([w.s([kc, nzc], 'cxpcld', '( %s -> ( K ^c -u Z ) e. CC )' % A2),
            w.s([k1c, nzc], 'cxpcld', '( %s -> ( ( K + 1 ) ^c -u Z ) e. CC )' % A2)], 'subcld',
           '( %s -> ( ( K ^c -u Z ) - ( ( K + 1 ) ^c -u Z ) ) e. CC )' % A2)
atc = w.s([scl, difc], 'mulcld', '( %s -> %s e. CC )' % (A2, ATMV('K')))
kt1 = w.s([krp, t1r], 'rpcxpcld', '( %s -> ( K ^c %s ) e. RR+ )' % (A2, T1))
kmt1 = w.s([krp, w.s([t1r], 'renegcld', '( %s -> -u %s e. RR )' % (A2, T1))], 'rpcxpcld',
           '( %s -> ( K ^c -u %s ) e. RR+ )' % (A2, T1))
# the value of AA at K
sub = w.s([w.s([w.s([], 'fveq2', '( q = K -> ( S ` q ) = ( S ` K ) )'),
                w.s([w.s([], 'oveq1', '( q = K -> ( q ^c -u Z ) = ( K ^c -u Z ) )'),
                     w.s([w.s([], 'oveq1', '( q = K -> ( q + 1 ) = ( K + 1 ) )')], 'oveq1d',
                         '( q = K -> ( ( q + 1 ) ^c -u Z ) = ( ( K + 1 ) ^c -u Z ) )')], 'oveq12d',
                    '( q = K -> ( ( q ^c -u Z ) - ( ( q + 1 ) ^c -u Z ) ) = ( ( K ^c -u Z ) - ( ( K + 1 ) ^c -u Z ) ) )')],
               'oveq12d', '( q = K -> %s = %s )' % (ATMV('q'), ATMV('K'))),
           w.s([], 'oveq1', '( q = K -> ( q ^c %s ) = ( K ^c %s ) )' % (T1, T1))], 'oveq12d',
          '( q = K -> ( %s x. ( q ^c %s ) ) = ( %s x. ( K ^c %s ) ) )' % (ATMV('q'), T1, ATMV('K'), T1))
val = w.s([kn, w.s([w.s([], 'ovex', '( %s x. ( K ^c %s ) ) e. _V' % (ATMV('K'), T1))], 'a1i',
                   '( %s -> ( %s x. ( K ^c %s ) ) e. _V )' % (A2, ATMV('K'), T1)),
           w.s([sub, w.s([], 'eqid', '%s = %s' % (AA, AA))], 'fvmptg',
               '( ( K e. NN /\\ ( %s x. ( K ^c %s ) ) e. _V ) -> ( %s ` K ) = ( %s x. ( K ^c %s ) ) )' % (ATMV('K'), T1, AA, ATMV('K'), T1))],
          'syl2anc', '( %s -> ( %s ` K ) = ( %s x. ( K ^c %s ) ) )' % (A2, AA, ATMV('K'), T1))
# cancel the powers
cadd = w.s([w.s([kc, kne], 'jca', '( %s -> ( K e. CC /\\ K =/= 0 ) )' % A2), t1c, nt1c, w.inst('cxpadd')],
           'syl3anc', '( %s -> ( K ^c ( %s + -u %s ) ) = ( ( K ^c %s ) x. ( K ^c -u %s ) ) )' % (A2, T1, T1, T1, T1))
z0e = w.s([t1c], 'negidd', '( %s -> ( %s + -u %s ) = 0 )' % (A2, T1, T1))
one1 = w.s([w.s([w.s([z0e], 'oveq2d', '( %s -> ( K ^c ( %s + -u %s ) ) = ( K ^c 0 ) )' % (A2, T1, T1)),
                 w.s([kc, w.inst('cxp0')], 'syl', '( %s -> ( K ^c 0 ) = 1 )' % A2)], 'eqtrd',
                '( %s -> ( K ^c ( %s + -u %s ) ) = 1 )' % (A2, T1, T1))], 'id',
           '( %s -> ( K ^c ( %s + -u %s ) ) = 1 )' % (A2, T1, T1))
w.lines.pop()
one1 = w.s([w.s([z0e], 'oveq2d', '( %s -> ( K ^c ( %s + -u %s ) ) = ( K ^c 0 ) )' % (A2, T1, T1)),
            w.s([kc, w.inst('cxp0')], 'syl', '( %s -> ( K ^c 0 ) = 1 )' % A2)], 'eqtrd',
           '( %s -> ( K ^c ( %s + -u %s ) ) = 1 )' % (A2, T1, T1))
pone = w.s([w.s([cadd], 'eqcomd', '( %s -> ( ( K ^c %s ) x. ( K ^c -u %s ) ) = ( K ^c ( %s + -u %s ) ) )' % (A2, T1, T1, T1, T1)),
            one1], 'eqtrd', '( %s -> ( ( K ^c %s ) x. ( K ^c -u %s ) ) = 1 )' % (A2, T1, T1))
assoc = w.s([atc, w.s([kt1], 'rpcnd', '( %s -> ( K ^c %s ) e. CC )' % (A2, T1)),
             w.s([kmt1], 'rpcnd', '( %s -> ( K ^c -u %s ) e. CC )' % (A2, T1))], 'mulassd',
            '( %s -> ( ( %s x. ( K ^c %s ) ) x. ( K ^c -u %s ) ) = ( %s x. ( ( K ^c %s ) x. ( K ^c -u %s ) ) ) )' % (A2, ATMV('K'), T1, T1, ATMV('K'), T1, T1))
w.qed([w.s([val], 'oveq1d', '( %s -> ( ( %s ` K ) x. ( K ^c -u %s ) ) = ( ( %s x. ( K ^c %s ) ) x. ( K ^c -u %s ) ) )' % (A2, AA, T1, ATMV('K'), T1, T1)),
       w.s([assoc, w.s([w.s([pone], 'oveq2d', '( %s -> ( %s x. ( ( K ^c %s ) x. ( K ^c -u %s ) ) ) = ( %s x. 1 ) )' % (A2, ATMV('K'), T1, T1, ATMV('K'))),
                        w.s([atc], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A2, ATMV('K'), ATMV('K')))], 'eqtrd',
                       '( %s -> ( %s x. ( ( K ^c %s ) x. ( K ^c -u %s ) ) ) = %s )' % (A2, ATMV('K'), T1, T1, ATMV('K')))],
           'eqtrd', '( %s -> ( ( %s x. ( K ^c %s ) ) x. ( K ^c -u %s ) ) = %s )' % (A2, ATMV('K'), T1, T1, ATMV('K')))],
      'eqtrd', '( %s -> ( ( %s ` K ) x. ( K ^c -u %s ) ) = %s )' % (A2, AA, T1, ATMV('K')))
run4(w)

# ---------------------------------------------------------------- abzctx
def abctx(w, A1):
    """shared steps for the Abel series theorems"""
    d = {}
    d['sf'] = w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, ABS)), w.inst('simp1')], 'syl', '( %s -> S : NN --> CC )' % A1)
    d['br'] = w.s([w.s([], 'simpl', '( %s -> %s )' % (A1, ABS)), w.inst('simp2')], 'syl', '( %s -> B e. RR )' % A1)
    d['zc'] = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, ZPP)), w.inst('simpl')], 'syl', '( %s -> Z e. CC )' % A1)
    d['z0'] = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, ZPP)), w.inst('simpr')], 'syl', '( %s -> 0 < %s )' % (A1, RZ))
    d['rzr'] = w.s([d['zc']], 'recld', '( %s -> %s e. RR )' % (A1, RZ))
    d['one'] = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A1)
    d['t1r'] = w.s([d['rzr'], d['one']], 'readdcld', '( %s -> %s e. RR )' % (A1, T1))
    d['t1c'] = w.s([d['t1r']], 'recnd', '( %s -> %s e. CC )' % (A1, T1))
    d['ret1'] = w.s([d['t1r']], 'rered', '( %s -> ( Re ` %s ) = %s )' % (A1, T1, T1))
    z0r = w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A1)
    lt1 = w.s([w.s([w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % A1)], 'eqcomd',
                   '( %s -> 1 = ( 0 + 1 ) )' % A1),
               w.s([z0r, d['rzr'], d['one'], d['z0']], 'ltadd1dd', '( %s -> ( 0 + 1 ) < %s )' % (A1, T1))],
              'eqbrtrd', '( %s -> 1 < %s )' % (A1, T1))
    d['ltre'] = w.s([lt1, w.s([d['ret1']], 'eqcomd', '( %s -> %s = ( Re ` %s ) )' % (A1, T1, T1))], 'breqtrd',
                    '( %s -> 1 < ( Re ` %s ) )' % (A1, T1))
    d['zt'] = w.s([d['t1c'], d['ltre']], 'jca', '( %s -> ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (A1, T1, T1))
    d['cfb'] = w.s([w.s([], 'id', '( %s -> %s )' % (A1, A1)), w.inst('abcfb')], 'syl',
                   '( %s -> ( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s ) )' % (A1, AA, BZ, AA, BZ))
    d['sub'] = w.s([d['cfb'], d['zt']], 'jca',
                   '( %s -> ( ( %s : NN --> CC /\\ %s e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ %s ) /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) ) )' % (A1, AA, BZ, AA, BZ, T1, T1))
    return d


def sumrw(w, A1, d, idx):
    """( A1 -> sum_ idx e. NN ( ( AA ` idx ) x. ( idx ^c -u T1 ) ) = sum_ idx e. NN ATM(idx) )"""
    AK = '( %s /\\ %s e. NN )' % (A1, idx)
    kn = w.s([], 'simpr', '( %s -> %s e. NN )' % (AK, idx))
    mu = w.s([w.s([w.s([w.s([d['sf']], 'adantr', '( %s -> S : NN --> CC )' % AK),
                        w.s([d['zc']], 'adantr', '( %s -> Z e. CC )' % AK),
                        w.s([d['z0']], 'adantr', '( %s -> 0 < %s )' % (AK, RZ))], '3jca',
                       '( %s -> %s )' % (AK, SF)), kn], 'jca', '( %s -> ( %s /\\ %s e. NN ) )' % (AK, SF, idx)),
                w.inst('abmul')], 'syl',
               '( %s -> ( ( %s ` %s ) x. ( %s ^c -u %s ) ) = %s )' % (AK, AA, idx, idx, T1, ATMV(idx)))
    return w.s([mu], 'sumeq2dv',
               '( %s -> sum_ %s e. NN ( ( %s ` %s ) x. ( %s ^c -u %s ) ) = sum_ %s e. NN %s )' % (A1, idx, AA, idx, idx, T1, idx, ATMV(idx)))


# ---------------------------------------------------------------- abcl
w = W('abcl', 'The Abel series of a bounded partial-sum sequence converges absolutely '
      'on ` 0 < ( Re ` Z ) `, so its sum is a complex number ( ~ dsercl ).')
d = abctx(w, A1)
rw = sumrw(w, A1, d, 'k')
cl = w.s([d['sub'], w.inst('dsercl')], 'syl',
         '( %s -> sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u %s ) ) e. CC )' % (A1, AA, T1))
w.qed([rw, cl], 'eqeltrrd', '( %s -> sum_ k e. NN %s e. CC )' % (A1, ATMV('k')))
run4(w)

# ---------------------------------------------------------------- abcvg
w = W('abcvg', 'The Abel series of a bounded partial-sum sequence converges on '
      '` 0 < ( Re ` Z ) ` ( ~ dsercvg ).')
d = abctx(w, A1)
NM = '( n e. NN |-> ( ( %s ` n ) x. ( n ^c -u %s ) ) )' % (AA, T1)
cv = w.s([d['sub'], w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A1, NM))
AN = '( %s /\\ n e. NN )' % A1
mu = w.s([w.s([w.s([w.s([d['sf']], 'adantr', '( %s -> S : NN --> CC )' % AN),
                    w.s([d['zc']], 'adantr', '( %s -> Z e. CC )' % AN),
                    w.s([d['z0']], 'adantr', '( %s -> 0 < %s )' % (AN, RZ))], '3jca', '( %s -> %s )' % (AN, SF)),
                w.s([], 'simpr', '( %s -> n e. NN )' % AN)], 'jca', '( %s -> ( %s /\\ n e. NN ) )' % (AN, SF)),
            w.inst('abmul')], 'syl',
           '( %s -> ( ( %s ` n ) x. ( n ^c -u %s ) ) = %s )' % (AN, AA, T1, ATMV('n')))
mpe = w.s([mu], 'mpteq2dva', '( %s -> %s = ( n e. NN |-> %s ) )' % (A1, NM, ATMV('n')))
w.qed([w.s([mpe], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , ( n e. NN |-> %s ) ) )' % (A1, NM, ATMV('n'))), cv],
      'eqeltrrd' if False else 'dummy', 'x')
w.lines.pop()
w.qed([w.s([w.s([mpe], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , ( n e. NN |-> %s ) ) )' % (A1, NM, ATMV('n')))], 'eqcomd',
           '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) = seq 1 ( + , %s ) )' % (A1, ATMV('n'), NM)), cv], 'eqeltrd',
      '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (A1, ATMV('n')))
run4(w)

# ---------------------------------------------------------------- abbnd
w = W('abbnd', 'The Abel series bound on the right half-plane: a bounded partial-sum '
      'sequence gives ` ( B x. ( abs ` Z ) ) x. ( 1 + 1 / ( Re ` Z ) ) `.  This is '
      '` norm_Afun_le ` of Route Z\'s LGrowth.lean, whose ` N ` is the bound ` B ` on '
      'the character partial sums.')
d = abctx(w, A1)
rw = sumrw(w, A1, d, 'k')
bd = w.s([d['sub'], w.inst('dserbnd')], 'syl',
         '( %s -> ( abs ` sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u %s ) ) ) <_ ( %s x. ( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) ) )' % (A1, AA, T1, BZ, T1))
pc = w.s([d['rzr'], d['one'], w.s([d['rzr']], 'recnd', '( %s -> %s e. CC )' % (A1, RZ)),
          w.s([d['one']], 'recnd', '( %s -> 1 e. CC )' % A1)], 'jca', 'dummy')
w.lines.pop()
pcan = w.s([w.s([d['rzr']], 'recnd', '( %s -> %s e. CC )' % (A1, RZ)),
            w.s([d['one']], 'recnd', '( %s -> 1 e. CC )' % A1)], 'pncand',
           '( %s -> ( %s - 1 ) = %s )' % (A1, T1, RZ))
rew = w.s([w.s([d['ret1']], 'oveq1d', '( %s -> ( ( Re ` %s ) - 1 ) = ( %s - 1 ) )' % (A1, T1, T1)), pcan], 'eqtrd',
          '( %s -> ( ( Re ` %s ) - 1 ) = %s )' % (A1, T1, RZ))
rhs = w.s([w.s([w.s([rew], 'oveq2d', '( %s -> ( 1 / ( ( Re ` %s ) - 1 ) ) = ( 1 / %s ) )' % (A1, T1, RZ))], 'oveq2d',
               '( %s -> ( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) = ( 1 + ( 1 / %s ) ) )' % (A1, T1, RZ))], 'oveq2d',
          '( %s -> ( %s x. ( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) ) = ( %s x. ( 1 + ( 1 / %s ) ) ) )' % (A1, BZ, T1, BZ, RZ))
w.qed([w.s([w.s([rw], 'fveq2d', '( %s -> ( abs ` sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u %s ) ) ) = ( abs ` sum_ k e. NN %s ) )' % (A1, AA, T1, ATMV('k'))), bd],
           'eqbrtrrd', '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( %s x. ( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) ) )' % (A1, ATMV('k'), BZ, T1)),
       rhs], 'breqtrd', '( %s -> ( abs ` sum_ k e. NN %s ) <_ ( %s x. ( 1 + ( 1 / %s ) ) ) )' % (A1, ATMV('k'), BZ, RZ))
run4(w)
