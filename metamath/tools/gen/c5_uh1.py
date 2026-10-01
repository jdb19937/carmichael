"""C5, generic block 1: the partial-sum functions of a term-function sequence
(seqof), their closure, and the Weierstrass M-test."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

PS = PSQ('F')
GH = '( h e. NN |-> ( ( F ` h ) ` z ) )'
FM = FMAP('F')


def ghval(w, ante, i, mem, z='z'):
    """( ante -> ( GH ` i ) = ( ( F ` i ) ` z ) )"""
    s1 = w.s([], 'fveq2', '( h = %s -> ( F ` h ) = ( F ` %s ) )' % (i, i))
    s2 = w.s([s1], 'fveq1d', '( h = %s -> ( ( F ` h ) ` %s ) = ( ( F ` %s ) ` %s ) )' % (i, z, i, z))
    g = GH if z == 'z' else GH.replace('` z )', '` %s )' % z)
    return mpv(w, ante, g, i, '( ( F ` %s ) ` %s )' % (i, z), s2, mem, vexd(w, ante, '( ( F ` %s ) ` %s )' % (i, z), 'fv'))


# ---------------------------------------------------------------- uhps
w = W('uhps', 'The partial-sum functions of a term-function sequence: the N-th partial sum '
      'function is the pointwise finite sum ( ~ seqof , ~ fsumser ).')
A0 = '( %s /\\ N e. NN )' % FM
ff = w.s([], 'simpl', '( %s -> %s )' % (A0, FM))
nn = w.s([], 'simpr', '( %s -> N e. NN )' % A0)
nu1, z1, n1 = nnuz(w, A0)
ue = uex(w, A0, ff, n1)
nuz = w.s([nn, nu1], 'eleqtrdi', '( %s -> N e. ( ZZ>= ` 1 ) )' % A0)
# seqof.3
Ai = '( %s /\\ i e. ( 1 ... N ) )' % A0
inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... N ) )' % Ai), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
fif = fval(w, Ai, 'i', inn, w.s([ff], 'adantr', '( %s -> %s )' % (Ai, FM)))
fmp = w.s([fif], 'feqmptd', '( %s -> ( F ` i ) = ( z e. U |-> ( ( F ` i ) ` z ) ) )' % Ai)
gv = ghval(w, Ai, 'i', inn)
mpe = w.s([w.s([gv], 'eqcomd', '( %s -> ( ( F ` i ) ` z ) = ( %s ` i ) )' % (Ai, GH))], 'mpteq2dv',
          '( %s -> ( z e. U |-> ( ( F ` i ) ` z ) ) = ( z e. U |-> ( %s ` i ) ) )' % (Ai, GH))
h3 = w.s([fmp, mpe], 'eqtrd', '( %s -> ( F ` i ) = ( z e. U |-> ( %s ` i ) ) )' % (Ai, GH))
so = w.s([ue, nuz, h3], 'seqof', '( %s -> ( %s ` N ) = ( z e. U |-> ( seq 1 ( + , %s ) ` N ) ) )' % (A0, PS, GH))
# fsumser under z e. U
Az = '( %s /\\ z e. U )' % A0
Azk = '( %s /\\ k e. ( 1 ... N ) )' % Az
knn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... N ) )' % Azk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Azk)
gvk = ghval(w, Azk, 'k', knn)
fkf = fval(w, Azk, 'k', knn, w.s([ff], 'ad2antrr', '( %s -> %s )' % (Azk, FM)))
zu = w.s([], 'simplr', '( %s -> z e. U )' % Azk)
fkz = w.s([fkf, zu], 'ffvelcdmd', '( %s -> ( ( F ` k ) ` z ) e. CC )' % Azk)
fs = w.s([gvk, w.s([nuz], 'adantr', '( %s -> N e. ( ZZ>= ` 1 ) )' % Az), fkz], 'fsumser',
         '( %s -> sum_ k e. ( 1 ... N ) ( ( F ` k ) ` z ) = ( seq 1 ( + , %s ) ` N ) )' % (Az, GH))
mp2 = w.s([w.s([fs], 'eqcomd', '( %s -> ( seq 1 ( + , %s ) ` N ) = sum_ k e. ( 1 ... N ) ( ( F ` k ) ` z ) )' % (Az, GH))],
          'mpteq2dva', '( %s -> ( z e. U |-> ( seq 1 ( + , %s ) ` N ) ) = %s )' % (A0, GH, PSMAP('F', 'N')))
w.qed([so, mp2], 'eqtrd', '( %s -> ( %s ` N ) = %s )' % (A0, PS, PSMAP('F', 'N')))
run5(w)

# ---------------------------------------------------------------- uhpsf
w = W('uhpsf', 'The partial-sum functions of a term-function sequence form a sequence of '
      'functions on the same domain.')
A0 = FM
Ai = '( %s /\\ i e. NN )' % A0
nu1, z1, n1 = nnuz(w, A0)
ue = uex(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, FM)), n1)
inn = w.s([], 'simpr', '( %s -> i e. NN )' % Ai)
fmi = w.s([], 'simpl', '( %s -> %s )' % (Ai, FM))
psv = w.s([w.s([fmi, inn], 'jca', '( %s -> ( %s /\\ i e. NN ) )' % (Ai, FM)), w.inst('uhps')], 'syl',
          '( %s -> ( %s ` i ) = %s )' % (Ai, PS, PSMAP('F', 'i')))
Aiz = '( %s /\\ z e. U )' % Ai
Aizk = '( %s /\\ k e. ( 1 ... i ) )' % Aiz
knn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... i ) )' % Aizk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Aizk)
fkf = fval(w, Aizk, 'k', knn, w.s([fmi], 'ad2antrr', '( %s -> %s )' % (Aizk, FM)))
fkz = w.s([fkf, w.s([], 'simplr', '( %s -> z e. U )' % Aizk)], 'ffvelcdmd', '( %s -> ( ( F ` k ) ` z ) e. CC )' % Aizk)
scl = w.s([w.s([], 'fzfid', '( %s -> ( 1 ... i ) e. Fin )' % Aiz), fkz], 'fsumcl',
          '( %s -> sum_ k e. ( 1 ... i ) ( ( F ` k ) ` z ) e. CC )' % Aiz)
mf = w.s([scl, w.s([], 'eqid', '%s = %s' % (PSMAP('F', 'i'), PSMAP('F', 'i')))], 'fmptd',
         '( %s -> %s : U --> CC )' % (Ai, PSMAP('F', 'i')))
mm = elmapf(w, Ai, PSMAP('F', 'i'), w.s([ue], 'adantr', '( %s -> U e. _V )' % Ai), mf)
el = w.s([psv, mm], 'eqeltrd', '( %s -> ( %s ` i ) e. ( CC ^m U ) )' % (Ai, PS))
ral = w.s([el], 'ralrimiva', '( %s -> A. i e. NN ( %s ` i ) e. ( CC ^m U ) )' % (A0, PS))
fn0 = w.s([z1, w.inst('seqfn')], 'syl', '( %s -> %s Fn ( ZZ>= ` 1 ) )' % (A0, PS))
u1n = w.s([w.s([nu1], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A0)
fneq = w.s([u1n], 'fneq2d', '( %s -> ( %s Fn ( ZZ>= ` 1 ) <-> %s Fn NN ) )' % (A0, PS, PS))
fn = w.s([fn0, fneq], 'mpbid', '( %s -> %s Fn NN )' % (A0, PS))
bi = w.s([], 'ffnfv', '( %s : NN --> ( CC ^m U ) <-> ( %s Fn NN /\\ A. i e. NN ( %s ` i ) e. ( CC ^m U ) ) )' % (PS, PS, PS))
w.qed([w.s([fn, ral], 'jca', '( %s -> ( %s Fn NN /\\ A. i e. NN ( %s ` i ) e. ( CC ^m U ) ) )' % (A0, PS, PS)),
       w.s([bi], 'a1i', '( %s -> ( %s : NN --> ( CC ^m U ) <-> ( %s Fn NN /\\ A. i e. NN ( %s ` i ) e. ( CC ^m U ) ) ) )' % (A0, PS, PS, PS))],
      'mpbird', '( %s -> %s : NN --> ( CC ^m U ) )' % (A0, PS))
run5(w)

# ---------------------------------------------------------------- uhmt
w = W('uhmt', 'The Weierstrass M-test for a term-function sequence with a summable majorant: '
      'the partial-sum functions converge uniformly ( ~ mtest ).')
A0 = UHS()
UM = UHM('F', 'M')
ff = w.s([], 'simpl', '( %s -> %s )' % (A0, FM))
um = w.s([], 'simpr', '( %s -> %s )' % (A0, UM))
mf = w.s([um, w.inst('simp1')], 'syl', '( %s -> M : NN --> RR )' % A0)
mcv = w.s([um, w.inst('simp2')], 'syl', '( %s -> seq 1 ( + , M ) e. dom ~~> )' % A0)
mb = w.s([um, w.inst('simp3')], 'syl', '( %s -> A. j e. NN A. y e. U ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j ) )' % A0)
nu1, z1, n1 = nnuz(w, A0)
ue = uex(w, A0, ff, n1)
mex = w.s([mf, a1(w, A0, 'nnex', 'NN e. _V'), w.inst('fex')], 'syl2anc', '( %s -> M e. _V )' % A0)
Ai = '( %s /\\ i e. NN )' % A0
mc = w.s([w.s([mf], 'adantr', '( %s -> M : NN --> RR )' % Ai), w.s([], 'simpr', '( %s -> i e. NN )' % Ai)], 'ffvelcdmd',
         '( %s -> ( M ` i ) e. RR )' % Ai)
Aiw = '( %s /\\ ( i e. NN /\\ w e. U ) )' % A0
s1 = w.s([w.s([w.s([], 'fveq2', '( j = i -> ( F ` j ) = ( F ` i ) )')], 'fveq1d',
              '( j = i -> ( ( F ` j ) ` y ) = ( ( F ` i ) ` y ) )')], 'fveq2d',
         '( j = i -> ( abs ` ( ( F ` j ) ` y ) ) = ( abs ` ( ( F ` i ) ` y ) ) )')
s2 = w.s([], 'fveq2', '( j = i -> ( M ` j ) = ( M ` i ) )')
sb1 = w.s([s1, s2], 'breq12d', '( j = i -> ( ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j ) <-> ( abs ` ( ( F ` i ) ` y ) ) <_ ( M ` i ) ) )')
s3 = w.s([w.s([], 'fveq2', '( y = w -> ( ( F ` i ) ` y ) = ( ( F ` i ) ` w ) )')], 'fveq2d',
         '( y = w -> ( abs ` ( ( F ` i ) ` y ) ) = ( abs ` ( ( F ` i ) ` w ) ) )')
sb2 = w.s([s3], 'breq1d', '( y = w -> ( ( abs ` ( ( F ` i ) ` y ) ) <_ ( M ` i ) <-> ( abs ` ( ( F ` i ) ` w ) ) <_ ( M ` i ) ) )')
bnd = w.s([sb1, sb2, w.s([mb], 'adantr', '( %s -> A. j e. NN A. y e. U ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j ) )' % Aiw),
           w.s([], 'simprl', '( %s -> i e. NN )' % Aiw), w.s([], 'simprr', '( %s -> w e. U )' % Aiw)], 'rspc2dv',
          '( %s -> ( abs ` ( ( F ` i ) ` w ) ) <_ ( M ` i ) )' % Aiw)
w.qed([nu1, z1, ue, ff, mex, mc, bnd, mcv], 'mtest', '( %s -> %s e. dom ( ~~>u ` U ) )' % (A0, PS))
run5(w)
