"""Sortie A4a, batch 0: the arithmetic of Nat.sqrt and Nat.log that AlgScan's
cost theorems consume.  MM_DB=sorties/a4a.mm python3 tools/gen/a4a_num.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1lib
from tm import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

def SQ(a): return '( Nfloor ` ( sqrt ` %s ) )' % a
def FL(a): return '( |_ ` ( sqrt ` %s ) )' % a

# --------------------------------------------------------------- nsqrtcl
w = W('nsqrtcl', 'Closure of the integer square root (Lean: Nat.sqrt a : Nat).')
A = 'A e. NN0'
i = w.s([], 'id', '( %s -> A e. NN0 )' % A)
ar = w.s([i], 'nn0red', '( %s -> A e. RR )' % A)
a0 = w.s([i], 'nn0ge0d', '( %s -> 0 <_ A )' % A)
sq = w.s([ar, a0, w.inst('resqrtcl')], 'syl2anc', '( %s -> ( sqrt ` A ) e. RR )' % A)
w.qed([sq, w.inst('nfloorcl')], 'syl', '( %s -> %s e. NN0 )' % (A, SQ('A')))
run(w)

# --------------------------------------------------------------- nsqrtfl
w = W('nsqrtfl', 'The integer square root is the floor of the real square root.')
i = w.s([], 'id', '( %s -> A e. NN0 )' % A)
ar = w.s([i], 'nn0red', '( %s -> A e. RR )' % A)
a0 = w.s([i], 'nn0ge0d', '( %s -> 0 <_ A )' % A)
sq = w.s([ar, a0, w.inst('resqrtcl')], 'syl2anc', '( %s -> ( sqrt ` A ) e. RR )' % A)
g0 = w.s([ar, a0, w.inst('sqrtge0')], 'syl2anc', '( %s -> 0 <_ ( sqrt ` A ) )' % A)
w.qed([sq, g0, w.inst('nfloorfl')], 'syl2anc', '( %s -> %s = %s )' % (A, SQ('A'), FL('A')))
run(w)

# --------------------------------------------------------------- nsqrtle
w = W('nsqrtle', 'Characterisation of the integer square root (Lean: Nat.le_sqrt).')
P = '( E e. NN0 /\\ A e. NN0 )'
e0 = w.s([], 'simpl', '( %s -> E e. NN0 )' % P)
a0m = w.s([], 'simpr', '( %s -> A e. NN0 )' % P)
er = w.s([e0], 'nn0red', '( %s -> E e. RR )' % P)
ecn = w.s([e0], 'nn0cnd', '( %s -> E e. CC )' % P)
ez = w.s([e0], 'nn0zd', '( %s -> E e. ZZ )' % P)
ege = w.s([e0], 'nn0ge0d', '( %s -> 0 <_ E )' % P)
ar = w.s([a0m], 'nn0red', '( %s -> A e. RR )' % P)
age = w.s([a0m], 'nn0ge0d', '( %s -> 0 <_ A )' % P)
# ( sqrt ` ( E x. E ) ) = E
sv = w.s([ecn, w.inst('sqval')], 'syl', '( %s -> ( E ^ 2 ) = ( E x. E ) )' % P)
ss = w.s([er, ege, w.inst('sqrtsq')], 'syl2anc', '( %s -> ( sqrt ` ( E ^ 2 ) ) = E )' % P)
sv2 = w.s([sv], 'fveq2d', '( %s -> ( sqrt ` ( E ^ 2 ) ) = ( sqrt ` ( E x. E ) ) )' % P)
sqe = w.s([sv2, ss], 'eqtr3d', '( %s -> ( sqrt ` ( E x. E ) ) = E )' % P)
# ( E x. E ) e. RR, 0 <_ ( E x. E )
ee = w.s([e0, e0], 'nn0mulcld', '( %s -> ( E x. E ) e. NN0 )' % P)
eer = w.s([ee], 'nn0red', '( %s -> ( E x. E ) e. RR )' % P)
eeg = w.s([ee], 'nn0ge0d', '( %s -> 0 <_ ( E x. E ) )' % P)
b1 = w.s([w.s([eer, eeg], 'jca', '( %s -> ( ( E x. E ) e. RR /\\ 0 <_ ( E x. E ) ) )' % P),
          w.s([ar, age], 'jca', '( %s -> ( A e. RR /\\ 0 <_ A ) )' % P), w.inst('sqrtle')], 'syl2anc',
         '( %s -> ( ( E x. E ) <_ A <-> ( sqrt ` ( E x. E ) ) <_ ( sqrt ` A ) ) )' % P)
b2 = w.s([sqe], 'breq1d', '( %s -> ( ( sqrt ` ( E x. E ) ) <_ ( sqrt ` A ) <-> E <_ ( sqrt ` A ) ) )' % P)
b3 = w.s([b1, b2], 'bitrd', '( %s -> ( ( E x. E ) <_ A <-> E <_ ( sqrt ` A ) ) )' % P)
sqr = w.s([ar, age, w.inst('resqrtcl')], 'syl2anc', '( %s -> ( sqrt ` A ) e. RR )' % P)
b4 = w.s([sqr, ez, w.inst('flge')], 'syl2anc', '( %s -> ( E <_ ( sqrt ` A ) <-> E <_ %s ) )' % (P, FL('A')))
b5 = w.s([b3, b4], 'bitrd', '( %s -> ( ( E x. E ) <_ A <-> E <_ %s ) )' % (P, FL('A')))
fl = w.s([a0m, w.inst('nsqrtfl')], 'syl', '( %s -> %s = %s )' % (P, SQ('A'), FL('A')))
b6 = w.s([fl], 'breq2d', '( %s -> ( E <_ %s <-> E <_ %s ) )' % (P, SQ('A'), FL('A')))
w.qed([b6, b5], 'bitr4d', '( %s -> ( E <_ %s <-> ( E x. E ) <_ A ) )' % (P, SQ('A')))
run(w)

# --------------------------------------------------------------- nsqrtmo
w = W('nsqrtmo', 'The integer square root is monotone (Lean: Nat.sqrt_le_sqrt).')
P = '( ( A e. NN0 /\\ C e. NN0 ) /\\ A <_ C )'
an = w.s([], 'simpll', '( %s -> A e. NN0 )' % P)
cn = w.s([], 'simplr', '( %s -> C e. NN0 )' % P)
ac = w.s([], 'simpr', '( %s -> A <_ C )' % P)
sa = w.s([an, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (P, SQ('A')))
h1 = w.s([sa, an, w.inst('nsqrtle')], 'syl2anc', '( %s -> ( %s <_ %s <-> ( %s x. %s ) <_ A ) )' % (P, SQ('A'), SQ('A'), SQ('A'), SQ('A')))
id1 = w.s([], 'leidd', '( %s -> %s <_ %s )' % (P, SQ('A'), SQ('A')))
h2 = w.s([h1, id1], 'mpbid', '( %s -> ( %s x. %s ) <_ A )' % (P, SQ('A'), SQ('A')))
mm = w.s([sa, sa], 'nn0mulcld', '( %s -> ( %s x. %s ) e. NN0 )' % (P, SQ('A'), SQ('A')))
mr = w.s([mm], 'nn0red', '( %s -> ( %s x. %s ) e. RR )' % (P, SQ('A'), SQ('A')))
ar = w.s([an], 'nn0red', '( %s -> A e. RR )' % P)
cr = w.s([cn], 'nn0red', '( %s -> C e. RR )' % P)
h3 = w.s([mr, ar, cr, h2, ac], 'letrd', '( %s -> ( %s x. %s ) <_ C )' % (P, SQ('A'), SQ('A')))
h4 = w.s([sa, cn, w.inst('nsqrtle')], 'syl2anc', '( %s -> ( %s <_ %s <-> ( %s x. %s ) <_ C ) )' % (P, SQ('A'), SQ('C'), SQ('A'), SQ('A')))
w.qed([h4, h3], 'mpbird', '( %s -> %s <_ %s )' % (P, SQ('A'), SQ('C')))
run(w)

NL = lambda b, n: '( %s Nlog %s )' % (b, n)

# --------------------------------------------------------------- nlogz
w = W('nlogz', 'Nlog is zero outside its main case (Lean: Nat.log_of_lt / Nat.log_zero_right).')
P = '( ( B e. NN0 /\\ N e. NN0 ) /\\ -. ( 2 <_ B /\\ 1 <_ N ) )'
IFB = 'if ( ( 2 <_ B /\\ 1 <_ N ) , ( |_ ` ( B logb N ) ) , 0 )'
b0 = w.s([], 'simpll', '( %s -> B e. NN0 )' % P)
n0 = w.s([], 'simplr', '( %s -> N e. NN0 )' % P)
v = w.s([b0, n0, w.inst('nlogval')], 'syl2anc', '( %s -> %s = %s )' % (P, NL('B', 'N'), IFB))
nf = w.s([], 'simpr', '( %s -> -. ( 2 <_ B /\\ 1 <_ N ) )' % P)
fa = w.s([nf], 'iffalsed', '( %s -> %s = 0 )' % (P, IFB))
w.qed([v, fa], 'eqtrd', '( %s -> %s = 0 )' % (P, NL('B', 'N')))
run(w)

# --------------------------------------------------------------- nlogmo
w = W('nlogmo', 'Nlog is monotone in its argument (Lean: Nat.log_mono_right).')
P = '( ( B e. ( ZZ>= ` 2 ) /\\ ( A e. NN0 /\\ C e. NN0 ) ) /\\ A <_ C )'
ub = w.s([], 'simpll', '( %s -> B e. ( ZZ>= ` 2 ) )' % P)
an = w.s([], 'simplrl', '( %s -> A e. NN0 )' % P)
cn = w.s([], 'simplrr', '( %s -> C e. NN0 )' % P)
ac = w.s([], 'simpr', '( %s -> A <_ C )' % P)
bn = w.s([w.s([ub, w.inst('eluz2nn')], 'syl', '( %s -> B e. NN )' % P)], 'nnnn0d', '( %s -> B e. NN0 )' % P)
# case 1 <_ A
Q = '( %s /\\ 1 <_ A )' % P
ubq = w.s([ub], 'adantr', '( %s -> B e. ( ZZ>= ` 2 ) )' % Q)
anq = w.s([an], 'adantr', '( %s -> A e. NN0 )' % Q)
cnq = w.s([cn], 'adantr', '( %s -> C e. NN0 )' % Q)
acq = w.s([ac], 'adantr', '( %s -> A <_ C )' % Q)
bnq = w.s([bn], 'adantr', '( %s -> B e. NN0 )' % Q)
a1q = w.s([], 'simpr', '( %s -> 1 <_ A )' % Q)
ann = w.s([anq, a1q, w.inst('elnnnn0c')], 'sylanbrc', '( %s -> A e. NN )' % Q)
arq = w.s([anq], 'nn0red', '( %s -> A e. RR )' % Q)
crq = w.s([cnq], 'nn0red', '( %s -> C e. RR )' % Q)
o1 = w.s([], '1red', '( %s -> 1 e. RR )' % Q)
c1q = w.s([o1, arq, crq, a1q, acq], 'letrd', '( %s -> 1 <_ C )' % Q)
cnn = w.s([cnq, c1q, w.inst('elnnnn0c')], 'sylanbrc', '( %s -> C e. NN )' % Q)
kn = w.s([bnq, anq, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (Q, NL('B', 'A')))
le = w.s([ubq, ann, w.inst('nlogle')], 'syl2anc', '( %s -> ( B ^ %s ) <_ A )' % (Q, NL('B', 'A')))
bnn = w.s([ubq, w.inst('eluz2nn')], 'syl', '( %s -> B e. NN )' % Q)
exn = w.s([w.s([bnn], 'nnnn0d', '( %s -> B e. NN0 )' % Q), kn], 'nn0expcld', '( %s -> ( B ^ %s ) e. NN0 )' % (Q, NL('B', 'A')))
exr = w.s([exn], 'nn0red', '( %s -> ( B ^ %s ) e. RR )' % (Q, NL('B', 'A')))
le2 = w.s([exr, arq, crq, le, acq], 'letrd', '( %s -> ( B ^ %s ) <_ C )' % (Q, NL('B', 'A')))
ubb = w.s([w.s([ubq, cnn], 'jca', '( %s -> ( B e. ( ZZ>= ` 2 ) /\\ C e. NN ) )' % Q),
           w.s([kn, le2], 'jca', '( %s -> ( %s e. NN0 /\\ ( B ^ %s ) <_ C ) )' % (Q, NL('B', 'A'), NL('B', 'A'))),
           w.inst('nlogub')], 'syl2anc', '( %s -> %s <_ %s )' % (Q, NL('B', 'A'), NL('B', 'C')))
# case -. 1 <_ A
R = '( %s /\\ -. 1 <_ A )' % P
bnr = w.s([bn], 'adantr', '( %s -> B e. NN0 )' % R)
anr = w.s([an], 'adantr', '( %s -> A e. NN0 )' % R)
cnr = w.s([cn], 'adantr', '( %s -> C e. NN0 )' % R)
na1 = w.s([], 'simpr', '( %s -> -. 1 <_ A )' % R)
nca = w.s([na1], 'intnand', '( %s -> -. ( 2 <_ B /\\ 1 <_ A ) )' % R)
z = w.s([w.s([bnr, anr], 'jca', '( %s -> ( B e. NN0 /\\ A e. NN0 ) )' % R), nca, w.inst('nlogz')], 'syl2anc',
        '( %s -> %s = 0 )' % (R, NL('B', 'A')))
ccl = w.s([bnr, cnr, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (R, NL('B', 'C')))
cg0 = w.s([ccl], 'nn0ge0d', '( %s -> 0 <_ %s )' % (R, NL('B', 'C')))
lr = w.s([z, cg0], 'eqbrtrd', '( %s -> %s <_ %s )' % (R, NL('B', 'A'), NL('B', 'C')))
w.qed([ubb, lr], 'pm2.61dan', '( %s -> %s <_ %s )' % (P, NL('B', 'A'), NL('B', 'C')))
run(w)

# --------------------------------------------------------------- nlogsuc
w = W('nlogsuc', 'One more power of the base fits below R (Lean: Nat.log_mul_base with Nat.log_mono_right).')
P = '( ( B e. ( ZZ>= ` 2 ) /\\ ( S e. NN /\\ R e. NN ) ) /\\ ( S x. B ) <_ R )'
ub = w.s([], 'simpll', '( %s -> B e. ( ZZ>= ` 2 ) )' % P)
sn = w.s([], 'simplrl', '( %s -> S e. NN )' % P)
rn = w.s([], 'simplrr', '( %s -> R e. NN )' % P)
sb = w.s([], 'simpr', '( %s -> ( S x. B ) <_ R )' % P)
bnn = w.s([ub, w.inst('eluz2nn')], 'syl', '( %s -> B e. NN )' % P)
bn0 = w.s([bnn], 'nnnn0d', '( %s -> B e. NN0 )' % P)
sn0 = w.s([sn], 'nnnn0d', '( %s -> S e. NN0 )' % P)
kn = w.s([bn0, sn0, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (P, NL('B', 'S')))
K = NL('B', 'S')
le = w.s([ub, sn, w.inst('nlogle')], 'syl2anc', '( %s -> ( B ^ %s ) <_ S )' % (P, K))
bcn = w.s([bn0], 'nn0cnd', '( %s -> B e. CC )' % P)
pp = w.s([bcn, kn, w.inst('expp1')], 'syl2anc', '( %s -> ( B ^ ( %s + 1 ) ) = ( ( B ^ %s ) x. B ) )' % (P, K, K))
exn = w.s([bn0, kn], 'nn0expcld', '( %s -> ( B ^ %s ) e. NN0 )' % (P, K))
exr = w.s([exn], 'nn0red', '( %s -> ( B ^ %s ) e. RR )' % (P, K))
sr = w.s([sn0], 'nn0red', '( %s -> S e. RR )' % P)
br = w.s([bn0], 'nn0red', '( %s -> B e. RR )' % P)
bg0 = w.s([bn0], 'nn0ge0d', '( %s -> 0 <_ B )' % P)
m1 = w.s([exr, sr, br, bg0, le], 'lemul1ad', '( %s -> ( ( B ^ %s ) x. B ) <_ ( S x. B ) )' % (P, K))
mr = w.s([exr, br], 'remulcld', '( %s -> ( ( B ^ %s ) x. B ) e. RR )' % (P, K))
sbr = w.s([sr, br], 'remulcld', '( %s -> ( S x. B ) e. RR )' % P)
rr = w.s([rn], 'nnred', '( %s -> R e. RR )' % P)
m2 = w.s([mr, sbr, rr, m1, sb], 'letrd', '( %s -> ( ( B ^ %s ) x. B ) <_ R )' % (P, K))
m3 = w.s([pp, m2], 'eqbrtrd', '( %s -> ( B ^ ( %s + 1 ) ) <_ R )' % (P, K))
k1 = w.s([kn, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (P, K))
w.qed([w.s([ub, rn], 'jca', '( %s -> ( B e. ( ZZ>= ` 2 ) /\\ R e. NN ) )' % P),
       w.s([k1, m3], 'jca', '( %s -> ( ( %s + 1 ) e. NN0 /\\ ( B ^ ( %s + 1 ) ) <_ R ) )' % (P, K, K)),
       w.inst('nlogub')], 'syl2anc', '( %s -> ( %s + 1 ) <_ %s )' % (P, K, NL('B', 'R')))
run(w)
