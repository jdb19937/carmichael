"""Sortie A2, batch 2: elementary logarithm, square-root and real-power facts."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

Q99 = '( ; 9 9 / ; ; 1 0 0 )'


def sqrtle2(w, ante, X, Y, xr, x0, yr, y0, hle):
    """( ante -> ( sqrt ` X ) <_ Y ) from hle : ( ante -> X <_ ( Y ^ 2 ) )"""
    ysq = w.s([yr], 'resqcld', '( %s -> ( %s ^ 2 ) e. RR )' % (ante, Y))
    ysq0 = w.s([yr], 'sqge0d', '( %s -> 0 <_ ( %s ^ 2 ) )' % (ante, Y))
    bi = w.s([xr, x0, ysq, ysq0, w.inst('sqrtle')], 'syl22anc',
             '( %s -> ( %s <_ ( %s ^ 2 ) <-> ( sqrt ` %s ) <_ ( sqrt ` ( %s ^ 2 ) ) ) )' % (ante, X, Y, X, Y))
    st = w.s([hle, bi], 'mpbid', '( %s -> ( sqrt ` %s ) <_ ( sqrt ` ( %s ^ 2 ) ) )' % (ante, X, Y))
    eq = w.s([yr, y0, w.inst('sqrtsq')], 'syl2anc', '( %s -> ( sqrt ` ( %s ^ 2 ) ) = %s )' % (ante, Y, Y))
    return w.s([st, eq], 'breqtrd', '( %s -> ( sqrt ` %s ) <_ %s )' % (ante, X, Y))


# ------------------------------------------------------------------ loglet
w = W('loglet', 'log A <_ A for A >_ 1 (Lean: Real.log_le_sub_one_of_pos).')
A = '( A e. RR /\\ 1 <_ A )'
ar = w.s([], 'simpl', '( %s -> A e. RR )' % A)
a1 = w.s([], 'simpr', '( %s -> 1 <_ A )' % A)
one = w.s([], '1red', '( %s -> 1 e. RR )' % A)
am1 = w.s([ar, one], 'resubcld', '( %s -> ( A - 1 ) e. RR )' % A)
am10 = linarith(w, A, [a1], '0 <_ ( A - 1 )', leaves={'A': ar})
a0 = linarith(w, A, [a1], '0 <_ A', leaves={'A': ar})
ls = w.s([am1, am10, w.inst('loglesqrt')], 'syl2anc',
         '( %s -> ( log ` ( ( A - 1 ) + 1 ) ) <_ ( sqrt ` ( A - 1 ) ) )' % A)
acn = w.s([ar], 'recnd', '( %s -> A e. CC )' % A)
onec = w.s([], 'ax-1cn', '1 e. CC')
onecd = w.s([onec], 'a1i', '( %s -> 1 e. CC )' % A)
np = w.s([acn, onecd], 'npcand', '( %s -> ( ( A - 1 ) + 1 ) = A )' % A)
ls2 = w.s([np], 'fveq2d', '( %s -> ( log ` ( ( A - 1 ) + 1 ) ) = ( log ` A ) )' % A)
ls3 = w.s([ls2, ls], 'eqbrtrrd', '( %s -> ( log ` A ) <_ ( sqrt ` ( A - 1 ) ) )' % A)
asq = w.s([ar], 'resqcld', '( %s -> ( A ^ 2 ) e. RR )' % A)
amul = w.s([ar, ar, a0, a1], 'lemul1ad', '( %s -> ( 1 x. A ) <_ ( A x. A ) )' % A)
oneA = w.s([acn], 'mullidd', '( %s -> ( 1 x. A ) = A )' % A)
svA = w.s([acn], 'sqvald', '( %s -> ( A ^ 2 ) = ( A x. A ) )' % A)
aa = w.s([w.s([oneA], 'eqcomd', '( %s -> A = ( 1 x. A ) )' % A), amul], 'eqbrtrd', '( %s -> A <_ ( A x. A ) )' % A)
aa2 = w.s([aa, w.s([svA], 'eqcomd', '( %s -> ( A x. A ) = ( A ^ 2 ) )' % A)], 'breqtrd', '( %s -> A <_ ( A ^ 2 ) )' % A)
mle = linarith(w, A, [aa2, a1], '( A - 1 ) <_ ( A ^ 2 )', leaves={'A': ar, '( A ^ 2 )': asq})
sq = sqrtle2(w, A, '( A - 1 )', 'A', am1, am10, ar, a0, mle)
sqr = w.s([am1, am10, w.inst('resqrtcl')], 'syl2anc', '( %s -> ( sqrt ` ( A - 1 ) ) e. RR )' % A)
apos = linarith(w, A, [a1], '0 < A', leaves={'A': ar})
arp = w.s([ar, apos], 'elrpd', '( %s -> A e. RR+ )' % A)
logr = w.s([arp, w.inst('relogcl')], 'syl', '( %s -> ( log ` A ) e. RR )' % A)
w.qed([logr, sqr, ar, ls3, sq], 'letrd', '( %s -> ( log ` A ) <_ A )' % A)
run(w)

# ------------------------------------------------------------------ log2ge
w = W('log2ge', 'A crude lower bound on log 2 (replaces Lean s Real.log_two_gt_d9).')
r1 = w.s([], '1rp', '1 e. RR+')
ld = w.s([r1, w.inst('logdiflbnd')], 'ax-mp', '( 1 / ( 1 + 1 ) ) <_ ( ( log ` ( 1 + 1 ) ) - ( log ` 1 ) )')
e2 = w.s([], '1p1e2', '( 1 + 1 ) = 2')
o1 = w.s([e2], 'oveq2i', '( 1 / ( 1 + 1 ) ) = ( 1 / 2 )')
f1 = w.s([e2], 'fveq2i', '( log ` ( 1 + 1 ) ) = ( log ` 2 )')
l0 = w.s([], 'log1', '( log ` 1 ) = 0')
d1 = w.s([f1, l0], 'oveq12i', '( ( log ` ( 1 + 1 ) ) - ( log ` 1 ) ) = ( ( log ` 2 ) - 0 )')
lr = w.s([], 'relogcl', '( 2 e. RR+ -> ( log ` 2 ) e. RR )')
r2 = w.s([], '2rp', '2 e. RR+')
lrr = w.s([r2, lr], 'ax-mp', '( log ` 2 ) e. RR')
lcn = w.s([lrr], 'recni', '( log ` 2 ) e. CC')
s0 = w.s([lcn], 'subid1i', '( ( log ` 2 ) - 0 ) = ( log ` 2 )')
d2 = w.s([d1, s0], 'eqtri', '( ( log ` ( 1 + 1 ) ) - ( log ` 1 ) ) = ( log ` 2 )')
b1 = w.s([o1, d2], 'breq12i', '( ( 1 / ( 1 + 1 ) ) <_ ( ( log ` ( 1 + 1 ) ) - ( log ` 1 ) ) <-> ( 1 / 2 ) <_ ( log ` 2 ) )')
w.qed([ld, b1], 'mpbi', '( 1 / 2 ) <_ ( log ` 2 )')
run(w)

# ------------------------------------------------------------------ expell2
w = W('expell2', 'exp ( R ell2 N ) = ( log N ) ^c R.')
A = '( N e. ( ZZ>= ` 3 ) /\\ R e. RR )'
LN = '( log ` N )'; L2N = '( ell2 ` N )'
n3 = w.s([], 'simpl', '( %s -> N e. ( ZZ>= ` 3 ) )' % A)
rr = w.s([], 'simpr', '( %s -> R e. RR )' % A)
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> N e. ( ZZ>= ` 2 ) )' % A)
nn = w.s([n2, w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % A)
n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A)
nrp = w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % A)
lnr = w.s([nrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A, LN))
gt1 = w.s([n2, w.inst('eluz2gt1')], 'syl', '( %s -> 1 < N )' % A)
bi = w.s([nrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < %s <-> 1 < N ) )' % (A, LN))
lpos = w.s([gt1, bi], 'mpbird', '( %s -> 0 < %s )' % (A, LN))
lrp = w.s([lnr, lpos], 'elrpd', '( %s -> %s e. RR+ )' % (A, LN))
lcn = w.s([lnr], 'recnd', '( %s -> %s e. CC )' % (A, LN))
lne0 = w.s([lrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A, LN))
rcn = w.s([rr], 'recnd', '( %s -> R e. CC )' % A)
ce = w.s([lcn, lne0, rcn, w.inst('cxpef')], 'syl3anc',
         '( %s -> ( %s ^c R ) = ( exp ` ( R x. ( log ` %s ) ) ) )' % (A, LN, LN))
iv = w.s([n0, w.inst('ell2val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, L2N, LN))
iv2 = w.s([iv], 'eqcomd', '( %s -> ( log ` %s ) = %s )' % (A, LN, L2N))
oe = w.s([iv2], 'oveq2d', '( %s -> ( R x. ( log ` %s ) ) = ( R x. %s ) )' % (A, LN, L2N))
fe = w.s([oe], 'fveq2d', '( %s -> ( exp ` ( R x. ( log ` %s ) ) ) = ( exp ` ( R x. %s ) ) )' % (A, LN, L2N))
ce2 = w.s([ce, fe], 'eqtrd', '( %s -> ( %s ^c R ) = ( exp ` ( R x. %s ) ) )' % (A, LN, L2N))
w.qed([ce2], 'eqcomd', '( %s -> ( exp ` ( R x. %s ) ) = ( %s ^c R ) )' % (A, L2N, LN))
run(w)

# ------------------------------------------------------------------ cxpge3
w = W('cxpge3', '3 <_ A ^c ( 99 / 100 ) for A >_ 9 (Lean: Step3W.lean hrw3).')
A = '( A e. RR /\\ 9 <_ A )'
ar = w.s([], 'simpl', '( %s -> A e. RR )' % A)
a9 = w.s([], 'simpr', '( %s -> 9 <_ A )' % A)
n9 = w.s([], '9re', '9 e. RR'); n9d = w.s([n9], 'a1i', '( %s -> 9 e. RR )' % A)
n90 = w.s([], '9pos', '0 < 9')
n90d = w.s([w.s([w.s([], '0re', '0 e. RR'), n9, n90], 'ltleii', '0 <_ 9')], 'a1i', '( %s -> 0 <_ 9 )' % A)
a0 = linarith(w, A, [a9], '0 <_ A', leaves={'A': ar})
q99 = w.s([num.fact(w, Q99, 'RR')], 'a1i', '( %s -> %s e. RR )' % (A, Q99))
q990 = w.s([num.fact(w, Q99, 'ge0')], 'a1i', '( %s -> 0 <_ %s )' % (A, Q99))
# 9 ^c ( 1 / 2 ) = 3
n9c = w.s([n9], 'recni', '9 e. CC')
cs = w.s([n9c, w.inst('cxpsqrt')], 'ax-mp', '( 9 ^c ( 1 / 2 ) ) = ( sqrt ` 9 )')
s3 = w.s([], 'sq3', '( 3 ^ 2 ) = 9')
r3 = w.s([], '3re', '3 e. RR'); p3 = w.s([], '3pos', '0 < 3')
le3 = w.s([w.s([], '0re', '0 e. RR'), r3, p3], 'ltleii', '0 <_ 3')
ss = w.s([r3, le3, w.inst('sqrtsq')], 'mp2an', '( sqrt ` ( 3 ^ 2 ) ) = 3')
ss2 = w.s([s3], 'fveq2i', '( sqrt ` ( 3 ^ 2 ) ) = ( sqrt ` 9 )')
sq9 = w.s([w.s([ss2], 'eqcomi', '( sqrt ` 9 ) = ( sqrt ` ( 3 ^ 2 ) )'), ss], 'eqtri', '( sqrt ` 9 ) = 3')
c9 = w.s([cs, sq9], 'eqtri', '( 9 ^c ( 1 / 2 ) ) = 3')
c9d = w.s([c9], 'a1i', '( %s -> ( 9 ^c ( 1 / 2 ) ) = 3 )' % A)
# 9 ^c ( 1 / 2 ) <_ 9 ^c ( 99 / 100 )
h12 = w.s([num.fact(w, '( 1 / 2 )', 'RR')], 'a1i', '( %s -> ( 1 / 2 ) e. RR )' % A)
le12 = linarith(w, A, [], '( 1 / 2 ) <_ %s' % Q99, leaves={})
n91c = w.s([w.s([], '1re', '1 e. RR'), n9, w.s([], '1lt9', '1 < 9')], 'ltleii', '1 <_ 9')
n91 = w.s([n91c], 'a1i', '( %s -> 1 <_ 9 )' % A)
cx1 = w.s([n9d, n91, h12, q99, le12], 'cxplead', '( %s -> ( 9 ^c ( 1 / 2 ) ) <_ ( 9 ^c %s ) )' % (A, Q99))
cx2 = w.s([n9d, ar, q99, n90d, q990, a9], 'cxple2ad', '( %s -> ( 9 ^c %s ) <_ ( A ^c %s ) )' % (A, Q99, Q99))
r3d = w.s([r3], 'a1i', '( %s -> 3 e. RR )' % A)
c9r = w.s([c9d], 'eqcomd', '( %s -> 3 = ( 9 ^c ( 1 / 2 ) ) )' % A)
c91 = w.s([c9r, cx1], 'eqbrtrd', '( %s -> 3 <_ ( 9 ^c %s ) )' % (A, Q99))
cr1 = w.s([n9d, n90d, q99], 'recxpcld', '( %s -> ( 9 ^c %s ) e. RR )' % (A, Q99))
cr2 = w.s([ar, a0, q99], 'recxpcld', '( %s -> ( A ^c %s ) e. RR )' % (A, Q99))
w.qed([r3d, cr1, cr2, c91, cx2], 'letrd', '( %s -> 3 <_ ( A ^c %s ) )' % (A, Q99))
run(w)

# ------------------------------------------------------------------ mul4rot
w = W('mul4rot', 'A rearrangement of a four-factor product: D ( C A B ) = A ( ( D C ) B ) .')
A = '( ( D e. CC /\\ C e. CC ) /\\ ( A e. CC /\\ B e. CC ) )'
dc = w.s([], 'simpll', '( %s -> D e. CC )' % A)
cc = w.s([], 'simplr', '( %s -> C e. CC )' % A)
ac = w.s([], 'simprl', '( %s -> A e. CC )' % A)
bc = w.s([], 'simprr', '( %s -> B e. CC )' % A)
e1 = w.s([cc, ac, bc], 'mulassd', '( %s -> ( ( C x. A ) x. B ) = ( C x. ( A x. B ) ) )' % A)
e2 = w.s([e1], 'oveq2d', '( %s -> ( D x. ( ( C x. A ) x. B ) ) = ( D x. ( C x. ( A x. B ) ) ) )' % A)
abc = w.s([ac, bc], 'mulcld', '( %s -> ( A x. B ) e. CC )' % A)
e3 = w.s([dc, cc, abc], 'mulassd', '( %s -> ( ( D x. C ) x. ( A x. B ) ) = ( D x. ( C x. ( A x. B ) ) ) )' % A)
lhs = w.s([e2, w.s([e3], 'eqcomd', '( %s -> ( D x. ( C x. ( A x. B ) ) ) = ( ( D x. C ) x. ( A x. B ) ) )' % A)], 'eqtrd',
          '( %s -> ( D x. ( ( C x. A ) x. B ) ) = ( ( D x. C ) x. ( A x. B ) ) )' % A)
dcc = w.s([dc, cc], 'mulcld', '( %s -> ( D x. C ) e. CC )' % A)
rhs = w.s([ac, dcc, bc], 'mul12d', '( %s -> ( A x. ( ( D x. C ) x. B ) ) = ( ( D x. C ) x. ( A x. B ) ) )' % A)
w.qed([lhs, rhs], 'eqtr4d', '( %s -> ( D x. ( ( C x. A ) x. B ) ) = ( A x. ( ( D x. C ) x. B ) ) )' % A)
run(w)

# --------------------------------------------------- the exponents 99 / 100
Q99 = '( ; 9 9 / ; ; 1 0 0 )'; Q100 = '( ; ; 1 0 0 / ; 9 9 )'

w = W('p10099', '1 + ( 1 / 99 ) = 100 / 99 .')
c99 = num.fact(w, '; 9 9', 'CC')
n99 = num.fact(w, '; 9 9', 'ne0')
c1 = w.s([], 'ax-1cn', '1 e. CC')
dd = w.s([c99, c1, w.s([c99, n99], 'pm3.2i', '( ; 9 9 e. CC /\\ ; 9 9 =/= 0 )'), w.inst('divdir')], 'mp3an',
         '( ( ; 9 9 + 1 ) / ; 9 9 ) = ( ( ; 9 9 / ; 9 9 ) + ( 1 / ; 9 9 ) )')
di = w.s([c99, n99, w.inst('divid')], 'mp2an', '( ; 9 9 / ; 9 9 ) = 1')
ad = num.add_nat(w, 99, 1)
l1 = w.s([ad], 'oveq1i', '( ( ; 9 9 + 1 ) / ; 9 9 ) = %s' % Q100)
l2 = w.s([di], 'oveq1i', '( ( ; 9 9 / ; 9 9 ) + ( 1 / ; 9 9 ) ) = ( 1 + ( 1 / ; 9 9 ) )')
e1 = w.s([w.s([l1], 'eqcomi', '%s = ( ( ; 9 9 + 1 ) / ; 9 9 )' % Q100), dd], 'eqtri',
         '%s = ( ( ; 9 9 / ; 9 9 ) + ( 1 / ; 9 9 ) )' % Q100)
e2 = w.s([e1, l2], 'eqtri', '%s = ( 1 + ( 1 / ; 9 9 ) )' % Q100)
w.qed([e2], 'eqcomi', '( 1 + ( 1 / ; 9 9 ) ) = %s' % Q100)
run(w)

w = W('q9910', '( 100 / 99 ) x. ( 99 / 100 ) = 1 .')
c100 = num.fact(w, '; ; 1 0 0', 'CC')
n100 = num.fact(w, '; ; 1 0 0', 'ne0')
c99 = num.fact(w, '; 9 9', 'CC')
n99 = num.fact(w, '; 9 9', 'ne0')
j1 = w.s([c100, n100], 'pm3.2i', '( ; ; 1 0 0 e. CC /\\ ; ; 1 0 0 =/= 0 )')
j2 = w.s([c99, n99], 'pm3.2i', '( ; 9 9 e. CC /\\ ; 9 9 =/= 0 )')
w.qed([j1, j2, w.inst('divcan6')], 'mp2an', '( %s x. %s ) = 1' % (Q100, Q99))
run(w)
