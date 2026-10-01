"""Sortie A3b, batch 1: the two eventual helpers the wrappers need beyond A1's
ell2ge / ell3ge and A2's ell3sqle / quadexpe (A3b-blueprint.md section 2.1)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a3lib
from tm import *
import num
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

EV = lambda P: 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % P
A = '( ell2 ` n )'

# ------------------------------------------------------------------ evcxpge
w = W('evcxpge', 'Eventually a positive constant is below any positive real power of ell2 (the explicit-threshold lemma extrwrpow pulled back along ell2; Lean: tendsto_rpow_atTop composed with tendsto_ell2_atTopW).')
H = '( B e. RR+ /\\ G e. RR+ )'
TH = '( B ^c ( 1 / G ) )'
brp = w.s([], 'simpl', '( %s -> B e. RR+ )' % H)
grp = w.s([], 'simpr', '( %s -> G e. RR+ )' % H)
ginv = w.s([grp], 'rpreccld', '( %s -> ( 1 / G ) e. RR+ )' % H)
thrp = w.s([brp, w.s([ginv], 'rpred', '( %s -> ( 1 / G ) e. RR )' % H)], 'rpcxpcld', '( %s -> %s e. RR+ )' % (H, TH))
thre = w.s([thrp], 'rpred', '( %s -> %s e. RR )' % (H, TH))
e1 = w.s([thre, w.inst('ell2ge')], 'syl', '( %s -> %s )' % (H, EV('%s <_ %s' % (TH, A))))
e2 = w.s([w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))], 'a1i', '( %s -> %s )' % (H, EV('n e. ( ZZ>= ` 3 )')))
bun = w.s([e1, e2], 'evan2', '( %s -> %s )' % (H, EV('( %s <_ %s /\\ n e. ( ZZ>= ` 3 ) )' % (TH, A))))
P = '( %s /\\ ( %s <_ %s /\\ n e. ( ZZ>= ` 3 ) ) )' % (H, TH, A)
pb = w.s([], 'simpll', '( %s -> B e. RR+ )' % P)
pg = w.s([], 'simplr', '( %s -> G e. RR+ )' % P)
pth = w.s([], 'simprl', '( %s -> %s <_ %s )' % (P, TH, A))
puz = w.s([], 'simprr', '( %s -> n e. ( ZZ>= ` 3 ) )' % P)
puz2 = w.s([puz, w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % P)
pare = w.s([puz2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (P, A))
tri = w.s([pb, pg, pare], '3jca', '( %s -> ( B e. RR+ /\\ G e. RR+ /\\ %s e. RR ) )' % (P, A))
pw = w.s([tri, pth, w.inst('extrwrpow')], 'syl2anc', '( %s -> B <_ ( %s ^c G ) )' % (P, A))
w.qed([bun, pw], 'evimd', '( %s -> %s )' % (H, EV('B <_ ( %s ^c G )' % A)))
assert run(w)

# ------------------------------------------------------------------ evexpsq
w = W('evexpsq', 'Eventually a nonnegative multiple of the square of ell2 is below the exponential of ell2 (A2 quadexpe at R = 1; the hexp2 step of Lean\'s eventually_uW).')
H = '( K e. RR /\\ 0 <_ K )'
kre = w.s([], 'simpl', '( %s -> K e. RR )' % H)
k0 = w.s([], 'simpr', '( %s -> 0 <_ K )' % H)
i1rp = w.s([num.fact(w, '1', 'RR+')], 'a1i', '( %s -> 1 e. RR+ )' % H)
q = w.s([w.s([kre, k0, i1rp], '3jca', '( %s -> ( K e. RR /\\ 0 <_ K /\\ 1 e. RR+ ) )' % H), w.inst('quadexpe')], 'syl', '( %s -> %s )' % (H, EV('( K x. ( %s ^ 2 ) ) <_ ( exp ` ( 1 x. %s ) )' % (A, A))))
e2 = w.s([w.s([], 'evge3', EV('n e. ( ZZ>= ` 3 )'))], 'a1i', '( %s -> %s )' % (H, EV('n e. ( ZZ>= ` 3 )')))
bun = w.s([q, e2], 'evan2', '( %s -> %s )' % (H, EV('( ( K x. ( %s ^ 2 ) ) <_ ( exp ` ( 1 x. %s ) ) /\\ n e. ( ZZ>= ` 3 ) )' % (A, A))))
P = '( %s /\\ ( ( K x. ( %s ^ 2 ) ) <_ ( exp ` ( 1 x. %s ) ) /\\ n e. ( ZZ>= ` 3 ) ) )' % (H, A, A)
ple = w.s([], 'simprl', '( %s -> ( K x. ( %s ^ 2 ) ) <_ ( exp ` ( 1 x. %s ) ) )' % (P, A, A))
puz = w.s([], 'simprr', '( %s -> n e. ( ZZ>= ` 3 ) )' % P)
puz2 = w.s([puz, w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % P)
pare = w.s([puz2, w.inst('ell2cl')], 'syl', '( %s -> %s e. RR )' % (P, A))
pacn = w.s([pare], 'recnd', '( %s -> %s e. CC )' % (P, A))
mid = w.s([pacn], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (P, A, A))
efeq = w.s([mid], 'fveq2d', '( %s -> ( exp ` ( 1 x. %s ) ) = ( exp ` %s ) )' % (P, A, A))
pw = w.s([ple, efeq], 'breqtrd', '( %s -> ( K x. ( %s ^ 2 ) ) <_ ( exp ` %s ) )' % (P, A, A))
w.qed([bun, pw], 'evimd', '( %s -> %s )' % (H, EV('( K x. ( %s ^ 2 ) ) <_ ( exp ` %s )' % (A, A))))
assert run(w)
