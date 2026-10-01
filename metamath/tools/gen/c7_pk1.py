"""C7, Perron block 1: the coordinate form of the rectangle, the edge algebra,
the reversed horizontal edge."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *

# ---------------------------------------------------------------- rectintco
A0 = '( F e. V /\\ ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ R e. RR ) )'
CA = CPT('P', 'S'); CB = CPT('Q', 'R'); C1 = CPT('Q', 'S'); C2 = CPT('P', 'R')
R1 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (CB, CA)
R2 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (CA, CB)
w = W('rectintco', 'The boundary integral around a rectangle whose corners are given in '
      'coordinates: the four edges in the order ~ rectintval produces them, with the '
      'two remaining corners written out ( ~ crre , ~ crim ).')
fv = w.s([], 'simp1', '( %s -> F e. V )' % A0)
pr = w.s([w.s([], 'simp2', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> P e. RR )' % A0)
qr = w.s([w.s([], 'simp2', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> Q e. RR )' % A0)
sr = w.s([w.s([], 'simp3', '( %s -> ( S e. RR /\\ R e. RR ) )' % A0), w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
rr = w.s([w.s([], 'simp3', '( %s -> ( S e. RR /\\ R e. RR ) )' % A0), w.inst('simpr')], 'syl', '( %s -> R e. RR )' % A0)
ic = a1(w, A0, 'ax-icn', '_i e. CC')
def cpt(x, y, xr, yr):
    return w.s([w.s([xr], 'recnd', '( %s -> %s e. CC )' % (A0, x)),
                w.s([ic, w.s([yr], 'recnd', '( %s -> %s e. CC )' % (A0, y))], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, y))],
               'addcld', '( %s -> %s e. CC )' % (A0, CPT(x, y)))
ac = cpt('P', 'S', pr, sr); bc = cpt('Q', 'R', qr, rr)
rv = w.s([fv, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (
    A0, CA, CB, '( ( ( F lint <. %s , %s >. ) + ( F lint <. %s , %s >. ) ) + ( ( F lint <. %s , %s >. ) + ( F lint <. %s , %s >. ) ) )' % (CA, R1, R1, CB, CB, R2, R2, CA)))
reb = w.s([qr, rr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = Q )' % (A0, CB))
ima = w.s([pr, sr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = S )' % (A0, CA))
rea = w.s([pr, sr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = P )' % (A0, CA))
imb = w.s([qr, rr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = R )' % (A0, CB))
c1e = w.s([reb, w.s([ima], 'oveq2d', '( %s -> ( _i x. ( Im ` %s ) ) = ( _i x. S ) )' % (A0, CA))], 'oveq12d', '( %s -> %s = %s )' % (A0, R1, C1))
c2e = w.s([rea, w.s([imb], 'oveq2d', '( %s -> ( _i x. ( Im ` %s ) ) = ( _i x. R ) )' % (A0, CB))], 'oveq12d', '( %s -> %s = %s )' % (A0, R2, C2))
def lint(x, y):
    return '( F lint <. %s , %s >. )' % (x, y)
e1 = w.s([w.s([c1e], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, CA, R1, CA, C1))], 'oveq2d', '( %s -> %s = %s )' % (A0, lint(CA, R1), lint(CA, C1)))
e2 = w.s([w.s([c1e], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, R1, CB, C1, CB))], 'oveq2d', '( %s -> %s = %s )' % (A0, lint(R1, CB), lint(C1, CB)))
e3 = w.s([w.s([c2e], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, CB, R2, CB, C2))], 'oveq2d', '( %s -> %s = %s )' % (A0, lint(CB, R2), lint(CB, C2)))
e4 = w.s([w.s([c2e], 'opeq1d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (A0, R2, CA, C2, CA))], 'oveq2d', '( %s -> %s = %s )' % (A0, lint(R2, CA), lint(C2, CA)))
s12 = w.s([e1, e2], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, lint(CA, R1), lint(R1, CB), lint(CA, C1), lint(C1, CB)))
s34 = w.s([e3, e4], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, lint(CB, R2), lint(R2, CA), lint(CB, C2), lint(C2, CA)))
sall = w.s([s12, s34], 'oveq12d', '( %s -> ( ( %s + %s ) + ( %s + %s ) ) = %s )' % (
    A0, lint(CA, R1), lint(R1, CB), lint(CB, R2), lint(R2, CA), FOUR('F', 'P', 'Q', 'S', 'R')))
w.qed([rv, sall], 'eqtrd', '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (A0, CA, CB, FOUR('F', 'P', 'Q', 'S', 'R')))
run7(w)

# ---------------------------------------------------------------- edgesol
A0 = '( ( ( X e. CC /\\ Y e. CC ) /\\ ( V e. CC /\\ K e. CC ) ) /\\ W e. CC )'
EQ = '( ( X + Y ) + ( V + K ) ) = W'
A1 = '( %s /\\ %s )' % (A0, EQ)
M = '( X + ( Y + V ) )'
w = W('edgesol', 'Solving the four-edge identity for one edge and bounding it: if the four '
      'edges sum to ` W ` then the fourth differs from ` W ` by at most the sum of the '
      'moduli of the other three ( ` kernel_solve ` of Route Z\'s PerronKernel.lean).')
xc = w.s([], 'ad2antrr', '( %s -> ( X e. CC /\\ Y e. CC ) )' % A1)
xc1 = w.s([xc, w.inst('simpl')], 'syl', '( %s -> X e. CC )' % A1)
yc = w.s([xc, w.inst('simpr')], 'syl', '( %s -> Y e. CC )' % A1)
vk = w.s([w.s([], 'simplr', '( %s -> ( V e. CC /\\ K e. CC ) )' % A0)], 'adantr', '( %s -> ( V e. CC /\\ K e. CC ) )' % A1)
vc = w.s([vk, w.inst('simpl')], 'syl', '( %s -> V e. CC )' % A1)
kc = w.s([vk, w.inst('simpr')], 'syl', '( %s -> K e. CC )' % A1)
wc = w.s([w.s([], 'simpr', '( %s -> W e. CC )' % A0)], 'adantr', '( %s -> W e. CC )' % A1)
eq = w.s([], 'simpr', '( %s -> %s )' % (A1, EQ))
yv = w.s([yc, vc], 'addcld', '( %s -> ( Y + V ) e. CC )' % A1)
mc = w.s([xc1, yv], 'addcld', '( %s -> %s e. CC )' % (A1, M))
# ( ( X + Y ) + ( V + K ) ) = ( M + K )
r1 = w.s([xc1, yc, w.s([vc, kc], 'addcld', '( %s -> ( V + K ) e. CC )' % A1)], 'addassd', '( %s -> ( ( X + Y ) + ( V + K ) ) = ( X + ( Y + ( V + K ) ) ) )' % A1)
r2 = w.s([yc, vc, kc], 'addassd', '( %s -> ( ( Y + V ) + K ) = ( Y + ( V + K ) ) )' % A1)
r3 = w.s([w.s([r2], 'eqcomd', '( %s -> ( Y + ( V + K ) ) = ( ( Y + V ) + K ) )' % A1)], 'oveq2d', '( %s -> ( X + ( Y + ( V + K ) ) ) = ( X + ( ( Y + V ) + K ) ) )' % A1)
r4 = w.s([xc1, yv, kc], 'addassd', '( %s -> ( ( X + ( Y + V ) ) + K ) = ( X + ( ( Y + V ) + K ) ) )' % A1)
r5 = w.s([w.s([r1, r3], 'eqtrd', '( %s -> ( ( X + Y ) + ( V + K ) ) = ( X + ( ( Y + V ) + K ) ) )' % A1),
          w.s([r4], 'eqcomd', '( %s -> ( X + ( ( Y + V ) + K ) ) = ( %s + K ) )' % (A1, M))], 'eqtrd',
         '( %s -> ( ( X + Y ) + ( V + K ) ) = ( %s + K ) )' % (A1, M))
weq = w.s([w.s([eq], 'eqcomd', '( %s -> W = ( ( X + Y ) + ( V + K ) ) )' % A1), r5], 'eqtrd', '( %s -> W = ( %s + K ) )' % (A1, M))
# K - W = -u M
d1 = w.s([weq], 'oveq2d', '( %s -> ( K - W ) = ( K - ( %s + K ) ) )' % (A1, M))
mk = w.s([mc, kc], 'addcld', '( %s -> ( %s + K ) e. CC )' % (A1, M))
d2 = w.s([mk, kc], 'negsubdi2d', '( %s -> -u ( ( %s + K ) - K ) = ( K - ( %s + K ) ) )' % (A1, M, M))
d3 = w.s([w.s([mc, kc], 'pncand', '( %s -> ( ( %s + K ) - K ) = %s )' % (A1, M, M))], 'negeqd', '( %s -> -u ( ( %s + K ) - K ) = -u %s )' % (A1, M, M))
d4 = w.s([d1, w.s([w.s([d2], 'eqcomd', '( %s -> ( K - ( %s + K ) ) = -u ( ( %s + K ) - K ) )' % (A1, M, M)), d3], 'eqtrd',
                   '( %s -> ( K - ( %s + K ) ) = -u %s )' % (A1, M, M))], 'eqtrd', '( %s -> ( K - W ) = -u %s )' % (A1, M))
ab = w.s([w.s([d4], 'fveq2d', '( %s -> ( abs ` ( K - W ) ) = ( abs ` -u %s ) )' % (A1, M)), w.s([mc], 'absnegd', '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (A1, M, M))],
         'eqtrd', '( %s -> ( abs ` ( K - W ) ) = ( abs ` %s ) )' % (A1, M))
t1 = w.s([xc1, yv], 'abstrid', '( %s -> ( abs ` %s ) <_ ( ( abs ` X ) + ( abs ` ( Y + V ) ) ) )' % (A1, M))
t2 = w.s([yc, vc], 'abstrid', '( %s -> ( abs ` ( Y + V ) ) <_ ( ( abs ` Y ) + ( abs ` V ) ) )' % A1)
ax = w.s([xc1], 'abscld', '( %s -> ( abs ` X ) e. RR )' % A1)
ayv = w.s([yv], 'abscld', '( %s -> ( abs ` ( Y + V ) ) e. RR )' % A1)
ay = w.s([yc], 'abscld', '( %s -> ( abs ` Y ) e. RR )' % A1)
av = w.s([vc], 'abscld', '( %s -> ( abs ` V ) e. RR )' % A1)
t3 = w.s([ayv, w.s([ay, av], 'readdcld', '( %s -> ( ( abs ` Y ) + ( abs ` V ) ) e. RR )' % A1), ax, t2], 'leadd2dd',
         '( %s -> ( ( abs ` X ) + ( abs ` ( Y + V ) ) ) <_ ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` V ) ) ) )' % A1)
am = w.s([mc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A1, M))
t4 = w.s([am, w.s([ax, ayv], 'readdcld', '( %s -> ( ( abs ` X ) + ( abs ` ( Y + V ) ) ) e. RR )' % A1),
          w.s([ax, w.s([ay, av], 'readdcld', '( %s -> ( ( abs ` Y ) + ( abs ` V ) ) e. RR )' % A1)], 'readdcld', '( %s -> ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` V ) ) ) e. RR )' % A1),
          t1, t3], 'letrd', '( %s -> ( abs ` %s ) <_ ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` V ) ) ) )' % (A1, M))
fin = w.s([ab, t4], 'eqbrtrd', '( %s -> ( abs ` ( K - W ) ) <_ ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` V ) ) ) )' % A1)
w.qed([fin], 'ex', '( %s -> ( %s -> ( abs ` ( K - W ) ) <_ ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` V ) ) ) ) )' % (A0, EQ))
run7(w)

# ---------------------------------------------------------------- hedgbndr
A0C = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( P e. RR /\\ Q e. RR ) )'
A2 = '( %s /\\ ( ( S e. RR /\\ S =/= 0 ) /\\ P <_ Q ) )' % A0C
HA = CPT('P', 'S'); HBB = CPT('Q', 'S')
REC = '( 1 / ( abs ` S ) )'
BNDH = '( %s x. ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) )' % (REC, LGU)
w = W('hedgbndr', 'The horizontal-edge bound for the Perron integrand on the edge traversed '
      'from right to left: the integral changes sign ( ~ lintrev ) and ~ hedgbnd applies.')
a0 = w.s([], 'simpl', '( %s -> %s )' % (A2, A0C))
urp = w.s([w.s([a0, w.inst('simpl')], 'syl', '( %s -> ( U e. RR+ /\\ U =/= 1 ) )' % A2), w.inst('simpl')], 'syl', '( %s -> U e. RR+ )' % A2)
pr = w.s([w.s([a0, w.inst('simpr')], 'syl', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A2), w.inst('simpl')], 'syl', '( %s -> P e. RR )' % A2)
qr = w.s([w.s([a0, w.inst('simpr')], 'syl', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A2), w.inst('simpr')], 'syl', '( %s -> Q e. RR )' % A2)
sr = w.s([], 'simprll', '( %s -> S e. RR )' % A2)
sne = w.s([], 'simprlr', '( %s -> S =/= 0 )' % A2)
ic = a1(w, A2, 'ax-icn', '_i e. CC')
isc = w.s([ic, w.s([sr], 'recnd', '( %s -> S e. CC )' % A2)], 'mulcld', '( %s -> ( _i x. S ) e. CC )' % A2)
ac = w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A2), isc], 'addcld', '( %s -> %s e. CC )' % (A2, HA))
bc = w.s([w.s([qr], 'recnd', '( %s -> Q e. CC )' % A2), isc], 'addcld', '( %s -> %s e. CC )' % (A2, HBB))
pair1 = w.s([sr, sne], 'jca', '( %s -> ( S e. RR /\\ S =/= 0 ) )' % A2)
pair2 = w.s([pr, qr], 'jca', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A2)
both = w.s([pair1, pair2], 'jca', '( %s -> ( ( S e. RR /\\ S =/= 0 ) /\\ ( P e. RR /\\ Q e. RR ) ) )' % A2)
ssh = w.s([both, w.inst('cseghne0')], 'syl', '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (A2, HA, HBB, DOM))
sss = w.s([ssh, w.s([w.s([], 'dfss3', '( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s )' % (HA, HBB, DOM, HA, HBB, DOM))],
                    'a1i', '( %s -> ( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s ) )' % (A2, HA, HBB, DOM, HA, HBB, DOM))],
          'mpbird', '( %s -> ( %s cseg %s ) C_ %s )' % (A2, HA, HBB, DOM))
fcn = w.s([w.s([urp, a1(w, A2, 'ssid', '%s C_ %s' % (DOM, DOM))], 'jca', '( %s -> ( U e. RR+ /\\ %s C_ %s ) )' % (A2, DOM, DOM)), w.inst('pkfcn')], 'syl',
          '( %s -> %s e. ( %s -cn-> CC ) )' % (A2, PK0, DOM))
abp = w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A2, HA, HBB))
fp = w.s([fcn, sss], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (A2, PK0, DOM, HA, HBB, DOM))
rev = w.s([abp, fp, w.inst('lintrev')], 'syl2anc', '( %s -> %s = -u %s )' % (A2, E(HBB, HA), E(HA, HBB)))
lc = w.s([abp, fp, w.inst('lintcl')], 'syl2anc', '( %s -> %s e. CC )' % (A2, E(HA, HBB)))
ab = w.s([w.s([rev], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` -u %s ) )' % (A2, E(HBB, HA), E(HA, HBB))),
          w.s([lc], 'absnegd', '( %s -> ( abs ` -u %s ) = ( abs ` %s ) )' % (A2, E(HA, HBB), E(HA, HBB)))], 'eqtrd',
         '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A2, E(HBB, HA), E(HA, HBB)))
hb = w.s([w.s([], 'id', '( %s -> %s )' % (A2, A2)), w.inst('hedgbnd')], 'syl', '( %s -> ( abs ` %s ) <_ %s )' % (A2, E(HA, HBB), BNDH))
w.qed([ab, hb], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A2, E(HBB, HA), BNDH))
run7(w)
