"""Sortie C0b, batch 4: the rectangle-integral calculus (linteq, rectinteq,
rectintadd, rectintmulc, rectintqabs)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

RA = RE('A'); RB = RE('B'); IA = IM('A'); IB = IM('B')
P10 = PT(RB, IA); P01 = PT(RA, IB)
EDGES = [('A', P10), (P10, 'B'), ('B', P01), (P01, 'A')]

# ---- linteq: the segment integral depends only on the values on the segment
w = W('linteq', 'The line integral along a segment depends only on the values of the function on it.')
EQ = 'A. z e. ( A cseg B ) ( F ` z ) = ( G ` z )'
A0 = '( ( %s /\\ ( F e. V /\\ G e. V ) ) /\\ %s )' % (AB, EQ)
A1x = '( %s /\\ t e. ( 0 (,) 1 ) )' % A0
ac = w.s([], 'simplll', '( %s -> A e. CC )' % A0)
bc = w.s([], 'simpllr', '( %s -> B e. CC )' % A0)
fv = w.s([], 'simplrl', '( %s -> F e. V )' % A0)
gv = w.s([], 'simplrr', '( %s -> G e. V )' % A0)
eq = w.s([], 'simpr', '( %s -> %s )' % (A0, EQ))
INF = '( ( F ` %s ) x. ( B - A ) )' % LIN('A', 'B')
ING = '( ( G ` %s ) x. ( B - A ) )' % LIN('A', 'B')
lf = w.s([fv, ac, bc, w.inst('lintval')], 'syl3anc', '( %s -> ( F lint <. A , B >. ) = S. ( 0 (,) 1 ) %s _d t )' % (A0, INF))
lg = w.s([gv, ac, bc, w.inst('lintval')], 'syl3anc', '( %s -> ( G lint <. A , B >. ) = S. ( 0 (,) 1 ) %s _d t )' % (A0, ING))
t01 = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % A1x)
ssi = closed(w, A1x, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
ticc = w.s([ssi, t01], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % A1x)
lin = w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % A1x), w.s([bc], 'adantr', '( %s -> B e. CC )' % A1x), ticc, w.inst('cseglin')], 'syl3anc',
          '( %s -> %s e. ( A cseg B ) )' % (A1x, LIN('A', 'B')))
sub1 = w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (LIN('A', 'B'), LIN('A', 'B')))
sub2 = w.s([], 'fveq2', '( z = %s -> ( G ` z ) = ( G ` %s ) )' % (LIN('A', 'B'), LIN('A', 'B')))
sub = w.s([sub1, sub2], 'eqeq12d', '( z = %s -> ( ( F ` z ) = ( G ` z ) <-> ( F ` %s ) = ( G ` %s ) ) )' % (LIN('A', 'B'), LIN('A', 'B'), LIN('A', 'B')))
eq2 = w.s([eq], 'adantr', '( %s -> %s )' % (A1x, EQ))
pt = w.s([sub, eq2, lin], 'rspcdva', '( %s -> ( F ` %s ) = ( G ` %s ) )' % (A1x, LIN('A', 'B'), LIN('A', 'B')))
ie = w.s([pt], 'oveq1d', '( %s -> %s = %s )' % (A1x, INF, ING))
it = w.s([ie], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) %s _d t )' % (A0, INF, ING))
w.qed([w.s([lf, it], 'eqtrd', '( %s -> ( F lint <. A , B >. ) = S. ( 0 (,) 1 ) %s _d t )' % (A0, ING)), lg], 'eqtr4d',
      '( %s -> ( F lint <. A , B >. ) = ( G lint <. A , B >. ) )' % A0); run(w)

# ---- rectinteq
w = W('rectinteq', 'A rectangle boundary integral depends only on the values of the function on the rectangle.')
EQR = 'A. z e. ( A crect B ) ( F ` z ) = ( G ` z )'
A0 = '( ( %s /\\ %s /\\ ( F e. V /\\ G e. V ) ) /\\ %s )' % (AB, GEO, EQR)
ab = w.s([], 'simpl1', '( %s -> %s )' % (A0, AB))
geo = w.s([], 'simpl2', '( %s -> %s )' % (A0, GEO))
fg = w.s([], 'simpl3', '( %s -> ( F e. V /\\ G e. V ) )' % A0)
eqr = w.s([], 'simpr', '( %s -> %s )' % (A0, EQR))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
fv = w.s([fg, w.inst('simpl')], 'syl', '( %s -> F e. V )' % A0)
gv = w.s([fg, w.inst('simpr')], 'syl', '( %s -> G e. V )' % A0)
abg = w.s([ab, geo], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
corners = {'A': 'crectcnr1', P10: 'crectcnr2', 'B': 'crectcnr3', P01: 'crectcnr4'}
cst = {}
for pt_, lab in corners.items():
    cst[pt_] = w.s([abg, w.inst(lab)], 'syl', '( %s -> %s e. ( A crect B ) )' % (A0, pt_))
ccl = {'A': ac, 'B': bc}
ss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
for pt_ in (P10, P01):
    ccl[pt_] = w.s([ss, cst[pt_]], 'sseldd', '( %s -> %s e. CC )' % (A0, pt_))
eqs = []
for P, Q in EDGES:
    pq = w.s([cst[P], cst[Q]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (A0, P, Q))
    cvx = w.s([ab, pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A0, P, Q))
    sr = w.s([cvx, w.inst('ssralv')], 'syl', '( %s -> ( A. z e. ( A crect B ) ( F ` z ) = ( G ` z ) -> A. z e. ( %s cseg %s ) ( F ` z ) = ( G ` z ) ) )' % (A0, P, Q))
    al = w.s([sr, eqr], 'mpd', '( %s -> A. z e. ( %s cseg %s ) ( F ` z ) = ( G ` z ) )' % (A0, P, Q))
    h1 = w.s([ccl[P], ccl[Q]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, P, Q))
    h2 = w.s([fv, gv], 'jca', '( %s -> ( F e. V /\\ G e. V ) )' % A0)
    h3 = w.s([h1, h2], 'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. V /\\ G e. V ) ) )' % (A0, P, Q))
    eqs.append(w.s([h3, al, w.inst('linteq')], 'syl2anc', '( %s -> %s = %s )' % (A0, LINT('F', P, Q), LINT('G', P, Q))))
rvf = w.s([fv, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, RAW('A', 'B')))
rvg = w.s([gv, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> ( G rectint <. A , B >. ) = %s )' % (A0, RAW('A', 'B').replace('F lint', 'G lint')))
p1 = w.s([eqs[0], eqs[1]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT('F', 'A', P10), LINT('F', P10, 'B'), LINT('G', 'A', P10), LINT('G', P10, 'B')))
p2 = w.s([eqs[2], eqs[3]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT('F', 'B', P01), LINT('F', P01, 'A'), LINT('G', 'B', P01), LINT('G', P01, 'A')))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
w.qed([w.s([rvf, p3], 'eqtrd', '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, RAW('A', 'B').replace('F lint', 'G lint'))), rvg], 'eqtr4d',
      '( %s -> ( F rectint <. A , B >. ) = ( G rectint <. A , B >. ) )' % A0); run(w)

# ---- lintadd2: pointwise additivity of the segment integral
w = W('lintadd2', 'The line integral of a pointwise sum is the sum of the line integrals.')
PHF = PH
PHG = PH.replace('F e. (', 'G e. (')
PHH = PH.replace('F e. (', 'H e. (')
GH = '( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) )'
EQ = 'A. z e. ( A cseg B ) ( F ` z ) = ( ( G ` z ) + ( H ` z ) )'
A0 = '( %s /\\ %s /\\ %s )' % (PHF, GH, EQ)
A1x = '( %s /\\ t e. ( 0 (,) 1 ) )' % A0
ph = w.s([], 'simp1', '( %s -> %s )' % (A0, PHF))
gh = w.s([], 'simp2', '( %s -> %s )' % (A0, GH))
eq = w.s([], 'simp3', '( %s -> %s )' % (A0, EQ))
ac = w.s([ph, w.inst('simpll')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ph, w.inst('simplr')], 'syl', '( %s -> B e. CC )' % A0)
fcn = w.s([ph, w.inst('simprl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
sg = w.s([ph, w.inst('simprr')], 'syl', '( %s -> ( A cseg B ) C_ D )' % A0)
gcn = w.s([gh, w.inst('simpl')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
hcn = w.s([gh, w.inst('simpr')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
abp = w.s([ac, bc], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % A0)
phg = w.s([abp, w.s([gcn, sg], 'jca', '( %s -> ( G e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )' % A0)], 'jca', '( %s -> %s )' % (A0, PHG))
phh = w.s([abp, w.s([hcn, sg], 'jca', '( %s -> ( H e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )' % A0)], 'jca', '( %s -> %s )' % (A0, PHH))
L = LIN('A', 'B')
INF = '( ( F ` %s ) x. ( B - A ) )' % L
ING = '( ( G ` %s ) x. ( B - A ) )' % L
INH = '( ( H ` %s ) x. ( B - A ) )' % L
fex = w.s([fcn, w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
gex = w.s([gcn, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
hex = w.s([hcn, w.inst('elex')], 'syl', '( %s -> H e. _V )' % A0)
lvf = w.s([fex, ac, bc, w.inst('lintval')], 'syl3anc', '( %s -> ( F lint <. A , B >. ) = S. ( 0 (,) 1 ) %s _d t )' % (A0, INF))
lvg = w.s([gex, ac, bc, w.inst('lintval')], 'syl3anc', '( %s -> ( G lint <. A , B >. ) = S. ( 0 (,) 1 ) %s _d t )' % (A0, ING))
lvh = w.s([hex, ac, bc, w.inst('lintval')], 'syl3anc', '( %s -> ( H lint <. A , B >. ) = S. ( 0 (,) 1 ) %s _d t )' % (A0, INH))
# pointwise
t01 = w.s([], 'simpr', '( %s -> t e. ( 0 (,) 1 ) )' % A1x)
ssi = closed(w, A1x, 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')
ticc = w.s([ssi, t01], 'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % A1x)
ac2 = w.s([ac], 'adantr', '( %s -> A e. CC )' % A1x); bc2 = w.s([bc], 'adantr', '( %s -> B e. CC )' % A1x)
sg2 = w.s([sg], 'adantr', '( %s -> ( A cseg B ) C_ D )' % A1x)
gcn2 = w.s([gcn], 'adantr', '( %s -> G e. ( D -cn-> CC ) )' % A1x)
hcn2 = w.s([hcn], 'adantr', '( %s -> H e. ( D -cn-> CC ) )' % A1x)
lin = w.s([ac2, bc2, ticc, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (A1x, L))
gcl, _a, _b = intgclg(w, A1x, ac2, bc2, gcn2, sg2, ticc, 'G')
hcl, _a, _b = intgclg(w, A1x, ac2, bc2, hcn2, sg2, ticc, 'H')
s1 = w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (L, L))
s2 = w.s([], 'fveq2', '( z = %s -> ( G ` z ) = ( G ` %s ) )' % (L, L))
s3 = w.s([], 'fveq2', '( z = %s -> ( H ` z ) = ( H ` %s ) )' % (L, L))
s4 = w.s([s2, s3], 'oveq12d', '( z = %s -> ( ( G ` z ) + ( H ` z ) ) = ( ( G ` %s ) + ( H ` %s ) ) )' % (L, L, L))
sub = w.s([s1, s4], 'eqeq12d', '( z = %s -> ( ( F ` z ) = ( ( G ` z ) + ( H ` z ) ) <-> ( F ` %s ) = ( ( G ` %s ) + ( H ` %s ) ) ) )' % (L, L, L, L))
eq2 = w.s([eq], 'adantr', '( %s -> %s )' % (A1x, EQ))
pt = w.s([sub, eq2, lin], 'rspcdva', '( %s -> ( F ` %s ) = ( ( G ` %s ) + ( H ` %s ) ) )' % (A1x, L, L, L))
ba = w.s([bc2, ac2], 'subcld', '( %s -> ( B - A ) e. CC )' % A1x)
gv = w.s([w.s([gcn2, w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A1x), w.s([sg2, lin], 'sseldd', '( %s -> %s e. D )' % (A1x, L))], 'ffvelcdmd', '( %s -> ( G ` %s ) e. CC )' % (A1x, L))
hv = w.s([w.s([hcn2, w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % A1x), w.s([sg2, lin], 'sseldd', '( %s -> %s e. D )' % (A1x, L))], 'ffvelcdmd', '( %s -> ( H ` %s ) e. CC )' % (A1x, L))
dd = w.s([gv, hv, ba], 'adddird', '( %s -> ( ( ( G ` %s ) + ( H ` %s ) ) x. ( B - A ) ) = ( %s + %s ) )' % (A1x, L, L, ING, INH))
ie = w.s([w.s([pt], 'oveq1d', '( %s -> %s = ( ( ( G ` %s ) + ( H ` %s ) ) x. ( B - A ) ) )' % (A1x, INF, L, L)), dd], 'eqtrd',
         '( %s -> %s = ( %s + %s ) )' % (A1x, INF, ING, INH))
it1 = w.s([ie], 'itgeq2dv', '( %s -> S. ( 0 (,) 1 ) %s _d t = S. ( 0 (,) 1 ) ( %s + %s ) _d t )' % (A0, INF, ING, INH))
iblg = w.s([phg, w.inst('lintibl')], 'syl', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) e. L^1 )' % (A0, ING))
iblh = w.s([phh, w.inst('lintibl')], 'syl', '( %s -> ( t e. ( 0 (,) 1 ) |-> %s ) e. L^1 )' % (A0, INH))
it2 = w.s([gcl, iblg, hcl, iblh], 'itgadd', '( %s -> S. ( 0 (,) 1 ) ( %s + %s ) _d t = ( S. ( 0 (,) 1 ) %s _d t + S. ( 0 (,) 1 ) %s _d t ) )' % (A0, ING, INH, ING, INH))
rhs = w.s([lvg, lvh], 'oveq12d', '( %s -> ( ( G lint <. A , B >. ) + ( H lint <. A , B >. ) ) = ( S. ( 0 (,) 1 ) %s _d t + S. ( 0 (,) 1 ) %s _d t ) )' % (A0, ING, INH))
lhs = w.s([w.s([lvf, it1], 'eqtrd', '( %s -> ( F lint <. A , B >. ) = S. ( 0 (,) 1 ) ( %s + %s ) _d t )' % (A0, ING, INH)), it2], 'eqtrd',
          '( %s -> ( F lint <. A , B >. ) = ( S. ( 0 (,) 1 ) %s _d t + S. ( 0 (,) 1 ) %s _d t ) )' % (A0, ING, INH))
w.qed([lhs, rhs], 'eqtr4d', '( %s -> ( F lint <. A , B >. ) = ( ( G lint <. A , B >. ) + ( H lint <. A , B >. ) ) )' % A0); run(w)

# ---- rectintadd2: pointwise additivity of the rectangle boundary integral
w = W('rectintadd2', 'The rectangle boundary integral of a pointwise sum is the sum of the boundary integrals.')
GH = '( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) )'
EQR = 'A. z e. ( A crect B ) ( F ` z ) = ( ( G ` z ) + ( H ` z ) )'
A0 = '( %s /\\ %s /\\ %s )' % (PS, GH, EQR)
d = ctx(w, A0)
gh = w.s([], 'simp2', '( %s -> %s )' % (A0, GH))
eqr = w.s([], 'simp3', '( %s -> %s )' % (A0, EQR))
gcn = w.s([gh, w.inst('simpl')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
hcn = w.s([gh, w.inst('simpr')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
gex = w.s([gcn, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
hex = w.s([hcn, w.inst('elex')], 'syl', '( %s -> H e. _V )' % A0)
cst = {'A': d['pA'], P10: d['pP10'], 'B': d['pB'], P01: d['pP01']}
G4 = []; H4 = []; ccm = {}
for P, Q in EDGES:
    phf = phseg(w, A0, P, Q, d['ab'], cst[P], cst[Q], d['fcn'], d['rss'])
    phg = phseg(w, A0, P, Q, d['ab'], cst[P], cst[Q], gcn, d['rss'], 'G')
    phh = phseg(w, A0, P, Q, d['ab'], cst[P], cst[Q], hcn, d['rss'], 'H')
    ccm[LINT('G', P, Q)] = w.s([phg, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('G', P, Q)))
    ccm[LINT('H', P, Q)] = w.s([phh, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('H', P, Q)))
    pq = w.s([cst[P], cst[Q]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (A0, P, Q))
    cvx = w.s([d['ab'], pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A0, P, Q))
    sr = w.s([cvx, w.inst('ssralv')], 'syl', '( %s -> ( A. z e. ( A crect B ) ( F ` z ) = ( ( G ` z ) + ( H ` z ) ) -> A. z e. ( %s cseg %s ) ( F ` z ) = ( ( G ` z ) + ( H ` z ) ) ) )' % (A0, P, Q))
    al = w.s([sr, eqr], 'mpd', '( %s -> A. z e. ( %s cseg %s ) ( F ` z ) = ( ( G ` z ) + ( H ` z ) ) )' % (A0, P, Q))
    ghp = w.s([gcn, hcn], 'jca', '( %s -> %s )' % (A0, GH))
    st = w.s([phf, ghp, al, w.inst('lintadd2')], 'syl3anc', '( %s -> %s = ( %s + %s ) )' % (A0, LINT('F', P, Q), LINT('G', P, Q), LINT('H', P, Q)))
    G4.append(LINT('G', P, Q)); H4.append(LINT('H', P, Q))
    (G4 if False else None)
    ccm.setdefault('st' + P, st)
    globals()['st_%d' % len(G4)] = st
rvf = w.s([d['fex'], d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, RAW('A', 'B')))
rvg = w.s([gex, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> ( G rectint <. A , B >. ) = %s )' % (A0, RAW('A', 'B').replace('F lint', 'G lint')))
rvh = w.s([hex, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> ( H rectint <. A , B >. ) = %s )' % (A0, RAW('A', 'B').replace('F lint', 'H lint')))
st = [globals()['st_%d' % i] for i in range(1, 5)]
p1 = w.s([st[0], st[1]], 'oveq12d', '( %s -> ( %s + %s ) = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, LINT('F', *EDGES[0]), LINT('F', *EDGES[1]), G4[0], H4[0], G4[1], H4[1]))
p2 = w.s([st[2], st[3]], 'oveq12d', '( %s -> ( %s + %s ) = ( ( %s + %s ) + ( %s + %s ) ) )' % (A0, LINT('F', *EDGES[2]), LINT('F', *EDGES[3]), G4[2], H4[2], G4[3], H4[3]))
treeL = ('+', ('+', ('+', G4[0], H4[0]), ('+', G4[1], H4[1])), ('+', ('+', G4[2], H4[2]), ('+', G4[3], H4[3])))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B'), tree_text(treeL)))
key = {}
for i, x in enumerate(G4): key[x] = i
for i, x in enumerate(H4): key[x] = 4 + i
cs = CxSum(w, A0, ccm, key)
nL, atL = cs.nf(treeL)
lhs = w.s([w.s([rvf, p3], 'eqtrd', '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, tree_text(treeL))), nL], 'eqtrd',
          '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, rn(atL)))
treeR = ('+', ('+', ('+', G4[0], G4[1]), ('+', G4[2], G4[3])), ('+', ('+', H4[0], H4[1]), ('+', H4[2], H4[3])))
nR, atR = cs.nf(treeR)
sm = w.s([rvg, rvh], 'oveq12d', '( %s -> ( ( G rectint <. A , B >. ) + ( H rectint <. A , B >. ) ) = %s )' % (A0, tree_text(treeR)))
rhs = w.s([sm, nR], 'eqtrd', '( %s -> ( ( G rectint <. A , B >. ) + ( H rectint <. A , B >. ) ) = %s )' % (A0, rn(atR)))
w.qed([lhs, rhs], 'eqtr4d', '( %s -> ( F rectint <. A , B >. ) = ( ( G rectint <. A , B >. ) + ( H rectint <. A , B >. ) ) )' % A0); run(w)

# ---- rectintabs: the ML inequality for a rectangle boundary integral
w = W('rectintabs', 'The ML inequality for a rectangle boundary integral.')
ALM = 'A. z e. ( A crect B ) ( abs ` ( F ` z ) ) <_ M'
A0 = '( %s /\\ M e. RR /\\ %s )' % (PS, ALM)
WD = '( %s - %s )' % (RB, RA); HT = '( %s - %s )' % (IB, IA)
d = ctx(w, A0)
mr = w.s([], 'simp2', '( %s -> M e. RR )' % A0)
alm = w.s([], 'simp3', '( %s -> %s )' % (A0, ALM))
ic = closed(w, A0, 'ax-icn', '_i e. CC')
arc = w.s([d['ar']], 'recnd', '( %s -> %s e. CC )' % (A0, RA))
brc = w.s([d['br']], 'recnd', '( %s -> %s e. CC )' % (A0, RB))
aic = w.s([d['ai']], 'recnd', '( %s -> %s e. CC )' % (A0, IA))
bic = w.s([d['bi']], 'recnd', '( %s -> %s e. CC )' % (A0, IB))
iia = w.s([ic, aic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IA))
iib = w.s([ic, bic], 'mulcld', '( %s -> ( _i x. %s ) e. CC )' % (A0, IB))
repA = w.s([d['ac']], 'replimd', '( %s -> A = ( %s + ( _i x. %s ) ) )' % (A0, RA, IA))
repB = w.s([d['bc']], 'replimd', '( %s -> B = ( %s + ( _i x. %s ) ) )' % (A0, RB, IB))
wr = w.s([d['br'], d['ar']], 'resubcld', '( %s -> %s e. RR )' % (A0, WD))
hr = w.s([d['bi'], d['ai']], 'resubcld', '( %s -> %s e. RR )' % (A0, HT))
wc = w.s([brc, arc], 'subcld', '( %s -> %s e. CC )' % (A0, WD))
hc = w.s([bic, aic], 'subcld', '( %s -> %s e. CC )' % (A0, HT))
wg = w.s([w.s([d['br'], d['ar']], 'subge0d', '( %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (A0, WD, RA, RB)), d['ler']], 'mpbird', '( %s -> 0 <_ %s )' % (A0, WD))
hg = w.s([w.s([d['bi'], d['ai']], 'subge0d', '( %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (A0, HT, IA, IB)), d['lei']], 'mpbird', '( %s -> 0 <_ %s )' % (A0, HT))
absW = w.s([wr, wg], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A0, WD, WD))
absH = w.s([hr, hg], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A0, HT, HT))
absi1 = closed(w, A0, 'absi', '( abs ` _i ) = 1')
# the four edge differences and their absolute values
dif = {}
dif[('A', P10)] = w.s([w.s([repA], 'oveq2d', '( %s -> ( %s - A ) = ( %s - ( %s + ( _i x. %s ) ) ) )' % (A0, P10, P10, RA, IA)),
                       w.s([brc, arc, iia], 'pnpcan2d', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = %s )' % (A0, RB, IA, RA, IA, WD))],
                      'eqtrd', '( %s -> ( %s - A ) = %s )' % (A0, P10, WD))
dif[('B', P01)] = w.s([w.s([repB], 'oveq2d', '( %s -> ( %s - B ) = ( %s - ( %s + ( _i x. %s ) ) ) )' % (A0, P01, P01, RB, IB)),
                       w.s([arc, brc, iib], 'pnpcan2d', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = ( %s - %s ) )' % (A0, RA, IB, RB, IB, RA, RB))],
                      'eqtrd', '( %s -> ( %s - B ) = ( %s - %s ) )' % (A0, P01, RA, RB))
dif[(P10, 'B')] = w.s([w.s([w.s([repB], 'oveq1d', '( %s -> ( B - %s ) = ( ( %s + ( _i x. %s ) ) - %s ) )' % (A0, P10, RB, IB, P10)),
                            w.s([brc, iib, iia], 'pnpcand', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, RB, IB, RB, IA, IB, IA))], 'eqtrd',
                           '( %s -> ( B - %s ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, P10, IB, IA)),
                       w.s([w.s([ic, bic, aic], 'subdid', '( %s -> ( _i x. %s ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, HT, IB, IA))], 'eqcomd', '( %s -> ( ( _i x. %s ) - ( _i x. %s ) ) = ( _i x. %s ) )' % (A0, IB, IA, HT))],
                      'eqtrd', '( %s -> ( B - %s ) = ( _i x. %s ) )' % (A0, P10, HT))
dif[(P01, 'A')] = w.s([w.s([w.s([repA], 'oveq1d', '( %s -> ( A - %s ) = ( ( %s + ( _i x. %s ) ) - %s ) )' % (A0, P01, RA, IA, P01)),
                            w.s([arc, iia, iib], 'pnpcand', '( %s -> ( ( %s + ( _i x. %s ) ) - ( %s + ( _i x. %s ) ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, RA, IA, RA, IB, IA, IB))], 'eqtrd',
                           '( %s -> ( A - %s ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, P01, IA, IB)),
                       w.s([w.s([ic, aic, bic], 'subdid', '( %s -> ( _i x. ( %s - %s ) ) = ( ( _i x. %s ) - ( _i x. %s ) ) )' % (A0, IA, IB, IA, IB))], 'eqcomd', '( %s -> ( ( _i x. %s ) - ( _i x. %s ) ) = ( _i x. ( %s - %s ) ) )' % (A0, IA, IB, IA, IB))],
                      'eqtrd', '( %s -> ( A - %s ) = ( _i x. ( %s - %s ) ) )' % (A0, P01, IA, IB))
# absolute values of the four differences
absv = {}
absv[('A', P10)] = w.s([w.s([dif[('A', P10)]], 'fveq2d', '( %s -> ( abs ` ( %s - A ) ) = ( abs ` %s ) )' % (A0, P10, WD)), absW], 'eqtrd', '( %s -> ( abs ` ( %s - A ) ) = %s )' % (A0, P10, WD))
absv[('B', P01)] = w.s([w.s([w.s([dif[('B', P01)]], 'fveq2d', '( %s -> ( abs ` ( %s - B ) ) = ( abs ` ( %s - %s ) ) )' % (A0, P01, RA, RB)),
                             w.s([arc, brc], 'abssubd', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` %s ) )' % (A0, RA, RB, WD))], 'eqtrd', '( %s -> ( abs ` ( %s - B ) ) = ( abs ` %s ) )' % (A0, P01, WD)), absW], 'eqtrd',
                       '( %s -> ( abs ` ( %s - B ) ) = %s )' % (A0, P01, WD))
absv[(P10, 'B')] = w.s([w.s([w.s([dif[(P10, 'B')]], 'fveq2d', '( %s -> ( abs ` ( B - %s ) ) = ( abs ` ( _i x. %s ) ) )' % (A0, P10, HT)),
                             w.s([ic, hc], 'absmuld', '( %s -> ( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) ) )' % (A0, HT, HT))], 'eqtrd', '( %s -> ( abs ` ( B - %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) ) )' % (A0, P10, HT)),
                        w.s([w.s([absi1, absH], 'oveq12d', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. %s ) )' % (A0, HT, HT)), w.s([hc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, HT, HT))], 'eqtrd', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = %s )' % (A0, HT, HT))],
                       'eqtrd', '( %s -> ( abs ` ( B - %s ) ) = %s )' % (A0, P10, HT))
IAB = '( %s - %s )' % (IA, IB)
iabc = w.s([aic, bic], 'subcld', '( %s -> %s e. CC )' % (A0, IAB))
absIAB = w.s([w.s([aic, bic], 'abssubd', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, IAB, HT)), absH], 'eqtrd', '( %s -> ( abs ` %s ) = %s )' % (A0, IAB, HT))
absv[(P01, 'A')] = w.s([w.s([w.s([dif[(P01, 'A')]], 'fveq2d', '( %s -> ( abs ` ( A - %s ) ) = ( abs ` ( _i x. %s ) ) )' % (A0, P01, IAB)),
                             w.s([ic, iabc], 'absmuld', '( %s -> ( abs ` ( _i x. %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) ) )' % (A0, IAB, IAB))], 'eqtrd', '( %s -> ( abs ` ( A - %s ) ) = ( ( abs ` _i ) x. ( abs ` %s ) ) )' % (A0, P01, IAB)),
                        w.s([w.s([absi1, absIAB], 'oveq12d', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = ( 1 x. %s ) )' % (A0, IAB, HT)), w.s([hc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, HT, HT))], 'eqtrd', '( %s -> ( ( abs ` _i ) x. ( abs ` %s ) ) = %s )' % (A0, IAB, HT))],
                       'eqtrd', '( %s -> ( abs ` ( A - %s ) ) = %s )' % (A0, P01, HT))
# the four ML bounds
cst = {'A': d['pA'], P10: d['pP10'], 'B': d['pB'], P01: d['pP01']}
BND = {('A', P10): WD, (P10, 'B'): HT, ('B', P01): WD, (P01, 'A'): HT}
bnd = []; ccm = {}
for P, Q in EDGES:
    ph = phseg(w, A0, P, Q, d['ab'], cst[P], cst[Q], d['fcn'], d['rss'])
    ccm[LINT('F', P, Q)] = w.s([ph, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('F', P, Q)))
    pq = w.s([cst[P], cst[Q]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (A0, P, Q))
    cvx = w.s([d['ab'], pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A0, P, Q))
    sr = w.s([cvx, w.inst('ssralv')], 'syl', '( %s -> ( A. z e. ( A crect B ) ( abs ` ( F ` z ) ) <_ M -> A. z e. ( %s cseg %s ) ( abs ` ( F ` z ) ) <_ M ) )' % (A0, P, Q))
    al = w.s([sr, alm], 'mpd', '( %s -> A. z e. ( %s cseg %s ) ( abs ` ( F ` z ) ) <_ M )' % (A0, P, Q))
    la = w.s([ph, mr, al, w.inst('lintabs')], 'syl3anc', '( %s -> ( abs ` %s ) <_ ( M x. ( abs ` ( %s - %s ) ) ) )' % (A0, LINT('F', P, Q), Q, P))
    rw = w.s([absv[(P, Q)]], 'oveq2d', '( %s -> ( M x. ( abs ` ( %s - %s ) ) ) = ( M x. %s ) )' % (A0, Q, P, BND[(P, Q)]))
    bnd.append(w.s([la, rw], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( M x. %s ) )' % (A0, LINT('F', P, Q), BND[(P, Q)])))
# triangle inequality down the tree
rv = w.s([d['fex'], d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> ( F rectint <. A , B >. ) = %s )' % (A0, RAW('A', 'B')))
Ls = [LINT('F', *e) for e in EDGES]
S1 = '( %s + %s )' % (Ls[0], Ls[1]); S2 = '( %s + %s )' % (Ls[2], Ls[3])
c1 = w.s([ccm[Ls[0]], ccm[Ls[1]]], 'addcld', '( %s -> %s e. CC )' % (A0, S1))
c2 = w.s([ccm[Ls[2]], ccm[Ls[3]]], 'addcld', '( %s -> %s e. CC )' % (A0, S2))
tri0 = w.s([c1, c2], 'abstrid', '( %s -> ( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, S1, S2, S1, S2))
tri1 = w.s([ccm[Ls[0]], ccm[Ls[1]]], 'abstrid', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, S1, Ls[0], Ls[1]))
tri2 = w.s([ccm[Ls[2]], ccm[Ls[3]]], 'abstrid', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, S2, Ls[2], Ls[3]))
ar1 = w.s([c1], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, S1))
ar2 = w.s([c2], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, S2))
al_ = [w.s([ccm[x]], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, x)) for x in Ls]
mw = w.s([mr, wr], 'remulcld', '( %s -> ( M x. %s ) e. RR )' % (A0, WD))
mh = w.s([mr, hr], 'remulcld', '( %s -> ( M x. %s ) e. RR )' % (A0, HT))
s12 = w.s([al_[0], al_[1], mw, mh, bnd[0], bnd[1]], 'le2addd', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ ( ( M x. %s ) + ( M x. %s ) ) )' % (A0, Ls[0], Ls[1], WD, HT))
s34 = w.s([al_[2], al_[3], mw, mh, bnd[2], bnd[3]], 'le2addd', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ ( ( M x. %s ) + ( M x. %s ) ) )' % (A0, Ls[2], Ls[3], WD, HT))
b1 = w.s([ar1, w.s([al_[0], al_[1]], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A0, Ls[0], Ls[1])), w.s([mw, mh], 'readdcld', '( %s -> ( ( M x. %s ) + ( M x. %s ) ) e. RR )' % (A0, WD, HT)), tri1, s12], 'letrd',
         '( %s -> ( abs ` %s ) <_ ( ( M x. %s ) + ( M x. %s ) ) )' % (A0, S1, WD, HT))
b2 = w.s([ar2, w.s([al_[2], al_[3]], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A0, Ls[2], Ls[3])), w.s([mw, mh], 'readdcld', '( %s -> ( ( M x. %s ) + ( M x. %s ) ) e. RR )' % (A0, WD, HT)), tri2, s34], 'letrd',
         '( %s -> ( abs ` %s ) <_ ( ( M x. %s ) + ( M x. %s ) ) )' % (A0, S2, WD, HT))
mwh = w.s([mw, mh], 'readdcld', '( %s -> ( ( M x. %s ) + ( M x. %s ) ) e. RR )' % (A0, WD, HT))
tot = w.s([ar1, ar2, mwh, mwh, b1, b2], 'le2addd', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) <_ ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) )' % (A0, S1, S2, WD, HT, WD, HT))
chn = w.s([w.s([c1, c2], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, S1, S2)), None] if False else [w.s([w.s([c1, c2], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, S1, S2))], 'abscld', '( %s -> ( abs ` ( %s + %s ) ) e. RR )' % (A0, S1, S2)),
       w.s([ar1, ar2], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A0, S1, S2)),
       w.s([mwh, mwh], 'readdcld', '( %s -> ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) e. RR )' % (A0, WD, HT, WD, HT)), tri0, tot], 'letrd',
       '( %s -> ( abs ` ( %s + %s ) ) <_ ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) )' % (A0, S1, S2, WD, HT, WD, HT))
# the final identity 2M(W+H)
mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
whc = w.s([wc, hc], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, WD, HT))
e1 = w.s([w.s([mc, wc, hc], 'adddid', '( %s -> ( M x. ( %s + %s ) ) = ( ( M x. %s ) + ( M x. %s ) ) )' % (A0, WD, HT, WD, HT))], 'eqcomd',
         '( %s -> ( ( M x. %s ) + ( M x. %s ) ) = ( M x. ( %s + %s ) ) )' % (A0, WD, HT, WD, HT))
e2 = w.s([e1, e1], 'oveq12d', '( %s -> ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) = ( ( M x. ( %s + %s ) ) + ( M x. ( %s + %s ) ) ) )' % (A0, WD, HT, WD, HT, WD, HT, WD, HT))
e3 = w.s([w.s([w.s([mc, whc], 'mulcld', '( %s -> ( M x. ( %s + %s ) ) e. CC )' % (A0, WD, HT))], '2timesd', '( %s -> ( 2 x. ( M x. ( %s + %s ) ) ) = ( ( M x. ( %s + %s ) ) + ( M x. ( %s + %s ) ) ) )' % (A0, WD, HT, WD, HT, WD, HT))], 'eqcomd',
         '( %s -> ( ( M x. ( %s + %s ) ) + ( M x. ( %s + %s ) ) ) = ( 2 x. ( M x. ( %s + %s ) ) ) )' % (A0, WD, HT, WD, HT, WD, HT))
t2c = closed(w, A0, '2cn', '2 e. CC')
e4 = w.s([w.s([t2c, mc, whc], 'mulassd', '( %s -> ( ( 2 x. M ) x. ( %s + %s ) ) = ( 2 x. ( M x. ( %s + %s ) ) ) )' % (A0, WD, HT, WD, HT))], 'eqcomd',
         '( %s -> ( 2 x. ( M x. ( %s + %s ) ) ) = ( ( 2 x. M ) x. ( %s + %s ) ) )' % (A0, WD, HT, WD, HT))
brd = w.s([chn, w.s([w.s([e2, e3], 'eqtrd', '( %s -> ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) = ( 2 x. ( M x. ( %s + %s ) ) ) )' % (A0, WD, HT, WD, HT, WD, HT)), e4], 'eqtrd',
                     '( %s -> ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) = ( ( 2 x. M ) x. ( %s + %s ) ) )' % (A0, WD, HT, WD, HT, WD, HT))], 'breqtrd',
           '( %s -> ( abs ` ( %s + %s ) ) <_ ( ( 2 x. M ) x. ( %s + %s ) ) )' % (A0, S1, S2, WD, HT))
w.qed([w.s([rv], 'fveq2d', '( %s -> ( abs ` ( F rectint <. A , B >. ) ) = ( abs ` ( %s + %s ) ) )' % (A0, S1, S2)), brd], 'eqbrtrd',
      '( %s -> ( abs ` ( F rectint <. A , B >. ) ) <_ ( ( 2 x. M ) x. ( %s + %s ) ) )' % (A0, WD, HT)); run(w)
