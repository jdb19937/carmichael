"""Sortie C0c batch 11: the finite-sum forms of the segment and rectangle
integrals (Lean's rectInt_sum)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

SUMB = lambda X: 'sum_ k e. K ( ( G ` k ) ` %s )' % X
SUMF = '( u e. D |-> %s )' % SUMB('u')
GK = '( G ` k )'
EDGES = [('A', P10), (P10, 'B'), ('B', P01), (P01, 'A')]
ALJ = 'A. j e. K ( G ` j ) e. ( D -cn-> CC )'
FAM = lambda car: '( ( K e. Fin /\\ D C_ CC ) /\\ ( %s /\\ %s C_ D ) )' % (ALJ, car)


def gkcn(w, A1, alj1):
    s1 = w.s([], 'fveq2', '( j = k -> ( G ` j ) = %s )' % GK)
    s2 = w.s([s1], 'eleq1d', '( j = k -> ( ( G ` j ) e. ( D -cn-> CC ) <-> %s e. ( D -cn-> CC ) ) )' % GK)
    return w.s([s2, alj1, w.s([], 'simpr', '( %s -> k e. K )' % A1)], 'rspcdva', '( %s -> %s e. ( D -cn-> CC ) )' % (A1, GK))


# ---- lintfsum
w = W('lintfsum', 'The line integral of a pointwise finite sum of continuous functions is the sum of the line integrals.')
SEG = '( A cseg B )'
A0 = '( %s /\\ %s )' % (AB, FAM(SEG))
A1 = '( %s /\\ k e. K )' % A0
A2 = '( %s /\\ t e. %s )' % (A0, O01)
A3 = '( %s /\\ ( t e. %s /\\ k e. K ) )' % (A0, O01)
L = LIN('A', 'B')
ING = '( ( %s ` %s ) x. ( B - A ) )' % (GK, L)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
fam = w.s([], 'simpr', '( %s -> %s )' % (A0, FAM(SEG)))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
kf = w.s([fam, w.inst('simpll')], 'syl', '( %s -> K e. Fin )' % A0)
dcc = w.s([fam, w.inst('simplr')], 'syl', '( %s -> D C_ CC )' % A0)
alj = w.s([fam, w.inst('simprl')], 'syl', '( %s -> %s )' % (A0, ALJ))
sg = w.s([fam, w.inst('simprr')], 'syl', '( %s -> %s C_ D )' % (A0, SEG))
dex = w.s([closed(w, A0, 'cnex', 'CC e. _V'), dcc], 'ssexd', '( %s -> D e. _V )' % A0)
smex = w.s([dex], 'mptexd', '( %s -> %s e. _V )' % (A0, SUMF))
# the value of the sum function at the parametrised point
t2 = w.s([], 'simpr', '( %s -> t e. %s )' % (A2, O01))
ssi = closed(w, A2, 'ioossicc', '%s C_ %s' % (O01, U01))
ticc = w.s([ssi, t2], 'sseldd', '( %s -> t e. %s )' % (A2, U01))
lin = w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % A2), w.s([bc], 'adantr', '( %s -> B e. CC )' % A2), ticc, w.inst('cseglin')], 'syl3anc',
          '( %s -> %s e. %s )' % (A2, L, SEG))
lind = w.s([w.s([sg], 'adantr', '( %s -> %s C_ D )' % (A2, SEG)), lin], 'sseldd', '( %s -> %s e. D )' % (A2, L))
# closure of the summand under A3
kk3 = w.s([w.s([], 'simpr', '( %s -> ( t e. %s /\\ k e. K ) )' % (A3, O01)), w.inst('simpr')], 'syl', '( %s -> k e. K )' % A3)
t3 = w.s([w.s([], 'simpr', '( %s -> ( t e. %s /\\ k e. K ) )' % (A3, O01)), w.inst('simpl')], 'syl', '( %s -> t e. %s )' % (A3, O01))
alj3 = w.s([alj], 'adantr', '( %s -> %s )' % (A3, ALJ))
gk3 = gkcn(w, '( %s /\\ k e. K )' % A3 if False else A3, alj3) if False else None
q1 = w.s([], 'fveq2', '( j = k -> ( G ` j ) = %s )' % GK)
q2 = w.s([q1], 'eleq1d', '( j = k -> ( ( G ` j ) e. ( D -cn-> CC ) <-> %s e. ( D -cn-> CC ) ) )' % GK)
gk3 = w.s([q2, alj3, kk3], 'rspcdva', '( %s -> %s e. ( D -cn-> CC ) )' % (A3, GK))
ssi3 = closed(w, A3, 'ioossicc', '%s C_ %s' % (O01, U01))
ticc3 = w.s([ssi3, t3], 'sseldd', '( %s -> t e. %s )' % (A3, U01))
cl3, lind3, gf3 = intgclg(w, A3, w.s([ac], 'adantr', '( %s -> A e. CC )' % A3), w.s([bc], 'adantr', '( %s -> B e. CC )' % A3),
                          gk3, w.s([sg], 'adantr', '( %s -> %s C_ D )' % (A3, SEG)), ticc3, GK)
# the sum of the values at the parametrised point is complex
A2K = '( %s /\\ k e. K )' % A2
alj2k = w.s([w.s([alj], 'adantr', '( %s -> %s )' % (A2, ALJ))], 'adantr', '( %s -> %s )' % (A2K, ALJ))
gk2k = w.s([q2, alj2k, w.s([], 'simpr', '( %s -> k e. K )' % A2K)], 'rspcdva', '( %s -> %s e. ( D -cn-> CC ) )' % (A2K, GK))
gfv = w.s([w.s([gk2k, w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (A2K, GK)), w.s([lind], 'adantr', '( %s -> %s e. D )' % (A2K, L))],
          'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (A2K, GK, L))
sumcl = w.s([w.s([kf], 'adantr', '( %s -> K e. Fin )' % A2), gfv], 'fsumcl', '( %s -> %s e. CC )' % (A2, SUMB(L)))
sub1 = w.s([], 'fveq2', '( u = %s -> ( %s ` u ) = ( %s ` %s ) )' % (L, GK, GK, L))
sub2 = w.s([sub1], 'sumeq2sdv', '( u = %s -> %s = %s )' % (L, SUMB('u'), SUMB(L)))
fvi = w.s([sub2, w.s([], 'eqid', '%s = %s' % (SUMF, SUMF))], 'fvmptg',
          '( ( %s e. D /\\ %s e. CC ) -> ( %s ` %s ) = %s )' % (L, SUMB(L), SUMF, L, SUMB(L)))
fv = w.s([lind, sumcl, fvi], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (A2, SUMF, L, SUMB(L)))
ba = w.s([w.s([bc], 'adantr', '( %s -> B e. CC )' % A2), w.s([ac], 'adantr', '( %s -> A e. CC )' % A2)], 'subcld', '( %s -> ( B - A ) e. CC )' % A2)
mc1 = w.s([w.s([kf], 'adantr', '( %s -> K e. Fin )' % A2), ba, gfv], 'fsummulc1',
          '( %s -> ( %s x. ( B - A ) ) = sum_ k e. K %s )' % (A2, SUMB(L), ING))
ie = w.s([w.s([fv], 'oveq1d', '( %s -> ( ( %s ` %s ) x. ( B - A ) ) = ( %s x. ( B - A ) ) )' % (A2, SUMF, L, SUMB(L))), mc1], 'eqtrd',
         '( %s -> ( ( %s ` %s ) x. ( B - A ) ) = sum_ k e. K %s )' % (A2, SUMF, L, ING))
lvs = w.s([smex, ac, bc, w.inst('lintval')], 'syl3anc',
          '( %s -> %s = %s )' % (A0, LINT(SUMF, 'A', 'B'), ITG(O01, '( ( %s ` %s ) x. ( B - A ) )' % (SUMF, L))))
it1 = w.s([ie], 'itgeq2dv', '( %s -> %s = %s )' % (A0, ITG(O01, '( ( %s ` %s ) x. ( B - A ) )' % (SUMF, L)), ITG(O01, 'sum_ k e. K %s' % ING)))
# itgfsum
gk1 = gkcn(w, A1, w.s([alj], 'adantr', '( %s -> %s )' % (A1, ALJ)))
ph1 = w.s([w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % A1), w.s([bc], 'adantr', '( %s -> B e. CC )' % A1)], 'jca',
               '( %s -> ( A e. CC /\\ B e. CC ) )' % A1),
           w.s([gk1, w.s([sg], 'adantr', '( %s -> %s C_ D )' % (A1, SEG))], 'jca',
               '( %s -> ( %s e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A1, GK, SEG))], 'jca',
          '( %s -> %s )' % (A1, PH.replace('F e. (', GK + ' e. (')))
ibl = w.s([ph1, w.inst('lintibl')], 'syl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A1, O01, ING))
mb = closed(w, A0, 'ioombl', '%s e. dom vol' % O01)
fs = w.s([mb, kf, cl3, ibl], 'itgfsum',
         '( %s -> ( ( t e. %s |-> sum_ k e. K %s ) e. L^1 /\\ %s = sum_ k e. K %s ) )' % (A0, O01, ING, ITG(O01, 'sum_ k e. K %s' % ING), ITG(O01, ING)))
fs2 = w.s([fs, w.inst('simpr')], 'syl', '( %s -> %s = sum_ k e. K %s )' % (A0, ITG(O01, 'sum_ k e. K %s' % ING), ITG(O01, ING)))
lvk = w.s([w.s([gk1, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A1, GK)), w.s([ac], 'adantr', '( %s -> A e. CC )' % A1),
           w.s([bc], 'adantr', '( %s -> B e. CC )' % A1), w.inst('lintval')], 'syl3anc',
          '( %s -> %s = %s )' % (A1, LINT(GK, 'A', 'B'), ITG(O01, ING)))
sm = w.s([w.s([lvk], 'eqcomd', '( %s -> %s = %s )' % (A1, ITG(O01, ING), LINT(GK, 'A', 'B')))], 'sumeq2dv',
         '( %s -> sum_ k e. K %s = sum_ k e. K %s )' % (A0, ITG(O01, ING), LINT(GK, 'A', 'B')))
w.qed([w.s([w.s([lvs, it1], 'eqtrd', '( %s -> %s = %s )' % (A0, LINT(SUMF, 'A', 'B'), ITG(O01, 'sum_ k e. K %s' % ING))), fs2], 'eqtrd',
           '( %s -> %s = sum_ k e. K %s )' % (A0, LINT(SUMF, 'A', 'B'), ITG(O01, ING))), sm], 'eqtrd',
      '( %s -> %s = sum_ k e. K %s )' % (A0, LINT(SUMF, 'A', 'B'), LINT(GK, 'A', 'B'))); run(w)

# ---- rectintsum
w = W('rectintsum', 'The rectangle boundary integral of a pointwise finite sum of continuous functions is the sum of the boundary integrals.')
RECT = '( A crect B )'
A0 = '( ( %s /\\ %s ) /\\ %s )' % (AB, GEO, FAM(RECT))
A1 = '( %s /\\ k e. K )' % A0
abg = w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
fam = w.s([], 'simpr', '( %s -> %s )' % (A0, FAM(RECT)))
ab = w.s([abg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
kf = w.s([fam, w.inst('simpll')], 'syl', '( %s -> K e. Fin )' % A0)
dcc = w.s([fam, w.inst('simplr')], 'syl', '( %s -> D C_ CC )' % A0)
alj = w.s([fam, w.inst('simprl')], 'syl', '( %s -> %s )' % (A0, ALJ))
rss = w.s([fam, w.inst('simprr')], 'syl', '( %s -> %s C_ D )' % (A0, RECT))
dex = w.s([closed(w, A0, 'cnex', 'CC e. _V'), dcc], 'ssexd', '( %s -> D e. _V )' % A0)
smex = w.s([dex], 'mptexd', '( %s -> %s e. _V )' % (A0, SUMF))
cst = {}
for nm, lab in (('A', 'crectcnr1'), (P10, 'crectcnr2'), ('B', 'crectcnr3'), (P01, 'crectcnr4')):
    cst[nm] = w.s([abg, w.inst(lab)], 'syl', '( %s -> %s e. %s )' % (A0, nm, RECT))
rc = w.s([ac, bc, w.inst('crectss')], 'syl2anc', '( %s -> %s C_ CC )' % (A0, RECT))
ccl = {'A': ac, 'B': bc}
for nm in (P10, P01):
    ccl[nm] = w.s([rc, cst[nm]], 'sseldd', '( %s -> %s e. CC )' % (A0, nm))
# per-edge lintfsum
lfs = {}; segd = {}
for S, T in EDGES:
    pq = w.s([cst[S], cst[T]], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A0, S, RECT, T, RECT))
    cvx = w.s([ab, pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ %s )' % (A0, S, T, RECT))
    sd = w.s([cvx, rss], 'sstrd', '( %s -> ( %s cseg %s ) C_ D )' % (A0, S, T))
    segd[(S, T)] = sd
    h = w.s([w.s([ccl[S], ccl[T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T)),
             w.s([w.s([kf, dcc], 'jca', '( %s -> ( K e. Fin /\\ D C_ CC ) )' % A0),
                  w.s([alj, sd], 'jca', '( %s -> ( %s /\\ ( %s cseg %s ) C_ D ) )' % (A0, ALJ, S, T))], 'jca',
                 '( %s -> %s )' % (A0, FAM('( %s cseg %s )' % (S, T))))], 'jca',
            '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ %s ) )' % (A0, S, T, FAM('( %s cseg %s )' % (S, T))))
    lfs[(S, T)] = w.s([h, w.inst('lintfsum')], 'syl', '( %s -> %s = sum_ k e. K %s )' % (A0, LINT(SUMF, S, T), LINT(GK, S, T)))
# under A1: rectintval for ( G ` k ) and the closures
alj1 = w.s([alj], 'adantr', '( %s -> %s )' % (A1, ALJ))
gk1 = gkcn(w, A1, alj1)
gex = w.s([gk1, w.inst('elex')], 'syl', '( %s -> %s e. _V )' % (A1, GK))
rvk = w.s([gex, w.s([ac], 'adantr', '( %s -> A e. CC )' % A1), w.s([bc], 'adantr', '( %s -> B e. CC )' % A1), w.inst('rectintval')], 'syl3anc',
          '( %s -> %s = %s )' % (A1, RINT(GK, 'A', 'B'), RAW('A', 'B').replace('F lint', GK + ' lint')))
mcl = {}
for S, T in EDGES:
    ph = phseg(w, A1, S, T, w.s([ab], 'adantr', '( %s -> %s )' % (A1, AB)), w.s([cst[S]], 'adantr', '( %s -> %s e. %s )' % (A1, S, RECT)),
               w.s([cst[T]], 'adantr', '( %s -> %s e. %s )' % (A1, T, RECT)), gk1, w.s([rss], 'adantr', '( %s -> %s C_ D )' % (A1, RECT)), GK)
    mcl[(S, T)] = w.s([ph, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A1, LINT(GK, S, T)))
M = [LINT(GK, *e) for e in EDGES]
S1 = '( %s + %s )' % (M[0], M[1]); S2 = '( %s + %s )' % (M[2], M[3])
c1 = w.s([mcl[EDGES[0]], mcl[EDGES[1]]], 'addcld', '( %s -> %s e. CC )' % (A1, S1))
c2 = w.s([mcl[EDGES[2]], mcl[EDGES[3]]], 'addcld', '( %s -> %s e. CC )' % (A1, S2))
sm0 = w.s([rvk], 'sumeq2dv', '( %s -> sum_ k e. K %s = sum_ k e. K ( %s + %s ) )' % (A0, RINT(GK, 'A', 'B'), S1, S2))
sa0 = w.s([kf, c1, c2], 'fsumadd', '( %s -> sum_ k e. K ( %s + %s ) = ( sum_ k e. K %s + sum_ k e. K %s ) )' % (A0, S1, S2, S1, S2))
sa1 = w.s([kf, mcl[EDGES[0]], mcl[EDGES[1]]], 'fsumadd', '( %s -> sum_ k e. K %s = ( sum_ k e. K %s + sum_ k e. K %s ) )' % (A0, S1, M[0], M[1]))
sa2 = w.s([kf, mcl[EDGES[2]], mcl[EDGES[3]]], 'fsumadd', '( %s -> sum_ k e. K %s = ( sum_ k e. K %s + sum_ k e. K %s ) )' % (A0, S2, M[2], M[3]))
TGTR = '( ( sum_ k e. K %s + sum_ k e. K %s ) + ( sum_ k e. K %s + sum_ k e. K %s ) )' % tuple(M)
sa3 = w.s([sa0, w.s([sa1, sa2], 'oveq12d', '( %s -> ( sum_ k e. K %s + sum_ k e. K %s ) = %s )' % (A0, S1, S2, TGTR))], 'eqtrd',
          '( %s -> sum_ k e. K ( %s + %s ) = %s )' % (A0, S1, S2, TGTR))
rhs = w.s([sm0, sa3], 'eqtrd', '( %s -> sum_ k e. K %s = %s )' % (A0, RINT(GK, 'A', 'B'), TGTR))
# the left-hand side
rvs = w.s([smex, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT(SUMF, 'A', 'B'), RAW('A', 'B').replace('F lint', SUMF + ' lint')))
p1 = w.s([lfs[EDGES[0]], lfs[EDGES[1]]], 'oveq12d', '( %s -> ( %s + %s ) = ( sum_ k e. K %s + sum_ k e. K %s ) )' % (A0, LINT(SUMF, *EDGES[0]), LINT(SUMF, *EDGES[1]), M[0], M[1]))
p2 = w.s([lfs[EDGES[2]], lfs[EDGES[3]]], 'oveq12d', '( %s -> ( %s + %s ) = ( sum_ k e. K %s + sum_ k e. K %s ) )' % (A0, LINT(SUMF, *EDGES[2]), LINT(SUMF, *EDGES[3]), M[2], M[3]))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B').replace('F lint', SUMF + ' lint'), TGTR))
w.qed([w.s([rvs, p3], 'eqtrd', '( %s -> %s = %s )' % (A0, RINT(SUMF, 'A', 'B'), TGTR)), rhs], 'eqtr4d',
      '( %s -> %s = sum_ k e. K %s )' % (A0, RINT(SUMF, 'A', 'B'), RINT(GK, 'A', 'B'))); run(w)
