"""Sortie C0c batch 6: the pointwise scalar-multiple forms of the segment and
rectangle integrals (the calculus gaps C0b named)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

EDGES = [('A', P10), (P10, 'B'), ('B', P01), (P01, 'A')]

# ---- lintmulc2: pointwise scalar multiple of a segment integral
w = W('lintmulc2', 'The line integral of a pointwise scalar multiple is the scalar multiple of the line integral.')
PHF = PH; PHG = PH.replace('F e. (', 'G e. (')
GC = '( G e. ( D -cn-> CC ) /\\ C e. CC )'
EQ = 'A. z e. ( A cseg B ) ( F ` z ) = ( C x. ( G ` z ) )'
A0 = '( %s /\\ %s /\\ %s )' % (PHF, GC, EQ)
A1 = '( %s /\\ t e. %s )' % (A0, O01)
L = LIN('A', 'B')
INF = '( ( F ` %s ) x. ( B - A ) )' % L
ING = '( ( G ` %s ) x. ( B - A ) )' % L
ph = w.s([], 'simp1', '( %s -> %s )' % (A0, PHF))
gc = w.s([], 'simp2', '( %s -> %s )' % (A0, GC))
eq = w.s([], 'simp3', '( %s -> %s )' % (A0, EQ))
ac = w.s([ph, w.inst('simpll')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ph, w.inst('simplr')], 'syl', '( %s -> B e. CC )' % A0)
fcn = w.s([ph, w.inst('simprl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
sg = w.s([ph, w.inst('simprr')], 'syl', '( %s -> ( A cseg B ) C_ D )' % A0)
gcn = w.s([gc, w.inst('simpl')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
cc = w.s([gc, w.inst('simpr')], 'syl', '( %s -> C e. CC )' % A0)
abp = w.s([ac, bc], 'jca', '( %s -> ( A e. CC /\\ B e. CC ) )' % A0)
phg = w.s([abp, w.s([gcn, sg], 'jca', '( %s -> ( G e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )' % A0)], 'jca', '( %s -> %s )' % (A0, PHG))
fex = w.s([fcn, w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
gex = w.s([gcn, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
lvf = w.s([fex, ac, bc, w.inst('lintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, LINT('F', 'A', 'B'), ITG(O01, INF)))
lvg = w.s([gex, ac, bc, w.inst('lintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, LINT('G', 'A', 'B'), ITG(O01, ING)))
t01 = w.s([], 'simpr', '( %s -> t e. %s )' % (A1, O01))
ssi = closed(w, A1, 'ioossicc', '%s C_ %s' % (O01, U01))
ticc = w.s([ssi, t01], 'sseldd', '( %s -> t e. %s )' % (A1, U01))
ac2 = w.s([ac], 'adantr', '( %s -> A e. CC )' % A1); bc2 = w.s([bc], 'adantr', '( %s -> B e. CC )' % A1)
sg2 = w.s([sg], 'adantr', '( %s -> ( A cseg B ) C_ D )' % A1)
gcn2 = w.s([gcn], 'adantr', '( %s -> G e. ( D -cn-> CC ) )' % A1)
cc2 = w.s([cc], 'adantr', '( %s -> C e. CC )' % A1)
lin = w.s([ac2, bc2, ticc, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (A1, L))
gcl, ld, gf = intgclg(w, A1, ac2, bc2, gcn2, sg2, ticc, 'G')
s1 = w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (L, L))
s2 = w.s([], 'fveq2', '( z = %s -> ( G ` z ) = ( G ` %s ) )' % (L, L))
s3 = w.s([s2], 'oveq2d', '( z = %s -> ( C x. ( G ` z ) ) = ( C x. ( G ` %s ) ) )' % (L, L))
sub = w.s([s1, s3], 'eqeq12d', '( z = %s -> ( ( F ` z ) = ( C x. ( G ` z ) ) <-> ( F ` %s ) = ( C x. ( G ` %s ) ) ) )' % (L, L, L))
eq2 = w.s([eq], 'adantr', '( %s -> %s )' % (A1, EQ))
pt = w.s([sub, eq2, lin], 'rspcdva', '( %s -> ( F ` %s ) = ( C x. ( G ` %s ) ) )' % (A1, L, L))
gv = w.s([gf, ld], 'ffvelcdmd', '( %s -> ( G ` %s ) e. CC )' % (A1, L))
ba = w.s([bc2, ac2], 'subcld', '( %s -> ( B - A ) e. CC )' % A1)
mas = w.s([cc2, gv, ba], 'mulassd', '( %s -> ( ( C x. ( G ` %s ) ) x. ( B - A ) ) = ( C x. %s ) )' % (A1, L, ING))
ie = w.s([w.s([pt], 'oveq1d', '( %s -> %s = ( ( C x. ( G ` %s ) ) x. ( B - A ) ) )' % (A1, INF, L)), mas], 'eqtrd',
         '( %s -> %s = ( C x. %s ) )' % (A1, INF, ING))
it1 = w.s([ie], 'itgeq2dv', '( %s -> %s = %s )' % (A0, ITG(O01, INF), ITG(O01, '( C x. %s )' % ING)))
iblg = w.s([phg, w.inst('lintibl')], 'syl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, O01, ING))
it2 = w.s([cc, gcl, iblg], 'itgmulc2', '( %s -> ( C x. %s ) = %s )' % (A0, ITG(O01, ING), ITG(O01, '( C x. %s )' % ING)))
w.qed([w.s([lvf, it1], 'eqtrd', '( %s -> %s = %s )' % (A0, LINT('F', 'A', 'B'), ITG(O01, '( C x. %s )' % ING))),
       w.s([w.s([lvg], 'oveq2d', '( %s -> ( C x. %s ) = ( C x. %s ) )' % (A0, LINT('G', 'A', 'B'), ITG(O01, ING))), it2], 'eqtrd',
           '( %s -> ( C x. %s ) = %s )' % (A0, LINT('G', 'A', 'B'), ITG(O01, '( C x. %s )' % ING)))],
      'eqtr4d', '( %s -> %s = ( C x. %s ) )' % (A0, LINT('F', 'A', 'B'), LINT('G', 'A', 'B'))); run(w)

# ---- rectintmulc2: pointwise scalar multiple of a rectangle boundary integral
w = W('rectintmulc2', 'The rectangle boundary integral of a pointwise scalar multiple is the scalar multiple of the boundary integral.')
GC = '( G e. ( D -cn-> CC ) /\\ C e. CC )'
EQR = 'A. z e. ( A crect B ) ( F ` z ) = ( C x. ( G ` z ) )'
A0 = '( %s /\\ %s /\\ %s )' % (PS, GC, EQR)
d = ctx(w, A0)
gc = w.s([], 'simp2', '( %s -> %s )' % (A0, GC))
eqr = w.s([], 'simp3', '( %s -> %s )' % (A0, EQR))
gcn = w.s([gc, w.inst('simpl')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
cc = w.s([gc, w.inst('simpr')], 'syl', '( %s -> C e. CC )' % A0)
gex = w.s([gcn, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
cst = {'A': d['pA'], P10: d['pP10'], 'B': d['pB'], P01: d['pP01']}
G4 = []; sts = []; ccm = {}
for P, Q in EDGES:
    phf = phseg(w, A0, P, Q, d['ab'], cst[P], cst[Q], d['fcn'], d['rss'])
    phg = phseg(w, A0, P, Q, d['ab'], cst[P], cst[Q], gcn, d['rss'], 'G')
    ccm[LINT('G', P, Q)] = w.s([phg, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('G', P, Q)))
    pq = w.s([cst[P], cst[Q]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (A0, P, Q))
    cvx = w.s([d['ab'], pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (A0, P, Q))
    sr = w.s([cvx, w.inst('ssralv')], 'syl', '( %s -> ( %s -> A. z e. ( %s cseg %s ) ( F ` z ) = ( C x. ( G ` z ) ) ) )' % (A0, EQR, P, Q))
    al = w.s([sr, eqr], 'mpd', '( %s -> A. z e. ( %s cseg %s ) ( F ` z ) = ( C x. ( G ` z ) ) )' % (A0, P, Q))
    gcp = w.s([gcn, cc], 'jca', '( %s -> %s )' % (A0, GC))
    sts.append(w.s([phf, gcp, al, w.inst('lintmulc2')], 'syl3anc', '( %s -> %s = ( C x. %s ) )' % (A0, LINT('F', P, Q), LINT('G', P, Q))))
    G4.append(LINT('G', P, Q))
rvf = w.s([d['fex'], d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B')))
rvg = w.s([gex, d['ac'], d['bc'], w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('G', 'A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
p1 = w.s([sts[0], sts[1]], 'oveq12d', '( %s -> ( %s + %s ) = ( ( C x. %s ) + ( C x. %s ) ) )' % (A0, LINT('F', *EDGES[0]), LINT('F', *EDGES[1]), G4[0], G4[1]))
p2 = w.s([sts[2], sts[3]], 'oveq12d', '( %s -> ( %s + %s ) = ( ( C x. %s ) + ( C x. %s ) ) )' % (A0, LINT('F', *EDGES[2]), LINT('F', *EDGES[3]), G4[2], G4[3]))
TRE = '( ( ( C x. %s ) + ( C x. %s ) ) + ( ( C x. %s ) + ( C x. %s ) ) )' % tuple(G4)
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B'), TRE))
S1 = '( %s + %s )' % (G4[0], G4[1]); S2 = '( %s + %s )' % (G4[2], G4[3])
c1 = w.s([ccm[G4[0]], ccm[G4[1]]], 'addcld', '( %s -> %s e. CC )' % (A0, S1))
c2 = w.s([ccm[G4[2]], ccm[G4[3]]], 'addcld', '( %s -> %s e. CC )' % (A0, S2))
a1 = w.s([cc, ccm[G4[0]], ccm[G4[1]]], 'adddid', '( %s -> ( C x. %s ) = ( ( C x. %s ) + ( C x. %s ) ) )' % (A0, S1, G4[0], G4[1]))
a2 = w.s([cc, ccm[G4[2]], ccm[G4[3]]], 'adddid', '( %s -> ( C x. %s ) = ( ( C x. %s ) + ( C x. %s ) ) )' % (A0, S2, G4[2], G4[3]))
a3 = w.s([cc, c1, c2], 'adddid', '( %s -> ( C x. ( %s + %s ) ) = ( ( C x. %s ) + ( C x. %s ) ) )' % (A0, S1, S2, S1, S2))
a4 = w.s([a3, w.s([a1, a2], 'oveq12d', '( %s -> ( ( C x. %s ) + ( C x. %s ) ) = %s )' % (A0, S1, S2, TRE))], 'eqtrd',
         '( %s -> ( C x. ( %s + %s ) ) = %s )' % (A0, S1, S2, TRE))
rhs = w.s([w.s([rvg], 'oveq2d', '( %s -> ( C x. %s ) = ( C x. ( %s + %s ) ) )' % (A0, RINT('G', 'A', 'B'), S1, S2)), a4], 'eqtrd',
          '( %s -> ( C x. %s ) = %s )' % (A0, RINT('G', 'A', 'B'), TRE))
w.qed([w.s([rvf, p3], 'eqtrd', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), TRE)), rhs], 'eqtr4d',
      '( %s -> %s = ( C x. %s ) )' % (A0, RINT('F', 'A', 'B'), RINT('G', 'A', 'B'))); run(w)
