"""Sortie C1 section 2: the frame of a rectangle and the generic-carrier
rectangle calculus (equality, linear combination and the ML inequality with the
pointwise hypothesis over any set containing the boundary)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c1_lib import *

INT = '( P e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (
    RA, RE('P'), RE('P'), RB, IA, IM('P'), IM('P'), IB)
INTQ = INT.replace('P', 'Q')
FEQ = ['crectfe1', 'crectfe2', 'crectfe3', 'crectfe4']

# ---- crectfru: the frame lies in the rectangle -----------------------------
w = W('crectfru', 'The boundary frame of a rectangle lies in the rectangle.')
A0 = '( %s /\\ %s )' % (AB, GEO)
ab = w.s([], 'simpl', '( %s -> %s )' % (A0, AB))
cnr = {}
for nm, lab, pt in (('A', 'crectcnr1', 'A'), (P10, 'crectcnr2', P10), ('B', 'crectcnr3', 'B'), (P01, 'crectcnr4', P01)):
    cnr[nm] = w.s([w.inst(lab)], 'mpi', '( %s -> %s e. ( A crect B ) )' % (A0, pt)) if False else \
        w.s([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst(lab)], 'syl', '( %s -> %s e. ( A crect B ) )' % (A0, pt))
inc = []
for i, (S, T) in enumerate(EDGES):
    pq = w.s([cnr[S], cnr[T]], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (A0, S, T))
    inc.append(w.s([ab, pq, w.inst('crectcvx')], 'syl2anc', '( %s -> %s C_ ( A crect B ) )' % (A0, SEGS[i])))
u1 = w.s([inc[0], inc[1]], 'unssd', '( %s -> ( %s u. %s ) C_ ( A crect B ) )' % (A0, SEGS[0], SEGS[1]))
u2 = w.s([inc[2], inc[3]], 'unssd', '( %s -> ( %s u. %s ) C_ ( A crect B ) )' % (A0, SEGS[2], SEGS[3]))
w.qed([u1, u2], 'unssd', '( %s -> %s C_ ( A crect B ) )' % (A0, FR)); run1(w)

# ---- crectfrp: the frame avoids a strictly interior point ------------------
w = W('crectfrp', 'The boundary frame of a rectangle avoids a strictly interior point.')
A0 = '( %s /\\ %s )' % (AB, INT)
PU = '( ( A crect B ) \\ { P } )'
idst = w.s([], 'id', '( %s -> %s )' % (A0, A0))
inc = [w.s([idst, w.inst(FEQ[i])], 'syl', '( %s -> %s C_ %s )' % (A0, SEGS[i], PU)) for i in range(4)]
u1 = w.s([inc[0], inc[1]], 'unssd', '( %s -> ( %s u. %s ) C_ %s )' % (A0, SEGS[0], SEGS[1], PU))
u2 = w.s([inc[2], inc[3]], 'unssd', '( %s -> ( %s u. %s ) C_ %s )' % (A0, SEGS[2], SEGS[3], PU))
w.qed([u1, u2], 'unssd', '( %s -> %s C_ %s )' % (A0, FR, PU)); run1(w)

# ---- ssdifpr ---------------------------------------------------------------
w = W('ssdifpr', 'A subset of two singleton-punctured sets is a subset of the pair-punctured set.')
A0 = '( E C_ ( X \\ { P } ) /\\ E C_ ( X \\ { Q } ) )'
h1 = w.s([], 'simpl', '( %s -> E C_ ( X \\ { P } ) )' % A0)
h2 = w.s([], 'simpr', '( %s -> E C_ ( X \\ { Q } ) )' % A0)
inn = w.s([h1, h2], 'ssind', '( %s -> E C_ ( ( X \\ { P } ) i^i ( X \\ { Q } ) ) )' % A0)
d1 = w.s([], 'df-pr', '{ P , Q } = ( { P } u. { Q } )')
d2 = w.s([d1], 'difeq2i', '( X \\ { P , Q } ) = ( X \\ ( { P } u. { Q } ) )')
d3 = w.s([], 'difundi', '( X \\ ( { P } u. { Q } ) ) = ( ( X \\ { P } ) i^i ( X \\ { Q } ) )')
d4 = w.s([d2, d3], 'eqtri', '( X \\ { P , Q } ) = ( ( X \\ { P } ) i^i ( X \\ { Q } ) )')
d5 = w.s([d4], 'a1i', '( %s -> ( X \\ { P , Q } ) = ( ( X \\ { P } ) i^i ( X \\ { Q } ) ) )' % A0)
w.qed([inn, d5], 'sseqtrrd', '( %s -> E C_ ( X \\ { P , Q } ) )' % A0); run1(w)

# ---- crectfrd: the frame avoids two strictly interior points ---------------
w = W('crectfrd', 'The boundary frame of a rectangle avoids two strictly interior points.')
A0 = '( %s /\\ %s /\\ %s )' % (AB, INT, INTQ)
ab = w.s([], 'simp1', '( %s -> %s )' % (A0, AB))
ip = w.s([], 'simp2', '( %s -> %s )' % (A0, INT))
iq = w.s([], 'simp3', '( %s -> %s )' % (A0, INTQ))
s1 = w.s([w.s([ab, ip], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INT)), w.inst('crectfrp')], 'syl',
         '( %s -> %s C_ ( ( A crect B ) \\ { P } ) )' % (A0, FR))
s2 = w.s([w.s([ab, iq], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, INTQ)), w.inst('crectfrp')], 'syl',
         '( %s -> %s C_ ( ( A crect B ) \\ { Q } ) )' % (A0, FR))
w.qed([s1, s2, w.inst('ssdifpr')], 'syl2anc', '( %s -> %s C_ ( ( A crect B ) \\ { P , Q } ) )' % (A0, FR)); run1(w)

# ---- rectinteqe ------------------------------------------------------------
w = W('rectinteqe', 'A rectangle boundary integral depends only on the values of '
      'the function on a set containing the boundary frame.')
FG = '( F e. V /\\ G e. V )'
EQE = 'A. u e. E ( F ` u ) = ( G ` u )'
A0 = '( ( %s /\\ %s C_ E ) /\\ %s /\\ %s )' % (AB, FR, FG, EQE)
base = w.s([], 'simp1', '( %s -> ( %s /\\ %s C_ E ) )' % (A0, AB, FR))
ab = w.s([base, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
fre = w.s([base, w.inst('simpr')], 'syl', '( %s -> %s C_ E )' % (A0, FR))
fg = w.s([], 'simp2', '( %s -> %s )' % (A0, FG))
eqe = w.s([], 'simp3', '( %s -> %s )' % (A0, EQE))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
fv = w.s([fg, w.inst('simpl')], 'syl', '( %s -> F e. V )' % A0)
gv = w.s([fg, w.inst('simpr')], 'syl', '( %s -> G e. V )' % A0)
fex = w.s([fv, w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
gex = w.s([gv, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
fgex = w.s([fex, gex], 'jca', '( %s -> ( F e. _V /\\ G e. _V ) )' % A0)
se = edges4(w, A0, fre)
eqs = []
for i, (S, T) in enumerate(EDGES):
    sr = w.s([se[i], w.inst('ssralv')], 'syl', '( %s -> ( %s -> A. u e. %s ( F ` u ) = ( G ` u ) ) )' % (A0, EQE, SEGS[i]))
    al = w.s([sr, eqe], 'mpd', '( %s -> A. u e. %s ( F ` u ) = ( G ` u ) )' % (A0, SEGS[i]))
    h = w.s([w.s([cc[S], cc[T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T)), fgex], 'jca',
            '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. _V /\\ G e. _V ) ) )' % (A0, S, T))
    eqs.append(w.s([h, al, w.inst('linteq')], 'syl2anc', '( %s -> %s = %s )' % (A0, LINT('F', S, T), LINT('G', S, T))))
rvf = w.s([fv, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B')))
rvg = w.s([gv, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('G', 'A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
p1 = w.s([eqs[0], eqs[1]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT('F', *EDGES[0]), LINT('F', *EDGES[1]), LINT('G', *EDGES[0]), LINT('G', *EDGES[1])))
p2 = w.s([eqs[2], eqs[3]], 'oveq12d', '( %s -> ( %s + %s ) = ( %s + %s ) )' % (A0, LINT('F', *EDGES[2]), LINT('F', *EDGES[3]), LINT('G', *EDGES[2]), LINT('G', *EDGES[3])))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
w.qed([w.s([rvf, p3], 'eqtrd', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B').replace('F lint', 'G lint'))), rvg],
      'eqtr4d', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RINT('G', 'A', 'B'))); run1(w)

# ---- rectintlce ------------------------------------------------------------
w = W('rectintlce', 'The rectangle boundary integral of a pointwise linear '
      'combination of two functions continuous on a set containing the boundary frame.')
GHE = '( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) /\\ E C_ D )'
FCGE = '( F e. V /\\ C e. CC /\\ %s )' % GHE
EQL = 'A. u e. E ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) )'
A0 = '( ( %s /\\ %s C_ E ) /\\ %s /\\ %s )' % (AB, FR, FCGE, EQL)
base = w.s([], 'simp1', '( %s -> ( %s /\\ %s C_ E ) )' % (A0, AB, FR))
ab = w.s([base, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, AB))
fre = w.s([base, w.inst('simpr')], 'syl', '( %s -> %s C_ E )' % (A0, FR))
fcg = w.s([], 'simp2', '( %s -> %s )' % (A0, FCGE))
eql = w.s([], 'simp3', '( %s -> %s )' % (A0, EQL))
ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
cc = cornerc(w, A0, ac, bc, ar, br, ai, bi)
fv = w.s([fcg, w.inst('simp1')], 'syl', '( %s -> F e. V )' % A0)
ccx = w.s([fcg, w.inst('simp2')], 'syl', '( %s -> C e. CC )' % A0)
gh = w.s([fcg, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, GHE))
gcn = w.s([gh, w.inst('simp1')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
hcn = w.s([gh, w.inst('simp2')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0)
ed = w.s([gh, w.inst('simp3')], 'syl', '( %s -> E C_ D )' % A0)
gex = w.s([gcn, w.inst('elex')], 'syl', '( %s -> G e. _V )' % A0)
hex = w.s([hcn, w.inst('elex')], 'syl', '( %s -> H e. _V )' % A0)
se = edges4(w, A0, fre)
G4 = []; H4 = []; CG4 = []; ccm = {}; sts = []
for i, (S, T) in enumerate(EDGES):
    sd = w.s([se[i], ed], 'sstrd', '( %s -> %s C_ D )' % (A0, SEGS[i]))
    sr = w.s([se[i], w.inst('ssralv')], 'syl', '( %s -> ( %s -> A. u e. %s ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) ) )' % (A0, EQL, SEGS[i]))
    al = w.s([sr, eql], 'mpd', '( %s -> A. u e. %s ( F ` u ) = ( ( C x. ( G ` u ) ) + ( H ` u ) ) )' % (A0, SEGS[i]))
    st_ = w.s([gcn, hcn, sd], '3jca', '( %s -> ( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, SEGS[i]))
    h2 = w.s([fv, ccx, st_], '3jca', '( %s -> ( F e. V /\\ C e. CC /\\ ( G e. ( D -cn-> CC ) /\\ H e. ( D -cn-> CC ) /\\ %s C_ D ) ) )' % (A0, SEGS[i]))
    h1 = w.s([cc[S], cc[T]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, S, T))
    sts.append(w.s([h1, h2, al, w.inst('lintlc')], 'syl3anc',
                   '( %s -> %s = ( ( C x. %s ) + %s ) )' % (A0, LINT('F', S, T), LINT('G', S, T), LINT('H', S, T))))
    phg = w.s([h1, w.s([gcn, sd], 'jca', '( %s -> ( G e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, SEGS[i]))], 'jca',
              '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ %s C_ D ) ) )' % (A0, S, T, SEGS[i]))
    phh = w.s([h1, w.s([hcn, sd], 'jca', '( %s -> ( H e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, SEGS[i]))], 'jca',
              '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( H e. ( D -cn-> CC ) /\\ %s C_ D ) ) )' % (A0, S, T, SEGS[i]))
    gcl = w.s([phg, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('G', S, T)))
    hcl = w.s([phh, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('H', S, T)))
    ccm[LINT('G', S, T)] = gcl; ccm[LINT('H', S, T)] = hcl
    ccm['( C x. %s )' % LINT('G', S, T)] = w.s([ccx, gcl], 'mulcld', '( %s -> ( C x. %s ) e. CC )' % (A0, LINT('G', S, T)))
    G4.append(LINT('G', S, T)); H4.append(LINT('H', S, T)); CG4.append('( C x. %s )' % LINT('G', S, T))
rvf = w.s([fv, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), RAW('A', 'B')))
rvg = w.s([gex, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('G', 'A', 'B'), RAW('A', 'B').replace('F lint', 'G lint')))
rvh = w.s([hex, ac, bc, w.inst('rectintval')], 'syl3anc', '( %s -> %s = %s )' % (A0, RINT('H', 'A', 'B'), RAW('A', 'B').replace('F lint', 'H lint')))
treeL = ('+', ('+', ('+', CG4[0], H4[0]), ('+', CG4[1], H4[1])), ('+', ('+', CG4[2], H4[2]), ('+', CG4[3], H4[3])))
p1 = w.s([sts[0], sts[1]], 'oveq12d', '( %s -> ( %s + %s ) = %s )' % (A0, LINT('F', *EDGES[0]), LINT('F', *EDGES[1]), tree_text(treeL[1])))
p2 = w.s([sts[2], sts[3]], 'oveq12d', '( %s -> ( %s + %s ) = %s )' % (A0, LINT('F', *EDGES[2]), LINT('F', *EDGES[3]), tree_text(treeL[2])))
p3 = w.s([p1, p2], 'oveq12d', '( %s -> %s = %s )' % (A0, RAW('A', 'B'), tree_text(treeL)))
key = {}
for i, x in enumerate(CG4): key[x] = i
for i, x in enumerate(H4): key[x] = 4 + i
cs = CxSum(w, A0, ccm, key)
nL, atL = cs.nf(treeL)
lhs = w.s([w.s([rvf, p3], 'eqtrd', '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), tree_text(treeL))), nL], 'eqtrd',
          '( %s -> %s = %s )' % (A0, RINT('F', 'A', 'B'), rn(atL)))
GS1 = '( %s + %s )' % (G4[0], G4[1]); GS2 = '( %s + %s )' % (G4[2], G4[3])
cg1 = w.s([ccm[G4[0]], ccm[G4[1]]], 'addcld', '( %s -> %s e. CC )' % (A0, GS1))
cg2 = w.s([ccm[G4[2]], ccm[G4[3]]], 'addcld', '( %s -> %s e. CC )' % (A0, GS2))
a1 = w.s([ccx, ccm[G4[0]], ccm[G4[1]]], 'adddid', '( %s -> ( C x. %s ) = ( %s + %s ) )' % (A0, GS1, CG4[0], CG4[1]))
a2 = w.s([ccx, ccm[G4[2]], ccm[G4[3]]], 'adddid', '( %s -> ( C x. %s ) = ( %s + %s ) )' % (A0, GS2, CG4[2], CG4[3]))
a3 = w.s([ccx, cg1, cg2], 'adddid', '( %s -> ( C x. ( %s + %s ) ) = ( ( C x. %s ) + ( C x. %s ) ) )' % (A0, GS1, GS2, GS1, GS2))
treeCG = ('+', ('+', CG4[0], CG4[1]), ('+', CG4[2], CG4[3]))
a4 = w.s([a3, w.s([a1, a2], 'oveq12d', '( %s -> ( ( C x. %s ) + ( C x. %s ) ) = %s )' % (A0, GS1, GS2, tree_text(treeCG)))], 'eqtrd',
         '( %s -> ( C x. ( %s + %s ) ) = %s )' % (A0, GS1, GS2, tree_text(treeCG)))
cgr = w.s([w.s([rvg], 'oveq2d', '( %s -> ( C x. %s ) = ( C x. ( %s + %s ) ) )' % (A0, RINT('G', 'A', 'B'), GS1, GS2)), a4], 'eqtrd',
          '( %s -> ( C x. %s ) = %s )' % (A0, RINT('G', 'A', 'B'), tree_text(treeCG)))
treeH = ('+', ('+', H4[0], H4[1]), ('+', H4[2], H4[3]))
treeR = ('+', treeCG, treeH)
sm = w.s([cgr, rvh], 'oveq12d', '( %s -> ( ( C x. %s ) + %s ) = %s )' % (A0, RINT('G', 'A', 'B'), RINT('H', 'A', 'B'), tree_text(treeR)))
nR, atR = cs.nf(treeR)
rhs = w.s([sm, nR], 'eqtrd', '( %s -> ( ( C x. %s ) + %s ) = %s )' % (A0, RINT('G', 'A', 'B'), RINT('H', 'A', 'B'), rn(atR)))
w.qed([lhs, rhs], 'eqtr4d', '( %s -> %s = ( ( C x. %s ) + %s ) )' % (A0, RINT('F', 'A', 'B'), RINT('G', 'A', 'B'), RINT('H', 'A', 'B'))); run1(w)

# ---- rectintabse -----------------------------------------------------------
w = W('rectintabse', 'The ML inequality for a rectangle boundary integral, with '
      'the bound on the values assumed only on a set containing the boundary frame.')
ALM = 'A. u e. E ( abs ` ( F ` u ) ) <_ M'
A0 = '( %s /\\ M e. RR /\\ %s )' % (PSE, ALM)
WD = '( %s - %s )' % (RB, RA); HT = '( %s - %s )' % (IB, IA)
d = ctxe(w, A0)
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
BND = {('A', P10): WD, (P10, 'B'): HT, ('B', P01): WD, (P01, 'A'): HT}
bnd = []; ccm = {}
for i, (S, T) in enumerate(EDGES):
    ph = phsege(w, A0, d, i)
    ccm[LINT('F', S, T)] = w.s([ph, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('F', S, T)))
    sr = w.s([d['se'][i], w.inst('ssralv')], 'syl', '( %s -> ( %s -> A. u e. %s ( abs ` ( F ` u ) ) <_ M ) )' % (A0, ALM, SEGS[i]))
    al = w.s([sr, alm], 'mpd', '( %s -> A. u e. %s ( abs ` ( F ` u ) ) <_ M )' % (A0, SEGS[i]))
    la = w.s([ph, mr, al, w.inst('lintabs')], 'syl3anc', '( %s -> ( abs ` %s ) <_ ( M x. ( abs ` ( %s - %s ) ) ) )' % (A0, LINT('F', S, T), T, S))
    rw = w.s([absv[(S, T)]], 'oveq2d', '( %s -> ( M x. ( abs ` ( %s - %s ) ) ) = ( M x. %s ) )' % (A0, T, S, BND[(S, T)]))
    bnd.append(w.s([la, rw], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( M x. %s ) )' % (A0, LINT('F', S, T), BND[(S, T)])))
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
chn = w.s([w.s([w.s([c1, c2], 'addcld', '( %s -> ( %s + %s ) e. CC )' % (A0, S1, S2))], 'abscld', '( %s -> ( abs ` ( %s + %s ) ) e. RR )' % (A0, S1, S2)),
           w.s([ar1, ar2], 'readdcld', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) e. RR )' % (A0, S1, S2)),
           w.s([mwh, mwh], 'readdcld', '( %s -> ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) e. RR )' % (A0, WD, HT, WD, HT)), tri0, tot], 'letrd',
          '( %s -> ( abs ` ( %s + %s ) ) <_ ( ( ( M x. %s ) + ( M x. %s ) ) + ( ( M x. %s ) + ( M x. %s ) ) ) )' % (A0, S1, S2, WD, HT, WD, HT))
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
      '( %s -> ( abs ` ( F rectint <. A , B >. ) ) <_ ( ( 2 x. M ) x. ( %s + %s ) ) )' % (A0, WD, HT)); run1(w)
