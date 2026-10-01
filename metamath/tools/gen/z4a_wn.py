"""Sortie Z4a, batch 4: the induced-character step (LargeSieve W_norm_eq)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from z4alib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

DQ = DB('Q'); DF = DB('F'); LQ = LZ('Q'); LF = LZ('F'); IQ = INV('Q'); IF = INV('F')
IFY = '( %s ` Y )' % IF; X = EMB('F', 'Q', 'Y'); TQ = GS('Q', X); R = '( Q / F )'
def grp(w, ante, nst, n):
    g = w.s([], 'eqid', '( DChr ` %s ) = ( DChr ` %s )' % (n, n))
    ab = w.s([nst, w.s([g], 'dchrabl', '( %s e. NN -> ( DChr ` %s ) e. Abel )' % (n, n))], 'syl', '( %s -> ( DChr ` %s ) e. Abel )' % (ante, n))
    return w.s([ab, w.inst('ablgrp')], 'syl', '( %s -> ( DChr ` %s ) e. Grp )' % (ante, n))
def hwn_parts(w, ante):
    """from ( ante -> HWN ) pieces: q, f, dv, sqf, cop, y, ycond, h3 = ( F e. NN /\\ Q e. NN /\\ F || Q )"""
    hwn = w.s([], 'id', '( %s -> %s )' % (ante, ante)) if ante == HWN else None
    return hwn

# ---- dchrwnormlem1
A0 = '( %s /\\ U e. ZZ /\\ ( U gcd Q ) = 1 )' % HWN
w = W('dchrwnormlem1', 'Lemma for dchrwnorm: the inverse of the induced inverse character is the induced character, whose value at a unit is the value of the primitive character (Lean hchinv, heval).')
hwn = w.s([], 'simp1', '( %s -> %s )' % (A0, HWN)); u = w.s([], 'simp2', '( %s -> U e. ZZ )' % A0); ucop = w.s([], 'simp3', '( %s -> ( U gcd Q ) = 1 )' % A0)
p1 = w.s([hwn], 'simp1d', '( %s -> ( Q e. NN /\\ F e. NN /\\ F || Q ) )' % A0); p3 = w.s([hwn], 'simp3d', '( %s -> ( Y e. %s /\\ ( F DChrCond Y ) = F ) )' % (A0, DF))
q = w.s([p1], 'simp1d', '( %s -> Q e. NN )' % A0); f = w.s([p1], 'simp2d', '( %s -> F e. NN )' % A0); dv = w.s([p1], 'simp3d', '( %s -> F || Q )' % A0)
y = w.s([p3], 'simpld', '( %s -> Y e. %s )' % (A0, DF))
h3 = w.s([f, q, dv], '3jca', '( %s -> ( F e. NN /\\ Q e. NN /\\ F || Q ) )' % A0)
ify = grpinv(w, A0, f, y, 'F', 'Y')
inv = w.s([w.s([h3, ify], 'jca', '( %s -> ( ( F e. NN /\\ Q e. NN /\\ F || Q ) /\\ %s e. %s ) )' % (A0, IFY, DF)), w.inst('dchrindinv')], 'syl', '( %s -> ( ( F DChrInd Q ) ` ( %s ` %s ) ) = ( %s ` %s ) )' % (A0, IF, IFY, IQ, X))
gf = grp(w, A0, f, 'F')
ii = w.s([gf, y, w.s([w.s([], 'eqid', '%s = %s' % (DF, DF)), w.s([], 'eqid', '%s = %s' % (IF, IF))], 'grpinvinv', '( ( ( DChr ` F ) e. Grp /\\ Y e. %s ) -> ( %s ` %s ) = Y )' % (DF, IF, IFY))], 'syl2anc', '( %s -> ( %s ` %s ) = Y )' % (A0, IF, IFY))
e1 = w.s([w.s([ii], 'fveq2d', '( %s -> ( ( F DChrInd Q ) ` ( %s ` %s ) ) = ( ( F DChrInd Q ) ` Y ) )' % (A0, IF, IFY)), inv], 'eqtr3d', '( %s -> ( ( F DChrInd Q ) ` Y ) = ( %s ` %s ) )' % (A0, IQ, X))
v1 = w.s([w.s([h3, y], 'jca', '( %s -> ( ( F e. NN /\\ Q e. NN /\\ F || Q ) /\\ Y e. %s ) )' % (A0, DF)), u, ucop, w.inst('dchrindval1')], 'syl3anc', '( %s -> ( ( ( F DChrInd Q ) ` Y ) ` ( %s ` U ) ) = ( Y ` ( %s ` U ) ) )' % (A0, LQ, LF))
w.qed([w.s([w.s([e1], 'eqcomd', '( %s -> ( %s ` %s ) = ( ( F DChrInd Q ) ` Y ) )' % (A0, IQ, X))], 'fveq1d', '( %s -> ( ( %s ` %s ) ` ( %s ` U ) ) = ( ( ( F DChrInd Q ) ` Y ) ` ( %s ` U ) ) )' % (A0, IQ, X, LQ, LQ)), v1], 'eqtrd', '( %s -> ( ( %s ` %s ) ` ( %s ` U ) ) = ( Y ` ( %s ` U ) ) )' % (A0, IQ, X, LQ, LF)); run(w)

# ---- dchrwnormlem2
A0 = HWN
RF = '( %s x. F )' % R
w = W('dchrwnormlem2', 'Lemma for dchrwnorm: the Gauss sum of the induced inverse character has squared modulus F (Lean htau, from norm_sq_gaussSum_changeLevel and conductor_inv).')
p1 = w.s([], 'simp1', '( %s -> ( Q e. NN /\\ F e. NN /\\ F || Q ) )' % A0); p2 = w.s([], 'simp2', '( %s -> ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd F ) = 1 ) )' % (A0, R, R)); p3 = w.s([], 'simp3', '( %s -> ( Y e. %s /\\ ( F DChrCond Y ) = F ) )' % (A0, DF))
q = w.s([p1], 'simp1d', '( %s -> Q e. NN )' % A0); f = w.s([p1], 'simp2d', '( %s -> F e. NN )' % A0); dv = w.s([p1], 'simp3d', '( %s -> F || Q )' % A0)
y = w.s([p3], 'simpld', '( %s -> Y e. %s )' % (A0, DF)); yc = w.s([p3], 'simprd', '( %s -> ( F DChrCond Y ) = F )' % A0)
r = w.s([dv, w.s([q, f, w.inst('nndivdvds')], 'syl2anc', '( %s -> ( F || Q <-> %s e. NN ) )' % (A0, R))], 'mpbid', '( %s -> %s e. NN )' % (A0, R))
ify = grpinv(w, A0, f, y, 'F', 'Y')
ci = w.s([w.s([f, y], 'jca', '( %s -> ( F e. NN /\\ Y e. %s ) )' % (A0, DF)), w.inst('dchrcondinv')], 'syl', '( %s -> ( F DChrCond %s ) = ( F DChrCond Y ) )' % (A0, IFY))
cond = w.s([ci, yc], 'eqtrd', '( %s -> ( F DChrCond %s ) = F )' % (A0, IFY))
ind = w.s([w.s([r, f], 'jca', '( %s -> ( %s e. NN /\\ F e. NN ) )' % (A0, R)), p2, w.s([ify, cond], 'jca', '( %s -> ( %s e. %s /\\ ( F DChrCond %s ) = F ) )' % (A0, IFY, DF, IFY)), w.inst('dchrgsind')], 'syl3anc', '( %s -> ( ( abs ` ( %s DChrGS ( ( F DChrInd %s ) ` %s ) ) ) ^ 2 ) = F )' % (A0, RF, RF, IFY))
can = w.s([w.s([q], 'nncnd', '( %s -> Q e. CC )' % A0), w.s([f], 'nncnd', '( %s -> F e. CC )' % A0), w.s([f], 'nnne0d', '( %s -> F =/= 0 )' % A0)], 'divcan1d', '( %s -> %s = Q )' % (A0, RF))
c1 = w.s([w.s([w.s([can], 'oveq2d', '( %s -> ( F DChrInd %s ) = ( F DChrInd Q ) )' % (A0, RF))], 'fveq1d', '( %s -> ( ( F DChrInd %s ) ` %s ) = %s )' % (A0, RF, IFY, X))], 'oveq12d', '( %s -> ( %s DChrGS ( ( F DChrInd %s ) ` %s ) ) = %s )' % (A0, RF, RF, IFY, TQ))
w.lines.pop()
c1 = w.s([can, w.s([w.s([can], 'oveq2d', '( %s -> ( F DChrInd %s ) = ( F DChrInd Q ) )' % (A0, RF))], 'fveq1d', '( %s -> ( ( F DChrInd %s ) ` %s ) = %s )' % (A0, RF, IFY, X))], 'oveq12d', '( %s -> ( %s DChrGS ( ( F DChrInd %s ) ` %s ) ) = %s )' % (A0, RF, RF, IFY, TQ))
c2 = w.s([w.s([c1], 'fveq2d', '( %s -> ( abs ` ( %s DChrGS ( ( F DChrInd %s ) ` %s ) ) ) = ( abs ` %s ) )' % (A0, RF, RF, IFY, TQ))], 'oveq1d', '( %s -> ( ( abs ` ( %s DChrGS ( ( F DChrInd %s ) ` %s ) ) ) ^ 2 ) = ( ( abs ` %s ) ^ 2 ) )' % (A0, RF, RF, IFY, TQ))
w.qed([c2, ind], 'eqtr3d', '( %s -> ( ( abs ` %s ) ^ 2 ) = F )' % (A0, TQ)); run(w)

# ---- dchrwnorm
A0 = '( %s /\\ %s /\\ %s )' % (HWN, HW, COPALL('Q'))
XU = EV(X, 'Q', 'u'); TZU = TZ('Q', 'u'); AN = '( A ` n )'
LHS = 'sum_ u e. %s ( %s x. %s )' % (CR('Q'), XU, TZU)
IXN = IX(X, 'Q', 'n'); SI = 'sum_ n e. W ( %s x. %s )' % (AN, IXN); SY = WSUM('Y', 'F')
w = W('dchrwnorm', 'The induced-character step (LargeSieve W_norm_eq): for a primitive character Y mod F and the squarefree cofactor Q / F coprime to F, the squared modulus of the twisted average of the induced inverse character over the coprime residues mod Q is F times the squared modulus of the Y-twisted window sum.')
hwn = w.s([], 'simp1', '( %s -> %s )' % (A0, HWN)); hw = w.s([], 'simp2', '( %s -> %s )' % (A0, HW)); cop = w.s([], 'simp3', '( %s -> %s )' % (A0, COPALL('Q')))
p1 = w.s([hwn], 'simp1d', '( %s -> ( Q e. NN /\\ F e. NN /\\ F || Q ) )' % A0); p3 = w.s([hwn], 'simp3d', '( %s -> ( Y e. %s /\\ ( F DChrCond Y ) = F ) )' % (A0, DF))
q = w.s([p1], 'simp1d', '( %s -> Q e. NN )' % A0); f = w.s([p1], 'simp2d', '( %s -> F e. NN )' % A0); dv = w.s([p1], 'simp3d', '( %s -> F || Q )' % A0)
y = w.s([p3], 'simpld', '( %s -> Y e. %s )' % (A0, DF))
ify = grpinv(w, A0, f, y, 'F', 'Y')
xcl = w.s([w.s([w.s([f, q, dv], '3jca', '( %s -> ( F e. NN /\\ Q e. NN /\\ F || Q ) )' % A0), ify], 'jca', '( %s -> ( ( F e. NN /\\ Q e. NN /\\ F || Q ) /\\ %s e. %s ) )' % (A0, IFY, DF)), w.inst('dchrindcl')], 'syl', '( %s -> %s e. %s )' % (A0, X, DQ))
hcq = w.s([q, xcl], 'jca', '( %s -> ( Q e. NN /\\ %s e. %s ) )' % (A0, X, DQ))
tw = w.s([hcq, hw, cop, w.inst('dchrtwsum')], 'syl3anc', '( %s -> %s = ( %s x. %s ) )' % (A0, LHS, TQ, SI))
An = '( %s /\\ n e. W )' % A0
nmem = w.s([], 'simpr', '( %s -> n e. W )' % An)
nz, an = win(w, An, w.s([hw], 'adantr', '( %s -> %s )' % (An, HW)), nmem)
ncop = copn(w, An, w.s([cop], 'adantr', '( %s -> %s )' % (An, COPALL('Q'))), nmem, 'Q')
l1 = w.s([w.s([hwn], 'adantr', '( %s -> %s )' % (An, HWN)), nz, ncop, w.inst('dchrwnormlem1')], 'syl3anc', '( %s -> %s = %s )' % (An, IXN, EV('Y', 'F', 'n')))
s1 = w.s([w.s([w.s([l1], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (An, AN, IXN, AN, EV('Y', 'F', 'n')))], 'sumeq2dv', '( %s -> %s = %s )' % (A0, SI, SY))], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, TQ, SI, TQ, SY))
eq = w.s([tw, s1], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A0, LHS, TQ, SY))
tcl = w.s([hcq, w.inst('dchrgscl')], 'syl', '( %s -> %s e. CC )' % (A0, TQ))
g, z, d, l = dchyp(w, 'F')
yn = w.s([g, z, d, l, w.s([y], 'adantr', '( %s -> Y e. %s )' % (An, DF)), nz], 'dchrzrhcl', '( %s -> %s e. CC )' % (An, EV('Y', 'F', 'n')))
sycl = w.s([w.s([hw], 'simp1d', '( %s -> W e. Fin )' % A0), w.s([an, yn], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (An, AN, EV('Y', 'F', 'n')))], 'fsumcl', '( %s -> %s e. CC )' % (A0, SY))
a1 = w.s([w.s([w.s([eq], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( %s x. %s ) ) )' % (A0, LHS, TQ, SY)), w.s([tcl, sycl], 'absmuld', '( %s -> ( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (A0, TQ, SY, TQ, SY))], 'eqtrd', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (A0, LHS, TQ, SY))], 'oveq1d', '( %s -> %s = ( ( ( abs ` %s ) x. ( abs ` %s ) ) ^ 2 ) )' % (A0, ABS2(LHS), TQ, SY))
tab = w.s([w.s([tcl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, TQ))], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (A0, TQ)); sab = w.s([w.s([sycl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, SY))], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (A0, SY))
a2 = w.s([tab, sab, w.s([], '2nn0', '2 e. NN0'), ], 'mulexpd', '( %s -> ( ( ( abs ` %s ) x. ( abs ` %s ) ) ^ 2 ) = ( %s x. %s ) )' % (A0, TQ, SY, ABS2(TQ), ABS2(SY)))
w.lines.pop()
two = w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A0)
a2 = w.s([tab, sab, two], 'mulexpd', '( %s -> ( ( ( abs ` %s ) x. ( abs ` %s ) ) ^ 2 ) = ( %s x. %s ) )' % (A0, TQ, SY, ABS2(TQ), ABS2(SY)))
a3 = w.s([w.s([hwn, w.inst('dchrwnormlem2')], 'syl', '( %s -> %s = F )' % (A0, ABS2(TQ)))], 'oveq1d', '( %s -> ( %s x. %s ) = ( F x. %s ) )' % (A0, ABS2(TQ), ABS2(SY), ABS2(SY)))
w.qed([w.s([a1, a2], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A0, ABS2(LHS), ABS2(TQ), ABS2(SY))), a3], 'eqtrd', '( %s -> %s = ( F x. %s ) )' % (A0, ABS2(LHS), ABS2(SY))); run(w)
