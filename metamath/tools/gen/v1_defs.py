"""Sortie V1, batch 1: value lemmas, closure and nonnegativity of psiAP, thetaAP, piAP, psiChar."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
sys.path.insert(0, os.path.dirname(__file__)); from v1_lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ---- psiapfval
w = W('psiapfval', 'Value of the function psiAP at a modulus: the operation sending a residue and a real to the psi sum of the residue class.')
c1 = w.s([], 'oveq2', '( q = Q -> ( n mod q ) = ( n mod Q ) )')
c2 = w.s([], 'oveq2', '( q = Q -> ( a mod q ) = ( a mod Q ) )')
c3 = w.s([c1, c2], 'eqeq12d', '( q = Q -> ( %s <-> %s ) )' % (COND('n', 'q', 'a'), COND('n', 'Q', 'a')))
c4 = w.s([c3], 'ifbid', '( q = Q -> %s = %s )' % (IFL('n', 'q', 'a'), IFL('n', 'Q', 'a')))
c5 = w.s([c4], 'sumeq2sdv', '( q = Q -> %s = %s )' % (PSISUM('q', 'a', 'y'), PSISUM('Q', 'a', 'y')))
c6 = w.s([c5], 'mpoeq3dv', '( q = Q -> %s = %s )' % (MPO(PSISUM('q', 'a', 'y')), MPO(PSISUM('Q', 'a', 'y'))))
d = w.s([], 'df-psiap', 'psiAP = ( q e. NN |-> %s )' % MPO(PSISUM('q', 'a', 'y')))
z = w.s([], 'zex', 'ZZ e. _V'); r = w.s([], 'reex', 'RR e. _V')
e = w.s([], 'mpoexga', '( ( ZZ e. _V /\\ RR e. _V ) -> %s e. _V )' % MPO(PSISUM('Q', 'a', 'y')))
e2 = w.s([z, r, e], 'mp2an', '%s e. _V' % MPO(PSISUM('Q', 'a', 'y')))
w.qed([c6, d, e2], 'fvmpt', '( Q e. NN -> ( psiAP ` Q ) = %s )' % MPO(PSISUM('Q', 'a', 'y'))); run(w)

# ---- thetaapfval
w = W('thetaapfval', 'Value of the function thetaAP at a modulus.')
c1 = w.s([], 'oveq2', '( q = Q -> ( n mod q ) = ( n mod Q ) )')
c2 = w.s([], 'oveq2', '( q = Q -> ( a mod q ) = ( a mod Q ) )')
c3 = w.s([c1, c2], 'eqeq12d', '( q = Q -> ( %s <-> %s ) )' % (COND('n', 'q', 'a'), COND('n', 'Q', 'a')))
c3b = w.s([c3], 'anbi2d', '( q = Q -> ( ( n e. Prime /\\ %s ) <-> ( n e. Prime /\\ %s ) ) )' % (COND('n', 'q', 'a'), COND('n', 'Q', 'a')))
c4 = w.s([c3b], 'rabbidv', '( q = Q -> %s = %s )' % (RAB('q', 'a', 'y'), RAB('Q', 'a', 'y')))
c5 = w.s([c4], 'sumeq1d', '( q = Q -> %s = %s )' % (THSUM('q', 'a', 'y'), THSUM('Q', 'a', 'y')))
c6 = w.s([c5], 'mpoeq3dv', '( q = Q -> %s = %s )' % (MPO(THSUM('q', 'a', 'y')), MPO(THSUM('Q', 'a', 'y'))))
d = w.s([], 'df-thetaap', 'thetaAP = ( q e. NN |-> %s )' % MPO(THSUM('q', 'a', 'y')))
z = w.s([], 'zex', 'ZZ e. _V'); r = w.s([], 'reex', 'RR e. _V')
e = w.s([], 'mpoexga', '( ( ZZ e. _V /\\ RR e. _V ) -> %s e. _V )' % MPO(THSUM('Q', 'a', 'y')))
e2 = w.s([z, r, e], 'mp2an', '%s e. _V' % MPO(THSUM('Q', 'a', 'y')))
w.qed([c6, d, e2], 'fvmpt', '( Q e. NN -> ( thetaAP ` Q ) = %s )' % MPO(THSUM('Q', 'a', 'y'))); run(w)

# ---- piapfval
w = W('piapfval', 'Value of the function piAP at a modulus.')
c1 = w.s([], 'oveq2', '( q = Q -> ( n mod q ) = ( n mod Q ) )')
c2 = w.s([], 'oveq2', '( q = Q -> ( a mod q ) = ( a mod Q ) )')
c3 = w.s([c1, c2], 'eqeq12d', '( q = Q -> ( %s <-> %s ) )' % (COND('n', 'q', 'a'), COND('n', 'Q', 'a')))
c3b = w.s([c3], 'anbi2d', '( q = Q -> ( ( n e. Prime /\\ %s ) <-> ( n e. Prime /\\ %s ) ) )' % (COND('n', 'q', 'a'), COND('n', 'Q', 'a')))
c4 = w.s([c3b], 'rabbidv', '( q = Q -> %s = %s )' % (RAB('q', 'a', 'y'), RAB('Q', 'a', 'y')))
c5 = w.s([c4], 'fveq2d', '( q = Q -> %s = %s )' % (PISUM('q', 'a', 'y'), PISUM('Q', 'a', 'y')))
c6 = w.s([c5], 'mpoeq3dv', '( q = Q -> %s = %s )' % (MPO(PISUM('q', 'a', 'y')), MPO(PISUM('Q', 'a', 'y'))))
d = w.s([], 'df-piap', 'piAP = ( q e. NN |-> %s )' % MPO(PISUM('q', 'a', 'y')))
z = w.s([], 'zex', 'ZZ e. _V'); r = w.s([], 'reex', 'RR e. _V')
e = w.s([], 'mpoexga', '( ( ZZ e. _V /\\ RR e. _V ) -> %s e. _V )' % MPO(PISUM('Q', 'a', 'y')))
e2 = w.s([z, r, e], 'mp2an', '%s e. _V' % MPO(PISUM('Q', 'a', 'y')))
w.qed([c6, d, e2], 'fvmpt', '( Q e. NN -> ( piAP ` Q ) = %s )' % MPO(PISUM('Q', 'a', 'y'))); run(w)

# ---- psicharfval
w = W('psicharfval', 'Value of the function psiChar at a modulus: the operation sending a Dirichlet character and a real to the twisted psi sum.')
c1 = w.s([], 'fveq2', '( q = Q -> ( DChr ` q ) = ( DChr ` Q ) )')
c2 = w.s([c1], 'fveq2d', '( q = Q -> %s = %s )' % (DB('q'), DB('Q')))
c3 = w.s([], 'eqidd', '( q = Q -> RR = RR )')
z1 = w.s([], 'fveq2', '( q = Q -> ( Z/nZ ` q ) = ( Z/nZ ` Q ) )')
z2 = w.s([z1], 'fveq2d', '( q = Q -> %s = %s )' % (LZ('q'), LZ('Q')))
z3 = w.s([z2], 'fveq1d', '( q = Q -> ( %s ` n ) = ( %s ` n ) )' % (LZ('q'), LZ('Q')))
z4 = w.s([z3], 'fveq2d', '( q = Q -> ( x ` ( %s ` n ) ) = ( x ` ( %s ` n ) ) )' % (LZ('q'), LZ('Q')))
z5 = w.s([z4], 'oveq1d', '( q = Q -> %s = %s )' % (CHTERM('q', 'x', 'n'), CHTERM('Q', 'x', 'n')))
z6 = w.s([z5], 'sumeq2sdv', '( q = Q -> %s = %s )' % (CHSUM('q', 'x', 'y'), CHSUM('Q', 'x', 'y')))
c6 = w.s([c2, c3, z6], 'mpoeq123dv', '( q = Q -> %s = %s )' % (MPOX('q', CHSUM('q', 'x', 'y')), MPOX('Q', CHSUM('Q', 'x', 'y'))))
d = w.s([], 'df-psichar', 'psiChar = ( q e. NN |-> %s )' % MPOX('q', CHSUM('q', 'x', 'y')))
z = w.s([], 'fvex', '%s e. _V' % DB('Q')); r = w.s([], 'reex', 'RR e. _V')
e = w.s([], 'mpoexga', '( ( %s e. _V /\\ RR e. _V ) -> %s e. _V )' % (DB('Q'), MPOX('Q', CHSUM('Q', 'x', 'y'))))
e2 = w.s([z, r, e], 'mp2an', '%s e. _V' % MPOX('Q', CHSUM('Q', 'x', 'y')))
w.qed([c6, d, e2], 'fvmpt', '( Q e. NN -> ( psiChar ` Q ) = %s )' % MPOX('Q', CHSUM('Q', 'x', 'y'))); run(w)

# ---- the values at a residue and a point
def valws(label, desc, fval, mpo_qay, body_QAY, body_Qay, sym, congr):
    """congr(w, HH) returns the step proving ( HH -> body_Qay = body_QAY )"""
    w = W(label, desc)
    f0 = w.s([], fval, '( Q e. NN -> ( %s ` Q ) = %s )' % (sym, mpo_qay))
    f = w.s([f0], '3ad2ant1', '( %s -> ( %s ` Q ) = %s )' % (H, sym, mpo_qay))
    HH = '( %s /\\ ( a = A /\\ y = Y ) )' % H
    s = congr(w, HH)
    ha = w.s([], 'simp2', '( %s -> A e. ZZ )' % H); hy = w.s([], 'simp3', '( %s -> Y e. RR )' % H)
    ex = w.s([], 'sumex' if body_QAY.startswith('sum_') else 'fvex', '%s e. _V' % body_QAY)
    exd = w.s([ex], 'a1i', '( %s -> %s e. _V )' % (H, body_QAY))
    w.qed([f, s, ha, hy, exd], 'ovmpod', '( %s -> ( A ( %s ` Q ) Y ) = %s )' % (H, sym, body_QAY))
    return w

def congr_psi(w, HH):
    a1 = w.s([], 'simprl', '( %s -> a = A )' % HH); y1 = w.s([], 'simprr', '( %s -> y = Y )' % HH)
    y2 = w.s([y1], 'fveq2d', '( %s -> ( |_ ` y ) = ( |_ ` Y ) )' % HH); y3 = w.s([y2], 'oveq2d', '( %s -> %s = %s )' % (HH, FZ('y'), FZ('Y')))
    a2 = w.s([a1], 'oveq1d', '( %s -> ( a mod Q ) = ( A mod Q ) )' % HH)
    a3 = w.s([a2], 'eqeq2d', '( %s -> ( %s <-> %s ) )' % (HH, COND('n', 'Q', 'a'), COND('n', 'Q', 'A')))
    a4 = w.s([a3], 'ifbid', '( %s -> %s = %s )' % (HH, IFL('n', 'Q', 'a'), IFL('n', 'Q', 'A')))
    a5 = w.s([a4], 'adantr', '( ( %s /\\ n e. %s ) -> %s = %s )' % (HH, FZ('y'), IFL('n', 'Q', 'a'), IFL('n', 'Q', 'A')))
    return w.s([y3, a5], 'sumeq12dv', '( %s -> %s = %s )' % (HH, PSISUM('Q', 'a', 'y'), PSISUM('Q', 'A', 'Y')))

def congr_rab(w, HH):
    a1 = w.s([], 'simprl', '( %s -> a = A )' % HH); y1 = w.s([], 'simprr', '( %s -> y = Y )' % HH)
    y2 = w.s([y1], 'fveq2d', '( %s -> ( |_ ` y ) = ( |_ ` Y ) )' % HH); y3 = w.s([y2], 'oveq2d', '( %s -> %s = %s )' % (HH, FZ('y'), FZ('Y')))
    a2 = w.s([a1], 'oveq1d', '( %s -> ( a mod Q ) = ( A mod Q ) )' % HH)
    a3 = w.s([a2], 'eqeq2d', '( %s -> ( %s <-> %s ) )' % (HH, COND('n', 'Q', 'a'), COND('n', 'Q', 'A')))
    a4 = w.s([a3], 'anbi2d', '( %s -> ( ( n e. Prime /\\ %s ) <-> ( n e. Prime /\\ %s ) ) )' % (HH, COND('n', 'Q', 'a'), COND('n', 'Q', 'A')))
    return w.s([y3, a4], 'rabeqbidv', '( %s -> %s = %s )' % (HH, RAB('Q', 'a', 'y'), RAB('Q', 'A', 'Y')))

w = valws('psiapval', 'Value of psi in a residue class (Lean: psiAP_def).', 'psiapfval', MPO(PSISUM('Q', 'a', 'y')), PSISUM('Q', 'A', 'Y'), PSISUM('Q', 'a', 'y'), 'psiAP', congr_psi); run(w)
w = valws('thetaapval', 'Value of theta in a residue class (Lean: thetaAP_def).', 'thetaapfval', MPO(THSUM('Q', 'a', 'y')), THSUM('Q', 'A', 'Y'), THSUM('Q', 'a', 'y'), 'thetaAP',
          lambda w, HH: w.s([congr_rab(w, HH)], 'sumeq1d', '( %s -> %s = %s )' % (HH, THSUM('Q', 'a', 'y'), THSUM('Q', 'A', 'Y')))); run(w)
w = valws('piapval', 'Value of the prime-counting function in a residue class (Lean: piAP_def).', 'piapfval', MPO(PISUM('Q', 'a', 'y')), PISUM('Q', 'A', 'Y'), PISUM('Q', 'a', 'y'), 'piAP',
          lambda w, HH: w.s([congr_rab(w, HH)], 'fveq2d', '( %s -> %s = %s )' % (HH, PISUM('Q', 'a', 'y'), PISUM('Q', 'A', 'Y')))); run(w)

# ---- psicharval
w = W('psicharval', 'Value of the character-twisted psi (Lean: psiChar_def).')
f0 = w.s([], 'psicharfval', '( Q e. NN -> ( psiChar ` Q ) = %s )' % MPOX('Q', CHSUM('Q', 'x', 'y')))
f = w.s([f0], '3ad2ant1', '( %s -> ( psiChar ` Q ) = %s )' % (HX, MPOX('Q', CHSUM('Q', 'x', 'y'))))
HH = '( %s /\\ ( x = X /\\ y = Y ) )' % HX
x1 = w.s([], 'simprl', '( %s -> x = X )' % HH); y1 = w.s([], 'simprr', '( %s -> y = Y )' % HH)
y2 = w.s([y1], 'fveq2d', '( %s -> ( |_ ` y ) = ( |_ ` Y ) )' % HH); y3 = w.s([y2], 'oveq2d', '( %s -> %s = %s )' % (HH, FZ('y'), FZ('Y')))
x2 = w.s([x1], 'fveq1d', '( %s -> ( x ` ( %s ` n ) ) = ( X ` ( %s ` n ) ) )' % (HH, LZ('Q'), LZ('Q')))
x3 = w.s([x2], 'oveq1d', '( %s -> %s = %s )' % (HH, CHTERM('Q', 'x', 'n'), CHTERM('Q', 'X', 'n')))
x4 = w.s([x3], 'adantr', '( ( %s /\\ n e. %s ) -> %s = %s )' % (HH, FZ('y'), CHTERM('Q', 'x', 'n'), CHTERM('Q', 'X', 'n')))
s = w.s([y3, x4], 'sumeq12dv', '( %s -> %s = %s )' % (HH, CHSUM('Q', 'x', 'y'), CHSUM('Q', 'X', 'Y')))
hx = w.s([], 'simp2', '( %s -> X e. %s )' % (HX, DB('Q'))); hy = w.s([], 'simp3', '( %s -> Y e. RR )' % HX)
ex = w.s([], 'sumex', '%s e. _V' % CHSUM('Q', 'X', 'Y')); exd = w.s([ex], 'a1i', '( %s -> %s e. _V )' % (HX, CHSUM('Q', 'X', 'Y')))
w.qed([f, s, hx, hy, exd], 'ovmpod', '( %s -> ( X ( psiChar ` Q ) Y ) = %s )' % (HX, CHSUM('Q', 'X', 'Y'))); run(w)

# ---- summand lemmas: nonnegative reals as ( 0 [,) +oo )
w = W('psiaplem1', 'The summand of psiAP is a nonnegative real.')
A = 'n e. NN'
l = w.s([], 'vmacl', '( %s -> ( Lam ` n ) e. RR )' % A); g = w.s([], 'vmage0', '( %s -> 0 <_ ( Lam ` n ) )' % A)
e = w.s([l, g, w.inst('elrege0')], 'sylanbrc', '( %s -> ( Lam ` n ) e. ( 0 [,) +oo ) )' % A)
z0 = w.s([], '0re', '0 e. RR'); z1 = w.s([], '0le0', '0 <_ 0'); z2 = w.s([z0, z1, w.inst('elrege0')], 'mpbir2an', '0 e. ( 0 [,) +oo )')
z3 = w.s([z2], 'a1i', '( %s -> 0 e. ( 0 [,) +oo ) )' % A)
w.qed([e, z3], 'ifcld', '( %s -> %s e. ( 0 [,) +oo ) )' % (A, IFL('n', 'Q', 'A'))); run(w)

w = W('thetaaplem1', 'The logarithm of a positive integer is a nonnegative real.')
A = 'p e. NN'
r = w.s([], 'nnrp', '( %s -> p e. RR+ )' % A); l = w.s([r], 'relogcld', '( %s -> ( log ` p ) e. RR )' % A)
re = w.s([], 'nnred', '( %s -> p e. RR )' % A); g1 = w.s([], 'nnge1', '( %s -> 1 <_ p )' % A)
g = w.s([re, g1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` p ) )' % A)
w.qed([l, g, w.inst('elrege0')], 'sylanbrc', '( %s -> ( log ` p ) e. ( 0 [,) +oo ) )' % A); run(w)

# ---- closure and nonnegativity
def summand_psi(w, ante, n='n'):
    """( ( ante /\\ n e. FZ(Y) ) -> IFL e. ( 0 [,) +oo ) ) and the RR / 0 <_ facts"""
    AA = '( %s /\\ %s e. %s )' % (ante, n, FZ('Y'))
    e1 = w.s([], 'simpr', '( %s -> %s e. %s )' % (AA, n, FZ('Y'))); e2 = w.s([e1, w.inst('elfznn')], 'syl', '( %s -> %s e. NN )' % (AA, n))
    e3 = w.s([e2, w.inst('psiaplem1')], 'syl', '( %s -> %s e. ( 0 [,) +oo ) )' % (AA, IFL(n, 'Q', 'A')))
    e4 = w.s([e3, w.inst('elrege0')], 'sylib', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (AA, IFL(n, 'Q', 'A'), IFL(n, 'Q', 'A')))
    r = w.s([e4], 'simpld', '( %s -> %s e. RR )' % (AA, IFL(n, 'Q', 'A'))); g = w.s([e4], 'simprd', '( %s -> 0 <_ %s )' % (AA, IFL(n, 'Q', 'A')))
    return r, g

w = W('psiapcl', 'Closure: psi in a residue class is a real number.')
v = w.s([], 'psiapval', '( %s -> %s = %s )' % (H, PSI, PSISUM('Q', 'A', 'Y')))
fi = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (H, FZ('Y')))
r, g = summand_psi(w, H)
s = w.s([fi, r], 'fsumrecl', '( %s -> %s e. RR )' % (H, PSISUM('Q', 'A', 'Y')))
w.qed([v, s], 'eqeltrd', '( %s -> %s e. RR )' % (H, PSI)); run(w)

w = W('psiapge0', 'psi in a residue class is nonnegative (Lean: psiAP_nonneg).')
v = w.s([], 'psiapval', '( %s -> %s = %s )' % (H, PSI, PSISUM('Q', 'A', 'Y')))
fi = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (H, FZ('Y')))
r, g = summand_psi(w, H)
s = w.s([fi, r, g], 'fsumge0', '( %s -> 0 <_ %s )' % (H, PSISUM('Q', 'A', 'Y')))
w.qed([s, v], 'breqtrrd', '( %s -> 0 <_ %s )' % (H, PSI)); run(w)

def summand_theta(w, ante):
    AA = '( %s /\\ p e. %s )' % (ante, S)
    e1 = w.s([], 'simpr', '( %s -> p e. %s )' % (AA, S)); e2 = w.s([e1, w.inst('elrabi')], 'syl', '( %s -> p e. %s )' % (AA, FZ('Y')))
    e2b = w.s([e2, w.inst('elfznn')], 'syl', '( %s -> p e. NN )' % AA)
    e3 = w.s([e2b, w.inst('thetaaplem1')], 'syl', '( %s -> ( log ` p ) e. ( 0 [,) +oo ) )' % AA)
    e4 = w.s([e3, w.inst('elrege0')], 'sylib', '( %s -> ( ( log ` p ) e. RR /\\ 0 <_ ( log ` p ) ) )' % AA)
    r = w.s([e4], 'simpld', '( %s -> ( log ` p ) e. RR )' % AA); g = w.s([e4], 'simprd', '( %s -> 0 <_ ( log ` p ) )' % AA)
    return r, g

w = W('thetaapcl', 'Closure: theta in a residue class is a real number.')
v = w.s([], 'thetaapval', '( %s -> %s = %s )' % (H, TH, THSUM('Q', 'A', 'Y')))
fi = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (H, FZ('Y'))); fi2 = w.s([fi, w.inst('rabfi')], 'syl', '( %s -> %s e. Fin )' % (H, S))
r, g = summand_theta(w, H)
s = w.s([fi2, r], 'fsumrecl', '( %s -> %s e. RR )' % (H, THSUM('Q', 'A', 'Y')))
w.qed([v, s], 'eqeltrd', '( %s -> %s e. RR )' % (H, TH)); run(w)

w = W('thetaapge0', 'theta in a residue class is nonnegative (Lean: thetaAP_nonneg).')
v = w.s([], 'thetaapval', '( %s -> %s = %s )' % (H, TH, THSUM('Q', 'A', 'Y')))
fi = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (H, FZ('Y'))); fi2 = w.s([fi, w.inst('rabfi')], 'syl', '( %s -> %s e. Fin )' % (H, S))
r, g = summand_theta(w, H)
s = w.s([fi2, r, g], 'fsumge0', '( %s -> 0 <_ %s )' % (H, THSUM('Q', 'A', 'Y')))
w.qed([s, v], 'breqtrrd', '( %s -> 0 <_ %s )' % (H, TH)); run(w)

w = W('piapcl', 'Closure: the prime count in a residue class is a nonnegative integer.')
v = w.s([], 'piapval', '( %s -> %s = %s )' % (H, PI, PISUM('Q', 'A', 'Y')))
fi = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (H, FZ('Y'))); fi2 = w.s([fi, w.inst('rabfi')], 'syl', '( %s -> %s e. Fin )' % (H, S))
h = w.s([fi2, w.inst('hashcl')], 'syl', '( %s -> %s e. NN0 )' % (H, PISUM('Q', 'A', 'Y')))
w.qed([v, h], 'eqeltrd', '( %s -> %s e. NN0 )' % (H, PI)); run(w)

w = W('psicharcl', 'Closure: the character-twisted psi is a complex number.')
v = w.s([], 'psicharval', '( %s -> %s = %s )' % (HX, PSICH, CHSUM('Q', 'X', 'Y')))
fi = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (HX, FZ('Y')))
AA = '( %s /\\ n e. %s )' % (HX, FZ('Y'))
e1 = w.s([], 'simpr', '( %s -> n e. %s )' % (AA, FZ('Y'))); e2 = w.s([e1, w.inst('elfznn')], 'syl', '( %s -> n e. NN )' % AA)
ez = w.s([e2], 'nnzd', '( %s -> n e. ZZ )' % AA)
g1 = w.s([], 'eqid', '( DChr ` Q ) = ( DChr ` Q )'); g2 = w.s([], 'eqid', '( Z/nZ ` Q ) = ( Z/nZ ` Q )')
g3 = w.s([], 'eqid', '%s = %s' % (DB('Q'), DB('Q'))); g4 = w.s([], 'eqid', '%s = %s' % (LZ('Q'), LZ('Q')))
hx = w.s([], 'simpl2', '( %s -> X e. %s )' % (AA, DB('Q')))
c = w.s([g1, g2, g3, g4, hx, ez], 'dchrzrhcl', '( %s -> ( X ` ( %s ` n ) ) e. CC )' % (AA, LZ('Q')))
l = w.s([e2, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` n ) e. RR )' % AA); lc = w.s([l], 'recnd', '( %s -> ( Lam ` n ) e. CC )' % AA)
m = w.s([c, lc], 'mulcld', '( %s -> %s e. CC )' % (AA, CHTERM('Q', 'X', 'n')))
s = w.s([fi, m], 'fsumcl', '( %s -> %s e. CC )' % (HX, CHSUM('Q', 'X', 'Y')))
w.qed([v, s], 'eqeltrd', '( %s -> %s e. CC )' % (HX, PSICH)); run(w)
