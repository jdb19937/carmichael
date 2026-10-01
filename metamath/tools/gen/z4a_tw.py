"""Sortie Z4a, batch 2: the Gauss-sum transfer (LargeSieve char_twisted_sum_eq)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from z4alib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

F0 = FZO('N'); CRN = CR('N'); DN = DB('N'); L = LZ('N'); T = GS('N', 'X')
XU = EV('X', 'N', 'u')

# ---- dchrtwsumlem
A0 = '( %s /\\ U e. ZZ /\\ ( U gcd N ) = 1 )' % HC
EU = E('( U x. u )'); EA = E('( U x. a )')
SU = 'sum_ u e. %s ( %s x. %s )' % (CRN, XU, EU); SA = 'sum_ a e. %s ( %s x. %s )' % (F0, EV('X', 'N', 'a'), EA)
w = W('dchrtwsumlem', 'Lemma for dchrtwsum: the character-twisted sum of the additive character at U u over the coprime residues u is the inverse character at U times the Gauss sum (Lean hinner).')
hc = w.s([], 'simp1', '( %s -> %s )' % (A0, HC)); n = w.s([hc], 'simpld', '( %s -> N e. NN )' % A0); x = w.s([hc], 'simprd', '( %s -> X e. %s )' % (A0, DN))
u = w.s([], 'simp2', '( %s -> U e. ZZ )' % A0); cop = w.s([], 'simp3', '( %s -> ( U gcd N ) = 1 )' % A0)
Au = '( %s /\\ u e. %s )' % (A0, F0)
uz = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (Au, F0)), w.inst('elfzoelz')], 'syl', '( %s -> u e. ZZ )' % Au)
uu = w.s([w.s([u], 'adantr', '( %s -> U e. ZZ )' % Au), uz], 'zmulcld', '( %s -> ( U x. u ) e. ZZ )' % Au)
bcl = ecl(w, Au, w.s([n], 'adantr', '( %s -> N e. NN )' % Au), w.s([uu], 'zcnd', '( %s -> ( U x. u ) e. CC )' % Au), '( U x. u )')
s1 = w.s([n, x, bcl], 'dchrsumcr', '( %s -> %s = sum_ u e. %s ( %s x. %s ) )' % (A0, SU, F0, XU, EU))
cv, C = cbvsum(w, F0, '( %s x. %s )' % (XU, EU), 'u', 'a')
assert C == '( %s x. %s )' % (EV('X', 'N', 'a'), EA), C
s2 = w.s([cv], 'a1i', '( %s -> sum_ u e. %s ( %s x. %s ) = %s )' % (A0, F0, XU, EU, SA))
s3 = w.s([hc, u, cop, w.inst('dchrgsshift')], 'syl3anc', '( %s -> %s = ( %s x. %s ) )' % (A0, SA, IX('X', 'N', 'U'), T))
w.qed([w.s([s1, s2], 'eqtrd', '( %s -> %s = %s )' % (A0, SU, SA)), s3], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A0, SU, IX('X', 'N', 'U'), T)); run(w)

# ---- dchrtwsum
A0 = '( %s /\\ %s /\\ %s )' % (HC, HW, COPALL('N'))
AN = '( A ` n )'; ENU = E('( n x. u )'); IXN = IX('X', 'N', 'n')
TZU = TZ('N', 'u')
G = '( %s x. ( %s x. %s ) )' % (XU, AN, ENU)   # X(L u) x. ( A n x. E(n u) )
G2 = '( %s x. ( %s x. %s ) )' % (AN, XU, ENU)  # A n x. ( X(L u) x. E(n u) )
LHS = 'sum_ u e. %s ( %s x. %s )' % (CRN, XU, TZU)
RHS = '( %s x. sum_ n e. W ( %s x. %s ) )' % (T, AN, IXN)
w = W('dchrtwsum', 'The Gauss-sum transfer (LargeSieve char_twisted_sum_eq): for coefficients supported on integers coprime to N, the character-twisted average over the coprime residues of the additive-character sums is the Gauss sum times the inverse-character-twisted coefficient sum.')
hc = w.s([], 'simp1', '( %s -> %s )' % (A0, HC)); n = w.s([hc], 'simpld', '( %s -> N e. NN )' % A0); x = w.s([hc], 'simprd', '( %s -> X e. %s )' % (A0, DN))
hw = w.s([], 'simp2', '( %s -> %s )' % (A0, HW)); cop = w.s([], 'simp3', '( %s -> %s )' % (A0, COPALL('N')))
wfin = w.s([hw], 'simp1d', '( %s -> W e. Fin )' % A0)
crf = crfin(w, A0)
g, z, d, l = dchyp(w)
Au = '( %s /\\ u e. %s )' % (A0, CRN); Aun = '( %s /\\ n e. W )' % Au
An = '( %s /\\ n e. W )' % A0; Anu = '( %s /\\ u e. %s )' % (An, CRN)
Aun2 = '( %s /\\ ( u e. %s /\\ n e. W ) )' % (A0, CRN)
def term_cl(ante, nst, xst, hwst, umem, nmem):
    """closures of X(L u), A n, E(n u) under ante"""
    uz = crz(w, ante, umem); nz, an = win(w, ante, hwst, nmem)
    xu = w.s([g, z, d, l, xst, uz], 'dchrzrhcl', '( %s -> %s e. CC )' % (ante, XU))
    nu = w.s([nz, uz], 'zmulcld', '( %s -> ( n x. u ) e. ZZ )' % ante)
    e = ecl(w, ante, nst, w.s([nu], 'zcnd', '( %s -> ( n x. u ) e. CC )' % ante), '( n x. u )')
    return xu, an, e
# step 1 under Au: xu x. TZ(u) = sum_n ( xu x. ( an x. E ) )
umem = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, CRN))
uz1 = crz(w, Au, umem)
xu1 = w.s([g, z, d, l, w.s([x], 'adantr', '( %s -> X e. %s )' % (Au, DN)), uz1], 'dchrzrhcl', '( %s -> %s e. CC )' % (Au, XU))
xu_, an_, e_ = term_cl(Aun, w.s([n], 'ad2antrr', '( %s -> N e. NN )' % Aun), w.s([x], 'ad2antrr', '( %s -> X e. %s )' % (Aun, DN)), w.s([hw], 'ad2antrr', '( %s -> %s )' % (Aun, HW)), w.s([umem], 'adantr', '( %s -> u e. %s )' % (Aun, CRN)), w.s([], 'simpr', '( %s -> n e. W )' % Aun))
bcl1 = w.s([an_, e_], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Aun, AN, ENU))
s1 = w.s([w.s([wfin], 'adantr', '( %s -> W e. Fin )' % Au), xu1, bcl1], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ n e. W %s )' % (Au, XU, TZU, G))
t1 = w.s([s1], 'sumeq2dv', '( %s -> %s = sum_ u e. %s sum_ n e. W %s )' % (A0, LHS, CRN, G))
# step 2: swap
un2 = w.s([], 'simpr', '( %s -> ( u e. %s /\\ n e. W ) )' % (Aun2, CRN))
xu2, an2, e2 = term_cl(Aun2, w.s([n], 'adantr', '( %s -> N e. NN )' % Aun2), w.s([x], 'adantr', '( %s -> X e. %s )' % (Aun2, DN)), w.s([hw], 'adantr', '( %s -> %s )' % (Aun2, HW)), w.s([un2], 'simpld', '( %s -> u e. %s )' % (Aun2, CRN)), w.s([un2], 'simprd', '( %s -> n e. W )' % Aun2))
gcl2 = w.s([xu2, w.s([an2, e2], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Aun2, AN, ENU))], 'mulcld', '( %s -> %s e. CC )' % (Aun2, G))
t2 = w.s([crf, wfin, gcl2], 'fsumcom', '( %s -> sum_ u e. %s sum_ n e. W %s = sum_ n e. W sum_ u e. %s %s )' % (A0, CRN, G, CRN, G))
# step 3 under An
nmem = w.s([], 'simpr', '( %s -> n e. W )' % An)
nz3, an3 = win(w, An, w.s([hw], 'adantr', '( %s -> %s )' % (An, HW)), nmem)
ncop = copn(w, An, w.s([cop], 'adantr', '( %s -> %s )' % (An, COPALL('N'))), nmem)
xu4, an4, e4 = term_cl(Anu, w.s([n], 'ad2antrr', '( %s -> N e. NN )' % Anu), w.s([x], 'ad2antrr', '( %s -> X e. %s )' % (Anu, DN)), w.s([hw], 'ad2antrr', '( %s -> %s )' % (Anu, HW)), w.s([], 'simpr', '( %s -> u e. %s )' % (Anu, CRN)), w.s([nmem], 'adantr', '( %s -> n e. W )' % Anu))
m12 = w.s([xu4, an4, e4], 'mul12d', '( %s -> %s = %s )' % (Anu, G, G2))
s3a = w.s([m12], 'sumeq2dv', '( %s -> sum_ u e. %s %s = sum_ u e. %s %s )' % (An, CRN, G, CRN, G2))
bcl4 = w.s([xu4, e4], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Anu, XU, ENU))
SXE = 'sum_ u e. %s ( %s x. %s )' % (CRN, XU, ENU)
s3b = w.s([w.s([crf], 'adantr', '( %s -> %s e. Fin )' % (An, CRN)), an3, bcl4], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ u e. %s %s )' % (An, AN, SXE, CRN, G2))
s3c = w.s([s3a, s3b], 'eqtr4d', '( %s -> sum_ u e. %s %s = ( %s x. %s ) )' % (An, CRN, G, AN, SXE))
lem = w.s([w.s([hc], 'adantr', '( %s -> %s )' % (An, HC)), nz3, ncop, w.inst('dchrtwsumlem')], 'syl3anc', '( %s -> %s = ( %s x. %s ) )' % (An, SXE, IXN, T))
s3d = w.s([lem], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. %s ) ) )' % (An, AN, SXE, AN, IXN, T))
ixn = ixcl(w, An, w.s([n], 'adantr', '( %s -> N e. NN )' % An), w.s([x], 'adantr', '( %s -> X e. %s )' % (An, DN)), nz3, 'N', 'X', 'n')
tcl = w.s([hc, w.inst('dchrgscl')], 'syl', '( %s -> %s e. CC )' % (A0, T)); tcln = w.s([tcl], 'adantr', '( %s -> %s e. CC )' % (An, T))
s3e = w.s([w.s([an3, ixn, tcln], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) ) )' % (An, AN, IXN, T, AN, IXN, T))], 'eqcomd', '( %s -> ( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s ) )' % (An, AN, IXN, T, AN, IXN, T))
s3f = w.s([w.s([an3, ixn], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (An, AN, IXN)), tcln], 'mulcomd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) ) )' % (An, AN, IXN, T, T, AN, IXN))
s3 = w.s([w.s([w.s([s3c, s3d], 'eqtrd', '( %s -> sum_ u e. %s %s = ( %s x. ( %s x. %s ) ) )' % (An, CRN, G, AN, IXN, T)), s3e], 'eqtrd', '( %s -> sum_ u e. %s %s = ( ( %s x. %s ) x. %s ) )' % (An, CRN, G, AN, IXN, T)), s3f], 'eqtrd', '( %s -> sum_ u e. %s %s = ( %s x. ( %s x. %s ) ) )' % (An, CRN, G, T, AN, IXN))
t3 = w.s([s3], 'sumeq2dv', '( %s -> sum_ n e. W sum_ u e. %s %s = sum_ n e. W ( %s x. ( %s x. %s ) ) )' % (A0, CRN, G, T, AN, IXN))
# step 4
bcl5 = w.s([an3, ixn], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (An, AN, IXN))
t4 = w.s([wfin, tcl, bcl5], 'fsummulc2', '( %s -> %s = sum_ n e. W ( %s x. ( %s x. %s ) ) )' % (A0, RHS, T, AN, IXN))
w.qed([w.s([w.s([t1, t2], 'eqtrd', '( %s -> %s = sum_ n e. W sum_ u e. %s %s )' % (A0, LHS, CRN, G)), t3], 'eqtrd', '( %s -> %s = sum_ n e. W ( %s x. ( %s x. %s ) ) )' % (A0, LHS, T, AN, IXN)), t4], 'eqtr4d', '( %s -> %s = %s )' % (A0, LHS, RHS)); run(w)
