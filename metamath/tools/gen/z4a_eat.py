"""Sortie Z4a, batch 1: the exponential e ( nu beta ) (LargeSieve eAt, eAt_add,
norm_eAt, norm_eAt_center), the unit-sum restriction (sum_units_eq) and the
conjugate of a character value (MeanValue conj_char_eq_inv)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from z4alib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

C2 = '( 2 x. ( _i x. _pi ) )'
def c2cl(w, ante):
    ip = w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')
    c = w.s([w.s([], '2cn', '2 e. CC'), ip], 'mulcli', '%s e. CC' % C2)
    return w.s([c], 'a1i', '( %s -> %s e. CC )' % (ante, C2))

# ---- eatcl
A0 = '( V e. CC /\\ B e. CC )'
w = W('eatcl', 'Closure of the exponential e ( nu beta ) = exp ( 2 pi i nu beta ) (LargeSieve eAt).')
v = w.s([], 'simpl', '( %s -> V e. CC )' % A0); b = w.s([], 'simpr', '( %s -> B e. CC )' % A0)
c2 = c2cl(w, A0)
vb = w.s([v, b], 'mulcld', '( %s -> ( V x. B ) e. CC )' % A0)
w.qed([w.s([c2, vb], 'mulcld', '( %s -> ( %s x. ( V x. B ) ) e. CC )' % (A0, C2))], 'efcld', '( %s -> %s e. CC )' % (A0, EAT('V', 'B'))); run(w)

# ---- eatadd
A0 = '( M e. CC /\\ K e. CC /\\ B e. CC )'
MB = '( M x. B )'; KB = '( K x. B )'
w = W('eatadd', 'The exponential e ( nu beta ) is additive in the frequency (LargeSieve eAt_add).')
m = w.s([], 'simp1', '( %s -> M e. CC )' % A0); k = w.s([], 'simp2', '( %s -> K e. CC )' % A0); b = w.s([], 'simp3', '( %s -> B e. CC )' % A0)
c2 = c2cl(w, A0)
d1 = w.s([m, k, b], 'adddird', '( %s -> ( ( M + K ) x. B ) = ( %s + %s ) )' % (A0, MB, KB))
d2 = w.s([d1], 'oveq2d', '( %s -> ( %s x. ( ( M + K ) x. B ) ) = ( %s x. ( %s + %s ) ) )' % (A0, C2, C2, MB, KB))
mb = w.s([m, b], 'mulcld', '( %s -> %s e. CC )' % (A0, MB)); kb = w.s([k, b], 'mulcld', '( %s -> %s e. CC )' % (A0, KB))
P = '( %s x. %s )' % (C2, MB); Q = '( %s x. %s )' % (C2, KB)
d3 = w.s([c2, mb, kb], 'adddid', '( %s -> ( %s x. ( %s + %s ) ) = ( %s + %s ) )' % (A0, C2, MB, KB, P, Q))
d5 = w.s([w.s([d2, d3], 'eqtrd', '( %s -> ( %s x. ( ( M + K ) x. B ) ) = ( %s + %s ) )' % (A0, C2, P, Q))], 'fveq2d', '( %s -> %s = ( exp ` ( %s + %s ) ) )' % (A0, EAT('( M + K )', 'B'), P, Q))
d6 = w.s([w.s([c2, mb], 'mulcld', '( %s -> %s e. CC )' % (A0, P)), w.s([c2, kb], 'mulcld', '( %s -> %s e. CC )' % (A0, Q)), w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (A0, P, Q, P, Q))
w.qed([d5, d6], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (A0, EAT('( M + K )', 'B'), EAT('M', 'B'), EAT('K', 'B'))); run(w)

# ---- eatabs
A0 = '( V e. RR /\\ B e. RR )'
TP = '( 2 x. _pi )'; VB = '( V x. B )'
w = W('eatabs', 'The exponential e ( nu beta ) has modulus 1 for real nu, beta (LargeSieve norm_eAt).')
v = w.s([], 'simpl', '( %s -> V e. RR )' % A0); b = w.s([], 'simpr', '( %s -> B e. RR )' % A0)
vc = w.s([v], 'recnd', '( %s -> V e. CC )' % A0); bc = w.s([b], 'recnd', '( %s -> B e. CC )' % A0)
c2c = w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0); ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0); pc = w.s([w.s([], 'picn', '_pi e. CC')], 'a1i', '( %s -> _pi e. CC )' % A0)
vb = w.s([vc, bc], 'mulcld', '( %s -> %s e. CC )' % (A0, VB)); vbr = w.s([v, b], 'remulcld', '( %s -> %s e. RR )' % (A0, VB))
e1 = w.s([c2c, ic, pc], 'mul12d', '( %s -> %s = ( _i x. %s ) )' % (A0, C2, TP))
e2 = w.s([e1], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( _i x. %s ) x. %s ) )' % (A0, C2, VB, TP, VB))
tpc = w.s([c2c, pc], 'mulcld', '( %s -> %s e. CC )' % (A0, TP))
e3 = w.s([ic, tpc, vb], 'mulassd', '( %s -> ( ( _i x. %s ) x. %s ) = ( _i x. ( %s x. %s ) ) )' % (A0, TP, VB, TP, VB))
e4 = w.s([e2, e3], 'eqtrd', '( %s -> ( %s x. %s ) = ( _i x. ( %s x. %s ) ) )' % (A0, C2, VB, TP, VB))
e6 = w.s([w.s([e4], 'fveq2d', '( %s -> %s = ( exp ` ( _i x. ( %s x. %s ) ) ) )' % (A0, EAT('V', 'B'), TP, VB))], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( exp ` ( _i x. ( %s x. %s ) ) ) ) )' % (A0, EAT('V', 'B'), TP, VB))
tpr = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], 'pire', '_pi e. RR')], 'remulcli', '%s e. RR' % TP)], 'a1i', '( %s -> %s e. RR )' % (A0, TP))
e7 = w.s([w.s([tpr, vbr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, TP, VB)), w.inst('absefi')], 'syl', '( %s -> ( abs ` ( exp ` ( _i x. ( %s x. %s ) ) ) ) = 1 )' % (A0, TP, VB))
w.qed([e6, e7], 'eqtrd', '( %s -> ( abs ` %s ) = 1 )' % (A0, EAT('V', 'B'))); run(w)

# ---- eatcenter
A0 = '( %s /\\ M e. RR /\\ B e. RR )' % HW
An = '( %s /\\ n e. W )' % A0
EM = EAT('M', 'B'); ENM = EAT('( n - M )', 'B'); EN = EAT('n', 'B')
S0 = ESUM('n', 'B'); S1 = ESUM('( n - M )', 'B')
w = W('eatcenter', 'Recentring the frequencies of a window sum by a real shift does not change its modulus (LargeSieve norm_eAt_center).')
hw = w.s([], 'simp1', '( %s -> %s )' % (A0, HW)); m = w.s([], 'simp2', '( %s -> M e. RR )' % A0); b = w.s([], 'simp3', '( %s -> B e. RR )' % A0)
wfin = w.s([hw], 'simp1d', '( %s -> W e. Fin )' % A0); wss = w.s([hw], 'simp2d', '( %s -> W C_ ZZ )' % A0); af = w.s([hw], 'simp3d', '( %s -> A : W --> CC )' % A0)
mc0 = w.s([m], 'recnd', '( %s -> M e. CC )' % A0); bc0 = w.s([b], 'recnd', '( %s -> B e. CC )' % A0)
nW = w.s([], 'simpr', '( %s -> n e. W )' % An)
nz = w.s([w.s([wss], 'adantr', '( %s -> W C_ ZZ )' % An), nW, w.inst('ssel2')], 'syl2anc', '( %s -> n e. ZZ )' % An)
ncn = w.s([nz], 'zcnd', '( %s -> n e. CC )' % An)
an = w.s([w.s([af], 'adantr', '( %s -> A : W --> CC )' % An), nW], 'ffvelcdmd', '( %s -> ( A ` n ) e. CC )' % An)
mc = w.s([mc0], 'adantr', '( %s -> M e. CC )' % An); bc = w.s([bc0], 'adantr', '( %s -> B e. CC )' % An)
e0 = w.s([w.s([mc, ncn], 'pncan3d', '( %s -> ( M + ( n - M ) ) = n )' % An)], 'eqcomd', '( %s -> n = ( M + ( n - M ) ) )' % An)
e3 = w.s([w.s([w.s([e0], 'oveq1d', '( %s -> ( n x. B ) = ( ( M + ( n - M ) ) x. B ) )' % An)], 'oveq2d', '( %s -> ( %s x. ( n x. B ) ) = ( %s x. ( ( M + ( n - M ) ) x. B ) ) )' % (An, C2, C2))], 'fveq2d', '( %s -> %s = %s )' % (An, EN, EAT('( M + ( n - M ) )', 'B')))
nm = w.s([ncn, mc], 'subcld', '( %s -> ( n - M ) e. CC )' % An)
e4 = w.s([mc, nm, bc, w.inst('eatadd')], 'syl3anc', '( %s -> %s = ( %s x. %s ) )' % (An, EAT('( M + ( n - M ) )', 'B'), EM, ENM))
e6 = w.s([w.s([e3, e4], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (An, EN, EM, ENM))], 'oveq2d', '( %s -> ( ( A ` n ) x. %s ) = ( ( A ` n ) x. ( %s x. %s ) ) )' % (An, EN, EM, ENM))
em = w.s([mc, bc, w.inst('eatcl')], 'syl2anc', '( %s -> %s e. CC )' % (An, EM)); enm = w.s([nm, bc, w.inst('eatcl')], 'syl2anc', '( %s -> %s e. CC )' % (An, ENM))
e7 = w.s([an, em, enm], 'mul12d', '( %s -> ( ( A ` n ) x. ( %s x. %s ) ) = ( %s x. ( ( A ` n ) x. %s ) ) )' % (An, EM, ENM, EM, ENM))
s1 = w.s([w.s([e6, e7], 'eqtrd', '( %s -> ( ( A ` n ) x. %s ) = ( %s x. ( ( A ` n ) x. %s ) ) )' % (An, EN, EM, ENM))], 'sumeq2dv', '( %s -> %s = sum_ n e. W ( %s x. ( ( A ` n ) x. %s ) ) )' % (A0, S0, EM, ENM))
em0 = w.s([mc0, bc0, w.inst('eatcl')], 'syl2anc', '( %s -> %s e. CC )' % (A0, EM))
bcl = w.s([an, enm], 'mulcld', '( %s -> ( ( A ` n ) x. %s ) e. CC )' % (An, ENM))
s2 = w.s([wfin, em0, bcl], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ n e. W ( %s x. ( ( A ` n ) x. %s ) ) )' % (A0, EM, S1, EM, ENM))
s4 = w.s([w.s([s1, s2], 'eqtr4d', '( %s -> %s = ( %s x. %s ) )' % (A0, S0, EM, S1))], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( %s x. %s ) ) )' % (A0, S0, EM, S1))
scl = w.s([wfin, bcl], 'fsumcl', '( %s -> %s e. CC )' % (A0, S1))
s5 = w.s([em0, scl], 'absmuld', '( %s -> ( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (A0, EM, S1, EM, S1))
s7 = w.s([w.s([m, b, w.inst('eatabs')], 'syl2anc', '( %s -> ( abs ` %s ) = 1 )' % (A0, EM))], 'oveq1d', '( %s -> ( ( abs ` %s ) x. ( abs ` %s ) ) = ( 1 x. ( abs ` %s ) ) )' % (A0, EM, S1, S1))
s8 = w.s([w.s([scl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, S1))], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (A0, S1))
s9 = w.s([s8], 'mullidd', '( %s -> ( 1 x. ( abs ` %s ) ) = ( abs ` %s ) )' % (A0, S1, S1))
w.qed([w.s([w.s([s4, s5], 'eqtrd', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (A0, S0, EM, S1)), s7], 'eqtrd', '( %s -> ( abs ` %s ) = ( 1 x. ( abs ` %s ) ) )' % (A0, S0, S1)), s9], 'eqtrd', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (A0, S0, S1)); run(w)

# ---- dchrsumcr ($e hypotheses)
F0 = FZO('N'); CRN = CR('N'); DN = DB('N'); L = LZ('N')
XU = EV('X', 'N', 'u'); TERM = '( %s x. B )' % XU
w = W('dchrsumcr', 'A sum weighted by a Dirichlet character over the coprime residues equals the sum over all residues: the character vanishes off the units (LargeSieve sum_units_eq).')
h1 = hyp(w, 1, 'dchrsumcr.n', '( ph -> N e. NN )'); h2 = hyp(w, 2, 'dchrsumcr.x', '( ph -> X e. %s )' % DN); h3 = hyp(w, 3, 'dchrsumcr.b', '( ( ph /\\ u e. %s ) -> B e. CC )' % F0)
ss = w.s([w.s([], 'ssrab2', '%s C_ %s' % (CRN, F0))], 'a1i', '( ph -> %s C_ %s )' % (CRN, F0))
Au = '( ph /\\ u e. %s )' % CRN
ei = w.inst('elrabi')
uF0 = w.s([w.s([], 'simpr', '( %s -> u e. %s )' % (Au, CRN)), ei], 'syl', '( %s -> u e. %s )' % (Au, F0))
bcl = w.s([ei, h3], 'sylan2', '( %s -> B e. CC )' % Au)
uz = w.s([uF0, w.inst('elfzoelz')], 'syl', '( %s -> u e. ZZ )' % Au)
g, z, d, l = dchyp(w)
xcl = w.s([g, z, d, l, w.s([h2], 'adantr', '( %s -> X e. %s )' % (Au, DN)), uz], 'dchrzrhcl', '( %s -> %s e. CC )' % (Au, XU))
c2 = w.s([xcl, bcl], 'mulcld', '( %s -> %s e. CC )' % (Au, TERM))
Ad = '( ph /\\ u e. ( %s \\ %s ) )' % (F0, CRN)
ud = w.s([], 'simpr', '( %s -> u e. ( %s \\ %s ) )' % (Ad, F0, CRN))
uF = w.s([ud], 'eldifad', '( %s -> u e. %s )' % (Ad, F0)); un = w.s([ud], 'eldifbd', '( %s -> -. u e. %s )' % (Ad, CRN))
sub = w.s([w.s([], 'oveq1', '( k = u -> ( k gcd N ) = ( u gcd N ) )')], 'eqeq1d', '( k = u -> ( ( k gcd N ) = 1 <-> ( u gcd N ) = 1 ) )')
er = w.s([sub], 'elrab', '( u e. %s <-> ( u e. %s /\\ ( u gcd N ) = 1 ) )' % (CRN, F0))
era = w.s([er], 'a1i', '( %s -> ( u e. %s <-> ( u e. %s /\\ ( u gcd N ) = 1 ) ) )' % (Ad, CRN, F0))
bi = w.s([uF, era], 'mpbirand', '( %s -> ( u e. %s <-> ( u gcd N ) = 1 ) )' % (Ad, CRN))
ncop = w.s([un, bi], 'mtbid', '( %s -> -. ( u gcd N ) = 1 )' % Ad)
uz2 = w.s([uF, w.inst('elfzoelz')], 'syl', '( %s -> u e. ZZ )' % Ad)
hc = w.s([w.s([h1, h2], 'jca', '( ph -> %s )' % HC)], 'adantr', '( %s -> %s )' % (Ad, HC))
zero = w.s([hc, uz2, ncop, w.inst('dchrzrh0')], 'syl3anc', '( %s -> %s = 0 )' % (Ad, XU))
z2 = w.s([zero], 'oveq1d', '( %s -> %s = ( 0 x. B ) )' % (Ad, TERM))
bcl2 = w.s([w.inst('eldifi'), h3], 'sylan2', '( %s -> B e. CC )' % Ad)
z4 = w.s([z2, w.s([bcl2], 'mul02d', '( %s -> ( 0 x. B ) = 0 )' % Ad)], 'eqtrd', '( %s -> %s = 0 )' % (Ad, TERM))
fin = w.s([w.s([], 'fzofi', '%s e. Fin' % F0)], 'a1i', '( ph -> %s e. Fin )' % F0)
w.qed([ss, c2, z4, fin], 'fsumss', '( ph -> sum_ u e. %s %s = sum_ u e. %s %s )' % (CRN, TERM, F0, TERM)); run(w)

# ---- dchrcjinv
A0 = '( %s /\\ ( A e. ZZ /\\ B e. ZZ ) /\\ N || ( ( A x. B ) - 1 ) )' % HC
ZA = EV('X', 'N', 'A'); ZB = EV('X', 'N', 'B'); CZA = CJ(ZA); AB = '( A x. B )'
w = W('dchrcjinv', 'The conjugate of a Dirichlet character at a unit is its value at an inverse of the unit (MeanValue conj_char_eq_inv).')
hc = w.s([], 'simp1', '( %s -> %s )' % (A0, HC)); n = w.s([hc], 'simpld', '( %s -> N e. NN )' % A0); x = w.s([hc], 'simprd', '( %s -> X e. %s )' % (A0, DN))
ab = w.s([], 'simp2', '( %s -> ( A e. ZZ /\\ B e. ZZ ) )' % A0); a = w.s([ab], 'simpld', '( %s -> A e. ZZ )' % A0); b = w.s([ab], 'simprd', '( %s -> B e. ZZ )' % A0); dv = w.s([], 'simp3', '( %s -> N || ( %s - 1 ) )' % (A0, AB))
g, z, d, l = dchyp(w)
za = w.s([g, z, d, l, x, a], 'dchrzrhcl', '( %s -> %s e. CC )' % (A0, ZA)); zb = w.s([g, z, d, l, x, b], 'dchrzrhcl', '( %s -> %s e. CC )' % (A0, ZB))
p1 = w.s([g, z, d, l, x, a, b], 'dchrzrhmul', '( %s -> %s = ( %s x. %s ) )' % (A0, EV('X', 'N', AB), ZA, ZB))
abz = w.s([a, b], 'zmulcld', '( %s -> %s e. ZZ )' % (A0, AB)); one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0)
n0 = w.s([n], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
zd = w.s([z, l], 'zndvds', '( ( N e. NN0 /\\ %s e. ZZ /\\ 1 e. ZZ ) -> ( ( %s ` %s ) = ( %s ` 1 ) <-> N || ( %s - 1 ) ) )' % (AB, L, AB, L, AB))
leq = w.s([dv, w.s([n0, abz, one, zd], 'syl3anc', '( %s -> ( ( %s ` %s ) = ( %s ` 1 ) <-> N || ( %s - 1 ) ) )' % (A0, L, AB, L, AB))], 'mpbird', '( %s -> ( %s ` %s ) = ( %s ` 1 ) )' % (A0, L, AB, L))
p4 = w.s([w.s([leq], 'fveq2d', '( %s -> %s = ( X ` ( %s ` 1 ) ) )' % (A0, EV('X', 'N', AB), L)), w.s([g, z, d, l, x], 'dchrzrh1', '( %s -> ( X ` ( %s ` 1 ) ) = 1 )' % (A0, L))], 'eqtrd', '( %s -> %s = 1 )' % (A0, EV('X', 'N', AB)))
p5 = w.s([p1, p4], 'eqtr3d', '( %s -> ( %s x. %s ) = 1 )' % (A0, ZA, ZB))
ba = w.s([w.s([w.s([b], 'zcnd', '( %s -> B e. CC )' % A0), w.s([a], 'zcnd', '( %s -> A e. CC )' % A0)], 'mulcomd', '( %s -> ( B x. A ) = %s )' % (A0, AB))], 'oveq1d', '( %s -> ( ( B x. A ) - 1 ) = ( %s - 1 ) )' % (A0, AB))
dv2 = w.s([dv, ba], 'breqtrrd', '( %s -> N || ( ( B x. A ) - 1 ) )' % A0)
copa = w.s([n, w.s([b, a], 'jca', '( %s -> ( B e. ZZ /\\ A e. ZZ ) )' % A0), dv2, w.inst('dvdsinvcop')], 'syl3anc', '( %s -> ( A gcd N ) = 1 )' % A0)
zu = w.s([], 'eqid', '%s = %s' % (UZ('N'), UZ('N')))
un = w.s([z, zu, l], 'znunit', '( ( N e. NN0 /\\ A e. ZZ ) -> ( ( %s ` A ) e. %s <-> ( A gcd N ) = 1 ) )' % (L, UZ('N')))
lu = w.s([copa, w.s([n0, a, un], 'syl2anc', '( %s -> ( ( %s ` A ) e. %s <-> ( A gcd N ) = 1 ) )' % (A0, L, UZ('N')))], 'mpbird', '( %s -> ( %s ` A ) e. %s )' % (A0, L, UZ('N')))
ab1 = w.s([g, d, x, z, zu, lu], 'dchrabs', '( %s -> ( abs ` %s ) = 1 )' % (A0, ZA))
sq = w.s([za, w.inst('absvalsq')], 'syl', '( %s -> ( ( abs ` %s ) ^ 2 ) = ( %s x. %s ) )' % (A0, ZA, ZA, CZA))
one2 = w.s([w.s([ab1], 'oveq1d', '( %s -> ( ( abs ` %s ) ^ 2 ) = ( 1 ^ 2 ) )' % (A0, ZA)), w.s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( %s -> ( 1 ^ 2 ) = 1 )' % A0)], 'eqtrd', '( %s -> ( ( abs ` %s ) ^ 2 ) = 1 )' % (A0, ZA))
zcz1 = w.s([sq, one2], 'eqtr3d', '( %s -> ( %s x. %s ) = 1 )' % (A0, ZA, CZA))
cza = w.s([za], 'cjcld', '( %s -> %s e. CC )' % (A0, CZA))
e1 = w.s([w.s([cza], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A0, CZA, CZA))], 'eqcomd', '( %s -> %s = ( %s x. 1 ) )' % (A0, CZA, CZA))
e2 = w.s([w.s([p5], 'eqcomd', '( %s -> 1 = ( %s x. %s ) )' % (A0, ZA, ZB))], 'oveq2d', '( %s -> ( %s x. 1 ) = ( %s x. ( %s x. %s ) ) )' % (A0, CZA, CZA, ZA, ZB))
e3 = w.s([w.s([cza, za, zb], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) ) )' % (A0, CZA, ZA, ZB, CZA, ZA, ZB))], 'eqcomd', '( %s -> ( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s ) )' % (A0, CZA, ZA, ZB, CZA, ZA, ZB))
e4 = w.s([w.s([cza, za], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, CZA, ZA, ZA, CZA)), zcz1], 'eqtrd', '( %s -> ( %s x. %s ) = 1 )' % (A0, CZA, ZA))
e5 = w.s([e4], 'oveq1d', '( %s -> ( ( %s x. %s ) x. %s ) = ( 1 x. %s ) )' % (A0, CZA, ZA, ZB, ZB))
e6 = w.s([zb], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0, ZB, ZB))
c1 = w.s([e1, e2], 'eqtrd', '( %s -> %s = ( %s x. ( %s x. %s ) ) )' % (A0, CZA, CZA, ZA, ZB))
c2 = w.s([c1, e3], 'eqtrd', '( %s -> %s = ( ( %s x. %s ) x. %s ) )' % (A0, CZA, CZA, ZA, ZB))
c3 = w.s([c2, e5], 'eqtrd', '( %s -> %s = ( 1 x. %s ) )' % (A0, CZA, ZB))
w.qed([c3, e6], 'eqtrd', '( %s -> %s = %s )' % (A0, CZA, ZB)); run(w)
