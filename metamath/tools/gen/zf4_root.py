"""Sortie ZF4, batch 2: the root of unity ( -u 1 ^c ( 2 / N ) ) as the
additive character: modulus, periodicity, conjugate, and the orthogonality
sum (Mathlib AddChar.sum_mulShift for ZMod.stdAddChar) as a geometric sum."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from zf4lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

RN = R('N'); I = '( _i x. _pi )'; Q = '( ( 2 / N ) x. %s )' % I

def rcl(w, ante, nstep):
    """R e. CC and R =/= 0 under ante from nstep: ( ante -> N e. NN )"""
    cl = w.s([nstep, w.inst('root1cl')], 'syl', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (ante, RN, RN))
    return w.s([cl], 'simpld', '( %s -> %s e. CC )' % (ante, RN)), w.s([cl], 'simprd', '( %s -> %s =/= 0 )' % (ante, RN))

# ---- root1ef
w = W('root1ef', 'The root of unity as an exponential.')
A0 = 'N e. NN'
n = w.s([], 'id', '( N e. NN -> N e. NN )')
ncn = w.s([n], 'nncnd', '( %s -> N e. CC )' % A0); nne = w.s([n], 'nnne0d', '( %s -> N =/= 0 )' % A0)
two = w.s([], '2cnd', '( %s -> 2 e. CC )' % A0)
q = w.s([two, ncn, nne], 'divcld', '( %s -> ( 2 / N ) e. CC )' % A0)
m1 = w.s([w.s([], 'neg1cn', '-u 1 e. CC')], 'a1i', '( %s -> -u 1 e. CC )' % A0)
m1n = w.s([w.s([], 'neg1ne0', '-u 1 =/= 0')], 'a1i', '( %s -> -u 1 =/= 0 )' % A0)
r1 = w.s([m1, m1n, q, w.inst('cxpef')], 'syl3anc', '( %s -> %s = ( exp ` ( ( 2 / N ) x. ( log ` -u 1 ) ) ) )' % (A0, RN))
lg = w.s([w.s([w.s([], 'logm1', '( log ` -u 1 ) = %s' % I)], 'a1i', '( %s -> ( log ` -u 1 ) = %s )' % (A0, I))], 'oveq2d', '( %s -> ( ( 2 / N ) x. ( log ` -u 1 ) ) = %s )' % (A0, Q))
w.qed([r1, w.s([lg], 'fveq2d', '( %s -> ( exp ` ( ( 2 / N ) x. ( log ` -u 1 ) ) ) = ( exp ` %s ) )' % (A0, Q))], 'eqtrd', '( %s -> %s = ( exp ` %s ) )' % (A0, RN, Q)); run(w)

# ---- root1abs
A0 = '( N e. NN /\\ K e. ZZ )'
Y = '( ( 2 / N ) x. _pi )'
w = W('root1abs', 'Integer powers of the root of unity have modulus 1 (Mathlib ZMod.stdAddChar has values on the unit circle).')
n = w.s([], 'simpl', '( %s -> N e. NN )' % A0); k = w.s([], 'simpr', '( %s -> K e. ZZ )' % A0)
rc, rn = rcl(w, A0, n)
ef = w.s([n, w.inst('root1ef')], 'syl', '( %s -> %s = ( exp ` %s ) )' % (A0, RN, Q))
q = w.s([w.s([], '2re', '2 e. RR'), w.s([n], 'nnred', '( %s -> N e. RR )' % A0), w.s([n], 'nnne0d', '( %s -> N =/= 0 )' % A0)], '', '( %s -> ( 2 / N ) e. RR )' % A0)
w.lines.pop()
q = w.s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), w.s([n], 'nnred', '( %s -> N e. RR )' % A0), w.s([n], 'nnne0d', '( %s -> N =/= 0 )' % A0)], 'redivcld', '( %s -> ( 2 / N ) e. RR )' % A0)
yr = w.s([q, w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A0)], 'remulcld', '( %s -> %s e. RR )' % (A0, Y))
c12 = w.s([w.s([q], 'recnd', '( %s -> ( 2 / N ) e. CC )' % A0), w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), w.s([w.s([], 'picn', '_pi e. CC')], 'a1i', '( %s -> _pi e. CC )' % A0)], 'mul12d', '( %s -> %s = ( _i x. %s ) )' % (A0, Q, Y))
ef2 = w.s([ef, w.s([c12], 'fveq2d', '( %s -> ( exp ` %s ) = ( exp ` ( _i x. %s ) ) )' % (A0, Q, Y))], 'eqtrd', '( %s -> %s = ( exp ` ( _i x. %s ) ) )' % (A0, RN, Y))
ab1 = w.s([w.s([ef2], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` ( exp ` ( _i x. %s ) ) ) )' % (A0, RN, Y)), w.s([yr, w.inst('absefi')], 'syl', '( %s -> ( abs ` ( exp ` ( _i x. %s ) ) ) = 1 )' % (A0, Y))], 'eqtrd', '( %s -> ( abs ` %s ) = 1 )' % (A0, RN))
ae = w.s([rc, rn, k, w.inst('absexpz')], 'syl3anc', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) ^ K ) )' % (A0, RP('K'), RN))
w.qed([ae, w.s([w.s([ab1], 'oveq1d', '( %s -> ( ( abs ` %s ) ^ K ) = ( 1 ^ K ) )' % (A0, RN)), w.s([k, w.inst('1exp')], 'syl', '( %s -> ( 1 ^ K ) = 1 )' % A0)], 'eqtrd', '( %s -> ( ( abs ` %s ) ^ K ) = 1 )' % (A0, RN))], 'eqtrd', '( %s -> ( abs ` %s ) = 1 )' % (A0, RP('K'))); run(w)

# ---- root1dvds
A0 = '( N e. NN /\\ A e. ZZ /\\ B e. ZZ )'
w = W('root1dvds', 'The powers of the root of unity depend only on the exponent mod N.')
n = w.s([], 'simp1', '( %s -> N e. NN )' % A0); a = w.s([], 'simp2', '( %s -> A e. ZZ )' % A0); b = w.s([], 'simp3', '( %s -> B e. ZZ )' % A0)
rc, rn = rcl(w, A0, n)
sub = w.s([rc, rn, b, a], 'expsubd', '( %s -> %s = ( %s / %s ) )' % (A0, RP('( A - B )'), RP('A'), RP('B')))
eq = w.s([n, w.s([a, b], 'zsubcld', '( %s -> ( A - B ) e. ZZ )' % A0), w.inst('root1eq1')], 'syl2anc', '( %s -> ( %s = 1 <-> N || ( A - B ) ) )' % (A0, RP('( A - B )')))
d1 = w.s([rc, rn, a], 'expclzd', '( %s -> %s e. CC )' % (A0, RP('A'))); d2 = w.s([rc, rn, b], 'expclzd', '( %s -> %s e. CC )' % (A0, RP('B')))
d2n = w.s([rc, rn, b], 'expne0d', '( %s -> %s =/= 0 )' % (A0, RP('B')))
dq = w.s([d1, d2, d2n, w.inst('diveq1')], 'syl3anc', '( %s -> ( ( %s / %s ) = 1 <-> %s = %s ) )' % (A0, RP('A'), RP('B'), RP('A'), RP('B')))
e1 = w.s([w.s([sub], 'eqeq1d', '( %s -> ( %s = 1 <-> ( %s / %s ) = 1 ) )' % (A0, RP('( A - B )'), RP('A'), RP('B'))), dq], 'bitrd', '( %s -> ( %s = 1 <-> %s = %s ) )' % (A0, RP('( A - B )'), RP('A'), RP('B')))
w.qed([w.s([eq, e1], 'bitr3d', '( %s -> ( N || ( A - B ) <-> %s = %s ) )' % (A0, RP('A'), RP('B')))], 'biimpd', '( %s -> ( N || ( A - B ) -> %s = %s ) )' % (A0, RP('A'), RP('B'))); run(w)

# ---- root1mod
A0 = '( N e. NN /\\ A e. ZZ )'
AM = '( A mod N )'
w = W('root1mod', 'The power of the root of unity at the residue of A equals the power at A.')
n = w.s([], 'simpl', '( %s -> N e. NN )' % A0); a = w.s([], 'simpr', '( %s -> A e. ZZ )' % A0)
mz = w.s([w.s([a, n, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, AM))], 'nn0zd', '( %s -> %s e. ZZ )' % (A0, AM))
ab = w.s([w.s([a], 'zred', '( %s -> A e. RR )' % A0), w.s([n], 'nnrpd', '( %s -> N e. RR+ )' % A0), w.inst('modabs2')], 'syl2anc', '( %s -> ( %s mod N ) = %s )' % (A0, AM, AM))
md = w.s([n, mz, a, w.inst('moddvds')], 'syl3anc', '( %s -> ( ( %s mod N ) = ( A mod N ) <-> N || ( %s - A ) ) )' % (A0, AM, AM))
dv = w.s([ab, md], 'mpbid', '( %s -> N || ( %s - A ) )' % (A0, AM))
w.qed([dv, w.s([n, mz, a, w.inst('root1dvds')], 'syl3anc', '( %s -> ( N || ( %s - A ) -> %s = %s ) )' % (A0, AM, RP(AM), RP('A')))], 'mpd', '( %s -> %s = %s )' % (A0, RP(AM), RP('A'))); run(w)

# ---- root1cjz
A0 = '( N e. NN /\\ K e. ZZ )'
w = W('root1cjz', 'The conjugate of a power of the root of unity is the power at the negated exponent (Mathlib AddChar.map_neg_eq_conj).')
n = w.s([], 'simpl', '( %s -> N e. NN )' % A0); k = w.s([], 'simpr', '( %s -> K e. ZZ )' % A0)
cj = w.s([n, k, w.inst('root1cj')], 'syl2anc', '( %s -> ( * ` %s ) = %s )' % (A0, RP('K'), RP('( N - K )')))
ncn = w.s([n], 'nncnd', '( %s -> N e. CC )' % A0); kcn = w.s([k], 'zcnd', '( %s -> K e. CC )' % A0)
s1 = w.s([w.s([ncn, kcn], 'subcld', '( %s -> ( N - K ) e. CC )' % A0), kcn], 'subnegd', '( %s -> ( ( N - K ) - -u K ) = ( ( N - K ) + K ) )' % A0)
s2 = w.s([s1, w.s([ncn, kcn], 'npcand', '( %s -> ( ( N - K ) + K ) = N )' % A0)], 'eqtrd', '( %s -> ( ( N - K ) - -u K ) = N )' % A0)
dv = w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A0), w.inst('iddvds')], 'syl', '( %s -> N || N )' % A0)
dv2 = w.s([dv, w.s([s2], 'eqcomd', '( %s -> N = ( ( N - K ) - -u K ) )' % A0)], 'eqbrtrd' if False else 'breqtrd', '( %s -> N || ( ( N - K ) - -u K ) )' % A0)
imp = w.s([n, w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A0), k], 'zsubcld', '( %s -> ( N - K ) e. ZZ )' % A0), w.s([k], 'znegcld', '( %s -> -u K e. ZZ )' % A0), w.inst('root1dvds')], 'syl3anc', '( %s -> ( N || ( ( N - K ) - -u K ) -> %s = %s ) )' % (A0, RP('( N - K )'), RP('-u K')))
w.qed([cj, w.s([dv2, imp], 'mpd', '( %s -> %s = %s )' % (A0, RP('( N - K )'), RP('-u K')))], 'eqtrd', '( %s -> ( * ` %s ) = %s )' % (A0, RP('K'), RP('-u K'))); run(w)

# ---- root1sumlem1: ( R ^ ( a x. W ) ) = ( ( R ^ W ) ^ a ) summed
A0 = '( N e. NN /\\ W e. ZZ )'
Ak = '( %s /\\ a e. %s )' % (A0, FZO('N'))
S1 = 'sum_ a e. %s %s' % (FZO('N'), RP('( a x. W )')); S2 = 'sum_ a e. %s ( %s ^ a )' % (FZO('N'), RP('W'))
w = W('root1sumlem1', 'Lemma for root1sum: the orthogonality sum as a geometric sum.')
n = w.s([w.s([], 'simpl', '( %s -> N e. NN )' % A0)], 'adantr', '( %s -> N e. NN )' % Ak)
wz = w.s([w.s([], 'simpr', '( %s -> W e. ZZ )' % A0)], 'adantr', '( %s -> W e. ZZ )' % Ak)
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Ak, FZO('N'))), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Ak)
rc, rn = rcl(w, Ak, n)
c = w.s([w.s([az], 'zcnd', '( %s -> a e. CC )' % Ak), w.s([wz], 'zcnd', '( %s -> W e. CC )' % Ak)], 'mulcomd', '( %s -> ( a x. W ) = ( W x. a ) )' % Ak)
m = w.s([w.s([rc, rn], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (Ak, RN, RN)), w.s([wz, az], 'jca', '( %s -> ( W e. ZZ /\\ a e. ZZ ) )' % Ak), w.inst('expmulz')], 'syl2anc', '( %s -> %s = ( %s ^ a ) )' % (Ak, RP('( W x. a )'), RP('W')))
t = w.s([w.s([c], 'oveq2d', '( %s -> %s = %s )' % (Ak, RP('( a x. W )'), RP('( W x. a )'))), m], 'eqtrd', '( %s -> %s = ( %s ^ a ) )' % (Ak, RP('( a x. W )'), RP('W')))
w.qed([t], 'sumeq2dv', '( %s -> %s = %s )' % (A0, S1, S2)); run(w)

# ---- root1sumlem2: the non-divisible case
A1 = '( ( N e. NN /\\ W e. ZZ ) /\\ -. N || W )'
RW = RP('W')
w = W('root1sumlem2', 'Lemma for root1sum: when N does not divide W the geometric sum vanishes (geoserg).')
n = w.s([], 'simpll', '( %s -> N e. NN )' % A1); wz = w.s([], 'simplr', '( %s -> W e. ZZ )' % A1); nd = w.s([], 'simpr', '( %s -> -. N || W )' % A1)
rc, rn = rcl(w, A1, n)
rwc = w.s([rc, rn, wz], 'expclzd', '( %s -> %s e. CC )' % (A1, RW))
ne1 = w.s([nd, w.s([n, wz, w.inst('root1eq1')], 'syl2anc', '( %s -> ( %s = 1 <-> N || W ) )' % (A1, RW))], 'mtbird', '( %s -> -. %s = 1 )' % (A1, RW))
ne1b = w.s([ne1], 'neqned', '( %s -> %s =/= 1 )' % (A1, RW))
z0 = w.s([], '0nn0', '0 e. NN0'); z0d = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % A1)
uz = w.s([w.s([w.s([n], 'nnnn0d', '( %s -> N e. NN0 )' % A1), w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '( %s -> N e. ( ZZ>= ` 0 ) )' % A1)], 'idi' if False else 'id', '( %s -> N e. ( ZZ>= ` 0 ) )' % A1)
w.lines.pop()
uz = w.s([w.s([n], 'nnnn0d', '( %s -> N e. NN0 )' % A1), w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '( %s -> N e. ( ZZ>= ` 0 ) )' % A1)
geo = w.s([rwc, ne1b, z0d, uz], 'geoserg', '( %s -> sum_ a e. %s ( %s ^ a ) = ( ( ( %s ^ 0 ) - ( %s ^ N ) ) / ( 1 - %s ) ) )' % (A1, FZO('N'), RW, RW, RW, RW))
e0 = w.s([rwc], 'exp0d', '( %s -> ( %s ^ 0 ) = 1 )' % (A1, RW))
# ( ( R ^ W ) ^ N ) = R ^ ( W x. N ) = R ^ ( N x. W ) = ( R ^ N ) ^ W = 1 ^ W = 1
m1 = w.s([w.s([rc, rn], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (A1, RN, RN)), w.s([wz, w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A1)], 'jca', '( %s -> ( W e. ZZ /\\ N e. ZZ ) )' % A1), w.inst('expmulz')], 'syl2anc', '( %s -> %s = ( %s ^ N ) )' % (A1, RP('( W x. N )'), RW))
cm = w.s([w.s([wz], 'zcnd', '( %s -> W e. CC )' % A1), w.s([n], 'nncnd', '( %s -> N e. CC )' % A1)], 'mulcomd', '( %s -> ( W x. N ) = ( N x. W ) )' % A1)
m2 = w.s([w.s([rc, rn], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (A1, RN, RN)), w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A1), wz], 'jca', '( %s -> ( N e. ZZ /\\ W e. ZZ ) )' % A1), w.inst('expmulz')], 'syl2anc', '( %s -> %s = ( %s ^ W ) )' % (A1, RP('( N x. W )'), RP('N')))
r1 = w.s([n, w.inst('root1id')], 'syl', '( %s -> %s = 1 )' % (A1, RP('N')))
m3 = w.s([w.s([r1], 'oveq1d', '( %s -> ( %s ^ W ) = ( 1 ^ W ) )' % (A1, RP('N'))), w.s([wz, w.inst('1exp')], 'syl', '( %s -> ( 1 ^ W ) = 1 )' % A1)], 'eqtrd', '( %s -> ( %s ^ W ) = 1 )' % (A1, RP('N')))
eN = w.s([w.s([m1], 'eqcomd', '( %s -> ( %s ^ N ) = %s )' % (A1, RW, RP('( W x. N )'))), w.s([w.s([w.s([cm], 'oveq2d', '( %s -> %s = %s )' % (A1, RP('( W x. N )'), RP('( N x. W )'))), m2], 'eqtrd', '( %s -> %s = ( %s ^ W ) )' % (A1, RP('( W x. N )'), RP('N'))), m3], 'eqtrd', '( %s -> %s = 1 )' % (A1, RP('( W x. N )')))], 'eqtrd', '( %s -> ( %s ^ N ) = 1 )' % (A1, RW))
num = w.s([w.s([e0, eN], 'oveq12d', '( %s -> ( ( %s ^ 0 ) - ( %s ^ N ) ) = ( 1 - 1 ) )' % (A1, RW, RW)), w.s([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'a1i', '( %s -> ( 1 - 1 ) = 0 )' % A1)], 'eqtrd', '( %s -> ( ( %s ^ 0 ) - ( %s ^ N ) ) = 0 )' % (A1, RW, RW))
den = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), rwc, w.s([ne1b], 'necomd', '( %s -> 1 =/= %s )' % (A1, RW))], 'subne0d', '( %s -> ( 1 - %s ) =/= 0 )' % (A1, RW))
dencl = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), rwc], 'subcld', '( %s -> ( 1 - %s ) e. CC )' % (A1, RW))
q0 = w.s([w.s([num], 'oveq1d', '( %s -> ( ( ( %s ^ 0 ) - ( %s ^ N ) ) / ( 1 - %s ) ) = ( 0 / ( 1 - %s ) ) )' % (A1, RW, RW, RW, RW)), w.s([dencl, den], 'div0d', '( %s -> ( 0 / ( 1 - %s ) ) = 0 )' % (A1, RW))], 'eqtrd', '( %s -> ( ( ( %s ^ 0 ) - ( %s ^ N ) ) / ( 1 - %s ) ) = 0 )' % (A1, RW, RW, RW))
w.qed([geo, q0], 'eqtrd', '( %s -> sum_ a e. %s ( %s ^ a ) = 0 )' % (A1, FZO('N'), RW)); run(w)

# ---- root1sum
A0 = '( N e. NN /\\ W e. ZZ )'
A1 = '( %s /\\ N || W )' % A0; A2 = '( %s /\\ -. N || W )' % A0
Ak1 = '( %s /\\ a e. %s )' % (A1, FZO('N'))
IF = 'if ( N || W , N , 0 )'
w = W('root1sum', 'Orthogonality of the additive character (Mathlib AddChar.sum_mulShift with ZMod.isPrimitive_stdAddChar): the sum over the residues a of the ( a x. W )-th power of the root of unity is N when N divides W and 0 otherwise.')
l1 = w.s([], 'root1sumlem1', '( %s -> %s = %s )' % (A0, S1, S2))
# case N || W
n1 = w.s([], 'simpll', '( %s -> N e. NN )' % A1); w1 = w.s([], 'simplr', '( %s -> W e. ZZ )' % A1); d1 = w.s([], 'simpr', '( %s -> N || W )' % A1)
eq1 = w.s([d1, w.s([n1, w1, w.inst('root1eq1')], 'syl2anc', '( %s -> ( %s = 1 <-> N || W ) )' % (A1, RW))], 'mpbird', '( %s -> %s = 1 )' % (A1, RW))
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Ak1, FZO('N'))), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Ak1)
t1 = w.s([w.s([w.s([eq1], 'adantr', '( %s -> %s = 1 )' % (Ak1, RW))], 'oveq1d', '( %s -> ( %s ^ a ) = ( 1 ^ a ) )' % (Ak1, RW)), w.s([az, w.inst('1exp')], 'syl', '( %s -> ( 1 ^ a ) = 1 )' % Ak1)], 'eqtrd', '( %s -> ( %s ^ a ) = 1 )' % (Ak1, RW))
s1 = w.s([t1], 'sumeq2dv', '( %s -> %s = sum_ a e. %s 1 )' % (A1, S2, FZO('N')))
fc = w.s([w.s([w.s([], 'fzofi', '%s e. Fin' % FZO('N'))], 'a1i', '( %s -> %s e. Fin )' % (A1, FZO('N'))), w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), w.inst('fsumconst')], 'syl2anc', '( %s -> sum_ a e. %s 1 = ( ( # ` %s ) x. 1 ) )' % (A1, FZO('N'), FZO('N')))
h = w.s([w.s([w.s([n1], 'nnnn0d', '( %s -> N e. NN0 )' % A1), w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = N )' % (A1, FZO('N')))], 'oveq1d', '( %s -> ( ( # ` %s ) x. 1 ) = ( N x. 1 ) )' % (A1, FZO('N')))
n1e = w.s([w.s([n1], 'nncnd', '( %s -> N e. CC )' % A1)], 'mulridd', '( %s -> ( N x. 1 ) = N )' % A1)
c1 = w.s([w.s([w.s([w.s([l1], 'adantr', '( %s -> %s = %s )' % (A1, S1, S2)), s1], 'eqtrd', '( %s -> %s = sum_ a e. %s 1 )' % (A1, S1, FZO('N'))), fc], 'eqtrd', '( %s -> %s = ( ( # ` %s ) x. 1 ) )' % (A1, S1, FZO('N'))), w.s([h, n1e], 'eqtrd', '( %s -> ( ( # ` %s ) x. 1 ) = N )' % (A1, FZO('N')))], 'eqtrd', '( %s -> %s = N )' % (A1, S1))
if1 = w.s([d1], 'iftrued', '( %s -> %s = N )' % (A1, IF))
case1 = w.s([c1, if1], 'eqtr4d', '( %s -> %s = %s )' % (A1, S1, IF))
# case -. N || W
c2 = w.s([w.s([l1], 'adantr', '( %s -> %s = %s )' % (A2, S1, S2)), w.s([], 'root1sumlem2', '( %s -> %s = 0 )' % (A2, S2))], 'eqtrd', '( %s -> %s = 0 )' % (A2, S1))
if2 = w.s([w.s([], 'simpr', '( %s -> -. N || W )' % A2)], 'iffalsed', '( %s -> %s = 0 )' % (A2, IF))
case2 = w.s([c2, if2], 'eqtr4d', '( %s -> %s = %s )' % (A2, S1, IF))
w.qed([case1, case2], 'pm2.61dan', '( %s -> %s = %s )' % (A0, S1, IF)); run(w)

# ---- dchrgsorth: the exp form
Ak = '( %s /\\ a e. %s )' % (A0, FZO('N'))
SE = 'sum_ a e. %s %s' % (FZO('N'), E('( a x. W )'))
w = W('dchrgsorth', 'Orthogonality of the additive character in the exponential form (Lean AddChar.sum_mulShift for ZMod.stdAddChar; LConvexity, LargeSieve): sum over a of exp ( 2 _pi _i a W / N ).')
n = w.s([w.s([], 'simpl', '( %s -> N e. NN )' % A0)], 'adantr', '( %s -> N e. NN )' % Ak)
wz = w.s([w.s([], 'simpr', '( %s -> W e. ZZ )' % A0)], 'adantr', '( %s -> W e. ZZ )' % Ak)
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Ak, FZO('N'))), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Ak)
ef = w.s([n, w.s([az, wz], 'zmulcld', '( %s -> ( a x. W ) e. ZZ )' % Ak), w.inst('dchrgsef')], 'syl2anc', '( %s -> %s = %s )' % (Ak, E('( a x. W )'), RP('( a x. W )')))
w.qed([w.s([ef], 'sumeq2dv', '( %s -> %s = %s )' % (A0, SE, S1)), w.s([], 'root1sum', '( %s -> %s = %s )' % (A0, S1, IF))], 'eqtrd', '( %s -> %s = %s )' % (A0, SE, IF)); run(w)

# ---- fzocongeq0
A0 = '( N e. NN /\\ B e. %s /\\ C e. %s )' % (FZO('N'), FZO('N'))
w = W('fzocongeq0', 'Two residues in ( 0 ..^ N ) are congruent mod N only if they are equal (fzocongeq at 0).')
c = w.s([w.s([], 'simp2', '( %s -> B e. %s )' % (A0, FZO('N'))), w.s([], 'simp3', '( %s -> C e. %s )' % (A0, FZO('N'))), w.inst('fzocongeq')], 'syl2anc', '( %s -> ( ( N - 0 ) || ( B - C ) <-> B = C ) )' % A0)
s = w.s([w.s([w.s([], 'simp1', '( %s -> N e. NN )' % A0)], 'nncnd', '( %s -> N e. CC )' % A0)], 'subid1d', '( %s -> ( N - 0 ) = N )' % A0)
w.qed([w.s([s], 'breq1d', '( %s -> ( ( N - 0 ) || ( B - C ) <-> N || ( B - C ) ) )' % A0), c], 'bitr3d', '( %s -> ( N || ( B - C ) <-> B = C ) )' % A0); run(w)
