"""Sortie ZF4, batch 3: reindexing a Gauss sum by a unit (Mathlib
gaussSum_mulShift) and the shift identity gaussSum_mulShift_eq."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
from zf4lib import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

RN = R('N'); F0 = FZO('N')
def rcl(w, ante, nstep):
    cl = w.s([nstep, w.inst('root1cl')], 'syl', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (ante, RN, RN))
    return w.s([cl], 'simpld', '( %s -> %s e. CC )' % (ante, RN)), w.s([cl], 'simprd', '( %s -> %s =/= 0 )' % (ante, RN))

# ---- zmoddvds
A0 = '( N e. NN /\\ A e. ZZ )'; AM = '( A mod N )'
w = W('zmoddvds', 'N divides the difference of an integer and its residue.')
n = w.s([], 'simpl', '( %s -> N e. NN )' % A0); a = w.s([], 'simpr', '( %s -> A e. ZZ )' % A0)
mz = w.s([w.s([a, n, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, AM))], 'nn0zd', '( %s -> %s e. ZZ )' % (A0, AM))
ab = w.s([w.s([a], 'zred', '( %s -> A e. RR )' % A0), w.s([n], 'nnrpd', '( %s -> N e. RR+ )' % A0), w.inst('modabs2')], 'syl2anc', '( %s -> ( %s mod N ) = %s )' % (A0, AM, AM))
md = w.s([n, mz, a, w.inst('moddvds')], 'syl3anc', '( %s -> ( ( %s mod N ) = ( A mod N ) <-> N || ( %s - A ) ) )' % (A0, AM, AM))
w.qed([ab, md], 'mpbid', '( %s -> N || ( %s - A ) )' % (A0, AM)); run(w)

# ---- dchrzrhmod
A0 = '( %s /\\ A e. ZZ )' % HC
w = W('dchrzrhmod', 'A Dirichlet character at the class of the residue of A is its value at the class of A.')
hc = w.s([], 'simpl', '( %s -> %s )' % (A0, HC)); n = w.s([hc], 'simpld', '( %s -> N e. NN )' % A0); a = w.s([], 'simpr', '( %s -> A e. ZZ )' % A0)
mz = w.s([w.s([a, n, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (A0, AM))], 'nn0zd', '( %s -> %s e. ZZ )' % (A0, AM))
dv = w.s([n, a, w.inst('zmoddvds')], 'syl2anc', '( %s -> N || ( %s - A ) )' % (A0, AM))
zd = w.s([w.s([n], 'nnnn0d', '( %s -> N e. NN0 )' % A0), mz, a, w.s([w.s([], 'eqid', '( Z/nZ ` N ) = ( Z/nZ ` N )'), w.s([], 'eqid', '%s = %s' % (LZ('N'), LZ('N')))], 'zndvds', '( ( N e. NN0 /\\ %s e. ZZ /\\ A e. ZZ ) -> ( ( %s ` %s ) = ( %s ` A ) <-> N || ( %s - A ) ) )' % (AM, LZ('N'), AM, LZ('N'), AM))], 'syl3anc', '( %s -> ( ( %s ` %s ) = ( %s ` A ) <-> N || ( %s - A ) ) )' % (A0, LZ('N'), AM, LZ('N'), AM))
w.qed([w.s([dv, zd], 'mpbird', '( %s -> ( %s ` %s ) = ( %s ` A ) )' % (A0, LZ('N'), AM, LZ('N')))], 'fveq2d', '( %s -> %s = %s )' % (A0, EV('X', 'N', AM), EV('X', 'N', 'A'))); run(w)

# ---- root1dvdsmul1, root1dvdsmul2
A0 = '( N e. NN /\\ ( A e. ZZ /\\ B e. ZZ /\\ C e. ZZ ) /\\ N || ( A - B ) )'
for lab, lhs1, lhs2, prod, dvl in (('root1dvdsmul1', '( A x. C )', '( B x. C )', '( ( A - B ) x. C )', 'dvdsmultr1'),
                                   ('root1dvdsmul2', '( C x. A )', '( C x. B )', '( C x. ( A - B ) )', 'dvdsmultr2')):
    w = W(lab, 'Powers of the root of unity at products of congruent exponents agree.')
    n = w.s([], 'simp1', '( %s -> N e. NN )' % A0); t = w.s([], 'simp2', '( %s -> ( A e. ZZ /\\ B e. ZZ /\\ C e. ZZ ) )' % A0); dv = w.s([], 'simp3', '( %s -> N || ( A - B ) )' % A0)
    a = w.s([t], 'simp1d', '( %s -> A e. ZZ )' % A0); b = w.s([t], 'simp2d', '( %s -> B e. ZZ )' % A0); c = w.s([t], 'simp3d', '( %s -> C e. ZZ )' % A0)
    ab = w.s([a, b], 'zsubcld', '( %s -> ( A - B ) e. ZZ )' % A0)
    if lab == 'root1dvdsmul1':
        d2 = w.s([w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A0), ab, c, w.inst(dvl)], 'syl3anc', '( %s -> ( N || ( A - B ) -> N || %s ) )' % (A0, prod)), dv], 'mpd' if False else 'mpd', '( %s -> N || %s )' % (A0, prod))
        w.lines.pop()
        d2 = w.s([dv, w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A0), ab, c, w.inst(dvl)], 'syl3anc', '( %s -> ( N || ( A - B ) -> N || %s ) )' % (A0, prod))], 'mpd', '( %s -> N || %s )' % (A0, prod))
        dist = w.s([w.s([a], 'zcnd', '( %s -> A e. CC )' % A0), w.s([b], 'zcnd', '( %s -> B e. CC )' % A0), w.s([c], 'zcnd', '( %s -> C e. CC )' % A0)], 'subdird', '( %s -> %s = ( %s - %s ) )' % (A0, prod, lhs1, lhs2))
    else:
        d2 = w.s([dv, w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A0), c, ab, w.inst(dvl)], 'syl3anc', '( %s -> ( N || ( A - B ) -> N || %s ) )' % (A0, prod))], 'mpd', '( %s -> N || %s )' % (A0, prod))
        dist = w.s([w.s([c], 'zcnd', '( %s -> C e. CC )' % A0), w.s([a], 'zcnd', '( %s -> A e. CC )' % A0), w.s([b], 'zcnd', '( %s -> B e. CC )' % A0)], 'subdid', '( %s -> %s = ( %s - %s ) )' % (A0, prod, lhs1, lhs2))
    d3 = w.s([d2, dist], 'breqtrd', '( %s -> N || ( %s - %s ) )' % (A0, lhs1, lhs2))
    z1 = w.s([a, c], 'zmulcld', '( %s -> %s e. ZZ )' % (A0, lhs1)) if lab == 'root1dvdsmul1' else w.s([c, a], 'zmulcld', '( %s -> %s e. ZZ )' % (A0, lhs1))
    z2 = w.s([b, c], 'zmulcld', '( %s -> %s e. ZZ )' % (A0, lhs2)) if lab == 'root1dvdsmul1' else w.s([c, b], 'zmulcld', '( %s -> %s e. ZZ )' % (A0, lhs2))
    w.qed([d3, w.s([n, z1, z2, w.inst('root1dvds')], 'syl3anc', '( %s -> ( N || ( %s - %s ) -> %s = %s ) )' % (A0, lhs1, lhs2, RP(lhs1), RP(lhs2)))], 'mpd', '( %s -> %s = %s )' % (A0, RP(lhs1), RP(lhs2))); run(w)

# ---- fzomodf1olem
A0 = '( N e. NN /\\ U e. ZZ /\\ %s )' % COP('U', 'N')
A1 = '( %s /\\ ( B e. %s /\\ C e. %s ) )' % (A0, F0, F0)
w = W('fzomodf1olem', 'Lemma for fzomodf1o: multiplication by a unit is injective on the residues.')
n = w.s([w.s([], 'simp1', '( %s -> N e. NN )' % A0)], 'adantr', '( %s -> N e. NN )' % A1)
u = w.s([w.s([], 'simp2', '( %s -> U e. ZZ )' % A0)], 'adantr', '( %s -> U e. ZZ )' % A1)
cop = w.s([w.s([], 'simp3', '( %s -> %s )' % (A0, COP('U', 'N')))], 'adantr', '( %s -> %s )' % (A1, COP('U', 'N')))
b = w.s([], 'simprl', '( %s -> B e. %s )' % (A1, F0)); c = w.s([], 'simprr', '( %s -> C e. %s )' % (A1, F0))
bz = w.s([b, w.inst('elfzoelz')], 'syl', '( %s -> B e. ZZ )' % A1); cz = w.s([c, w.inst('elfzoelz')], 'syl', '( %s -> C e. ZZ )' % A1)
ub = w.s([u, bz], 'zmulcld', '( %s -> ( U x. B ) e. ZZ )' % A1); uc = w.s([u, cz], 'zmulcld', '( %s -> ( U x. C ) e. ZZ )' % A1)
md = w.s([n, ub, uc, w.inst('moddvds')], 'syl3anc', '( %s -> ( ( ( U x. B ) mod N ) = ( ( U x. C ) mod N ) <-> N || ( ( U x. B ) - ( U x. C ) ) ) )' % A1)
dist = w.s([w.s([u], 'zcnd', '( %s -> U e. CC )' % A1), w.s([bz], 'zcnd', '( %s -> B e. CC )' % A1), w.s([cz], 'zcnd', '( %s -> C e. CC )' % A1)], 'subdid', '( %s -> ( U x. ( B - C ) ) = ( ( U x. B ) - ( U x. C ) ) )' % A1)
md2 = w.s([md, w.s([w.s([dist], 'eqcomd', '( %s -> ( ( U x. B ) - ( U x. C ) ) = ( U x. ( B - C ) ) )' % A1)], 'breq2d', '( %s -> ( N || ( ( U x. B ) - ( U x. C ) ) <-> N || ( U x. ( B - C ) ) ) )' % A1)], 'bitrd', '( %s -> ( ( ( U x. B ) mod N ) = ( ( U x. C ) mod N ) <-> N || ( U x. ( B - C ) ) ) )' % A1)
gc = w.s([w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A1), u], 'gcdcomd', '( %s -> ( N gcd U ) = ( U gcd N ) )' % A1), cop], 'eqtrd', '( %s -> ( N gcd U ) = 1 )' % A1)
cd = w.s([w.s([n], 'nnzd', '( %s -> N e. ZZ )' % A1), u, w.s([bz, cz], 'zsubcld', '( %s -> ( B - C ) e. ZZ )' % A1), w.inst('coprmdvds')], 'syl3anc', '( %s -> ( ( N || ( U x. ( B - C ) ) /\\ ( N gcd U ) = 1 ) -> N || ( B - C ) ) )' % A1)
cd2 = w.s([gc, cd], 'mpan2d', '( %s -> ( N || ( U x. ( B - C ) ) -> N || ( B - C ) ) )' % A1)
ce = w.s([n, b, c, w.inst('fzocongeq0')], 'syl3anc', '( %s -> ( N || ( B - C ) <-> B = C ) )' % A1)
w.qed([w.s([md2], 'biimpd', '( %s -> ( ( ( U x. B ) mod N ) = ( ( U x. C ) mod N ) -> N || ( U x. ( B - C ) ) ) )' % A1), w.s([cd2, w.s([ce], 'biimpd', '( %s -> ( N || ( B - C ) -> B = C ) )' % A1)], 'syld', '( %s -> ( N || ( U x. ( B - C ) ) -> B = C ) )' % A1)], 'syld', '( %s -> ( ( ( U x. B ) mod N ) = ( ( U x. C ) mod N ) -> B = C ) )' % A1); run(w)

# ---- fzomodf1o
MAP = '( x e. %s |-> ( ( U x. x ) mod N ) )' % F0
w = W('fzomodf1o', 'Multiplication by a unit U mod N permutes the residues ( 0 ..^ N ) (Mathlib Units.mulLeft_bijective on ZMod N).')
n = w.s([], 'simp1', '( %s -> N e. NN )' % A0); u = w.s([], 'simp2', '( %s -> U e. ZZ )' % A0)
Ax = '( %s /\\ x e. %s )' % (A0, F0)
ux = w.s([w.s([u], 'adantr', '( %s -> U e. ZZ )' % Ax), w.s([w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, F0)), w.inst('elfzoelz')], 'syl', '( %s -> x e. ZZ )' % Ax)], 'zmulcld', '( %s -> ( U x. x ) e. ZZ )' % Ax)
mem = w.s([ux, w.s([n], 'adantr', '( %s -> N e. NN )' % Ax), w.inst('zmodfzo')], 'syl2anc', '( %s -> ( ( U x. x ) mod N ) e. %s )' % (Ax, F0))
r1 = w.s([mem], 'ralrimiva', '( %s -> A. x e. %s ( ( U x. x ) mod N ) e. %s )' % (A0, F0, F0))
Axy = '( %s /\\ ( x e. %s /\\ y e. %s ) )' % (A0, F0, F0)
inj = w.s([], 'fzomodf1olem', '( %s -> ( ( ( U x. x ) mod N ) = ( ( U x. y ) mod N ) -> x = y ) )' % Axy)
r2 = w.s([inj], 'ralrimivva', '( %s -> A. x e. %s A. y e. %s ( ( ( U x. x ) mod N ) = ( ( U x. y ) mod N ) -> x = y ) )' % (A0, F0, F0))
sub = w.s([w.s([], 'oveq2', '( x = y -> ( U x. x ) = ( U x. y ) )')], 'oveq1d', '( x = y -> ( ( U x. x ) mod N ) = ( ( U x. y ) mod N ) )')
f1 = w.s([w.s([], 'eqid', '%s = %s' % (MAP, MAP)), sub], 'f1mpt', '( %s : %s -1-1-> %s <-> ( A. x e. %s ( ( U x. x ) mod N ) e. %s /\\ A. x e. %s A. y e. %s ( ( ( U x. x ) mod N ) = ( ( U x. y ) mod N ) -> x = y ) ) )' % (MAP, F0, F0, F0, F0, F0, F0))
f1d = w.s([w.s([r1, r2], 'jca', '( %s -> ( A. x e. %s ( ( U x. x ) mod N ) e. %s /\\ A. x e. %s A. y e. %s ( ( ( U x. x ) mod N ) = ( ( U x. y ) mod N ) -> x = y ) ) )' % (A0, F0, F0, F0, F0)), f1], 'sylibr', '( %s -> %s : %s -1-1-> %s )' % (A0, MAP, F0, F0))
fin = w.s([], 'fzofi', '%s e. Fin' % F0)
en = w.s([fin], 'enrefi' if False else 'enref' if False else 'enrefg', '( %s e. Fin -> %s ~~ %s )' % (F0, F0, F0))
w.lines.pop()
en = w.s([fin, w.inst('enrefg')], 'ax-mp', '%s ~~ %s' % (F0, F0))
bi = w.s([en, fin, w.inst('f1finf1o')], 'mp2an', '( %s : %s -1-1-> %s <-> %s : %s -1-1-onto-> %s )' % (MAP, F0, F0, MAP, F0, F0))
w.qed([f1d, bi], 'sylib', '( %s -> %s : %s -1-1-onto-> %s )' % (A0, MAP, F0, F0)); run(w)

# ---- dchrgsreix
AR = '( %s /\\ A e. ZZ /\\ ( U e. ZZ /\\ %s ) )' % (HC, COP('U', 'N'))
Ab = '( %s /\\ b e. %s )' % (AR, F0); Aa = '( %s /\\ a e. %s )' % (AR, F0)
UB = '( U x. b )'; UBM = '( ( U x. b ) mod N )'
TGT = 'sum_ a e. %s ( %s x. %s )' % (F0, EV('X', 'N', '( U x. a )'), RP('( A x. ( U x. a ) )'))
w = W('dchrgsreix', 'The shifted Gauss sum reindexed by a unit U: the sum over a of X at U a times the root of unity at A U a (Mathlib Fintype.sum_bijective with mulLeft_bijective).')
hc = w.s([], 'simp1', '( %s -> %s )' % (AR, HC)); n = w.s([hc], 'simpld', '( %s -> N e. NN )' % AR); x = w.s([hc], 'simprd', '( %s -> X e. %s )' % (AR, DB('N')))
a = w.s([], 'simp2', '( %s -> A e. ZZ )' % AR); uc = w.s([], 'simp3', '( %s -> ( U e. ZZ /\\ %s ) )' % (AR, COP('U', 'N'))); u = w.s([uc], 'simpld', '( %s -> U e. ZZ )' % AR); cop = w.s([uc], 'simprd', '( %s -> %s )' % (AR, COP('U', 'N')))
bij = w.s([n, u, cop, w.inst('fzomodf1o')], 'syl3anc', '( %s -> %s : %s -1-1-onto-> %s )' % (AR, MAP, F0, F0))
# val: ( F ` b ) = ( ( U x. b ) mod N )
Abx = '( %s /\\ x = b )' % Ab
sb = w.s([w.s([w.s([], 'simpr', '( %s -> x = b )' % Abx)], 'oveq2d', '( %s -> ( U x. x ) = ( U x. b ) )' % Abx)], 'oveq1d', '( %s -> ( ( U x. x ) mod N ) = %s )' % (Abx, UBM))
val = w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (Ab, MAP, MAP)), sb, w.s([], 'simpr', '( %s -> b e. %s )' % (Ab, F0)), w.s([w.s([], 'ovex', '%s e. _V' % UBM)], 'a1i', '( %s -> %s e. _V )' % (Ab, UBM))], 'fvmptd', '( %s -> ( %s ` b ) = %s )' % (Ab, MAP, UBM))
fin = w.s([w.s([], 'fzofi', '%s e. Fin' % F0)], 'a1i', '( %s -> %s e. Fin )' % (AR, F0))
g, z, d, l = dchyp(w)
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, F0)), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Aa)
xc = w.s([g, z, d, l, w.s([x], 'adantr', '( %s -> X e. %s )' % (Aa, DB('N'))), az], 'dchrzrhcl', '( %s -> %s e. CC )' % (Aa, EV('X', 'N', 'a')))
rc = w.s([w.s([n], 'adantr', '( %s -> N e. NN )' % Aa), w.s([w.s([a], 'adantr', '( %s -> A e. ZZ )' % Aa), az], 'zmulcld', '( %s -> ( A x. a ) e. ZZ )' % Aa), w.inst('root1expcl')], 'syl2anc', '( %s -> %s e. CC )' % (Aa, RP('( A x. a )')))
bcl = w.s([xc, rc], 'mulcld', '( %s -> %s e. CC )' % (Aa, TERMR('X', 'N', 'a', 'A')))
re, D = fsumf1o(w, AR, 'a', F0, TERMR('X', 'N', 'a', 'A'), 'b', F0, MAP, UBM, fin, bij, val, bcl)
# reduce D under Ab
nb = w.s([n], 'adantr', '( %s -> N e. NN )' % Ab); hcb = w.s([hc], 'adantr', '( %s -> %s )' % (Ab, HC))
bz = w.s([w.s([], 'simpr', '( %s -> b e. %s )' % (Ab, F0)), w.inst('elfzoelz')], 'syl', '( %s -> b e. ZZ )' % Ab)
ubz = w.s([w.s([u], 'adantr', '( %s -> U e. ZZ )' % Ab), bz], 'zmulcld', '( %s -> %s e. ZZ )' % (Ab, UB))
x1 = w.s([hcb, ubz, w.inst('dchrzrhmod')], 'syl2anc', '( %s -> %s = %s )' % (Ab, EV('X', 'N', UBM), EV('X', 'N', UB)))
ubmz = w.s([w.s([ubz, nb, w.inst('zmodcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (Ab, UBM))], 'nn0zd', '( %s -> %s e. ZZ )' % (Ab, UBM))
dv = w.s([nb, ubz, w.inst('zmoddvds')], 'syl2anc', '( %s -> N || ( %s - %s ) )' % (Ab, UBM, UB))
r1 = w.s([nb, w.s([ubmz, ubz, w.s([a], 'adantr', '( %s -> A e. ZZ )' % Ab)], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ A e. ZZ ) )' % (Ab, UBM, UB)), dv, w.inst('root1dvdsmul2')], 'syl3anc', '( %s -> %s = %s )' % (Ab, RP('( A x. %s )' % UBM), RP('( A x. %s )' % UB)))
t = w.s([x1, r1], 'oveq12d', '( %s -> %s = ( %s x. %s ) )' % (Ab, D, EV('X', 'N', UB), RP('( A x. %s )' % UB)))
s2 = w.s([t], 'sumeq2dv', '( %s -> sum_ b e. %s %s = sum_ b e. %s ( %s x. %s ) )' % (AR, F0, D, F0, EV('X', 'N', UB), RP('( A x. %s )' % UB)))
cv, C2 = cbvsum(w, F0, '( %s x. %s )' % (EV('X', 'N', UB), RP('( A x. %s )' % UB)), 'b', 'a')
assert C2 == '( %s x. %s )' % (EV('X', 'N', '( U x. a )'), RP('( A x. ( U x. a ) )')), C2
w.qed([w.s([re, s2], 'eqtrd', '( %s -> %s = sum_ b e. %s ( %s x. %s ) )' % (AR, GR('X', 'N', 'A'), F0, EV('X', 'N', UB), RP('( A x. %s )' % UB))), w.s([cv], 'a1i', '( %s -> sum_ b e. %s ( %s x. %s ) = %s )' % (AR, F0, EV('X', 'N', UB), RP('( A x. %s )' % UB), TGT))], 'eqtrd', '( %s -> %s = %s )' % (AR, GR('X', 'N', 'A'), TGT)); run(w)

# ---- dchrgsmul
XU = EV('X', 'N', 'U'); AU = '( A x. U )'
w = W('dchrgsmul', 'Reindexing by a unit U: X at U times the Gauss sum shifted by A U is the Gauss sum shifted by A (Mathlib gaussSum_mulShift).')
hc = w.s([], 'simp1', '( %s -> %s )' % (AR, HC)); n = w.s([hc], 'simpld', '( %s -> N e. NN )' % AR); x = w.s([hc], 'simprd', '( %s -> X e. %s )' % (AR, DB('N')))
a = w.s([], 'simp2', '( %s -> A e. ZZ )' % AR); uc = w.s([], 'simp3', '( %s -> ( U e. ZZ /\\ %s ) )' % (AR, COP('U', 'N'))); u = w.s([uc], 'simpld', '( %s -> U e. ZZ )' % AR)
re = w.s([], 'dchrgsreix', '( %s -> %s = %s )' % (AR, GR('X', 'N', 'A'), TGT))
g, z, d, l = dchyp(w)
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, F0)), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Aa)
xa = w.s([x], 'adantr', '( %s -> X e. %s )' % (Aa, DB('N'))); ua = w.s([u], 'adantr', '( %s -> U e. ZZ )' % Aa); aa = w.s([a], 'adantr', '( %s -> A e. ZZ )' % Aa); na = w.s([n], 'adantr', '( %s -> N e. NN )' % Aa)
mul = w.s([g, z, d, l, xa, ua, az], 'dchrzrhmul', '( %s -> %s = ( %s x. %s ) )' % (Aa, EV('X', 'N', '( U x. a )'), XU, EV('X', 'N', 'a')))
asc = w.s([w.s([w.s([aa], 'zcnd', '( %s -> A e. CC )' % Aa), w.s([ua], 'zcnd', '( %s -> U e. CC )' % Aa), w.s([az], 'zcnd', '( %s -> a e. CC )' % Aa)], 'mulassd', '( %s -> ( %s x. a ) = ( A x. ( U x. a ) ) )' % (Aa, AU))], 'eqcomd', '( %s -> ( A x. ( U x. a ) ) = ( %s x. a ) )' % (Aa, AU))
rr = w.s([asc], 'oveq2d', '( %s -> %s = %s )' % (Aa, RP('( A x. ( U x. a ) )'), RP('( %s x. a )' % AU)))
xuc = w.s([g, z, d, l, xa, ua], 'dchrzrhcl', '( %s -> %s e. CC )' % (Aa, XU)); xac = w.s([g, z, d, l, xa, az], 'dchrzrhcl', '( %s -> %s e. CC )' % (Aa, EV('X', 'N', 'a')))
rc = w.s([na, w.s([w.s([aa, ua], 'zmulcld', '( %s -> %s e. ZZ )' % (Aa, AU)), az], 'zmulcld', '( %s -> ( %s x. a ) e. ZZ )' % (Aa, AU)), w.inst('root1expcl')], 'syl2anc', '( %s -> %s e. CC )' % (Aa, RP('( %s x. a )' % AU)))
t1 = w.s([mul, rr], 'oveq12d', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) x. %s ) )' % (Aa, EV('X', 'N', '( U x. a )'), RP('( A x. ( U x. a ) )'), XU, EV('X', 'N', 'a'), RP('( %s x. a )' % AU)))
t2 = w.s([xuc, xac, rc], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. %s ) )' % (Aa, XU, EV('X', 'N', 'a'), RP('( %s x. a )' % AU), XU, TERMR('X', 'N', 'a', AU)))
s1 = w.s([w.s([t1, t2], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (Aa, EV('X', 'N', '( U x. a )'), RP('( A x. ( U x. a ) )'), XU, TERMR('X', 'N', 'a', AU)))], 'sumeq2dv', '( %s -> %s = sum_ a e. %s ( %s x. %s ) )' % (AR, TGT, F0, XU, TERMR('X', 'N', 'a', AU)))
fin = w.s([w.s([], 'fzofi', '%s e. Fin' % F0)], 'a1i', '( %s -> %s e. Fin )' % (AR, F0))
xuc0 = w.s([g, z, d, l, x, u], 'dchrzrhcl', '( %s -> %s e. CC )' % (AR, XU))
bcl = w.s([xac, rc], 'mulcld', '( %s -> %s e. CC )' % (Aa, TERMR('X', 'N', 'a', AU)))
mc = w.s([fin, xuc0, bcl], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ a e. %s ( %s x. %s ) )' % (AR, XU, GR('X', 'N', AU), F0, XU, TERMR('X', 'N', 'a', AU)))
w.qed([mc, w.s([w.s([re, s1], 'eqtrd', '( %s -> %s = sum_ a e. %s ( %s x. %s ) )' % (AR, GR('X', 'N', 'A'), F0, XU, TERMR('X', 'N', 'a', AU)))], 'eqcomd', '( %s -> sum_ a e. %s ( %s x. %s ) = %s )' % (AR, F0, XU, TERMR('X', 'N', 'a', AU), GR('X', 'N', 'A')))], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (AR, XU, GR('X', 'N', AU), GR('X', 'N', 'A'))); run(w)

# ---- dchrgsper
AP = '( %s /\\ ( A e. ZZ /\\ B e. ZZ ) /\\ N || ( A - B ) )' % HC
Aa = '( %s /\\ a e. %s )' % (AP, F0)
w = W('dchrgsper', 'The shifted Gauss sum depends on the shift only mod N.')
n = w.s([w.s([w.s([], 'simp1', '( %s -> %s )' % (AP, HC))], 'simpld', '( %s -> N e. NN )' % AP)], 'adantr', '( %s -> N e. NN )' % Aa)
ab = w.s([w.s([], 'simp2', '( %s -> ( A e. ZZ /\\ B e. ZZ ) )' % AP)], 'adantr', '( %s -> ( A e. ZZ /\\ B e. ZZ ) )' % Aa)
dv = w.s([w.s([], 'simp3', '( %s -> N || ( A - B ) )' % AP)], 'adantr', '( %s -> N || ( A - B ) )' % Aa)
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, F0)), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Aa)
r = w.s([n, w.s([w.s([ab], 'simpld', '( %s -> A e. ZZ )' % Aa), w.s([ab], 'simprd', '( %s -> B e. ZZ )' % Aa), az], '3jca', '( %s -> ( A e. ZZ /\\ B e. ZZ /\\ a e. ZZ ) )' % Aa), dv, w.inst('root1dvdsmul1')], 'syl3anc', '( %s -> %s = %s )' % (Aa, RP('( A x. a )'), RP('( B x. a )')))
w.qed([w.s([r], 'oveq2d', '( %s -> %s = %s )' % (Aa, TERMR('X', 'N', 'a', 'A'), TERMR('X', 'N', 'a', 'B')))], 'sumeq2dv', '( %s -> %s = %s )' % (AP, GR('X', 'N', 'A'), GR('X', 'N', 'B'))); run(w)

# ---- dchrgsshiftr
AS = '( %s /\\ U e. ZZ /\\ %s )' % (HC, COP('U', 'N'))
T = GS('N', 'X'); IXU = '( ( %s ` X ) ` ( %s ` U ) )' % (INV('N'), LZ('N')); CXU = '( * ` %s )' % XU
Aa = '( %s /\\ a e. %s )' % (AS, F0)
w = W('dchrgsshiftr', 'The shift identity (Mathlib gaussSum_mulShift_eq) in the root form: the Gauss sum shifted by a unit U is the inverse character at U times the Gauss sum.')
hc = w.s([], 'simp1', '( %s -> %s )' % (AS, HC)); n = w.s([hc], 'simpld', '( %s -> N e. NN )' % AS); x = w.s([hc], 'simprd', '( %s -> X e. %s )' % (AS, DB('N')))
u = w.s([], 'simp2', '( %s -> U e. ZZ )' % AS); cop = w.s([], 'simp3', '( %s -> %s )' % (AS, COP('U', 'N')))
m = w.s([hc, w.s([], '1zzd', '( %s -> 1 e. ZZ )' % AS), w.s([u, cop], 'jca', '( %s -> ( U e. ZZ /\\ %s ) )' % (AS, COP('U', 'N'))), w.inst('dchrgsmul')], 'syl3anc', '( %s -> ( %s x. %s ) = %s )' % (AS, XU, GR('X', 'N', '( 1 x. U )'), GR('X', 'N', '1')))
uc = w.s([w.s([u], 'zcnd', '( %s -> U e. CC )' % AS)], 'mullidd', '( %s -> ( 1 x. U ) = U )' % AS)
ua = w.s([uc], 'adantr', '( %s -> ( 1 x. U ) = U )' % Aa)
s1 = w.s([w.s([w.s([w.s([ua], 'oveq1d', '( %s -> ( ( 1 x. U ) x. a ) = ( U x. a ) )' % Aa)], 'oveq2d', '( %s -> %s = %s )' % (Aa, RP('( ( 1 x. U ) x. a )'), RP('( U x. a )')))], 'oveq2d', '( %s -> %s = %s )' % (Aa, TERMR('X', 'N', 'a', '( 1 x. U )'), TERMR('X', 'N', 'a', 'U')))], 'sumeq2dv', '( %s -> %s = %s )' % (AS, GR('X', 'N', '( 1 x. U )'), GR('X', 'N', 'U')))
v3 = w.s([hc, w.inst('dchrgsval3')], 'syl', '( %s -> %s = %s )' % (AS, T, GR('X', 'N', '1')))
key = w.s([w.s([w.s([s1], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (AS, XU, GR('X', 'N', '( 1 x. U )'), XU, GR('X', 'N', 'U')))], 'eqcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (AS, XU, GR('X', 'N', 'U'), XU, GR('X', 'N', '( 1 x. U )'))), w.s([m, w.s([v3], 'eqcomd', '( %s -> %s = %s )' % (AS, GR('X', 'N', '1'), T))], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (AS, XU, GR('X', 'N', '( 1 x. U )'), T))], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (AS, XU, GR('X', 'N', 'U'), T))
# |X(U)| = 1, conj(z) z = 1
g, z, d, l = dchyp(w)
zu = w.s([], 'eqid', '%s = %s' % (UZ('N'), UZ('N')))
un = w.s([cop, w.s([w.s([n], 'nnnn0d', '( %s -> N e. NN0 )' % AS), u, w.s([z, zu, l], 'znunit', '( ( N e. NN0 /\\ U e. ZZ ) -> ( ( %s ` U ) e. %s <-> %s ) )' % (LZ('N'), UZ('N'), COP('U', 'N')))], 'syl2anc', '( %s -> ( ( %s ` U ) e. %s <-> %s ) )' % (AS, LZ('N'), UZ('N'), COP('U', 'N')))], 'mpbird', '( %s -> ( %s ` U ) e. %s )' % (AS, LZ('N'), UZ('N')))
ab1 = w.s([g, d, x, z, zu, un], 'dchrabs', '( %s -> ( abs ` %s ) = 1 )' % (AS, XU))
xuc = w.s([g, z, d, l, x, u], 'dchrzrhcl', '( %s -> %s e. CC )' % (AS, XU))
sq = w.s([xuc, w.inst('absvalsq')], 'syl', '( %s -> ( ( abs ` %s ) ^ 2 ) = ( %s x. %s ) )' % (AS, XU, XU, CXU))
one = w.s([w.s([w.s([ab1], 'oveq1d', '( %s -> ( ( abs ` %s ) ^ 2 ) = ( 1 ^ 2 ) )' % (AS, XU)), w.s([w.s([], 'sq1', '( 1 ^ 2 ) = 1')], 'a1i', '( %s -> ( 1 ^ 2 ) = 1 )' % AS)], 'eqtrd', '( %s -> ( ( abs ` %s ) ^ 2 ) = 1 )' % (AS, XU)), sq], 'eqtr3d', '( %s -> ( %s x. %s ) = 1 )' % (AS, XU, CXU))
cxc = w.s([xuc], 'cjcld', '( %s -> %s e. CC )' % (AS, CXU))
one2 = w.s([w.s([cxc, xuc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (AS, CXU, XU, XU, CXU)), one], 'eqtrd', '( %s -> ( %s x. %s ) = 1 )' % (AS, CXU, XU))
# GR(X,U) = 1 GR = ( cz z ) GR = cz ( z GR ) = cz T
gcl = w.s([], 'fzofi', '%s e. Fin' % F0)
az = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, F0)), w.inst('elfzoelz')], 'syl', '( %s -> a e. ZZ )' % Aa)
xac = w.s([g, z, d, l, w.s([x], 'adantr', '( %s -> X e. %s )' % (Aa, DB('N'))), az], 'dchrzrhcl', '( %s -> %s e. CC )' % (Aa, EV('X', 'N', 'a')))
rc = w.s([w.s([n], 'adantr', '( %s -> N e. NN )' % Aa), w.s([w.s([u], 'adantr', '( %s -> U e. ZZ )' % Aa), az], 'zmulcld', '( %s -> ( U x. a ) e. ZZ )' % Aa), w.inst('root1expcl')], 'syl2anc', '( %s -> %s e. CC )' % (Aa, RP('( U x. a )')))
grc = w.s([w.s([gcl], 'a1i', '( %s -> %s e. Fin )' % (AS, F0)), w.s([xac, rc], 'mulcld', '( %s -> %s e. CC )' % (Aa, TERMR('X', 'N', 'a', 'U')))], 'fsumcl', '( %s -> %s e. CC )' % (AS, GR('X', 'N', 'U')))
e1 = w.s([w.s([grc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (AS, GR('X', 'N', 'U'), GR('X', 'N', 'U')))], 'eqcomd', '( %s -> %s = ( 1 x. %s ) )' % (AS, GR('X', 'N', 'U'), GR('X', 'N', 'U')))
e2 = w.s([w.s([one2], 'eqcomd', '( %s -> 1 = ( %s x. %s ) )' % (AS, CXU, XU))], 'oveq1d', '( %s -> ( 1 x. %s ) = ( ( %s x. %s ) x. %s ) )' % (AS, GR('X', 'N', 'U'), CXU, XU, GR('X', 'N', 'U')))
e3 = w.s([cxc, xuc, grc], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) ) )' % (AS, CXU, XU, GR('X', 'N', 'U'), CXU, XU, GR('X', 'N', 'U')))
e4 = w.s([key], 'oveq2d', '( %s -> ( %s x. ( %s x. %s ) ) = ( %s x. %s ) )' % (AS, CXU, XU, GR('X', 'N', 'U'), CXU, T))
cj = dchr_conj(w, AS, n, x, u, 'N', 'X', 'U')
w.qed([w.s([w.s([w.s([e1, e2], 'eqtrd', '( %s -> %s = ( ( %s x. %s ) x. %s ) )' % (AS, GR('X', 'N', 'U'), CXU, XU, GR('X', 'N', 'U'))), e3], 'eqtrd', '( %s -> %s = ( %s x. ( %s x. %s ) ) )' % (AS, GR('X', 'N', 'U'), CXU, XU, GR('X', 'N', 'U'))), e4], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (AS, GR('X', 'N', 'U'), CXU, T)), w.s([w.s([cj], 'eqcomd', '( %s -> %s = %s )' % (AS, CXU, IXU))], 'oveq1d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (AS, CXU, T, IXU, T))], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (AS, GR('X', 'N', 'U'), IXU, T)); run(w)

# ---- dchrgsshift
w = W('dchrgsshift', 'The shift identity (Lean gaussSum_mulShift_eq; LargeSieve char_twisted_sum_eq): the Gauss sum with the additive character shifted by a unit U is the inverse character at U times the Gauss sum.')
n = w.s([w.s([], 'simp1', '( %s -> %s )' % (AS, HC))], 'simpld', '( %s -> N e. NN )' % AS); u = w.s([], 'simp2', '( %s -> U e. ZZ )' % AS)
w.qed([w.s([n, u, w.inst('dchrgsefsum')], 'syl2anc', '( %s -> %s = %s )' % (AS, G('X', 'N', 'U'), GR('X', 'N', 'U'))), w.s([], 'dchrgsshiftr', '( %s -> %s = ( %s x. %s ) )' % (AS, GR('X', 'N', 'U'), IXU, T))], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (AS, G('X', 'N', 'U'), IXU, T)); run(w)
