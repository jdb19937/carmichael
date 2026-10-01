"""Sortie A3, batch 3: pool elements are coprime to the modulus, and every
integer coprime to the modulus has L || ( a ^ lambdaL Q ) - 1 (the vebkz
hypothesis; Lean: pool_coprimeW, exponent_dvd_lambdaW)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a3lib
from a3lib import fpp, lmodprod, memdvds, FPP, FP0
from tm import *
from lin import linarith
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

LM = '( Lmod ` Q )'
LA = '( lambdaL ` Q )'
PL = '( ( Q pool Z ) ` K )'

# ------------------------------------------------------------ extrwfrm
w = W('extrwfrm', 'Fermat for an exponent divisible by P - 1: P || ( ( A ^ M ) - 1 ) (inside Lean exponent_dvd_lambdaW).')
H = '( ( P e. Prime /\\ A e. ZZ /\\ -. P || A ) /\\ ( M e. NN /\\ ( P - 1 ) || M ) )'
pp = w.s([], 'simpl1', '( %s -> P e. Prime )' % H)
az = w.s([], 'simpl2', '( %s -> A e. ZZ )' % H)
nd = w.s([], 'simpl3', '( %s -> -. P || A )' % H)
mnn = w.s([], 'simprl', '( %s -> M e. NN )' % H)
mdv = w.s([], 'simprr', '( %s -> ( P - 1 ) || M )' % H)
puz = w.s([pp, w.inst('prmuz2')], 'syl', '( %s -> P e. ( ZZ>= ` 2 ) )' % H)
pnn = w.s([pp, w.inst('prmnn')], 'syl', '( %s -> P e. NN )' % H)
prp = w.s([pnn], 'nnrpd', '( %s -> P e. RR+ )' % H)
p1nn = w.s([puz, w.inst('uz2m1nn')], 'syl', '( %s -> ( P - 1 ) e. NN )' % H)
# J = M / ( P - 1 ) e. NN
jnn = w.s([w.s([mnn, p1nn, w.inst('nndivdvds')], 'syl2anc', '( %s -> ( ( P - 1 ) || M <-> ( M / ( P - 1 ) ) e. NN ) )' % H), mdv], 'mpbid', '( %s -> ( M / ( P - 1 ) ) e. NN )' % H)
jnn0 = w.s([jnn], 'nnnn0d', '( %s -> ( M / ( P - 1 ) ) e. NN0 )' % H)
meq = w.s([w.s([mnn], 'nncnd', '( %s -> M e. CC )' % H), w.s([p1nn], 'nncnd', '( %s -> ( P - 1 ) e. CC )' % H), w.s([p1nn], 'nnne0d', '( %s -> ( P - 1 ) =/= 0 )' % H)], 'divcan2d', '( %s -> ( ( P - 1 ) x. ( M / ( P - 1 ) ) ) = M )' % H)
# Fermat
fer = w.s([pp, az, nd, w.inst('vfermltl')], 'syl3anc', '( %s -> ( ( A ^ ( P - 1 ) ) mod P ) = 1 )' % H)
one = w.s([w.s([pnn], 'nnred', '( %s -> P e. RR )' % H), w.s([puz, w.inst('eluz2gt1')], 'syl', '( %s -> 1 < P )' % H), w.inst('1mod')], 'syl2anc', '( %s -> ( 1 mod P ) = 1 )' % H)
fer2 = w.s([fer, w.s([one], 'eqcomd', '( %s -> 1 = ( 1 mod P ) )' % H)], 'eqtrd', '( %s -> ( ( A ^ ( P - 1 ) ) mod P ) = ( 1 mod P ) )' % H)
aez = w.s([az, w.s([p1nn], 'nnnn0d', '( %s -> ( P - 1 ) e. NN0 )' % H)], 'zexpcld', '( %s -> ( A ^ ( P - 1 ) ) e. ZZ )' % H)
mex = w.s([w.s([w.s([aez, w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % H)], 'jca', '( %s -> ( ( A ^ ( P - 1 ) ) e. ZZ /\\ 1 e. ZZ ) )' % H), w.s([jnn0, prp], 'jca', '( %s -> ( ( M / ( P - 1 ) ) e. NN0 /\\ P e. RR+ ) )' % H), fer2], '3jca', '( %s -> ( ( ( A ^ ( P - 1 ) ) e. ZZ /\\ 1 e. ZZ ) /\\ ( ( M / ( P - 1 ) ) e. NN0 /\\ P e. RR+ ) /\\ ( ( A ^ ( P - 1 ) ) mod P ) = ( 1 mod P ) ) )' % H), w.inst('modexp')], 'syl', '( %s -> ( ( ( A ^ ( P - 1 ) ) ^ ( M / ( P - 1 ) ) ) mod P ) = ( ( 1 ^ ( M / ( P - 1 ) ) ) mod P ) )' % H)
oneexp = w.s([w.s([jnn0], 'nn0zd', '( %s -> ( M / ( P - 1 ) ) e. ZZ )' % H), w.inst('1exp')], 'syl', '( %s -> ( 1 ^ ( M / ( P - 1 ) ) ) = 1 )' % H)
mex2 = w.s([mex, w.s([oneexp], 'oveq1d', '( %s -> ( ( 1 ^ ( M / ( P - 1 ) ) ) mod P ) = ( 1 mod P ) )' % H)], 'eqtrd', '( %s -> ( ( ( A ^ ( P - 1 ) ) ^ ( M / ( P - 1 ) ) ) mod P ) = ( 1 mod P ) )' % H)
em = w.s([w.s([az], 'zcnd', '( %s -> A e. CC )' % H), w.s([p1nn], 'nnnn0d', '( %s -> ( P - 1 ) e. NN0 )' % H), jnn0, w.inst('expmul')], 'syl3anc', '( %s -> ( A ^ ( ( P - 1 ) x. ( M / ( P - 1 ) ) ) ) = ( ( A ^ ( P - 1 ) ) ^ ( M / ( P - 1 ) ) ) )' % H)
em2 = w.s([w.s([meq], 'oveq2d', '( %s -> ( A ^ ( ( P - 1 ) x. ( M / ( P - 1 ) ) ) ) = ( A ^ M ) )' % H)], 'eqcomd', '( %s -> ( A ^ M ) = ( A ^ ( ( P - 1 ) x. ( M / ( P - 1 ) ) ) ) )' % H)
tot = w.s([w.s([w.s([em2, em], 'eqtrd', '( %s -> ( A ^ M ) = ( ( A ^ ( P - 1 ) ) ^ ( M / ( P - 1 ) ) ) )' % H)], 'oveq1d', '( %s -> ( ( A ^ M ) mod P ) = ( ( ( A ^ ( P - 1 ) ) ^ ( M / ( P - 1 ) ) ) mod P ) )' % H), mex2], 'eqtrd', '( %s -> ( ( A ^ M ) mod P ) = ( 1 mod P ) )' % H)
amz = w.s([az, w.s([mnn], 'nnnn0d', '( %s -> M e. NN0 )' % H)], 'zexpcld', '( %s -> ( A ^ M ) e. ZZ )' % H)
md = w.s([pnn, amz, w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % H), w.inst('moddvds')], 'syl3anc', '( %s -> ( ( ( A ^ M ) mod P ) = ( 1 mod P ) <-> P || ( ( A ^ M ) - 1 ) ) )' % H)
w.qed([md, tot], 'mpbid', '( %s -> P || ( ( A ^ M ) - 1 ) )' % H)
run(w)

# ------------------------------------------------------------ extrwlam
w = W('extrwlam', 'Every integer coprime to the modulus L satisfies L || ( ( a ^ lambdaL Q ) - 1 ): the vebkz exponent hypothesis (Lean: exponent_dvd_lambdaW, in integer form).')
H = '( Q e. %s /\\ A e. ZZ /\\ ( A gcd %s ) = 1 )' % (FPP, LM)
NM = '( ( A ^ %s ) - 1 )' % LA
q1 = w.s([], 'simp1', '( %s -> Q e. %s )' % (H, FPP))
az = w.s([], 'simp2', '( %s -> A e. ZZ )' % H)
gc = w.s([], 'simp3', '( %s -> ( A gcd %s ) = 1 )' % (H, LM))
ss, fin, f0 = fpp(w, H, q1)
lmp = lmodprod(w, H, f0)
lnn = w.s([q1, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (H, LM))
lz = w.s([lnn], 'nnzd', '( %s -> %s e. ZZ )' % (H, LM))
lann = w.s([q1, w.inst('lambdalcl')], 'syl', '( %s -> %s e. NN )' % (H, LA))
amz = w.s([w.s([az, w.s([lann], 'nnnn0d', '( %s -> %s e. NN0 )' % (H, LA))], 'zexpcld', '( %s -> ( A ^ %s ) e. ZZ )' % (H, LA)), w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % H)], 'zsubcld', '( %s -> %s e. ZZ )' % (H, NM))
# per element of Q
HQ = '( %s /\\ q e. Q )' % H
qel = w.s([], 'simpr', '( %s -> q e. Q )' % HQ)
ssq = w.s([ss], 'adantr', '( %s -> Q C_ Prime )' % HQ)
finq = w.s([fin], 'adantr', '( %s -> Q e. Fin )' % HQ)
qdvp, qp = memdvds(w, HQ, 'Q', finq, ssq, qel)
lmpq = w.s([lmp], 'adantr', '( %s -> %s = prod_ j e. Q j )' % (HQ, LM))
qdvl = w.s([qdvp, lmpq], 'breqtrrd', '( %s -> q || %s )' % (HQ, LM))
qz = w.s([qp, w.inst('prmz')], 'syl', '( %s -> q e. ZZ )' % HQ)
azq = w.s([az], 'adantr', '( %s -> A e. ZZ )' % HQ)
lzq = w.s([lz], 'adantr', '( %s -> %s e. ZZ )' % (HQ, LM))
dg = w.s([w.s([qz, azq, lzq], '3jca', '( %s -> ( q e. ZZ /\\ A e. ZZ /\\ %s e. ZZ ) )' % (HQ, LM)), w.inst('dvdsgcd')], 'syl', '( %s -> ( ( q || A /\\ q || %s ) -> q || ( A gcd %s ) ) )' % (HQ, LM, LM))
dg2 = w.s([dg, qdvl], 'mpan2d', '( %s -> ( q || A -> q || ( A gcd %s ) ) )' % (HQ, LM))
gcq = w.s([gc], 'adantr', '( %s -> ( A gcd %s ) = 1 )' % (HQ, LM))
bi1 = w.s([w.s([gcq], 'breq2d', '( %s -> ( q || ( A gcd %s ) <-> q || 1 ) )' % (HQ, LM))], 'biimpd', '( %s -> ( q || ( A gcd %s ) -> q || 1 ) )' % (HQ, LM))
imp1 = w.s([dg2, bi1], 'syld', '( %s -> ( q || A -> q || 1 ) )' % HQ)
n1 = w.s([qp, w.inst('nprmdvds1')], 'syl', '( %s -> -. q || 1 )' % HQ)
nda = w.s([n1, imp1], 'mtod', '( %s -> -. q || A )' % HQ)
ldv = w.s([w.s([w.s([q1], 'adantr', '( %s -> Q e. %s )' % (HQ, FPP)), qel], 'jca', '( %s -> ( Q e. %s /\\ q e. Q ) )' % (HQ, FPP)), w.inst('lambdaldvds')], 'syl', '( %s -> ( q - 1 ) || %s )' % (HQ, LA))
lannq = w.s([lann], 'adantr', '( %s -> %s e. NN )' % (HQ, LA))
frm = w.s([w.s([w.s([qp, azq, nda], '3jca', '( %s -> ( q e. Prime /\\ A e. ZZ /\\ -. q || A ) )' % HQ), w.s([lannq, ldv], 'jca', '( %s -> ( %s e. NN /\\ ( q - 1 ) || %s ) )' % (HQ, LA, LA))], 'jca', '( %s -> ( ( q e. Prime /\\ A e. ZZ /\\ -. q || A ) /\\ ( %s e. NN /\\ ( q - 1 ) || %s ) ) )' % (HQ, LA, LA)), w.inst('extrwfrm')], 'syl', '( %s -> q || %s )' % (HQ, NM))
ral = w.s([frm], 'ralrimiva', '( %s -> A. q e. Q q || %s )' % (H, NM))
cb = w.s([w.s([w.s([], 'id', '( q = j -> q = j )')], 'breq1d', '( q = j -> ( q || %s <-> j || %s ) )' % (NM, NM))], 'cbvralvw', '( A. q e. Q q || %s <-> A. j e. Q j || %s )' % (NM, NM))
ralj = w.s([ral, w.s([cb], 'a1i', '( %s -> ( A. q e. Q q || %s <-> A. j e. Q j || %s ) )' % (H, NM, NM))], 'mpbid', '( %s -> A. j e. Q j || %s )' % (H, NM))
pd = w.s([w.s([w.s([fin, ss], 'jca', '( %s -> ( Q e. Fin /\\ Q C_ Prime ) )' % H), w.inst('extrwprmdvds')], 'syl', '( %s -> ( ( %s e. ZZ /\\ A. j e. Q j || %s ) -> prod_ j e. Q j || %s ) )' % (H, NM, NM, NM)), w.s([amz, ralj], 'jca', '( %s -> ( %s e. ZZ /\\ A. j e. Q j || %s ) )' % (H, NM, NM))], 'mpd', '( %s -> prod_ j e. Q j || %s )' % (H, NM))
w.qed([lmp, pd], 'eqbrtrd', '( %s -> %s || %s )' % (H, LM, NM))
run(w)

# ------------------------------------------------------------ extrwlamall
w = W('extrwlamall', 'The exponent hypothesis of vebkz for the modulus L and the exponent lambdaL Q (Lean: exponent_dvd_lambdaW as consumed by round_extractW).')
H = 'Q e. %s' % FPP
H2 = '( %s /\\ a e. ZZ )' % H
A3 = '( %s /\\ ( a gcd %s ) = 1 )' % (H2, LM)
q1 = w.s([], 'simpll', '( %s -> Q e. %s )' % (A3, FPP))
az = w.s([], 'simplr', '( %s -> a e. ZZ )' % A3)
gc = w.s([], 'simpr', '( %s -> ( a gcd %s ) = 1 )' % (A3, LM))
lam = w.s([w.s([q1, az, gc], '3jca', '( %s -> ( Q e. %s /\\ a e. ZZ /\\ ( a gcd %s ) = 1 ) )' % (A3, FPP, LM)), w.inst('extrwlam')], 'syl', '( %s -> %s || ( ( a ^ %s ) - 1 ) )' % (A3, LM, LA))
im = w.s([lam], 'ex', '( %s -> ( ( a gcd %s ) = 1 -> %s || ( ( a ^ %s ) - 1 ) ) )' % (H2, LM, LM, LA))
w.qed([im], 'ralrimiva', '( %s -> A. a e. ZZ ( ( a gcd %s ) = 1 -> %s || ( ( a ^ %s ) - 1 ) ) )' % (H, LM, LM, LA))
run(w)

# ------------------------------------------------------------ extrwpcop
w = W('extrwpcop', 'A pool element is coprime to the modulus: it is a prime above z, while every prime of Q is at most z (Lean: pool_coprimeW).')
H = '( ( Q e. %s /\\ Z e. NN0 /\\ K e. NN0 ) /\\ ( A. q e. Q q <_ Z /\\ P e. %s ) )' % (FPP, PL)
q1 = w.s([], 'simpl1', '( %s -> Q e. %s )' % (H, FPP))
zn = w.s([], 'simpl2', '( %s -> Z e. NN0 )' % H)
kn = w.s([], 'simpl3', '( %s -> K e. NN0 )' % H)
qle = w.s([], 'simprl', '( %s -> A. q e. Q q <_ Z )' % H)
pel = w.s([], 'simprr', '( %s -> P e. %s )' % (H, PL))
ss, fin, f0 = fpp(w, H, q1)
lmp = lmodprod(w, H, f0)
lz = w.s([w.s([q1, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (H, LM))], 'nnzd', '( %s -> %s e. ZZ )' % (H, LM))
pe = w.s([w.s([w.s([f0, zn, kn], '3jca', '( %s -> ( Q e. %s /\\ Z e. NN0 /\\ K e. NN0 ) )' % (H, FP0)), pel], 'jca', '( %s -> ( ( Q e. %s /\\ Z e. NN0 /\\ K e. NN0 ) /\\ P e. %s ) )' % (H, FP0, PL)), w.inst('poolel')], 'syl', '( %s -> ( P e. Prime /\\ Z < P /\\ P <_ ( xceil ` Q ) ) )' % H)
pp = w.s([pe], 'simp1d', '( %s -> P e. Prime )' % H)
zlt = w.s([pe], 'simp2d', '( %s -> Z < P )' % H)
# if P || L then P e. Q, so P <_ Z, contradicting Z < P
pdv = w.s([w.s([fin, ss, pp], '3jca', '( %s -> ( Q e. Fin /\\ Q C_ Prime /\\ P e. Prime ) )' % H), w.inst('extrwpdv')], 'syl', '( %s -> ( P || prod_ j e. Q j -> P e. Q ) )' % H)
tolm = w.s([w.s([lmp], 'breq2d', '( %s -> ( P || %s <-> P || prod_ j e. Q j ) )' % (H, LM))], 'biimpd', '( %s -> ( P || %s -> P || prod_ j e. Q j ) )' % (H, LM))
inq = w.s([tolm, pdv], 'syld', '( %s -> ( P || %s -> P e. Q ) )' % (H, LM))
# P e. Q gives P <_ Z
HP = '( %s /\\ P e. Q )' % H
cgp = w.s([w.s([], 'id', '( q = P -> q = P )')], 'breq1d', '( q = P -> ( q <_ Z <-> P <_ Z ) )')
ple = w.s([cgp, w.s([qle], 'adantr', '( %s -> A. q e. Q q <_ Z )' % HP), w.s([], 'simpr', '( %s -> P e. Q )' % HP)], 'rspcdva', '( %s -> P <_ Z )' % HP)
zre = w.s([w.s([zn], 'adantr', '( %s -> Z e. NN0 )' % HP)], 'nn0red', '( %s -> Z e. RR )' % HP)
pnn = w.s([w.s([pp], 'adantr', '( %s -> P e. Prime )' % HP), w.inst('prmnn')], 'syl', '( %s -> P e. NN )' % HP)
pre = w.s([pnn], 'nnred', '( %s -> P e. RR )' % HP)
zltp = w.s([zlt], 'adantr', '( %s -> Z < P )' % HP)
plt = w.s([pre, zre, pre, ple, zltp], 'lelttrd', '( %s -> P < P )' % HP)
nplt = w.s([pre, w.inst('ltnr')], 'syl', '( %s -> -. P < P )' % HP)
nq = w.s([plt, nplt], 'pm2.65da', '( %s -> -. P e. Q )' % H)
ndl = w.s([nq, inq], 'mtod', '( %s -> -. P || %s )' % (H, LM))
cp = w.s([pp, lz, w.inst('coprm')], 'syl2anc', '( %s -> ( -. P || %s <-> ( P gcd %s ) = 1 ) )' % (H, LM, LM))
w.qed([cp, ndl], 'mpbid', '( %s -> ( P gcd %s ) = 1 )' % (H, LM))
run(w)
