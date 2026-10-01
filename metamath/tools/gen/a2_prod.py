"""Sortie A2, batch 6: arithmetic of a product of distinct primes
( L = Lmod Q ): divisibility, the prime-divisor set, squarefreeness, the
bounds 2 ^ T <_ L <_ z ^ T, and the number of divisors."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a2lib import *
only = sys.argv[1:]
def run(w, unify_only=False):
    if only and w.label not in only: return True
    return w.run(unify_only)

FP = '( ~P Prime i^i Fin )'
FN0 = '( ~P NN0 i^i Fin )'
PRQ = 'prod_ q e. Q q'
LM = '( Lmod ` Q )'


def fpparts(w, ante, st):
    """( ante -> Q C_ Prime ), ( ante -> Q e. Fin ), ( ante -> Q e. ( ~P NN0 i^i Fin ) )"""
    b = w.s([st, w.inst('elfpw')], 'sylib', '( %s -> ( Q C_ Prime /\\ Q e. Fin ) )' % ante)
    qs = w.s([b], 'simpld', '( %s -> Q C_ Prime )' % ante)
    qf = w.s([b], 'simprd', '( %s -> Q e. Fin )' % ante)
    pn = w.s([], 'prmssnn', 'Prime C_ NN')
    nn0 = w.s([], 'nnssnn0', 'NN C_ NN0')
    pn0 = w.s([pn, nn0], 'sstri', 'Prime C_ NN0')
    qn0 = w.s([qs, w.s([pn0], 'a1i', '( %s -> Prime C_ NN0 )' % ante)], 'sstrd', '( %s -> Q C_ NN0 )' % ante)
    fn0 = w.s([w.s([qn0, qf], 'jca', '( %s -> ( Q C_ NN0 /\\ Q e. Fin ) )' % ante), w.inst('elfpw')], 'sylibr',
              '( %s -> Q e. %s )' % (ante, FN0))
    nz = w.s([], 'nnssz', 'NN C_ ZZ')
    pz = w.s([pn, nz], 'sstri', 'Prime C_ ZZ')
    qz = w.s([qs, w.s([pz], 'a1i', '( %s -> Prime C_ ZZ )' % ante)], 'sstrd', '( %s -> Q C_ ZZ )' % ante)
    return qs, qf, fn0, qz


# ------------------------------------------------------------- prmproddvds
w = W('prmproddvds', 'Every prime of Q divides the modulus L = Lmod Q (Lean: Finset.dvd_prod_of_mem).')
A = '( Q e. %s /\\ P e. Q )' % FP
qfp = w.s([], 'simpl', '( %s -> Q e. %s )' % (A, FP))
pq = w.s([], 'simpr', '( %s -> P e. Q )' % A)
qs, qf, fn0, qz = fpparts(w, A, qfp)
dv = w.s([qf, qz], 'fproddvdsd', '( %s -> A. x e. Q x || prod_ k e. Q k )' % A)
idx = w.s([], 'id', '( x = P -> x = P )')
cg, _b = w.wcongr('x || prod_ k e. Q k', {'x': 'P'}, 'x = P', {'x': idx})
ins = w.s([cg, dv, pq], 'rspcdva', '( %s -> P || prod_ k e. Q k )' % A)
idk = w.s([], 'id', '( k = q -> k = q )')
cb = w.s([idk], 'cbvprodv', 'prod_ k e. Q k = %s' % PRQ)
cbd = w.s([cb], 'a1i', '( %s -> prod_ k e. Q k = %s )' % (A, PRQ))
ins2 = w.s([ins, cbd], 'breqtrd', '( %s -> P || %s )' % (A, PRQ))
lv = w.s([fn0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (A, LM, PRQ))
w.qed([ins2, w.s([lv], 'eqcomd', '( %s -> %s = %s )' % (A, PRQ, LM))], 'breqtrd', '( %s -> P || %s )' % (A, LM))
run(w)

# --------------------------------------------------------------- prmprodlb
w = W('prmprodlb', '2 ^ ( # Q ) <_ Lmod Q for a finite set of primes (Lean: Step3W.lean hL2T).')
A = 'Q e. %s' % FP
qfp = w.s([], 'id', '( %s -> Q e. %s )' % (A, FP))
qs, qf, fn0, qz = fpparts(w, A, qfp)
nf = w.s([], 'nfv', 'F/ q %s' % A)
B = '( %s /\\ q e. Q )' % A
qin = w.s([], 'simpr', '( %s -> q e. Q )' % B)
qpr = w.s([w.s([qs], 'adantr', '( %s -> Q C_ Prime )' % B), qin], 'sseldd', '( %s -> q e. Prime )' % B)
qnn = w.s([qpr, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % B)
qre = w.s([qnn], 'nnred', '( %s -> q e. RR )' % B)
q2 = w.s([w.s([qpr, w.inst('prmuz2')], 'syl', '( %s -> q e. ( ZZ>= ` 2 ) )' % B), w.inst('eluzle')], 'syl', '( %s -> 2 <_ q )' % B)
r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % B)
z2 = w.s([w.s([], '0le2', '0 <_ 2')], 'a1i', '( %s -> 0 <_ 2 )' % B)
fl = w.s([nf, qf, r2, z2, qre, q2], 'fprodle', '( %s -> prod_ q e. Q 2 <_ %s )' % (A, PRQ))
c2 = w.s([], '2cn', '2 e. CC')
fc = w.s([qf, w.s([c2], 'a1i', '( %s -> 2 e. CC )' % A), w.inst('fprodconst')], 'syl2anc',
         '( %s -> prod_ q e. Q 2 = ( 2 ^ ( # ` Q ) ) )' % A)
fl2 = w.s([w.s([fc], 'eqcomd', '( %s -> ( 2 ^ ( # ` Q ) ) = prod_ q e. Q 2 )' % A), fl], 'eqbrtrd',
          '( %s -> ( 2 ^ ( # ` Q ) ) <_ %s )' % (A, PRQ))
lv = w.s([fn0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (A, LM, PRQ))
w.qed([fl2, w.s([lv], 'eqcomd', '( %s -> %s = %s )' % (A, PRQ, LM))], 'breqtrd', '( %s -> ( 2 ^ ( # ` Q ) ) <_ %s )' % (A, LM))
run(w)

# --------------------------------------------------------------- prmprodub
w = W('prmprodub', 'Lmod Q <_ Z ^ ( # Q ) when every prime of Q is at most Z (Lean: Step3W.lean hLzT).')
A = '( Q e. %s /\\ Z e. NN0 /\\ A. p e. Q p <_ Z )' % FP
qfp = w.s([], 'simp1', '( %s -> Q e. %s )' % (A, FP))
zn0 = w.s([], 'simp2', '( %s -> Z e. NN0 )' % A)
hle = w.s([], 'simp3', '( %s -> A. p e. Q p <_ Z )' % A)
qs, qf, fn0, qz = fpparts(w, A, qfp)
nf = w.s([], 'nfv', 'F/ q %s' % A)
B = '( %s /\\ q e. Q )' % A
qin = w.s([], 'simpr', '( %s -> q e. Q )' % B)
qpr = w.s([w.s([qs], 'adantr', '( %s -> Q C_ Prime )' % B), qin], 'sseldd', '( %s -> q e. Prime )' % B)
qnn = w.s([qpr, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % B)
qre = w.s([qnn], 'nnred', '( %s -> q e. RR )' % B)
qge0 = w.s([w.s([qnn], 'nnnn0d', '( %s -> q e. NN0 )' % B)], 'nn0ge0d', '( %s -> 0 <_ q )' % B)
zre = w.s([w.s([zn0], 'nn0red', '( %s -> Z e. RR )' % A)], 'adantr', '( %s -> Z e. RR )' % B)
idp = w.s([], 'id', '( p = q -> p = q )')
cg, _b = w.wcongr('p <_ Z', {'p': 'q'}, 'p = q', {'p': idp})
ins = w.s([cg, w.s([hle], 'adantr', '( %s -> A. p e. Q p <_ Z )' % B), qin], 'rspcdva', '( %s -> q <_ Z )' % B)
fl = w.s([nf, qf, qre, qge0, zre, ins], 'fprodle', '( %s -> %s <_ prod_ q e. Q Z )' % (A, PRQ))
zcn = w.s([zn0], 'nn0cnd', '( %s -> Z e. CC )' % A)
fc = w.s([qf, zcn, w.inst('fprodconst')], 'syl2anc', '( %s -> prod_ q e. Q Z = ( Z ^ ( # ` Q ) ) )' % A)
fl2 = w.s([fl, fc], 'breqtrd', '( %s -> %s <_ ( Z ^ ( # ` Q ) ) )' % (A, PRQ))
lv = w.s([fn0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (A, LM, PRQ))
w.qed([lv, fl2], 'eqbrtrd', '( %s -> %s <_ ( Z ^ ( # ` Q ) ) )' % (A, LM))
run(w)

# ------------------------------------------------------- prmprodset (induction)
SET = lambda P: '{ p e. Prime | p || %s }' % P
PRV = lambda v: 'prod_ q e. %s q' % v
PH = lambda v: '( %s C_ Prime -> %s = %s )' % (v, SET(PRV(v)), v)

w = W('prmprodsetb', 'Base case: no prime divides the empty product.')
A = '(/) C_ Prime'
p0 = w.s([], 'prod0', '%s = 1' % PRV('(/)'))
p0d = w.s([p0], 'a1i', '( %s -> %s = 1 )' % (A, PRV('(/)')))
E = '( %s /\\ p e. Prime )' % A
br = w.s([w.s([p0d], 'adantr', '( %s -> %s = 1 )' % (E, PRV('(/)')))], 'breq2d',
         '( %s -> ( p || %s <-> p || 1 ) )' % (E, PRV('(/)')))
rb = w.s([br], 'rabbidva', '( %s -> %s = %s )' % (A, SET(PRV('(/)')), SET('1')))
nd = w.s([], 'nprmdvds1', '( p e. Prime -> -. p || 1 )')
rg = w.s([nd], 'rgen', 'A. p e. Prime -. p || 1')
e0 = w.s([rg, w.inst('rabeq0')], 'mpbir', '%s = (/)' % SET('1'))
w.qed([rb, w.s([e0], 'a1i', '( %s -> %s = (/) )' % (A, SET('1')))], 'eqtrd', PH('(/)'))
run(w)

w = W('prmprodnn', 'A product of distinct primes is a positive integer.')
A = 'Q e. %s' % FP
qfp = w.s([], 'id', '( %s -> Q e. %s )' % (A, FP))
qs, qf, fn0, qz = fpparts(w, A, qfp)
cl = w.s([qfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (A, LM))
lv = w.s([fn0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (A, LM, PRQ))
w.qed([lv, cl], 'eqeltrrd', '( %s -> %s e. NN )' % (A, PRQ))
run(w)

w = W('prmprodsplit', 'Adjoining a prime to Q multiplies the product by it.')
A = '( Q e. %s /\\ P e. Prime /\\ -. P e. Q )' % FP
QP = '( Q u. { P } )'
qfp = w.s([], 'simp1', '( %s -> Q e. %s )' % (A, FP))
ppr = w.s([], 'simp2', '( %s -> P e. Prime )' % A)
pnot = w.s([], 'simp3', '( %s -> -. P e. Q )' % A)
qs, qf, fn0, qz = fpparts(w, A, qfp)
pnn = w.s([ppr, w.inst('prmnn')], 'syl', '( %s -> P e. NN )' % A)
pcn = w.s([pnn], 'nncnd', '( %s -> P e. CC )' % A)
pex = w.s([pnn, w.inst('elex')], 'syl', '( %s -> P e. _V )' % A)
dj = w.s([pnot, w.inst('disjsn')], 'sylibr', '( %s -> ( Q i^i { P } ) = (/) )' % A)
ueqd = w.s([w.s([], 'eqid', '%s = %s' % (QP, QP))], 'a1i', '( %s -> %s = %s )' % (A, QP, QP))
snf = w.s([w.s([], 'snfi', '{ P } e. Fin')], 'a1i', '( %s -> { P } e. Fin )' % A)
qpfin = w.s([qf, snf, w.inst('unfi')], 'syl2anc', '( %s -> %s e. Fin )' % (A, QP))
C = '( %s /\\ q e. %s )' % (A, QP)
qyz = w.s([], 'simpr', '( %s -> q e. %s )' % (C, QP))
qpsub = w.s([qs, w.s([ppr, w.inst('snssi')], 'syl', '( %s -> { P } C_ Prime )' % A)], 'unssd', '( %s -> %s C_ Prime )' % (A, QP))
qpr2 = w.s([w.s([qpsub], 'adantr', '( %s -> %s C_ Prime )' % (C, QP)), qyz], 'sseldd', '( %s -> q e. Prime )' % C)
qcn = w.s([w.s([qpr2, w.inst('prmnn')], 'syl', '( %s -> q e. NN )' % C)], 'nncnd', '( %s -> q e. CC )' % C)
spl = w.s([dj, ueqd, qpfin, qcn], 'fprodsplit', '( %s -> prod_ q e. %s q = ( %s x. prod_ q e. { P } q ) )' % (A, QP, PRQ))
idq = w.s([], 'id', '( q = P -> q = P )')
ps = w.s([idq], 'prodsn', '( ( P e. _V /\\ P e. CC ) -> prod_ q e. { P } q = P )')
psd = w.s([pex, pcn, ps], 'syl2anc', '( %s -> prod_ q e. { P } q = P )' % A)
w.qed([spl, w.s([psd], 'oveq2d', '( %s -> ( %s x. prod_ q e. { P } q ) = ( %s x. P ) )' % (A, PRQ, PRQ))], 'eqtrd',
      '( %s -> prod_ q e. %s q = ( %s x. P ) )' % (A, QP, PRQ))
run(w)

w = W('rabdvdseq', 'The set of prime divisors depends only on the number.')
b = w.s([], 'breq2', '( A = B -> ( p || A <-> p || B ) )')
w.qed([b], 'rabbidv', '( A = B -> %s = %s )' % (SET('A'), SET('B')))
run(w)

w = W('prmprodsetlem', 'Induction step: adjoining a new prime to Q adjoins it to the set of prime divisors of the product.')
PY = PRV('y'); YZ = '( y u. { z } )'; PYZ = PRV(YZ); PZ = '( %s x. z )' % PY
SEQY = '%s = y' % SET(PY)
A = '( ( y e. Fin /\\ -. z e. y ) /\\ ( y C_ Prime -> %s ) /\\ %s C_ Prime )' % (SEQY, YZ)
fz = w.s([], 'simp1', '( %s -> ( y e. Fin /\\ -. z e. y ) )' % A)
yfin = w.s([fz], 'simpld', '( %s -> y e. Fin )' % A)
znot = w.s([fz], 'simprd', '( %s -> -. z e. y )' % A)
ih = w.s([], 'simp2', '( %s -> ( y C_ Prime -> %s ) )' % (A, SEQY))
yzs = w.s([], 'simp3', '( %s -> %s C_ Prime )' % (A, YZ))
ys = w.s([yzs], 'unssad', '( %s -> y C_ Prime )' % A)
zss = w.s([yzs], 'unssbd', '( %s -> { z } C_ Prime )' % A)
zex = w.s([], 'vex', 'z e. _V')
zexd = w.s([zex], 'a1i', '( %s -> z e. _V )' % A)
zpr = w.s([zss, w.s([zexd, w.inst('snssg')], 'syl', '( %s -> ( z e. Prime <-> { z } C_ Prime ) )' % A)], 'mpbird',
          '( %s -> z e. Prime )' % A)
seqy = w.s([ys, ih], 'mpd', '( %s -> %s )' % (A, SEQY))
yfp = w.s([w.s([ys, yfin], 'jca', '( %s -> ( y C_ Prime /\\ y e. Fin ) )' % A), w.inst('elfpw')], 'sylibr',
          '( %s -> y e. %s )' % (A, FP))
pynn = w.s([yfp, w.inst('prmprodnn')], 'syl', '( %s -> %s e. NN )' % (A, PY))
pyz_ = w.s([pynn], 'nnzd', '( %s -> %s e. ZZ )' % (A, PY))
znn = w.s([zpr, w.inst('prmnn')], 'syl', '( %s -> z e. NN )' % A)
zz_ = w.s([znn], 'nnzd', '( %s -> z e. ZZ )' % A)
spl2 = w.s([w.s([yfp, zpr, znot], '3jca', '( %s -> ( y e. %s /\\ z e. Prime /\\ -. z e. y ) )' % (A, FP)),
            w.inst('prmprodsplit')], 'syl', '( %s -> %s = %s )' % (A, PYZ, PZ))
# { p e. Prime | p || ( PY x. z ) } = y u. { z }
idp = w.s([], 'id', '( p = r -> p = r )')
cgl, _b = w.wcongr('p || %s' % PZ, {'p': 'r'}, 'p = r', {'p': idp})
ell = w.s([cgl], 'elrab', '( r e. %s <-> ( r e. Prime /\\ r || %s ) )' % (SET(PZ), PZ))
elld = w.s([ell], 'a1i', '( %s -> ( r e. %s <-> ( r e. Prime /\\ r || %s ) ) )' % (A, SET(PZ), PZ))
elu = w.s([], 'elun', '( r e. %s <-> ( r e. y \\/ r e. { z } ) )' % YZ)
vs = w.s([], 'velsn', '( r e. { z } <-> r = z )')
elu2 = w.s([w.s([vs], 'orbi2i', '( ( r e. y \\/ r e. { z } ) <-> ( r e. y \\/ r = z ) )')], 'bitri' if False else 'a1i', '( %s -> ( ( r e. y \\/ r e. { z } ) <-> ( r e. y \\/ r = z ) ) )' % A)
elud = w.s([w.s([elu], 'a1i', '( %s -> ( r e. %s <-> ( r e. y \\/ r e. { z } ) ) )' % (A, YZ)), elu2], 'bitrd',
           '( %s -> ( r e. %s <-> ( r e. y \\/ r = z ) ) )' % (A, YZ))
# forward
E = '( %s /\\ ( r e. Prime /\\ r || %s ) )' % (A, PZ)
rp = w.s([], 'simprl', '( %s -> r e. Prime )' % E)
rd = w.s([], 'simprr', '( %s -> r || %s )' % (E, PZ))
eu = w.s([rp, w.s([pyz_], 'adantr', '( %s -> %s e. ZZ )' % (E, PY)), w.s([zz_], 'adantr', '( %s -> z e. ZZ )' % E),
          w.inst('euclemma')], 'syl3anc', '( %s -> ( r || %s <-> ( r || %s \\/ r || z ) ) )' % (E, PZ, PY))
or1 = w.s([rd, eu], 'mpbid', '( %s -> ( r || %s \\/ r || z ) )' % (E, PY))
cgl2, _b2 = w.wcongr('p || %s' % PY, {'p': 'r'}, 'p = r', {'p': idp})
elp = w.s([cgl2], 'elrab', '( r e. %s <-> ( r e. Prime /\\ r || %s ) )' % (SET(PY), PY))
E1 = '( %s /\\ r || %s )' % (E, PY)
m1 = w.s([w.s([w.s([rp], 'adantr', '( %s -> r e. Prime )' % E1), w.s([], 'simpr', '( %s -> r || %s )' % (E1, PY))], 'jca',
             '( %s -> ( r e. Prime /\\ r || %s ) )' % (E1, PY)),
          w.s([elp], 'a1i', '( %s -> ( r e. %s <-> ( r e. Prime /\\ r || %s ) ) )' % (E1, SET(PY), PY))], 'mpbird',
         '( %s -> r e. %s )' % (E1, SET(PY)))
m1y = w.s([m1, w.s([seqy], 'ad2antrr', '( %s -> %s )' % (E1, SEQY))], 'eleqtrd', '( %s -> r e. y )' % E1)
o1 = w.s([m1y], 'orcd', '( %s -> ( r e. y \\/ r = z ) )' % E1)
E2 = '( %s /\\ r || z )' % E
ruz = w.s([w.s([rp], 'adantr', '( %s -> r e. Prime )' % E2), w.inst('prmuz2')], 'syl', '( %s -> r e. ( ZZ>= ` 2 ) )' % E2)
dp = w.s([ruz, w.s([zpr], 'ad2antrr', '( %s -> z e. Prime )' % E2), w.inst('dvdsprm')], 'syl2anc',
         '( %s -> ( r || z <-> r = z ) )' % E2)
rez = w.s([w.s([], 'simpr', '( %s -> r || z )' % E2), dp], 'mpbid', '( %s -> r = z )' % E2)
o2 = w.s([rez], 'olcd', '( %s -> ( r e. y \\/ r = z ) )' % E2)
fwd0 = w.s([o1, o2], 'jaodan', '( ( %s /\\ ( r || %s \\/ r || z ) ) -> ( r e. y \\/ r = z ) )' % (E, PY))
fwd = w.s([or1, fwd0], 'mpdan', '( %s -> ( r e. y \\/ r = z ) )' % E)
# backward
F = '( %s /\\ ( r e. y \\/ r = z ) )' % A
F1 = '( %s /\\ r e. y )' % A
ry = w.s([], 'simpr', '( %s -> r e. y )' % F1)
rset = w.s([ry, w.s([seqy], 'adantr', '( %s -> %s )' % (F1, SEQY))], 'eleqtrrd', '( %s -> r e. %s )' % (F1, SET(PY)))
rb2 = w.s([rset, w.s([elp], 'a1i', '( %s -> ( r e. %s <-> ( r e. Prime /\\ r || %s ) ) )' % (F1, SET(PY), PY))], 'mpbid',
          '( %s -> ( r e. Prime /\\ r || %s ) )' % (F1, PY))
rp1 = w.s([rb2], 'simpld', '( %s -> r e. Prime )' % F1)
rd1 = w.s([rb2], 'simprd', '( %s -> r || %s )' % (F1, PY))
rz1 = w.s([rp1, w.inst('prmz')], 'syl', '( %s -> r e. ZZ )' % F1)
dm = w.s([rz1, w.s([pyz_], 'adantr', '( %s -> %s e. ZZ )' % (F1, PY)), w.s([zz_], 'adantr', '( %s -> z e. ZZ )' % F1),
          w.inst('dvdsmultr1')], 'syl3anc', '( %s -> ( r || %s -> r || %s ) )' % (F1, PY, PZ))
rdz = w.s([rd1, dm], 'mpd', '( %s -> r || %s )' % (F1, PZ))
b1 = w.s([rp1, rdz], 'jca', '( %s -> ( r e. Prime /\\ r || %s ) )' % (F1, PZ))
F2 = '( %s /\\ r = z )' % A
rzq = w.s([], 'simpr', '( %s -> r = z )' % F2)
rp2 = w.s([rzq, w.s([zpr], 'adantr', '( %s -> z e. Prime )' % F2)], 'eqeltrd', '( %s -> r e. Prime )' % F2)
dm2 = w.s([w.s([pyz_], 'adantr', '( %s -> %s e. ZZ )' % (F2, PY)), w.s([zz_], 'adantr', '( %s -> z e. ZZ )' % F2),
           w.inst('dvdsmul2')], 'syl2anc', '( %s -> z || %s )' % (F2, PZ))
rdz2 = w.s([w.s([rzq], 'breq1d', '( %s -> ( r || %s <-> z || %s ) )' % (F2, PZ, PZ)), dm2], 'mpbird', '( %s -> r || %s )' % (F2, PZ))
b2 = w.s([rp2, rdz2], 'jca', '( %s -> ( r e. Prime /\\ r || %s ) )' % (F2, PZ))
bwd = w.s([b1, b2], 'jaodan', '( %s -> ( r e. Prime /\\ r || %s ) )' % (F, PZ))
bi = w.s([fwd, bwd], 'impbida', '( %s -> ( ( r e. Prime /\\ r || %s ) <-> ( r e. y \\/ r = z ) ) )' % (A, PZ))
bi2 = w.s([elld, bi], 'bitrd', '( %s -> ( r e. %s <-> ( r e. y \\/ r = z ) ) )' % (A, SET(PZ)))
bi3 = w.s([bi2, w.s([elud], 'bicomd', '( %s -> ( ( r e. y \\/ r = z ) <-> r e. %s ) )' % (A, YZ))], 'bitrd',
          '( %s -> ( r e. %s <-> r e. %s ) )' % (A, SET(PZ), YZ))
eq1 = w.s([bi3], 'eqrdv', '( %s -> %s = %s )' % (A, SET(PZ), YZ))
# rewrite back to the product over y u. { z }
rw2 = w.s([spl2, w.inst('rabdvdseq')], 'syl', '( %s -> %s = %s )' % (A, SET(PYZ), SET(PZ)))
w.qed([rw2, eq1], 'eqtrd', '( %s -> %s = %s )' % (A, SET(PYZ), YZ))
run(w)

w = W('prmprodsetv', 'The prime divisors of the product over a finite set of primes are exactly that set (induction on the set).')
YZ = '( y u. { z } )'
idv = w.s([], 'id', '( v = (/) -> v = (/) )')
c1, _b = w.wcongr(PH('v'), {'v': '(/)'}, 'v = (/)', {'v': idv})
idv2 = w.s([], 'id', '( v = y -> v = y )')
c2, _b = w.wcongr(PH('v'), {'v': 'y'}, 'v = y', {'v': idv2})
idv3 = w.s([], 'id', '( v = %s -> v = %s )' % (YZ, YZ))
c3, _b = w.wcongr(PH('v'), {'v': YZ}, 'v = %s' % YZ, {'v': idv3})
idv4 = w.s([], 'id', '( v = Q -> v = Q )')
c4, _b = w.wcongr(PH('v'), {'v': 'Q'}, 'v = Q', {'v': idv4})
base = w.s([], 'prmprodsetb', PH('(/)'))
stp = w.s([], 'prmprodsetlem', '( ( ( y e. Fin /\\ -. z e. y ) /\\ %s /\\ %s C_ Prime ) -> %s = %s )' % (PH('y'), YZ, SET(PRV(YZ)), YZ))
stp3 = w.s([stp], '3exp', '( ( y e. Fin /\\ -. z e. y ) -> ( %s -> %s ) )' % (PH('y'), PH(YZ)))
w.qed([c1, c2, c3, c4, base, stp3], 'findcard2s', '( Q e. Fin -> %s )' % PH('Q'))
run(w)

w = W('prmprodset', 'The set of prime divisors of L = Lmod Q is Q (Lean: Nat.primeFactors_prod, Step3W.lean hPF).')
A = 'Q e. %s' % FP
qfp = w.s([], 'id', '( %s -> Q e. %s )' % (A, FP))
qs, qf, fn0, qz = fpparts(w, A, qfp)
ind = w.s([qf, w.inst('prmprodsetv')], 'syl', '( %s -> %s )' % (A, PH('Q')))
eq = w.s([qs, ind], 'mpd', '( %s -> %s = Q )' % (A, SET(PRQ)))
lv = w.s([fn0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (A, LM, PRQ))
rw = w.s([lv, w.inst('rabdvdseq')], 'syl', '( %s -> %s = %s )' % (A, SET(LM), SET(PRQ)))
w.qed([rw, eq], 'eqtrd', '( %s -> %s = Q )' % (A, SET(LM)))
run(w)

w = W('prmprodndvds', 'A prime outside Q does not divide the product over Q.')
A = '( Q e. %s /\\ P e. Prime /\\ -. P e. Q )' % FP
qfp = w.s([], 'simp1', '( %s -> Q e. %s )' % (A, FP))
ppr = w.s([], 'simp2', '( %s -> P e. Prime )' % A)
pnot = w.s([], 'simp3', '( %s -> -. P e. Q )' % A)
qs, qf, fn0, qz = fpparts(w, A, qfp)
eq = w.s([qfp, w.inst('prmprodset')], 'syl', '( %s -> %s = Q )' % (A, SET(LM)))
lv = w.s([fn0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (A, LM, PRQ))
rw = w.s([lv, w.inst('rabdvdseq')], 'syl', '( %s -> %s = %s )' % (A, SET(LM), SET(PRQ)))
eq2 = w.s([w.s([rw], 'eqcomd', '( %s -> %s = %s )' % (A, SET(PRQ), SET(LM))), eq], 'eqtrd', '( %s -> %s = Q )' % (A, SET(PRQ)))
idp = w.s([], 'id', '( p = P -> p = P )')
cg, _b = w.wcongr('p || %s' % PRQ, {'p': 'P'}, 'p = P', {'p': idp})
el = w.s([cg], 'elrab', '( P e. %s <-> ( P e. Prime /\\ P || %s ) )' % (SET(PRQ), PRQ))
B = '( %s /\\ P || %s )' % (A, PRQ)
mem = w.s([w.s([w.s([ppr], 'adantr', '( %s -> P e. Prime )' % B), w.s([], 'simpr', '( %s -> P || %s )' % (B, PRQ))], 'jca',
              '( %s -> ( P e. Prime /\\ P || %s ) )' % (B, PRQ)),
           w.s([el], 'a1i', '( %s -> ( P e. %s <-> ( P e. Prime /\\ P || %s ) ) )' % (B, SET(PRQ), PRQ))], 'mpbird',
          '( %s -> P e. %s )' % (B, SET(PRQ)))
inq = w.s([mem, w.s([eq2], 'adantr', '( %s -> %s = Q )' % (B, SET(PRQ)))], 'eleqtrd', '( %s -> P e. Q )' % B)
w.qed([inq, pnot], 'mtand', '( %s -> -. P || %s )' % (A, PRQ))
run(w)

SQ = lambda v: '( %s C_ Prime -> ( mmu ` %s ) =/= 0 )' % (v, PRV(v))

w = W('sqf1', '1 is squarefree.')
B = '( p e. Prime /\\ ( p ^ 2 ) || 1 )'
pnn = w.s([w.s([], 'simpl', '( %s -> p e. Prime )' % B), w.inst('prmnn')], 'syl', '( %s -> p e. NN )' % B)
pz = w.s([pnn], 'nnzd', '( %s -> p e. ZZ )' % B)
sv = w.s([w.s([pnn], 'nncnd', '( %s -> p e. CC )' % B)], 'sqvald', '( %s -> ( p ^ 2 ) = ( p x. p ) )' % B)
dm = w.s([pz, pz, w.inst('dvdsmul2')], 'syl2anc', '( %s -> p || ( p x. p ) )' % B)
dm2 = w.s([dm, w.s([sv], 'eqcomd', '( %s -> ( p x. p ) = ( p ^ 2 ) )' % B)], 'breqtrd', '( %s -> p || ( p ^ 2 ) )' % B)
d1 = w.s([], 'simpr', '( %s -> ( p ^ 2 ) || 1 )' % B)
sqz = w.s([pz, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % B)], 'zexpcld', '( %s -> ( p ^ 2 ) e. ZZ )' % B)
one = w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % B)
tr = w.s([pz, sqz, one, w.inst('dvdstr')], 'syl3anc', '( %s -> ( ( p || ( p ^ 2 ) /\\ ( p ^ 2 ) || 1 ) -> p || 1 ) )' % B)
p1 = w.s([tr, w.s([dm2, d1], 'jca', '( %s -> ( p || ( p ^ 2 ) /\\ ( p ^ 2 ) || 1 ) )' % B)], 'mpd', '( %s -> p || 1 )' % B)
np = w.s([w.s([], 'simpl', '( %s -> p e. Prime )' % B), w.inst('nprmdvds1')], 'syl', '( %s -> -. p || 1 )' % B)
nt = w.s([p1, np], 'pm2.65da', '( p e. Prime -> -. ( p ^ 2 ) || 1 )')
rg = w.s([nt], 'rgen', 'A. p e. Prime -. ( p ^ 2 ) || 1')
nex = w.s([rg, w.inst('ralnex')], 'mpbi', '-. E. p e. Prime ( p ^ 2 ) || 1')
ins = w.s([w.s([], '1nn', '1 e. NN'), w.inst('isnsqf')], 'ax-mp', '( ( mmu ` 1 ) = 0 <-> E. p e. Prime ( p ^ 2 ) || 1 )')
n0 = w.s([nex, ins], 'mtbir', '-. ( mmu ` 1 ) = 0')
w.qed([n0, w.inst('df-ne')], 'mpbir', '( mmu ` 1 ) =/= 0')
run(w)

w = W('prmprodsqfb', 'Base case: the empty product 1 is squarefree.')
A = '(/) C_ Prime'
p0 = w.s([], 'prod0', '%s = 1' % PRV('(/)'))
fe = w.s([p0], 'fveq2i', '( mmu ` %s ) = ( mmu ` 1 )' % PRV('(/)'))
s1 = w.s([], 'sqf1', '( mmu ` 1 ) =/= 0')
ne = w.s([fe, s1], 'eqnetri', '( mmu ` %s ) =/= 0' % PRV('(/)'))
w.qed([ne], 'a1i', SQ('(/)'))
run(w)

w = W('prmprodsqflem', 'Induction step: adjoining a new prime keeps the product squarefree.')
PY = PRV('y'); YZ = '( y u. { z } )'; PYZ = PRV(YZ); PZ = '( %s x. z )' % PY
SQY = '( mmu ` %s ) =/= 0' % PY
A = '( ( y e. Fin /\\ -. z e. y ) /\\ %s /\\ %s C_ Prime )' % (SQ('y'), YZ)
fz = w.s([], 'simp1', '( %s -> ( y e. Fin /\\ -. z e. y ) )' % A)
yfin = w.s([fz], 'simpld', '( %s -> y e. Fin )' % A)
znot = w.s([fz], 'simprd', '( %s -> -. z e. y )' % A)
ih = w.s([], 'simp2', '( %s -> %s )' % (A, SQ('y')))
yzs = w.s([], 'simp3', '( %s -> %s C_ Prime )' % (A, YZ))
ys = w.s([yzs], 'unssad', '( %s -> y C_ Prime )' % A)
zss = w.s([yzs], 'unssbd', '( %s -> { z } C_ Prime )' % A)
zexd = w.s([w.s([], 'vex', 'z e. _V')], 'a1i', '( %s -> z e. _V )' % A)
zpr = w.s([zss, w.s([zexd, w.inst('snssg')], 'syl', '( %s -> ( z e. Prime <-> { z } C_ Prime ) )' % A)], 'mpbird',
          '( %s -> z e. Prime )' % A)
sqy = w.s([ys, ih], 'mpd', '( %s -> %s )' % (A, SQY))
yfp = w.s([w.s([ys, yfin], 'jca', '( %s -> ( y C_ Prime /\\ y e. Fin ) )' % A), w.inst('elfpw')], 'sylibr', '( %s -> y e. %s )' % (A, FP))
j3 = w.s([yfp, zpr, znot], '3jca', '( %s -> ( y e. %s /\\ z e. Prime /\\ -. z e. y ) )' % (A, FP))
spl = w.s([j3, w.inst('prmprodsplit')], 'syl', '( %s -> %s = %s )' % (A, PYZ, PZ))
pynn = w.s([yfp, w.inst('prmprodnn')], 'syl', '( %s -> %s e. NN )' % (A, PY))
pyz_ = w.s([pynn], 'nnzd', '( %s -> %s e. ZZ )' % (A, PY))
znn = w.s([zpr, w.inst('prmnn')], 'syl', '( %s -> z e. NN )' % A)
zz_ = w.s([znn], 'nnzd', '( %s -> z e. ZZ )' % A)
nd = w.s([j3, w.inst('prmprodndvds')], 'syl', '( %s -> -. z || %s )' % (A, PY))
cop = w.s([nd, w.s([zpr, pyz_, w.inst('coprm')], 'syl2anc', '( %s -> ( -. z || %s <-> ( z gcd %s ) = 1 ) )' % (A, PY, PY))], 'mpbid',
          '( %s -> ( z gcd %s ) = 1 )' % (A, PY))
gc = w.s([zz_, pyz_, w.inst('gcdcom')], 'syl2anc', '( %s -> ( z gcd %s ) = ( %s gcd z ) )' % (A, PY, PY))
cop2 = w.s([w.s([gc], 'eqcomd', '( %s -> ( %s gcd z ) = ( z gcd %s ) )' % (A, PY, PY)), cop], 'eqtrd', '( %s -> ( %s gcd z ) = 1 )' % (A, PY))
sqz = w.s([zpr, w.inst('sqfprm')], 'syl', '( %s -> ( mmu ` z ) =/= 0 )' % A)
p1 = w.s([pynn, znn, cop2], '3jca', '( %s -> ( %s e. NN /\\ z e. NN /\\ ( %s gcd z ) = 1 ) )' % (A, PY, PY))
p2 = w.s([sqy, sqz], 'jca', '( %s -> ( %s /\\ ( mmu ` z ) =/= 0 ) )' % (A, SQY))
mm = w.s([p1, p2, w.inst('mumullem2')], 'syl2anc', '( %s -> ( mmu ` %s ) =/= 0 )' % (A, PZ))
fe = w.s([spl], 'fveq2d', '( %s -> ( mmu ` %s ) = ( mmu ` %s ) )' % (A, PYZ, PZ))
w.qed([fe, mm], 'eqnetrd', '( %s -> ( mmu ` %s ) =/= 0 )' % (A, PYZ))
run(w)

w = W('prmprodsqfv', 'A product of distinct primes is squarefree (induction on the set).')
YZ = '( y u. { z } )'
idv = w.s([], 'id', '( v = (/) -> v = (/) )')
c1, _b = w.wcongr(SQ('v'), {'v': '(/)'}, 'v = (/)', {'v': idv})
idv2 = w.s([], 'id', '( v = y -> v = y )')
c2, _b = w.wcongr(SQ('v'), {'v': 'y'}, 'v = y', {'v': idv2})
idv3 = w.s([], 'id', '( v = %s -> v = %s )' % (YZ, YZ))
c3, _b = w.wcongr(SQ('v'), {'v': YZ}, 'v = %s' % YZ, {'v': idv3})
idv4 = w.s([], 'id', '( v = Q -> v = Q )')
c4, _b = w.wcongr(SQ('v'), {'v': 'Q'}, 'v = Q', {'v': idv4})
base = w.s([], 'prmprodsqfb', SQ('(/)'))
stp = w.s([], 'prmprodsqflem', '( ( ( y e. Fin /\\ -. z e. y ) /\\ %s /\\ %s C_ Prime ) -> ( mmu ` %s ) =/= 0 )' % (SQ('y'), YZ, PRV(YZ)))
stp3 = w.s([stp], '3exp', '( ( y e. Fin /\\ -. z e. y ) -> ( %s -> %s ) )' % (SQ('y'), SQ(YZ)))
w.qed([c1, c2, c3, c4, base, stp3], 'findcard2s', '( Q e. Fin -> %s )' % SQ('Q'))
run(w)

w = W('prmprodsqf', 'L = Lmod Q is squarefree (Lean: prod_primes_squarefree of Step3W.lean).')
A = 'Q e. %s' % FP
qfp = w.s([], 'id', '( %s -> Q e. %s )' % (A, FP))
qs, qf, fn0, qz = fpparts(w, A, qfp)
ind = w.s([qf, w.inst('prmprodsqfv')], 'syl', '( %s -> %s )' % (A, SQ('Q')))
ne = w.s([qs, ind], 'mpd', '( %s -> ( mmu ` %s ) =/= 0 )' % (A, PRQ))
lv = w.s([fn0, w.inst('lmodqval')], 'syl', '( %s -> %s = %s )' % (A, LM, PRQ))
w.qed([w.s([lv], 'fveq2d', '( %s -> ( mmu ` %s ) = ( mmu ` %s ) )' % (A, LM, PRQ)), ne], 'eqnetrd',
      '( %s -> ( mmu ` %s ) =/= 0 )' % (A, LM))
run(w)

# ------------------------------------------------- divisors of a squarefree L
DIVM = lambda L: '{ m e. ( 1 ... %s ) | m || %s }' % (L, L)
DIVN = lambda L: '{ m e. NN | m || %s }' % L
SQDIV = lambda L: '{ m e. NN | ( ( mmu ` m ) =/= 0 /\\ m || %s ) }' % L
PRD = lambda L: '{ p e. Prime | p || %s }' % L

w = W('divsetfi', 'The set of divisors of L is finite.')
fz = w.s([], 'fzfi', '( 1 ... L ) e. Fin')
w.qed([fz, w.inst('rabfi')], 'ax-mp', '%s e. Fin' % DIVM('L'))
run(w)

w = W('divsetnn', 'The divisors of L in ( 1 ... L ) are all the positive divisors (Lean: Nat.divisors).')
A = 'L e. NN'
idm = w.s([], 'id', '( m = d -> m = d )')
cg1, _b = w.wcongr('m || L', {'m': 'd'}, 'm = d', {'m': idm})
e1 = w.s([cg1], 'elrab', '( d e. %s <-> ( d e. ( 1 ... L ) /\\ d || L ) )' % DIVM('L'))
e2 = w.s([cg1], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || L ) )' % DIVN('L'))
B = '( %s /\\ ( d e. ( 1 ... L ) /\\ d || L ) )' % A
dfz = w.s([], 'simprl', '( %s -> d e. ( 1 ... L ) )' % B)
dnn = w.s([dfz, w.inst('elfznn')], 'syl', '( %s -> d e. NN )' % B)
fwd = w.s([dnn, w.s([], 'simprr', '( %s -> d || L )' % B)], 'jca', '( %s -> ( d e. NN /\\ d || L ) )' % B)
C = '( %s /\\ ( d e. NN /\\ d || L ) )' % A
dnn2 = w.s([], 'simprl', '( %s -> d e. NN )' % C)
ddv = w.s([], 'simprr', '( %s -> d || L )' % C)
lnn = w.s([], 'simpl', '( %s -> L e. NN )' % C)
dle = w.s([ddv, w.s([w.s([dnn2], 'nnzd', '( %s -> d e. ZZ )' % C), lnn, w.inst('dvdsle')], 'syl2anc',
                    '( %s -> ( d || L -> d <_ L ) )' % C)], 'mpd', '( %s -> d <_ L )' % C)
fzb = w.s([w.s([lnn], 'nnzd', '( %s -> L e. ZZ )' % C), w.inst('fznn')], 'syl',
          '( %s -> ( d e. ( 1 ... L ) <-> ( d e. NN /\\ d <_ L ) ) )' % C)
dfz2 = w.s([w.s([dnn2, dle], 'jca', '( %s -> ( d e. NN /\\ d <_ L ) )' % C), fzb], 'mpbird', '( %s -> d e. ( 1 ... L ) )' % C)
bwd = w.s([dfz2, ddv], 'jca', '( %s -> ( d e. ( 1 ... L ) /\\ d || L ) )' % C)
bi = w.s([fwd, bwd], 'impbida', '( %s -> ( ( d e. ( 1 ... L ) /\\ d || L ) <-> ( d e. NN /\\ d || L ) ) )' % A)
b1 = w.s([w.s([e1], 'a1i', '( %s -> ( d e. %s <-> ( d e. ( 1 ... L ) /\\ d || L ) ) )' % (A, DIVM('L'))), bi], 'bitrd',
         '( %s -> ( d e. %s <-> ( d e. NN /\\ d || L ) ) )' % (A, DIVM('L')))
b2 = w.s([b1, w.s([w.s([e2], 'bicomi', '( ( d e. NN /\\ d || L ) <-> d e. %s )' % DIVN('L'))], 'a1i',
                  '( %s -> ( ( d e. NN /\\ d || L ) <-> d e. %s ) )' % (A, DIVN('L')))], 'bitrd',
         '( %s -> ( d e. %s <-> d e. %s ) )' % (A, DIVM('L'), DIVN('L')))
w.qed([b2], 'eqrdv', '( %s -> %s = %s )' % (A, DIVM('L'), DIVN('L')))
run(w)

w = W('sqfdivset', 'Every divisor of a squarefree L is squarefree.')
A = '( L e. NN /\\ ( mmu ` L ) =/= 0 )'
B = '( %s /\\ m e. NN )' % A
mnn = w.s([], 'simpr', '( %s -> m e. NN )' % B)
lnn = w.s([], 'simpll', '( %s -> L e. NN )' % B)
lsq = w.s([], 'simplr', '( %s -> ( mmu ` L ) =/= 0 )' % B)
D = '( %s /\\ m || L )' % B
ds = w.s([w.s([lnn], 'adantr', '( %s -> L e. NN )' % D), w.s([mnn], 'adantr', '( %s -> m e. NN )' % D),
          w.s([], 'simpr', '( %s -> m || L )' % D), w.inst('dvdssqf')], 'syl3anc',
         '( %s -> ( ( mmu ` L ) =/= 0 -> ( mmu ` m ) =/= 0 ) )' % D)
msq = w.s([w.s([lsq], 'adantr', '( %s -> ( mmu ` L ) =/= 0 )' % D), ds], 'mpd', '( %s -> ( mmu ` m ) =/= 0 )' % D)
bwd = w.s([msq, w.s([], 'simpr', '( %s -> m || L )' % D)], 'jca', '( %s -> ( ( mmu ` m ) =/= 0 /\\ m || L ) )' % D)
fwd = w.s([], 'simprr', '( ( %s /\\ ( ( mmu ` m ) =/= 0 /\\ m || L ) ) -> m || L )' % B)
bi = w.s([fwd, bwd], 'impbida', '( %s -> ( ( ( mmu ` m ) =/= 0 /\\ m || L ) <-> m || L ) )' % B)
w.qed([bi], 'rabbidva', '( %s -> %s = %s )' % (A, SQDIV('L'), DIVN('L')))
run(w)

w = W('pcntmpt', 'A bound-variable renaming of the prime-valuation function.')
o1 = w.s([], 'oveq1', '( b = p -> ( b pCnt a ) = ( p pCnt a ) )')
c1 = w.s([o1], 'cbvmptv', '( b e. Prime |-> ( b pCnt a ) ) = ( p e. Prime |-> ( p pCnt a ) )')
m1 = w.s([c1], 'mpteq2i', '( a e. NN |-> ( b e. Prime |-> ( b pCnt a ) ) ) = ( a e. NN |-> ( p e. Prime |-> ( p pCnt a ) ) )')
o2 = w.s([], 'oveq2', '( a = k -> ( p pCnt a ) = ( p pCnt k ) )')
m2 = w.s([o2], 'mpteq2dv', '( a = k -> ( p e. Prime |-> ( p pCnt a ) ) = ( p e. Prime |-> ( p pCnt k ) ) )')
c2 = w.s([m2], 'cbvmptv', '( a e. NN |-> ( p e. Prime |-> ( p pCnt a ) ) ) = ( k e. NN |-> ( p e. Prime |-> ( p pCnt k ) ) )')
w.qed([m1, c2], 'eqtri', '( a e. NN |-> ( b e. Prime |-> ( b pCnt a ) ) ) = ( k e. NN |-> ( p e. Prime |-> ( p pCnt k ) ) )')
run(w)

w = W('sqfdivcard', 'A squarefree L has exactly 2 ^ omega ( L ) divisors (Lean: Nat.card_divisors, Step3W.lean hdivcard).')
A = '( L e. NN /\\ ( mmu ` L ) =/= 0 )'
S = SQDIV('L')
F = '( k e. %s |-> { p e. Prime | p || k } )' % S
G = '( a e. NN |-> ( b e. Prime |-> ( b pCnt a ) ) )'
lnn = w.s([], 'simpl', '( %s -> L e. NN )' % A)
h1 = w.s([], 'eqid', '%s = %s' % (S, S))
h2 = w.s([], 'eqid', '%s = %s' % (F, F))
h3 = w.s([], 'pcntmpt', '%s = ( k e. NN |-> ( p e. Prime |-> ( p pCnt k ) ) )' % G)
f1o = w.s([h1, h2, h3], 'sqff1o', '( L e. NN -> %s : %s -1-1-onto-> ~P %s )' % (F, S, PRD('L')))
f1od = w.s([lnn, f1o], 'syl', '( %s -> %s : %s -1-1-onto-> ~P %s )' % (A, F, S, PRD('L')))
sex = w.s([w.s([], 'nnex', 'NN e. _V')], 'rabex', '%s e. _V' % S)
sexd = w.s([sex], 'a1i', '( %s -> %s e. _V )' % (A, S))
en = w.s([sexd, f1od, w.inst('f1oeng')], 'syl2anc', '( %s -> %s ~~ ~P %s )' % (A, S, PRD('L')))
he = w.s([en, w.inst('hasheni')], 'syl', '( %s -> ( # ` %s ) = ( # ` ~P %s ) )' % (A, S, PRD('L')))
pf = w.s([lnn, w.inst('prmdvdsfi')], 'syl', '( %s -> %s e. Fin )' % (A, PRD('L')))
hp = w.s([pf, w.inst('hashpw')], 'syl', '( %s -> ( # ` ~P %s ) = ( 2 ^ ( # ` %s ) ) )' % (A, PRD('L'), PRD('L')))
he2 = w.s([he, hp], 'eqtrd', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` %s ) ) )' % (A, S, PRD('L')))
sd = w.s([], 'sqfdivset', '( %s -> %s = %s )' % (A, S, DIVN('L')))
w.qed([w.s([w.s([sd], 'eqcomd', '( %s -> %s = %s )' % (A, DIVN('L'), S))], 'fveq2d',
           '( %s -> ( # ` %s ) = ( # ` %s ) )' % (A, DIVN('L'), S)), he2], 'eqtrd',
      '( %s -> ( # ` %s ) = ( 2 ^ ( # ` %s ) ) )' % (A, DIVN('L'), PRD('L')))
run(w)

w = W('prmproddivcard', 'L = Lmod Q has exactly 2 ^ ( # Q ) divisors (Lean: Step3W.lean hdivcard).')
A = 'Q e. %s' % FP
qfp = w.s([], 'id', '( %s -> Q e. %s )' % (A, FP))
qs, qf, fn0, qz = fpparts(w, A, qfp)
lnn = w.s([qfp, w.inst('lmodqcl')], 'syl', '( %s -> %s e. NN )' % (A, LM))
lsq = w.s([qfp, w.inst('prmprodsqf')], 'syl', '( %s -> ( mmu ` %s ) =/= 0 )' % (A, LM))
j = w.s([lnn, lsq], 'jca', '( %s -> ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) )' % (A, LM, LM))
dn = w.s([lnn, w.inst('divsetnn')], 'syl', '( %s -> %s = %s )' % (A, DIVM(LM), DIVN(LM)))
sc = w.s([j, w.inst('sqfdivcard')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` %s ) ) )' % (A, DIVN(LM), PRD(LM)))
ps = w.s([qfp, w.inst('prmprodset')], 'syl', '( %s -> %s = Q )' % (A, PRD(LM)))
sc2 = w.s([sc, w.s([w.s([ps], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` Q ) )' % (A, PRD(LM)))], 'oveq2d',
                   '( %s -> ( 2 ^ ( # ` %s ) ) = ( 2 ^ ( # ` Q ) ) )' % (A, PRD(LM)))], 'eqtrd',
           '( %s -> ( # ` %s ) = ( 2 ^ ( # ` Q ) ) )' % (A, DIVN(LM)))
w.qed([w.s([dn], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (A, DIVM(LM), DIVN(LM))), sc2], 'eqtrd',
      '( %s -> ( # ` %s ) = ( 2 ^ ( # ` Q ) ) )' % (A, DIVM(LM)))
run(w)
