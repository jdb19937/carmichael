"""Sortie A3b, batch 3: the extraction inputs at windowed scales, pointwise
(A3b-blueprint.md section 2.3)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
import a3blib as LIB
from a3blib import HC, HC1, HC2, HN, NS, N5, IW, P2, GW, PL, A, B
from a3blib import L as LM
from tm import *
from lin import linarith
import num
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

a, b = A(), B()
n = NS()
ANT = '( %s /\\ %s /\\ %s )' % (HC, HN(), IW())
ZB = '( 1 < Z /\\ %s <_ ( log ` Z ) /\\ ( log ` Z ) <_ ( 3 x. %s ) )' % (b, b)
QP = '( Q e. ~P %s /\\ ( # ` Q ) = T )' % GW
GG = '( ( ( 3 / 2 ) x. %s ) x. %s )' % (a, b)
GLW = '( 0 < %s /\\ %s <_ ( log ` ( %s + 1 ) ) )' % (GG, GG, LM)
POOLB = '( ( log ` N ) ^c ( 6 / 5 ) ) <_ ( # ` %s )' % PL
BUD = '( ( ( ( log ` N ) / %s ) + 1 ) x. %s ) <_ ( # ` %s )' % (GG, P2, PL)

# ------------------------------------------------------------------ extrwglw
w = W('extrwglw', 'The round-count denominator is positive and below log ( LM + 1 ) at windowed scales (Lean: hlogL_ge and hlogL1_ge of extraction_inputsW of ExtractionW.lean).')
AX = '( %s /\\ %s )' % (ANT, QP)
def st(hyps, ref, f, X=None):
    return w.s(hyps, ref, '( %s -> %s )' % (X or AX, f))
anl = st([], 'simpl', ANT)
d = LIB.relay(w, AX, anl)
qpw = st([], 'simprl', 'Q e. ~P %s' % GW)
qcd = st([], 'simprr', '( # ` Q ) = T')
zb = st([anl, w.inst('extrwzcw')], 'syl', ZB)
z = LIB.zfacts(w, AX, d, zb)
# extrwloglgw
g1 = st([st([z['znn'], z['z1lt']], 'jca', '( Z e. NN /\\ 1 < Z )'),
         st([d['wn0'], d['yn0']], 'jca', '( W e. NN0 /\\ Y e. NN0 )')], 'jca',
        '( ( Z e. NN /\\ 1 < Z ) /\\ ( W e. NN0 /\\ Y e. NN0 ) )')
g2 = st([d['wlo'], qpw], 'jca', '( ( Z ^c ( ; 9 9 / ; ; 1 0 0 ) ) <_ ( W + 1 ) /\\ Q e. ~P %s )' % GW)
lg = st([g1, g2, w.inst('extrwloglgw')], 'syl2anc', '( ( # ` Q ) x. ( ( log ` Z ) / 2 ) ) <_ ( log ` %s )' % LM)
lg2 = st([st([qcd], 'oveq1d', '( ( # ` Q ) x. ( ( log ` Z ) / 2 ) ) = ( T x. ( ( log ` Z ) / 2 ) )'), lg], 'eqbrtrrd',
         '( T x. ( ( log ` Z ) / 2 ) ) <_ ( log ` %s )' % LM)
# G = ( ( 3 x. A ) x. ( B / 2 ) )
acn = st([d['are']], 'recnd', '%s e. CC' % a)
bcn = st([d['bre']], 'recnd', '%s e. CC' % b)
i3cn = st([num.cc(w, '3')], 'a1i', '3 e. CC')
i2cn = st([num.cc(w, '2')], 'a1i', '2 e. CC')
i2ne = st([num.fact(w, '2', 'ne0')], 'a1i', '2 =/= 0')
e1 = st([i3cn, acn, i2cn, i2ne], 'div23d', '( ( 3 x. %s ) / 2 ) = ( ( 3 / 2 ) x. %s )' % (a, a))
e2 = st([e1], 'eqcomd', '( ( 3 / 2 ) x. %s ) = ( ( 3 x. %s ) / 2 )' % (a, a))
e3 = st([e2], 'oveq1d', '%s = ( ( ( 3 x. %s ) / 2 ) x. %s )' % (GG, a, b))
a3cn = st([i3cn, acn], 'mulcld', '( 3 x. %s ) e. CC' % a)
e4 = st([a3cn, bcn, i2cn, i2ne], 'div23d', '( ( ( 3 x. %s ) x. %s ) / 2 ) = ( ( ( 3 x. %s ) / 2 ) x. %s )' % (a, b, a, b))
e5 = st([a3cn, bcn, i2cn, i2ne], 'divassd', '( ( ( 3 x. %s ) x. %s ) / 2 ) = ( ( 3 x. %s ) x. ( %s / 2 ) )' % (a, b, a, b))
e6 = st([e4, e5], 'eqtr3d', '( ( ( 3 x. %s ) / 2 ) x. %s ) = ( ( 3 x. %s ) x. ( %s / 2 ) )' % (a, b, a, b))
geq = st([e3, e6], 'eqtrd', '%s = ( ( 3 x. %s ) x. ( %s / 2 ) )' % (GG, a, b))
# ( ( 3 A ) x. ( B / 2 ) ) <_ ( T x. ( log Z / 2 ) )
a3re = st([i3cn, acn], 'mulcld', '( 3 x. %s ) e. CC' % a)
a3r = st([st([num.fact(w, '3', 'RR')], 'a1i', '3 e. RR'), d['are']], 'remulcld', '( 3 x. %s ) e. RR' % a)
b2r = st([d['bre'], st([num.fact(w, '2', 'RR')], 'a1i', '2 e. RR'), i2ne], 'redivcld', '( %s / 2 ) e. RR' % b)
lz2r = st([z['lzre'], st([num.fact(w, '2', 'RR')], 'a1i', '2 e. RR'), i2ne], 'redivcld', '( ( log ` Z ) / 2 ) e. RR')
LV = {a: ('RR', d['are']), b: ('RR', d['bre']), 'T': ('RR', d['tre']), '( log ` Z )': ('RR', z['lzre'])}
a3g0 = linarith(w, AX, [d['n2']], '0 <_ ( 3 x. %s )' % a, leaves=LV)
b2g0 = linarith(w, AX, [d['n3']], '0 <_ ( %s / 2 )' % b, leaves=LV)
b2le = linarith(w, AX, [z['blz']], '( %s / 2 ) <_ ( ( log ` Z ) / 2 )' % b, leaves=LV)
m12 = st([a3r, d['tre'], b2r, lz2r, a3g0, b2g0, d['tlo'], b2le], 'lemul12ad',
         '( ( 3 x. %s ) x. ( %s / 2 ) ) <_ ( T x. ( ( log ` Z ) / 2 ) )' % (a, b))
# LM e. NN, log LM <_ log ( LM + 1 )
qss = st([qpw, w.inst('elpwi')], 'syl', 'Q C_ %s' % GW)
qfpp = st([st([d['zn0'], d['wn0'], d['yn0']], '3jca', '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )'), qss, w.inst('s3sfp')], 'syl2anc', 'Q e. ( ~P Prime i^i Fin )')
lnn = st([qfpp, w.inst('lmodqcl')], 'syl', '%s e. NN' % LM)
lrp = st([lnn], 'nnrpd', '%s e. RR+' % LM)
lre = st([lnn], 'nnred', '%s e. RR' % LM)
l1rp = st([lrp, st([num.fact(w, '1', 'RR+')], 'a1i', '1 e. RR+')], 'rpaddcld', '( %s + 1 ) e. RR+' % LM)
llep1 = linarith(w, AX, [], '%s <_ ( %s + 1 )' % (LM, LM), leaves={LM: ('RR', lre)})
lgle = st([st([lrp, l1rp, w.inst('logleb')], 'syl2anc', '( %s <_ ( %s + 1 ) <-> ( log ` %s ) <_ ( log ` ( %s + 1 ) ) )' % (LM, LM, LM, LM)), llep1], 'mpbid',
          '( log ` %s ) <_ ( log ` ( %s + 1 ) )' % (LM, LM))
# chain
gre = st([st([st([num.fact(w, '3', 'RR')], 'a1i', '3 e. RR'), st([num.fact(w, '2', 'RR')], 'a1i', '2 e. RR'), i2ne], 'redivcld', '( 3 / 2 ) e. RR'), d['are']], 'remulcld', '( ( 3 / 2 ) x. %s ) e. RR' % a)
ggre = st([gre, d['bre']], 'remulcld', '%s e. RR' % GG)
tlz = st([d['tre'], lz2r], 'remulcld', '( T x. ( ( log ` Z ) / 2 ) ) e. RR')
llre = st([lrp], 'relogcld', '( log ` %s ) e. RR' % LM)
l1lre = st([l1rp], 'relogcld', '( log ` ( %s + 1 ) ) e. RR' % LM)
m12b = st([geq, m12], 'eqbrtrd', '%s <_ ( T x. ( ( log ` Z ) / 2 ) )' % GG)
c1 = st([ggre, tlz, llre, m12b, lg2], 'letrd', '%s <_ ( log ` %s )' % (GG, LM))
c2 = st([ggre, llre, l1lre, c1, lgle], 'letrd', '%s <_ ( log ` ( %s + 1 ) )' % (GG, LM))
g0a = linarith(w, AX, [d['n2']], '0 < ( ( 3 / 2 ) x. %s )' % a, leaves=LV)
g0b = linarith(w, AX, [d['n3']], '0 < %s' % b, leaves=LV)
g0 = st([gre, d['bre'], g0a, g0b], 'mulgt0d', '0 < %s' % GG)
w.qed([g0, c2], 'jca', '( %s -> %s )' % (AX, GLW))
assert run(w)


# ------------------------------------------------------------------ extrwbdw
w = W('extrwbdw', 'The budget at windowed scales: ( log n / ( 1.5 ell2 n ell3 n ) + 1 ) times the batch bound is below the pool size (Lean: hrle and hbudget of extraction_inputsW of ExtractionW.lean).')
AY = '( %s /\\ %s /\\ ( K e. NN /\\ %s ) )' % (ANT, QP, POOLB)
def st(hyps, ref, f, X=None):
    return w.s(hyps, ref, '( %s -> %s )' % (X or AY, f))
anl = st([], 'simp1', ANT)
d = LIB.relay(w, AY, anl)
qp = st([], 'simp2', QP)
qpw = st([qp], 'simpld', 'Q e. ~P %s' % GW)
kp = st([], 'simp3', '( K e. NN /\\ %s )' % POOLB)
knn = st([kp], 'simpld', 'K e. NN')
pb = st([kp], 'simprd', POOLB)
zb = st([anl, w.inst('extrwzcw')], 'syl', ZB)
z = LIB.zfacts(w, AY, d, zb)
glw = st([st([anl, qp], 'jca', '( %s /\\ %s )' % (ANT, QP)), w.inst('extrwglw')], 'syl', GLW)
g0 = st([glw], 'simpld', '0 < %s' % GG)
i2ne = st([num.fact(w, '2', 'ne0')], 'a1i', '2 =/= 0')
i32 = st([st([num.fact(w, '3', 'RR')], 'a1i', '3 e. RR'), st([num.fact(w, '2', 'RR')], 'a1i', '2 e. RR'), i2ne], 'redivcld', '( 3 / 2 ) e. RR')
gre = st([i32, d['are']], 'remulcld', '( ( 3 / 2 ) x. %s ) e. RR' % a)
ggre = st([gre, d['bre']], 'remulcld', '%s e. RR' % GG)
ggrp = st([ggre, g0], 'elrpd', '%s e. RR+' % GG)
# log N e. RR+ and exp ( ell2 N ) = log N
nre = st([d['nn0']], 'nn0red', 'N e. RR')
n1lt = st([d['uz2'], w.inst('eluz2gt1')], 'syl', '1 < N')
lnrp = st([nre, n1lt, w.inst('rplogcl')], 'syl2anc', '( log ` N ) e. RR+')
lnre = st([lnrp], 'rpred', '( log ` N ) e. RR')
lnge0 = st([lnrp], 'rpge0d', '0 <_ ( log ` N )')
e2v = st([d['nn0'], w.inst('ell2val')], 'syl', '%s = ( log ` ( log ` N ) )' % a)
efeq = st([st([e2v], 'fveq2d', '( exp ` %s ) = ( exp ` ( log ` ( log ` N ) ) )' % a),
           st([lnrp, w.inst('reeflog')], 'syl', '( exp ` ( log ` ( log ` N ) ) ) = ( log ` N )')], 'eqtrd',
          '( exp ` %s ) = ( log ` N )' % a)
# the first factor
U = '( ( ( log ` N ) / %s ) + 1 )' % GG
QQ = '( ( log ` N ) / %s )' % GG
p1 = st([d['arb'], d['br1'], w.inst('extrwp1')], 'syl2anc', '( ( ( exp ` %s ) / %s ) + 1 ) <_ ( exp ` ( ( ; 1 1 / ; 1 0 ) x. %s ) )' % (a, GG, a))
ueq = st([st([efeq], 'oveq1d', '( ( exp ` %s ) / %s ) = %s' % (a, GG, QQ))], 'oveq1d',
         '( ( ( exp ` %s ) / %s ) + 1 ) = %s' % (a, GG, U))
p1b = st([ueq, p1], 'eqbrtrrd', '%s <_ ( exp ` ( ( ; 1 1 / ; 1 0 ) x. %s ) )' % (U, a))
qre = st([lnre, ggre, st([g0], 'gt0ne0d', '%s =/= 0' % GG)], 'redivcld', '%s e. RR' % QQ)
q0 = st([lnre, ggrp, lnge0], 'divge0d', '0 <_ %s' % QQ)
ure = st([qre, st([num.fact(w, '1', 'RR')], 'a1i', '1 e. RR')], 'readdcld', '%s e. RR' % U)
u0 = linarith(w, AY, [q0], '0 <_ %s' % U, leaves={QQ: ('RR', qre)})
# the second factor
p2 = st([anl, w.inst('extrwp2w')], 'syl', '%s <_ ( exp ` ( ( 1 / ; 1 0 ) x. %s ) )' % (P2, a))
y1n0 = st([d['yn0'], st([num.fact(w, '1', 'NN0')], 'a1i', '1 e. NN0')], 'nn0addcld', '( Y + 1 ) e. NN0')
zg0 = st([d['zn0']], 'nn0ge0d', '0 <_ Z')
zyre = st([d['zre'], y1n0], 'reexpcld', '( Z ^ ( Y + 1 ) ) e. RR')
zyg0 = st([d['zre'], y1n0, zg0], 'expge0d', '0 <_ ( Z ^ ( Y + 1 ) )')
tlzre = st([d['tre'], z['lzre']], 'remulcld', '( T x. ( log ` Z ) ) e. RR')
tg0 = st([d['tn0']], 'nn0ge0d', '0 <_ T')
tlzg0 = st([d['tre'], z['lzre'], tg0, z['lz0']], 'mulge0d', '0 <_ ( T x. ( log ` Z ) )')
f2re = st([st([num.fact(w, '1', 'RR')], 'a1i', '1 e. RR'), tlzre], 'readdcld', '( 1 + ( T x. ( log ` Z ) ) ) e. RR')
f2g0 = linarith(w, AY, [tlzg0], '0 <_ ( 1 + ( T x. ( log ` Z ) ) )', leaves={'( T x. ( log ` Z ) )': ('RR', tlzre)})
prre = st([zyre, f2re], 'remulcld', '( ( Z ^ ( Y + 1 ) ) x. ( 1 + ( T x. ( log ` Z ) ) ) ) e. RR')
prg0 = st([zyre, f2re, zyg0, f2g0], 'mulge0d', '0 <_ ( ( Z ^ ( Y + 1 ) ) x. ( 1 + ( T x. ( log ` Z ) ) ) )')
p2re = st([prre, st([num.fact(w, '2', 'RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % P2)
p2g0 = linarith(w, AY, [prg0], '0 <_ %s' % P2, leaves={'( ( Z ^ ( Y + 1 ) ) x. ( 1 + ( T x. ( log ` Z ) ) ) )': ('RR', prre)})
# extrwstar, then the pool count
s1 = st([ure, u0, p1b], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( exp ` ( ( ; 1 1 / ; 1 0 ) x. %s ) ) )' % (U, U, U, a))
s2 = st([p2re, p2g0, p2], '3jca', '( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( exp ` ( ( 1 / ; 1 0 ) x. %s ) ) )' % (P2, P2, P2, a))
star = st([d['arb'], s1, s2, w.inst('extrwstar')], 'syl3anc', '( %s x. %s ) <_ ( exp ` ( ( 6 / 5 ) x. %s ) )' % (U, P2, a))
i65 = st([num.fact(w, '( 6 / 5 )', 'RR')], 'a1i', '( 6 / 5 ) e. RR')
ee = st([d['n1'], i65, w.inst('expell2')], 'syl2anc', '( exp ` ( ( 6 / 5 ) x. %s ) ) = ( ( log ` N ) ^c ( 6 / 5 ) )' % a)
star2 = st([star, ee], 'breqtrd', '( %s x. %s ) <_ ( ( log ` N ) ^c ( 6 / 5 ) )' % (U, P2))
qss = st([qpw, w.inst('elpwi')], 'syl', 'Q C_ %s' % GW)
qfpp = st([st([d['zn0'], d['wn0'], d['yn0']], '3jca', '( Z e. NN0 /\\ W e. NN0 /\\ Y e. NN0 )'), qss, w.inst('s3sfp')], 'syl2anc', 'Q e. ( ~P Prime i^i Fin )')
import a3lib
qs, qfin, qf0 = a3lib.fpp(w, AY, qfpp)
plfi = st([qf0, d['zn0'], st([knn], 'nnnn0d', 'K e. NN0'), w.inst('poolfi')], 'syl3anc', '%s e. Fin' % PL)
plre = st([st([plfi, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % PL)], 'nn0red', '( # ` %s ) e. RR' % PL)
uprre = st([ure, p2re], 'remulcld', '( %s x. %s ) e. RR' % (U, P2))
cxre = st([lnre, lnge0, i65], 'recxpcld', '( ( log ` N ) ^c ( 6 / 5 ) ) e. RR')
w.qed([uprre, cxre, plre, star2, pb], 'letrd', '( %s -> %s )' % (AY, BUD))
assert run(w)

# ------------------------------------------------------------------ extrwiw
CONCL4 = LIB.dbconcl('extrwins')
w = W('extrwiw', 'The five extraction inputs at windowed scales, pointwise (Lean: the body of extraction_inputsW of ExtractionW.lean).')
KC = '( K e. NN /\\ ( K gcd %s ) = 1 /\\ %s )' % (LM, POOLB)
AZ = '( %s /\\ %s /\\ %s )' % (ANT, QP, KC)
def st(hyps, ref, f, X=None):
    return w.s(hyps, ref, '( %s -> %s )' % (X or AZ, f))
anl = st([], 'simp1', ANT)
d = LIB.relay(w, AZ, anl)
qp = st([], 'simp2', QP)
kc = st([], 'simp3', KC)
knn = st([kc], 'simp1d', 'K e. NN')
kcop = st([kc], 'simp2d', '( K gcd %s ) = 1' % LM)
pb = st([kc], 'simp3d', POOLB)
zb = st([anl, w.inst('extrwzcw')], 'syl', ZB)
z = LIB.zfacts(w, AZ, d, zb)
glw = st([st([anl, qp], 'jca', '( %s /\\ %s )' % (ANT, QP)), w.inst('extrwglw')], 'syl', GLW)
bud = st([st([anl, qp, st([knn, pb], 'jca', '( K e. NN /\\ %s )' % POOLB)], '3jca',
             '( %s /\\ %s /\\ ( K e. NN /\\ %s ) )' % (ANT, QP, POOLB)), w.inst('extrwbdw')], 'syl', BUD)
i2ne = st([num.fact(w, '2', 'ne0')], 'a1i', '2 =/= 0')
i32 = st([st([num.fact(w, '3', 'RR')], 'a1i', '3 e. RR'), st([num.fact(w, '2', 'RR')], 'a1i', '2 e. RR'), i2ne], 'redivcld', '( 3 / 2 ) e. RR')
ggre = st([st([i32, d['are']], 'remulcld', '( ( 3 / 2 ) x. %s ) e. RR' % a), d['bre']], 'remulcld', '%s e. RR' % GG)
t1 = linarith(w, AZ, [d['tlo'], d['n2']], '1 <_ T', leaves={'T': ('RR', d['tre']), a: ('RR', d['are'])})
x1 = st([st([z['znn'], d['wn0']], 'jca', '( Z e. NN /\\ W e. NN0 )'),
         st([d['yn0'], d['tn0']], 'jca', '( Y e. NN0 /\\ T e. NN0 )')], 'jca',
        '( ( Z e. NN /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) )')
x2 = st([qp, st([knn, kcop], 'jca', '( K e. NN /\\ ( K gcd %s ) = 1 )' % LM)], 'jca',
        '( %s /\\ ( K e. NN /\\ ( K gcd %s ) = 1 ) )' % (QP, LM))
X = st([x1, x2], 'jca', '( ( ( Z e. NN /\\ W e. NN0 ) /\\ ( Y e. NN0 /\\ T e. NN0 ) ) /\\ ( %s /\\ ( K e. NN /\\ ( K gcd %s ) = 1 ) ) )' % (QP, LM))
y1 = st([st([ggre, st([glw], 'simpld', '0 < %s' % GG), st([glw], 'simprd', '%s <_ ( log ` ( %s + 1 ) )' % (GG, LM))], '3jca',
            '( %s e. RR /\\ 0 < %s /\\ %s <_ ( log ` ( %s + 1 ) ) )' % (GG, GG, GG, LM)),
         st([d['uz2'], t1], 'jca', '( N e. ( ZZ>= ` 2 ) /\\ 1 <_ T )')], 'jca',
        '( ( %s e. RR /\\ 0 < %s /\\ %s <_ ( log ` ( %s + 1 ) ) ) /\\ ( N e. ( ZZ>= ` 2 ) /\\ 1 <_ T ) )' % (GG, GG, GG, LM))
Y = st([y1, bud], 'jca',
       '( ( ( %s e. RR /\\ 0 < %s /\\ %s <_ ( log ` ( %s + 1 ) ) ) /\\ ( N e. ( ZZ>= ` 2 ) /\\ 1 <_ T ) ) /\\ %s )' % (GG, GG, GG, LM, BUD))
w.qed([X, Y, w.inst('extrwins')], 'syl2anc', '( %s -> %s )' % (AZ, CONCL4))
assert run(w)
