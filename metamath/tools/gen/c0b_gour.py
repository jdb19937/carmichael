"""Sortie C0b, batch 5: Cauchy-Goursat for rectangles by quartering.
The four quarter maps G H J K, the selector L and the nested sequence N are
carried as $e hypotheses (no new $c); every theorem here goes through runh."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *

RA = RE('A'); RB = RE('B'); IA = IM('A'); IB = IM('B')
U1 = '( 1st ` p )'; U2 = '( 2nd ` p )'
MXP = '( ( ( Re ` %s ) + ( Re ` %s ) ) / 2 )' % (U1, U2)
MYP = '( ( ( Im ` %s ) + ( Im ` %s ) ) / 2 )' % (U1, U2)
GDEF = 'G = ( p e. ( CC X. CC ) |-> <. %s , %s >. )' % (U1, PT(MXP, MYP))
HDEF = 'H = ( p e. ( CC X. CC ) |-> <. %s , %s >. )' % (PT(MXP, '( Im ` %s )' % U1), PT('( Re ` %s )' % U2, MYP))
JDEF = 'J = ( p e. ( CC X. CC ) |-> <. %s , %s >. )' % (PT(MXP, MYP), U2)
KDEF = 'K = ( p e. ( CC X. CC ) |-> <. %s , %s >. )' % (PT('( Re ` %s )' % U1, MYP), PT(MXP, '( Im ` %s )' % U2))
QUART = '( ( abs ` ( F rectint p ) ) / 4 )'
LDEF = ('L = ( p e. ( CC X. CC ) |-> if ( %s <_ ( abs ` ( F rectint ( G ` p ) ) ) , ( G ` p ) , '
        'if ( %s <_ ( abs ` ( F rectint ( H ` p ) ) ) , ( H ` p ) , '
        'if ( %s <_ ( abs ` ( F rectint ( J ` p ) ) ) , ( J ` p ) , ( K ` p ) ) ) ) )' % (QUART, QUART, QUART))
OP = '( u e. _V , v e. _V |-> ( L ` u ) )'
CF = '( NN0 X. { <. A , B >. } )'
NDEF = 'N = seq 0 ( %s , %s )' % (OP, CF)
SEQ = 'seq 0 ( %s , %s )' % (OP, CF)

# ---- gourn0
w = W('gourn0', 'The nested-rectangle sequence starts at the given rectangle.')
hyp(w, '1', 'gourn0.n', NDEF)
z0 = w.s([], '0z', '0 e. ZZ')
s1 = w.s([z0, w.inst('seq1')], 'ax-mp', '( %s ` 0 ) = ( %s ` 0 )' % (SEQ, CF))
nf = w.s(['1'], 'fveq1i', '( N ` 0 ) = ( %s ` 0 )' % SEQ)
oe = w.s([], 'opex', '<. A , B >. e. _V')
n0 = w.s([], '0nn0', '0 e. NN0')
s2 = w.s([oe, n0, w.inst('fvconst2g')], 'mp2an', '( %s ` 0 ) = <. A , B >.' % CF)
w.qed([w.s([nf, s1], 'eqtri', '( N ` 0 ) = ( %s ` 0 )' % CF), s2], 'eqtri', '( N ` 0 ) = <. A , B >.')
run(w, True)

# ---- gournp1
w = W('gournp1', 'The recursion step of the nested-rectangle sequence.')
hyp(w, '1', 'gournp1.n', NDEF)
A0 = 'M e. NN0'
uz = w.s([w.s([], 'elnn0uz', '( M e. NN0 <-> M e. ( ZZ>= ` 0 ) )')], 'biimpi', '( M e. NN0 -> M e. ( ZZ>= ` 0 ) )')
p1 = w.s([uz, w.inst('seqp1')], 'syl', '( %s -> ( %s ` ( M + 1 ) ) = ( ( %s ` M ) %s ( %s ` ( M + 1 ) ) ) )' % (A0, SEQ, SEQ, OP, CF))
nl = w.s(['1'], 'fveq1i', '( N ` ( M + 1 ) ) = ( %s ` ( M + 1 ) )' % SEQ)
nr = w.s(['1'], 'fveq1i', '( N ` M ) = ( %s ` M )' % SEQ)
nrc = w.s([nr], 'eqcomi', '( %s ` M ) = ( N ` M )' % SEQ)
rw = w.s([nrc], 'oveq1i', '( ( %s ` M ) %s ( %s ` ( M + 1 ) ) ) = ( ( N ` M ) %s ( %s ` ( M + 1 ) ) )' % (SEQ, OP, CF, OP, CF))
st1 = w.s([nl, p1], 'eqtrid', '( %s -> ( N ` ( M + 1 ) ) = ( ( %s ` M ) %s ( %s ` ( M + 1 ) ) ) )' % (A0, SEQ, OP, CF))
st2 = w.s([st1, w.s([rw], 'a1i', '( %s -> ( ( %s ` M ) %s ( %s ` ( M + 1 ) ) ) = ( ( N ` M ) %s ( %s ` ( M + 1 ) ) ) )' % (A0, SEQ, OP, CF, OP, CF))], 'eqtrd',
          '( %s -> ( N ` ( M + 1 ) ) = ( ( N ` M ) %s ( %s ` ( M + 1 ) ) ) )' % (A0, OP, CF))
# evaluate the operation
E1 = '( u = ( N ` M ) /\\ v = ( %s ` ( M + 1 ) ) )' % CF
sb = w.s([w.s([], 'simpl', '( %s -> u = ( N ` M ) )' % E1)], 'fveq2d', '( %s -> ( L ` u ) = ( L ` ( N ` M ) ) )' % E1)
de = w.s([], 'eqid', '%s = %s' % (OP, OP))
v1 = w.s([], 'fvex', '( N ` M ) e. _V')
v2 = w.s([], 'fvex', '( %s ` ( M + 1 ) ) e. _V' % CF)
v3 = w.s([], 'fvex', '( L ` ( N ` M ) ) e. _V')
ov = w.s([v1, v2, v3, w.s([sb, de], 'ovmpoga', '( ( ( N ` M ) e. _V /\\ ( %s ` ( M + 1 ) ) e. _V /\\ ( L ` ( N ` M ) ) e. _V ) -> ( ( N ` M ) %s ( %s ` ( M + 1 ) ) ) = ( L ` ( N ` M ) ) )' % (CF, OP, CF))], 'mp3an',
          '( ( N ` M ) %s ( %s ` ( M + 1 ) ) ) = ( L ` ( N ` M ) )' % (OP, CF))
w.qed([st2, w.s([ov], 'a1i', '( %s -> ( ( N ` M ) %s ( %s ` ( M + 1 ) ) ) = ( L ` ( N ` M ) ) )' % (A0, OP, CF))], 'eqtrd',
      '( %s -> ( N ` ( M + 1 ) ) = ( L ` ( N ` M ) ) )' % A0)
run(w, True)

# ---- gourdvbr: the derivative as a limit of the difference quotient
GQ = '( w e. ( D \\ { Z } ) |-> ( ( ( F ` w ) - ( F ` Z ) ) / ( w - Z ) ) )'
TOPC = '( ( TopOpen ` CCfld ) |`t CC )'
w = W('gourdvbr', 'The complex derivative at a point of the domain is the limit of the difference quotient.')
A0 = '( F e. ( D -cn-> CC ) /\\ Z e. dom ( CC _D F ) /\\ C = ( ( CC _D F ) ` Z ) )'
fcn = w.s([], 'simp1', '( %s -> F e. ( D -cn-> CC ) )' % A0)
zd = w.s([], 'simp2', '( %s -> Z e. dom ( CC _D F ) )' % A0)
ceq = w.s([], 'simp3', '( %s -> C = ( ( CC _D F ) ` Z ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
dvf = closed(w, A0, 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC')
fun = w.s([dvf, w.inst('ffun')], 'syl', '( %s -> Fun ( CC _D F ) )' % A0)
brb = w.s([fun, w.inst('funfvbrb')], 'syl', '( %s -> ( Z e. dom ( CC _D F ) <-> Z ( CC _D F ) ( ( CC _D F ) ` Z ) ) )' % A0)
br1 = w.s([brb, zd], 'mpbird', '( %s -> Z ( CC _D F ) ( ( CC _D F ) ` Z ) )' % A0) if False else w.s([zd, brb], 'mpbid', '( %s -> Z ( CC _D F ) ( ( CC _D F ) ` Z ) )' % A0)
br = w.s([br1, ceq], 'breqtrrd', '( %s -> Z ( CC _D F ) C )' % A0)
t = w.s([], 'eqid', '%s = %s' % (TOPC, TOPC))
k = w.s([], 'eqid', '( TopOpen ` CCfld ) = ( TopOpen ` CCfld )')
g = w.s([], 'eqid', '%s = %s' % (GQ, GQ))
sc = closed(w, A0, 'ssid', 'CC C_ CC')
ed = w.s([t, k, g, sc, ff, dss], 'eldv', '( %s -> ( Z ( CC _D F ) C <-> ( Z e. ( ( int ` %s ) ` D ) /\\ C e. ( %s limCC Z ) ) ) )' % (A0, TOPC, GQ))
cj = w.s([ed, br], 'mpbid', '( %s -> ( Z e. ( ( int ` %s ) ` D ) /\\ C e. ( %s limCC Z ) ) )' % (A0, TOPC, GQ))
w.qed([cj], 'simprd', '( %s -> C e. ( %s limCC Z ) )' % (A0, GQ)); run(w)

# ---- gourdvq: the difference-quotient estimate in product form
def BODY(t):
    return '( ( %s =/= Z /\\ ( abs ` ( %s - Z ) ) < Y ) -> ( abs ` ( ( %s ` %s ) - C ) ) < E )' % (t, t, GQ, t)
ALLS = 'A. s e. ( D \\ { Z } ) %s' % BODY('s')
DQ = '( ( F ` z ) - ( F ` Z ) )'; ZZ = '( z - Z )'
NUM = '( %s - ( C x. %s ) )' % (DQ, ZZ)
GOALB = '( ( abs ` %s ) < Y -> ( abs ` %s ) <_ ( E x. ( abs ` %s ) ) )' % (ZZ, NUM, ZZ)
w = W('gourdvq', 'From the difference-quotient estimate near a point, the linear approximation estimate.')
A0 = '( ( F e. ( D -cn-> CC ) /\\ Z e. D /\\ C e. CC ) /\\ ( Y e. RR+ /\\ E e. RR+ ) /\\ %s )' % ALLS
tri = w.s([], 'simp1', '( %s -> ( F e. ( D -cn-> CC ) /\\ Z e. D /\\ C e. CC ) )' % A0)
fcn = w.s([tri, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
zdm = w.s([tri, w.inst('simp2')], 'syl', '( %s -> Z e. D )' % A0)
ccc = w.s([tri, w.inst('simp3')], 'syl', '( %s -> C e. CC )' % A0)
pr2 = w.s([], 'simp2', '( %s -> ( Y e. RR+ /\\ E e. RR+ ) )' % A0)
yrp = w.s([pr2, w.inst('simpl')], 'syl', '( %s -> Y e. RR+ )' % A0)
erp = w.s([pr2, w.inst('simpr')], 'syl', '( %s -> E e. RR+ )' % A0)
alls = w.s([], 'simp3', '( %s -> %s )' % (A0, ALLS))
ff0 = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
ds0 = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
A1 = '( %s /\\ z e. D )' % A0
zd = w.s([], 'simpr', '( %s -> z e. D )' % A1)
def dn(st, f, lvl):
    return w.s([st], 'adantr', '( %s -> %s )' % (lvl, f))
ff = dn(ff0, 'F : D --> CC', A1); ds = dn(ds0, 'D C_ CC', A1)
zdm1 = dn(zdm, 'Z e. D', A1); cc1 = dn(ccc, 'C e. CC', A1); erp1 = dn(erp, 'E e. RR+', A1)
alls1 = dn(alls, ALLS, A1); yrp1 = dn(yrp, 'Y e. RR+', A1)
fz = w.s([ff, zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
fZ = w.s([ff, zdm1], 'ffvelcdmd', '( %s -> ( F ` Z ) e. CC )' % A1)
zcc = w.s([ds, zd], 'sseldd', '( %s -> z e. CC )' % A1)
Zcc = w.s([ds, zdm1], 'sseldd', '( %s -> Z e. CC )' % A1)
A2 = '( %s /\\ ( abs ` %s ) < Y )' % (A1, ZZ)
lty = w.s([], 'simpr', '( %s -> ( abs ` %s ) < Y )' % (A2, ZZ))
for nm, st, f in (('fz2', fz, '( F ` z ) e. CC'), ('fZ2', fZ, '( F ` Z ) e. CC'), ('zcc2', zcc, 'z e. CC'),
                  ('Zcc2', Zcc, 'Z e. CC'), ('cc2', cc1, 'C e. CC'), ('erp2', erp1, 'E e. RR+'),
                  ('alls2', alls1, ALLS), ('zd2', zd, 'z e. D')):
    globals()[nm] = w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
zmZ = w.s([zcc2, Zcc2], 'subcld', '( %s -> %s e. CC )' % (A2, ZZ))
dqc = w.s([fz2, fZ2], 'subcld', '( %s -> %s e. CC )' % (A2, DQ))
czz = w.s([cc2, zmZ], 'mulcld', '( %s -> ( C x. %s ) e. CC )' % (A2, ZZ))
numc = w.s([dqc, czz], 'subcld', '( %s -> %s e. CC )' % (A2, NUM))
absn = w.s([numc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A2, NUM))
absz = w.s([zmZ], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A2, ZZ))
absz0 = w.s([zmZ], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A2, ZZ))
ere = w.s([erp2, w.inst('rpre')], 'syl', '( %s -> E e. RR )' % A2)
ecc = w.s([ere], 'recnd', '( %s -> E e. CC )' % A2)
eabs = w.s([ere, absz], 'remulcld', '( %s -> ( E x. ( abs ` %s ) ) e. RR )' % (A2, ZZ))
# --- case z = Z
AE = '( %s /\\ z = Z )' % A2
zeq = w.s([], 'simpr', '( %s -> z = Z )' % AE)
for nm, st, f in (('Zcc3', Zcc2, 'Z e. CC'), ('fZ3', fZ2, '( F ` Z ) e. CC'), ('cc3', cc2, 'C e. CC'), ('ecc3', ecc, 'E e. CC')):
    globals()[nm] = w.s([st], 'adantr', '( %s -> %s )' % (AE, f))
e1 = w.s([w.s([zeq], 'oveq1d', '( %s -> %s = ( Z - Z ) )' % (AE, ZZ)), w.s([Zcc3], 'subidd', '( %s -> ( Z - Z ) = 0 )' % AE)], 'eqtrd', '( %s -> %s = 0 )' % (AE, ZZ))
e2 = w.s([w.s([w.s([zeq], 'fveq2d', '( %s -> ( F ` z ) = ( F ` Z ) )' % AE)], 'oveq1d', '( %s -> %s = ( ( F ` Z ) - ( F ` Z ) ) )' % (AE, DQ)), w.s([fZ3], 'subidd', '( %s -> ( ( F ` Z ) - ( F ` Z ) ) = 0 )' % AE)], 'eqtrd', '( %s -> %s = 0 )' % (AE, DQ))
e3 = w.s([w.s([e1], 'oveq2d', '( %s -> ( C x. %s ) = ( C x. 0 ) )' % (AE, ZZ)), w.s([cc3], 'mul01d', '( %s -> ( C x. 0 ) = 0 )' % AE)], 'eqtrd', '( %s -> ( C x. %s ) = 0 )' % (AE, ZZ))
z0 = closed(w, AE, '0m0e0', '( 0 - 0 ) = 0')
e4 = w.s([w.s([e2, e3], 'oveq12d', '( %s -> %s = ( 0 - 0 ) )' % (AE, NUM)), z0], 'eqtrd', '( %s -> %s = 0 )' % (AE, NUM))
ab0 = closed(w, AE, 'abs0', '( abs ` 0 ) = 0')
e5 = w.s([w.s([e4], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` 0 ) )' % (AE, NUM)), ab0], 'eqtrd', '( %s -> ( abs ` %s ) = 0 )' % (AE, NUM))
e6 = w.s([w.s([e1], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` 0 ) )' % (AE, ZZ)), ab0], 'eqtrd', '( %s -> ( abs ` %s ) = 0 )' % (AE, ZZ))
e7 = w.s([w.s([e6], 'oveq2d', '( %s -> ( E x. ( abs ` %s ) ) = ( E x. 0 ) )' % (AE, ZZ)), w.s([ecc3], 'mul01d', '( %s -> ( E x. 0 ) = 0 )' % AE)], 'eqtrd', '( %s -> ( E x. ( abs ` %s ) ) = 0 )' % (AE, ZZ))
e8 = closed(w, AE, '0le0', '0 <_ 0')
case1 = w.s([e8, e5, e7], '3brtr4d', '( %s -> ( abs ` %s ) <_ ( E x. ( abs ` %s ) ) )' % (AE, NUM, ZZ))
# --- case z =/= Z
AN = '( %s /\\ z =/= Z )' % A2
zne = w.s([], 'simpr', '( %s -> z =/= Z )' % AN)
for nm, st, f in (('zd4', zd2, 'z e. D'), ('zcc4', zcc2, 'z e. CC'), ('Zcc4', Zcc2, 'Z e. CC'),
                  ('fz4', fz2, '( F ` z ) e. CC'), ('fZ4', fZ2, '( F ` Z ) e. CC'), ('cc4', cc2, 'C e. CC'),
                  ('alls4', alls2, ALLS), ('lty4', lty, '( abs ` %s ) < Y' % ZZ), ('ere4', ere, 'E e. RR'),
                  ('absn4', absn, '( abs ` %s ) e. RR' % NUM), ('absz4', absz, '( abs ` %s ) e. RR' % ZZ),
                  ('absz04', absz0, '0 <_ ( abs ` %s )' % ZZ), ('zmZ4', zmZ, '%s e. CC' % ZZ),
                  ('dqc4', dqc, '%s e. CC' % DQ), ('numc4', numc, '%s e. CC' % NUM), ('czz4', czz, '( C x. %s ) e. CC' % ZZ)):
    globals()[nm] = w.s([st], 'adantr', '( %s -> %s )' % (AN, f))
zdifb = closed(w, AN, 'eldifsn', '( z e. ( D \\ { Z } ) <-> ( z e. D /\\ z =/= Z ) )')
zdif = w.s([zdifb, w.s([zd4, zne], 'jca', '( %s -> ( z e. D /\\ z =/= Z ) )' % AN)], 'mpbird', '( %s -> z e. ( D \\ { Z } ) )' % AN)
n1 = w.s([], 'neeq1', '( s = z -> ( s =/= Z <-> z =/= Z ) )')
o1 = w.s([], 'oveq1', '( s = z -> ( s - Z ) = %s )' % ZZ)
f1 = w.s([o1], 'fveq2d', '( s = z -> ( abs ` ( s - Z ) ) = ( abs ` %s ) )' % ZZ)
b1 = w.s([f1], 'breq1d', '( s = z -> ( ( abs ` ( s - Z ) ) < Y <-> ( abs ` %s ) < Y ) )' % ZZ)
a1 = w.s([n1, b1], 'anbi12d', '( s = z -> ( ( s =/= Z /\\ ( abs ` ( s - Z ) ) < Y ) <-> ( z =/= Z /\\ ( abs ` %s ) < Y ) ) )' % ZZ)
g1 = w.s([], 'fveq2', '( s = z -> ( %s ` s ) = ( %s ` z ) )' % (GQ, GQ))
o2 = w.s([g1], 'oveq1d', '( s = z -> ( ( %s ` s ) - C ) = ( ( %s ` z ) - C ) )' % (GQ, GQ))
f2 = w.s([o2], 'fveq2d', '( s = z -> ( abs ` ( ( %s ` s ) - C ) ) = ( abs ` ( ( %s ` z ) - C ) ) )' % (GQ, GQ))
b2 = w.s([f2], 'breq1d', '( s = z -> ( ( abs ` ( ( %s ` s ) - C ) ) < E <-> ( abs ` ( ( %s ` z ) - C ) ) < E ) )' % (GQ, GQ))
sub = w.s([a1, b2], 'imbi12d', '( s = z -> ( %s <-> %s ) )' % (BODY('s'), BODY('z')))
inst = w.s([sub, alls4, zdif], 'rspcdva', '( %s -> %s )' % (AN, BODY('z')))
cond = w.s([zne, lty4], 'jca', '( %s -> ( z =/= Z /\\ ( abs ` %s ) < Y ) )' % (AN, ZZ))
lt = w.s([cond, inst], 'mpd', '( %s -> ( abs ` ( ( %s ` z ) - C ) ) < E )' % (AN, GQ))
# the value of the difference quotient at z
QT = '( %s / %s )' % (DQ, ZZ)
znZ0 = w.s([zcc4, Zcc4, zne], 'subne0d', '( %s -> %s =/= 0 )' % (AN, ZZ))
qtc = w.s([dqc4, zmZ4, znZ0], 'divcld', '( %s -> %s e. CC )' % (AN, QT))
sa = w.s([], 'fveq2', '( w = z -> ( F ` w ) = ( F ` z ) )')
sb = w.s([sa], 'oveq1d', '( w = z -> ( ( F ` w ) - ( F ` Z ) ) = %s )' % DQ)
sc2 = w.s([], 'oveq1', '( w = z -> ( w - Z ) = %s )' % ZZ)
sd = w.s([sb, sc2], 'oveq12d', '( w = z -> ( ( ( F ` w ) - ( F ` Z ) ) / ( w - Z ) ) = %s )' % QT)
se = w.s([], 'eqid', '%s = %s' % (GQ, GQ))
qtex = closed(w, AN, 'ovex', '%s e. _V' % QT)
gqv = w.s([zdif, qtex, w.s([sd, se], 'fvmptg', '( ( z e. ( D \\ { Z } ) /\\ %s e. _V ) -> ( %s ` z ) = %s )' % (QT, GQ, QT))], 'syl2anc', '( %s -> ( %s ` z ) = %s )' % (AN, GQ, QT))
# the product form
DIFF = '( %s - C )' % QT
diffc = w.s([qtc, cc4], 'subcld', '( %s -> %s e. CC )' % (AN, DIFF))
s1 = w.s([qtc, cc4, zmZ4], 'subdird', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) - ( C x. %s ) ) )' % (AN, DIFF, ZZ, QT, ZZ, ZZ))
s2 = w.s([dqc4, zmZ4, znZ0], 'divcan1d', '( %s -> ( %s x. %s ) = %s )' % (AN, QT, ZZ, DQ))
s3 = w.s([s1, w.s([s2], 'oveq1d', '( %s -> ( ( %s x. %s ) - ( C x. %s ) ) = %s )' % (AN, QT, ZZ, ZZ, NUM))], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (AN, DIFF, ZZ, NUM))
s4 = w.s([diffc, zmZ4], 'absmuld', '( %s -> ( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (AN, DIFF, ZZ, DIFF, ZZ))
s5 = w.s([w.s([w.s([s3], 'fveq2d', '( %s -> ( abs ` ( %s x. %s ) ) = ( abs ` %s ) )' % (AN, DIFF, ZZ, NUM))], 'eqcomd', '( %s -> ( abs ` %s ) = ( abs ` ( %s x. %s ) ) )' % (AN, NUM, DIFF, ZZ)), s4], 'eqtrd',
         '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (AN, NUM, DIFF, ZZ))
ltq = w.s([w.s([w.s([gqv], 'oveq1d', '( %s -> ( ( %s ` z ) - C ) = %s )' % (AN, GQ, DIFF))], 'fveq2d', '( %s -> ( abs ` ( ( %s ` z ) - C ) ) = ( abs ` %s ) )' % (AN, GQ, DIFF)), lt], 'eqbrtrrd',
          '( %s -> ( abs ` %s ) < E )' % (AN, DIFF))
absd = w.s([diffc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (AN, DIFF))
leq = w.s([absd, ere4, ltq], 'ltled', '( %s -> ( abs ` %s ) <_ E )' % (AN, DIFF))
tri3 = w.s([absd, ere4, w.s([absz4, absz04], 'jca', '( %s -> ( ( abs ` %s ) e. RR /\\ 0 <_ ( abs ` %s ) ) )' % (AN, ZZ, ZZ))], '3jca',
           '( %s -> ( ( abs ` %s ) e. RR /\\ E e. RR /\\ ( ( abs ` %s ) e. RR /\\ 0 <_ ( abs ` %s ) ) ) )' % (AN, DIFF, ZZ, ZZ))
mul = w.s([tri3, leq, w.inst('lemul1a')], 'syl2anc', '( %s -> ( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( E x. ( abs ` %s ) ) )' % (AN, DIFF, ZZ, ZZ))
case2 = w.s([s5, mul], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( E x. ( abs ` %s ) ) )' % (AN, NUM, ZZ))
both = w.s([case1, case2], 'pm2.61dane', '( %s -> ( abs ` %s ) <_ ( E x. ( abs ` %s ) ) )' % (A2, NUM, ZZ))
exs = w.s([both], 'ex', '( %s -> %s )' % (A1, GOALB))
w.qed([exs], 'ralrimiva', '( %s -> A. z e. D %s )' % (A0, GOALB)); run(w, True)

# ---- gourdveps: the linear approximation estimate in epsilon-delta form
def PSI(x, y):
    return 'A. s e. ( D \\ { Z } ) ( ( s =/= Z /\\ ( abs ` ( s - Z ) ) < %s ) -> ( abs ` ( ( %s ` s ) - C ) ) < %s )' % (y, GQ, x)
def GB(r):
    return '( ( abs ` %s ) < %s -> ( abs ` %s ) <_ ( E x. ( abs ` %s ) ) )' % (ZZ, r, NUM, ZZ)
w = W('gourdveps', 'The linear approximation estimate at a point of differentiability, in epsilon-delta form.')
PHI = '( F e. ( D -cn-> CC ) /\\ Z e. dom ( CC _D F ) /\\ C = ( ( CC _D F ) ` Z ) )'
A0 = '( %s /\\ E e. RR+ )' % PHI
fcn = w.s([], 'simp1', '( %s -> F e. ( D -cn-> CC ) )' % PHI)
zdd = w.s([], 'simp2', '( %s -> Z e. dom ( CC _D F ) )' % PHI)
ceq = w.s([], 'simp3', '( %s -> C = ( ( CC _D F ) ` Z ) )' % PHI)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % PHI)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % PHI)
sc = closed(w, PHI, 'ssid', 'CC C_ CC')
bss = w.s([sc, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % PHI)
zdm = w.s([bss, zdd], 'sseldd', '( %s -> Z e. D )' % PHI)
dvf = closed(w, PHI, 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC')
ccc = w.s([ceq, w.s([dvf, zdd], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` Z ) e. CC )' % PHI)], 'eqeltrd', '( %s -> C e. CC )' % PHI)
Zcc = w.s([dss, zdm], 'sseldd', '( %s -> Z e. CC )' % PHI)
fZ = w.s([ff, zdm], 'ffvelcdmd', '( %s -> ( F ` Z ) e. CC )' % PHI)
# GQ is a function into CC
AW = '( %s /\\ w e. ( D \\ { Z } ) )' % PHI
wd = w.s([], 'simpr', '( %s -> w e. ( D \\ { Z } ) )' % AW)
wdd = w.s([wd, w.inst('eldifi')], 'syl', '( %s -> w e. D )' % AW)
wne = w.s([w.s([wd, w.s([], 'eldifsn', '( w e. ( D \\ { Z } ) <-> ( w e. D /\\ w =/= Z ) )')], 'sylib', '( %s -> ( w e. D /\\ w =/= Z ) )' % AW)], 'simprd', '( %s -> w =/= Z )' % AW)
ffw = w.s([ff], 'adantr', '( %s -> F : D --> CC )' % AW)
Zw = w.s([Zcc], 'adantr', '( %s -> Z e. CC )' % AW)
fZw = w.s([fZ], 'adantr', '( %s -> ( F ` Z ) e. CC )' % AW)
dsw = w.s([dss], 'adantr', '( %s -> D C_ CC )' % AW)
wcc = w.s([dsw, wdd], 'sseldd', '( %s -> w e. CC )' % AW)
fw = w.s([ffw, wdd], 'ffvelcdmd', '( %s -> ( F ` w ) e. CC )' % AW)
wn0 = w.s([wcc, Zw, wne], 'subne0d', '( %s -> ( w - Z ) =/= 0 )' % AW)
qw = w.s([w.s([fw, fZw], 'subcld', '( %s -> ( ( F ` w ) - ( F ` Z ) ) e. CC )' % AW), w.s([wcc, Zw], 'subcld', '( %s -> ( w - Z ) e. CC )' % AW), wn0], 'divcld',
         '( %s -> ( ( ( F ` w ) - ( F ` Z ) ) / ( w - Z ) ) e. CC )' % AW)
gqf = w.s([qw], 'fmptd', '( %s -> %s : ( D \\ { Z } ) --> CC )' % (PHI, GQ))
dfss = w.s([closed(w, PHI, 'difss', '( D \\ { Z } ) C_ D'), dss], 'sstrd', '( %s -> ( D \\ { Z } ) C_ CC )' % PHI)
lc = w.s([gqf, dfss, Zcc], 'ellimc3', '( %s -> ( C e. ( %s limCC Z ) <-> ( C e. CC /\\ A. x e. RR+ E. y e. RR+ %s ) ) )' % (PHI, GQ, PSI('x', 'y')))
br = w.s([], 'gourdvbr', '( %s -> C e. ( %s limCC Z ) )' % (PHI, GQ))
allx = w.s([w.s([lc, br], 'mpbid', '( %s -> ( C e. CC /\\ A. x e. RR+ E. y e. RR+ %s ) )' % (PHI, PSI('x', 'y')))], 'simprd', '( %s -> A. x e. RR+ E. y e. RR+ %s )' % (PHI, PSI('x', 'y')))
# instantiate x := E
sb1 = w.s([], 'breq2', '( x = E -> ( ( abs ` ( ( %s ` s ) - C ) ) < x <-> ( abs ` ( ( %s ` s ) - C ) ) < E ) )' % (GQ, GQ))
sb2 = w.s([sb1], 'imbi2d', '( x = E -> ( ( ( s =/= Z /\\ ( abs ` ( s - Z ) ) < y ) -> ( abs ` ( ( %s ` s ) - C ) ) < x ) <-> ( ( s =/= Z /\\ ( abs ` ( s - Z ) ) < y ) -> ( abs ` ( ( %s ` s ) - C ) ) < E ) ) )' % (GQ, GQ))
sb3 = w.s([sb2], 'ralbidv', '( x = E -> ( %s <-> %s ) )' % (PSI('x', 'y'), PSI('E', 'y')))
sb4 = w.s([sb3], 'rexbidv', '( x = E -> ( E. y e. RR+ %s <-> E. y e. RR+ %s ) )' % (PSI('x', 'y'), PSI('E', 'y')))
erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
allx2 = w.s([allx], 'adantr', '( %s -> A. x e. RR+ E. y e. RR+ %s )' % (A0, PSI('x', 'y')))
exy = w.s([sb4, allx2, erp], 'rspcdva', '( %s -> E. y e. RR+ %s )' % (A0, PSI('E', 'y')))
# from a witness y to the conclusion
A1 = '( %s /\\ y e. RR+ )' % A0
yrp = w.s([], 'simpr', '( %s -> y e. RR+ )' % A1)
A2 = '( %s /\\ %s )' % (A1, PSI('E', 'y'))
psi = w.s([], 'simpr', '( %s -> %s )' % (A2, PSI('E', 'y')))
for nm, st, f in (('fcn2', fcn, 'F e. ( D -cn-> CC )'), ('zdm2', zdm, 'Z e. D'), ('ccc2', ccc, 'C e. CC')):
    globals()[nm] = w.s([w.s([w.s([st], 'adantr', '( %s -> %s )' % (A0, f))], 'adantr', '( %s -> %s )' % (A1, f))], 'adantr', '( %s -> %s )' % (A2, f))
erp2 = w.s([w.s([erp], 'adantr', '( %s -> E e. RR+ )' % A1)], 'adantr', '( %s -> E e. RR+ )' % A2)
yrp2 = w.s([yrp], 'adantr', '( %s -> y e. RR+ )' % A2)
h1 = w.s([fcn2, zdm2, ccc2], '3jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ Z e. D /\\ C e. CC ) )' % A2)
h2 = w.s([yrp2, erp2], 'jca', '( %s -> ( y e. RR+ /\\ E e. RR+ ) )' % A2)
dvq = w.s([h1, h2, psi, w.inst('gourdvq')], 'syl3anc', '( %s -> A. z e. D %s )' % (A2, GB('y')))
rb1 = w.s([], 'breq2', '( r = y -> ( ( abs ` %s ) < r <-> ( abs ` %s ) < y ) )' % (ZZ, ZZ))
rb2 = w.s([rb1], 'imbi1d', '( r = y -> ( %s <-> %s ) )' % (GB('r'), GB('y')))
rb3 = w.s([rb2], 'ralbidv', '( r = y -> ( A. z e. D %s <-> A. z e. D %s ) )' % (GB('r'), GB('y')))
ex = w.s([yrp2, dvq, w.s([rb3], 'rspcev', '( ( y e. RR+ /\\ A. z e. D %s ) -> E. r e. RR+ A. z e. D %s )' % (GB('y'), GB('r')))], 'syl2anc',
         '( %s -> E. r e. RR+ A. z e. D %s )' % (A2, GB('r')))
imp = w.s([ex], 'ex', '( %s -> ( %s -> E. r e. RR+ A. z e. D %s ) )' % (A1, PSI('E', 'y'), GB('r')))
rl = w.s([imp], 'rexlimdva', '( %s -> ( E. y e. RR+ %s -> E. r e. RR+ A. z e. D %s ) )' % (A0, PSI('E', 'y'), GB('r')))
w.qed([exy, rl], 'mpd', '( %s -> E. r e. RR+ A. z e. D %s )' % (A0, GB('r')))
run(w)

# ---- the four quarter maps: values and geometry
RU = RE('U'); RV = RE('V'); IU = IM('U'); IV = IM('V')
MX = '( ( %s + %s ) / 2 )' % (RU, RV); MY = '( ( %s + %s ) / 2 )' % (IU, IV)
HU1 = '( ( %s - %s ) / 2 )' % (RV, RU); HU2 = '( ( %s - %s ) / 2 )' % (IV, IU)
OPUV = '<. U , V >.'
UVCC = '( U e. CC /\\ V e. CC )'
ADMT = '( %s /\\ ( %s <_ %s /\\ %s <_ %s ) )' % (UVCC, RU, RV, IU, IV)
QUARTS = [('1', 'G', GDEF, 'U', PT(MX, MY)),
          ('2', 'H', HDEF, PT(MX, IU), PT(RV, MY)),
          ('3', 'J', JDEF, PT(MX, MY), 'V'),
          ('4', 'K', KDEF, PT(RU, MY), PT(MX, IV))]


def bodyp(Fn):
    """the mpt body of the definition of the quarter map Fn"""
    d = {'G': GDEF, 'H': HDEF, 'J': JDEF, 'K': KDEF}[Fn]
    i = d.index('|->') + 4
    return d[i:d.rindex(')')].strip()


for num, Fn, DEF, CQ, EQ in QUARTS:
    w = W('gourv' + num, 'The value of the quarter map at a rectangle given by its corners.')
    hyp(w, '1', 'gourv%s.d' % num, DEF)
    uc = w.s([], 'simpl', '( %s -> U e. CC )' % UVCC)
    vc = w.s([], 'simpr', '( %s -> V e. CC )' % UVCC)
    idp = w.s([], 'id', '( p = %s -> p = %s )' % (OPUV, OPUV))
    st, bod = w.congr(bodyp(Fn), {'p': OPUV}, 'p = %s' % OPUV, {'p': idp})
    fv = w.s([st, '1'], 'fvmptg', '( ( %s e. ( CC X. CC ) /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (OPUV, bod, Fn, OPUV, bod))
    xp = w.s([uc, vc, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( CC X. CC ) )' % (UVCC, OPUV))
    bx = closed(w, UVCC, 'opex', '%s e. _V' % bod)
    v0 = w.s([xp, bx, fv], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (UVCC, Fn, OPUV, bod))
    o1 = w.s([uc, vc, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = U )' % (UVCC, OPUV))
    o2 = w.s([uc, vc, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = V )' % (UVCC, OPUV))
    st2, fin = w.rewrite(bod, {'( 1st ` %s )' % OPUV: ('U', o1), '( 2nd ` %s )' % OPUV: ('V', o2)}, UVCC)
    w.qed([v0, st2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (UVCC, Fn, OPUV, fin))
    run(w, True)


def ADM1(q):
    return '( %s e. ( CC X. CC ) /\\ ( ( Re ` ( 1st ` %s ) ) <_ ( Re ` ( 2nd ` %s ) ) /\\ ( Im ` ( 1st ` %s ) ) <_ ( Im ` ( 2nd ` %s ) ) ) )' % (q, q, q, q, q)


def GEO1(q):
    return ('( ( ( 1st ` %s ) crect ( 2nd ` %s ) ) C_ ( U crect V ) /\\ '
            '( ( ( Re ` ( 2nd ` %s ) ) - ( Re ` ( 1st ` %s ) ) ) <_ %s /\\ ( ( Im ` ( 2nd ` %s ) ) - ( Im ` ( 1st ` %s ) ) ) <_ %s ) )'
            % (q, q, q, q, HU1, q, q, HU2))


def QCUV(P, Q):
    return ('( ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) ) /\\ '
            '( ( %s crect %s ) C_ ( U crect V ) /\\ ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ %s /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ %s ) ) )'
            % (P, Q, P, Q, P, Q, P, Q, Q, P, HU1, Q, P, HU2))


for num, Fn, DEF, CQ, EQ in QUARTS:
    w = W('gourq' + num, 'The quarter map sends an admissible rectangle to an admissible quarter of it.')
    hyp(w, '1', 'gourq%s.d' % num, DEF)
    OPQ = '<. %s , %s >.' % (CQ, EQ)
    A0 = '( %s /\\ Q = ( %s ` %s ) )' % (ADMT, Fn, OPUV)
    adm = w.s([], 'simpl', '( %s -> %s )' % (A0, ADMT))
    qd = w.s([], 'simpr', '( %s -> Q = ( %s ` %s ) )' % (A0, Fn, OPUV))
    uvcc = w.s([adm, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, UVCC))
    geo = w.s([adm, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A0, RU, RV, IU, IV))
    vi = w.s(['1'], 'gourv' + num, '( %s -> ( %s ` %s ) = %s )' % (UVCC, Fn, OPUV, OPQ))
    val = w.s([uvcc, vi], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A0, Fn, OPUV, OPQ))
    qeq = w.s([qd, val], 'eqtrd', '( %s -> Q = %s )' % (A0, OPQ))
    ex = w.s([], 'eqid', '%s = %s' % (MX, MX))
    ey = w.s([], 'eqid', '%s = %s' % (MY, MY))
    md = w.s([w.s([ex], 'a1i', '( %s -> %s = %s )' % (A0, MX, MX)), w.s([ey], 'a1i', '( %s -> %s = %s )' % (A0, MY, MY))], 'jca',
             '( %s -> ( %s = %s /\\ %s = %s ) )' % (A0, MX, MX, MY, MY))
    cq = w.s([uvcc, geo, md, w.inst('crectq' + num)], 'syl3anc', '( %s -> %s )' % (A0, QCUV(CQ, EQ)))
    ccp = w.s([cq, w.inst('simpll')], 'syl', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CQ, EQ))
    ordp = w.s([cq, w.inst('simplr')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, CQ, EQ, CQ, EQ))
    inc = w.s([cq, w.inst('simprl')], 'syl', '( %s -> ( %s crect %s ) C_ ( U crect V ) )' % (A0, CQ, EQ))
    sid = w.s([cq, w.inst('simprr')], 'syl', '( %s -> ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ %s /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ %s ) )' % (A0, EQ, CQ, HU1, EQ, CQ, HU2))
    ccq = w.s([ccp, w.inst('simpl')], 'syl', '( %s -> %s e. CC )' % (A0, CQ))
    ecq = w.s([ccp, w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (A0, EQ))
    o1 = w.s([ordp, w.inst('simpl')], 'syl', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, CQ, EQ))
    o2 = w.s([ordp, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, CQ, EQ))
    sd1 = w.s([sid, w.inst('simpl')], 'syl', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) <_ %s )' % (A0, EQ, CQ, HU1))
    sd2 = w.s([sid, w.inst('simpr')], 'syl', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) <_ %s )' % (A0, EQ, CQ, HU2))
    op1 = w.s([ccq, ecq, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (A0, OPQ, CQ))
    op2 = w.s([ccq, ecq, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (A0, OPQ, EQ))
    e1 = w.s([w.s([qeq], 'fveq2d', '( %s -> ( 1st ` Q ) = ( 1st ` %s ) )' % (A0, OPQ)), op1], 'eqtrd', '( %s -> ( 1st ` Q ) = %s )' % (A0, CQ))
    e2 = w.s([w.s([qeq], 'fveq2d', '( %s -> ( 2nd ` Q ) = ( 2nd ` %s ) )' % (A0, OPQ)), op2], 'eqtrd', '( %s -> ( 2nd ` Q ) = %s )' % (A0, EQ))
    xp = w.s([qeq, w.s([ccq, ecq, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( CC X. CC ) )' % (A0, OPQ))], 'eqeltrd', '( %s -> Q e. ( CC X. CC ) )' % A0)
    r1 = w.s([e1], 'fveq2d', '( %s -> ( Re ` ( 1st ` Q ) ) = ( Re ` %s ) )' % (A0, CQ))
    r2 = w.s([e2], 'fveq2d', '( %s -> ( Re ` ( 2nd ` Q ) ) = ( Re ` %s ) )' % (A0, EQ))
    m1 = w.s([e1], 'fveq2d', '( %s -> ( Im ` ( 1st ` Q ) ) = ( Im ` %s ) )' % (A0, CQ))
    m2 = w.s([e2], 'fveq2d', '( %s -> ( Im ` ( 2nd ` Q ) ) = ( Im ` %s ) )' % (A0, EQ))
    t2 = w.s([o1, r1, r2], '3brtr4d', '( %s -> ( Re ` ( 1st ` Q ) ) <_ ( Re ` ( 2nd ` Q ) ) )' % A0)
    t3 = w.s([o2, m1, m2], '3brtr4d', '( %s -> ( Im ` ( 1st ` Q ) ) <_ ( Im ` ( 2nd ` Q ) ) )' % A0)
    t4 = w.s([w.s([e1, e2], 'oveq12d', '( %s -> ( ( 1st ` Q ) crect ( 2nd ` Q ) ) = ( %s crect %s ) )' % (A0, CQ, EQ)), inc], 'eqsstrd',
             '( %s -> ( ( 1st ` Q ) crect ( 2nd ` Q ) ) C_ ( U crect V ) )' % A0)
    t5 = w.s([w.s([r2, r1], 'oveq12d', '( %s -> ( ( Re ` ( 2nd ` Q ) ) - ( Re ` ( 1st ` Q ) ) ) = ( ( Re ` %s ) - ( Re ` %s ) ) )' % (A0, EQ, CQ)), sd1], 'eqbrtrd',
             '( %s -> ( ( Re ` ( 2nd ` Q ) ) - ( Re ` ( 1st ` Q ) ) ) <_ %s )' % (A0, HU1))
    t6 = w.s([w.s([m2, m1], 'oveq12d', '( %s -> ( ( Im ` ( 2nd ` Q ) ) - ( Im ` ( 1st ` Q ) ) ) = ( ( Im ` %s ) - ( Im ` %s ) ) )' % (A0, EQ, CQ)), sd2], 'eqbrtrd',
             '( %s -> ( ( Im ` ( 2nd ` Q ) ) - ( Im ` ( 1st ` Q ) ) ) <_ %s )' % (A0, HU2))
    L = w.s([xp, w.s([t2, t3], 'jca', '( %s -> ( ( Re ` ( 1st ` Q ) ) <_ ( Re ` ( 2nd ` Q ) ) /\\ ( Im ` ( 1st ` Q ) ) <_ ( Im ` ( 2nd ` Q ) ) ) )' % A0)], 'jca', '( %s -> %s )' % (A0, ADM1('Q')))
    R = w.s([t4, w.s([t5, t6], 'jca', '( %s -> ( ( ( Re ` ( 2nd ` Q ) ) - ( Re ` ( 1st ` Q ) ) ) <_ %s /\\ ( ( Im ` ( 2nd ` Q ) ) - ( Im ` ( 1st ` Q ) ) ) <_ %s ) )' % (A0, HU1, HU2))], 'jca', '( %s -> %s )' % (A0, GEO1('Q')))
    w.qed([L, R], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, ADM1('Q'), GEO1('Q')))
    run(w, True)


# ---- gourlval: the value of the selector at a rectangle given by its corners
def CND(Fn):
    return '( ( abs ` ( F rectint %s ) ) / 4 ) <_ ( abs ` ( F rectint ( %s ` %s ) ) )' % (OPUV, Fn, OPUV)
IFUV = ('if ( %s , ( G ` %s ) , if ( %s , ( H ` %s ) , if ( %s , ( J ` %s ) , ( K ` %s ) ) ) )'
        % (CND('G'), OPUV, CND('H'), OPUV, CND('J'), OPUV, OPUV))
w = W('gourlval', 'The value of the quarter selector at a rectangle given by its corners.')
hyp(w, '1', 'gourlval.d', LDEF)
uc = w.s([], 'simpl', '( %s -> U e. CC )' % UVCC)
vc = w.s([], 'simpr', '( %s -> V e. CC )' % UVCC)
LBODY = LDEF[LDEF.index('|->') + 4:LDEF.rindex(')')].strip()
idp = w.s([], 'id', '( p = %s -> p = %s )' % (OPUV, OPUV))
st, bod = w.wcongr(LBODY, {'p': OPUV}, 'p = %s' % OPUV, {'p': idp}) if False else w.congr(LBODY, {'p': OPUV}, 'p = %s' % OPUV, {'p': idp})
fv = w.s([st, '1'], 'fvmptg', '( ( %s e. ( CC X. CC ) /\\ %s e. _V ) -> ( L ` %s ) = %s )' % (OPUV, bod, OPUV, bod))
xp = w.s([uc, vc, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( CC X. CC ) )' % (UVCC, OPUV))
bx = closed(w, UVCC, 'ifex', '%s e. _V' % bod)
w.qed([xp, bx, fv], 'syl2anc', '( %s -> ( L ` %s ) = %s )' % (UVCC, OPUV, bod))
run(w, True)


# ---- gourrcl: closure of the boundary integral over an admissible pair
w = W('gourrcl', 'The boundary integral over an admissible sub-rectangle given as a pair is a complex number.')
FD = '( F e. ( D -cn-> CC ) /\\ ( U crect V ) C_ D )'
ADMQ = '( Q e. ( CC X. CC ) /\\ ( ( Re ` ( 1st ` Q ) ) <_ ( Re ` ( 2nd ` Q ) ) /\\ ( Im ` ( 1st ` Q ) ) <_ ( Im ` ( 2nd ` Q ) ) ) /\\ ( ( 1st ` Q ) crect ( 2nd ` Q ) ) C_ ( U crect V ) )'
A0 = '( %s /\\ %s )' % (FD, ADMQ)
fcn = w.s([], 'simpll', '( %s -> F e. ( D -cn-> CC ) )' % A0)
uvss = w.s([], 'simplr', '( %s -> ( U crect V ) C_ D )' % A0)
qxp = w.s([], 'simpr1', '( %s -> Q e. ( CC X. CC ) )' % A0)
qord = w.s([], 'simpr2', '( %s -> ( ( Re ` ( 1st ` Q ) ) <_ ( Re ` ( 2nd ` Q ) ) /\\ ( Im ` ( 1st ` Q ) ) <_ ( Im ` ( 2nd ` Q ) ) ) )' % A0)
qinc = w.s([], 'simpr3', '( %s -> ( ( 1st ` Q ) crect ( 2nd ` Q ) ) C_ ( U crect V ) )' % A0)
c1 = w.s([qxp, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` Q ) e. CC )' % A0)
c2 = w.s([qxp, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` Q ) e. CC )' % A0)
ssd = w.s([qinc, uvss], 'sstrd', '( %s -> ( ( 1st ` Q ) crect ( 2nd ` Q ) ) C_ D )' % A0)
ps = w.s([w.s([c1, c2], 'jca', '( %s -> ( ( 1st ` Q ) e. CC /\\ ( 2nd ` Q ) e. CC ) )' % A0), qord,
          w.s([fcn, ssd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( ( 1st ` Q ) crect ( 2nd ` Q ) ) C_ D ) )' % A0)], '3jca',
         '( %s -> %s )' % (A0, PSOF('( 1st ` Q )', '( 2nd ` Q )')))
cl = w.s([ps, w.inst('rectintcl')], 'syl', '( %s -> ( F rectint <. ( 1st ` Q ) , ( 2nd ` Q ) >. ) e. CC )' % A0)
q2 = w.s([qxp, w.inst('1st2nd2')], 'syl', '( %s -> Q = <. ( 1st ` Q ) , ( 2nd ` Q ) >. )' % A0)
w.qed([w.s([q2], 'oveq2d', '( %s -> ( F rectint Q ) = ( F rectint <. ( 1st ` Q ) , ( 2nd ` Q ) >. ) )' % A0), cl], 'eqeltrd',
      '( %s -> ( F rectint Q ) e. CC )' % A0); run(w)


# ---- gourqsel: the selector picks an admissible quarter carrying a quarter of the integral
from lin import linarith
w = W('gourqsel', 'The quarter selector returns an admissible quarter whose boundary integral is at least a quarter of the whole.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF)], start=1):
    hyp(w, str(k), 'gourqsel.%s' % nm.lower(), DEF)
A0 = PSOF('U', 'V')
LQ = '( L ` %s )' % OPUV
QUV = '( ( abs ` ( F rectint %s ) ) / 4 )' % OPUV
FD = '( F e. ( D -cn-> CC ) /\\ ( U crect V ) C_ D )'


def ADMQ(q):
    return '( %s e. ( CC X. CC ) /\\ ( ( Re ` ( 1st ` %s ) ) <_ ( Re ` ( 2nd ` %s ) ) /\\ ( Im ` ( 1st ` %s ) ) <_ ( Im ` ( 2nd ` %s ) ) ) /\\ ( ( 1st ` %s ) crect ( 2nd ` %s ) ) C_ ( U crect V ) )' % (q, q, q, q, q, q, q)


uvcc = w.s([], 'simp1', '( %s -> %s )' % (A0, UVCC))
geo = w.s([], 'simp2', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A0, RU, RV, IU, IV))
fcn = w.s([], 'simp3l', '( %s -> F e. ( D -cn-> CC ) )' % A0)
uvss = w.s([], 'simp3r', '( %s -> ( U crect V ) C_ D )' % A0)
admt = w.s([uvcc, geo], 'jca', '( %s -> %s )' % (A0, ADMT))
fd = w.s([fcn, uvss], 'jca', '( %s -> %s )' % (A0, FD))
lv = w.s([uvcc, w.s(['5'], 'gourlval', '( %s -> ( L ` %s ) = %s )' % (UVCC, OPUV, IFUV))], 'syl', '( %s -> %s = %s )' % (A0, LQ, IFUV))
absI = w.s([w.s([], 'rectintcl', '( %s -> ( F rectint %s ) e. CC )' % (A0, OPUV))], 'abscld', '( %s -> ( abs ` ( F rectint %s ) ) e. RR )' % (A0, OPUV))
QI = {}; ABSI = {}; ABSEQ = {}
for k, (num, Fn, DEF, CQ, EQ) in enumerate(QUARTS, start=1):
    GP = '( %s ` %s )' % (Fn, OPUV)
    I = '( F rectint %s )' % GP
    QI[num] = I
    ei = w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, GP, GP))
    gq = w.s([admt, ei, w.s([str(k)], 'gourq' + num, '( ( %s /\\ %s = %s ) -> ( %s /\\ %s ) )' % (ADMT, GP, GP, ADM1(GP), GEO1(GP)))], 'syl2anc',
             '( %s -> ( %s /\\ %s ) )' % (A0, ADM1(GP), GEO1(GP)))
    a1 = w.s([gq, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ADM1(GP)))
    g1 = w.s([gq, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, GEO1(GP)))
    aq = w.s([w.s([a1, w.inst('simpl')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A0, GP)),
              w.s([a1, w.inst('simpr')], 'syl', '( %s -> ( ( Re ` ( 1st ` %s ) ) <_ ( Re ` ( 2nd ` %s ) ) /\\ ( Im ` ( 1st ` %s ) ) <_ ( Im ` ( 2nd ` %s ) ) ) )' % (A0, GP, GP, GP, GP)),
              w.s([g1, w.inst('simpl')], 'syl', '( %s -> ( ( 1st ` %s ) crect ( 2nd ` %s ) ) C_ ( U crect V ) )' % (A0, GP, GP))], '3jca', '( %s -> %s )' % (A0, ADMQ(GP)))
    cl = w.s([fd, aq, w.inst('gourrcl')], 'syl2anc', '( %s -> %s e. CC )' % (A0, I))
    ABSI[num] = w.s([cl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, I))
    vv = w.s([uvcc, w.s([str(k)], 'gourv' + num, '( %s -> %s = <. %s , %s >. )' % (UVCC, GP, CQ, EQ))], 'syl', '( %s -> %s = <. %s , %s >. )' % (A0, GP, CQ, EQ))
    ABSEQ[num] = w.s([w.s([vv], 'oveq2d', '( %s -> %s = ( F rectint <. %s , %s >. ) )' % (A0, I, CQ, EQ))], 'fveq2d',
                     '( %s -> ( abs ` %s ) = ( abs ` ( F rectint <. %s , %s >. ) ) )' % (A0, I, CQ, EQ))
# the triangle inequality over the four quarters
JS = ['( F rectint <. %s , %s >. )' % (c, e) for _n, _f, _d, c, e in QUARTS]
idA = w.s([], 'id', '( %s -> %s )' % (A0, A0))
exMX = closed(w, A0, 'eqid', '%s = %s' % (MX, MX))
eyMY = closed(w, A0, 'eqid', '%s = %s' % (MY, MY))
tri0 = w.s([idA, exMX, eyMY, w.inst('rectintqabs')], 'syl3anc',
           '( %s -> ( abs ` ( F rectint %s ) ) <_ ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A0, OPUV, JS[0], JS[1], JS[2], JS[3]))
sm = w.s([w.s([ABSEQ['1'], ABSEQ['2']], 'oveq12d', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) = ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, QI['1'], QI['2'], JS[0], JS[1])),
            w.s([ABSEQ['3'], ABSEQ['4']], 'oveq12d', '( %s -> ( ( abs ` %s ) + ( abs ` %s ) ) = ( ( abs ` %s ) + ( abs ` %s ) ) )' % (A0, QI['3'], QI['4'], JS[2], JS[3]))], 'oveq12d',
           '( %s -> ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) = ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )'
           % (A0, QI['1'], QI['2'], QI['3'], QI['4'], JS[0], JS[1], JS[2], JS[3]))
tri = w.s([tri0, sm], 'breqtrrd', '( %s -> ( abs ` ( F rectint %s ) ) <_ ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) ) )' % (A0, OPUV, QI['1'], QI['2'], QI['3'], QI['4']))
CONC = '( %s /\\ %s /\\ %s <_ ( abs ` ( F rectint %s ) ) )' % (ADM1(LQ), GEO1(LQ), QUV, LQ)
COND = {n: '%s <_ ( abs ` %s )' % (QUV, QI[n]) for n in '1234'}
IF3 = 'if ( %s , ( J ` %s ) , ( K ` %s ) )' % (COND['3'], OPUV, OPUV)
IF2 = 'if ( %s , ( H ` %s ) , %s )' % (COND['2'], OPUV, IF3)
ENV = [('admt', admt, ADMT), ('fd', fd, FD), ('lv', lv, '%s = %s' % (LQ, IFUV)), ('absI', absI, '( abs ` ( F rectint %s ) ) e. RR' % OPUV),
       ('tri', tri, '( abs ` ( F rectint %s ) ) <_ ( ( ( abs ` %s ) + ( abs ` %s ) ) + ( ( abs ` %s ) + ( abs ` %s ) ) )' % (OPUV, QI['1'], QI['2'], QI['3'], QI['4']))]
for n in '1234':
    ENV.append(('abs' + n, ABSI[n], '( abs ` %s ) e. RR' % QI[n]))


def push(env, lvl):
    return [(k, w.s([st], 'adantr', '( %s -> %s )' % (lvl, f)), f) for k, st, f in env]


def getk(env, k):
    for kk, st, f in env:
        if kk == k:
            return st
    raise KeyError(k)


def mkcase(env, lvl, num, Fn, ifexpr, cndstep, bndsteps=None):
    """close a case where the selector value is ( Fn ` OPUV )"""
    GP = '( %s ` %s )' % (Fn, OPUV)
    t = w.s([cndstep], 'iftrued' if bndsteps is None else 'iffalsed', '( %s -> %s = %s )' % (lvl, ifexpr, GP))
    eq = w.s([getk(env, 'lvcur'), t], 'eqtrd', '( %s -> %s = %s )' % (lvl, LQ, GP))
    gq = w.s([getk(env, 'admt'), eq, w.s([{'G': '1', 'H': '2', 'J': '3', 'K': '4'}[Fn]], 'gourq' + num,
                                         '( ( %s /\\ %s = %s ) -> ( %s /\\ %s ) )' % (ADMT, LQ, GP, ADM1(LQ), GEO1(LQ)))], 'syl2anc',
             '( %s -> ( %s /\\ %s ) )' % (lvl, ADM1(LQ), GEO1(LQ)))
    adm = w.s([gq, w.inst('simpl')], 'syl', '( %s -> %s )' % (lvl, ADM1(LQ)))
    ge = w.s([gq, w.inst('simpr')], 'syl', '( %s -> %s )' % (lvl, GEO1(LQ)))
    fe = w.s([w.s([eq], 'oveq2d', '( %s -> ( F rectint %s ) = %s )' % (lvl, LQ, QI[num]))], 'fveq2d',
             '( %s -> ( abs ` ( F rectint %s ) ) = ( abs ` %s ) )' % (lvl, LQ, QI[num]))
    src = bndsteps if bndsteps is not None else cndstep
    bnd = w.s([src, fe], 'breqtrrd', '( %s -> %s <_ ( abs ` ( F rectint %s ) ) )' % (lvl, QUV, LQ))
    return w.s([adm, ge, bnd], '3jca', '( %s -> %s )' % (lvl, CONC))


# case 1: the first condition holds
LA = '( %s /\\ %s )' % (A0, COND['1'])
eA = push(ENV, LA) + [('lvcur', getk(push(ENV, LA), 'lv'), '')]
eA = push(ENV, LA)
eA.append(('lvcur', getk(eA, 'lv'), ''))
cA = mkcase(eA, LA, '1', 'G', IFUV, w.s([], 'simpr', '( %s -> %s )' % (LA, COND['1'])))
# case 2: not the first, the second
LB = '( %s /\\ -. %s )' % (A0, COND['1'])
eB = push(ENV, LB)
n1B = w.s([], 'simpr', '( %s -> -. %s )' % (LB, COND['1']))
f1 = w.s([n1B], 'iffalsed', '( %s -> %s = %s )' % (LB, IFUV, IF2))
lvB = w.s([getk(eB, 'lv'), f1], 'eqtrd', '( %s -> %s = %s )' % (LB, LQ, IF2))
eB2 = [(k, st, f) for k, st, f in eB] + [('lv2', lvB, '%s = %s' % (LQ, IF2)), ('n1', n1B, '-. %s' % COND['1'])]
LBB = '( %s /\\ %s )' % (LB, COND['2'])
eBB = push(eB2, LBB)
eBB.append(('lvcur', getk(eBB, 'lv2'), ''))
cB = mkcase(eBB, LBB, '2', 'H', IF2, w.s([], 'simpr', '( %s -> %s )' % (LBB, COND['2'])))
# case 3: not the first two, the third
LBN = '( %s /\\ -. %s )' % (LB, COND['2'])
eBN = push(eB2, LBN)
n2 = w.s([], 'simpr', '( %s -> -. %s )' % (LBN, COND['2']))
f2 = w.s([n2], 'iffalsed', '( %s -> %s = %s )' % (LBN, IF2, IF3))
lvBN = w.s([getk(eBN, 'lv2'), f2], 'eqtrd', '( %s -> %s = %s )' % (LBN, LQ, IF3))
eBN2 = [(k, st, f) for k, st, f in eBN] + [('lv3', lvBN, '%s = %s' % (LQ, IF3)), ('n2', n2, '-. %s' % COND['2'])]
LBNB = '( %s /\\ %s )' % (LBN, COND['3'])
eBNB = push(eBN2, LBNB)
eBNB.append(('lvcur', getk(eBNB, 'lv3'), ''))
cBN = mkcase(eBNB, LBNB, '3', 'J', IF3, w.s([], 'simpr', '( %s -> %s )' % (LBNB, COND['3'])))
# case 4: none of the three
LBNN = '( %s /\\ -. %s )' % (LBN, COND['3'])
eBNN = push(eBN2, LBNN)
n3 = w.s([], 'simpr', '( %s -> -. %s )' % (LBNN, COND['3']))
qre = w.s([getk(eBNN, 'absI'), closed(w, LBNN, '4re', '4 e. RR'), closed(w, LBNN, '4ne0', '4 =/= 0')], 'redivcld', '( %s -> %s e. RR )' % (LBNN, QUV))
LVS = {}
for n in '123':
    ns = {'1': getk(eBNN, 'n1'), '2': getk(eBNN, 'n2'), '3': n3}[n]
    lt = w.s([w.s([getk(eBNN, 'abs' + n), qre], 'ltnled', '( %s -> ( ( abs ` %s ) < %s <-> -. %s <_ ( abs ` %s ) ) )' % (LBNN, QI[n], QUV, QUV, QI[n])), ns], 'mpbird',
             '( %s -> ( abs ` %s ) < %s )' % (LBNN, QI[n], QUV))
    LVS[n] = lt
LEAVES = {'( abs ` ( F rectint %s ) )' % OPUV: getk(eBNN, 'absI')}
for n in '1234':
    LEAVES['( abs ` %s )' % QI[n]] = getk(eBNN, 'abs' + n)
b4 = linarith(w, LBNN, [getk(eBNN, 'tri'), LVS['1'], LVS['2'], LVS['3']], '%s <_ ( abs ` %s )' % (QUV, QI['4']), leaves=LEAVES)
eBNN.append(('lvcur', getk(eBNN, 'lv3'), ''))
cBNN = mkcase(eBNN, LBNN, '4', 'K', IF3, n3, bndsteps=b4)
# assemble the case tree
r3 = w.s([cBN, cBNN], 'pm2.61dan', '( %s -> %s )' % (LBN, CONC))
r2 = w.s([cB, r3], 'pm2.61dan', '( %s -> %s )' % (LB, CONC))
w.qed([cA, r2], 'pm2.61dan', '( %s -> %s )' % (A0, CONC))
run(w, True)


# ---- gourstep: one step of the nested-rectangle recursion
def NK(k): return '( N ` %s )' % k
def F1(q): return '( 1st ` %s )' % q
def F2(q): return '( 2nd ` %s )' % q
def INVQ(q):
    return ('( %s e. ( CC X. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( %s crect %s ) C_ ( A crect B ) )'
            % (q, F1(q), F2(q), F1(q), F2(q), F1(q), F2(q)))
def ADM1Q(q, u, v):
    return '( %s e. ( CC X. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (q, F1(q), F2(q), F1(q), F2(q))
def GEO1Q(q, u, v):
    return ('( ( %s crect %s ) C_ ( %s crect %s ) /\\ ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ ( ( ( Re ` %s ) - ( Re ` %s ) ) / 2 ) /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ ( ( ( Im ` %s ) - ( Im ` %s ) ) / 2 ) ) )'
            % (F1(q), F2(q), u, v, F2(q), F1(q), v, u, F2(q), F1(q), v, u))
def BNDQ(q, p):
    return '( ( abs ` ( F rectint %s ) ) / 4 ) <_ ( abs ` ( F rectint %s ) )' % (p, q)

w = W('gourstep', 'One step of the nested-rectangle recursion: the next rectangle is an admissible quarter of the current one.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gourstep.%s' % nm.lower(), DEF)
NKK = NK('M'); NK1 = NK('( M + 1 )')
UU = F1(NKK); VV = F2(NKK)
A0 = '( %s /\\ M e. NN0 /\\ %s )' % (PS, INVQ(NKK))
ps = w.s([], 'simp1', '( %s -> %s )' % (A0, PS))
kn = w.s([], 'simp2', '( %s -> M e. NN0 )' % A0)
inv = w.s([], 'simp3', '( %s -> %s )' % (A0, INVQ(NKK)))
xpk = w.s([inv, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A0, NKK))
ordk = w.s([inv, w.inst('simp2')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, UU, VV, UU, VV))
inck = w.s([inv, w.inst('simp3')], 'syl', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A0, UU, VV))
fcn = w.s([ps, w.inst('simp3l')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
rss = w.s([ps, w.inst('simp3r')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
uc = w.s([xpk, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (A0, UU))
vc = w.s([xpk, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (A0, VV))
ssd = w.s([inck, rss], 'sstrd', '( %s -> ( %s crect %s ) C_ D )' % (A0, UU, VV))
psuv = w.s([w.s([uc, vc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, UU, VV)), ordk,
            w.s([fcn, ssd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ D ) )' % (A0, UU, VV))], '3jca',
           '( %s -> %s )' % (A0, PSOF(UU, VV)))
OPK = '<. %s , %s >.' % (UU, VV)
LUV = '( L ` %s )' % OPK
seli = w.s(['1', '2', '3', '4', '5'], 'gourqsel', '( %s -> ( %s /\\ %s /\\ %s ) )' % (PSOF(UU, VV), ADM1Q(LUV, UU, VV), GEO1Q(LUV, UU, VV), BNDQ(LUV, OPK)))
sel = w.s([psuv, seli], 'syl', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, ADM1Q(LUV, UU, VV), GEO1Q(LUV, UU, VV), BNDQ(LUV, OPK)))
s1 = w.s([sel, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, ADM1Q(LUV, UU, VV)))
s2 = w.s([sel, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, GEO1Q(LUV, UU, VV)))
s3 = w.s([sel, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, BNDQ(LUV, OPK)))
# identify ( N ` ( M + 1 ) ) with ( L ` <. u , v >. )
npi = w.s(['6'], 'gournp1', '( M e. NN0 -> %s = ( L ` %s ) )' % (NK1, NKK))
np = w.s([kn, npi], 'syl', '( %s -> %s = ( L ` %s ) )' % (A0, NK1, NKK))
pq = w.s([xpk, w.inst('1st2nd2')], 'syl', '( %s -> %s = %s )' % (A0, NKK, OPK))
nq = w.s([np, w.s([pq], 'fveq2d', '( %s -> ( L ` %s ) = %s )' % (A0, NKK, LUV))], 'eqtrd', '( %s -> %s = %s )' % (A0, NK1, LUV))
nqc = w.s([nq], 'eqcomd', '( %s -> %s = %s )' % (A0, LUV, NK1))
pqc = w.s([pq], 'eqcomd', '( %s -> %s = %s )' % (A0, OPK, NKK))
t1, _ = w.wcongr(ADM1Q(LUV, UU, VV), {}, A0, {}, rules={LUV: (NK1, nqc)})
r1 = w.s([s1, t1], 'mpbid', '( %s -> %s )' % (A0, ADM1Q(NK1, UU, VV)))
t2, _ = w.wcongr(GEO1Q(LUV, UU, VV), {}, A0, {}, rules={LUV: (NK1, nqc)})
r2 = w.s([s2, t2], 'mpbid', '( %s -> %s )' % (A0, GEO1Q(NK1, UU, VV)))
t3, _ = w.wcongr(BNDQ(LUV, OPK), {}, A0, {}, rules={LUV: (NK1, nqc), OPK: (NKK, pqc)})
r3 = w.s([s3, t3], 'mpbid', '( %s -> %s )' % (A0, BNDQ(NK1, NKK)))
# the invariant at M + 1
xp1 = w.s([r1, w.inst('simpl')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A0, NK1))
or1 = w.s([r1, w.inst('simpr')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, F1(NK1), F2(NK1), F1(NK1), F2(NK1)))
in1 = w.s([r2, w.inst('simpl')], 'syl', '( %s -> ( %s crect %s ) C_ ( %s crect %s ) )' % (A0, F1(NK1), F2(NK1), UU, VV))
wd1 = w.s([r2, w.inst('simpr')], 'syl', '( %s -> ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ ( ( ( Re ` %s ) - ( Re ` %s ) ) / 2 ) /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ ( ( ( Im ` %s ) - ( Im ` %s ) ) / 2 ) ) )'
           % (A0, F2(NK1), F1(NK1), VV, UU, F2(NK1), F1(NK1), VV, UU))
inA = w.s([in1, inck], 'sstrd', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A0, F1(NK1), F2(NK1)))
invp = w.s([xp1, or1, inA], '3jca', '( %s -> %s )' % (A0, INVQ(NK1)))
w.qed([invp, w.s([in1, wd1], 'jca', '( %s -> %s )' % (A0, GEO1Q(NK1, UU, VV))), r3], '3jca',
      '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, INVQ(NK1), GEO1Q(NK1, UU, VV), BNDQ(NK1, NKK)))
run(w, True)


def indsub(w, prop, sub, pre=PS):
    """( x = sub -> ( ( pre -> prop(x) ) <-> ( pre -> prop(sub) ) ) ); returns (step, prop(sub))"""
    idp = w.s([], 'id', '( x = %s -> x = %s )' % (sub, sub))
    st, new = w.wcongr(prop, {'x': sub}, 'x = %s' % sub, {'x': idp})
    st2 = w.s([st], 'imbi2d', '( x = %s -> ( ( %s -> %s ) <-> ( %s -> %s ) ) )' % (sub, pre, prop, pre, new))
    return st2, new


# ---- gouradm: every rectangle of the sequence is admissible
w = W('gouradm', 'Every rectangle of the nested sequence is an admissible sub-rectangle.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gouradm.%s' % nm.lower(), DEF)
PROP = INVQ(NK('x'))
h1, p0 = indsub(w, PROP, '0')
h2, py = indsub(w, PROP, 'y')
h3, py1 = indsub(w, PROP, '( y + 1 )')
h4, pM = indsub(w, PROP, 'M')
# base case
OPAB = '<. A , B >.'
n0 = w.s(['6'], 'gourn0', '( N ` 0 ) = %s' % OPAB)
ac = w.s([], 'simp1l', '( %s -> A e. CC )' % PS)
bc = w.s([], 'simp1r', '( %s -> B e. CC )' % PS)
ler = w.s([], 'simp2l', '( %s -> %s <_ %s )' % (PS, RE('A'), RE('B')))
lei = w.s([], 'simp2r', '( %s -> %s <_ %s )' % (PS, IM('A'), IM('B')))
xpb = w.s([ac, bc, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( CC X. CC ) )' % (PS, OPAB))
o1 = w.s([ac, bc, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = A )' % (PS, OPAB))
o2 = w.s([ac, bc, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = B )' % (PS, OPAB))
br1 = w.s([ler, w.s([o1], 'fveq2d', '( %s -> ( Re ` ( 1st ` %s ) ) = %s )' % (PS, OPAB, RE('A'))), w.s([o2], 'fveq2d', '( %s -> ( Re ` ( 2nd ` %s ) ) = %s )' % (PS, OPAB, RE('B')))], '3brtr4d',
           '( %s -> ( Re ` ( 1st ` %s ) ) <_ ( Re ` ( 2nd ` %s ) ) )' % (PS, OPAB, OPAB))
br2 = w.s([lei, w.s([o1], 'fveq2d', '( %s -> ( Im ` ( 1st ` %s ) ) = %s )' % (PS, OPAB, IM('A'))), w.s([o2], 'fveq2d', '( %s -> ( Im ` ( 2nd ` %s ) ) = %s )' % (PS, OPAB, IM('B')))], '3brtr4d',
           '( %s -> ( Im ` ( 1st ` %s ) ) <_ ( Im ` ( 2nd ` %s ) ) )' % (PS, OPAB, OPAB))
ssi = closed(w, PS, 'ssid', '( A crect B ) C_ ( A crect B )')
inb = w.s([w.s([o1, o2], 'oveq12d', '( %s -> ( ( 1st ` %s ) crect ( 2nd ` %s ) ) = ( A crect B ) )' % (PS, OPAB, OPAB)), ssi], 'eqsstrd',
          '( %s -> ( ( 1st ` %s ) crect ( 2nd ` %s ) ) C_ ( A crect B ) )' % (PS, OPAB, OPAB))
ib = w.s([xpb, w.s([br1, br2], 'jca', '( %s -> ( ( Re ` ( 1st ` %s ) ) <_ ( Re ` ( 2nd ` %s ) ) /\\ ( Im ` ( 1st ` %s ) ) <_ ( Im ` ( 2nd ` %s ) ) ) )' % (PS, OPAB, OPAB, OPAB, OPAB)), inb], '3jca',
         '( %s -> %s )' % (PS, INVQ(OPAB)))
n0d = w.s([w.s([n0], 'a1i', '( %s -> ( N ` 0 ) = %s )' % (PS, OPAB))], 'eqcomd', '( %s -> %s = ( N ` 0 ) )' % (PS, OPAB))
tb, _ = w.wcongr(INVQ(OPAB), {}, PS, {}, rules={OPAB: ('( N ` 0 )', n0d)})
base = w.s([ib, tb], 'mpbid', '( %s -> %s )' % (PS, p0))
# induction step
LS = '( ( y e. NN0 /\\ ( %s -> %s ) ) /\\ %s )' % (PS, py, PS)
psl = w.s([], 'simpr', '( %s -> %s )' % (LS, PS))
ynn = w.s([], 'simpll', '( %s -> y e. NN0 )' % LS)
ihy = w.s([psl, w.s([], 'simplr', '( %s -> ( %s -> %s ) )' % (LS, PS, py))], 'mpd', '( %s -> %s )' % (LS, py))
sti = w.s(['1', '2', '3', '4', '5', '6'], 'gourstep', '( ( %s /\\ y e. NN0 /\\ %s ) -> ( %s /\\ %s /\\ %s ) )' % (PS, py, py1, GEO1Q(NK('( y + 1 )'), F1(NK('y')), F2(NK('y'))), BNDQ(NK('( y + 1 )'), NK('y'))))
stp = w.s([psl, ynn, ihy, sti], 'syl3anc', '( %s -> ( %s /\\ %s /\\ %s ) )' % (LS, py1, GEO1Q(NK('( y + 1 )'), F1(NK('y')), F2(NK('y'))), BNDQ(NK('( y + 1 )'), NK('y'))))
i1 = w.s([stp, w.inst('simp1')], 'syl', '( %s -> %s )' % (LS, py1))
e1 = w.s([i1], 'ex', '( ( y e. NN0 /\\ ( %s -> %s ) ) -> ( %s -> %s ) )' % (PS, py, PS, py1))
e2 = w.s([e1], 'ex', '( y e. NN0 -> ( ( %s -> %s ) -> ( %s -> %s ) ) )' % (PS, py, PS, py1))
ind = w.s([h1, h2, h3, h4, base, e2], 'nn0ind', '( M e. NN0 -> ( %s -> %s ) )' % (PS, pM))
w.qed([w.s([ind], 'com12', '( %s -> ( M e. NN0 -> %s ) )' % (PS, pM))], 'imp', '( ( %s /\\ M e. NN0 ) -> %s )' % (PS, pM))
run(w, True)


# ---- gournest: the rectangles of the sequence are nested
w = W('gournest', 'The rectangles of the nested sequence decrease.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gournest.%s' % nm.lower(), DEF)
CTX = '( %s /\\ P e. NN0 )' % PS
def RJ(j): return '( ( 1st ` ( N ` %s ) ) crect ( 2nd ` ( N ` %s ) ) )' % (j, j)
PROPJ = '%s C_ %s' % (RJ('j'), RJ('P'))


def jsub(w, sub):
    idp = w.s([], 'id', '( j = %s -> j = %s )' % (sub, sub))
    st, new = w.wcongr(PROPJ, {'j': sub}, 'j = %s' % sub, {'j': idp})
    st2 = w.s([st], 'imbi2d', '( j = %s -> ( ( %s -> %s ) <-> ( %s -> %s ) ) )' % (sub, CTX, PROPJ, CTX, new))
    return st2, new


h1, pPbase = jsub(w, 'P')
h2, pk = jsub(w, 'k')
h3, pk1 = jsub(w, '( k + 1 )')
h4, pM = jsub(w, 'M')
bss = w.s([], 'ssid', '%s C_ %s' % (RJ('P'), RJ('P')))
bs = w.s([w.s([bss], 'a1i', '( %s -> %s )' % (CTX, pPbase))], 'a1i', '( P e. ZZ -> ( %s -> %s ) )' % (CTX, pPbase))
TRI = '( P e. ZZ /\\ k e. ZZ /\\ P <_ k )'
PHK = '( %s -> %s )' % (CTX, pk)
LV = '( ( %s /\\ %s ) /\\ %s )' % (TRI, PHK, CTX)
ctx = w.s([], 'simpr', '( %s -> %s )' % (LV, CTX))
tri = w.s([], 'simpll', '( %s -> %s )' % (LV, TRI))
phk = w.s([], 'simplr', '( %s -> %s )' % (LV, PHK))
ihk = w.s([ctx, phk], 'mpd', '( %s -> %s )' % (LV, pk))
kz = w.s([tri, w.inst('simp2')], 'syl', '( %s -> k e. ZZ )' % LV)
Kle = w.s([tri, w.inst('simp3')], 'syl', '( %s -> P <_ k )' % LV)
psl = w.s([ctx, w.inst('simpl')], 'syl', '( %s -> %s )' % (LV, PS))
knn = w.s([ctx, w.inst('simpr')], 'syl', '( %s -> P e. NN0 )' % LV)
Kge = w.s([knn, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ P )' % LV)
kre = w.s([kz, w.inst('zred')], 'syl', '( %s -> k e. RR )' % LV)
Kre = w.s([knn, w.inst('nn0red')], 'syl', '( %s -> P e. RR )' % LV)
z0 = closed(w, LV, '0re', '0 e. RR')
kge = w.s([z0, Kre, kre, Kge, Kle], 'letrd', '( %s -> 0 <_ k )' % LV)
knn0 = w.s([w.s([kz, kge], 'jca', '( %s -> ( k e. ZZ /\\ 0 <_ k ) )' % LV), w.s([w.s([], 'elnn0z', '( k e. NN0 <-> ( k e. ZZ /\\ 0 <_ k ) )')], 'a1i', '( %s -> ( k e. NN0 <-> ( k e. ZZ /\\ 0 <_ k ) ) )' % LV)], 'mpbird', '( %s -> k e. NN0 )' % LV)
admi = w.s(['1', '2', '3', '4', '5', '6'], 'gouradm', '( ( %s /\\ k e. NN0 ) -> %s )' % (PS, INVQ(NK('k'))))
inv = w.s([psl, knn0, admi], 'syl2anc', '( %s -> %s )' % (LV, INVQ(NK('k'))))
sti = w.s(['1', '2', '3', '4', '5', '6'], 'gourstep', '( ( %s /\\ k e. NN0 /\\ %s ) -> ( %s /\\ %s /\\ %s ) )' % (PS, INVQ(NK('k')), INVQ(NK('( k + 1 )')), GEO1Q(NK('( k + 1 )'), F1(NK('k')), F2(NK('k'))), BNDQ(NK('( k + 1 )'), NK('k'))))
stp = w.s([psl, knn0, inv, sti], 'syl3anc', '( %s -> ( %s /\\ %s /\\ %s ) )' % (LV, INVQ(NK('( k + 1 )')), GEO1Q(NK('( k + 1 )'), F1(NK('k')), F2(NK('k'))), BNDQ(NK('( k + 1 )'), NK('k'))))
one = w.s([w.s([stp, w.inst('simp2')], 'syl', '( %s -> %s )' % (LV, GEO1Q(NK('( k + 1 )'), F1(NK('k')), F2(NK('k'))))), w.inst('simpl')], 'syl', '( %s -> %s C_ %s )' % (LV, RJ('( k + 1 )'), RJ('k')))
res = w.s([one, ihk], 'sstrd', '( %s -> %s )' % (LV, pk1))
st6 = w.s([w.s([res], 'ex', '( ( %s /\\ %s ) -> ( %s -> %s ) )' % (TRI, PHK, CTX, pk1))], 'ex', '( %s -> ( %s -> ( %s -> %s ) ) )' % (TRI, PHK, CTX, pk1))
uzi = w.s([h1, h2, h3, h4, bs, st6], 'uzind', '( ( P e. ZZ /\\ M e. ZZ /\\ P <_ M ) -> ( %s -> %s ) )' % (CTX, pM))
A0 = '( %s /\\ P e. NN0 /\\ M e. ( ZZ>= ` P ) )' % PS
ps2 = w.s([], 'simp1', '( %s -> %s )' % (A0, PS))
kn2 = w.s([], 'simp2', '( %s -> P e. NN0 )' % A0)
mu = w.s([], 'simp3', '( %s -> M e. ( ZZ>= ` P ) )' % A0)
kz2 = w.s([kn2, w.inst('nn0z')], 'syl', '( %s -> P e. ZZ )' % A0)
mz2 = w.s([mu, w.inst('eluzelz')], 'syl', '( %s -> M e. ZZ )' % A0)
kle2 = w.s([mu, w.inst('eluzle')], 'syl', '( %s -> P <_ M )' % A0)
ct2 = w.s([ps2, kn2], 'jca', '( %s -> %s )' % (A0, CTX))
w.qed([ct2, w.s([kz2, mz2, kle2, uzi], 'syl3anc', '( %s -> ( %s -> %s ) )' % (A0, CTX, pM))], 'mpd', '( %s -> %s )' % (A0, pM))
run(w, True)


# ---- gourwid: the side lengths of the sequence shrink geometrically
WDT = '( %s - %s )' % (RE('B'), RE('A')); HGT = '( %s - %s )' % (IM('B'), IM('A'))
def SD(x, part, tot):
    return '( ( %s ` %s ) - ( %s ` %s ) ) <_ ( %s / ( 2 ^ %s ) )' % (part, F2(NK(x)), part, F1(NK(x)), tot, x)
def PW(x):
    return '( %s /\\ %s )' % (SD(x, 'Re', WDT), SD(x, 'Im', HGT))

w = W('gourwid', 'The side lengths of the nested rectangles shrink like a power of one half.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gourwid.%s' % nm.lower(), DEF)
PROP = PW('x')
h1, p0 = indsub(w, PROP, '0')
h2, py = indsub(w, PROP, 'y')
h3, py1 = indsub(w, PROP, '( y + 1 )')
h4, pM = indsub(w, PROP, 'M')
# --- base case
OPAB = '<. A , B >.'
ac = w.s([], 'simp1l', '( %s -> A e. CC )' % PS)
bc = w.s([], 'simp1r', '( %s -> B e. CC )' % PS)
n0 = w.s([w.s(['6'], 'gourn0', '( N ` 0 ) = %s' % OPAB)], 'a1i', '( %s -> ( N ` 0 ) = %s )' % (PS, OPAB))
o1 = w.s([n0, w.s([ac, bc, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = A )' % (PS, OPAB))], 'eqtrd' if False else 'eqtrd', '( %s -> ( 1st ` ( N ` 0 ) ) = A )' % PS)
w.lines.pop()
f1e = w.s([n0], 'fveq2d', '( %s -> ( 1st ` ( N ` 0 ) ) = ( 1st ` %s ) )' % (PS, OPAB))
f2e = w.s([n0], 'fveq2d', '( %s -> ( 2nd ` ( N ` 0 ) ) = ( 2nd ` %s ) )' % (PS, OPAB))
o1 = w.s([f1e, w.s([ac, bc, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = A )' % (PS, OPAB))], 'eqtrd', '( %s -> ( 1st ` ( N ` 0 ) ) = A )' % PS)
o2 = w.s([f2e, w.s([ac, bc, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = B )' % (PS, OPAB))], 'eqtrd', '( %s -> ( 2nd ` ( N ` 0 ) ) = B )' % PS)
t2c = closed(w, PS, '2cn', '2 e. CC')
e20 = w.s([t2c, w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % PS)
b0 = []
for part, tot, cl in (('Re', WDT, 'recl'), ('Im', HGT, 'imcl')):
    ar = w.s([ac, w.inst(cl)], 'syl', '( %s -> ( %s ` A ) e. RR )' % (PS, part))
    br = w.s([bc, w.inst(cl)], 'syl', '( %s -> ( %s ` B ) e. RR )' % (PS, part))
    tr = w.s([br, ar], 'resubcld', '( %s -> %s e. RR )' % (PS, tot))
    lhs = w.s([w.s([o2], 'fveq2d', '( %s -> ( %s ` ( 2nd ` ( N ` 0 ) ) ) = ( %s ` B ) )' % (PS, part, part)),
               w.s([o1], 'fveq2d', '( %s -> ( %s ` ( 1st ` ( N ` 0 ) ) ) = ( %s ` A ) )' % (PS, part, part))], 'oveq12d',
              '( %s -> ( ( %s ` ( 2nd ` ( N ` 0 ) ) ) - ( %s ` ( 1st ` ( N ` 0 ) ) ) ) = %s )' % (PS, part, part, tot))
    rhs = w.s([w.s([e20], 'oveq2d', '( %s -> ( %s / ( 2 ^ 0 ) ) = ( %s / 1 ) )' % (PS, tot, tot)), w.s([w.s([tr], 'recnd', '( %s -> %s e. CC )' % (PS, tot))], 'div1d', '( %s -> ( %s / 1 ) = %s )' % (PS, tot, tot))], 'eqtrd',
              '( %s -> ( %s / ( 2 ^ 0 ) ) = %s )' % (PS, tot, tot))
    b0.append(w.s([w.s([tr], 'leidd', '( %s -> %s <_ %s )' % (PS, tot, tot)), lhs, rhs], '3brtr4d', '( %s -> %s )' % (PS, SD('0', part, tot))))
base = w.s([b0[0], b0[1]], 'jca', '( %s -> %s )' % (PS, p0))
# --- induction step
LS = '( ( y e. NN0 /\\ ( %s -> %s ) ) /\\ %s )' % (PS, py, PS)
psl = w.s([], 'simpr', '( %s -> %s )' % (LS, PS))
ynn = w.s([], 'simpll', '( %s -> y e. NN0 )' % LS)
ihy = w.s([psl, w.s([], 'simplr', '( %s -> ( %s -> %s ) )' % (LS, PS, py))], 'mpd', '( %s -> %s )' % (LS, py))
acl = w.s([psl, w.inst('simp1l')], 'syl', '( %s -> A e. CC )' % LS)
bcl = w.s([psl, w.inst('simp1r')], 'syl', '( %s -> B e. CC )' % LS)
admi = w.s(['1', '2', '3', '4', '5', '6'], 'gouradm', '( ( %s /\\ y e. NN0 ) -> %s )' % (PS, INVQ(NK('y'))))
inv = w.s([psl, ynn, admi], 'syl2anc', '( %s -> %s )' % (LS, INVQ(NK('y'))))
xpy = w.s([inv, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (LS, NK('y')))
u1 = w.s([xpy, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (LS, F1(NK('y'))))
u2 = w.s([xpy, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (LS, F2(NK('y'))))
sti = w.s(['1', '2', '3', '4', '5', '6'], 'gourstep', '( ( %s /\\ y e. NN0 /\\ %s ) -> ( %s /\\ %s /\\ %s ) )' % (PS, INVQ(NK('y')), INVQ(NK('( y + 1 )')), GEO1Q(NK('( y + 1 )'), F1(NK('y')), F2(NK('y'))), BNDQ(NK('( y + 1 )'), NK('y'))))
stp = w.s([psl, ynn, inv, sti], 'syl3anc', '( %s -> ( %s /\\ %s /\\ %s ) )' % (LS, INVQ(NK('( y + 1 )')), GEO1Q(NK('( y + 1 )'), F1(NK('y')), F2(NK('y'))), BNDQ(NK('( y + 1 )'), NK('y'))))
g2 = w.s([w.s([stp, w.inst('simp2')], 'syl', '( %s -> %s )' % (LS, GEO1Q(NK('( y + 1 )'), F1(NK('y')), F2(NK('y'))))), w.inst('simpr')], 'syl',
         '( %s -> ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ ( ( ( Re ` %s ) - ( Re ` %s ) ) / 2 ) /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ ( ( ( Im ` %s ) - ( Im ` %s ) ) / 2 ) ) )'
         % (LS, F2(NK('( y + 1 )')), F1(NK('( y + 1 )')), F2(NK('y')), F1(NK('y')), F2(NK('( y + 1 )')), F1(NK('( y + 1 )')), F2(NK('y')), F1(NK('y'))))
xpy1 = w.s([w.s([stp, w.inst('simp1')], 'syl', '( %s -> %s )' % (LS, INVQ(NK('( y + 1 )')))), w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (LS, NK('( y + 1 )')))
v1 = w.s([xpy1, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (LS, F1(NK('( y + 1 )'))))
v2 = w.s([xpy1, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (LS, F2(NK('( y + 1 )'))))
rp2 = closed(w, LS, '2rp', '2 e. RR+')
ey = w.s([rp2, w.s([ynn, w.inst('nn0z')], 'syl', '( %s -> y e. ZZ )' % LS)], 'rpexpcld', '( %s -> ( 2 ^ y ) e. RR+ )' % LS)
t2cl = closed(w, LS, '2cn', '2 e. CC')
ex1 = w.s([t2cl, ynn], 'expp1d', '( %s -> ( 2 ^ ( y + 1 ) ) = ( ( 2 ^ y ) x. 2 ) )' % LS)
res = []
for idx, (part, tot, cl) in enumerate((('Re', WDT, 'recl'), ('Im', HGT, 'imcl'))):
    ihp = w.s([ihy, w.inst('simpl' if idx == 0 else 'simpr')], 'syl', '( %s -> %s )' % (LS, SD('y', part, tot)))
    gp = w.s([g2, w.inst('simpl' if idx == 0 else 'simpr')], 'syl',
             '( %s -> ( ( %s ` %s ) - ( %s ` %s ) ) <_ ( ( ( %s ` %s ) - ( %s ` %s ) ) / 2 ) )' % (LS, part, F2(NK('( y + 1 )')), part, F1(NK('( y + 1 )')), part, F2(NK('y')), part, F1(NK('y'))))
    ar = w.s([acl, w.inst(cl)], 'syl', '( %s -> ( %s ` A ) e. RR )' % (LS, part))
    br = w.s([bcl, w.inst(cl)], 'syl', '( %s -> ( %s ` B ) e. RR )' % (LS, part))
    tr = w.s([br, ar], 'resubcld', '( %s -> %s e. RR )' % (LS, tot))
    p1r = w.s([w.s([u2, w.inst(cl)], 'syl', '( %s -> ( %s ` %s ) e. RR )' % (LS, part, F2(NK('y')))), w.s([u1, w.inst(cl)], 'syl', '( %s -> ( %s ` %s ) e. RR )' % (LS, part, F1(NK('y'))))], 'resubcld',
              '( %s -> ( ( %s ` %s ) - ( %s ` %s ) ) e. RR )' % (LS, part, F2(NK('y')), part, F1(NK('y'))))
    p2r = w.s([w.s([v2, w.inst(cl)], 'syl', '( %s -> ( %s ` %s ) e. RR )' % (LS, part, F2(NK('( y + 1 )')))), w.s([v1, w.inst(cl)], 'syl', '( %s -> ( %s ` %s ) e. RR )' % (LS, part, F1(NK('( y + 1 )'))))], 'resubcld',
              '( %s -> ( ( %s ` %s ) - ( %s ` %s ) ) e. RR )' % (LS, part, F2(NK('( y + 1 )')), part, F1(NK('( y + 1 )'))))
    qr = w.s([tr, ey], 'rerpdivcld', '( %s -> ( %s / ( 2 ^ y ) ) e. RR )' % (LS, tot))
    d1 = w.s([w.s([p1r, qr, rp2], 'lediv1d', '( %s -> ( ( ( %s ` %s ) - ( %s ` %s ) ) <_ ( %s / ( 2 ^ y ) ) <-> ( ( ( %s ` %s ) - ( %s ` %s ) ) / 2 ) <_ ( ( %s / ( 2 ^ y ) ) / 2 ) ) )'
                  % (LS, part, F2(NK('y')), part, F1(NK('y')), tot, part, F2(NK('y')), part, F1(NK('y')), tot)), ihp], 'mpbid',
             '( %s -> ( ( ( %s ` %s ) - ( %s ` %s ) ) / 2 ) <_ ( ( %s / ( 2 ^ y ) ) / 2 ) )' % (LS, part, F2(NK('y')), part, F1(NK('y')), tot))
    dd = w.s([w.s([tr], 'recnd', '( %s -> %s e. CC )' % (LS, tot)), w.s([ey, w.inst('rpcnd' if False else 'rpcn')], 'syl', '( %s -> ( 2 ^ y ) e. CC )' % LS), w.s([ey, w.inst('rpne0')], 'syl', '( %s -> ( 2 ^ y ) =/= 0 )' % LS), t2cl, closed(w, LS, '2ne0', '2 =/= 0')], 'divdiv1d',
             '( %s -> ( ( %s / ( 2 ^ y ) ) / 2 ) = ( %s / ( ( 2 ^ y ) x. 2 ) ) )' % (LS, tot, tot))
    rw = w.s([w.s([ex1], 'oveq2d', '( %s -> ( %s / ( 2 ^ ( y + 1 ) ) ) = ( %s / ( ( 2 ^ y ) x. 2 ) ) )' % (LS, tot, tot))], 'eqcomd', '( %s -> ( %s / ( ( 2 ^ y ) x. 2 ) ) = ( %s / ( 2 ^ ( y + 1 ) ) )' % (LS, tot, tot) + ' )')
    d2 = w.s([d1, w.s([dd, rw], 'eqtrd', '( %s -> ( ( %s / ( 2 ^ y ) ) / 2 ) = ( %s / ( 2 ^ ( y + 1 ) ) ) )' % (LS, tot, tot))], 'breqtrd',
             '( %s -> ( ( ( %s ` %s ) - ( %s ` %s ) ) / 2 ) <_ ( %s / ( 2 ^ ( y + 1 ) ) ) )' % (LS, part, F2(NK('y')), part, F1(NK('y')), tot))
    hr = w.s([p1r], 'rehalfcld', '( %s -> ( ( ( %s ` %s ) - ( %s ` %s ) ) / 2 ) e. RR )' % (LS, part, F2(NK('y')), part, F1(NK('y'))))
    qr1 = w.s([tr, w.s([rp2, w.s([w.s([ynn, w.inst('nn0p1nn')], 'syl', '( %s -> ( y + 1 ) e. NN )' % LS), w.inst('nnzd' if False else 'nnz')], 'syl', '( %s -> ( y + 1 ) e. ZZ )' % LS)], 'rpexpcld', '( %s -> ( 2 ^ ( y + 1 ) ) e. RR+ )' % LS)], 'rerpdivcld',
               '( %s -> ( %s / ( 2 ^ ( y + 1 ) ) ) e. RR )' % (LS, tot))
    res.append(w.s([p2r, hr, qr1, gp, d2], 'letrd', '( %s -> %s )' % (LS, SD('( y + 1 )', part, tot))))
stepc = w.s([res[0], res[1]], 'jca', '( %s -> %s )' % (LS, py1))
e2 = w.s([w.s([stepc], 'ex', '( ( y e. NN0 /\\ ( %s -> %s ) ) -> ( %s -> %s ) )' % (PS, py, PS, py1))], 'ex', '( y e. NN0 -> ( ( %s -> %s ) -> ( %s -> %s ) ) )' % (PS, py, PS, py1))
ind = w.s([h1, h2, h3, h4, base, e2], 'nn0ind', '( M e. NN0 -> ( %s -> %s ) )' % (PS, pM))
w.qed([w.s([ind], 'com12', '( %s -> ( M e. NN0 -> %s ) )' % (PS, pM))], 'imp', '( ( %s /\\ M e. NN0 ) -> %s )' % (PS, pM))
run(w, True)


# ---- gourabs: the boundary integrals of the sequence stay large
OPAB = '<. A , B >.'
IAB = '( F rectint %s )' % OPAB
def PA(x):
    return '( ( abs ` %s ) / ( 4 ^ %s ) ) <_ ( abs ` ( F rectint %s ) )' % (IAB, x, NK(x))

w = W('gourabs', 'The boundary integrals of the nested rectangles are at least a fourth power of the first.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gourabs.%s' % nm.lower(), DEF)
PROP = PA('x')
h1, p0 = indsub(w, PROP, '0')
h2, py = indsub(w, PROP, 'y')
h3, py1 = indsub(w, PROP, '( y + 1 )')
h4, pM = indsub(w, PROP, 'M')
# --- base case
iab = w.s([w.s([], 'rectintcl', '( %s -> %s e. CC )' % (PS, IAB))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (PS, IAB))
t4c = closed(w, PS, '4cn', '4 e. CC')
e40 = w.s([t4c, w.inst('exp0')], 'syl', '( %s -> ( 4 ^ 0 ) = 1 )' % PS)
lhs0 = w.s([w.s([e40], 'oveq2d', '( %s -> ( ( abs ` %s ) / ( 4 ^ 0 ) ) = ( ( abs ` %s ) / 1 ) )' % (PS, IAB, IAB)),
            w.s([w.s([iab], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (PS, IAB))], 'div1d', '( %s -> ( ( abs ` %s ) / 1 ) = ( abs ` %s ) )' % (PS, IAB, IAB))], 'eqtrd',
           '( %s -> ( ( abs ` %s ) / ( 4 ^ 0 ) ) = ( abs ` %s ) )' % (PS, IAB, IAB))
n0d = w.s([w.s(['6'], 'gourn0', '( N ` 0 ) = %s' % OPAB)], 'a1i', '( %s -> ( N ` 0 ) = %s )' % (PS, OPAB))
rhs0 = w.s([w.s([n0d], 'oveq2d', '( %s -> ( F rectint ( N ` 0 ) ) = %s )' % (PS, IAB))], 'fveq2d', '( %s -> ( abs ` ( F rectint ( N ` 0 ) ) ) = ( abs ` %s ) )' % (PS, IAB))
base = w.s([w.s([iab], 'leidd', '( %s -> ( abs ` %s ) <_ ( abs ` %s ) )' % (PS, IAB, IAB)), lhs0, rhs0], '3brtr4d', '( %s -> %s )' % (PS, p0))
# --- induction step
LS = '( ( y e. NN0 /\\ ( %s -> %s ) ) /\\ %s )' % (PS, py, PS)
psl = w.s([], 'simpr', '( %s -> %s )' % (LS, PS))
ynn = w.s([], 'simpll', '( %s -> y e. NN0 )' % LS)
ihy = w.s([psl, w.s([], 'simplr', '( %s -> ( %s -> %s ) )' % (LS, PS, py))], 'mpd', '( %s -> %s )' % (LS, py))
FDAB = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D )'
fdl = w.s([psl, w.inst('simp3')], 'syl', '( %s -> %s )' % (LS, FDAB))
admi = w.s(['1', '2', '3', '4', '5', '6'], 'gouradm', '( ( %s /\\ y e. NN0 ) -> %s )' % (PS, INVQ(NK('y'))))
inv = w.s([psl, ynn, admi], 'syl2anc', '( %s -> %s )' % (LS, INVQ(NK('y'))))
sti = w.s(['1', '2', '3', '4', '5', '6'], 'gourstep', '( ( %s /\\ y e. NN0 /\\ %s ) -> ( %s /\\ %s /\\ %s ) )' % (PS, INVQ(NK('y')), INVQ(NK('( y + 1 )')), GEO1Q(NK('( y + 1 )'), F1(NK('y')), F2(NK('y'))), BNDQ(NK('( y + 1 )'), NK('y'))))
stp = w.s([psl, ynn, inv, sti], 'syl3anc', '( %s -> ( %s /\\ %s /\\ %s ) )' % (LS, INVQ(NK('( y + 1 )')), GEO1Q(NK('( y + 1 )'), F1(NK('y')), F2(NK('y'))), BNDQ(NK('( y + 1 )'), NK('y'))))
inv1 = w.s([stp, w.inst('simp1')], 'syl', '( %s -> %s )' % (LS, INVQ(NK('( y + 1 )'))))
bq = w.s([stp, w.inst('simp3')], 'syl', '( %s -> %s )' % (LS, BNDQ(NK('( y + 1 )'), NK('y'))))
ay = w.s([w.s([fdl, inv, w.inst('gourrcl')], 'syl2anc', '( %s -> ( F rectint %s ) e. CC )' % (LS, NK('y')))], 'abscld', '( %s -> ( abs ` ( F rectint %s ) ) e. RR )' % (LS, NK('y')))
ay1 = w.s([w.s([fdl, inv1, w.inst('gourrcl')], 'syl2anc', '( %s -> ( F rectint %s ) e. CC )' % (LS, NK('( y + 1 )')))], 'abscld', '( %s -> ( abs ` ( F rectint %s ) ) e. RR )' % (LS, NK('( y + 1 )')))
iabl = w.s([w.s([psl, w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (LS, IAB))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (LS, IAB))
rp4 = w.s([closed(w, LS, '4re', '4 e. RR'), closed(w, LS, '4pos', '0 < 4')], 'elrpd', '( %s -> 4 e. RR+ )' % LS)
t4cl = closed(w, LS, '4cn', '4 e. CC')
ey = w.s([rp4, w.s([ynn, w.inst('nn0z')], 'syl', '( %s -> y e. ZZ )' % LS)], 'rpexpcld', '( %s -> ( 4 ^ y ) e. RR+ )' % LS)
ey1 = w.s([rp4, w.s([w.s([ynn, w.inst('nn0p1nn')], 'syl', '( %s -> ( y + 1 ) e. NN )' % LS), w.inst('nnz')], 'syl', '( %s -> ( y + 1 ) e. ZZ )' % LS)], 'rpexpcld', '( %s -> ( 4 ^ ( y + 1 ) ) e. RR+ )' % LS)
qy = w.s([iabl, ey], 'rerpdivcld', '( %s -> ( ( abs ` %s ) / ( 4 ^ y ) ) e. RR )' % (LS, IAB))
qy1 = w.s([iabl, ey1], 'rerpdivcld', '( %s -> ( ( abs ` %s ) / ( 4 ^ ( y + 1 ) ) ) e. RR )' % (LS, IAB))
d1 = w.s([w.s([qy, ay, rp4], 'lediv1d', '( %s -> ( ( ( abs ` %s ) / ( 4 ^ y ) ) <_ ( abs ` ( F rectint %s ) ) <-> ( ( ( abs ` %s ) / ( 4 ^ y ) ) / 4 ) <_ ( ( abs ` ( F rectint %s ) ) / 4 ) ) )' % (LS, IAB, NK('y'), IAB, NK('y'))), ihy], 'mpbid',
         '( %s -> ( ( ( abs ` %s ) / ( 4 ^ y ) ) / 4 ) <_ ( ( abs ` ( F rectint %s ) ) / 4 ) )' % (LS, IAB, NK('y')))
ex1 = w.s([t4cl, ynn], 'expp1d', '( %s -> ( 4 ^ ( y + 1 ) ) = ( ( 4 ^ y ) x. 4 ) )' % LS)
dd = w.s([w.s([iabl], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (LS, IAB)), w.s([ey, w.inst('rpcn')], 'syl', '( %s -> ( 4 ^ y ) e. CC )' % LS), w.s([ey, w.inst('rpne0')], 'syl', '( %s -> ( 4 ^ y ) =/= 0 )' % LS), t4cl, closed(w, LS, '4ne0', '4 =/= 0')], 'divdiv1d',
         '( %s -> ( ( ( abs ` %s ) / ( 4 ^ y ) ) / 4 ) = ( ( abs ` %s ) / ( ( 4 ^ y ) x. 4 ) ) )' % (LS, IAB, IAB))
rw = w.s([w.s([ex1], 'oveq2d', '( %s -> ( ( abs ` %s ) / ( 4 ^ ( y + 1 ) ) ) = ( ( abs ` %s ) / ( ( 4 ^ y ) x. 4 ) ) )' % (LS, IAB, IAB))], 'eqcomd',
         '( %s -> ( ( abs ` %s ) / ( ( 4 ^ y ) x. 4 ) ) = ( ( abs ` %s ) / ( 4 ^ ( y + 1 ) ) ) )' % (LS, IAB, IAB))
eqq = w.s([dd, rw], 'eqtrd', '( %s -> ( ( ( abs ` %s ) / ( 4 ^ y ) ) / 4 ) = ( ( abs ` %s ) / ( 4 ^ ( y + 1 ) ) ) )' % (LS, IAB, IAB))
d2 = w.s([w.s([eqq], 'eqcomd', '( %s -> ( ( abs ` %s ) / ( 4 ^ ( y + 1 ) ) ) = ( ( ( abs ` %s ) / ( 4 ^ y ) ) / 4 ) )' % (LS, IAB, IAB)), d1], 'eqbrtrd', '( %s -> ( ( abs ` %s ) / ( 4 ^ ( y + 1 ) ) ) <_ ( ( abs ` ( F rectint %s ) ) / 4 ) )' % (LS, IAB, NK('y')))
stepc = w.s([qy1, w.s([ay, rp4], 'rerpdivcld', '( %s -> ( ( abs ` ( F rectint %s ) ) / 4 ) e. RR )' % (LS, NK('y'))), ay1, d2, bq], 'letrd', '( %s -> %s )' % (LS, py1))
e2 = w.s([w.s([stepc], 'ex', '( ( y e. NN0 /\\ ( %s -> %s ) ) -> ( %s -> %s ) )' % (PS, py, PS, py1))], 'ex', '( y e. NN0 -> ( ( %s -> %s ) -> ( %s -> %s ) ) )' % (PS, py, PS, py1))
ind = w.s([h1, h2, h3, h4, base, e2], 'nn0ind', '( M e. NN0 -> ( %s -> %s ) )' % (PS, pM))
w.qed([w.s([ind], 'com12', '( %s -> ( M e. NN0 -> %s ) )' % (PS, pM))], 'imp', '( ( %s /\\ M e. NN0 ) -> %s )' % (PS, pM))
run(w, True)


# ---- gourcmp: every lower corner is left of and below every upper corner
w = W('gourcmp', 'Every lower left corner of the sequence is left of and below every upper right corner.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gourcmp.%s' % nm.lower(), DEF)
A0 = '( %s /\\ P e. NN0 /\\ M e. NN0 )' % PS
CONC = '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (F1(NK('P')), F2(NK('M')), F1(NK('P')), F2(NK('M')))
ps0 = w.s([], 'simp1', '( %s -> %s )' % (A0, PS))
pn0 = w.s([], 'simp2', '( %s -> P e. NN0 )' % A0)
mn0 = w.s([], 'simp3', '( %s -> M e. NN0 )' % A0)


def corner(lvl, j, ps, jn, which):
    """( lvl -> corner of R_j e. R_j ), plus the corner-order facts of R_j"""
    admi = w.s(['1', '2', '3', '4', '5', '6'], 'gouradm', '( ( %s /\\ %s e. NN0 ) -> %s )' % (PS, j, INVQ(NK(j))))
    inv = w.s([ps, jn, admi], 'syl2anc', '( %s -> %s )' % (lvl, INVQ(NK(j))))
    xp = w.s([inv, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (lvl, NK(j)))
    u = w.s([xp, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (lvl, F1(NK(j))))
    v = w.s([xp, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (lvl, F2(NK(j))))
    od = w.s([inv, w.inst('simp2')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (lvl, F1(NK(j)), F2(NK(j)), F1(NK(j)), F2(NK(j))))
    pr = w.s([w.s([u, v], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (lvl, F1(NK(j)), F2(NK(j)))), od], 'jca',
             '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) ) )' % (lvl, F1(NK(j)), F2(NK(j)), F1(NK(j)), F2(NK(j)), F1(NK(j)), F2(NK(j))))
    lab = 'crectcnr1' if which == 1 else 'crectcnr3'
    pt = F1(NK(j)) if which == 1 else F2(NK(j))
    cin = w.s([pr, w.inst(lab)], 'syl', '( %s -> %s e. ( %s crect %s ) )' % (lvl, pt, F1(NK(j)), F2(NK(j))))
    return cin, u, v, pt


def place(lvl, ps, src, dst, jsrc, jdst, snn, dnn, which, pick):
    """put the corner of R_src into R_dst and read off the two inequalities"""
    cin, su, sv, pt = corner(lvl, jsrc, ps, snn, which)
    _c2, du, dv, _p = corner(lvl, jdst, ps, dnn, 1)
    nesti = w.s(['1', '2', '3', '4', '5', '6'], 'gournest', '( ( %s /\\ %s e. NN0 /\\ %s e. ( ZZ>= ` %s ) ) -> %s C_ %s )' % (PS, jdst, jsrc, jdst, RJ2(jsrc), RJ2(jdst)))
    uz = w.s([w.s([w.s([dnn, w.inst('nn0z')], 'syl', '( %s -> %s e. ZZ )' % (lvl, jdst)), w.s([snn, w.inst('nn0z')], 'syl', '( %s -> %s e. ZZ )' % (lvl, jsrc)), pick], '3jca',
                  '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (lvl, jdst, jsrc, jdst, jsrc)),
              w.s([w.s([], 'eluz2', '( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (jsrc, jdst, jdst, jsrc, jdst, jsrc))], 'a1i',
                  '( %s -> ( %s e. ( ZZ>= ` %s ) <-> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) ) )' % (lvl, jsrc, jdst, jdst, jsrc, jdst, jsrc))], 'mpbird',
             '( %s -> %s e. ( ZZ>= ` %s ) )' % (lvl, jsrc, jdst))
    inc = w.s([ps, dnn, uz, nesti], 'syl3anc', '( %s -> %s C_ %s )' % (lvl, RJ2(jsrc), RJ2(jdst)))
    ind = w.s([inc, cin], 'sseldd', '( %s -> %s e. %s )' % (lvl, pt, RJ2(jdst)))
    elc = w.s([w.s([du, dv], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (lvl, F1(NK(jdst)), F2(NK(jdst)))), w.inst('elcrect')], 'syl',
              '( %s -> ( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )'
              % (lvl, pt, RJ2(jdst), pt, pt, F1(NK(jdst)), F2(NK(jdst)), pt, F1(NK(jdst)), F2(NK(jdst))))
    tt = w.s([ind, elc], 'mpbid', '( %s -> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )'
             % (lvl, pt, pt, F1(NK(jdst)), F2(NK(jdst)), pt, F1(NK(jdst)), F2(NK(jdst))))
    out = []
    for part, sel in (('Re', 'simp2'), ('Im', 'simp3')):
        mem = w.s([tt, w.inst(sel)], 'syl', '( %s -> ( %s ` %s ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) )' % (lvl, part, pt, part, F1(NK(jdst)), part, F2(NK(jdst))))
        cl = 'recl' if part == 'Re' else 'imcl'
        lo = w.s([w.s([du, w.inst(cl)], 'syl', '( %s -> ( %s ` %s ) e. RR )' % (lvl, part, F1(NK(jdst)))), w.s([dv, w.inst(cl)], 'syl', '( %s -> ( %s ` %s ) e. RR )' % (lvl, part, F2(NK(jdst)))), w.inst('elicc2')], 'syl2anc',
                 '( %s -> ( ( %s ` %s ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( ( %s ` %s ) e. RR /\\ ( %s ` %s ) <_ ( %s ` %s ) /\\ ( %s ` %s ) <_ ( %s ` %s ) ) ) )'
                 % (lvl, part, pt, part, F1(NK(jdst)), part, F2(NK(jdst)), part, pt, part, F1(NK(jdst)), part, pt, part, pt, part, F2(NK(jdst))))
        t3 = w.s([mem, lo], 'mpbid', '( %s -> ( ( %s ` %s ) e. RR /\\ ( %s ` %s ) <_ ( %s ` %s ) /\\ ( %s ` %s ) <_ ( %s ` %s ) ) )'
                 % (lvl, part, pt, part, F1(NK(jdst)), part, pt, part, pt, part, F2(NK(jdst))))
        out.append(w.s([t3, w.inst('simp2' if which == 2 else 'simp3')], 'syl',
                       ('( %s -> ( %s ` %s ) <_ ( %s ` %s ) )' % (lvl, part, F1(NK(jdst)), part, pt)) if which == 2
                       else ('( %s -> ( %s ` %s ) <_ ( %s ` %s ) )' % (lvl, part, pt, part, F2(NK(jdst))))))
    return out


def RJ2(j): return '( %s crect %s )' % (F1(NK(j)), F2(NK(j)))


LK = '( %s /\\ P <_ M )' % A0
psK = w.s([ps0], 'adantr', '( %s -> %s )' % (LK, PS))
knK = w.s([pn0], 'adantr', '( %s -> P e. NN0 )' % LK)
mnK = w.s([mn0], 'adantr', '( %s -> M e. NN0 )' % LK)
pkK = w.s([], 'simpr', '( %s -> P <_ M )' % LK)
o1 = place(LK, psK, 'M', 'P', 'M', 'P', mnK, knK, 2, pkK)
c1 = w.s([o1[0], o1[1]], 'jca', '( %s -> %s )' % (LK, CONC))
LM = '( %s /\\ M <_ P )' % A0
psM = w.s([ps0], 'adantr', '( %s -> %s )' % (LM, PS))
knM = w.s([pn0], 'adantr', '( %s -> P e. NN0 )' % LM)
mnM = w.s([mn0], 'adantr', '( %s -> M e. NN0 )' % LM)
pkM = w.s([], 'simpr', '( %s -> M <_ P )' % LM)
o2 = place(LM, psM, 'P', 'M', 'P', 'M', knM, mnM, 1, pkM)
c2 = w.s([o2[0], o2[1]], 'jca', '( %s -> %s )' % (LM, CONC))
tric = w.s([w.s([pn0, w.inst('nn0red')], 'syl', '( %s -> P e. RR )' % A0), w.s([mn0, w.inst('nn0red')], 'syl', '( %s -> M e. RR )' % A0), w.inst('letric')], 'syl2anc',
           '( %s -> ( P <_ M \\/ M <_ P ) )' % A0)
w.qed([tric, c1, c2], 'mpjaodan', '( %s -> %s )' % (A0, CONC))
run(w, True)


# ---- gourz: the common point of the nested rectangles
TR = '{ r e. RR | E. n e. NN0 r = ( Re ` ( 1st ` ( N ` n ) ) ) }'
TI = '{ r e. RR | E. n e. NN0 r = ( Im ` ( 1st ` ( N ` n ) ) ) }'
X0 = 'sup ( %s , RR , < )' % TR
Y0 = 'sup ( %s , RR , < )' % TI
Z0 = '( %s + ( _i x. %s ) )' % (X0, Y0)
w = W('gourz', 'The supremum point lies in every rectangle of the nested sequence.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gourz.%s' % nm.lower(), DEF)
A0 = '( %s /\\ M e. NN0 )' % PS
ps0 = w.s([], 'simpl', '( %s -> %s )' % (A0, PS))
mn0 = w.s([], 'simpr', '( %s -> M e. NN0 )' % A0)
admi = w.s(['1', '2', '3', '4', '5', '6'], 'gouradm', '( ( %s /\\ M e. NN0 ) -> %s )' % (PS, INVQ(NK('M'))))
inv = admi
xpm = w.s([inv, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A0, NK('M')))
um = w.s([xpm, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (A0, F1(NK('M'))))
vm = w.s([xpm, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (A0, F2(NK('M'))))
res = {}
for part, cl, T, SP in (('Re', 'recl', TR, X0), ('Im', 'imcl', TI, Y0)):
    LO = '( %s ` %s )' % (part, F1(NK('M')))
    HI = '( %s ` %s )' % (part, F2(NK('M')))
    lor = w.s([um, w.inst(cl)], 'syl', '( %s -> %s e. RR )' % (A0, LO))
    hir = w.s([vm, w.inst(cl)], 'syl', '( %s -> %s e. RR )' % (A0, HI))
    # membership of LO in T
    e1 = w.s([], 'eqeq1', '( r = %s -> ( r = ( %s ` ( 1st ` ( N ` n ) ) ) <-> %s = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (LO, part, LO, part))
    e2 = w.s([e1], 'rexbidv', '( r = %s -> ( E. n e. NN0 r = ( %s ` ( 1st ` ( N ` n ) ) ) <-> E. n e. NN0 %s = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (LO, part, LO, part))
    er = w.s([e2], 'elrab', '( %s e. %s <-> ( %s e. RR /\\ E. n e. NN0 %s = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (LO, T, LO, LO, part))
    w1 = w.s([w.s([w.s([], 'fveq2', '( n = M -> ( N ` n ) = ( N ` M ) )')], 'fveq2d', '( n = M -> ( 1st ` ( N ` n ) ) = %s )' % F1(NK('M')))], 'fveq2d',
             '( n = M -> ( %s ` ( 1st ` ( N ` n ) ) ) = %s )' % (part, LO))
    w2 = w.s([w1], 'eqeq2d', '( n = M -> ( %s = ( %s ` ( 1st ` ( N ` n ) ) ) <-> %s = %s ) )' % (LO, part, LO, LO))
    exi = w.s([mn0, w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, LO, LO)),
               w.s([w2], 'rspcev', '( ( M e. NN0 /\\ %s = %s ) -> E. n e. NN0 %s = ( %s ` ( 1st ` ( N ` n ) ) ) )' % (LO, LO, LO, part))], 'syl2anc',
              '( %s -> E. n e. NN0 %s = ( %s ` ( 1st ` ( N ` n ) ) ) )' % (A0, LO, part))
    mem = w.s([w.s([lor, exi], 'jca', '( %s -> ( %s e. RR /\\ E. n e. NN0 %s = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (A0, LO, LO, part)),
               w.s([er], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. RR /\\ E. n e. NN0 %s = ( %s ` ( 1st ` ( N ` n ) ) ) ) ) )' % (A0, LO, T, LO, LO, part))], 'mpbird',
              '( %s -> %s e. %s )' % (A0, LO, T))
    # the upper bound
    AY = '( %s /\\ y e. %s )' % (A0, T)
    yt = w.s([], 'simpr', '( %s -> y e. %s )' % (AY, T))
    ey1 = w.s([], 'eqeq1', '( r = y -> ( r = ( %s ` ( 1st ` ( N ` n ) ) ) <-> y = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (part, part))
    ey2 = w.s([ey1], 'rexbidv', '( r = y -> ( E. n e. NN0 r = ( %s ` ( 1st ` ( N ` n ) ) ) <-> E. n e. NN0 y = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (part, part))
    eyr = w.s([ey2], 'elrab', '( y e. %s <-> ( y e. RR /\\ E. n e. NN0 y = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (T, part))
    ytt = w.s([yt, w.s([eyr], 'a1i', '( %s -> ( y e. %s <-> ( y e. RR /\\ E. n e. NN0 y = ( %s ` ( 1st ` ( N ` n ) ) ) ) ) )' % (AY, T, part))], 'mpbid',
              '( %s -> ( y e. RR /\\ E. n e. NN0 y = ( %s ` ( 1st ` ( N ` n ) ) ) ) )' % (AY, part))
    yexn = w.s([ytt], 'simprd', '( %s -> E. n e. NN0 y = ( %s ` ( 1st ` ( N ` n ) ) ) )' % (AY, part))
    cb1 = w.s([w.s([w.s([], 'fveq2', '( n = k -> ( N ` n ) = ( N ` k ) )')], 'fveq2d', '( n = k -> ( 1st ` ( N ` n ) ) = ( 1st ` ( N ` k ) ) )')], 'fveq2d',
              '( n = k -> ( %s ` ( 1st ` ( N ` n ) ) ) = ( %s ` ( 1st ` ( N ` k ) ) ) )' % (part, part))
    cb2 = w.s([cb1], 'eqeq2d', '( n = k -> ( y = ( %s ` ( 1st ` ( N ` n ) ) ) <-> y = ( %s ` ( 1st ` ( N ` k ) ) ) ) )' % (part, part))
    cb3 = w.s([cb2], 'cbvrexvw', '( E. n e. NN0 y = ( %s ` ( 1st ` ( N ` n ) ) ) <-> E. k e. NN0 y = ( %s ` ( 1st ` ( N ` k ) ) ) )' % (part, part))
    yex = w.s([yexn, w.s([cb3], 'a1i', '( %s -> ( E. n e. NN0 y = ( %s ` ( 1st ` ( N ` n ) ) ) <-> E. k e. NN0 y = ( %s ` ( 1st ` ( N ` k ) ) ) ) )' % (AY, part, part))], 'mpbid',
              '( %s -> E. k e. NN0 y = ( %s ` ( 1st ` ( N ` k ) ) ) )' % (AY, part))
    AK = '( %s /\\ k e. NN0 )' % AY
    cmpi = w.s(['1', '2', '3', '4', '5', '6'], 'gourcmp', '( ( %s /\\ k e. NN0 /\\ M e. NN0 ) -> ( ( Re ` ( 1st ` ( N ` k ) ) ) <_ ( Re ` %s ) /\\ ( Im ` ( 1st ` ( N ` k ) ) ) <_ ( Im ` %s ) ) )' % (PS, F2(NK('M')), F2(NK('M'))))
    cmp = w.s([w.s([w.s([ps0], 'adantr', '( %s -> %s )' % (AY, PS))], 'adantr', '( %s -> %s )' % (AK, PS)),
               w.s([], 'simpr', '( %s -> k e. NN0 )' % AK),
               w.s([w.s([mn0], 'adantr', '( %s -> M e. NN0 )' % AY)], 'adantr', '( %s -> M e. NN0 )' % AK), cmpi], 'syl3anc',
              '( %s -> ( ( Re ` ( 1st ` ( N ` k ) ) ) <_ ( Re ` %s ) /\\ ( Im ` ( 1st ` ( N ` k ) ) ) <_ ( Im ` %s ) ) )' % (AK, F2(NK('M')), F2(NK('M'))))
    one = w.s([cmp, w.inst('simpl' if part == 'Re' else 'simpr')], 'syl', '( %s -> ( %s ` ( 1st ` ( N ` k ) ) ) <_ %s )' % (AK, part, HI))
    AKE = '( %s /\\ y = ( %s ` ( 1st ` ( N ` k ) ) ) )' % (AK, part)
    trn = w.s([w.s([], 'simpr', '( %s -> y = ( %s ` ( 1st ` ( N ` k ) ) ) )' % (AKE, part)), w.s([one], 'adantr', '( %s -> ( %s ` ( 1st ` ( N ` k ) ) ) <_ %s )' % (AKE, part, HI))], 'eqbrtrd',
              '( %s -> y <_ %s )' % (AKE, HI))
    imp2 = w.s([w.s([trn], 'ex', '( %s -> ( y = ( %s ` ( 1st ` ( N ` k ) ) ) -> y <_ %s ) )' % (AK, part, HI))], 'rexlimdva',
               '( %s -> ( E. k e. NN0 y = ( %s ` ( 1st ` ( N ` k ) ) ) -> y <_ %s ) )' % (AY, part, HI))
    yle = w.s([yex, imp2], 'mpd', '( %s -> y <_ %s )' % (AY, HI))
    ral = w.s([yle], 'ralrimiva', '( %s -> A. y e. %s y <_ %s )' % (A0, T, HI))
    tss = closed(w, A0, 'ssrab2', '%s C_ RR' % T)
    ant = w.s([w.s([tss, mem], 'jca', '( %s -> ( %s C_ RR /\\ %s e. %s ) )' % (A0, T, LO, T)),
               w.s([hir, ral], 'jca', '( %s -> ( %s e. RR /\\ A. y e. %s y <_ %s ) )' % (A0, HI, T, HI))], 'jca',
              '( %s -> ( ( %s C_ RR /\\ %s e. %s ) /\\ ( %s e. RR /\\ A. y e. %s y <_ %s ) ) )' % (A0, T, LO, T, HI, T, HI))
    sne = w.s([ant, w.inst('gsupne')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (A0, LO, SP, SP, HI))
    scl = w.s([ant, w.inst('gsupcl')], 'syl', '( %s -> %s e. RR )' % (A0, SP))
    mm = w.s([w.s([lor, hir, w.inst('elicc2')], 'syl2anc', '( %s -> ( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) ) )' % (A0, SP, LO, HI, SP, LO, SP, SP, HI)),
               w.s([scl, w.s([sne, w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A0, LO, SP)), w.s([sne, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A0, SP, HI))], '3jca',
                   '( %s -> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (A0, SP, LO, SP, SP, HI))], 'mpbird',
              '( %s -> %s e. ( %s [,] %s ) )' % (A0, SP, LO, HI))
    res[part] = mm
w.qed([w.s([um, vm], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, F1(NK('M')), F2(NK('M')))),
       w.s([res['Re'], res['Im']], 'jca', '( %s -> ( %s e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ %s e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (A0, X0, F1(NK('M')), F2(NK('M')), Y0, F1(NK('M')), F2(NK('M')))),
       w.inst('crectpt')], 'syl2anc', '( %s -> %s e. ( %s crect %s ) )' % (A0, Z0, F1(NK('M')), F2(NK('M'))))
run(w, True)


# ---- gourdifk: the boundary integral over a rectangle of the sequence equals
# the boundary integral of the remainder of the linear approximation
FZ = '( F ` Z )'
AFFV = '( %s + ( C x. ( y - Z ) ) )' % FZ
ODEF = 'O = ( y e. D |-> ( ( F ` y ) - %s ) )' % AFFV
SDEF = 'S = ( y e. CC |-> %s )' % AFFV
TDEF = 'T = ( y e. CC |-> ( ( ( %s - ( C x. Z ) ) x. y ) + ( ( C / 2 ) x. ( y ^ 2 ) ) ) )' % FZ
DEFS = [('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF), ('O', ODEF), ('S', SDEF), ('T', TDEF)]
w = W('gourdifk', 'The boundary integral over a rectangle of the sequence equals that of the linear-approximation remainder.')
for k, (nm, DEF) in enumerate(DEFS, start=1):
    hyp(w, str(k), 'gourdifk.%s' % nm.lower(), DEF)
CZD = '( C e. CC /\\ Z e. CC /\\ Z e. D )'
A0 = '( %s /\\ %s /\\ M e. NN0 )' % (PS, CZD)
AM = F1(NK('M')); BM = F2(NK('M'))
ps0 = w.s([], 'simp1', '( %s -> %s )' % (A0, PS))
czd = w.s([], 'simp2', '( %s -> %s )' % (A0, CZD))
mn0 = w.s([], 'simp3', '( %s -> M e. NN0 )' % A0)
cc = w.s([czd, w.inst('simp1')], 'syl', '( %s -> C e. CC )' % A0)
zc = w.s([czd, w.inst('simp2')], 'syl', '( %s -> Z e. CC )' % A0)
zdd = w.s([czd, w.inst('simp3')], 'syl', '( %s -> Z e. D )' % A0)
fcn = w.s([ps0, w.inst('simp3l')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
rss = w.s([ps0, w.inst('simp3r')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
fzc = w.s([ff, zdd], 'ffvelcdmd', '( %s -> %s e. CC )' % (A0, FZ))
admi = w.s(['1', '2', '3', '4', '5', '6'], 'gouradm', '( ( %s /\\ M e. NN0 ) -> %s )' % (PS, INVQ(NK('M'))))
inv = w.s([w.s([ps0, mn0], 'jca', '( %s -> ( %s /\\ M e. NN0 ) )' % (A0, PS)), admi], 'syl' if False else 'mpd', 'x')
w.lines.pop()
inv = w.s([ps0, mn0, admi], 'syl2anc', '( %s -> %s )' % (A0, INVQ(NK('M'))))
xpm = w.s([inv, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A0, NK('M')))
amc = w.s([xpm, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (A0, AM))
bmc = w.s([xpm, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (A0, BM))
ordm = w.s([inv, w.inst('simp2')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, AM, BM, AM, BM))
incm = w.s([inv, w.inst('simp3')], 'syl', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A0, AM, BM))
ssd = w.s([incm, rss], 'sstrd', '( %s -> ( %s crect %s ) C_ D )' % (A0, AM, BM))
psm = w.s([w.s([amc, bmc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, AM, BM)), ordm,
           w.s([fcn, ssd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ D ) )' % (A0, AM, BM))], '3jca', '( %s -> %s )' % (A0, PSOF(AM, BM)))
remi = w.s(['7', '8'], 'gourrem', '( ( F e. ( D -cn-> CC ) /\\ ( %s e. CC /\\ C e. CC /\\ Z e. CC ) ) -> ( O e. ( D -cn-> CC ) /\\ A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) ) )' % FZ)
rem = w.s([w.s([fcn, w.s([fzc, cc, zc], '3jca', '( %s -> ( %s e. CC /\\ C e. CC /\\ Z e. CC ) )' % (A0, FZ))], 'jca',
                '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s e. CC /\\ C e. CC /\\ Z e. CC ) ) )' % (A0, FZ)), remi], 'syl',
          '( %s -> ( O e. ( D -cn-> CC ) /\\ A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) ) )' % A0)
ocn = w.s([rem, w.inst('simpl')], 'syl', '( %s -> O e. ( D -cn-> CC ) )' % A0)
alD = w.s([rem, w.inst('simpr')], 'syl', '( %s -> A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) )' % A0)
alM = w.s([w.s([ssd, w.inst('ssralv')], 'syl', '( %s -> ( A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) -> A. w e. ( %s crect %s ) ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) ) )' % (A0, AM, BM)), alD], 'mpd',
          '( %s -> A. w e. ( %s crect %s ) ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) )' % (A0, AM, BM))
affi = w.s(['9', '8'], 'gouraffdv', '( ( %s e. CC /\\ C e. CC /\\ Z e. CC ) -> ( ( T : CC --> CC /\\ ( CC _D T ) = S ) /\\ S e. ( CC -cn-> CC ) ) )' % FZ)
aff = w.s([w.s([fzc, cc, zc], '3jca', '( %s -> ( %s e. CC /\\ C e. CC /\\ Z e. CC ) )' % (A0, FZ)), affi], 'syl',
          '( %s -> ( ( T : CC --> CC /\\ ( CC _D T ) = S ) /\\ S e. ( CC -cn-> CC ) ) )' % A0)
hyp3 = w.s([ocn, w.s([aff, w.inst('simpl')], 'syl', '( %s -> ( T : CC --> CC /\\ ( CC _D T ) = S ) )' % A0), w.s([aff, w.inst('simpr')], 'syl', '( %s -> S e. ( CC -cn-> CC ) )' % A0)], '3jca',
           '( %s -> ( O e. ( D -cn-> CC ) /\\ ( T : CC --> CC /\\ ( CC _D T ) = S ) /\\ S e. ( CC -cn-> CC ) ) )' % A0)
sub0 = w.s([psm, hyp3, alM, w.inst('rectintsub0')], 'syl3anc', '( %s -> ( F rectint <. %s , %s >. ) = ( O rectint <. %s , %s >. ) )' % (A0, AM, BM, AM, BM))
pqm = w.s([xpm, w.inst('1st2nd2')], 'syl', '( %s -> %s = <. %s , %s >. )' % (A0, NK('M'), AM, BM))
w.qed([w.s([pqm], 'oveq2d', '( %s -> ( F rectint %s ) = ( F rectint <. %s , %s >. ) )' % (A0, NK('M'), AM, BM)), sub0], 'eqtrd',
      '( %s -> ( F rectint %s ) = ( O rectint <. %s , %s >. ) )' % (A0, NK('M'), AM, BM))
run(w, True)


# ---- gourmlk: the ML bound on a rectangle of the sequence
def LOCS(t):
    return '( ( abs ` ( %s - Z ) ) < R -> ( abs ` ( ( ( F ` %s ) - %s ) - ( C x. ( %s - Z ) ) ) ) <_ ( E x. ( abs ` ( %s - Z ) ) ) )' % (t, t, FZ, t, t)
LOCAL = 'A. s e. D %s' % LOCS('s')
w = W('gourmlk', 'The ML bound on a rectangle of the nested sequence.')
for k, (nm, DEF) in enumerate(DEFS, start=1):
    hyp(w, str(k), 'gourmlk.%s' % nm.lower(), DEF)
AM = F1(NK('M')); BM = F2(NK('M'))
DMM = '( ( ( Re ` %s ) - ( Re ` %s ) ) + ( ( Im ` %s ) - ( Im ` %s ) ) )' % (BM, AM, BM, AM)
C1 = '( %s /\\ %s /\\ M e. NN0 )' % (PS, CZD)
C2 = '( E e. RR+ /\\ R e. RR+ /\\ %s )' % LOCAL
C3 = '( Z e. ( %s crect %s ) /\\ %s < R )' % (AM, BM, DMM)
A0 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1))
c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2))
c3 = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
ps0 = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, PS))
czd = w.s([c1, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, CZD))
mn0 = w.s([c1, w.inst('simp3')], 'syl', '( %s -> M e. NN0 )' % A0)
cc = w.s([czd, w.inst('simp1')], 'syl', '( %s -> C e. CC )' % A0)
zc = w.s([czd, w.inst('simp2')], 'syl', '( %s -> Z e. CC )' % A0)
zdd = w.s([czd, w.inst('simp3')], 'syl', '( %s -> Z e. D )' % A0)
erp = w.s([c2, w.inst('simp1')], 'syl', '( %s -> E e. RR+ )' % A0)
rrp = w.s([c2, w.inst('simp2')], 'syl', '( %s -> R e. RR+ )' % A0)
loc = w.s([c2, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, LOCAL))
zrm = w.s([c3, w.inst('simpl')], 'syl', '( %s -> Z e. ( %s crect %s ) )' % (A0, AM, BM))
dlt = w.s([c3, w.inst('simpr')], 'syl', '( %s -> %s < R )' % (A0, DMM))
fcn = w.s([ps0, w.inst('simp3l')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
rss = w.s([ps0, w.inst('simp3r')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
fzc = w.s([ff, zdd], 'ffvelcdmd', '( %s -> %s e. CC )' % (A0, FZ))
admi = w.s(['1', '2', '3', '4', '5', '6'], 'gouradm', '( ( %s /\\ M e. NN0 ) -> %s )' % (PS, INVQ(NK('M'))))
inv = w.s([ps0, mn0, admi], 'syl2anc', '( %s -> %s )' % (A0, INVQ(NK('M'))))
xpm = w.s([inv, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A0, NK('M')))
amc = w.s([xpm, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (A0, AM))
bmc = w.s([xpm, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (A0, BM))
ordm = w.s([inv, w.inst('simp2')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, AM, BM, AM, BM))
incm = w.s([inv, w.inst('simp3')], 'syl', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A0, AM, BM))
ssd = w.s([incm, rss], 'sstrd', '( %s -> ( %s crect %s ) C_ D )' % (A0, AM, BM))
# the remainder is continuous
remi = w.s(['7', '8'], 'gourrem', '( ( F e. ( D -cn-> CC ) /\\ ( %s e. CC /\\ C e. CC /\\ Z e. CC ) ) -> ( O e. ( D -cn-> CC ) /\\ A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) ) )' % FZ)
rem = w.s([w.s([fcn, w.s([fzc, cc, zc], '3jca', '( %s -> ( %s e. CC /\\ C e. CC /\\ Z e. CC ) )' % (A0, FZ))], 'jca',
                '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s e. CC /\\ C e. CC /\\ Z e. CC ) ) )' % (A0, FZ)), remi], 'syl',
          '( %s -> ( O e. ( D -cn-> CC ) /\\ A. w e. D ( F ` w ) = ( ( O ` w ) + ( S ` w ) ) ) )' % A0)
ocn = w.s([rem, w.inst('simpl')], 'syl', '( %s -> O e. ( D -cn-> CC ) )' % A0)
# the pointwise bound
pti = w.s(['7'], 'gourpt', '( ( ( F e. ( D -cn-> CC ) /\\ ( C e. CC /\\ Z e. CC ) ) /\\ ( E e. RR+ /\\ R e. RR+ /\\ %s ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s crect %s ) C_ D /\\ ( Z e. ( %s crect %s ) /\\ %s < R ) ) ) -> A. z e. ( %s crect %s ) ( abs ` ( O ` z ) ) <_ ( E x. %s ) )'
           % (LOCAL, AM, BM, AM, BM, AM, BM, DMM, AM, BM, DMM))
pt = w.s([w.s([w.s([fcn, w.s([cc, zc], 'jca', '( %s -> ( C e. CC /\\ Z e. CC ) )' % A0)], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( C e. CC /\\ Z e. CC ) ) )' % A0),
               w.s([erp, rrp, loc], '3jca', '( %s -> ( E e. RR+ /\\ R e. RR+ /\\ %s ) )' % (A0, LOCAL)),
               w.s([w.s([amc, bmc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, AM, BM)), ssd, w.s([zrm, dlt], 'jca', '( %s -> ( Z e. ( %s crect %s ) /\\ %s < R ) )' % (A0, AM, BM, DMM))], '3jca',
                   '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s crect %s ) C_ D /\\ ( Z e. ( %s crect %s ) /\\ %s < R ) ) )' % (A0, AM, BM, AM, BM, AM, BM, DMM))], '3jca',
              '( %s -> ( ( F e. ( D -cn-> CC ) /\\ ( C e. CC /\\ Z e. CC ) ) /\\ ( E e. RR+ /\\ R e. RR+ /\\ %s ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s crect %s ) C_ D /\\ ( Z e. ( %s crect %s ) /\\ %s < R ) ) ) )'
              % (A0, LOCAL, AM, BM, AM, BM, AM, BM, DMM)), pti], 'syl',
         '( %s -> A. z e. ( %s crect %s ) ( abs ` ( O ` z ) ) <_ ( E x. %s ) )' % (A0, AM, BM, DMM))
# rectintabs on the remainder
amr = w.s([amc, w.inst('recl')], 'syl', '( %s -> ( Re ` %s ) e. RR )' % (A0, AM))
bmr = w.s([bmc, w.inst('recl')], 'syl', '( %s -> ( Re ` %s ) e. RR )' % (A0, BM))
ami = w.s([amc, w.inst('imcl')], 'syl', '( %s -> ( Im ` %s ) e. RR )' % (A0, AM))
bmi = w.s([bmc, w.inst('imcl')], 'syl', '( %s -> ( Im ` %s ) e. RR )' % (A0, BM))
dmre = w.s([w.s([bmr, amr], 'resubcld', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) e. RR )' % (A0, BM, AM)), w.s([bmi, ami], 'resubcld', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) e. RR )' % (A0, BM, AM))], 'readdcld', '( %s -> %s e. RR )' % (A0, DMM))
ere = w.s([erp, w.inst('rpre')], 'syl', '( %s -> E e. RR )' % A0)
edm = w.s([ere, dmre], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (A0, DMM))
psO = w.s([w.s([amc, bmc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, AM, BM)), ordm,
           w.s([ocn, ssd], 'jca', '( %s -> ( O e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ D ) )' % (A0, AM, BM))], '3jca',
          '( %s -> %s )' % (A0, PSOF(AM, BM).replace('F e. (', 'O e. (')))
mlb = w.s([psO, edm, pt, w.inst('rectintabs')], 'syl3anc', '( %s -> ( abs ` ( O rectint <. %s , %s >. ) ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A0, AM, BM, DMM, DMM))
difi = w.s(['1', '2', '3', '4', '5', '6', '7', '8', '9'], 'gourdifk', '( ( %s /\\ %s /\\ M e. NN0 ) -> ( F rectint %s ) = ( O rectint <. %s , %s >. ) )' % (PS, CZD, NK('M'), AM, BM))
dif = w.s([ps0, czd, mn0, difi], 'syl3anc', '( %s -> ( F rectint %s ) = ( O rectint <. %s , %s >. ) )' % (A0, NK('M'), AM, BM))
w.qed([w.s([dif], 'fveq2d', '( %s -> ( abs ` ( F rectint %s ) ) = ( abs ` ( O rectint <. %s , %s >. ) ) )' % (A0, NK('M'), AM, BM)), mlb], 'eqbrtrd',
      '( %s -> ( abs ` ( F rectint %s ) ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A0, NK('M'), DMM, DMM))
run(w, True)


# ---- gourfin: the boundary integral is smaller than every multiple of the squared perimeter
HOLO = '( %s /\\ %s /\\ ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) ) )' % (AB, GEO)
ZDEF = 'Z = ( %s + ( _i x. %s ) )' % (X0, Y0)
CDEF = 'C = ( ( CC _D F ) ` Z )'
WD = '( %s - %s )' % (RE('B'), RE('A')); HG = '( %s - %s )' % (IM('B'), IM('A'))
WH = '( %s + %s )' % (WD, HG)
IAB = '( F rectint <. A , B >. )'
DEFS2 = DEFS + [('Z', ZDEF), ('C', CDEF)]
w = W('gourfin', 'The boundary integral of a holomorphic function on a rectangle is below every multiple of the squared perimeter.')
for k, (nm, DEF) in enumerate(DEFS2, start=1):
    hyp(w, str(k), 'gourfin.%s' % nm.lower(), DEF)
HH = [str(i) for i in range(1, 7)]
A0 = '( %s /\\ E e. RR+ )' % HOLO
hol = w.s([], 'simpl', '( %s -> %s )' % (A0, HOLO))
erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
ac = w.s([hol, w.inst('simp1l')], 'syl', '( %s -> A e. CC )' % A0)
bc = w.s([hol, w.inst('simp1r')], 'syl', '( %s -> B e. CC )' % A0)
geo = w.s([hol, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, GEO))
fcn = w.s([hol, w.inst('simp3l')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
dvs = w.s([hol, w.inst('simp3r')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
sc = closed(w, A0, 'ssid', 'CC C_ CC')
bss = w.s([sc, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
rss = w.s([dvs, bss], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
ps0 = w.s([w.s([ac, bc], 'jca', '( %s -> %s )' % (A0, AB)), geo, w.s([fcn, rss], 'jca', '( %s -> %s )' % (A0, FCN))], '3jca', '( %s -> %s )' % (A0, PS))
# Z lies in the rectangle
n00 = w.s([w.s(['6'], 'gourn0', '( N ` 0 ) = <. A , B >.')], 'a1i', '( %s -> ( N ` 0 ) = <. A , B >. )' % A0)
o10 = w.s([w.s([n00], 'fveq2d', '( %s -> ( 1st ` ( N ` 0 ) ) = ( 1st ` <. A , B >. ) )' % A0), w.s([ac, bc, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. A , B >. ) = A )' % A0)], 'eqtrd', '( %s -> ( 1st ` ( N ` 0 ) ) = A )' % A0)
o20 = w.s([w.s([n00], 'fveq2d', '( %s -> ( 2nd ` ( N ` 0 ) ) = ( 2nd ` <. A , B >. ) )' % A0), w.s([ac, bc, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. A , B >. ) = B )' % A0)], 'eqtrd', '( %s -> ( 2nd ` ( N ` 0 ) ) = B )' % A0)
zi = w.s(HH, 'gourz', '( ( %s /\\ 0 e. NN0 ) -> %s e. ( ( 1st ` ( N ` 0 ) ) crect ( 2nd ` ( N ` 0 ) ) ) )' % (PS, Z0))
z00 = w.s([ps0, closed(w, A0, '0nn0', '0 e. NN0'), zi], 'syl2anc', '( %s -> %s e. ( ( 1st ` ( N ` 0 ) ) crect ( 2nd ` ( N ` 0 ) ) ) )' % (A0, Z0))
zab = w.s([z00, w.s([o10, o20], 'oveq12d', '( %s -> ( ( 1st ` ( N ` 0 ) ) crect ( 2nd ` ( N ` 0 ) ) ) = ( A crect B ) )' % A0)], 'eleqtrd', '( %s -> %s e. ( A crect B ) )' % (A0, Z0))
zr = w.s([w.s(['10'], 'a1i', '( %s -> %s )' % (A0, ZDEF)), zab], 'eqeltrd', '( %s -> Z e. ( A crect B ) )' % A0)
zdv = w.s([dvs, zr], 'sseldd', '( %s -> Z e. dom ( CC _D F ) )' % A0)
zdd = w.s([rss, zr], 'sseldd', '( %s -> Z e. D )' % A0)
zcc = w.s([dss, zdd], 'sseldd', '( %s -> Z e. CC )' % A0)
dvf = closed(w, A0, 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC')
ccc = w.s([w.s(['11'], 'a1i', '( %s -> %s )' % (A0, CDEF)), w.s([dvf, zdv], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` Z ) e. CC )' % A0)], 'eqeltrd', '( %s -> C e. CC )' % A0)
czd = w.s([ccc, zcc, zdd], '3jca', '( %s -> %s )' % (A0, CZD))
# the local estimate
dvei = w.s([], 'gourdveps', '( ( ( F e. ( D -cn-> CC ) /\\ Z e. dom ( CC _D F ) /\\ C = ( ( CC _D F ) ` Z ) ) /\\ E e. RR+ ) -> E. d e. RR+ A. z e. D %s )' % LOCS('z').replace(' R ', ' d '))
dve = w.s([w.s([w.s([fcn, zdv, w.s(['11'], 'a1i', '( %s -> %s )' % (A0, CDEF))], '3jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ Z e. dom ( CC _D F ) /\\ C = ( ( CC _D F ) ` Z ) ) )' % A0), erp], 'jca',
                '( %s -> ( ( F e. ( D -cn-> CC ) /\\ Z e. dom ( CC _D F ) /\\ C = ( ( CC _D F ) ` Z ) ) /\\ E e. RR+ ) )' % A0), dvei], 'syl',
           '( %s -> E. d e. RR+ A. z e. D %s )' % (A0, LOCS('z').replace(' R ', ' d ')))
CONC = '( abs ` %s ) <_ ( 2 x. ( E x. ( %s x. %s ) ) )' % (IAB, WH, WH)
# --- level A1: a radius r
A1 = '( %s /\\ d e. RR+ )' % A0
rrp = w.s([], 'simpr', '( %s -> d e. RR+ )' % A1)
def d1(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (A1, f))
ps1 = d1(ps0, PS); cz1 = d1(czd, CZD); erp1 = d1(erp, 'E e. RR+'); ac1 = d1(ac, 'A e. CC'); bc1 = d1(bc, 'B e. CC')
LOCR = 'A. s e. D %s' % LOCS('s').replace(' R ', ' d ')
ALZ = 'A. z e. D %s' % LOCS('z').replace(' R ', ' d ')
A2 = '( %s /\\ %s )' % (A1, ALZ)
alz = w.s([], 'simpr', '( %s -> %s )' % (A2, ALZ))
cb1 = w.s([], 'oveq1', '( z = s -> ( z - Z ) = ( s - Z ) )')
cb2 = w.s([w.s([cb1], 'fveq2d', '( z = s -> ( abs ` ( z - Z ) ) = ( abs ` ( s - Z ) ) )')], 'breq1d', '( z = s -> ( ( abs ` ( z - Z ) ) < d <-> ( abs ` ( s - Z ) ) < d ) )')
cb3 = w.s([w.s([w.s([w.s([], 'fveq2', '( z = s -> ( F ` z ) = ( F ` s ) )')], 'oveq1d', '( z = s -> ( ( F ` z ) - %s ) = ( ( F ` s ) - %s ) )' % (FZ, FZ)),
                w.s([cb1], 'oveq2d', '( z = s -> ( C x. ( z - Z ) ) = ( C x. ( s - Z ) ) )')], 'oveq12d',
               '( z = s -> ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) = ( ( ( F ` s ) - %s ) - ( C x. ( s - Z ) ) ) )' % (FZ, FZ))], 'fveq2d',
          '( z = s -> ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) = ( abs ` ( ( ( F ` s ) - %s ) - ( C x. ( s - Z ) ) ) ) )' % (FZ, FZ))
cb4 = w.s([cb3, w.s([w.s([cb1], 'fveq2d', '( z = s -> ( abs ` ( z - Z ) ) = ( abs ` ( s - Z ) ) )')], 'oveq2d', '( z = s -> ( E x. ( abs ` ( z - Z ) ) ) = ( E x. ( abs ` ( s - Z ) ) ) )')], 'breq12d',
          '( z = s -> ( ( abs ` ( ( ( F ` z ) - %s ) - ( C x. ( z - Z ) ) ) ) <_ ( E x. ( abs ` ( z - Z ) ) ) <-> ( abs ` ( ( ( F ` s ) - %s ) - ( C x. ( s - Z ) ) ) ) <_ ( E x. ( abs ` ( s - Z ) ) ) ) )' % (FZ, FZ))
cbv = w.s([w.s([cb2, cb4], 'imbi12d', '( z = s -> ( %s <-> %s ) )' % (LOCS('z').replace(' R ', ' d '), LOCS('s').replace(' R ', ' d ')))], 'cbvralvw', '( %s <-> %s )' % (ALZ, LOCR))
locs = w.s([alz, w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A2, ALZ, LOCR))], 'mpbid', '( %s -> %s )' % (A2, LOCR))
def d2(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (A2, f))
ps2 = d2(ps1, PS); cz2 = d2(cz1, CZD); erp2 = d2(erp1, 'E e. RR+'); rrp2 = d2(rrp, 'd e. RR+')
ac2 = d2(ac1, 'A e. CC'); bc2 = d2(bc1, 'B e. CC')
ar2 = w.s([ac2, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A2, RE('A')))
br2 = w.s([bc2, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A2, RE('B')))
ai2 = w.s([ac2, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A2, IM('A')))
bi2 = w.s([bc2, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A2, IM('B')))
wdr = w.s([br2, ar2], 'resubcld', '( %s -> %s e. RR )' % (A2, WD))
hgr = w.s([bi2, ai2], 'resubcld', '( %s -> %s e. RR )' % (A2, HG))
whr = w.s([wdr, hgr], 'readdcld', '( %s -> %s e. RR )' % (A2, WH))
ex1 = w.s([w.s([whr, w.s([rrp2, w.inst('rpre')], 'syl', '( %s -> d e. RR )' % A2)], 'jca', 'x')], 'id', 'y')
w.lines.pop(); w.lines.pop()
whdr = w.s([whr, rrp2], 'rerpdivcld', '( %s -> ( %s / d ) e. RR )' % (A2, WH))
exb = w.s([whdr, closed(w, A2, '2re', '2 e. RR'), closed(w, A2, '1lt2', '1 < 2'), w.inst('expnbnd')], 'syl3anc', '( %s -> E. k e. NN ( %s / d ) < ( 2 ^ k ) )' % (A2, WH))
# --- level A3: an exponent k
A3 = '( %s /\\ ( k e. NN /\\ ( %s / d ) < ( 2 ^ k ) ) )' % (A2, WH)
knn = w.s([], 'simprl', '( %s -> k e. NN )' % A3)
kgt = w.s([], 'simprr', '( %s -> ( %s / d ) < ( 2 ^ k ) )' % (A3, WH))
def d3(st, f):
    return w.s([st], 'adantr', '( %s -> %s )' % (A3, f))
ps3 = d3(ps2, PS); cz3 = d3(cz2, CZD); erp3 = d3(erp2, 'E e. RR+'); rrp3 = d3(rrp2, 'd e. RR+')
loc3 = d3(locs, LOCR); whr3 = d3(whr, '%s e. RR' % WH); wdr3 = d3(wdr, '%s e. RR' % WD); hgr3 = d3(hgr, '%s e. RR' % HG)
kn0 = w.s([knn, w.inst('nnnn0')], 'syl', '( %s -> k e. NN0 )' % A3)
rp2 = closed(w, A3, '2rp', '2 e. RR+')
pk = w.s([rp2, w.s([knn, w.inst('nnz')], 'syl', '( %s -> k e. ZZ )' % A3)], 'rpexpcld', '( %s -> ( 2 ^ k ) e. RR+ )' % A3)
pkr = w.s([pk, w.inst('rpre')], 'syl', '( %s -> ( 2 ^ k ) e. RR )' % A3)
QQ = '( %s / ( 2 ^ k ) )' % WH
qr = w.s([whr3, pk], 'rerpdivcld', '( %s -> %s e. RR )' % (A3, QQ))
rre = w.s([rrp3, w.inst('rpre')], 'syl', '( %s -> d e. RR )' % A3)
lt1 = w.s([w.s([whr3, pkr, rrp3], 'ltdivmuld', '( %s -> ( ( %s / d ) < ( 2 ^ k ) <-> %s < ( d x. ( 2 ^ k ) ) ) )' % (A3, WH, WH)), kgt], 'mpbid', '( %s -> %s < ( d x. ( 2 ^ k ) ) )' % (A3, WH))
lt2 = w.s([lt1, w.s([w.s([rre], 'recnd', '( %s -> d e. CC )' % A3), w.s([pkr], 'recnd', '( %s -> ( 2 ^ k ) e. CC )' % A3)], 'mulcomd', '( %s -> ( d x. ( 2 ^ k ) ) = ( ( 2 ^ k ) x. d ) )' % A3)], 'breqtrd', '( %s -> %s < ( ( 2 ^ k ) x. d ) )' % (A3, WH))
qlt = w.s([w.s([whr3, rre, pk], 'ltdivmuld', '( %s -> ( %s < d <-> %s < ( ( 2 ^ k ) x. d ) ) )' % (A3, QQ, WH)), lt2], 'mpbird', '( %s -> %s < d )' % (A3, QQ))
AK = F1(NK('k')); BK = F2(NK('k'))
DMK = '( ( ( Re ` %s ) - ( Re ` %s ) ) + ( ( Im ` %s ) - ( Im ` %s ) ) )' % (BK, AK, BK, AK)
widi = w.s(HH, 'gourwid', '( ( %s /\\ k e. NN0 ) -> ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ ( %s / ( 2 ^ k ) ) /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ ( %s / ( 2 ^ k ) ) ) )' % (PS, BK, AK, WD, BK, AK, HG))
wid = w.s([ps3, kn0, widi], 'syl2anc', '( %s -> ( ( ( Re ` %s ) - ( Re ` %s ) ) <_ ( %s / ( 2 ^ k ) ) /\\ ( ( Im ` %s ) - ( Im ` %s ) ) <_ ( %s / ( 2 ^ k ) ) ) )' % (A3, BK, AK, WD, BK, AK, HG))
admi3 = w.s(HH, 'gouradm', '( ( %s /\\ k e. NN0 ) -> %s )' % (PS, INVQ(NK('k'))))
inv3 = w.s([ps3, kn0, admi3], 'syl2anc', '( %s -> %s )' % (A3, INVQ(NK('k'))))
xpk = w.s([inv3, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A3, NK('k')))
akc = w.s([xpk, w.inst('xp1st')], 'syl', '( %s -> %s e. CC )' % (A3, AK))
bkc = w.s([xpk, w.inst('xp2nd')], 'syl', '( %s -> %s e. CC )' % (A3, BK))
ordk = w.s([inv3, w.inst('simp2')], 'syl', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A3, AK, BK, AK, BK))
akr = w.s([akc, w.inst('recl')], 'syl', '( %s -> ( Re ` %s ) e. RR )' % (A3, AK))
bkr = w.s([bkc, w.inst('recl')], 'syl', '( %s -> ( Re ` %s ) e. RR )' % (A3, BK))
aki = w.s([akc, w.inst('imcl')], 'syl', '( %s -> ( Im ` %s ) e. RR )' % (A3, AK))
bki = w.s([bkc, w.inst('imcl')], 'syl', '( %s -> ( Im ` %s ) e. RR )' % (A3, BK))
dk1 = w.s([bkr, akr], 'resubcld', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) e. RR )' % (A3, BK, AK))
dk2 = w.s([bki, aki], 'resubcld', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) e. RR )' % (A3, BK, AK))
dkr = w.s([dk1, dk2], 'readdcld', '( %s -> %s e. RR )' % (A3, DMK))
g1 = w.s([w.s([bkr, akr], 'subge0d', '( %s -> ( 0 <_ ( ( Re ` %s ) - ( Re ` %s ) ) <-> ( Re ` %s ) <_ ( Re ` %s ) ) )' % (A3, BK, AK, AK, BK)), w.s([ordk, w.inst('simpl')], 'syl', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A3, AK, BK))], 'mpbird', '( %s -> 0 <_ ( ( Re ` %s ) - ( Re ` %s ) ) )' % (A3, BK, AK))
g2 = w.s([w.s([bki, aki], 'subge0d', '( %s -> ( 0 <_ ( ( Im ` %s ) - ( Im ` %s ) ) <-> ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A3, BK, AK, AK, BK)), w.s([ordk, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A3, AK, BK))], 'mpbird', '( %s -> 0 <_ ( ( Im ` %s ) - ( Im ` %s ) ) )' % (A3, BK, AK))
dkge = w.s([dk1, dk2, g1, g2], 'addge0d', '( %s -> 0 <_ %s )' % (A3, DMK))
sumq = w.s([w.s([wdr3], 'recnd', '( %s -> %s e. CC )' % (A3, WD)), w.s([hgr3], 'recnd', '( %s -> %s e. CC )' % (A3, HG)), w.s([pkr], 'recnd', '( %s -> ( 2 ^ k ) e. CC )' % A3), w.s([pk, w.inst('rpne0')], 'syl', '( %s -> ( 2 ^ k ) =/= 0 )' % A3)], 'divdird',
           '( %s -> %s = ( ( %s / ( 2 ^ k ) ) + ( %s / ( 2 ^ k ) ) ) )' % (A3, QQ, WD, HG))
dkle = w.s([w.s([dk1, dk2, w.s([wdr3, pk], 'rerpdivcld', '( %s -> ( %s / ( 2 ^ k ) ) e. RR )' % (A3, WD)), w.s([hgr3, pk], 'rerpdivcld', '( %s -> ( %s / ( 2 ^ k ) ) e. RR )' % (A3, HG)),
                 w.s([wid, w.inst('simpl')], 'syl', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) <_ ( %s / ( 2 ^ k ) ) )' % (A3, BK, AK, WD)),
                 w.s([wid, w.inst('simpr')], 'syl', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) <_ ( %s / ( 2 ^ k ) ) )' % (A3, BK, AK, HG))], 'le2addd',
                '( %s -> %s <_ ( ( %s / ( 2 ^ k ) ) + ( %s / ( 2 ^ k ) ) ) )' % (A3, DMK, WD, HG)), w.s([sumq], 'eqcomd', '( %s -> ( ( %s / ( 2 ^ k ) ) + ( %s / ( 2 ^ k ) ) ) = %s )' % (A3, WD, HG, QQ))], 'breqtrd',
           '( %s -> %s <_ %s )' % (A3, DMK, QQ))
dklt = w.s([dkr, qr, rre, dkle, qlt], 'lelttrd', '( %s -> %s < d )' % (A3, DMK))
zki = w.s(HH, 'gourz', '( ( %s /\\ k e. NN0 ) -> %s e. ( %s crect %s ) )' % (PS, Z0, AK, BK))
zk0 = w.s([ps3, kn0, zki], 'syl2anc', '( %s -> %s e. ( %s crect %s ) )' % (A3, Z0, AK, BK))
zk = w.s([w.s(['10'], 'a1i', '( %s -> %s )' % (A3, ZDEF)), zk0], 'eqeltrd', '( %s -> Z e. ( %s crect %s ) )' % (A3, AK, BK))
mlki = w.s([str(i) for i in range(1, 10)], 'gourmlk', '( ( ( %s /\\ %s /\\ k e. NN0 ) /\\ ( E e. RR+ /\\ d e. RR+ /\\ %s ) /\\ ( Z e. ( %s crect %s ) /\\ %s < d ) ) -> ( abs ` ( F rectint %s ) ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )'
            % (PS, CZD, LOCR, AK, BK, DMK, NK('k'), DMK, DMK))
mlk = w.s([w.s([w.s([ps3, cz3, kn0], '3jca', '( %s -> ( %s /\\ %s /\\ k e. NN0 ) )' % (A3, PS, CZD)),
                w.s([erp3, rrp3, loc3], '3jca', '( %s -> ( E e. RR+ /\\ d e. RR+ /\\ %s ) )' % (A3, LOCR)),
                w.s([zk, dklt], 'jca', '( %s -> ( Z e. ( %s crect %s ) /\\ %s < d ) )' % (A3, AK, BK, DMK))], '3jca',
               '( %s -> ( ( %s /\\ %s /\\ k e. NN0 ) /\\ ( E e. RR+ /\\ d e. RR+ /\\ %s ) /\\ ( Z e. ( %s crect %s ) /\\ %s < d ) ) )' % (A3, PS, CZD, LOCR, AK, BK, DMK)), mlki], 'syl',
          '( %s -> ( abs ` ( F rectint %s ) ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A3, NK('k'), DMK, DMK))
# replace DMK by QQ in the bound
ere3 = w.s([erp3, w.inst('rpre')], 'syl', '( %s -> E e. RR )' % A3)
ege3 = w.s([erp3, w.inst('rpge0')], 'syl', '( %s -> 0 <_ E )' % A3)
qge = w.s([dkr, qr, dkge, dkle], 'letrd', '( %s -> 0 <_ %s )' % (A3, QQ))
m1 = w.s([w.s([dkr, qr, w.s([ere3, ege3], 'jca', '( %s -> ( E e. RR /\\ 0 <_ E ) )' % A3)], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( E e. RR /\\ 0 <_ E ) ) )' % (A3, DMK, QQ)), dkle, w.inst('lemul2a')], 'syl2anc',
         '( %s -> ( E x. %s ) <_ ( E x. %s ) )' % (A3, DMK, QQ))
edk = w.s([ere3, dkr], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (A3, DMK))
eq_ = w.s([ere3, qr], 'remulcld', '( %s -> ( E x. %s ) e. RR )' % (A3, QQ))
t2r = closed(w, A3, '2re', '2 e. RR')
t2g = closed(w, A3, '0le2', '0 <_ 2')
m2 = w.s([w.s([edk, eq_, w.s([t2r, t2g], 'jca', '( %s -> ( 2 e. RR /\\ 0 <_ 2 ) )' % A3)], '3jca', '( %s -> ( ( E x. %s ) e. RR /\\ ( E x. %s ) e. RR /\\ ( 2 e. RR /\\ 0 <_ 2 ) ) )' % (A3, DMK, QQ)), m1, w.inst('lemul2a')], 'syl2anc',
         '( %s -> ( 2 x. ( E x. %s ) ) <_ ( 2 x. ( E x. %s ) ) )' % (A3, DMK, QQ))
tdk = w.s([t2r, edk], 'remulcld', '( %s -> ( 2 x. ( E x. %s ) ) e. RR )' % (A3, DMK))
tq = w.s([t2r, eq_], 'remulcld', '( %s -> ( 2 x. ( E x. %s ) ) e. RR )' % (A3, QQ))
m3 = w.s([w.s([tdk, tq, w.s([dkr, dkge], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A3, DMK, DMK))], '3jca', '( %s -> ( ( 2 x. ( E x. %s ) ) e. RR /\\ ( 2 x. ( E x. %s ) ) e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A3, DMK, QQ, DMK, DMK)), m2, w.inst('lemul1a')], 'syl2anc',
         '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A3, DMK, DMK, QQ, DMK))
tqge = w.s([t2r, eq_, t2g, w.s([ere3, qr, ege3, qge], 'mulge0d', '( %s -> 0 <_ ( E x. %s ) )' % (A3, QQ))], 'mulge0d', '( %s -> 0 <_ ( 2 x. ( E x. %s ) ) )' % (A3, QQ))
m4 = w.s([w.s([dkr, qr, w.s([tq, tqge], 'jca', '( %s -> ( ( 2 x. ( E x. %s ) ) e. RR /\\ 0 <_ ( 2 x. ( E x. %s ) ) ) )' % (A3, QQ, QQ))], '3jca',
               '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( ( 2 x. ( E x. %s ) ) e. RR /\\ 0 <_ ( 2 x. ( E x. %s ) ) ) ) )' % (A3, DMK, QQ, QQ, QQ)), dkle, w.inst('lemul2a')], 'syl2anc',
         '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A3, QQ, DMK, QQ, QQ))
bdk = w.s([tdk, dkr], 'remulcld', '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) e. RR )' % (A3, DMK, DMK))
bqd = w.s([tq, dkr], 'remulcld', '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) e. RR )' % (A3, QQ, DMK))
bqq = w.s([tq, qr], 'remulcld', '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) e. RR )' % (A3, QQ, QQ))
bnd = w.s([bdk, bqd, bqq, m3, m4], 'letrd', '( %s -> ( ( 2 x. ( E x. %s ) ) x. %s ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A3, DMK, DMK, QQ, QQ))
# gourabs and the conclusion
absi = w.s(HH, 'gourabs', '( ( %s /\\ k e. NN0 ) -> ( ( abs ` %s ) / ( 4 ^ k ) ) <_ ( abs ` ( F rectint %s ) ) )' % (PS, IAB, NK('k')))
abk = w.s([ps3, kn0, absi], 'syl2anc', '( %s -> ( ( abs ` %s ) / ( 4 ^ k ) ) <_ ( abs ` ( F rectint %s ) ) )' % (A3, IAB, NK('k')))
iabr = w.s([w.s([ps3, w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (A3, IAB))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A3, IAB))
rp4 = w.s([closed(w, A3, '4re', '4 e. RR'), closed(w, A3, '4pos', '0 < 4')], 'elrpd', '( %s -> 4 e. RR+ )' % A3)
e4k = w.s([rp4, w.s([knn, w.inst('nnz')], 'syl', '( %s -> k e. ZZ )' % A3)], 'rpexpcld', '( %s -> ( 4 ^ k ) e. RR+ )' % A3)
q4r = w.s([iabr, e4k], 'rerpdivcld', '( %s -> ( ( abs ` %s ) / ( 4 ^ k ) ) e. RR )' % (A3, IAB))
fik = w.s([w.s([ps3, w.inst('simp3l')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A3), w.s([ps3, w.inst('simp3r')], 'syl', '( %s -> ( A crect B ) C_ D )' % A3)], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )' % A3)
admq = w.s([w.s([inv3, w.inst('simp1')], 'syl', '( %s -> %s e. ( CC X. CC ) )' % (A3, NK('k'))), ordk, w.s([inv3, w.inst('simp3')], 'syl', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A3, AK, BK))], '3jca',
           '( %s -> ( %s e. ( CC X. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( %s crect %s ) C_ ( A crect B ) ) )' % (A3, NK('k'), AK, BK, AK, BK, AK, BK))
rcli = w.s([], 'gourrcl', '( ( ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) /\\ ( %s e. ( CC X. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( %s crect %s ) C_ ( A crect B ) ) ) -> ( F rectint %s ) e. CC )' % (NK('k'), AK, BK, AK, BK, AK, BK, NK('k')))
ikr = w.s([w.s([fik, admq, rcli], 'syl2anc', '( %s -> ( F rectint %s ) e. CC )' % (A3, NK('k')))], 'abscld', '( %s -> ( abs ` ( F rectint %s ) ) e. RR )' % (A3, NK('k')))
ch1 = w.s([q4r, ikr, bqq, abk, w.s([ikr, bdk, bqq, mlk, bnd], 'letrd', '( %s -> ( abs ` ( F rectint %s ) ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A3, NK('k'), QQ, QQ))], 'letrd',
          '( %s -> ( ( abs ` %s ) / ( 4 ^ k ) ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) )' % (A3, IAB, QQ, QQ))
ch2 = w.s([w.s([iabr, bqq, e4k], 'ledivmuld', '( %s -> ( ( ( abs ` %s ) / ( 4 ^ k ) ) <_ ( ( 2 x. ( E x. %s ) ) x. %s ) <-> ( abs ` %s ) <_ ( ( 4 ^ k ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) ) )' % (A3, IAB, QQ, QQ, IAB, QQ, QQ)), ch1], 'mpbid',
          '( %s -> ( abs ` %s ) <_ ( ( 4 ^ k ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) )' % (A3, IAB, QQ, QQ))
# ( 4 ^ k ) = ( ( 2 ^ k ) x. ( 2 ^ k ) )
t2c3 = closed(w, A3, '2cn', '2 e. CC')
e4 = w.s([w.s([w.s([closed(w, A3, '2t2e4', '( 2 x. 2 ) = 4')], 'oveq1d', '( %s -> ( ( 2 x. 2 ) ^ k ) = ( 4 ^ k ) )' % A3)], 'eqcomd', '( %s -> ( 4 ^ k ) = ( ( 2 x. 2 ) ^ k ) )' % A3),
          w.s([t2c3, t2c3, kn0, w.inst('mulexp')], 'syl3anc', '( %s -> ( ( 2 x. 2 ) ^ k ) = ( ( 2 ^ k ) x. ( 2 ^ k ) ) )' % A3)], 'eqtrd',
         '( %s -> ( 4 ^ k ) = ( ( 2 ^ k ) x. ( 2 ^ k ) ) )' % A3)
prdi = w.s([], 'gourprod', '( ( ( ( 2 ^ k ) e. CC /\\ ( 2 ^ k ) =/= 0 ) /\\ ( %s e. CC /\\ E e. CC ) ) -> ( ( ( 2 ^ k ) x. ( 2 ^ k ) ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( 2 x. ( E x. ( %s x. %s ) ) ) )' % (WH, QQ, QQ, WH, WH))
prd = w.s([w.s([w.s([w.s([pkr], 'recnd', '( %s -> ( 2 ^ k ) e. CC )' % A3), w.s([pk, w.inst('rpne0')], 'syl', '( %s -> ( 2 ^ k ) =/= 0 )' % A3)], 'jca', '( %s -> ( ( 2 ^ k ) e. CC /\\ ( 2 ^ k ) =/= 0 ) )' % A3),
                w.s([w.s([whr3], 'recnd', '( %s -> %s e. CC )' % (A3, WH)), w.s([ere3], 'recnd', '( %s -> E e. CC )' % A3)], 'jca', '( %s -> ( %s e. CC /\\ E e. CC ) )' % (A3, WH))], 'jca',
               '( %s -> ( ( ( 2 ^ k ) e. CC /\\ ( 2 ^ k ) =/= 0 ) /\\ ( %s e. CC /\\ E e. CC ) ) )' % (A3, WH)), prdi], 'syl',
          '( %s -> ( ( ( 2 ^ k ) x. ( 2 ^ k ) ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( 2 x. ( E x. ( %s x. %s ) ) ) )' % (A3, QQ, QQ, WH, WH))
fin3 = w.s([ch2, w.s([w.s([e4], 'oveq1d', '( %s -> ( ( 4 ^ k ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( ( ( 2 ^ k ) x. ( 2 ^ k ) ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) )' % (A3, QQ, QQ, QQ, QQ)), prd], 'eqtrd',
                      '( %s -> ( ( 4 ^ k ) x. ( ( 2 x. ( E x. %s ) ) x. %s ) ) = ( 2 x. ( E x. ( %s x. %s ) ) ) )' % (A3, QQ, QQ, WH, WH))], 'breqtrd', '( %s -> %s )' % (A3, CONC))
# discharge the two existentials
imk = w.s([fin3], 'exp32' if False else 'expr', '( ( %s /\\ k e. NN ) -> ( ( %s / d ) < ( 2 ^ k ) -> %s ) )' % (A2, WH, CONC))
rxk = w.s([imk], 'rexlimdva', '( %s -> ( E. k e. NN ( %s / d ) < ( 2 ^ k ) -> %s ) )' % (A2, WH, CONC))
c2s = w.s([exb, rxk], 'mpd', '( %s -> %s )' % (A2, CONC))
imz = w.s([c2s], 'ex', '( %s -> ( %s -> %s ) )' % (A1, ALZ, CONC))
rxz = w.s([imz], 'rexlimdva', '( %s -> ( E. d e. RR+ %s -> %s ) )' % (A0, ALZ, CONC))
w.qed([dve, rxz], 'mpd', '( %s -> %s )' % (A0, CONC))
run(w, True)


# ---- the discharge chain and rectintgour
def tsub(text, m):
    return ' '.join(m.get(t, t) for t in text.split())


ZEXP = '( %s + ( _i x. %s ) )' % (X0, Y0)
CEXP = '( ( CC _D F ) ` %s )' % ZEXP
MZC = {'Z': ZEXP, 'C': CEXP}
OEXP = tsub(ODEF.split('=', 1)[1].strip(), MZC)
SEXP = tsub(SDEF.split('=', 1)[1].strip(), MZC)
TEXP = tsub(TDEF.split('=', 1)[1].strip(), MZC)
CONCF = '( abs ` %s ) <_ ( 2 x. ( E x. ( %s x. %s ) ) )' % (IAB, WH, WH)
A0F = '( %s /\\ E e. RR+ )' % HOLO

w = W('gourfin2', 'The Goursat estimate with the limit point and the remainder discharged.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF), ('L', LDEF), ('N', NDEF)], start=1):
    hyp(w, str(k), 'gourfin2.%s' % nm.lower(), DEF)
eo = w.s([], 'eqid', '%s = %s' % (OEXP, OEXP))
es = w.s([], 'eqid', '%s = %s' % (SEXP, SEXP))
et = w.s([], 'eqid', '%s = %s' % (TEXP, TEXP))
ez = w.s([], 'eqid', '%s = %s' % (ZEXP, ZEXP))
ecc = w.s([], 'eqid', '%s = %s' % (CEXP, CEXP))
w.qed(['1', '2', '3', '4', '5', '6', eo, es, et, ez, ecc], 'gourfin', '( %s -> %s )' % (A0F, CONCF))
run(w, True)

LEXP = LDEF.split('=', 1)[1].strip()
NEXP = tsub(NDEF.split('=', 1)[1].strip(), {'L': LEXP})
CFX = '( NN0 X. { <. A , B >. } )'
OPUV2 = '( u e. _V , v e. _V |-> ( %s ` u ) )' % LEXP
OPAB2 = '( a e. _V , b e. _V |-> ( %s ` a ) )' % LEXP
w = W('gourfin3', 'The Goursat estimate with the selector and the sequence discharged.')
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF)], start=1):
    hyp(w, str(k), 'gourfin3.%s' % nm.lower(), DEF)
idpq = w.s([], 'id', '( p = q -> p = q )')
qh = []
for k, (nm, DEF) in enumerate([('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF)], start=1):
    body = DEF.split('|->', 1)[1].rsplit(')', 1)[0].strip()
    st, nb = w.congr(body, {'p': 'q'}, 'p = q', {'p': idpq})
    cb = w.s([st], 'cbvmptv', '( p e. ( CC X. CC ) |-> %s ) = ( q e. ( CC X. CC ) |-> %s )' % (body, nb))
    qh.append(w.s([str(k), cb], 'eqtri', '%s = ( q e. ( CC X. CC ) |-> %s )' % (nm, nb)))
LBODY2 = LDEF.split('|->', 1)[1].rsplit(')', 1)[0].strip()
stl, nbl = w.congr(LBODY2, {'p': 'q'}, 'p = q', {'p': idpq})
lq = w.s([stl], 'cbvmptv', '%s = ( q e. ( CC X. CC ) |-> %s )' % (LEXP, nbl))
sab1 = w.s([], 'fveq2', '( u = a -> ( %s ` u ) = ( %s ` a ) )' % (LEXP, LEXP))
sab2 = w.s([], 'eqidd', '( v = b -> ( %s ` a ) = ( %s ` a ) )' % (LEXP, LEXP))
mpe = w.s([sab1, sab2], 'cbvmpov', '%s = %s' % (OPUV2, OPAB2))
nq = w.s([mpe, w.inst('seqeq2')], 'ax-mp', 'seq 0 ( %s , %s ) = seq 0 ( %s , %s )' % (OPUV2, CFX, OPAB2, CFX))
w.qed(qh + [lq, nq], 'gourfin2', '( %s -> %s )' % (A0F, CONCF))
run(w, True)


# ---- rectintgour: Cauchy-Goursat for rectangles
w = W('rectintgour', 'Cauchy-Goursat for a rectangle: the boundary integral of a function differentiable on the closed rectangle vanishes.')
idpq = w.s([], 'id', '( p = q -> p = q )')
qh = []
for nm, DEF in [('G', GDEF), ('H', HDEF), ('J', JDEF), ('K', KDEF)]:
    body = DEF.split('|->', 1)[1].rsplit(')', 1)[0].strip()
    st, nb = w.congr(body, {'p': 'q'}, 'p = q', {'p': idpq})
    qh.append(w.s([st], 'cbvmptv', '( p e. ( CC X. CC ) |-> %s ) = ( q e. ( CC X. CC ) |-> %s )' % (body, nb)))
A0 = HOLO
ac = w.s([], 'simp1l', '( %s -> A e. CC )' % A0)
bc = w.s([], 'simp1r', '( %s -> B e. CC )' % A0)
geo = w.s([], 'simp2', '( %s -> %s )' % (A0, GEO))
fcn = w.s([], 'simp3l', '( %s -> F e. ( D -cn-> CC ) )' % A0)
dvs = w.s([], 'simp3r', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
rss = w.s([dvs, w.s([closed(w, A0, 'ssid', 'CC C_ CC'), ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
ps0 = w.s([w.s([ac, bc], 'jca', '( %s -> %s )' % (A0, AB)), geo, w.s([fcn, rss], 'jca', '( %s -> %s )' % (A0, FCN))], '3jca', '( %s -> %s )' % (A0, PS))
icl = w.s([ps0, w.inst('rectintcl')], 'syl', '( %s -> %s e. CC )' % (A0, IAB))
iar = w.s([icl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, IAB))
iag = w.s([icl], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (A0, IAB))
ar = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RE('A')))
br = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RE('B')))
ai = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IM('A')))
bi = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IM('B')))
wdr = w.s([br, ar], 'resubcld', '( %s -> %s e. RR )' % (A0, WD))
hgr = w.s([bi, ai], 'resubcld', '( %s -> %s e. RR )' % (A0, HG))
whr = w.s([wdr, hgr], 'readdcld', '( %s -> %s e. RR )' % (A0, WH))
wdg = w.s([w.s([br, ar], 'subge0d', '( %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (A0, WD, RE('A'), RE('B'))), w.s([geo, w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A0, RE('A'), RE('B')))], 'mpbird', '( %s -> 0 <_ %s )' % (A0, WD))
hgg = w.s([w.s([bi, ai], 'subge0d', '( %s -> ( 0 <_ %s <-> %s <_ %s ) )' % (A0, HG, IM('A'), IM('B'))), w.s([geo, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A0, IM('A'), IM('B')))], 'mpbird', '( %s -> 0 <_ %s )' % (A0, HG))
whg = w.s([wdr, hgr, wdg, hgg], 'addge0d', '( %s -> 0 <_ %s )' % (A0, WH))
# case WH = 0
LE = '( %s /\\ %s = 0 )' % (A0, WH)
whz = w.s([], 'simpr', '( %s -> %s = 0 )' % (LE, WH))
r1 = closed(w, LE, '1rp', '1 e. RR+')
f1 = w.s([qh[0], qh[1], qh[2], qh[3]], 'gourfin3', '( ( %s /\\ 1 e. RR+ ) -> ( abs ` %s ) <_ ( 2 x. ( 1 x. ( %s x. %s ) ) ) )' % (HOLO, IAB, WH, WH))
b1 = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (LE, A0)), r1], 'jca', '( %s -> ( %s /\\ 1 e. RR+ ) )' % (LE, HOLO)), f1], 'syl', '( %s -> ( abs ` %s ) <_ ( 2 x. ( 1 x. ( %s x. %s ) ) ) )' % (LE, IAB, WH, WH))
whc = w.s([w.s([whr], 'adantr', '( %s -> %s e. RR )' % (LE, WH))], 'recnd', '( %s -> %s e. CC )' % (LE, WH))
z1 = w.s([w.s([whz], 'oveq1d', '( %s -> ( %s x. %s ) = ( 0 x. %s ) )' % (LE, WH, WH, WH)), w.s([whc], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (LE, WH))], 'eqtrd', '( %s -> ( %s x. %s ) = 0 )' % (LE, WH, WH))
z2 = w.s([w.s([z1], 'oveq2d', '( %s -> ( 1 x. ( %s x. %s ) ) = ( 1 x. 0 ) )' % (LE, WH, WH)), w.s([closed(w, LE, 'ax-1cn', '1 e. CC')], 'mul01d', '( %s -> ( 1 x. 0 ) = 0 )' % LE)], 'eqtrd', '( %s -> ( 1 x. ( %s x. %s ) ) = 0 )' % (LE, WH, WH))
z3 = w.s([w.s([z2], 'oveq2d', '( %s -> ( 2 x. ( 1 x. ( %s x. %s ) ) ) = ( 2 x. 0 ) )' % (LE, WH, WH)), w.s([closed(w, LE, '2cn', '2 e. CC')], 'mul01d', '( %s -> ( 2 x. 0 ) = 0 )' % LE)], 'eqtrd', '( %s -> ( 2 x. ( 1 x. ( %s x. %s ) ) ) = 0 )' % (LE, WH, WH))
case1 = w.s([b1, z3], 'breqtrd', '( %s -> ( abs ` %s ) <_ 0 )' % (LE, IAB))
# case 0 < WH
LP = '( %s /\\ 0 < %s )' % (A0, WH)
whp = w.s([], 'simpr', '( %s -> 0 < %s )' % (LP, WH))
whrp = w.s([w.s([whr], 'adantr', '( %s -> %s e. RR )' % (LP, WH)), whp], 'elrpd', '( %s -> %s e. RR+ )' % (LP, WH))
PW = '( 2 x. ( %s x. %s ) )' % (WH, WH)
pwrp = w.s([closed(w, LP, '2rp', '2 e. RR+'), w.s([whrp, whrp], 'rpmulcld', '( %s -> ( %s x. %s ) e. RR+ )' % (LP, WH, WH))], 'rpmulcld', '( %s -> %s e. RR+ )' % (LP, PW))
LX = '( %s /\\ x e. RR+ )' % LP
xrp = w.s([], 'simpr', '( %s -> x e. RR+ )' % LX)
pwx = w.s([pwrp], 'adantr', '( %s -> %s e. RR+ )' % (LX, PW))
EX = '( x / %s )' % PW
exrp = w.s([xrp, pwx], 'rpdivcld', '( %s -> %s e. RR+ )' % (LX, EX))
f2 = w.s([qh[0], qh[1], qh[2], qh[3]], 'gourfin3', '( ( %s /\\ %s e. RR+ ) -> ( abs ` %s ) <_ ( 2 x. ( %s x. ( %s x. %s ) ) ) )' % (HOLO, EX, IAB, EX, WH, WH))
b2 = w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (LP, A0))], 'adantr', '( %s -> %s )' % (LX, A0)), exrp], 'jca', '( %s -> ( %s /\\ %s e. RR+ ) )' % (LX, HOLO, EX)), f2], 'syl',
         '( %s -> ( abs ` %s ) <_ ( 2 x. ( %s x. ( %s x. %s ) ) ) )' % (LX, IAB, EX, WH, WH))
whcx = w.s([w.s([w.s([whr], 'adantr', '( %s -> %s e. RR )' % (LP, WH))], 'adantr', '( %s -> %s e. RR )' % (LX, WH))], 'recnd', '( %s -> %s e. CC )' % (LX, WH))
excc = w.s([exrp, w.inst('rpcn')], 'syl', '( %s -> %s e. CC )' % (LX, EX))
e1 = w.s([closed(w, LX, '2cn', '2 e. CC'), excc, w.s([whcx, whcx], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (LX, WH, WH))], 'mul12d',
         '( %s -> ( 2 x. ( %s x. ( %s x. %s ) ) ) = ( %s x. ( 2 x. ( %s x. %s ) ) ) )' % (LX, EX, WH, WH, EX, WH, WH))
e2 = w.s([w.s([xrp, w.inst('rpcn')], 'syl', '( %s -> x e. CC )' % LX), w.s([pwx, w.inst('rpcn')], 'syl', '( %s -> %s e. CC )' % (LX, PW)), w.s([pwx, w.inst('rpne0')], 'syl', '( %s -> %s =/= 0 )' % (LX, PW))], 'divcan1d',
         '( %s -> ( %s x. %s ) = x )' % (LX, EX, PW))
bx = w.s([b2, w.s([e1, e2], 'eqtrd', '( %s -> ( 2 x. ( %s x. ( %s x. %s ) ) ) = x )' % (LX, EX, WH, WH))], 'breqtrd', '( %s -> ( abs ` %s ) <_ x )' % (LX, IAB))
bx2 = w.s([bx, w.s([w.s([w.s([xrp, w.inst('rpcn')], 'syl', '( %s -> x e. CC )' % LX)], 'addlidd', '( %s -> ( 0 + x ) = x )' % LX)], 'eqcomd', '( %s -> x = ( 0 + x ) )' % LX)], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( 0 + x ) )' % (LX, IAB))
ral = w.s([bx2], 'ralrimiva', '( %s -> A. x e. RR+ ( abs ` %s ) <_ ( 0 + x ) )' % (LP, IAB))
iarp = w.s([iar], 'adantr', '( %s -> ( abs ` %s ) e. RR )' % (LP, IAB))
case2 = w.s([w.s([iarp, closed(w, LP, '0re', '0 e. RR'), w.inst('alrple')], 'syl2anc', '( %s -> ( ( abs ` %s ) <_ 0 <-> A. x e. RR+ ( abs ` %s ) <_ ( 0 + x ) ) )' % (LP, IAB, IAB)), ral], 'mpbird', '( %s -> ( abs ` %s ) <_ 0 )' % (LP, IAB))
# combine
dsj = w.s([w.s([closed(w, A0, '0re', '0 e. RR'), whr, w.inst('leloe')], 'syl2anc', '( %s -> ( 0 <_ %s <-> ( 0 < %s \\/ 0 = %s ) ) )' % (A0, WH, WH, WH)), whg], 'mpbid', '( %s -> ( 0 < %s \\/ 0 = %s ) )' % (A0, WH, WH))
case1b = w.s([w.s([], 'simpr', '( %s -> 0 = %s )' % ('( %s /\\ 0 = %s )' % (A0, WH), WH))], 'eqcomd', '( %s -> %s = 0 )' % ('( %s /\\ 0 = %s )' % (A0, WH), WH))
c1b = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % ('( %s /\\ 0 = %s )' % (A0, WH), A0)), case1b], 'jca', '( %s -> %s )' % ('( %s /\\ 0 = %s )' % (A0, WH), LE)), w.s([case1], 'ex', '( %s -> ( %s = 0 -> ( abs ` %s ) <_ 0 ) )' % (A0, WH, IAB))], 'id' if False else 'id', 'x')
w.lines.pop()
c1b = w.s([case1b, w.s([w.s([case1], 'ex', '( %s -> ( %s = 0 -> ( abs ` %s ) <_ 0 ) )' % (A0, WH, IAB))], 'adantr', '( %s -> ( %s = 0 -> ( abs ` %s ) <_ 0 ) )' % ('( %s /\\ 0 = %s )' % (A0, WH), WH, IAB))], 'mpd',
           '( %s -> ( abs ` %s ) <_ 0 )' % ('( %s /\\ 0 = %s )' % (A0, WH), IAB))
le0 = w.s([dsj, case2, c1b], 'mpjaodan', '( %s -> ( abs ` %s ) <_ 0 )' % (A0, IAB))
eq0 = w.s([w.s([iar, closed(w, A0, '0re', '0 e. RR'), w.inst('letri3')], 'syl2anc', '( %s -> ( ( abs ` %s ) = 0 <-> ( ( abs ` %s ) <_ 0 /\\ 0 <_ ( abs ` %s ) ) ) )' % (A0, IAB, IAB, IAB)),
           w.s([le0, iag], 'jca', '( %s -> ( ( abs ` %s ) <_ 0 /\\ 0 <_ ( abs ` %s ) ) )' % (A0, IAB, IAB))], 'mpbird', '( %s -> ( abs ` %s ) = 0 )' % (A0, IAB))
w.qed([eq0, w.s([icl, w.inst('abs00')], 'syl', '( %s -> ( ( abs ` %s ) = 0 <-> %s = 0 ) )' % (A0, IAB, IAB))], 'mpbid', '( %s -> %s = 0 )' % (A0, IAB))
run(w)
