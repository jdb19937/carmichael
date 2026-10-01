"""Sortie C0c batch 8: the extended difference quotient (Mathlib's dslope)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

CCP = '( CC \\ { P } )'
CC0 = '( CC \\ { 0 } )'
RINVF = '( z e. %s |-> ( 1 / ( z - P ) ) )' % CCP
EP = '( D \\ { P } )'
QUO = lambda X: '( ( ( F ` %s ) - ( F ` P ) ) / ( %s - P ) )' % (X, X)
DSF = '( z e. D |-> if ( z = P , C , %s ) )' % QUO('z')
QPF = '( z e. %s |-> %s )' % (EP, QUO('z'))
FP = '( F e. ( D -cn-> CC ) /\\ P e. D )'

# ---- rinvcn: 1 / ( z - P ) is continuous off P
w = W('rinvcn', 'The function 1 / ( z - P ) is continuous on the complex plane with P removed.')
A0 = 'P e. CC'
A1 = '( %s /\\ z e. %s )' % (A0, CCP)
pc = w.s([], 'id', '( %s -> P e. CC )' % A0)
ssc = closed(w, A0, 'difss', '%s C_ CC' % CCP)
ccc = closed(w, A0, 'ssid', 'CC C_ CC')
idm = w.s([ssc, ccc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( z e. %s |-> z ) e. ( %s -cn-> CC ) )' % (A0, CCP, CCP))
cpm = w.s([pc, ssc, ccc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. %s |-> P ) e. ( %s -cn-> CC ) )' % (A0, CCP, CCP))
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
scn = w.s([w.s([ej], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i',
          '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
sub = w.s([ej, scn, idm, cpm], 'cncfmpt2f', '( %s -> ( z e. %s |-> ( z - P ) ) e. ( %s -cn-> CC ) )' % (A0, CCP, CCP))
# the inner map lands in ( CC \ { 0 } )
zm = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, CCP))
zc = w.s([zm, w.inst('eldifi')], 'syl', '( %s -> z e. CC )' % A1)
zne = w.s([w.s([zm, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
zpne = w.s([zc, pc1, zne], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
zpc = w.s([zc, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
zp0 = w.s([w.s([zpc, zpne], 'jca', '( %s -> ( ( z - P ) e. CC /\\ ( z - P ) =/= 0 ) )' % A1), w.inst('eldifsn')], 'sylibr',
          '( %s -> ( z - P ) e. %s )' % (A1, CC0))
eqi = w.s([], 'eqid', '( z e. %s |-> ( z - P ) ) = ( z e. %s |-> ( z - P ) )' % (CCP, CCP))
fmp = w.s([zp0, eqi], 'fmptd', '( %s -> ( z e. %s |-> ( z - P ) ) : %s --> %s )' % (A0, CCP, CCP, CC0))
ss0 = closed(w, A0, 'difss', '%s C_ CC' % CC0)
cdm = w.s([ss0, sub, w.inst('cncfcdm')], 'syl2anc',
          '( %s -> ( ( z e. %s |-> ( z - P ) ) e. ( %s -cn-> %s ) <-> ( z e. %s |-> ( z - P ) ) : %s --> %s ) )' % (A0, CCP, CCP, CC0, CCP, CCP, CC0))
ab = w.s([fmp, cdm], 'mpbird', '( %s -> ( z e. %s |-> ( z - P ) ) e. ( %s -cn-> %s ) )' % (A0, CCP, CCP, CC0))
e1 = w.s([], 'eqid', '( x e. %s |-> ( 1 / x ) ) = ( x e. %s |-> ( 1 / x ) )' % (CC0, CC0))
cd0 = w.s([e1], 'cdivcncf', '( 1 e. CC -> ( x e. %s |-> ( 1 / x ) ) e. ( %s -cn-> CC ) )' % (CC0, CC0))
cd = w.s([w.s([], 'ax-1cn', '1 e. CC'), cd0], 'ax-mp', '( x e. %s |-> ( 1 / x ) ) e. ( %s -cn-> CC )' % (CC0, CC0))
cdd = w.s([cd], 'a1i', '( %s -> ( x e. %s |-> ( 1 / x ) ) e. ( %s -cn-> CC ) )' % (A0, CC0, CC0))
bc = closed(w, A0, 'ssid', '%s C_ %s' % (CC0, CC0))
nf = w.s([], 'nfv', 'F/ z %s' % A0)
st = w.s([], 'oveq2', '( x = ( z - P ) -> ( 1 / x ) = ( 1 / ( z - P ) ) )')
w.qed([nf, ab, cdd, bc, st], 'cncfcompt2', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RINVF, CCP)); run(w)

# ---- dsqcn: the difference quotient is continuous off P
w = W('dsqcn', 'The difference quotient of a continuous function at a point of its domain is continuous off that point.')
A0 = FP
A1 = '( %s /\\ z e. %s )' % (A0, EP)
fcn = w.s([], 'simpl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pd = w.s([], 'simpr', '( %s -> P e. D )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
fpc = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
ess = closed(w, A0, 'difss', '%s C_ D' % EP)
essc = w.s([ess, dss], 'sstrd', '( %s -> %s C_ CC )' % (A0, EP))
ccc = closed(w, A0, 'ssid', 'CC C_ CC')
fres = w.s([ess, w.inst('rescncf')], 'syl', '( %s -> ( F e. ( D -cn-> CC ) -> ( F |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, EP, EP))
fres2 = w.s([fres, fcn], 'mpd', '( %s -> ( F |` %s ) e. ( %s -cn-> CC ) )' % (A0, EP, EP))
fmpt = w.s([ff], 'feqmptd', '( %s -> F = ( z e. D |-> ( F ` z ) ) )' % A0)
rsm = w.s([ess, w.inst('resmpt')], 'syl', '( %s -> ( ( z e. D |-> ( F ` z ) ) |` %s ) = ( z e. %s |-> ( F ` z ) ) )' % (A0, EP, EP))
fr3 = w.s([w.s([fmpt], 'reseq1d', '( %s -> ( F |` %s ) = ( ( z e. D |-> ( F ` z ) ) |` %s ) )' % (A0, EP, EP)), rsm], 'eqtrd',
          '( %s -> ( F |` %s ) = ( z e. %s |-> ( F ` z ) ) )' % (A0, EP, EP))
fmp = w.s([fr3, fres2], 'eqeltrrd', '( %s -> ( z e. %s |-> ( F ` z ) ) e. ( %s -cn-> CC ) )' % (A0, EP, EP))
cpm = w.s([fpc, essc, ccc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( z e. %s |-> ( F ` P ) ) e. ( %s -cn-> CC ) )' % (A0, EP, EP))
ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
scn = w.s([w.s([ej], 'subcn', '- e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> - e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
mcn = w.s([w.s([ej], 'mulcn', 'x. e. ( ( %s tX %s ) Cn %s )' % (TOP, TOP, TOP))], 'a1i', '( %s -> x. e. ( ( %s tX %s ) Cn %s ) )' % (A0, TOP, TOP, TOP))
num = w.s([ej, scn, fmp, cpm], 'cncfmpt2f', '( %s -> ( z e. %s |-> ( ( F ` z ) - ( F ` P ) ) ) e. ( %s -cn-> CC ) )' % (A0, EP, EP))
# the reciprocal factor, from rinvcn restricted
pcx = w.s([dss, pd], 'sseldd', '( %s -> P e. CC )' % A0)
riv = w.s([pcx, w.inst('rinvcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, RINVF, CCP))
epss = w.s([w.s([ess, dss], 'sstrd', '( %s -> %s C_ CC )' % (A0, EP))] if False else [], 'id', '') if False else None
# ( D \ { P } ) C_ ( CC \ { P } )
epc = w.s([dss, w.inst('difss2') if False else w.inst('ssdif')], 'syl', '( %s -> %s C_ %s )' % (A0, EP, CCP))
rres = w.s([w.s([epc, w.inst('rescncf')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, RINVF, CCP, RINVF, EP, EP)), riv],
           'mpd', '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0, RINVF, EP, EP))
rsm2 = w.s([epc, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = ( z e. %s |-> ( 1 / ( z - P ) ) ) )' % (A0, RINVF, EP, EP))
rmp = w.s([rsm2, rres], 'eqeltrrd', '( %s -> ( z e. %s |-> ( 1 / ( z - P ) ) ) e. ( %s -cn-> CC ) )' % (A0, EP, EP))
prod = w.s([ej, mcn, num, rmp], 'cncfmpt2f',
           '( %s -> ( z e. %s |-> ( ( ( F ` z ) - ( F ` P ) ) x. ( 1 / ( z - P ) ) ) ) e. ( %s -cn-> CC ) )' % (A0, EP, EP))
# rewrite the product as the quotient
zm = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, EP))
zd = w.s([w.s([ess], 'adantr', '( %s -> %s C_ D )' % (A1, EP)), zm], 'sseldd', '( %s -> z e. D )' % A1)
zne = w.s([w.s([zm, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. D /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
zc = w.s([w.s([dss], 'adantr', '( %s -> D C_ CC )' % A1), zd], 'sseldd', '( %s -> z e. CC )' % A1)
pc1 = w.s([pcx], 'adantr', '( %s -> P e. CC )' % A1)
zpne = w.s([zc, pc1, zne], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A1)
zpc = w.s([zc, pc1], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
fzc = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A1)
nc = w.s([fzc, w.s([fpc], 'adantr', '( %s -> ( F ` P ) e. CC )' % A1)], 'subcld', '( %s -> ( ( F ` z ) - ( F ` P ) ) e. CC )' % A1)
dv = w.s([nc, zpc, zpne], 'divrecd', '( %s -> %s = ( ( ( F ` z ) - ( F ` P ) ) x. ( 1 / ( z - P ) ) ) )' % (A1, QUO('z')))
mp2 = w.s([dv], 'mpteq2dva', '( %s -> %s = ( z e. %s |-> ( ( ( F ` z ) - ( F ` P ) ) x. ( 1 / ( z - P ) ) ) ) )' % (A0, QPF, EP))
w.qed([mp2, prod], 'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, QPF, EP)); run(w)

IFB = 'if ( z = P , C , %s )' % QUO('z')

def qcong(w, X):
    """steps for ( z = X -> QUO(z) = QUO(X) )"""
    c1 = w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (X, X))
    c2 = w.s([c1], 'oveq1d', '( z = %s -> ( ( F ` z ) - ( F ` P ) ) = ( ( F ` %s ) - ( F ` P ) ) )' % (X, X))
    c3 = w.s([], 'oveq1', '( z = %s -> ( z - P ) = ( %s - P ) )' % (X, X))
    return w.s([c2, c3], 'oveq12d', '( z = %s -> %s = %s )' % (X, QUO('z'), QUO(X)))

# ---- dsvaln: the value of the extended difference quotient off P
w = W('dsvaln', 'The value of the extended difference quotient away from the base point.')
A0 = '( %s /\\ ( Z e. D /\\ Z =/= P ) )' % FP
A2 = '( %s /\\ z = Z )' % A0
fcn = w.s([], 'simpll', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pd = w.s([], 'simplr', '( %s -> P e. D )' % A0)
zd = w.s([], 'simprl', '( %s -> Z e. D )' % A0)
zne = w.s([], 'simprr', '( %s -> Z =/= P )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
zc = w.s([dss, zd], 'sseldd', '( %s -> Z e. CC )' % A0)
pc = w.s([dss, pd], 'sseldd', '( %s -> P e. CC )' % A0)
zpne = w.s([zc, pc, zne], 'subne0d', '( %s -> ( Z - P ) =/= 0 )' % A0)
zpc = w.s([zc, pc], 'subcld', '( %s -> ( Z - P ) e. CC )' % A0)
nc = w.s([w.s([ff, zd], 'ffvelcdmd', '( %s -> ( F ` Z ) e. CC )' % A0), w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)],
         'subcld', '( %s -> ( ( F ` Z ) - ( F ` P ) ) e. CC )' % A0)
qc = w.s([nc, zpc, zpne], 'divcld', '( %s -> %s e. CC )' % (A0, QUO('Z')))
zeq = w.s([], 'simpr', '( %s -> z = Z )' % A2)
zne2 = w.s([zeq, w.s([zne], 'adantr', '( %s -> Z =/= P )' % A2)], 'eqnetrd', '( %s -> z =/= P )' % A2)
iff = w.s([w.s([zne2], 'neneqd', '( %s -> -. z = P )' % A2), w.inst('iffalse')], 'syl', '( %s -> %s = %s )' % (A2, IFB, QUO('z')))
cg = qcong(w, 'Z')
h2 = w.s([iff, w.s([zeq, cg], 'syl' if False else 'syl', '( %s -> %s = %s )' % (A2, QUO('z'), QUO('Z')))], 'eqtrd',
         '( %s -> %s = %s )' % (A2, IFB, QUO('Z')))
h1 = w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, DSF, DSF))
w.qed([h1, h2, zd, qc], 'fvmptd', '( %s -> ( %s ` Z ) = %s )' % (A0, DSF, QUO('Z'))); run(w)

# ---- dsvalp: the value at the base point
w = W('dsvalp', 'The value of the extended difference quotient at the base point.')
A0 = '( P e. D /\\ C e. CC )'
A2 = '( %s /\\ z = P )' % A0
pd = w.s([], 'simpl', '( %s -> P e. D )' % A0)
cc = w.s([], 'simpr', '( %s -> C e. CC )' % A0)
h1 = w.s([], 'eqidd', '( %s -> %s = %s )' % (A0, DSF, DSF))
h2 = w.s([w.s([], 'simpr', '( %s -> z = P )' % A2), w.inst('iftrue')], 'syl', '( %s -> %s = C )' % (A2, IFB))
w.qed([h1, h2, pd, cc], 'fvmptd', '( %s -> ( %s ` P ) = C )' % (A0, DSF)); run(w)

# ---- dsres: the restriction off P is the plain difference quotient
w = W('dsres', 'Away from the base point the extended difference quotient is the plain one.')
A0 = FP
A1 = '( %s /\\ z e. %s )' % (A0, EP)
ess = closed(w, A0, 'difss', '%s C_ D' % EP)
rs = w.s([ess, w.inst('resmpt')], 'syl', '( %s -> ( %s |` %s ) = ( z e. %s |-> %s ) )' % (A0, DSF, EP, EP, IFB))
zm = w.s([], 'simpr', '( %s -> z e. %s )' % (A1, EP))
zne = w.s([w.s([zm, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. D /\\ z =/= P ) )' % A1), w.inst('simpr')], 'syl', '( %s -> z =/= P )' % A1)
iff = w.s([w.s([zne], 'neneqd', '( %s -> -. z = P )' % A1), w.inst('iffalse')], 'syl', '( %s -> %s = %s )' % (A1, IFB, QUO('z')))
mp = w.s([iff], 'mpteq2dva', '( %s -> ( z e. %s |-> %s ) = %s )' % (A0, EP, IFB, QPF))
w.qed([rs, mp], 'eqtrd', '( %s -> ( %s |` %s ) = %s )' % (A0, DSF, EP, QPF)); run(w)

# ---- dsf: the extended difference quotient is a function into CC
w = W('dsf', 'The extended difference quotient maps the domain into the complex numbers.')
A0 = '( F e. ( D -cn-> CC ) /\\ P e. D /\\ C e. CC )'
A1 = '( %s /\\ z e. D )' % A0
A2 = '( %s /\\ z = P )' % A1
A3 = '( %s /\\ z =/= P )' % A1
fcn = w.s([], 'simp1', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pd = w.s([], 'simp2', '( %s -> P e. D )' % A0)
cc = w.s([], 'simp3', '( %s -> C e. CC )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
c2 = w.s([w.s([w.s([], 'simpr', '( %s -> z = P )' % A2), w.inst('iftrue')], 'syl', '( %s -> %s = C )' % (A2, IFB)),
          w.s([w.s([cc], 'adantr', '( %s -> C e. CC )' % A1)], 'adantr', '( %s -> C e. CC )' % A2)], 'eqeltrd',
         '( %s -> %s e. CC )' % (A2, IFB))
zd3 = w.s([], 'simplr', '( %s -> z e. D )' % A3)
zne3 = w.s([], 'simpr', '( %s -> z =/= P )' % A3)
dss3 = w.s([w.s([dss], 'adantr', '( %s -> D C_ CC )' % A1)], 'adantr', '( %s -> D C_ CC )' % A3)
ff3 = w.s([w.s([ff], 'adantr', '( %s -> F : D --> CC )' % A1)], 'adantr', '( %s -> F : D --> CC )' % A3)
pd3 = w.s([w.s([pd], 'adantr', '( %s -> P e. D )' % A1)], 'adantr', '( %s -> P e. D )' % A3)
zc3 = w.s([dss3, zd3], 'sseldd', '( %s -> z e. CC )' % A3)
pc3 = w.s([dss3, pd3], 'sseldd', '( %s -> P e. CC )' % A3)
nc3 = w.s([w.s([ff3, zd3], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % A3), w.s([ff3, pd3], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A3)],
          'subcld', '( %s -> ( ( F ` z ) - ( F ` P ) ) e. CC )' % A3)
qc3 = w.s([nc3, w.s([zc3, pc3], 'subcld', '( %s -> ( z - P ) e. CC )' % A3), w.s([zc3, pc3, zne3], 'subne0d', '( %s -> ( z - P ) =/= 0 )' % A3)],
          'divcld', '( %s -> %s e. CC )' % (A3, QUO('z')))
c3 = w.s([w.s([w.s([zne3], 'neneqd', '( %s -> -. z = P )' % A3), w.inst('iffalse')], 'syl', '( %s -> %s = %s )' % (A3, IFB, QUO('z'))), qc3],
         'eqeltrd', '( %s -> %s e. CC )' % (A3, IFB))
cl = w.s([c2, c3], 'pm2.61dane', '( %s -> %s e. CC )' % (A1, IFB))
w.qed([cl, w.s([], 'eqid', '%s = %s' % (DSF, DSF))], 'fmptd', '( %s -> %s : D --> CC )' % (A0, DSF)); run(w)

ABS = '( abs ` ( S - P ) )'
Q = '( ( d x. %s ) / ( d + %s ) )' % (ABS, ABS)
def PSI(x, X):
    return '( ( abs ` ( %s - S ) ) < %s -> ( abs ` ( ( %s ` %s ) - ( %s ` S ) ) ) < E )' % (X, x, QPF, X, QPF)
def CHI(x, X):
    return '( ( abs ` ( %s - S ) ) < %s -> ( abs ` ( ( %s ` %s ) - ( %s ` S ) ) ) < E )' % (X, x, DSF, X, DSF)
GOALB = lambda x: 'A. v e. D %s' % CHI(x, 'v')
GOAL = 'E. k e. RR+ %s' % GOALB('k')

# ---- dscnp: the continuity estimate at a point other than the base point
w = W('dscnp', 'The epsilon-delta estimate for the extended difference quotient away from the base point.')
FPC = '( F e. ( D -cn-> CC ) /\\ P e. D /\\ C e. CC )'
A0 = '( %s /\\ ( S e. D /\\ S =/= P /\\ E e. RR+ ) )' % FPC
A1 = '( %s /\\ ( d e. RR+ /\\ A. t e. %s %s ) )' % (A0, EP, PSI('d', 't'))
A2 = '( %s /\\ v e. D )' % A1
A3 = '( %s /\\ ( abs ` ( v - S ) ) < %s )' % (A2, Q)
A4 = '( %s /\\ v = P )' % A3
fp3 = w.s([], 'simpl', '( %s -> %s )' % (A0, FPC))
sne3 = w.s([], 'simpr', '( %s -> ( S e. D /\\ S =/= P /\\ E e. RR+ ) )' % A0)
fcn = w.s([fp3, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pd = w.s([fp3, w.inst('simp2')], 'syl', '( %s -> P e. D )' % A0)
sd = w.s([sne3, w.inst('simp1')], 'syl', '( %s -> S e. D )' % A0)
sne = w.s([sne3, w.inst('simp2')], 'syl', '( %s -> S =/= P )' % A0)
erp = w.s([sne3, w.inst('simp3')], 'syl', '( %s -> E e. RR+ )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
sc = w.s([dss, sd], 'sseldd', '( %s -> S e. CC )' % A0)
pc = w.s([dss, pd], 'sseldd', '( %s -> P e. CC )' % A0)
spc = w.s([sc, pc], 'subcld', '( %s -> ( S - P ) e. CC )' % A0)
spne = w.s([sc, pc, sne], 'subne0d', '( %s -> ( S - P ) =/= 0 )' % A0)
absr = w.s([spc], 'abscld', '( %s -> %s e. RR )' % (A0, ABS))
absp = w.s([spne, w.s([spc, w.inst('absgt0')], 'syl', '( %s -> ( ( S - P ) =/= 0 <-> 0 < %s ) )' % (A0, ABS))], 'mpbid', '( %s -> 0 < %s )' % (A0, ABS))
absrp = w.s([absr, absp], 'elrpd', '( %s -> %s e. RR+ )' % (A0, ABS))
sep = w.s([w.s([sd, sne], 'jca', '( %s -> ( S e. D /\\ S =/= P ) )' % A0), w.inst('eldifsn')], 'sylibr', '( %s -> S e. %s )' % (A0, EP))
dsq = w.s([w.s([fcn, pd], 'jca', '( %s -> %s )' % (A0, FP)), w.inst('dsqcn')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, QPF, EP))
exi = w.s([dsq, sep, erp, w.inst('cncfi')], 'syl3anc', '( %s -> E. d e. RR+ A. t e. %s %s )' % (A0, EP, PSI('d', 't')))
# under A1
drp = w.s([w.s([], 'simpr', '( %s -> ( d e. RR+ /\\ A. t e. %s %s ) )' % (A1, EP, PSI('d', 't'))), w.inst('simpl')], 'syl', '( %s -> d e. RR+ )' % A1)
alt = w.s([w.s([], 'simpr', '( %s -> ( d e. RR+ /\\ A. t e. %s %s ) )' % (A1, EP, PSI('d', 't'))), w.inst('simpr')], 'syl',
          '( %s -> A. t e. %s %s )' % (A1, EP, PSI('d', 't')))
sm = w.s([drp, w.s([absrp], 'adantr', '( %s -> %s e. RR+ )' % (A1, ABS)), w.inst('softmin')], 'syl2anc',
         '( %s -> ( %s e. RR+ /\\ ( %s <_ d /\\ %s <_ %s ) ) )' % (A1, Q, Q, Q, ABS))
qrp = w.s([sm, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A1, Q))
qled = w.s([sm, w.inst('simprl')], 'syl', '( %s -> %s <_ d )' % (A1, Q))
qlea = w.s([sm, w.inst('simprr')], 'syl', '( %s -> %s <_ %s )' % (A1, Q, ABS))
# under A3
vd = w.s([], 'simplr', '( %s -> v e. D )' % A3)
ltq = w.s([], 'simpr', '( %s -> ( abs ` ( v - S ) ) < %s )' % (A3, Q))
sc3 = w.s([sc], 'ad3antrrr' if False else 'ad3antrrr', '( %s -> S e. CC )' % A3)
pc3 = w.s([pc], 'ad3antrrr', '( %s -> P e. CC )' % A3)
dss3 = w.s([dss], 'ad3antrrr', '( %s -> D C_ CC )' % A3)
er3 = w.s([erp], 'ad3antrrr', '( %s -> E e. RR+ )' % A3)
vc = w.s([dss3, vd], 'sseldd', '( %s -> v e. CC )' % A3)
avs = w.s([w.s([vc, sc3], 'subcld', '( %s -> ( v - S ) e. CC )' % A3)], 'abscld', '( %s -> ( abs ` ( v - S ) ) e. RR )' % A3)
qr3 = w.s([w.s([qrp], 'ad2antrr', '( %s -> %s e. RR+ )' % (A3, Q))], 'rpred', '( %s -> %s e. RR )' % (A3, Q))
dr3 = w.s([w.s([drp], 'ad2antrr', '( %s -> d e. RR+ )' % A3)], 'rpred', '( %s -> d e. RR )' % A3)
ar3 = w.s([absr], 'ad3antrrr', '( %s -> %s e. RR )' % (A3, ABS))
ltd = w.s([avs, qr3, dr3, ltq, w.s([qled], 'ad2antrr', '( %s -> %s <_ d )' % (A3, Q))], 'ltletrd', '( %s -> ( abs ` ( v - S ) ) < d )' % A3)
lta = w.s([avs, qr3, ar3, ltq, w.s([qlea], 'ad2antrr', '( %s -> %s <_ %s )' % (A3, Q, ABS))], 'ltletrd', '( %s -> ( abs ` ( v - S ) ) < %s )' % (A3, ABS))
# v =/= P
veq = w.s([], 'simpr', '( %s -> v = P )' % A4)
o1 = w.s([veq], 'oveq1d', '( %s -> ( v - S ) = ( P - S ) )' % A4)
o2 = w.s([o1], 'fveq2d', '( %s -> ( abs ` ( v - S ) ) = ( abs ` ( P - S ) ) )' % A4)
o3 = w.s([w.s([pc3], 'adantr', '( %s -> P e. CC )' % A4), w.s([sc3], 'adantr', '( %s -> S e. CC )' % A4), w.inst('abssub')], 'syl2anc',
         '( %s -> ( abs ` ( P - S ) ) = %s )' % (A4, ABS))
o4 = w.s([w.s([o2, o3], 'eqtrd', '( %s -> ( abs ` ( v - S ) ) = %s )' % (A4, ABS))], 'eqcomd', '( %s -> %s = ( abs ` ( v - S ) ) )' % (A4, ABS))
bad = w.s([o4, w.s([lta], 'adantr', '( %s -> ( abs ` ( v - S ) ) < %s )' % (A4, ABS))], 'eqbrtrd', '( %s -> %s < %s )' % (A4, ABS, ABS))
nbad = w.s([w.s([ar3], 'adantr', '( %s -> %s e. RR )' % (A4, ABS)), w.inst('ltnr')], 'syl', '( %s -> -. %s < %s )' % (A4, ABS, ABS))
vne = w.s([w.s([bad, nbad], 'pm2.65da', '( %s -> -. v = P )' % A3)], 'neqned', '( %s -> v =/= P )' % A3)
vep = w.s([w.s([vd, vne], 'jca', '( %s -> ( v e. D /\\ v =/= P ) )' % A3), w.inst('eldifsn')], 'sylibr', '( %s -> v e. %s )' % (A3, EP))
# PSI at v
t1 = w.s([], 'oveq1', '( t = v -> ( t - S ) = ( v - S ) )')
t2 = w.s([t1], 'fveq2d', '( t = v -> ( abs ` ( t - S ) ) = ( abs ` ( v - S ) ) )')
t3 = w.s([t2], 'breq1d', '( t = v -> ( ( abs ` ( t - S ) ) < d <-> ( abs ` ( v - S ) ) < d ) )')
t4 = w.s([], 'fveq2', '( t = v -> ( %s ` t ) = ( %s ` v ) )' % (QPF, QPF))
t5 = w.s([t4], 'oveq1d', '( t = v -> ( ( %s ` t ) - ( %s ` S ) ) = ( ( %s ` v ) - ( %s ` S ) ) )' % (QPF, QPF, QPF, QPF))
t6 = w.s([w.s([t5], 'fveq2d', '( t = v -> ( abs ` ( ( %s ` t ) - ( %s ` S ) ) ) = ( abs ` ( ( %s ` v ) - ( %s ` S ) ) ) )' % (QPF, QPF, QPF, QPF))],
         'breq1d', '( t = v -> ( ( abs ` ( ( %s ` t ) - ( %s ` S ) ) ) < E <-> ( abs ` ( ( %s ` v ) - ( %s ` S ) ) ) < E ) )' % (QPF, QPF, QPF, QPF))
tsub = w.s([t3, t6], 'imbi12d', '( t = v -> ( %s <-> %s ) )' % (PSI('d', 't'), PSI('d', 'v')))
alt3 = w.s([alt], 'ad2antrr', '( %s -> A. t e. %s %s )' % (A3, EP, PSI('d', 't')))
psiv = w.s([tsub, alt3, vep], 'rspcdva', '( %s -> %s )' % (A3, PSI('d', 'v')))
ltq2 = w.s([psiv, ltd], 'mpd', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` S ) ) ) < E )' % (A3, QPF, QPF))
# transfer to DSF
res = w.s([w.s([w.s([fcn, pd], 'jca', '( %s -> %s )' % (A0, FP)), w.inst('dsres')], 'syl', '( %s -> ( %s |` %s ) = %s )' % (A0, DSF, EP, QPF))],
          'ad3antrrr', '( %s -> ( %s |` %s ) = %s )' % (A3, DSF, EP, QPF))
def transfer(X, mem):
    a = w.s([res], 'fveq1d', '( %s -> ( ( %s |` %s ) ` %s ) = ( %s ` %s ) )' % (A3, DSF, EP, X, QPF, X))
    b = w.s([mem, w.inst('fvres')], 'syl', '( %s -> ( ( %s |` %s ) ` %s ) = ( %s ` %s ) )' % (A3, DSF, EP, X, DSF, X))
    return w.s([a, b], 'eqtr3d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A3, QPF, X, DSF, X))
sep3 = w.s([sep], 'ad3antrrr', '( %s -> S e. %s )' % (A3, EP))
tv = transfer('v', vep); ts = transfer('S', sep3)
fin = w.s([w.s([w.s([tv, ts], 'oveq12d', '( %s -> ( ( %s ` v ) - ( %s ` S ) ) = ( ( %s ` v ) - ( %s ` S ) ) )' % (A3, QPF, QPF, DSF, DSF))],
                'fveq2d', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` S ) ) ) = ( abs ` ( ( %s ` v ) - ( %s ` S ) ) ) )' % (A3, QPF, QPF, DSF, DSF)), ltq2],
          'eqbrtrrd', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` S ) ) ) < E )' % (A3, DSF, DSF))
chi = w.s([fin], 'ex', '( %s -> %s )' % (A2, CHI(Q, 'v')))
gb = w.s([chi], 'ralrimiva', '( %s -> %s )' % (A1, GOALB(Q)))
# existential introduction at the witness Q
k1 = w.s([], 'breq2', '( k = %s -> ( ( abs ` ( v - S ) ) < k <-> ( abs ` ( v - S ) ) < %s ) )' % (Q, Q))
k2 = w.s([k1], 'imbi1d', '( k = %s -> ( %s <-> %s ) )' % (Q, CHI('k', 'v'), CHI(Q, 'v')))
k3 = w.s([k2], 'ralbidv', '( k = %s -> ( %s <-> %s ) )' % (Q, GOALB('k'), GOALB(Q)))
k4 = w.s([k3], 'adantl', '( ( %s /\\ k = %s ) -> ( %s <-> %s ) )' % (A1, Q, GOALB('k'), GOALB(Q)))
exq = w.s([qrp, k4, gb], 'rspcedvd', '( %s -> %s )' % (A1, GOAL))
w.qed([exi, exq], 'rexlimddv', '( %s -> %s )' % (A0, GOAL)); run(w)

HOL = '( F e. ( D -cn-> CC ) /\\ P e. dom ( CC _D F ) /\\ C = ( ( CC _D F ) ` P ) )'
NUM = lambda X: '( ( ( F ` %s ) - ( F ` P ) ) - ( C x. ( %s - P ) ) )' % (X, X)
def THETA(x, X):
    return '( ( abs ` ( %s - P ) ) < %s -> ( abs ` %s ) <_ ( ( E / 2 ) x. ( abs ` ( %s - P ) ) ) )' % (X, x, NUM(X), X)
def CHIP(x, X):
    return '( ( abs ` ( %s - P ) ) < %s -> ( abs ` ( ( %s ` %s ) - ( %s ` P ) ) ) < E )' % (X, x, DSF, X, DSF)
GOALPB = lambda x: 'A. v e. D %s' % CHIP(x, 'v')
GOALP = 'E. k e. RR+ %s' % GOALPB('k')

# ---- dscnq: the continuity estimate at the base point, from the derivative
w = W('dscnq', 'The epsilon-delta estimate for the extended difference quotient at the base point, from differentiability there.')
A0 = '( %s /\\ E e. RR+ )' % HOL
A1 = '( %s /\\ ( n e. RR+ /\\ A. m e. D %s ) )' % (A0, THETA('n', 'm'))
A2 = '( %s /\\ v e. D )' % A1
A3 = '( %s /\\ ( abs ` ( v - P ) ) < n )' % A2
A4 = '( %s /\\ v = P )' % A3
A5 = '( %s /\\ v =/= P )' % A3
hol = w.s([], 'simpl', '( %s -> %s )' % (A0, HOL))
erp = w.s([], 'simpr', '( %s -> E e. RR+ )' % A0)
fcn = w.s([hol, w.inst('simp1')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pdm = w.s([hol, w.inst('simp2')], 'syl', '( %s -> P e. dom ( CC _D F ) )' % A0)
ceq = w.s([hol, w.inst('simp3')], 'syl', '( %s -> C = ( ( CC _D F ) ` P ) )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
ccs = closed(w, A0, 'ssid', 'CC C_ CC')
dvb = w.s([ccs, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
pd = w.s([dvb, pdm], 'sseldd', '( %s -> P e. D )' % A0)
pc = w.s([dss, pd], 'sseldd', '( %s -> P e. CC )' % A0)
dvf = closed(w, A0, 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC')
cc = w.s([ceq, w.s([dvf, pdm], 'ffvelcdmd', '( %s -> ( ( CC _D F ) ` P ) e. CC )' % A0)], 'eqeltrd', '( %s -> C e. CC )' % A0)
ehrp = w.s([erp, w.inst('rphalfcl')], 'syl', '( %s -> ( E / 2 ) e. RR+ )' % A0)
exi = w.s([hol, ehrp, w.inst('gourdveps')], 'syl2anc', '( %s -> E. n e. RR+ A. m e. D %s )' % (A0, THETA('n', 'm')))
nrp = w.s([w.s([], 'simpr', '( %s -> ( n e. RR+ /\\ A. m e. D %s ) )' % (A1, THETA('n', 'm'))), w.inst('simpl')], 'syl', '( %s -> n e. RR+ )' % A1)
alm = w.s([w.s([], 'simpr', '( %s -> ( n e. RR+ /\\ A. m e. D %s ) )' % (A1, THETA('n', 'm'))), w.inst('simpr')], 'syl',
          '( %s -> A. m e. D %s )' % (A1, THETA('n', 'm')))
# under A3
vd = w.s([], 'simplr', '( %s -> v e. D )' % A3)
ltn = w.s([], 'simpr', '( %s -> ( abs ` ( v - P ) ) < n )' % A3)
for nm, st in (('pc', pc), ('cc', cc), ('dss', dss), ('ff', ff), ('erp', erp), ('pd', pd), ('fcn', fcn)):
    globals()['a3' + nm] = w.s([st], 'ad3antrrr', '( %s -> %s )' % (A3, w.lines[[l.split(':')[0] for l in w.lines].index(st)].split(' |- ( ')[1].rsplit(' )', 1)[0].split(' -> ', 1)[1]))
vc = w.s([a3dss, vd], 'sseldd', '( %s -> v e. CC )' % A3)
vpc = w.s([vc, a3pc], 'subcld', '( %s -> ( v - P ) e. CC )' % A3)
m1 = w.s([], 'oveq1', '( m = v -> ( m - P ) = ( v - P ) )')
m2 = w.s([m1], 'fveq2d', '( m = v -> ( abs ` ( m - P ) ) = ( abs ` ( v - P ) ) )')
m3 = w.s([m2], 'breq1d', '( m = v -> ( ( abs ` ( m - P ) ) < n <-> ( abs ` ( v - P ) ) < n ) )')
m4 = w.s([], 'fveq2', '( m = v -> ( F ` m ) = ( F ` v ) )')
m5 = w.s([m4], 'oveq1d', '( m = v -> ( ( F ` m ) - ( F ` P ) ) = ( ( F ` v ) - ( F ` P ) ) )')
m6 = w.s([m1], 'oveq2d', '( m = v -> ( C x. ( m - P ) ) = ( C x. ( v - P ) ) )')
m7 = w.s([m5, m6], 'oveq12d', '( m = v -> %s = %s )' % (NUM('m'), NUM('v')))
m8 = w.s([w.s([m7], 'fveq2d', '( m = v -> ( abs ` %s ) = ( abs ` %s ) )' % (NUM('m'), NUM('v'))),
          w.s([m2], 'oveq2d', '( m = v -> ( ( E / 2 ) x. ( abs ` ( m - P ) ) ) = ( ( E / 2 ) x. ( abs ` ( v - P ) ) ) )')],
         'breq12d', '( m = v -> ( ( abs ` %s ) <_ ( ( E / 2 ) x. ( abs ` ( m - P ) ) ) <-> ( abs ` %s ) <_ ( ( E / 2 ) x. ( abs ` ( v - P ) ) ) ) )' % (NUM('m'), NUM('v')))
msub = w.s([m3, m8], 'imbi12d', '( m = v -> ( %s <-> %s ) )' % (THETA('n', 'm'), THETA('n', 'v')))
thv = w.s([msub, w.s([alm], 'ad2antrr', '( %s -> A. m e. D %s )' % (A3, THETA('n', 'm'))), vd], 'rspcdva', '( %s -> %s )' % (A3, THETA('n', 'v')))
bnd = w.s([thv, ltn], 'mpd', '( %s -> ( abs ` %s ) <_ ( ( E / 2 ) x. ( abs ` ( v - P ) ) ) )' % (A3, NUM('v')))
dvp = w.s([w.s([a3pd, a3cc], 'jca', '( %s -> ( P e. D /\\ C e. CC ) )' % A3), w.inst('dsvalp')], 'syl', '( %s -> ( %s ` P ) = C )' % (A3, DSF))
# case v = P
veq = w.s([], 'simpr', '( %s -> v = P )' % A4)
d1 = w.s([veq], 'fveq2d', '( %s -> ( %s ` v ) = ( %s ` P ) )' % (A4, DSF, DSF))
dvc = w.s([w.s([dvp], 'adantr', '( %s -> ( %s ` P ) = C )' % (A4, DSF)), w.s([a3cc], 'adantr', '( %s -> C e. CC )' % A4)], 'eqeltrd',
          '( %s -> ( %s ` P ) e. CC )' % (A4, DSF))
dvvc = w.s([d1, dvc], 'eqeltrd', '( %s -> ( %s ` v ) e. CC )' % (A4, DSF))
z0 = w.s([dvvc, d1], 'subeq0bd', '( %s -> ( ( %s ` v ) - ( %s ` P ) ) = 0 )' % (A4, DSF, DSF))
ab0 = w.s([w.s([z0], 'fveq2d', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) = ( abs ` 0 ) )' % (A4, DSF, DSF)),
           closed(w, A4, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) = 0 )' % (A4, DSF, DSF))
c1 = w.s([ab0, w.s([w.s([a3erp], 'adantr', '( %s -> E e. RR+ )' % A4)], 'rpgt0d', '( %s -> 0 < E )' % A4)], 'eqbrtrd',
         '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) < E )' % (A4, DSF, DSF))
# case v =/= P
vne = w.s([], 'simpr', '( %s -> v =/= P )' % A5)
vc5 = w.s([vc], 'adantr', '( %s -> v e. CC )' % A5); pc5 = w.s([a3pc], 'adantr', '( %s -> P e. CC )' % A5)
cc5 = w.s([a3cc], 'adantr', '( %s -> C e. CC )' % A5); ff5 = w.s([a3ff], 'adantr', '( %s -> F : D --> CC )' % A5)
vd5 = w.s([vd], 'adantr', '( %s -> v e. D )' % A5); pd5 = w.s([a3pd], 'adantr', '( %s -> P e. D )' % A5)
er5 = w.s([a3erp], 'adantr', '( %s -> E e. RR+ )' % A5); fc5 = w.s([a3fcn], 'adantr', '( %s -> F e. ( D -cn-> CC ) )' % A5)
vpc5 = w.s([vc5, pc5], 'subcld', '( %s -> ( v - P ) e. CC )' % A5)
vpne = w.s([vc5, pc5, vne], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % A5)
fvc = w.s([ff5, vd5], 'ffvelcdmd', '( %s -> ( F ` v ) e. CC )' % A5)
fpc = w.s([ff5, pd5], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A5)
nc = w.s([fvc, fpc], 'subcld', '( %s -> ( ( F ` v ) - ( F ` P ) ) e. CC )' % A5)
cvp = w.s([cc5, vpc5], 'mulcld', '( %s -> ( C x. ( v - P ) ) e. CC )' % A5)
numc = w.s([nc, cvp], 'subcld', '( %s -> %s e. CC )' % (A5, NUM('v')))
dsn = w.s([w.s([w.s([fc5, pd5], 'jca', '( %s -> %s )' % (A5, FP)), w.s([vd5, vne], 'jca', '( %s -> ( v e. D /\\ v =/= P ) )' % A5)], 'jca',
                '( %s -> ( %s /\\ ( v e. D /\\ v =/= P ) ) )' % (A5, FP)), w.inst('dsvaln')], 'syl', '( %s -> ( %s ` v ) = %s )' % (A5, DSF, QUO('v')))
dif = w.s([dsn, w.s([dvp], 'adantr', '( %s -> ( %s ` P ) = C )' % (A5, DSF))], 'oveq12d',
          '( %s -> ( ( %s ` v ) - ( %s ` P ) ) = ( %s - C ) )' % (A5, DSF, DSF, QUO('v')))
ds1 = w.s([nc, cvp, w.s([vpc5, vpne], 'jca', '( %s -> ( ( v - P ) e. CC /\\ ( v - P ) =/= 0 ) )' % A5), w.inst('divsubdir')], 'syl3anc',
          '( %s -> ( %s / ( v - P ) ) = ( %s - ( ( C x. ( v - P ) ) / ( v - P ) ) ) )' % (A5, NUM('v'), QUO('v')))
ds2 = w.s([cc5, vpc5, vpne], 'divcan4d', '( %s -> ( ( C x. ( v - P ) ) / ( v - P ) ) = C )' % A5)
ds3 = w.s([ds1, w.s([ds2], 'oveq2d', '( %s -> ( %s - ( ( C x. ( v - P ) ) / ( v - P ) ) ) = ( %s - C ) )' % (A5, QUO('v'), QUO('v')))], 'eqtrd',
          '( %s -> ( %s / ( v - P ) ) = ( %s - C ) )' % (A5, NUM('v'), QUO('v')))
abq = w.s([numc, vpc5, vpne], 'absdivd', '( %s -> ( abs ` ( %s / ( v - P ) ) ) = ( ( abs ` %s ) / ( abs ` ( v - P ) ) ) )' % (A5, NUM('v'), NUM('v')))
lhs = w.s([w.s([dif, w.s([ds3], 'eqcomd', '( %s -> ( %s - C ) = ( %s / ( v - P ) ) )' % (A5, QUO('v'), NUM('v')))], 'eqtrd',
                '( %s -> ( ( %s ` v ) - ( %s ` P ) ) = ( %s / ( v - P ) ) )' % (A5, DSF, DSF, NUM('v'))), abq], 'eqtrd' if False else 'fveq2d', '') if False else None
lhs1 = w.s([dif, w.s([ds3], 'eqcomd', '( %s -> ( %s - C ) = ( %s / ( v - P ) ) )' % (A5, QUO('v'), NUM('v')))], 'eqtrd',
           '( %s -> ( ( %s ` v ) - ( %s ` P ) ) = ( %s / ( v - P ) ) )' % (A5, DSF, DSF, NUM('v')))
lhs2 = w.s([w.s([lhs1], 'fveq2d', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) = ( abs ` ( %s / ( v - P ) ) ) )' % (A5, DSF, DSF, NUM('v'))), abq],
           'eqtrd', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) = ( ( abs ` %s ) / ( abs ` ( v - P ) ) ) )' % (A5, DSF, DSF, NUM('v')))
absvpr = w.s([w.s([vpc5], 'abscld', '( %s -> ( abs ` ( v - P ) ) e. RR )' % A5),
              w.s([vpne, w.s([vpc5, w.inst('absgt0')], 'syl', '( %s -> ( ( v - P ) =/= 0 <-> 0 < ( abs ` ( v - P ) ) ) )' % A5)], 'mpbid',
                  '( %s -> 0 < ( abs ` ( v - P ) ) )' % A5)], 'elrpd', '( %s -> ( abs ` ( v - P ) ) e. RR+ )' % A5)
ehr = w.s([w.s([er5, w.inst('rphalfcl')], 'syl', '( %s -> ( E / 2 ) e. RR+ )' % A5)], 'rpred', '( %s -> ( E / 2 ) e. RR )' % A5)
absnr = w.s([numc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A5, NUM('v')))
cm = w.s([w.s([absvpr], 'rpcnd', '( %s -> ( abs ` ( v - P ) ) e. CC )' % A5), w.s([ehr], 'recnd', '( %s -> ( E / 2 ) e. CC )' % A5)], 'mulcomd',
         '( %s -> ( ( abs ` ( v - P ) ) x. ( E / 2 ) ) = ( ( E / 2 ) x. ( abs ` ( v - P ) ) )' % A5 + ' )')
bnd5 = w.s([w.s([bnd], 'adantr', '( %s -> ( abs ` %s ) <_ ( ( E / 2 ) x. ( abs ` ( v - P ) ) ) )' % (A5, NUM('v'))), cm], 'breqtrrd',
           '( %s -> ( abs ` %s ) <_ ( ( abs ` ( v - P ) ) x. ( E / 2 ) ) )' % (A5, NUM('v')))
ldm = w.s([absnr, ehr, absvpr], 'ledivmuld',
          '( %s -> ( ( ( abs ` %s ) / ( abs ` ( v - P ) ) ) <_ ( E / 2 ) <-> ( abs ` %s ) <_ ( ( abs ` ( v - P ) ) x. ( E / 2 ) ) ) )' % (A5, NUM('v'), NUM('v')))
le2 = w.s([bnd5, ldm], 'mpbird', '( %s -> ( ( abs ` %s ) / ( abs ` ( v - P ) ) ) <_ ( E / 2 ) )' % (A5, NUM('v')))
hlt = w.s([er5, w.inst('rphalflt')], 'syl', '( %s -> ( E / 2 ) < E )' % A5)
dq = w.s([absnr, absvpr], 'rerpdivcld', '( %s -> ( ( abs ` %s ) / ( abs ` ( v - P ) ) ) e. RR )' % (A5, NUM('v')))
lt5 = w.s([dq, ehr, w.s([er5], 'rpred', '( %s -> E e. RR )' % A5), le2, hlt], 'lelttrd',
          '( %s -> ( ( abs ` %s ) / ( abs ` ( v - P ) ) ) < E )' % (A5, NUM('v')))
c2 = w.s([lhs2, lt5], 'eqbrtrd', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) < E )' % (A5, DSF, DSF))
tot = w.s([c1, c2], 'pm2.61dane', '( %s -> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) < E )' % (A3, DSF, DSF))
chi = w.s([tot], 'ex', '( %s -> %s )' % (A2, CHIP('n', 'v')))
gb = w.s([chi], 'ralrimiva', '( %s -> %s )' % (A1, GOALPB('n')))
k1 = w.s([], 'breq2', '( k = n -> ( ( abs ` ( v - P ) ) < k <-> ( abs ` ( v - P ) ) < n ) )')
k2 = w.s([k1], 'imbi1d', '( k = n -> ( %s <-> %s ) )' % (CHIP('k', 'v'), CHIP('n', 'v')))
k3 = w.s([k2], 'ralbidv', '( k = n -> ( %s <-> %s ) )' % (GOALPB('k'), GOALPB('n')))
k4 = w.s([k3], 'adantl', '( ( %s /\\ k = n ) -> ( %s <-> %s ) )' % (A1, GOALPB('k'), GOALPB('n')))
exq = w.s([nrp, k4, gb], 'rspcedvd', '( %s -> %s )' % (A1, GOALP))
w.qed([exi, exq], 'rexlimddv', '( %s -> %s )' % (A0, GOALP)); run(w)

def GX(X):
    return 'E. k e. RR+ A. v e. D ( ( abs ` ( v - %s ) ) < k -> ( abs ` ( ( %s ` v ) - ( %s ` %s ) ) ) < e )' % (X, DSF, DSF, X)
def GXB(x, X):
    return 'A. v e. D ( ( abs ` ( v - %s ) ) < %s -> ( abs ` ( ( %s ` v ) - ( %s ` %s ) ) ) < e )' % (X, x, DSF, DSF, X)
def GXI(x, X):
    return '( ( abs ` ( v - %s ) ) < %s -> ( abs ` ( ( %s ` v ) - ( %s ` %s ) ) ) < e )' % (X, x, DSF, DSF, X)

# ---- dscn: the extended difference quotient is continuous on the whole domain
w = W('dscn', 'The extended difference quotient of a continuous function differentiable at the base point is continuous on the domain.')
A0 = HOL
A1 = '( %s /\\ ( s e. D /\\ e e. RR+ ) )' % A0
A2 = '( %s /\\ s = P )' % A1
A3 = '( %s /\\ s =/= P )' % A1
fcn = w.s([], 'simp1', '( %s -> F e. ( D -cn-> CC ) )' % A0)
pdm = w.s([], 'simp2', '( %s -> P e. dom ( CC _D F ) )' % A0)
ceq = w.s([], 'simp3', '( %s -> C = ( ( CC _D F ) ` P ) )' % A0)
dss = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
ccs = closed(w, A0, 'ssid', 'CC C_ CC')
pd = w.s([w.s([ccs, ff, dss], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0), pdm], 'sseldd', '( %s -> P e. D )' % A0)
cc = w.s([ceq, w.s([closed(w, A0, 'dvfcn', '( CC _D F ) : dom ( CC _D F ) --> CC'), pdm], 'ffvelcdmd',
                   '( %s -> ( ( CC _D F ) ` P ) e. CC )' % A0)], 'eqeltrd', '( %s -> C e. CC )' % A0)
fpc = w.s([fcn, pd, cc], '3jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D /\\ C e. CC ) )' % A0)
dsfn = w.s([fpc, w.inst('dsf')], 'syl', '( %s -> %s : D --> CC )' % (A0, DSF))
sd = w.s([w.s([], 'simpr', '( %s -> ( s e. D /\\ e e. RR+ ) )' % A1), w.inst('simpl')], 'syl', '( %s -> s e. D )' % A1)
erp = w.s([w.s([], 'simpr', '( %s -> ( s e. D /\\ e e. RR+ ) )' % A1), w.inst('simpr')], 'syl', '( %s -> e e. RR+ )' % A1)
# case s = P
seq = w.s([], 'simpr', '( %s -> s = P )' % A2)
g1 = w.s([], 'oveq2', '( s = P -> ( v - s ) = ( v - P ) )')
g2 = w.s([g1], 'fveq2d', '( s = P -> ( abs ` ( v - s ) ) = ( abs ` ( v - P ) ) )')
g3 = w.s([g2], 'breq1d', '( s = P -> ( ( abs ` ( v - s ) ) < k <-> ( abs ` ( v - P ) ) < k ) )')
g4 = w.s([], 'fveq2', '( s = P -> ( %s ` s ) = ( %s ` P ) )' % (DSF, DSF))
g5 = w.s([g4], 'oveq2d', '( s = P -> ( ( %s ` v ) - ( %s ` s ) ) = ( ( %s ` v ) - ( %s ` P ) ) )' % (DSF, DSF, DSF, DSF))
g6 = w.s([w.s([g5], 'fveq2d', '( s = P -> ( abs ` ( ( %s ` v ) - ( %s ` s ) ) ) = ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) )' % (DSF, DSF, DSF, DSF))],
         'breq1d', '( s = P -> ( ( abs ` ( ( %s ` v ) - ( %s ` s ) ) ) < e <-> ( abs ` ( ( %s ` v ) - ( %s ` P ) ) ) < e ) )' % (DSF, DSF, DSF, DSF))
g7 = w.s([g3, g6], 'imbi12d', '( s = P -> ( %s <-> %s ) )' % (GXI('k', 's'), GXI('k', 'P')))
g8 = w.s([g7], 'ralbidv', '( s = P -> ( %s <-> %s ) )' % (GXB('k', 's'), GXB('k', 'P')))
g9 = w.s([g8], 'rexbidv', '( s = P -> ( %s <-> %s ) )' % (GX('s'), GX('P')))
qq = w.s([w.s([w.s([fcn, pdm, ceq], '3jca', '( %s -> %s )' % (A0, HOL)), w.inst('id')], 'syl' if False else 'syl', '( %s -> %s )' % (A0, HOL)) if False else
          w.s([w.s([fcn, pdm, ceq], '3jca', '( %s -> %s )' % (A0, HOL))], 'adantr', '( %s -> %s )' % (A1, HOL)), erp], 'jca',
         '( %s -> ( %s /\\ e e. RR+ ) )' % (A1, HOL))
dq = w.s([w.s([qq], 'adantr', '( %s -> ( %s /\\ e e. RR+ ) )' % (A2, HOL)), w.inst('dscnq')], 'syl', '( %s -> %s )' % (A2, GX('P')))
c1 = w.s([dq, w.s([seq, w.s([g9], 'a1i', '( %s -> ( s = P -> ( %s <-> %s ) ) )' % (A2, GX('s'), GX('P')))], 'mpd',
                  '( %s -> ( %s <-> %s ) )' % (A2, GX('s'), GX('P')))], 'mpbird', '( %s -> %s )' % (A2, GX('s')))
# case s =/= P
c2 = w.s([w.s([w.s([fpc], 'ad2antrr' if False else 'adantr', '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D /\\ C e. CC ) )' % A1)], 'adantr',
              '( %s -> ( F e. ( D -cn-> CC ) /\\ P e. D /\\ C e. CC ) )' % A3),
          w.s([w.s([sd], 'adantr', '( %s -> s e. D )' % A3), w.s([], 'simpr', '( %s -> s =/= P )' % A3),
               w.s([erp], 'adantr', '( %s -> e e. RR+ )' % A3)], '3jca', '( %s -> ( s e. D /\\ s =/= P /\\ e e. RR+ ) )' % A3),
          w.inst('dscnp')], 'syl2anc', '( %s -> %s )' % (A3, GX('s')))
tot = w.s([c1, c2], 'pm2.61dane', '( %s -> %s )' % (A1, GX('s')))
rl = w.s([tot], 'ralrimivva', '( %s -> A. s e. D A. e e. RR+ %s )' % (A0, GX('s')))
el = w.s([dss, ccs, w.inst('elcncf2')], 'syl2anc',
         '( %s -> ( %s e. ( D -cn-> CC ) <-> ( %s : D --> CC /\\ A. s e. D A. e e. RR+ %s ) ) )' % (A0, DSF, DSF, GX('s')))
w.qed([dsfn, rl, el], 'mpbir2and', '( %s -> %s e. ( D -cn-> CC ) )' % (A0, DSF)); run(w)
