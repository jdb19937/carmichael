"""C4, Perron block 1: the integrand ` ( U ^c z ) / z ` and its holomorphy."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

CXE = '( z e. E |-> ( U ^c z ) )'
CXC = '( z e. CC |-> ( U ^c z ) )'
PKE = '( z e. E |-> ( ( U ^c z ) / z ) )'
PK0 = '( z e. ( CC \\ { 0 } ) |-> ( ( U ^c z ) / z ) )'

# ---------------------------------------------------------------- cxfcn
A0 = '( U e. RR+ /\\ E C_ CC )'
w = W('cxfcn', 'The exponential map ` z |-> ( U ^c z ) ` of a positive real base is '
      'continuous on any set of complex numbers: it is ` exp ` composed with a '
      'linear map ( ~ cxpef ).')
urp = w.s([], 'simpl', '( %s -> U e. RR+ )' % A0)
ess = w.s([], 'simpr', '( %s -> E C_ CC )' % A0)
lu = w.s([urp, w.inst('relogcl')], 'syl', '( %s -> ( log ` U ) e. RR )' % A0)
luc = w.s([lu], 'recnd', '( %s -> ( log ` U ) e. CC )' % A0)
idc = w.s([ess, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), w.inst('cncfmptid')],
          'syl2anc', '( %s -> ( z e. E |-> z ) e. ( E -cn-> CC ) )' % A0)
cst = w.s([luc, ess, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), w.inst('cncfmptc')],
          'syl3anc', '( %s -> ( z e. E |-> ( log ` U ) ) e. ( E -cn-> CC ) )' % A0)
lin = w.s([idc, cst], 'mulcncf', '( %s -> ( z e. E |-> ( z x. ( log ` U ) ) ) e. ( E -cn-> CC ) )' % A0)
ef = w.s([w.s([], 'efcn', 'exp e. ( CC -cn-> CC )')], 'a1i', '( %s -> exp e. ( CC -cn-> CC ) )' % A0)
cmp = w.s([ef, lin], 'cncfmpt1f', '( %s -> ( z e. E |-> ( exp ` ( z x. ( log ` U ) ) ) ) e. ( E -cn-> CC ) )' % A0)
AZ = '( %s /\\ z e. E )' % A0
zc = w.s([w.s([ess], 'adantr', '( %s -> E C_ CC )' % AZ), w.s([], 'simpr', '( %s -> z e. E )' % AZ)],
         'sseldd', '( %s -> z e. CC )' % AZ)
uc = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ)], 'rpcnd', '( %s -> U e. CC )' % AZ)], 'id',
         '( %s -> U e. CC )' % AZ)
w.lines.pop()
uc = w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ)], 'rpcnd', '( %s -> U e. CC )' % AZ)
une = w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ)], 'rpne0d', '( %s -> U =/= 0 )' % AZ)
val = w.s([uc, une, zc, w.inst('cxpef')], 'syl3anc', '( %s -> ( U ^c z ) = ( exp ` ( z x. ( log ` U ) ) ) )' % AZ)
eqm = w.s([w.s([val], 'eqcomd', '( %s -> ( exp ` ( z x. ( log ` U ) ) ) = ( U ^c z ) )' % AZ)], 'mpteq2dva',
          '( %s -> ( z e. E |-> ( exp ` ( z x. ( log ` U ) ) ) ) = %s )' % (A0, CXE))
w.qed([eqm, cmp], 'eqeltrrd', '( %s -> %s e. ( E -cn-> CC ) )' % (A0, CXE))
run4(w)

# ---------------------------------------------------------------- cxfhol
w = W('cxfhol', 'The exponential map ` z |-> ( U ^c z ) ` of a positive real base is '
      'holomorphic on the whole plane ( ~ dvcxp2 ).')
A1 = 'U e. RR+'
urp = w.s([], 'id', '( %s -> U e. RR+ )' % A1)
cn = w.s([w.s([urp, w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A1)], 'jca',
               '( %s -> ( U e. RR+ /\\ CC C_ CC ) )' % A1), w.inst('cxfcn')], 'syl',
         '( %s -> %s e. ( CC -cn-> CC ) )' % (A1, CXC))
dv = w.s([urp, w.inst('dvcxp2')], 'syl',
         '( %s -> ( CC _D %s ) = ( z e. CC |-> ( ( log ` U ) x. ( U ^c z ) ) ) )' % (A1, CXC))
AZ2 = '( %s /\\ z e. CC )' % A1
luc = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ2), w.inst('relogcl')], 'syl',
               '( %s -> ( log ` U ) e. RR )' % AZ2)], 'recnd', '( %s -> ( log ` U ) e. CC )' % AZ2)
uc2 = w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ2)], 'rpcnd', '( %s -> U e. CC )' % AZ2)
cxc = w.s([uc2, w.s([], 'simpr', '( %s -> z e. CC )' % AZ2)], 'cxpcld', '( %s -> ( U ^c z ) e. CC )' % AZ2)
cls = w.s([luc, cxc], 'mulcld', '( %s -> ( ( log ` U ) x. ( U ^c z ) ) e. CC )' % AZ2)
dom = dvdom(w, A1, CXC, 'z', 'CC', '( ( log ` U ) x. ( U ^c z ) )', dv, cls)
w.qed([cn, dom], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) ) )' % (A1, CXC, CXC))
run4(w)

# ---------------------------------------------------------------- pkfcn
A2 = '( U e. RR+ /\\ E C_ ( CC \\ { 0 } ) )'
w = W('pkfcn', 'The Perron integrand ` z |-> ( ( U ^c z ) / z ) ` is continuous off '
      'the origin.')
urp = w.s([], 'simpl', '( %s -> U e. RR+ )' % A2)
ess = w.s([], 'simpr', '( %s -> E C_ ( CC \\ { 0 } ) )' % A2)
ecc = w.s([ess, w.s([w.s([], 'difss', '( CC \\ { 0 } ) C_ CC')], 'a1i', '( %s -> ( CC \\ { 0 } ) C_ CC )' % A2)],
          'sstrd', '( %s -> E C_ CC )' % A2)
cx = w.s([w.s([urp, ecc], 'jca', '( %s -> ( U e. RR+ /\\ E C_ CC ) )' % A2), w.inst('cxfcn')], 'syl',
         '( %s -> %s e. ( E -cn-> CC ) )' % (A2, CXE))
z0 = w.s([w.s([w.s([], '0cn', '0 e. CC')], 'a1i', '( %s -> 0 e. CC )' % A2), ess, w.inst('rinvcnss')],
         'syl2anc', '( %s -> ( z e. E |-> ( 1 / ( z - 0 ) ) ) e. ( E -cn-> CC ) )' % A2)
AZ3 = '( %s /\\ z e. E )' % A2
zcc = w.s([w.s([ecc], 'adantr', '( %s -> E C_ CC )' % AZ3), w.s([], 'simpr', '( %s -> z e. E )' % AZ3)],
          'sseldd', '( %s -> z e. CC )' % AZ3)
s1 = w.s([zcc], 'subid1d', '( %s -> ( z - 0 ) = z )' % AZ3)
inv = w.s([w.s([s1], 'oveq2d', '( %s -> ( 1 / ( z - 0 ) ) = ( 1 / z ) )' % AZ3)], 'mpteq2dva',
          '( %s -> ( z e. E |-> ( 1 / ( z - 0 ) ) ) = ( z e. E |-> ( 1 / z ) ) )' % A2)
inv2 = w.s([inv, z0], 'eqeltrrd', '( %s -> ( z e. E |-> ( 1 / z ) ) e. ( E -cn-> CC ) )' % A2)
prod = w.s([cx, inv2], 'mulcncf', '( %s -> ( z e. E |-> ( ( U ^c z ) x. ( 1 / z ) ) ) e. ( E -cn-> CC ) )' % A2)
zne = w.s([w.s([ess], 'adantr', '( %s -> E C_ ( CC \\ { 0 } ) )' % AZ3),
           w.s([], 'simpr', '( %s -> z e. E )' % AZ3)], 'sseldd', '( %s -> z e. ( CC \\ { 0 } ) )' % AZ3)
zne0 = w.s([zne, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= 0 ) )' % AZ3)
zn2 = w.s([zne0, w.inst('simpr')], 'syl', '( %s -> z =/= 0 )' % AZ3)
cxz = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ3)], 'rpcnd', '( %s -> U e. CC )' % AZ3), zcc],
          'cxpcld', '( %s -> ( U ^c z ) e. CC )' % AZ3)
dvr = w.s([cxz, zcc, zn2], 'divrecd', '( %s -> ( ( U ^c z ) / z ) = ( ( U ^c z ) x. ( 1 / z ) ) )' % AZ3)
eqm2 = w.s([dvr], 'mpteq2dva', '( %s -> %s = ( z e. E |-> ( ( U ^c z ) x. ( 1 / z ) ) ) )' % (A2, PKE))
w.qed([eqm2, prod], 'eqeltrd', '( %s -> %s e. ( E -cn-> CC ) )' % (A2, PKE))
run4(w)
