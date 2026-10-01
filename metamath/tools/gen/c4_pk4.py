"""C4, Perron block 4: the holomorphy of the integrand off the origin."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

DOM = '( CC \\ { 0 } )'
PK0 = PKF('U')
CXC = '( z e. CC |-> ( U ^c z ) )'
CXD = '( z e. %s |-> ( U ^c z ) )' % DOM
IDD = '( z e. %s |-> z )' % DOM
TOP = '( TopOpen ` CCfld )'
DRV = '( ( ( ( ( log ` U ) x. ( U ^c z ) ) x. z ) - ( 1 x. ( U ^c z ) ) ) / ( z ^ 2 ) )'

A0 = 'U e. RR+'
w = W('pkfhol', 'The Perron integrand ` ( U ^c z ) / z ` is holomorphic on the plane '
      'minus the origin ( ~ dvmptdiv , ~ dvcxp2 ).')
urp = w.s([], 'id', '( %s -> U e. RR+ )' % A0)
cn = w.s([w.s([urp, w.s([w.s([], 'ssid', '%s C_ %s' % (DOM, DOM))], 'a1i', '( %s -> %s C_ %s )' % (A0, DOM, DOM))], 'jca',
               '( %s -> ( U e. RR+ /\\ %s C_ %s ) )' % (A0, DOM, DOM)), w.inst('pkfcn')], 'syl',
         '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, PK0, DOM))
sc = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
jk = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
opn = w.s([w.s([w.s([], '0cn', '0 e. CC')], 'a1i', '( %s -> 0 e. CC )' % A0), w.inst('cnopnsn')], 'syl',
          '( %s -> %s e. %s )' % (A0, DOM, TOP))
ss = w.s([w.s([], 'difss', '%s C_ CC' % DOM)], 'a1i', '( %s -> %s C_ CC )' % (A0, DOM))
# the numerator derivative on the punctured plane
AZ = '( %s /\\ z e. CC )' % A0
luc = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ), w.inst('relogcl')], 'syl',
               '( %s -> ( log ` U ) e. RR )' % AZ)], 'recnd', '( %s -> ( log ` U ) e. CC )' % AZ)
cxz = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ)], 'rpcnd', '( %s -> U e. CC )' % AZ),
           w.s([], 'simpr', '( %s -> z e. CC )' % AZ)], 'cxpcld', '( %s -> ( U ^c z ) e. CC )' % AZ)
prd = w.s([luc, cxz], 'mulcld', '( %s -> ( ( log ` U ) x. ( U ^c z ) ) e. CC )' % AZ)
dvc = w.s([urp, w.inst('dvcxp2')], 'syl',
          '( %s -> ( CC _D %s ) = ( z e. CC |-> ( ( log ` U ) x. ( U ^c z ) ) ) )' % (A0, CXC))
dvd = w.s([sc, cxz, prd, dvc, ss, jk, keq, opn], 'dvmptres',
          '( %s -> ( CC _D %s ) = ( z e. %s |-> ( ( log ` U ) x. ( U ^c z ) ) ) )' % (A0, CXD, DOM))
# the identity derivative on the punctured plane
one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % AZ)
dvi = w.s([sc], 'dvmptid', '( %s -> ( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 ) )' % A0)
dvi2 = w.s([sc, w.s([], 'simpr', '( %s -> z e. CC )' % AZ), one, dvi, ss, jk, keq, opn], 'dvmptres',
           '( %s -> ( CC _D %s ) = ( z e. %s |-> 1 ) )' % (A0, IDD, DOM))
# the quotient rule
AD = '( %s /\\ z e. %s )' % (A0, DOM)
zd = w.s([], 'simpr', '( %s -> z e. %s )' % (AD, DOM))
zc = w.s([zd, w.inst('eldifi')], 'syl', '( %s -> z e. CC )' % AD)
cxd = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AD)], 'rpcnd', '( %s -> U e. CC )' % AD), zc],
          'cxpcld', '( %s -> ( U ^c z ) e. CC )' % AD)
lud = w.s([w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AD), w.inst('relogcl')], 'syl',
                    '( %s -> ( log ` U ) e. RR )' % AD)], 'recnd', '( %s -> ( log ` U ) e. CC )' % AD), cxd],
          'mulcld', '( %s -> ( ( log ` U ) x. ( U ^c z ) ) e. CC )' % AD)
oned = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % AD)
dq = w.s([sc, cxd, lud, dvd, zd, oned, dvi2], 'dvmptdiv',
         '( %s -> ( CC _D %s ) = ( z e. %s |-> %s ) )' % (A0, PK0, DOM, DRV))
zne = w.s([w.s([zd, w.inst('eldifsn')], 'sylib', '( %s -> ( z e. CC /\\ z =/= 0 ) )' % AD), w.inst('simpr')], 'syl',
          '( %s -> z =/= 0 )' % AD)
cls = w.s([w.s([w.s([lud, zc], 'mulcld', '( %s -> ( ( ( log ` U ) x. ( U ^c z ) ) x. z ) e. CC )' % AD),
                w.s([oned, cxd], 'mulcld', '( %s -> ( 1 x. ( U ^c z ) ) e. CC )' % AD)], 'subcld',
               '( %s -> ( ( ( ( log ` U ) x. ( U ^c z ) ) x. z ) - ( 1 x. ( U ^c z ) ) ) e. CC )' % AD),
           w.s([zc, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % AD)], 'expcld',
               '( %s -> ( z ^ 2 ) e. CC )' % AD),
           w.s([zc, zne, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % AD)], 'expne0d',
               '( %s -> ( z ^ 2 ) =/= 0 )' % AD)], 'divcld', '( %s -> %s e. CC )' % (AD, DRV))
dm = dvdom(w, A0, PK0, 'z', DOM, DRV, dq, cls)
w.qed([cn, dm], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, PK0, DOM, DOM, PK0))
run4(w)
