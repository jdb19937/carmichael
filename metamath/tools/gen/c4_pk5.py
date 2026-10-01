"""C4, Perron block 5: the two rectangle identities for the Perron integrand."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

DOM = '( CC \\ { 0 } )'
PK0 = PKF('U')
CXC = '( z e. CC |-> ( U ^c z ) )'
GEO = '( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) )'
AB = '( A e. CC /\\ B e. CC )'

# ---------------------------------------------------------------- crectne0
A0 = '( %s /\\ 0 < ( Re ` A ) )' % AB
w = W('crectne0', 'A closed rectangle in the open right half-plane misses the origin.')
ac = w.s([], 'simpll', '( %s -> A e. CC )' % A0)
bc = w.s([], 'simplr', '( %s -> B e. CC )' % A0)
ra0 = w.s([], 'simpr', '( %s -> 0 < ( Re ` A ) )' % A0)
AU = '( %s /\\ a e. ( A crect B ) )' % A0
am = w.s([], 'simpr', '( %s -> a e. ( A crect B ) )' % AU)
el = w.s([w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % AU), w.s([bc], 'adantr', '( %s -> B e. CC )' % AU)],
               'jca', '( %s -> %s )' % (AU, AB)), w.inst('elcrect')], 'syl',
         '( %s -> ( a e. ( A crect B ) <-> ( a e. CC /\\ ( Re ` a ) e. ( ( Re ` A ) [,] ( Re ` B ) ) /\\ ( Im ` a ) e. ( ( Im ` A ) [,] ( Im ` B ) ) ) ) )' % AU)
tr = w.s([am, el], 'mpbid', '( %s -> ( a e. CC /\\ ( Re ` a ) e. ( ( Re ` A ) [,] ( Re ` B ) ) /\\ ( Im ` a ) e. ( ( Im ` A ) [,] ( Im ` B ) ) ) )' % AU)
acc = w.s([tr, w.inst('simp1')], 'syl', '( %s -> a e. CC )' % AU)
ricc = w.s([tr, w.inst('simp2')], 'syl', '( %s -> ( Re ` a ) e. ( ( Re ` A ) [,] ( Re ` B ) ) )' % AU)
rar = w.s([w.s([ac], 'adantr', '( %s -> A e. CC )' % AU)], 'recld', '( %s -> ( Re ` A ) e. RR )' % AU)
rbr = w.s([w.s([bc], 'adantr', '( %s -> B e. CC )' % AU)], 'recld', '( %s -> ( Re ` B ) e. RR )' % AU)
e2 = w.s([rar, rbr, w.inst('elicc2')], 'syl2anc',
         '( %s -> ( ( Re ` a ) e. ( ( Re ` A ) [,] ( Re ` B ) ) <-> ( ( Re ` a ) e. RR /\\ ( Re ` A ) <_ ( Re ` a ) /\\ ( Re ` a ) <_ ( Re ` B ) ) ) )' % AU)
tr2 = w.s([ricc, e2], 'mpbid', '( %s -> ( ( Re ` a ) e. RR /\\ ( Re ` A ) <_ ( Re ` a ) /\\ ( Re ` a ) <_ ( Re ` B ) ) )' % AU)
rer = w.s([tr2, w.inst('simp1')], 'syl', '( %s -> ( Re ` a ) e. RR )' % AU)
rge = w.s([tr2, w.inst('simp2')], 'syl', '( %s -> ( Re ` A ) <_ ( Re ` a ) )' % AU)
r0 = w.s([w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % AU), rar, rer,
          w.s([ra0], 'adantr', '( %s -> 0 < ( Re ` A ) )' % AU), rge], 'ltletrd', '( %s -> 0 < ( Re ` a ) )' % AU)
AZ = '( %s /\\ a = 0 )' % AU
q1 = w.s([w.s([w.s([], 'simpr', '( %s -> a = 0 )' % AZ)], 'fveq2d', '( %s -> ( Re ` a ) = ( Re ` 0 ) )' % AZ),
          w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % AZ)], 'eqtrd',
         '( %s -> ( Re ` a ) = 0 )' % AZ)
q2 = w.s([w.s([r0], 'adantr', '( %s -> 0 < ( Re ` a ) )' % AZ), q1], 'breqtrd', '( %s -> 0 < 0 )' % AZ)
q3 = w.s([w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('ltnr')], 'ax-mp', '-. 0 < 0')], 'a1i', '( %s -> -. 0 < 0 )' % AZ)],
         'id', '( %s -> -. 0 < 0 )' % AZ)
w.lines.pop()
q3 = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('ltnr')], 'ax-mp', '-. 0 < 0')], 'a1i', '( %s -> -. 0 < 0 )' % AZ)
ane = w.s([w.s([q2, q3], 'pm2.65da', '( %s -> -. a = 0 )' % AU)], 'neqned', '( %s -> a =/= 0 )' % AU)
mem = w.s([acc, ane, w.inst('eldifsn')], 'sylanbrc', '( %s -> a e. %s )' % (AU, DOM))
w.qed([w.s([mem], 'ralrimiva', '( %s -> A. a e. ( A crect B ) a e. %s )' % (A0, DOM)),
       w.s([w.s([], 'dfss3', '( ( A crect B ) C_ %s <-> A. a e. ( A crect B ) a e. %s )' % (DOM, DOM))], 'a1i',
           '( %s -> ( ( A crect B ) C_ %s <-> A. a e. ( A crect B ) a e. %s ) )' % (A0, DOM, DOM))],
      'mpbird', '( %s -> ( A crect B ) C_ %s )' % (A0, DOM))
run4(w)

# ---------------------------------------------------------------- pkrecid0
A1 = '( ( U e. RR+ /\\ %s ) /\\ ( %s /\\ 0 < ( Re ` A ) ) )' % (AB, GEO)
w = W('pkrecid0', 'The boundary integral of the Perron integrand around a rectangle in '
      'the open right half-plane vanishes: Cauchy-Goursat ( ~ rectintgour ) applies '
      'because the integrand is holomorphic off the origin ( ~ pkfhol ) and the '
      'rectangle misses it ( ~ crectne0 ).')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A1)
abp = w.s([], 'simplr', '( %s -> %s )' % (A1, AB))
geo = w.s([], 'simprl', '( %s -> %s )' % (A1, GEO))
ra0 = w.s([], 'simprr', '( %s -> 0 < ( Re ` A ) )' % A1)
hol = w.s([urp, w.inst('pkfhol')], 'syl',
          '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (A1, PK0, DOM, DOM, PK0))
ss = w.s([w.s([abp, ra0], 'jca', '( %s -> ( %s /\\ 0 < ( Re ` A ) ) )' % (A1, AB)), w.inst('crectne0')], 'syl',
         '( %s -> ( A crect B ) C_ %s )' % (A1, DOM))
holo = w.s([hol, ss, w.inst('holcrect')], 'syl2anc',
           '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) ) )' % (A1, PK0, DOM, PK0))
w.qed([abp, geo, holo, w.inst('rectintgour')], 'syl3anc',
      '( %s -> ( %s rectint <. A , B >. ) = 0 )' % (A1, PK0))
run4(w)

# ---------------------------------------------------------------- pkrecid
TPIC = '( 2 x. ( _i x. _pi ) )'
INT0 = '( ( ( Re ` A ) < 0 /\\ 0 < ( Re ` B ) ) /\\ ( ( Im ` A ) < 0 /\\ 0 < ( Im ` B ) ) )'
INTR = '( ( ( Re ` A ) < ( Re ` 0 ) /\\ ( Re ` 0 ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` 0 ) /\\ ( Im ` 0 ) < ( Im ` B ) ) )'
G1 = '( a e. ( ( A crect B ) \\ { 0 } ) |-> ( ( %s ` a ) / ( a - 0 ) ) )' % CXC
A2 = '( U e. RR+ /\\ %s /\\ %s )' % (AB, INT0)
w = W('pkrecid', 'Perron\'s contour with the pole inside: the boundary integral of '
      '` ( U ^c z ) / z ` around a rectangle whose interior contains the origin is '
      '` 2 _i _pi `.  Cauchy\'s integral formula ~ rectintcau at ` P = 0 ` with the '
      'entire numerator ` ( U ^c z ) ` ( ~ cxfhol ), whose value at ` 0 ` is ` 1 `.')
urp = w.s([], 'simp1', '( %s -> U e. RR+ )' % A2)
abp = w.s([], 'simp2', '( %s -> %s )' % (A2, AB))
ints = w.s([], 'simp3', '( %s -> %s )' % (A2, INT0))
ac = w.s([abp, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A2)
bc = w.s([abp, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A2)
re0 = w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % A2)
im0 = w.s([w.s([], 'im0', '( Im ` 0 ) = 0')], 'a1i', '( %s -> ( Im ` 0 ) = 0 )' % A2)
# the interiority in the ( Re ` 0 ) form
i1 = w.s([ints, w.inst('simpll')], 'syl', '( %s -> ( Re ` A ) < 0 )' % A2)
i2 = w.s([ints, w.inst('simplr')], 'syl', '( %s -> 0 < ( Re ` B ) )' % A2)
i3 = w.s([ints, w.inst('simprl')], 'syl', '( %s -> ( Im ` A ) < 0 )' % A2)
i4 = w.s([ints, w.inst('simprr')], 'syl', '( %s -> 0 < ( Im ` B ) )' % A2)
j1 = w.s([i1, w.s([re0], 'eqcomd', '( %s -> 0 = ( Re ` 0 ) )' % A2)], 'breqtrd', '( %s -> ( Re ` A ) < ( Re ` 0 ) )' % A2)
j2 = w.s([re0, i2], 'eqbrtrd', '( %s -> ( Re ` 0 ) < ( Re ` B ) )' % A2)
j3 = w.s([i3, w.s([im0], 'eqcomd', '( %s -> 0 = ( Im ` 0 ) )' % A2)], 'breqtrd', '( %s -> ( Im ` A ) < ( Im ` 0 ) )' % A2)
j4 = w.s([im0, i4], 'eqbrtrd', '( %s -> ( Im ` 0 ) < ( Im ` B ) )' % A2)
pint = w.s([w.s([w.s([], '0cn', '0 e. CC')], 'a1i', '( %s -> 0 e. CC )' % A2),
            w.s([w.s([j1, j2], 'jca', '( %s -> ( ( Re ` A ) < ( Re ` 0 ) /\\ ( Re ` 0 ) < ( Re ` B ) ) )' % A2),
                 w.s([j3, j4], 'jca', '( %s -> ( ( Im ` A ) < ( Im ` 0 ) /\\ ( Im ` 0 ) < ( Im ` B ) ) )' % A2)],
                'jca', '( %s -> %s )' % (A2, INTR))], 'jca', '( %s -> ( 0 e. CC /\\ %s ) )' % (A2, INTR))
# the numerator is entire
hol = w.s([urp, w.inst('cxfhol')], 'syl',
          '( %s -> ( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) ) )' % (A2, CXC, CXC))
rss = w.s([ac, bc, w.inst('crectss')], 'syl2anc', '( %s -> ( A crect B ) C_ CC )' % A2)
holo = w.s([hol, rss, w.inst('holcrect')], 'syl2anc',
           '( %s -> ( %s e. ( CC -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D %s ) ) )' % (A2, CXC, CXC))
cau = w.s([abp, pint, holo, w.inst('rectintcau')], 'syl3anc',
          '( %s -> ( %s rectint <. A , B >. ) = ( %s x. ( %s ` 0 ) ) )' % (A2, G1, TPIC, CXC))
# ( CXC ` 0 ) = 1
v0 = w.s([w.s([w.s([], '0cn', '0 e. CC')], 'a1i', '( %s -> 0 e. CC )' % A2),
          w.s([w.s([], 'ovex', '( U ^c 0 ) e. _V')], 'a1i', '( %s -> ( U ^c 0 ) e. _V )' % A2),
          w.s([w.s([], 'oveq2', '( z = 0 -> ( U ^c z ) = ( U ^c 0 ) )'), w.s([], 'eqid', '%s = %s' % (CXC, CXC))],
              'fvmptg', '( ( 0 e. CC /\\ ( U ^c 0 ) e. _V ) -> ( %s ` 0 ) = ( U ^c 0 ) )' % CXC)], 'syl2anc',
         '( %s -> ( %s ` 0 ) = ( U ^c 0 ) )' % (A2, CXC))
v1 = w.s([v0, w.s([w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A2), w.inst('cxp0')], 'syl',
                  '( %s -> ( U ^c 0 ) = 1 )' % A2)], 'eqtrd', '( %s -> ( %s ` 0 ) = 1 )' % (A2, CXC))
tpic = w.s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A2),
            w.s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A2),
                 w.s([w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A2)], 'recnd',
                     '( %s -> _pi e. CC )' % A2)], 'mulcld', '( %s -> ( _i x. _pi ) e. CC )' % A2)], 'mulcld',
           '( %s -> %s e. CC )' % (A2, TPIC))
rhs = w.s([w.s([v1], 'oveq2d', '( %s -> ( %s x. ( %s ` 0 ) ) = ( %s x. 1 ) )' % (A2, TPIC, CXC, TPIC)),
           w.s([tpic], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A2, TPIC, TPIC))], 'eqtrd',
          '( %s -> ( %s x. ( %s ` 0 ) ) = %s )' % (A2, TPIC, CXC, TPIC))
# replace the integrand by the Perron integrand
AUP = '( %s /\\ u e. ( ( A crect B ) \\ { 0 } ) )' % A2
um = w.s([], 'simpr', '( %s -> u e. ( ( A crect B ) \\ { 0 } ) )' % AUP)
ur = w.s([w.s([rss], 'adantr', '( %s -> ( A crect B ) C_ CC )' % AUP),
          w.s([um, w.inst('eldifi')], 'syl', '( %s -> u e. ( A crect B ) )' % AUP)], 'sseldd',
         '( %s -> u e. CC )' % AUP)
une = w.s([w.s([um, w.inst('eldifsni')], 'syl', '( %s -> u =/= 0 )' % AUP)], 'id', '( %s -> u =/= 0 )' % AUP)
w.lines.pop()
une = w.s([um, w.inst('eldifsni')], 'syl', '( %s -> u =/= 0 )' % AUP)
ud = w.s([ur, une, w.inst('eldifsn')], 'sylanbrc', '( %s -> u e. %s )' % (AUP, DOM))
g1v = w.s([um, w.s([w.s([], 'ovex', '( ( %s ` u ) / ( u - 0 ) ) e. _V' % CXC)], 'a1i',
                   '( %s -> ( ( %s ` u ) / ( u - 0 ) ) e. _V )' % (AUP, CXC)),
           w.s([w.s([w.s([], 'fveq2', '( a = u -> ( %s ` a ) = ( %s ` u ) )' % (CXC, CXC)),
                     w.s([], 'oveq1', '( a = u -> ( a - 0 ) = ( u - 0 ) )')], 'oveq12d',
                    '( a = u -> ( ( %s ` a ) / ( a - 0 ) ) = ( ( %s ` u ) / ( u - 0 ) ) )' % (CXC, CXC)),
                w.s([], 'eqid', '%s = %s' % (G1, G1))], 'fvmptg',
               '( ( u e. ( ( A crect B ) \\ { 0 } ) /\\ ( ( %s ` u ) / ( u - 0 ) ) e. _V ) -> ( %s ` u ) = ( ( %s ` u ) / ( u - 0 ) ) )' % (CXC, G1, CXC))],
          'syl2anc', '( %s -> ( %s ` u ) = ( ( %s ` u ) / ( u - 0 ) ) )' % (AUP, G1, CXC))
cxu = w.s([ur, w.s([w.s([], 'ovex', '( U ^c u ) e. _V')], 'a1i', '( %s -> ( U ^c u ) e. _V )' % AUP),
           w.s([w.s([], 'oveq2', '( z = u -> ( U ^c z ) = ( U ^c u ) )'), w.s([], 'eqid', '%s = %s' % (CXC, CXC))],
               'fvmptg', '( ( u e. CC /\\ ( U ^c u ) e. _V ) -> ( %s ` u ) = ( U ^c u ) )' % CXC)], 'syl2anc',
          '( %s -> ( %s ` u ) = ( U ^c u ) )' % (AUP, CXC))
usub = w.s([ur], 'subid1d', '( %s -> ( u - 0 ) = u )' % AUP)
pkv = w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AUP), ud], 'jca',
          '( %s -> ( U e. RR+ /\\ u e. %s ) )' % (AUP, DOM))
pkvv = w.s([pkv, w.inst('pkfval')], 'syl', '( %s -> ( %s ` u ) = ( ( U ^c u ) / u ) )' % (AUP, PK0))
w.lines.pop()
sub2 = w.s([w.s([], 'oveq2', '( z = u -> ( U ^c z ) = ( U ^c u ) )'), w.s([], 'id', '( z = u -> z = u )')],
           'oveq12d', '( z = u -> ( ( U ^c z ) / z ) = ( ( U ^c u ) / u ) )')
pkvv = w.s([ud, w.s([w.s([], 'ovex', '( ( U ^c u ) / u ) e. _V')], 'a1i', '( %s -> ( ( U ^c u ) / u ) e. _V )' % AUP),
            w.s([sub2, w.s([], 'eqid', '%s = %s' % (PK0, PK0))], 'fvmptg',
                '( ( u e. %s /\\ ( ( U ^c u ) / u ) e. _V ) -> ( %s ` u ) = ( ( U ^c u ) / u ) )' % (DOM, PK0))],
           'syl2anc', '( %s -> ( %s ` u ) = ( ( U ^c u ) / u ) )' % (AUP, PK0))
same = w.s([w.s([g1v, w.s([cxu, usub], 'oveq12d',
                          '( %s -> ( ( %s ` u ) / ( u - 0 ) ) = ( ( U ^c u ) / u ) )' % (AUP, CXC))], 'eqtrd',
                '( %s -> ( %s ` u ) = ( ( U ^c u ) / u ) )' % (AUP, G1)),
            w.s([pkvv], 'eqcomd', '( %s -> ( ( U ^c u ) / u ) = ( %s ` u ) )' % (AUP, PK0))], 'eqtrd',
           '( %s -> ( %s ` u ) = ( %s ` u ) )' % (AUP, G1, PK0))
crex = w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'a1i', '( %s -> CC e. _V )' % A2), rss], 'ssexd',
           '( %s -> ( A crect B ) e. _V )' % A2)
pex = w.s([crex, w.inst('difexg')], 'syl', '( %s -> ( ( A crect B ) \\ { 0 } ) e. _V )' % A2)
g1v2 = w.s([pex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A2, G1))
dex = w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'a1i', '( %s -> CC e. _V )' % A2), w.inst('difexg')], 'syl',
          '( %s -> %s e. _V )' % (A2, DOM))
pk0v = w.s([dex, w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (A2, PK0))
eqi = w.s([w.s([abp, pint], 'jca', '( %s -> ( %s /\\ ( 0 e. CC /\\ %s ) ) )' % (A2, AB, INTR)),
           w.s([g1v2, pk0v], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A2, G1, PK0)),
           w.s([same], 'ralrimiva', '( %s -> A. u e. ( ( A crect B ) \\ { 0 } ) ( %s ` u ) = ( %s ` u ) )' % (A2, G1, PK0)),
           w.inst('rectinteqp')], 'syl3anc',
          '( %s -> ( %s rectint <. A , B >. ) = ( %s rectint <. A , B >. ) )' % (A2, G1, PK0))
w.qed([w.s([eqi], 'eqcomd', '( %s -> ( %s rectint <. A , B >. ) = ( %s rectint <. A , B >. ) )' % (A2, PK0, G1)),
       w.s([cau, rhs], 'eqtrd', '( %s -> ( %s rectint <. A , B >. ) = %s )' % (A2, G1, TPIC))], 'eqtrd',
      '( %s -> ( %s rectint <. A , B >. ) = %s )' % (A2, PK0, TPIC))
run4(w)
