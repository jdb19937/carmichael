"""C4, Perron block 3: the modulus of the integrand and the vertical edge bound."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

PK0 = PKF('U')
DOM = '( CC \\ { 0 } )'

# ---------------------------------------------------------------- pkfval
A0 = '( U e. RR+ /\\ V e. %s )' % DOM
w = W('pkfval', 'The value and the modulus of the Perron integrand ` ( U ^c z ) / z ` '
      'at a nonzero point.')
urp = w.s([], 'simpl', '( %s -> U e. RR+ )' % A0)
vd = w.s([], 'simpr', '( %s -> V e. %s )' % (A0, DOM))
vp = w.s([vd, w.inst('eldifsn')], 'sylib', '( %s -> ( V e. CC /\\ V =/= 0 ) )' % A0)
vc = w.s([vp, w.inst('simpl')], 'syl', '( %s -> V e. CC )' % A0)
vne = w.s([vp, w.inst('simpr')], 'syl', '( %s -> V =/= 0 )' % A0)
sub = w.s([w.s([], 'oveq2', '( z = V -> ( U ^c z ) = ( U ^c V ) )'), w.s([], 'id', '( z = V -> z = V )')],
          'oveq12d', '( z = V -> ( ( U ^c z ) / z ) = ( ( U ^c V ) / V ) )')
val = w.s([vd, w.s([w.s([], 'ovex', '( ( U ^c V ) / V ) e. _V')], 'a1i', '( %s -> ( ( U ^c V ) / V ) e. _V )' % A0),
           w.s([sub, w.s([], 'eqid', '%s = %s' % (PK0, PK0))], 'fvmptg',
               '( ( V e. %s /\\ ( ( U ^c V ) / V ) e. _V ) -> ( %s ` V ) = ( ( U ^c V ) / V ) )' % (DOM, PK0))],
          'syl2anc', '( %s -> ( %s ` V ) = ( ( U ^c V ) / V ) )' % (A0, PK0))
ad = w.s([w.s([w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0), vc], 'cxpcld', '( %s -> ( U ^c V ) e. CC )' % A0),
          vc, vne], 'absdivd',
         '( %s -> ( abs ` ( ( U ^c V ) / V ) ) = ( ( abs ` ( U ^c V ) ) / ( abs ` V ) ) )' % A0)
ac = w.s([urp, vc, w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` ( U ^c V ) ) = ( U ^c ( Re ` V ) ) )' % A0)
w.qed([w.s([val], 'fveq2d', '( %s -> ( abs ` ( %s ` V ) ) = ( abs ` ( ( U ^c V ) / V ) ) )' % (A0, PK0)),
       w.s([ad, w.s([ac], 'oveq1d',
                    '( %s -> ( ( abs ` ( U ^c V ) ) / ( abs ` V ) ) = ( ( U ^c ( Re ` V ) ) / ( abs ` V ) ) )' % A0)],
           'eqtrd', '( %s -> ( abs ` ( ( U ^c V ) / V ) ) = ( ( U ^c ( Re ` V ) ) / ( abs ` V ) ) )' % A0)],
      'eqtrd', '( %s -> ( abs ` ( %s ` V ) ) = ( ( U ^c ( Re ` V ) ) / ( abs ` V ) ) )' % (A0, PK0))
run4(w)

# ---------------------------------------------------------------- csegne0
A1 = '( ( P e. RR /\\ P =/= 0 ) /\\ ( S e. RR /\\ T e. RR ) )'
CA = CPT('P', 'S'); CB = CPT('P', 'T')
w = W('csegne0', 'A vertical segment off the imaginary axis misses the origin: every '
      'point has the same nonzero real part ( ~ csegvre ).')
pr = w.s([], 'simpll', '( %s -> P e. RR )' % A1)
pne = w.s([], 'simplr', '( %s -> P =/= 0 )' % A1)
sr = w.s([], 'simprl', '( %s -> S e. RR )' % A1)
tr = w.s([], 'simprr', '( %s -> T e. RR )' % A1)
ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A1)
ac = w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A1),
          w.s([ic, w.s([sr], 'recnd', '( %s -> S e. CC )' % A1)], 'mulcld', '( %s -> ( _i x. S ) e. CC )' % A1)],
         'addcld', '( %s -> %s e. CC )' % (A1, CA))
bc = w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A1),
          w.s([ic, w.s([tr], 'recnd', '( %s -> T e. CC )' % A1)], 'mulcld', '( %s -> ( _i x. T ) e. CC )' % A1)],
         'addcld', '( %s -> %s e. CC )' % (A1, CB))
rea = w.s([pr, sr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = P )' % (A1, CA))
reb = w.s([pr, tr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = P )' % (A1, CB))
eqr = w.s([rea, w.s([reb], 'eqcomd', '( %s -> P = ( Re ` %s ) )' % (A1, CB))], 'eqtrd',
          '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (A1, CA, CB))
cv = w.s([ac, bc, eqr, w.inst('csegvre')], 'syl3anc',
         '( %s -> A. u e. ( %s cseg %s ) ( Re ` u ) = ( Re ` %s ) )' % (A1, CA, CB, CA))
AU = '( %s /\\ u e. ( %s cseg %s ) )' % (A1, CA, CB)
um = w.s([], 'simpr', '( %s -> u e. ( %s cseg %s ) )' % (AU, CA, CB))
uc = w.s([w.s([w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AU, CA)), w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AU, CB)),
               w.inst('csegcl')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ CC )' % (AU, CA, CB)), um], 'sseldd',
         '( %s -> u e. CC )' % AU)
ureq = w.s([w.s([cv], 'adantr', '( %s -> A. u e. ( %s cseg %s ) ( Re ` u ) = ( Re ` %s ) )' % (AU, CA, CB, CA)),
            um, w.inst('rspa')], 'syl2anc', '( %s -> ( Re ` u ) = ( Re ` %s ) )' % (AU, CA))
urp2 = w.s([ureq, w.s([rea], 'adantr', '( %s -> ( Re ` %s ) = P )' % (AU, CA))], 'eqtrd',
           '( %s -> ( Re ` u ) = P )' % AU)
# u =/= 0 : otherwise ( Re ` u ) = 0
AZ = '( %s /\\ u = 0 )' % AU
e1 = w.s([w.s([], 'simpr', '( %s -> u = 0 )' % AZ)], 'fveq2d', '( %s -> ( Re ` u ) = ( Re ` 0 ) )' % AZ)
e2 = w.s([e1, w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % AZ)], 'eqtrd',
         '( %s -> ( Re ` u ) = 0 )' % AZ)
e3 = w.s([w.s([urp2], 'adantr', '( %s -> ( Re ` u ) = P )' % AZ), e2], 'eqtr3d', '( %s -> P = 0 )' % AZ)
e4 = w.s([w.s([w.s([pne], 'adantr', '( %s -> P =/= 0 )' % AU)], 'neneqd', '( %s -> -. P = 0 )' % AU)], 'adantr',
         '( %s -> -. P = 0 )' % AZ)
une = w.s([w.s([e3, e4], 'pm2.65da', '( %s -> -. u = 0 )' % AU)], 'neqned', '( %s -> u =/= 0 )' % AU)
mem = w.s([uc, une, w.inst('eldifsn')], 'sylanbrc', '( %s -> u e. %s )' % (AU, DOM))
w.qed([mem], 'ralrimiva', '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (A1, CA, CB, DOM))
run4(w)

# ---------------------------------------------------------------- vedgbnd
A2 = '( ( U e. RR+ /\\ ( P e. RR /\\ P =/= 0 ) ) /\\ ( S e. RR /\\ T e. RR ) )'
MB = '( ( U ^c P ) / ( abs ` P ) )'
w = W('vedgbnd', 'The vertical-edge bound for the Perron integrand: on the segment at '
      'real part ` P ` the modulus is at most ` ( U ^c P ) / ( abs ` P ) `, so the '
      'segment integral is at most that times the length ( ~ lintabs ).  This is '
      '` norm_vert_edge_le ` of Route Z\'s PerronKernel.lean.')
upr = w.s([], 'simpl', '( %s -> ( U e. RR+ /\\ ( P e. RR /\\ P =/= 0 ) ) )' % A2)
urp = w.s([upr, w.inst('simpl')], 'syl', '( %s -> U e. RR+ )' % A2)
prr = w.s([upr, w.inst('simpr')], 'syl', '( %s -> ( P e. RR /\\ P =/= 0 ) )' % A2)
pr = w.s([prr, w.inst('simpl')], 'syl', '( %s -> P e. RR )' % A2)
pne = w.s([prr, w.inst('simpr')], 'syl', '( %s -> P =/= 0 )' % A2)
sr = w.s([], 'simprl', '( %s -> S e. RR )' % A2)
tr = w.s([], 'simprr', '( %s -> T e. RR )' % A2)
ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A2)
ac = w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A2),
          w.s([ic, w.s([sr], 'recnd', '( %s -> S e. CC )' % A2)], 'mulcld', '( %s -> ( _i x. S ) e. CC )' % A2)],
         'addcld', '( %s -> %s e. CC )' % (A2, CA))
bc = w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A2),
          w.s([ic, w.s([tr], 'recnd', '( %s -> T e. CC )' % A2)], 'mulcld', '( %s -> ( _i x. T ) e. CC )' % A2)],
         'addcld', '( %s -> %s e. CC )' % (A2, CB))
rea = w.s([pr, sr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = P )' % (A2, CA))
reb = w.s([pr, tr, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` %s ) = P )' % (A2, CB))
eqr = w.s([rea, w.s([reb], 'eqcomd', '( %s -> P = ( Re ` %s ) )' % (A2, CB))], 'eqtrd',
          '( %s -> ( Re ` %s ) = ( Re ` %s ) )' % (A2, CA, CB))
# the segment misses the origin
ne0 = w.s([w.s([w.s([prr, w.s([sr, tr], 'jca', '( %s -> ( S e. RR /\\ T e. RR ) )' % A2)], 'jca',
                    '( %s -> ( ( P e. RR /\\ P =/= 0 ) /\\ ( S e. RR /\\ T e. RR ) ) )' % A2), w.inst('csegne0')], 'syl',
               '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (A2, CA, CB, DOM)),
           w.s([w.s([], 'dfss3', '( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s )' % (CA, CB, DOM, CA, CB, DOM))], 'a1i',
               '( %s -> ( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s ) )' % (A2, CA, CB, DOM, CA, CB, DOM))],
          'mpbird', '( %s -> ( %s cseg %s ) C_ %s )' % (A2, CA, CB, DOM))
fcn = w.s([w.s([urp, w.s([w.s([], 'ssid', '%s C_ %s' % (DOM, DOM))], 'a1i', '( %s -> %s C_ %s )' % (A2, DOM, DOM))], 'jca',
               '( %s -> ( U e. RR+ /\\ %s C_ %s ) )' % (A2, DOM, DOM)), w.inst('pkfcn')], 'syl',
          '( %s -> %s e. ( %s -cn-> CC ) )' % (A2, PK0, DOM))
# the pointwise bound
cvre = w.s([ac, bc, eqr, w.inst('csegvre')], 'syl3anc',
           '( %s -> A. u e. ( %s cseg %s ) ( Re ` u ) = ( Re ` %s ) )' % (A2, CA, CB, CA))
AZ2 = '( %s /\\ a e. ( %s cseg %s ) )' % (A2, CA, CB)
zm = w.s([], 'simpr', '( %s -> a e. ( %s cseg %s ) )' % (AZ2, CA, CB))
zd = w.s([w.s([ne0], 'adantr', '( %s -> ( %s cseg %s ) C_ %s )' % (AZ2, CA, CB, DOM)), zm], 'sseldd',
         '( %s -> a e. %s )' % (AZ2, DOM))
zp = w.s([zd, w.inst('eldifsn')], 'sylib', '( %s -> ( a e. CC /\\ a =/= 0 ) )' % AZ2)
zc = w.s([zp, w.inst('simpl')], 'syl', '( %s -> a e. CC )' % AZ2)
zne = w.s([zp, w.inst('simpr')], 'syl', '( %s -> a =/= 0 )' % AZ2)
zsub = w.s([w.s([], 'fveq2', '( u = a -> ( Re ` u ) = ( Re ` a ) )')], 'eqeq1d',
           '( u = a -> ( ( Re ` u ) = ( Re ` %s ) <-> ( Re ` a ) = ( Re ` %s ) ) )' % (CA, CA))
zre = w.s([zsub, w.s([cvre], 'adantr', '( %s -> A. u e. ( %s cseg %s ) ( Re ` u ) = ( Re ` %s ) )' % (AZ2, CA, CB, CA)), zm],
          'rspcdva', '( %s -> ( Re ` a ) = ( Re ` %s ) )' % (AZ2, CA))
zreP = w.s([zre, w.s([rea], 'adantr', '( %s -> ( Re ` %s ) = P )' % (AZ2, CA))], 'eqtrd',
           '( %s -> ( Re ` a ) = P )' % AZ2)
pv = w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ2), zd], 'jca',
         '( %s -> ( U e. RR+ /\\ a e. %s ) )' % (AZ2, DOM))
pab = w.s([pv, w.inst('pkfval')], 'syl',
          '( %s -> ( abs ` ( %s ` a ) ) = ( ( U ^c ( Re ` a ) ) / ( abs ` a ) ) )' % (AZ2, PK0))
pab2 = w.s([pab, w.s([w.s([zreP], 'oveq2d', '( %s -> ( U ^c ( Re ` a ) ) = ( U ^c P ) )' % AZ2)], 'oveq1d',
                     '( %s -> ( ( U ^c ( Re ` a ) ) / ( abs ` a ) ) = ( ( U ^c P ) / ( abs ` a ) ) )' % AZ2)],
           'eqtrd', '( %s -> ( abs ` ( %s ` a ) ) = ( ( U ^c P ) / ( abs ` a ) ) )' % (AZ2, PK0))
absP = w.s([w.s([w.s([pr], 'adantr', '( %s -> P e. RR )' % AZ2)], 'recnd', '( %s -> P e. CC )' % AZ2),
            w.s([pne], 'adantr', '( %s -> P =/= 0 )' % AZ2)], 'absrpcld', '( %s -> ( abs ` P ) e. RR+ )' % AZ2)
absz = w.s([zc, zne], 'absrpcld', '( %s -> ( abs ` a ) e. RR+ )' % AZ2)
lezp = w.s([w.s([zc, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` a ) ) <_ ( abs ` a ) )' % AZ2),
            w.s([zreP], 'fveq2d', '( %s -> ( abs ` ( Re ` a ) ) = ( abs ` P ) )' % AZ2)], 'eqbrtrd',
           '( %s -> ( abs ` P ) <_ ( abs ` a ) )' % AZ2)
w.lines.pop()
lezp = w.s([w.s([w.s([zreP], 'fveq2d', '( %s -> ( abs ` ( Re ` a ) ) = ( abs ` P ) )' % AZ2)], 'eqcomd',
                '( %s -> ( abs ` P ) = ( abs ` ( Re ` a ) ) )' % AZ2),
            w.s([zc, w.inst('absrele')], 'syl', '( %s -> ( abs ` ( Re ` a ) ) <_ ( abs ` a ) )' % AZ2)], 'eqbrtrd',
           '( %s -> ( abs ` P ) <_ ( abs ` a ) )' % AZ2)
upr2 = w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AZ2), w.s([pr], 'adantr', '( %s -> P e. RR )' % AZ2)],
           'rpcxpcld', '( %s -> ( U ^c P ) e. RR+ )' % AZ2)
div = w.s([absP, absz, w.s([upr2], 'rpred', '( %s -> ( U ^c P ) e. RR )' % AZ2),
           w.s([upr2], 'rpge0d', '( %s -> 0 <_ ( U ^c P ) )' % AZ2), lezp], 'lediv2ad',
          '( %s -> ( ( U ^c P ) / ( abs ` a ) ) <_ %s )' % (AZ2, MB))
ptw = w.s([pab2, div], 'eqbrtrd', '( %s -> ( abs ` ( %s ` a ) ) <_ %s )' % (AZ2, PK0, MB))
allz = w.s([ptw], 'ralrimiva', '( %s -> A. a e. ( %s cseg %s ) ( abs ` ( %s ` a ) ) <_ %s )' % (A2, CA, CB, PK0, MB))
mr = w.s([w.s([urp, pr], 'rpcxpcld', '( %s -> ( U ^c P ) e. RR+ )' % A2),
          w.s([w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A2), pne], 'absrpcld', '( %s -> ( abs ` P ) e. RR+ )' % A2)],
              'rpred', '( %s -> ( abs ` P ) e. RR )' % A2),
          w.s([w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A2), pne], 'absrpcld', '( %s -> ( abs ` P ) e. RR+ )' % A2)],
              'rpne0d', '( %s -> ( abs ` P ) =/= 0 )' % A2)], 'redivcld', 'dummy')
w.lines.pop()
apr = w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A2), pne], 'absrpcld', '( %s -> ( abs ` P ) e. RR+ )' % A2)
mr = w.s([w.s([urp, pr], 'rpcxpcld', '( %s -> ( U ^c P ) e. RR+ )' % A2), apr], 'rpdivcld',
         '( %s -> %s e. RR+ )' % (A2, MB))
w.qed([w.s([w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A2, CA, CB)),
            w.s([fcn, ne0], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (A2, PK0, DOM, CA, CB, DOM))],
           'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) ) )' % (A2, CA, CB, PK0, DOM, CA, CB, DOM)),
       w.s([mr], 'rpred', '( %s -> %s e. RR )' % (A2, MB)), allz, w.inst('lintabs')], 'syl3anc',
      '( %s -> ( abs ` ( %s lint <. %s , %s >. ) ) <_ ( %s x. ( abs ` ( %s - %s ) ) ) )' % (A2, PK0, CA, CB, MB, CB, CA))
run4(w)
