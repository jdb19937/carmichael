"""C4, Perron block 8: the horizontal edge bound."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

DOM = '( CC \\ { 0 } )'
PK0 = PKF('U')
HA = CPT('P', 'S'); HBB = CPT('Q', 'S')
X = '( 0 (,) 1 )'
K = '( Q - P )'
L = '( log ` U )'


def WT(t):
    return '( P + ( %s x. %s ) )' % (t, K)


HBD = '( ( U ^c %s ) x. %s )' % (WT('t'), K)

# ---------------------------------------------------------------- cseghne0
A1 = '( ( S e. RR /\\ S =/= 0 ) /\\ ( P e. RR /\\ Q e. RR ) )'
w = W('cseghne0', 'A horizontal segment off the real axis misses the origin: every '
      'point has the same nonzero imaginary part ( ~ cseghim ).')
sr = w.s([], 'simpll', '( %s -> S e. RR )' % A1)
sne = w.s([], 'simplr', '( %s -> S =/= 0 )' % A1)
pr = w.s([], 'simprl', '( %s -> P e. RR )' % A1)
qr = w.s([], 'simprr', '( %s -> Q e. RR )' % A1)
ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A1)
isc = w.s([ic, w.s([sr], 'recnd', '( %s -> S e. CC )' % A1)], 'mulcld', '( %s -> ( _i x. S ) e. CC )' % A1)
ac = w.s([w.s([pr], 'recnd', '( %s -> P e. CC )' % A1), isc], 'addcld', '( %s -> %s e. CC )' % (A1, HA))
bc = w.s([w.s([qr], 'recnd', '( %s -> Q e. CC )' % A1), isc], 'addcld', '( %s -> %s e. CC )' % (A1, HBB))
ima = w.s([pr, sr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = S )' % (A1, HA))
imb = w.s([qr, sr, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` %s ) = S )' % (A1, HBB))
eqi = w.s([ima, w.s([imb], 'eqcomd', '( %s -> S = ( Im ` %s ) )' % (A1, HBB))], 'eqtrd',
          '( %s -> ( Im ` %s ) = ( Im ` %s ) )' % (A1, HA, HBB))
cv = w.s([ac, bc, eqi, w.inst('cseghim')], 'syl3anc',
         '( %s -> A. u e. ( %s cseg %s ) ( Im ` u ) = ( Im ` %s ) )' % (A1, HA, HBB, HA))
AU = '( %s /\\ u e. ( %s cseg %s ) )' % (A1, HA, HBB)
um = w.s([], 'simpr', '( %s -> u e. ( %s cseg %s ) )' % (AU, HA, HBB))
uc = w.s([w.s([w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AU, HA)), w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AU, HBB)),
               w.inst('csegcl')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ CC )' % (AU, HA, HBB)), um], 'sseldd',
         '( %s -> u e. CC )' % AU)
ueq = w.s([w.s([cv], 'adantr', '( %s -> A. u e. ( %s cseg %s ) ( Im ` u ) = ( Im ` %s ) )' % (AU, HA, HBB, HA)), um,
           w.inst('rspa')], 'syl2anc', '( %s -> ( Im ` u ) = ( Im ` %s ) )' % (AU, HA))
ueqS = w.s([ueq, w.s([ima], 'adantr', '( %s -> ( Im ` %s ) = S )' % (AU, HA))], 'eqtrd', '( %s -> ( Im ` u ) = S )' % AU)
AZ = '( %s /\\ u = 0 )' % AU
z1 = w.s([w.s([w.s([], 'simpr', '( %s -> u = 0 )' % AZ)], 'fveq2d', '( %s -> ( Im ` u ) = ( Im ` 0 ) )' % AZ),
          w.s([w.s([], 'im0', '( Im ` 0 ) = 0')], 'a1i', '( %s -> ( Im ` 0 ) = 0 )' % AZ)], 'eqtrd',
         '( %s -> ( Im ` u ) = 0 )' % AZ)
z2 = w.s([w.s([ueqS], 'adantr', '( %s -> ( Im ` u ) = S )' % AZ), z1], 'eqtr3d', '( %s -> S = 0 )' % AZ)
z3 = w.s([w.s([w.s([sne], 'adantr', '( %s -> S =/= 0 )' % AU)], 'neneqd', '( %s -> -. S = 0 )' % AU)], 'adantr',
         '( %s -> -. S = 0 )' % AZ)
une = w.s([w.s([z2, z3], 'pm2.65da', '( %s -> -. u = 0 )' % AU)], 'neqned', '( %s -> u =/= 0 )' % AU)
mem = w.s([uc, une, w.inst('eldifsn')], 'sylanbrc', '( %s -> u e. %s )' % (AU, DOM))
w.qed([mem], 'ralrimiva', '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (A1, HA, HBB, DOM))
run4(w)

# ---------------------------------------------------------------- hedgbnd
A0C = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( P e. RR /\\ Q e. RR ) )'
A2 = '( %s /\\ ( ( S e. RR /\\ S =/= 0 ) /\\ P <_ Q ) )' % A0C
REC = '( 1 / ( abs ` S ) )'
HH = '( %s x. %s )' % (REC, HBD)
DIF = '( %s - %s )' % (HBB, HA)
WW = '( %s + ( t x. %s ) )' % (HA, DIF)
INTG = '( ( %s ` %s ) x. %s )' % (PK0, WW, DIF)
w = W('hedgbnd', 'The horizontal-edge bound for the Perron integrand: on the segment '
      'at height ` S ` the modulus of the integrand is at most '
      '` ( U ^c ( Re ` z ) ) / ( abs ` S ) `, and the resulting majorant integrates '
      'to ` ( ( U ^c Q ) - ( U ^c P ) ) / ( log ` U ) ` ( ~ cxpaffitg ).  This is '
      '` norm_horiz_edge_le ` of Route Z\'s PerronKernel.lean.')
a0 = w.s([], 'simpl', '( %s -> %s )' % (A2, A0C))
urp = w.s([w.s([a0, w.inst('simpl')], 'syl', '( %s -> ( U e. RR+ /\\ U =/= 1 ) )' % A2), w.inst('simpl')], 'syl',
          '( %s -> U e. RR+ )' % A2)
une = w.s([w.s([a0, w.inst('simpl')], 'syl', '( %s -> ( U e. RR+ /\\ U =/= 1 ) )' % A2), w.inst('simpr')], 'syl',
          '( %s -> U =/= 1 )' % A2)
pr = w.s([w.s([a0, w.inst('simpr')], 'syl', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A2), w.inst('simpl')], 'syl',
         '( %s -> P e. RR )' % A2)
qr = w.s([w.s([a0, w.inst('simpr')], 'syl', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A2), w.inst('simpr')], 'syl',
         '( %s -> Q e. RR )' % A2)
sr = w.s([], 'simprll', '( %s -> S e. RR )' % A2)
sne = w.s([], 'simprlr', '( %s -> S =/= 0 )' % A2)
ple = w.s([], 'simprr', '( %s -> P <_ Q )' % A2)
pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A2)
qc = w.s([qr], 'recnd', '( %s -> Q e. CC )' % A2)
kr = w.s([qr, pr], 'resubcld', '( %s -> %s e. RR )' % (A2, K))
kc = w.s([kr], 'recnd', '( %s -> %s e. CC )' % (A2, K))
k0 = w.s([ple, w.s([qr, pr], 'subge0d', '( %s -> ( 0 <_ %s <-> P <_ Q ) )' % (A2, K))], 'mpbird',
         '( %s -> 0 <_ %s )' % (A2, K))
ic = w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A2)
isc = w.s([ic, w.s([sr], 'recnd', '( %s -> S e. CC )' % A2)], 'mulcld', '( %s -> ( _i x. S ) e. CC )' % A2)
ac = w.s([pc, isc], 'addcld', '( %s -> %s e. CC )' % (A2, HA))
bc = w.s([qc, isc], 'addcld', '( %s -> %s e. CC )' % (A2, HBB))
asr = w.s([w.s([sr], 'recnd', '( %s -> S e. CC )' % A2), sne], 'absrpcld', '( %s -> ( abs ` S ) e. RR+ )' % A2)
recp = w.s([w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % A2), asr], 'rpdivcld',
           '( %s -> %s e. RR+ )' % (A2, REC))
# ( HBB - HA ) = ( Q - P )
d1 = w.s([qc, isc, pc, isc], 'addsub4d', '( %s -> %s = ( %s + ( ( _i x. S ) - ( _i x. S ) ) ) )' % (A2, DIF, K))
dba = w.s([d1, w.s([w.s([w.s([isc], 'subidd', '( %s -> ( ( _i x. S ) - ( _i x. S ) ) = 0 )' % A2)], 'oveq2d',
                        '( %s -> ( %s + ( ( _i x. S ) - ( _i x. S ) ) ) = ( %s + 0 ) )' % (A2, K, K)),
                    w.s([kc], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (A2, K, K))], 'eqtrd',
                   '( %s -> ( %s + ( ( _i x. S ) - ( _i x. S ) ) ) = %s )' % (A2, K, K))], 'eqtrd',
          '( %s -> %s = %s )' % (A2, DIF, K))
# the pointwise work
AT = '( %s /\\ t e. %s )' % (A2, X)
tio = w.s([], 'simpr', '( %s -> t e. %s )' % (AT, X))
tr = w.s([w.s([w.s([], 'ioossre', '%s C_ RR' % X)], 'a1i', '( %s -> %s C_ RR )' % (AT, X)), tio], 'sseldd',
         '( %s -> t e. RR )' % AT)
tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % AT)
kct = w.s([kc], 'adantr', '( %s -> %s e. CC )' % (AT, K))
pct = w.s([pc], 'adantr', '( %s -> P e. CC )' % AT)
isct = w.s([isc], 'adantr', '( %s -> ( _i x. S ) e. CC )' % AT)
wre = w.s([w.s([w.s([dba], 'adantr', '( %s -> %s = %s )' % (AT, DIF, K))], 'oveq2d',
                '( %s -> ( t x. %s ) = ( t x. %s ) )' % (AT, DIF, K))], 'oveq2d',
           '( %s -> %s = ( %s + ( t x. %s ) ) )' % (AT, WW, HA, K))
wre2 = w.s([wre, w.s([pct, isct, w.s([tc, kct], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (AT, K))], 'add32d',
                     '( %s -> ( ( P + ( _i x. S ) ) + ( t x. %s ) ) = ( ( P + ( t x. %s ) ) + ( _i x. S ) ) )' % (AT, K, K))],
           'eqtrd', '( %s -> %s = ( %s + ( _i x. S ) ) )' % (AT, WW, WT('t')))
wtr = w.s([w.s([pr], 'adantr', '( %s -> P e. RR )' % AT), w.s([tr, w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K))],
                                                             'remulcld', '( %s -> ( t x. %s ) e. RR )' % (AT, K))],
          'readdcld', '( %s -> %s e. RR )' % (AT, WT('t')))
srt = w.s([sr], 'adantr', '( %s -> S e. RR )' % AT)
rew = w.s([w.s([wre2], 'fveq2d', '( %s -> ( Re ` %s ) = ( Re ` ( %s + ( _i x. S ) ) ) )' % (AT, WW, WT('t'))),
           w.s([wtr, srt, w.inst('crre')], 'syl2anc', '( %s -> ( Re ` ( %s + ( _i x. S ) ) ) = %s )' % (AT, WT('t'), WT('t')))],
          'eqtrd', '( %s -> ( Re ` %s ) = %s )' % (AT, WW, WT('t')))
imw = w.s([w.s([wre2], 'fveq2d', '( %s -> ( Im ` %s ) = ( Im ` ( %s + ( _i x. S ) ) ) )' % (AT, WW, WT('t'))),
           w.s([wtr, srt, w.inst('crim')], 'syl2anc', '( %s -> ( Im ` ( %s + ( _i x. S ) ) ) = S )' % (AT, WT('t')))],
          'eqtrd', '( %s -> ( Im ` %s ) = S )' % (AT, WW))
# W is in the punctured plane
pair1 = w.s([sr, sne], 'jca', '( %s -> ( S e. RR /\\ S =/= 0 ) )' % A2)
pair2 = w.s([pr, qr], 'jca', '( %s -> ( P e. RR /\\ Q e. RR ) )' % A2)
both = w.s([pair1, pair2], 'jca', '( %s -> ( ( S e. RR /\\ S =/= 0 ) /\\ ( P e. RR /\\ Q e. RR ) ) )' % A2)
ssh = w.s([both, w.inst('cseghne0')], 'syl',
          '( %s -> A. u e. ( %s cseg %s ) u e. %s )' % (A2, HA, HBB, DOM))
sss = w.s([ssh, w.s([w.s([], 'dfss3', '( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s )' % (HA, HBB, DOM, HA, HBB, DOM))],
                    'a1i', '( %s -> ( ( %s cseg %s ) C_ %s <-> A. u e. ( %s cseg %s ) u e. %s ) )' % (A2, HA, HBB, DOM, HA, HBB, DOM))],
          'mpbird', '( %s -> ( %s cseg %s ) C_ %s )' % (A2, HA, HBB, DOM))
t01 = w.s([w.s([w.s([], 'ioossicc', '%s C_ ( 0 [,] 1 )' % X)], 'a1i', '( %s -> %s C_ ( 0 [,] 1 ) )' % (AT, X)), tio],
          'sseldd', '( %s -> t e. ( 0 [,] 1 ) )' % AT)
wseg = w.s([w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AT, HA)), w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AT, HBB)),
            t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( %s cseg %s ) )' % (AT, WW, HA, HBB))
wd = w.s([w.s([sss], 'adantr', '( %s -> ( %s cseg %s ) C_ %s )' % (AT, HA, HBB, DOM)), wseg], 'sseldd',
         '( %s -> %s e. %s )' % (AT, WW, DOM))
wc = w.s([wd, w.inst('eldifi')], 'syl', '( %s -> %s e. CC )' % (AT, WW))
wne = w.s([wd, w.inst('eldifsni')], 'syl', '( %s -> %s =/= 0 )' % (AT, WW))
# the pointwise bound
pkv = w.s([w.s([w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AT), wd], 'jca',
                '( %s -> ( U e. RR+ /\\ %s e. %s ) )' % (AT, WW, DOM)), w.inst('pkfval')], 'syl',
          '( %s -> ( abs ` ( %s ` %s ) ) = ( ( U ^c ( Re ` %s ) ) / ( abs ` %s ) ) )' % (AT, PK0, WW, WW, WW))
pkv2 = w.s([pkv, w.s([w.s([rew], 'oveq2d', '( %s -> ( U ^c ( Re ` %s ) ) = ( U ^c %s ) )' % (AT, WW, WT('t')))], 'oveq1d',
                     '( %s -> ( ( U ^c ( Re ` %s ) ) / ( abs ` %s ) ) = ( ( U ^c %s ) / ( abs ` %s ) ) )' % (AT, WW, WW, WT('t'), WW))],
           'eqtrd', '( %s -> ( abs ` ( %s ` %s ) ) = ( ( U ^c %s ) / ( abs ` %s ) ) )' % (AT, PK0, WW, WT('t'), WW))
fcn = w.s([w.s([urp, w.s([w.s([], 'ssid', '%s C_ %s' % (DOM, DOM))], 'a1i', '( %s -> %s C_ %s )' % (A2, DOM, DOM))], 'jca',
               '( %s -> ( U e. RR+ /\\ %s C_ %s ) )' % (A2, DOM, DOM)), w.inst('pkfcn')], 'syl',
          '( %s -> %s e. ( %s -cn-> CC ) )' % (A2, PK0, DOM))
pkfv = w.s([w.s([fcn], 'adantr', '( %s -> %s e. ( %s -cn-> CC ) )' % (AT, PK0, DOM)), w.inst('cncff')], 'syl',
           '( %s -> %s : %s --> CC )' % (AT, PK0, DOM))
pkcl = w.s([pkfv, wd], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (AT, PK0, WW))
difc = w.s([w.s([bc], 'adantr', '( %s -> %s e. CC )' % (AT, HBB)), w.s([ac], 'adantr', '( %s -> %s e. CC )' % (AT, HA))],
           'subcld', '( %s -> %s e. CC )' % (AT, DIF))
absi = w.s([pkcl, difc], 'absmuld',
           '( %s -> ( abs ` %s ) = ( ( abs ` ( %s ` %s ) ) x. ( abs ` %s ) ) )' % (AT, INTG, PK0, WW, DIF))
absd = w.s([w.s([w.s([dba], 'adantr', '( %s -> %s = %s )' % (AT, DIF, K))], 'fveq2d',
                '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (AT, DIF, K)),
            w.s([w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K)), w.s([k0], 'adantr', '( %s -> 0 <_ %s )' % (AT, K))],
                'absidd', '( %s -> ( abs ` %s ) = %s )' % (AT, K, K))], 'eqtrd',
           '( %s -> ( abs ` %s ) = %s )' % (AT, DIF, K))
absi2 = w.s([absi, w.s([pkv2, absd], 'oveq12d',
                       '( %s -> ( ( abs ` ( %s ` %s ) ) x. ( abs ` %s ) ) = ( ( ( U ^c %s ) / ( abs ` %s ) ) x. %s ) )' % (AT, PK0, WW, DIF, WT('t'), WW, K))],
            'eqtrd', '( %s -> ( abs ` %s ) = ( ( ( U ^c %s ) / ( abs ` %s ) ) x. %s ) )' % (AT, INTG, WT('t'), WW, K))
# the estimate
absw = w.s([wc, wne], 'absrpcld', '( %s -> ( abs ` %s ) e. RR+ )' % (AT, WW))
asrt = w.s([asr], 'adantr', '( %s -> ( abs ` S ) e. RR+ )' % AT)
lew = w.s([w.s([w.s([imw], 'fveq2d', '( %s -> ( abs ` ( Im ` %s ) ) = ( abs ` S ) )' % (AT, WW))], 'eqcomd',
                '( %s -> ( abs ` S ) = ( abs ` ( Im ` %s ) ) )' % (AT, WW)),
            w.s([wc, w.inst('absimle')], 'syl', '( %s -> ( abs ` ( Im ` %s ) ) <_ ( abs ` %s ) )' % (AT, WW, WW))],
           'eqbrtrd', '( %s -> ( abs ` S ) <_ ( abs ` %s ) )' % (AT, WW))
urpt = w.s([urp], 'adantr', '( %s -> U e. RR+ )' % AT)
cxp = w.s([urpt, wtr], 'rpcxpcld', '( %s -> ( U ^c %s ) e. RR+ )' % (AT, WT('t')))
dle = w.s([asrt, absw, w.s([cxp], 'rpred', '( %s -> ( U ^c %s ) e. RR )' % (AT, WT('t'))),
           w.s([cxp], 'rpge0d', '( %s -> 0 <_ ( U ^c %s ) )' % (AT, WT('t'))), lew], 'lediv2ad',
          '( %s -> ( ( U ^c %s ) / ( abs ` %s ) ) <_ ( ( U ^c %s ) / ( abs ` S ) ) )' % (AT, WT('t'), WW, WT('t')))
mle = w.s([w.s([w.s([cxp, absw], 'rpdivcld', '( %s -> ( ( U ^c %s ) / ( abs ` %s ) ) e. RR+ )' % (AT, WT('t'), WW))],
               'rpred', '( %s -> ( ( U ^c %s ) / ( abs ` %s ) ) e. RR )' % (AT, WT('t'), WW)),
           w.s([w.s([cxp, asrt], 'rpdivcld', '( %s -> ( ( U ^c %s ) / ( abs ` S ) ) e. RR+ )' % (AT, WT('t')))],
               'rpred', '( %s -> ( ( U ^c %s ) / ( abs ` S ) ) e. RR )' % (AT, WT('t'))),
           w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K)), w.s([k0], 'adantr', '( %s -> 0 <_ %s )' % (AT, K)), dle],
          'lemul1ad',
          '( %s -> ( ( ( U ^c %s ) / ( abs ` %s ) ) x. %s ) <_ ( ( ( U ^c %s ) / ( abs ` S ) ) x. %s ) )' % (AT, WT('t'), WW, K, WT('t'), K))
# ( ( U ^c W ) / ( abs ` S ) ) x. K = ( 1 / ( abs ` S ) ) x. ( ( U ^c W ) x. K )
alg1 = w.s([w.s([cxp], 'rpcnd', '( %s -> ( U ^c %s ) e. CC )' % (AT, WT('t'))), kct,
            w.s([asrt], 'rpcnd', '( %s -> ( abs ` S ) e. CC )' % AT),
            w.s([asrt], 'rpne0d', '( %s -> ( abs ` S ) =/= 0 )' % AT)], 'div23d',
           '( %s -> ( ( ( U ^c %s ) x. %s ) / ( abs ` S ) ) = ( ( ( U ^c %s ) / ( abs ` S ) ) x. %s ) )' % (AT, WT('t'), K, WT('t'), K))
alg2 = w.s([w.s([w.s([cxp], 'rpcnd', '( %s -> ( U ^c %s ) e. CC )' % (AT, WT('t'))), kct], 'mulcld',
                '( %s -> %s e. CC )' % (AT, HBD)),
            w.s([asrt], 'rpcnd', '( %s -> ( abs ` S ) e. CC )' % AT),
            w.s([asrt], 'rpne0d', '( %s -> ( abs ` S ) =/= 0 )' % AT)], 'divrec2d',
           '( %s -> ( %s / ( abs ` S ) ) = %s )' % (AT, HBD, HH))
alg = w.s([w.s([alg1], 'eqcomd',
               '( %s -> ( ( ( U ^c %s ) / ( abs ` S ) ) x. %s ) = ( ( ( U ^c %s ) x. %s ) / ( abs ` S ) ) )' % (AT, WT('t'), K, WT('t'), K)),
           alg2], 'eqtrd', '( %s -> ( ( ( U ^c %s ) / ( abs ` S ) ) x. %s ) = %s )' % (AT, WT('t'), K, HH))
ptw = w.s([absi2, w.s([mle, alg], 'breqtrd',
                      '( %s -> ( ( ( U ^c %s ) / ( abs ` %s ) ) x. %s ) <_ %s )' % (AT, WT('t'), WW, K, HH))],
          'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (AT, INTG, HH))
hrr = w.s([w.s([w.s([recp], 'rpred', '( %s -> %s e. RR )' % (A2, REC))], 'adantr', '( %s -> %s e. RR )' % (AT, REC)),
           w.s([w.s([cxp], 'rpred', '( %s -> ( U ^c %s ) e. RR )' % (AT, WT('t'))),
                w.s([kr], 'adantr', '( %s -> %s e. RR )' % (AT, K))], 'remulcld', '( %s -> %s e. RR )' % (AT, HBD))],
          'remulcld', '( %s -> %s e. RR )' % (AT, HH))
# the integrability of the majorant
cib = w.s([a0, w.inst('cxpaffibl')], 'syl',
          '( %s -> ( ( t e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ ( t e. %s |-> %s ) e. L^1 ) )' % (A2, X, HBD, X, X, HBD))
hoibl = w.s([cib, w.inst('simpr')], 'syl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A2, X, HBD))
hbcl = w.s([w.s([cxp], 'rpcnd', '( %s -> ( U ^c %s ) e. CC )' % (AT, WT('t'))), kct], 'mulcld',
           '( %s -> %s e. CC )' % (AT, HBD))
hibl = w.s([w.s([recp], 'rpcnd', '( %s -> %s e. CC )' % (A2, REC)), hbcl, hoibl], 'iblmulc2',
           '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A2, X, HH))
# lintle
le = w.s([ac, bc, fcn, sss, hibl, hrr, ptw], 'lintle',
         '( %s -> ( abs ` ( %s lint <. %s , %s >. ) ) <_ S. %s %s _d t )' % (A2, PK0, HA, HBB, X, HH))
# the value of the majorant integral
itgv = w.s([w.s([recp], 'rpcnd', '( %s -> %s e. CC )' % (A2, REC)), hbcl, hoibl], 'itgmulc2',
           '( %s -> ( %s x. S. %s %s _d t ) = S. %s %s _d t )' % (A2, REC, X, HBD, X, HH))
aitg = w.s([a0, w.inst('cxpaffitg')], 'syl',
           '( %s -> S. %s %s _d t = ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) )' % (A2, X, HBD, L))
w.qed([le, w.s([w.s([itgv], 'eqcomd', '( %s -> S. %s %s _d t = ( %s x. S. %s %s _d t ) )' % (A2, X, HH, REC, X, HBD)),
                w.s([aitg], 'oveq2d',
                    '( %s -> ( %s x. S. %s %s _d t ) = ( %s x. ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) ) )' % (A2, REC, X, HBD, REC, L))],
               'eqtrd', '( %s -> S. %s %s _d t = ( %s x. ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) ) )' % (A2, X, HH, REC, L))],
      'breqtrd',
      '( %s -> ( abs ` ( %s lint <. %s , %s >. ) ) <_ ( %s x. ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) ) )' % (A2, PK0, HA, HBB, REC, L))
run4(w, h=False)
