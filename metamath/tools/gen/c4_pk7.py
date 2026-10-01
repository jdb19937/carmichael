"""C4, Perron block 7: the affine exponential integral over the unit parameter."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from c4_lib import *

X = '( 0 (,) 1 )'
XC = '( 0 [,] 1 )'
K = '( Q - P )'
L = '( log ` U )'
TOP = '( TopOpen ` CCfld )'
JR = '( %s |`t RR )' % TOP


def WT(t):
    return '( P + ( %s x. %s ) )' % (t, K)


A0 = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( P e. RR /\\ Q e. RR ) )'

w = W('cxpaffdv', 'The derivative of ` ( U ^c ( P + t ( Q - P ) ) ) / ( log ` U ) ` in '
      'the unit parameter is ` ( U ^c ( P + t ( Q - P ) ) ) ( Q - P ) `: the '
      'primitive of the horizontal-edge majorant of Perron\'s contour.')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0)
une = w.s([], 'simplr', '( %s -> U =/= 1 )' % A0)
pr = w.s([], 'simprl', '( %s -> P e. RR )' % A0)
qr = w.s([], 'simprr', '( %s -> Q e. RR )' % A0)
kr = w.s([qr, pr], 'resubcld', '( %s -> %s e. RR )' % (A0, K))
kc = w.s([kr], 'recnd', '( %s -> %s e. CC )' % (A0, K))
pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A0)
lr = w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0, L))
lc = w.s([lr], 'recnd', '( %s -> %s e. CC )' % (A0, L))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0)
u0 = w.s([urp], 'rpne0d', '( %s -> U =/= 0 )' % A0)
# log U =/= 0
lne = w.s([urp, une, w.inst('logne0')], 'syl2anc', '( %s -> %s =/= 0 )' % (A0, L))
# the open interval is open in the subspace topology on RR
jeq = w.s([w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)], 'eqcomi', '%s = ( topGen ` ran (,) )' % JR)
w.lines.pop()
jeq = w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)
xopn = w.s([w.s([w.s([], 'iooretop', '%s e. ( topGen ` ran (,) )' % X)], 'a1i',
                '( %s -> %s e. ( topGen ` ran (,) ) )' % (A0, X)),
            w.s([jeq], 'a1i', '( %s -> ( topGen ` ran (,) ) = %s )' % (A0, JR))], 'eleqtrd',
           '( %s -> %s e. %s )' % (A0, X, JR))
jeq2 = w.s([jeq], 'eqcomi', '%s = ( topGen ` ran (,) )' % JR)
w.lines.pop()
jform = w.s([], 'eqid', '%s = %s' % (JR, JR))
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
sr = w.s([w.s([], 'prid1', 'RR e. { RR , CC }')], 'a1i', '( %s -> RR e. { RR , CC } )' % A0)
xss = w.s([w.s([], 'ioossre', '%s C_ RR' % X)], 'a1i', '( %s -> %s C_ RR )' % (A0, X))
# the derivative of t on X
dvi = w.s([sr], 'dvmptid', '( %s -> ( RR _D ( t e. RR |-> t ) ) = ( t e. RR |-> 1 ) )' % A0)
AT = '( %s /\\ t e. %s )' % (A0, X)
tr = w.s([w.s([xss], 'adantr', '( %s -> %s C_ RR )' % (AT, X)), w.s([], 'simpr', '( %s -> t e. %s )' % (AT, X))],
         'sseldd', '( %s -> t e. RR )' % AT)
tc = w.s([tr], 'recnd', '( %s -> t e. CC )' % AT)
one = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % AT)
zc = w.s([w.s([], '0cn', '0 e. CC')], 'a1i', '( %s -> 0 e. CC )' % AT)
ARR = '( %s /\\ t e. RR )' % A0
trr = w.s([], 'simpr', '( %s -> t e. RR )' % ARR)
tcr = w.s([trr], 'recnd', '( %s -> t e. CC )' % ARR)
oner = w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % ARR)
zcr = w.s([w.s([], '0cn', '0 e. CC')], 'a1i', '( %s -> 0 e. CC )' % ARR)
kcr = w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ARR, K))
pcr = w.s([pc], 'adantr', '( %s -> P e. CC )' % ARR)
lcr = w.s([lc], 'adantr', '( %s -> %s e. CC )' % (ARR, L))
dvi2 = w.s([sr, tcr, oner, dvi, xss, jform, keq, xopn], 'dvmptres',
           '( %s -> ( RR _D ( t e. %s |-> t ) ) = ( t e. %s |-> 1 ) )' % (A0, X, X))
# the derivative of the constant K on X
dvk = w.s([sr, kc], 'dvmptc', '( %s -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> 0 ) )' % (A0, K))
kcd = w.s([kc], 'adantr', '( %s -> %s e. CC )' % (AT, K))
dvk2 = w.s([sr, kcr, zcr, dvk, xss, jform, keq, xopn], 'dvmptres',
           '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> 0 ) )' % (A0, X, K, X))
# the product t x. K
dvtk = w.s([sr, tc, one, dvi2, kcd, zc, dvk2], 'dvmptmul',
           '( %s -> ( RR _D ( t e. %s |-> ( t x. %s ) ) ) = ( t e. %s |-> ( ( 1 x. %s ) + ( 0 x. t ) ) ) )' % (A0, X, K, X, K))
b1 = w.s([w.s([kcd], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (AT, K, K)),
          w.s([tc], 'mul02d', '( %s -> ( 0 x. t ) = 0 )' % AT)], 'oveq12d',
         '( %s -> ( ( 1 x. %s ) + ( 0 x. t ) ) = ( %s + 0 ) )' % (AT, K, K))
b2 = w.s([b1, w.s([kcd], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (AT, K, K))], 'eqtrd',
         '( %s -> ( ( 1 x. %s ) + ( 0 x. t ) ) = %s )' % (AT, K, K))
dvtk2 = w.s([dvtk, w.s([b2], 'mpteq2dva',
                       '( %s -> ( t e. %s |-> ( ( 1 x. %s ) + ( 0 x. t ) ) ) = ( t e. %s |-> %s ) )' % (A0, X, K, X, K))],
            'eqtrd', '( %s -> ( RR _D ( t e. %s |-> ( t x. %s ) ) ) = ( t e. %s |-> %s ) )' % (A0, X, K, X, K))
# the sum P + ( t x. K )
pcd = w.s([pc], 'adantr', '( %s -> P e. CC )' % AT)
dvp = w.s([sr, pc], 'dvmptc', '( %s -> ( RR _D ( t e. RR |-> P ) ) = ( t e. RR |-> 0 ) )' % A0)
dvp2 = w.s([sr, pcr, zcr, dvp, xss, jform, keq, xopn], 'dvmptres',
           '( %s -> ( RR _D ( t e. %s |-> P ) ) = ( t e. %s |-> 0 ) )' % (A0, X, X))
tkc = w.s([tc, kcd], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (AT, K))
dvw = w.s([sr, pcd, zc, dvp2, tkc, kcd, dvtk2], 'dvmptadd',
          '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> ( 0 + %s ) ) )' % (A0, X, WT('t'), X, K))
dvw2 = w.s([dvw, w.s([w.s([kcd], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (AT, K, K))], 'mpteq2dva',
                     '( %s -> ( t e. %s |-> ( 0 + %s ) ) = ( t e. %s |-> %s ) )' % (A0, X, K, X, K))],
           'eqtrd', '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> %s ) )' % (A0, X, WT('t'), X, K))
# the product with the constant log U
wc = w.s([pcd, tkc], 'addcld', '( %s -> %s e. CC )' % (AT, WT('t')))
lcd = w.s([lc], 'adantr', '( %s -> %s e. CC )' % (AT, L))
dvl = w.s([sr, lc], 'dvmptc', '( %s -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> 0 ) )' % (A0, L))
dvl2 = w.s([sr, lcr, zcr, dvl, xss, jform, keq, xopn], 'dvmptres',
           '( %s -> ( RR _D ( t e. %s |-> %s ) ) = ( t e. %s |-> 0 ) )' % (A0, X, L, X))
dvwl = w.s([sr, wc, kcd, dvw2, lcd, zc, dvl2], 'dvmptmul',
           '( %s -> ( RR _D ( t e. %s |-> ( %s x. %s ) ) ) = ( t e. %s |-> ( ( %s x. %s ) + ( 0 x. %s ) ) ) )' % (A0, X, WT('t'), L, X, K, L, WT('t')))
c1 = w.s([w.s([wc], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (AT, WT('t')))], 'oveq2d',
         '( %s -> ( ( %s x. %s ) + ( 0 x. %s ) ) = ( ( %s x. %s ) + 0 ) )' % (AT, K, L, WT('t'), K, L))
c2 = w.s([c1, w.s([w.s([kcd, lcd], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (AT, K, L))], 'addridd',
                  '( %s -> ( ( %s x. %s ) + 0 ) = ( %s x. %s ) )' % (AT, K, L, K, L))], 'eqtrd',
         '( %s -> ( ( %s x. %s ) + ( 0 x. %s ) ) = ( %s x. %s ) )' % (AT, K, L, WT('t'), K, L))
dvwl2 = w.s([dvwl, w.s([c2], 'mpteq2dva',
                       '( %s -> ( t e. %s |-> ( ( %s x. %s ) + ( 0 x. %s ) ) ) = ( t e. %s |-> ( %s x. %s ) ) )' % (A0, X, K, L, WT('t'), X, K, L))],
            'eqtrd', '( %s -> ( RR _D ( t e. %s |-> ( %s x. %s ) ) ) = ( t e. %s |-> ( %s x. %s ) ) )' % (A0, X, WT('t'), L, X, K, L))
# the exponential as a mapping and its derivative
AY = '( %s /\\ y e. CC )' % A0
efy = w.s([w.s([w.s([], 'eff', 'exp : CC --> CC')], 'a1i', '( %s -> exp : CC --> CC )' % A0)], 'feqmptd',
          '( %s -> exp = ( y e. CC |-> ( exp ` y ) ) )' % A0)
dve = w.s([w.s([w.s([], 'dvef', '( CC _D exp ) = exp')], 'a1i', '( %s -> ( CC _D exp ) = exp )' % A0)], 'id',
          '( %s -> ( CC _D exp ) = exp )' % A0)
w.lines.pop()
dve = w.s([w.s([], 'dvef', '( CC _D exp ) = exp')], 'a1i', '( %s -> ( CC _D exp ) = exp )' % A0)
dvey = w.s([w.s([w.s([efy], 'oveq2d', '( %s -> ( CC _D exp ) = ( CC _D ( y e. CC |-> ( exp ` y ) ) ) )' % A0)], 'eqcomd',
                '( %s -> ( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( CC _D exp ) )' % A0),
            w.s([dve, efy], 'eqtrd', '( %s -> ( CC _D exp ) = ( y e. CC |-> ( exp ` y ) ) )' % A0)], 'eqtrd',
           '( %s -> ( CC _D ( y e. CC |-> ( exp ` y ) ) ) = ( y e. CC |-> ( exp ` y ) ) )' % A0)
scc = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
efcl = w.s([w.s([], 'simpr', '( %s -> y e. CC )' % AY), w.inst('efcld')], 'syl', '( %s -> ( exp ` y ) e. CC )' % AY)
wlc = w.s([wc, lcd], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (AT, WT('t'), L))
klc = w.s([kcd, lcd], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (AT, K, L))
se = w.s([], 'fveq2', '( y = ( %s x. %s ) -> ( exp ` y ) = ( exp ` ( %s x. %s ) ) )' % (WT('t'), L, WT('t'), L))
co = w.s([sr, scc, wlc, klc, efcl, efcl, dvwl2, dvey, se, se], 'dvmptco',
         '( %s -> ( RR _D ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) ) = ( t e. %s |-> ( ( exp ` ( %s x. %s ) ) x. ( %s x. %s ) ) ) )' % (A0, X, WT('t'), L, X, WT('t'), L, K, L))
# ( exp ` ( W x. log U ) ) = ( U ^c W )
ucd = w.s([uc], 'adantr', '( %s -> U e. CC )' % AT)
u0d = w.s([u0], 'adantr', '( %s -> U =/= 0 )' % AT)
cef = w.s([ucd, u0d, wc, w.inst('cxpef')], 'syl3anc',
          '( %s -> ( U ^c %s ) = ( exp ` ( %s x. %s ) ) )' % (AT, WT('t'), WT('t'), L))
cefr = w.s([cef], 'eqcomd', '( %s -> ( exp ` ( %s x. %s ) ) = ( U ^c %s ) )' % (AT, WT('t'), L, WT('t')))
lhsm = w.s([cefr], 'mpteq2dva',
           '( %s -> ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) = ( t e. %s |-> ( U ^c %s ) ) )' % (A0, X, WT('t'), L, X, WT('t')))
rhsm = w.s([w.s([cefr], 'oveq1d',
                '( %s -> ( ( exp ` ( %s x. %s ) ) x. ( %s x. %s ) ) = ( ( U ^c %s ) x. ( %s x. %s ) ) )' % (AT, WT('t'), L, K, L, WT('t'), K, L))],
           'mpteq2dva',
           '( %s -> ( t e. %s |-> ( ( exp ` ( %s x. %s ) ) x. ( %s x. %s ) ) ) = ( t e. %s |-> ( ( U ^c %s ) x. ( %s x. %s ) ) ) )' % (A0, X, WT('t'), L, K, L, X, WT('t'), K, L))
co2 = w.s([w.s([w.s([lhsm], 'oveq2d',
                    '( %s -> ( RR _D ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) ) = ( RR _D ( t e. %s |-> ( U ^c %s ) ) ) )' % (A0, X, WT('t'), L, X, WT('t')))], 'eqcomd',
               '( %s -> ( RR _D ( t e. %s |-> ( U ^c %s ) ) ) = ( RR _D ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) ) )' % (A0, X, WT('t'), X, WT('t'), L)),
           w.s([co, rhsm], 'eqtrd',
               '( %s -> ( RR _D ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) ) = ( t e. %s |-> ( ( U ^c %s ) x. ( %s x. %s ) ) ) )' % (A0, X, WT('t'), L, X, WT('t'), K, L))],
          'eqtrd', '( %s -> ( RR _D ( t e. %s |-> ( U ^c %s ) ) ) = ( t e. %s |-> ( ( U ^c %s ) x. ( %s x. %s ) ) ) )' % (A0, X, WT('t'), X, WT('t'), K, L))
# divide by log U
cxc = w.s([ucd, wc], 'cxpcld', '( %s -> ( U ^c %s ) e. CC )' % (AT, WT('t')))
prc = w.s([cxc, klc], 'mulcld', '( %s -> ( ( U ^c %s ) x. ( %s x. %s ) ) e. CC )' % (AT, WT('t'), K, L))
dc = w.s([sr, cxc, prc, co2, lc, lne], 'dvmptdivc',
         '( %s -> ( RR _D ( t e. %s |-> ( ( U ^c %s ) / %s ) ) ) = ( t e. %s |-> ( ( ( U ^c %s ) x. ( %s x. %s ) ) / %s ) ) )' % (A0, X, WT('t'), L, X, WT('t'), K, L, L))
# ( ( A x. ( K x. L ) ) / L ) = ( A x. K )
as1 = w.s([cxc, kcd, lcd], 'mulassd',
          '( %s -> ( ( ( U ^c %s ) x. %s ) x. %s ) = ( ( U ^c %s ) x. ( %s x. %s ) ) )' % (AT, WT('t'), K, L, WT('t'), K, L))
cn1 = w.s([w.s([cxc, kcd], 'mulcld', '( %s -> ( ( U ^c %s ) x. %s ) e. CC )' % (AT, WT('t'), K)), lcd,
           w.s([lne], 'adantr', '( %s -> %s =/= 0 )' % (AT, L))], 'divcan4d',
          '( %s -> ( ( ( ( U ^c %s ) x. %s ) x. %s ) / %s ) = ( ( U ^c %s ) x. %s ) )' % (AT, WT('t'), K, L, L, WT('t'), K))
bod = w.s([w.s([w.s([as1], 'eqcomd',
                    '( %s -> ( ( U ^c %s ) x. ( %s x. %s ) ) = ( ( ( U ^c %s ) x. %s ) x. %s ) )' % (AT, WT('t'), K, L, WT('t'), K, L))], 'oveq1d',
               '( %s -> ( ( ( U ^c %s ) x. ( %s x. %s ) ) / %s ) = ( ( ( ( U ^c %s ) x. %s ) x. %s ) / %s ) )' % (AT, WT('t'), K, L, L, WT('t'), K, L, L)),
           cn1], 'eqtrd',
          '( %s -> ( ( ( U ^c %s ) x. ( %s x. %s ) ) / %s ) = ( ( U ^c %s ) x. %s ) )' % (AT, WT('t'), K, L, L, WT('t'), K))
w.qed([dc, w.s([bod], 'mpteq2dva',
               '( %s -> ( t e. %s |-> ( ( ( U ^c %s ) x. ( %s x. %s ) ) / %s ) ) = ( t e. %s |-> ( ( U ^c %s ) x. %s ) ) )' % (A0, X, WT('t'), K, L, L, X, WT('t'), K))],
      'eqtrd', '( %s -> ( RR _D ( t e. %s |-> ( ( U ^c %s ) / %s ) ) ) = ( t e. %s |-> ( ( U ^c %s ) x. %s ) ) )' % (A0, X, WT('t'), L, X, WT('t'), K))
run4(w)

# ---------------------------------------------------------------- cxpaffcn
HB = '( ( U ^c %s ) x. %s )' % (WT('t'), K)
GPC = '( t e. %s |-> ( ( U ^c %s ) / %s ) )' % (XC, WT('t'), L)
GPO = '( t e. %s |-> ( ( U ^c %s ) / %s ) )' % (X, WT('t'), L)
HC = '( t e. %s |-> %s )' % (XC, HB)
HO = '( t e. %s |-> %s )' % (X, HB)
A0C = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( P e. RR /\\ Q e. RR ) )'
w = W('cxpaffcn', 'The affine exponential and its multiple are continuous on the '
      'closed unit parameter interval.')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0C)
une = w.s([], 'simplr', '( %s -> U =/= 1 )' % A0C)
pr = w.s([], 'simprl', '( %s -> P e. RR )' % A0C)
qr = w.s([], 'simprr', '( %s -> Q e. RR )' % A0C)
kc = w.s([w.s([qr, pr], 'resubcld', '( %s -> %s e. RR )' % (A0C, K))], 'recnd', '( %s -> %s e. CC )' % (A0C, K))
pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A0C)
lc = w.s([w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0C, L))], 'recnd', '( %s -> %s e. CC )' % (A0C, L))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0C)
u0 = w.s([urp], 'rpne0d', '( %s -> U =/= 0 )' % A0C)
ussr = w.s([w.s([], 'unitssre', '%s C_ RR' % XC)], 'a1i', '( %s -> %s C_ RR )' % (A0C, XC))
usscn = w.s([ussr, w.s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', '( %s -> RR C_ CC )' % A0C)], 'sstrd',
            '( %s -> %s C_ CC )' % (A0C, XC))
sscc = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0C)
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( t e. %s |-> t ) e. ( %s -cn-> CC ) )' % (A0C, XC, XC))
kcst = w.s([kc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, K, XC))
pcst = w.s([pc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> P ) e. ( %s -cn-> CC ) )' % (A0C, XC, XC))
lcst = w.s([lc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, L, XC))
mul1 = w.s([idc, kcst], 'mulcncf', '( %s -> ( t e. %s |-> ( t x. %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, K, XC))
add1 = w.s([pcst, mul1], 'addcncf', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), XC))
mul2 = w.s([add1, lcst], 'mulcncf', '( %s -> ( t e. %s |-> ( %s x. %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), L, XC))
efc = w.s([w.s([], 'efcn', 'exp e. ( CC -cn-> CC )')], 'a1i', '( %s -> exp e. ( CC -cn-> CC ) )' % A0C)
cmp = w.s([efc, mul2], 'cncfmpt1f', '( %s -> ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), L, XC))
ATC = '( %s /\\ t e. %s )' % (A0C, XC)
tcc = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (ATC, XC))],
          'sseldd', '( %s -> t e. RR )' % ATC)
tcn = w.s([tcc], 'recnd', '( %s -> t e. CC )' % ATC)
wcc = w.s([w.s([pc], 'adantr', '( %s -> P e. CC )' % ATC),
           w.s([tcn, w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ATC, K))], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (ATC, K))],
          'addcld', '( %s -> %s e. CC )' % (ATC, WT('t')))
cef = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % ATC), w.s([u0], 'adantr', '( %s -> U =/= 0 )' % ATC), wcc,
           w.inst('cxpef')], 'syl3anc', '( %s -> ( U ^c %s ) = ( exp ` ( %s x. %s ) ) )' % (ATC, WT('t'), WT('t'), L))
mpe = w.s([cef], 'mpteq2dva', '( %s -> ( t e. %s |-> ( U ^c %s ) ) = ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) )' % (A0C, XC, WT('t'), XC, WT('t'), L))
cxcn = w.s([mpe, cmp], 'eqeltrd', '( %s -> ( t e. %s |-> ( U ^c %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), XC))
w.qed([cxcn, kcst], 'mulcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, HC, XC))
run4(w)

# ---------------------------------------------------------------- cxpaffcnb
HB = '( ( U ^c %s ) x. %s )' % (WT('t'), K)
GPC = '( t e. %s |-> ( ( U ^c %s ) / %s ) )' % (XC, WT('t'), L)
GPO = '( t e. %s |-> ( ( U ^c %s ) / %s ) )' % (X, WT('t'), L)
HC = '( t e. %s |-> %s )' % (XC, HB)
HO = '( t e. %s |-> %s )' % (X, HB)
A0C = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( P e. RR /\\ Q e. RR ) )'
w = W('cxpaffcnb', 'The affine exponential is continuous on the closed unit '
      'parameter interval.')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0C)
une = w.s([], 'simplr', '( %s -> U =/= 1 )' % A0C)
pr = w.s([], 'simprl', '( %s -> P e. RR )' % A0C)
qr = w.s([], 'simprr', '( %s -> Q e. RR )' % A0C)
kc = w.s([w.s([qr, pr], 'resubcld', '( %s -> %s e. RR )' % (A0C, K))], 'recnd', '( %s -> %s e. CC )' % (A0C, K))
pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A0C)
lc = w.s([w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0C, L))], 'recnd', '( %s -> %s e. CC )' % (A0C, L))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0C)
u0 = w.s([urp], 'rpne0d', '( %s -> U =/= 0 )' % A0C)
ussr = w.s([w.s([], 'unitssre', '%s C_ RR' % XC)], 'a1i', '( %s -> %s C_ RR )' % (A0C, XC))
usscn = w.s([ussr, w.s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', '( %s -> RR C_ CC )' % A0C)], 'sstrd',
            '( %s -> %s C_ CC )' % (A0C, XC))
sscc = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0C)
idc = w.s([usscn, sscc, w.inst('cncfmptid')], 'syl2anc', '( %s -> ( t e. %s |-> t ) e. ( %s -cn-> CC ) )' % (A0C, XC, XC))
kcst = w.s([kc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, K, XC))
pcst = w.s([pc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> P ) e. ( %s -cn-> CC ) )' % (A0C, XC, XC))
lcst = w.s([lc, usscn, sscc, w.inst('cncfmptc')], 'syl3anc', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, L, XC))
mul1 = w.s([idc, kcst], 'mulcncf', '( %s -> ( t e. %s |-> ( t x. %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, K, XC))
add1 = w.s([pcst, mul1], 'addcncf', '( %s -> ( t e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), XC))
mul2 = w.s([add1, lcst], 'mulcncf', '( %s -> ( t e. %s |-> ( %s x. %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), L, XC))
efc = w.s([w.s([], 'efcn', 'exp e. ( CC -cn-> CC )')], 'a1i', '( %s -> exp e. ( CC -cn-> CC ) )' % A0C)
cmp = w.s([efc, mul2], 'cncfmpt1f', '( %s -> ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), L, XC))
ATC = '( %s /\\ t e. %s )' % (A0C, XC)
tcc = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (ATC, XC))],
          'sseldd', '( %s -> t e. RR )' % ATC)
tcn = w.s([tcc], 'recnd', '( %s -> t e. CC )' % ATC)
wcc = w.s([w.s([pc], 'adantr', '( %s -> P e. CC )' % ATC),
           w.s([tcn, w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ATC, K))], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (ATC, K))],
          'addcld', '( %s -> %s e. CC )' % (ATC, WT('t')))
cef = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % ATC), w.s([u0], 'adantr', '( %s -> U =/= 0 )' % ATC), wcc,
           w.inst('cxpef')], 'syl3anc', '( %s -> ( U ^c %s ) = ( exp ` ( %s x. %s ) ) )' % (ATC, WT('t'), WT('t'), L))
mpe = w.s([cef], 'mpteq2dva', '( %s -> ( t e. %s |-> ( U ^c %s ) ) = ( t e. %s |-> ( exp ` ( %s x. %s ) ) ) )' % (A0C, XC, WT('t'), XC, WT('t'), L))
w.qed([mpe, cmp], 'eqeltrd', '( %s -> ( t e. %s |-> ( U ^c %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), XC))
run4(w)

# ---------------------------------------------------------------- cxpaffitg
w = W('cxpaffitg', 'The affine exponential integral over the unit parameter: the '
      'horizontal-edge integral of Perron\'s contour, ` integral_const_rpow ` of '
      'Route Z\'s PerronKernel.lean in the parametrised form ~ lintval produces.')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0C)
une = w.s([], 'simplr', '( %s -> U =/= 1 )' % A0C)
pr = w.s([], 'simprl', '( %s -> P e. RR )' % A0C)
qr = w.s([], 'simprr', '( %s -> Q e. RR )' % A0C)
krr = w.s([qr, pr], 'resubcld', '( %s -> %s e. RR )' % (A0C, K))
kc = w.s([krr], 'recnd', '( %s -> %s e. CC )' % (A0C, K))
pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A0C)
qc = w.s([qr], 'recnd', '( %s -> Q e. CC )' % A0C)
lr = w.s([urp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A0C, L))
lc = w.s([lr], 'recnd', '( %s -> %s e. CC )' % (A0C, L))
lne = w.s([urp, une, w.inst('logne0')], 'syl2anc', '( %s -> %s =/= 0 )' % (A0C, L))
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0C)
r0 = w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0C)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0C)
le01 = w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % A0C)
ussr = w.s([w.s([], 'unitssre', '%s C_ RR' % XC)], 'a1i', '( %s -> %s C_ RR )' % (A0C, XC))
usscn = w.s([ussr, w.s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', '( %s -> RR C_ CC )' % A0C)], 'sstrd',
            '( %s -> %s C_ CC )' % (A0C, XC))
# the closures on the closed interval
ATC = '( %s /\\ t e. %s )' % (A0C, XC)
tcc = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (ATC, XC))],
          'sseldd', '( %s -> t e. RR )' % ATC)
tcn = w.s([tcc], 'recnd', '( %s -> t e. CC )' % ATC)
wcc = w.s([w.s([pc], 'adantr', '( %s -> P e. CC )' % ATC),
           w.s([tcn, w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ATC, K))], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (ATC, K))],
          'addcld', '( %s -> %s e. CC )' % (ATC, WT('t')))
cxcc = w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % ATC), wcc], 'cxpcld', '( %s -> ( U ^c %s ) e. CC )' % (ATC, WT('t')))
hcc = w.s([cxcc, w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ATC, K))], 'mulcld', '( %s -> %s e. CC )' % (ATC, HB))
# the primitive is continuous on the closed interval
base = w.s([w.s([], 'id', '( %s -> %s )' % (A0C, A0C)), w.inst('cxpaffcnb')], 'syl',
           '( %s -> ( t e. %s |-> ( U ^c %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), XC))
recl = w.s([w.s([w.s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '( %s -> 1 e. CC )' % A0C), lc, lne], 'divcld',
                '( %s -> ( 1 / %s ) e. CC )' % (A0C, L)), usscn,
            w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0C), w.inst('cncfmptc')], 'syl3anc',
           '( %s -> ( t e. %s |-> ( 1 / %s ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, L, XC))
prodcn = w.s([base, recl], 'mulcncf',
             '( %s -> ( t e. %s |-> ( ( U ^c %s ) x. ( 1 / %s ) ) ) e. ( %s -cn-> CC ) )' % (A0C, XC, WT('t'), L, XC))
dvr = w.s([cxcc, w.s([lc], 'adantr', '( %s -> %s e. CC )' % (ATC, L)), w.s([lne], 'adantr', '( %s -> %s =/= 0 )' % (ATC, L))],
          'divrecd', '( %s -> ( ( U ^c %s ) / %s ) = ( ( U ^c %s ) x. ( 1 / %s ) ) )' % (ATC, WT('t'), L, WT('t'), L))
gpccn = w.s([w.s([dvr], 'mpteq2dva',
                 '( %s -> %s = ( t e. %s |-> ( ( U ^c %s ) x. ( 1 / %s ) ) ) )' % (A0C, GPC, XC, WT('t'), L)), prodcn],
            'eqeltrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, GPC, XC))
# the derivative of the primitive on the closed interval equals the one on the open one
jform = w.s([], 'eqid', '%s = %s' % (JR, JR))
keq = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
gcl = w.s([cxcc, w.s([lc], 'adantr', '( %s -> %s e. CC )' % (ATC, L)), w.s([lne], 'adantr', '( %s -> %s =/= 0 )' % (ATC, L))],
          'divcld', '( %s -> ( ( U ^c %s ) / %s ) e. CC )' % (ATC, WT('t'), L))
icn = w.s([w.s([r0, r1, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` %s ) = %s )' % (A0C, XC, X)),
           w.s([], 'id', 'x')], 'id', 'y')
w.lines.pop(); w.lines.pop()
icc0 = w.s([r0, r1, w.inst('iccntr')], 'syl2anc', '( %s -> ( ( int ` ( topGen ` ran (,) ) ) ` %s ) = %s )' % (A0C, XC, X))
jeq2 = w.s([w.s([], 'tgioo4', '( topGen ` ran (,) ) = %s' % JR)], 'eqcomi', '%s = ( topGen ` ran (,) )' % JR)
icc = w.s([w.s([w.s([jeq2], 'a1i', '( %s -> %s = ( topGen ` ran (,) ) )' % (A0C, JR))], 'fveq2d',
               '( %s -> ( int ` %s ) = ( int ` ( topGen ` ran (,) ) ) )' % (A0C, JR))], 'fveq1d',
          '( %s -> ( ( int ` %s ) ` %s ) = ( ( int ` ( topGen ` ran (,) ) ) ` %s ) )' % (A0C, JR, XC, XC))
icc2 = w.s([icc, icc0], 'eqtrd', '( %s -> ( ( int ` %s ) ` %s ) = %s )' % (A0C, JR, XC, X))
ntr = w.s([w.s([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', '( %s -> RR C_ CC )' % A0C), ussr, gcl, jform, keq, icc2],
          'dvmptntr', '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0C, GPC, GPO))
dvo = w.s([w.s([], 'id', '( %s -> %s )' % (A0C, A0C)), w.inst('cxpaffdv')], 'syl',
          '( %s -> ( RR _D %s ) = %s )' % (A0C, GPO, HO))
dvf = w.s([ntr, dvo], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0C, GPC, HO))
GPCA = '( a e. %s |-> ( ( U ^c %s ) / %s ) )' % (XC, WT('a'), L)
cbvs = w.s([w.s([w.s([w.s([], 'oveq1', '( t = a -> ( t x. %s ) = ( a x. %s ) )' % (K, K))], 'oveq2d',
                     '( t = a -> %s = %s )' % (WT('t'), WT('a')))], 'oveq2d',
                '( t = a -> ( U ^c %s ) = ( U ^c %s ) )' % (WT('t'), WT('a')))], 'oveq1d',
            '( t = a -> ( ( U ^c %s ) / %s ) = ( ( U ^c %s ) / %s ) )' % (WT('t'), L, WT('a'), L))
cbv = w.s([cbvs], 'cbvmptv', '%s = %s' % (GPC, GPCA))
cbvd = w.s([cbv], 'a1i', '( %s -> %s = %s )' % (A0C, GPC, GPCA))
dvfa = w.s([w.s([w.s([cbvd], 'eqcomd', '( %s -> %s = %s )' % (A0C, GPCA, GPC))], 'oveq2d',
                '( %s -> ( RR _D %s ) = ( RR _D %s ) )' % (A0C, GPCA, GPC)), dvf], 'eqtrd',
           '( %s -> ( RR _D %s ) = %s )' % (A0C, GPCA, HO))

# the derivative is continuous and integrable on the open interval
hccn = w.s([w.s([], 'id', '( %s -> %s )' % (A0C, A0C)), w.inst('cxpaffcn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, HC, XC))
ioss = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC))], 'a1i', '( %s -> %s C_ %s )' % (A0C, X, XC))
hocn = w.s([w.s([w.s([ioss, hccn, w.inst('rescncf')], 'mpisyl' if False else 'syl2anc', 'dummy')], 'id', 'x')], 'id', 'y')
w.lines.pop(); w.lines.pop(); w.lines.pop()
resc = w.s([ioss, w.s([hccn], 'a1d' if False else 'id', 'x')], 'id', 'y')
w.lines.pop(); w.lines.pop()
rc = w.s([w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('rescncf')], 'ax-mp',
              '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HC, XC, HC, X, X)), hccn], 'mpi' if False else 'dummy', 'x')
w.lines.pop(); w.lines.pop()
rcl = w.s([], 'rescncf', 'dummy')
w.lines.pop()
rci = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('rescncf')], 'ax-mp',
          '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HC, XC, HC, X, X))
hres = w.s([hccn, w.s([rci], 'a1i', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0C, HC, XC, HC, X, X))],
           'mpd', '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0C, HC, X, X))
rsm = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (HC, X, HO))
hocn = w.s([w.s([w.s([rsm], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A0C, HC, X, HO))], 'eqcomd',
                '( %s -> %s = ( %s |` %s ) )' % (A0C, HO, HC, X)), hres], 'eqeltrd',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, HO, X))
hcibl = w.s([r0, r1, hccn, w.inst('cniccibl')], 'syl3anc', '( %s -> %s e. L^1 )' % (A0C, HC))
hoibl = w.s([ioss, w.s([w.s([], 'ioombl', '%s e. dom vol' % X)], 'a1i', '( %s -> %s e. dom vol )' % (A0C, X)),
             hcc, hcibl], 'iblss', '( %s -> %s e. L^1 )' % (A0C, HO))
# the fundamental theorem of calculus
dcn = w.s([w.s([dvfa], 'eqcomd', '( %s -> %s = ( RR _D %s ) )' % (A0C, HO, GPCA)), hocn], 'eqeltrrd',
          '( %s -> ( RR _D %s ) e. ( %s -cn-> CC ) )' % (A0C, GPCA, X))
dib = w.s([w.s([dvfa], 'eqcomd', '( %s -> %s = ( RR _D %s ) )' % (A0C, HO, GPCA)), hoibl], 'eqeltrrd',
          '( %s -> ( RR _D %s ) e. L^1 )' % (A0C, GPCA))
gpccna = w.s([cbvd, gpccn], 'eqeltrrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, GPCA, XC))
w.lines.pop()
gpccna = w.s([w.s([cbvd], 'eqcomd', '( %s -> %s = %s )' % (A0C, GPCA, GPC)), gpccn], 'eqeltrd',
             '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, GPCA, XC))
ftc = w.s([r0, r1, le01, dcn, dib, gpccna], 'ftc2',
          '( %s -> S. %s ( ( RR _D %s ) ` t ) _d t = ( ( %s ` 1 ) - ( %s ` 0 ) ) )' % (A0C, X, GPCA, GPCA, GPCA))
# the integrand
ATO = "( %s /\\ t e. %s )" % (A0C, X)
tio = w.s([], 'simpr', '( %s -> t e. %s )' % (ATO, X))
hcl2 = w.s([w.s([], 'ovex', '%s e. _V' % HB)], 'a1i', '( %s -> %s e. _V )' % (ATO, HB))
hval = w.s([w.s([w.s([], 'eqid', '%s = %s' % (HO, HO))], 'a1i', '( %s -> %s = %s )' % (A0C, HO, HO)), hcl2],
           'fvmpt2d', '( %s -> ( %s ` t ) = %s )' % (ATO, HO, HB))
dval = w.s([w.s([w.s([dvfa], 'adantr', '( %s -> ( RR _D %s ) = %s )' % (ATO, GPCA, HO))], 'fveq1d',
                '( %s -> ( ( RR _D %s ) ` t ) = ( %s ` t ) )' % (ATO, GPCA, HO)), hval], 'eqtrd',
           '( %s -> ( ( RR _D %s ) ` t ) = %s )' % (ATO, GPCA, HB))
itg = w.s([dval], 'itgeq2dv', '( %s -> S. %s ( ( RR _D %s ) ` t ) _d t = S. %s %s _d t )' % (A0C, X, GPCA, X, HB))
# the two endpoint values
one1 = w.s([w.s([], '1elunit', '1 e. %s' % XC)], 'a1i', '( %s -> 1 e. %s )' % (A0C, XC))
zero1 = w.s([w.s([], '0elunit', '0 e. %s' % XC)], 'a1i', '( %s -> 0 e. %s )' % (A0C, XC))
sub1 = w.s([w.s([w.s([w.s([], 'oveq1', '( a = 1 -> ( a x. %s ) = ( 1 x. %s ) )' % (K, K))], 'oveq2d',
                     '( a = 1 -> %s = ( P + ( 1 x. %s ) ) )' % (WT('a'), K))], 'oveq2d',
                '( a = 1 -> ( U ^c %s ) = ( U ^c ( P + ( 1 x. %s ) ) ) )' % (WT('a'), K))], 'oveq1d',
            '( a = 1 -> ( ( U ^c %s ) / %s ) = ( ( U ^c ( P + ( 1 x. %s ) ) ) / %s ) )' % (WT('a'), L, K, L))
v1 = w.s([one1, w.s([w.s([], 'ovex', '( ( U ^c ( P + ( 1 x. %s ) ) ) / %s ) e. _V' % (K, L))], 'a1i',
                    '( %s -> ( ( U ^c ( P + ( 1 x. %s ) ) ) / %s ) e. _V )' % (A0C, K, L)),
          w.s([sub1, w.s([], 'eqid', '%s = %s' % (GPCA, GPCA))], 'fvmptg',
              '( ( 1 e. %s /\\ ( ( U ^c ( P + ( 1 x. %s ) ) ) / %s ) e. _V ) -> ( %s ` 1 ) = ( ( U ^c ( P + ( 1 x. %s ) ) ) / %s ) )' % (XC, K, L, GPCA, K, L))],
         'syl2anc', '( %s -> ( %s ` 1 ) = ( ( U ^c ( P + ( 1 x. %s ) ) ) / %s ) )' % (A0C, GPCA, K, L))
pk1 = w.s([w.s([kc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0C, K, K)),
           w.s([pc, qc], 'pncan3d', '( %s -> ( P + %s ) = Q )' % (A0C, K))], 'jca', 'dummy')
w.lines.pop()
pk1 = w.s([w.s([w.s([kc], 'mullidd', '( %s -> ( 1 x. %s ) = %s )' % (A0C, K, K))], 'oveq2d',
               '( %s -> ( P + ( 1 x. %s ) ) = ( P + %s ) )' % (A0C, K, K)),
           w.s([pc, qc], 'pncan3d', '( %s -> ( P + %s ) = Q )' % (A0C, K))], 'eqtrd',
          '( %s -> ( P + ( 1 x. %s ) ) = Q )' % (A0C, K))
v1b = w.s([v1, w.s([w.s([pk1], 'oveq2d', '( %s -> ( U ^c ( P + ( 1 x. %s ) ) ) = ( U ^c Q ) )' % (A0C, K))], 'oveq1d',
                   '( %s -> ( ( U ^c ( P + ( 1 x. %s ) ) ) / %s ) = ( ( U ^c Q ) / %s ) )' % (A0C, K, L, L))],
           'eqtrd', '( %s -> ( %s ` 1 ) = ( ( U ^c Q ) / %s ) )' % (A0C, GPCA, L))
sub0 = w.s([w.s([w.s([w.s([], 'oveq1', '( a = 0 -> ( a x. %s ) = ( 0 x. %s ) )' % (K, K))], 'oveq2d',
                     '( a = 0 -> %s = ( P + ( 0 x. %s ) ) )' % (WT('a'), K))], 'oveq2d',
                '( a = 0 -> ( U ^c %s ) = ( U ^c ( P + ( 0 x. %s ) ) ) )' % (WT('a'), K))], 'oveq1d',
            '( a = 0 -> ( ( U ^c %s ) / %s ) = ( ( U ^c ( P + ( 0 x. %s ) ) ) / %s ) )' % (WT('a'), L, K, L))
v0 = w.s([zero1, w.s([w.s([], 'ovex', '( ( U ^c ( P + ( 0 x. %s ) ) ) / %s ) e. _V' % (K, L))], 'a1i',
                     '( %s -> ( ( U ^c ( P + ( 0 x. %s ) ) ) / %s ) e. _V )' % (A0C, K, L)),
          w.s([sub0, w.s([], 'eqid', '%s = %s' % (GPCA, GPCA))], 'fvmptg',
              '( ( 0 e. %s /\\ ( ( U ^c ( P + ( 0 x. %s ) ) ) / %s ) e. _V ) -> ( %s ` 0 ) = ( ( U ^c ( P + ( 0 x. %s ) ) ) / %s ) )' % (XC, K, L, GPCA, K, L))],
         'syl2anc', '( %s -> ( %s ` 0 ) = ( ( U ^c ( P + ( 0 x. %s ) ) ) / %s ) )' % (A0C, GPCA, K, L))
pk0 = w.s([w.s([w.s([kc], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (A0C, K))], 'oveq2d',
               '( %s -> ( P + ( 0 x. %s ) ) = ( P + 0 ) )' % (A0C, K)),
           w.s([pc], 'addridd', '( %s -> ( P + 0 ) = P )' % A0C)], 'eqtrd',
          '( %s -> ( P + ( 0 x. %s ) ) = P )' % (A0C, K))
v0b = w.s([v0, w.s([w.s([pk0], 'oveq2d', '( %s -> ( U ^c ( P + ( 0 x. %s ) ) ) = ( U ^c P ) )' % (A0C, K))], 'oveq1d',
                   '( %s -> ( ( U ^c ( P + ( 0 x. %s ) ) ) / %s ) = ( ( U ^c P ) / %s ) )' % (A0C, K, L, L))],
           'eqtrd', '( %s -> ( %s ` 0 ) = ( ( U ^c P ) / %s ) )' % (A0C, GPCA, L))
cq = w.s([uc, qc], 'cxpcld', '( %s -> ( U ^c Q ) e. CC )' % A0C)
cp = w.s([uc, pc], 'cxpcld', '( %s -> ( U ^c P ) e. CC )' % A0C)
dsd = w.s([cq, cp, lc, lne], 'divsubdird',
          '( %s -> ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) = ( ( ( U ^c Q ) / %s ) - ( ( U ^c P ) / %s ) ) )' % (A0C, L, L, L))
w.qed([w.s([itg], 'eqcomd', '( %s -> S. %s %s _d t = S. %s ( ( RR _D %s ) ` t ) _d t )' % (A0C, X, HB, X, GPCA)),
       w.s([ftc, w.s([w.s([v1b, v0b], 'oveq12d',
                          '( %s -> ( ( %s ` 1 ) - ( %s ` 0 ) ) = ( ( ( U ^c Q ) / %s ) - ( ( U ^c P ) / %s ) ) )' % (A0C, GPCA, GPCA, L, L)),
                      w.s([dsd], 'eqcomd',
                          '( %s -> ( ( ( U ^c Q ) / %s ) - ( ( U ^c P ) / %s ) ) = ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) )' % (A0C, L, L, L))],
                     'eqtrd', '( %s -> ( ( %s ` 1 ) - ( %s ` 0 ) ) = ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) )' % (A0C, GPCA, GPCA, L))],
           'eqtrd', '( %s -> S. %s ( ( RR _D %s ) ` t ) _d t = ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) )' % (A0C, X, GPCA, L))],
      'eqtrd', '( %s -> S. %s %s _d t = ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) )' % (A0C, X, HB, L))
run4(w)

# ---------------------------------------------------------------- cxpaffibl
w = W('cxpaffibl', 'The affine exponential majorant is continuous and integrable on '
      'the open unit parameter interval: the two side conditions ~ lintle asks of a '
      'horizontal edge of Perron\'s contour.')
urp = w.s([], 'simpll', '( %s -> U e. RR+ )' % A0C)
pr = w.s([], 'simprl', '( %s -> P e. RR )' % A0C)
qr = w.s([], 'simprr', '( %s -> Q e. RR )' % A0C)
kc = w.s([w.s([qr, pr], 'resubcld', '( %s -> %s e. RR )' % (A0C, K))], 'recnd', '( %s -> %s e. CC )' % (A0C, K))
pc = w.s([pr], 'recnd', '( %s -> P e. CC )' % A0C)
uc = w.s([urp], 'rpcnd', '( %s -> U e. CC )' % A0C)
r0 = w.s([w.s([], '0re', '0 e. RR')], 'a1i', '( %s -> 0 e. RR )' % A0C)
r1 = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A0C)
ussr = w.s([w.s([], 'unitssre', '%s C_ RR' % XC)], 'a1i', '( %s -> %s C_ RR )' % (A0C, XC))
ATC = '( %s /\\ t e. %s )' % (A0C, XC)
tcc = w.s([w.s([ussr], 'adantr', '( %s -> %s C_ RR )' % (ATC, XC)), w.s([], 'simpr', '( %s -> t e. %s )' % (ATC, XC))],
          'sseldd', '( %s -> t e. RR )' % ATC)
tcn = w.s([tcc], 'recnd', '( %s -> t e. CC )' % ATC)
wcc = w.s([w.s([pc], 'adantr', '( %s -> P e. CC )' % ATC),
           w.s([tcn, w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ATC, K))], 'mulcld', '( %s -> ( t x. %s ) e. CC )' % (ATC, K))],
          'addcld', '( %s -> %s e. CC )' % (ATC, WT('t')))
hcc = w.s([w.s([w.s([uc], 'adantr', '( %s -> U e. CC )' % ATC), wcc], 'cxpcld',
                '( %s -> ( U ^c %s ) e. CC )' % (ATC, WT('t'))),
           w.s([kc], 'adantr', '( %s -> %s e. CC )' % (ATC, K))], 'mulcld', '( %s -> %s e. CC )' % (ATC, HB))
hccn = w.s([w.s([], 'id', '( %s -> %s )' % (A0C, A0C)), w.inst('cxpaffcn')], 'syl',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, HC, XC))
ioss = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC))], 'a1i', '( %s -> %s C_ %s )' % (A0C, X, XC))
rci = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('rescncf')], 'ax-mp',
          '( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (HC, XC, HC, X, X))
hres = w.s([hccn, w.s([rci], 'a1i', '( %s -> ( %s e. ( %s -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) ) )' % (A0C, HC, XC, HC, X, X))],
           'mpd', '( %s -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (A0C, HC, X, X))
rsm = w.s([w.s([], 'ioossicc', '%s C_ %s' % (X, XC)), w.inst('resmpt')], 'ax-mp', '( %s |` %s ) = %s' % (HC, X, HO))
hocn = w.s([w.s([w.s([rsm], 'a1i', '( %s -> ( %s |` %s ) = %s )' % (A0C, HC, X, HO))], 'eqcomd',
                '( %s -> %s = ( %s |` %s ) )' % (A0C, HO, HC, X)), hres], 'eqeltrd',
           '( %s -> %s e. ( %s -cn-> CC ) )' % (A0C, HO, X))
hcibl = w.s([r0, r1, hccn, w.inst('cniccibl')], 'syl3anc', '( %s -> %s e. L^1 )' % (A0C, HC))
hoibl = w.s([ioss, w.s([w.s([], 'ioombl', '%s e. dom vol' % X)], 'a1i', '( %s -> %s e. dom vol )' % (A0C, X)),
             hcc, hcibl], 'iblss', '( %s -> %s e. L^1 )' % (A0C, HO))
w.qed([hocn, hoibl], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. L^1 ) )' % (A0C, HO, X, HO))
run4(w)
