"""Sortie C0c batch 3: the affine substitution that reduces every edge of the
winding integral to one segment integral of 1 / x in the slit plane."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0c_lib import *

CS = '( C x. ( S - P ) )'; CT = '( C x. ( T - P ) )'
CPQ = '( C e. CC /\\ P e. CC )'; STC = '( S e. CC /\\ T e. CC )'
ALZ = lambda E: 'A. z e. ( S cseg T ) ( C x. ( z - P ) ) e. %s' % E

# ---- csegaffeq: the affine image of a parametrised point
w = W('csegaffeq', 'The affine image of a point of a segment, as a point of the image segment.')
A0 = '( %s /\\ %s /\\ U e. CC )' % (CPQ, STC)
cc = w.s([w.s([], 'simp1', '( %s -> %s )' % (A0, CPQ)), w.inst('simpl')], 'syl', '( %s -> C e. CC )' % A0)
pc = w.s([w.s([], 'simp1', '( %s -> %s )' % (A0, CPQ)), w.inst('simpr')], 'syl', '( %s -> P e. CC )' % A0)
sc = w.s([w.s([], 'simp2', '( %s -> %s )' % (A0, STC)), w.inst('simpl')], 'syl', '( %s -> S e. CC )' % A0)
tc = w.s([w.s([], 'simp2', '( %s -> %s )' % (A0, STC)), w.inst('simpr')], 'syl', '( %s -> T e. CC )' % A0)
uc = w.s([], 'simp3', '( %s -> U e. CC )' % A0)
spc = w.s([sc, pc], 'subcld', '( %s -> ( S - P ) e. CC )' % A0)
tpc = w.s([tc, pc], 'subcld', '( %s -> ( T - P ) e. CC )' % A0)
tsc = w.s([tc, sc], 'subcld', '( %s -> ( T - S ) e. CC )' % A0)
uts = w.s([uc, tsc], 'mulcld', '( %s -> ( U x. ( T - S ) ) e. CC )' % A0)
# ( CT - CS ) = ( C x. ( T - S ) )
d1 = w.s([w.s([cc, tpc, spc], 'subdid', '( %s -> ( C x. ( ( T - P ) - ( S - P ) ) ) = ( %s - %s ) )' % (A0, CT, CS))],
         'eqcomd', '( %s -> ( %s - %s ) = ( C x. ( ( T - P ) - ( S - P ) ) ) )' % (A0, CT, CS))
d2 = w.s([tc, sc, pc, w.inst('nnncan2')], 'syl3anc', '( %s -> ( ( T - P ) - ( S - P ) ) = ( T - S ) )' % A0)
d3 = w.s([d1, w.s([d2], 'oveq2d', '( %s -> ( C x. ( ( T - P ) - ( S - P ) ) ) = ( C x. ( T - S ) ) )' % A0)],
         'eqtrd', '( %s -> ( %s - %s ) = ( C x. ( T - S ) ) )' % (A0, CT, CS))
# U x. ( CT - CS ) = C x. ( U x. ( T - S ) )
d4 = w.s([w.s([d3], 'oveq2d', '( %s -> ( U x. ( %s - %s ) ) = ( U x. ( C x. ( T - S ) ) ) )' % (A0, CT, CS)),
          w.s([uc, cc, tsc], 'mul12d', '( %s -> ( U x. ( C x. ( T - S ) ) ) = ( C x. ( U x. ( T - S ) ) ) )' % A0)],
         'eqtrd', '( %s -> ( U x. ( %s - %s ) ) = ( C x. ( U x. ( T - S ) ) ) )' % (A0, CT, CS))
d5 = w.s([d4], 'oveq2d', '( %s -> ( %s + ( U x. ( %s - %s ) ) ) = ( %s + ( C x. ( U x. ( T - S ) ) ) ) )' % (A0, CS, CT, CS, CS))
d6 = w.s([w.s([cc, spc, uts], 'adddid', '( %s -> ( C x. ( ( S - P ) + ( U x. ( T - S ) ) ) ) = ( %s + ( C x. ( U x. ( T - S ) ) ) ) )' % (A0, CS))],
         'eqcomd', '( %s -> ( %s + ( C x. ( U x. ( T - S ) ) ) ) = ( C x. ( ( S - P ) + ( U x. ( T - S ) ) ) ) )' % (A0, CS))
d7 = w.s([w.s([sc, uts, pc, w.inst('addsub')], 'syl3anc',
              '( %s -> ( ( S + ( U x. ( T - S ) ) ) - P ) = ( ( S - P ) + ( U x. ( T - S ) ) ) )' % A0)],
         'oveq2d', '( %s -> ( C x. ( ( S + ( U x. ( T - S ) ) ) - P ) ) = ( C x. ( ( S - P ) + ( U x. ( T - S ) ) ) ) )' % A0)
w.qed([w.s([d5, d6], 'eqtrd', '( %s -> ( %s + ( U x. ( %s - %s ) ) ) = ( C x. ( ( S - P ) + ( U x. ( T - S ) ) ) ) )' % (A0, CS, CT, CS)), d7],
      'eqtr4d', '( %s -> ( %s + ( U x. ( %s - %s ) ) ) = ( C x. ( ( S + ( U x. ( T - S ) ) ) - P ) ) )' % (A0, CS, CT, CS)); run(w)

# ---- csegaffss: the affine image of a segment lies where the values lie
w = W('csegaffss', 'If the affine image of every point of a segment lies in a class, so does the whole image segment.')
A0 = '( %s /\\ %s /\\ %s )' % (CPQ, STC, ALZ('E'))
A1 = '( %s /\\ y e. ( %s cseg %s ) )' % (A0, CS, CT)
A2 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A1
cpq = w.s([], 'simp1', '( %s -> %s )' % (A0, CPQ))
stc = w.s([], 'simp2', '( %s -> %s )' % (A0, STC))
alz = w.s([], 'simp3', '( %s -> %s )' % (A0, ALZ('E')))
cc = w.s([cpq, w.inst('simpl')], 'syl', '( %s -> C e. CC )' % A0)
pc = w.s([cpq, w.inst('simpr')], 'syl', '( %s -> P e. CC )' % A0)
sc = w.s([stc, w.inst('simpl')], 'syl', '( %s -> S e. CC )' % A0)
tc = w.s([stc, w.inst('simpr')], 'syl', '( %s -> T e. CC )' % A0)
csc = w.s([cc, w.s([sc, pc], 'subcld', '( %s -> ( S - P ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, CS))
ctc = w.s([cc, w.s([tc, pc], 'subcld', '( %s -> ( T - P ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, CT))
ymem = w.s([], 'simpr', '( %s -> y e. ( %s cseg %s ) )' % (A1, CS, CT))
ex = w.s([w.s([w.s([csc], 'adantr', '( %s -> %s e. CC )' % (A1, CS)), w.s([ctc], 'adantr', '( %s -> %s e. CC )' % (A1, CT)),
               w.inst('csegel')], 'syl2anc', '( %s -> ( y e. ( %s cseg %s ) <-> E. t e. ( 0 [,] 1 ) y = %s ) )' % (A1, CS, CT, LIN(CS, CT))),
          ymem], 'mpbid', '( %s -> E. t e. ( 0 [,] 1 ) y = %s )' % (A1, LIN(CS, CT)))
# under A2: the image point is C x. ( Z - P ) with Z on the source segment
Z = LIN('S', 'T'); IMG = '( C x. ( %s - P ) )' % Z
t01 = w.s([], 'simpr', '( %s -> t e. ( 0 [,] 1 ) )' % A2)
tssc = closed(w, A2, 'unitsscn', '( 0 [,] 1 ) C_ CC')
tcn = w.s([tssc, t01], 'sseldd', '( %s -> t e. CC )' % A2)
a2cc = w.s([cc], 'ad2antrr', '( %s -> C e. CC )' % A2)
a2pc = w.s([pc], 'ad2antrr', '( %s -> P e. CC )' % A2)
a2sc = w.s([sc], 'ad2antrr', '( %s -> S e. CC )' % A2)
a2tc = w.s([tc], 'ad2antrr', '( %s -> T e. CC )' % A2)
aff = w.s([w.s([a2cc, a2pc], 'jca', '( %s -> %s )' % (A2, CPQ)), w.s([a2sc, a2tc], 'jca', '( %s -> %s )' % (A2, STC)), tcn, w.inst('csegaffeq')],
          'syl3anc', '( %s -> %s = %s )' % (A2, LIN(CS, CT), IMG))
zmem = w.s([a2sc, a2tc, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( S cseg T ) )' % (A2, Z))
sub1 = w.s([], 'oveq1', '( z = %s -> ( z - P ) = ( %s - P ) )' % (Z, Z))
sub2 = w.s([sub1], 'oveq2d', '( z = %s -> ( C x. ( z - P ) ) = %s )' % (Z, IMG))
sub = w.s([sub2], 'eleq1d', '( z = %s -> ( ( C x. ( z - P ) ) e. E <-> %s e. E ) )' % (Z, IMG))
alz2 = w.s([alz], 'ad2antrr', '( %s -> %s )' % (A2, ALZ('E')))
imem = w.s([sub, alz2, zmem], 'rspcdva', '( %s -> %s e. E )' % (A2, IMG))
lmem = w.s([aff, imem], 'eqeltrd', '( %s -> %s e. E )' % (A2, LIN(CS, CT)))
imp2 = w.s([lmem, w.inst('eleq1a')], 'syl', '( %s -> ( y = %s -> y e. E ) )' % (A2, LIN(CS, CT)))
rl = w.s([imp2], 'rexlimdva', '( %s -> ( E. t e. ( 0 [,] 1 ) y = %s -> y e. E ) )' % (A1, LIN(CS, CT)))
ym = w.s([rl, ex], 'mpd', '( %s -> y e. E )' % A1)
w.qed([w.s([ym], 'ex', '( %s -> ( y e. ( %s cseg %s ) -> y e. E ) )' % (A0, CS, CT))], 'ssrdv',
      '( %s -> ( %s cseg %s ) C_ E )' % (A0, CS, CT)); run(w)

# ---- lintaff: the affine substitution at the level of the integrand
WPZ = WP('P')
ALU = lambda E: 'A. u e. ( S cseg T ) ( C x. ( u - P ) ) e. %s' % E
CE = '( C e. CC /\\ C =/= 0 )'; PST = '( P e. CC /\\ S e. CC /\\ T e. CC )'
CC0 = '( CC \\ { 0 } )'
w = W('lintaff', 'The integral of 1 / ( z - P ) along a segment equals the integral of the reciprocal along the affine image of the segment.')
A0 = '( %s /\\ %s /\\ %s )' % (CE, PST, ALU(DD))
A1 = '( %s /\\ t e. %s )' % (A0, O01)
Z = LIN('S', 'T'); IMG = '( C x. ( %s - P ) )' % Z; L2 = LIN(CS, CT)
ce = w.s([], 'simp1', '( %s -> %s )' % (A0, CE))
pst = w.s([], 'simp2', '( %s -> %s )' % (A0, PST))
alu = w.s([], 'simp3', '( %s -> %s )' % (A0, ALU(DD)))
cc = w.s([ce, w.inst('simpl')], 'syl', '( %s -> C e. CC )' % A0)
cne = w.s([ce, w.inst('simpr')], 'syl', '( %s -> C =/= 0 )' % A0)
pc = w.s([pst, w.inst('simp1')], 'syl', '( %s -> P e. CC )' % A0)
sc = w.s([pst, w.inst('simp2')], 'syl', '( %s -> S e. CC )' % A0)
tc = w.s([pst, w.inst('simp3')], 'syl', '( %s -> T e. CC )' % A0)
csc = w.s([cc, w.s([sc, pc], 'subcld', '( %s -> ( S - P ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, CS))
ctc = w.s([cc, w.s([tc, pc], 'subcld', '( %s -> ( T - P ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, CT))
# sethood of the two mappings
cx = closed(w, A0, 'cnex', 'CC e. _V')
d1 = w.s([cx, w.inst('difexg')], 'syl', '( %s -> ( CC \\ { P } ) e. _V )' % A0)
d2 = w.s([cx, w.inst('difexg')], 'syl', '( %s -> %s e. _V )' % (A0, DD))
wpex = w.s([d1], 'mptexd', '( %s -> %s e. _V )' % (A0, WPZ))
invex = w.s([d2], 'mptexd', '( %s -> %s e. _V )' % (A0, INV))
lv1 = w.s([wpex, sc, tc, w.inst('lintval')], 'syl3anc',
          '( %s -> %s = %s )' % (A0, LINT(WPZ, 'S', 'T'), ITG(O01, '( ( %s ` %s ) x. ( T - S ) )' % (WPZ, Z))))
lv2 = w.s([invex, csc, ctc, w.inst('lintval')], 'syl3anc',
          '( %s -> %s = %s )' % (A0, LINT(INV, CS, CT), ITG(O01, '( ( %s ` %s ) x. ( %s - %s ) )' % (INV, L2, CT, CS))))
# pointwise identity of the two integrands
t01 = w.s([], 'simpr', '( %s -> t e. %s )' % (A1, O01))
ssi = closed(w, A1, 'ioossicc', '%s C_ %s' % (O01, U01))
ticc = w.s([ssi, t01], 'sseldd', '( %s -> t e. %s )' % (A1, U01))
tssc = closed(w, A1, 'unitsscn', '%s C_ CC' % U01)
tcn = w.s([tssc, ticc], 'sseldd', '( %s -> t e. CC )' % A1)
for nm, st in (('cc', cc), ('cne', cne), ('pc', pc), ('sc', sc), ('tc', tc), ('csc', csc), ('ctc', ctc), ('alu', alu)):
    globals()['r' + nm] = w.s([st], 'adantr', '( %s -> %s )' % (A1, w.lines[[l.split(':')[0] for l in w.lines].index(st)].split(' |- ( ')[1].rsplit(' )', 1)[0].split(' -> ', 1)[1]))
zmem = w.s([rsc, rtc, ticc, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( S cseg T ) )' % (A1, Z))
sub1 = w.s([], 'oveq1', '( u = %s -> ( u - P ) = ( %s - P ) )' % (Z, Z))
sub2 = w.s([sub1], 'oveq2d', '( u = %s -> ( C x. ( u - P ) ) = %s )' % (Z, IMG))
sub = w.s([sub2], 'eleq1d', '( u = %s -> ( ( C x. ( u - P ) ) e. %s <-> %s e. %s ) )' % (Z, DD, IMG, DD))
imem = w.s([sub, ralu, zmem], 'rspcdva', '( %s -> %s e. %s )' % (A1, IMG, DD))
e0 = w.s([], 'eqid', '%s = %s' % (DD, DD))
ine = w.s([imem, w.s([e0], 'logdmn0', '( %s e. %s -> %s =/= 0 )' % (IMG, DD, IMG))], 'syl', '( %s -> %s =/= 0 )' % (A1, IMG))
zc = w.s([rsc, w.s([tcn, w.s([rtc, rsc], 'subcld', '( %s -> ( T - S ) e. CC )' % A1)], 'mulcld', '( %s -> ( t x. ( T - S ) ) e. CC )' % A1)],
         'addcld', '( %s -> %s e. CC )' % (A1, Z))
zpc = w.s([zc, rpc], 'subcld', '( %s -> ( %s - P ) e. CC )' % (A1, Z))
zpne = w.s([rcc, zpc, ine], 'mulne0bbd', '( %s -> ( %s - P ) =/= 0 )' % (A1, Z))
zne = w.s([zc, rpc, zpne], 'subne0ad', '( %s -> %s =/= P )' % (A1, Z))
zmem2 = w.s([w.s([zc, zne], 'jca', '( %s -> ( %s e. CC /\\ %s =/= P ) )' % (A1, Z, Z)), w.inst('eldifsn')], 'sylibr',
            '( %s -> %s e. ( CC \\ { P } ) )' % (A1, Z))
# values of the two mappings
iv1 = w.s([], 'oveq1', '( z = %s -> ( z - P ) = ( %s - P ) )' % (Z, Z))
iv2 = w.s([iv1], 'oveq2d', '( z = %s -> ( 1 / ( z - P ) ) = ( 1 / ( %s - P ) ) )' % (Z, Z))
iv3 = w.s([], 'eqid', '%s = %s' % (WPZ, WPZ))
invc = w.s([zpc, zpne], 'reccld', '( %s -> ( 1 / ( %s - P ) ) e. CC )' % (A1, Z))
fvi1 = w.s([iv2, iv3], 'fvmptg', '( ( %s e. ( CC \\ { P } ) /\\ ( 1 / ( %s - P ) ) e. CC ) -> ( %s ` %s ) = ( 1 / ( %s - P ) ) )' % (Z, Z, WPZ, Z, Z))
wpv = w.s([zmem2, invc, fvi1], 'syl2anc', '( %s -> ( %s ` %s ) = ( 1 / ( %s - P ) ) )' % (A1, WPZ, Z, Z))
jv2 = w.s([], 'oveq2', '( x = %s -> ( 1 / x ) = ( 1 / %s ) )' % (IMG, IMG))
jv3 = w.s([], 'eqid', '%s = %s' % (INV, INV))
imgc = w.s([rcc, zpc], 'mulcld', '( %s -> %s e. CC )' % (A1, IMG))
invc2 = w.s([imgc, ine], 'reccld', '( %s -> ( 1 / %s ) e. CC )' % (A1, IMG))
aff = w.s([w.s([rcc, rpc], 'jca', '( %s -> %s )' % (A1, CPQ)), w.s([rsc, rtc], 'jca', '( %s -> %s )' % (A1, STC)), tcn, w.inst('csegaffeq')],
          'syl3anc', '( %s -> %s = %s )' % (A1, L2, IMG))
fvi2 = w.s([jv2, jv3], 'fvmptg', '( ( %s e. %s /\\ ( 1 / %s ) e. CC ) -> ( %s ` %s ) = ( 1 / %s ) )' % (IMG, DD, IMG, INV, IMG, IMG))
invv0 = w.s([imem, invc2, fvi2], 'syl2anc', '( %s -> ( %s ` %s ) = ( 1 / %s ) )' % (A1, INV, IMG, IMG))
invv = w.s([w.s([aff], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A1, INV, L2, INV, IMG)), invv0], 'eqtrd',
           '( %s -> ( %s ` %s ) = ( 1 / %s ) )' % (A1, INV, L2, IMG))
# ( CT - CS ) = ( C x. ( T - S ) )
tsc = w.s([rtc, rsc], 'subcld', '( %s -> ( T - S ) e. CC )' % A1)
spc = w.s([rsc, rpc], 'subcld', '( %s -> ( S - P ) e. CC )' % A1)
tpc = w.s([rtc, rpc], 'subcld', '( %s -> ( T - P ) e. CC )' % A1)
k1 = w.s([w.s([rcc, tpc, spc], 'subdid', '( %s -> ( C x. ( ( T - P ) - ( S - P ) ) ) = ( %s - %s ) )' % (A1, CT, CS))],
         'eqcomd', '( %s -> ( %s - %s ) = ( C x. ( ( T - P ) - ( S - P ) ) ) )' % (A1, CT, CS))
k2 = w.s([rtc, rsc, rpc, w.inst('nnncan2')], 'syl3anc', '( %s -> ( ( T - P ) - ( S - P ) ) = ( T - S ) )' % A1)
k3 = w.s([k1, w.s([k2], 'oveq2d', '( %s -> ( C x. ( ( T - P ) - ( S - P ) ) ) = ( C x. ( T - S ) ) )' % A1)], 'eqtrd',
         '( %s -> ( %s - %s ) = ( C x. ( T - S ) ) )' % (A1, CT, CS))
# the integrands agree
ctsc = w.s([rcc, tsc], 'mulcld', '( %s -> ( C x. ( T - S ) ) e. CC )' % A1)
q1 = w.s([tsc, zpc, zpne], 'divrec2d', '( %s -> ( ( T - S ) / ( %s - P ) ) = ( ( 1 / ( %s - P ) ) x. ( T - S ) ) )' % (A1, Z, Z))
q2 = w.s([ctsc, imgc, ine], 'divrec2d', '( %s -> ( ( C x. ( T - S ) ) / %s ) = ( ( 1 / %s ) x. ( C x. ( T - S ) ) ) )' % (A1, IMG, IMG))
q3 = w.s([tsc, zpc, rcc, zpne, rcne], 'divcan5d', '( %s -> ( ( C x. ( T - S ) ) / %s ) = ( ( T - S ) / ( %s - P ) ) )' % (A1, IMG, Z))
lint_lhs = '( ( %s ` %s ) x. ( T - S ) )' % (WPZ, Z)
lint_rhs = '( ( %s ` %s ) x. ( %s - %s ) )' % (INV, L2, CT, CS)
p1 = w.s([wpv], 'oveq1d', '( %s -> %s = ( ( 1 / ( %s - P ) ) x. ( T - S ) ) )' % (A1, lint_lhs, Z))
p2 = w.s([invv, k3], 'oveq12d', '( %s -> %s = ( ( 1 / %s ) x. ( C x. ( T - S ) ) ) )' % (A1, lint_rhs, IMG))
p3 = w.s([w.s([q3, q1], 'eqtrd', '( %s -> ( ( C x. ( T - S ) ) / %s ) = ( ( 1 / ( %s - P ) ) x. ( T - S ) ) )' % (A1, IMG, Z)), q2],
         'eqtr3d', '( %s -> ( ( 1 / ( %s - P ) ) x. ( T - S ) ) = ( ( 1 / %s ) x. ( C x. ( T - S ) ) ) )' % (A1, Z, IMG))
pt = w.s([w.s([p1, p3], 'eqtrd', '( %s -> %s = ( ( 1 / %s ) x. ( C x. ( T - S ) ) ) )' % (A1, lint_lhs, IMG)), p2], 'eqtr4d',
         '( %s -> %s = %s )' % (A1, lint_lhs, lint_rhs))
it = w.s([pt], 'itgeq2dv', '( %s -> %s = %s )' % (A0, ITG(O01, lint_lhs), ITG(O01, lint_rhs)))
w.qed([w.s([lv1, it], 'eqtrd', '( %s -> %s = %s )' % (A0, LINT(WPZ, 'S', 'T'), ITG(O01, lint_rhs))), lv2], 'eqtr4d',
      '( %s -> %s = %s )' % (A0, LINT(WPZ, 'S', 'T'), LINT(INV, CS, CT))); run(w)

# ---- lintlog: the edge integral as a difference of logarithms
w = W('lintlog', 'The integral of 1 / ( z - P ) along a segment whose affine image lies in the slit plane, by the principal logarithm.')
A0 = '( %s /\\ %s /\\ %s )' % (CE, PST, ALU(DD))
ce = w.s([], 'simp1', '( %s -> %s )' % (A0, CE))
pst = w.s([], 'simp2', '( %s -> %s )' % (A0, PST))
alu = w.s([], 'simp3', '( %s -> %s )' % (A0, ALU(DD)))
cc = w.s([ce, w.inst('simpl')], 'syl', '( %s -> C e. CC )' % A0)
pc = w.s([pst, w.inst('simp1')], 'syl', '( %s -> P e. CC )' % A0)
sc = w.s([pst, w.inst('simp2')], 'syl', '( %s -> S e. CC )' % A0)
tc = w.s([pst, w.inst('simp3')], 'syl', '( %s -> T e. CC )' % A0)
csc = w.s([cc, w.s([sc, pc], 'subcld', '( %s -> ( S - P ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, CS))
ctc = w.s([cc, w.s([tc, pc], 'subcld', '( %s -> ( T - P ) e. CC )' % A0)], 'mulcld', '( %s -> %s e. CC )' % (A0, CT))
ss = w.s([w.s([cc, pc], 'jca', '( %s -> %s )' % (A0, CPQ)), w.s([sc, tc], 'jca', '( %s -> %s )' % (A0, STC)), alu, w.inst('csegaffss')],
         'syl3anc', '( %s -> ( %s cseg %s ) C_ %s )' % (A0, CS, CT, DD))
rec = w.s([w.s([w.s([csc, ctc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, CS, CT)), ss], 'jca',
               '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (A0, CS, CT, CS, CT, DD)), w.inst('lintrec')], 'syl',
          '( %s -> %s = ( %s - %s ) )' % (A0, LINT(INV, CS, CT), LOG(CT), LOG(CS)))
af = w.s([w.inst('lintaff')] + [], 'syl', '') if False else None
w.qed([w.s([ce, pst, alu, w.inst('lintaff')], 'syl3anc', '( %s -> %s = %s )' % (A0, LINT(WPZ, 'S', 'T'), LINT(INV, CS, CT))), rec],
      'eqtrd', '( %s -> %s = ( %s - %s ) )' % (A0, LINT(WPZ, 'S', 'T'), LOG(CT), LOG(CS))); run(w)


def logcor(label, desc, HYP, Cv, cne_lab, valS, valT, mkeq):
    """lintlog at a fixed unit C: HYP(x) the per-point hypothesis in the variable x."""
    w = W(label, desc)
    A0 = '( %s /\\ A. u e. ( S cseg T ) %s )' % (PST, HYP('u'))
    A1 = '( %s /\\ v e. ( S cseg T ) )' % A0
    pst = w.s([], 'simpl', '( %s -> %s )' % (A0, PST))
    alu = w.s([], 'simpr', '( %s -> A. u e. ( S cseg T ) %s )' % (A0, HYP('u')))
    pc = w.s([pst, w.inst('simp1')], 'syl', '( %s -> P e. CC )' % A0)
    sc = w.s([pst, w.inst('simp2')], 'syl', '( %s -> S e. CC )' % A0)
    tc = w.s([pst, w.inst('simp3')], 'syl', '( %s -> T e. CC )' % A0)
    cb1 = w.s([], 'oveq1' if HYP('u').startswith('( u') else 'oveq2', '( u = v -> %s = %s )' % (HYP('u').split(' e. ')[0], HYP('v').split(' e. ')[0]))
    cb2 = w.s([cb1], 'eleq1d', '( u = v -> ( %s <-> %s ) )' % (HYP('u'), HYP('v')))
    cb = w.s([cb2], 'cbvralvw', '( A. u e. ( S cseg T ) %s <-> A. v e. ( S cseg T ) %s )' % (HYP('u'), HYP('v')))
    alv = w.s([w.s([alu], 'adantr', '( %s -> A. u e. ( S cseg T ) %s )' % (A1, HYP('u'))), w.s([cb], 'a1i', '( %s -> ( A. u e. ( S cseg T ) %s <-> A. v e. ( S cseg T ) %s ) )' % (A1, HYP('u'), HYP('v')))],
              'mpbid', '( %s -> A. v e. ( S cseg T ) %s )' % (A1, HYP('v')))
    vmem = w.s([], 'simpr', '( %s -> v e. ( S cseg T ) )' % A1)
    hv = w.s([alv, vmem, w.inst('rspa')], 'syl2anc', '( %s -> %s )' % (A1, HYP('v')))
    pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
    sc1 = w.s([sc], 'adantr', '( %s -> S e. CC )' % A1)
    tc1 = w.s([tc], 'adantr', '( %s -> T e. CC )' % A1)
    ssc = w.s([sc1, tc1, w.inst('csegcl')], 'syl2anc', '( %s -> ( S cseg T ) C_ CC )' % A1)
    vc = w.s([ssc, vmem], 'sseldd', '( %s -> v e. CC )' % A1)
    eq = mkeq(w, A1, 'v', vc, pc1)
    mem = w.s([eq, hv], 'eqeltrd', '( %s -> ( %s x. ( v - P ) ) e. %s )' % (A1, Cv, DD))
    rl = w.s([mem], 'ralrimiva', '( %s -> A. v e. ( S cseg T ) ( %s x. ( v - P ) ) e. %s )' % (A0, Cv, DD))
    cec = closed(w, A0, cne_lab[0], '%s e. CC' % Cv)
    cen = closed(w, A0, cne_lab[1], '%s =/= 0' % Cv)
    ll = w.s([w.s([cec, cen], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (A0, Cv, Cv)), pst, rl, w.inst('lintlog')], 'syl3anc',
             '( %s -> %s = ( %s - %s ) )' % (A0, LINT(WPZ, 'S', 'T'), LOG('( %s x. ( T - P ) )' % Cv), LOG('( %s x. ( S - P ) )' % Cv)))
    et = mkeq(w, A0, 'T', tc, pc); es = mkeq(w, A0, 'S', sc, pc)
    rw = w.s([w.s([et], 'fveq2d', '( %s -> %s = %s )' % (A0, LOG('( %s x. ( T - P ) )' % Cv), LOG(valT))),
              w.s([es], 'fveq2d', '( %s -> %s = %s )' % (A0, LOG('( %s x. ( S - P ) )' % Cv), LOG(valS)))],
             'oveq12d', '( %s -> ( %s - %s ) = ( %s - %s ) )' % (A0, LOG('( %s x. ( T - P ) )' % Cv), LOG('( %s x. ( S - P ) )' % Cv), LOG(valT), LOG(valS)))
    w.qed([ll, rw], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (A0, LINT(WPZ, 'S', 'T'), LOG(valT), LOG(valS))); run(w)


def eq1(w, ante, X, xc, pc):
    xp = w.s([xc, pc], 'subcld', '( %s -> ( %s - P ) e. CC )' % (ante, X))
    return w.s([xp, w.inst('mullid')], 'syl', '( %s -> ( 1 x. ( %s - P ) ) = ( %s - P ) )' % (ante, X, X))


def eqm1(w, ante, X, xc, pc):
    xp = w.s([xc, pc], 'subcld', '( %s -> ( %s - P ) e. CC )' % (ante, X))
    a = w.s([xp, w.inst('mulm1')], 'syl', '( %s -> ( -u 1 x. ( %s - P ) ) = -u ( %s - P ) )' % (ante, X, X))
    b = w.s([xc, pc, w.inst('negsubdi2')], 'syl2anc', '( %s -> -u ( %s - P ) = ( P - %s ) )' % (ante, X, X))
    return w.s([a, b], 'eqtrd', '( %s -> ( -u 1 x. ( %s - P ) ) = ( P - %s ) )' % (ante, X, X))


logcor('lintlog1', 'The integral of 1 / ( z - P ) along a segment with z - P in the slit plane.',
       lambda x: '( %s - P ) e. %s' % (x, DD), '1', ('ax-1cn', 'ax-1ne0'), '( S - P )', '( T - P )', eq1)
logcor('lintlog2', 'The integral of 1 / ( z - P ) along a segment with P - z in the slit plane.',
       lambda x: '( P - %s ) e. %s' % (x, DD), '-u 1', ('neg1cn', 'neg1ne0'), '( P - S )', '( P - T )', eqm1)
