"""Sortie A5, batch 8: the operation count of the search against the budget
(Lean: hcost of SearchAlg.lean).
MM_DB=sorties/a5.mm python3 tools/gen/a5_cost.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from tm import *
from a2lib import WH
from cl import Closure
from lin import linarith
import num

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

X5 = '( A ^ 5 )'
SQZ = '( Nfloor ` ( sqrt ` Z ) )'
SQX = '( Nfloor ` ( sqrt ` %s ) )' % X5
LGZ = '( 2 Nlog Z )'
LP = '( # ` P )'
LS = '( # ` S )'
B1 = '( ( Z + 1 ) x. ( ( ( %s + Y ) + %s ) + 6 ) )' % (SQZ, LGZ)
B2 = '( K x. ( ( T + 2 ) + ( ( 2 ^ T ) x. ( %s + 3 ) ) ) )' % SQX
B3 = '( %s x. ( A + 3 ) )' % LP
B4 = '( %s x. ( ( %s + %s ) + 6 ) )' % (LS, SQX, LS)
CP = '( ( ( ( ( ( ( Z CostPieces Y ) ` T ) ` A ) ` %s ) ` K ) ` %s ) ` %s )' % (X5, LP, LS)
CPU = '( ( ( ( ( ( ( %s + ( 2 x. T ) ) + 2 ) + %s ) + %s ) + 1 ) + %s ) + 4 )' % (B1, B2, B3, B4)
COSTEX = '( ( ( ( ( ( ( 2nd ` R ) + T ) + T ) + 2 ) + ( 2nd ` J ) ) + ( 2nd ` X ) ) + ( 2nd ` U ) )'

w = WH('a5cost', 'The operation count of a successful search is within the budget of the paper (Lean: hcost of SearchAlg.lean).')
h1 = w.h('( Z e. NN /\\ W e. NN0 /\\ Y e. NN )')
h2 = w.h('( T e. NN0 /\\ K e. NN0 )')
h3 = w.h('R = ( ( Z Reservoir W ) ` Y )')
h4 = w.h('( A e. NN /\\ P e. Word NN0 /\\ S e. Word NN0 )')
h5 = w.h('( 2nd ` J ) <_ %s' % B2)
h6 = w.h('( 2nd ` X ) <_ ( %s + 1 )' % B3)
h7 = w.h('M e. NN0')
h8 = w.h('A. p e. ran S p <_ %s' % X5)
h9 = w.h('U = ( M Verify S )')
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)

znn = st([h1], 'simp1d', 'Z e. NN')
wn0 = st([h1], 'simp2d', 'W e. NN0')
ynn = st([h1], 'simp3d', 'Y e. NN')
tn0 = st([h2], 'simpld', 'T e. NN0')
kn0 = st([h2], 'simprd', 'K e. NN0')
ann = st([h4], 'simp1d', 'A e. NN')
pwrd = st([h4], 'simp2d', 'P e. Word NN0')
swrd = st([h4], 'simp3d', 'S e. Word NN0')
zn0 = st([znn], 'nnnn0d', 'Z e. NN0')
yn0 = st([ynn], 'nnnn0d', 'Y e. NN0')
x5n = st([ann, w.s([num.fact(w, '5', 'NN0')], 'a1i', '( ph -> 5 e. NN0 )'), w.inst('nnexpcl')], 'syl2anc',
         '%s e. NN' % X5)
x5n0 = st([x5n], 'nnnn0d', '%s e. NN0' % X5)
# the reservoir charge
r2eq = w.s([h3], 'fveq2d', '( ph -> ( 2nd ` R ) = ( 2nd ` ( ( Z Reservoir W ) ` Y ) ) )')
resc = st([r2eq, st([st([znn, wn0, ynn], '3jca', '( Z e. NN /\\ W e. NN0 /\\ Y e. NN )'), w.inst('rescost')], 'syl',
                  '( 2nd ` ( ( Z Reservoir W ) ` Y ) ) <_ %s' % B1)], 'eqbrtrd',
           '( 2nd ` R ) <_ %s' % B1)
# the verification charge
u2eq = w.s([h9], 'fveq2d', '( ph -> ( 2nd ` U ) = ( 2nd ` ( M Verify S ) ) )')
verc = st([u2eq, st([st([st([h7, x5n0, swrd], '3jca', '( M e. NN0 /\\ %s e. NN0 /\\ S e. Word NN0 )' % X5), h8], 'jca',
                       '( ( M e. NN0 /\\ %s e. NN0 /\\ S e. Word NN0 ) /\\ A. p e. ran S p <_ %s )' % (X5, X5)),
                   w.inst('verifycost')], 'syl', '( 2nd ` ( M Verify S ) ) <_ ( %s + 4 )' % B4)], 'eqbrtrd',
           '( 2nd ` U ) <_ ( %s + 4 )' % B4)
# the closures of the compound charges
sqzn = st([st([st([zn0], 'nn0red', 'Z e. RR'), st([zn0], 'nn0ge0d', '0 <_ Z'), w.inst('resqrtcl')], 'syl2anc',
              '( sqrt ` Z ) e. RR'), w.inst('nfloorcl')], 'syl', '%s e. NN0' % SQZ)
sqxn = st([st([st([x5n0], 'nn0red', '%s e. RR' % X5), st([x5n0], 'nn0ge0d', '0 <_ %s' % X5), w.inst('resqrtcl')],
              'syl2anc', '( sqrt ` %s ) e. RR' % X5), w.inst('nfloorcl')], 'syl', '%s e. NN0' % SQX)
lgzn = st([w.s([num.fact(w, '2', 'NN0')], 'a1i', '( ph -> 2 e. NN0 )'), zn0, w.inst('nlogcl')], 'syl2anc',
          '%s e. NN0' % LGZ)
lpn = st([pwrd, w.inst('lencl')], 'syl', '%s e. NN0' % LP)
lsn = st([swrd, w.inst('lencl')], 'syl', '%s e. NN0' % LS)
cls = Closure(w, 'ph', {'Z': ('NN0', zn0), 'Y': ('NN0', yn0), 'T': ('NN0', tn0),
                        'K': ('NN0', kn0), 'A': ('NN', ann)})
for txt, stp in ((SQZ, sqzn), (SQX, sqxn), (LGZ, lgzn), (LP, lpn), (LS, lsn)):
    cls.leaf(txt, 'NN0', stp)
rre = st([st([h3, st([st([st([znn, wn0], 'jca', '( Z e. NN /\\ W e. NN0 )'), ynn], 'jca',
                          '( ( Z e. NN /\\ W e. NN0 ) /\\ Y e. NN )'), w.inst('reservoircl')], 'syl',
                     '( ( Z Reservoir W ) ` Y ) e. ( Word NN0 X. NN0 )')], 'eqeltrd',
              'R e. ( Word NN0 X. NN0 )'), w.inst('xp2nd')], 'syl', '( 2nd ` R ) e. NN0')
cls.leaf('( 2nd ` R )', 'NN0', rre)
# ( 2nd ` J ), ( 2nd ` X ), ( 2nd ` U ) are real by the bounds they satisfy;
# their typing comes from the caller through the three charge hypotheses
h10 = w.h('( ( 2nd ` J ) e. NN0 /\\ ( 2nd ` X ) e. NN0 /\\ ( 2nd ` U ) e. NN0 )')
cls.leaf('( 2nd ` J )', 'NN0', st([h10], 'simp1d', '( 2nd ` J ) e. NN0'))
cls.leaf('( 2nd ` X )', 'NN0', st([h10], 'simp2d', '( 2nd ` X ) e. NN0'))
cls.leaf('( 2nd ` U )', 'NN0', st([h10], 'simp3d', '( 2nd ` U ) e. NN0'))
le = linarith(w, 'ph', [resc, h5, h6, verc], '%s <_ %s' % (COSTEX, CPU),
              closure=cls, atoms=[B1, B2, B3, B4])
an0 = st([ann], 'nnnn0d', 'A e. NN0')
_parts = [(yn0, 'Y e. NN0'), (tn0, 'T e. NN0'), (an0, 'A e. NN0'),
          (x5n0, '%s e. NN0' % X5), (kn0, 'K e. NN0'), (lpn, '%s e. NN0' % LP),
          (lsn, '%s e. NN0' % LS)]
_cur = 'Z e. NN0'
_acc = zn0
for _s, _t in _parts:
    _cur = '( %s /\\ %s )' % (_cur, _t)
    _acc = st([_acc, _s], 'jca', _cur)
cpv2 = st([_acc, w.inst('costpiecesval')], 'syl', '%s = %s' % (CP, CPU))
w.qed([le, st([cpv2], 'eqcomd', '%s = %s' % (CPU, CP))], 'breqtrd', '( ph -> %s <_ %s )' % (COSTEX, CP))
run(w)
