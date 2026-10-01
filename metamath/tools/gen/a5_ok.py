"""Sortie A5, batch 3: the success path of Alg.search, output and cost unfolded
(Lean: AlgBudget.search_success).
MM_DB=sorties/a5.mm python3 tools/gen/a5_ok.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from tm import *
from a2lib import WH

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    assert w.run(), w.label

SC = '<. <. <. Z , W >. , <. Y , T >. >. , H >.'
SR = '( %s Search N )' % SC
MM = '( 1st ` ( 2nd ` ( 1st ` X ) ) )'
SS = '( 2nd ` ( 2nd ` ( 1st ` X ) ) )'
PAY = '( inl ` <. %s , %s >. )' % (MM, SS)
COST = '( ( ( C + ( 2nd ` J ) ) + ( 2nd ` X ) ) + ( 2nd ` U ) )'
B3 = '<. if ( ( 1st ` U ) = 1o , %s , ( inr ` (/) ) ) , %s >.' % (PAY, COST)
B2 = 'if ( ( 1st ` X ) = ( inr ` (/) ) , <. ( inr ` (/) ) , ( ( C + ( 2nd ` J ) ) + ( 2nd ` X ) ) >. , %s )' % B3
B1 = 'if ( ( 1st ` J ) = ( inr ` (/) ) , <. ( inr ` (/) ) , ( C + ( 2nd ` J ) ) >. , %s )' % B2
B0 = 'if ( I < T , <. ( inr ` (/) ) , ( ( 2nd ` R ) + 1 ) >. , %s )' % B1

# --------------------------------------------------------------- okproj
w = W('okproj', 'The three projections of a successful search result (Lean: the some (m, S) pattern).')
P = '( ( M e. _V /\\ S e. _V /\\ K e. _V ) /\\ D = <. ( inl ` <. M , S >. ) , K >. )'
st = lambda hyps, ref, f: w.s(hyps, ref, '( %s -> %s )' % (P, f))
mv = st([st([], 'simpl', '( M e. _V /\\ S e. _V /\\ K e. _V )')], 'simp1d', 'M e. _V')
sv = st([st([], 'simpl', '( M e. _V /\\ S e. _V /\\ K e. _V )')], 'simp2d', 'S e. _V')
kv = st([st([], 'simpl', '( M e. _V /\\ S e. _V /\\ K e. _V )')], 'simp3d', 'K e. _V')
de = st([], 'simpr', 'D = <. ( inl ` <. M , S >. ) , K >.')
opv = w.s([], 'opex', '<. M , S >. e. _V')
opva = st([opv], 'a1i', '<. M , S >. e. _V')
ilv = w.s([], 'fvex', '( inl ` <. M , S >. ) e. _V')
ilva = st([ilv], 'a1i', '( inl ` <. M , S >. ) e. _V')
# first projection
f1 = w.s([de], 'fveq2d', '( %s -> ( 1st ` D ) = ( 1st ` <. ( inl ` <. M , S >. ) , K >. ) )' % P)
f1b = st([ilva, kv, w.inst('op1stg')], 'syl2anc',
         '( 1st ` <. ( inl ` <. M , S >. ) , K >. ) = ( inl ` <. M , S >. )')
f1c = st([f1, f1b], 'eqtrd', '( 1st ` D ) = ( inl ` <. M , S >. )')
ne = st([opva, w.s([], '0ex', '(/) e. _V'), w.inst('inlneinr')], 'sylancl',
        '( inl ` <. M , S >. ) =/= ( inr ` (/) )')
ne2 = st([f1c, ne], 'eqnetrd', '( 1st ` D ) =/= ( inr ` (/) )')
# the payload
p2 = w.s([f1c], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` D ) ) = ( 2nd ` ( inl ` <. M , S >. ) ) )' % P)
ilv2 = st([opva, w.inst('inlval')], 'syl', '( inl ` <. M , S >. ) = <. (/) , <. M , S >. >.')
p2b = w.s([ilv2], 'fveq2d', '( %s -> ( 2nd ` ( inl ` <. M , S >. ) ) = ( 2nd ` <. (/) , <. M , S >. >. ) )' % P)
p2c = st([w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % P), opva, w.inst('op2ndg')],
         'syl2anc', '( 2nd ` <. (/) , <. M , S >. >. ) = <. M , S >.')
pay = st([st([p2, p2b], 'eqtrd', '( 2nd ` ( 1st ` D ) ) = ( 2nd ` <. (/) , <. M , S >. >. )'), p2c],
         'eqtrd', '( 2nd ` ( 1st ` D ) ) = <. M , S >.')
# the two components
m1 = w.s([pay], 'fveq2d', '( %s -> ( 1st ` ( 2nd ` ( 1st ` D ) ) ) = ( 1st ` <. M , S >. ) )' % P)
m1b = st([mv, sv, w.inst('op1stg')], 'syl2anc', '( 1st ` <. M , S >. ) = M')
mres = st([m1, m1b], 'eqtrd', '( 1st ` ( 2nd ` ( 1st ` D ) ) ) = M')
s1 = w.s([pay], 'fveq2d', '( %s -> ( 2nd ` ( 2nd ` ( 1st ` D ) ) ) = ( 2nd ` <. M , S >. ) )' % P)
s1b = st([mv, sv, w.inst('op2ndg')], 'syl2anc', '( 2nd ` <. M , S >. ) = S')
sres = st([s1, s1b], 'eqtrd', '( 2nd ` ( 2nd ` ( 1st ` D ) ) ) = S')
# the cost
c1 = w.s([de], 'fveq2d', '( %s -> ( 2nd ` D ) = ( 2nd ` <. ( inl ` <. M , S >. ) , K >. ) )' % P)
c1b = st([ilva, kv, w.inst('op2ndg')], 'syl2anc', '( 2nd ` <. ( inl ` <. M , S >. ) , K >. ) = K')
cres = st([c1, c1b], 'eqtrd', '( 2nd ` D ) = K')
w.qed([ne2, st([mres, sres], 'jca',
               '( ( 1st ` ( 2nd ` ( 1st ` D ) ) ) = M /\\ ( 2nd ` ( 2nd ` ( 1st ` D ) ) ) = S )'), cres],
      '3jca',
      '( %s -> ( ( 1st ` D ) =/= ( inr ` (/) ) /\\ ( ( 1st ` ( 2nd ` ( 1st ` D ) ) ) = M /\\ ( 2nd ` ( 2nd ` ( 1st ` D ) ) ) = S ) /\\ ( 2nd ` D ) = K ) )' % P)
run(w)

# --------------------------------------------------------------- srchok
w = WH('srchok', 'The success path of the algorithm of the paper, output and cost unfolded (Lean: search_success of AlgBudget.lean).')
h1 = w.h('( Z e. NN /\\ W e. NN0 )')
h2 = w.h('( Y e. NN /\\ T e. NN0 )')
h3 = w.h('( H e. NN0 /\\ N e. NN0 )')
h4 = w.h('R = ( ( Z Reservoir W ) ` Y )')
h5 = w.h('I = ( # ` ( 1st ` R ) )')
h6 = w.h('Q = ( ( 1st ` R ) substr <. ( I - T ) , I >. )')
h7 = w.h('G = ( ProdL ` Q )')
h8 = w.h('A = ( 1st ` G )')
h9 = w.h('C = ( ( ( ( 2nd ` R ) + T ) + ( 2nd ` G ) ) + 2 )')
h10 = w.h('J = ( ( ( ( ( Q Scan ( A ^ 5 ) ) ` Z ) ` H ) ` 1 ) ` ( A ^ 5 ) )')
h11 = w.h('P = ( 2nd ` ( 2nd ` ( 1st ` J ) ) )')
h12 = w.h('X = ( ( A Extract N ) ` P )')
h13 = w.h('U = ( ( 1st ` ( 2nd ` ( 1st ` X ) ) ) Verify ( 2nd ` ( 2nd ` ( 1st ` X ) ) ) )')
h14 = w.h('T <_ I')
h15 = w.h('( 1st ` J ) =/= ( inr ` (/) )')
h16 = w.h('( 1st ` X ) =/= ( inr ` (/) )')
h17 = w.h('( 1st ` U ) = 1o')
st = lambda hyps, ref, f: w.s(hyps, ref, '( ph -> %s )' % f)

zz = st([h1], 'simpld', 'Z e. NN')
ww = st([h1], 'simprd', 'W e. NN0')
yy = st([h2], 'simpld', 'Y e. NN')
tt = st([h2], 'simprd', 'T e. NN0')
hh = st([h3], 'simpld', 'H e. NN0')
nn = st([h3], 'simprd', 'N e. NN0')
# the fifteen-fold antecedent of searchval
acc = st([zz, ww], 'jca', '( Z e. NN /\\ W e. NN0 )')
texts = ['Y e. NN', 'T e. NN0', 'H e. NN0', 'N e. NN0',
         'R = ( ( Z Reservoir W ) ` Y )', 'I = ( # ` ( 1st ` R ) )',
         'Q = ( ( 1st ` R ) substr <. ( I - T ) , I >. )', 'G = ( ProdL ` Q )',
         'A = ( 1st ` G )', 'C = ( ( ( ( 2nd ` R ) + T ) + ( 2nd ` G ) ) + 2 )',
         'J = ( ( ( ( ( Q Scan ( A ^ 5 ) ) ` Z ) ` H ) ` 1 ) ` ( A ^ 5 ) )',
         'P = ( 2nd ` ( 2nd ` ( 1st ` J ) ) )', 'X = ( ( A Extract N ) ` P )',
         'U = ( ( 1st ` ( 2nd ` ( 1st ` X ) ) ) Verify ( 2nd ` ( 2nd ` ( 1st ` X ) ) ) )']
steps = [yy, tt, hh, nn, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
cur = '( Z e. NN /\\ W e. NN0 )'
for s, t in zip(steps, texts):
    cur = '( %s /\\ %s )' % (cur, t)
    acc = st([acc, s], 'jca', cur)
sv = st([acc, w.inst('searchval')], 'syl', '%s = %s' % (SR, B0))
# -. I < T
# I is real: from T <_ I we cannot get it; use R's typing
rres = st([h4, st([st([zz, ww], 'jca', '( Z e. NN /\\ W e. NN0 )'), yy, w.inst('reservoircl')], 'syl2anc',
                  '( ( Z Reservoir W ) ` Y ) e. ( Word NN0 X. NN0 )')], 'eqeltrd',
          'R e. ( Word NN0 X. NN0 )')
rwrd = st([rres, w.inst('xp1st')], 'syl', '( 1st ` R ) e. Word NN0')
ilen = st([h5, st([rwrd, w.inst('lencl')], 'syl', '( # ` ( 1st ` R ) ) e. NN0')], 'eqeltrd', 'I e. NN0')
ire = st([ilen], 'nn0red', 'I e. RR')
tre = st([tt], 'nn0red', 'T e. RR')
nlt = st([h14, st([tre, ire, w.inst('lenlt')], 'syl2anc', '( T <_ I <-> -. I < T )')], 'mpbid', '-. I < T')
e0 = w.s([nlt], 'iffalsed', '( ph -> %s = %s )' % (B0, B1))
e1 = w.s([st([h15], 'neneqd', '-. ( 1st ` J ) = ( inr ` (/) )')], 'iffalsed', '( ph -> %s = %s )' % (B1, B2))
e2 = w.s([st([h16], 'neneqd', '-. ( 1st ` X ) = ( inr ` (/) )')], 'iffalsed', '( ph -> %s = %s )' % (B2, B3))
e3 = w.s([h17], 'iftrued', '( ph -> if ( ( 1st ` U ) = 1o , %s , ( inr ` (/) ) ) = %s )' % (PAY, PAY))
e4 = w.s([e3], 'opeq1d', '( ph -> %s = <. %s , %s >. )' % (B3, PAY, COST))
w.qed([st([st([st([sv, e0], 'eqtrd', '%s = %s' % (SR, B1)), e1], 'eqtrd', '%s = %s' % (SR, B2)), e2],
          'eqtrd', '%s = %s' % (SR, B3)), e4],
      'eqtrd', '( ph -> %s = <. %s , %s >. )' % (SR, PAY, COST))
run(w)
