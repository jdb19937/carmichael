"""Sortie C0b, batch 7: the generic nested-supremum lemma and the interval
absolute-difference bound (gsupne, iccabssub)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c0b_lib import *
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from lin import linarith

# ---- gsupne
w = W('gsupne', 'A supremum of a bounded nonempty set of reals lies between a member and an upper bound.')
SUP = 'sup ( T , RR , < )'
A0 = '( ( T C_ RR /\\ X e. T ) /\\ ( Y e. RR /\\ A. y e. T y <_ Y ) )'
tss = w.s([], 'simpll', '( %s -> T C_ RR )' % A0)
xt = w.s([], 'simplr', '( %s -> X e. T )' % A0)
yr = w.s([], 'simprl', '( %s -> Y e. RR )' % A0)
al = w.s([], 'simprr', '( %s -> A. y e. T y <_ Y )' % A0)
ne = w.s([xt, w.inst('ne0i')], 'syl', '( %s -> T =/= (/) )' % A0)
sb = w.s([w.s([], 'breq2', '( x = Y -> ( y <_ x <-> y <_ Y ) )')], 'ralbidv', '( x = Y -> ( A. y e. T y <_ x <-> A. y e. T y <_ Y ) )')
bnd = w.s([yr, al, w.s([sb], 'rspcev', '( ( Y e. RR /\\ A. y e. T y <_ Y ) -> E. x e. RR A. y e. T y <_ x )')], 'syl2anc',
          '( %s -> E. x e. RR A. y e. T y <_ x )' % A0)
tri = w.s([tss, ne, bnd], '3jca', '( %s -> ( T C_ RR /\\ T =/= (/) /\\ E. x e. RR A. y e. T y <_ x ) )' % A0)
lb = w.s([tri, xt, w.inst('suprub')], 'syl2anc', '( %s -> X <_ %s )' % (A0, SUP))
cb = w.s([w.s([], 'breq1', '( y = z -> ( y <_ Y <-> z <_ Y ) )')], 'cbvralvw', '( A. y e. T y <_ Y <-> A. z e. T z <_ Y )')
alz = w.s([al, w.s([cb], 'a1i', '( %s -> ( A. y e. T y <_ Y <-> A. z e. T z <_ Y ) )' % A0)], 'mpbid', '( %s -> A. z e. T z <_ Y )' % A0)
ub = w.s([w.s([tri, yr, w.inst('suprleub')], 'syl2anc', '( %s -> ( %s <_ Y <-> A. z e. T z <_ Y ) )' % (A0, SUP)), alz], 'mpbird', '( %s -> %s <_ Y )' % (A0, SUP))
w.qed([lb, ub], 'jca', '( %s -> ( X <_ %s /\\ %s <_ Y ) )' % (A0, SUP, SUP)); run(w)

# ---- iccabssub
w = W('iccabssub', 'Two points of a closed interval are within its length of each other.')
A0 = '( ( M e. RR /\\ N e. RR ) /\\ ( X e. ( M [,] N ) /\\ Y e. ( M [,] N ) ) )'
mr = w.s([], 'simpll', '( %s -> M e. RR )' % A0)
nr = w.s([], 'simplr', '( %s -> N e. RR )' % A0)
xi = w.s([], 'simprl', '( %s -> X e. ( M [,] N ) )' % A0)
yi = w.s([], 'simprr', '( %s -> Y e. ( M [,] N ) )' % A0)
ex = w.s([mr, nr, w.inst('elicc2')], 'syl2anc', '( %s -> ( X e. ( M [,] N ) <-> ( X e. RR /\\ M <_ X /\\ X <_ N ) ) )' % A0)
ey = w.s([mr, nr, w.inst('elicc2')], 'syl2anc', '( %s -> ( Y e. ( M [,] N ) <-> ( Y e. RR /\\ M <_ Y /\\ Y <_ N ) ) )' % A0)
tx = w.s([ex, xi], 'mpbird' if False else 'mpbid', '( %s -> ( X e. RR /\\ M <_ X /\\ X <_ N ) )' % A0)
w.lines.pop()
tx = w.s([xi, ex], 'mpbid', '( %s -> ( X e. RR /\\ M <_ X /\\ X <_ N ) )' % A0)
ty = w.s([yi, ey], 'mpbid', '( %s -> ( Y e. RR /\\ M <_ Y /\\ Y <_ N ) )' % A0)
xr = w.s([tx, w.inst('simp1')], 'syl', '( %s -> X e. RR )' % A0)
mx = w.s([tx, w.inst('simp2')], 'syl', '( %s -> M <_ X )' % A0)
xn = w.s([tx, w.inst('simp3')], 'syl', '( %s -> X <_ N )' % A0)
yr = w.s([ty, w.inst('simp1')], 'syl', '( %s -> Y e. RR )' % A0)
my = w.s([ty, w.inst('simp2')], 'syl', '( %s -> M <_ Y )' % A0)
yn = w.s([ty, w.inst('simp3')], 'syl', '( %s -> Y <_ N )' % A0)
LV = {'M': mr, 'N': nr, 'X': xr, 'Y': yr}
HY = [mx, xn, my, yn]
g1 = linarith(w, A0, HY, '-u ( N - M ) <_ ( X - Y )', leaves=LV)
g2 = linarith(w, A0, HY, '( X - Y ) <_ ( N - M )', leaves=LV)
sub = w.s([xr, yr], 'resubcld', '( %s -> ( X - Y ) e. RR )' % A0)
dif = w.s([nr, mr], 'resubcld', '( %s -> ( N - M ) e. RR )' % A0)
w.qed([w.s([sub, dif, w.inst('absle')], 'syl2anc', '( %s -> ( ( abs ` ( X - Y ) ) <_ ( N - M ) <-> ( -u ( N - M ) <_ ( X - Y ) /\\ ( X - Y ) <_ ( N - M ) ) ) )' % A0),
       w.s([g1, g2], 'jca', '( %s -> ( -u ( N - M ) <_ ( X - Y ) /\\ ( X - Y ) <_ ( N - M ) ) )' % A0)], 'mpbird',
      '( %s -> ( abs ` ( X - Y ) ) <_ ( N - M ) )' % A0); run(w)

# ---- gsupcl
w = W('gsupcl', 'The supremum of a bounded nonempty set of reals is a real number.')
A0 = '( ( T C_ RR /\\ X e. T ) /\\ ( Y e. RR /\\ A. y e. T y <_ Y ) )'
tss = w.s([], 'simpll', '( %s -> T C_ RR )' % A0)
xt = w.s([], 'simplr', '( %s -> X e. T )' % A0)
yr = w.s([], 'simprl', '( %s -> Y e. RR )' % A0)
al = w.s([], 'simprr', '( %s -> A. y e. T y <_ Y )' % A0)
ne = w.s([xt, w.inst('ne0i')], 'syl', '( %s -> T =/= (/) )' % A0)
sb = w.s([w.s([], 'breq2', '( x = Y -> ( y <_ x <-> y <_ Y ) )')], 'ralbidv', '( x = Y -> ( A. y e. T y <_ x <-> A. y e. T y <_ Y ) )')
bnd = w.s([yr, al, w.s([sb], 'rspcev', '( ( Y e. RR /\\ A. y e. T y <_ Y ) -> E. x e. RR A. y e. T y <_ x )')], 'syl2anc',
          '( %s -> E. x e. RR A. y e. T y <_ x )' % A0)
tri = w.s([tss, ne, bnd], '3jca', '( %s -> ( T C_ RR /\\ T =/= (/) /\\ E. x e. RR A. y e. T y <_ x ) )' % A0)
w.qed([tri, w.inst('suprcl')], 'syl', '( %s -> sup ( T , RR , < ) e. RR )' % A0); run(w)
