"""Sortie S, batch 4: the relation TM2CompT (Lean's TM2ComputableInTime) unfolded and projected."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

body = defbody('df-tm2compt')                 # { <. h , e >. | WFF }
assert body.startswith('{ <. h , e >. |') and body.endswith('}')
wff = body[len('{ <. h , e >. |'):-1].strip()
WFF = lambda H, E: sub(wff, {'h': H, 'e': E})
node = parse_wff(WFF('H', 'E')); assert node.kind == '3an', node.kind
P, Q, R = [k.text() for k in node.kids]
Pn = parse_wff(P); P1, P2 = [k.text() for k in Pn.kids]
Qn = parse_wff(Q); Q1, Q2, Q3 = [k.text() for k in Qn.kids]
Rn = parse_wff(R); assert Rn.kind == 'ral' and Rn.bound == ('a',), (Rn.kind, Rn.bound)
DOM, BR = [k.text() for k in Rn.kids]
EA = lambda E: '( 1st ` ( 1st ` ( 1st ` %s ) ) )' % E
assert DOM == 'dom ' + EA('E'), DOM
HE = 'H TM2CompT E'

w = W('tm2comptrel', 'TM2CompT is a relation.')
d = w.s([], 'df-tm2compt', 'TM2CompT = %s' % body)
r = w.s([d], 'releqi', '( Rel TM2CompT <-> Rel %s )' % body)
ro = w.s([], 'relopab', 'Rel %s' % body)
w.qed([ro, r], 'mpbir', 'Rel TM2CompT'); run(w)

w = W('tm2comptbr', "The relation TM2CompT unfolded: H = <. tm , <. ia , oa >. , time >. witnesses that E = <. <. ea , A0 >. , <. eb , A1 >. , f >. is computed in time (Lean's TM2ComputableInTime ea eb f).")
A = '( h = H /\\ e = E )'
l1 = w.s([], 'simpl', '( %s -> h = H )' % A); l2 = w.s([], 'simpr', '( %s -> e = E )' % A)
c, wHE = w.wcongr(wff, {'h': 'H', 'e': 'E'}, A, {'h': l1, 'e': l2}); assert wHE == WFF('H', 'E'), wHE
d = w.s([], 'df-tm2compt', 'TM2CompT = %s' % body)
w.qed([c, d], 'brabga', '( ( H e. V /\\ E e. W ) -> ( %s <-> %s ) )' % (HE, WFF('H', 'E'))); run(w)

w = W('tm2comptex', 'The arguments of TM2CompT are sets.')
rel = w.s([], 'tm2comptrel', 'Rel TM2CompT'); bi = w.inst('brrelex12')
w.qed([rel, bi], 'mpan', '( %s -> ( H e. _V /\\ E e. _V ) )' % HE); run(w)

w = W('tm2comptd', 'The relation TM2CompT unfolded, as a deduction from the relation itself.')
ex = w.s([], 'tm2comptex', '( %s -> ( H e. _V /\\ E e. _V ) )' % HE)
bi = w.inst('tm2comptbr'); br = w.s([ex, bi], 'syl', '( %s -> ( %s <-> %s ) )' % (HE, HE, WFF('H', 'E')))
i = w.s([], 'id', '( %s -> %s )' % (HE, HE))
w.qed([i, br], 'mpbid', '( %s -> %s )' % (HE, WFF('H', 'E'))); run(w)

w = W('tm2comptmach', 'A witness of TM2CompT carries a bundled finite machine.')
d = w.s([], 'tm2comptd', '( %s -> %s )' % (HE, WFF('H', 'E')))
p = w.s([d], 'simp1d', '( %s -> %s )' % (HE, P))
w.qed([p], 'simprd', '( %s -> %s )' % (HE, P2)); run(w)

w = W('tm2comptia', 'A witness of TM2CompT carries a bijection from the input stack alphabet onto the input alphabet.')
d = w.s([], 'tm2comptd', '( %s -> %s )' % (HE, WFF('H', 'E')))
q = w.s([d], 'simp2d', '( %s -> %s )' % (HE, Q))
w.qed([q], 'simp1d', '( %s -> %s )' % (HE, Q1)); run(w)

w = W('tm2comptoa', 'A witness of TM2CompT carries a bijection from the output stack alphabet onto the output alphabet.')
d = w.s([], 'tm2comptd', '( %s -> %s )' % (HE, WFF('H', 'E')))
q = w.s([d], 'simp2d', '( %s -> %s )' % (HE, Q))
w.qed([q], 'simp2d', '( %s -> %s )' % (HE, Q2)); run(w)

w = W('tm2compttime', 'A witness of TM2CompT carries a time function on the natural numbers (Lean: h.time).')
d = w.s([], 'tm2comptd', '( %s -> %s )' % (HE, WFF('H', 'E')))
q = w.s([d], 'simp2d', '( %s -> %s )' % (HE, Q))
w.qed([q], 'simp3d', '( %s -> %s )' % (HE, Q3)); run(w)

w = W('tm2comptout', 'A witness of TM2CompT computes the function: on every input X the machine outputs the encoded value within time of the input length (Lean: h.outputsFun).')
A2 = '( %s /\\ X e. %s )' % (HE, DOM)
d = w.s([], 'tm2comptd', '( %s -> %s )' % (HE, WFF('H', 'E')))
r = w.s([d], 'simp3d', '( %s -> %s )' % (HE, R)); r2 = w.s([r], 'adantr', '( %s -> %s )' % (A2, R))
x = w.s([], 'simpr', '( %s -> X e. %s )' % (A2, DOM))
l = w.s([], 'id', '( a = X -> a = X )')
c, brX = w.wcongr(BR, {'a': 'X'}, 'a = X', {'a': l}); assert brX == sub(BR, {'a': 'X'})
w.qed([c, r2, x], 'rspcdva', '( %s -> %s )' % (A2, brX)); run(w)
