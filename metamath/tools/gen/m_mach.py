import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
NONE = '( inr ` (/) )'
def MT(m): return '( 1st ` ( 1st ` %s ) )' % m
def MK0(m): return '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % m
def MK1(m): return '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % m
def MMAIN(m): return '( 1st ` ( 1st ` ( 2nd ` %s ) ) )' % m
def MINIT(m): return '( 2nd ` ( 1st ` ( 2nd ` %s ) ) )' % m
def MPROG(m): return '( 2nd ` ( 2nd ` %s ) )' % m
def MG(m): return G(MT(m))
def INITB(m, l): return sub(defbody('df-tm2init').split('|->', 1)[1].rsplit(')', 1)[0].strip(), {'m': m, 'l': l})
def HALTB(m, l): return sub(defbody('df-tm2halt').split('|->', 1)[1].rsplit(')', 1)[0].strip(), {'m': m, 'l': l})
def OUTTB(m, n): return sub(defbody('df-tm2outt').split('|->', 1)[1].rsplit(')', 1)[0].strip(), {'m': m, 'n': n})

# tm2initval
for label, df, bodyf, desc in (('tm2initval', 'df-tm2init', INITB, 'Value of TM2init: the initial configuration on input word X (Lean\'s initList).'),
                               ('tm2haltval', 'df-tm2halt', HALTB, 'Value of TM2halt: the halting configuration with output word X (Lean\'s haltList).')):
    w = W(label, desc)
    A = '( m = M /\\ l = X )'
    l1 = w.s([], 'simpl', '( %s -> m = M )' % A); l2 = w.s([], 'simpr', '( %s -> l = X )' % A)
    c, bMX = w.congr(bodyf('m', 'l'), {'m': 'M', 'l': 'X'}, A, {'m': l1, 'l': l2})
    d = w.s([], df, '%s = %s' % ({'df-tm2init': 'TM2init', 'df-tm2halt': 'TM2halt'}[df], defbody(df)))
    f = w.s([c, d], 'ovmpoga', '( ( M e. _V /\\ X e. _V /\\ %s e. _V ) -> ( M %s X ) = %s )' % (bMX, {'df-tm2init': 'TM2init', 'df-tm2halt': 'TM2halt'}[df], bMX))
    e = w.s([], 'opex', '%s e. _V' % bMX)
    B = '( M e. V /\\ X e. W )'
    x1 = w.s([], 'elex', '( M e. V -> M e. _V )'); x2 = w.s([], 'elex', '( X e. W -> X e. _V )')
    a1 = w.s([x1], 'adantr', '( %s -> M e. _V )' % B); a2 = w.s([x2], 'adantl', '( %s -> X e. _V )' % B); a3 = w.s([e], 'a1i', '( %s -> %s e. _V )' % (B, bMX))
    w.qed([a1, a2, a3, f], 'syl3anc', '( %s -> ( M %s X ) = %s )' % (B, {'df-tm2init': 'TM2init', 'df-tm2halt': 'TM2halt'}[df], bMX))
    run(w)

# tm2outtval
w = W('tm2outtval', 'Value of TM2OutputsInTime: the relation between input words and optional output words reached within N steps.')
A = '( m = M /\\ n = N )'
l1 = w.s([], 'simpl', '( %s -> m = M )' % A); l2 = w.s([], 'simpr', '( %s -> n = N )' % A)
c, bMN = w.congr(OUTTB('m', 'n'), {'m': 'M', 'n': 'N'}, A, {'m': l1, 'n': l2})
d = w.s([], 'df-tm2outt', 'TM2OutputsInTime = %s' % defbody('df-tm2outt'))
f = w.s([c, d], 'ovmpoga', '( ( M e. _V /\\ N e. NN0 /\\ %s e. _V ) -> ( M TM2OutputsInTime N ) = %s )' % (bMN, bMN))
W0 = 'Word ( %s ` %s )' % (MG('M'), MK0('M')); W1 = '( Word ( %s ` %s ) |_| 1o )' % (MG('M'), MK1('M'))
s1 = w.s([], 'opabssxp', '%s C_ ( %s X. %s )' % (bMN, W0, W1))
e1 = w.s([], 'fvex', '( %s ` %s ) e. _V' % (MG('M'), MK0('M'))); e1i = w.inst('wrdexg'); e2 = w.s([e1, e1i], 'ax-mp', '%s e. _V' % W0)
e3 = w.s([], 'fvex', '( %s ` %s ) e. _V' % (MG('M'), MK1('M'))); e3i = w.inst('wrdexg'); e4 = w.s([e3, e3i], 'ax-mp', 'Word ( %s ` %s ) e. _V' % (MG('M'), MK1('M')))
e5 = w.s([], '1oex', '1o e. _V'); e5i = w.inst('djuex'); e6 = w.s([e4, e5, e5i], 'mp2an', '%s e. _V' % W1)
e7i = w.inst('xpexg'); e7 = w.s([e2, e6, e7i], 'mp2an', '( %s X. %s ) e. _V' % (W0, W1))
e8i = w.inst('ssexg'); e8 = w.s([s1, e7, e8i], 'mp2an', '%s e. _V' % bMN)
B = '( M e. V /\\ N e. NN0 )'
x1 = w.s([], 'elex', '( M e. V -> M e. _V )'); a1 = w.s([x1], 'adantr', '( %s -> M e. _V )' % B); a2 = w.s([], 'simpr', '( %s -> N e. NN0 )' % B); a3 = w.s([e8], 'a1i', '( %s -> %s e. _V )' % (B, bMN))
w.qed([a1, a2, a3, f], 'syl3anc', '( %s -> ( M TM2OutputsInTime N ) = %s )' % (B, bMN))
run(w)

# tm2outtbr
w = W('tm2outtbr', 'The input-output relation within N steps, unfolded to the state transition relation of the step function.')
W0 = 'Word ( %s ` %s )' % (MG('M'), MK0('M')); W1 = '( Word ( %s ` %s ) |_| 1o )' % (MG('M'), MK1('M'))
MEM = '( X e. %s /\\ Y e. %s )' % (W0, W1)
A = '( M e. V /\\ N e. NN0 /\\ %s )' % MEM
bMN = OUTTB('M', 'N')
body = parse(bMN)  # opab: we need the inner wff text
# bMN = { <. a , b >. | ( DOMS /\ REL ) }
inner = bMN[len('{ <. a , b >. | '):-2]
E = '( a = X /\\ b = Y )'
l1 = w.s([], 'simpl', '( %s -> a = X )' % E); l2 = w.s([], 'simpr', '( %s -> b = Y )' % E)
c, innerXY = w.wcongr(inner, {'a': 'X', 'b': 'Y'}, E, {'a': l1, 'b': l2})
e = w.s([], 'eqid', '%s = %s' % (bMN, bMN))
br = w.s([c, e], 'brabga', '( ( X e. %s /\\ Y e. %s ) -> ( X %s Y <-> %s ) )' % (W0, W1, bMN, innerXY))
m = w.s([], 'simp3', '( %s -> %s )' % (A, MEM)); br2 = w.s([m, br], 'syl', '( %s -> ( X %s Y <-> %s ) )' % (A, bMN, innerXY))
t1 = w.s([], 'simp1', '( %s -> M e. V )' % A); t2 = w.s([], 'simp2', '( %s -> N e. NN0 )' % A)
vi = w.inst('tm2outtval'); v = w.s([t1, t2, vi], 'syl2anc', '( %s -> ( M TM2OutputsInTime N ) = %s )' % (A, bMN))
v2 = w.s([v], 'breqd', '( %s -> ( X ( M TM2OutputsInTime N ) Y <-> X %s Y ) )' % (A, bMN))
REL = parse_wff(innerXY).kids[1].text()
assert innerXY == '( %s /\\ %s )' % (MEM, REL)
bt = w.s([m], 'biantrurd', '( %s -> ( %s <-> ( %s /\\ %s ) ) )' % (A, REL, MEM, REL))
b3 = w.s([br2, bt], 'bitr4d', '( %s -> ( X %s Y <-> %s ) )' % (A, bMN, REL))
w.qed([v2, b3], 'bitrd', '( %s -> ( X ( M TM2OutputsInTime N ) Y <-> %s ) )' % (A, REL))
run(w)
print('REL:', REL)

# elfintm2
w = W('elfintm2', 'Membership in FinTM2 for an explicit machine tuple <. <. G , L , S >. , <. C , D >. , <. B , I , M >. >. (nested pairs written out).')
U = '<. <. <. <. G , L >. , S >. , <. C , D >. >. , <. <. B , I >. , M >. >.'
A = '( ( G e. V /\\ L e. W /\\ S e. X ) /\\ ( C e. Y /\\ D e. Z ) /\\ ( B e. U /\\ I e. O /\\ M e. P ) )'
body = defbody('df-fintm2'); inner = body[len('{ m | '):-2]
l = w.s([], 'id', '( m = %s -> m = %s )' % (U, U))
c, innerU = w.wcongr(inner, {'m': U}, 'm = %s' % U, {'m': l})
ux = w.s([], 'opex', '%s e. _V' % U)
el = w.s([c], 'elabg', '( %s e. _V -> ( %s e. FinTM2 <-> %s ) )' % (U, U, innerU))
w.lines[-1] = w.lines[-1]  # elabg needs df: A e. { x | ph }; FinTM2 = { m | ... } -> use df-fintm2 rewriting
# replace: prove ( U e. { m | inner } <-> innerU ) then rewrite via df-fintm2
w.lines.pop()
el = w.s([c], 'elabg', '( %s e. _V -> ( %s e. %s <-> %s ) )' % (U, U, body, innerU))
el2 = w.s([ux, el], 'ax-mp', '( %s e. %s <-> %s )' % (U, body, innerU))
d = w.s([], 'df-fintm2', 'FinTM2 = %s' % body)
d2 = w.s([d], 'eleq2i', '( %s e. FinTM2 <-> %s e. %s )' % (U, U, body))
el3 = w.s([d2, el2], 'bitri', '( %s e. FinTM2 <-> %s )' % (U, innerU))
# set-ness steps for the projections
st = {}
g1 = w.s([], 'simp1', '( %s -> ( G e. V /\\ L e. W /\\ S e. X ) )' % A); st['G'] = w.s([w.s([g1], 'simp1d', '( %s -> G e. V )' % A)], 'elexd', '( %s -> G e. _V )' % A)
st['L'] = w.s([w.s([g1], 'simp2d', '( %s -> L e. W )' % A)], 'elexd', '( %s -> L e. _V )' % A); st['S'] = w.s([w.s([g1], 'simp3d', '( %s -> S e. X )' % A)], 'elexd', '( %s -> S e. _V )' % A)
g2 = w.s([], 'simp2', '( %s -> ( C e. Y /\\ D e. Z ) )' % A); st['C'] = w.s([w.s([g2], 'simpld', '( %s -> C e. Y )' % A)], 'elexd', '( %s -> C e. _V )' % A); st['D'] = w.s([w.s([g2], 'simprd', '( %s -> D e. Z )' % A)], 'elexd', '( %s -> D e. _V )' % A)
g3 = w.s([], 'simp3', '( %s -> ( B e. U /\\ I e. O /\\ M e. P ) )' % A); st['B'] = w.s([w.s([g3], 'simp1d', '( %s -> B e. U )' % A)], 'elexd', '( %s -> B e. _V )' % A)
st['I'] = w.s([w.s([g3], 'simp2d', '( %s -> I e. O )' % A)], 'elexd', '( %s -> I e. _V )' % A); st['M'] = w.s([w.s([g3], 'simp3d', '( %s -> M e. P )' % A)], 'elexd', '( %s -> M e. _V )' % A)
ev, res = evaluate(w, A, innerU, st, wff=True)
el4 = w.s([el3], 'a1i', '( %s -> ( %s e. FinTM2 <-> %s ) )' % (A, U, innerU))
el5 = w.s([el4, ev], 'bitrd', '( %s -> ( %s e. FinTM2 <-> %s ) )' % (A, U, res))
# drop the shape conditions
tree = parse_wff(res); SH = tree.kids[0]; REST = tree.kids[1]
sh1, sh2 = SH.kids
# sh1: U e. ( ( _V X. ( _V X. _V ) ) X. ( ( _V X. _V ) X. _V ) ) ; sh2: <. <. G , L >. , S >. e. ( ( _V X. _V ) X. _V )
def inxp(elems):
    """build ( A -> <..> e. product of _V ) for nested pair per structure"""
    pass
p1 = w.s([st['G'], st['L'], w.inst('opelxpi')], 'syl2anc', '( %s -> <. G , L >. e. ( _V X. _V ) )' % A)
p2 = w.s([p1, st['S'], w.inst('opelxpi')], 'syl2anc', '( %s -> <. <. G , L >. , S >. e. ( ( _V X. _V ) X. _V ) )' % A)
p3 = w.s([st['C'], st['D'], w.inst('opelxpi')], 'syl2anc', '( %s -> <. C , D >. e. ( _V X. _V ) )' % A)
tx = w.s([p2], 'elexd', '( %s -> <. <. G , L >. , S >. e. _V )' % A)
p4 = w.s([tx, p3, w.inst('opelxpi')], 'syl2anc', '( %s -> <. <. <. G , L >. , S >. , <. C , D >. >. e. ( _V X. ( _V X. _V ) ) )' % A)
p5 = w.s([st['B'], st['I'], w.inst('opelxpi')], 'syl2anc', '( %s -> <. B , I >. e. ( _V X. _V ) )' % A)
p6 = w.s([p5, st['M'], w.inst('opelxpi')], 'syl2anc', '( %s -> <. <. B , I >. , M >. e. ( ( _V X. _V ) X. _V ) )' % A)
p7 = w.s([p4, p6, w.inst('opelxpi')], 'syl2anc', '( %s -> %s )' % (A, sh1.text()))
assert sh2.text() == '<. <. G , L >. , S >. e. ( ( _V X. _V ) X. _V )', sh2.text()
p8 = w.s([p7, p2], 'jca', '( %s -> %s )' % (A, SH.text()))
bt = w.s([p8], 'biantrurd', '( %s -> ( %s <-> %s ) )' % (A, REST.text(), res))
w.qed([el5, bt], 'bitr4d', '( %s -> ( %s e. FinTM2 <-> %s ) )' % (A, U, REST.text()))
run(w)
print('COND:', REST.text())
