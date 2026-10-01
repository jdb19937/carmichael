import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
exec(open(os.path.join(os.path.dirname(__file__), 'o_rev4.py')).read().split('# ---- relexpsucfv2')[0])
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
REVM = '<. <. %s , <. (/) , 1o >. >. , <. <. (/) , %s >. , %s >. >.' % (T1, NONE, M1)
G = lambda n, c, a, b: '( ( %s ^r ( %s + 1 ) ) ` ( inl ` %s ) ) = ( inl ` %s )' % (OS, n, Cf(c, a, b), HALTC('( ( reverse ` %s ) ++ %s )' % (a, b)))
INNER = lambda n, a: 'A. b e. Word A A. c e. %s %s' % (S1, G(n, 'c', a, 'b'))
PH = lambda n: '( %s -> A. a e. Word A ( ( # ` a ) = %s -> %s ) )' % (AZ, n, INNER(n, 'a'))
AF = '( A e. Fin /\\ Z e. A )'

# ---- revm
w = W('revm', 'The reverse machine (two stacks, one label, states = optional letters) is a bundled finite machine.')
A = AF
a = w.s([], 'simpl', '( %s -> A e. Fin )' % A); zz = w.s([], 'simpr', '( %s -> Z e. A )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
az = w.s([a, zz], 'jca', '( %s -> ( A e. Fin /\\ Z e. A ) )' % A)
px = w.s([], 'prex', '%s e. _V' % G1); px2 = w.s([px], 'a1i', '( %s -> %s e. _V )' % (A, G1))
o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
sx = w.s([ax, o2, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (A, S1))
z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
nx = w.s([], 'fvex', '%s e. _V' % NONE); nx2 = w.s([nx], 'a1i', '( %s -> %s e. _V )' % (A, NONE))
mx = w.s([], 'snex', '%s e. _V' % M1); mx2 = w.s([mx], 'a1i', '( %s -> %s e. _V )' % (A, M1))
j1 = w.s([px2, o2, sx], '3jca', '( %s -> ( %s e. _V /\\ 1o e. _V /\\ %s e. _V ) )' % (A, G1, S1))
j2 = w.s([z2, o2], 'jca', '( %s -> ( (/) e. _V /\\ 1o e. _V ) )' % A)
j3 = w.s([z2, nx2, mx2], '3jca', '( %s -> ( (/) e. _V /\\ %s e. _V /\\ %s e. _V ) )' % (A, NONE, M1))
COND = '( ( Fun %s /\\ dom %s e. Fin /\\ ( (/) e. dom %s /\\ 1o e. dom %s /\\ ( %s ` (/) ) e. Fin ) ) /\\ ( 1o e. Fin /\\ (/) e. 1o ) /\\ ( %s e. Fin /\\ %s e. %s /\\ %s : 1o --> ( TM2Stmt ` %s ) ) )' % (G1, G1, G1, G1, G1, S1, NONE, S1, M1, T1)
el = w.s([j1, j2, j3, w.inst('elfintm2')], 'syl3anc', '( %s -> ( %s e. FinTM2 <-> %s ) )' % (A, REVM, COND))
extra = g1rules(w, A, ax); SM = {'A': ax}
ev, COND2 = evaluate(w, A, COND, SM, extra_rules=extra, wff=True)
el2 = w.s([el, ev], 'bitrd', '( %s -> ( %s e. FinTM2 <-> %s ) )' % (A, REVM, COND2))
n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A)
aa = w.s([ax, ax], 'jca', '( %s -> ( A e. _V /\\ A e. _V ) )' % A)
c1 = w.s([j2, aa, n2, w.inst('funprg')], 'syl3anc', '( %s -> Fun %s )' % (A, G1))
c2 = w.s([], 'prfi', '%s e. Fin' % TWO); c2b = w.s([c2], 'a1i', '( %s -> %s e. Fin )' % (A, TWO))
c3 = w.s([z, w.inst('prid1g')], 'ax-mp', '(/) e. %s' % TWO); c3b = w.s([c3], 'a1i', '( %s -> (/) e. %s )' % (A, TWO))
c4 = w.s([o, w.inst('prid2g')], 'ax-mp', '1o e. %s' % TWO); c4b = w.s([c4], 'a1i', '( %s -> 1o e. %s )' % (A, TWO))
c5 = w.s([c3b, c4b, a], '3jca', '( %s -> ( (/) e. %s /\\ 1o e. %s /\\ A e. Fin ) )' % (A, TWO, TWO))
p1 = w.s([c1, c2b, c5], '3jca', '( %s -> ( Fun %s /\\ %s e. Fin /\\ ( (/) e. %s /\\ 1o e. %s /\\ A e. Fin ) ) )' % (A, G1, TWO, TWO, TWO))
o1 = w.s([], '1onn', '1o e. _om'); of = w.s([o1, w.inst('nnfi')], 'ax-mp', '1o e. Fin'); ofb = w.s([of], 'a1i', '( %s -> 1o e. Fin )' % A)
z1 = w.s([], '0lt1o', '(/) e. 1o'); z1b = w.s([z1], 'a1i', '( %s -> (/) e. 1o )' % A)
p2 = w.s([ofb, z1b], 'jca', '( %s -> ( 1o e. Fin /\\ (/) e. 1o ) )' % A)
isf = w.s([], 'isfinite', '( A e. Fin <-> A ~< _om )'); af = w.s([a, isf], 'sylib', '( %s -> A ~< _om )' % A)
isf1 = w.s([], 'isfinite', '( 1o e. Fin <-> 1o ~< _om )'); of1 = w.s([of, isf1], 'mpbi', '1o ~< _om'); of1b = w.s([of1], 'a1i', '( %s -> 1o ~< _om )' % A)
dj = w.s([af, of1b, w.inst('djufi')], 'syl2anc', '( %s -> %s ~< _om )' % (A, S1))
isfs = w.s([], 'isfinite', '( %s e. Fin <-> %s ~< _om )' % (S1, S1)); sfin = w.s([dj, isfs], 'sylibr', '( %s -> %s e. Fin )' % (A, S1))
ns = w.s([z1, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, S1)); nsb = w.s([ns], 'a1i', '( %s -> %s e. %s )' % (A, NONE, S1))
sxs = w.s([], 'opex', '%s e. _V' % STM)
f1 = w.s([], 'f1osn', '%s : { (/) } -1-1-onto-> { %s }' % (M1, STM)); f2 = w.s([f1, w.inst('f1of')], 'ax-mp', '%s : { (/) } --> { %s }' % (M1, STM))
d1 = w.s([], 'df1o2', '1o = { (/) }'); d2 = w.s([d1], 'feq2i', '( %s : 1o --> { %s } <-> %s : { (/) } --> { %s } )' % (M1, STM, M1, STM))
f3 = w.s([f2, d2], 'mpbir', '%s : 1o --> { %s }' % (M1, STM)); f3b = w.s([f3], 'a1i', '( %s -> %s : 1o --> { %s } )' % (A, M1, STM))
st = w.s([az, w.inst('revstm')], 'syl', '( %s -> %s e. %s )' % (A, STM, ST1)); st2 = w.s([st], 'snssd', '( %s -> { %s } C_ %s )' % (A, STM, ST1))
f4 = w.s([f3b, st2, w.inst('fss')], 'syl2anc', '( %s -> %s : 1o --> %s )' % (A, M1, ST1))
p3 = w.s([sfin, nsb, f4], '3jca', '( %s -> ( %s e. Fin /\\ %s e. %s /\\ %s : 1o --> %s ) )' % (A, S1, NONE, S1, M1, ST1))
p = w.s([p1, p2, p3], '3jca', '( %s -> %s )' % (A, COND2))
w.qed([p, el2], 'mpbird', '( %s -> %s e. FinTM2 )' % (A, REVM))
run(w)

# ---- revinitc / revhaltc
for label, lem, desc, CF, stkl in (('revinitc', 'tm2initval', 'The initial configuration of the reverse machine on input W.', Cf(NONE, 'W', '(/)'), 'stk2pp0'),
                                  ('revhaltc', 'tm2haltval', 'The halting configuration of the reverse machine with output W.', HALTC('W'), 'stk2pp1')):
    w = W(label, desc)
    A = '( A e. V /\\ W e. Word A )'
    a = w.s([], 'simpl', '( %s -> A e. V )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
    ww = w.s([], 'simpr', '( %s -> W e. Word A )' % A); wx = w.s([ww], 'elexd', '( %s -> W e. _V )' % A)
    ix = w.s([], 'opex', '%s e. _V' % REVM); ix2 = w.s([ix], 'a1i', '( %s -> %s e. _V )' % (A, REVM))
    body = {'tm2initval': defbody('df-tm2init'), 'tm2haltval': defbody('df-tm2halt')}[lem]
    val = sub(body.split('|->', 1)[1].rsplit(')', 1)[0].strip(), {'m': REVM, 'l': 'W'})
    op = {'tm2initval': 'TM2init', 'tm2haltval': 'TM2halt'}[lem]
    v = w.s([ix2, wx, w.inst(lem)], 'syl2anc', '( %s -> ( %s %s W ) = %s )' % (A, REVM, op, val))
    extra = g1rules(w, A, ax); SM = {'A': ax, 'W': wx}
    K = '(/)' if lem == 'tm2initval' else '1o'
    MP = '( k e. %s |-> if ( k = %s , W , (/) ) )' % (TWO, K)
    sp = w.s([wx, w.inst(stkl)], 'syl', '( %s -> %s = %s )' % (A, MP, PP('W', '(/)') if K == '(/)' else PP('(/)', 'W')))
    def ex2(n):
        r = extra(n)
        if r: return r
        if n.text() == MP: return (PP('W', '(/)') if K == '(/)' else PP('(/)', 'W'), sp)
        return None
    ev, res = evaluate(w, A, val, SM, extra_rules=ex2)
    assert res == CF, (res, CF)
    w.qed([v, ev], 'eqtrd', '( %s -> ( %s %s W ) = %s )' % (A, REVM, op, CF))
    run(w)

# ---- revmach
w = W('revmach', 'Test program 2: the reverse machine outputs the reverse of its input word W in ( # ` W ) + 1 steps.')
A = '( A e. Fin /\\ Z e. A /\\ W e. Word A )'
a = w.s([], 'simp1', '( %s -> A e. Fin )' % A); zz = w.s([], 'simp2', '( %s -> Z e. A )' % A); ww = w.s([], 'simp3', '( %s -> W e. Word A )' % A)
ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A); wx = w.s([ww], 'elexd', '( %s -> W e. _V )' % A)
az = w.s([a, zz], 'jca', '( %s -> ( A e. Fin /\\ Z e. A ) )' % A)
ix = w.s([], 'opex', '%s e. _V' % REVM); ix2 = w.s([ix], 'a1i', '( %s -> %s e. _V )' % (A, REVM))
tx = w.s([], 'opex', '%s e. _V' % T1); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T1))
N = '( ( # ` W ) + 1 )'
ln = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % A); nn = w.s([ln, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (A, N))
extra = g1rules(w, A, ax); SM = {'A': ax, 'W': wx}
MG = lambda m: '( 1st ` ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % m
MK0 = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % REVM; MK1 = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % REVM
W0 = 'Word ( %s ` %s )' % (MG(REVM), MK0); W1 = '( Word ( %s ` %s ) |_| 1o )' % (MG(REVM), MK1)
ev0, w0t = evaluate(w, A, W0, SM, extra_rules=extra); assert w0t == 'Word A', w0t
ev1, w1t = evaluate(w, A, W1, SM, extra_rules=extra); assert w1t == '( Word A |_| 1o )', w1t
RW = '( reverse ` W )'
rc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> %s e. Word A )' % (A, RW)); rx = w.s([rc], 'elexd', '( %s -> %s e. _V )' % (A, RW))
m0 = w.s([ww, ev0], 'eleqtrrd', '( %s -> W e. %s )' % (A, W0))
l1 = w.s([rc, w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. ( Word A |_| 1o ) )' % (A, RW)); m1 = w.s([l1, ev1], 'eleqtrrd', '( %s -> ( inl ` %s ) e. %s )' % (A, RW, W1))
mm = w.s([m0, m1], 'jca', '( %s -> ( W e. %s /\\ ( inl ` %s ) e. %s ) )' % (A, W0, RW, W1))
MT = '( 1st ` ( 1st ` %s ) )' % REVM; MP = '( 2nd ` ( 2nd ` %s ) )' % REVM
OPT = 'if ( ( inl ` %s ) = %s , %s , ( inl ` ( %s TM2halt ( 2nd ` ( inl ` %s ) ) ) ) )' % (RW, NONE, NONE, REVM, RW)
REL = '( %s TM2init W ) ( ( %s TM2step %s ) EvalsToInTime %s ) %s' % (REVM, MT, MP, N, OPT)
b = w.s([ix2, nn, mm, w.inst('tm2outtbr')], 'syl3anc', '( %s -> ( W ( %s TM2OutputsInTime %s ) ( inl ` %s ) <-> %s ) )' % (A, REVM, N, RW, REL))
z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
ne = w.s([rx, z2, w.inst('inlneinr')], 'syl2anc', '( %s -> ( inl ` %s ) =/= %s )' % (A, RW, NONE)); ne2 = w.s([ne], 'neneqd', '( %s -> -. ( inl ` %s ) = %s )' % (A, RW, NONE))
iv = w.s([rx, w.inst('inlval')], 'syl', '( %s -> ( inl ` %s ) = <. (/) , %s >. )' % (A, RW, RW)); iv2 = w.s([iv], 'fveq2d', '( %s -> ( 2nd ` ( inl ` %s ) ) = ( 2nd ` <. (/) , %s >. ) )' % (A, RW, RW))
iv3 = w.s([z2, rx, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. (/) , %s >. ) = %s )' % (A, RW, RW)); iv4 = w.s([iv2, iv3], 'eqtrd', '( %s -> ( 2nd ` ( inl ` %s ) ) = %s )' % (A, RW, RW))
hc = w.s([a, rc, w.inst('revhaltc')], 'syl2anc', '( %s -> ( %s TM2halt %s ) = %s )' % (A, REVM, RW, HALTC(RW)))
ic = w.s([a, ww, w.inst('revinitc')], 'syl2anc', '( %s -> ( %s TM2init W ) = %s )' % (A, REVM, Cf(NONE, 'W', '(/)')))
def ex2(n):
    r = extra(n)
    if r: return r
    if n.text() == '( 2nd ` ( inl ` %s ) )' % RW: return (RW, iv4)
    if n.text() == '( %s TM2halt %s )' % (REVM, RW): return (HALTC(RW), hc)
    if n.text() == '( %s TM2init W )' % REVM: return (Cf(NONE, 'W', '(/)'), ic)
    return None
evr, REL2 = evaluate(w, A, REL, SM, extra_rules=ex2, ifrules={'( inl ` %s ) = %s' % (RW, NONE): (False, ne2)}, wff=True)
CI = Cf(NONE, 'W', '(/)')
assert REL2 == '%s ( %s EvalsToInTime %s ) ( inl ` %s )' % (CI, STEP1, N, HALTC(RW)), REL2
b2 = w.s([b, evr], 'bitrd', '( %s -> ( W ( %s TM2OutputsInTime %s ) ( inl ` %s ) <-> %s ) )' % (A, REVM, N, RW, REL2))
# evalsttlem
sf = w.s([az, w.inst('revstepf')], 'syl', '( %s -> %s : %s --> %s )' % (A, STEP1, CFG1, DJC))
cx = w.s([], 'fvex', '%s e. _V' % CFG1); cx2 = w.s([cx], 'a1i', '( %s -> %s e. _V )' % (A, CFG1))
c1 = w.s([cx2, sf], 'jca', '( %s -> ( %s e. _V /\\ %s : %s --> %s ) )' % (A, CFG1, STEP1, CFG1, DJC))
nf = w.s([], 'nn0fz0', '( %s e. NN0 <-> %s e. ( 0 ... %s ) )' % (N, N, N)); nf2 = w.s([nn, nf], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (A, N, N))
c2 = w.s([nn, nf2], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. ( 0 ... %s ) ) )' % (A, N, N, N))
e0 = w.s([], 'wrd0', '(/) e. Word A'); e0b = w.s([e0], 'a1i', '( %s -> (/) e. Word A )' % A)
ns = w.s([w.s([], '0lt1o', '(/) e. 1o'), w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, S1)); nsb = w.s([ns], 'a1i', '( %s -> %s e. %s )' % (A, NONE, S1))
h3 = w.s([ww, e0b, nsb], '3jca', '( %s -> ( W e. Word A /\\ (/) e. Word A /\\ %s e. %s ) )' % (A, NONE, S1))
B0w = '( ( A e. Fin /\\ Z e. A ) /\\ ( W e. Word A /\\ (/) e. Word A /\\ %s e. %s ) )' % (NONE, S1)
b0w = w.s([az, h3], 'jca', '( %s -> %s )' % (A, B0w))
cf = w.s([b0w, w.inst('revcfg')], 'syl', '( %s -> %s e. %s )' % (A, CI, CFG1))
ev_ = w.s([c1, c2, cf, w.inst('evalsttlem')], 'syl3anc', '( %s -> %s ( %s EvalsToInTime %s ) ( ( %s ^r %s ) ` ( inl ` %s ) ) )' % (A, CI, STEP1, N, OS, N, CI))
# revrun instantiation
rr = w.s([ln, w.inst('revrun')], 'syl', '( %s -> %s )' % (A, PH('( # ` W )').replace(AZ, '( A e. Fin /\\ Z e. A )', 1)))
rr2 = w.s([az, rr], 'mpd', '( %s -> A. a e. Word A ( ( # ` a ) = ( # ` W ) -> %s ) )' % (A, INNER('( # ` W )', 'a')))
la = w.s([], 'id', '( a = W -> a = W )'); ca, bodyW = w.wcongr('( ( # ` a ) = ( # ` W ) -> %s )' % INNER('( # ` W )', 'a'), {'a': 'W'}, 'a = W', {'a': la})
i1 = w.s([ca, rr2, ww], 'rspcdva', '( %s -> %s )' % (A, bodyW))
eqw = w.s([], 'eqid', '( # ` W ) = ( # ` W )'); eqw2 = w.s([eqw], 'a1i', '( %s -> ( # ` W ) = ( # ` W ) )' % A)
i2 = w.s([eqw2, i1], 'mpd', '( %s -> %s )' % (A, INNER('( # ` W )', 'W')))
lb = w.s([], 'id', '( b = (/) -> b = (/) )'); cb, bodyE = w.wcongr('A. c e. %s %s' % (S1, G('( # ` W )', 'c', 'W', 'b')), {'b': '(/)'}, 'b = (/)', {'b': lb})
i3 = w.s([cb, i2, e0b], 'rspcdva', '( %s -> %s )' % (A, bodyE))
lc = w.s([], 'id', '( c = %s -> c = %s )' % (NONE, NONE)); cc, bodyN = w.wcongr(G('( # ` W )', 'c', 'W', '(/)'), {'c': NONE}, 'c = %s' % NONE, {'c': lc})
i4 = w.s([cc, i3, nsb], 'rspcdva', '( %s -> %s )' % (A, bodyN))
assert bodyN == G('( # ` W )', NONE, 'W', '(/)')
cr = w.s([rc, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (A, RW, RW))
cg, _ = w.rewrite('( inl ` %s )' % HALTC('( %s ++ (/) )' % RW), {'( %s ++ (/) )' % RW: (RW, cr)}, A)
i5 = w.s([i4, cg], 'eqtrd', '( %s -> ( ( %s ^r %s ) ` ( inl ` %s ) ) = ( inl ` %s ) )' % (A, OS, N, CI, HALTC(RW)))
fin = w.s([ev_, i5], 'breqtrd', '( %s -> %s )' % (A, REL2))
w.qed([fin, b2], 'mpbird', '( %s -> W ( %s TM2OutputsInTime %s ) ( inl ` %s ) )' % (A, REVM, N, RW))
run(w)
