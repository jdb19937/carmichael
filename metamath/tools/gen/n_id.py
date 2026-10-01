import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
NONE = '( inr ` (/) )'
Gt = lambda T: '( 1st ` ( 1st ` %s ) )' % T
# ---- tm2initstk (general)
w = W('tm2initstk', 'The stacks of the initial and halting configurations: a word on one stack, the empty word elsewhere.')
T = 'T'; STK = '( TM2Stk ` T )'; KT = 'dom ' + Gt(T); WD = lambda k: 'Word ( %s ` %s )' % (Gt(T), k)
MP = '( j e. %s |-> if ( j = K , W , (/) ) )' % KT
IXP = 'X_ k e. %s Word ( %s ` k )' % (KT, Gt(T))
A = '( T e. V /\\ K e. %s /\\ W e. %s )' % (KT, WD('K'))
t = w.s([], 'simp1', '( %s -> T e. V )' % A); kk = w.s([], 'simp2', '( %s -> K e. %s )' % (A, KT)); ww = w.s([], 'simp3', '( %s -> W e. %s )' % (A, WD('K')))
vi = w.inst('tm2stkval'); v = w.s([t, vi], 'syl', '( %s -> %s = %s )' % (A, STK, IXP))
gx = w.s([], 'fvex', '%s e. _V' % Gt(T)); dxi = w.inst('dmexg'); dx = w.s([gx, dxi], 'ax-mp', '%s e. _V' % KT)
mxi = w.inst('mptexg'); mx = w.s([dx, mxi], 'ax-mp', '%s e. _V' % MP); mx2 = w.s([mx], 'a1i', '( %s -> %s e. _V )' % (A, MP))
wx = w.s([ww], 'elexd', '( %s -> W e. _V )' % A); zx = w.s([], '0ex', '(/) e. _V'); zx2 = w.s([zx], 'a1i', '( %s -> (/) e. _V )' % A)
ixi = w.inst('ifexg'); ix = w.s([wx, zx2, ixi], 'syl2anc', '( %s -> if ( j = K , W , (/) ) e. _V )' % A)
ral = w.s([ix], 'ralrimivw', '( %s -> A. j e. %s if ( j = K , W , (/) ) e. _V )' % (A, KT))
e = w.s([], 'eqid', '%s = %s' % (MP, MP)); fng = w.s([e], 'mptfng', '( A. j e. %s if ( j = K , W , (/) ) e. _V <-> %s Fn %s )' % (KT, MP, KT))
fn = w.s([ral, fng], 'sylib', '( %s -> %s Fn %s )' % (A, MP, KT))
A2 = '( %s /\\ k e. %s )' % (A, KT)
k2 = w.s([], 'simpr', '( %s -> k e. %s )' % (A2, KT)); ixk = w.s([wx, zx2, w.inst('ifexg')], 'syl2anc', '( %s -> if ( k = K , W , (/) ) e. _V )' % A)
ix2 = w.s([ixk], 'adantr', '( %s -> if ( k = K , W , (/) ) e. _V )' % A2)
cb0 = w.s([], 'eqeq1', '( j = k -> ( j = K <-> k = K ) )'); cb1 = w.s([cb0], 'ifbid', '( j = k -> if ( j = K , W , (/) ) = if ( k = K , W , (/) ) )')
cb = w.s([cb1], 'cbvmptv', '%s = ( k e. %s |-> if ( k = K , W , (/) ) )' % (MP, KT))
fv = w.s([cb], 'fvmpt2', '( ( k e. %s /\\ if ( k = K , W , (/) ) e. _V ) -> ( %s ` k ) = if ( k = K , W , (/) ) )' % (KT, MP))
fv2 = w.s([k2, ix2, fv], 'syl2anc', '( %s -> ( %s ` k ) = if ( k = K , W , (/) ) )' % (A2, MP))
A3 = '( %s /\\ k = K )' % A2
e3 = w.s([], 'simpr', '( %s -> k = K )' % A3); i3 = w.s([e3], 'iftrued', '( %s -> if ( k = K , W , (/) ) = W )' % A3)
w3 = w.s([ww], 'ad2antrr', '( %s -> W e. %s )' % (A3, WD('K')))
g3 = w.s([e3], 'fveq2d', '( %s -> ( %s ` k ) = ( %s ` K ) )' % (A3, Gt(T), Gt(T))); wqi = w.inst('wrdeq'); g3b = w.s([g3, wqi], 'syl', '( %s -> %s = %s )' % (A3, WD('k'), WD('K')))
m3 = w.s([i3, w3], 'eqeltrd', '( %s -> if ( k = K , W , (/) ) e. %s )' % (A3, WD('K')))
m3b = w.s([m3, g3b], 'eleqtrrd', '( %s -> if ( k = K , W , (/) ) e. %s )' % (A3, WD('k')))
A4 = '( %s /\\ k =/= K )' % A2
n4 = w.s([], 'simpr', '( %s -> k =/= K )' % A4); n4b = w.s([n4], 'neneqd', '( %s -> -. k = K )' % A4)
i4 = w.s([n4b], 'iffalsed', '( %s -> if ( k = K , W , (/) ) = (/) )' % A4)
z4 = w.s([], 'wrd0', '(/) e. %s' % WD('k')); z4b = w.s([z4], 'a1i', '( %s -> (/) e. %s )' % (A4, WD('k')))
m4 = w.s([i4, z4b], 'eqeltrd', '( %s -> if ( k = K , W , (/) ) e. %s )' % (A4, WD('k')))
m = w.s([m3b, m4], 'pm2.61dane', '( %s -> if ( k = K , W , (/) ) e. %s )' % (A2, WD('k')))
m2 = w.s([fv2, m], 'eqeltrd', '( %s -> ( %s ` k ) e. %s )' % (A2, MP, WD('k')))
r = w.s([m2], 'ralrimiva', '( %s -> A. k e. %s ( %s ` k ) e. %s )' % (A, KT, MP, WD('k')))
ex = w.s([], 'elixp2', '( %s e. %s <-> ( %s e. _V /\\ %s Fn %s /\\ A. k e. %s ( %s ` k ) e. %s ) )' % (MP, IXP, MP, MP, KT, KT, MP, WD('k')))
q = w.s([mx2, fn, r, ex], 'syl3anbrc', '( %s -> %s e. %s )' % (A, MP, IXP))
w.qed([q, v], 'eleqtrrd', '( %s -> %s e. %s )' % (A, MP, STK))
run(w)

# ---- the halt machine
G0 = '{ <. (/) , A >. }'; T0 = '<. <. %s , 1o >. , 1o >.' % G0; HALT = '<. 6 , (/) >.'; M0 = '{ <. (/) , %s >. }' % HALT
IDM = '<. <. %s , <. (/) , (/) >. >. , <. <. (/) , (/) >. , %s >. >.' % (T0, M0)
D0 = '( k e. { (/) } |-> if ( k = (/) , W , (/) ) )'
D0J = '( j e. { (/) } |-> if ( j = (/) , W , (/) ) )'
INITC = '<. ( inl ` (/) ) , <. (/) , %s >. >.' % D0; HALTC = '<. %s , <. (/) , %s >. >.' % (NONE, D0)
STEP = '( %s TM2step %s )' % (T0, M0)
def gproj_rules(w, A, ax):
    """rules: ( { <. (/) , A >. } ` (/) ) -> A ; dom { <. (/) , A >. } -> { (/) }"""
    z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
    fi = w.inst('fvsng'); f = w.s([z2, ax, fi], 'syl2anc', '( %s -> ( %s ` (/) ) = A )' % (A, G0))
    di = w.inst('dmsnopg'); d = w.s([ax, di], 'syl', '( %s -> dom %s = { (/) } )' % (A, G0))
    def extra(n):
        if n.text() == '( %s ` (/) )' % G0: return ('A', f)
        if n.text() == 'dom %s' % G0: return ('{ (/) }', d)
        return None
    return extra

# tm2idm
w = W('tm2idm', 'The halt machine (Mathlib\'s idComputer on the alphabet A): one stack, one label, one state, program halt. It is a bundled finite machine.')
A = 'A e. Fin'
ax = w.s([], 'elex', '( A e. Fin -> A e. _V )')
sx = w.s([], 'snex', '%s e. _V' % G0); sx2 = w.s([sx], 'a1i', '( %s -> %s e. _V )' % (A, G0))
ox = w.s([], '1oex', '1o e. _V'); ox2 = w.s([ox], 'a1i', '( %s -> 1o e. _V )' % A)
zx = w.s([], '0ex', '(/) e. _V'); zx2 = w.s([zx], 'a1i', '( %s -> (/) e. _V )' % A)
mx = w.s([], 'snex', '%s e. _V' % M0); mx2 = w.s([mx], 'a1i', '( %s -> %s e. _V )' % (A, M0))
j1 = w.s([sx2, ox2, ox2], '3jca', '( %s -> ( %s e. _V /\\ 1o e. _V /\\ 1o e. _V ) )' % (A, G0))
j2 = w.s([zx2, zx2], 'jca', '( %s -> ( (/) e. _V /\\ (/) e. _V ) )' % A)
j3 = w.s([zx2, zx2, mx2], '3jca', '( %s -> ( (/) e. _V /\\ (/) e. _V /\\ %s e. _V ) )' % (A, M0))
ei = w.inst('elfintm2')
COND = '( ( Fun %s /\\ dom %s e. Fin /\\ ( (/) e. dom %s /\\ (/) e. dom %s /\\ ( %s ` (/) ) e. Fin ) ) /\\ ( 1o e. Fin /\\ (/) e. 1o ) /\\ ( 1o e. Fin /\\ (/) e. 1o /\\ %s : 1o --> ( TM2Stmt ` %s ) ) )' % (G0, G0, G0, G0, G0, M0, T0)
el = w.s([j1, j2, j3, ei], 'syl3anc', '( %s -> ( %s e. FinTM2 <-> %s ) )' % (A, IDM, COND))
extra = gproj_rules(w, A, ax)
ev, COND2 = evaluate(w, A, COND, {}, extra_rules=extra, wff=True)
el2 = w.s([el, ev], 'bitrd', '( %s -> ( %s e. FinTM2 <-> %s ) )' % (A, IDM, COND2))
zx0 = w.s([], '0ex', '(/) e. _V'); zx0b = w.s([zx0], 'a1i', '( %s -> (/) e. _V )' % A)
c1i = w.inst('funsng'); c1b = w.s([zx0b, ax, c1i], 'syl2anc', '( %s -> Fun %s )' % (A, G0))
c2 = w.s([], 'snfi', '{ (/) } e. Fin'); c2b = w.s([c2], 'a1i', '( %s -> { (/) } e. Fin )' % A)
c3i = w.inst('snidg'); c3 = w.s([zx, c3i], 'ax-mp', '(/) e. { (/) }'); c3b = w.s([c3], 'a1i', '( %s -> (/) e. { (/) } )' % A)
c4 = w.s([], 'id', '( %s -> A e. Fin )' % A)
c5 = w.s([c3b, c3b, c4], '3jca', '( %s -> ( (/) e. { (/) } /\\ (/) e. { (/) } /\\ A e. Fin ) )' % A)
p1 = w.s([c1b, c2b, c5], '3jca', '( %s -> ( Fun %s /\\ { (/) } e. Fin /\\ ( (/) e. { (/) } /\\ (/) e. { (/) } /\\ A e. Fin ) ) )' % (A, G0))
o1 = w.s([], '1onn', '1o e. _om'); o2i = w.inst('nnfi'); o2 = w.s([o1, o2i], 'ax-mp', '1o e. Fin'); o2b = w.s([o2], 'a1i', '( %s -> 1o e. Fin )' % A)
o3 = w.s([], '0lt1o', '(/) e. 1o'); o3b = w.s([o3], 'a1i', '( %s -> (/) e. 1o )' % A)
p2 = w.s([o2b, o3b], 'jca', '( %s -> ( 1o e. Fin /\\ (/) e. 1o ) )' % A)
# M0 : 1o --> STMT
hx = w.s([], 'opex', '%s e. _V' % HALT)
f1 = w.s([], 'f1osn', '%s : { (/) } -1-1-onto-> { %s }' % (M0, HALT)); f1i = w.inst('f1of'); f2 = w.s([f1, f1i], 'ax-mp', '%s : { (/) } --> { %s }' % (M0, HALT))
d1 = w.s([], 'df1o2', '1o = { (/) }'); d2 = w.s([d1], 'feq2i', '( %s : 1o --> { %s } <-> %s : { (/) } --> { %s } )' % (M0, HALT, M0, HALT))
f3 = w.s([f2, d2], 'mpbir', '%s : 1o --> { %s }' % (M0, HALT)); f3b = w.s([f3], 'a1i', '( %s -> %s : 1o --> { %s } )' % (A, M0, HALT))
tx = w.s([], 'opex', '%s e. _V' % T0); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T0))
hi = w.inst('tm2halt'); h = w.s([tx2, hi], 'syl', '( %s -> %s e. ( TM2Stmt ` %s ) )' % (A, HALT, T0))
h2 = w.s([h], 'snssd', '( %s -> { %s } C_ ( TM2Stmt ` %s ) )' % (A, HALT, T0))
fsi = w.inst('fss'); f4 = w.s([f3b, h2, fsi], 'syl2anc', '( %s -> %s : 1o --> ( TM2Stmt ` %s ) )' % (A, M0, T0))
p3 = w.s([o2b, o3b, f4], '3jca', '( %s -> ( 1o e. Fin /\\ (/) e. 1o /\\ %s : 1o --> ( TM2Stmt ` %s ) ) )' % (A, M0, T0))
p = w.s([p1, p2, p3], '3jca', '( %s -> %s )' % (A, COND2))
w.qed([p, el2], 'mpbird', '( %s -> %s e. FinTM2 )' % (A, IDM))
run(w)

# tm2idinit / tm2idhaltc
for label, lem, desc, CF in (('tm2idinit', 'tm2initval', 'The initial configuration of the halt machine on input W.', INITC),
                              ('tm2idhaltc', 'tm2haltval', 'The halting configuration of the halt machine with output W.', HALTC)):
    w = W(label, desc)
    A = '( A e. Fin /\\ W e. Word A )'
    a = w.s([], 'simpl', '( %s -> A e. Fin )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
    ww = w.s([], 'simpr', '( %s -> W e. Word A )' % A); wx = w.s([ww], 'elexd', '( %s -> W e. _V )' % A)
    ix = w.s([], 'opex', '%s e. _V' % IDM); ix2 = w.s([ix], 'a1i', '( %s -> %s e. _V )' % (A, IDM))
    vi = w.inst(lem)
    body = {'tm2initval': defbody('df-tm2init'), 'tm2haltval': defbody('df-tm2halt')}[lem]
    val = sub(body.split('|->', 1)[1].rsplit(')', 1)[0].strip(), {'m': IDM, 'l': 'W'})
    op = {'tm2initval': 'TM2init', 'tm2haltval': 'TM2halt'}[lem]
    v = w.s([ix2, wx, vi], 'syl2anc', '( %s -> ( %s %s W ) = %s )' % (A, IDM, op, val))
    extra = gproj_rules(w, A, ax)
    ev, res = evaluate(w, A, val, {}, extra_rules=extra)
    assert res == CF, (res, CF)
    w.qed([v, ev], 'eqtrd', '( %s -> ( %s %s W ) = %s )' % (A, IDM, op, CF))
    run(w)

# tm2idstep: ( STEP ` INITC ) = ( inl ` HALTC )
w = W('tm2idstep', 'One step of the halt machine from its initial configuration reaches the halting configuration.')
A = '( A e. Fin /\\ W e. Word A )'
a = w.s([], 'simpl', '( %s -> A e. Fin )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
ww = w.s([], 'simpr', '( %s -> W e. Word A )' % A)
tx = w.s([], 'opex', '%s e. _V' % T0); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T0))
mx = w.s([], 'snex', '%s e. _V' % M0); mx2 = w.s([mx], 'a1i', '( %s -> %s e. _V )' % (A, M0))
tm = w.s([tx2, mx2], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A, T0, M0))
z = w.s([], '0lt1o', '(/) e. 1o'); z2 = w.s([z], 'a1i', '( %s -> (/) e. 1o )' % A)
# D0 e. ( TM2Stk ` T0 )
extra = gproj_rules(w, A, ax)
zx = w.s([], '0ex', '(/) e. _V'); zx2 = w.s([zx], 'a1i', '( %s -> (/) e. _V )' % A)
c3i = w.inst('snidg'); c3 = w.s([zx, c3i], 'ax-mp', '(/) e. { (/) }'); c3b = w.s([c3], 'a1i', '( %s -> (/) e. { (/) } )' % A)
KT0 = 'dom %s' % Gt(T0)
ev1, kt = evaluate(w, A, KT0, {}, extra_rules=extra)   # ( A -> dom ( 1st ` ( 1st ` T0 ) ) = { (/) } )
assert kt == '{ (/) }'
k0 = w.s([c3b, ev1], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, KT0))
WD0 = 'Word ( %s ` (/) )' % Gt(T0)
ev2, wd = evaluate(w, A, WD0, {}, extra_rules=extra); assert wd == 'Word A', wd
w0 = w.s([ww, ev2], 'eleqtrrd', '( %s -> W e. %s )' % (A, WD0))
si = w.inst('tm2initstk'); s0 = w.s([tx2, k0, w0, si], 'syl3anc', '( %s -> ( j e. %s |-> if ( j = (/) , W , (/) ) ) e. ( TM2Stk ` %s ) )' % (A, KT0, T0))
mq = w.s([ev1], 'mpteq1d', '( %s -> ( j e. %s |-> if ( j = (/) , W , (/) ) ) = %s )' % (A, KT0, D0J))
cb0 = w.s([], 'eqeq1', '( j = k -> ( j = (/) <-> k = (/) ) )'); cb1 = w.s([cb0], 'ifbid', '( j = k -> if ( j = (/) , W , (/) ) = if ( k = (/) , W , (/) ) )')
cb = w.s([cb1], 'cbvmptv', '%s = %s' % (D0J, D0)); mq2 = w.s([mq, cb], 'eqtrdi', '( %s -> ( j e. %s |-> if ( j = (/) , W , (/) ) ) = %s )' % (A, KT0, D0))
s1 = w.s([mq2, s0], 'eqeltrrd', '( %s -> %s e. ( TM2Stk ` %s ) )' % (A, D0, T0))
# projections of T0: L = 1o, S = 1o
Lt0 = '( 2nd ` ( 1st ` %s ) )' % T0; St0 = '( 2nd ` %s )' % T0
evL, lt = evaluate(w, A, Lt0, {}, extra_rules=extra); assert lt == '1o'
evS, st_ = evaluate(w, A, St0, {}, extra_rules=extra); assert st_ == '1o'
zl = w.s([z2, evL], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, Lt0)); zs = w.s([z2, evS], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, St0))
sd = w.s([zs, s1], 'jca', '( %s -> ( (/) e. %s /\\ %s e. ( TM2Stk ` %s ) ) )' % (A, St0, D0, T0))
hy = w.s([zl, sd], 'jca', '( %s -> ( (/) e. %s /\\ ( (/) e. %s /\\ %s e. ( TM2Stk ` %s ) ) ) )' % (A, Lt0, St0, D0, T0))
sti = w.inst('tm2stepsome'); stp = w.s([tm, hy, sti], 'syl2anc', '( %s -> ( %s ` %s ) = ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. (/) , %s >. ) ) )' % (A, STEP, INITC, M0, T0, D0))
hx = w.s([], 'opex', '%s e. _V' % HALT); fvi = w.inst('fvsng'); fv = w.s([zx, hx, fvi], 'mp2an', '( %s ` (/) ) = %s' % (M0, HALT))
fv2 = w.s([fv], 'a1i', '( %s -> ( %s ` (/) ) = %s )' % (A, M0, HALT))
fv3 = w.s([fv2], 'oveq1d', '( %s -> ( ( %s ` (/) ) ( TM2sa ` %s ) <. (/) , %s >. ) = ( %s ( TM2sa ` %s ) <. (/) , %s >. ) )' % (A, M0, T0, D0, HALT, T0, D0))
hi = w.inst('tm2sahalt'); h = w.s([tx2, sd, hi], 'syl2anc', '( %s -> ( %s ( TM2sa ` %s ) <. (/) , %s >. ) = %s )' % (A, HALT, T0, D0, HALTC))
h2 = w.s([fv3, h], 'eqtrd', '( %s -> ( ( %s ` (/) ) ( TM2sa ` %s ) <. (/) , %s >. ) = %s )' % (A, M0, T0, D0, HALTC))
h3 = w.s([h2], 'fveq2d', '( %s -> ( inl ` ( ( %s ` (/) ) ( TM2sa ` %s ) <. (/) , %s >. ) ) = ( inl ` %s ) )' % (A, M0, T0, D0, HALTC))
w.qed([stp, h3], 'eqtrd', '( %s -> ( %s ` %s ) = ( inl ` %s ) )' % (A, STEP, INITC, HALTC))
run(w)

# tm2idhalt
w = W('tm2idhalt', 'Test program 1 (Mathlib\'s idComputableInPolyTime): the halt machine outputs its input in one step.')
A = '( A e. Fin /\\ W e. Word A )'
a = w.s([], 'simpl', '( %s -> A e. Fin )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
ww = w.s([], 'simpr', '( %s -> W e. Word A )' % A); wx = w.s([ww], 'elexd', '( %s -> W e. _V )' % A)
ix = w.s([], 'opex', '%s e. _V' % IDM); ix2 = w.s([ix], 'a1i', '( %s -> %s e. _V )' % (A, IDM))
tx = w.s([], 'opex', '%s e. _V' % T0); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T0))
n1 = w.s([], '1nn0', '1 e. NN0'); n1b = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % A)
extra = gproj_rules(w, A, ax)
MG = lambda m: Gt('( 1st ` ( 1st ` %s ) )' % m)
MK0 = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % IDM; MK1 = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % IDM
W0 = 'Word ( %s ` %s )' % (MG(IDM), MK0); W1 = '( Word ( %s ` %s ) |_| 1o )' % (MG(IDM), MK1)
ev0, w0t = evaluate(w, A, W0, {}, extra_rules=extra); assert w0t == 'Word A', w0t
ev1, w1t = evaluate(w, A, W1, {}, extra_rules=extra); assert w1t == '( Word A |_| 1o )', w1t
m0 = w.s([ww, ev0], 'eleqtrrd', '( %s -> W e. %s )' % (A, W0))
li = w.inst('djulcl'); l1 = w.s([ww, li], 'syl', '( %s -> ( inl ` W ) e. ( Word A |_| 1o ) )' % A)
m1 = w.s([l1, ev1], 'eleqtrrd', '( %s -> ( inl ` W ) e. %s )' % (A, W1))
mm = w.s([m0, m1], 'jca', '( %s -> ( W e. %s /\\ ( inl ` W ) e. %s ) )' % (A, W0, W1))
bi = w.inst('tm2outtbr')
MT = '( 1st ` ( 1st ` %s ) )' % IDM; MP = '( 2nd ` ( 2nd ` %s ) )' % IDM
OPT = 'if ( ( inl ` W ) = %s , %s , ( inl ` ( %s TM2halt ( 2nd ` ( inl ` W ) ) ) ) )' % (NONE, NONE, IDM)
REL = '( %s TM2init W ) ( ( %s TM2step %s ) EvalsToInTime 1 ) %s' % (IDM, MT, MP, OPT)
b = w.s([ix2, n1b, mm, bi], 'syl3anc', '( %s -> ( W ( %s TM2OutputsInTime 1 ) ( inl ` W ) <-> %s ) )' % (A, IDM, REL))
# simplify REL
zx = w.s([], '0ex', '(/) e. _V'); zx2 = w.s([zx], 'a1i', '( %s -> (/) e. _V )' % A)
nei = w.inst('inlneinr'); ne = w.s([wx, zx2, nei], 'syl2anc', '( %s -> ( inl ` W ) =/= %s )' % (A, NONE)); ne2 = w.s([ne], 'neneqd', '( %s -> -. ( inl ` W ) = %s )' % (A, NONE))
ivi = w.inst('inlval'); iv = w.s([wx, ivi], 'syl', '( %s -> ( inl ` W ) = <. (/) , W >. )' % A)
iv2 = w.s([iv], 'fveq2d', '( %s -> ( 2nd ` ( inl ` W ) ) = ( 2nd ` <. (/) , W >. ) )' % A)
o2i = w.inst('op2ndg'); iv3 = w.s([zx2, wx, o2i], 'syl2anc', '( %s -> ( 2nd ` <. (/) , W >. ) = W )' % A)
iv4 = w.s([iv2, iv3], 'eqtrd', '( %s -> ( 2nd ` ( inl ` W ) ) = W )' % A)
hci = w.inst('tm2idhaltc'); hc = w.s([a, ww, hci], 'syl2anc', '( %s -> ( %s TM2halt W ) = %s )' % (A, IDM, HALTC))
ici = w.inst('tm2idinit'); ic = w.s([a, ww, ici], 'syl2anc', '( %s -> ( %s TM2init W ) = %s )' % (A, IDM, INITC))
def extra2(n):
    r = extra(n)
    if r: return r
    if n.text() == '( 2nd ` ( inl ` W ) )': return ('W', iv4)
    if n.text() == '( %s TM2halt W )' % IDM: return (HALTC, hc)
    if n.text() == '( %s TM2init W )' % IDM: return (INITC, ic)
    return None
evr, REL2 = evaluate(w, A, REL, {}, extra_rules=extra2, ifrules={'( inl ` W ) = %s' % NONE: (False, ne2)}, wff=True)
assert REL2 == '%s ( %s EvalsToInTime 1 ) ( inl ` %s )' % (INITC, STEP, HALTC), REL2
b2 = w.s([b, evr], 'bitrd', '( %s -> ( W ( %s TM2OutputsInTime 1 ) ( inl ` W ) <-> %s ) )' % (A, IDM, REL2))
# prove REL2 via evalsttlem
CFG0 = '( TM2Cfg ` %s )' % T0; DJC = '( %s |_| 1o )' % CFG0; OS = '( OptStep ` %s )' % STEP
mx = w.s([], 'snex', '%s e. _V' % M0); mx2 = w.s([mx], 'a1i', '( %s -> %s e. _V )' % (A, M0))
Lt0 = '( 2nd ` ( 1st ` %s ) )' % T0
evL, lt = evaluate(w, A, Lt0, {}, extra_rules=extra); assert lt == '1o'
hx = w.s([], 'opex', '%s e. _V' % HALT)
f1 = w.s([], 'f1osn', '%s : { (/) } -1-1-onto-> { %s }' % (M0, HALT)); f1i = w.inst('f1of'); f2 = w.s([f1, f1i], 'ax-mp', '%s : { (/) } --> { %s }' % (M0, HALT))
d1 = w.s([], 'df1o2', '1o = { (/) }'); d2 = w.s([d1], 'feq2i', '( %s : 1o --> { %s } <-> %s : { (/) } --> { %s } )' % (M0, HALT, M0, HALT))
f3 = w.s([f2, d2], 'mpbir', '%s : 1o --> { %s }' % (M0, HALT)); f3b = w.s([f3], 'a1i', '( %s -> %s : 1o --> { %s } )' % (A, M0, HALT))
hi = w.inst('tm2halt'); h = w.s([tx2, hi], 'syl', '( %s -> %s e. ( TM2Stmt ` %s ) )' % (A, HALT, T0))
h2 = w.s([h], 'snssd', '( %s -> { %s } C_ ( TM2Stmt ` %s ) )' % (A, HALT, T0))
fsi = w.inst('fss'); f4 = w.s([f3b, h2, fsi], 'syl2anc', '( %s -> %s : 1o --> ( TM2Stmt ` %s ) )' % (A, M0, T0))
evLr = w.s([evL], 'eqcomd', '( %s -> 1o = %s )' % (A, Lt0))
f5 = w.s([evLr], 'feq2d', '( %s -> ( %s : 1o --> ( TM2Stmt ` %s ) <-> %s : %s --> ( TM2Stmt ` %s ) ) )' % (A, M0, T0, M0, Lt0, T0))
f6 = w.s([f4, f5], 'mpbid', '( %s -> %s : %s --> ( TM2Stmt ` %s ) )' % (A, M0, Lt0, T0))
sfi = w.inst('tm2stepf'); sf = w.s([tx2, f6, sfi], 'syl2anc', '( %s -> %s : %s --> %s )' % (A, STEP, CFG0, DJC))
cx = w.s([], 'fvex', '%s e. _V' % CFG0); cx2 = w.s([cx], 'a1i', '( %s -> %s e. _V )' % (A, CFG0))
c1 = w.s([cx2, sf], 'jca', '( %s -> ( %s e. _V /\\ %s : %s --> %s ) )' % (A, CFG0, STEP, CFG0, DJC))
n0 = w.s([], 'nn0fz0', '( 1 e. NN0 <-> 1 e. ( 0 ... 1 ) )'); n01 = w.s([n1, n0], 'mpbi', '1 e. ( 0 ... 1 )'); n01b = w.s([n01], 'a1i', '( %s -> 1 e. ( 0 ... 1 ) )' % A)
c2 = w.s([n1b, n01b], 'jca', '( %s -> ( 1 e. NN0 /\\ 1 e. ( 0 ... 1 ) ) )' % A)
# INITC e. CFG0: from tm2idinit and init cfg membership: via tm2cfgval
ici2 = w.inst('tm2idinit')
# build membership directly: ( inl ` (/) ) e. ( 1o |_| 1o ) ... use CFG = ( ( L |_| 1o ) X. ( S X. STK ) ) with L, S projections of T0
z = w.s([], '0lt1o', '(/) e. 1o'); z2 = w.s([z], 'a1i', '( %s -> (/) e. 1o )' % A)
St0 = '( 2nd ` %s )' % T0; evS, st_ = evaluate(w, A, St0, {}, extra_rules=extra)
zl = w.s([z2, evL], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, Lt0)); zs = w.s([z2, evS], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, St0))
c3i = w.inst('snidg'); c3 = w.s([zx, c3i], 'ax-mp', '(/) e. { (/) }'); c3b = w.s([c3], 'a1i', '( %s -> (/) e. { (/) } )' % A)
KT0 = 'dom %s' % Gt(T0); evk, kt = evaluate(w, A, KT0, {}, extra_rules=extra); assert kt == '{ (/) }'
k0 = w.s([c3b, evk], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, KT0))
WD0 = 'Word ( %s ` (/) )' % Gt(T0); evw, wd = evaluate(w, A, WD0, {}, extra_rules=extra); assert wd == 'Word A'
w0 = w.s([ww, evw], 'eleqtrrd', '( %s -> W e. %s )' % (A, WD0))
si = w.inst('tm2initstk'); s0 = w.s([tx2, k0, w0, si], 'syl3anc', '( %s -> ( j e. %s |-> if ( j = (/) , W , (/) ) ) e. ( TM2Stk ` %s ) )' % (A, KT0, T0))
mq = w.s([evk], 'mpteq1d', '( %s -> ( j e. %s |-> if ( j = (/) , W , (/) ) ) = %s )' % (A, KT0, D0J))
cb0 = w.s([], 'eqeq1', '( j = k -> ( j = (/) <-> k = (/) ) )'); cb1 = w.s([cb0], 'ifbid', '( j = k -> if ( j = (/) , W , (/) ) = if ( k = (/) , W , (/) ) )')
cb = w.s([cb1], 'cbvmptv', '%s = %s' % (D0J, D0)); mq2 = w.s([mq, cb], 'eqtrdi', '( %s -> ( j e. %s |-> if ( j = (/) , W , (/) ) ) = %s )' % (A, KT0, D0))
s1 = w.s([mq2, s0], 'eqeltrrd', '( %s -> %s e. ( TM2Stk ` %s ) )' % (A, D0, T0))
dli = w.inst('djulcl'); il = w.s([zl, dli], 'syl', '( %s -> ( inl ` (/) ) e. ( %s |_| 1o ) )' % (A, Lt0))
pi = w.inst('opelxpi'); pr = w.s([zs, s1, pi], 'syl2anc', '( %s -> <. (/) , %s >. e. ( %s X. ( TM2Stk ` %s ) ) )' % (A, D0, St0, T0))
pi2 = w.inst('opelxpi'); pr2 = w.s([il, pr, pi2], 'syl2anc', '( %s -> %s e. ( ( %s |_| 1o ) X. ( %s X. ( TM2Stk ` %s ) ) ) )' % (A, INITC, Lt0, St0, T0))
cvi = w.inst('tm2cfgval'); cv = w.s([tx2, cvi], 'syl', '( %s -> %s = ( ( %s |_| 1o ) X. ( %s X. ( TM2Stk ` %s ) ) ) )' % (A, CFG0, Lt0, St0, T0))
ic0 = w.s([pr2, cv], 'eleqtrrd', '( %s -> %s e. %s )' % (A, INITC, CFG0))
evi = w.inst('evalsttlem'); ev_ = w.s([c1, c2, ic0, evi], 'syl3anc', '( %s -> %s ( %s EvalsToInTime 1 ) ( ( %s ^r 1 ) ` ( inl ` %s ) ) )' % (A, INITC, STEP, OS, INITC))
# ( ( OS ^r 1 ) ` ( inl ` INITC ) ) = ( inl ` HALTC )
ofi = w.inst('optstepf'); of = w.s([cx2, sf, ofi], 'syl2anc', '( %s -> %s : %s --> %s )' % (A, OS, DJC, DJC))
dx = w.s([], 'fvex', '%s e. _V' % DJC); dx2 = w.s([dx], 'a1i', '( %s -> %s e. _V )' % (A, DJC))
w.lines.pop(); w.lines.pop()
dxi = w.inst('djuex'); ox = w.s([], '1oex', '1o e. _V'); ox2 = w.s([ox], 'a1i', '( %s -> 1o e. _V )' % A)
dx2 = w.s([cx2, ox2, dxi], 'syl2anc', '( %s -> %s e. _V )' % (A, DJC))
bo = w.s([dx2, of], 'jca', '( %s -> ( %s e. _V /\\ %s : %s --> %s ) )' % (A, DJC, OS, DJC, DJC))
n0b = w.s([], '0nn0', '0 e. NN0'); n0c = w.s([n0b], 'a1i', '( %s -> 0 e. NN0 )' % A)
xi = w.inst('djulcl'); xin = w.s([ic0, xi], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (A, INITC, DJC))
rsi = w.inst('relexpsucfv'); rs = w.s([bo, n0c, xin, rsi], 'syl3anc', '( %s -> ( ( %s ^r ( 0 + 1 ) ) ` ( inl ` %s ) ) = ( %s ` ( ( %s ^r 0 ) ` ( inl ` %s ) ) ) )' % (A, OS, INITC, OS, OS, INITC))
r0i = w.inst('relexp0fv'); r0 = w.s([dx2, of, xin, r0i], 'syl3anc', '( %s -> ( ( %s ^r 0 ) ` ( inl ` %s ) ) = ( inl ` %s ) )' % (A, OS, INITC, INITC))
r0b = w.s([r0], 'fveq2d', '( %s -> ( %s ` ( ( %s ^r 0 ) ` ( inl ` %s ) ) ) = ( %s ` ( inl ` %s ) ) )' % (A, OS, OS, INITC, OS, INITC))
p1 = w.s([], '0p1e1', '( 0 + 1 ) = 1'); p2 = w.s([p1], 'oveq2i', '( %s ^r ( 0 + 1 ) ) = ( %s ^r 1 )' % (OS, OS)); p3 = w.s([p2], 'fveq1i', '( ( %s ^r ( 0 + 1 ) ) ` ( inl ` %s ) ) = ( ( %s ^r 1 ) ` ( inl ` %s ) )' % (OS, INITC, OS, INITC))
sx = w.s([], 'ovex', '%s e. _V' % STEP); sx2 = w.s([sx], 'a1i', '( %s -> %s e. _V )' % (A, STEP))
fdi = w.inst('fdm'); fd = w.s([sf, fdi], 'syl', '( %s -> dom %s = %s )' % (A, STEP, CFG0))
ic1 = w.s([ic0, fd], 'eleqtrrd', '( %s -> %s e. dom %s )' % (A, INITC, STEP))
osi = w.inst('optstepsome'); os = w.s([sx2, ic1, osi], 'syl2anc', '( %s -> ( %s ` ( inl ` %s ) ) = ( %s ` %s ) )' % (A, OS, INITC, STEP, INITC))
sti = w.inst('tm2idstep'); stp = w.s([a, ww, sti], 'syl2anc', '( %s -> ( %s ` %s ) = ( inl ` %s ) )' % (A, STEP, INITC, HALTC))
ch1 = w.s([rs, r0b], 'eqtrd', '( %s -> ( ( %s ^r ( 0 + 1 ) ) ` ( inl ` %s ) ) = ( %s ` ( inl ` %s ) ) )' % (A, OS, INITC, OS, INITC))
ch2 = w.s([ch1, os], 'eqtrd', '( %s -> ( ( %s ^r ( 0 + 1 ) ) ` ( inl ` %s ) ) = ( %s ` %s ) )' % (A, OS, INITC, STEP, INITC))
ch3 = w.s([ch2, stp], 'eqtrd', '( %s -> ( ( %s ^r ( 0 + 1 ) ) ` ( inl ` %s ) ) = ( inl ` %s ) )' % (A, OS, INITC, HALTC))
ch4 = w.s([p3, ch3], 'eqtr3id', '( %s -> ( ( %s ^r 1 ) ` ( inl ` %s ) ) = ( inl ` %s ) )' % (A, OS, INITC, HALTC))
fin = w.s([ev_, ch4], 'breqtrd', '( %s -> %s )' % (A, REL2))
w.qed([fin, b2], 'mpbird', '( %s -> W ( %s TM2OutputsInTime 1 ) ( inl ` W ) )' % (A, IDM))
run(w)
