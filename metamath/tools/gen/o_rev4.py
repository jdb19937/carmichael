import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
NONE = '( inr ` (/) )'; TWO = '{ (/) , 1o }'
G1 = '{ <. (/) , A >. , <. 1o , A >. }'; S1 = '( A |_| 1o )'; T1 = '<. <. %s , 1o >. , %s >.' % (G1, S1)
FPOP = '( 2nd |` ( %s X. %s ) )' % (S1, S1)
FBR = '( v e. %s |-> if ( v = %s , (/) , 1o ) )' % (S1, NONE)
FPUSH = '( v e. %s |-> if ( v = %s , Z , ( 2nd ` v ) ) )' % (S1, NONE)
FGOTO = '( %s X. { (/) } )' % S1; FLOAD = '( %s X. { %s } )' % (S1, NONE)
Q4 = '<. 5 , %s >.' % FGOTO; Q2 = '<. 0 , <. 1o , <. %s , %s >. >. >.' % (FPUSH, Q4)
Q3 = '<. 3 , <. %s , <. 6 , (/) >. >. >.' % FLOAD; Q1 = '<. 4 , <. %s , <. %s , %s >. >. >.' % (FBR, Q2, Q3)
STM = '<. 2 , <. (/) , <. %s , %s >. >. >.' % (FPOP, Q1)
M1 = '{ <. (/) , %s >. }' % STM
ST1 = '( TM2Stmt ` %s )' % T1; STK1 = '( TM2Stk ` %s )' % T1; SA1 = '( TM2sa ` %s )' % T1; STEP1 = '( %s TM2step %s )' % (T1, M1)
CFG1 = '( TM2Cfg ` %s )' % T1; DJC = '( %s |_| 1o )' % CFG1; OS = '( OptStep ` %s )' % STEP1
PP = lambda u, v: '{ <. (/) , %s >. , <. 1o , %s >. }' % (u, v)
Cf = lambda q, u, v: '<. ( inl ` (/) ) , <. %s , %s >. >.' % (q, PP(u, v))
HALTC = lambda v: '<. %s , <. %s , %s >. >.' % (NONE, NONE, PP('(/)', v))
Lt = '( 2nd ` ( 1st ` %s ) )' % T1; St = '( 2nd ` %s )' % T1; Gt = '( 1st ` ( 1st ` %s ) )' % T1; KT = 'dom %s' % Gt
AZ = '( A e. V /\\ Z e. A )'
def ne01(w):
    a = w.s([], '1n0', '1o =/= (/)'); return w.s([a], 'necomi', '(/) =/= 1o')
def g1rules(w, A, ax):
    z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
    o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
    n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A)
    f0 = w.s([z2, ax, n2, w.inst('fvpr1g')], 'syl3anc', '( %s -> ( %s ` (/) ) = A )' % (A, G1))
    f1 = w.s([o2, ax, n2, w.inst('fvpr2g')], 'syl3anc', '( %s -> ( %s ` 1o ) = A )' % (A, G1))
    d = w.s([ax, ax, w.inst('dmpropg')], 'syl2anc', '( %s -> dom %s = %s )' % (A, G1, TWO))
    def extra(n):
        if n.text() == '( %s ` (/) )' % G1: return ('A', f0)
        if n.text() == '( %s ` 1o )' % G1: return ('A', f1)
        if n.text() == 'dom %s' % G1: return (TWO, d)
        return None
    return extra

# ---- relexpsucfv2
w = W('relexpsucfv2', 'The ( N + 1 )-th iterate of a function is the N-th iterate of the function applied once (Lean\'s Function.iterate_succ_apply).')
A = '( ( B e. V /\\ G : B --> B ) /\\ N e. NN0 /\\ X e. B )'
g = w.s([], 'simp1r', '( %s -> G : B --> B )' % A); n = w.s([], 'simp2', '( %s -> N e. NN0 )' % A); x = w.s([], 'simp3', '( %s -> X e. B )' % A)
r = w.s([g, w.inst('frel')], 'syl', '( %s -> Rel G )' % A)
e = w.s([r, n], 'relexpsucrd', '( %s -> ( G ^r ( N + 1 ) ) = ( ( G ^r N ) o. G ) )' % A)
e2 = w.s([e], 'fveq1d', '( %s -> ( ( G ^r ( N + 1 ) ) ` X ) = ( ( ( G ^r N ) o. G ) ` X ) )' % A)
c = w.s([g, x, w.inst('fvco3')], 'syl2anc', '( %s -> ( ( ( G ^r N ) o. G ) ` X ) = ( ( G ^r N ) ` ( G ` X ) ) )' % A)
w.qed([e2, c], 'eqtrd', '( %s -> ( ( G ^r ( N + 1 ) ) ` X ) = ( ( G ^r N ) ` ( G ` X ) ) )' % A)
run(w)

# ---- revstepf
w = W('revstepf', 'The step function of the reverse machine maps configurations to optional configurations.')
A = AZ
a = w.s([], 'simpl', '( %s -> A e. V )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
tx = w.s([], 'opex', '%s e. _V' % T1); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T1))
extra = g1rules(w, A, ax); SM = {'A': ax}
evL, lt = evaluate(w, A, Lt, SM, extra_rules=extra); assert lt == '1o'
sx = w.s([], 'opex', '%s e. _V' % STM)
f1 = w.s([], 'f1osn', '%s : { (/) } -1-1-onto-> { %s }' % (M1, STM)); f2 = w.s([f1, w.inst('f1of')], 'ax-mp', '%s : { (/) } --> { %s }' % (M1, STM))
d1 = w.s([], 'df1o2', '1o = { (/) }'); d2 = w.s([d1], 'feq2i', '( %s : 1o --> { %s } <-> %s : { (/) } --> { %s } )' % (M1, STM, M1, STM))
f3 = w.s([f2, d2], 'mpbir', '%s : 1o --> { %s }' % (M1, STM)); f3b = w.s([f3], 'a1i', '( %s -> %s : 1o --> { %s } )' % (A, M1, STM))
st = w.s([], 'revstm', '( %s -> %s e. %s )' % (A, STM, ST1)); st2 = w.s([st], 'snssd', '( %s -> { %s } C_ %s )' % (A, STM, ST1))
f4 = w.s([f3b, st2, w.inst('fss')], 'syl2anc', '( %s -> %s : 1o --> %s )' % (A, M1, ST1))
evLr = w.s([evL], 'eqcomd', '( %s -> 1o = %s )' % (A, Lt))
f5 = w.s([evLr], 'feq2d', '( %s -> ( %s : 1o --> %s <-> %s : %s --> %s ) )' % (A, M1, ST1, M1, Lt, ST1)); f6 = w.s([f4, f5], 'mpbid', '( %s -> %s : %s --> %s )' % (A, M1, Lt, ST1))
w.qed([tx2, f6, w.inst('tm2stepf')], 'syl2anc', '( %s -> %s : %s --> %s )' % (A, STEP1, CFG1, DJC))
run(w)

# ---- revcfg
B0 = '( %s /\\ ( U e. Word A /\\ W e. Word A /\\ Q e. %s ) )' % (AZ, S1)
C0 = Cf('Q', 'U', 'W')
w = W('revcfg', 'The running configurations of the reverse machine are configurations.')
A = B0
az = w.s([], 'simpl', '( %s -> %s )' % (A, AZ)); a = w.s([az], 'simpld', '( %s -> A e. V )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
h = w.s([], 'simpr', '( %s -> ( U e. Word A /\\ W e. Word A /\\ Q e. %s ) )' % (A, S1)); u = w.s([h], 'simp1d', '( %s -> U e. Word A )' % A); ww = w.s([h], 'simp2d', '( %s -> W e. Word A )' % A); q = w.s([h], 'simp3d', '( %s -> Q e. %s )' % (A, S1))
tx = w.s([], 'opex', '%s e. _V' % T1); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T1))
extra = g1rules(w, A, ax); SM = {'A': ax}
evL, lt = evaluate(w, A, Lt, SM, extra_rules=extra); evS, st_ = evaluate(w, A, St, SM, extra_rules=extra)
z = w.s([], '0lt1o', '(/) e. 1o'); z2 = w.s([z], 'a1i', '( %s -> (/) e. 1o )' % A); zl = w.s([z2, evL], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, Lt))
il = w.s([zl, w.inst('djulcl')], 'syl', '( %s -> ( inl ` (/) ) e. ( %s |_| 1o ) )' % (A, Lt))
qs = w.s([q, evS], 'eleqtrrd', '( %s -> Q e. %s )' % (A, St))
uw = w.s([u, ww], 'jca', '( %s -> ( U e. Word A /\\ W e. Word A ) )' % A); pk = w.s([a, uw, w.inst('ppstk')], 'syl2anc', '( %s -> %s e. %s )' % (A, PP('U', 'W'), STK1))
pr = w.s([qs, pk, w.inst('opelxpi')], 'syl2anc', '( %s -> <. Q , %s >. e. ( %s X. %s ) )' % (A, PP('U', 'W'), St, STK1))
pr2 = w.s([il, pr, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( ( %s |_| 1o ) X. ( %s X. %s ) ) )' % (A, C0, Lt, St, STK1))
cv = w.s([tx2, w.inst('tm2cfgval')], 'syl', '( %s -> %s = ( ( %s |_| 1o ) X. ( %s X. %s ) ) )' % (A, CFG1, Lt, St, STK1))
w.qed([pr2, cv], 'eleqtrrd', '( %s -> %s e. %s )' % (A, C0, CFG1))
run(w)

# ---- revos
w = W('revos', 'The option-lifted step function of the reverse machine on a running configuration.')
A = B0
az = w.s([], 'simpl', '( %s -> %s )' % (A, AZ))
sf = w.s([az, w.inst('revstepf')], 'syl', '( %s -> %s : %s --> %s )' % (A, STEP1, CFG1, DJC))
c = w.s([], 'revcfg', '( %s -> %s e. %s )' % (A, C0, CFG1))
sx = w.s([], 'ovex', '%s e. _V' % STEP1); sx2 = w.s([sx], 'a1i', '( %s -> %s e. _V )' % (A, STEP1))
fd = w.s([sf, w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (A, STEP1, CFG1)); c2 = w.s([c, fd], 'eleqtrrd', '( %s -> %s e. dom %s )' % (A, C0, STEP1))
w.qed([sx2, c2, w.inst('optstepsome')], 'syl2anc', '( %s -> ( %s ` ( inl ` %s ) ) = ( %s ` %s ) )' % (A, OS, C0, STEP1, C0))
run(w)

# ---- revit
w = W('revit', 'Peeling one step off the iterated option-lifted step function of the reverse machine.')
A = '( %s /\\ N e. NN0 )' % B0
b0 = w.s([], 'simpl', '( %s -> %s )' % (A, B0)); n = w.s([], 'simpr', '( %s -> N e. NN0 )' % A)
az = w.s([b0], 'simpld', '( %s -> %s )' % (A, AZ))
sf = w.s([az, w.inst('revstepf')], 'syl', '( %s -> %s : %s --> %s )' % (A, STEP1, CFG1, DJC))
cx = w.s([], 'fvex', '%s e. _V' % CFG1); cx2 = w.s([cx], 'a1i', '( %s -> %s e. _V )' % (A, CFG1))
of = w.s([cx2, sf, w.inst('optstepf')], 'syl2anc', '( %s -> %s : %s --> %s )' % (A, OS, DJC, DJC))
o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A); dx = w.s([cx2, o2, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (A, DJC))
bo = w.s([dx, of], 'jca', '( %s -> ( %s e. _V /\\ %s : %s --> %s ) )' % (A, DJC, OS, DJC, DJC))
c = w.s([b0, w.inst('revcfg')], 'syl', '( %s -> %s e. %s )' % (A, C0, CFG1)); xi = w.s([c, w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (A, C0, DJC))
r = w.s([bo, n, xi, w.inst('relexpsucfv2')], 'syl3anc', '( %s -> ( ( %s ^r ( N + 1 ) ) ` ( inl ` %s ) ) = ( ( %s ^r N ) ` ( %s ` ( inl ` %s ) ) ) )' % (A, OS, C0, OS, OS, C0))
os_ = w.s([b0, w.inst('revos')], 'syl', '( %s -> ( %s ` ( inl ` %s ) ) = ( %s ` %s ) )' % (A, OS, C0, STEP1, C0))
os2 = w.s([os_], 'fveq2d', '( %s -> ( ( %s ^r N ) ` ( %s ` ( inl ` %s ) ) ) = ( ( %s ^r N ) ` ( %s ` %s ) ) )' % (A, OS, OS, C0, OS, STEP1, C0))
w.qed([r, os2], 'eqtrd', '( %s -> ( ( %s ^r ( N + 1 ) ) ` ( inl ` %s ) ) = ( ( %s ^r N ) ` ( %s ` %s ) ) )' % (A, OS, C0, OS, STEP1, C0))
run(w)

# ---- wrdhdtl, wrdtllen, revtail
TAIL = '( U substr <. 1 , ( # ` U ) >. )'
w = W('wrdhdtl', 'A nonempty word is its first letter followed by its tail.')
A = '( U e. Word A /\\ U =/= (/) )'
u = w.s([], 'simpl', '( %s -> U e. Word A )' % A)
n = w.s([], 'lennncl', '( %s -> ( # ` U ) e. NN )' % A); n0 = w.s([n, w.inst('nnnn0')], 'syl', '( %s -> ( # ` U ) e. NN0 )' % A)
g = w.s([n, w.inst('nnge1')], 'syl', '( %s -> 1 <_ ( # ` U ) )' % A); one = w.s([], '1nn0', '1 e. NN0'); one2 = w.s([one], 'a1i', '( %s -> 1 e. NN0 )' % A)
e1 = w.s([], 'elfz2nn0', '( 1 e. ( 0 ... ( # ` U ) ) <-> ( 1 e. NN0 /\\ ( # ` U ) e. NN0 /\\ 1 <_ ( # ` U ) ) )')
f1 = w.s([one2, n0, g, e1], 'syl3anbrc', '( %s -> 1 e. ( 0 ... ( # ` U ) ) )' % A)
e2 = w.s([], 'nn0fz0', '( ( # ` U ) e. NN0 <-> ( # ` U ) e. ( 0 ... ( # ` U ) ) )'); f2 = w.s([n0, e2], 'sylib', '( %s -> ( # ` U ) e. ( 0 ... ( # ` U ) ) )' % A)
c = w.s([u, f1, f2, w.inst('ccatpfx')], 'syl3anc', '( %s -> ( ( U prefix 1 ) ++ %s ) = ( U prefix ( # ` U ) ) )' % (A, TAIL))
p1 = w.s([], 'pfx1', '( %s -> ( U prefix 1 ) = <" ( U ` 0 ) "> )' % A); p1b = w.s([p1], 'oveq1d', '( %s -> ( ( U prefix 1 ) ++ %s ) = ( <" ( U ` 0 ) "> ++ %s ) )' % (A, TAIL, TAIL))
pid = w.s([u, w.inst('pfxid')], 'syl', '( %s -> ( U prefix ( # ` U ) ) = U )' % A)
c2 = w.s([p1b, c], 'eqtr3d', '( %s -> ( <" ( U ` 0 ) "> ++ %s ) = ( U prefix ( # ` U ) ) )' % (A, TAIL))
c3 = w.s([c2, pid], 'eqtrd', '( %s -> ( <" ( U ` 0 ) "> ++ %s ) = U )' % (A, TAIL))
w.qed([c3], 'eqcomd', '( %s -> U = ( <" ( U ` 0 ) "> ++ %s ) )' % (A, TAIL))
run(w)

w = W('wrdtllen', 'The length of the tail of a nonempty word.')
A = '( U e. Word A /\\ U =/= (/) )'
u = w.s([], 'simpl', '( %s -> U e. Word A )' % A)
n = w.s([], 'lennncl', '( %s -> ( # ` U ) e. NN )' % A); n0 = w.s([n, w.inst('nnnn0')], 'syl', '( %s -> ( # ` U ) e. NN0 )' % A)
g = w.s([n, w.inst('nnge1')], 'syl', '( %s -> 1 <_ ( # ` U ) )' % A); one = w.s([], '1nn0', '1 e. NN0'); one2 = w.s([one], 'a1i', '( %s -> 1 e. NN0 )' % A)
e1 = w.s([], 'elfz2nn0', '( 1 e. ( 0 ... ( # ` U ) ) <-> ( 1 e. NN0 /\\ ( # ` U ) e. NN0 /\\ 1 <_ ( # ` U ) ) )')
f1 = w.s([one2, n0, g, e1], 'syl3anbrc', '( %s -> 1 e. ( 0 ... ( # ` U ) ) )' % A)
e2 = w.s([], 'nn0fz0', '( ( # ` U ) e. NN0 <-> ( # ` U ) e. ( 0 ... ( # ` U ) ) )'); f2 = w.s([n0, e2], 'sylib', '( %s -> ( # ` U ) e. ( 0 ... ( # ` U ) ) )' % A)
w.qed([u, f1, f2, w.inst('swrdlen')], 'syl3anc', '( %s -> ( # ` %s ) = ( ( # ` U ) - 1 ) )' % (A, TAIL))
run(w)

w = W('revtail', 'Reversing a nonempty word: the reverse of the tail followed by the first letter.')
A = '( U e. Word A /\\ U =/= (/) /\\ W e. Word A )'
u = w.s([], 'simp1', '( %s -> U e. Word A )' % A); un = w.s([], 'simp2', '( %s -> U =/= (/) )' % A); ww = w.s([], 'simp3', '( %s -> W e. Word A )' % A)
u0 = w.s([u, un, w.inst('wrdfv0')], 'syl2anc', '( %s -> ( U ` 0 ) e. A )' % A); s1 = w.s([u0, w.inst('s1cl')], 'syl', '( %s -> <" ( U ` 0 ) "> e. Word A )' % A)
t = w.s([u, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word A )' % (A, TAIL))
hd = w.s([u, un, w.inst('wrdhdtl')], 'syl2anc', '( %s -> U = ( <" ( U ` 0 ) "> ++ %s ) )' % (A, TAIL))
r1 = w.s([hd], 'fveq2d', '( %s -> ( reverse ` U ) = ( reverse ` ( <" ( U ` 0 ) "> ++ %s ) ) )' % (A, TAIL))
r2 = w.s([s1, t, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( <" ( U ` 0 ) "> ++ %s ) ) = ( ( reverse ` %s ) ++ ( reverse ` <" ( U ` 0 ) "> ) ) )' % (A, TAIL, TAIL))
r3 = w.s([], 'revs1', '( reverse ` <" ( U ` 0 ) "> ) = <" ( U ` 0 ) ">'); r3b = w.s([r3], 'oveq2i', '( ( reverse ` %s ) ++ ( reverse ` <" ( U ` 0 ) "> ) ) = ( ( reverse ` %s ) ++ <" ( U ` 0 ) "> )' % (TAIL, TAIL))
r4 = w.s([r1, r2], 'eqtrd', '( %s -> ( reverse ` U ) = ( ( reverse ` %s ) ++ ( reverse ` <" ( U ` 0 ) "> ) ) )' % (A, TAIL))
r5 = w.s([r4, r3b], 'eqtrdi', '( %s -> ( reverse ` U ) = ( ( reverse ` %s ) ++ <" ( U ` 0 ) "> ) )' % (A, TAIL))
r6 = w.s([r5], 'oveq1d', '( %s -> ( ( reverse ` U ) ++ W ) = ( ( ( reverse ` %s ) ++ <" ( U ` 0 ) "> ) ++ W ) )' % (A, TAIL))
rt = w.s([t, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word A )' % (A, TAIL))
as_ = w.s([rt, s1, ww, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( ( reverse ` %s ) ++ <" ( U ` 0 ) "> ) ++ W ) = ( ( reverse ` %s ) ++ ( <" ( U ` 0 ) "> ++ W ) ) )' % (A, TAIL, TAIL))
w.qed([r6, as_], 'eqtrd', '( %s -> ( ( reverse ` U ) ++ W ) = ( ( reverse ` %s ) ++ ( <" ( U ` 0 ) "> ++ W ) ) )' % (A, TAIL))
run(w)
