import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
NONE = '( inr ` (/) )'
TWO = '{ (/) , 1o }'
G1 = '{ <. (/) , A >. , <. 1o , A >. }'; S1 = '( A |_| 1o )'; T1 = '<. <. %s , 1o >. , %s >.' % (G1, S1)
FPOP = '( 2nd |` ( %s X. %s ) )' % (S1, S1)
FBR = '( v e. %s |-> if ( v = %s , (/) , 1o ) )' % (S1, NONE)
FPUSH = '( v e. %s |-> if ( v = %s , Z , ( 2nd ` v ) ) )' % (S1, NONE)
FGOTO = '( %s X. { (/) } )' % S1; FLOAD = '( %s X. { %s } )' % (S1, NONE)
Q4 = '<. 5 , %s >.' % FGOTO; Q2 = '<. 0 , <. 1o , <. %s , %s >. >. >.' % (FPUSH, Q4)
Q3 = '<. 3 , <. %s , <. 6 , (/) >. >. >.' % FLOAD; Q1 = '<. 4 , <. %s , <. %s , %s >. >. >.' % (FBR, Q2, Q3)
STM = '<. 2 , <. (/) , <. %s , %s >. >. >.' % (FPOP, Q1)
M1 = '{ <. (/) , %s >. }' % STM
REVM = '<. <. %s , <. (/) , 1o >. >. , <. <. (/) , %s >. , %s >. >.' % (T1, NONE, M1)
ST1 = '( TM2Stmt ` %s )' % T1

def ne01(w):
    a = w.s([], '1n0', '1o =/= (/)'); return w.s([a], 'necomi', '(/) =/= 1o')
def g1rules(w, A, ax):
    """rules: ( G1 ` (/) ) -> A, ( G1 ` 1o ) -> A, dom G1 -> { (/) , 1o }"""
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

# ---- revfpop
w = W('revfpop', 'The pop function of the reverse machine returns the popped optional letter.')
A = '( Q e. %s /\\ X e. %s )' % (S1, S1)
p = w.s([], 'opelxpi', '( %s -> <. Q , X >. e. ( %s X. %s ) )' % (A, S1, S1))
f = w.s([p, w.inst('fvres')], 'syl', '( %s -> ( %s ` <. Q , X >. ) = ( 2nd ` <. Q , X >. ) )' % (A, FPOP))
qx = w.s([w.s([], 'simpl', '( %s -> Q e. %s )' % (A, S1))], 'elexd', '( %s -> Q e. _V )' % A); xx = w.s([w.s([], 'simpr', '( %s -> X e. %s )' % (A, S1))], 'elexd', '( %s -> X e. _V )' % A)
o = w.s([qx, xx, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. Q , X >. ) = X )' % A)
w.qed([f, o], 'eqtrd', '( %s -> ( %s ` <. Q , X >. ) = X )' % (A, FPOP))
run(w)

# ---- revfbr / revfpush
for label, F, body, desc, hyp in (('revfbr', FBR, 'if ( v = %s , (/) , 1o )' % NONE, 'The branch function of the reverse machine: false on none, true on a letter.', None),
                                  ('revfpush', FPUSH, 'if ( v = %s , Z , ( 2nd ` v ) )' % NONE, 'The push function of the reverse machine: the letter held in the state.', 'Z e. A')):
    w = W(label, desc)
    A = 'Q e. %s' % S1 if hyp is None else '( Q e. %s /\\ %s )' % (S1, hyp)
    q = w.s([], 'id', '( Q e. %s -> Q e. %s )' % (S1, S1)) if hyp is None else w.s([], 'simpl', '( %s -> Q e. %s )' % (A, S1))
    l = w.s([], 'id', '( v = Q -> v = Q )'); c, bQ = w.congr(body, {'v': 'Q'}, 'v = Q', {'v': l})
    e = w.s([], 'eqid', '%s = %s' % (F, F))
    fv = w.s([c, e], 'fvmptg', '( ( Q e. %s /\\ %s e. _V ) -> ( %s ` Q ) = %s )' % (S1, bQ, F, bQ))
    if hyp is None:
        z = w.s([], '0ex', '(/) e. _V'); o = w.s([], '1oex', '1o e. _V'); bx = w.s([z, o], 'ifex', '%s e. _V' % bQ); bx2 = w.s([bx], 'a1i', '( %s -> %s e. _V )' % (A, bQ))
    else:
        zz = w.s([w.s([], 'simpr', '( %s -> Z e. A )' % A)], 'elexd', '( %s -> Z e. _V )' % A); fx = w.s([], 'fvex', '( 2nd ` Q ) e. _V'); fx2 = w.s([fx], 'a1i', '( %s -> ( 2nd ` Q ) e. _V )' % A)
        bx2 = w.s([zz, fx2, w.inst('ifexg')], 'syl2anc', '( %s -> %s e. _V )' % (A, bQ))
    w.qed([q, bx2, fv], 'syl2anc', '( %s -> ( %s ` Q ) = %s )' % (A, F, bQ))
    run(w)

# ---- revfgoto / revfload
for label, F, val, desc in (('revfgoto', FGOTO, '(/)', 'The goto function of the reverse machine: always the label main.'),
                            ('revfload', FLOAD, NONE, 'The load function of the reverse machine: reset the state to none.')):
    w = W(label, desc)
    A = 'Q e. %s' % S1
    w.qed([], 'fvconst2', '( %s -> ( %s ` Q ) = %s )' % (A, F, val))
    run(w)

# ---- memberships of the functions
w = W('revfpopel', 'The pop function of the reverse machine has the type required by pop.')
A = 'A e. V'
ax = w.s([], 'elex', '( A e. V -> A e. _V )'); o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
sx = w.s([ax, o2, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (A, S1))
xx = w.s([sx, sx, w.inst('xpexg')], 'syl2anc', '( %s -> ( %s X. %s ) e. _V )' % (A, S1, S1))
f = w.s([], 'f2ndres', '%s : ( %s X. %s ) --> %s' % (FPOP, S1, S1, S1)); f2 = w.s([f], 'a1i', '( %s -> %s : ( %s X. %s ) --> %s )' % (A, FPOP, S1, S1, S1))
e = w.s([sx, xx, w.inst('elmapd')], 'syl2anc', '( %s -> ( %s e. ( %s ^m ( %s X. %s ) ) <-> %s : ( %s X. %s ) --> %s ) )' % (A, FPOP, S1, S1, S1, FPOP, S1, S1, S1))
w.lines[-1] = w.lines[-1].replace(':syl2anc', ':elmapd').replace('%s,%s,i' % (sx, xx), '%s,%s' % (sx, xx))
# simpler: use elmapg closed
w.lines.pop()
eg = w.s([sx, xx, w.inst('elmapg')], 'syl2anc', '( %s -> ( %s e. ( %s ^m ( %s X. %s ) ) <-> %s : ( %s X. %s ) --> %s ) )' % (A, FPOP, S1, S1, S1, FPOP, S1, S1, S1))
w.qed([f2, eg], 'mpbird', '( %s -> %s e. ( %s ^m ( %s X. %s ) ) )' % (A, FPOP, S1, S1, S1))
run(w)

w = W('revfbrel', 'The branch function of the reverse machine has the type required by branch.')
A = 'A e. V'
ax = w.s([], 'elex', '( A e. V -> A e. _V )'); o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
sx = w.s([ax, o2, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (A, S1)); tx = w.s([], '2oex', '2o e. _V'); tx2 = w.s([tx], 'a1i', '( %s -> 2o e. _V )' % A)
z = w.s([], '0ex', '(/) e. _V'); d = w.s([], 'df2o3', '2o = %s' % TWO)
z1 = w.s([z, w.inst('prid1g')], 'ax-mp', '(/) e. %s' % TWO); z2 = w.s([d], 'eleq2i', '( (/) e. 2o <-> (/) e. %s )' % TWO); z3 = w.s([z1, z2], 'mpbir', '(/) e. 2o')
o1 = w.s([o, w.inst('prid2g')], 'ax-mp', '1o e. %s' % TWO); o3 = w.s([d], 'eleq2i', '( 1o e. 2o <-> 1o e. %s )' % TWO); o4 = w.s([o1, o3], 'mpbir', '1o e. 2o')
A2 = '( %s /\\ v e. %s )' % (A, S1)
z4 = w.s([z3], 'a1i', '( %s -> (/) e. 2o )' % A2); o5 = w.s([o4], 'a1i', '( %s -> 1o e. 2o )' % A2)
ic = w.s([z4, o5], 'ifcld', '( %s -> if ( v = %s , (/) , 1o ) e. 2o )' % (A2, NONE))
fm = w.s([ic], 'fmptd', '( %s -> %s : %s --> 2o )' % (A, FBR, S1))
eg = w.s([tx2, sx, w.inst('elmapg')], 'syl2anc', '( %s -> ( %s e. ( 2o ^m %s ) <-> %s : %s --> 2o ) )' % (A, FBR, S1, FBR, S1))
w.qed([fm, eg], 'mpbird', '( %s -> %s e. ( 2o ^m %s ) )' % (A, FBR, S1))
run(w)

w = W('revfpushel', 'The push function of the reverse machine has the type required by push.')
A = '( A e. V /\\ Z e. A )'
a = w.s([], 'simpl', '( %s -> A e. V )' % A); zz = w.s([], 'simpr', '( %s -> Z e. A )' % A)
ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A); o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
sx = w.s([ax, o2, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (A, S1))
A2 = '( %s /\\ v e. %s )' % (A, S1)
COND = 'v = %s' % NONE; A3 = '( %s /\\ %s )' % (A2, COND); A4 = '( %s /\\ -. %s )' % (A2, COND)
t = w.s([zz], 'ad2antrr', '( %s -> Z e. A )' % A3)
v4 = w.s([], 'simplr', '( %s -> v e. %s )' % (A4, S1)); nc = w.s([], 'simpr', '( %s -> -. %s )' % (A4, COND))
dj = w.s([v4, w.inst('djur')], 'syl', '( %s -> ( E. l e. A v = ( inl ` l ) \\/ E. l e. 1o v = ( inr ` l ) ) )' % A4)
GOAL = '( 2nd ` v ) e. A'
A5 = '( %s /\\ ( l e. A /\\ v = ( inl ` l ) ) )' % A4
l5 = w.s([], 'simprl', '( %s -> l e. A )' % A5); e5 = w.s([], 'simprr', '( %s -> v = ( inl ` l ) )' % A5); lx = w.s([l5], 'elexd', '( %s -> l e. _V )' % A5)
i1 = w.s([lx, w.inst('inlval')], 'syl', '( %s -> ( inl ` l ) = <. (/) , l >. )' % A5); i0 = w.s([e5, i1], 'eqtrd', '( %s -> v = <. (/) , l >. )' % A5)
i2 = w.s([i0], 'fveq2d', '( %s -> ( 2nd ` v ) = ( 2nd ` <. (/) , l >. ) )' % A5)
z = w.s([], '0ex', '(/) e. _V'); z5 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A5)
i3 = w.s([z5, lx, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. (/) , l >. ) = l )' % A5); i4 = w.s([i2, i3], 'eqtrd', '( %s -> ( 2nd ` v ) = l )' % A5)
g5 = w.s([i4, l5], 'eqeltrd', '( %s -> %s )' % (A5, GOAL)); g5b = w.s([g5], 'rexlimdvaa', '( %s -> ( E. l e. A v = ( inl ` l ) -> %s ) )' % (A4, GOAL))
A6 = '( %s /\\ ( l e. 1o /\\ v = ( inr ` l ) ) )' % A4
l6 = w.s([], 'simprl', '( %s -> l e. 1o )' % A6); e6 = w.s([], 'simprr', '( %s -> v = ( inr ` l ) )' % A6)
e1o = w.s([], 'el1o', '( l e. 1o <-> l = (/) )'); l6b = w.s([l6, e1o], 'sylib', '( %s -> l = (/) )' % A6); l6c = w.s([l6b], 'fveq2d', '( %s -> ( inr ` l ) = %s )' % (A6, NONE))
e6b = w.s([e6, l6c], 'eqtrd', '( %s -> %s )' % (A6, COND)); nc6 = w.s([nc], 'adantr', '( %s -> -. %s )' % (A6, COND))
g6 = w.s([e6b, nc6], 'pm2.21dd', '( %s -> %s )' % (A6, GOAL)); g6b = w.s([g6], 'rexlimdvaa', '( %s -> ( E. l e. 1o v = ( inr ` l ) -> %s ) )' % (A4, GOAL))
jd = w.s([g5b, g6b], 'jaod', '( %s -> ( ( E. l e. A v = ( inl ` l ) \\/ E. l e. 1o v = ( inr ` l ) ) -> %s ) )' % (A4, GOAL))
f4 = w.s([dj, jd], 'mpd', '( %s -> %s )' % (A4, GOAL))
ic = w.s([t, f4], 'ifclda', '( %s -> if ( v = %s , Z , ( 2nd ` v ) ) e. A )' % (A2, NONE))
fm = w.s([ic], 'fmptd', '( %s -> %s : %s --> A )' % (A, FPUSH, S1))
eg = w.s([ax, sx, w.inst('elmapg')], 'syl2anc', '( %s -> ( %s e. ( A ^m %s ) <-> %s : %s --> A ) )' % (A, FPUSH, S1, FPUSH, S1))
w.qed([fm, eg], 'mpbird', '( %s -> %s e. ( A ^m %s ) )' % (A, FPUSH, S1))
run(w)

for label, F, val, cod, desc in (('revfgotoel', FGOTO, '(/)', '1o', 'The goto function of the reverse machine has the type required by goto.'),
                                 ('revfloadel', FLOAD, NONE, S1, 'The load function of the reverse machine has the type required by load.')):
    w = W(label, desc)
    A = 'A e. V'
    ax = w.s([], 'elex', '( A e. V -> A e. _V )'); o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
    sx = w.s([ax, o2, w.inst('djuex')], 'syl2anc', '( %s -> %s e. _V )' % (A, S1))
    if val == '(/)':
        m = w.s([], '0lt1o', '(/) e. 1o'); cx = o2
    else:
        m0 = w.s([], '0lt1o', '(/) e. 1o'); m = w.s([m0, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, S1)); cx = sx
    f = w.s([m, w.inst('fconst6g')], 'ax-mp', '%s : %s --> %s' % (F, S1, cod)); f2 = w.s([f], 'a1i', '( %s -> %s : %s --> %s )' % (A, F, S1, cod))
    eg = w.s([cx, sx, w.inst('elmapg')], 'syl2anc', '( %s -> ( %s e. ( %s ^m %s ) <-> %s : %s --> %s ) )' % (A, F, cod, S1, F, S1, cod))
    w.qed([f2, eg], 'mpbird', '( %s -> %s e. ( %s ^m %s ) )' % (A, F, cod, S1))
    run(w)

# ---- revstm: STM e. ( TM2Stmt ` T1 ) (and sub-statements)
w = W('revstm', 'The program of the reverse machine is a statement: pop k0, then branch on the popped letter to push k1 and loop, or to reset and halt.')
A = '( A e. V /\\ Z e. A )'
a = w.s([], 'simpl', '( %s -> A e. V )' % A); zz = w.s([], 'simpr', '( %s -> Z e. A )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
tx = w.s([], 'opex', '%s e. _V' % T1); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T1))
extra = g1rules(w, A, ax)
SM = {'A': ax}
Lt = '( 2nd ` ( 1st ` %s ) )' % T1; St = '( 2nd ` %s )' % T1; Gt = '( 1st ` ( 1st ` %s ) )' % T1
evL, lt = evaluate(w, A, Lt, SM, extra_rules=extra); assert lt == '1o'
evS, st_ = evaluate(w, A, St, SM, extra_rules=extra); assert st_ == S1
def conv(step, expr_from_proj, expr_evald, memtext):
    """given ( A -> X e. EVALD ) and ( A -> PROJ = EVALD ) produce ( A -> X e. PROJ )"""
    pass
# halt
h = w.s([tx2, w.inst('tm2halt')], 'syl', '( %s -> <. 6 , (/) >. e. %s )' % (A, ST1))
# load FLOAD halt: FLOAD e. ( S ^m S ) with S = ( 2nd ` T1 )
fl = w.s([a, w.inst('revfloadel')], 'syl', '( %s -> %s e. ( %s ^m %s ) )' % (A, FLOAD, S1, S1))
MS = '( %s ^m %s )' % (St, St); evMS, ms = evaluate(w, A, MS, SM, extra_rules=extra); assert ms == '( %s ^m %s )' % (S1, S1)
fl2 = w.s([fl, evMS], 'eleqtrrd', '( %s -> %s e. %s )' % (A, FLOAD, MS))
q3 = w.s([tx2, fl2, h, w.inst('tm2load')], 'syl3anc', '( %s -> %s e. %s )' % (A, Q3, ST1))
# goto FGOTO: FGOTO e. ( L ^m S )
fg = w.s([a, w.inst('revfgotoel')], 'syl', '( %s -> %s e. ( 1o ^m %s ) )' % (A, FGOTO, S1))
MG = '( %s ^m %s )' % (Lt, St); evMG, mg = evaluate(w, A, MG, SM, extra_rules=extra); assert mg == '( 1o ^m %s )' % S1
fg2 = w.s([fg, evMG], 'eleqtrrd', '( %s -> %s e. %s )' % (A, FGOTO, MG))
q4 = w.s([tx2, fg2, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (A, Q4, ST1))
# push 1o FPUSH q4: 1o e. dom G, FPUSH e. ( ( G ` 1o ) ^m S )
o = w.s([], '1oex', '1o e. _V'); o1 = w.s([o, w.inst('prid2g')], 'ax-mp', '1o e. %s' % TWO); o1b = w.s([o1], 'a1i', '( %s -> 1o e. %s )' % (A, TWO))
KT = 'dom %s' % Gt; evK, kt = evaluate(w, A, KT, SM, extra_rules=extra); assert kt == TWO
k1 = w.s([o1b, evK], 'eleqtrrd', '( %s -> 1o e. %s )' % (A, KT))
fp = w.s([a, zz, w.inst('revfpushel')], 'syl2anc', '( %s -> %s e. ( A ^m %s ) )' % (A, FPUSH, S1))
MP = '( ( %s ` 1o ) ^m %s )' % (Gt, St); evMP, mp = evaluate(w, A, MP, SM, extra_rules=extra); assert mp == '( A ^m %s )' % S1, mp
fp2 = w.s([fp, evMP], 'eleqtrrd', '( %s -> %s e. %s )' % (A, FPUSH, MP))
kf = w.s([k1, fp2], 'jca', '( %s -> ( 1o e. %s /\\ %s e. %s ) )' % (A, KT, FPUSH, MP))
q2 = w.s([tx2, kf, q4, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (A, Q2, ST1))
# branch FBR q2 q3
fb = w.s([a, w.inst('revfbrel')], 'syl', '( %s -> %s e. ( 2o ^m %s ) )' % (A, FBR, S1))
MB = '( 2o ^m %s )' % St; evMB, mb = evaluate(w, A, MB, SM, extra_rules=extra); assert mb == '( 2o ^m %s )' % S1
fb2 = w.s([fb, evMB], 'eleqtrrd', '( %s -> %s e. %s )' % (A, FBR, MB))
qq = w.s([q2, q3], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, Q2, ST1, Q3, ST1))
q1 = w.s([tx2, fb2, qq, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (A, Q1, ST1))
# pop (/) FPOP q1
z = w.s([], '0ex', '(/) e. _V'); z1 = w.s([z, w.inst('prid1g')], 'ax-mp', '(/) e. %s' % TWO); z1b = w.s([z1], 'a1i', '( %s -> (/) e. %s )' % (A, TWO))
k0 = w.s([z1b, evK], 'eleqtrrd', '( %s -> (/) e. %s )' % (A, KT))
fo = w.s([a, w.inst('revfpopel')], 'syl', '( %s -> %s e. ( %s ^m ( %s X. %s ) ) )' % (A, FPOP, S1, S1, S1))
MK = '( %s ^m ( %s X. ( ( %s ` (/) ) |_| 1o ) ) )' % (St, St, Gt); evMK, mk = evaluate(w, A, MK, SM, extra_rules=extra); assert mk == '( %s ^m ( %s X. %s ) )' % (S1, S1, S1), mk
fo2 = w.s([fo, evMK], 'eleqtrrd', '( %s -> %s e. %s )' % (A, FPOP, MK))
kf0 = w.s([k0, fo2], 'jca', '( %s -> ( (/) e. %s /\\ %s e. %s ) )' % (A, KT, FPOP, MK))
w.qed([tx2, kf0, q1, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (A, STM, ST1))
run(w)
