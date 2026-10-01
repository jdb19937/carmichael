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
ST1 = '( TM2Stmt ` %s )' % T1; STK1 = '( TM2Stk ` %s )' % T1; SA1 = '( TM2sa ` %s )' % T1; STEP1 = '( %s TM2step %s )' % (T1, M1)
DUMMY = {k: 'x' for k in ('Q', 'U', 'W', 'Z', 'A', FPOP, FBR, FPUSH, FGOTO, FLOAD, Q1, Q2, Q3, Q4, STM)}
PP = lambda u, v: '{ <. (/) , %s >. , <. 1o , %s >. }' % (u, v)
Lt = '( 2nd ` ( 1st ` %s ) )' % T1; St = '( 2nd ` %s )' % T1; Gt = '( 1st ` ( 1st ` %s ) )' % T1; KT = 'dom %s' % Gt

def ne01(w):
    a = w.s([], '1n0', '1o =/= (/)'); return w.s([a], 'necomi', '(/) =/= 1o')
def g1rules(w, A, ax, dom_as_2o=False):
    z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
    o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
    n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A)
    f0 = w.s([z2, ax, n2, w.inst('fvpr1g')], 'syl3anc', '( %s -> ( %s ` (/) ) = A )' % (A, G1))
    f1 = w.s([o2, ax, n2, w.inst('fvpr2g')], 'syl3anc', '( %s -> ( %s ` 1o ) = A )' % (A, G1))
    d = w.s([ax, ax, w.inst('dmpropg')], 'syl2anc', '( %s -> dom %s = %s )' % (A, G1, TWO))
    if dom_as_2o:
        d2 = w.s([], 'df2o3', '2o = %s' % TWO); d = w.s([d, d2], 'eqtr4di', '( %s -> dom %s = 2o )' % (A, G1))
    def extra(n):
        if n.text() == '( %s ` (/) )' % G1: return ('A', f0)
        if n.text() == '( %s ` 1o )' % G1: return ('A', f1)
        if n.text() == 'dom %s' % G1: return ('2o' if dom_as_2o else TWO, d)
        return None
    return extra

# ---- wrdfv0
w = W('wrdfv0', 'The first letter of a nonempty word is a letter of the alphabet.')
A = '( U e. Word A /\\ U =/= (/) )'
n = w.s([], 'lennncl', '( %s -> ( # ` U ) e. NN )' % A); g = w.s([n, w.inst('nnge1')], 'syl', '( %s -> 1 <_ ( # ` U ) )' % A)
u = w.s([], 'simpl', '( %s -> U e. Word A )' % A)
w.qed([u, g, w.inst('wrdsymb1')], 'syl2anc', '( %s -> ( U ` 0 ) e. A )' % A)
run(w)

# ---- ppstk
w = W('ppstk', 'A pair of words over A is a stack assignment of the reverse machine.')
A = '( A e. V /\\ ( U e. Word A /\\ W e. Word A ) )'
a = w.s([], 'simpl', '( %s -> A e. V )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
uw = w.s([], 'simpr', '( %s -> ( U e. Word A /\\ W e. Word A ) )' % A); u = w.s([uw], 'simpld', '( %s -> U e. Word A )' % A); ww = w.s([uw], 'simprd', '( %s -> W e. Word A )' % A)
ux = w.s([u], 'elexd', '( %s -> U e. _V )' % A); wx = w.s([ww], 'elexd', '( %s -> W e. _V )' % A)
tx = w.s([], 'opex', '%s e. _V' % T1); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T1))
IXP = 'X_ k e. %s Word ( %s ` k )' % (KT, Gt)
v = w.s([tx2, w.inst('tm2stkval')], 'syl', '( %s -> %s = %s )' % (A, STK1, IXP))
extra = g1rules(w, A, ax); SM = {'A': ax}
evK, kt = evaluate(w, A, KT, SM, extra_rules=extra); assert kt == TWO
P = PP('U', 'W')
px = w.s([], 'prex', '%s e. _V' % P); px2 = w.s([px], 'a1i', '( %s -> %s e. _V )' % (A, P))
z = w.s([], '0ex', '(/) e. _V'); o = w.s([], '1oex', '1o e. _V'); zo = w.s([z, o], 'pm3.2i', '( (/) e. _V /\\ 1o e. _V )'); zo2 = w.s([zo], 'a1i', '( %s -> ( (/) e. _V /\\ 1o e. _V ) )' % A)
uwx = w.s([ux, wx], 'jca', '( %s -> ( U e. _V /\\ W e. _V ) )' % A); n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A)
fn = w.s([zo2, uwx, n2, w.inst('fnprg')], 'syl3anc', '( %s -> %s Fn %s )' % (A, P, TWO))
fe = w.s([evK], 'fneq2d', '( %s -> ( %s Fn %s <-> %s Fn %s ) )' % (A, P, KT, P, TWO)); fn2 = w.s([fn, fe], 'mpbird', '( %s -> %s Fn %s )' % (A, P, KT))
BODY = '( %s ` k ) e. Word ( %s ` k )' % (P, Gt)
l0 = w.s([], 'id', '( k = (/) -> k = (/) )'); c0, b0 = w.wcongr(BODY, {'k': '(/)'}, 'k = (/)', {'k': l0})
l1 = w.s([], 'id', '( k = 1o -> k = 1o )'); c1, b1 = w.wcongr(BODY, {'k': '1o'}, 'k = 1o', {'k': l1})
r = w.s([c0, c1], 'ralprg', '( ( (/) e. _V /\\ 1o e. _V ) -> ( A. k e. %s %s <-> ( %s /\\ %s ) ) )' % (TWO, BODY, b0, b1))
r2 = w.s([zo, r], 'ax-mp', '( A. k e. %s %s <-> ( %s /\\ %s ) )' % (TWO, BODY, b0, b1))
z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
v0 = w.s([z2, ux, n2, w.inst('fvpr1g')], 'syl3anc', '( %s -> ( %s ` (/) ) = U )' % (A, P))
v1 = w.s([o2, wx, n2, w.inst('fvpr2g')], 'syl3anc', '( %s -> ( %s ` 1o ) = W )' % (A, P))
ev0, wd0 = evaluate(w, A, 'Word ( %s ` (/) )' % Gt, SM, extra_rules=extra); assert wd0 == 'Word A'
ev1, wd1 = evaluate(w, A, 'Word ( %s ` 1o )' % Gt, SM, extra_rules=extra); assert wd1 == 'Word A'
m0 = w.s([u, ev0], 'eleqtrrd', '( %s -> U e. Word ( %s ` (/) ) )' % (A, Gt)); m0b = w.s([v0, m0], 'eqeltrd', '( %s -> %s )' % (A, b0))
m1 = w.s([ww, ev1], 'eleqtrrd', '( %s -> W e. Word ( %s ` 1o ) )' % (A, Gt)); m1b = w.s([v1, m1], 'eqeltrd', '( %s -> %s )' % (A, b1))
mj = w.s([m0b, m1b], 'jca', '( %s -> ( %s /\\ %s ) )' % (A, b0, b1)); ral = w.s([mj, r2], 'sylibr', '( %s -> A. k e. %s %s )' % (A, TWO, BODY))
re = w.s([evK], 'raleqdv', '( %s -> ( A. k e. %s %s <-> A. k e. %s %s ) )' % (A, KT, BODY, TWO, BODY)); ral2 = w.s([ral, re], 'mpbird', '( %s -> A. k e. %s %s )' % (A, KT, BODY))
ex = w.s([], 'elixp2', '( %s e. %s <-> ( %s e. _V /\\ %s Fn %s /\\ A. k e. %s %s ) )' % (P, IXP, P, P, KT, KT, BODY))
q = w.s([px2, fn2, ral2, ex], 'syl3anbrc', '( %s -> %s e. %s )' % (A, P, IXP))
w.qed([q, v], 'eleqtrrd', '( %s -> %s e. %s )' % (A, P, STK1))
run(w)

# ---- revq4..revq1 (sub-statements)
def revq(label, target, desc):
    w = W(label, desc)
    A = '( A e. V /\\ Z e. A )'
    a = w.s([], 'simpl', '( %s -> A e. V )' % A); zz = w.s([], 'simpr', '( %s -> Z e. A )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
    tx = w.s([], 'opex', '%s e. _V' % T1); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T1))
    extra = g1rules(w, A, ax); SM = {'A': ax}
    def mem(elem, projexpr, evald, step):
        ev, r = evaluate(w, A, projexpr, SM, extra_rules=extra); assert r == evald, (r, evald)
        return w.s([step, ev], 'eleqtrrd', '( %s -> %s e. %s )' % (A, elem, projexpr))
    if target == 'Q4':
        fg = w.s([a, w.inst('revfgotoel')], 'syl', '( %s -> %s e. ( 1o ^m %s ) )' % (A, FGOTO, S1))
        fg2 = mem(FGOTO, '( %s ^m %s )' % (Lt, St), '( 1o ^m %s )' % S1, fg)
        w.qed([tx2, fg2, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (A, Q4, ST1))
    elif target == 'Q3':
        h = w.s([tx2, w.inst('tm2halt')], 'syl', '( %s -> <. 6 , (/) >. e. %s )' % (A, ST1))
        fl = w.s([a, w.inst('revfloadel')], 'syl', '( %s -> %s e. ( %s ^m %s ) )' % (A, FLOAD, S1, S1))
        fl2 = mem(FLOAD, '( %s ^m %s )' % (St, St), '( %s ^m %s )' % (S1, S1), fl)
        w.qed([tx2, fl2, h, w.inst('tm2load')], 'syl3anc', '( %s -> %s e. %s )' % (A, Q3, ST1))
    elif target == 'Q2':
        q4 = w.s([], 'revq4', '( %s -> %s e. %s )' % (A, Q4, ST1))
        o = w.s([], '1oex', '1o e. _V'); o1 = w.s([o, w.inst('prid2g')], 'ax-mp', '1o e. %s' % TWO); o1b = w.s([o1], 'a1i', '( %s -> 1o e. %s )' % (A, TWO))
        k1 = mem('1o', KT, TWO, o1b)
        fp = w.s([a, zz, w.inst('revfpushel')], 'syl2anc', '( %s -> %s e. ( A ^m %s ) )' % (A, FPUSH, S1))
        fp2 = mem(FPUSH, '( ( %s ` 1o ) ^m %s )' % (Gt, St), '( A ^m %s )' % S1, fp)
        kf = w.s([k1, fp2], 'jca', '( %s -> ( 1o e. %s /\\ %s e. ( ( %s ` 1o ) ^m %s ) ) )' % (A, KT, FPUSH, Gt, St))
        w.qed([tx2, kf, q4, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (A, Q2, ST1))
    elif target == 'Q1':
        q2 = w.s([], 'revq2', '( %s -> %s e. %s )' % (A, Q2, ST1)); q3 = w.s([], 'revq3', '( %s -> %s e. %s )' % (A, Q3, ST1))
        fb = w.s([a, w.inst('revfbrel')], 'syl', '( %s -> %s e. ( 2o ^m %s ) )' % (A, FBR, S1))
        fb2 = mem(FBR, '( 2o ^m %s )' % St, '( 2o ^m %s )' % S1, fb)
        qq = w.s([q2, q3], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, Q2, ST1, Q3, ST1))
        w.qed([tx2, fb2, qq, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (A, Q1, ST1))
    return run(w)
revq('revq4', 'Q4', 'The reverse machine: goto main.')
revq('revq3', 'Q3', 'The reverse machine: reset the state and halt.')
revq('revq2', 'Q2', 'The reverse machine: push the letter on the output stack and loop.')
revq('revq1', 'Q1', 'The reverse machine: branch on the popped letter.')

# ---- revstep0 / revstep1
def revstep(label, empty, desc):
    w = W(label, desc)
    if empty:
        A = '( ( A e. V /\\ Z e. A ) /\\ W e. Word A /\\ Q e. %s )' % S1
        az = w.s([], 'simp1', '( %s -> ( A e. V /\\ Z e. A ) )' % A); ww = w.s([], 'simp2', '( %s -> W e. Word A )' % A); q = w.s([], 'simp3', '( %s -> Q e. %s )' % (A, S1))
        U = '(/)'; u = w.s([], 'wrd0', '(/) e. Word A'); u = w.s([u], 'a1i', '( %s -> (/) e. Word A )' % A)
    else:
        A = '( ( A e. V /\\ Z e. A ) /\\ ( U e. Word A /\\ U =/= (/) /\\ W e. Word A ) /\\ Q e. %s )' % S1
        az = w.s([], 'simp1', '( %s -> ( A e. V /\\ Z e. A ) )' % A); h = w.s([], 'simp2', '( %s -> ( U e. Word A /\\ U =/= (/) /\\ W e. Word A ) )' % A); q = w.s([], 'simp3', '( %s -> Q e. %s )' % (A, S1))
        U = 'U'; u = w.s([h], 'simp1d', '( %s -> U e. Word A )' % A); un = w.s([h], 'simp2d', '( %s -> U =/= (/) )' % A); ww = w.s([h], 'simp3d', '( %s -> W e. Word A )' % A)
    a = w.s([az], 'simpld', '( %s -> A e. V )' % A); zz = w.s([az], 'simprd', '( %s -> Z e. A )' % A); ax = w.s([a], 'elexd', '( %s -> A e. _V )' % A)
    tx = w.s([], 'opex', '%s e. _V' % T1); tx2 = w.s([tx], 'a1i', '( %s -> %s e. _V )' % (A, T1))
    mx = w.s([], 'snex', '%s e. _V' % M1); mx2 = w.s([mx], 'a1i', '( %s -> %s e. _V )' % (A, M1))
    extra = g1rules(w, A, ax, dom_as_2o=True); SM = {'A': ax, 'Z': w.s([zz], 'elexd', '( %s -> Z e. _V )' % A)}
    ux = w.s([u], 'elexd', '( %s -> U e. _V )' % A) if not empty else w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    wx = w.s([ww], 'elexd', '( %s -> W e. _V )' % A)
    SM['U'] = ux; SM['W'] = wx; SM['Q'] = w.s([q], 'elexd', '( %s -> Q e. _V )' % A)
    def mem(elem, projexpr, evald, step):
        ev, r = evaluate(w, A, projexpr, SM, extra_rules=extra); assert r == evald, (r, evald)
        return w.s([step, ev], 'eleqtrrd', '( %s -> %s e. %s )' % (A, elem, projexpr))
    def stk(u_, w_, us, ws):
        j = w.s([us, ws], 'jca', '( %s -> ( %s e. Word A /\\ %s e. Word A ) )' % (A, u_, w_))
        return w.s([a, j, w.inst('ppstk')], 'syl2anc', '( %s -> %s e. %s )' % (A, PP(u_, w_), STK1))
    P0 = PP(U, 'W'); C0 = '<. ( inl ` (/) ) , <. Q , %s >. >.' % P0
    # step: tm2stepsome
    z = w.s([], '0lt1o', '(/) e. 1o'); z2 = w.s([z], 'a1i', '( %s -> (/) e. 1o )' % A)
    zl = mem('(/)', Lt, '1o', z2); qs = mem('Q', St, S1, q); d0 = stk(U, 'W', u, ww)
    sd = w.s([qs, d0], 'jca', '( %s -> ( Q e. %s /\\ %s e. %s ) )' % (A, St, P0, STK1))
    hy = w.s([zl, sd], 'jca', '( %s -> ( (/) e. %s /\\ ( Q e. %s /\\ %s e. %s ) ) )' % (A, Lt, St, P0, STK1))
    tm = w.s([tx2, mx2], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (A, T1, M1))
    stp = w.s([tm, hy, w.inst('tm2stepsome')], 'syl2anc', '( %s -> ( %s ` %s ) = ( inl ` ( ( %s ` (/) ) %s <. Q , %s >. ) ) )' % (A, STEP1, C0, M1, SA1, P0))
    zx = w.s([], '0ex', '(/) e. _V'); sx = w.s([], 'opex', '%s e. _V' % STM); fv = w.s([zx, sx, w.inst('fvsng')], 'mp2an', '( %s ` (/) ) = %s' % (M1, STM))
    fv2 = w.s([fv], 'a1i', '( %s -> ( %s ` (/) ) = %s )' % (A, M1, STM)); fv3 = w.s([fv2], 'oveq1d', '( %s -> ( ( %s ` (/) ) %s <. Q , %s >. ) = ( %s %s <. Q , %s >. ) )' % (A, M1, SA1, P0, STM, SA1, P0))
    # pop
    q1 = w.s([az, w.inst('revq1')], 'syl', '( %s -> %s e. %s )' % (A, Q1, ST1))
    zk = w.s([zx, w.inst('prid1g')], 'ax-mp', '(/) e. %s' % TWO); d23 = w.s([], 'df2o3', '2o = %s' % TWO); zk2 = w.s([d23], 'eleq2i', '( (/) e. 2o <-> (/) e. %s )' % TWO); zk3 = w.s([zk, zk2], 'mpbir', '(/) e. 2o'); zk4 = w.s([zk3], 'a1i', '( %s -> (/) e. 2o )' % A)
    k0 = mem('(/)', KT, '2o', zk4)
    fo = w.s([a, w.inst('revfpopel')], 'syl', '( %s -> %s e. ( %s ^m ( %s X. %s ) ) )' % (A, FPOP, S1, S1, S1))
    fo2 = mem(FPOP, '( %s ^m ( %s X. ( ( %s ` (/) ) |_| 1o ) ) )' % (St, St, Gt), '( %s ^m ( %s X. %s ) )' % (S1, S1, S1), fo)
    hp = w.s([k0, fo2, q1], '3jca', '( %s -> ( (/) e. %s /\\ %s e. ( %s ^m ( %s X. ( ( %s ` (/) ) |_| 1o ) ) ) /\\ %s e. %s ) )' % (A, KT, FPOP, St, St, Gt, Q1, ST1))
    ws = W('scratch', ''); _, RHSpop = evaluate(ws, 'ph', CLAUSE('T', SA1, '<. 2 , <. (/) , <. %s , %s >. >. >.' % (FPOP, Q1), '<. Q , %s >.' % P0), DUMMY); RHSpop = sub(RHSpop, {'T': T1})
    pop = w.s([tx2, hp, sd, w.inst('tm2sapop')], 'syl3anc', '( %s -> ( %s %s <. Q , %s >. ) = %s )' % (A, STM, SA1, P0, RHSpop))
    # evaluate RHSpop: PP ` (/) -> U ; head ; FPOP value ; update
    n = ne01(w); n2 = w.s([n], 'a1i', '( %s -> (/) =/= 1o )' % A); zz2 = w.s([zx], 'a1i', '( %s -> (/) e. _V )' % A)
    pv0 = w.s([zz2, ux, n2, w.inst('fvpr1g')], 'syl3anc', '( %s -> ( %s ` (/) ) = %s )' % (A, P0, U))
    o = w.s([], '1oex', '1o e. _V'); o2 = w.s([o], 'a1i', '( %s -> 1o e. _V )' % A)
    pv1 = w.s([o2, wx, n2, w.inst('fvpr2g')], 'syl3anc', '( %s -> ( %s ` 1o ) = W )' % (A, P0))
    rules1 = {('( %s ` (/) )' % P0): (U, pv0), ('( %s ` 1o )' % P0): ('W', pv1)}
    def ex1(nd):
        r = extra(nd)
        if r: return r
        return rules1.get(nd.text())
    e1, R1 = evaluate(w, A, RHSpop, SM, extra_rules=ex1)
    # now R1 has HEAD = if ( U = (/) , none , inl ( U ` 0 ) ) and tail ( U substr <. 1 , ( # ` U ) >. )
    if empty:
        sw = w.s([], 'swrd0', '( (/) substr <. 1 , ( # ` (/) ) >. ) = (/)'); sw2 = w.s([sw], 'a1i', '( %s -> ( (/) substr <. 1 , ( # ` (/) ) >. ) = (/) )' % A)
        TAIL = '(/)'; tailstep = sw2; tailw = u
        HEADV = NONE; ifr = {}
    else:
        TAIL = '( U substr <. 1 , ( # ` U ) >. )'; tailstep = None
        tailw = w.s([u, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word A )' % (A, TAIL))
        un2 = w.s([un], 'neneqd', '( %s -> -. U = (/) )' % A); ifr = {'U = (/)': (False, un2)}
        HEADV = '( inl ` ( U ` 0 ) )'
    tailx = w.s([tailw], 'elexd', '( %s -> %s e. _V )' % (A, TAIL))
    upd = w.s([ux, wx, tailx, w.inst('ppupd0')], 'syl3anc', '( %s -> ( ( %s |` ( 2o \\ { (/) } ) ) u. { <. (/) , %s >. } ) = %s )' % (A, P0, TAIL, PP(TAIL, 'W')))
    if empty:
        upd0 = w.s([sw2], 'opeq2d', '( %s -> <. (/) , ( (/) substr <. 1 , ( # ` (/) ) >. ) >. = <. (/) , (/) >. )' % A)
        upd0b = w.s([upd0], 'sneqd', '( %s -> { <. (/) , ( (/) substr <. 1 , ( # ` (/) ) >. ) >. } = { <. (/) , (/) >. } )' % A)
        upd0c = w.s([upd0b], 'uneq2d', '( %s -> ( ( %s |` ( 2o \\ { (/) } ) ) u. { <. (/) , ( (/) substr <. 1 , ( # ` (/) ) >. ) >. } ) = ( ( %s |` ( 2o \\ { (/) } ) ) u. { <. (/) , (/) >. } ) )' % (A, P0, P0))
        upd = w.s([upd0c, upd], 'eqtrd', '( %s -> ( ( %s |` ( 2o \\ { (/) } ) ) u. { <. (/) , ( (/) substr <. 1 , ( # ` (/) ) >. ) >. } ) = %s )' % (A, P0, PP(TAIL, 'W')))
        UPDT = '( ( %s |` ( 2o \\ { (/) } ) ) u. { <. (/) , ( (/) substr <. 1 , ( # ` (/) ) >. ) >. } )' % P0
    else:
        UPDT = '( ( %s |` ( 2o \\ { (/) } ) ) u. { <. (/) , %s >. } )' % (P0, TAIL)
    P1 = PP(TAIL, 'W')
    # head value step: HEAD -> HEADV
    HEAD = 'if ( %s = (/) , %s , ( inl ` ( %s ` 0 ) ) )' % (U, NONE, U)
    if empty:
        hd = w.s([w.s([], 'eqid', '(/) = (/)')], 'a1i', '( %s -> (/) = (/) )' % A); hdv = w.s([hd], 'iftrued', '( %s -> %s = %s )' % (A, HEAD, HEADV))
    else:
        hdv = w.s([un2], 'iffalsed', '( %s -> %s = %s )' % (A, HEAD, HEADV))
    # HEADV e. S1
    if empty:
        hs = w.s([z, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, S1)); hs2 = w.s([hs], 'a1i', '( %s -> %s e. %s )' % (A, HEADV, S1))
    else:
        u0 = w.s([u, un, w.inst('wrdfv0')], 'syl2anc', '( %s -> ( U ` 0 ) e. A )' % A); hs2 = w.s([u0, w.inst('djulcl')], 'syl', '( %s -> %s e. %s )' % (A, HEADV, S1))
    fpv = w.s([q, hs2, w.inst('revfpop')], 'syl2anc', '( %s -> ( %s ` <. Q , %s >. ) = %s )' % (A, FPOP, HEADV, HEADV))
    def ex2(nd):
        r = extra(nd)
        if r: return r
        if nd.text() == HEAD: return (HEADV, hdv)
        if nd.text() == '( %s ` <. Q , %s >. )' % (FPOP, HEADV): return (HEADV, fpv)
        if nd.text() == UPDT: return (P1, upd)
        return None
    e2, R2 = evaluate(w, A, R1, SM, extra_rules=ex2)
    assert R2 == '( %s %s <. %s , %s >. )' % (Q1, SA1, HEADV, P1), R2
    # branch
    q2 = w.s([az, w.inst('revq2')], 'syl', '( %s -> %s e. %s )' % (A, Q2, ST1)); q3 = w.s([az, w.inst('revq3')], 'syl', '( %s -> %s e. %s )' % (A, Q3, ST1))
    fb = w.s([a, w.inst('revfbrel')], 'syl', '( %s -> %s e. ( 2o ^m %s ) )' % (A, FBR, S1)); fb2 = mem(FBR, '( 2o ^m %s )' % St, '( 2o ^m %s )' % S1, fb)
    hb = w.s([fb2, q2, q3], '3jca', '( %s -> ( %s e. ( 2o ^m %s ) /\\ %s e. %s /\\ %s e. %s ) )' % (A, FBR, St, Q2, ST1, Q3, ST1))
    hvs = mem(HEADV, St, S1, hs2); d1 = stk(TAIL, 'W', tailw, ww); sd1 = w.s([hvs, d1], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, HEADV, St, P1, STK1))
    _, RHSbr = evaluate(ws, 'ph', CLAUSE('T', SA1, Q1, '<. %s , %s >.' % (HEADV, P1)), DUMMY); RHSbr = sub(RHSbr, {'T': T1})
    br = w.s([tx2, hb, sd1, w.inst('tm2sabr')], 'syl3anc', '( %s -> %s = %s )' % (A, R2, RHSbr))
    fbv = w.s([hs2, w.inst('revfbr')], 'syl', '( %s -> ( %s ` %s ) = if ( %s = %s , (/) , 1o ) )' % (A, FBR, HEADV, HEADV, NONE))
    if empty:
        fbv2, _ = evaluate(w, A, 'if ( %s = %s , (/) , 1o )' % (HEADV, NONE), SM); FBV = '(/)'
        nn = w.s([], '1n0', '1o =/= (/)'); nn2 = w.s([nn], 'nesymi', '-. (/) = 1o'); nn3 = w.s([nn2], 'a1i', '( %s -> -. (/) = 1o )' % A); ifr2 = {'(/) = 1o': (False, nn3)}
    else:
        u0x = w.s([u0], 'elexd', '( %s -> ( U ` 0 ) e. _V )' % A); zz3 = w.s([zx], 'a1i', '( %s -> (/) e. _V )' % A)
        nei = w.s([u0x, zz3, w.inst('inlneinr')], 'syl2anc', '( %s -> %s =/= %s )' % (A, HEADV, NONE)); nei2 = w.s([nei], 'neneqd', '( %s -> -. %s = %s )' % (A, HEADV, NONE))
        fbv2, _ = evaluate(w, A, 'if ( %s = %s , (/) , 1o )' % (HEADV, NONE), SM, ifrules={'%s = %s' % (HEADV, NONE): (False, nei2)}); FBV = '1o'; ifr2 = {}
    fbv3 = w.s([fbv, fbv2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (A, FBR, HEADV, FBV))
    def ex3(nd):
        if nd.text() == '( %s ` %s )' % (FBR, HEADV): return (FBV, fbv3)
        return None
    e3, R3 = evaluate(w, A, RHSbr, SM, extra_rules=ex3, ifrules=ifr2)
    if empty:
        assert R3 == '( %s %s <. %s , %s >. )' % (Q3, SA1, HEADV, P1), R3
        # load
        fl = w.s([a, w.inst('revfloadel')], 'syl', '( %s -> %s e. ( %s ^m %s ) )' % (A, FLOAD, S1, S1)); fl2 = mem(FLOAD, '( %s ^m %s )' % (St, St), '( %s ^m %s )' % (S1, S1), fl)
        hh = w.s([tx2, w.inst('tm2halt')], 'syl', '( %s -> <. 6 , (/) >. e. %s )' % (A, ST1))
        hl = w.s([fl2, hh], 'jca', '( %s -> ( %s e. ( %s ^m %s ) /\\ <. 6 , (/) >. e. %s ) )' % (A, FLOAD, St, St, ST1))
        _, RHSld = evaluate(ws, 'ph', CLAUSE('T', SA1, Q3, '<. %s , %s >.' % (HEADV, P1)), DUMMY); RHSld = sub(RHSld, {'T': T1})
        ld = w.s([tx2, hl, sd1, w.inst('tm2saload')], 'syl3anc', '( %s -> %s = %s )' % (A, R3, RHSld))
        flv = w.s([hs2, w.inst('revfload')], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A, FLOAD, HEADV, NONE))
        def ex4(nd):
            if nd.text() == '( %s ` %s )' % (FLOAD, HEADV): return (NONE, flv)
            return None
        e4, R4 = evaluate(w, A, RHSld, SM, extra_rules=ex4)
        assert R4 == '( <. 6 , (/) >. %s <. %s , %s >. )' % (SA1, NONE, P1), R4
        ns = w.s([z, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, S1)); ns2 = w.s([ns], 'a1i', '( %s -> %s e. %s )' % (A, NONE, S1)); nss = mem(NONE, St, S1, ns2)
        sd2 = w.s([nss, d1], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, NONE, St, P1, STK1))
        FIN = '<. %s , <. %s , %s >. >.' % (NONE, NONE, P1)
        ht = w.s([tx2, sd2, w.inst('tm2sahalt')], 'syl2anc', '( %s -> %s = %s )' % (A, R4, FIN))
        chain = [stp, fv3, pop, e1, e2, br, e3, ld, e4, ht]
    else:
        assert R3 == '( %s %s <. %s , %s >. )' % (Q2, SA1, HEADV, P1), R3
        # push 1o FPUSH Q4
        q4 = w.s([az, w.inst('revq4')], 'syl', '( %s -> %s e. %s )' % (A, Q4, ST1))
        ok1 = w.s([o, w.inst('prid2g')], 'ax-mp', '1o e. %s' % TWO); ok2 = w.s([d23], 'eleq2i', '( 1o e. 2o <-> 1o e. %s )' % TWO); ok3 = w.s([ok1, ok2], 'mpbir', '1o e. 2o'); ok4 = w.s([ok3], 'a1i', '( %s -> 1o e. 2o )' % A)
        k1 = mem('1o', KT, '2o', ok4)
        fp = w.s([a, zz, w.inst('revfpushel')], 'syl2anc', '( %s -> %s e. ( A ^m %s ) )' % (A, FPUSH, S1)); fp2 = mem(FPUSH, '( ( %s ` 1o ) ^m %s )' % (Gt, St), '( A ^m %s )' % S1, fp)
        hps = w.s([k1, fp2, q4], '3jca', '( %s -> ( 1o e. %s /\\ %s e. ( ( %s ` 1o ) ^m %s ) /\\ %s e. %s ) )' % (A, KT, FPUSH, Gt, St, Q4, ST1))
        _, RHSpu = evaluate(ws, 'ph', CLAUSE('T', SA1, Q2, '<. %s , %s >.' % (HEADV, P1)), DUMMY); RHSpu = sub(RHSpu, {'T': T1})
        pu = w.s([tx2, hps, sd1, w.inst('tm2sapush')], 'syl3anc', '( %s -> %s = %s )' % (A, R3, RHSpu))
        fpv_ = w.s([hs2, zz, w.inst('revfpush')], 'syl2anc', '( %s -> ( %s ` %s ) = if ( %s = %s , Z , ( 2nd ` %s ) ) )' % (A, FPUSH, HEADV, HEADV, NONE, HEADV))
        iv = w.s([u0x, w.inst('inlval')], 'syl', '( %s -> %s = <. (/) , ( U ` 0 ) >. )' % (A, HEADV)); iv2 = w.s([iv], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. (/) , ( U ` 0 ) >. ) )' % (A, HEADV))
        iv3 = w.s([zz3, u0x, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. (/) , ( U ` 0 ) >. ) = ( U ` 0 ) )' % A); iv4 = w.s([iv2, iv3], 'eqtrd', '( %s -> ( 2nd ` %s ) = ( U ` 0 ) )' % (A, HEADV))
        def ex5(nd):
            if nd.text() == '( 2nd ` %s )' % HEADV: return ('( U ` 0 )', iv4)
            return None
        fpv2, _ = evaluate(w, A, 'if ( %s = %s , Z , ( 2nd ` %s ) )' % (HEADV, NONE, HEADV), SM, extra_rules=ex5, ifrules={'%s = %s' % (HEADV, NONE): (False, nei2)})
        fpv3 = w.s([fpv_, fpv2], 'eqtrd', '( %s -> ( %s ` %s ) = ( U ` 0 ) )' % (A, FPUSH, HEADV))
        tailx2 = tailx; pv1b = w.s([o2, wx, n2, w.inst('fvpr2g')], 'syl3anc', '( %s -> ( %s ` 1o ) = W )' % (A, P1))
        CONS = '( <" ( U ` 0 ) "> ++ W )'
        s1 = w.s([u0, w.inst('s1cl')], 'syl', '( %s -> <" ( U ` 0 ) "> e. Word A )' % A); cc = w.s([s1, ww, w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word A )' % (A, CONS)); ccx = w.s([cc], 'elexd', '( %s -> %s e. _V )' % (A, CONS))
        upd1 = w.s([tailx2, wx, ccx, w.inst('ppupd1')], 'syl3anc', '( %s -> ( ( %s |` ( 2o \\ { 1o } ) ) u. { <. 1o , %s >. } ) = %s )' % (A, P1, CONS, PP(TAIL, CONS)))
        P2 = PP(TAIL, CONS)
        def ex6(nd):
            r = extra(nd)
            if r: return r
            if nd.text() == '( %s ` %s )' % (FPUSH, HEADV): return ('( U ` 0 )', fpv3)
            if nd.text() == '( %s ` 1o )' % P1: return ('W', pv1b)
            if nd.text() == '( ( %s |` ( 2o \\ { 1o } ) ) u. { <. 1o , %s >. } )' % (P1, CONS): return (P2, upd1)
            return None
        e5, R5 = evaluate(w, A, RHSpu, SM, extra_rules=ex6)
        assert R5 == '( %s %s <. %s , %s >. )' % (Q4, SA1, HEADV, P2), R5
        # goto
        fg = w.s([a, w.inst('revfgotoel')], 'syl', '( %s -> %s e. ( 1o ^m %s ) )' % (A, FGOTO, S1)); fg2 = mem(FGOTO, '( %s ^m %s )' % (Lt, St), '( 1o ^m %s )' % S1, fg)
        d2_ = stk(TAIL, CONS, tailw, cc); sd3 = w.s([hvs, d2_], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, HEADV, St, P2, STK1))
        _, RHSgo = evaluate(ws, 'ph', CLAUSE('T', SA1, Q4, '<. %s , %s >.' % (HEADV, P2)), DUMMY); RHSgo = sub(RHSgo, {'T': T1})
        go = w.s([tx2, fg2, sd3, w.inst('tm2sagoto')], 'syl3anc', '( %s -> %s = %s )' % (A, R5, RHSgo))
        fgv = w.s([hs2, w.inst('revfgoto')], 'syl', '( %s -> ( %s ` %s ) = (/) )' % (A, FGOTO, HEADV))
        def ex7(nd):
            if nd.text() == '( %s ` %s )' % (FGOTO, HEADV): return ('(/)', fgv)
            return None
        e6, FIN = evaluate(w, A, RHSgo, SM, extra_rules=ex7)
        assert FIN == '<. ( inl ` (/) ) , <. %s , %s >. >.' % (HEADV, P2), FIN
        chain = [stp, fv3, pop, e1, e2, br, e3, pu, e5, go, e6]
    # compose: ( STEP1 ` C0 ) = ( inl ` ( ( M1 ` (/) ) SA <Q,P0> ) ); inner chain equalities on the argument of inl
    inner = [fv3, pop, e1, e2, br, e3] + ([ld, e4, ht] if empty else [pu, e5, go, e6])
    # each is ( A -> X_i = X_{i+1} ); chain with eqtrd
    def rhs(st):
        for l in w.lines:
            if l.startswith(st + ':'):
                f = l.split('|-', 1)[1].strip(); return parse_wff(f[len('( %s -> ' % A):-2]).kids[1].text(), parse_wff(f[len('( %s -> ' % A):-2]).kids[0].text()
    acc = inner[0]; lhs0 = rhs(inner[0])[1]
    for st in inner[1:]:
        r = rhs(st)[0]
        acc = w.s([acc, st], 'eqtrd', '( %s -> %s = %s )' % (A, lhs0, r))
    accf = w.s([acc], 'fveq2d', '( %s -> ( inl ` %s ) = ( inl ` %s ) )' % (A, lhs0, FIN))
    w.qed([stp, accf], 'eqtrd', '( %s -> ( %s ` %s ) = ( inl ` %s ) )' % (A, STEP1, C0, FIN))
    return run(w)
revstep('revstep0', True, 'One step of the reverse machine on an empty input stack: reset the state and halt.')
revstep('revstep1', False, 'One step of the reverse machine on a nonempty input stack: move the top letter to the output stack.')
