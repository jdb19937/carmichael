import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
T='T'; PRT=PR(T); ST=STMT(T); STK='( TM2Stk ` T )'; SAT=SA(T); CFG='( TM2Cfg ` T )'
Gt, Lt, St, Kt = G(T), L(T), S(T), K(T)
CFGX = '( ( %s |_| 1o ) X. %s )' % (Lt, PRT)
NONE = '( inr ` (/) )'
def BODY(t, m, c): return sub(defbody('df-tm2step').split('|->', 2)[2].rsplit(')', 2)[0].strip(), {'t': t, 'm': m, 'c': c})
MPT = lambda t, m: '( c e. ( TM2Cfg ` %s ) |-> %s )' % (t, BODY(t, m, 'c'))

# tm2stepval
w = W('tm2stepval', 'Value of TM2step: the step function of program M as a mapping on configurations.')
A = '( t = T /\\ m = M )'
l1 = w.s([], 'simpl', '( %s -> t = T )' % A); l2 = w.s([], 'simpr', '( %s -> m = M )' % A)
c, mpt = w.congr(MPT('t', 'm'), {'t': 'T', 'm': 'M'}, A, {'t': l1, 'm': l2})
assert mpt == MPT('T', 'M')
d = w.s([], 'df-tm2step', 'TM2step = %s' % defbody('df-tm2step'))
f = w.s([c, d], 'ovmpoga', '( ( T e. _V /\\ M e. _V /\\ %s e. _V ) -> ( T TM2step M ) = %s )' % (mpt, mpt))
e1 = w.s([], 'fvex', '%s e. _V' % CFG); e2i = w.inst('mptexg'); e2 = w.s([e1, e2i], 'ax-mp', '%s e. _V' % mpt)
B = '( T e. V /\\ M e. W )'
x1 = w.s([], 'elex', '( T e. V -> T e. _V )'); x2 = w.s([], 'elex', '( M e. W -> M e. _V )')
a1 = w.s([x1], 'adantr', '( %s -> T e. _V )' % B); a2 = w.s([x2], 'adantl', '( %s -> M e. _V )' % B); a3 = w.s([e2], 'a1i', '( %s -> %s e. _V )' % (B, mpt))
w.qed([a1, a2, a3, f], 'syl3anc', '( %s -> ( T TM2step M ) = %s )' % (B, mpt))
run(w)

# tm2stepfv
w = W('tm2stepfv', 'Value of the step function at a configuration.')
B = '( T e. V /\\ M e. W )'; A = '( %s /\\ C e. %s )' % (B, CFG)
v = w.s([], 'tm2stepval', '( %s -> ( T TM2step M ) = %s )' % (B, MPT('T', 'M'))); v2 = w.s([v], 'adantr', '( %s -> ( T TM2step M ) = %s )' % (A, MPT('T', 'M')))
v3 = w.s([v2], 'fveq1d', '( %s -> ( ( T TM2step M ) ` C ) = ( %s ` C ) )' % (A, MPT('T', 'M')))
l = w.s([], 'id', '( c = C -> c = C )'); cg, bC = w.congr(BODY('T', 'M', 'c'), {'c': 'C'}, 'c = C', {'c': l})
e = w.s([], 'eqid', '%s = %s' % (MPT('T', 'M'), MPT('T', 'M')))
f = w.s([cg, e], 'fvmptg', '( ( C e. %s /\\ %s e. _V ) -> ( %s ` C ) = %s )' % (CFG, bC, MPT('T', 'M'), bC))
x1 = w.s([], 'fvex', '%s e. _V' % NONE); x2 = w.s([], 'fvex', '( inl ` ( ( M ` ( 2nd ` ( 1st ` C ) ) ) %s ( 2nd ` C ) ) ) e. _V' % SAT)
x3 = w.s([x1, x2], 'ifex', '%s e. _V' % bC)
c1 = w.s([], 'simpr', '( %s -> C e. %s )' % (A, CFG)); c2 = w.s([x3], 'a1i', '( %s -> %s e. _V )' % (A, bC))
f2 = w.s([c1, c2, f], 'syl2anc', '( %s -> ( %s ` C ) = %s )' % (A, MPT('T', 'M'), bC))
w.qed([v3, f2], 'eqtrd', '( %s -> ( ( T TM2step M ) ` C ) = %s )' % (A, bC))
run(w)

# tm2stepnone
w = W('tm2stepnone', 'The step function halts on a configuration without label: ` step <. none , v , S >. = none `.')
B = '( T e. V /\\ M e. W )'; SD = '( A e. %s /\\ D e. %s )' % (St, STK); A = '( %s /\\ %s )' % (B, SD)
C0 = '<. %s , <. A , D >. >.' % NONE
b = w.s([], 'simpl', '( %s -> %s )' % (A, B)); t = w.s([b], 'simpld', '( %s -> T e. V )' % A)
sd = w.s([], 'simpr', '( %s -> %s )' % (A, SD)); a = w.s([sd], 'simpld', '( %s -> A e. %s )' % (A, St)); d = w.s([sd], 'simprd', '( %s -> D e. %s )' % (A, STK))
n1 = w.s([], '0lt1o', '(/) e. 1o'); n2i = w.inst('djurcl'); n2 = w.s([n1, n2i], 'ax-mp', '%s e. ( %s |_| 1o )' % (NONE, Lt)); n3 = w.s([n2], 'a1i', '( %s -> %s e. ( %s |_| 1o ) )' % (A, NONE, Lt))
pi = w.inst('opelxpi'); p = w.s([a, d, pi], 'syl2anc', '( %s -> <. A , D >. e. %s )' % (A, PRT))
ci = w.inst('opelxpi'); c = w.s([n3, p, ci], 'syl2anc', '( %s -> %s e. %s )' % (A, C0, CFGX))
vi = w.inst('tm2cfgval'); v = w.s([t, vi], 'syl', '( %s -> %s = %s )' % (A, CFG, CFGX))
c2 = w.s([c, v], 'eleqtrrd', '( %s -> %s e. %s )' % (A, C0, CFG))
fi = w.inst('tm2stepfv'); f = w.s([b, c2, fi], 'syl2anc', '( %s -> ( ( T TM2step M ) ` %s ) = %s )' % (A, C0, BODY('T', 'M', C0)))
setmap = {'A': w.s([a], 'elexd', '( %s -> A e. _V )' % A), 'D': w.s([d], 'elexd', '( %s -> D e. _V )' % A)}
ev, res = evaluate(w, A, BODY('T', 'M', C0), setmap)
assert res == NONE, res
w.qed([f, ev], 'eqtrd', '( %s -> ( ( T TM2step M ) ` %s ) = %s )' % (A, C0, NONE))
run(w)

# tm2stepsome
w = W('tm2stepsome', 'The step function on a configuration with label: ` step <. some l , v , S >. = some ( stepAux ( M l ) v S ) `.')
B = '( T e. V /\\ M e. W )'; SD = '( A e. %s /\\ D e. %s )' % (St, STK); H = '( B e. %s /\\ %s )' % (Lt, SD); A = '( %s /\\ %s )' % (B, H)
C0 = '<. ( inl ` B ) , <. A , D >. >.'
b = w.s([], 'simpl', '( %s -> %s )' % (A, B)); t = w.s([b], 'simpld', '( %s -> T e. V )' % A)
h = w.s([], 'simpr', '( %s -> %s )' % (A, H)); lb = w.s([h], 'simpld', '( %s -> B e. %s )' % (A, Lt)); sd = w.s([h], 'simprd', '( %s -> %s )' % (A, SD))
a = w.s([sd], 'simpld', '( %s -> A e. %s )' % (A, St)); d = w.s([sd], 'simprd', '( %s -> D e. %s )' % (A, STK))
n2i = w.inst('djulcl'); n3 = w.s([lb, n2i], 'syl', '( %s -> ( inl ` B ) e. ( %s |_| 1o ) )' % (A, Lt))
pi = w.inst('opelxpi'); p = w.s([a, d, pi], 'syl2anc', '( %s -> <. A , D >. e. %s )' % (A, PRT))
ci = w.inst('opelxpi'); c = w.s([n3, p, ci], 'syl2anc', '( %s -> %s e. %s )' % (A, C0, CFGX))
vi = w.inst('tm2cfgval'); v = w.s([t, vi], 'syl', '( %s -> %s = %s )' % (A, CFG, CFGX))
c2 = w.s([c, v], 'eleqtrrd', '( %s -> %s e. %s )' % (A, C0, CFG))
fi = w.inst('tm2stepfv'); f = w.s([b, c2, fi], 'syl2anc', '( %s -> ( ( T TM2step M ) ` %s ) = %s )' % (A, C0, BODY('T', 'M', C0)))
bx = w.s([lb], 'elexd', '( %s -> B e. _V )' % A)
setmap = {'A': w.s([a], 'elexd', '( %s -> A e. _V )' % A), 'D': w.s([d], 'elexd', '( %s -> D e. _V )' % A), 'B': bx}
z = w.s([], '0ex', '(/) e. _V'); z2 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A)
nei = w.inst('inlneinr'); ne = w.s([bx, z2, nei], 'syl2anc', '( %s -> ( inl ` B ) =/= %s )' % (A, NONE))
ne2 = w.s([ne], 'neneqd', '( %s -> -. ( inl ` B ) = %s )' % (A, NONE))
iv = w.inst('inlval'); i1 = w.s([bx, iv], 'syl', '( %s -> ( inl ` B ) = <. (/) , B >. )' % A)
i2 = w.s([i1], 'fveq2d', '( %s -> ( 2nd ` ( inl ` B ) ) = ( 2nd ` <. (/) , B >. ) )' % A)
o2 = w.inst('op2ndg'); i3 = w.s([z2, bx, o2], 'syl2anc', '( %s -> ( 2nd ` <. (/) , B >. ) = B )' % A)
i4 = w.s([i2, i3], 'eqtrd', '( %s -> ( 2nd ` ( inl ` B ) ) = B )' % A)
def extra(n):
    if n.text() == '( 2nd ` ( inl ` B ) )': return ('B', i4)
    return None
ev, res = evaluate(w, A, BODY('T', 'M', C0), setmap, extra_rules=extra, ifrules={'( inl ` B ) = %s' % NONE: (False, ne2)})
assert res == '( inl ` ( ( M ` B ) %s <. A , D >. ) )' % SAT, res
w.qed([f, ev], 'eqtrd', '( %s -> ( ( T TM2step M ) ` %s ) = %s )' % (A, C0, res))
run(w)

# tm2stepf
w = W('tm2stepf', 'The step function of a program maps configurations to optional configurations.')
A = '( T e. V /\\ M : %s --> %s )' % (Lt, ST)
t = w.s([], 'simpl', '( %s -> T e. V )' % A); mf = w.s([], 'simpr', '( %s -> M : %s --> %s )' % (A, Lt, ST))
lx = w.s([], 'fvex', '%s e. _V' % Lt); lx2 = w.s([lx], 'a1i', '( %s -> %s e. _V )' % (A, Lt))
fxi = w.inst('fex'); mx = w.s([mf, lx2, fxi], 'syl2anc', '( %s -> M e. _V )' % A)
vi = w.inst('tm2stepval'); v = w.s([t, mx, vi], 'syl2anc', '( %s -> ( T TM2step M ) = %s )' % (A, MPT('T', 'M')))
A2 = '( %s /\\ c e. %s )' % (A, CFG)
COND = '( 1st ` c ) = %s' % NONE
ELSE = '( inl ` ( ( M ` ( 2nd ` ( 1st ` c ) ) ) %s ( 2nd ` c ) ) )' % SAT
DJC = '( %s |_| 1o )' % CFG
n1 = w.s([], '0lt1o', '(/) e. 1o'); n2i = w.inst('djurcl'); n2 = w.s([n1, n2i], 'ax-mp', '%s e. %s' % (NONE, DJC))
tcase = w.s([n2], 'a1i', '( ( %s /\\ %s ) -> %s e. %s )' % (A2, COND, NONE, DJC))
A3 = '( %s /\\ -. %s )' % (A2, COND)
t3 = w.s([t], 'ad2antrr', '( %s -> T e. V )' % A3); mf3 = w.s([mf], 'ad2antrr', '( %s -> M : %s --> %s )' % (A3, Lt, ST))
c3 = w.s([], 'simplr', '( %s -> c e. %s )' % (A3, CFG)); nc3 = w.s([], 'simpr', '( %s -> -. %s )' % (A3, COND))
cvi = w.inst('tm2cfgval'); cv = w.s([t3, cvi], 'syl', '( %s -> %s = %s )' % (A3, CFG, CFGX))
c4 = w.s([c3, cv], 'eleqtrd', '( %s -> c e. %s )' % (A3, CFGX))
x1i = w.inst('xp1st'); x1 = w.s([c4, x1i], 'syl', '( %s -> ( 1st ` c ) e. ( %s |_| 1o ) )' % (A3, Lt))
x2i = w.inst('xp2nd'); x2 = w.s([c4, x2i], 'syl', '( %s -> ( 2nd ` c ) e. %s )' % (A3, PRT))
dji = w.inst('djur'); dj = w.s([x1, dji], 'syl', '( %s -> ( E. l e. %s ( 1st ` c ) = ( inl ` l ) \\/ E. l e. 1o ( 1st ` c ) = ( inr ` l ) ) )' % (A3, Lt))
GOAL = '%s e. %s' % (ELSE, DJC)
# inl case
A4 = '( %s /\\ ( l e. %s /\\ ( 1st ` c ) = ( inl ` l ) ) )' % (A3, Lt)
l4 = w.s([], 'simprl', '( %s -> l e. %s )' % (A4, Lt)); e4 = w.s([], 'simprr', '( %s -> ( 1st ` c ) = ( inl ` l ) )' % A4)
lx4 = w.s([l4], 'elexd', '( %s -> l e. _V )' % A4)
iv = w.inst('inlval'); i1 = w.s([lx4, iv], 'syl', '( %s -> ( inl ` l ) = <. (/) , l >. )' % A4)
i0 = w.s([e4, i1], 'eqtrd', '( %s -> ( 1st ` c ) = <. (/) , l >. )' % A4)
i2 = w.s([i0], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` c ) ) = ( 2nd ` <. (/) , l >. ) )' % A4)
z = w.s([], '0ex', '(/) e. _V'); z4 = w.s([z], 'a1i', '( %s -> (/) e. _V )' % A4)
o2 = w.inst('op2ndg'); i3 = w.s([z4, lx4, o2], 'syl2anc', '( %s -> ( 2nd ` <. (/) , l >. ) = l )' % A4)
i4 = w.s([i2, i3], 'eqtrd', '( %s -> ( 2nd ` ( 1st ` c ) ) = l )' % A4)
i5 = w.s([i4], 'fveq2d', '( %s -> ( M ` ( 2nd ` ( 1st ` c ) ) ) = ( M ` l ) )' % A4)
i6 = w.s([i5], 'oveq1d', '( %s -> ( ( M ` ( 2nd ` ( 1st ` c ) ) ) %s ( 2nd ` c ) ) = ( ( M ` l ) %s ( 2nd ` c ) ) )' % (A4, SAT, SAT))
mf4 = w.s([mf3], 'adantr', '( %s -> M : %s --> %s )' % (A4, Lt, ST)); t4 = w.s([t3], 'adantr', '( %s -> T e. V )' % A4); x24 = w.s([x2], 'adantr', '( %s -> ( 2nd ` c ) e. %s )' % (A4, PRT))
fvi = w.inst('ffvelcdm'); ml = w.s([mf4, l4, fvi], 'syl2anc', '( %s -> ( M ` l ) e. %s )' % (A4, ST))
cli = w.inst('tm2sacl'); cl = w.s([t4, ml, x24, cli], 'syl3anc', '( %s -> ( ( M ` l ) %s ( 2nd ` c ) ) e. %s )' % (A4, SAT, CFG))
cl2 = w.s([i6, cl], 'eqeltrd', '( %s -> ( ( M ` ( 2nd ` ( 1st ` c ) ) ) %s ( 2nd ` c ) ) e. %s )' % (A4, SAT, CFG))
dli = w.inst('djulcl'); g4 = w.s([cl2, dli], 'syl', '( %s -> %s )' % (A4, GOAL))
g4b = w.s([g4], 'rexlimdvaa', '( %s -> ( E. l e. %s ( 1st ` c ) = ( inl ` l ) -> %s ) )' % (A3, Lt, GOAL))
# inr case
A5 = '( %s /\\ ( l e. 1o /\\ ( 1st ` c ) = ( inr ` l ) ) )' % A3
l5 = w.s([], 'simprl', '( %s -> l e. 1o )' % A5); e5 = w.s([], 'simprr', '( %s -> ( 1st ` c ) = ( inr ` l ) )' % A5)
e1o = w.s([], 'el1o', '( l e. 1o <-> l = (/) )'); l5b = w.s([l5, e1o], 'sylib', '( %s -> l = (/) )' % A5)
l5c = w.s([l5b], 'fveq2d', '( %s -> ( inr ` l ) = %s )' % (A5, NONE))
e5b = w.s([e5, l5c], 'eqtrd', '( %s -> %s )' % (A5, COND))
nc5 = w.s([nc3], 'adantr', '( %s -> -. %s )' % (A5, COND))
g5 = w.s([e5b, nc5], 'pm2.21dd', '( %s -> %s )' % (A5, GOAL))
g5b = w.s([g5], 'rexlimdvaa', '( %s -> ( E. l e. 1o ( 1st ` c ) = ( inr ` l ) -> %s ) )' % (A3, GOAL))
jd = w.s([g4b, g5b], 'jaod', '( %s -> ( ( E. l e. %s ( 1st ` c ) = ( inl ` l ) \\/ E. l e. 1o ( 1st ` c ) = ( inr ` l ) ) -> %s ) )' % (A3, Lt, GOAL))
fcase = w.s([dj, jd], 'mpd', '( %s -> %s )' % (A3, GOAL))
ifc = w.s([tcase, fcase], 'ifclda', '( %s -> %s e. %s )' % (A2, BODY('T', 'M', 'c'), DJC))
fm = w.s([ifc], 'fmptd', '( %s -> %s : %s --> %s )' % (A, MPT('T', 'M'), CFG, DJC))
fe = w.s([v], 'feq1d', '( %s -> ( ( T TM2step M ) : %s --> %s <-> %s : %s --> %s ) )' % (A, CFG, DJC, MPT('T', 'M'), CFG, DJC))
w.qed([fm, fe], 'mpbird', '( %s -> ( T TM2step M ) : %s --> %s )' % (A, CFG, DJC))
run(w)
