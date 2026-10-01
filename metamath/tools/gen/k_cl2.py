import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
T='T'; PRT=PR(T); ST=STMT(T); Ly=LY(T); STK='( TM2Stk ` T )'; SAT=SA(T); CFG='( TM2Cfg ` T )'
def LYn(n): return LYN(T, n)
Gt, Lt, St, Kt = G(T), L(T), S(T), K(T)
MAPG = '( %s ^m %s )' % (Lt, St); MAPS = '( %s ^m %s )' % (St, St); MAPB = '( 2o ^m %s )' % St
MAPP = lambda k: '( ( %s ` %s ) ^m %s )' % (Gt, k, St)
MAPK = lambda k: '( %s ^m ( %s X. ( ( %s ` %s ) |_| 1o ) ) )' % (St, St, Gt, k)
IHN = lambda n: 'A. q e. %s A. p e. %s ( q %s p ) e. %s' % (LYn(n), PRT, SAT, CFG)
WFF2 = open(os.path.join(ROOT, 'scratch', 'tm2layelim2.wff')).read().strip()

def ih_inst(w, A, ih, rst, yst, R, Y):
    l1 = w.s([], 'id', '( q = %s -> q = %s )' % (R, R))
    c1, _ = w.wcongr('A. p e. %s ( q %s p ) e. %s' % (PRT, SAT, CFG), {'q': R}, 'q = %s' % R, {'q': l1})
    i1 = w.s([c1, ih, rst], 'rspcdva', '( %s -> A. p e. %s ( %s %s p ) e. %s )' % (A, PRT, R, SAT, CFG))
    l2 = w.s([], 'id', '( p = %s -> p = %s )' % (Y, Y))
    c2, _ = w.wcongr('( %s %s p ) e. %s' % (R, SAT, CFG), {'p': Y}, 'p = %s' % Y, {'p': l2})
    return w.s([c2, i1, yst], 'rspcdva', '( %s -> ( %s %s %s ) e. %s )' % (A, R, SAT, Y, CFG))

# ---- tm2sacl2: case assembly
w = W('tm2saclx', 'Closure of TM2sa at statements first appearing at depth N + 1, given closure at depth N.')
LYN_ = LYn('N'); DOM = '( %s \\ %s )' % (LYn('suc N'), LYN_)
B0 = '( ( T e. V /\\ N e. _om ) /\\ %s /\\ P e. %s )' % (IHN('N'), PRT)
A0 = '( %s /\\ Q e. %s )' % (B0, DOM)
GOAL = '( Q %s P ) e. %s' % (SAT, CFG)
b0 = w.s([], 'simpl', '( %s -> %s )' % (A0, B0))
base = {'b0': b0, 'qd': w.s([], 'simpr', '( %s -> Q e. %s )' % (A0, DOM))}
tn = w.s([b0], 'simp1d', '( %s -> ( T e. V /\\ N e. _om ) )' % A0)
base['t'] = w.s([tn], 'simpld', '( %s -> T e. V )' % A0); base['n'] = w.s([tn], 'simprd', '( %s -> N e. _om )' % A0)
BT = {'b0': B0, 't': 'T e. V', 'n': 'N e. _om', 'qd': 'Q e. %s' % DOM}
levels = [A0]; ctx = []; cache = {}
def lift(name, target_level):
    if isinstance(name, int):
        v, d = ctx[name]; lvl = name + 1
        key = (v, d, levels[target_level])
        if key in cache: return cache[key]
        if target_level == lvl: st = w.s([], 'simpr', '( %s -> %s e. %s )' % (levels[lvl], v, d))
        else: st = w.s([lift(name, target_level - 1)], 'adantr', '( %s -> %s e. %s )' % (levels[target_level], v, d))
    else:
        key = (name, levels[target_level])
        if key in cache: return cache[key]
        if target_level == 0: st = base[name]
        else: st = w.s([lift(name, target_level - 1)], 'adantr', '( %s -> %s )' % (levels[target_level], BT[name]))
    cache[key] = st; return st
def find(v):
    for i, (x, d) in enumerate(ctx):
        if x == v: return i, d
    raise KeyError(v)
def leaf(node, level):
    ante = levels[level]
    tup = node.kids[1].text(); tag = parse(tup).kids[0].text()
    b = lift('b0', level)
    GT = sub(GOAL, {'Q': tup})
    if tag == '6':
        c1 = w.s([], 'tm2sacl6', '( %s -> %s )' % (B0, GT)); c4 = w.s([b, c1], 'syl', '( %s -> %s )' % (ante, GT))
    else:
        if tag == '5':
            hyps = 'f e. %s' % MAPG; c3 = lift(find('f')[0], level)
        elif tag == '3':
            hyps = '( f e. %s /\\ g e. %s )' % (MAPS, LYN_)
            c3 = w.s([lift(find('f')[0], level), lift(find('g')[0], level)], 'jca', '( %s -> %s )' % (ante, hyps))
        elif tag == '4':
            hyps = '( f e. %s /\\ h e. %s /\\ g e. %s )' % (MAPB, LYN_, LYN_)
            c3 = w.s([lift(find('f')[0], level), lift(find('h')[0], level), lift(find('g')[0], level)], '3jca', '( %s -> %s )' % (ante, hyps))
        else:
            mapf = MAPP('k') if tag == '0' else MAPK('k')
            hyps = '( k e. %s /\\ f e. %s /\\ g e. %s )' % (Kt, mapf, LYN_)
            c3 = w.s([lift(find('k')[0], level), lift(find('f')[0], level), lift(find('g')[0], level)], '3jca', '( %s -> %s )' % (ante, hyps))
        c1 = w.s([], 'tm2sacl' + tag, '( %s -> ( %s -> %s ) )' % (B0, hyps, GT))
        c4a = w.s([b, c1], 'syl', '( %s -> ( %s -> %s ) )' % (ante, hyps, GT))
        c4 = w.s([c3, c4a], 'mpd', '( %s -> %s )' % (ante, GT))
    l = w.s([], 'id', '( Q = %s -> Q = %s )' % (tup, tup))
    c5, _ = w.wcongr(GOAL, {'Q': tup}, 'Q = %s' % tup, {'Q': l})
    return w.s([c4, c5], 'syl5ibrcom', '( %s -> ( Q = %s -> %s ) )' % (ante, tup, GOAL))
def handle(node, level):
    ante = levels[level]
    if node.kind == 'or':
        s1 = handle(node.kids[0], level); s2 = handle(node.kids[1], level)
        return w.s([s1, s2], 'jaod', '( %s -> ( %s -> %s ) )' % (ante, node.text(), GOAL))
    if node.kind == 'rex':
        v = node.bound[0]; A_, body = node.kids
        ctx.append((v, A_.text())); levels.append('( %s /\\ %s e. %s )' % (ante, v, A_.text()))
        s = handle(body, level + 1)
        ctx.pop(); levels.pop()
        return w.s([s], 'rexlimdva', '( %s -> ( %s -> %s ) )' % (ante, node.text(), GOAL))
    if node.kind == 'eq': return leaf(node, level)
    raise NotImplementedError(node.kind)
WFFX = sub(WFF2, {'X': LYN_}); tree = parse_wff(WFFX); REST = tree.kids[1]
e1i = w.inst('eldifi'); e1 = w.s([base['qd'], e1i], 'syl', '( %s -> Q e. %s )' % (A0, LYn('suc N')))
e2i = w.inst('tm2laysuc'); e2 = w.s([base['n'], e2i], 'syl', '( %s -> %s = ( T TM2lay %s ) )' % (A0, LYn('suc N'), LYN_))
e3 = w.s([e1, e2], 'eleqtrd', '( %s -> Q e. ( T TM2lay %s ) )' % (A0, LYN_))
x = w.s([], 'fvex', '%s e. _V' % LYN_); x2 = w.s([x], 'a1i', '( %s -> %s e. _V )' % (A0, LYN_))
j = w.s([base['t'], x2], 'jca', '( %s -> ( T e. V /\\ %s e. _V ) )' % (A0, LYN_))
i = w.inst('tm2layelim2'); e4 = w.s([j, i], 'syl', '( %s -> ( Q e. ( T TM2lay %s ) -> %s ) )' % (A0, LYN_, WFFX))
e5 = w.s([e3, e4], 'mpd', '( %s -> %s )' % (A0, WFFX))
e6i = w.inst('eldifn'); e6 = w.s([base['qd'], e6i], 'syl', '( %s -> -. Q e. %s )' % (A0, LYN_))
pm = w.s([], 'pm2.53', '( %s -> ( -. Q e. %s -> %s ) )' % (WFFX, LYN_, REST.text()))
e7 = w.s([e5, pm], 'syl', '( %s -> ( -. Q e. %s -> %s ) )' % (A0, LYN_, REST.text()))
e8 = w.s([e6, e7], 'mpd', '( %s -> %s )' % (A0, REST.text()))
h = handle(REST, 0)
w.qed([e8, h], 'mpd', '( %s -> %s )' % (A0, GOAL))
run(w)

# ---- tm2sacllem: induction
w = W('tm2sacllem', 'Closure of TM2sa on each depth layer (induction on the depth).')
PH = lambda v: '( T e. V -> %s )' % IHN(v)
subs = []
for nm, v in (('e', '(/)'), ('y', 'y'), ('u', 'suc y'), ('n', 'N')):
    l = w.s([], 'id', '( w = %s -> w = %s )' % (v, v), name=nm + '0')
    c, _ = w.wcongr(PH('w'), {'w': v}, 'w = %s' % v, {'w': l})
    subs.append(c)
b1 = w.s([], 'tm2lay0', '%s = (/)' % LYn('(/)'))
b2 = w.s([], 'ral0', 'A. q e. (/) A. p e. %s ( q %s p ) e. %s' % (PRT, SAT, CFG))
b3 = w.s([], 'raleq', '( %s = (/) -> ( %s <-> A. q e. (/) A. p e. %s ( q %s p ) e. %s ) )' % (LYn('(/)'), IHN('(/)'), PRT, SAT, CFG))
b4 = w.s([b1, b3], 'ax-mp', '( %s <-> A. q e. (/) A. p e. %s ( q %s p ) e. %s )' % (IHN('(/)'), PRT, SAT, CFG))
b5 = w.s([b2, b4], 'mpbir', IHN('(/)')); b6 = w.s([b5], 'a1i', PH('(/)'))
A1 = '( ( y e. _om /\\ T e. V ) /\\ %s )' % IHN('y')
A2 = '( ( %s /\\ a e. %s ) /\\ b e. %s )' % (A1, LYn('suc y'), PRT)
t2 = w.s([], 'ad2antrr', '( %s -> ( y e. _om /\\ T e. V ) )' % A2)
w.lines[-1] = w.lines[-1]  # placeholder
# derive projections
y2 = w.s([], 'simplll', '( %s -> y e. _om )' % A2); tv2 = w.s([], 'simpllr', '( %s -> T e. V )' % A2)
w.lines.remove([l for l in w.lines if l.startswith(t2 + ':')][0])
ih2 = w.s([], 'simplr', '( %s -> %s )' % (A2, IHN('y'))); a2 = w.s([], 'simpr', '( %s -> b e. %s )' % (A2, PRT))
# wait: structure ( ( A1 /\ a e. Ly suc y ) /\ b e. PR ): simplr gives a e. Ly suc y; A1 pieces need deeper
w.lines = [l for l in w.lines if not l.startswith(ih2 + ':') and not l.startswith(y2 + ':') and not l.startswith(tv2 + ':')]
aa = w.s([], 'simplr', '( %s -> a e. %s )' % (A2, LYn('suc y')))
a1s = w.s([], 'simpll', '( %s -> %s )' % (A2, A1))
ih2 = w.s([a1s], 'simprd', '( %s -> %s )' % (A2, IHN('y')))
yt = w.s([a1s], 'simpld', '( %s -> ( y e. _om /\\ T e. V ) )' % A2)
y2 = w.s([yt], 'simpld', '( %s -> y e. _om )' % A2); tv2 = w.s([yt], 'simprd', '( %s -> T e. V )' % A2)
# case a e. Ly y
A3 = '( %s /\\ a e. %s )' % (A2, LYn('y'))
ih3 = w.s([ih2], 'adantr', '( %s -> %s )' % (A3, IHN('y'))); a3 = w.s([], 'simpr', '( %s -> a e. %s )' % (A3, LYn('y'))); b3s = w.s([a2], 'adantr', '( %s -> b e. %s )' % (A3, PRT))
c1 = ih_inst(w, A3, ih3, a3, b3s, 'a', 'b')
# case -. a e. Ly y
A4 = '( %s /\\ -. a e. %s )' % (A2, LYn('y'))
DOMy = '( %s \\ %s )' % (LYn('suc y'), LYn('y'))
aa4 = w.s([aa], 'adantr', '( %s -> a e. %s )' % (A4, LYn('suc y'))); na4 = w.s([], 'simpr', '( %s -> -. a e. %s )' % (A4, LYn('y')))
ed = w.s([], 'eldif', '( a e. %s <-> ( a e. %s /\\ -. a e. %s ) )' % (DOMy, LYn('suc y'), LYn('y')))
ad = w.s([aa4, na4, ed], 'sylanbrc', '( %s -> a e. %s )' % (A4, DOMy))
tv4 = w.s([tv2], 'adantr', '( %s -> T e. V )' % A4); y4 = w.s([y2], 'adantr', '( %s -> y e. _om )' % A4)
ih4 = w.s([ih2], 'adantr', '( %s -> %s )' % (A4, IHN('y'))); b4s = w.s([a2], 'adantr', '( %s -> b e. %s )' % (A4, PRT))
ty = w.s([tv4, y4], 'jca', '( %s -> ( T e. V /\\ y e. _om ) )' % A4)
bb = w.s([ty, ih4, b4s], '3jca', '( %s -> ( ( T e. V /\\ y e. _om ) /\\ %s /\\ b e. %s ) )' % (A4, IHN('y'), PRT))
ci = w.inst('tm2saclx'); c2 = w.s([bb, ad, ci], 'syl2anc', '( %s -> ( a %s b ) e. %s )' % (A4, SAT, CFG))
c = w.s([c1, c2], 'pm2.61dan', '( %s -> ( a %s b ) e. %s )' % (A2, SAT, CFG))
c = w.s([c], 'anasss', '( ( %s /\\ ( a e. %s /\\ b e. %s ) ) -> ( a %s b ) e. %s )' % (A1, LYn('suc y'), PRT, SAT, CFG))
r = w.s([c], 'ralrimivva', '( %s -> A. a e. %s A. b e. %s ( a %s b ) e. %s )' % (A1, LYn('suc y'), PRT, SAT, CFG))
la = w.s([], 'id', '( a = q -> a = q )'); ca, _ = w.wcongr('( a %s b ) e. %s' % (SAT, CFG), {'a': 'q'}, 'a = q', {'a': la})
lb = w.s([], 'id', '( b = p -> b = p )'); cb, _ = w.wcongr('( q %s b ) e. %s' % (SAT, CFG), {'b': 'p'}, 'b = p', {'b': lb})
cv = w.s([ca, cb], 'cbvral2vw', '( A. a e. %s A. b e. %s ( a %s b ) e. %s <-> %s )' % (LYn('suc y'), PRT, SAT, CFG, IHN('suc y')))
r2 = w.s([r, cv], 'sylib', '( %s -> %s )' % (A1, IHN('suc y')))
r3 = w.s([r2], 'exp31', '( y e. _om -> ( T e. V -> ( %s -> %s ) ) )' % (IHN('y'), IHN('suc y')))
r4 = w.s([r3], 'a2d', '( y e. _om -> ( %s -> %s ) )' % (PH('y'), PH('suc y')))
w.qed(subs + [b6, r4], 'finds', '( N e. _om -> %s )' % PH('N'))
run(w)

# ---- tm2sacl
w = W('tm2sacl', 'Closure of TM2sa: the result of a statement at a (state, stacks) pair is a configuration.')
A = '( T e. V /\\ Q e. %s /\\ P e. %s )' % (ST, PRT)
t = w.s([], 'simp1', '( %s -> T e. V )' % A); q = w.s([], 'simp2', '( %s -> Q e. %s )' % (A, ST)); p = w.s([], 'simp3', '( %s -> P e. %s )' % (A, PRT))
e = w.inst('tm2stmtel'); e2 = w.s([t, e], 'syl', '( %s -> ( Q e. %s <-> E. n e. _om Q e. %s ) )' % (A, ST, LYn('n')))
e3 = w.s([q, e2], 'mpbid', '( %s -> E. n e. _om Q e. %s )' % (A, LYn('n')))
A2 = '( %s /\\ ( n e. _om /\\ Q e. %s ) )' % (A, LYn('n'))
t2 = w.s([t], 'adantr', '( %s -> T e. V )' % A2); p2 = w.s([p], 'adantr', '( %s -> P e. %s )' % (A2, PRT))
n2 = w.s([], 'simprl', '( %s -> n e. _om )' % A2); q2 = w.s([], 'simprr', '( %s -> Q e. %s )' % (A2, LYn('n')))
i = w.inst('tm2sacllem'); i2 = w.s([n2, i], 'syl', '( %s -> ( T e. V -> %s ) )' % (A2, IHN('n')))
ih = w.s([t2, i2], 'mpd', '( %s -> %s )' % (A2, IHN('n')))
f = ih_inst(w, A2, ih, q2, p2, 'Q', 'P')
w.qed([e3, f], 'rexlimddv', '( %s -> ( Q %s P ) e. %s )' % (A, SAT, CFG))
run(w)

# ---- tm2saf
w = W('tm2saf', 'TM2sa is a function from statements and (state, stacks) pairs to configurations.')
s1 = w.s([], 'tm2safn2', '( T e. V -> %s Fn ( %s X. %s ) )' % (SAT, ST, PRT))
A2 = '( ( T e. V /\\ a e. %s ) /\\ b e. %s )' % (ST, PRT)
t2 = w.s([], 'simpll', '( %s -> T e. V )' % A2); a2 = w.s([], 'simplr', '( %s -> a e. %s )' % (A2, ST)); b2 = w.s([], 'simpr', '( %s -> b e. %s )' % (A2, PRT))
i = w.inst('tm2sacl'); c = w.s([t2, a2, b2, i], 'syl3anc', '( %s -> ( a %s b ) e. %s )' % (A2, SAT, CFG))
c = w.s([c], 'anasss', '( ( T e. V /\\ ( a e. %s /\\ b e. %s ) ) -> ( a %s b ) e. %s )' % (ST, PRT, SAT, CFG))
r = w.s([c], 'ralrimivva', '( T e. V -> A. a e. %s A. b e. %s ( a %s b ) e. %s )' % (ST, PRT, SAT, CFG))
e = w.s([], 'ffnov', '( %s : ( %s X. %s ) --> %s <-> ( %s Fn ( %s X. %s ) /\\ A. a e. %s A. b e. %s ( a %s b ) e. %s ) )' % (SAT, ST, PRT, CFG, SAT, ST, PRT, ST, PRT, SAT, CFG))
w.qed([s1, r, e], 'sylanbrc', '( T e. V -> %s : ( %s X. %s ) --> %s )' % (SAT, ST, PRT, CFG))
run(w)
