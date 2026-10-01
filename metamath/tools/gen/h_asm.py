import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
T='T'; PRT=PR(T); ST=STMT(T); Ly=LY(T); STK='( TM2Stk ` T )'; SAT=SA(T)
def LYn(n): return LYN(T, n)
def FN_(n): return FN(T, n)
Gt, Lt, St, Kt = G(T), L(T), S(T), K(T)
MAPG = '( %s ^m %s )' % (Lt, St); MAPS = '( %s ^m %s )' % (St, St); MAPB = '( 2o ^m %s )' % St
MAPP = lambda k: '( ( %s ` %s ) ^m %s )' % (Gt, k, St)
MAPK = lambda k: '( %s ^m ( %s X. ( ( %s ` %s ) |_| 1o ) ) )' % (St, St, Gt, k)
WFF = open(os.path.join(ROOT, 'scratch', 'tm2layelim.wff')).read().strip()
REN = {'q': 'g', 'p': 'h'}

# ---- tm2layelim2: renamed bound variables
w = W('tm2layelim2', 'Inversion of the constructor layer with renamed bound variables (technical).')
def conv(node):
    Kd = node.kind
    if Kd == 'or':
        s1, w1 = conv(node.kids[0]); s2, w2 = conv(node.kids[1])
        if s1 is None and s2 is None: return None, node.text()
        if s1 is None: s1 = w.s([], 'biid', '( %s <-> %s )' % (w1, w1))
        if s2 is None: s2 = w.s([], 'biid', '( %s <-> %s )' % (w2, w2))
        return w.s([s1, s2], 'orbi12i', '( ( %s \\/ %s ) <-> ( %s \\/ %s ) )' % (node.kids[0].text(), node.kids[1].text(), w1, w2)), '( %s \\/ %s )' % (w1, w2)
    if Kd == 'rex':
        v = node.bound[0]; A_, body = node.kids
        cur_v = v; cur_body = body.text(); step = None
        if v in REN:
            nv = REN[v]
            l = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, nv, v, nv))
            c, nb = w.wcongr(body.text(), {v: nv}, '%s = %s' % (v, nv), {v: l})
            step = w.s([c], 'cbvrexvw', '( E. %s e. %s %s <-> E. %s e. %s %s )' % (v, A_.text(), body.text(), nv, A_.text(), nb))
            cur_v = nv; cur_body = nb
        s2, w2 = conv(parse_wff(cur_body))
        if s2 is not None:
            r = w.s([s2], 'rexbii', '( E. %s e. %s %s <-> E. %s e. %s %s )' % (cur_v, A_.text(), cur_body, cur_v, A_.text(), w2))
            step = r if step is None else w.s([step, r], 'bitri', '( E. %s e. %s %s <-> E. %s e. %s %s )' % (v, A_.text(), body.text(), cur_v, A_.text(), w2))
            cur_body = w2
        return step, 'E. %s e. %s %s' % (cur_v, A_.text(), cur_body)
    return None, node.text()
cs, WFF2 = conv(parse_wff(WFF))
B = '( T e. V /\\ X e. W )'
e = w.s([], 'tm2layelim', '( %s -> ( Q e. ( T TM2lay X ) -> %s ) )' % (B, WFF))
w.qed([e, cs], 'imbitrdi', '( %s -> ( Q e. ( T TM2lay X ) -> %s ) )' % (B, WFF2))
run(w)
open(os.path.join(ROOT, 'scratch', 'tm2layelim2.wff'), 'w').write(WFF2)

# ---- tm2clcong
w = W('tm2clcong', 'The clauses applied to the depth-N function and to TM2sa agree on statements first appearing at depth N + 1.')
LYN_ = LYn('N'); DOM = '( %s \\ %s )' % (LYn('suc N'), LYN_)
A0 = '( ( T e. V /\\ N e. _om ) /\\ ( Q e. %s /\\ P e. %s ) )' % (DOM, PRT)
GOAL = '( Q ( T TM2cl %s ) P ) = ( Q ( T TM2cl %s ) P )' % (FN_('N'), SAT)
base = {'t': w.s([], 'simpll', '( %s -> T e. V )' % A0), 'n': w.s([], 'simplr', '( %s -> N e. _om )' % A0),
        'qd': w.s([], 'simprl', '( %s -> Q e. %s )' % (A0, DOM)), 'p': w.s([], 'simprr', '( %s -> P e. %s )' % (A0, PRT))}
levels = [A0]; ctx = []   # ctx[i] = (var, dom) for level i+1
cache = {}
def lift(name, target_level):
    """step for base item or ctx conjunct at a given level"""
    key = (name, levels[target_level])
    if key in cache: return cache[key]
    if isinstance(name, int):  # ctx index
        v, d = ctx[name]; lvl = name + 1
        key = (v, d, levels[target_level])
        if key in cache: return cache[key]
        if target_level == lvl:
            st = w.s([], 'simpr', '( %s -> %s e. %s )' % (levels[lvl], v, d))
        else:
            st = w.s([lift(name, target_level - 1)], 'adantr', '( %s -> %s e. %s )' % (levels[target_level], v, d))
    else:
        if target_level == 0: st = base[name]
        else:
            txt = {'t': 'T e. V', 'n': 'N e. _om', 'p': 'P e. %s' % PRT, 'qd': 'Q e. %s' % DOM}[name]
            st = w.s([lift(name, target_level - 1)], 'adantr', '( %s -> %s )' % (levels[target_level], txt))
    cache[key] = st; return st
def find(v):
    for i, (x, d) in enumerate(ctx):
        if x == v: return i, d
    raise KeyError(v)
def leaf(node, level):
    ante = levels[level]
    tup = node.kids[1].text(); tag = parse(tup).kids[0].text()
    tn = w.s([lift('t', level), lift('n', level)], 'jca', '( %s -> ( T e. V /\\ N e. _om ) )' % ante)
    b0 = w.s([tn, lift('p', level)], 'jca', '( %s -> ( ( T e. V /\\ N e. _om ) /\\ P e. %s ) )' % (ante, PRT))
    B0 = '( ( T e. V /\\ N e. _om ) /\\ P e. %s )' % PRT
    GT = sub(GOAL, {'Q': tup})
    if tag == '6':
        c1 = w.s([], 'tm2clcong6', '( %s -> %s )' % (B0, GT)); c4 = w.s([b0, c1], 'syl', '( %s -> %s )' % (ante, GT))
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
        c1 = w.s([], 'tm2clcong' + tag, '( %s -> ( %s -> %s ) )' % (B0, hyps, GT))
        c4a = w.s([b0, c1], 'syl', '( %s -> ( %s -> %s ) )' % (ante, hyps, GT))
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
    if node.kind == 'eq':
        return leaf(node, level)
    raise NotImplementedError(node.kind)
WFFX = sub(WFF2, {'X': LYN_})
tree = parse_wff(WFFX)
assert tree.kind == 'or' and tree.kids[0].text() == 'Q e. %s' % LYN_
REST = tree.kids[1]
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

# ---- tm2stmtmin2
w = W('tm2stmtmin2', 'Every statement first appears at some depth.')
A = '( T e. V /\\ Q e. %s )' % ST
EX = 'E. n e. _om ( Q e. %s /\\ -. Q e. %s )' % (LYn('suc n'), LYn('n'))
t = w.s([], 'simpl', '( %s -> T e. V )' % A); q = w.s([], 'simpr', '( %s -> Q e. %s )' % (A, ST))
e = w.inst('tm2stmtel'); e2 = w.s([t, e], 'syl', '( %s -> ( Q e. %s <-> E. n e. _om Q e. %s ) )' % (A, ST, LYn('n')))
lm = w.s([], 'id', '( n = m -> n = m )'); cm, _ = w.wcongr('Q e. %s' % LYn('n'), {'n': 'm'}, 'n = m', {'n': lm})
cm2 = w.s([cm], 'cbvrexvw', '( E. n e. _om Q e. %s <-> E. m e. _om Q e. %s )' % (LYn('n'), LYn('m')))
e3 = w.s([e2, cm2], 'bitrdi', '( %s -> ( Q e. %s <-> E. m e. _om Q e. %s ) )' % (A, ST, LYn('m')))
e4 = w.s([q, e3], 'mpbid', '( %s -> E. m e. _om Q e. %s )' % (A, LYn('m')))
A2 = '( %s /\\ ( m e. _om /\\ Q e. %s ) )' % (A, LYn('m'))
m1 = w.s([], 'simprl', '( %s -> m e. _om )' % A2); m2 = w.s([], 'simprr', '( %s -> Q e. %s )' % (A2, LYn('m')))
i = w.inst('tm2stmtmin'); m3 = w.s([m1, i], 'syl', '( %s -> ( Q e. %s -> %s ) )' % (A2, LYn('m'), EX))
m4 = w.s([m2, m3], 'mpd', '( %s -> %s )' % (A2, EX))
w.qed([e4, m4], 'rexlimddv', '( %s -> %s )' % (A, EX))
run(w)

# ---- tm2safix
w = W('tm2safix', 'TM2sa satisfies the clauses: the fixed-point equation of Lean\'s stepAux.')
A = '( T e. V /\\ Q e. %s /\\ P e. %s )' % (ST, PRT)
t = w.s([], 'simp1', '( %s -> T e. V )' % A); q = w.s([], 'simp2', '( %s -> Q e. %s )' % (A, ST)); p = w.s([], 'simp3', '( %s -> P e. %s )' % (A, PRT))
EX = 'E. n e. _om ( Q e. %s /\\ -. Q e. %s )' % (LYn('suc n'), LYn('n'))
i = w.inst('tm2stmtmin2'); e = w.s([t, q, i], 'syl2anc', '( %s -> %s )' % (A, EX))
A2 = '( %s /\\ ( n e. _om /\\ ( Q e. %s /\\ -. Q e. %s ) ) )' % (A, LYn('suc n'), LYn('n'))
DOMn = '( %s \\ %s )' % (LYn('suc n'), LYn('n'))
t2 = w.s([t], 'adantr', '( %s -> T e. V )' % A2); p2 = w.s([p], 'adantr', '( %s -> P e. %s )' % (A2, PRT))
n2 = w.s([], 'simprl', '( %s -> n e. _om )' % A2); q1 = w.s([], 'simprrl', '( %s -> Q e. %s )' % (A2, LYn('suc n'))); q2 = w.s([], 'simprrr', '( %s -> -. Q e. %s )' % (A2, LYn('n')))
ed = w.s([], 'eldif', '( Q e. %s <-> ( Q e. %s /\\ -. Q e. %s ) )' % (DOMn, LYn('suc n'), LYn('n')))
qd = w.s([q1, q2, ed], 'sylanbrc', '( %s -> Q e. %s )' % (A2, DOMn))
tn = w.s([t2, n2], 'jca', '( %s -> ( T e. V /\\ n e. _om ) )' % A2); qp = w.s([qd, p2], 'jca', '( %s -> ( Q e. %s /\\ P e. %s ) )' % (A2, DOMn, PRT))
v = w.inst('tm2savalsuc'); v2 = w.s([tn, qp, v], 'syl2anc', '( %s -> ( Q %s P ) = ( Q ( T TM2cl %s ) P ) )' % (A2, SAT, FN_('n')))
c = w.inst('tm2clcong'); c2 = w.s([tn, qp, c], 'syl2anc', '( %s -> ( Q ( T TM2cl %s ) P ) = ( Q ( T TM2cl %s ) P ) )' % (A2, FN_('n'), SAT))
f = w.s([v2, c2], 'eqtrd', '( %s -> ( Q %s P ) = ( Q ( T TM2cl %s ) P ) )' % (A2, SAT, SAT))
w.qed([e, f], 'rexlimddv', '( %s -> ( Q %s P ) = ( Q ( T TM2cl %s ) P ) )' % (A, SAT, SAT))
run(w)
