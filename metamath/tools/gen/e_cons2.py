import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
T='T'; PRT=PR(T); ST=STMT(T); Ly=LY(T)
def LYn(n): return LYN(T, n)
Gt, Lt, St, Kt = G(T), L(T), S(T), K(T)
MAPG = '( %s ^m %s )' % (Lt, St); MAPS = '( %s ^m %s )' % (St, St); MAPB = '( 2o ^m %s )' % St
MAPP = lambda k: '( ( %s ` %s ) ^m %s )' % (Gt, k, St)
MAPK = lambda k: '( %s ^m ( %s X. ( ( %s ` %s ) |_| 1o ) ) )' % (St, St, Gt, k)

def stmt_from_layer(w, ante, elem, mem, tv, nom, N):
    """mem: ( ante -> elem e. ( T TM2lay ( Ly ` N ) ) ), tv: ( ante -> T e. V ), nom: ( ante -> N e. _om )"""
    i1 = w.inst('tm2laysuc'); s1 = w.s([nom, i1], 'syl', '( %s -> %s = ( T TM2lay %s ) )' % (ante, LYn('suc ' + N), LYn(N)))
    s2 = w.s([mem, s1], 'eleqtrrd', '( %s -> %s e. %s )' % (ante, elem, LYn('suc ' + N)))
    i3 = w.inst('peano2'); s3 = w.s([nom, i3], 'syl', '( %s -> suc %s e. _om )' % (ante, N))
    i4 = w.inst('tm2layssstmt'); s4 = w.s([tv, s3, i4], 'syl2anc', '( %s -> %s C_ %s )' % (ante, LYn('suc ' + N), ST))
    return w.s([s4, s2], 'sseldd', '( %s -> %s e. %s )' % (ante, elem, ST))

def lyv(w, ante, N):
    e = w.s([], 'fvex', '%s e. _V' % LYn(N)); return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ante, LYn(N)))

# tm2halt
w = W('tm2halt', 'halt is a statement.')
A = 'T e. V'
t = w.s([], 'id', '( T e. V -> T e. V )')
x = lyv(w, A, '(/)')
b = w.s([t, x], 'jca', '( %s -> ( T e. V /\\ %s e. _V ) )' % (A, LYn('(/)')))
i = w.inst('tm2layhalt'); m = w.s([b, i], 'syl', '( %s -> <. 6 , (/) >. e. ( T TM2lay %s ) )' % (A, LYn('(/)')))
n0 = w.s([], 'peano1', '(/) e. _om'); n = w.s([n0], 'a1i', '( %s -> (/) e. _om )' % A)
fin = stmt_from_layer(w, A, '<. 6 , (/) >.', m, t, n, '(/)'); w.lines[-1] = 'qed' + w.lines[-1][len(fin):]
run(w)

# tm2goto
w = W('tm2goto', 'goto f is a statement for f : L --> S ... (f a function from states to labels).')
A = '( T e. V /\\ F e. %s )' % MAPG
t = w.s([], 'simpl', '( %s -> T e. V )' % A); f = w.s([], 'simpr', '( %s -> F e. %s )' % (A, MAPG))
x = lyv(w, A, '(/)'); b = w.s([t, x], 'jca', '( %s -> ( T e. V /\\ %s e. _V ) )' % (A, LYn('(/)')))
i = w.inst('tm2laygoto'); m = w.s([b, f, i], 'syl2anc', '( %s -> <. 5 , F >. e. ( T TM2lay %s ) )' % (A, LYn('(/)')))
n0 = w.s([], 'peano1', '(/) e. _om'); n = w.s([n0], 'a1i', '( %s -> (/) e. _om )' % A)
fin = stmt_from_layer(w, A, '<. 5 , F >.', m, t, n, '(/)'); w.lines[-1] = 'qed' + w.lines[-1][len(fin):]
run(w)

def one_sub(label, desc, elem, hyp, layerlemma, hypform):
    r"""statements with one sub-statement Q: ( ( T e. V /\ hyp /\ Q e. STMT ) -> elem e. STMT )
    hypform: function(ante) -> step proving ( ante -> HYPS-of-layerlemma ) where layer lemma ante is ( ( T e. V /\ X e. W ) /\ HYPS )"""
    w = W(label, desc)
    A = '( T e. V /\\ %s /\\ Q e. %s )' % (hyp, ST)
    t = w.s([], 'simp1', '( %s -> T e. V )' % A); q = w.s([], 'simp3', '( %s -> Q e. %s )' % (A, ST))
    e = w.inst('tm2stmtel'); e2 = w.s([t, e], 'syl', '( %s -> ( Q e. %s <-> E. n e. _om Q e. %s ) )' % (A, ST, LYn('n')))
    e3 = w.s([q, e2], 'mpbid', '( %s -> E. n e. _om Q e. %s )' % (A, LYn('n')))
    A2 = '( %s /\\ ( n e. _om /\\ Q e. %s ) )' % (A, LYn('n'))
    t2 = w.s([t], 'adantr', '( %s -> T e. V )' % A2); n2 = w.s([], 'simprl', '( %s -> n e. _om )' % A2); q2 = w.s([], 'simprr', '( %s -> Q e. %s )' % (A2, LYn('n')))
    x = lyv(w, A2, 'n'); b = w.s([t2, x], 'jca', '( %s -> ( T e. V /\\ %s e. _V ) )' % (A2, LYn('n')))
    h = hypform(w, A2, q2)
    i = w.inst(layerlemma); m = w.s([b, h, i], 'syl2anc', '( %s -> %s e. ( T TM2lay %s ) )' % (A2, elem, LYn('n')))
    fin = stmt_from_layer(w, A2, elem, m, t2, n2, 'n')
    w.qed([e3, fin], 'rexlimddv', '( %s -> %s e. %s )' % (A, elem, ST))
    return run(w)

def hf_load(w, A2, q2):
    f = w.s([], 'simpl2', '( %s -> F e. %s )' % (A2, MAPS))
    return w.s([f, q2], 'jca', '( %s -> ( F e. %s /\\ Q e. %s ) )' % (A2, MAPS, LYn('n')))
one_sub('tm2load', 'load f q is a statement when q is.', '<. 3 , <. F , Q >. >.', 'F e. %s' % MAPS, 'tm2layload', hf_load)

def hf_kfq(mapf):
    def hf(w, A2, q2):
        k = w.s([], 'simpl2', '( %s -> ( K e. %s /\\ F e. %s ) )' % (A2, Kt, mapf))
        k1 = w.s([k], 'simpld', '( %s -> K e. %s )' % (A2, Kt)); k2 = w.s([k], 'simprd', '( %s -> F e. %s )' % (A2, mapf))
        return w.s([k1, k2, q2], '3jca', '( %s -> ( K e. %s /\\ F e. %s /\\ Q e. %s ) )' % (A2, Kt, mapf, LYn('n')))
    return hf
one_sub('tm2push', 'push k f q is a statement when q is.', '<. 0 , <. K , <. F , Q >. >. >.', '( K e. %s /\\ F e. %s )' % (Kt, MAPP('K')), 'tm2laypush', hf_kfq(MAPP('K')))
one_sub('tm2peek', 'peek k f q is a statement when q is.', '<. 1 , <. K , <. F , Q >. >. >.', '( K e. %s /\\ F e. %s )' % (Kt, MAPK('K')), 'tm2laypeek', hf_kfq(MAPK('K')))
one_sub('tm2pop', 'pop k f q is a statement when q is.', '<. 2 , <. K , <. F , Q >. >. >.', '( K e. %s /\\ F e. %s )' % (Kt, MAPK('K')), 'tm2laypop', hf_kfq(MAPK('K')))

# tm2stmtel2
w = W('tm2stmtel2', 'Two statements lie in a common depth layer.')
A = '( T e. V /\\ P e. %s /\\ Q e. %s )' % (ST, ST)
t = w.s([], 'simp1', '( %s -> T e. V )' % A); p = w.s([], 'simp2', '( %s -> P e. %s )' % (A, ST)); q = w.s([], 'simp3', '( %s -> Q e. %s )' % (A, ST))
e = w.inst('tm2stmtel'); e2 = w.s([t, e], 'syl', '( %s -> ( P e. %s <-> E. n e. _om P e. %s ) )' % (A, ST, LYn('n')))
lm = w.s([], 'id', '( n = m -> n = m )'); cm, _ = w.wcongr('P e. %s' % LYn('n'), {'n': 'm'}, 'n = m', {'n': lm})
cm2 = w.s([cm], 'cbvrexvw', '( E. n e. _om P e. %s <-> E. m e. _om P e. %s )' % (LYn('n'), LYn('m')))
e3 = w.s([e2, cm2], 'bitrdi', '( %s -> ( P e. %s <-> E. m e. _om P e. %s ) )' % (A, ST, LYn('m')))
e4 = w.s([p, e3], 'mpbid', '( %s -> E. m e. _om P e. %s )' % (A, LYn('m')))
f = w.inst('tm2stmtel'); f2 = w.s([t, f], 'syl', '( %s -> ( Q e. %s <-> E. n e. _om Q e. %s ) )' % (A, ST, LYn('n')))
ll = w.s([], 'id', '( n = l -> n = l )'); cl, _ = w.wcongr('Q e. %s' % LYn('n'), {'n': 'l'}, 'n = l', {'n': ll})
cl2 = w.s([cl], 'cbvrexvw', '( E. n e. _om Q e. %s <-> E. l e. _om Q e. %s )' % (LYn('n'), LYn('l')))
f3 = w.s([f2, cl2], 'bitrdi', '( %s -> ( Q e. %s <-> E. l e. _om Q e. %s ) )' % (A, ST, LYn('l')))
f4 = w.s([q, f3], 'mpbid', '( %s -> E. l e. _om Q e. %s )' % (A, LYn('l')))
A2 = '( %s /\\ ( m e. _om /\\ P e. %s ) )' % (A, LYn('m'))
A3 = '( %s /\\ ( l e. _om /\\ Q e. %s ) )' % (A2, LYn('l'))
t3 = w.s([t], 'ad2antrr', '( %s -> T e. V )' % A3)
m3 = w.s([], 'simplrl', '( %s -> m e. _om )' % A3); pm = w.s([], 'simplrr', '( %s -> P e. %s )' % (A3, LYn('m')))
l3 = w.s([], 'simprl', '( %s -> l e. _om )' % A3); ql = w.s([], 'simprr', '( %s -> Q e. %s )' % (A3, LYn('l')))
o = w.s([], 'ordom', 'Ord _om'); o2 = w.s([o], 'a1i', '( %s -> Ord _om )' % A3)
u = w.inst('ordunel'); u2 = w.s([o2, m3, l3, u], 'syl3anc', '( %s -> ( m u. l ) e. _om )' % A3)
s1 = w.s([], 'ssun1', 'm C_ ( m u. l )'); s2 = w.s([], 'ssun2', 'l C_ ( m u. l )')
i1 = w.inst('tm2layss'); j1 = w.s([t3, m3, u2, i1], 'syl3anc', '( %s -> ( m C_ ( m u. l ) -> %s C_ %s ) )' % (A3, LYn('m'), LYn('( m u. l )')))
j1b = w.s([s1, j1], 'mpi', '( %s -> %s C_ %s )' % (A3, LYn('m'), LYn('( m u. l )')))
i2 = w.inst('tm2layss'); j2 = w.s([t3, l3, u2, i2], 'syl3anc', '( %s -> ( l C_ ( m u. l ) -> %s C_ %s ) )' % (A3, LYn('l'), LYn('( m u. l )')))
j2b = w.s([s2, j2], 'mpi', '( %s -> %s C_ %s )' % (A3, LYn('l'), LYn('( m u. l )')))
pk = w.s([j1b, pm], 'sseldd', '( %s -> P e. %s )' % (A3, LYn('( m u. l )'))); qk = w.s([j2b, ql], 'sseldd', '( %s -> Q e. %s )' % (A3, LYn('( m u. l )')))
both = w.s([pk, qk], 'jca', '( %s -> ( P e. %s /\\ Q e. %s ) )' % (A3, LYn('( m u. l )'), LYn('( m u. l )')))
ln = w.s([], 'id', '( n = ( m u. l ) -> n = ( m u. l ) )')
cn, _ = w.wcongr('( P e. %s /\\ Q e. %s )' % (LYn('n'), LYn('n')), {'n': '( m u. l )'}, 'n = ( m u. l )', {'n': ln})
EX = 'E. n e. _om ( P e. %s /\\ Q e. %s )' % (LYn('n'), LYn('n'))
r = w.s([cn], 'rspcev', '( ( ( m u. l ) e. _om /\\ ( P e. %s /\\ Q e. %s ) ) -> %s )' % (LYn('( m u. l )'), LYn('( m u. l )'), EX))
r2 = w.s([u2, both, r], 'syl2anc', '( %s -> %s )' % (A3, EX))
r3 = w.s([f4], 'adantr', '( %s -> E. l e. _om Q e. %s )' % (A2, LYn('l')))
r4 = w.s([r3, r2], 'rexlimddv', '( %s -> %s )' % (A2, EX))
w.qed([e4, r4], 'rexlimddv', '( %s -> %s )' % (A, EX))
run(w)

# tm2br
w = W('tm2br', 'branch f p q is a statement when p and q are.')
A = '( T e. V /\\ F e. %s /\\ ( P e. %s /\\ Q e. %s ) )' % (MAPB, ST, ST)
t = w.s([], 'simp1', '( %s -> T e. V )' % A); f = w.s([], 'simp2', '( %s -> F e. %s )' % (A, MAPB))
p = w.s([], 'simp3l', '( %s -> P e. %s )' % (A, ST)); q = w.s([], 'simp3r', '( %s -> Q e. %s )' % (A, ST))
i = w.inst('tm2stmtel2'); e = w.s([t, p, q, i], 'syl3anc', '( %s -> E. n e. _om ( P e. %s /\\ Q e. %s ) )' % (A, LYn('n'), LYn('n')))
A2 = '( %s /\\ ( n e. _om /\\ ( P e. %s /\\ Q e. %s ) ) )' % (A, LYn('n'), LYn('n'))
t2 = w.s([t], 'adantr', '( %s -> T e. V )' % A2); f2 = w.s([f], 'adantr', '( %s -> F e. %s )' % (A2, MAPB))
n2 = w.s([], 'simprl', '( %s -> n e. _om )' % A2); p2 = w.s([], 'simprrl', '( %s -> P e. %s )' % (A2, LYn('n'))); q2 = w.s([], 'simprrr', '( %s -> Q e. %s )' % (A2, LYn('n')))
x = lyv(w, A2, 'n'); b = w.s([t2, x], 'jca', '( %s -> ( T e. V /\\ %s e. _V ) )' % (A2, LYn('n')))
h = w.s([f2, p2, q2], '3jca', '( %s -> ( F e. %s /\\ P e. %s /\\ Q e. %s ) )' % (A2, MAPB, LYn('n'), LYn('n')))
elem = '<. 4 , <. F , <. P , Q >. >. >.'
i2 = w.inst('tm2laybr'); m = w.s([b, h, i2], 'syl2anc', '( %s -> %s e. ( T TM2lay %s ) )' % (A2, elem, LYn('n')))
fin = stmt_from_layer(w, A2, elem, m, t2, n2, 'n')
w.qed([e, fin], 'rexlimddv', '( %s -> %s e. %s )' % (A, elem, ST))
run(w)
