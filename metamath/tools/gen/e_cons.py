import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
T='T'; PRT=PR(T); ST=STMT(T); Ly=LY(T)
def LYn(n): return LYN(T, n)
Gt, Lt, St, Kt = G(T), L(T), S(T), K(T)

def member(w, node, elem, ante, path):
    """step proving ( ante -> elem e. node ); path consumed in order"""
    K_ = node.kind
    if K_ == 'in:u.':
        d = path.pop(0)
        if d == 'L':
            sub_ = member(w, node.kids[0], elem, ante, path)
            i = w.inst('elun1')
        else:
            sub_ = member(w, node.kids[1], elem, ante, path)
            i = w.inst('elun2')
        return w.s([sub_, i], 'syl', '( %s -> %s e. %s )' % (ante, elem, node.text()))
    if K_ == 'iun':
        v = node.bound[0]; val, valstep = path.pop(0)
        A_, B_ = node.kids
        Bsub = ' '.join(subst_toks(B_.toks, {v: val}))
        sub_ = member(w, parse(Bsub), elem, ante, path)
        l = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, val, v, val))
        c, _ = w.wcongr('%s e. %s' % (elem, B_.text()), {v: val}, '%s = %s' % (v, val), {v: l})
        r = w.s([c], 'rspcev', '( ( %s e. %s /\\ %s e. %s ) -> E. %s e. %s %s e. %s )' % (val, A_.text(), elem, Bsub, v, A_.text(), elem, B_.text()))
        r2 = w.s([valstep, sub_, r], 'syl2anc', '( %s -> E. %s e. %s %s e. %s )' % (ante, v, A_.text(), elem, B_.text()))
        e = w.s([], 'eliun', '( %s e. %s <-> E. %s e. %s %s e. %s )' % (elem, node.text(), v, A_.text(), elem, B_.text()))
        return w.s([r2, e], 'sylibr', '( %s -> %s e. %s )' % (ante, elem, node.text()))
    if K_ == 'sn':
        assert node.kids[0].text() == elem, (node.kids[0].text(), elem)
        o = w.s([], 'opex', '%s e. _V' % elem); i = w.inst('snidg')
        c = w.s([o, i], 'ax-mp', '%s e. { %s }' % (elem, elem))
        return w.s([c], 'a1i', '( %s -> %s e. { %s } )' % (ante, elem, elem))
    if K_ == 'atom':
        return path.pop(0)
    raise NotImplementedError(K_)

def layer_lemma(label, desc, elem, hyps, hypsel, path):
    """hyps: wff or None; hypsel: dict var-membership -> selector producing ( A -> mem )"""
    w = W(label, desc)
    B = '( T e. V /\\ X e. W )'
    A = B if hyps is None else '( %s /\\ %s )' % (B, hyps)
    v = w.inst('tm2layval')
    if hyps is None:
        v2 = w.s([v], 'tm2layval', '( %s -> ( T TM2lay X ) = %s )' % (A, PHI(T, 'X')))
        w.lines.pop(-2)  # drop the unused instance line
        v2 = w.lines[-1].split(':')[0]
        w.lines[-1] = w.lines[-1].replace('%s:%s:tm2layval' % (v2, v), '%s::tm2layval' % v2)
    else:
        v2 = w.s([], 'tm2layval', '( %s -> ( T TM2lay X ) = %s )' % (B, PHI(T, 'X')))
        w.lines.pop(-2)
        v2 = w.s([v2], 'adantr', '( %s -> ( T TM2lay X ) = %s )' % (A, PHI(T, 'X')))
    steps = {}
    for mem, sel in hypsel.items():
        steps[mem] = w.s([], sel, '( %s -> %s )' % (A, mem))
    p = [x if isinstance(x, str) else (x[0], steps[x[1]]) for x in path]
    m = member(w, parse(PHI(T, 'X')), elem, A, p)
    w.qed([m, v2], 'eleqtrrd', '( %s -> %s e. ( T TM2lay X ) )' % (A, elem))
    return run(w)

MAPG = '( %s ^m %s )' % (Lt, St); MAPS = '( %s ^m %s )' % (St, St); MAPB = '( 2o ^m %s )' % St
MAPP = lambda k: '( ( %s ` %s ) ^m %s )' % (Gt, k, St)
MAPK = lambda k: '( %s ^m ( %s X. ( ( %s ` %s ) |_| 1o ) ) )' % (St, St, Gt, k)

layer_lemma('tm2layhalt', 'halt belongs to every constructor layer.', '<. 6 , (/) >.', None, {}, ['R', 'L', 'L', 'L'])
layer_lemma('tm2laygoto', 'goto f belongs to every constructor layer.', '<. 5 , F >.', 'F e. %s' % MAPG, {'F e. %s' % MAPG: 'simpr'}, ['R', 'L', 'L', 'R', ('F', 'F e. %s' % MAPG)])
layer_lemma('tm2layload', 'load f q belongs to the constructor layer over X when q e. X.', '<. 3 , <. F , Q >. >.', '( F e. %s /\\ Q e. X )' % MAPS,
            {'F e. %s' % MAPS: 'simprl', 'Q e. X': 'simprr'}, ['R', 'L', 'R', 'L', ('F', 'F e. %s' % MAPS), ('Q', 'Q e. X')])
layer_lemma('tm2laybr', 'branch f p q belongs to the constructor layer over X when p , q e. X.', '<. 4 , <. F , <. P , Q >. >. >.', '( F e. %s /\\ P e. X /\\ Q e. X )' % MAPB,
            {'F e. %s' % MAPB: 'simpr1', 'P e. X': 'simpr2', 'Q e. X': 'simpr3'}, ['R', 'L', 'R', 'R', ('F', 'F e. %s' % MAPB), ('P', 'P e. X'), ('Q', 'Q e. X')])
layer_lemma('tm2laypush', 'push k f q belongs to the constructor layer over X when q e. X.', '<. 0 , <. K , <. F , Q >. >. >.', '( K e. %s /\\ F e. %s /\\ Q e. X )' % (Kt, MAPP('K')),
            {'K e. %s' % Kt: 'simpr1', 'F e. %s' % MAPP('K'): 'simpr2', 'Q e. X': 'simpr3'}, ['R', 'R', ('K', 'K e. %s' % Kt), 'L', ('F', 'F e. %s' % MAPP('K')), ('Q', 'Q e. X')])
layer_lemma('tm2laypeek', 'peek k f q belongs to the constructor layer over X when q e. X.', '<. 1 , <. K , <. F , Q >. >. >.', '( K e. %s /\\ F e. %s /\\ Q e. X )' % (Kt, MAPK('K')),
            {'K e. %s' % Kt: 'simpr1', 'F e. %s' % MAPK('K'): 'simpr2', 'Q e. X': 'simpr3'}, ['R', 'R', ('K', 'K e. %s' % Kt), 'R', ('F', 'F e. %s' % MAPK('K')), ('Q', 'Q e. X'), 'L'])
layer_lemma('tm2laypop', 'pop k f q belongs to the constructor layer over X when q e. X.', '<. 2 , <. K , <. F , Q >. >. >.', '( K e. %s /\\ F e. %s /\\ Q e. X )' % (Kt, MAPK('K')),
            {'K e. %s' % Kt: 'simpr1', 'F e. %s' % MAPK('K'): 'simpr2', 'Q e. X': 'simpr3'}, ['R', 'R', ('K', 'K e. %s' % Kt), 'R', ('F', 'F e. %s' % MAPK('K')), ('Q', 'Q e. X'), 'R'])
