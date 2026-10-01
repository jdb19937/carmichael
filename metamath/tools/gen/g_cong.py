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
DJ = lambda k: '( ( %s ` %s ) |_| 1o )' % (Gt, k)
WD = lambda k: 'Word ( %s ` %s )' % (Gt, k)
B0 = '( ( T e. V /\\ N e. _om ) /\\ P e. %s )' % PRT
FNN = FN_('N'); LYN_ = LYn('N')

def rhs_of(Q0):
    """RHS of tm2clX for H generic, computed by evaluation in a scratch worksheet"""
    w = W('scratch', '')
    _, res = evaluate(w, 'ph', CLAUSE(T, 'H', Q0, 'P'), {'F': 'x', 'Q': 'x', 'R': 'x', 'K': 'x'})
    return res

def case_lemma(label, desc, cl_lemma, Q0, hyps, hypsel, subs, stmt_builder, arg_closure):
    """hyps: wff of the case hypotheses (same shape as tm2clX middle group) or None
    hypsel: {membership wff: selector from ( A -> hyp-group )}
    subs: list of sub-statement variables (in Ly`N)
    stmt_builder(w, A, st): step ( A -> Q0 e. STMT ) from projection dict st
    arg_closure(w, A, st, rhsH): returns (kind, data): ('none',) | ('one', argtext, step ARG e. PR) | ('br', cond)"""
    w = W(label, desc)
    A = B0 if hyps is None else '( %s /\\ %s )' % (B0, hyps)
    st = {}
    if hyps is None:
        st['t'] = w.s([], 'simpll', '( %s -> T e. V )' % A); st['n'] = w.s([], 'simplr', '( %s -> N e. _om )' % A); st['p'] = w.s([], 'simpr', '( %s -> P e. %s )' % (A, PRT))
    else:
        st['t'] = w.s([], 'simplll', '( %s -> T e. V )' % A); st['n'] = w.s([], 'simpllr', '( %s -> N e. _om )' % A); st['p'] = w.s([], 'simplr', '( %s -> P e. %s )' % (A, PRT))
        st['hyps'] = w.s([], 'simpr', '( %s -> %s )' % (A, hyps))
        for mem, sel in hypsel.items():
            st[mem] = w.s([st['hyps']], sel, '( %s -> %s )' % (A, mem)) if sel != 'id' else st['hyps']
    tn = w.s([st['t'], st['n']], 'jca', '( %s -> ( T e. V /\\ N e. _om ) )' % A)
    ssi = w.inst('tm2layssstmt'); ss = w.s([st['t'], st['n'], ssi], 'syl2anc', '( %s -> %s C_ %s )' % (A, LYN_, ST))
    for v in subs:
        st[v + 'st'] = w.s([ss, st['%s e. %s' % (v, LYN_)]], 'sseldd', '( %s -> %s e. %s )' % (A, v, ST))
    q0 = stmt_builder(w, A, st)
    j3 = w.s([q0, st['p']], 'jca', '( %s -> ( %s e. %s /\\ P e. %s ) )' % (A, Q0, ST, PRT))
    RHS = rhs_of(Q0)
    vals = {}
    for H in (FNN, SAT):
        hH = w.s([], 'fvex', '%s e. _V' % H); hH = w.s([hH], 'a1i', '( %s -> %s e. _V )' % (A, H))
        j1 = w.s([st['t'], hH], 'jca', '( %s -> ( T e. V /\\ %s e. _V ) )' % (A, H))
        i = w.inst(cl_lemma)
        rhsH = sub(RHS, {'H': H})
        if hyps is None:
            vals[H] = w.s([j1, j3, i], 'syl2anc', '( %s -> ( %s ( T TM2cl %s ) P ) = %s )' % (A, Q0, H, rhsH))
        else:
            vals[H] = w.s([j1, st['hyps'], j3, i], 'syl3anc', '( %s -> ( %s ( T TM2cl %s ) P ) = %s )' % (A, Q0, H, rhsH))
    kind = arg_closure(w, A, st)
    LHS = '( %s ( T TM2cl %s ) P )' % (Q0, FNN); RHSS = '( %s ( T TM2cl %s ) P )' % (Q0, SAT)
    if kind[0] == 'none':
        fin = w.s([vals[FNN], vals[SAT]], 'eqtr4d', '( %s -> %s = %s )' % (A, LHS, RHSS))
    elif kind[0] == 'one':
        _, argtext, argcl, subv = kind
        assert sub(RHS, {'H': 'H'}) == '( %s H %s )' % (subv, argtext), (RHS, argtext)
        j = w.s([st['%s e. %s' % (subv, LYN_)], argcl], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, subv, LYN_, argtext, PRT))
        mi = w.inst('tm2safnval'); mid = w.s([tn, j, mi], 'syl2anc', '( %s -> ( %s %s %s ) = ( %s %s %s ) )' % (A, subv, FNN, argtext, subv, SAT, argtext))
        e1 = w.s([vals[FNN], mid], 'eqtrd', '( %s -> %s = ( %s %s %s ) )' % (A, LHS, subv, SAT, argtext))
        fin = w.s([e1, vals[SAT]], 'eqtr4d', '( %s -> %s = %s )' % (A, LHS, RHSS))
    else:  # branch
        cond = kind[1]
        mids = []
        for v in ('R', 'Q'):
            j = w.s([st['%s e. %s' % (v, LYN_)], st['p']], 'jca', '( %s -> ( %s e. %s /\\ P e. %s ) )' % (A, v, LYN_, PRT))
            mi = w.inst('tm2safnval'); mids.append(w.s([tn, j, mi], 'syl2anc', '( %s -> ( %s %s P ) = ( %s %s P ) )' % (A, v, FNN, v, SAT)))
        mid = w.s(mids, 'ifeq12d', '( %s -> if ( %s , ( R %s P ) , ( Q %s P ) ) = if ( %s , ( R %s P ) , ( Q %s P ) ) )' % (A, cond, FNN, FNN, cond, SAT, SAT))
        e1 = w.s([vals[FNN], mid], 'eqtrd', '( %s -> %s = if ( %s , ( R %s P ) , ( Q %s P ) ) )' % (A, LHS, cond, SAT, SAT))
        fin = w.s([e1, vals[SAT]], 'eqtr4d', '( %s -> %s = %s )' % (A, LHS, RHSS))
    if hyps is None:
        w.lines[-1] = 'qed' + w.lines[-1][len(fin):]
    else:
        w.qed([fin], 'ex', '( %s -> ( %s -> %s = %s ) )' % (B0, hyps, LHS, RHSS))
    return run(w)

# common closure pieces
def v_in_S(w, A, st):
    i = w.inst('xp1st'); return w.s([st['p'], i], 'syl', '( %s -> ( 1st ` P ) e. %s )' % (A, St))
def s_in_STK(w, A, st):
    i = w.inst('xp2nd'); return w.s([st['p'], i], 'syl', '( %s -> ( 2nd ` P ) e. %s )' % (A, STK))
def fmap(w, A, fstep, dom, cod):
    i = w.inst('elmapi'); return w.s([fstep, i], 'syl', '( %s -> F : %s --> %s )' % (A, dom, cod))
def fval(w, A, fstep, argstep, arg, dom, cod):
    i = w.inst('ffvelcdm'); return w.s([fstep, argstep, i], 'syl2anc', '( %s -> ( F ` %s ) e. %s )' % (A, arg, cod))
def pair(w, A, s1, e1, C1, s2, e2, C2):
    i = w.inst('opelxpi'); return w.s([s1, s2, i], 'syl2anc', '( %s -> <. %s , %s >. e. ( %s X. %s ) )' % (A, e1, e2, C1, C2))

# halt
case_lemma('tm2clcong6', 'The clauses of halt agree for the depth-N function and TM2sa.', 'tm2clhalt', '<. 6 , (/) >.', None, {}, [],
           lambda w, A, st: (lambda i: w.s([st['t'], i], 'syl', '( %s -> <. 6 , (/) >. e. %s )' % (A, ST)))(w.inst('tm2halt')),
           lambda w, A, st: ('none',))
# goto
case_lemma('tm2clcong5', 'The clauses of goto agree for the depth-N function and TM2sa.', 'tm2clgoto', '<. 5 , F >.', 'F e. %s' % MAPG, {'F e. %s' % MAPG: 'id'}, [],
           lambda w, A, st: (lambda i: w.s([st['t'], st['F e. %s' % MAPG], i], 'syl2anc', '( %s -> <. 5 , F >. e. %s )' % (A, ST)))(w.inst('tm2goto')),
           lambda w, A, st: ('none',))
# branch
case_lemma('tm2clcong4', 'The clauses of branch agree for the depth-N function and TM2sa.', 'tm2clbr', '<. 4 , <. F , <. R , Q >. >. >.',
           '( F e. %s /\\ R e. %s /\\ Q e. %s )' % (MAPB, LYN_, LYN_), {'F e. %s' % MAPB: 'simp1d', 'R e. %s' % LYN_: 'simp2d', 'Q e. %s' % LYN_: 'simp3d'}, ['R', 'Q'],
           lambda w, A, st: (lambda i, j: w.s([st['t'], st['F e. %s' % MAPB], j, i], 'syl3anc', '( %s -> <. 4 , <. F , <. R , Q >. >. >. e. %s )' % (A, ST)))(w.inst('tm2br'), w.s([st['Rst'], st['Qst']], 'jca', '( %s -> ( R e. %s /\\ Q e. %s ) )' % (A, ST, ST))),
           lambda w, A, st: ('br', '( F ` ( 1st ` P ) ) = 1o'))
# load
def load_cl(w, A, st):
    v = v_in_S(w, A, st); s = s_in_STK(w, A, st)
    f = fmap(w, A, st['F e. %s' % MAPS], St, St); fv = fval(w, A, f, v, '( 1st ` P )', St, St)
    arg = '<. ( F ` ( 1st ` P ) ) , ( 2nd ` P ) >.'
    p = pair(w, A, fv, '( F ` ( 1st ` P ) )', St, s, '( 2nd ` P )', STK)
    return ('one', arg, p, 'Q')
case_lemma('tm2clcong3', 'The clauses of load agree for the depth-N function and TM2sa.', 'tm2clload', '<. 3 , <. F , Q >. >.',
           '( F e. %s /\\ Q e. %s )' % (MAPS, LYN_), {'F e. %s' % MAPS: 'simpld', 'Q e. %s' % LYN_: 'simprd'}, ['Q'],
           lambda w, A, st: (lambda i: w.s([st['t'], st['F e. %s' % MAPS], st['Qst'], i], 'syl3anc', '( %s -> <. 3 , <. F , Q >. >. e. %s )' % (A, ST)))(w.inst('tm2load')),
           load_cl)
# push / peek / pop
KHYP = lambda mapf: '( K e. %s /\\ F e. %s /\\ Q e. %s )' % (Kt, mapf, LYN_)
def kfq_sel(mapf): return {'K e. %s' % Kt: 'simp1d', 'F e. %s' % mapf: 'simp2d', 'Q e. %s' % LYN_: 'simp3d'}
def kfq_stmt(lemma, mapf, Q0):
    def b(w, A, st):
        j = w.s([st['K e. %s' % Kt], st['F e. %s' % mapf]], 'jca', '( %s -> ( K e. %s /\\ F e. %s ) )' % (A, Kt, mapf))
        i = w.inst(lemma)
        return w.s([st['t'], j, st['Qst'], i], 'syl3anc', '( %s -> %s e. %s )' % (A, Q0, ST))
    return b
UPDW = lambda word: '( ( ( 2nd ` P ) |` ( %s \\ { K } ) ) u. { <. K , %s >. } )' % (Kt, word)
HEAD = 'if ( ( ( 2nd ` P ) ` K ) = (/) , ( inr ` (/) ) , ( inl ` ( ( ( 2nd ` P ) ` K ) ` 0 ) ) )'
def stk_k(w, A, st, s):
    i = w.inst('tm2stkfv'); return w.s([st['t'], s, st['K e. %s' % Kt], i], 'syl3anc', '( %s -> ( ( 2nd ` P ) ` K ) e. %s )' % (A, WD('K')))
def upd(w, A, st, s, wordstep, word):
    j = w.s([st['K e. %s' % Kt], wordstep], 'jca', '( %s -> ( K e. %s /\\ %s e. %s ) )' % (A, Kt, word, WD('K')))
    i = w.inst('tm2stkupd'); return w.s([st['t'], s, j, i], 'syl3anc', '( %s -> %s e. %s )' % (A, UPDW(word), STK))
def push_cl(w, A, st):
    v = v_in_S(w, A, st); s = s_in_STK(w, A, st)
    f = fmap(w, A, st['F e. %s' % MAPP('K')], St, '( %s ` K )' % Gt); fv = fval(w, A, f, v, '( 1st ` P )', St, '( %s ` K )' % Gt)
    i1 = w.inst('s1cl'); w1 = w.s([fv, i1], 'syl', '( %s -> <" ( F ` ( 1st ` P ) ) "> e. %s )' % (A, WD('K')))
    w2 = stk_k(w, A, st, s)
    word = '( <" ( F ` ( 1st ` P ) ) "> ++ ( ( 2nd ` P ) ` K ) )'
    i3 = w.inst('ccatcl'); w3 = w.s([w1, w2, i3], 'syl2anc', '( %s -> %s e. %s )' % (A, word, WD('K')))
    u = upd(w, A, st, s, w3, word)
    arg = '<. ( 1st ` P ) , %s >.' % UPDW(word)
    p = pair(w, A, v, '( 1st ` P )', St, u, UPDW(word), STK)
    return ('one', arg, p, 'Q')
case_lemma('tm2clcong0', 'The clauses of push agree for the depth-N function and TM2sa.', 'tm2clpush', '<. 0 , <. K , <. F , Q >. >. >.',
           KHYP(MAPP('K')), kfq_sel(MAPP('K')), ['Q'], kfq_stmt('tm2push', MAPP('K'), '<. 0 , <. K , <. F , Q >. >. >.'), push_cl)
def head_state(w, A, st, s):
    v = v_in_S(w, A, st)
    i = w.inst('tm2stkhead'); hd = w.s([st['t'], s, st['K e. %s' % Kt], i], 'syl3anc', '( %s -> %s e. %s )' % (A, HEAD, DJ('K')))
    pr = pair(w, A, v, '( 1st ` P )', St, hd, HEAD, DJ('K'))
    f = fmap(w, A, st['F e. %s' % MAPK('K')], '( %s X. %s )' % (St, DJ('K')), St)
    return fval(w, A, f, pr, '<. ( 1st ` P ) , %s >.' % HEAD, '( %s X. %s )' % (St, DJ('K')), St)
def peek_cl(w, A, st):
    s = s_in_STK(w, A, st); fv = head_state(w, A, st, s)
    arg = '<. ( F ` <. ( 1st ` P ) , %s >. ) , ( 2nd ` P ) >.' % HEAD
    p = pair(w, A, fv, '( F ` <. ( 1st ` P ) , %s >. )' % HEAD, St, s, '( 2nd ` P )', STK)
    return ('one', arg, p, 'Q')
case_lemma('tm2clcong1', 'The clauses of peek agree for the depth-N function and TM2sa.', 'tm2clpeek', '<. 1 , <. K , <. F , Q >. >. >.',
           KHYP(MAPK('K')), kfq_sel(MAPK('K')), ['Q'], kfq_stmt('tm2peek', MAPK('K'), '<. 1 , <. K , <. F , Q >. >. >.'), peek_cl)
def pop_cl(w, A, st):
    s = s_in_STK(w, A, st); fv = head_state(w, A, st, s)
    w2 = stk_k(w, A, st, s)
    word = '( ( ( 2nd ` P ) ` K ) substr <. 1 , ( # ` ( ( 2nd ` P ) ` K ) ) >. )'
    i3 = w.inst('swrdcl'); w3 = w.s([w2, i3], 'syl', '( %s -> %s e. %s )' % (A, word, WD('K')))
    u = upd(w, A, st, s, w3, word)
    arg = '<. ( F ` <. ( 1st ` P ) , %s >. ) , %s >.' % (HEAD, UPDW(word))
    p = pair(w, A, fv, '( F ` <. ( 1st ` P ) , %s >. )' % HEAD, St, u, UPDW(word), STK)
    return ('one', arg, p, 'Q')
case_lemma('tm2clcong2', 'The clauses of pop agree for the depth-N function and TM2sa.', 'tm2clpop', '<. 2 , <. K , <. F , Q >. >. >.',
           KHYP(MAPK('K')), kfq_sel(MAPK('K')), ['Q'], kfq_stmt('tm2pop', MAPK('K'), '<. 2 , <. K , <. F , Q >. >. >.'), pop_cl)
