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
DJ = lambda k: '( ( %s ` %s ) |_| 1o )' % (Gt, k)
WD = lambda k: 'Word ( %s ` %s )' % (Gt, k)
LYN_ = LYn('N')
IH = 'A. q e. %s A. p e. %s ( q %s p ) e. %s' % (LYN_, PRT, SAT, CFG)
B0 = '( ( T e. V /\\ N e. _om ) /\\ %s /\\ P e. %s )' % (IH, PRT)
CFGX = '( ( %s |_| 1o ) X. %s )' % (Lt, PRT)
V_ = '( 1st ` P )'; D_ = '( 2nd ` P )'; PVD = '<. %s , %s >.' % (V_, D_)

def ih_inst(w, A, ih, rst, yst, R, Y):
    """( A -> ( R SA Y ) e. CFG ) from IH, ( A -> R e. Ly N ), ( A -> Y e. PR )"""
    l1 = w.s([], 'id', '( q = %s -> q = %s )' % (R, R))
    c1, _ = w.wcongr('A. p e. %s ( q %s p ) e. %s' % (PRT, SAT, CFG), {'q': R}, 'q = %s' % R, {'q': l1})
    i1 = w.s([c1, ih, rst], 'rspcdva', '( %s -> A. p e. %s ( %s %s p ) e. %s )' % (A, PRT, R, SAT, CFG))
    l2 = w.s([], 'id', '( p = %s -> p = %s )' % (Y, Y))
    c2, _ = w.wcongr('( %s %s p ) e. %s' % (R, SAT, CFG), {'p': Y}, 'p = %s' % Y, {'p': l2})
    return w.s([c2, i1, yst], 'rspcdva', '( %s -> ( %s %s %s ) e. %s )' % (A, R, SAT, Y, CFG))

def v_in_S(w, A, st):
    i = w.inst('xp1st'); return w.s([st['p'], i], 'syl', '( %s -> %s e. %s )' % (A, V_, St))
def s_in_STK(w, A, st):
    i = w.inst('xp2nd'); return w.s([st['p'], i], 'syl', '( %s -> %s e. %s )' % (A, D_, STK))
def fmap(w, A, fstep, dom, cod):
    i = w.inst('elmapi'); return w.s([fstep, i], 'syl', '( %s -> F : %s --> %s )' % (A, dom, cod))
def fval(w, A, fstep, argstep, arg, cod):
    i = w.inst('ffvelcdm'); return w.s([fstep, argstep, i], 'syl2anc', '( %s -> ( F ` %s ) e. %s )' % (A, arg, cod))
def pair(w, A, s1, e1, C1, s2, e2, C2):
    i = w.inst('opelxpi'); return w.s([s1, s2, i], 'syl2anc', '( %s -> <. %s , %s >. e. ( %s X. %s ) )' % (A, e1, e2, C1, C2))
UPDW = lambda word: '( ( %s |` ( %s \\ { K } ) ) u. { <. K , %s >. } )' % (D_, Kt, word)
HEAD = 'if ( ( %s ` K ) = (/) , ( inr ` (/) ) , ( inl ` ( ( %s ` K ) ` 0 ) ) )' % (D_, D_)
def stk_k(w, A, st, s):
    i = w.inst('tm2stkfv'); return w.s([st['t'], s, st['K e. %s' % Kt], i], 'syl3anc', '( %s -> ( %s ` K ) e. %s )' % (A, D_, WD('K')))
def upd(w, A, st, s, wordstep, word):
    j = w.s([st['K e. %s' % Kt], wordstep], 'jca', '( %s -> ( K e. %s /\\ %s e. %s ) )' % (A, Kt, word, WD('K')))
    i = w.inst('tm2stkupd'); return w.s([st['t'], s, j, i], 'syl3anc', '( %s -> %s e. %s )' % (A, UPDW(word), STK))
def head_state(w, A, st, s):
    v = v_in_S(w, A, st)
    i = w.inst('tm2stkhead'); hd = w.s([st['t'], s, st['K e. %s' % Kt], i], 'syl3anc', '( %s -> %s e. %s )' % (A, HEAD, DJ('K')))
    pr = pair(w, A, v, V_, St, hd, HEAD, DJ('K'))
    f = fmap(w, A, st['F e. %s' % MAPK('K')], '( %s X. %s )' % (St, DJ('K')), St)
    return fval(w, A, f, pr, '<. %s , %s >.' % (V_, HEAD), St)

def cl_lemma(label, desc, eq_lemma, Q0, hyps, hypsel, subs, eqhyps_builder, rhs_closure):
    """eqhyps_builder(w, A, st) -> step ( A -> EQHYPS ) matching the equation lemma's middle group (or None for halt)
    rhs_closure(w, A, st, RHS) -> step ( A -> RHS e. CFG )"""
    w = W(label, desc)
    A = B0 if hyps is None else '( %s /\\ %s )' % (B0, hyps)
    st = {}
    if hyps is None:
        st['tn'] = w.s([], 'simp1', '( %s -> ( T e. V /\\ N e. _om ) )' % A); st['ih'] = w.s([], 'simp2', '( %s -> %s )' % (A, IH)); st['p'] = w.s([], 'simp3', '( %s -> P e. %s )' % (A, PRT))
    else:
        st['tn'] = w.s([], 'simpl1', '( %s -> ( T e. V /\\ N e. _om ) )' % A); st['ih'] = w.s([], 'simpl2', '( %s -> %s )' % (A, IH)); st['p'] = w.s([], 'simpl3', '( %s -> P e. %s )' % (A, PRT))
        st['hyps'] = w.s([], 'simpr', '( %s -> %s )' % (A, hyps))
        for mem, sel in hypsel.items():
            st[mem] = w.s([st['hyps']], sel, '( %s -> %s )' % (A, mem)) if sel != 'id' else st['hyps']
    st['t'] = w.s([st['tn']], 'simpld', '( %s -> T e. V )' % A); st['n'] = w.s([st['tn']], 'simprd', '( %s -> N e. _om )' % A)
    ssi = w.inst('tm2layssstmt'); ss = w.s([st['t'], st['n'], ssi], 'syl2anc', '( %s -> %s C_ %s )' % (A, LYN_, ST))
    for v in subs:
        st[v + 'st'] = w.s([ss, st['%s e. %s' % (v, LYN_)]], 'sseldd', '( %s -> %s e. %s )' % (A, v, ST))
    st['v'] = v_in_S(w, A, st); st['d'] = s_in_STK(w, A, st)
    vd = w.s([st['v'], st['d']], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, V_, St, D_, STK))
    pi = w.inst('1st2nd2'); pe = w.s([st['p'], pi], 'syl', '( %s -> P = %s )' % (A, PVD))
    pe2 = w.s([pe], 'oveq2d', '( %s -> ( %s %s P ) = ( %s %s %s ) )' % (A, Q0, SAT, Q0, SAT, PVD))
    # equation lemma
    eqi = w.inst(eq_lemma)
    RHS = None
    # compute RHS text from evaluate as in i_eq, with A := ( 1st ` P ), D := ( 2nd ` P )
    ws = W('scratch', ''); _, res = evaluate(ws, 'ph', CLAUSE(T, SAT, Q0, PVD), {'F': 'x', 'Q': 'x', 'R': 'x', 'K': 'x'})
    RHS = res
    eh = eqhyps_builder(w, A, st)
    if eh is None:
        eq = w.s([st['t'], vd, eqi], 'syl2anc', '( %s -> ( %s %s %s ) = %s )' % (A, Q0, SAT, PVD, RHS))
    else:
        eq = w.s([st['t'], eh, vd, eqi], 'syl3anc', '( %s -> ( %s %s %s ) = %s )' % (A, Q0, SAT, PVD, RHS))
    e2 = w.s([pe2, eq], 'eqtrd', '( %s -> ( %s %s P ) = %s )' % (A, Q0, SAT, RHS))
    cl = rhs_closure(w, A, st, RHS)
    fin = w.s([e2, cl], 'eqeltrd', '( %s -> ( %s %s P ) e. %s )' % (A, Q0, SAT, CFG))
    if hyps is None:
        w.lines[-1] = 'qed' + w.lines[-1][len(fin):]
    else:
        w.qed([fin], 'ex', '( %s -> ( %s -> ( %s %s P ) e. %s ) )' % (B0, hyps, Q0, SAT, CFG))
    return run(w)

def to_cfg(w, A, st, step, elem):
    """from ( A -> elem e. CFGX ) to ( A -> elem e. CFG )"""
    i = w.inst('tm2cfgval'); v = w.s([st['t'], i], 'syl', '( %s -> %s = %s )' % (A, CFG, CFGX))
    return w.s([step, v], 'eleqtrrd', '( %s -> %s e. %s )' % (A, elem, CFG))

# halt
def halt_cl(w, A, st, RHS):
    c1 = w.s([], '0lt1o', '(/) e. 1o'); i = w.inst('djurcl'); c2 = w.s([c1, i], 'ax-mp', '( inr ` (/) ) e. ( %s |_| 1o )' % Lt)
    c3 = w.s([c2], 'a1i', '( %s -> ( inr ` (/) ) e. ( %s |_| 1o ) )' % (A, Lt))
    pr = pair(w, A, st['v'], V_, St, st['d'], D_, STK)
    o = pair(w, A, c3, '( inr ` (/) )', '( %s |_| 1o )' % Lt, pr, PVD, PRT)
    return to_cfg(w, A, st, o, RHS)
cl_lemma('tm2sacl6', 'Closure of stepAux for halt.', 'tm2sahalt', '<. 6 , (/) >.', None, {}, [], lambda w, A, st: None, halt_cl)
# goto
def goto_cl(w, A, st, RHS):
    f = fmap(w, A, st['F e. %s' % MAPG], St, Lt); fv = fval(w, A, f, st['v'], V_, Lt)
    i = w.inst('djulcl'); c = w.s([fv, i], 'syl', '( %s -> ( inl ` ( F ` %s ) ) e. ( %s |_| 1o ) )' % (A, V_, Lt))
    pr = pair(w, A, st['v'], V_, St, st['d'], D_, STK)
    o = pair(w, A, c, '( inl ` ( F ` %s ) )' % V_, '( %s |_| 1o )' % Lt, pr, PVD, PRT)
    return to_cfg(w, A, st, o, RHS)
cl_lemma('tm2sacl5', 'Closure of stepAux for goto.', 'tm2sagoto', '<. 5 , F >.', 'F e. %s' % MAPG, {'F e. %s' % MAPG: 'id'}, [],
         lambda w, A, st: st['F e. %s' % MAPG], goto_cl)
# branch
def br_cl(w, A, st, RHS):
    pr = pair(w, A, st['v'], V_, St, st['d'], D_, STK)
    r = ih_inst(w, A, st['ih'], st['R e. %s' % LYN_], pr, 'R', PVD)
    q = ih_inst(w, A, st['ih'], st['Q e. %s' % LYN_], pr, 'Q', PVD)
    return w.s([r, q], 'ifcld', '( %s -> %s e. %s )' % (A, RHS, CFG))
cl_lemma('tm2sacl4', 'Closure of stepAux for branch.', 'tm2sabr', '<. 4 , <. F , <. R , Q >. >. >.',
         '( F e. %s /\\ R e. %s /\\ Q e. %s )' % (MAPB, LYN_, LYN_), {'F e. %s' % MAPB: 'simp1d', 'R e. %s' % LYN_: 'simp2d', 'Q e. %s' % LYN_: 'simp3d'}, ['R', 'Q'],
         lambda w, A, st: w.s([st['F e. %s' % MAPB], st['Rst'], st['Qst']], '3jca', '( %s -> ( F e. %s /\\ R e. %s /\\ Q e. %s ) )' % (A, MAPB, ST, ST)), br_cl)
# load
def load_cl(w, A, st, RHS):
    f = fmap(w, A, st['F e. %s' % MAPS], St, St); fv = fval(w, A, f, st['v'], V_, St)
    arg = '<. ( F ` %s ) , %s >.' % (V_, D_)
    p = pair(w, A, fv, '( F ` %s )' % V_, St, st['d'], D_, STK)
    return ih_inst(w, A, st['ih'], st['Q e. %s' % LYN_], p, 'Q', arg)
cl_lemma('tm2sacl3', 'Closure of stepAux for load.', 'tm2saload', '<. 3 , <. F , Q >. >.',
         '( F e. %s /\\ Q e. %s )' % (MAPS, LYN_), {'F e. %s' % MAPS: 'simpld', 'Q e. %s' % LYN_: 'simprd'}, ['Q'],
         lambda w, A, st: w.s([st['F e. %s' % MAPS], st['Qst']], 'jca', '( %s -> ( F e. %s /\\ Q e. %s ) )' % (A, MAPS, ST)), load_cl)
# push/peek/pop
KHYP = lambda mapf: '( K e. %s /\\ F e. %s /\\ Q e. %s )' % (Kt, mapf, LYN_)
def kfq_sel(mapf): return {'K e. %s' % Kt: 'simp1d', 'F e. %s' % mapf: 'simp2d', 'Q e. %s' % LYN_: 'simp3d'}
def kfq_eqh(mapf):
    return lambda w, A, st: w.s([st['K e. %s' % Kt], st['F e. %s' % mapf], st['Qst']], '3jca', '( %s -> ( K e. %s /\\ F e. %s /\\ Q e. %s ) )' % (A, Kt, mapf, ST))
def push_cl(w, A, st, RHS):
    f = fmap(w, A, st['F e. %s' % MAPP('K')], St, '( %s ` K )' % Gt); fv = fval(w, A, f, st['v'], V_, '( %s ` K )' % Gt)
    i1 = w.inst('s1cl'); w1 = w.s([fv, i1], 'syl', '( %s -> <" ( F ` %s ) "> e. %s )' % (A, V_, WD('K')))
    w2 = stk_k(w, A, st, st['d'])
    word = '( <" ( F ` %s ) "> ++ ( %s ` K ) )' % (V_, D_)
    i3 = w.inst('ccatcl'); w3 = w.s([w1, w2, i3], 'syl2anc', '( %s -> %s e. %s )' % (A, word, WD('K')))
    u = upd(w, A, st, st['d'], w3, word)
    arg = '<. %s , %s >.' % (V_, UPDW(word))
    p = pair(w, A, st['v'], V_, St, u, UPDW(word), STK)
    return ih_inst(w, A, st['ih'], st['Q e. %s' % LYN_], p, 'Q', arg)
cl_lemma('tm2sacl0', 'Closure of stepAux for push.', 'tm2sapush', '<. 0 , <. K , <. F , Q >. >. >.', KHYP(MAPP('K')), kfq_sel(MAPP('K')), ['Q'], kfq_eqh(MAPP('K')), push_cl)
def peek_cl(w, A, st, RHS):
    fv = head_state(w, A, st, st['d'])
    arg = '<. ( F ` <. %s , %s >. ) , %s >.' % (V_, HEAD, D_)
    p = pair(w, A, fv, '( F ` <. %s , %s >. )' % (V_, HEAD), St, st['d'], D_, STK)
    return ih_inst(w, A, st['ih'], st['Q e. %s' % LYN_], p, 'Q', arg)
cl_lemma('tm2sacl1', 'Closure of stepAux for peek.', 'tm2sapeek', '<. 1 , <. K , <. F , Q >. >. >.', KHYP(MAPK('K')), kfq_sel(MAPK('K')), ['Q'], kfq_eqh(MAPK('K')), peek_cl)
def pop_cl(w, A, st, RHS):
    fv = head_state(w, A, st, st['d'])
    w2 = stk_k(w, A, st, st['d'])
    word = '( ( %s ` K ) substr <. 1 , ( # ` ( %s ` K ) ) >. )' % (D_, D_)
    i3 = w.inst('swrdcl'); w3 = w.s([w2, i3], 'syl', '( %s -> %s e. %s )' % (A, word, WD('K')))
    u = upd(w, A, st, st['d'], w3, word)
    arg = '<. ( F ` <. %s , %s >. ) , %s >.' % (V_, HEAD, UPDW(word))
    p = pair(w, A, fv, '( F ` <. %s , %s >. )' % (V_, HEAD), St, u, UPDW(word), STK)
    return ih_inst(w, A, st['ih'], st['Q e. %s' % LYN_], p, 'Q', arg)
cl_lemma('tm2sacl2', 'Closure of stepAux for pop.', 'tm2sapop', '<. 2 , <. K , <. F , Q >. >. >.', KHYP(MAPK('K')), kfq_sel(MAPK('K')), ['Q'], kfq_eqh(MAPK('K')), pop_cl)
