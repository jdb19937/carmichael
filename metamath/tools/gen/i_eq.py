import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()
T='T'; PRT=PR(T); ST=STMT(T); STK='( TM2Stk ` T )'; SAT=SA(T)
Gt, Lt, St, Kt = G(T), L(T), S(T), K(T)
MAPG = '( %s ^m %s )' % (Lt, St); MAPS = '( %s ^m %s )' % (St, St); MAPB = '( 2o ^m %s )' % St
MAPP = lambda k: '( ( %s ` %s ) ^m %s )' % (Gt, k, St)
MAPK = lambda k: '( %s ^m ( %s X. ( ( %s ` %s ) |_| 1o ) ) )' % (St, St, Gt, k)
PAD = '<. A , D >.'
SD = '( A e. %s /\\ D e. %s )' % (St, STK)

def rhs_of(Q0):
    w = W('scratch', '')
    _, res = evaluate(w, 'ph', CLAUSE(T, 'H', Q0, 'P'), {'F': 'x', 'Q': 'x', 'R': 'x', 'K': 'x'})
    return res

def eq_lemma(label, desc, cl_lemma, Q0, hyps, hypsel, stmt_builder):
    w = W(label, desc)
    A = '( T e. V /\\ %s )' % SD if hyps is None else '( T e. V /\\ %s /\\ %s )' % (hyps, SD)
    st = {}
    if hyps is None:
        st['t'] = w.s([], 'simpl', '( %s -> T e. V )' % A); sd = w.s([], 'simpr', '( %s -> %s )' % (A, SD))
    else:
        st['t'] = w.s([], 'simp1', '( %s -> T e. V )' % A); sd = w.s([], 'simp3', '( %s -> %s )' % (A, SD))
        st['hyps'] = w.s([], 'simp2', '( %s -> %s )' % (A, hyps))
        for mem, sel in hypsel.items():
            st[mem] = w.s([st['hyps']], sel, '( %s -> %s )' % (A, mem)) if sel != 'id' else st['hyps']
    st['a'] = w.s([sd], 'simpld', '( %s -> A e. %s )' % (A, St)); st['d'] = w.s([sd], 'simprd', '( %s -> D e. %s )' % (A, STK))
    pi = w.inst('opelxpi'); st['p'] = w.s([st['a'], st['d'], pi], 'syl2anc', '( %s -> %s e. %s )' % (A, PAD, PRT))
    q0 = stmt_builder(w, A, st)
    fi = w.inst('tm2safix'); f = w.s([st['t'], q0, st['p'], fi], 'syl3anc', '( %s -> ( %s %s %s ) = ( %s ( T TM2cl %s ) %s ) )' % (A, Q0, SAT, PAD, Q0, SAT, PAD))
    hH = w.s([], 'fvex', '%s e. _V' % SAT); hH = w.s([hH], 'a1i', '( %s -> %s e. _V )' % (A, SAT))
    j1 = w.s([st['t'], hH], 'jca', '( %s -> ( T e. V /\\ %s e. _V ) )' % (A, SAT))
    j3 = w.s([q0, st['p']], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A, Q0, ST, PAD, PRT))
    RHS = sub(rhs_of(Q0), {'H': SAT, 'P': PAD})
    ci = w.inst(cl_lemma)
    if hyps is None:
        c = w.s([j1, j3, ci], 'syl2anc', '( %s -> ( %s ( T TM2cl %s ) %s ) = %s )' % (A, Q0, SAT, PAD, RHS))
    else:
        c = w.s([j1, st['hyps'], j3, ci], 'syl3anc', '( %s -> ( %s ( T TM2cl %s ) %s ) = %s )' % (A, Q0, SAT, PAD, RHS))
    setmap = {'A': w.s([st['a']], 'elexd', '( %s -> A e. _V )' % A), 'D': w.s([st['d']], 'elexd', '( %s -> D e. _V )' % A)}
    ev, res = evaluate(w, A, RHS, setmap)
    if ev is None:
        w.qed([f, c], 'eqtrd', '( %s -> ( %s %s %s ) = %s )' % (A, Q0, SAT, PAD, RHS))
    else:
        e1 = w.s([f, c], 'eqtrd', '( %s -> ( %s %s %s ) = %s )' % (A, Q0, SAT, PAD, RHS))
        w.qed([e1, ev], 'eqtrd', '( %s -> ( %s %s %s ) = %s )' % (A, Q0, SAT, PAD, res))
    ok = run(w); print('   ', res); return ok

eq_lemma('tm2sahalt', 'Equation of stepAux for halt: ` stepAux halt v S = <. none , v , S >. `.', 'tm2clhalt', '<. 6 , (/) >.', None, {},
         lambda w, A, st: (lambda i: w.s([st['t'], i], 'syl', '( %s -> <. 6 , (/) >. e. %s )' % (A, ST)))(w.inst('tm2halt')))
eq_lemma('tm2sagoto', 'Equation of stepAux for goto: ` stepAux (goto f) v S = <. some (f v) , v , S >. `.', 'tm2clgoto', '<. 5 , F >.', 'F e. %s' % MAPG, {'F e. %s' % MAPG: 'id'},
         lambda w, A, st: (lambda i: w.s([st['t'], st['F e. %s' % MAPG], i], 'syl2anc', '( %s -> <. 5 , F >. e. %s )' % (A, ST)))(w.inst('tm2goto')))
eq_lemma('tm2sabr', 'Equation of stepAux for branch: ` stepAux (branch f q1 q2) v S = cond (f v) (stepAux q1 v S) (stepAux q2 v S) `.', 'tm2clbr', '<. 4 , <. F , <. R , Q >. >. >.',
         '( F e. %s /\\ R e. %s /\\ Q e. %s )' % (MAPB, ST, ST), {'F e. %s' % MAPB: 'simp1d', 'R e. %s' % ST: 'simp2d', 'Q e. %s' % ST: 'simp3d'},
         lambda w, A, st: (lambda i, j: w.s([st['t'], st['F e. %s' % MAPB], j, i], 'syl3anc', '( %s -> <. 4 , <. F , <. R , Q >. >. >. e. %s )' % (A, ST)))(w.inst('tm2br'), w.s([st['R e. %s' % ST], st['Q e. %s' % ST]], 'jca', '( %s -> ( R e. %s /\\ Q e. %s ) )' % (A, ST, ST))))
eq_lemma('tm2saload', 'Equation of stepAux for load: ` stepAux (load a q) v S = stepAux q (a v) S `.', 'tm2clload', '<. 3 , <. F , Q >. >.',
         '( F e. %s /\\ Q e. %s )' % (MAPS, ST), {'F e. %s' % MAPS: 'simpld', 'Q e. %s' % ST: 'simprd'},
         lambda w, A, st: (lambda i: w.s([st['t'], st['F e. %s' % MAPS], st['Q e. %s' % ST], i], 'syl3anc', '( %s -> <. 3 , <. F , Q >. >. e. %s )' % (A, ST)))(w.inst('tm2load')))
def kfq(lemma, mapf, Q0):
    def b(w, A, st):
        j = w.s([st['K e. %s' % Kt], st['F e. %s' % mapf]], 'jca', '( %s -> ( K e. %s /\\ F e. %s ) )' % (A, Kt, mapf))
        i = w.inst(lemma)
        return w.s([st['t'], j, st['Q e. %s' % ST], i], 'syl3anc', '( %s -> %s e. %s )' % (A, Q0, ST))
    return b
KH = lambda mapf: '( K e. %s /\\ F e. %s /\\ Q e. %s )' % (Kt, mapf, ST)
KS = lambda mapf: {'K e. %s' % Kt: 'simp1d', 'F e. %s' % mapf: 'simp2d', 'Q e. %s' % ST: 'simp3d'}
eq_lemma('tm2sapush', 'Equation of stepAux for push: ` stepAux (push k f q) v S = stepAux q v (update S k (f v :: S k)) `.', 'tm2clpush', '<. 0 , <. K , <. F , Q >. >. >.',
         KH(MAPP('K')), KS(MAPP('K')), kfq('tm2push', MAPP('K'), '<. 0 , <. K , <. F , Q >. >. >.'))
eq_lemma('tm2sapeek', 'Equation of stepAux for peek: ` stepAux (peek k f q) v S = stepAux q (f v (S k).head?) S `.', 'tm2clpeek', '<. 1 , <. K , <. F , Q >. >. >.',
         KH(MAPK('K')), KS(MAPK('K')), kfq('tm2peek', MAPK('K'), '<. 1 , <. K , <. F , Q >. >. >.'))
eq_lemma('tm2sapop', 'Equation of stepAux for pop: ` stepAux (pop k f q) v S = stepAux q (f v (S k).head?) (update S k (S k).tail) `.', 'tm2clpop', '<. 2 , <. K , <. F , Q >. >. >.',
         KH(MAPK('K')), KS(MAPK('K')), kfq('tm2pop', MAPK('K'), '<. 2 , <. K , <. F , Q >. >. >.'))
