import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); from tm import *
only = sys.argv[1:]
T='T'; PRT=PR(T); ST=STMT(T)

def clause_lemma(label, desc, Q0, hyps, hypvars):
    """hyps: wff string of the middle group (or None); hypvars: list of (var, membership-wff-selector-step-ref)"""
    w = W(label, desc)
    B = '( T e. V /\\ H e. W )'; C = '( %s e. %s /\\ P e. %s )' % (Q0, ST, PRT)
    if hyps is None:
        A = '( %s /\\ %s )' % (B, C)
        a1 = w.s([], 'simpl', '( %s -> %s )' % (A, B)); a3 = w.s([], 'simpr', '( %s -> %s )' % (A, C))
    else:
        A = '( %s /\\ %s /\\ %s )' % (B, hyps, C)
        a1 = w.s([], 'simp1', '( %s -> %s )' % (A, B)); a3 = w.s([], 'simp3', '( %s -> %s )' % (A, C))
    v = w.inst('tm2clvalq')
    v2 = w.s([a1, a3, v], 'syl2anc', '( %s -> ( %s ( T TM2cl H ) P ) = %s )' % (A, Q0, CLAUSE(T, 'H', Q0, 'P')))
    setmap = {}
    for var, sel, mem in hypvars:
        m = w.s([], sel, '( %s -> %s )' % (A, mem))
        setmap[var] = w.s([m], 'elexd', '( %s -> %s e. _V )' % (A, var))
    ev, res = evaluate(w, A, CLAUSE(T, 'H', Q0, 'P'), setmap)
    w.qed([v2, ev], 'eqtrd', '( %s -> ( %s ( T TM2cl H ) P ) = %s )' % (A, Q0, res))
    if only and label not in only: return
    ok = w.run()
    print('   ', res[:150])

clause_lemma('tm2clhalt', 'The clause of halt: stop with the current state and stacks.', '<. 6 , (/) >.', None, [])
clause_lemma('tm2clgoto', 'The clause of goto f: jump to label ( f ` v ).', '<. 5 , F >.', 'F e. U', [('F', 'simp2', 'F e. U')])
clause_lemma('tm2clbr', 'The clause of branch f q1 q2: continue with q1 or q2 according to ( f ` v ).', '<. 4 , <. F , <. R , Q >. >. >.',
             '( F e. U /\\ R e. Y /\\ Q e. Z )', [('F', 'simp21', 'F e. U'), ('R', 'simp22', 'R e. Y'), ('Q', 'simp23', 'Q e. Z')])
clause_lemma('tm2clload', 'The clause of load f q: continue with q at state ( f ` v ).', '<. 3 , <. F , Q >. >.',
             '( F e. U /\\ Q e. Z )', [('F', 'simp2l', 'F e. U'), ('Q', 'simp2r', 'Q e. Z')])
clause_lemma('tm2clpush', 'The clause of push k f q: continue with q after pushing ( f ` v ) on stack k.', '<. 0 , <. K , <. F , Q >. >. >.',
             '( K e. U /\\ F e. Y /\\ Q e. Z )', [('K', 'simp21', 'K e. U'), ('F', 'simp22', 'F e. Y'), ('Q', 'simp23', 'Q e. Z')])
clause_lemma('tm2clpeek', 'The clause of peek k f q: continue with q at state ( f ` <. v , head? >. ) where head? is the optional top of stack k.', '<. 1 , <. K , <. F , Q >. >. >.',
             '( K e. U /\\ F e. Y /\\ Q e. Z )', [('K', 'simp21', 'K e. U'), ('F', 'simp22', 'F e. Y'), ('Q', 'simp23', 'Q e. Z')])
clause_lemma('tm2clpop', 'The clause of pop k f q: as peek, and remove the top of stack k.', '<. 2 , <. K , <. F , Q >. >. >.',
             '( K e. U /\\ F e. Y /\\ Q e. Z )', [('K', 'simp21', 'K e. U'), ('F', 'simp22', 'F e. Y'), ('Q', 'simp23', 'Q e. Z')])
