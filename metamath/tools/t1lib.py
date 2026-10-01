"""Sortie T1: the fragment calculus of the machine layer, and the symbolic
machine-execution generator.

Expression builders for the Hoare triple `C ( T TM2Hoare M ) <. D , N >.`
and the run relation, on top of tools/tm.py's worksheet builder `W`.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))
from tm import *
from c0lib import runh, addh, hyp, imp, closed, instapply

# ---------------------------------------------------------------- expressions

def OPS(T, M):
    """the optional-step function of the machine <. T , M >."""
    return '( OptStep ` ( %s TM2step %s ) )' % (T, M)


def ITER(T, M, N, X):
    """( ( ( OptStep ` ( T TM2step M ) ) ^r N ) ` X )"""
    return '( ( %s ^r %s ) ` %s )' % (OPS(T, M), N, X)


def HR(C, T, M, D, N):
    """the Hoare triple C ( T TM2Hoare M ) <. D , N >."""
    return '%s ( %s TM2Hoare %s ) <. %s , %s >.' % (C, T, M, D, N)


def CFGCL(T, A, P):
    """the class of configurations at label A whose state-stack part lies in P"""
    return '( { ( inl ` %s ) } X. %s )' % (A, P)


def HALTCL(P):
    """the class of halted configurations whose state-stack part lies in P"""
    return '( { ( inr ` (/) ) } X. %s )' % P


def BODY(T, M, C, D, N, u='u', i='i', w='w'):
    """the body of df-tm2hr at explicit C, D, N"""
    return ('A. %s e. %s E. %s e. ( 0 ... %s ) E. %s e. %s %s = ( inl ` %s )'
            % (u, C, i, N, w, D, ITER(T, M, i, '( inl ` %s )' % u), w))


def PWX(T):
    """the typing factor of df-tm2hr"""
    return '( ~P %s X. ( ~P %s X. NN0 ) )' % (CFG(T), CFG(T))


def OPAB(T, M, c='c', y='y', u='u', i='i', w='w'):
    """the opab of df-tm2hr with the outer binders instantiated to T, M"""
    return ('{ <. %s , %s >. | A. %s e. %s E. %s e. ( 0 ... ( 2nd ` %s ) ) '
            'E. %s e. ( 1st ` %s ) %s = ( inl ` %s ) }'
            % (c, y, u, c, i, y, w, y, ITER(T, M, i, '( inl ` %s )' % u), w))


def HRVAL(T, M):
    return '( %s i^i %s )' % (OPAB(T, M), PWX(T))


# ---------------------------------------------------------------- step helpers

def setex(w, ante, text, ref, hyps=()):
    """( ante -> text e. _V ) from a closed ref"""
    return instapply(w, ante, ref, '%s e. _V' % text, list(hyps))


def cfgex(w, ante, T):
    """( ante -> ( TM2Cfg ` T ) e. _V )"""
    c = w.s([], 'fvex', '%s e. _V' % CFG(T))
    return w.s([c], 'a1i', '( %s -> %s e. _V )' % (ante, CFG(T)))


def TYP(C, D, N, T):
    """the typing conjunct the triple carries"""
    return '( %s C_ %s /\\ %s C_ %s /\\ %s e. NN0 )' % (C, CFG(T), D, CFG(T), N)


PHM = '( T e. V /\\ M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T ) )'


def OPTC(T):
    """the optional-configuration space ( ( TM2Cfg ` T ) |_| 1o )"""
    return '( %s |_| 1o )' % CFG(T)


def tvstep(w, ante, phm):
    """( ante -> ( T e. V /\\ M e. _V ) ) from a step proving ( ante -> PHM )"""
    t = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ante)
    m = w.s([phm, w.inst('tm2hmvv')], 'syl', '( %s -> M e. _V )' % ante)
    return w.s([t, m], 'jca', '( %s -> ( T e. V /\\ M e. _V ) )' % ante)


def hrintro(w, ante, phm, C, D, N, ty, body, qed=False):
    """conclude ( ante -> C ( T TM2Hoare M ) <. D , N >. ) from the typing step
    `ty` and the run step `body`"""
    tv = tvstep(w, ante, phm)
    bi = w.s([tv, ty, w.inst('tm2hrbr2')], 'syl2anc',
             '( %s -> ( %s <-> %s ) )' % (ante, HR(C, 'T', 'M', D, N), BODY('T', 'M', C, D, N)))
    f = '( %s -> %s )' % (ante, HR(C, 'T', 'M', D, N))
    if qed:
        w.qed([bi, body], 'mpbird', f); return None
    return w.s([bi, body], 'mpbird', f)


def hrelim(w, ante, phm, C, D, N, br):
    """from a step `br` proving ( ante -> C ( T TM2Hoare M ) <. D , N >. ),
    return (typing step, run step)"""
    pb = w.s([phm, br], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, PHM, HR(C, 'T', 'M', D, N)))
    tvp = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ante)
    mvp = w.s([phm, w.inst('tm2hmvv')], 'syl', '( %s -> M e. _V )' % ante)
    tv = w.s([tvp, mvp], 'jca', '( %s -> ( T e. V /\\ M e. _V ) )' % ante)
    tvb = w.s([tv, br], 'jca', '( %s -> ( ( T e. V /\\ M e. _V ) /\\ %s ) )' % (ante, HR(C, 'T', 'M', D, N)))
    ty = w.s([tvb, w.inst('tm2hrtyp')], 'syl', '( %s -> %s )' % (ante, TYP(C, D, N, 'T')))
    bi = w.s([tv, ty, w.inst('tm2hrbr2')], 'syl2anc',
             '( %s -> ( %s <-> %s ) )' % (ante, HR(C, 'T', 'M', D, N), BODY('T', 'M', C, D, N)))
    bd = w.s([bi, br], 'mpbid', '( %s -> %s )' % (ante, BODY('T', 'M', C, D, N)))
    return ty, bd


def rename_body(w, ante, src, C, D, N, u2, i2, w2, T='T', M='M'):
    """from a step `src` proving ( ante -> BODY(T,M,C,D,N) ) with the standard
    binders u, i, w, produce a step with the binders renamed to u2, i2, w2."""
    G = OPS(T, M)
    def eqf(uu, ii, ww):
        return '%s = ( inl ` %s )' % (ITER(T, M, ii, '( inl ` %s )' % uu), ww)
    def inner(uu, ii, ww):
        return 'E. %s e. %s %s' % (ww, D, eqf(uu, ii, ww))
    def mid(uu, ii, ww):
        return 'E. %s e. ( 0 ... %s ) %s' % (ii, N, inner(uu, ii, ww))
    def outer(uu, ii, ww):
        return 'A. %s e. %s %s' % (uu, C, mid(uu, ii, ww))
    # w -> w2
    a1 = w.s([], 'fveq2', '( w = %s -> ( inl ` w ) = ( inl ` %s ) )' % (w2, w2))
    a2 = w.s([a1], 'eqeq2d', '( w = %s -> ( %s <-> %s ) )' % (w2, eqf('u', 'i', 'w'), eqf('u', 'i', w2)))
    e1 = w.s([a2], 'cbvrexvw', '( %s <-> %s )' % (inner('u', 'i', 'w'), inner('u', 'i', w2)))
    e2 = w.s([e1], 'rexbii', '( %s <-> %s )' % (mid('u', 'i', 'w'), mid('u', 'i', w2)))
    # i -> i2
    b1 = w.s([], 'oveq2', '( i = %s -> ( %s ^r i ) = ( %s ^r %s ) )' % (i2, G, G, i2))
    b2 = w.s([b1], 'fveq1d', '( i = %s -> %s = %s )'
             % (i2, ITER(T, M, 'i', '( inl ` u )'), ITER(T, M, i2, '( inl ` u )')))
    b3 = w.s([b2], 'eqeq1d', '( i = %s -> ( %s <-> %s ) )' % (i2, eqf('u', 'i', w2), eqf('u', i2, w2)))
    b4 = w.s([b3], 'rexbidv', '( i = %s -> ( %s <-> %s ) )' % (i2, inner('u', 'i', w2), inner('u', i2, w2)))
    e3 = w.s([b4], 'cbvrexvw', '( %s <-> %s )' % (mid('u', 'i', w2), mid('u', i2, w2)))
    e4 = w.s([e2, e3], 'bitri', '( %s <-> %s )' % (mid('u', 'i', 'w'), mid('u', i2, w2)))
    e5 = w.s([e4], 'ralbii', '( %s <-> %s )' % (outer('u', 'i', 'w'), outer('u', i2, w2)))
    if u2 == 'u':
        e7 = e5
    else:
        c1 = w.s([], 'fveq2', '( u = %s -> ( inl ` u ) = ( inl ` %s ) )' % (u2, u2))
        c2 = w.s([c1], 'fveq2d', '( u = %s -> %s = %s )'
                 % (u2, ITER(T, M, i2, '( inl ` u )'), ITER(T, M, i2, '( inl ` %s )' % u2)))
        c3 = w.s([c2], 'eqeq1d', '( u = %s -> ( %s <-> %s ) )' % (u2, eqf('u', i2, w2), eqf(u2, i2, w2)))
        c4 = w.s([c3], 'rexbidv', '( u = %s -> ( %s <-> %s ) )' % (u2, inner('u', i2, w2), inner(u2, i2, w2)))
        c5 = w.s([c4], 'rexbidv', '( u = %s -> ( %s <-> %s ) )' % (u2, mid('u', i2, w2), mid(u2, i2, w2)))
        e6 = w.s([c5], 'cbvralvw', '( %s <-> %s )' % (outer('u', i2, w2), outer(u2, i2, w2)))
        e7 = w.s([e5, e6], 'bitri', '( %s <-> %s )' % (outer('u', 'i', 'w'), outer(u2, i2, w2)))
    o2 = outer(u2, i2, w2)
    e8 = w.s([e7], 'a1i', '( %s -> ( %s <-> %s ) )' % (ante, outer('u', 'i', 'w'), o2))
    return w.s([e8, src], 'mpbid', '( %s -> %s )' % (ante, o2)), o2


# ------------------------------------------------------- statement constructors

def PUSH(K, F, Q):   return '<. 0 , <. %s , <. %s , %s >. >. >.' % (K, F, Q)
def PEEK(K, F, Q):   return '<. 1 , <. %s , <. %s , %s >. >. >.' % (K, F, Q)
def POP(K, F, Q):    return '<. 2 , <. %s , <. %s , %s >. >. >.' % (K, F, Q)
def LOAD(F, Q):      return '<. 3 , <. %s , %s >. >.' % (F, Q)
def BRANCH(F, R, Q): return '<. 4 , <. %s , <. %s , %s >. >. >.' % (F, R, Q)
def GOTO(F):         return '<. 5 , %s >.' % F
HALT = '<. 6 , (/) >.'


def UPD(T, D, Kk, X):
    """Lean's `Function.update S k x` on a stack assignment"""
    return '( ( %s |` ( %s \\ { %s } ) ) u. { <. %s , %s >. } )' % (D, K(T), Kk, Kk, X)


def HEAD(D, K):
    """Lean's `(S k).head?`"""
    return 'if ( ( %s ` %s ) = (/) , ( inr ` (/) ) , ( inl ` ( ( %s ` %s ) ` 0 ) ) )' % (D, K, D, K)


def TAIL(D, K):
    """Lean's `(S k).tail`"""
    return '( ( %s ` %s ) substr <. 1 , ( # ` ( %s ` %s ) ) >. )' % (D, K, D, K)


# --------------------------------------------------- symbolic machine execution

def _balanced(toks):
    """split a token list of a `<. a , b >.` or `( a OP b )` term at depth 1"""
    d = 0; parts = [[]]
    for t in toks:
        if t in ('(', '<.'):
            d += 1
            if d == 1:
                continue
        elif t in (')', '>.'):
            d -= 1
            if d == 0:
                continue
        if d == 1 and t == ',':
            parts.append([]); continue
        parts[-1].append(t)
    return [' '.join(p) for p in parts]


def tag_of(stmt):
    """the constructor tag and the components of an explicit statement tuple"""
    parts = _balanced(stmt.split())
    if len(parts) != 2:
        return None, None
    return parts[0], parts[1]


def split_sa(text, T):
    """(Q, P) if text is ( Q ( TM2sa ` T ) P ), else None"""
    sa = SA(T)
    toks = text.split()
    if not toks or toks[0] != '(' or toks[-1] != ')':
        return None
    d = 0; sat = sa.split()
    for i, t in enumerate(toks):
        if d == 1 and toks[i:i + len(sat)] == sat:
            return ' '.join(toks[1:i]), ' '.join(toks[i + len(sat):-1])
        if t in ('(', '<.'):
            d += 1
        elif t in (')', '>.'):
            d -= 1
    return None


class Exec:
    """Symbolic execution of one machine step.

    `facts` maps a wff text to the name of a step proving
    ` ( ante -> <that wff> ) `; the generator asks for the typing side
    conditions of the seven ` stepAux ` equations
    (` K e. dom G `, ` F e. ... `, ` Q e. ( TM2Stmt ` T ) `, ` A e. S `,
    ` D e. ( TM2Stk ` T ) `, ` T e. V `) and, at a ` branch ` , for the truth
    value of its condition (key ` ( F ` A ) = 1o `, value ` (True|False, step) `
    in `ifrules`).  `rules` is applied by tools/tm.py's `evaluate` to every
    intermediate right-hand side, so that stack updates and function values
    collapse to the forms the fragment's invariant uses.
    """

    def __init__(self, w, ante, T, facts, rules=None, ifrules=None, setmap=None):
        self.w = w; self.ante = ante; self.T = T
        self.facts = dict(facts)
        if rules is None or callable(rules):
            self.rules = rules
        else:
            tbl = dict(rules)
            self.rules = lambda n: tbl.get(n.text())
        self.ifrules = dict(ifrules or {})
        self.setmap = dict(setmap or {})
        self.trace = []

    def need(self, wff):
        if wff not in self.facts:
            raise KeyError('symbolic execution needs a step for: %s' % wff)
        return self.facts[wff]

    def _clause(self, stmt, pair):
        """one application of an equation lemma; returns (step, rhs)"""
        w, T, ante = self.w, self.T, self.ante
        tag, rest = tag_of(stmt)
        A, D = _balanced(pair.split())
        tv = self.need('%s e. V' % T)
        a = self.need('%s e. %s' % (A, S(T)))
        d = self.need('%s e. %s' % (D, STK(T)))
        ad = w.s([a, d], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ante, A, S(T), D, STK(T)))
        lhs = '( %s %s %s )' % (stmt, SA(T), pair)
        if tag == '6':
            rhs = '<. ( inr ` (/) ) , %s >.' % pair
            st = w.s([tv, ad, w.inst('tm2sahalt')], 'syl2anc', '( %s -> %s = %s )' % (ante, lhs, rhs))
            return st, rhs
        if tag == '5':
            F = rest
            f = self.need('%s e. ( %s ^m %s )' % (F, L(T), S(T)))
            rhs = '<. ( inl ` ( %s ` %s ) ) , %s >.' % (F, A, pair)
            st = w.s([tv, f, ad, w.inst('tm2sagoto')], 'syl3anc', '( %s -> %s = %s )' % (ante, lhs, rhs))
            return st, rhs
        if tag == '3':
            F, Q = _balanced(rest.split())
            f = self.need('%s e. ( %s ^m %s )' % (F, S(T), S(T)))
            q = self.need('%s e. %s' % (Q, STMT(T)))
            fq = w.s([f, q], 'jca', '( %s -> ( %s e. ( %s ^m %s ) /\\ %s e. %s ) )'
                     % (ante, F, S(T), S(T), Q, STMT(T)))
            rhs = '( %s %s <. ( %s ` %s ) , %s >. )' % (Q, SA(T), F, A, D)
            st = w.s([tv, fq, ad, w.inst('tm2saload')], 'syl3anc', '( %s -> %s = %s )' % (ante, lhs, rhs))
            return st, rhs
        if tag == '4':
            F, rest2 = _balanced(rest.split())
            R, Q = _balanced(rest2.split())
            f = self.need('%s e. ( 2o ^m %s )' % (F, S(T)))
            r = self.need('%s e. %s' % (R, STMT(T)))
            q = self.need('%s e. %s' % (Q, STMT(T)))
            frq = w.s([f, r, q], '3jca', '( %s -> ( %s e. ( 2o ^m %s ) /\\ %s e. %s /\\ %s e. %s ) )'
                      % (ante, F, S(T), R, STMT(T), Q, STMT(T)))
            rhs = 'if ( ( %s ` %s ) = 1o , ( %s %s %s ) , ( %s %s %s ) )' % (F, A, R, SA(T), pair, Q, SA(T), pair)
            st = w.s([tv, frq, ad, w.inst('tm2sabr')], 'syl3anc', '( %s -> %s = %s )' % (ante, lhs, rhs))
            return st, rhs
        if tag in ('0', '1', '2'):
            K, rest2 = _balanced(rest.split())
            F, Q = _balanced(rest2.split())
            k = self.need('%s e. %s' % (K, K_(T)))
            q = self.need('%s e. %s' % (Q, STMT(T)))
            if tag == '0':
                f = self.need('%s e. ( ( %s ` %s ) ^m %s )' % (F, G(T), K, S(T)))
                fty = '%s e. ( ( %s ` %s ) ^m %s )' % (F, G(T), K, S(T))
                newD = UPD(T, D, K, '( <" ( %s ` %s ) "> ++ ( %s ` %s ) )' % (F, A, D, K))
                newA = A
                ref = 'tm2sapush'
            else:
                fty = '%s e. ( %s ^m ( %s X. ( ( %s ` %s ) |_| 1o ) ) )' % (F, S(T), S(T), G(T), K)
                f = self.need(fty)
                newA = '( %s ` <. %s , %s >. )' % (F, A, HEAD(D, K))
                newD = D if tag == '1' else UPD(T, D, K, TAIL(D, K))
                ref = 'tm2sapeek' if tag == '1' else 'tm2sapop'
            kfq = w.s([k, f, q], '3jca', '( %s -> ( %s e. %s /\\ %s /\\ %s e. %s ) )'
                      % (ante, K, K_(T), fty, Q, STMT(T)))
            rhs = '( %s %s <. %s , %s >. )' % (Q, SA(T), newA, newD)
            st = w.s([tv, kfq, ad, w.inst(ref)], 'syl3anc', '( %s -> %s = %s )' % (ante, lhs, rhs))
            return st, rhs
        raise ValueError('not a statement tuple: ' + stmt)

    def run(self, stmt, pair, maxsteps=24):
        """prove ( ante -> ( stmt ( TM2sa ` T ) pair ) = <configuration> )"""
        w, ante = self.w, self.ante
        lhs = '( %s %s %s )' % (stmt, SA(self.T), pair)
        cur = lhs; acc = None
        for _ in range(maxsteps):
            sp = split_sa(cur, self.T)
            if sp is None:
                break
            st, rhs = self._clause(sp[0], sp[1])
            acc = st if acc is None else w.s([acc, st], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, rhs))
            cur = rhs
            ev, res = evaluate(w, ante, cur, self.setmap, ifrules=self.ifrules,
                               extra_rules=self.rules)
            if ev is not None:
                acc = w.s([acc, ev], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, res))
                cur = res
            self.trace.append(cur)
        return acc, cur


def K_(T):
    """the stack index set dom ( 1st ` ( 1st ` T ) )"""
    return K(T)


def hstepc(w, ante, T, M, A, E, D1, D2, mstep, alcl, elcl, d1cl, d2cl, body,
           v='v', a='a', t='t', qed=False):
    """One machine step of a fragment as a Hoare triple between the classes
    ` ( { ( inl ` A ) } X. ( S X. { D1 } ) ) ` and
    ` ( { ( inl ` E ) } X. ( S X. { D2 } ) ) ` --- every internal state, the
    stacks pinned.  This is the shape every leaf fragment of the machine layer
    uses: the registers are loaded from the stacks, so the new stacks do not
    depend on the incoming state.

    `body(av)` returns (step proving
    ` ( av -> ( ( M ` A ) ( TM2sa ` T ) <. v , D1 >. ) = <. ( inl ` E ) , <. NEWV , D2 >. >. ) `,
    NEWV, step proving ` ( av -> NEWV e. ( 2nd ` T ) ) `), where
    ` av = ( ante /\\ v e. ( 2nd ` T ) ) `.
    """
    ST = '( %s X. %s )' % (S(T), STK(T))
    P1 = '( %s X. { %s } )' % (S(T), D1)
    C1 = '( { ( inl ` %s ) } X. %s )' % (A, P1)
    P2 = '( %s X. { %s } )' % (S(T), D2)
    C2 = '( { ( inl ` %s ) } X. %s )' % (E, P2)
    av = '( %s /\\ %s e. %s )' % (ante, v, S(T))
    SA_ = lambda x: '( ( %s ` %s ) %s %s )' % (M, A, SA(T), x)
    eq, NEWV, nvcl = body(av)
    RES = '<. ( inl ` %s ) , <. %s , %s >. >.' % (E, NEWV, D2)
    # the result is in the postcondition class
    inle = w.s([], 'fvex', '( inl ` %s ) e. _V' % E)
    sn1 = w.s([inle, w.inst('snidg')], 'ax-mp', '( inl ` %s ) e. { ( inl ` %s ) }' % (E, E))
    sn1a = w.s([sn1], 'a1i', '( %s -> ( inl ` %s ) e. { ( inl ` %s ) } )' % (av, E, E))
    d2v = w.s([d2cl], 'elexd', '( %s -> %s e. _V )' % (ante, D2))
    d2va = w.s([d2v], 'adantr', '( %s -> %s e. _V )' % (av, D2))
    sn2 = w.s([d2va, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (av, D2, D2))
    pr2 = w.s([nvcl, sn2], 'opelxpd', '( %s -> <. %s , %s >. e. %s )' % (av, NEWV, D2, P2))
    res = w.s([sn1a, pr2], 'opelxpd', '( %s -> %s e. %s )' % (av, RES, C2))
    inc = w.s([eq, res], 'eqeltrd', '( %s -> %s e. %s )' % (av, SA_('<. %s , %s >.' % (v, D1)), C2))
    ral1 = w.s([inc], 'ralrimiva', '( %s -> A. %s e. %s %s e. %s )' % (ante, v, S(T), SA_('<. %s , %s >.' % (v, D1)), C2))
    # A. v e. S A. t e. { D1 }  ->  A. a e. ( S X. { D1 } )
    d1v = w.s([d1cl], 'elexd', '( %s -> %s e. _V )' % (ante, D1))
    q1 = w.s([], 'opeq2', '( %s = %s -> <. %s , %s >. = <. %s , %s >. )' % (t, D1, v, t, v, D1))
    q2 = w.s([q1], 'oveq2d', '( %s = %s -> %s = %s )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), SA_('<. %s , %s >.' % (v, D1))))
    q3 = w.s([q2], 'eleq1d', '( %s = %s -> ( %s e. %s <-> %s e. %s ) )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), C2, SA_('<. %s , %s >.' % (v, D1)), C2))
    q4 = w.s([q3], 'ralsng', '( %s e. _V -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (D1, t, D1, SA_('<. %s , %s >.' % (v, t)), C2, SA_('<. %s , %s >.' % (v, D1)), C2))
    q5 = w.s([d1v, q4], 'syl', '( %s -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (ante, t, D1, SA_('<. %s , %s >.' % (v, t)), C2, SA_('<. %s , %s >.' % (v, D1)), C2))
    q6 = w.s([q5], 'ralbidv', '( %s -> ( A. %s e. %s A. %s e. { %s } %s e. %s <-> A. %s e. %s %s e. %s ) )'
             % (ante, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), C2, v, S(T), SA_('<. %s , %s >.' % (v, D1)), C2))
    q7 = w.s([q6, ral1], 'mpbird', '( %s -> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (ante, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), C2))
    p1 = w.s([], 'oveq2', '( %s = <. %s , %s >. -> %s = %s )'
             % (a, v, t, SA_(a), SA_('<. %s , %s >.' % (v, t))))
    p2 = w.s([p1], 'eleq1d', '( %s = <. %s , %s >. -> ( %s e. %s <-> %s e. %s ) )'
             % (a, v, t, SA_(a), C2, SA_('<. %s , %s >.' % (v, t)), C2))
    p3 = w.s([p2], 'ralxp', '( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (a, P1, SA_(a), C2, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), C2))
    p3a = w.s([p3], 'a1i', '( %s -> ( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s ) )'
              % (ante, a, P1, SA_(a), C2, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), C2))
    cond = w.s([p3a, q7], 'mpbird', '( %s -> A. %s e. %s %s e. %s )' % (ante, a, P1, SA_(a), C2))
    # typing
    sd1 = w.s([d1cl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D1, STK(T)))
    sd2 = w.s([d2cl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D2, STK(T)))
    ssr = w.s([], 'ssid', '%s C_ %s' % (S(T), S(T)))
    ssra = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (ante, S(T), S(T)))
    x1 = w.s([ssra, sd1, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ante, P1, ST))
    x2 = w.s([ssra, sd2, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ante, P2, ST))
    tvv = w.s([mstep[1], w.inst('simpl')], 'syl', '( %s -> %s e. V )' % (ante, T))
    c2ss = w.s([tvv, elcl, x2, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ante, C2, CFG(T)))
    j1 = w.s([alcl, x1, c2ss], '3jca', '( %s -> ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) )'
             % (ante, A, L(T), P1, ST, C2, CFG(T)))
    j2 = w.s([mstep[1], j1], 'jca', '( %s -> ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) )'
             % (ante, PHM, A, L(T), P1, ST, C2, CFG(T)))
    j3 = w.s([j2, cond], 'jca', '( %s -> ( ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) /\\ A. %s e. %s %s e. %s ) )'
             % (ante, PHM, A, L(T), P1, ST, C2, CFG(T), a, P1, SA_(a), C2))
    f = '( %s -> %s )' % (ante, HR(C1, T, M, C2, '1'))
    if qed:
        w.qed([j3, w.inst('tm2hstep')], 'syl', f); return None, C1, C2
    tri = w.s([j3, w.inst('tm2hstep')], 'syl', f)
    return tri, C1, C2


def CONSTF(T, X):
    """Lean's `fun _ => X` as a function on the internal states"""
    return '( %s X. { %s } )' % (S(T), X)


def updkval(w, ante, T, D, Kk, Y, tv, dd, kk, yv):
    """( ante -> ( UPD(D,Kk,Y) ` Kk ) = Y ) from steps tv : T e. V, dd : D e. Stk,
    kk : Kk e. dom G, yv : Y e. _V"""
    p1 = w.s([tv, dd], 'jca', '( %s -> ( %s e. V /\\ %s e. %s ) )' % (ante, T, D, STK(T)))
    p2 = w.s([kk, yv], 'jca', '( %s -> ( %s e. %s /\\ %s e. _V ) )' % (ante, Kk, K(T), Y))
    v = w.s([p1, p2, kk, w.inst('tm2stkupv')], 'syl3anc',
            '( %s -> ( %s ` %s ) = if ( %s = %s , %s , ( %s ` %s ) ) )'
            % (ante, UPD(T, D, Kk, Y), Kk, Kk, Kk, Y, D, Kk))
    e = w.s([], 'eqid', '%s = %s' % (Kk, Kk))
    ea = w.s([e], 'a1i', '( %s -> %s = %s )' % (ante, Kk, Kk))
    t = w.s([ea], 'iftrued', '( %s -> if ( %s = %s , %s , ( %s ` %s ) ) = %s )' % (ante, Kk, Kk, Y, D, Kk, Y))
    return w.s([v, t], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ante, UPD(T, D, Kk, Y), Kk, Y))


def hstepP(w, ante, T, M, A, D1, Dpost, mstep, alcl, dpostss, d1cl, body,
           v='v', a='a', t='t', qed=False, phmtxt=None):
    """One machine step of a fragment as a Hoare triple from
    ` ( { ( inl ` A ) } X. ( S X. { D1 } ) ) ` --- every internal state, the
    stacks pinned --- to an arbitrary class ` Dpost ` of configurations.

    `body(av)` returns (step proving
    ` ( av -> ( ( M ` A ) ( TM2sa ` T ) <. v , D1 >. ) = RES ) `, RES,
    step proving ` ( av -> RES e. Dpost ) `), with
    ` av = ( ante /\\ v e. ( 2nd ` T ) ) `.
    """
    ST = '( %s X. %s )' % (S(T), STK(T))
    P1 = '( %s X. { %s } )' % (S(T), D1)
    C1 = '( { ( inl ` %s ) } X. %s )' % (A, P1)
    av = '( %s /\\ %s e. %s )' % (ante, v, S(T))
    SA_ = lambda x: '( ( %s ` %s ) %s %s )' % (M, A, SA(T), x)
    eq, RES, rescl = body(av)
    inc = w.s([eq, rescl], 'eqeltrd', '( %s -> %s e. %s )' % (av, SA_('<. %s , %s >.' % (v, D1)), Dpost))
    ral1 = w.s([inc], 'ralrimiva', '( %s -> A. %s e. %s %s e. %s )'
               % (ante, v, S(T), SA_('<. %s , %s >.' % (v, D1)), Dpost))
    d1v = w.s([d1cl], 'elexd', '( %s -> %s e. _V )' % (ante, D1))
    q1 = w.s([], 'opeq2', '( %s = %s -> <. %s , %s >. = <. %s , %s >. )' % (t, D1, v, t, v, D1))
    q2 = w.s([q1], 'oveq2d', '( %s = %s -> %s = %s )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), SA_('<. %s , %s >.' % (v, D1))))
    q3 = w.s([q2], 'eleq1d', '( %s = %s -> ( %s e. %s <-> %s e. %s ) )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), Dpost, SA_('<. %s , %s >.' % (v, D1)), Dpost))
    q4 = w.s([q3], 'ralsng', '( %s e. _V -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (D1, t, D1, SA_('<. %s , %s >.' % (v, t)), Dpost, SA_('<. %s , %s >.' % (v, D1)), Dpost))
    q5 = w.s([d1v, q4], 'syl', '( %s -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (ante, t, D1, SA_('<. %s , %s >.' % (v, t)), Dpost, SA_('<. %s , %s >.' % (v, D1)), Dpost))
    q6 = w.s([q5], 'ralbidv', '( %s -> ( A. %s e. %s A. %s e. { %s } %s e. %s <-> A. %s e. %s %s e. %s ) )'
             % (ante, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), Dpost, v, S(T),
                SA_('<. %s , %s >.' % (v, D1)), Dpost))
    q7 = w.s([q6, ral1], 'mpbird', '( %s -> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (ante, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), Dpost))
    p1 = w.s([], 'oveq2', '( %s = <. %s , %s >. -> %s = %s )'
             % (a, v, t, SA_(a), SA_('<. %s , %s >.' % (v, t))))
    p2 = w.s([p1], 'eleq1d', '( %s = <. %s , %s >. -> ( %s e. %s <-> %s e. %s ) )'
             % (a, v, t, SA_(a), Dpost, SA_('<. %s , %s >.' % (v, t)), Dpost))
    p3 = w.s([p2], 'ralxp', '( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (a, P1, SA_(a), Dpost, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), Dpost))
    p3a = w.s([p3], 'a1i', '( %s -> ( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s ) )'
              % (ante, a, P1, SA_(a), Dpost, v, S(T), t, D1, SA_('<. %s , %s >.' % (v, t)), Dpost))
    cond = w.s([p3a, q7], 'mpbird', '( %s -> A. %s e. %s %s e. %s )' % (ante, a, P1, SA_(a), Dpost))
    sd1 = w.s([d1cl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D1, STK(T)))
    ssr = w.s([], 'ssid', '%s C_ %s' % (S(T), S(T)))
    ssra = w.s([ssr], 'a1i', '( %s -> %s C_ %s )' % (ante, S(T), S(T)))
    x1 = w.s([ssra, sd1, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ante, P1, ST))
    j1 = w.s([alcl, x1, dpostss], '3jca', '( %s -> ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) )'
             % (ante, A, L(T), P1, ST, Dpost, CFG(T)))
    PH = phmtxt or PHM
    j2 = w.s([mstep, j1], 'jca', '( %s -> ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) )'
             % (ante, PH, A, L(T), P1, ST, Dpost, CFG(T)))
    j3 = w.s([j2, cond], 'jca', '( %s -> ( ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) /\\ A. %s e. %s %s e. %s ) )'
             % (ante, PH, A, L(T), P1, ST, Dpost, CFG(T), a, P1, SA_(a), Dpost))
    f = '( %s -> %s )' % (ante, HR(C1, T, M, Dpost, '1'))
    if qed:
        w.qed([j3, w.inst('tm2hstep')], 'syl', f); return None, C1
    return w.s([j3, w.inst('tm2hstep')], 'syl', f), C1
