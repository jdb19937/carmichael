"""Sortie T4 helpers: the bit layer of TM/Arith.lean, TM/Sub.lean and
TM/Prims.lean (T4-blueprint.md).  Expressions of the layer, a closure for
its types (`2o`, `3o`, `Word 2o`, the layer's own functions) on top of
tools/cl.py, definition unfolding along the arity convention (through
tools/a1blib.py), and the small worksheet idioms the generators share.
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tm
from tm import W                                   # noqa: F401
import congr as _c
from cl import Closure, ClosureError, head, headkey, strip_ante, formula_of, lift  # noqa: F401
import num
import a1blib as _a
mptfv = _a.mptfv
mpoov = _a.mpoov


# ---------------------------------------------------------------- expressions
def BIT(N, I):
    return 'if ( %s e. ( bits ` %s ) , 1o , (/) )' % (I, N)


def BN(C):
    return '( bToNat ` %s )' % C


def TN(L):
    return '( toNat ` %s )' % L


def BWRD(N, M):
    return '( %s bwrd %s )' % (N, M)


def LEN(L):
    return '( # ` %s )' % L


def P2(I):
    return '( 2 ^ %s )' % I


def MOD2(A, I):
    return '( %s mod ( 2 ^ %s ) )' % (A, I)


def FZO(M):
    return '( 0 ..^ %s )' % M


def MAX(X, Y):
    return 'if ( ( # ` %s ) <_ ( # ` %s ) , ( # ` %s ) , ( # ` %s ) )' % (X, Y, Y, X)


def SUM(X, Y, C):
    return '( ( ( toNat ` %s ) + ( toNat ` %s ) ) + ( bToNat ` %s ) )' % (X, Y, C)


def DIF(X, Y, C):
    return '( ( toNat ` %s ) - ( ( toNat ` %s ) + ( bToNat ` %s ) ) )' % (X, Y, C)


def FOLD(F, A, B, C, I):
    return '( ( %s ( %s bwFold %s ) %s ) ` %s )' % (F, A, B, C, I)


def OP3(A, F, B, C):
    """( ( A F B ) ` C )"""
    return '( ( %s %s %s ) ` %s )' % (A, F, B, C)


def CONS(B, L):
    return '( <" %s "> ++ %s )' % (B, L)


def BITSET(L):
    """the set of positions of L holding 1o"""
    return '{ i e. ( 0 ..^ ( # ` %s ) ) | ( %s ` i ) = 1o }' % (L, L)


def BOOLS(C):
    return 'if ( %s , 1o , (/) )' % C


W2 = 'Word 2o'
NONE = '( inr ` (/) )'


def ante_and(*parts):
    return _a.ante_and(*parts)


# ------------------------------------------------------------------- closure
FORM = {'2o': '%s e. 2o', '3o': '%s e. 3o', 'Fin': '%s e. Fin', '_V': '%s e. _V',
        'Word 2o': '%s e. Word 2o', "Word Gamma'": "%s e. Word Gamma'",
        'NN0': '%s e. NN0', 'NN': '%s e. NN', 'ZZ': '%s e. ZZ', 'RR': '%s e. RR',
        'CC': '%s e. CC', 'RR+': '%s e. RR+'}

# closure theorems of the layer: (head, target) -> (label, [(kind, argidx)])
# with the arguments in the arity convention order
T4RULES = {
    ('fv:bToNat', 'NN0'): ('bwbncl', [('2o', 0)]),
    ('fv:toNat', 'NN0'): ('tonatcl', [('Word 2o', 0)]),
    ('ov:bwrd', 'Word 2o'): ('bwrdcl', [('ZZ', 0), ('NN0', 1)]),
    ('ov:Ncmp', '3o'): ('ncmpcl', [('NN0', 0), ('NN0', 1)]),
    ('fv:addCarry', 'Word 2o'): ('addcarrycl', [('2o', 0)]),
    ('fv:bitOf', '2o'): ('bitofcl', [('( 2o |_| 1o )', 0)]),
    ('fv:bl', 'NN0'): ('blcl', [('NN0', 0)]),
    ('fv:incBits', 'Word 2o'): ('incbitscl', [('Word 2o', 0)]),
    ('fv:carries', 'NN0'): ('carriescl', [('Word 2o', 0)]),
    ('fv:incRest', 'Word 2o'): ('increstcl', [('Word 2o', 0)]),
    ('fv:predBits', 'Word 2o'): ('predbitscl', [('Word 2o', 0)]),
    ('fv:borrows', 'NN0'): ('borrowscl', [('Word 2o', 0)]),
    ('fv:predRest', 'Word 2o'): ('predrestcl', [('Word 2o', 0)]),
    ('ov:zeroBits', '2o'): ('zerobitscl', [('Word 2o', 0), ('2o', 1)]),
}
# curried three-argument functions ( ( A f B ) ` C )
T4RULES3 = {
    'sumBit': ('sumbitcl', '2o', ['2o', '2o', '2o']),
    'majBit': ('majcl', '2o', ['2o', '2o', '2o']),
    'borrow': ('borrowcl', '2o', ['2o', '2o', '2o']),
    'cmpStep': ('cmpstepcl', '3o', ['2o', '2o', '3o']),
    'addBits': ('addbitscl', 'Word 2o', ['Word 2o', 'Word 2o', '2o']),
    'subBits': ('subbitscl', 'Word 2o', ['Word 2o', 'Word 2o', '2o']),
    'subBorrow': ('subborrowcl', '2o', ['Word 2o', 'Word 2o', '2o']),
    'subTrunc': ('subtrunccl', 'Word 2o', ['Word 2o', 'Word 2o', '2o']),
    'cmpBits': ('cmpbitscl', '3o', ['Word 2o', 'Word 2o', '3o']),
}
CLOSED = {('1o', '2o'): '1oel2o', ('(/)', '2o'): '0el2o', ('(/)', '3o'): 'bw0el3o',
          ('1o', '3o'): 'bw1oel3o', ('2o', '3o'): 'bw2oel3o', ('(/)', 'Word 2o'): 'wrd0',
          ('(/)', "Word Gamma'"): 'wrd0', ('1o', '_V'): '1oex', ('2o', '_V'): '2oex',
          ('(/)', '_V'): '0ex', ('3o', '_V'): 'bw3oex', ('NN0', '_V'): 'nn0ex',
          ('ZZ', '_V'): 'zex', ('_V', '_V'): None}


def fmt(T, E):
    if T in FORM:
        return FORM[T] % E
    if T.startswith('Word'):
        return '%s e. %s' % (E, T)
    if T in ('ge0', 'gt0', 'ne0', 'ge1', 'gt1'):
        from cl import fmt as _f
        return _f(T, E)
    return '%s e. %s' % (E, T)


def curried(text):
    """(f, [args]) for ( ( A f B ) ` C ) with f in T4RULES3, else None"""
    try:
        n = _c.parse(text)
    except Exception:
        return None
    if n.kind != 'fv':
        return None
    inner = n.kids[0]
    if inner.kind == 'ov' and inner.kids[1].text() in T4RULES3:
        return inner.kids[1].text(), [inner.kids[0].text(), inner.kids[2].text(), n.kids[1].text()]
    return None


class Cl(Closure):
    """tools/cl.py's closure plus the types of the bit layer."""

    def child(self, k, A):
        c = Closure.child(self, k, A)
        c.__class__ = Cl
        # a bound variable ranging over a restricted class abstraction on
        # ( 0 ..^ X ) is a nonnegative integer
        try:
            n = _c.parse(A)
        except Exception:
            n = None
        if n is not None and n.kind == 'rab' and (k, 'NN0') not in c.memo:
            dom = n.kids[0].text()
            if dom.startswith('( 0 ..^ '):
                el = self.w.s([], 'simpr', '( %s -> %s e. %s )' % (c.ante, k, A))
                i1 = self.w.inst('elrabi'); e2 = self.w.s([el, i1], 'syl', '( %s -> %s e. %s )' % (c.ante, k, dom))
                i2 = self.w.inst('elfzonn0'); c.memo[(k, 'NN0')] = self.w.s([e2, i2], 'syl', '( %s -> %s e. NN0 )' % (c.ante, k))
        return c

    def have(self, E, kind, step):
        return Closure.have(self, ' '.join(E.split()), kind, step)

    def _stepf(self, hyps, ref, T, E):
        return self.w.s(hyps, ref, '( %s -> %s )' % (self.ante, fmt(T, E)))

    def _prove(self, E, T):
        w = self.w
        E = ' '.join(E.split())
        if (E, T) in CLOSED and CLOSED[(E, T)]:
            c = num.closed(w, [], CLOSED[(E, T)], fmt(T, E))
            return self._stepf([c], 'a1i', T, E)
        if T == 'Word':
            for src in ('Word 2o', "Word Gamma'"):
                try:
                    return self.prove(E, src)
                except ClosureError:
                    pass
        h = head(E)
        hk = headkey(h)
        if T == '_V':
            for src in ('2o', '3o', 'Word 2o', "Word Gamma'"):
                if (E, src) in self.memo:
                    return self._stepf([self.memo[(E, src)]], 'elexd', T, E)
            try:
                n = _c.parse(E)
            except Exception:
                n = None
            if n is not None and n.kind in ('ov', 'fv'):
                c = num.closed(w, [], {'ov': 'ovex', 'fv': 'fvex'}[n.kind], fmt(T, E))
                return self._stepf([c], 'a1i', T, E)
            if n is not None and n.kind == 'mpt':
                d = self.prove(n.kids[0].text(), '_V')
                i = w.inst('mptexg')
                return self._stepf([d, i], 'syl', T, E)
            if n is not None and n.kind == 'mpo':
                d1 = self.prove(n.kids[0].text(), '_V'); d2 = self.prove(n.kids[1].text(), '_V')
                i = w.inst('mpoexga')
                return self._stepf([d1, d2, i], 'syl2anc', T, E)
            if n is not None and n.kind == 'rab':
                d = self.prove(n.kids[0].text(), '_V')
                i = w.inst('rabexg')
                return self._stepf([d, i], 'syl', T, E)
            if n is not None and n.kind == 'sum':
                c = num.closed(w, [], 'sumex', fmt(T, E))
                return self._stepf([c], 'a1i', T, E)
            if hk == 'if' or (n is not None and n.kind in ('s1',)) or E in ('(/)', '1o', '2o'):
                for src in ('2o', '3o', 'Word 2o', 'NN0', 'ZZ'):
                    try:
                        return self._stepf([self.prove(E, src)], 'elexd', T, E)
                    except ClosureError:
                        pass
        # the layer's own functions
        cur = curried(E)
        if cur and T4RULES3[cur[0]][1] == T:
            lab, _, kinds = T4RULES3[cur[0]]
            hyps = [self.prove(a, k) for a, k in zip(cur[1], kinds)]
            j = self.jca3(hyps)
            i = w.inst(lab)
            return self._stepf([j, i], 'syl', T, E)
        if (hk, T) in T4RULES:
            lab, reqs = T4RULES[(hk, T)]
            args = _c.parse(E)
            if args.kind == 'fv':
                al = [args.kids[1].text()]
            else:
                al = [args.kids[0].text(), args.kids[2].text()]
            hyps = [self.prove(al[i], k) for k, i in reqs]
            i = w.inst(lab)
            if len(hyps) == 1:
                return self._stepf(hyps + [i], 'syl', T, E)
            return self._stepf(hyps + [i], 'syl2anc', T, E)
        if T in ('2o', '3o', 'Word 2o', "Word Gamma'"):
            if hk == 'if':
                a = self.prove(h[2], T)
                b = self.prove(h[3], T)
                return self._stepf([a, b], 'ifcld', T, E)
            if T == '3o' and E in ('1o', '(/)', '2o'):
                pass
            if T == '3o':
                # through 2o
                try:
                    s2 = self.prove(E, '2o')
                    ss = num.closed(w, [], 'bw2oss3o', '2o C_ 3o')
                    ssd = self.w.s([ss], 'a1i', '( %s -> 2o C_ 3o )' % self.ante)
                    return self._stepf([ssd, s2], 'sseldd', T, E)
                except ClosureError:
                    pass
            if T.startswith('Word'):
                n = _c.parse(E)
                if n.kind == 'ov' and n.kids[1].text() == '++':
                    a = self.prove(n.kids[0].text(), T); b = self.prove(n.kids[2].text(), T)
                    i = w.inst('ccatcl')
                    return self._stepf([a, b, i], 'syl2anc', T, E)
                if n.kind == 's1':
                    a = self.prove(n.kids[0].text(), T.split(' ', 1)[1])
                    i = w.inst('s1cl')
                    return self._stepf([a, i], 'syl', T, E)
                if n.kind == 'fv' and n.kids[0].text() == 'reverse':
                    a = self.prove(n.kids[1].text(), T)
                    i = w.inst('revcl')
                    return self._stepf([a, i], 'syl', T, E)
                if n.kind == 'ov' and n.kids[1].text() == 'repeatS':
                    a = self.prove(n.kids[0].text(), T.split(' ', 1)[1]); b = self.prove(n.kids[2].text(), 'NN0')
                    i = w.inst('repsw')
                    return self._stepf([a, b, i], 'syl2anc', T, E)
                if n.kind == 'ov' and n.kids[1].text() == 'substr':
                    a = self.prove(n.kids[0].text(), T)
                    i = w.inst('swrdcl')
                    return self._stepf([a, i], 'syl', T, E)
                if n.kind == 'ov' and n.kids[1].text() == 'prefix':
                    a = self.prove(n.kids[0].text(), T)
                    i = w.inst('pfxcl')
                    return self._stepf([a, i], 'syl', T, E)
                if n.kind == 'fv' and n.kids[0].text() == 'encodeNat' and T == 'Word 2o':
                    a = self.prove(n.kids[1].text(), 'NN0')
                    i = w.inst('encnatcl')
                    return self._stepf([a, i], 'syl', T, E)
            if self.parent is not None:
                try:
                    st = self.parent.prove(E, T)
                    return self._stepf([st], 'adantr', T, E)
                except ClosureError:
                    pass
            raise ClosureError('T4 closure: no rule proves %s under %s' % (fmt(T, E), self.ante), fmt(T, E), [fmt(T, E)])
        if T == 'Fin':
            n = _c.parse(E)
            if n.kind == 'fv' and n.kids[0].text() == 'bits':
                a = self.prove(n.kids[1].text(), 'NN0')
                i = w.inst('bitsfi')
                return self._stepf([a, i], 'syl', T, E)
        if T == 'NN0' and hk == 'mod':
            # ( A mod ( 2 ^ I ) ) with the modulus in NN
            try:
                a = self.prove(h[1], 'ZZ'); b = self.prove(h[2], 'NN')
                i = w.inst('zmodcl')
                return self._stepf([a, b, i], 'syl2anc', T, E)
            except ClosureError:
                pass
        if T == 'NN' and hk == 'exp' and h[1] == '2':
            two = num.closed(w, [], '2nn', '2 e. NN')
            twod = self.w.s([two], 'a1i', '( %s -> 2 e. NN )' % self.ante)
            b = self.prove(h[2], 'NN0')
            i = w.inst('nnexpcl')
            return self._stepf([twod, b, i], 'syl2anc', T, E)
        return Closure._prove(self, E, T)

    def jca3(self, hyps):
        """( ante -> ( a /\\ b /\\ c ) ) from three steps (3jca), two (jca)"""
        forms = [strip_ante(formula_of(self.w, h), self.ante) for h in hyps]
        if len(hyps) == 3:
            return self.w.s(hyps, '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (self.ante, forms[0], forms[1], forms[2]))
        if len(hyps) == 2:
            return self.w.s(hyps, 'jca', '( %s -> ( %s /\\ %s ) )' % (self.ante, forms[0], forms[1]))
        return hyps[0]


def mkcl(w, ante, leaves):
    """a T4 closure under ANTE from {expr: (kind, step)} or {expr: kind}
    (the step then being the simp*-projection of the conjunct)"""
    lv = {}
    for E, v in leaves.items():
        if isinstance(v, str):
            lv[E] = (v, w.s([], 'id', '( %s -> %s )' % (ante, fmt(v, E))))
        else:
            lv[E] = v
    return Cl(w, ante, lv)


def projname(n, i):
    """the simp* lemma projecting part i of a left-nested n-conjunction"""
    if n == 1:
        return 'id'
    if i == n - 1:
        return 'simpr'
    if i == 0:
        return {1: 'simpl', 2: 'simpll', 3: 'simplll', 4: 'simp-4l', 5: 'simp-5l', 6: 'simp-6l'}[n - 1]
    d = n - 1 - i
    return {1: 'simplr', 2: 'simpllr', 3: 'simp-4r', 4: 'simp-5r', 5: 'simp-6r'}[d]


def conj_leaves(w, ante, parts):
    """`parts` is the list of (expr, kind) conjuncts of ANTE in order (a
    left-nested conjunction); returns the leaves dict with the projection
    steps"""
    n = len(parts)
    out = {}
    three = False
    try:
        three = _c.parse_wff(ante).kind == '3an'
    except Exception:
        pass
    for i, (e, k) in enumerate(parts):
        ref = ('simp%d' % (i + 1)) if three else projname(n, i)
        out[e] = (k, w.s([], ref, '( %s -> %s )' % (ante, fmt(k, e))))
    return out


def conj_steps(w, ante, wffs):
    """projection steps of the conjuncts (wff texts) of a left-nested ANTE"""
    n = len(wffs)
    return [w.s([], projname(n, i), '( %s -> %s )' % (ante, f)) for i, f in enumerate(wffs)]


# ------------------------------------------------------- definition unfolding
def defval(w, cl, label, const, args, name=None):
    """( ante -> APPLIED = value ): a1blib.defapply along the arity convention"""
    st, val = _a.defapply(w, cl, label, const, args)
    if name:
        w.lines[-1] = w.lines[-1].replace(st + ':', name + ':', 1)
        return name, val
    return st, val


# ------------------------------------------------------------- if reduction
def ifT(w, ante, condstep, expr):
    """( ante -> if ( ph , A , B ) = A ) from a step proving ( ante -> ph )"""
    n = _c.parse(expr)
    assert n.kind == 'if', expr
    return w.s([condstep], 'iftrued', '( %s -> %s = %s )' % (ante, expr, n.kids[1].text())), n.kids[1].text()


def ifF(w, ante, ncondstep, expr):
    """( ante -> if ( ph , A , B ) = B ) from a step proving ( ante -> -. ph )"""
    n = _c.parse(expr)
    assert n.kind == 'if', expr
    return w.s([ncondstep], 'iffalsed', '( %s -> %s = %s )' % (ante, expr, n.kids[2].text())), n.kids[2].text()


def eqtr(w, ante, steps, lhs, mids):
    """chain ( ante -> lhs = m1 ), ( ante -> m1 = m2 ) ... by eqtrd; mids are
    the right-hand sides in order; returns the final step"""
    acc = steps[0]
    for st, m in zip(steps[1:], mids[1:]):
        acc = w.s([acc, st], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, m))
    return acc


def rewrite(w, ante, expr, rules):
    """( ante -> expr = expr' ) applying `rules` {old: (new, step)} once"""
    return w.rewrite(expr, rules, ante)


def rewrite_chain(w, ante, expr, rulesets):
    """apply several rule dicts in sequence, chaining with eqtrd; returns
    (step or None, final)"""
    cur = expr; steps = []; mids = []
    for rules in rulesets:
        rules = {k: v for k, v in rules.items() if k in cur}
        if not rules:
            continue
        st, new = w.rewrite(cur, rules, ante)
        if st is None:
            continue
        steps.append(st); mids.append(new); cur = new
    if not steps:
        return None, expr
    acc = steps[0]
    for st, m in zip(steps[1:], mids[1:]):
        acc = w.s([acc, st], 'eqtrd', '( %s -> %s = %s )' % (ante, expr, m))
    return acc, cur


def wrewrite(w, ante, wff, rules):
    """( ante -> ( wff <-> wff' ) )"""
    return w.wcongr(wff, {}, ante, {}, rules=rules)


# ------------------------------------------------------------- cases on 2o
def cases2o(w, ante, B, memstep, body, concl):
    """Prove ( ante -> concl ) by the two cases B = (/) and B = 1o, given
    memstep: ( ante -> B e. 2o ) and body(ante2, eqstep) returning a step
    ( ante2 -> concl ) for ante2 = ( ante /\\ B = v ).  Uses bwel2o and
    mpjaodan."""
    dj = w.inst('bwel2o')
    d = w.s([memstep, dj], 'syl', '( %s -> ( %s = (/) \\/ %s = 1o ) )' % (ante, B, B))
    a0 = '( %s /\\ %s = (/) )' % (ante, B)
    e0 = w.s([], 'simpr', '( %s -> %s = (/) )' % (a0, B))
    s0 = body(a0, e0, '(/)')
    a1 = '( %s /\\ %s = 1o )' % (ante, B)
    e1 = w.s([], 'simpr', '( %s -> %s = 1o )' % (a1, B))
    s1 = body(a1, e1, '1o')
    return w.s([s0, s1, d], 'mpjaodan', '( %s -> %s )' % (ante, concl))


def subst_eq(w, ante, eqstep, var, val, expr):
    """( ante -> expr = expr[var := val] ) from ( ante -> var = val )"""
    st, new = w.congr(expr, {var: val}, ante, {var: eqstep})
    if st is None:
        st = w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, expr, expr))
    return st, new


def wsubst_eq(w, ante, eqstep, var, val, wff):
    st, new = w.wcongr(wff, {var: val}, ante, {var: eqstep})
    if st is None:
        st = w.s([], 'biidd', '( %s -> ( %s <-> %s ) )' % (ante, wff, wff))
    return st, new


# --------------------------------------------------------------- truth values
class PropEval:
    """Closed truth-value evaluation of a wff built from `( X = 1o )`,
    `( X = Y )` for X, Y in {(/), 1o, 2o}, -., /\\, \\/, \\/_, <->, under the
    antecedent T. (steps are ( T. -> ph ) or ( T. -> -. ph ))."""

    def __init__(self, w):
        self.w = w
        self.ante = 'T.'
        self.memo = {}

    def lit(self, X, Y):
        """(truth, step) for X = Y with X, Y literal ordinals"""
        w = self.w
        if X == Y:
            e = num.closed(w, [], 'eqid', '%s = %s' % (X, X))
            return True, w.s([e], 'a1i', '( T. -> %s = %s )' % (X, X))
        key = tuple(sorted([X, Y]))
        lab = {('(/)', '1o'): '1n0', ('(/)', '2o'): '2on0', ('1o', '2o'): 'bw1o2o'}[key]
        # 1n0: 1o =/= (/); 2on0: 2o =/= (/); bw1o2o: 1o =/= 2o
        ne = num.closed(w, [], lab, {'1n0': '1o =/= (/)', '2on0': '2o =/= (/)', 'bw1o2o': '1o =/= 2o'}[lab])
        big, small = {'1n0': ('1o', '(/)'), '2on0': ('2o', '(/)'), 'bw1o2o': ('1o', '2o')}[lab]
        if (X, Y) == (big, small):
            nq = num.closed(w, [ne], 'neneqi' if False else 'neii', '-. %s = %s' % (X, Y))
        else:
            nq = num.closed(w, [ne], 'nesymi', '-. %s = %s' % (X, Y))
        return False, w.s([nq], 'a1i', '( T. -> -. %s = %s )' % (X, Y))

    def ev(self, node):
        """(truth, step) with the step proving ( T. -> ph ) or ( T. -> -. ph )"""
        w = self.w
        t = node.text()
        if t in self.memo:
            return self.memo[t]
        k = node.kind
        if k == 'eq':
            r = self.lit(node.kids[0].text(), node.kids[1].text())
        elif k == 'not':
            v, s = self.ev(node.kids[0])
            inner = node.kids[0].text()
            if v:
                r = (False, w.s([s], 'notnotd', '( T. -> -. -. %s )' % inner))
            else:
                r = (True, s)
        elif k in ('and', 'or', 'bi', 'xor'):
            v1, s1 = self.ev(node.kids[0]); v2, s2 = self.ev(node.kids[1])
            p, q = node.kids[0].text(), node.kids[1].text()
            if k == 'and':
                if v1 and v2:
                    r = (True, w.s([s1, s2], 'jca', '( T. -> ( %s /\\ %s ) )' % (p, q)))
                elif not v1:
                    i = w.inst('simpl'); i2 = w.inst('con3i')
                    st = w.s([s1], 'intnanrd', '( T. -> -. ( %s /\\ %s ) )' % (p, q))
                    r = (False, st)
                else:
                    r = (False, w.s([s2], 'intnand', '( T. -> -. ( %s /\\ %s ) )' % (p, q)))
            elif k == 'or':
                if v1:
                    r = (True, w.s([s1], 'orcd', '( T. -> ( %s \\/ %s ) )' % (p, q)))
                elif v2:
                    r = (True, w.s([s2], 'olcd', '( T. -> ( %s \\/ %s ) )' % (p, q)))
                else:
                    j = w.s([s1, s2], 'jca', '( T. -> ( -. %s /\\ -. %s ) )' % (p, q))
                    i = w.inst('ioran')
                    r = (False, w.s([j, i], 'sylibr', '( T. -> -. ( %s \\/ %s ) )' % (p, q)))
            elif k == 'bi':
                r = self._bi(p, q, v1, s1, v2, s2)
            else:   # xor
                vb, sb = self._bi(p, q, v1, s1, v2, s2)
                i = w.inst('df-xor')
                if vb:
                    # ( p <-> q ) true => -. ( p \/_ q )
                    nn = w.s([sb], 'notnotd', '( T. -> -. -. ( %s <-> %s ) )' % (p, q))
                    r = (False, w.s([nn, i], 'sylnibr' if False else 'sylnibr', '( T. -> -. ( %s \\/_ %s ) )' % (p, q)))
                else:
                    r = (True, w.s([sb, i], 'sylibr', '( T. -> ( %s \\/_ %s ) )' % (p, q)))
        else:
            raise ValueError('PropEval: ' + t)
        self.memo[t] = r
        return r

    def _bi(self, p, q, v1, s1, v2, s2):
        w = self.w
        if v1 == v2:
            if v1:
                st = w.s([s1, s2], '2thd', '( T. -> ( %s <-> %s ) )' % (p, q))
            else:
                st = w.s([s1, s2], '2falsed', '( T. -> ( %s <-> %s ) )' % (p, q))
            return True, st
        if v1:
            # p true, q false: -. ( p <-> q )
            i = w.inst('pm5.501')
            b = w.s([s1, i], 'syl', '( T. -> ( %s <-> ( %s <-> %s ) ) )' % (q, p, q))
            return False, w.s([s2, b], 'mtbid', '( T. -> -. ( %s <-> %s ) )' % (p, q))
        i = w.inst('nbn2')
        b = w.s([s1, i], 'syl', '( T. -> ( -. %s <-> ( %s <-> %s ) ) )' % (q, p, q))
        nn = w.s([s2], 'notnotd', '( T. -> -. -. %s )' % q)
        return False, w.s([nn, b], 'mtbid', '( T. -> -. ( %s <-> %s ) )' % (p, q))

    def reduce_ifs(self, expr):
        """( T. -> expr = expr' ) with every if whose condition is closed
        reduced; returns (step or None, expr')"""
        w = self.w
        cur = expr; chain = []; mids = []
        while True:
            rules = {}
            def visit(n):
                if n.kind == 'if':
                    try:
                        v, s = self.ev(n.kids[0])
                    except (ValueError, KeyError):
                        v = None
                    if v is not None:
                        if v:
                            st = w.s([s], 'iftrued', '( T. -> %s = %s )' % (n.text(), n.kids[1].text()))
                            rules[n.text()] = (n.kids[1].text(), st)
                        else:
                            st = w.s([s], 'iffalsed', '( T. -> %s = %s )' % (n.text(), n.kids[2].text()))
                            rules[n.text()] = (n.kids[2].text(), st)
                        return
                for k in n.kids:
                    visit(k)
            visit(_c.parse(cur))
            if not rules:
                break
            st, new = w.rewrite(cur, rules, 'T.')
            chain.append(st); mids.append(new); cur = new
        if not chain:
            return None, expr
        acc = chain[0]
        for st, m in zip(chain[1:], mids[1:]):
            acc = w.s([acc, st], 'eqtrd', '( T. -> %s = %s )' % (expr, m))
        return acc, cur


# ------------------------------------------------------------ word equality
def wrdeq(w, ante, L, R, clL, clR, leneq, letter, i='i', name=None):
    """( ante -> L = R ) by eqwrd: from clL: ( ante -> L e. Word S ), clR,
    leneq: ( ante -> ( # ` L ) = ( # ` R ) ) and letter(a2, istep) returning
    a step ( ( ante /\\ i e. ( 0 ..^ ( # ` L ) ) ) -> ( L ` i ) = ( R ` i ) )."""
    dom = '( 0 ..^ ( # ` %s ) )' % L
    a2 = '( %s /\\ %s e. %s )' % (ante, i, dom)
    ist = w.s([], 'simpr', '( %s -> %s e. %s )' % (a2, i, dom))
    lt = letter(a2, ist)
    al = w.s([lt], 'ralrimiva', '( %s -> A. %s e. %s ( %s ` %s ) = ( %s ` %s ) )' % (ante, i, dom, L, i, R, i))
    body = '( ( # ` %s ) = ( # ` %s ) /\\ A. %s e. %s ( %s ` %s ) = ( %s ` %s ) )' % (L, R, i, dom, L, i, R, i)
    j = w.s([leneq, al], 'jca', '( %s -> %s )' % (ante, body))
    e = w.inst('eqwrd')
    bi = w.s([clL, clR, e], 'syl2anc', '( %s -> ( %s = %s <-> %s ) )' % (ante, L, R, body))
    if name == 'qed':
        w.qed([j, bi], 'mpbird', '( %s -> %s = %s )' % (ante, L, R))
        return 'qed'
    return w.s([j, bi], 'mpbird', '( %s -> %s = %s )' % (ante, L, R), name=name)


def promote(w, st):
    """turn the step ST (the last line) into the qed line"""
    for k in range(len(w.lines) - 1, -1, -1):
        if w.lines[k].startswith(st + ':'):
            w.lines[k] = w.lines[k].replace(st + ':', 'qed:', 1)
            return
    raise KeyError(st)


def lenrw(w, ante, L, lenstep, memstep, i='i'):
    """from ( ante -> i e. ( 0 ..^ X ) ) and ( ante -> ( # ` L ) = X ), the
    step ( ante -> i e. ( 0 ..^ ( # ` L ) ) )"""
    f = formula_of(w, lenstep)
    X = strip_ante(f, ante).split(' = ', 1)[1]
    o = w.s([lenstep], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ %s ) )' % (ante, L, X))
    return w.s([memstep, o], 'eleqtrrd', '( %s -> %s e. ( 0 ..^ ( # ` %s ) ) )' % (ante, i, L))


def nn0uz(w, ante, mstep, M):
    """( ante -> M e. ( ZZ>= ` 0 ) ) from ( ante -> M e. NN0 )"""
    u = num.closed(w, [], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')
    return w.s([mstep, u], 'eleqtrdi', '( %s -> %s e. ( ZZ>= ` 0 ) )' % (ante, M))


def bitcongr(w, ante, eqstep, N, I, J):
    """( ante -> BIT(N,I) = BIT(N,J) ) from ( ante -> I = J )"""
    e = w.s([eqstep], 'eleq1d', '( %s -> ( %s e. ( bits ` %s ) <-> %s e. ( bits ` %s ) ) )' % (ante, I, N, J, N))
    return w.s([e], 'ifbid', '( %s -> %s = %s )' % (ante, BIT(N, I), BIT(N, J)))


def sumren(w, ante, A, i, n):
    """( ante -> sum_ i e. A ( 2 ^ i ) = sum_ n e. A ( 2 ^ n ) )"""
    e = w.s([], 'oveq2', '( %s = %s -> ( 2 ^ %s ) = ( 2 ^ %s ) )' % (i, n, i, n))
    c = w.s([e], 'cbvsumv', 'sum_ %s e. %s ( 2 ^ %s ) = sum_ %s e. %s ( 2 ^ %s )' % (i, A, i, n, A, n))
    return w.s([c], 'a1i', '( %s -> sum_ %s e. %s ( 2 ^ %s ) = sum_ %s e. %s ( 2 ^ %s ) )' % (ante, i, A, i, n, A, n))


def bitsetel(w, ante, L, I, istep):
    """( ante -> ( I e. BITSET(L) <-> ( L ` I ) = 1o ) ) given istep: ( ante -> I e. ( 0 ..^ ( # ` L ) ) )"""
    dom = '( 0 ..^ ( # ` %s ) )' % L
    f = w.s([], 'fveq2', '( i = %s -> ( %s ` i ) = ( %s ` %s ) )' % (I, L, L, I))
    e = w.s([f], 'eqeq1d', '( i = %s -> ( ( %s ` i ) = 1o <-> ( %s ` %s ) = 1o ) )' % (I, L, L, I))
    r = w.s([e], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ ( %s ` %s ) = 1o ) )' % (I, BITSET(L), I, dom, L, I))
    rd = w.s([r], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. %s /\\ ( %s ` %s ) = 1o ) ) )' % (ante, I, BITSET(L), I, dom, L, I))
    b = w.s([istep], 'biantrurd', '( %s -> ( ( %s ` %s ) = 1o <-> ( %s e. %s /\\ ( %s ` %s ) = 1o ) ) )' % (ante, L, I, I, dom, L, I))
    return w.s([rd, b], 'bitr4d', '( %s -> ( %s e. %s <-> ( %s ` %s ) = 1o ) )' % (ante, I, BITSET(L), L, I))


def bool_from_bi(w, ante, X, cond, bistep, symstep):
    """( ante -> X = if ( cond , 1o , (/) ) ) from bistep: ( ante -> ( X = 1o <-> cond ) )
    and symstep: ( ante -> X e. 2o )"""
    B = 'if ( %s , 1o , (/) )' % cond
    a1 = '( %s /\\ X0 )' % ante
    a1 = '( %s /\\ %s = 1o )' % (ante, X)
    h1 = w.s([], 'simpr', '( %s -> %s = 1o )' % (a1, X))
    bi1 = w.s([bistep], 'adantr', '( %s -> ( %s = 1o <-> %s ) )' % (a1, X, cond))
    m1 = w.s([h1, bi1], 'mpbid', '( %s -> %s )' % (a1, cond))
    i1 = w.s([m1], 'iftrued', '( %s -> %s = 1o )' % (a1, B))
    c1 = w.s([h1, i1], 'eqtr4d', '( %s -> %s = %s )' % (a1, X, B))
    a2 = '( %s /\\ -. %s = 1o )' % (ante, X)
    h2 = w.s([], 'simpr', '( %s -> -. %s = 1o )' % (a2, X))
    bi2 = w.s([bistep], 'adantr', '( %s -> ( %s = 1o <-> %s ) )' % (a2, X, cond))
    m2 = w.s([h2, bi2], 'mtbid', '( %s -> -. %s )' % (a2, cond))
    i2 = w.s([m2], 'iffalsed', '( %s -> %s = (/) )' % (a2, B))
    s2 = w.s([symstep], 'adantr', '( %s -> %s e. 2o )' % (a2, X))
    n2 = w.s([s2, w.inst('bwel2on')], 'syl', '( %s -> ( -. %s = 1o <-> %s = (/) ) )' % (a2, X, X))
    z2 = w.s([h2, n2], 'mpbid', '( %s -> %s = (/) )' % (a2, X))
    c2 = w.s([z2, i2], 'eqtr4d', '( %s -> %s = %s )' % (a2, X, B))
    return w.s([c1, c2], 'pm2.61dan', '( %s -> %s = %s )' % (ante, X, B))


def uz2(w, ante):
    """( ante -> 2 e. ( ZZ>= ` 2 ) )"""
    z2 = num.closed(w, [], '2z', '2 e. ZZ'); u = w.inst('uzid')
    u2 = num.closed(w, [z2, u], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    return w.s([u2], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ante)


def ltexp2(w, ante, cl, M, N):
    """( ante -> ( M < N <-> ( 2 ^ M ) < ( 2 ^ N ) ) ) for integers M, N"""
    r2c = num.closed(w, [], '2re', '2 e. RR'); r2 = w.s([r2c], 'a1i', '( %s -> 2 e. RR )' % ante)
    mz = cl.mem(M, 'ZZ'); nz = cl.mem(N, 'ZZ')
    j = w.s([r2, mz, nz], '3jca', '( %s -> ( 2 e. RR /\\ %s e. ZZ /\\ %s e. ZZ ) )' % (ante, M, N))
    lt = num.closed(w, [], '1lt2', '1 < 2'); ltd = w.s([lt], 'a1i', '( %s -> 1 < 2 )' % ante)
    return w.s([j, ltd, w.inst('ltexp2')], 'syl2anc', '( %s -> ( %s < %s <-> ( 2 ^ %s ) < ( 2 ^ %s ) ) )' % (ante, M, N, M, N))


# ------------------------------------------------- a wff parser with \/_
class _P:
    """( X = Y ), -. ph, ( ph /\\ ps ), ( ph \\/ ps ), ( ph \\/_ ps ), ( ph <-> ps )
    over literal/atomic classes; produces congr.Node objects (kinds eq, not,
    and, or, xor, bi) so that PropEval can evaluate them."""
    OPS = {'/\\': 'and', '\\/': 'or', '\\/_': 'xor', '<->': 'bi', '->': 'imp'}

    def __init__(self, text):
        self.t = text.split(); self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, tok=None):
        cur = self.t[self.i]
        assert tok is None or cur == tok, (tok, cur, ' '.join(self.t))
        self.i += 1
        return cur

    def wff(self):
        start = self.i
        if self.peek() == '-.':
            self.eat(); ph = self.wff()
            return _c.Node('not', [ph], self.t[start:self.i])
        if self.peek() == '(':
            # try ( class = class ) first: classes here are single tokens or
            # parenthesised class expressions of tools/congr.py
            save = self.i
            self.eat('(')
            try:
                A = self.cls()
                if self.peek() == '=':
                    self.eat('='); B = self.cls(); self.eat(')')
                    return _c.Node('eq', [A, B], self.t[start:self.i])
            except Exception:
                pass
            self.i = save
            self.eat('('); ph = self.wff(); op = self.eat(); ps = self.wff(); self.eat(')')
            return _c.Node(self.OPS[op], [ph, ps], self.t[start:self.i])
        A = self.cls(); self.eat('='); B = self.cls()
        return _c.Node('eq', [A, B], self.t[start:self.i])

    def cls(self):
        start = self.i
        if self.peek() == '(':
            depth = 0
            while True:
                tok = self.eat()
                if tok == '(':
                    depth += 1
                elif tok == ')':
                    depth -= 1
                    if depth == 0:
                        break
            return _c.Node('atom', [], self.t[start:self.i])
        self.eat()
        return _c.Node('atom', [], self.t[start:self.i])


def parsewff(text):
    return _P(text).wff()


def wffcongr(w, ante, node, sub, leaves):
    """( ante -> ( ph <-> ph[sub] ) ) for a wff of the mini-parser whose atoms
    are single set variables (in sub) or literals; leaves: var -> step
    proving ( ante -> var = X ).  Returns (step or None, new text)."""
    k = node.kind
    if k == 'eq':
        A, B = node.kids[0].text(), node.kids[1].text()
        if A in sub and B in sub:
            l = w.s([leaves[A], leaves[B]], 'eqeq12d', '( %s -> ( %s = %s <-> %s = %s ) )' % (ante, A, B, sub[A], sub[B]))
            return l, '%s = %s' % (sub[A], sub[B])
        if A in sub:
            return w.s([leaves[A]], 'eqeq1d', '( %s -> ( %s = %s <-> %s = %s ) )' % (ante, A, B, sub[A], B)), '%s = %s' % (sub[A], B)
        if B in sub:
            return w.s([leaves[B]], 'eqeq2d', '( %s -> ( %s = %s <-> %s = %s ) )' % (ante, A, B, A, sub[B])), '%s = %s' % (A, sub[B])
        return None, node.text()
    if k == 'not':
        s, nt = wffcongr(w, ante, node.kids[0], sub, leaves)
        if s is None:
            return None, node.text()
        return w.s([s], 'notbid', '( %s -> ( -. %s <-> -. %s ) )' % (ante, node.kids[0].text(), nt)), '-. ' + nt
    s1, n1 = wffcongr(w, ante, node.kids[0], sub, leaves)
    s2, n2 = wffcongr(w, ante, node.kids[1], sub, leaves)
    if s1 is None and s2 is None:
        return None, node.text()
    if s1 is None:
        s1 = w.s([], 'biidd', '( %s -> ( %s <-> %s ) )' % (ante, n1, n1))
    if s2 is None:
        s2 = w.s([], 'biidd', '( %s -> ( %s <-> %s ) )' % (ante, n2, n2))
    op = {'and': '/\\', 'or': '\\/', 'xor': '\\/_', 'bi': '<->', 'imp': '->'}[k]
    lem = {'and': 'anbi12d', 'or': 'orbi12d', 'xor': 'xorbi12d', 'bi': 'bibi12d', 'imp': 'imbi12d'}[k]
    old = node.text(); new = '( %s %s %s )' % (n1, op, n2)
    return w.s([s1, s2], lem, '( %s -> ( %s <-> %s ) )' % (ante, old, new)), new


def op3val(w, label, const, A, B, C, cond, kindC='2o', desc=None):
    """the value lemma of a curried Boolean operation
    ( ( A e. 2o /\\ B e. 2o /\\ C e. kindC ) -> ( ( A const B ) ` C ) = if ( cond[A,B,C] , 1o , (/) ) )
    where cond is the definition's condition in a, b, c; the branch values
    are read from the definition body."""
    body = tm.defbody(label)
    # body: ( a e. 2o , b e. 2o |-> ( c e. K |-> if ( COND , X , Y ) ) )
    n = _c.parse(body) if '\\/_' not in body else None
    inner = body.split('|-> ', 1)[1].rsplit(' )', 1)[0]          # ( c e. K |-> if ( ... ) )
    ifexpr = inner.split('|-> ', 1)[1].rsplit(' )', 1)[0]          # if ( COND , X , Y )
    condtxt = ifexpr[len('if ( '):]
    # split off the two branches at the top-level commas
    depth = 0; cuts = []
    toks = condtxt.split()
    for i, t in enumerate(toks):
        if t in ('(', '{'): depth += 1
        elif t in (')', '}'): depth -= 1
        elif t == ',' and depth == 0: cuts.append(i)
    COND = ' '.join(toks[:cuts[0]]); X = ' '.join(toks[cuts[0] + 1:cuts[1]]); Y = ' '.join(toks[cuts[1] + 1:-1])
    IF = lambda c: 'if ( %s , %s , %s )' % (c, X, Y)
    ante = '( %s e. 2o /\\ %s e. 2o /\\ %s e. %s )' % (A, B, C, kindC)
    node = parsewff(COND)
    # ( ( a = A /\ b = B ) -> if(COND) = if(COND[A,B]) )
    e2 = '( a = %s /\\ b = %s )' % (A, B)
    la = w.s([], 'simpl', '( %s -> a = %s )' % (e2, A)); lb = w.s([], 'simpr', '( %s -> b = %s )' % (e2, B))
    s1, c1 = wffcongr(w, e2, node, {'a': A, 'b': B}, {'a': la, 'b': lb})
    i1 = w.s([s1], 'ifbid', '( %s -> %s = %s )' % (e2, IF(COND), IF(c1)))
    MPT = lambda c: '( c e. %s |-> %s )' % (kindC, IF(c))
    m1 = w.s([i1], 'mpteq2dv', '( %s -> %s = %s )' % (e2, MPT(COND), MPT(c1)))
    d = w.s([], label, '%s = %s' % (const, body))
    ov = w.s([m1, d], 'ovmpoga', '( ( %s e. 2o /\\ %s e. 2o /\\ %s e. _V ) -> ( %s %s %s ) = %s )' % (A, B, MPT(c1), A, const, B, MPT(c1)))
    kex = num.closed(w, [], {'2o': '2oex', '3o': 'bw3oex'}[kindC], '%s e. _V' % kindC)
    mx = num.closed(w, [kex, w.inst('mptexg')], 'ax-mp', '%s e. _V' % MPT(c1))
    pa = w.s([], 'simp1', '( %s -> %s e. 2o )' % (ante, A)); pb = w.s([], 'simp2', '( %s -> %s e. 2o )' % (ante, B)); pc = w.s([], 'simp3', '( %s -> %s e. %s )' % (ante, C, kindC))
    mxd = w.s([mx], 'a1i', '( %s -> %s e. _V )' % (ante, MPT(c1)))
    o = w.s([pa, pb, mxd, ov], 'syl3anc', '( %s -> ( %s %s %s ) = %s )' % (ante, A, const, B, MPT(c1)))
    f1 = w.s([o], 'fveq1d', '( %s -> ( ( %s %s %s ) ` %s ) = ( %s ` %s ) )' % (ante, A, const, B, C, MPT(c1), C))
    e3 = 'c = %s' % C
    lc = w.s([], 'id', '( %s -> c = %s )' % (e3, C))
    s2, c2 = wffcongr(w, e3, parsewff(c1), {'c': C}, {'c': lc})
    i2 = w.s([s2], 'ifbid', '( %s -> %s = %s )' % (e3, IF(c1), IF(c2)))
    em = w.s([], 'eqid', '%s = %s' % (MPT(c1), MPT(c1)))
    fv = w.s([i2, em], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (C, kindC, IF(c2), MPT(c1), C, IF(c2)))
    xe = num.closed(w, [], {'1o': '1oex', '(/)': '0ex', '2o': '2oex'}.get(X, 'fvex'), '%s e. _V' % X) if X in ('1o', '(/)', '2o') else None
    if X in ('1o', '(/)', '2o') and Y in ('1o', '(/)', '2o'):
        ye = num.closed(w, [], {'1o': '1oex', '(/)': '0ex', '2o': '2oex'}[Y], '%s e. _V' % Y)
        ie = num.closed(w, [xe, ye, w.inst('ifexg')], 'mp2an', '%s e. _V' % IF(c2))
        ied = w.s([ie], 'a1i', '( %s -> %s e. _V )' % (ante, IF(c2)))
    else:
        cl = Cl(w, ante, {C: (kindC, pc)})
        ied = cl.mem(IF(c2), '_V')
    f2 = w.s([pc, ied, fv], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, MPT(c1), C, IF(c2)))
    st = w.s([f1, f2], 'eqtrd', '( %s -> ( ( %s %s %s ) ` %s ) = %s )' % (ante, A, const, B, C, IF(c2)))
    return st, IF(c2), ante


def closed_if(w, ifexpr, cond_node):
    """( T. -> if ( cond , X , Y ) = v ) for a closed condition; returns (step, v)"""
    pe = PropEval(w)
    v, s = pe.ev(cond_node)
    n = _c.parse(ifexpr) if '\\/_' not in ifexpr else None
    # branches by text
    toks = ifexpr.split(); depth = 0; cuts = []
    for i, t in enumerate(toks[2:], 2):
        if t in ('(', '{'): depth += 1
        elif t in (')', '}'): depth -= 1
        elif t == ',' and depth == 0: cuts.append(i)
    X = ' '.join(toks[cuts[0] + 1:cuts[1]]); Y = ' '.join(toks[cuts[1] + 1:-1])
    if v:
        return w.s([s], 'iftrued', '( T. -> %s = %s )' % (ifexpr, X)), X
    return w.s([s], 'iffalsed', '( T. -> %s = %s )' % (ifexpr, Y)), Y
