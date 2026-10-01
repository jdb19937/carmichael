"""Congruence step generator for mmj2 worksheets.

The parser covers the fragment of set.mm class/wff syntax used in
carmichael.mm: operation and function values, ordered pairs and triples,
singletons/pairs/triples, class abstractions (`{ x | ph }`, `{ x e. A | ph }`,
`{ <. x , y >. | ph }`), maps-to and two-argument maps-to, `if`, indexed
unions and products, `Word`, `dom`, `ran`, `U.`, `suc`, converse, `rec`,
`seq`, singleton words, decimal numerals, `-u`, `~P`, and `sum_` / `prod_`.

parse(tokens) builds a tree for the fragment of set.mm class/wff syntax used in
carmichael.mm; congr(tree, sub, ante, leaves, gen) emits deduction-form steps
`( ante -> E = E[sub] )` for a substitution of set variables by class
expressions, choosing the set.mm congruence lemma from the children that
change.  `leaves` maps a substituted variable to the name of the worksheet
step proving `( ante -> x = X )`.  gen is a StepGen (fresh names, output).

Binders: the body hypothesis of `sumeq2dv` / `prodeq2dv` is under the extended
antecedent `( ph /\\ k e. A )`, so a body-only change takes the `s` variant and
a change to both the range and the body lifts the body hypothesis with
`adantr`.  Every such lemma carries a `$d` against the antecedent; when the
bound variable occurs there, `closed_route` proves the congruence under the
closed antecedent `( x = X )` and carries it back with one `syl`, and
`dvcheck` raises `DVError` when even that does not apply.
"""
import re

INFIX_SPECIAL = {'u.': ('uneq1d', 'uneq2d', 'uneq12d'),
                 '\\': ('difeq1d', 'difeq2d', 'difeq12d'),
                 'X.': ('xpeq1d', 'xpeq2d', 'xpeq12d'),
                 '|`': ('reseq1d', 'reseq2d', 'reseq12d'),
                 'i^i': ('ineq1d', 'ineq2d', 'ineq12d'),
                 '|_|': ('djueq1d*', 'djueq2d*', 'djueq12d*'),
                 'o.': ('coeq1d', 'coeq2d', 'coeq12d')}
SETVAR = re.compile(r'^[a-zA-Z]$')
LOWVAR = re.compile(r'^[a-z]$')

# congruence lemmas whose `$d` forbids the bound variable from occurring in
# the deduction's antecedent (bound occurrences included): the check that
# tools/fsum.py performs for `fsum*`, applied at generation time here
DV_LEMMAS = ('sumeq2dv', 'sumeq2sdv', 'sumeq12dv', 'prodeq2dv', 'prodeq2sdv',
             'prodeq12dv', 'rabbidv', 'rabeqbidv', 'ralbidv', 'raleqbidv',
             'rexbidv', 'rexeqbidv', 'ixpeq2dv', 'ixpeq12dv',
             'mpteq2dv', 'mpteq12dv', 'mpoeq3dv', 'mpoeq123dv')

# node kinds whose congruence lemma carries such a `$d`: when the bound
# variable occurs in the antecedent, the congruence is proved instead under
# the closed antecedent `( x = X )` and discharged with syl (`closed_route`)
DV_KINDS = ('sum', 'prod', 'ral', 'rex', 'rab', 'mpt', 'mpo', 'ixp')


class DVError(Exception):
    """a bound variable occurs in the antecedent of a congruence step"""


def dvcheck(ante, var, lemma):
    if re.search(r'(^|\s)%s(\s|$)' % re.escape(var), ante):
        raise DVError('%s needs $d %s ph, but %s occurs in the antecedent %s'
                      % (lemma, var, var, ante))


class Node:
    def __init__(self, kind, kids, toks, bound=()):
        self.kind = kind      # 'atom','ov','fv','op','ot','sn','pr','if','eq','el',
                              # 'iun','ixp','word','dom','ran','uni','suc','rec','s1',
                              # 'mpt','mpo','ne','not','and'
        self.kids = kids
        self.toks = toks      # full token list of this subterm
        self.bound = bound    # set variables bound at this node

    def text(self):
        return ' '.join(self.toks)

    def free(self):
        s = set()
        if self.kind == 'atom':
            if SETVAR.match(self.toks[0]):
                s.add(self.toks[0])
            return s
        for k in self.kids:
            s |= k.free()
        return s - set(self.bound)


def tokenize(s):
    return s.split()


class Parser:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def eat(self, tok=None):
        cur = self.t[self.i]
        if tok is not None and cur != tok:
            raise SyntaxError('expected %r got %r at %d: %s' % (tok, cur, self.i, ' '.join(self.t[max(0, self.i - 8):self.i + 8])))
        self.i += 1
        return cur

    def cls(self):
        start = self.i
        tok = self.peek()
        if tok == ';':
            self.eat(); A = self.cls(); B = self.cls()
            return Node('dec', [A, B], self.t[start:self.i])
        if tok in ('-u', '~P'):
            self.eat(); A = self.cls()
            return Node('neg' if tok == '-u' else 'pw', [A], self.t[start:self.i])
        if tok in ('prod_', 'sum_'):
            self.eat(); x = self.eat(); self.eat('e.'); A = self.cls(); B = self.cls()
            return Node('prod' if tok == 'prod_' else 'sum', [A, B], self.t[start:self.i], bound=(x,))
        if tok == 'seq':
            self.eat(); M = self.cls(); self.eat('('); PL = self.cls(); self.eat(','); F = self.cls(); self.eat(')')
            return Node('seq', [M, PL, F], self.t[start:self.i])
        if tok == '{' and LOWVAR.match(self.peek(1) or '') and self.peek(2) == 'e.':
            self.eat('{'); x = self.eat(); self.eat('e.'); A = self.cls(); self.eat('|'); ph = self.wff(); self.eat('}')
            return Node('rab', [A, ph], self.t[start:self.i], bound=(x,))
        if tok == '(':
            self.eat('(')
            if LOWVAR.match(self.peek() or '') and self.peek(1) == 'e.':
                x = self.eat(); self.eat('e.'); A = self.cls()
                if self.peek() == ',':
                    self.eat(','); y = self.eat(); self.eat('e.'); B = self.cls(); self.eat('|->'); C = self.cls(); self.eat(')')
                    return Node('mpo', [A, B, C], self.t[start:self.i], bound=(x, y))
                self.eat('|->'); B = self.cls(); self.eat(')')
                return Node('mpt', [A, B], self.t[start:self.i], bound=(x,))
            A = self.cls()
            if self.peek() == '`':
                self.eat('`'); B = self.cls(); self.eat(')')
                return Node('fv', [A, B], self.t[start:self.i])
            op = self.peek()
            if op in INFIX_SPECIAL:
                self.eat(); B = self.cls(); self.eat(')')
                return Node('in:' + op, [A, B], self.t[start:self.i])
            F = self.cls(); B = self.cls(); self.eat(')')
            return Node('ov', [A, F, B], self.t[start:self.i])
        if tok == '<.':
            self.eat(); A = self.cls(); self.eat(','); B = self.cls()
            if self.peek() == ',':
                self.eat(','); C = self.cls(); self.eat('>.')
                return Node('ot', [A, B, C], self.t[start:self.i])
            self.eat('>.')
            return Node('op', [A, B], self.t[start:self.i])
        if tok == '{':
            self.eat()
            if self.peek() == '<.' and self.peek(2) == ',' and self.peek(4) == '>.' and self.peek(5) == '|':
                self.eat('<.'); x = self.eat(); self.eat(','); y = self.eat(); self.eat('>.'); self.eat('|'); ph = self.wff(); self.eat('}')
                return Node('opab', [ph], self.t[start:self.i], bound=(x, y))
            if LOWVAR.match(self.peek() or '') and self.peek(1) == '|':
                x = self.eat(); self.eat('|'); ph = self.wff(); self.eat('}')
                return Node('ab', [ph], self.t[start:self.i], bound=(x,))
            A = self.cls()
            if self.peek() == ',':
                self.eat(','); B = self.cls()
                if self.peek() == ',':
                    self.eat(','); C = self.cls(); self.eat('}')
                    return Node('tp', [A, B, C], self.t[start:self.i])
                self.eat('}')
                return Node('pr', [A, B], self.t[start:self.i])
            self.eat('}')
            return Node('sn', [A], self.t[start:self.i])
        if tok == 'if':
            self.eat(); self.eat('('); ph = self.wff(); self.eat(','); A = self.cls(); self.eat(','); B = self.cls(); self.eat(')')
            return Node('if', [ph, A, B], self.t[start:self.i])
        if tok in ('U_', 'X_'):
            self.eat(); x = self.eat(); self.eat('e.'); A = self.cls(); B = self.cls()
            return Node('iun' if tok == 'U_' else 'ixp', [A, B], self.t[start:self.i], bound=(x,))
        if tok in ('Word', 'dom', 'ran', 'U.', 'suc', "`'"):
            self.eat(); A = self.cls()
            return Node({'Word': 'word', 'dom': 'dom', 'ran': 'ran', 'U.': 'uni', 'suc': 'suc', "`'": 'cnv'}[tok], [A], self.t[start:self.i])
        if tok == 'rec':
            self.eat(); self.eat('('); F = self.cls(); self.eat(','); A = self.cls(); self.eat(')')
            return Node('rec', [F, A], self.t[start:self.i])
        if tok == '<"':
            self.eat(); A = self.cls(); self.eat('">')
            return Node('s1', [A], self.t[start:self.i])
        self.eat()
        return Node('atom', [], self.t[start:self.i])

    # relation tokens that separate two classes in an atomic wff
    BR = ('<_', '<', '||', 'InWindow', 'TM2CompT', '~~>r', 'gcd', 'ppi')

    def wff(self):
        start = self.i
        # an atomic wff first, so that a class in parentheses is never
        # mistaken for ( ph op ps )
        if self.peek() == '(':
            save = self.i
            try:
                A = self.cls()
                op = self.peek()
                if op in ('=', 'e.', '=/=', 'C_', 'Fn'):
                    self.eat(); B = self.cls()
                    return Node({'=': 'eq', 'e.': 'el', '=/=': 'ne', 'C_': 'ss', 'Fn': 'fn'}[op], [A, B], self.t[start:self.i])
                if op == ':':
                    self.eat(); B = self.cls(); arrow = self.eat(); C = self.cls()
                    return Node({'-->': 'f', '-1-1-onto->': 'f1o', '-1-1->': 'f1', '-onto->': 'fo'}[arrow], [A, B, C], self.t[start:self.i])
                if op in self.BR:
                    self.eat(); B = self.cls()
                    return Node('br', [A, Node('atom', [], [op]), B], self.t[start:self.i])
            except (SyntaxError, KeyError, IndexError):
                pass
            self.i = save
        if self.peek() in ('E.', 'A.') and self.peek(2) == 'e.':
            qtok = self.eat(); x = self.eat(); self.eat('e.'); A = self.cls(); ph = self.wff()
            return Node('rex' if qtok == 'E.' else 'ral', [A, ph], self.t[start:self.i], bound=(x,))
        if self.peek() == '-.':
            self.eat(); ph = self.wff()
            return Node('not', [ph], self.t[start:self.i])
        if self.peek() == 'Fun':
            self.eat(); A = self.cls()
            return Node('fun', [A], self.t[start:self.i])
        if self.peek() == '(':
            # ( ph /\ ps ) or ( A = B ) is not a wff form; wffs in ifs are A = B
            save = self.i
            try:
                self.eat('('); ph = self.wff(); op = self.eat(); ps = self.wff()
                if op in ('/\\', '\\/') and self.peek() == op:
                    self.eat(op); ch = self.wff(); self.eat(')')
                    return Node({'/\\': '3an', '\\/': '3or'}[op], [ph, ps, ch], self.t[start:self.i])
                self.eat(')')
                return Node({'/\\': 'and', '\\/': 'or', '->': 'imp', '<->': 'bi'}[op], [ph, ps], self.t[start:self.i])
            except (SyntaxError, KeyError, IndexError):
                self.i = save
        A = self.cls()
        op = self.peek()
        if op in ('=', 'e.', '=/=', 'C_', 'Fn'):
            self.eat(); B = self.cls()
            return Node({'=': 'eq', 'e.': 'el', '=/=': 'ne', 'C_': 'ss', 'Fn': 'fn'}[op], [A, B], self.t[start:self.i])
        if op == ':':
            self.eat(); B = self.cls(); arrow = self.eat(); C = self.cls()
            return Node({'-->': 'f', '-1-1-onto->': 'f1o', '-1-1->': 'f1', '-onto->': 'fo'}[arrow], [A, B, C], self.t[start:self.i])
        R = self.cls(); B = self.cls()
        return Node('br', [A, R, B], self.t[start:self.i])


def parse(s):
    p = Parser(tokenize(s))
    n = p.cls()
    if p.i != len(p.t):
        raise SyntaxError('trailing tokens: %s' % ' '.join(p.t[p.i:]))
    return n


def parse_wff(s):
    p = Parser(tokenize(s))
    n = p.wff()
    if p.i != len(p.t):
        raise SyntaxError('trailing tokens: %s' % ' '.join(p.t[p.i:]))
    return n


def subst_toks(toks, sub, bound=()):
    """Substitute set variables by token lists (no capture handling beyond
    skipping variables bound at the top; callers keep substituted variables
    distinct from bound ones)."""
    out = []
    for t in toks:
        if t in sub and t not in bound:
            out.extend(sub[t].split())
        else:
            out.append(t)
    return out


class StepGen:
    def __init__(self, prefix='c'):
        self.n = 0
        self.prefix = prefix
        self.lines = []

    def fresh(self):
        self.n += 1
        return '%s%d' % (self.prefix, self.n)

    def step(self, hyps, ref, formula, name=None):
        name = name or self.fresh()
        self.lines.append('%s:%s:%s |- %s' % (name, ','.join(hyps), ref, formula))
        return name


def occurs(var, text):
    return re.search(r'(^|\s)%s(\s|$)' % re.escape(var), text) is not None


def closed_route(node, sub, ante, leaves, gen, bound, rules):
    """The congruence of a binder node whose bound variable occurs in ANTE.
    Every such set.mm lemma has `$d`, so the congruence is proved under the
    closed antecedent E, the conjunction of the substitutions it uses
    (`( x = X )`, or `( ( x = X ) /\\ ( y = Y ) )`), whose leaves are `id` /
    `simpl` / `simp1`, and carried back to ANTE with one `syl`.  Returns
    (step, new_toks), or None when the route does not apply."""
    used = sorted(v for v in node.free() & set(sub))
    if not used or len(used) > 3:
        return None
    if rules and any(k in node.text() for k in rules):
        return None
    eqs = ['%s = %s' % (v, sub[v]) for v in used]
    E = eqs[0] if len(eqs) == 1 else '( %s )' % (' /\\ '.join(eqs))
    for v in node.bound:
        if occurs(v, E):
            return None
    if len(used) == 1:
        refs = ['id']
    elif len(used) == 2:
        refs = ['simpl', 'simpr']
    else:
        refs = ['simp1', 'simp2', 'simp3']
    lv = dict(leaves)
    for v, ref in zip(used, refs):
        lv[v] = gen.step([], ref, '( %s -> %s = %s )' % (E, v, sub[v]))
    st, nt = congr(node, sub, E, lv, gen, bound, None)
    if st is None:
        return None
    old = node.text(); nw = ' '.join(nt)
    concl = ('( %s <-> %s )' % (old, nw)) if node.kind in ('ral', 'rex') else ('%s = %s' % (old, nw))
    f = '( %s -> %s )' % (ante, concl)
    if len(used) == 1:
        return gen.step([leaves[used[0]], st], 'syl', f), nt
    ref = 'jca' if len(used) == 2 else '3jca'
    j = gen.step([leaves[v] for v in used], ref, '( %s -> %s )' % (ante, E))
    return gen.step([j, st], 'syl', f), nt


def congr(node, sub, ante, leaves, gen, bound=(), rules=None):
    """Return (stepname or None, new_toks). None means the subterm is unchanged.
    rules: {subterm text: (new text, step name proving ante -> old = new)}."""
    if rules and node.text() in rules:
        nt, st = rules[node.text()]
        return st, nt.split()
    fr = node.free()
    if not rules and not (fr & set(sub)):
        return None, node.toks
    if node.kind in DV_KINDS and any(occurs(v, ante) for v in node.bound):
        got = closed_route(node, sub, ante, leaves, gen, bound, rules)
        if got is not None:
            return got
    if node.kind == 'atom':
        v = node.toks[0]
        if v in sub:
            return leaves[v], sub[v].split()
        return None, node.toks
    kids = []
    for k in node.kids:
        s, nt = congr(k, sub, ante, leaves, gen, bound + tuple(node.bound), rules)
        kids.append((s, nt, k))
    changed = [i for i, (s, _, _) in enumerate(kids) if s is not None]
    if not changed:
        return None, node.toks
    new = list(node.toks)
    K = node.kind
    # rebuild new token list
    if K == 'ov':
        new = ['('] + kids[0][1] + kids[1][1] + kids[2][1] + [')']
    elif K == 'fv':
        new = ['('] + kids[0][1] + ['`'] + kids[1][1] + [')']
    elif K.startswith('in:'):
        new = ['('] + kids[0][1] + [K[3:]] + kids[1][1] + [')']
    elif K == 'op':
        new = ['<.'] + kids[0][1] + [','] + kids[1][1] + ['>.']
    elif K == 'ot':
        new = ['<.'] + kids[0][1] + [','] + kids[1][1] + [','] + kids[2][1] + ['>.']
    elif K == 'sn':
        new = ['{'] + kids[0][1] + ['}']
    elif K == 'pr':
        new = ['{'] + kids[0][1] + [','] + kids[1][1] + ['}']
    elif K == 'tp':
        new = ['{'] + kids[0][1] + [','] + kids[1][1] + [','] + kids[2][1] + ['}']
    elif K == 'opab':
        new = ['{', '<.', node.bound[0], ',', node.bound[1], '>.', '|'] + kids[0][1] + ['}']
    elif K == 'ab':
        new = ['{', node.bound[0], '|'] + kids[0][1] + ['}']
    elif K == 'if':
        new = ['if', '('] + kids[0][1] + [','] + kids[1][1] + [','] + kids[2][1] + [')']
    elif K in ('eq', 'el', 'ne', 'ss', 'fn'):
        new = kids[0][1] + [{'eq': '=', 'el': 'e.', 'ne': '=/=', 'ss': 'C_', 'fn': 'Fn'}[K]] + kids[1][1]
    elif K in ('and', 'or', 'imp', 'bi'):
        new = ['('] + kids[0][1] + [{'and': '/\\', 'or': '\\/', 'imp': '->', 'bi': '<->'}[K]] + kids[1][1] + [')']
    elif K == 'not':
        new = ['-.'] + kids[0][1]
    elif K in ('3an', '3or'):
        o = {'3an': '/\\', '3or': '\\/'}[K]
        new = ['('] + kids[0][1] + [o] + kids[1][1] + [o] + kids[2][1] + [')']
    elif K == 'fun':
        new = ['Fun'] + kids[0][1]
    elif K in ('f', 'f1o', 'f1', 'fo'):
        new = kids[0][1] + [':'] + kids[1][1] + [{'f': '-->', 'f1o': '-1-1-onto->', 'f1': '-1-1->', 'fo': '-onto->'}[K]] + kids[2][1]
    elif K == 'br':
        new = kids[0][1] + kids[1][1] + kids[2][1]
    elif K in ('rex', 'ral'):
        new = [node.toks[0], node.bound[0], 'e.'] + kids[0][1] + kids[1][1]
    elif K in ('iun', 'ixp'):
        new = [node.toks[0], node.bound[0], 'e.'] + kids[0][1] + kids[1][1]
    elif K in ('word', 'dom', 'ran', 'uni', 'suc', 'cnv'):
        new = [node.toks[0]] + kids[0][1]
    elif K == 'rec':
        new = ['rec', '('] + kids[0][1] + [','] + kids[1][1] + [')']
    elif K == 's1':
        new = ['<"'] + kids[0][1] + ['">']
    elif K == 'mpt':
        new = ['(', node.bound[0], 'e.'] + kids[0][1] + ['|->'] + kids[1][1] + [')']
    elif K == 'mpo':
        new = ['(', node.bound[0], 'e.'] + kids[0][1] + [',', node.bound[1], 'e.'] + kids[1][1] + ['|->'] + kids[2][1] + [')']
    elif K == 'dec':
        new = [';'] + kids[0][1] + kids[1][1]
    elif K in ('neg', 'pw'):
        new = [node.toks[0]] + kids[0][1]
    elif K in ('prod', 'sum'):
        new = [node.toks[0], node.bound[0], 'e.'] + kids[0][1] + kids[1][1]
    elif K == 'rab':
        new = ['{', node.bound[0], 'e.'] + kids[0][1] + ['|'] + kids[1][1] + ['}']
    elif K == 'seq':
        new = ['seq'] + kids[0][1] + ['('] + kids[1][1] + [','] + kids[2][1] + [')']
    else:
        raise NotImplementedError(K)
    old = ' '.join(node.toks)
    nw = ' '.join(new)
    rel = '<->' if K in ('eq', 'el', 'ne', 'ss', 'fn', 'not', 'and', 'or', 'imp', 'bi', 'rex', 'ral', 'fun', 'f', 'f1o', 'f1', 'fo', 'br', '3an', '3or') else '='
    f = '( %s -> ( %s %s %s ) )' % (ante, old, rel, nw) if rel == '<->' else '( %s -> %s = %s )' % (ante, old, nw)

    def hyp(i):
        return kids[i][0]

    def idd(i):
        return gen.step([], 'eqidd', '( %s -> %s = %s )' % (ante, kids[i][2].text(), kids[i][2].text()))

    def two(names, i1, i2):
        if changed == [i1]:
            return gen.step([hyp(i1)], names[0], f)
        if changed == [i2]:
            return gen.step([hyp(i2)], names[1], f)
        return gen.step([hyp(i1), hyp(i2)], names[2], f)

    def twodv(names, i1, i2):
        lemma = names[0] if changed == [i1] else (names[1] if changed == [i2] else names[2])
        if lemma in DV_LEMMAS:
            for v in node.bound:
                dvcheck(ante, v, lemma)
        return two(names, i1, i2)

    if K == 'ov':
        if 1 not in changed:
            return two(('oveq1d', 'oveq2d', 'oveq12d'), 0, 2), new
        if changed == [1]:
            return gen.step([hyp(1)], 'oveqd', f), new
        hs = [hyp(i) if hyp(i) else idd(i) for i in range(3)]
        return gen.step(hs, 'oveq123d', f), new
    if K == 'fv':
        return two(('fveq1d', 'fveq2d', 'fveq12d'), 0, 1), new
    if K.startswith('in:'):
        names = INFIX_SPECIAL[K[3:]]
        if names[0].endswith('*'):
            # closed lemmas djueq1/djueq2/djueq12 via syl / syl2anc
            if changed == [0]:
                inst = gen.step([], 'djueq1', '( %s = %s -> %s = %s )' % (kids[0][2].text(), ' '.join(kids[0][1]), old, nw))
                return gen.step([hyp(0), inst], 'syl', f), new
            if changed == [1]:
                inst = gen.step([], 'djueq2', '( %s = %s -> %s = %s )' % (kids[1][2].text(), ' '.join(kids[1][1]), old, nw))
                return gen.step([hyp(1), inst], 'syl', f), new
            inst = gen.step([], 'djueq12', '( ( %s = %s /\\ %s = %s ) -> %s = %s )' % (kids[0][2].text(), ' '.join(kids[0][1]), kids[1][2].text(), ' '.join(kids[1][1]), old, nw))
            return gen.step([hyp(0), hyp(1), inst], 'syl2anc', f), new
        return two(names, 0, 1), new
    if K == 'op':
        return two(('opeq1d', 'opeq2d', 'opeq12d'), 0, 1), new
    if K == 'ot':
        if len(changed) == 1:
            return gen.step([hyp(changed[0])], ['oteq1d', 'oteq2d', 'oteq3d'][changed[0]], f), new
        hs = [hyp(i) if hyp(i) else idd(i) for i in range(3)]
        return gen.step(hs, 'oteq123d', f), new
    if K == 'sn':
        return gen.step([hyp(0)], 'sneqd', f), new
    if K == 'pr':
        return two(('preq1d', 'preq2d', 'preq12d'), 0, 1), new
    if K == 'tp':
        if len(changed) == 1:
            return gen.step([hyp(changed[0])], ['tpeq1d', 'tpeq2d', 'tpeq3d'][changed[0]], f), new
        hs = [hyp(i) if hyp(i) else idd(i) for i in range(3)]
        return gen.step(hs, 'tpeq123d', f), new
    if K == 'opab':
        return gen.step([hyp(0)], 'opabbidv', f), new
    if K == 'ab':
        return gen.step([hyp(0)], 'abbidv', f), new
    if K == 'if':
        if 0 not in changed:
            return two(('ifeq1d', 'ifeq2d', 'ifeq12d'), 1, 2), new
        if changed == [0]:
            return gen.step([hyp(0)], 'ifbid', f), new
        if changed == [0, 1]:
            return gen.step([hyp(0), hyp(1)], 'ifbieq1d', f), new
        if changed == [0, 2]:
            return gen.step([hyp(0), hyp(2)], 'ifbieq2d', f), new
        return gen.step([hyp(0), hyp(1), hyp(2)], 'ifbieq12d', f), new
    if K == 'eq':
        return two(('eqeq1d', 'eqeq2d', 'eqeq12d'), 0, 1), new
    if K == 'el':
        return two(('eleq1d', 'eleq2d', 'eleq12d'), 0, 1), new
    if K == 'ne':
        return two(('neeq1d', 'neeq2d', 'neeq12d'), 0, 1), new
    if K == 'ss':
        return two(('sseq1d', 'sseq2d', 'sseq12d'), 0, 1), new
    if K == 'fn':
        return two(('fneq1d', 'fneq2d', 'fneq12d'), 0, 1), new
    if K == 'and':
        return two(('anbi1d', 'anbi2d', 'anbi12d'), 0, 1), new
    if K == 'or':
        return two(('orbi1d', 'orbi2d', 'orbi12d'), 0, 1), new
    if K == 'imp':
        return two(('imbi1d', 'imbi2d', 'imbi12d'), 0, 1), new
    if K == 'bi':
        return two(('bibi1d', 'bibi2d', 'bibi12d'), 0, 1), new
    if K == 'not':
        return gen.step([hyp(0)], 'notbid', f), new
    if K in ('3an', '3or'):
        pre = '3anbi' if K == '3an' else '3orbi'
        if len(changed) == 1 and K == '3an':
            return gen.step([hyp(changed[0])], pre + ['1d', '2d', '3d'][changed[0]], f), new
        hs = [hyp(i) if hyp(i) else gen.step([], 'biidd', '( %s -> ( %s <-> %s ) )' % (ante, kids[i][2].text(), kids[i][2].text())) for i in range(3)]
        return gen.step(hs, pre + '123d', f), new
    if K == 'fun':
        return gen.step([hyp(0)], 'funeqd', f), new
    if K in ('f', 'f1o'):
        pre = 'feq' if K == 'f' else 'f1oeq'
        if len(changed) == 1:
            return gen.step([hyp(changed[0])], pre + ['1d', '2d', '3d'][changed[0]], f), new
        if changed == [0, 1] and K == 'f':
            return gen.step([hyp(0), hyp(1)], pre + '12d', f), new
        hs = [hyp(i) if hyp(i) else idd(i) for i in range(3)]
        return gen.step(hs, pre + '123d', f), new
    if K == 'br':
        if changed == [1]:
            return gen.step([hyp(1)], 'breqd', f), new
        if 1 not in changed:
            return two(('breq1d', 'breq2d', 'breq12d'), 0, 2), new
        hs = [hyp(i) if hyp(i) else idd(i) for i in range(3)]
        return gen.step(hs, 'breq123d', f), new
    if K == 'rex':
        return twodv(('rexeqdv', 'rexbidv', 'rexeqbidv'), 0, 1), new
    if K == 'ral':
        return twodv(('raleqdv', 'ralbidv', 'raleqbidv'), 0, 1), new
    if K == 'iun':
        return two(('iuneq1d', 'iuneq2d', 'iuneq12d'), 0, 1), new
    if K == 'ixp':
        return twodv(('ixpeq1d', 'ixpeq2dv', 'ixpeq12dv'), 0, 1), new
    if K == 'word':
        inst = gen.step([], 'wrdeq', '( %s = %s -> %s = %s )' % (kids[0][2].text(), ' '.join(kids[0][1]), old, nw))
        return gen.step([hyp(0), inst], 'syl', f), new
    if K in ('dom', 'ran', 'uni', 'suc', 'cnv'):
        return gen.step([hyp(0)], {'dom': 'dmeqd', 'ran': 'rneqd', 'uni': 'unieqd', 'suc': 'suceqd', 'cnv': 'cnveqd'}[K], f), new
    if K == 'rec':
        if changed == [0]:
            inst = gen.step([], 'rdgeq1', '( %s = %s -> %s = %s )' % (kids[0][2].text(), ' '.join(kids[0][1]), old, nw))
            return gen.step([hyp(0), inst], 'syl', f), new
        if changed == [1]:
            inst = gen.step([], 'rdgeq2', '( %s = %s -> %s = %s )' % (kids[1][2].text(), ' '.join(kids[1][1]), old, nw))
            return gen.step([hyp(1), inst], 'syl', f), new
        inst = gen.step([], 'rdgeq12', '( ( %s = %s /\\ %s = %s ) -> %s = %s )' % (kids[0][2].text(), ' '.join(kids[0][1]), kids[1][2].text(), ' '.join(kids[1][1]), old, nw))
        return gen.step([hyp(0), hyp(1), inst], 'syl2anc', f), new
    if K == 's1':
        return gen.step([hyp(0)], 's1eqd', f), new
    if K == 'mpt':
        return twodv(('mpteq1d', 'mpteq2dv', 'mpteq12dv'), 0, 1), new
    if K == 'mpo':
        if changed == [2]:
            dvcheck(ante, node.bound[0], 'mpoeq3dv'); dvcheck(ante, node.bound[1], 'mpoeq3dv')
            return gen.step([hyp(2)], 'mpoeq3dv', f), new
        hs = [hyp(i) if hyp(i) else idd(i) for i in range(3)]
        return gen.step(hs, 'mpoeq123dv', f), new
    if K == 'dec':
        raise NotImplementedError('congruence inside a decimal numeral')
    if K in ('neg', 'pw'):
        return gen.step([hyp(0)], 'negeqd' if K == 'neg' else 'pweqd', f), new
    if K in ('prod', 'sum'):
        # the body hypothesis of prodeq2dv / sumeq2dv is under the extended
        # antecedent ( ph /\ k e. A ), which is not what the recursion proves:
        # a body-only change takes the `s` variant, and a change to both the
        # range and the body lifts the body hypothesis with adantr, because
        # prodeq12dv / sumeq12dv have no `s` variant.
        names = (('prodeq1d', 'prodeq2sdv', 'prodeq12dv') if K == 'prod'
                 else ('sumeq1d', 'sumeq2sdv', 'sumeq12dv'))
        k = node.bound[0]
        if changed == [0]:
            return gen.step([hyp(0)], names[0], f), new
        if changed == [1]:
            dvcheck(ante, k, names[1])
            return gen.step([hyp(1)], names[1], f), new
        dvcheck(ante, k, names[2])
        rng = kids[0][2].text()
        b = gen.step([hyp(1)], 'adantr', '( ( %s /\\ %s e. %s ) -> %s = %s )'
                     % (ante, k, rng, kids[1][2].text(), ' '.join(kids[1][1])))
        return gen.step([hyp(0), b], names[2], f), new
    if K == 'rab':
        return twodv(('rabeqdv', 'rabbidv', 'rabeqbidv'), 0, 1), new
    if K == 'seq':
        if len(changed) == 1:
            return gen.step([hyp(changed[0])], 'seqeq%dd' % (changed[0] + 1), f), new
        hs = [hyp(i) if hyp(i) else idd(i) for i in range(3)]
        return gen.step(hs, 'seqeq123d', f), new
    raise NotImplementedError(K)


def congruence(expr, sub, ante, leaves, gen, rules=None):
    """expr: class expression string; sub: {var: replacement string};
    ante: antecedent wff string; leaves: {var: step name proving ante -> var = repl};
    rules: {old subterm text: (new text, step name)} rewrites applied at exact matches.
    Returns (final step name, new expression string)."""
    node = parse(expr)
    s, nt = congr(node, sub, ante, leaves, gen, rules=rules)
    return s, ' '.join(nt)


def wff_congruence(expr, sub, ante, leaves, gen, rules=None):
    node = parse_wff(expr)
    s, nt = congr(node, sub, ante, leaves, gen, rules=rules)
    return s, ' '.join(nt)


def _vexd(w, ante, val, closure=None, exs=None):
    """a step proving ( ante -> VAL e. _V )"""
    if exs is not None:
        return exs
    if closure is not None:
        return closure.mem(val, '_V')
    k = parse(val).kind
    if k == 'ov':
        return w.s([], 'ovexd', '( %s -> %s e. _V )' % (ante, val))
    if k == 'fv':
        return w.s([], 'fvexd', '( %s -> %s e. _V )' % (ante, val))
    raise NotImplementedError('pass exs= or closure=: no _V route for ' + val)


def mptval(w, ante, x, X, body, T, mem, mp=None, exs=None, closure=None,
           rules=None, name=None, gen=None):
    """The value of a mapping at an argument:

        ( ante -> ( MP ` T ) = BODY[ x := T ] )   for   MP = ( x e. X |-> BODY )

    `mem` proves ( ante -> T e. X ); `mp` is the mapping's name when it is a
    defined class, and defaults to the mapping written out; `exs` proves
    ( ante -> value e. _V ) and is otherwise taken from `closure` or from
    `ovexd` / `fvexd`.  The substitution hypothesis ( x = T -> BODY = value )
    is written by `congruence`, so a body containing a nested mapping, a sum or
    an integral costs nothing extra; `rules` is passed to it.

    Returns (step, value).  This is C1's `$e`-family value generator, C2's
    `mptval` and C3's `mpv`, whose 25 call sites each wrote the substitution
    chain by hand."""
    mp = mp or '( %s e. %s |-> %s )' % (x, X, body)
    eq = '%s = %s' % (x, T)
    g = gen or StepGen('m')
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, val = congruence(body, {x: T}, eq, {x: idx}, g, rules=rules)
    w.lines.extend(g.lines); g.lines = []
    if st is None:
        st = w.s([], 'eqidd', '( %s -> %s = %s )' % (eq, body, val))
    dvcheck_sub('fvmptg', {'x': x, 'A': T, 'B': body, 'C': val, 'D': X})
    em = w.s([], 'eqid', '%s = %s' % (mp, mp))
    fm = w.s([st, em], 'fvmptg',
             '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (T, X, val, mp, T, val))
    ex = _vexd(w, ante, val, closure, exs)
    f = '( %s -> ( %s ` %s ) = %s )' % (ante, mp, T, val)
    if name == 'qed':
        w.qed([mem, ex, fm], 'syl2anc', f)
        return 'qed', val
    return w.s([mem, ex, fm], 'syl2anc', f, name=name), val


def dvcheck_sub(label, sub):
    """raise DVError when the distinct-variable conditions of LABEL forbid the
    texts this substitution puts into it (tools/dv.py).  Silent when the index
    is unavailable."""
    try:
        import dv as _dv
    except ImportError:
        return
    try:
        bad = _dv.check(label, sub)
    except Exception:
        return
    if bad:
        raise DVError('\n'.join(bad))


def rewrite(expr, rules, ante, gen):
    return congruence(expr, {}, ante, {}, gen, rules=rules)
