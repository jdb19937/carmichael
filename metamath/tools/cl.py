"""Closure and sign discharge for mmj2 worksheets (sortie G): the analogue
of Lean's `positivity` / `fun_prop` side-condition automation.

    from tm import W
    from cl import Closure, ClosureError
    w = W('label', 'description')
    ante = '( N e. NN /\\ X e. RR )'
    c = Closure(w, ante, {'N': ('NN', w.s([], 'simpl', '( %s -> N e. NN )' % ante)),
                          'X': ('RR', w.s([], 'simpr', '( %s -> X e. RR )' % ante))})
    st = c.mem('( ( N ^ 2 ) x. ( log ` N ) )', 'RR')   # step: ( ante -> ... e. RR )
    st = c.gt0('( ( exp ` X ) x. ( N + 1 ) )')          # step: ( ante -> 0 < ... )
    st = c.ge0(E); c.ne0(E); c.mem(E, 'NN0'); c.mem(E, 'Fin'); c.mem(W, 'Word 2o')

Leaves map an expression text to (kind, step) or to a list of them; a leaf
given as a bare step name has its kind read from the step's formula in the
worksheet.  Kinds: CC RR RR+ ZZ NN0 NN, `Word S`, Fin, and the sign facts
ge0 (`0 <_ E`), gt0 (`0 < E`), ne0 (`E =/= 0`), ge1 (`1 <_ E`), gt1
(`1 < E`).  Numeral literals need no leaves (tools/num.py proves them).

mem(E, T) tries, in order: a leaf; a literal; the structural rule table for
the head operator of E (`( A + B )`, `( A x. B )`, `( A - B )`, `-u A`,
`( A / B )`, `( A ^ N )`, `( log ` A )`, `( exp ` A )`, `( |_ ` A )`,
`( sqrt ` A )`, `( abs ` A )`, `( # ` A )`, `( ppi ` A )`,
`( encodeNat ` N )`, `( 2 logb A )`, `( M ... N )`, `( M ..^ N )`,
`( A X. B )`, `( M gcd N )`,
`sum_ k e. A B`, `prod_ k e. A B`, `( A ^c B )`, `( A mod B )`,
`( mmu ` A )`, `( phi ` A )`, `( Nceil ` A )`, `( Nfloor ` A )`,
`( B Nlog N )`, `if ( ph , A , B )` (both branches, `ifcld`),
`{ x e. A | ph }` (finite when A is), `E e. _V`); then upcasts
(NN -> NN0 -> ZZ -> RR -> CC, RR+ -> RR, RR /\\ 0 < E -> RR+).  `1 <_ E`
comes from NN, from `1 < E`, from `0 < E` for an integer (`zgt0ge1`), from
`expge1`, from `efle` at 0 for `( exp ` X )` with `0 <_ X`, and from a
product of two factors that are each at least 1.  Every result is memoized;
a failure raises ClosureError listing the facts that would unblock it, any
one of which the caller can supply as a leaf or through `have`.

`Closure.atom(E)` declares E atomic, so that tools/lin.py stops its
decomposition there; `Closure.leaf(E, kind, step)` records a fact and
declares E atomic at once.

`lift(w, step, to_ante)` lifts a step proved under any conjunct of an
antecedent to the whole antecedent, one `adantr` / `adantl` / `3adant*` per
level; `Closure.lift(step)` lifts to the closure's own antecedent.

Sums and products: the body is proved under the antecedent
`( ante /\\ k e. A )` by a child Closure whose leaf for `k` is derived from
`A` (`( 1 ... N )` -> NN, `( M ... N )` -> ZZ, `( 0 ... N )` -> NN0,
`( 0 ..^ N )` -> NN0, `( ZZ>= ` M )` -> ZZ, NN, NN0, ZZ, RR, RR+, Prime -> NN);
facts of the parent are lifted with `adantr`.  The bound variable must not
occur in `ante` (the `$d` hygiene of M2-HANDOFF.md).
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
import num

# the label the `0 <_ ( 2 logb X )` route cites.  set.mm's `logbge0b` is a
# mathbox theorem and the last one this module emits; `logb2ge0`
# (tools/gen/g4_logb.py) is our own main-body route to the half of it used
# here, and takes ( X e. RR+ /\ 1 <_ X ) directly.  The default is the mathbox
# label so that every stored worksheet reproduces character for character; the
# sortie that regenerates them sets
#     cl.LOGB_GE0 = 'logb2ge0'
# and the citation leaves MATHBOX_OK.
LOGB_GE0 = 'logbge0b'


class ClosureError(Exception):
    """message names the requirements that would unblock the proof; .blocked
    is the first of them and .wanted is the whole list"""
    def __init__(self, msg, blocked=None, wanted=()):
        Exception.__init__(self, msg)
        self.blocked = blocked or msg
        self.wanted = tuple(wanted) or ((self.blocked,) if self.blocked else ())


# ---------------------------------------------------------------- syntax

OPEN = {'(': ')', '<.': '>.', '{': '}', '<"': '">'}
CLOSE = {v: k for k, v in OPEN.items()}


def split_top(toks):
    """split a token list into balanced top-level pieces"""
    out, cur, depth = [], [], 0
    for t in toks:
        cur.append(t)
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
        if depth == 0:
            out.append(' '.join(cur)); cur = []
    if cur:
        raise SyntaxError('unbalanced: ' + ' '.join(toks))
    return _glue(out)


# prefix heads that absorb a fixed number of following top-level pieces:
# `-u A`, `; A B` (decimal), `if ( ph , A , B )`, and the four binder forms
# `sum_ k e. A B`, `prod_ k e. A B`, `U_ k e. A B`, `X_ k e. A B` (the
# binder contributes the pieces `k`, `e.`, the range and the body).
PREFIX_ARITY = {'-u': 1, ';': 2, 'if': 1, 'sum_': 4, 'prod_': 4, 'U_': 4, 'X_': 4}


def _glue(pieces):
    """glue each prefix head of PREFIX_ARITY to its operands, so that a term
    such as `sum_ k e. ( 1 ... N ) ( 1 / k )` is one top-level piece"""
    out = []; i = 0
    while i < len(pieces):
        p = pieces[i]
        n = PREFIX_ARITY.get(p)
        if n is not None:
            rest = _glue(pieces[i + 1:])
            if len(rest) >= n:
                out.append(' '.join([p] + rest[:n])); out.extend(rest[n:]); return out
        out.append(p); i += 1
    return out


def split_sep(toks, seps):
    """split a token list at its top-level occurrences of any token in seps"""
    out, cur, depth = [], [], 0
    for t in toks:
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
        if depth == 0 and t in seps:
            out.append(' '.join(cur)); cur = []
        else:
            cur.append(t)
    out.append(' '.join(cur))
    return out


INFIX = {'+': 'add', 'x.': 'mul', '-': 'sub', '/': 'div', '^': 'exp', '^c': 'cxp',
         '...': 'fz', '..^': 'fzo', 'logb': 'logb', 'mod': 'mod',
         'X.': 'xp', 'gcd': 'gcd'}
SIGNS = ('ge0', 'gt0', 'ne0', 'ge1', 'gt1')

# how many unsatisfied requirements a ClosureError lists before it counts
MAX_WANTED = 8


LOWVAR = re.compile(r'^[a-z]$')


def head(text):
    """('lit', text) | ('atom', text) | ('add'|'mul'|..., A, B) | ('neg', A)
    | ('fv', F, X) | ('ov', A, F, B) | ('sum'|'prod', k, A, B)
    | ('if', ph, A, B) | ('rab', x, A, ph) | ('other', text)"""
    if num.is_lit(text):
        return ('lit', text)
    toks = text.split()
    if len(toks) == 1:
        return ('atom', text)
    if toks[0] == '-u':
        return ('neg', ' '.join(toks[1:]))
    if toks[0] in ('sum_', 'prod_') and toks[2] == 'e.':
        rest = split_top(toks[3:])
        if len(rest) == 2:
            return ('sum' if toks[0] == 'sum_' else 'prod', toks[1], rest[0], rest[1])
    if toks[0] == 'if' and len(toks) > 2 and toks[1] == '(' and toks[-1] == ')':
        parts = split_sep(toks[2:-1], (',',))
        if len(parts) == 3:
            return ('if', parts[0], parts[1], parts[2])
    if toks[0] == '{' and toks[-1] == '}' and len(toks) > 4 and LOWVAR.match(toks[1]) and toks[2] == 'e.':
        parts = split_sep(toks[3:-1], ('|',))
        if len(parts) == 2:
            return ('rab', toks[1], parts[0], parts[1])
    if toks[0] == '(' and toks[-1] == ')':
        try:
            parts = split_top(toks[1:-1])
        except SyntaxError:
            return ('other', text)
        if len(parts) == 3:
            if parts[1] == '`':
                return ('fv', parts[0], parts[2])
            if parts[1] in INFIX:
                return (INFIX[parts[1]], parts[0], parts[2])
            return ('ov', parts[0], parts[1], parts[2])
    return ('other', text)


def hargs(h):
    """the class arguments of a head tuple, in the order rules index them"""
    k = h[0]
    if k == 'fv':
        return [h[2]]
    if k == 'ov':
        return [h[1], h[3]]
    if k == 'rab':
        return [h[2]]
    if k in ('sum', 'prod'):
        return [h[2], h[3]]
    if k == 'if':
        return [h[1], h[2], h[3]]
    return list(h[1:])


def headkey(h):
    """the rule-table key of a head tuple"""
    if h[0] == 'fv':
        return 'fv:' + h[1]
    if h[0] == 'ov':
        return 'ov:' + h[2]
    return h[0]


# ---------------------------------------------------------------- rules
# rule = (lemma, form, requirements); form 'd': deduction lemma whose $e
# hypotheses are the requirements in order; 'c': closed implication whose
# antecedent is the conjunction of the requirements (syl / syl2anc /
# syl3anc); 'a': closed theorem without hypotheses, lifted by a1i.
# requirement = (kind, argument index) with kind a membership target or a
# sign fact, or ('closed', callable(w) -> step) for a closed fact.

MEM_RULES = {
    ('add', 'CC'): [('addcld', 'd', [('CC', 0), ('CC', 1)])],
    ('add', 'RR'): [('readdcld', 'd', [('RR', 0), ('RR', 1)])],
    ('add', 'ZZ'): [('zaddcld', 'd', [('ZZ', 0), ('ZZ', 1)])],
    ('add', 'NN0'): [('nn0addcld', 'd', [('NN0', 0), ('NN0', 1)])],
    ('add', 'NN'): [('nnaddcld', 'd', [('NN', 0), ('NN', 1)]),
                    ('nn0nnaddcl', 'c', [('NN0', 0), ('NN', 1)])],
    ('add', 'RR+'): [('rpaddcld', 'd', [('RR+', 0), ('RR+', 1)])],
    ('mul', 'CC'): [('mulcld', 'd', [('CC', 0), ('CC', 1)])],
    ('mul', 'RR'): [('remulcld', 'd', [('RR', 0), ('RR', 1)])],
    ('mul', 'ZZ'): [('zmulcld', 'd', [('ZZ', 0), ('ZZ', 1)])],
    ('mul', 'NN0'): [('nn0mulcld', 'd', [('NN0', 0), ('NN0', 1)])],
    ('mul', 'NN'): [('nnmulcld', 'd', [('NN', 0), ('NN', 1)])],
    ('mul', 'RR+'): [('rpmulcld', 'd', [('RR+', 0), ('RR+', 1)])],
    ('sub', 'CC'): [('subcld', 'd', [('CC', 0), ('CC', 1)])],
    ('sub', 'RR'): [('resubcld', 'd', [('RR', 0), ('RR', 1)])],
    ('sub', 'ZZ'): [('zsubcld', 'd', [('ZZ', 0), ('ZZ', 1)])],
    ('neg', 'CC'): [('negcld', 'd', [('CC', 0)])],
    ('neg', 'RR'): [('renegcld', 'd', [('RR', 0)])],
    ('neg', 'ZZ'): [('znegcld', 'd', [('ZZ', 0)])],
    ('div', 'CC'): [('divcld', 'd', [('CC', 0), ('CC', 1), ('ne0', 1)])],
    ('div', 'RR'): [('rerpdivcld', 'd', [('RR', 0), ('RR+', 1)]),
                    ('redivcld', 'd', [('RR', 0), ('RR', 1), ('ne0', 1)])],
    ('div', 'RR+'): [('rpdivcld', 'd', [('RR+', 0), ('RR+', 1)])],
    ('exp', 'CC'): [('expcld', 'd', [('CC', 0), ('NN0', 1)])],
    ('exp', 'RR'): [('reexpcld', 'd', [('RR', 0), ('NN0', 1)])],
    ('exp', 'RR+'): [('rpexpcld', 'd', [('RR+', 0), ('ZZ', 1)])],
    ('exp', 'NN0'): [('nn0expcld', 'd', [('NN0', 0), ('NN0', 1)])],
    ('exp', 'NN'): [('nnexpcld', 'd', [('NN', 0), ('NN0', 1)])],
    ('exp', 'ZZ'): [('zexpcld', 'd', [('ZZ', 0), ('NN0', 1)])],
    ('fv:log', 'RR'): [('relogcld', 'd', [('RR+', 0)])],
    ('fv:log', 'RR+'): [('rplogcl', 'c', [('RR', 0), ('gt1', 0)])],
    ('fv:exp', 'RR+'): [('rpefcld', 'd', [('RR', 0)])],
    ('fv:exp', 'RR'): [('reefcld', 'd', [('RR', 0)])],
    ('fv:exp', 'CC'): [('efcld', 'd', [('CC', 0)])],
    ('fv:|_', 'ZZ'): [('flcld', 'd', [('RR', 0)])],
    ('fv:|_', 'NN0'): [('flge0nn0', 'c', [('RR', 0), ('ge0', 0)])],
    ('fv:sqrt', 'RR'): [('resqrtcld', 'd', [('RR', 0), ('ge0', 0)])],
    ('fv:sqrt', 'RR+'): [('rpsqrtcld', 'd', [('RR+', 0)])],
    ('fv:abs', 'RR'): [('abscld', 'd', [('CC', 0)])],
    ('fv:#', 'NN0'): [('hashcl', 'c', [('Fin', 0)]), ('lencl', 'c', [('Word', 0)])],
    ('fv:ppi', 'NN0'): [('ppicl', 'c', [('RR', 0)])],
    ('fv:phi', 'NN'): [('phicld', 'd', [('NN', 0)])],
    ('fv:mmu', 'ZZ'): [('mucl', 'c', [('NN', 0)])],
    ('fv:Nceil', 'NN0'): [('nceilcl', 'c', [('RR', 0)])],
    ('fv:Nfloor', 'NN0'): [('nfloorcl', 'c', [('RR', 0)])],
    ('ov:Nlog', 'NN0'): [('nlogcl', 'c', [('NN0', 0), ('NN0', 1)])],
    ('cxp', 'CC'): [('cxpcld', 'd', [('CC', 0), ('CC', 1)])],
    ('cxp', 'RR'): [('recxpcld', 'd', [('RR', 0), ('ge0', 0), ('RR', 1)])],
    ('cxp', 'RR+'): [('rpcxpcld', 'd', [('RR+', 0), ('RR', 1)])],
    ('mod', 'RR'): [('modcld', 'd', [('RR', 0), ('RR+', 1)])],
    ('mod', 'NN0'): [('zmodcl', 'c', [('ZZ', 0), ('NN', 1)])],
    ('fv:encodeNat', 'Word 2o'): [('encnatcl', 'c', [('NN0', 0)])],
    ('xp', 'Fin'): [('xpfi', 'c', [('Fin', 0), ('Fin', 1)])],
    ('xp', '_V'): [('xpexg', 'c', [('_V', 0), ('_V', 1)])],
    ('gcd', 'NN0'): [('gcdcld', 'd', [('ZZ', 0), ('ZZ', 1)])],
    ('gcd', 'NN'): [('gcdnncl', 'c', [('NN', 0), ('NN', 1)])],
    ('fz', 'Fin'): [('fzfid', 'a0', [])],
    ('fzo', 'Fin'): [('fzofi', 'a', [])],
    ('sum', 'CC'): [('fsumcl', 's', [('Fin', 0), ('CC', 'body')])],
    ('sum', 'RR'): [('fsumrecl', 's', [('Fin', 0), ('RR', 'body')])],
    ('sum', 'NN0'): [('fsumnn0cl', 's', [('Fin', 0), ('NN0', 'body')])],
    ('prod', 'CC'): [('fprodcl', 's', [('Fin', 0), ('CC', 'body')])],
    ('prod', 'RR'): [('fprodrecl', 's', [('Fin', 0), ('RR', 'body')])],
    ('prod', 'NN'): [('fprodnncl', 's', [('Fin', 0), ('NN', 'body')])],
    ('prod', 'NN0'): [('fprodnn0cl', 's', [('Fin', 0), ('NN0', 'body')])],
    ('prod', 'RR+'): [('fprodrpcl', 's', [('Fin', 0), ('RR+', 'body')])],
}

SIGN_RULES = {
    ('add', 'ge0'): [('addge0d', 'd', [('RR', 0), ('RR', 1), ('ge0', 0), ('ge0', 1)])],
    ('add', 'gt0'): [('addgt0d', 'd', [('RR', 0), ('RR', 1), ('gt0', 0), ('gt0', 1)]),
                     ('addgegt0d', 'd', [('RR', 0), ('RR', 1), ('ge0', 0), ('gt0', 1)]),
                     ('addgtge0d', 'd', [('RR', 0), ('RR', 1), ('gt0', 0), ('ge0', 1)])],
    ('mul', 'ge0'): [('mulge0d', 'd', [('RR', 0), ('RR', 1), ('ge0', 0), ('ge0', 1)])],
    ('mul', 'gt0'): [('mulgt0d', 'd', [('RR', 0), ('RR', 1), ('gt0', 0), ('gt0', 1)])],
    ('div', 'ge0'): [('divge0d', 'd', [('RR', 0), ('RR+', 1), ('ge0', 0)])],
    ('div', 'gt0'): [('divgt0d', 'd', [('RR', 0), ('RR', 1), ('gt0', 0), ('gt0', 1)])],
    ('exp', 'ge0'): [('expge0d', 'd', [('RR', 0), ('NN0', 1), ('ge0', 0)])],
    ('exp', 'gt0'): [('expgt0', 'c', [('RR', 0), ('ZZ', 1), ('gt0', 0)])],
    ('fv:exp', 'gt0'): [('efgt0', 'c', [('RR', 0)])],
    ('fv:sqrt', 'ge0'): [('sqrtge0d', 'd', [('RR', 0), ('ge0', 0)])],
    ('fv:sqrt', 'gt0'): [('sqrtgt0d', 'd', [('RR+', 0)])],
    ('fv:abs', 'ge0'): [('absge0d', 'd', [('CC', 0)])],
    ('fv:log', 'ge0'): [('logge0', 'c', [('RR', 0), ('ge1', 0)])],
    ('sum', 'ge0'): [('fsumge0', 's', [('Fin', 0), ('RR', 'body'), ('ge0', 'body')])],
    ('exp', 'ge1'): [('expge1', 'c', [('RR', 0), ('NN0', 1), ('ge1', 0)])],
    ('fv:exp', 'gt1'): [('efgt1', 'c', [('RR+', 0)])],
}

# upcasts: target -> [(source kind, lemma)]; all deduction form
UPCAST = {
    'CC': [('RR', 'recnd'), ('NN0', 'nn0cnd'), ('ZZ', 'zcnd'), ('NN', 'nncnd'), ('RR+', 'rpcnd')],
    'RR': [('RR+', 'rpred'), ('ZZ', 'zred'), ('NN0', 'nn0red'), ('NN', 'nnred')],
    'ZZ': [('NN0', 'nn0zd'), ('NN', 'nnzd')],
    'NN0': [('NN', 'nnnn0d')],
    'RR+': [('NN', 'nnrpd')],
    'ge0': [('RR+', 'rpge0d'), ('NN0', 'nn0ge0d')],
    'gt0': [('RR+', 'rpgt0d'), ('NN', 'nngt0d')],
    'ne0': [('RR+', 'rpne0d'), ('NN', 'nnne0d')],
    'ge1': [('NN', 'nnge1d')],
}

# the leaf kind of a bound variable from its range
RANGE_KIND = {'NN': ('NN', None), 'NN0': ('NN0', None), 'ZZ': ('ZZ', None), 'RR': ('RR', None),
              'CC': ('CC', None), 'RR+': ('RR+', None), 'Prime': ('NN', 'prmnn')}


def range_kind(A):
    """(kind, lemma) giving what a bound variable ranging over A satisfies:
    the lemma takes `k e. A` to that fact, or is None when `k e. A` is the
    fact itself"""
    h = head(A)
    if h[0] == 'fz':
        if h[1] == '1':
            return 'NN', 'elfznn'
        if h[1] == '0':
            return 'NN0', 'elfznn0'
        return 'ZZ', 'elfzelz'
    if h[0] == 'fzo' and h[1] == '0':
        return 'NN0', 'elfzonn0'
    if h[0] == 'fv' and h[1] == 'ZZ>=':
        return 'ZZ', 'eluzelz'
    if h[0] == 'rab' and h[2] in RANGE_KIND and RANGE_KIND[h[2]][1] is None:
        return RANGE_KIND[h[2]][0], 'elrabi'
    if A in RANGE_KIND:
        return RANGE_KIND[A]
    return None, None

FORMULA = {'CC': '%s e. CC', 'RR': '%s e. RR', 'RR+': '%s e. RR+', 'ZZ': '%s e. ZZ', 'NN0': '%s e. NN0',
           'NN': '%s e. NN', 'Fin': '%s e. Fin', '_V': '%s e. _V', 'Prime': '%s e. Prime',
           'ge0': '0 <_ %s', 'gt0': '0 < %s', 'ne0': '%s =/= 0',
           'ge1': '1 <_ %s', 'gt1': '1 < %s'}


def fmt(kind, E):
    if kind.startswith('Word'):
        return '%s e. %s' % (E, kind)
    return FORMULA[kind] % E


def kind_of_formula(f):
    """('NN0', 'N') from `N e. NN0` etc. (inside the antecedent)"""
    m = re.match(r'^(.*) e\. (CC|RR\+|RR|ZZ|NN0|NN|Fin|_V|Prime|Word .*)$', f)
    if m:
        return m.group(2), m.group(1)
    m = re.match(r'^0 <_ (.*)$', f)
    if m:
        return 'ge0', m.group(1)
    m = re.match(r'^0 < (.*)$', f)
    if m:
        return 'gt0', m.group(1)
    m = re.match(r'^1 <_ (.*)$', f)
    if m:
        return 'ge1', m.group(1)
    m = re.match(r'^1 < (.*)$', f)
    if m:
        return 'gt1', m.group(1)
    m = re.match(r'^(.*) =/= 0$', f)
    if m:
        return 'ne0', m.group(1)
    return None


def formula_of(w, name):
    """the formula of worksheet step NAME.  An mmj2 `$e` hypothesis line is
    written `hN::label` but referred to as `N`, so both spellings match."""
    for l in w.lines:
        if l.startswith(name + ':') or l.startswith('h' + name + ':'):
            return ' '.join(l.split('|-', 1)[1].split())
    raise KeyError('no step ' + name)


def strip_ante(formula, ante):
    pre = '( %s -> ' % ante
    if formula.startswith(pre) and formula.endswith(' )'):
        return formula[len(pre):-2]
    raise ValueError('formula %r is not under antecedent %r' % (formula, ante))


def _conjuncts(a):
    """the two or three top-level conjuncts of an antecedent, or None"""
    toks = a.split()
    if len(toks) > 2 and toks[0] == '(' and toks[-1] == ')':
        try:
            parts = split_sep(toks[1:-1], ('/\\',))
        except SyntaxError:
            return None
        if len(parts) in (2, 3) and all(parts):
            return parts
    return None


def ante_path(frm, to):
    """the list of (lemma, antecedent) steps that lift a deduction from the
    antecedent FRM to the antecedent TO, or None if TO does not contain FRM
    as a conjunct at any depth"""
    frm = ' '.join(frm.split()); to = ' '.join(to.split())
    if frm == to:
        return []
    ps = _conjuncts(to)
    if ps is None:
        return None
    if len(ps) == 2:
        for i, lemma in ((0, 'adantr'), (1, 'adantl')):
            sub = ante_path(frm, ps[i])
            if sub is not None:
                return sub + [(lemma, to)]
        return None
    for i, lemma in ((0, '3adant1'), (1, '3adant2'), (2, '3adant3')):
        rest = [p for j, p in enumerate(ps) if j != i]
        sub = ante_path(frm, '( %s /\\ %s )' % (rest[0], rest[1]))
        if sub is not None:
            return sub + [(lemma, to)]
    return None


def split_imp(formula):
    """('A', 'P') from `( A -> P )`, or None"""
    toks = formula.split()
    if len(toks) > 2 and toks[0] == '(' and toks[-1] == ')':
        parts = split_sep(toks[1:-1], ('->',))
        if len(parts) == 2:
            return parts[0], parts[1]
    return None


def lift(w, step, to_ante, name=None):
    """Lift the worksheet step STEP, which proves `( A -> P )`, to
    `( TO_ANTE -> P )` for any antecedent that contains `A` as a conjunct at
    any nesting depth: one `adantr`/`adantl`/`3adant*` per level.  Returns
    the name of the final step (STEP itself when `A` is already TO_ANTE).
    `adantr` counts one level; this counts them all."""
    f = formula_of(w, step)
    sp = split_imp(f)
    if sp is None:
        raise ClosureError('step %s does not prove an implication: %s' % (step, f))
    frm, concl = sp
    path = ante_path(frm, to_ante)
    if path is None:
        raise ClosureError('antecedent %s is not a conjunct of %s' % (frm, to_ante))
    if not path:
        if name is not None and name != step:
            return w.s([step], 'id', '( %s -> %s )' % (to_ante, concl), name=name)
        return step
    cur = step
    for i, (lemma, ante) in enumerate(path):
        nm = name if i == len(path) - 1 else None
        cur = w.s([cur], lemma, '( %s -> %s )' % (ante, concl), name=nm)
    return cur


class Closure:
    def __init__(self, w, ante, leaves=None, parent=None, extra=None):
        self.w = w; self.ante = ante; self.parent = parent; self.extra = extra
        self.memo = {}; self.busy = set(); self.leaves = {}; self.atoms = set()
        for E, v in (leaves or {}).items():
            if isinstance(v, str):
                v = [v]
            if isinstance(v, tuple):
                v = [v]
            for item in v:
                if isinstance(item, str):
                    k = kind_of_formula(strip_ante(formula_of(w, item), ante))
                    if k is None:
                        raise ValueError('leaf step %s: unrecognised formula' % item)
                    kind, expr = k
                    if expr != E:
                        raise ValueError('leaf step %s proves a fact about %s, not %s' % (item, expr, E))
                    self.memo[(E, kind)] = item
                else:
                    kind, st = item
                    self.memo[(E, kind)] = st

    # -- public
    def mem(self, E, T):
        return self.prove(E, T)

    def ge0(self, E):
        return self.prove(E, 'ge0')

    def gt0(self, E):
        return self.prove(E, 'gt0')

    def ne0(self, E):
        return self.prove(E, 'ne0')

    def have(self, E, kind, step):
        """record an externally proved fact"""
        self.memo[(E, kind)] = step
        return step

    def atom(self, E):
        """declare E atomic: tools/lin.py stops its decomposition there, so
        neither the certificate search nor the closure sees a subterm of E.
        A leaf passed to the constructor is NOT atomic in this sense -- a
        caller who declares `( 4 x. C )` for its closure still wants the
        certificate to see the product -- so the declaration is explicit."""
        self.atoms.add(' '.join(E.split()))
        return E

    def leaf(self, E, kind, step):
        """record an externally proved fact and declare E atomic"""
        self.atom(E)
        return self.have(' '.join(E.split()), kind, step)

    def lift(self, step, name=None):
        """lift a step proved under a conjunct of this closure's antecedent
        to this closure's antecedent (tools/cl.py `lift`)"""
        return lift(self.w, step, self.ante, name=name)

    # -- core
    def prove(self, E, T):
        E = ' '.join(E.split())
        key = (E, T)
        if key in self.memo:
            return self.memo[key]
        if key in self.busy:
            # the fact itself is what would unblock the route that came back here
            raise ClosureError('cycle at %s : %s' % (E, T), fmt(T, E))
        self.busy.add(key)
        try:
            st = self._prove(E, T)
        finally:
            self.busy.discard(key)
        self.memo[key] = st
        return st

    def _step(self, hyps, ref, formula):
        return self.w.s(hyps, ref, '( %s -> %s )' % (self.ante, formula))

    def _prove(self, E, T):
        w = self.w
        failures = []
        # literal
        if num.is_lit(E):
            try:
                c = num.fact(w, E, T)
                return self._step([c], 'a1i', fmt(T, E))
            except (ValueError, AssertionError) as e:
                pass
        # Word target: any Word leaf matches for the generic 'Word' requirement
        if T == 'Word':
            for (E2, k), st in list(self.memo.items()):
                if E2 == E and k.startswith('Word'):
                    return st
        h = head(E)
        hk = headkey(h)
        if hk == 'logb' and h[1] == '2' and T in ('RR', 'ge0'):
            try:
                if T == 'ge0' and LOGB_GE0 != 'logbge0b':
                    x = self.prove(h[2], 'RR+')
                    g = self.prove(h[2], 'ge1')
                    i = w.inst(LOGB_GE0)
                    return self._step([x, g, i], 'syl2anc', fmt(T, E))
                z2 = num.closed(w, [], '2z', '2 e. ZZ'); u = w.inst('uzid')
                u2 = num.closed(w, [z2, u], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
                u3 = self._step([u2], 'a1i', '2 e. ( ZZ>= ` 2 )')
                x = self.prove(h[2], 'RR+')
                if T == 'RR':
                    i = w.inst('relogbzcl')
                    return self._step([u3, x, i], 'syl2anc', fmt(T, E))
                i = w.inst('logbge0b')
                bi = self._step([u3, x, i], 'syl2anc', '( 0 <_ %s <-> 1 <_ %s )' % (E, h[2]))
                return self._step([self.prove(h[2], 'ge1'), bi], 'mpbird', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        table = SIGN_RULES if T in SIGNS else MEM_RULES
        rules = list(table.get((hk, T), []))
        if hk == 'if' and T not in SIGNS:
            # both branches in the target: ifcld, for any membership target
            rules.append(('ifcld', 'd', [(T, 1), (T, 2)]))
        if T == 'Word':
            for (hk2, T2), rs in MEM_RULES.items():
                if hk2 == hk and T2.startswith('Word'):
                    rules += rs
        for lemma, form, reqs in rules:
            try:
                return self._apply(E, T, h, lemma, form, reqs)
            except ClosureError as e:
                failures.append(e)
        # exponent 2: sqge0d needs no sign of the base
        if hk == 'exp' and T == 'ge0' and h[2] == '2':
            try:
                return self._step([self.prove(h[1], 'RR')], 'sqge0d', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        # a restricted class abstraction is finite when its domain is
        if h[0] == 'rab' and T == 'Fin':
            try:
                fin = self.prove(h[2], 'Fin')
                c = num.closed(w, [], 'ssrab2', '%s C_ %s' % (E, h[2]))
                ss = self._step([c], 'a1i', '%s C_ %s' % (E, h[2]))
                return self._step([fin, ss], 'ssfid', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        # setness: every operation value, function value and negation is a set,
        # and so is anything already known to lie in a class
        if T == '_V':
            lemma = None
            if hk == 'neg':
                lemma = 'negex'
            elif hk == 'ov' or hk in INFIX.values():
                lemma = 'ovex'
            elif hk.startswith('fv:'):
                lemma = 'fvex'
            if lemma is not None:
                c = num.closed(w, [], lemma, fmt(T, E))
                return self._step([c], 'a1i', fmt(T, E))
            for src in ('CC', 'RR', 'ZZ', 'NN0', 'NN', 'RR+', 'Fin'):
                try:
                    return self._step([self.prove(E, src)], 'elexd', fmt(T, E))
                except ClosureError as e:
                    failures.append(e)
        # upcasts
        for src, lemma in UPCAST.get(T, []):
            try:
                return self._step([self.prove(E, src)], lemma, fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        if T == 'RR+':
            try:
                return self._step([self.prove(E, 'RR'), self.prove(E, 'gt0')], 'elrpd', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        if T == 'ge0':
            try:
                z = self._step([], '0red', '0 e. RR')
                return self._step([z, self.prove(E, 'RR'), self.prove(E, 'gt0')], 'ltled', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        if T == 'ge1':
            try:
                o = self._step([], '1red', '1 e. RR')
                return self._step([o, self.prove(E, 'RR'), self.prove(E, 'gt1')], 'ltled', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        # 1 <_ E for an integer that is positive, and for a product of two
        # factors that are each at least 1
        if T == 'ge1':
            try:
                i = w.inst('zgt0ge1')
                bi = self._step([self.prove(E, 'ZZ'), i], 'syl', '( 0 < %s <-> 1 <_ %s )' % (E, E))
                return self._step([self.prove(E, 'gt0'), bi], 'mpbid', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
            if hk == 'mul':
                try:
                    A, B = h[1], h[2]
                    rA, rB = self.prove(A, 'RR'), self.prove(B, 'RR')
                    i = w.inst('lemulge11')
                    le = self._step([rA, rB, self.prove(A, 'ge0'), self.prove(B, 'ge1'), i],
                                    'syl22anc', '%s <_ %s' % (A, E))
                    o = self._step([], '1red', '1 e. RR')
                    return self._step([o, rA, self.prove(E, 'RR'), self.prove(A, 'ge1'), le],
                                      'letrd', fmt(T, E))
                except ClosureError as e:
                    failures.append(e)
            if hk == 'fv:exp':
                # 1 <_ ( exp ` X ) for a nonnegative real exponent: efle at 0
                # and ( exp ` 0 ) = 1
                try:
                    X = h[2]; E0 = '( exp ` 0 )'
                    z = self._step([], '0red', '0 e. RR')
                    i = w.inst('efle')
                    bi = self._step([z, self.prove(X, 'RR'), i], 'syl2anc',
                                    '( 0 <_ %s <-> %s <_ %s )' % (X, E0, E))
                    le = self._step([self.prove(X, 'ge0'), bi], 'mpbid', '%s <_ %s' % (E0, E))
                    c = num.closed(w, [], 'ef0', '%s = 1' % E0)
                    e1 = self._step([c], 'a1i', '%s = 1' % E0)
                    e2 = self._step([e1], 'eqcomd', '1 = %s' % E0)
                    return self._step([e2, le], 'eqbrtrd', fmt(T, E))
                except ClosureError as e:
                    failures.append(e)
        if T == 'ne0':
            try:
                return self._step([self.prove(E, 'gt0')], 'gt0ne0d', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        # parent (for the body of a sum): lift with adantr
        if self.parent is not None:
            try:
                st = self.parent.prove(E, T)
                return self._step([st], 'adantr', fmt(T, E))
            except ClosureError as e:
                failures.append(e)
        wanted = []
        for e in failures:
            for f in (e.wanted or (e.blocked,)):
                if f not in wanted:
                    wanted.append(f)
        if fmt(T, E) not in wanted:
            wanted.append(fmt(T, E))     # supplying the goal itself unblocks it
        # a missing sign fact is the usual culprit and the one a caller can
        # supply at once, so it is named before the memberships
        wanted = ([f for f in wanted if (kind_of_formula(f) or ('', ''))[0] in SIGNS] +
                  [f for f in wanted if (kind_of_formula(f) or ('', ''))[0] not in SIGNS])
        blocked = wanted[0]
        rest = [f for f in wanted if f != fmt(T, E)] or wanted
        shown = rest[:MAX_WANTED]
        more = '' if len(rest) <= MAX_WANTED else '\n  ... and %d more' % (len(rest) - MAX_WANTED)
        raise ClosureError('no rule proves %s under %s; every route needs a fact this '
                           'closure does not have -- supply one of:\n  %s%s'
                           % (fmt(T, E), self.ante, '\n  '.join(shown), more), blocked, wanted)

    def _req(self, h, kind, idx):
        if idx == 'body':
            raise ClosureError('internal')
        if kind == 'closed':
            return idx(self.w)
        return self.prove(hargs(h)[idx], kind)

    def _apply(self, E, T, h, lemma, form, reqs):
        w = self.w
        if form == 'a0':      # deduction lemma without hypotheses
            return self._step([], lemma, fmt(T, E))
        if form == 'a':       # closed theorem, lifted
            c = num.closed(w, [], lemma, fmt(T, E))
            return self._step([c], 'a1i', fmt(T, E))
        if form == 's':       # sum / product: child closure for the body
            k, A, B = h[1], h[2], h[3]
            hyps = []
            child = None
            for kind, idx in reqs:
                if idx == 'body':
                    if child is None:
                        child = self.child(k, A)
                    hyps.append(child.prove(B, kind))
                else:
                    hyps.append(self.prove(A, kind))
            return self._step(hyps, lemma, fmt(T, E))
        hyps = [self._req(h, kind, idx) for kind, idx in reqs]
        if form == 'd':
            return self._step(hyps, lemma, fmt(T, E))
        i = w.inst(lemma)
        ref = {1: 'syl', 2: 'syl2anc', 3: 'syl3anc'}[len(hyps)]
        return self._step(hyps + [i], ref, fmt(T, E))

    def child(self, k, A):
        """closure under ( ante /\\ k e. A ) with the leaf for k derived from A"""
        if re.search(r'(^|\s)%s(\s|$)' % re.escape(k), self.ante):
            raise ClosureError('bound variable %s occurs in the antecedent %s' % (k, self.ante))
        ante2 = '( %s /\\ %s e. %s )' % (self.ante, k, A)
        c = Closure(self.w, ante2, parent=self, extra='%s e. %s' % (k, A))
        c.atoms = set(self.atoms)
        el = self.w.s([], 'simpr', '( %s -> %s e. %s )' % (ante2, k, A))
        kind, lemma = range_kind(A)
        if kind is not None:
            if lemma is None:
                c.memo[(k, kind)] = el
            else:
                i = self.w.inst(lemma)
                c.memo[(k, kind)] = self.w.s([el, i], 'syl', '( %s -> %s )' % (ante2, fmt(kind, k)))
        return c

    def pair_child(self, x, A, y, B):
        """closure under ( ante /\\ ( x e. A /\\ y e. B ) ), the antecedent of
        the body hypothesis of `fsumcom` and `fsumdvdsmul`"""
        for v in (x, y):
            if re.search(r'(^|\s)%s(\s|$)' % re.escape(v), self.ante):
                raise ClosureError('bound variable %s occurs in the antecedent %s' % (v, self.ante))
        ante2 = '( %s /\\ ( %s e. %s /\\ %s e. %s ) )' % (self.ante, x, A, y, B)
        c = Closure(self.w, ante2, parent=self)
        c.atoms = set(self.atoms)
        for v, R, ref in ((x, A, 'simprl'), (y, B, 'simprr')):
            el = self.w.s([], ref, '( %s -> %s e. %s )' % (ante2, v, R))
            kind, lemma = range_kind(R)
            if kind is None:
                continue
            if lemma is None:
                c.memo[(v, kind)] = el
            else:
                i = self.w.inst(lemma)
                c.memo[(v, kind)] = self.w.s([el, i], 'syl', '( %s -> %s )' % (ante2, fmt(kind, v)))
        return c
