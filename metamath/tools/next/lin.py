"""A `linarith` substitute for real arithmetic in deduction form (sortie G).

    from tm import W
    from lin import linarith
    w = W('gtest1', 'description')
    A = '( ( A e. RR /\\ B e. RR ) /\\ ( A <_ B /\\ 0 <_ A ) )'
    ra = w.s([], 'simpll', '( %s -> A e. RR )' % A)
    rb = w.s([], 'simplr', '( %s -> B e. RR )' % A)
    h1 = w.s([], 'simprl', '( %s -> A <_ B )' % A)
    h2 = w.s([], 'simprr', '( %s -> 0 <_ A )' % A)
    linarith(w, A, [h1, h2], '( 2 x. A ) <_ ( A + B )', leaves={'A': ra, 'B': rb}, name='qed')
    w.run()

linarith(w, ante, hyps, goal, leaves=None, closure=None, name=None, products=False):
  hyps    worksheet step names, each proving ( ante -> X <_ Y ), ( ante -> X < Y )
          or ( ante -> X = Y ); the formulas are read from the worksheet
  goal    `C <_ D` or `C < D` (the antecedent may be included)
  leaves  atom -> step proving ( ante -> atom e. RR ) (or (kind, step), as
          tools/cl.py accepts); closure: a cl.Closure to use instead
  name    step name of the conclusion; 'qed' writes the qed line
  returns the name of the step proving ( ante -> goal )

nlinarith(w, ante, hyps, goal, ...) is linarith with products=True: when no
linear certificate exists, every product of a pair of hypotheses is added as
a further nonnegative fact (its sign side condition discharged through
tools/cl.py) and the search is run again over the enlarged set; when that
fails too, the products of three hypotheses whose monomials already occur in
the problem are added and it is run a third time.  The product monomials are
further atoms, so the certificate stays linear; the normal form handles any
degree, and lin.MAXDEG (3) caps what the search will build.

lineq(w, ante, lhs, rhs, hyps=..., ...) proves an equality between two linear
real expressions by the two inequalities and letri3d.

cert=  (sortie G5) a supplied certificate instead of the search: a dict from
a hypothesis step name, or a tuple of step names for their product, to its
multiplier -- `cert={(qge, h5): 2, qqT: 128}` says
`goal = 2 (h5's form)(qge's form) + 128 (qqT's form) + slack`.  An equation
step counts as `Y - X`; a negative multiplier on a single equation step uses
`X - Y`.  The slack is computed, and LinError names the residual when the
certificate does not close.  The chain emitted is the one the search would
emit for the same certificate; the mode exists so that a caller who knows the
certificate is not at the mercy of the simplex's choice, and so that a failed
search can be replaced by the intended proof.

fast=  (sortie G5) the structural fast path for a goal with at most one
hypothesis: instead of proving the normal-form identity, the goal is taken
apart along its own syntax -- `le2addd` for a sum against a sum, `lemul2ad`
for a common literal factor, `lediv1dd` for a common denominator, `letrd`
through the hypothesis, `lesub1dd` / `lesub2dd` / `le2subd`, `lenegd`,
`addge01d` / `subge02d` for an added or subtracted nonnegative term, a closed
numeral comparison at the leaves (`num.le_lit`) -- with every sub-goal checked
against the certificate arithmetic before a step is written.  A goal outside
the rules falls through to the general path unchanged.  Off by default so
that every stored worksheet reproduces; `lin.FASTPATH = True` (or the
environment variable LIN_FAST=1) turns it on for a whole generator, `fast=True`
for one call.  V4b's assembly worksheets shrink by 30 per cent with it on.

Linear expressions: `( A + B )`, `( A - B )`, `( k x. A )`, `( A x. k )`,
`( A / q )`, `-u A`, literals (numerals `0`..`9`, decimals `; 1 2`,
fractions `( p / q )`, negated literals); anything else is an atom, an opaque
class expression compared by its text (`( log ` N )`, `( C x. ( ell2 ` N ) )`).
A `sum_`, `prod_` or `if` term is a single atom whatever it contains, so an
inequality with one on either side is a linear problem in it; its closure
comes from tools/cl.py like any other atom.  So is any expression the caller
declares atomic -- `atoms=[E, ...]`, or `Closure.atom(E)` / `Closure.leaf(E,
kind, step)` -- : the decomposition stops there and the closure is never
asked for a subterm of it.  Literals must be canonical
(lowest terms, no leading zeros).  With products=True a product of two
non-literals is expanded instead of being one atom.

Certificate: each hypothesis X rel Y is the linear form Y - X (>= 0, > 0, or
= 0, an equation counting as two inequalities); the goal C rel D is g = D - C.
A simplex over fractions.Fraction finds multipliers c_i >= 0 and a constant
r >= 0 with sum c_i f_i + r = g coefficientwise, and, for a strict goal,
c_i > 0 on a strict hypothesis or r > 0.

Proof: `0 <_ ( Y - X )` by subge0d (posdifd when strict, eqled for an
equation), scaled by `( c x. ... )` with mulge0d/mulgt0d, summed with
addge0d/addgegt0d/addgtge0d/addgt0d into `0 <_ S`; the identity
`S = ( D - C )` is proved by normalising both sides to the same normal form
`( ( c + ( k1 x. a1 ) ) + ( k2 x. a2 ) ) ...` (atoms sorted, integer
coefficients after scaling by the common denominator d, cancelled with
mulcanad); then breqtrd, subge0d/posdifd.  The normal form of a scaled
expression `( s x. E )` is computed recursively with adddid, subdid,
mulassd, mulneg1d/mulneg2d, mul02d, mullidd, and merged with add4d,
add32d, addassd, adddird; coefficient arithmetic is closed (tools/num.py).
"""
import os, re, sys
from fractions import Fraction
from math import gcd
sys.path.insert(0, os.path.dirname(__file__))
import num
from cl import Closure, ClosureError, split_top, formula_of, strip_ante
import congr


class LinError(Exception):
    pass


# the highest degree a monomial of the certificate may reach.  Degree 2 is
# a product of two hypotheses; degree 3 is a product of three, which is what
# a hypothesis bounding a triple product needs; degree 4 is what a polynomial
# bound such as Brun-Titchmarsh's needs.  Each degree is searched as soon as
# its products are in, so the certificate of a problem the previous degree
# already solved is unchanged.  A product is added only when every monomial of
# it already occurs in the problem, which is what keeps the count down: the
# number of products grows as the MAXDEG-th power of the hypothesis count.
# The normal form handles any degree.
MAXDEG = 4


# ---------------------------------------------------------------- parsing

class Node:
    def __init__(self, kind, text, kids=(), val=None):
        self.kind = kind; self.text = text; self.kids = list(kids); self.val = val

    def __repr__(self):
        return '%s(%s)' % (self.kind, self.text)


ARITH = {'+': 'add', '-': 'sub', 'x.': 'mul', '/': 'div'}


def parse(text, products=False, leaves=()):
    """parse an expression into Nodes: lit, atom, add, sub, neg,
    scale (k x. E), div (E / q), and, with products=True, mul (E x. F) for a
    product of two non-literals (which linear mode keeps as one opaque atom).
    A `sum_`, `prod_` or `if` term is one atom, whatever it contains, and so
    is any expression in `leaves` (the texts the caller declared to the
    Closure): the decomposition stops there, so the closure is never asked
    for a subterm the caller has already covered."""
    text = ' '.join(text.split())
    v = num.lit_value(text)
    if v is not None:
        return Node('lit', text, val=v)
    if text in leaves:
        return Node('atom', text)
    toks = text.split()
    if toks[0] == '-u':
        return Node('neg', text, [parse(' '.join(toks[1:]), products, leaves)])
    if toks[0] == '(' and toks[-1] == ')':
        try:
            parts = split_top(toks[1:-1])
        except SyntaxError:
            return Node('atom', text)
        if len(parts) == 3 and parts[1] in ARITH:
            op = ARITH[parts[1]]
            a, b = parse(parts[0], products, leaves), parse(parts[2], products, leaves)
            if op in ('add', 'sub'):
                return Node(op, text, [a, b])
            if op == 'mul':
                if a.kind == 'lit':
                    return Node('scale', text, [b], val=a.val)
                if b.kind == 'lit':
                    return Node('scaler', text, [a], val=b.val)
                if products:
                    return Node('mul', text, [a, b])
                return Node('atom', text)
            if op == 'div':
                if b.kind == 'lit' and b.val > 0 and b.val.denominator == 1:
                    return Node('div', text, [a], val=b.val)
                return Node('atom', text)
    return Node('atom', text)


# the largest exponent `expand_pow` will write out as a product.  An integer
# power is an opaque atom to the certificate search, so `3 <_ ( p ^ 2 )` has no
# certificate while `3 <_ ( p x. p )` has one; the expansion is applied only
# after the search has failed as written, so a worksheet that succeeded before
# is unchanged.
MAXPOW = 4


def powmap(text, lv=(), limit=None, out=None):
    """{ `( E ^ n )` subterm : the n-fold product of E }, outermost first, for
    every small positive integer literal exponent.  A declared atom is not
    entered, and a power whose base is itself a power is expanded one level:
    `( ( X ^ 2 ) ^ 2 )` becomes `( ( X ^ 2 ) x. ( X ^ 2 ) )`."""
    limit = MAXPOW if limit is None else limit
    out = {} if out is None else out
    text = ' '.join(text.split())
    if text in lv:
        return out
    toks = text.split()
    if not (toks[0] == '(' and toks[-1] == ')'):
        return out
    try:
        parts = split_top(toks[1:-1])
    except SyntaxError:
        return out
    if len(parts) == 3 and parts[1] == '^':
        v = num.lit_value(parts[2])
        if v is not None and v.denominator == 1 and 2 <= v <= limit:
            prod = parts[0]
            for _ in range(int(v) - 1):
                prod = '( %s x. %s )' % (prod, parts[0])
            out[text] = prod
            return out
    for pp in parts:
        powmap(pp, lv, limit, out)
    return out


def expand_pow(text, lv=(), limit=None):
    """TEXT with every small integer power written out as a product"""
    text = ' '.join(text.split())
    for k, v in powmap(text, lv, limit).items():
        text = text.replace(k, v)
    return text


def powexp(w, ante, E, n, cl, gen=None):
    """the step proving ( ante -> ( E ^ n ) = ( ... ( E x. E ) ... x. E ) ),
    by `sqvald` and one `expp1d` per further factor"""
    def st(hyps, ref, f):
        return w.s(hyps, ref, '( %s -> %s )' % (ante, f))
    cc = cl.mem(E, 'CC')
    cur = '( %s x. %s )' % (E, E)
    step = st([cc], 'sqvald', '( %s ^ 2 ) = %s' % (E, cur))
    for m in range(3, int(n) + 1):
        pt, mt = num.nat_text(m - 1), num.nat_text(m)
        n0 = st([num.nn0(w, m - 1)], 'a1i', '%s e. NN0' % pt)
        e1 = st([cc, n0], 'expp1d', '( %s ^ ( %s + 1 ) ) = ( ( %s ^ %s ) x. %s )'
                % (E, pt, E, pt, E))
        oe = w.s([num.add_nat(w, m - 1, 1)], 'oveq2i',
                 '( %s ^ ( %s + 1 ) ) = ( %s ^ %s )' % (E, pt, E, mt))
        oed = st([oe], 'a1i', '( %s ^ ( %s + 1 ) ) = ( %s ^ %s )' % (E, pt, E, mt))
        tr = st([oed, e1], 'eqtr3d', '( %s ^ %s ) = ( ( %s ^ %s ) x. %s )' % (E, mt, E, pt, E))
        nxt = '( %s x. %s )' % (cur, E)
        o1 = st([step], 'oveq1d', '( ( %s ^ %s ) x. %s ) = %s' % (E, pt, E, nxt))
        step = st([tr, o1], 'eqtrd', '( %s ^ %s ) = %s' % (E, mt, nxt))
        cur = nxt
    return step, cur


def powrules(w, ante, texts, cl, lv=()):
    """the rewrite rules tools/congr.py needs to turn every small integer power
    occurring in TEXTS into a product: { subterm : (product, step) }"""
    rules = {}
    for t in texts:
        for k, v in powmap(t, lv).items():
            if k in rules:
                continue
            base = split_top(k.split()[1:-1])
            E, n = base[0], num.lit_value(base[2])
            step, prod = powexp(w, ante, E, n, cl)
            rules[k] = (prod, step)
    return rules


def powconv(w, ante, text, rules, gen=None):
    """(step proving ( ante -> text = expanded ), expanded), or (None, text)"""
    if not rules:
        return None, text
    g = gen or congr.StepGen('p')
    st, new = congr.rewrite(text, dict(rules), ante, g)
    w.lines.extend(g.lines); g.lines = []
    return st, ' '.join(new.split())


def mono_text(m):
    """the class expression of a monomial (a tuple of atom texts in order):
    `a` for a single atom, `( a x. b )` for a product"""
    if not m:
        return ''
    t = m[0]
    for a in m[1:]:
        t = '( %s x. %s )' % (t, a)
    return t


def padd(f, g, s=Fraction(1)):
    out = dict(f)
    for k, c in g.items():
        v = out.get(k, Fraction(0)) + s * c
        if v == 0:
            out.pop(k, None)
        else:
            out[k] = v
    return out


def pmul(f, g):
    out = {}
    for k1, c1 in f.items():
        for k2, c2 in g.items():
            k = tuple(sorted(k1 + k2, key=lambda a: a))
            v = out.get(k, Fraction(0)) + c1 * c2
            if v == 0:
                out.pop(k, None)
            else:
                out[k] = v
    return out


def poly_form(node, s=Fraction(1)):
    """dict monomial -> coefficient; the monomial is a tuple of atom texts in
    order, the constant is the empty tuple.  A linear expression has only
    monomials of length 1."""
    k = node.kind
    if k == 'lit':
        v = s * node.val
        return {(): v} if v else {}
    if k == 'atom':
        return {(node.text,): s} if s else {}
    if k == 'add':
        return padd(poly_form(node.kids[0], s), poly_form(node.kids[1], s))
    if k == 'sub':
        return padd(poly_form(node.kids[0], s), poly_form(node.kids[1], s), -1)
    if k == 'neg':
        return poly_form(node.kids[0], -s)
    if k in ('scale', 'scaler'):
        return poly_form(node.kids[0], s * node.val)
    if k == 'div':
        return poly_form(node.kids[0], s / node.val)
    if k == 'mul':
        return pmul(poly_form(node.kids[0], s), poly_form(node.kids[1], Fraction(1)))
    return {}


linear_form = poly_form


def denominators(node, s=Fraction(1), out=None):
    """denominators of every path product (for the common scale d)"""
    if out is None:
        out = set()
    if node.kind == 'lit':
        out.add((s * node.val).denominator)
    elif node.kind == 'atom':
        out.add(s.denominator)
    elif node.kind == 'mul':
        # the two factors are normalised separately, the scale going to the
        # left one: the common scale must clear both factors at once
        dA = dB = 1
        for q in denominators(node.kids[0]):
            dA = lcm(dA, q)
        for q in denominators(node.kids[1]):
            dB = lcm(dB, q)
        out.add(s.denominator * dA * dB)
    else:
        s2 = s
        if node.kind in ('scale', 'scaler'):
            s2 = s * node.val
        elif node.kind == 'div':
            s2 = s / node.val
        elif node.kind == 'neg':
            s2 = -s
        out.add(s2.denominator)
        for k in node.kids:
            denominators(k, s2, out)
    return out


def lcm(a, b):
    return a * b // gcd(a, b)


# ---------------------------------------------------------------- simplex

def simplex_max(A, b, c):
    """maximize c.x subject to A x = b, x >= 0 (Fractions).  Returns (status,
    x) with status 'optimal', 'unbounded' (x has objective > 0 along the
    ray) or 'infeasible'.  Dense tableau, Bland's rule, two phases."""
    m, n = len(A), len(c)
    # make b >= 0
    A = [row[:] for row in A]; b = b[:]
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]; b[i] = -b[i]
    # phase 1 tableau: variables x (n) + artificials (m)
    T = []
    for i in range(m):
        T.append(A[i] + [Fraction(1) if j == i else Fraction(0) for j in range(m)] + [b[i]])
    basis = [n + i for i in range(m)]
    N = n + m

    def pivot(r, col):
        p = T[r][col]
        T[r] = [v / p for v in T[r]]
        for i in range(len(T)):
            if i != r and T[i][col] != 0:
                f = T[i][col]
                T[i] = [T[i][j] - f * T[r][j] for j in range(N + 1)]
        basis[r] = col

    def run(obj, allowed):
        """obj: list of N costs to maximize; allowed: usable columns"""
        while True:
            # reduced costs
            red = []
            for j in allowed:
                rc = obj[j] - sum(obj[basis[i]] * T[i][j] for i in range(m))
                red.append((j, rc))
            enter = None
            for j, rc in red:
                if rc > 0:
                    enter = j; break        # Bland: smallest index
            if enter is None:
                return 'optimal'
            ratio = None; leave = None
            for i in range(m):
                if T[i][enter] > 0:
                    q = T[i][N] / T[i][enter]
                    if ratio is None or q < ratio or (q == ratio and basis[i] < basis[leave]):
                        ratio = q; leave = i
            if leave is None:
                return ('unbounded', enter)
            pivot(leave, enter)

    obj1 = [Fraction(0)] * n + [Fraction(-1)] * m
    run(obj1, list(range(N)))
    if any(T[i][N] != 0 and basis[i] >= n for i in range(m)):
        return 'infeasible', None
    # drive artificials out of the basis where possible
    for i in range(m):
        if basis[i] >= n:
            for j in range(n):
                if T[i][j] != 0:
                    pivot(i, j); break
    allowed = list(range(n))
    obj2 = list(c) + [Fraction(0)] * m
    res = run(obj2, allowed)

    def solution():
        x = [Fraction(0)] * n
        for i in range(m):
            if basis[i] < n:
                x[basis[i]] = T[i][N]
        return x
    if res == 'optimal':
        return 'optimal', solution()
    enter = res[1]
    x = solution()
    # move along the ray: x_enter = 1, basics adjust
    x[enter] += 1
    for i in range(m):
        if basis[i] < n:
            x[basis[i]] -= T[i][enter]
    return 'unbounded', x


def certificate(forms, strict_flags, goal, goal_strict):
    """forms: list of linear forms f_i (dicts); goal g.  Find c_i >= 0, r >= 0
    with sum c_i f_i + r = g; for a strict goal, maximise the strict mass.
    Returns (c list, r) or raises LinError."""
    atoms = sorted(set(k for f in forms + [goal] for k in f if k), key=mono_text)
    rows = [a for a in atoms] + [()]
    n = len(forms) + 1   # + r
    A = []; b = []
    for key in rows:
        row = [f.get(key, Fraction(0)) for f in forms] + [Fraction(1) if key == () else Fraction(0)]
        A.append(row); b.append(goal.get(key, Fraction(0)))
    if goal_strict:
        c = [Fraction(1) if s else Fraction(0) for s in strict_flags] + [Fraction(1)]
    else:
        c = [Fraction(-1)] * len(forms) + [Fraction(0)]   # prefer few hypotheses
    status, x = simplex_max(A, b, c)
    if status == 'infeasible':
        raise LinError('no certificate: the goal does not follow linearly from the hypotheses')
    if goal_strict:
        mass = sum(x[i] for i in range(len(forms)) if strict_flags[i]) + x[-1]
        if mass <= 0:
            raise LinError('no certificate: the goal is strict but no strict hypothesis or positive slack is available')
    return x[:-1], x[-1]


# ---------------------------------------------------------------- normal forms

class Vec:
    """a polynomial as an ordered list of (monomial, coeff) plus a constant;
    the monomials are tuples of atom texts, ordered by `mono_text`, and a
    linear form has only monomials of length 1"""
    def __init__(self, const=Fraction(0), terms=()):
        self.const = Fraction(const); self.terms = list(terms)

    def text(self):
        t = num.lit_text(self.const)
        for a, k in self.terms:
            t = '( %s + ( %s x. %s ) )' % (t, num.lit_text(k), mono_text(a))
        return t

    def prefix(self):
        """the Vec without its last term, and that term"""
        return Vec(self.const, self.terms[:-1]), self.terms[-1]


def scaled(E, s):
    return E if s == 1 else '( %s x. %s )' % (num.lit_text(s), E)


class Normalizer:
    def __init__(self, w, ante, closure):
        self.w = w; self.ante = ante; self.cl = closure

    def st(self, hyps, ref, formula):
        return self.w.s(hyps, ref, '( %s -> %s )' % (self.ante, formula))

    def eq(self, hyps, ref, lhs, rhs):
        return self.st(hyps, ref, '%s = %s' % (lhs, rhs))

    def cc(self, E):
        return self.cl.mem(E, 'CC')

    def closed(self, step, formula):
        return self.st([step], 'a1i', formula)

    def chain(self, steps, lhs, rhss):
        """eqtrd chain: steps[i] proves lhs_i = rhss[i]"""
        acc = steps[0]
        for i in range(1, len(steps)):
            acc = self.eq([acc, steps[i]], 'eqtrd', lhs, rhss[i])
        return acc

    def negscale(self, s, B):
        """step: -u scaled(B, s) = scaled(B, -s), and the text scaled(B, -s)"""
        if s == 1:
            m = self.eq([self.cc(B)], 'mulm1d', '( -u 1 x. %s )' % B, '-u %s' % B)
            return self.eq([m], 'eqcomd', '-u %s' % B, '( -u 1 x. %s )' % B)
        ts = num.lit_text(s)
        st1 = self.eq([self.cc(ts), self.cc(B)], 'mulneg1d', '( -u %s x. %s )' % (ts, B), '-u ( %s x. %s )' % (ts, B))
        st2 = self.eq([st1], 'eqcomd', '-u ( %s x. %s )' % (ts, B), '( -u %s x. %s )' % (ts, B))
        cur = '( -u %s x. %s )' % (ts, B)
        steps = [st2]; rhss = [cur]
        if s < 0:
            n = num.neg_lit(self.w, ts)
            nd = self.closed(n, '-u %s = %s' % (ts, num.lit_text(-s)))
            cur2 = '( %s x. %s )' % (num.lit_text(-s), B)
            steps.append(self.eq([nd], 'oveq1d', cur, cur2)); rhss.append(cur2); cur = cur2
        if -s == 1:
            steps.append(self.eq([self.cc(B)], 'mullidd', cur, B)); rhss.append(B)
        return self.chain(steps, '-u ( %s x. %s )' % (ts, B), rhss)

    def nf(self, node, s):
        """step proving scaled(node.text, s) = T(vec), and vec"""
        w = self.w; E = node.text; ts = num.lit_text(s); ET = scaled(E, s)
        if node.kind == 'lit':
            v = s * node.val
            assert v.denominator == 1, (E, s)
            vec = Vec(v)
            if s == 1 and E == num.lit_text(node.val):
                return self.st([], 'eqidd', '%s = %s' % (E, E)), vec
            if s == 1:
                m = self.eq([self.cc(E)], 'mullidd', '( 1 x. %s )' % E, E)
                st0 = self.eq([m], 'eqcomd', E, '( 1 x. %s )' % E)
                c = self.closed(num.mul_lit(w, 1, E), '( 1 x. %s ) = %s' % (E, vec.text()))
                return self.eq([st0, c], 'eqtrd', E, vec.text()), vec
            c = self.closed(num.mul_lit(w, s, E), '%s = %s' % (ET, vec.text()))
            return c, vec
        if node.kind == 'atom':
            vec = Vec(0, [((E,), s)])
            T = vec.text(); inner = '( %s x. %s )' % (ts, E)
            a = self.eq([self.cc(inner)], 'addlidd', T, inner)
            a2 = self.eq([a], 'eqcomd', inner, T)
            if s == 1:
                m = self.eq([self.cc(E)], 'mullidd', inner, E)
                m2 = self.eq([m], 'eqcomd', E, inner)
                return self.eq([m2, a2], 'eqtrd', E, T), vec
            return a2, vec
        if node.kind == 'add':
            A, B = node.kids
            steps = []; rhss = []
            if s != 1:
                cur = '( %s + %s )' % (scaled(A.text, s), scaled(B.text, s))
                steps.append(self.eq([self.cc(ts), self.cc(A.text), self.cc(B.text)], 'adddid', ET, cur)); rhss.append(cur)
            sA, vA = self.nf(A, s); sB, vB = self.nf(B, s)
            cur = '( %s + %s )' % (vA.text(), vB.text())
            steps.append(self.eq([sA, sB], 'oveq12d', '( %s + %s )' % (scaled(A.text, s), scaled(B.text, s)), cur)); rhss.append(cur)
            sM, vM = self.nfadd(vA, vB)
            steps.append(sM); rhss.append(vM.text())
            return self.chain(steps, ET, rhss), vM
        if node.kind == 'sub':
            A, B = node.kids
            steps = []; rhss = []
            X, Y = scaled(A.text, s), scaled(B.text, s)
            if s != 1:
                cur = '( %s - %s )' % (X, Y)
                steps.append(self.eq([self.cc(ts), self.cc(A.text), self.cc(B.text)], 'subdid', ET, cur)); rhss.append(cur)
            ns = self.eq([self.cc(X), self.cc(Y)], 'negsubd', '( %s + -u %s )' % (X, Y), '( %s - %s )' % (X, Y))
            cur = '( %s + -u %s )' % (X, Y)
            steps.append(self.eq([ns], 'eqcomd', '( %s - %s )' % (X, Y), cur)); rhss.append(cur)
            ng = self.negscale(s, B.text)
            Ym = scaled(B.text, -s)
            cur = '( %s + %s )' % (X, Ym)
            steps.append(self.eq([ng], 'oveq2d', '( %s + -u %s )' % (X, Y), cur)); rhss.append(cur)
            sA, vA = self.nf(A, s); sB, vB = self.nf(B, -s)
            cur2 = '( %s + %s )' % (vA.text(), vB.text())
            steps.append(self.eq([sA, sB], 'oveq12d', cur, cur2)); rhss.append(cur2)
            sM, vM = self.nfadd(vA, vB)
            steps.append(sM); rhss.append(vM.text())
            return self.chain(steps, ET, rhss), vM
        if node.kind == 'neg':
            A = node.kids[0]
            steps = []; rhss = []
            if s != 1:
                cur = '-u ( %s x. %s )' % (ts, A.text)
                steps.append(self.eq([self.cc(ts), self.cc(A.text)], 'mulneg2d', ET, cur)); rhss.append(cur)
            ng = self.negscale(s, A.text)
            steps.append(ng); rhss.append(scaled(A.text, -s))
            sA, vA = self.nf(A, -s)
            steps.append(sA); rhss.append(vA.text())
            return self.chain(steps, ET, rhss), vA
        if node.kind == 'mul':
            A, B = node.kids
            dB = 1
            for q in denominators(B):
                dB = lcm(dB, q)
            sB_ = Fraction(dB); sA_ = s / sB_
            if sA_.denominator != 1:
                raise LinError('cannot normalise the product %s at scale %s' % (E, s))
            SA, SB = num.lit_text(sA_), num.lit_text(sB_)
            XA = '( %s x. %s )' % (SA, A.text); XB = '( %s x. %s )' % (SB, B.text)
            both = '( %s x. %s )' % (XA, XB)
            assoc = '( ( %s x. %s ) x. %s )' % (SA, SB, E)
            m4 = self.eq([self.cc(SA), self.cc(A.text), self.cc(SB), self.cc(B.text)], 'mul4d', both, assoc)
            c = self.closed(num.mul_lit(w, sA_, SB), '( %s x. %s ) = %s' % (SA, SB, ts))
            o = self.eq([c], 'oveq1d', assoc, '( %s x. %s )' % (ts, E))
            fwd = self.eq([m4, o], 'eqtrd', both, '( %s x. %s )' % (ts, E))
            if s == 1:
                ml = self.eq([self.cc(E)], 'mullidd', '( 1 x. %s )' % E, E)
                fwd = self.eq([fwd, ml], 'eqtrd', both, E)
            back = self.eq([fwd], 'eqcomd', ET, both)
            sA, vA = self.nfs(A, sA_); sB, vB = self.nfs(B, sB_)
            cur2 = '( %s x. %s )' % (vA.text(), vB.text())
            o2 = self.eq([sA, sB], 'oveq12d', both, cur2)
            sM, vM = self.nfmul(vA, vB)
            return self.chain([back, o2, sM], ET, [both, cur2, vM.text()]), vM
        if node.kind == 'scaler':
            A = node.kids[0]; K = num.lit_text(node.val)
            inner = '( %s x. %s )' % (K, A.text)
            mc = self.eq([self.cc(A.text), self.cc(K)], 'mulcomd', E, inner)
            node2 = Node('scale', inner, [A], val=node.val)
            if s == 1:
                s2, v2 = self.nf(node2, 1)
                return self.eq([mc, s2], 'eqtrd', E, v2.text()), v2
            lift = self.eq([mc], 'oveq2d', ET, scaled(inner, s))
            s2, v2 = self.nf(node2, s)
            return self.eq([lift, s2], 'eqtrd', ET, v2.text()), v2
        if node.kind == 'div':
            A = node.kids[0]; q = node.val; Q = num.lit_text(q)
            if q == 1:
                d1 = self.eq([self.cc(A.text)], 'div1d', E, A.text)
                node2 = A
                inner = A.text
            else:
                inner = '( ( 1 / %s ) x. %s )' % (Q, A.text)
                i = w.inst('divrec2')
                d1 = self.eq([self.cc(A.text), self.cc(Q), self.cl.ne0(Q), i], 'syl3anc', E, inner)
                node2 = Node('scale', inner, [A], val=Fraction(1) / q)
            if s == 1:
                s2, v2 = self.nf(node2, 1)
                return self.eq([d1, s2], 'eqtrd', E, v2.text()), v2
            lift = self.eq([d1], 'oveq2d', ET, scaled(inner, s))
            s2, v2 = self.nf(node2, s)
            return self.eq([lift, s2], 'eqtrd', ET, v2.text()), v2
        if node.kind == 'scale':
            A = node.kids[0]; k = node.val; K = num.lit_text(k)
            assert E == '( %s x. %s )' % (K, A.text), 'non-canonical literal in ' + E
            steps = []; rhss = []
            if s == 1:
                assert k.denominator == 1 and k != 0, (E, s)
                if k == 1:
                    m = self.eq([self.cc(A.text)], 'mullidd', E, A.text)
                    sA, vA = self.nf(A, k)
                    return self.eq([m, sA], 'eqtrd', E, vA.text()), vA
                return self.nf(A, k)
            sk = s * k
            assert sk.denominator == 1, (E, s)
            ma = self.eq([self.cc(ts), self.cc(K), self.cc(A.text)], 'mulassd', '( ( %s x. %s ) x. %s )' % (ts, K, A.text), ET)
            cur = '( ( %s x. %s ) x. %s )' % (ts, K, A.text)
            steps.append(self.eq([ma], 'eqcomd', ET, cur)); rhss.append(cur)
            c = self.closed(num.mul_lit(w, s, K), '( %s x. %s ) = %s' % (ts, K, num.lit_text(sk)))
            cur2 = '( %s x. %s )' % (num.lit_text(sk), A.text)
            steps.append(self.eq([c], 'oveq1d', cur, cur2)); rhss.append(cur2)
            if sk == 0:
                steps.append(self.eq([self.cc(A.text)], 'mul02d', cur2, '0')); rhss.append('0')
                return self.chain(steps, ET, rhss), Vec(0)
            if sk == 1:
                steps.append(self.eq([self.cc(A.text)], 'mullidd', cur2, A.text)); rhss.append(A.text)
            sA, vA = self.nf(A, sk)
            steps.append(sA); rhss.append(vA.text())
            return self.chain(steps, ET, rhss), vA
        raise LinError('cannot normalise ' + E)

    def nfs(self, node, s):
        """like nf, but the left-hand side is always written `( s x. E )`"""
        st, v = self.nf(node, s)
        if s == 1:
            E = node.text
            m = self.eq([self.cc(E)], 'mullidd', '( 1 x. %s )' % E, E)
            return self.eq([m, st], 'eqtrd', '( 1 x. %s )' % E, v.text()), v
        return st, v

    def monoins(self, m, a):
        """step proving ( mono_text(m) x. a ) = mono_text(sorted(m + (a,))),
        or None when the two texts already coincide.  `m` is sorted, so `a`
        is carried left past the atoms above it, one `mul32d` each, and the
        innermost swap is a `mulcomd`."""
        M = mono_text(m); lhs = '( %s x. %s )' % (M, a)
        mm = tuple(sorted(m + (a,))); MM = mono_text(mm)
        if lhs == MM:
            return None
        mp, b = m[:-1], m[-1]
        if not mp:
            return self.eq([self.cc(b), self.cc(a)], 'mulcomd', lhs, MM)
        Mp = mono_text(mp)
        swapped = '( ( %s x. %s ) x. %s )' % (Mp, a, b)
        st = self.eq([self.cc(Mp), self.cc(b), self.cc(a)], 'mul32d', lhs, swapped)
        ins = self.monoins(mp, a)
        if ins is None:
            return st
        mid = mono_text(tuple(sorted(mp + (a,))))
        o = self.eq([ins], 'oveq1d', swapped, '( %s x. %s )' % (mid, b))
        return self.eq([st, o], 'eqtrd', lhs, MM)

    def monoprod(self, m1, m2):
        """step proving ( mono_text(m1) x. mono_text(m2) ) = mono_text of the
        sorted concatenation, or None when the two texts already coincide"""
        M1, M2 = mono_text(m1), mono_text(m2)
        lhs = '( %s x. %s )' % (M1, M2)
        mm = tuple(sorted(m1 + m2)); MM = mono_text(mm)
        if lhs == MM:
            return None
        if len(m2) == 1:
            return self.monoins(m1, m2[0])
        m2p, c = m2[:-1], m2[-1]
        M2p = mono_text(m2p)
        assoc = '( ( %s x. %s ) x. %s )' % (M1, M2p, c)
        ma = self.eq([self.cc(M1), self.cc(M2p), self.cc(c)], 'mulassd', assoc, lhs)
        steps = [self.eq([ma], 'eqcomd', lhs, assoc)]; rhss = [assoc]
        inner = self.monoprod(m1, m2p)
        mid = tuple(sorted(m1 + m2p))
        if inner is not None:
            cur = '( %s x. %s )' % (mono_text(mid), c)
            steps.append(self.eq([inner], 'oveq1d', rhss[-1], cur)); rhss.append(cur)
        ins = self.monoins(mid, c)
        if ins is not None:
            steps.append(ins); rhss.append(MM)
        return self.chain(steps, lhs, rhss)

    def nfmono(self, k1, m1, k2, m2):
        """step proving ( ( k1 x. m1 ) x. ( k2 x. m2 ) ) = T, and the Vec of
        the product monomial (degree at most MAXDEG)"""
        K1, K2 = num.lit_text(k1), num.lit_text(k2)
        M1, M2 = mono_text(m1), mono_text(m2)
        lhs = '( ( %s x. %s ) x. ( %s x. %s ) )' % (K1, M1, K2, M2)
        mm = tuple(sorted(m1 + m2))
        if len(mm) > MAXDEG:
            raise LinError('monomial %s has degree %d, above the cap lin.MAXDEG = %d'
                           % (mono_text(mm), len(mm), MAXDEG))
        kk = k1 * k2; KK = num.lit_text(kk)
        prod = '( %s x. %s )' % (M1, M2)
        assoc = '( ( %s x. %s ) x. %s )' % (K1, K2, prod)
        steps = [self.eq([self.cc(K1), self.cc(M1), self.cc(K2), self.cc(M2)], 'mul4d', lhs, assoc)]
        rhss = [assoc]
        c = self.closed(num.mul_lit(self.w, k1, K2), '( %s x. %s ) = %s' % (K1, K2, KK))
        cur = '( %s x. %s )' % (KK, prod)
        steps.append(self.eq([c], 'oveq1d', assoc, cur)); rhss.append(cur)
        MM = mono_text(mm)
        if MM != prod:
            mc = self.monoprod(m1, m2)
            cur = '( %s x. %s )' % (KK, MM)
            steps.append(self.eq([mc], 'oveq2d', rhss[-1], cur)); rhss.append(cur)
        v = Vec(0, [(mm, kk)]); T = v.text()
        a = self.eq([self.cc(cur)], 'addlidd', T, cur)
        steps.append(self.eq([a], 'eqcomd', cur, T)); rhss.append(T)
        return self.chain(steps, lhs, rhss), v

    def nfmulterm(self, v1, k, m):
        """step proving ( T1 x. ( k x. m ) ) = T, and the product Vec"""
        K = num.lit_text(k); M = mono_text(m); u = '( %s x. %s )' % (K, M)
        T1 = v1.text(); lhs = '( %s x. %s )' % (T1, u)
        if not v1.terms:
            c1 = v1.const
            if c1 == 0:
                return self.eq([self.cc(u)], 'mul02d', lhs, '0'), Vec(0)
            C = num.lit_text(c1)
            inner = '( ( %s x. %s ) x. %s )' % (C, K, M)
            ma = self.eq([self.cc(C), self.cc(K), self.cc(M)], 'mulassd', inner, lhs)
            steps = [self.eq([ma], 'eqcomd', lhs, inner)]; rhss = [inner]
            ck = c1 * k; CK = num.lit_text(ck)
            cst = self.closed(num.mul_lit(self.w, c1, K), '( %s x. %s ) = %s' % (C, K, CK))
            cur = '( %s x. %s )' % (CK, M)
            steps.append(self.eq([cst], 'oveq1d', inner, cur)); rhss.append(cur)
            v = Vec(0, [(m, ck)]); T = v.text()
            a = self.eq([self.cc(cur)], 'addlidd', T, cur)
            steps.append(self.eq([a], 'eqcomd', cur, T)); rhss.append(T)
            return self.chain(steps, lhs, rhss), v
        p1, (m1, k1) = v1.prefix()
        t = '( %s x. %s )' % (num.lit_text(k1), mono_text(m1)); P1 = p1.text()
        spread = '( ( %s x. %s ) + ( %s x. %s ) )' % (P1, u, t, u)
        dd = self.eq([self.cc(P1), self.cc(t), self.cc(u)], 'adddird', lhs, spread)
        sP, vP = self.nfmulterm(p1, k, m)
        sT, vT = self.nfmono(k1, m1, k, m)
        cur = '( %s + %s )' % (vP.text(), vT.text())
        o = self.eq([sP, sT], 'oveq12d', spread, cur)
        sM, vM = self.nfadd(vP, vT)
        return self.chain([dd, o, sM], lhs, [spread, cur, vM.text()]), vM

    def nfscale(self, v, c):
        """step proving ( c x. T ) = T', and the scaled Vec"""
        C = num.lit_text(c); T = v.text(); lhs = '( %s x. %s )' % (C, T)
        if c == 0:
            return self.eq([self.cc(T)], 'mul02d', lhs, '0'), Vec(0)
        if c == 1:
            return self.eq([self.cc(T)], 'mullidd', lhs, T), v
        if not v.terms:
            res = Vec(c * v.const)
            return self.closed(num.mul_lit(self.w, c, T), '%s = %s' % (lhs, res.text())), res
        p, (m, k) = v.prefix()
        u = '( %s x. %s )' % (num.lit_text(k), mono_text(m)); P = p.text()
        spread = '( ( %s x. %s ) + ( %s x. %s ) )' % (C, P, C, u)
        dd = self.eq([self.cc(C), self.cc(P), self.cc(u)], 'adddid', lhs, spread)
        sP, vP = self.nfscale(p, c)
        sT, vT = self.nfmulterm(Vec(c), k, m)
        cur = '( %s + %s )' % (vP.text(), vT.text())
        o = self.eq([sP, sT], 'oveq12d', spread, cur)
        sM, vM = self.nfadd(vP, vT)
        return self.chain([dd, o, sM], lhs, [spread, cur, vM.text()]), vM

    def nfmul(self, v1, v2):
        """step proving ( T1 x. T2 ) = T, and the product Vec"""
        T1, T2 = v1.text(), v2.text()
        lhs = '( %s x. %s )' % (T1, T2)
        if not v2.terms:
            flip = '( %s x. %s )' % (T2, T1)
            mc = self.eq([self.cc(T1), self.cc(T2)], 'mulcomd', lhs, flip)
            sS, vS = self.nfscale(v1, v2.const)
            return self.eq([mc, sS], 'eqtrd', lhs, vS.text()), vS
        p2, (m2, k2) = v2.prefix()
        u = '( %s x. %s )' % (num.lit_text(k2), mono_text(m2)); P2 = p2.text()
        spread = '( ( %s x. %s ) + ( %s x. %s ) )' % (T1, P2, T1, u)
        dd = self.eq([self.cc(T1), self.cc(P2), self.cc(u)], 'adddid', lhs, spread)
        sA, vA = self.nfmul(v1, p2)
        sB, vB = self.nfmulterm(v1, k2, m2)
        cur = '( %s + %s )' % (vA.text(), vB.text())
        o = self.eq([sA, sB], 'oveq12d', spread, cur)
        sM, vM = self.nfadd(vA, vB)
        return self.chain([dd, o, sM], lhs, [spread, cur, vM.text()]), vM

    def nfadd(self, v1, v2):
        """step proving ( T1 + T2 ) = T, and the merged Vec"""
        T1, T2 = v1.text(), v2.text()
        lhs = '( %s + %s )' % (T1, T2)
        if not v1.terms and not v2.terms:
            v = Vec(v1.const + v2.const)
            return self.closed(num.add_int(self.w, v1.const, v2.const), '%s = %s' % (lhs, v.text())), v
        if not v1.terms:
            p2, (bm, kb) = v2.prefix(); b = mono_text(bm); u = '( %s x. %s )' % (num.lit_text(kb), b)
            a = self.eq([self.cc(T1), self.cc(p2.text()), self.cc(u)], 'addassd', '( ( %s + %s ) + %s )' % (T1, p2.text(), u), lhs)
            a2 = self.eq([a], 'eqcomd', lhs, '( ( %s + %s ) + %s )' % (T1, p2.text(), u))
            sM, vM = self.nfadd(v1, p2)
            v = Vec(vM.const, vM.terms + [(bm, kb)])
            o = self.eq([sM], 'oveq1d', '( ( %s + %s ) + %s )' % (T1, p2.text(), u), v.text())
            return self.eq([a2, o], 'eqtrd', lhs, v.text()), v
        if not v2.terms:
            p1, (am, ka) = v1.prefix(); a_ = mono_text(am); t = '( %s x. %s )' % (num.lit_text(ka), a_)
            a = self.eq([self.cc(p1.text()), self.cc(t), self.cc(T2)], 'add32d', lhs, '( ( %s + %s ) + %s )' % (p1.text(), T2, t))
            sM, vM = self.nfadd(p1, v2)
            v = Vec(vM.const, vM.terms + [(am, ka)])
            o = self.eq([sM], 'oveq1d', '( ( %s + %s ) + %s )' % (p1.text(), T2, t), v.text())
            return self.eq([a, o], 'eqtrd', lhs, v.text()), v
        p1, (am, ka) = v1.prefix(); p2, (bm, kb) = v2.prefix()
        a_ = mono_text(am); b = mono_text(bm)
        t = '( %s x. %s )' % (num.lit_text(ka), a_); u = '( %s x. %s )' % (num.lit_text(kb), b)
        if a_ > b:
            a = self.eq([self.cc(p1.text()), self.cc(t), self.cc(T2)], 'add32d', lhs, '( ( %s + %s ) + %s )' % (p1.text(), T2, t))
            sM, vM = self.nfadd(p1, v2)
            v = Vec(vM.const, vM.terms + [(am, ka)])
            o = self.eq([sM], 'oveq1d', '( ( %s + %s ) + %s )' % (p1.text(), T2, t), v.text())
            return self.eq([a, o], 'eqtrd', lhs, v.text()), v
        if a_ < b:
            a = self.eq([self.cc(T1), self.cc(p2.text()), self.cc(u)], 'addassd', '( ( %s + %s ) + %s )' % (T1, p2.text(), u), lhs)
            a2 = self.eq([a], 'eqcomd', lhs, '( ( %s + %s ) + %s )' % (T1, p2.text(), u))
            sM, vM = self.nfadd(v1, p2)
            v = Vec(vM.const, vM.terms + [(bm, kb)])
            o = self.eq([sM], 'oveq1d', '( ( %s + %s ) + %s )' % (T1, p2.text(), u), v.text())
            return self.eq([a2, o], 'eqtrd', lhs, v.text()), v
        # same atom: add4d, adddird, closed sum of coefficients
        a4 = self.eq([self.cc(p1.text()), self.cc(t), self.cc(p2.text()), self.cc(u)], 'add4d', lhs,
                     '( ( %s + %s ) + ( %s + %s ) )' % (p1.text(), p2.text(), t, u))
        sM, vM = self.nfadd(p1, p2)
        kk = ka + kb; KA, KB = num.lit_text(ka), num.lit_text(kb)
        dd = self.eq([self.cc(KA), self.cc(KB), self.cc(a_)], 'adddird', '( ( %s + %s ) x. %s )' % (KA, KB, a_), '( %s + %s )' % (t, u))
        dd2 = self.eq([dd], 'eqcomd', '( %s + %s )' % (t, u), '( ( %s + %s ) x. %s )' % (KA, KB, a_))
        c = self.closed(num.add_int(self.w, ka, kb), '( %s + %s ) = %s' % (KA, KB, num.lit_text(kk)))
        tk = '( %s x. %s )' % (num.lit_text(kk), a_)
        c2 = self.eq([c], 'oveq1d', '( ( %s + %s ) x. %s )' % (KA, KB, a_), tk)
        tu = self.eq([dd2, c2], 'eqtrd', '( %s + %s )' % (t, u), tk)
        both = self.eq([sM, tu], 'oveq12d', '( ( %s + %s ) + ( %s + %s ) )' % (p1.text(), p2.text(), t, u), '( %s + %s )' % (vM.text(), tk))
        acc = self.eq([a4, both], 'eqtrd', lhs, '( %s + %s )' % (vM.text(), tk))
        if kk == 0:
            z = self.eq([self.cc(a_)], 'mul02d', tk, '0')
            z2 = self.eq([z], 'oveq2d', '( %s + %s )' % (vM.text(), tk), '( %s + 0 )' % vM.text())
            z3 = self.eq([self.cc(vM.text())], 'addridd', '( %s + 0 )' % vM.text(), vM.text())
            acc = self.eq([acc, z2], 'eqtrd', lhs, '( %s + 0 )' % vM.text())
            return self.eq([acc, z3], 'eqtrd', lhs, vM.text()), vM
        v = Vec(vM.const, vM.terms + [(am, kk)])
        return acc, v


# ---------------------------------------------------------------- linarith

def parse_rel(text):
    parts = split_top(text.split())
    if len(parts) != 3 or parts[1] not in ('<_', '<', '='):
        raise LinError('not a relation A <_ B, A < B or A = B: ' + text)
    return parts[0], parts[1], parts[2]


# ---------------------------------------------------------------- fast path
# The structural prover for the single-hypothesis case (sortie G5).  The
# certificate of a one-hypothesis goal is `D - C = c ( Y - X ) + r`; instead
# of proving that identity by normal forms (120 to 260 steps for a numeral
# slack, V4b's measurement), the goal is decomposed along its own syntax --
# `le2addd` for a sum against a sum, `lemul2ad` for a common literal factor,
# `letrd` through the hypothesis, a closed numeral comparison at the leaves --
# with every sub-goal validated against the certificate arithmetic before a
# step is written.  A goal the rules do not cover returns None and the general
# path runs unchanged.  Off by default (`FASTPATH`, or `fast=True` per call),
# so that every stored worksheet reproduces.

FASTPATH = os.environ.get('LIN_FAST', '') == '1'
FAST_DEPTH = 40


class _Fast:
    def __init__(self, w, ante, cl, lv, hyp, name):
        """hyp: None or (X, rel, Y, step) with rel in `<_`, `<`, `=`"""
        self.w = w; self.ante = ante; self.cl = cl; self.lv = lv; self.name = name
        self.hyp = None; self.f = None; self.fn = {}; self.f0 = Fraction(0)
        self.hstrict = False; self.hkind = None
        if hyp is not None:
            X, rel, Y, step = hyp
            self.hyp = (X, Y, step); self.hrel = rel
            self.hstrict = rel == '<'
            self.hkind = 'eq' if rel == '=' else 'ineq'
            self.setf(X, Y)

    def setf(self, X, Y):
        f = padd(self.poly(Y), self.poly(X), Fraction(-1))
        self.f = f
        self.fn = {k: v for k, v in f.items() if k}
        self.f0 = f.get((), Fraction(0))

    def flip(self):
        """use an equation hypothesis in the other orientation"""
        X, Y, step = self.hyp
        self.hyp = (Y, X, step); self.hkind = 'eqr'; self.setf(Y, X)

    def poly(self, t):
        return poly_form(parse(t, False, self.lv))

    def mult(self, pn):
        """c with pn == c * fn, or None"""
        if not pn:
            return Fraction(0)
        if not self.fn:
            return None
        a = next(iter(pn))
        if a not in self.fn:
            return None
        c = pn[a] / self.fn[a]
        if any(pn.get(k, 0) != c * v for k, v in self.fn.items()) or any(k not in self.fn for k in pn):
            return None
        return c

    def decomp(self, C, D):
        """(c, r) with poly(D) - poly(C) = c f + r, c >= 0, r >= 0; else None"""
        p = padd(self.poly(D), self.poly(C), Fraction(-1))
        pn = {k: v for k, v in p.items() if k}
        c = self.mult(pn)
        if c is None or c < 0:
            return None
        r = p.get((), Fraction(0)) - c * self.f0
        if r < 0:
            return None
        return c, r

    def strict_ok(self, c, r):
        return (c > 0 and self.hstrict) or r > 0

    @staticmethod
    def islit(t):
        v = num.lit_value(t)
        return v is not None and v >= 0

    # -- planning: nothing is written
    def plan(self, C, rel, D, depth=0):
        if depth > FAST_DEPTH:
            return None
        d = self.decomp(C, D)
        if d is None:
            return None
        c, r = d
        strict = rel == '<'
        if strict and not self.strict_ok(c, r):
            return None
        if self.hyp is not None:
            X, Y, step = self.hyp
            if C == X and D == Y:
                return ('hyp',)
        if self.islit(C) and self.islit(D):
            return ('lit',)
        if C == D and not strict:
            return ('refl',)
        if self.hyp is not None and X != Y:
            if C == X:
                rel2 = '<_' if (not strict or self.hstrict) else '<'
                sub = self.plan(Y, rel2, D, depth + 1)
                if sub is not None:
                    return ('transr', sub, rel2)
            if D == Y:
                rel2 = '<_' if (not strict or self.hstrict) else '<'
                sub = self.plan(C, rel2, X, depth + 1)
                if sub is not None:
                    return ('transl', sub, rel2)
        nC, nD = parse(C, False, self.lv), parse(D, False, self.lv)
        combos = [('<', '<_'), ('<_', '<')] if strict else [('<_', '<_')]
        if nC.kind == 'add' and nD.kind == 'add':
            for s1, s2 in combos:
                p1 = self.plan(nC.kids[0].text, s1, nD.kids[0].text, depth + 1)
                p2 = p1 and self.plan(nC.kids[1].text, s2, nD.kids[1].text, depth + 1)
                if p1 and p2:
                    return ('add', p1, p2, s1, s2)
        if self.islit(C) and nD.kind == 'add':
            a = num.lit_value(C)
            ms = []
            for k in nD.kids:
                p = self.poly(k.text)
                ci = self.mult({kk: v for kk, v in p.items() if kk})
                if ci is None or ci < 0:
                    ms = None; break
                ms.append(p.get((), Fraction(0)) - ci * self.f0)
            if ms is not None:
                m1, m2 = ms
                if m1 >= 0 and m2 >= 0:
                    a1 = min(m1, a)
                elif m2 < 0:
                    a1 = a - m2
                else:
                    a1 = m1
                a2 = a - a1
                if a1 >= 0 and a2 >= 0 and a1.denominator == 1 and a2.denominator == 1:
                    for s1, s2 in combos:
                        p1 = self.plan(num.lit_text(a1), s1, nD.kids[0].text, depth + 1)
                        p2 = p1 and self.plan(num.lit_text(a2), s2, nD.kids[1].text, depth + 1)
                        if p1 and p2:
                            return ('litadd', p1, p2, s1, s2, a1, a2)
        if nC.kind == 'add' and self.islit(D):
            b = num.lit_value(D)
            ns = []
            for k in nC.kids:
                p = self.poly(k.text)
                ci = self.mult({kk: -v for kk, v in p.items() if kk})
                if ci is None or ci < 0:
                    ns = None; break
                ns.append(p.get((), Fraction(0)) + ci * self.f0)
            if ns is not None:
                n1, n2 = ns
                b1 = n1 if n1 >= 0 else (0 if b - n2 >= 0 else n1)
                b2 = b - b1
                if b1 >= 0 and b2 >= 0 and b1.denominator == 1 and b2.denominator == 1:
                    for s1, s2 in combos:
                        p1 = self.plan(nC.kids[0].text, s1, num.lit_text(b1), depth + 1)
                        p2 = p1 and self.plan(nC.kids[1].text, s2, num.lit_text(b2), depth + 1)
                        if p1 and p2:
                            return ('addlit', p1, p2, s1, s2, b1, b2)
        for kind in ('scale', 'scaler'):
            if nC.kind == kind and nD.kind == kind and nC.val == nD.val and nC.val > 0:
                sub = self.plan(nC.kids[0].text, rel, nD.kids[0].text, depth + 1)
                if sub is not None:
                    return (kind, sub)
            if self.islit(C) and nD.kind == kind and nD.val > 0:
                a = num.lit_value(C) / nD.val
                sub = self.plan(num.lit_text(a), rel, nD.kids[0].text, depth + 1)
                if sub is not None:
                    return ('lit' + kind, sub, a)
            if nC.kind == kind and self.islit(D) and nC.val > 0:
                b = num.lit_value(D) / nC.val
                sub = self.plan(nC.kids[0].text, rel, num.lit_text(b), depth + 1)
                if sub is not None:
                    return (kind + 'lit', sub, b)
        if nC.kind == 'div' and nD.kind == 'div' and nC.val == nD.val:
            sub = self.plan(nC.kids[0].text, rel, nD.kids[0].text, depth + 1)
            if sub is not None:
                return ('div', sub)
        if self.islit(C) and nD.kind == 'div':
            a = num.lit_value(C) * nD.val
            sub = self.plan(num.lit_text(a), rel, nD.kids[0].text, depth + 1)
            if sub is not None:
                return ('litdiv', sub, a)
        if nC.kind == 'div' and self.islit(D):
            b = num.lit_value(D) * nC.val
            sub = self.plan(nC.kids[0].text, rel, num.lit_text(b), depth + 1)
            if sub is not None:
                return ('divlit', sub, b)
        if nC.kind == 'sub' and nD.kind == 'sub':
            C1, C2 = nC.kids[0].text, nC.kids[1].text; D1, D2 = nD.kids[0].text, nD.kids[1].text
            if C2 == D2:
                sub = self.plan(C1, rel, D1, depth + 1)
                if sub is not None:
                    return ('sub1', sub)
            if C1 == D1:
                sub = self.plan(D2, rel, C2, depth + 1)
                if sub is not None:
                    return ('sub2', sub)
            p1 = self.plan(C1, rel, D1, depth + 1)
            p2 = p1 and self.plan(D2, rel, C2, depth + 1)
            if p1 and p2:
                return ('sub', p1, p2)
        if not strict and nD.kind == 'add':
            if C == nD.kids[0].text:
                sub = self.plan('0', '<_', nD.kids[1].text, depth + 1)
                if sub is not None:
                    return ('addc1', sub)
            if C == nD.kids[1].text:
                sub = self.plan('0', '<_', nD.kids[0].text, depth + 1)
                if sub is not None:
                    return ('addc2', sub)
        if not strict and nC.kind == 'sub' and nC.kids[0].text == D:
            sub = self.plan('0', '<_', nC.kids[1].text, depth + 1)
            if sub is not None:
                return ('subc', sub)
        if nC.kind == 'neg' and nD.kind == 'neg':
            sub = self.plan(nD.kids[0].text, rel, nC.kids[0].text, depth + 1)
            if sub is not None:
                return ('neg', sub)
        return None

    # -- emission
    def out(self, hyps, ref, formula, top):
        f = '( %s -> %s )' % (self.ante, formula)
        if top and self.name == 'qed':
            self.w.qed(hyps, ref, f)
            return 'qed'
        return self.w.s(hyps, ref, f, name=self.name if top else None)

    def st(self, hyps, ref, formula):
        return self.w.s(hyps, ref, '( %s -> %s )' % (self.ante, formula))

    def rr(self, E):
        return self.cl.mem(E, 'RR')

    def closed(self, step, formula):
        return self.st([step], 'a1i', formula)

    def hypstep(self, rel):
        """the step proving X rel Y in the chosen orientation"""
        X, Y, step = self.hyp
        if self.hkind == 'ineq':
            if rel == '<_' and self.hstrict:
                return self.st([self.rr(X), self.rr(Y), step], 'ltled', '%s <_ %s' % (X, Y))
            return step
        if self.hkind == 'eqr':
            step = self.st([step], 'eqcomd', '%s = %s' % (X, Y))
        return self.st([self.rr(X), step], 'eqled', '%s <_ %s' % (X, Y))

    def emit(self, plan, C, rel, D, top=False):
        kind = plan[0]; strict = rel == '<'
        if kind == 'hyp':
            s = self.hypstep(rel)
            return self.rename(s, C, rel, D) if top else s
        if kind == 'lit':
            c = num.le_lit(self.w, C, D, strict)
            return self.out([c], 'a1i', '%s %s %s' % (C, rel, D), top)
        if kind == 'refl':
            return self.out([self.rr(C)], 'leidd', '%s <_ %s' % (C, D), top)
        if kind in ('transr', 'transl'):
            X, Y, step = self.hyp
            sub, rel2 = plan[1], plan[2]
            if kind == 'transr':
                h = self.hypstep('<_' if not strict or not self.hstrict else '<')
                s2 = self.emit(sub, Y, rel2, D)
                hs = [self.rr(C), self.rr(Y), self.rr(D), h, s2]
                if not strict:
                    ref = 'letrd'
                elif self.hstrict:
                    ref = 'ltletrd'
                else:
                    ref = 'lelttrd'
            else:
                h = self.hypstep('<_' if not strict or not self.hstrict else '<')
                s1 = self.emit(sub, C, rel2, X)
                hs = [self.rr(C), self.rr(X), self.rr(D), s1, h]
                if not strict:
                    ref = 'letrd'
                elif self.hstrict:
                    ref = 'lelttrd'
                else:
                    ref = 'ltletrd'
            return self.out(hs, ref, '%s %s %s' % (C, rel, D), top)
        nC, nD = parse(C, False, self.lv), parse(D, False, self.lv)
        ADD = {('<_', '<_'): 'le2addd', ('<', '<_'): 'ltleaddd', ('<_', '<'): 'leltaddd', ('<', '<'): 'lt2addd'}
        if kind == 'add':
            p1, p2, s1, s2 = plan[1:]
            C1, C2 = nC.kids[0].text, nC.kids[1].text; D1, D2 = nD.kids[0].text, nD.kids[1].text
            e1 = self.emit(p1, C1, s1, D1); e2 = self.emit(p2, C2, s2, D2)
            return self.out([self.rr(C1), self.rr(C2), self.rr(D1), self.rr(D2), e1, e2], ADD[(s1, s2)],
                            '%s %s %s' % (C, rel, D), top)
        if kind == 'litadd':
            p1, p2, s1, s2, a1, a2 = plan[1:]
            D1, D2 = nD.kids[0].text, nD.kids[1].text
            A1, A2 = num.lit_text(a1), num.lit_text(a2)
            e1 = self.emit(p1, A1, s1, D1); e2 = self.emit(p2, A2, s2, D2)
            s = self.st([self.rr(A1), self.rr(A2), self.rr(D1), self.rr(D2), e1, e2], ADD[(s1, s2)],
                        '( %s + %s ) %s %s' % (A1, A2, rel, D))
            eq = self.closed(num.add_nat(self.w, a1, a2), '( %s + %s ) = %s' % (A1, A2, C))
            return self.out([eq, s], 'eqbrtrrd', '%s %s %s' % (C, rel, D), top)
        if kind == 'addlit':
            p1, p2, s1, s2, b1, b2 = plan[1:]
            C1, C2 = nC.kids[0].text, nC.kids[1].text
            B1, B2 = num.lit_text(b1), num.lit_text(b2)
            e1 = self.emit(p1, C1, s1, B1); e2 = self.emit(p2, C2, s2, B2)
            s = self.st([self.rr(C1), self.rr(C2), self.rr(B1), self.rr(B2), e1, e2], ADD[(s1, s2)],
                        '%s %s ( %s + %s )' % (C, rel, B1, B2))
            eq = self.closed(num.add_nat(self.w, b1, b2), '( %s + %s ) = %s' % (B1, B2, D))
            return self.out([s, eq], 'breqtrd', '%s %s %s' % (C, rel, D), top)
        if kind in ('scale', 'scaler', 'litscale', 'litscaler', 'scalelit', 'scalerlit'):
            sub = plan[1]
            if kind in ('scale', 'scaler'):
                K = num.lit_text(nC.val); C1, D1 = nC.kids[0].text, nD.kids[0].text
            elif kind.startswith('lit'):
                K = num.lit_text(nD.val); C1, D1 = num.lit_text(plan[2]), nD.kids[0].text
            else:
                K = num.lit_text(nC.val); C1, D1 = nC.kids[0].text, num.lit_text(plan[2])
            e = self.emit(sub, C1, rel, D1)
            left = kind.endswith('scaler') or kind == 'scaler'
            if strict:
                hs = [self.rr(C1), self.rr(D1), self.cl.mem(K, 'RR+'), e]
                ref = 'ltmul1dd' if left else 'ltmul2dd'
            else:
                hs = [self.rr(C1), self.rr(D1), self.rr(K), self.cl.ge0(K), e]
                ref = 'lemul1ad' if left else 'lemul2ad'
            L_ = ('( %s x. %s )' % (C1, K)) if left else ('( %s x. %s )' % (K, C1))
            R_ = ('( %s x. %s )' % (D1, K)) if left else ('( %s x. %s )' % (K, D1))
            if kind in ('scale', 'scaler'):
                return self.out(hs, ref, '%s %s %s' % (C, rel, D), top)
            s = self.st(hs, ref, '%s %s %s' % (L_, rel, R_))
            if kind.startswith('lit'):
                eq = self.closed(num.mul_lits(self.w, C1, K) if left else num.mul_lits(self.w, K, C1),
                                 '%s = %s' % (L_, C))
                return self.out([eq, s], 'eqbrtrrd', '%s %s %s' % (C, rel, D), top)
            eq = self.closed(num.mul_lits(self.w, D1, K) if left else num.mul_lits(self.w, K, D1),
                             '%s = %s' % (R_, D))
            return self.out([s, eq], 'breqtrd', '%s %s %s' % (C, rel, D), top)
        if kind == 'div':
            Q = num.lit_text(nC.val); C1, D1 = nC.kids[0].text, nD.kids[0].text
            e = self.emit(plan[1], C1, rel, D1)
            return self.out([self.rr(C1), self.rr(D1), self.cl.mem(Q, 'RR+'), e],
                            'ltdiv1dd' if strict else 'lediv1dd', '%s %s %s' % (C, rel, D), top)
        if kind == 'litdiv':
            Q = num.lit_text(nD.val); D1 = nD.kids[0].text; A = num.lit_text(plan[2])
            e = self.emit(plan[1], A, rel, D1)
            eq = self.closed(num.mul_lits(self.w, C, Q), '( %s x. %s ) = %s' % (C, Q, A))
            s = self.st([eq, e], 'eqbrtrd', '( %s x. %s ) %s %s' % (C, Q, rel, D1))
            bi = self.st([self.rr(C), self.rr(D1), self.cl.mem(Q, 'RR+')], 'ltmuldivd' if strict else 'lemuldivd',
                         '( ( %s x. %s ) %s %s <-> %s %s %s )' % (C, Q, rel, D1, C, rel, D))
            return self.out([s, bi], 'mpbid', '%s %s %s' % (C, rel, D), top)
        if kind == 'divlit':
            Q = num.lit_text(nC.val); C1 = nC.kids[0].text; B = num.lit_text(plan[2])
            e = self.emit(plan[1], C1, rel, B)
            eq = self.closed(num.mul_lits(self.w, Q, D), '( %s x. %s ) = %s' % (Q, D, B))
            s = self.st([e, eq], 'breqtrrd', '%s %s ( %s x. %s )' % (C1, rel, Q, D))
            bi = self.st([self.rr(C1), self.rr(D), self.cl.mem(Q, 'RR+')], 'ltdivmuld' if strict else 'ledivmuld',
                         '( %s %s %s <-> %s %s ( %s x. %s ) )' % (C, rel, D, C1, rel, Q, D))
            return self.out([s, bi], 'mpbird', '%s %s %s' % (C, rel, D), top)
        if kind in ('sub1', 'sub2', 'sub'):
            C1, C2 = nC.kids[0].text, nC.kids[1].text; D1, D2 = nD.kids[0].text, nD.kids[1].text
            if kind == 'sub1':
                e = self.emit(plan[1], C1, rel, D1)
                return self.out([self.rr(C1), self.rr(D1), self.rr(C2), e], 'ltsub1dd' if strict else 'lesub1dd',
                                '%s %s %s' % (C, rel, D), top)
            if kind == 'sub2':
                e = self.emit(plan[1], D2, rel, C2)
                return self.out([self.rr(D2), self.rr(C2), self.rr(C1), e], 'ltsub2dd' if strict else 'lesub2dd',
                                '%s %s %s' % (C, rel, D), top)
            e1 = self.emit(plan[1], C1, rel, D1); e2 = self.emit(plan[2], D2, rel, C2)
            return self.out([self.rr(C1), self.rr(D2), self.rr(D1), self.rr(C2), e1, e2],
                            'lt2subd' if strict else 'le2subd', '%s %s %s' % (C, rel, D), top)
        if kind in ('addc1', 'addc2'):
            D1, D2 = nD.kids[0].text, nD.kids[1].text
            other = D2 if kind == 'addc1' else D1
            e = self.emit(plan[1], '0', '<_', other)
            bi = self.st([self.rr(C), self.rr(other)], 'addge01d' if kind == 'addc1' else 'addge02d',
                         '( 0 <_ %s <-> %s <_ %s )' % (other, C, D))
            return self.out([e, bi], 'mpbid', '%s <_ %s' % (C, D), top)
        if kind == 'subc':
            C2 = nC.kids[1].text
            e = self.emit(plan[1], '0', '<_', C2)
            bi = self.st([self.rr(D), self.rr(C2)], 'subge02d', '( 0 <_ %s <-> %s <_ %s )' % (C2, C, D))
            return self.out([e, bi], 'mpbid', '%s <_ %s' % (C, D), top)
        if kind == 'neg':
            C1, D1 = nC.kids[0].text, nD.kids[0].text
            e = self.emit(plan[1], D1, rel, C1)
            bi = self.st([self.rr(D1), self.rr(C1)], 'ltnegd' if strict else 'lenegd',
                         '( %s %s %s <-> %s %s %s )' % (D1, rel, C1, C, rel, D))
            return self.out([e, bi], 'mpbid', '%s %s %s' % (C, rel, D), top)
        raise LinError('internal: unknown fast-path rule ' + kind)

    def rename(self, s, C, rel, D):
        """the hypothesis step itself is the goal: give it the requested name"""
        if self.name is None:
            return s
        if self.name == 'qed':
            self.w.qed([s], 'id', '( %s -> %s %s %s )' % (self.ante, C, rel, D))
            return 'qed'
        return self.w.s([s], 'id', '( %s -> %s %s %s )' % (self.ante, C, rel, D), name=self.name)


def fastpath(w, ante, cl, lv, raw, C, grel, D, name):
    """the fast path for at most one hypothesis: the step, or None"""
    if len(raw) > 1:
        return None
    hyp = None
    if raw:
        X, rel, Y, h = raw[0]
        hyp = (X, rel, Y, h)
    F = _Fast(w, ante, cl, lv, hyp, name)
    plan = F.plan(C, grel, D)
    if plan is None and hyp is not None and rel == '=':
        F.flip()
        plan = F.plan(C, grel, D)
    if plan is None:
        return None
    return F.emit(plan, C, grel, D, top=True)


def linarith(w, ante, hyps, goal, leaves=None, closure=None, name=None, products=False, atoms=None,
             cert=None, fast=None):
    cl = closure or Closure(w, ante, leaves or {})
    N = Normalizer(w, ante, cl)
    lv = frozenset(set(getattr(cl, 'atoms', ()) or ()) | set(atoms or ()))
    for a in lv:
        cl.atom(a)
    goal = ' '.join(goal.split())
    if goal.startswith('( %s -> ' % ante):
        goal = strip_ante(goal, ante)
    C, grel, D = parse_rel(goal)
    if grel == '=':
        raise LinError('equality goals are not supported; prove both <_ directions, or use lineq')
    raw = []
    for h in hyps:
        X, rel, Y = parse_rel(strip_ante(formula_of(w, h), ante))
        raw.append((X, rel, Y, h))

    if (FASTPATH if fast is None else fast) and cert is None and not products:
        st_ = fastpath(w, ante, cl, lv, raw, C, grel, D, name)
        if st_ is not None:
            return st_

    def from_cert(Ct, Dt, rw):
        """the supplied certificate over the texts Ct, Dt, RW, checked
        coefficientwise; LinError names the residual when it does not close"""
        nC, nD = parse(Ct, True, lv), parse(Dt, True, lv)
        gform = poly_form(Node('sub', '( %s - %s )' % (Dt, Ct), [nD, nC]))
        items = []; where = {}
        for X, rel, Y, h in rw:
            if rel == '=':
                where[h] = (len(items), len(items) + 1)
                items.append((X, '<_', Y, h, 'eq')); items.append((Y, '<_', X, h, 'eqr'))
            else:
                where[h] = (len(items), None)
                items.append((X, rel, Y, h, 'ineq'))
        forms = [poly_form(Node('sub', '', [parse(Y, True, lv), parse(X, True, lv)]))
                 for X, rel, Y, h, k in items]
        stricts = [rel == '<' for X, rel, Y, h, k in items]
        cs = [Fraction(0)] * len(items)
        pairs = []; triples = []
        for key, c in cert.items():
            c = Fraction(c)
            names = (key,) if isinstance(key, str) else tuple(key)
            idx = []
            for nm in names:
                if nm not in where:
                    raise LinError('certificate names %r, which is not one of the hypotheses %s'
                                   % (nm, [h for X, rel, Y, h in rw]))
                i, j = where[nm]
                if len(names) == 1 and j is not None and c < 0:
                    i, c = j, -c
                idx.append(i)
            if c < 0:
                raise LinError('certificate multiplier of %r is negative' % (key,))
            if len(idx) == 1:
                cs[idx[0]] += c
            else:
                idx = tuple(sorted(idx))
                if len(idx) > MAXDEG:
                    raise LinError('certificate product %r has degree %d, above lin.MAXDEG = %d' % (key, len(idx), MAXDEG))
                tf = forms[idx[0]]; st_ = stricts[idx[0]]
                for a in idx[1:]:
                    tf = pmul(tf, forms[a]); st_ = st_ and stricts[a]
                if len(idx) == 2:
                    pairs.append(idx)
                else:
                    triples.append(idx)
                forms.append(tf); stricts.append(st_); cs.append(c)
        # the pairs must precede the triples in the coefficient vector
        order = list(range(len(items))) + \
                [len(items) + n for n, ix in enumerate(pairs + triples) if len(ix) == 2] + \
                [len(items) + n for n, ix in enumerate(pairs + triples) if len(ix) > 2]
        forms = [forms[i] for i in order]; stricts = [stricts[i] for i in order]; cs = [cs[i] for i in order]
        resid = dict(gform)
        for f, c in zip(forms, cs):
            resid = padd(resid, f, -c)
        r = resid.pop((), Fraction(0))
        if resid or r < 0:
            raise LinError('the supplied certificate does not close: goal - certificate = %s + %s'
                           % (' + '.join('%s * %s' % (num.lit_text(v), mono_text(k)) for k, v in resid.items()) or '0', num.lit_text(r)))
        if grel == '<' and sum(c for c, s_ in zip(cs, stricts) if s_) + r <= 0:
            raise LinError('the supplied certificate has no strict mass for a strict goal')
        return items, forms, stricts, pairs, triples, cs, r, nC, nD, gform

    def search(Ct, Dt, rw):
        """the certificate for `Ct grel Dt` under RW, or LinError.  Nothing is
        written to the worksheet here, so a failed attempt leaves no trace."""
        if cert is not None:
            return from_cert(Ct, Dt, rw)
        nC, nD = parse(Ct, products, lv), parse(Dt, products, lv)
        gform = poly_form(Node('sub', '( %s - %s )' % (Dt, Ct), [nD, nC]))
        # hypotheses: (X, rel, Y, step) and their forms Y - X
        items = []
        for X, rel, Y, h in rw:
            if rel == '=':
                items.append((X, '<_', Y, h, 'eq')); items.append((Y, '<_', X, h, 'eqr'))
            else:
                items.append((X, rel, Y, h, 'ineq'))
        forms = [poly_form(Node('sub', '', [parse(Y, products, lv), parse(X, products, lv)]))
                 for X, rel, Y, h, k in items]
        stricts = [rel == '<' for X, rel, Y, h, k in items]
        pairs = []; triples = []
        try:
            cs, r = certificate(forms, stricts, gform, grel == '<')
        except LinError:
            if not products:
                raise
            # nlinarith-lite: every product of two hypotheses is a further
            # nonnegative fact, and the certificate search is run again over the
            # enlarged set (the sign side conditions come from the closure)
            for i in range(len(items)):
                for j in range(i, len(items)):
                    pf = pmul(forms[i], forms[j])
                    if not pf:
                        continue
                    pairs.append((i, j)); forms.append(pf)
                    stricts.append(stricts[i] and stricts[j])
            try:
                cs, r = certificate(forms, stricts, gform, grel == '<')
            except LinError:
                # degree three and above: products of three or more hypotheses.
                # Only those whose monomials the problem already contains are
                # added -- a product that introduces a monomial occurring
                # nowhere else contributes a row that must cancel to zero -- so
                # an all-linear problem adds none of them and the search does
                # not explode.
                known = set()
                for f in forms + [gform]:
                    known |= set(f)
                base = len(items)
                combos = [(a,) for a in range(base)]
                cs = None
                for deg in range(2, MAXDEG + 1):
                    nxt = []
                    for c in combos:
                        for a in range(c[-1], base):
                            nxt.append(c + (a,))
                    combos = nxt
                    if deg < 3:
                        continue
                    grew = False
                    for c in combos:
                        tf = forms[c[0]]
                        for a in c[1:]:
                            tf = pmul(tf, forms[a])
                        if not tf or not set(tf) <= known:
                            continue
                        if max(len(k) for k in tf) > MAXDEG:
                            continue
                        st_ = stricts[c[0]]
                        for a in c[1:]:
                            st_ = st_ and stricts[a]
                        triples.append(c); forms.append(tf); stricts.append(st_)
                        grew = True
                    if not grew:
                        continue
                    # each degree is searched as soon as it is complete, so a
                    # certificate the previous degree admits is the one found
                    try:
                        cs, r = certificate(forms, stricts, gform, grel == '<')
                        break
                    except LinError:
                        cs = None
                if cs is None:
                    raise
        return items, forms, stricts, pairs, triples, cs, r, nC, nD, gform

    goal_C, goal_D = C, D
    powers = None
    try:
        items, forms, stricts, pairs, triples, cs, r, nC, nD, gform = search(C, D, raw)
    except LinError:
        # an integer power is an atom to the search; write it out as a product
        # and try once more.  The expansion reaches the worksheet only when the
        # second search succeeds, so nothing is written on the failing path.
        eC, eD = expand_pow(C, lv), expand_pow(D, lv)
        erw = [(expand_pow(X, lv), rel, expand_pow(Y, lv), h) for X, rel, Y, h in raw]
        if (eC, eD, erw) == (C, D, raw):
            raise
        items, forms, stricts, pairs, triples, cs, r, nC, nD, gform = search(eC, eD, erw)
        powers = (eC, eD, erw)

    if powers is not None:
        eC, eD, erw = powers
        rules = powrules(w, ante, [C, D] + [t for X, rel, Y, h in raw for t in (X, Y)], cl, lv)
        gen = congr.StepGen('p')
        conv = {}

        def expanded(t, et):
            """the step proving ( ante -> t = et ), memoized"""
            if t == et:
                return None
            if t not in conv:
                stx, got = powconv(w, ante, t, rules, gen)
                if stx is None or got != et:
                    raise LinError('internal: the expansion of %s is %s, not %s' % (t, got, et))
                conv[t] = stx
            return conv[t]

        def carry(step, X, Y, eX, eY, rel):
            """the hypothesis step, restated over the expanded texts"""
            sx, sy = expanded(X, eX), expanded(Y, eY)
            if sx is None and sy is None:
                return step
            if sx is None:
                sx = w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, X, eX))
            if sy is None:
                sy = w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, Y, eY))
            ref = '3eqtr3d' if rel == '=' else '3brtr3d'
            op = '=' if rel == '=' else rel
            return w.s([step, sx, sy], ref, '( %s -> %s %s %s )' % (ante, eX, op, eY))

        raw2 = []
        for (X, rel, Y, h), (eX, _, eY, _) in zip(raw, erw):
            raw2.append((eX, rel, eY, carry(h, X, Y, eX, eY, rel)))
        items = []
        for X, rel, Y, h in raw2:
            if rel == '=':
                items.append((X, '<_', Y, h, 'eq')); items.append((Y, '<_', X, h, 'eqr'))
            else:
                items.append((X, rel, Y, h, 'ineq'))
        gC, gD = expanded(C, eC), expanded(D, eD)
        C, D = eC, eD

    def st(hyps_, ref, f):
        return w.s(hyps_, ref, '( %s -> %s )' % (ante, f))

    base_memo = {}

    def base(idx):
        """(diff text, step proving 0 <_ diff or 0 < diff, strict)"""
        if idx in base_memo:
            return base_memo[idx]
        X, rel, Y, h, kind = items[idx]
        rX, rY = cl.mem(X, 'RR'), cl.mem(Y, 'RR')
        diff = '( %s - %s )' % (Y, X)
        if kind == 'eq':
            le = st([rX, h], 'eqled', '%s <_ %s' % (X, Y))
        elif kind == 'eqr':
            e2 = st([h], 'eqcomd', '%s = %s' % (X, Y))
            le = st([rX, e2], 'eqled', '%s <_ %s' % (X, Y))
        else:
            le = h
        if rel == '<':
            bi = st([rX, rY], 'posdifd', '( %s < %s <-> 0 < %s )' % (X, Y, diff))
            b = st([le, bi], 'mpbid', '0 < %s' % diff)
        else:
            bi = st([rY, rX], 'subge0d', '( 0 <_ %s <-> %s <_ %s )' % (diff, X, Y))
            b = st([le, bi], 'mpbird', '0 <_ %s' % diff)
        cl.have(diff, 'gt0' if rel == '<' else 'ge0', b)
        base_memo[idx] = (diff, b, rel == '<')
        return base_memo[idx]

    terms = []   # (node, text, step, strict)

    def addterm(node, text, step, strict, c):
        if c == 1:
            terms.append((node, text, step, strict)); return
        K = num.lit_text(c); tt = '( %s x. %s )' % (K, text)
        rd = cl.mem(text, 'RR')
        if strict:
            s2 = st([cl.mem(K, 'RR'), rd, cl.gt0(K), step], 'mulgt0d', '0 < %s' % tt)
        else:
            s2 = st([cl.mem(K, 'RR'), rd, cl.ge0(K), step], 'mulge0d', '0 <_ %s' % tt)
        cl.have(tt, 'gt0' if strict else 'ge0', s2)
        terms.append((Node('scale', tt, [node], val=c), tt, s2, strict))

    prod_memo = {}

    def mulfact(d1, s1, k1, d2, s2, k2):
        """(text, step, strict) for the product of two nonnegative facts"""
        pt = '( %s x. %s )' % (d1, d2)
        if pt in prod_memo:
            return prod_memo[pt]
        r1, r2 = cl.mem(d1, 'RR'), cl.mem(d2, 'RR')
        if k1 and k2:
            ps = st([r1, r2, s1, s2], 'mulgt0d', '0 < %s' % pt); pstrict = True
        else:
            ps = st([r1, r2, cl.ge0(d1), cl.ge0(d2)], 'mulge0d', '0 <_ %s' % pt); pstrict = False
        cl.have(pt, 'gt0' if pstrict else 'ge0', ps)
        prod_memo[pt] = (pt, ps, pstrict)
        return prod_memo[pt]

    for idx in range(len(items)):
        if cs[idx] == 0:
            continue
        X, rel, Y = items[idx][0], items[idx][1], items[idx][2]
        diff, b, strict = base(idx)
        dnode = Node('sub', diff, [parse(Y, products or cert is not None, lv), parse(X, products or cert is not None, lv)])
        addterm(dnode, diff, b, strict, cs[idx])
    for n, (i, j) in enumerate(pairs):
        c = cs[len(items) + n]
        if c == 0:
            continue
        di, bi_, si = base(i); dj, bj, sj = base(j)
        pt, pst, pstrict = mulfact(di, bi_, si, dj, bj, sj)
        pnode = Node('mul', pt, [parse(di, True, lv), parse(dj, True, lv)])
        addterm(pnode, pt, pst, pstrict, c)
    for n, combo in enumerate(triples):
        c = cs[len(items) + len(pairs) + n]
        if c == 0:
            continue
        pt, pst, pstrict = base(combo[0])
        pnode = parse(pt, products or cert is not None, lv)
        for a in combo[1:]:
            dj, bj, sj = base(a)
            pt, pst, pstrict = mulfact(pt, pst, pstrict, dj, bj, sj)
            pnode = Node('mul', pt, [pnode, parse(dj, products or cert is not None, lv)])
        addterm(pnode, pt, pst, pstrict, c)
    if r > 0:
        R = num.lit_text(r)
        terms.append((Node('lit', R, val=r), R, cl.gt0(R), True))
    if not terms:
        terms.append((Node('lit', '0', val=Fraction(0)), '0', cl.ge0('0'), False))
    # sum
    node, text, step, strict = terms[0]
    for n2, t2, s2, k2 in terms[1:]:
        tot = '( %s + %s )' % (text, t2)
        lemma = {(False, False): 'addge0d', (False, True): 'addgegt0d', (True, False): 'addgtge0d', (True, True): 'addgt0d'}[(strict, k2)]
        step = st([cl.mem(text, 'RR'), cl.mem(t2, 'RR'), step, s2], lemma, '%s %s' % ('0 <' if (strict or k2) else '0 <_', tot))
        node = Node('add', tot, [node, n2]); text = tot; strict = strict or k2
    # identity S = ( D - C )
    dnode = Node('sub', '( %s - %s )' % (D, C), [nD, nC])
    d = 1
    for q in denominators(node) | denominators(dnode):
        d = lcm(d, q)
    d = Fraction(d)
    sS, vS = N.nf(node, d); sG, vG = N.nf(dnode, d)
    if vS.text() != vG.text():
        raise LinError('internal: normal forms differ\n  %s\n  %s' % (vS.text(), vG.text()))
    eq = st([sS, sG], 'eqtr4d', '%s = %s' % (scaled(text, d), scaled(dnode.text, d)))
    if d != 1:
        td = num.lit_text(d)
        eq = st([cl.mem(text, 'CC'), cl.mem(dnode.text, 'CC'), cl.mem(td, 'CC'), cl.ne0(td), eq], 'mulcanad', '%s = %s' % (text, dnode.text))
    fin = st([step, eq], 'breqtrd', '%s %s' % ('0 <' if strict else '0 <_', dnode.text))
    rC, rD = cl.mem(C, 'RR'), cl.mem(D, 'RR')
    if grel == '<':
        if not strict:
            raise LinError('internal: strict goal from a non-strict sum')
        bi = st([rC, rD], 'posdifd', '( %s < %s <-> 0 < %s )' % (C, D, dnode.text))
        hy, ref = [fin, bi], 'mpbird'
    else:
        if strict:
            z = st([], '0red', '0 e. RR')
            fin = st([z, cl.mem(dnode.text, 'RR'), fin], 'ltled', '0 <_ %s' % dnode.text)
        bi = st([rD, rC], 'subge0d', '( 0 <_ %s <-> %s <_ %s )' % (dnode.text, C, D))
        hy, ref = [fin, bi], 'mpbid'
    if powers is not None and (gC is not None or gD is not None):
        # the certificate proved the expanded goal; restate the one asked for
        e1 = gC if gC is not None else w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, goal_C, C))
        e2 = gD if gD is not None else w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, goal_D, D))
        mid = w.s(hy, ref, '( %s -> %s %s %s )' % (ante, C, grel, D))
        hy, ref = [mid, e1, e2], '3brtr4d'
    if name == 'qed':
        w.qed(hy, ref, '( %s -> %s )' % (ante, goal))
        return 'qed'
    return w.s(hy, ref, '( %s -> %s )' % (ante, goal), name=name)


def nlinarith(w, ante, hyps, goal, leaves=None, closure=None, name=None, atoms=None, cert=None, fast=None):
    """linarith, and, if no linear certificate exists, the same search over
    the hypotheses together with every product of a pair of them, then with
    every product of a triple (an `nlinarith`-lite: a product of nonnegative
    facts is nonnegative, and the resulting monomials are treated as further
    atoms).  The triples are restricted to the monomials the problem already
    contains, so a problem of degree at most two adds none of them."""
    return linarith(w, ante, hyps, goal, leaves=leaves, closure=closure, name=name,
                    products=True, atoms=atoms, cert=cert, fast=fast)


def lineq(w, ante, lhs, rhs, hyps=(), leaves=None, closure=None, name=None,
          products=False, atoms=None, fast=None):
    """( ante -> lhs = rhs ) for two linear real expressions, by the two
    inequalities and `letri3d`.  `products=True` runs the nonlinear search on
    each of them."""
    cl = closure or Closure(w, ante, leaves or {})
    a = linarith(w, ante, list(hyps), '%s <_ %s' % (lhs, rhs), closure=cl,
                 products=products, atoms=atoms, fast=fast)
    b = linarith(w, ante, list(hyps), '%s <_ %s' % (rhs, lhs), closure=cl,
                 products=products, atoms=atoms, fast=fast)
    both = '( %s <_ %s /\\ %s <_ %s )' % (lhs, rhs, rhs, lhs)
    j = w.s([a, b], 'jca', '( %s -> %s )' % (ante, both))
    bi = w.s([cl.mem(lhs, 'RR'), cl.mem(rhs, 'RR')], 'letri3d',
             '( %s -> ( %s = %s <-> %s ) )' % (ante, lhs, rhs, both))
    f = '( %s -> %s = %s )' % (ante, lhs, rhs)
    if name == 'qed':
        w.qed([j, bi], 'mpbird', f)
        return 'qed'
    return w.s([j, bi], 'mpbird', f, name=name)
