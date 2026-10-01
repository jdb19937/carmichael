"""Distinct-variable audit for the labels a worksheet cites.

`carmichael.mm` carries no `$d` of its own, so a citation whose distinct-variable
conditions are not satisfiable by the caller's letters is a dead end: the letters
have to be chosen before the mathematics is written.  This module reads the `$d`
blocks of `set.mm` (and of our own database) and answers the three questions a
sortie asks.

    import dv
    print(dv.report(['fsumless', 'fsumf1o', 'fsumxp'], binds='k j'))
      # per lemma, the letters each instantiated class variable forbids, the
      # letters that survive every lemma, and a flag on every bound letter of
      # the caller that one of them forbids
    dv.free_letters(['cvgcmp', 'isumle'])          # ['a', 'b', 'c', ...]
    dv.check('fvmptg', {'x': 't', 'A': A, 'B': B, 'C': C})
      # [] or a list of violations; dv.assertok raises DVError on the first
    dv.worksheet('worksheets/foo.mmp')             # the labels a worksheet cites

The conditions of the OPTIONAL frame are reported with the mandatory ones,
in parentheses: a lemma's proof dummies are enforced by mmj2 at unification,
and the theorem a proof writes carries them onward to its own consumers.

A `$d x A` forbids `x` in the expression substituted for `A` **whatever the
occurrence**: a bound `A. x` inside it violates the condition exactly as a free
occurrence does.  `check` tests token occurrence, so it sees both.

Run it on a worksheet:

    python3 tools/dv.py worksheets/LABEL.mmp [-b 'k j']
    python3 tools/dv.py -l fsumless fsumf1o fsumxp [-b 'k j']
"""
import os, pickle, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DB = os.path.join(ROOT, os.environ.get('MM_DB', 'carmichael.mm'))
CACHE = os.path.join(ROOT, 'scratch', 'dv-%s.idx' % os.path.basename(DB).replace('.mm', ''))

SETVAR, CLASS, WFF = 'setvar', 'class', 'wff'


class DVError(Exception):
    pass


class Frame(object):
    """the distinct-variable frame of one assertion.  `kind` is shared by every
    frame of a database (set.mm declares its `$f` once, at the outermost scope);
    a frame that shadows one carries the difference in `local`."""
    __slots__ = ('label', 'stmt', 'hyps', 'dvs', 'local', 'mand', '_kind')

    def __init__(self, label, stmt, hyps, dvs, kind, local, mand):
        self.label = label      # the label
        self.stmt = stmt        # the statement's tokens
        self.hyps = hyps        # the $e hypotheses' token lists, in order
        self.dvs = dvs          # set of frozenset pairs of variable names
        self._kind = kind       # the shared variable -> 'setvar'/'class'/'wff'
        self.local = local      # the entries of this scope that differ
        self.mand = mand        # the variables of the mandatory frame

    @property
    def kind(self):
        if not self.local:
            return self._kind
        k = dict(self._kind); k.update(self.local); return k

    def kindof(self, v):
        return self.local.get(v) or self._kind.get(v)

    def setvars(self, mandatory_only=False):
        vs = self.mand if mandatory_only else set(self._kind) | set(self.local)
        return sorted(v for v in vs if self.kindof(v) == SETVAR)

    def clsvars(self):
        """the class and wff variables of the mandatory frame, in the order
        they first occur (these are what a caller instantiates)"""
        out, seen = [], set()
        for t in list(self.stmt) + [t for h in self.hyps for t in h]:
            if t in self.mand and t not in seen and self.kindof(t) in (CLASS, WFF):
                seen.add(t); out.append(t)
        return out

    def forbids(self, v):
        """(mandatory setvars, dummy setvars) that `$d` forbids in v"""
        m, d = set(), set()
        for pair in self.dvs:
            if v not in pair:
                continue
            other = [t for t in pair if t != v]
            if not other:
                continue
            o = other[0]
            if self.kindof(o) != SETVAR:
                continue
            (m if o in self.mand else d).add(o)
        return sorted(m), sorted(d)


# ------------------------------------------------------------------ the index

def _source(path, seen=None):
    """the text of a database with its `$[ ... $]` includes expanded (they
    resolve against carmichael/metamath/, as every tool runs from there)"""
    seen = seen if seen is not None else set()
    path = os.path.abspath(path)
    if path in seen:
        return ''
    seen.add(path)
    txt = open(path).read()
    txt = re.sub(r'\$\(.*?\$\)', ' ', txt, flags=re.S)          # comments
    txt = re.sub(r'\$=.*?\$\.', ' $.', txt, flags=re.S)         # proofs
    out = []
    pos = 0
    for m in re.finditer(r'\$\[\s*(\S+)\s*\$\]', txt):
        out.append(txt[pos:m.start()])
        out.append(_source(os.path.join(ROOT, m.group(1)), seen))
        pos = m.end()
    out.append(txt[pos:])
    return ' '.join(out)


def _build(path):
    toks = [sys.intern(t) for t in _source(path).split()]
    frames = {}
    shared = {}          # every $f type ever declared, the common case
    kstack = [{}]        # $f types
    dstack = [set()]     # $d pairs
    estack = [[]]        # $e hypotheses, as (label, tokens)
    i, n = 0, len(toks)
    while i < n:
        t = toks[i]
        if t == '${':
            kstack.append({}); dstack.append(set()); estack.append([]); i += 1; continue
        if t == '$}':
            kstack.pop(); dstack.pop(); estack.pop(); i += 1; continue
        if t in ('$v', '$c'):
            while toks[i] != '$.':
                i += 1
            i += 1; continue
        if t == '$d':
            j = i + 1; vs = []
            while toks[j] != '$.':
                vs.append(toks[j]); j += 1
            for a in range(len(vs)):
                for b in range(a + 1, len(vs)):
                    dstack[-1].add(frozenset((vs[a], vs[b])))
            i = j + 1; continue
        # a labelled statement: LABEL $f/$e/$a/$p ... $.
        if i + 1 < n and toks[i + 1].startswith('$') and toks[i + 1] in ('$f', '$e', '$a', '$p'):
            label, key = toks[i], toks[i + 1]
            j = i + 2; body = []
            while toks[j] != '$.':
                body.append(toks[j]); j += 1
            if key == '$f':
                kstack[-1][body[1]] = body[0]
                shared.setdefault(body[1], body[0])
            elif key == '$e':
                estack[-1].append((label, body))
            else:
                kind = {}
                for d in kstack:
                    kind.update(d)
                local = dict((v, t) for v, t in kind.items() if shared.get(v) != t)
                dvs = set()
                for d in dstack:
                    dvs |= d
                hyps = [b for e in estack for (_, b) in e]
                mand = set()
                for seq in [body] + hyps:
                    for tk in seq:
                        if tk in kind:
                            mand.add(tk)
                frames[label] = Frame(label, body, hyps, frozenset(dvs), shared, local, mand)
            i = j + 1; continue
        i += 1
    return shared, frames


_FRAMES = None


def frames(db=None):
    """the frame index, cached under scratch/ against the database's mtime"""
    global _FRAMES
    if _FRAMES is not None and db is None:
        return _FRAMES
    path = db or DB
    stamp = []
    for p in (path, os.path.join(ROOT, 'set.mm-repo', 'set.mm'), os.path.join(ROOT, 'carmichael.mm')):
        try:
            st = os.stat(p); stamp.append((os.path.basename(p), st.st_size, int(st.st_mtime)))
        except OSError:
            pass
    stamp = tuple(stamp)
    cache = CACHE if db is None else os.path.join(
        ROOT, 'scratch', 'dv-%s.idx' % os.path.basename(path).replace('.mm', ''))
    try:
        with open(cache, 'rb') as f:
            got, shared, fr = pickle.load(f)
        for x in fr.values():
            x._kind = shared
        if got == stamp:
            if db is None:
                _FRAMES = fr
            return fr
    except Exception:
        pass
    shared, fr = _build(path)
    try:
        with open(cache, 'wb') as f:
            pickle.dump((stamp, shared, fr), f, 2)
    except Exception:
        pass
    if db is None:
        _FRAMES = fr
    return fr


def frame(label, db=None):
    fr = frames(db).get(label)
    if fr is None:
        raise DVError('no assertion %s in %s' % (label, os.path.basename(db or DB)))
    return fr


# ------------------------------------------------------------------ the report

def _letters():
    return [chr(c) for c in range(ord('a'), ord('z') + 1)]


def _shared(db=None):
    """the database's variable -> kind map"""
    fr = frames(db)
    for x in fr.values():
        return x.kind
    return {}


def free_letters(labels, db=None):
    """the single lower-case letters no cited lemma forbids anywhere"""
    bad = set()
    for lab in labels:
        try:
            f = frame(lab, db)
        except DVError:
            continue
        for v in f.clsvars():
            m, d = f.forbids(v)
            bad |= set(m) | set(d)
    return [c for c in _letters() if c not in bad]


def report(labels, binds=(), db=None):
    """C3's table: per lemma, the letters each instantiated class variable
    forbids (the lemma's proof dummies in parentheses), the letters that survive
    every lemma, and a flag on every letter the caller binds that some lemma
    forbids.  `<<<` is a letter no lemma binds itself, so the caller's binder
    falls in a class variable and mmj2 will refuse; `?` is one of the lemma's
    own binders, which is fine where the caller's letter IS that binder and a
    violation where the caller's antecedent, range or body binds it as well."""
    if isinstance(binds, str):
        binds = binds.split()
    binds = list(binds)
    rows, missing, hard, soft = [], [], set(), set()
    for lab in labels:
        try:
            f = frame(lab, db)
        except DVError:
            missing.append(lab); continue
        cells = []
        for v in f.clsvars():
            m, d = f.forbids(v)
            if not m and not d:
                continue
            txt = ' '.join(m)
            if d:
                txt += (' ' if txt else '') + '(' + ' '.join(d) + ')'
            cells.append((v, txt, set(m) | set(d)))
        rows.append((lab, f, cells))
    if not rows:
        return 'no assertion of ' + ' '.join(labels) + ' is in the database'
    out = []
    w = max([len(l) for l, _, _ in rows] + [6])
    out.append('%-*s  %-8s %s' % (w, 'lemma', 'binds', 'forbidden in each instantiated variable'))
    out.append('%-*s  %-8s %s' % (w, '-' * w, '-' * 8, '-' * 40))
    for lab, f, cells in rows:
        own = f.setvars(mandatory_only=True)
        if not cells:
            out.append('%-*s  %-8s %s' % (w, lab, ' '.join(own), '--'))
            continue
        first = True
        for v, txt, bad in cells:
            h = sorted((bad & set(binds)) - set(own))
            q = sorted(bad & set(binds) & set(own))
            hard |= set(h); soft |= set(q)
            mark = ('  <<< ' + ' '.join(h)) if h else ''
            mark += ('  ? ' + ' '.join(q)) if q else ''
            out.append('%-*s  %-8s %s: %s%s'
                       % (w, lab if first else '', ' '.join(own) if first else '', v, txt, mark))
            first = False
    if missing:
        out.append('')
        out.append('not in the database: ' + ' '.join(missing))
    free = free_letters([l for l, _, _ in rows], db)
    out.append('')
    out.append('letters that survive every lemma: ' + ' '.join(free))
    if hard:
        out.append('BOUND BY THE CALLER AND FORBIDDEN: ' + ' '.join(sorted(hard)))
        out.append('  (a bound occurrence violates a $d exactly as a free one does:')
        out.append('   rename the binder, or move the quantifier outside the substitution)')
    if soft:
        out.append('the caller binds ' + ' '.join(sorted(soft)) + ', which the lemma binds '
                   'too: check that')
        out.append('  nothing else the lemma is instantiated with binds ' + ' '.join(sorted(soft)))
    if binds and not hard and not soft:
        out.append('the caller binds ' + ' '.join(binds) + ': no lemma forbids any of them')
    return '\n'.join(out)


# ------------------------------------------------------------- the hard check

def occurs(var, text):
    """does `var` occur as a token of `text`?  Bound occurrences count."""
    return var in text.split()


def variables(text, db=None):
    """the tokens of `text` that the database declares as variables"""
    k = _shared(db)
    return [t for t in text.split() if t in k]


def check(label, sub, db=None):
    """the violations of `label`'s $d under the substitution `sub`
    (the lemma's variable -> the text the caller puts there).  A pair whose
    two texts share a variable is a violation, whether the shared variable is
    free or bound in them.  A variable `sub` does not mention is not checked,
    except that a proof dummy of the lemma is reported as unchecked."""
    f = frame(label, db)
    bad = []
    for pair in sorted(f.dvs, key=lambda p: sorted(p)):
        u, v = sorted(pair)
        if u not in sub and v not in sub:
            continue
        su, sv = sub.get(u), sub.get(v)
        if su is None or sv is None:
            known, un = (u, v) if su is not None else (v, u)
            txt = su if su is not None else sv
            if f.kindof(un) == SETVAR and un not in f.mand and un in variables(txt, db):
                bad.append('%s: $d %s %s violated -- %s is a proof dummy of %s '
                           'and %s := %s contains it'
                           % (label, u, v, un, label, known, txt))
            continue
        shared = sorted(set(variables(su, db)) & set(variables(sv, db)))
        if shared:
            bad.append('%s: $d %s %s violated -- %s := %s and %s := %s share %s'
                       % (label, u, v, u, su, v, sv, ' '.join(shared)))
    return bad


def assertok(label, sub, db=None):
    bad = check(label, sub, db)
    if bad:
        raise DVError('\n'.join(bad))
    return True


# ----------------------------------------------------------------- worksheets

STEP = re.compile(r'^(?:h?[A-Za-z0-9_]+|qed):([^:]*):(\S*)')


def worksheet(path):
    """the labels a worksheet cites, in order of first occurrence"""
    src = open(path).read() if os.path.exists(path) else path
    out, seen = [], set()
    for line in src.splitlines():
        if line.startswith('*') or line.startswith('$'):
            continue
        m = STEP.match(line.strip())
        if not m:
            continue
        ref = m.group(2)
        if ref and ref not in seen:
            seen.add(ref); out.append(ref)
    return out


BINDHEAD = ('A.', 'E.', 'E!', 'E*', 'sum_', 'prod_', 'U_', '|^|_', 'X_', 'iota',
            'iota_', 'rec')


def _islet(t):
    return len(t) == 1 and t.isalpha()


def binders(src):
    """the set variables a worksheet binds: quantifiers, mappings, sums,
    products, indexed unions, class abstractions and integrals.  A letter bound
    anywhere in the proof counts, scratch steps included -- that is what enters
    the theorem's generated `$d` and blocks a later instantiation."""
    if os.path.exists(src):
        src = open(src).read()
    toks = src.split()
    out = set()
    for i, t in enumerate(toks):
        nxt = toks[i + 1] if i + 1 < len(toks) else ''
        if t in BINDHEAD and _islet(nxt):
            out.add(nxt)
        elif t == '_d' and _islet(nxt):            # S. A B _d x
            out.add(nxt)
        elif t == '{' and _islet(nxt) and nxt.islower():
            out.add(nxt)
        elif t == '|->':
            # walk back to the opening paren of the mapping, collecting the
            # binders of an `mpt` or an `mpo` at that depth
            depth = 0
            for j in range(i - 1, -1, -1):
                u = toks[j]
                if u == ')':
                    depth += 1
                elif u == '(':
                    if depth == 0:
                        break
                    depth -= 1
                elif depth == 0 and _islet(u) and u.islower() and \
                        toks[j + 1] in ('e.', ',', '|->'):
                    out.add(u)
    return sorted(out)


def statement(src):
    """the formula a worksheet's qed step proves"""
    if os.path.exists(src):
        src = open(src).read()
    for line in src.splitlines():
        if line.startswith('qed'):
            return line.split('|-', 1)[1].strip() if '|-' in line else ''
    return ''


def dummies(src):
    """the letters the worksheet binds only in its proof.  These enter the
    theorem's generated `$d` exactly as the statement's own binders do, so a
    consumer that instantiates a class variable of the theorem must avoid them
    as well."""
    st = set(statement(src).split())
    return [b for b in binders(src) if b not in st]


def lint(target, binds=None, db=None):
    """the report for a worksheet path (labels and binders read off it) or for
    an explicit list of labels"""
    if isinstance(target, (list, tuple)):
        return report(list(target), binds or (), db)
    labels = worksheet(target)
    b = binds if binds is not None else binders(target)
    out = [report(labels, b, db), '']
    d = dummies(target)
    out.append('this worksheet binds: ' + (' '.join(binders(target)) or '--'))
    out.append('  of which only in the proof: ' + (' '.join(d) or '--'))
    out.append('  a consumer instantiating a class variable of this theorem must')
    out.append('  avoid every letter on the first line, the proof dummies included')
    return '\n'.join(out)


def main(argv):
    args = list(argv)
    binds = None
    if '-b' in args:
        k = args.index('-b'); binds = args[k + 1].split(); del args[k:k + 2]
    if args and args[0] == '-l':
        print(report(args[1:], binds or ()))
        return 0
    if not args:
        print(__doc__); return 1
    for a in args:
        print('== ' + a)
        print(lint(a, binds))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
