"""Sortie BM: shared generator helpers (label index over set.mm + carmichael.mm + sorties/bm.mm,
the mathbox gate, `ap` for closed lemmas, antecedent unpacking)."""
import sys, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from tm import W
import num, lin, cl as _cl, congr
from cl import lift, split_imp, Closure, formula_of, strip_ante, split_top
from bmlib import *
import bmlib
import mm as _MM
lin.FASTPATH = True
lin.MAXDEG = 6
ROOT = os.path.abspath(bmlib.ROOT)      # `from bmlib import *` rebinds HERE
only = [a for a in sys.argv[1:] if not a.startswith('-')]

_IDX = None
_MBOX = None


def _load():
    global _IDX
    if _IDX is None:
        _IDX = {}
        pth = os.path.join(ROOT, 'scratch', 'assertions-carmichael.idx')
        for l in open(pth):
            a = l.rstrip('\n').split(' ', 2)
            if len(a) == 3:
                _IDX[a[0]] = a[2]
    return _IDX


def thm(lab):
    """the assertion text of LAB with its |- (frozen S first, then the index, then the sortie file)"""
    if lab in S:
        return '|- ' + S[lab]
    idx = _load()
    if lab in idx:
        return idx[lab]
    return '|- ' + stmt(lab)


def known(lab):
    try:
        thm(lab)
        return True
    except KeyError:
        return False


def refs_of(w):
    out = set()
    for l in w.lines:
        head = l.split('|-')[0] if '|-' in l else l
        parts = head.split(':')
        if len(parts) >= 3:
            ref = parts[2].strip()
            if ref and ref not in ('idi',) and not ref.startswith(w.label + '.'):
                out.add(ref)
    return out


def go(w):
    """label existence + mathbox gate on every cited label, then add (unless the command line
    names other labels)"""
    global _MBOX
    if only and w.label not in only:
        return True
    if _MBOX is None:
        _MBOX = _MM.mathbox_labels(open(_MM.SETMM).read())
    refs = refs_of(w)
    missing = sorted(r for r in refs if not known(r))
    if missing:
        print('MISSING LABELS', w.label, missing)
        w.write()
        return False
    bad = sorted(r for r in refs if r in _MBOX)
    if bad:
        print('MATHBOX CITATION', w.label, bad)
        return False
    return w.run()


def _conj_tree(text):
    toks = text.split()
    if toks[0] == '(' and toks[-1] == ')':
        inner = toks[1:-1]
        depth = 0; cut = []
        for i, t in enumerate(inner):
            if t in ('(', '{', '<.', '<"'):
                depth += 1
            elif t in (')', '}', '>.', '">'):
                depth -= 1
            elif t == '/\\' and depth == 0:
                cut.append(i)
        if cut and len(cut) in (1, 2):
            parts = []; prev = 0
            for c_ in cut:
                parts.append(' '.join(inner[prev:c_])); prev = c_ + 1
            parts.append(' '.join(inner[prev:]))
            return ('and', [_conj_tree(p_) for p_ in parts])
    return ('leaf', text)


def _flat(node):
    if node[0] == 'leaf':
        return node[1]
    return '( ' + ' /\\ '.join(_flat(k) for k in node[1]) + ' )'


def ap(w, ante, hyps, lab, f, sub=None):
    """apply LAB to hyps (steps proving ( ante -> leaf_i ), in the order of the leaves of LAB's
    antecedent) giving ( ante -> f ).  Deduction-form labels ( '( ph ->' ) are cited directly;
    closed ones get the antecedent tree rebuilt with jca/3jca and syl.  `sub` (token map)
    is applied to the antecedent read from the statement."""
    t = thm(lab).replace('|- ', '', 1)
    if t.startswith('( ph -> '):
        return w.s(hyps, lab, '( %s -> %s )' % (ante, f))
    if not hyps:
        c = w.s([], lab, f)
        return w.s([c], 'a1i', '( %s -> %s )' % (ante, f))
    a, _ = split_imp(t)
    if sub:
        a = ' '.join(sub.get(x, x) for x in a.split())
    tree = _conj_tree(a)
    hyps = list(hyps)
    pos = [0]

    def nodetext(node):
        return node[1] if node[0] == 'leaf' else _flat(node)

    def build(node):
        # a supplied step proving this whole node is used as is (a hypothesis may cover a group)
        if pos[0] < len(hyps):
            f = strip_ante(formula_of(w, hyps[pos[0]]), ante)
            if f == nodetext(node):
                pos[0] += 1
                return hyps[pos[0] - 1]
        if node[0] == 'leaf':
            if pos[0] >= len(hyps):
                raise ValueError('ap %s: no step for leaf %s' % (lab, node[1][:80]))
            pos[0] += 1
            return hyps[pos[0] - 1]
        kids = [build(k) for k in node[1]]
        fs = [formula_of(w, k) for k in kids]
        bodies = [strip_ante(x_, ante) for x_ in fs]
        return w.s(kids, 'jca' if len(kids) == 2 else '3jca', '( %s -> ( %s ) )' % (ante, (' /\\ '.join(bodies))))
    top = build(tree)
    assert pos[0] == len(hyps), ('ap %s: %d steps unused' % (lab, len(hyps) - pos[0]))
    i = w.inst(lab)
    return w.s([top, i], 'syl', '( %s -> %s )' % (ante, f))


def unpack(w, ante, root=None, out=None):
    """steps ( ante -> leaf ) for every leaf of ante's /\\ tree (dict text -> step)"""
    if out is None:
        out = {}
    if root is None:
        root = w.s([], 'id', '( %s -> %s )' % (ante, ante))

    def walk(text, step):
        tr = _conj_tree(text)
        if tr[0] == 'leaf':
            out.setdefault(text, step); return
        kids = [k[1] if k[0] == 'leaf' else _flat(k) for k in tr[1]]
        refs = ['simpld', 'simprd'] if len(kids) == 2 else ['simp1d', 'simp2d', 'simp3d']
        for k, r in zip(kids, refs):
            walk(k, w.s([step], r, '( %s -> %s )' % (ante, k)))
    walk(ante, root)
    return out


def unpack_step(w, ante, step, text, out=None):
    """leaves of the /\\ tree of TEXT, given step : ( ante -> TEXT )"""
    if out is None:
        out = {}
    tr = _conj_tree(text)
    if tr[0] == 'leaf':
        out.setdefault(text, step); return out
    kids = [k[1] if k[0] == 'leaf' else _flat(k) for k in tr[1]]
    refs = ['simpld', 'simprd'] if len(kids) == 2 else ['simp1d', 'simp2d', 'simp3d']
    for k, r in zip(kids, refs):
        unpack_step(w, ante, w.s([step], r, '( %s -> %s )' % (ante, k)), k, out)
    return out


def S_(w, ante):
    return lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))


def A1(w, ante, closed_step, f):
    return w.s([closed_step], 'a1i', '( %s -> %s )' % (ante, f))


def hyp(w, name, label, f):
    w.lines.append('%s::%s |- %s' % (name, label, f))
    return name


def tsub(f, m):
    return ' '.join(m.get(t, t) for t in f.split())


def id_eq(w, x, X):
    """closed step ( x = X -> x = X )"""
    return w.s([], 'id', '( %s = %s -> %s = %s )' % (x, X, x, X))


def wc(w, body, x, X):
    """closed congruence ( x = X -> ( body <-> body[x := X] ) ); returns (step, new text)"""
    return w.wcongr(body, {x: X}, '%s = %s' % (x, X), {x: id_eq(w, x, X)})


def cc(w, expr, x, X):
    """closed congruence ( x = X -> expr = expr[x := X] )"""
    return w.congr(expr, {x: X}, '%s = %s' % (x, X), {x: id_eq(w, x, X)})


def rspc(w, ante, allstep, x, X, body, memstep):
    """( ante -> body[x := X] ) from allstep : ( ante -> A. x e. A body ) and memstep : ( ante -> X e. A )
    (rspcdva through a closed congruence)"""
    st, new = wc(w, body, x, X)
    return w.s([st, allstep, memstep], 'rspcdva', '( %s -> %s )' % (ante, new)), new


def mpi(w, step, lemma, f):
    """closed modus ponens: from step : P and lemma : ( P -> f ), the step f"""
    return w.s([step, w.inst(lemma)], 'ax-mp', f)


def finrab(w, expr):
    """closed step: { x e. ( M ... N ) | ph } e. Fin, or a rab over such a rab (nested rabs of a
    finite interval): EXPR is the set text"""
    t = expr.split()
    assert t[0] == '{'
    # innermost domain: the interval
    inner = expr
    chain = []
    while inner.startswith('{'):
        toks = inner.split()
        # find the domain: tokens after 'e.' up to the top-level '|'
        depth = 0
        for i in range(3, len(toks)):
            if toks[i] in ('(', '{', '<.'):
                depth += 1
            elif toks[i] in (')', '}', '>.'):
                depth -= 1
            elif toks[i] == '|' and depth == 0:
                dom = ' '.join(toks[3:i]); break
        chain.append(inner)
        inner = dom
    assert inner.startswith('( ') and ' ... ' in inner, inner
    st = w.s([], 'fzfi', '%s e. Fin' % inner)
    for e in reversed(chain):
        st = mpi(w, st, 'rabfi', '%s e. Fin' % e)
    return st
