"""Sortie A5 helpers: instantiation of nested restricted quantifiers at
compound terms, and the texts of the four windowed analytic inputs.

`instq` is the workhorse: `rspcdva` needs a closed substitution lemma
`( x = C -> ( ps <-> ch ) )` for each level, which `tools/congr.py` builds,
and `rspcdva` itself carries no `$d` against the deduction's antecedent, so
the instantiation is legal even when the antecedent binds variables.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib                                   # parser extensions
import congr


def _strip(text, var, dom):
    pre = 'A. %s e. %s ' % (var, dom)
    t = ' '.join(text.split())
    assert t.startswith(pre), (t[:80], pre)
    return t[len(pre):]


def instq(w, ante, step, quants, body, vals, valsteps):
    """From `step` proving ( ante -> A. v1 e. D1 ... A. vk e. Dk BODY ),
    return (stepname, text) for ( ante -> BODY[v1:=vals[0], ...] ).
    `quants` is [(var, domain)], `body` the whole quantified wff, and
    `valsteps[i]` proves ( ante -> vals[i] e. Di ) (with the earlier
    substitutions already applied to Di)."""
    cur, rest = step, ' '.join(body.split())
    for (v, dom), val, vs in zip(quants, vals, valsteps):
        inner = _strip(rest, v, dom)
        eq = '%s = %s' % (v, val)
        idst = w.s([], 'id', '( %s -> %s )' % (eq, eq))
        sl, new = w.wcongr(inner, {v: val}, eq, {v: idst})
        cur = w.s([sl, cur, vs], 'rspcdva', '( %s -> %s )' % (ante, new))
        rest = new
    return cur, rest


def conj(w, ante, steps, texts, ref='jca'):
    """left-nested conjunction of the given steps"""
    acc, cur = steps[0], texts[0]
    for s, t in zip(steps[1:], texts[1:]):
        cur = '( %s /\\ %s )' % (cur, t)
        acc = w.s([acc, s], ref, '( %s -> %s )' % (ante, cur))
    return acc, cur


def split_imp(text):
    """split a top-level implication '( A -> B )' into (A, B)"""
    t = ' '.join(text.split())
    assert t.startswith('( ') and t.endswith(' )'), t[:60]
    toks = t.split()[1:-1]
    d = 0
    for i, tk in enumerate(toks):
        if tk == '(' or tk == '<.' or tk == '{':
            d += 1
        elif tk == ')' or tk == '>.' or tk == '}':
            d -= 1
        elif tk == '->' and d == 0:
            return ' '.join(toks[:i]), ' '.join(toks[i + 1:])
    raise AssertionError('no top-level -> in ' + t[:80])


def unwind(w, ante, step, text, actions):
    """Walk into a nested `A. v e. D ( P -> ... )`.  Each action is
    ('q', var, domain, value, valuestep) to instantiate a quantifier, or
    ('m', hypstep) to discharge the antecedent of an implication with
    `mpd`.  Returns (stepname, remaining text)."""
    cur, rest = step, ' '.join(text.split())
    for act in actions:
        if act[0] == 'q':
            _, v, dom, val, vs = act
            inner = _strip(rest, v, dom)
            eq = '%s = %s' % (v, val)
            idst = w.s([], 'id', '( %s -> %s )' % (eq, eq))
            sl, new = w.wcongr(inner, {v: val}, eq, {v: idst})
            cur = w.s([sl, cur, vs], 'rspcdva', '( %s -> %s )' % (ante, new))
            rest = new
        else:
            _, hs = act
            _, new = split_imp(rest)
            cur = w.s([hs, cur], 'mpd', '( %s -> %s )' % (ante, new))
            rest = new
    return cur, rest


def dbstmt(label):
    """the statement of a theorem already in the database, whitespace-normalised"""
    import subprocess
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = subprocess.run(['python3', 'tools/mm.py', 'show', label], capture_output=True,
                         text=True, env=dict(os.environ), cwd=root).stdout
    body = out.split(' $p ', 1)[1].split('$=')[0]
    body = ' '.join(body.split())
    assert body.startswith('|- '), body[:40]
    return body[3:].strip()


def subvars(text, m):
    return ' '.join(m.get(t, t) for t in text.split(' '))


EVPRE = 'E. m e. NN0 A. n e. ( ZZ>= ` m ) '
WINPRE = 'A. z e. NN0 A. w e. NN0 A. y e. NN0 A. t e. NN0 '
SUB = {'n': 'N', 'z': 'Z', 'w': 'W', 'y': 'Y', 't': 'T'}


def winbody(label, sub=None):
    """the body of an eventual windowed theorem: everything after
    `( ph -> E. m e. NN0 A. n ... A. t e. NN0 ( <window> -> ` , with the
    filter's bound variables renamed to class variables."""
    s = dbstmt(label)
    _, t = split_imp(s)
    assert t.startswith(EVPRE), t[:60]
    t = t[len(EVPRE):]
    assert t.startswith(WINPRE), t[:60]
    t = t[len(WINPRE):]
    _, body = split_imp(t)
    return subvars(body, sub or SUB)


def ccongr(w, ante, expr, pairs, wff=True):
    """A congruence inside binders whose letters must not enter the deduction's
    antecedent: prove it under the closed antecedent that is the conjunction of
    the equations, and carry it back with one `syl`.  `pairs` is a list of
    (old text, new text, step proving ( ante -> old = new )).  Returns
    (stepname, new expression)."""
    eqs = ['%s = %s' % (o, n) for o, n, _ in pairs]
    if len(eqs) == 1:
        cante = eqs[0]
        getters = [w.s([], 'id', '( %s -> %s )' % (cante, eqs[0]))]
        anteproof = pairs[0][2]
    else:
        cante = '( %s )' % ' /\\ '.join(eqs) if len(eqs) == 2 else None
        assert len(eqs) == 2, 'only one or two equations supported'
        cante = '( %s /\\ %s )' % (eqs[0], eqs[1])
        getters = [w.s([], 'simpl', '( %s -> %s )' % (cante, eqs[0])),
                   w.s([], 'simpr', '( %s -> %s )' % (cante, eqs[1]))]
        anteproof = w.s([pairs[0][2], pairs[1][2]], 'jca', '( %s -> %s )' % (ante, cante))
    rules = {o: (n, g) for (o, n, _), g in zip(pairs, getters)}
    fn = w.wcongr if wff else w.congr
    stp, new = fn(expr, {}, cante, {}, rules=rules)
    out = w.s([anteproof, stp], 'syl', '( %s -> ( %s %s %s ) )'
              % (ante, expr, '<->' if wff else '=', new)) if wff else \
        w.s([anteproof, stp], 'syl', '( %s -> %s = %s )' % (ante, expr, new))
    return out, new


def bundle(w, ante, steps, texts):
    """left-nested conjunction of many facts; returns (step, text)"""
    return conj(w, ante, steps, texts)


def bundletext(texts):
    cur = texts[0]
    for t in texts[1:]:
        cur = '( %s /\\ %s )' % (cur, t)
    return cur


def unbundle(w, ante, step, texts):
    """inverse of `bundle`: the list of steps for each conjunct"""
    n = len(texts)
    cur, out = step, [None] * n
    for i in range(n - 1, 0, -1):
        left = bundletext(texts[:i])
        out[i] = w.s([cur], 'simprd', '( %s -> %s )' % (ante, texts[i]))
        cur = w.s([cur], 'simpld', '( %s -> %s )' % (ante, left)) if i > 1 else \
            w.s([cur], 'simpld', '( %s -> %s )' % (ante, texts[0]))
    out[0] = cur
    return out


def winquant(label, sub=None):
    """everything after `( ph -> E. m e. NN0 A. n e. ( ZZ>= ` m ) ` in an
    eventual windowed theorem, with the filter's `n` renamed to a class
    variable: `A. z e. NN0 ... A. t e. NN0 ( <window> -> BODY )`."""
    s = dbstmt(label)
    _, t = split_imp(s)
    assert t.startswith(EVPRE), t[:60]
    return subvars(t[len(EVPRE):], sub or {'n': 'N'})


def dbhyps(label):
    """the `$e` hypothesis formulas of a theorem in the database, in order"""
    import subprocess, re
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = subprocess.run(['python3', 'tools/mm.py', 'show', label], capture_output=True,
                         text=True, env=dict(os.environ), cwd=root).stdout
    out = ' '.join(out.split())
    parts = re.split(r'\d+ %s\.\d+ \$e \|- ' % re.escape(label), out)[1:]
    return [p.split(' $.')[0].strip() for p in parts]
