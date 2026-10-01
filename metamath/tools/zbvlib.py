"""Sortie ZBV helpers (ZF1 reindexing, the Mertens product, BVL2)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from cl import lift, Closure, ClosureError
from c0lib import hyp


def mkst(w, a):
    """steps under the antecedent a"""
    return lambda hyps, ref, g, name=None: w.s(hyps, ref, '( %s -> %s )' % (a, g), name=name)


def a1(w, ante, step, f):
    """lift a closed step to ( ante -> f )"""
    return w.s([step], 'a1i', '( %s -> %s )' % (ante, f))


def clo(w, ref, f):
    """a closed fact"""
    return w.s([], ref, f)


def adl(w, step, extra):
    """( A -> P ) to ( ( A /\\ extra ) -> P )"""
    from cl import formula_of, split_imp
    a, c = split_imp(formula_of(w, step))
    return w.s([step], 'adantr', '( ( %s /\\ %s ) -> %s )' % (a, extra, c))


def adlr(w, step, extra):
    """( ( A /\\ B ) -> P ) to ( ( ( A /\\ extra ) /\\ B ) -> P )"""
    from cl import formula_of, split_imp, split_sep
    a, c = split_imp(formula_of(w, step))
    toks = a.split()
    inner, right = split_sep(toks[1:-1], ('/\\',))
    return w.s([step], 'adantlr', '( ( ( %s /\\ %s ) /\\ %s ) -> %s )' % (inner, extra, right, c))


def rename(w, ante, A, k, j, step, body):
    """from step: ( ( ante /\\ k e. A ) -> body ) derive
    ( ( ante /\\ j e. A ) -> body[j/k] ); returns (step, new body)"""
    ral = w.s([step], 'ralrimiva', '( %s -> A. %s e. %s %s )' % (ante, k, A, body))
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (k, j, k, j))
    st, new = w.wcongr(body, {k: j}, '%s = %s' % (k, j), {k: idk})
    cb = w.s([st], 'cbvralvw', '( A. %s e. %s %s <-> A. %s e. %s %s )' % (k, A, body, j, A, new))
    ralj = w.s([ral, cb], 'sylib', '( %s -> A. %s e. %s %s )' % (ante, j, A, new))
    return w.s([ralj], 'r19.21bi', '( ( %s /\\ %s e. %s ) -> %s )' % (ante, j, A, new)), new


def inst(w, ante, A, k, T, step, body, mem):
    """from step: ( ( ante /\\ k e. A ) -> body ) and mem: ( ante -> T e. A ) derive
    ( ante -> body[T/k] ) by rspcdva; returns (step, new body)"""
    ral = w.s([step], 'ralrimiva', '( %s -> A. %s e. %s %s )' % (ante, k, A, body))
    idk = w.s([], 'id', '( %s = %s -> %s = %s )' % (k, T, k, T))
    st, new = w.wcongr(body, {k: T}, '%s = %s' % (k, T), {k: idk})
    return w.s([st, ral, mem], 'rspcdva', '( %s -> %s )' % (ante, new)), new


NNUZ = 'NN = ( ZZ>= ` 1 )'


def addh(label):
    """c0lib.addh, but renumbering only when mmj2 listed the $e labels among the
    proof's labels (it does so for some theorems and not others)"""
    import re as _re
    import mm as _MM
    from c0lib import renumber, _vars
    ws = os.path.join(_MM.WSDIR, label + '.mmp')
    ok, text = _MM.run_mmj2(ws)
    if not ok:
        bad = [l for l in text.split('\n') if _re.match(r'^(E-|Step )', l)]
        return False, '\n'.join(bad[:12]) or text[-1500:]
    lab, comment, hyps, concl, dvs, proof = _MM.parse_unified(text)
    m = _re.match(r'\(\s*(.*?)\s*\)', proof, _re.S)
    labels = m.group(1).split()
    if any(h in labels for h, _f in hyps):
        toks = set(concl.split())
        for _h, f in hyps:
            toks |= set(f.split())
        nf = len(toks & _vars())
        proof = renumber(proof, nf, [h for h, _f in hyps])
    db = open(_MM.DB).read()
    if _re.search(r'^\s*%s \$p' % _re.escape(lab), db, _re.M):
        return False, 'label %s already in %s' % (lab, _MM.DBREL)
    with open(_MM.DB, 'a') as f:
        f.write('\n' + _MM.block(lab, comment, hyps, concl, dvs, proof))
    vok, vout = _MM.verify()
    if not vok:
        open(_MM.DB, 'w').write(db)
        return False, vout.strip()[-1500:]
    return True, 'ADDED ' + lab


def runh(w, unify_only=False):
    """W.run() for a worksheet with $e hypotheses (zbvlib.addh)"""
    import re as _re
    import mm as _MM
    w.write()
    if unify_only:
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        print(('OK   ' if ok else 'FAIL ') + w.label)
        if not ok:
            print('\n'.join(l for l in text.split('\n') if _re.match(r'^(E-|Step )', l))[:2000])
        return ok
    ok, msg = addh(w.label)
    print(('OK   ' if ok else 'FAIL ') + w.label)
    if not ok:
        print(msg)
    return ok


def mpv(w, ante, x, X, body, T, mem, exs=None, name=None):
    """congr.mptval with the worksheet's own step generator (no duplicate
    step names across calls) and an automatic _V route for `if` bodies"""
    from congr import mptval, subst_toks
    if exs is None and body.startswith('if ('):
        val = ' '.join(subst_toks(body.split(), {x: T}))
        from cl import split_top
        # if ( cond , A , B ): pieces after 'if' are one group
        inner = val[len('if ( '):-2]
        from cl import split_sep
        cond, A, B = split_sep(inner.split(), (',',))
        ea = w.s([], 'ovexd', '( %s -> %s e. _V )' % (ante, A)) if A.startswith('( ') else \
            w.s([w.s([], 'c0ex' if A == '0' else '1ex', '%s e. _V' % A)], 'a1i', '( %s -> %s e. _V )' % (ante, A))
        eb = w.s([], 'ovexd', '( %s -> %s e. _V )' % (ante, B)) if B.startswith('( ') else \
            w.s([w.s([], 'c0ex' if B == '0' else '1ex', '%s e. _V' % B)], 'a1i', '( %s -> %s e. _V )' % (ante, B))
        exs = w.s([ea, eb], 'ifexd', '( %s -> %s e. _V )' % (ante, val))
    return mptval(w, ante, x, X, body, T, mem, exs=exs, name=name, gen=w.g)


def sy(w, ante, step, ref, goal):
    """( ante -> goal ) from ( ante -> P ) by the closed theorem ref: ( P -> goal )"""
    return w.s([step, w.inst(ref)], 'syl', '( %s -> %s )' % (ante, goal))


def sy2(w, ante, s1, s2, ref, goal):
    return w.s([s1, s2, w.inst(ref)], 'syl2anc', '( %s -> %s )' % (ante, goal))


def sy3(w, ante, s1, s2, s3, ref, goal):
    return w.s([s1, s2, s3, w.inst(ref)], 'syl3anc', '( %s -> %s )' % (ante, goal))
