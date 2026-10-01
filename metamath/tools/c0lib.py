"""Helpers for sortie C0 (segments, line integrals, rectangles): expressions and
small step patterns on top of tools/tm.py's worksheet builder W."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from tm import *

U01 = '( 0 [,] 1 )'; O01 = '( 0 (,) 1 )'
def LIN(A, B, t='t'): return '( %s + ( %s x. ( %s - %s ) ) )' % (A, t, B, A)
def SEG(A, B): return '( %s cseg %s )' % (A, B)
def LINT(F, A, B): return '( %s lint <. %s , %s >. )' % (F, A, B)
def RECT(A, B): return '( %s crect %s )' % (A, B)
def RINT(F, A, B): return '( %s rectint <. %s , %s >. )' % (F, A, B)
def ITG(X, E, t='t'): return 'S. %s %s _d %s' % (X, E, t)
def DITG(P, Q, E, t='t'): return 'S_ [ %s -> %s ] %s _d %s' % (P, Q, E, t)
def INTG(F, A, B, t='t'): return '( ( %s ` %s ) x. ( %s - %s ) )' % (F, LIN(A, B, t), B, A)
def MPT(x, X, E): return '( %s e. %s |-> %s )' % (x, X, E)
def B1(A, B): return '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (B, A)
def A1(A, B): return '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (A, B)
PH = '( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) )'
TOP = '( TopOpen ` CCfld )'
JR = '( ( TopOpen ` CCfld ) |`t RR )'


def imp(w, ante, ref, concl, hyps=()):
    """deduction step ( ante -> concl ) by ref from hyps"""
    return w.s(list(hyps), ref, '( %s -> %s )' % (ante, concl))


def closed(w, ante, ref, fact):
    """closed fact lifted with a1i"""
    c = w.s([], ref, fact)
    return w.s([c], 'a1i', '( %s -> %s )' % (ante, fact))


def instapply(w, ante, ref, concl, hyps):
    """instance step of ref plus syl/syl2anc/syl3anc from hyp steps"""
    i = w.inst(ref)
    n = len(hyps)
    rule = {0: 'ax-mp', 1: 'syl', 2: 'syl2anc', 3: 'syl3anc'}[n]
    if n == 0:
        return w.s([i], 'ax-mp', concl)
    return w.s(list(hyps) + [i], rule, '( %s -> %s )' % (ante, concl))


def phctx(w, ante, under=False):
    """steps for the conjuncts of PH: (a, b, fcn, sg); under=True means ante = ( PH and ps )"""
    if under:
        a = w.s([], 'simplll', '( %s -> A e. CC )' % ante); b = w.s([], 'simpllr', '( %s -> B e. CC )' % ante)
        f = w.s([], 'simplrl', '( %s -> F e. ( D -cn-> CC ) )' % ante); g = w.s([], 'simplrr', '( %s -> ( A cseg B ) C_ D )' % ante)
    else:
        a = w.s([], 'simpll', '( %s -> A e. CC )' % ante); b = w.s([], 'simplr', '( %s -> B e. CC )' % ante)
        f = w.s([], 'simprl', '( %s -> F e. ( D -cn-> CC ) )' % ante); g = w.s([], 'simprr', '( %s -> ( A cseg B ) C_ D )' % ante)
    return a, b, f, g


def intgcl(w, ante, a, b, f, g, t01, t='t'):
    """( ante -> INTG e. CC ) from steps a: A e. CC, b: B e. CC, f: F e. ( D -cn-> CC ),
    g: ( A cseg B ) C_ D, t01: t e. ( 0 [,] 1 ), all under ante"""
    l = w.s([a, b, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (ante, LIN('A', 'B', t)))
    ld = w.s([g, l], 'sseldd', '( %s -> %s e. D )' % (ante, LIN('A', 'B', t)))
    ff = w.s([f, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % ante)
    fv = w.s([ff, ld], 'ffvelcdmd', '( %s -> ( F ` %s ) e. CC )' % (ante, LIN('A', 'B', t)))
    ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % ante)
    return w.s([fv, ba], 'mulcld', '( %s -> %s e. CC )' % (ante, INTG('F', 'A', 'B', t)))


def cnop(w, ante, op):
    """steps (eqid J = TOP, ( ante -> op e. ( ( J tX J ) Cn J ) )) for op in + - x."""
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    lbl = {'+': 'addcn', '-': 'subcn', 'x.': 'mulcn'}[op]
    c = w.s([e], lbl, '%s e. ( ( %s tX %s ) Cn %s )' % (op, TOP, TOP, TOP))
    return e, w.s([c], 'a1i', '( %s -> %s e. ( ( %s tX %s ) Cn %s ) )' % (ante, op, TOP, TOP, TOP))


def phfrom(w, ante, p):
    """the four conjuncts of PH from a step p proving ( ante -> PH )"""
    a = w.s([p, w.inst('simpll')], 'syl', '( %s -> A e. CC )' % ante); b = w.s([p, w.inst('simplr')], 'syl', '( %s -> B e. CC )' % ante)
    f = w.s([p, w.inst('simprl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % ante); g = w.s([p, w.inst('simprr')], 'syl', '( %s -> ( A cseg B ) C_ D )' % ante)
    return a, b, f, g


def intgclg(w, ante, a, b, f, g, t01, Fn='F', t='t'):
    """as intgcl for a function named Fn (steps f: Fn e. ( D -cn-> CC ), g: segment C_ D)"""
    l = w.s([a, b, t01, w.inst('cseglin')], 'syl3anc', '( %s -> %s e. ( A cseg B ) )' % (ante, LIN('A', 'B', t)))
    ld = w.s([g, l], 'sseldd', '( %s -> %s e. D )' % (ante, LIN('A', 'B', t)))
    ff = w.s([f, w.inst('cncff')], 'syl', '( %s -> %s : D --> CC )' % (ante, Fn))
    fv = w.s([ff, ld], 'ffvelcdmd', '( %s -> ( %s ` %s ) e. CC )' % (ante, Fn, LIN('A', 'B', t)))
    ba = w.s([b, a], 'subcld', '( %s -> ( B - A ) e. CC )' % ante)
    return w.s([fv, ba], 'mulcld', '( %s -> %s e. CC )' % (ante, INTG(Fn, 'A', 'B', t))), ld, ff


def vol01(w, ante):
    """( ante -> ( vol ` ( 0 (,) 1 ) ) = 1 ) and ( ante -> ( 0 (,) 1 ) e. dom vol ), ( ante -> ( vol ` ( 0 (,) 1 ) ) e. RR )"""
    r0 = w.s([], '0re', '0 e. RR'); r1 = w.s([], '1re', '1 e. RR'); le = w.s([], '0le1', '0 <_ 1')
    v = w.s([r0, r1, le, w.inst('volioo')], 'mp3an', '( vol ` ( 0 (,) 1 ) ) = ( 1 - 0 )')
    m = w.s([], '1m0e1', '( 1 - 0 ) = 1'); v1 = w.s([v, m], 'eqtri', '( vol ` ( 0 (,) 1 ) ) = 1')
    v1d = w.s([v1], 'a1i', '( %s -> ( vol ` ( 0 (,) 1 ) ) = 1 )' % ante)
    vr = w.s([v1, r1], 'eqeltri', '( vol ` ( 0 (,) 1 ) ) e. RR'); vrd = w.s([vr], 'a1i', '( %s -> ( vol ` ( 0 (,) 1 ) ) e. RR )' % ante)
    mb = closed(w, ante, 'ioombl', '( 0 (,) 1 ) e. dom vol')
    return v1d, mb, vrd


# ---------------------------------------------------------------------------
# Worksheets with $e hypotheses.  mmj2's batch unifier does not count the
# logical hypotheses of a theorem it has not yet seen among that theorem's
# mandatory hypotheses: it puts their labels in the compressed proof's label
# list instead.  Every reference beyond the mandatory $f hypotheses is then one
# index short per $e.  renumber() decodes the letter string, shifts those
# references, and re-encodes; the appended theorem is verified as usual.
import re as _re, subprocess as _sp
import mm as _MM

_VARS = None


def _vars():
    global _VARS
    if _VARS is None:
        src = open(_MM.SETMM).read()
        _VARS = set(_re.findall(r'^\s*\S+ \$f (?:wff|setvar|class) (\S+) \$\.', src, _re.M))
    return _VARS


def _dec(s):
    out = []; n = 0
    for c in s:
        if c == 'Z':
            out.append('Z')
        elif 'U' <= c <= 'Y':
            n = n * 5 + (ord(c) - ord('U') + 1)
        elif 'A' <= c <= 'T':
            out.append(n * 20 + (ord(c) - ord('A') + 1)); n = 0
        else:
            raise ValueError('bad proof character ' + c)
    if n:
        raise ValueError('truncated proof')
    return out


def _enc(items):
    out = []
    for it in items:
        if it == 'Z':
            out.append('Z'); continue
        last = chr(ord('A') + (it - 1) % 20); n = (it - 1) // 20; pre = ''
        while n > 0:
            d = (n - 1) % 5 + 1; pre = chr(ord('U') + d - 1) + pre; n = (n - d) // 5
        out.append(pre + last)
    return ''.join(out)


def renumber(proof, nf, hyplabels):
    """Rewrite a compressed proof mmj2 generated for a theorem whose $e
    hypotheses it did not count among the mandatory hypotheses: the $e labels
    are dropped from the label list and every reference is mapped to the
    numbering a verifier computes (nf mandatory $f, then the $e, then the
    labels, then the saved steps)."""
    m = _re.match(r'\(\s*(.*?)\s*\)\s*(.*)$', proof, _re.S)
    labels = m.group(1).split(); letters = ''.join(m.group(2).split())
    ne = len(hyplabels)
    keep = [l for l in labels if l not in hyplabels]
    idx = {}
    for j, l in enumerate(labels, 1):
        idx[nf + j] = nf + hyplabels.index(l) + 1 if l in hyplabels else nf + ne + keep.index(l) + 1
    out = []
    for it in _dec(letters):
        if it == 'Z' or it <= nf:
            out.append(it)
        elif it <= nf + len(labels):
            out.append(idx[it])
        else:
            out.append(nf + ne + len(keep) + (it - nf - len(labels)))   # saved step
    return '( %s ) %s' % (' '.join(keep), _enc(out))


def addh(label):
    """unify worksheets/LABEL.mmp, renumber the proof, append to MM_DB, verify"""
    ws = os.path.join(WSDIR, label + '.mmp')
    ok, text = _MM.run_mmj2(ws)
    if not ok:
        bad = [l for l in text.split('\n') if _re.match(r'^(E-|Step )', l)]
        return False, '\n'.join(bad[:12]) or text[-1500:]
    lab, comment, hyps, concl, dvs, proof = _MM.parse_unified(text)
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
    """W.run() for a worksheet with $e hypotheses"""
    w.write()
    if unify_only:
        ok, text = _MM.run_mmj2(os.path.join(WSDIR, w.label + '.mmp'))
        print(('OK   ' if ok else 'FAIL ') + w.label)
        if not ok:
            print('\n'.join(l for l in text.split('\n') if _re.match(r'^(E-|Step )', l))[:2000])
        return ok
    ok, msg = addh(w.label)
    print(('OK   ' if ok else 'FAIL ') + w.label)
    if not ok:
        print(msg)
    return ok


def hyp(w, name, label, formula):
    """a $e hypothesis line; later steps refer to it by its number"""
    w.s([], label, formula, name='h' + name)
    return name
