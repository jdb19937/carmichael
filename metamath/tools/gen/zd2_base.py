"""Sortie ZD2: shared helpers for the generators (built on tools/zd2lib.py, ZR's and ZC1's step libraries)."""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
os.environ.setdefault('MM_ENGINE', 'mmatch')
from zd2lib import *
import zd2lib as ZL
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of, Closure
import num
from ef4lib import Ctx, leaf, ral_at, cbvral
from ef4_g import elrab_unpack, elrab_pack
from zr_i import scale_facts
from zr_k import ri_facts, cell_facts
from c8_o import numst
import mm as _MM

only = sys.argv[1:]
_MBOX = None


def refs_of(w):
    out = set()
    for l in w.lines:
        head = l.split('|-')[0] if '|-' in l else l
        parts = head.split(':')
        if len(parts) >= 3:
            ref = parts[2].strip()
            if ref and ref not in ('idi',):
                out.add(ref)
    return out


def go(w):
    """mathbox gate on every cited label (scratch/z5mbox.py's test), then add (unless the
    command line names other labels)"""
    global _MBOX
    if only and w.label not in only:
        return True
    if _MBOX is None:
        _MBOX = _MM.mathbox_labels(open(_MM.SETMM).read())
    bad = sorted(r for r in refs_of(w) if r in _MBOX)
    if bad:
        print('MATHBOX CITATION', w.label, bad)
        return False
    return w.run()


# ---- closed numerals and constants -------------------------------------------------------------
K800 = '( 2 ^ ; ; 8 0 0 )'


def ctau_facts(w):
    """closed steps: CTau e. RR, 0 <_ CTau, 1 <_ CTau (never evaluating 2 ^ 800)"""
    knn = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % K800)
    k0 = w.s([knn], 'nnnn0i', '%s e. NN0' % K800)
    cnn = w.s([w.s([], '2nn', '2 e. NN'), k0, w.inst('nnexpcl')], 'mp2an', '( 2 ^ %s ) e. NN' % K800)
    df = w.s([], 'df-ctau', 'CTau = ( 2 ^ %s )' % K800)
    ctnn = w.s([df, cnn], 'eqeltri', 'CTau e. NN')
    ctre = w.s([ctnn], 'nnrei', 'CTau e. RR')
    ct1 = w.s([ctnn, w.inst('nnge1')], 'ax-mp', '1 <_ CTau')
    ct0 = w.s([w.s([ctnn], 'nnnn0i', 'CTau e. NN0')], 'nn0ge0i', '0 <_ CTau')
    return dict(re=ctre, ge0=ct0, ge1=ct1, nn=ctnn)


def a1c(w, ante, step, f):
    """a closed step lifted to ( ante -> f )"""
    return w.s([step], 'a1i', '( %s -> %s )' % (ante, f))


def const_facts(w, ante):
    """( ante -> X e. RR ) and ( ante -> 0 <_ X ) for A1C, B2C, C11, C12 (a dict of pairs)"""
    ct = ctau_facts(w)
    c = Ctx(w, ante)
    out = {}
    ctr = c.a1(ct['re'], 'CTau e. RR'); ct0 = c.a1(ct['ge0'], '0 <_ CTau')
    t14r = numst(w, ante, '( ; 1 0 ^ ; 1 4 )', 'RR'); t14g = numst(w, ante, '( ; 1 0 ^ ; 1 4 )', 'ge0')
    two = numst(w, ante, '2', 'RR'); two0 = numst(w, ante, '2', 'ge0')
    p = c([two, t14r], 'remulcld', '( 2 x. ( ; 1 0 ^ ; 1 4 ) ) e. RR')
    p0 = c([two, t14r, two0, t14g], 'mulge0d', '0 <_ ( 2 x. ( ; 1 0 ^ ; 1 4 ) )')
    out[A1C] = (c([p, ctr], 'remulcld', '%s e. RR' % A1C), c([p, ctr, p0, ct0], 'mulge0d', '0 <_ %s' % A1C))
    ct3 = c([ctr, numst(w, ante, '3', 'NN0') if False else c.a1(w.s([], '3nn0', '3 e. NN0'), '3 e. NN0')], 'reexpcld', '( CTau ^ 3 ) e. RR')
    ct30 = c([ctr, c.a1(w.s([], '3nn0', '3 e. NN0'), '3 e. NN0'), ct0], 'expge0d', '0 <_ ( CTau ^ 3 )')
    c2e12 = '; ; ; ; ; ; ; ; ; ; ; ; 2 0 0 0 0 0 0 0 0 0 0 0 0'
    e12r = numst(w, ante, c2e12, 'RR'); e120 = numst(w, ante, c2e12, 'ge0')
    out[C11] = (c([e12r, ct3], 'remulcld', '%s e. RR' % C11), c([e12r, ct3, e120, ct30], 'mulge0d', '0 <_ %s' % C11))
    c12r = numst(w, ante, C12, 'RR'); c120 = numst(w, ante, C12, 'ge0')
    out[C12] = (c12r, c120)
    n32r = numst(w, ante, N320000, 'RR'); n320 = numst(w, ante, N320000, 'ge0')
    q = c([n32r, c12r], 'remulcld', '( %s x. %s ) e. RR' % (N320000, C12))
    q0 = c([n32r, c12r, n320, c120], 'mulge0d', '0 <_ ( %s x. %s )' % (N320000, C12))
    out[B2C] = (c([q, out[C11][0]], 'remulcld', '%s e. RR' % B2C), c([q, out[C11][0], q0, out[C11][1]], 'mulge0d', '0 <_ %s' % B2C))
    return out


def mulge0c(w, ar, br, a0, b0, A, B):
    """closed 0 <_ ( A x. B ) from A e. RR, B e. RR, 0 <_ A, 0 <_ B (set.mm's mulge0i is an implication)"""
    im = w.s([ar, br], 'mulge0i', '( ( 0 <_ %s /\\ 0 <_ %s ) -> 0 <_ ( %s x. %s ) )' % (A, B, A, B))
    return w.s([w.s([a0, b0], 'pm3.2i', '( 0 <_ %s /\\ 0 <_ %s )' % (A, B)), im], 'ax-mp', '0 <_ ( %s x. %s )' % (A, B))


def closed_consts(w):
    """closed steps: X e. RR and 0 <_ X for A1C, B2C, C11, C12 (a dict of pairs)"""
    ct = ctau_facts(w)
    out = {}
    tenr = num.fact(w, '; 1 0', 'RR'); ten0 = num.fact(w, '; 1 0', 'ge0'); n14 = num.nn0(w, 14)
    t14r = w.s([tenr, n14, w.inst('reexpcl')], 'mp2an', '( ; 1 0 ^ ; 1 4 ) e. RR')
    t14g = w.s([tenr, n14, ten0, w.inst('expge0')], 'mp3an', '0 <_ ( ; 1 0 ^ ; 1 4 )')
    two = w.s([], '2re', '2 e. RR'); two0 = w.s([], '0le2', '0 <_ 2')
    p = w.s([two, t14r], 'remulcli', '( 2 x. ( ; 1 0 ^ ; 1 4 ) ) e. RR')
    p0 = mulge0c(w, two, t14r, two0, t14g, '2', '( ; 1 0 ^ ; 1 4 )')
    out[A1C] = (w.s([p, ct['re']], 'remulcli', '%s e. RR' % A1C), mulge0c(w, p, ct['re'], p0, ct['ge0'], '( 2 x. ( ; 1 0 ^ ; 1 4 ) )', 'CTau'))
    ct3 = w.s([ct['re'], w.s([], '3nn0', '3 e. NN0'), w.inst('reexpcl')], 'mp2an', '( CTau ^ 3 ) e. RR')
    ct30 = w.s([ct['re'], w.s([], '3nn0', '3 e. NN0'), ct['ge0'], w.inst('expge0')], 'mp3an', '0 <_ ( CTau ^ 3 )')
    c2e12 = '; ; ; ; ; ; ; ; ; ; ; ; 2 0 0 0 0 0 0 0 0 0 0 0 0'
    e12r = num.fact(w, c2e12, 'RR'); e120 = num.fact(w, c2e12, 'ge0')
    out[C11] = (w.s([e12r, ct3], 'remulcli', '%s e. RR' % C11), mulge0c(w, e12r, ct3, e120, ct30, c2e12, '( CTau ^ 3 )'))
    c12r = num.fact(w, C12, 'RR'); c120 = num.fact(w, C12, 'ge0')
    out[C12] = (c12r, c120)
    n32r = num.fact(w, N320000, 'RR'); n320 = num.fact(w, N320000, 'ge0')
    q = w.s([n32r, c12r], 'remulcli', '( %s x. %s ) e. RR' % (N320000, C12))
    q0 = mulge0c(w, n32r, c12r, n320, c120, N320000, C12)
    out[B2C] = (w.s([q, out[C11][0]], 'remulcli', '%s e. RR' % B2C), mulge0c(w, q, out[C11][0], q0, out[C11][1], '( %s x. %s )' % (N320000, C12), C11))
    return out


def nf_of(w, x, text):
    """a closed step F/ x TEXT, for a wff whose only occurrences of x are bound by restricted
    universal quantifiers (nfv, nfan, nfra1, nfral)"""
    from c9lib import top_and
    toks = text.split()
    if x not in toks:
        return w.s([], 'nfv', 'F/ %s %s' % (x, text))
    if toks[0] == 'A.' and toks[2] == 'e.':
        y = toks[1]
        # A. y e. A body : find the range A and the body
        from cl import split_top
        i = 3
        depth = 0
        # the range is one token or a parenthesised group
        if toks[3] in ('(', '{', '<.'):
            close = {'(': ')', '{': '}', '<.': '>.'}[toks[3]]
            depth = 0
            for j in range(3, len(toks)):
                if toks[j] in ('(', '{', '<.'):
                    depth += 1
                elif toks[j] in (')', '}', '>.'):
                    depth -= 1
                    if depth == 0:
                        i = j + 1
                        break
        else:
            i = 4
        A = ' '.join(toks[3:i]); body = ' '.join(toks[i:])
        if y == x:
            return w.s([], 'nfra1', 'F/ %s %s' % (x, text))
        assert x not in A.split(), (x, A)
        return w.s([w.s([], 'nfcv', 'F/_ %s %s' % (x, A)), nf_of(w, x, body)], 'nfral', 'F/ %s %s' % (x, text))
    if toks[0] == '(' and toks[-1] == ')':
        parts = top_and(text)
        if len(parts) == 2:
            return w.s([nf_of(w, x, parts[0]), nf_of(w, x, parts[1])], 'nfan', 'F/ %s %s' % (x, text))
        if len(parts) == 3:
            return w.s([nf_of(w, x, parts[0]), nf_of(w, x, parts[1]), nf_of(w, x, parts[2])], 'nf3an', 'F/ %s %s' % (x, text))
    raise ValueError('nf_of: cannot handle ' + text[:120])


def ralrimi_nf(w, step, x, A, ante, body):
    """( ante -> A. x e. A body ) from step : ( ( ante /\\ x e. A ) -> body ), when ante binds x"""
    ex = w.s([step], 'ex', '( %s -> ( %s e. %s -> %s ) )' % (ante, x, A, body))
    return w.s([nf_of(w, x, ante), ex], 'ralrimi', '( %s -> A. %s e. %s %s )' % (ante, x, A, body))
