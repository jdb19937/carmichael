"""Sortie TP: helpers and the frozen statements (TuranPowerSum.lean, the used half: Turan's second
main theorem with the constant ( N / ( 8 e ( M + N ) ) ) ^ N, and N ^ N <_ N! e ^ N).

    python3 tools/tplib.py print                                   # the frozen table
    MM_DB=sorties/tp.mm python3 tools/tplib.py check [LABEL...]    # grammar check (mmatch)

Letters: power-sum index j (headlines) / h (core), window exponent k, Newton index i,
integration variable z / u, roots-of-unity index j, induction variables n t.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from tm import W
import lin
import cl as _cl
from cl import lift, Closure
lin.FASTPATH = True

DB = 'sorties/tp.mm'


def stmt(label):
    """the assertion of LABEL from sorties/tp.mm or carmichael.mm, without |-"""
    for fn in (DB, 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- objects -------------------------------------------------------------------------
def CN(N='N', M='M'):
    """Turan's constant ( N / ( 8 e ( M + N ) ) ) ^ N"""
    return '( ( %s / ( ( 8 x. ( exp ` 1 ) ) x. ( %s + %s ) ) ) ^ %s )' % (N, M, N, N)


def WIN(N='N', M='M'):
    return '( ( %s + 1 ) ... ( %s + %s ) )' % (M, M, N)


def PSUM(Z, k, I, j='j'):
    return 'sum_ %s e. %s ( ( %s ` %s ) ^ %s )' % (j, I, Z, j, k)


FN = lambda N='N': '( 0 ..^ %s )' % N

# ---- frozen statements ---------------------------------------------------------------
S = {}
S['tppowfac'] = '( ( X e. RR /\\ 0 <_ X /\\ K e. NN0 ) -> ( X ^ K ) <_ ( ( ! ` K ) x. ( exp ` X ) ) )'
S['tppowself'] = '( N e. NN0 -> ( N ^ N ) <_ ( ( ! ` N ) x. ( exp ` N ) ) )'
S['tpcore'] = '( ( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ ( V : ( 0 ..^ N ) --> CC /\\ A. r e. ( 0 ..^ N ) ( abs ` ( V ` r ) ) <_ 1 ) /\\ ( J e. ( 0 ..^ N ) /\\ ( V ` J ) = 1 ) ) -> E. k e. ( ( M + 1 ) ... ( M + N ) ) ( ( N / ( ( 8 x. ( exp ` 1 ) ) x. ( M + N ) ) ) ^ N ) <_ ( abs ` sum_ j e. ( 0 ..^ N ) ( ( V ` j ) ^ k ) ) )'
S['tpmaxg'] = '( ( ( N e. NN /\\ M e. NN0 ) /\\ ( I e. Fin /\\ ( # ` I ) <_ N /\\ Z : I --> CC ) /\\ ( X e. I /\\ A. y e. I ( abs ` ( Z ` y ) ) <_ ( abs ` ( Z ` X ) ) /\\ ( T e. RR /\\ 0 <_ T /\\ T <_ ( abs ` ( Z ` X ) ) ) ) ) -> E. k e. ( ( M + 1 ) ... ( M + N ) ) ( ( ( N / ( ( 8 x. ( exp ` 1 ) ) x. ( M + N ) ) ) ^ N ) x. ( T ^ k ) ) <_ ( abs ` sum_ j e. I ( ( Z ` j ) ^ k ) ) )'
S['tpmax'] = ('( ( ( N e. NN /\\ M e. NN0 /\\ Z : %s --> CC ) /\\ A. j e. %s ( abs ` ( Z ` j ) ) <_ ( abs ` ( Z ` 0 ) ) ) -> '
              'E. k e. %s ( %s x. ( ( abs ` ( Z ` 0 ) ) ^ k ) ) <_ ( abs ` %s ) )') % (
    FN(), FN(), WIN(), CN(), PSUM('Z', 'k', FN()))
S['tpmaxlb'] = ('( ( ( N e. NN /\\ M e. NN0 /\\ Z : %s --> CC ) /\\ A. j e. %s ( abs ` ( Z ` j ) ) <_ ( abs ` ( Z ` 0 ) ) /\\ '
                '( T e. RR /\\ 0 <_ T /\\ T <_ ( abs ` ( Z ` 0 ) ) ) ) -> '
                'E. k e. %s ( %s x. ( T ^ k ) ) <_ ( abs ` %s ) )') % (FN(), FN(), WIN(), CN(), PSUM('Z', 'k', FN()))

HEAD = ['tppowfac', 'tppowself', 'tpcore', 'tpmaxg', 'tpmax', 'tpmaxlb']


def order():
    return list(S)


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'tpgc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'tpgc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=tpgc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::tpgc%s.1 |- %s\n' % (lab, S[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch', MM_DB=DB)
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in order():
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or order())


# ---- apply a deduction-form lemma by matching its conclusion -----------------------------
import json
_CACHE = os.path.join(HERE, '..', 'scratch', 'tpcache.json')
_VK = None
_HY = None


def varkind():
    global _VK
    if _VK is None:
        p = os.path.join(HERE, '..', 'scratch', 'tpvars.json')
        if os.path.exists(p):
            _VK = json.load(open(p))
        else:
            src = open(os.path.join(HERE, '..', 'set.mm-repo', 'set.mm')).read()
            _VK = {v: k for k, v in re.findall(r'\$f (wff|class|setvar) (\S+) \$\.', src)}
            json.dump(_VK, open(p, 'w'))
    return _VK


def _load():
    global _HY
    if _HY is None:
        _HY = json.load(open(_CACHE)) if os.path.exists(_CACHE) else {}
    return _HY


def hypinfo(*labels):
    """{label: (hyps, concl)} of database assertions (metamath show, cached)"""
    hy = _load()
    miss = [l for l in labels if l not in hy]
    if miss:
        import mm as _mm
        args = ['read "%s"' % _mm.DBREL, 'set width 9999'] + ['show statement %s' % l for l in miss] + ['exit']
        p = subprocess.run([_mm.MMEXE] + args, cwd=_mm.ROOT, capture_output=True, text=True)
        cur = []
        for l in p.stdout.splitlines():
            m = re.match(r'^\s*\d+ (\S+) \$e \|- (.*) \$\.\s*$', l)
            if m:
                cur.append(m.group(2).strip()); continue
            m = re.match(r'^\s*\d+ (\S+) \$[pa] \|- (.*?)( \$= \.\.\. )?\$\.\s*$', l)
            if m:
                lab = m.group(1)
                hy[lab] = (cur, m.group(2).replace(' $= ...', '').strip()); cur = []
                continue
            if re.match(r'^\s*\d+ ', l) is None and '$d' not in l:
                pass
        json.dump(hy, open(_CACHE, 'w'))
    return {l: hy[l] for l in labels}


OPENB = {'(': ')', '{': '}', '<.': '>.', '[': ']', '<"': '">'}
CLOSEB = set(OPENB.values())


def _balanced(toks):
    d = 0
    for t in toks:
        if t in OPENB: d += 1
        elif t in CLOSEB:
            d -= 1
            if d < 0: return False
    return d == 0


def match(pat, tgt, m=None):
    """token-level matcher: variables of set.mm match balanced token runs (setvars one token)"""
    vk = varkind()
    m = dict(m or {})

    def go(i, j, m):
        if i == len(pat):
            return m if j == len(tgt) else None
        p = pat[i]
        if p in vk:
            if p in m:
                v = m[p].split()
                if tgt[j:j + len(v)] == v:
                    return go(i + 1, j + len(v), m)
                return None
            if vk[p] == 'setvar':
                if j < len(tgt):
                    m2 = dict(m); m2[p] = tgt[j]
                    return go(i + 1, j + 1, m2)
                return None
            for e in range(j + 1, len(tgt) + 1):
                seg = tgt[j:e]
                if not _balanced(seg):
                    continue
                m2 = dict(m); m2[p] = ' '.join(seg)
                r = go(i + 1, e, m2)
                if r is not None:
                    return r
            return None
        if j < len(tgt) and tgt[j] == p:
            return go(i + 1, j + 1, m)
        return None
    import sys as _s
    _s.setrecursionlimit(100000)
    return go(0, 0, m)


def subst(f, m):
    return ' '.join(m.get(t, t) for t in f.split())


def find_step(w, formula):
    """name of a worksheet step proving exactly formula"""
    for l in reversed(w.lines):
        a, _, b = l.partition(' |- ')
        if b.strip() == formula:
            return a.split(':')[0]
    return None


def ap(w, A, lab, goal, c=None, facts=(), sub=None, name=None):
    """step ( A -> goal ) by the deduction-form lemma lab; each $e hypothesis is taken from facts
    (step names, matched by formula), from the worksheet, or discharged by the closure c"""
    hy, concl = hypinfo(lab)[lab]
    full = '( %s -> %s )' % (A, goal)
    m = match(concl.split(), full.split(), sub)
    if m is None:
        raise ValueError('ap %s: conclusion %s does not match %s' % (lab, concl, full))
    fmap = {}
    for f in facts:
        fl = formula_of_step(w, f)
        fmap[fl] = f
    hs = []
    for h in hy:
        hf = subst(h, m)
        st = fmap.get(hf) or find_step(w, hf)
        if st is None and c is not None and hf.startswith('( %s -> ' % A):
            body = hf[len('( %s -> ' % A):-2]
            st = discharge(c, body)
        if st is None:
            raise ValueError('ap %s: no step for hypothesis %s' % (lab, hf))
        hs.append(st)
    return w.s(hs, lab, full, name=name)


def formula_of_step(w, name):
    for l in w.lines:
        a, _, b = l.partition(' |- ')
        if a.split(':')[0] == name:
            return b.strip()
    raise KeyError(name)


def discharge(c, body):
    m = re.match(r'^(.*) e\. (CC|RR|RR\+|NN0|NN|ZZ)$', body)
    if m:
        return c.mem(m.group(1), m.group(2))
    m = re.match(r'^(.*) =/= 0$', body)
    if m:
        return c.ne0(m.group(1))
    m = re.match(r'^0 < (.*)$', body)
    if m:
        return c.gt0(m.group(1))
    m = re.match(r'^0 <_ (.*)$', body)
    if m:
        return c.ge0(m.group(1))
    return None


def split_top_imp(f):
    t = f.split()
    assert t[0] == '(' and t[-1] == ')'
    d = 0
    for i in range(1, len(t) - 1):
        if t[i] in OPENB: d += 1
        elif t[i] in CLOSEB: d -= 1
        elif d == 0 and t[i] == '->':
            return ' '.join(t[1:i]), ' '.join(t[i + 1:-1])
    return None


def split_conj(f):
    """top-level conjuncts of ( P /\\ Q ) or ( P /\\ Q /\\ R ), else None"""
    t = f.split()
    if not (t and t[0] == '(' and t[-1] == ')'):
        return None
    d = 0; parts = []; cur = []; ops = []
    for x in t[1:-1]:
        if x in OPENB: d += 1
        elif x in CLOSEB: d -= 1
        if d == 0 and x == '/\\':
            parts.append(' '.join(cur)); cur = []; continue
        cur.append(x)
    parts.append(' '.join(cur))
    if len(parts) in (2, 3) and all(_balanced(p.split()) for p in parts):
        return parts
    return None


def prove_under(w, A, f, c=None, fmap=None):
    """step ( A -> f ) for a conjunction of known / dischargeable facts"""
    full = '( %s -> %s )' % (A, f)
    st = (fmap or {}).get(full) or find_step(w, full)
    if st:
        return st
    parts = split_conj(f)
    if parts:
        subs = [prove_under(w, A, p, c, fmap) for p in parts]
        return w.s(subs, 'jca' if len(parts) == 2 else '3jca', full)
    if c is not None:
        st = discharge(c, f)
        if st:
            return st
    raise ValueError('prove_under: no step for %s' % full)


def apc(w, A, lab, goal, c=None, facts=(), sub=None, name=None):
    """step ( A -> goal ) by the closed lemma lab ( H -> C ) through syl"""
    hy, concl = hypinfo(lab)[lab]
    H, C = split_top_imp(concl)
    m = match(C.split(), goal.split(), sub)
    if m is None:
        raise ValueError('apc %s: %s does not match %s' % (lab, C, goal))
    Hs = subst(H, m)
    fmap = {formula_of_step(w, f): f for f in facts}
    hst = prove_under(w, A, Hs, c, fmap)
    hs = []
    for h in hy:
        hf = subst(h, m)
        st = fmap.get(hf) or find_step(w, hf)
        if st is None:
            raise ValueError('apc %s: no step for $e %s' % (lab, hf))
        hs.append(st)
    i = w.s(hs, lab, '( %s -> %s )' % (Hs, goal))
    return w.s([hst, i], 'syl', '( %s -> %s )' % (A, goal), name=name)
