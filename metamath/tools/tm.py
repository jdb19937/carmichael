"""Shared expressions and worksheet helpers for the TM2 section of carmichael.mm."""
import os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(__file__))
from congr import *

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAINDB = os.path.join(ROOT, 'carmichael.mm')
DB = os.path.join(ROOT, os.environ.get('MM_DB', 'carmichael.mm'))
WSDIR = os.path.join(ROOT, os.environ.get('MM_WS', 'worksheets'))


def defbody(label):
    s = open(MAINDB).read()
    if DB != MAINDB and (label + ' $a') in open(DB).read():
        s = open(DB).read()
    i = s.index('\n' + ' ' * 0 + label + ' $a', 0) if ('\n' + label + ' $a') in s else s.index(label + ' $a')
    j = s.index('$.', i)
    toks = s[i:j].split()
    assert toks[0] == label and toks[1] == '$a' and toks[2] == '|-' and toks[4] == '='
    return ' '.join(toks[5:])


def sub(expr, m):
    return ' '.join(subst_toks(expr.split(), m))


# type-parameter projections
def G(T): return '( 1st ` ( 1st ` %s ) )' % T
def L(T): return '( 2nd ` ( 1st ` %s ) )' % T
def S(T): return '( 2nd ` %s )' % T
def K(T): return 'dom ' + G(T)
def STK(T): return '( TM2Stk ` %s )' % T
def PR(T): return '( ( 2nd ` %s ) X. ( TM2Stk ` %s ) )' % (T, T)
def CFG(T): return '( TM2Cfg ` %s )' % T
def STMT(T): return '( TM2Stmt ` %s )' % T
def SA(T): return '( TM2sa ` %s )' % T
def LYF(T, x='x'): return '( %s e. _V |-> ( %s TM2lay %s ) )' % (x, T, x)
def LY(T, x='x'): return 'rec ( %s , (/) )' % LYF(T, x)
def LYN(T, N, x='x'): return '( %s ` %s )' % (LY(T, x), N)
def PHI(T, X): return sub(defbody('df-tm2lay').split('|->', 1)[1].rsplit(')', 1)[0].strip(), {'t': T, 'x': X})
def CLAUSE(T, H, q='q', p='p'):
    body = defbody('df-tm2cl')
    # ( t e. _V , h e. _V |-> ( q e. A , p e. B |-> CLAUSE ) )
    inner = body.split('|->', 2)[2].rsplit(')', 2)[0].strip()
    return sub(inner, {'t': T, 'h': H, 'q': q, 'p': p})
def CLMPO(T, H):
    return '( q e. %s , p e. %s |-> %s )' % (STMT(T), PR(T), CLAUSE(T, H))
def CL(T, H): return '( %s TM2cl %s )' % (T, H)
def ZF(T, z='z'):
    body = defbody('df-tm2sa')
    i = body.index('rec ( ') + 6
    # find the mpt: from i, balanced parens
    toks = body[i:].split(); d = 0
    for j, t in enumerate(toks):
        if t == '(': d += 1
        elif t == ')':
            d -= 1
            if d == 0: break
    m = ' '.join(toks[:j + 1])
    return sub(m, {'t': T, 'z': z})
def RR(T, z='z'): return 'rec ( %s , <. (/) , (/) >. )' % ZF(T, z)
def ZFP(T, z='z'):
    """ZF with the inner binders q, p renamed a, b"""
    m = ZF(T, z)
    return m.replace('( q e. ', '( a e. ').replace(', p e. ', ', b e. ').replace('|-> ( q ( ', '|-> ( a ( ').replace(') p ) ) ) >. )', ') b ) ) ) >. )')
def RRP(T, z='z'): return 'rec ( %s , <. (/) , (/) >. )' % ZFP(T, z)
def RN(T, N, z='z'): return '( %s ` %s )' % (RR(T, z), N)
def FN(T, N, z='z'): return '( 2nd ` %s )' % RN(T, N, z)
def MPO(T, N, z='z', x='x'):
    """the extension mapping added at depth N+1 (as in df-tm2sa with z := ( RR ` N ))"""
    return '( q e. ( ( %s TM2lay ( 1st ` %s ) ) \\ ( 1st ` %s ) ) , p e. %s |-> ( q ( %s TM2cl %s ) p ) )' % (T, RN(T, N, z), RN(T, N, z), PR(T), T, FN(T, N, z))
def MPOL(T, N, z='z', x='x'):
    """same after rewriting ( 1st ` ( RR ` N ) ) = ( Ly ` N ) and the layer"""
    return '( q e. ( %s \\ %s ) , p e. %s |-> ( q ( %s TM2cl %s ) p ) )' % (LYN(T, 'suc ' + N, x), LYN(T, N, x), PR(T), T, FN(T, N, z))


def ws(label, desc, steps, extra=''):
    os.makedirs(WSDIR, exist_ok=True)
    path = os.path.join(WSDIR, label + '.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=%s  LOC_AFTER=?\n\n* %s\n\n' % (label, desc))
        for st in steps:
            f.write(st.rstrip() + '\n')
        if extra:
            f.write(extra.rstrip() + '\n')
        f.write('$)\n')
    return path


def add(label, unify_only=False):
    cmd = [sys.executable, os.path.join(ROOT, 'tools', 'mm.py'), 'unify' if unify_only else 'add', os.path.join(WSDIR, label + '.mmp')]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    ok = ('ADDED %s' % label) in out
    lines = [l for l in out.split('\n') if re.match(r'^(E-|I-PA-0106|Step |ADDED|FAILED|.*rror|.*failed|.*DjVars|.*REFUSED)', l)]
    return ok, '\n'.join(lines[:25]) if not ok else 'ADDED ' + label


class W:
    """worksheet builder with a StepGen"""
    def __init__(self, label, desc):
        self.label = label; self.desc = desc; self.g = StepGen('c'); self.lines = []; self.n = 0
    def s(self, hyps, ref, formula, name=None):
        if name is None:
            self.n += 1; name = 's%d' % self.n
        self.lines.append('%s:%s:%s |- %s' % (name, ','.join(hyps), ref, formula))
        return name
    def inst(self, ref, name=None):
        if name is None:
            self.n += 1; name = 'i%d' % self.n
        self.lines.append('%s::%s' % (name, ref))
        return name
    def qed(self, hyps, ref, formula):
        self.lines.append('qed:%s:%s |- %s' % (','.join(hyps), ref, formula))
    def congr(self, expr, m, ante, leaves, rules=None):
        st, new = congruence(expr, m, ante, leaves, self.g, rules=rules)
        self.lines.extend(self.g.lines); self.g.lines = []
        return st, new
    def wcongr(self, expr, m, ante, leaves, rules=None):
        st, new = wff_congruence(expr, m, ante, leaves, self.g, rules=rules)
        self.lines.extend(self.g.lines); self.g.lines = []
        return st, new
    def rewrite(self, expr, rules, ante):
        return self.congr(expr, {}, ante, {}, rules=rules)
    def write(self):
        return ws(self.label, self.desc, self.lines)
    def run(self, unify_only=False):
        self.write()
        ok, msg = add(self.label, unify_only)
        print(('OK   ' if ok else 'FAIL ') + self.label); 
        if not ok: print(msg)
        return ok


def MPOLAB(T, N, z='z', x='x'):
    """extension mapping at depth N with binders a, b (statement form used after tm2sar2b)"""
    return '( a e. ( %s \\ %s ) , b e. %s |-> ( a ( %s TM2cl %s ) b ) )' % (LYN(T, 'suc ' + N, x), LYN(T, N, x), PR(T), T, FN(T, N, z))


def ZFP2(T, z='z'):
    """ZF with the inner binders q, p renamed c, d"""
    m = ZF(T, z)
    return m.replace('( q e. ', '( c e. ').replace(', p e. ', ', d e. ').replace('|-> ( q ( ', '|-> ( c ( ').replace(') p ) ) ) >. )', ') d ) ) ) >. )')
def RRP2(T, z='z'): return 'rec ( %s , <. (/) , (/) >. )' % ZFP2(T, z)


NUMEX = {'0': 'c0ex', '1': '1ex', '2': '2ex', '3': '3ex'}
NUMRE = {str(i): '%dre' % i for i in range(7)}


def numset(w, n, ante):
    """step: ( ante -> n e. _V ) for a numeral 0..6"""
    if n in NUMEX:
        c = w.s([], NUMEX[n], '%s e. _V' % n)
    else:
        r = w.s([], NUMRE[n], '%s e. RR' % n)
        c = w.s([r], 'elexi', '%s e. _V' % n)
    return w.s([c], 'a1i', '( %s -> %s e. _V )' % (ante, n))


def numne(w, n, m):
    """closed step: -. n = m for distinct numerals"""
    a, b = int(n), int(m)
    lo, hi = min(a, b), max(a, b)
    if lo == 0:
        lt = w.s([], '0lt1' if hi == 1 else '%dpos' % hi, '0 < %d' % hi)
    else:
        lt = w.s([], '%dlt%d' % (lo, hi), '%d < %d' % (lo, hi))
    r1 = w.s([], NUMRE[str(lo)], '%d e. RR' % lo); r2 = w.s([], NUMRE[str(hi)], '%d e. RR' % hi)
    ne0 = w.s([r1, r2], 'ltnei', '( %d < %d -> %d =/= %d )' % (lo, hi, hi, lo))
    ne = w.s([lt, ne0], 'ax-mp', '%d =/= %d' % (hi, lo))
    if a < b:   # have b =/= a, want -. a = b
        return w.s([ne], 'nesymi', '-. %s = %s' % (n, m))
    nn = w.s([], 'neneq', '( %s =/= %s -> -. %s = %s )' % (n, m, n, m))
    return w.s([ne, nn], 'ax-mp', '-. %s = %s' % (n, m))


def setstep(w, text, ante, setmap):
    if text in setmap: return setmap[text]
    if re.match(r'^[0-6]$', text):
        st = numset(w, text, ante); setmap[text] = st; return st
    if text == '(/)':
        st = w.s([], '0ex', '(/) e. _V'); st = w.s([st], 'a1i', '( %s -> (/) e. _V )' % ante); setmap[text] = st; return st
    n = parse(text)
    if n.kind == 'op':
        st = w.s([], 'opex', '%s e. _V' % text); st = w.s([st], 'a1i', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    if n.kind == 'ov':
        st = w.s([], 'ovex', '%s e. _V' % text); st = w.s([st], 'a1i', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    if n.kind == 'fv':
        st = w.s([], 'fvex', '%s e. _V' % text); st = w.s([st], 'a1i', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    if n.kind in ('sn', 'pr', 'tp'):
        st = w.s([], {'sn': 'snex', 'pr': 'prex', 'tp': 'tpex'}[n.kind], '%s e. _V' % text); st = w.s([st], 'a1i', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    if text in ('1o', '2o', '_om'):
        st = w.s([], {'1o': '1oex', '2o': '2oex', '_om': 'omex'}[text], '%s e. _V' % text); st = w.s([st], 'a1i', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    if n.kind in ('in:|_|', 'in:X.', 'in:u.'):
        a = setstep(w, n.kids[0].text(), ante, setmap); b = setstep(w, n.kids[1].text(), ante, setmap)
        i = w.inst({'in:|_|': 'djuex', 'in:X.': 'xpexg', 'in:u.': 'unexg'}[n.kind])
        st = w.s([a, b, i], 'syl2anc', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    if n.kind == 'in:\\':
        a = setstep(w, n.kids[0].text(), ante, setmap); i = w.inst('difexg')
        st = w.s([a, i], 'syl', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    if n.kind == 'dom':
        a = setstep(w, n.kids[0].text(), ante, setmap); i = w.inst('dmexg')
        st = w.s([a, i], 'syl', '( %s -> %s e. _V )' % (ante, text)); setmap[text] = st; return st
    raise KeyError('no set-ness step for ' + text)


def evaluate(w, ante, expr, setmap, extra_rules=None, ifrules=None, wff=False):
    """Evaluate projections of explicit pairs and ifs with numeral conditions.
    extra_rules: function(node) -> (newtext, step) or None, for additional rewrites.
    Returns (step proving ( ante -> expr = result ) or None, result)."""
    cur = expr; chain = []
    while True:
        node = parse_wff(cur) if wff else parse(cur); rules = {}
        def visit(n):
            if n.kind == 'fv' and n.kids[0].text() in ('1st', '2nd') and n.kids[1].kind == 'op':
                A, B = n.kids[1].kids
                sa = setstep(w, A.text(), ante, setmap); sb = setstep(w, B.text(), ante, setmap)
                first = n.kids[0].text() == '1st'
                inst = w.inst('op1stg' if first else 'op2ndg')
                st = w.s([sa, sb, inst], 'syl2anc', '( %s -> %s = %s )' % (ante, n.text(), (A if first else B).text()))
                rules[n.text()] = ((A if first else B).text(), st); return
            if n.kind == 'if' and n.kids[0].kind == 'eq' and n.kids[0].kids[0].text() == n.kids[0].kids[1].text():
                a = n.kids[0].kids[0].text()
                e = w.s([], 'eqid', '%s = %s' % (a, a)); e2 = w.s([e], 'a1i', '( %s -> %s = %s )' % (ante, a, a))
                st = w.s([e2], 'iftrued', '( %s -> %s = %s )' % (ante, n.text(), n.kids[1].text()))
                rules[n.text()] = (n.kids[1].text(), st); return
            if n.kind == 'if' and ifrules and n.kids[0].text() in ifrules:
                truth, st0 = ifrules[n.kids[0].text()]
                if truth:
                    st = w.s([st0], 'iftrued', '( %s -> %s = %s )' % (ante, n.text(), n.kids[1].text()))
                    rules[n.text()] = (n.kids[1].text(), st)
                else:
                    st = w.s([st0], 'iffalsed', '( %s -> %s = %s )' % (ante, n.text(), n.kids[2].text()))
                    rules[n.text()] = (n.kids[2].text(), st)
                return
            if n.kind == 'if' and n.kids[0].kind == 'eq' and re.match(r'^[0-6]$', n.kids[0].kids[0].text()) and re.match(r'^[0-6]$', n.kids[0].kids[1].text()):
                a, b = n.kids[0].kids[0].text(), n.kids[0].kids[1].text()
                if a == b:
                    e = w.s([], 'eqid', '%s = %s' % (a, a)); e2 = w.s([e], 'a1i', '( %s -> %s = %s )' % (ante, a, a))
                    st = w.s([e2], 'iftrued', '( %s -> %s = %s )' % (ante, n.text(), n.kids[1].text()))
                    rules[n.text()] = (n.kids[1].text(), st)
                else:
                    e = numne(w, a, b); e2 = w.s([e], 'a1i', '( %s -> -. %s = %s )' % (ante, a, b))
                    st = w.s([e2], 'iffalsed', '( %s -> %s = %s )' % (ante, n.text(), n.kids[2].text()))
                    rules[n.text()] = (n.kids[2].text(), st)
                return
            if extra_rules:
                r = extra_rules(n)
                if r:
                    rules[n.text()] = r; return
            for k in n.kids: visit(k)
        visit(node)
        if not rules: break
        st, new = (w.wcongr(cur, {}, ante, {}, rules=rules) if wff else w.rewrite(cur, rules, ante)); chain.append(st); cur = new
    if not chain: return None, cur
    acc = chain[0]; prev = expr
    # rebuild intermediate expressions for eqtrd formulas
    exprs = [expr]
    # recompute by replaying: simpler to store during loop; do a second pass
    return _chain(w, ante, expr, chain, wff), cur


def _chain(w, ante, expr, chain, wff=False):
    # chain steps are ( ante -> e_i = e_{i+1} ); extract e_{i+1} from the step formulas
    def rhs(stepname):
        for l in w.lines:
            if l.startswith(stepname + ':'):
                f = l.split('|-', 1)[1].strip()
                # ( ante -> A = B ) : take B = after last ' = ' at depth 1... parse
                inner = f[len('( %s -> ' % ante):-2]
                n = parse_wff(inner)
                return n.kids[1].text()
        raise KeyError(stepname)
    acc = chain[0]; lhs = expr
    for st in chain[1:]:
        r = rhs(st)
        if wff:
            acc = w.s([acc, st], 'bitrd', '( %s -> ( %s <-> %s ) )' % (ante, lhs, r))
        else:
            acc = w.s([acc, st], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, r))
    return acc
