"""Helpers of sortie T15 (the concrete machine, carmtm).

Worksheet builder: tools/tm.py `W`; congruences: tools/congr.py.
"""
import os, sys, re
sys.path.insert(0, os.path.dirname(__file__))
import tm
from tm import W
from congr import congruence, wff_congruence, StepGen

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ------------------------------------------------------------ terms
OPF = '( g e. _V , y e. _V |-> ( w e. Word NN0 |-> ( ( i e. NN0 |-> ( g ` ( w ++ <" i "> ) ) ) u. { <. -u 1 , w >. } ) ) )'
F0 = '( w e. Word NN0 |-> { <. -u 1 , w >. } )'
SEQF = 'seq 0 ( %s , ( NN0 X. { %s } ) )' % (OPF, F0)
OPA = '( a e. _V , b e. _V |-> ( a ` b ) )'


def GF(N):
    """( TMFam ` ( N + 1 ) ) as a mapping"""
    return '( w e. Word NN0 |-> ( ( i e. NN0 |-> ( ( TMFam ` %s ) ` ( w ++ <" i "> ) ) ) u. { <. -u 1 , w >. } ) )' % N


def UF(N, Wd):
    return '( ( i e. NN0 |-> ( ( TMFam ` %s ) ` ( %s ++ <" i "> ) ) ) u. { <. -u 1 , %s >. } )' % (N, Wd, Wd)


def WF(R, Wd, n='n'):
    return '( %s e. NN0 |-> if ( %s = 0 , %s , ( %s ` ( %s - 1 ) ) ) )' % (n, n, R, Wd, n)


def WSEQ(R, Wd):
    return 'seq 0 ( %s , %s )' % (OPA, WF(R, Wd))


def LAB(Wd):
    return '( TMLab ` %s )' % Wd


def WALK(R, Wd):
    return '( %s TMWalk %s )' % (R, Wd)


def S1(x):
    return '<" %s ">' % x


def CC(a, b):
    return '( %s ++ %s )' % (a, b)


# ------------------------------------------------------------ steps
def cong(w, expr, sub, ante, leaves, rules=None):
    g = StepGen('c%d_' % len(w.lines))
    st, new = congruence(expr, sub, ante, leaves, g, rules=rules)
    w.lines.extend(g.lines)
    return st, new


def subhyp(w, x, T, body):
    """step ( x = T -> body = body[x:=T] ) and the new body"""
    eq = '%s = %s' % (x, T)
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    st, val = cong(w, body, {x: T}, eq, {x: idx})
    if st is None:
        st = w.s([], 'eqidd', '( %s -> %s = %s )' % (eq, body, val))
    return st, val


def fvm(w, ante, F, dfref, x, X, body, T, mem, exs):
    """( ante -> ( F ` T ) = body[x:=T] ) for a defined mapping F = ( x e. X |-> body ).
    dfref: label or step proving F = ( x e. X |-> body ) (None when F is the mapping itself)."""
    st, val = subhyp(w, x, T, body)
    mp = '( %s e. %s |-> %s )' % (x, X, body)
    if dfref is None:
        df = w.s([], 'eqid', '%s = %s' % (mp, mp)); F = mp
    elif dfref.startswith('df-'):
        df = w.s([], dfref, '%s = %s' % (F, mp))
    else:
        df = dfref
    fm = w.s([st, df], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (T, X, val, F, T, val))
    return w.s([mem, exs, fm], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, F, T, val)), val


def ovm(w, ante, F, dfref, x, y, X, Y, body, A, B, memA, memB, exs):
    """( ante -> ( A F B ) = body[x:=A,y:=B] ) for F = ( x e. X , y e. Y |-> body )"""
    s1, v1 = subhyp(w, x, A, body)
    s2, v2 = subhyp(w, y, B, v1)
    mp = '( %s e. %s , %s e. %s |-> %s )' % (x, X, y, Y, body)
    if dfref is None:
        df = w.s([], 'eqid', '%s = %s' % (mp, mp)); F = mp
    elif dfref.startswith('df-'):
        df = w.s([], dfref, '%s = %s' % (F, mp))
    else:
        df = dfref
    fm = w.s([s1, s2, df], 'ovmpog', '( ( %s e. %s /\\ %s e. %s /\\ %s e. _V ) -> ( %s %s %s ) = %s )'
             % (A, X, B, Y, v2, A, F, B, v2))
    return w.s([memA, memB, exs, fm], 'syl3anc', '( %s -> ( %s %s %s ) = %s )' % (ante, A, F, B, v2)), v2


def a1(w, ante, closed_step, formula):
    return w.s([closed_step], 'a1i', '( %s -> %s )' % (ante, formula))


def run(w):
    return w.run()


# ------------------------------------------------------------ installation predicates
IDX = os.path.join(ROOT, 'scratch', 'assertions-t15.idx')
if not os.path.exists(IDX):
    IDX = os.path.join(ROOT, 'scratch', 'assertions-carmichael.idx')
OPEN = ('(', '{', '<.', '<"')
CLOSE = (')', '}', '>.', '">')


def grab(t, i):
    """index after the balanced group starting at t[i]"""
    d = 0
    for j in range(i, len(t)):
        if t[j] in OPEN: d += 1
        elif t[j] in CLOSE: d -= 1
        if d == 0: return j + 1
    raise ValueError('unbalanced')


def numtok(t, i):
    """numeral at t[i] -> (value, next index)"""
    if t[i] == ';':
        a, j = numtok(t, i + 1)
        b, k = numtok(t, j)
        return int(str(a) + str(b)), k
    return int(t[i]), i + 1


def num_text(n):
    s = str(n)
    if len(s) == 1: return s
    return '; ' + num_text(int(s[:-1])) + ' ' + s[-1] if len(s) > 2 else '; %s %s' % (s[0], s[1])


def arg_term(t, i):
    """a class argument: variable, numeral, or parenthesised term"""
    if t[i] == '(':
        j = grab(t, i); return t[i:j], j
    if t[i] == ';':
        j = numtok(t, i)[1]; return t[i:j], j
    return [t[i]], i + 1


def load_preds():
    syn, body = {}, {}
    for l in open(IDX):
        lab, k, f = l.rstrip('\n').split(' ', 2)
        if lab.startswith('wtmi') and f.startswith('wff '):
            toks = f.split()[1:]; syn[toks[0]] = toks[1:]
        if lab.startswith('df-tmi'):
            t = f.split()
            i = t.index('<->')
            head = t[2:i]; b = t[i + 1:-1]
            body[head[0]] = (head[1:], b, lab)
    return body


def wff_tree(t, preds):
    """parse a conjunction tree: ('and', [kids]) | ('pred', name, {var: toks}) | ('eq', lhs, rhs) | ('el', lhs, rhs)"""
    def parse(i):
        if t[i] in preds:
            name = t[i]; vs = preds[name][0]; j = i + 1; args = {}
            for v in vs:
                a, j = arg_term(t, j); args[v] = a
            return ('pred', name, args), j
        assert t[i] == '(', t[i:i + 5]
        j = grab(t, i)
        inner = t[i + 1:j - 1]
        # top-level /\ ?
        d = 0; cuts = []
        for k, x in enumerate(inner):
            if x in OPEN: d += 1
            elif x in CLOSE: d -= 1
            elif d == 0 and x == '/\\': cuts.append(k)
        if cuts and inner[0] != 'A.':
            kids = []; st = 0
            for c in cuts + [len(inner)]:
                sub = inner[st:c]
                node, e = parse_sub(sub)
                kids.append(node); st = c + 1
            return ('and', kids), j
        # leaf
        d = 0
        for k, x in enumerate(inner):
            if x in OPEN: d += 1
            elif x in CLOSE: d -= 1
            elif d == 0 and x in ('=', 'e.'):
                return (('eq' if x == '=' else 'el'), inner[:k], inner[k + 1:]), j
        return ('raw', t[i:j]), j

    def parse_sub(sub):
        if sub[0] in preds or (sub[0] == '(' and grab(sub, 0) == len(sub)):
            node, e = parse_in(sub, 0)
            assert e == len(sub), ' '.join(sub)
            return node, e
        d = 0
        for k, x in enumerate(sub):
            if x in OPEN: d += 1
            elif x in CLOSE: d -= 1
            elif d == 0 and x in ('=', 'e.'):
                return (('eq' if x == '=' else 'el'), sub[:k], sub[k + 1:]), len(sub)
        raise ValueError(' '.join(sub))

    def parse_in(s, i):
        nonlocal t
        save = t; t = s
        try:
            return parse(i)
        finally:
            t = save
    node, e = parse(0)
    assert e == len(t)
    return node


# ------------------------------------------------------------ content nodes and families
CUSTOM = ['TMIsrch', 'TMIscal', 'TMIscth', 'TMIsctt', 'TMIsczz', 'TMIscyy', 'TMIsc99', 'TMIver']
FAMPAR = {'TMIroot': ['C', 'K'], 'TMIsrch': ['C', 'K'], 'TMIscal': ['C', 'K'], 'TMIsczz': ['C'], 'TMIscyy': ['K']}


def ntok(name):
    return 'TMn' + name[3:]


def ftok(name):
    return 'TMF' + name[3:]


def flatten(tr):
    if tr[0] == 'and':
        out = []
        for k in tr[1]: out += flatten(k)
        return out
    return [tr]


def label_index(toks):
    """( P ` n ) -> n, else None"""
    if len(toks) >= 5 and toks[0] == '(' and toks[1] == 'P' and toks[2] == '`' and toks[-1] == ')':
        try:
            n, e = numtok(toks, 3)
        except Exception:
            return None
        if e == len(toks) - 1: return n
    return None


def entries(name, P):
    """{index: ('own', stmt_toks) | ('fam', childname, args)} for a kind"""
    vs, b, lab = P[name]
    ent = {}
    for lf in flatten(wff_tree(b, P)):
        if lf[0] == 'eq' and lf[1][:3] == ['(', 'M', '`']:
            i = label_index(lf[1][3:-1]); assert i is not None
            ent[i] = ('own', lf[2])
        elif lf[0] == 'pred':
            i = label_index(lf[2]['P']); assert i is not None
            ent[i] = ('fam', lf[1], lf[2])
    assert sorted(ent) == list(range(len(ent))), (name, sorted(ent))
    return ent


def csyn(name, P, args=None):
    """content node term for kind name with args (dict var->text) or its own variables"""
    vs = [v for v in P[name][0] if v != 'M']
    if args is None:
        return '( %s %s )' % (ntok(name), ' '.join(vs))
    return '( %s %s )' % (ntok(name), ' '.join(' '.join(args[v]) if isinstance(args[v], list) else args[v] for v in vs))


def content_body(name, P):
    ent = entries(name, P)
    items = []
    for i in range(len(ent)):
        e = ent[i]
        items.append(' '.join(e[1]) if e[0] == 'own' else csyn(e[1], P, e[2]))
    txt = items[-1]
    for i in range(len(items) - 2, -1, -1):
        txt = 'if ( j = %s , %s , %s )' % (num_text(i), items[i], txt)
    return '( j e. NN0 |-> %s )' % txt, items


PNV_BODY = ('( j e. NN0 |-> <. 0 , <. K , <. ( ( 2nd ` T ) X. { ( ( <" 4 "> ++ ( reverse ` ( encNatGam ` N ) ) ) ` j ) } ) , '
            '<. 5 , ( ( 2nd ` T ) X. { ( P ` ( j + 1 ) ) } ) >. >. >. >. )')
PNF_BODY = ('( k e. ( 0 ... ( ( # ` ( encNatGam ` N ) ) + 1 ) ) |-> if ( k = ( ( # ` ( encNatGam ` N ) ) + 1 ) , X , '
            '( TMLab ` ( W ++ <" k "> ) ) ) )')


def path_addr(toks, Wd='W'):
    """( ( ( P ` 5 ) ` 0 ) ` 0 ) -> address term ( ( ( W ++ <" 5 "> ) ++ <" 0 "> ) ++ <" 0 "> ), indices"""
    idx = []
    t = toks
    while t != ['P']:
        assert t[0] == '(' and t[-1] == ')'
        inner = t[1:-1]
        d = 0
        for k, x in enumerate(inner):
            if x in OPEN: d += 1
            elif x in CLOSE: d -= 1
            elif d == 0 and x == '`': break
        idx.insert(0, numtok(inner, k + 1)[0])
        t = inner[:k]
    a = Wd
    for n in idx:
        a = '( %s ++ <" %s "> )' % (a, num_text(n))
    return a, idx


def fam_syn(name):
    return '( %s W%s )' % (ftok(name), ''.join(' ' + v for v in FAMPAR.get(name, [])))


def fam_body(name, P):
    ent = entries(name, P)
    cases = []
    for i in sorted(ent):
        e = ent[i]
        if e[0] != 'fam': continue
        child, args = e[1], e[2]
        Wi = '( W ++ <" %s "> )' % num_text(i)
        if child == 'TMIpnv':
            ex, _ = path_addr(args['E'])
            cases.append((i, '( TMpnF %s %s ( TMLab ` %s ) )' % (Wi, ' '.join(args['N']), ex)))
        elif child in CUSTOM:
            cases.append((i, '( %s %s%s )' % (ftok(child), Wi, ''.join(' ' + ' '.join(args[v]) for v in FAMPAR.get(child, [])))))
    txt = '( TMLab ` ( W ++ <" i "> ) )'
    for i, c in reversed(cases):
        txt = 'if ( i = %s , %s , %s )' % (num_text(i), c, txt)
    return '( i e. NN0 |-> %s )' % txt


# ------------------------------------------------------------ instances of closed lemmas
def stmt_of(label, _retry=True):
    for l in open(IDX):
        lab, k, f = l.rstrip('\n').split(' ', 2)
        if lab == label:
            return f[3:] if f.startswith('|- ') else f
    if _retry:
        import subprocess
        env = dict(os.environ); env['MM_DB'] = 'sorties/t15.mm'
        subprocess.run([sys.executable, os.path.join(ROOT, 'tools', 'mm.py'), 'index'], cwd=ROOT, env=env, capture_output=True)
        return stmt_of(label, False)
    raise KeyError(label)


def split_imp(f):
    """( A -> B ) -> (A, B)"""
    t = f.split()
    assert t[0] == '(' and t[-1] == ')'
    inner = t[1:-1]; d = 0
    for k, x in enumerate(inner):
        if x in OPEN: d += 1
        elif x in CLOSE: d -= 1
        elif d == 0 and x == '->':
            return ' '.join(inner[:k]), ' '.join(inner[k + 1:])
    raise ValueError(f)


def subst_text(text, m):
    return ' '.join(x for t in text.split() for x in (m[t].split() if t in m else [t]))


def and_parts(text):
    """( A /\\ B [/\\ C] ) -> [A, B, (C)] or None"""
    t = text.split()
    if t[0] != '(' or grab(t, 0) != len(t): return None
    inner = t[1:-1]; d = 0; cuts = []
    for k, x in enumerate(inner):
        if x in OPEN: d += 1
        elif x in CLOSE: d -= 1
        elif d == 0 and x == '/\\': cuts.append(k)
    if not cuts: return None
    parts = []; st = 0
    for c in cuts + [len(inner)]:
        parts.append(' '.join(inner[st:c])); st = c + 1
    return parts


def build_conj(w, ante, target, leaves):
    """step proving ( ante -> target ) from leaves {text: step}"""
    if target in leaves: return leaves[target]
    parts = and_parts(target)
    if parts is None:
        raise KeyError('no step for leaf: ' + target)
    sts = [build_conj(w, ante, p, leaves) for p in parts]
    st = w.s(sts, 'jca' if len(parts) == 2 else '3jca', '( %s -> %s )' % (ante, target))
    leaves[target] = st
    return st


def use(w, ante, label, m, leaves):
    """instantiate closed lemma `label` ( A -> B ) at substitution m; returns (step ( ante -> B' ), B')"""
    A, B = split_imp(stmt_of(label))
    A2, B2 = subst_text(A, m), subst_text(B, m)
    a = build_conj(w, ante, A2, leaves)
    return w.s([a, w.inst(label)], 'syl', '( %s -> %s )' % (ante, B2)), B2


# ------------------------------------------------------------ congruence over T15's own class syntax
MYSYN = ('TMFroot', 'TMTy', 'TMMach', 'TMProg', 'TMLbl', 'TMRoot', 'TMpnF')


def _mask(text, table):
    t = text.split()
    out = []; i = 0
    while i < len(t):
        if t[i] == '(' and i + 1 < len(t) and (t[i + 1] in MYSYN or t[i + 1].startswith('TMn') or t[i + 1].startswith('TMF')):
            j = grab(t, i)
            grp = ' '.join(t[i:j])
            if grp not in table:
                table[grp] = 'QQMASK%d' % len(table)
            out.append(table[grp]); i = j; continue
        out.append(t[i]); i += 1
    return ' '.join(out)


def cong_m(w, expr, ante, rules):
    """congruence ( ante -> expr = expr' ) with rules, T15 class syntax masked as atoms"""
    table = {}
    e2 = _mask(expr, table)
    r2 = {}
    for k, (v, st) in rules.items():
        r2[_mask(k, table)] = (_mask(v, table), st)
    a2 = _mask(ante, table)
    n0 = len(w.lines)
    st, new = cong(w, e2, {}, a2, {}, rules=r2)
    inv = {v: k for k, v in table.items()}
    for idx in range(n0, len(w.lines)):
        w.lines[idx] = ' '.join(inv.get(x, x) for x in w.lines[idx].split(' '))
    return st, ' '.join(inv.get(x, x) for x in new.split())


# ------------------------------------------------------------ the root installation predicate (df-tmiroot)
ROOT_S0 = "<. (/) , <. ( inr ` (/) ) , <. ( inr ` (/) ) , <. (/) , <. (/) , <. (/) , (/) >. >. >. >. >. >."
def MV(K,J,A,E):
    return ("<. 2 , <. %s , <. TMrdA , <. 4 , <. ( u e. TMSt |-> if ( ( TMra ` u ) = ( inr ` (/) ) , (/) , 1o ) ) , <. <. 0 , <. %s , <. ( u e. TMSt |-> <. 1 , ( bitOf ` ( TMra ` u ) ) >. ) , <. 5 , ( ( 2nd ` T ) X. { %s } ) >. >. >. >. , <. 5 , ( ( 2nd ` T ) X. { %s } ) >. >. >. >. >. >. >." % (K,J,A,E))
BR = "<. 4 , <. ( u e. TMSt |-> if ( ( TMcmp ` u ) = 2o , (/) , 1o ) ) , <. <. 5 , ( ( 2nd ` T ) X. { ( P ` 5 ) } ) >. , <. 5 , ( ( 2nd ` T ) X. { ( ( P ` 7 ) ` 0 ) } ) >. >. >. >."
FIN = "<. 3 , <. ( ( 2nd ` T ) X. { %s } ) , <. 6 , (/) >. >. >." % ROOT_S0
L = "( 2nd ` ( 1st ` T ) )"
ROOT_RHS = ("( ( ( TMIinp T M ( P ` 0 ) ( ( P ` 1 ) ` 0 ) /\\ TMIdup 7 6 5 T M ( P ` 1 ) ( ( P ` 2 ) ` 0 ) /\\ TMIpnv 4 ; 1 6 T M ( P ` 2 ) ( ( P ` 3 ) ` 0 ) ) "
       "/\\ ( TMIcmp 4 6 T M ( P ` 3 ) ( P ` 4 ) /\\ ( M ` ( P ` 4 ) ) = %s /\\ ( M ` ( P ` 5 ) ) = %s ) ) "
       "/\\ ( ( ( M ` ( P ` 6 ) ) = %s /\\ TMIfal T M ( P ` 7 ) ( P ` 9 ) /\\ TMIsrch C K T M ( P ` 8 ) ( P ` 9 ) ) "
       "/\\ ( ( M ` ( P ` 9 ) ) = %s /\\ ( ( P ` 4 ) e. %s /\\ ( P ` 5 ) e. %s /\\ ( P ` 6 ) e. %s ) /\\ ( P ` 9 ) e. %s ) ) )"
       % (BR, MV('7','2','( P ` 5 )','( P ` 6 )'), MV('2','0','( P ` 6 )','( ( ( P ` 8 ) ` 4 ) ` 0 )'), FIN, L, L, L, L))
