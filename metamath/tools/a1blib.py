"""Sortie A1b helpers: a closure discharge for the types of
lean/Carmichael/Algorithm.lean (products, disjoint unions, function spaces,
words, 2o and the sortie's own functions), and the worksheet idioms that
unfold a definition (`fvmptg`, `ovmpoga`).  The `seq` node of the parser and
its congruences are in tools/congr.py.
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib as _a1                      # rab, prod_, decimals, -u, ~P
import congr as _c
from congr import Node, LOWVAR

import tm                                # noqa: E402
from tm import W                         # noqa: F401
import num                               # noqa: E402


# --------------------------------------------------------------- expressions
W0 = 'Word NN0'
B2 = '( 2o X. NN0 )'
WN = '( Word NN0 X. NN0 )'
N2 = '( NN0 X. NN0 )'
OPL = '( ( NN0 X. Word NN0 ) |_| 1o )'
OPN = '( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )'
EXD = '( Word NN0 X. ( NN0 X. ( Word NN0 X. Tbl ) ) )'
TB = 'Tbl'
NONE = '( inr ` (/) )'


def MAP(cod, dom):
    return '( %s ^m %s )' % (cod, dom)


def HD(c='c'):
    return '( %s ` 0 )' % c


def TL(c='c'):
    return '( %s substr <. 1 , ( # ` %s ) >. )' % (c, c)


# codomains of the sortie's own functions, keyed by the operation/function
# token, with the label of the closure theorem and the argument types
CODOM = {}


def declare(token, cod, cl, args):
    """args: list of type texts, in Lean's argument order"""
    CODOM[token] = (cod, cl, args)


declare('PrimeGo', B2, 'primegocl', ['NN0', 'NN0', 'NN0'])
declare('IsPrimeTD', B2, 'isprimetdcl', ['NN0'])
declare('DivOut', N2, 'divoutcl', ['NN', 'NN0', 'NN0'])
declare('SmoothGo', N2, 'smoothgocl', ['NN', 'NN0', 'NN0'])
declare('SmoothTD', B2, 'smoothtdcl', ['NN', 'NN0'])
declare('MulAll', WN, 'mulallcl', ['NN0', W0])
declare('DivisorsOf', WN, 'divisorsofcl', [W0])
declare('CoprimeTo', B2, 'coprimetocl', [W0, 'NN0'])
declare('ProdL', N2, 'prodlcl', [W0])
declare('ResGo', WN, 'resgocl', ['NN0', 'NN', 'NN', 'NN0'])
declare('Reservoir', WN, 'reservoircl', ['NN', 'NN0', 'NN'])
declare('PoolGo', WN, 'poolgocl', ['NN0', 'NN0', 'NN0', W0])
declare('PoolAlg', WN, 'poolalgcl', [W0, 'NN0', 'NN0', 'NN0'])
declare('Scan', OPN, 'scancl', [W0, 'NN0', 'NN0', 'NN0', 'NN0', 'NN0'])
declare('SetIfNone', TB, 'setifnonecl', [TB, 'NN0', W0])
declare('DpGo', '( Tbl X. NN0 )', 'dpgocl', ['NN', 'NN0', TB, 'NN0', TB])
declare('DpStep', '( Tbl X. NN0 )', 'dpstepcl', ['NN', 'NN0', TB])
declare('ExtractGo', OPN, 'extractgocl', ['NN', 'NN0', W0, 'NN0', W0, TB])
declare('Extract', OPN, 'extractcl', ['NN', 'NN0', W0])
declare('NotMemTD', B2, 'notmemtdcl', ['NN0', W0])
declare('NodupTD', B2, 'noduptdcl', [W0])
declare('AllPrimeTD', B2, 'allprimetdcl', [W0])
declare('KorseltTD', B2, 'korselttdcl', ['NN0', W0])
declare('Verify', B2, 'verifycl', ['NN0', W0])


def callargs(text):
    """If `text` is an application of one of our functions, return
    (token, [arg texts]); otherwise None.  Handles the arity convention
    ( f ` A ), ( A f B ), ( ( A f B ) ` C ) ` D ) ..."""
    n = _c.parse(text)
    args = []
    while n.kind == 'fv':
        args.insert(0, n.kids[1].text())
        n = n.kids[0]
    if n.kind == 'ov':
        tok = n.kids[1].text()
        if tok in CODOM:
            return tok, [n.kids[0].text(), n.kids[2].text()] + args
        return None
    if n.kind == 'atom' and n.toks[0] in CODOM and args:
        return n.toks[0], args
    return None


EXPAND = {'Tbl': '( ( Word NN0 |_| 1o ) ^m NN0 )'}
ALIAS = {'Tbl': '( ( Word NN0 |_| 1o ) ^m NN0 )',
         'Scales': '( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 )'}


# ------------------------------------------------------------------- closure
class ClError(Exception):
    pass


UPCAST = [('NN', 'NN0', 'nnnn0d'), ('NN', 'ZZ', 'nnzd'), ('NN0', 'ZZ', 'nn0zd'),
          ('NN0', 'RR', 'nn0red'), ('NN', 'RR', 'nnred'), ('ZZ', 'RR', 'zred')]


class Cl:
    """Membership discharge under one antecedent.  `facts` maps an expression
    to (target, step) or a list of those."""

    def __init__(self, w, ante, facts=None, parent=None):
        self.w = w
        self.ante = ante
        self.memo = {}
        self.setmap = {}
        self.parent = parent
        for e, v in (facts or {}).items():
            for t, s in (v if isinstance(v, list) else [v]):
                self.memo[(e, t)] = s

    def child(self, part, neg=False):
        a2 = '( %s /\\ %s )' % (self.ante, ('-. ' + part) if neg else part)
        return Cl(self.w, a2, parent=self)

    def have(self, e, t, s):
        self.memo[(e, t)] = s
        return s

    def _s(self, hyps, ref, e, t):
        return self.w.s(hyps, ref, '( %s -> %s e. %s )' % (self.ante, e, t))

    def jca(self, steps, parts):
        """( ante -> ante_and(*parts) ) from steps proving each part"""
        st, acc = steps[0], parts[0]
        for nxt, p in zip(steps[1:], parts[1:]):
            acc2 = '( %s /\\ %s )' % (acc, p)
            st = self.w.s([st, nxt], 'jca', '( %s -> %s )' % (self.ante, acc2))
            acc = acc2
        return st

    def ge0(self, e):
        """( ante -> 0 <_ e ), for an expression in NN0, NN or RR+"""
        key = (e, 'ge0')
        if key in self.memo:
            return self.memo[key]
        for k, lab in (('NN0', 'nn0ge0d'), ('NN', 'nngt0d'), ('RR+', 'rpge0d')):
            if (e, k) in self.memo or k == 'NN0':
                try:
                    st = self.mem(e, k)
                except ClError:
                    continue
                if k == 'NN':
                    st = self.w.s([st], 'nnnn0d', '( %s -> %s e. NN0 )' % (self.ante, e))
                    lab = 'nn0ge0d'
                out = self.w.s([st], lab, '( %s -> 0 <_ %s )' % (self.ante, e))
                self.memo[key] = out
                return out
        raise ClError('no nonnegativity for ' + e)

    def setness(self, e):
        return tm.setstep(self.w, e, self.ante, self.setmap)

    def allkeys(self):
        """the (expression, target) keys known here or in an ancestor"""
        out = list(self.memo.keys())
        c = self.parent
        while c is not None:
            out += list(c.memo.keys())
            c = c.parent
        return out

    def maptype(self, f):
        """a type of `f` that is a function space, or None"""
        def ismap(t):
            m = re.match(r'^\( (.*) \^m (.*) \)$', EXPAND.get(t, t))
            return bool(m and _balanced(m.group(1)))
        for (x, ty) in self.allkeys():
            if x == f and not ty.startswith('fn:') and ty != '_V' and ismap(ty):
                return ty
        ca = callargs(f)
        if ca and ismap(CODOM[ca[0]][0]):
            return CODOM[ca[0]][0]
        try:
            n = _c.parse(f)
        except Exception:
            return None
        if n.kind == 'fv' and n.kids[0].text() in ('1st', '2nd'):
            pt = self.prodtype(n.kids[1].text())
            m = _split_xp(pt) if pt else None
            if m:
                cand = m[0] if n.kids[0].text() == '1st' else m[1]
                if ismap(cand):
                    return cand
        return None

    def prodtype(self, e):
        """the product type of e, as text, or None"""
        for (x, t) in self.allkeys():
            if x == e and re.match(r'^\( .* X\. .* \)$', t) and _balanced_xp(t):
                return t
        n = _c.parse(e)
        if n.kind == 'op':
            return None
        ca = callargs(e)
        if ca:
            return CODOM[ca[0]][0]
        if n.kind == 'fv' and n.kids[0].text() in ('1st', '2nd'):
            pt = self.prodtype(n.kids[1].text())
            m = _split_xp(pt) if pt else None
            if m:
                cand = m[0] if n.kids[0].text() == '1st' else m[1]
                if _split_xp(EXPAND.get(cand, cand)):
                    return cand
        if n.kind == 'fv':
            f = n.kids[0].text()
            for (x, t) in self.allkeys():
                if x == f:
                    m = re.match(r'^\( (.*) \^m (.*) \)$', EXPAND.get(t, t))
                    if m and _balanced(m.group(1)):
                        return m.group(1)
        return None

    def mem(self, e, t):
        key = (e, t)
        if key in self.memo:
            return self.memo[key]
        st = self._mem(e, t)
        self.memo[key] = st
        return st

    def _mem(self, e, t):
        w, ante = self.w, self.ante
        if self.parent is not None:
            try:
                st = self.parent.mem(e, t)
                return self._s([st], 'adantr', e, t)
            except (ClError, KeyError, AssertionError, SyntaxError):
                pass
        # upcasts from a known membership
        for a, b, lab in UPCAST:
            if b == t and (e, a) in self.memo:
                return self._s([self.memo[(e, a)]], lab, e, t)
        if t == '_V':
            for (x, ty), stp in list(self.memo.items()):
                if x == e and stp is not None and not ty.startswith('fn:') and ty != '_V':
                    return self._s([stp, w.s([], 'elex', '( %s e. %s -> %s e. _V )' % (e, ty, e))], 'syl', e, t)
            try:
                k = _c.parse(e)
            except Exception:
                k = None
            if k is not None and k.kind == 'seq':
                return self._s([w.s([], 'seqex', '%s e. _V' % e)], 'a1i', e, t)
            if k is not None and k.kind == 'if':
                a = self.mem(k.kids[1].text(), t)
                b = self.mem(k.kids[2].text(), t)
                return self._s([a, b], 'ifcld', e, t)
            if k is not None and k.kind == 'mpt':
                d = self.mem(k.kids[0].text(), '_V')
                i = w.s([], 'mptexg', '( %s e. _V -> %s e. _V )' % (k.kids[0].text(), e))
                return self._s([d, i], 'syl', e, t)
            if k is not None and k.kind == 'mpo':
                d1 = self.mem(k.kids[0].text(), '_V')
                d2 = self.mem(k.kids[1].text(), '_V')
                i = w.s([], 'mpoexga', '( ( %s e. _V /\\ %s e. _V ) -> %s e. _V )'
                        % (k.kids[0].text(), k.kids[1].text(), e))
                return self._s([d1, d2, i], 'syl2anc', e, t)
            if k is not None and k.kind == 'ov':
                return self._s([w.s([], 'ovex', '%s e. _V' % e)], 'a1i', e, t)
            NAMED = {'NN0': 'nn0ex', 'NN': 'nnex', 'ZZ': 'zex', 'RR': 'reex',
                     'CC': 'cnex', '1o': '1oex', '2o': '2oex'}
            if k is not None and k.kind == 'atom' and e in NAMED:
                return self._s([w.s([], NAMED[e], '%s e. _V' % e)], 'a1i', e, t)
            if k is not None and k.kind == 'atom' and e == 'Tbl':
                o = w.s([], 'df-tbl', 'Tbl = ( ( Word NN0 |_| 1o ) ^m NN0 )')
                x = w.s([], 'ovex', '( ( Word NN0 |_| 1o ) ^m NN0 ) e. _V')
                return self._s([w.s([o, x], 'eqeltri', 'Tbl e. _V')], 'a1i', e, t)
            if k is not None and k.kind == 'word':
                return self._s([w.s([], 'wrdexi', '%s e. _V' % e)], 'a1i', e, t)
            if k is not None and k.kind == 'in:|`':
                a = self.mem(k.kids[0].text(), '_V')
                i = w.s([], 'resexg', '( %s e. _V -> %s e. _V )' % (k.kids[0].text(), e))
                return self._s([a, i], 'syl', e, t)
            if k is not None and k.kind in ('in:X.', 'in:|_|', 'in:u.'):
                a = self.mem(k.kids[0].text(), '_V')
                b = self.mem(k.kids[1].text(), '_V')
                i = w.s([], {'in:X.': 'xpexg', 'in:|_|': 'djuex', 'in:u.': 'unexg'}[k.kind],
                        '( ( %s e. _V /\\ %s e. _V ) -> %s e. _V )'
                        % (k.kids[0].text(), k.kids[1].text(), e))
                return self._s([a, b, i], 'syl2anc', e, t)
            return self.setness(e)
        # numerals
        if re.match(r'^[0-9]$', e) or re.match(r'^; ', e) or _isfrac(e):
            if t in ('NN0', 'NN', 'ZZ', 'RR', 'CC', 'RR+'):
                c = num.fact(w, e, t)
                return self._s([c], 'a1i', e, t)
        if e == '1o' and t == '2o':
            return self._s([w.s([], '1oel2o', '1o e. 2o')], 'a1i', e, t)
        if e == '(/)' and t == '2o':
            return self._s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', e, t)
        if e == '(/)' and t == '1o':
            a = w.s([], 'eqid', '(/) = (/)')
            b = w.s([], 'el1o', '( (/) e. 1o <-> (/) = (/) )')
            return self._s([w.s([a, b], 'mpbir', '(/) e. 1o')], 'a1i', e, t)
        if e == '(/)' and t in (W0, 'Word S'):
            return self._s([w.s([], 'wrd0', '(/) e. %s' % t)], 'a1i', e, t)
        if e == 'EmptyTbl' and t == 'Tbl':
            return self._s([w.s([], 'emptytblcl', 'EmptyTbl e. Tbl')], 'a1i', e, t)
        n = _c.parse(e)
        # if: unconditionally, or by a case split on the condition
        if n.kind == 'if':
            cond = n.kids[0].text()
            try:
                a = self.mem(n.kids[1].text(), t)
                b = self.mem(n.kids[2].text(), t)
                return self._s([a, b], 'ifcld', e, t)
            except ClError:
                pass
            out = []
            for neg in (False, True):
                ch = self.child(cond, neg)
                a2 = ch.ante
                cs = w.s([], 'simpr', '( %s -> %s%s )' % (a2, '-. ' if neg else '', cond))
                if neg:
                    ck = _c.parse_wff(cond)
                    if ck.kind == 'eq' and ck.kids[1].text() == '(/)':
                        ch.memo[(ck.kids[0].text(), 'ne(/)')] = w.s(
                            [cs], 'neqned', '( %s -> %s =/= (/) )' % (a2, ck.kids[0].text()))
                    if ck.kind == 'eq' and ck.kids[1].text() == '( inr ` (/) )':
                        ch.memo[(ck.kids[0].text(), 'neinr')] = w.s(
                            [cs], 'neqned', '( %s -> %s =/= ( inr ` (/) ) )' % (a2, ck.kids[0].text()))
                eq = w.s([cs], 'iffalsed' if neg else 'iftrued',
                         '( %s -> %s = %s )' % (a2, e, n.kids[2 if neg else 1].text()))
                mm = ch.mem(n.kids[2 if neg else 1].text(), t)
                out.append(w.s([eq, mm], 'eqeltrd', '( %s -> %s e. %s )' % (a2, e, t)))
            return self._s(out, 'pm2.61dan', e, t)
        # ordered pair into a product
        if n.kind == 'op':
            m = _split_xp(t)
            if m:
                a = self.mem(n.kids[0].text(), m[0])
                b = self.mem(n.kids[1].text(), m[1])
                i = w.s([], 'opelxpi', '( ( %s e. %s /\\ %s e. %s ) -> %s e. %s )'
                        % (n.kids[0].text(), m[0], n.kids[1].text(), m[1], e, t))
                return self._s([a, b, i], 'syl2anc', e, t)
        # inl / inr into a disjoint union
        if n.kind == 'fv' and n.kids[0].text() in ('inl', 'inr'):
            m = _split_dju(t)
            if m:
                side = m[0] if n.kids[0].text() == 'inl' else m[1]
                a = self.mem(n.kids[1].text(), side)
                i = w.s([], 'djulcl' if n.kids[0].text() == 'inl' else 'djurcl',
                        '( %s e. %s -> %s e. %s )' % (n.kids[1].text(), side, e, t))
                return self._s([a, i], 'syl', e, t)
        # the payload of a non-none element of a disjoint union
        if n.kind == 'fv' and n.kids[0].text() == '2nd':
            X = n.kids[1].text()
            ne = self.memo.get((X, 'neinr'))
            if ne is not None:
                dj = '( %s |_| 1o )' % t
                try:
                    xm = self.mem(X, dj)
                except ClError:
                    xm = None
                if xm is not None:
                    cj = self.jca([xm, ne], ['%s e. %s' % (X, dj), '%s =/= ( inr ` (/) )' % X])
                    i = w.s([], 'algdjun', '( ( %s e. %s /\\ %s =/= ( inr ` (/) ) ) -> ( %s e. %s /\\ %s = ( inl ` %s ) ) )'
                            % (X, dj, X, e, t, X, e))
                    aj = w.s([cj, i], 'syl', '( %s -> ( %s e. %s /\\ %s = ( inl ` %s ) ) )'
                             % (self.ante, e, t, X, e))
                    return self._s([aj], 'simpld', e, t)
        # projections
        if n.kind == 'fv' and n.kids[0].text() in ('1st', '2nd'):
            arg = n.kids[1].text()
            pt = self.prodtype(arg)
            m = _split_xp(pt) if pt else None
            if m:
                side = m[0] if n.kids[0].text() == '1st' else m[1]
                a = self.mem(arg, pt)
                i = w.s([], 'xp1st' if n.kids[0].text() == '1st' else 'xp2nd',
                        '( %s e. %s -> %s e. %s )' % (arg, pt, e, side))
                got = self._s([a, i], 'syl', e, side)
                if side == t:
                    return got
                self.memo[(e, side)] = got
                return self.mem(e, t)
        # floor of a quotient of a nonnegative integer by a positive one
        if n.kind == 'fv' and n.kids[0].text() == '|_' and t == 'NN0':
            q = n.kids[1]
            if q.kind == 'ov' and q.kids[1].text() == '/':
                A, B = q.kids[0].text(), q.kids[2].text()
                ar = self.mem(A, 'RR')
                a0 = w.s([self.mem(A, 'NN0')], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ante, A))
                brp = w.s([self.mem(B, 'NN')], 'nnrpd', '( %s -> %s e. RR+ )' % (ante, B))
                qr = w.s([ar, brp], 'rerpdivcld', '( %s -> %s e. RR )' % (ante, q.text()))
                qg = w.s([ar, brp, a0], 'divge0d', '( %s -> 0 <_ %s )' % (ante, q.text()))
                i = w.s([], 'flge0nn0', '( ( %s e. RR /\\ 0 <_ %s ) -> %s e. NN0 )'
                        % (q.text(), q.text(), e))
                cj = self.jca([qr, qg], ['%s e. RR' % q.text(), '0 <_ %s' % q.text()])
                return self._s([cj, i], 'syl', e, t)
        # the first letter of a nonempty word
        if n.kind == 'fv' and n.kids[1].text() == '0':
            u = n.kids[0].text()
            ne = self.memo.get((u, 'ne(/)'))
            if ne is not None:
                uw = self.mem(u, W0)
                cj = self.jca([uw, ne], ['%s e. %s' % (u, W0), '%s =/= (/)' % u])
                got = self._s([cj, w.s([], 'wrdfv0', '( ( %s e. %s /\\ %s =/= (/) ) -> %s e. NN0 )'
                                       % (u, W0, u, e))], 'syl', e, 'NN0')
                if t == 'NN0':
                    return got
                self.memo[(e, 'NN0')] = got
                return self.mem(e, t)
        # length
        if n.kind == 'fv' and n.kids[0].text() == '#' and t in ('NN0', 'NN', 'ZZ', 'RR'):
            arg = n.kids[1].text()
            a = self.mem(arg, W0)
            i = w.s([], 'lencl', '( %s e. %s -> %s e. NN0 )' % (arg, W0, e))
            got = self._s([a, i], 'syl', e, 'NN0')
            self.memo[(e, 'NN0')] = got
            return got if t == 'NN0' else self.mem(e, t)
        # value of one of our own functions
        ca = callargs(e)
        if ca:
            tok, args = ca
            cod, lab, doms = CODOM[tok]
            if len(args) == len(doms):
                hs = [self.mem(a, d) for a, d in zip(args, doms)]
                i = w.s([], lab, '( %s -> %s e. %s )'
                        % (ante_and(*['%s e. %s' % (a, d) for a, d in zip(args, doms)]), e, cod)
                        if len(args) > 1 else '( %s e. %s -> %s e. %s )' % (args[0], doms[0], e, cod))
                if len(hs) == 1:
                    got = self._s([hs[0], i], 'syl', e, cod)
                else:
                    cj = self.jca(hs, ['%s e. %s' % (a, d) for a, d in zip(args, doms)])
                    got = self._s([cj, i], 'syl', e, cod)
                if cod == t:
                    return got
                self.memo[(e, cod)] = got
                return self.mem(e, t)
        # application of a level function h e. ( Cod ^m Dom )
        if n.kind == 'fv':
            f = n.kids[0].text()
            ty = self.maptype(f)
            if ty is not None:
                    stp = self.mem(f, ty)
                    ty0, ty = ty, EXPAND.get(ty, ty)
                    m = re.match(r'^\( (.*) \^m (.*) \)$', ty)
                    if m and _balanced(m.group(1)):
                        cod, dom = m.group(1), m.group(2)
                        if ty0 != ty:
                            stp = w.s([stp, w.s([], 'df-' + ty0.lower(), '%s = %s' % (ty0, ty))],
                                      'eleqtrdi', '( %s -> %s e. %s )' % (self.ante, f, ty))
                            self.memo[(f, ty)] = stp
                        fs = self._s([stp], 'x', f, ty) if False else None
                        ff = self.memo.get((f, 'fn:' + ty))
                        if ff is None:
                            i = w.s([], 'elmapi', '( %s e. %s -> %s : %s --> %s )' % (f, ty, f, dom, cod))
                            ff = w.s([stp, i], 'syl', '( %s -> %s : %s --> %s )' % (self.ante, f, dom, cod))
                            self.memo[(f, 'fn:' + ty)] = ff
                        a = self.mem(n.kids[1].text(), dom)
                        i2 = w.s([], 'ffvelcdm', '( ( %s : %s --> %s /\\ %s e. %s ) -> %s e. %s )'
                                  % (f, dom, cod, n.kids[1].text(), dom, e, cod))
                        got = self._s([ff, a, i2], 'syl2anc', e, cod)
                        if cod == t:
                            return got
                        self.memo[(e, cod)] = got
                        return self.mem(e, t)
        if n.kind == 'fv' and n.kids[0].text() in ('Nfloor', 'Nceil') and t == 'NN0':
            x = n.kids[1].text()
            lab = 'nfloorcl' if n.kids[0].text() == 'Nfloor' else 'nceilcl'
            i = w.s([], lab, '( %s e. RR -> %s e. NN0 )' % (x, e))
            return self._s([self.mem(x, 'RR'), i], 'syl', e, t)
        if n.kind == 'fv' and n.kids[0].text() == 'sqrt' and t == 'RR':
            x = n.kids[1].text()
            return self._s([self.mem(x, 'RR'), self.ge0(x)], 'resqrtcld', e, t)
        if n.kind == 'ov':
            A, F, B = n.kids[0].text(), n.kids[1].text(), n.kids[2].text()
            if F == 'Nlog' and t == 'NN0':
                i = w.s([], 'nlogcl', '( ( %s e. NN0 /\\ %s e. NN0 ) -> %s e. NN0 )' % (A, B, e))
                cj = self.jca([self.mem(A, 'NN0'), self.mem(B, 'NN0')],
                              ['%s e. NN0' % A, '%s e. NN0' % B])
                return self._s([cj, i], 'syl', e, t)
            if F == '^c' and t == 'RR':
                i = w.s([], 'recxpcl', '( ( %s e. RR /\\ 0 <_ %s /\\ %s e. RR ) -> %s e. RR )'
                        % (A, A, B, e))
                cj = w.s([self.mem(A, 'RR'), self.ge0(A), self.mem(B, 'RR')], '3jca',
                         '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s e. RR ) )' % (self.ante, A, A, B))
                return self._s([cj, i], 'syl', e, t)
            if F == '+' and t in ('NN0', 'NN', 'ZZ'):
                lab = {'NN0': 'nn0addcld', 'NN': 'nnaddcld', 'ZZ': 'zaddcld'}[t]
                return self._s([self.mem(A, t), self.mem(B, t)], lab, e, t)
            if F == 'x.' and t in ('NN0', 'NN', 'ZZ'):
                lab = {'NN0': 'nn0mulcld', 'NN': 'nnmulcld', 'ZZ': 'zmulcld'}[t]
                return self._s([self.mem(A, t), self.mem(B, t)], lab, e, t)
            if F == '-' and t == 'NN0' and B == '1':
                return self._s([self.mem(A, 'NN'), w.s([], 'nnm1nn0', '( %s e. NN -> %s e. NN0 )' % (A, e))], 'syl', e, t)
            if F == '-' and t == 'ZZ':
                return self._s([self.mem(A, 'ZZ'), self.mem(B, 'ZZ')], 'zsubcld', e, t)
            if F == '^' and t in ('NN0', 'NN'):
                lab = {'NN0': 'nn0expcld', 'NN': 'nnexpcld'}[t]
                return self._s([self.mem(A, t), self.mem(B, 'NN0')], lab, e, t)
            if F == 'mod' and t == 'NN0':
                i = w.s([], 'zmodcl', '( ( %s e. ZZ /\\ %s e. NN ) -> %s e. NN0 )' % (A, B, e))
                return self._s([self.mem(A, 'ZZ'), self.mem(B, 'NN'), i], 'syl2anc', e, t)
            if F == '++' and t == W0:
                i = w.s([], 'ccatcl', '( ( %s e. %s /\\ %s e. %s ) -> %s e. %s )' % (A, W0, B, W0, e, t))
                return self._s([self.mem(A, W0), self.mem(B, W0), i], 'syl2anc', e, t)
            if F == 'substr' and t == W0:
                i = w.s([], 'swrdcl', '( %s e. %s -> %s e. %s )' % (A, W0, e, t))
                return self._s([self.mem(A, W0)], 'x', e, t) if False else \
                    self._s([self.mem(A, W0), i], 'syl', e, t)
        if n.kind == 's1' and t == W0:
            i = w.s([], 's1cl', '( %s e. NN0 -> %s e. %s )' % (n.kids[0].text(), e, t))
            return self._s([self.mem(n.kids[0].text(), 'NN0'), i], 'syl', e, t)
        if t in ALIAS:
            st = self.mem(e, ALIAS[t])
            df = w.s([w.s([], 'df-' + t.lower(), '%s = %s' % (t, ALIAS[t]))], 'a1i',
                     '( %s -> %s = %s )' % (ante, t, ALIAS[t]))
            return self._s([st, df], 'eleqtrrd', e, t)
        raise ClError('no rule for %s e. %s' % (e, t))


def _isfrac(e):
    return bool(re.match(r'^\( (?:; )*[0-9 ]+ / (?:; )*[0-9 ]+ \)$', e))


def _balanced(s):
    d = 0
    for tk in s.split():
        if tk == '(':
            d += 1
        elif tk == ')':
            d -= 1
            if d < 0:
                return False
    return d == 0


def _balanced_xp(t):
    return _split_xp(t) is not None


def _split_top(s, op):
    """split `( A op B )` at the top-level op; returns (A, B) or None"""
    toks = s.split()
    if not toks or toks[0] != '(' or toks[-1] != ')':
        return None
    inner = toks[1:-1]
    d = 0
    for i, tk in enumerate(inner):
        if tk == '(':
            d += 1
        elif tk == ')':
            d -= 1
        elif tk == op and d == 0:
            return ' '.join(inner[:i]), ' '.join(inner[i + 1:])
    return None


def _split_xp(t):
    return _split_top(t, 'X.')


def _split_dju(t):
    return _split_top(t, '|_|')


# ------------------------------------------------------- definition unfolding
def _eqhyp(w, binders, args, body):
    """step proving ( ( x = A /\\ y = B ) -> body = body[A,B] ) and the new body"""
    if len(binders) == 1:
        ante = '%s = %s' % (binders[0], args[0])
        leaves = {binders[0]: w.s([], 'id', '( %s -> %s )' % (ante, ante))}
    else:
        ante = '( %s = %s /\\ %s = %s )' % (binders[0], args[0], binders[1], args[1])
        leaves = {binders[0]: w.s([], 'simpl', '( %s -> %s = %s )' % (ante, binders[0], args[0])),
                  binders[1]: w.s([], 'simpr', '( %s -> %s = %s )' % (ante, binders[1], args[1]))}
    sub = dict(zip(binders, args))
    st, new = w.congr(body, sub, ante, leaves)
    if st is None:
        st = w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, body, body))
        new = body
    return st, new


def mptfv(w, cl, mpt, arg, argstep=None, name=None, dom=None, x=None, body=None, defref=None, F=None):
    """( ante -> ( F ` arg ) = body[arg/x] ) with F = ( x e. dom |-> body );
    defref: the label proving F = mpt ('eqid' when F is the mapping itself)."""
    if x is None:
        n = _c.parse(mpt)
        assert n.kind == 'mpt', mpt
        x = n.bound[0]
        dom = n.kids[0].text()
        body = n.kids[1].text()
    if F is None:
        F, defref = mpt, 'eqid'
    e1, val = _eqhyp(w, [x], [arg], body)
    e2 = w.s([], defref, '%s = %s' % (F, mpt))
    if argstep is None:
        argstep = cl.mem(arg, dom)
    vst = cl.mem(val, '_V')
    i = w.s([e1, e2], 'fvmptg',
            '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (arg, dom, val, F, arg, val))
    return w.s([argstep, vst, i], 'syl2anc',
               '( %s -> ( %s ` %s ) = %s )' % (cl.ante, F, arg, val), name=name), val


def mpoov(w, cl, mpo, A, B, astep=None, bstep=None, name=None, defref=None, F=None):
    """( ante -> ( A F B ) = body[A,B] ) with F = ( x e. C , y e. D |-> body )"""
    n = _c.parse(mpo)
    assert n.kind == 'mpo', mpo
    x, y = n.bound
    C, Dm = n.kids[0].text(), n.kids[1].text()
    body = n.kids[2].text()
    if F is None:
        F, defref = mpo, 'eqid'
    e1, val = _eqhyp(w, [x, y], [A, B], body)
    e2 = w.s([], defref, '%s = %s' % (F, mpo))
    if astep is None:
        astep = cl.mem(A, C)
    if bstep is None:
        bstep = cl.mem(B, Dm)
    vst = cl.mem(val, '_V')
    i = w.s([e1, e2], 'ovmpoga',
            '( ( %s e. %s /\\ %s e. %s /\\ %s e. _V ) -> ( %s %s %s ) = %s )'
            % (A, C, B, Dm, val, A, F, B, val))
    return w.s([astep, bstep, vst, i], 'syl3anc',
               '( %s -> ( %s %s %s ) = %s )' % (cl.ante, A, F, B, val), name=name), val


def defmpt(label):
    """the right-hand side of a df- whose body is a mapping"""
    return tm.defbody(label)


# ---------------------------------------------------- the four theorems of a recursion
def defapply(w, cl, label, const, args, body=None):
    """Unfold a definition at its arguments, following the arity convention:
    ( f ` A ), ( A f B ), ( ( A f B ) ` C ) ...  Returns (step, value) where the
    step proves ( ante -> applied = value )."""
    if body is None:
        body = tm.defbody(label)
    n = _c.parse(body)
    if n.kind == 'mpo':
        st, val = mpoov(w, cl, body, args[0], args[1], defref=label, F=const)
        applied = '( %s %s %s )' % (args[0], const, args[1])
        rest = args[2:]
    else:
        st, val = mptfv(w, cl, body, args[0], defref=label, F=const)
        applied = '( %s ` %s )' % (const, args[0])
        rest = args[1:]
    for a in rest:
        nxt = '( %s ` %s )' % (applied, a)
        e1 = w.s([st], 'fveq1d', '( %s -> %s = ( %s ` %s ) )' % (cl.ante, nxt, val, a))
        e2, val2 = mptfv(w, cl, val, a)
        st = w.s([e1, e2], 'eqtrd', '( %s -> %s = %s )' % (cl.ante, nxt, val2))
        applied, val = nxt, val2
    return st, val


def applied_text(const, args):
    if len(args) == 1:
        return '( %s ` %s )' % (const, args[0])
    t = '( %s %s %s )' % (args[0], const, args[1])
    for a in args[2:]:
        t = '( %s ` %s )' % (t, a)
    return t


class Spec:
    """A recursion of Algorithm.lean.

    leanargs: [(binder in df-, type, class variable, role)] in Lean's order;
      role is 'fix' (kept outside the recursion), 'chg' (a parameter of the
      recursion) or 'fuel' (the recursion index; absent for a list recursion,
      where the index is the length of the 'chg' word given by `listvar`).
    base: the level-0 value, in terms of the binder `g`.
    """

    def __init__(self, tok, stok, dom, cod, leanargs, base, listvar=None, desc=''):
        self.tok, self.stok = tok, stok
        self.dom, self.cod = dom, cod
        self.leanargs = leanargs
        self.base = base
        self.listvar = listvar
        self.desc = desc
        self.df = 'df-' + tok.lower()
        self.dfs = 'df-' + stok.lower()
        self.fix = [a for a in leanargs if a[3] == 'fix']
        self.chg = [a for a in leanargs if a[3] == 'chg']
        self.fuel = [a for a in leanargs if a[3] == 'fuel']
        self.hm = MAP(cod, dom)

    def stepinst(self, vals=None):
        vals = vals or [a[2] for a in self.fix]
        if not vals:
            return self.stok
        return applied_text(self.stok, vals)

    def basemap(self):
        return '( g e. %s |-> %s )' % (self.dom, self.base)

    def lev(self, lvl, fixvals=None):
        return '( ( %s AlgRec %s ) ` %s )' % (self.basemap(), self.stepinst(fixvals), lvl)

    def ctuple(self, vals=None):
        """the parameter tuple from the changing arguments"""
        vals = vals if vals is not None else [a[2] for a in self.chg]
        t = vals[-1]
        for v in reversed(vals[:-1]):
            t = '<. %s , %s >.' % (v, t)
        return t

    def level_text(self, chgvals=None):
        if self.fuel:
            return self.fuel[0][2]
        cv = chgvals if chgvals is not None else [a[2] for a in self.chg]
        return '( # ` %s )' % cv[self.listvar]

    def call(self, vals=None):
        """the applied form ( ( A f B ) ` C ) ... at class variables"""
        vals = vals or [a[2] for a in self.leanargs]
        return applied_text(self.tok, vals)

    def _peel(self):
        """the ( h , u |-> ( c e. Dom |-> CLAUSE ) ) node of df-XXXS"""
        n = _c.parse(tm.defbody(self.dfs))
        left = len(self.fix)
        while left:
            if n.kind == 'mpo':
                n, left = n.kids[2], left - 2
            else:
                n, left = n.kids[1], left - 1
        assert n.kind == 'mpo' and left == 0, (n.kind, left)
        return n

    def clause(self):
        """the step clause, with the fixed binders replaced by their class
        variables, as it stands in df-XXXS (binders h, u, c)"""
        n = self._peel()
        inner = n.kids[2]
        assert inner.kind == 'mpt', inner.kind
        cls = inner.kids[1].text()
        sub = {a[0]: a[2] for a in self.fix}
        return tm.sub(cls, sub) if sub else cls

    def mpo(self, fixvals=None):
        fixvals = fixvals or [a[2] for a in self.fix]
        sub = {a[0]: v for a, v in zip(self.fix, fixvals)}
        t = self._peel().text()
        return tm.sub(t, sub) if sub else t


def ante_and(*parts):
    a = parts[0]
    for p in parts[1:]:
        a = '( %s /\\ %s )' % (a, p)
    return a


def typed(pairs):
    """'( A e. T /\\ B e. U )' grouped in twos, or the single conjunct"""
    if not pairs:
        return None
    cs = ['%s e. %s' % (v, t) for v, t in pairs]
    return ante_and(*cs)


def split_and(w, ante, step, parts, out=None):
    """From a step proving ( ante -> ante_and(*parts) ), return a dict part ->
    step proving ( ante -> part ), by repeated simpld/simprd."""
    out = {} if out is None else out
    if len(parts) == 1:
        out[parts[0]] = step
        return out
    left = ante_and(*parts[:-1])
    a = w.s([step], 'simpld', '( %s -> %s )' % (ante, left))
    b = w.s([step], 'simprd', '( %s -> %s )' % (ante, parts[-1]))
    out[parts[-1]] = b
    return split_and(w, ante, a, parts[:-1], out)


def conjsteps(w, parts):
    """the antecedent ante_and(*parts) and a dict part -> step proving
    ( ante -> part ), by simpr / simpld+simprd"""
    ante = ante_and(*parts)
    if len(parts) == 1:
        return ante, {parts[0]: w.s([], 'id', '( %s -> %s )' % (ante, parts[0]))}
    out = {parts[-1]: w.s([], 'simpr', '( %s -> %s )' % (ante, parts[-1]))}
    left = ante_and(*parts[:-1])
    a = w.s([], 'simpl', '( %s -> %s )' % (ante, left))
    split_and(w, ante, a, parts[:-1], out)
    return ante, out


def fixante(sp):
    return typed([(a[2], a[1]) for a in sp.fix])


def stepeq(w, cl, sp):
    """( ante -> STEPINST = MPO ), or a closed equation when there are no fixed
    arguments."""
    if sp.fix:
        return defapply(w, cl, sp.dfs, sp.stok, [a[2] for a in sp.fix])[0]
    e = w.s([], sp.dfs, '%s = %s' % (sp.stok, sp.mpo()))
    return w.s([e], 'a1i', '( %s -> %s = %s )' % (cl.ante, sp.stok, sp.mpo()))


def th_sf(sp, clauseclosure):
    """the step-typing theorem
    ( fixed typed -> STEPINST : ( ( Cod ^m Dom ) X. NN0 ) --> ( Cod ^m Dom ) )"""
    lab = sp.tok.lower() + 'sf'
    hm, si, mpo = sp.hm, sp.stepinst(), sp.mpo()
    fixparts = ['%s e. %s' % (a[2], a[1]) for a in sp.fix]
    w = W(lab, 'The step operation of ~ %s carries a level function and an index to a '
               'level function, the hypothesis ~ algrecmap needs.%s' % (sp.df, sp.desc))
    parts = fixparts + ['h e. %s' % hm, 'u e. NN0', 'c e. %s' % sp.dom]
    a4, st4 = conjsteps(w, parts)
    cl4 = Cl(w, a4)
    for a in sp.fix:
        cl4.have(a[2], a[1], st4['%s e. %s' % (a[2], a[1])])
    cl4.have('h', hm, st4['h e. %s' % hm])
    cl4.have('u', 'NN0', st4['u e. NN0'])
    cl4.have('c', sp.dom, st4['c e. %s' % sp.dom])
    clause = sp.clause()
    inner = clauseclosure(w, cl4, sp)
    a3 = ante_and(*parts[:-1])
    bm = '( c e. %s |-> %s )' % (sp.dom, clause)
    fm = w.s([inner, w.s([], 'eqid', '%s = %s' % (bm, bm))], 'fmptd',
             '( %s -> %s : %s --> %s )' % (a3, bm, sp.dom, sp.cod))
    cl3 = Cl(w, a3)
    dv, cv = cl3.mem(sp.dom, '_V'), cl3.mem(sp.cod, '_V')
    em = w.s([cv, dv, w.s([], 'elmapg', '( ( %s e. _V /\\ %s e. _V ) -> ( %s e. %s <-> %s : %s --> %s ) )'
                          % (sp.cod, sp.dom, bm, hm, bm, sp.dom, sp.cod))], 'syl2anc',
             '( %s -> ( %s e. %s <-> %s : %s --> %s ) )' % (a3, bm, hm, bm, sp.dom, sp.cod))
    el = w.s([fm, em], 'mpbird', '( %s -> %s e. %s )' % (a3, bm, hm))
    a2 = ante_and(*parts[:-2])
    r1 = w.s([el], 'ralrimiva', '( %s -> A. u e. NN0 %s e. %s )' % (a2, bm, hm))
    ral = 'A. h e. %s A. u e. NN0 %s e. %s' % (hm, bm, hm)
    bi = w.s([w.s([], 'eqid', '%s = %s' % (mpo, mpo))], 'fmpo',
             '( %s <-> %s : ( %s X. NN0 ) --> %s )' % (ral, mpo, hm, hm))
    if sp.fix:
        fa = ante_and(*fixparts)
        r2 = w.s([r1], 'ralrimiva', '( %s -> %s )' % (fa, ral))
        fst = w.s([r2, bi], 'sylib', '( %s -> %s : ( %s X. NN0 ) --> %s )' % (fa, mpo, hm, hm))
        _, hs = conjsteps(w, fixparts)
        clf = Cl(w, fa)
        for a in sp.fix:
            clf.have(a[2], a[1], hs['%s e. %s' % (a[2], a[1])])
        eqs = stepeq(w, clf, sp)
        b2 = w.s([eqs], 'feq1d', '( %s -> ( %s : ( %s X. NN0 ) --> %s <-> %s : ( %s X. NN0 ) --> %s ) )'
                 % (fa, si, hm, hm, mpo, hm, hm))
        w.qed([b2, fst], 'mpbird', '( %s -> %s : ( %s X. NN0 ) --> %s )' % (fa, si, hm, hm))
    else:
        r3 = w.s([r1], 'rgen', ral)
        fst = w.s([r3, bi], 'mpbi', '%s : ( %s X. NN0 ) --> %s' % (mpo, hm, hm))
        eqs = w.s([], sp.dfs, '%s = %s' % (sp.stok, mpo))
        b2 = w.s([eqs], 'feq1i', '( %s : ( %s X. NN0 ) --> %s <-> %s : ( %s X. NN0 ) --> %s )'
                 % (si, hm, hm, mpo, hm, hm))
        w.qed([b2, fst], 'mpbir', '%s : ( %s X. NN0 ) --> %s' % (si, hm, hm))
    return w


def _fsf(w, cl, sp):
    """( ante -> STEPINST : ( HM X. NN0 ) --> HM ) from the sortie's own `fsf`"""
    hm, si = sp.hm, sp.stepinst()
    concl = '%s : ( %s X. NN0 ) --> %s' % (si, hm, hm)
    lab = sp.tok.lower() + 'sf'
    if not sp.fix:
        return w.s([w.s([], lab, concl)], 'a1i', '( %s -> %s )' % (cl.ante, concl))
    hs = [cl.mem(a[2], a[1]) for a in sp.fix]
    i = w.s([], lab, '( %s -> %s )'
            % (ante_and(*['%s e. %s' % (a[2], a[1]) for a in sp.fix]), concl))
    if len(hs) == 1:
        return w.s([hs[0], i], 'syl', '( %s -> %s )' % (cl.ante, concl))
    cj = cl.jca(hs, ['%s e. %s' % (a[2], a[1]) for a in sp.fix])
    return w.s([cj, i], 'syl', '( %s -> %s )' % (cl.ante, concl))


def _basein(w, cl, sp):
    """( ante -> BASEMAP e. HM )"""
    bm, hm = sp.basemap(), sp.hm
    a2 = '( %s /\\ g e. %s )' % (cl.ante, sp.dom)
    cg = Cl(w, a2)
    cg.have('g', sp.dom, w.s([], 'simpr', '( %s -> g e. %s )' % (a2, sp.dom)))
    b = cg.mem(sp.base, sp.cod)
    fm = w.s([b, w.s([], 'eqid', '%s = %s' % (bm, bm))], 'fmptd',
             '( %s -> %s : %s --> %s )' % (cl.ante, bm, sp.dom, sp.cod))
    em = w.s([cl.mem(sp.cod, '_V'), cl.mem(sp.dom, '_V'), w.s([], 'elmapg', '( ( %s e. _V /\\ %s e. _V ) -> ( %s e. %s <-> %s : %s --> %s ) )'
                          % (sp.cod, sp.dom, bm, hm, bm, sp.dom, sp.cod))], 'syl2anc',
             '( %s -> ( %s e. %s <-> %s : %s --> %s ) )' % (cl.ante, bm, hm, bm, sp.dom, sp.cod))
    return w.s([fm, em], 'mpbird', '( %s -> %s e. %s )' % (cl.ante, bm, hm))


def _levin(w, cl, sp, lvl, lvlstep):
    """( ante -> ( Lev ` lvl ) e. HM )"""
    hm = sp.hm
    hv = cl.mem(hm, '_V')
    bi = _basein(w, cl, sp)
    sf = _fsf(w, cl, sp)
    tri = w.s([hv, bi, sf], 'jca31' if False else '3jca',
              '( %s -> ( %s e. _V /\\ %s e. %s /\\ %s : ( %s X. NN0 ) --> %s ) )'
              % (cl.ante, hm, sp.basemap(), hm, sp.stepinst(), hm, hm))
    i = w.s([], 'algrecmap', '( ( ( %s e. _V /\\ %s e. %s /\\ %s : ( %s X. NN0 ) --> %s ) /\\ %s e. NN0 ) -> %s e. %s )'
            % (hm, sp.basemap(), hm, sp.stepinst(), hm, hm, lvl, sp.lev(lvl), hm))
    return w.s([tri, lvlstep, i], 'syl2anc',
               '( %s -> %s e. %s )' % (cl.ante, sp.lev(lvl), hm))


def _stepset(w, cl, sp):
    """( ante -> STEPINST e. _V )"""
    hm = sp.hm
    sf = _fsf(w, cl, sp)
    xp = w.s([cl.mem(hm, '_V'), cl.mem('NN0', '_V'),
              w.s([], 'xpexg', '( ( %s e. _V /\\ NN0 e. _V ) -> ( %s X. NN0 ) e. _V )' % (hm, hm))],
             'syl2anc', '( %s -> ( %s X. NN0 ) e. _V )' % (cl.ante, hm))
    fx = w.s([], 'fex', '( ( %s : ( %s X. NN0 ) --> %s /\\ ( %s X. NN0 ) e. _V ) -> %s e. _V )'
             % (sp.stepinst(), hm, hm, hm, sp.stepinst()))
    return w.s([sf, xp, fx], 'syl2anc', '( %s -> %s e. _V )' % (cl.ante, sp.stepinst()))


def th_cl(sp):
    """( args typed -> CALL e. Cod )"""
    lab = sp.tok.lower() + 'cl'
    parts = ['%s e. %s' % (a[2], a[1]) for a in sp.leanargs]
    ante, hs = conjsteps(w := W(lab, 'The value of ~ %s is a pair of a result and an '
                                     'operation count.%s' % (sp.df, sp.desc)), parts)
    cl = Cl(w, ante)
    for a in sp.leanargs:
        cl.have(a[2], a[1], hs['%s e. %s' % (a[2], a[1])])
    eqf, val = defapply(w, cl, sp.df, sp.tok, [a[2] for a in sp.leanargs])
    lvl = sp.level_text()
    lv = _levin(w, cl, sp, lvl, cl.mem(lvl, 'NN0'))
    cl.have(sp.lev(lvl), sp.hm, lv)
    ct = cl.mem(val, sp.cod)
    w.qed([eqf, ct], 'eqeltrd', '( %s -> %s e. %s )' % (ante, sp.call(), sp.cod))
    return w


def th_0(sp):
    """Lean's eq_1: the value at fuel 0 (or at the empty list)"""
    lab = sp.tok.lower() + '0'
    if sp.fuel:
        vals = [('0' if a[3] == 'fuel' else a[2]) for a in sp.leanargs]
        keep = [a for a in sp.leanargs if a[3] != 'fuel']
        lvl0 = '0'
    else:
        lw = sp.chg[sp.listvar]
        vals = [('(/)' if a is lw else a[2]) for a in sp.leanargs]
        keep = [a for a in sp.leanargs if a is not lw]
        lvl0 = '( # ` (/) )'
    parts = ['%s e. %s' % (a[2], a[1]) for a in keep]
    w = W(lab, 'The base of the recursion of ~ %s , Lean\'s first equation lemma.%s'
          % (sp.df, sp.desc))
    if parts:
        ante, hs = conjsteps(w, parts)
    else:
        ante, hs = 'T.', {}
    cl = Cl(w, ante)
    for a in keep:
        cl.have(a[2], a[1], hs['%s e. %s' % (a[2], a[1])])
    eqf, val = defapply(w, cl, sp.df, sp.tok, vals)
    cur = eqf
    if not sp.fuel:
        h0 = w.s([w.s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ante)
        st, val2 = w.rewrite(val, {'( # ` (/) )': ('0', h0)}, ante)
        cur = w.s([cur, st], 'eqtrd', '( %s -> %s = %s )' % (ante, applied_text(sp.tok, vals), val2))
        val = val2
    bmv = cl.mem(sp.basemap(), '_V')
    ssv = _stepset(w, cl, sp)
    a0 = w.s([bmv, ssv, w.s([], 'algrec0', '( ( %s e. _V /\\ %s e. _V ) -> %s = %s )'
                            % (sp.basemap(), sp.stepinst(), sp.lev('0'), sp.basemap()))], 'syl2anc',
             '( %s -> %s = %s )' % (ante, sp.lev('0'), sp.basemap()))
    chg = [('(/)' if (not sp.fuel and a is sp.chg[sp.listvar]) else a[2]) for a in sp.chg]
    ct = sp.ctuple(chg)
    f1 = w.s([a0], 'fveq1d', '( %s -> %s = ( %s ` %s ) )' % (ante, val, sp.basemap(), ct))
    f2, bval = mptfv(w, cl, sp.basemap(), ct)
    c1 = w.s([cur, f1], 'eqtrd', '( %s -> %s = ( %s ` %s ) )' % (ante, applied_text(sp.tok, vals), sp.basemap(), ct))
    c2 = w.s([c1, f2], 'eqtrd', '( %s -> %s = %s )' % (ante, applied_text(sp.tok, vals), bval))
    rs, bval2 = reduceops(w, cl, bval)
    if rs is not None:
        c2 = w.s([c2, rs], 'eqtrd', '( %s -> %s = %s )' % (ante, applied_text(sp.tok, vals), bval2))
        bval = bval2
    if ante == 'T.':
        w.qed([c2], 'mptru', '%s = %s' % (applied_text(sp.tok, vals), bval))
    else:
        promote_qed(w, c2)
    return w


def _rwchain(w, ante, lhs, step, cur, rules):
    """rewrite `cur` by `rules` and chain onto `step` (which proves lhs = cur)"""
    st, new = w.rewrite(cur, rules, ante)
    if st is None:
        return step, cur
    return w.s([step, st], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, new)), new


def consfacts(w, cl, P, Lw):
    """head, length and tail of ( <" P "> ++ Lw ), as rewrite rules"""
    a = cl.ante
    cons = '( <" %s "> ++ %s )' % (P, Lw)
    s1 = w.s([], 's1len', '( # ` <" %s "> ) = 1' % P)
    s1d = w.s([s1], 'a1i', '( %s -> ( # ` <" %s "> ) = 1 )' % (a, P))
    pw = cl.mem('<" %s ">' % P, W0)
    lw = cl.mem(Lw, W0)
    # head
    one = w.s([], '1nn', '1 e. NN')
    lb = w.s([], 'lbfzo0', '( 0 e. ( 0 ..^ 1 ) <-> 1 e. NN )')
    z1 = w.s([one, lb], 'mpbir', '0 e. ( 0 ..^ 1 )')
    oq = w.s([s1], 'oveq2i', '( 0 ..^ ( # ` <" %s "> ) ) = ( 0 ..^ 1 )' % P)
    z2 = w.s([z1, oq], 'eleqtrri', '0 e. ( 0 ..^ ( # ` <" %s "> ) )' % P)
    z2d = w.s([z2], 'a1i', '( %s -> 0 e. ( 0 ..^ ( # ` <" %s "> ) ) )' % (a, P))
    cv = w.s([pw, lw, z2d, w.s([], 'ccatval1',
                                '( ( <" %s "> e. %s /\\ %s e. %s /\\ 0 e. ( 0 ..^ ( # ` <" %s "> ) ) ) -> ( %s ` 0 ) = ( <" %s "> ` 0 ) )'
                                % (P, W0, Lw, W0, P, cons, P))], 'syl3anc',
             '( %s -> ( %s ` 0 ) = ( <" %s "> ` 0 ) )' % (a, cons, P))
    fv = w.s([cl.mem(P, 'NN0'), w.s([], 's1fv', '( %s e. NN0 -> ( <" %s "> ` 0 ) = %s )' % (P, P, P))],
             'syl', '( %s -> ( <" %s "> ` 0 ) = %s )' % (a, P, P))
    hd = w.s([cv, fv], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (a, cons, P))
    # length
    cln = w.s([pw, lw, w.s([], 'ccatlen', '( ( <" %s "> e. %s /\\ %s e. %s ) -> ( # ` %s ) = ( ( # ` <" %s "> ) + ( # ` %s ) ) )'
                            % (P, W0, Lw, W0, cons, P, Lw))], 'syl2anc',
              '( %s -> ( # ` %s ) = ( ( # ` <" %s "> ) + ( # ` %s ) ) )' % (a, cons, P, Lw))
    ln1 = w.s([s1d], 'oveq1d', '( %s -> ( ( # ` <" %s "> ) + ( # ` %s ) ) = ( 1 + ( # ` %s ) ) )' % (a, P, Lw, Lw))
    ln = w.s([cln, ln1], 'eqtrd', '( %s -> ( # ` %s ) = ( 1 + ( # ` %s ) ) )' % (a, cons, Lw))
    # tail
    old = '( %s substr <. ( # ` <" %s "> ) , ( ( # ` <" %s "> ) + ( # ` %s ) ) >. )' % (cons, P, P, Lw)
    sw = w.s([pw, lw, w.s([], 'swrdccat2', '( ( <" %s "> e. %s /\\ %s e. %s ) -> %s = %s )'
                           % (P, W0, Lw, W0, old, Lw))], 'syl2anc', '( %s -> %s = %s )' % (a, old, Lw))
    rw, new = w.rewrite(old, {'( # ` <" %s "> )' % P: ('1', s1d)}, a)
    tl = w.s([rw, sw], 'eqtr3d', '( %s -> %s = %s )' % (a, new, Lw))
    assert new == '( %s substr <. 1 , ( 1 + ( # ` %s ) ) >. )' % (cons, Lw), new
    # length in the form ( ( # ` L ) + 1 )
    lc = cl.mem('( # ` %s )' % Lw, 'NN0')
    lcn = w.s([lc], 'nn0cnd', '( %s -> ( # ` %s ) e. CC )' % (a, Lw))
    onec = w.s([], '1cnd', '( %s -> 1 e. CC )' % a)
    ac = w.s([onec, lcn], 'addcomd', '( %s -> ( 1 + ( # ` %s ) ) = ( ( # ` %s ) + 1 ) )' % (a, Lw, Lw))
    ln2 = w.s([ln, ac], 'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (a, cons, Lw))
    return {'hd': ('( %s ` 0 )' % cons, P, hd),
            'len': ('( # ` %s )' % cons, '( 1 + ( # ` %s ) )' % Lw, ln),
            'lenp1': ('( # ` %s )' % cons, '( ( # ` %s ) + 1 )' % Lw, ln2),
            'tl': (new, Lw, tl)}


def th_p1(sp, P='P', Lw='W', extra=None, hook=None, lab=None, desc=None):
    """Lean's second equation lemma: the value at fuel N + 1, or at a cons.
    extra: further hypotheses (wff texts) appended to the antecedent;
    hook(w, cl, sp): returns { condition text: (truth, step) } for ~ reduceifs ,
    after registering any facts the condition provides in `cl`."""
    if sp.fuel:
        fv = sp.fuel[0][2]
        vals = [('( %s + 1 )' % fv if a[3] == 'fuel' else a[2]) for a in sp.leanargs]
        parts = ['%s e. %s' % (a[2], a[1]) for a in sp.leanargs]
        lab = sp.tok.lower() + 'p1'
    else:
        lwv = sp.chg[sp.listvar]
        cons = '( <" %s "> ++ %s )' % (P, Lw)
        vals = [(cons if a is lwv else a[2]) for a in sp.leanargs]
        parts = [('%s e. %s' % (a[2], a[1])) for a in sp.leanargs if a is not lwv]
        parts += ['%s e. NN0' % P, '%s e. %s' % (Lw, W0)]
        lab = lab or sp.tok.lower() + 'cs'
    lab = lab or sp.tok.lower() + 'p1'
    parts = parts + list(extra or [])
    w = W(lab, desc or ('The step of the recursion of ~ %s , Lean\'s second equation lemma.%s'
                        % (sp.df, sp.desc)))
    ante, hs = conjsteps(w, parts)
    cl = Cl(w, ante)
    for p in parts:
        if ' e. ' not in p:
            continue
        v, t = p.split(' e. ', 1)
        cl.have(v, t, hs[p])
    cl.hyps = hs
    cf = None
    if not sp.fuel:
        cf = consfacts(w, cl, P, Lw)
        cl.have(cons, W0, cl.mem(cons, W0))
    call = applied_text(sp.tok, vals)
    eqf, val = defapply(w, cl, sp.df, sp.tok, vals)
    if sp.fuel:
        n = fv
    else:
        n = '( # ` %s )' % Lw
        old, new, st = cf['lenp1']
        eqf, val = _rwchain(w, ante, call, eqf, val, {old: (new, st)})
    # algrecp1
    bmv = cl.mem(sp.basemap(), '_V')
    ssv = _stepset(w, cl, sp)
    nst = cl.mem(n, 'NN0')
    ap = w.s([bmv, ssv, nst, w.s([], 'algrecp1',
                                   '( ( %s e. _V /\\ %s e. _V /\\ %s e. NN0 ) -> %s = ( %s %s %s ) )'
                                   % (sp.basemap(), sp.stepinst(), n, sp.lev('( %s + 1 )' % n), sp.lev(n), sp.stepinst(), n))], 'syl3anc',
             '( %s -> %s = ( %s %s %s ) )' % (ante, sp.lev('( %s + 1 )' % n), sp.lev(n), sp.stepinst(), n))
    se = stepeq(w, cl, sp)
    ov = w.s([se], 'oveqd', '( %s -> ( %s %s %s ) = ( %s %s %s ) )'
             % (ante, sp.lev(n), sp.stepinst(), n, sp.lev(n), sp.mpo(), n))
    lv = _levin(w, cl, sp, n, nst)
    cl.have(sp.lev(n), sp.hm, lv)
    mo, mval = mpoov(w, cl, sp.mpo(), sp.lev(n), n, astep=lv, bstep=nst)
    lvl1 = w.s([w.s([ap, ov], 'eqtrd', '( %s -> %s = ( %s %s %s ) )'
                    % (ante, sp.lev('( %s + 1 )' % n), sp.lev(n), sp.mpo(), n)), mo], 'eqtrd',
               '( %s -> %s = %s )' % (ante, sp.lev('( %s + 1 )' % n), mval))
    chg = [(cons if (not sp.fuel and a is lwv) else a[2]) for a in sp.chg]
    ct = sp.ctuple(chg)
    f1 = w.s([lvl1], 'fveq1d', '( %s -> %s = ( %s ` %s ) )' % (ante, val, mval, ct))
    cur = w.s([eqf, f1], 'eqtrd', '( %s -> %s = ( %s ` %s ) )' % (ante, call, mval, ct))
    f2, cval = mptfv(w, cl, mval, ct)
    cur = w.s([cur, f2], 'eqtrd', '( %s -> %s = %s )' % (ante, call, cval))
    val = cval
    # reduce projections of the explicit parameter tuple
    rs, val2 = reduceops(w, cl, val)
    if rs is not None:
        cur = w.s([cur, rs], 'eqtrd', '( %s -> %s = %s )' % (ante, call, val2))
        val = val2
    # discharge the ` c = (/) ` guard of the clause
    if not sp.fuel:
        ne = consne0(w, cl, P, Lw, cf['lenp1'][2])
        rs, val2 = reduceifs(w, ante, val, {'%s = (/)' % cons: (False, ne)})
        if rs is not None:
            cur = w.s([cur, rs], 'eqtrd', '( %s -> %s = %s )' % (ante, call, val2))
            val = val2
        # reduce head, length and tail of the cons
        for key in ('len', 'tl', 'hd'):
            old, new, st = cf[key]
            cur, val = _rwchain(w, ante, call, cur, val, {old: (new, st)})
        rs, val2 = reduceops(w, cl, val)
        if rs is not None:
            cur = w.s([cur, rs], 'eqtrd', '( %s -> %s = %s )' % (ante, call, val2))
            val = val2
    # user conditions (Lean's `match` on a runtime value)
    if hook is not None:
        conds = hook(w, cl, sp)
        if conds:
            rs, val2 = reduceifs(w, ante, val, conds)
            if rs is not None:
                cur = w.s([cur, rs], 'eqtrd', '( %s -> %s = %s )' % (ante, call, val2))
                val = val2
    # fold the recursive calls
    levn = sp.lev(n)
    for ct2 in sorted(_findcalls(val, levn), key=len, reverse=True):
        parts2 = _untuple(ct2, len(sp.chg))
        vals2 = []
        ci = 0
        for a in sp.leanargs:
            if a[3] == 'chg':
                vals2.append(parts2[ci]); ci += 1
            elif a[3] == 'fuel':
                vals2.append(n if sp.fuel else n)
            else:
                vals2.append(a[2])
        if not sp.fuel:
            vals2 = [(n if a[3] == 'fuel' else v) for a, v in zip(sp.leanargs, vals2)]
        e2, v2 = defapply(w, cl, sp.df, sp.tok, vals2)
        assert v2 == '( %s ` %s )' % (levn, ct2), (v2, ct2)
        back = w.s([e2], 'eqcomd', '( %s -> ( %s ` %s ) = %s )' % (ante, levn, ct2, applied_text(sp.tok, vals2)))
        cur, val = _rwchain(w, ante, call, cur, val,
                            {'( %s ` %s )' % (levn, ct2): (applied_text(sp.tok, vals2), back)})
    promote_qed(w, cur)
    return w


def promote_qed(w, step):
    last = w.lines[-1]
    assert last.startswith(step + ':'), (step, last)
    w.lines[-1] = 'qed' + last[len(step):]


def _findcalls(expr, levn):
    """the arguments X of every ( levn ` X ) occurring in expr"""
    out = set()

    def visit(n):
        if n.kind == 'fv' and n.kids[0].text() == levn:
            out.add(n.kids[1].text())
        for k in n.kids:
            visit(k)
    visit(_c.parse(expr))
    return out


def _untuple(t, k):
    if k == 1:
        return [t]
    m = _split_top(t, ',')
    n = _c.parse(t)
    assert n.kind == 'op', t
    return [n.kids[0].text()] + _untuple(n.kids[1].text(), k - 1)


def reduceops(w, cl, expr):
    """Reduce ( 1st ` <. A , B >. ) and ( 2nd ` <. A , B >. ) throughout `expr`.
    Returns (step proving ( ante -> expr = result ) or None, result)."""
    cur, chain, lhs = expr, [], expr
    while True:
        rules = {}

        def visit(n):
            if n.kind == 'fv' and n.kids[0].text() in ('1st', '2nd') and n.kids[1].kind == 'op':
                A, B = n.kids[1].kids
                sa, sb = cl.mem(A.text(), '_V'), cl.mem(B.text(), '_V')
                first = n.kids[0].text() == '1st'
                i = w.s([], 'op1stg' if first else 'op2ndg',
                        '( ( %s e. _V /\\ %s e. _V ) -> %s = %s )'
                        % (A.text(), B.text(), n.text(), (A if first else B).text()))
                tgt = (A if first else B).text()
                st = w.s([sa, sb, i], 'syl2anc', '( %s -> %s = %s )' % (cl.ante, n.text(), tgt))
                rules[n.text()] = (tgt, st)
                return
            for k in n.kids:
                visit(k)
        visit(_c.parse(cur))
        if not rules:
            break
        st, new = w.rewrite(cur, rules, cl.ante)
        chain.append((st, new))
        cur = new
    if not chain:
        return None, expr
    acc, _ = chain[0]
    prev = chain[0][1]
    for st, new in chain[1:]:
        acc = w.s([acc, st], 'eqtrd', '( %s -> %s = %s )' % (cl.ante, lhs, new))
        prev = new
    return acc, cur


def reduceifs(w, ante, expr, conds):
    """Reduce every `if` whose condition is a key of `conds` (mapping the
    condition text to (truth, step proving it or its negation)).
    Returns (step or None, result)."""
    cur, chain, lhs = expr, [], expr
    while True:
        rules = {}

        def visit(n):
            if n.kind == 'if' and n.kids[0].text() in conds:
                truth, st0 = conds[n.kids[0].text()]
                tgt = n.kids[1 if truth else 2].text()
                st = w.s([st0], 'iftrued' if truth else 'iffalsed',
                         '( %s -> %s = %s )' % (ante, n.text(), tgt))
                rules[n.text()] = (tgt, st)
                return
            for k in n.kids:
                visit(k)
        visit(_c.parse(cur))
        if not rules:
            break
        st, new = w.rewrite(cur, rules, ante)
        chain.append((st, new))
        cur = new
    if not chain:
        return None, expr
    acc = chain[0][0]
    for st, new in chain[1:]:
        acc = w.s([acc, st], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, new))
    return acc, cur


def consne0(w, cl, P, Lw, lenp1step):
    """( ante -> -. ( <" P "> ++ Lw ) = (/) ), from the length step of consfacts"""
    a = cl.ante
    cons = '( <" %s "> ++ %s )' % (P, Lw)
    lc = cl.mem('( # ` %s )' % Lw, 'NN0')
    p1 = w.s([lc, w.s([], 'nn0p1nn', '( ( # ` %s ) e. NN0 -> ( ( # ` %s ) + 1 ) e. NN )' % (Lw, Lw))],
             'syl', '( %s -> ( ( # ` %s ) + 1 ) e. NN )' % (a, Lw))
    n0 = w.s([p1], 'nnne0d', '( %s -> ( ( # ` %s ) + 1 ) =/= 0 )' % (a, Lw))
    ne = w.s([lenp1step, n0], 'eqnetrd', '( %s -> ( # ` %s ) =/= 0 )' % (a, cons))
    nq = w.s([ne], 'neneqd', '( %s -> -. ( # ` %s ) = 0 )' % (a, cons))
    cv = cl.mem(cons, '_V')
    hz = w.s([cv, w.s([], 'hasheq0', '( %s e. _V -> ( ( # ` %s ) = 0 <-> %s = (/) ) )' % (cons, cons, cons))], 'syl',
             '( %s -> ( ( # ` %s ) = 0 <-> %s = (/) ) )' % (a, cons, cons))
    return w.s([nq, hz], 'mtbid', '( %s -> -. %s = (/) )' % (a, cons))
