r"""T15 (e): one theorem per installation predicate at the concrete program.

Kind theorem `t15kX` for `df-tmiX` (X = the predicate's suffix):

  hypotheses (all under ph)
    .1  ( ( T e. _V /\ R e. _V ) /\ ( 1st ` ( 1st ` T ) ) = TMGam /\ ( 2nd ` T ) = TMSt )
    .2  ( ( 0 ... ; 3 0 ) C_ A /\ A C_ NN0 )
    .3  HL  (address labels are labels)
    .4  HM  (the program at an address label is the walked trie, when typed)
    .5  W e. Word A        .6  ( ( # ` W ) + r ) <_ ; 3 0
    .7  P = ( TMLab ` W )  (custom kinds: P = ( TMFX W ... ))
    .8  E e. L             .9  ( R TMWalk W ) = ( TMnX ... T P E )
    .10...  stack parameters in ( 0 ..^ 8 ), numeric parameters (custom kinds)
  conclusion  ( ph -> TMIX ... T M P E )
"""
import os, sys, json, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t15lib import *
import num

P = load_preds()
L_ = '( 2nd ` ( 1st ` T ) )'
S_ = '( TM2Stmt ` T )'
G1 = '( 1st ` ( 1st ` T ) )'
HL = 'A. v e. Word A ( ( # ` v ) <_ ; 3 0 -> ( TMLab ` v ) e. %s )' % L_
HM = ('A. v e. Word A ( ( ( # ` v ) <_ ; 3 0 /\\ ( R TMWalk v ) e. %s ) -> '
      '( M ` ( TMLab ` v ) ) = ( R TMWalk v ) )' % S_)
CTX = ['( ( T e. _V /\\ R e. _V ) /\\ %s = TMGam /\\ ( 2nd ` T ) = TMSt )' % G1,
       '( ( 0 ... ; 3 0 ) C_ A /\\ A C_ NN0 )', HL, HM]
STACKV = ["K", "J", "I", "I'", "I\"", "I0", "K0", "J0"]
REG = os.path.join(ROOT, 'scratch', 't15', 'kinds.json')


def label_of(name):
    return 't15k' + name[3:].lower().replace("'", 'p').replace('"', 'q')


def subst_toks(toks, m):
    return [x for t in toks for x in (m[t].split() if t in m else [t])]


# ------------------------------------------------------------ structure
def chains(toks):
    """all maximal ( ... ( P ` a ) ` b ... ) chains: list of index lists"""
    out = []
    for i, t in enumerate(toks):
        if t == 'P' and i > 0 and toks[i - 1] == '(' and toks[i + 1] == '`':
            start = i - 1; idx = []
            while True:
                end = grab(toks, start)
                inner = toks[start + 1:end - 1]
                # inner = X ` n
                d = 0
                for k, x in enumerate(inner):
                    if x in OPEN: d += 1
                    elif x in CLOSE: d -= 1
                    elif d == 0 and x == '`': break
                try:
                    idx.append(numtok(inner, k + 1)[0])
                except Exception:
                    idx = None; break
                if start > 0 and toks[start - 1] == '(' and end < len(toks) and toks[end] == '`':
                    start -= 1
                else:
                    break
            if idx is not None:
                out.append(idx)
    return out


_REQ = {}


def req(name):
    if name in _REQ: return _REQ[name]
    if name == 'TMIpnv':
        _REQ[name] = 1; return 1
    vs, b, lab = P[name]
    r = 1
    for c in chains(b):
        r = max(r, len(c))
    for i, e in entries(name, P).items():
        if e[0] == 'fam':
            r = max(r, 1 + req(e[1]))
    _REQ[name] = r
    return r


def stack_params(name):
    return [v for v in P[name][0] if v in STACKV]


# ------------------------------------------------------------ the builder
class Kind:
    def __init__(self, name):
        self.name = name
        self.vs, self.body, self.dflab = P[name]
        self.lab = label_of(name)
        self.w = W(self.lab, 'The installation predicate ~ %s holds at the concrete program (generated).' % self.dflab)
        self.ph = 'ph'
        self.r = req(name)
        self.ent = entries(name, P)
        self.memo = {}
        self.w.memo = {}

    # -- small closed facts
    def s(self, hyps, ref, f):
        return self.w.s(hyps, ref, f)

    def c(self, f, ref, hyps=()):
        """closed step, memoized"""
        if f in self.memo: return self.memo[f]
        st = self.w.s(list(hyps), ref, f); self.memo[f] = st; return st

    def d(self, st, f):
        """( ph -> f ) from closed step st"""
        key = ('d', f)
        if key in self.memo: return self.memo[key]
        r = self.w.s([st], 'a1i', '( ph -> %s )' % f); self.memo[key] = r; return r

    def hyp(self, n, f):
        name = 'h%d' % n
        self.w.lines.append('%s::%s.%d |- ( ph -> %s )' % (name, self.lab, n, f))
        return name

    # -- context
    def context(self):
        w = self.w
        self.H = []
        for i, f in enumerate(CTX):
            self.H.append(self.hyp(i + 1, f))
        t = self.H[0]
        self.tr = self.s([t], 'simp1d', '( ph -> ( T e. _V /\\ R e. _V ) )')
        self.tv = self.s([self.tr], 'simpld', '( ph -> T e. _V )')
        self.rv = self.s([self.tr], 'simprd', '( ph -> R e. _V )')
        self.tg = self.s([t], 'simp2d', '( ph -> %s = TMGam )' % G1)
        self.ts = self.s([t], 'simp3d', '( ph -> ( 2nd ` T ) = TMSt )')
        self.s20 = self.s([self.H[1]], 'simpld', '( ph -> ( 0 ... ; 3 0 ) C_ A )')
        self.sA = self.s([self.H[1]], 'simprd', '( ph -> A C_ NN0 )')
        self.hl, self.hm = self.H[2], self.H[3]
        n = 5
        self.hw = self.hyp(n, 'W e. Word A'); n += 1
        self.hd = self.hyp(n, '( ( # ` W ) + %s ) <_ ; 3 0' % num_text(self.r)); n += 1
        self.famterm = self.fam_term()
        self.hp = self.hyp(n, 'P = %s' % self.famterm); n += 1
        self.he = self.hyp(n, 'E e. %s' % L_); n += 1
        self.content = csyn(self.name, P)
        self.hr = self.hyp(n, '( R TMWalk W ) = %s' % self.content); n += 1
        self.par = {}
        for v in stack_params(self.name):
            self.par[v] = self.hyp(n, '%s e. ( 0 ..^ 8 )' % v); n += 1
        self.extra_hyps(n)

    def fam_term(self):
        return '( TMLab ` W )'

    def extra_hyps(self, n):
        pass

    # -- numerals
    def nn0d(self, n):
        return self.d(num.nn0(self.w, n), '%s e. NN0' % num_text(n))

    def inA(self, i):
        key = ('inA', i)
        if key in self.memo: return self.memo[key]
        w = self.w
        a = num.nn0(w, i); b = num.nn0(w, 30); c = num.le_nat(w, i, 30)
        e = self.c('( %s e. ( 0 ... ; 3 0 ) <-> ( %s e. NN0 /\\ ; 3 0 e. NN0 /\\ %s <_ ; 3 0 ) )' % (num_text(i), num_text(i), num_text(i)), 'elfz2nn0')
        f = self.c('%s e. ( 0 ... ; 3 0 )' % num_text(i), 'mpbir3an', [a, b, c, e])
        r = self.s([self.s20, self.d(f, '%s e. ( 0 ... ; 3 0 )' % num_text(i))], 'sseldd', '( ph -> %s e. A )' % num_text(i))
        self.memo[key] = r
        return r

    def stackd(self, k):
        """( ph -> k e. ( 0 ..^ 8 ) )"""
        if k in self.par: return self.par[k]
        key = ('stk', k)
        if key in self.memo: return self.memo[key]
        n = int(k)
        w = self.w
        a = num.nn0(w, n); b = self.c('8 e. NN', '8nn'); c = num.le_nat(w, n, 8, strict=True)
        e = self.c('( %s e. ( 0 ..^ 8 ) <-> ( %s e. NN0 /\\ 8 e. NN /\\ %s < 8 ) )' % (k, k, k), 'elfzo0')
        f = self.c('%s e. ( 0 ..^ 8 )' % k, 'mpbir3an', [a, b, c, e])
        r = self.d(f, '%s e. ( 0 ..^ 8 )' % k)
        self.memo[key] = r
        return r

    def kdom(self, k):
        key = ('kdom', k)
        if key in self.memo: return self.memo[key]
        j = self.s([self.tg, self.stackd(k)], 'jca', '( ph -> ( %s = TMGam /\\ %s e. ( 0 ..^ 8 ) ) )' % (G1, k))
        r = self.s([j, self.w.inst('t15kdom')], 'syl', '( ph -> ( %s e. dom %s /\\ ( %s ` %s ) = Gamma\' ) )' % (k, G1, G1, k))
        a = self.s([r], 'simpld', '( ph -> %s e. dom %s )' % (k, G1))
        b = self.s([r], 'simprd', '( ph -> ( %s ` %s ) = Gamma\' )' % (G1, k))
        self.memo[key] = (a, b)
        return a, b

    def neq(self, i, k):
        """closed -. i = k"""
        f = '-. %s = %s' % (num_text(i), num_text(k))
        if f in self.memo: return self.memo[f]
        w = self.w
        lo, hi = min(i, k), max(i, k)
        lt = num.le_nat(w, lo, hi, strict=True)
        r1 = num.re_nat(w, lo); r2 = num.re_nat(w, hi)
        ne = self.c('%s =/= %s' % (num_text(lo), num_text(hi)), 'ltneii', [r1, lt])
        if i == lo:
            st = self.c(f, 'neii', [ne])
        else:
            ne2 = self.c('%s =/= %s' % (num_text(hi), num_text(lo)), 'necomi', [ne])
            st = self.c(f, 'neii', [ne2])
        return st

    # -- addresses
    def addr_root(self):
        return (('W', self.hw, self.r, self.hd))

    def apply(self, a, i):
        """a = (text, wstep, s, lstep); returns (eq ( ph -> ( ( TMLab ` a ) ` i ) = ( TMLab ` a' ) ), a')"""
        key = ('ap', a[0], i)
        if key in self.memo: return self.memo[key]
        text, ws, s, ls = a
        assert s >= 1, (self.name, text, i)
        w = self.w
        N, S = s - 1, s
        j1 = self.s([ws, ls], 'jca', '( ph -> ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 ) )' % (text, text, num_text(S)))
        ad = self.d(num.add_nat(w, N, 1), '( %s + 1 ) = %s' % (num_text(N), num_text(S)))
        j2a = self.s([self.nn0d(N), ad], 'jca', '( ph -> ( %s e. NN0 /\\ ( %s + 1 ) = %s ) )' % (num_text(N), num_text(N), num_text(S)))
        j2b = self.s([self.inA(i), self.sA], 'jca', '( ph -> ( %s e. A /\\ A C_ NN0 ) )' % num_text(i))
        j2 = self.s([j2a, j2b], 'jca', '( ph -> ( ( %s e. NN0 /\\ ( %s + 1 ) = %s ) /\\ ( %s e. A /\\ A C_ NN0 ) ) )' % (num_text(N), num_text(N), num_text(S), num_text(i)))
        j = self.s([j1, j2], 'jca', '( ph -> ( ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 ) /\\ ( ( %s e. NN0 /\\ ( %s + 1 ) = %s ) /\\ ( %s e. A /\\ A C_ NN0 ) ) ) )'
                   % (text, text, num_text(S), num_text(N), num_text(N), num_text(S), num_text(i)))
        t2 = '( %s ++ <" %s "> )' % (text, num_text(i))
        c3 = '( ( ( TMLab ` %s ) ` %s ) = ( TMLab ` %s ) /\\ %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 )' % (text, num_text(i), t2, t2, t2, num_text(N))
        tt = self.s([j, w.inst('t15ap')], 'syl', '( ph -> %s )' % c3)
        e = self.s([tt], 'simp1d', '( ph -> ( ( TMLab ` %s ) ` %s ) = ( TMLab ` %s ) )' % (text, num_text(i), t2))
        ws2 = self.s([tt], 'simp2d', '( ph -> %s e. Word A )' % t2)
        ls2 = self.s([tt], 'simp3d', '( ph -> ( ( # ` %s ) + %s ) <_ ; 3 0 )' % (t2, num_text(N)))
        r = (e, (t2, ws2, N, ls2))
        self.memo[key] = r
        return r

    # -- family values: ('lab', addr) | ('fam', kind, addr, args) | ('pnf', addr, Ntext, Xtext)
    def fv_text(self, fv):
        if fv[0] == 'lab': return '( TMLab ` %s )' % fv[1][0]
        if fv[0] == 'fam': return '( %s %s%s )' % (ftok(fv[1]), fv[2][0], ''.join(' ' + a for a in fv[3]))
        return '( TMpnF %s %s %s )' % (fv[1][0], fv[2], fv[3])

    def P_fv(self):
        return ('lab', self.addr_root())

    def apply_fv(self, fv, i):
        """( ph -> ( VAL ` i ) = VAL' ), fv'"""
        if fv[0] == 'lab':
            e, a2 = self.apply(fv[1], i)
            return e, ('lab', a2)
        raise NotImplementedError(fv[0])

    def eval_chain(self, idx):
        """( ph -> CHAINTEXT = VAL ), fv  for ( ... ( P ` i0 ) ` i1 ... )"""
        key = ('ch', tuple(idx))
        if key in self.memo: return self.memo[key]
        text = 'P'
        fv = self.P_fv()
        eq = None
        for i in idx:
            new = '( %s ` %s )' % (text, num_text(i))
            e1 = self.s([eq if eq else self.hp], 'fveq1d', '( ph -> %s = ( %s ` %s ) )' % (new, self.fv_text(fv), num_text(i)))
            e2, fv2 = self.apply_fv(fv, i)
            eq = self.s([e1, e2], 'eqtrd', '( ph -> %s = %s )' % (new, self.fv_text(fv2)))
            text, fv = new, fv2
        r = (eq, fv)
        self.memo[key] = r
        return r

    def labmem(self, toks):
        """( ph -> TERM e. L ) for a label term (E or a chain in P)"""
        t = ' '.join(toks)
        if t == 'E': return self.he
        key = ('lm', t)
        if key in self.memo: return self.memo[key]
        idx = chains(toks)
        assert len(idx) >= 1 and len(idx[0]) >= 1, t
        eq, fv = self.eval_chain(idx[0])
        assert fv[0] == 'lab', (t, fv)
        a = fv[1]
        j = self.s([a[1], a[3], self.nn0d(a[2])], '3jca', '( ph -> ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 /\\ %s e. NN0 ) )'
                   % (a[0], a[0], num_text(a[2]), num_text(a[2])))
        jj = self.s([self.hl, j], 'jca', '( ph -> ( %s /\\ ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 /\\ %s e. NN0 ) ) )'
                    % (HL, a[0], a[0], num_text(a[2]), num_text(a[2])))
        m = self.s([jj, self.w.inst('t15lab')], 'syl', '( ph -> ( TMLab ` %s ) e. %s )' % (a[0], L_))
        r = self.s([eq, m], 'eqeltrd', '( ph -> %s e. %s )' % (t, L_))
        self.memo[key] = r
        return r

    # -- content
    def content_map(self):
        if not hasattr(self, '_cmap'):
            self._cmap, self._items = content_body(self.name, P)
        return self._cmap, self._items

    def ce(self, i):
        """( ph -> ( CONTENT ` i ) = entry_i )"""
        key = ('ce', i)
        if key in self.memo: return self.memo[key]
        w = self.w
        cmap, items = self.content_map()
        df = self.c('%s = %s' % (self.content, cmap), 'df-' + ntok(self.name).lower())
        dfd = self.d(df, '%s = %s' % (self.content, cmap))
        # the chain under ( ph /\ j = i )
        pj = '( ph /\\ j = %s )' % num_text(i)
        je = self.s([], 'simpr', '( %s -> j = %s )' % (pj, num_text(i)))
        chain = cmap[len('( j e. NN0 |-> '):-2]
        cur = chain
        eqs = []
        n = len(items)
        for k in range(n - 1):
            rest = cur[len('if ( j = %s , %s , ' % (num_text(k), items[k])):-2]
            if k == i:
                st = self.s([je], 'iftrued', '( %s -> %s = %s )' % (pj, cur, items[k]))
                eqs.append((st, items[k])); cur = items[k]; break
            b = self.s([je, w.inst('eqeq1')], 'syl', '( %s -> ( j = %s <-> %s = %s ) )' % (pj, num_text(k), num_text(i), num_text(k)))
            nik = self.s([self.neq(i, k)], 'a1i', '( %s -> -. %s = %s )' % (pj, num_text(i), num_text(k)))
            nk = self.s([nik, b], 'mtbird', '( %s -> -. j = %s )' % (pj, num_text(k)))
            st = self.s([nk], 'iffalsed', '( %s -> %s = %s )' % (pj, cur, rest))
            eqs.append((st, rest)); cur = rest
        assert cur == items[i], (self.name, i)
        if not eqs:
            h2 = self.s([], 'eqidd', '( %s -> %s = %s )' % (pj, cur, cur))
        else:
            h2 = eqs[0][0]
            for st, rhs in eqs[1:]:
                h2 = self.s([h2, st], 'eqtrd', '( %s -> %s = %s )' % (pj, chain, rhs))
        mem = self.nn0d(i)
        ex = self.setex(items[i])
        r = self.s([dfd, h2, mem, ex], 'fvmptd', '( ph -> ( %s ` %s ) = %s )' % (self.content, num_text(i), items[i]))
        self.memo[key] = r
        return r

    def _rhs(self, st):
        for l in self.w.lines:
            if l.startswith(st + ':'):
                f = l.split('|- ', 1)[1]
                return f.split(' = ', 1)[1][:-2] if False else self._split_eq(f)
        raise KeyError(st)

    def _split_eq(self, f):
        # f = ( ante -> A = B ); return B
        toks = f.split()
        # strip outer ( ... )
        inner = toks[1:-1]
        k = inner.index('->')
        rel = inner[k + 1:]
        d = 0
        for m, x in enumerate(rel):
            if x in OPEN: d += 1
            elif x in CLOSE: d -= 1
            elif d == 0 and x == '=':
                return ' '.join(rel[m + 1:])
        raise ValueError(f)

    def setex(self, item):
        """( ph -> item e. _V )"""
        key = ('ex', item)
        if key in self.memo: return self.memo[key]
        w = self.w
        toks = item.split()
        if toks[0] == '<.':
            st = self.c('%s e. _V' % item, 'opex')
        else:
            # content node of a child: ( TMnY args )
            child = [n for n in P if ntok(n) == toks[1]][0]
            vs = [v for v in P[child][0] if v != 'M']
            args = []
            j = 2
            for v in vs:
                a, j = arg_term(toks, j); args.append(' '.join(a))
            m = dict(zip(vs, args))
            if child == 'TMIpnv':
                body = PNV_BODY
            else:
                body = content_body(child, P)[0]
            body2 = ' '.join(subst_toks(body.split(), m))
            df = self.c('%s = %s' % (item, body2), 'df-' + ntok(child).lower())
            n0 = self.c('NN0 e. _V', 'nn0ex')
            mx = self.c('%s e. _V' % body2, 'mptex', [n0])
            st = self.c('%s e. _V' % item, 'eqeltri', [df, mx])
        r = self.d(st, '%s e. _V' % item)
        self.memo[key] = r
        return r

    # -- typing
    def split_pair(self, toks):
        assert toks[0] == '<.' and toks[-1] == '>.', ' '.join(toks)
        inner = toks[1:-1]
        d = 0
        for k, x in enumerate(inner):
            if x in OPEN: d += 1
            elif x in CLOSE: d -= 1
            elif d == 0 and x == ',':
                return inner[:k], inner[k + 1:]
        raise ValueError(' '.join(toks))

    def typ(self, toks):
        """( ph -> STMT e. ( TM2Stmt ` T ) )"""
        t = ' '.join(toks)
        key = ('ty', t)
        if key in self.memo: return self.memo[key]
        w = self.w
        tag, rest = self.split_pair(toks)
        tag = ' '.join(tag)
        f = '( ph -> %s e. %s )' % (t, S_)
        if tag == '6':
            r = self.s([self.tv, w.inst('tm2halt')], 'syl', f)
        elif tag == '5':
            fc = self.goto_fn(rest)
            r = self.s([self.tv, fc, w.inst('tm2goto')], 'syl2anc', f)
        elif tag in ('0', '1', '2'):
            K, r2 = self.split_pair(rest)
            F, Q = self.split_pair(r2)
            K = ' '.join(K)
            kd, kg = self.kdom(K)
            if tag == '0':
                fc = self.push_fn(F, K, kg)
                req_ = '( ( %s ` %s ) ^m ( 2nd ` T ) )' % (G1, K)
                ref = 'tm2push'
            else:
                fc = self.read_fn(F, K, kg)
                req_ = '( ( 2nd ` T ) ^m ( ( 2nd ` T ) X. ( ( %s ` %s ) |_| 1o ) ) )' % (G1, K)
                ref = 'tm2peek' if tag == '1' else 'tm2pop'
            q = self.typ(Q)
            j = self.s([kd, fc], 'jca', '( ph -> ( %s e. dom %s /\\ %s e. %s ) )' % (K, G1, ' '.join(F), req_))
            r = self.s([self.tv, j, q, w.inst(ref)], 'syl3anc', f)
        elif tag == '3':
            F, Q = self.split_pair(rest)
            fc = self.load_fn(F)
            q = self.typ(Q)
            r = self.s([self.tv, fc, q, w.inst('tm2load')], 'syl3anc', f)
        elif tag == '4':
            F, r2 = self.split_pair(rest)
            A, B = self.split_pair(r2)
            fc = self.br_fn(F)
            a = self.typ(A); b = self.typ(B)
            j = self.s([a, b], 'jca', '( ph -> ( %s e. %s /\\ %s e. %s ) )' % (' '.join(A), S_, ' '.join(B), S_))
            r = self.s([self.tv, fc, j, w.inst('tm2br')], 'syl3anc', f)
        else:
            raise NotImplementedError(t)
        self.memo[key] = r
        return r

    def const_fn(self, F, Btext, bex, zstep):
        """F = ( ( 2nd ` T ) X. { Z } ): ( ph -> F e. ( B ^m ( 2nd ` T ) ) )"""
        j = self.s([bex, zstep], 'jca', '( ph -> ( %s e. _V /\\ %s e. %s ) )' % (Btext, self.zof(F), Btext))
        return self.s([j, self.w.inst('t15cst')], 'syl', '( ph -> %s e. ( %s ^m ( 2nd ` T ) ) )' % (' '.join(F), Btext))

    def zof(self, F):
        t = ' '.join(F)
        m = re.match(r'^\( \( 2nd ` T \) X\. \{ (.*) \} \)$', t)
        assert m, t
        return m.group(1)

    def goto_fn(self, F):
        z = self.zof(F)
        lm = self.labmem(z.split())
        lex = self.d(self.c('%s e. _V' % L_, 'fvex'), '%s e. _V' % L_)
        return self.const_fn(F, L_, lex, lm)

    def gam_letter(self, z):
        """( ph -> z e. Gamma' ) for a constant letter"""
        key = ('gl', z)
        if key in self.memo: return self.memo[key]
        w = self.w
        if z in ('0', '2', '3', '4'):
            st = self.c('%s e. Gamma\'' % z, 'gamma' + z)
        else:
            m = re.match(r'^<\. 1 , (1o|\(/\)) >\.$', z)
            assert m, z
            b = self.c('%s e. 2o' % m.group(1), '1oel2o' if m.group(1) == '1o' else '0el2o')
            st = self.c('%s e. Gamma\'' % z, 'ax-mp', [b, w.inst('bitgamma')])
        r = self.d(st, '%s e. Gamma\'' % z)
        self.memo[key] = r
        return r

    def to_gk(self, st, F, K, kg, dom):
        """from ( ph -> F e. ( Gamma' ^m DOM ) ) to ( ph -> F e. ( ( G ` K ) ^m DOM ) )"""
        e = self.s([kg], 'oveq1d', '( ph -> ( ( %s ` %s ) ^m %s ) = ( Gamma\' ^m %s ) )' % (G1, K, dom, dom))
        return self.s([st, e], 'eleqtrrd', '( ph -> %s e. ( ( %s ` %s ) ^m %s ) )' % (' '.join(F), G1, K, dom))

    def push_fn(self, F, K, kg):
        t = ' '.join(F)
        gex = self.d(self.c('Gamma\' e. _V', 'gammaex'), 'Gamma\' e. _V')
        if t.startswith('( ( 2nd ` T ) X. {'):
            st = self.const_fn(F, 'Gamma\'', gex, self.gam_letter(self.zof(F)))
        else:
            st = self.map_fn(F, 'Gamma\'', gex)
        return self.to_gk(st, F, K, kg, '( 2nd ` T )')

    READ = {'TMrdA': 'tmcrdaf', 'TMrdB': 'tmcrdbf', 'TMrdBit': 'tmcrdbitf', 'TMrdEnd': 'tmcrdendf',
            'TMrdBra': 'tmcrdbraf', 'TMrdKet': 'tmcrdketf', 'TMrdBlank': 'tmcrdblkf', 'TMrdEmp': 'tmcrdempf', 'TMrdBraOr': 'tmrdbrorf'}

    def read_fn(self, F, K, kg):
        t = ' '.join(F)
        ty = '( TMSt ^m ( TMSt X. ( Gamma\' |_| 1o ) ) )'
        if t in self.READ:
            st = self.c('%s e. %s' % (t, ty), self.READ[t])
        elif t == '( 1st |` ( TMSt X. ( Gamma\' |_| 1o ) ) )':
            st = self.c('%s e. %s' % (t, ty), 'tmcpidf')
        else:
            raise NotImplementedError('read handler ' + t)
        sd = self.d(st, '%s e. %s' % (t, ty))
        j1 = self.s([self.ts, kg], 'jca', '( ph -> ( ( 2nd ` T ) = TMSt /\\ ( %s ` %s ) = Gamma\' ) )' % (G1, K))
        j = self.s([j1, sd], 'jca', '( ph -> ( ( ( 2nd ` T ) = TMSt /\\ ( %s ` %s ) = Gamma\' ) /\\ %s e. %s ) )' % (G1, K, t, ty))
        return self.s([j, self.w.inst('t15rd')], 'syl', '( ph -> %s e. ( ( 2nd ` T ) ^m ( ( 2nd ` T ) X. ( ( %s ` %s ) |_| 1o ) ) ) )' % (t, G1, K))

    def load_fn(self, F):
        t = ' '.join(F)
        tex = self.d(self.c('TMSt e. _V', 'elexi', [self.c('TMSt e. Fin', 'tmstfi')]), 'TMSt e. _V')
        if t.startswith('( ( 2nd ` T ) X. {'):
            z = self.zof(F)
            zt = self.closed_st(z)
            zd = self.s([self.d(zt, '%s e. TMSt' % z), self.ts], 'eleqtrrd', '( ph -> %s e. ( 2nd ` T ) )' % z)
            sx = self.d(self.c('( 2nd ` T ) e. _V', 'fvex'), '( 2nd ` T ) e. _V')
            return self.const_fn(F, '( 2nd ` T )', sx, zd)
        if t == '( _I |` TMSt )':
            w = self.w
            tx = self.c('TMSt e. _V', 'elexi', [self.c('TMSt e. Fin', 'tmstfi')])
            f1 = self.c('( _I |` TMSt ) : TMSt -1-1-onto-> TMSt', 'f1oi')
            f2 = self.c('( _I |` TMSt ) : TMSt --> TMSt', 'ax-mp', [f1, w.inst('f1of')])
            em = self.c('( ( TMSt e. _V /\\ TMSt e. _V ) -> ( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt ) )', 'elmapg')
            e2 = self.c('( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt )', 'mp2an', [tx, tx, em])
            m = self.c('( _I |` TMSt ) e. ( TMSt ^m TMSt )', 'mpbir', [f2, e2])
            md = self.d(m, '( _I |` TMSt ) e. ( TMSt ^m TMSt )')
            e1 = self.s([self.ts], 'oveq2d', '( ph -> ( TMSt ^m ( 2nd ` T ) ) = ( TMSt ^m TMSt ) )')
            st = self.s([md, e1], 'eleqtrrd', '( ph -> ( _I |` TMSt ) e. ( TMSt ^m ( 2nd ` T ) ) )')
        else:
            st = self.map_fn(F, 'TMSt', tex)
        e = self.s([self.ts], 'oveq1d', '( ph -> ( ( 2nd ` T ) ^m ( 2nd ` T ) ) = ( TMSt ^m ( 2nd ` T ) ) )')
        return self.s([st, e], 'eleqtrrd', '( ph -> %s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % t)

    def closed_st(self, z):
        """closed: z e. TMSt for a constant state tuple"""
        w = self.w
        X = z.split()
        comps = []; cur = X
        for k in range(6):
            a, b = self.split_pair(cur); comps.append(a); cur = b
        comps.append(cur)
        tails = []; cur = X
        for k in range(6):
            tails.append(cur); a, cur = self.split_pair(cur)
        tails.append(cur)
        tys = self.STY
        pr = ['( 3o X. 2o )']
        for ty in reversed(tys[:5]):
            pr.insert(0, '( %s X. %s )' % (ty, pr[0]))
        def ct(t, Y):
            t = ' '.join(t)
            if (t, Y) in self.CONST: return self.c('%s e. %s' % (t, Y), self.CONST[(t, Y)])
            if t == '( inr ` (/) )': return self.c('( inr ` (/) ) e. ( 2o |_| 1o )', 'ax-mp', [self.c('(/) e. 1o', '0lt1o'), w.inst('djurcl')])
            raise NotImplementedError(t)
        st = ct(comps[6], '2o')
        for k in range(5, -1, -1):
            a = ct(comps[k], tys[k])
            st = self.c('%s e. %s' % (' '.join(tails[k]), pr[k]), 'opelxpi', [a, st]) if False else self.c('%s e. %s' % (' '.join(tails[k]), pr[k]), 'mp2an', [a, st, w.inst('opelxpi')])
        dft = self.c('TMSt = %s' % pr[0], 'df-tmst')
        return self.c('%s e. TMSt' % z, 'eleqtrri', [st, dft])

    ACC = {'TMfl': ('df-tmfl', 'tmcflcl'), 'TMda': ('df-tmda', 'tmcdacl'), 'TMdb': ('df-tmdb', 'tmcdbcl'),
           'TMcar': ('df-tmcar', 'tmccarcl')}

    def br_fn(self, F):
        t = ' '.join(F)
        tex = self.d(self.c('2o e. _V', '2oex'), '2o e. _V')
        if t in self.ACC:
            return self.acc_fn(t)
        return self.map_fn(F, '2o', tex)

    def acc_fn(self, t):
        key = ('acc', t)
        if key in self.memo: return self.memo[key]
        w = self.w
        dfl, cl = self.ACC[t]
        body = {'TMfl': '( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` v ) ) ) ) ) )',
                'TMda': '( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` v ) ) ) )',
                'TMdb': '( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` v ) ) ) ) )',
                'TMcar': '( 1st ` v )'}[t]
        mp = '( v e. TMSt |-> %s )' % body
        df = self.c('%s = %s' % (t, mp), dfl)
        fx = self.c('%s e. _V' % body, 'fvex')
        fn = self.c('%s Fn TMSt' % t, 'fnmpti', [fx, df])
        c1 = self.c('( v e. TMSt -> ( %s ` v ) e. 2o )' % t, cl)
        rg = self.c('A. v e. TMSt ( %s ` v ) e. 2o' % t, 'rgen', [c1])
        ff = self.c('( %s : TMSt --> 2o <-> ( %s Fn TMSt /\\ A. v e. TMSt ( %s ` v ) e. 2o ) )' % (t, t, t), 'ffnfv')
        f1 = self.c('%s : TMSt --> 2o' % t, 'mpbir2an', [fn, rg, ff])
        tx = self.c('TMSt e. _V', 'elexi', [self.c('TMSt e. Fin', 'tmstfi')])
        em = self.c('( ( 2o e. _V /\\ TMSt e. _V ) -> ( %s e. ( 2o ^m TMSt ) <-> %s : TMSt --> 2o ) )' % (t, t), 'elmapg')
        e2 = self.c('( %s e. ( 2o ^m TMSt ) <-> %s : TMSt --> 2o )' % (t, t), 'mp2an', [self.c('2o e. _V', '2oex'), tx, em])
        m = self.c('%s e. ( 2o ^m TMSt )' % t, 'mpbir', [f1, e2])
        md = self.d(m, '%s e. ( 2o ^m TMSt )' % t)
        e = self.s([self.ts], 'oveq2d', '( ph -> ( 2o ^m ( 2nd ` T ) ) = ( 2o ^m TMSt ) )')
        r = self.s([md, e], 'eleqtrrd', '( ph -> %s e. ( 2o ^m ( 2nd ` T ) ) )' % t)
        self.memo[key] = r
        return r

    def map_fn(self, F, Y, yex):
        """F = ( u e. TMSt |-> X ): ( ph -> F e. ( Y ^m ( 2nd ` T ) ) )"""
        t = ' '.join(F)
        key = ('map', t, Y)
        if key in self.memo: return self.memo[key]
        assert F[:5] == ['(', 'u', 'e.', 'TMSt', '|->'], t
        X = F[5:-1]
        pu = '( ph /\\ u e. TMSt )'
        um = self.s([], 'simpr', '( %s -> u e. TMSt )' % pu)
        self._pu = (pu, um, {})
        b = self.btyp(X, Y)
        al = self.s([b], 'ralrimiva', '( ph -> A. u e. TMSt %s e. %s )' % (' '.join(X), Y))
        r = self.s([self.ts, yex, al, self.w.inst('tmcmapty')], 'syl3anc', '( ph -> %s e. ( %s ^m ( 2nd ` T ) ) )' % (t, Y))
        self.memo[key] = r
        return r

    FIELD = {'TMcar': ('tmccarcl', '2o'), 'TMra': ('tmcracl', '( 2o |_| 1o )'), 'TMrb': ('tmcrbcl', '( 2o |_| 1o )'),
             'TMda': ('tmcdacl', '2o'), 'TMdb': ('tmcdbcl', '2o'), 'TMcmp': ('tmccmpcl', '3o'), 'TMfl': ('tmcflcl', '2o')}
    STY = ['2o', '( 2o |_| 1o )', '( 2o |_| 1o )', '2o', '2o', '3o', '2o']
    CONST = {('1o', '2o'): '1oel2o', ('(/)', '2o'): '0el2o', ('(/)', '3o'): 'bw0el3o', ('1o', '3o'): 'bw1oel3o',
             ('2o', '3o'): 'bw2oel3o'}

    def btyp(self, X, Y):
        """( pu -> X e. Y )"""
        pu, um, memo = self._pu
        t = ' '.join(X)
        if (t, Y) in memo: return memo[(t, Y)]
        w = self.w
        f = '( %s -> %s e. %s )' % (pu, t, Y)
        if (t, Y) in self.CONST:
            r = self.s([self.c('%s e. %s' % (t, Y), self.CONST[(t, Y)])], 'a1i', f)
        elif X[0] == 'if':
            # if ( ch , A , B )
            inner = X[2:-1]
            d = 0; cut = None
            parts = []; st = 0
            for k, x in enumerate(inner):
                if x in OPEN: d += 1
                elif x in CLOSE: d -= 1
                elif d == 0 and x == ',':
                    parts.append(inner[st:k]); st = k + 1
            parts.append(inner[st:])
            ch, A, B = parts
            a = self.btyp(A, Y); b = self.btyp(B, Y)
            r = self.s([a, b], 'ifcld', f)
        elif t == '( inr ` (/) )' and Y == '( 2o |_| 1o )':
            r = self.s([self.c('( inr ` (/) ) e. ( 2o |_| 1o )', 'ax-mp', [self.c('(/) e. 1o', '0lt1o'), w.inst('djurcl')])], 'a1i', f)
        elif X[0] == '<.' and Y == "Gamma'":
            a, b = self.split_pair(X)
            assert a == ['1'], t
            bb = self.btyp(b, '2o')
            r = self.s([bb, w.inst('bitgamma')], 'syl', f)
        elif X[0] == '(' and X[1] in self.FIELD and X[2] == '`' and X[3] == 'u':
            cl, ty = self.FIELD[X[1]]
            assert ty == Y, (t, Y)
            r = self.s([um, w.inst(cl)], 'syl', f)
        elif X[:3] == ['(', 'bitOf', '`']:
            a = self.btyp(X[3:-1], '( 2o |_| 1o )')
            r = self.s([a, w.inst('bitofcl')], 'syl', f)
        elif X[0] == '(' and X[1] == '(' and X[-2] != '`':
            # ( ( A op B ) ` C )
            j = grab(X, 1)
            inner = X[2:j - 1]
            C = X[j + 1:-1]
            d = 0
            for k, x in enumerate(inner):
                if x in OPEN: d += 1
                elif x in CLOSE: d -= 1
                elif d == 0 and x in ('sumBit', 'majBit', 'borrow', 'cmpStep'):
                    op = x; A = inner[:k]; B = inner[k + 1:]; break
            cl = {'sumBit': 'sumbitcl', 'majBit': 'majcl', 'borrow': 'borrowcl', 'cmpStep': 'cmpstepcl'}[op]
            a = self.btyp(A, '2o'); b = self.btyp(B, '2o'); c = self.btyp(C, '3o' if op == 'cmpStep' else '2o')
            r = self.s([a, b, c, w.inst(cl)], 'syl3anc', f)
        elif X[0] == '<.' and Y == 'TMSt':
            comps = []
            cur = X
            for k in range(6):
                a, b = self.split_pair(cur)
                comps.append(a); cur = b
            comps.append(cur)
            prod = ['( 3o X. 2o )']
            tys = self.STY
            txt = '( 3o X. 2o )'
            pr = [txt]
            for ty in reversed(tys[:5]):
                txt = '( %s X. %s )' % (ty, txt); pr.insert(0, txt)
            # pr[k] is the type of the tail starting at component k
            tails = []
            cur = X
            for k in range(6):
                tails.append(cur); a, cur = self.split_pair(cur)
            tails.append(cur)
            st = self.btyp(comps[6], '2o')
            for k in range(5, -1, -1):
                a = self.btyp(comps[k], tys[k])
                tyk = '( %s X. %s )' % (tys[k], pr[k + 1] if k + 1 < 6 else '2o') if k < 5 else '( 3o X. 2o )'
                st = self.s([a, st], 'opelxpd', '( %s -> %s e. %s )' % (pu, ' '.join(tails[k]), tyk))
            dft = self.c('TMSt = %s' % pr[0], 'df-tmst')
            r = self.s([st, self.s([dft], 'a1i', '( %s -> TMSt = %s )' % (pu, pr[0]))], 'eleqtrrd', f)
        elif X[:3] == ['(', 'inl', '`'] and Y == '( 2o |_| 1o )':
            a = self.btyp(X[3:-1], '2o')
            r = self.s([a, w.inst('djulcl')], 'syl', f)
        else:
            raise NotImplementedError('body %s : %s' % (t, Y))
        memo[(t, Y)] = r
        return r

    # -- the theorem
    def own(self, i, stmt):
        """( ph -> ( M ` ( P ` i ) ) = stmt )"""
        w = self.w
        eq, fv = self.eval_chain([i])
        a = fv[1]
        wk = self.s([self.rv, self.hw, self.inA(i), w.inst('tmwalks1')], 'syl3anc',
                    '( ph -> ( R TMWalk %s ) = ( ( R TMWalk W ) ` %s ) )' % (a[0], num_text(i)))
        w2 = self.s([self.hr], 'fveq1d', '( ph -> ( ( R TMWalk W ) ` %s ) = ( %s ` %s ) )' % (num_text(i), self.content, num_text(i)))
        st = ' '.join(stmt)
        w3 = self.s([wk, w2, self.ce(i)], '3eqtrd', '( ph -> ( R TMWalk %s ) = %s )' % (a[0], st))
        ty = self.typ(stmt)
        j1 = self.s([self.hl, self.hm], 'jca', '( ph -> ( %s /\\ %s ) )' % (HL, HM))
        j2 = self.s([a[1], a[3], self.nn0d(a[2])], '3jca', '( ph -> ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 /\\ %s e. NN0 ) )'
                    % (a[0], a[0], num_text(a[2]), num_text(a[2])))
        j3 = self.s([w3, ty], 'jca', '( ph -> ( ( R TMWalk %s ) = %s /\\ %s e. %s ) )' % (a[0], st, st, S_))
        o = self.s([j1, j2, j3, w.inst('t15own')], 'syl3anc',
                   '( ph -> ( ( M ` ( TMLab ` %s ) ) = %s /\\ ( TMLab ` %s ) e. %s ) )' % (a[0], st, a[0], L_))
        o1 = self.s([o], 'simpld', '( ph -> ( M ` ( TMLab ` %s ) ) = %s )' % (a[0], st))
        e2 = self.s([eq], 'fveq2d', '( ph -> ( M ` ( P ` %s ) ) = ( M ` ( TMLab ` %s ) ) )' % (num_text(i), a[0]))
        return self.s([e2, o1], 'eqtrd', '( ph -> ( M ` ( P ` %s ) ) = %s )' % (num_text(i), st))

    def child(self, j, cname, args):
        """( ph -> TMIY args T M ( P ` j ) Ej )"""
        w = self.w
        reg = json.load(open(REG))
        info = reg[cname]
        clab = info['label']
        eq, fv = self.eval_chain([j])
        a = fv[1] if fv[0] == 'lab' else fv[2]
        hyps = list(self.H)
        hyps.append(a[1])
        rY = info['r']
        if rY == a[2]:
            ls = a[3]
        else:
            w_ = self.w
            j1 = self.s([a[1], a[3]], 'jca', '( ph -> ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 ) )' % (a[0], a[0], num_text(a[2])))
            r1 = self.d(num.re_nat(w_, rY), '%s e. RR' % num_text(rY))
            r2 = self.d(num.re_nat(w_, a[2]), '%s e. RR' % num_text(a[2]))
            lr = self.d(num.le_nat(w_, rY, a[2]), '%s <_ %s' % (num_text(rY), num_text(a[2])))
            j2 = self.s([r1, r2, lr], '3jca', '( ph -> ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) )' % (num_text(rY), num_text(a[2]), num_text(rY), num_text(a[2])))
            jj = self.s([j1, j2], 'jca', '( ph -> ( ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 ) /\\ ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) ) )'
                        % (a[0], a[0], num_text(a[2]), num_text(rY), num_text(a[2]), num_text(rY), num_text(a[2])))
            ls = self.s([jj, w.inst('t15wk')], 'syl', '( ph -> ( ( # ` %s ) + %s ) <_ ; 3 0 )' % (a[0], num_text(rY)))
        hyps.append(ls)
        hyps.append(eq)
        Ej = args['E']
        hyps.append(self.labmem(Ej))
        wk = self.s([self.rv, self.hw, self.inA(j), w.inst('tmwalks1')], 'syl3anc',
                    '( ph -> ( R TMWalk %s ) = ( ( R TMWalk W ) ` %s ) )' % (a[0], num_text(j)))
        w2 = self.s([self.hr], 'fveq1d', '( ph -> ( ( R TMWalk W ) ` %s ) = ( %s ` %s ) )' % (num_text(j), self.content, num_text(j)))
        cc = csyn(cname, P, args)
        hyps.append(self.s([wk, w2, self.ce(j)], '3eqtrd', '( ph -> ( R TMWalk %s ) = %s )' % (a[0], cc)))
        for v in stack_params(cname):
            hyps.append(self.stackd(' '.join(args[v])))
        vs = P[cname][0]
        concl = '%s %s' % (cname, ' '.join(' '.join(args[v]) for v in vs))
        return self.s(hyps, clab, '( ph -> %s )' % concl)

    def leaf(self, lf):
        if lf[0] == 'eq':
            i = label_index(lf[1][3:-1])
            return self.own(i, lf[2]), '( M ` ( P ` %s ) ) = %s' % (num_text(i), ' '.join(lf[2]))
        if lf[0] == 'pred':
            i = label_index(lf[2]['P'])
            vs = P[lf[1]][0]
            return self.child(i, lf[1], lf[2]), '%s %s' % (lf[1], ' '.join(' '.join(lf[2][v]) for v in vs))
        if lf[0] == 'el':
            assert ' '.join(lf[2]) == L_
            return self.labmem(lf[1]), '%s e. %s' % (' '.join(lf[1]), L_)
        raise ValueError(lf)

    def conj(self, tr):
        if tr[0] != 'and':
            return self.leaf(tr)
        parts = [self.conj(k) for k in tr[1]]
        f = '( %s )' % ' /\\ '.join(p[1] for p in parts)
        ref = 'jca' if len(parts) == 2 else '3jca'
        assert len(parts) in (2, 3)
        return self.s([p[0] for p in parts], ref, '( ph -> %s )' % f), f

    def build(self):
        self.context()
        tr = wff_tree(self.body, P)
        st, f = self.conj(tr)
        head = '%s %s' % (self.name, ' '.join(self.vs))
        df = self.c('( %s <-> %s )' % (head, f), self.dflab)
        self.w.qed([st, df], 'sylibr', '( ph -> %s )' % head)
        return self.w

    def register(self):
        reg = json.load(open(REG)) if os.path.exists(REG) else {}
        reg[self.name] = {'label': self.lab, 'r': self.r}
        os.makedirs(os.path.dirname(REG), exist_ok=True)
        json.dump(reg, open(REG, 'w'), indent=1)


def order():
    """kinds bottom-up (children first), uniform kinds only"""
    seen, out = set(), []

    def visit(n):
        if n in seen: return
        seen.add(n)
        for i, e in entries(n, P).items() if n != 'TMIpnv' else []:
            if e[0] == 'fam': visit(e[1])
        out.append(n)
    visit('TMIsrch')
    return out


if __name__ == '__main__' and sys.argv[1:2] != ['custom']:
    args = sys.argv[1:]
    if args == ['order']:
        print(' '.join(order())); sys.exit()
    for n in args:
        k = Kind(n)
        w = k.build()
        if w.run():
            k.register()


# ------------------------------------------------------------ custom kinds (families with pushNum)
EXTRA = {
    'TMIsczz': ['C e. NN0', '( 0 ... ( C + 1 ) ) C_ A'],
    'TMIscyy': ['K e. NN', '( 0 ... ( K + 1 ) ) C_ A'],
    'TMIsc99': ['( 0 ... ; ; 1 0 1 ) C_ A'],
}
EXTRA['TMIscal'] = ['C e. NN0', 'K e. NN', '( 0 ... ( C + 1 ) ) C_ A', '( 0 ... ( K + 1 ) ) C_ A', '( 0 ... ; ; 1 0 1 ) C_ A']
EXTRA['TMIsrch'] = list(EXTRA['TMIscal'])
EXTRA['TMIroot'] = list(EXTRA['TMIscal'])
NOSTACK = {'TMIroot', 'TMIsrch', 'TMIscal', 'TMIsczz', 'TMIscyy'}
_stack_params = stack_params


def stack_params(name):
    return [] if name in NOSTACK else _stack_params(name)


class CustomKind(Kind):
    def fam_term(self):
        return fam_syn(self.name)

    def extra_hyps(self, n):
        self.xh = {}
        for f in EXTRA.get(self.name, []):
            self.xh[f] = self.hyp(n, f); n += 1

    def P_fv(self):
        return ('fam', self.name, self.addr_root(), FAMPAR.get(self.name, []))

    def lookup_ctx(self, f):
        """a step proving ( ph -> f ) among the context"""
        if f in self.xh: return self.xh[f]
        raise KeyError(f)

    def apply_fv(self, fv, i):
        if fv[0] == 'lab':
            return Kind.apply_fv(self, fv, i)
        w = self.w
        if fv[0] == 'fam':
            kname, a, pars = fv[1], fv[2], fv[3]
            m = {'W': a[0]}
            m.update(dict(zip(FAMPAR.get(kname, []), pars)))
            body = ' '.join(subst_toks(fam_body(kname, P).split(), m))
            lhs = self.fv_text(fv)
            df = self.c('%s = %s' % (lhs, body), 'df-' + ftok(kname).lower())
            dfd = self.d(df, '%s = %s' % (lhs, body))
            # cases of the chain
            ent = entries(kname, P)
            cases = []
            for k in sorted(ent):
                e = ent[k]
                if e[0] == 'fam' and (e[1] == 'TMIpnv' or e[1] in CUSTOM):
                    cases.append(k)
            pj = '( ph /\\ i = %s )' % num_text(i)
            je = self.s([], 'simpr', '( %s -> i = %s )' % (pj, num_text(i)))
            chain = body[len('( i e. NN0 |-> '):-2]
            cur = chain
            eqs = []
            for k in cases:
                # cur = if ( i = k , F_k , rest )
                d_ = 0
                toks = cur.split()
                # split if ( i = k , A , B )
                inner = toks[2:-1]
                parts = []; st = 0; dd = 0
                for q, x in enumerate(inner):
                    if x in OPEN: dd += 1
                    elif x in CLOSE: dd -= 1
                    elif dd == 0 and x == ',':
                        parts.append(inner[st:q]); st = q + 1
                parts.append(inner[st:])
                A_, B_ = ' '.join(parts[1]), ' '.join(parts[2])
                if k == i:
                    s_ = self.s([je], 'iftrued', '( %s -> %s = %s )' % (pj, cur, A_))
                    eqs.append((s_, A_)); cur = A_; break
                b = self.s([je, w.inst('eqeq1')], 'syl', '( %s -> ( i = %s <-> %s = %s ) )' % (pj, num_text(k), num_text(i), num_text(k)))
                nik = self.s([self.neq(i, k)], 'a1i', '( %s -> -. %s = %s )' % (pj, num_text(i), num_text(k)))
                nk = self.s([nik, b], 'mtbird', '( %s -> -. i = %s )' % (pj, num_text(k)))
                s_ = self.s([nk], 'iffalsed', '( %s -> %s = %s )' % (pj, cur, B_))
                eqs.append((s_, B_)); cur = B_
            e2, a2 = self.apply(a, i)
            if i not in cases:
                assert cur == '( TMLab ` ( %s ++ <" i "> ) )' % a[0], cur
                eqi = self.s([], 'id', '( i = %s -> i = %s )' % (num_text(i), num_text(i)))
                st_, val = cong(w, cur, {'i': num_text(i)}, 'i = %s' % num_text(i), {'i': eqi})
                s_ = self.s([st_], 'adantl', '( %s -> %s = %s )' % (pj, cur, val))
                eqs.append((s_, val)); cur = val
                nfv = ('lab', a2)
                ex = self.d(self.c('%s e. _V' % val, 'fvex'), '%s e. _V' % val)
            else:
                e_ = ent[i]
                if e_[1] == 'TMIpnv':
                    ex_, _ = path_addr(e_[2]['E'], a[0])
                    nfv = ('pnf', a2, ' '.join(subst_toks(e_[2]['N'], m)), '( TMLab ` %s )' % ex_)
                else:
                    nfv = ('fam', e_[1], a2, [' '.join(subst_toks(e_[2][v], m)) for v in FAMPAR.get(e_[1], [])])
                assert cur == self.fv_text(nfv), (cur, self.fv_text(nfv))
                ex = self.famex(nfv)
            h2 = eqs[0][0]
            for s_, rhs in eqs[1:]:
                h2 = self.s([h2, s_], 'eqtrd', '( %s -> %s = %s )' % (pj, chain, rhs))
            val = self.fv_text(nfv)
            r = self.s([dfd, h2, self.nn0d(i), ex], 'fvmptd', '( ph -> ( %s ` %s ) = %s )' % (lhs, num_text(i), val))
            return r, nfv
        if fv[0] == 'pnf':
            assert i == 0
            a, Nt, Xt = fv[1], fv[2], fv[3]
            m = {'W': a[0], 'N': Nt, 'X': Xt}
            LEN = '( # ` ( encNatGam ` %s ) )' % Nt
            body = ' '.join(subst_toks(PNF_BODY.split(), m))
            lhs = self.fv_text(fv)
            df = self.c('%s = %s' % (lhs, body), 'df-tmpnf')
            dfd = self.d(df, '%s = %s' % (lhs, body))
            pj = '( ph /\\ k = 0 )'
            ke = self.s([], 'simpr', '( %s -> k = 0 )' % pj)
            nn = self.numty(Nt, 'NN0')
            gw = self.s([nn, w.inst('encnatgamcl')], 'syl', "( ph -> ( encNatGam ` %s ) e. Word Gamma' )" % Nt)
            ln = self.s([gw, w.inst('lencl')], 'syl', '( ph -> %s e. NN0 )' % LEN)
            l1 = self.s([ln, w.inst('nn0p1nn')], 'syl', '( ph -> ( %s + 1 ) e. NN )' % LEN)
            l1n = self.s([l1], 'nnne0d', '( ph -> ( %s + 1 ) =/= 0 )' % LEN)
            l1d = self.s([l1n], 'necomd', '( ph -> 0 =/= ( %s + 1 ) )' % LEN)
            l1e = self.s([l1d], 'neneqd', '( ph -> -. 0 = ( %s + 1 ) )' % LEN)
            l1p = self.s([l1e], 'adantr', '( %s -> -. 0 = ( %s + 1 ) )' % (pj, LEN))
            bq = self.s([ke, w.inst('eqeq1')], 'syl', '( %s -> ( k = ( %s + 1 ) <-> 0 = ( %s + 1 ) ) )' % (pj, LEN, LEN))
            nk = self.s([l1p, bq], 'mtbird', '( %s -> -. k = ( %s + 1 ) )' % (pj, LEN))
            cur = body[len('( k e. ( 0 ... ( %s + 1 ) ) |-> ' % LEN):-2]
            B_ = '( TMLab ` ( %s ++ <" k "> ) )' % a[0]
            s1 = self.s([nk], 'iffalsed', '( %s -> %s = %s )' % (pj, cur, B_))
            eqk = self.s([], 'id', '( k = 0 -> k = 0 )')
            st_, val = cong(w, B_, {'k': '0'}, 'k = 0', {'k': eqk})
            s2 = self.s([st_], 'adantl', '( %s -> %s = %s )' % (pj, B_, val))
            h2 = self.s([s1, s2], 'eqtrd', '( %s -> %s = %s )' % (pj, cur, val))
            l1n0 = self.s([l1], 'nnnn0d', '( ph -> ( %s + 1 ) e. NN0 )' % LEN)
            mem = self.s([l1n0, w.inst('0elfz')], 'syl', '( ph -> 0 e. ( 0 ... ( %s + 1 ) ) )' % LEN)
            ex = self.d(self.c('%s e. _V' % val, 'fvex'), '%s e. _V' % val)
            r = self.s([dfd, h2, mem, ex], 'fvmptd', '( ph -> ( %s ` 0 ) = %s )' % (lhs, val))
            e2, a2 = self.apply(a, 0)
            return r, ('lab', a2)
        raise NotImplementedError(fv[0])

    def famex(self, fv):
        """( ph -> VAL e. _V ) for a family class"""
        w = self.w
        val = self.fv_text(fv)
        if fv[0] == 'pnf':
            a, Nt, Xt = fv[1], fv[2], fv[3]
            body = ' '.join(subst_toks(PNF_BODY.split(), {'W': a[0], 'N': Nt, 'X': Xt}))
            df = self.c('%s = %s' % (val, body), 'df-tmpnf')
            dom = '( 0 ... ( ( # ` ( encNatGam ` %s ) ) + 1 ) )' % Nt
            ox = self.c('%s e. _V' % dom, 'ovex')
        else:
            kname, a, pars = fv[1], fv[2], fv[3]
            m = {'W': a[0]}; m.update(dict(zip(FAMPAR.get(kname, []), pars)))
            body = ' '.join(subst_toks(fam_body(kname, P).split(), m))
            df = self.c('%s = %s' % (val, body), 'df-' + ftok(kname).lower())
            ox = self.c('NN0 e. _V', 'nn0ex')
        mx = self.c('%s e. _V' % body, 'mptex', [ox])
        st = self.c('%s e. _V' % val, 'eqeltri', [df, mx])
        return self.d(st, '%s e. _V' % val)

    def numty(self, Nt, ty):
        """( ph -> Nt e. ty ) for a pushNum operand"""
        key = ('nt', Nt, ty)
        if key in self.memo: return self.memo[key]
        w = self.w
        if re.match(r'^[\d; ]+$', Nt):
            v = num.nat_value(Nt) if hasattr(num, 'nat_value') else int(Nt)
            r = self.d(num.nn0(w, v), '%s e. NN0' % Nt)
        elif Nt == 'C':
            r = self.xh['C e. NN0']
        elif Nt == 'K':
            r = self.s([self.xh['K e. NN']], 'nnnn0d', '( ph -> K e. NN0 )')
        elif Nt == '( K - 1 )':
            r = self.s([self.xh['K e. NN'], w.inst('nnm1nn0')], 'syl', '( ph -> ( K - 1 ) e. NN0 )')
        else:
            raise NotImplementedError(Nt)
        self.memo[key] = r
        return r

    def alpha(self, Nt):
        """( ph -> ( 0 ... ( Nt + 1 ) ) C_ A )"""
        w = self.w
        f = '( 0 ... ( %s + 1 ) ) C_ A' % Nt
        if f in self.xh: return self.xh[f]
        if re.match(r'^[\d; ]+$', Nt):
            v = num.nat_value(Nt)
            if v + 1 <= 30:
                B, bs = '; 3 0', self.s([self.H[1]], 'simpld', '( ph -> ( 0 ... ; 3 0 ) C_ A )')
            else:
                B, bs = '; ; 1 0 1', self.xh['( 0 ... ; ; 1 0 1 ) C_ A']
            n1 = num.add_nat(w, v, 1)
            eu0 = self.c('( ( %s e. ZZ /\\ %s e. ZZ ) -> ( %s e. ( ZZ>= ` %s ) <-> %s <_ %s ) )' % (num_text(v + 1), B, B, num_text(v + 1), num_text(v + 1), B), 'eluz')
            z1 = self.c('%s e. ZZ' % num_text(v + 1), 'nn0zi', [num.nn0(w, v + 1)])
            z2 = self.c('%s e. ZZ' % B, 'nn0zi', [num.nn0(w, num.nat_value(B))])
            le = num.le_nat(w, v + 1, num.nat_value(B))
            eu = self.c('%s e. ( ZZ>= ` %s )' % (B, num_text(v + 1)), 'mpbir', [le, self.c('( %s e. ( ZZ>= ` %s ) <-> %s <_ %s )' % (B, num_text(v + 1), num_text(v + 1), B), 'mp2an', [z1, z2, eu0])])
            fs = self.c('( 0 ... %s ) C_ ( 0 ... %s )' % (num_text(v + 1), B), 'ax-mp', [eu, w.inst('fzss2')])
            eqn = self.c('( 0 ... ( %s + 1 ) ) = ( 0 ... %s )' % (Nt, num_text(v + 1)), 'oveq2i', [n1])
            fs2 = self.c('( 0 ... ( %s + 1 ) ) C_ ( 0 ... %s )' % (Nt, B), 'eqsstri', [eqn, fs])
            return self.s([self.d(fs2, '( 0 ... ( %s + 1 ) ) C_ ( 0 ... %s )' % (Nt, B)), bs], 'sstrd', '( ph -> %s )' % f)
        if Nt == '( K - 1 )':
            kn = self.xh['K e. NN']
            kc = self.s([kn], 'nncnd', '( ph -> K e. CC )')
            np_ = self.s([kc, w.inst('npcan1')], 'syl', '( ph -> ( ( K - 1 ) + 1 ) = K )')
            kz = self.s([kn], 'nnzd', '( ph -> K e. ZZ )')
            kr = self.s([kn], 'nnred', '( ph -> K e. RR )')
            k1z = self.s([kz], 'peano2zd', '( ph -> ( K + 1 ) e. ZZ )')
            lk = self.s([kr], 'lep1d', '( ph -> K <_ ( K + 1 ) )')
            ez = self.s([kz, k1z, w.inst('eluz')], 'syl2anc', '( ph -> ( ( K + 1 ) e. ( ZZ>= ` K ) <-> K <_ ( K + 1 ) ) )')
            eu = self.s([lk, ez], 'mpbird', '( ph -> ( K + 1 ) e. ( ZZ>= ` K ) )')
            fs = self.s([eu, w.inst('fzss2')], 'syl', '( ph -> ( 0 ... K ) C_ ( 0 ... ( K + 1 ) ) )')
            e2 = self.s([np_], 'oveq2d', '( ph -> ( 0 ... ( ( K - 1 ) + 1 ) ) = ( 0 ... K ) )')
            fs2 = self.s([e2, fs], 'eqsstrd', '( ph -> ( 0 ... ( ( K - 1 ) + 1 ) ) C_ ( 0 ... ( K + 1 ) ) )')
            return self.s([fs2, self.xh['( 0 ... ( K + 1 ) ) C_ A']], 'sstrd', '( ph -> %s )' % f)
        raise NotImplementedError(Nt)

    def child(self, j, cname, args):
        if cname not in CUSTOM and cname != 'TMIpnv':
            return Kind.child(self, j, cname, args)
        w = self.w
        reg = json.load(open(REG))
        info = reg[cname]
        eq, fv = self.eval_chain([j])
        a = fv[1] if fv[0] in ('lab', 'pnf') else fv[2]
        hyps = list(self.H)
        hyps.append(a[1])
        rY = info['r']
        assert rY <= a[2]
        if rY == a[2]:
            ls = a[3]
        else:
            j1 = self.s([a[1], a[3]], 'jca', '( ph -> ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 ) )' % (a[0], a[0], num_text(a[2])))
            r1 = self.d(num.re_nat(w, rY), '%s e. RR' % num_text(rY))
            r2 = self.d(num.re_nat(w, a[2]), '%s e. RR' % num_text(a[2]))
            lr = self.d(num.le_nat(w, rY, a[2]), '%s <_ %s' % (num_text(rY), num_text(a[2])))
            j2 = self.s([r1, r2, lr], '3jca', '( ph -> ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) )' % (num_text(rY), num_text(a[2]), num_text(rY), num_text(a[2])))
            jj = self.s([j1, j2], 'jca', '( ph -> ( ( %s e. Word A /\\ ( ( # ` %s ) + %s ) <_ ; 3 0 ) /\\ ( %s e. RR /\\ %s e. RR /\\ %s <_ %s ) ) )'
                        % (a[0], a[0], num_text(a[2]), num_text(rY), num_text(a[2]), num_text(rY), num_text(a[2])))
            ls = self.s([jj, w.inst('t15wk')], 'syl', '( ph -> ( ( # ` %s ) + %s ) <_ ; 3 0 )' % (a[0], num_text(rY)))
        hyps.append(ls)
        hyps.append(eq)
        Ej = args['E']
        hyps.append(self.labmem(Ej))
        wk = self.s([self.rv, self.hw, self.inA(j), w.inst('tmwalks1')], 'syl3anc',
                    '( ph -> ( R TMWalk %s ) = ( ( R TMWalk W ) ` %s ) )' % (a[0], num_text(j)))
        w2 = self.s([self.hr], 'fveq1d', '( ph -> ( ( R TMWalk W ) ` %s ) = ( %s ` %s ) )' % (num_text(j), self.content, num_text(j)))
        cc = csyn(cname, P, args)
        hyps.append(self.s([wk, w2, self.ce(j)], '3eqtrd', '( ph -> ( R TMWalk %s ) = %s )' % (a[0], cc)))
        if cname == 'TMIpnv':
            hyps.append(self.stackd(' '.join(args['K'])))
            # E = X
            ex_eq, exfv = self.eval_chain(chains(Ej)[0])
            assert self.fv_text(exfv) == fv[3], (self.fv_text(exfv), fv[3])
            hyps.append(ex_eq)
            Nt = ' '.join(args['N'])
            hyps.append(self.numty(Nt, 'NN0'))
            hyps.append(self.alpha(Nt))
        else:
            m = {v: ' '.join(args[v]) for v in P[cname][0]}
            for f in EXTRA.get(cname, []):
                f2 = ' '.join(subst_toks(f.split(), m))
                hyps.append(self.xh[f2])
        vs = P[cname][0]
        concl = '%s %s' % (cname, ' '.join(' '.join(args[v]) for v in vs))
        return self.s(hyps, info['label'], '( ph -> %s )' % concl)


def custom_main(names):
    for n in names:
        k = CustomKind(n)
        w = k.build()
        if w.run():
            k.register()


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'custom':
    custom_main(sys.argv[2:])
