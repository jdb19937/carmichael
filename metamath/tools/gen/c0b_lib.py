"""Sortie C0b: shared expressions and step patterns (Cauchy-Goursat for
rectangles).  Built on tools/c0lib.py (sortie C0)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c0lib import *

only = sys.argv[1:]


def run(w, h=False):
    if only and w.label not in only:
        return True
    return runh(w) if h else w.run()


# ---- expressions -----------------------------------------------------------
def RE(X): return '( Re ` %s )' % X
def IM(X): return '( Im ` %s )' % X
def PT(X, Y): return '( %s + ( _i x. %s ) )' % (X, Y)
def RI(X, Y): return '( ( Re ` %s ) [,] ( Re ` %s ) )' % (X, Y)
def II(X, Y): return '( ( Im ` %s ) [,] ( Im ` %s ) )' % (X, Y)
def PAR(M, N, S): return '( %s + ( %s x. ( %s - %s ) ) )' % (M, S, N, M)

AB = '( A e. CC /\\ B e. CC )'
GEO = '( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) )'
FCN = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D )'
PS = '( %s /\\ %s /\\ %s )' % (AB, GEO, FCN)


def PHSEG(P, Q):
    """the PH of C0's segment lemmas, for the segment from P to Q"""
    return '( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (P, Q, P, Q)


def phseg(w, ante, P, Q, ab, pr, qr, fcn, rss, Fn='F'):
    """( ante -> PHSEG(P,Q) ) from steps ab: ( A e. CC /\\ B e. CC ),
    pr: P e. ( A crect B ), qr: Q e. ( A crect B ), fcn: F e. ( D -cn-> CC ),
    rss: ( A crect B ) C_ D"""
    pq = w.s([pr, qr], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (ante, P, Q))
    cv = w.s([ab, pq, w.inst('crectcvx')], 'syl2anc', '( %s -> ( %s cseg %s ) C_ ( A crect B ) )' % (ante, P, Q))
    sd = w.s([cv, rss], 'sstrd', '( %s -> ( %s cseg %s ) C_ D )' % (ante, P, Q))
    ss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % ante)
    pc = w.s([ss, pr], 'sseldd', '( %s -> %s e. CC )' % (ante, P))
    qc = w.s([ss, qr], 'sseldd', '( %s -> %s e. CC )' % (ante, Q))
    l = w.s([pc, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ante, P, Q))
    r = w.s([fcn, sd], 'jca', '( %s -> ( %s e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (ante, Fn, P, Q))
    return w.s([l, r], 'jca', '( %s -> %s )' % (ante, PHSEG(P, Q).replace('F e. (', Fn + ' e. (')))


# ---- complex sum normalizer -------------------------------------------------
# cxnf proves ( ante -> TREE = right-nested sum of the atoms in a fixed order ).
# TREE is a nested ('+', L, R) tuple over atom strings; cc maps each atom to a
# worksheet step proving ( ante -> atom e. CC ); key maps each atom to its
# position in the target order.

def rn(atoms):
    """right-nested sum text of a nonempty list of atom texts"""
    t = atoms[-1]
    for a in reversed(atoms[:-1]):
        t = '( %s + %s )' % (a, t)
    return t


def tree_text(tree):
    if isinstance(tree, str):
        return tree
    return '( %s + %s )' % (tree_text(tree[1]), tree_text(tree[2]))


class CxSum:
    def __init__(self, w, ante, cc, key):
        self.w = w; self.ante = ante; self.cc = dict(cc); self.key = key; self.ccmemo = {}

    def _cc(self, atoms):
        """step for ( ante -> rn(atoms) e. CC )"""
        t = rn(atoms)
        if t in self.ccmemo:
            return self.ccmemo[t]
        if len(atoms) == 1:
            st = self.cc[atoms[0]]
        else:
            st = self.w.s([self.cc[atoms[0]], self._cc(atoms[1:])], 'addcld',
                          '( %s -> %s e. CC )' % (self.ante, t))
        self.ccmemo[t] = st
        return st

    def _eq(self, a, b):
        return '( %s -> %s = %s )' % (self.ante, a, b)

    def insert(self, x, lst):
        """( x + rn(lst) ) = rn(sorted insert); returns (step, newlist)"""
        w = self.w
        if self.key[x] <= self.key[lst[0]]:
            new = [x] + lst
            return w.s([], 'eqidd', self._eq(rn(new), rn(new))), new
        if len(lst) == 1:
            new = [lst[0], x]
            st = w.s([self.cc[x], self.cc[lst[0]]], 'addcomd', self._eq(rn([x] + lst), rn(new)))
            return st, new
        s1, rest = lst[0], lst[1:]
        a12 = w.s([self.cc[x], self.cc[s1], self._cc(rest)], 'add12d',
                  self._eq('( %s + %s )' % (x, rn(lst)), '( %s + %s )' % (s1, rn([x] + rest))))
        sub, new2 = self.insert(x, rest)
        lift = w.s([sub], 'oveq2d', self._eq('( %s + %s )' % (s1, rn([x] + rest)), '( %s + %s )' % (s1, rn(new2))))
        st = w.s([a12, lift], 'eqtrd', self._eq('( %s + %s )' % (x, rn(lst)), rn([s1] + new2)))
        return st, [s1] + new2

    def merge(self, al, ar):
        """( rn(al) + rn(ar) ) = rn(merged); returns (step, list)"""
        w = self.w
        if len(al) == 1:
            return self.insert(al[0], ar)
        x, rest = al[0], al[1:]
        asc = w.s([self.cc[x], self._cc(rest), self._cc(ar)], 'addassd',
                  self._eq('( %s + %s )' % (rn(al), rn(ar)), '( %s + ( %s + %s ) )' % (x, rn(rest), rn(ar))))
        sub, am2 = self.merge(rest, ar)
        lift = w.s([sub], 'oveq2d',
                   self._eq('( %s + ( %s + %s ) )' % (x, rn(rest), rn(ar)), '( %s + %s )' % (x, rn(am2))))
        ins, am = self.insert(x, am2)
        st = w.s([w.s([asc, lift], 'eqtrd', self._eq('( %s + %s )' % (rn(al), rn(ar)), '( %s + %s )' % (x, rn(am2)))), ins],
                 'eqtrd', self._eq('( %s + %s )' % (rn(al), rn(ar)), rn(am)))
        return st, am

    def nf(self, tree):
        """( tree = rn(sorted atoms) ); returns (step, list)"""
        w = self.w
        if isinstance(tree, str):
            return w.s([], 'eqidd', self._eq(tree, tree)), [tree]
        sl, al = self.nf(tree[1]); sr, ar = self.nf(tree[2])
        t = tree_text(tree)
        s1 = w.s([sl, sr], 'oveq12d', self._eq(t, '( %s + %s )' % (rn(al), rn(ar))))
        s2, am = self.merge(al, ar)
        return w.s([s1, s2], 'eqtrd', self._eq(t, rn(am))), am


def PSOF(P, Q):
    """the standing rectangle antecedent PS for the rectangle < P , Q >"""
    return '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ D ) )' % (P, Q, P, Q, P, Q, P, Q)


def psub(w, A0, d, P, Q, pc, qc, sRP, sIP, sRQ, sIQ, leR, leI, loR, hiR, loI, hiI):
    """( A0 -> PSOF(P,Q) ) for a sub-rectangle of < A , B >.
    sRP/sIP/sRQ/sIQ prove ( Re ` P ) = rp etc.; leR/leI the two corner
    inequalities between the coordinate VALUES; loR/hiR/loI/hiI that those
    values lie between A's and B's."""
    g1 = w.s([leR, sRP, sRQ], '3brtr4d', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, P, Q))
    g2 = w.s([leI, sIP, sIQ], '3brtr4d', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, P, Q))
    c1 = w.s([loR, sRP], 'breqtrrd', '( %s -> ( Re ` A ) <_ ( Re ` %s ) )' % (A0, P))
    c2 = w.s([sRQ, hiR], 'eqbrtrd', '( %s -> ( Re ` %s ) <_ ( Re ` B ) )' % (A0, Q))
    c3 = w.s([loI, sIP], 'breqtrrd', '( %s -> ( Im ` A ) <_ ( Im ` %s ) )' % (A0, P))
    c4 = w.s([sIQ, hiI], 'eqbrtrd', '( %s -> ( Im ` %s ) <_ ( Im ` B ) )' % (A0, Q))
    i1 = w.s([c1, c2], 'jca', '( %s -> ( ( Re ` A ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` B ) ) )' % (A0, P, Q))
    i2 = w.s([c3, c4], 'jca', '( %s -> ( ( Im ` A ) <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ ( Im ` B ) ) )' % (A0, P, Q))
    inc = w.s([i1, i2], 'jca', '( %s -> ( ( ( Re ` A ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` B ) ) /\\ ( ( Im ` A ) <_ ( Im ` %s ) /\\ ( Im ` %s ) <_ ( Im ` B ) ) ) )' % (A0, P, Q, P, Q))
    pq = w.s([pc, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, P, Q))
    ss = w.s([d['ab'], pq, inc, w.inst('crectss2')], 'syl3anc', '( %s -> ( %s crect %s ) C_ ( A crect B ) )' % (A0, P, Q))
    ssd = w.s([ss, d['rss']], 'sstrd', '( %s -> ( %s crect %s ) C_ D )' % (A0, P, Q))
    geo = w.s([g1, g2], 'jca', '( %s -> ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (A0, P, Q, P, Q))
    fc = w.s([d['fcn'], ssd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( %s crect %s ) C_ D ) )' % (A0, P, Q))
    return w.s([pq, geo, fc], '3jca', '( %s -> %s )' % (A0, PSOF(P, Q)))


# ---- rectangle-split helpers (used by c0b_split, c0b_qtr) ----
RA = RE('A'); RB = RE('B'); IA = IM('A'); IB = IM('B')
P10 = PT(RB, IA); P01 = PT(RA, IB)


def RAW(P, Q):
    """rectintval's right-hand side for the rectangle < P , Q >"""
    c1 = PT(RE(Q), IM(P)); c2 = PT(RE(P), IM(Q))
    return '( ( ( F lint <. %s , %s >. ) + ( F lint <. %s , %s >. ) ) + ( ( F lint <. %s , %s >. ) + ( F lint <. %s , %s >. ) ) )' % (P, c1, c1, Q, Q, c2, c2, P)


def ctx(w, A0, ps=None):
    """the standing context of a rectangle lemma; returns a dict of step names.
    ps: a step already proving ( A0 -> PS ); by default simp1 of A0."""
    d = {}
    if ps is None:
        ps = w.s([], 'simp1', '( %s -> %s )' % (A0, PS))
    d['ab'] = ab = w.s([ps, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    d['geo'] = geo = w.s([ps, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, GEO))
    fc = w.s([ps, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, FCN))
    d['fcn'] = w.s([fc, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    d['rss'] = w.s([fc, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ D )' % A0)
    d['ac'] = ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    d['bc'] = bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    d['ar'] = w.s([ac, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RA))
    d['br'] = w.s([bc, w.inst('recl')], 'syl', '( %s -> %s e. RR )' % (A0, RB))
    d['ai'] = w.s([ac, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IA))
    d['bi'] = w.s([bc, w.inst('imcl')], 'syl', '( %s -> %s e. RR )' % (A0, IB))
    d['ler'] = w.s([geo, w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A0, RA, RB))
    d['lei'] = w.s([geo, w.inst('simpr')], 'syl', '( %s -> %s <_ %s )' % (A0, IA, IB))
    d['abg'] = abg = w.s([ab, geo], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, AB, GEO))
    for nm, lab, pt in (('pA', 'crectcnr1', 'A'), ('pP10', 'crectcnr2', P10),
                        ('pB', 'crectcnr3', 'B'), ('pP01', 'crectcnr4', P01)):
        d[nm] = w.s([abg, w.inst(lab)], 'syl', '( %s -> %s e. ( A crect B ) )' % (A0, pt))
    d['fex'] = w.s([d['fcn'], w.inst('elex')], 'syl', '( %s -> F e. _V )' % A0)
    # endpoints of the two coordinate intervals
    for nm, lo, hi, lab, tgt, itv in (('iaI', 'ai', 'bi', 'lbicc2', IA, II('A', 'B')),
                                      ('ibI', 'ai', 'bi', 'ubicc2', IB, II('A', 'B')),
                                      ('raI', 'ar', 'br', 'lbicc2', RA, RI('A', 'B')),
                                      ('rbI', 'ar', 'br', 'ubicc2', RB, RI('A', 'B'))):
        x1 = w.s([d[lo], w.inst('rexr')], 'syl', '( %s -> %s e. RR* )' % (A0, IA if itv == II('A', 'B') else RA))
        x2 = w.s([d[hi], w.inst('rexr')], 'syl', '( %s -> %s e. RR* )' % (A0, IB if itv == II('A', 'B') else RB))
        le = d['lei'] if itv == II('A', 'B') else d['ler']
        d[nm] = w.s([x1, x2, le, w.inst(lab)], 'syl3anc', '( %s -> %s e. %s )' % (A0, tgt, itv))
    return d


def mkpt(w, A0, d, X, Y, xi, yi):
    """( A0 -> ( X + ( _i x. Y ) ) e. ( A crect B ) ) by crectpt"""
    h = w.s([xi, yi], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (A0, X, RI('A', 'B'), Y, II('A', 'B')))
    return w.s([d['ab'], h, w.inst('crectpt')], 'syl2anc', '( %s -> %s e. ( A crect B ) )' % (A0, PT(X, Y)))


def lints(w, A0, d, pts, pairs):
    """PHSEG and lintcl steps for each pair; pts maps a point text to its
    'in the rectangle' step.  Returns {(P,Q): (phstep, ccstep)}"""
    out = {}
    for P, Q in pairs:
        ph = phseg(w, A0, P, Q, d['ab'], pts[P], pts[Q], d['fcn'], d['rss'])
        cc = w.s([ph, w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (A0, LINT('F', P, Q)))
        out[(P, Q)] = (ph, cc)
    return out


def expand(w, A0, d, P, Q, pc, qc, rules):
    """( A0 -> ( F rectint <. P , Q >. ) = clean ) from rectintval plus rewrites"""
    rv = w.s([d['fex'], pc, qc, w.inst('rectintval')], 'syl3anc',
             '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (A0, P, Q, RAW(P, Q)))
    if not rules:
        return rv, RAW(P, Q)
    st, new = w.rewrite(RAW(P, Q), rules, A0)
    return w.s([rv, st], 'eqtrd', '( %s -> ( F rectint <. %s , %s >. ) = %s )' % (A0, P, Q, new)), new


def cancel(w, A0, cs, atoms, f, j, jeq, cc):
    """from rn(atoms) with the last two atoms f, j and a step jeq proving
    ( A0 -> j = -u f ), prove ( A0 -> rn(atoms) = rn(atoms[:-2]) )"""
    fj = '( %s + %s )' % (f, j)
    o1 = w.s([jeq], 'oveq2d', '( %s -> %s = ( %s + -u %s ) )' % (A0, fj, f, f))
    o2 = w.s([cc[f]], 'negidd', '( %s -> ( %s + -u %s ) = 0 )' % (A0, f, f))
    z = w.s([o1, o2], 'eqtrd', '( %s -> %s = 0 )' % (A0, fj))
    # ( last + ( f + j ) ) = last
    rest = atoms[:-2]
    last = rest[-1]
    a1 = w.s([z], 'oveq2d', '( %s -> ( %s + %s ) = ( %s + 0 ) )' % (A0, last, fj, last))
    a2 = w.s([cc[last]], 'addridd', '( %s -> ( %s + 0 ) = %s )' % (A0, last, last))
    st = w.s([a1, a2], 'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A0, last, fj, last))
    cur = '( %s + %s )' % (last, fj); tgt = last
    for a in reversed(rest[:-1]):
        nc = '( %s + %s )' % (a, cur); nt = '( %s + %s )' % (a, tgt)
        st = w.s([st], 'oveq2d', '( %s -> %s = %s )' % (A0, nc, nt))
        cur = nc; tgt = nt
    return st


