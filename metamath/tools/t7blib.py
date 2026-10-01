r"""Sortie T7b: installation predicates for the concrete machine.

A fragment F with stack parameters ks, installed in the machine ( T , M ) at
the label function P with exit E, is the wff

    TMIxxx ks T M P E

defined (df-tmixxx) as the conjunction of F's OWN program equations (labels
( P ` 0 ) , ( P ` 1 ) , ... ; ( P ` 0 ) the entry) and the label typings, and,
for every fragment F calls, the CALLEE's predicate at a label function
( P ` n ) and the callee's exit: never the callee's equations.  This mirrors
Lean's ` Frag.Installed F M iota e ` ( ` ∀ l, M (iota l) = F.code iota e l ` ),
the label function iota being P ; the sub-embedding ` iota ∘ Sum.inl ` of a
sequence is the value ( P ` n ) (a label function in its own right).

Helpers on top of tools/t7lib.py (read-only).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t7lib import *
from t7sub import PROG_SUBX, LABS_SUB, TREE_SUBX, CONCL_SUBX
from t7cmp import PROG_CMP, LABS_CMP, TREE_CMP, CONCL_CMP
from t7inc import PROG_INC, LABS_INC, TREE_INC, CONCL_INC
from t7prd import PROG_PRD, LABS_PRD, TREE_PRD, CONCL_PRD


def PL(P, n):
    """the label ( P ` n ) (decimal numerals from 10 on)"""
    n = int(n)
    t = str(n) if n < 10 else '; %d %d' % (n // 10, n % 10)
    return '( %s ` %s )' % (P, t)


def mk(*parts):
    """a conjunction tree from the non-empty parts (a single part stands alone)"""
    ps = [x for x in parts if x not in (None, ())]
    if len(ps) == 1:
        return ps[0]
    assert 2 <= len(ps) <= 3, ps
    return tuple(ps)


class Frag:
    """a fragment: its own equations (a tree over generic label names), its own
    label typings, and its callees ( name , stack arguments , entry name ,
    exit name ); callee j sits at the label function ( P ` ( nown + j ) ) and
    its entry, the generic name `entry`, is ( ( P ` ( nown + j ) ) ` 0 )"""
    def __init__(self, name, const, stacks, labels, exit, prog, labs, lean, children=()):
        self.name = name; self.const = const; self.stacks = list(stacks)
        self.labels = list(labels); self.exit = exit
        self.prog = prog; self.labs = labs; self.lean = lean
        self.children = list(children)

    def slot(self, j):
        return len(self.labels) + j

    def entry(self, P='P'):
        """the entry label at the label function P: the own label 0, or, for a
        fragment that starts with a call (self.start, a callee's entry name), that
        callee's entry"""
        start = getattr(self, 'start', None)
        if start is None:
            start = self.labels[0] if self.labels else self.children[0][2]
        return self.lmap(P, 'E')[start]

    def entry_child(self):
        """the index of the callee a fragment with own labels starts with, if any"""
        return getattr(self, 'first_child', None)

    def lmap(self, P='P', E='E'):
        m = {l: PL(P, i) for i, l in enumerate(self.labels)}
        for j, (fn, ks, en, ex) in enumerate(self.children):
            m[en] = FRAGS[fn].entry(PL(P, self.slot(j))) if fn in FRAGS else PL(PL(P, self.slot(j)), 0)
        m[self.exit] = E
        return m

    def pred(self, ks=None, T='T', M='M', P='P', E='E'):
        ks = ks or self.stacks
        return ' '.join([self.const] + list(ks) + [T, M, P, E])

    def child_preds(self):
        m = self.lmap()
        out = []
        for j, (fn, ks, en, ex) in enumerate(self.children):
            out.append(FRAGS[fn].pred(ks, 'T', 'M', PL('P', self.slot(j)), m[ex]))
        return out

    def rhs_tree(self):
        """the tree of the df- right side at the formal letters"""
        m = self.lmap()
        cps = self.child_preds()
        prog = tsub(self.prog, m) if self.prog else None
        labs = tsub(self.labs, m) if self.labs else None
        if not self.children:
            return (prog, labs)
        return mk(mk(prog, grp(cps)), labs)

    def rhs(self):
        return cj(self.rhs_tree())

    def df(self):
        return '( %s <-> %s )' % (self.pred(), self.rhs())

    def at(self, ks, P, E, T='T', M='M'):
        """the substitution taking the formal letters to an instance"""
        m = dict(zip(self.stacks, ks)); m.update({'T': T, 'M': M, 'P': P, 'E': E})
        return m


def grp(xs):
    """group a list into a tree of arity 2/3"""
    xs = list(xs)
    if len(xs) <= 3:
        return mk(*xs)
    h = (len(xs) + 1) // 2
    return (grp(xs[:h]), grp(xs[h:]))


FRAGS = {}


def leaf(name, const, stacks, labels, exit, prog, labs, lean):
    FRAGS[name] = Frag(name, const, stacks, labels, exit, prog, labs, lean)
    return FRAGS[name]


DROP_PROG = MEQ('A', STM_DROP)
DROP_LABS = (LAB('A'), LAB('E'))

leaf('dup', 'TMIdup', 'KJI', ['A', "A'", 'A"', "E'", 'E"'], 'E', PROG_DUP, LABS6,
     "` dup x y s = pushSym s comma ; moveNum x s ; pushSym x comma ; pushSym y comma ; move2Num s x y `")
leaf('drop', 'TMIdrop', 'K', ['A'], 'E', DROP_PROG, DROP_LABS,
     "` dropNum x = loop ( fun v => v.ra.isSome ) ( popTop x readA ) ` (one statement)")
leaf('iz', 'TMIiz', 'KI', ['A', "A'", 'A"', "E'", 'E"'], 'E', PROG_IZ, LABS6,
     "` isZero x s = pushSym s comma ; moveNum x s ; pushSym x comma ; load' ( flag := true ) ; zeroScan s x `")
leaf('cmp', 'TMIcmp', 'KJ', ["A'", 'A'], 'E', PROG_CMP(), LABS_CMP,
     "` cmpFrag x y = load' ( cmp := .eq , ra rb := none , da db := false ) ; loop ( !(da && db) ) cmpBody `")
leaf('sub', 'TMIsub', 'KJI', ["A'", 'A', 'A"', "E'", 'E"'], 'E', PROG_SUBX(), LABS_SUB,
     "` sub x y z x ` (the subtractor's init, loop and ` zeroIfBorrow ` , then ` moveNum z x ` )")
leaf('inc', 'TMIinc', 'KJ', ['A', "A'", 'A"'], 'E', PROG_INC, LABS_INC,
     "` incr x s = pushSym s comma ; incLoop x s ; moveNum s x `")
leaf('prd', 'TMIprd', 'KJ', ['A', "A'", 'A"'], 'E', PROG_PRD, LABS_PRD,
     "` predNum x s = pushSym s comma ; predLoop x s ; moveNum s x `")
leaf('can', 'TMIcan', 'KJ', ['A', "A'", 'A"', "E'", 'E"'], 'E', PROG_CAN, LABS6,
     "` canonNum x s = pushSym s comma ; moveNum x s ; stripLoop s ; pushSym x comma ; moveNum s x `")
leaf('add', 'TMIadd', 'KJI', ["A'", 'A', 'E', "E'"], 'E"', PROG_ADDX(), LABS_ADD,
     "` add x y z x ` (the adder's init and loop, then ` moveNum z x ` )")


def unfold_stmt(f):
    """the unfolding theorem: predicate -> own equations and label typings"""
    return '( %s -> %s )' % (f.pred(), f.rhs())


class Bld(Builder):
    """Builder that first looks the whole subtree's text up (extra, then the
    antecedent's Ctx) before rebuilding it from its leaves"""
    def __init__(self, w, ph, ctx, extra=None):
        Builder.__init__(self, w, ph, ctx, extra)
        self.known = dict(ctx.all())
        self.known.update(self.extra)

    def __call__(self, tree):
        key = cj(tree)
        if key in self.known:
            return self.known[key]
        return Builder.__call__(self, tree)


def comp(name, const, stacks, labels, exit, prog, labs, lean, children):
    FRAGS[name] = Frag(name, const, stacks, labels, exit, prog, labs, lean, children)
    return FRAGS[name]


def leaves_of(tree):
    out = {}
    def go(t):
        if isinstance(t, str):
            if t.startswith('( M ` '):
                out[t.split()[3]] = t
            return
        for x in t:
            go(x)
    go(tree)
    return out


# ------------------------------------------------------------ mul, mulC (Canon.lean, MulDiv.lean)
from t7mul import PROG_FML, LABS_FML, TREE_MB, CONCL_MB, CAN_LAB
_ML = leaves_of(PROG_FML)
comp('mul', 'TMImul', ['K', 'J', 'I', "I'", 'I"'], ['P0', 'P1', 'A', 'B0', 'E0', 'B"', 'A0'], "E'",
     ((_ML['P0'], _ML['P1']), (_ML['A'], _ML['B0']), ((_ML['E0'], _ML['B"']), _ML['A0'])),
     ((LAB('P0'), LAB('P1'), LAB('A')), (LAB('B0'), LAB('E0')), (LAB('B"'), LAB('A0'))),
     "` mul x y w s t = pushSym w comma ; popBit y ; loop ( !da ) ( ite ( ra = some true ) ( dup x t s ; add w t s w ) skip ; "
     "pushSym x 0 ; popBit y ) ; dropNum x ` (the one-statement fragments and the control inline)",
     [('dup', ['K', 'I"', "I'"], "B'", 'Q0'), ('add', ['I', 'I"', "I'"], 'Q0', 'B"'), ('drop', ['K'], 'E', "E'")])
comp('mulc', 'TMImulC', ['K', 'J', 'I', "I'", 'I"'], [], 'E', None, None,
     "` mulC x y w s t = mul x y w s t ; canonNum w s `",
     [('mul', ['K', 'J', 'I', "I'", 'I"'], 'P0', "E'"), ('can', ['I', "I'"], "E'", 'E')])


def unfold_all(w, ph, st, fname, ks, P, E, T='T', M='M', out=None, rec=True):
    """from st : ( ph -> PRED instance ), steps for every leaf of the full
    recursive unfolding (own equations and typings of the fragment and of all
    its callees); returns dict leaf text -> step"""
    f = FRAGS[fname]
    out = {} if out is None else out
    m = f.at(ks, P, E, T, M)
    dfi = w.s([], 'df-%s' % f.const.lower(), tsub_text(f.df(), m))
    rt = tsub(f.rhs_tree(), m)
    u = w.s([st, dfi], 'sylib', '( %s -> %s )' % (ph, cj(rt)))
    cu = Ctx(w, ph, rt, root=u)
    out.update(cu.all())
    lm = f.lmap(P, E)
    if not rec:
        return out
    for j, (fn, cks, en, ex) in enumerate(f.children):
        cks2 = [m.get(k, k) for k in cks]
        cp = FRAGS[fn].pred(cks2, T, M, PL(P, f.slot(j)), lm[ex])
        unfold_all(w, ph, out[cp], fn, cks2, PL(P, f.slot(j)), lm[ex], T, M, out)
    return out


# ------------------------------------------------------------ divmod (MulDiv.lean, Canon.lean)
# stacks: K = x , J = y , I = q , I' = j , I" = s , I0 = t
Z0B = '<. 1 , (/) >.'
CNGT_ = CNGT
CNFL = CNOT('fl')
S6 = ['K', 'J', 'I', "I'", 'I"', 'I0']
comp('dmu', 'TMIdmu', ['K', 'J', "I'", 'I"', 'I0'], ['B0'], 'E',
     MEQ('B0', PUSH('J', CONST(Z0B), GT("B'"))), LAB('B0'),
     "` dmUpBody x y j s t = pushSym y ( bit false ) ; incr j s ; dup y t s ; dup x s t ; cmpFrag t s `",
     [('inc', ["I'", 'I"'], "B'", 'U1'), ('dup', ['J', 'I0', 'I"'], 'U1', 'U2'), ('dup', ['K', 'I"', 'I0'], 'U2', 'U3'),
      ('cmp', ['I0', 'I"'], 'U3', 'E')])
comp('dmd', 'TMIdmd', S6, ['A0', 'B"', 'E0', 'E"'], 'E',
     ((MEQ('A0', POP('J', 'TMrdBit', GT('B"'))), MEQ('B"', PUSH('I', CONST(Z0B), GT('D0')))),
      (MEQ('E0', BRANCH(CNGT, GT('B1_'), GT('E"'))), MEQ('E"', LOAD(LID, GT('G0'))))),
     ((LAB('A0'), LAB('B"')), (LAB('E0'), LAB('E"'))),
     "` dmDownBody x y q j s t = predNum j s ; popBit y ; pushSym q ( bit false ) ; dup y t s ; dup x s t ; "
     "cmpFrag t s ; ite ( !decide ( cmp = gt ) ) ( dup y t s ; sub x t s x ; incr q s ) skip ; isZero j s `",
     [('prd', ["I'", 'I"'], 'A"', 'A0'), ('dup', ['J', 'I0', 'I"'], 'D0', 'V1'), ('dup', ['K', 'I"', 'I0'], 'V1', 'V2'),
      ('cmp', ['I0', 'I"'], 'V2', 'E0'), ('dup', ['J', 'I0', 'I"'], 'B1_', 'V3'), ('sub', ['K', 'I0', 'I"'], 'V3', 'V4'),
      ('inc', ['I', 'I"'], 'V4', 'G0'), ('iz', ["I'", 'I"'], 'G0', 'E')])
FRAGS['dmd'].start = 'A"'
comp('dmc', 'TMIdmc', S6, ['P0', 'A', 'E', "A'"], "G'",
     ((MEQ('P0', PUSH("I'", CONST('4'), GT('P1'))), MEQ('A', BRANCH(CNGT, GT('B0'), GT('E')))),
      (MEQ('E', PUSH('I', CONST('4'), GT('E1'))), MEQ("A'", BRANCH(CNFL, GT('A"'), GT("E'"))))),
     ((LAB('P0'), LAB('A')), (LAB('E'), LAB("A'"))),
     "` divmodCore x y q j s t = pushNum j 0 ; dup y t s ; dup x s t ; cmpFrag t s ; loop ( !decide ( cmp = gt ) ) "
     "( dmUpBody x y j s t ) ; pushSym q comma ; isZero j s ; loop ( !flag ) ( dmDownBody x y q j s t ) ; dropNum j `",
     [('dup', ['J', 'I0', 'I"'], 'P1', 'W1'), ('dup', ['K', 'I"', 'I0'], 'W1', 'W2'), ('cmp', ['I0', 'I"'], 'W2', 'A'),
      ('dmu', ['K', 'J', "I'", 'I"', 'I0'], 'B0', 'A'), ('iz', ["I'", 'I"'], 'E1', "A'"),
      ('dmd', S6, 'A"', "A'"), ('drop', ["I'"], "E'", "G'")])
comp('dm', 'TMIdm', S6, [], 'E', None, None, "` divmod x y q j s t = divmodCore x y q j s t ; dropNum y `",
     [('dmc', S6, 'C0', 'C1'), ('drop', ['J'], 'C1', 'E')])
comp('divf', 'TMIdivf', S6, [], 'E', None, None, "` divFrag x y q j s t = divmod x y q j s t ; dropNum x `",
     [('dm', S6, 'C0', 'C1'), ('drop', ['K'], 'C1', 'E')])
comp('modf', 'TMImodf', S6, [], 'E', None, None, "` modFrag x y q j s t = divmod x y q j s t ; dropNum q `",
     [('dm', S6, 'C0', 'C1'), ('drop', ['I'], 'C1', 'E')])
comp('dmcc', 'TMIdivmodC', S6, [], 'E', None, None,
     "` divmodC x y q j s t = divmod x y q j s t ; canonNum x s ; canonNum q s `",
     [('dm', S6, 'C0', 'C1'), ('can', ['K', 'I"'], 'C1', 'C2'), ('can', ['I', 'I"'], 'C2', 'E')])
comp('divc', 'TMIdivC', S6, [], 'E', None, None, "` divC x y q j s t = divFrag x y q j s t ; canonNum q s `",
     [('divf', S6, 'C0', 'C1'), ('can', ['I', 'I"'], 'C1', 'E')])
comp('modc', 'TMImodC', S6, [], 'E', None, None, "` modC x y q j s t = modFrag x y q j s t ; canonNum x s `",
     [('modf', S6, 'C0', 'C1'), ('can', ['K', 'I"'], 'C1', 'E')])


# ------------------------------------------------------------ helpers for the composite triples

def wg4(w, ph, X, xg):
    """( ph -> ( <" 4 "> ++ X ) e. Word Gamma' ) from xg : X e. Word Gamma'"""
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    return w.s([s4, xg, w.inst('ccatcl')], 'syl2anc', "( %s -> ( <\" 4 \"> ++ %s ) e. Word Gamma' )" % (ph, X))


def wgcat(w, ph, A, B, a, b):
    return w.s([a, b, w.inst('ccatcl')], 'syl2anc', "( %s -> ( %s ++ %s ) e. Word Gamma' )" % (ph, A, B))


def wib(w, ph, L, lw):
    """( ph -> ( inclBool o. L ) e. Word Gamma' ) from lw : L e. Word 2o"""
    return w.s([lw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, L))


class Stacks:
    """a stack term D with known values: vals[s] = (text, step ( ph -> ( D ` s ) = text )),
    gam[s] = step ( ph -> text e. Word Gamma' ); memb : ( ph -> D e. Stk ); the machine mk
    (tools/gen/t7_e_cmp.py machine) and ne(a, b) giving ( ph -> a =/= b )"""
    def __init__(self, w, ph, mk, D, memb, ne, vals=None):
        self.w = w; self.ph = ph; self.mk = mk; self.D = D; self.memb = memb; self.ne = ne
        self.vals = dict(vals or {})

    def kd(self, s):
        return self.mk['k'][s]['kd']

    def val(self, s):
        """step ( ph -> ( D ` s ) = text ), text"""
        return self.vals[s]

    def upd(self, s, X, xg):
        """the stack term UPD( D , s , X ) (xg : X e. Word Gamma')"""
        w, ph = self.w, self.ph
        tv = self.mk['tv']
        xk = w.s([xg, self.mk['k'][s]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s)))
        D2 = UP(self.D, s, X)
        m2 = updcl(w, ph, self.D, s, X, tv, self.memb, self.kd(s), xk)
        xv = w.s([xg], 'elexd', '( %s -> %s e. _V )' % (ph, X))
        vals = {}
        for t, (txt, st, g) in self.vals.items():
            if t == s:
                continue
            e = updnv(w, ph, self.D, s, X, t, tv, self.memb, self.kd(s), xv, self.kd(t), self.ne(t, s))
            vals[t] = (txt, w.s([e, st], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, D2, t, txt)), g)
        vals[s] = (X, updkv(w, ph, self.D, s, X, tv, self.memb, self.kd(s), xv), xg)
        return Stacks(w, ph, self.mk, D2, m2, self.ne, vals)


def ne_fn(w, ph, c, pairs):
    """ne(a, b) from the antecedent's leaves ` a =/= b ` in either orientation"""
    memo = {}
    def ne(a, b):
        if (a, b) in memo:
            return memo[(a, b)]
        if '%s =/= %s' % (a, b) in pairs:
            st = c['%s =/= %s' % (a, b)]
        else:
            st = w.s([c['%s =/= %s' % (b, a)]], 'necomd', '( %s -> %s =/= %s )' % (ph, a, b))
        memo[(a, b)] = st
        return st
    return ne


def dist_tree(ks):
    """all pairs of ks in order, grouped"""
    return grp(['%s =/= %s' % (a, b) for i, a in enumerate(ks) for b in ks[i + 1:]])


def idx_tree(ks):
    return grp([IDX(k) for k in ks])


# ------------------------------------------------------------ the families of the division loops
NF = '( # ` ( encodeNat ` F ) )'
NG = '( # ` ( encodeNat ` G ) )'
EG = '( encodeNat ` G )'
YXt = lambda X: '( <" 4 "> ++ %s )' % X
def SHG(e): return '( ( (/) repeatS %s ) ++ ( encodeNat ` G ) )' % e
def YUB(t): return '( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) )' % SHG(t)
def QUB(t): return "( ( encNatGam ` %s ) ++ ( <\" 4 \"> ++ ( D ` I' ) ) )" % t
def NUB(t): return '{ h e. TMSt | ( TMcmp ` h ) = ( ( ( 2 ^ %s ) x. G ) Ncmp F ) }' % t
YUF = '( k e. NN0 |-> %s )' % YUB('k')
QUF = '( k e. NN0 |-> %s )' % QUB('k')
NUF = '( k e. NN0 |-> %s )' % NUB('k')
def DV(t): return '( ( 2 ^ ( R - %s ) ) x. G )' % t
def XDB(t): return '( ( inclBool o. ( ( F mod %s ) bwrd %s ) ) ++ ( <" 4 "> ++ X ) )' % (DV(t), NF)
def YDB(t): return '( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) )' % SHG('( R - %s )' % t)
def HDB(t): return '( ( inclBool o. ( ( |_ ` ( F / %s ) ) bwrd %s ) ) ++ ( <" 4 "> ++ ( D ` I ) ) )' % (DV(t), t)
def QDB(t): return "( ( encNatGam ` ( R - %s ) ) ++ ( <\" 4 \"> ++ ( D ` I' ) ) )" % t
def NDB(t): return '{ h e. TMSt | ( TMfl ` h ) = if ( %s = R , 1o , (/) ) }' % t
def N0B(t): return '{ h e. TMSt | ( TMcmp ` h ) = ( %s Ncmp ( F mod %s ) ) }' % (DV('( %s + 1 )' % t), DV(t))
XDF = '( k e. NN0 |-> %s )' % XDB('k')
YDF = '( k e. NN0 |-> %s )' % YDB('k')
HDF = '( k e. NN0 |-> %s )' % HDB('k')
QDF = '( k e. NN0 |-> %s )' % QDB('k')
NDF = '( k e. NN0 |-> %s )' % NDB('k')
N0F = '( k e. NN0 |-> %s )' % N0B('k')
NSF = '( k e. NN0 |-> TMSt )'
def FAPP(F_, t): return '( %s ` %s )' % (F_, t)
def PDB(t):
    return UP(UP(UP(UP('D', "I'", FAPP(QDF, t)), 'J', FAPP(YDF, t)), 'I', FAPP(HDF, t)), 'K', FAPP(XDF, t))
PDF = '( j e. NN0 |-> %s )' % PDB('j')
# uniform bounds
UPB = '( ( ( 7 x. %s ) + ( 3 x. %s ) ) + ; 1 5 )' % (NF, NG)
T1B = '( ( 2 x. %s ) + 3 )' % NF
TQB = '( ( ( 5 x. %s ) + ( 3 x. %s ) ) + ; 1 2 )' % (NF, NG)
T0B = '( ( 7 x. %s ) + ; 1 3 )' % NF
TPB = '( ( 2 x. %s ) + 5 )' % NF


def chain_text(D, chain):
    t = D
    for k, v in chain:
        t = UP(t, k, v)
    return t


def stk_normalize(w, ph, mk, D, dd, ne, chain, gam, order):
    """( ph -> chain_text( D , chain ) = chain_text( D , out ) ) where out has one update per key
    (the last value), in the key order `order`, an update of k with ( D ` k ) removed (D the base
    stack, dd : D e. Stk); gam : value text -> step ( ph -> v e. Word Gamma' ).  Uses tm2stkupc
    (swaps), tm2stkup2 (merges), tm2stkupid.  Returns (step or None, out)."""
    kk = mk['k']; tv = mk['tv']
    L = list(chain)
    cur_text = chain_text(D, L)
    eqs = []
    memo = {}

    def memb(prefix):
        key = chain_text(D, prefix)
        if key in memo:
            return memo[key]
        if not prefix:
            memo[key] = dd
            return dd
        pm = memb(prefix[:-1])
        k, v = prefix[-1]
        xk = w.s([gam[v], kk[k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, v, GX(k)))
        st = updcl(w, ph, chain_text(D, prefix[:-1]), k, v, tv, pm, kk[k]['kd'], xk)
        memo[key] = st
        return st

    def gk(k, v):
        return w.s([gam[v], kk[k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, v, GX(k)))

    def apply(i, new_pair_list, eq_step):
        """replace the subterm chain_text(D, L[:i+2]) (i.e. positions i, i+1) or L[:i+1]"""
        nonlocal L, cur_text
        old_sub = chain_text(D, L[:i + len(new_pair_list[1])])
        new_L = L[:i] + new_pair_list[0] + L[i + len(new_pair_list[1]):]
        new_sub = chain_text(D, L[:i] + new_pair_list[0])
        if old_sub == cur_text:
            r = eq_step
            n = new_sub
        else:
            r, n = w.rewrite(cur_text, {old_sub: (new_sub, eq_step)}, ph)
        assert n == chain_text(D, new_L), (n, chain_text(D, new_L))
        eqs.append((r, n))
        L = new_L
        cur_text = n

    def swap(i):
        """swap positions i and i+1"""
        (k1, v1), (k2, v2) = L[i], L[i + 1]
        base = chain_text(D, L[:i])
        st = upc(w, ph, base, k1, v1, k2, v2, tv, memb(L[:i]), ne(k1, k2), kk[k1]['kd'], gk(k1, v1), kk[k2]['kd'], gk(k2, v2))
        apply(i, ([(k2, v2), (k1, v1)], [L[i], L[i + 1]]), st)

    def merge(i):
        (k1, v1), (k2, v2) = L[i], L[i + 1]
        assert k1 == k2
        base = chain_text(D, L[:i])
        st = up2(w, ph, base, k1, v1, v2, tv, memb(L[:i]), kk[k1]['kd'], gk(k1, v1), gk(k2, v2))
        apply(i, ([(k2, v2)], [L[i], L[i + 1]]), st)

    # dedupe
    while True:
        seen = {}
        dup = None
        for j, (k, v) in enumerate(L):
            if k in seen:
                dup = (seen[k], j); break
            seen[k] = j
        if dup is None:
            break
        i, j = dup
        for p in range(j - 1, i, -1):
            swap(p)
        merge(i)
    # identity updates
    for idx_ in range(len(L)):
        pass
    while True:
        found = None
        for j, (k, v) in enumerate(L):
            if v == '( %s ` %s )' % (D, k):
                found = j; break
        if found is None:
            break
        for p in range(found - 1, -1, -1):
            swap(p)
        k, v = L[0]
        st = upid(w, ph, D, k, tv, dd, kk[k]['kd'])
        apply(0, ([], [L[0]]), st)
    # sort
    pos = {k: n for n, k in enumerate(order)}
    changed = True
    while changed:
        changed = False
        for p in range(len(L) - 1):
            if pos[L[p][0]] > pos[L[p + 1][0]]:
                swap(p); changed = True
    if not eqs:
        return None, L
    st = eqs[0][0]
    for r, n in eqs[1:]:
        st = w.s([st, r], 'eqtrd', '( %s -> %s = %s )' % (ph, chain_text(D, chain), n))
    return st, L


# ------------------------------------------------------------ PrimTD: primeGoBody, primeGoF, isPrimeTDF
# stacks: K = xm , J = xd , I = xf , I' = s , I" = t , I0 = u
CLT = '( u e. TMSt |-> if ( ( TMcmp ` u ) = (/) , 1o , (/) ) )'       # decide ( cmp = .lt )
NOTFL = 'if ( ( TMfl ` u ) = 1o , (/) , 1o )'                           # !flag
L_TT = LSET(car='(/)', fl='1o')           # carry := false , flag := true
L_FF = LSET(car='(/)', fl='(/)')          # carry := false , flag := false
L_NF = LSET(car=NOTFL, fl='1o')           # carry := !flag , flag := true
L_F0 = LSET(fl='(/)')                     # flag := false
BIT1B = '<. 1 , 1o >.'
comp('pgb', 'TMIpgb', S6, ["B'", 'B"', "E'", 'E"', "A'"], 'A',
     ((MEQ("B'", BRANCH(CLT, GT('B"'), GT('E0'))), MEQ('B"', LOAD(L_TT, GT('A')))),
      (MEQ("E'", BRANCH('TMfl', GT('E"'), GT('A0'))), MEQ('E"', LOAD(L_FF, GT('A'))), MEQ("A'", LOAD(L_NF, GT('A'))))),
     ((LAB("B'"), LAB('B"')), (LAB("E'"), LAB('E"'), LAB("A'"))),
     "` primeGoBody xm xd xf s t u = dup xd s t ; dup xd t s ; mulC s t u xf xm ; dup xm s t ; cmpFrag s u ; "
     "ite ( cmp = lt ) ( load' ( carry := false , flag := true ) ) ( dup xm s t ; dup xd t s ; modC s t u xd xf xm ; "
     "isZero s t ; dropNum s ; ite flag ( load' ( carry := false , flag := false ) ) ( incr xd s ; predNum xf s ; "
     "isZero xf s ; load' ( carry := !flag , flag := true ) ) ) `",
     [('dup', ['J', "I'", 'I"'], 'B0', 'X1'), ('dup', ['J', 'I"', "I'"], 'X1', 'X2'),
      ('mulc', ["I'", 'I"', 'I0', 'I', 'K'], 'X2', 'X3'), ('dup', ['K', "I'", 'I"'], 'X3', 'X4'), ('cmp', ["I'", 'I0'], 'X4', "B'"),
      ('dup', ['K', "I'", 'I"'], 'E0', 'Y1'), ('dup', ['J', 'I"', "I'"], 'Y1', 'Y2'),
      ('modc', ["I'", 'I"', 'I0', 'J', 'I', 'K'], 'Y2', 'Y3'), ('iz', ["I'", 'I"'], 'Y3', 'Y4'), ('drop', ["I'"], 'Y4', "E'"),
      ('inc', ['J', "I'"], 'A0', 'Z1'), ('prd', ['I', "I'"], 'Z1', 'Z2'), ('iz', ['I', "I'"], 'Z2', "A'")])
FRAGS['pgb'].start = 'B0'
comp('pg', 'TMIpg', S6, ['P1', 'A'], 'E',
     (MEQ('P1', LOAD(L_NF, GT('A'))), MEQ('A', BRANCH('TMcar', GT('B0'), GT('E')))),
     (LAB('P1'), LAB('A')),
     "` primeGoF xm xd xf s t u = isZero xf s ; load' ( carry := !flag , flag := true ) ; loop carry ( primeGoBody xm xd xf s t u ) `",
     [('iz', ['I', "I'"], 'P0', 'P1'), ('pgb', S6, 'B0', 'A')])
FRAGS['pg'].start = 'P0'
comp('ipt', 'TMIipt', S6, ['P0', 'Q1', 'Q2', "B'", 'B"', 'E0', 'Q3', 'Q4'], 'E',
     ((MEQ('P0', PUSH("I'", CONST('4'), GT('Q1'))), MEQ('Q1', PUSH("I'", CONST(BIT1B), GT('Q2'))), MEQ('Q2', PUSH("I'", CONST(Z0B), GT('W1')))),
      (MEQ("B'", BRANCH(CLT, GT('B"'), GT('E0'))), MEQ('B"', LOAD(L_F0, GT('E')))),
      (MEQ('E0', PUSH('J', CONST('4'), GT('Q3'))), MEQ('Q3', PUSH('J', CONST(BIT1B), GT('Q4'))), MEQ('Q4', PUSH('J', CONST(Z0B), GT('W3'))))),
     ((LAB('P0'), LAB('Q1'), LAB('Q2')), (LAB("B'"), LAB('B"')), (LAB('E0'), LAB('Q3'), LAB('Q4'))),
     "` isPrimeTDF xm xd xf s t u = pushNum s 2 ; dup xm t u ; cmpFrag t s ; ite ( cmp = lt ) ( load' ( flag := false ) ) "
     "( pushNum xd 2 ; dup xm xf s ; primeGoF xm xd xf s t u ; dropNum xd ; dropNum xf ) `",
     [('dup', ['K', 'I"', 'I0'], 'W1', 'W2'), ('cmp', ['I"', "I'"], 'W2', "B'"),
      ('dup', ['K', 'I', "I'"], 'W3', "E'"), ('pg', S6, "E'", 'E"'), ('drop', ['J'], 'E"', 'W4'), ('drop', ['I'], 'W4', 'E')])
