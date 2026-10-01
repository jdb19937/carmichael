"""Sortie T5: the assemblies of Arith, Sub and Prims (composites and loops
over the fragment lemmas of T1-T3).  Helpers on top of tools/t1lib.py:
antecedent decomposition, Hoare-triple plumbing (sequence, weaken, shrink,
rewrite the endpoints), stack-update algebra, statement typings and the
bound arithmetic.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t1lib import *
from t3_lib import hstepc2, hstepE
from t2_c_mov import constfty, updn
from cl import Closure
from lin import linarith

STMT_T = '( TM2Stmt ` T )'
DG = K('T')
SS = S('T')
LL = L('T')
STK_T = STK('T')
CFG_T = CFG('T')


def GX(k):
    """the alphabet of stack k"""
    return '( %s ` %s )' % (G('T'), k)


def CLN(A, N, D):
    """( { ( inl ` A ) } X. ( N X. { D } ) )"""
    return '( { ( inl ` %s ) } X. ( %s X. { %s } ) )' % (A, N, D)


def GT(X):
    return GOTO(CONSTF('T', X))


def UP(D, k, X):
    return UPD('T', D, k, X)


def NVF(F, r, z):
    return '( %s ` <. %s , ( inl ` %s ) >. )' % (F, r, z)


def conj(*parts):
    assert len(parts) in (2, 3)
    return '( ' + ' /\\ '.join(parts) + ' )'


def cj(tree):
    """text of a nested conjunction tree (tuples of arity 2 or 3, strings at
    the leaves)"""
    if isinstance(tree, str):
        return tree
    return conj(*[cj(t) for t in tree])


class Ctx:
    """antecedent decomposition: `Ctx(w, ph, tree)[leaf]` is a step proving
    `( ph -> leaf )`, produced by simp1/simp2/simp3/simpld/simprd down the
    tree; `tree` is the nested tuple whose text is `ph` (or a conjunct of it
    reached by `lift`, see `sub`)."""
    def __init__(self, w, ph, tree, root=None):
        self.w = w; self.ph = ph; self.tree = tree
        self.memo = {}
        self.root = root      # step proving ( ph -> cj(tree) ), None if ph == cj(tree)
        assert root is not None or cj(tree) == ph, (cj(tree), ph)

    def _get(self, tree, step):
        """returns a dict leaf -> step for the subtree, with `step` proving
        ( ph -> cj(tree) ) (None at the root)"""
        w, ph = self.w, self.ph
        if isinstance(tree, str):
            if step is None:
                step = w.s([], 'id', '( %s -> %s )' % (ph, tree))
            self.memo[tree] = step; return
        n = len(tree)
        for i, sub in enumerate(tree):
            f = cj(sub)
            if step is None:
                ref = {2: ('simpl', 'simpr'), 3: ('simp1', 'simp2', 'simp3')}[n][i]
                st = w.s([], ref, '( %s -> %s )' % (ph, f))
            elif n == 2:
                st = w.s([step], ('simpld', 'simprd')[i], '( %s -> %s )' % (ph, f))
            else:
                st = w.s([step, w.inst(('simp1', 'simp2', 'simp3')[i])], 'syl', '( %s -> %s )' % (ph, f))
            self.memo[f] = st
            if not isinstance(sub, str):
                self._get(sub, st)

    def __getitem__(self, leaf):
        if leaf not in self.memo:
            self._get(self.tree, self.root)
        return self.memo[leaf]

    def all(self):
        self._get(self.tree, self.root)
        return dict(self.memo)


def lift(w, st, ph, f, ref='adantr'):
    """( ph -> f ) from st by ref (adantr by default)"""
    return w.s([st], ref, '( %s -> %s )' % (ph, f))


class Lifter:
    """lift steps from an antecedent to a larger one with one lemma"""
    def __init__(self, w, ph, ref='adantr'):
        self.w = w; self.ph = ph; self.ref = ref; self.memo = {}

    def __call__(self, st, f):
        key = (st, f)
        if key not in self.memo:
            self.memo[key] = self.w.s([st], self.ref, '( %s -> %s )' % (self.ph, f))
        return self.memo[key]


# ------------------------------------------------------------ triples

def hrseq(w, ph, phm, t1, t2, C, D, R, n1, n2):
    """( ph -> C ~~> R in ( n1 + n2 ) ) from t1 : C ~~> D in n1, t2 : D ~~> R in n2"""
    return w.s([phm, t1, t2], 'syl3anc', '( %s -> %s )' % (ph, HR(C, 'T', 'M', R, '( %s + %s )' % (n1, n2))))


def hrle(w, ph, phm, tri, C, D, n, m, mcl, le, qed=False):
    """( ph -> C ~~> D in m ) from tri : C ~~> D in n, mcl : m e. NN0, le : n <_ m"""
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, PHM, HR(C, 'T', 'M', D, n)))
    b = w.s([mcl, le], 'jca', '( %s -> ( %s e. NN0 /\\ %s <_ %s ) )' % (ph, m, n, m))
    f = '( %s -> %s )' % (ph, HR(C, 'T', 'M', D, m))
    if qed:
        w.qed([a, b, w.inst('tm2hle')], 'syl2anc', f); return None
    return w.s([a, b, w.inst('tm2hle')], 'syl2anc', f)


def hrssc(w, ph, phm, tri, C, D, n, C2, ss):
    """( ph -> C2 ~~> D in n ) from tri : C ~~> D in n and ss : C2 C_ C"""
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, PHM, HR(C, 'T', 'M', D, n)))
    return w.s([a, ss, w.inst('tm2hssc')], 'syl2anc', '( %s -> %s )' % (ph, HR(C2, 'T', 'M', D, n)))


def hrssd(w, ph, phm, tri, C, D, n, D2, ss, d2cfg):
    """( ph -> C ~~> D2 in n ) from tri : C ~~> D in n, ss : D C_ D2, d2cfg : D2 C_ Cfg"""
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, PHM, HR(C, 'T', 'M', D, n)))
    b = w.s([ss, d2cfg], 'jca', '( %s -> ( %s C_ %s /\\ %s C_ %s ) )' % (ph, D, D2, D2, CFG_T))
    return w.s([a, b, w.inst('tm2hssd')], 'syl2anc', '( %s -> %s )' % (ph, HR(C, 'T', 'M', D2, n)))


def hrrw(w, ph, tri, C1, D1, n1, ceq=None, deq=None, neq=None, qed=False):
    """rewrite the endpoints and the bound of a triple.  ceq proves
    ( ph -> C1 = C2 ) (None: unchanged), deq ( ph -> D1 = D2 ), neq
    ( ph -> n1 = n2 ).  Returns (step, C2, D2, n2)."""
    def rhs(st, default):
        if st is None:
            return default
        f = None
        for l in w.lines:
            if l.startswith(st + ':'):
                f = l.split('|-', 1)[1].strip(); break
        inner = f[len('( %s -> ' % ph):-2]
        node = parse_wff(inner)
        return node.kids[1].text()
    C2 = rhs(ceq, C1); D2 = rhs(deq, D1); n2 = rhs(neq, n1)
    if ceq is None and deq is None and neq is None:
        return tri, C1, D1, n1
    if deq is None:
        deq = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, D1, D1))
    if neq is None:
        neq = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, n1, n1))
    o = w.s([deq, neq], 'opeq12d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, D1, n1, D2, n2))
    if ceq is None:
        b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C1, 'T', 'M', D1, n1), HR(C1, 'T', 'M', D2, n2)))
    else:
        b = w.s([ceq, o], 'breq12d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C1, 'T', 'M', D1, n1), HR(C2, 'T', 'M', D2, n2)))
    f = '( %s -> %s )' % (ph, HR(C2, 'T', 'M', D2, n2))
    if qed:
        w.qed([b, tri], 'mpbid', f); return None, C2, D2, n2
    return w.s([b, tri], 'mpbid', f), C2, D2, n2


def cfgcl(w, ph, A, N, D, tv, acl, nss, dcl):
    """( ph -> C( A , N , D ) C_ ( TM2Cfg ` T ) )"""
    sn = w.s([dcl], 'snssd', '( %s -> { %s } C_ %s )' % (ph, D, STK_T))
    xs = w.s([nss, sn, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ ( %s X. %s ) )' % (ph, N, D, SS, STK_T))
    return w.s([tv, acl, xs, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ph, CLN(A, N, D), CFG_T))


def clnss(w, ph, A, N, N2, D, nss):
    """( ph -> C( A , N , D ) C_ C( A , N2 , D ) ) from nss : N C_ N2"""
    sd = w.s([], 'ssid', '{ %s } C_ { %s }' % (D, D))
    sda = w.s([sd], 'a1i', '( %s -> { %s } C_ { %s } )' % (ph, D, D))
    x1 = w.s([nss, sda, w.inst('xpss12')], 'syl2anc',
             '( %s -> ( %s X. { %s } ) C_ ( %s X. { %s } ) )' % (ph, N, D, N2, D))
    sl = w.s([], 'ssid', '{ ( inl ` %s ) } C_ { ( inl ` %s ) }' % (A, A))
    sla = w.s([sl], 'a1i', '( %s -> { ( inl ` %s ) } C_ { ( inl ` %s ) } )' % (ph, A, A))
    return w.s([sla, x1, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ph, CLN(A, N, D), CLN(A, N2, D)))


# ------------------------------------------------------------ stacks

def upid(w, ph, D, k, tv, dd, kk):
    """( ph -> UPD( D , k , ( D ` k ) ) = D )"""
    return w.s([tv, dd, kk, w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = %s )' % (ph, UP(D, k, '( %s ` %s )' % (D, k)), D))


def updcl(w, ph, D, k, X, tv, dd, kk, xw):
    """( ph -> UPD( D , k , X ) e. Stk ) from xw : X e. Word Gk"""
    j = w.s([kk, xw], 'jca', '( %s -> ( %s e. %s /\\ %s e. Word %s ) )' % (ph, k, DG, X, GX(k)))
    return w.s([tv, dd, j, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, UP(D, k, X), STK_T))


def updkv(w, ph, D, k, X, tv, dd, kk, xv):
    """( ph -> ( UPD( D , k , X ) ` k ) = X ) from xv : X e. _V"""
    return updkval(w, ph, 'T', D, k, X, tv, dd, kk, xv)


def updnv(w, ph, D, k, X, j, tv, dd, kk, xv, jj, ne):
    """( ph -> ( UPD( D , k , X ) ` j ) = ( D ` j ) ) from ne : j =/= k, xv : X e. W (any W)"""
    return updn(w, ph, D, k, X, '_V', j, tv, dd, kk, xv, jj, ne)


def stkfv(w, ph, D, k, tv, dd, kk):
    """( ph -> ( D ` k ) e. Word Gk )"""
    return w.s([tv, dd, kk, w.inst('tm2stkfv')], 'syl3anc', '( %s -> ( %s ` %s ) e. Word %s )' % (ph, D, k, GX(k)))


def elv(w, ph, st, X):
    """( ph -> X e. _V ) from a membership step"""
    return w.s([st], 'elexd', '( %s -> %s e. _V )' % (ph, X))


def wordv(w, ph, st, X, A):
    """( ph -> X e. W ) with W := Word A, as tm2stkupv/tm2stkupn want any class: elexd is enough"""
    return elv(w, ph, st, X)


def upc(w, ph, D, k, Y, j, Z, tv, dd, ne, kk, yw, jj, zw):
    """( ph -> UPD( UPD( D , k , Y ) , j , Z ) = UPD( UPD( D , j , Z ) , k , Y ) ) for k =/= j"""
    a = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T)), ne], 'jca',
             '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ %s =/= %s ) )' % (ph, D, STK_T, k, j))
    b = w.s([kk, yw], 'jca', '( %s -> ( %s e. %s /\\ %s e. Word %s ) )' % (ph, k, DG, Y, GX(k)))
    c = w.s([jj, zw], 'jca', '( %s -> ( %s e. %s /\\ %s e. Word %s ) )' % (ph, j, DG, Z, GX(j)))
    return w.s([a, b, c, w.inst('tm2stkupc')], 'syl3anc', '( %s -> %s = %s )'
               % (ph, UP(UP(D, k, Y), j, Z), UP(UP(D, j, Z), k, Y)))


def up2(w, ph, D, k, Y, Z, tv, dd, kk, yw, zw):
    """( ph -> UPD( UPD( D , k , Y ) , k , Z ) = UPD( D , k , Z ) )"""
    a = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T))
    b = w.s([yw, zw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Y, GX(k), Z, GX(k)))
    return w.s([a, kk, b, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )'
               % (ph, UP(UP(D, k, Y), k, Z), UP(D, k, Z)))


def up3(w, ph, D, k, Y, j, Z, U, tv, dd, ne, kk, yw, uw, jj, zw):
    """( ph -> UPD( UPD( UPD( D , k , Y ) , j , Z ) , k , U ) = UPD( UPD( D , k , U ) , j , Z ) )"""
    a = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T)), ne], 'jca',
             '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ %s =/= %s ) )' % (ph, D, STK_T, k, j))
    b = w.s([kk, w.s([yw, uw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Y, GX(k), U, GX(k)))],
            'jca', '( %s -> ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, k, DG, Y, GX(k), U, GX(k)))
    c = w.s([jj, zw], 'jca', '( %s -> ( %s e. %s /\\ %s e. Word %s ) )' % (ph, j, DG, Z, GX(j)))
    return w.s([a, b, c, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )'
               % (ph, UP(UP(UP(D, k, Y), j, Z), k, U), UP(UP(D, k, U), j, Z)))


def up4(w, ph, D, k, Y, j, Z, U, R, tv, dd, ne, kk, yw, uw, jj, zw, rw):
    """( ph -> UPD4( D ; k Y ; j Z ; k U ; j R ) = UPD( UPD( D , k , U ) , j , R ) )"""
    a = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T)), ne], 'jca',
             '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ %s =/= %s ) )' % (ph, D, STK_T, k, j))
    b = w.s([kk, w.s([yw, uw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Y, GX(k), U, GX(k)))],
            'jca', '( %s -> ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, k, DG, Y, GX(k), U, GX(k)))
    c = w.s([jj, w.s([zw, rw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Z, GX(j), R, GX(j)))],
            'jca', '( %s -> ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, j, DG, Z, GX(j), R, GX(j)))
    return w.s([a, b, c, w.inst('tm2stkup4')], 'syl3anc', '( %s -> %s = %s )'
               % (ph, UP(UP(UP(UP(D, k, Y), j, Z), k, U), j, R), UP(UP(D, k, U), j, R)))


# ------------------------------------------------------------ statement typings

def gotocl(w, ph, tv, X, xcl):
    f = constfty(w, ph, X, LL, xcl)
    return w.s([tv, f, w.inst('tm2goto')], 'syl2anc', '( %s -> %s e. %s )' % (ph, GT(X), STMT_T))


def pushcl(w, ph, tv, k, F, Q, kk, fcl, qcl):
    j = w.s([kk, fcl], 'jca', '( %s -> ( %s e. %s /\\ %s e. ( %s ^m %s ) ) )' % (ph, k, DG, F, GX(k), SS))
    return w.s([tv, j, qcl, w.inst('tm2push')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PUSH(k, F, Q), STMT_T))


def pushccl(w, ph, tv, k, Z, Q, kk, zcl, qcl):
    """push of a constant letter Z"""
    f = constfty(w, ph, Z, GX(k), zcl)
    return pushcl(w, ph, tv, k, CONSTF('T', Z), Q, kk, f, qcl)


def popcl(w, ph, tv, k, F, Q, kk, fcl, qcl):
    j = w.s([kk, fcl], 'jca', '( %s -> ( %s e. %s /\\ %s e. ( %s ^m ( %s X. ( %s |_| 1o ) ) ) ) )'
            % (ph, k, DG, F, SS, SS, GX(k)))
    return w.s([tv, j, qcl, w.inst('tm2pop')], 'syl3anc', '( %s -> %s e. %s )' % (ph, POP(k, F, Q), STMT_T))


def peekcl(w, ph, tv, k, F, Q, kk, fcl, qcl):
    j = w.s([kk, fcl], 'jca', '( %s -> ( %s e. %s /\\ %s e. ( %s ^m ( %s X. ( %s |_| 1o ) ) ) ) )'
            % (ph, k, DG, F, SS, SS, GX(k)))
    return w.s([tv, j, qcl, w.inst('tm2peek')], 'syl3anc', '( %s -> %s e. %s )' % (ph, PEEK(k, F, Q), STMT_T))


def brcl(w, ph, tv, C, R, Q, ccl, rcl, qcl):
    j = w.s([rcl, qcl], 'jca', '( %s -> ( %s e. %s /\\ %s e. %s ) )' % (ph, R, STMT_T, Q, STMT_T))
    return w.s([tv, ccl, j, w.inst('tm2br')], 'syl3anc', '( %s -> %s e. %s )' % (ph, BRANCH(C, R, Q), STMT_T))


def loadcl(w, ph, tv, F, Q, fcl, qcl):
    return w.s([tv, fcl, qcl, w.inst('tm2load')], 'syl3anc', '( %s -> %s e. %s )' % (ph, LOAD(F, Q), STMT_T))


# ------------------------------------------------------------ words

def s1w(w, ph, zcl, Z, A):
    return w.s([zcl], 's1cld', '( %s -> <" %s "> e. Word %s )' % (ph, Z, A))


def ccatw(w, ph, xw, yw, X, Y, A):
    return w.s([xw, yw, w.inst('ccatcl')], 'syl2anc', '( %s -> ( %s ++ %s ) e. Word %s )' % (ph, X, Y, A))


def revw(w, ph, xw, X, A):
    return w.s([xw, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. Word %s )' % (ph, X, A))


def sswordd(w, ph, xw, X, B, A, ss):
    """( ph -> X e. Word A ) from xw : X e. Word B and ss : B C_ A"""
    a = w.s([ss, w.inst('sswrd')], 'syl', '( %s -> Word %s C_ Word %s )' % (ph, B, A))
    return w.s([a, xw], 'sseldd', '( %s -> %s e. Word %s )' % (ph, X, A))


def formula(w, st):
    """the formula a step proves"""
    for l in w.lines:
        if l.startswith(st + ':'):
            return l.split('|-', 1)[1].strip()
    raise KeyError(st)


def concl(w, ph, st):
    """the consequent of a step proving ( ph -> X )"""
    f = formula(w, st)
    pre = '( %s -> ' % ph
    assert f.startswith(pre) and f.endswith(' )'), (f, ph)
    return f[len(pre):-2]


def jtree(w, ph, tree):
    """build ( ph -> cj(tree) ) with jca/3jca from a tree whose leaves are
    step names proving ( ph -> leaf ); returns (step, text)"""
    if isinstance(tree, str):
        return tree, concl(w, ph, tree)
    parts = [jtree(w, ph, t) for t in tree]
    txt = conj(*[p[1] for p in parts])
    st = w.s([p[0] for p in parts], 'jca' if len(parts) == 2 else '3jca', '( %s -> %s )' % (ph, txt))
    return st, txt


def applylem(w, ph, ref, tree, concl_text):
    """( ph -> concl_text ) by syl from the lemma `ref` whose antecedent is
    the conjunction of the tree's leaves"""
    st, txt = jtree(w, ph, tree)
    return w.s([st, w.inst(ref)], 'syl', '( %s -> %s )' % (ph, concl_text))


# ------------------------------------------------------------ arithmetic

def nn0cl(w, ph, E, leaves):
    """( ph -> E e. NN0 ) via tools/cl.py with leaf steps"""
    c = Closure(w, ph, leaves=leaves)
    return c.mem(E, 'NN0')


def bound(w, ph, phm, tri, C, D, n, m, leaves, hyps=(), qed=False):
    """( ph -> C ~~> D in m ) from tri : C ~~> D in n, proving n <_ m by
    linarith over the leaves (atom -> step proving ( ph -> atom e. NN0 ))
    and the equation/inequality steps hyps"""
    c = Closure(w, ph, leaves=leaves)
    mcl = c.mem(m, 'NN0')
    le = linarith(w, ph, list(hyps), '%s <_ %s' % (n, m), closure=c)
    return hrle(w, ph, phm, tri, C, D, n, m, mcl, le, qed=qed)


def clneq(w, ph, A, N, deq, D1, D2):
    """( ph -> C( A , N , D1 ) = C( A , N , D2 ) ) from deq : ( ph -> D1 = D2 )"""
    a = w.s([deq], 'sneqd', '( %s -> { %s } = { %s } )' % (ph, D1, D2))
    b = w.s([a], 'xpeq2d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ph, N, D1, N, D2))
    return w.s([b], 'xpeq2d', '( %s -> %s = %s )' % (ph, CLN(A, N, D1), CLN(A, N, D2)))


def clnneq(w, ph, A, neq, N1, N2, D):
    """( ph -> C( A , N1 , D ) = C( A , N2 , D ) ) from neq : ( ph -> N1 = N2 )"""
    b = w.s([neq], 'xpeq1d', '( %s -> ( %s X. { %s } ) = ( %s X. { %s } ) )' % (ph, N1, D, N2, D))
    return w.s([b], 'xpeq2d', '( %s -> %s = %s )' % (ph, CLN(A, N1, D), CLN(A, N2, D)))


def upeq(w, ph, D, k, xeq, X1, X2):
    """( ph -> UPD( D , k , X1 ) = UPD( D , k , X2 ) ) from xeq : ( ph -> X1 = X2 )"""
    a = w.s([xeq], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, k, X1, k, X2))
    b = w.s([a], 'sneqd', '( %s -> { <. %s , %s >. } = { <. %s , %s >. } )' % (ph, k, X1, k, X2))
    return w.s([b], 'uneq2d', '( %s -> %s = %s )' % (ph, UP(D, k, X1), UP(D, k, X2)))


def upidv(w, ph, D, k, X, xeq, tv, dd, kk):
    """( ph -> UPD( D , k , X ) = D ) from xeq : ( ph -> ( D ` k ) = X )"""
    xc = w.s([xeq], 'eqcomd', '( %s -> %s = ( %s ` %s ) )' % (ph, X, D, k))
    e = upeq(w, ph, D, k, xc, X, '( %s ` %s )' % (D, k))
    u = upid(w, ph, D, k, tv, dd, kk)
    return w.s([e, u], 'eqtrd', '( %s -> %s = %s )' % (ph, UP(D, k, X), D))
