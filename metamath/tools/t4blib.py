"""Sortie T4b helpers: the remainder of the bit layer (T4b-blueprint.md) on
top of the read-only tools/t4lib.py.  Adds the closure rules the group
needs (`( 2 pCnt N ) e. NN0`, `( |_ ` X ) e. ZZ`, a quotient recorded by
`have`) and the small idioms shared by the cons clauses.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4lib import *          # noqa: F401,F403
import t4lib as _t
import congr as _c
import num
from cl import ClosureError, head, headkey, lift, formula_of, strip_ante   # noqa: F401


class Cl(_t.Cl):
    """t4lib's closure plus pCnt and floor."""

    def child(self, k, A):
        c = _t.Cl.child(self, k, A)
        c.__class__ = Cl
        return c

    def _prove(self, E, T):
        w = self.w
        E = ' '.join(E.split())
        h = head(E)
        hk = headkey(h)
        if T == 'NN0' and hk == 'ov:pCnt' and h[1] == '2':
            two = num.closed(w, [], '2prm', '2 e. Prime')
            twod = w.s([two], 'a1i', '( %s -> 2 e. Prime )' % self.ante)
            n = self.prove(h[3], 'NN')
            i = w.inst('pccl')
            return self._stepf([twod, n, i], 'syl2anc', T, E)
        if T == 'ZZ' and hk == 'fv:|_':
            r = self.prove(h[2], 'RR')
            i = w.inst('flcl')
            return self._stepf([r, i], 'syl', T, E)
        return _t.Cl._prove(self, E, T)


def mkcl(w, ante, leaves):
    lv = {}
    for E, v in leaves.items():
        if isinstance(v, str):
            lv[E] = (v, w.s([], 'id', '( %s -> %s )' % (ante, fmt(v, E))))
        else:
            lv[E] = v
    return Cl(w, ante, lv)


def MI(T, K):
    """the length of incBits"""
    return 'if ( ( %s + 1 ) = ( 2 ^ %s ) , ( %s + 1 ) , %s )' % (T, K, K, K)


def MP(T, K):
    """the length of predBits"""
    return 'if ( ( 2 x. %s ) = ( 2 ^ %s ) , ( %s - 1 ) , %s )' % (T, K, K, K)


def CARV(T, K):
    return 'if ( ( %s + 1 ) = ( 2 ^ %s ) , %s , ( 2 pCnt ( %s + 1 ) ) )' % (T, K, K, T)


def BORV(T, K):
    return 'if ( %s = 0 , %s , ( 2 pCnt %s ) )' % (T, K, T)


def REP(S, N):
    return '( %s repeatS %s )' % (S, N)


def SWRD(L, F, T):
    return '( %s substr <. %s , %s >. )' % (L, F, T)


def PFX(L, N):
    return '( %s prefix %s )' % (L, N)


def conslen(w, cl, ante, B, L):
    """( ante -> ( # ` ( <" B "> ++ L ) ) = ( ( # ` L ) + 1 ) )"""
    XA = CONS(B, L)
    lx = w.s([cl.mem('<" %s ">' % B, 'Word 2o'), cl.mem(L, 'Word 2o'), w.inst('ccatlen')], 'syl2anc',
             '( %s -> ( # ` %s ) = ( ( # ` <" %s "> ) + ( # ` %s ) ) )' % (ante, XA, B, L))
    s1 = w.s([w.s([], 's1len', '( # ` <" %s "> ) = 1' % B)], 'a1i', '( %s -> ( # ` <" %s "> ) = 1 )' % (ante, B))
    o = w.s([s1], 'oveq1d', '( %s -> ( ( # ` <" %s "> ) + ( # ` %s ) ) = ( 1 + ( # ` %s ) ) )' % (ante, B, L, L))
    ac = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % ante), cl.mem(LEN(L), 'CC')], 'addcomd',
             '( %s -> ( 1 + ( # ` %s ) ) = ( ( # ` %s ) + 1 ) )' % (ante, L, L))
    return w.s([lx, o, ac], '3eqtrd', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (ante, XA, L))


def two_prime(w, ante):
    c = num.closed(w, [], '2prm', '2 e. Prime')
    return w.s([c], 'a1i', '( %s -> 2 e. Prime )' % ante)


def exp_p1(w, cl, ante, K):
    """( ante -> ( 2 ^ ( K + 1 ) ) = ( ( 2 ^ K ) x. 2 ) )"""
    tc = w.s([], '2cnd', '( %s -> 2 e. CC )' % ante)
    return w.s([tc, cl.mem(K, 'NN0'), w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( ( 2 ^ %s ) x. 2 ) )' % (ante, K, K))


def exp_p1c(w, cl, ante, K):
    """( ante -> ( 2 ^ ( K + 1 ) ) = ( 2 x. ( 2 ^ K ) ) )"""
    e = exp_p1(w, cl, ante, K)
    c = w.s([cl.mem(P2(K), 'CC'), w.s([], '2cnd', '( %s -> 2 e. CC )' % ante)], 'mulcomd', '( %s -> ( ( 2 ^ %s ) x. 2 ) = ( 2 x. ( 2 ^ %s ) ) )' % (ante, K, K))
    return w.s([e, c], 'eqtrd', '( %s -> ( 2 ^ ( %s + 1 ) ) = ( 2 x. ( 2 ^ %s ) ) )' % (ante, K, K))


def ne_from_oddne(w, cl, ante, A, B):
    """( ante -> -. ( ( 2 x. A ) + 1 ) = ( 2 x. B ) ) for A, B e. ZZ"""
    return w.s([cl.mem(A, 'ZZ'), cl.mem(B, 'ZZ'), w.inst('bwoddne')], 'syl2anc', '( %s -> -. ( ( 2 x. %s ) + 1 ) = ( 2 x. %s ) )' % (ante, A, B))


def cases_if(w, ante, cond, body_t, body_f, concl):
    """( ante -> concl ) by the cases cond / -. cond; body_t(a1, h) with
    h : ( a1 -> cond ), body_f(a2, h) with h : ( a2 -> -. cond ); pm2.61dan"""
    a1 = '( %s /\\ %s )' % (ante, cond); h1 = w.s([], 'simpr', '( %s -> %s )' % (a1, cond))
    s1 = body_t(a1, h1)
    a2 = '( %s /\\ -. %s )' % (ante, cond); h2 = w.s([], 'simpr', '( %s -> -. %s )' % (a2, cond))
    s2 = body_f(a2, h2)
    return w.s([s1, s2], 'pm2.61dan', '( %s -> %s )' % (ante, concl))


def subcl(w, cl, ante, child_ante):
    """a child closure under child_ante whose parent is cl"""
    c = Cl(w, child_ante, {}); c.parent = cl
    return c
