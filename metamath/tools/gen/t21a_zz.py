"""Sortie T21a: helpers shared by zones II-IV (density bodies in the letters y p o v u)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_, run
import num, lin
import cl as _cl
import cl
from tm import W


def nco_eq(w, a, t, n='N'):
    """closed step |- NCo(a,t) = NC(a,t) (characters y -> x, zeros p -> q, binder o -> r)"""
    Ey, Ex = '( %s DChrLF y )' % n, '( %s DChrLF x )' % n
    phi = lambda b, e: '( %s =/= 1 /\\ ( %s ` %s ) = 0 )' % (b, e, b)
    idor = w.s([], 'id', '( o = r -> o = r )')
    c1, _ = w.wcongr(phi('o', Ey), {'o': 'r'}, 'o = r', {'o': idor})
    Zo = ZFo(a, t, n); Zr = ZF(Ey, a, t)
    r1 = w.s([c1], 'cbvrabv', '%s = %s' % (Zo, Zr))
    s1 = w.s([r1], 'sumeq1i', 'sum_ p e. %s ( %s holord p ) = sum_ p e. %s ( %s holord p )' % (Zo, Ey, Zr, Ey))
    s2 = w.s([w.s([], 'oveq2', '( p = q -> ( %s holord p ) = ( %s holord q ) )' % (Ey, Ey))], 'cbvsumv', 'sum_ p e. %s ( %s holord p ) = sum_ q e. %s ( %s holord q )' % (Zr, Ey, Zr, Ey))
    IN_y = 'sum_ q e. %s ( %s holord q )' % (Zr, Ey)
    s12 = w.s([s1, s2], 'eqtri', 'sum_ p e. %s ( %s holord p ) = %s' % (Zo, Ey, IN_y))
    DBn = '( Base ` ( DChr ` %s ) )' % n
    o1 = w.s([w.s([s12], 'a1i', '( y e. %s -> sum_ p e. %s ( %s holord p ) = %s )' % (DBn, Zo, Ey, IN_y))], 'sumeq2i', 'sum_ y e. %s sum_ p e. %s ( %s holord p ) = sum_ y e. %s %s' % (DBn, Zo, Ey, DBn, IN_y))
    idyx = w.s([], 'id', '( y = x -> y = x )')
    c2, new = w.congr(IN_y, {'y': 'x'}, 'y = x', {'y': idyx})
    o2 = w.s([c2], 'cbvsumv', 'sum_ y e. %s %s = sum_ x e. %s %s' % (DBn, IN_y, DBn, new))
    return w.s([o1, o2], 'eqtri', '%s = %s' % (NCo(a, t, n), NC(a, t, n)))


def fold_hyp(w, Ck, body, bstep, a, ar, low, lowle, ale1, T, rhs_fold, mono):
    """Under Ck (free of t, v, u): from bstep : ( Ck -> body ) (a density body A. v A. u ...),
    a class `a` with ar : ( Ck -> a e. RR ), lowle : ( Ck -> low <_ a ), ale1 : ( Ck -> a <_ 1 ),
    build ( Ck -> A. t e. RR ( ( 2 <_ t /\\ t <_ T ) -> NC(a,t) <_ rhs_fold(t) ) ).
    mono(Cx, rhs_body_step) turns ( Cx -> NC <_ RHS_body(t,a) ) into ( Cx -> NC <_ rhs_fold(t) ),
    Cx = ( ( Ck /\\ t e. RR ) /\\ ( 2 <_ t /\\ t <_ T ) )."""
    inner = body.split(' ', 8)[8]
    idv = w.s([], 'id', '( v = t -> v = t )')
    c1, b_t = w.wcongr(inner, {'v': 't'}, 'v = t', {'v': idv})
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (a, a))
    c2, b_ta = w.wcongr(b_t, {'u': a}, 'u = %s' % a, {'u': idu})
    rs = w.s([c1, c2], 'rspc2v', '( ( t e. RR /\\ %s e. RR ) -> ( %s -> %s ) )' % (a, body, b_ta))
    Ct = '( %s /\\ t e. RR )' % Ck
    L = lambda s_, A_: _cl.lift(w, s_, A_)
    inst = w.s([w.s([w.s([], 'simpr', '( %s -> t e. RR )' % Ct), L(ar, Ct)], 'jca', '( %s -> ( t e. RR /\\ %s e. RR ) )' % (Ct, a)), L(bstep, Ct), rs], 'sylc', '( %s -> %s )' % (Ct, b_ta))
    Cx = '( %s /\\ ( 2 <_ t /\\ t <_ %s ) )' % (Ct, T)
    pre, post = b_ta[2:-2].split(' -> ', 1)
    t2 = w.s([], 'simprl', '( %s -> 2 <_ t )' % Cx)
    prem = w.s([t2, L(lowle, Cx), L(ale1, Cx)], '3jca', '( %s -> %s )' % (Cx, pre))
    got = w.s([prem, L(inst, Cx)], 'mpd', '( %s -> %s )' % (Cx, post))
    lhs_o, rhs_b = post.split(' <_ ', 1) if False else (NCo(a, 't'), post[len(NCo(a, 't')) + 4:])
    ce = w.s([nco_eq(w, a, 't')], 'a1i', '( %s -> %s = %s )' % (Cx, NCo(a, 't'), NC(a, 't')))
    got2 = w.s([ce, got], 'eqbrtrrd', '( %s -> %s <_ %s )' % (Cx, NC(a, 't'), rhs_b))
    fin = mono(Cx, got2, rhs_b)
    imp = w.s([fin], 'ex', '( %s -> ( ( 2 <_ t /\\ t <_ %s ) -> %s <_ %s ) )' % (Ct, T, NC(a, 't'), rhs_fold('t')))
    return w.s([imp], 'ralrimiva', '( %s -> A. t e. RR ( ( 2 <_ t /\\ t <_ %s ) -> %s <_ %s ) )' % (Ck, T, NC(a, 't'), rhs_fold('t')))


def clos(w, A, leaves):
    c = _cl.Closure(w, A, {})
    for k_, s_ in leaves.items():
        c.leaf(k_, 'RR', s_)
    return c
