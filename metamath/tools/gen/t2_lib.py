"""T2: generator helpers on top of tools/t1lib.py.

`hstepcp` is `t1lib.hstepc` with the state factor of the pre- and
postcondition a class ` NP C_ ( 2nd ` T ) ` instead of ` ( 2nd ` T ) `
itself --- blueprint D3, the shape every state-tracking fragment needs.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *


def hstepcp(w, ante, T, M, A, E, NP, D1, D2, mstep, alcl, elcl, npss, d1cl, d2cl, body,
            v='v', a='a', t='t', qed=False):
    """One machine step of a fragment as a Hoare triple between
    ` ( { ( inl ` A ) } X. ( NP X. { D1 } ) ) ` and
    ` ( { ( inl ` E ) } X. ( NP X. { D2 } ) ) ` --- the internal states
    restricted to ` NP ` , the stacks pinned.

    `npss` proves ` ( ante -> NP C_ ( 2nd ` T ) ) ` ; `body(av)` returns
    (step proving
    ` ( av -> ( ( M ` A ) ( TM2sa ` T ) <. v , D1 >. ) = <. ( inl ` E ) , <. NEWV , D2 >. >. ) `,
    NEWV, step proving ` ( av -> NEWV e. NP ) `), with
    ` av = ( ante /\\ v e. NP ) `.
    """
    ST = '( %s X. %s )' % (S(T), STK(T))
    P1 = '( %s X. { %s } )' % (NP, D1)
    C1 = '( { ( inl ` %s ) } X. %s )' % (A, P1)
    P2 = '( %s X. { %s } )' % (NP, D2)
    C2 = '( { ( inl ` %s ) } X. %s )' % (E, P2)
    av = '( %s /\\ %s e. %s )' % (ante, v, NP)
    SA_ = lambda x: '( ( %s ` %s ) %s %s )' % (M, A, SA(T), x)
    eq, NEWV, nvcl = body(av)
    RES = '<. ( inl ` %s ) , <. %s , %s >. >.' % (E, NEWV, D2)
    inle = w.s([], 'fvex', '( inl ` %s ) e. _V' % E)
    sn1 = w.s([inle, w.inst('snidg')], 'ax-mp', '( inl ` %s ) e. { ( inl ` %s ) }' % (E, E))
    sn1a = w.s([sn1], 'a1i', '( %s -> ( inl ` %s ) e. { ( inl ` %s ) } )' % (av, E, E))
    d2v = w.s([d2cl], 'elexd', '( %s -> %s e. _V )' % (ante, D2))
    d2va = w.s([d2v], 'adantr', '( %s -> %s e. _V )' % (av, D2))
    sn2 = w.s([d2va, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (av, D2, D2))
    pr2 = w.s([nvcl, sn2], 'opelxpd', '( %s -> <. %s , %s >. e. %s )' % (av, NEWV, D2, P2))
    res = w.s([sn1a, pr2], 'opelxpd', '( %s -> %s e. %s )' % (av, RES, C2))
    inc = w.s([eq, res], 'eqeltrd', '( %s -> %s e. %s )' % (av, SA_('<. %s , %s >.' % (v, D1)), C2))
    ral1 = w.s([inc], 'ralrimiva', '( %s -> A. %s e. %s %s e. %s )'
               % (ante, v, NP, SA_('<. %s , %s >.' % (v, D1)), C2))
    d1v = w.s([d1cl], 'elexd', '( %s -> %s e. _V )' % (ante, D1))
    q1 = w.s([], 'opeq2', '( %s = %s -> <. %s , %s >. = <. %s , %s >. )' % (t, D1, v, t, v, D1))
    q2 = w.s([q1], 'oveq2d', '( %s = %s -> %s = %s )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), SA_('<. %s , %s >.' % (v, D1))))
    q3 = w.s([q2], 'eleq1d', '( %s = %s -> ( %s e. %s <-> %s e. %s ) )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), C2, SA_('<. %s , %s >.' % (v, D1)), C2))
    q4 = w.s([q3], 'ralsng', '( %s e. _V -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (D1, t, D1, SA_('<. %s , %s >.' % (v, t)), C2, SA_('<. %s , %s >.' % (v, D1)), C2))
    q5 = w.s([d1v, q4], 'syl', '( %s -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (ante, t, D1, SA_('<. %s , %s >.' % (v, t)), C2, SA_('<. %s , %s >.' % (v, D1)), C2))
    q6 = w.s([q5], 'ralbidv', '( %s -> ( A. %s e. %s A. %s e. { %s } %s e. %s <-> A. %s e. %s %s e. %s ) )'
             % (ante, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), C2, v, NP,
                SA_('<. %s , %s >.' % (v, D1)), C2))
    q7 = w.s([q6, ral1], 'mpbird', '( %s -> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (ante, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), C2))
    p1 = w.s([], 'oveq2', '( %s = <. %s , %s >. -> %s = %s )'
             % (a, v, t, SA_(a), SA_('<. %s , %s >.' % (v, t))))
    p2 = w.s([p1], 'eleq1d', '( %s = <. %s , %s >. -> ( %s e. %s <-> %s e. %s ) )'
             % (a, v, t, SA_(a), C2, SA_('<. %s , %s >.' % (v, t)), C2))
    p3 = w.s([p2], 'ralxp', '( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (a, P1, SA_(a), C2, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), C2))
    p3a = w.s([p3], 'a1i', '( %s -> ( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s ) )'
              % (ante, a, P1, SA_(a), C2, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), C2))
    cond = w.s([p3a, q7], 'mpbird', '( %s -> A. %s e. %s %s e. %s )' % (ante, a, P1, SA_(a), C2))
    sd1 = w.s([d1cl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D1, STK(T)))
    sd2 = w.s([d2cl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D2, STK(T)))
    x1 = w.s([npss, sd1, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ante, P1, ST))
    x2 = w.s([npss, sd2, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ante, P2, ST))
    tvv = w.s([mstep[1], w.inst('simpl')], 'syl', '( %s -> %s e. V )' % (ante, T))
    c2ss = w.s([tvv, elcl, x2, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ante, C2, CFG(T)))
    j1 = w.s([alcl, x1, c2ss], '3jca', '( %s -> ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) )'
             % (ante, A, L(T), P1, ST, C2, CFG(T)))
    j2 = w.s([mstep[1], j1], 'jca', '( %s -> ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) )'
             % (ante, PHM, A, L(T), P1, ST, C2, CFG(T)))
    j3 = w.s([j2, cond], 'jca', '( %s -> ( ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) /\\ A. %s e. %s %s e. %s ) )'
             % (ante, PHM, A, L(T), P1, ST, C2, CFG(T), a, P1, SA_(a), C2))
    f = '( %s -> %s )' % (ante, HR(C1, T, M, C2, '1'))
    if qed:
        w.qed([j3, w.inst('tm2hstep')], 'syl', f); return None, C1, C2
    tri = w.s([j3, w.inst('tm2hstep')], 'syl', f)
    return tri, C1, C2
