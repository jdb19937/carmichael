"""T3: generator helpers on top of tools/t1lib.py and tools/gen/t2_lib.py.

`hstepc2` is `t2_lib.hstepcp` with *two* state classes: the precondition's
` N1 C_ ( 2nd ` T ) ` and the postcondition's ` N2 C_ ( 2nd ` T ) ` .  Every
fragment of T3 changes the internal state (a carry, a flag, a comparison),
so the pre- and postcondition state classes differ.

`hstepE` is the same plumbing with an arbitrary postcondition class and a
body that proves the *membership* directly, for a step whose result is
reached through an existential (the two-operand read phase).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *


def _ralred(w, ante, T, M, A, NP, D1, POST, ral1, v, a, t, d1cl):
    """from ral1 : ( ante -> A. v e. NP ( ( M ` A ) sa <. v , D1 >. ) e. POST )
    conclude ( ante -> A. a e. ( NP X. { D1 } ) ( ( M ` A ) sa a ) e. POST )"""
    P1 = '( %s X. { %s } )' % (NP, D1)
    SA_ = lambda x: '( ( %s ` %s ) %s %s )' % (M, A, SA(T), x)
    d1v = w.s([d1cl], 'elexd', '( %s -> %s e. _V )' % (ante, D1))
    q1 = w.s([], 'opeq2', '( %s = %s -> <. %s , %s >. = <. %s , %s >. )' % (t, D1, v, t, v, D1))
    q2 = w.s([q1], 'oveq2d', '( %s = %s -> %s = %s )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), SA_('<. %s , %s >.' % (v, D1))))
    q3 = w.s([q2], 'eleq1d', '( %s = %s -> ( %s e. %s <-> %s e. %s ) )'
             % (t, D1, SA_('<. %s , %s >.' % (v, t)), POST, SA_('<. %s , %s >.' % (v, D1)), POST))
    q4 = w.s([q3], 'ralsng', '( %s e. _V -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (D1, t, D1, SA_('<. %s , %s >.' % (v, t)), POST, SA_('<. %s , %s >.' % (v, D1)), POST))
    q5 = w.s([d1v, q4], 'syl', '( %s -> ( A. %s e. { %s } %s e. %s <-> %s e. %s ) )'
             % (ante, t, D1, SA_('<. %s , %s >.' % (v, t)), POST, SA_('<. %s , %s >.' % (v, D1)), POST))
    q6 = w.s([q5], 'ralbidv', '( %s -> ( A. %s e. %s A. %s e. { %s } %s e. %s <-> A. %s e. %s %s e. %s ) )'
             % (ante, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), POST, v, NP,
                SA_('<. %s , %s >.' % (v, D1)), POST))
    q7 = w.s([q6, ral1], 'mpbird', '( %s -> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (ante, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), POST))
    p1 = w.s([], 'oveq2', '( %s = <. %s , %s >. -> %s = %s )'
             % (a, v, t, SA_(a), SA_('<. %s , %s >.' % (v, t))))
    p2 = w.s([p1], 'eleq1d', '( %s = <. %s , %s >. -> ( %s e. %s <-> %s e. %s ) )'
             % (a, v, t, SA_(a), POST, SA_('<. %s , %s >.' % (v, t)), POST))
    p3 = w.s([p2], 'ralxp', '( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s )'
             % (a, P1, SA_(a), POST, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), POST))
    p3a = w.s([p3], 'a1i', '( %s -> ( A. %s e. %s %s e. %s <-> A. %s e. %s A. %s e. { %s } %s e. %s ) )'
              % (ante, a, P1, SA_(a), POST, v, NP, t, D1, SA_('<. %s , %s >.' % (v, t)), POST))
    return w.s([p3a, q7], 'mpbird', '( %s -> A. %s e. %s %s e. %s )' % (ante, a, P1, SA_(a), POST))


def hstepE(w, ante, T, M, A, NP, D1, POST, mstep, alcl, postss, npss, d1cl, body,
           v='v', a='a', t='t', qed=False):
    """One machine step from ` ( { ( inl ` A ) } X. ( NP X. { D1 } ) ) ` --- the
    states restricted to ` NP ` , the stacks pinned --- to an arbitrary class
    ` POST ` of configurations.  `body(av)` proves
    ` ( av -> ( ( M ` A ) ( TM2sa ` T ) <. v , D1 >. ) e. POST ) ` at
    ` av = ( ante /\\ v e. NP ) ` .  `mstep` is a pair (the ` ( M ` A ) = ... `
    step, the PHM step)."""
    ST = '( %s X. %s )' % (S(T), STK(T))
    P1 = '( %s X. { %s } )' % (NP, D1)
    C1 = '( { ( inl ` %s ) } X. %s )' % (A, P1)
    av = '( %s /\\ %s e. %s )' % (ante, v, NP)
    SA_ = lambda x: '( ( %s ` %s ) %s %s )' % (M, A, SA(T), x)
    inc = body(av)
    ral1 = w.s([inc], 'ralrimiva', '( %s -> A. %s e. %s %s e. %s )'
               % (ante, v, NP, SA_('<. %s , %s >.' % (v, D1)), POST))
    cond = _ralred(w, ante, T, M, A, NP, D1, POST, ral1, v, a, t, d1cl)
    sd1 = w.s([d1cl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D1, STK(T)))
    x1 = w.s([npss, sd1, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ante, P1, ST))
    j1 = w.s([alcl, x1, postss], '3jca', '( %s -> ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) )'
             % (ante, A, L(T), P1, ST, POST, CFG(T)))
    j2 = w.s([mstep[1], j1], 'jca', '( %s -> ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) )'
             % (ante, PHM, A, L(T), P1, ST, POST, CFG(T)))
    j3 = w.s([j2, cond], 'jca',
             '( %s -> ( ( %s /\\ ( %s e. %s /\\ %s C_ %s /\\ %s C_ %s ) ) /\\ A. %s e. %s %s e. %s ) )'
             % (ante, PHM, A, L(T), P1, ST, POST, CFG(T), a, P1, SA_(a), POST))
    f = '( %s -> %s )' % (ante, HR(C1, T, M, POST, '1'))
    if qed:
        w.qed([j3, w.inst('tm2hstep')], 'syl', f); return None, C1
    return w.s([j3, w.inst('tm2hstep')], 'syl', f), C1


def hstepc2(w, ante, T, M, A, E, N1, N2, D1, D2, mstep, alcl, elcl, n1ss, n2ss, d1cl, d2cl,
            body, v='v', a='a', t='t', qed=False):
    """One machine step as a Hoare triple between
    ` ( { ( inl ` A ) } X. ( N1 X. { D1 } ) ) ` and
    ` ( { ( inl ` E ) } X. ( N2 X. { D2 } ) ) ` : the state class may change.

    `body(av)` returns (step proving
    ` ( av -> ( ( M ` A ) ( TM2sa ` T ) <. v , D1 >. ) = <. ( inl ` E ) , <. NEWV , D2 >. >. ) `,
    NEWV, step proving ` ( av -> NEWV e. N2 ) `), with ` av = ( ante /\\ v e. N1 ) `.
    """
    ST = '( %s X. %s )' % (S(T), STK(T))
    P2 = '( %s X. { %s } )' % (N2, D2)
    C2 = '( { ( inl ` %s ) } X. %s )' % (E, P2)
    av = '( %s /\\ %s e. %s )' % (ante, v, N1)
    SA_ = lambda x: '( ( %s ` %s ) %s %s )' % (M, A, SA(T), x)

    def bodyE(av2):
        eq, NEWV, nvcl = body(av2)
        RES = '<. ( inl ` %s ) , <. %s , %s >. >.' % (E, NEWV, D2)
        inle = w.s([], 'fvex', '( inl ` %s ) e. _V' % E)
        sn1 = w.s([inle, w.inst('snidg')], 'ax-mp', '( inl ` %s ) e. { ( inl ` %s ) }' % (E, E))
        sn1a = w.s([sn1], 'a1i', '( %s -> ( inl ` %s ) e. { ( inl ` %s ) } )' % (av2, E, E))
        d2v = w.s([d2cl], 'elexd', '( %s -> %s e. _V )' % (ante, D2))
        d2va = w.s([d2v], 'adantr', '( %s -> %s e. _V )' % (av2, D2))
        sn2 = w.s([d2va, w.inst('snidg')], 'syl', '( %s -> %s e. { %s } )' % (av2, D2, D2))
        pr2 = w.s([nvcl, sn2], 'opelxpd', '( %s -> <. %s , %s >. e. %s )' % (av2, NEWV, D2, P2))
        res = w.s([sn1a, pr2], 'opelxpd', '( %s -> %s e. %s )' % (av2, RES, C2))
        return w.s([eq, res], 'eqeltrd', '( %s -> %s e. %s )'
                   % (av2, SA_('<. %s , %s >.' % (v, D1)), C2))

    sd2 = w.s([d2cl], 'snssd', '( %s -> { %s } C_ %s )' % (ante, D2, STK(T)))
    x2 = w.s([n2ss, sd2, w.inst('xpss12')], 'syl2anc', '( %s -> %s C_ %s )' % (ante, P2, ST))
    tvv = w.s([mstep[1], w.inst('simpl')], 'syl', '( %s -> %s e. V )' % (ante, T))
    c2ss = w.s([tvv, elcl, x2, w.inst('tm2hcfgss')], 'syl3anc', '( %s -> %s C_ %s )' % (ante, C2, CFG(T)))
    r = hstepE(w, ante, T, M, A, N1, D1, C2, mstep, alcl, c2ss, n1ss, d1cl, bodyE,
               v=v, a=a, t=t, qed=qed)
    return (r[0], r[1], C2)
