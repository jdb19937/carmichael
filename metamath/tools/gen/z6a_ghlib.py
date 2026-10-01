"""Z6a (block z6ab): shared step patterns for the holomorphy of Gamma."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from z6alib import *

TOP = '( TopOpen ` CCfld )'


def HOLG(Fn, Dm):
    return '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (Fn, Dm, Dm, Fn)


def MP(x, X, E):
    return '( %s e. %s |-> %s )' % (x, X, E)


def BX(L='L', R='R'):
    return '( ( `\' Re " ( %s (,) %s ) ) i^i ( `\' Im " ( -u %s (,) %s ) ) )' % (L, R, R, R)


def st(w, ante):
    """step writer under the antecedent"""
    return lambda hyps, ref, g, name=None: w.s(hyps, ref, '( %s -> %s )' % (ante, g), name=name)


def c1(w, ante, ref, fact):
    """closed fact lifted into the antecedent"""
    return w.s([w.s([], ref, fact)], 'a1i', '( %s -> %s )' % (ante, fact))


def opnss(w, ante, uo, U):
    """( ante -> U C_ CC ) from uo: ( ante -> U e. TOP )"""
    e = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ton = w.s([w.s([e], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOP)], 'a1i', '( %s -> %s e. ( TopOn ` CC ) )' % (ante, TOP))
    return w.s([ton, uo, w.inst('toponss')], 'syl2anc', '( %s -> %s C_ CC )' % (ante, U))


def dvres(w, ante, x, U, A, B, dcc, clsA, clsB, uo, ucc):
    """( ante -> ( CC _D ( x e. U |-> A ) ) = ( x e. U |-> B ) ) from
    dcc: ( ante -> ( CC _D ( x e. CC |-> A ) ) = ( x e. CC |-> B ) ),
    clsA, clsB: ( ( ante /\\ x e. CC ) -> A e. CC ), ( ... -> B e. CC ), uo: U open, ucc: U C_ CC"""
    sc = c1(w, ante, 'cnelprrecn', 'CC e. { RR , CC }')
    ej = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    return w.s([sc, clsA, clsB, dcc, ucc, ej, ek, uo], 'dvmptres',
               '( %s -> ( CC _D %s ) = %s )' % (ante, MP(x, U, A), MP(x, U, B)))


def holfromdv(w, ante, x, X, A, B, dveq, clsA, clsB, xss):
    """( ante -> HOLG( ( x e. X |-> A ), X ) ) from dveq: ( ante -> ( CC _D ( x e. X |-> A ) ) = ( x e. X |-> B ) ),
    clsA, clsB: ( ( ante /\\ x e. X ) -> A / B e. CC ), xss: ( ante -> X C_ CC )"""
    MA = MP(x, X, A); MB = MP(x, X, B)
    hf = w.s([clsB, w.s([], 'eqid', '%s = %s' % (MB, MB))], 'fmptd', '( %s -> %s : %s --> CC )' % (ante, MB, X))
    dm = w.s([w.s([dveq], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom %s )' % (ante, MA, MB)),
              w.s([hf, w.inst('fdm')], 'syl', '( %s -> dom %s = %s )' % (ante, MB, X))], 'eqtrd', '( %s -> dom ( CC _D %s ) = %s )' % (ante, MA, X))
    ssd = w.s([w.s([dm], 'eqcomd', '( %s -> %s = dom ( CC _D %s ) )' % (ante, X, MA))], 'eqimssd', '( %s -> %s C_ dom ( CC _D %s ) )' % (ante, X, MA))
    gf = w.s([clsA, w.s([], 'eqid', '%s = %s' % (MA, MA))], 'fmptd', '( %s -> %s : %s --> CC )' % (ante, MA, X))
    cn = w.s([w.s([w.s([c1(w, ante, 'ssid', 'CC C_ CC'), gf, xss], '3jca', '( %s -> ( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC ) )' % (ante, MA, X, X)), dm], 'jca',
                  '( %s -> ( ( CC C_ CC /\\ %s : %s --> CC /\\ %s C_ CC ) /\\ dom ( CC _D %s ) = %s ) )' % (ante, MA, X, X, MA, X)), w.inst('dvcn')], 'syl',
             '( %s -> %s e. ( %s -cn-> CC ) )' % (ante, MA, X))
    return w.s([cn, ssd], 'jca', '( %s -> %s )' % (ante, HOLG(MA, X)))


def holeq(w, ante, MA, MB, X, hol, eq):
    """( ante -> HOLG(MB, X) ) from hol: ( ante -> HOLG(MA, X) ) and eq: ( ante -> MA = MB )"""
    b1 = w.s([eq], 'eleq1d', '( %s -> ( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) ) )' % (ante, MA, X, MB, X))
    b2 = w.s([w.s([w.s([eq], 'oveq2d', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (ante, MA, MB))], 'dmeqd', '( %s -> dom ( CC _D %s ) = dom ( CC _D %s ) )' % (ante, MA, MB))],
             'sseq2d', '( %s -> ( %s C_ dom ( CC _D %s ) <-> %s C_ dom ( CC _D %s ) ) )' % (ante, X, MA, X, MB))
    return w.s([hol, w.s([b1, b2], 'anbi12d', '( %s -> ( %s <-> %s ) )' % (ante, HOLG(MA, X), HOLG(MB, X)))], 'mpbid', '( %s -> %s )' % (ante, HOLG(MB, X)))


def status(label):
    import re
    p = os.path.join(os.path.dirname(__file__), '..', '..', 'worksheets', label + '.mmp')
    n = sum(1 for l in open(p) if re.match(r'^[0-9a-z]+:', l))
    with open(os.path.join(os.path.dirname(__file__), '..', '..', 'scratch', 'z6ab-status.md'), 'a') as f:
        f.write('- %s: done (%d steps)\n' % (label, n))


def mpval(w, ante, x, X, body, T, mem, exs=None):
    """( ante -> ( ( x e. X |-> body ) ` T ) = body[T/x] ) by fvmptd3; returns (step, value)"""
    from congr import StepGen
    mp = '( %s e. %s |-> %s )' % (x, X, body)
    idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (x, T, x, T))
    stp, val = w.congr(body, {x: T}, '%s = %s' % (x, T), {x: idx})
    if stp is None:
        stp = w.s([], 'eqidd', '( %s = %s -> %s = %s )' % (x, T, body, val))
    if exs is None:
        from congr import parse as _parse
        k = _parse(val).kind
        assert k in ('fv', 'ov'), 'pass exs= for ' + val
        exs = w.s([], 'fvexd' if k == 'fv' else 'ovexd', '( %s -> %s e. _V )' % (ante, val))
    em = w.s([], 'eqid', '%s = %s' % (mp, mp))
    return w.s([em, stp, mem, exs], 'fvmptd3', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, T, val)), val
