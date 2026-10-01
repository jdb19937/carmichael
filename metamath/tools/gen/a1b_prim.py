#!/usr/bin/env python3
"""Sortie A1b: the primitives of Algorithm.lean (primeGo, isPrimeTD, divOut,
smoothGo, smoothTD).  MM_DB=sorties/a1b.mm python3 tools/gen/a1b_prim.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import (W, Cl, Spec, th_sf, th_cl, th_0, th_p1, defapply, mptfv,
                    conjsteps, B2, N2, W0)

CLAUSE = lambda w, cl, sp: cl.mem(sp.clause(), sp.cod)

PRIMEGO = Spec('PrimeGo', 'PrimeGoS', 'NN0', B2,
               [('m', 'NN0', 'M', 'fix'), ('d', 'NN0', 'D', 'chg'), ('f', 'NN0', 'F', 'fuel')],
               '<. 1o , 0 >.',
               desc='  Lean: primeGo, the trial-division loop.')

DIVOUT = Spec('DivOut', 'DivOutS', 'NN0', N2,
              [('d', 'NN', 'D', 'fix'), ('r', 'NN0', 'R', 'chg'), ('f', 'NN0', 'F', 'fuel')],
              '<. g , 0 >.',
              desc='  Lean: divOut, the divide-out loop.')

SMOOTHGO = Spec('SmoothGo', 'SmoothGoS', '( NN X. NN0 )', N2,
                [('d', 'NN', 'D', 'chg'), ('r', 'NN0', 'R', 'chg'), ('f', 'NN0', 'F', 'fuel')],
                '<. ( 2nd ` g ) , 0 >.',
                desc='  Lean: smoothGo, the outer loop of the smoothness test.')

SPECS = {s.tok: s for s in (PRIMEGO, DIVOUT, SMOOTHGO)}


def isprimetdval():
    w = W('isprimetdval', 'The value of ~ df-isprimetd .  Lean: isPrimeTD.')
    ante, hs = conjsteps(w, ['M e. NN0'])
    cl = Cl(w, ante)
    cl.have('M', 'NN0', hs['M e. NN0'])
    st, val = defapply(w, cl, 'df-isprimetd', 'IsPrimeTD', ['M'])
    L.promote_qed(w, st)
    return w


def isprimetdcl():
    w = W('isprimetdcl', 'The primality test returns a boolean and an operation count.')
    ante, hs = conjsteps(w, ['M e. NN0'])
    cl = Cl(w, ante)
    cl.have('M', 'NN0', hs['M e. NN0'])
    st, val = defapply(w, cl, 'df-isprimetd', 'IsPrimeTD', ['M'])
    mm = cl.mem(val, B2)
    w.qed([st, mm], 'eqeltrd', '( %s -> ( IsPrimeTD ` M ) e. %s )' % (ante, B2))
    return w


def smoothtdval():
    w = W('smoothtdval', 'The value of ~ df-smoothtd .  Lean: smoothTD.')
    ante, hs = conjsteps(w, ['Y e. NN', 'K e. NN0'])
    cl = Cl(w, ante)
    cl.have('Y', 'NN', hs['Y e. NN'])
    cl.have('K', 'NN0', hs['K e. NN0'])
    st, val = defapply(w, cl, 'df-smoothtd', 'SmoothTD', ['Y', 'K'])
    L.promote_qed(w, st)
    return w


def smoothtdcl():
    w = W('smoothtdcl', 'The smoothness test returns a boolean and an operation count.')
    ante, hs = conjsteps(w, ['Y e. NN', 'K e. NN0'])
    cl = Cl(w, ante)
    cl.have('Y', 'NN', hs['Y e. NN'])
    cl.have('K', 'NN0', hs['K e. NN0'])
    ym1 = w.s([hs['Y e. NN'], w.inst('nnm1nn0')], 'syl', '( %s -> ( Y - 1 ) e. NN0 )' % ante)
    cl.have('( Y - 1 )', 'NN0', ym1)
    st, val = defapply(w, cl, 'df-smoothtd', 'SmoothTD', ['Y', 'K'])
    mm = cl.mem(val, B2)
    w.qed([st, mm], 'eqeltrd', '( %s -> ( Y SmoothTD K ) e. %s )' % (ante, B2))
    return w


def _mk(sp, kind):
    if kind == 'sf':
        return th_sf(sp, CLAUSE)
    if kind == 'cl':
        return th_cl(sp)
    if kind == '0':
        return th_0(sp)
    return th_p1(sp)


BUILD = {}
for _s in SPECS.values():
    for _k in ('sf', 'cl', '0', 'p1'):
        BUILD[_s.tok.lower() + _k] = (lambda s, k: (lambda: _mk(s, k)))(_s, _k)
BUILD['isprimetdval'] = isprimetdval
BUILD['isprimetdcl'] = isprimetdcl
BUILD['smoothtdval'] = smoothtdval
BUILD['smoothtdcl'] = smoothtdcl

ORDER = ['primegosf', 'primegocl', 'primego0', 'primegop1',
         'isprimetdval', 'isprimetdcl',
         'divoutsf', 'divoutcl', 'divout0', 'divoutp1',
         'smoothgosf', 'smoothgocl', 'smoothgo0', 'smoothgop1',
         'smoothtdval', 'smoothtdcl']

if __name__ == '__main__':
    names = sys.argv[1:] or ORDER
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
