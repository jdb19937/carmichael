#!/usr/bin/env python3
"""Sortie A1b: step 5 of Algorithm.lean (notMemTD, nodupTD, allPrimeTD,
korseltTD, verify).  MM_DB=sorties/a1b.mm python3 tools/gen/a1b_ver.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import (W, Cl, Spec, th_sf, th_cl, th_0, th_p1, defapply, conjsteps,
                    promote_qed, applied_text, B2, W0)

CLAUSE = lambda w, cl, sp: cl.mem(sp.clause(), sp.cod)

NOTMEM = Spec('NotMemTD', 'NotMemS', W0, B2,
              [('p', 'NN0', 'Q', 'fix'), ('l', W0, 'S', 'chg')],
              '<. 1o , 0 >.', listvar=0,
              desc='  Lean: notMemTD, the non-membership test of step 5.')

NODUP = Spec('NodupTD', 'NodupS', W0, B2,
             [('l', W0, 'S', 'chg')],
             '<. 1o , 0 >.', listvar=0,
             desc='  Lean: nodupTD, the distinctness test of step 5.')

ALLPRIME = Spec('AllPrimeTD', 'AllPrimeS', W0, B2,
                [('l', W0, 'S', 'chg')],
                '<. 1o , 0 >.', listvar=0,
                desc='  Lean: allPrimeTD, the all-primes test of step 5.')

KORSELT = Spec('KorseltTD', 'KorseltS', W0, B2,
               [('m', 'NN0', 'M', 'fix'), ('l', W0, 'S', 'chg')],
               '<. 1o , 0 >.', listvar=0,
               desc='  Lean: korseltTD, the Korselt test of step 5.')

SPECS = [NOTMEM, NODUP, ALLPRIME, KORSELT]


def _val(lab, const, label, args, desc, cod=None):
    def go():
        w = W(lab, desc)
        parts = ['%s e. %s' % (v, t) for v, t in args]
        ante, hs = conjsteps(w, parts)
        cl = Cl(w, ante)
        for v, t in args:
            cl.have(v, t, hs['%s e. %s' % (v, t)])
        st, val = defapply(w, cl, label, const, [v for v, _ in args])
        if cod is None:
            promote_qed(w, st)
        else:
            mm = cl.mem(val, cod)
            w.qed([st, mm], 'eqeltrd', '( %s -> %s e. %s )'
                  % (ante, applied_text(const, [v for v, _ in args]), cod))
        return w
    return go


VER_ARGS = [('M', 'NN0'), ('S', W0)]

BUILD = {}
for _s in SPECS:
    BUILD[_s.tok.lower() + 'sf'] = (lambda s: (lambda: th_sf(s, CLAUSE)))(_s)
    BUILD[_s.tok.lower() + 'cl'] = (lambda s: (lambda: th_cl(s)))(_s)
    BUILD[_s.tok.lower() + '0'] = (lambda s: (lambda: th_0(s)))(_s)
    BUILD[_s.tok.lower() + 'cs'] = (lambda s: (lambda: th_p1(s)))(_s)
BUILD['verifyval'] = _val('verifyval', 'Verify', 'df-verify', VER_ARGS,
                          'The value of ~ df-verify .  Lean: verify.')
BUILD['verifycl'] = _val('verifycl', 'Verify', 'df-verify', VER_ARGS,
                         'Step 5 returns a boolean and an operation count.', B2)

ORDER = [t + k for s in SPECS for t, k in [(s.tok.lower(), x) for x in ('sf', 'cl', '0', 'cs')]]
ORDER += ['verifyval', 'verifycl']

if __name__ == '__main__':
    names = sys.argv[1:] or ORDER
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
