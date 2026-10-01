#!/usr/bin/env python3
"""Sortie A1b: the list recursions of Algorithm.lean (mulAll, divisorsOf,
coprimeTo, prodL).  MM_DB=sorties/a1b.mm python3 tools/gen/a1b_list.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import Spec, th_sf, th_cl, th_0, th_p1, B2, N2, WN, W0

CLAUSE = lambda w, cl, sp: cl.mem(sp.clause(), sp.cod)

MULALL = Spec('MulAll', 'MulAllS', W0, WN,
              [('q', 'NN0', 'Q', 'fix'), ('l', W0, 'S', 'chg')],
              '<. (/) , 0 >.', listvar=0,
              desc='  Lean: mulAll, the scaling map of the divisor enumeration.')

DIVISORSOF = Spec('DivisorsOf', 'DivisorsOfS', W0, WN,
                  [('l', W0, 'S', 'chg')],
                  '<. <" 1 "> , 0 >.', listvar=0,
                  desc='  Lean: divisorsOf, the subset products of a list.')

COPRIMETO = Spec('CoprimeTo', 'CoprimeToS', W0, B2,
                 [('l', W0, 'S', 'chg'), ('k', 'NN0', 'K', 'fix')],
                 '<. 1o , 0 >.', listvar=0,
                 desc='  Lean: coprimeTo, the coprimality test of step 3.')

PRODL = Spec('ProdL', 'ProdLS', W0, N2,
             [('l', W0, 'S', 'chg')],
             '<. 1 , 0 >.', listvar=0,
             desc='  Lean: prodL, the product of a list.')

SPECS = [MULALL, DIVISORSOF, COPRIMETO, PRODL]

BUILD = {}
for _s in SPECS:
    BUILD[_s.tok.lower() + 'sf'] = (lambda s: (lambda: th_sf(s, CLAUSE)))(_s)
    BUILD[_s.tok.lower() + 'cl'] = (lambda s: (lambda: th_cl(s)))(_s)
    BUILD[_s.tok.lower() + '0'] = (lambda s: (lambda: th_0(s)))(_s)
    BUILD[_s.tok.lower() + 'cs'] = (lambda s: (lambda: th_p1(s)))(_s)

ORDER = [t + k for s in SPECS for t, k in [(s.tok.lower(), x) for x in ('sf', 'cl', '0', 'cs')]]

if __name__ == '__main__':
    names = sys.argv[1:] or ORDER
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
