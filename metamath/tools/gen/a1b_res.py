#!/usr/bin/env python3
"""Sortie A1b: steps 2 and 3 of Algorithm.lean (resGo, reservoir, poolGo,
poolAlg, scan).  MM_DB=sorties/a1b.mm python3 tools/gen/a1b_res.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import (W, Cl, Spec, th_sf, th_cl, th_0, th_p1, defapply, conjsteps,
                    promote_qed, B2, WN, W0, OPN)

CLAUSE = lambda w, cl, sp: cl.mem(sp.clause(), sp.cod)

RESGO = Spec('ResGo', 'ResGoS', 'NN', WN,
             [('z', 'NN0', 'Z', 'fix'), ('y', 'NN', 'Y', 'fix'),
              ('q', 'NN', 'Q', 'chg'), ('f', 'NN0', 'F', 'fuel')],
             '<. (/) , 0 >.',
             desc='  Lean: resGo, the reservoir loop of step 2.')

POOLGO = Spec('PoolGo', 'PoolGoS', W0, WN,
              [('x', 'NN0', 'X', 'fix'), ('z', 'NN0', 'Z', 'fix'),
               ('k', 'NN0', 'K', 'fix'), ('l', W0, 'S', 'chg')],
              '<. (/) , 0 >.', listvar=0,
              desc='  Lean: poolGo, the pool loop of step 3.')

SCAN = Spec('Scan', 'ScanS', 'NN0', OPN,
            [('q', W0, 'S', 'fix'), ('x', 'NN0', 'X', 'fix'), ('z', 'NN0', 'Z', 'fix'),
             ('o', 'NN0', 'O', 'fix'), ('k', 'NN0', 'K', 'chg'), ('f', 'NN0', 'F', 'fuel')],
            '<. ( inr ` (/) ) , 0 >.',
            desc='  Lean: scan, the search of step 3 for an accepted shift.')

SPECS = [RESGO, POOLGO, SCAN]


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
                  % (ante, L.applied_text(const, [v for v, _ in args]), cod))
        return w
    return go


RES_ARGS = [('Z', 'NN'), ('V', 'NN0'), ('Y', 'NN')]
POOLALG_ARGS = [('S', W0), ('X', 'NN0'), ('Z', 'NN0'), ('K', 'NN0')]

BUILD = {}
for _s in SPECS:
    BUILD[_s.tok.lower() + 'sf'] = (lambda s: (lambda: th_sf(s, CLAUSE)))(_s)
    BUILD[_s.tok.lower() + 'cl'] = (lambda s: (lambda: th_cl(s)))(_s)
    BUILD[_s.tok.lower() + '0'] = (lambda s: (lambda: th_0(s)))(_s)
    BUILD[_s.tok.lower() + ('cs' if _s.listvar is not None else 'p1')] = \
        (lambda s: (lambda: th_p1(s)))(_s)
BUILD['reservoirval'] = _val('reservoirval', 'Reservoir', 'df-reservoir', RES_ARGS,
                             'The value of ~ df-reservoir .  Lean: reservoir.')
BUILD['reservoircl'] = _val('reservoircl', 'Reservoir', 'df-reservoir', RES_ARGS,
                            'Step 2 returns a list of primes and an operation count.', WN)
BUILD['poolalgval'] = _val('poolalgval', 'PoolAlg', 'df-poolalg', POOLALG_ARGS,
                           'The value of ~ df-poolalg .  Lean: poolAlg.')
BUILD['poolalgcl'] = _val('poolalgcl', 'PoolAlg', 'df-poolalg', POOLALG_ARGS,
                          'The pool of step 3 is a list and an operation count.', WN)

ORDER = ['resgosf', 'resgocl', 'resgo0', 'resgop1', 'reservoirval', 'reservoircl',
         'poolgosf', 'poolgocl', 'poolgo0', 'poolgocs', 'poolalgval', 'poolalgcl',
         'scansf', 'scancl', 'scan0', 'scanp1']

if __name__ == '__main__':
    names = sys.argv[1:] or ORDER
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
