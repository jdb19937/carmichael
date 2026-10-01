#!/usr/bin/env python3
"""Sortie A1b: the extraction loop of step 4 (extractGo, extract).
MM_DB=sorties/a1b.mm python3 tools/gen/a1b_ext.py [LABEL...]"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import a1blib as L
from a1blib import (W, Cl, Spec, th_sf, th_cl, th_0, th_p1, defapply, conjsteps,
                    promote_qed, W0, TB, OPN, EXD)

CLAUSE = lambda w, cl, sp: cl.mem(sp.clause(), sp.cod)

EXTRACTGO = Spec('ExtractGo', 'ExtractGoS', EXD, OPN,
                 [('l', 'NN', 'L', 'fix'), ('n', 'NN0', 'N', 'fix'),
                  ('p', W0, 'S', 'chg'), ('m', 'NN0', 'M', 'chg'),
                  ('v', W0, 'U', 'chg'), ('t', TB, 'T', 'chg')],
                 '<. ( inr ` (/) ) , 0 >.', listvar=0,
                 desc='  Lean: extractGo, the greedy extraction loop of step 4.')


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


EXTRACT_ARGS = [('L', 'NN'), ('N', 'NN0'), ('S', W0)]

ST1 = '( 1st ` ( ( L DpStep P ) ` T ) )'
LOOK = '( %s ` ( 1 mod L ) )' % ST1
CONDN = '%s = ( inr ` (/) )' % LOOK
CONDS = '%s =/= ( inr ` (/) )' % LOOK


def _hookn(w, cl, sp):
    return {CONDN: (True, cl.hyps[CONDN])}


def _hooks(w, cl, sp):
    ne = cl.hyps[CONDS]
    cl.memo[(LOOK, 'neinr')] = ne
    return {CONDN: (False, w.s([ne], 'neneqd', '( %s -> -. %s )' % (cl.ante, CONDN)))}


def extractgocsn():
    return th_p1(EXTRACTGO, extra=[CONDN], hook=_hookn, lab='extractgocsn',
                 desc='The step of the recursion of ~ df-extractgo when the residue '
                      '` 1 mod L ` has no witness, Lean\'s second equation lemma in the '
                      '` none ` branch of its match.  ~ extractgocss is the other branch.')


def extractgocss():
    return th_p1(EXTRACTGO, extra=[CONDS], hook=_hooks, lab='extractgocss',
                 desc='The step of the recursion of ~ df-extractgo when the residue '
                      '` 1 mod L ` has a witness ` ( 2nd ` ( st.1 ` ( 1 mod L ) ) ) `, '
                      'Lean\'s second equation lemma in the ` some S ` branch of its '
                      'match.  ~ extractgocsn is the other branch.')


BUILD = {'extractgosf': lambda: th_sf(EXTRACTGO, CLAUSE),
         'extractgocl': lambda: th_cl(EXTRACTGO),
         'extractgo0': lambda: th_0(EXTRACTGO),
         'extractgocsn': extractgocsn,
         'extractgocss': extractgocss,
         'extractval': _val('extractval', 'Extract', 'df-extract', EXTRACT_ARGS,
                            'The value of ~ df-extract .  Lean: extract.'),
         'extractcl': _val('extractcl', 'Extract', 'df-extract', EXTRACT_ARGS,
                           'Step 4 returns an optional pair and an operation count.', OPN)}

ORDER = ['extractgosf', 'extractgocl', 'extractgo0', 'extractgocsn', 'extractgocss',
         'extractval', 'extractcl']

if __name__ == '__main__':
    names = sys.argv[1:] or ORDER
    ok = True
    for nm in names:
        ok = BUILD[nm]().run() and ok
    sys.exit(0 if ok else 1)
