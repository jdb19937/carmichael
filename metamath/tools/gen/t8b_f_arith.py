"""T8b: the stage sums of setIfNoneF and lookupSlot as polynomial identities in the atoms
` J ` (the index), ` S ` ( ` slotC ` ), ` H ` , ` C ` (copyList's case bound).

  ttsetcx   walkDown + slotC + walkUp + 3 = setC
  ttlookcx  walkDown + ( C + 9 ) + walkUp + 2 = lookC with C = N ( 6 b + 17 )

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_f_arith.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
from lin import lineq, nlinarith
from cl import Closure

SEL = sys.argv[1:]
WDNX = '( ( J x. ( ( S + ( 4 x. H ) ) + 9 ) ) + ( ( 3 x. H ) + 8 ) )'
WUPX = '( ( J x. ( S + 2 ) ) + 3 )'
SETX = '( ( ( ( J x. ( ( ( 2 x. S ) + ( 4 x. H ) ) + ; 1 1 ) ) + S ) + ( 3 x. H ) ) + ; 1 4 )'
LKX = '( ( ( ( J x. ( ( ( 2 x. S ) + ( 4 x. H ) ) + ; 1 1 ) ) + C ) + ( 3 x. H ) ) + ; 2 2 )'
ST = {
    'ttsetcx': '( ( J e. NN0 /\\ S e. NN0 /\\ H e. NN0 ) -> ( ( ( %s + S ) + %s ) + 3 ) = %s )' % (WDNX, WUPX, SETX),
    'ttcopycx': '( ( L e. NN0 /\\ C e. NN0 /\\ S e. NN0 ) -> ( ( ( L x. ( ( ( C + ; 1 1 ) + S ) + 2 ) ) + ( ( L x. ( S + 2 ) ) + 3 ) ) + 4 ) <_ ( ( L x. ( ( C + ( 2 x. S ) ) + ; 1 5 ) ) + 8 ) )',
    'ttdpbcx': '( ( B e. NN0 /\\ S e. NN0 ) -> ( ( ( ( ; 2 5 x. ( 2 x. B ) ) + ; 5 3 ) + ( S + ( ( 6 x. B ) + ; 1 0 ) ) ) + 2 ) <_ ( ( ( ; 5 6 x. B ) + ; 6 7 ) + S ) )',
    'ttmodbx': '( ( ( X e. NN0 /\\ Y e. NN0 /\\ B e. NN0 ) /\\ ( X <_ B /\\ Y <_ B ) ) -> ( ( X x. ( ( ; 2 3 x. ( X + Y ) ) + ; 6 0 ) ) + ( ( 9 x. ( X + Y ) ) + ; 2 8 ) ) <_ ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 1 8 x. B ) ) + ; 2 8 ) )',
    'ttdpcx': '( ( B e. NN0 /\\ S e. NN0 /\\ Z e. NN0 ) -> ( ( ( ( ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 2 2 x. B ) ) + ; 3 8 ) + ( S + ( ( 4 x. B ) + ; 1 1 ) ) ) + ( ( 3 x. B ) + 3 ) ) + Z ) + 4 ) <_ ( ( ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 3 3 x. B ) ) + ; 6 4 ) + S ) + Z ) )',
    'ttlookcx': '( ( J e. NN0 /\\ ( S e. NN0 /\\ C e. NN0 ) /\\ H e. NN0 ) -> ( ( ( %s + ( C + 9 ) ) + %s ) + 2 ) = %s )' % (WDNX, WUPX, LKX),
}


def mk(lab):
    ph = ST[lab].split(' -> ')[0][2:]
    lhs = ST[lab][len('( ' + ph + ' -> '):-2]
    a, b = lhs.split(' = ', 1) if False else (None, None)
    w = W(lab, {'ttsetcx': 'The stage sum of Lean\'s ` setIfNoneF_runs ` as a polynomial identity (atoms ` J ` , ` S ` , ` H ` ).',
               'ttdpbcx': '( ( B e. NN0 /\\ S e. NN0 ) -> ( ( ( ( ; 2 5 x. ( 2 x. B ) ) + ; 5 3 ) + ( S + ( ( 6 x. B ) + ; 1 0 ) ) ) + 2 ) <_ ( ( ( ; 5 6 x. B ) + ; 6 7 ) + S ) )',
    'ttmodbx': '( ( ( X e. NN0 /\\ Y e. NN0 /\\ B e. NN0 ) /\\ ( X <_ B /\\ Y <_ B ) ) -> ( ( X x. ( ( ; 2 3 x. ( X + Y ) ) + ; 6 0 ) ) + ( ( 9 x. ( X + Y ) ) + ; 2 8 ) ) <_ ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 1 8 x. B ) ) + ; 2 8 ) )',
    'ttdpcx': '( ( B e. NN0 /\\ S e. NN0 /\\ Z e. NN0 ) -> ( ( ( ( ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 2 2 x. B ) ) + ; 3 8 ) + ( S + ( ( 4 x. B ) + ; 1 1 ) ) ) + ( ( 3 x. B ) + 3 ) ) + Z ) + 4 ) <_ ( ( ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 3 3 x. B ) ) + ; 6 4 ) + S ) + Z ) )',
    'ttlookcx': 'The stage sum of Lean\'s ` lookupSlot_runs ` as a polynomial identity (atoms ` J ` , ` S ` , ` H ` , ` C ` ).',
               'ttmodbx': 'Lean\'s bound of ` modFrag ` at inputs of at most ` b ` bits (the ` hmod ` of ` dpStepF_runs ` ).',
               'ttdpcx': 'The stage sum of Lean\'s ` dpStepF_runs ` is at most ` dpC ` (atoms ` B ` , ` S ` , ` Z ` ).',
               'ttdpbcx': 'The stage sum of Lean\'s ` dpBodyF_runs ` is at most ` dpBodyC ` (atoms ` B ` , ` S ` ).',
               'ttcopycx': 'The stage sum of Lean\'s ` copyTbl_runs ` is at most ` copyC ` (atoms ` L ` , ` C ` , ` S ` ).'}[lab])
    c = Ctx(w, ph, parse_conj(ph))
    extra_h = []
    if lab == 'ttmodbx':
        extra_h = [c['X <_ B'], c['Y <_ B']]
    vs = {'ttsetcx': ['J', 'S', 'H'], 'ttlookcx': ['J', 'S', 'H', 'C'], 'ttcopycx': ['L', 'C', 'S'], 'ttdpbcx': ['B', 'S'], 'ttmodbx': ['X', 'Y', 'B'], 'ttdpcx': ['B', 'S', 'Z']}[lab]
    leaves = {v: ('NN0', c['%s e. NN0' % v]) for v in vs}
    cl = Closure(w, ph, leaves)
    body = ST[lab][len('( %s -> ' % ph):-2]
    toks = body.split()
    # split at the top-level ' = '
    d = 0
    for i, t in enumerate(toks):
        if t in ('(', '<.', '{'):
            d += 1
        elif t in (')', '>.', '}'):
            d -= 1
        elif t in ('=', '<_') and d == 0:
            L_, R_, rel = ' '.join(toks[:i]), ' '.join(toks[i + 1:]), t
            break
    if rel == '=':
        e = lineq(w, ph, L_, R_, closure=cl, products=True)
    else:
        e = nlinarith(w, ph, [cl.ge0(v) for v in vs] + extra_h, '%s <_ %s' % (L_, R_), closure=cl)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        mk(l)
