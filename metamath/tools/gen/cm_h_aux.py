"""Sortie CM: shared step helpers for cm_h (census count is real)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *


def cntre(w, A0, zr):
    """( A0 -> CNT(S,V,|_ Z) e. RR ) from zr ( A0 -> Z e. RR )"""
    K = '( |_ ` Z )'
    Bm = BC('S', 'V', 'm')
    Cm = '( %s /\\ m e. ( 1 ... %s ) )' % (A0, K)
    cm = mk(w, Cm)
    mn = cm('syl', [w.s([], 'simpr', '( %s -> m e. ( 1 ... %s ) )' % (Cm, K)), w.inst('elfznn')], 'm e. NN')
    hm = cm('syl', [cm('simpld', [cm('syl', [mn, w.inst('cen2bcf')], '( %s e. Fin /\\ ( # ` %s ) <_ m )' % (Bm, Bm))], '%s e. Fin' % Bm), w.inst('hashcl')], '( # ` %s ) e. NN0' % Bm)
    return D(w, A0, 'fsumrecl', [D(w, A0, 'fzfid', [], '( 1 ... %s ) e. Fin' % K), cm('nn0red', [hm], '( # ` %s ) e. RR' % Bm)], '%s e. RR' % CNT('S', 'V', K))
