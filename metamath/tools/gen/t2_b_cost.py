"""T2: the B-form weakening of a Hoare triple (blueprint D5)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tm2hleb():
    lab = 'tm2hleb'
    TR = HR('C', 'T', 'M', 'D', 'N')
    ph = '( ( %s /\\ %s ) /\\ ( B e. NN0 /\\ N <_ ( TMB ` B ) ) )' % (PHM, TR)
    w = W(lab, 'A Hoare triple weakened to the cost function ` TMB ` of '
               'TM/Cost.lean.  Every ` _le_B ` corollary of TM/Prims.lean is '
               'this theorem plus one inequality on bit lengths.')
    l = w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (ph, PHM, TR))
    r = w.s([], 'simpr', '( %s -> ( B e. NN0 /\\ N <_ ( TMB ` B ) ) )' % ph)
    b = w.s([r], 'simpld', '( %s -> B e. NN0 )' % ph)
    le = w.s([r], 'simprd', '( %s -> N <_ ( TMB ` B ) )' % ph)
    cl = w.s([b, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` B ) e. NN )' % ph)
    c0 = w.s([cl, w.inst('nnnn0')], 'syl', '( %s -> ( TMB ` B ) e. NN0 )' % ph)
    j = w.s([c0, le], 'jca', '( %s -> ( ( TMB ` B ) e. NN0 /\\ N <_ ( TMB ` B ) ) )' % ph)
    j2 = w.s([l, j], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( ( TMB ` B ) e. NN0 /\\ N <_ ( TMB ` B ) ) ) )'
              % (ph, PHM, TR))
    w.qed([j2, w.inst('tm2hle')], 'syl', '( %s -> %s )' % (ph, HR('C', 'T', 'M', 'D', '( TMB ` B )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2hleb'): tm2hleb()
