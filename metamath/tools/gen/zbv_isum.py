"""Sortie ZBV, block ZF1: reindexing an infinite sum along a strictly
increasing map NN --> NN (set.mm's isercoll at the sum_ level).

isumcollcvg  ( ph -> ( seq 1 ( + , H ) e. dom ~~> <-> seq 1 ( + , F ) e. dom ~~> ) )
isumcoll     ( ph -> sum_ n e. NN ( F ` n ) = sum_ j e. NN ( H ` j ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbvlib import *

HG = '( ph -> G : NN --> NN )'
HI = '( ( ph /\\ k e. NN ) -> ( G ` k ) < ( G ` ( k + 1 ) ) )'
H0 = '( ( ph /\\ n e. ( NN \\ ran G ) ) -> ( F ` n ) = 0 )'
HF = '( ( ph /\\ n e. NN ) -> ( F ` n ) e. CC )'
HH = '( ( ph /\\ k e. NN ) -> ( H ` k ) = ( F ` ( G ` k ) ) )'
SH = 'seq 1 ( + , H )'
SF = 'seq 1 ( + , F )'


def hyps(w):
    L = w.label
    return [hyp(w, '1', L + '.g', HG), hyp(w, '2', L + '.i', HI),
            hyp(w, '3', L + '.0', H0), hyp(w, '4', L + '.f', HF),
            hyp(w, '5', L + '.h', HH)]


def isumcollcvg():
    w = W('isumcollcvg', 'Convergence of a series is unchanged by collapsing the zero terms '
                         'off the range of a strictly increasing map (isercoll at the level '
                         'of dom ~~>).')
    hg, hi, h0, hf, hh = hyps(w)
    z = clo(w, 'nnuz', NNUZ)
    out = []
    for (X, Y, name) in ((SH, SF, 'fwd'), (SF, SH, 'bwd')):
        A = '( ph /\\ %s e. dom ~~> )' % X
        st = mkst(w, A)
        L = '( ~~> ` %s )' % X
        cd = st([w.s([], 'climdm', '( %s e. dom ~~> <-> %s ~~> %s )' % (X, X, L))], 'a1i',
                '( %s e. dom ~~> <-> %s ~~> %s )' % (X, X, L))
        lim = st([st([], 'simpr', '%s e. dom ~~>' % X), cd], 'mpbid', '%s ~~> %s' % (X, L))
        one = st([], '1zzd', '1 e. ZZ')
        bic = st([z, one, adl(w, hg, '%s e. dom ~~>' % X), adlr(w, hi, '%s e. dom ~~>' % X),
                  adlr(w, h0, '%s e. dom ~~>' % X), adlr(w, hf, '%s e. dom ~~>' % X),
                  adlr(w, hh, '%s e. dom ~~>' % X)], 'isercoll',
                 '( %s ~~> %s <-> %s ~~> %s )' % (SH, L, SF, L))
        limy = st([lim, bic], 'mpbid' if X == SH else 'mpbird', '%s ~~> %s' % (Y, L))
        rel = w.s([], 'climrel', 'Rel ~~>')
        eld = st([st([rel], 'a1i', 'Rel ~~>'), limy, w.inst('releldm')], 'syl2anc', '%s e. dom ~~>' % Y)
        out.append(w.s([eld], 'ex', '( ph -> ( %s e. dom ~~> -> %s e. dom ~~> ) )' % (X, Y)))
    w.qed(out, 'impbid', '( ph -> ( %s e. dom ~~> <-> %s e. dom ~~> ) )' % (SH, SF))
    return w


def isumcoll():
    w = W('isumcoll', 'Reindexing an infinite sum along a strictly increasing map: the sum '
                      'of F over NN equals the sum of its values along G when F vanishes '
                      'off the range of G and the reindexed series converges.')
    hg, hi, h0, hf, hh = hyps(w)
    hc = hyp(w, '6', 'isumcoll.c', '( ph -> %s e. dom ~~> )' % SH)
    z = clo(w, 'nnuz', NNUZ)
    AK = '( ph /\\ k e. NN )'
    sk = mkst(w, AK)
    gk = sk([adl(w, hg, 'k e. NN'), sk([], 'simpr', 'k e. NN')], 'ffvelcdmd', '( G ` k ) e. NN')
    fgk, _ = inst(w, AK, 'NN', 'n', '( G ` k )', adlr(w, hf, 'k e. NN'), '( F ` n ) e. CC', gk)
    hkc = sk([hh, fgk], 'eqeltrd', '( H ` k ) e. CC')
    hjc, _ = rename(w, 'ph', 'NN', 'k', 'j', hkc, '( H ` k ) e. CC')
    AJ = '( ph /\\ j e. NN )'
    one = w.s([], '1zzd', '( ph -> 1 e. ZZ )')
    eqj = w.s([], 'eqidd', '( %s -> ( H ` j ) = ( H ` j ) )' % AJ)
    SUM = 'sum_ j e. NN ( H ` j )'
    lh = w.s([z, one, eqj, hjc, hc], 'isumclim2', '( ph -> %s ~~> %s )' % (SH, SUM))
    bic = w.s([z, one, hg, hi, h0, hf, hh], 'isercoll',
              '( ph -> ( %s ~~> %s <-> %s ~~> %s ) )' % (SH, SUM, SF, SUM))
    lf = w.s([lh, bic], 'mpbid', '( ph -> %s ~~> %s )' % (SF, SUM))
    eqn = w.s([], 'eqidd', '( ( ph /\\ n e. NN ) -> ( F ` n ) = ( F ` n ) )')
    w.qed([z, one, eqn, hf, lf], 'isumclim', '( ph -> sum_ n e. NN ( F ` n ) = %s )' % SUM)
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['isumcollcvg', 'isumcoll']:
        runh(globals()[f]())
