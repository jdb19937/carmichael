"""Sortie T21b: t21om (omega_le_self)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *

PN = '{ p e. Prime | p || N }'


def gen_om():
    w = W('t21om', 'The number of prime factors of ` N ` is at most ` N ` (Lean ` omega_le_self ` ; ~ hashss , ~ hashfz1 ).')
    A0 = 'N e. NN'
    s = S_(w, A0)
    Ap = '( %s /\\ x e. %s )' % (A0, PN)
    sp = S_(w, Ap)
    el = sp([sp([], 'simpr', 'x e. %s' % PN), w.s([w.s([], 'breq1', '( p = x -> ( p || N <-> x || N ) )')], 'elrab', '( x e. %s <-> ( x e. Prime /\\ x || N ) )' % PN)], 'sylib', '( x e. Prime /\\ x || N )')
    xn = sp([sp([el], 'simpld', 'x e. Prime'), w.inst('prmnn')], 'syl', 'x e. NN')
    xl = sp([sp([el], 'simprd', 'x || N'), sp([sp([sp([xn], 'nnzd', 'x e. ZZ'), sp([], 'simpl', 'N e. NN')], 'jca', '( x e. ZZ /\\ N e. NN )'), w.inst('dvdsle')], 'syl', '( x || N -> x <_ N )')], 'mpd', 'x <_ N')
    xf = sp([sp([xn, sp([], 'simpl', 'N e. NN'), xl], '3jca', '( x e. NN /\\ N e. NN /\\ x <_ N )'), w.s([], 'elfz1b', '( x e. ( 1 ... N ) <-> ( x e. NN /\\ N e. NN /\\ x <_ N ) )')], 'sylibr', 'x e. ( 1 ... N )')
    ss = s([w.s([xf], 'ex', '( N e. NN -> ( x e. %s -> x e. ( 1 ... N ) ) )' % PN)], 'ssrdv', '%s C_ ( 1 ... N )' % PN)
    h = s([s([s([], 'fzfid', '( 1 ... N ) e. Fin'), ss], 'jca', '( ( 1 ... N ) e. Fin /\\ %s C_ ( 1 ... N ) )' % PN), w.inst('hashss')], 'syl', '( # ` %s ) <_ ( # ` ( 1 ... N ) )' % PN)
    hf = s([s([], 'nnnn0', 'N e. NN0') if False else w.s([], 'nnnn0', '( N e. NN -> N e. NN0 )'), w.inst('hashfz1')], 'syl', '( # ` ( 1 ... N ) ) = N')
    w.qed([h, hf], 'breqtrd', SB['t21om'])
    return go(w)


if __name__ == '__main__':
    gen_om()
