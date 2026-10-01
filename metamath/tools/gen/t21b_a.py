"""Sortie T21b: t21bcj (letters of badChars)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_base import *


def gen_bcj():
    w = W('t21bcj', 'The Census set ` badChars ( S , V , M ) ` in the character letter ` j ` ( ~ cbvrabv ; the letters of ~ t21nzb ).')
    phi = lambda y: '( ( M DChrCond %s ) = M /\\ { o e. %s | ( o =/= 1 /\\ ( ( M DChrLF %s ) ` o ) = 0 ) } =/= (/) )' % (y, BOX('S', 'V'), y)
    idy = w.s([], 'id', '( y = j -> y = j )')
    c, new = w.wcongr(phi('y'), {'y': 'j'}, 'y = j', {'y': idy})
    assert new == phi('j'), new
    w.qed([c], 'cbvrabv', SB['t21bcj'])
    return go(w)


if __name__ == '__main__':
    gen_bcj()
