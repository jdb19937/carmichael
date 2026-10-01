"""`logb2ge0`, our own base-two logarithm nonnegativity.

    MM_DB=sorties/g4.mm python3 tools/gen/g4_logb.py

set.mm's `logbge0b` is a mathbox theorem, and it is the last mathbox citation
`tools/cl.py` emits (its `0 <_ ( 2 logb X )` route).  This is the main-body
route to the half of it the automation uses: `relogbval` at base 2, `logge0`
for the numerator, `rplogcl` for the denominator and `divge0`.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tm import W

ANTE = '( X e. RR+ /\\ 1 <_ X )'


def build():
    w = W('logb2ge0', 'The base-two logarithm of a real number at least one is '
                      'nonnegative, from ` relogbval ` and ` divge0 ` . This is the '
                      'main-body route to the half of set.mm\'s mathbox theorem '
                      '` logbge0b ` that the proof automation of tools/cl.py needs.')
    rp = w.s([], 'simpl', '( %s -> X e. RR+ )' % ANTE)
    g1 = w.s([], 'simpr', '( %s -> 1 <_ X )' % ANTE)
    xr = w.s([rp, w.inst('rpre')], 'syl', '( %s -> X e. RR )' % ANTE)
    # ( 2 logb X ) = ( ( log ` X ) / ( log ` 2 ) )
    z2 = w.s([], '2z', '2 e. ZZ')
    u2 = w.s([z2, w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    u2d = w.s([u2], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ANTE)
    val = w.s([u2d, rp, w.inst('relogbval')], 'syl2anc',
              '( %s -> ( 2 logb X ) = ( ( log ` X ) / ( log ` 2 ) ) )' % ANTE)
    # 0 <_ ( log ` X )
    lx = w.s([rp, w.inst('relogcl')], 'syl', '( %s -> ( log ` X ) e. RR )' % ANTE)
    lx0 = w.s([xr, g1, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` X ) )' % ANTE)
    # 0 < ( log ` 2 )
    r2 = w.s([], '2re', '2 e. RR')
    lt = w.s([], '1lt2', '1 < 2')
    l2 = w.s([r2, lt, w.inst('rplogcl')], 'mp2an', '( log ` 2 ) e. RR+')
    l2d = w.s([l2], 'a1i', '( %s -> ( log ` 2 ) e. RR+ )' % ANTE)
    l2r = w.s([l2d], 'rpred', '( %s -> ( log ` 2 ) e. RR )' % ANTE)
    l2p = w.s([l2d], 'rpgt0d', '( %s -> 0 < ( log ` 2 ) )' % ANTE)
    q = w.s([w.s([lx, lx0], 'jca', '( %s -> ( ( log ` X ) e. RR /\\ 0 <_ ( log ` X ) ) )' % ANTE),
             w.s([l2r, l2p], 'jca', '( %s -> ( ( log ` 2 ) e. RR /\\ 0 < ( log ` 2 ) ) )' % ANTE),
             w.inst('divge0')], 'syl2anc',
            '( %s -> 0 <_ ( ( log ` X ) / ( log ` 2 ) ) )' % ANTE)
    w.qed([q, val], 'breqtrrd', '( %s -> 0 <_ ( 2 logb X ) )' % ANTE)
    return w


if __name__ == '__main__':
    sys.exit(0 if build().run() else 1)
