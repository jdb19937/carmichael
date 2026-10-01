"""T10: append the handler ` readBraOr ` (df-tmrdbror) and the installation predicates of the sortie
(PREDS10, by t7b_a_defs) to the sortie file.

    MM_DB=sorties/t10.mm python3 tools/gen/t10_a_defs.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
import t7b_a_defs as AD

RBO_BLOCK = r'''
  $c TMrdBraOr $.
  $( Syntax: the peek handler ` readBraOr ` . $)
  ctmrdbror $a class TMrdBraOr $.
  ${
    $d v o $.
    $( Definition of the peek handler ` readBraOr ` .  Lean (TM/Lists.lean,
       ` peekBraOr ` ): ` peek x ( fun v o => { v with flag := v.flag || `
       ` decide (o = some Gamma'.bra) } ) ` , the letter ` bra ` being ` 2 ` ,
       ` some ` being ` inl ` and ` b || c ` being ` 1o ` exactly when one of
       them is ` 1o ` . $)
'''


def rbo():
    txt = open(AD.DBP).read()
    if 'df-tmrdbror $a' in txt:
        print('skip readBraOr'); return
    body = RBO_BLOCK + AD.wrap('df-tmrdbror $a |- %s $.' % DF_RBO, '    ') + '\n  $}\n'
    with open(AD.DBP, 'a') as fh:
        fh.write(body)
    print('appended readBraOr')


if __name__ == '__main__':
    rbo()
    AD.main(PREDS10)
