"""T8a: append the definitions of the sortie to the sortie file: the peek handlers
` readKet ` , ` readBlank ` , the word ` encSlots ` , and the installation
predicates TMImvs TMIcps TMIdpl TMIwup TMIwdn TMIetb (by t7b_a_defs).

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_a_defs.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
import t7b_a_defs as AD

HDR = r'''
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The concrete Table, part 1 (sortie T8a): the peek handlers readKet and
  readBlank, the word of a list of slots, and the installation predicates of
  moveSlot, copySlot, dropList, walkUp, walkDown, emptyTbl
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c TMrdKet TMrdBlank encSlots $.
  $( Syntax: the peek handler ` readKet ` . $)
  ctmrdket $a class TMrdKet $.
  $( Syntax: the peek handler ` readBlank ` . $)
  ctmrdblk $a class TMrdBlank $.
  $( Syntax: the word of a list of slots of the DP table. $)
  cencslots $a class encSlots $.

  ${
    $d v o $.
    $( Definition of the peek handler ` readKet ` .  Lean (TM/Table.lean):
       ` def readKet (v : St) (o : Option Gamma') : St := `
       ` { v with flag := decide (o = some Gamma'.ket) } ` , the letter
       ` ket ` being ` 3 ` and ` some ` being ` inl ` . $)
    df-tmrdket $a |- TMrdKet = ( v e. TMSt , o e. ( Gamma' |_| 1o ) |-> %s ) $.

    $( Definition of the peek handler ` readBlank ` .  Lean (TM/Table.lean):
       ` def readBlank (v : St) (o : Option Gamma') : St := `
       ` { v with flag := decide (o = some Gamma'.blank) } ` , the letter
       ` blank ` being ` 0 ` and ` some ` being ` inl ` . $)
    df-tmrdblk $a |- TMrdBlank = ( v e. TMSt , o e. ( Gamma' |_| 1o ) |-> %s ) $.
  $}

  $( Definition of the word of a list of slots of the DP table on a stack,
     head slot on top: the free-monoid sum of the slots' words ( ~ df-tm2encslot ).
     Lean (TM/Table.lean):
     ` def encSlots (sl : List (Option (List Nat))) : List Gamma' := `
     ` sl.flatMap encSlot ` . $)
  df-tm2encslots $a |- encSlots = ( l e. Word ( Word NN0 |_| 1o ) |-> ( (
    freeMnd ` Gamma' ) gsum ( encSlot o. l ) ) ) $.
'''


def main():
    txt = open(AD.DBP).read()
    if 'df-tmrdket $a' not in txt:
        body = HDR % (HVAL('v', 'o', KET), HVAL('v', 'o', BLANK))
        body = '\n'.join(AD.wrap(l.strip(), '    ') if l.startswith('    df-tmrd') else l for l in body.split('\n'))
        with open(AD.DBP, 'a') as fh:
            fh.write(body)
        print('appended handlers and encSlots')
    AD.main(PREDS)


if __name__ == '__main__':
    main()
