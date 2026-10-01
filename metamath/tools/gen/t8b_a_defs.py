"""T8b: append the installation predicates of the sortie to the sortie file:
TMIsin TMIlks TMIctb TMIme TMIrst TMIdpb TMIdps (by t7b_a_defs).

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_a_defs.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
import t7b_a_defs as AD

HDR = r'''
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The concrete Table, part 2 (sortie T8b): the installation predicates of
  setIfNoneF, lookupSlot, copyTbl, moveEntry, resStep, dpBodyF, dpStepF
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
'''


def main():
    txt = open(AD.DBP).read()
    if 'sortie T8b): the installation' not in txt:
        with open(AD.DBP, 'a') as fh:
            fh.write(HDR)
    AD.main(PREDS8B)


if __name__ == '__main__':
    main()
