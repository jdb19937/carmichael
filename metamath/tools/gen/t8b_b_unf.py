"""T8b: the unfolding theorems tmisinu tmilksu tmictbu tmimeu tmirstu tmidpbu tmidpsu (by t7b_b_unf).

    MM_DB=sorties/t8b.mm python3 tools/gen/t8b_b_unf.py NAME...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8blib import *
import t7b_b_unf as UF

if __name__ == '__main__':
    for n in (sys.argv[1:] or PREDS8B):
        UF.unf(n)
