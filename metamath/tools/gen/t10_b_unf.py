"""T10: the unfolding theorems tmiXXXu of the sortie's predicates (by t7b_b_unf).

    MM_DB=sorties/t10.mm python3 tools/gen/t10_b_unf.py [NAME...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t10lib import *
import t7b_b_unf as UF

if __name__ == '__main__':
    for n in (sys.argv[1:] or PREDS10):
        UF.unf(n)
