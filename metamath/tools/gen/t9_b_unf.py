"""T9: the unfolding theorems tmiprlu tmiextu tmiexsu tmiexpu tmiexbu tmiexgu tmiexfu (by t7b_b_unf).

    MM_DB=sorties/t9.mm python3 tools/gen/t9_b_unf.py NAME...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
import t7b_b_unf as UF

if __name__ == '__main__':
    for n in (sys.argv[1:] or PREDS9):
        UF.unf(n)
