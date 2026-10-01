"""T12: append the installation predicates of the sortie (PREDS12, by t7b_a_defs) to the sortie file.

    MM_DB=sorties/t12.mm python3 tools/gen/t12_a_defs.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
import t7b_a_defs as AD

if __name__ == '__main__':
    AD.main(sys.argv[1:] or PREDS12)
