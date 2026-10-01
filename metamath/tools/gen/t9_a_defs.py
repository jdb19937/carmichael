"""T9: append the installation predicates of the sortie to the sortie file:
TMIprl TMIext TMIexs TMIexp TMIexb TMIexg TMIexf (by t7b_a_defs).

    MM_DB=sorties/t9.mm python3 tools/gen/t9_a_defs.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
import t7b_a_defs as AD

if __name__ == '__main__':
    AD.main(PREDS9)
