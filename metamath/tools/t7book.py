"""T7: the frozen statements of the concrete composites and wrappers this
sortie books (blueprint section 8), produced by ` conc ` from the generic
theorems of the database.  Kept apart from tools/t7lib.py so that the
generators of the delivered theorems do not pay for reading the database."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t7lib import *

BOOKED = []


def book(label, tree, concl):
    BOOKED.append((label, statement(tree, concl)))


# (tmciz is delivered: its consumer form is in tools/t7lib.py)
