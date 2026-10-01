"""EF56 frozen-statement table: python3 tools/gen/ef56_main.py print | check [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
import ef56lib as L
if 'print' in sys.argv:
    for lab in L.S:
        print('| `%s` | `%s` |' % (lab, L.S[lab]))
elif 'check' in sys.argv:
    L.check([a for a in sys.argv[2:]] or list(L.S))
