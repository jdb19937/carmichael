"""T-MD: the frozen statements and their grammar check through mmj2
(T5b's t5b_freeze.py).

    MM_DB=sorties/tmd.mm python3 tools/gen/tmd_freeze.py         # grammar check
    MM_DB=sorties/tmd.mm python3 tools/gen/tmd_freeze.py print   # the statements
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
import mm as _MM

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def allstmts():
    out = [(l, s) for l, s in NSTMTS]
    out += [(l, statement(t, c)) for l, t, c in STATEMENTS]
    out += [(l, s) for l, s in STMTS_TMD.items()]
    return out


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'tmd'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'tmd', 'tmdgc.mmp')
    st = allstmts()
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=tmdgc  LOC_AFTER=?\n\n* grammar check of the frozen statements of T-MD\n\n')
        for i, (lab, s) in enumerate(st, 1):
            f.write('%d:: |- %s\n' % (i, s))
        f.write('qed:: |- ( 1 = 1 -> 1 = 1 )\n$)\n')
    ok, text = _MM.run_mmj2(path)
    errs = re.findall(r'Step (\d+)[^\n]*grammatical', text)
    for e in errs:
        print('GRAMMAR ERROR in', st[int(e) - 1][0])
    if not errs:
        print('grammar OK for %d statements' % len(st))
    return text


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab, s in allstmts():
            print('%s (%d tokens)\n%s\n' % (lab, len(s.split()), s))
    else:
        t = check()
        if 'dump' in sys.argv:
            print(t[-6000:])
