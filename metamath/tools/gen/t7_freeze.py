"""T7: the frozen statements and their grammar check through mmj2 (T-MD's
tmd_freeze.py).

    MM_DB=sorties/t7.mm python3 tools/gen/t7_freeze.py         # grammar check
    MM_DB=sorties/t7.mm python3 tools/gen/t7_freeze.py print   # the statements
    MM_DB=sorties/t7.mm python3 tools/gen/t7_freeze.py check LABEL...   # compare with the database
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
import t7book
import t7mul
import t7sub
import t7cmp
import t7inc
import t7prd
import t7leb
import mm as _MM

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def allstmts():
    return list(STMTS7) + list(t7book.BOOKED)


def check(sel=None):
    os.makedirs(os.path.join(ROOT, 'scratch', 't7'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 't7', 't7gc.mmp')
    st = [(l, s) for l, s in allstmts() if not sel or l in sel]
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=t7gc  LOC_AFTER=?\n\n* grammar check of the frozen statements of T7\n\n')
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


def compare(labels):
    """the database statement against the frozen one"""
    d = dict(allstmts())
    for l in labels:
        try:
            db = stmt(l)
        except KeyError:
            print('%s: not in the database' % l); continue
        print('%s: %s' % (l, 'EQUAL' if db == d[l] else 'DIFFERS'))
        if db != d[l]:
            print('  db: ' + db[:400]); print('  fz: ' + d[l][:400])


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab, s in allstmts():
            print('%s (%d tokens)\n%s\n' % (lab, len(s.split()), s))
    elif 'check' in sys.argv:
        compare(sys.argv[sys.argv.index('check') + 1:])
    else:
        t = check([a for a in sys.argv[1:] if a != 'dump'])
        if 'dump' in sys.argv:
            print(t[-6000:])
