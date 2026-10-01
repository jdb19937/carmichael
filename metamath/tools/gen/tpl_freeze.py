"""T-PL: the frozen statements and their grammar check through mmj2
(T-MD's tmd_freeze.py).

    MM_DB=sorties/tpl.mm python3 tools/gen/tpl_freeze.py         # grammar check
    MM_DB=sorties/tpl.mm python3 tools/gen/tpl_freeze.py print   # the statements
    MM_DB=sorties/tpl.mm python3 tools/gen/tpl_freeze.py check   # every delivered theorem equals its frozen text
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *
import mm as _MM

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'tpl'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'tpl', 'tplgc.mmp')
    st = allstmts()
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=tplgc  LOC_AFTER=?\n\n* grammar check of the frozen statements of T-PL\n\n')
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


def delivered():
    """compare every theorem of the sortie file with its frozen text"""
    db = open(os.path.join(ROOT, os.environ.get('MM_DB', 'carmichael.mm'))).read()
    bad = 0
    for lab, s in allstmts():
        m = re.search(r'\n\s*%s \$p \|- (.*?) \$=' % re.escape(lab), db, re.S)
        if not m:
            print('NOT DELIVERED', lab); continue
        got = ' '.join(m.group(1).split())
        if got != s:
            bad += 1; print('DIFFERS', lab); print('  frozen:', s[:200]); print('  db    :', got[:200])
    print('%d delivered theorems differ from their frozen statements' % bad)


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab, s in allstmts():
            print('%s (%d tokens)\n%s\n' % (lab, len(s.split()), s))
    elif 'check' in sys.argv:
        delivered()
    else:
        t = check()
        if 'dump' in sys.argv:
            print(t[-6000:])
