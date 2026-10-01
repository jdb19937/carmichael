"""T8a: the frozen statements and their grammar check through mmj2
(T-MD's tmd_freeze.py).

    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_freeze.py         # grammar check
    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_freeze.py print   # the statements
    MM_DB=sorties/t8a.mm python3 tools/gen/t8a_freeze.py check   # every delivered theorem equals its frozen text
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t8alib import *
import mm as _MM

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 't8a'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 't8a', 't8agc.mmp')
    st = allstmts()
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=t8agc  LOC_AFTER=?\n\n* grammar check of the frozen statements of T8a\n\n')
        for i, (lab, s) in enumerate(st, 1):
            f.write('%d:: |- %s\n' % (i, s))
        f.write('qed:: |- ( 1 = 1 -> 1 = 1 )\n$)\n')
    ok, text = _MM.run_mmj2(path)
    errs = re.findall(r'Step (\d+)[^\n]*grammatical', text)
    errs += re.findall(r'E-PA-\d+ Theorem t8agc Step (\d+):', text)
    for e in errs:
        print('GRAMMAR ERROR in', st[int(e) - 1][0] if e.isdigit() and int(e) <= len(st) else e)
    if 'E-' in text and not errs:
        errs = ['?']; print('mmj2 error:', [l for l in text.split('\n') if 'E-' in l][:5])
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
