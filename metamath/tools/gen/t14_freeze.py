"""T14: the statements of the sortie and their check against the database.

    MM_DB=sorties/t14.mm python3 tools/gen/t14_freeze.py         # grammar check of every statement
    MM_DB=sorties/t14.mm python3 tools/gen/t14_freeze.py print   # the statements
    MM_DB=sorties/t14.mm python3 tools/gen/t14_freeze.py check   # every delivered theorem equals its registered text
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
_args = sys.argv[1:]; sys.argv = sys.argv[:1]
from t14lib import STMTS14, ORDER14
import mm as _MM

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def text(lab):
    s = STMTS14[lab]
    return s if isinstance(s, str) else s[1]


def check_grammar():
    os.makedirs(os.path.join(ROOT, 'scratch', 't14'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 't14', 't14gc.mmp')
    items = []
    for lab in ORDER14:
        s = STMTS14[lab]
        if isinstance(s, str):
            items.append((lab, s))
        else:
            for h in s[0]:
                items.append((lab + ' (hyp)', h))
            items.append((lab, s[1]))
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=t14gc  LOC_AFTER=?\n\n* grammar check of the statements of T14\n\n')
        for i, (lab, s) in enumerate(items, 1):
            f.write('%d:: |- %s\n' % (i, s))
        f.write('qed:: |- ( 1 = 1 -> 1 = 1 )\n$)\n')
    ok, out = _MM.run_mmj2(path)
    errs = re.findall(r'E-PA-\d+ Theorem t14gc Step (\d+):', out)
    errs += re.findall(r'Step (\d+)[^\n]*grammatical', out)
    for e in sorted(set(errs)):
        print('GRAMMAR ERROR in', items[int(e) - 1][0])
    if not errs:
        print('grammar OK for %d formulas (%d statements)' % (len(items), len(ORDER14)))


def delivered():
    db = open(os.path.join(ROOT, os.environ.get('MM_DB', 'carmichael.mm'))).read()
    bad = 0; n = 0
    for lab in ORDER14:
        m = re.search(r'\n\s*%s \$p \|- (.*?) \$=' % re.escape(lab), db, re.S)
        if not m:
            print('NOT DELIVERED', lab); continue
        n += 1
        got = ' '.join(m.group(1).split())
        if got != text(lab):
            bad += 1; print('DIFFERS', lab); print('  registered:', text(lab)[:200]); print('  db        :', got[:200])
        s = STMTS14[lab]
        if not isinstance(s, str):
            for i, h in enumerate(s[0], 1):
                mh = re.search(r'\n\s*%s\.%d \$e \|- (.*?) \$\.' % (re.escape(lab), i), db, re.S)
                if not mh or ' '.join(mh.group(1).split()) != h:
                    bad += 1; print('HYP DIFFERS', lab, i)
    print('%d delivered theorems differ from their registered statements; %d of %d statements delivered'
          % (bad, n, len(ORDER14)))


if __name__ == '__main__':
    if 'print' in _args:
        for lab in ORDER14:
            s = STMTS14[lab]
            if isinstance(s, str):
                print('%s\n  %s\n' % (lab, s))
            else:
                for i, h in enumerate(s[0], 1):
                    print('%s.%d $e %s' % (lab, i, h))
                print('%s\n  %s\n' % (lab, s[1]))
    elif 'check' in _args:
        delivered()
    else:
        check_grammar()
