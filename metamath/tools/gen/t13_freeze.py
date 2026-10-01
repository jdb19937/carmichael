"""T13: the statements of the sortie and their check against the database (T12's t12_freeze.py).

    MM_DB=sorties/t13.mm python3 tools/gen/t13_freeze.py         # grammar check of every statement through mmj2
    MM_DB=sorties/t13.mm python3 tools/gen/t13_freeze.py print   # the statements
    MM_DB=sorties/t13.mm python3 tools/gen/t13_freeze.py check   # every delivered theorem equals its registered text
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.argv, _args = sys.argv[:1], sys.argv[1:]
from t13lib import *
for _m in ('t13_a_pos', 't13_b_help', 't13_c_u0', 't13_e_bnd', 't13_f_stage', 't13_g_fin'):
    __import__(_m)
import mm as _MM
sys.argv += _args

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RUN = ['tmisrc4v', 'tmisrc4o', 'tmisrc3x', 'tmisrc2s', 'tmisrczs']          # registered from the Run: read from the database


def all_labels():
    return ORDER13 + [l for l in RUN if l not in ORDER13]


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 't13'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 't13', 't13gc.mmp')
    st = allstmts13()
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=t13gc  LOC_AFTER=?\n\n* grammar check of the statements of T13\n\n')
        for i, (lab, s) in enumerate(st, 1):
            f.write('%d:: |- %s\n' % (i, s))
        f.write('qed:: |- ( 1 = 1 -> 1 = 1 )\n$)\n')
    ok, text = _MM.run_mmj2(path)
    errs = re.findall(r'Step (\d+)[^\n]*grammatical', text)
    errs += re.findall(r'E-PA-\d+ Theorem t13gc Step (\d+):', text)
    for e in errs:
        print('GRAMMAR ERROR in', st[int(e) - 1][0] if e.isdigit() and int(e) <= len(st) else e)
    if 'E-' in text and not errs:
        errs = ['?']; print('mmj2 error:', [l for l in text.split('\n') if 'E-' in l][:5])
    if not errs:
        print('grammar OK for %d statements' % len(st))
    return text


def delivered():
    db = open(os.path.join(ROOT, os.environ.get('MM_DB', 'carmichael.mm'))).read()
    bad = 0
    for lab, s in allstmts13():
        m = re.search(r'\n\s*%s \$p \|- (.*?) \$=' % re.escape(lab), db, re.S)
        if not m:
            print('NOT DELIVERED', lab); continue
        got = ' '.join(m.group(1).split())
        if got != s:
            bad += 1; print('DIFFERS', lab); print('  registered:', s[:200]); print('  db        :', got[:200])
    print('%d delivered theorems differ from their registered statements; %d statements checked' % (bad, len(allstmts13())))
    for lab in RUN:
        if not re.search(r'\n\s*%s \$p ' % re.escape(lab), db):
            print('NOT DELIVERED', lab)


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab, s in allstmts13():
            print('%s (%d tokens)\n%s\n' % (lab, len(s.split()), s))
    elif 'check' in sys.argv:
        delivered()
    else:
        check()
