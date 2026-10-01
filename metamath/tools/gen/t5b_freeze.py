"""T5b: the frozen statements, and a grammar check of every one of them
through mmj2 (one worksheet whose steps are the statements; parse errors are
reported per step, unification is not attempted).

    MM_DB=sorties/t5b.mm python3 tools/gen/t5b_freeze.py         # grammar check
    MM_DB=sorties/t5b.mm python3 tools/gen/t5b_freeze.py print   # the statements
    MM_DB=sorties/t5b.mm python3 tools/gen/t5b_freeze.py parts   # the derived pieces
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5blib import *
import mm as _MM

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 't5bgc'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 't5bgc', 't5bgc.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=t5bgc  LOC_AFTER=?\n\n* grammar check of the frozen statements of T5b\n\n')
        for i, (lab, tree, concl) in enumerate(STATEMENTS, 1):
            f.write('%d:: |- %s\n' % (i, statement(tree, concl)))
        f.write('qed:: |- ( 1 = 1 -> 1 = 1 )\n$)\n')
    ok, text = _MM.run_mmj2(path)
    errs = re.findall(r'Step (\d+)[^\n]*grammatical', text)
    for e in errs:
        print('GRAMMAR ERROR in', STATEMENTS[int(e) - 1][0])
    if not errs:
        print('grammar OK for %d statements' % len(STATEMENTS))
    return text


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab, tree, concl in STATEMENTS:
            s = statement(tree, concl)
            print('%s (%d tokens, %d conjuncts)\n%s\n' % (lab, len(s.split()), len(flat(tree)), s))
    elif 'parts' in sys.argv:
        for name in ('STM_IP', 'STM_IL', 'STM_IM', 'HC1', 'HC2', 'HE2', 'DISJ_INC1', 'STM_PP', 'STM_PL', 'STM_PM',
                     'HCP', 'HCMVP', 'HEMVP', 'DISJ_PRD1', 'STM_ZP', 'STM_ZM', 'STM_Z3', 'STM_Z4', 'STM_ZS',
                     'HCMVZ', 'HEMVZ', 'HLDZ', 'HCZSZ', 'HEZSZ', 'HCMVZP', 'HEMVZP', 'HLDZP', 'HCZSZP', 'HEZSZP'):
            print('%s = %s\n' % (name, globals()[name]))
    else:
        t = check()
        if 'dump' in sys.argv:
            print(t[-6000:])
