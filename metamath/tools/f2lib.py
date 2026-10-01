"""Sortie F2 (M-FINAL, stage A): the frozen statements of `f2alpha`, `f2cw`, `f2rex`, `f2lgd`
and the recipe for stage B's `carmtm`.

    python3 tools/f2lib.py print                                   # the frozen table
    MM_DB=sorties/f2.mm python3 tools/f2lib.py check [LABEL...]    # grammar check (mmatch)
    MM_DB=sorties/f2.mm python3 tools/gen/f2_freeze.py             # f2lgd = ( LOGGED -> carmtm ) verbatim

Letters.  `carmtm` (scratch/carmtm.mmp) binds f h c m n e i a; `carmtmw` carries the mandatory
`$d ph e i k m n q` and `$d D k l m n q x`, `$d F k l m n q x`.  BM's `bmpig21` puts the AGP 3.1
matrix (carmsw.3's, letters x l q p k d m) under `E. a e. NN0 E. r e. NN0`; `a` is bound in `carmtm`,
so `rexlimivv` ($d a carmtm) cannot eliminate it: the outer existential is renamed `a -> s` once
(`f2rex`, cbvrexvw).  The matrix's bound `k m q` meet `$d ph k m q`, so `carmtmw`'s `ph` holds the
matrix with `k m q -> g j o` (`f2alpha` is the closed alpha-equivalence back).  `s g j o` are outside
e i k m n q (carmtmw's ph frame), outside x l p d r (the matrix), outside f h c m n e i a (carmtm),
and o is outside cbvsumv's f m n x.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from zdilib import LOGFREE, LOGGED
from bmlib import MATRIX, DA, DZ, F3160, PIG, ANTE, CONS, BOUND, PSET, DIV, CNT, XB, X1B, XH, PF, PCOND

ROOT = os.path.join(HERE, '..')

DS = 's'                       # carmsw's D in F2 (BM's `a` is bound in carmtm)
RN = {'k': 'g', 'm': 'j', 'q': 'o'}   # the matrix's bound letters inside carmtmw's ph


def ren(text, m=RN):
    return ' '.join(m.get(t, t) for t in text.split())


def carmtm():
    """the frozen text of carmtm (scratch/carmtm.mmp), without |-"""
    frozen = open(os.path.join(ROOT, 'scratch', 'carmtm.mmp')).read()
    q = ' '.join(frozen[frozen.index('qed::') + 5:].split('$)')[0].split())
    assert q.startswith('|- ')
    return q[3:]


CARMTM = carmtm()
MATA = MATRIX(DA, DZ, F3160)          # bmpig21's matrix (D := a, F := r)
MAT = MATRIX(DS, DZ, F3160)           # the same at D := s
MATP = ren(MAT)                       # k m q -> g j o
PH = '( %s e. NN0 /\\ %s e. NN0 /\\ %s )' % (DS, DZ, MATP)

S = {}
S['f2alpha'] = '( %s <-> %s )' % (MATP, MAT)
S['f2cw'] = '( %s -> %s )' % (PH, CARMTM)
S['f2rex'] = '( E. %s e. NN0 E. %s e. NN0 %s -> %s )' % (DA, DZ, MATA, CARMTM)
S['f2lgd'] = '( %s -> %s )' % (LOGGED, CARMTM)
S['carmtm'] = CARMTM                  # stage B (after LDEN merges): ax-mp from loggedDensity and f2lgd
ORDER = ['f2alpha', 'f2cw', 'f2rex', 'f2lgd']


def stmt(label, dbs=('sorties/f2.mm', 'carmichael.mm')):
    """the assertion of LABEL from the sortie file or carmichael.mm, without |-"""
    for fn in dbs:
        p = os.path.join(ROOT, fn)
        if not os.path.exists(p):
            continue
        txt = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def hyps(label, fn='carmichael.mm'):
    """the $e hypotheses of LABEL in declared order, without |-"""
    txt = open(os.path.join(ROOT, fn)).read()
    d = {int(m.group(1)): ' '.join(m.group(2).split())
         for m in re.finditer(r'\b%s\.(\d+) \$e \|- (.*?) \$\.' % re.escape(label), txt, re.S)}
    return [d[k] for k in sorted(d)]


def check(labels):
    d = os.path.join(ROOT, 'scratch', 'f2gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'f2gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=f2gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h99::f2gc%s.99 |- %s\n' % (lab, S[lab]))
            f.write('qed:h99:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=ROOT,
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))
    return bad == 0


if __name__ == '__main__':
    if sys.argv[1:2] == ['print']:
        for k in ORDER + ['carmtm']:
            print(k, S[k]); print()
    elif sys.argv[1:2] == ['check']:
        sys.exit(0 if check(sys.argv[2:] or ORDER + ['carmtm']) else 1)
