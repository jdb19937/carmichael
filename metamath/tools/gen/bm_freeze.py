"""Sortie BM freeze check: the matrix of `bmpig21` is carmsw.3's matrix verbatim (D := a, F := r),
LOGFREE / LOGGED are tools/zdilib.py's texts, and (after the proof) the database's `bmpig21`,
`bmpig21a` equal the frozen texts.

    MM_DB=sorties/bm.mm python3 tools/gen/bm_freeze.py check
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import bmlib
from bmlib import S, MATRIX, DA, DZ, F3160, PIG
import zdilib

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def carmsw3():
    txt = open(os.path.join(ROOT, 'carmichael.mm')).read()
    m = re.search(r'\scarmsw\.3 \$e \|- (.*?) \$\.', txt, re.S)
    f = ' '.join(m.group(1).split())
    assert f.startswith('( ph -> ') and f.endswith(' )')
    return f[len('( ph -> '):-2]


def check():
    mat = carmsw3()
    mine = MATRIX(DA, DZ, F3160)
    sub = ' '.join({'D': DA, 'F': DZ}.get(t, t) for t in mat.split())
    print('carmsw.3 matrix tokens:', len(mat.split()))
    print('matrix = carmsw.3 verbatim: %s' % ('yes' if sub == mine else 'NO'))
    if sub != mine:
        a, b = sub.split(), mine.split()
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                print('first difference at token %d: carmsw.3 %r, bmlib %r' % (i, x, y)); break
    ok = sub == mine
    lf = S['bmpig21'].startswith('( ( %s /\\ %s ) -> ' % (zdilib.LOGFREE, zdilib.LOGGED))
    print('LOGFREE, LOGGED = tools/zdilib.py verbatim: %s' % ('yes' if lf else 'NO'))
    ok = ok and lf
    print('bmpig21 = ( ( LOGFREE /\\ LOGGED ) -> E. %s e. NN0 E. %s e. NN0 MATRIX ): %s'
          % (DA, DZ, 'yes' if S['bmpig21'] == '( ( %s /\\ %s ) -> %s )' % (zdilib.LOGFREE, zdilib.LOGGED, PIG(F3160)) else 'NO'))
    for lab in ('bmpig21', 'bmpig21a'):
        try:
            db = bmlib.stmt(lab)
        except KeyError:
            print('%s: not in the database yet' % lab)
            continue
        same = db == S[lab]
        print('database %s = frozen text: %s' % (lab, 'yes' if same else 'NO'))
        ok = ok and same
    return ok


if __name__ == '__main__':
    if sys.argv[1:2] == ['check']:
        sys.exit(0 if check() else 1)
