"""Sortie LDEN freeze check: the headline statement (frozen in tools/ldenlib.py under the label
`loggeddensity`; the brief's `loggedDensity` is refused by `tools/mm.py axioms`, which enumerates
[0-9a-z]+ labels only) is tools/zdilib.py's LOGGED verbatim, the text worksheets/carmtm.mmp cites
under `loggedDensity` is the same, and (after the proofs) every LDEN statement in the database
equals its frozen text.

    MM_DB=sorties/lden.mm python3 tools/gen/lden_freeze.py          # before the first proof and after the last
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import ldenlib
from ldenlib import STATEMENTS, ORDER
import zdilib

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def main():
    ok = True
    same = STATEMENTS['loggeddensity'] == zdilib.LOGGED
    print('loggedDensity = LOGGED verbatim: %s' % ('yes' if same else 'NO'))
    print('label: loggeddensity (tools/mm.py axioms enumerates [0-9a-z]+ labels only; stage B cites it)')
    ok = ok and same
    p = os.path.join(ROOT, 'worksheets', 'carmtm.mmp')
    if os.path.exists(p):
        m = re.search(r'^s1::loggedDensity \|- (.*)$', open(p).read(), re.M)
        cited = ' '.join(m.group(1).split()) if m else None
        print('worksheets/carmtm.mmp cites LOGGED verbatim: %s' % ('yes' if cited == zdilib.LOGGED else 'NO'))
        ok = ok and cited == zdilib.LOGGED
    n = 0
    for lab in ORDER:
        try:
            db = ldenlib.dbstmt(lab)
        except KeyError:
            continue
        n += 1
        same = db == STATEMENTS[lab]
        if not same:
            print('database %s = frozen text: NO' % lab)
        ok = ok and same
    print('database statements checked against the frozen texts: %d of %d, all equal: %s' % (n, len(ORDER), 'yes' if ok else 'NO'))
    print('LDEN FREEZE %s' % ('OK' if ok else 'FAIL'))
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
