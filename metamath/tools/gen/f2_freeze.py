"""Sortie F2 freeze check: every F2 statement (frozen in tools/f2lib.py) against the database,
and f2lgd against ( LOGGED -> carmtm ) assembled from tools/zdilib.py and scratch/carmtm.mmp.

    MM_DB=sorties/f2.mm python3 tools/gen/f2_freeze.py          # before the first proof and after the last
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import f2lib
from f2lib import S, ORDER, CARMTM, MATA
import zdilib, bmlib

DB = os.environ.get('MM_DB', 'carmichael.mm')


def main():
    ok = True
    target = '( %s -> %s )' % (zdilib.LOGGED, CARMTM)
    same = S['f2lgd'] == target
    print('f2lgd = ( LOGGED -> carmtm ) verbatim: %s' % ('yes' if same else 'NO'))
    ok = ok and same
    print('carmtm frozen text: %d tokens (scratch/carmtm.mmp); LOGGED: %d tokens (tools/zdilib.py)'
          % (len(CARMTM.split()), len(zdilib.LOGGED.split())))
    # f2rex's antecedent is bmpig21's consequent (BM's frozen text, = carmsw.3's matrix at D := a, F := r)
    pig = '( ( %s /\\ %s ) -> E. a e. NN0 E. r e. NN0 %s )' % (zdilib.LOGFREE, zdilib.LOGGED, MATA)
    same = bmlib.S['bmpig21'] == pig and S['f2rex'] == '( E. a e. NN0 E. r e. NN0 %s -> %s )' % (MATA, CARMTM)
    print('f2rex antecedent = bmpig21 consequent (bmlib frozen text): %s' % ('yes' if same else 'NO'))
    ok = ok and same
    same = f2lib.stmt('bmpig21') == bmlib.S['bmpig21'] and f2lib.stmt('zd2lfl') == '( %s -> %s )' % (zdilib.LOGGED, zdilib.LOGFREE)
    print('database bmpig21 = bmlib frozen text, zd2lfl = ( LOGGED -> LOGFREE ): %s' % ('yes' if same else 'NO'))
    ok = ok and same
    # f2cw is carmtmw's conclusion at ph := ( s e. NN0 /\ r e. NN0 /\ MATRIX' ) with carmsw.3's matrix renamed
    hy = f2lib.hyps('carmtmw')
    mat3 = hy[2][len('( ph -> '):-2] if len(hy) == 3 else ''
    sub = ' '.join({'D': f2lib.DS, 'F': f2lib.DZ}.get(t, t) for t in mat3.split())
    same = f2lib.ren(sub) == f2lib.MATP and f2lib.stmt('carmtmw') == '( ph -> %s )' % CARMTM
    print('f2cw antecedent = carmtmw.3 at D := s, F := r with k m q -> g j o; carmtmw = ( ph -> carmtm ): %s'
          % ('yes' if same else 'NO'))
    ok = ok and same
    for lab in ORDER + ['carmtm']:
        try:
            db = f2lib.stmt(lab, dbs=(DB,) if lab != 'carmtm' else (DB, 'carmichael.mm'))
        except KeyError:
            print('database %s: not in %s yet' % (lab, DB))
            continue
        same = db == S[lab]
        print('database %s = frozen text: %s' % (lab, 'yes' if same else 'NO'))
        ok = ok and same
    try:
        ld = f2lib.stmt('loggeddensity', dbs=(DB, 'carmichael.mm'))
        print('loggeddensity = LOGGED verbatim: %s' % ('yes' if ld == zdilib.LOGGED else 'NO'))
    except KeyError:
        print('loggeddensity: not in the database (stage B waits for LDEN)')
    print('F2 FREEZE %s' % ('OK' if ok else 'FAIL'))
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
