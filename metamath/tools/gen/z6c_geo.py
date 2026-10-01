"""Sortie Z6c: z6geo, extracted from worksheets/z5fdetcvg.mmp (its first block, the geometric majorant),
with the antecedent reduced to X e. RR+.
Run: MM_DB=sorties/z6c.mm python3 tools/gen/z6c_geo.py"""
import sys, os, re
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
sys.path.insert(0, os.path.join(ROOT, 'tools'))
from z6clib import STATEMENTS
from tm import ws, add

AA = ('( ( ( ( A e. RR /\\ 0 < A ) /\\ ( B e. RR /\\ A < B ) ) /\\ ( X e. RR+ /\\ ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) ) ) /\\ '
      '( ( C : NN --> CC /\\ A. j e. NN ( abs ` ( C ` j ) ) <_ 1 ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) )')


def build():
    src = open(os.path.join(ROOT, 'worksheets', 'z5fdetcvg.mmp')).read().split('\n')
    out = []
    started = False
    for l in src:
        m = re.match(r'^([a-z]\d+):', l)
        if not m:
            continue
        lab = m.group(1)
        if lab == 's12':
            started = True
            out.append('s6::id |- ( X e. RR+ -> X e. RR+ )')
        if not started:
            continue
        out.append(l.replace(AA, 'X e. RR+'))
        if lab == 's128':
            break
    assert out[-1].startswith('s128:')
    out[-1] = 'qed' + out[-1][4:]
    f = out[-1].split('|-', 1)[1].strip()
    assert f == STATEMENTS['z6geo'], f
    return out


if __name__ == '__main__':
    lines = build()
    ws('z6geo', 'The geometric majorant of the detector series: ` sum_ m m q ^ m ` converges for ` q = e ^ ( -1 / X ) ` , ` X > 0 ` '
       '(~ geomulcvg , ~ iserex ; the first block of ~ z5fdetcvg ; Lean ` summable_pow_mul_geometric_of_norm_lt_one ` in ` summable_Sterm ` ).', lines)
    ok, msg = add('z6geo')
    print(('OK   ' if ok else 'FAIL ') + 'z6geo'); print(msg)
