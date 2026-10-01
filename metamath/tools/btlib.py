"""Sortie BT helpers (BrunTitchmarsh.lean, the consumer form of
`brunTitchmarsh_progression`).

`bruntit` (V4b, merged) is Lean's `brunTitchmarsh_progression`.  STATEMENTS
freezes `bruntitex`, Lean's `BrunTitchmarsh` Prop (BMembership.lean 158) as
`brunTitchmarsh_holds` (BMembership21.lean 166) proves it: the threshold is
existential, `y0 := ( |^ ` ( exp ` 200000000 ) )`.
`MM_DB=sorties/bt.mm python3 tools/btlib.py` grammar-checks it with mmatch.
"""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import num

C2E8 = num.nat_text(200000000)
EXPK = '( exp ` %s )' % C2E8
Y0 = '( |^ ` %s )' % EXPK
Z2 = '( ZZ>= ` 2 )'
RPOW = '( y ^c ( ; 1 9 / ; 2 0 ) )'
CNT = '( # ` { i e. ( 0 ... y ) | ( i e. Prime /\\ ( i mod m ) = ( 1 mod m ) ) } )'
BND = '( ( 3 x. y ) / ( ( phi ` m ) x. ( log ` ( y / m ) ) ) )'


def body(t):
    """the matrix of BrunTitchmarsh at threshold t"""
    return 'A. y e. NN0 A. m e. %s ( ( %s <_ y /\\ m <_ %s ) -> %s <_ %s )' % (Z2, t, RPOW, CNT, BND)


STATEMENTS = {}
STATEMENTS['bruntitex'] = 'E. t e. NN0 %s' % body('t')


def gramcheck(labels):
    out = {}
    for lab in labels:
        f = STATEMENTS[lab]
        path = 'worksheets/btgc%s.mmp' % lab
        with open(path, 'w') as fh:
            fh.write('$( <MM> <PROOF_ASST> THEOREM=btgc%s  LOC_AFTER=?\n\n* gc\n\n'
                     'h1::btgc%s.1 |- %s\nqed:1:idi |- %s\n$)\n' % (lab, lab, f, f))
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run(['python3', 'tools/mm.py', 'unify', path], capture_output=True, text=True, env=env)
        out[lab] = 'UNIFY OK' in r.stdout
        if out[lab]:
            os.remove(path)
        else:
            print(r.stdout[-1500:], r.stderr[-800:])
    return out


if __name__ == '__main__':
    print(gramcheck(sys.argv[1:] or list(STATEMENTS)))
