"""Sortie Z5d helpers (Route Z: Detection.lean).

STATEMENTS / HYPS are the frozen statements of Z5d-blueprint.md, one place,
so that the blueprint, the grammar check and the generators cannot drift apart.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5clib import *          # z5c/z5b/z5a/zd1 macros, W, mkst, sy, mpv, litr, litle, dfacts, ...
from z5clib import STATEMENTS as Z5CS
from c0lib import hyp

# ---- section G: the Gamma strip bound I8(b)
RZ = '( Re ` Z )'
AIZ = '( abs ` ( Im ` Z ) )'
STRIP = '( 0 <_ %s /\\ %s <_ 1 )' % (RZ, RZ)
EUTM = lambda m, Z='Z': '( ( ( ( %s + 1 ) / %s ) ^c %s ) / ( ( %s / %s ) + 1 ) )' % (m, m, Z, Z, m)    # gamcvg2's factor
RAT = lambda m: '( ( %s + %s ) / ( abs ` ( Z + %s ) ) )' % (m, RZ, m)                                  # ( m + Re z ) / | z + m |
QK = lambda k, N='N': '( ( %s + 1 ) / ( ( %s + 1 ) + %s ) )' % (k, k, N)
BCL = lambda N='N': '( ( ( 4 ^ %s ) x. ( ( 2 x. %s ) + 1 ) ) / ( %s x. ( %s + 1 ) ) )' % (N, N, N, N)
BC21 = lambda N='N': '( ( ( 2 x. %s ) + 1 ) _C %s )' % (N, N)
E60 = lambda U: '( ; 6 0 x. ( exp ` -u %s ) )' % U
GAMH60 = GAMH.replace('( K x. ', '( ; 6 0 x. ')

# ---- section P: I9(b)
CS = lambda K, W: '{ x e. ( 1 ... %s ) | ( x gcd %s ) = 1 }' % (W, K)
KS = lambda t: 'sup ( { k e. NN | ( k ^ 2 ) || %s } , RR , < )' % t
P1 = lambda N, R: 'sum_ r e. ( %s RSet %s ) ( 1 / r )' % (N, R)

# ---- section Q: Q_R
QSQ = lambda N='N', R='R': '{ q e. Prime | ( q || %s /\\ q <_ %s ) }' % (N, R)
QSU = lambda N='N', R='R': '{ u e. Prime | ( u || %s /\\ u <_ %s ) }' % (N, R)
QRP = lambda N='N', R='R': 'prod_ p e. %s ( 1 - ( 1 / p ) )' % QSQ(N, R)          # QR N R (ZD1's form)
QRN = lambda N='N', R='R': 'prod_ w e. %s w' % QSU(N, R)                          # qR N R
MERT = lambda R='R': 'prod_ p e. ( ( 1 ... ( |_ ` %s ) ) i^i Prime ) ( 1 / ( 1 - ( 1 / p ) ) )' % R   # MertensProd R (zdmert's form)

LAM60 = LAM0.replace('x. K ) )', 'x. ; 6 0 ) )')
PRN_ = PRIN('N')

STATEMENTS = {
    # section G: I8(b)
    'z5dbern': '( ( ( A e. RR /\\ 1 <_ A ) /\\ ( X e. RR /\\ ( 0 <_ X /\\ X <_ 1 ) ) ) -> ( A ^c X ) <_ ( 1 + ( X x. ( A - 1 ) ) ) )',
    'z5deutb': '( ( ( Z e. CC /\\ %s ) /\\ M e. NN ) -> ( abs ` %s ) <_ %s )' % (STRIP, EUTM('M'), RAT('M')),
    'z5dgzp': ('( ( ( Z e. ( CC \\ ( ZZ \\ NN ) ) /\\ %s ) /\\ M e. NN0 ) -> ( abs ` ( ( _G ` Z ) x. Z ) ) <_ prod_ k e. ( 1 ... M ) %s )'
               % (STRIP, RAT('k'))),
    'z5dfac': ('( ( ( Z e. CC /\\ %s ) /\\ ( N e. NN0 /\\ N <_ %s ) /\\ M e. NN ) -> ( %s ^ 2 ) <_ ( 2 x. ( %s ^ 2 ) ) )'
               % (STRIP, AIZ, RAT('M'), QK('M'))),
    'z5dqnid': '( N e. NN0 -> prod_ k e. ( 1 ... N ) %s = ( ( N + 1 ) / %s ) )' % (QK('k'), BC21()),
    'z5dbcl': '( N e. ( ZZ>= ` 4 ) -> %s <_ %s )' % (BCL(), BC21()),
    'z5dgnum': ('( ( ( N e. ( ZZ>= ` 4 ) /\\ ( U e. RR /\\ N <_ U /\\ U < ( N + 1 ) ) ) /\\ ( ( G e. RR /\\ 0 <_ G ) /\\ ( C e. RR /\\ %s <_ C ) ) /\\ '
                '( ( G ^ 2 ) x. ( U ^ 2 ) ) <_ ( ( 2 ^ N ) x. ( ( ( N + 1 ) / C ) ^ 2 ) ) ) -> G <_ %s )' % (BCL(), E60('U'))),
    'z5dgsm': '( ( ( U e. RR /\\ ( 1 / 2 ) <_ U /\\ U < 4 ) /\\ ( G e. RR /\\ 0 <_ G ) /\\ ( G x. U ) <_ 1 ) -> G <_ %s )' % E60('U'),
    'z5dgam': ('( ( Z e. CC /\\ ( 0 <_ %s /\\ %s <_ 1 /\\ ( 1 / 2 ) <_ %s ) ) -> ( abs ` ( _G ` Z ) ) <_ %s )'
               % (RZ, RZ, AIZ, E60(AIZ))),
    'z5dgamh': GAMH60,
    'z5dlog2': '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )',
    # section P: I9(b)
    'z5dsqp': '( T e. NN -> ( ( %s e. NN /\\ ( %s ^ 2 ) || T ) /\\ ( mmu ` ( T / ( %s ^ 2 ) ) ) =/= 0 ) )' % (KS('T'), KS('T'), KS('T')),
    'z5dinvsq': '( W e. NN0 -> sum_ k e. ( 1 ... W ) ( 1 / ( k ^ 2 ) ) <_ 2 )',
    'z5dhk': '( ( K e. NN /\\ W e. NN ) -> sum_ m e. ( 1 ... W ) ( 1 / m ) <_ ( ( K / ( phi ` K ) ) x. sum_ j e. %s ( 1 / j ) ) )' % CS('K', 'W'),
    'z5dcs2': '( ( K e. NN /\\ W e. NN ) -> sum_ j e. %s ( 1 / j ) <_ ( 2 x. %s ) )' % (CS('K', 'W'), P1('K', 'W')),
    'z5dp1k': '( ( K e. NN /\\ R e. RR+ ) -> ( ( ( 1 / 2 ) x. ( ( phi ` K ) / K ) ) x. ( log ` R ) ) <_ %s )' % P1('K', 'R'),
    'z5dp1low': '( ( N e. NN /\\ D e. RR+ ) -> ( ( ( 1 / ; ; 2 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ %s )' % P1D,
    # section Q: Q_R
    'z5dqr': ('( N e. NN -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ ( { q e. Prime | q || %s } = %s /\\ ( ( phi ` %s ) / %s ) = %s ) ) )'
              % (QRN(), QRN(), QRN(), QSQ(), QRN(), QRN(), QRP())),
    'z5dqrset': '( ( N e. NN /\\ R e. RR ) -> ( %s RSet R ) = ( N RSet R ) )' % QRN(),
    'z5dtotqr': '( N e. NN -> ( ( phi ` N ) / N ) <_ %s )' % QRP(),
    'z5dp1qr': '( ( N e. NN /\\ R e. RR+ ) -> ( ( ( 1 / 2 ) x. %s ) x. ( log ` R ) ) <_ %s )' % (QRP(), P1('N', 'R')),
    'z5dp1qrd': '( ( N e. NN /\\ D e. RR+ ) -> ( ( ( 1 / ; ; 2 0 0 ) x. %s ) x. ( log ` D ) ) <_ %s )' % (QRP('N', RPD), P1D),
    'z5dp1mert': '( ( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) ) -> %s <_ ( %s x. %s ) )' % (P1('N', 'R'), QRP(), MERT()),
}

# ---- section U: Proposition 4.4 unconditional (the frozen Z6c statement, hdet aside)
A1D = ('( ( %s /\\ N e. NN ) /\\ ( ( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) ) /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) )' % HZD3)
HGAM60 = '( C = %s -> %s <_ ( abs ` ( Im ` S ) ) )' % (PRN_, LAM60)
CONC = '( ( ( 1 / ; ; 4 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ ( abs ` F )'
STATEMENTS['z5ddlb1'] = '( ( %s /\\ ( ( C : NN --> CC /\\ %s ) /\\ ( F e. CC /\\ ( %s /\\ %s ) ) ) ) -> %s )' % (A1D, HGAM60, HP1_, HDET_, CONC)
STATEMENTS['z5ddlb'] = '( ( %s /\\ ( ( C : NN --> CC /\\ %s ) /\\ ( F e. CC /\\ %s ) ) ) -> %s )' % (A1D, HGAM60, HDET_, CONC)

HYPS = {}

# the linear core of z5dgnum, on class variables (a lemma added during the sortie: the worksheet of z5dgnum passed 5,000 steps)
GLV = ['A', 'B', 'C', 'D', 'E', 'F', 'T', 'H', 'S', 'N', 'U']
HYPS['z5dglin'] = [('1', '( ph -> ( ( 2 x. A ) + ( 2 x. B ) ) <_ ( ( N x. T ) + ( 2 x. ( D - ( ( ( N x. ( 2 x. T ) ) + E ) - ( C + D ) ) ) ) ) )'),
                   ('2', '( ph -> C <_ B )'),
                   ('3', '( ph -> ( T + ( 2 x. D ) ) <_ ( F + E ) )'),
                   ('4', '( ph -> ( ( 2 x. ( F - ( 4 x. T ) ) ) - T ) <_ ( ( N + 2 ) / ; 1 6 ) )'),
                   ('5', '( ph -> ( N x. ( ; 5 6 / ; 8 1 ) ) <_ ( N x. T ) )'),
                   ('6', '( ph -> U < ( N + 1 ) )'),
                   ('7', '( ph -> T < ( ; ; 2 5 3 / ; ; 3 6 5 ) )'),
                   ('8', '( ph -> ( T + ( 3 x. H ) ) <_ S )'),
                   ('9', '( ph -> 1 <_ H )'),
                   ('10', '( ph -> 0 <_ N )')] + [('%d' % (11 + i), '( ph -> %s e. RR )' % v) for i, v in enumerate(GLV)]
STATEMENTS['z5dglin'] = '( ph -> ( A + U ) <_ S )'

ORDER = ['z5dbern', 'z5deutb', 'z5dgzp', 'z5dfac', 'z5dqnid', 'z5dbcl', 'z5dlog2', 'z5dglin', 'z5dgnum', 'z5dgsm', 'z5dgam', 'z5dgamh',
         'z5dsqp', 'z5dinvsq', 'z5dhk', 'z5dcs2', 'z5dp1k', 'z5dp1low',
         'z5dqr', 'z5dqrset', 'z5dtotqr', 'z5dp1qr', 'z5dp1qrd', 'z5dp1mert',
         'z5ddlb1', 'z5ddlb']


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('z5dg' + lab, 'grammar check of %s' % lab)
        for n, f in HYPS.get(lab, []):
            hyp(w, n, '%s.%s' % (lab, n), f)
        w.lines.append('qed:?:? |- %s' % STATEMENTS[lab])
        w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if _re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out


def hyps_of(w, lab):
    return [hyp(w, n, '%s.%s' % (lab, n), f) for n, f in HYPS.get(lab, [])]


def run(w):
    return (runh if HYPS.get(w.label) else (lambda x: x.run()))(w)


def cns(lab):
    from cl import split_imp
    return split_imp(STATEMENTS[lab])[1]


def ante(lab):
    from cl import split_imp
    return split_imp(STATEMENTS[lab])[0]


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])
