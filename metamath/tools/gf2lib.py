"""Sortie GF2: frozen statements and helpers (GramFunction.lean 1074-2883).

    python3 tools/gf2lib.py print                                   # the frozen table
    MM_DB=sorties/gf2.mm python3 tools/gf2lib.py check [LABEL...]    # grammar check (mmatch)

Objects (macros, no df-), besides GF1's (tools/gf1lib.py: PH, AVG, KK, KQ, G1, MH, HM, C7):
  BGX(X, S)   = sum_ n e. NN ( ( BM ` n ) x. ( X ` ZR(n) ) ) x. n ^c -u S       Lean Bgram (Bgen (bMaj ..) chi S)
                at the frozen parameters, character X e. Base ( DChr ` N )
  BG(C, S)    = the same with a character FUNCTION C on NN (generic layer)
  PHI(N, R)   = sum_ r e. ( N RSet R ) ( ( phi ` r ) / ( r ^ 2 ) )              Lean PhiR
  G1F(W)      = G1 ( log M0 , log XP , ELLD , W ) at M0 = D ^c ( 3 / 5 ), XP = D ^c ( 6 / 5 ),
                ELLD = ( 1 / 100 ) log D                                         Lean G1 (M0par D) (Xpar D) (ellpar D)
  MAIN(S)     = ( ( phi N / N ) . PHI ) . G1F ( -u S )                            the principal residue
  C11         = 2 10 ^ 12 . CTau ^ 3                                             Lean C11 (NUMERALS.md row)
  C9(K)       = ( K . C7 ) . ( 5 + 2 log 400 )                                   Lean C9 CM
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
import gf1lib as G1L
from gf1lib import PH, AVG, KK, KQ, G1, HOL, HPM1, C7, DIV, RS, MH, HM, ZR, DB_, EXPH

DB = os.environ.get('MM_DB', 'sorties/gf2.mm')

# ---- frozen parameters (ZD1/Z5a macros written out) ---------------------------------------------
Z1 = '( D ^c ( ; 3 1 / ; 5 0 ) )'
Z2 = '( D ^c ( ; 6 3 / ; ; 1 0 0 ) )'
XP = '( D ^c ( 6 / 5 ) )'
M0 = '( D ^c ( 3 / 5 ) )'
RP = '( D ^c ( 1 / ; ; 1 0 0 ) )'
ELLD = '( ( 1 / ; ; 1 0 0 ) x. ( log ` D ) )'
PF = '( N PFun %s )' % RP
WF = '( WWin ` <. %s , %s , %s >. )' % (M0, XP, ELLD)
BM = '( %s bMaj %s )' % (PF, WF)
CDT = lambda T: '( <. %s , %s >. cDet <. %s , %s , %s >. )' % (Z1, Z2, PF, XP, T)
QT = lambda n, T='T': 'if ( ( %s ` %s ) = 0 , 0 , ( ( ( %s ` %s ) ^ 2 ) / ( %s ` %s ) ) )' % (BM, n, CDT(T), n, BM, n)
HZD = '( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) )'
HZ2 = '( D e. RR /\\ 1 < D /\\ 2 <_ ( log ` D ) )'
HT = '( T e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ T /\\ T <_ 1 ) )'
H0 = '( %s /\\ %s )' % (HZD, HT)

BGX = lambda X, S, n='n': 'sum_ %s e. NN ( ( ( %s ` %s ) x. ( %s ` %s ) ) x. ( %s ^c -u %s ) )' % (n, BM, n, X, ZR('N', n), n, S)
BG = lambda B, C, S, n='n': 'sum_ %s e. NN ( ( ( %s ` %s ) x. ( %s ` %s ) ) x. ( %s ^c -u %s ) )' % (n, B, n, C, n, n, S)
PHI = lambda N, R: 'sum_ r e. ( %s RSet %s ) ( ( phi ` r ) / ( r ^ 2 ) )' % (N, R)
LM0 = '( log ` %s )' % M0
LXP = '( log ` %s )' % XP
G1F = lambda W: G1(LM0, LXP, ELLD, W)
MAIN = lambda S: '( ( ( ( phi ` N ) / N ) x. %s ) x. %s )' % (PHI('N', RP), G1F('-u %s' % S))
C11 = '( ; ; ; ; ; ; ; ; ; ; ; ; 2 0 0 0 0 0 0 0 0 0 0 0 0 x. ( CTau ^ 3 ) )'
C9 = lambda K: '( ( %s x. %s ) x. ( 5 + ( 2 x. ( log ` ; ; 4 0 0 ) ) ) )' % (K, C7)
QRP = 'prod_ p e. { q e. Prime | ( q || N /\\ q <_ %s ) } ( 1 - ( 1 / p ) )' % RP
MERT = 'prod_ p e. ( ( 1 ... ( |_ ` %s ) ) i^i Prime ) ( 1 / ( 1 - ( 1 / p ) ) )' % RP
CHJ = lambda j: '( a e. NN |-> ( ( Q ` %s ) ` %s ) )' % (j, ZR('N', 'a'))
FDJ = lambda j: '( ( <. %s , %s >. FDet <. %s , %s , %s >. ) ` ( P ` %s ) )' % (Z1, Z2, PF, XP, CHJ(j), j)
XJK = '( ( Q ` j ) ( +g ` ( DChr ` N ) ) ( ( invg ` ( DChr ` N ) ) ` ( Q ` k ) ) )'
SJK = '( ( ( P ` j ) - T ) + ( * ` ( ( P ` k ) - T ) ) )'

S = {}
# ---- the headlines ZeroDensity (ZD2) consumes ------------------------------------------------------
# Lean Bgram_eq_main_add_rem_frozen + norm_Brem_le' (their only consumer, gram_row_le's hterm, uses
# exactly the triangle inequality of the two): the Gram function minus its principal residue.
S['gf2bt'] = ('( ( ( %s /\\ ( N e. NN /\\ X e. %s ) ) /\\ ( S e. CC /\\ ( ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ ( 1 / ; 5 0 ) ) /\\ '
              '( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ ( 2 x. D ) ) ) ) -> '
              '( abs ` ( %s - if ( X = ( 0g ` ( DChr ` N ) ) , %s , 0 ) ) ) <_ ( ( %s x. ( ( log ` D ) ^ 3 ) ) x. ( D ^c -u ( 7 / ; ; 1 0 0 ) ) ) )') % (
    HZ2, DB_('N'), BGX('X', 'S'), MAIN('S'), C11)
# Lean row_sum_le (Lemma 6.4)
VK = '( V ` k )'
S['gf2row'] = ('( ( ( ( D e. RR /\\ 1 < D /\\ 1 <_ ( log ` D ) ) /\\ N e. NN ) /\\ ( ( S e. Fin /\\ '
               'A. k e. S ( %s e. CC /\\ ( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) ) ) ) /\\ '
               '( A. k e. S ( k =/= J -> ( 1 / ( log ` D ) ) <_ ( abs ` ( Im ` %s ) ) ) /\\ '
               'A. m e. NN ( # ` { k e. S | ( ( m / ( log ` D ) ) <_ ( abs ` ( Im ` %s ) ) /\\ ( abs ` ( Im ` %s ) ) < ( ( m + 1 ) / ( log ` D ) ) ) } ) <_ 2 ) '
               '/\\ ( K e. RR /\\ %s <_ ( K x. ( log ` %s ) ) ) ) ) -> '
               'sum_ k e. S ( abs ` %s ) <_ ( ( ( %s x. ( %s ^ 2 ) ) x. ( 1 / ; ; 1 0 0 ) ) x. ( ( log ` D ) ^ 2 ) ) )') % (
    VK, VK, VK, VK, VK, VK, MERT, RP, MAIN(VK), C9('K'), QRP)
# Lean halasz_duality_frozen (Lemma 5.1 at the frozen parameters)
S['gf2hal'] = ('( ( ( %s /\\ N e. NN ) /\\ ( J e. Fin /\\ A. j e. J ( ( Q ` j ) e. %s /\\ ( ( P ` j ) e. CC /\\ T <_ ( Re ` ( P ` j ) ) ) ) ) ) -> '
               '( sum_ j e. J ( abs ` %s ) ^ 2 ) <_ ( sum_ n e. NN %s x. sum_ j e. J sum_ k e. J ( abs ` %s ) ) )') % (
    H0, DB_('N'), FDJ('j'), QT('n'), BGX(XJK, SJK, 'n'))

FROZEN = ['gf2bt', 'gf2row', 'gf2hal']
ORDER = [k for k in S if '.' not in k]


def hyps(label):
    return [(k, S[k]) for k in S if k.startswith(label + '.')]


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'gf2gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'gf2gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=gf2gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::gf2gc%s.1 |- %s\n' % (lab, S[lab]))
            for i, (k, h) in enumerate(hyps(lab)):
                f.write('h%d::gf2gc%s.%d |- %s\n' % (i + 2, lab, i + 2, h))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch', MM_DB=DB)
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in S:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or ORDER)
