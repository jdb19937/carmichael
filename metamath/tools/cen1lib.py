"""Sortie CEN1: helpers and the frozen statements (Census.lean 1-905: the Lambda series at 1 + u,
the product character, conjugation of n^s, the |1 + sum|^2 expansion, comparison convergence,
Re(-L'/L) from the Landau expansion on squares).

    python3 tools/cen1lib.py print                                   # the frozen table
    MM_DB=sorties/cen1.mm python3 tools/cen1lib.py check [LABEL...]   # grammar check (mmatch)

Letters.  Character N X (LFN binds s k i), height T, shift A, zero R, delta D, point S, zero sum q
over ZD (binder r), Dirichlet sums k.  Product character U V X Z, integer A.  Expansion: index
set J, binders j l, weight A, terms V W.  Convergence: k over NN, coefficient B, constant C.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from tm import W
import lin
import cl as _cl
from cl import lift, Closure
from c9lib import SQ, HP0, CHI, LFN, R138
lin.FASTPATH = True

DB = 'sorties/cen1.mm'
_TXT = {}


def stmt(label):
    """the assertion of LABEL from sorties/cen1.mm or carmichael.mm, without |-"""
    for fn in (DB, 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if fn == DB or fn not in _TXT:
            _TXT[fn] = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), _TXT[fn], re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- objects (KD1's) -----------------------------------------------------------------
CT = lambda t: '( 2 + ( _i x. %s ) )' % t
ZD = lambda T='T': '{ r e. %s | ( %s ` r ) = 0 }' % (SQ(CT(T), R138), LFN)
MU = lambda q='q': '( %s holord %s )' % (LFN, q)
CHV = lambda n, N='N', X='X': '( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` %s ) )' % (X, N, n)
KLAN = '; ; ; ; ; ; ; 1 7 5 0 0 0 0 0'
LOGX = lambda T='T': '( log ` ( N x. ( ( abs ` %s ) + 2 ) ) )' % T
KL = lambda T='T': '( %s x. %s )' % (KLAN, LOGX(T))
NXH = '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'


def LAM(S, k='k'):
    """-L'/L as the Dirichlet series sum chi(k) Lam(k) k^-S (kdlogdv's right side)"""
    return 'sum_ %s e. NN ( ( %s x. ( Lam ` %s ) ) x. ( %s ^c -u %s ) )' % (k, CHV(k), k, k, S)


def VM(S, k='k'):
    return 'sum_ %s e. NN ( ( Lam ` %s ) x. ( %s ^c -u %s ) )' % (k, k, k, S)


def RQ(S, q='q'):
    return '( Re ` ( %s / ( %s - %s ) ) )' % (MU(q), S, q)


PT = lambda A, T: '( ( 1 + %s ) + ( _i x. %s ) )' % (A, T)
IND = lambda U, M, X: '( ( %s DChrInd %s ) ` %s )' % (U, M, X)
UV = '( U x. V )'
PSI = '( %s ( +g ` ( DChr ` %s ) ) %s )' % (IND('U', UV, 'X'), UV, IND('V', UV, '( ( invg ` ( DChr ` V ) ) ` Z )'))

# ---- frozen statements ---------------------------------------------------------------------
S = {}
# Census 437 + 461 (LSeries_ofReal_eq, tsum_vonMangoldt_rpow_le): the real Lambda series, Re form
S['cenvmb'] = '( ( U e. RR+ /\\ U <_ 1 ) -> ( %s e. RR /\\ ( Re ` %s ) <_ ( ( ( 5 / 4 ) / U ) + 5 ) ) )' % (
    VM('( 1 + U )'), VM('( 1 + U )'))
# Census 557 prodChar_apply
S['cenprodv'] = ('( ( ( U e. NN /\\ V e. NN ) /\\ ( X e. ( Base ` ( DChr ` U ) ) /\\ Z e. ( Base ` ( DChr ` V ) ) ) /\\ A e. ZZ ) -> '
                 '( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` A ) ) = ( %s x. ( * ` %s ) ) )') % (
    PSI, UV, CHV('A', 'U', 'X'), CHV('A', 'V', 'Z'))
# Census 790 / 816 / 898 (conj_natCast_cpow_*)
S['cencjcx'] = '( ( K e. NN /\\ S e. CC ) -> ( * ` ( K ^c S ) ) = ( K ^c ( * ` S ) ) )'
# Census 829 mul_conj_expand (deduction form; hypotheses cenexp.1-.4)
S['cenexp.1'] = '( ph -> J e. Fin )'
S['cenexp.2'] = '( ( ph /\\ j e. J ) -> V e. CC )'
S['cenexp.3'] = '( j = l -> V = W )'
S['cenexp.4'] = '( ph -> A e. RR )'
S['cenexp'] = ('( ph -> ( A x. ( ( abs ` ( 1 + sum_ j e. J V ) ) ^ 2 ) ) = ( ( ( A + ( 2 x. sum_ j e. J ( Re ` ( A x. V ) ) ) ) + '
               'sum_ j e. J ( A x. ( ( abs ` V ) ^ 2 ) ) ) + sum_ j e. J sum_ l e. ( J \\ { j } ) ( Re ` ( A x. ( V x. ( * ` W ) ) ) ) ) )')
# Census 870 summable_term_of_le (deduction form; hypotheses cencvg.1-.4)
S['cencvg.1'] = '( ph -> ( S e. CC /\\ 1 < ( Re ` S ) ) )'
S['cencvg.2'] = '( ph -> C e. RR )'
S['cencvg.3'] = '( ( ph /\\ k e. NN ) -> B e. CC )'
S['cencvg.4'] = '( ( ph /\\ k e. NN ) -> ( abs ` B ) <_ ( C x. ( Lam ` k ) ) )'
S['cencvg'] = '( ph -> seq 1 ( + , ( k e. NN |-> ( B x. ( k ^c -u S ) ) ) ) e. dom ~~> )'
# Census 653 / 697 core: Landau on the square, real parts
S['cenlnd'] = ('( ( ( %s /\\ T e. RR ) /\\ ( S e. CC /\\ ( abs ` ( S - %s ) ) <_ ( 3 / 2 ) /\\ 1 < ( Re ` S ) ) ) -> '
               '( ( Re ` %s ) <_ ( %s - sum_ q e. %s %s ) /\\ A. q e. %s ( %s e. RR /\\ 0 <_ %s ) ) )') % (
    CHI, CT('T'), LAM('S'), KL(), ZD(), RQ('S'), ZD(), RQ('S'), RQ('S'))
# Census 653 re_neg_logDeriv_le
S['cenrele'] = '( ( %s /\\ ( T e. RR /\\ ( A e. RR+ /\\ A <_ ( 1 / 2 ) ) ) ) -> ( Re ` %s ) <_ %s )' % (
    CHI, LAM(PT('A', 'T')), KL())
# Census 697 re_neg_logDeriv_le_of_zero, at 1 + 3 D (Lean 1 + 2 delta), gain 1 / ( 4 D ) (Lean 1 / ( 3 delta ))
S['cenrelz'] = ('( ( %s /\\ ( ( D e. RR+ /\\ D <_ ( 1 / ; 4 0 ) ) /\\ ( R e. CC /\\ ( %s ` R ) = 0 /\\ ( ( 1 - D ) <_ ( Re ` R ) /\\ ( Re ` R ) <_ 1 ) ) ) ) -> '
                '( Re ` %s ) <_ ( %s - ( 1 / ( 4 x. D ) ) ) )') % (
    CHI, LFN, LAM(PT('( 3 x. D )', '( Im ` R )')), KL('( Im ` R )'))

ORDER = [k for k in S if '.' not in k]


def hyps(label):
    return [(k, S[k]) for k in S if k.startswith(label + '.')]


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'cen1gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'cen1gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=cen1gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::cen1gc%s.1 |- %s\n' % (lab, S[lab]))
            for i, (k, h) in enumerate(hyps(lab)):
                f.write('h%d::cen1gc%s.%d |- %s\n' % (i + 2, lab, i + 2, h))
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
