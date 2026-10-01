"""Sortie CEN2: helpers and the frozen statements (Census.lean 905-1737: the positivity core
no_thirteen_bad at 1 + 3 delta, the small regime, the trivial regime, badChars, censusCount,
censusC2, censusC3, MidCensusHyp, census_contract, card_badConductors_le).

    python3 tools/cen2lib.py print                                   # the frozen table
    MM_DB=sorties/cen2.mm python3 tools/cen2lib.py check [LABEL...]   # grammar check (mmatch)

Objects consumed downstream (CM, T21b): BC (badChars), CNT (censusCount), C2 (censusC2), C3
(censusC3), THR (the threshold 10^-10), MCH (MidCensusHyp).  Bound letters of these closed
objects: modulus m, character y, zero o (the letters of zdilib's density interfaces, T21a),
MidCensusHyp's u v w.  Free letters: abscissa S, height V, cutoff Z (or K for an integer).
Core letters: character set J (binder j, l), level function M, zero function P, width D.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from tm import W
import lin
from cl import lift, Closure
from c9lib import CHI, LFN
from cen1lib import CHV, KLAN, stmt as _stmt1
lin.FASTPATH = True

DB = 'sorties/cen2.mm'
_TXT = {}


def stmt(label):
    """the assertion of LABEL from sorties/cen2.mm or carmichael.mm, without |-"""
    for fn in (DB, 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if fn == DB or fn not in _TXT:
            _TXT[fn] = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), _TXT[fn], re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- numerals ------------------------------------------------------------------------------
def dec(s):
    """decimal numeral text of the digit string s"""
    return ' '.join([';'] * (len(s) - 1) + list(s))


E10 = dec('1' + '0' * 10)                      # 10^10
THR = '( 1 / %s )' % E10                       # Lean 1/1000000000, here 10^-10 (NUMERALS)
C3 = dec('1' + '0' * 13)                       # censusC3 = 10^13 (Lean 10^12)
TEN = '; 1 0'
C2 = lambda V='V': '( ( %s ^ ( %s ^ %s ) ) x. ( %s + 2 ) )' % (TEN, TEN, TEN, V)   # 10^(10^10) (nu + 2)
F3940 = '( ; 3 9 / ; 4 0 )'
F140 = '( 1 / ; 4 0 )'
N13 = '; 1 3'

# ---- census objects ------------------------------------------------------------------------
BOX = lambda S, V: '( ( %s + ( _i x. -u %s ) ) crect ( 1 + ( _i x. %s ) ) )' % (S, V, V)


def ZFB(S, V, M, y='y', o='o'):
    """zeroFinset of ( M DChrLF y ) in [ S , 1 ] x [ -V , V ] (ZC1's ZF, letters of zdilib)"""
    return '{ %s e. %s | ( %s =/= 1 /\\ ( ( %s DChrLF %s ) ` %s ) = 0 ) }' % (o, BOX(S, V), o, M, y, o)


def BC(S, V, M, y='y', o='o'):
    """badChars sigma nu d: the primitive characters mod M with a zero in the box"""
    return '{ %s e. ( Base ` ( DChr ` %s ) ) | ( ( %s DChrCond %s ) = %s /\\ %s =/= (/) ) }' % (
        y, M, M, y, M, ZFB(S, V, M, y, o))


def CNT(S, V, K, m='m'):
    """censusCount sigma nu K"""
    return 'sum_ %s e. ( 1 ... %s ) ( # ` %s )' % (m, K, BC(S, V, m))


BND = lambda S, V, Z: '( %s x. ( %s ^c ( %s x. ( 1 - %s ) ) ) )' % (C2(V), Z, C3, S)
LOGZ = lambda Z, V: '( log ` ( %s x. ( %s + 2 ) ) )' % (Z, V)
MCH = ('A. u e. RR A. v e. RR A. w e. RR ( ( ( %s <_ u /\\ u <_ 1 ) /\\ ( 1 <_ v /\\ 2 <_ w ) /\\ '
       '( ( 1 - u ) < ( 2 / %s ) /\\ %s < ( ( 1 - u ) x. %s ) ) ) -> %s <_ %s )') % (
    F3940, C3, THR, LOGZ('w', 'v'), CNT('u', 'v', '( |_ ` w )'), BND('u', 'v', 'w'))
TYP = '( S e. RR /\\ V e. RR /\\ Z e. RR )'
RNG = '( ( %s <_ S /\\ S <_ 1 ) /\\ ( 1 <_ V /\\ 2 <_ Z ) )' % F3940

# ---- core objects (1 + 3 D, KD1/CEN1 letters: series index k) ------------------------------
PT3 = lambda T: '( ( 1 + ( 3 x. D ) ) + ( _i x. %s ) )' % T
AW = lambda k='k': '( ( Lam ` %s ) x. ( %s ^c -u ( 1 + ( 3 x. D ) ) ) )' % (k, k)
TW = lambda T, k='k': '( %s ^c -u ( _i x. %s ) )' % (k, T)
VT = lambda N, X, T, k='k': '( %s x. %s )' % (CHV(k, N, X), TW(T, k))
BV = '( ( ( 5 / 4 ) / ( 3 x. D ) ) + 5 )'
DDH = '( D e. RR+ /\\ D <_ %s )' % F140
KLOG = lambda A: '( %s x. ( log ` %s ) )' % (KLAN, A)
SQ = lambda E: '( ( abs ` %s ) ^ 2 )' % E

S = {}
# pointwise identities (Census 1068-1112: hg1, hg4 with prodChar_apply)
S['cen2t1'] = ('( ( ( k e. NN /\\ D e. RR ) /\\ ( E e. CC /\\ T e. RR ) ) -> ( %s x. ( E x. %s ) ) = '
               '( ( E x. ( Lam ` k ) ) x. ( k ^c -u %s ) ) )') % (AW(), TW('T'), PT3('T'))
S['cen2t3'] = ('( ( ( k e. NN /\\ D e. RR ) /\\ ( ( E e. CC /\\ F e. CC ) /\\ ( T e. RR /\\ U e. RR ) ) ) -> '
               '( %s x. ( ( E x. %s ) x. ( * ` ( F x. %s ) ) ) ) = ( ( ( E x. ( * ` F ) ) x. ( Lam ` k ) ) x. ( k ^c -u %s ) ) )') % (
    AW(), TW('T'), TW('U'), PT3('( T - U )'))
# helpers: character values and the unimodular twist
S['cen2chv'] = '( ( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ A e. ZZ ) -> ( %s e. CC /\\ ( abs ` %s ) <_ 1 ) )' % (CHV('A'), CHV('A'))
S['cen2tw'] = '( ( k e. NN /\\ T e. RR ) -> ( %s e. CC /\\ ( abs ` %s ) = 1 ) )' % (TW('T'), TW('T'))
# the three series groups (Census hbound0/hbound3, hbound1, hbound4 with hsum0-hsum4)
_VC = VT('N', 'X', 'T')
_SA = 'sum_ k e. NN %s' % AW()
_SC = 'sum_ k e. NN ( %s x. %s )' % (AW(), SQ(_VC))
S['cen2gc'] = ('( ( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ ( T e. RR /\\ %s ) ) -> '
               '( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s <_ %s ) ) /\\ '
               '( seq 1 ( + , ( k e. NN |-> ( %s x. %s ) ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s <_ %s ) ) ) )') % (
    DDH, AW(), _SA, _SA, BV, AW(), SQ(_VC), _SC, _SC, BV)
# generic: real parts of a dominated Dirichlet series (summable_re with summable_term_of_le)
_BK = '( B x. ( k ^c -u S ) )'
_SR = 'sum_ k e. NN ( Re ` %s )' % _BK
S['cen2re.1'] = '( ph -> ( S e. CC /\\ 1 < ( Re ` S ) ) )'
S['cen2re.2'] = '( ph -> C e. RR )'
S['cen2re.3'] = '( ( ph /\\ k e. NN ) -> B e. CC )'
S['cen2re.4'] = '( ( ph /\\ k e. NN ) -> ( abs ` B ) <_ ( C x. ( Lam ` k ) ) )'
S['cen2re.5'] = '( k = n -> B = E )'
S['cen2re'] = ('( ph -> ( seq 1 ( + , ( k e. NN |-> ( Re ` %s ) ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s = ( Re ` sum_ k e. NN %s ) ) ) )') % (
    _BK, _SR, _SR, _BK)
# the linear group with a generic height (Census hsum1, hbound2 in Dirichlet-series form)
_VTT = VT('N', 'X', 'T')
_BT = '( Re ` ( %s x. %s ) )' % (AW(), _VTT)
_ST = 'sum_ k e. NN %s' % _BT
_LAMT = 'sum_ k e. NN ( ( %s x. ( Lam ` k ) ) x. ( k ^c -u %s ) )' % (CHV('k'), PT3('T'))
S['cen2gs'] = ('( ( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ ( T e. RR /\\ %s ) ) -> '
               '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s = ( Re ` %s ) ) ) )') % (DDH, _BT, _ST, _ST, _LAMT)
_VR = VT('N', 'X', '( Im ` R )')
_BB = '( Re ` ( %s x. %s ) )' % (AW(), _VR)
_SB = 'sum_ k e. NN %s' % _BB
S['cen2gb'] = ('( ( %s /\\ ( %s /\\ ( R e. CC /\\ ( %s ` R ) = 0 /\\ ( ( 1 - D ) <_ ( Re ` R ) /\\ ( Re ` R ) <_ 1 ) ) ) ) -> '
               '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s <_ ( %s - ( 1 / ( 4 x. D ) ) ) ) ) )') % (
    CHI, DDH, LFN, _BB, _SB, _SB, KLOG('( N x. ( ( abs ` ( Im ` R ) ) + 2 ) )'))
_EE = '( Re ` ( %s x. ( %s x. ( * ` %s ) ) ) )' % (AW(), VT('N', 'X', 'T'), VT('M', 'Y', 'U'))
_SE = 'sum_ k e. NN %s' % _EE
PRIM2 = ('( ( ( N e. NN /\\ M e. NN ) /\\ ( ( X e. ( Base ` ( DChr ` N ) ) /\\ ( N DChrCond X ) = N ) /\\ '
         '( Y e. ( Base ` ( DChr ` M ) ) /\\ ( M DChrCond Y ) = M ) ) /\\ X =/= Y ) /\\ ( ( T e. RR /\\ U e. RR ) /\\ %s ) )') % DDH
S['cen2gd'] = '( %s -> ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ ( %s e. RR /\\ %s <_ %s ) ) )' % (
    PRIM2, _EE, _SE, _SE, KLOG('( ( N x. M ) x. ( ( abs ` ( T - U ) ) + 2 ) )'))
# generic: the sum of two convergent series (climadd with seradd)
S['cen2sadd'] = ('( ( ( F : NN --> CC /\\ G : NN --> CC /\\ H : NN --> CC ) /\\ ( seq 1 ( + , F ) ~~> A /\\ seq 1 ( + , G ) ~~> B ) /\\ '
                 'A. a e. NN ( H ` a ) = ( ( F ` a ) + ( G ` a ) ) ) -> seq 1 ( + , H ) ~~> ( A + B ) )')
# generic: positivity of the summed expansion (Census htsum, hpos, hre_eq; Summable.tsum_finsetSum by bvswap)
JL = '( J \\ { j } )'
TOT = lambda k: ('( ( ( ( A ` %s ) + ( 2 x. sum_ j e. J ( B ` %s ) ) ) + sum_ j e. J ( C ` %s ) ) + '
                 'sum_ j e. J sum_ l e. %s ( E ` %s ) )') % (k, k, k, JL, k)
S['cen2lim.1'] = '( ph -> J e. Fin )'
S['cen2lim.2'] = '( ( ph /\\ k e. NN ) -> 0 <_ %s )' % TOT('k')
S['cen2lim.3'] = '( ph -> A : NN --> RR )'
S['cen2lim.4'] = '( ( ph /\\ j e. J ) -> ( B : NN --> RR /\\ C : NN --> RR ) )'
S['cen2lim.5'] = '( ( ph /\\ ( j e. J /\\ l e. %s ) ) -> E : NN --> RR )' % JL
S['cen2lim.6'] = '( ph -> seq 1 ( + , A ) e. dom ~~> )'
S['cen2lim.7'] = '( ( ph /\\ j e. J ) -> ( seq 1 ( + , B ) e. dom ~~> /\\ seq 1 ( + , C ) e. dom ~~> ) )'
S['cen2lim.8'] = '( ( ph /\\ ( j e. J /\\ l e. %s ) ) -> seq 1 ( + , E ) e. dom ~~> )' % JL
S['cen2lim'] = ('( ph -> 0 <_ ( ( ( sum_ k e. NN ( A ` k ) + ( 2 x. sum_ j e. J sum_ k e. NN ( B ` k ) ) ) + sum_ j e. J sum_ k e. NN ( C ` k ) ) + '
                'sum_ j e. J sum_ l e. %s sum_ k e. NN ( E ` k ) ) )') % JL
# Census 907 no_thirteen_bad (threshold 10^-10; evaluated at 1 + 3 delta inside the proof)
MJ = '( M ` a )'
PJ = '( P ` a )'
FAM = ('A. a e. J ( ( ( %s e. NN /\\ 2 <_ %s /\\ %s <_ Z ) /\\ ( a e. ( Base ` ( DChr ` %s ) ) /\\ ( %s DChrCond a ) = %s ) ) /\\ '
       '( ( %s e. CC /\\ %s =/= 1 /\\ ( ( %s DChrLF a ) ` %s ) = 0 ) /\\ '
       '( ( 1 - D ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 /\\ ( abs ` ( Im ` %s ) ) <_ V ) ) )') % (
    MJ, MJ, MJ, MJ, MJ, MJ, PJ, PJ, MJ, PJ, PJ, PJ, PJ)
PARS = '( %s /\\ ( ( V e. RR /\\ 1 <_ V ) /\\ ( Z e. RR /\\ 2 <_ Z ) ) /\\ ( D x. %s ) <_ %s )' % (DDH, LOGZ('Z', 'V'), THR)
def BODY(N, X, R):
    """the family condition for one character X mod N with zero R (FAM's body)"""
    return ('( ( ( %s e. NN /\\ 2 <_ %s /\\ %s <_ Z ) /\\ ( %s e. ( Base ` ( DChr ` %s ) ) /\\ ( %s DChrCond %s ) = %s ) ) /\\ '
            '( ( %s e. CC /\\ %s =/= 1 /\\ ( ( %s DChrLF %s ) ` %s ) = 0 ) /\\ '
            '( ( 1 - D ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 1 /\\ ( abs ` ( Im ` %s ) ) <_ V ) ) )') % (
        N, N, N, X, N, N, X, N, R, R, N, X, R, R, R, R)


assert FAM == 'A. a e. J ' + BODY(MJ, 'a', PJ)
LL = LOGZ('Z', 'V')
S['cen2pt'] = ('( ( ( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) ) /\\ ( k e. NN /\\ T e. RR /\\ D e. RR ) ) -> '
               '( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. CC ) )') % (AW(), AW(), VT('N', 'X', 'T'))
_V1 = VT('N', 'X', '( Im ` R )')
_B1 = '( Re ` ( %s x. %s ) )' % (AW(), _V1)
_C1 = '( %s x. %s )' % (AW(), SQ(_V1))
S['cen2one'] = ('( ( %s /\\ %s ) -> ( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ ( sum_ k e. NN %s e. RR /\\ sum_ k e. NN %s <_ ( ( %s x. %s ) - ( 1 / ( 4 x. D ) ) ) ) ) /\\ '
                '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ ( sum_ k e. NN %s e. RR /\\ sum_ k e. NN %s <_ %s ) ) ) )') % (
    BODY('N', 'X', 'R'), PARS, _B1, _B1, _B1, KLAN, LL, _C1, _C1, _C1, BV)
_E2 = '( Re ` ( %s x. ( %s x. ( * ` %s ) ) ) )' % (AW(), _V1, VT('M', 'Y', '( Im ` Q )'))
S['cen2two'] = ('( ( ( %s /\\ %s /\\ X =/= Y ) /\\ %s ) -> ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ '
                '( sum_ k e. NN %s e. RR /\\ sum_ k e. NN %s <_ ( %s x. ( 2 x. %s ) ) ) ) )') % (
    BODY('N', 'X', 'R'), BODY('M', 'Y', 'Q'), PARS, _E2, _E2, _E2, KLAN, LL)
S['cen2n13'] = '-. ( ( ( J e. Fin /\\ ( # ` J ) = %s ) /\\ %s ) /\\ %s )' % (N13, FAM, PARS)
# census helpers (Lean card_filter_le, card_eq_totient, mem_zeroFinset, the sigma packaging of 1515-1560)
S['cen2bcf'] = '( M e. NN -> ( %s e. Fin /\\ ( # ` %s ) <_ M ) )' % (BC('S', 'V', 'M'), BC('S', 'V', 'M'))
S['cen2zb'] = ('( ( ( S e. RR /\\ V e. RR ) /\\ O e. %s ) -> ( O e. CC /\\ ( S <_ ( Re ` O ) /\\ ( Re ` O ) <_ 1 ) /\\ ( abs ` ( Im ` O ) ) <_ V ) )') % BOX('S', 'V')
S['cen2fam'] = ('( ( ( N e. ( 2 ... K ) /\\ K <_ Z ) /\\ ( X e. %s /\\ R e. %s ) /\\ ( ( S e. RR /\\ V e. RR /\\ Z e. RR ) /\\ ( D e. RR /\\ ( 1 - S ) <_ D ) ) ) -> %s )') % (
    BC('S', 'V', 'N'), ZFB('S', 'V', 'N', 'X'), 'BODYNXR')
UN = lambda K: 'U_ m e. ( 2 ... %s ) %s' % (K, BC('S', 'V', 'm'))
S['cen2tail'] = '( K e. ZZ -> ( %s e. Fin /\\ ( # ` %s ) = sum_ m e. ( 2 ... K ) ( # ` %s ) ) )' % (UN('K'), UN('K'), BC('S', 'V', 'm'))
S['cen2lg1'] = '( ( ( V e. RR /\\ 1 <_ V ) /\\ ( Z e. RR /\\ 2 <_ Z ) ) -> 1 <_ %s )' % LOGZ('Z', 'V')
# generic: a finite set has a subset of every smaller size
S['cen2sub'] = '( ( A e. Fin /\\ N e. NN0 /\\ N <_ ( # ` A ) ) -> E. s ( s C_ A /\\ ( # ` s ) = N ) )'
# Census 1466 censusCount_le_of_small
S['cen2small'] = '( ( %s /\\ %s /\\ ( ( 1 - S ) x. %s ) <_ %s ) -> %s <_ %s )' % (
    TYP, RNG, LOGZ('Z', 'V'), THR, CNT('S', 'V', '( |_ ` Z )'), N13)
# Census 1609 censusCount_le_sq
S['cen2sq'] = '( K e. NN0 -> %s <_ ( K x. K ) )' % CNT('S', 'V', 'K')
# Census 1665 census_contract (MidCensusHyp a hypothesis, as in Lean)
S['cen2cc'] = '( ( %s /\\ ( %s /\\ %s ) ) -> %s <_ %s )' % (MCH, TYP, RNG, CNT('S', 'V', '( |_ ` Z )'), BND('S', 'V', 'Z'))
# Census 1718 card_badConductors_le
S['cen2bad'] = ('( ( %s /\\ ( %s /\\ %s ) /\\ ( D e. Fin /\\ A. m e. D ( ( m e. NN0 /\\ 2 <_ m ) /\\ ( m <_ Z /\\ %s =/= (/) ) ) ) ) -> '
                '( # ` D ) <_ %s )') % (MCH, TYP, RNG, BC('S', 'V', 'm'), BND('S', 'V', 'Z'))

S['cen2fam'] = S['cen2fam'].replace('BODYNXR', BODY('N', 'X', 'R'))
ORDER = [k for k in S if '.' not in k]


def hyps(label):
    return [(k, S[k]) for k in S if k.startswith(label + '.')]


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'cen2gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'cen2gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=cen2gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::cen2gc%s.1 |- %s\n' % (lab, S[lab]))
            for i, (k, h) in enumerate(hyps(lab)):
                f.write('h%d::cen2gc%s.%d |- %s\n' % (i + 2, lab, i + 2, h))
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


# ---- helpers -------------------------------------------------------------------------------
def tokrep(text, m):
    return ' '.join(m.get(t, t) for t in text.split())


def ren(w, body, k='k', n='n'):
    """( k = n -> body = body[n/k] ) and the renamed body"""
    from congr import congruence
    from tm import StepGen
    eq = '%s = %s' % (k, n)
    idx = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    g = w.g
    st, val = congruence(body, {k: n}, eq, {k: idx}, g)
    w.lines.extend(g.lines); g.lines = []
    return st, val


def cvn(w, A0, body, cv, k='k', n='n'):
    """from cv ( A0 -> seq 1 ( + , ( k e. NN |-> body ) ) e. dom ~~> ) the same for the n-mapping; returns (step, body_n, mapeq)"""
    st, bn = ren(w, body, k, n)
    Mk = '( %s e. NN |-> %s )' % (k, body); Mn = '( %s e. NN |-> %s )' % (n, bn)
    me = w.s([st], 'cbvmptv', '%s = %s' % (Mk, Mn))
    se = w.s([w.s([me], 'a1i', '( %s -> %s = %s )' % (A0, Mk, Mn))], 'seqeq3d', '( %s -> seq 1 ( + , %s ) = seq 1 ( + , %s ) )' % (A0, Mk, Mn))
    c = w.s([se, cv], 'eqeltrrd',
            '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, Mn))
    return c, bn, me


def fvn(w, A0, body, rr, k='k', n='n'):
    """the value of the n-mapping at k under A0 and k e. NN"""
    from congr import mptval
    A1 = '( %s /\\ %s e. NN )' % (A0, k)
    bn = tokrep(body, {k: n})
    kn = w.s([], 'simpr', '( %s -> %s e. NN )' % (A1, k))
    ex = w.s([rr], 'elexd', '( %s -> %s e. _V )' % (A1, body))
    fv, val = mptval(w, A1, n, 'NN', bn, k, kn, exs=ex, gen=w.g)
    assert val == ' '.join(body.split()), (val, body)
    return fv


def sumre(w, A0, body, rr, cv, k='k', n='n'):
    """( A0 -> sum_ k e. NN body e. RR ); returns (step, fv, cv_n)"""
    c, bn, _ = cvn(w, A0, body, cv, k, n)
    fv = fvn(w, A0, body, rr, k, n)
    st = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0), fv, rr, c], 'isumrecl',
             '( %s -> sum_ %s e. NN %s e. RR )' % (A0, k, body))
    return st, fv, c


def sumle(w, A0, b1, r1, f1, c1, b2, r2, f2, c2, le, k='k'):
    """( A0 -> sum b1 <_ sum b2 ) (isumle; f1 f2 c1 c2 from sumre)"""
    return w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0), f1, r1, f2, r2, le, c1, c2], 'isumle',
               '( %s -> sum_ %s e. NN %s <_ sum_ %s e. NN %s )' % (A0, k, b1, k, b2))


def split_all(w, ctx, formula, step, out=None):
    """every conjunct (recursively) of formula, proved under ctx from step ( ctx -> formula ); returns {conjunct: step}"""
    from c9lib import top_and
    out = {} if out is None else out
    out[formula] = step
    t = formula.split()
    if len(t) < 3 or t[0] != '(' or t[-1] != ')':
        return out
    try:
        parts = top_and(formula)
    except AssertionError:
        return out
    if len(parts) == 2:
        refs = ['simpld', 'simprd']
    elif len(parts) == 3:
        refs = ['simp1d', 'simp2d', 'simp3d']
    else:
        return out
    for p, r in zip(parts, refs):
        if p in out:
            continue
        st = w.s([step], r, '( %s -> %s )' % (ctx, p))
        split_all(w, ctx, p, st, out)
    return out
