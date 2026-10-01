"""Sortie KD2: helpers and the frozen statements (KDerivDetect.lean 1481-3124: the seven budgets, step 3,
the tails, the window bound, the derivative kernel, Abel summation on the window, the endgame, kderiv_detection).

    python3 tools/kd2lib.py print                                   # the frozen table
    MM_DB=sorties/kd2.mm python3 tools/kd2lib.py check [LABEL...]    # grammar check (mmatch)

Letters.  Budgets: count N, index J (Lean j, Turan exponent J + 2), eta E, scale L, remainder C.  Headline:
character N X, height T, eta E, Lean's W is Y, integration letter u, window primes p (PWS binds p a).
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
import kd1lib as K1
from kd1lib import (W, lin, lift, Closure, CHI, LFN, ZD, MU, S0, LSK, KL, LOGX, KLAN, NDET, MDET, XONE, XTWO,
                    PWS, CHV, ONE, NXH, R120, DIAG, DIAGSEQ, ZSUB)
lin.FASTPATH = False   # the fast path mis-orders lemul2ad products (kd2bcau, kd2bpp)

DB = 'sorties/kd2.mm'


def stmt(label):
    for fn in (DB, 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- objects -----------------------------------------------------------------------
R5000 = '( 1 / ; ; ; 5 0 0 0 )'
C56E = '( ; 5 6 x. ( exp ` 1 ) )'
C8E8 = '; ; ; ; ; ; ; ; 8 4 0 0 0 0 0 0 0'          # Ndet's constant
C35 = '; ; ; ; ; ; ; 3 5 0 0 0 0 0 0'                # 2 . 17500000: KL <_ C35 L


def QQ(N='N', E='E', J='J'):
    """Lean's Turan floor Q = (1/(56 e))^N (1/(2 eta))^(j+2)"""
    return '( ( ( 1 / %s ) ^ %s ) x. ( ( 1 / ( 2 x. %s ) ) ^ ( %s + 2 ) ) )' % (C56E, N, E, J)


def Q8(N='N', E='E', J='J'): return '( %s / 8 )' % QQ(N, E, J)
def FQ8(N='N', E='E', J='J'): return '( ( ! ` ( %s + 1 ) ) x. %s )' % (J, Q8(N, E, J))


def PSET(Y, Z, a='a'):
    """PWS's index set: primes in ( Y , |_ Z ]"""
    return '{ %s e. ( 1 ... ( |_ ` %s ) ) | ( %s e. Prime /\\ %s < %s ) }' % (a, Z, a, Y, a)


def CP(p, T='T'):
    """PWS's summand chi(p) log p p^(-1 - i T)"""
    return '( ( %s x. ( log ` %s ) ) x. ( %s ^c ( -u 1 - ( %s x. _i ) ) ) )' % (CHV(p), p, p, T)


def PHI(J, t, E='E'): return '( ( ( log ` %s ) ^ ( %s + 1 ) ) x. ( %s ^c -u %s ) )' % (t, J, t, E)
def PSI(J, t, E='E'):
    return '( ( ( %s ^c ( -u 1 - %s ) ) x. ( ( log ` %s ) ^ %s ) ) x. ( ( %s + 1 ) - ( %s x. ( log ` %s ) ) ) )' % (t, E, t, J, J, E, t)


def DWIN(J, Y, Z, T='T', E='E', p='p'):
    return 'sum_ %s e. %s ( %s x. %s )' % (p, PSET(Y, Z), PHI(J, p, E), CP(p, T))


def DG2(K, U):
    """kddiag2's bound K! e (5/4)(K+2)/U^(K+1)"""
    return '( ( ( ( ! ` %s ) x. ( exp ` 1 ) ) x. ( ( 5 / 4 ) x. ( %s + 2 ) ) ) / ( %s ^ ( %s + 1 ) ) )' % (K, K, U, K)


Z6 = ZSUB(ZD(), '( abs ` ( p - %s ) ) <_ ( 6 x. E )' % ONE('T'))
FAR = lambda C: '( ( ( 1 / E ) x. ( ( ( ( 5 / 4 ) / E ) + 5 ) + %s ) ) / ( ( 6 x. E ) ^ J ) )' % C
CAU = lambda C: '( ( 2 x. ( 3 ^ ( J + 1 ) ) ) x. %s )' % C
M6 = '( 6 x. N )'

def LT(K, S, n):
    """the LSK summand at n"""
    return '( ( ( ( log ` %s ) ^ %s ) x. ( %s x. ( Lam ` %s ) ) ) x. ( %s ^c -u %s ) )' % (n, K, CHV(n), n, n, S)


VMT = lambda k, U: '( ( Lam ` %s ) x. ( %s ^c -u ( 1 + %s ) ) )' % (k, k, U)
def DT(M, K, U): return '( ( ( Lam ` %s ) x. ( ( log ` %s ) ^ %s ) ) x. ( %s ^c -u ( 1 + %s ) ) )' % (M, M, K, M, U)
def BN(x): return 'if ( %s e. Prime , 0 , ( ( Lam ` %s ) x. ( %s ^c -u ( 3 / 4 ) ) ) )' % (x, x, x)
def PTR(M, K='K'):
    return ('( ( ( ( 4 ^ %s ) x. ( ! ` %s ) ) x. %s ) + ( ( ( ( log ` Y ) ^ %s ) x. %s ) + ( ( Z ^c -u ( E / 2 ) ) x. %s ) ) )'
            % (K, K, BN(M), K, VMT(M, 'E'), DT(M, K, '( E / 2 )')))

# ---- frozen statements -------------------------------------------------------------
S = {}
# helpers of the budgets
S['kd2nmul'] = ('( ( ( A e. RR /\\ 0 <_ A ) /\\ ( B e. RR /\\ ( 2 x. A ) <_ B ) /\\ N e. NN0 ) -> '
                '( N x. ( A ^ N ) ) <_ ( B ^ N ) )')
S['kd2stir'] = ('( ( ( A e. RR /\\ 0 <_ A ) /\\ ( K e. NN0 /\\ A <_ K ) ) -> '
                '( ( A / ( exp ` 1 ) ) ^ K ) <_ ( ! ` K ) )')
DEN = '( ( 8 x. ( %s ^ N ) ) x. ( ( 2 x. E ) ^ ( J + 2 ) ) )' % C56E
S['kd2q8'] = ('( ( ( E e. RR+ /\\ N e. NN0 /\\ J e. NN0 ) /\\ ( X e. RR /\\ F e. RR ) ) -> '
              '( X <_ ( F x. %s ) <-> ( X x. %s ) <_ F ) )') % (Q8(), DEN)
S['kd2tc'] = '( %s e. RR+ /\\ %s < ; ; 1 6 8 )' % (C56E, C56E)

BH = '( ( E e. RR+ /\\ E <_ %s ) /\\ ( N e. NN /\\ J e. NN0 ) /\\ ( %s + 1 ) <_ ( J + 2 ) )' % (R5000, M6)
LH = '( ( L e. RR /\\ 0 <_ L ) /\\ ( 6 + ( ( %s x. E ) x. L ) ) <_ N )' % C8E8
S['kd2bfar'] = '( ( %s /\\ ( %s /\\ ; 4 9 <_ N ) /\\ ( C e. RR /\\ C <_ ( %s x. L ) ) ) -> %s <_ %s )' % (BH, LH, C35, FAR('C'), Q8())
S['kd2bcau'] = '( ( %s /\\ %s /\\ ( C e. RR /\\ 0 <_ C /\\ C <_ ( %s x. L ) ) ) -> %s <_ %s )' % (BH, LH, C35, CAU('C'), Q8())
S['kd2bpp'] = '( %s -> ( ; 2 0 x. ( 4 ^ ( J + 1 ) ) ) <_ %s )' % (BH, Q8())
S['kd2blow'] = ('( ( %s /\\ 5 <_ N ) -> ( ( ( %s / ( ; 1 6 x. E ) ) ^ ( J + 1 ) ) x. ( ( ( 5 / 4 ) / E ) + 5 ) ) <_ %s )') % (
    BH, M6, FQ8())
HH = '( E e. RR+ /\\ ( N e. NN /\\ J e. NN0 ) /\\ ( J + 2 ) <_ ( 7 x. N ) )'
S['kd2bhigh'] = '( %s -> ( ( exp ` -u ( 8 x. %s ) ) x. %s ) <_ %s )' % (HH, M6, DG2('( J + 1 )', '( E / 2 )'), FQ8())
X2L = '( ( ; 1 6 x. %s ) / E )' % M6
S['kd2bbd'] = ('( ( %s /\\ ( J + 2 ) <_ ( 7 x. N ) ) -> ( ( ( %s ^ ( J + 1 ) ) x. ( exp ` -u ( ; 1 6 x. %s ) ) ) x. '
               '( ( exp ` 1 ) x. ( ( ( 5 / 4 ) x. %s ) + 5 ) ) ) <_ %s )') % (BH, X2L, M6, X2L, FQ8())
S['kd2bend'] = ('( ( %s /\\ ; ; ; ; 7 3 9 8 4 <_ N ) -> 1 <_ ( ( ( ( E ^ 3 ) x. %s ) x. ( exp ` ( 6 x. %s ) ) ) x. '
                '( ( E x. ( ( ( %s x. ( E ^ J ) ) / ; 6 8 ) ^ 2 ) ) / ( ; 1 6 x. %s ) ) ) )') % (HH, M6, M6, QQ(), M6)

# step 3
LSH = '( %s /\\ ( E e. RR+ /\\ E <_ 1 ) /\\ ( S e. CC /\\ ( Re ` S ) = ( 1 + E ) /\\ K e. NN0 ) )' % NXH
S['kd2lscl'] = '( %s -> %s e. CC )' % (LSH, LSK('K', 'S'))
S['kd2lsb'] = ('( ( ( %s /\\ ( T e. RR /\\ E e. RR+ /\\ E <_ %s ) ) /\\ ( ( J e. NN0 /\\ Q e. RR ) /\\ '
               '( Q <_ ( abs ` sum_ q e. %s ( %s / ( ( %s - q ) ^ ( J + 2 ) ) ) ) /\\ %s <_ ( Q / 8 ) /\\ %s <_ ( Q / 8 ) ) ) ) -> '
               '( ( ! ` ( J + 1 ) ) x. ( ( 3 / 4 ) x. Q ) ) <_ ( abs ` %s ) )') % (
    CHI, R120, Z6, MU(), S0(), FAR(KL), CAU(KL), LSK('( J + 1 )', S0()))

# tails
VMT = lambda k, U: '( ( Lam ` %s ) x. ( %s ^c -u ( 1 + %s ) ) )' % (k, k, U)
S['kd2vmp'] = ('( ( ( U e. RR+ /\\ U <_ 1 ) /\\ ( A e. Fin /\\ A C_ NN ) ) -> sum_ k e. A %s <_ ( ( ( 5 / 4 ) / U ) + 5 ) )') % VMT('k', 'U')
S['kd2npf'] = ('( M e. RR -> sum_ n e. ( 1 ... ( |_ ` M ) ) if ( n e. Prime , 0 , ( ( Lam ` n ) x. ( n ^c -u ( 3 / 4 ) ) ) ) <_ ; 2 0 )')
S['kd2pwt'] = ('( ( %s /\\ ( T e. RR /\\ E e. RR /\\ J e. NN0 ) /\\ P e. Prime ) -> '
               '( ( ( ( log ` P ) ^ ( J + 1 ) ) x. ( %s x. ( Lam ` P ) ) ) x. ( P ^c -u %s ) ) = ( %s x. %s ) )') % (
    NXH, CHV('P'), S0(), PHI('J', 'P'), CP('P'))
TL = ('( ( ( ; 2 0 x. ( ( 4 ^ ( J + 1 ) ) x. ( ! ` ( J + 1 ) ) ) ) + ( ( ( log ` Y ) ^ ( J + 1 ) ) x. ( ( ( 5 / 4 ) / E ) + 5 ) ) ) + '
      '( ( Z ^c -u ( E / 2 ) ) x. %s ) )') % DG2('( J + 1 )', '( E / 2 )')
S['kd2dgp'] = ('( ( ( ( U e. RR+ /\\ U <_ %s ) /\\ K e. NN0 ) /\\ ( A e. Fin /\\ A C_ NN ) ) -> sum_ k e. A %s <_ %s )') % (R120, DT('k', 'K', 'U'), DG2('K', 'U'))
SUBH = ('( %s /\\ ( T e. RR /\\ E e. RR+ /\\ E <_ %s ) /\\ ( ( Y e. RR /\\ 1 <_ Y ) /\\ ( Z e. RR /\\ Y <_ Z ) /\\ J e. NN0 ) )') % (NXH, R120)
S['kd2psum'] = ('( ( %s /\\ ( W e. NN /\\ ( |_ ` Z ) <_ W ) ) -> ( abs ` ( sum_ n e. ( 1 ... W ) %s - %s ) ) <_ %s )') % (
    SUBH, LT('( J + 1 )', S0(), 'n'), DWIN('J', 'Y', 'Z'), TL)
S['kd2sub'] = ('( ( %s /\\ ( T e. RR /\\ E e. RR+ /\\ E <_ %s ) /\\ ( ( Y e. RR /\\ 1 <_ Y ) /\\ ( Z e. RR /\\ Y <_ Z ) /\\ J e. NN0 ) ) -> '
               '( abs ` ( %s - %s ) ) <_ %s )') % (NXH, R120, LSK('( J + 1 )', S0()), DWIN('J', 'Y', 'Z'), TL)

S['kd2pt'] = ('( ( ( E e. RR+ /\\ K e. NN0 ) /\\ ( ( Y e. RR /\\ 1 <_ Y ) /\\ Z e. RR+ ) /\\ ( M e. NN /\\ ( -. M e. Prime \\/ -. Y < M \\/ -. M <_ Z ) ) ) -> '
              '%s <_ %s )') % (DT('M', 'K', 'E'), PTR('M'))

# window
S['kd2wb'] = ('( ( %s /\\ ( T e. RR /\\ Y e. RR /\\ U e. RR ) /\\ ( Z e. RR /\\ ( exp ` ; 2 0 ) <_ Z /\\ U <_ Z ) ) -> '
              '( abs ` %s ) <_ ( ( exp ` 1 ) x. ( ( ( 5 / 4 ) x. ( log ` Z ) ) + 5 ) ) )') % (NXH, PWS('T', 'Y', 'U'))
S['kd2pwsif'] = ('( ( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( Z e. RR /\\ U e. RR /\\ U <_ Z ) ) -> '
                 '%s = sum_ p e. %s if ( p <_ U , %s , 0 ) )') % (NXH, PWS('T', 'Y', 'U'), PSET('Y', 'Z'), CP('p'))

# kernel
S['kd2dv'] = ('( ( E e. RR /\\ J e. NN0 ) -> ( ( RR _D ( u e. RR+ |-> %s ) ) = ( u e. RR+ |-> %s ) /\\ '
              '( u e. RR+ |-> %s ) e. ( RR+ -cn-> CC ) ) )') % (PHI('J', 'u'), PSI('J', 'u'), PSI('J', 'u'))
S['kd2kb'] = ('( ( ( E e. RR+ /\\ ( J e. NN0 /\\ M e. RR /\\ M <_ ( J + 1 ) ) ) /\\ ( U e. RR /\\ 1 <_ U /\\ ( E x. ( log ` U ) ) <_ ( ; 1 6 x. M ) ) ) -> '
              '( ( abs ` %s ) x. U ) <_ ( ( ( ; 1 7 x. ( J + 1 ) ) x. ( ! ` J ) ) / ( E ^ J ) ) )') % PSI('J', 'U')

# integration
HYPS = {}
HYPS['kd2ind'] = ['( ph -> ( Y e. RR /\\ Z e. RR ) )', '( ph -> ( A e. RR /\\ Y < A /\\ A <_ Z ) )', '( ph -> ( u e. ( A (,) Z ) |-> F ) e. L^1 )',
                  '( ( ph /\\ u e. ( Y (,) Z ) ) -> F e. CC )']
S['kd2ind'] = ('( ph -> ( ( u e. ( Y (,) Z ) |-> if ( A <_ u , F , 0 ) ) e. L^1 /\\ S. ( Y (,) Z ) if ( A <_ u , F , 0 ) _d u = S. ( A (,) Z ) F _d u ) )')
S['kd2log'] = ('( ( A e. RR+ /\\ B e. RR /\\ A <_ B ) -> ( ( u e. ( A (,) B ) |-> ( 1 / u ) ) e. L^1 /\\ '
               'S. ( A (,) B ) ( 1 / u ) _d u = ( ( log ` B ) - ( log ` A ) ) ) )')
PWU = PWS('T', 'Y', 'u')
S['kd2abel'] = ('( ( %s /\\ ( T e. RR /\\ E e. RR /\\ J e. NN0 ) /\\ ( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z ) ) -> '
                '( ( u e. ( Y (,) Z ) |-> ( %s x. %s ) ) e. L^1 /\\ %s = ( ( %s x. %s ) - S. ( Y (,) Z ) ( %s x. %s ) _d u ) ) )') % (
    NXH, PSI('J', 'u'), PWU, DWIN('J', 'Y', 'Z'), PHI('J', 'Z'), PWS('T', 'Y', 'Z'), PSI('J', 'u'), PWU)
S['kd2ibl'] = ('( ( %s /\\ T e. RR /\\ ( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z ) ) -> '
               '( u e. ( Y (,) Z ) |-> ( ( ( abs ` %s ) ^ 2 ) / u ) ) e. L^1 )') % (NXH, PWU)
S['kd2amx'] = ('( ( ( G e. RR+ /\\ K e. RR+ /\\ C e. RR+ ) /\\ ( I e. RR /\\ ( ( ( 2 x. G ) x. K ) x. ( G x. C ) ) <_ ( C x. ( ( ( K ^ 2 ) x. I ) + ( ( G ^ 2 ) x. K ) ) ) ) ) -> '
               '( ( G ^ 2 ) / K ) <_ I )')
HYPS['kd2am'] = ['( ph -> ( Y e. RR+ /\\ Z e. RR /\\ Y <_ Z ) )', '( ph -> ( u e. ( Y (,) Z ) |-> ( P x. F ) ) e. L^1 )',
                 '( ph -> ( u e. ( Y (,) Z ) |-> ( ( ( abs ` F ) ^ 2 ) / u ) ) e. L^1 )', '( ( ph /\\ u e. ( Y (,) Z ) ) -> ( P e. RR /\\ F e. CC ) )',
                 '( ( ph /\\ u e. ( Y (,) Z ) ) -> ( ( abs ` P ) x. u ) <_ C )',
                 '( ph -> ( C e. RR+ /\\ ( K e. RR+ /\\ ( ( log ` Z ) - ( log ` Y ) ) <_ K ) /\\ ( G e. RR+ /\\ ( G x. C ) <_ ( abs ` S. ( Y (,) Z ) ( P x. F ) _d u ) ) ) )']
S['kd2am'] = '( ph -> ( ( G ^ 2 ) / K ) <_ S. ( Y (,) Z ) ( ( ( abs ` F ) ^ 2 ) / u ) _d u )'

# headline
LY = '( log ` Y )'
XO, XT = XONE('E', LY), XTWO('E', LY)
A0H = ('( ( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( N <_ Y /\\ ( ( abs ` T ) + 2 ) <_ Y ) ) /\\ '
       '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) /\\ '
       'E. p e. CC ( ( %s ` p ) = 0 /\\ ( abs ` ( p - %s ) ) <_ E ) ) )') % (CHI, R5000, LY, LFN, ONE('T'))
ND = NDET('E', LY); MD = MDET('E', LY)
QJ = QQ(ND, 'E', 'J')
S['kd2da'] = ('( ( %s /\\ ( J e. NN0 /\\ ( ( ( 6 x. %s ) + 1 ) <_ ( J + 2 ) /\\ ( J + 2 ) <_ ( 7 x. %s ) ) /\\ %s <_ ( abs ` sum_ q e. %s ( %s / ( ( %s - q ) ^ ( J + 2 ) ) ) ) ) ) -> '
              '( ( ! ` ( J + 1 ) ) x. ( ( 3 / 4 ) x. %s ) ) <_ ( abs ` %s ) )') % (A0H, ND, ND, QJ, Z6, MU(), S0(), QJ, LSK('( J + 1 )', S0()))
FJ = '( ! ` ( J + 1 ) )'
HJB = ('( J e. NN0 /\\ ( ( ( 6 x. %s ) + 1 ) <_ ( J + 2 ) /\\ ( J + 2 ) <_ ( 7 x. %s ) ) /\\ ( %s x. ( ( 3 / 4 ) x. %s ) ) <_ ( abs ` %s ) )') % (ND, ND, FJ, QJ, LSK('( J + 1 )', S0()))
XO_, XT_ = XONE('E', LY), XTWO('E', LY)
FINAL = ('1 <_ ( ( ( ( E ^ 3 ) x. %s ) x. ( exp ` ( 6 x. %s ) ) ) x. S. ( %s (,) %s ) ( ( ( abs ` %s ) ^ 2 ) / u ) _d u )') % (MD, MD, XO_, XT_, PWS('T', XO_, 'u'))
A0B = ('( ( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( N <_ Y /\\ ( ( abs ` T ) + 2 ) <_ Y ) ) /\\ '
       '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) ) )') % (CHI, R5000, LY)
S['kd2db'] = '( ( %s /\\ %s ) -> %s )' % (A0B, HJB, FINAL)
S['kd2det'] = ('( ( ( %s /\\ ( T e. RR /\\ Y e. RR ) /\\ ( N <_ Y /\\ ( ( abs ` T ) + 2 ) <_ Y ) ) /\\ '
               '( ( E e. RR+ /\\ E <_ %s ) /\\ 1 <_ ( ( ; 1 2 x. E ) x. %s ) /\\ '
               'E. p e. CC ( ( %s ` p ) = 0 /\\ ( abs ` ( p - %s ) ) <_ E ) ) ) -> '
               '1 <_ ( ( ( ( E ^ 3 ) x. %s ) x. ( exp ` ( 6 x. %s ) ) ) x. S. ( %s (,) %s ) ( ( ( abs ` %s ) ^ 2 ) / u ) _d u ) )') % (
    CHI, R5000, LY, LFN, ONE('T'), MDET('E', LY), MDET('E', LY), XO, XT, PWS('T', XO, 'u'))


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'kd2gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'kd2gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=kd2gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::kd2gc%s.1 |- %s\n' % (lab, S[lab]))
            for k, hf in enumerate(HYPS.get(lab, [])):
                f.write('h%d::kd2gc%s.%d |- %s\n' % (k + 2, lab, k + 2, hf))
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
        check([a for a in sys.argv[2:]] or list(S))


# ---- step helpers ----------------------------------------------------------------------
def D(w, ante, ref, hyps, concl, name=None):
    """deduction step ( ante -> concl )"""
    return w.s(hyps, ref, '( %s -> %s )' % (ante, concl), name=name)


def a1(w, ante, ref, fact):
    """closed fact lifted to ( ante -> fact )"""
    return w.s([w.s([], ref, fact)], 'a1i', '( %s -> %s )' % (ante, fact))


def chain(w, ante, terms, steps, rel=None):
    """( ante -> t0 R tn ) from steps[i] : ( ante -> t_i R_i t_(i+1) ); rel[i] in '=', '<_', '<'"""
    rel = rel or ['='] * len(steps)
    steps = list(steps)
    for i, st in enumerate(steps):
        if isinstance(st, tuple):
            steps[i] = w.s([st[1]], 'eqcomd', '( %s -> %s = %s )' % (ante, terms[i], terms[i + 1]))
    cur, cr = steps[0], rel[0]
    for i in range(1, len(steps)):
        r = rel[i]
        a, b, c = terms[0], terms[i], terms[i + 1]
        if cr == '=' and r == '=':
            ref, nr = 'eqtrd', '='
        elif cr == '=':
            ref, nr = 'eqbrtrd', r
        elif r == '=':
            ref, nr = 'breqtrd', cr
        else:
            raise ValueError('chain: use letrd/ltletrd with memberships')
        cur = w.s([cur, steps[i]], ref, '( %s -> %s %s %s )' % (ante, a, nr, c))
        cr = nr
    return cur


def only_run(w, only):
    if only and w.label not in only:
        return True
    return w.run()


def numpow(w, b, n):
    """closed step ( b ^ n ) = value for small naturals b >= 1, n >= 1 (expp1 chain)"""
    import num
    bt = num.nat_text(b)
    cur = w.s([num.cc(w, bt), w.inst('exp1')], 'ax-mp', '( %s ^ 1 ) = %s' % (bt, bt))
    v = b
    for k in range(1, n):
        kt, k1t = num.nat_text(k), num.nat_text(k + 1)
        e = w.s([w.s([num.cc(w, bt), num.nn0(w, k)], 'pm3.2i', '( %s e. CC /\\ %s e. NN0 )' % (bt, kt)), w.inst('expp1')], 'ax-mp',
                '( %s ^ ( %s + 1 ) ) = ( ( %s ^ %s ) x. %s )' % (bt, kt, bt, kt, bt))
        a = num.add_nat(w, k, 1)
        e0 = w.s([a], 'oveq2i', '( %s ^ ( %s + 1 ) ) = ( %s ^ %s )' % (bt, kt, bt, k1t))
        e1 = w.s([e0, e], 'eqtr3i', '( %s ^ %s ) = ( ( %s ^ %s ) x. %s )' % (bt, k1t, bt, kt, bt))
        e2 = w.s([cur], 'oveq1i', '( ( %s ^ %s ) x. %s ) = ( %s x. %s )' % (bt, kt, bt, num.nat_text(v), bt))
        m = num.mul_nat(w, v, b)
        v = v * b
        cur = w.s([w.s([e1, e2], 'eqtri', '( %s ^ %s ) = ( %s x. %s )' % (bt, k1t, num.nat_text(v // b), bt)), m], 'eqtri',
                  '( %s ^ %s ) = %s' % (bt, k1t, num.nat_text(v)))
    return cur


def inst_stmt(label, sub):
    from c8lib import tsub
    from cl import split_imp
    return split_imp(tsub(stmt(label), sub))


def use(w, A, label, sub, hstep):
    """( A -> C' ) from hstep : ( A -> H' ) where label : ( H -> C ) instantiated by the token map sub"""
    h, c = inst_stmt(label, sub)
    return w.s([hstep, w.inst(label)], 'syl', '( %s -> %s )' % (A, c))


SQ13 = K1.SQ(K1.CT('T'), K1.R138)


def zcc(w, A, z, zmem, tr):
    """( A -> z e. CC ) from zmem : ( A -> z e. ZD ), tr : ( A -> T e. RR )"""
    d = lambda ref, h, c: D(w, A, ref, h, c)
    R138 = K1.R138
    CTT = K1.CT('T')
    RI = '( %s + ( _i x. %s ) )' % (R138, R138)
    ic = a1(w, A, 'ax-icn', '_i e. CC')
    r138 = d('recnd', [w.s([__import__('num').real(w, R138)], 'a1i', '( %s -> %s e. RR )' % (A, R138))], '%s e. CC' % R138)
    cct = d('addcld', [a1(w, A, '2cn', '2 e. CC'), d('mulcld', [ic, d('recnd', [tr], 'T e. CC')], '( _i x. T ) e. CC')], '%s e. CC' % CTT)
    ric = d('addcld', [r138, d('mulcld', [ic, r138], '( _i x. %s ) e. CC' % R138)], '%s e. CC' % RI)
    lo = '( %s - %s )' % (CTT, RI); hi = '( %s + %s )' % (CTT, RI)
    sqcc = d('syl', [d('jca', [d('subcld', [cct, ric], '%s e. CC' % lo), d('addcld', [cct, ric], '%s e. CC' % hi)], '( %s e. CC /\\ %s e. CC )' % (lo, hi)), w.inst('crectss')],
             '%s C_ CC' % SQ13)
    zs = d('sseldd', [a1(w, A, 'ssrab2', '%s C_ %s' % (ZD(), SQ13)), zmem], '%s e. %s' % (z, SQ13))
    return d('sseldd', [sqcc, zs], '%s e. CC' % z)


def LT(K, S, n):
    """the LSK summand at n"""
    return '( ( ( ( log ` %s ) ^ %s ) x. ( %s x. ( Lam ` %s ) ) ) x. ( %s ^c -u %s ) )' % (n, K, CHV(n), n, n, S)


def tcong(w, x, y, K, S):
    """closed ( x = y -> LT(x) = LT(y) )"""
    H = '%s = %s' % (x, y)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (H, f))
    lg = s([], 'fveq2', '( log ` %s ) = ( log ` %s )' % (x, y))
    lk = s([lg], 'oveq1d', '( ( log ` %s ) ^ %s ) = ( ( log ` %s ) ^ %s )' % (x, K, y, K))
    ZR = '( ZRHom ` ( Z/nZ ` N ) )'
    z1 = s([], 'fveq2', '( %s ` %s ) = ( %s ` %s )' % (ZR, x, ZR, y))
    z2 = s([z1], 'fveq2d', '%s = %s' % (CHV(x), CHV(y)))
    lm = s([], 'fveq2', '( Lam ` %s ) = ( Lam ` %s )' % (x, y))
    cl_ = s([z2, lm], 'oveq12d', '( %s x. ( Lam ` %s ) ) = ( %s x. ( Lam ` %s ) )' % (CHV(x), x, CHV(y), y))
    a = s([lk, cl_], 'oveq12d', '( ( ( log ` %s ) ^ %s ) x. ( %s x. ( Lam ` %s ) ) ) = ( ( ( log ` %s ) ^ %s ) x. ( %s x. ( Lam ` %s ) ) )' % (x, K, CHV(x), x, y, K, CHV(y), y))
    c = s([], 'oveq1', '( %s ^c -u %s ) = ( %s ^c -u %s )' % (x, S, y, S))
    return s([a, c], 'oveq12d', '%s = %s' % (LT(K, S, x), LT(K, S, y)))
