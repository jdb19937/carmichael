"""Sortie T21b: T21.lean 1269-2197 (the exceptional set, the zero transfer, the explicit
formula for every character, orthogonality, truncation, thresholds, theta_AP_T21).
Frozen statements `SB` (BM and F2 read `t21thm`), objects, helpers.  Built on tools/t21alib.py.

    python3 tools/t21blib.py print                                   # the frozen table
    MM_DB=sorties/t21b.mm python3 tools/t21blib.py check [LABEL...]  # grammar check (mmatch)
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from t21alib import *
import t21alib as _t21a

# ---- objects ------------------------------------------------------------------------------
E1 = '( 1 DChrLF ( 0g ` ( DChr ` 1 ) ) )'
U0 = '( 0g ` ( DChr ` N ) )'
U01 = '( 0g ` ( DChr ` 1 ) )'
NX = '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'
EN = '( N DChrLF X )'
HP0 = "( `' Re \" ( 0 (,) +oo ) )"
COND = '( N DChrCond X )'
PRIM = '( N DChrPrim X )'
CY = '( a e. NN |-> ( %s ` ( ( ZRHom ` ( Z/nZ ` %s ) ) ` a ) ) )' % (PRIM, COND)
DN = '{ x e. NN | x || N }'
F2931800 = '( ; ; 2 9 3 / ; ; ; 1 8 0 0 )'
F259900 = '( ; ; 2 5 9 / ; ; 9 0 0 )'
C12 = '; ; ; ; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0 0 0 0'          # 10^12 (ef6ef)
C13 = '; ; ; ; ; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0 0 0 0 0'      # 10^13 (cmbad)
C675 = '; ; ; ; ; ; ; ; ; ; ; ; ; ; 6 7 5 0 0 0 0 0 0 0 0 0 0 0 0'  # 675 . 10^12
C2T = '( ; 1 0 ^ ( ; 1 0 ^ ; 1 0 ) )'                              # censusC2 / ( nu + 2 )
N4320 = '; ; ; ; ; ; 4 3 2 0 0 0 0'
N50112 = '; ; ; ; 5 0 1 1 2'
N6912 = '; ; ; 6 9 1 2'


def PFX(z):
    """the Euler factor of X at the primitive character: sum_(d | N) mu(d) chi*(d) d^-z"""
    return 'sum_ d e. %s ( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u %s ) )' % (DN, CY, z)


def BOXV(s, v):
    return BOX(s, v)


def BC(s, v, m, y='y', o='o'):
    """Census badChars(s, v, m) (CEN2/CM letters y o)"""
    return ('{ %s e. ( Base ` ( DChr ` %s ) ) | ( ( %s DChrCond %s ) = %s /\\ { %s e. %s | ( %s =/= 1 /\\ ( ( %s DChrLF %s ) ` %s ) = 0 ) } =/= (/) ) }'
            % (y, m, m, y, m, o, BOX(s, v), o, m, y, o))


def BAD(z, s, v, y='y', e='e'):
    """badSet at x >= x2: the conductors e in [ 2 , floor z ] carrying a bad primitive character"""
    return '{ %s e. ( 2 ... ( |_ ` %s ) ) | %s =/= (/) }' % (e, z, BC(s, v, e, y))


def SC(e, t, y):
    """the zero sum of the explicit formula"""
    return 'sum_ q e. %s ( ( %s holord q ) x. ( ( %s ^c q ) / q ) )' % (ZF(e, HALF, t), e, y)


def EFERR(n, t, y):
    return ('( %s x. ( ( ( ( %s x. ( ( log ` ( ( %s x. %s ) x. %s ) ) ^ 2 ) ) / %s ) + ( ( %s ^c ( 5 / 8 ) ) x. ( ( log ` ( %s x. ( %s + 2 ) ) ) ^ 2 ) ) ) + ( ( log ` ( ( %s x. %s ) x. %s ) ) ^ 2 ) ) )'
            % (C12, y, n, t, y, t, y, n, t, n, t, y))


def OM(n):
    return '( # ` { p e. Prime | p || %s } )' % n


def SQL(y):
    return '( ( 2 x. ( sqrt ` %s ) ) x. ( log ` %s ) )' % (y, y)


def ZETA(u, v):
    return 'A. s e. CC ( ( ( %s <_ ( Re ` s ) /\\ ( Re ` s ) <_ 1 ) /\\ ( abs ` ( Im ` s ) ) <_ %s ) -> ( %s ` s ) =/= 0 )' % (u, v, E1)


def HBAD(z, s, v, n, y='y'):
    return 'A. i e. %s -. i || %s' % (BAD(z, s, v, y), n)


def HEMPTY(n, w, t, v):
    return 'A. y e. ( Base ` ( DChr ` %s ) ) A. p e. %s ( %s <_ ( Re ` p ) -> %s < ( abs ` ( Im ` p ) ) )' % (n, ZFo(HALF, w, n), t, v)


CSL = '( ; 5 0 x. ( ( K + 2 ) x. ( log ` %s ) ) )' % LX


def THR(X='X'):
    """the eight threshold conjuncts of theta_AP_T21 at the point X (multiplied out)"""
    lx = '( log ` %s )' % X
    csl = '( ; 5 0 x. ( ( K + 2 ) x. ( log ` %s ) ) )' % lx
    t1 = '( exp ` ; 1 0 ) <_ %s' % X
    t2 = '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( %s ^c %s ) )' % (C675, lx, X, F2931800)
    t3 = '( ; 8 1 x. %s ) <_ ( E x. ( %s ^c %s ) )' % (lx, X, F259900)
    t4 = '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( %s ^c %s ) )' % (N4320, lx, X, F7900)
    t5 = '( ( %s x. ( 5 ^ K ) ) x. H ) <_ ( E x. ( %s ^c %s ) )' % (N50112, lx, F92)
    t6 = '( ; 1 8 x. %s ) <_ %s' % (csl, lx)
    t7 = 'R <_ %s' % csl
    t8a = 'R <_ ( ( 1 - U ) x. %s )' % lx
    t8b = '( ; 4 0 x. R ) <_ %s' % lx
    return '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (t1, t2, t3, t4, t5, t6, t7, t8a, t8b)


TAUX = TAU
RHO = '( ( ; ; 2 0 0 / 9 ) x. ( log ` ( ( %s x. G ) / E ) ) )' % N6912
LFH = '( ( ( G e. RR /\\ 1 <_ G ) /\\ ( C e. RR /\\ 1 <_ C /\\ C <_ 2 ) ) /\\ %s )' % LFD_BODY('G', 'C')
LGH = '( ( ( H e. RR /\\ 1 <_ H ) /\\ ( P e. RR /\\ 0 <_ P /\\ P <_ ( 7 / 2 ) ) /\\ ( B e. RR /\\ 1 <_ B /\\ B <_ ( 5 / 4 ) ) ) /\\ ( K e. NN0 /\\ %s ) )' % LGD_BODY('H', 'P', 'B', 'K')
RVH = '( ( R e. RR+ /\\ V e. RR+ ) /\\ ( ( %s x. ( G x. ( exp ` ( -u %s x. R ) ) ) ) <_ E /\\ ( ; 2 7 x. ( G x. ( exp ` ( ; 2 8 x. R ) ) ) ) <_ ( E x. V ) ) )' % (N6912, F9200)
Z191 = '( X ^c %s )' % F191
SB = {}

# ---- the exceptional set and the zero transfer ----
SB['t21bcj'] = '%s = %s' % (BC('S', 'V', 'M'), BC('S', 'V', 'M', y='j'))
SB['t21lfp'] = '( ( %s /\\ S e. %s ) -> ( %s ` S ) = ( %s x. ( ( %s DChrLF %s ) ` S ) ) )' % (NX, HP0, EN, PFX('S'), COND, PRIM)
SB['t21pfne'] = '( ( %s /\\ ( S e. CC /\\ 0 < ( Re ` S ) ) ) -> %s =/= 0 )' % (NX, PFX('S'))
SB['t21nzb'] = ('( ( ( N e. NN /\\ ( T e. RR /\\ U e. RR /\\ U <_ T ) ) /\\ ( ( V e. RR /\\ W e. RR /\\ Z e. RR ) /\\ N <_ Z ) /\\ ( %s /\\ %s ) ) -> %s )'
                % (ZETA('U', 'V'), HBAD('Z', 'T', 'V', 'N', y='j'), HEMPTY('N', 'W', 'T', 'V')))
SB['t21card'] = ('( ( ( R e. RR+ /\\ ( V e. RR /\\ 1 <_ V ) ) /\\ ( X e. RR /\\ 1 < X /\\ 2 <_ %s ) /\\ ( ; 3 9 / ; 4 0 ) <_ %s ) -> ( # ` %s ) <_ ( ( %s x. ( V + 2 ) ) x. ( exp ` ( %s x. ( %s x. R ) ) ) ) )'
                 % (Z191, TAU, BAD(Z191, TAU, 'V'), C2T, F191, C13))

# ---- the explicit formula for every character ----
SB['t21zse'] = '( ( ( %s /\\ X = %s ) /\\ ( T e. RR /\\ Y e. CC ) ) -> %s = %s )' % (NX, U0, SC(EN, 'T', 'Y'), SC(E1, 'T', 'Y'))
SB['t21psd'] = ('( ( N e. NN /\\ ( Y e. RR /\\ 1 <_ Y ) ) -> ( abs ` ( ( %s ( psiChar ` N ) Y ) - ( %s ( psiChar ` 1 ) Y ) ) ) <_ ( %s x. ( log ` Y ) ) )'
                % (U0, U01, OM('N')))
EFH = '( ( Y e. RR /\\ ; ; 1 0 0 <_ Y ) /\\ ( T e. RR /\\ 2 <_ T ) /\\ N <_ Y )'
SB['t21efa'] = ('( ( %s /\\ %s ) -> ( abs ` ( ( ( X ( psiChar ` N ) Y ) - if ( X = %s , Y , 0 ) ) + %s ) ) <_ ( %s + ( %s x. ( log ` Y ) ) ) )'
                % (NX, EFH, U0, SC(EN, 'T', 'Y'), EFERR('N', 'T', 'Y'), OM('N')))

# ---- orthogonality ----
SB['t21nzs'] = ('( ( %s /\\ ( T e. RR /\\ Y e. RR+ ) ) -> ( abs ` %s ) <_ ( 3 x. sum_ q e. %s ( %s x. ( Y ^c ( Re ` q ) ) ) ) )'
                % (NX, SC(EN, 'T', 'Y'), ZF(EN, HALF, 'T'), WT(EN)))
AH = '( N e. NN /\\ A e. ZZ /\\ ( A gcd N ) = 1 )'
ERRS = '( ( %s + ( %s x. ( log ` Y ) ) ) + ( ( 3 / ( phi ` N ) ) x. %s ) )' % (EFERR('N', 'T', 'Y'), OM('N'), ZT('T', 'Y', HALF))
SB['t21psi'] = '( ( %s /\\ %s ) -> ( abs ` ( ( A ( psiAP ` N ) Y ) - ( Y / ( phi ` N ) ) ) ) <_ %s )' % (AH, EFH, ERRS)
SB['t21tha'] = '( ( %s /\\ %s ) -> ( abs ` ( ( A ( thetaAP ` N ) Y ) - ( Y / ( phi ` N ) ) ) ) <_ ( %s + %s ) )' % (AH, EFH, ERRS, SQL('Y'))

# ---- truncation and the small terms at T = X^3 ----
SB['t21om'] = '( N e. NN -> %s <_ N )' % OM('N')
SB['t21efe'] = ('( ( ( N e. NN /\\ %s ) /\\ ( ( Y e. RR /\\ %s ) /\\ Y <_ X ) /\\ ( ( E e. RR /\\ 0 < E ) /\\ ( %s x. ( %s ^ 2 ) ) <_ ( E x. ( X ^c %s ) ) ) ) -> %s <_ ( ( ( E / 9 ) x. Y ) / N ) )'
                % (XE, LEVEL, C675, LX, F2931800, EFERR('N', X3, 'Y')))
SB['t21sm'] = ('( ( ( N e. NN /\\ %s ) /\\ ( ( Y e. RR /\\ %s ) /\\ Y <_ X ) /\\ ( ( E e. RR /\\ 0 < E ) /\\ ( ; 8 1 x. %s ) <_ ( E x. ( X ^c %s ) ) ) ) -> ( ( %s x. ( log ` Y ) ) + %s ) <_ ( ( ( ( 2 x. E ) / ; 2 7 ) x. Y ) / N ) )'
               % (XE, LEVEL, LX, F259900, OM('N'), SQL('Y')))

# ---- thresholds ----
EV = lambda f: 'E. b e. RR A. x e. RR ( b <_ x -> %s )' % f
SB['t21evan'] = '( ( %s /\\ %s ) -> %s )' % (EV('ph'), EV('ps'), EV('( ph /\\ ps )'))
SB['t21evmo'] = '( A. x e. RR ( ph -> ps ) -> ( %s -> %s ) )' % (EV('ph'), EV('ps'))
SB['t21evl2'] = '( ( A e. RR+ /\\ B e. RR+ /\\ R e. RR+ ) -> %s )' % EV('( A x. ( ( log ` x ) ^ 2 ) ) <_ ( B x. ( x ^c R ) )')
SB['t21evll'] = '( A e. RR+ -> %s )' % EV('( A x. ( log ` ( log ` x ) ) ) <_ ( log ` x )')
SB['t21evlg'] = '( A e. RR -> %s )' % EV('( A <_ ( log ` x ) /\\ A <_ ( log ` ( log ` x ) ) /\\ A <_ ( ( log ` x ) ^c %s ) )' % F92)
SB['t21thr'] = '( ( ( E e. RR+ /\\ K e. NN0 /\\ H e. RR ) /\\ ( R e. RR+ /\\ U e. RR /\\ U < 1 ) ) -> %s )' % EV(THR('x'))

# ---- assembly ----
T4X = '( %s x. ( %s ^ 2 ) ) <_ ( E x. ( X ^c %s ) )' % (N4320, LX, F7900)
T5X = '( ( %s x. ( 5 ^ K ) ) x. H ) <_ ( E x. ( %s ^c %s ) )' % (N50112, LX, F92)
T6X = '( ; 1 8 x. %s ) <_ %s' % (CSL, LX)
SB['t21zt'] = ('( ( ( ( N e. NN /\\ %s ) /\\ ( ( Y e. RR /\\ %s ) /\\ Y <_ X ) /\\ ( E e. RR /\\ 0 < E ) ) /\\ ( %s /\\ %s /\\ %s ) /\\ ( ( %s /\\ %s /\\ %s ) /\\ ( ( R <_ %s /\\ ( ; 4 0 x. R ) <_ %s ) /\\ %s ) ) ) -> %s <_ ( ( 4 x. ( E x. Y ) ) / ; 2 7 ) )'
               % (XE, LEVEL, LFH, LGH, RVH, T4X, T5X, T6X, CSL, LX, HEMPTY('N', X3, TAU, 'V'), ZT(X3, 'Y', HALF)))
SB['t21pt'] = ('( ( ( ( E e. RR /\\ 0 < E ) /\\ %s /\\ %s ) /\\ ( %s /\\ ( ( X e. RR /\\ %s ) /\\ ( U e. RR /\\ %s ) ) ) /\\ ( %s /\\ ( ( Y e. RR /\\ %s ) /\\ Y <_ X ) /\\ %s ) ) -> ( abs ` ( ( A ( thetaAP ` N ) Y ) - ( Y / ( phi ` N ) ) ) ) <_ ( ( E x. Y ) / ( phi ` N ) ) )'
               % (LFH, LGH, RVH, THR('X'), ZETA('U', 'V'), AH, LEVEL, HBAD(Z191, TAU, 'V', 'N')))

L191 = '( l ^c %s )' % F191
L709 = '( l ^c %s )' % F709
TAUL = '( 1 - ( R / ( log ` l ) ) )'
FBAD = '( l e. NN0 |-> if ( b <_ l , %s , (/) ) )'   # R V filled by the proof


def GOAL(E_='E'):
    return ('E. j e. NN0 E. b e. RR E. f ( f : NN0 --> ( ~P NN i^i Fin ) /\\ ( A. l e. NN0 ( # ` ( f ` l ) ) <_ j /\\ A. l e. NN0 A. i e. ( f ` l ) 2 <_ i ) /\\ '
            'A. l e. NN0 A. d e. NN A. a e. ZZ A. z e. RR ( ( ( b <_ l /\\ ( a gcd d ) = 1 ) /\\ ( d <_ %s /\\ ( d x. %s ) <_ z /\\ z <_ l ) /\\ A. i e. ( f ` l ) -. i || d ) -> '
            '( abs ` ( ( a ( thetaAP ` d ) z ) - ( z / ( phi ` d ) ) ) ) <_ ( ( %s x. z ) / ( phi ` d ) ) ) )' % (L191, L709, E_))


EH = '( E e. RR /\\ 0 < E /\\ E < ( 1 / 3 ) )'
LFC = '( ( G e. RR /\\ C e. RR ) /\\ ( 1 <_ G /\\ 1 <_ C /\\ C <_ 2 ) /\\ A. m e. NN %s )' % LFD_BODY('G', 'C', 'm')
LGC = ('( ( ( H e. RR /\\ P e. RR /\\ B e. RR ) /\\ K e. NN0 ) /\\ ( ( 1 <_ H /\\ 0 <_ P /\\ P <_ ( 7 / 2 ) ) /\\ ( 1 <_ B /\\ B <_ ( 5 / 4 ) ) ) /\\ A. m e. NN %s )'
       % LGD_BODY('H', 'P', 'B', 'K', 'm'))
SB['t21cor'] = '( ( ( %s /\\ %s ) /\\ %s ) -> %s )' % (LFC, LGC, EH, GOAL())
SB['t21thm'] = '( ( ( %s /\\ %s ) /\\ %s ) -> %s )' % (LOGFREE, LOGGED, EH, GOAL())

# ---- constants and the exceptional-set function (helpers of t21cor) ----
E28R = '( exp ` ( ; 2 8 x. %s ) )' % RHO
VV = '( ( ; 2 7 x. ( G x. %s ) ) / E )' % E28R
SB['t21rv'] = ('( ( ( G e. RR /\\ 1 <_ G ) /\\ %s ) -> ( ( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( ( %s x. ( G x. ( exp ` ( -u %s x. %s ) ) ) ) <_ E /\\ ( ; 2 7 x. ( G x. %s ) ) <_ ( E x. %s ) ) ) /\\ 1 <_ %s ) )'
               % ('( E e. RR /\\ 0 < E /\\ E < ( 1 / 3 ) )', RHO, VV, N6912, F9200, RHO, E28R, VV, VV))
TAUl = '( 1 - ( R / ( log ` l ) ) )'
TAUk = '( 1 - ( R / ( log ` k ) ) )'
FF = '( k e. NN0 |-> if ( b <_ k , %s , (/) ) )' % BAD('( k ^c %s )' % F191, TAUk, 'V')
D0 = '( ( %s x. ( V + 2 ) ) x. ( exp ` ( %s x. ( %s x. R ) ) ) )' % (C2T, F191, C13)
SB['t21bf'] = ('( ( ( R e. RR+ /\\ ( V e. RR /\\ 1 <_ V ) ) /\\ ( b e. RR /\\ A. x e. RR ( b <_ x -> ( ( exp ` ; 1 0 ) <_ x /\\ ( ; 4 0 x. R ) <_ ( log ` x ) ) ) ) ) -> ( ( |^ ` %s ) e. NN0 /\\ %s : NN0 --> ( ~P NN i^i Fin ) /\\ ( A. l e. NN0 ( # ` ( %s ` l ) ) <_ ( |^ ` %s ) /\\ A. l e. NN0 A. i e. ( %s ` l ) 2 <_ i ) ) )'
               % (D0, FF, FF, D0, FF))

HYPS = {}


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 't21bgc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'gc%s.mmp' % lab)
        hy = HYPS.get(lab, {})
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for i in sorted(hy):
                f.write('h%d::gc%s.%d |- %s\n' % (i + 1, lab, i, hy[i]))
            f.write('h1::gc%s.99 |- %s\n' % (lab, SB[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % SB[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
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
        for lab in SB:
            print('| `%s` | `%s` |' % (lab, SB[lab]))
    elif 'check' in sys.argv:
        check(sys.argv[2:] or list(SB))
