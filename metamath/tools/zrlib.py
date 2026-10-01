"""Sortie ZR: helpers and the frozen statements (ZetaBox + ZetaZeroFree = ZZF; Representatives = REP).
Built on tools/ef56lib.py.

    python3 tools/zrlib.py print                                  # the frozen table
    MM_DB=sorties/zr.mm python3 tools/zrlib.py check [LABEL...]  # grammar check (mmatch)

Letters: ETA and GF bind z k; E1 = ( 1 DChrLF ( 0g ` ( DChr ` 1 ) ) ); DLAM binds k; the square zero set ZSE
binds r, its sums q; the headline existentials u (box abscissa), c (zero-free constant), x (Landau zero mass).
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from ef56lib import *
import ef56lib as _ef56
import ef4lib as _ef4
import ef3lib as _ef3
import ef2lib as _ef2
import zc1lib as _zc1
import c10lib as _c10
import ef1lib as _ef1


def stmt(label):
    """the assertion of LABEL from sorties/zr.mm or carmichael.mm, without |-"""
    for fn in ('sorties/zr.mm', 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if not os.path.exists(p):
            continue
        txt = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


for _m in (_ef56, _ef4, _ef3, _ef2, _c10, _zc1, _ef1):
    _m.stmt = stmt

# ---- objects -----------------------------------------------------------------------------
KL = '; ; ; ; ; ; ; 1 7 5 0 0 0 0 0'                   # Landau constant 17500000 (C10, NUMERALS row 1)
ZFK = '; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0'          # zfK = 10^9 (Lean 12 K + 112 at K = 520000)
ZFE = '( 1 / ( ; 3 1 x. %s ) )' % ZFK                 # zfE (Lean 1 / ( 7 zfK ))
DL = lambda s: 'sum_ k e. NN ( ( Lam ` k ) x. ( k ^c -u %s ) )' % s
SWT = lambda W, T: '( ( 1 + %s ) + ( _i x. %s ) )' % (W, T)
SW = SWT('W', 'T')
LT2 = lambda T: '( log ` ( ( abs ` %s ) + 2 ) )' % T
C2T = lambda T: '( 2 + ( _i x. %s ) )' % T
SQ13 = lambda T: '( ( %s - ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) ) crect ( %s + ( ( ; 1 3 / 8 ) + ( _i x. ( ; 1 3 / 8 ) ) ) ) )' % (C2T(T), C2T(T))
ZSE = lambda T: '{ r e. %s | ( %s ` r ) = 0 }' % (SQ13(T), ETA)
W20 = '( W e. RR+ /\\ W <_ ( 1 / ; 2 0 ) )'
WTT = '( W / ( ( W ^ 2 ) + ( T ^ 2 ) ) )'
GTERM = lambda S_: 'sum_ q e. %s ( Re ` ( ( ( %s holord q ) - if ( q = 1 , 1 , 0 ) ) / ( %s - q ) ) )' % (ZSE('T'), GF, S_)
TWOPI = '( _i x. ( 2 x. _pi ) )'

S = {}
# ---- ZZF: frozen headline statements (consumers ZD2 = ZeroDensity 1088, T21b = T21 1986) -------------
S['zrbox'] = ('( V e. RR+ -> E. u e. RR ( ( ( 1 / 2 ) <_ u /\\ u < 1 ) /\\ A. s e. CC ( ( ( u <_ ( Re ` s ) /\\ ( Re ` s ) <_ 1 ) '
              '/\\ ( abs ` ( Im ` s ) ) <_ V ) -> ( %s ` s ) =/= 0 ) ) )') % E1
S['zrzf'] = ('E. c e. RR ( ( 0 < c /\\ c <_ ( 1 / 2 ) ) /\\ A. r e. CC ( ( %s ` r ) = 0 -> '
             '( Re ` r ) < ( 1 - ( c / ( log ` ( ( abs ` ( Im ` r ) ) + 3 ) ) ) ) ) )') % E1
S['zrhi'] = ('( ( ( R e. CC /\\ ( %s ` R ) = 0 ) /\\ ( 2 <_ ( abs ` ( Im ` R ) ) /\\ ( 3 / 8 ) <_ ( Re ` R ) ) ) -> '
             '( Re ` R ) <_ ( 1 - ( %s / %s ) ) )') % (E1, ZFE, LT2('( Im ` R )'))
S['zrl1'] = '( ( T e. RR /\\ T =/= 0 ) -> ( %s ` ( 1 + ( _i x. T ) ) ) =/= 0 )' % E1
# ---- ZZF: internal statements ---------------------------------------------------------------------
S['zrisre'] = ('( ( F : NN --> CC /\\ seq 1 ( + , F ) e. dom ~~> ) -> ( ( Re ` sum_ k e. NN ( F ` k ) ) = '
               'sum_ k e. NN ( Re ` ( F ` k ) ) /\\ seq 1 ( + , ( Re o. F ) ) e. dom ~~> ) )')
S['zrsadd'] = ('( ( ( ( F : NN --> CC /\\ G : NN --> CC /\\ H : NN --> CC ) /\\ A. k e. NN ( H ` k ) = ( ( F ` k ) + ( G ` k ) ) ) /\\ '
               '( seq 1 ( + , F ) ~~> A /\\ seq 1 ( + , G ) ~~> B ) ) -> seq 1 ( + , H ) ~~> ( A + B ) )')
S['zrvmc'] = '( ( Z e. CC /\\ 1 < ( Re ` Z ) ) -> seq 1 ( + , ( n e. NN |-> ( ( Lam ` n ) x. ( n ^c -u Z ) ) ) ) e. dom ~~> )'
TK = lambda K, s: '( Re ` ( ( Lam ` %s ) x. ( %s ^c -u %s ) ) )' % (K, K, s)
X1, X2 = '( X + ( _i x. T ) )', '( X + ( _i x. ( 2 x. T ) ) )'
S['zr341t'] = '( ( K e. NN /\\ ( X e. RR /\\ T e. RR ) ) -> 0 <_ ( ( ( 3 x. %s ) + ( 4 x. %s ) ) + %s ) )' % (TK('K', 'X'), TK('K', X1), TK('K', X2))
S['zr341'] = ('( ( ( X e. RR /\\ 1 < X ) /\\ T e. RR ) -> 0 <_ ( ( ( 3 x. ( Re ` %s ) ) + ( 4 x. ( Re ` %s ) ) ) + ( Re ` %s ) ) )') % (DL('X'), DL(X1), DL(X2))
S['zrrec'] = '( ( Z e. CC /\\ Z =/= 0 ) -> ( Re ` ( 1 / Z ) ) = ( ( Re ` Z ) / ( ( abs ` Z ) ^ 2 ) ) )'
S['zrexp'] = ('( ( ( V e. CC /\\ V =/= 0 ) /\\ ( abs ` V ) <_ ( 9 / ; 1 0 ) ) -> '
              '( abs ` ( ( 1 / ( ( exp ` V ) - 1 ) ) - ( 1 / V ) ) ) <_ ; 1 0 )')
S['zrgv'] = ('( ( S e. CC /\\ 1 < ( Re ` S ) ) -> ( ( ( exp ` ( ( S - 1 ) x. ( log ` 2 ) ) ) - 1 ) =/= 0 /\\ '
             '%s = ( ( log ` 2 ) / ( ( exp ` ( ( S - 1 ) x. ( log ` 2 ) ) ) - 1 ) ) ) )') % LDF(GF, 'S')
S['zrzs'] = ('( ( T e. RR /\\ Q e. %s ) -> ( ( Q e. %s /\\ ( %s ` Q ) = 0 ) /\\ ( ( 3 / 8 ) <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 ) /\\ '
             '( abs ` ( ( Im ` Q ) - T ) ) <_ ( ; 1 3 / 8 ) ) )') % (ZSE('T'), HP0, ETA)
S['zrgq'] = ('( ( T e. RR /\\ %s ) -> ( Re ` %s ) <_ ( ( ; 1 0 + %s ) + %s ) )') % (W20, LDF(GF, SW), WTT, GTERM(SW))
S['zrlan'] = ('( ( T e. RR /\\ %s ) -> E. x e. RR ( ( 0 <_ x /\\ ( Re ` %s ) <_ ( ( ( %s x. %s ) + ( ; 1 0 + %s ) ) - x ) ) /\\ '
              'A. b e. RR ( ( ( ( 3 / 8 ) <_ b /\\ b <_ 1 ) /\\ ( %s ` ( b + ( _i x. T ) ) ) = 0 ) -> ( 1 / ( ( 1 + W ) - b ) ) <_ x ) ) )') % (
    W20, DL(SW), KL, LT2('T'), WTT, E1)
S['zrkey'] = ('( ( ( T e. RR /\\ T =/= 0 ) /\\ %s /\\ ( ( B e. RR /\\ ( ( 3 / 8 ) <_ B /\\ B <_ 1 ) ) /\\ ( %s ` ( B + ( _i x. T ) ) ) = 0 ) ) -> '
              '( 4 x. ( 1 / ( ( 1 + W ) - B ) ) ) <_ ( ( ( 3 x. ( ( 5 / 4 ) / W ) ) + ( ( 6 x. %s ) x. %s ) ) + ( ; 6 5 + ( 5 x. ( W / ( T ^ 2 ) ) ) ) ) )') % (
    W20, E1, KL, LT2('T'))
S['zre1n'] = '( ( S e. CC /\\ 1 < ( Re ` S ) ) -> ( %s ` S ) =/= 0 )' % E1

L2 = '( log ` 2 )'
PHI = lambda K: '( ( T x. %s ) - ( 2 x. ( _pi x. %s ) ) )' % (L2, K)
SK = lambda K: '( 1 + ( _i x. ( ( 2 x. ( _pi x. %s ) ) / %s ) ) )' % (K, L2)
EXL = lambda z: '( exp ` ( %s x. %s ) )' % (z, L2)
S['zrl2'] = '( ( 1 / 3 ) < %s /\\ %s < 1 )' % (L2, L2)
S['zrcos'] = '( ( P e. RR /\\ ( ( 1 / 2 ) <_ ( abs ` P ) /\\ ( abs ` P ) <_ _pi ) ) -> ( cos ` P ) < ( ; 1 1 / ; 1 2 ) )'
S['zrgvk'] = ('( ( ( T e. RR /\\ W e. RR ) /\\ K e. ZZ ) -> ( ( ( %s - %s ) x. %s ) = ( ( W x. %s ) + ( _i x. %s ) ) /\\ '
              '%s = %s ) )') % (SW, SK('K'), L2, L2, PHI('K'), EXL('( %s - 1 )' % SW), EXL('( %s - %s )' % (SW, SK('K'))))
S['zrgb'] = ('( ( ( T e. RR /\\ %s ) /\\ ( K e. ZZ /\\ ( ( 1 / 2 ) <_ ( abs ` %s ) /\\ ( abs ` %s ) <_ _pi ) ) ) -> ( Re ` %s ) <_ 0 )') % (
    W20, PHI('K'), PHI('K'), LDF(GF, SW))
S['zrga'] = ('( ( ( T e. RR /\\ %s ) /\\ ( K e. ZZ /\\ ( abs ` %s ) < ( 1 / 2 ) ) ) -> ( Re ` %s ) <_ ( ; 1 0 + ( Re ` ( 1 / ( %s - %s ) ) ) ) )') % (
    W20, PHI('K'), LDF(GF, SW), SW, SK('K'))
GORD = lambda Q: '( ( %s holord %s ) - if ( %s = 1 , 1 , 0 ) )' % (GF, Q, Q)
S['zrgnn'] = ('( ( ( T e. RR /\\ W e. RR+ ) /\\ Q e. %s ) -> ( %s e. NN0 /\\ 0 < ( Re ` ( %s - Q ) ) /\\ 0 <_ ( Re ` ( %s / ( %s - Q ) ) ) ) )') % (
    ZSE('T'), GORD('Q'), SW, GORD('Q'), SW)
S['zrgk'] = ('( ( ( T e. RR /\\ %s ) /\\ ( ( K e. ZZ /\\ K =/= 0 ) /\\ ( abs ` %s ) < ( 1 / 2 ) ) ) -> ( %s e. %s /\\ '
             '( Re ` ( 1 / ( %s - %s ) ) ) <_ ( Re ` ( %s / ( %s - %s ) ) ) ) )') % (W20, PHI('K'), SK('K'), ZSE('T'), SW, SK('K'), GORD(SK('K')), SW, SK('K'))
S['zrord'] = ('( ( ( %s /\\ ( F ` 2 ) =/= 0 ) /\\ P e. %s ) -> ( ( F holord P ) e. NN0 /\\ ( ( F ` P ) = 0 -> ( F holord P ) e. NN ) ) )') % (HOLF('F', HP0), HP0)
ZBX = lambda V: '{ r e. ( ( ( 1 / 2 ) + ( _i x. -u %s ) ) crect ( 1 + ( _i x. %s ) ) ) | ( r =/= 1 /\\ ( %s ` r ) = 0 ) }' % (V, V, E1)
S['zrbx'] = '( ( V e. RR+ /\\ R e. %s ) -> ( ( 1 / 2 ) <_ ( Re ` R ) /\\ ( Re ` R ) < 1 ) )' % ZBX('V')

# ---- REP: objects (Lean Representatives; d = N, sigma = S, t = T, good = the class G, chi = X or x in the set Y) ----
LD = '( log ` ( N x. ( T + 2 ) ) )'
EX = lambda x: '( N DChrLF %s )' % x
BOXR = '( ( S + ( _i x. -u T ) ) crect ( 1 + ( _i x. T ) ) )'
ZFX = lambda x: '{ r e. %s | ( r =/= 1 /\\ ( %s ` r ) = 0 ) }' % (BOXR, EX(x))
ORDX = lambda x, q: '( %s holord %s )' % (EX(x), q)
LCX = lambda x, g: 'sum_ q e. { v e. %s | ( abs ` ( ( Im ` v ) - %s ) ) <_ ( 1 / %s ) } %s' % (ZFX(x), g, LD, ORDX(x, 'q'))
IDX = lambda z: '( |_ ` ( ( ( Im ` %s ) + T ) x. %s ) )' % (z, LD)
QP = '( |_ ` ( ( 2 x. T ) x. %s ) )' % LD
CELL = lambda x, m: '{ v e. %s | ( v e. G /\\ %s = %s ) }' % (ZFX(x), IDX('v'), m)
RI = lambda P: '{ p e. ( Y X. ( 0 ... %s ) ) | ( %s =/= (/) /\\ ( ( 2nd ` p ) mod 2 ) = %s ) }' % (QP, CELL('( 1st ` p )', '( 2nd ` p )'), P)
CLOC = '( 5 x. ( 3 + %s ) )' % KL
LAM = '( ( 1 - S ) x. %s )' % LD
NX = '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )'
SS = '( S e. RR /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ S /\\ S <_ 1 ) )'
TT = '( T e. RR /\\ 0 <_ T )'
NY = '( ( N e. NN /\\ Y C_ ( Base ` ( DChr ` N ) ) ) /\\ Y e. Fin )'
GOODS = lambda Y: 'sum_ x e. %s sum_ q e. { v e. %s | v e. G } %s' % (Y, ZFX('x'), ORDX('x', 'q'))
JJ = '( ( # ` %s ) + ( # ` %s ) )' % (RI('0'), RI('1'))
S['zrscale'] = '( ( N e. NN /\\ ( T e. RR /\\ 0 <_ T ) ) -> ( 2 <_ ( N x. ( T + 2 ) ) /\\ 0 < %s ) )' % LD
S['zridx'] = ('( ( ( N e. NN /\\ ( T e. RR /\\ 0 <_ T ) ) /\\ ( Z e. CC /\\ ( abs ` ( Im ` Z ) ) <_ T ) ) -> ( ( %s e. NN0 /\\ %s <_ %s ) /\\ '
              '( %s <_ ( ( ( Im ` Z ) + T ) x. %s ) /\\ ( ( ( Im ` Z ) + T ) x. %s ) < ( %s + 1 ) ) ) )') % (IDX('Z'), IDX('Z'), QP, IDX('Z'), LD, LD, IDX('Z'))
S['zrlc'] = ('( ( %s /\\ ( %s /\\ %s ) /\\ ( ; 2 5 <_ %s /\\ ( U e. RR /\\ ( abs ` U ) <_ T ) ) ) -> %s <_ ( %s x. ( 1 + %s ) ) )') % (NX, SS, TT, LD, LCX('X', 'U'), CLOC, LAM)
S['zrcov'] = ('( ( ( %s /\\ ( ( S e. RR /\\ 0 < S /\\ S <_ 1 ) /\\ %s ) ) /\\ ( B e. RR /\\ A. x e. Y A. u e. RR ( ( abs ` u ) <_ T -> %s <_ B ) ) ) -> %s <_ ( B x. %s ) )') % (
    NY, TT, LCX('x', 'u'), GOODS('Y'), JJ)
S['zrsg'] = ('( ( %s /\\ ( %s /\\ %s ) /\\ ; 2 5 <_ %s ) -> %s <_ ( ( %s x. ( 1 + %s ) ) x. %s ) )') % (NY, SS, TT, LD, GOODS('Y'), CLOC, LAM, JJ)
S['zrsp'] = ('( ( ( ( ( N e. NN /\\ S e. RR ) /\\ %s ) /\\ ( P e. RR /\\ Q e. %s /\\ R e. %s ) ) /\\ ( ( ( 1st ` Q ) = ( 1st ` R ) /\\ Q =/= R ) /\\ ( A e. %s /\\ B e. %s ) ) ) -> '
             '( 1 / %s ) <_ ( abs ` ( ( Im ` A ) - ( Im ` B ) ) ) )') % (TT, RI('P'), RI('P'), CELL('( 1st ` Q )', '( 2nd ` Q )'), CELL('( 1st ` R )', '( 2nd ` R )'), LD)
BANDQ = lambda M: ('{ q e. %s | ( ( 1st ` q ) = ( 1st ` Q ) /\\ ( ( %s x. ( 1 / %s ) ) <_ ( abs ` ( ( Im ` ( H ` q ) ) - ( Im ` ( H ` Q ) ) ) ) /\\ '
                   '( abs ` ( ( Im ` ( H ` q ) ) - ( Im ` ( H ` Q ) ) ) ) < ( ( %s + 1 ) x. ( 1 / %s ) ) ) ) }') % (RI('P'), M, LD, M, LD)
S['zrband'] = ('( ( ( ( ( N e. NN /\\ S e. RR ) /\\ %s ) /\\ ( P e. RR /\\ Q e. %s ) ) /\\ ( A. q e. %s ( H ` q ) e. %s /\\ M e. NN0 ) ) -> ( # ` %s ) <_ 2 )') % (
    TT, RI('P'), RI('P'), CELL('( 1st ` q )', '( 2nd ` q )'), BANDQ('M'))
XSE = 'sum_ q e. %s ( Re ` ( ( %s holord q ) / ( %s - q ) ) )' % (ZSE('T'), E1, SW)
S['zrlanx'] = ('( ( T e. RR /\\ %s ) -> ( ( Re ` %s ) <_ ( ( ( %s x. %s ) + ( ; 1 0 + %s ) ) - %s ) /\\ 0 <_ %s ) )') % (W20, DL(SW), KL, LT2('T'), WTT, XSE, XSE)
DISK = lambda T, W: '{ p e. %s | ( abs ` ( p - ( 1 + ( _i x. %s ) ) ) ) <_ %s }' % (ZSE(T), T, W)
S['zrsdz'] = ('( ( T e. RR /\\ %s ) -> sum_ q e. %s ( %s holord q ) <_ ( ; 1 2 + ( ( ( 4 x. %s ) x. W ) x. %s ) ) )') % (W20, DISK('T', 'W'), E1, KL, LT2('T'))
S['zrwin'] = ('( ( ( S e. RR /\\ ( ; 9 9 / ; ; 1 0 0 ) <_ S ) /\\ ( T e. RR /\\ U e. RR /\\ E e. RR ) /\\ ( E <_ ( 1 / ; 2 5 ) /\\ ( V e. %s /\\ ( abs ` ( ( Im ` V ) - U ) ) <_ E ) ) ) -> '
             '( V e. %s /\\ ( abs ` ( V - ( 1 + ( _i x. U ) ) ) ) <_ ( ( 1 - S ) + E ) /\\ V e. %s ) )') % (BOXR, SQ13('U'), HP0)
ETAW = '( ( 1 - S ) + ( 1 / %s ) )' % LD
S['zrlc1'] = ('( ( ( %s /\\ X =/= ( 0g ` ( DChr ` N ) ) ) /\\ ( %s /\\ %s ) /\\ ( ; 2 5 <_ %s /\\ ( U e. RR /\\ ( abs ` U ) <_ T ) ) ) -> '
              '%s <_ ( 6 + ( ; ; ; ; ; ; ; 7 0 0 0 0 0 0 0 x. ( 1 + %s ) ) ) )') % (NX, SS, TT, LD, LCX('X', 'U'), LAM)
S['zrlc0'] = ('( ( ( %s /\\ X = ( 0g ` ( DChr ` N ) ) ) /\\ ( %s /\\ %s ) /\\ ( ; 2 5 <_ %s /\\ ( U e. RR /\\ ( abs ` U ) <_ T ) ) ) -> '
              '%s <_ ( ; 1 2 + ( ( 4 x. %s ) x. ( 1 + %s ) ) ) )') % (NX, SS, TT, LD, LCX('X', 'U'), KL, LAM)
PTB = lambda Z: '( %s e. CC /\\ ( abs ` ( Im ` %s ) ) <_ T )' % (Z, Z)
S['zrc2'] = ('( ( ( ( N e. NN /\\ %s ) /\\ %s /\\ %s ) /\\ ( %s + 2 ) <_ %s ) -> ( 1 / %s ) <_ ( ( Im ` B ) - ( Im ` A ) ) )') % (TT, PTB('A'), PTB('B'), IDX('A'), IDX('B'), LD)
S['zrc1'] = ('( ( ( ( N e. NN /\\ %s ) /\\ %s /\\ %s ) /\\ %s = %s ) -> ( abs ` ( ( Im ` A ) - ( Im ` B ) ) ) < ( 1 / %s ) )') % (TT, PTB('A'), PTB('B'), IDX('A'), IDX('B'), LD)
S['zrpar'] = '( ( ( M e. NN0 /\\ E e. ZZ ) /\\ ( ( E mod 2 ) = 0 /\\ ( ( M - 1 ) < E /\\ E < ( M + 2 ) ) ) ) -> E = ( M + ( M mod 2 ) ) )'
GX = lambda x: '{ v e. %s | v e. G }' % ZFX(x)
BOX01 = '( ( S e. RR /\\ 0 < S /\\ S <_ 1 ) /\\ %s )' % TT
S['zrfib'] = ('( ( %s /\\ %s ) -> sum_ q e. %s %s = sum_ m e. ( 0 ... %s ) sum_ q e. %s %s )') % (NX, BOX01, GX('X'), ORDX('X', 'q'), QP, CELL('X', 'm'), ORDX('X', 'q'))
S['zrcb'] = ('( ( ( %s /\\ %s ) /\\ ( ( B e. RR /\\ A. u e. RR ( ( abs ` u ) <_ T -> %s <_ B ) ) /\\ ( M e. ZZ /\\ %s =/= (/) ) ) ) -> sum_ q e. %s %s <_ B )') % (
    NX, BOX01, LCX('X', 'u'), CELL('X', 'M'), CELL('X', 'M'), ORDX('X', 'q'))
S['zrszc'] = ('( ( %s /\\ ( %s /\\ %s ) /\\ ; 2 5 <_ %s ) -> sum_ x e. Y sum_ q e. %s %s <_ ( ( %s x. ( 1 + %s ) ) x. %s ) )') % (
    NY, SS, TT, LD, ZFX('x'), ORDX('x', 'q'), CLOC, LAM, tsub(JJ, {'G': 'CC'}))
S['zrhalf'] = ('( ( ( F e. CC /\\ E e. CC ) /\\ ( P e. RR /\\ 0 <_ P ) /\\ ( Q e. RR /\\ ( ( 3 / 4 ) <_ Q /\\ ( ( abs ` ( ( F + ( Q x. P ) ) - E ) ) <_ ( P / 8 ) /\\ ( abs ` E ) <_ ( P / 8 ) ) ) ) ) -> '
               '( P / 2 ) <_ ( abs ` F ) )')
QRPD = lambda D: 'prod_ p e. { q e. Prime | ( q || N /\\ q <_ ( %s ^c ( 1 / ; ; 1 0 0 ) ) ) } ( 1 - ( 1 / p ) )' % D
_zl = stmt('zl3dlbz')
_zla, _zlc = ante_of(_zl)
PHIF = '( ( ( 1 / ; ; 4 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) )'
assert _zlc.startswith(PHIF + ' <_ ')
FDVX = _zlc[len(PHIF + ' <_ '):]
S['zrdet'] = '( %s -> ( ( ( 1 / ; ; 4 0 0 ) x. %s ) x. ( log ` D ) ) <_ %s )' % (_zla, QRPD('D'), FDVX)
EXQ = '( exp ` ( -u 1 / ( D ^c ( 6 / 5 ) ) ) )'
S['zrexq'] = '( ( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) ) -> ( %s e. RR /\\ ( 3 / 4 ) <_ %s ) )' % (EXQ, EXQ)
DSC = '( N x. ( T + 2 ) )'
LAMG = '( ( ( log ` ( log ` %s ) ) + ( ( 6 / 5 ) x. ( ( 1 - S ) x. ( log ` %s ) ) ) ) + ( log ` ( ( ; ; ; 3 2 0 0 x. ( exp ` 1 ) ) x. ; 6 0 ) ) )' % (DSC, DSC)
T1G = '( ( ( 2 x. ( ; 1 0 ^ ; 1 4 ) ) x. CTau ) x. %s ) <_ ( %s ^c ( ; 7 9 / ; ; ; 4 0 0 0 ) )' % (LD, DSC)
HGOOD = 'A. x e. Y ( x = ( 0g ` ( DChr ` N ) ) -> A. z e. G %s <_ ( abs ` ( Im ` z ) ) )' % LAMG
_dc = ante_of(S['zrdet'])[1]
S['zrdetg'] = ('( ( ( ( N e. NN /\\ Y C_ ( Base ` ( DChr ` N ) ) ) /\\ ( %s /\\ %s ) ) /\\ ( ( ; ; 2 0 0 <_ %s /\\ %s ) /\\ %s ) /\\ ( P e. RR /\\ Q e. %s /\\ A e. %s ) ) -> %s )') % (
    SS, TT, LD, T1G, HGOOD, RI('P'), CELL('( 1st ` Q )', '( 2nd ` Q )'), tsub(_dc, {'D': DSC, 'X': '( 1st ` Q )', 'S': 'A', 'T': 'S'}))
HYPS = {}
ORDER_ZZF = ['zrisre', 'zrvmc', 'zr341t', 'zr341', 'zrrec', 'zrexp', 'zrgv', 'zrzs', 'zrgq', 'zrlan', 'zrkey', 'zrl1', 'zre1n', 'zrhi', 'zrbox', 'zrzf']


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'zr', 'gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'zrgc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=zrgc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for i, (n, h) in enumerate(HYPS.get(lab, [])):
                f.write('h%d::zrgc%s.%s |- %s\n' % (i + 10, lab, n, h))
            f.write('h1::zrgc%s.x |- %s\n' % (lab, S[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
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
        for lab in S:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or list(S))
