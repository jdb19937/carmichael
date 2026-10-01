"""Sortie ZD2: ZeroDensity.lean remainder (sections 2-5 and 7 at the objects of Z5a, GF2, ZR,
ZC1, ZBV), ending in `zd2lfl` = `logfree_of_logged` : ( LOGGED -> LOGFREE ) with the texts of
tools/zdilib.py VERBATIM.  Built on tools/zrlib.py (REP objects) and tools/gf2lib.py (Gram objects).

    python3 tools/zd2lib.py print                                   # the frozen table
    MM_DB=sorties/zd2.mm python3 tools/zd2lib.py check [LABEL...]   # grammar check (mmatch)

Letters.  Objects: x (characters), q (zeros), r (ZF binder), v (cell binder), p (repIndex
binder), n (the Dirichlet series), a (the character function of FDet), j k (the Gram double
sum), m (gf2row's band index), z (the chi_0 clause of HGOOD), f (the selector chosen by
ac6sfi), u v (zdthresh/zdband quantifiers).  Frozen quantified forms: n t s (modulus,
height, abscissa), existentials a b (Theorem M: gamma_m, D_0) and d (Theorem Z: gamma_zeta).
The interface letters m v u y p o g c h w k (tools/zdilib.py) meet the others only in
`zd2lfl`, where the point instances are converted x q r <-> y p o by closed cbv equalities.
Scale D = ( N x. ( T + 2 ) ) is written out (DSC), as ZR and Z5a do.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
os.environ.setdefault('MM_DB', 'sorties/zd2.mm')
from zrlib import *
import zrlib as _zr
import gf2lib as G2
from t21alib import LOGFREE, LOGGED, LFD_BODY, LGD_BODY, NCo, ZFo

DB = os.environ.get('MM_DB', 'sorties/zd2.mm')


def stmt(label):
    """the assertion of LABEL from sorties/zd2.mm or carmichael.mm, without |-"""
    for fn in ('sorties/zd2.mm', 'carmichael.mm'):
        p = os.path.join(HERE, '..', fn)
        if not os.path.exists(p):
            continue
        txt = open(p).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


_zr.stmt = stmt

# ---- numerals -------------------------------------------------------------------------------
C12 = '; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0'          # C12 = 10^9 (ZD1)
N3200 = '; ; ; 3 2 0 0'
N320000 = '; ; ; ; ; 3 2 0 0 0 0'
N6400 = '; ; ; 6 4 0 0'                                # ZC1's box count (Lean 1120)
N400 = '; ; 4 0 0'
N20 = '; 2 0'
F52 = '( 5 / 2 )'
F92 = '( 9 / 2 )'
F99 = '( ; 9 9 / ; ; 1 0 0 )'
F3950 = '( ; 3 9 / ; 5 0 )'
F910 = '( 9 / ; 1 0 )'
CTAU = 'CTau'
C7 = G2.C7                                             # 8337480
C11 = G2.C11                                           # 2 10^12 CTau^3
C9K = G2.C9('K')                                       # ( ( K x. C7 ) x. ( 5 + 2 log 400 ) )
CJK = '( ( %s x. %s ) x. %s )' % (N3200, C12, C9K)     # Lean CJ CM = 3200 C12 C9 CM
GAMK = '( %s x. ( %s x. %s ) )' % (N20, CLOC, CJK)     # Lean gamM CM = 20 Cloc CJ CM (zdgood's form)
CMX = ante_of(stmt('zdmert'))[1].split(' <_ ( ', 1)[1].split(' x. ( log')[0]   # ZBV's Mertens constant
assert CMX.startswith('( exp ` (') and CMX.count('(') == CMX.count(')'), CMX
A1C = '( ( 2 x. ( ; 1 0 ^ ; 1 4 ) ) x. %s )' % CTAU    # T1's constant
B2C = '( ( %s x. %s ) x. %s )' % (N320000, C12, C11)   # T2's constant

# ---- the frozen parameters at D = N ( T + 2 ) ------------------------------------------------
DSC = '( N x. ( T + 2 ) )'
LD = '( log ` %s )' % DSC
atD = lambda text: tsub(text, {'D': DSC})
Z1D, Z2D, XPD, M0D, RPD, ELLD = [atD(t) for t in (G2.Z1, G2.Z2, G2.XP, G2.M0, G2.RP, G2.ELLD)]
PFD = '( N PFun %s )' % RPD
WFD = '( WWin ` <. %s , %s , %s >. )' % (M0D, XPD, ELLD)
BMD = '( %s bMaj %s )' % (PFD, WFD)
CDTD = '( <. %s , %s >. cDet <. %s , %s , S >. )' % (Z1D, Z2D, PFD, XPD)
QTD = lambda n: 'if ( ( %s ` %s ) = 0 , 0 , ( ( ( %s ` %s ) ^ 2 ) / ( %s ` %s ) ) )' % (BMD, n, CDTD, n, BMD, n)
SIG = 'sum_ n e. NN %s' % QTD('n')
ZRN = lambda a: '( ( ZRHom ` ( Z/nZ ` N ) ) ` %s )' % a
BGXD = lambda X, W: 'sum_ n e. NN ( ( ( %s ` n ) x. ( %s ` %s ) ) x. ( n ^c -u %s ) )' % (BMD, X, ZRN('n'), W)
MAIND = lambda W: atD(G2.MAIN(W))
XBD = '( %s ^c ( 2 - ( 2 x. S ) ) )' % XPD
QRPD = atD(G2.QRP)
MERTD = atD(G2.MERT)
MERTH = '( K e. RR /\\ %s <_ ( K x. ( log ` %s ) ) )' % (MERTD, RPD)
CREM = '( ( %s x. ( %s ^ 3 ) ) x. ( %s ^c -u ( 7 / ; ; 1 0 0 ) ) )' % (C11, LD, DSC)
ROW = '( ( ( %s x. ( %s ^ 2 ) ) x. ( 1 / ; ; 1 0 0 ) ) x. ( %s ^ 2 ) )' % (C9K, QRPD, LD)
T2G = '( %s x. %s ) <_ ( %s ^c ( ; 1 3 / ; ; 5 0 0 ) )' % (B2C, LD, DSC)
DPOW = '( %s ^c ( %s x. ( 1 - S ) ) )' % (DSC, F52)
TPOW = '( ( T + 2 ) ^c ( %s x. ( 1 - S ) ) )' % F52
VDET = '( ( ( 1 / %s ) x. %s ) x. %s )' % (N400, QRPD, LD)

# ---- the parity system with a selector H (ZR's RI, CELL) -----------------------------------
CHJ = lambda j: '( a e. NN |-> ( ( 1st ` %s ) ` %s ) )' % (j, ZRN('a'))
FDJ = lambda j: '( ( <. %s , %s >. FDet <. %s , %s , %s >. ) ` ( H ` %s ) )' % (Z1D, Z2D, PFD, XPD, CHJ(j), j)
XJK = lambda j, k: '( ( 1st ` %s ) ( +g ` ( DChr ` N ) ) ( ( invg ` ( DChr ` N ) ) ` ( 1st ` %s ) ) )' % (j, k)
SJK = lambda j, k: '( ( ( H ` %s ) - S ) + ( * ` ( ( H ` %s ) - S ) ) )' % (j, k)
HSEL = 'A. q e. %s ( H ` q ) e. %s' % (RI('P'), CELL('( 1st ` q )', '( 2nd ` q )'))
X0 = '( 0g ` ( DChr ` N ) )'
DB_N = '( Base ` ( DChr ` N ) )'

# ---- box sums (ZC1's rendering, letters x q r) -------------------------------------------------
ZC1_ = lambda s, t: 'sum_ q e. %s ( %s holord q )' % (ZF(E1, s, t), E1)            # zeroCountBox 1 s t
EXN = lambda n, x: '( %s DChrLF %s )' % (n, x)
ZCX = lambda n, x, s, t: 'sum_ q e. %s ( %s holord q )' % (ZF(EXN(n, x), s, t), EXN(n, x))
ZC0 = lambda n, s, t: ZCX(n, '( 0g ` ( DChr ` %s ) )' % n, s, t)                    # the principal character mod n
NC = lambda n, s, t: 'sum_ x e. ( Base ` ( DChr ` %s ) ) %s' % (n, ZCX(n, 'x', s, t))
NCNP = lambda n, s, t: 'sum_ x e. ( ( Base ` ( DChr ` %s ) ) \\ { ( 0g ` ( DChr ` %s ) ) } ) %s' % (n, n, ZCX(n, 'x', s, t))

# ---- hypothesis blocks -------------------------------------------------------------------------
NYS = '( ( N e. NN /\\ Y C_ %s ) /\\ ( %s /\\ %s ) )' % (DB_N, SS, TT)
THR = '( ( ; ; 2 0 0 <_ %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (LD, T1G, T2G, HGOOD)
MK = '( ( K e. RR /\\ 0 <_ K ) /\\ %s <_ ( K x. ( log ` %s ) ) )' % (MERTD, RPD)
PT = '( ( 2 <_ T /\\ ( %s <_ S /\\ S <_ 1 ) ) /\\ b <_ %s )' % (F99, DSC)
PTZ = '( 2 <_ T /\\ ( %s <_ S /\\ S <_ 1 ) )' % F99

S = {}
# ---- closure of Detector's PhiR (a sum binding r: proved under a clean antecedent) ----------------
S['zd2phic'] = '( ( N e. NN /\\ R e. RR ) -> %s e. CC )' % G2.PHI('N', 'R')
# ---- the Gram argument (Lean gramArg_re, gramArg_im, gramArg_re_bounds, gramArg_height) ----------
NYP = '( %s /\\ ( P e. RR /\\ %s ) )' % (NYS, HSEL)
GARG = ('( ( %s e. %s /\\ ( %s = %s <-> ( 1st ` B ) = ( 1st ` A ) ) ) /\\ ( ( %s e. CC /\\ ( 0 <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ ( 1 / ; 5 0 ) ) ) /\\ '
        '( ( Im ` %s ) = ( ( Im ` ( H ` A ) ) - ( Im ` ( H ` B ) ) ) /\\ ( N x. ( ( abs ` ( Im ` %s ) ) + 2 ) ) <_ ( 2 x. %s ) ) ) )') % (
    XJK('A', 'B'), DB_N, XJK('A', 'B'), X0, SJK('A', 'B'), SJK('A', 'B'), SJK('A', 'B'), SJK('A', 'B'), SJK('A', 'B'), DSC)
S['zd2garg'] = '( ( %s /\\ ( A e. %s /\\ B e. %s ) ) -> %s )' % (NYP, RI('P'), RI('P'), GARG)
# ---- one Gram term (Lean gram_row_le's hterm: gf2bt with the principal residue as an if) ---------
S['zd2gterm'] = ('( ( ( %s /\\ 2 <_ %s ) /\\ ( A e. %s /\\ B e. %s ) ) -> ( abs ` %s ) <_ ( if ( ( 1st ` B ) = ( 1st ` A ) , ( abs ` %s ) , 0 ) + %s ) )') % (
    NYP, LD, RI('P'), RI('P'), BGXD(XJK('A', 'B'), SJK('A', 'B')), MAIND(SJK('A', 'B')), CREM)
# ---- the parity system with its innermost binder renamed r -> b (gf2row forbids r in its set) -----
RIB = lambda P: tsub(RI(P), {'r': 'b'})
FS = lambda J: '{ j e. %s | ( 1st ` j ) = ( 1st ` %s ) }' % (RI('P'), J)        # the indices with the character of J
FSB = lambda J: '{ j e. %s | ( 1st ` j ) = ( 1st ` %s ) }' % (RIB('P'), J)
S['zd2rib'] = '%s = %s' % (RIB('P'), RI('P'))
# ---- the main-term row (Lean gram_row_le's hrow: row_sum_le on the indices with the character of J)
S['zd2grow'] = '( ( ( %s /\\ ( ( 2 <_ %s /\\ %s ) /\\ ( P e. RR /\\ %s ) ) ) /\\ J e. %s ) -> sum_ k e. %s ( abs ` %s ) <_ %s )' % (
    NYS, LD, MERTH, HSEL, RI('P'), FS('J'), MAIND(SJK('J', 'k')), ROW)
# ---- the Gram row (Lean gram_row_le, with gramArg_re_bounds / gramArg_height inside) -------------
S['zd2gram'] = ('( ( ( %s /\\ ( ( 2 <_ %s /\\ %s ) /\\ ( P e. RR /\\ %s ) ) ) /\\ J e. %s ) -> '
                'sum_ k e. %s ( abs ` %s ) <_ ( %s + ( ( # ` %s ) x. %s ) ) )') % (
    NYS, LD, MERTH, HSEL, RI('P'), RI('P'), BGXD(XJK('J', 'k'), SJK('J', 'k')), ROW, RI('P'), CREM)
# ---- Theorem 8.3's inputs: the diagonal, the (T2) absorption, the detection at a representative, the double sum
S['zd2sig'] = '( ( ( N e. NN /\\ ( %s /\\ %s ) ) /\\ ; ; 2 0 0 <_ %s ) -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s <_ ( %s x. %s ) ) )' % (SS, TT, LD, SIG, SIG, SIG, C12, XBD)
S['zd2hb'] = '( ( ( N e. NN /\\ ( %s /\\ %s ) ) /\\ ( ; ; 2 0 0 <_ %s /\\ %s ) ) -> ( ( %s x. %s ) x. %s ) <_ ( ( %s ^ 2 ) / 2 ) )' % (SS, TT, LD, T2G, C12, XBD, CREM, VDET)
S['zd2det'] = ('( ( ( %s /\\ ( ( ; ; 2 0 0 <_ %s /\\ %s ) /\\ %s ) ) /\\ ( ( P e. RR /\\ %s ) /\\ J e. %s ) ) -> '
               '( ( ( H ` J ) e. CC /\\ S <_ ( Re ` ( H ` J ) ) ) /\\ ( %s e. CC /\\ %s <_ ( abs ` %s ) ) ) )') % (NYS, LD, T1G, HGOOD, HSEL, RI('P'), FDJ('J'), VDET, FDJ('J'))
DBL = 'sum_ j e. %s sum_ k e. %s ( abs ` %s )' % (RI('P'), RI('P'), BGXD(XJK('j', 'k'), SJK('j', 'k')))
S['zd2dbl'] = '( ( %s /\\ ( ( 2 <_ %s /\\ %s ) /\\ ( P e. RR /\\ %s ) ) ) -> %s <_ ( ( # ` %s ) x. ( %s + ( ( # ` %s ) x. %s ) ) ) )' % (NYS, LD, MERTH, HSEL, DBL, RI('P'), ROW, RI('P'), CREM)
# ---- Theorem 8.3 (Lean card_paritySystem_le): with a selector, then the selector chosen -----------
S['zd2cpsh'] = '( ( ( %s /\\ %s /\\ %s ) /\\ ( P e. RR /\\ %s ) ) -> ( # ` %s ) <_ ( %s x. %s ) )' % (NYS, THR, MK, HSEL, RI('P'), CJK, XBD)
S['zd2cps'] = '( ( ( %s /\\ %s /\\ %s ) /\\ P e. RR ) -> ( # ` %s ) <_ ( %s x. %s ) )' % (NYS, THR, MK, RI('P'), CJK, XBD)
# ---- Corollary 8.4 (Lean sum_good_le_density) ------------------------------------------------------
S['zd2good'] = '( ( %s /\\ %s /\\ %s ) -> %s <_ ( %s x. %s ) )' % (NYS, THR, MK, GOODS('Y'), GAMK, DPOW)
# ---- Theorem M with thresholds (Lean sum_zeroCountBox_nonprincipal_le_of_thresholds) --------------
THR0 = '( ( ; ; 2 0 0 <_ %s /\\ %s ) /\\ %s )' % (LD, T1G, T2G)
S['zd2mthr'] = '( ( ( N e. NN /\\ ( %s /\\ %s ) ) /\\ %s /\\ %s ) -> %s <_ ( %s x. %s ) )' % (SS, TT, THR0, MK, NCNP('N', 'S', 'T'), GAMK, DPOW)
# ---- the thresholds (Lean thresholds_eventually at the two constants) ------------------------------
S['zd2thr'] = ('E. u e. RR ( 1 <_ u /\\ A. v e. RR ( u <_ v -> ( ; ; 2 0 0 <_ ( log ` v ) /\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 7 9 / ; ; ; 4 0 0 0 ) ) '
                '/\\ ( %s x. ( log ` v ) ) <_ ( v ^c ( ; 1 3 / ; ; 5 0 0 ) ) ) ) )') % (A1C, B2C)
# ---- Theorem M, unconditional frozen form (Lean sum_zeroCountBox_nonprincipal_le) -----------------
MBODY = lambda n, t, s: ('( ( ( 2 <_ %s /\\ ( %s <_ %s /\\ %s <_ 1 ) ) /\\ b <_ ( %s x. ( %s + 2 ) ) ) -> %s <_ ( a x. ( ( %s x. ( %s + 2 ) ) ^c ( %s x. ( 1 - %s ) ) ) ) )'
                         % (t, F99, s, s, n, t, NCNP(n, s, t), n, t, F52, s))
S['zd2thm'] = 'E. a E. b ( ( ( a e. RR /\\ 0 <_ a ) /\\ ( b e. RR /\\ 1 <_ b ) ) /\\ A. n e. NN A. t e. RR A. s e. RR %s )' % MBODY('n', 't', 's')
# ---- Theorem Z (Lean zeroCountBox_one_le_density_of_mertens, zeroCountBox_trivChar_le_density) -----
GLAM = '{ z e. CC | %s <_ ( abs ` ( Im ` z ) ) }' % LAMG                                     # good := Lambda0 <_ |Im|
LAMG1 = tsub(LAMG, {'N': '1'})
S['zd2zsm'] = ('( ( ( ( T e. RR /\\ 2 <_ T ) /\\ %s ) /\\ ( V e. RR /\\ ( T + 2 ) <_ V ) ) -> %s <_ ( %s x. ( V x. ( log ` ( V + 2 ) ) ) ) )'
               % (SS, ZC1_('S', 'T'), N6400))
ZBAND = lambda s, t: '{ v e. %s | ( abs ` ( Im ` v ) ) < %s }' % (ZF(E1, s, t), tsub(LAMG, {'N': '1'}))
ZGOOD = lambda s, t: '{ v e. %s | %s <_ ( abs ` ( Im ` v ) ) }' % (ZF(E1, s, t), tsub(LAMG, {'N': '1'}))
L1 = '( log ` ( 1 x. ( T + 2 ) ) )'
ZFREE = 'A. r e. CC ( ( %s ` r ) = 0 -> ( Re ` r ) < ( 1 - ( c / ( log ` ( ( abs ` ( Im ` r ) ) + 3 ) ) ) ) )' % E1
BANDH = '( ( log ` %s ) <_ ( %s / 4 ) /\\ ( ( log ` %s ) ^ 2 ) <_ ( ( c ^ 2 ) x. %s ) /\\ ( ( log ` ( ( %s x. ( exp ` 1 ) ) x. ; 6 0 ) ) + 3 ) <_ ( %s / 2 ) )' % (L1, L1, L1, L1, N3200, L1)
ZPH = '( ( ( T e. RR /\\ 2 <_ T ) /\\ %s ) /\\ ( ( c e. RR /\\ 0 < c ) /\\ ( ; ; 2 0 0 <_ %s /\\ %s ) ) )' % (SS, L1, BANDH)
S['zd2zbe'] = '( ( %s /\\ ( %s /\\ ( ( ( 1 - S ) x. %s ) ^ 2 ) <_ %s ) ) -> sum_ q e. %s ( %s holord q ) = 0 )' % (ZPH, ZFREE, L1, L1, ZBAND('S', 'T'), E1)
S['zd2zbc'] = '( ( %s /\\ %s < ( ( ( 1 - S ) x. %s ) ^ 2 ) ) -> sum_ q e. %s ( %s holord q ) <_ ( %s x. %s ) )' % (ZPH, L1, L1, ZBAND('S', 'T'), E1, N6400, TPOW)
THR1 = tsub(THR0, {'N': '1'})
MK1 = tsub(MK, {'N': '1'})
S['zd2zbg'] = '( ( ( ( T e. RR /\\ 2 <_ T ) /\\ %s ) /\\ %s /\\ %s ) -> sum_ q e. %s ( %s holord q ) <_ ( %s x. ( ( 1 x. ( T + 2 ) ) ^c ( %s x. ( 1 - S ) ) ) ) )' % (
    SS, THR1, MK1, ZGOOD('S', 'T'), E1, tsub(GAMK, {'N': '1'}), F52)
S['zd2zpt'] = '( ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) -> %s <_ ( ( %s + %s ) x. %s ) )' % (ZPH, ZFREE, THR1, MK1, ZC1_('S', 'T'), tsub(GAMK, {'N': '1'}), N6400, TPOW)
# ---- Theorem Z at a point with the constants as class variables (U = D_0, c = c_zeta, L = L_0, K = C_M)
V0 = 'if ( U <_ ( exp ` L ) , ( exp ` L ) , U )'
D0Z = '( ( ( 1 + ( %s x. ( %s x. ( log ` ( %s + 2 ) ) ) ) ) + %s ) + %s )' % (N6400, V0, V0, tsub(GAMK, {'N': '1'}), N6400)
D1 = '( 1 x. ( T + 2 ) )'
RPD1 = tsub(RPD, {'N': '1'}); MERT1 = tsub(MERTD, {'N': '1'})
THRC = '( U <_ %s -> ( ( ; ; 2 0 0 <_ %s /\\ %s /\\ %s ) /\\ %s <_ ( K x. ( log ` %s ) ) ) )' % (D1, L1, tsub(T1G, {'N': '1'}), tsub(T2G, {'N': '1'}), MERT1, RPD1)
BANDC = '( L <_ %s -> %s )' % (L1, BANDH)
S['zd2tzpt'] = ('( ( ( ( ( U e. RR /\\ 1 <_ U ) /\\ ( ( c e. RR /\\ 0 < c ) /\\ ( L e. RR /\\ ; ; 2 0 0 <_ L ) ) ) /\\ ( ( T e. RR /\\ 2 <_ T ) /\\ %s ) ) /\\ '
                 '( ( %s /\\ %s ) /\\ ( %s /\\ ( K e. RR /\\ 0 <_ K ) ) ) ) -> %s <_ ( %s x. %s ) )') % (SS, THRC, BANDC, ZFREE, ZC1_('S', 'T'), D0Z, TPOW)
ZBODY1 = lambda t, s: '( ( 2 <_ %s /\\ ( %s <_ %s /\\ %s <_ 1 ) ) -> %s <_ ( d x. ( ( %s + 2 ) ^c ( %s x. ( 1 - %s ) ) ) ) )' % (t, F99, s, s, ZC1_(s, t), t, F52, s)
S['zd2tz1'] = 'E. d ( ( d e. RR /\\ 1 <_ d ) /\\ A. t e. RR A. s e. RR %s )' % ZBODY1('t', 's')
ZBODY = lambda n, t, s: '( ( 2 <_ %s /\\ ( %s <_ %s /\\ %s <_ 1 ) ) -> %s <_ ( d x. ( ( %s + 2 ) ^c ( %s x. ( 1 - %s ) ) ) ) )' % (t, F99, s, s, ZC0(n, s, t), t, F52, s)
S['zd2tz'] = 'E. d ( ( d e. RR /\\ 1 <_ d ) /\\ A. n e. NN A. t e. RR A. s e. RR %s )' % ZBODY('n', 't', 's')
# ---- Theorem A (Lean sum_zeroCountBox_le_sq, theoremH, logfree_of_logged_of_mertens) ---------------
S['zd2split'] = '( ( N e. NN /\\ ( ( S e. RR /\\ 0 < S /\\ S <_ 1 ) /\\ T e. RR ) ) -> %s = ( %s + %s ) )' % (NC('N', 'S', 'T'), ZC0('N', 'S', 'T'), NCNP('N', 'S', 'T'))
S['zd2sq'] = '( ( N e. NN /\\ ( ( S e. RR /\\ ( 1 / 2 ) <_ S /\\ S <_ 1 ) /\\ ( T e. RR /\\ 1 <_ T ) ) ) -> %s <_ ( %s x. ( %s ^ 2 ) ) )' % (NC('N', 'S', 'T'), N6400, DSC)
EE = '( N x. ( T ^c C ) )'
EPOW = '( %s ^c ( %s x. ( 1 - S ) ) )' % (EE, F92)
GAM2 = '( ( ( 2 x. ( G + Z ) ) + ( %s x. ( E ^ 2 ) ) ) + ( ( H x. ( ( %s x. ( K + 1 ) ) ^ K ) ) + 1 ) )' % (N6400, N400)
HM = tsub(MBODY('N', 'T', 'S'), {'a': 'G', 'b': 'E'})
HZ = tsub(ZBODY('N', 'T', 'S'), {'d': 'Z'})
HH = '( ( 2 <_ T /\\ %s <_ S /\\ S <_ 1 ) -> %s <_ ( ( H x. ( %s ^c ( W x. ( 1 - S ) ) ) ) x. ( %s ^ K ) ) )' % (F3950, NC('N', 'S', 'T'), EE, LD)
CST = ('( ( ( ( H e. RR /\\ 1 <_ H ) /\\ ( W e. RR /\\ 0 <_ W /\\ W <_ ( 7 / 2 ) ) ) /\\ ( ( C e. RR /\\ 1 <_ C /\\ C <_ ( 5 / 4 ) ) /\\ K e. NN0 ) ) /\\ '
       '( ( G e. RR /\\ 0 <_ G ) /\\ ( ( E e. RR /\\ 1 <_ E ) /\\ ( Z e. RR /\\ 1 <_ Z ) ) ) )')
PTH = '( N e. NN /\\ ( ( T e. RR /\\ 2 <_ T ) /\\ ( S e. RR /\\ ( %s <_ S /\\ S <_ 1 ) ) ) )' % F910
S['zd2pt'] = '( ( ( %s /\\ %s ) /\\ ( %s /\\ ( %s /\\ %s ) ) ) -> %s <_ ( %s x. %s ) )' % (CST, PTH, HM, HZ, HH, NC('N', 'S', 'T'), GAM2, EPOW)
# ---- THE FROZEN OUTPUT (Lean logfree_of_logged): DensityInterface texts verbatim --------------------
S['zd2lfl'] = '( %s -> %s )' % (LOGGED, LOGFREE)

FROZEN = ['zd2thm', 'zd2tz', 'zd2lfl']
ORDER = ['zd2thr', 'zd2phic', 'zd2garg', 'zd2gterm', 'zd2rib', 'zd2grow', 'zd2gram', 'zd2sig', 'zd2hb', 'zd2det', 'zd2dbl', 'zd2cpsh', 'zd2cps', 'zd2good', 'zd2mthr', 'zd2thm',
         'zd2zsm', 'zd2zbe', 'zd2zbc', 'zd2zbg', 'zd2zpt', 'zd2tzpt', 'zd2tz1', 'zd2tz',
         'zd2split', 'zd2sq', 'zd2pt', 'zd2lfl']


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'zd2', 'gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'zd2gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=zd2gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::zd2gc%s.x |- %s\n' % (lab, S[lab]))
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
        for lab in ORDER:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or ORDER)
