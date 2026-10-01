"""Sortie Z6a helpers (Route Z: DetectionShift.lean).

STATEMENTS / HYPS / ORDER are the frozen statements of Z6a-blueprint.md, one
place, so that the blueprint, the grammar check and the generators cannot
drift apart.  Running `MM_DB=sorties/z6a.mm python3 tools/z6alib.py [LABEL...]`
grammar-checks them (mmj2 unify on a bare `qed` worksheet).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5dlib import *          # z5d/z5c/z5b/z5a/zd1 macros, W, mkst, a1, run helpers, ...
from z5dlib import STATEMENTS as Z5DS
from c0lib import hyp

# ------------------------------------------------------------------ objects
HPZ = "( `' Re \" ( 0 (,) +oo ) )"                    # C3's HP 0, the open right half-plane
HPT = lambda T: "( `' Re \" ( %s (,) +oo ) )" % T
DG = '( CC \\ ( ZZ \\ NN ) )'                          # the domain of _G
TPI = '( 2 x. ( _i x. _pi ) )'
KG = '( ( ; ; ; 1 0 2 4 x. ; ; ; 1 6 3 2 ) / ( log ` 2 ) )'   # the Gamma line moment on 1/100 <_ Re <_ 3 (gamlmom at H = 1632)
KGL = '( ( ; 5 0 / ; 4 9 ) x. %s )' % KG                     # the same on -99/100 <_ Re <_ -98/100 (functional equation)
E4 = lambda x: '( 2 ^c -u ( %s / 4 ) )' % x                  # 2 ^ ( - x / 4 )
E2 = lambda x: '( 2 ^c -u ( %s / 2 ) )' % x
LI = lambda G, c, t='t': '( %s lint <. ( %s + ( _i x. -u %s ) ) , ( %s + ( _i x. %s ) ) >. )' % (G, c, t, c, t)
VLF = lambda G, c: '( t e. RR+ |-> %s )' % LI(G, c)          # the truncated vertical line integrals, t -> +oo
VL = lambda G, c: '( ~~>r ` %s )' % VLF(G, c)                 # the vertical line integral int_(c) = _i int_RR G ( c + _i u ) du
GY = lambda Y='Y': '( w e. %s |-> ( ( _G ` w ) x. ( %s ^c -u w ) ) )' % (DG, Y)   # the Mellin integrand Gamma ( w ) Y ^ -w
MOM = lambda C, T='T': ('S. ( -u %s (,) %s ) ( ( abs ` ( _G ` ( %s + ( _i x. u ) ) ) ) x. ( ( 1 + ( abs ` u ) ) ^ 2 ) ) _d u' % (T, T, C))
MOMF = lambda C, T='T': ('( u e. ( -u %s (,) %s ) |-> ( ( abs ` ( _G ` ( %s + ( _i x. u ) ) ) ) x. ( ( 1 + ( abs ` u ) ) ^ 2 ) ) )' % (T, T, C))
GAMH1632 = ('A. d e. CC ( ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` d ) /\\ ( Re ` d ) <_ 3 ) -> '
            '( abs ` ( _G ` d ) ) <_ ( ; ; ; 1 6 3 2 x. ( 2 ^c -u ( ( abs ` ( Im ` d ) ) / 2 ) ) ) )')

# the L-function interface (section 0 of the blueprint): E is ( s - 1 ) L ( s , chi ), holomorphic on HP 0
PRN = PRIN('N')
RESV = 'if ( C = %s , ( ( phi ` N ) / N ) , 0 )' % PRN        # the residue of L ( s , chi ) at s = 1
OMG = lambda N='N': '( 2 ^ ( # ` { p e. Prime | p || %s } ) )' % N    # 2 ^ omega ( N )
CVXB = lambda s: ('( ( ; ; ; ; ; 2 0 0 0 0 0 x. %s ) x. ( ( ( ( N x. ( ( abs ` ( Im ` %s ) ) + 2 ) ) ^c if ( 1 <_ ( Re ` %s ) , 0 , ( ( 1 - ( Re ` %s ) ) / 2 ) ) ) '
                  'x. ( log ` ( N x. ( ( abs ` ( Im ` %s ) ) + 3 ) ) ) ) + ( 1 / ( abs ` ( %s - 1 ) ) ) ) )' % (OMG(), s, s, s, s, s))
CVXH = ('A. s e. %s ( ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` s ) /\\ ( Re ` s ) <_ 2 /\\ s =/= 1 ) -> ( abs ` ( ( E ` s ) / ( s - 1 ) ) ) <_ %s )'
        % (HPZ, CVXB('s')))
LSs = 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u s ) )'
DSER = 'A. s e. %s ( 1 < ( Re ` s ) -> ( E ` s ) = ( ( s - 1 ) x. %s ) )' % (HPZ, LSs)
EHOL = '( E e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D E ) )' % (HPZ, HPZ)
LIF = '( ( %s /\\ ( E ` 1 ) = %s ) /\\ ( %s /\\ %s ) )' % (EHOL, RESV, DSER, CVXH)

# the parameters at D (Detector.lean's z1par, z2par, Rpar, Xpar)
T1 = '( ( ( 2 x. ( ; 1 0 ^ ; 1 4 ) ) x. CTau ) x. ( log ` D ) ) <_ ( D ^c ( ; 7 9 / ; ; ; 4 0 0 0 ) )'
KPT = '( ( ( ; ; ; ; ; 6 0 0 0 0 0 x. CTau ) x. ( D ^c ( ; ; 3 9 7 / ; ; 8 0 0 ) ) ) x. ( log ` D ) )'   # the I1 constant on Re = 1/100
CL = '( ( 1 / ; ; 1 0 0 ) - ( Re ` S ) )'                   # the left contour line eps2 - beta
MRr = lambda r, s: '( ( <. %s , %s >. Mr <. C , %s >. ) ` %s )' % (Z1D, Z2D, r, s)
DS = "( %s i^i ( ( `' Re \" ( -u ( Re ` S ) (,) +oo ) ) \\ { ( 1 - S ) } ) )" % DG
GR = lambda r: ('( w e. %s |-> ( ( ( _G ` w ) x. ( %s ^c w ) ) x. ( ( ( E ` ( S + w ) ) / ( ( S + w ) - 1 ) ) x. %s ) ) )'
                % (DS, XPD, MRr(r, '( S + w )')))
ECTR = '( ( 1 / %s ) x. sum_ r e. ( N RSet %s ) ( ( 1 / r ) x. %s ) )' % (TPI, RPD, VL(GR('r'), CL))
FDV = '( ( <. %s , %s >. FDet <. ( N PFun %s ) , %s , C >. ) ` S )' % (Z1D, Z2D, RPD, XPD)
SRNG = '( S e. CC /\\ ( ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) )'
HDN = '( N x. ( ( abs ` ( Im ` S ) ) + 2 ) ) <_ D'
CHRB = '( %s /\\ %s )' % (CHR, CB)

STATEMENTS = {}
HYPS = {}

# ================================================================== section 1: the Mellin identity (DetectionShift 104-190)
# --- Gamma: values, the explicit strip constant, the line moments, holomorphy
STATEMENTS['z6gamre'] = '( ( X e. RR /\\ 0 < X /\\ X <_ 3 ) -> ( _G ` X ) <_ ( ( 1 / X ) + 2 ) )'
STATEMENTS['z6gam1632'] = GAMH1632
STATEMENTS['z6gmom'] = ('( ( ( C e. RR /\\ ( 1 / ; ; 1 0 0 ) <_ C /\\ C <_ 3 ) /\\ T e. RR+ ) -> ( %s e. L^1 /\\ %s <_ %s ) )'
                        % (MOMF('C'), MOM('C'), KG))
STATEMENTS['z6gmoml'] = ('( ( ( C e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ C /\\ C <_ -u ( ; 9 8 / ; ; 1 0 0 ) ) /\\ T e. RR+ ) -> ( %s e. L^1 /\\ %s <_ %s ) )'
                         % (MOMF('C'), MOM('C'), KGL))
STATEMENTS['z6gamfe'] = '( ( Z e. %s /\\ K e. NN0 ) -> ( _G ` ( Z + K ) ) = ( ( _G ` Z ) x. prod_ j e. ( 0 ..^ K ) ( Z + j ) ) )' % DG
STATEMENTS['z6gamhol'] = '( ( z e. %s |-> ( _G ` z ) ) e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D ( z e. %s |-> ( _G ` z ) ) ) )' % (HPZ, HPZ, HPZ, HPZ)
STATEMENTS['z6gamhold'] = '( ( z e. %s |-> ( _G ` z ) ) e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D ( z e. %s |-> ( _G ` z ) ) ) )' % (DG, DG, DG, DG)
# --- vertical line integrals as limits of lint over ( c - i t , c + i t )
STATEMENTS['z6lvert'] = ('( ( ( C e. RR /\\ T e. RR+ ) /\\ ( G e. ( D -cn-> CC ) /\\ ( ( C + ( _i x. -u T ) ) cseg ( C + ( _i x. T ) ) ) C_ D ) ) -> '
                         '( ( u e. ( -u T (,) T ) |-> ( G ` ( C + ( _i x. u ) ) ) ) e. L^1 /\\ %s = ( _i x. S. ( -u T (,) T ) ( G ` ( C + ( _i x. u ) ) ) _d u ) ) )'
                         % LI('G', 'C', 'T'))
STATEMENTS['z6rlimle'] = '( ( ( t e. RR+ |-> A ) ~~>r W /\\ ( B e. RR /\\ A. t e. RR+ ( abs ` A ) <_ B ) ) -> ( abs ` W ) <_ B )'
STATEMENTS['z6vlcvg'] = ('( ( ( C e. RR /\\ ( G e. ( D -cn-> CC ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. D ) ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ '
                         'A. u e. RR ( Y <_ ( abs ` u ) -> ( abs ` ( G ` ( C + ( _i x. u ) ) ) ) <_ ( M x. %s ) ) ) ) -> '
                         '( %s ~~>r %s /\\ A. t e. RR+ ( Y <_ t -> ( abs ` ( %s - %s ) ) <_ ( ( ( 8 x. M ) / ( log ` 2 ) ) x. %s ) ) ) )'
                         % (E4('( abs ` u )'), VLF('G', 'C'), VL('G', 'C'), VL('G', 'C'), LI('G', 'C'), E4('t')))
STATEMENTS['z6vleq'] = ('( ( ( C e. RR /\\ ( F e. V /\\ G e. W ) ) /\\ A. u e. RR ( F ` ( C + ( _i x. u ) ) ) = ( G ` ( C + ( _i x. u ) ) ) ) -> %s = %s )'
                        % (VL('F', 'C'), VL('G', 'C')))
STRIPD = ('A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ ( ( ( Re ` z ) = A \\/ ( Re ` z ) = B ) \\/ Y <_ ( abs ` ( Im ` z ) ) ) ) -> z e. D )')
STRIPM = ('A. z e. CC ( ( ( A <_ ( Re ` z ) /\\ ( Re ` z ) <_ B ) /\\ Y <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( G ` z ) ) <_ ( M x. %s ) )'
          % E4('( abs ` ( Im ` z ) )'))
STATEMENTS['z6shift'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ A < B ) /\\ ( ( G e. ( D -cn-> CC ) /\\ %s ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ %s ) ) /\\ '
                         '( K e. CC /\\ A. t e. RR+ ( Y <_ t -> ( G rectint <. ( A + ( _i x. -u t ) ) , ( B + ( _i x. t ) ) >. ) = K ) ) ) -> ( %s - %s ) = K )'
                         % (STRIPD, STRIPM, VL('G', 'B'), VL('G', 'A')))
# --- the Mellin identity by residues of Gamma ( w ) Y ^ -w at w = 0 , -1 , -2 , ...
STATEMENTS['z6gyhol'] = '( Y e. RR+ -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (GY(), DG, DG, GY())
STATEMENTS['z6gyr'] = ('( ( Y e. RR+ /\\ ( W e. CC /\\ ( ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 3 ) ) ) -> '
                       '( abs ` ( ( _G ` W ) x. ( Y ^c -u W ) ) ) <_ ( ( ; 6 4 x. ( ( Y ^c -u ( 1 / 2 ) ) + ( Y ^c -u 3 ) ) ) x. %s ) )'
                       % E4('( abs ` ( Im ` W ) )'))
STATEMENTS['z6gyl'] = ('( ( ( Y e. RR+ /\\ K e. NN0 ) /\\ ( W e. CC /\\ ( ( ( -u K - ( 1 / 2 ) ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ ( ( 1 / 2 ) - K ) ) /\\ 1 <_ ( abs ` ( Im ` W ) ) ) ) ) -> '
                       '( abs ` ( ( _G ` W ) x. ( Y ^c -u W ) ) ) <_ ( ( ; 6 4 x. ( ( Y ^c ( K + ( 1 / 2 ) ) ) + ( Y ^c ( K - ( 1 / 2 ) ) ) ) ) x. %s ) )'
                       % E4('( abs ` ( Im ` W ) )'))
LW = '( ( -u K - ( 1 / 2 ) ) + ( _i x. U ) )'
STATEMENTS['z6gyline'] = ('( ( ( Y e. RR+ /\\ K e. NN0 ) /\\ U e. RR ) -> ( abs ` ( ( _G ` %s ) x. ( Y ^c -u %s ) ) ) <_ '
                          '( ( ( 2 x. ( Y ^c ( K + ( 1 / 2 ) ) ) ) / ( ! ` K ) ) x. ( abs ` ( _G ` ( ( 1 / 2 ) + ( _i x. U ) ) ) ) ) )' % (LW, LW))
STATEMENTS['z6mstep'] = ('( ( Y e. RR+ /\\ K e. NN0 ) -> ( %s - %s ) = ( %s x. ( ( -u Y ^ K ) / ( ! ` K ) ) ) )'
                         % (VL(GY(), '( ( 1 / 2 ) - K )'), VL(GY(), '( -u K - ( 1 / 2 ) )'), TPI))
STATEMENTS['z6mright'] = ('( ( Y e. RR+ /\\ ( C e. RR /\\ ( ( 1 / 2 ) <_ C /\\ C <_ 3 ) ) ) -> %s = %s )'
                          % (VL(GY(), 'C'), VL(GY(), '( 1 / 2 )')))
STATEMENTS['z6mleft'] = ('( ( Y e. RR+ /\\ K e. NN0 ) -> ( abs ` %s ) <_ ( ( ( 2 x. ( Y ^c ( K + ( 1 / 2 ) ) ) ) / ( ! ` K ) ) x. %s ) )'
                         % (VL(GY(), '( -u K - ( 1 / 2 ) )'), KG))
STATEMENTS['z6mellin'] = ('( ( Y e. RR+ /\\ ( C e. RR /\\ ( ( 1 / 2 ) <_ C /\\ C <_ 3 ) ) ) -> %s ~~>r ( %s x. ( exp ` -u Y ) ) )'
                          % (VLF(GY(), 'C'), TPI))
STATEMENTS['z6mtail'] = ('( ( Y e. RR+ /\\ T e. RR+ ) -> ( abs ` ( %s - ( %s x. ( exp ` -u Y ) ) ) ) <_ ( ( Y ^c -u 3 ) x. ( ( ; ; 2 5 6 / ( log ` 2 ) ) x. %s ) ) )'
                         % (LI(GY(), '3', 'T'), TPI, E4('T')))

# ================================================================== section 2: blueprint Lemma 4.2 (DetectionShift 192-620)
STATEMENTS['z6p1ge1'] = '( ( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) ) -> 1 <_ %s )' % P1('N', 'R')
STATEMENTS['z6cube'] = '( ( N e. NN /\\ ( R e. RR /\\ 1 <_ R ) ) -> sum_ r e. ( N RSet R ) ( ( 1 / r ) x. ( r ^ 3 ) ) <_ ( R ^ 3 ) )'
STATEMENTS['z6omg'] = '( N e. NN -> %s <_ ( CTau x. ( N ^c ( 1 / ; ; 8 0 0 ) ) ) )' % OMG()
STATEMENTS['z6omgd'] = '( ( N e. NN /\\ ( D e. RR /\\ N <_ D ) ) -> %s <_ ( CTau x. ( D ^c ( 1 / ; ; 8 0 0 ) ) ) )' % OMG()
STATEMENTS['z6lshift'] = ('( ( ( ( %s /\\ N e. NN ) /\\ ( S e. CC /\\ %s ) ) /\\ ( ( W e. CC /\\ ( Re ` W ) = ( 1 / ; ; 1 0 0 ) ) /\\ ( V e. RR /\\ V <_ %s ) ) ) -> '
                          'V <_ ( %s x. ( ( 1 + ( abs ` ( ( Im ` W ) - ( Im ` S ) ) ) ) ^ 2 ) ) )' % (HZD3, HDN, CVXB('W'), KPT))
STATEMENTS['z6mrhol'] = ('( ( ( %s /\\ R e. NN ) /\\ C : NN --> CC ) -> ( ( s e. CC |-> %s ) e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D ( s e. CC |-> %s ) ) ) )'
                         % (HAB0, MR('s'), MR('s')))
STATEMENTS['z6grcn'] = ('( ( ( %s /\\ N e. NN ) /\\ ( ( C : NN --> CC /\\ R e. NN ) /\\ ( S e. CC /\\ E e. ( %s -cn-> CC ) ) ) ) -> %s e. ( %s -cn-> CC ) )'
                        % (HZD3, HPZ, GR('R'), DS))
A2HY = ('( ( ( %s /\\ N e. NN ) /\\ ( ( C : NN --> CC /\\ %s ) /\\ ( %s /\\ %s ) ) ) /\\ ( E e. ( %s -cn-> CC ) /\\ %s ) )'
        % (HZD3, CB, SRNG, HDN, HPZ, CVXH))
WPT = '( ( ( _G ` W ) x. ( %s ^c W ) ) x. ( ( ( E ` ( S + W ) ) / ( ( S + W ) - 1 ) ) x. %s ) )' % (XPD, MRr('R', '( S + W )'))
STATEMENTS['z6ectri'] = ('( ( %s /\\ ( ( R e. NN /\\ ( mmu ` R ) =/= 0 ) /\\ ( W e. CC /\\ ( ( Re ` S ) + ( Re ` W ) ) = ( 1 / ; ; 1 0 0 ) ) ) ) -> '
                         '( abs ` %s ) <_ ( ( ( ( %s ^c ( Re ` W ) ) x. %s ) x. ( %s x. ( R ^ 3 ) ) ) x. ( ( abs ` ( _G ` W ) ) x. ( ( 1 + ( abs ` ( Im ` W ) ) ) ^ 2 ) ) ) )'
                         % (A2HY, WPT, XPD, KPT, Z2D))
STATEMENTS['z6ectrl'] = ('( ( %s /\\ ( R e. NN /\\ ( mmu ` R ) =/= 0 ) ) -> ( %s ~~>r %s /\\ ( abs ` %s ) <_ ( ( ( ( ( %s ^c %s ) x. %s ) x. %s ) x. %s ) x. ( R ^ 3 ) ) ) )'
                         % (A2HY, VLF(GR('R'), CL), VL(GR('R'), CL), VL(GR('R'), CL), XPD, CL, KPT, Z2D, KGL))
STATEMENTS['z6ectr'] = '( ( %s /\\ %s ) -> ( abs ` %s ) <_ ( %s / 8 ) )' % (A2HY, T1, ECTR, P1D)

ORDER = ['z6gamre', 'z6gam1632', 'z6gmom', 'z6gmoml', 'z6gamfe', 'z6gamhol', 'z6gamhold',
         'z6lvert', 'z6rlimle', 'z6vlcvg', 'z6vleq', 'z6shift',
         'z6gyhol', 'z6gyr', 'z6gyl', 'z6gyline', 'z6mstep', 'z6mright', 'z6mleft', 'z6mellin', 'z6mtail',
         'z6p1ge1', 'z6cube', 'z6omg', 'z6omgd', 'z6lshift', 'z6mrhol', 'z6grcn', 'z6ectri', 'z6ectrl', 'z6ectr']

# ================================================================== sections 3-7: frozen for the next sorties (headlines)
# section 3: the Cauchy formula with one extra continuity-only point, the holomorphy of the numerator
QP = '( ( ( Re ` A ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` B ) ) /\\ ( ( Im ` A ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` B ) ) )'
STATEMENTS['z6gour2'] = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( ( P e. CC /\\ %s ) /\\ ( Q e. CC /\\ %s ) ) /\\ '
                         '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ ( ( A crect B ) \\ { P , Q } ) C_ dom ( CC _D F ) ) ) -> ( F rectint <. A , B >. ) = 0 )'
                         % (QP % ('P', 'P', 'P', 'P'), QP % ('Q', 'Q', 'Q', 'Q')))
STATEMENTS['z6cau2'] = ('( ( ( ( A e. CC /\\ B e. CC ) /\\ ( ( P e. CC /\\ %s ) /\\ ( Q e. CC /\\ %s ) ) /\\ P =/= Q ) /\\ '
                        '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ ( ( A crect B ) \\ { Q } ) C_ dom ( CC _D F ) ) ) -> '
                        '( ( z e. ( ( A crect B ) \\ { P } ) |-> ( ( F ` z ) / ( z - P ) ) ) rectint <. A , B >. ) = ( %s x. ( F ` P ) ) )'
                        % (QP % ('P', 'P', 'P', 'P'), QP % ('Q', 'Q', 'Q', 'Q'), TPI))
# section 4: the anchor identity (Lemma 4.1 on Re w = 3) at one modulus r
STERM = lambda r, n: ('( ( ( ( ( %s bvA %s ) ` %s ) x. ( ( mmu ` ( %s gcd %s ) ) x. ( phi ` ( %s gcd %s ) ) ) ) x. ( C ` %s ) ) x. ( ( exp ` ( -u %s / %s ) ) x. ( %s ^c -u S ) ) )'
                      % (Z1D, Z2D, n, r, n, r, n, n, n, XPD, n))
G3 = lambda r: ('( w e. %s |-> ( ( ( _G ` w ) x. ( %s ^c w ) ) x. ( sum_ k e. NN ( ( C ` k ) x. ( k ^c -u ( S + w ) ) ) x. %s ) ) )'
                % (HPT('2'), XPD, MRr(r, '( S + w )')))
A4 = '( ( ( %s /\\ N e. NN ) /\\ ( %s /\\ ( R e. NN /\\ ( mmu ` R ) =/= 0 ) ) ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) )' % (HZD3, CHRB)
STATEMENTS['z6anchor'] = ('( %s -> ( seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> /\\ ( %s x. sum_ n e. NN %s ) = %s ) )'
                          % (A4, STERM('R', 'n'), TPI, STERM('R', 'n'), VL(G3('R'), '3')))
# section 5: the rectangle identity and the shift Re w = 3 -> Re w = eps2 - beta
A5 = ('( ( ( %s /\\ N e. NN ) /\\ ( ( C : NN --> CC /\\ ( R e. NN /\\ ( mmu ` R ) =/= 0 ) ) /\\ ( %s /\\ S =/= 1 ) ) ) /\\ ( %s /\\ ( E ` S ) = 0 ) )'
      % (HZD3, SRNG, LIF))
STATEMENTS['z6shiftr'] = ('( %s -> ( %s - %s ) = ( %s x. ( ( ( _G ` ( 1 - S ) ) x. ( %s ^c ( 1 - S ) ) ) x. ( %s x. %s ) ) ) )'
                          % (A5, VL(GR('R'), '3'), VL(GR('R'), CL), TPI, XPD, RESV, MRr('R', '1')))
# section 6: the detector sum split by the pseudocharacters (tsum_detector_split, sum_Rset_Sterm)
A6 = '( ( ( %s /\\ N e. NN ) /\\ ( C : NN --> CC /\\ %s ) ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) )' % (HZD3, CB)
STATEMENTS['z6split'] = ('( %s -> ( %s + ( ( exp ` ( -u 1 / %s ) ) x. %s ) ) = sum_ r e. ( N RSet %s ) ( ( 1 / r ) x. sum_ n e. NN %s ) )'
                         % (A6, FDV, XPD, P1D, RPD, STERM('r', 'n')))
# section 7: Lemma 4.1, Lemmas 4.1 + 4.2 (DetectionEstimate), Proposition 4.4
A7 = ('( ( ( %s /\\ N e. NN ) /\\ ( %s /\\ ( ( %s /\\ S =/= 1 ) /\\ %s ) ) ) /\\ ( %s /\\ ( %s /\\ ( E ` S ) = 0 ) ) )'
      % (HZD3, CHRB, SRNG, HDN, T1, LIF))
EPCS = EPC
STATEMENTS['z6detid'] = '( %s -> ( %s + ( ( exp ` ( -u 1 / %s ) ) x. %s ) ) = ( %s + %s ) )' % (A7, FDV, XPD, P1D, ECTR, EPCS)
STATEMENTS['z6detall'] = '( %s -> %s )' % (A7, HDET_.replace('( F + ', '( %s + ' % FDV, 1))
STATEMENTS['z6dlbz'] = ('( ( %s /\\ ( C = %s -> %s <_ ( abs ` ( Im ` S ) ) ) ) -> ( ( ( 1 / ; ; 4 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ ( abs ` %s ) )'
                        % (A7, PRN, LAM60, FDV))
LATER = ['z6gour2', 'z6cau2', 'z6anchor', 'z6shiftr', 'z6split', 'z6detid', 'z6detall', 'z6dlbz']

# ---- helper lemmas added by the block A/C proving agent (not in the blueprint's table)
# z6gamle1: the M = 0 case of z5dgzp on the real segment ( 0 , 1 ] (z6gamre's three cases)
STATEMENTS['z6gamle1'] = '( ( Y e. RR /\\ 0 < Y /\\ Y <_ 1 ) -> ( ( _G ` Y ) x. Y ) <_ 1 )'
# z6gaml1: the functional equation on the left line -1 < Re w <_ -98/100 (z6gmoml's pointwise step)
_WL = '( C + ( _i x. U ) )'
_WL1 = '( ( C + 1 ) + ( _i x. U ) )'
STATEMENTS['z6gaml1'] = ('( ( ( C e. RR /\\ -u 1 < C /\\ C <_ -u ( ; 9 8 / ; ; 1 0 0 ) ) /\\ U e. RR ) -> ( ( %s e. %s /\\ %s =/= 0 ) /\\ '
                         '( ( _G ` %s ) = ( ( _G ` %s ) / %s ) /\\ ( abs ` ( _G ` %s ) ) <_ ( ( ; 5 0 / ; 4 9 ) x. ( abs ` ( _G ` %s ) ) ) ) ) )'
                         % (_WL, DG, _WL, _WL, _WL1, _WL, _WL, _WL1))

# z6aff: the affine change of variables u = A + t ( B - A ) for a function continuous on [ A , B ] (z6lvert)
STATEMENTS['z6aff'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ A < B ) /\\ H e. ( ( A [,] B ) -cn-> CC ) ) -> '
                       'S. ( A (,) B ) ( H ` u ) _d u = S. ( 0 (,) 1 ) ( ( H ` ( A + ( t x. ( B - A ) ) ) ) x. ( B - A ) ) _d t )')
# z6segl: the vertical segment ( C - i T ) -- ( C + i T ) in coordinates
_SA = '( C + ( _i x. -u T ) )'
_SB = '( C + ( _i x. T ) )'
STATEMENTS['z6segl'] = ('( ( C e. CC /\\ T e. CC /\\ X e. CC ) -> ( ( %s + ( X x. ( %s - %s ) ) ) = ( C + ( _i x. ( -u T + ( X x. ( T - -u T ) ) ) ) ) /\\ '
                        '( %s - %s ) = ( _i x. ( T - -u T ) ) ) )' % (_SA, _SB, _SA, _SB, _SA))
# z6segv: the points C + i U , -T <_ U <_ T , lie on that segment
STATEMENTS['z6segv'] = '( ( ( C e. RR /\\ T e. RR+ ) /\\ U e. ( -u T [,] T ) ) -> ( C + ( _i x. U ) ) e. ( %s cseg %s ) )' % (_SA, _SB)

# z6absle: a class whose absolute value is below something is a complex number (the absolute value of a proper class is (/), not in RR*)
STATEMENTS['z6absle'] = '( ( abs ` A ) <_ B -> A e. CC )'
# z6rlimlem: z6rlimle for a function symbol F (the $d ph x of rlimle forbids the mapping's letter in the antecedent)
STATEMENTS['z6rlimlem'] = '( ( ( F ~~>r W /\\ F : RR+ --> CC ) /\\ ( B e. RR /\\ A. y e. RR+ ( abs ` ( F ` y ) ) <_ B ) ) -> ( abs ` W ) <_ B )'

# z6segd: the vertical segment lies in any D containing the vertical line (z6vlcvg's hypothesis to z6lvert's)
STATEMENTS['z6segd'] = '( ( ( C e. RR /\\ T e. RR+ ) /\\ A. u e. RR ( C + ( _i x. u ) ) e. D ) -> ( %s cseg %s ) C_ D )' % (_SA, _SB)
# z6e4lim: 2 ^ ( - t / 4 ) -> 0 (cxp2lim at the base 2 ^ ( 1 / 4 ))
STATEMENTS['z6e4lim'] = '( t e. RR+ |-> %s ) ~~>r 0' % E4('t')
# z6half: the ML bound of one tail of a line integral against an exponential majorant (deduction form; cxpaffitg2)
STATEMENTS['z6half'] = ('( ph -> ( abs ` S. ( A (,) B ) F _d v ) <_ ( M x. ( ( ( 2 ^c ( K x. B ) ) - ( 2 ^c ( K x. A ) ) ) / ( K x. ( log ` 2 ) ) ) ) )')
HYPS['z6half'] = [('1', '( ph -> ( ( A e. RR /\\ B e. RR ) /\\ A <_ B ) )'),
                  ('2', '( ph -> ( K e. RR /\\ K =/= 0 ) )'),
                  ('3', '( ph -> M e. RR )'),
                  ('4', '( ( ph /\\ v e. ( A (,) B ) ) -> F e. CC )'),
                  ('5', '( ph -> ( v e. ( A (,) B ) |-> F ) e. L^1 )'),
                  ('6', '( ( ph /\\ v e. ( A (,) B ) ) -> ( abs ` F ) <_ ( M x. ( 2 ^c ( K x. v ) ) ) )')]

# z6kalg: the two tails of z6vltail add up (real algebra)
_V1 = '( ( ( 2 ^c ( ( 1 / 4 ) x. -u P ) ) - ( 2 ^c ( ( 1 / 4 ) x. -u Q ) ) ) / ( ( 1 / 4 ) x. ( log ` 2 ) ) )'
_V2 = '( ( ( 2 ^c ( -u ( 1 / 4 ) x. Q ) ) - ( 2 ^c ( -u ( 1 / 4 ) x. P ) ) ) / ( -u ( 1 / 4 ) x. ( log ` 2 ) ) )'
_K8 = '( ( 8 x. M ) / ( log ` 2 ) )'
STATEMENTS['z6kalg'] = ('( ( M e. RR /\\ ( P e. RR /\\ Q e. RR ) ) -> ( ( M x. %s ) + ( M x. %s ) ) = ( %s x. ( %s - %s ) ) )'
                        % (_V1, _V2, _K8, E4('P'), E4('Q')))
# z6vltail: the Cauchy tail of the truncated line integrals (z6vlcvg's core)
from cl import split_imp as _spl
_HV = _spl(STATEMENTS['z6vlcvg'])[0]
STATEMENTS['z6vltail'] = ('( ( %s /\\ ( ( P e. RR /\\ Q e. RR ) /\\ ( Y <_ P /\\ P <_ Q ) ) ) -> ( abs ` ( %s - %s ) ) <_ ( %s x. %s ) )'
                          % (_HV, LI('G', 'C', 'Q'), LI('G', 'C', 'P'), _K8, E4('P')))

# z6vlex: the truncated line integrals converge (caucvgr with the tail z6vltail)
STATEMENTS['z6vlex'] = '( %s -> %s ~~>r %s )' % (_HV, VLF('G', 'C'), VL('G', 'C'))
# z6vlt: the tail bound in the limit, at a class R (z6vlcvg instantiates R := t)
STATEMENTS['z6vlt'] = ('( ( %s /\\ ( R e. RR+ /\\ Y <_ R ) ) -> ( abs ` ( %s - %s ) ) <_ ( %s x. %s ) )'
                       % (_HV, VL('G', 'C'), LI('G', 'C', 'R'), _K8, E4('R')))

# z6hedge: a horizontal segment at height H , | H | >_ Y , inside the strip: in D , with the ML bound (z6shift's edges)
_HS = '( ( ( A e. RR /\\ B e. RR ) /\\ A <_ B ) /\\ ( ( G e. ( D -cn-> CC ) /\\ %s ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ %s ) ) )' % (STRIPD, STRIPM)
_X1 = '( P + ( _i x. H ) )'
_X2 = '( Q + ( _i x. H ) )'
STATEMENTS['z6hedge'] = ('( ( %s /\\ ( ( H e. RR /\\ Y <_ ( abs ` H ) ) /\\ ( P e. ( A [,] B ) /\\ Q e. ( A [,] B ) ) ) ) -> '
                         '( ( %s cseg %s ) C_ D /\\ ( abs ` ( G lint <. %s , %s >. ) ) <_ ( ( M x. ( abs ` ( Q - P ) ) ) x. %s ) ) )'
                         % (_HS, _X1, _X2, _X1, _X2, E4('( abs ` H )')))
# z6shl: z6shift with the rectangle heights bound by r and the line integrals by s (rectintshlr's $d t ph , $d t X W)
_VLs = lambda c: '( ~~>r ` ( s e. RR+ |-> %s ) )' % LI('G', c, 's')
STATEMENTS['z6shl'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ A < B ) /\\ ( ( G e. ( D -cn-> CC ) /\\ %s ) /\\ ( ( M e. RR /\\ Y e. RR+ ) /\\ %s ) ) /\\ '
                       '( K e. CC /\\ A. r e. RR+ ( Y <_ r -> ( G rectint <. ( A + ( _i x. -u r ) ) , ( B + ( _i x. r ) ) >. ) = K ) ) ) -> ( %s - %s ) = K )'
                       % (STRIPD, STRIPM, _VLs('B'), _VLs('A')))


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('z6ag' + lab, 'grammar check of %s' % lab)
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



# ---- block z6ab helper lemmas (Gamma holomorphy; generators tools/gen/z6a_gh1.py .. z6a_gh7.py)
STATEMENTS['z6hid'] = '( D e. ( TopOpen ` CCfld ) -> ( ( z e. D |-> z ) e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D ( z e. D |-> z ) ) ) )'
STATEMENTS['z6hexp'] = '( ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) ) -> ( ( z e. D |-> ( exp ` ( F ` z ) ) ) e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D ( z e. D |-> ( exp ` ( F ` z ) ) ) ) ) )'
STATEMENTS['z6hshift'] = '( ( ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) ) /\\ ( U e. ( TopOpen ` CCfld ) /\\ N e. CC /\\ A. w e. U ( w + N ) e. D ) ) -> ( ( z e. U |-> ( F ` ( z + N ) ) ) e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D ( z e. U |-> ( F ` ( z + N ) ) ) ) ) )'
STATEMENTS['z6hv1'] = '( ( K e. NN /\\ Z e. ( `\' Re " ( -u 1 (,) +oo ) ) ) -> ( ( ( Z / K ) + 1 ) e. ( CC \\ ( -oo (,] 0 ) ) /\\ ( Z + K ) =/= 0 ) )'
STATEMENTS['z6htdv'] = '( ( K e. NN /\\ U e. ( TopOpen ` CCfld ) /\\ U C_ ( `\' Re " ( -u 1 (,) +oo ) ) ) -> ( CC _D ( z e. U |-> ( ( z x. ( log ` ( ( K + 1 ) / K ) ) ) - ( log ` ( ( z / K ) + 1 ) ) ) ) ) = ( z e. U |-> ( ( log ` ( ( K + 1 ) / K ) ) - ( 1 / ( z + K ) ) ) ) )'
STATEMENTS['z6hthol'] = '( ( K e. NN /\\ U e. ( TopOpen ` CCfld ) /\\ U C_ ( `\' Re " ( -u 1 (,) +oo ) ) ) -> ( ( z e. U |-> ( ( z x. ( log ` ( ( K + 1 ) / K ) ) ) - ( log ` ( ( z / K ) + 1 ) ) ) ) e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D ( z e. U |-> ( ( z x. ( log ` ( ( K + 1 ) / K ) ) ) - ( log ` ( ( z / K ) + 1 ) ) ) ) ) ) )'
STATEMENTS['z6hdtb'] = '( ( K e. NN /\\ ( X e. CC /\\ 0 <_ ( Re ` X ) ) ) -> ( abs ` ( ( log ` ( ( K + 1 ) / K ) ) - ( 1 / ( X + K ) ) ) ) <_ ( ( 1 + ( abs ` X ) ) / ( K ^ 2 ) ) )'
STATEMENTS['z6htb'] = '( ( K e. NN /\\ ( Z e. CC /\\ 0 <_ ( Re ` Z ) ) ) -> ( abs ` ( ( Z x. ( log ` ( ( K + 1 ) / K ) ) ) - ( log ` ( ( Z / K ) + 1 ) ) ) ) <_ ( ( ( 1 + ( abs ` Z ) ) / ( K ^ 2 ) ) x. ( abs ` Z ) ) )'
STATEMENTS['z6hbxuh'] = '( ( L e. RR+ /\\ R e. RR ) -> ( ( ( a e. NN |-> ( p e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) |-> ( ( p x. ( log ` ( ( a + 1 ) / a ) ) ) - ( log ` ( ( p / a ) + 1 ) ) ) ) ) : NN --> ( CC ^m ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) ) /\\ A. j e. NN ( ( ( a e. NN |-> ( p e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) |-> ( ( p x. ( log ` ( ( a + 1 ) / a ) ) ) - ( log ` ( ( p / a ) + 1 ) ) ) ) ) ` j ) e. ( ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) -cn-> CC ) /\\ ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) C_ dom ( CC _D ( ( a e. NN |-> ( p e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) |-> ( ( p x. ( log ` ( ( a + 1 ) / a ) ) ) - ( log ` ( ( p / a ) + 1 ) ) ) ) ) ` j ) ) ) ) /\\ ( ( ( n e. NN |-> ( ( ( 1 + ( 2 x. R ) ) x. ( 2 x. R ) ) x. ( n ^c -u 2 ) ) ) : NN --> RR /\\ seq 1 ( + , ( n e. NN |-> ( ( ( 1 + ( 2 x. R ) ) x. ( 2 x. R ) ) x. ( n ^c -u 2 ) ) ) ) e. dom ~~> /\\ A. j e. NN A. y e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) ( abs ` ( ( ( a e. NN |-> ( p e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) |-> ( ( p x. ( log ` ( ( a + 1 ) / a ) ) ) - ( log ` ( ( p / a ) + 1 ) ) ) ) ) ` j ) ` y ) ) <_ ( ( n e. NN |-> ( ( ( 1 + ( 2 x. R ) ) x. ( 2 x. R ) ) x. ( n ^c -u 2 ) ) ) ` j ) ) /\\ ( ( n e. NN |-> ( ( 1 + ( 2 x. R ) ) x. ( n ^c -u 2 ) ) ) : NN --> RR /\\ seq 1 ( + , ( n e. NN |-> ( ( 1 + ( 2 x. R ) ) x. ( n ^c -u 2 ) ) ) ) e. dom ~~> /\\ A. j e. NN A. y e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) ( abs ` ( ( CC _D ( ( a e. NN |-> ( p e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) |-> ( ( p x. ( log ` ( ( a + 1 ) / a ) ) ) - ( log ` ( ( p / a ) + 1 ) ) ) ) ) ` j ) ) ` y ) ) <_ ( ( n e. NN |-> ( ( 1 + ( 2 x. R ) ) x. ( n ^c -u 2 ) ) ) ` j ) ) ) ) )'
STATEMENTS['z6hbxhol'] = '( ( L e. RR+ /\\ R e. RR ) -> ( ( z e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) |-> sum_ k e. NN ( ( z x. ( log ` ( ( k + 1 ) / k ) ) ) - ( log ` ( ( z / k ) + 1 ) ) ) ) e. ( ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) -cn-> CC ) /\\ ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) C_ dom ( CC _D ( z e. ( ( `\' Re " ( L (,) R ) ) i^i ( `\' Im " ( -u R (,) R ) ) ) |-> sum_ k e. NN ( ( z x. ( log ` ( ( k + 1 ) / k ) ) ) - ( log ` ( ( z / k ) + 1 ) ) ) ) ) ) )'
STATEMENTS['z6hgval'] = '( ( Z e. CC /\\ 0 < ( Re ` Z ) ) -> ( sum_ k e. NN ( ( Z x. ( log ` ( ( k + 1 ) / k ) ) ) - ( log ` ( ( Z / k ) + 1 ) ) ) e. CC /\\ ( _G ` Z ) = ( ( exp ` sum_ k e. NN ( ( Z x. ( log ` ( ( k + 1 ) / k ) ) ) - ( log ` ( ( Z / k ) + 1 ) ) ) ) / Z ) ) )'
STATEMENTS['z6hdgopn'] = '( CC \\ ( ZZ \\ NN ) ) e. ( TopOpen ` CCfld )'
STATEMENTS['z6hgind'] = '( N e. NN0 -> ( ( x e. ( ( `\' Re " ( -u N (,) +oo ) ) i^i ( CC \\ ( ZZ \\ NN ) ) ) |-> ( _G ` x ) ) e. ( ( ( `\' Re " ( -u N (,) +oo ) ) i^i ( CC \\ ( ZZ \\ NN ) ) ) -cn-> CC ) /\\ ( ( `\' Re " ( -u N (,) +oo ) ) i^i ( CC \\ ( ZZ \\ NN ) ) ) C_ dom ( CC _D ( x e. ( ( `\' Re " ( -u N (,) +oo ) ) i^i ( CC \\ ( ZZ \\ NN ) ) ) |-> ( _G ` x ) ) ) ) )'


# ---- block z6ae helper lemmas (z6lshift's pieces; generator tools/gen/z6a_e3.py)
# z6els1: the two linear-in-products bounds N ( t + 2 ) <_ D ( 1 + U ), N ( t + 3 ) <_ 2 D ( 1 + U ) from t - A <_ U, N ( A + 2 ) <_ D
STATEMENTS['z6els1'] = ('( ( ( N e. NN /\\ D e. RR ) /\\ ( ( T e. RR /\\ 0 <_ T ) /\\ ( A e. RR /\\ 0 <_ A ) /\\ ( U e. RR /\\ 0 <_ U ) ) /\\ '
                        '( ( T - A ) <_ U /\\ ( N x. ( A + 2 ) ) <_ D ) ) -> ( ( N x. ( T + 2 ) ) <_ ( D x. ( 1 + U ) ) /\\ '
                        '( N x. ( T + 3 ) ) <_ ( ( 2 x. D ) x. ( 1 + U ) ) ) )')
# z6els2: log B <_ 2 log D ( 1 + U ) from B <_ 2 D ( 1 + U ), log D >_ 200
STATEMENTS['z6els2'] = ('( ( ( D e. RR+ /\\ ; ; 2 0 0 <_ ( log ` D ) ) /\\ ( U e. RR /\\ 0 <_ U ) /\\ ( B e. RR+ /\\ B <_ ( ( 2 x. D ) x. ( 1 + U ) ) ) ) -> '
                        '( log ` B ) <_ ( ( 2 x. ( log ` D ) ) x. ( 1 + U ) ) )')
# z6els3: A ^ ( 99/200 ) <_ D ^ ( 99/200 ) ( 1 + U ) from 0 <_ A <_ D ( 1 + U ), 1 <_ D
STATEMENTS['z6els3'] = ('( ( ( D e. RR /\\ 1 <_ D ) /\\ ( U e. RR /\\ 0 <_ U ) /\\ ( ( A e. RR /\\ 0 <_ A ) /\\ A <_ ( D x. ( 1 + U ) ) ) ) -> '
                        '( ( A ^c ( ; 9 9 / ; ; 2 0 0 ) ) <_ ( ( D ^c ( ; 9 9 / ; ; 2 0 0 ) ) x. ( 1 + U ) ) /\\ 1 <_ ( D ^c ( ; 9 9 / ; ; 2 0 0 ) ) ) )')
# z6els4: on Re W = 1/100, 1 / | W - 1 | <_ 2 and the convexity exponent is 99/200
STATEMENTS['z6els4'] = ('( ( W e. CC /\\ ( Re ` W ) = ( 1 / ; ; 1 0 0 ) ) -> ( ( 1 / ( abs ` ( W - 1 ) ) ) <_ 2 /\\ '
                        'if ( 1 <_ ( Re ` W ) , 0 , ( ( 1 - ( Re ` W ) ) / 2 ) ) = ( ; 9 9 / ; ; 2 0 0 ) ) )')
# z6els5: the final algebra of z6lshift over atoms V O C F P G I H L U
STATEMENTS['z6els5'] = ('( ( ( ( ( V e. RR /\\ V <_ ( ( ; ; ; ; ; 2 0 0 0 0 0 x. O ) x. ( ( P x. G ) + I ) ) ) /\\ ( ( O e. RR /\\ 0 <_ O ) /\\ O <_ ( C x. F ) ) ) /\\ '
                        '( ( C e. RR /\\ F e. RR ) /\\ ( ( P e. RR /\\ 0 <_ P ) /\\ P <_ ( H x. ( 1 + U ) ) ) ) ) /\\ '
                        '( ( ( G e. RR /\\ 0 <_ G ) /\\ G <_ ( ( 2 x. L ) x. ( 1 + U ) ) ) /\\ ( ( ( I e. RR /\\ 0 <_ I ) /\\ I <_ 2 ) /\\ '
                        '( ( H e. RR /\\ 1 <_ H ) /\\ ( ( L e. RR /\\ ; ; 2 0 0 <_ L ) /\\ ( U e. RR /\\ 0 <_ U ) ) ) ) ) ) -> '
                        'V <_ ( ( ( ( ; ; ; ; ; 6 0 0 0 0 0 x. C ) x. ( F x. H ) ) x. L ) x. ( ( 1 + U ) ^ 2 ) ) )')

# ---- block D helper lemmas (the Mellin identity; generators tools/gen/z6a_m1.py ..., z6a_mlib.py)
_TOPO = '( TopOpen ` CCfld )'
_HOLG = lambda F, D: '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (F, D, D, F)
_STR = lambda A, B: "( `' Re \" ( %s (,) %s ) )" % (A, B)
# z6mstopn: an open vertical strip is open
STATEMENTS['z6mstopn'] = '%s e. %s' % (_STR('A', 'B'), _TOPO)
# z6melst: membership in the open vertical strip
STATEMENTS['z6melst'] = '( ( A e. RR* /\\ B e. RR* ) -> ( Z e. %s <-> ( Z e. CC /\\ ( A < ( Re ` Z ) /\\ ( Re ` Z ) < B ) ) ) )' % _STR('A', 'B')
# z6mycxh: w |-> Y ^c -u w is holomorphic on every open set
STATEMENTS['z6mycxh'] = '( ( Y e. RR+ /\\ U e. %s ) -> %s )' % (_TOPO, _HOLG('( w e. U |-> ( Y ^c -u w ) )', 'U'))
# z6mrfhol: the rising factorial w |-> w RiseFac K is holomorphic on every open set
STATEMENTS['z6mrfhol'] = '( ( K e. NN0 /\\ U e. %s ) -> %s )' % (_TOPO, _HOLG('( w e. U |-> ( w RiseFac K ) )', 'U'))
# z6mfhol: the Cauchy numerator of z6mstep, Gamma ( w + K + 1 ) Y ^ -w / ( w RiseFac K ), is holomorphic on the strip -K-1 < Re w < 1-K
MSTRIP = _STR('( -u K - 1 )', '( 1 - K )')
MF0 = '( w e. %s |-> ( ( ( _G ` ( w + ( K + 1 ) ) ) x. ( Y ^c -u w ) ) / ( w RiseFac K ) ) )' % MSTRIP
STATEMENTS['z6mfhol'] = '( ( Y e. RR+ /\\ K e. NN0 ) -> %s )' % _HOLG(MF0, MSTRIP)
# ---- block z6ae helper lemmas: entire functions of s built from pieces (z6mrhol; generator tools/gen/z6a_e4.py)
ENTS = lambda F: '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (F, F)
MSS = lambda A: '( s e. CC |-> %s )' % A
STATEMENTS['z6ehtr'] = '( F = G -> ( %s <-> %s ) )' % (ENTS('F'), ENTS('G'))
STATEMENTS['z6ehdv'] = ('( ( A. s e. CC A e. CC /\\ ( ( CC _D %s ) = ( s e. CC |-> B ) /\\ A. s e. CC B e. V ) ) -> %s )'
                        % (MSS('A'), ENTS(MSS('A'))))
STATEMENTS['z6ehder'] = ('( %s -> ( ( CC _D %s ) : CC --> CC /\\ ( CC _D %s ) = ( s e. CC |-> ( ( CC _D %s ) ` s ) ) ) )'
                         % (ENTS(MSS('A')), MSS('A'), MSS('A'), MSS('A')))
STATEMENTS['z6ehc'] = '( ph -> %s )' % ENTS(MSS('B'))
HYPS['z6ehc'] = [('1', '( ph -> B e. CC )')]
STATEMENTS['z6ehx'] = '( A e. RR+ -> %s )' % ENTS(MSS('( A ^c -u s )'))
STATEMENTS['z6ehadd'] = '( ph -> %s )' % ENTS(MSS('( A + B )'))
HYPS['z6ehadd'] = [('1', '( ph -> %s )' % ENTS(MSS('A'))), ('2', '( ph -> %s )' % ENTS(MSS('B')))]
STATEMENTS['z6ehmul'] = '( ph -> %s )' % ENTS(MSS('( A x. B )'))
HYPS['z6ehmul'] = [('1', '( ph -> %s )' % ENTS(MSS('A'))), ('2', '( ph -> %s )' % ENTS(MSS('B')))]
STATEMENTS['z6ehfs'] = '( ph -> %s )' % ENTS(MSS('sum_ i e. I A'))
HYPS['z6ehfs'] = [('1', '( ph -> I e. Fin )'), ('2', '( ( ph /\\ i e. I ) -> %s )' % ENTS(MSS('A')))]
STATEMENTS['z6ehfp'] = '( ph -> %s )' % ENTS(MSS('prod_ i e. I A'))
HYPS['z6ehfp'] = [('1', '( ph -> I e. Fin )'), ('2', '( ( ph /\\ i e. I ) -> %s )' % ENTS(MSS('A'))), ('3', '( i = j -> A = E )')]
# z6mycx: Y ^ X lies below Y ^ B + Y ^ A for A <_ X <_ B (convexity in the exponent, both cases of Y against 1)
STATEMENTS['z6mycx'] = '( ( Y e. RR+ /\\ ( A e. RR /\\ B e. RR /\\ X e. RR ) /\\ ( A <_ X /\\ X <_ B ) ) -> ( Y ^c X ) <_ ( ( Y ^c B ) + ( Y ^c A ) ) )'
# z6mg64: the Gamma strip bound 64 2 ^ ( - | Im W | / 4 ) on 1/2 <_ Re W <_ 3 ( gamvb, z6gamre )
STATEMENTS['z6mg64'] = ('( ( W e. CC /\\ ( ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 3 ) ) -> ( abs ` ( _G ` W ) ) <_ ( ; 6 4 x. %s ) )'
                        % E4('( abs ` ( Im ` W ) )'))
# z6mgdiv: one step of the functional equation to the left, | Gamma ( W ) | <_ | Gamma ( W + 1 ) | / R for R <_ | W |
STATEMENTS['z6mgdiv'] = '( ( W e. %s /\\ ( R e. RR+ /\\ R <_ ( abs ` W ) ) ) -> ( abs ` ( _G ` W ) ) <_ ( ( abs ` ( _G ` ( W + 1 ) ) ) / R ) )' % DG
# z6mndg: a point with a non-integral real part or a nonzero imaginary part is in the domain of Gamma
STATEMENTS['z6mndg'] = '( ( W e. CC /\\ ( -. ( Re ` W ) e. ZZ \\/ ( Im ` W ) =/= 0 ) ) -> W e. %s )' % DG
# z6mnhz: the lines Re w = -K - 1/2 and Re w = 1/2 - K avoid the integers
STATEMENTS['z6mnhz'] = '( K e. NN0 -> ( -. ( -u K - ( 1 / 2 ) ) e. ZZ /\\ -. ( ( 1 / 2 ) - K ) e. ZZ ) )'
# z6mre1: the real and imaginary parts of W + 1
STATEMENTS['z6mre1'] = '( W e. CC -> ( ( Re ` ( W + 1 ) ) = ( ( Re ` W ) + 1 ) /\\ ( Im ` ( W + 1 ) ) = ( Im ` W ) ) )'
# z6mgup: the strip bound 64 2 ^ ( - | Im | / 4 ) passes from W + 1 to W when | Im W | >_ 1
STATEMENTS['z6mgup'] = ('( ( W e. CC /\\ 1 <_ ( abs ` ( Im ` W ) ) /\\ ( abs ` ( _G ` ( W + 1 ) ) ) <_ ( ; 6 4 x. %s ) ) -> ( abs ` ( _G ` W ) ) <_ ( ; 6 4 x. %s ) )'
                        % (E4('( abs ` ( Im ` ( W + 1 ) ) )'), E4('( abs ` ( Im ` W ) )')))
# z6mgstr: the strip bound on -K - 1/2 <_ Re W <_ 1/2 - K , | Im W | >_ 1 (induction on K)
STATEMENTS['z6mgstr'] = ('( ( K e. NN0 /\\ ( W e. CC /\\ ( ( ( -u K - ( 1 / 2 ) ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ ( ( 1 / 2 ) - K ) ) /\\ 1 <_ ( abs ` ( Im ` W ) ) ) ) ) -> '
                         '( abs ` ( _G ` W ) ) <_ ( ; 6 4 x. %s ) )' % E4('( abs ` ( Im ` W ) )'))
# z6mgln: Gamma on the line Re w = -K - 1/2 against Gamma on Re w = 1/2 (induction on K)
STATEMENTS['z6mgln'] = ('( ( K e. NN0 /\\ U e. RR ) -> ( abs ` ( _G ` ( ( -u K - ( 1 / 2 ) ) + ( _i x. U ) ) ) ) <_ '
                        '( ( 2 / ( ! ` K ) ) x. ( abs ` ( _G ` ( ( 1 / 2 ) + ( _i x. U ) ) ) ) ) )')
# z6ehmulc: z6ehmul in closed form (holmul plus a change of bound variable); the induction step of z6ehfp needs it
STATEMENTS['z6ehmulc'] = '( ( %s /\\ %s ) -> %s )' % (ENTS(MSS('A')), ENTS(MSS('B')), ENTS(MSS('( A x. B )')))
# z6mgyvc: z6vlcvg for the Mellin integrand, the line majorant written on _G ( w ) Y ^ -u w (bound letter v in the hypotheses)
_GYv = '( abs ` ( ( _G ` ( C + ( _i x. v ) ) ) x. ( Y ^c -u ( C + ( _i x. v ) ) ) ) ) <_ ( M x. %s )' % E4('( abs ` v )')
STATEMENTS['z6mgyvc'] = ('( ( ( ( Y e. RR+ /\\ C e. RR ) /\\ A. v e. RR ( C + ( _i x. v ) ) e. %s ) /\\ ( ( M e. RR /\\ R e. RR+ ) /\\ A. v e. RR ( R <_ ( abs ` v ) -> %s ) ) ) -> %s )'
                         % (DG, _GYv, ' '.join(__import__('congr').subst_toks(cns('z6vlcvg').split(), {'G': GY(), 'Y': 'R'}))))
# z6mrfp: the rising factorial as z6gamfe's product
STATEMENTS['z6mrfp'] = '( ( Z e. CC /\\ K e. NN0 ) -> prod_ j e. ( 0 ..^ K ) ( Z + j ) = ( Z RiseFac K ) )'
# z6mrdg: the rectangle -K - 1/2 <_ Re <_ 1/2 - K minus the point -K lies in the domain of Gamma
STATEMENTS['z6mrdg'] = ('( ( K e. NN0 /\\ ( U e. CC /\\ ( ( ( -u K - ( 1 / 2 ) ) <_ ( Re ` U ) /\\ ( Re ` U ) <_ ( ( 1 / 2 ) - K ) ) /\\ U =/= -u K ) ) ) -> U e. %s )' % DG)
# z6malg, z6malg2: field algebra of z6mfu and z6mfp
STATEMENTS['z6malg'] = '( ( ( A e. CC /\\ Y e. CC ) /\\ ( R e. CC /\\ R =/= 0 ) /\\ ( S e. CC /\\ S =/= 0 ) ) -> ( ( ( ( A x. ( R x. S ) ) x. Y ) / R ) / S ) = ( A x. Y ) )'
STATEMENTS['z6malg2'] = '( ( ( X e. CC /\\ F e. CC /\\ F =/= 0 ) /\\ ( E e. CC /\\ ( E x. E ) = 1 ) ) -> ( ( 1 x. X ) / ( E x. F ) ) = ( ( E x. X ) / F ) )'
# z6mfp: the residue value, the Cauchy numerator at w = -K
STATEMENTS['z6mfp'] = '( ( Y e. RR+ /\\ K e. NN0 ) -> ( %s ` -u K ) = ( ( -u Y ^ K ) / ( ! ` K ) ) )' % MF0
# z6mfu: off w = -K the Cauchy integrand is the Mellin integrand ( z6gamfe at K + 1 )
STATEMENTS['z6mfu'] = ('( ( ( Y e. RR+ /\\ K e. NN0 ) /\\ ( U e. %s /\\ U e. %s ) ) -> ( ( %s ` U ) / ( U - -u K ) ) = ( ( _G ` U ) x. ( Y ^c -u U ) ) )'
                       % (MSTRIP, DG, MF0))
# z6mrect: the rectangle [ -K - 1/2 , 1/2 - K ] x [ -T , T ] integral of the Mellin integrand is 2 pi i times the residue at -K
STATEMENTS['z6mrect'] = ('( ( ( Y e. RR+ /\\ K e. NN0 ) /\\ T e. RR+ ) -> ( %s rectint <. ( ( -u K - ( 1 / 2 ) ) + ( _i x. -u T ) ) , ( ( ( 1 / 2 ) - K ) + ( _i x. T ) ) >. ) = '
                         '( %s x. ( ( -u Y ^ K ) / ( ! ` K ) ) ) )' % (GY(), TPI))
# z6mvlr, z6mvll: the Mellin line integrals converge on 1/2 <_ Re = C <_ 3 and on Re = -K - 1/2
STATEMENTS['z6mvlr'] = '( ( Y e. RR+ /\\ ( C e. RR /\\ ( ( 1 / 2 ) <_ C /\\ C <_ 3 ) ) ) -> %s ~~>r %s )' % (VLF(GY(), 'C'), VL(GY(), 'C'))
STATEMENTS['z6mvll'] = '( ( Y e. RR+ /\\ K e. NN0 ) -> %s ~~>r %s )' % (VLF(GY(), '( -u K - ( 1 / 2 ) )'), VL(GY(), '( -u K - ( 1 / 2 ) )'))
# z6mlt: the truncated left line integral is below ( 2 Y ^ ( K + 1/2 ) / K ! ) KG
STATEMENTS['z6mlt'] = ('( ( ( Y e. RR+ /\\ K e. NN0 ) /\\ T e. RR+ ) -> ( abs ` %s ) <_ ( ( ( 2 x. ( Y ^c ( K + ( 1 / 2 ) ) ) ) / ( ! ` K ) ) x. %s ) )'
                       % (LI(GY(), '( -u K - ( 1 / 2 ) )', 'T'), KG))
# z6mtel: the telescoped residues, VL ( 1/2 ) = VL ( -K - 1/2 ) + 2 pi i sum_ k <_ K ( -Y ) ^ k / k !
_ESUM = lambda n: 'sum_ k e. ( 0 ... %s ) ( ( -u Y ^ k ) / ( ! ` k ) )' % n
STATEMENTS['z6mtel'] = ('( ( Y e. RR+ /\\ K e. NN0 ) -> %s = ( %s + ( %s x. %s ) ) )'
                        % (VL(GY(), '( 1 / 2 )'), VL(GY(), '( -u K - ( 1 / 2 ) )'), TPI, _ESUM('K')))
# z6malg3: field algebra of z6mhalf
STATEMENTS['z6malg3'] = ('( ( ( P e. CC /\\ Q e. CC ) /\\ ( F e. CC /\\ F =/= 0 ) /\\ G e. CC ) -> '
                         '( ( ( 2 x. ( P x. Q ) ) / F ) x. G ) = ( ( ( 2 x. Q ) x. G ) x. ( P / F ) ) )')
# z6mhalf: the Mellin identity on Re w = 1/2
STATEMENTS['z6mhalf'] = '( Y e. RR+ -> %s = ( %s x. ( exp ` -u Y ) ) )' % (VL(GY(), '( 1 / 2 )'), TPI)
# z6mg32: the Gamma bound on Re W = 3, | Gamma ( W ) | <_ 32 2 ^ ( - | Im W | / 4 ) ( gamvb, Gamma ( 3 ) = 2 )
STATEMENTS['z6mg32'] = '( ( W e. CC /\\ ( Re ` W ) = 3 ) -> ( abs ` ( _G ` W ) ) <_ ( ; 3 2 x. %s ) )' % E4('( abs ` ( Im ` W ) )')

# ---- block E-late helper lemmas (z6grcn .. z6ectr; generator tools/gen/z6a_e5.py)
# z6eci1: the product algebra of z6ectri, ( G X ) ( V M ) <_ ( ( X K ) Z ) ( G Q ) from V <_ K Q , M <_ Z
STATEMENTS['z6eci1'] = ('( ( ( ( ( G e. RR /\\ 0 <_ G ) /\\ ( X e. RR /\\ 0 <_ X ) ) /\\ ( ( V e. RR /\\ 0 <_ V ) /\\ V <_ ( K x. Q ) ) /\\ '
                        '( ( M e. RR /\\ 0 <_ M ) /\\ M <_ Z ) ) /\\ ( K e. RR /\\ Q e. RR /\\ Z e. RR ) ) -> '
                        '( ( G x. X ) x. ( V x. M ) ) <_ ( ( ( X x. K ) x. Z ) x. ( G x. Q ) ) )')
# z6eci2: a point on Re = 1/100 lies in HP 0 and meets the hypotheses of the convexity bound CVXH
STATEMENTS['z6eci2'] = ('( ( Z e. CC /\\ ( Re ` Z ) = ( 1 / ; ; 1 0 0 ) ) -> ( ( Z e. %s /\\ 0 <_ ( Re ` Z ) ) /\\ '
                        '( ( 1 / ; ; 2 0 0 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 2 /\\ Z =/= 1 ) ) )' % HPZ)
# z6eci3: a point W with Re S + Re W = 1/100 lies in DS, and -1 < Re W <_ -98/100
STATEMENTS['z6eci3'] = ('( ( %s /\\ ( W e. CC /\\ ( ( Re ` S ) + ( Re ` W ) ) = ( 1 / ; ; 1 0 0 ) ) ) -> '
                        '( W e. %s /\\ ( -u 1 < ( Re ` W ) /\\ ( Re ` W ) <_ -u ( ; 9 8 / ; ; 1 0 0 ) ) ) )' % (SRNG, DS))
# z6ecl0: the left contour line CL = 1/100 - Re S lies in [ -99/100 , -98/100 ] (z6gmoml's range)
STATEMENTS['z6ecl0'] = '( %s -> ( %s e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ %s /\\ %s <_ -u ( ; 9 8 / ; ; 1 0 0 ) ) )' % (SRNG, CL, CL, CL)
# z6eck: the constant X ^ Q KPT z2 R ^ 3 of z6ectri at a real exponent Q is positive
K0 = lambda Q: '( ( ( %s ^c %s ) x. %s ) x. ( %s x. ( R ^ 3 ) ) )' % (XPD, Q, KPT, Z2D)
STATEMENTS['z6eck'] = '( ( %s /\\ ( R e. NN /\\ Q e. RR ) ) -> %s e. RR+ )' % (HZD3, K0('Q'))
# z6ecl2: Gamma on the left line against the moment weight: | Gamma ( C + i U ) | ( 1 + | U | ) ^ 2 <_ ( 50/49 ) 1632 128 2 ^ ( - | U | / 4 )
_GCU = '( abs ` ( _G ` ( C + ( _i x. U ) ) ) )'
_QU = '( ( 1 + ( abs ` U ) ) ^ 2 )'
STATEMENTS['z6ecl2'] = ('( ( ( C e. RR /\\ -u ( ; 9 9 / ; ; 1 0 0 ) <_ C /\\ C <_ -u ( ; 9 8 / ; ; 1 0 0 ) ) /\\ U e. RR ) -> '
                        '( %s x. %s ) <_ ( ( ( ; 5 0 / ; 4 9 ) x. ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) ) x. %s ) )' % (_GCU, _QU, E4('( abs ` U )')))
# z6ecl1: z6ectri at the point CL + i U of the left line (in DS, with the value of GR(R) there)
_ZU = '( %s + ( _i x. U ) )' % CL
AR = '( %s /\\ ( R e. NN /\\ ( mmu ` R ) =/= 0 ) )' % A2HY
STATEMENTS['z6ecl1'] = ('( ( %s /\\ U e. RR ) -> ( %s e. %s /\\ ( abs ` ( %s ` %s ) ) <_ ( %s x. ( ( abs ` ( _G ` %s ) ) x. %s ) ) ) )'
                        % (AR, _ZU, DS, GR('R'), _ZU, K0(CL), _ZU, _QU))
# z6ecl3: the truncated line integral of GR(R) on Re w = CL is below K0 KGL (z6lvert, itgabs, z6ecl1, z6gmoml)
STATEMENTS['z6ecl3'] = '( ( %s /\\ T e. RR+ ) -> ( abs ` %s ) <_ ( %s x. %s ) )' % (AR, LI(GR('R'), CL, 'T'), K0(CL), KGL)
# z6ect1 .. z6ect6, z6ecalg: the pieces of z6ectr (blueprint Lemma 4.2)
PEX = lambda Q: '( ( ( ( ( %s ^c %s ) x. %s ) x. %s ) x. %s ) x. ( %s ^ 3 ) )' % (XPD, Q, KPT, Z2D, KGL, RPD)
_C6 = '; ; ; ; ; 6 0 0 0 0 0'
R3X = lambda Q: '( ( ( ( %s x. CTau ) x. ( log ` D ) ) x. %s ) x. ( D ^c ( ( ( 6 / 5 ) x. %s ) + ( ; 3 7 / ; 3 2 ) ) ) )' % (_C6, KGL, Q)
N14 = ' '.join([';'] * 14 + ['2'] + ['0'] * 14)           # 2 x. 10 ^ 14 as a numeral
K247 = '; ; ; ; ; ; 2 4 7 0 0 0 0'                          # 2470000 >_ KGL
# z6ect1: the finite sum over RSet, | ECTR | <_ X ^ CL KPT z2 KGL R ^ 3 (z6ectrl per r, z6cube)
STATEMENTS['z6ect1'] = '( %s -> ( abs ` %s ) <_ %s )' % (A2HY, ECTR, PEX(CL))
# z6ecalg: the rearrangement of z6ect3
STATEMENTS['z6ecalg'] = ('( ( ( A e. CC /\\ B e. CC /\\ C e. CC ) /\\ ( E e. CC /\\ ( K e. CC /\\ L e. CC /\\ G e. CC ) ) ) -> '
                         '( ( ( ( A x. ( ( K x. B ) x. L ) ) x. C ) x. G ) x. E ) = ( ( ( K x. L ) x. G ) x. ( ( ( A x. B ) x. C ) x. E ) ) )')
# z6ect3: the exponent walk, X ^ Q KPT z2 KGL R ^ 3 = 600000 C_tau log D KGL D ^ ( 6/5 Q + 37/32 )
STATEMENTS['z6ect3'] = '( ( %s /\\ Q e. RR ) -> %s = %s )' % (HZD3, PEX('Q'), R3X('Q'))
# z6ect6: KGL <_ 2470000 (1 / log 2 <_ 81/56, z5dlog2)
STATEMENTS['z6ect6'] = '%s <_ %s' % (KGL, K247)
# z6ect5: the final arithmetic of (T1)
STATEMENTS['z6ect5'] = ('( ( ( ( M e. RR /\\ 0 <_ M ) /\\ ( %s x. M ) <_ 1 ) /\\ ( P e. RR /\\ P <_ ( ( %s x. %s ) x. M ) ) ) -> P <_ ( 1 / 8 ) )'
                        % (N14, _C6, K247))
# z6ect4: (T1) and Q <_ -98/100 give 600000 C_tau log D KGL D ^ ( 6/5 Q + 37/32 ) <_ 1/8
STATEMENTS['z6ect4'] = '( ( ( %s /\\ %s ) /\\ ( Q e. RR /\\ Q <_ -u ( ; 9 8 / ; ; 1 0 0 ) ) ) -> %s <_ ( 1 / 8 ) )' % (HZD3, T1, R3X('Q'))

if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or (ORDER + LATER))
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])
