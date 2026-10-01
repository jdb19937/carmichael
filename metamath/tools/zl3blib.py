"""Sortie ZL3b helpers (Route Z, ZL3 sections D and E: Poisson summation by residues,
the Gaussian transformation).  Everything of section D is done in the rotated plane
w = i z: the poles of the kernel 1 / ( e ^ ( 2 pi w ) - 1 ) sit on the imaginary axis at
i n, the growing rectangles are R_N = [ -1 - i ( N + 1/2 ) , 1 + i ( N + 1/2 ) ], and the
horizontal lines of the z-plane are the vertical lines of Z6a's machinery (z6lvert,
z6vlcvg, z6shift).

STATEMENTS / ORDER: the frozen statements of ZL3b-blueprint.md.
`MM_DB=sorties/zl3b.mm python3 tools/zl3blib.py [LABEL...]` grammar-checks them.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from zl3lib import *                      # W, hyp, runh, HOL, PZ, FT, ...
import zl3lib as ZL3
from zl2lib import D, chain, go

STATEMENTS = {}
HYPS = {}
ORDER = []


def CP(x, y):
    return '( %s + ( _i x. %s ) )' % (x, y)


def E2(x):
    """e ^ ( 2 pi x )"""
    return '( exp ` ( ( 2 x. _pi ) x. %s ) )' % x


def LI(F, P, Q):
    return '( %s lint <. %s , %s >. )' % (F, P, Q)


def RI(F, P, Q):
    return '( %s rectint <. %s , %s >. )' % (F, P, Q)


def FRC(x1, y1, x2, y2):
    """the frame (four edges) of the rectangle [ x1 + i y1 , x2 + i y2 ], corners simplified"""
    A, P10, B, P01 = CP(x1, y1), CP(x2, y1), CP(x2, y2), CP(x1, y2)
    return '( ( ( %s cseg %s ) u. ( %s cseg %s ) ) u. ( ( %s cseg %s ) u. ( %s cseg %s ) ) )' % (A, P10, P10, B, B, P01, P01, A)


def STRICT(A, B, P):
    return ('( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) )'
            % (A, P, P, B, A, P, P, B))


def RCOND(A, B, P, R):
    return ('( ( %s <_ ( ( Re ` %s ) - ( Re ` %s ) ) /\\ %s <_ ( ( Re ` %s ) - ( Re ` %s ) ) ) /\\ ( %s <_ ( ( Im ` %s ) - ( Im ` %s ) ) /\\ %s <_ ( ( Im ` %s ) - ( Im ` %s ) ) ) )'
            % (R, P, A, R, B, P, R, P, A, R, B, P))


def FRAME(A, B):
    """the raw frame of crectfre / holqhol"""
    P10 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (B, A)
    P01 = '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (A, B)
    return '( ( ( %s cseg %s ) u. ( %s cseg %s ) ) u. ( ( %s cseg %s ) u. ( %s cseg %s ) ) )' % (A, P10, P10, B, B, P01, P01, A)


HALF = '( 1 / 2 )'
D0 = '{ v e. CC | %s =/= 1 }' % E2('v')                               # where the kernel is finite
FK = '( w e. %s |-> ( ( H ` w ) / ( %s - 1 ) ) )' % (D0, E2('w'))     # H ( w ) / ( e ^ ( 2 pi w ) - 1 )
EF = '( w e. CC |-> ( %s - 1 ) )' % E2('w')
HENT = '( H e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D H ) )'


def QN(n):
    """the unit rectangle around the pole i n"""
    return CP('-u 1', '( %s - ( 1 / 2 ) )' % n), CP('1', '( %s + ( 1 / 2 ) )' % n)


def RN(N):
    """R_N"""
    return CP('-u 1', '-u ( %s + ( 1 / 2 ) )' % N), CP('1', '( %s + ( 1 / 2 ) )' % N)


# ------------------------------------------------------------------ D1: the kernel
STATEMENTS['zl3ez'] = '( ( A e. CC /\\ %s = 1 ) -> ( ( Re ` A ) = 0 /\\ ( Im ` A ) e. ZZ ) )' % E2('A')
STATEMENTS['zl3ezn'] = ('( ( N e. ZZ /\\ ( A e. CC /\\ ( ( N - 1 ) < ( Im ` A ) /\\ ( Im ` A ) < ( N + 1 ) ) ) /\\ %s = 1 ) -> A = ( _i x. N ) )'
                        % E2('A'))
STATEMENTS['zl3imopn'] = "( `' Im \" ( A (,) B ) ) e. ( TopOpen ` CCfld )"
STATEMENTS['zl3dve'] = '( %s e. ( CC -cn-> CC ) /\\ ( CC _D %s ) = ( w e. CC |-> ( ( 2 x. _pi ) x. %s ) ) )' % (EF, EF, E2('w'))
# ------------------------------------------------------------------ D2: the residue at a simple zero of the denominator
_A, _B = 'A', 'B'
HOLQCTX = ('( ( ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) ) /\\ ( ( A e. CC /\\ B e. CC ) /\\ ( P e. CC /\\ %s ) /\\ ( A crect B ) C_ D ) ) /\\ '
           '( ( ( R e. RR /\\ %s ) /\\ 0 < R ) /\\ ( M e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ M ) ) )'
           % (STRICT('A', 'B', 'P'), RCOND('A', 'B', 'P', 'R'), FRAME('A', 'B')))
HYPS['zl3qvp'] = [('c', 'C = ( j e. NN0 |-> ( ( y e. ( ( A crect B ) \\ { P } ) |-> ( ( F ` y ) / ( ( y - P ) ^ ( j + 1 ) ) ) ) rectint <. A , B >. ) )'),
                  ('q', 'Q = ( z e. D |-> if ( z = P , ( ( C ` 1 ) / ( 2 x. ( _i x. _pi ) ) ) , ( ( F ` z ) / ( ( z - P ) ^ 1 ) ) ) )')]
STATEMENTS['zl3qvp'] = ('( ( %s /\\ ( F ` P ) = 0 ) -> ( ( Q e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D Q ) ) /\\ ( Q ` P ) = ( ( CC _D F ) ` P ) ) )'
                        % HOLQCTX)
STATEMENTS['zl3res'] = ('( ( ( ( ( H e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D H ) ) /\\ ( E e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D E ) ) ) /\\ '
                        '( ( ( A e. CC /\\ B e. CC ) /\\ ( P e. CC /\\ %s ) /\\ ( A crect B ) C_ D ) /\\ ( ( R e. RR /\\ %s ) /\\ 0 < R ) ) ) /\\ '
                        '( ( ( E ` P ) = 0 /\\ ( ( CC _D E ) ` P ) =/= 0 ) /\\ ( A. b e. D ( b =/= P -> ( E ` b ) =/= 0 ) /\\ '
                        '( G e. V /\\ A. a e. ( ( A crect B ) \\ { P } ) ( G ` a ) = ( ( H ` a ) / ( E ` a ) ) ) ) ) ) -> '
                        '( G rectint <. A , B >. ) = ( ( 2 x. ( _i x. _pi ) ) x. ( ( H ` P ) / ( ( CC _D E ) ` P ) ) ) )'
                        % (STRICT('A', 'B', 'P'), RCOND('A', 'B', 'P', 'R')))
STATEMENTS['zl3resn'] = ('( ( %s /\\ N e. ZZ ) -> %s = ( _i x. ( H ` ( _i x. N ) ) ) )' % (HENT, RI(FK, *QN('N'))))
# ------------------------------------------------------------------ D3: additivity over the unit rectangles
STATEMENTS['zl3rval'] = ('( ( ( X e. RR /\\ Y e. RR ) /\\ ( U e. RR /\\ W e. RR ) /\\ F e. V ) -> %s = ( ( %s + %s ) + ( %s + %s ) ) )'
                         % (RI('F', CP('X', 'U'), CP('Y', 'W')), LI('F', CP('X', 'U'), CP('Y', 'U')), LI('F', CP('Y', 'U'), CP('Y', 'W')),
                            LI('F', CP('Y', 'W'), CP('X', 'W')), LI('F', CP('X', 'W'), CP('X', 'U'))))
STATEMENTS['zl3vsp'] = ('( ( ( ( X e. RR /\\ Y e. RR ) /\\ ( U e. RR /\\ W e. RR /\\ C e. RR ) /\\ ( U < C /\\ C < W ) ) /\\ '
                        '( F e. ( D -cn-> CC ) /\\ ( ( %s u. %s ) u. %s ) C_ D ) ) -> %s = ( %s + %s ) )'
                        % (FRC('X', 'U', 'Y', 'W'), FRC('X', 'U', 'Y', 'C'), FRC('X', 'C', 'Y', 'W'),
                           RI('F', CP('X', 'U'), CP('Y', 'W')), RI('F', CP('X', 'U'), CP('Y', 'C')), RI('F', CP('X', 'C'), CP('Y', 'W'))))
STATEMENTS['zl3frd'] = ('( ( ( U e. RR /\\ W e. RR ) /\\ ( -. U e. ZZ /\\ -. W e. ZZ ) /\\ U <_ W ) -> %s C_ %s )'
                        % (FRC('-u 1', 'U', '1', 'W'), D0))
STATEMENTS['zl3fkcn'] = '( %s -> %s e. ( %s -cn-> CC ) )' % (HENT, FK, D0)
STATEMENTS['zl3rsum'] = ('( ( %s /\\ N e. NN0 ) -> %s = ( _i x. sum_ n e. ( -u N ... N ) ( H ` ( _i x. n ) ) ) )'
                         % (HENT, RI(FK, *RN('N'))))


# ------------------------------------------------------------------ D4-D6: the sides of R_N, the limit, zl3pois
def LT(G, C, T):
    """lint of G along the vertical segment Re = C, | Im | <_ T"""
    return '( %s lint <. ( %s + ( _i x. -u %s ) ) , ( %s + ( _i x. %s ) ) >. )' % (G, C, T, C, T)


def VL(G, C):
    return '( ~~>r ` ( t e. RR+ |-> %s ) )' % LT(G, C, 't')


def GKE(G, A, k='k'):
    """the k-th term G ( y ) e ^ ( k A y ) of the geometric expansion"""
    return '( y e. CC |-> ( ( %s ` y ) x. ( exp ` ( ( %s x. %s ) x. y ) ) ) )' % (G, k, A)


HDEC = 'A. c e. CC ( ( abs ` ( Re ` c ) ) <_ 1 -> ( abs ` ( H ` c ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) )'
HCTX = '( %s /\\ ( K e. RR+ /\\ %s ) )' % (HENT, HDEC)
HT = ('( k e. ZZ |-> ( ~~>r ` ( t e. RR+ |-> S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. '
      '( exp ` -u ( ( 2 x. ( _i x. _pi ) ) x. ( k x. x ) ) ) ) _d x ) ) )')
TPN = '-u ( 2 x. _pi )'
GL = '( w e. CC |-> ( ( H ` w ) x. ( exp ` ( %s x. w ) ) ) )' % TPN
FKL = '( w e. %s |-> ( ( H ` w ) / ( 1 - %s ) ) )' % (D0, E2('w'))
EDGA = ('( ( ( C e. RR /\\ A e. RR ) /\\ ( A x. C ) < 0 ) /\\ ( ( ( G e. ( CC -cn-> CC ) /\\ K e. RR+ ) /\\ '
        'A. b e. RR ( abs ` ( G ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` b ) ) ) ) /\\ ( P e. V /\\ '
        'A. b e. RR ( P ` %s ) = ( ( ( G ` %s ) x. ( exp ` ( A x. %s ) ) ) / ( 1 - ( exp ` ( A x. %s ) ) ) ) ) ) )'
        % (CP('C', 'b'), CP('C', 'b'), CP('C', 'b'), CP('C', 'b'), CP('C', 'b')))
STATEMENTS['zl3kb'] = '( ( A e. CC /\\ ( ( Im ` A ) - ( 1 / 2 ) ) e. ZZ ) -> 1 <_ ( abs ` ( %s - 1 ) ) )' % E2('A')
STATEMENTS['zl3hbd'] = ('( ( %s /\\ ( ( X e. RR /\\ Y e. RR /\\ U e. RR ) /\\ ( ( ( abs ` X ) <_ 1 /\\ ( abs ` Y ) <_ 1 ) /\\ ( U - ( 1 / 2 ) ) e. ZZ ) ) ) -> '
                        '( abs ` %s ) <_ ( ( K x. ( 2 ^c -u ( abs ` U ) ) ) x. ( abs ` ( Y - X ) ) ) )' % (HCTX, LI(FK, CP('X', 'U'), CP('Y', 'U'))))
HYPS['zl3mser'] = [('1', '( ph -> B e. RR )'), ('2', '( ph -> R e. RR )'), ('3', '( ph -> 0 <_ R )'), ('4', '( ph -> R < 1 )'),
                   ('5', '( ( ph /\\ k e. NN ) -> ( F ` k ) e. CC )'), ('6', '( ( ph /\\ k e. NN ) -> ( abs ` ( F ` k ) ) <_ ( B x. ( R ^ k ) ) )')]
STATEMENTS['zl3mser'] = '( ph -> ( seq 1 ( + , F ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( F ` k ) ) <_ ( ( B x. R ) / ( 1 - R ) ) ) )'
STATEMENTS['zl3eseg'] = '( ( %s /\\ T e. RR+ ) -> seq 1 ( + , ( k e. NN |-> %s ) ) ~~> %s )' % (EDGA, LT(GKE('G', 'A'), 'C', 'T'), LT('P', 'C', 'T'))
EBND = lambda T: '( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( ( 2 ^c -u ( %s / 4 ) ) x. ( ( exp ` ( A x. C ) ) / ( 1 - ( exp ` ( A x. C ) ) ) ) ) )' % T
STATEMENTS['zl3edgb'] = ('( ( %s /\\ ( T e. RR+ /\\ 1 <_ T ) ) -> ( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ sum_ k e. NN %s e. CC ) /\\ ( abs ` ( %s - sum_ k e. NN %s ) ) <_ %s ) )'
                         % (EDGA, VL(GKE('G', 'A'), 'C'), VL(GKE('G', 'A'), 'C'), LT('P', 'C', 'T'), VL(GKE('G', 'A'), 'C'), EBND('T')))
STATEMENTS['zl3edge'] = ('( %s -> ( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ sum_ k e. NN %s e. CC ) /\\ A. s e. RR+ ( 1 <_ s -> ( abs ` ( %s - sum_ k e. NN %s ) ) <_ %s ) ) )'
                         % (EDGA, VL(GKE('G', 'A'), 'C'), VL(GKE('G', 'A'), 'C'), LT('P', 'C', 's'), VL(GKE('G', 'A'), 'C'), EBND('s')))
STATEMENTS['zl3shv'] = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ A < B ) /\\ ( ( G e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D G ) ) /\\ ( M e. RR /\\ '
                        'A. b e. CC ( ( A <_ ( Re ` b ) /\\ ( Re ` b ) <_ B ) -> ( abs ` ( G ` b ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` b ) ) ) ) ) ) ) ) -> '
                        '( %s = %s /\\ %s e. CC ) )' % (VL('G', 'B'), VL('G', 'A'), VL('G', 'A')))
STATEMENTS['zl3vl0'] = ('( ( ( G e. ( CC -cn-> CC ) /\\ M e. RR ) /\\ A. b e. RR ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` b ) ) ) ) -> '
                        '( ( ( t e. RR+ |-> S. ( -u t (,) t ) ( G ` %s ) _d x ) e. dom ~~>r /\\ ( ~~>r ` ( t e. RR+ |-> S. ( -u t (,) t ) ( G ` %s ) _d x ) ) e. CC ) /\\ '
                        '%s = ( _i x. ( ~~>r ` ( t e. RR+ |-> S. ( -u t (,) t ) ( G ` %s ) _d x ) ) ) ) )'
                        % (CP('0', 'b'), CP('0', 'x'), CP('0', 'x'), VL('G', '0'), CP('0', 'x')))
STATEMENTS['zl3eaw'] = ('( A e. CC -> ( ( y e. CC |-> ( exp ` ( A x. y ) ) ) e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D ( y e. CC |-> ( exp ` ( A x. y ) ) ) ) ) )')
STATEMENTS['zl3gkr'] = '( ( %s /\\ k e. NN ) -> ( ( %s = %s /\\ %s e. CC ) /\\ ( %s = ( _i x. ( %s ` k ) ) /\\ ( %s ` k ) e. CC ) ) )' % (HCTX, VL(GKE('H', TPN), '1'), VL(GKE('H', TPN), '0'), VL(GKE('H', TPN), '1'), VL(GKE('H', TPN), '0'), HT, HT)
STATEMENTS['zl3gkl'] = ('( ( %s /\\ k e. NN ) -> ( ( %s = %s /\\ %s e. CC ) /\\ ( %s = ( _i x. ( %s ` ( 1 - k ) ) ) /\\ ( %s ` ( 1 - k ) ) e. CC ) ) )'
                        % (HCTX, VL(GKE(GL, '( 2 x. _pi )'), '-u 1'), VL(GKE(GL, '( 2 x. _pi )'), '0'), VL(GKE(GL, '( 2 x. _pi )'), '-u 1'), VL(GKE(GL, '( 2 x. _pi )'), '0'), HT, HT))
STATEMENTS['zl3lrn'] = ('( ( ( ( A e. CC /\\ B e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A cseg B ) C_ D ) ) /\\ ( G e. V /\\ A. b e. ( A cseg B ) ( G ` b ) = -u ( F ` b ) ) ) -> '
                        '( F lint <. B , A >. ) = ( G lint <. A , B >. ) )')
STATEMENTS['zl3fzs'] = ('( ( H : CC --> CC /\\ N e. NN0 ) -> sum_ n e. ( -u N ... N ) ( H ` ( _i x. n ) ) = '
                        '( ( H ` ( _i x. 0 ) ) + sum_ n e. ( 1 ... N ) ( ( H ` ( _i x. n ) ) + ( H ` ( _i x. -u n ) ) ) ) )')
STATEMENTS['zl3sqz'] = ('( ( ( L e. CC /\\ C e. RR ) /\\ ( R e. RR /\\ ( 0 <_ R /\\ R < 1 ) ) /\\ ( S e. V /\\ A. n e. NN ( ( S ` n ) e. CC /\\ '
                        '( abs ` ( ( S ` n ) - L ) ) <_ ( C x. ( R ^ n ) ) ) ) ) -> S ~~> L )')
PZH = '( ( H ` ( _i x. 0 ) ) + sum_ n e. NN ( ( H ` ( _i x. n ) ) + ( H ` ( _i x. -u n ) ) ) )'
SRR = 'sum_ k e. NN %s' % VL(GKE('H', TPN), '1')
SLL = 'sum_ k e. NN %s' % VL(GKE(GL, '( 2 x. _pi )'), '-u 1')
STATEMENTS['zl3d0'] = '( ( A e. CC /\\ ( Re ` A ) =/= 0 ) -> A e. %s )' % D0
RRt = '( exp ` ( %s x. 1 ) )' % TPN
RLt = '( exp ` ( ( 2 x. _pi ) x. -u 1 ) )'
KL = '( K x. ( exp ` ( 2 x. _pi ) ) )'
CT = ('( ( 4 x. K ) + ( ( ( ( 8 x. K ) / ( log ` 2 ) ) x. ( %s / ( 1 - %s ) ) ) + ( ( ( 8 x. %s ) / ( log ` 2 ) ) x. ( %s / ( 1 - %s ) ) ) ) )'
      % (RRt, RRt, KL, RLt, RLt))
STATEMENTS['zl3wbd'] = ('( ( %s /\\ N e. NN ) -> ( ( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> ) /\\ ( %s + %s ) e. CC ) /\\ '
                        '( abs ` ( ( _i x. sum_ n e. ( -u N ... N ) ( H ` ( _i x. n ) ) ) - ( %s + %s ) ) ) <_ ( %s x. ( ( 2 ^c -u ( 1 / 4 ) ) ^ N ) ) ) )'
                        % (HCTX, VL(GKE('H', TPN), '1'), VL(GKE(GL, '( 2 x. _pi )'), '-u 1'), 'sum_ k e. NN %s' % VL(GKE('H', TPN), '1'),
                           'sum_ k e. NN %s' % VL(GKE(GL, '( 2 x. _pi )'), '-u 1'), 'sum_ k e. NN %s' % VL(GKE('H', TPN), '1'),
                           'sum_ k e. NN %s' % VL(GKE(GL, '( 2 x. _pi )'), '-u 1'), CT))
STATEMENTS['zl3wlim'] = ('( %s -> ( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> ) /\\ '
                         '( %s e. CC /\\ ( _i x. %s ) = ( %s + %s ) ) ) )' % (HCTX, VL(GKE('H', TPN), '1'), VL(GKE(GL, '( 2 x. _pi )'), '-u 1'), PZH, PZH, SRR, SLL))
STATEMENTS['zl3wpois'] = '( %s -> %s = %s )' % (HCTX, PZH, PZ(HT))

STATEMENTS['zl3pois'] = ZL3.STATEMENTS['zl3pois']
STATEMENTS['zl3thg'] = ZL3.STATEMENTS['zl3thg']

ORDER = ['zl3ez', 'zl3ezn', 'zl3imopn', 'zl3dve', 'zl3qvp', 'zl3res', 'zl3resn', 'zl3rval', 'zl3vsp', 'zl3frd', 'zl3fkcn', 'zl3rsum', 'zl3kb', 'zl3hbd', 'zl3mser', 'zl3eseg', 'zl3edgb', 'zl3edge', 'zl3shv', 'zl3vl0', 'zl3eaw', 'zl3gkr', 'zl3gkl', 'zl3lrn', 'zl3fzs', 'zl3sqz', 'zl3d0', 'zl3wbd', 'zl3wlim', 'zl3wpois']


# ------------------------------------------------------------------ E: the Gaussian transformation
GAL, GAR = ZL3.GL, ZL3.GR                                   # the two sides of zl3thg


def GF(U, A, B, Pe, v='y'):
    """( v + B ) ^ Pe e ^ ( -pi U ( v + A ) ^ 2 ), an entire function of v"""
    return ('( %s e. CC |-> ( ( ( %s + %s ) ^ %s ) x. ( exp ` -u ( ( _pi x. %s ) x. ( ( %s + %s ) ^ 2 ) ) ) ) )'
            % (v, v, B, Pe, U, v, A))


def TRN(G, S):
    return '( y e. CC |-> ( %s ` ( y + %s ) ) )' % (G, S)


FF = GF('T', 'A', 'A', 'P')                                 # GL on CC
PS1 = GF('-u 1', '0', '0', '0', 'x')                           # e ^ ( pi w ^ 2 ): the Gaussian of the rotated plane
C0 = VL(PS1, '0')                                           # i times the Gaussian integral
FTF = ZL3.FT.replace('( F ` x )', '( %s ` x )' % FF)        # the transform of FF
CTP = '( ( -u _i ^ P ) x. ( T ^c -u ( ( 1 / 2 ) + P ) ) )'
TPAR = '( T e. RR+ /\\ A e. RR /\\ P e. { 0 , 1 } )'
BLC = lambda C: 'A. b e. RR ( abs ` ( G ` %s ) ) <_ ( M x. ( 2 ^c -u ( abs ` b ) ) )' % CP(C, 'b')
GENT = '( G e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D G ) )'
KF = '( ( 2 x. ( ( exp ` ( _pi x. T ) ) x. ( exp ` ( 1 / ( _pi x. T ) ) ) ) ) x. ( 2 ^c ( abs ` A ) ) )'
STATEMENTS['zl3hol'] = '( ( ( U e. CC /\\ P e. NN0 ) /\\ ( A e. CC /\\ B e. CC ) ) -> %s )' % HOL(GF('U', 'A', 'B', 'P'), 'CC')
STATEMENTS['zl3gre'] = ('( ( T e. RR+ /\\ X e. RR ) -> ( ( 1 + ( abs ` X ) ) x. ( exp ` -u ( ( _pi x. T ) x. ( X ^ 2 ) ) ) ) <_ '
                        '( ( exp ` ( 1 / ( _pi x. T ) ) ) x. ( 2 ^c -u ( abs ` X ) ) ) )')
STATEMENTS['zl3gcb'] = ('( ( ( T e. RR+ /\\ P e. { 0 , 1 } ) /\\ ( U e. CC /\\ V e. CC ) /\\ ( ( C e. RR /\\ R e. RR ) /\\ ( 0 <_ C /\\ '
                        '( abs ` U ) <_ ( ( abs ` ( Re ` V ) ) + C ) /\\ ( abs ` ( Im ` V ) ) <_ R ) ) ) -> '
                        '( abs ` ( ( U ^ P ) x. ( exp ` -u ( ( _pi x. T ) x. ( V ^ 2 ) ) ) ) ) <_ '
                        '( ( ( 1 + C ) x. ( ( exp ` ( ( _pi x. T ) x. ( R ^ 2 ) ) ) x. ( exp ` ( 1 / ( _pi x. T ) ) ) ) ) x. ( 2 ^c -u ( abs ` ( Re ` V ) ) ) ) )')
STATEMENTS['zl3fb'] = ('( %s -> ( %s e. RR+ /\\ A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( %s ` z ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) ) ) )'
                       % (TPAR, KF, FF, KF))
STATEMENTS['zl3ltr'] = ('( ( ( P e. CC /\\ Q e. CC /\\ S e. CC ) /\\ G : CC --> CC ) -> %s = %s )'
                        % (LI(TRN('G', 'S'), 'P', 'Q'), LI('G', '( P + S )', '( Q + S )')))
STATEMENTS['zl3tl'] = ('( ( ( L e. CC /\\ C e. RR ) /\\ ( D e. RR+ /\\ Y e. RR ) /\\ ( F : RR+ --> CC /\\ A. s e. RR+ ( Y <_ s -> '
                       '( abs ` ( ( F ` s ) - L ) ) <_ ( C x. ( ( 2 ^c -u ( s / 4 ) ) ^c D ) ) ) ) ) -> F ~~>r L )')
STATEMENTS['zl3epc'] = ('( ( ( ( C e. RR /\\ G e. ( CC -cn-> CC ) ) /\\ ( M e. RR /\\ %s ) ) /\\ ( ( H e. RR /\\ V e. RR /\\ W e. RR ) /\\ '
                        '( ( H <_ V /\\ H <_ W ) \\/ ( V <_ -u H /\\ W <_ -u H ) ) ) ) -> ( abs ` %s ) <_ ( ( M x. ( 2 ^c -u H ) ) x. ( abs ` ( W - V ) ) ) )'
                        % (BLC('C'), LI('G', CP('C', 'V'), CP('C', 'W'))))
STATEMENTS['zl3v2'] = ('( ( ( C e. RR /\\ G e. ( CC -cn-> CC ) ) /\\ ( ( U e. RR /\\ V e. RR /\\ W e. RR ) /\\ ( U <_ V /\\ V <_ W /\\ U < W ) ) ) -> '
                       '%s = ( %s + %s ) )' % (LI('G', CP('C', 'U'), CP('C', 'W')), LI('G', CP('C', 'U'), CP('C', 'V')), LI('G', CP('C', 'V'), CP('C', 'W'))))
STATEMENTS['zl3vtr'] = ('( ( ( C e. RR /\\ E e. RR ) /\\ ( ( G e. ( CC -cn-> CC ) /\\ M e. RR ) /\\ %s ) ) -> ( t e. RR+ |-> %s ) ~~>r %s )'
                        % (BLC('C'), LT(TRN('G', '( _i x. E )'), 'C', 't'), VL('G', 'C')))
STATEMENTS['zl3csh'] = ('( ( ( A e. RR /\\ E e. RR ) /\\ ( %s /\\ ( M e. RR /\\ A. c e. CC ( ( abs ` ( Re ` c ) ) <_ ( abs ` A ) -> '
                        '( abs ` ( G ` c ) ) <_ ( M x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) ) ) ) ) -> ( t e. RR+ |-> %s ) ~~>r %s )'
                        % (GENT, LT(TRN('G', CP('A', 'E')), '0', 't'), VL('G', '0')))
STATEMENTS['zl3lod'] = '( ( ( A e. CC /\\ G e. ( CC -cn-> CC ) ) /\\ A. y e. CC ( G ` -u y ) = -u ( G ` y ) ) -> ( G lint <. -u A , A >. ) = 0 )'
STATEMENTS['zl3lsc'] = ('( ( ( P e. CC /\\ Q e. CC ) /\\ ( L e. CC /\\ L =/= 0 ) /\\ G e. ( CC -cn-> CC ) ) -> '
                        '( ( y e. CC |-> ( G ` ( L x. y ) ) ) lint <. P , Q >. ) = ( ( G lint <. ( L x. P ) , ( L x. Q ) >. ) / L ) )')
STATEMENTS['zl3scl'] = ('( ( L e. RR+ /\\ ( ( G e. ( CC -cn-> CC ) /\\ M e. RR ) /\\ %s ) ) -> ( ( t e. RR+ |-> %s ) ~~>r ( %s / L ) /\\ %s e. CC ) )'
                        % (BLC('0'), LT('( y e. CC |-> ( G ` ( L x. y ) ) )', '0', 't'), VL('G', '0'), VL('G', '0')))
STATEMENTS['zl3ftw'] = ('( ( T e. RR+ /\\ P e. { 0 , 1 } /\\ K e. RR ) -> ( ( t e. RR+ |-> %s ) ~~>r ( ( K ^ P ) x. ( %s / ( sqrt ` T ) ) ) /\\ %s e. CC ) )'
                        % (LT(GF('-u T', '0', 'K', 'P', 'w'), '0', 't'), C0, C0))
STATEMENTS['zl3ft'] = '( ( %s /\\ j e. ZZ ) -> ( %s ` j ) = ( ( %s x. ( -u _i x. %s ) ) x. ( %s ` j ) ) )' % (TPAR, FTF, CTP, C0, GAR)
STATEMENTS['zl3pzm'] = ('( ( ( C e. CC /\\ G e. V /\\ H e. W ) /\\ ( A. m e. ZZ ( ( H ` m ) e. CC /\\ ( G ` m ) = ( C x. ( H ` m ) ) ) /\\ '
                        'seq 1 ( + , ( m e. NN |-> ( ( H ` m ) + ( H ` -u m ) ) ) ) e. dom ~~> ) ) -> %s = ( C x. %s ) )' % (PZ('G'), PZ('H')))
STATEMENTS['zl3grc'] = '( %s -> seq 1 ( + , ( m e. NN |-> ( ( %s ` m ) + ( %s ` -u m ) ) ) ) e. dom ~~> )' % (TPAR, GAR, GAR)
STATEMENTS['zl3thg0'] = '( %s -> %s = ( ( %s x. ( -u _i x. %s ) ) x. %s ) )' % (TPAR, PZ(GAL), CTP, C0, PZ(GAR))
STATEMENTS['zl3c1'] = '( -u _i x. %s ) = 1' % C0
ORDER += ['zl3hol', 'zl3gre', 'zl3gcb', 'zl3fb', 'zl3ltr', 'zl3tl', 'zl3epc', 'zl3v2', 'zl3vtr', 'zl3csh', 'zl3lod', 'zl3lsc', 'zl3scl',
          'zl3ftw', 'zl3ft', 'zl3pzm', 'zl3grc', 'zl3thg0', 'zl3c1']

KAP = '( j / T )'
SJ = CP('-u %s' % KAP, 'A')
OMJ = GF('-u T', '0', KAP, 'P', 'w')
EJ = '( ( exp ` -u ( _pi x. ( ( j ^ 2 ) / T ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) ) ) )'
CSTJ = '( ( -u _i ^ P ) x. %s )' % EJ
STATEMENTS['zl3fti'] = ('( ( %s /\\ ( j e. ZZ /\\ X e. RR ) ) -> ( %s x. ( %s ` %s ) ) = ( ( %s ` X ) x. ( exp ` -u ( ( 2 x. ( _i x. _pi ) ) x. ( j x. X ) ) ) ) )'
                        % (TPAR, CSTJ, TRN(OMJ, SJ), CP('0', 'X'), FF))
ORDER.insert(ORDER.index('zl3ft'), 'zl3fti')

ITR = '( t e. RR+ |-> S. ( -u t (,) t ) ( %s ` %s ) _d x )' % (TRN(OMJ, SJ), CP('0', 'x'))
STATEMENTS['zl3ftv'] = '( ( %s /\\ j e. ZZ ) -> %s ~~>r ( -u _i x. ( ( %s ^ P ) x. ( %s / ( sqrt ` T ) ) ) ) )' % (TPAR, ITR, KAP, C0)
ORDER.insert(ORDER.index('zl3ft'), 'zl3ftv')


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('zl3bg' + lab, 'grammar check of %s' % lab)
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


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])
