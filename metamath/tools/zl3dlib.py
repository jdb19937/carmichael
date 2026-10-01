"""Sortie ZL3d helpers: sections A (parameter integrals), F (character theta), G (Mellin
identity) of ZL3-blueprint.md.  STATEMENTS / ORDER are this sortie's frozen statements
(headlines zl3pih, zl3thfe, zl3mel verbatim from tools/zl3lib.py).
`MM_DB=sorties/zl3d.mm python3 tools/zl3dlib.py [LABEL...]` grammar-checks them with mmatch."""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
import zl3lib as ZL3

STATEMENTS = {}
HYPS = {}
ORDER = []


def st(label, text, hyps=()):
    STATEMENTS[label] = ' '.join(text.split())
    HYPS[label] = list(hyps)
    ORDER.append(label)


def split_imp(s):
    toks = s[2:-2].split(' ')
    depth = 0
    for i, t in enumerate(toks):
        if t == '(':
            depth += 1
        elif t == ')':
            depth -= 1
        elif t == '->' and depth == 0:
            return ' '.join(toks[:i]), ' '.join(toks[i + 1:])
    raise ValueError(s)


# ------------------------------------------------------------------ section A objects
PH = split_imp(ZL3.STATEMENTS['zl3pih'])[0]          # the hypotheses of zl3pih (G K B, bound y)
# the same with the bound letter v: the intermediate lemmas keep y (the integration variable)
# out of their antecedents, so that mpteq2dva / offval2 / itgeq2dv ($d y ph) apply
PHV = PH.replace('A. y e. ( 1 [,) +oo ) ( abs ` ( G ` y ) ) <_ ( K x. ( exp ` -u ( B x. y ) ) )',
                 'A. v e. ( 1 [,) +oo ) ( abs ` ( G ` v ) ) <_ ( K x. ( exp ` -u ( B x. v ) ) )')
assert PHV != PH
INTV = '( ( P e. RR /\\ 1 <_ P ) /\\ ( Q e. RR /\\ P <_ Q ) )'   # the interval [ P , Q ], 1 <_ P


def PA(s, P='P', Q='Q', y='y'):
    """int_P^Q G ( y ) y ^ s dy"""
    return 'S. ( %s (,) %s ) ( ( G ` %s ) x. ( %s ^c %s ) ) _d %s' % (P, Q, y, y, s, y)


def PV(s, P='P', Q='Q', y='y'):
    """int_P^Q G ( y ) log y y ^ s dy (the s-derivative of PA)"""
    return 'S. ( %s (,) %s ) ( ( G ` %s ) x. ( ( log ` %s ) x. ( %s ^c %s ) ) ) _d %s' % (P, Q, y, y, y, s, y)


def MJ(j, R='R'):
    """the majorant K e ^ ( -B j ) e ^ ( R log ( j + 1 ) )"""
    return '( ( K x. ( exp ` -u ( B x. %s ) ) ) x. ( exp ` ( %s x. ( log ` ( %s + 1 ) ) ) ) )' % (j, R, j)


def STRIPO(R):
    return "( `' Re \" ( -u %s (,) %s ) )" % (R, R)


IMP = lambda s: '( t e. RR+ |-> S. ( 1 (,) t ) ( ( G ` y ) x. ( y ^c %s ) ) _d y )' % s

# A1 |e ^ U - 1 - U| <_ |U| ^ 2 on the unit disc
st('zl3eqb', '( ( U e. CC /\\ ( abs ` U ) <_ 1 ) -> ( abs ` ( ( ( exp ` U ) - 1 ) - U ) ) <_ ( ( abs ` U ) ^ 2 ) )')
# A1b continuity of x ^c S and log x x. x ^c S on a compact interval of RR+
CXM = lambda s, P='P', Q='Q': '( x e. ( %s [,] %s ) |-> ( x ^c %s ) )' % (P, Q, s)
LXM = lambda s, P='P', Q='Q': '( x e. ( %s [,] %s ) |-> ( ( log ` x ) x. ( x ^c %s ) ) )' % (P, Q, s)
st('zl3cxc', '( ( S e. CC /\\ ( P e. RR+ /\\ Q e. RR ) ) -> ( %s e. ( ( P [,] Q ) -cn-> CC ) /\\ %s e. ( ( P [,] Q ) -cn-> CC ) ) )' % (CXM('S'), LXM('S')))
# A2 integrability of G times a continuous function on a compact subinterval of [ 1 , +oo )
st('zl3gib', '( ( %s /\\ ( ( P e. RR /\\ 1 <_ P ) /\\ Q e. RR ) /\\ H e. ( ( P [,] Q ) -cn-> CC ) ) '
             '-> ( y e. ( P (,) Q ) |-> ( ( G ` y ) x. ( H ` y ) ) ) e. L^1 )' % PHV)
# A3 a linear bound on the difference quotient gives the derivative
st('zl3dvb', '( ( ( D e. ( TopOpen ` CCfld ) /\\ S e. D ) /\\ ( F : D --> CC /\\ V e. CC ) /\\ ( C e. RR /\\ R e. RR+ /\\ '
             'A. z e. D ( ( z =/= S /\\ ( abs ` ( z - S ) ) < R ) -> ( abs ` ( ( ( ( F ` z ) - ( F ` S ) ) / ( z - S ) ) - V ) ) '
             '<_ ( C x. ( abs ` ( z - S ) ) ) ) ) ) -> S ( CC _D F ) V )')
# A4a the ring identity behind the difference quotient
st('zl3alg', '( ( ( A e. CC /\\ U e. CC ) /\\ ( E e. CC /\\ L e. CC ) /\\ ( H e. CC /\\ H =/= 0 ) ) -> ( ( ( 1 / H ) x. ( ( A x. ( U x. E ) ) - ( A x. U ) ) ) '
             '- ( A x. ( L x. U ) ) ) = ( A x. ( U x. ( ( ( E - 1 ) - ( H x. L ) ) / H ) ) ) )')
# A4 the difference-quotient estimate of the parameter integral
st('zl3pdq', '( ( %s /\\ %s /\\ ( ( S e. CC /\\ Z e. CC ) /\\ ( Z =/= S /\\ ( ( abs ` ( Z - S ) ) x. ( log ` Q ) ) <_ 1 ) ) ) -> '
             '( abs ` ( ( ( %s - %s ) / ( Z - S ) ) - %s ) ) <_ ( ( ( ( K x. ( exp ` ( ( abs ` ( Re ` S ) ) x. ( log ` Q ) ) ) ) x. '
             '( ( log ` Q ) ^ 2 ) ) x. ( Q - P ) ) x. ( abs ` ( Z - S ) ) ) )' % (PHV, INTV, PA('Z'), PA('S'), PV('S')))
# A5 the parameter integral is holomorphic with the derivative PV
st('zl3pdv', '( ( %s /\\ %s /\\ D e. ( TopOpen ` CCfld ) ) -> ( ( ( s e. D |-> %s ) e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D ( s e. D |-> %s ) ) ) '
             '/\\ ( CC _D ( s e. D |-> %s ) ) = ( s e. D |-> %s ) ) )' % (PHV, INTV, PA('s'), PA('s'), PA('s'), PV('s')))
# A6 polynomial growth against exponential growth
st('zl3pxe', '( ( R e. RR /\\ E e. RR+ ) -> E. c e. RR+ A. y e. ( 1 [,) +oo ) ( exp ` ( R x. ( log ` y ) ) ) <_ ( c x. ( exp ` ( E x. y ) ) ) )')
# A7 the unit-interval bounds of the integrand, the piece and its derivative
st('zl3pbd', '( ( %s /\\ ( R e. RR /\\ S e. CC /\\ ( ( abs ` ( Re ` S ) ) + 1 ) <_ R ) /\\ ( J e. NN /\\ T e. ( J [,] ( J + 1 ) ) ) ) -> '
             '( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (PHV, PA('S', 'J', 'T'), MJ('J'), PV('S', 'J', 'T'), MJ('J')))
# A8 the majorant is summable
st('zl3msum', '( ( K e. RR+ /\\ B e. RR+ /\\ R e. RR ) -> seq 1 ( + , ( j e. NN |-> %s ) ) e. dom ~~> )' % MJ('j'))
# A9 a function of t within E ( |_ t ) of a convergent sequence at |_ t converges with it
st('zl3flr', '( ( ( F : RR+ --> CC /\\ L e. CC ) /\\ ( S : NN --> CC /\\ S ~~> L ) /\\ ( E : NN --> RR /\\ E ~~> 0 /\\ '
             'A. t e. ( 1 [,) +oo ) ( abs ` ( ( F ` t ) - ( S ` ( |_ ` t ) ) ) ) <_ ( E ` ( |_ ` t ) ) ) ) -> F ~~>r L )')
# A10a partial sums of the unit pieces
FJM = lambda s: '( j e. NN |-> %s )' % PA(s, 'j', '( j + 1 )', 'x')
st('zl3pcs', '( ( %s /\\ S e. CC /\\ N e. NN ) -> ( seq 1 ( + , %s ) ` N ) = %s )' % (PHV, FJM('S'), PA('S', '1', '( N + 1 )')))
# A10 the improper integral is the series of its unit pieces
st('zl3pcv', '( ( %s /\\ S e. CC ) -> %s ~~>r sum_ j e. NN %s )' % (PHV, IMP('S'), PA('S', 'j', '( j + 1 )', 'x')))
st('zl3pih', ZL3.STATEMENTS['zl3pih'])


def gramcheck(labels):
    out = {}
    for lab in labels:
        p = os.path.join('worksheets', 'zl3dg_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=zl3dg_%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for n, h in HYPS.get(lab, []):
                f.write('%s::? |- %s\n' % (n, h))
            f.write('qed::ax-1 |- %s\n$)\n' % STATEMENTS[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'unify', p], capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = [l for l in txt.split('\n') if 'grammar' in l.lower() or 'parse' in l.lower()]
        os.remove(p)
    return out



# ------------------------------------------------------------------ section F: the character theta
HBF = lambda F='F', C='C': ('( %s : ZZ --> CC /\\ ( %s e. RR /\\ A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) ) ) )'
                            % (F, C, F, C))
PZF = ZL3.PZ
SYM = lambda F, j: 'sum_ n e. ( -u %s ... %s ) ( %s ` n )' % (j, j, F)
GB = lambda F='F': '( m e. ZZ |-> ( %s ` ( b + ( m x. M ) ) ) )' % F
st('zl3fzz', '( ( F : ZZ --> CC /\\ J e. NN0 ) -> %s = ( ( F ` 0 ) + sum_ n e. ( 1 ... J ) ( ( F ` n ) + ( F ` -u n ) ) ) )' % SYM('F', 'J'))
st('zl3pzt', '( %s -> ( seq 1 ( + , ( n e. NN |-> ( ( F ` n ) + ( F ` -u n ) ) ) ) e. dom ~~> /\\ A. j e. NN0 ( abs ` ( %s - %s ) ) <_ ( ( 2 x. C ) x. ( ( 1 / 2 ) ^ j ) ) ) )'
   % (HBF(), PZF('F'), SYM('F', 'j')))
st('zl3frg', '( ( ( M e. NN /\\ Q e. ZZ /\\ J e. NN0 ) /\\ F : ZZ --> CC ) -> sum_ n e. ( ( Q x. M ) ... ( ( Q x. M ) + ( ( J x. M ) - 1 ) ) ) ( F ` n ) = '
             'sum_ b e. ( 0 ..^ M ) sum_ m e. ( Q ... ( Q + ( J - 1 ) ) ) ( F ` ( b + ( m x. M ) ) ) )')
st('zl3rgb', '( ( ( M e. NN /\\ %s ) /\\ b e. ( 0 ..^ M ) ) -> %s )' % (HBF(), HBF(GB(), '( C x. ( 2 ^ M ) )')))
st('zl3rg', '( ( M e. NN /\\ %s ) -> %s = sum_ b e. ( 0 ..^ M ) %s )' % (HBF(), PZF('F'), PZF(GB())))
st('zl3pzf', '( ( A e. Fin /\\ A. b e. A ( ( H ` b ) : ZZ --> CC /\\ seq 1 ( + , ( n e. NN |-> ( ( ( H ` b ) ` n ) + ( ( H ` b ) ` -u n ) ) ) ) e. dom ~~> ) ) -> '
             '%s = sum_ b e. A %s )' % (PZF('( k e. ZZ |-> sum_ b e. A ( ( H ` b ) ` k ) )'), PZF('( H ` b )')))

# the character part of section F
CH = lambda Z='Y': '( M e. NN /\\ %s e. ( Base ` ( DChr ` M ) ) )' % Z
LM = ZL3.LM
ZT = lambda Z, x, P: ('( n e. ZZ |-> ( ( %s ` ( %s ` n ) ) x. ( ( n ^ %s ) x. ( exp ` -u ( ( _pi x. ( n ^ 2 ) ) x. ( %s / M ) ) ) ) ) )' % (Z, LM, P, x))
THP = lambda C, x, P: ('sum_ n e. NN ( ( %s ` n ) x. ( ( n ^ %s ) x. ( exp ` -u ( ( _pi x. ( n ^ 2 ) ) x. ( %s / M ) ) ) ) )' % (C, P, x))
CZ = lambda Z: '( a e. NN |-> ( %s ` ( %s ` a ) ) )' % (Z, LM)
st('zl3par', '( %s -> ( ( %s e. { 0 , 1 } /\\ %s e. ( Base ` ( DChr ` M ) ) ) /\\ ( ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) ) ) )'
   % (CH(), ZL3.PAR, ZL3.YB, LM, ZL3.PAR, ZL3.YB, LM, ZL3.PAR))
st('zl3zt', '( ( %s /\\ ( P e. { 0 , 1 } /\\ ( Z ` ( %s ` -u 1 ) ) = ( -u 1 ^ P ) ) /\\ X e. RR+ ) -> ( %s /\\ %s = ( %s + ( 2 x. %s ) ) ) )'
   % (CH('Z'), LM, HBF(ZT('Z', 'X', 'P'), '( exp ` ( 1 / ( _pi x. ( X / M ) ) ) )'), PZF(ZT('Z', 'X', 'P')), ZL3.RM, THP(CZ('Z'), 'X', 'P')))

ZTY = lambda x: ZT('Y', x, ZL3.PAR)
GLB = '( x e. ZZ |-> ( ( ( x + ( b / M ) ) ^ %s ) x. ( exp ` -u ( ( _pi x. ( M / y ) ) x. ( ( x + ( b / M ) ) ^ 2 ) ) ) ) )' % ZL3.PAR
GRB = ('( k e. ZZ |-> ( ( k ^ %s ) x. ( ( exp ` -u ( _pi x. ( ( k ^ 2 ) / ( M / y ) ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( k x. ( b / M ) ) ) ) ) ) )'
       % ZL3.PAR)
KB = '( ( -u _i ^ %s ) x. ( ( M / y ) ^c -u ( ( 1 / 2 ) + %s ) ) )' % (ZL3.PAR, ZL3.PAR)
THGR = '( ( -u _i ^ %s ) x. ( ( ( M / y ) ^c -u ( ( 1 / 2 ) + %s ) ) x. %s ) )' % (ZL3.PAR, ZL3.PAR, PZF(GRB))
st('zl3gb', '( ( ( %s /\\ y e. RR+ ) /\\ b e. ( 0 ..^ M ) ) -> %s = ( ( ( Y ` ( %s ` b ) ) x. ( M ^ %s ) ) x. %s ) )'
   % (CH(), PZF(GB(ZTY('( 1 / y )'))), LM, ZL3.PAR, THGR))

PR = ZL3.PR
EXv = lambda n, x: '( exp ` -u ( ( _pi x. ( %s ^ 2 ) ) x. ( %s / M ) ) )' % (n, x)
ZTgs = lambda Z, n, x, P: '( ( %s ` ( %s ` %s ) ) x. ( ( %s ^ %s ) x. %s ) )' % (Z, LM, n, n, P, EXv(n, x))
st('zl3gs', '( ( %s /\\ y e. RR+ /\\ k e. ZZ ) -> sum_ b e. ( 0 ..^ M ) ( ( Y ` ( %s ` b ) ) x. ( %s ` k ) ) = ( ( M DChrGS Y ) x. %s ) )'
   % (PR, LM, GRB, ZTgs(ZL3.YB, 'k', 'y', ZL3.PAR)))
st('zl3cst', '( ( ( M e. NN /\\ P e. { 0 , 1 } /\\ y e. RR+ ) /\\ T e. CC ) -> ( ( ( M ^ P ) x. ( ( -u _i ^ P ) x. ( ( M / y ) ^c -u ( ( 1 / 2 ) + P ) ) ) ) x. T ) = '
   '( ( T / ( ( _i ^ P ) x. ( M ^c ( 1 / 2 ) ) ) ) x. ( y ^c ( P + ( 1 / 2 ) ) ) ) )')
st('zl3thy', '( ( %s /\\ y e. RR+ ) -> %s = ( %s x. ( ( y ^c ( %s + ( 1 / 2 ) ) ) x. %s ) ) )'
   % (PR, PZF(ZT('Y', '( 1 / y )', ZL3.PAR)), ZL3.EPS, ZL3.PAR, PZF(ZT(ZL3.YB, 'y', ZL3.PAR))))
st('zl3thfe', ZL3.STATEMENTS['zl3thfe'])

st('zl3tc', '( ( %s /\\ ( P e. { 0 , 1 } /\\ ( Z ` ( %s ` -u 1 ) ) = ( -u 1 ^ P ) ) /\\ X e. RR+ ) -> %s e. CC )' % (CH('Z'), LM, THP(CZ('Z'), 'X', 'P')))

# ------------------------------------------------------------------ section G: the Mellin identity
EUI = lambda W, Lc, tt: 'S. ( ( 1 / %s ) (,) %s ) ( ( exp ` -u ( %s x. x ) ) x. ( x ^c ( %s - 1 ) ) ) _d x' % (tt, tt, Lc, W)
st('zl3ew1', '( ( ( W e. CC /\\ 1 < ( Re ` W ) ) /\\ L e. RR+ ) -> ( t e. RR+ |-> %s ) ~~>r ( ( L ^c -u W ) x. ( _G ` W ) ) )' % EUI('W', 'L', 't'))
st('zl3ew2', '( ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ L e. RR+ ) -> ( t e. RR+ |-> %s ) ~~>r ( ( L ^c -u W ) x. ( _G ` W ) ) )' % EUI('W', 'L', 't'))
st('zl3ewb', '( ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ L e. RR+ /\\ T e. RR+ ) -> ( abs ` %s ) <_ ( ( L ^c -u ( Re ` W ) ) x. ( _G ` ( Re ` W ) ) ) )' % EUI('W', 'L', 'T'))

st('zl3dvl', '( ( L e. CC /\\ ( P e. RR /\\ Q e. RR ) ) -> ( RR _D ( x e. ( P [,] Q ) |-> ( exp ` -u ( L x. x ) ) ) ) = ( x e. ( P (,) Q ) |-> ( -u L x. ( exp ` -u ( L x. x ) ) ) ) )')
st('zl3dvw', '( ( ( W e. CC /\\ W =/= 0 ) /\\ ( P e. RR+ /\\ Q e. RR ) ) -> ( RR _D ( x e. ( P [,] Q ) |-> ( ( x ^c W ) / W ) ) ) = ( x e. ( P (,) Q ) |-> ( x ^c ( W - 1 ) ) ) )')

WA = '( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ L e. RR+ )'
st('zl3wtf', '( %s -> ( t e. RR+ |-> ( ( exp ` -u ( L x. t ) ) x. ( ( t ^c W ) / W ) ) ) ~~>r 0 )' % WA)
st('zl3wte', '( %s -> ( t e. RR+ |-> ( ( exp ` -u ( L x. ( 1 / t ) ) ) x. ( ( ( 1 / t ) ^c W ) / W ) ) ) ~~>r 0 )' % WA)


# the theta series of a coefficient function C bounded by 1, parity P
TA = '( ( M e. NN /\\ P e. { 0 , 1 } ) /\\ ( C : NN --> CC /\\ A. i e. NN ( abs ` ( C ` i ) ) <_ 1 ) )'
MP = '( M e. NN /\\ P e. { 0 , 1 } )'
TT = lambda n, x: '( ( C ` %s ) x. ( ( %s ^ P ) x. %s ) )' % (n, n, EXv(n, x))
KE = lambda E: '( exp ` ( 1 / ( _pi x. ( %s / M ) ) ) )' % E
KT = '( %s x. ( exp ` ( _pi / M ) ) )' % KE('1')
st('zl3tb0', '( ( %s /\\ ( E e. RR+ /\\ X e. RR /\\ E <_ X ) /\\ N e. NN ) -> ( ( N ^ P ) x. %s ) <_ ( %s x. ( ( 1 / 2 ) ^ N ) ) )' % (MP, EXv('N', 'X'), KE('E')))
st('zl3tdc', '( ( %s /\\ ( X e. RR /\\ 1 <_ X ) /\\ N e. NN ) -> ( ( N ^ P ) x. %s ) <_ ( ( exp ` -u ( ( _pi / M ) x. ( X - 1 ) ) ) x. ( %s x. ( ( 1 / 2 ) ^ N ) ) ) )'
   % (MP, EXv('N', 'X'), KE('1')))
st('zl3tab', '( ( %s /\\ X e. RR /\\ N e. NN ) -> ( %s e. CC /\\ ( abs ` %s ) <_ ( ( N ^ P ) x. %s ) ) )' % (TA, TT('N', 'X'), TT('N', 'X'), EXv('N', 'X')))
st('zl3thu', '( ( %s /\\ E e. RR+ ) -> ( x e. ( E [,) +oo ) |-> %s ) e. ( ( E [,) +oo ) -cn-> CC ) )' % (TA, THP('C', 'x', 'P')))
st('zl3thd', '( ( %s /\\ ( X e. RR /\\ 1 <_ X ) ) -> ( abs ` %s ) <_ ( %s x. ( exp ` -u ( ( _pi / M ) x. X ) ) ) )' % (TA, THP('C', 'X', 'P'), KT))
GTH = '( y e. ( 1 [,) +oo ) |-> %s )' % THP('C', 'y', 'P')
PHT = ' '.join({'G': GTH, 'K': KT, 'B': '( _pi / M )'}.get(tk, tk) for tk in PHV.split())
st('zl3thph', '( %s -> %s )' % (TA, PHT))
UH = ('( F : NN --> ( CC ^m %s ) /\\ ( H : NN --> RR /\\ seq 1 ( + , H ) e. dom ~~> /\\ '
      'A. j e. NN A. y e. %s ( abs ` ( ( F ` j ) ` y ) ) <_ ( H ` j ) ) )')
st('zl3mex', '( ( ( P e. RR /\\ Q e. RR ) /\\ %s /\\ A. j e. NN ( F ` j ) e. L^1 ) -> '
   'S. ( P (,) Q ) sum_ k e. NN ( ( F ` k ) ` x ) _d x = sum_ k e. NN S. ( P (,) Q ) ( ( F ` k ) ` x ) _d x )'
   % (UH % ('( P (,) Q )', '( P (,) Q )')))
st('zl3tan', '( ( ( A C_ RR /\\ sup ( A , RR* , < ) = +oo ) /\\ %s /\\ A. j e. NN ( F ` j ) ~~>r ( D ` j ) ) -> '
   '( t e. A |-> sum_ k e. NN ( ( F ` k ) ` t ) ) ~~>r sum_ k e. NN ( D ` k ) )' % (UH % ('A', 'A')))

st('zl3fsc', '( ph -> ( x e. X |-> sum_ k e. A B ) e. ( X -cn-> CC ) )',
   [('1', '( ph -> X C_ CC )'), ('2', '( ph -> A e. Fin )'), ('3', '( ( ph /\\ k e. A ) -> ( x e. X |-> B ) e. ( X -cn-> CC ) )')])

LN = lambda n: '( ( _pi x. ( %s ^ 2 ) ) / M )' % n
WS = lambda s_: '( ( %s + P ) / 2 )' % s_
GAMP = lambda s_: '( ( ( M / _pi ) ^c %s ) x. ( _G ` %s ) )' % (WS(s_), WS(s_))
st('zl3lnw', '( ( %s /\\ N e. NN /\\ S e. CC ) -> ( ( N ^ P ) x. ( %s ^c -u %s ) ) = ( ( ( M / _pi ) ^c %s ) x. ( N ^c -u S ) ) )' % (MP, LN('N'), WS('S'), WS('S')))

MTI = lambda W, t: 'S. ( ( 1 / %s ) (,) %s ) ( %s x. ( x ^c ( %s - 1 ) ) ) _d x' % (t, t, THP('C', 'x', 'P'), W)
CK = lambda k: '( ( C ` %s ) x. ( %s ^ P ) )' % (k, k)
st('zl3mtw', '( ( %s /\\ W e. CC /\\ t e. RR+ ) -> %s = sum_ k e. NN ( %s x. %s ) )' % (TA, MTI('W', 't'), CK('k'), EUI('W', LN('k'), 't')))

LSC = lambda s_: 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u %s ) )' % s_
st('zl3mlm', '( ( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) ) -> ( t e. RR+ |-> %s ) ~~>r ( %s x. %s ) )' % (TA, MTI(WS('S'), 't'), GAMP('S'), LSC('S')))

st('zl3inv', '( ( ( ( T e. RR /\\ 1 <_ T ) /\\ ( E e. RR+ /\\ E < ( 1 / T ) ) ) /\\ F e. ( ( E (,) +oo ) -cn-> CC ) ) -> '
   '-u S. ( ( 1 / T ) (,) 1 ) ( F ` u ) _d u = S. ( 1 (,) T ) ( ( F ` ( x ^c -u 1 ) ) x. ( -u 1 x. ( x ^c ( -u 1 - 1 ) ) ) ) _d x )')

st('zl3pol', '( ( Z e. CC /\\ 0 < ( Re ` Z ) ) -> ( t e. RR+ |-> S. ( 1 (,) t ) ( x ^c ( -u Z - 1 ) ) _d x ) ~~>r ( 1 / Z ) )')

st('zl3m1', '( ( %s /\\ M = 1 ) -> ( %s = 0 /\\ %s = 1 ) )' % (ZL3.PR, ZL3.PAR, ZL3.EPS))

GZ = lambda W, E='E', Q='Q', z='z': '( %s e. ( %s (,) %s ) |-> ( %s x. ( %s ^c ( %s - 1 ) ) ) )' % (z, E, Q, THP('C', z, 'P'), z, W)
st('zl3gcz', '( ( ( %s /\\ W e. CC ) /\\ ( E e. RR+ /\\ Q e. RR ) ) -> ( %s e. ( ( E (,) Q ) -cn-> CC ) /\\ %s e. L^1 ) )' % (TA, GZ('W'), GZ('W')))

st('zl3inw', '( ( ( ( ( T e. RR /\\ 1 <_ T ) /\\ ( E e. RR+ /\\ E < ( 1 / T ) ) ) /\\ ( Q e. RR /\\ 1 < Q ) ) /\\ F e. ( ( E (,) Q ) -cn-> CC ) ) -> '
   '-u S. ( ( 1 / T ) (,) 1 ) ( F ` u ) _d u = S. ( 1 (,) T ) ( ( F ` ( x ^c -u 1 ) ) x. ( -u 1 x. ( x ^c ( -u 1 - 1 ) ) ) ) _d x )')

st('zl3alt', '( ( ( R e. CC /\\ E e. CC /\\ U e. CC ) /\\ ( B e. CC /\\ H e. CC /\\ T e. CC ) /\\ ( ( ( R / 2 ) + T ) = ( E x. ( U x. ( ( R / 2 ) + B ) ) ) /\\ ( R x. ( E x. U ) ) = ( R x. H ) ) ) -> '
   'T = ( ( E x. ( U x. B ) ) + ( R x. ( ( H - 1 ) / 2 ) ) ) )')

TFE_R = lambda X: '( ( %s x. ( ( %s ^c ( %s + ( 1 / 2 ) ) ) x. %s ) ) + ( %s x. ( ( ( %s ^c ( 1 / 2 ) ) - 1 ) / 2 ) ) )' % (ZL3.EPS, X, ZL3.PAR, ZL3.TH(ZL3.CYBM, X), ZL3.RM, X)
st('zl3tfe', '( ( %s /\\ X e. RR+ ) -> %s = %s )' % (ZL3.PR, ZL3.TH(ZL3.CYM, '( X ^c -u 1 )'), TFE_R('X')))

VS = lambda s_: '( ( ( 1 - %s ) + P ) / 2 )' % s_
CXA_L = ('( ( ( ( E x. ( ( X ^c ( P + ( 1 / 2 ) ) ) x. B ) ) + ( R x. ( ( ( X ^c ( 1 / 2 ) ) - 1 ) / 2 ) ) ) x. ( ( X ^c -u 1 ) ^c ( %s - 1 ) ) ) x. '
         '( -u 1 x. ( X ^c ( -u 1 - 1 ) ) ) )' % WS('S'))
CXA_R = ('-u ( ( E x. ( B x. ( X ^c ( %s - 1 ) ) ) ) + ( ( R / 2 ) x. ( ( X ^c ( -u ( %s - ( 1 / 2 ) ) - 1 ) ) - ( X ^c ( -u %s - 1 ) ) ) ) )'
         % (VS('S'), WS('S'), WS('S')))
st('zl3cxa', '( ( ( X e. RR+ /\\ ( S e. CC /\\ P e. CC ) ) /\\ ( E e. CC /\\ R e. CC /\\ B e. CC ) ) -> %s = %s )' % (CXA_L, CXA_R))

PPZ = '( ( 1 / S ) + ( 1 / ( 1 - S ) ) )'
st('zl3ppa', '( ( S e. CC /\\ S =/= 0 /\\ S =/= 1 ) -> ( ( 1 / ( ( ( S + 0 ) / 2 ) - ( 1 / 2 ) ) ) - ( 1 / ( ( S + 0 ) / 2 ) ) ) = -u ( 2 x. %s ) )' % PPZ)

TAZ = lambda Z: ' '.join(CZ(Z) if tk == 'C' else tk for tk in TA.split())
st('zl3ta', '( ( %s /\\ P e. { 0 , 1 } ) -> %s )' % (CH('Z'), TAZ('Z')))

WM = '( ( s + %s ) / 2 )' % ZL3.PAR
VM = '( ( ( 1 - s ) + %s ) / 2 )' % ZL3.PAR
JB = lambda t: 'S. ( 1 (,) %s ) ( %s x. ( x ^c ( %s - 1 ) ) ) _d x' % (t, ZL3.TH(ZL3.CYBM, 'x'), VM)
P1 = lambda t: 'S. ( 1 (,) %s ) ( x ^c ( -u ( %s - ( 1 / 2 ) ) - 1 ) ) _d x' % (t, WM)
P2 = lambda t: 'S. ( 1 (,) %s ) ( x ^c ( -u %s - 1 ) ) _d x' % (t, WM)
KT_ = lambda t: 'S. ( ( 1 / %s ) (,) 1 ) ( %s x. ( x ^c ( %s - 1 ) ) ) _d x' % (t, ZL3.TH(ZL3.CYM, 'x'), WM)
KR = lambda t: '( ( %s x. %s ) + ( ( %s / 2 ) x. ( %s - %s ) ) )' % (ZL3.EPS, JB(t), ZL3.RM, P1(t), P2(t))
st('zl3kt', '( ( ( %s /\\ s e. CC ) /\\ ( t e. RR /\\ 1 <_ t ) ) -> %s = %s )' % (ZL3.PR, KT_('t'), KR('t')))

GLM = '( %s x. %s )' % (ZL3.GAMF('s'), ZL3.LS(ZL3.CYM, 's'))
ILB = ZL3.IL(ZL3.CYBM, '( 1 - s )')
PT = '( ( %s / 2 ) x. ( ( 1 / ( %s - ( 1 / 2 ) ) ) - ( 1 / %s ) ) )' % (ZL3.RM, WM, WM)
XV_ = '( %s - ( ( %s x. %s ) + %s ) )' % (GLM, ZL3.EPS, ILB, PT)
IMAP = lambda C: '( t e. RR+ |-> S. ( 1 (,) t ) ( %s x. ( y ^c ( %s - 1 ) ) ) _d y )' % (ZL3.TH(C, 'y'), WM if C == ZL3.CYM else VM)
st('zl3ilm', '( ( ( %s /\\ s e. CC ) /\\ 1 < ( Re ` s ) ) -> %s ~~>r %s )' % (ZL3.PR, IMAP(ZL3.CYM), XV_))

DP = '( ( 1 / ( %s - ( 1 / 2 ) ) ) - ( 1 / %s ) )' % (WM, WM)
st('zl3ilc', '( ( ( %s /\\ s e. CC ) /\\ 1 < ( Re ` s ) ) -> ( ( %s : RR+ --> CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (ZL3.PR, IMAP(ZL3.CYM), ILB, GLM, DP))

st('zl3mel', ZL3.STATEMENTS['zl3mel'])


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])
