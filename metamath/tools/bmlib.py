"""Sortie BM: BMembership.lean + BMembership21.lean, ending in `pigeonhole_21'`
(`bmpig21`, the AGP 3.1 pigeonhole statement in carmsw.3's exact matrix, conditional
on ( LOGFREE /\\ LOGGED )).  Frozen statements `S`, objects, helpers.

    python3 tools/bmlib.py print                                  # the frozen table
    MM_DB=sorties/bm.mm python3 tools/bmlib.py check [LABEL...]   # grammar check (mmatch)
    MM_DB=sorties/bm.mm python3 tools/gen/bm_freeze.py check      # matrix = carmsw.3 verbatim

Letters.  The matrix of carmsw.3 is fixed (x l q p k d m; carmsw.3's D and F are the outer
existentials, here `a` and `r`, chosen outside carmtmw's `$d ph ...` list b e i k m n q u v z).
The BMembership hypotheses of `bmpig` (A5's explicit-hypothesis idiom) bind
  LOWER: c g e q (Lean x y d a), n (the count), i (the exceptional set)
  BT (bruntitex's body): y m i;  PI: y;  card/ge2: n i
and their free witnesses at the top are j b f s t; the proof of `bmpig` generalises over
x l w o u only, so no letter of a hypothesis meets a `$d ph`.  The helper lemmas are closed.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'gen'))
import num
from zdilib import LOGFREE, LOGGED
from btlib import body as BTBODY, Z2, RPOW, CNT as BTCNT, BND as BTBND

ROOT = os.path.join(HERE, '..')

# ---- literals ---------------------------------------------------------------------------
F21 = '( ; 2 1 / ; ; 1 0 0 )'
F79 = '( ; 7 9 / ; ; 1 0 0 )'
F79H = '( ; 7 9 / ; ; 2 0 0 )'
F793200 = '( ; 7 9 / ; ; ; 3 2 0 0 )'
F3160 = '( 3 / ; ; 1 6 0 )'
F1920 = '( ; 1 9 / ; 2 0 )'
F1110 = '( ; 1 1 / ; 1 0 )'
F112 = '( 1 / ; 1 2 )'
F110 = '( 1 / ; 1 0 )'
F120 = '( 1 / ; 2 0 )'
F132 = '( 1 / ; 3 2 )'
F191 = '( ; ; 1 9 1 / ; ; 9 0 0 )'
F709 = '( ; ; 7 0 9 / ; ; 9 0 0 )'
F53 = '( 5 / 3 )'
F35 = '( 3 / 5 )'
F116 = '( ; 1 1 / 6 )'
F511 = '( 5 / ; 1 1 )'
F303800 = '( ; ; 3 0 3 / ; ; 8 0 0 )'
F121279 = '( ; ; ; 1 2 1 2 / ; 7 9 )'
N100 = '; ; 1 0 0'


# ---- objects ----------------------------------------------------------------------------
def DIV(n):
    """the divisor set of n as carmsw.3 writes it"""
    return '{ m e. ( 1 ... %s ) | m || %s }' % (n, n)


def CNTS(n, y, d='d'):
    return '{ %s e. %s | %s <_ %s }' % (d, DIV(n), d, y)


def CNT(n, y, d='d'):
    """the number of divisors of n up to y"""
    return '( # ` %s )' % CNTS(n, y, d)


def XB(x):
    return '( %s ^c %s )' % (x, F21)


def X1B(x):
    return '( %s ^c %s )' % (x, F79)


def XH(x):
    return '( %s ^c %s )' % (x, F79H)


def PF(l, v='v', u='u'):
    """the prime factors of l (the lemmas' letters; carmsw.3 writes { p e. Prime | p || l })"""
    return '{ %s e. Prime | %s || %s }' % (u, u, l)


def PCOND(d, k, x):
    return '( ( ( %s x. %s ) + 1 ) <_ %s /\\ ( ( %s x. %s ) + 1 ) e. Prime )' % (d, k, x, d, k)


def PSET(l, k, x, d='d'):
    """the divisors d of l with d k + 1 a prime up to x (carmsw.3's second set)"""
    return '{ %s e. %s | %s }' % (d, DIV(l), PCOND(d, k, x))


def ANTE(z, x, l, sumb):
    return ('( ( %s < %s /\\ 1 < %s /\\ ( mmu ` %s ) =/= 0 ) /\\ ( A. q e. Prime ( q || %s -> q <_ %s ) /\\ '
            'sum_ q e. { p e. Prime | p || %s } ( 1 / q ) <_ %s ) )' % (z, x, l, l, l, XH(x), l, sumb))


def BOUND(a, x, l):
    return '( ( ( 2 ^c ( -u %s - 2 ) ) / ( log ` %s ) ) x. %s )' % (a, x, CNT(l, XB(x)))


def CONS(a, x, l):
    return ('E. k e. NN ( ( k <_ %s /\\ ( k gcd %s ) = 1 ) /\\ %s <_ ( # ` %s ) )'
            % (X1B(x), l, BOUND(a, x, l), PSET(l, 'k', x)))


def MATRIX(a, z, sumb):
    """carmsw.3's matrix with D := a, F := z and the sum bound sumb"""
    return 'A. x e. NN0 A. l e. NN0 ( %s -> %s )' % (ANTE(z, 'x', 'l', sumb), CONS(a, 'x', 'l'))


DA, DZ = 'a', 'r'       # the outer existentials (Lean D, z_3)
PIG = lambda sumb: 'E. %s e. NN0 E. %s e. NN0 %s' % (DA, DZ, MATRIX(DA, DZ, sumb))

FMAP = lambda f: '%s : NN0 --> ( ~P NN i^i Fin )' % f
CARD = lambda f, j: 'A. n e. NN0 ( # ` ( %s ` n ) ) <_ %s' % (f, j)
GE2 = lambda f: 'A. n e. NN0 A. i e. ( %s ` n ) 2 <_ i' % f


def THETA(b, f, e=F112, n='n'):
    """t21thm's third conjunct at E := e with its x-letter l renamed n"""
    return ('A. %s e. NN0 A. d e. NN A. a e. ZZ A. z e. RR ( ( ( %s <_ %s /\\ ( a gcd d ) = 1 ) /\\ ( d <_ ( %s ^c %s ) /\\ '
            '( d x. ( %s ^c %s ) ) <_ z /\\ z <_ %s ) /\\ A. i e. ( %s ` %s ) -. i || d ) -> '
            '( abs ` ( ( a ( thetaAP ` d ) z ) - ( z / ( phi ` d ) ) ) ) <_ ( ( %s x. z ) / ( phi ` d ) ) )'
            % (n, b, n, n, F191, n, F709, n, f, n, e))


def BODY1(j, b, f):
    """t21thm's existential body at E := 1/12 (letter n for Lean's x)"""
    return '( %s /\\ ( %s /\\ %s ) /\\ %s )' % (FMAP(f), CARD(f, j), GE2(f), THETA(b, f))


def RESCNT(g, e, q, n='n'):
    """the primes up to g congruent to q mod e"""
    return '( # ` { %s e. ( 0 ... %s ) | ( %s e. Prime /\\ ( %s mod %s ) = ( %s mod %s ) ) } )' % (n, g, n, n, e, q, e)


def LOWER(b, f):
    """BMembership.lower at B = 21/100 (Lean x y d a -> c g e q)"""
    return ('A. c e. NN0 A. g e. NN0 A. e e. NN A. q e. ZZ ( ( ( %s <_ c /\\ ( q gcd e ) = 1 ) /\\ ( e <_ %s /\\ ( e x. %s ) <_ g /\\ g <_ c ) /\\ '
            'A. i e. ( %s ` c ) -. i || e ) -> ( ( ppi ` g ) / ( 2 x. ( phi ` e ) ) ) <_ %s )'
            % (b, XB('c'), X1B('c'), f, RESCNT('g', 'e', 'q')))


def PIB(u):
    """PiLower's body at threshold u"""
    return 'A. y e. NN0 ( %s <_ y -> ( y / ( %s x. ( log ` y ) ) ) <_ ( ppi ` y ) )' % (u, F1110)


def PPIB(s):
    """ppiubeps at E = 1/10 with letters s, y"""
    return 'A. y e. ( ZZ>= ` %s ) ( ppi ` y ) <_ ( ( ( ( log ` 4 ) + %s ) x. y ) / ( log ` y ) )' % (s, F110)


BP = lambda b, s: '( ( abs ` %s ) + ( ( ( %s + 1 ) ^ 2 ) + 2 ) )' % (b, s)     # bMembership21's x_2
UP = lambda b: '( ( abs ` %s ) + 2 )' % b                                     # piLower_of_density's threshold

# per-divisor objects (Lean per_divisor_lower)
YC = lambda x, e: '( |^ ` ( %s x. %s ) )' % (e, X1B(x))                        # y = ceil( d x^(1-B) )
WT = lambda x, e: '( ( %s x. %s ) / ( ( phi ` %s ) x. ( log ` %s ) ) )' % (e, X1B(x), e, x)
KF = lambda x, l: '{ z e. ( 1 ... ( |_ ` %s ) ) | ( z gcd %s ) = 1 }' % (X1B(x), l)
SK = lambda x, l, e: '{ k e. %s | %s }' % (KF(x, l), PCOND(e, 'k', x))
ASET = lambda y, e: '{ n e. ( 0 ... %s ) | ( n e. Prime /\\ ( n mod %s ) = ( 1 mod %s ) ) }' % (y, e, e)
AQ = lambda y, e, q: '{ i e. ( 0 ... %s ) | ( i e. Prime /\\ ( i mod ( %s x. %s ) ) = ( 1 mod ( %s x. %s ) ) ) }' % (y, e, q, e, q)
A0 = lambda y, e, l: '{ h e. %s | ( ( ( h - 1 ) / %s ) gcd %s ) = 1 }' % (ASET(y, e), e, l)
LOWI = lambda x, e: '( ( ppi ` %s ) / ( 2 x. ( phi ` %s ) ) ) <_ ( # ` %s )' % (YC(x, e), e, ASET(YC(x, e), e))
PDLC = lambda x: '( %s x. ( %s / ( log ` %s ) ) )' % (F120, X1B(x), x)

# ---- frozen statements -------------------------------------------------------------------
S = {}
H = {}

S['bmeldiv'] = '( N e. NN -> ( A e. %s <-> ( A e. NN /\\ A || N ) ) )' % DIV('N')
S['bmhashim'] = '( ( F Fn A /\\ B e. Fin /\\ B C_ A ) -> ( # ` ( F " B ) ) <_ ( # ` B ) )'
H['bmhashsum'] = {1: '( x = y -> ( ph <-> ps ) )'}
S['bmhashsum'] = '( A e. Fin -> ( # ` { x e. A | ph } ) = sum_ y e. A if ( ps , 1 , 0 ) )'
S['bmtot'] = '( ( D e. NN /\\ Q e. Prime ) -> ( ( phi ` D ) x. ( Q - 1 ) ) <_ ( phi ` ( D x. Q ) ) )'
S['bmlog4'] = '( ( log ` 4 ) + %s ) <_ %s' % (F110, F116)
S['bmpow'] = '( J e. NN0 -> ( ( 2 ^c ( -u ( J + 3 ) - 2 ) ) x. ( 2 ^ J ) ) = %s )' % F132

# the reduced modulus (exists_reduced_modulus)
S['bmhalf'] = '( ( ( W e. NN /\\ ( mmu ` W ) =/= 0 ) /\\ ( P e. Prime /\\ P || W ) ) -> A. y e. RR %s <_ ( 2 x. %s ) )' % (CNT('W', 'y'), CNT('( W / P )', 'y'))
PRED = lambda s: ('A. n e. NN ( ( ( mmu ` n ) =/= 0 /\\ A. i e. %s 2 <_ i ) -> E. w e. NN ( w || n /\\ A. i e. %s -. i || w /\\ '
                  'A. y e. RR %s <_ ( ( 2 ^ ( # ` %s ) ) x. %s ) ) )' % (s, s, CNT('n', 'y'), s, CNT('w', 'y')))
S['bmred0'] = PRED('(/)')
S['bmredlem'] = '( ( t e. Fin /\\ -. u e. t ) -> ( %s -> %s ) )' % (PRED('t'), PRED('( t u. { u } )'))
S['bmred'] = ('( ( ( L e. NN /\\ ( mmu ` L ) =/= 0 ) /\\ ( G e. Fin /\\ A. i e. G 2 <_ i ) /\\ ( J e. NN0 /\\ ( # ` G ) <_ J ) ) -> '
              'E. w e. NN ( w || L /\\ A. i e. G -. i || w /\\ A. y e. RR %s <_ ( ( 2 ^ J ) x. %s ) ) )' % (CNT('L', 'y'), CNT('w', 'y')))

# per-divisor lower bound (per_divisor_lower), closed lemmas over letters
XHYP = '( X e. NN0 /\\ 3 <_ X )'
EHYP = '( E e. NN /\\ E <_ %s )' % XB('X')
THYP = '( T e. RR /\\ T <_ %s )' % X1B('X')
UHYP = '( U e. RR /\\ U <_ %s )' % X1B('X')
LHYP = '( L e. NN /\\ A. v e. Prime ( v || L -> v <_ %s ) /\\ sum_ v e. %s ( 1 / v ) <_ %s )' % (XH('X'), PF('L'), F793200)
XF = '( ( X e. RR+ /\\ 1 < X /\\ ( log ` X ) e. RR+ ) /\\ ( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ ) /\\ ( ( %s x. %s ) = X /\\ ( %s x. %s ) = %s ) )' % (X1B('X'), XB('X'), XH('X'), XB('X'), X1B('X'), XH('X'), XH('X'), X1B('X'))
S['bmpdlx'] = '( %s -> %s )' % (XHYP, XF)
DXE = '( E x. %s )' % X1B('X')
YF = '( ( %s e. NN0 /\\ %s <_ %s ) /\\ ( %s < ( %s + 1 ) /\\ %s <_ ( ( ; ; 1 0 1 / ; ; 1 0 0 ) x. %s ) ) /\\ ( %s <_ %s /\\ %s <_ X ) )' % (YC('X', 'E'), DXE, YC('X', 'E'), YC('X', 'E'), DXE, YC('X', 'E'), DXE, X1B('X'), DXE, YC('X', 'E'))
S['bmpdly'] = '( ( %s /\\ ( %s <_ %s /\\ %s ) ) -> %s )' % (XHYP, N100, X1B('X'), EHYP, YF)
S['bmpdlbt'] = ('( ( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( Q e. Prime /\\ Q <_ %s ) ) -> '
                '( # ` %s ) <_ ( ( %s x. %s ) x. ( 1 / Q ) ) )'
                % (XHYP, N100, X1B('X'), EHYP, THYP, BTBODY('T'), XH('X'), AQ(YC('X', 'E'), 'E', 'Q'), F121279, WT('X', 'E')))
S['bmpdlsum'] = ('( ( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ %s ) -> '
                 'sum_ v e. %s ( # ` %s ) <_ ( %s x. %s ) )'
                 % (XHYP, N100, X1B('X'), EHYP, THYP, BTBODY('T'), LHYP, PF('L'), AQ(YC('X', 'E'), 'E', 'v'), F303800, WT('X', 'E')))
S['bmpdlsplit'] = ('( ( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ L e. NN ) -> ( # ` %s ) <_ ( ( # ` %s ) + sum_ v e. %s ( # ` %s ) ) )'
                   % (XHYP, N100, X1B('X'), EHYP, ASET(YC('X', 'E'), 'E'), A0(YC('X', 'E'), 'E', 'L'), PF('L'), AQ(YC('X', 'E'), 'E', 'v')))
S['bmpdlinj'] = ('( ( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ L e. NN ) -> ( # ` %s ) <_ ( # ` %s ) )'
                 % (XHYP, N100, X1B('X'), EHYP, A0(YC('X', 'E'), 'E', 'L'), SK('X', 'L', 'E')))
S['bmpdlmain'] = ('( ( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ %s ) -> ( %s x. %s ) <_ ( # ` %s ) )'
                  % (XHYP, N100, X1B('X'), EHYP, UHYP, PIB('U'), LOWI('X', 'E'), F511, WT('X', 'E'), ASET(YC('X', 'E'), 'E')))
S['bmpdl'] = ('( ( ( %s /\\ %s /\\ ( %s <_ %s /\\ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) -> %s <_ ( # ` %s ) )'
              % (XHYP, LHYP, N100, X1B('X'), THYP, UHYP, BTBODY('T'), PIB('U'), EHYP, LOWI('X', 'E'), PDLC('X'), SK('X', 'L', 'E')))

# the double counting and the pigeonhole over k
S['bmdc'] = ('( ( ( D e. Fin /\\ K e. Fin /\\ K =/= (/) ) /\\ ( ( X e. RR /\\ 0 < X ) /\\ ( C e. RR /\\ 0 <_ C ) /\\ ( # ` K ) <_ X ) /\\ '
             'A. o e. D C <_ ( # ` { k e. K | %s } ) ) -> E. u e. K ( ( C x. ( # ` D ) ) / X ) <_ ( # ` { v e. D | %s } ) )'
             % (PCOND('o', 'k', 'M'), PCOND('v', 'u', 'M')))
S['bmssdiv'] = ('( ( L e. NN /\\ W e. NN /\\ W || L ) -> { v e. %s | %s } C_ %s )'
                % (CNTS('W', 'Y'), PCOND('v', 'U', 'M'), PSET('L', 'U', 'M')))

# the pigeonhole (pigeonhole_of_BMembership), A5's explicit-hypothesis idiom
H['bmpig'] = {
    1: '( ph -> J e. NN0 )',
    2: '( ph -> B e. RR )',
    3: '( ph -> %s )' % FMAP('F'),
    4: '( ph -> %s )' % CARD('F', 'J'),
    5: '( ph -> %s )' % GE2('F'),
    6: '( ph -> %s )' % LOWER('B', 'F'),
    7: '( ph -> T e. RR )',
    8: '( ph -> %s )' % BTBODY('T'),
    9: '( ph -> U e. RR )',
    10: '( ph -> %s )' % PIB('U'),
}
S['bmpig'] = '( ph -> %s )' % PIG(F793200)

# BMembership21
S['bmlow'] = ('( ( ( B e. RR /\\ %s ) /\\ %s /\\ ( S e. NN /\\ %s ) ) -> %s )'
              % (FMAP('F'), THETA('B', 'F'), PPIB('S'), LOWER(BP('B', 'S'), 'F')))
S['bmpil'] = ('( ( ( B e. RR /\\ %s ) /\\ %s /\\ %s ) -> %s )'
              % (FMAP('F'), GE2('F'), THETA('B', 'F'), PIB(UP('B'))))
S['bmpig21b'] = ('( ( ( ( j e. NN0 /\\ b e. RR ) /\\ %s ) /\\ ( s e. NN /\\ %s ) /\\ ( t e. NN0 /\\ %s ) ) -> %s )'
                 % (BODY1('j', 'b', 'f'), PPIB('s'), BTBODY('t'), PIG(F793200)))
S['bmpig21a'] = '( ( %s /\\ %s ) -> %s )' % (LOGFREE, LOGGED, PIG(F793200))
S['bmpig21'] = '( ( %s /\\ %s ) -> %s )' % (LOGFREE, LOGGED, PIG(F3160))

ORDER = list(S)


def stmt(label):
    """the assertion of LABEL from sorties/bm.mm or carmichael.mm, without |-"""
    for fn in ('sorties/bm.mm', 'carmichael.mm'):
        txt = open(os.path.join(ROOT, fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def check(labels):
    d = os.path.join(ROOT, 'scratch', 'bmgc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'bmgc%s.mmp' % lab)
        hy = H.get(lab, {})
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=bmgc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for i in sorted(hy):
                f.write('h%d::bmgc%s.%d |- %s\n' % (i, lab, i, hy[i]))
            f.write('h99::bmgc%s.99 |- %s\n' % (lab, S[lab]))
            f.write('qed:h99:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=ROOT,
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))
    return bad == 0


if __name__ == '__main__':
    if sys.argv[1:2] == ['print']:
        for k in ORDER:
            for i in sorted(H.get(k, {})):
                print('%s.%d %s' % (k, i, H[k][i]))
            print(k, S[k])
    elif sys.argv[1:2] == ['check']:
        check(sys.argv[2:] or ORDER)
