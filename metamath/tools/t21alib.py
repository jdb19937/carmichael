"""Sortie T21a: T21.lean 94-1269 (zero sets, L-gamma, fold, levels, sigma grid,
geometric sums, harmonic sum, zones I-IV at T = X^3).  Frozen statements `S`
(T21b reads them), objects, helpers.  Built on tools/zc1lib.py.

    python3 tools/t21alib.py print               # the frozen table
    MM_DB=sorties/t21a.mm python3 tools/t21alib.py check [LABEL...]   # grammar check
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from zc1lib import *
import zc1lib as _zc1


def stmt(label):
    for fn in ('sorties/t21a.mm', 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


# ---- objects (letters: x characters, q zeros, r the ZF binder, t s density quantifiers) ----
DB = '( Base ` ( DChr ` N ) )'
EX = '( N DChrLF x )'


def ZFX(a, t, e=EX):
    return ZF(e, a, t)


def ORD(e=EX, q='q'):
    return '( %s holord %s )' % (e, q)


def WT(e=EX, q='q'):
    return '( %s / ( 1 + ( abs ` ( Im ` %s ) ) ) )' % (ORD(e, q), q)


def NC(a, t, n='N'):
    """sum over the characters mod n of zeroCountBox at abscissa a, height t"""
    e = '( %s DChrLF x )' % n
    return "sum_ x e. ( Base ` ( DChr ` %s ) ) sum_ q e. %s %s" % (n, ZF(e, a, t), ORD(e))


def WS(a, t):
    """sum over characters of sum over zeros of ord / ( 1 + |Im| )"""
    return 'sum_ x e. %s sum_ q e. %s %s' % (DB, ZFX(a, t), WT())


def YR(y):
    return '( %s ^c ( Re ` q ) )' % y


def ZT(t, y, c):
    """zeroSumTotal at abscissa c (zone IV at c = tau; the full sum at c = 1/2)"""
    return 'sum_ x e. %s sum_ q e. %s ( %s x. %s )' % (DB, ZFX(c, t), WT(), YR(y))


def ZS(t, y, a, b):
    """zoneSum: the zeros with a <_ Re < b"""
    return 'sum_ x e. %s sum_ q e. ( %s \\ %s ) ( %s x. %s )' % (DB, ZFX(a, t), ZFX(b, t), WT(), YR(y))


HALF = '( 1 / 2 )'
F3950 = '( ; 3 9 / ; 5 0 )'
F910 = '( 9 / ; 1 0 )'
F92 = '( 9 / 2 )'
F191 = '( ; ; 1 9 1 / ; ; 9 0 0 )'
F709 = '( ; ; 7 0 9 / ; ; 9 0 0 )'
F7900 = '( 7 / ; ; 9 0 0 )'
F9200 = '( 9 / ; ; 2 0 0 )'
X3 = '( X ^ 3 )'
LX = '( log ` X )'
TAU = '( 1 - ( R / %s ) )' % LX
SSTAR = '( 1 - ( ( ; 5 0 x. ( ( K + 2 ) x. ( log ` %s ) ) ) / %s ) )' % (LX, LX)

# the two density interfaces (DensityInterface.lean), per modulus N (the body of the A. n)
def ZFo(a, t, n='N', y='y', o='o'):
    """ZF with characters y and binder o (the letters of hypotheses that sit in antecedents)"""
    return '{ %s e. %s | ( %s =/= 1 /\\ ( ( %s DChrLF %s ) ` %s ) = 0 ) }' % (o, BOX(a, t), o, n, y, o)


def NCo(a, t, n='N'):
    """NC in the hypothesis letters: characters y, zeros p, binder o"""
    e = '( %s DChrLF y )' % n
    return 'sum_ y e. ( Base ` ( DChr ` %s ) ) sum_ p e. %s ( %s holord p )' % (n, ZFo(a, t, n), e)


# Density hypotheses sit in antecedents of theorems whose proofs sum over x, q, k and bind
# t, r: they use the letters v (height), u (abscissa), y (characters), p (zeros), o (binder).
def LFD_BODY(g, c, n='N'):
    return 'A. v e. RR A. u e. RR ( ( 2 <_ v /\\ %s <_ u /\\ u <_ 1 ) -> %s <_ ( %s x. ( ( %s x. ( v ^c %s ) ) ^c ( %s x. ( 1 - u ) ) ) ) )' % (F910, NCo('u', 'v', n), g, n, c, F92)


def LGD_BODY(h, p, c, k, n='N'):
    return 'A. v e. RR A. u e. RR ( ( 2 <_ v /\\ %s <_ u /\\ u <_ 1 ) -> %s <_ ( ( %s x. ( ( %s x. ( v ^c %s ) ) ^c ( %s x. ( 1 - u ) ) ) ) x. ( ( log ` ( %s x. ( v + 2 ) ) ) ^ %s ) ) )' % (F3950, NCo('u', 'v', n), h, n, c, p, n, k)


LEVEL = '( N <_ ( X ^c %s ) /\\ ( N x. ( X ^c %s ) ) <_ Y )' % (F191, F709)
XE = '( X e. RR /\\ ( exp ` 1 ) <_ X )'

S = {}

# ---- zero sets ----
S['t21zfel'] = '( ( A e. RR /\\ T e. RR ) -> ( Q e. %s <-> ( Q e. CC /\\ ( ( A <_ ( Re ` Q ) /\\ ( Re ` Q ) <_ 1 ) /\\ ( abs ` ( Im ` Q ) ) <_ T ) /\\ ( Q =/= 1 /\\ ( F ` Q ) = 0 ) ) ) )' % ZF('F', 'A', 'T')
S['t21zfss'] = '( ( ( A e. RR /\\ B e. RR /\\ A <_ B ) /\\ ( U e. RR /\\ T e. RR /\\ U <_ T ) ) -> %s C_ %s )' % (ZF('F', 'B', 'U'), ZF('F', 'A', 'T'))

S['t21zfd'] = '( ( ( A e. RR /\\ B e. RR /\\ T e. RR ) /\\ Q e. ( %s \\ %s ) ) -> ( Q e. %s /\\ ( Re ` Q ) < B ) )' % (ZF('F', 'A', 'T'), ZF('F', 'B', 'T'), ZF('F', 'A', 'T'))

# ---- L-gamma ----
FLT = '( 1 ... ( |_ ` T ) )'
S['t21lgr'] = '( ( ( T e. RR /\\ 1 <_ T ) /\\ ( G e. RR /\\ 0 <_ G /\\ G <_ T ) ) -> ( 1 / ( 1 + G ) ) <_ ( ( 1 / T ) + sum_ n e. %s if ( G <_ n , ( 1 / ( n x. ( n + 1 ) ) ) , 0 ) ) )' % FLT
S['t21lgs'] = '( ( N e. NN /\\ ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ ( T e. RR /\\ 1 <_ T ) ) -> %s <_ ( ( %s / T ) + sum_ n e. %s ( %s / ( n x. ( n + 1 ) ) ) ) )' % (WS('A', 'T'), NC('A', 'T'), FLT, NC('A', 'n'))

# ---- fold ----
S['t21zs'] = '( ( U e. RR+ /\\ M e. ZZ ) -> sum_ n e. ( 1 ... M ) ( n ^c -u ( 1 + U ) ) <_ ( 1 + ( 1 / U ) ) )'
FOLDHYP = 'A. t e. RR ( ( 2 <_ t /\\ t <_ T ) -> %s <_ ( ( C x. ( ( N x. ( t ^c P ) ) ^c W ) ) x. L ) )' % NC('A', 't')
S['t21fold'] = ('( ( ( N e. NN /\\ ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ ( T e. RR /\\ 2 <_ T ) ) /\\ ( ( C e. RR /\\ 0 <_ C ) /\\ ( L e. RR /\\ 0 <_ L ) /\\ ( P e. RR /\\ W e. RR /\\ 0 <_ W ) ) /\\ ( ( U e. RR+ /\\ U <_ 1 /\\ ( P x. W ) <_ ( 1 - U ) ) /\\ %s ) ) -> %s <_ ( ( ( C x. ( N ^c W ) ) x. L ) x. ( 2 + ( 1 / U ) ) ) )'
                % (FOLDHYP, WS('A', 'T')))

# ---- levels ----
S['t21dpow'] = '( ( ( ( X e. RR /\\ 1 <_ X ) /\\ ( D e. RR /\\ 1 <_ D /\\ D <_ ( X ^c U ) ) ) /\\ ( ( U e. RR /\\ V e. RR /\\ Y e. RR ) /\\ ( D x. ( X ^c V ) ) <_ Y ) /\\ ( A e. RR /\\ B e. RR /\\ ( 0 <_ B /\\ B <_ A ) ) ) -> ( D ^c A ) <_ ( ( X ^c ( ( U x. ( A - B ) ) - ( V x. B ) ) ) x. ( Y ^c B ) ) )'
S['t21ld'] = '( ( ( X e. RR /\\ 2 <_ X ) /\\ ( D e. RR /\\ 1 <_ D /\\ D <_ ( X ^c %s ) ) ) -> ( log ` ( D x. ( ( X ^ 3 ) + 2 ) ) ) <_ ( 5 x. ( log ` X ) ) )' % F191
S['t21d92'] = '( ( ( X e. RR /\\ 1 <_ X ) /\\ ( D e. RR /\\ 1 <_ D /\\ D <_ ( X ^c %s ) ) /\\ ( Y e. RR /\\ ( D x. ( X ^c %s ) ) <_ Y ) ) -> ( D ^c %s ) <_ ( ( X ^c -u %s ) x. Y ) )' % (F191, F709, F92, F9200)

# ---- sigma grid ----
GRIDS = 'sum_ k e. ( 0 ..^ M ) if ( ( S + ( k x. H ) ) <_ B , ( V x. ( Y ^c ( S + ( ( k + 1 ) x. H ) ) ) ) , 0 )'
S['t21gridr'] = ('( ( ( Y e. RR /\\ 1 <_ Y ) /\\ ( H e. RR+ /\\ M e. NN0 ) /\\ ( ( S e. RR /\\ B e. RR /\\ U e. RR ) /\\ ( ( S <_ B /\\ B < U ) /\\ U <_ ( S + ( M x. H ) ) ) /\\ ( V e. RR /\\ 0 <_ V ) ) ) -> ( V x. ( Y ^c B ) ) <_ %s )' % GRIDS)
GRIDH = {
    1: '( ph -> I e. Fin )',
    2: '( ( ph /\\ x e. I ) -> A e. Fin )',
    3: '( ( ( ph /\\ x e. I ) /\\ q e. A ) -> ( ( q e. CC /\\ ( V e. RR /\\ 0 <_ V ) ) /\\ ( S <_ ( Re ` q ) /\\ ( Re ` q ) < U ) ) )',
    4: '( ( ( ph /\\ x e. I ) /\\ k e. ( 0 ..^ M ) ) -> ( C e. Fin /\\ A. q e. C ( V e. RR /\\ 0 <_ V ) /\\ A. q e. A ( ( S + ( k x. H ) ) <_ ( Re ` q ) -> q e. C ) ) )',
    5: '( ph -> ( ( Y e. RR /\\ 1 <_ Y ) /\\ ( H e. RR+ /\\ M e. NN0 ) /\\ ( ( S e. RR /\\ U e. RR ) /\\ U <_ ( S + ( M x. H ) ) ) ) )',
    6: '( ( ph /\\ k e. ( 0 ..^ M ) ) -> ( D e. RR /\\ sum_ x e. I sum_ q e. C V <_ D ) )',
}
S['t21grid'] = '( ph -> sum_ x e. I sum_ q e. A ( V x. ( Y ^c ( Re ` q ) ) ) <_ sum_ k e. ( 0 ..^ M ) ( ( Y ^c ( S + ( ( k + 1 ) x. H ) ) ) x. D ) )'
S['t21e9'] = '( exp ` -u %s ) <_ ( ; ; 2 0 0 / ; ; 2 0 9 )' % F9200
LH = '( 1 / %s )' % LX
MG = '( ( |_ ` ( ( T - S ) x. %s ) ) + 1 )' % LX
RR9 = '( exp ` -u %s )' % F9200
EXPT = '( X ^c ( -u %s x. ( 1 - T ) ) )' % F9200
SGK = '( S + ( K x. %s ) )' % LH
S['t21gterm'] = ('( ( ( %s /\\ ( Y e. RR /\\ 1 <_ Y /\\ Y <_ X ) ) /\\ ( ( D e. RR /\\ 1 <_ D ) /\\ ( D ^c %s ) <_ ( ( X ^c -u %s ) x. Y ) ) /\\ ( ( S e. RR /\\ T e. RR /\\ T <_ 1 ) /\\ ( J e. NN0 /\\ K e. RR ) /\\ ( %s <_ T /\\ ( J + K ) <_ ( ( T - S ) x. %s ) ) ) ) -> ( ( Y ^c ( S + ( ( K + 1 ) x. %s ) ) ) x. ( D ^c ( %s x. ( 1 - %s ) ) ) ) <_ ( ( ( exp ` 1 ) x. Y ) x. ( %s x. ( %s ^ J ) ) ) )'
                 % (XE, F92, F9200, SGK, LX, LH, F92, SGK, EXPT, RR9))
S['t21geo'] = '( ( ( R e. RR /\\ 0 <_ R /\\ R < 1 ) /\\ N e. NN0 ) -> sum_ k e. ( 0 ..^ ( N + 1 ) ) ( R ^ ( N - k ) ) <_ ( 1 / ( 1 - R ) ) )'
S['t21ggeo'] = ('( ( ( %s /\\ ( Y e. RR /\\ 1 <_ Y /\\ Y <_ X ) ) /\\ ( ( D e. RR /\\ 1 <_ D ) /\\ ( D ^c %s ) <_ ( ( X ^c -u %s ) x. Y ) ) /\\ ( ( S e. RR /\\ T e. RR ) /\\ ( S <_ T /\\ T <_ 1 ) ) ) -> sum_ k e. ( 0 ..^ %s ) ( ( Y ^c ( S + ( ( k + 1 ) x. %s ) ) ) x. ( D ^c ( %s x. ( 1 - ( S + ( k x. %s ) ) ) ) ) ) <_ ( ( ; 6 4 x. Y ) x. ( X ^c ( -u %s x. ( 1 - T ) ) ) ) )'
                % (XE, F92, F9200, MG, LH, F92, LH, F9200))
SK = '( S + ( k x. %s ) )' % LH
GZH = {
    1: '( ph -> ( ( N e. NN /\\ %s /\\ ( Y e. RR /\\ %s /\\ Y <_ X ) ) /\\ ( ( S e. RR /\\ T e. RR ) /\\ ( %s <_ S /\\ S <_ T /\\ T <_ 1 ) ) /\\ ( Q e. RR /\\ 0 <_ Q ) ) )' % (XE, LEVEL, HALF),
    2: '( ( ph /\\ ( k e. NN0 /\\ %s <_ T ) ) -> %s <_ ( Q x. ( N ^c ( %s x. ( 1 - %s ) ) ) ) )' % (SK, WS(SK, X3), F92, SK),
}
S['t21gz'] = '( ph -> %s <_ ( Q x. ( ( ; 6 4 x. Y ) x. ( X ^c ( -u %s x. ( 1 - T ) ) ) ) ) )' % (ZS(X3, 'Y', 'S', 'T'), F9200)

# ---- harmonic sum ----
S['t21harm'] = '( ( T e. RR /\\ 1 <_ T ) -> sum_ n e. %s ( 1 / ( n + 1 ) ) <_ ( log ` ( ( |_ ` T ) + 1 ) ) )' % FLT

# ---- zones ----
S['t21split'] = ('( ( ( N e. NN /\\ T e. RR /\\ Y e. RR+ ) /\\ ( ( A e. RR /\\ B e. RR /\\ C e. RR ) /\\ ( %s <_ A /\\ A <_ B ) /\\ ( B <_ C /\\ C <_ 1 ) ) ) -> %s = ( ( ( %s + %s ) + %s ) + %s ) )'
                 % (HALF, ZT('T', 'Y', HALF), ZS('T', 'Y', HALF, 'A'), ZS('T', 'Y', 'A', 'B'), ZS('T', 'Y', 'B', 'C'), ZT('T', 'Y', 'C')))
S['t21wsi'] = '( ( N e. NN /\\ %s /\\ N <_ ( X ^c %s ) ) -> %s <_ ( ; ; ; ; ; 1 6 0 0 0 0 x. ( N x. ( %s ^ 2 ) ) ) )' % (XE, F191, WS(HALF, X3), LX)
S['t21z1'] = ('( ( ( N e. NN /\\ %s /\\ ( Y e. RR /\\ E e. RR ) ) /\\ ( %s /\\ ( ; ; ; ; ; ; 4 3 2 0 0 0 0 x. ( %s ^ 2 ) ) <_ ( E x. ( X ^c %s ) ) ) ) -> %s <_ ( ( E x. Y ) / ; 2 7 ) )'
              % (XE, LEVEL, LX, F7900, ZS(X3, 'Y', HALF, F3950)))
S['t21z2'] = ('( ( ( ( N e. NN /\\ %s /\\ ( Y e. RR /\\ E e. RR ) ) /\\ ( %s /\\ Y <_ X ) ) /\\ ( ( ( H e. RR /\\ 1 <_ H ) /\\ ( P e. RR /\\ 0 <_ P /\\ P <_ ( 7 / 2 ) ) /\\ ( C e. RR /\\ 1 <_ C /\\ C <_ ( 5 / 4 ) ) ) /\\ ( K e. NN0 /\\ %s ) ) /\\ ( %s <_ %s /\\ ( ( ; ; ; ; 5 0 1 1 2 x. ( 5 ^ K ) ) x. H ) <_ ( E x. ( %s ^c %s ) ) ) ) -> %s <_ ( ( E x. Y ) / ; 2 7 ) )'
              % (XE, LEVEL, LGD_BODY('H', 'P', 'C', 'K'), F3950, SSTAR, LX, F92, ZS(X3, 'Y', F3950, SSTAR)))
S['t21z3'] = ('( ( ( ( N e. NN /\\ %s ) /\\ ( ( Y e. RR /\\ %s ) /\\ Y <_ X ) ) /\\ ( ( ( G e. RR /\\ 1 <_ G ) /\\ ( C e. RR /\\ 1 <_ C ) ) /\\ %s ) /\\ ( ( R e. RR+ /\\ S e. RR ) /\\ ( %s <_ S /\\ S <_ %s ) /\\ ( C x. ( %s x. ( 1 - S ) ) ) <_ %s ) ) -> %s <_ ( ( ( ; ; 2 5 6 x. G ) x. Y ) x. ( exp ` ( -u %s x. R ) ) ) )'
              % (XE, LEVEL, LFD_BODY('G', 'C'), F910, TAU, F92, HALF, ZS(X3, 'Y', 'S', TAU), F9200))
S['t21z4'] = ('( ( ( ( N e. NN /\\ %s ) /\\ ( N <_ ( X ^c %s ) /\\ ( Y e. RR /\\ 1 <_ Y ) ) ) /\\ ( ( ( G e. RR /\\ 1 <_ G ) /\\ ( C e. RR /\\ C <_ 2 ) ) /\\ %s ) /\\ ( ( R e. RR+ /\\ V e. RR+ /\\ ( ; 1 0 x. R ) <_ %s ) /\\ A. y e. %s A. p e. %s ( %s <_ ( Re ` p ) -> V < ( abs ` ( Im ` p ) ) ) ) ) -> %s <_ ( ( ( G x. ( exp ` ( ; 2 8 x. R ) ) ) x. Y ) / V ) )'
              % (XE, F191, LFD_BODY('G', 'C'), LX, DB, ZFo(HALF, X3), TAU, ZT(X3, 'Y', TAU)))

# Lean's LogFreeDensity / LoggedDensity as closed wffs (the full interface; also in tools/zdilib.py)
LOGFREE = 'E. g E. c ( ( g e. RR /\\ c e. RR ) /\\ ( 1 <_ g /\\ 1 <_ c /\\ c <_ 2 ) /\\ A. m e. NN %s )' % LFD_BODY('g', 'c', 'm')
LOGGED = 'E. h E. w E. c E. k ( ( ( h e. RR /\\ w e. RR /\\ c e. RR ) /\\ k e. NN0 ) /\\ ( ( 1 <_ h /\\ 0 <_ w /\\ w <_ ( 7 / 2 ) ) /\\ ( 1 <_ c /\\ c <_ ( 5 / 4 ) ) ) /\\ A. m e. NN %s )' % LGD_BODY('h', 'w', 'c', 'k', 'm')

LGH = {
    1: '( ph -> ( T e. RR /\\ 1 <_ T ) )',
    2: '( ph -> I e. Fin )',
    3: '( ( ph /\\ x e. I ) -> S e. Fin )',
    4: '( ( ( ph /\\ x e. I ) /\\ q e. S ) -> ( q e. CC /\\ ( W e. RR /\\ 0 <_ W ) /\\ ( abs ` ( Im ` q ) ) <_ T ) )',
    5: '( ( ( ph /\\ x e. I ) /\\ n e. %s ) -> ( Z C_ S /\\ A. q e. S ( ( abs ` ( Im ` q ) ) <_ n -> q e. Z ) ) )' % FLT,
}
S['t21lg'] = '( ph -> sum_ x e. I sum_ q e. S ( W / ( 1 + ( abs ` ( Im ` q ) ) ) ) <_ ( ( sum_ x e. I sum_ q e. S W / T ) + sum_ n e. %s ( sum_ x e. I sum_ q e. Z W / ( n x. ( n + 1 ) ) ) ) )' % FLT
F2T = '( 2 ... ( |_ ` T ) )'
FOLDRH = {
    1: '( ph -> ( T e. RR /\\ 2 <_ T ) )',
    2: '( ph -> ( B e. RR /\\ 0 <_ B ) )',
    3: '( ph -> ( U e. RR+ /\\ ( C e. RR /\\ C <_ ( 1 - U ) ) ) )',
    4: '( ph -> ( G e. RR /\\ G <_ ( B x. ( T ^c C ) ) ) )',
    5: '( ph -> ( H e. RR /\\ H <_ ( B x. ( 2 ^c C ) ) ) )',
    6: '( ( ph /\\ n e. %s ) -> ( K e. RR /\\ K <_ ( B x. ( n ^c C ) ) ) )' % F2T,
    7: '( n = 1 -> K = H )',
}
S['t21foldr'] = '( ph -> ( ( G / T ) + sum_ n e. %s ( K / ( n x. ( n + 1 ) ) ) ) <_ ( B x. ( 2 + ( 1 / U ) ) ) )' % FLT
GRIDLAB = {'t21grid': GRIDH, 't21lg': LGH, 't21foldr': FOLDRH, 't21gz': GZH}


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 't21agc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'gc%s.mmp' % lab)
        hy = GRIDLAB.get(lab, {})
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for i in sorted(hy):
                f.write('h%d::gc%s.%d |- %s\n' % (i + 1, lab, i, hy[i]))
            f.write('h1::gc%s.99 |- %s\n' % (lab, S[lab]))
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


S['t21e272'] = '( exp ` 1 ) <_ ( ; 6 8 / ; 2 5 )'


# ---- step helpers --------------------------------------------------------------------
_IDX = None


def thm(lab):
    """the assertion text of LAB (set.mm, carmichael.mm, sorties/t21a.mm), without |-"""
    global _IDX
    if _IDX is None:
        _IDX = {}
        for fn in ('assertions-carmichael.idx', 'assertions-t21a.idx'):
            pth = os.path.join(HERE, '..', 'scratch', fn)
            if os.path.exists(pth):
                for l in open(pth):
                    a = l.rstrip('\n').split(' ', 2)
                    if len(a) == 3:
                        _IDX[a[0]] = a[2]
    if lab not in _IDX:
        return stmt(lab) and '|- ' + stmt(lab)
    return _IDX[lab]


def _conj_tree(text):
    """parse a wff into its /\\ tree: ('and', [kids]) or ('leaf', text)"""
    from cl import split_top
    toks = text.split()
    if toks[0] == '(' and toks[-1] == ')':
        inner = toks[1:-1]
        depth = 0; cut = []
        for i, t in enumerate(inner):
            if t in ('(', '{', '<.', '<"'):
                depth += 1
            elif t in (')', '}', '>.', '">'):
                depth -= 1
            elif t == '/\\' and depth == 0:
                cut.append(i)
        if cut and len(cut) in (1, 2):
            parts = []; prev = 0
            for c_ in cut:
                parts.append(' '.join(inner[prev:c_])); prev = c_ + 1
            parts.append(' '.join(inner[prev:]))
            return ('and', [_conj_tree(p_) for p_ in parts])
    return ('leaf', text)


def ap(w, ante, hyps, lab, f):
    """apply LAB to hyps (steps proving ( ante -> leaf_i )) giving ( ante -> f ).
    Deduction-form labels ( '( ph ->' ) are cited directly; closed ones get the
    antecedent tree rebuilt with jca/3jca and syl."""
    t = thm(lab).replace('|- ', '', 1)
    if t.startswith('( ph -> '):
        return w.s(hyps, lab, '( %s -> %s )' % (ante, f))
    if not hyps:
        c = w.s([], lab, f)
        return w.s([c], 'a1i', '( %s -> %s )' % (ante, f))
    from cl import split_imp
    a, _ = split_imp(t)
    tree = _conj_tree(a)
    it = iter(hyps)
    from cl import formula_of

    def build(node):
        if node[0] == 'leaf':
            return next(it)
        kids = [build(k) for k in node[1]]
        fs = [formula_of(w, k) for k in kids]
        bodies = [x_.split(' -> ', 1)[1][:-2] if x_.startswith('( %s -> ' % ante) else None for x_ in fs]
        bodies = [strip_ante(x_, ante) for x_ in fs]
        return w.s(kids, 'jca' if len(kids) == 2 else '3jca', '( %s -> ( %s ) )' % (ante, (' /\\ '.join(bodies))))
    top = build(tree)
    i = w.inst(lab)
    return w.s([top, i], 'syl', '( %s -> %s )' % (ante, f))


def strip_ante(formula, ante):
    from cl import strip_ante as _sa
    return _sa(formula, ante)


def unpack(w, ante, root=None, out=None):
    """steps ( ante -> leaf ) for every leaf of ante's /\\ tree (dict text -> step)"""
    if out is None:
        out = {}
    if root is None:
        root = w.s([], 'id', '( %s -> %s )' % (ante, ante))
        node_text = ante
    else:
        node_text = None
    def walk(text, step):
        tr = _conj_tree(text)
        if tr[0] == 'leaf':
            out.setdefault(text, step); return
        kids = [k[1] if k[0] == 'leaf' else _flat(k) for k in tr[1]]
        refs = ['simpld', 'simprd'] if len(kids) == 2 else ['simp1d', 'simp2d', 'simp3d']
        for k, r in zip(kids, refs):
            walk(k, w.s([step], r, '( %s -> %s )' % (ante, k)))
    walk(ante, root)
    return out



def unpack_step(w, ante, step, text, out=None):
    """leaves of the /\\ tree of TEXT, given step : ( ante -> TEXT )"""
    if out is None:
        out = {}
    tr = _conj_tree(text)
    if tr[0] == 'leaf':
        out.setdefault(text, step); return out
    kids = [k[1] if k[0] == 'leaf' else _flat(k) for k in tr[1]]
    refs = ['simpld', 'simprd'] if len(kids) == 2 else ['simp1d', 'simp2d', 'simp3d']
    for k, r in zip(kids, refs):
        unpack_step(w, ante, w.s([step], r, '( %s -> %s )' % (ante, k)), k, out)
    return out

def _flat(node):
    if node[0] == 'leaf':
        return node[1]
    return '( ' + ' /\\ '.join(_flat(k) for k in node[1]) + ' )'


def ifnn(w, ante, cond, a, a_rr, a_ge0):
    """( ante -> if ( cond , a , 0 ) e. RR ), ( ante -> 0 <_ if ( cond , a , 0 ) )"""
    E = 'if ( %s , %s , 0 )' % (cond, a)
    bi = w.s([], 'elrege0', '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (a, a, a))
    am = w.s([w.s([a_rr, a_ge0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ante, a, a)), bi], 'sylibr', '( %s -> %s e. ( 0 [,) +oo ) )' % (ante, a))
    zm = w.s([w.s([], '0e0icopnf', '0 e. ( 0 [,) +oo )')], 'a1i', '( %s -> 0 e. ( 0 [,) +oo ) )' % ante)
    em = w.s([am, zm], 'ifcld', '( %s -> %s e. ( 0 [,) +oo ) )' % (ante, E))
    bi2 = w.s([], 'elrege0', '( %s e. ( 0 [,) +oo ) <-> ( %s e. RR /\\ 0 <_ %s ) )' % (E, E, E))
    both = w.s([em, bi2], 'sylib', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ante, E, E))
    return w.s([both], 'simpld', '( %s -> %s e. RR )' % (ante, E)), w.s([both], 'simprd', '( %s -> 0 <_ %s )' % (ante, E))


def run(w):
    """check every cited label exists (set.mm, carmichael.mm, the sortie), then add"""
    thm('ax-mp')
    missing = set()
    for l in w.lines:
        head = l.split('|-')[0] if '|-' in l else l
        parts = head.split(':')
        if len(parts) >= 3:
            ref = parts[2].strip()
            if ref and ref not in _IDX and not ref.startswith(w.label) and ref not in ('idi',):
                try:
                    stmt(ref)
                except KeyError:
                    missing.add(ref)
    if missing:
        print('MISSING LABELS', w.label, sorted(missing))
        return False
    return w.run()


def zf_eq(w, t, V, a='A', e=EX):
    """closed step ( t = V -> ZF(a,t) = ZF(a,V) ) (t a setvar)"""
    H = '%s = %s' % (t, V)
    s1 = w.s([], 'negeq', '( %s -> -u %s = -u %s )' % (H, t, V))
    s2 = w.s([s1], 'oveq2d', '( %s -> ( _i x. -u %s ) = ( _i x. -u %s ) )' % (H, t, V))
    s3 = w.s([s2], 'oveq2d', '( %s -> ( %s + ( _i x. -u %s ) ) = ( %s + ( _i x. -u %s ) ) )' % (H, a, t, a, V))
    s4 = w.s([], 'oveq2', '( %s -> ( _i x. %s ) = ( _i x. %s ) )' % (H, t, V))
    s5 = w.s([s4], 'oveq2d', '( %s -> ( 1 + ( _i x. %s ) ) = ( 1 + ( _i x. %s ) ) )' % (H, t, V))
    s6 = w.s([s3, s5], 'oveq12d', '( %s -> %s = %s )' % (H, BOX(a, t), BOX(a, V)))
    return w.s([s6], 'rabeqdv', '( %s -> %s = %s )' % (H, ZF(e, a, t), ZF(e, a, V)))


def nc_eq(w, t, V, a='A'):
    """closed step ( t = V -> NC(a,t) = NC(a,V) )"""
    H = '%s = %s' % (t, V)
    z = zf_eq(w, t, V, a)
    i = w.s([z], 'sumeq1d', '( %s -> sum_ q e. %s %s = sum_ q e. %s %s )' % (H, ZFX(a, t), ORD(), ZFX(a, V), ORD()))
    return w.s([i], 'sumeq2sdv', '( %s -> %s = %s )' % (H, NC(a, t), NC(a, V)))


def nc_real(w, A_, nn, ar, a0, a1, tr, a='A', t='T'):
    """( A_ -> NC(a,t) e. RR ) and the per-character context facts"""
    from cl import lift
    C1 = '( %s /\\ x e. %s )' % (A_, DB)
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (C1, DB))
    Z = ZFX(a, t)
    ez = ap(w, C1, [lift(w, nn, C1), xin, lift(w, ar, C1), lift(w, a0, C1), lift(w, a1, C1), lift(w, tr, C1)], 'ezf', '( %s e. Fin /\\ A. q e. %s %s e. NN )' % (Z, Z, ORD()))
    zfin = w.s([ez], 'simpld', '( %s -> %s e. Fin )' % (C1, Z))
    C2 = '( %s /\\ q e. %s )' % (C1, Z)
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, Z))
    ordn = w.s([lift(w, w.s([ez], 'simprd', '( %s -> A. q e. %s %s e. NN )' % (C1, Z, ORD())), C2), qin,
                w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (Z, ORD(), Z, ORD()))], 'sylc', '( %s -> %s e. NN )' % (C2, ORD()))
    orr = w.s([ordn], 'nnred', '( %s -> %s e. RR )' % (C2, ORD()))
    or0 = w.s([w.s([ordn], 'nnnn0d', '( %s -> %s e. NN0 )' % (C2, ORD()))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (C2, ORD()))
    inner = w.s([zfin, orr], 'fsumrecl', '( %s -> sum_ q e. %s %s e. RR )' % (C1, Z, ORD()))
    g = w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'); b = w.s([], 'eqid', '%s = %s' % (DB, DB))
    dfin = w.s([nn, w.s([g, b], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB)], 'syl', '( %s -> %s e. Fin )' % (A_, DB))
    tot = w.s([dfin, inner], 'fsumrecl', '( %s -> %s e. RR )' % (A_, NC(a, t)))
    return tot, dict(C1=C1, C2=C2, zfin=zfin, orr=orr, or0=or0, inner=inner, dfin=dfin)


def q_facts(w, C2, qin, ar, tr, a='A', t='T', e=EX):
    """from qin : ( C2 -> q e. ZF(a,t) ): steps for q e. CC, a <_ Re q, Re q <_ 1, abs Im q <_ t, Re q e. RR"""
    Z = ZF(e, a, t)
    CND = '( q e. CC /\\ ( ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ %s ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (a, t, e)
    el = ap(w, C2, [ar, tr], 't21zfel', '( q e. %s <-> %s )' % (Z, CND))
    c = w.s([qin, el], 'mpbid', '( %s -> %s )' % (C2, CND))
    qc = w.s([c], 'simp1d', '( %s -> q e. CC )' % C2)
    m = w.s([c], 'simp2d', '( %s -> ( ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ %s ) )' % (C2, a, t))
    rr = w.s([m], 'simpld', '( %s -> ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) )' % (C2, a))
    return dict(qc=qc, lo=w.s([rr], 'simpld', '( %s -> %s <_ ( Re ` q ) )' % (C2, a)), hi=w.s([rr], 'simprd', '( %s -> ( Re ` q ) <_ 1 )' % C2),
                im=w.s([m], 'simprd', '( %s -> ( abs ` ( Im ` q ) ) <_ %s )' % (C2, t)), re=w.s([qc], 'recld', '( %s -> ( Re ` q ) e. RR )' % C2),
                imr=w.s([w.s([w.s([qc], 'imcld', '( %s -> ( Im ` q ) e. RR )' % C2)], 'recnd', '( %s -> ( Im ` q ) e. CC )' % C2)], 'abscld', '( %s -> ( abs ` ( Im ` q ) ) e. RR )' % C2),
                im0=w.s([w.s([w.s([qc], 'imcld', '( %s -> ( Im ` q ) e. RR )' % C2)], 'recnd', '( %s -> ( Im ` q ) e. CC )' % C2)], 'absge0d', '( %s -> 0 <_ ( abs ` ( Im ` q ) ) )' % C2))


def wt_facts(w, C2, orr, or0, qf):
    """( C2 -> WT e. RR ), ( C2 -> 0 <_ WT ), ( C2 -> ( 1 + abs Im q ) e. RR+ )"""
    import lin as _lin
    G = '( abs ` ( Im ` q ) )'; g1 = '( 1 + %s )' % G
    g1r = w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % C2), qf['imr']], 'readdcld', '( %s -> %s e. RR )' % (C2, g1))
    g1p = w.s([g1r, _lin.linarith(w, C2, [qf['im0']], '0 < %s' % g1, leaves={G: qf['imr']})], 'elrpd', '( %s -> %s e. RR+ )' % (C2, g1))
    return (w.s([orr, g1p], 'rerpdivcld', '( %s -> %s e. RR )' % (C2, WT())), w.s([orr, g1p, or0], 'divge0d', '( %s -> 0 <_ %s )' % (C2, WT())), g1p)


def ws_real(w, A_, nn, ar, a0, a1, tr, a='A', t='T'):
    from cl import lift
    tot, inf = nc_real(w, A_, nn, ar, a0, a1, tr, a, t)
    C1, C2 = inf['C1'], inf['C2']
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C2, ZFX(a, t)))
    qf = q_facts(w, C2, qin, lift(w, ar, C2), lift(w, tr, C2), a, t)
    wr, w0, _ = wt_facts(w, C2, inf['orr'], inf['or0'], qf)
    inner = w.s([inf['zfin'], wr], 'fsumrecl', '( %s -> sum_ q e. %s %s e. RR )' % (C1, ZFX(a, t), WT()))
    return w.s([inf['dfin'], inner], 'fsumrecl', '( %s -> %s e. RR )' % (A_, WS(a, t)))


def zs_real(w, A_, nn, ar, a0, a1, tr, yr, y0, a, b, t, Y='Y'):
    """( A_ -> ZS(t, Y, a, b) e. RR ) (a is the lower abscissa: 0 < a <_ 1)"""
    from cl import lift
    tot, inf = nc_real(w, A_, nn, ar, a0, a1, tr, a, t)
    C1 = inf['C1']
    Za, Zb = ZFX(a, t), ZFX(b, t)
    D = '( %s \\ %s )' % (Za, Zb)
    dfin = ap(w, C1, [inf['zfin']], 'diffi', '%s e. Fin' % D)
    C3 = '( %s /\\ q e. %s )' % (C1, D)
    qa = ap(w, C3, [w.s([], 'simpr', '( %s -> q e. %s )' % (C3, D))], 'eldifi', 'q e. %s' % Za)
    m = w.s([w.s([], 'simpl', '( %s -> %s )' % (C3, C1)), qa], 'jca', '( %s -> %s )' % (C3, inf['C2']))
    via = lambda s_, f: w.s([m, s_], 'syl', '( %s -> %s )' % (C3, f))
    qf = q_facts(w, C3, qa, lift(w, ar, C3), lift(w, tr, C3), a, t)
    wr, _, _ = wt_facts(w, C3, via(inf['orr'], '%s e. RR' % ORD()), via(inf['or0'], '0 <_ %s' % ORD()), qf)
    yre = w.s([lift(w, yr, C3), lift(w, y0, C3), qf['re']], 'recxpcld', '( %s -> ( %s ^c ( Re ` q ) ) e. RR )' % (C3, Y))
    body = w.s([wr, yre], 'remulcld', '( %s -> ( %s x. ( %s ^c ( Re ` q ) ) ) e. RR )' % (C3, WT(), Y))
    inner = w.s([dfin, body], 'fsumrecl', '( %s -> sum_ q e. %s ( %s x. ( %s ^c ( Re ` q ) ) ) e. RR )' % (C1, D, WT(), Y))
    return w.s([inf['dfin'], inner], 'fsumrecl', '( %s -> %s e. RR )' % (A_, ZS(t, Y, a, b)))

if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in S:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check(sys.argv[2:] or list(S))
