"""Sortie EF4: helpers and the frozen statements (ExplicitFormula 4133-5662: conjugation, horizontal and right
edges, exists_cuts, band mass, contour_ne_one, explicit_formula_ne_one).  Built on tools/ef3lib.py and tools/ef1lib.py.

    python3 tools/ef4lib.py print                                   # the frozen table
    MM_DB=sorties/ef4.mm python3 tools/ef4lib.py check [LABEL...]   # grammar check (mmatch)

Letters: CJ's mapping binder e; heights U (bottom, -u U) and V (top); abscissa S; the chain has K cuts G;
the left-edge windows are M with offset -u U; zeros q, filters p, r (ZS, ZF, BZ); j windows/cuts;
LFN binds s k i, LDI binds u v, DD binds t x w, PS/PSI bind n z, RHF binds z k.
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from ef3lib import *
import ef3lib as _ef3
import ef2lib as _ef2
import zc1lib as _zc1
import c10lib as _c10
import ef1lib as _ef1


def stmt(label):
    """the assertion of LABEL from sorties/ef4.mm or carmichael.mm, without |-"""
    for fn in ('sorties/ef4.mm', 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def patch(*mods):
    for m in mods:
        m.stmt = stmt


patch(_ef3, _ef2, _c10, _zc1)

# ---- objects -----------------------------------------------------------------------
CJ = lambda F='F': '( e e. %s |-> ( * ` ( %s ` ( * ` e ) ) ) )' % (HP0, F)      # Lean conjF on HP0
C1 = _ef1.C0                                    # c = 1 + 1 / log Y
PS1 = _ef1.PS(C1)                               # 2 pi i perronSum at c
PSC = _ef1.PS                                   # PS(C)
PSI = _ef1.PSI
LO, HI = _ef1.LO, _ef1.HI
YT = _ef1.YT
LDL = LDI(LFN)                                  # the strip integrand of L
LN4 = '( log ` ( N x. ( T + 4 ) ) )'           # LT4 at A = N
LNT = '( log ` ( N x. ( T + 2 ) ) )'
LNY = '( log ` ( ( N x. T ) x. Y ) )'
P1 = '( ( Y x. ( %s ^ 2 ) ) / T )' % LNY
P2 = '( ( Y ^c ( 5 / 8 ) ) x. ( %s ^ 2 ) )' % LNT
KC = '; ; ; ; ; ; ; ; 4 0 0 0 0 0 0 0 0'        # contour_ne_one 400000000 (Lean 100000000, 2 pi normalised)
KE = '; ; ; ; ; ; ; ; 5 0 0 0 0 0 0 0 0'        # explicit_formula_ne_one 500000000 (Lean 200000000)
KB = '; ; ; 1 6 0 0'                            # band_mass_le 1600 (Lean 224)
ZFE = ZF(E, '( 1 / 2 )', 'T')
SCE = 'sum_ q e. %s ( ( %s holord q ) x. ( ( Y ^c q ) / q ) )' % (ZFE, E)
RS1 = '( ( %s holord q ) x. ( ( Y ^c q ) / q ) )' % LFN
SRL = 'sum_ q e. %s %s' % (ZR('S', C1, '-u U', 'V', LFN), RS1)
PTL = lambda x, t: '( %s + ( _i x. %s ) )' % (x, t)
BOT = '( %s lint <. %s , %s >. )' % (LDL, PTL('S', '-u U'), PTL(C1, '-u U'))
TOP = '( %s lint <. %s , %s >. )' % (LDL, PTL('S', 'V'), PTL(C1, 'V'))
EB = '( %s lint <. %s , %s >. )' % (LDL, PTL(C1, '-u U'), PTL(C1, '-u T'))
ET = '( %s lint <. %s , %s >. )' % (LDL, PTL(C1, 'T'), PTL(C1, 'V'))
LEFT = '( %s lint <. %s , %s >. )' % (LDL, PTL('S', '-u U'), PTL('S', 'V'))
BZ4 = BZ(LFN, '( T + 4 )')
CHN = lambda j: '( G ` %s )' % j


def LD(pt, F='F'):
    return '( ( ( CC _D %s ) ` %s ) / ( %s ` %s ) )' % (F, pt, F, pt)


def GOOD(pt, F='F', L=LT4):
    """F ( pt ) =/= 0 and abs ( F' / F ) ( pt ) <_ KGH L ^ 2"""
    return '( ( %s ` %s ) =/= 0 /\\ ( abs ` %s ) <_ ( %s x. ( %s ^ 2 ) ) )' % (F, pt, LD(pt, F), KGH, L)


# ---- frozen statements ---------------------------------------------------------------
S = {}
# conjugation
S['ef4cjd'] = ('( ( ( F : %s --> CC /\\ W e. %s ) /\\ ( * ` W ) e. dom ( CC _D F ) ) -> '
               'W ( CC _D %s ) ( * ` ( ( CC _D F ) ` ( * ` W ) ) ) )') % (HP0, HP0, CJ())
S['ef4cjh'] = '( %s -> ( %s /\\ A. b e. %s ( ( CC _D %s ) ` b ) = ( * ` ( ( CC _D F ) ` ( * ` b ) ) ) ) )' % (
    HOLF('F', HP0), HOLF(CJ(), HP0), HP0, CJ())
S['ef4ddc'] = '( %s -> %s )' % (DD(), DD(CJ()))
SVB = '( v + ( _i x. -u u ) )'
S['ef4ghb'] = ('( ( ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) /\\ ( G e. Fin /\\ G C_ RR /\\ ( # ` G ) <_ ( ; 1 6 x. %s ) ) ) -> '
               'E. u e. ( T [,] ( T + 1 ) ) ( A. g e. G ( 1 / ( %s x. %s ) ) <_ ( abs ` ( u - g ) ) /\\ '
               'A. v e. ( ( 1 / 2 ) [,] 3 ) %s ) )') % (DD(), LT4, GAP, LT4, GOOD(SVB))
# edges
PX = PTL('x', 'S')
S['ef4hz'] = ('( ( ( G e. ( D -cn-> CC ) /\\ ( Y e. RR+ /\\ Y =/= 1 ) ) /\\ ( ( P e. RR /\\ Q e. RR /\\ P <_ Q ) /\\ ( S e. RR /\\ B e. RR ) ) /\\ '
              'A. x e. ( P [,] Q ) ( %s e. D /\\ ( abs ` ( G ` %s ) ) <_ ( B x. ( Y ^c x ) ) ) ) -> '
              '( abs ` ( G lint <. %s , %s >. ) ) <_ ( B x. ( ( ( Y ^c Q ) - ( Y ^c P ) ) / ( log ` Y ) ) ) )') % (
    PX, PX, PTL('P', 'S'), PTL('Q', 'S'))
PC = PTL('C', 't')
S['ef4vz'] = ('( ( ( G e. ( D -cn-> CC ) /\\ C e. RR ) /\\ ( ( U e. RR /\\ V e. RR /\\ U <_ V ) /\\ B e. RR ) /\\ '
              'A. t e. ( U [,] V ) ( %s e. D /\\ ( abs ` ( G ` %s ) ) <_ B ) ) -> '
              '( abs ` ( G lint <. %s , %s >. ) ) <_ ( B x. ( V - U ) ) )') % (PC, PC, PTL('C', 'U'), PTL('C', 'V'))
PH = PTL('x', 'H')
S['ef4hed'] = ('( ( ( %s /\\ ( Y e. RR /\\ 1 < Y ) ) /\\ ( ( ( S e. RR /\\ C e. RR ) /\\ ( 0 < S /\\ S <_ C ) ) /\\ '
               '( ( T e. RR /\\ 0 < T ) /\\ ( H e. RR /\\ T <_ ( abs ` H ) ) /\\ K e. RR ) ) /\\ '
               'A. x e. ( S [,] C ) ( ( F ` %s ) =/= 0 /\\ ( abs ` %s ) <_ K ) ) -> '
               '( abs ` ( %s lint <. %s , %s >. ) ) <_ ( ( K / T ) x. ( ( Y ^c C ) / ( log ` Y ) ) ) )') % (
    HOLF('F', HP0), PH, LD(PH), LDI(), PTL('S', 'H'), PTL('C', 'H'))
S['ef4lfd'] = '( ( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) ) -> %s = -u %s )' % (CHI, LD('S', LFN), _ef1.DLV('S'))
S['ef4rm'] = ('( ( %s /\\ ( ( Y e. RR+ /\\ C e. RR /\\ 1 < C ) /\\ T e. RR ) ) -> ( %s lint <. %s , %s >. ) = -u %s )') % (
    CHI, LDL, LO('C', 'T'), HI('C', 'T'), PSC('C'))
S['ef4rx'] = ('( ( ( %s /\\ ( Y e. RR /\\ ; ; 1 0 0 <_ Y ) ) /\\ ( ( T e. RR /\\ 0 < T ) /\\ ( U e. RR /\\ V e. RR ) /\\ ( U <_ V /\\ ( V - U ) <_ 1 ) ) /\\ '
              'A. t e. ( U [,] V ) T <_ ( abs ` t ) ) -> ( abs ` ( %s lint <. %s , %s >. ) ) <_ ( 8 x. ( ( Y x. ( log ` Y ) ) / T ) ) )') % (
    CHI, LDL, PTL(C1, 'U'), PTL(C1, 'V'))
# L ( 1 ) =/= 0
AI = 'sum_ i e. ( 1 ... m ) ( A ` i )'
S['ef4ab1'] = ('( ( ( A : NN --> CC /\\ B e. RR /\\ A. m e. NN ( abs ` %s ) <_ B ) /\\ seq 1 ( + , ( n e. NN |-> ( ( A ` n ) / n ) ) ) ~~> L ) -> '
               'sum_ k e. NN ( sum_ i e. ( 1 ... k ) ( A ` i ) x. ( ( k ^c -u 1 ) - ( ( k + 1 ) ^c -u 1 ) ) ) = L )') % AI
S['ef4l1'] = '( %s -> ( %s ` 1 ) =/= 0 )' % (CHI, LFN)
# zero sets
S['ef4zf'] = ('( ( %s /\\ ( ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ T e. RR ) ) -> ( %s = { r e. %s | ( %s ` r ) = 0 } /\\ '
              'A. q e. %s ( %s holord q ) = ( %s holord q ) ) )') % (CHI, ZF(E, 'A', 'T'), BOX('A', 'T'), LFN, ZF(E, 'A', 'T'), E, LFN)
BAND = ('( ( F ` p ) = 0 /\\ ( ( ( 1 / 2 ) <_ ( Re ` p ) /\\ ( Re ` p ) <_ ( 3 / 2 ) ) /\\ '
        '( T < ( abs ` ( Im ` p ) ) /\\ ( abs ` ( Im ` p ) ) <_ ( T + 1 ) ) ) )')
S['ef4bm'] = '( ( ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) /\\ ( G C_ CC /\\ A. p e. G %s ) ) -> %s <_ ( %s x. %s ) )' % (
    DD(), BAND, MASS('G', 'F'), KB, LT4)
# toolkit
GJ1 = CHN('( j + 1 )')
S['ef4cut'] = ('( ( ( B e. Fin /\\ B C_ RR ) /\\ ( P e. RR /\\ Q e. RR /\\ 1 <_ ( Q - P ) ) ) -> E. m e. NN E. g ( g : ( 0 ... m ) --> RR /\\ '
               '( ( ( g ` 0 ) = P /\\ ( g ` m ) = Q ) /\\ A. j e. ( 0 ..^ m ) ( ( g ` j ) < ( g ` ( j + 1 ) ) /\\ ( ( g ` ( j + 1 ) ) - ( g ` j ) ) <_ 1 ) ) /\\ '
               '( A. j e. ( 1 ..^ m ) -. ( g ` j ) e. B /\\ A. j e. ( 0 ... m ) ( P <_ ( g ` j ) /\\ ( g ` j ) <_ Q ) ) ) )')
HSSD = [('1', '( ph -> A e. Fin )'), ('2', '( ph -> B e. Fin )'), ('3', '( ( ph /\\ q e. ( A u. B ) ) -> C e. CC )')]
S['ef4ssd'] = ('( ph -> ( sum_ q e. A C - sum_ q e. B C ) = ( sum_ q e. ( A \\ B ) C - sum_ q e. ( B \\ A ) C ) )')
# the contour
HCH = ('( ( ( K e. NN /\\ G : ( 0 ... K ) --> RR ) /\\ A. j e. ( 0 ..^ K ) ( %s < %s /\\ ( %s - %s ) <_ 1 ) /\\ '
       '( ( G ` 0 ) = -u U /\\ ( G ` K ) = V ) ) /\\ ( A. j e. ( 0 ... K ) A. x e. ( S [,] %s ) ( %s ` %s ) =/= 0 /\\ '
       'A. t e. ( -u U [,] V ) ( %s ` %s ) =/= 0 ) )') % (
    CHN('j'), GJ1, GJ1, CHN('j'), C1, LFN, PTL('x', CHN('j')), LFN, PTL('S', 't'))
S['ef4id'] = ('( ( ( %s /\\ %s ) /\\ ( ( ( U e. RR /\\ V e. RR ) /\\ ( T <_ U /\\ T <_ V ) ) /\\ ( S e. RR /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S < %s ) ) ) /\\ %s ) -> '
              '( %s + ( %s x. %s ) ) = ( ( ( %s - %s ) + ( %s + %s ) ) - %s ) )') % (
    CHI, YT, C1, HCH, PS1, TPI, SRL, BOT, TOP, EB, ET, LEFT)
HUV = '( ( U e. RR /\\ V e. RR ) /\\ ( ( T <_ U /\\ U <_ ( T + 1 ) ) /\\ ( T <_ V /\\ V <_ ( T + 1 ) ) ) )'
SS8 = '( S e. RR /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S <_ ( 5 / 8 ) ) )'
S['ef4zs'] = ('( ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ A. v e. ( ( 1 / 2 ) [,] 3 ) ( ( %s ` %s ) =/= 0 /\\ ( %s ` %s ) =/= 0 ) ) -> '
              '( abs ` ( %s - %s ) ) <_ ( ( ( ; ; ; ; 7 2 0 0 0 x. ( Y ^c S ) ) x. ( %s ^ 2 ) ) + ( ( %s x. Y ) x. ( %s / T ) ) ) )') % (
    CHI, YT, HUV, SS8, LFN, PTL('v', '-u U'), LFN, PTL('v', 'V'), SCE, SRL, LNT, KB, LN4)
HGD = 'A. v e. ( ( 1 / 2 ) [,] 3 ) ( %s /\\ %s )' % (GOOD(PTL('v', '-u U'), LFN, LN4), GOOD(PTL('v', 'V'), LFN, LN4))
HWM = '( M e. NN0 /\\ ( V <_ ( -u U + ( M / 2 ) ) /\\ ( -u U + ( M / 2 ) ) <_ ( T + 2 ) ) )'
HSG = ('( ( %s /\\ -. S e. ( Re " %s ) ) /\\ %s /\\ ( A. j e. ( 0 ..^ M ) A. q e. %s ( Re ` q ) =/= S /\\ %s <_ ( %s x. ( %s ^ 2 ) ) ) )') % (
    SS8, BZ4, HWM, ZK('j', '-u U', LFN), PHI('S', '-u U', 'M', LFN), KS, LN4)
HCT = ('( ( ( K e. NN /\\ G : ( 0 ... K ) --> RR ) /\\ A. j e. ( 0 ..^ K ) ( %s < %s /\\ ( %s - %s ) <_ 1 ) /\\ '
       '( ( G ` 0 ) = -u U /\\ ( G ` K ) = V ) ) /\\ ( A. j e. ( 1 ..^ K ) -. ( G ` j ) e. ( Im " %s ) /\\ '
       'A. j e. ( 0 ... K ) ( -u U <_ ( G ` j ) /\\ ( G ` j ) <_ V ) ) )') % (CHN('j'), GJ1, GJ1, CHN('j'), BZ4)
CBND = '( abs ` ( %s + ( %s x. %s ) ) ) <_ ( ( 2 x. _pi ) x. ( %s x. ( %s + %s ) ) )' % (PS1, TPI, SCE, KC, P1, P2)
S['ef4core'] = '( ( ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) /\\ %s /\\ %s ) -> %s )' % (CHI, YT, HUV, HGD, HSG, HCT, CBND)
S['ef4cnt'] = '( ( %s /\\ %s ) -> %s )' % (CHI, YT, CBND)
S['ef4ef'] = '( ( %s /\\ %s ) -> ( abs ` ( %s + %s ) ) <_ ( %s x. ( ( %s + %s ) + ( %s ^ 2 ) ) ) )' % (CHI, YT, PSI, SCE, KE, P1, P2, LNY)

PV = lambda x: '( C + ( _i x. %s ) )' % x
S['ef4vsl'] = ('( ( ( G e. ( D -cn-> CC ) /\\ C e. RR ) /\\ ( ( P e. RR /\\ Q e. RR /\\ R e. RR ) /\\ ( P <_ Q /\\ Q <_ R /\\ P < R ) ) /\\ '
               'A. t e. ( P [,] R ) %s e. D ) -> ( G lint <. %s , %s >. ) = ( ( G lint <. %s , %s >. ) + ( G lint <. %s , %s >. ) ) )') % (
    PV('t'), PV('P'), PV('R'), PV('P'), PV('Q'), PV('Q'), PV('R'))
HZ = ante_of(S['ef4zs'])[0]
CFL = '{ r e. %s | ( %s ` r ) = 0 }' % (BOX('( 1 / 2 )', 'T'), LFN)
RF = ZR('S', C1, '-u U', 'V', LFN)
S['ef4zs1'] = '( %s -> ( abs ` sum_ q e. ( %s \\ %s ) %s ) <_ ( ( ; ; ; ; 7 2 0 0 0 x. ( Y ^c S ) ) x. ( %s ^ 2 ) ) )' % (HZ, CFL, RF, RS1, LNT)
S['ef4zs2'] = '( %s -> ( abs ` sum_ q e. ( %s \\ %s ) %s ) <_ ( ( %s x. Y ) x. ( %s / T ) ) )' % (HZ, RF, CFL, RS1, KB, LN4)
HLN = ('( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ ( ( %s /\\ -. S e. ( Re " %s ) ) /\\ ( ( K e. NN /\\ G : ( 0 ... K ) --> RR ) /\\ ( ( G ` 0 ) = -u U /\\ ( G ` K ) = V ) ) /\\ '
       '( A. e e. ( 1 ..^ K ) -. ( G ` e ) e. ( Im " %s ) /\\ A. e e. ( 0 ... K ) ( -u U <_ ( G ` e ) /\\ ( G ` e ) <_ V ) ) ) )') % (CHI, YT, HUV, HGD, SS8, BZ4, BZ4)
S['ef4ln'] = '( %s -> ( A. j e. ( 0 ... K ) A. x e. ( S [,] %s ) ( %s ` %s ) =/= 0 /\\ A. t e. ( -u U [,] ( T + 2 ) ) ( %s ` %s ) =/= 0 ) )' % (
    HLN, C1, LFN, PTL('x', CHN('j')), LFN, PTL('S', 't'))
HB = '( ( ( %s x. ( %s ^ 2 ) ) / T ) x. ( ( Y ^c %s ) / ( log ` Y ) ) )' % (KGH, LN4, C1)
RB = '( 8 x. ( ( Y x. ( log ` Y ) ) / T ) )'
LB = '( ( %s x. ( Y ^c S ) ) x. ( %s ^ 2 ) )' % (KL, LN4)
ZB = '( ( ( ; ; ; ; 7 2 0 0 0 x. ( Y ^c S ) ) x. ( %s ^ 2 ) ) + ( ( %s x. Y ) x. ( %s / T ) ) )' % (LNT, KB, LN4)
EDGE = '( ( ( 2 x. %s ) + ( 2 x. %s ) ) + %s )' % (HB, RB, LB)
S['ef4nm'] = ('( ( ( %s /\\ %s ) /\\ %s /\\ ( ( A e. RR /\\ B e. RR ) /\\ ( A <_ %s /\\ B <_ %s ) ) ) -> '
              '( A + ( ( 2 x. _pi ) x. B ) ) <_ ( ( 2 x. _pi ) x. ( %s x. ( %s + %s ) ) ) )') % (CHI, YT, SS8, EDGE, ZB, KC, P1, P2)
S['ef4scc'] = '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (HZ, SCE, SRL)
S['ef4idc'] = '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (ante_of(S['ef4id'])[0], BOT, TOP, EB, ET, LEFT, PS1)
HYPS = {'ef4ssd': HSSD}
ORDER = list(S)


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'ef4gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'ef4gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=ef4gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::ef4gc%s.1 |- %s\n' % (lab, S[lab]))
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
        for lab in ORDER:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or ORDER)


# ---- worksheet helpers -----------------------------------------------------------------
def _find(A, f, path=()):
    f = ' '.join(f.split())
    if A == f:
        return path
    if not (A.startswith('( ') and A.endswith(' )')):
        return None
    try:
        parts = top_and(A)
    except AssertionError:
        return None
    if len(parts) == 1:
        return None
    for i, p in enumerate(parts):
        r = _find(p, f, path + ((len(parts), i),))
        if r is not None:
            return r
    return None


_SEL = {(2, 0): 'simpl', (2, 1): 'simpr', (3, 0): 'simp1', (3, 1): 'simp2', (3, 2): 'simp3'}


def leaf(w, A, f, memo=None):
    """( A -> f ) for a conjunct f anywhere in the conjunction tree A (simpl/simpr/simp1-3 chains)"""
    f = ' '.join(f.split())
    key = (A, f)
    if memo is not None and key in memo:
        return memo[key]
    path = _find(A, f)
    if path is None:
        raise KeyError('not a conjunct: ' + f)
    cur = A
    st = w.s([], 'id', '( %s -> %s )' % (A, A))
    for n, i in path:
        parts = top_and(cur)
        st = w.s([st, w.inst(_SEL[(n, i)])], 'syl', '( %s -> %s )' % (A, parts[i]))
        cur = parts[i]
    if memo is not None:
        memo[key] = st
    return st


class Ctx:
    """step maker under a fixed antecedent with conjunct lookup"""
    def __init__(self, w, A):
        self.w, self.A, self.memo = w, A, {}

    def __call__(self, h, r, f, name=None):
        return self.w.s(h, r, '( %s -> %s )' % (self.A, f), name=name)

    def g(self, f):
        return leaf(self.w, self.A, f, self.memo)

    def a1(self, st, f):
        """closed step st : f lifted by a1i"""
        return self.w.s([st], 'a1i', '( %s -> %s )' % (self.A, f))


def ral_at(w, A, al, var, val, body, valin):
    """( A -> body[var:=val] ) from al : ( A -> A. var e. X body ) and valin : ( A -> val e. X )"""
    eq, new = w.wcongr(body, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
    return w.s([eq, al, valin], 'rspcdva', '( %s -> %s )' % (A, new)), new


def cbvral(w, X, var, new, body):
    """closed step ( A. var e. X body <-> A. new e. X body[var:=new] )"""
    eq, nb = w.wcongr(body, {var: new}, '%s = %s' % (var, new), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, new, var, new))})
    return w.s([eq], 'cbvralvw', '( A. %s e. %s %s <-> A. %s e. %s %s )' % (var, X, body, new, X, nb)), nb


def seg_sub(w, A0, Aa, Bb, ac, bc, D, mem_fn):
    """( A0 -> ( Aa cseg Bb ) C_ D ); mem_fn(A1) gives ( A1 -> ( Aa + ( t x. ( Bb - Aa ) ) ) e. D ) for
    A1 = ( A0 /\\ t e. ( 0 [,] 1 ) ); t and a must not occur in A0"""
    PT_ = '( %s + ( t x. ( %s - %s ) ) )' % (Aa, Bb, Aa)
    A1 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A0
    m1 = mem_fn(A1)
    SEG = '( %s cseg %s )' % (Aa, Bb)
    A2 = '( %s /\\ a e. %s )' % (A0, SEG)
    A3 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A2
    A4 = '( %s /\\ a = %s )' % (A3, PT_)
    m3 = w.s([m1], 'adantlr', '( %s -> %s e. %s )' % (A3, PT_, D))
    m4 = w.s([w.s([], 'simpr', '( %s -> a = %s )' % (A4, PT_)), w.s([m3], 'adantr', '( %s -> %s e. %s )' % (A4, PT_, D))], 'eqeltrd', '( %s -> a e. %s )' % (A4, D))
    m5 = w.s([m4], 'ex', '( %s -> ( a = %s -> a e. %s ) )' % (A3, PT_, D))
    EX = 'E. t e. ( 0 [,] 1 ) a = %s' % PT_
    m6 = w.s([m5], 'rexlimdva', '( %s -> ( %s -> a e. %s ) )' % (A2, EX, D))
    el = w.s([w.s([], 'simpr', '( %s -> a e. %s )' % (A2, SEG)), w.s([w.s([ac], 'adantr', '( %s -> %s e. CC )' % (A2, Aa)), w.s([bc], 'adantr', '( %s -> %s e. CC )' % (A2, Bb)), w.inst('csegel')],
                                                                     'syl2anc', '( %s -> ( a e. %s <-> %s ) )' % (A2, SEG, EX))], 'mpbid', '( %s -> %s )' % (A2, EX))
    m7 = w.s([el, m6], 'mpd', '( %s -> a e. %s )' % (A2, D))
    return w.s([w.s([m7], 'ex', '( %s -> ( a e. %s -> a e. %s ) )' % (A0, SEG, D))], 'ssrdv', '( %s -> %s C_ %s )' % (A0, SEG, D))


def open_to_closed(w, A0, st):
    """from st : ( ( A0 /\\ t e. ( 0 [,] 1 ) ) -> f ) the same under t e. ( 0 (,) 1 )"""
    f = [l for l in w.lines if l.startswith(st + ':')][0].split(' |- ', 1)[1]
    body = ante_of(f)[1]
    ss = w.s([w.s([], 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )'), w.inst('ssel')], 'ax-mp', '( t e. ( 0 (,) 1 ) -> t e. ( 0 [,] 1 ) )')
    return w.s([ss, st], 'sylan2', '( ( %s /\\ t e. ( 0 (,) 1 ) ) -> %s )' % (A0, body))


def ne0_re(c, z, zc, r0):
    """( A -> z =/= 0 ) from z e. CC and r0 : ( A -> 0 < ( Re ` z ) )"""
    w = c.w
    rz = c([r0], 'gt0ne0d', '( Re ` %s ) =/= 0' % z)
    r0_ = w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (z, z)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> ( Re ` %s ) = 0 )' % (z, z))
    return c([rz, w.s([r0_], 'necon3i', '( ( Re ` %s ) =/= 0 -> %s =/= 0 )' % (z, z))], 'syl', '%s =/= 0' % z)


def subst(w, expr, var, val):
    """closed step ( var = val -> expr = expr[var:=val] ) and the new text"""
    idx = w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))
    st, new = w.congr(expr, {var: val}, '%s = %s' % (var, val), {var: idx})
    if st is None:
        st = w.s([], 'eqidd', '( %s = %s -> %s = %s )' % (var, val, expr, new))
    return st, new


def hp0_facts(c, z, zin):
    """from ( A -> z e. HP0 ): z e. CC, 0 < ( Re ` z )"""
    w = c.w
    e = c([c.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (z, HP0, z, z))
    b = c([zin, e], 'mpbid', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (z, z))
    return c([b, w.inst('simpl')], 'syl', '%s e. CC' % z), c([b, w.inst('simpr')], 'syl', '0 < ( Re ` %s )' % z), e


def hp0_cj(c, z, zin):
    """( A -> ( * ` z ) e. HP0 ) from ( A -> z e. HP0 )"""
    w = c.w
    zc, r0, _ = hp0_facts(c, z, zin)
    Z = '( * ` %s )' % z
    e = c([c.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (Z, HP0, Z, Z))
    rc = c([zc, w.inst('recj')], 'syl', '( Re ` %s ) = ( Re ` %s )' % (Z, z))
    r1 = c([r0, c([rc], 'eqcomd', '( Re ` %s ) = ( Re ` %s )' % (z, Z))], 'breqtrd', '0 < ( Re ` %s )' % Z)
    return c([c([c([zc], 'cjcld', '%s e. CC' % Z), r1], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (Z, Z)), e], 'mpbird', '%s e. %s' % (Z, HP0))


def rebuild(w, c0, f, special):
    """( c0.A -> f ) where every leaf of f is in special (formula -> step) or a conjunct of c0.A"""
    f = ' '.join(f.split())
    if f in special:
        return special[f]
    if _find(c0.A, f) is not None:
        return c0.g(f)
    parts = top_and(f)
    if len(parts) == 1:
        raise KeyError('no step for ' + f)
    steps = [rebuild(w, c0, p, special) for p in parts]
    return c0(steps, 'jca' if len(parts) == 2 else '3jca', f)
