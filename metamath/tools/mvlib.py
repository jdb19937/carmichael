"""Sortie MV helpers (Route Z: MeanValue.lean + the four used declarations of
LargeValues.lean).  STATEMENTS / HYPS / ORDER are the frozen statements of
MV-blueprint.md; `MM_DB=sorties/mv.mm python3 tools/mvlib.py [LABEL...]`
grammar-checks them with mmatch."""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

STATEMENTS = {}
HYPS = {}
ORDER = []


def st(label, text, hyps=()):
    STATEMENTS[label] = ' '.join(text.split())
    HYPS[label] = list(hyps)
    ORDER.append(label)


# ------------------------------------------------------------------ notation
def IOO(a, b): return '( %s (,) %s )' % (a, b)
def ITG(I, X, t='t'): return 'S. %s %s _d %s' % (I, X, t)
def ABS2(e): return '( ( abs ` %s ) ^ 2 )' % e
def KS(A, t='t'): return '( ( sin ` ( %s x. %s ) ) ^ 2 )' % (A, t)
def KQ(A, t='t'): return '( %s / ( %s ^ 2 ) )' % (KS(A, t), t)                       # sin^2(At)/t^2
def KC(A, H, t='t'): return '( ( %s x. ( cos ` ( %s x. %s ) ) ) / ( %s ^ 2 ) )' % (KS(A, t), H, t, t)
def HQ(B, t='t'): return '( ( 1 - ( cos ` ( %s x. %s ) ) ) / ( %s ^ 2 ) )' % (B, t, t)
def TRI(D, Y): return 'if ( ( abs ` %s ) <_ %s , ( %s - ( abs ` %s ) ) , 0 )' % (Y, D, D, Y)
def PT(N, X, m='m', k='k'):
    """sum_{m<N} ( 1 + 2 sum_{k=1}^m cos ( 2 k X ) ) = sin^2(N X)/sin^2(X)"""
    return 'sum_ %s e. ( 0 ..^ %s ) ( 1 + ( 2 x. sum_ %s e. ( 1 ... %s ) ( cos ` ( ( 2 x. %s ) x. %s ) ) ) )' % (m, N, k, m, k, X)
CNR = '( RR -cn-> CC )'
def CNI(a, b): return '( %s -cn-> CC )' % IOO(a, b)
HALF = '( 1 / 2 )'
PI2 = '( _pi / 2 )'
GA = lambda A: '( ( %s x. _pi ) / 2 )' % A                                            # A pi / 2

# kernel_mvt objects: index set P, coefficients C, frequencies L
HK = '( P e. Fin /\\ A. a e. P ( ( C ` a ) e. CC /\\ ( L ` a ) e. RR ) )'
def EX(Lv, t): return '( exp ` ( _i x. ( %s x. %s ) ) )' % (Lv, t)
def SX(t, i='i'): return 'sum_ %s e. P ( ( C ` %s ) x. %s )' % (i, i, EX('( L ` %s )' % i, t))
def SXD(t, i='i'): return 'sum_ %s e. P ( ( ( C ` %s ) x. ( _i x. ( L ` %s ) ) ) x. %s )' % (i, i, i, EX('( L ` %s )' % i, t))
def CCJ(i, j): return '( ( C ` %s ) x. ( * ` ( C ` %s ) ) )' % (i, j)
DT = '( _pi / ( 2 x. T ) )'                                                           # the window delta
def BIL(D=DT): return 'sum_ i e. P sum_ j e. P ( %s x. %s )' % (CCJ('i', 'j'), TRI(D, '( ( L ` i ) - ( L ` j ) )'))

# Dirichlet characters (set.mm DChr), Z4a spelling
def DB(n='N'): return '( Base ` ( DChr ` %s ) )' % n
def LZ(n='N'): return '( ZRHom ` ( Z/nZ ` %s ) )' % n
def CHV(x, a, n='N'): return '( %s ` ( %s ` %s ) )' % (x, LZ(n), a)
FZM = '( 1 ... M )'
AOK = 'A. k e. %s ( A ` k ) e. CC' % FZM
def NEX(n, t): return '( exp ` ( _i x. ( -u ( log ` %s ) x. %s ) ) )' % (n, t)
def DS(x, t, A='A', n='n'):
    return 'sum_ %s e. %s ( ( ( %s ` %s ) x. %s ) x. %s )' % (n, FZM, A, n, CHV(x, n), NEX(n, t))
def DSP(x, t, A='A', n='n'):
    return 'sum_ %s e. %s ( ( ( %s ` %s ) x. %s ) x. ( %s ^c -u ( _i x. %s ) ) )' % (n, FZM, A, n, CHV(x, n), n, t)
SA2 = 'sum_ n e. %s %s' % (FZM, ABS2('( A ` n )'))
SLA2 = 'sum_ n e. %s ( ( 1 + ( ( log ` n ) ^ 2 ) ) x. %s )' % (FZM, ABS2('( A ` n )'))
HMV = '( ( N e. NN /\\ T e. RR+ ) /\\ ( M e. NN0 /\\ %s ) )' % AOK
TT = '( -u T (,) T )'
T1 = '( -u ( T + 1 ) (,) ( T + 1 ) )'
def JI1(y): return IOO('( %s - %s )' % (y, HALF), '( %s + %s )' % (y, HALF))
SEP1 = 'A. a e. P A. b e. P ( a =/= b -> 1 <_ ( abs ` ( ( Y ` a ) - ( Y ` b ) ) ) )'
HF = '( F : RR --> CC /\\ ( RR _D F ) = G /\\ G e. %s )' % CNR
# spaced families: index set S, character map K, point map Y
HFAM = '( S e. Fin /\\ K : S --> %s /\\ Y : S --> RR )' % DB()
SEPF = 'A. a e. S A. b e. S ( ( a =/= b /\\ ( K ` a ) = ( K ` b ) ) -> 1 <_ ( abs ` ( ( Y ` a ) - ( Y ` b ) ) ) )'
RNGF = 'A. a e. S ( abs ` ( Y ` a ) ) <_ T'
HLV = '( ( N e. NN /\\ T e. RR /\\ 2 <_ T ) /\\ ( M e. NN0 /\\ %s ) )' % AOK

# ------------------------------------------------------------------ item 2: the Fejer identity, finite form
st('mvdk', '( ( M e. NN0 /\\ X e. CC ) -> ( sin ` ( ( ( 2 x. M ) + 1 ) x. X ) ) = ( ( sin ` X ) x. '
   '( 1 + ( 2 x. sum_ k e. ( 1 ... M ) ( cos ` ( ( 2 x. k ) x. X ) ) ) ) ) )')
st('mvsinsq', '( ( N e. NN0 /\\ X e. CC ) -> ( ( sin ` ( N x. X ) ) ^ 2 ) = ( ( ( sin ` X ) ^ 2 ) x. %s ) )' % PT('N', 'X'))
st('mvdvsin', '( B e. RR -> ( RR _D ( t e. RR |-> ( sin ` ( B x. t ) ) ) ) = ( t e. RR |-> ( B x. ( cos ` ( B x. t ) ) ) ) )')
st('mvcositg', '( ( C e. RR+ /\\ K e. NN ) -> %s = 0 )' % ITG(IOO('0', '( _pi / ( 2 x. C ) )'), '( cos ` ( ( 2 x. K ) x. ( C x. t ) ) )'))
st('mvfejint', '( ( C e. RR+ /\\ N e. NN0 ) -> ( ( t e. %s |-> %s ) e. L^1 /\\ %s = ( N x. ( _pi / ( 2 x. C ) ) ) ) )' % (
    IOO('0', '( _pi / ( 2 x. C ) )'), PT('N', '( C x. t )'), ITG(IOO('0', '( _pi / ( 2 x. C ) )'), PT('N', '( C x. t )'))))
st('mvcoslb', '( ( X e. RR /\\ 0 < X /\\ X <_ 2 ) -> ( 1 - ( ( X ^ 2 ) / 2 ) ) <_ ( cos ` X ) )')
st('mvsindbl', '( ( ( H e. RR /\\ 0 < H /\\ H <_ 1 ) /\\ ( L e. RR /\\ 0 <_ L /\\ L <_ ( sin ` H ) ) ) -> '
   '( ( 2 x. L ) x. ( 1 - ( ( H ^ 2 ) / 2 ) ) ) <_ ( sin ` ( 2 x. H ) ) )')
st('mvsinlb', '( ( Y e. RR /\\ 0 < Y /\\ Y <_ 2 ) -> ( Y x. ( 1 - ( ( ; 1 7 x. ( Y ^ 2 ) ) / ; 9 6 ) ) ) <_ ( sin ` Y ) )')
st('mvsinb', '( Y e. ( 0 (,) ( _pi / 2 ) ) -> ( 0 < ( sin ` Y ) /\\ ( sin ` Y ) < Y /\\ '
   '( ( 1 / ( ( sin ` Y ) ^ 2 ) ) - ( 1 / ( Y ^ 2 ) ) ) <_ 9 ) )')
st('mvsinabs', '( X e. RR -> ( abs ` ( sin ` X ) ) <_ ( abs ` X ) )')
st('mvibl', '( ( ( A e. RR /\\ B e. RR ) /\\ ( F e. ( ( A (,) B ) -cn-> CC ) /\\ Z e. RR /\\ A. y e. ( A (,) B ) ( abs ` ( F ` y ) ) <_ Z ) ) '
   '-> F e. L^1 )')
st('mvkibl', '( ( ( A e. RR /\\ H e. RR ) /\\ ( U e. RR /\\ V e. RR /\\ 0 <_ U ) ) -> ( ( t e. %s |-> %s ) e. L^1 /\\ '
   '( t e. %s |-> %s ) e. L^1 ) )' % (IOO('U', 'V'), KC('A', 'H'), IOO('U', 'V'), KQ('A')))
st('mvgn', '( ( A e. RR+ /\\ N e. NN ) -> ( ( %s - ( 9 x. ( ( A / N ) x. %s ) ) ) <_ %s /\\ %s <_ %s ) )' % (
    GA('A'), PI2, ITG(IOO('0', '( ( N x. _pi ) / ( 2 x. A ) )'), KQ('A')), ITG(IOO('0', '( ( N x. _pi ) / ( 2 x. A ) )'), KQ('A')), GA('A')))
st('mvtail', '( ( A e. RR /\\ ( R e. RR+ /\\ Q e. RR /\\ R <_ Q ) ) -> %s <_ ( 1 / R ) )' % ITG(IOO('R', 'Q'), KQ('A')))
st('mvlim', '( ( ( X e. RR /\\ Y e. RR /\\ Z e. RR ) /\\ ( J e. RR /\\ A. n e. NN ( J <_ n -> X <_ ( Y + ( Z / n ) ) ) ) ) -> X <_ Y )')
st('mvgr', '( ( A e. RR+ /\\ R e. RR+ ) -> ( ( %s - ( 1 / R ) ) <_ %s /\\ %s <_ %s ) )' % (
    GA('A'), ITG(IOO('0', 'R'), KQ('A')), ITG(IOO('0', 'R'), KQ('A')), GA('A')))
st('mvhq', '( ( B e. RR /\\ R e. RR+ ) -> ( ( t e. %s |-> %s ) e. L^1 /\\ ( abs ` ( %s - ( %s x. ( abs ` B ) ) ) ) <_ ( 2 / R ) ) )' % (
    IOO('0', 'R'), HQ('B'), ITG(IOO('0', 'R'), HQ('B')), PI2))
st('mvtriabs', '( ( A e. RR /\\ 0 <_ A /\\ H e. RR ) -> ( ( ( abs ` ( ( 2 x. A ) + H ) ) + ( abs ` ( ( 2 x. A ) - H ) ) ) - ( 2 x. ( abs ` H ) ) ) '
   '= ( 2 x. %s ) )' % TRI('( 2 x. A )', 'H'))
st('mvfej', '( ( ( A e. RR /\\ 0 <_ A ) /\\ ( H e. RR /\\ R e. RR+ ) ) -> ( ( t e. %s |-> %s ) e. L^1 /\\ '
   '( abs ` ( %s - ( ( _pi / 4 ) x. %s ) ) ) <_ ( 2 / R ) ) )' % (
    IOO('0', 'R'), KC('A', 'H'), ITG(IOO('0', 'R'), KC('A', 'H')), TRI('( 2 x. A )', 'H')))

# ------------------------------------------------------------------ items 1, 3: kernel lower bound, kernel_mvt
st('mvsinlow', '( ( Y e. RR /\\ 0 < Y /\\ Y <_ 1 ) -> ( ( 2 / 3 ) x. ( Y ^ 2 ) ) <_ ( ( sin ` Y ) ^ 2 ) )')
st('mvrefl', '( ( T e. RR+ /\\ F e. %s ) -> S. ( -u T (,) 0 ) ( F ` t ) _d t = S. ( 0 (,) T ) ( F ` -u t ) _d t )' % CNR)
st('mvsx', '( ( %s /\\ t e. RR ) -> ( %s + %s ) = ( 2 x. sum_ i e. P sum_ j e. P ( ( Re ` %s ) x. ( cos ` ( ( ( L ` i ) - ( L ` j ) ) x. t ) ) ) ) )' % (
    HK, ABS2(SX('t')), ABS2(SX('-u t')), CCJ('i', 'j')))
st('mvsxdv', '( %s -> ( ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) /\\ ( t e. RR |-> %s ) e. %s /\\ ( t e. RR |-> %s ) e. %s ) )' % (
    HK, SX('t'), SXD('t'), SX('t'), CNR, SXD('t'), CNR))
AK = '( _pi / ( 4 x. T ) )'
QQ = '( %s + %s )' % (ABS2(SX('t')), ABS2(SX('-u t')))
st('mvkm0', '( ( T e. RR+ /\\ %s ) -> ( ( t e. ( 0 (,) T ) |-> %s ) e. L^1 /\\ %s = %s ) )' % (HK, QQ, ITG(TT, ABS2(SX('t'))), ITG(IOO('0', 'T'), QQ)))
KQQ = '( %s x. %s )' % (KQ(AK), QQ)
THIJ = '( ( L ` i ) - ( L ` j ) )'
def KSUM(U, V): return 'sum_ i e. P sum_ j e. P ( ( Re ` %s ) x. %s )' % (CCJ('i', 'j'), ITG(IOO(U, V), KC(AK, THIJ)))
st('mvkm2', '( ( ( T e. RR+ /\\ %s ) /\\ ( U e. RR /\\ V e. RR /\\ 0 <_ U ) ) -> ( ( t e. %s |-> %s ) e. L^1 /\\ %s = ( 2 x. %s ) ) )' % (
    HK, IOO('U', 'V'), KQQ, ITG(IOO('U', 'V'), KQQ), KSUM('U', 'V')))
st('mvkm1', '( ( ( T e. RR+ /\\ %s ) /\\ ( R e. RR+ /\\ T <_ R ) ) -> %s <_ ( ( 3 / ( 2 x. ( %s ^ 2 ) ) ) x. ( 2 x. sum_ i e. P sum_ j e. P '
   '( ( Re ` %s ) x. %s ) ) ) )' % (HK, ITG(TT, ABS2(SX('t'))), AK, CCJ('i', 'j'), ITG(IOO('0', 'R'), KC(AK, '( ( L ` i ) - ( L ` j ) )'))))
st('mvkmvt', '( ( T e. RR+ /\\ %s ) -> %s <_ ( ( ( ; 1 2 x. ( T ^ 2 ) ) / _pi ) x. ( Re ` %s ) ) )' % (
    HK, ITG(TT, ABS2(SX('t'))), BIL()))

# ------------------------------------------------------------------ items 4, 5: counting, orthogonality, mean_value_chars
st('mvlgap', '( ( M e. NN /\\ Q e. NN /\\ M <_ Q ) -> ( ( Q - M ) / Q ) <_ ( ( log ` Q ) - ( log ` M ) ) )')
st('mvwabs', '( ( ( m e. ( 1 ... Q ) /\\ n e. ( 1 ... Q ) ) /\\ ( T e. RR+ /\\ ( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s ) ) -> '
   '( abs ` ( n - m ) ) <_ ( ( 2 x. Q ) / T ) )' % DT)
st('mvwin', '( ( ( D e. NN /\\ T e. RR+ /\\ Q e. NN0 ) /\\ m e. ( 1 ... Q ) ) -> sum_ n e. ( 1 ... Q ) if ( ( D || ( n - m ) /\\ '
   '( abs ` ( ( log ` n ) - ( log ` m ) ) ) < %s ) , 1 , 0 ) <_ ( ( ( 4 x. Q ) / ( D x. T ) ) + 1 ) )' % DT)
st('mvorth', '( ( N e. NN /\\ U e. ZZ /\\ V e. ZZ ) -> ( abs ` sum_ x e. %s ( %s x. ( * ` %s ) ) ) <_ if ( N || ( U - V ) , ( phi ` N ) , 0 ) )' % (
    DB(), CHV('x', 'U'), CHV('x', 'V')))
def WPAIR(m='m', n='n'):
    return '( ( ( abs ` ( A ` %s ) ) x. ( abs ` ( A ` %s ) ) ) x. ( %s x. if ( N || ( %s - %s ) , ( phi ` N ) , 0 ) ) )' % (
        m, n, TRI(DT, '( -u ( log ` %s ) - -u ( log ` %s ) )' % (m, n)), m, n)
MID = '( ( ( ; 1 2 x. ( T ^ 2 ) ) / _pi ) x. sum_ m e. %s sum_ n e. %s %s )' % (FZM, FZM, WPAIR())
st('mvmvc1', '( %s -> ( sum_ x e. %s %s e. RR /\\ sum_ x e. %s %s <_ %s ) )' % (HMV, DB(), ITG(TT, ABS2(DS('x', 't'))), DB(), ITG(TT, ABS2(DS('x', 't'))), MID))
st('mvmvc2', '( %s -> ( %s e. RR /\\ ( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s ) e. RR /\\ %s <_ ( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s ) ) )' % (HMV, MID, SA2, MID, SA2))
st('mvmvc', '( %s -> sum_ x e. %s %s <_ ( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s ) )' % (
    HMV, DB(), ITG(TT, ABS2(DS('x', 't'))), SA2))
st('mvmvcp', '( %s -> sum_ x e. %s %s <_ ( ( ; ; 1 0 0 x. ( M + ( N x. T ) ) ) x. %s ) )' % (
    HMV, DB(), ITG(TT, ABS2(DSP('x', 't'))), SA2))

# ------------------------------------------------------------------ item 6: LargeValues
st('mvdisj', '( ph -> sum_ i e. P %s <_ %s )' % (ITG(JI1('( Y ` i )'), 'X'), ITG(T1, 'X')),
   [('mvdisj.p', '( ph -> ( P e. Fin /\\ Y : P --> RR /\\ T e. RR ) )'), ('mvdisj.a', '( ph -> A. a e. P ( abs ` ( Y ` a ) ) <_ T )'),
    ('mvdisj.s', '( ph -> %s )' % SEP1), ('mvdisj.c', '( ph -> ( t e. RR |-> X ) e. %s )' % CNR),
    ('mvdisj.r', '( ( ph /\\ t e. RR ) -> X e. RR )'), ('mvdisj.n', '( ( ph /\\ t e. RR ) -> 0 <_ X )')])
st('mvpcs', '( ( %s /\\ ( P e. Fin /\\ Y : P --> RR /\\ T e. RR ) /\\ ( A. a e. P ( abs ` ( Y ` a ) ) <_ T /\\ %s ) ) -> '
   'sum_ i e. P %s <_ ( ( 2 x. %s ) + %s ) )' % (
    HF, SEP1, ABS2('( F ` ( Y ` i ) )'), ITG(T1, ABS2('( F ` t )')), ITG(T1, ABS2('( G ` t )'))))
ADM = '( u e. NN |-> ( ( A ` u ) x. ( _i x. -u ( log ` u ) ) ) )'
HFX = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (HLV, HFAM, RNGF, SEPF)
SXF = '{ q e. S | ( K ` q ) = x }'
FIBL = 'sum_ r e. %s %s' % (SXF, ABS2(DS('x', '( Y ` r )')))
FI1 = ITG(T1, ABS2(DS('x', 't'))); FI2 = ITG(T1, ABS2(DS('x', 't', A=ADM)))
st('mvdfam1', '( ( %s /\\ x e. %s ) -> ( ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ %s <_ ( ( 2 x. %s ) + %s ) ) )' % (
    HFX, DB(), FIBL, FI1, FI2, FIBL, FI1, FI2))
st('mvdfam', '( ( %s /\\ %s /\\ ( %s /\\ %s ) ) -> sum_ r e. S %s <_ ( ( ; ; 2 0 0 x. ( M + ( N x. ( T + 1 ) ) ) ) x. %s ) )' % (
    HLV, HFAM, RNGF, SEPF, ABS2(DS('( K ` r )', '( Y ` r )')), SLA2))
LVB = '( ( %s /\\ 1 <_ M ) /\\ ( %s /\\ ( V e. RR /\\ 0 <_ V ) ) /\\ ( %s /\\ %s ) )' % (HLV, HFAM, RNGF, SEPF)
st('mvlvm', '( ( %s /\\ A. a e. S V <_ ( abs ` %s ) ) -> '
   '( ( # ` S ) x. ( V ^ 2 ) ) <_ ( ( ( ; ; 3 0 0 x. ( ( 1 + ( log ` M ) ) ^ 2 ) ) x. ( M + ( N x. T ) ) ) x. %s ) )' % (
    LVB, DS('( K ` a )', '( Y ` a )'), SA2))

def gramcheck(labels):
    out = {}
    for lab in labels:
        p = os.path.join('worksheets', 'mvg_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=mvg_%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for n, h in HYPS.get(lab, []):
                f.write('%s::? |- %s\n' % (n.split('.')[-1], h))
            f.write('qed::ax-1 |- %s\n$)\n' % STATEMENTS[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'unify', p], capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = [l for l in txt.split('\n') if 'grammar' in l.lower() or 'parse' in l.lower()]
        os.remove(p)
    return out



# ------------------------------------------------------------------ worksheet helpers
import z4blib as _Z4B
from z4blib import a1, ap, parts, J, eqt, eqc, body, fvmd, qedlast, _lhs_rhs
from z4blib import st as dst
from tm import W
import cl as _cl
from cl import Closure, ClosureError, lift, formula_of, strip_ante, split_imp
import lin as _lin
from lin import linarith, nlinarith, lineq
_lin.FASTPATH = True
_orig_cl_init = _cl.Closure.__init__


def _cl_init(self, w, ante, leaves=None, parent=None, extra=None):
    _orig_cl_init(self, w, ante, leaves, parent, extra)
    self.initleaves = set((leaves or {}).keys())


_cl.Closure.__init__ = _cl_init
for _k, _v in {('fv:sin', 'RR'): [('resincld', 'd', [('RR', 0)])], ('fv:sin', 'CC'): [('sincld', 'd', [('CC', 0)])],
               ('fv:cos', 'RR'): [('recoscld', 'd', [('RR', 0)])], ('fv:cos', 'CC'): [('coscld', 'd', [('CC', 0)])],
               ('fv:Re', 'RR'): [('recld', 'd', [('CC', 0)])], ('fv:Im', 'RR'): [('imcld', 'd', [('CC', 0)])],
               ('fv:*', 'CC'): [('cjcld', 'd', [('CC', 0)])]}.items():
    _cl.MEM_RULES.setdefault(_k, _v)


def ringeq(w, ante, lhs, rhs, cl, name=None):
    """( ante -> lhs = rhs ) for two polynomial expressions over CC (atoms from cl, literal
    denominators allowed), by normal forms; with denominators, both sides are scaled by their lcm
    and mulcand cancels it"""
    N = _lin.Normalizer(w, ante, cl)
    old = _lin.MAXDEG
    _lin.MAXDEG = max(old, 12)
    try:
        return _ringeq(w, ante, lhs, rhs, cl, N, name)
    finally:
        _lin.MAXDEG = old


def _ringeq(w, ante, lhs, rhs, cl, N, name):
    lv = tuple(set(cl.leaves) | set(getattr(cl, 'initleaves', ())) | set(cl.atoms))
    a, b = _lin.parse(lhs, True, lv), _lin.parse(rhs, True, lv)
    d = 1
    for q in list(_lin.denominators(a)) + list(_lin.denominators(b)):
        d = _lin.lcm(d, q)
    if d == 1:
        s1, v1 = N.nf(a, 1); s2, v2 = N.nf(b, 1)
        if v1.text() != v2.text():
            raise ValueError('ringeq: %s  vs  %s' % (v1.text(), v2.text()))
        return w.s([s1, s2], 'eqtr4d', '( %s -> %s = %s )' % (ante, lhs, rhs), name=name)
    from fractions import Fraction
    s1, v1 = N.nf(a, Fraction(d)); s2, v2 = N.nf(b, Fraction(d))
    if v1.text() != v2.text():
        raise ValueError('ringeq: %s  vs  %s' % (v1.text(), v2.text()))
    D = _lin.num.lit_text(Fraction(d))
    e = w.s([s1, s2], 'eqtr4d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (ante, D, lhs, D, rhs))
    bi = w.s([cl.mem(lhs, 'CC'), cl.mem(rhs, 'CC'), cl.mem(D, 'CC'), cl.ne0(D)], 'mulcand',
             '( %s -> ( ( %s x. %s ) = ( %s x. %s ) <-> %s = %s ) )' % (ante, D, lhs, D, rhs, lhs, rhs))
    return w.s([e, bi], 'mpbid', '( %s -> %s = %s )' % (ante, lhs, rhs), name=name)



def ringeqp(w, ante, lhs, rhs, cl, name=None):
    """ringeq after writing every small integer power of either side out as a product
    (repeatedly, so that powers inside powers are expanded too)"""
    def expand(t):
        steps = []
        for _ in range(6):
            rules = _lin.powrules(w, ante, [t], cl)
            if not rules:
                break
            s_, t2 = _lin.powconv(w, ante, t, rules, gen=w.g)
            steps.append((s_, t2)); t = t2
        return steps, t
    ls, L2 = expand(lhs)
    rs, R2 = expand(rhs)
    cur = ringeq(w, ante, L2, R2, cl)            # L2 = R2
    # lhs = L2
    for s_, t2 in reversed(ls):
        pass
    left = lhs; chainL = None
    for s_, t2 in ls:
        chainL = s_ if chainL is None else w.s([chainL, s_], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, t2))
    if chainL is not None:
        cur = w.s([chainL, cur], 'eqtrd', '( %s -> %s = %s )' % (ante, lhs, R2))
    chainR = None
    for s_, t2 in rs:
        chainR = s_ if chainR is None else w.s([chainR, s_], 'eqtrd', '( %s -> %s = %s )' % (ante, rhs, t2))
    if chainR is not None:
        cur = w.s([cur, chainR], 'eqtr4d', '( %s -> %s = %s )' % (ante, lhs, rhs))
    return cur


def ltle(w, ante, cl, step):
    """( ante -> A <_ B ) from step ( ante -> A < B ), with the two memberships supplied"""
    f = body(w, step, ante)
    A, rel, B = _lhs_rhs(f)
    assert rel == '<', f
    return w.s([cl.mem(A, 'RR'), cl.mem(B, 'RR'), step], 'ltled', '( %s -> %s <_ %s )' % (ante, A, B))

_LABELS = None


def labels():
    global _LABELS
    if _LABELS is None:
        import re as _re
        import mm as _MM
        _LABELS = set()
        for p in (_MM.SETMM, _MM.MAINDB, _MM.DB):
            _LABELS |= set(_re.findall(r"^\s*(\S+)\s+\$[ape]\s", open(p).read(), _re.M))
    return _LABELS


def checkrefs(w, again=True):
    """labels cited by W's steps that exist nowhere (typos), as a list"""
    global _LABELS
    L = labels(); bad = []
    names = set(l.split(':', 1)[0] for l in w.lines)
    for l in w.lines:
        f = l.split(' |- ')[0] if ' |- ' in l else l
        parts_ = f.split(':')
        if len(parts_) >= 3:
            ref = parts_[2].strip()
            if ref and ref not in L and ref not in names and not ref.startswith(w.label + '.'):
                bad.append(ref)
    if bad and again:
        _LABELS = None
        return checkrefs(w, False)
    return sorted(set(bad)) + ['MATHBOX:' + r for r in mboxrefs(w)]


_MB = None


def mboxrefs(w):
    global _MB
    import mm as _MM
    if _MB is None:
        _MB = _MM.mathbox_labels(open(_MM.SETMM).read()) - set(_MM.MATHBOX_OK)
    out = set()
    for l in w.lines:
        f = l.split(' |- ')[0] if ' |- ' in l else l
        p_ = f.split(':')
        if len(p_) >= 3 and p_[2].strip() in _MB:
            out.add(p_[2].strip())
    return sorted(out)


# ------------------------------------------------------------------ continuity of mapping expressions
CNFUN = {'sin': 'sincn', 'cos': 'coscn', 'exp': 'efcn', '*': 'cjcncf'}


def _occurs(v, E):
    return v in E.split()


class CN:
    """continuity of ( v e. DOM |-> E ) in ( DOM -cn-> CC ) under ANTE, by structure.
    cl0: Closure under ANTE (constants); clv: Closure under ( ANTE /\\ v e. DOM ) (nonzero
    denominators); domss: step ( ante -> DOM C_ CC )."""
    def __init__(self, w, ante, v, dom, domss, cl0, clv, known=None):
        self.w, self.ante, self.v, self.dom, self.domss, self.cl0, self.clv = w, ante, v, dom, domss, cl0, clv
        self.memo = dict(known or {})

    def mp(self, E):
        return '( %s e. %s |-> %s )' % (self.v, self.dom, E)

    def goal(self, E, T='CC'):
        return '( %s -> %s e. ( %s -cn-> %s ) )' % (self.ante, self.mp(E), self.dom, T)

    def __call__(self, E):
        if E in self.memo:
            return self.memo[E]
        r = self._go(E)
        self.memo[E] = r
        return r

    def _go(self, E):
        w, A = self.w, self.ante
        ccss = a1(w, A, 'ssid', 'CC C_ CC')
        if not _occurs(self.v, E):
            return w.s([self.cl0.mem(E, 'CC'), self.domss, ccss, w.inst('cncfmptc')], 'syl3anc', self.goal(E))
        if E == self.v:
            return w.s([self.domss, ccss, w.inst('cncfmptid')], 'syl2anc', self.goal(E))
        from cl import head
        h = head(E)
        if h[0] in ('add', 'sub', 'mul'):
            ref = {'add': 'addcncf', 'sub': 'subcncf', 'mul': 'mulcncf'}[h[0]]
            return w.s([self(h[1]), self(h[2])], ref, self.goal(E))
        if h[0] == 'neg':
            return self._neg(E, h[1])
        if h[0] == 'fv' and h[1] in CNFUN:
            f = a1(w, A, CNFUN[h[1]], '%s e. ( CC -cn-> CC )' % h[1])
            return w.s([f, self(h[2])], 'cncfmpt1f', self.goal(E))
        if h[0] == 'fv' and h[1] in ('abs', 'Re', 'Im'):
            r = {'abs': 'abscncf', 'Re': 'recncf', 'Im': 'imcncf'}[h[1]]
            s = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an',
                    '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
            c = w.s([s, w.s([], r, '%s e. ( CC -cn-> RR )' % h[1])], 'sselii', '%s e. ( CC -cn-> CC )' % h[1])
            return w.s([w.s([c], 'a1i', '( %s -> %s e. ( CC -cn-> CC ) )' % (A, h[1])), self(h[2])], 'cncfmpt1f', self.goal(E))
        if h[0] == 'exp' and h[2] == '2':
            X = h[1]
            Av = '( %s /\\ %s e. %s )' % (A, self.v, self.dom)
            sq = dst(w, Av, [self.clv.mem(X, 'CC')], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (X, X, X))
            eq = dst(w, A, [sq], 'mpteq2dva', '%s = %s' % (self.mp(E), self.mp('( %s x. %s )' % (X, X))))
            m = self('( %s x. %s )' % (X, X))
            return dst(w, A, [eq, m], 'eqeltrd', '%s e. ( %s -cn-> CC )' % (self.mp(E), self.dom))
        if h[0] == 'div':
            X, Y = h[1], h[2]
            Av = '( %s /\\ %s e. %s )' % (A, self.v, self.dom)
            yc = self.clv.mem(Y, 'CC'); yn = self.clv.ne0(Y)
            ynz = dst(w, Av, [yc, yn], 'eldifsnd', '%s e. ( CC \\ { 0 } )' % Y)
            fm = dst(w, A, [ynz], 'fmptd', '%s : %s --> ( CC \\ { 0 } )' % (self.mp(Y), self.dom))
            dss = w.s([w.s([], 'difss', '( CC \\ { 0 } ) C_ CC')], 'a1i', '( %s -> ( CC \\ { 0 } ) C_ CC )' % A)
            bi = w.s([dss, self(Y), w.inst('cncfcdm')], 'syl2anc',
                     '( %s -> ( %s e. ( %s -cn-> ( CC \\ { 0 } ) ) <-> %s : %s --> ( CC \\ { 0 } ) ) )' % (A, self.mp(Y), self.dom, self.mp(Y), self.dom))
            yn0 = w.s([fm, bi], 'mpbird', '( %s -> %s e. ( %s -cn-> ( CC \\ { 0 } ) ) )' % (A, self.mp(Y), self.dom))
            return w.s([self(X), yn0], 'divcncf', self.goal(E))
        raise ClosureError('CN: cannot handle ' + E)

    def _neg(self, E, X):
        w, A = self.w, self.ante
        Av = '( %s /\\ %s e. %s )' % (A, self.v, self.dom)
        m = dst(w, Av, [self.clv.mem(X, 'CC')], 'mulm1d', '( -u 1 x. %s ) = -u %s' % (X, X))
        eq = dst(w, A, [m], 'mpteq2dva', '%s = %s' % (self.mp('( -u 1 x. %s )' % X), self.mp(E)))
        c = self('( -u 1 x. %s )' % X)
        return dst(w, A, [eq, c], 'eqeltrrd', '%s e. ( %s -cn-> CC )' % (self.mp(E), self.dom))


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])
