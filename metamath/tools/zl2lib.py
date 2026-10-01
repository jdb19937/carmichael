"""Sortie ZL2 helpers (Route Z: LConvexity.lean, the convexity bound CVXH).

STATEMENTS / HYPS / ORDER are the frozen statements of ZL2-blueprint.md, one
place.  `MM_DB=sorties/zl2.mm python3 tools/zl2lib.py [LABEL...]` grammar-checks
them (mmj2 unify on a bare `qed` worksheet).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from c7lib import *                        # W, a1, runh, ... (C5/C4 step patterns)
from c0lib import hyp, runh
import z6alib as Z6A                       # the consumer's macros: CVXB, CVXH, HPZ, OMG

# ------------------------------------------------------------------ objects
RE = lambda z: '( Re ` %s )' % z
IM = lambda z: '( Im ` %s )' % z
AIM = lambda z: '( abs ` ( Im ` %s ) )' % z
STRIP = lambda a, b: "( `' Re \" ( %s [,] %s ) )" % (a, b)
HOL = lambda F, D: '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (F, D, D, F)
HALF = '( 1 / 2 )'
NHALF = '-u ( 1 / 2 )'
STR = STRIP(NHALF, '2')                                   # the strip -1/2 <_ Re <_ 2
GRWB = lambda F, D, z='z', K='K', B='B': ('( ( %s e. RR+ /\\ %s e. RR /\\ 0 <_ %s ) /\\ A. %s e. %s ( abs ` ( %s ` %s ) ) <_ ( %s x. ( exp ` ( %s x. ( abs ` ( Im ` %s ) ) ) ) ) )'
                                          % (K, B, B, z, D, F, z, K, B, z))
QT = lambda z, N='N': '( %s x. ( ( abs ` ( Im ` %s ) ) + 2 ) )' % (N, z)       # N ( |Im z| + 2 )
QL = lambda z, N='N': '( %s x. ( ( abs ` ( Im ` %s ) ) + 3 ) )' % (N, z)       # N ( |Im z| + 3 )
EXPO = lambda z: 'if ( 1 <_ ( Re ` %s ) , 0 , ( ( 1 - ( Re ` %s ) ) / 2 ) )' % (z, z)   # max ( ( 1 - sigma ) / 2 , 0 )
CXB = lambda z, N='N': '( ( %s ^c %s ) x. ( log ` %s ) )' % (QT(z, N), EXPO(z), QL(z, N))   # the convexity shape
RGT = lambda F='F', A='A', z='z': ('A. %s e. CC ( ( 1 < ( Re ` %s ) /\\ ( Re ` %s ) <_ 2 ) -> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 1 + ( 1 / ( ( Re ` %s ) - 1 ) ) ) ) )'
                                  % (z, z, z, F, z, A, z))
LFTB = lambda z, A='A', N='N': ('( ( ( ; 1 2 x. %s ) x. ( 1 + ( 1 / -u ( Re ` %s ) ) ) ) x. ( %s ^c ( ( 1 / 2 ) - ( Re ` %s ) ) ) )'
                                % (A, z, QT(z, N), z))
LFT = lambda F='F', A='A', N='N', z='z': ('A. %s e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) < 0 ) -> ( abs ` ( %s ` %s ) ) <_ %s )'
                                          % (z, z, z, F, z, LFTB(z, A, N)))
SRNG2 = lambda S='S': '( %s e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 2 ) )' % (S, S, S)
# the hypotheses of the generic convexity theorem (norm_LFunction_le_convexity')
HCVX = ('( ( ( N e. NN /\\ A e. RR+ ) /\\ ( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U ) ) /\\ ( %s /\\ ( %s /\\ %s ) ) )'
        % (STR, GRWB('F', STR), RGT(), LFT()))
C5E = '; ; ; ; ; 1 0 0 0 0 0'
# the normalized Phragmen-Lindeloef lemma: line bound at Re = E
PLNL = lambda E: ('A. z e. %s ( ( Re ` z ) = %s -> ( ( ( abs ` ( F ` z ) ) x. ( exp ` ( ( ( %s - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` z ) - ( Im ` W ) ) ^ 2 ) ) ) ) '
                  'x. ( exp ` ( ( %s - P ) x. C ) ) ) <_ Q )' % (STRIP('X', 'Y'), E, E, E))
NRM = lambda z: '( ( exp ` ( ( %s - W ) ^ 2 ) ) x. ( exp ` ( ( %s - P ) x. C ) ) )' % (z, z)
GN = '( z e. D |-> ( ( F ` z ) x. %s ) )' % NRM('z')          # the normalized function
PLNA = ('( ( ( ( X e. RR /\\ Y e. RR ) /\\ ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) ) /\\ %s ) /\\ '
        '( ( W e. %s /\\ ( P e. RR /\\ C e. RR ) /\\ Q e. RR+ ) /\\ ( %s /\\ %s ) ) )'
        % (STRIP('X', 'Y'), GRWB('F', STRIP('X', 'Y')), STRIP('X', 'Y'), PLNL('X'), PLNL('Y')))
PLNH = ('( ( ( X e. RR /\\ Y e. RR ) /\\ ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) ) /\\ ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) )'
        % STRIP('X', 'Y'))
# the Gamma-factor strip [-1/2,0]
STRG = STRIP(NHALF, '0')
GINT = ('( ( ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) /\\ %s ) /\\ '
        '( A. z e. CC ( ( Re ` z ) = -u ( 1 / 2 ) -> ( abs ` ( F ` z ) ) <_ ( 3 x. ( 2 + ( abs ` z ) ) ) ) /\\ '
        'A. z e. CC ( ( Re ` z ) = 0 -> ( abs ` ( F ` z ) ) <_ ( 3 x. ( ( ( abs ` ( Im ` z ) ) + 2 ) ^c ( 1 / 2 ) ) ) ) ) )'
        % (STRG, GRWB('F', STRG)))
GQ = lambda z: '( ( ( abs ` ( Im ` %s ) ) + 2 ) ^c ( ( 1 / 2 ) - ( Re ` %s ) ) )' % (z, z)
GCF = lambda z: '( 2 x. ( ( 2 x. _pi ) ^c -u ( 1 - %s ) ) )' % z     # Gamma_C ( 1 - z ) / Gamma ( 1 - z )
# the functional-equation form of the left edge (LFunction_left_even / _odd, generic)
FEQ = ('A. z e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) < 0 ) -> ( F ` z ) = ( ( ( N ^c ( ( 1 / 2 ) - z ) ) x. E ) x. ( ( Q ` z ) x. ( G ` ( 1 - z ) ) ) ) )')
# the Gamma-factor bound and the right-edge bound carry the typing of the values ( Q ` z ), ( G ` z )
# in their bodies (Lean's Q, G are functions CC -> CC; a set.mm class F has ( F ` z ) e. CC only by hypothesis)
QBND = ('A. z e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) <_ 0 ) -> ( ( Q ` z ) e. CC /\\ ( abs ` ( Q ` z ) ) <_ ( ; 1 2 x. %s ) ) )' % GQ('z'))
GRGT = 'A. z e. CC ( 1 < ( Re ` z ) -> ( ( G ` z ) e. CC /\\ ( abs ` ( G ` z ) ) <_ ( A x. ( 1 + ( 1 / ( ( Re ` z ) - 1 ) ) ) ) ) )'
DCN = '( Base ` ( DChr ` N ) )'

STATEMENTS = {}
HYPS = {}

# ================================================================== section A: helpers (LConvexity 45-102)
STATEMENTS['zl2e4'] = '( exp ` 4 ) <_ ; 8 1'
STATEMENTS['zl2gau'] = '( V e. RR -> ( ( 1 + ( abs ` V ) ) x. ( exp ` -u ( V ^ 2 ) ) ) <_ 3 )'
STATEMENTS['zl2ngau'] = ('( ( Z e. CC /\\ W e. CC ) -> ( abs ` ( exp ` ( ( Z - W ) ^ 2 ) ) ) = '
                         '( exp ` ( ( ( ( Re ` Z ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` Z ) - ( Im ` W ) ) ^ 2 ) ) ) )')
STATEMENTS['zl2npow'] = '( ( Z e. CC /\\ C e. RR ) -> ( abs ` ( exp ` ( Z x. C ) ) ) = ( exp ` ( ( Re ` Z ) x. C ) ) )'
STATEMENTS['zl2tab'] = '( ( Y e. RR /\\ V e. RR ) -> ( ( abs ` Y ) + 2 ) <_ ( ( ( abs ` V ) + 2 ) x. ( 1 + ( abs ` ( Y - V ) ) ) ) )'
# ================================================================== section B: the root number (LConvexity 104-278; Gauss sums are ZF4's)
STATEMENTS['zl2rtn'] = ('( ( ( N e. NN /\\ X e. %s ) /\\ ( ( N DChrCond X ) = N /\\ K e. NN0 ) ) -> '
                        '( abs ` ( ( N DChrGS X ) / ( ( _i ^ K ) x. ( N ^c ( 1 / 2 ) ) ) ) ) = 1 )' % DCN)
# ================================================================== section E: the growth condition (LConvexity 478-516)
STATEMENTS['zl2grw'] = ('( ( ( P e. RR /\\ 0 <_ P ) /\\ ( U e. RR /\\ 0 <_ U ) ) -> '
                        '( P x. ( ( 4 + U ) ^ 3 ) ) <_ ( ( ; 6 4 x. P ) x. ( exp ` U ) ) )')
# ================================================================== section P: Phragmen-Lindeloef with the Gaussian and power normalizers
STATEMENTS['zl2plnh'] = '( %s -> %s )' % (PLNH, HOL(GN, 'D'))
STATEMENTS['zl2plnv'] = ('( ( ( W e. CC /\\ ( P e. RR /\\ C e. RR ) ) /\\ ( Z e. CC /\\ V e. CC ) ) -> ( abs ` ( V x. %s ) ) = '
                         '( ( ( abs ` V ) x. ( exp ` ( ( ( ( Re ` Z ) - ( Re ` W ) ) ^ 2 ) - ( ( ( Im ` Z ) - ( Im ` W ) ) ^ 2 ) ) ) ) x. ( exp ` ( ( ( Re ` Z ) - P ) x. C ) ) ) )'
                         % NRM('Z'))
STATEMENTS['zl2plng'] = ('( ( ( ( X e. RR /\\ Y e. RR ) /\\ ( W e. %s /\\ ( P e. RR /\\ C e. RR ) ) ) /\\ Z e. %s ) -> '
                         '( abs ` %s ) <_ ( exp ` ( ( ( Y - X ) ^ 2 ) + ( ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` P ) ) ) x. ( abs ` C ) ) ) ) )'
                         % (STRIP('X', 'Y'), STRIP('X', 'Y'), NRM('Z')))
STATEMENTS['zl2pln'] = '( %s -> ( ( abs ` ( F ` W ) ) x. ( exp ` ( ( ( Re ` W ) - P ) x. C ) ) ) <_ Q )' % PLNA
# ================================================================== section F: the interpolated Gamma-factor bound, generic (LConvexity 518-736)
STATEMENTS['zl2gint'] = ('( ( %s /\\ ( W e. CC /\\ ( -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 0 ) ) ) -> ( abs ` ( F ` W ) ) <_ ( ; 3 4 x. %s ) )'
                         % (GINT, GQ('W')))
# ================================================================== section G: the left edge, generic (LConvexity 738-948)
STATEMENTS['zl2gcf'] = ('( ( ( Z e. CC /\\ ( -u ( 1 / 2 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ 0 ) ) /\\ ( V e. CC /\\ ( abs ` V ) <_ ( ; 3 4 x. %s ) ) ) -> '
                        '( abs ` ( %s x. V ) ) <_ ( ; 1 2 x. %s ) )' % (GQ('Z'), GCF('Z'), GQ('Z')))
STATEMENTS['zl2left'] = ('( ( ( ( N e. NN /\\ A e. RR ) /\\ ( E e. CC /\\ ( abs ` E ) = 1 ) ) /\\ ( %s /\\ ( %s /\\ %s ) ) ) -> %s )'
                         % (FEQ, QBND, GRGT, LFT()))
# ================================================================== section H: the convexity bound, generic (LConvexity 950-1297)
STATEMENTS['zl2cvx'] = ('( ( %s /\\ %s ) -> ( abs ` ( F ` S ) ) <_ ( ( %s x. A ) x. %s ) )' % (HCVX, SRNG2(), C5E, CXB('S')))
STATEMENTS['zl2cvx1'] = ('( ( %s /\\ ( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) -> '
                         '( abs ` ( F ` S ) ) <_ ( ( %s x. A ) x. ( ( %s ^c ( ( 1 - ( Re ` S ) ) / 2 ) ) x. ( log ` %s ) ) ) )'
                         % (HCVX, C5E, QT('S'), QL('S')))

# ------------------------------------------------------------------ section H helpers: the parameters of the convexity proof
# (LConvexity 968-1010: D = N ( |t| + 2 ), M = N ( |t| + 3 ), L = 1 + log M, sigma_R = 1 + 1/L, sigma_L = -1/L,
#  W = sigma_R - sigma_L, b = 108 D ^ ( 1/2 ), c = log b / W), generic in T = |t|, D and L
DDT = '( N x. ( T + 2 ) )'
MMT = '( N x. ( T + 3 ) )'
LLT = '( 1 + ( log ` %s ) )' % MMT
SRL = '( 1 + ( 1 / L ) )'
SLL = '-u ( 1 / L )'
WWL = '( %s - %s )' % (SRL, SLL)
BB = lambda D: '( ; ; 1 0 8 x. ( %s ^c ( 1 / 2 ) ) )' % D
CCL = lambda D: '( ( log ` %s ) / %s )' % (BB(D), WWL)
LLS = '( 1 + ( log ` %s ) )' % QL('S')                        # L at t = Im S
SRLS = SRL.replace(' L )', ' %s )' % LLS)                     # sigma_R at t = Im S
STATEMENTS['zl2cvxa'] = ('( ( N e. NN /\\ T e. RR /\\ 0 <_ T ) -> ( ( ( %s e. RR+ /\\ 1 <_ %s ) /\\ ( %s e. RR+ /\\ 3 <_ %s ) /\\ %s <_ %s ) /\\ '
                          '( ( 1 <_ ( log ` %s ) /\\ ( %s e. RR+ /\\ 2 <_ %s ) ) /\\ ( log ` %s ) <_ %s ) ) )'
                          % (DDT, DDT, MMT, MMT, DDT, MMT, MMT, LLT, LLT, DDT, LLT))
STATEMENTS['zl2cvxb'] = ('( ( ( D e. RR+ /\\ 1 <_ D ) /\\ ( L e. RR+ /\\ 2 <_ L ) /\\ ( log ` D ) <_ L ) -> '
                          '( ( ( D ^c ( 1 / L ) ) <_ 3 /\\ ( 1 <_ ( D ^c ( 1 / 2 ) ) /\\ ( %s e. RR+ /\\ 1 <_ %s ) ) ) /\\ '
                          '( ( ( 1 / L ) <_ ( 1 / 2 ) /\\ ( %s e. RR+ /\\ %s <_ 2 ) ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ ( exp ` ( ( %s - %s ) x. %s ) ) = ( 1 / %s ) ) ) ) )'
                          % (BB('D'), BB('D'), WWL, WWL, CCL('D'), CCL('D'), SLL, SRL, CCL('D'), BB('D')))
STATEMENTS['zl2cvxm'] = ('( ( ( ( G e. RR /\\ 0 <_ G ) /\\ ( ( X e. RR /\\ 0 <_ X ) /\\ ( Y e. RR /\\ ( 0 <_ Y /\\ Y <_ 3 ) ) ) ) /\\ '
                          '( ( ( V e. RR /\\ 0 <_ V ) /\\ ( H e. RR /\\ ( 0 <_ H /\\ ( V x. H ) <_ 3 ) ) ) /\\ ( ( P e. RR /\\ 0 <_ P ) /\\ ( ; ; 1 0 8 x. ( X x. P ) ) = 1 ) ) ) -> '
                          '( ( ( G x. ( ( X x. Y ) x. V ) ) x. ( ; 8 1 x. H ) ) x. P ) <_ ( ( ; 2 7 / 4 ) x. G ) )')
GAUS = lambda E: '( exp ` ( ( ( %s - ( Re ` S ) ) ^ 2 ) - ( ( ( Im ` Z ) - ( Im ` S ) ) ^ 2 ) ) )' % E
Q81 = '( ( ; 8 1 x. A ) x. ( 1 + L ) )'
STATEMENTS['zl2cvxr'] = ('( ( ( ( ( A e. RR+ /\\ ( L e. RR+ /\\ 2 <_ L ) ) /\\ ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ %s ) ) ) /\\ ( C e. RR /\\ %s ) ) /\\ ( ( Z e. CC /\\ ( F ` Z ) e. CC ) /\\ ( Re ` Z ) = %s ) ) -> '
                          '( ( ( abs ` ( F ` Z ) ) x. %s ) x. ( exp ` ( ( %s - %s ) x. C ) ) ) <_ %s )' % (SRL, RGT(), SRL, GAUS(SRL), SRL, SRL, Q81))
STATEMENTS['zl2cvxl'] = ('( ( ( ( ( N e. NN /\\ A e. RR+ ) /\\ ( L e. RR+ /\\ 2 <_ L ) ) /\\ ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ ( 3 / 2 ) ) ) ) /\\ '
                          '( ( ( C e. RR /\\ ( exp ` ( ( %s - %s ) x. C ) ) = ( 1 / %s ) ) /\\ ( %s ^c ( 1 / L ) ) <_ 3 ) /\\ ( %s /\\ ( ( Z e. CC /\\ ( F ` Z ) e. CC ) /\\ ( Re ` Z ) = %s ) ) ) ) -> '
                          '( ( ( abs ` ( F ` Z ) ) x. %s ) x. ( exp ` ( ( %s - %s ) x. C ) ) ) <_ %s )'
                          % (SLL, SRL, BB(QT('S')), QT('S'), LFT(), SLL, GAUS(SLL), SLL, SRL, Q81))
STATEMENTS['zl2cvxu'] = ('( ( ( ( A e. RR+ /\\ ( D e. RR+ /\\ 1 <_ D ) ) /\\ ( ( L e. RR+ /\\ 2 <_ L ) /\\ ( D ^c ( 1 / L ) ) <_ 3 ) ) /\\ '
                          '( ( S e. CC /\\ ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ %s ) ) /\\ ( V e. RR /\\ ( V x. ( exp ` ( ( ( Re ` S ) - %s ) x. %s ) ) ) <_ %s ) ) ) -> '
                          'V <_ ( ( ; ; ; ; 2 6 2 4 4 x. A ) x. ( ( 1 + L ) x. ( D ^c %s ) ) ) )' % (SRL, SRL, CCL('D'), Q81, EXPO('S')))
STATEMENTS['zl2cvxpl'] = ('( ( ( %s /\\ %s ) /\\ ( Re ` S ) <_ %s ) -> ( abs ` ( F ` S ) ) <_ ( ( %s x. A ) x. %s ) )' % (HCVX, SRNG2(), SRLS, C5E, CXB('S')))
STATEMENTS['zl2cvxd'] = ('( ( ( %s /\\ %s ) /\\ %s < ( Re ` S ) ) -> ( abs ` ( F ` S ) ) <_ ( ( %s x. A ) x. %s ) )' % (HCVX, SRNG2(), SRLS, C5E, CXB('S')))

ORDER = ['zl2e4', 'zl2gau', 'zl2ngau', 'zl2npow', 'zl2tab', 'zl2rtn', 'zl2grw',
         'zl2plnh', 'zl2plnv', 'zl2plng', 'zl2pln', 'zl2gint', 'zl2gcf', 'zl2left',
         'zl2cvxa', 'zl2cvxb', 'zl2cvxm', 'zl2cvxr', 'zl2cvxl', 'zl2cvxu', 'zl2cvxpl', 'zl2cvxd', 'zl2cvx', 'zl2cvx1']


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('zl2g' + lab, 'grammar check of %s' % lab)
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


def run(w):
    if HYPS.get(w.label):
        return runh(w)
    return w.run()




# ------------------------------------------------------------------ step helpers
from cl import Closure
import lin as LIN
LIN.FASTPATH = True


def E(w, ante, ref, hyps, l, r):
    return w.s(hyps, ref, '( %s -> %s = %s )' % (ante, l, r))


def D(w, ante, ref, hyps, concl, name=None):
    """deduction step ( ante -> concl )"""
    return w.s(hyps, ref, '( %s -> %s )' % (ante, concl), name=name)


def chain(w, ante, terms, steps, name=None):
    """( ante -> t0 = tn ) from steps[i]: ( ante -> t_i = t_(i+1) ) (or ('r', st) reversed)"""
    cur = None
    for i, st in enumerate(steps):
        a, b = terms[i], terms[i + 1]
        if isinstance(st, tuple):
            st = w.s([st[1]], 'eqcomd', '( %s -> %s = %s )' % (ante, a, b))
        if cur is None:
            cur = st if (len(steps) > 1 or name is None) else w.s([st], 'idi', '( %s -> %s = %s )' % (ante, a, b), name=name)
        else:
            last = i == len(steps) - 1
            cur = w.s([cur, st], 'eqtrd', '( %s -> %s = %s )' % (ante, terms[0], b), name=(name if last else None))
    return cur


def efle_(w, ante, a, b, ar, br, le):
    """( ante -> ( exp ` a ) <_ ( exp ` b ) ) from le: ( ante -> a <_ b )"""
    bi = w.s([ar, br, w.inst('efle')], 'syl2anc', '( %s -> ( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) ) )' % (ante, a, b, a, b))
    return w.s([le, bi], 'mpbid', '( %s -> ( exp ` %s ) <_ ( exp ` %s ) )' % (ante, a, b))


def efadd_(w, ante, a, b, ac, bc):
    """( ante -> ( exp ` ( a + b ) ) = ( ( exp ` a ) x. ( exp ` b ) ) )"""
    return w.s([ac, bc, w.inst('efadd')], 'syl2anc', '( %s -> ( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) ) )' % (ante, a, b, a, b))


def go(w, only):
    if only and w.label not in only:
        return True
    if os.environ.get('ZL2_WRITE'):          # write the worksheet only (unify it by hand: tools/mm.py unify)
        w.write(); print('WROTE', w.label, len(w.lines), 'lines'); return True
    return run(w)


# helper (section P): an entire function restricted to an open set
STATEMENTS['zl2hent'] = ('( ( ( ( z e. CC |-> A ) e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D ( z e. CC |-> A ) ) ) /\\ D e. ( TopOpen ` CCfld ) ) -> '
                         '( ( z e. D |-> A ) e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D ( z e. D |-> A ) ) ) )')
ORDER.insert(ORDER.index('zl2plnh'), 'zl2hent')


# ================================================================== the end theorem: CVXH at ( N DChrLF X ) (ZL1's CVXHX)
import zl1lib as ZL1
CVXHX = ZL1.CVXHX
NXL = ZL1.NX
MC = '( N DChrCond X )'                                   # the conductor
YP = '( N DChrPrim X )'                                   # the primitive character inducing X
LMC = '( ZRHom ` ( Z/nZ ` %s ) )' % MC
CY = '( a e. NN |-> ( %s ` ( %s ` a ) ) )' % (YP, LMC)
CYB = '( a e. NN |-> ( ( ( invg ` ( DChr ` %s ) ) ` %s ) ` ( %s ` a ) ) )' % (MC, YP, LMC)
RP = 'if ( X = ( 0g ` ( DChr ` N ) ) , 1 , 0 )'          # the residue of the primitive L-function
SERY = ('A. z e. CC ( ( 1 < ( Re ` z ) /\\ ( Re ` z ) <_ 2 ) -> ( ( F ` z ) + ( %s / ( z - 1 ) ) ) = sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u z ) ) )'
        % (RP, CY))
FEY = ('A. z e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` z ) /\\ ( Re ` z ) < 0 ) -> ( ( F ` z ) + ( %s / ( z - 1 ) ) ) = '
       '( ( ( %s ^c ( ( 1 / 2 ) - z ) ) x. T ) x. ( ( Q ` z ) x. sum_ k e. NN ( ( %s ` k ) x. ( k ^c -u ( 1 - z ) ) ) ) ) )'
       % (RP, MC, CYB))
PCONT = ('( ( ( F e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D F ) /\\ %s C_ U ) /\\ %s ) /\\ ( %s /\\ ( ( T e. CC /\\ ( abs ` T ) = 1 ) /\\ ( %s /\\ %s ) ) ) )'
         % (STR, GRWB('F', STR), SERY, FEY, QBND))
STATEMENTS['zl2cvxe'] = '( ( %s /\\ %s ) -> %s )' % (NXL, PCONT, CVXHX)
ORDER.append('zl2cvxe')


def ele3(w):
    """closed step: _e <_ 3 (egt2lt3; ege2le3 carries $e hypotheses)"""
    lt = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')
    return w.s([w.s([], 'ere', '_e e. RR'), w.s([], '3re', '3 e. RR'), lt], 'ltleii', '_e <_ 3')


def e1le3(w):
    """closed step: ( exp ` 1 ) <_ 3"""
    return w.s([w.s([], 'df-e', '_e = ( exp ` 1 )'), ele3(w)], 'eqbrtrri', '( exp ` 1 ) <_ 3')


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])


# ================================================================== the end theorem's helpers (designed on reach: HANDOFF section 6)
DIV = lambda K: '{ x e. NN | x || %s }' % K
CXN = ZL1.CX                                              # ( a e. NN |-> ( X ` ( LH ` a ) ) ), ZL1's character on NN
LHN = '( ZRHom ` ( Z/nZ ` N ) )'
CFB1 = lambda A: '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (A, A)
LAVB = lambda A: 'A. y e. RR ( 1 <_ y -> sum_ d e. ( 1 ... ( |_ ` y ) ) ( ( abs ` ( %s ` d ) ) / d ) <_ ( ( log ` y ) + 1 ) )' % A
DS = lambda A, Z, k='k': 'sum_ %s e. NN ( ( %s ` %s ) x. ( %s ^c -u %s ) )' % (k, A, k, k, Z)
AF = '( q e. NN |-> if ( q || N , ( ( mmu ` q ) x. ( %s ` q ) ) , 0 ) )' % CY
PFS = lambda z: 'sum_ d e. %s ( ( ( mmu ` d ) x. ( %s ` d ) ) x. ( d ^c -u %s ) )' % (DIV('N'), CY, z)
PF = '( w e. CC |-> %s )' % PFS('w')
OMGN = Z6A.OMG()
LF = ZL1.LF                                               # ( N DChrLF X )
TOPC = '( TopOpen ` CCfld )'
HPZ = ZL1.HPZ
DD = '( U i^i %s )' % HPZ
GPR = lambda w: '( ( ( ( %s - 1 ) x. ( F ` %s ) ) + %s ) x. ( PF ` %s ) )'.replace('PF', PF) % (w, w, RP, w)   # ( ( w - 1 ) F ( w ) + R ) P ( w )
HH = '( u e. %s |-> ( ( %s ` u ) - %s ) )' % (DD, LF, GPR('u'))          # binder u: PF binds w, holidrect's dummies are w y s
# generic holomorphy helpers
STATEMENTS['zl2hres'] = ('( ( %s /\\ ( U e. %s /\\ U C_ D ) ) -> %s )' % (HOL('F', 'D'), TOPC, HOL('( z e. U |-> ( F ` z ) )', 'U')))
STATEMENTS['zl2hadd'] = '( ( %s /\\ %s ) -> %s )' % (HOL('F', 'D'), HOL('G', 'D'), HOL('( z e. D |-> ( ( F ` z ) + ( G ` z ) ) )', 'D'))
STATEMENTS['zl2hsub'] = '( ( %s /\\ %s ) -> %s )' % (HOL('F', 'D'), HOL('G', 'D'), HOL('( z e. D |-> ( ( F ` z ) - ( G ` z ) ) )', 'D'))
# the character on NN (generic in N, X; instantiated at the conductor and the primitive character)
STATEMENTS['zl2chb'] = '( %s -> %s )' % (NXL, CFB1(CXN))
STATEMENTS['zl2chs'] = ('( ( %s /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) ) -> ( %s e. CC /\\ ( abs ` %s ) <_ ( 1 + ( 1 / ( ( Re ` Z ) - 1 ) ) ) ) )'
                        % (NXL, DS(CXN, 'Z'), DS(CXN, 'Z')))
STATEMENTS['zl2chm'] = '( ( %s /\\ ( K e. NN /\\ D e. %s ) ) -> ( ( %s ` D ) x. ( %s ` ( K / D ) ) ) = ( %s ` K ) )' % (NXL, DIV('K'), CXN, CXN, CXN)
STATEMENTS['zl2cfblav'] = '( ( A : NN --> CC /\\ A. m e. NN ( abs ` ( A ` m ) ) <_ 1 ) -> %s )' % LAVB('A')
# the Dirichlet polynomial of the Euler factors
STATEMENTS['zl2afv'] = '( K e. NN -> ( %s ` K ) = if ( K || N , ( ( mmu ` K ) x. ( %s ` K ) ) , 0 ) )' % (AF, CY)
STATEMENTS['zl2afb'] = '( %s -> %s )' % (NXL, CFB1(AF))
STATEMENTS['zl2musub'] = ('( ( N e. NN /\\ K e. NN ) -> sum_ d e. %s if ( d || N , ( mmu ` d ) , 0 ) = if ( ( K gcd N ) = 1 , 1 , 0 ) )' % DIV('K'))
STATEMENTS['zl2cxv2'] = '( ( %s /\\ K e. NN ) -> ( %s ` K ) = if ( ( K gcd N ) = 1 , ( %s ` K ) , 0 ) )' % (NXL, CXN, CY)
STATEMENTS['zl2cxc'] = '( ( %s /\\ K e. NN ) -> sum_ d e. %s ( ( %s ` d ) x. ( %s ` ( K / d ) ) ) = ( %s ` K ) )' % (NXL, DIV('K'), AF, CY, CXN)
STATEMENTS['zl2dsp'] = '( ( %s /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) ) -> %s = ( %s x. %s ) )' % (NXL, DS(CXN, 'Z'), DS(AF, 'Z'), DS(CY, 'Z'))
STATEMENTS['zl2dpf'] = '( ( %s /\\ Z e. CC ) -> %s = %s )' % (NXL, DS(AF, 'Z'), PFS('Z'))
STATEMENTS['zl2muabs'] = '( D e. NN -> ( abs ` ( mmu ` D ) ) = if ( ( mmu ` D ) =/= 0 , 1 , 0 ) )'
STATEMENTS['zl2sqfc'] = '( N e. NN -> sum_ d e. %s ( abs ` ( mmu ` d ) ) = %s )' % (DIV('N'), OMGN)
STATEMENTS['zl2dpb'] = '( ( %s /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) -> ( abs ` %s ) <_ %s )' % (NXL, PFS('S'), OMGN)
STATEMENTS['zl2dpv'] = '( Z e. CC -> ( %s ` Z ) = %s )' % (PF, PFS('Z'))
STATEMENTS['zl2dph'] = '( %s -> %s )' % (NXL, HOL(PF, 'CC'))
# the L-function of X as the product, on the strip
NXP = '( %s /\\ %s )' % (NXL, PCONT)
STATEMENTS['zl2lfe1'] = ('( ( %s /\\ ( S e. CC /\\ ( 1 < ( Re ` S ) /\\ ( Re ` S ) <_ 2 ) ) ) -> ( %s ` S ) = %s )' % (NXP, LF, GPR('S')))
STATEMENTS['zl2lfh'] = '( %s -> %s )' % (NXP, HOL(HH, DD))
STATEMENTS['zl2lfe'] = ('( ( %s /\\ ( S e. CC /\\ ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` S ) /\\ ( Re ` S ) <_ 2 ) ) ) -> ( %s ` S ) = %s )' % (NXP, LF, GPR('S')))
# the edges of F at A = 2, modulus M
FPM = '( w e. CC |-> ( ( F ` w ) + ( %s / ( w - 1 ) ) ) )' % RP          # F + R / ( w - 1 ), the primitive L-function
GYB = '( w e. CC |-> %s )' % DS(CYB, 'w')                                  # the Dirichlet series of the inverse character
STATEMENTS['zl2ergt'] = '( %s -> %s )' % (NXP, RGT('F', '2'))
STATEMENTS['zl2elft'] = '( %s -> %s )' % (NXP, LFT('F', '2', MC))
STATEMENTS['zl2ecvx'] = ('( ( %s /\\ %s ) -> ( abs ` ( F ` S ) ) <_ ( ( %s x. 2 ) x. %s ) )' % (NXP, SRNG2(), C5E, CXB('S', MC)))
# the identity-theorem rectangle for the L-function identity (height V + 1, margin 1/400, zero neighbourhood at 5/4)
RCA = lambda V: '( ( 1 / ; ; 2 0 0 ) + ( _i x. -u ( %s + 1 ) ) )' % V
RCB = lambda V: '( ( 3 / 2 ) + ( _i x. ( %s + 1 ) ) )' % V
RQ = '( 1 / ; ; 4 0 0 )'
FAT = lambda V: '( ( %s - ( %s + ( _i x. %s ) ) ) crect ( %s + ( %s + ( _i x. %s ) ) ) )' % (RCA(V), RQ, RQ, RCB(V), RQ, RQ)
X54 = '( 5 / 4 )'
STATEMENTS['zl2lfrc'] = '( ( %s /\\ ( V e. RR /\\ 0 <_ V ) ) -> %s C_ %s )' % (NXP, FAT('V'), DD)
STATEMENTS['zl2lfnb'] = '( %s -> E. s e. RR+ A. v e. %s ( ( abs ` ( v - %s ) ) < s -> ( %s ` v ) = 0 ) )' % (NXP, DD, X54, HH)
STATEMENTS['zl2lfz'] = '( ( %s /\\ ( V e. RR /\\ 0 <_ V ) ) -> A. y e. ( %s crect %s ) ( %s ` y ) = 0 )' % (NXP, RCA('V'), RCB('V'), HH)
STATEMENTS['zl2egr'] = ('( %s -> A. y e. CC ( 1 < ( Re ` y ) -> ( ( %s ` y ) e. CC /\\ ( abs ` ( %s ` y ) ) <_ ( 1 x. ( 1 + ( 1 / ( ( Re ` y ) - 1 ) ) ) ) ) ) )' % (NXP, GYB, GYB))
STATEMENTS['zl2efe'] = ('( %s -> A. y e. CC ( ( -u ( 1 / 2 ) <_ ( Re ` y ) /\\ ( Re ` y ) < 0 ) -> ( %s ` y ) = ( ( ( %s ^c ( ( 1 / 2 ) - y ) ) x. T ) x. ( ( Q ` y ) x. ( %s ` ( 1 - y ) ) ) ) ) )'
                        % (NXP, FPM, MC, GYB))
STATEMENTS['zl2elft1'] = '( %s -> %s )' % (NXP, LFT(FPM, '1', MC))
for _l in ['zl2hres', 'zl2hadd', 'zl2hsub', 'zl2chb', 'zl2chs', 'zl2chm', 'zl2cfblav', 'zl2afv', 'zl2afb', 'zl2musub', 'zl2cxv2', 'zl2cxc',
           'zl2dsp', 'zl2dpf', 'zl2muabs', 'zl2sqfc', 'zl2dpb', 'zl2dpv', 'zl2dph', 'zl2lfe1', 'zl2lfh', 'zl2lfrc', 'zl2lfnb', 'zl2lfz', 'zl2lfe',
           'zl2ergt', 'zl2egr', 'zl2efe', 'zl2elft1', 'zl2elft', 'zl2ecvx']:
    ORDER.insert(ORDER.index('zl2cvxe'), _l)
