"""Sortie Z5a helpers (Route Z: Detector.lean from the top).

STATEMENTS / HYPS are the frozen statements of Z5a-blueprint.md, one place,
so that the blueprint, the grammar check and the generators cannot drift apart.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zd1lib import *          # Z1, Z2, XP, RP, ELLD, C12, B1, B2, BA, FN, EN, HZD, HT, H0, PL, BVL, DV, XB, helpers
from zd1lib import STATEMENTS as ZD1S

# ---- the Detector objects (Detector.lean section 1, GramFunction section 10)
M0 = '( D ^c ( 3 / 5 ) )'                                   # M0par D
HZ2 = '( D e. RR /\\ 1 < D /\\ 2 <_ ( log ` D ) )'          # Lean hD, hLD (2 <_ log D)
PSI = lambda r, n: '( ( mmu ` ( %s gcd %s ) ) x. ( phi ` ( %s gcd %s ) ) )' % (r, n, r, n)   # psi r n
RSET = lambda N, R: '( %s RSet %s )' % (N, R)
PFUN = lambda N, R: '( %s PFun %s )' % (N, R)
PFV = lambda N, R, K: 'sum_ r e. %s ( %s / r )' % (RSET(N, R), PSI('r', K))
WG = lambda K, t='t': '( exp ` ( -u %s / ( exp ` %s ) ) )' % (K, t)     # the window integrand
DI = lambda a, L, K: 'S_ [ %s -> ( %s + %s ) ] %s _d t' % (a, a, L, WG(K))
AV = lambda a, L, K: '( ( 1 / %s ) x. %s )' % (L, DI(a, L, K))
WW = lambda M, X, L: '( WWin ` <. %s , %s , %s >. )' % (M, X, L)
WBODY = lambda M, X, L, K: '( %s - %s )' % (AV('( log ` %s )' % X, L, K), AV('( log ` %s )' % M, L, K))
BMV = lambda P, W, K: '( ( ( 1 / %s ) x. ( ( %s ` %s ) ^ 2 ) ) x. ( %s ` %s ) )' % (K, P, K, W, K)
CDT = lambda A, B, P, X, S, K: '( ( ( ( ( %s bvA %s ) ` %s ) x. ( %s ` %s ) ) x. ( exp ` ( -u %s / %s ) ) ) x. ( %s ^c -u %s ) )' % (A, B, K, P, K, K, X, K, S)
CDV = lambda A, B, P, X, S, K: 'if ( %s < %s , %s , 0 )' % (A, K, CDT(A, B, P, X, S, K))
FDT = lambda A, B, P, X, C, S, n='n': ('if ( %s < %s , ( ( ( ( ( ( %s bvA %s ) ` %s ) x. ( %s ` %s ) ) x. ( exp ` ( -u %s / %s ) ) ) x. ( %s ` %s ) ) x. ( %s ^c -u %s ) ) , 0 )'
                                       % (A, n, A, B, n, P, n, n, X, C, n, n, S))
# at the frozen parameters
PF = PFUN('N', RP)
WF = WW(M0, XP, ELLD)
BM = '( %s bMaj %s )' % (PF, WF)
CD = '( <. %s , %s >. cDet <. %s , %s , T >. )' % (Z1, Z2, PF, XP)
QT = lambda k: 'if ( ( %s ` %s ) = 0 , 0 , ( ( ( %s ` %s ) ^ 2 ) / ( %s ` %s ) ) )' % (BM, k, CD, k, BM, k)
TERM3 = lambda k: '( 3 x. ( ( ( %s ^c ( 1 - ( 2 x. T ) ) ) x. ( %s ^ 2 ) ) x. ( exp ` ( -u %s / %s ) ) ) )' % (k, BA(k), k, XP)
HAB0 = '( ( A e. RR /\\ 0 < A ) /\\ ( B e. RR /\\ A < B ) )'
HAB1 = '( ( A e. RR /\\ 1 <_ A ) /\\ ( B e. RR /\\ A < B ) )'
BVLK = lambda K: BVL(K)
WV = lambda K: '( %s ` %s )' % (WW('M', 'X', 'L'), K)

STATEMENTS = {
    # section A: posLog and the weight
    'z5plbnd': '( X e. RR+ -> ( 0 <_ %s /\\ ( log ` X ) <_ %s ) )' % (PL('X'), PL('X')),
    'z5pl0': '( ( X e. RR /\\ X <_ 1 ) -> %s = 0 )' % PL('X'),
    'z5plmul': '( ( ( X e. RR /\\ 0 <_ X ) /\\ ( C e. RR /\\ 1 <_ C ) ) -> %s <_ ( %s + ( log ` C ) ) )' % (PL('( X x. C )'), PL('X')),
    'z5lamval': '( ( ( A e. V /\\ B e. W ) /\\ K e. NN ) -> ( ( A bvLam B ) ` K ) = %s )' % BVLK('K'),
    'z5lammu': '( ( %s /\\ ( K e. NN /\\ K <_ A ) ) -> ( ( A bvLam B ) ` K ) = ( mmu ` K ) )' % HAB1,
    'z5lam0': '( ( %s /\\ ( K e. NN /\\ B <_ K ) ) -> ( ( A bvLam B ) ` K ) = 0 )' % HAB0,
    'z5lamabs': '( ( %s /\\ K e. NN ) -> ( abs ` ( ( A bvLam B ) ` K ) ) <_ 1 )' % HAB0,
    'z5bvamu': '( ( %s /\\ ( N e. NN /\\ N <_ A ) ) -> ( ( A bvA B ) ` N ) = if ( N = 1 , 1 , 0 ) )' % HAB1,
    'z5bva1': '( %s -> ( ( A bvA B ) ` 1 ) = 1 )' % HAB1,
    'z5bva0': '( ( %s /\\ ( N e. NN /\\ ( 1 < N /\\ N <_ A ) ) ) -> ( ( A bvA B ) ` N ) = 0 )' % HAB1,
    'z5bvaabs': '( ( %s /\\ N e. NN ) -> ( abs ` ( ( A bvA B ) ` N ) ) <_ N )' % HAB0,
    # section B: pseudocharacters
    'z5phile': '( N e. NN -> ( phi ` N ) <_ N )',
    'z5rsetval': '( ( N e. V /\\ R e. W ) -> %s = { k e. ( 1 ... ( |_ ` R ) ) | ( ( mmu ` k ) =/= 0 /\\ ( k gcd N ) = 1 ) } )' % RSET('N', 'R'),
    'z5elrset': '( ( N e. V /\\ R e. W ) -> ( K e. %s <-> ( K e. ( 1 ... ( |_ ` R ) ) /\\ ( ( mmu ` K ) =/= 0 /\\ ( K gcd N ) = 1 ) ) ) )' % RSET('N', 'R'),
    'z5rsetfi': '( ( N e. V /\\ R e. W ) -> ( %s C_ ( 1 ... ( |_ ` R ) ) /\\ %s e. Fin ) )' % (RSET('N', 'R'), RSET('N', 'R')),
    'z5rsetcard': '( ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) -> ( # ` %s ) <_ ( |_ ` R ) )' % RSET('N', 'R'),
    'z5pfunval': '( ( ( N e. V /\\ R e. W ) /\\ K e. NN ) -> ( %s ` K ) = %s )' % (PFUN('N', 'R'), PFV('N', 'R', 'K')),
    'z5psiabs': '( ( R e. NN /\\ K e. NN ) -> ( abs ` %s ) <_ R )' % PSI('R', 'K'),
    'z5pfunre': '( ( ( N e. V /\\ R e. W ) /\\ K e. NN ) -> ( %s ` K ) e. RR )' % PFUN('N', 'R'),
    'z5pfunabs': '( ( ( N e. V /\\ ( R e. RR /\\ 0 <_ R ) ) /\\ K e. NN ) -> ( abs ` ( %s ` K ) ) <_ ( |_ ` R ) )' % PFUN('N', 'R'),
    'z5pfun1': '( ( N e. V /\\ R e. W ) -> ( %s ` 1 ) = sum_ r e. %s ( 1 / r ) )' % (PFUN('N', 'R'), RSET('N', 'R')),
    'z5p1ge0': '( ( N e. V /\\ R e. W ) -> 0 <_ sum_ r e. %s ( 1 / r ) )' % RSET('N', 'R'),
    # section C: the window
    'z5wwinval': '( ( ( M e. U /\\ X e. V /\\ L e. W ) /\\ K e. NN ) -> %s = %s )' % (WV('K'), WBODY('M', 'X', 'L', 'K')),
    'z5wcn': '( ( ( A e. RR /\\ B e. RR ) /\\ K e. RR ) -> ( t e. ( A [,] B ) |-> %s ) e. ( ( A [,] B ) -cn-> CC ) )' % WG('K'),
    'z5wibl': '( ( ( A e. RR /\\ B e. RR ) /\\ K e. RR ) -> ( ( t e. ( A (,) B ) |-> %s ) e. L^1 /\\ S. ( A (,) B ) %s _d t e. RR ) )' % (WG('K'), WG('K')),
    'z5wmono': '( ( ( K e. RR /\\ 0 <_ K ) /\\ ( Y e. RR /\\ Z e. RR /\\ Y <_ Z ) ) -> %s <_ %s )' % (WG('K', 'Y'), WG('K', 'Z')),
    'z5wavg': '( ( ( A e. RR /\\ L e. RR+ ) /\\ ( K e. RR /\\ 0 <_ K ) ) -> ( ( exp ` ( -u K / ( exp ` A ) ) ) <_ %s /\\ %s <_ ( exp ` ( -u K / ( exp ` ( A + L ) ) ) ) ) )'
              % (AV('A', 'L', 'K'), AV('A', 'L', 'K')),
    'z5wlow': '( ( ( M e. RR+ /\\ X e. RR+ /\\ L e. RR+ ) /\\ K e. NN ) -> ( ( exp ` ( -u K / X ) ) - ( exp ` ( -u K / ( M x. ( exp ` L ) ) ) ) ) <_ %s )' % WV('K'),
    'z5wpos': '( ( ( ( M e. RR+ /\\ L e. RR+ ) /\\ ( X e. RR /\\ ( M x. ( exp ` L ) ) < X ) ) /\\ K e. NN ) -> 0 < %s )' % WV('K'),
    'z5wthird': '( ( ( ( M e. RR+ /\\ L e. RR+ ) /\\ ( Z e. RR+ /\\ X e. RR ) ) /\\ ( ( ( M x. ( exp ` L ) ) <_ Z /\\ ( 2 x. Z ) <_ X ) /\\ ( K e. NN /\\ Z < K ) ) ) -> '
                '( ( 1 / 3 ) x. ( exp ` ( -u K / X ) ) ) <_ %s )' % WV('K'),
    'z5fwin': '( %s -> ( ( 1 <_ %s /\\ %s < %s ) /\\ ( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s ) ) )' % (HZ2, Z1, Z1, Z2, M0, ELLD, Z1, Z1, XP),
    # section D: majorant, coefficients, detector
    'z5bmajval': '( ( ( P e. V /\\ W e. U ) /\\ K e. NN ) -> ( ( P bMaj W ) ` K ) = %s )' % BMV('P', 'W', 'K'),
    'z5cdetval': '( ( ( ( A e. U /\\ B e. V ) /\\ ( P e. W /\\ X e. T /\\ S e. Z ) ) /\\ K e. NN ) -> ( ( <. A , B >. cDet <. P , X , S >. ) ` K ) = %s )'
                 % CDV('A', 'B', 'P', 'X', 'S', 'K'),
    'z5fdetval': '( ( ( ( A e. U /\\ B e. V ) /\\ ( P e. W /\\ X e. T /\\ C e. Z ) ) /\\ S e. CC ) -> ( ( <. A , B >. FDet <. P , X , C >. ) ` S ) = sum_ n e. NN %s )'
                 % FDT('A', 'B', 'P', 'X', 'C', 'S'),
    'z5bmaj0': '( ( ( %s /\\ N e. V ) /\\ K e. NN ) -> 0 <_ ( %s ` K ) )' % (HZ2, BM),
    'z5cdterm': '( ( ( %s /\\ N e. V ) /\\ ( T e. RR /\\ K e. NN ) ) -> %s <_ %s )' % (HZ2, QT('K'), TERM3('K')),
    'z5cdt0': '( ( ( %s /\\ N e. V ) /\\ ( T e. RR /\\ K e. NN ) ) -> ( %s e. RR /\\ 0 <_ %s ) )' % (HZ2, QT('K'), QT('K')),
    'z5sigdiag': '( ( %s /\\ N e. V ) -> ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ sum_ n e. NN %s <_ ( %s x. %s ) ) )' % (H0, QT('k'), QT('n'), C12, XB),
}

HYPS = {}

ORDER = ['z5plbnd', 'z5pl0', 'z5plmul', 'z5lamval', 'z5lammu', 'z5lam0', 'z5lamabs', 'z5bvamu', 'z5bva1', 'z5bva0', 'z5bvaabs',
         'z5phile', 'z5rsetval', 'z5elrset', 'z5rsetfi', 'z5rsetcard', 'z5pfunval', 'z5psiabs', 'z5pfunre', 'z5pfunabs', 'z5pfun1', 'z5p1ge0',
         'z5wwinval', 'z5wcn', 'z5wibl', 'z5wmono', 'z5wavg', 'z5wlow', 'z5wpos', 'z5wthird', 'z5fwin',
         'z5bmajval', 'z5cdetval', 'z5fdetval', 'z5bmaj0', 'z5cdterm', 'z5cdt0', 'z5sigdiag']


def gramcheck(labels):
    """grammar-check frozen statements: a worksheet per label with the $e lines and a bare qed"""
    import mm as _MM, re as _re
    from c0lib import hyp
    out = {}
    for lab in labels:
        w = W('z5g' + lab.replace('.', ''), 'grammar check of %s' % lab)
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
    from c0lib import hyp
    return [hyp(w, n, '%s.%s' % (lab, n), f) for n, f in HYPS.get(lab, [])]


def run(w):
    return (runh if HYPS.get(w.label) else (lambda x: x.run()))(w)


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])


# ---- step patterns
def cases(w, ante, phi, tstep, fstep, concl, name=None):
    """( ante -> concl ) from ( ( ante /\\ phi ) -> concl ) and ( ( ante /\\ -. phi ) -> concl )"""
    return w.s([tstep, fstep], 'pm2.61dan', '( %s -> %s )' % (ante, concl), name=name)


def ift(w, a, phi, A, B):
    """( a -> if ( phi , A , B ) = A ), a = ( X /\\ phi )"""
    return w.s([w.s([], 'simpr', '( %s -> %s )' % (a, phi)), w.inst('iftrue')], 'syl', '( %s -> if ( %s , %s , %s ) = %s )' % (a, phi, A, B, A))


def iff_(w, a, phi, A, B):
    """( a -> if ( phi , A , B ) = B ), a = ( X /\\ -. phi )"""
    return w.s([w.s([], 'simpr', '( %s -> -. %s )' % (a, phi)), w.inst('iffalse')], 'syl', '( %s -> if ( %s , %s , %s ) = %s )' % (a, phi, A, B, B))


def iftd(w, ante, pst, phi, A, B):
    """( ante -> if ( phi , A , B ) = A ) from pst: ( ante -> phi )"""
    return w.s([pst, w.inst('iftrue')], 'syl', '( %s -> if ( %s , %s , %s ) = %s )' % (ante, phi, A, B, A))


def iffd(w, ante, pst, phi, A, B):
    """( ante -> if ( phi , A , B ) = B ) from pst: ( ante -> -. phi )"""
    return w.s([pst, w.inst('iffalse')], 'syl', '( %s -> if ( %s , %s , %s ) = %s )' % (ante, phi, A, B, B))


def onele(w, ante, xr, yrp, xley, X, Y):
    """( ante -> 1 <_ ( X / Y ) ) from X e. RR (xr), Y e. RR+ (yrp), Y <_ X (xley)"""
    st = mkst(w, ante)
    bi = st([st([], '1red', '1 e. RR'), xr, yrp], 'lemuldivd', '( ( 1 x. %s ) <_ %s <-> 1 <_ ( %s / %s ) )' % (Y, X, X, Y))
    m = st([st([st([st([yrp], 'rpcnd', '%s e. CC' % Y)], 'mullidd', '( 1 x. %s ) = %s' % (Y, Y)), xley], 'eqbrtrd', '( 1 x. %s ) <_ %s' % (Y, X)), bi], 'mpbid',
           '1 <_ ( %s / %s )' % (X, Y))
    return m


def lepone(w, ante, xr, yrp, xley, X, Y):
    """( ante -> ( X / Y ) <_ 1 ) from X e. RR, Y e. RR+, X <_ Y"""
    st = mkst(w, ante)
    bi = st([xr, st([], '1red', '1 e. RR'), yrp], 'ledivmuld', '( ( %s / %s ) <_ 1 <-> %s <_ ( %s x. 1 ) )' % (X, Y, X, Y))
    m = st([st([xley, st([st([st([yrp], 'rpcnd', '%s e. CC' % Y)], 'mulridd', '( %s x. 1 ) = %s' % (Y, Y))], 'eqcomd', '%s = ( %s x. 1 )' % (Y, Y))], 'breqtrd',
               '%s <_ ( %s x. 1 )' % (X, Y)), bi], 'mpbird', '( %s / %s ) <_ 1' % (X, Y))
    return m


def cg(w, expr, v, V):
    """( v = V -> expr = expr[V/v] )"""
    idv = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, V, v, V))
    st, new = w.congr(expr, {v: V}, '%s = %s' % (v, V), {v: idv})
    return st


RSB = lambda N, R, k='k': '{ %s e. ( 1 ... ( |_ ` %s ) ) | ( ( mmu ` %s ) =/= 0 /\\ ( %s gcd %s ) = 1 ) }' % (k, R, k, k, N)
