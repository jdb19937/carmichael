"""Sortie MV, section A: the trigonometric identities behind the Fejer integral
(mvdk, mvsinsq)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from mvlib import *
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    bad = checkrefs(w)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, bad)); return False
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def rw(w, ante, expr, rules):
    """( ante -> expr = expr' ) rewriting the exact subterms of RULES {old: (new, step)}"""
    return w.rewrite(expr, rules, ante)[0]


def sinarg(w, ante, u, u2, eqst):
    """( ante -> ( sin ` u ) = ( sin ` u2 ) ) from eqst: ( ante -> u = u2 )"""
    return dst(w, ante, [eqst], 'fveq2d', '( sin ` %s ) = ( sin ` %s )' % (u, u2))


def mvdk():
    w = W('mvdk', 'The Dirichlet-kernel identity sin ( ( 2 M + 1 ) X ) = sin X ( 1 + 2 sum_ k <_ M cos ( 2 k X ) ), by telescoping (the elementary input of the Fejer integral, MeanValue fourier_triC replaced).')
    A0 = '( M e. NN0 /\\ X e. CC )'
    P = parts(w, A0)
    mn, xc = P['M e. NN0'], P['X e. CC']
    cl = Closure(w, A0, {'M': ('NN0', mn), 'X': ('CC', xc)})
    # telfsum2 with lemma-k := m, lemma-j := k, A := sin ( ( ( 2 m ) - 1 ) X )
    Aexp = '( sin ` ( ( ( 2 x. m ) - 1 ) x. X ) )'
    hs = []
    for ante, rep in [('m = k', 'k'), ('m = ( k + 1 )', '( k + 1 )'), ('m = 1', '1'), ('m = ( M + 1 )', '( M + 1 )')]:
        idst = w.s([], 'id', '( %s -> %s )' % (ante, ante))
        s, new = w.congr(Aexp, {'m': rep}, ante, {'m': idst})
        hs.append((s, new))
    (h1, B), (h2, C), (h3, D), (h4, E) = hs
    mz = dst(w, A0, [mn], 'nn0zd', 'M e. ZZ')
    m1 = ap(w, A0, 'nn0p1nn', [mn], '( M + 1 ) e. NN')
    m1u = ap(w, A0, 'elnnuz', [m1], '( M + 1 ) e. ( ZZ>= ` 1 )') if False else None
    m1u = dst(w, A0, [w.s([m1, w.inst('nnuz')], 'eleqtrdi', '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % A0)], 'id', '( M + 1 ) e. ( ZZ>= ` 1 )') if False else \
        w.s([m1, w.inst('nnuz')], 'eleqtrdi', '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % A0)
    Am = '( %s /\\ m e. ( 1 ... ( M + 1 ) ) )' % A0
    cm = Closure(w, Am, {'m': ('ZZ', ap(w, Am, 'elfzelz', [w.s([], 'simpr', '( %s -> m e. ( 1 ... ( M + 1 ) ) )' % Am)], 'm e. ZZ')),
                         'X': ('CC', lift(w, xc, Am))})
    acl = cm.mem(Aexp, 'CC')
    tel = w.s([h1, h2, h3, h4, mz, m1u, acl], 'telfsum2', '( %s -> sum_ k e. ( 1 ... M ) ( %s - %s ) = ( %s - %s ) )' % (A0, C, B, E, D))
    # per term: C - B = sin X ( 2 cos ( 2 k X ) )
    Ak = '( %s /\\ k e. ( 1 ... M ) )' % A0
    kz = ap(w, Ak, 'elfzelz', [w.s([], 'simpr', '( %s -> k e. ( 1 ... M ) )' % Ak)], 'k e. ZZ')
    ck = Closure(w, Ak, {'k': ('ZZ', kz), 'X': ('CC', lift(w, xc, Ak))})
    U = C[len('( sin ` '):-2]; V = B[len('( sin ` '):-2]
    sub = ap(w, Ak, 'subsin', [ck.mem(U, 'CC'), ck.mem(V, 'CC')],
             '( %s - %s ) = ( 2 x. ( ( cos ` ( ( %s + %s ) / 2 ) ) x. ( sin ` ( ( %s - %s ) / 2 ) ) ) )' % (C, B, U, V, U, V))
    K2 = '( ( 2 x. k ) x. X )'
    e1 = ringeq(w, Ak, '( ( %s + %s ) / 2 )' % (U, V), K2, ck)
    e2 = ringeq(w, Ak, '( ( %s - %s ) / 2 )' % (U, V), 'X', ck)
    r1 = rw(w, Ak, '( 2 x. ( ( cos ` ( ( %s + %s ) / 2 ) ) x. ( sin ` ( ( %s - %s ) / 2 ) ) ) )' % (U, V, U, V),
            {'( ( %s + %s ) / 2 )' % (U, V): (K2, e1), '( ( %s - %s ) / 2 )' % (U, V): ('X', e2)})
    T1 = '( 2 x. ( ( cos ` %s ) x. ( sin ` X ) ) )' % K2
    T2 = '( ( sin ` X ) x. ( 2 x. ( cos ` %s ) ) )' % K2
    ck.leaf('( cos ` %s )' % K2, 'CC', ck.mem('( cos ` %s )' % K2, 'CC'))
    ck.leaf('( sin ` X )', 'CC', ck.mem('( sin ` X )', 'CC'))
    r2 = ringeq(w, Ak, T1, T2, ck)
    term = eqt(w, Ak, eqt(w, Ak, sub, r1), r2)
    SUMC = 'sum_ k e. ( 1 ... M ) ( cos ` %s )' % K2
    s1 = dst(w, A0, [term], 'sumeq2dv', 'sum_ k e. ( 1 ... M ) ( %s - %s ) = sum_ k e. ( 1 ... M ) %s' % (C, B, T2))
    fz = w.s([], 'fzfid', '( %s -> ( 1 ... M ) e. Fin )' % A0)
    sx = cl.mem('( sin ` X )', 'CC')
    c2 = dst(w, Ak, [ck.mem('( cos ` %s )' % K2, 'CC')], 'id', '( cos ` %s ) e. CC' % K2) if False else ck.mem('( 2 x. ( cos ` %s ) )' % K2, 'CC')
    m1s = dst(w, A0, [fz, sx, c2], 'fsummulc2', '( ( sin ` X ) x. sum_ k e. ( 1 ... M ) ( 2 x. ( cos ` %s ) ) ) = sum_ k e. ( 1 ... M ) %s' % (K2, T2))
    cck = ck.mem('( cos ` %s )' % K2, 'CC')
    m2s = dst(w, A0, [fz, w.s([], '2cnd', '( %s -> 2 e. CC )' % A0), cck], 'fsummulc2', '( 2 x. %s ) = sum_ k e. ( 1 ... M ) ( 2 x. ( cos ` %s ) )' % (SUMC, K2))
    m3 = dst(w, A0, [m2s], 'oveq2d', '( ( sin ` X ) x. ( 2 x. %s ) ) = ( ( sin ` X ) x. sum_ k e. ( 1 ... M ) ( 2 x. ( cos ` %s ) ) )' % (SUMC, K2))
    Q = '( ( sin ` X ) x. ( 2 x. %s ) )' % SUMC
    lhs_eq = eqt(w, A0, eqt(w, A0, eqc(w, A0, tel), s1), eqc(w, A0, eqt(w, A0, m3, m1s)))   # ( E - D ) = Q
    # E = sin ( ( ( 2 M ) + 1 ) X ), D = sin X
    EU = E[len('( sin ` '):-2]; DU = D[len('( sin ` '):-2]
    MX = '( ( ( 2 x. M ) + 1 ) x. X )'
    eE = sinarg(w, A0, EU, MX, ringeq(w, A0, EU, MX, cl))
    eD = sinarg(w, A0, DU, 'X', ringeq(w, A0, DU, 'X', cl))
    SM = '( sin ` %s )' % MX
    d1 = dst(w, A0, [eE, eD], 'oveq12d', '( %s - %s ) = ( %s - ( sin ` X ) )' % (E, D, SM))
    k1 = eqt(w, A0, eqc(w, A0, d1), lhs_eq)          # ( SM - sin X ) = Q
    smc = cl.mem(SM, 'CC')
    np = dst(w, A0, [smc, sx], 'npcand', '( ( %s - ( sin ` X ) ) + ( sin ` X ) ) = %s' % (SM, SM))
    k2 = dst(w, A0, [k1], 'oveq1d', '( ( %s - ( sin ` X ) ) + ( sin ` X ) ) = ( %s + ( sin ` X ) )' % (SM, Q))
    cl.leaf(SUMC, 'CC', cl.mem(SUMC, 'CC'))
    cl.leaf('( sin ` X )', 'CC', sx)
    k3 = ringeq(w, A0, '( %s + ( sin ` X ) )' % Q, '( ( sin ` X ) x. ( 1 + ( 2 x. %s ) ) )' % SUMC, cl)
    fin = eqt(w, A0, eqt(w, A0, eqc(w, A0, np), k2), k3)
    w.qed([fin], 'id' if False else 'eqtri', STATEMENTS['mvdk']) if False else None
    last = w.lines[-1]
    nm = last.split(':', 1)[0]
    w.lines[-1] = 'qed' + last[len(nm):]
    go(w)



def telhyps(w, Aexp, var, reps):
    """the substitution hypotheses ( var = rep -> A = A[rep] ) of a telescoping lemma"""
    out = []
    for rep in reps:
        ante = '%s = %s' % (var, rep)
        idst = w.s([], 'id', '( %s -> %s )' % (ante, ante))
        out.append(w.congr(Aexp, {var: rep}, ante, {var: idst}))
    return out


def sq2(w, ante, E, cst):
    """( ante -> ( E ^ 2 ) = ( E x. E ) ) from cst: E e. CC"""
    return dst(w, ante, [cst], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (E, E, E))


def mvsinsq():
    w = W('mvsinsq', 'sin ^ 2 ( N X ) = sin ^ 2 X . sum_ m < N ( 1 + 2 sum_ k <_ m cos ( 2 k X ) ), the Fejer-kernel identity, by telescoping sin ^ 2 ( ( m + 1 ) X ) - sin ^ 2 ( m X ) = sin ( ( 2 m + 1 ) X ) sin X and mvdk.')
    A0 = '( N e. NN0 /\\ X e. CC )'
    P = parts(w, A0)
    nn, xc = P['N e. NN0'], P['X e. CC']
    cl = Closure(w, A0, {'N': ('NN0', nn), 'X': ('CC', xc)})
    Aexp = '( ( sin ` ( j x. X ) ) ^ 2 )'
    (h1, B), (h2, C), (h3, D), (h4, E) = telhyps(w, Aexp, 'j', ['m', '( m + 1 )', '0', 'N'])
    nu = w.s([nn, w.inst('nn0uz')], 'eleqtrdi', '( %s -> N e. ( ZZ>= ` 0 ) )' % A0)
    Aj = '( %s /\\ j e. ( 0 ... N ) )' % A0
    cj = Closure(w, Aj, {'j': ('ZZ', ap(w, Aj, 'elfzelz', [w.s([], 'simpr', '( %s -> j e. ( 0 ... N ) )' % Aj)], 'j e. ZZ')),
                         'X': ('CC', lift(w, xc, Aj))})
    tel = w.s([h1, h2, h3, h4, nu, cj.mem(Aexp, 'CC')], 'telfsumo2',
              '( %s -> sum_ m e. ( 0 ..^ N ) ( %s - %s ) = ( %s - %s ) )' % (A0, C, B, E, D))
    # per term
    Am = '( %s /\\ m e. ( 0 ..^ N ) )' % A0
    mn0 = ap(w, Am, 'elfzonn0', [w.s([], 'simpr', '( %s -> m e. ( 0 ..^ N ) )' % Am)], 'm e. NN0')
    xm = lift(w, xc, Am)
    cm = Closure(w, Am, {'m': ('NN0', mn0), 'X': ('CC', xm)})
    U = '( ( m + 1 ) x. X )'; V = '( m x. X )'
    UpV = '( %s + %s )' % (U, V); UmV = '( %s - %s )' % (U, V)
    sm = ap(w, Am, 'sinmul', [cm.mem(UpV, 'CC'), cm.mem(UmV, 'CC')],
            '( ( sin ` %s ) x. ( sin ` %s ) ) = ( ( ( cos ` ( %s - %s ) ) - ( cos ` ( %s + %s ) ) ) / 2 )' % (UpV, UmV, UpV, UmV, UpV, UmV))
    e1 = ringeq(w, Am, '( %s - %s )' % (UpV, UmV), '( 2 x. %s )' % V, cm)
    e2 = ringeq(w, Am, '( %s + %s )' % (UpV, UmV), '( 2 x. %s )' % U, cm)
    c1 = ap(w, Am, 'cos2tsin', [cm.mem(V, 'CC')], '( cos ` ( 2 x. %s ) ) = ( 1 - ( 2 x. ( ( sin ` %s ) ^ 2 ) ) )' % (V, V))
    c2 = ap(w, Am, 'cos2tsin', [cm.mem(U, 'CC')], '( cos ` ( 2 x. %s ) ) = ( 1 - ( 2 x. ( ( sin ` %s ) ^ 2 ) ) )' % (U, U))
    k1 = eqt(w, Am, dst(w, Am, [e1], 'fveq2d', '( cos ` ( %s - %s ) ) = ( cos ` ( 2 x. %s ) )' % (UpV, UmV, V)), c1)
    k2 = eqt(w, Am, dst(w, Am, [e2], 'fveq2d', '( cos ` ( %s + %s ) ) = ( cos ` ( 2 x. %s ) )' % (UpV, UmV, U)), c2)
    SU = '( ( sin ` %s ) ^ 2 )' % U; SV = '( ( sin ` %s ) ^ 2 )' % V
    CU = '( 1 - ( 2 x. %s ) )' % SU; CV = '( 1 - ( 2 x. %s ) )' % SV
    k3 = dst(w, Am, [k1, k2], 'oveq12d', '( ( cos ` ( %s - %s ) ) - ( cos ` ( %s + %s ) ) ) = ( %s - %s )' % (UpV, UmV, UpV, UmV, CV, CU))
    k4 = dst(w, Am, [k3], 'oveq1d', '( ( ( cos ` ( %s - %s ) ) - ( cos ` ( %s + %s ) ) ) / 2 ) = ( ( %s - %s ) / 2 )' % (UpV, UmV, UpV, UmV, CV, CU))
    cm.leaf(SU, 'CC', cm.mem(SU, 'CC')); cm.leaf(SV, 'CC', cm.mem(SV, 'CC'))
    k5 = ringeq(w, Am, '( ( %s - %s ) / 2 )' % (CV, CU), '( %s - %s )' % (SU, SV), cm)
    prod = eqt(w, Am, eqt(w, Am, sm, k4), k5)          # sin(U+V) sin(U-V) = SU - SV
    M1 = '( ( ( 2 x. m ) + 1 ) x. X )'
    a1_ = dst(w, Am, [ringeq(w, Am, UpV, M1, cm)], 'fveq2d', '( sin ` %s ) = ( sin ` %s )' % (UpV, M1))
    a2_ = dst(w, Am, [ringeq(w, Am, UmV, 'X', cm)], 'fveq2d', '( sin ` %s ) = ( sin ` X )' % UmV)
    P1 = '( 1 + ( 2 x. sum_ k e. ( 1 ... m ) ( cos ` ( ( 2 x. k ) x. X ) ) ) )'
    dk = ap(w, Am, 'mvdk', [mn0, xm], '( sin ` %s ) = ( ( sin ` X ) x. %s )' % (M1, P1))
    a3 = dst(w, Am, [eqt(w, Am, a1_, dk), a2_], 'oveq12d', '( ( sin ` %s ) x. ( sin ` %s ) ) = ( ( ( sin ` X ) x. %s ) x. ( sin ` X ) )' % (UpV, UmV, P1))
    SX_ = '( sin ` X )'
    cm.leaf(SX_, 'CC', cm.mem(SX_, 'CC')); cm.leaf(P1, 'CC', cm.mem(P1, 'CC'))
    q = sq2(w, Am, SX_, cm.mem(SX_, 'CC'))
    T2 = '( ( ( sin ` X ) ^ 2 ) x. %s )' % P1
    r0 = ringeq(w, Am, '( ( ( sin ` X ) x. %s ) x. ( sin ` X ) )' % P1, '( ( ( sin ` X ) x. ( sin ` X ) ) x. %s )' % P1, cm)
    r1 = dst(w, Am, [eqc(w, Am, q)], 'oveq1d', '( ( ( sin ` X ) x. ( sin ` X ) ) x. %s ) = %s' % (P1, T2))
    term = eqt(w, Am, eqt(w, Am, eqt(w, Am, eqc(w, Am, prod), a3), r0), r1)     # SU - SV = sin^2 X . P1
    # C, B are exactly SU, SV
    assert C == SU and B == SV, (C, B)
    s1 = dst(w, A0, [term], 'sumeq2dv', 'sum_ m e. ( 0 ..^ N ) ( %s - %s ) = sum_ m e. ( 0 ..^ N ) %s' % (C, B, T2))
    fz = a1(w, A0, 'fzofi', '( 0 ..^ N ) e. Fin')
    s2 = dst(w, A0, [fz, cl.mem('( ( sin ` X ) ^ 2 )', 'CC'), cm.mem(P1, 'CC')], 'fsummulc2',
             '( ( ( sin ` X ) ^ 2 ) x. %s ) = sum_ m e. ( 0 ..^ N ) %s' % (PT('N', 'X'), T2))
    RHS = '( ( ( sin ` X ) ^ 2 ) x. %s )' % PT('N', 'X')
    big = eqt(w, A0, eqt(w, A0, eqc(w, A0, tel), s1), eqc(w, A0, s2))   # ( E - D ) = RHS
    # D = 0
    d0 = w.s([xc], 'mul02d', '( %s -> ( 0 x. X ) = 0 )' % A0)
    d1 = dst(w, A0, [d0], 'fveq2d', '( sin ` ( 0 x. X ) ) = ( sin ` 0 )')
    d2 = eqt(w, A0, d1, a1(w, A0, 'sin0', '( sin ` 0 ) = 0'))
    d3 = dst(w, A0, [d2], 'oveq1d', '%s = ( 0 ^ 2 )' % D)
    d4 = eqt(w, A0, d3, a1(w, A0, 'sq0', '( 0 ^ 2 ) = 0'))
    e5 = dst(w, A0, [d4], 'oveq2d', '( %s - %s ) = ( %s - 0 )' % (E, D, E))
    e6 = eqt(w, A0, e5, dst(w, A0, [cl.mem(E, 'CC')], 'subid1d', '( %s - 0 ) = %s' % (E, E)))
    fin = eqt(w, A0, eqc(w, A0, e6), big)
    qedlast(w)
    go(w)

if __name__ == '__main__':
    mvdk()
    mvsinsq()
