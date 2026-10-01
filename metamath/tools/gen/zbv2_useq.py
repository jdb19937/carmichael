"""Sortie ZBV2, section 3 part B: uSeq and prod_one_add_uSeq_le (ZBV2-blueprint.md
section 3.2).  The tail product is bounded by an induction on the cleared
invariant 3 M P(M) <= 5 (M - 2) with the ratio bound
( 1 + u(n) ) n ( n - 3 ) <= ( n - 1 ) ( n - 2 ) (bvuseqrat); the head
prod_ ( 2 ... 5 ) is evaluated numerically.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *
import num
import lin
lin.MAXDEG = 5

X = lambda n: '( 1 + %s )' % U(n)
PT = lambda lo, m: 'prod_ n e. ( %s ... %s ) %s' % (lo, m, X('n'))
NUMe = lambda n: '( ( 2 x. %s ) - 1 )' % n
DENe = lambda n: '( %s x. ( ( %s - 1 ) ^ 2 ) )' % (n, n)
PHI = lambda x: '( ( 3 x. %s ) x. %s ) <_ ( 5 x. ( %s - 2 ) )' % (x, PT('6', x), x)


def ufacts(w, ante, nre, n2, n, lv=None):
    """from nre: ( ante -> n e. RR ), n2: ( ante -> 2 <_ n ): closures of u(n), X(n) = 1 + u(n), 0 <_ u(n), 1 <_ X(n)"""
    st = mkst(w, ante)
    L = dict(lv or {}); L[n] = nre
    one = st([], '1red', '1 e. RR')
    nume = st([st([w.s([num.re_nat(w, 2)], 'a1i', '( %s -> 2 e. RR )' % ante), nre], 'remulcld', '( 2 x. %s ) e. RR' % n), one], 'resubcld', '%s e. RR' % NUMe(n))
    num0 = linarith(w, ante, [n2], '0 <_ %s' % NUMe(n), leaves=L)
    nrp = st([nre, linarith(w, ante, [n2], '0 < %s' % n, leaves=L)], 'elrpd', '%s e. RR+' % n)
    n1 = '( %s - 1 )' % n
    n1re = st([nre, one], 'resubcld', '%s e. RR' % n1)
    n1gt = linarith(w, ante, [n2], '0 < %s' % n1, leaves=L)
    sqgt = st([n1re, st([n1gt], 'gt0ne0d', '%s =/= 0' % n1)], 'sqgt0d', '0 < ( %s ^ 2 )' % n1)
    sqre = st([n1re, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ante)], 'reexpcld', '( %s ^ 2 ) e. RR' % n1)
    sqrp = st([sqre, sqgt], 'elrpd', '( %s ^ 2 ) e. RR+' % n1)
    denrp = st([nrp, sqrp], 'rpmulcld', '%s e. RR+' % DENe(n))
    ure = st([nume, denrp], 'rerpdivcld', '%s e. RR' % U(n))
    u0 = st([nume, denrp, num0], 'divge0d', '0 <_ %s' % U(n))
    xre = st([one, ure], 'readdcld', '%s e. RR' % X(n))
    x1 = linarith(w, ante, [u0], '1 <_ %s' % X(n), leaves={U(n): ure})
    return dict(nume=nume, num0=num0, nrp=nrp, n1re=n1re, n1gt=n1gt, sqre=sqre, sqrp=sqrp, denrp=denrp, ure=ure, u0=u0,
                xre=xre, x1=x1, xcc=st([xre], 'recnd', '%s e. CC' % X(n)))


def bvuseq0():
    w = W('bvuseq0', 'uSeq is nonnegative (Lean uSeq_nonneg, for n >= 2).')
    A = 'N e. ( ZZ>= ` 2 )'
    nre = w.s([], 'eluzelre', '( %s -> N e. RR )' % A); n2 = w.s([], 'eluzle', '( %s -> 2 <_ N )' % A)
    f = ufacts(w, A, nre, n2, 'N')
    w.qed([f['u0'], w.inst('id')], 'syl', STATEMENTS['bvuseq0'])
    return w


def bvuseqrat():
    w = W('bvuseqrat', 'The ratio bound ( 1 + u(N) ) N ( N - 3 ) <= ( N - 1 ) ( N - 2 ) for N >= 4: the factors of the '
                       'tail product telescope (replaces the induction sum_uSeq_tail).')
    A = 'N e. ( ZZ>= ` 4 )'
    st = mkst(w, A)
    nre = w.s([], 'eluzelre', '( %s -> N e. RR )' % A); n4 = w.s([], 'eluzle', '( %s -> 4 <_ N )' % A)
    n2 = linarith(w, A, [n4], '2 <_ N', leaves={'N': nre})
    f = ufacts(w, A, nre, n2, 'N')
    n1 = '( N - 1 )'; SQ = '( %s ^ 2 )' % n1; SQM = '( %s x. %s )' % (n1, n1)
    D2 = '( N x. %s )' % SQM
    sqv = st([st([f['n1re']], 'recnd', '%s e. CC' % n1)], 'sqvald', '%s = %s' % (SQ, SQM))
    denc = st([f['denrp']], 'rpcnd', '%s e. CC' % DENe('N')); denne = st([f['denrp']], 'rpne0d', '%s =/= 0' % DENe('N'))
    hu0 = st([st([f['nume']], 'recnd', '%s e. CC' % NUMe('N')), denc, denne], 'divcan1d', '( %s x. %s ) = %s' % (U('N'), DENe('N'), NUMe('N')))
    eqd = st([st([sqv], 'oveq2d', '%s = %s' % (DENe('N'), D2))], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (U('N'), DENe('N'), U('N'), D2))
    hu = st([eqd, hu0], 'eqtr3d', '( %s x. %s ) = %s' % (U('N'), D2, NUMe('N')))
    h3 = linarith(w, A, [n4], '3 <_ N', leaves={'N': nre})
    L = '( %s x. ( N x. ( N - 3 ) ) )' % X('N'); R = '( %s x. ( N - 2 ) )' % n1
    goal = '( %s x. %s ) <_ ( %s x. %s )' % (L, SQM, R, SQM)
    gm = nlinarith(w, A, [hu, h3, n4], goal, leaves={'N': nre, U('N'): f['ure']}, atoms=[U('N')], cert={(hu, h3): 1, n4: 3})
    cl = Closure(w, A, {'N': nre, U('N'): f['ure']})
    cl.atom(U('N'))
    sqmrp = st([st([f['n1re'], f['n1gt']], 'elrpd', '%s e. RR+' % n1)] * 2, 'rpmulcld', '%s e. RR+' % SQM)
    bi = st([cl.mem(L, 'RR'), cl.mem(R, 'RR'), sqmrp], 'lemul1d', '( %s <_ %s <-> %s )' % (L, R, goal))
    w.qed([gm, bi], 'mpbird', STATEMENTS['bvuseqrat'])
    return w


def uzlift(w, ante, step, a, b, x):
    """from step: ( ante -> x e. ( ZZ>= ` a ) ) and a >= b (numerals): ( ante -> x e. ( ZZ>= ` b ) )"""
    st = mkst(w, ante)
    xz = sy(w, ante, step, 'eluzelz', '%s e. ZZ' % x)
    xle = sy(w, ante, step, 'eluzle', '%s <_ %s' % (a, x))
    xre = st([xz], 'zred', '%s e. RR' % x)
    le = linarith(w, ante, [xle], '%s <_ %s' % (b, x), leaves={x: xre})
    bz = st([num.z_nat(w, int(b))], 'a1i', '%s e. ZZ' % b)
    bi = sy2(w, ante, bz, xz, 'eluz', '( %s e. ( ZZ>= ` %s ) <-> %s <_ %s )' % (x, b, b, x))
    return st([le, bi], 'mpbird', '%s e. ( ZZ>= ` %s )' % (x, b))


def bvuprodind():
    w = W('bvuprodind', 'The tail invariant 3 M prod_ ( 6 ... M ) ( 1 + u(n) ) <= 5 ( M - 2 ) by induction on M >= 6 '
                        '(replaces sum_uSeq_tail and the exp(1/2) estimate of prod_one_add_uSeq_le).')
    # the substitution hypotheses of uzind4
    subs = []
    for T in ('6', 'k', '( k + 1 )', 'M'):
        idj = w.s([], 'id', '( j = %s -> j = %s )' % (T, T))
        s, new = w.wcongr(PHI('j'), {'j': T}, 'j = %s' % T, {'j': idj})
        subs.append(s)
    # base M = 6
    B = '6 e. ZZ'
    sb = mkst(w, B)
    sx, fr6 = fracev(w, U('6'))
    x6 = '( 1 + %s )' % fr6
    x6eq = num.closed(w, [sx], 'oveq2i', '%s = %s' % (X('6'), x6))
    x6c = num.closed(w, [x6eq, num.closed(w, [num.closed(w, [], 'ax-1cn', '1 e. CC'), num.cc(w, fr6)], 'addcli', '%s e. CC' % x6)], 'eqeltri', '%s e. CC' % X('6'))
    idn = w.s([], 'id', '( n = 6 -> n = 6 )')
    cg, _ = w.congr(X('n'), {'n': '6'}, 'n = 6', {'n': idn})
    f1 = w.s([cg], 'fprod1', '( ( 6 e. ZZ /\\ %s e. CC ) -> %s = %s )' % (X('6'), PT('6', '6'), X('6')))
    p6 = w.s([w.s([], 'id', '( %s -> 6 e. ZZ )' % B), sb([x6c], 'a1i', '%s e. CC' % X('6')), f1], 'syl2anc', '( %s -> %s = %s )' % (B, PT('6', '6'), X('6')))
    p6v = sb([p6, sb([x6eq], 'a1i', '%s = %s' % (X('6'), x6))], 'eqtrd', '%s = %s' % (PT('6', '6'), x6))
    lit = linarith(w, B, [], '( ( 3 x. 6 ) x. %s ) <_ ( 5 x. ( 6 - 2 ) )' % x6, products=True)
    base = sb([sb([p6v], 'oveq2d', '( ( 3 x. 6 ) x. %s ) = ( ( 3 x. 6 ) x. %s )' % (PT('6', '6'), x6)), lit], 'eqbrtrd', PHI('6'))
    # step
    AK = '( k e. ( ZZ>= ` 6 ) /\\ %s )' % PHI('k')
    sk = mkst(w, AK)
    kuz = sk([], 'simpl', 'k e. ( ZZ>= ` 6 )'); hch = sk([], 'simpr', PHI('k'))
    kre = sy(w, AK, kuz, 'eluzelre', 'k e. RR'); k6 = sy(w, AK, kuz, 'eluzle', '6 <_ k')
    K1 = '( k + 1 )'
    k1uz = sy(w, AK, kuz, 'peano2uz', '%s e. ( ZZ>= ` 6 )' % K1)
    k1uz4 = uzlift(w, AK, k1uz, '6', '4', K1)
    k1re = sk([kre, sk([], '1red', '1 e. RR')], 'readdcld', '%s e. RR' % K1)
    rat_c = STATEMENTS['bvuseqrat'].split(' -> ', 1)[1][:-2]
    rat = sy(w, AK, k1uz4, 'bvuseqrat', ' '.join(rat_c.replace('N', K1).split()))
    # the product facts under K0 = k e. ( ZZ>= ` 6 ) alone (AK binds n inside PHI(k))
    K0 = 'k e. ( ZZ>= ` 6 )'
    s0 = mkst(w, K0)
    def fac(hi):
        AN = '( %s /\\ n e. ( 6 ... %s ) )' % (K0, hi); sn = mkst(w, AN)
        nel = sn([], 'simpr', 'n e. ( 6 ... %s )' % hi)
        nre = sn([sy(w, AN, nel, 'elfzelz', 'n e. ZZ')], 'zred', 'n e. RR')
        n6 = sy(w, AN, nel, 'elfzle1', '6 <_ n')
        n2 = linarith(w, AN, [n6], '2 <_ n', leaves={'n': nre})
        return ufacts(w, AN, nre, n2, 'n'), AN
    fk1, _ = fac(K1)
    fk, ANk = fac('k')
    kuz0 = w.s([], 'id', '( %s -> %s )' % (K0, K0))
    idn1 = w.s([], 'id', '( n = %s -> n = %s )' % (K1, K1))
    cgk, _ = w.congr(X('n'), {'n': K1}, 'n = %s' % K1, {'n': idn1})
    pp1 = lift(w, w.s([kuz0, fk1['xcc'], cgk], 'fprodp1', '( %s -> %s = ( %s x. %s ) )' % (K0, PT('6', K1), PT('6', 'k'), X(K1))), AK)
    fin = s0([], 'fzfid', '( 6 ... k ) e. Fin')
    ptre = lift(w, s0([fin, fk['xre']], 'fprodrecl', '%s e. RR' % PT('6', 'k')), AK)
    x0 = linarith(w, ANk, [fk['x1']], '0 <_ %s' % X('n'), leaves={U('n'): fk['ure']})
    hP = lift(w, s0([w.s([], 'nfv', 'F/ n %s' % K0), fin, fk['xre'], x0], 'fprodge0', '0 <_ %s' % PT('6', 'k')), AK)
    hk1 = linarith(w, AK, [k6], '1 <_ k', leaves={'k': kre})
    # u(k+1) closures directly under AK
    k12 = linarith(w, AK, [k6], '2 <_ %s' % K1, leaves={'k': kre})
    fx = ufacts(w, AK, k1re, k12, K1, lv={'k': kre})
    PK = PT('6', 'k')
    LHS = '( ( 3 x. %s ) x. ( %s x. %s ) )' % (K1, PK, X(K1)); RHS = '( 5 x. ( %s - 2 ) )' % K1
    goal = '( %s x. ( k - 2 ) ) <_ ( %s x. ( k - 2 ) )' % (LHS, RHS)
    lv = {'k': kre, PK: ptre, U(K1): fx['ure']}
    gm = nlinarith(w, AK, [rat, hP, hch, hk1], goal, leaves=lv, atoms=[PK, U(K1)], cert={(rat, hP): 3, (hch, hk1): 1})
    cl = Closure(w, AK, lv); cl.atom(PK); cl.atom(U(K1))
    k2rp = sk([sk([kre, w.s([num.re_nat(w, 2)], 'a1i', '( %s -> 2 e. RR )' % AK)], 'resubcld', '( k - 2 ) e. RR'), linarith(w, AK, [k6], '0 < ( k - 2 )', leaves={'k': kre})], 'elrpd', '( k - 2 ) e. RR+')
    bi = sk([cl.mem(LHS, 'RR'), cl.mem(RHS, 'RR'), k2rp], 'lemul1d', '( %s <_ %s <-> %s )' % (LHS, RHS, goal))
    le = sk([gm, bi], 'mpbird', '%s <_ %s' % (LHS, RHS))
    eq = sk([pp1], 'oveq2d', '( ( 3 x. %s ) x. %s ) = %s' % (K1, PT('6', K1), LHS))
    th = sk([eq, le], 'eqbrtrd', PHI(K1))
    step = w.s([th], 'ex', '( k e. ( ZZ>= ` 6 ) -> ( %s -> %s ) )' % (PHI('k'), PHI(K1)))
    w.qed(subs + [base, step], 'uzind4', STATEMENTS['bvuprodind'])
    return w


def bvuprodtail():
    w = W('bvuprodtail', 'prod_ ( 6 ... M ) ( 1 + u(n) ) <= 5 / 3 (from the invariant bvuprodind).')
    A = 'M e. ( ZZ>= ` 6 )'
    st = mkst(w, A)
    hind = w.s([], 'bvuprodind', STATEMENTS['bvuprodind'])
    mre = w.s([], 'eluzelre', '( %s -> M e. RR )' % A); m6 = w.s([], 'eluzle', '( %s -> 6 <_ M )' % A)
    AN = '( %s /\\ n e. ( 6 ... M ) )' % A; sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. ( 6 ... M )')
    nre = sn([sy(w, AN, nel, 'elfzelz', 'n e. ZZ')], 'zred', 'n e. RR')
    n2 = linarith(w, AN, [sy(w, AN, nel, 'elfzle1', '6 <_ n')], '2 <_ n', leaves={'n': nre})
    f = ufacts(w, AN, nre, n2, 'n')
    P = PT('6', 'M')
    pre = st([st([], 'fzfid', '( 6 ... M ) e. Fin'), f['xre']], 'fprodrecl', '%s e. RR' % P)
    C = '( 3 x. M )'
    goal = '( %s x. %s ) <_ ( ( 5 / 3 ) x. %s )' % (P, C, C)
    gm = linarith(w, A, [hind], goal, leaves={'M': mre, P: pre}, atoms=[P], products=True)
    cl = Closure(w, A, {'M': mre, P: pre}); cl.atom(P)
    crp = st([w.s([w.s([], '3rp', '3 e. RR+')], 'a1i', '( %s -> 3 e. RR+ )' % A),
              st([mre, linarith(w, A, [m6], '0 < M', leaves={'M': mre})], 'elrpd', 'M e. RR+')], 'rpmulcld', '%s e. RR+' % C)
    bi = st([pre, cl.mem('( 5 / 3 )', 'RR'), crp], 'lemul1d', '( %s <_ ( 5 / 3 ) <-> %s )' % (P, goal))
    w.qed([gm, bi], 'mpbird', STATEMENTS['bvuprodtail'])
    return w


def bvuprod5():
    w = W('bvuprod5', 'prod_ ( 2 ... 5 ) ( 1 + u(n) ) = 65059 / 13824 <= 24 / 5 (numerical head of prod_one_add_uSeq_le).')
    T = 'T.'
    st = mkst(w, T)
    # prod ( 2 ... m ) = ( prod ( 2 ... ( m - 1 ) ) x. X(m) ), m = 5, 4, 3; prod ( 2 ... 2 ) = X(2)
    idn = w.s([], 'id', '( n = 2 -> n = 2 )')
    cg, _ = w.congr(X('n'), {'n': '2'}, 'n = 2', {'n': idn})
    vals = {}
    for m in (2, 3, 4, 5):
        sx, fr = fracev(w, U(str(m)))
        vals[m] = (sx, fr)
    def xcc(m):
        sx, fr = vals[m]
        xv = '( 1 + %s )' % fr
        eq = num.closed(w, [sx], 'oveq2i', '%s = %s' % (X(str(m)), xv))
        c = num.closed(w, [eq, num.closed(w, [num.closed(w, [], 'ax-1cn', '1 e. CC'), num.cc(w, fr)], 'addcli', '%s e. CC' % xv)], 'eqeltri', '%s e. CC' % X(str(m)))
        return eq, c
    eq2, c2 = xcc(2)
    f1 = w.s([cg], 'fprod1', '( ( 2 e. ZZ /\\ %s e. CC ) -> %s = %s )' % (X('2'), PT('2', '2'), X('2')))
    cur = w.s([w.s([w.s([], '2z', '2 e. ZZ'), c2], 'pm3.2i', '( 2 e. ZZ /\\ %s e. CC )' % X('2')), f1], 'ax-mp', '%s = %s' % (PT('2', '2'), X('2')))
    cur = st([cur], 'a1i', '%s = %s' % (PT('2', '2'), X('2')))
    expr = X('2')
    for m in (3, 4, 5):
        pm = str(m - 1)
        # fprodp1 at N = m - 1
        AN = '( %s /\\ n e. ( 2 ... ( %s + 1 ) ) )' % (T, pm); sn = mkst(w, AN)
        nel = sn([], 'simpr', 'n e. ( 2 ... ( %s + 1 ) )' % pm)
        nre = sn([sy(w, AN, nel, 'elfzelz', 'n e. ZZ')], 'zred', 'n e. RR')
        f = ufacts(w, AN, nre, sy(w, AN, nel, 'elfzle1', '2 <_ n'), 'n')
        idp = w.s([], 'id', '( n = ( %s + 1 ) -> n = ( %s + 1 ) )' % (pm, pm))
        cgp, _ = w.congr(X('n'), {'n': '( %s + 1 )' % pm}, 'n = ( %s + 1 )' % pm, {'n': idp})
        uz = uzlift(w, T, st([w.s([num.z_nat(w, m - 1), w.inst('uzid')], 'ax-mp', '%s e. ( ZZ>= ` %s )' % (pm, pm))], 'a1i', '%s e. ( ZZ>= ` %s )' % (pm, pm)), pm, '2', pm)
        pp = w.s([uz, f['xcc'], cgp], 'fprodp1', '( %s -> %s = ( %s x. %s ) )' % (T, PT('2', '( %s + 1 )' % pm), PT('2', pm), X('( %s + 1 )' % pm)))
        ad = num.add_nat(w, m - 1, 1)
        ieq = num.closed(w, [ad], 'oveq2i', '( 2 ... ( %s + 1 ) ) = ( 2 ... %d )' % (pm, m))
        peq = num.closed(w, [ieq], 'prodeq1i', '%s = %s' % (PT('2', '( %s + 1 )' % pm), PT('2', str(m))))
        # X( ( pm + 1 ) ) = X( m ) by congruence on the numeral
        s1 = st([st([peq], 'a1i', '%s = %s' % (PT('2', '( %s + 1 )' % pm), PT('2', str(m)))), pp], 'eqtr3d', '%s = ( %s x. %s )' % (PT('2', str(m)), PT('2', pm), X('( %s + 1 )' % pm)))
        # rewrite ( pm + 1 ) -> m inside X, and prod ( 2 ... pm ) -> expr
        adt = st([ad], 'a1i', '( %s + 1 ) = %d' % (pm, m))
        rw, new = w.rewrite('( %s x. %s )' % (PT('2', pm), X('( %s + 1 )' % pm)), {'( %s + 1 )' % pm: (str(m), adt), PT('2', pm): (expr, cur)}, T)
        expr = '( %s x. %s )' % (expr, X(str(m)))
        assert new == expr, (new, expr)
        cur = st([s1, rw], 'eqtrd', '%s = %s' % (PT('2', str(m)), expr))
    # evaluate
    rules = {}
    for m in (2, 3, 4, 5):
        sx, fr = vals[m]
        rules[U(str(m))] = (fr, st([sx], 'a1i', '%s = %s' % (U(str(m)), fr)))
    rw, lit = w.rewrite(expr, rules, T)
    le = linarith(w, T, [], '%s <_ ( ; 2 4 / 5 )' % lit, products=True)
    fin = st([st([cur, rw], 'eqtrd', '%s = %s' % (PT('2', '5'), lit)), le], 'eqbrtrd', STATEMENTS['bvuprod5'])
    w.qed([fin], 'mptru', STATEMENTS['bvuprod5'])
    return w


def bvuprod():
    w = W('bvuprod', 'prod_ ( 2 ... M ) ( 1 + u(n) ) <= 8 (Lean prod_one_add_uSeq_le).')
    A = 'M e. NN'
    st = mkst(w, A)
    mnn = w.s([], 'id', '( %s -> M e. NN )' % A)
    mre = st([mnn], 'nnred', 'M e. RR'); mz = st([mnn], 'nnzd', 'M e. ZZ')
    five = st([w.s([], '5re', '5 e. RR')], 'a1i', '5 e. RR')
    fivez = st([num.z_nat(w, 5)], 'a1i', '5 e. ZZ')
    tri = sy2(w, A, mre, five, 'lelttric', '( M <_ 5 \\/ 5 < M )')
    P25 = PT('2', '5'); c5 = w.s([], 'bvuprod5', STATEMENTS['bvuprod5'])

    def facs(ante, hi):
        AN = '( %s /\\ n e. ( 2 ... %s ) )' % (ante, hi); sn = mkst(w, AN)
        nel = sn([], 'simpr', 'n e. ( 2 ... %s )' % hi)
        nre = sn([sy(w, AN, nel, 'elfzelz', 'n e. ZZ')], 'zred', 'n e. RR')
        return ufacts(w, AN, nre, sy(w, AN, nel, 'elfzle1', '2 <_ n'), 'n')
    # case M <_ 5
    A1 = '( %s /\\ M <_ 5 )' % A; s1 = mkst(w, A1)
    f25 = facs(A1, '5'); f2m = facs(A1, 'M')
    m5 = s1([], 'simpr', 'M <_ 5')
    uz5 = s1([m5, sy2(w, A1, lift(w, mz, A1), lift(w, fivez, A1), 'eluz', '( 5 e. ( ZZ>= ` M ) <-> M <_ 5 )')], 'mpbird', '5 e. ( ZZ>= ` M )')
    ss = sy(w, A1, uz5, 'fzss2', '( 2 ... M ) C_ ( 2 ... 5 )')
    le1 = w.s([s1([], 'fzfid', '( 2 ... 5 ) e. Fin'), ss, f25['xre'], f25['x1']], 'bvprodle1', '( %s -> %s <_ %s )' % (A1, PT('2', 'M'), P25))
    p2mr = s1([s1([], 'fzfid', '( 2 ... M ) e. Fin'), f2m['xre']], 'fprodrecl', '%s e. RR' % PT('2', 'M'))
    p25r = s1([s1([], 'fzfid', '( 2 ... 5 ) e. Fin'), f25['xre']], 'fprodrecl', '%s e. RR' % P25)
    c1 = linarith(w, A1, [le1, s1([c5], 'a1i', STATEMENTS['bvuprod5'])], '%s <_ 8' % PT('2', 'M'), leaves={PT('2', 'M'): p2mr, P25: p25r})
    # case 5 < M
    A2 = '( %s /\\ 5 < M )' % A; s2 = mkst(w, A2)
    lt = s2([], 'simpr', '5 < M')
    mz2 = lift(w, mz, A2); mre2 = lift(w, mre, A2)
    p1 = s2([lt, sy2(w, A2, lift(w, fivez, A2), mz2, 'zltp1le', '( 5 < M <-> ( 5 + 1 ) <_ M )')], 'mpbid', '( 5 + 1 ) <_ M')
    m6 = s2([s2([w.s([], '5p1e6', '( 5 + 1 ) = 6')], 'a1i', '( 5 + 1 ) = 6'), p1], 'eqbrtrrd', '6 <_ M')
    sixz = s2([num.z_nat(w, 6)], 'a1i', '6 e. ZZ')
    muz6 = s2([m6, sy2(w, A2, sixz, mz2, 'eluz', '( M e. ( ZZ>= ` 6 ) <-> 6 <_ M )')], 'mpbird', 'M e. ( ZZ>= ` 6 )')
    five_in = s2([s2([num.z_nat(w, 2)], 'a1i', '2 e. ZZ'), mz2, lift(w, fivez, A2), s2([num.le_nat(w, 2, 5)], 'a1i', '2 <_ 5'), linarith(w, A2, [lt], '5 <_ M', leaves={'M': mre2})],
                 'elfzd', '5 e. ( 2 ... M )')
    spl = sy(w, A2, five_in, 'fzsplit', '( 2 ... M ) = ( ( 2 ... 5 ) u. ( ( 5 + 1 ) ... M ) )')
    rw6, new6 = w.rewrite('( ( 2 ... 5 ) u. ( ( 5 + 1 ) ... M ) )', {'( 5 + 1 )': ('6', s2([w.s([], '5p1e6', '( 5 + 1 ) = 6')], 'a1i', '( 5 + 1 ) = 6'))}, A2)
    un = s2([spl, rw6], 'eqtrd', '( 2 ... M ) = %s' % new6)
    dj = s2([w.s([w.s([], '5lt6', '5 < 6'), w.inst('fzdisj')], 'ax-mp', '( ( 2 ... 5 ) i^i ( 6 ... M ) ) = (/)')], 'a1i', '( ( 2 ... 5 ) i^i ( 6 ... M ) ) = (/)')
    f2m2 = facs(A2, 'M')
    split = s2([dj, un, s2([], 'fzfid', '( 2 ... M ) e. Fin'), f2m2['xcc']], 'fprodsplit', '%s = ( %s x. %s )' % (PT('2', 'M'), P25, PT('6', 'M')))
    f25b = facs(A2, '5')
    A6 = '( %s /\\ n e. ( 6 ... M ) )' % A2; s6 = mkst(w, A6)
    nel6 = s6([], 'simpr', 'n e. ( 6 ... M )')
    nre6 = s6([sy(w, A6, nel6, 'elfzelz', 'n e. ZZ')], 'zred', 'n e. RR')
    f6 = ufacts(w, A6, nre6, linarith(w, A6, [sy(w, A6, nel6, 'elfzle1', '6 <_ n')], '2 <_ n', leaves={'n': nre6}), 'n')
    x06 = linarith(w, A6, [f6['x1']], '0 <_ %s' % X('n'), leaves={U('n'): f6['ure']})
    A5 = '( %s /\\ n e. ( 2 ... 5 ) )' % A2
    x05 = linarith(w, A5, [f25b['x1']], '0 <_ %s' % X('n'), leaves={U('n'): f25b['ure']})
    p25r2 = s2([s2([], 'fzfid', '( 2 ... 5 ) e. Fin'), f25b['xre']], 'fprodrecl', '%s e. RR' % P25)
    p6r = s2([s2([], 'fzfid', '( 6 ... M ) e. Fin'), f6['xre']], 'fprodrecl', '%s e. RR' % PT('6', 'M'))
    p250 = s2([w.s([], 'nfv', 'F/ n %s' % A2), s2([], 'fzfid', '( 2 ... 5 ) e. Fin'), f25b['xre'], x05], 'fprodge0', '0 <_ %s' % P25)
    p60 = s2([w.s([], 'nfv', 'F/ n %s' % A2), s2([], 'fzfid', '( 6 ... M ) e. Fin'), f6['xre'], x06], 'fprodge0', '0 <_ %s' % PT('6', 'M'))
    cl = Closure(w, A2, {})
    tail = sy(w, A2, muz6, 'bvuprodtail', '%s <_ ( 5 / 3 )' % PT('6', 'M'))
    mul = s2([p25r2, cl.mem('( ; 2 4 / 5 )', 'RR'), p6r, cl.mem('( 5 / 3 )', 'RR'), p250, p60, s2([c5], 'a1i', STATEMENTS['bvuprod5']), tail], 'lemul12ad',
             '( %s x. %s ) <_ ( ( ; 2 4 / 5 ) x. ( 5 / 3 ) )' % (P25, PT('6', 'M')))
    prr = s2([p25r2, p6r], 'remulcld', '( %s x. %s ) e. RR' % (P25, PT('6', 'M')))
    m8 = linarith(w, A2, [mul], '( %s x. %s ) <_ 8' % (P25, PT('6', 'M')), leaves={'( %s x. %s )' % (P25, PT('6', 'M')): prr}, atoms=['( %s x. %s )' % (P25, PT('6', 'M'))], products=True)
    c2 = s2([split, m8], 'eqbrtrd', '%s <_ 8' % PT('2', 'M'))
    w.qed([c1, c2, tri], 'mpjaodan', STATEMENTS['bvuprod'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvuseq0', 'bvuseqrat', 'bvuprodind', 'bvuprodtail', 'bvuprod5', 'bvuprod']:
        globals()[f]().run()
