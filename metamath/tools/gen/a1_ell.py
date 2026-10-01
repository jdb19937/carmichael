"""Sortie A1, batch 2: ell2 = log log n and ell3 = log log log n: values, reality and positivity thresholds, monotonicity, growth."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..')); import a1lib; from tm import *
only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

L = lambda X: '( log ` %s )' % X
E2 = lambda N: '( ell2 ` %s )' % N
E3 = lambda N: '( ell3 ` %s )' % N
UZ = lambda k, N: '%s e. ( ZZ>= ` %s )' % (N, k)

# ---- values
w = W('ell2val', 'Value of ell2: log log N (Lean: ell2).')
l1 = w.s([], 'id', '( n = N -> n = N )')
c, b = w.congr(L(L('n')), {'n': 'N'}, 'n = N', {'n': l1}); assert b == L(L('N'))
d = w.s([], 'df-ell2', 'ell2 = ( n e. NN0 |-> %s )' % L(L('n')))
x = w.s([], 'fvex', '%s e. _V' % L(L('N')))
w.qed([c, d, x], 'fvmpt', '( N e. NN0 -> %s = %s )' % (E2('N'), L(L('N')))); run(w)

w = W('ell3val', 'Value of ell3: log of ell2 N (Lean: ell3).')
l1 = w.s([], 'id', '( n = N -> n = N )')
c, b = w.congr(L(E2('n')), {'n': 'N'}, 'n = N', {'n': l1}); assert b == L(E2('N'))
d = w.s([], 'df-ell3', 'ell3 = ( n e. NN0 |-> %s )' % L(E2('n')))
x = w.s([], 'fvex', '%s e. _V' % L(E2('N')))
w.qed([c, d, x], 'fvmpt', '( N e. NN0 -> %s = %s )' % (E3('N'), L(E2('N')))); run(w)


def logn_rp(w, A, n2):
    """from step n2: ( A -> N e. ( ZZ>= ` 2 ) ) derive N e. NN0, N e. RR+, ( log ` N ) e. RR+; returns (n0, nrp, lrp)"""
    nn = w.s([n2, w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % A)
    n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A)
    nrp = w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % A)
    gt1 = w.s([n2, w.inst('eluz2gt1')], 'syl', '( %s -> 1 < N )' % A)
    lb = w.s([nrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < %s <-> 1 < N ) )' % (A, L('N')))
    lgt = w.s([gt1, lb], 'mpbird', '( %s -> 0 < %s )' % (A, L('N')))
    lr = w.s([nrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A, L('N')))
    lrp = w.s([lr, lgt], 'elrpd', '( %s -> %s e. RR+ )' % (A, L('N')))
    return n0, nrp, lrp

# ---- ell2cl
w = W('ell2cl', 'ell2 N is real for N >= 2 (log N is positive).')
A = UZ('2', 'N')
n2 = w.s([], 'id', '( %s -> %s )' % (A, A))
n0, nrp, lrp = logn_rp(w, A, n2)
v = w.s([n0, w.inst('ell2val')], 'syl', '( %s -> %s = %s )' % (A, E2('N'), L(L('N'))))
llr = w.s([lrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A, L(L('N'))))
w.qed([v, llr], 'eqeltrd', '( %s -> %s e. RR )' % (A, E2('N'))); run(w)

# ---- ell2rp
w = W('ell2rp', 'ell2 N is a positive real for N >= 3 (log N > 1 since _e < 3; ScalesTM.lean hl2pos).')
A = UZ('3', 'N')
n3 = w.s([], 'id', '( %s -> %s )' % (A, A))
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> %s )' % (A, UZ('2', 'N')))
n0, nrp, lrp = logn_rp(w, A, n2)
v = w.s([n0, w.inst('ell2val')], 'syl', '( %s -> %s = %s )' % (A, E2('N'), L(L('N'))))
er = w.s([], 'ere', '_e e. RR'); erd = w.s([er], 'a1i', '( %s -> _e e. RR )' % A)
tr = w.s([], '3re', '3 e. RR'); trd = w.s([tr], 'a1i', '( %s -> 3 e. RR )' % A)
nr = w.s([nrp], 'rpred', '( %s -> N e. RR )' % A)
e3 = w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )'); e3b = w.s([e3], 'simpri', '_e < 3'); e3d = w.s([e3b], 'a1i', '( %s -> _e < 3 )' % A)
n3le = w.s([n3, w.inst('eluzle')], 'syl', '( %s -> 3 <_ N )' % A)
en = w.s([erd, trd, nr, e3d, n3le], 'ltletrd', '( %s -> _e < N )' % A)
ep = w.s([], 'epr', '_e e. RR+'); epd = w.s([ep], 'a1i', '( %s -> _e e. RR+ )' % A)
lb = w.s([epd, nrp, w.inst('logltb')], 'syl2anc', '( %s -> ( _e < N <-> ( log ` _e ) < %s ) )' % (A, L('N')))
le = w.s([en, lb], 'mpbid', '( %s -> ( log ` _e ) < %s )' % (A, L('N')))
lg = w.s([], 'loge', '( log ` _e ) = 1'); lgd = w.s([lg], 'a1i', '( %s -> ( log ` _e ) = 1 )' % A)
l1 = w.s([lgd, le], 'eqbrtrrd', '( %s -> 1 < %s )' % (A, L('N')))
lb2 = w.s([lrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < %s <-> 1 < %s ) )' % (A, L(L('N')), L('N')))
gt0 = w.s([l1, lb2], 'mpbird', '( %s -> 0 < %s )' % (A, L(L('N'))))
llr = w.s([lrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A, L(L('N'))))
rp = w.s([llr, gt0], 'elrpd', '( %s -> %s e. RR+ )' % (A, L(L('N'))))
w.qed([v, rp], 'eqeltrd', '( %s -> %s e. RR+ )' % (A, E2('N'))); run(w)

w = W('ell2gt0', 'ell2 N is positive for N >= 3.')
A = UZ('3', 'N')
r = w.s([], 'ell2rp', '( %s -> %s e. RR+ )' % (A, E2('N')))
w.qed([r], 'rpgt0d', '( %s -> 0 < %s )' % (A, E2('N'))); run(w)

w = W('ell3cl', 'ell3 N is real for N >= 3.')
A = UZ('3', 'N')
n3 = w.s([], 'id', '( %s -> %s )' % (A, A))
n2 = w.s([n3, w.inst('uzuzle23')], 'syl', '( %s -> %s )' % (A, UZ('2', 'N')))
nn = w.s([n2, w.inst('eluz2nn')], 'syl', '( %s -> N e. NN )' % A); n0 = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A)
v = w.s([n0, w.inst('ell3val')], 'syl', '( %s -> %s = %s )' % (A, E3('N'), L(E2('N'))))
r = w.s([], 'ell2rp', '( %s -> %s e. RR+ )' % (A, E2('N')))
lr = w.s([r, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A, L(E2('N'))))
w.qed([v, lr], 'eqeltrd', '( %s -> %s e. RR )' % (A, E3('N'))); run(w)

# ---- ell2le: monotone
w = W('ell2le', 'ell2 is monotone for arguments >= 2 (Lean: Real.log_le_log twice; ScalesTM.lean hlogM_lo).')
A = '( %s /\\ %s )' % (UZ('2', 'M'), UZ('M', 'N'))
m2 = w.s([], 'simpl', '( %s -> %s )' % (A, UZ('2', 'M'))); nm = w.s([], 'simpr', '( %s -> %s )' % (A, UZ('M', 'N')))
n2 = w.s([nm, m2, w.inst('uztrn')], 'syl2anc', '( %s -> %s )' % (A, UZ('2', 'N')))
def prefix(w, A, u2, X):
    nn = w.s([u2, w.inst('eluz2nn')], 'syl', '( %s -> %s e. NN )' % (A, X))
    n0 = w.s([nn], 'nnnn0d', '( %s -> %s e. NN0 )' % (A, X)); nrp = w.s([nn], 'nnrpd', '( %s -> %s e. RR+ )' % (A, X))
    gt1 = w.s([u2, w.inst('eluz2gt1')], 'syl', '( %s -> 1 < %s )' % (A, X))
    lb = w.s([nrp, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < %s <-> 1 < %s ) )' % (A, L(X), X))
    lgt = w.s([gt1, lb], 'mpbird', '( %s -> 0 < %s )' % (A, L(X)))
    lr = w.s([nrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A, L(X)))
    lrp = w.s([lr, lgt], 'elrpd', '( %s -> %s e. RR+ )' % (A, L(X)))
    v = w.s([n0, w.inst('ell2val')], 'syl', '( %s -> %s = %s )' % (A, E2(X), L(L(X))))
    return nrp, lrp, v
mrp, lmrp, vm = prefix(w, A, m2, 'M'); nrp, lnrp, vn = prefix(w, A, n2, 'N')
mn = w.s([nm, w.inst('eluzle')], 'syl', '( %s -> M <_ N )' % A)
b1 = w.s([mrp, nrp, w.inst('logleb')], 'syl2anc', '( %s -> ( M <_ N <-> %s <_ %s ) )' % (A, L('M'), L('N')))
l1 = w.s([mn, b1], 'mpbid', '( %s -> %s <_ %s )' % (A, L('M'), L('N')))
b2 = w.s([lmrp, lnrp, w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (A, L('M'), L('N'), L(L('M')), L(L('N'))))
l2 = w.s([l1, b2], 'mpbid', '( %s -> %s <_ %s )' % (A, L(L('M')), L(L('N'))))
e1 = w.s([vm, l2], 'eqbrtrd', '( %s -> %s <_ %s )' % (A, E2('M'), L(L('N'))))
w.qed([e1, vn], 'breqtrrd', '( %s -> %s <_ %s )' % (A, E2('M'), E2('N'))); run(w)

# ---- ell3le
w = W('ell3le', 'ell3 is monotone for arguments >= 3.')
A = '( %s /\\ %s )' % (UZ('3', 'M'), UZ('M', 'N'))
m3 = w.s([], 'simpl', '( %s -> %s )' % (A, UZ('3', 'M'))); nm = w.s([], 'simpr', '( %s -> %s )' % (A, UZ('M', 'N')))
n3 = w.s([nm, m3, w.inst('uztrn')], 'syl2anc', '( %s -> %s )' % (A, UZ('3', 'N')))
m2 = w.s([m3, w.inst('uzuzle23')], 'syl', '( %s -> %s )' % (A, UZ('2', 'M')))
le2 = w.s([m2, nm, w.inst('ell2le')], 'syl2anc', '( %s -> %s <_ %s )' % (A, E2('M'), E2('N')))
rm = w.s([m3, w.inst('ell2rp')], 'syl', '( %s -> %s e. RR+ )' % (A, E2('M'))); rn = w.s([n3, w.inst('ell2rp')], 'syl', '( %s -> %s e. RR+ )' % (A, E2('N')))
b = w.s([rm, rn, w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (A, E2('M'), E2('N'), L(E2('M')), L(E2('N'))))
l = w.s([le2, b], 'mpbid', '( %s -> %s <_ %s )' % (A, L(E2('M')), L(E2('N'))))
def n0of(w, A, u3, X):
    u2 = w.s([u3, w.inst('uzuzle23')], 'syl', '( %s -> %s )' % (A, UZ('2', X)))
    nn = w.s([u2, w.inst('eluz2nn')], 'syl', '( %s -> %s e. NN )' % (A, X))
    return w.s([nn], 'nnnn0d', '( %s -> %s e. NN0 )' % (A, X))
m0 = n0of(w, A, m3, 'M'); n0 = n0of(w, A, n3, 'N')
vm = w.s([m0, w.inst('ell3val')], 'syl', '( %s -> %s = %s )' % (A, E3('M'), L(E2('M'))))
vn = w.s([n0, w.inst('ell3val')], 'syl', '( %s -> %s = %s )' % (A, E3('N'), L(E2('N'))))
e1 = w.s([vm, l], 'eqbrtrd', '( %s -> %s <_ %s )' % (A, E3('M'), L(E2('N'))))
w.qed([e1, vn], 'breqtrrd', '( %s -> %s <_ %s )' % (A, E3('M'), E3('N'))); run(w)

# ---- ell3lt: log x < x
w = W('ell3lt', 'ell3 N < ell2 N for N >= 3 (log x < x for positive x; Step2W.lean hlog2/hlog3).')
A = UZ('3', 'N')
n3 = w.s([], 'id', '( %s -> %s )' % (A, A)); n0 = n0of(w, A, n3, 'N')
X = E2('N')
xp = w.s([], 'ell2rp', '( %s -> %s e. RR+ )' % (A, X)); xr = w.s([xp], 'rpred', '( %s -> %s e. RR )' % (A, X)); xc = w.s([xr], 'recnd', '( %s -> %s e. CC )' % (A, X))
one = w.s([], '1red', '( %s -> 1 e. RR )' % A); onec = w.s([], '1cnd', '( %s -> 1 e. CC )' % A)
g = w.s([xp, w.inst('efgt1p')], 'syl', '( %s -> ( 1 + %s ) < ( exp ` %s ) )' % (A, X, X))
lt1 = w.s([xr, w.inst('ltp1')], 'syl', '( %s -> %s < ( %s + 1 ) )' % (A, X, X))
ac = w.s([xc, onec], 'addcomd', '( %s -> ( %s + 1 ) = ( 1 + %s ) )' % (A, X, X))
lt1b = w.s([lt1, ac], 'breqtrd', '( %s -> %s < ( 1 + %s ) )' % (A, X, X))
p1r = w.s([one, xr], 'readdcld', '( %s -> ( 1 + %s ) e. RR )' % (A, X))
er = w.s([xr], 'reefcld', '( %s -> ( exp ` %s ) e. RR )' % (A, X))
lt2 = w.s([xr, p1r, er, lt1b, g], 'lttrd', '( %s -> %s < ( exp ` %s ) )' % (A, X, X))
eg = w.s([xr, w.inst('efgt0')], 'syl', '( %s -> 0 < ( exp ` %s ) )' % (A, X)); erp = w.s([er, eg], 'elrpd', '( %s -> ( exp ` %s ) e. RR+ )' % (A, X))
b = w.s([xp, erp, w.inst('logltb')], 'syl2anc', '( %s -> ( %s < ( exp ` %s ) <-> %s < ( log ` ( exp ` %s ) ) ) )' % (A, X, X, L(X), X))
l = w.s([lt2, b], 'mpbid', '( %s -> %s < ( log ` ( exp ` %s ) ) )' % (A, L(X), X))
re = w.s([xr, w.inst('relogef')], 'syl', '( %s -> ( log ` ( exp ` %s ) ) = %s )' % (A, X, X))
l2 = w.s([l, re], 'breqtrd', '( %s -> %s < %s )' % (A, L(X), X))
v = w.s([n0, w.inst('ell3val')], 'syl', '( %s -> %s = %s )' % (A, E3('N'), L(X)))
w.qed([v, l2], 'eqbrtrd', '( %s -> %s < %s )' % (A, E3('N'), X)); run(w)

# ---- ell3ge0
w = W('ell3ge0', 'ell3 N is nonnegative when ell2 N >= 1 (Step2W.lean: positivity from the eventual thresholds).')
A = '( %s /\\ 1 <_ %s )' % (UZ('3', 'N'), E2('N'))
n3 = w.s([], 'simpl', '( %s -> %s )' % (A, UZ('3', 'N'))); h = w.s([], 'simpr', '( %s -> 1 <_ %s )' % (A, E2('N')))
n0 = n0of(w, A, n3, 'N')
xp = w.s([n3, w.inst('ell2rp')], 'syl', '( %s -> %s e. RR+ )' % (A, E2('N')))
b = w.s([xp, w.inst('logge0b')], 'syl', '( %s -> ( 0 <_ %s <-> 1 <_ %s ) )' % (A, L(E2('N')), E2('N')))
g = w.s([h, b], 'mpbird', '( %s -> 0 <_ %s )' % (A, L(E2('N'))))
v = w.s([n0, w.inst('ell3val')], 'syl', '( %s -> %s = %s )' % (A, E3('N'), L(E2('N'))))
w.qed([g, v], 'breqtrrd', '( %s -> 0 <_ %s )' % (A, E3('N'))); run(w)


# ---- ell2ge, ell3ge: growth (Tendsto ell2 atTop atTop via eventually_ge_atTop)
def growth(label, desc, depth):
    """depth 2: ell2; depth 3: ell3.  Witness m = ( Nceil ` ( X + depth ) ) with X = exp^depth B."""
    w = W(label, desc)
    EL = E2 if depth == 2 else E3
    Xs = 'B'
    for _ in range(depth): Xs = '( exp ` %s )' % Xs
    k = str(depth)
    M = '( Nceil ` ( %s + %s ) )' % (Xs, k)
    A0 = 'B e. RR'
    A = '( B e. RR /\\ n e. ( ZZ>= ` %s ) )' % M
    b = w.s([], 'simpl', '( %s -> B e. RR )' % A); nu = w.s([], 'simpr', '( %s -> n e. ( ZZ>= ` %s ) )' % (A, M))
    # the exponential tower: reals and positives
    tower = ['B']; reals = {'B': b}
    cur = 'B'
    for _ in range(depth):
        nxt = '( exp ` %s )' % cur
        reals[nxt] = w.s([reals[cur]], 'reefcld', '( %s -> %s e. RR )' % (A, nxt)); tower.append(nxt); cur = nxt
    X = cur; xr = reals[X]
    xgt = w.s([reals[tower[-2]], w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, X)); xrp = w.s([xr, xgt], 'elrpd', '( %s -> %s e. RR+ )' % (A, X))
    kr = w.s([], '%sre' % k, '%s e. RR' % k); krd = w.s([kr], 'a1i', '( %s -> %s e. RR )' % (A, k))
    xk = w.s([xr, krd], 'readdcld', '( %s -> ( %s + %s ) e. RR )' % (A, X, k))
    mle = w.s([xk, w.inst('nceilge')], 'syl', '( %s -> ( %s + %s ) <_ %s )' % (A, X, k, M))
    mn0 = w.s([xk, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (A, M)); mr = w.s([mn0], 'nn0red', '( %s -> %s e. RR )' % (A, M))
    nz = w.s([nu, w.inst('eluzelz')], 'syl', '( %s -> n e. ZZ )' % A); nr = w.s([nz], 'zred', '( %s -> n e. RR )' % A)
    mn = w.s([nu, w.inst('eluzle')], 'syl', '( %s -> %s <_ n )' % (A, M))
    xkn = w.s([xk, mr, nr, mle, mn], 'letrd', '( %s -> ( %s + %s ) <_ n )' % (A, X, k))
    # k <_ n
    xge = w.s([xgt], 'ltled', '( %s -> 0 <_ %s )' % (A, X))
    a2 = w.s([krd, xr, w.inst('addge02')], 'syl2anc', '( %s -> ( 0 <_ %s <-> %s <_ ( %s + %s ) ) )' % (A, X, k, X, k))
    kle = w.s([xge, a2], 'mpbid', '( %s -> %s <_ ( %s + %s ) )' % (A, k, X, k))
    kn = w.s([krd, xk, nr, kle, xkn], 'letrd', '( %s -> %s <_ n )' % (A, k))
    kz = w.s([], '%sz' % k, '%s e. ZZ' % k); kzd = w.s([kz], 'a1i', '( %s -> %s e. ZZ )' % (A, k))
    j = w.s([kzd, nz, kn], '3jca', '( %s -> ( %s e. ZZ /\\ n e. ZZ /\\ %s <_ n ) )' % (A, k, k))
    nk = w.s([j, w.inst('eluz2')], 'sylibr', '( %s -> n e. ( ZZ>= ` %s ) )' % (A, k))
    # X <_ n
    if k == '2':
        kge = w.s([], '0le2', '0 <_ 2')
    else:
        kp = w.s([], '3pos', '0 < 3'); r0 = w.s([], '0re', '0 e. RR'); r3 = w.s([], '3re', '3 e. RR')
        li = w.s([r0, r3], 'ltlei', '( 0 < 3 -> 0 <_ 3 )'); kge = w.s([kp, li], 'ax-mp', '0 <_ 3')
    kged = w.s([kge], 'a1i', '( %s -> 0 <_ %s )' % (A, k))
    a1 = w.s([xr, krd, w.inst('addge01')], 'syl2anc', '( %s -> ( 0 <_ %s <-> %s <_ ( %s + %s ) ) )' % (A, k, X, X, k))
    xle = w.s([kged, a1], 'mpbid', '( %s -> %s <_ ( %s + %s ) )' % (A, X, X, k))
    xn = w.s([xr, xk, nr, xle, xkn], 'letrd', '( %s -> %s <_ n )' % (A, X))
    # peel the logarithms: log^j n >= exp^(depth-j) B, keeping positivity of log^j n
    n2 = nk if depth == 2 else w.s([nk, w.inst('uzuzle23')], 'syl', '( %s -> n e. ( ZZ>= ` 2 ) )' % A)
    nn = w.s([n2, w.inst('eluz2nn')], 'syl', '( %s -> n e. NN )' % A); n0 = w.s([nn], 'nnnn0d', '( %s -> n e. NN0 )' % A)
    nrp = w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % A)
    # level 0: X <_ n with X, n in RR+
    lhs, rhs, lhsrp, rhsrp, cmp_ = X, 'n', xrp, nrp, xn
    for j in range(depth):
        # from lhs <_ rhs (both RR+) to log lhs <_ log rhs; log lhs = tower[depth-1-j]
        bi = w.s([lhsrp, rhsrp, w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) ) )' % (A, lhs, rhs, lhs, rhs))
        ll = w.s([cmp_, bi], 'mpbid', '( %s -> ( log ` %s ) <_ ( log ` %s ) )' % (A, lhs, rhs))
        inner = tower[depth - 1 - j]
        re = w.s([reals[inner], w.inst('relogef')], 'syl', '( %s -> ( log ` %s ) = %s )' % (A, lhs, inner))
        cmp_ = w.s([re, ll], 'eqbrtrrd', '( %s -> %s <_ ( log ` %s ) )' % (A, inner, rhs))
        newrhs = '( log ` %s )' % rhs
        if j < depth - 1:
            # positivity of newrhs: inner e. RR+ (a value of exp) and inner <_ newrhs
            innerrp = w.s([reals[inner], w.s([reals[tower[depth - 2 - j]], w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, inner))], 'elrpd', '( %s -> %s e. RR+ )' % (A, inner))
            nr_ = w.s([rhsrp, w.inst('relogcl')], 'syl', '( %s -> %s e. RR )' % (A, newrhs))
            ir = reals[inner]
            gt = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % A), ir, nr_, w.s([reals[tower[depth - 2 - j]], w.inst('efgt0')], 'syl', '( %s -> 0 < %s )' % (A, inner)), cmp_], 'ltletrd', '( %s -> 0 < %s )' % (A, newrhs))
            newrp = w.s([nr_, gt], 'elrpd', '( %s -> %s e. RR+ )' % (A, newrhs))
            lhs, rhs, lhsrp, rhsrp = inner, newrhs, innerrp, newrp
        else:
            final = cmp_; rhs = newrhs
    # rhs is log^depth n; rewrite through the definitions
    if depth == 2:
        v = w.s([n0, w.inst('ell2val')], 'syl', '( %s -> %s = %s )' % (A, E2('n'), L(L('n'))))
        res = w.s([final, v], 'breqtrrd', '( %s -> B <_ %s )' % (A, E2('n')))
    else:
        v2 = w.s([n0, w.inst('ell2val')], 'syl', '( %s -> %s = %s )' % (A, E2('n'), L(L('n'))))
        v3 = w.s([n0, w.inst('ell3val')], 'syl', '( %s -> %s = %s )' % (A, E3('n'), L(E2('n'))))
        v3b = w.s([v2], 'fveq2d', '( %s -> %s = %s )' % (A, L(E2('n')), L(L(L('n')))))
        v = w.s([v3, v3b], 'eqtrd', '( %s -> %s = %s )' % (A, E3('n'), L(L(L('n')))))
        res = w.s([final, v], 'breqtrrd', '( %s -> B <_ %s )' % (A, E3('n')))
    ral = w.s([res], 'ralrimiva', '( %s -> A. n e. ( ZZ>= ` %s ) B <_ %s )' % (A0, M, EL('n')))
    xr0 = w.s([], 'id', '( B e. RR -> B e. RR )'); cur = 'B'
    for _ in range(depth):
        nxt = '( exp ` %s )' % cur; xr0 = w.s([xr0], 'reefcld', '( %s -> %s e. RR )' % (A0, nxt)); cur = nxt
    kr0 = w.s([kr], 'a1i', '( %s -> %s e. RR )' % (A0, k))
    xk0 = w.s([xr0, kr0], 'readdcld', '( %s -> ( %s + %s ) e. RR )' % (A0, X, k))
    m0 = w.s([xk0, w.inst('nceilcl')], 'syl', '( %s -> %s e. NN0 )' % (A0, M))
    l1 = w.s([], 'id', '( m = %s -> m = %s )' % (M, M))
    c, res2 = w.wcongr('A. n e. ( ZZ>= ` m ) B <_ %s' % EL('n'), {'m': M}, 'm = %s' % M, {'m': l1})
    j2 = w.s([m0, ral], 'jca', '( %s -> ( %s e. NN0 /\\ A. n e. ( ZZ>= ` %s ) B <_ %s ) )' % (A0, M, M, EL('n')))
    i = w.s([c], 'rspcev', '( ( %s e. NN0 /\\ A. n e. ( ZZ>= ` %s ) B <_ %s ) -> E. m e. NN0 A. n e. ( ZZ>= ` m ) B <_ %s )' % (M, M, EL('n'), EL('n')))
    w.qed([j2, i], 'syl', '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) B <_ %s )' % (A0, EL('n')))
    run(w)

growth('ell2ge', 'ell2 tends to infinity: every real bound is eventually exceeded (Lean: tendsto_ell2.eventually_ge_atTop B in Step2W.lean, ScalesTM.lean, SearchAlg.lean).', 2)
growth('ell3ge', 'ell3 tends to infinity: every real bound is eventually exceeded (Lean: tendsto_ell3.eventually_ge_atTop B).', 3)
