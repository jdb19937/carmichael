"""Sortie T14 (c1): natLog_bridge, the layer lemma, ceiling division, pow2_sandwich.
MM_DB=sorties/t14.mm python3 tools/gen/t14_b_win.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t14lib import *

G = G2


def two_uz(w, A):
    return w.s([w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i',
               '( %s -> 2 e. ( ZZ>= ` 2 ) )' % A)


# ------------------------------------------------------------------ ln2ge23
def ln2ge23():
    w = W('ln2ge23', 'log 2 is at least 2 / 3: the first partial sum of the series of log2tlbnd '
                     '(Lean: Real.log_two_gt_d9, used as 0.6931471803 < log 2).')
    T = lambda n: '( 2 / ( ( 3 x. ( ( 2 x. %s ) + 1 ) ) x. ( 9 ^ %s ) ) )' % (n, n)
    UP = '( 3 / ( ( 4 x. ( ( 2 x. 1 ) + 1 ) ) x. ( 9 ^ 1 ) ) )'
    S1 = 'sum_ n e. ( 0 ... ( 1 - 1 ) ) %s' % T('n')
    h = w.s([w.s([], '1nn0', '1 e. NN0'), w.inst('log2tlbnd')], 'ax-mp', '( %s - %s ) e. ( 0 [,] %s )' % (G, S1, UP))
    a = w.s([], '2t0e0', '( 2 x. 0 ) = 0')
    b = w.s([a], 'oveq1i', '( ( 2 x. 0 ) + 1 ) = ( 0 + 1 )')
    b2 = w.s([b, w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'eqtri', '( ( 2 x. 0 ) + 1 ) = 1')
    c = w.s([b2], 'oveq2i', '( 3 x. ( ( 2 x. 0 ) + 1 ) ) = ( 3 x. 1 )')
    c2 = w.s([c, w.s([], '3t1e3', '( 3 x. 1 ) = 3')], 'eqtri', '( 3 x. ( ( 2 x. 0 ) + 1 ) ) = 3')
    f = w.s([w.s([], '9cn', '9 e. CC'), w.inst('exp0')], 'ax-mp', '( 9 ^ 0 ) = 1')
    g = w.s([c2, f], 'oveq12i', '( ( 3 x. ( ( 2 x. 0 ) + 1 ) ) x. ( 9 ^ 0 ) ) = ( 3 x. 1 )')
    g2 = w.s([g, w.s([], '3t1e3', '( 3 x. 1 ) = 3')], 'eqtri', '( ( 3 x. ( ( 2 x. 0 ) + 1 ) ) x. ( 9 ^ 0 ) ) = 3')
    t0 = w.s([g2], 'oveq2i', '%s = ( 2 / 3 )' % T('0'))
    # the sum over ( 0 ... 0 )
    s0 = w.s([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'oveq2i', '( 0 ... ( 1 - 1 ) ) = ( 0 ... 0 )')
    s1 = w.s([s0], 'sumeq1i', '%s = sum_ n e. ( 0 ... 0 ) %s' % (S1, T('n')))
    idn = w.s([], 'id', '( n = 0 -> n = 0 )')
    cg, new = w.congr(T('n'), {'n': '0'}, 'n = 0', {'n': idn})
    assert new == T('0'), new
    tcc = w.s([t0, w.s([w.s([], '2cn', '2 e. CC'), w.s([], '3cn', '3 e. CC'), w.s([], '3ne0', '3 =/= 0')], 'divcli',
                      '( 2 / 3 ) e. CC')], 'eqeltri', '%s e. CC' % T('0'))
    f1 = w.s([cg], 'fsum1', '( ( 0 e. ZZ /\\ %s e. CC ) -> sum_ n e. ( 0 ... 0 ) %s = %s )' % (T('0'), T('n'), T('0')))
    s2 = w.s([w.s([], '0z', '0 e. ZZ'), tcc, f1], 'mp2an', 'sum_ n e. ( 0 ... 0 ) %s = %s' % (T('n'), T('0')))
    s3 = w.s([s1, s2], 'eqtri', '%s = %s' % (S1, T('0')))
    s4 = w.s([s3, t0], 'eqtri', '%s = ( 2 / 3 )' % S1)
    h2 = w.s([s4], 'oveq2i', '( %s - %s ) = ( %s - ( 2 / 3 ) )' % (G, S1, G))
    h3 = w.s([h, h2], 'eqeltrri', '( %s - ( 2 / 3 ) ) e. ( 0 [,] %s )' % (G, UP))
    # 0 <_ log 2 - 2 / 3 from the interval
    icc = w.s([w.s([], '0re', '0 e. RR'), w.s([w.s([], '3re', '3 e. RR'), num_re(w, '( ( 4 x. ( ( 2 x. 1 ) + 1 ) ) x. ( 9 ^ 1 ) )'),
               num_ne0(w, '( ( 4 x. ( ( 2 x. 1 ) + 1 ) ) x. ( 9 ^ 1 ) )')], 'redivcli', '%s e. RR' % UP),
               w.inst('elicc2')], 'mp2an',
              '( ( %s - ( 2 / 3 ) ) e. ( 0 [,] %s ) <-> ( ( %s - ( 2 / 3 ) ) e. RR /\\ 0 <_ ( %s - ( 2 / 3 ) ) /\\ ( %s - ( 2 / 3 ) ) <_ %s ) )'
              % (G, UP, G, G, G, UP))
    i2 = w.s([h3, icc], 'mpbi', '( ( %s - ( 2 / 3 ) ) e. RR /\\ 0 <_ ( %s - ( 2 / 3 ) ) /\\ ( %s - ( 2 / 3 ) ) <_ %s )'
             % (G, G, G, UP))
    i3 = w.s([i2], 'simp2i', '0 <_ ( %s - ( 2 / 3 ) )' % G)
    lg = w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '%s e. RR' % G)
    t23 = w.s([w.s([], '2re', '2 e. RR'), w.s([], '3re', '3 e. RR'), w.s([], '3ne0', '3 =/= 0')], 'redivcli', '( 2 / 3 ) e. RR')
    bi = w.s([lg, t23, w.inst('subge0')], 'mp2an', '( 0 <_ ( %s - ( 2 / 3 ) ) <-> ( 2 / 3 ) <_ %s )' % (G, G))
    w.qed([i3, bi], 'mpbi', '( 2 / 3 ) <_ %s' % G)
    return run(w)


def num_re(w, E):
    cl = Closure(w, '1 = 1', {})
    st = cl.mem(E, 'RR')
    return w.s([w.s([], 'eqid', '1 = 1'), st], 'ax-mp', '%s e. RR' % E)


def num_ne0(w, E):
    cl = Closure(w, '1 = 1', {})
    st = cl.ne0(E)
    return w.s([w.s([], 'eqid', '1 = 1'), st], 'ax-mp', '%s =/= 0' % E)


# ------------------------------------------------------------------ nlogbr
def nlogbr():
    w = W('nlogbr', 'The bridge between Nlog and log: ( 2 Nlog X ) log 2 <_ log X < ( ( 2 Nlog X ) + 1 ) log 2 '
                    '(Lean: natLog_bridge).')
    A = 'X e. NN'
    cl = Closure(w, A, {'X': ('NN', w.s([], 'id', '( X e. NN -> X e. NN )'))})
    n = NL('X')
    tu = two_uz(w, A)
    xnn = cl.mem('X', 'NN')
    le = w.s([tu, xnn, w.inst('nlogle')], 'syl2anc', '( %s -> ( 2 ^ %s ) <_ X )' % (A, n))
    lt = w.s([tu, xnn, w.inst('nloglt')], 'syl2anc', '( %s -> X < ( 2 ^ ( %s + 1 ) ) )' % (A, n))
    nn0 = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), cl.mem('X', 'NN0'), w.inst('nlogcl')],
              'syl2anc', '( %s -> %s e. NN0 )' % (A, n))
    cl.have(n, 'NN0', nn0)
    two = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A)
    r1 = w.s([two, cl.mem(n, 'ZZ'), w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( 2 ^ %s ) ) = ( %s x. %s ) )' % (A, n, n, G))
    r2 = w.s([two, cl.mem('( %s + 1 )' % n, 'ZZ'), w.inst('relogexp')], 'syl2anc',
             '( %s -> ( log ` ( 2 ^ ( %s + 1 ) ) ) = ( ( %s + 1 ) x. %s ) )' % (A, n, n, G))
    b1 = w.s([cl.mem('( 2 ^ %s )' % n, 'RR+'), cl.mem('X', 'RR+'), w.inst('logleb')], 'syl2anc',
             '( %s -> ( ( 2 ^ %s ) <_ X <-> ( log ` ( 2 ^ %s ) ) <_ %s ) )' % (A, n, n, LOG('X')))
    b2 = w.s([cl.mem('X', 'RR+'), cl.mem('( 2 ^ ( %s + 1 ) )' % n, 'RR+'), w.inst('logltb')], 'syl2anc',
             '( %s -> ( X < ( 2 ^ ( %s + 1 ) ) <-> %s < ( log ` ( 2 ^ ( %s + 1 ) ) ) ) )' % (A, n, LOG('X'), n))
    c1 = w.s([le, b1], 'mpbid', '( %s -> ( log ` ( 2 ^ %s ) ) <_ %s )' % (A, n, LOG('X')))
    c2 = w.s([lt, b2], 'mpbid', '( %s -> %s < ( log ` ( 2 ^ ( %s + 1 ) ) ) )' % (A, LOG('X'), n))
    d1 = w.s([r1, c1], 'eqbrtrrd', '( %s -> ( %s x. %s ) <_ %s )' % (A, n, G, LOG('X')))
    d2 = w.s([c2, r2], 'breqtrd', '( %s -> %s < ( ( %s + 1 ) x. %s ) )' % (A, LOG('X'), n, G))
    w.qed([d1, d2], 'jca', '( %s -> %s )' % (A, STMTS14['nlogbr'].split(' -> ', 1)[1][:-2]))
    return run(w)


def glog2(w, A):
    """( A -> 2 / 3 <_ log 2 ), ( A -> log 2 < 253 / 365 ), ( A -> log 2 e. RR )"""
    lo = w.s([w.s([], 'ln2ge23', '( 2 / 3 ) <_ %s' % G)], 'a1i', '( %s -> ( 2 / 3 ) <_ %s )' % (A, G))
    hi = w.s([w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % G)], 'a1i', '( %s -> %s < ( ; ; 2 5 3 / ; ; 3 6 5 ) )' % (A, G))
    re = w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '%s e. RR' % G)], 'a1i', '( %s -> %s e. RR )' % (A, G))
    return lo, hi, re


def bridge(w, A, cl, X):
    """the two halves of nlogbr at X (cl proves X e. NN)"""
    n = NL(X)
    f = STMTS14['nlogbr'].replace('X', '@').replace('@', X)
    br = w.s([cl.mem(X, 'NN'), w.inst('nlogbr')], 'syl', '( %s -> %s )' % (A, f.split(' -> ', 1)[1][:-2]))
    return proj(w, A, br, 0), proj(w, A, br, 1)


# ------------------------------------------------------------------ nlog2log
def nlog2log():
    w = W('nlog2log', 'Nlog 2 below twice the natural logarithm: ( 2 Nlog X ) <_ 2 log X (Lean: natLog_le_two_log).')
    A = 'X e. NN'
    cl = Closure(w, A, {'X': ('NN', w.s([], 'id', '( X e. NN -> X e. NN )'))})
    lo, hi, gre = glog2(w, A); cl.have(G, 'RR', gre); cl.atom(G)
    b1, b2 = bridge(w, A, cl, 'X')
    n = NL('X')
    n0 = cl.ge0(n)
    cl.atom(LOG('X'))
    nlinarith(w, A, [b1, lo, n0], '%s <_ ( 2 x. %s )' % (n, LOG('X')), closure=cl, name='qed')
    return run(w)


# ------------------------------------------------------------------ nloglay
def nloglay():
    w = W('nloglay', 'One layer of iterated Nlog: if L >= 3 and L <_ log X <_ L + D then L <_ ( 2 Nlog X ) <_ '
                     '3 / 2 ( L + D ) (Lean: the three layers of scalesTM_inWindow).')
    A = STMTS14['nloglay'].split(' -> ')[0][2:]
    pj = Proj(w, A)
    cl = Closure(w, A, {'X': ('NN', pj('X e. NN')), 'L': ('RR', pj('L e. RR')), 'D': ('RR', pj('D e. RR'))})
    lo, hi, gre = glog2(w, A); cl.have(G, 'RR', gre); cl.atom(G)
    b1, b2 = bridge(w, A, cl, 'X')
    n = NL('X'); lX = LOG('X'); cl.atom(lX)
    l3 = pj('3 <_ L'); llx = pj('L <_ %s' % lX); lxd = pj('%s <_ ( L + D )' % lX)
    g0 = linarith(w, A, [lo], '0 < %s' % G, closure=cl)
    k1 = nlinarith(w, A, [b2, llx, l3, hi], '( L x. %s ) < ( %s x. %s )' % (G, n, G), closure=cl)
    grp = w.s([gre, g0], 'elrpd', '( %s -> %s e. RR+ )' % (A, G))
    bi = w.s([cl.mem('L', 'RR'), cl.mem(n, 'RR'), grp], 'ltmul1d',
             '( %s -> ( L < %s <-> ( L x. %s ) < ( %s x. %s ) ) )' % (A, n, G, n, G))
    k2 = w.s([k1, bi], 'mpbird', '( %s -> L < %s )' % (A, n))
    k3 = w.s([k2], 'ltled', '( %s -> L <_ %s )' % (A, n))
    n0 = cl.ge0(n)
    k4 = nlinarith(w, A, [b1, lxd, lo, n0], '%s <_ ( ( 3 / 2 ) x. ( L + D ) )' % n, closure=cl)
    w.qed([k3, k4], 'jca', '( %s -> ( L <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( L + D ) ) ) )' % (A, n, n))
    return run(w)


# ------------------------------------------------------------------ ceildv
def ceildv():
    w = W('ceildv', 'Ceiling division: Q |_ R / Q _| lies in [ R - Q + 1 , R ] for integers R and Q >= 1 '
                    '(Lean: the omega facts e1_nat, e2_nat, f_nat of scalesTM_inWindow).')
    A = '( R e. ZZ /\\ Q e. NN )'
    pj = Proj(w, A)
    cl = Closure(w, A, {'R': ('ZZ', pj('R e. ZZ')), 'Q': ('NN', pj('Q e. NN'))})
    q = '( R / Q )'; f = '( |_ ` %s )' % q
    qre = cl.mem(q, 'RR')
    fz = w.s([qre], 'flcld', '( %s -> %s e. ZZ )' % (A, f)); cl.have(f, 'ZZ', fz)
    a = w.s([qre, w.inst('flle')], 'syl', '( %s -> %s <_ %s )' % (A, f, q))
    b = w.s([qre, w.inst('flltp1')], 'syl', '( %s -> %s < ( %s + 1 ) )' % (A, q, f))
    qp = cl.mem('Q', 'RR+')
    a2 = w.s([cl.mem(f, 'RR'), qre, qp], 'lemul2d' if False else 'lemul2d',
             '( %s -> ( %s <_ %s <-> ( Q x. %s ) <_ ( Q x. %s ) ) )' % (A, f, q, f, q))
    a3 = w.s([a, a2], 'mpbid', '( %s -> ( Q x. %s ) <_ ( Q x. %s ) )' % (A, f, q))
    dv = w.s([cl.mem('R', 'CC'), cl.mem('Q', 'CC'), cl.ne0('Q')], 'divcan2d', '( %s -> ( Q x. %s ) = R )' % (A, q))
    up = w.s([a3, dv], 'breqtrd', '( %s -> ( Q x. %s ) <_ R )' % (A, f))
    b2 = w.s([qre, cl.mem('( %s + 1 )' % f, 'RR'), qp], 'ltmul2d',
             '( %s -> ( %s < ( %s + 1 ) <-> ( Q x. %s ) < ( Q x. ( %s + 1 ) ) ) )' % (A, q, f, q, f))
    b3 = w.s([b, b2], 'mpbid', '( %s -> ( Q x. %s ) < ( Q x. ( %s + 1 ) ) )' % (A, q, f))
    b4 = w.s([dv, b3], 'eqbrtrrd', '( %s -> R < ( Q x. ( %s + 1 ) ) )' % (A, f))
    b5 = nlinarith(w, A, [b4], '( R - Q ) < ( Q x. %s )' % f, closure=cl)
    zz = w.s([cl.mem('( R - Q )', 'ZZ'), cl.mem('( Q x. %s )' % f, 'ZZ'), w.inst('zltp1le')], 'syl2anc',
             '( %s -> ( ( R - Q ) < ( Q x. %s ) <-> ( ( R - Q ) + 1 ) <_ ( Q x. %s ) ) )' % (A, f, f))
    lo = w.s([b5, zz], 'mpbid', '( %s -> ( ( R - Q ) + 1 ) <_ ( Q x. %s ) )' % (A, f))
    w.qed([lo, up], 'jca', '( %s -> %s )' % (A, STMTS14['ceildv'].split(' -> ', 1)[1][:-2]))
    return run(w)


# ------------------------------------------------------------------ p2sw
def p2sw():
    w = W('p2sw', 'Powers of two sandwich a real power: A ( Nlog X + 1 ) <_ E <_ A ( Nlog X + 1 ) + R gives '
                  'X ^c A <_ 2 ^ E <_ 2 ^c ( A + R ) X ^c A (Lean: pow2_sandwich, by logarithms).')
    A = STMTS14['p2sw'].split(' -> ')[0][2:]
    pj = Proj(w, A)
    cl = Closure(w, A, {'X': ('NN', pj('X e. NN')), 'E': ('NN0', pj('E e. NN0')),
                        'A': [('RR', pj('A e. RR')), ('ge0', pj('0 <_ A'))], 'R': ('RR', pj('R e. RR'))})
    lo, hi, gre = glog2(w, A); cl.have(G, 'RR', gre); cl.atom(G)
    g0 = linarith(w, A, [lo], '0 <_ %s' % G, closure=cl); cl.have(G, 'ge0', g0)
    b1, b2 = bridge(w, A, cl, 'X')
    n = NL('X'); lX = LOG('X'); cl.atom(lX)
    h1 = pj('( A x. %s ) <_ E' % BX); h2 = pj('E <_ ( ( A x. %s ) + R )' % BX)
    xa = '( X ^c A )'; te = '( 2 ^ E )'; ta = '( 2 ^c ( A + R ) )'
    two = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A)
    xrp = cl.mem('X', 'RR+')
    xarp = w.s([xrp, cl.mem('A', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, xa))
    terp = w.s([two, cl.mem('E', 'ZZ')], 'rpexpcld', '( %s -> %s e. RR+ )' % (A, te))
    tarp = w.s([two, cl.mem('( A + R )', 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, ta))
    L1 = w.s([xrp, cl.mem('A', 'RR')], 'logcxpd', '( %s -> ( log ` %s ) = ( A x. %s ) )' % (A, xa, lX))
    L2 = w.s([two, cl.mem('E', 'ZZ'), w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` %s ) = ( E x. %s ) )' % (A, te, G))
    u1 = w.s([cl.mem(lX, 'RR'), cl.mem('( ( %s + 1 ) x. %s )' % (n, G), 'RR'), cl.mem('A', 'RR'), cl.ge0('A'),
              w.s([b2], 'ltled', '( %s -> %s <_ ( ( %s + 1 ) x. %s ) )' % (A, lX, n, G))], 'lemul2ad',
             '( %s -> ( A x. %s ) <_ ( A x. ( ( %s + 1 ) x. %s ) ) )' % (A, lX, n, G))
    u2 = w.s([cl.mem('( A x. %s )' % BX, 'RR'), cl.mem('E', 'RR'), gre, g0, h1], 'lemul1ad',
             '( %s -> ( ( A x. %s ) x. %s ) <_ ( E x. %s ) )' % (A, BX, G, G))
    c1 = nlinarith(w, A, [L1, L2, u1, u2], '( log ` %s ) <_ ( log ` %s )' % (xa, te), closure=cl)
    bi1 = w.s([xarp, terp, w.inst('logleb')], 'syl2anc', '( %s -> ( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) ) )' % (A, xa, te, xa, te))
    r1 = w.s([c1, bi1], 'mpbird', '( %s -> %s <_ %s )' % (A, xa, te))
    v1 = w.s([cl.mem('E', 'RR'), cl.mem('( ( A x. %s ) + R )' % BX, 'RR'), gre, g0, h2], 'lemul1ad',
             '( %s -> ( E x. %s ) <_ ( ( ( A x. %s ) + R ) x. %s ) )' % (A, G, BX, G))
    v2 = w.s([cl.mem('( %s x. %s )' % (n, G), 'RR'), cl.mem(lX, 'RR'), cl.mem('A', 'RR'), cl.ge0('A'), b1], 'lemul2ad',
             '( %s -> ( A x. ( %s x. %s ) ) <_ ( A x. %s ) )' % (A, n, G, lX))
    L3 = w.s([tarp, xarp], 'relogmuld', '( %s -> ( log ` ( %s x. %s ) ) = ( ( log ` %s ) + ( log ` %s ) ) )' % (A, ta, xa, ta, xa))
    L4 = w.s([two, cl.mem('( A + R )', 'RR')], 'logcxpd', '( %s -> ( log ` %s ) = ( ( A + R ) x. %s ) )' % (A, ta, G))
    cl.atom('( log ` %s )' % xa); cl.atom('( log ` %s )' % te); cl.atom('( log ` %s )' % ta)
    cl.atom('( log ` ( %s x. %s ) )' % (ta, xa))
    c2 = nlinarith(w, A, [L1, L2, L3, L4, v1, v2], '( log ` %s ) <_ ( log ` ( %s x. %s ) )' % (te, ta, xa), closure=cl)
    prp = w.s([tarp, xarp], 'rpmulcld', '( %s -> ( %s x. %s ) e. RR+ )' % (A, ta, xa))
    bi2 = w.s([terp, prp, w.inst('logleb')], 'syl2anc',
              '( %s -> ( %s <_ ( %s x. %s ) <-> ( log ` %s ) <_ ( log ` ( %s x. %s ) ) ) )' % (A, te, ta, xa, te, ta, xa))
    r2 = w.s([c2, bi2], 'mpbird', '( %s -> %s <_ ( %s x. %s ) )' % (A, te, ta, xa))
    w.qed([r1, r2], 'jca', '( %s -> %s )' % (A, STMTS14['p2sw'].split(' -> ', 1)[1][:-2]))
    return run(w)


if __name__ == '__main__':
    for f in (ln2ge23, nlogbr, nlog2log, nloglay, ceildv, p2sw):
        if want(f.__name__):
            f()
