"""C7b section 6 (C7a, first part): the logarithmic derivative of a finite product
prod_ q e. S ( ( z - q ) ^ ( O ` q ) ) on ( CC \\ S ) (cfinopn, dvsubexp,
fprodlogdvlem, fprodlogdvf, fprodlogdv)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
import congr as _cg
lin.FASTPATH = True

TOPO = '( TopOpen ` CCfld )'
D = '( CC \\ S )'
H0 = '( S e. Fin /\\ S C_ CC /\\ O : S --> NN )'


def PR(T, z='z', q='q'):
    return 'prod_ %s e. %s ( ( %s - %s ) ^ ( O ` %s ) )' % (q, T, z, q, q)


def SM(T, z='z', q='q'):
    return 'sum_ %s e. %s ( ( O ` %s ) / ( %s - %s ) )' % (q, T, q, z, q)


def PHI(T, x='z'):
    return '( CC _D ( %s e. %s |-> %s ) ) = ( %s e. %s |-> ( %s x. %s ) )' % (x, D, PR(T, x), x, D, PR(T, x), SM(T, x))


def closed(w, ante, ref, f):
    return w.s([w.s([], ref, f)], 'a1i', '( %s -> %s )' % (ante, f))


if __name__ == '__main__' and (not only or 'cfinopn' in only):
    w = W('cfinopn', 'The complement of a finite set of complex numbers is open.')
    ph = '( S e. Fin /\\ S C_ CC )'
    ej = w.s([], 'eqid', '%s = %s' % (TOPO, TOPO))
    un = w.s([], 'unicntop', 'CC = U. %s' % TOPO)
    fre = w.s([w.s([ej], 'cnfldhaus', '%s e. Haus' % TOPO), w.inst('haust1')], 'ax-mp', '%s e. Fre' % TOPO)
    fre = w.s([fre], 'a1i', '( %s -> %s e. Fre )' % (ph, TOPO))
    ss = w.s([], 'simpr', '( %s -> S C_ CC )' % ph)
    fi = w.s([], 'simpl', '( %s -> S e. Fin )' % ph)
    cld = w.s([fre, ss, fi, w.s([un], 't1ficld', '( ( %s e. Fre /\\ S C_ CC /\\ S e. Fin ) -> S e. ( Clsd ` %s ) )' % (TOPO, TOPO))], 'syl3anc',
              '( %s -> S e. ( Clsd ` %s ) )' % (ph, TOPO))
    w.qed([cld, w.s([un], 'cldopn', '( S e. ( Clsd ` %s ) -> %s e. %s )' % (TOPO, D, TOPO))], 'syl', '( %s -> %s e. %s )' % (ph, D, TOPO))
    run7b(w)

if __name__ == '__main__' and (not only or 'dvsubexp' in only):
    w = W('dvsubexp', 'The derivative of ` ( z - P ) ^ N ` on an open set.')
    A0 = '( ( E e. %s /\\ E C_ CC ) /\\ ( P e. CC /\\ N e. NN ) )' % TOPO
    A1 = '( %s /\\ z e. E )' % A0
    A2 = '( %s /\\ z e. CC )' % A0
    A3 = '( %s /\\ v e. CC )' % A0
    et = w.s([], 'simpll', '( %s -> E e. %s )' % (A0, TOPO))
    ec = w.s([], 'simplr', '( %s -> E C_ CC )' % A0)
    pc = w.s([], 'simprl', '( %s -> P e. CC )' % A0)
    nn = w.s([], 'simprr', '( %s -> N e. NN )' % A0)
    hn = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    ej = w.s([], 'eqid', '%s = %s' % (TOPO, TOPO))
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOPO, TOPO))], 'eqcomi', '%s = ( %s |`t CC )' % (TOPO, TOPO))
    ce = closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    zc = w.s([], 'simpr', '( %s -> z e. CC )' % A2)
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % A2)
    pc2 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A2)
    zero = w.s([], '0cnd', '( %s -> 0 e. CC )' % A2)
    dvid = w.s([ce], 'dvmptid', '( %s -> ( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 ) )' % A0)
    dvc = w.s([ce, pc], 'dvmptc', '( %s -> ( CC _D ( z e. CC |-> P ) ) = ( z e. CC |-> 0 ) )' % A0)
    dvl = w.s([ce, zc, one, dvid, pc2, zero, dvc], 'dvmptsub', '( %s -> ( CC _D ( z e. CC |-> ( z - P ) ) ) = ( z e. CC |-> ( 1 - 0 ) ) )' % A0)
    zpc = w.s([zc, pc2], 'subcld', '( %s -> ( z - P ) e. CC )' % A2)
    d10 = w.s([one, zero], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % A2)
    LIN = '( z e. E |-> ( z - P ) )'
    dvle = w.s([ce, zpc, d10, dvl, ec, jr, ej, et], 'dvmptres', '( %s -> ( CC _D %s ) = ( z e. E |-> ( 1 - 0 ) ) )' % (A0, LIN))
    ze = w.s([], 'simpr', '( %s -> z e. E )' % A1)
    zc1 = w.s([w.s([ec], 'adantr', '( %s -> E C_ CC )' % A1), ze], 'sseldd', '( %s -> z e. CC )' % A1)
    zpc1 = w.s([zc1, w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)], 'subcld', '( %s -> ( z - P ) e. CC )' % A1)
    d101 = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), w.s([], '0cnd', '( %s -> 0 e. CC )' % A1)], 'subcld', '( %s -> ( 1 - 0 ) e. CC )' % A1)
    vc = w.s([], 'simpr', '( %s -> v e. CC )' % A3)
    nn3 = w.s([nn], 'adantr', '( %s -> N e. NN )' % A3)
    vn = w.s([vc, w.s([hn], 'adantr', '( %s -> N e. NN0 )' % A3)], 'expcld', '( %s -> ( v ^ N ) e. CC )' % A3)
    vd = w.s([w.s([nn3], 'nncnd', '( %s -> N e. CC )' % A3), w.s([vc, w.s([nn3, w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % A3)], 'expcld', '( %s -> ( v ^ ( N - 1 ) ) e. CC )' % A3)],
             'mulcld', '( %s -> ( N x. ( v ^ ( N - 1 ) ) ) e. CC )' % A3)
    dve = w.s([nn, w.inst('dvexp')], 'syl', '( %s -> ( CC _D ( v e. CC |-> ( v ^ N ) ) ) = ( v e. CC |-> ( N x. ( v ^ ( N - 1 ) ) ) ) )' % A0)
    se = w.s([], 'oveq1', '( v = ( z - P ) -> ( v ^ N ) = ( ( z - P ) ^ N ) )')
    sf = w.s([w.s([], 'oveq1', '( v = ( z - P ) -> ( v ^ ( N - 1 ) ) = ( ( z - P ) ^ ( N - 1 ) ) )')], 'oveq2d',
             '( v = ( z - P ) -> ( N x. ( v ^ ( N - 1 ) ) ) = ( N x. ( ( z - P ) ^ ( N - 1 ) ) ) )')
    G = '( N x. ( ( z - P ) ^ ( N - 1 ) ) )'
    RHS = '( %s x. ( 1 - 0 ) )' % G
    PWE = '( z e. E |-> ( ( z - P ) ^ N ) )'
    dvp = w.s([ce, ce, zpc1, d101, vn, vd, dvle, dve, se, sf], 'dvmptco', '( %s -> ( CC _D %s ) = ( z e. E |-> %s ) )' % (A0, PWE, RHS))
    gc = w.s([w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A1)], 'nncnd', '( %s -> N e. CC )' % A1),
              w.s([zpc1, w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % A1), w.inst('nnm1nn0')], 'syl', '( %s -> ( N - 1 ) e. NN0 )' % A1)], 'expcld',
                  '( %s -> ( ( z - P ) ^ ( N - 1 ) ) e. CC )' % A1)], 'mulcld', '( %s -> %s e. CC )' % (A1, G))
    r1 = w.s([w.s([w.s([], '1m0e1', '( 1 - 0 ) = 1')], 'a1i', '( %s -> ( 1 - 0 ) = 1 )' % A1)], 'oveq2d', '( %s -> %s = ( %s x. 1 ) )' % (A1, RHS, G))
    r2 = w.s([r1, w.s([gc], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (A1, G, G))], 'eqtrd', '( %s -> %s = %s )' % (A1, RHS, G))
    meq = w.s([r2], 'mpteq2dva', '( %s -> ( z e. E |-> %s ) = ( z e. E |-> %s ) )' % (A0, RHS, G))
    w.qed([dvp, meq], 'eqtrd', '( %s -> ( CC _D %s ) = ( z e. E |-> %s ) )' % (A0, PWE, G))
    run7b(w)

TU = '( T u. { Q } )'
STEP = '( T C_ S /\\ Q e. ( S \\ T ) )'

if __name__ == '__main__' and (not only or 'fprodlogdvlem' in only):
    w = W('fprodlogdvlem', 'Induction step of ~ fprodlogdvf : the logarithmic-derivative identity for the product over ` T ` passes to ` T u. { Q } ` .')
    A0 = '( %s /\\ %s )' % (H0, STEP)
    h0 = w.s([], 'simpl', '( %s -> %s )' % (A0, H0))
    sfin = w.s([h0, w.inst('simp1')], 'syl', '( %s -> S e. Fin )' % A0)
    scc = w.s([h0, w.inst('simp2')], 'syl', '( %s -> S C_ CC )' % A0)
    of = w.s([h0, w.inst('simp3')], 'syl', '( %s -> O : S --> NN )' % A0)
    tss = w.s([], 'simprl', '( %s -> T C_ S )' % A0)
    qst = w.s([], 'simprr', '( %s -> Q e. ( S \\ T ) )' % A0)
    qs = w.s([qst, w.inst('eldifi')], 'syl', '( %s -> Q e. S )' % A0)
    qnt = w.s([qst, w.inst('eldifn')], 'syl', '( %s -> -. Q e. T )' % A0)
    tfin = w.s([sfin, tss], 'ssfid', '( %s -> T e. Fin )' % A0)
    M = '( O ` Q )'
    mn = w.s([of, qs], 'ffvelcdmd', '( %s -> %s e. NN )' % (A0, M))
    qc = w.s([scc, qs], 'sseldd', '( %s -> Q e. CC )' % A0)
    dop = w.s([w.s([sfin, scc], 'jca', '( %s -> ( S e. Fin /\\ S C_ CC ) )' % A0), w.inst('cfinopn')], 'syl', '( %s -> %s e. %s )' % (A0, D, TOPO))
    dcc = closed(w, A0, 'difss', '%s C_ CC' % D)
    # pointwise facts under Az
    Az = '( %s /\\ z e. %s )' % (A0, D)
    zd = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, D))
    zc = w.s([zd, w.inst('eldifi')], 'syl', '( %s -> z e. CC )' % Az)
    zns = w.s([zd, w.inst('eldifn')], 'syl', '( %s -> -. z e. S )' % Az)
    qsz = w.s([qs], 'adantr', '( %s -> Q e. S )' % Az)
    qnez = w.s([qsz, zns, w.inst('nelne2')], 'syl2anc', '( %s -> Q =/= z )' % Az)
    zq0 = w.s([zc, w.s([qc], 'adantr', '( %s -> Q e. CC )' % Az), w.s([qnez], 'necomd', '( %s -> z =/= Q )' % Az)], 'subne0d', '( %s -> ( z - Q ) =/= 0 )' % Az)
    Azq = '( %s /\\ q e. T )' % Az
    qT = w.s([], 'simpr', '( %s -> q e. T )' % Azq)
    qS = w.s([w.s([w.s([tss], 'adantr', '( %s -> T C_ S )' % Az)], 'adantr', '( %s -> T C_ S )' % Azq), qT], 'sseldd', '( %s -> q e. S )' % Azq)
    qcc = w.s([w.s([w.s([scc], 'adantr', '( %s -> S C_ CC )' % Az)], 'adantr', '( %s -> S C_ CC )' % Azq), qS], 'sseldd', '( %s -> q e. CC )' % Azq)
    oq = w.s([w.s([w.s([of], 'adantr', '( %s -> O : S --> NN )' % Az)], 'adantr', '( %s -> O : S --> NN )' % Azq), qS], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN )' % Azq)
    zcq = w.s([zc], 'adantr', '( %s -> z e. CC )' % Azq)
    zmq = w.s([zcq, qcc], 'subcld', '( %s -> ( z - q ) e. CC )' % Azq)
    zqn = w.s([w.s([qS, w.s([zns], 'adantr', '( %s -> -. z e. S )' % Azq), w.inst('nelne2')], 'syl2anc', '( %s -> q =/= z )' % Azq)], 'necomd', '( %s -> z =/= q )' % Azq)
    zmq0 = w.s([zcq, qcc, zqn], 'subne0d', '( %s -> ( z - q ) =/= 0 )' % Azq)
    t1 = w.s([zmq, w.s([oq], 'nnnn0d', '( %s -> ( O ` q ) e. NN0 )' % Azq)], 'expcld', '( %s -> ( ( z - q ) ^ ( O ` q ) ) e. CC )' % Azq)
    t2 = w.s([w.s([oq], 'nncnd', '( %s -> ( O ` q ) e. CC )' % Azq), zmq, zmq0], 'divcld', '( %s -> ( ( O ` q ) / ( z - q ) ) e. CC )' % Azq)
    tfz = w.s([tfin], 'adantr', '( %s -> T e. Fin )' % Az)
    P = PR('T'); L = SM('T')
    pc = w.s([tfz, t1], 'fprodcl', '( %s -> %s e. CC )' % (Az, P))
    lc = w.s([tfz, t2], 'fsumcl', '( %s -> %s e. CC )' % (Az, L))
    Wq = '( z - Q )'
    wc = w.s([zc, w.s([qc], 'adantr', '( %s -> Q e. CC )' % Az)], 'subcld', '( %s -> %s e. CC )' % (Az, Wq))
    mz = w.s([mn], 'adantr', '( %s -> %s e. NN )' % (Az, M))
    mc = w.s([mz], 'nncnd', '( %s -> %s e. CC )' % (Az, M))
    G = '( %s ^ %s )' % (Wq, M)
    U = '( %s ^ ( %s - 1 ) )' % (Wq, M)
    Gp = '( %s x. %s )' % (M, U)
    gc = w.s([wc, w.s([mz], 'nnnn0d', '( %s -> %s e. NN0 )' % (Az, M))], 'expcld', '( %s -> %s e. CC )' % (Az, G))
    uc = w.s([wc, w.s([mz, w.inst('nnm1nn0')], 'syl', '( %s -> ( %s - 1 ) e. NN0 )' % (Az, M))], 'expcld', '( %s -> %s e. CC )' % (Az, U))
    gpc = w.s([mc, uc], 'mulcld', '( %s -> %s e. CC )' % (Az, Gp))
    X = '( %s / %s )' % (M, Wq)
    xc = w.s([mc, wc, zq0], 'divcld', '( %s -> %s e. CC )' % (Az, X))
    # the splits
    qex = w.s([qc], 'elexd', '( %s -> Q e. _V )' % A0)
    qexz = w.s([qex], 'adantr', '( %s -> Q e. _V )' % Az)
    qntz = w.s([qnt], 'adantr', '( %s -> -. Q e. T )' % Az)
    cs1 = w.s([w.s([], 'oveq2', '( q = Q -> ( z - q ) = %s )' % Wq), w.s([], 'fveq2', '( q = Q -> ( O ` q ) = %s )' % M)], 'oveq12d',
              '( q = Q -> ( ( z - q ) ^ ( O ` q ) ) = %s )' % G)
    ps = w.s([w.s([], 'nfv', 'F/ q %s' % Az), w.s([], 'nfcv', 'F/_ q %s' % G), tfz, qexz, qntz, t1, cs1, gc], 'fprodsplitsn',
             '( %s -> %s = ( %s x. %s ) )' % (Az, PR(TU), P, G))
    cs2 = w.s([w.s([], 'fveq2', '( q = Q -> ( O ` q ) = %s )' % M), w.s([], 'oveq2', '( q = Q -> ( z - q ) = %s )' % Wq)], 'oveq12d',
              '( q = Q -> ( ( O ` q ) / ( z - q ) ) = %s )' % X)
    ss_ = w.s([w.s([], 'nfv', 'F/ q %s' % Az), w.s([], 'nfcv', 'F/_ q %s' % X), tfz, qexz, qntz, t2, cs2, xc], 'fsumsplitsn',
              '( %s -> %s = ( %s + %s ) )' % (Az, SM(TU), L, X))
    # G x. X = G'
    e1 = w.s([wc, mz, w.inst('expm1t')], 'syl2anc', '( %s -> %s = ( %s x. %s ) )' % (Az, G, U, Wq))
    e2 = w.s([e1], 'oveq1d', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) x. %s ) )' % (Az, G, X, U, Wq, X))
    e3 = w.s([uc, wc, xc], 'mulassd', '( %s -> ( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) ) )' % (Az, U, Wq, X, U, Wq, X))
    e4 = w.s([w.s([mc, wc, zq0], 'divcan2d', '( %s -> ( %s x. %s ) = %s )' % (Az, Wq, X, M))], 'oveq2d', '( %s -> ( %s x. ( %s x. %s ) ) = ( %s x. %s ) )' % (Az, U, Wq, X, U, M))
    e5 = w.s([uc, mc], 'mulcomd', '( %s -> ( %s x. %s ) = %s )' % (Az, U, M, Gp))
    gx = w.s([w.s([w.s([e2, e3], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. %s ) ) )' % (Az, G, X, U, Wq, X)), e4], 'eqtrd',
                  '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (Az, G, X, U, M)), e5], 'eqtrd', '( %s -> ( %s x. %s ) = %s )' % (Az, G, X, Gp))
    # the identity ( ( P L ) G + G' P ) = ( P G ) ( L + X )
    PG = '( %s x. %s )' % (P, G)
    i1 = w.s([w.s([pc, gc], 'mulcld', '( %s -> %s e. CC )' % (Az, PG)), lc, xc], 'adddid', '( %s -> ( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) ) )' % (Az, PG, L, X, PG, L, PG, X))
    i2 = w.s([pc, gc, lc], 'mul32d', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) x. %s ) )' % (Az, PG, L, P, L, G))
    i3 = w.s([pc, gc, xc], 'mulassd', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. %s ) ) )' % (Az, PG, X, P, G, X))
    i4 = w.s([w.s([gx], 'oveq2d', '( %s -> ( %s x. ( %s x. %s ) ) = ( %s x. %s ) )' % (Az, P, G, X, P, Gp)), w.s([pc, gpc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (Az, P, Gp, Gp, P))],
             'eqtrd', '( %s -> ( %s x. ( %s x. %s ) ) = ( %s x. %s ) )' % (Az, P, G, X, Gp, P))
    i34 = w.s([i3, i4], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (Az, PG, X, Gp, P))
    LHS = '( ( ( %s x. %s ) x. %s ) + ( %s x. %s ) )' % (P, L, G, Gp, P)
    i5 = w.s([i1, w.s([i2, i34], 'oveq12d', '( %s -> ( ( %s x. %s ) + ( %s x. %s ) ) = %s )' % (Az, PG, L, PG, X, LHS))], 'eqtrd',
             '( %s -> ( %s x. ( %s + %s ) ) = %s )' % (Az, PG, L, X, LHS))
    NEW = '( %s x. %s )' % (PR(TU), SM(TU))
    i6 = w.s([ps, ss_], 'oveq12d', '( %s -> %s = ( %s x. ( %s + %s ) ) )' % (Az, NEW, PG, L, X))
    rhs_eq = w.s([i6, i5], 'eqtrd', '( %s -> %s = %s )' % (Az, NEW, LHS))
    # the induction hypothesis with the binder v
    A1 = '( %s /\\ %s )' % (A0, PHI('T', 'v'))
    A1z = '( %s /\\ z e. %s )' % (A1, D)

    def up(st, f):
        return w.s([st], 'adantlr', '( %s -> %s )' % (A1z, f))
    idv = w.s([], 'id', '( v = z -> v = z )')
    c1, pz = w.congr(PR('T', 'v'), {'v': 'z'}, 'v = z', {'v': idv})
    c2, pl = w.congr('( %s x. %s )' % (PR('T', 'v'), SM('T', 'v')), {'v': 'z'}, 'v = z', {'v': idv})
    m1 = w.s([c1], 'cbvmptv', '( v e. %s |-> %s ) = ( z e. %s |-> %s )' % (D, PR('T', 'v'), D, P))
    m2 = w.s([c2], 'cbvmptv', '( v e. %s |-> ( %s x. %s ) ) = ( z e. %s |-> ( %s x. %s ) )' % (D, PR('T', 'v'), SM('T', 'v'), D, P, L))
    bi = w.s([w.s([m1], 'oveq2i', '( CC _D ( v e. %s |-> %s ) ) = ( CC _D ( z e. %s |-> %s ) )' % (D, PR('T', 'v'), D, P)), m2], 'eqeq12i', '( %s <-> %s )' % (PHI('T', 'v'), PHI('T')))
    ih = w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, PHI('T', 'v'))), bi], 'sylib', '( %s -> %s )' % (A1, PHI('T')))
    ce = closed(w, A1, 'cnelprrecn', 'CC e. { RR , CC }')
    a0 = w.s([], 'simpl', '( %s -> %s )' % (A1, A0))
    dsub = w.s([w.s([w.s([w.s([dop, dcc], 'jca', '( %s -> ( %s e. %s /\\ %s C_ CC ) )' % (A0, D, TOPO, D)), w.s([qc, mn], 'jca', '( %s -> ( Q e. CC /\\ %s e. NN ) )' % (A0, M))], 'jca',
                          '( %s -> ( ( %s e. %s /\\ %s C_ CC ) /\\ ( Q e. CC /\\ %s e. NN ) ) )' % (A0, D, TOPO, D, M)), w.inst('dvsubexp')], 'syl',
                    '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> %s ) )' % (A0, D, G, D, Gp))], 'adantr', '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> %s ) )' % (A1, D, G, D, Gp))
    plc = w.s([pc, lc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (Az, P, L))
    dm = w.s([ce, up(pc, '%s e. CC' % P), up(plc, '( %s x. %s ) e. CC' % (P, L)), ih, up(gc, '%s e. CC' % G), up(gpc, '%s e. CC' % Gp), dsub], 'dvmptmul',
             '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> %s ) )' % (A1, D, PG, D, LHS))
    ml = w.s([up(ps, '%s = %s' % (PR(TU), PG))], 'mpteq2dva', '( %s -> ( z e. %s |-> %s ) = ( z e. %s |-> %s ) )' % (A1, D, PR(TU), D, PG))
    mr = w.s([up(rhs_eq, '%s = %s' % (NEW, LHS))], 'mpteq2dva', '( %s -> ( z e. %s |-> %s ) = ( z e. %s |-> %s ) )' % (A1, D, NEW, D, LHS))
    dl = w.s([ml], 'oveq2d', '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( CC _D ( z e. %s |-> %s ) ) )' % (A1, D, PR(TU), D, PG))
    fin = w.s([w.s([dl, dm], 'eqtrd', '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> %s ) )' % (A1, D, PR(TU), D, LHS)), mr], 'eqtr4d', '( %s -> %s )' % (A1, PHI(TU)))
    ex = w.s([fin], 'ex', '( %s -> ( %s -> %s ) )' % (A0, PHI('T', 'v'), PHI(TU)))
    w.qed([bi, ex], 'biimtrrid', '( %s -> ( %s -> %s ) )' % (A0, PHI('T'), PHI(TU)))
    run7b(w)


if __name__ == '__main__' and (not only or 'fprodlogdvf' in only):
    w = W('fprodlogdvf', 'The derivative of the finite product ` prod_ q e. S ( z - q ) ^ ( O ` q ) ` on ` CC \\ S ` is the product times '
          '` sum_ q e. S ( O ` q ) / ( z - q ) ` (by induction over the subsets of ` S ` , ~ findcard2d ).')
    A0 = H0
    subs = []
    for X in ('(/)', 'b', '( b u. { c } )', 'S'):
        ida = w.s([], 'id', '( a = %s -> a = %s )' % (X, X))
        st, new = w.wcongr(PHI('a'), {'a': X}, 'a = %s' % X, {'a': ida})
        assert new == PHI(X), new
        subs.append(st)
    # base
    ej = w.s([], 'eqid', '%s = %s' % (TOPO, TOPO))
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOPO, TOPO))], 'eqcomi', '%s = ( %s |`t CC )' % (TOPO, TOPO))
    sfin = w.s([], 'simp1', '( %s -> S e. Fin )' % A0)
    scc = w.s([], 'simp2', '( %s -> S C_ CC )' % A0)
    dop = w.s([w.s([sfin, scc], 'jca', '( %s -> ( S e. Fin /\\ S C_ CC ) )' % A0), w.inst('cfinopn')], 'syl', '( %s -> %s e. %s )' % (A0, D, TOPO))
    dopr = w.s([dop, jr], 'eleqtrdi', '( %s -> %s e. ( %s |`t CC ) )' % (A0, D, TOPO))
    # main-body route: dvmptc on CC, restricted to the open set by dvmptres
    cnpr = closed(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    dcc = w.s([cnpr, w.s([], '1cnd', '( %s -> 1 e. CC )' % A0)], 'dvmptc',
              '( %s -> ( CC _D ( z e. CC |-> 1 ) ) = ( z e. CC |-> 0 ) )' % A0)
    a1 = w.s([], '1cnd', '( ( %s /\\ z e. CC ) -> 1 e. CC )' % A0)
    b0 = w.s([], '0cnd', '( ( %s /\\ z e. CC ) -> 0 e. CC )' % A0)
    dss = w.s([], 'difssd', '( %s -> %s C_ CC )' % (A0, D))
    jeq = w.s([], 'eqid', '( %s |`t CC ) = ( %s |`t CC )' % (TOPO, TOPO))
    dc = w.s([cnpr, a1, b0, dcc, dss, jeq, ej, dopr], 'dvmptres',
             '( %s -> ( CC _D ( z e. %s |-> 1 ) ) = ( z e. %s |-> 0 ) )' % (A0, D, D))
    p0 = w.s([], 'prod0', '%s = 1' % PR('(/)'))
    s0 = w.s([], 'sum0', '%s = 0' % SM('(/)'))
    ml = w.s([p0], 'mpteq2i', '( z e. %s |-> %s ) = ( z e. %s |-> 1 )' % (D, PR('(/)'), D))
    ps0 = w.s([w.s([p0, s0], 'oveq12i', '( %s x. %s ) = ( 1 x. 0 )' % (PR('(/)'), SM('(/)'))), w.s([w.s([], 'ax-1cn', '1 e. CC')], 'mul01i', '( 1 x. 0 ) = 0')], 'eqtri',
              '( %s x. %s ) = 0' % (PR('(/)'), SM('(/)')))
    mr = w.s([ps0], 'mpteq2i', '( z e. %s |-> ( %s x. %s ) ) = ( z e. %s |-> 0 )' % (D, PR('(/)'), SM('(/)'), D))
    dl = w.s([ml], 'oveq2i', '( CC _D ( z e. %s |-> %s ) ) = ( CC _D ( z e. %s |-> 1 ) )' % (D, PR('(/)'), D))
    base = w.s([w.s([w.s([dl], 'a1i', '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( CC _D ( z e. %s |-> 1 ) ) )' % (A0, D, PR('(/)'), D)), dc], 'eqtrd',
                    '( %s -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> 0 ) )' % (A0, D, PR('(/)'), D)),
                w.s([mr], 'a1i', '( %s -> ( z e. %s |-> ( %s x. %s ) ) = ( z e. %s |-> 0 ) )' % (A0, D, PR('(/)'), SM('(/)'), D))], 'eqtr4d', '( %s -> %s )' % (A0, PHI('(/)')))
    step = w.s([], 'fprodlogdvlem', '( ( %s /\\ ( b C_ S /\\ c e. ( S \\ b ) ) ) -> ( %s -> %s ) )' % (A0, PHI('b'), PHI('( b u. { c } )')))
    w.qed(subs + [base, step, sfin], 'findcard2d', '( %s -> %s )' % (A0, PHI('S')))
    run7b(w)

if __name__ == '__main__' and (not only or 'fprodlogdv' in only):
    w = W('fprodlogdv', 'The logarithmic derivative of a finite product of powers of linear factors at a point off its zeros.')
    A0 = '( %s /\\ Z e. %s )' % (H0, D)
    ph = w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, H0)), w.inst('fprodlogdvf')], 'syl', '( %s -> %s )' % (A0, PHI('S')))
    MP = '( z e. %s |-> ( %s x. %s ) )' % (D, PR('S'), SM('S'))
    fv = w.s([ph], 'fveq1d', '( %s -> ( ( CC _D ( z e. %s |-> %s ) ) ` Z ) = ( %s ` Z ) )' % (A0, D, PR('S'), MP))
    st, v = _cg.mptval(w, A0, 'z', D, '( %s x. %s )' % (PR('S'), SM('S')), 'Z', w.s([], 'simpr', '( %s -> Z e. %s )' % (A0, D)), gen=w.g)
    assert v == '( %s x. %s )' % (PR('S', 'Z'), SM('S', 'Z')), v
    w.qed([fv, st], 'eqtrd', '( %s -> ( ( CC _D ( z e. %s |-> %s ) ) ` Z ) = %s )' % (A0, D, PR('S'), v))
    run7b(w)


if __name__ == '__main__' and (not only or 'fprodlcl' in only):
    w = W('fprodlcl', 'The finite product ` prod_ q e. S ( Z - q ) ^ ( O ` q ) ` is a nonzero complex number off ` S ` , and ` sum_ q e. S ( O ` q ) / ( Z - q ) ` is complex.')
    A0 = '( %s /\\ Z e. %s )' % (H0, D)
    h0 = w.s([], 'simpl', '( %s -> %s )' % (A0, H0))
    sfin = w.s([h0, w.inst('simp1')], 'syl', '( %s -> S e. Fin )' % A0)
    scc = w.s([h0, w.inst('simp2')], 'syl', '( %s -> S C_ CC )' % A0)
    of = w.s([h0, w.inst('simp3')], 'syl', '( %s -> O : S --> NN )' % A0)
    zd = w.s([], 'simpr', '( %s -> Z e. %s )' % (A0, D))
    zc = w.s([zd, w.inst('eldifi')], 'syl', '( %s -> Z e. CC )' % A0)
    zns = w.s([zd, w.inst('eldifn')], 'syl', '( %s -> -. Z e. S )' % A0)
    Aq = '( %s /\\ q e. S )' % A0
    qS = w.s([], 'simpr', '( %s -> q e. S )' % Aq)
    qcc = w.s([w.s([scc], 'adantr', '( %s -> S C_ CC )' % Aq), qS], 'sseldd', '( %s -> q e. CC )' % Aq)
    oq = w.s([w.s([of], 'adantr', '( %s -> O : S --> NN )' % Aq), qS], 'ffvelcdmd', '( %s -> ( O ` q ) e. NN )' % Aq)
    zcq = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Aq)
    zmq = w.s([zcq, qcc], 'subcld', '( %s -> ( Z - q ) e. CC )' % Aq)
    zqn = w.s([w.s([qS, w.s([zns], 'adantr', '( %s -> -. Z e. S )' % Aq), w.inst('nelne2')], 'syl2anc', '( %s -> q =/= Z )' % Aq)], 'necomd', '( %s -> Z =/= q )' % Aq)
    zmq0 = w.s([zcq, qcc, zqn], 'subne0d', '( %s -> ( Z - q ) =/= 0 )' % Aq)
    oq0 = w.s([oq], 'nnnn0d', '( %s -> ( O ` q ) e. NN0 )' % Aq)
    t1 = w.s([zmq, oq0], 'expcld', '( %s -> ( ( Z - q ) ^ ( O ` q ) ) e. CC )' % Aq)
    t1n = w.s([zmq, zmq0, w.s([oq], 'nnzd', '( %s -> ( O ` q ) e. ZZ )' % Aq)], 'expne0d', '( %s -> ( ( Z - q ) ^ ( O ` q ) ) =/= 0 )' % Aq)
    t2 = w.s([w.s([oq], 'nncnd', '( %s -> ( O ` q ) e. CC )' % Aq), zmq, zmq0], 'divcld', '( %s -> ( ( O ` q ) / ( Z - q ) ) e. CC )' % Aq)
    pc = w.s([sfin, t1], 'fprodcl', '( %s -> %s e. CC )' % (A0, PR('S', 'Z')))
    pn = w.s([sfin, t1, t1n], 'fprodn0', '( %s -> %s =/= 0 )' % (A0, PR('S', 'Z')))
    lc = w.s([sfin, t2], 'fsumcl', '( %s -> %s e. CC )' % (A0, SM('S', 'Z')))
    w.qed([pc, pn, lc], '3jca', '( %s -> ( %s e. CC /\\ %s =/= 0 /\\ %s e. CC ) )' % (A0, PR('S', 'Z'), PR('S', 'Z'), SM('S', 'Z')))
    run7b(w)
