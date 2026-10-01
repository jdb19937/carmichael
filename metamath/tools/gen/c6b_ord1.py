"""Sortie C6b, part 7: the order of vanishing, first half (holordval,
cnptnear, cncfzero, holordunilem, holorduni, holordeq, holordtop)."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')); from c6blib import *


def ORDB(d, g, n, f='F', p='P'):
    return '( %s e. %s /\\ %s /\\ ( ( %s ` %s ) =/= 0 /\\ A. z e. %s ( %s ` z ) = ( ( ( z - %s ) ^ %s ) x. ( %s ` z ) ) ) )' % (p, d, HOLG(g, d), g, p, d, f, p, n, g)


def ORD(n, f='F', p='P'):
    return 'E. d e. %s E. g %s' % (TOP, ORDB('d', 'g', n, f, p))


def ORDSET(f='F', p='P'):
    return '{ n e. NN0 | %s }' % ORD('n', f, p)


def INF(f='F', p='P'):
    return 'inf ( %s , RR* , < )' % ORDSET(f, p)


def T(E, G, N):
    return '( ( %s e. %s /\\ P e. %s ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s ` P ) =/= 0 ) /\\ ( %s e. NN0 /\\ A. z e. %s ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) ) )' % (E, TOP, E, G, E, G, N, E, N, G)


def FACE(E, G, N, z='z'):
    return 'A. %s e. %s ( F ` %s ) = ( ( ( %s - P ) ^ %s ) x. ( %s ` %s ) )' % (z, E, z, z, N, G, z)


def HEQ(E, G, N):
    """the antecedent of holordeq"""
    return '( ( F e. V /\\ ( %s e. %s /\\ P e. %s ) ) /\\ ( %s /\\ ( %s ` P ) =/= 0 ) /\\ ( %s e. NN0 /\\ %s ) )' % (E, TOP, E, HOLG(G, E), G, N, FACE(E, G, N))


def ordsubn(w, n1, n2):
    """closed: ( n1 = n2 -> ( ORD(n1) <-> ORD(n2) ) )"""
    A = '%s = %s' % (n1, n2)
    s = w.s([w.s([w.s([w.s([], 'oveq2', '( %s -> ( ( z - P ) ^ %s ) = ( ( z - P ) ^ %s ) )' % (A, n1, n2))], 'oveq1d', '( %s -> ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) )' % (A, n1, n2))], 'eqeq2d',
                  '( %s -> ( ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) <-> ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) ) )' % (A, n1, n2))], 'ralbidv',
             '( %s -> ( A. z e. d ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) <-> A. z e. d ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) ) )' % (A, n1, n2))
    b = w.s([w.s([s], 'anbi2d', '( %s -> ( ( ( g ` P ) =/= 0 /\\ A. z e. d ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) ) <-> ( ( g ` P ) =/= 0 /\\ A. z e. d ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( g ` z ) ) ) ) )' % (A, n1, n2))], '3anbi3d',
             '( %s -> ( %s <-> %s ) )' % (A, ORDB('d', 'g', n1), ORDB('d', 'g', n2)))
    return w.s([w.s([b], 'exbidv', '( %s -> ( E. g %s <-> E. g %s ) )' % (A, ORDB('d', 'g', n1), ORDB('d', 'g', n2)))], 'rexbidv', '( %s -> ( %s <-> %s ) )' % (A, ORD(n1), ORD(n2)))


if __name__ == '__main__':
    # ---- holordval ------------------------------------------------------------------
    w = W('holordval', 'The value of the order of vanishing: the infimum in the extended reals of the exponents of the local factorisations of F at P .')
    A0 = '( F e. V /\\ P e. CC )'
    AE = '( f = F /\\ p = P )'
    fe = w.s([], 'simpl', '( %s -> f = F )' % AE); pe = w.s([], 'simpr', '( %s -> p = P )' % AE)
    s1 = w.s([pe], 'eleq1d', '( %s -> ( p e. d <-> P e. d ) )' % AE)
    s2 = w.s([], 'biidd', '( %s -> ( %s <-> %s ) )' % (AE, HOLG('g', 'd'), HOLG('g', 'd')))
    s3 = w.s([w.s([pe], 'fveq2d', '( %s -> ( g ` p ) = ( g ` P ) )' % AE)], 'neeq1d', '( %s -> ( ( g ` p ) =/= 0 <-> ( g ` P ) =/= 0 ) )' % AE)
    lhs = w.s([fe], 'fveq1d', '( %s -> ( f ` z ) = ( F ` z ) )' % AE)
    rhs = w.s([w.s([w.s([pe], 'oveq2d', '( %s -> ( z - p ) = ( z - P ) )' % AE)], 'oveq1d', '( %s -> ( ( z - p ) ^ n ) = ( ( z - P ) ^ n ) )' % AE)], 'oveq1d', '( %s -> ( ( ( z - p ) ^ n ) x. ( g ` z ) ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) )' % AE)
    s4 = w.s([w.s([lhs, rhs], 'eqeq12d', '( %s -> ( ( f ` z ) = ( ( ( z - p ) ^ n ) x. ( g ` z ) ) <-> ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) ) )' % AE)], 'ralbidv',
             '( %s -> ( A. z e. d ( f ` z ) = ( ( ( z - p ) ^ n ) x. ( g ` z ) ) <-> A. z e. d ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) ) )' % AE)
    s34 = w.s([s3, s4], 'anbi12d', '( %s -> ( ( ( g ` p ) =/= 0 /\\ A. z e. d ( f ` z ) = ( ( ( z - p ) ^ n ) x. ( g ` z ) ) ) <-> ( ( g ` P ) =/= 0 /\\ A. z e. d ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) ) ) )' % AE)
    body = w.s([s1, s2, s34], '3anbi123d', '( %s -> ( %s <-> %s ) )' % (AE, ORDB('d', 'g', 'n', 'f', 'p'), ORDB('d', 'g', 'n')))
    ex = w.s([body], 'exbidv', '( %s -> ( E. g %s <-> E. g %s ) )' % (AE, ORDB('d', 'g', 'n', 'f', 'p'), ORDB('d', 'g', 'n')))
    rex = w.s([ex], 'rexbidv', '( %s -> ( %s <-> %s ) )' % (AE, ORD('n', 'f', 'p'), ORD('n')))
    rab = w.s([rex], 'rabbidv', '( %s -> %s = %s )' % (AE, ORDSET('f', 'p'), ORDSET()))
    inf = w.s([rab], 'infeq1d', '( %s -> %s = %s )' % (AE, INF('f', 'p'), INF()))
    hd = w.s([], 'df-holord', 'holord = ( f e. _V , p e. CC |-> %s )' % INF('f', 'p'))
    inst = w.s([inf, hd], 'ovmpoga', '( ( F e. _V /\\ P e. CC /\\ %s e. _V ) -> ( F holord P ) = %s )' % (INF(), INF()))
    fex = w.s([w.s([], 'simpl', '( %s -> F e. V )' % A0)], 'elexd', '( %s -> F e. _V )' % A0)
    pc = w.s([], 'simpr', '( %s -> P e. CC )' % A0)
    iex = w.s([w.s([w.s([], 'xrltso', '< Or RR*')], 'infex', '%s e. _V' % INF())], 'a1i', '( %s -> %s e. _V )' % (A0, INF()))
    w.qed([fex, pc, iex, inst], 'syl3anc', '( %s -> ( F holord P ) = %s )' % (A0, INF()))
    run1(w)

    # ---- cnptnear -------------------------------------------------------------------
    w = W('cnptnear', 'An open subset of the complex plane contains, within any positive distance of each of its points, a point other than that point.')
    A0 = '( ( E e. %s /\\ P e. E ) /\\ S e. RR+ )' % TOP
    ep = w.s([], 'simpl', '( %s -> ( E e. %s /\\ P e. E ) )' % (A0, TOP))
    srp = w.s([], 'simpr', '( %s -> S e. RR+ )' % A0)
    ee = w.s([ep, w.inst('simpl')], 'syl', '( %s -> E e. %s )' % (A0, TOP))
    pe = w.s([ep, w.inst('simpr')], 'syl', '( %s -> P e. E )' % A0)
    BALL = 'A. z e. CC ( ( abs ` ( z - P ) ) < t -> z e. E )'
    ex = w.s([ep, w.inst('cnopnbl')], 'syl', '( %s -> E. t e. RR+ %s )' % (A0, BALL))
    un = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    ecc = w.s([w.s([ee, w.inst('elssuni')], 'syl', '( %s -> E C_ U. %s )' % (A0, TOP)), w.s([un], 'eqcomi', 'U. %s = CC' % TOP)], 'sseqtrdi', '( %s -> E C_ CC )' % A0)
    pc = w.s([ecc, pe], 'sseldd', '( %s -> P e. CC )' % A0)
    A1 = '( %s /\\ ( t e. RR+ /\\ %s ) )' % (A0, BALL)
    trp = w.s([w.s([], 'simpr', '( %s -> ( t e. RR+ /\\ %s ) )' % (A1, BALL)), w.inst('simpl')], 'syl', '( %s -> t e. RR+ )' % A1)
    ball = w.s([w.s([], 'simpr', '( %s -> ( t e. RR+ /\\ %s ) )' % (A1, BALL)), w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, BALL))
    srp1 = w.s([srp], 'adantr', '( %s -> S e. RR+ )' % A1)
    SM = '( ( S x. t ) / ( S + t ) )'
    TT = '( %s / 2 )' % SM
    sm = w.s([srp1, trp, w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ S /\\ %s <_ t ) ) )' % (A1, SM, SM, SM))
    smrp = w.s([sm, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A1, SM))
    sml = w.s([sm, w.inst('simpr')], 'syl', '( %s -> ( %s <_ S /\\ %s <_ t ) )' % (A1, SM, SM))
    ttrp = w.s([smrp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A1, TT))
    ttr = w.s([ttrp], 'rpred', '( %s -> %s e. RR )' % (A1, TT))
    ttc = w.s([ttr], 'recnd', '( %s -> %s e. CC )' % (A1, TT))
    tlt = w.s([smrp, w.inst('rphalflt')], 'syl', '( %s -> %s < %s )' % (A1, TT, SM))
    smr = w.s([smrp], 'rpred', '( %s -> %s e. RR )' % (A1, SM))
    lts = w.s([ttr, smr, w.s([srp1], 'rpred', '( %s -> S e. RR )' % A1), tlt, w.s([sml, w.inst('simpl')], 'syl', '( %s -> %s <_ S )' % (A1, SM))], 'ltletrd', '( %s -> %s < S )' % (A1, TT))
    ltt = w.s([ttr, smr, w.s([trp], 'rpred', '( %s -> t e. RR )' % A1), tlt, w.s([sml, w.inst('simpr')], 'syl', '( %s -> %s <_ t )' % (A1, SM))], 'ltletrd', '( %s -> %s < t )' % (A1, TT))
    Z = '( P + %s )' % TT
    pc1 = w.s([pc], 'adantr', '( %s -> P e. CC )' % A1)
    zc = w.s([pc1, ttc], 'addcld', '( %s -> %s e. CC )' % (A1, Z))
    zmp = w.s([pc1, ttc], 'pncan2d', '( %s -> ( %s - P ) = %s )' % (A1, Z, TT))
    azp = w.s([w.s([zmp], 'fveq2d', '( %s -> ( abs ` ( %s - P ) ) = ( abs ` %s ) )' % (A1, Z, TT)), w.s([ttr, w.s([ttrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A1, TT))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A1, TT, TT))], 'eqtrd',
              '( %s -> ( abs ` ( %s - P ) ) = %s )' % (A1, Z, TT))
    zne = w.s([w.s([zmp, w.s([ttrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A1, TT))], 'eqnetrd', '( %s -> ( %s - P ) =/= 0 )' % (A1, Z)),
               w.s([w.s([zc, pc1, w.inst('subeq0')], 'syl2anc', '( %s -> ( ( %s - P ) = 0 <-> %s = P ) )' % (A1, Z, Z))], 'necon3bid', '( %s -> ( ( %s - P ) =/= 0 <-> %s =/= P ) )' % (A1, Z, Z))], 'mpbid', '( %s -> %s =/= P )' % (A1, Z))
    bsub = w.s([w.s([w.s([w.s([], 'oveq1', '( z = %s -> ( z - P ) = ( %s - P ) )' % (Z, Z))], 'fveq2d', '( z = %s -> ( abs ` ( z - P ) ) = ( abs ` ( %s - P ) ) )' % (Z, Z))], 'breq1d', '( z = %s -> ( ( abs ` ( z - P ) ) < t <-> ( abs ` ( %s - P ) ) < t ) )' % (Z, Z)),
               w.s([], 'eleq1', '( z = %s -> ( z e. E <-> %s e. E ) )' % (Z, Z))], 'imbi12d', '( z = %s -> ( ( ( abs ` ( z - P ) ) < t -> z e. E ) <-> ( ( abs ` ( %s - P ) ) < t -> %s e. E ) ) )' % (Z, Z, Z))
    zE = w.s([w.s([azp, ltt], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < t )' % (A1, Z)), w.s([bsub, ball, zc], 'rspcdva', '( %s -> ( ( abs ` ( %s - P ) ) < t -> %s e. E ) )' % (A1, Z, Z))], 'mpd', '( %s -> %s e. E )' % (A1, Z))
    zlt = w.s([azp, lts], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < S )' % (A1, Z))
    CONC = 'E. x e. E ( x =/= P /\\ ( abs ` ( x - P ) ) < S )'
    xsub = w.s([w.s([], 'neeq1', '( x = %s -> ( x =/= P <-> %s =/= P ) )' % (Z, Z)), w.s([w.s([w.s([], 'oveq1', '( x = %s -> ( x - P ) = ( %s - P ) )' % (Z, Z))], 'fveq2d', '( x = %s -> ( abs ` ( x - P ) ) = ( abs ` ( %s - P ) ) )' % (Z, Z))], 'breq1d', '( x = %s -> ( ( abs ` ( x - P ) ) < S <-> ( abs ` ( %s - P ) ) < S ) )' % (Z, Z))], 'anbi12d',
               '( x = %s -> ( ( x =/= P /\\ ( abs ` ( x - P ) ) < S ) <-> ( %s =/= P /\\ ( abs ` ( %s - P ) ) < S ) ) )' % (Z, Z, Z))
    con = w.s([zE, w.s([zne, zlt], 'jca', '( %s -> ( %s =/= P /\\ ( abs ` ( %s - P ) ) < S ) )' % (A1, Z, Z)), w.s([xsub], 'rspcev', '( ( %s e. E /\\ ( %s =/= P /\\ ( abs ` ( %s - P ) ) < S ) ) -> %s )' % (Z, Z, Z, CONC))], 'syl2anc', '( %s -> %s )' % (A1, CONC))
    w.qed([ex, con], 'rexlimddv', '( %s -> %s )' % (A0, CONC))
    run1(w)

    # ---- cncfzero -------------------------------------------------------------------
    w = W('cncfzero', 'A continuous function on an open set that vanishes at every point other than P vanishes at P too.')
    ZER0 = 'A. z e. E ( z =/= P -> ( H ` z ) = 0 )'
    A0 = '( ( H e. ( E -cn-> CC ) /\\ E e. %s /\\ P e. E ) /\\ %s )' % (TOP, ZER0)
    hyp = w.s([], 'simpl', '( %s -> ( H e. ( E -cn-> CC ) /\\ E e. %s /\\ P e. E ) )' % (A0, TOP))
    zer = w.s([], 'simpr', '( %s -> %s )' % (A0, ZER0))
    hcn = w.s([hyp, w.inst('simp1')], 'syl', '( %s -> H e. ( E -cn-> CC ) )' % A0)
    ee = w.s([hyp, w.inst('simp2')], 'syl', '( %s -> E e. %s )' % (A0, TOP))
    pe = w.s([hyp, w.inst('simp3')], 'syl', '( %s -> P e. E )' % A0)
    A1 = '( %s /\\ ( H ` P ) =/= 0 )' % A0
    NEAR = 'A. z e. E ( ( abs ` ( z - P ) ) < r -> ( H ` z ) =/= 0 )'
    near = w.s([w.s([hcn], 'adantr', '( %s -> H e. ( E -cn-> CC ) )' % A1), w.s([pe], 'adantr', '( %s -> P e. E )' % A1), w.s([], 'simpr', '( %s -> ( H ` P ) =/= 0 )' % A1), w.inst('cncfne0')], 'syl3anc', '( %s -> E. r e. RR+ %s )' % (A1, NEAR))
    A2 = '( %s /\\ ( r e. RR+ /\\ %s ) )' % (A1, NEAR)
    rrp = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (A2, NEAR)), w.inst('simpl')], 'syl', '( %s -> r e. RR+ )' % A2)
    nr = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (A2, NEAR)), w.inst('simpr')], 'syl', '( %s -> %s )' % (A2, NEAR))
    PT = 'E. x e. E ( x =/= P /\\ ( abs ` ( x - P ) ) < r )'
    pt = w.s([w.s([w.s([ee], 'ad2antrr', '( %s -> E e. %s )' % (A2, TOP)), w.s([pe], 'ad2antrr', '( %s -> P e. E )' % A2)], 'jca', '( %s -> ( E e. %s /\\ P e. E ) )' % (A2, TOP)), rrp, w.inst('cnptnear')], 'syl2anc', '( %s -> %s )' % (A2, PT))
    A3 = '( %s /\\ ( x e. E /\\ ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) ) )' % A2
    xe = w.s([w.s([], 'simpr', '( %s -> ( x e. E /\\ ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) ) )' % A3), w.inst('simpl')], 'syl', '( %s -> x e. E )' % A3)
    xp = w.s([w.s([], 'simpr', '( %s -> ( x e. E /\\ ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) ) )' % A3), w.inst('simpr')], 'syl', '( %s -> ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) )' % A3)
    xne = w.s([xp, w.inst('simpl')], 'syl', '( %s -> x =/= P )' % A3)
    xlt = w.s([xp, w.inst('simpr')], 'syl', '( %s -> ( abs ` ( x - P ) ) < r )' % A3)
    zsub = w.s([w.s([], 'neeq1', '( z = x -> ( z =/= P <-> x =/= P ) )'), w.s([w.s([], 'fveq2', '( z = x -> ( H ` z ) = ( H ` x ) )')], 'eqeq1d', '( z = x -> ( ( H ` z ) = 0 <-> ( H ` x ) = 0 ) )')], 'imbi12d',
               '( z = x -> ( ( z =/= P -> ( H ` z ) = 0 ) <-> ( x =/= P -> ( H ` x ) = 0 ) ) )')
    hx0 = w.s([xne, w.s([zsub, w.s([zer], 'ad3antrrr', '( %s -> %s )' % (A3, ZER0)), xe], 'rspcdva', '( %s -> ( x =/= P -> ( H ` x ) = 0 ) )' % A3)], 'mpd', '( %s -> ( H ` x ) = 0 )' % A3)
    nsub = w.s([w.s([w.s([w.s([], 'oveq1', '( z = x -> ( z - P ) = ( x - P ) )')], 'fveq2d', '( z = x -> ( abs ` ( z - P ) ) = ( abs ` ( x - P ) ) )')], 'breq1d', '( z = x -> ( ( abs ` ( z - P ) ) < r <-> ( abs ` ( x - P ) ) < r ) )'),
               w.s([w.s([], 'fveq2', '( z = x -> ( H ` z ) = ( H ` x ) )')], 'neeq1d', '( z = x -> ( ( H ` z ) =/= 0 <-> ( H ` x ) =/= 0 ) )')], 'imbi12d',
              '( z = x -> ( ( ( abs ` ( z - P ) ) < r -> ( H ` z ) =/= 0 ) <-> ( ( abs ` ( x - P ) ) < r -> ( H ` x ) =/= 0 ) ) )')
    hxne = w.s([xlt, w.s([nsub, w.s([nr], 'adantr', '( %s -> %s )' % (A3, NEAR)), xe], 'rspcdva', '( %s -> ( ( abs ` ( x - P ) ) < r -> ( H ` x ) =/= 0 ) )' % A3)], 'mpd', '( %s -> ( H ` x ) =/= 0 )' % A3)
    f3 = w.s([hxne, hx0], 'pm2.21ddne', '( %s -> F. )' % A3)
    f2 = w.s([pt, f3], 'rexlimddv', '( %s -> F. )' % A2)
    f1 = w.s([near, f2], 'rexlimddv', '( %s -> F. )' % A1)
    w.qed([w.s([f1], 'inegd', '( %s -> -. ( H ` P ) =/= 0 )' % A0), w.s([], 'nne', '( -. ( H ` P ) =/= 0 <-> ( H ` P ) = 0 )')], 'sylib', '( %s -> ( H ` P ) = 0 )' % A0)
    run1(w)

    # ---- holordunilem ---------------------------------------------------------------
    w = W('holordunilem', 'Two local factorisations of F at P with continuous cofactors nonzero at P cannot have different exponents: the smaller exponent is impossible.')
    T1 = T('E', 'G', 'N'); T2 = T('D', 'H', 'M')
    A0 = '( ( %s /\\ %s ) /\\ N < M )' % (T1, T2)
    t12 = w.s([], 'simpl', '( %s -> ( %s /\\ %s ) )' % (A0, T1, T2))
    t1 = w.s([t12, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, T1))
    t2 = w.s([t12, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, T2))
    lt = w.s([], 'simpr', '( %s -> N < M )' % A0)
    def unpack(t, E, G, N):
        e1 = w.s([t, w.inst('simp1')], 'syl', '( %s -> ( %s e. %s /\\ P e. %s ) )' % (A0, E, TOP, E))
        g1 = w.s([t, w.inst('simp2')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s ` P ) =/= 0 ) )' % (A0, G, E, G))
        n1 = w.s([t, w.inst('simp3')], 'syl', '( %s -> ( %s e. NN0 /\\ %s ) )' % (A0, N, FACE(E, G, N)))
        r = {}
        r['ee'] = w.s([e1, w.inst('simpl')], 'syl', '( %s -> %s e. %s )' % (A0, E, TOP))
        r['pe'] = w.s([e1, w.inst('simpr')], 'syl', '( %s -> P e. %s )' % (A0, E))
        r['gcn'] = w.s([g1, w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, G, E))
        r['gpne'] = w.s([g1, w.inst('simpr')], 'syl', '( %s -> ( %s ` P ) =/= 0 )' % (A0, G))
        r['nn0'] = w.s([n1, w.inst('simpl')], 'syl', '( %s -> %s e. NN0 )' % (A0, N))
        r['fac'] = w.s([n1, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, FACE(E, G, N)))
        r['gf'] = w.s([r['gcn'], w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (A0, G, E))
        r['ecc'] = w.s([r['gcn'], w.inst('cncfrss')], 'syl', '( %s -> %s C_ CC )' % (A0, E))
        return r
    a = unpack(t1, 'E', 'G', 'N'); b = unpack(t2, 'D', 'H', 'M')
    pc = w.s([a['ecc'], a['pe']], 'sseldd', '( %s -> P e. CC )' % A0)
    EI = '( E i^i D )'
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    topt = w.s([w.s([ej], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (A0, TOP))
    ei = w.s([topt, a['ee'], b['ee'], w.inst('inopn')], 'syl3anc', '( %s -> %s e. %s )' % (A0, EI, TOP))
    pei = w.s([w.s([a['pe'], b['pe']], 'jca', '( %s -> ( P e. E /\\ P e. D ) )' % A0), w.s([], 'elin', '( P e. %s <-> ( P e. E /\\ P e. D ) )' % EI)], 'sylibr', '( %s -> P e. %s )' % (A0, EI))
    eis1 = closed(w, A0, 'inss1', '%s C_ E' % EI); eis2 = closed(w, A0, 'inss2', '%s C_ D' % EI)
    eicc = w.s([eis1, a['ecc']], 'sstrd', '( %s -> %s C_ CC )' % (A0, EI))
    MN = '( M - N )'
    nz = w.s([a['nn0']], 'nn0zd', '( %s -> N e. ZZ )' % A0); mz = w.s([b['nn0']], 'nn0zd', '( %s -> M e. ZZ )' % A0)
    mnn = w.s([lt, w.s([nz, mz, w.inst('znnsub')], 'syl2anc', '( %s -> ( N < M <-> %s e. NN ) )' % (A0, MN))], 'mpbid', '( %s -> %s e. NN )' % (A0, MN))
    mnn0 = w.s([mnn], 'nnnn0d', '( %s -> %s e. NN0 )' % (A0, MN))
    KB = lambda y: '( ( G ` %s ) - ( ( ( %s - P ) ^ %s ) x. ( H ` %s ) ) )' % (y, y, MN, y)
    K = '( y e. %s |-> %s )' % (EI, KB('y'))
    # continuity of K
    gr = w.s([a['gf'], eis1], 'feqresmpt', '( %s -> ( G |` %s ) = ( y e. %s |-> ( G ` y ) ) )' % (A0, EI, EI))
    grc = w.s([w.s([eis1, w.inst('rescncf')], 'syl', '( %s -> ( G e. ( E -cn-> CC ) -> ( G |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, EI, EI)), a['gcn']], 'mpd', '( %s -> ( G |` %s ) e. ( %s -cn-> CC ) )' % (A0, EI, EI))
    gmap = w.s([gr, grc], 'eqeltrrd', '( %s -> ( y e. %s |-> ( G ` y ) ) e. ( %s -cn-> CC ) )' % (A0, EI, EI))
    hr = w.s([b['gf'], eis2], 'feqresmpt', '( %s -> ( H |` %s ) = ( y e. %s |-> ( H ` y ) ) )' % (A0, EI, EI))
    hrc = w.s([w.s([eis2, w.inst('rescncf')], 'syl', '( %s -> ( H e. ( D -cn-> CC ) -> ( H |` %s ) e. ( %s -cn-> CC ) ) )' % (A0, EI, EI)), b['gcn']], 'mpd', '( %s -> ( H |` %s ) e. ( %s -cn-> CC ) )' % (A0, EI, EI))
    hmap = w.s([hr, hrc], 'eqeltrrd', '( %s -> ( y e. %s |-> ( H ` y ) ) e. ( %s -cn-> CC ) )' % (A0, EI, EI))
    PW = '( y e. %s |-> ( ( y - P ) ^ %s ) )' % (EI, MN)
    pw = w.s([w.s([w.s([ei, eicc], 'jca', '( %s -> ( %s e. %s /\\ %s C_ CC ) )' % (A0, EI, TOP, EI)), w.s([pc, mnn], 'jca', '( %s -> ( P e. CC /\\ %s e. NN ) )' % (A0, MN)), w.inst('holpowp')], 'syl2anc',
                  '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (A0, PW, EI, EI, PW)), w.inst('simpl')], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, PW, EI))
    mul = w.s([pw, hmap], 'mulcncf', '( %s -> ( y e. %s |-> ( ( ( y - P ) ^ %s ) x. ( H ` y ) ) ) e. ( %s -cn-> CC ) )' % (A0, EI, MN, EI))
    kcn = w.s([gmap, mul], 'subcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, K, EI))
    # K vanishes off P
    def kval(ante, X, xin):
        sub = w.s([w.s([], 'fveq2', '( y = %s -> ( G ` y ) = ( G ` %s ) )' % (X, X)), w.s([w.s([w.s([], 'oveq1', '( y = %s -> ( y - P ) = ( %s - P ) )' % (X, X))], 'oveq1d', '( y = %s -> ( ( y - P ) ^ %s ) = ( ( %s - P ) ^ %s ) )' % (X, MN, X, MN)), w.s([], 'fveq2', '( y = %s -> ( H ` y ) = ( H ` %s ) )' % (X, X))], 'oveq12d',
                                                                                          '( y = %s -> ( ( ( y - P ) ^ %s ) x. ( H ` y ) ) = ( ( ( %s - P ) ^ %s ) x. ( H ` %s ) ) )' % (X, MN, X, MN, X))], 'oveq12d', '( y = %s -> %s = %s )' % (X, KB('y'), KB(X)))
        vx = w.s([w.s([], 'ovex', '%s e. _V' % KB(X))], 'a1i', '( %s -> %s e. _V )' % (ante, KB(X)))
        return w.s([xin, vx, w.s([sub, w.s([], 'eqid', '%s = %s' % (K, K))], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (X, EI, KB(X), K, X, KB(X)))], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, K, X, KB(X)))
    U0 = '( %s /\\ v e. %s )' % (A0, EI)
    U1 = '( %s /\\ v =/= P )' % U0
    vei = w.s([w.s([], 'simpr', '( %s -> v e. %s )' % (U0, EI))], 'adantr', '( %s -> v e. %s )' % (U1, EI))
    vE = w.s([w.s([eis1], 'ad2antrr', '( %s -> %s C_ E )' % (U1, EI)), vei], 'sseldd', '( %s -> v e. E )' % U1)
    vD = w.s([w.s([eis2], 'ad2antrr', '( %s -> %s C_ D )' % (U1, EI)), vei], 'sseldd', '( %s -> v e. D )' % U1)
    vc = w.s([w.s([eicc], 'ad2antrr', '( %s -> %s C_ CC )' % (U1, EI)), vei], 'sseldd', '( %s -> v e. CC )' % U1)
    vne = w.s([], 'simpr', '( %s -> v =/= P )' % U1)
    def L1(st, f):
        return w.s([st], 'ad2antrr', '( %s -> %s )' % (U1, f))
    def facat(G, N):
        A = 'z = v'
        return w.s([w.s([], 'fveq2', '( %s -> ( F ` z ) = ( F ` v ) )' % A), w.s([w.s([w.s([], 'oveq1', '( %s -> ( z - P ) = ( v - P ) )' % A)], 'oveq1d', '( %s -> ( ( z - P ) ^ %s ) = ( ( v - P ) ^ %s ) )' % (A, N, N)), w.s([], 'fveq2', '( %s -> ( %s ` z ) = ( %s ` v ) )' % (A, G, G))], 'oveq12d',
                                                                                  '( %s -> ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) = ( ( ( v - P ) ^ %s ) x. ( %s ` v ) ) )' % (A, N, G, N, G))], 'eqeq12d',
                   '( %s -> ( ( F ` z ) = ( ( ( z - P ) ^ %s ) x. ( %s ` z ) ) <-> ( F ` v ) = ( ( ( v - P ) ^ %s ) x. ( %s ` v ) ) ) )' % (A, N, G, N, G))
    fz1 = w.s([facat('G', 'N'), L1(a['fac'], FACE('E', 'G', 'N')), vE], 'rspcdva', '( %s -> ( F ` v ) = ( ( ( v - P ) ^ N ) x. ( G ` v ) ) )' % U1)
    fz2 = w.s([facat('H', 'M'), L1(b['fac'], FACE('D', 'H', 'M')), vD], 'rspcdva', '( %s -> ( F ` v ) = ( ( ( v - P ) ^ M ) x. ( H ` v ) ) )' % U1)
    eq = w.s([fz1, fz2], 'eqtr3d', '( %s -> ( ( ( v - P ) ^ N ) x. ( G ` v ) ) = ( ( ( v - P ) ^ M ) x. ( H ` v ) ) )' % U1)
    pc1 = L1(pc, 'P e. CC')
    vp = w.s([vc, pc1], 'subcld', '( %s -> ( v - P ) e. CC )' % U1)
    nc = w.s([L1(a['nn0'], 'N e. NN0')], 'nn0cnd', '( %s -> N e. CC )' % U1); mc = w.s([L1(b['nn0'], 'M e. NN0')], 'nn0cnd', '( %s -> M e. CC )' % U1)
    ea = w.s([vp, L1(a['nn0'], 'N e. NN0'), L1(mnn0, '%s e. NN0' % MN), w.inst('expadd')], 'syl3anc', '( %s -> ( ( v - P ) ^ ( N + %s ) ) = ( ( ( v - P ) ^ N ) x. ( ( v - P ) ^ %s ) ) )' % (U1, MN, MN))
    nm = w.s([w.s([nc, mc], 'pncan3d', '( %s -> ( N + %s ) = M )' % (U1, MN))], 'oveq2d', '( %s -> ( ( v - P ) ^ ( N + %s ) ) = ( ( v - P ) ^ M ) )' % (U1, MN))
    em = w.s([nm, ea], 'eqtr3d', '( %s -> ( ( v - P ) ^ M ) = ( ( ( v - P ) ^ N ) x. ( ( v - P ) ^ %s ) ) )' % (U1, MN))
    vpn = w.s([vp, L1(a['nn0'], 'N e. NN0')], 'expcld', '( %s -> ( ( v - P ) ^ N ) e. CC )' % U1)
    vpm = w.s([vp, L1(mnn0, '%s e. NN0' % MN)], 'expcld', '( %s -> ( ( v - P ) ^ %s ) e. CC )' % (U1, MN))
    gv = w.s([L1(a['gf'], 'G : E --> CC'), vE], 'ffvelcdmd', '( %s -> ( G ` v ) e. CC )' % U1)
    hv = w.s([L1(b['gf'], 'H : D --> CC'), vD], 'ffvelcdmd', '( %s -> ( H ` v ) e. CC )' % U1)
    rhs = w.s([w.s([em], 'oveq1d', '( %s -> ( ( ( v - P ) ^ M ) x. ( H ` v ) ) = ( ( ( ( v - P ) ^ N ) x. ( ( v - P ) ^ %s ) ) x. ( H ` v ) ) )' % (U1, MN)), w.s([vpn, vpm, hv], 'mulassd', '( %s -> ( ( ( ( v - P ) ^ N ) x. ( ( v - P ) ^ %s ) ) x. ( H ` v ) ) = ( ( ( v - P ) ^ N ) x. ( ( ( v - P ) ^ %s ) x. ( H ` v ) ) ) )' % (U1, MN, MN))], 'eqtrd',
              '( %s -> ( ( ( v - P ) ^ M ) x. ( H ` v ) ) = ( ( ( v - P ) ^ N ) x. ( ( ( v - P ) ^ %s ) x. ( H ` v ) ) ) )' % (U1, MN))
    eq2 = w.s([eq, rhs], 'eqtrd', '( %s -> ( ( ( v - P ) ^ N ) x. ( G ` v ) ) = ( ( ( v - P ) ^ N ) x. ( ( ( v - P ) ^ %s ) x. ( H ` v ) ) ) )' % (U1, MN))
    pne = w.s([vp, w.s([vc, pc1, vne], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % U1), w.s([L1(a['nn0'], 'N e. NN0')], 'nn0zd', '( %s -> N e. ZZ )' % U1), w.inst('expne0i')], 'syl3anc', '( %s -> ( ( v - P ) ^ N ) =/= 0 )' % U1)
    can = w.s([vpn, gv, w.s([vpm, hv], 'mulcld', '( %s -> ( ( ( v - P ) ^ %s ) x. ( H ` v ) ) e. CC )' % (U1, MN)), pne, eq2], 'mulcanad', '( %s -> ( G ` v ) = ( ( ( v - P ) ^ %s ) x. ( H ` v ) ) )' % (U1, MN))
    k0 = w.s([can, w.s([gv, w.s([vpm, hv], 'mulcld', '( %s -> ( ( ( v - P ) ^ %s ) x. ( H ` v ) ) e. CC )' % (U1, MN)), w.inst('subeq0')], 'syl2anc', '( %s -> ( %s = 0 <-> ( G ` v ) = ( ( ( v - P ) ^ %s ) x. ( H ` v ) ) ) )' % (U1, KB('v'), MN))], 'mpbird', '( %s -> %s = 0 )' % (U1, KB('v')))
    kv = w.s([kval(U1, 'v', vei), k0], 'eqtrd', '( %s -> ( %s ` v ) = 0 )' % (U1, K))
    ralv = w.s([w.s([kv], 'ex', '( %s -> ( v =/= P -> ( %s ` v ) = 0 ) )' % (U0, K))], 'ralrimiva', '( %s -> A. v e. %s ( v =/= P -> ( %s ` v ) = 0 ) )' % (A0, EI, K))
    kp0 = w.s([w.s([kcn, ei, pei], '3jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s e. %s /\\ P e. %s ) )' % (A0, K, EI, EI, TOP, EI)), ralv, w.inst('cncfzero')], 'syl2anc', '( %s -> ( %s ` P ) = 0 )' % (A0, K))
    kpv = kval(A0, 'P', pei)
    hp = w.s([b['gf'], b['pe']], 'ffvelcdmd', '( %s -> ( H ` P ) e. CC )' % A0)
    z1 = w.s([w.s([w.s([w.s([pc], 'subidd', '( %s -> ( P - P ) = 0 )' % A0)], 'oveq1d', '( %s -> ( ( P - P ) ^ %s ) = ( 0 ^ %s ) )' % (A0, MN, MN)), w.s([mnn, w.inst('0exp')], 'syl', '( %s -> ( 0 ^ %s ) = 0 )' % (A0, MN))], 'eqtrd', '( %s -> ( ( P - P ) ^ %s ) = 0 )' % (A0, MN))], 'oveq1d',
             '( %s -> ( ( ( P - P ) ^ %s ) x. ( H ` P ) ) = ( 0 x. ( H ` P ) ) )' % (A0, MN))
    z2 = w.s([z1, w.s([hp], 'mul02d', '( %s -> ( 0 x. ( H ` P ) ) = 0 )' % A0)], 'eqtrd', '( %s -> ( ( ( P - P ) ^ %s ) x. ( H ` P ) ) = 0 )' % (A0, MN))
    gp = w.s([a['gf'], a['pe']], 'ffvelcdmd', '( %s -> ( G ` P ) e. CC )' % A0)
    kpg = w.s([kpv, w.s([w.s([z2], 'oveq2d', '( %s -> %s = ( ( G ` P ) - 0 ) )' % (A0, KB('P'))), w.s([gp], 'subid1d', '( %s -> ( ( G ` P ) - 0 ) = ( G ` P ) )' % A0)], 'eqtrd', '( %s -> %s = ( G ` P ) )' % (A0, KB('P')))], 'eqtrd', '( %s -> ( %s ` P ) = ( G ` P ) )' % (A0, K))
    gp0 = w.s([kpg, kp0], 'eqtr3d', '( %s -> ( G ` P ) = 0 )' % A0)
    fals = w.s([a['gpne'], gp0], 'pm2.21ddne', '( %s -> F. )' % A0)
    w.qed([fals], 'inegd', '( ( %s /\\ %s ) -> -. N < M )' % (T1, T2))
    run1(w)

    # ---- holorduni ------------------------------------------------------------------
    w = W('holorduni', 'Uniqueness of the exponent of a local factorisation with a continuous cofactor nonzero at the point.')
    A0 = '( %s /\\ %s )' % (T1, T2)
    l1 = w.s([], 'holordunilem', '( %s -> -. N < M )' % A0)
    l2 = w.s([w.s([], 'holordunilem', '( ( %s /\\ %s ) -> -. M < N )' % (T2, T1))], 'ancoms', '( %s -> -. M < N )' % A0)
    nr = w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (A0, T1)), w.inst('simp3')], 'syl', '( %s -> ( N e. NN0 /\\ %s ) )' % (A0, FACE('E', 'G', 'N'))), w.inst('simpl')], 'syl', '( %s -> N e. NN0 )' % A0)], 'nn0red', '( %s -> N e. RR )' % A0)
    mr = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (A0, T2)), w.inst('simp3')], 'syl', '( %s -> ( M e. NN0 /\\ %s ) )' % (A0, FACE('D', 'H', 'M'))), w.inst('simpl')], 'syl', '( %s -> M e. NN0 )' % A0)], 'nn0red', '( %s -> M e. RR )' % A0)
    w.qed([w.s([l1, l2], 'jca', '( %s -> ( -. N < M /\\ -. M < N ) )' % A0), w.s([nr, mr, w.inst('lttri3')], 'syl2anc', '( %s -> ( N = M <-> ( -. N < M /\\ -. M < N ) ) )' % A0)], 'mpbird', '( %s -> N = M )' % A0)
    run1(w)

    # ---- holordeq -------------------------------------------------------------------
    w = W('holordeq', 'The order of vanishing of F at P is the exponent of any local factorisation of F at P with a holomorphic cofactor nonzero at P .')
    A0 = HEQ('E', 'G', 'N')
    fe = w.s([w.s([], 'simp1', '( %s -> ( F e. V /\\ ( E e. %s /\\ P e. E ) ) )' % (A0, TOP)), w.inst('simpl')], 'syl', '( %s -> F e. V )' % A0)
    ep = w.s([w.s([], 'simp1', '( %s -> ( F e. V /\\ ( E e. %s /\\ P e. E ) ) )' % (A0, TOP)), w.inst('simpr')], 'syl', '( %s -> ( E e. %s /\\ P e. E ) )' % (A0, TOP))
    ee = w.s([ep, w.inst('simpl')], 'syl', '( %s -> E e. %s )' % (A0, TOP)); pe = w.s([ep, w.inst('simpr')], 'syl', '( %s -> P e. E )' % A0)
    gg = w.s([], 'simp2', '( %s -> ( %s /\\ ( G ` P ) =/= 0 ) )' % (A0, HOLG('G', 'E')))
    hg = w.s([gg, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOLG('G', 'E'))); gpne = w.s([gg, w.inst('simpr')], 'syl', '( %s -> ( G ` P ) =/= 0 )' % A0)
    gcn = w.s([hg, w.inst('simpl')], 'syl', '( %s -> G e. ( E -cn-> CC ) )' % A0)
    nf = w.s([], 'simp3', '( %s -> ( N e. NN0 /\\ %s ) )' % (A0, FACE('E', 'G', 'N')))
    nn0 = w.s([nf, w.inst('simpl')], 'syl', '( %s -> N e. NN0 )' % A0); fac = w.s([nf, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, FACE('E', 'G', 'N')))
    pc = w.s([w.s([gcn, w.inst('cncfrss')], 'syl', '( %s -> E C_ CC )' % A0), pe], 'sseldd', '( %s -> P e. CC )' % A0)
    val = w.s([fe, pc, w.inst('holordval')], 'syl2anc', '( %s -> ( F holord P ) = %s )' % (A0, INF()))
    # the set of exponents is { N }
    B0 = '( %s /\\ n e. NN0 )' % A0
    # (->)
    C0 = '( ( %s /\\ d e. %s ) /\\ %s )' % (B0, TOP, ORDB('d', 'g', 'n'))
    ob = w.s([], 'simpr', '( %s -> %s )' % (C0, ORDB('d', 'g', 'n')))
    b0 = w.s([], 'simpll', '( %s -> %s )' % (C0, B0))
    a0c = w.s([b0, w.inst('simpl')], 'syl', '( %s -> %s )' % (C0, A0))
    dt = w.s([], 'simplr', '( %s -> d e. %s )' % (C0, TOP))
    pd = w.s([ob, w.inst('simp1')], 'syl', '( %s -> P e. d )' % C0)
    hgd = w.s([ob, w.inst('simp2')], 'syl', '( %s -> %s )' % (C0, HOLG('g', 'd')))
    gd = w.s([ob, w.inst('simp3')], 'syl', '( %s -> ( ( g ` P ) =/= 0 /\\ %s ) )' % (C0, FACE('d', 'g', 'n')))
    t1 = w.s([w.s([w.s([a0c, ee], 'syl', '( %s -> E e. %s )' % (C0, TOP)), w.s([a0c, pe], 'syl', '( %s -> P e. E )' % C0)], 'jca', '( %s -> ( E e. %s /\\ P e. E ) )' % (C0, TOP)),
              w.s([w.s([a0c, gcn], 'syl', '( %s -> G e. ( E -cn-> CC ) )' % C0), w.s([a0c, gpne], 'syl', '( %s -> ( G ` P ) =/= 0 )' % C0)], 'jca', '( %s -> ( G e. ( E -cn-> CC ) /\\ ( G ` P ) =/= 0 ) )' % C0),
              w.s([a0c, nf], 'syl', '( %s -> ( N e. NN0 /\\ %s ) )' % (C0, FACE('E', 'G', 'N')))], '3jca', '( %s -> %s )' % (C0, T('E', 'G', 'N')))
    t2 = w.s([w.s([dt, pd], 'jca', '( %s -> ( d e. %s /\\ P e. d ) )' % (C0, TOP)),
              w.s([w.s([hgd, w.inst('simpl')], 'syl', '( %s -> g e. ( d -cn-> CC ) )' % C0), w.s([gd, w.inst('simpl')], 'syl', '( %s -> ( g ` P ) =/= 0 )' % C0)], 'jca', '( %s -> ( g e. ( d -cn-> CC ) /\\ ( g ` P ) =/= 0 ) )' % C0),
              w.s([w.s([b0, w.inst('simpr')], 'syl', '( %s -> n e. NN0 )' % C0), w.s([gd, w.inst('simpr')], 'syl', '( %s -> %s )' % (C0, FACE('d', 'g', 'n')))], 'jca', '( %s -> ( n e. NN0 /\\ %s ) )' % (C0, FACE('d', 'g', 'n')))], '3jca',
             '( %s -> %s )' % (C0, T('d', 'g', 'n')))
    neq = w.s([w.s([t1, t2, w.inst('holorduni')], 'syl2anc', '( %s -> N = n )' % C0)], 'eqcomd', '( %s -> n = N )' % C0)
    fwd = w.s([w.s([w.s([w.s([neq], 'ex', '( ( %s /\\ d e. %s ) -> ( %s -> n = N ) )' % (B0, TOP, ORDB('d', 'g', 'n')))], 'exlimdv', '( ( %s /\\ d e. %s ) -> ( E. g %s -> n = N ) )' % (B0, TOP, ORDB('d', 'g', 'n')))], 'rexlimdva',
                  '( %s -> ( %s -> n = N ) )' % (B0, ORD('n')))], 'imp', '( ( %s /\\ %s ) -> n = N )' % (B0, ORD('n')))
    # (<-)
    ordN = w.s([pe, hg, w.s([gpne, fac], 'jca', '( %s -> ( ( G ` P ) =/= 0 /\\ %s ) )' % (A0, FACE('E', 'G', 'N')))], '3jca', '( %s -> %s )' % (A0, ORDB('E', 'G', 'N')))
    gsub = w.s([w.s([], 'eleq1', '( g = G -> ( g e. ( E -cn-> CC ) <-> G e. ( E -cn-> CC ) ) )'), w.s([w.s([w.s([], 'oveq2', '( g = G -> ( CC _D g ) = ( CC _D G ) )')], 'dmeqd', '( g = G -> dom ( CC _D g ) = dom ( CC _D G ) )')], 'sseq2d', '( g = G -> ( E C_ dom ( CC _D g ) <-> E C_ dom ( CC _D G ) ) )')], 'anbi12d',
               '( g = G -> ( %s <-> %s ) )' % (HOLG('g', 'E'), HOLG('G', 'E')))
    g3 = w.s([w.s([w.s([], 'fveq1', '( g = G -> ( g ` P ) = ( G ` P ) )')], 'neeq1d', '( g = G -> ( ( g ` P ) =/= 0 <-> ( G ` P ) =/= 0 ) )'),
              w.s([w.s([w.s([w.s([], 'fveq1', '( g = G -> ( g ` z ) = ( G ` z ) )')], 'oveq2d', '( g = G -> ( ( ( z - P ) ^ N ) x. ( g ` z ) ) = ( ( ( z - P ) ^ N ) x. ( G ` z ) ) )')], 'eqeq2d', '( g = G -> ( ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( g ` z ) ) <-> ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( G ` z ) ) ) )')], 'ralbidv',
                   '( g = G -> ( %s <-> %s ) )' % (FACE('E', 'g', 'N'), FACE('E', 'G', 'N')))], 'anbi12d', '( g = G -> ( ( ( g ` P ) =/= 0 /\\ %s ) <-> ( ( G ` P ) =/= 0 /\\ %s ) ) )' % (FACE('E', 'g', 'N'), FACE('E', 'G', 'N')))
    gb = w.s([gsub, g3], '3anbi23d', '( g = G -> ( %s <-> %s ) )' % (ORDB('E', 'g', 'N'), ORDB('E', 'G', 'N')))
    exg = w.s([w.s([gcn], 'elexd', '( %s -> G e. _V )' % A0), ordN, w.s([gb], 'spcegv', '( G e. _V -> ( %s -> E. g %s ) )' % (ORDB('E', 'G', 'N'), ORDB('E', 'g', 'N')))], 'sylc', '( %s -> E. g %s )' % (A0, ORDB('E', 'g', 'N')))
    dsub = w.s([w.s([], 'eleq2', '( d = E -> ( P e. d <-> P e. E ) )'), w.s([w.s([w.s([], 'oveq1', '( d = E -> ( d -cn-> CC ) = ( E -cn-> CC ) )')], 'eleq2d', '( d = E -> ( g e. ( d -cn-> CC ) <-> g e. ( E -cn-> CC ) ) )'), w.s([], 'sseq1', '( d = E -> ( d C_ dom ( CC _D g ) <-> E C_ dom ( CC _D g ) ) )')], 'anbi12d', '( d = E -> ( %s <-> %s ) )' % (HOLG('g', 'd'), HOLG('g', 'E'))),
               w.s([w.s([], 'raleq', '( d = E -> ( %s <-> %s ) )' % (FACE('d', 'g', 'N'), FACE('E', 'g', 'N')))], 'anbi2d', '( d = E -> ( ( ( g ` P ) =/= 0 /\\ %s ) <-> ( ( g ` P ) =/= 0 /\\ %s ) ) )' % (FACE('d', 'g', 'N'), FACE('E', 'g', 'N')))], '3anbi123d',
              '( d = E -> ( %s <-> %s ) )' % (ORDB('d', 'g', 'N'), ORDB('E', 'g', 'N')))
    dsube = w.s([dsub], 'exbidv', '( d = E -> ( E. g %s <-> E. g %s ) )' % (ORDB('d', 'g', 'N'), ORDB('E', 'g', 'N')))
    ordNN = w.s([ee, exg, w.s([dsube], 'rspcev', '( ( E e. %s /\\ E. g %s ) -> %s )' % (TOP, ORDB('E', 'g', 'N'), ORD('N')))], 'syl2anc', '( %s -> %s )' % (A0, ORD('N')))
    B1 = '( %s /\\ n = N )' % B0
    bwd = w.s([w.s([w.s([], 'simpr', '( %s -> n = N )' % B1), ordsubn(w, 'n', 'N')], 'syl', '( %s -> ( %s <-> %s ) )' % (B1, ORD('n'), ORD('N'))), w.s([ordNN], 'ad2antrr', '( %s -> %s )' % (B1, ORD('N')))], 'mpbird', '( %s -> %s )' % (B1, ORD('n')))
    bic = w.s([w.s([fwd], 'ex', '( %s -> ( %s -> n = N ) )' % (B0, ORD('n'))), w.s([bwd], 'ex', '( %s -> ( n = N -> %s ) )' % (B0, ORD('n')))], 'impbid', '( %s -> ( %s <-> n = N ) )' % (B0, ORD('n')))
    rab = w.s([bic], 'rabbidva', '( %s -> %s = { n e. NN0 | n = N } )' % (A0, ORDSET()))
    sn = w.s([rab, w.s([nn0, w.inst('rabsn')], 'syl', '( %s -> { n e. NN0 | n = N } = { N } )' % A0)], 'eqtrd', '( %s -> %s = { N } )' % (A0, ORDSET()))
    inf = w.s([w.s([sn], 'infeq1d', '( %s -> %s = inf ( { N } , RR* , < ) )' % (A0, INF())), w.s([closed(w, A0, 'xrltso', '< Or RR*'), w.s([w.s([nn0], 'nn0red', '( %s -> N e. RR )' % A0)], 'rexrd', '( %s -> N e. RR* )' % A0), w.inst('infsn')], 'syl2anc', '( %s -> inf ( { N } , RR* , < ) = N )' % A0)], 'eqtrd',
              '( %s -> %s = N )' % (A0, INF()))
    w.qed([val, inf], 'eqtrd', '( %s -> ( F holord P ) = N )' % A0)
    run1(w)

    # ---- holordtop ------------------------------------------------------------------
    w = W('holordtop', 'The order of vanishing of a function that vanishes on an open set containing P is +oo (the infimum of the empty set of exponents).')
    ALLZ = 'A. z e. E ( F ` z ) = 0'
    A0 = '( F e. V /\\ ( E e. %s /\\ P e. E ) /\\ %s )' % (TOP, ALLZ)
    fv = w.s([], 'simp1', '( %s -> F e. V )' % A0)
    ep = w.s([], 'simp2', '( %s -> ( E e. %s /\\ P e. E ) )' % (A0, TOP))
    allz = w.s([], 'simp3', '( %s -> %s )' % (A0, ALLZ))
    ee = w.s([ep, w.inst('simpl')], 'syl', '( %s -> E e. %s )' % (A0, TOP)); pe = w.s([ep, w.inst('simpr')], 'syl', '( %s -> P e. E )' % A0)
    un = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    ecc = w.s([w.s([ee, w.inst('elssuni')], 'syl', '( %s -> E C_ U. %s )' % (A0, TOP)), w.s([un], 'eqcomi', 'U. %s = CC' % TOP)], 'sseqtrdi', '( %s -> E C_ CC )' % A0)
    pc = w.s([ecc, pe], 'sseldd', '( %s -> P e. CC )' % A0)
    val = w.s([fv, pc, w.inst('holordval')], 'syl2anc', '( %s -> ( F holord P ) = %s )' % (A0, INF()))
    B0 = '( %s /\\ n e. NN0 )' % A0
    C0 = '( ( %s /\\ d e. %s ) /\\ %s )' % (B0, TOP, ORDB('d', 'g', 'n'))
    ob = w.s([], 'simpr', '( %s -> %s )' % (C0, ORDB('d', 'g', 'n')))
    b0 = w.s([], 'simpll', '( %s -> %s )' % (C0, B0))
    a0c = w.s([b0, w.inst('simpl')], 'syl', '( %s -> %s )' % (C0, A0))
    dt = w.s([], 'simplr', '( %s -> d e. %s )' % (C0, TOP))
    pd = w.s([ob, w.inst('simp1')], 'syl', '( %s -> P e. d )' % C0)
    gcn = w.s([w.s([ob, w.inst('simp2')], 'syl', '( %s -> %s )' % (C0, HOLG('g', 'd'))), w.inst('simpl')], 'syl', '( %s -> g e. ( d -cn-> CC ) )' % C0)
    gd = w.s([ob, w.inst('simp3')], 'syl', '( %s -> ( ( g ` P ) =/= 0 /\\ %s ) )' % (C0, FACE('d', 'g', 'n')))
    gpne = w.s([gd, w.inst('simpl')], 'syl', '( %s -> ( g ` P ) =/= 0 )' % C0)
    facd = w.s([gd, w.inst('simpr')], 'syl', '( %s -> %s )' % (C0, FACE('d', 'g', 'n')))
    ISOD = 'A. z e. d ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) -> ( F ` z ) =/= 0 )'
    iso = w.s([w.s([gcn, pd, gpne], '3jca', '( %s -> ( g e. ( d -cn-> CC ) /\\ P e. d /\\ ( g ` P ) =/= 0 ) )' % C0), w.s([w.s([b0, w.inst('simpr')], 'syl', '( %s -> n e. NN0 )' % C0), facd], 'jca', '( %s -> ( n e. NN0 /\\ %s ) )' % (C0, FACE('d', 'g', 'n'))), w.inst('holzisol')], 'syl2anc',
              '( %s -> E. r e. RR+ %s )' % (C0, ISOD))
    C1 = '( %s /\\ ( r e. RR+ /\\ %s ) )' % (C0, ISOD)
    rrp = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (C1, ISOD)), w.inst('simpl')], 'syl', '( %s -> r e. RR+ )' % C1)
    isod = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (C1, ISOD)), w.inst('simpr')], 'syl', '( %s -> %s )' % (C1, ISOD))
    EI = '( E i^i d )'
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    topt = w.s([w.s([ej], 'cnfldtop', '%s e. Top' % TOP)], 'a1i', '( %s -> %s e. Top )' % (C1, TOP))
    ei = w.s([topt, w.s([w.s([a0c, ee], 'syl', '( %s -> E e. %s )' % (C0, TOP))], 'adantr', '( %s -> E e. %s )' % (C1, TOP)), w.s([dt], 'adantr', '( %s -> d e. %s )' % (C1, TOP)), w.inst('inopn')], 'syl3anc', '( %s -> %s e. %s )' % (C1, EI, TOP))
    pei = w.s([w.s([w.s([w.s([a0c, pe], 'syl', '( %s -> P e. E )' % C0)], 'adantr', '( %s -> P e. E )' % C1), w.s([pd], 'adantr', '( %s -> P e. d )' % C1)], 'jca', '( %s -> ( P e. E /\\ P e. d ) )' % C1), w.s([], 'elin', '( P e. %s <-> ( P e. E /\\ P e. d ) )' % EI)], 'sylibr', '( %s -> P e. %s )' % (C1, EI))
    PT = 'E. x e. %s ( x =/= P /\\ ( abs ` ( x - P ) ) < r )' % EI
    pt = w.s([w.s([ei, pei], 'jca', '( %s -> ( %s e. %s /\\ P e. %s ) )' % (C1, EI, TOP, EI)), rrp, w.inst('cnptnear')], 'syl2anc', '( %s -> %s )' % (C1, PT))
    C2 = '( %s /\\ ( x e. %s /\\ ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) ) )' % (C1, EI)
    xe = w.s([w.s([], 'simpr', '( %s -> ( x e. %s /\\ ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) ) )' % (C2, EI)), w.inst('simpl')], 'syl', '( %s -> x e. %s )' % (C2, EI))
    xp = w.s([w.s([], 'simpr', '( %s -> ( x e. %s /\\ ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) ) )' % (C2, EI)), w.inst('simpr')], 'syl', '( %s -> ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) )' % C2)
    xin = w.s([xe, w.s([], 'elin', '( x e. %s <-> ( x e. E /\\ x e. d ) )' % EI)], 'sylib', '( %s -> ( x e. E /\\ x e. d ) )' % C2)
    xE = w.s([xin, w.inst('simpl')], 'syl', '( %s -> x e. E )' % C2); xd = w.s([xin, w.inst('simpr')], 'syl', '( %s -> x e. d )' % C2)
    fx0 = w.s([w.s([w.s([], 'fveq2', '( z = x -> ( F ` z ) = ( F ` x ) )')], 'eqeq1d', '( z = x -> ( ( F ` z ) = 0 <-> ( F ` x ) = 0 ) )'), w.s([w.s([w.s([a0c, allz], 'syl', '( %s -> %s )' % (C0, ALLZ))], 'adantr', '( %s -> %s )' % (C1, ALLZ))], 'adantr', '( %s -> %s )' % (C2, ALLZ)), xE], 'rspcdva', '( %s -> ( F ` x ) = 0 )' % C2)
    isub = w.s([w.s([w.s([], 'neeq1', '( z = x -> ( z =/= P <-> x =/= P ) )'), w.s([w.s([w.s([], 'oveq1', '( z = x -> ( z - P ) = ( x - P ) )')], 'fveq2d', '( z = x -> ( abs ` ( z - P ) ) = ( abs ` ( x - P ) ) )')], 'breq1d', '( z = x -> ( ( abs ` ( z - P ) ) < r <-> ( abs ` ( x - P ) ) < r ) )')], 'anbi12d',
                    '( z = x -> ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) <-> ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) ) )'),
               w.s([w.s([], 'fveq2', '( z = x -> ( F ` z ) = ( F ` x ) )')], 'neeq1d', '( z = x -> ( ( F ` z ) =/= 0 <-> ( F ` x ) =/= 0 ) )')], 'imbi12d',
              '( z = x -> ( ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) -> ( F ` z ) =/= 0 ) <-> ( ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) -> ( F ` x ) =/= 0 ) ) )')
    fxne = w.s([xp, w.s([isub, w.s([isod], 'adantr', '( %s -> %s )' % (C2, ISOD)), xd], 'rspcdva', '( %s -> ( ( x =/= P /\\ ( abs ` ( x - P ) ) < r ) -> ( F ` x ) =/= 0 ) )' % C2)], 'mpd', '( %s -> ( F ` x ) =/= 0 )' % C2)
    f2 = w.s([fxne, fx0], 'pm2.21ddne', '( %s -> F. )' % C2)
    f1 = w.s([pt, f2], 'rexlimddv', '( %s -> F. )' % C1)
    f0 = w.s([iso, f1], 'rexlimddv', '( %s -> F. )' % C0)
    nord = w.s([w.s([w.s([w.s([w.s([f0], 'ex', '( ( %s /\\ d e. %s ) -> ( %s -> F. ) )' % (B0, TOP, ORDB('d', 'g', 'n')))], 'exlimdv', '( ( %s /\\ d e. %s ) -> ( E. g %s -> F. ) )' % (B0, TOP, ORDB('d', 'g', 'n')))], 'rexlimdva',
                          '( %s -> ( %s -> F. ) )' % (B0, ORD('n')))], 'imp', '( ( %s /\\ %s ) -> F. )' % (B0, ORD('n')))], 'inegd', '( %s -> -. %s )' % (B0, ORD('n')))
    emp = w.s([w.s([nord], 'ralrimiva', '( %s -> A. n e. NN0 -. %s )' % (A0, ORD('n'))), w.s([], 'rabeq0', '( %s = (/) <-> A. n e. NN0 -. %s )' % (ORDSET(), ORD('n')))], 'sylibr', '( %s -> %s = (/) )' % (A0, ORDSET()))
    inf = w.s([w.s([emp], 'infeq1d', '( %s -> %s = inf ( (/) , RR* , < ) )' % (A0, INF())), closed(w, A0, 'xrinf0', 'inf ( (/) , RR* , < ) = +oo')], 'eqtrd', '( %s -> %s = +oo )' % (A0, INF()))
    w.qed([val, inf], 'eqtrd', '( %s -> ( F holord P ) = +oo )' % A0)
    run1(w)
