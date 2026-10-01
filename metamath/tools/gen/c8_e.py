"""Sortie C8, section 2: the grid size (hlogn)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *


class Chain:
    """a tower of antecedents L0 -> L1 -> ... with ( Lk -> Li ) steps"""
    def __init__(self, w, levels):
        self.w = w; self.levels = levels
        self.imp = {}
        k = len(levels) - 1
        self.k = k
        cur = None
        for i in range(k - 1, -1, -1):
            if cur is None:
                cur = w.s([], 'simpl', '( %s -> %s )' % (levels[k], levels[i]))
            else:
                cur = w.s([cur, w.inst('simpl')], 'syl', '( %s -> %s )' % (levels[k], levels[i]))
            self.imp[i] = cur

    def lift(self, f, i, phi):
        return self.w.s([self.imp[i], f], 'syl', '( %s -> %s )' % (self.levels[self.k], phi))


def gen_hlogn():
    w = W('hlogn', 'The grid: for ` N ` large every quotient of consecutive values of ` F ` along the segment from the corner ` A ` to a point of the rectangle lies in the slit plane.')
    A0 = '( %s /\\ %s )' % (ABGEO, NZ0)
    abg = w.s([], 'simpl', '( %s -> %s )' % (A0, ABGEO))
    nz = w.s([], 'simpr', '( %s -> %s )' % (A0, NZ0))
    d = abgeoctx(w, A0, abg)
    ksd = w.s([d['hol'], d['ab'], d['nest'], w.inst('holnss')], 'syl3anc', '( %s -> ( A crect B ) C_ D )' % A0)
    LB = 'A. c e. ( A crect B ) m <_ ( abs ` ( F ` c ) )'
    LIP = 'A. a e. ( A crect B ) A. b e. ( A crect B ) ( abs ` ( ( F ` a ) - ( F ` b ) ) ) <_ ( l x. ( abs ` ( a - b ) ) )'
    lbd = w.s([d['ab'], w.s([d['fcn'], ksd], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )' % A0), nz, w.inst('crectlbd')], 'syl3anc',
              '( %s -> E. m e. RR+ %s )' % (A0, LB))
    lip = w.s([abg, w.inst('hollip')], 'syl', '( %s -> E. l e. RR+ %s )' % (A0, LIP))
    X = '( ( l x. %s ) / m )' % PER
    CONC = 'E. n e. NN %s' % SLITP('n')
    L1 = '( ( %s /\\ m e. RR+ ) /\\ %s )' % (A0, LB)
    L2 = '( ( %s /\\ l e. RR+ ) /\\ %s )' % (L1, LIP)
    L3 = '( %s /\\ n e. NN )' % L2
    L4 = '( %s /\\ %s < n )' % (L3, X)
    L5 = '( %s /\\ ( p e. ( A crect B ) /\\ j e. ( 0 ..^ n ) ) )' % L4
    A0m = '( %s /\\ m e. RR+ )' % A0
    L1l = '( %s /\\ l e. RR+ )' % L1
    ch = Chain(w, [A0, A0m, L1, L1l, L2, L3, L4, L5])
    # level-5 facts
    ab = ch.lift(d['ab'], 0, AB)
    geo = ch.lift(d['geo'], 0, GEO)
    abgeo = w.s([ab, geo], 'jca', '( %s -> ( %s /\\ %s ) )' % (L5, AB, GEO))
    ff = ch.lift(d['ff'], 0, 'F : D --> CC')
    kd = ch.lift(ksd, 0, '( A crect B ) C_ D')
    ac = ch.lift(d['ac'], 0, 'A e. CC')
    mrp = ch.lift(w.s([], 'simplr', '( %s -> m e. RR+ )' % L1), 2, 'm e. RR+')
    lb = ch.lift(w.s([], 'simpr', '( %s -> %s )' % (L1, LB)), 2, LB)
    lrp = ch.lift(w.s([], 'simplr', '( %s -> l e. RR+ )' % L2), 4, 'l e. RR+')
    lipc = ch.lift(w.s([], 'simpr', '( %s -> %s )' % (L2, LIP)), 4, LIP)
    nn = ch.lift(w.s([], 'simpr', '( %s -> n e. NN )' % L3), 5, 'n e. NN')
    xlt = ch.lift(w.s([], 'simpr', '( %s -> %s < n )' % (L4, X)), 6, '%s < n' % X)
    pin = w.s([], 'simprl', '( %s -> p e. ( A crect B ) )' % L5)
    jin = w.s([], 'simprr', '( %s -> j e. ( 0 ..^ n ) )' % L5)
    jfz = w.s([jin, w.s([], 'elfzo0', '( j e. ( 0 ..^ n ) <-> ( j e. NN0 /\\ n e. NN /\\ j < n ) )')], 'sylib', '( %s -> ( j e. NN0 /\\ n e. NN /\\ j < n ) )' % L5)
    jn0 = w.s([jfz, w.inst('simp1')], 'syl', '( %s -> j e. NN0 )' % L5)
    jltn = w.s([jfz, w.inst('simp3')], 'syl', '( %s -> j < n )' % L5)
    jr = w.s([jn0], 'nn0red', '( %s -> j e. RR )' % L5)
    j0 = w.s([jn0], 'nn0ge0d', '( %s -> 0 <_ j )' % L5)
    nrp = w.s([nn], 'nnrpd', '( %s -> n e. RR+ )' % L5)
    nr = w.s([nn], 'nnred', '( %s -> n e. RR )' % L5)
    T0 = '( j / n )'; T1 = '( ( j + 1 ) / n )'
    t0r = w.s([jr, nrp], 'rerpdivcld', '( %s -> %s e. RR )' % (L5, T0))
    t00 = w.s([jr, nrp, j0], 'divge0d', '( %s -> 0 <_ %s )' % (L5, T0))
    t01 = w.s([w.s([jr, nr, jltn], 'ltled', '( %s -> j <_ n )' % L5), w.s([jr, nrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> j <_ n ) )' % (L5, T0))],
              'mpbird', '( %s -> %s <_ 1 )' % (L5, T0))
    t0in = w.s([w.s([t0r, t00, t01], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (L5, T0, T0, T0)),
                w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (T0, T0, T0, T0))], 'sylibr', '( %s -> %s e. ( 0 [,] 1 ) )' % (L5, T0))
    j1r = w.s([jr, w.s([], '1red', '( %s -> 1 e. RR )' % L5)], 'readdcld', '( %s -> ( j + 1 ) e. RR )' % L5)
    j10 = w.s([jr, w.s([], '1red', '( %s -> 1 e. RR )' % L5), j0, w.s([w.s([], '0le1', '0 <_ 1')], 'a1i', '( %s -> 0 <_ 1 )' % L5)], 'addge0d', '( %s -> 0 <_ ( j + 1 ) )' % L5)
    t1r = w.s([j1r, nrp], 'rerpdivcld', '( %s -> %s e. RR )' % (L5, T1))
    t10 = w.s([j1r, nrp, j10], 'divge0d', '( %s -> 0 <_ %s )' % (L5, T1))
    j1le = w.s([jltn, w.s([w.s([jn0], 'nn0zd', '( %s -> j e. ZZ )' % L5), w.s([nn], 'nnzd', '( %s -> n e. ZZ )' % L5), w.inst('zltp1le')], 'syl2anc',
                          '( %s -> ( j < n <-> ( j + 1 ) <_ n ) )' % L5)], 'mpbid', '( %s -> ( j + 1 ) <_ n )' % L5)
    t11 = w.s([j1le, w.s([j1r, nrp, w.inst('divle1le')], 'syl2anc', '( %s -> ( %s <_ 1 <-> ( j + 1 ) <_ n ) )' % (L5, T1))], 'mpbird', '( %s -> %s <_ 1 )' % (L5, T1))
    t1in = w.s([w.s([t1r, t10, t11], '3jca', '( %s -> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (L5, T1, T1, T1)),
                w.s([], 'elicc01', '( %s e. ( 0 [,] 1 ) <-> ( %s e. RR /\\ 0 <_ %s /\\ %s <_ 1 ) )' % (T1, T1, T1, T1))], 'sylibr', '( %s -> %s e. ( 0 [,] 1 ) )' % (L5, T1))
    PA = AFF(T1, 'p'); PB = AFF(T0, 'p')
    pain = w.s([abgeo, w.s([pin, t1in], 'jca', '( %s -> ( p e. ( A crect B ) /\\ %s e. ( 0 [,] 1 ) ) )' % (L5, T1)), w.inst('crectaff')], 'syl2anc',
               '( %s -> %s e. ( A crect B ) )' % (L5, PA))
    pbin = w.s([abgeo, w.s([pin, t0in], 'jca', '( %s -> ( p e. ( A crect B ) /\\ %s e. ( 0 [,] 1 ) ) )' % (L5, T0)), w.inst('crectaff')], 'syl2anc',
               '( %s -> %s e. ( A crect B ) )' % (L5, PB))
    FPA = '( F ` %s )' % PA; FPB = '( F ` %s )' % PB
    fpa = w.s([ff, w.s([kd, pain], 'sseldd', '( %s -> %s e. D )' % (L5, PA))], 'ffvelcdmd', '( %s -> %s e. CC )' % (L5, FPA))
    fpb = w.s([ff, w.s([kd, pbin], 'sseldd', '( %s -> %s e. D )' % (L5, PB))], 'ffvelcdmd', '( %s -> %s e. CC )' % (L5, FPB))
    # the Lipschitz bound at PA, PB
    s1 = w.s([w.s([w.s([w.s([], 'fveq2', '( a = %s -> ( F ` a ) = %s )' % (PA, FPA))], 'oveq1d', '( a = %s -> ( ( F ` a ) - ( F ` b ) ) = ( %s - ( F ` b ) ) )' % (PA, FPA))],
                  'fveq2d', '( a = %s -> ( abs ` ( ( F ` a ) - ( F ` b ) ) ) = ( abs ` ( %s - ( F ` b ) ) ) )' % (PA, FPA)),
              w.s([w.s([w.s([], 'oveq1', '( a = %s -> ( a - b ) = ( %s - b ) )' % (PA, PA))], 'fveq2d', '( a = %s -> ( abs ` ( a - b ) ) = ( abs ` ( %s - b ) ) )' % (PA, PA))],
                  'oveq2d', '( a = %s -> ( l x. ( abs ` ( a - b ) ) ) = ( l x. ( abs ` ( %s - b ) ) ) )' % (PA, PA))], 'breq12d',
             '( a = %s -> ( ( abs ` ( ( F ` a ) - ( F ` b ) ) ) <_ ( l x. ( abs ` ( a - b ) ) ) <-> ( abs ` ( %s - ( F ` b ) ) ) <_ ( l x. ( abs ` ( %s - b ) ) ) ) )' % (PA, FPA, PA))
    s2 = w.s([w.s([w.s([w.s([], 'fveq2', '( b = %s -> ( F ` b ) = %s )' % (PB, FPB))], 'oveq2d', '( b = %s -> ( %s - ( F ` b ) ) = ( %s - %s ) )' % (PB, FPA, FPA, FPB))],
                  'fveq2d', '( b = %s -> ( abs ` ( %s - ( F ` b ) ) ) = ( abs ` ( %s - %s ) ) )' % (PB, FPA, FPA, FPB)),
              w.s([w.s([w.s([], 'oveq2', '( b = %s -> ( %s - b ) = ( %s - %s ) )' % (PB, PA, PA, PB))], 'fveq2d', '( b = %s -> ( abs ` ( %s - b ) ) = ( abs ` ( %s - %s ) ) )' % (PB, PA, PA, PB))],
                  'oveq2d', '( b = %s -> ( l x. ( abs ` ( %s - b ) ) ) = ( l x. ( abs ` ( %s - %s ) ) ) )' % (PB, PA, PA, PB))], 'breq12d',
             '( b = %s -> ( ( abs ` ( %s - ( F ` b ) ) ) <_ ( l x. ( abs ` ( %s - b ) ) ) <-> ( abs ` ( %s - %s ) ) <_ ( l x. ( abs ` ( %s - %s ) ) ) ) )' % (PB, FPA, PA, FPA, FPB, PA, PB))
    DF = '( abs ` ( %s - %s ) )' % (FPA, FPB)
    DP = '( abs ` ( %s - %s ) )' % (PA, PB)
    lipab = w.s([w.s([pain, pbin], 'jca', '( %s -> ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) )' % (L5, PA, PB)), lipc,
                 w.s([s1, s2], 'rspc2va', '( ( ( %s e. ( A crect B ) /\\ %s e. ( A crect B ) ) /\\ %s ) -> %s <_ ( l x. %s ) )' % (PA, PB, LIP, DF, DP))],
                'syl2anc', '( %s -> %s <_ ( l x. %s ) )' % (L5, DF, DP))
    # PA - PB = ( p - A ) / n
    XA = '( p - A )'
    crss = ch.lift(d['crss'], 0, '( A crect B ) C_ CC')
    pc = w.s([crss, pin], 'sseldd', '( %s -> p e. CC )' % L5)
    xac = w.s([pc, ac], 'subcld', '( %s -> %s e. CC )' % (L5, XA))
    t1c = w.s([t1r], 'recnd', '( %s -> %s e. CC )' % (L5, T1)); t0c = w.s([t0r], 'recnd', '( %s -> %s e. CC )' % (L5, T0))
    a1 = w.s([ac, w.s([t1c, xac], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (L5, T1, XA)), w.s([t0c, xac], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (L5, T0, XA)),
              w.inst('pnpcan')], 'syl3anc', '( %s -> ( %s - %s ) = ( ( %s x. %s ) - ( %s x. %s ) ) )' % (L5, PA, PB, T1, XA, T0, XA))
    a2 = w.s([w.s([t1c, t0c, xac], 'subdird', '( %s -> ( ( %s - %s ) x. %s ) = ( ( %s x. %s ) - ( %s x. %s ) ) )' % (L5, T1, T0, XA, T1, XA, T0, XA))], 'eqcomd',
             '( %s -> ( ( %s x. %s ) - ( %s x. %s ) ) = ( ( %s - %s ) x. %s ) )' % (L5, T1, XA, T0, XA, T1, T0, XA))
    jc = w.s([jr], 'recnd', '( %s -> j e. CC )' % L5)
    nc = w.s([nr], 'recnd', '( %s -> n e. CC )' % L5)
    nne = w.s([nrp], 'rpne0d', '( %s -> n =/= 0 )' % L5)
    j1c = w.s([j1r], 'recnd', '( %s -> ( j + 1 ) e. CC )' % L5)
    a3 = w.s([w.s([j1c, jc, nc, nne], 'divsubdird', '( %s -> ( ( ( j + 1 ) - j ) / n ) = ( %s - %s ) )' % (L5, T1, T0))], 'eqcomd',
             '( %s -> ( %s - %s ) = ( ( ( j + 1 ) - j ) / n ) )' % (L5, T1, T0))
    a4 = w.s([jc, w.s([], '1cnd', '( %s -> 1 e. CC )' % L5), w.inst('pncan2')], 'syl2anc', '( %s -> ( ( j + 1 ) - j ) = 1 )' % L5)
    a5 = w.s([a3, w.s([a4], 'oveq1d', '( %s -> ( ( ( j + 1 ) - j ) / n ) = ( 1 / n ) )' % L5)], 'eqtrd', '( %s -> ( %s - %s ) = ( 1 / n ) )' % (L5, T1, T0))
    a6 = w.s([a5], 'oveq1d', '( %s -> ( ( %s - %s ) x. %s ) = ( ( 1 / n ) x. %s ) )' % (L5, T1, T0, XA, XA))
    a7 = w.s([w.s([xac, nc, nne], 'divrec2d', '( %s -> ( %s / n ) = ( ( 1 / n ) x. %s ) )' % (L5, XA, XA))], 'eqcomd',
             '( %s -> ( ( 1 / n ) x. %s ) = ( %s / n ) )' % (L5, XA, XA))
    dif = w.s([w.s([w.s([a1, a2], 'eqtrd', '( %s -> ( %s - %s ) = ( ( %s - %s ) x. %s ) )' % (L5, PA, PB, T1, T0, XA)), a6], 'eqtrd',
                   '( %s -> ( %s - %s ) = ( ( 1 / n ) x. %s ) )' % (L5, PA, PB, XA)), a7], 'eqtrd', '( %s -> ( %s - %s ) = ( %s / n ) )' % (L5, PA, PB, XA))
    AXA = '( abs ` %s )' % XA
    dab = w.s([w.s([dif], 'fveq2d', '( %s -> %s = ( abs ` ( %s / n ) ) )' % (L5, DP, XA)),
               w.s([w.s([xac, nc, nne], 'absdivd', '( %s -> ( abs ` ( %s / n ) ) = ( %s / ( abs ` n ) ) )' % (L5, XA, AXA)),
                    w.s([w.s([nr, w.s([nrp], 'rpge0d', '( %s -> 0 <_ n )' % L5)], 'absidd', '( %s -> ( abs ` n ) = n )' % L5)], 'oveq2d',
                        '( %s -> ( %s / ( abs ` n ) ) = ( %s / n ) )' % (L5, AXA, AXA))], 'eqtrd', '( %s -> ( abs ` ( %s / n ) ) = ( %s / n ) )' % (L5, XA, AXA))],
              'eqtrd', '( %s -> %s = ( %s / n ) )' % (L5, DP, AXA))
    # the chain of bounds
    per = w.s([ab, pin, w.inst('crectpa')], 'syl2anc', '( %s -> %s <_ %s )' % (L5, AXA, PER))
    axr = w.s([xac], 'abscld', '( %s -> %s e. RR )' % (L5, AXA))
    ar_ = w.s([ac], 'recld', '( %s -> %s e. RR )' % (L5, RA)); bc = ch.lift(d['bc'], 0, 'B e. CC')
    br_ = w.s([bc], 'recld', '( %s -> %s e. RR )' % (L5, RB))
    ai_ = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (L5, IA)); bi_ = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (L5, IB))
    perr = w.s([w.s([br_, ar_], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (L5, RB, RA)),
                w.s([bi_, ai_], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (L5, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (L5, PER))
    b1 = w.s([axr, perr, nrp, per], 'lediv1dd', '( %s -> ( %s / n ) <_ ( %s / n ) )' % (L5, AXA, PER))
    lr = w.s([lrp], 'rpred', '( %s -> l e. RR )' % L5)
    b2 = w.s([w.s([axr, nrp], 'rerpdivcld', '( %s -> ( %s / n ) e. RR )' % (L5, AXA)), w.s([perr, nrp], 'rerpdivcld', '( %s -> ( %s / n ) e. RR )' % (L5, PER)),
              lr, w.s([lrp], 'rpge0d', '( %s -> 0 <_ l )' % L5), b1], 'lemul2ad', '( %s -> ( l x. ( %s / n ) ) <_ ( l x. ( %s / n ) ) )' % (L5, AXA, PER))
    b3 = w.s([w.s([w.s([lr], 'recnd', '( %s -> l e. CC )' % L5), w.s([perr], 'recnd', '( %s -> %s e. CC )' % (L5, PER)), nc, nne], 'divassd',
                  '( %s -> ( ( l x. %s ) / n ) = ( l x. ( %s / n ) ) )' % (L5, PER, PER))], 'eqcomd', '( %s -> ( l x. ( %s / n ) ) = ( ( l x. %s ) / n ) )' % (L5, PER, PER))
    lper = w.s([lr, perr], 'remulcld', '( %s -> ( l x. %s ) e. RR )' % (L5, PER))
    mr = w.s([mrp], 'rpred', '( %s -> m e. RR )' % L5)
    c1 = w.s([xlt, w.s([lper, nr, mrp], 'ltdivmuld', '( %s -> ( %s < n <-> ( l x. %s ) < ( m x. n ) ) )' % (L5, X, PER))], 'mpbid', '( %s -> ( l x. %s ) < ( m x. n ) )' % (L5, PER))
    c2 = w.s([c1, w.s([w.s([mr], 'recnd', '( %s -> m e. CC )' % L5), nc], 'mulcomd', '( %s -> ( m x. n ) = ( n x. m ) )' % L5)], 'breqtrd', '( %s -> ( l x. %s ) < ( n x. m ) )' % (L5, PER))
    c3 = w.s([c2, w.s([lper, mr, nrp], 'ltdivmuld', '( %s -> ( ( ( l x. %s ) / n ) < m <-> ( l x. %s ) < ( n x. m ) ) )' % (L5, PER, PER))], 'mpbird',
             '( %s -> ( ( l x. %s ) / n ) < m )' % (L5, PER))
    c4 = w.s([b3, c3], 'eqbrtrd', '( %s -> ( l x. ( %s / n ) ) < m )' % (L5, PER))
    c5 = w.s([b2, c4], 'lelttrd' if False else 'idi', 'X') if False else None
    lx = w.s([lr, w.s([axr, nrp], 'rerpdivcld', '( %s -> ( %s / n ) e. RR )' % (L5, AXA))], 'remulcld', '( %s -> ( l x. ( %s / n ) ) e. RR )' % (L5, AXA))
    lp = w.s([lr, w.s([perr, nrp], 'rerpdivcld', '( %s -> ( %s / n ) e. RR )' % (L5, PER))], 'remulcld', '( %s -> ( l x. ( %s / n ) ) e. RR )' % (L5, PER))
    c5 = w.s([lx, lp, mr, b2, c4], 'lelttrd', '( %s -> ( l x. ( %s / n ) ) < m )' % (L5, AXA))
    c6 = w.s([lipab, w.s([dab], 'oveq2d', '( %s -> ( l x. %s ) = ( l x. ( %s / n ) ) )' % (L5, DP, AXA))], 'breqtrd', '( %s -> %s <_ ( l x. ( %s / n ) ) )' % (L5, DF, AXA))
    dfr = w.s([w.s([fpa, fpb], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (L5, FPA, FPB))], 'abscld', '( %s -> %s e. RR )' % (L5, DF))
    c7 = w.s([dfr, lx, mr, c6, c5], 'lelttrd', '( %s -> %s < m )' % (L5, DF))
    # the lower bound at PB
    sc = w.s([w.s([w.s([], 'fveq2', '( c = %s -> ( F ` c ) = %s )' % (PB, FPB))], 'fveq2d', '( c = %s -> ( abs ` ( F ` c ) ) = ( abs ` %s ) )' % (PB, FPB))], 'breq2d',
             '( c = %s -> ( m <_ ( abs ` ( F ` c ) ) <-> m <_ ( abs ` %s ) ) )' % (PB, FPB))
    mb = w.s([sc, pbin, lb], 'rspcdva', '( %s -> m <_ ( abs ` %s ) )' % (L5, FPB))
    fin = w.s([w.s([fpa, fpb], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (L5, FPA, FPB)), w.s([mrp, mb, c7], '3jca', '( %s -> ( m e. RR+ /\\ m <_ ( abs ` %s ) /\\ %s < m ) )' % (L5, FPB, DF)),
               w.inst('slitq')], 'syl2anc', '( %s -> %s e. %s )' % (L5, QT(T1, T0, 'p'), SLIT))
    ral = w.s([fin], 'ralrimivva', '( %s -> %s )' % (L4, SLITP('n')))
    rex = w.s([w.s([ral], 'ex', '( %s -> ( %s < n -> %s ) )' % (L3, X, SLITP('n')))], 'reximdva', '( %s -> ( E. n e. NN %s < n -> %s ) )' % (L2, X, CONC))
    ab2 = w.s([w.s([], 'simpll', '( %s -> %s )' % (L2, L1)), w.s([w.s([], 'simpl', '( %s -> %s )' % (L1, A0)) if False else w.s([], 'simpll', '( %s -> %s )' % (L1, A0)), d['ab']], 'syl', '( %s -> %s )' % (L1, AB))], 'syl', '( %s -> %s )' % (L2, AB))
    # X real at level 2
    ac2 = w.s([ab2, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % L2); bc2 = w.s([ab2, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % L2)
    perr2 = w.s([w.s([w.s([bc2], 'recld', '( %s -> %s e. RR )' % (L2, RB)), w.s([ac2], 'recld', '( %s -> %s e. RR )' % (L2, RA))], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (L2, RB, RA)),
                 w.s([w.s([bc2], 'imcld', '( %s -> %s e. RR )' % (L2, IB)), w.s([ac2], 'imcld', '( %s -> %s e. RR )' % (L2, IA))], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (L2, IB, IA))],
                'readdcld', '( %s -> %s e. RR )' % (L2, PER))
    l2r = w.s([w.s([w.s([], 'simplr', '( %s -> l e. RR+ )' % L2)], 'rpred', '( %s -> l e. RR )' % L2), perr2], 'remulcld', '( %s -> ( l x. %s ) e. RR )' % (L2, PER))
    m2rp = w.s([w.s([], 'simpll', '( %s -> %s )' % (L2, L1)), w.s([], 'simplr', '( %s -> m e. RR+ )' % L1)], 'syl', '( %s -> m e. RR+ )' % L2)
    xr2 = w.s([l2r, m2rp], 'rerpdivcld', '( %s -> %s e. RR )' % (L2, X))
    arc = w.s([xr2, w.inst('arch')], 'syl', '( %s -> E. n e. NN %s < n )' % (L2, X))
    c2x = w.s([arc, rex], 'mpd', '( %s -> %s )' % (L2, CONC))
    e1 = w.s([w.s([c2x], 'ex', '( ( %s /\\ l e. RR+ ) -> ( %s -> %s ) )' % (L1, LIP, CONC))], 'rexlimdva', '( %s -> ( E. l e. RR+ %s -> %s ) )' % (L1, LIP, CONC))
    lip1 = w.s([w.s([], 'simpll', '( %s -> %s )' % (L1, A0)), lip], 'syl', '( %s -> E. l e. RR+ %s )' % (L1, LIP))
    c1x = w.s([lip1, e1], 'mpd', '( %s -> %s )' % (L1, CONC))
    e0 = w.s([w.s([c1x], 'ex', '( ( %s /\\ m e. RR+ ) -> ( %s -> %s ) )' % (A0, LB, CONC))], 'rexlimdva', '( %s -> ( E. m e. RR+ %s -> %s ) )' % (A0, LB, CONC))
    w.qed([lbd, e0], 'mpd', '( %s -> %s )' % (A0, CONC))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_hlogn]:
        g()
