"""Sortie TP: the geometric sum of the Newton weights (tpgeo) and the closing inequality (tpfin)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tplib import *
import mvlib

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def req(w, A, l, r, c):
    return mvlib.ringeq(w, A, l, r, c)


Q = '( 8 / D )'
GT = '( ( 2 ^ i ) x. ( ( 4 / D ) ^ ( i + 1 ) ) )'
GS = 'sum_ i e. ( 0 ..^ N ) %s' % GT
S['tpgeo'] = ('( ( D e. RR+ /\\ D <_ 1 /\\ N e. NN ) -> %s <_ ( ( ( 4 / D ) x. ( 8 / 7 ) ) x. ( %s ^ ( N - 1 ) ) ) )' % (GS, Q))
K = '( N - 1 )'; M1 = '( M + 1 )'
DEX = '( ( N - 1 ) / ( M + N ) )'
X1 = '( ( 1 / ( 1 - D ) ) ^ %s )' % M1
S['tpfin'] = ('( ( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ D = %s ) -> ( ( ( 4 x. D ) x. ( %s x. %s ) ) x. %s ) < _pi )'
              % (DEX, X1, GS, CN()))


def gen_geo():
    w = W('tpgeo', 'The Newton weights of the interpolation: ` sum_ ( i < N ) 2 ^ i ( 4 / D ) ^ ( i + 1 ) <_ ( 4 / D ) ( 8 / 7 ) ( 8 / D ) ^ ( N - 1 ) ` '
               'for ` 0 < D <_ 1 ` (the geometric sum inside Lean ` exists_window_interpolant ` ).')
    A = '( D e. RR+ /\\ D <_ 1 /\\ N e. NN )'
    s = lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)
    dp = s([], 'simp1', 'D e. RR+'); d1 = s([], 'simp2', 'D <_ 1'); nn = s([], 'simp3', 'N e. NN')
    c = Closure(w, A, {'D': ('RR+', dp), 'N': ('NN', nn)})
    one = c.mem('1', 'RR+')
    l8 = ap(w, A, 'lediv2ad', '( 8 / 1 ) <_ ( 8 / D )', c, facts=[d1])
    q8 = s([ap(w, A, 'div1d', '( 8 / 1 ) = 8', c), l8], 'eqbrtrrd', '8 <_ %s' % Q)
    c.atom(Q)
    c.have(Q, 'RR+', c.mem(Q, 'RR+'))
    # term identity
    Ai = '( %s /\\ i e. ( 0 ..^ N ) )' % A
    si = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ai, f))
    ci = Closure(w, Ai, {'D': ('RR+', w.s([dp], 'adantr', '( %s -> D e. RR+ )' % Ai)),
                         'i': ('NN0', w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai), w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Ai))})
    Z = '( 4 / D )'; X = '( 2 ^ i )'; Y = '( %s ^ i )' % Z
    t1 = ap(w, Ai, 'expp1d', '( %s ^ ( i + 1 ) ) = ( %s x. %s )' % (Z, Y, Z), ci)
    t1b = si([t1], 'oveq2d', '%s = ( %s x. ( %s x. %s ) )' % (GT, X, Y, Z))
    for a in (X, Y, Z):
        ci.atom(a)
    t1c = req(w, Ai, '( %s x. ( %s x. %s ) )' % (X, Y, Z), '( ( %s x. %s ) x. %s )' % (X, Y, Z), ci)
    t2 = ap(w, Ai, 'mulexpd', '( ( 2 x. %s ) ^ i ) = ( %s x. %s )' % (Z, X, Y), ci)
    t3a = ap(w, Ai, 'divassd', '( ( 2 x. 4 ) / D ) = ( 2 x. %s )' % Z, ci)
    t3b = si([req(w, Ai, '( 2 x. 4 )', '8', ci)], 'oveq1d', '( ( 2 x. 4 ) / D ) = %s' % Q)
    t3 = si([t3a, t3b], 'eqtr3d', '( 2 x. %s ) = %s' % (Z, Q))
    t4 = si([t3], 'oveq1d', '( ( 2 x. %s ) ^ i ) = ( %s ^ i )' % (Z, Q))
    t5 = si([t2, t4], 'eqtr3d', '( %s x. %s ) = ( %s ^ i )' % (X, Y, Q))
    t6 = si([t5], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( ( %s ^ i ) x. %s )' % (X, Y, Z, Q, Z))
    ci.atom('( %s ^ i )' % Q)
    t7 = req(w, Ai, '( ( %s ^ i ) x. %s )' % (Q, Z), '( %s x. ( %s ^ i ) )' % (Z, Q), ci)
    term = si([t1b, t1c, t6], '3eqtrd', '%s = ( ( %s ^ i ) x. %s )' % (GT, Q, Z))
    term = si([term, t7], 'eqtrd', '%s = ( %s x. ( %s ^ i ) )' % (GT, Z, Q))
    se = s([term], 'sumeq2dv', '%s = sum_ i e. ( 0 ..^ N ) ( %s x. ( %s ^ i ) )' % (GS, Z, Q))
    G = 'sum_ i e. ( 0 ..^ N ) ( %s ^ i )' % Q
    fm = ap(w, A, 'fsummulc2', '( %s x. %s ) = sum_ i e. ( 0 ..^ N ) ( %s x. ( %s ^ i ) )' % (Z, G, Z, Q), c,
            facts=[s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin'),
                   ci.mem('( %s ^ i )' % Q, 'CC')])
    gsum = s([se, fm], 'eqtr4d', '%s = ( %s x. %s )' % (GS, Z, G))
    # geometric sum
    n0 = c.mem('N', 'NN0')
    nuz = s([n0, w.inst('elnn0uz')], 'sylib', 'N e. ( ZZ>= ` 0 )')
    q1 = lin.linarith(w, A, [q8], '1 < %s' % Q, closure=c)
    qn1 = ap(w, A, 'gtned', '%s =/= 1' % Q, c, facts=[q1])
    z0 = s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '0 e. NN0')
    g1 = ap(w, A, 'geoserg', '%s = ( ( ( %s ^ 0 ) - ( %s ^ N ) ) / ( 1 - %s ) )' % (G, Q, Q, Q), c, facts=[qn1, z0, nuz])
    QN = '( %s ^ N )' % Q
    g2 = ap(w, A, 'div2subd', '( ( ( %s ^ 0 ) - %s ) / ( 1 - %s ) ) = ( ( %s - ( %s ^ 0 ) ) / ( %s - 1 ) )' % (Q, QN, Q, QN, Q, Q), c,
            facts=[ap(w, A, 'necomd', '1 =/= %s' % Q, c, facts=[qn1])])
    e0 = apc(w, A, 'exp0', '( %s ^ 0 ) = 1' % Q, c)
    g3 = s([e0], 'oveq2d', '( %s - ( %s ^ 0 ) ) = ( %s - 1 )' % (QN, Q, QN))
    g3 = s([g3], 'oveq1d', '( ( %s - ( %s ^ 0 ) ) / ( %s - 1 ) ) = ( ( %s - 1 ) / ( %s - 1 ) )' % (QN, Q, Q, QN, Q))
    GG = '( ( %s - 1 ) / ( %s - 1 ) )' % (QN, Q)
    geq = s([g1, g2, g3], '3eqtrd', '%s = %s' % (G, GG))
    P = '( %s ^ ( N - 1 ) )' % Q
    np1 = ap(w, A, 'npcand', '( ( N - 1 ) + 1 ) = N', c)
    n1 = s([nn, w.inst('nnm1nn0')], 'syl', '( N - 1 ) e. NN0')
    c.have('( N - 1 )', 'NN0', n1)
    p1 = ap(w, A, 'expp1d', '( %s ^ ( ( N - 1 ) + 1 ) ) = ( %s x. %s )' % (Q, P, Q), c)
    p2 = s([np1], 'oveq2d', '( %s ^ ( ( N - 1 ) + 1 ) ) = %s' % (Q, QN))
    qnp = s([p2, p1], 'eqtr3d', '%s = ( %s x. %s )' % (QN, P, Q))
    c.atom(P); c.atom(QN)
    pg = c.ge0(P)
    q8g = lin.linarith(w, A, [q8], '0 <_ ( %s - 8 )' % Q, closure=c)
    pr = ap(w, A, 'mulge0d', '0 <_ ( %s x. ( %s - 8 ) )' % (P, Q), c, facts=[pg, q8g])
    B = '( ( 8 / 7 ) x. %s )' % P
    inq = lin.linarith(w, A, [pr, qnp], '( %s - 1 ) <_ ( %s x. ( %s - 1 ) )' % (QN, B, Q), closure=c, products=True)
    qm1 = lin.linarith(w, A, [q1], '0 < ( %s - 1 )' % Q, closure=c)
    c.have('( %s - 1 )' % Q, 'gt0', qm1)
    bi = ap(w, A, 'ledivmul2d', '( %s <_ %s <-> ( %s - 1 ) <_ ( %s x. ( %s - 1 ) ) )' % (GG, B, QN, B, Q), c)
    gle = s([inq, bi], 'mpbird', '%s <_ %s' % (GG, B))
    gle = s([geq, gle], 'eqbrtrd', '%s <_ %s' % (G, B))
    zg = c.ge0(Z)
    m1 = ap(w, A, 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (Z, G, Z, B), c, facts=[gle])
    c.atom(Z)
    m2 = req(w, A, '( %s x. %s )' % (Z, B), '( ( %s x. ( 8 / 7 ) ) x. %s )' % (Z, P), c)
    m3 = s([m1, m2], 'breqtrd', '( %s x. %s ) <_ ( ( %s x. ( 8 / 7 ) ) x. %s )' % (Z, G, Z, P))
    w.qed([gsum, m3], 'eqbrtrd', S['tpgeo'])
    return run(w)


def gen_fin():
    w = W('tpfin', 'The closing inequality of Turan\'s second main theorem on the square contour: '
               '` 4 D ( 1 / ( 1 - D ) ) ^ ( M + 1 ) ( sum_ i 2 ^ i ( 4 / D ) ^ ( i + 1 ) ) ( N / ( 8 e ( M + N ) ) ) ^ N < pi ` .')
    A = '( ( N e. NN /\\ 2 <_ N /\\ M e. NN0 ) /\\ D = %s )' % DEX
    s = lambda h, r, f, name=None: w.s(h, r, '( %s -> %s )' % (A, f), name=name)
    h3 = s([], 'simpl', '( N e. NN /\\ 2 <_ N /\\ M e. NN0 )')
    nn = s([h3], 'simp1d', 'N e. NN'); n2 = s([h3], 'simp2d', '2 <_ N'); mm = s([h3], 'simp3d', 'M e. NN0')
    dd = s([], 'simpr', 'D = %s' % DEX)
    c = Closure(w, A, {'N': ('NN', nn), 'M': ('NN0', mm)})
    kp = lin.linarith(w, A, [n2], '0 < ( N - 1 )', closure=c)
    c.have('( N - 1 )', 'gt0', kp)
    dx = c.mem(DEX, 'RR+')
    drp = s([dd, dx], 'eqeltrd', 'D e. RR+')
    c.have('D', 'RR+', drp)
    dle = ap(w, A, 'ledivmul2d', '( %s <_ 1 <-> ( N - 1 ) <_ ( 1 x. ( M + N ) ) )' % DEX, c)
    kle = lin.linarith(w, A, [c.ge0('M')], '( N - 1 ) <_ ( 1 x. ( M + N ) )', closure=c)
    dle = s([kle, dle], 'mpbird', '%s <_ 1' % DEX)
    dle = s([dd, dle], 'eqbrtrd', 'D <_ 1')
    geo = apc(w, A, 'tpgeo', S['tpgeo'].split(' -> ', 1)[1][:-2], c, facts=[drp, dle, nn])
    V = '( %s ^ ( N - 1 ) )' % Q
    T = '( ( %s x. %s ) x. %s )' % (X1, V, CN())
    # tpend's antecedent is exactly A
    end = w.s([], 'tpend', '( %s -> %s <_ ( 1 / 8 ) )' % (A, T))
    Gb = '( ( ( 4 / D ) x. ( 8 / 7 ) ) x. %s )' % V
    # 1 - D > 0
    # positivity of 1 - D: D < 1 because N - 1 < M + N
    klt = lin.linarith(w, A, [c.ge0('M')], '( N - 1 ) < ( 1 x. ( M + N ) )', closure=c)
    dlt = ap(w, A, 'ltdivmul2d', '( %s < 1 <-> ( N - 1 ) < ( 1 x. ( M + N ) ) )' % DEX, c)
    dlt = s([klt, dlt], 'mpbird', '%s < 1' % DEX)
    dlt = s([dd, dlt], 'eqbrtrd', 'D < 1')
    omd = lin.linarith(w, A, [dlt], '0 < ( 1 - D )', closure=c)
    c.have('( 1 - D )', 'gt0', omd)
    for a in (X1, V, CN(), GS, '( 4 / D )'):
        c.atom(a)
    x1g = c.ge0(X1); cng = c.ge0(CN()); dg4 = c.ge0('( 4 x. D )')
    m1 = ap(w, A, 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (X1, GS, X1, Gb), c, facts=[geo])
    m2 = ap(w, A, 'lemul2ad', '( ( 4 x. D ) x. ( %s x. %s ) ) <_ ( ( 4 x. D ) x. ( %s x. %s ) )' % (X1, GS, X1, Gb), c, facts=[m1])
    L = '( ( ( 4 x. D ) x. ( %s x. %s ) ) x. %s )' % (X1, GS, CN())
    R = '( ( ( 4 x. D ) x. ( %s x. %s ) ) x. %s )' % (X1, Gb, CN())
    m3 = ap(w, A, 'lemul1ad', '%s <_ %s' % (L, R), c, facts=[m2])
    Z = '( 4 / D )'
    r1 = mvlib.ringeq(w, A, R, '( ( D x. %s ) x. ( ( ; 3 2 / 7 ) x. %s ) )' % (Z, T), c)
    r2 = ap(w, A, 'divcan2d', '( D x. %s ) = 4' % Z, c)
    r3 = s([r2], 'oveq1d', '( ( D x. %s ) x. ( ( ; 3 2 / 7 ) x. %s ) ) = ( 4 x. ( ( ; 3 2 / 7 ) x. %s ) )' % (Z, T, T))
    c.atom(T)
    r4 = mvlib.ringeq(w, A, '( 4 x. ( ( ; 3 2 / 7 ) x. %s ) )' % T, '( ( ; ; 1 2 8 / 7 ) x. %s )' % T, c)
    req_ = s([r1, r3, r4], '3eqtrd', '%s = ( ( ; ; 1 2 8 / 7 ) x. %s )' % (R, T))
    m4 = s([m3, req_], 'breqtrd', '%s <_ ( ( ; ; 1 2 8 / 7 ) x. %s )' % (L, T))
    pi3 = s([w.s([], 'pigt3', '3 < _pi')], 'a1i', '3 < _pi')
    c.have('_pi', 'RR', s([w.s([], 'pire', '_pi e. RR')], 'a1i', '_pi e. RR'))
    lin.linarith(w, A, [m4, end, pi3], '%s < _pi' % L, closure=c, name='qed')
    return run(w)


if __name__ == '__main__':
    gen_geo()
    gen_fin()
