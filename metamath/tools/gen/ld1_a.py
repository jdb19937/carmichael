"""Sortie LD1, section 0: the parameter facts (ld1d4 ld1yp ld1jpar ld1nmax) and the numeric clauses
(ld1ntail ld1nblk ld1ntay).  Run: MM_DB=sorties/ld1.mm MM_ENGINE=mmatch python3 tools/gen/ld1_a.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ld1lib import *
from dshlib import STATEMENTS as DSTM
import lin as _L
_L.MAXPOW = 8

only = sys.argv[1:]
want = lambda l: not only or l in only


def fin(w, step=None):
    qedlast(w)
    return go(w)


def ld1d4():
    w = W('ld1d4', 'Lean ` exp_forty_le ` and ` four_le_of_log ` : ` 40 <_ log D ` gives ` e ^ 40 <_ D ` and ` 4 <_ D ` (~ efle , ~ reeflog , ~ efgt1p ).')
    A = HZH; P = parts(w, A); dr, d1, dl = hzh(w, A, P); rp, z = dpos(w, A, dr, d1)
    lr = dst(w, A, [rp], 'relogcld', '( log ` D ) e. RR')
    c = Closure(w, A, {'D': [('RR+', rp), ('gt1', d1)], '( log ` D )': ('RR', lr)})
    efl = ap(w, A, 'efle', [c.mem('; 4 0', 'RR'), lr], '( ; 4 0 <_ ( log ` D ) <-> ( exp ` ; 4 0 ) <_ ( exp ` ( log ` D ) ) )')
    e1 = dst(w, A, [dl, efl], 'mpbid', '( exp ` ; 4 0 ) <_ ( exp ` ( log ` D ) )')
    el = ap(w, A, 'reeflog', [rp], '( exp ` ( log ` D ) ) = D')
    e2 = dst(w, A, [e1, el], 'breqtrd', '( exp ` ; 4 0 ) <_ D')
    g = ap(w, A, 'efgt1p', [c.mem('; 4 0', 'RR+')], '( 1 + ; 4 0 ) < ( exp ` ; 4 0 )')
    f4 = linarith(w, A, [g, e2], '4 <_ D', closure=c)
    J(w, A, e2, f4)
    return fin(w)


def ld1yp():
    w = W('ld1yp', 'Lean ` Ypar_pos ` , ` one_le_Ypar ` , ` le_Ypar ` , ` four_le_Ypar ` : the smoothing length ` Y = D ^ ( 151 / 100 ) ` (~ dshyp , ~ cxplea , ~ ld1d4 ).')
    A = HZH; P = parts(w, A); dr, d1, dl = hzh(w, A, P); rp, z = dpos(w, A, dr, d1)
    hz = J(w, A, dr, d1, dl)
    h2 = J(w, A, dr, d1)
    yp = ap(w, A, 'dshyp', [h2], split_imp(DSTM['dshyp'])[1])
    yrp = dst(w, A, [yp], 'simpld', '%s e. RR+' % YP)
    yr = dst(w, A, [yrp], 'rpred', '%s e. RR' % YP)
    dc = dst(w, A, [dr], 'recnd', 'D e. CC')
    c1 = ap(w, A, 'cxp1', [dc], '( D ^c 1 ) = D')
    one = a1(w, A, '1re', '1 e. RR')
    d1le = dst(w, A, [one, dr, d1], 'ltled', '1 <_ D')
    Y151 = '( ; ; 1 5 1 / ; ; 1 0 0 )'
    r151 = w.s([num.real(w, Y151)], 'a1i', '( %s -> %s e. RR )' % (A, Y151))
    le151 = w.s([num.le_lit(w, '1', Y151)], 'a1i', '( %s -> 1 <_ %s )' % (A, Y151))
    cx = ap(w, A, 'cxplea', [J(w, A, dr, d1le), J(w, A, one, r151), le151], '( D ^c 1 ) <_ %s' % YP)
    dy = dst(w, A, [c1, cx], 'eqbrtrrd', 'D <_ %s' % YP)
    d4 = dst(w, A, [ap(w, A, 'ld1d4', [hz], concl('ld1d4'))], 'simprd', '4 <_ D')
    four = a1(w, A, '4re', '4 e. RR')
    y4 = dst(w, A, [four, dr, yr, d4, dy], 'letrd', '4 <_ %s' % YP)
    J(w, A, yp, J(w, A, dy, y4))
    return fin(w)


def ld1jpar():
    w = W('ld1jpar', 'Lean ` one_le_Jpar ` , ` log_le_Jpar ` , ` Jpar_le ` , ` Jpar_le_two_mul ` : the block count ` J = ceil ( log D ) ` (~ ceilge , ~ ceilm1lt , ~ elnnz ).')
    A = HZH; P = parts(w, A); dr, d1, dl = hzh(w, A, P); rp, z = dpos(w, A, dr, d1)
    lr = dst(w, A, [rp], 'relogcld', '( log ` D ) e. RR')
    jz = ap(w, A, 'ceilcl', [lr], '%s e. ZZ' % JPAR)
    jr = dst(w, A, [jz], 'zred', '%s e. RR' % JPAR)
    c = Closure(w, A, {'D': [('RR+', rp), ('gt1', d1)], '( log ` D )': ('RR', lr), JPAR: ('RR', jr)})
    ge = ap(w, A, 'ceilge', [lr], '( log ` D ) <_ %s' % JPAR)
    m1 = ap(w, A, 'ceilm1lt', [lr], '( %s - 1 ) < ( log ` D )' % JPAR)
    le1 = linarith(w, A, [m1], '%s <_ ( ( log ` D ) + 1 )' % JPAR, closure=c)
    le2 = linarith(w, A, [m1, dl], '%s <_ ( 2 x. ( log ` D ) )' % JPAR, closure=c)
    g3 = linarith(w, A, [ge, dl], '3 <_ %s' % JPAR, closure=c)
    g0 = linarith(w, A, [ge, dl], '0 < %s' % JPAR, closure=c)
    jn = dst(w, A, [J(w, A, jz, g0), a1(w, A, 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (JPAR, JPAR, JPAR))], 'mpbird', '%s e. NN' % JPAR)
    J(w, A, J(w, A, jn, g3), J(w, A, ge, le1, le2))
    return fin(w)


def ld1nmax():
    w = W('ld1nmax', 'Lean ` le_Nmax ` and ` Nmax_le ` : the truncation length ` Nmax = ceil ( 8 Y log D ) ` (~ ceilge , ~ ceilm1lt , ~ ld1yp ).')
    A = HZH; P = parts(w, A); dr, d1, dl = hzh(w, A, P); rp, z = dpos(w, A, dr, d1)
    hz = J(w, A, dr, d1, dl)
    lr = dst(w, A, [rp], 'relogcld', '( log ` D ) e. RR')
    yp = ap(w, A, 'ld1yp', [hz], concl('ld1yp'))
    yrp = dst(w, A, [dst(w, A, [yp], 'simpld', '( %s e. RR+ /\\ 1 < %s )' % (YP, YP))], 'simpld', '%s e. RR+' % YP)
    c = Closure(w, A, {'D': [('RR+', rp), ('gt1', d1)], '( log ` D )': ('RR', lr), YP: ('RR+', yrp)})
    lg0 = linarith(w, A, [dl], '0 < ( log ` D )', closure=c)
    c.leaf('( log ` D )', 'gt0', lg0)
    Wt = '( ( 8 x. %s ) x. ( log ` D ) )' % YP
    wr = c.mem(Wt, 'RR'); w0 = c.gt0(Wt)
    nz = ap(w, A, 'ceilcl', [wr], '%s e. ZZ' % NMAX)
    nr = dst(w, A, [nz], 'zred', '%s e. RR' % NMAX)
    c.leaf(NMAX, 'RR', nr)
    ge = ap(w, A, 'ceilge', [wr], '%s <_ %s' % (Wt, NMAX))
    m1 = ap(w, A, 'ceilm1lt', [wr], '( %s - 1 ) < %s' % (NMAX, Wt))
    le = linarith(w, A, [m1], '%s <_ ( %s + 1 )' % (NMAX, Wt), closure=c)
    g0 = linarith(w, A, [w0, ge], '0 < %s' % NMAX, closure=c)
    nn = dst(w, A, [J(w, A, nz, g0), a1(w, A, 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (NMAX, NMAX, NMAX))], 'mpbird', '%s e. NN' % NMAX)
    J(w, A, nn, ge, le)
    return fin(w)


def numante(w):
    A = '( X e. RR /\\ ; 4 0 <_ X )'
    P = parts(w, A)
    xr = P['X e. RR']; x40 = P['; 4 0 <_ X']
    c = Closure(w, A, {'X': ('RR', xr)})
    return A, xr, x40, c


def ld1ntail():
    w = W('ld1ntail', 'Lean ` numeric_tail ` (256 in place of 128, LD1-HANDOFF section 2 item 7): ` 256 <_ e ^ ( 0.98 x ) ` for ` x >_ 40 ` (~ efge1p2 ).')
    A, xr, x40, c = numante(w)
    B = '( ( ; 4 9 / ; 5 0 ) x. X )'
    br = c.mem(B, 'RR'); b0 = linarith(w, A, [x40], '0 <_ %s' % B, closure=c)
    ef = ap(w, A, 'efge1p2', [J(w, A, br, b0)], '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ ( exp ` %s )' % (B, B, B))
    nlinarith(w, A, [x40, ef], '; ; 2 5 6 <_ ( exp ` %s )' % B, closure=c, name='qed')
    return go(w)


def ld1nblk():
    w = W('ld1nblk', 'Lean ` numeric_blocks ` : ` 9 x <_ e ^ ( 0.1813 x ) ` for ` x >_ 40 ` , from ` e ^ 7.252 = ( e ^ 1.813 ) ^ 4 >_ ( 22 / 5 ) ^ 4 ` (~ efge1p2 , ~ efexp , ~ leexp1a , ~ bvefge1p ).')
    A, xr, x40, c = numante(w)
    cB = '( ; ; ; 1 8 1 3 / ; ; ; ; 1 0 0 0 0 )'; B = '( %s x. X )' % cB
    K = '( ; ; ; 1 8 1 3 / ; ; ; 1 0 0 0 )'; K7 = '( ; ; ; 1 8 1 3 / ; ; 2 5 0 )'
    E7 = '( exp ` %s )' % K7; EK = '( exp ` %s )' % K
    kr = w.s([num.real(w, K)], 'a1i', '( %s -> %s e. RR )' % (A, K))
    kc = dst(w, A, [kr], 'recnd', '%s e. CC' % K)
    k0 = w.s([num.fact(w, K, 'ge0')], 'a1i', '( %s -> 0 <_ %s )' % (A, K))
    m4 = w.s([num.mul_lits(w, '4', K)], 'a1i', '( %s -> ( 4 x. %s ) = %s )' % (A, K, K7))
    z4 = a1(w, A, '4z', '4 e. ZZ')
    ex4 = ap(w, A, 'efexp', [kc, z4], '( exp ` ( 4 x. %s ) ) = ( %s ^ 4 )' % (K, EK))
    e7 = eqt(w, A, eqc(w, A, dst(w, A, [m4], 'fveq2d', '( exp ` ( 4 x. %s ) ) = %s' % (K, E7))), ex4)   # E7 = EK ^ 4
    ef2 = ap(w, A, 'efge1p2', [J(w, A, kr, k0)], '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ %s' % (K, K, EK))
    sq = dst(w, A, [kc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (K, K, K))
    ef2b = dst(w, A, [dst(w, A, [dst(w, A, [sq], 'oveq1d', '( ( %s ^ 2 ) / 2 ) = ( ( %s x. %s ) / 2 )' % (K, K, K))], 'oveq2d',
                                  '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) = ( ( 1 + %s ) + ( ( %s x. %s ) / 2 ) )' % (K, K, K, K, K)), ef2], 'eqbrtrrd',
               '( ( 1 + %s ) + ( ( %s x. %s ) / 2 ) ) <_ %s' % (K, K, K, EK))
    ekr = c.mem(EK, 'RR')
    h92 = linarith(w, A, [ef2b], '( ; 2 2 / 5 ) <_ %s' % EK, closure=c)
    n4 = a1(w, A, '4nn0', '4 e. NN0')
    r92 = w.s([num.real(w, '( ; 2 2 / 5 )')], 'a1i', '( %s -> ( ; 2 2 / 5 ) e. RR )' % A)
    g92 = w.s([num.fact(w, '( ; 2 2 / 5 )', 'ge0')], 'a1i', '( %s -> 0 <_ ( ; 2 2 / 5 ) )' % A)
    p4 = ap(w, A, 'leexp1a', [J(w, A, r92, ekr, n4), J(w, A, g92, h92)], '( ( ; 2 2 / 5 ) ^ 4 ) <_ ( %s ^ 4 )' % EK)
    v4 = ringeqp(w, A, '( ( ; 2 2 / 5 ) ^ 4 )', '( ; ; ; ; ; 2 3 4 2 5 6 / ; ; 6 2 5 )', c)
    e7ge = dst(w, A, [dst(w, A, [v4, p4], 'eqbrtrrd', '( ; ; ; ; ; 2 3 4 2 5 6 / ; ; 6 2 5 ) <_ ( %s ^ 4 )' % EK), e7], 'eqbrtrrd' if False else 'x', 'x') if False else None
    e7ge = dst(w, A, [e7, dst(w, A, [v4, p4], 'eqbrtrrd', '( ; ; ; ; ; 2 3 4 2 5 6 / ; ; 6 2 5 ) <_ ( %s ^ 4 )' % EK)], 'eqbrtrrd' if False else 'x', 'x') if False else None
    # ( 6561 / 16 ) <_ ( EK ^ 4 ) = E7
    lo = dst(w, A, [v4, p4], 'eqbrtrrd', '( ; ; ; ; ; 2 3 4 2 5 6 / ; ; 6 2 5 ) <_ ( %s ^ 4 )' % EK)
    e7ge = dst(w, A, [lo, e7], 'breqtrrd', '( ; ; ; ; ; 2 3 4 2 5 6 / ; ; 6 2 5 ) <_ %s' % E7)
    # exp B = E7 exp ( B - K7 )
    br = c.mem(B, 'RR'); bc = dst(w, A, [br], 'recnd', '%s e. CC' % B)
    k7c = w.s([num.cc(w, K7)], 'a1i', '( %s -> %s e. CC )' % (A, K7))
    DB = '( %s - %s )' % (B, K7)
    pc = dst(w, A, [k7c, bc], 'pncan3d', '( %s + %s ) = %s' % (K7, DB, B))
    ea = ap(w, A, 'efadd', [k7c, dst(w, A, [bc, k7c], 'subcld', '%s e. CC' % DB)], '( exp ` ( %s + %s ) ) = ( %s x. ( exp ` %s ) )' % (K7, DB, E7, DB))
    sp = eqt(w, A, eqc(w, A, dst(w, A, [pc], 'fveq2d', '( exp ` ( %s + %s ) ) = ( exp ` %s )' % (K7, DB, B))), ea)   # exp B = E7 exp DB
    dbr = c.mem(DB, 'RR'); db0 = linarith(w, A, [x40], '0 <_ %s' % DB, closure=c)
    bm = ap(w, A, 'bvefge1p', [J(w, A, dbr, db0)], '( 1 + %s ) <_ ( exp ` %s )' % (DB, DB))
    e7r = c.mem(E7, 'RR'); e70 = c.ge0(E7)
    ml = dst(w, A, [bm, e7r, e70], 'lemul2ad', '( %s x. ( 1 + %s ) ) <_ ( %s x. ( exp ` %s ) )' % (E7, DB, E7, DB))
    ml2 = dst(w, A, [ml, eqc(w, A, sp)], 'breqtrd', '( %s x. ( 1 + %s ) ) <_ ( exp ` %s )' % (E7, DB, B))
    nlinarith(w, A, [x40, e7ge, ml2], '( 9 x. X ) <_ ( exp ` %s )' % B, closure=c, name='qed')
    return go(w)


def ld1ntay():
    w = W('ld1ntay', 'Lean ` numeric_taylor ` : ` 64 x ^ 2 <_ e ^ ( 0.961 x ) ` for ` x >_ 40 ` , from ` e ^ ( a / 3 ) >_ x ^ 2 / 20 ` cubed (~ efge1p2 , ~ leexp1a , ~ efexp ).')
    A, xr, x40, c = numante(w)
    B = '( ( ; ; 3 1 9 / ; ; ; 1 0 0 0 ) x. X )'; AA = '( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. X )'
    EB = '( exp ` %s )' % B
    br = c.mem(B, 'RR'); b0 = linarith(w, A, [x40], '0 <_ %s' % B, closure=c)
    ef2 = ap(w, A, 'efge1p2', [J(w, A, br, b0)], '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ %s' % (B, B, EB))
    x0 = linarith(w, A, [x40], '0 <_ X', closure=c)
    c.leaf('X', 'ge0', x0)
    X2 = '( X ^ 2 )'; X4 = '( X ^ 4 )'; X6 = '( X ^ 6 )'
    Q = '( %s / ; 2 0 )' % X2
    q1 = nlinarith(w, A, [ef2, x40], '%s <_ %s' % (Q, EB), closure=c)
    ebr = c.mem(EB, 'RR'); qr = c.mem(Q, 'RR'); q0 = c.ge0(Q)
    n3 = a1(w, A, '3nn0', '3 e. NN0')
    p3 = ap(w, A, 'leexp1a', [J(w, A, qr, ebr, n3), J(w, A, q0, q1)], '( %s ^ 3 ) <_ ( %s ^ 3 )' % (Q, EB))
    eq6 = ringeqp(w, A, '( %s ^ 3 )' % Q, '( %s / ; ; ; 8 0 0 0 )' % X6, c)
    q3 = dst(w, A, [eq6, p3], 'eqbrtrrd', '( %s / ; ; ; 8 0 0 0 ) <_ ( %s ^ 3 )' % (X6, EB))
    # X ^ 6 = X ^ 4 x. X ^ 2, 2560000 <_ X ^ 4
    xc = dst(w, A, [xr], 'recnd', 'X e. CC')
    n4 = a1(w, A, '4nn0', '4 e. NN0'); n2 = a1(w, A, '2nn0', '2 e. NN0')
    ea = dst(w, A, [xc, n4, n2], 'expaddd', '( X ^ ( 4 + 2 ) ) = ( %s x. %s )' % (X4, X2))
    s42 = w.s([num.add_nat(w, 4, 2)], 'a1i', '( %s -> ( 4 + 2 ) = 6 )' % A)
    h6 = eqt(w, A, eqc(w, A, dst(w, A, [s42], 'oveq2d', '( X ^ ( 4 + 2 ) ) = %s' % X6)), ea)
    r40 = c.mem('; 4 0', 'RR'); g40 = c.ge0('; 4 0')
    p4 = ap(w, A, 'leexp1a', [J(w, A, r40, xr, n4), J(w, A, g40, x40)], '( ; 4 0 ^ 4 ) <_ %s' % X4)
    v40 = ringeqp(w, A, '( ; 4 0 ^ 4 )', '; ; ; ; ; ; 2 5 6 0 0 0 0', c)
    x4 = dst(w, A, [v40, p4], 'eqbrtrrd', '; ; ; ; ; ; 2 5 6 0 0 0 0 <_ %s' % X4)
    x2r = c.mem(X2, 'RR'); x20 = c.ge0(X2)
    h2 = dst(w, A, [x4, x2r, x20], 'lemul1ad', '( ; ; ; ; ; ; 2 5 6 0 0 0 0 x. %s ) <_ ( %s x. %s )' % (X2, X4, X2))
    for e in (X2, X4, X6, '( %s x. %s )' % (X4, X2), '( %s ^ 3 )' % EB):
        c.atom(e)
    c.leaf(X4, 'RR', c.mem(X4, 'RR')); c.leaf('( %s x. %s )' % (X4, X2), 'RR', c.mem('( %s x. %s )' % (X4, X2), 'RR'))
    c.leaf(X6, 'RR', c.mem(X6, 'RR')); c.leaf('( %s ^ 3 )' % EB, 'RR', c.mem('( %s ^ 3 )' % EB, 'RR'))
    fin1 = linarith(w, A, [h6, h2, q3, x20], '( ; 6 4 x. %s ) <_ ( %s ^ 3 )' % (X2, EB), closure=c)
    # ( exp B ) ^ 3 = exp ( 3 B ) = exp AA
    bc = dst(w, A, [br], 'recnd', '%s e. CC' % B)
    z3 = a1(w, A, '3z', '3 e. ZZ')
    ex3 = ap(w, A, 'efexp', [bc, z3], '( exp ` ( 3 x. %s ) ) = ( %s ^ 3 )' % (B, EB))
    e3 = ringeq(w, A, '( 3 x. %s )' % B, AA, c)
    fe = eqt(w, A, eqc(w, A, dst(w, A, [e3], 'fveq2d', '( exp ` ( 3 x. %s ) ) = ( exp ` %s )' % (B, AA))), ex3)   # exp AA = EB ^ 3
    dst(w, A, [fin1, eqc(w, A, fe)], 'breqtrd', '( ; 6 4 x. %s ) <_ ( exp ` %s )' % (X2, AA))
    return fin(w)


if __name__ == '__main__':
    for lab in ORDER[:7]:
        if want(lab):
            ok = globals()[lab]()
            if not ok:
                sys.exit(1)
