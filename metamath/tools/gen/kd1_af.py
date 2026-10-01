"""Sortie KD1: the general-k diagonal bound, sharp form (kddiag2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith, nlinarith
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


BND = '( ( ( ( ! ` K ) x. ( exp ` 1 ) ) x. ( ( 5 / 4 ) x. ( K + 2 ) ) ) / ( U ^ ( K + 1 ) ) )'


def diag_at(w, ante, V, W, vp, wp, w1, kk, uc, sumeq):
    """kddiag at V, W with V + W = U ( sumeq : ( ante -> ( V + W ) = U ) ): returns (conv, bound) steps
    ( ante -> DIAGSEQ(K, 1 + U) e. dom ~~> ), ( ante -> DIAG(K, 1 + U) <_ ( K! / V^K ) ( ( 5/4 ) / W + 5 ) )"""
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
    X = '( 1 + ( %s + %s ) )' % (V, W)
    B1 = '( ( ( ! ` K ) / ( %s ^ K ) ) x. ( ( ( 5 / 4 ) / %s ) + 5 ) )' % (V, W)
    dg = a([a([vp, wp, w1], '3jca', '( %s e. RR+ /\\ %s e. RR+ /\\ %s <_ 1 )' % (V, W, W)), kk, w.inst('kddiag')], 'syl2anc',
           '( %s e. dom ~~> /\\ %s <_ %s )' % (DIAGSEQ('K', X), DIAG('K', X), B1))
    x1 = a([sumeq], 'oveq2d', '%s = ( 1 + U )' % X)
    ES = '%s = ( 1 + U )' % X
    ide = w.s([], 'id', '( %s -> %s )' % (ES, ES))
    c1, n1 = w.congr(DIAGSEQ('K', X), {}, ES, {}, rules={X: ('( 1 + U )', ide)})
    c2, n2 = w.congr(DIAG('K', X), {}, ES, {}, rules={X: ('( 1 + U )', ide)})
    e1 = a([x1, c1], 'syl', '%s = %s' % (DIAGSEQ('K', X), n1))
    e2 = a([x1, c2], 'syl', '%s = %s' % (DIAG('K', X), n2))
    conv = a([a([dg], 'simpld', '%s e. dom ~~>' % DIAGSEQ('K', X)), a([e1], 'eleq1d', '( %s e. dom ~~> <-> %s e. dom ~~> )' % (DIAGSEQ('K', X), n1))], 'mpbid', '%s e. dom ~~>' % n1)
    bd = a([e2, a([dg], 'simprd', '%s <_ %s' % (DIAG('K', X), B1))], 'eqbrtrrd', '%s <_ %s' % (n2, B1))
    return conv, bd, B1


def gen_diag2():
    w = W('kddiag2', 'Lean ` KDerivDetect.tsum_vonMangoldt_log_pow_rpow_le\' ` : ` sum Lam ( n ) ( log n ) ^ K n ^ -u ( 1 + U ) <_ K ! e ( 5 / 4 ) ( K + 2 ) / U ^ ( K + 1 ) ` for ` 0 < U <_ 1 / 20 ` (Lean ` K ! e ( K + 2 ) / U ^ ( K + 1 ) ` ; ` kddiag ` at ` V = U K / ( K + 1 ) ` , ` W = U / ( K + 1 ) ` , and at ` V = W = U / 2 ` for ` K = 0 ` ).')
    A0 = S['kddiag2'].split(' -> ( seq')[0][2:]
    GOAL = S['kddiag2'].split(' -> ', 1)[1][:-2]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    uu = s([], 'simpl', '( U e. RR+ /\\ U <_ %s )' % R120); kk = s([], 'simpr', 'K e. NN0')
    up = s([uu], 'simpld', 'U e. RR+'); u20 = s([uu], 'simprd', 'U <_ %s' % R120)
    ur = s([up], 'rpred', 'U e. RR'); uc = s([up], 'rpcnd', 'U e. CC'); un = s([up], 'rpne0d', 'U =/= 0')
    c0 = Closure(w, A0, {'U': ('RR', ur)})
    R = '( 1 / U )'
    rp = s([up], 'rpreccld', '%s e. RR+' % R); rr = s([rp], 'rpred', '%s e. RR' % R); rc = s([rp], 'rpcnd', '%s e. CC' % R)
    lr = s([up, c0.mem(R120, 'RR+')], 'lerecd', '( U <_ %s <-> ( 1 / %s ) <_ %s )' % (R120, R120, R))
    r20a = s([u20, lr], 'mpbid', '( 1 / %s ) <_ %s' % (R120, R))
    rrec = s([c0.mem('; 2 0', 'CC'), c0.ne0('; 2 0')], 'recrecd', '( 1 / %s ) = ; 2 0' % R120)
    r20 = s([rrec, r20a], 'eqbrtrrd', '; 2 0 <_ %s' % R)
    ep_ = w.s([w.s([w.s([], '1re', '1 e. RR'), w.inst('reefcl')], 'ax-mp', '( exp ` 1 ) e. RR')], 'a1i', '( %s -> ( exp ` 1 ) e. RR )' % A0)
    # ---------------- case K e. NN
    A1 = '( %s /\\ K e. NN )' % A0
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    L = lambda st: lift(w, st, A1)
    kn = a([], 'simpr', 'K e. NN')
    kr = a([kn], 'nnrpd', 'K e. RR+'); kc = a([kr], 'rpcnd', 'K e. CC'); kne = a([kr], 'rpne0d', 'K =/= 0')
    K1 = '( K + 1 )'
    k1p = a([kr, w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % A1)], 'rpaddcld', '%s e. RR+' % K1)
    k1c = a([k1p], 'rpcnd', '%s e. CC' % K1); k1n = a([k1p], 'rpne0d', '%s =/= 0' % K1)
    Q1 = '( K / %s )' % K1
    q1p = a([kr, k1p], 'rpdivcld', '%s e. RR+' % Q1)
    V = '( U x. %s )' % Q1; W_ = '( U / %s )' % K1
    vp = a([L(up), q1p], 'rpmulcld', '%s e. RR+' % V)
    wp = a([L(up), k1p], 'rpdivcld', '%s e. RR+' % W_)
    cw = Closure(w, A1, {'U': ('RR', L(ur)), 'K': ('RR', a([kr], 'rpred', 'K e. RR'))})
    cw.have('U', 'gt0', a([L(up)], 'rpgt0d', '0 < U')); cw.have('K', 'gt0', a([kr], 'rpgt0d', '0 < K'))
    wle1 = a([nlinarith(w, A1, [a([L(up)], 'rpge0d', '0 <_ U'), a([kr], 'rpge0d', '0 <_ K')], 'U <_ ( %s x. U )' % K1, closure=cw),
              a([L(ur), L(ur), k1p], 'ledivmuld', '( ( U / %s ) <_ U <-> U <_ ( %s x. U ) )' % (K1, K1))], 'mpbird', '( U / %s ) <_ U' % K1)
    cw.leaf(W_, 'RR', a([wp], 'rpred', '%s e. RR' % W_)); cw.atom(W_)
    w1 = linarith(w, A1, [wle1, L(u20)], '%s <_ 1' % W_, closure=cw)
    # V + W = U
    RK = '( 1 / %s )' % K1
    rkc = a([k1c, k1n], 'reccld', '%s e. CC' % RK)
    wd = a([L(uc), k1c, k1n], 'divrecd', '%s = ( U x. %s )' % (W_, RK))
    s1 = a([a([wd], 'oveq2d', '( %s + %s ) = ( %s + ( U x. %s ) )' % (V, W_, V, RK)), a([L(uc), a([kc, k1c, k1n], 'divcld', '%s e. CC' % Q1), rkc], 'adddid', '( U x. ( %s + %s ) ) = ( %s + ( U x. %s ) )' % (Q1, RK, V, RK))],
           'eqtr4d', '( %s + %s ) = ( U x. ( %s + %s ) )' % (V, W_, Q1, RK))
    s2 = a([kc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), k1c, k1n], 'divdird', '( %s / %s ) = ( %s + %s )' % (K1, K1, Q1, RK))
    s3 = a([k1c, k1n], 'dividd', '( %s / %s ) = 1' % (K1, K1))
    s4 = a([s2, s3], 'eqtr3d', '( %s + %s ) = 1' % (Q1, RK))
    s5 = a([s1, a([s4], 'oveq2d', '( U x. ( %s + %s ) ) = ( U x. 1 )' % (Q1, RK)), a([L(uc)], 'mulridd', '( U x. 1 ) = U')], '3eqtrd', '( %s + %s ) = U' % (V, W_))
    conv1, bd1, B1 = diag_at(w, A1, V, W_, vp, wp, w1, L(kk), L(uc), s5)
    FK = '( ! ` K )'
    fk = a([L(kk), w.inst('faccl')], 'syl', '%s e. NN' % FK)
    fkc = a([fk], 'nncnd', '%s e. CC' % FK); fkr = a([fk], 'nnred', '%s e. RR' % FK); fk0 = a([a([fk], 'nnrpd', '%s e. RR+' % FK)], 'rpge0d', '0 <_ %s' % FK)
    vc = a([vp], 'rpcnd', '%s e. CC' % V); vn = a([vp], 'rpne0d', '%s =/= 0' % V)
    wc = a([wp], 'rpcnd', '%s e. CC' % W_); wn = a([wp], 'rpne0d', '%s =/= 0' % W_)
    Q = '( %s / K )' % K1
    # K! / V^K = K! ( 1 / V ) ^ K
    vk = a([vc, L(kk)], 'expcld', '( %s ^ K ) e. CC' % V); vkn = a([vc, vn, a([L(kk)], 'nn0zd', 'K e. ZZ')], 'expne0d', '( %s ^ K ) =/= 0' % V)
    e1 = a([fkc, vk, vkn], 'divrecd', '( %s / ( %s ^ K ) ) = ( %s x. ( 1 / ( %s ^ K ) ) )' % (FK, V, FK, V))
    e2 = a([vc, vn, a([L(kk)], 'nn0zd', 'K e. ZZ')], 'exprecd', '( ( 1 / %s ) ^ K ) = ( 1 / ( %s ^ K ) )' % (V, V))
    e3 = a([e1, a([e2], 'oveq2d', '( %s x. ( ( 1 / %s ) ^ K ) ) = ( %s x. ( 1 / ( %s ^ K ) ) )' % (FK, V, FK, V))], 'eqtr4d', '( %s / ( %s ^ K ) ) = ( %s x. ( ( 1 / %s ) ^ K ) )' % (FK, V, FK, V))
    # 1 / V = R Q
    q1c = a([q1p], 'rpcnd', '%s e. CC' % Q1); q1n = a([q1p], 'rpne0d', '%s =/= 0' % Q1)
    e4 = a([w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), L(uc), w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), q1c, L(un), q1n], 'divmuldivd',
           '( ( 1 / U ) x. ( 1 / %s ) ) = ( ( 1 x. 1 ) / %s )' % (Q1, V))
    e5 = a([e4, a([w.s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( %s -> ( 1 x. 1 ) = 1 )' % A1)], 'oveq1d', '( ( 1 x. 1 ) / %s ) = ( 1 / %s )' % (V, V))], 'eqtrd', '( ( 1 / U ) x. ( 1 / %s ) ) = ( 1 / %s )' % (Q1, V))
    e6 = a([kc, k1c, kne, k1n], 'recdivd', '( 1 / %s ) = %s' % (Q1, Q))
    e7 = a([e5, a([e6], 'oveq2d', '( ( 1 / U ) x. ( 1 / %s ) ) = ( %s x. %s )' % (Q1, R, Q))], 'eqtr3d', '( 1 / %s ) = ( %s x. %s )' % (V, R, Q))
    # ( 5 / 4 ) / W = ( 5 / 4 ) ( ( K + 1 ) R )
    c54 = Closure(w, A1, {})
    e8 = a([c54.mem('( 5 / 4 )', 'CC'), wc, wn], 'divrecd', '( ( 5 / 4 ) / %s ) = ( ( 5 / 4 ) x. ( 1 / %s ) )' % (W_, W_))
    e9 = a([L(uc), k1c, L(un), k1n], 'recdivd', '( 1 / %s ) = ( %s / U )' % (W_, K1))
    e10 = a([k1c, L(uc), L(un)], 'divrecd', '( %s / U ) = ( %s x. %s )' % (K1, K1, R))
    e11 = a([e8, a([a([e9, e10], 'eqtrd', '( 1 / %s ) = ( %s x. %s )' % (W_, K1, R))], 'oveq2d', '( ( 5 / 4 ) x. ( 1 / %s ) ) = ( ( 5 / 4 ) x. ( %s x. %s ) )' % (W_, K1, R))], 'eqtrd',
            '( ( 5 / 4 ) / %s ) = ( ( 5 / 4 ) x. ( %s x. %s ) )' % (W_, K1, R))
    Y1 = '( ( ( 5 / 4 ) x. ( %s x. %s ) ) + 5 )' % (K1, R)
    RQK = '( ( %s x. %s ) ^ K )' % (R, Q)
    e12 = a([e3, a([a([e7], 'oveq1d', '( ( 1 / %s ) ^ K ) = %s' % (V, RQK))], 'oveq2d', '( %s x. ( ( 1 / %s ) ^ K ) ) = ( %s x. %s )' % (FK, V, FK, RQK))], 'eqtrd', '( %s / ( %s ^ K ) ) = ( %s x. %s )' % (FK, V, FK, RQK))
    eB = a([e12, a([e11], 'oveq1d', '( ( ( 5 / 4 ) / %s ) + 5 ) = %s' % (W_, Y1))], 'oveq12d', '%s = ( ( %s x. %s ) x. %s )' % (B1, FK, RQK, Y1))
    qc = a([k1c, kc, kne], 'divcld', '%s e. CC' % Q)
    RK_ = '( %s ^ K )' % R; QK = '( %s ^ K )' % Q
    mx = a([L(rc), qc, L(kk)], 'mulexpd', '%s = ( %s x. %s )' % (RQK, RK_, QK))
    eB2 = a([eB, a([a([mx], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (FK, RQK, FK, RK_, QK))], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( ( %s x. ( %s x. %s ) ) x. %s )' % (FK, RQK, Y1, FK, RK_, QK, Y1))],
            'eqtrd', '%s = ( ( %s x. ( %s x. %s ) ) x. %s )' % (B1, FK, RK_, QK, Y1))
    # Q ^ K <_ e
    IK = '( 1 / K )'
    ikp = a([kr], 'rpreccld', '%s e. RR+' % IK)
    qe = a([a([kc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A1), kc, kne], 'divdird', '%s = ( ( K / K ) + %s )' % (Q, IK)), a([a([kc, kne], 'dividd', '( K / K ) = 1')], 'oveq1d', '( ( K / K ) + %s ) = ( 1 + %s )' % (IK, IK))],
           'eqtrd', '%s = ( 1 + %s )' % (Q, IK))
    eg = a([ikp, w.inst('efgt1p')], 'syl', '( 1 + %s ) < ( exp ` %s )' % (IK, IK))
    c2 = Closure(w, A1, {IK: ('RR', a([ikp], 'rpred', '%s e. RR' % IK))}); c2.atom(IK)
    c2.leaf('( exp ` %s )' % IK, 'RR', a([a([ikp], 'rpred', '%s e. RR' % IK), w.inst('reefcl')], 'syl', '( exp ` %s ) e. RR' % IK)); c2.atom('( exp ` %s )' % IK)
    egl = a([c2.mem('( 1 + %s )' % IK, 'RR'), c2.mem('( exp ` %s )' % IK, 'RR'), eg], 'ltled', '( 1 + %s ) <_ ( exp ` %s )' % (IK, IK))
    q0 = linarith(w, A1, [a([ikp], 'rpge0d', '0 <_ %s' % IK)], '0 <_ ( 1 + %s )' % IK, closure=c2)
    ql = a([c2.mem('( 1 + %s )' % IK, 'RR'), c2.mem('( exp ` %s )' % IK, 'RR'), L(kk), q0, egl], 'leexp1ad', '( ( 1 + %s ) ^ K ) <_ ( ( exp ` %s ) ^ K )' % (IK, IK))
    ex = a([a([ikp], 'rpcnd', '%s e. CC' % IK), a([L(kk)], 'nn0zd', 'K e. ZZ'), w.inst('efexp')], 'syl2anc', '( exp ` ( K x. %s ) ) = ( ( exp ` %s ) ^ K )' % (IK, IK))
    ex2 = a([a([a([kc, kne], 'recidd', '( K x. %s ) = 1' % IK)], 'fveq2d', '( exp ` ( K x. %s ) ) = ( exp ` 1 )' % IK), ex], 'eqtr3d', '( exp ` 1 ) = ( ( exp ` %s ) ^ K )' % IK)
    ql2 = a([ql, ex2], 'breqtrrd', '( ( 1 + %s ) ^ K ) <_ ( exp ` 1 )' % IK)
    qk = a([a([a([qe], 'oveq1d', '%s = ( ( 1 + %s ) ^ K )' % (QK, IK))], 'id' if False else 'eqcomd', '( ( 1 + %s ) ^ K ) = %s' % (IK, QK)), ql2], 'eqbrtrrd' if False else 'T.', 'T.') if False else \
        a([a([qe], 'oveq1d', '%s = ( ( 1 + %s ) ^ K )' % (QK, IK)), ql2], 'eqbrtrd', '%s <_ ( exp ` 1 )' % QK)
    Z1 = '( ( 5 / 4 ) x. ( ( K + 2 ) x. %s ) )' % R
    cz = Closure(w, A1, {'K': ('CC', kc), R: ('CC', L(rc))}); cz.atom(R)
    DD = '( ( ( 5 / 4 ) x. %s ) - 5 )' % R
    zy = ringeq(w, A1, Z1, '( %s + %s )' % (Y1, DD), cz)
    cr = Closure(w, A1, {R: ('RR', L(rr)), 'K': ('RR', a([kr], 'rpred', 'K e. RR'))}); cr.atom(R)
    dd0 = linarith(w, A1, [L(r20)], '0 <_ %s' % DD, closure=cr)
    y1r = cr.mem(Y1, 'RR')
    yz = a([a([y1r, cr.mem(DD, 'RR')], 'addge01d', '( 0 <_ %s <-> %s <_ ( %s + %s ) )' % (DD, Y1, Y1, DD)), dd0], 'T.', 'T.') if False else \
        a([dd0, a([y1r, cr.mem(DD, 'RR')], 'addge01d', '( 0 <_ %s <-> %s <_ ( %s + %s ) )' % (DD, Y1, Y1, DD))], 'mpbid', '%s <_ ( %s + %s )' % (Y1, Y1, DD))
    yz2 = a([yz, zy], 'breqtrrd', '%s <_ %s' % (Y1, Z1))
    rk = a([L(rp), a([L(kk)], 'nn0zd', 'K e. ZZ')], 'rpexpcld', '%s e. RR+' % RK_)
    rkr = a([rk], 'rpred', '%s e. RR' % RK_); rk0 = a([rk], 'rpge0d', '0 <_ %s' % RK_)
    qp = a([k1p, kr], 'rpdivcld', '%s e. RR+' % Q)
    qkp = a([qp, a([L(kk)], 'nn0zd', 'K e. ZZ')], 'rpexpcld', '%s e. RR+' % QK)
    E1 = '( exp ` 1 )'
    m1 = a([a([qkp], 'rpred', '%s e. RR' % QK), L(ep_), rkr, rk0, qk], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (RK_, QK, RK_, E1))
    cy = Closure(w, A1, {R: ('RR', L(rr)), 'K': ('RR', a([kr], 'rpred', 'K e. RR'))}); cy.atom(R)
    cy.have(R, 'gt0', a([L(rp)], 'rpgt0d', '0 < %s' % R)); cy.have('K', 'gt0', a([kr], 'rpgt0d', '0 < K'))
    y10 = cy.ge0(Y1)
    m2 = a([a([rkr, a([qkp], 'rpred', '%s e. RR' % QK)], 'remulcld', '( %s x. %s ) e. RR' % (RK_, QK)), a([rkr, L(ep_)], 'remulcld', '( %s x. %s ) e. RR' % (RK_, E1)), y1r, cr.mem(Z1, 'RR'),
            a([a([rkr, a([qkp], 'rpred', '%s e. RR' % QK)], 'remulcld', '( %s x. %s ) e. RR' % (RK_, QK)) and rk0, a([qkp], 'rpge0d', '0 <_ %s' % QK)] and [rkr, a([qkp], 'rpred', '%s e. RR' % QK), rk0, a([qkp], 'rpge0d', '0 <_ %s' % QK)], 'mulge0d', '0 <_ ( %s x. %s )' % (RK_, QK)),
            y10, m1, yz2], 'lemul12ad', '( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. %s )' % (RK_, QK, Y1, RK_, E1, Z1))
    m3 = a([a([a([rkr, a([qkp], 'rpred', '%s e. RR' % QK)], 'remulcld', '( %s x. %s ) e. RR' % (RK_, QK)), y1r], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (RK_, QK, Y1)),
            a([a([rkr, L(ep_)], 'remulcld', '( %s x. %s ) e. RR' % (RK_, E1)), cr.mem(Z1, 'RR')], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (RK_, E1, Z1)), fkr, fk0, m2], 'lemul2ad',
           '( %s x. ( ( %s x. %s ) x. %s ) ) <_ ( %s x. ( ( %s x. %s ) x. %s ) )' % (FK, RK_, QK, Y1, FK, RK_, E1, Z1))
    ca = Closure(w, A1, {FK: ('CC', fkc), RK_: ('CC', a([rk], 'rpcnd', '%s e. CC' % RK_)), QK: ('CC', a([qkp], 'rpcnd', '%s e. CC' % QK)), Y1: ('CC', a([y1r], 'recnd', '%s e. CC' % Y1))})
    for x_ in (FK, RK_, QK, Y1):
        ca.atom(x_)
    rb = ringeq(w, A1, '( ( %s x. ( %s x. %s ) ) x. %s )' % (FK, RK_, QK, Y1), '( %s x. ( ( %s x. %s ) x. %s ) )' % (FK, RK_, QK, Y1), ca)
    # the target
    XN = '( ( %s x. %s ) x. ( ( 5 / 4 ) x. ( K + 2 ) ) )' % (FK, E1)
    uk1 = a([L(uc), a([L(kk), w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')], 'expcld', '( U ^ ( K + 1 ) ) e. CC')
    uk1n = a([L(uc), L(un), a([a([L(kk), w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')], 'nn0zd', '( K + 1 ) e. ZZ')], 'expne0d', '( U ^ ( K + 1 ) ) =/= 0')
    xnc = a([a([fkc, a([L(ep_)], 'recnd', '%s e. CC' % E1)], 'mulcld', '( %s x. %s ) e. CC' % (FK, E1)), a([c54.mem('( 5 / 4 )', 'CC'), a([kc, a([w.s([], '2cnd', '( %s -> 2 e. CC )' % A1)], 'id' if False else 'T.', 'T.') if False else w.s([], '2cnd', '( %s -> 2 e. CC )' % A1)], 'addcld', '( K + 2 ) e. CC')], 'mulcld', '( ( 5 / 4 ) x. ( K + 2 ) ) e. CC')],
            'mulcld', '%s e. CC' % XN)
    t1 = a([xnc, uk1, uk1n], 'divrecd', '%s = ( %s x. ( 1 / ( U ^ ( K + 1 ) ) ) )' % (BND, XN))
    t2 = a([L(uc), L(un), a([a([L(kk), w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')], 'nn0zd', '( K + 1 ) e. ZZ')], 'exprecd', '( %s ^ ( K + 1 ) ) = ( 1 / ( U ^ ( K + 1 ) ) )' % R)
    t3 = a([L(rc), L(kk)], 'expp1d', '( %s ^ ( K + 1 ) ) = ( %s x. %s )' % (R, RK_, R))
    t4 = a([t1, a([a([t2, t3], 'eqtr3d', '( 1 / ( U ^ ( K + 1 ) ) ) = ( %s x. %s )' % (RK_, R))], 'oveq2d', '( %s x. ( 1 / ( U ^ ( K + 1 ) ) ) ) = ( %s x. ( %s x. %s ) )' % (XN, XN, RK_, R))], 'eqtrd',
           '%s = ( %s x. ( %s x. %s ) )' % (BND, XN, RK_, R))
    cb = Closure(w, A1, {FK: ('CC', fkc), E1: ('CC', a([L(ep_)], 'recnd', '%s e. CC' % E1)), RK_: ('CC', a([rk], 'rpcnd', '%s e. CC' % RK_)), R: ('CC', L(rc)), 'K': ('CC', kc)})
    for x_ in (FK, E1, RK_, R):
        cb.atom(x_)
    t5 = ringeq(w, A1, '( %s x. ( ( %s x. %s ) x. %s ) )' % (FK, RK_, E1, Z1), '( %s x. ( %s x. %s ) )' % (XN, RK_, R), cb)
    tgt = a([t5, t4], 'eqtr4d', '( %s x. ( ( %s x. %s ) x. %s ) ) = %s' % (FK, RK_, E1, Z1, BND))
    b1b = a([a([eB2, rb], 'eqtrd', '%s = ( %s x. ( ( %s x. %s ) x. %s ) )' % (B1, FK, RK_, QK, Y1)), m3], 'eqbrtrd', '%s <_ ( %s x. ( ( %s x. %s ) x. %s ) )' % (B1, FK, RK_, E1, Z1))
    b1c = a([b1b, tgt], 'breqtrd', '%s <_ %s' % (B1, BND))
    SUMB = DIAG('K', '( 1 + U )')
    cA = Closure(w, A1, {})
    def xrchain(ante, lo_st, S_, B_, T_, bd_, bt_, trr):
        """( ante -> S_ <_ T_ ) from bd_ : S_ <_ B_ , bt_ : B_ <_ T_ , trr : T_ e. RR"""
        a_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        lx = w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')
        br = a_([bd_, w.s([lx], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (S_, B_, S_, B_))], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (S_, B_))
        return a_([a_([br], 'simpld', '%s e. RR*' % S_), a_([br], 'simprd', '%s e. RR*' % B_), a_([trr], 'rexrd', '%s e. RR*' % T_), bd_, bt_], 'xrletrd', '%s <_ %s' % (S_, T_))
    bndr = cr.mem(BND, 'RR') if False else a([a([a([fkr, L(ep_)], 'remulcld', '( %s x. %s ) e. RR' % (FK, E1)), cr.mem('( ( 5 / 4 ) x. ( K + 2 ) )', 'RR')], 'remulcld', '%s e. RR' % XN),
                                             a([L(up), a([a([L(kk), w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')], 'nn0zd', '( K + 1 ) e. ZZ')], 'rpexpcld', '( U ^ ( K + 1 ) ) e. RR+')], 'rerpdivcld', '%s e. RR' % BND)
    SUMB = DIAG('K', '( 1 + U )')
    fb1 = xrchain(A1, None, SUMB, B1, BND, bd1, b1c, bndr)
    G1 = a([conv1, fb1], 'jca', GOAL)
    # ---------------- case K = 0
    A2 = '( %s /\\ K = 0 )' % A0
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A2, f))
    M = lambda st: lift(w, st, A2)
    k0 = b([], 'simpr', 'K = 0')
    H = '( U / 2 )'
    hp = b([M(up)], 'rphalfcld', '%s e. RR+' % H)
    ch = Closure(w, A2, {'U': ('RR', M(ur))})

    h1 = linarith(w, A2, [M(u20)], '%s <_ 1' % H, closure=ch)
    hh = b([M(uc)], '2halvesd', '( %s + %s ) = U' % (H, H))
    conv2, bd2, B2 = diag_at(w, A2, H, H, hp, hp, h1, M(kk), M(uc), hh)
    k0i = w.s([], 'id', '( K = 0 -> K = 0 )')
    cB2, B2z = w.congr(B2, {'K': '0'}, 'K = 0', {'K': k0i})
    cBN, BNz = w.congr(BND, {'K': '0'}, 'K = 0', {'K': k0i})
    eb2 = b([k0, cB2], 'syl', '%s = %s' % (B2, B2z)); ebn = b([k0, cBN], 'syl', '%s = %s' % (BND, BNz))
    # B2z = 1 x. ( ( 5 / 4 ) / ( U / 2 ) + 5 ) and BNz = ( ( 1 x. e ) x. ( ( 5 / 4 ) x. 2 ) ) / U
    hc = b([hp], 'rpcnd', '%s e. CC' % H); hn = b([hp], 'rpne0d', '%s =/= 0' % H)
    f0 = w.s([w.s([], 'fac0', '( ! ` 0 ) = 1')], 'a1i', '( %s -> ( ! ` 0 ) = 1 )' % A2)
    x0 = b([hc], 'exp0d', '( %s ^ 0 ) = 1' % H)
    d11 = b([f0, x0], 'oveq12d', '( ( ! ` 0 ) / ( %s ^ 0 ) ) = ( 1 / 1 )' % H)
    d1 = b([d11, b([w.s([], '1cnd', '( %s -> 1 e. CC )' % A2)], 'div1d', '( 1 / 1 ) = 1')], 'eqtrd', '( ( ! ` 0 ) / ( %s ^ 0 ) ) = 1' % H)
    Y2 = '( ( ( 5 / 4 ) / %s ) + 5 )' % H
    assert B2z == '( ( ( ! ` 0 ) / ( %s ^ 0 ) ) x. %s )' % (H, Y2), B2z
    bz1 = b([d1], 'oveq1d', '%s = ( 1 x. %s )' % (B2z, Y2))
    c5 = Closure(w, A2, {})
    q5 = b([c5.mem('( 5 / 4 )', 'CC'), M(uc), w.s([], '2cnd', '( %s -> 2 e. CC )' % A2), M(un), w.s([], '2ne0d' if False else 'T.', 'T.') if False else c5.ne0('2')], 'divdiv2d', '( ( 5 / 4 ) / %s ) = ( ( ( 5 / 4 ) x. 2 ) / U )' % H)
    q6 = b([c5.mem('( ( 5 / 4 ) x. 2 )', 'CC'), M(uc), M(un)], 'divrecd', '( ( ( 5 / 4 ) x. 2 ) / U ) = ( ( ( 5 / 4 ) x. 2 ) x. %s )' % R)
    Y2b = '( ( ( ( 5 / 4 ) x. 2 ) x. %s ) + 5 )' % R
    y2e = b([b([q5, q6], 'eqtrd', '( ( 5 / 4 ) / %s ) = ( ( ( 5 / 4 ) x. 2 ) x. %s )' % (H, R))], 'oveq1d', '%s = %s' % (Y2, Y2b))
    bz2 = b([bz1, b([y2e], 'oveq2d', '( 1 x. %s ) = ( 1 x. %s )' % (Y2, Y2b))], 'eqtrd', '%s = ( 1 x. %s )' % (B2z, Y2b))
    XNz = '( ( ( ! ` 0 ) x. %s ) x. ( ( 5 / 4 ) x. ( 0 + 2 ) ) )' % E1
    assert BNz == '( %s / ( U ^ ( 0 + 1 ) ) )' % XNz, BNz
    u1 = b([b([w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % A2)], 'oveq2d', '( U ^ ( 0 + 1 ) ) = ( U ^ 1 )'), b([M(uc)], 'exp1d', '( U ^ 1 ) = U')], 'eqtrd', '( U ^ ( 0 + 1 ) ) = U')
    xnzc = b([b([b([f0, w.s([], '1cnd', '( %s -> 1 e. CC )' % A2)], 'eqeltrd', '( ! ` 0 ) e. CC'), b([M(ep_)], 'recnd', '%s e. CC' % E1)], 'mulcld', '( ( ! ` 0 ) x. %s ) e. CC' % E1),
               c5.mem('( ( 5 / 4 ) x. ( 0 + 2 ) )', 'CC')], 'mulcld', '%s e. CC' % XNz)
    bn1 = b([b([u1], 'oveq2d', '%s = ( %s / U )' % (BNz, XNz)), b([xnzc, M(uc), M(un)], 'divrecd', '( %s / U ) = ( %s x. %s )' % (XNz, XNz, R))], 'eqtrd', '%s = ( %s x. %s )' % (BNz, XNz, R))
    ce = Closure(w, A2, {E1: ('RR', M(ep_)), R: ('RR', M(rr))}); ce.atom(E1); ce.atom(R)
    ce.leaf('( ! ` 0 )', 'RR', b([f0, w.s([], '1red', '( %s -> 1 e. RR )' % A2)], 'eqeltrd', '( ! ` 0 ) e. RR')); ce.atom('( ! ` 0 )')
    eg = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e')
    e2a = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], 'ere', '_e e. RR'), eg], 'ltleii', '2 <_ _e'), w.s([], 'df-e', '_e = ( exp ` 1 )')], 'breqtri', '2 <_ ( exp ` 1 )')
    e2 = w.s([e2a], 'a1i', '( %s -> 2 <_ ( exp ` 1 ) )' % A2)
    ineq = nlinarith(w, A2, [e2, M(r20), f0], '( 1 x. %s ) <_ ( %s x. %s )' % (Y2b, XNz, R), closure=ce)
    bz3 = b([bz2, ineq], 'eqbrtrd', '%s <_ ( %s x. %s )' % (B2z, XNz, R))
    bz4 = b([eb2, b([bz3, b([ebn, bn1], 'eqtrd', '%s = ( %s x. %s )' % (BND, XNz, R))], 'breqtrrd', '%s <_ %s' % (B2z, BND))], 'eqbrtrd', '%s <_ %s' % (B2, BND))
    bnd2r = b([b([ebn, bn1], 'eqtrd', '%s = ( %s x. %s )' % (BND, XNz, R)), ce.mem('( %s x. %s )' % (XNz, R), 'RR')], 'eqeltrd', '%s e. RR' % BND)
    fb2 = xrchain(A2, None, SUMB, B2, BND, bd2, bz4, bnd2r)
    G2 = b([conv2, fb2], 'jca', GOAL)
    orr = s([kk, w.s([], 'elnn0', '( K e. NN0 <-> ( K e. NN \\/ K = 0 ) )')], 'sylib', '( K e. NN \\/ K = 0 )')
    w.qed([G1, G2, orr], 'mpjaodan', S['kddiag2'])
    return run(w)






if __name__ == '__main__':
    gen_diag2()
