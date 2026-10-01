"""ZL3b D6: zl3wpois (Poisson in the rotated plane) and zl3pois.
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_d6.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of, twopi, TP
from zl3b_d2 import cst, reim_cp, cpcl
from zl3b_d4 import chain_eq
from zl3b_d5 import vl_sub

only = sys.argv[1:]
S = STATEMENTS
TIP = '( 2 x. ( _i x. _pi ) )'
TWO = '( 2 x. _pi )'


def BODY(c):
    return '( ~~>r ` ( t e. RR+ |-> S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x ) )' % (TIP, c)


assert HT == '( k e. ZZ |-> %s )' % BODY('k')
HTq = '( q e. ZZ |-> %s )' % BODY('q')


def bsub(w, E, a_, b_):
    """( E -> BODY(a) = BODY(b) ), E is the text 'a = b'"""
    A5 = '( %s /\\ t e. RR+ )' % E
    A6 = '( %s /\\ x e. ( -u t (,) t ) )' % A5
    ee = w.s([w.s([], 'id', '( %s -> %s )' % (E, E))], 'ad2antrr', '( %s -> %s )' % (A6, E))
    inner = D(w, A6, 'oveq2d', [D(w, A6, 'fveq2d', [D(w, A6, 'negeqd', [D(w, A6, 'oveq2d', [D(w, A6, 'oveq1d', [ee], '( %s x. x ) = ( %s x. x )' % (a_, b_))], '( %s x. ( %s x. x ) ) = ( %s x. ( %s x. x ) )' % (TIP, a_, TIP, b_))],
                                                      '-u ( %s x. ( %s x. x ) ) = -u ( %s x. ( %s x. x ) )' % (TIP, a_, TIP, b_))], '( exp ` -u ( %s x. ( %s x. x ) ) ) = ( exp ` -u ( %s x. ( %s x. x ) ) )' % (TIP, a_, TIP, b_))],
                '( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) = ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) )' % (TIP, a_, TIP, b_))
    I = lambda c: 'S. ( -u t (,) t ) ( ( H ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x' % (TIP, c)
    ig = w.s([inner], 'itgeq2dv', '( %s -> %s = %s )' % (A5, I(a_), I(b_)))
    mq = w.s([ig], 'mpteq2dva', '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s ) )' % (E, I(a_), I(b_)))
    return D(w, E, 'fveq2d', [mq], '%s = %s' % (BODY(a_), BODY(b_)))


def mi(w, A_, X, xc):
    """( A_ -> ( -u _i x. ( _i x. X ) ) = X )"""
    ic_ = cst(w, A_, 'ax-icn', '_i e. CC')
    a1 = D(w, A_, 'eqcomd', [D(w, A_, 'mulassd', [D(w, A_, 'negcld', [ic_], '-u _i e. CC'), ic_, xc], '( ( -u _i x. _i ) x. %s ) = ( -u _i x. ( _i x. %s ) )' % (X, X))],
           '( -u _i x. ( _i x. %s ) ) = ( ( -u _i x. _i ) x. %s )' % (X, X))
    ii = D(w, A_, 'eqtrd', [D(w, A_, 'eqtrd', [D(w, A_, 'mulneg1d', [ic_, ic_], '( -u _i x. _i ) = -u ( _i x. _i )'), D(w, A_, 'negeqd', [cst(w, A_, 'ixi', '( _i x. _i ) = -u 1')], '-u ( _i x. _i ) = -u -u 1')],
                                               '( -u _i x. _i ) = -u -u 1'), D(w, A_, 'negnegd', [cst(w, A_, 'ax-1cn', '1 e. CC')], '-u -u 1 = 1')], '( -u _i x. _i ) = 1')
    return D(w, A_, 'eqtrd', [a1, D(w, A_, 'eqtrd', [D(w, A_, 'oveq1d', [ii], '( ( -u _i x. _i ) x. %s ) = ( 1 x. %s )' % (X, X)), D(w, A_, 'mullidd', [xc], '( 1 x. %s ) = %s' % (X, X))],
                                                       '( ( -u _i x. _i ) x. %s ) = %s' % (X, X))], '( -u _i x. ( _i x. %s ) ) = %s' % (X, X))


def fv_q(w, A_, X, xz):
    """( A_ -> ( HTq ` X ) = BODY(X) ) from xz: ( A_ -> X e. ZZ )"""
    return w.s([xz, w.s([bsub(w, 'q = %s' % X, 'q', X), w.s([], 'eqid', '%s = %s' % (HTq, HTq)), w.s([], 'fvex', '%s e. _V' % BODY(X))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (X, HTq, X, BODY(X)))],
               'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, HTq, X, BODY(X)))


if __name__ == '__main__' and (not only or 'zl3wpois' in only):
    w = W('zl3wpois', 'Poisson summation in the rotated plane: the sum of ` H ( i n ) ` over ` ZZ ` equals the sum over ` ZZ ` of the Fourier coefficients of ` x |-> H ( i x ) `.')
    ph = HCTX
    VRk = VL(GKE('H', TPN), '1'); VLk = VL(GKE(GL, TWO), '-u 1'); VRj = VL(GKE('H', TPN, 'j'), '1'); VLj = VL(GKE(GL, TWO, 'j'), '-u 1')
    SRR = 'sum_ k e. NN %s' % VRk; SLL = 'sum_ k e. NN %s' % VLk; SRRj = 'sum_ j e. NN %s' % VRj; SLLj = 'sum_ j e. NN %s' % VLj
    CONV = '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (VRk, VLk)
    wl = w.s([w.s([], 'id', '( %s -> %s )' % (ph, ph)), w.inst('zl3wlim')], 'syl', '( %s -> ( %s /\\ ( %s e. CC /\\ ( _i x. %s ) = ( %s + %s ) ) ) )' % (ph, CONV, PZH, PZH, SRR, SLL))
    cv = w.s([wl, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, CONV))
    wr_ = w.s([wl, w.inst('simpr')], 'syl', '( %s -> ( %s e. CC /\\ ( _i x. %s ) = ( %s + %s ) ) )' % (ph, PZH, PZH, SRR, SLL))
    pzc = w.s([wr_, w.inst('simpl')], 'syl', '( %s -> %s e. CC )' % (ph, PZH)); ipz = w.s([wr_, w.inst('simpr')], 'syl', '( %s -> ( _i x. %s ) = ( %s + %s ) )' % (ph, PZH, SRR, SLL))
    FR = '( j e. NN |-> %s )' % VRj; FL = '( j e. NN |-> %s )' % VLj
    def conv_j(cvx, Vk, F, G_, A_, C_):
        cb = w.s([vl_sub(w, 'k = j', 'k', 'j', G_, A_, C_)], 'cbvmptv', '( k e. NN |-> %s ) = %s' % (Vk, F))
        return D(w, ph, 'mpbid', [cvx, D(w, ph, 'eleq1d', [D(w, ph, 'seqeq3d', [w.s([cb], 'a1i', '( %s -> ( k e. NN |-> %s ) = %s )' % (ph, Vk, F))], 'seq 1 ( + , ( k e. NN |-> %s ) ) = seq 1 ( + , %s )' % (Vk, F))],
                                                         '( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (Vk, F))], 'seq 1 ( + , %s ) e. dom ~~>' % F)
    cvR = conv_j(w.s([cv, w.inst('simpl')], 'syl', '( %s -> seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (ph, VRk)), VRk, FR, 'H', TPN, '1')
    cvL = conv_j(w.s([cv, w.inst('simpr')], 'syl', '( %s -> seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (ph, VLk)), VLk, FL, GL, TWO, '-u 1')
    csR = w.s([vl_sub(w, 'k = j', 'k', 'j', 'H', TPN, '1')], 'cbvsumv', '%s = %s' % (SRR, SRRj))
    csL = w.s([vl_sub(w, 'k = j', 'k', 'j', GL, TWO, '-u 1')], 'cbvsumv', '%s = %s' % (SLL, SLLj))
    # per k
    P1 = '( %s /\\ k e. NN )' % ph
    kN = w.s([], 'simpr', '( %s -> k e. NN )' % P1)
    kz = D(w, P1, 'nnzd', [kN], 'k e. ZZ')
    htk = '( %s ` k )' % HT; ht1k = '( %s ` ( 1 - k ) )' % HT
    VR0 = VL(GKE('H', TPN), '0'); VL0 = VL(GKE(GL, TWO), '0')
    gr = w.s([w.s([], 'id', '( %s -> %s )' % (P1, P1)), w.inst('zl3gkr')], 'syl', '( %s -> ( ( %s = %s /\\ %s e. CC ) /\\ ( %s = ( _i x. %s ) /\\ %s e. CC ) ) )' % (P1, VRk, VR0, VRk, VR0, htk, htk))
    gl = w.s([w.s([], 'id', '( %s -> %s )' % (P1, P1)), w.inst('zl3gkl')], 'syl', '( %s -> ( ( %s = %s /\\ %s e. CC ) /\\ ( %s = ( _i x. %s ) /\\ %s e. CC ) ) )' % (P1, VLk, VL0, VLk, VL0, ht1k, ht1k))
    def parts(g, V, V0, X):
        a_ = w.s([g, w.inst('simpl')], 'syl', '( %s -> ( %s = %s /\\ %s e. CC ) )' % (P1, V, V0, V))
        b_ = w.s([g, w.inst('simpr')], 'syl', '( %s -> ( %s = ( _i x. %s ) /\\ %s e. CC ) )' % (P1, V0, X, X))
        vv = D(w, P1, 'eqtrd', [w.s([a_, w.inst('simpl')], 'syl', '( %s -> %s = %s )' % (P1, V, V0)), w.s([b_, w.inst('simpl')], 'syl', '( %s -> %s = ( _i x. %s ) )' % (P1, V0, X))], '%s = ( _i x. %s )' % (V, X))
        return vv, w.s([a_, w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (P1, V)), w.s([b_, w.inst('simpr')], 'syl', '( %s -> %s e. CC )' % (P1, X))
    vr, vrc, htkc = parts(gr, VRk, VR0, htk)
    vl, vlc, ht1kc = parts(gl, VLk, VL0, ht1k)
    cbq = w.s([bsub(w, 'k = q', 'k', 'q')], 'cbvmptv', '%s = %s' % (HT, HTq))
    toq = lambda A_, X: D(w, A_, 'fveq1d', [w.s([cbq], 'a1i', '( %s -> %s = %s )' % (A_, HT, HTq))], '( %s ` %s ) = ( %s ` %s )' % (HT, X, HTq, X))
    qk = '( %s ` k )' % HTq; q1k = '( %s ` ( 1 - k ) )' % HTq
    qkc = D(w, P1, 'eqeltrrd', [toq(P1, 'k'), htkc], '%s e. CC' % qk)
    q1kc = D(w, P1, 'eqeltrrd', [toq(P1, '( 1 - k )'), ht1kc], '%s e. CC' % q1k)
    ALLB = lambda v: '( ( %s ` %s ) e. CC /\\ ( %s ` ( 1 - %s ) ) e. CC )' % (HTq, v, HTq, v)
    allc = w.s([D(w, P1, 'jca', [qkc, q1kc], ALLB('k'))], 'ralrimiva', '( %s -> A. k e. NN %s )' % (ph, ALLB('k')))
    def spec(A_, X, xN, lift):
        E = 'k = %s' % X
        e = w.s([], 'id', '( %s -> %s )' % (E, E))
        beq = D(w, E, 'anbi12d', [D(w, E, 'eleq1d', [D(w, E, 'fveq2d', [e], '( %s ` k ) = ( %s ` %s )' % (HTq, HTq, X))], '( ( %s ` k ) e. CC <-> ( %s ` %s ) e. CC )' % (HTq, HTq, X)),
                                  D(w, E, 'eleq1d', [D(w, E, 'fveq2d', [D(w, E, 'oveq2d', [e], '( 1 - k ) = ( 1 - %s )' % X)], '( %s ` ( 1 - k ) ) = ( %s ` ( 1 - %s ) )' % (HTq, HTq, X))],
                                    '( ( %s ` ( 1 - k ) ) e. CC <-> ( %s ` ( 1 - %s ) ) e. CC )' % (HTq, HTq, X))], '( %s <-> %s )' % (ALLB('k'), ALLB(X)))
        sp = w.s([xN, lift(allc, 'A. k e. NN %s' % ALLB('k')), w.s([beq], 'rspcv', '( %s e. NN -> ( A. k e. NN %s -> %s ) )' % (X, ALLB('k'), ALLB(X)))], 'sylc', '( %s -> %s )' % (A_, ALLB(X)))
        return w.s([sp, w.inst('simpl')], 'syl', '( %s -> ( %s ` %s ) e. CC )' % (A_, HTq, X)), w.s([sp, w.inst('simpr')], 'syl', '( %s -> ( %s ` ( 1 - %s ) ) e. CC )' % (A_, HTq, X))
    frv = w.s([kN, w.s([vl_sub(w, 'j = k', 'j', 'k', 'H', TPN, '1'), w.s([], 'eqid', '%s = %s' % (FR, FR)), w.s([], 'fvex', '%s e. _V' % VRk)], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (FR, VRk))], 'syl',
              '( %s -> ( %s ` k ) = %s )' % (P1, FR, VRk))
    flv = w.s([kN, w.s([vl_sub(w, 'j = k', 'j', 'k', GL, TWO, '-u 1'), w.s([], 'eqid', '%s = %s' % (FL, FL)), w.s([], 'fvex', '%s e. _V' % VLk)], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (FL, VLk))], 'syl',
              '( %s -> ( %s ` k ) = %s )' % (P1, FL, VLk))
    nnu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); zu = w.s([], 'eqid', '( ZZ>= ` 1 ) = ( ZZ>= ` 1 )'); one_z = cst(w, ph, '1z', '1 e. ZZ')
    PU = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % ph
    kNU = D(w, PU, 'eleqtrrd', [w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % PU), cst(w, PU, 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'k e. NN')
    toU = lambda st, f: w.s([w.s([], 'simpl', '( %s -> %s )' % (PU, ph)), kNU, st], 'syl2anc', '( %s -> %s )' % (PU, f))
    nic = D(w, ph, 'negcld', [cst(w, ph, 'ax-icn', '_i e. CC')], '-u _i e. CC')
    rel = lambda F, L_: w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( seq 1 ( + , %s ) ~~> %s -> seq 1 ( + , %s ) e. dom ~~> )' % (F, L_, F))
    # right: seq HTq ~~> -i SRRj
    frl = D(w, ph, 'breqtrd', [w.s([nnu, one_z, frv, vrc, cvR], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (ph, FR, SRR)), w.s([csR], 'a1i', '( %s -> %s = %s )' % (ph, SRR, SRRj))],
              'seq 1 ( + , %s ) ~~> %s' % (FR, SRRj))
    gR = D(w, P1, 'eqtr4d', [D(w, P1, 'eqcomd', [toq(P1, 'k')], '%s = %s' % (qk, htk)),
                             D(w, P1, 'eqtrd', [D(w, P1, 'oveq2d', [D(w, P1, 'eqtrd', [frv, vr], '( %s ` k ) = ( _i x. %s )' % (FR, htk))], '( -u _i x. ( %s ` k ) ) = ( -u _i x. ( _i x. %s ) )' % (FR, htk)),
                                                mi(w, P1, htk, htkc)], '( -u _i x. ( %s ` k ) ) = %s' % (FR, htk))], '%s = ( -u _i x. ( %s ` k ) )' % (qk, FR))
    sRq = w.s([zu, one_z, nic, frl, toU(D(w, P1, 'eqeltrd', [frv, vrc], '( %s ` k ) e. CC' % FR), '( %s ` k ) e. CC' % FR), toU(gR, '%s = ( -u _i x. ( %s ` k ) )' % (qk, FR))], 'isermulc2',
              '( %s -> seq 1 ( + , %s ) ~~> ( -u _i x. %s ) )' % (ph, HTq, SRRj))
    SQ = 'sum_ k e. NN %s' % qk
    sq_ = w.s([nnu, one_z, D(w, P1, 'eqidd', [], '%s = %s' % (qk, qk)), qkc, sRq], 'isumclim', '( %s -> %s = ( -u _i x. %s ) )' % (ph, SQ, SRRj))
    qdm = w.s([sRq, rel(HTq, '( -u _i x. %s )' % SRRj)], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, HTq))
    # left: G1 = ( j e. NN |-> HTq ` ( 1 - j ) )
    G1 = '( j e. NN |-> ( %s ` ( 1 - j ) ) )' % HTq
    g1v = w.s([kN, w.s([w.s([w.s([], 'oveq2', '( j = k -> ( 1 - j ) = ( 1 - k ) )')], 'fveq2d', '( j = k -> ( %s ` ( 1 - j ) ) = %s )' % (HTq, q1k)), w.s([], 'eqid', '%s = %s' % (G1, G1)),
                       w.s([], 'fvex', '%s e. _V' % q1k)], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (G1, q1k))], 'syl', '( %s -> ( %s ` k ) = %s )' % (P1, G1, q1k))
    fll = D(w, ph, 'breqtrd', [w.s([nnu, one_z, flv, vlc, cvL], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (ph, FL, SLL)), w.s([csL], 'a1i', '( %s -> %s = %s )' % (ph, SLL, SLLj))],
              'seq 1 ( + , %s ) ~~> %s' % (FL, SLLj))
    gL = D(w, P1, 'eqtrd', [g1v, D(w, P1, 'eqtr4d', [D(w, P1, 'eqcomd', [toq(P1, '( 1 - k )')], '%s = %s' % (q1k, ht1k)),
                                                     D(w, P1, 'eqtrd', [D(w, P1, 'oveq2d', [D(w, P1, 'eqtrd', [flv, vl], '( %s ` k ) = ( _i x. %s )' % (FL, ht1k))], '( -u _i x. ( %s ` k ) ) = ( -u _i x. ( _i x. %s ) )' % (FL, ht1k)),
                                                                        mi(w, P1, ht1k, ht1kc)], '( -u _i x. ( %s ` k ) ) = %s' % (FL, ht1k))], '%s = ( -u _i x. ( %s ` k ) )' % (q1k, FL))],
           '( %s ` k ) = ( -u _i x. ( %s ` k ) )' % (G1, FL))
    sL1 = w.s([zu, one_z, nic, fll, toU(D(w, P1, 'eqeltrd', [flv, vlc], '( %s ` k ) e. CC' % FL), '( %s ` k ) e. CC' % FL), toU(gL, '( %s ` k ) = ( -u _i x. ( %s ` k ) )' % (G1, FL))], 'isermulc2',
              '( %s -> seq 1 ( + , %s ) ~~> ( -u _i x. %s ) )' % (ph, G1, SLLj))
    SQ1 = 'sum_ k e. NN %s' % q1k
    sq1 = w.s([nnu, one_z, g1v, q1kc, sL1], 'isumclim', '( %s -> %s = ( -u _i x. %s ) )' % (ph, SQ1, SLLj))
    g1dm = w.s([sL1, rel(G1, '( -u _i x. %s )' % SLLj)], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, G1))
    # PZH = SQ + SQ1
    srrc = w.s([nnu, one_z, frv, vrc, w.s([], 'x', 'x') if False else conv_j(w.s([cv, w.inst('simpl')], 'syl', '( %s -> seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (ph, VRk)), VRk, FR, 'H', TPN, '1')], 'isumcl', '( %s -> %s e. CC )' % (ph, SRR))
    sllc = w.s([nnu, one_z, flv, vlc, cvL], 'isumcl', '( %s -> %s e. CC )' % (ph, SLL))
    ic = cst(w, ph, 'ax-icn', '_i e. CC'); inz = cst(w, ph, 'ine0', '_i =/= 0')
    X_ = '( %s + %s )' % (SRR, SLL)
    xc = D(w, ph, 'addcld', [srrc, sllc], '%s e. CC' % X_)
    niX = '( -u _i x. %s )' % X_
    ii2 = D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [D(w, ph, 'mulneg2d', [ic, ic], '( _i x. -u _i ) = -u ( _i x. _i )'), D(w, ph, 'negeqd', [cst(w, ph, 'ixi', '( _i x. _i ) = -u 1')], '-u ( _i x. _i ) = -u -u 1')], '( _i x. -u _i ) = -u -u 1'),
                             D(w, ph, 'negnegd', [cst(w, ph, 'ax-1cn', '1 e. CC')], '-u -u 1 = 1')], '( _i x. -u _i ) = 1')
    inix = D(w, ph, 'eqtrd', [D(w, ph, 'eqcomd', [D(w, ph, 'mulassd', [ic, nic, xc], '( ( _i x. -u _i ) x. %s ) = ( _i x. %s )' % (X_, niX))], '( _i x. %s ) = ( ( _i x. -u _i ) x. %s )' % (niX, X_)),
                              D(w, ph, 'eqtrd', [D(w, ph, 'oveq1d', [ii2], '( ( _i x. -u _i ) x. %s ) = ( 1 x. %s )' % (X_, X_)), D(w, ph, 'mullidd', [xc], '( 1 x. %s ) = %s' % (X_, X_))], '( ( _i x. -u _i ) x. %s ) = %s' % (X_, X_))],
             '( _i x. %s ) = %s' % (niX, X_))
    pzx = D(w, ph, 'mulcanad', [pzc, D(w, ph, 'mulcld', [nic, xc], '%s e. CC' % niX), ic, inz, D(w, ph, 'eqtr4d', [ipz, inix], '( _i x. %s ) = ( _i x. %s )' % (PZH, niX))], '%s = %s' % (PZH, niX))
    ad = D(w, ph, 'adddid', [nic, srrc, sllc], '%s = ( ( -u _i x. %s ) + ( -u _i x. %s ) )' % (niX, SRR, SLL))
    sR_ = D(w, ph, 'eqtr4d', [sq_, D(w, ph, 'oveq2d', [w.s([csR], 'a1i', '( %s -> %s = %s )' % (ph, SRR, SRRj))], '( -u _i x. %s ) = ( -u _i x. %s )' % (SRR, SRRj))], '%s = ( -u _i x. %s )' % (SQ, SRR))
    sL_ = D(w, ph, 'eqtr4d', [sq1, D(w, ph, 'oveq2d', [w.s([csL], 'a1i', '( %s -> %s = %s )' % (ph, SLL, SLLj))], '( -u _i x. %s ) = ( -u _i x. %s )' % (SLL, SLLj))], '%s = ( -u _i x. %s )' % (SQ1, SLL))
    pz2 = D(w, ph, 'eqtr4d', [D(w, ph, 'eqtrd', [pzx, ad], '%s = ( ( -u _i x. %s ) + ( -u _i x. %s ) )' % (PZH, SRR, SLL)), D(w, ph, 'oveq12d', [sR_, sL_], '( %s + %s ) = ( ( -u _i x. %s ) + ( -u _i x. %s ) )' % (SQ, SQ1, SRR, SLL))],
            '%s = ( %s + %s )' % (PZH, SQ, SQ1))
    # reindex SQ1 = HTq ` 0 + sum_ k HTq ` -u k
    ip1 = w.s([nnu, one_z, g1v, q1kc, g1dm], 'isum1p', '( %s -> %s = ( ( %s ` 1 ) + sum_ k e. ( ZZ>= ` ( 1 + 1 ) ) %s ) )' % (ph, SQ1, G1, q1k))
    g11 = w.s([w.s([], '1nn', '1 e. NN'), w.s([w.s([w.s([], 'oveq2', '( j = 1 -> ( 1 - j ) = ( 1 - 1 ) )')], 'fveq2d', '( j = 1 -> ( %s ` ( 1 - j ) ) = ( %s ` ( 1 - 1 ) ) )' % (HTq, HTq)),
                                              w.s([], 'eqid', '%s = %s' % (G1, G1)), w.s([], 'fvex', '( %s ` ( 1 - 1 ) ) e. _V' % HTq)], 'fvmpt', '( 1 e. NN -> ( %s ` 1 ) = ( %s ` ( 1 - 1 ) ) )' % (G1, HTq))],
              'ax-mp', '( %s ` 1 ) = ( %s ` ( 1 - 1 ) )' % (G1, HTq))
    g10 = w.s([w.s([g11, w.s([w.s([], '1m1e0', '( 1 - 1 ) = 0')], 'fveq2i', '( %s ` ( 1 - 1 ) ) = ( %s ` 0 )' % (HTq, HTq))], 'eqtri', '( %s ` 1 ) = ( %s ` 0 )' % (G1, HTq))], 'a1i', '( %s -> ( %s ` 1 ) = ( %s ` 0 ) )' % (ph, G1, HTq))
    W2 = '( ZZ>= ` ( 1 + 1 ) )'
    cbs = w.s([w.s([w.s([], 'oveq2', '( k = j -> ( 1 - k ) = ( 1 - j ) )')], 'fveq2d', '( k = j -> %s = ( %s ` ( 1 - j ) ) )' % (q1k, HTq))], 'cbvsumv', 'sum_ k e. %s %s = sum_ j e. %s ( %s ` ( 1 - j ) )' % (W2, q1k, W2, HTq))
    P2 = '( %s /\\ j e. %s )' % (ph, W2)
    def uz2N(A_, v, vin):
        vz = w.s([vin, w.inst('eluzelz')], 'syl', '( %s -> %s e. ZZ )' % (A_, v))
        vge = w.s([vin, w.inst('eluzle')], 'syl', '( %s -> ( 1 + 1 ) <_ %s )' % (A_, v))
        o_ = cst(w, A_, '1re', '1 e. RR'); oo = D(w, A_, 'readdcld', [o_, o_], '( 1 + 1 ) e. RR'); vr_ = D(w, A_, 'zred', [vz], '%s e. RR' % v)
        v1 = D(w, A_, 'ltletrd', [o_, oo, vr_, D(w, A_, 'ltp1d', [o_], '1 < ( 1 + 1 )'), vge], '1 < %s' % v)
        vN = D(w, A_, 'mpbir2and', [vz, D(w, A_, 'lttrd', [cst(w, A_, '0re', '0 e. RR'), o_, vr_, cst(w, A_, '0lt1', '0 < 1'), v1], '0 < %s' % v), cst(w, A_, 'elnnz', '( %s e. NN <-> ( %s e. ZZ /\\ 0 < %s ) )' % (v, v, v))],
               '%s e. NN' % v)
        return vz, vr_, v1, vN
    jin = w.s([], 'simpr', '( %s -> j e. %s )' % (P2, W2))
    _, _, _, jNN = uz2N(P2, 'j', jin)
    q1jc = spec(P2, 'j', jNN, lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (P2, f)))[1]
    Ejk = 'j = ( 1 + k )'
    shf = w.s([w.s([], 'oveq2', '( %s -> ( 1 - j ) = ( 1 - ( 1 + k ) ) )' % Ejk)], 'fveq2d', '( %s -> ( %s ` ( 1 - j ) ) = ( %s ` ( 1 - ( 1 + k ) ) ) )' % (Ejk, HTq, HTq))
    ish = w.s([nnu, w.s([], 'eqid', '%s = %s' % (W2, W2)), shf, one_z, one_z, q1jc], 'isumshft', '( %s -> sum_ j e. %s ( %s ` ( 1 - j ) ) = sum_ k e. NN ( %s ` ( 1 - ( 1 + k ) ) ) )' % (ph, W2, HTq, HTq))
    kc1 = D(w, P1, 'nncnd', [kN], 'k e. CC'); c1_ = cst(w, P1, 'ax-1cn', '1 e. CC')
    omk = D(w, P1, 'eqtrd', [D(w, P1, 'eqcomd', [D(w, P1, 'negsubdi2d', [D(w, P1, 'addcld', [c1_, kc1], '( 1 + k ) e. CC'), c1_], '-u ( ( 1 + k ) - 1 ) = ( 1 - ( 1 + k ) )')], '( 1 - ( 1 + k ) ) = -u ( ( 1 + k ) - 1 )'),
                             D(w, P1, 'negeqd', [D(w, P1, 'pncan2d', [c1_, kc1], '( ( 1 + k ) - 1 ) = k')], '-u ( ( 1 + k ) - 1 ) = -u k')], '( 1 - ( 1 + k ) ) = -u k')
    SQM = 'sum_ k e. NN ( %s ` -u k )' % HTq
    ish2 = D(w, ph, 'eqtrd', [ish, w.s([D(w, P1, 'fveq2d', [omk], '( %s ` ( 1 - ( 1 + k ) ) ) = ( %s ` -u k )' % (HTq, HTq))], 'sumeq2dv', '( %s -> sum_ k e. NN ( %s ` ( 1 - ( 1 + k ) ) ) = %s )' % (ph, HTq, SQM))],
             'sum_ j e. %s ( %s ` ( 1 - j ) ) = %s' % (W2, HTq, SQM))
    Q0 = '( %s ` 0 )' % HTq
    sq1r = D(w, ph, 'eqtrd', [ip1, D(w, ph, 'oveq12d', [g10, D(w, ph, 'eqtrd', [w.s([cbs], 'a1i', '( %s -> sum_ k e. %s %s = sum_ j e. %s ( %s ` ( 1 - j ) ) )' % (ph, W2, q1k, W2, HTq)), ish2], 'sum_ k e. %s %s = %s' % (W2, q1k, SQM))],
                                        '( ( %s ` 1 ) + sum_ k e. %s %s ) = ( %s + %s )' % (G1, W2, q1k, Q0, SQM))], '%s = ( %s + %s )' % (SQ1, Q0, SQM))
    # convergence of seq of HTq ` -u j
    Gm = '( j e. NN |-> ( %s ` -u j ) )' % HTq
    gmv = w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % Gm)
    LZ = '( ~~> ` seq ( 1 + 1 ) ( + , %s ) )' % G1
    ise = w.s([gmv], 'isershft', '( ( 1 e. ZZ /\\ 1 e. ZZ ) -> ( seq 1 ( + , %s ) ~~> %s <-> seq ( 1 + 1 ) ( + , ( %s shift 1 ) ) ~~> %s ) )' % (Gm, LZ, Gm, LZ))
    P3 = '( %s /\\ k e. %s )' % (ph, W2)
    k3in = w.s([], 'simpr', '( %s -> k e. %s )' % (P3, W2))
    k3z, k3r, k31, k3N = uz2N(P3, 'k', k3in)
    k3c = D(w, P3, 'zcnd', [k3z], 'k e. CC')
    sv_ = w.s([cst(w, P3, 'ax-1cn', '1 e. CC'), k3c, w.s([gmv], 'shftval', '( ( 1 e. CC /\\ k e. CC ) -> ( ( %s shift 1 ) ` k ) = ( %s ` ( k - 1 ) ) )' % (Gm, Gm))], 'syl2anc', '( %s -> ( ( %s shift 1 ) ` k ) = ( %s ` ( k - 1 ) ) )' % (P3, Gm, Gm))
    km1N = D(w, P3, 'mpbir2and', [D(w, P3, 'zsubcld', [k3z, cst(w, P3, '1z', '1 e. ZZ')], '( k - 1 ) e. ZZ'),
                                  D(w, P3, 'mpbid', [k31, D(w, P3, 'posdifd', [cst(w, P3, '1re', '1 e. RR'), k3r], '( 1 < k <-> 0 < ( k - 1 ) )')], '0 < ( k - 1 )'),
                                  cst(w, P3, 'elnnz', '( ( k - 1 ) e. NN <-> ( ( k - 1 ) e. ZZ /\\ 0 < ( k - 1 ) ) )')], '( k - 1 ) e. NN')
    gmk = w.s([km1N, w.s([w.s([w.s([], 'negeq', '( j = ( k - 1 ) -> -u j = -u ( k - 1 ) )')], 'fveq2d', '( j = ( k - 1 ) -> ( %s ` -u j ) = ( %s ` -u ( k - 1 ) ) )' % (HTq, HTq)), w.s([], 'eqid', '%s = %s' % (Gm, Gm)),
                          w.s([], 'fvex', '( %s ` -u ( k - 1 ) ) e. _V' % HTq)], 'fvmpt', '( ( k - 1 ) e. NN -> ( %s ` ( k - 1 ) ) = ( %s ` -u ( k - 1 ) ) )' % (Gm, HTq))], 'syl', '( %s -> ( %s ` ( k - 1 ) ) = ( %s ` -u ( k - 1 ) ) )' % (P3, Gm, HTq))
    ng1 = D(w, P3, 'negsubdi2d', [k3c, cst(w, P3, 'ax-1cn', '1 e. CC')], '-u ( k - 1 ) = ( 1 - k )')
    g1k3 = w.s([k3N, w.s([w.s([w.s([], 'oveq2', '( j = k -> ( 1 - j ) = ( 1 - k ) )')], 'fveq2d', '( j = k -> ( %s ` ( 1 - j ) ) = %s )' % (HTq, q1k)), w.s([], 'eqid', '%s = %s' % (G1, G1)),
                         w.s([], 'fvex', '%s e. _V' % q1k)], 'fvmpt', '( k e. NN -> ( %s ` k ) = %s )' % (G1, q1k))], 'syl', '( %s -> ( %s ` k ) = %s )' % (P3, G1, q1k))
    fe = D(w, P3, 'eqtr4d', [D(w, P3, 'eqtrd', [sv_, D(w, P3, 'eqtrd', [gmk, D(w, P3, 'fveq2d', [ng1], '( %s ` -u ( k - 1 ) ) = %s' % (HTq, q1k))], '( %s ` ( k - 1 ) ) = %s' % (Gm, q1k))],
                                   '( ( %s shift 1 ) ` k ) = %s' % (Gm, q1k)), g1k3], '( ( %s shift 1 ) ` k ) = ( %s ` k )' % (Gm, G1))
    sfe = w.s([D(w, ph, 'peano2zd', [one_z], '( 1 + 1 ) e. ZZ'), fe], 'seqfeq', '( %s -> seq ( 1 + 1 ) ( + , ( %s shift 1 ) ) = seq ( 1 + 1 ) ( + , %s ) )' % (ph, Gm, G1))
    two_in = D(w, ph, 'eleqtrd', [w.s([w.s([w.s([], '1nn', '1 e. NN'), w.inst('peano2nn')], 'ax-mp', '( 1 + 1 ) e. NN')], 'a1i', '( %s -> ( 1 + 1 ) e. NN )' % ph), cst(w, ph, 'nnuz', 'NN = ( ZZ>= ` 1 )')], '( 1 + 1 ) e. ( ZZ>= ` 1 )')
    g1U = toU(D(w, P1, 'eqeltrd', [g1v, q1kc], '( %s ` k ) e. CC' % G1), '( %s ` k ) e. CC' % G1)
    ie = w.s([zu, two_in, g1U], 'iserex', '( %s -> ( seq 1 ( + , %s ) e. dom ~~> <-> seq ( 1 + 1 ) ( + , %s ) e. dom ~~> ) )' % (ph, G1, G1))
    s2dm = D(w, ph, 'mpbid', [g1dm, ie], 'seq ( 1 + 1 ) ( + , %s ) e. dom ~~>' % G1)
    s2l = w.s([s2dm, w.s([], 'climdm', '( seq ( 1 + 1 ) ( + , %s ) e. dom ~~> <-> seq ( 1 + 1 ) ( + , %s ) ~~> %s )' % (G1, G1, LZ))], 'sylib', '( %s -> seq ( 1 + 1 ) ( + , %s ) ~~> %s )' % (ph, G1, LZ))
    s2l2 = D(w, ph, 'mpbird', [s2l, D(w, ph, 'breq1d', [sfe], '( seq ( 1 + 1 ) ( + , ( %s shift 1 ) ) ~~> %s <-> seq ( 1 + 1 ) ( + , %s ) ~~> %s )' % (Gm, LZ, G1, LZ))],
             'seq ( 1 + 1 ) ( + , ( %s shift 1 ) ) ~~> %s' % (Gm, LZ))
    isea = w.s([w.s([w.s([w.s([], '1z', '1 e. ZZ'), w.s([], '1z', '1 e. ZZ')], 'pm3.2i', '( 1 e. ZZ /\\ 1 e. ZZ )'), ise], 'ax-mp', '( seq 1 ( + , %s ) ~~> %s <-> seq ( 1 + 1 ) ( + , ( %s shift 1 ) ) ~~> %s )' % (Gm, LZ, Gm, LZ))],
               'a1i', '( %s -> ( seq 1 ( + , %s ) ~~> %s <-> seq ( 1 + 1 ) ( + , ( %s shift 1 ) ) ~~> %s ) )' % (ph, Gm, LZ, Gm, LZ))
    gml = D(w, ph, 'mpbird', [s2l2, isea], 'seq 1 ( + , %s ) ~~> %s' % (Gm, LZ))
    gmdm = w.s([gml, rel(Gm, LZ)], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, Gm))
    # isumadd over n
    P4 = '( %s /\\ n e. NN )' % ph
    nN4 = w.s([], 'simpr', '( %s -> n e. NN )' % P4)
    l4 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (P4, f))
    qnc = spec(P4, 'n', nN4, l4)[0]
    n1N = D(w, P4, 'peano2nnd', [nN4], '( n + 1 ) e. NN')
    qm0 = spec(P4, '( n + 1 )', n1N, l4)[1]
    nc4 = D(w, P4, 'nncnd', [nN4], 'n e. CC')
    on = D(w, P4, 'eqtrd', [D(w, P4, 'oveq2d', [D(w, P4, 'addcomd', [nc4, cst(w, P4, 'ax-1cn', '1 e. CC')], '( n + 1 ) = ( 1 + n )')], '( 1 - ( n + 1 ) ) = ( 1 - ( 1 + n ) )'),
                            D(w, P4, 'eqtrd', [D(w, P4, 'eqcomd', [D(w, P4, 'negsubdi2d', [D(w, P4, 'addcld', [cst(w, P4, 'ax-1cn', '1 e. CC'), nc4], '( 1 + n ) e. CC'), cst(w, P4, 'ax-1cn', '1 e. CC')],
                                                                    '-u ( ( 1 + n ) - 1 ) = ( 1 - ( 1 + n ) )')], '( 1 - ( 1 + n ) ) = -u ( ( 1 + n ) - 1 )'),
                                               D(w, P4, 'negeqd', [D(w, P4, 'pncan2d', [cst(w, P4, 'ax-1cn', '1 e. CC'), nc4], '( ( 1 + n ) - 1 ) = n')], '-u ( ( 1 + n ) - 1 ) = -u n')], '( 1 - ( 1 + n ) ) = -u n')],
            '( 1 - ( n + 1 ) ) = -u n')
    qmnc = D(w, P4, 'eqeltrrd', [D(w, P4, 'fveq2d', [on], '( %s ` ( 1 - ( n + 1 ) ) ) = ( %s ` -u n )' % (HTq, HTq)), qm0], '( %s ` -u n ) e. CC' % HTq)
    gmn = w.s([nN4, w.s([w.s([w.s([], 'negeq', '( j = n -> -u j = -u n )')], 'fveq2d', '( j = n -> ( %s ` -u j ) = ( %s ` -u n ) )' % (HTq, HTq)), w.s([], 'eqid', '%s = %s' % (Gm, Gm)), w.s([], 'fvex', '( %s ` -u n ) e. _V' % HTq)],
                         'fvmpt', '( n e. NN -> ( %s ` n ) = ( %s ` -u n ) )' % (Gm, HTq))], 'syl', '( %s -> ( %s ` n ) = ( %s ` -u n ) )' % (P4, Gm, HTq))
    iad = w.s([nnu, one_z, D(w, P4, 'eqidd', [], '( %s ` n ) = ( %s ` n )' % (HTq, HTq)), qnc, gmn, qmnc, qdm, gmdm], 'isumadd',
              '( %s -> sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = ( sum_ n e. NN ( %s ` n ) + sum_ n e. NN ( %s ` -u n ) ) )' % (ph, HTq, HTq, HTq, HTq))
    cb1 = w.s([w.s([], 'fveq2', '( k = n -> %s = ( %s ` n ) )' % (qk, HTq))], 'cbvsumv', '%s = sum_ n e. NN ( %s ` n )' % (SQ, HTq))
    cb2 = w.s([w.s([w.s([], 'negeq', '( k = n -> -u k = -u n )')], 'fveq2d', '( k = n -> ( %s ` -u k ) = ( %s ` -u n ) )' % (HTq, HTq))], 'cbvsumv', '%s = sum_ n e. NN ( %s ` -u n )' % (SQM, HTq))
    iad2 = D(w, ph, 'eqtr4d', [iad, D(w, ph, 'oveq12d', [w.s([cb1], 'a1i', '( %s -> %s = sum_ n e. NN ( %s ` n ) )' % (ph, SQ, HTq)), w.s([cb2], 'a1i', '( %s -> %s = sum_ n e. NN ( %s ` -u n ) )' % (ph, SQM, HTq))],
                                         '( %s + %s ) = ( sum_ n e. NN ( %s ` n ) + sum_ n e. NN ( %s ` -u n ) )' % (SQ, SQM, HTq, HTq))], 'sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = ( %s + %s )' % (HTq, HTq, SQ, SQM))
    # memberships
    q10 = spec(ph, '1', cst(w, ph, '1nn', '1 e. NN'), lambda st, f: st)[1]
    q0c = D(w, ph, 'eqeltrd', [D(w, ph, 'eqcomd', [D(w, ph, 'fveq2d', [cst(w, ph, '1m1e0', '( 1 - 1 ) = 0')], '( %s ` ( 1 - 1 ) ) = %s' % (HTq, Q0))], '%s = ( %s ` ( 1 - 1 ) )' % (Q0, HTq)), q10], '%s e. CC' % Q0)
    sqc = w.s([nnu, one_z, D(w, P1, 'eqidd', [], '%s = %s' % (qk, qk)), qkc, qdm], 'isumcl', '( %s -> %s e. CC )' % (ph, SQ))
    sqmn = w.s([nnu, one_z, gmn, qmnc, gmdm], 'isumcl', '( %s -> sum_ n e. NN ( %s ` -u n ) e. CC )' % (ph, HTq))
    sqmc = D(w, ph, 'eqeltrd', [w.s([cb2], 'a1i', '( %s -> %s = sum_ n e. NN ( %s ` -u n ) )' % (ph, SQM, HTq)), sqmn], '%s e. CC' % SQM)
    # PZH = SQ + ( Q0 + SQM ) ; PZ(HT) = Q0 + sum ( .. ) in HTq form
    fin1 = D(w, ph, 'eqtrd', [pz2, D(w, ph, 'oveq2d', [sq1r], '( %s + %s ) = ( %s + ( %s + %s ) )' % (SQ, SQ1, SQ, Q0, SQM))], '%s = ( %s + ( %s + %s ) )' % (PZH, SQ, Q0, SQM))
    PZq = '( %s + sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) )' % (Q0, HTq, HTq)
    pzq = D(w, ph, 'oveq12d', [toq(ph, '0'), w.s([D(w, P4, 'oveq12d', [toq(P4, 'n'), toq(P4, '-u n')], '( ( %s ` n ) + ( %s ` -u n ) ) = ( ( %s ` n ) + ( %s ` -u n ) )' % (HT, HT, HTq, HTq))], 'sumeq2dv',
                                                 '( %s -> sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) )' % (ph, HT, HT, HTq, HTq))],
              '%s = %s' % (PZ(HT), PZq))
    r1 = D(w, ph, 'oveq2d', [iad2], '%s = ( %s + ( %s + %s ) )' % (PZq, Q0, SQ, SQM))
    r2 = D(w, ph, 'add12d', [q0c, sqc, sqmc], '( %s + ( %s + %s ) ) = ( %s + ( %s + %s ) )' % (Q0, SQ, SQM, SQ, Q0, SQM))
    tgt = chain_eq(w, ph, PZ(HT), [(pzq, PZq), (r1, '( %s + ( %s + %s ) )' % (Q0, SQ, SQM)), (r2, '( %s + ( %s + %s ) )' % (SQ, Q0, SQM))])
    w.qed([fin1, tgt], 'eqtr4d', S['zl3wpois'])
    go(w, only)


# ---------------------------------------------------------------- zl3pois
if __name__ == '__main__' and (not only or 'zl3pois' in only):
    w = W('zl3pois', 'Poisson summation for an entire function decaying like ` 2 ^ -| Re z | ` on the strip ` | Im z | <_ 1 ` ( Mathlib ` Real.tsum_eq_tsum_fourierIntegral ` ).')
    ph, concl = ante_of(S['zl3pois'])
    HOLF = '( F e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D F ) )'
    FDEC = 'A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( F ` z ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) )'
    assert ph == '( %s /\\ ( K e. RR+ /\\ %s ) )' % (HOLF, FDEC)
    hf = w.s([], 'simpl', '( %s -> %s )' % (ph, HOLF))
    kf = w.s([], 'simpr', '( %s -> ( K e. RR+ /\\ %s ) )' % (ph, FDEC))
    krp = w.s([kf, w.inst('simpl')], 'syl', '( %s -> K e. RR+ )' % ph); fdec = w.s([kf, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, FDEC))
    fcn = w.s([hf, w.inst('simpl')], 'syl', '( %s -> F e. ( CC -cn-> CC ) )' % ph)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : CC --> CC )' % ph)
    Hd = '( w e. CC |-> ( F ` ( -u _i x. w ) ) )'
    ARG = '( -u _i x. w )'
    # derivative of Hd
    A1 = '( %s /\\ w e. CC )' % ph
    A2 = '( %s /\\ b e. CC )' % ph
    ce = cst(w, ph, 'cnelprrecn', 'CC e. { RR , CC }')
    wc = w.s([], 'simpr', '( %s -> w e. CC )' % A1)
    nic = D(w, ph, 'negcld', [cst(w, ph, 'ax-icn', '_i e. CC')], '-u _i e. CC')
    did = w.s([ce], 'dvmptid', '( %s -> ( CC _D ( w e. CC |-> w ) ) = ( w e. CC |-> 1 ) )' % ph)
    dcm = w.s([ce, wc, cst(w, A1, 'ax-1cn', '1 e. CC'), did, nic], 'dvmptcmul', '( %s -> ( CC _D ( w e. CC |-> %s ) ) = ( w e. CC |-> ( -u _i x. 1 ) ) )' % (ph, ARG))
    argc = D(w, A1, 'mulcld', [w.s([nic], 'adantr', '( %s -> -u _i e. CC )' % A1), wc], '%s e. CC' % ARG)
    n1c = D(w, A1, 'mulcld', [w.s([nic], 'adantr', '( %s -> -u _i e. CC )' % A1), cst(w, A1, 'ax-1cn', '1 e. CC')], '( -u _i x. 1 ) e. CC')
    zc = w.s([], 'simpr', '( %s -> b e. CC )' % A2)
    fz = D(w, A2, 'ffvelcdmd', [w.s([ff], 'adantr', '( %s -> F : CC --> CC )' % A2), zc], '( F ` b ) e. CC')
    dff = w.s([hf, w.inst('holf')], 'syl', '( %s -> ( CC _D F ) : CC --> CC )' % ph)
    dfz = D(w, A2, 'ffvelcdmd', [w.s([dff], 'adantr', '( %s -> ( CC _D F ) : CC --> CC )' % A2), zc], '( ( CC _D F ) ` b ) e. CC')
    hdv0 = w.s([hf, w.inst('holdv')], 'syl', '( %s -> ( CC _D ( z e. CC |-> ( F ` z ) ) ) = ( z e. CC |-> ( ( CC _D F ) ` z ) ) )' % ph)
    cb1 = w.s([w.s([], 'fveq2', '( z = b -> ( F ` z ) = ( F ` b ) )')], 'cbvmptv', '( z e. CC |-> ( F ` z ) ) = ( b e. CC |-> ( F ` b ) )')
    cb2 = w.s([w.s([], 'fveq2', '( z = b -> ( ( CC _D F ) ` z ) = ( ( CC _D F ) ` b ) )')], 'cbvmptv', '( z e. CC |-> ( ( CC _D F ) ` z ) ) = ( b e. CC |-> ( ( CC _D F ) ` b ) )')
    hdv = D(w, ph, 'eqtr3d', [D(w, ph, 'oveq2d', [w.s([cb1], 'a1i', '( %s -> ( z e. CC |-> ( F ` z ) ) = ( b e. CC |-> ( F ` b ) ) )' % ph)],
                                                 '( CC _D ( z e. CC |-> ( F ` z ) ) ) = ( CC _D ( b e. CC |-> ( F ` b ) ) )'),
                              D(w, ph, 'eqtrd', [hdv0, w.s([cb2], 'a1i', '( %s -> ( z e. CC |-> ( ( CC _D F ) ` z ) ) = ( b e. CC |-> ( ( CC _D F ) ` b ) ) )' % ph)],
                                '( CC _D ( z e. CC |-> ( F ` z ) ) ) = ( b e. CC |-> ( ( CC _D F ) ` b ) )')],
              '( CC _D ( b e. CC |-> ( F ` b ) ) ) = ( b e. CC |-> ( ( CC _D F ) ` b ) )')
    sty = w.s([], 'fveq2', '( b = %s -> ( F ` b ) = ( F ` %s ) )' % (ARG, ARG))
    sty2 = w.s([], 'fveq2', '( b = %s -> ( ( CC _D F ) ` b ) = ( ( CC _D F ) ` %s ) )' % (ARG, ARG))
    DV = '( w e. CC |-> ( ( ( CC _D F ) ` %s ) x. ( -u _i x. 1 ) ) )' % ARG
    dco = w.s([ce, ce, argc, n1c, fz, dfz, dcm, hdv, sty, sty2], 'dvmptco', '( %s -> ( CC _D %s ) = %s )' % (ph, Hd, DV))
    dvc = D(w, A1, 'mulcld', [D(w, A1, 'ffvelcdmd', [w.s([dff], 'adantr', '( %s -> ( CC _D F ) : CC --> CC )' % A1), argc], '( ( CC _D F ) ` %s ) e. CC' % ARG), n1c], '( ( ( CC _D F ) ` %s ) x. ( -u _i x. 1 ) ) e. CC' % ARG)
    dm = D(w, ph, 'eqtrd', [D(w, ph, 'dmeqd', [dco], 'dom ( CC _D %s ) = dom %s' % (Hd, DV)), w.s([w.s([], 'eqid', '%s = %s' % (DV, DV)), dvc], 'dmmptd', '( %s -> dom %s = CC )' % (ph, DV))], 'dom ( CC _D %s ) = CC' % Hd)
    hdf = w.s([D(w, A1, 'ffvelcdmd', [w.s([ff], 'adantr', '( %s -> F : CC --> CC )' % A1), argc], '( F ` %s ) e. CC' % ARG), w.s([], 'eqid', '%s = %s' % (Hd, Hd))], 'fmptd', '( %s -> %s : CC --> CC )' % (ph, Hd))
    ss = cst(w, ph, 'ssid', 'CC C_ CC')
    hcn = w.s([w.s([ss, hdf, ss], '3jca', '( %s -> ( CC C_ CC /\\ %s : CC --> CC /\\ CC C_ CC ) )' % (ph, Hd)), dm, w.inst('dvcn')], 'syl2anc', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, Hd))
    hent = D(w, ph, 'jca', [hcn, D(w, ph, 'eqimssd', [D(w, ph, 'eqcomd', [dm], 'CC = dom ( CC _D %s )' % Hd)], 'CC C_ dom ( CC _D %s )' % Hd)], '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (Hd, Hd))
    # decay of Hd
    A3 = '( %s /\\ c e. CC )' % ph
    cc_ = w.s([], 'simpr', '( %s -> c e. CC )' % A3)
    nic3 = D(w, A3, 'negcld', [cst(w, A3, 'ax-icn', '_i e. CC')], '-u _i e. CC')
    P = '( -u _i x. c )'
    pc = D(w, A3, 'mulcld', [nic3, cc_], '%s e. CC' % P)
    hv = w.s([cc_, w.s([w.s([w.s([], 'oveq2', '( w = c -> %s = %s )' % (ARG, P))], 'fveq2d', '( w = c -> ( F ` %s ) = ( F ` %s ) )' % (ARG, P)), w.s([], 'eqid', '%s = %s' % (Hd, Hd)), w.s([], 'fvex', '( F ` %s ) e. _V' % P)],
                       'fvmpt', '( c e. CC -> ( %s ` c ) = ( F ` %s ) )' % (Hd, P))], 'syl', '( %s -> ( %s ` c ) = ( F ` %s ) )' % (A3, Hd, P))
    rep = w.s([cc_, w.inst('imre')], 'syl', '( %s -> ( Im ` c ) = ( Re ` %s ) )' % (A3, P))
    ic3 = cst(w, A3, 'ax-icn', '_i e. CC')
    m12 = w.s([ic3, cc_, w.inst('mulneg12')], 'syl2anc', '( %s -> %s = ( _i x. -u c ) )' % (A3, P))
    imp = D(w, A3, 'eqtrd', [D(w, A3, 'fveq2d', [m12], '( Im ` %s ) = ( Im ` ( _i x. -u c ) )' % P),
                             D(w, A3, 'eqtrd', [D(w, A3, 'eqcomd', [w.s([D(w, A3, 'negcld', [cc_], '-u c e. CC'), w.inst('reim')], 'syl', '( %s -> ( Re ` -u c ) = ( Im ` ( _i x. -u c ) ) )' % A3)],
                                                  '( Im ` ( _i x. -u c ) ) = ( Re ` -u c )'), w.s([cc_, w.inst('reneg')], 'syl', '( %s -> ( Re ` -u c ) = -u ( Re ` c ) )' % A3)], '( Im ` ( _i x. -u c ) ) = -u ( Re ` c )')],
            '( Im ` %s ) = -u ( Re ` c )' % P)
    aim = D(w, A3, 'eqtrd', [D(w, A3, 'fveq2d', [imp], '( abs ` ( Im ` %s ) ) = ( abs ` -u ( Re ` c ) )' % P), D(w, A3, 'absnegd', [D(w, A3, 'recnd', [D(w, A3, 'recld', [cc_], '( Re ` c ) e. RR')], '( Re ` c ) e. CC')],
                                                                                                                    '( abs ` -u ( Re ` c ) ) = ( abs ` ( Re ` c ) )')], '( abs ` ( Im ` %s ) ) = ( abs ` ( Re ` c ) )' % P)
    body = lambda X: '( ( abs ` ( Im ` %s ) ) <_ 1 -> ( abs ` ( F ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Re ` %s ) ) ) ) )' % (X, X, X)
    E = 'z = %s' % P
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    beq = D(w, E, 'imbi12d', [D(w, E, 'breq1d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Im ` z ) = ( Im ` %s )' % P)], '( abs ` ( Im ` z ) ) = ( abs ` ( Im ` %s ) )' % P)], '( ( abs ` ( Im ` z ) ) <_ 1 <-> ( abs ` ( Im ` %s ) ) <_ 1 )' % P),
                              D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( F ` z ) = ( F ` %s )' % P)], '( abs ` ( F ` z ) ) = ( abs ` ( F ` %s ) )' % P),
                                                  D(w, E, 'oveq2d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'fveq2d', [D(w, E, 'fveq2d', [e], '( Re ` z ) = ( Re ` %s )' % P)], '( abs ` ( Re ` z ) ) = ( abs ` ( Re ` %s ) )' % P)],
                                                                                                '-u ( abs ` ( Re ` z ) ) = -u ( abs ` ( Re ` %s ) )' % P)], '( 2 ^c -u ( abs ` ( Re ` z ) ) ) = ( 2 ^c -u ( abs ` ( Re ` %s ) ) )' % P)],
                                                    '( K x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) = ( K x. ( 2 ^c -u ( abs ` ( Re ` %s ) ) ) )' % P)],
                                '( ( abs ` ( F ` z ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) <-> ( abs ` ( F ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Re ` %s ) ) ) ) )' % (P, P))],
              '( %s <-> %s )' % (body('z'), body(P)))
    fp = w.s([pc, w.s([fdec], 'adantr', '( %s -> %s )' % (A3, FDEC)), w.s([beq], 'rspcv', '( %s e. CC -> ( %s -> %s ) )' % (P, FDEC, body(P)))], 'sylc', '( %s -> %s )' % (A3, body(P)))
    A4 = '( %s /\\ ( abs ` ( Re ` c ) ) <_ 1 )' % A3
    l4 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (A4, f))
    i1 = D(w, A4, 'eqbrtrd', [l4(aim, '( abs ` ( Im ` %s ) ) = ( abs ` ( Re ` c ) )' % P), w.s([], 'simpr', '( %s -> ( abs ` ( Re ` c ) ) <_ 1 )' % A4)], '( abs ` ( Im ` %s ) ) <_ 1' % P)
    fb = D(w, A4, 'mpd', [i1, l4(fp, body(P))], '( abs ` ( F ` %s ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Re ` %s ) ) ) )' % (P, P))
    hb = D(w, A4, 'breqtrd', [D(w, A4, 'eqbrtrd', [D(w, A4, 'fveq2d', [l4(hv, '( %s ` c ) = ( F ` %s )' % (Hd, P))], '( abs ` ( %s ` c ) ) = ( abs ` ( F ` %s ) )' % (Hd, P)), fb],
                                   '( abs ` ( %s ` c ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Re ` %s ) ) ) )' % (Hd, P)),
                              D(w, A4, 'oveq2d', [D(w, A4, 'oveq2d', [D(w, A4, 'negeqd', [D(w, A4, 'fveq2d', [D(w, A4, 'eqcomd', [l4(rep, '( Im ` c ) = ( Re ` %s )' % P)], '( Re ` %s ) = ( Im ` c )' % P)],
                                                                                           '( abs ` ( Re ` %s ) ) = ( abs ` ( Im ` c ) )' % P)], '-u ( abs ` ( Re ` %s ) ) = -u ( abs ` ( Im ` c ) )' % P)],
                                                                    '( 2 ^c -u ( abs ` ( Re ` %s ) ) ) = ( 2 ^c -u ( abs ` ( Im ` c ) ) )' % P)],
                                '( K x. ( 2 ^c -u ( abs ` ( Re ` %s ) ) ) ) = ( K x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) )' % P)],
            '( abs ` ( %s ` c ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) )' % Hd)
    hdec = w.s([w.s([hb], 'ex', '( %s -> ( ( abs ` ( Re ` c ) ) <_ 1 -> ( abs ` ( %s ` c ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) ) )' % (A3, Hd))], 'ralrimiva',
               '( %s -> A. c e. CC ( ( abs ` ( Re ` c ) ) <_ 1 -> ( abs ` ( %s ` c ) ) <_ ( K x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) ) )' % (ph, Hd))
    # zl3wpois at H := Hd
    subH = lambda t: ' '.join(Hd if x == 'H' else x for x in t.split())
    HC = subH(HCTX)
    wp = w.s([D(w, ph, 'jca', [hent, D(w, ph, 'jca', [krp, hdec], subH('( K e. RR+ /\\ %s )' % HDEC))], HC), w.inst('zl3wpois')], 'syl', '( %s -> %s )' % (ph, subH(S['zl3wpois'][len(HCTX) + 6:-2])))
    # Hd ( i X ) = F ( X )
    def hix(A_, X, xc):
        ic_ = cst(w, A_, 'ax-icn', '_i e. CC')
        ixc = D(w, A_, 'mulcld', [ic_, xc], '( _i x. %s ) e. CC' % X)
        v = w.s([ixc, w.s([w.s([w.s([], 'oveq2', '( w = ( _i x. %s ) -> %s = ( -u _i x. ( _i x. %s ) ) )' % (X, ARG, X))], 'fveq2d', '( w = ( _i x. %s ) -> ( F ` %s ) = ( F ` ( -u _i x. ( _i x. %s ) ) ) )' % (X, ARG, X)),
                           w.s([], 'eqid', '%s = %s' % (Hd, Hd)), w.s([], 'fvex', '( F ` ( -u _i x. ( _i x. %s ) ) ) e. _V' % X)], 'fvmpt', '( ( _i x. %s ) e. CC -> ( %s ` ( _i x. %s ) ) = ( F ` ( -u _i x. ( _i x. %s ) ) ) )' % (X, Hd, X, X))],
                'syl', '( %s -> ( %s ` ( _i x. %s ) ) = ( F ` ( -u _i x. ( _i x. %s ) ) ) )' % (A_, Hd, X, X))
        return D(w, A_, 'eqtrd', [v, D(w, A_, 'fveq2d', [mi(w, A_, X, xc)], '( F ` ( -u _i x. ( _i x. %s ) ) ) = ( F ` %s )' % (X, X))], '( %s ` ( _i x. %s ) ) = ( F ` %s )' % (Hd, X, X))
    h0 = hix(ph, '0', cst(w, ph, '0cn', '0 e. CC'))
    P5 = '( %s /\\ n e. NN )' % ph
    nc5 = D(w, P5, 'nncnd', [w.s([], 'simpr', '( %s -> n e. NN )' % P5)], 'n e. CC')
    hn = hix(P5, 'n', nc5); hmn = hix(P5, '-u n', D(w, P5, 'negcld', [nc5], '-u n e. CC'))
    lhs = D(w, ph, 'oveq12d', [h0, w.s([D(w, P5, 'oveq12d', [hn, hmn], '( ( %s ` ( _i x. n ) ) + ( %s ` ( _i x. -u n ) ) ) = ( ( F ` n ) + ( F ` -u n ) )' % (Hd, Hd))], 'sumeq2dv',
                                            '( %s -> sum_ n e. NN ( ( %s ` ( _i x. n ) ) + ( %s ` ( _i x. -u n ) ) ) = sum_ n e. NN ( ( F ` n ) + ( F ` -u n ) ) )' % (ph, Hd, Hd))],
            '%s = %s' % (subH(PZH), PZ('F')))
    # HT at Hd equals FT
    HTd = subH(HT)
    A6 = '( ( ( %s /\\ k e. ZZ ) /\\ t e. RR+ ) /\\ x e. ( -u t (,) t ) )' % ph
    xc6 = D(w, A6, 'recnd', [w.s([w.s([], 'simpr', '( %s -> x e. ( -u t (,) t ) )' % A6), w.inst('elioore')], 'syl', '( %s -> x e. RR )' % A6)], 'x e. CC')
    hx6 = hix(A6, 'x', xc6)
    INT = lambda G: '( ( %s ) x. ( exp ` -u ( %s x. ( k x. x ) ) ) )' % (G, TIP)
    ie = D(w, A6, 'oveq1d', [hx6], '( ( %s ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( k x. x ) ) ) ) = ( ( F ` x ) x. ( exp ` -u ( %s x. ( k x. x ) ) ) )' % (Hd, TIP, TIP))
    I1 = 'S. ( -u t (,) t ) ( ( %s ` ( _i x. x ) ) x. ( exp ` -u ( %s x. ( k x. x ) ) ) ) _d x' % (Hd, TIP)
    I2 = 'S. ( -u t (,) t ) ( ( F ` x ) x. ( exp ` -u ( %s x. ( k x. x ) ) ) ) _d x' % TIP
    ig = w.s([ie], 'itgeq2dv', '( ( ( %s /\\ k e. ZZ ) /\\ t e. RR+ ) -> %s = %s )' % (ph, I1, I2))
    mt = w.s([ig], 'mpteq2dva', '( ( %s /\\ k e. ZZ ) -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s ) )' % (ph, I1, I2))
    fk = D(w, '( %s /\\ k e. ZZ )' % ph, 'fveq2d', [mt], '( ~~>r ` ( t e. RR+ |-> %s ) ) = ( ~~>r ` ( t e. RR+ |-> %s ) )' % (I1, I2))
    hteq = w.s([fk], 'mpteq2dva', '( %s -> %s = %s )' % (ph, HTd, FT))
    rhs = D(w, ph, 'oveq12d', [D(w, ph, 'fveq1d', [hteq], '( %s ` 0 ) = ( %s ` 0 )' % (HTd, FT)),
                               w.s([D(w, P5, 'oveq12d', [D(w, P5, 'fveq1d', [w.s([hteq], 'adantr', '( %s -> %s = %s )' % (P5, HTd, FT))], '( %s ` n ) = ( %s ` n )' % (HTd, FT)),
                                                         D(w, P5, 'fveq1d', [w.s([hteq], 'adantr', '( %s -> %s = %s )' % (P5, HTd, FT))], '( %s ` -u n ) = ( %s ` -u n )' % (HTd, FT))],
                                     '( ( %s ` n ) + ( %s ` -u n ) ) = ( ( %s ` n ) + ( %s ` -u n ) )' % (HTd, HTd, FT, FT))], 'sumeq2dv',
                                   '( %s -> sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) = sum_ n e. NN ( ( %s ` n ) + ( %s ` -u n ) ) )' % (ph, HTd, HTd, FT, FT))],
              '%s = %s' % (PZ(HTd), PZ(FT)))
    w.qed([lhs, wp, rhs], '3eqtr3d', S['zl3pois'])
    go(w, only)
