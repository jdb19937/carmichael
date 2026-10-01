"""Sortie MV, section H: kernel_mvt itself (mvkmvt): mvkm1 at R = n, mvfej per pair, mvlim."""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from mvlib import *
from mv_g import hkat, HKQ
only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    assert w.lines[-1].split('|- ', 1)[1] == STATEMENTS[w.label], (w.lines[-1], STATEMENTS[w.label])
    bad = checkrefs(w)
    if bad:
        print('UNKNOWN LABELS in %s: %s' % (w.label, bad)); return False
    if os.environ.get('DRY'):
        w.write(); print('WROTE %s (%d steps)' % (w.label, len(w.lines))); return True
    return w.run()


def pairctx(w, ante, allst, extra):
    """closure under ( ( ante /\\ i e. P ) /\\ j e. P ) with C, L at i and j, plus EXTRA {text: (kind, step under ante)}"""
    Ai = '( %s /\\ i e. P )' % ante
    Aij = '( ( %s /\\ i e. P ) /\\ j e. P )' % ante
    ci = hkat(w, Aij, 'i', lift(w, allst, Aij), lift(w, w.s([], 'simpr', '( %s -> i e. P )' % Ai), Aij))
    cj = hkat(w, Aij, 'j', lift(w, allst, Aij), w.s([], 'simpr', '( %s -> j e. P )' % Aij))
    lv = {'( C ` i )': ('CC', ci[0]), '( L ` i )': ('RR', ci[1]), '( C ` j )': ('CC', cj[0]), '( L ` j )': ('RR', cj[1])}
    for k, v in extra.items():
        lv[k] = (v[0], lift(w, v[1], Aij))
    return Ai, Aij, Closure(w, Aij, lv)


def mvkmvt():
    w = W('mvkmvt', 'Kernel mean value bound (MeanValue kernel_mvt): for S ( t ) = sum_ i c_i exp ( i L_i t ) and T > 0, S. ( -u T , T ) | S | ^ 2 <_ ( 12 T ^ 2 / pi ) Re sum_ i sum_ j c_i c_j* max ( 0 , pi / ( 2 T ) - | L_i - L_j | ), Lean 6 T Re sum sum c c* tri_( 1 / 4T ) ( ( L_i - L_j ) / 2 pi ) exactly.')
    A0 = '( T e. RR+ /\\ %s )' % HK
    P_ = parts(w, A0)
    tp, hk, fin, allst = P_['T e. RR+'], P_[HK], P_['P e. Fin'], P_[HKQ]
    A = AK; D = '( 2 x. ( %s ^ 2 ) )' % A; K3 = '( 3 / %s )' % D
    cl = Closure(w, A0, {'T': ('RR+', tp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+'))})
    cl.leaf(A, 'RR+', cl.mem(A, 'RR+'))
    RC = '( Re ` %s )' % CCJ('i', 'j'); TH = THIJ
    T2A = TRI('( 2 x. %s )' % A, TH); TDT = TRI(DT, TH)
    V_ = '( ( _pi / 4 ) x. %s )' % T2A
    Y0 = 'sum_ i e. P sum_ j e. P ( %s x. %s )' % (RC, V_)
    M = 'sum_ i e. P sum_ j e. P ( abs ` %s )' % RC
    X = ITG(TT, ABS2(SX('t')))
    Yf = '( ( ( ; 1 2 x. ( T ^ 2 ) ) / _pi ) x. ( Re ` %s ) )' % BIL()
    # ---- the constant: K3 ( 2 ( pi / 4 ) ) = 12 T ^ 2 / pi
    aT1 = w.s([cl.mem('_pi', 'CC'), a1(w, A0, '4cn', '4 e. CC'), cl.mem('T', 'CC'), a1(w, A0, '4ne0', '4 =/= 0'), cl.ne0('T')], 'divdiv1d', '( %s -> ( ( _pi / 4 ) / T ) = %s )' % (A0, A))
    aT2 = w.s([cl.mem('( _pi / 4 )', 'CC'), cl.mem('T', 'CC'), cl.ne0('T')], 'divcan1d', '( %s -> ( ( ( _pi / 4 ) / T ) x. T ) = ( _pi / 4 ) )' % A0)
    aT = w.s([dst(w, A0, [aT1], 'oveq1d', '( ( ( _pi / 4 ) / T ) x. T ) = ( %s x. T )' % A), aT2], 'eqtr3d', '( %s -> ( %s x. T ) = ( _pi / 4 ) )' % (A0, A))
    Q = '( ( ; 1 2 x. ( T ^ 2 ) ) / _pi )'
    ip = '( 1 / _pi )'
    qd = w.s([cl.mem('( ; 1 2 x. ( T ^ 2 ) )', 'CC'), cl.mem('_pi', 'CC'), cl.ne0('_pi')], 'divrecd', '( %s -> %s = ( ( ; 1 2 x. ( T ^ 2 ) ) x. %s ) )' % (A0, Q, ip))
    ca = Closure(w, A0, {'T': ('RR', cl.mem('T', 'RR')), A: ('RR', cl.mem(A, 'RR')), ip: ('RR', cl.mem(ip, 'RR')), '_pi': ('RR', cl.mem('_pi', 'RR'))})
    c1 = ringeqp(w, A0, '( ( ( ; 1 2 x. ( T ^ 2 ) ) x. %s ) x. %s )' % (ip, D), '( ( ; 2 4 x. ( ( %s x. T ) ^ 2 ) ) x. %s )' % (A, ip), ca)
    c2 = dst(w, A0, [dst(w, A0, [dst(w, A0, [aT], 'oveq1d', '( ( %s x. T ) ^ 2 ) = ( ( _pi / 4 ) ^ 2 )' % A)], 'oveq2d',
                                '( ; 2 4 x. ( ( %s x. T ) ^ 2 ) ) = ( ; 2 4 x. ( ( _pi / 4 ) ^ 2 ) )' % A)], 'oveq1d',
             '( ( ; 2 4 x. ( ( %s x. T ) ^ 2 ) ) x. %s ) = ( ( ; 2 4 x. ( ( _pi / 4 ) ^ 2 ) ) x. %s )' % (A, ip, ip))
    c3 = ringeqp(w, A0, '( ( ; 2 4 x. ( ( _pi / 4 ) ^ 2 ) ) x. %s )' % ip, '( ( 3 / 2 ) x. ( _pi x. ( _pi x. %s ) ) )' % ip, ca)
    rid = w.s([cl.mem('_pi', 'CC'), cl.ne0('_pi')], 'recidd', '( %s -> ( _pi x. %s ) = 1 )' % (A0, ip))
    c4 = dst(w, A0, [dst(w, A0, [rid], 'oveq2d', '( _pi x. ( _pi x. %s ) ) = ( _pi x. 1 )' % ip)], 'oveq2d', '( ( 3 / 2 ) x. ( _pi x. ( _pi x. %s ) ) ) = ( ( 3 / 2 ) x. ( _pi x. 1 ) )' % ip)
    W2 = '( 2 x. ( _pi / 4 ) )'
    c5 = ringeq(w, A0, '( ( 3 / 2 ) x. ( _pi x. 1 ) )', '( 3 x. %s )' % W2, ca)
    QD = eqt(w, A0, eqt(w, A0, eqt(w, A0, eqt(w, A0, eqt(w, A0, dst(w, A0, [qd], 'oveq1d', '( %s x. %s ) = ( ( ( ; 1 2 x. ( T ^ 2 ) ) x. %s ) x. %s )' % (Q, D, ip, D)), c1), c2), c3), c4), c5)
    # QD: ( Q x. D ) = ( 3 x. W2 ); hence ( 3 x. W2 ) / D = Q and K3 x. W2 = Q
    dmq = w.s([cl.mem('( 3 x. %s )' % W2, 'CC'), cl.mem(Q, 'CC'), cl.mem(D, 'CC'), cl.ne0(D)], 'divmul3d', '( %s -> ( ( ( 3 x. %s ) / %s ) = %s <-> ( 3 x. %s ) = ( %s x. %s ) ) )' % (A0, W2, D, Q, W2, Q, D))
    q1 = w.s([eqc(w, A0, QD), dmq], 'mpbird', '( %s -> ( ( 3 x. %s ) / %s ) = %s )' % (A0, W2, D, Q))
    q2 = w.s([a1(w, A0, '3cn', '3 e. CC'), cl.mem(W2, 'CC'), cl.mem(D, 'CC'), cl.ne0(D)], 'div23d', '( %s -> ( ( 3 x. %s ) / %s ) = ( %s x. %s ) )' % (A0, W2, D, K3, W2))
    KW = eqt(w, A0, eqc(w, A0, q2), q1)          # ( K3 x. W2 ) = Q
    # ---- Y0 = ( pi / 4 ) sum sum RC TRI(DT)
    Ai, Aij, cp = pairctx(w, A0, allst, {'T': ('RR+', tp), '_pi': ('RR+', a1(w, A0, 'pirp', '_pi e. RR+')), A: ('RR+', cl.mem(A, 'RR+'))})
    twoA = ringeq(w, Aij, '( 2 x. ( 4 x. T ) )', '( 4 x. ( 2 x. T ) )', cp) if False else None
    dd1 = ringeq(w, Aij, '( 4 x. T )', '( 2 x. ( 2 x. T ) )', cp)
    dd2 = w.s([cp.mem('_pi', 'CC'), a1(w, Aij, '2cn', '2 e. CC'), cp.mem('( 4 x. T )', 'CC'), a1(w, Aij, '2ne0', '2 =/= 0') and cp.ne0('( 4 x. T )')], 'divassd',
              '( %s -> ( ( 2 x. _pi ) / ( 4 x. T ) ) = ( 2 x. %s ) )' % (Aij, A)) if False else None
    e_a = w.s([a1(w, Aij, '2cn', '2 e. CC'), cp.mem('_pi', 'CC'), cp.mem('( 4 x. T )', 'CC'), cp.ne0('( 4 x. T )')], 'divassd', '( %s -> ( ( 2 x. _pi ) / ( 4 x. T ) ) = ( 2 x. %s ) )' % (Aij, A))
    e_b = dst(w, Aij, [dd1], 'oveq2d', '( ( 2 x. _pi ) / ( 4 x. T ) ) = ( ( 2 x. _pi ) / ( 2 x. ( 2 x. T ) ) )')
    e_c = w.s([cp.mem('_pi', 'CC'), cp.mem('( 2 x. T )', 'CC'), a1(w, Aij, '2cn', '2 e. CC'), cp.ne0('( 2 x. T )'), a1(w, Aij, '2ne0', '2 =/= 0')], 'divcan5d',
              '( %s -> ( ( 2 x. _pi ) / ( 2 x. ( 2 x. T ) ) ) = %s )' % (Aij, DT))
    tA = w.s([e_a, eqt(w, Aij, e_b, e_c)], 'eqtr3d', '( %s -> ( 2 x. %s ) = %s )' % (Aij, A, DT))       # 2A = DT
    tri_eq = w.rewrite(T2A, {'( 2 x. %s )' % A: (DT, tA)}, Aij)
    assert tri_eq[1] == TDT, tri_eq[1]
    cp.leaf(RC, 'RR', cp.mem(RC, 'RR')); cp.leaf(TDT, 'RR', cp.mem(TDT, 'RR'))
    pt1 = eqt(w, Aij, dst(w, Aij, [dst(w, Aij, [tri_eq[0]], 'oveq2d', '%s = ( ( _pi / 4 ) x. %s )' % (V_, TDT))], 'oveq2d', '( %s x. %s ) = ( %s x. ( ( _pi / 4 ) x. %s ) )' % (RC, V_, RC, TDT)),
              ringeq(w, Aij, '( %s x. ( ( _pi / 4 ) x. %s ) )' % (RC, TDT), '( ( _pi / 4 ) x. ( %s x. %s ) )' % (RC, TDT), cp))
    Z1 = 'sum_ j e. P ( %s x. %s )' % (RC, TDT)
    ZZ = 'sum_ i e. P %s' % Z1
    cpi = Closure(w, Ai, {'_pi': ('RR+', a1(w, Ai, 'pirp', '_pi e. RR+'))})
    s1 = w.s([lift(w, fin, Ai), cpi.mem('( _pi / 4 )', 'CC'), cp.mem('( %s x. %s )' % (RC, TDT), 'CC')], 'fsummulc2',
             '( %s -> ( ( _pi / 4 ) x. %s ) = sum_ j e. P ( ( _pi / 4 ) x. ( %s x. %s ) ) )' % (Ai, Z1, RC, TDT))
    s1b = eqt(w, Ai, dst(w, Ai, [pt1], 'sumeq2dv', 'sum_ j e. P ( %s x. %s ) = sum_ j e. P ( ( _pi / 4 ) x. ( %s x. %s ) )' % (RC, V_, RC, TDT)), eqc(w, Ai, s1))
    z1c = w.s([lift(w, fin, Ai), cp.mem('( %s x. %s )' % (RC, TDT), 'CC')], 'fsumcl', '( %s -> %s e. CC )' % (Ai, Z1))
    s2 = w.s([fin, cl.mem('( _pi / 4 )', 'CC'), z1c], 'fsummulc2', '( %s -> ( ( _pi / 4 ) x. %s ) = sum_ i e. P ( ( _pi / 4 ) x. %s ) )' % (A0, ZZ, Z1))
    Y0e = eqt(w, A0, dst(w, A0, [s1b], 'sumeq2dv', '%s = sum_ i e. P ( ( _pi / 4 ) x. %s )' % (Y0, Z1)), eqc(w, A0, s2))    # Y0 = ( pi / 4 ) ZZ
    # ZZ = Re BIL
    B_ = '( %s x. %s )' % (CCJ('i', 'j'), TDT)
    r1 = w.s([fin, w.s([lift(w, fin, Ai), cp.mem(B_, 'CC')], 'fsumcl', '( %s -> sum_ j e. P %s e. CC )' % (Ai, B_))], 'fsumre', '( %s -> ( Re ` %s ) = sum_ i e. P ( Re ` sum_ j e. P %s ) )' % (A0, BIL(), B_))
    r2 = w.s([lift(w, fin, Ai), cp.mem(B_, 'CC')], 'fsumre', '( %s -> ( Re ` sum_ j e. P %s ) = sum_ j e. P ( Re ` %s ) )' % (Ai, B_, B_))
    mc = w.s([cp.mem(CCJ('i', 'j'), 'CC'), cp.mem(TDT, 'CC')], 'mulcomd', '( %s -> %s = ( %s x. %s ) )' % (Aij, B_, TDT, CCJ('i', 'j')))
    rm = w.s([cp.mem(TDT, 'RR'), cp.mem(CCJ('i', 'j'), 'CC'), w.inst('remul2')], 'syl2anc', '( %s -> ( Re ` ( %s x. %s ) ) = ( %s x. %s ) )' % (Aij, TDT, CCJ('i', 'j'), TDT, RC))
    mc2 = w.s([cp.mem(TDT, 'CC'), cp.mem(RC, 'CC')], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (Aij, TDT, RC, RC, TDT))
    rij = eqt(w, Aij, eqt(w, Aij, dst(w, Aij, [mc], 'fveq2d', '( Re ` %s ) = ( Re ` ( %s x. %s ) )' % (B_, TDT, CCJ('i', 'j'))), rm), mc2)
    r3 = eqt(w, Ai, r2, dst(w, Ai, [rij], 'sumeq2dv', 'sum_ j e. P ( Re ` %s ) = %s' % (B_, Z1)))
    REB = eqt(w, A0, r1, dst(w, A0, [r3], 'sumeq2dv', 'sum_ i e. P ( Re ` sum_ j e. P %s ) = %s' % (B_, ZZ)))       # Re BIL = ZZ
    cl.leaf(ZZ, 'RR', w.s([REB, w.s([w.s([fin, w.s([lift(w, fin, Ai), cp.mem(B_, 'CC')], 'fsumcl', '( %s -> sum_ j e. P %s e. CC )' % (Ai, B_))], 'fsumcl',
                                            '( %s -> %s e. CC )' % (A0, BIL()))], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, BIL()))], 'eqeltrrd', '( %s -> %s e. RR )' % (A0, ZZ)))
    # Yf = K3 ( 2 Y0 )
    cy = Closure(w, A0, {K3: ('RR', cl.mem(K3, 'RR')), '_pi': ('RR', cl.mem('_pi', 'RR')), ZZ: ('RR', cl.mem(ZZ, 'RR'))})
    y1 = dst(w, A0, [dst(w, A0, [Y0e], 'oveq2d', '( 2 x. %s ) = ( 2 x. ( ( _pi / 4 ) x. %s ) )' % (Y0, ZZ))], 'oveq2d', '( %s x. ( 2 x. %s ) ) = ( %s x. ( 2 x. ( ( _pi / 4 ) x. %s ) ) )' % (K3, Y0, K3, ZZ))
    y2 = ringeq(w, A0, '( %s x. ( 2 x. ( ( _pi / 4 ) x. %s ) ) )' % (K3, ZZ), '( ( %s x. %s ) x. %s )' % (K3, W2, ZZ), cy)
    y3 = dst(w, A0, [KW, eqc(w, A0, REB)], 'oveq12d', '( ( %s x. %s ) x. %s ) = %s' % (K3, W2, ZZ, Yf))
    YY = eqt(w, A0, eqt(w, A0, y1, y2), y3)            # ( K3 x. ( 2 x. Y0 ) ) = Yf
    # ---- for n >_ T
    Bn = '( ( %s /\\ n e. NN ) /\\ T <_ n )' % A0
    nn = w.s([], 'simplr', '( %s -> n e. NN )' % Bn)
    tn = w.s([], 'simpr', '( %s -> T <_ n )' % Bn)
    cb = Closure(w, Bn, {'T': ('RR+', lift(w, tp, Bn)), 'n': ('NN', nn), '_pi': ('RR+', a1(w, Bn, 'pirp', '_pi e. RR+')), A: ('RR+', lift(w, cl.mem(A, 'RR+'), Bn))})
    KS0 = KSUM('0', 'n')
    km = ap(w, Bn, 'mvkm1', [J(w, Bn, J(w, Bn, lift(w, tp, Bn), lift(w, hk, Bn)), J(w, Bn, cb.mem('n', 'RR+'), tn))], '%s <_ ( %s x. ( 2 x. %s ) )' % (X, K3, KS0))
    Bi, Bij, cq = pairctx(w, Bn, lift(w, allst, Bn), {'n': ('NN', nn), '_pi': ('RR+', a1(w, Bn, 'pirp', '_pi e. RR+')), A: ('RR+', lift(w, cl.mem(A, 'RR+'), Bn)),
                                                     'T': ('RR+', lift(w, tp, Bn))})
    IK = ITG(IOO('0', 'n'), KC(A, TH))
    fj = ap(w, Bij, 'mvfej', [J(w, Bij, J(w, Bij, cq.mem(A, 'RR'), ltle(w, Bij, cq, cq.gt0(A))), J(w, Bij, cq.mem(TH, 'RR'), cq.mem('n', 'RR+')))],
            '( ( t e. %s |-> %s ) e. L^1 /\\ ( abs ` ( %s - %s ) ) <_ ( 2 / n ) )' % (IOO('0', 'n'), KC(A, TH), IK, V_))
    kib = dst(w, Bij, [fj], 'simpld', '( t e. %s |-> %s ) e. L^1' % (IOO('0', 'n'), KC(A, TH)))
    fb = dst(w, Bij, [fj], 'simprd', '( abs ` ( %s - %s ) ) <_ ( 2 / n )' % (IK, V_))
    # KC real on ( 0 , n ) and the integral real
    Bijt = '( %s /\\ t e. %s )' % (Bij, IOO('0', 'n'))
    mt = w.s([], 'simpr', '( %s -> t e. %s )' % (Bijt, IOO('0', 'n')))
    trr = ap(w, Bijt, 'elioore', [mt], 't e. RR')
    t0 = dst(w, Bijt, [ap(w, Bijt, 'eliooord', [mt], '( 0 < t /\\ t < n )')], 'simpld', '0 < t')
    ctt = Closure(w, Bijt, {'t': [('RR', trr), ('gt0', t0)], A: ('RR', lift(w, cq.mem(A, 'RR'), Bijt)), TH: ('RR', lift(w, cq.mem(TH, 'RR'), Bijt))})
    t2p = w.s([trr, w.s([t0], 'gt0ne0d', '( %s -> t =/= 0 )' % Bijt)], 'sqgt0d', '( %s -> 0 < ( t ^ 2 ) )' % Bijt)
    ctt.leaf('( t ^ 2 )', 'ne0', w.s([t2p], 'gt0ne0d', '( %s -> ( t ^ 2 ) =/= 0 )' % Bijt))
    ikr = w.s([ctt.mem(KC(A, TH), 'RR'), kib], 'itgrecl', '( %s -> %s e. RR )' % (Bij, IK))
    cq.leaf(IK, 'RR', ikr); cq.leaf(RC, 'RR', cq.mem(RC, 'RR')); cq.leaf(V_, 'RR', cq.mem(V_, 'RR'))
    df = '( %s - %s )' % (IK, V_)
    cq.leaf(df, 'RR', cq.mem(df, 'RR'))
    pr = '( %s x. %s )' % (RC, df)
    l1 = ap(w, Bij, 'leabs', [cq.mem(pr, 'RR')], '%s <_ ( abs ` %s )' % (pr, pr))
    l2 = w.s([cq.mem(RC, 'CC'), cq.mem(df, 'CC')], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Bij, pr, RC, df))
    l3 = w.s([cq.mem('( abs ` %s )' % df, 'RR'), cq.mem('( 2 / n )', 'RR'), cq.mem('( abs ` %s )' % RC, 'RR'), w.s([cq.mem(RC, 'CC')], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Bij, RC)), fb],
             'lemul2ad', '( %s -> ( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( abs ` %s ) x. ( 2 / n ) ) )' % (Bij, RC, df, RC))
    rr_ = ringeq(w, Bij, pr, '( ( %s x. %s ) - ( %s x. %s ) )' % (RC, IK, RC, V_), cq)
    for t_ in ['( abs ` %s )' % pr, '( ( abs ` %s ) x. ( abs ` %s ) )' % (RC, df), '( ( abs ` %s ) x. ( 2 / n ) )' % RC, '( %s x. %s )' % (RC, IK), '( %s x. %s )' % (RC, V_), pr]:
        cq.leaf(t_, 'RR', cq.mem(t_, 'RR'))
    pb = linarith(w, Bij, [l1, l2, l3, rr_], '( %s x. %s ) <_ ( ( %s x. %s ) + ( ( abs ` %s ) x. ( 2 / n ) ) )' % (RC, IK, RC, V_, RC), closure=cq)
    U1 = '( %s x. %s )' % (RC, IK); U2 = '( ( %s x. %s ) + ( ( abs ` %s ) x. ( 2 / n ) ) )' % (RC, V_, RC)
    fl1 = w.s([lift(w, fin, Bi), cq.mem(U1, 'RR'), cq.mem(U2, 'RR'), pb], 'fsumle', '( %s -> sum_ j e. P %s <_ sum_ j e. P %s )' % (Bi, U1, U2))
    cbi = Closure(w, Bi, {})
    sj1 = w.s([lift(w, fin, Bi), cq.mem(U1, 'RR')], 'fsumrecl', '( %s -> sum_ j e. P %s e. RR )' % (Bi, U1))
    sj2 = w.s([lift(w, fin, Bi), cq.mem(U2, 'RR')], 'fsumrecl', '( %s -> sum_ j e. P %s e. RR )' % (Bi, U2))
    fl2 = w.s([lift(w, fin, Bn), sj1, sj2, fl1], 'fsumle', '( %s -> %s <_ sum_ i e. P sum_ j e. P %s )' % (Bn, KS0, U2))
    # split the right side
    W1 = '( %s x. %s )' % (RC, V_); W2e = '( ( abs ` %s ) x. ( 2 / n ) )' % RC
    fa1 = w.s([lift(w, fin, Bi), cq.mem(W1, 'CC'), cq.mem(W2e, 'CC')], 'fsumadd', '( %s -> sum_ j e. P %s = ( sum_ j e. P %s + sum_ j e. P %s ) )' % (Bi, U2, W1, W2e))
    sw1 = w.s([lift(w, fin, Bi), cq.mem(W1, 'CC')], 'fsumcl', '( %s -> sum_ j e. P %s e. CC )' % (Bi, W1))
    sw2 = w.s([lift(w, fin, Bi), cq.mem(W2e, 'CC')], 'fsumcl', '( %s -> sum_ j e. P %s e. CC )' % (Bi, W2e))
    fa2 = w.s([lift(w, fin, Bn), sw1, sw2], 'fsumadd', '( %s -> sum_ i e. P ( sum_ j e. P %s + sum_ j e. P %s ) = ( %s + sum_ i e. P sum_ j e. P %s ) )' % (Bn, W1, W2e, Y0, W2e))
    fa = eqt(w, Bn, dst(w, Bn, [fa1], 'sumeq2dv', 'sum_ i e. P sum_ j e. P %s = sum_ i e. P ( sum_ j e. P %s + sum_ j e. P %s )' % (U2, W1, W2e)), fa2)
    m1 = w.s([lift(w, fin, Bi), cq.mem('( 2 / n )', 'CC') if False else w.s([cb.mem('( 2 / n )', 'CC')], 'id', 'x') if False else lift(w, cb.mem('( 2 / n )', 'CC'), Bi),
              cq.mem('( abs ` %s )' % RC, 'CC')], 'fsummulc1', '( %s -> ( sum_ j e. P ( abs ` %s ) x. ( 2 / n ) ) = sum_ j e. P %s )' % (Bi, RC, W2e))
    sjm = w.s([lift(w, fin, Bi), cq.mem('( abs ` %s )' % RC, 'CC')], 'fsumcl', '( %s -> sum_ j e. P ( abs ` %s ) e. CC )' % (Bi, RC))
    m2 = w.s([lift(w, fin, Bn), cb.mem('( 2 / n )', 'CC'), sjm], 'fsummulc1', '( %s -> ( %s x. ( 2 / n ) ) = sum_ i e. P ( sum_ j e. P ( abs ` %s ) x. ( 2 / n ) ) )' % (Bn, M, RC))
    mm = eqt(w, Bn, m2, dst(w, Bn, [m1], 'sumeq2dv', 'sum_ i e. P ( sum_ j e. P ( abs ` %s ) x. ( 2 / n ) ) = sum_ i e. P sum_ j e. P %s' % (RC, W2e)))   # M ( 2 / n ) = SS W2e
    # reals
    cb.leaf(KS0, 'RR', w.s([lift(w, fin, Bn), sj1], 'fsumrecl', '( %s -> %s e. RR )' % (Bn, KS0)))
    cb.leaf(Y0, 'RR', w.s([lift(w, fin, Bn), w.s([lift(w, fin, Bi), cq.mem(W1, 'RR')], 'fsumrecl', '( %s -> sum_ j e. P %s e. RR )' % (Bi, W1))], 'fsumrecl', '( %s -> %s e. RR )' % (Bn, Y0)))
    cb.leaf(M, 'RR', w.s([lift(w, fin, Bn), w.s([lift(w, fin, Bi), cq.mem('( abs ` %s )' % RC, 'RR')], 'fsumrecl', '( %s -> sum_ j e. P ( abs ` %s ) e. RR )' % (Bi, RC))], 'fsumrecl', '( %s -> %s e. RR )' % (Bn, M)))
    SW2 = 'sum_ i e. P sum_ j e. P %s' % W2e
    SU2 = 'sum_ i e. P sum_ j e. P %s' % U2
    cb.leaf(SW2, 'RR', w.s([lift(w, fin, Bn), w.s([lift(w, fin, Bi), cq.mem(W2e, 'RR')], 'fsumrecl', '( %s -> sum_ j e. P %s e. RR )' % (Bi, W2e))], 'fsumrecl', '( %s -> %s e. RR )' % (Bn, SW2)))
    cb.leaf(SU2, 'RR', w.s([lift(w, fin, Bn), sj2], 'fsumrecl', '( %s -> %s e. RR )' % (Bn, SU2)))
    cb.leaf('( %s x. ( 2 / n ) )' % M, 'RR', cb.mem('( %s x. ( 2 / n ) )' % M, 'RR'))
    ksb = linarith(w, Bn, [fl2, fa, mm], '%s <_ ( %s + ( %s x. ( 2 / n ) ) )' % (KS0, Y0, M), closure=cb)
    k3r = cb.mem(K3, 'RR')
    k3g = ltle(w, Bn, cb, cb.gt0(K3))
    RHSn = '( %s + ( %s x. ( 2 / n ) ) )' % (Y0, M)
    mb = w.s([cb.mem('( 2 x. %s )' % KS0, 'RR'), cb.mem('( 2 x. %s )' % RHSn, 'RR'), k3r, k3g, linarith(w, Bn, [ksb], '( 2 x. %s ) <_ ( 2 x. %s )' % (KS0, RHSn), closure=cb)],
             'lemul2ad', '( %s -> ( %s x. ( 2 x. %s ) ) <_ ( %s x. ( 2 x. %s ) ) )' % (Bn, K3, KS0, K3, RHSn))
    Zc = '( %s x. ( 2 x. ( 2 x. %s ) ) )' % (K3, M)
    inv = '( 1 / n )'
    rn = w.s([a1(w, Bn, '2cn', '2 e. CC'), cb.mem('n', 'CC'), cb.ne0('n')], 'divrecd', '( %s -> ( 2 / n ) = ( 2 x. %s ) )' % (Bn, inv))
    zn = w.s([cb.mem(Zc, 'CC'), cb.mem('n', 'CC'), cb.ne0('n')], 'divrecd', '( %s -> ( %s / n ) = ( %s x. %s ) )' % (Bn, Zc, Zc, inv))
    ce = Closure(w, Bn, {K3: ('RR', k3r), Y0: ('RR', cb.mem(Y0, 'RR')), M: ('RR', cb.mem(M, 'RR')), inv: ('RR', cb.mem(inv, 'RR'))})
    ex1 = dst(w, Bn, [dst(w, Bn, [dst(w, Bn, [dst(w, Bn, [rn], 'oveq2d', '( %s x. ( 2 / n ) ) = ( %s x. ( 2 x. %s ) )' % (M, M, inv))], 'oveq2d',
                                              '%s = ( %s + ( %s x. ( 2 x. %s ) ) )' % (RHSn, Y0, M, inv))], 'oveq2d', '( 2 x. %s ) = ( 2 x. ( %s + ( %s x. ( 2 x. %s ) ) ) )' % (RHSn, Y0, M, inv))],
              'oveq2d', '( %s x. ( 2 x. %s ) ) = ( %s x. ( 2 x. ( %s + ( %s x. ( 2 x. %s ) ) ) ) )' % (K3, RHSn, K3, Y0, M, inv))
    ex2 = ringeq(w, Bn, '( %s x. ( 2 x. ( %s + ( %s x. ( 2 x. %s ) ) ) ) )' % (K3, Y0, M, inv), '( ( %s x. ( 2 x. %s ) ) + ( %s x. %s ) )' % (K3, Y0, Zc, inv), ce)
    ex3 = dst(w, Bn, [eqc(w, Bn, zn)], 'oveq2d', '( ( %s x. ( 2 x. %s ) ) + ( %s x. %s ) ) = ( ( %s x. ( 2 x. %s ) ) + ( %s / n ) )' % (K3, Y0, Zc, inv, K3, Y0, Zc))
    ex4 = dst(w, Bn, [lift(w, YY, Bn)], 'oveq1d', '( ( %s x. ( 2 x. %s ) ) + ( %s / n ) ) = ( %s + ( %s / n ) )' % (K3, Y0, Zc, Yf, Zc))
    EXn = eqt(w, Bn, eqt(w, Bn, eqt(w, Bn, ex1, ex2), ex3), ex4)
    bnd = w.s([w.s([km, mb], 'letrd' if False else 'id', 'x') if False else None][:0] or [], 'id', 'x') if False else None
    xr = w.s([ap(w, A0, 'mvkm0', [J(w, A0, tp, hk)], '( ( t e. ( 0 (,) T ) |-> %s ) e. L^1 /\\ %s = %s )' % (QQ, X, ITG(IOO('0', 'T'), QQ)))], 'simprd', '( %s -> %s = %s )' % (A0, X, ITG(IOO('0', 'T'), QQ)))
    # X real: from the lsibl integral of | S | ^ 2
    from mv_g import sxcl
    At = '( %s /\\ t e. RR )' % A0
    tr0 = w.s([], 'simpr', '( %s -> t e. RR )' % At)
    sxt = sxcl(w, At, lift(w, allst, At), lift(w, fin, At), 't', {'t': ('RR', tr0)})
    dvx = ap(w, A0, 'mvsxdv', [hk], '( ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> %s ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) /\\ ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (SX('t'), SXD('t'), SX('t'), SXD('t')))
    cn1 = w.s([dvx], 'simp2d', '( %s -> ( t e. RR |-> %s ) e. ( RR -cn-> CC ) )' % (A0, SX('t')))
    cnb = CN(w, A0, 't', 'RR', a1(w, A0, 'ax-resscn', 'RR C_ CC'), cl, Closure(w, At, {SX('t'): ('CC', sxt), 't': ('RR', tr0)}), known={SX('t'): cn1})
    ibx = w.s([cl.mem('-u T', 'RR'), cl.mem('T', 'RR'), cnb(ABS2(SX('t')))], 'lsibl', '( %s -> ( t e. %s |-> %s ) e. L^1 )' % (A0, TT, ABS2(SX('t'))))
    Ati = '( %s /\\ t e. %s )' % (A0, TT)
    tri_ = ap(w, Ati, 'elioore', [w.s([], 'simpr', '( %s -> t e. %s )' % (Ati, TT))], 't e. RR')
    sxi = sxcl(w, Ati, lift(w, allst, Ati), lift(w, fin, Ati), 't', {'t': ('RR', tri_)})
    xrr = w.s([Closure(w, Ati, {SX('t'): ('CC', sxi)}).mem(ABS2(SX('t')), 'RR'), ibx], 'itgrecl', '( %s -> %s e. RR )' % (A0, X))
    cb.leaf(X, 'RR', lift(w, xrr, Bn))
    y0r = w.s([fin, w.s([lift(w, fin, Ai), cp.mem('( %s x. %s )' % (RC, V_), 'RR')], 'fsumrecl', '( %s -> sum_ j e. P ( %s x. %s ) e. RR )' % (Ai, RC, V_))], 'fsumrecl',
              '( %s -> %s e. RR )' % (A0, Y0))
    cl.leaf(Y0, 'RR', y0r)
    yfr = w.s([YY, cl.mem('( %s x. ( 2 x. %s ) )' % (K3, Y0), 'RR')], 'eqeltrrd', '( %s -> %s e. RR )' % (A0, Yf))
    cb.leaf(Yf, 'RR', lift(w, yfr, Bn))
    for t_ in ['( %s x. ( 2 x. %s ) )' % (K3, KS0), '( %s x. ( 2 x. %s ) )' % (K3, RHSn), '( %s / n )' % Zc]:
        cb.leaf(t_, 'RR', cb.mem(t_, 'RR'))
    fn = linarith(w, Bn, [km, mb, EXn], '%s <_ ( %s + ( %s / n ) )' % (X, Yf, Zc), closure=cb)
    ra = w.s([w.s([fn], 'ex', '( ( %s /\\ n e. NN ) -> ( T <_ n -> %s <_ ( %s + ( %s / n ) ) ) )' % (A0, X, Yf, Zc))], 'ralrimiva',
             '( %s -> A. n e. NN ( T <_ n -> %s <_ ( %s + ( %s / n ) ) ) )' % (A0, X, Yf, Zc))
    Mr = w.s([fin, w.s([lift(w, fin, Ai), cp.mem('( abs ` %s )' % RC, 'RR')], 'fsumrecl', '( %s -> sum_ j e. P ( abs ` %s ) e. RR )' % (Ai, RC))], 'fsumrecl', '( %s -> %s e. RR )' % (A0, M))
    cl.leaf(M, 'RR', Mr)
    lim = ap(w, A0, 'mvlim', [J(w, A0, J(w, A0, xrr, yfr, cl.mem(Zc, 'RR')), J(w, A0, cl.mem('T', 'RR'), ra))], '%s <_ %s' % (X, Yf))
    qedlast(w)
    go(w)


if __name__ == '__main__':
    mvkmvt()
