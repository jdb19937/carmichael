"""ZL3b E5: completing the square (zl3fti) and the transform of the shifted Gaussian (zl3ft).
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_e5.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of
from zl3b_d2 import cst
from zl3b_d6 import mi
from zl3b_e1 import seg_pre
from zl3b_e3 import fvm, HOLt, mpt_rw
from zl3b_e4 import gfbody, gfv, p_nn0, hol_gf
from cl import Closure
import lin, congr

only = sys.argv[1:]
S = STATEMENTS


class Q:
    """deduction steps under a fixed antecedent with a closure for CC memberships"""
    def __init__(self, w, ph, leaves):
        self.w, self.ph = w, ph
        self.cl = Closure(w, ph, leaves)

    def c(self, e):
        return self.cl.mem(e, 'CC')

    def d(self, ref, hyps, concl):
        return D(self.w, self.ph, ref, hyps, concl)

    def eq(self, ref, args, lhs, rhs):
        """a lemma whose hypotheses are the CC memberships of args"""
        return self.d(ref, [self.c(a) for a in args], '%s = %s' % (lhs, rhs))

    def chain(self, first, pairs):
        cur = None; cur_r = None
        for st, r in pairs:
            cur = st if cur is None else self.d('eqtrd', [cur, st], '%s = %s' % (first, r))
            cur_r = r
        return cur

    def sym(self, st, lhs, rhs):
        return self.d('eqcomd', [st], '%s = %s' % (rhs, lhs))


# ---------------------------------------------------------------- zl3fti
if __name__ == '__main__' and (not only or 'zl3fti' in only):
    w = W('zl3fti', 'Completing the square: ` FF ( x ) e ^ ( -2 pi i j x ) ` is a constant times the rotated Gaussian ` Om ` translated by ` s `.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3fti'])
    tp = w.s([], 'simpl1', '( %s -> T e. RR+ )' % ph); ar = w.s([], 'simpl2', '( %s -> A e. RR )' % ph); pp = w.s([], 'simpl3', '( %s -> P e. { 0 , 1 } )' % ph)
    jz = w.s([], 'simprl', '( %s -> j e. ZZ )' % ph); xr = w.s([], 'simprr', '( %s -> X e. RR )' % ph)
    pn = p_nn0(w, ph, pp)
    q = Q(w, ph, {'T': tp, 'A': ar, 'j': jz, 'X': xr, 'P': pn, '_i': cst(w, ph, 'ax-icn', '_i e. CC'), '_pi': cst(w, ph, 'pirp', '_pi e. RR+')})
    tn0 = D(w, ph, 'rpne0d', [tp], 'T =/= 0')
    K = KAP; Wv = '( X + A )'; IW = '( _i x. %s )' % Wv
    Z0 = CP('0', 'X'); Z = '( %s + %s )' % (Z0, SJ)
    # values
    v1, _ = fvm(w, ph, 'y', '( %s ` ( y + %s ) )' % (OMJ, SJ), Z0, q.c(Z0), g)
    v2 = gfv(w, ph, '-u T', '0', K, 'P', Z, q.c(Z), g, 'w')
    val = gfbody('-u T', '0', K, 'P', Z)
    lv = q.d('eqtrd', [v1, v2], '( %s ` %s ) = %s' % (TRN(OMJ, SJ), Z0, val))
    # Z = ( IW - K )
    IX, IA, NK = '( _i x. X )', '( _i x. A )', '-u %s' % K
    z1 = q.d('oveq1d', [q.eq('addlidd', [IX], '( 0 + %s )' % IX, IX)], '%s = ( %s + %s )' % (Z, IX, SJ))
    z2 = q.eq('add12d', [IX, NK, IA], '( %s + ( %s + %s ) )' % (IX, NK, IA), '( %s + ( %s + %s ) )' % (NK, IX, IA))
    z3 = q.d('oveq2d', [q.sym(q.eq('adddid', ['_i', 'X', 'A'], '( _i x. %s )' % Wv, '( %s + %s )' % (IX, IA)), IW, '( %s + %s )' % (IX, IA))], '( %s + ( %s + %s ) ) = ( %s + %s )' % (NK, IX, IA, NK, IW))
    z4 = q.eq('addcomd', [NK, IW], '( %s + %s )' % (NK, IW), '( %s + %s )' % (IW, NK))
    z5 = q.eq('negsubd', [IW, K], '( %s + %s )' % (IW, NK), '( %s - %s )' % (IW, K))
    ZZ = '( %s - %s )' % (IW, K)
    zeq = q.chain(Z, [(z1, '( %s + %s )' % (IX, SJ)), (z2, '( %s + ( %s + %s ) )' % (NK, IX, IA)), (z3, '( %s + %s )' % (NK, IW)), (z4, '( %s + %s )' % (IW, NK)), (z5, ZZ)])
    # the P-part: ( -u _i ^ P ) x. ( ( Z + K ) ^ P ) = ( W ^ P )
    zk = q.chain('( %s + %s )' % (Z, K), [(q.d('oveq1d', [zeq], '( %s + %s ) = ( %s + %s )' % (Z, K, ZZ, K)), '( %s + %s )' % (ZZ, K)), (q.eq('npcand', [IW, K], '( %s + %s )' % (ZZ, K), IW), IW)])
    NI = '-u _i'
    p1 = q.sym(q.d('mulexpd', [q.c(NI), q.c('( %s + %s )' % (Z, K)), pn], '( ( %s x. ( %s + %s ) ) ^ P ) = ( ( %s ^ P ) x. ( ( %s + %s ) ^ P ) )' % (NI, Z, K, NI, Z, K)),
               '( ( %s x. ( %s + %s ) ) ^ P )' % (NI, Z, K), '( ( %s ^ P ) x. ( ( %s + %s ) ^ P ) )' % (NI, Z, K))
    p2 = q.d('oveq1d', [q.chain('( %s x. ( %s + %s ) )' % (NI, Z, K), [(q.d('oveq2d', [zk], '( %s x. ( %s + %s ) ) = ( %s x. %s )' % (NI, Z, K, NI, IW)), '( %s x. %s )' % (NI, IW)),
                                                                     (mi(w, ph, Wv, q.c(Wv)), Wv)])], '( ( %s x. ( %s + %s ) ) ^ P ) = ( %s ^ P )' % (NI, Z, K, Wv))
    ppart = q.d('eqtrd', [p1, p2], '( ( %s ^ P ) x. ( ( %s + %s ) ^ P ) ) = ( %s ^ P )' % (NI, Z, K, Wv))
    # the exponent
    Q2 = '( ( %s + 0 ) ^ 2 )' % Z
    W2 = '( %s ^ 2 )' % Wv
    PT = '( _pi x. T )'
    q1 = q.d('oveq1d', [q.d('eqtrd', [q.eq('addridd', [Z], '( %s + 0 )' % Z, Z), zeq], '( %s + 0 ) = %s' % (Z, ZZ))], '%s = ( %s ^ 2 )' % (Q2, ZZ))
    q2 = q.d('syl2anc', [q.c(IW), q.c(K), w.inst('binom2sub')], '( %s ^ 2 ) = ( ( ( %s ^ 2 ) - ( 2 x. ( %s x. %s ) ) ) + ( %s ^ 2 ) )' % (ZZ, IW, IW, K, K))
    i2w = q.chain('( %s ^ 2 )' % IW, [(q.eq('sqmuld', ['_i', Wv], '( %s ^ 2 )' % IW, '( ( _i ^ 2 ) x. %s )' % W2), '( ( _i ^ 2 ) x. %s )' % W2),
                                      (q.d('oveq1d', [cst(w, ph, 'i2', '( _i ^ 2 ) = -u 1')], '( ( _i ^ 2 ) x. %s ) = ( -u 1 x. %s )' % (W2, W2)), '( -u 1 x. %s )' % W2),
                                      (q.eq('mulm1d', [W2], '( -u 1 x. %s )' % W2, '-u %s' % W2), '-u %s' % W2)])
    TWK = '( 2 x. ( %s x. %s ) )' % (IW, K); K2 = '( %s ^ 2 )' % K
    QQ = '( ( -u %s - %s ) + %s )' % (W2, TWK, K2)
    q3 = q.d('oveq1d', [q.d('oveq1d', [i2w], '( ( %s ^ 2 ) - %s ) = ( -u %s - %s )' % (IW, TWK, W2, TWK))], '( ( ( %s ^ 2 ) - %s ) + %s ) = %s' % (IW, TWK, K2, QQ))
    qe = q.chain(Q2, [(q1, '( %s ^ 2 )' % ZZ), (q2, '( ( ( %s ^ 2 ) - %s ) + %s )' % (IW, TWK, K2)), (q3, QQ)])
    # -u ( ( _pi x. -u T ) x. Q2 ) = ( PT x. QQ )
    E3 = '-u ( ( _pi x. -u T ) x. %s )' % Q2
    e1 = q.d('negeqd', [q.d('oveq1d', [q.eq('mulneg2d', ['_pi', 'T'], '( _pi x. -u T )', '-u %s' % PT)], '( ( _pi x. -u T ) x. %s ) = ( -u %s x. %s )' % (Q2, PT, Q2))],
             '%s = -u ( -u %s x. %s )' % (E3, PT, Q2))
    e2 = q.d('negeqd', [q.eq('mulneg1d', [PT, Q2], '( -u %s x. %s )' % (PT, Q2), '-u ( %s x. %s )' % (PT, Q2))], '-u ( -u %s x. %s ) = -u -u ( %s x. %s )' % (PT, Q2, PT, Q2))
    e3 = q.eq('negnegd', ['( %s x. %s )' % (PT, Q2)], '-u -u ( %s x. %s )' % (PT, Q2), '( %s x. %s )' % (PT, Q2))
    e4 = q.d('oveq2d', [qe], '( %s x. %s ) = ( %s x. %s )' % (PT, Q2, PT, QQ))
    e3q = q.chain(E3, [(e1, '-u ( -u %s x. %s )' % (PT, Q2)), (e2, '-u -u ( %s x. %s )' % (PT, Q2)), (e3, '( %s x. %s )' % (PT, Q2)), (e4, '( %s x. %s )' % (PT, QQ))])
    # PT x. QQ = ( ( C - D ) + Aa ) with C = -u ( PT x. W2 ), D = ( ( 2 x. ( _i x. _pi ) ) x. ( j x. W ) ), Aa = ( _pi x. ( ( j ^ 2 ) / T ) )
    TIP = '( 2 x. ( _i x. _pi ) )'
    Cc = '-u ( %s x. %s )' % (PT, W2); Dd = '( %s x. ( j x. %s ) )' % (TIP, Wv); Aa = '( _pi x. ( ( j ^ 2 ) / T ) )'
    d1 = q.eq('adddid', [PT, '( -u %s - %s )' % (W2, TWK), K2], '( %s x. %s )' % (PT, QQ), '( ( %s x. ( -u %s - %s ) ) + ( %s x. %s ) )' % (PT, W2, TWK, PT, K2))
    d2 = q.eq('subdid', [PT, '-u %s' % W2, TWK], '( %s x. ( -u %s - %s ) )' % (PT, W2, TWK), '( ( %s x. -u %s ) - ( %s x. %s ) )' % (PT, W2, PT, TWK))
    d3 = q.eq('mulneg2d', [PT, W2], '( %s x. -u %s )' % (PT, W2), Cc)
    # PT x. TWK = Dd : ( _pi x. T ) x. ( 2 x. ( ( _i x. W ) x. K ) ) = ( 2 x. ( _i x. _pi ) ) x. ( j x. W )
    tk = q.d('divcan2d', [q.c('j'), q.c('T'), tn0], '( T x. %s ) = j' % K)
    m1 = q.eq('mul12d', [PT, '2', '( %s x. %s )' % (IW, K)], '( %s x. %s )' % (PT, TWK), '( 2 x. ( %s x. ( %s x. %s ) ) )' % (PT, IW, K))
    # ( PT x. ( IW x. K ) ) = ( ( _i x. _pi ) x. ( j x. W ) )
    IWK = '( %s x. %s )' % (IW, K)
    m2 = q.eq('mulassd', ['_i', Wv, K], IWK, '( _i x. ( %s x. %s ) )' % (Wv, K))
    m3 = q.eq('mulcomd', [Wv, K], '( %s x. %s )' % (Wv, K), '( %s x. %s )' % (K, Wv))
    iwk = q.chain(IWK, [(m2, '( _i x. ( %s x. %s ) )' % (Wv, K)), (q.d('oveq2d', [m3], '( _i x. ( %s x. %s ) ) = ( _i x. ( %s x. %s ) )' % (Wv, K, K, Wv)), '( _i x. ( %s x. %s ) )' % (K, Wv))])
    m4 = q.d('oveq2d', [iwk], '( %s x. %s ) = ( %s x. ( _i x. ( %s x. %s ) ) )' % (PT, IWK, PT, K, Wv))
    m5 = q.eq('mul4d', ['_pi', 'T', '_i', '( %s x. %s )' % (K, Wv)], '( %s x. ( _i x. ( %s x. %s ) ) )' % (PT, K, Wv), '( ( _pi x. _i ) x. ( T x. ( %s x. %s ) ) )' % (K, Wv))
    m6 = q.d('oveq12d', [q.eq('mulcomd', ['_pi', '_i'], '( _pi x. _i )', '( _i x. _pi )'),
                         q.d('eqtr3d', [q.eq('mulassd', ['T', K, Wv], '( ( T x. %s ) x. %s )' % (K, Wv), '( T x. ( %s x. %s ) )' % (K, Wv)), q.d('oveq1d', [tk], '( ( T x. %s ) x. %s ) = ( j x. %s )' % (K, Wv, Wv))],
                               '( T x. ( %s x. %s ) ) = ( j x. %s )' % (K, Wv, Wv))], '( ( _pi x. _i ) x. ( T x. ( %s x. %s ) ) ) = ( ( _i x. _pi ) x. ( j x. %s ) )' % (K, Wv, Wv))
    ptiwk = q.chain('( %s x. %s )' % (PT, IWK), [(m4, '( %s x. ( _i x. ( %s x. %s ) ) )' % (PT, K, Wv)), (m5, '( ( _pi x. _i ) x. ( T x. ( %s x. %s ) ) )' % (K, Wv)), (m6, '( ( _i x. _pi ) x. ( j x. %s ) )' % Wv)])
    m7 = q.d('oveq2d', [ptiwk], '( 2 x. ( %s x. %s ) ) = ( 2 x. ( ( _i x. _pi ) x. ( j x. %s ) ) )' % (PT, IWK, Wv))
    m8 = q.sym(q.eq('mulassd', ['2', '( _i x. _pi )', '( j x. %s )' % Wv], Dd, '( 2 x. ( ( _i x. _pi ) x. ( j x. %s ) ) )' % Wv), Dd, '( 2 x. ( ( _i x. _pi ) x. ( j x. %s ) ) )' % Wv)
    ptt = q.chain('( %s x. %s )' % (PT, TWK), [(m1, '( 2 x. ( %s x. %s ) )' % (PT, IWK)), (m7, '( 2 x. ( ( _i x. _pi ) x. ( j x. %s ) ) )' % Wv), (m8, Dd)])
    # PT x. K2 = Aa
    k2 = q.d('expdivd', [q.c('j'), q.c('T'), tn0, cst(w, ph, '2nn0', '2 e. NN0')], '%s = ( ( j ^ 2 ) / ( T ^ 2 ) )' % K2)
    J2 = '( j ^ 2 )'
    t2 = q.eq('sqvald', ['T'], '( T ^ 2 )', '( T x. T )')
    dd = q.sym(q.d('divdiv1d', [q.c(J2), q.c('T'), tn0, q.c('T'), tn0], '( ( %s / T ) / T ) = ( %s / ( T x. T ) )' % (J2, J2)), '( ( %s / T ) / T )' % J2, '( %s / ( T x. T ) )' % J2)
    k2b = q.chain(K2, [(k2, '( %s / ( T ^ 2 ) )' % J2), (q.d('oveq2d', [t2], '( %s / ( T ^ 2 ) ) = ( %s / ( T x. T ) )' % (J2, J2)), '( %s / ( T x. T ) )' % J2), (dd, '( ( %s / T ) / T )' % J2)])
    pk = q.chain('( %s x. %s )' % (PT, K2), [(q.eq('mulassd', ['_pi', 'T', K2], '( %s x. %s )' % (PT, K2), '( _pi x. ( T x. %s ) )' % K2), '( _pi x. ( T x. %s ) )' % K2),
                                              (q.d('oveq2d', [q.d('eqtrd', [q.d('oveq2d', [k2b], '( T x. %s ) = ( T x. ( ( %s / T ) / T ) )' % (K2, J2)),
                                                                            q.d('divcan2d', [q.c('( %s / T )' % J2), q.c('T'), tn0], '( T x. ( ( %s / T ) / T ) ) = ( %s / T )' % (J2, J2))],
                                                                     '( T x. %s ) = ( %s / T )' % (K2, J2))], '( _pi x. ( T x. %s ) ) = %s' % (K2, Aa)), Aa)])
    ptq = q.chain('( %s x. %s )' % (PT, QQ), [(d1, '( ( %s x. ( -u %s - %s ) ) + ( %s x. %s ) )' % (PT, W2, TWK, PT, K2)),
                                               (q.d('oveq12d', [q.d('eqtrd', [d2, q.d('oveq12d', [d3, ptt], '( ( %s x. -u %s ) - ( %s x. %s ) ) = ( %s - %s )' % (PT, W2, PT, TWK, Cc, Dd))],
                                                                    '( %s x. ( -u %s - %s ) ) = ( %s - %s )' % (PT, W2, TWK, Cc, Dd)), pk],
                                                      '( ( %s x. ( -u %s - %s ) ) + ( %s x. %s ) ) = ( ( %s - %s ) + %s )' % (PT, W2, TWK, PT, K2, Cc, Dd, Aa)), '( ( %s - %s ) + %s )' % (Cc, Dd, Aa))])
    e3f = q.d('eqtrd', [e3q, ptq], '%s = ( ( %s - %s ) + %s )' % (E3, Cc, Dd, Aa))
    # EL = ( ( -u Aa + Bb ) + ( ( Cc - Dd ) + Aa ) ) = ( Cc + -u ( TIP x. ( j x. X ) ) )
    Bb = '( %s x. ( j x. A ) )' % TIP
    EL = '( ( -u %s + %s ) + %s )' % (Aa, Bb, E3)
    CD = '( %s - %s )' % (Cc, Dd)
    f1 = q.d('oveq2d', [e3f], '%s = ( ( -u %s + %s ) + ( %s + %s ) )' % (EL, Aa, Bb, CD, Aa))
    f2 = q.eq('addcomd', ['( -u %s + %s )' % (Aa, Bb), '( %s + %s )' % (CD, Aa)], '( ( -u %s + %s ) + ( %s + %s ) )' % (Aa, Bb, CD, Aa), '( ( %s + %s ) + ( -u %s + %s ) )' % (CD, Aa, Aa, Bb))
    f3 = q.eq('addassd', [CD, Aa, '( -u %s + %s )' % (Aa, Bb)], '( ( %s + %s ) + ( -u %s + %s ) )' % (CD, Aa, Aa, Bb), '( %s + ( %s + ( -u %s + %s ) ) )' % (CD, Aa, Aa, Bb))
    f4a = q.chain('( -u %s + %s )' % (Aa, Bb), [(q.eq('addcomd', ['-u %s' % Aa, Bb], '( -u %s + %s )' % (Aa, Bb), '( %s + -u %s )' % (Bb, Aa)), '( %s + -u %s )' % (Bb, Aa)),
                                                (q.eq('negsubd', [Bb, Aa], '( %s + -u %s )' % (Bb, Aa), '( %s - %s )' % (Bb, Aa)), '( %s - %s )' % (Bb, Aa))])
    f4 = q.chain('( %s + ( -u %s + %s ) )' % (Aa, Aa, Bb), [(q.d('oveq2d', [f4a], '( %s + ( -u %s + %s ) ) = ( %s + ( %s - %s ) )' % (Aa, Aa, Bb, Aa, Bb, Aa)), '( %s + ( %s - %s ) )' % (Aa, Bb, Aa)),
                                                          (q.eq('pncan3d', [Aa, Bb], '( %s + ( %s - %s ) )' % (Aa, Bb, Aa), Bb), Bb)])
    f5 = q.d('oveq2d', [f4], '( %s + ( %s + ( -u %s + %s ) ) ) = ( %s + %s )' % (CD, Aa, Aa, Bb, CD, Bb))
    f6 = q.eq('subadd23d', [Cc, Dd, Bb], '( %s + %s )' % (CD, Bb), '( %s + ( %s - %s ) )' % (Cc, Bb, Dd))
    # Bb - Dd = -u ( TIP x. ( j x. X ) )
    JX = '( j x. X )'
    g1 = q.sym(q.eq('subdid', [TIP, '( j x. A )', '( j x. %s )' % Wv], '( %s x. ( ( j x. A ) - ( j x. %s ) ) )' % (TIP, Wv), '( %s - %s )' % (Bb, Dd)), '( %s x. ( ( j x. A ) - ( j x. %s ) ) )' % (TIP, Wv), '( %s - %s )' % (Bb, Dd))
    g2 = q.sym(q.eq('subdid', ['j', 'A', Wv], '( j x. ( A - %s ) )' % Wv, '( ( j x. A ) - ( j x. %s ) )' % Wv), '( j x. ( A - %s ) )' % Wv, '( ( j x. A ) - ( j x. %s ) )' % Wv)
    aw = q.chain('( A - %s )' % Wv, [(q.sym(q.eq('negsubdi2d', [Wv, 'A'], '-u ( %s - A )' % Wv, '( A - %s )' % Wv), '-u ( %s - A )' % Wv, '( A - %s )' % Wv), '-u ( %s - A )' % Wv),
                                     (q.d('negeqd', [q.eq('pncand', ['X', 'A'], '( %s - A )' % Wv, 'X')], '-u ( %s - A ) = -u X' % Wv), '-u X')])
    g3 = q.chain('( j x. ( A - %s ) )' % Wv, [(q.d('oveq2d', [aw], '( j x. ( A - %s ) ) = ( j x. -u X )' % Wv), '( j x. -u X )'), (q.eq('mulneg2d', ['j', 'X'], '( j x. -u X )', '-u %s' % JX), '-u %s' % JX)])
    bd = q.chain('( %s - %s )' % (Bb, Dd), [(g1, '( %s x. ( ( j x. A ) - ( j x. %s ) ) )' % (TIP, Wv)),
                                          (q.d('oveq2d', [q.d('eqtrd', [g2, g3], '( ( j x. A ) - ( j x. %s ) ) = -u %s' % (Wv, JX))], '( %s x. ( ( j x. A ) - ( j x. %s ) ) ) = ( %s x. -u %s )' % (TIP, Wv, TIP, JX)), '( %s x. -u %s )' % (TIP, JX)),
                                          (q.eq('mulneg2d', [TIP, JX], '( %s x. -u %s )' % (TIP, JX), '-u ( %s x. %s )' % (TIP, JX)), '-u ( %s x. %s )' % (TIP, JX))])
    ER = '( %s + -u ( %s x. %s ) )' % (Cc, TIP, JX)
    f7 = q.d('oveq2d', [bd], '( %s + ( %s - %s ) ) = %s' % (Cc, Bb, Dd, ER))
    expo = q.chain(EL, [(f1, '( ( -u %s + %s ) + ( %s + %s ) )' % (Aa, Bb, CD, Aa)), (f2, '( ( %s + %s ) + ( -u %s + %s ) )' % (CD, Aa, Aa, Bb)), (f3, '( %s + ( %s + ( -u %s + %s ) ) )' % (CD, Aa, Aa, Bb)),
                        (f5, '( %s + %s )' % (CD, Bb)), (f6, '( %s + ( %s - %s ) )' % (Cc, Bb, Dd)), (f7, ER)])
    # exponentials: EJ x. ( exp ` E3 ) = ( exp ` Cc ) x. ( exp ` -u ( TIP x. JX ) )
    X1, X2 = '-u %s' % Aa, Bb
    x1 = q.sym(q.eq('efaddd', [X1, X2], '( exp ` ( %s + %s ) )' % (X1, X2), EJ), '( exp ` ( %s + %s ) )' % (X1, X2), EJ) if False else None
    ea1 = q.d('syl2anc', [q.c(X1), q.c(X2), w.inst('efadd')], '( exp ` ( %s + %s ) ) = %s' % (X1, X2, EJ))
    ea2 = q.d('syl2anc', [q.c('( %s + %s )' % (X1, X2)), q.c(E3), w.inst('efadd')], '( exp ` %s ) = ( ( exp ` ( %s + %s ) ) x. ( exp ` %s ) )' % (EL, X1, X2, E3))
    ea3 = q.d('syl2anc', [q.c(Cc), q.c('-u ( %s x. %s )' % (TIP, JX)), w.inst('efadd')], '( exp ` %s ) = ( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) )' % (ER, Cc, TIP, JX))
    ex_ = q.chain('( %s x. ( exp ` %s ) )' % (EJ, E3), [(q.d('oveq1d', [q.sym(ea1, '( exp ` ( %s + %s ) )' % (X1, X2), EJ)], '( %s x. ( exp ` %s ) ) = ( ( exp ` ( %s + %s ) ) x. ( exp ` %s ) )' % (EJ, E3, X1, X2, E3)),
                                                          '( ( exp ` ( %s + %s ) ) x. ( exp ` %s ) )' % (X1, X2, E3)),
                                                         (q.sym(ea2, '( exp ` %s )' % EL, '( ( exp ` ( %s + %s ) ) x. ( exp ` %s ) )' % (X1, X2, E3)), '( exp ` %s )' % EL),
                                                         (q.d('fveq2d', [expo], '( exp ` %s ) = ( exp ` %s )' % (EL, ER)), '( exp ` %s )' % ER),
                                                         (ea3, '( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) )' % (Cc, TIP, JX))])
    # assemble
    ZKP = '( ( %s + %s ) ^ P )' % (Z, K)
    NIP = '( %s ^ P )' % NI
    lhs = '( %s x. ( %s ` %s ) )' % (CSTJ, TRN(OMJ, SJ), Z0)
    a1 = q.d('oveq2d', [lv], '%s = ( %s x. %s )' % (lhs, CSTJ, val))
    a2 = q.eq('mul4d', [NIP, EJ, ZKP, '( exp ` %s )' % E3], '( %s x. %s )' % (CSTJ, val), '( ( %s x. %s ) x. ( %s x. ( exp ` %s ) ) )' % (NIP, ZKP, EJ, E3))
    WP = '( %s ^ P )' % Wv
    a3 = q.d('oveq12d', [ppart, ex_], '( ( %s x. %s ) x. ( %s x. ( exp ` %s ) ) ) = ( %s x. ( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) ) )' % (NIP, ZKP, EJ, E3, WP, Cc, TIP, JX))
    a4 = q.sym(q.eq('mulassd', [WP, '( exp ` %s )' % Cc, '( exp ` -u ( %s x. %s ) )' % (TIP, JX)], '( ( %s x. ( exp ` %s ) ) x. ( exp ` -u ( %s x. %s ) ) )' % (WP, Cc, TIP, JX),
                    '( %s x. ( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) ) )' % (WP, Cc, TIP, JX)),
               '( ( %s x. ( exp ` %s ) ) x. ( exp ` -u ( %s x. %s ) ) )' % (WP, Cc, TIP, JX), '( %s x. ( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) ) )' % (WP, Cc, TIP, JX))
    fvx, fval = fvm(w, ph, 'y', '( ( ( y + A ) ^ P ) x. ( exp ` -u ( ( _pi x. T ) x. ( ( y + A ) ^ 2 ) ) ) )', 'X', q.c('X'), g)
    assert fval == '( %s x. ( exp ` %s ) )' % (WP, Cc), fval
    a5 = q.sym(q.d('oveq1d', [fvx], '( ( %s ` X ) x. ( exp ` -u ( %s x. %s ) ) ) = ( %s x. ( exp ` -u ( %s x. %s ) ) )' % (FF, TIP, JX, fval, TIP, JX)),
               '( ( %s ` X ) x. ( exp ` -u ( %s x. %s ) ) )' % (FF, TIP, JX), '( %s x. ( exp ` -u ( %s x. %s ) ) )' % (fval, TIP, JX))
    fin = q.chain(lhs, [(a1, '( %s x. %s )' % (CSTJ, val)), (a2, '( ( %s x. %s ) x. ( %s x. ( exp ` %s ) ) )' % (NIP, ZKP, EJ, E3)),
                        (a3, '( %s x. ( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) ) )' % (WP, Cc, TIP, JX)), (a4, '( ( %s x. ( exp ` %s ) ) x. ( exp ` -u ( %s x. %s ) ) )' % (WP, Cc, TIP, JX)),
                        (a5, '( ( %s ` X ) x. ( exp ` -u ( %s x. %s ) ) )' % (FF, TIP, JX))])
    w.qed([fin], 'idi', S['zl3fti'])
    go(w, only)


def val_of(w, A_, F, L, conv, ff):
    """( A_ -> ( ~~>r ` F ) = L ) from conv: ( A_ -> F ~~>r L ), ff: ( A_ -> F : RR+ --> CC )"""
    dm = w.s([conv, w.s([w.s([], 'rlimrel', 'Rel ~~>r')], 'releldmi', '( %s ~~>r %s -> %s e. dom ~~>r )' % (F, L, F))], 'syl', '( %s -> %s e. dom ~~>r )' % (A_, F))
    sup = cst(w, A_, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')
    rv = D(w, A_, 'mpbid', [dm, w.s([ff, sup], 'rlimdm', '( %s -> ( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) ) )' % (A_, F, F, F))], '%s ~~>r ( ~~>r ` %s )' % (F, F))
    return w.s([ff, sup, rv, conv], 'rlimuni', '( %s -> ( ~~>r ` %s ) = %s )' % (A_, F, L))


def lt_cl(w, A_, G, gc, C='0'):
    """( ( A_ /\\ t e. RR+ ) -> LT(G,C,t) e. CC ) and the mapping into CC"""
    At = '( %s /\\ t e. RR+ )' % A_
    tc = D(w, At, 'rpcnd', [w.s([], 'simpr', '( %s -> t e. RR+ )' % At)], 't e. CC')
    ic = cst(w, At, 'ax-icn', '_i e. CC'); cc = cst(w, At, '0cn', '0 e. CC') if C == '0' else None
    P, Qp = CP(C, '-u t'), CP(C, 't')
    pc = D(w, At, 'addcld', [cc, D(w, At, 'mulcld', [ic, D(w, At, 'negcld', [tc], '-u t e. CC')], '( _i x. -u t ) e. CC')], '%s e. CC' % P)
    qc = D(w, At, 'addcld', [cc, D(w, At, 'mulcld', [ic, tc], '( _i x. t ) e. CC')], '%s e. CC' % Qp)
    lc = D(w, At, 'syl', [seg_pre(w, At, P, Qp, pc, qc, w.s([gc], 'adantr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At, G)) if G == 'G' else None), w.inst('lintcl')], 'x') if False else None
    css = D(w, At, 'syl2anc', [pc, qc, w.inst('csegcl')], '( %s cseg %s ) C_ CC' % (P, Qp))
    pre = w.s([w.s([pc, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (At, P, Qp)), w.s([w.s([gc], 'adantr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At, G)), css], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (At, G, P, Qp))],
              'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At, P, Qp, G, P, Qp))
    lc = D(w, At, 'syl', [pre, w.inst('lintcl')], '%s e. CC' % LT(G, C, 't'))
    return w.s([lc], 'fmptd', '( %s -> ( t e. RR+ |-> %s ) : RR+ --> CC )' % (A_, LT(G, C, 't')))


def reim_ni(w, A_, c, cc):
    """( A_ -> ( Re ` ( -u _i x. c ) ) = ( Im ` c ) ) and ( A_ -> ( Im ` ( -u _i x. c ) ) = -u ( Re ` c ) )"""
    ic = cst(w, A_, 'ax-icn', '_i e. CC'); nic = D(w, A_, 'negcld', [ic], '-u _i e. CC')
    V = '( -u _i x. %s )' % c
    rni = D(w, A_, 'eqtrd', [w.s([ic, w.inst('reneg')], 'syl', '( %s -> ( Re ` -u _i ) = -u ( Re ` _i ) )' % A_), D(w, A_, 'eqtrd', [D(w, A_, 'negeqd', [cst(w, A_, 'rei', '( Re ` _i ) = 0')], '-u ( Re ` _i ) = -u 0'), cst(w, A_, 'neg0', '-u 0 = 0')], '-u ( Re ` _i ) = 0')],
            '( Re ` -u _i ) = 0')
    ini = D(w, A_, 'eqtrd', [w.s([ic, w.inst('imneg')], 'syl', '( %s -> ( Im ` -u _i ) = -u ( Im ` _i ) )' % A_), D(w, A_, 'negeqd', [cst(w, A_, 'imi', '( Im ` _i ) = 1')], '-u ( Im ` _i ) = -u 1')], '( Im ` -u _i ) = -u 1')
    X, Y = '( Re ` %s )' % c, '( Im ` %s )' % c
    xr = D(w, A_, 'recld', [cc], '%s e. RR' % X); yr = D(w, A_, 'imcld', [cc], '%s e. RR' % Y)
    r1 = D(w, A_, 'remuld', [nic, cc], '( Re ` %s ) = ( ( ( Re ` -u _i ) x. %s ) - ( ( Im ` -u _i ) x. %s ) )' % (V, X, Y))
    r2 = D(w, A_, 'oveq12d', [D(w, A_, 'oveq1d', [rni], '( ( Re ` -u _i ) x. %s ) = ( 0 x. %s )' % (X, X)), D(w, A_, 'oveq1d', [ini], '( ( Im ` -u _i ) x. %s ) = ( -u 1 x. %s )' % (Y, Y))],
             '( ( ( Re ` -u _i ) x. %s ) - ( ( Im ` -u _i ) x. %s ) ) = ( ( 0 x. %s ) - ( -u 1 x. %s ) )' % (X, Y, X, Y))
    xc_ = D(w, A_, 'recnd', [xr], '%s e. CC' % X); yc_ = D(w, A_, 'recnd', [yr], '%s e. CC' % Y)
    r3a = D(w, A_, 'oveq12d', [D(w, A_, 'mul02d', [xc_], '( 0 x. %s ) = 0' % X), D(w, A_, 'mulm1d', [yc_], '( -u 1 x. %s ) = -u %s' % (Y, Y))], '( ( 0 x. %s ) - ( -u 1 x. %s ) ) = ( 0 - -u %s )' % (X, Y, Y))
    r3b = D(w, A_, 'eqtrd', [D(w, A_, 'subnegd', [cst(w, A_, '0cn', '0 e. CC'), yc_], '( 0 - -u %s ) = ( 0 + %s )' % (Y, Y)), D(w, A_, 'addlidd', [yc_], '( 0 + %s ) = %s' % (Y, Y))], '( 0 - -u %s ) = %s' % (Y, Y))
    r3 = D(w, A_, 'eqtrd', [r3a, r3b], '( ( 0 x. %s ) - ( -u 1 x. %s ) ) = %s' % (X, Y, Y))
    re_ = D(w, A_, 'eqtrd', [D(w, A_, 'eqtrd', [r1, r2], '( Re ` %s ) = ( ( 0 x. %s ) - ( -u 1 x. %s ) )' % (V, X, Y)), r3], '( Re ` %s ) = %s' % (V, Y))
    i1 = D(w, A_, 'immuld', [nic, cc], '( Im ` %s ) = ( ( ( Re ` -u _i ) x. %s ) + ( ( Im ` -u _i ) x. %s ) )' % (V, Y, X))
    i2 = D(w, A_, 'oveq12d', [D(w, A_, 'oveq1d', [rni], '( ( Re ` -u _i ) x. %s ) = ( 0 x. %s )' % (Y, Y)), D(w, A_, 'oveq1d', [ini], '( ( Im ` -u _i ) x. %s ) = ( -u 1 x. %s )' % (X, X))],
             '( ( ( Re ` -u _i ) x. %s ) + ( ( Im ` -u _i ) x. %s ) ) = ( ( 0 x. %s ) + ( -u 1 x. %s ) )' % (Y, X, Y, X))
    i3a = D(w, A_, 'oveq12d', [D(w, A_, 'mul02d', [yc_], '( 0 x. %s ) = 0' % Y), D(w, A_, 'mulm1d', [xc_], '( -u 1 x. %s ) = -u %s' % (X, X))], '( ( 0 x. %s ) + ( -u 1 x. %s ) ) = ( 0 + -u %s )' % (Y, X, X))
    i3 = D(w, A_, 'eqtrd', [i3a, D(w, A_, 'addlidd', [D(w, A_, 'negcld', [xc_], '-u %s e. CC' % X)], '( 0 + -u %s ) = -u %s' % (X, X))], '( ( 0 x. %s ) + ( -u 1 x. %s ) ) = -u %s' % (Y, X, X))
    im_ = D(w, A_, 'eqtrd', [D(w, A_, 'eqtrd', [i1, i2], '( Im ` %s ) = ( ( 0 x. %s ) + ( -u 1 x. %s ) )' % (V, Y, X)), i3], '( Im ` %s ) = -u %s' % (V, X))
    return re_, im_


# ---------------------------------------------------------------- zl3ftv
if __name__ == '__main__' and (not only or 'zl3ftv' in only):
    from zl3b_e3 import hol_rw
    w = W('zl3ftv', 'The integrals of the translated rotated Gaussian along the imaginary axis converge to ` -i K ^ P C0 / sqrt T `.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3ftv'])
    tp = w.s([], 'simpl1', '( %s -> T e. RR+ )' % ph); ar = w.s([], 'simpl2', '( %s -> A e. RR )' % ph); pp = w.s([], 'simpl3', '( %s -> P e. { 0 , 1 } )' % ph)
    jz = w.s([], 'simpr', '( %s -> j e. ZZ )' % ph)
    pn = p_nn0(w, ph, pp)
    icc = cst(w, ph, 'ax-icn', '_i e. CC')
    q = Q(w, ph, {'T': tp, 'A': ar, 'j': jz, 'P': pn, '_i': icc, '_pi': cst(w, ph, 'pirp', '_pi e. RR+')})
    tn0 = D(w, ph, 'rpne0d', [tp], 'T =/= 0')
    K = KAP
    kr = D(w, ph, 'redivcld', [D(w, ph, 'zred', [jz], 'j e. RR'), D(w, ph, 'rpred', [tp], 'T e. RR'), tn0], '%s e. RR' % K)
    q.cl.leaves[K] = kr if hasattr(q.cl, 'leaves') and isinstance(q.cl.leaves, dict) else None
    kc = D(w, ph, 'recnd', [kr], '%s e. CC' % K)
    nkr = D(w, ph, 'renegcld', [kr], '-u %s e. RR' % K)
    TRO = TRN(OMJ, SJ)
    # (2) HOL ( OMJ )
    bo = lambda v: gfbody('-u T', '0', K, 'P', v)
    hy = D(w, ph, 'syl', [w.s([w.s([D(w, ph, 'negcld', [q.c('T')], '-u T e. CC'), pn], 'jca', '( %s -> ( -u T e. CC /\\ P e. NN0 ) )' % ph),
                               w.s([cst(w, ph, '0cn', '0 e. CC'), kc], 'jca', '( %s -> ( 0 e. CC /\\ %s e. CC ) )' % (ph, K))], 'jca',
                              '( %s -> ( ( -u T e. CC /\\ P e. NN0 ) /\\ ( 0 e. CC /\\ %s e. CC ) ) )' % (ph, K)), w.inst('zl3hol')], HOLt(GF('-u T', '0', K, 'P')))
    hom = hol_rw(w, ph, hy, GF('-u T', '0', K, 'P'), OMJ, mpt_rw(w, ph, 'y', bo, 'w', bo, lambda Av: w.s([], 'eqidd', '( %s -> %s = %s )' % (Av, bo('y'), bo('y'))), g))
    omc = w.s([hom], 'simpld', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, OMJ))
    # (3) strip bound
    AK = '( abs ` %s )' % K; ANK = '( abs ` -u %s )' % K
    PT = '( _pi x. T )'
    Mc = '( ( 1 + ( 2 x. %s ) ) x. ( ( exp ` ( %s x. ( %s ^ 2 ) ) ) x. ( exp ` ( 1 / %s ) ) ) )' % (AK, PT, AK, PT)
    Acc = '( ( %s /\\ c e. CC ) /\\ ( abs ` ( Re ` c ) ) <_ %s )' % (ph, ANK)
    L2 = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Acc, f))
    cc_ = w.s([], 'simplr', '( %s -> c e. CC )' % Acc); crb = w.s([], 'simpr', '( %s -> ( abs ` ( Re ` c ) ) <_ %s )' % (Acc, ANK))
    kc2 = L2(kc, '%s e. CC' % K); kr2 = L2(kr, '%s e. RR' % K)
    ank = D(w, Acc, 'absnegd', [kc2], '%s = %s' % (ANK, AK))
    crk = D(w, Acc, 'breqtrd', [crb, ank], '( abs ` ( Re ` c ) ) <_ %s' % AK)
    V = '( -u _i x. c )'; U = '( c + %s )' % K
    rev, imv = reim_ni(w, Acc, 'c', cc_)
    RC, IC = '( Re ` c )', '( Im ` c )'
    arc = D(w, Acc, 'abscld', [D(w, Acc, 'recnd', [D(w, Acc, 'recld', [cc_], '%s e. RR' % RC)], '%s e. CC' % RC)], '( abs ` %s ) e. RR' % RC)
    aic = D(w, Acc, 'abscld', [D(w, Acc, 'recnd', [D(w, Acc, 'imcld', [cc_], '%s e. RR' % IC)], '%s e. CC' % IC)], '( abs ` %s ) e. RR' % IC)
    akr = D(w, Acc, 'abscld', [kc2], '%s e. RR' % AK)
    acr = D(w, Acc, 'abscld', [cc_], '( abs ` c ) e. RR')
    u1 = D(w, Acc, 'abstrid', [cc_, kc2], '( abs ` %s ) <_ ( ( abs ` c ) + %s )' % (U, AK))
    u2 = w.s([cc_, w.inst('abscrle')], 'syl', '( %s -> ( abs ` c ) <_ ( ( abs ` %s ) + ( abs ` %s ) ) )' % (Acc, RC, IC))
    aU = '( abs ` %s )' % U
    aur = D(w, Acc, 'abscld', [D(w, Acc, 'addcld', [cc_, kc2], '%s e. CC' % U)], '%s e. RR' % aU)
    ARV = '( abs ` ( Re ` %s ) )' % V
    arv = D(w, Acc, 'fveq2d', [rev], '%s = ( abs ` %s )' % (ARV, IC))
    ub0 = lin.linarith(w, Acc, [u1, u2, crk], '%s <_ ( ( abs ` %s ) + ( 2 x. %s ) )' % (aU, IC, AK), leaves={aU: aur, '( abs ` c )': acr, '( abs ` %s )' % RC: arc, '( abs ` %s )' % IC: aic, AK: akr})
    ub = D(w, Acc, 'breqtrrd', [ub0, D(w, Acc, 'oveq1d', [arv], '( %s + ( 2 x. %s ) ) = ( ( abs ` %s ) + ( 2 x. %s ) )' % (ARV, AK, IC, AK))], '%s <_ ( %s + ( 2 x. %s ) )' % (aU, ARV, AK))
    AIV = '( abs ` ( Im ` %s ) )' % V
    iv = D(w, Acc, 'eqtrd', [D(w, Acc, 'fveq2d', [imv], '%s = ( abs ` -u %s )' % (AIV, RC)), D(w, Acc, 'absnegd', [D(w, Acc, 'recnd', [D(w, Acc, 'recld', [cc_], '%s e. RR' % RC)], '%s e. CC' % RC)], '( abs ` -u %s ) = ( abs ` %s )' % (RC, RC))],
           '%s = ( abs ` %s )' % (AIV, RC))
    ivb = D(w, Acc, 'eqbrtrd', [iv, crk], '%s <_ %s' % (AIV, AK))
    tp2 = L2(tp, 'T e. RR+'); pp2 = L2(pp, 'P e. { 0 , 1 }')
    ic2 = cst(w, Acc, 'ax-icn', '_i e. CC')
    vc = D(w, Acc, 'mulcld', [D(w, Acc, 'negcld', [ic2], '-u _i e. CC'), cc_], '%s e. CC' % V)
    c2k = D(w, Acc, 'remulcld', [cst(w, Acc, '2re', '2 e. RR'), akr], '( 2 x. %s ) e. RR' % AK)
    c2k0 = D(w, Acc, 'mulge0d', [cst(w, Acc, '2re', '2 e. RR'), akr, cst(w, Acc, '0le2', '0 <_ 2'), D(w, Acc, 'absge0d', [kc2], '0 <_ %s' % AK)], '0 <_ ( 2 x. %s )' % AK)
    EV = '( exp ` -u ( %s x. ( %s ^ 2 ) ) )' % (PT, V)
    gcb = D(w, Acc, 'syl', [w.s([w.s([tp2, pp2], 'jca', '( %s -> ( T e. RR+ /\\ P e. { 0 , 1 } ) )' % Acc), w.s([D(w, Acc, 'addcld', [cc_, kc2], '%s e. CC' % U), vc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Acc, U, V)),
                                 w.s([w.s([c2k, akr], 'jca', '( %s -> ( ( 2 x. %s ) e. RR /\\ %s e. RR ) )' % (Acc, AK, AK)), w.s([c2k0, ub, ivb], '3jca', '( %s -> ( 0 <_ ( 2 x. %s ) /\\ %s <_ ( %s + ( 2 x. %s ) ) /\\ %s <_ %s ) )' % (Acc, AK, aU, ARV, AK, AIV, AK))],
                                     'jca', '( %s -> ( ( ( 2 x. %s ) e. RR /\\ %s e. RR ) /\\ ( 0 <_ ( 2 x. %s ) /\\ %s <_ ( %s + ( 2 x. %s ) ) /\\ %s <_ %s ) ) )' % (Acc, AK, AK, AK, aU, ARV, AK, AIV, AK))], '3jca',
                                '( %s -> ( ( T e. RR+ /\\ P e. { 0 , 1 } ) /\\ ( %s e. CC /\\ %s e. CC ) /\\ ( ( ( 2 x. %s ) e. RR /\\ %s e. RR ) /\\ ( 0 <_ ( 2 x. %s ) /\\ %s <_ ( %s + ( 2 x. %s ) ) /\\ %s <_ %s ) ) ) )'
                                % (Acc, U, V, AK, AK, AK, aU, ARV, AK, AIV, AK)), w.inst('zl3gcb')],
            '( abs ` ( ( %s ^ P ) x. %s ) ) <_ ( %s x. ( 2 ^c -u %s ) )' % (U, EV, Mc, ARV))
    # OMJ ` c = ( U ^ P ) x. EV
    omv = gfv(w, Acc, '-u T', '0', K, 'P', 'c', cc_, g, 'w')
    qa = Q(w, Acc, {'T': tp2, 'c': cc_, '_i': ic2, '_pi': cst(w, Acc, 'pirp', '_pi e. RR+')})
    c0 = qa.eq('addridd', ['c'], '( c + 0 )', 'c')
    v2 = qa.chain('( %s ^ 2 )' % V, [(qa.eq('sqmuld', ['-u _i', 'c'], '( %s ^ 2 )' % V, '( ( -u _i ^ 2 ) x. ( c ^ 2 ) )'), '( ( -u _i ^ 2 ) x. ( c ^ 2 ) )'),
                                     (qa.d('oveq1d', [qa.d('eqtrd', [qa.eq('sqnegd', ['_i'], '( -u _i ^ 2 )', '( _i ^ 2 )'), cst(w, Acc, 'i2', '( _i ^ 2 ) = -u 1')], '( -u _i ^ 2 ) = -u 1')],
                                            '( ( -u _i ^ 2 ) x. ( c ^ 2 ) ) = ( -u 1 x. ( c ^ 2 ) )'), '( -u 1 x. ( c ^ 2 ) )'),
                                     (qa.eq('mulm1d', ['( c ^ 2 )'], '( -u 1 x. ( c ^ 2 ) )', '-u ( c ^ 2 )'), '-u ( c ^ 2 )')])
    ea = qa.chain('( ( _pi x. -u T ) x. ( ( c + 0 ) ^ 2 ) )', [
        (qa.d('oveq12d', [qa.eq('mulneg2d', ['_pi', 'T'], '( _pi x. -u T )', '-u %s' % PT), qa.d('oveq1d', [c0], '( ( c + 0 ) ^ 2 ) = ( c ^ 2 )')], '( ( _pi x. -u T ) x. ( ( c + 0 ) ^ 2 ) ) = ( -u %s x. ( c ^ 2 ) )' % PT),
         '( -u %s x. ( c ^ 2 ) )' % PT),
        (qa.d('eqtr4d', [qa.eq('mulneg1d', [PT, '( c ^ 2 )'], '( -u %s x. ( c ^ 2 ) )' % PT, '-u ( %s x. ( c ^ 2 ) )' % PT), qa.eq('mulneg2d', [PT, '( c ^ 2 )'], '( %s x. -u ( c ^ 2 ) )' % PT, '-u ( %s x. ( c ^ 2 ) )' % PT)],
               '( -u %s x. ( c ^ 2 ) ) = ( %s x. -u ( c ^ 2 ) )' % (PT, PT)), '( %s x. -u ( c ^ 2 ) )' % PT),
        (qa.d('oveq2d', [qa.sym(v2, '( %s ^ 2 )' % V, '-u ( c ^ 2 )')], '( %s x. -u ( c ^ 2 ) ) = ( %s x. ( %s ^ 2 ) )' % (PT, PT, V)), '( %s x. ( %s ^ 2 ) )' % (PT, V))])
    ev = qa.d('fveq2d', [qa.d('negeqd', [ea], '-u ( ( _pi x. -u T ) x. ( ( c + 0 ) ^ 2 ) ) = -u ( %s x. ( %s ^ 2 ) )' % (PT, V))], '( exp ` -u ( ( _pi x. -u T ) x. ( ( c + 0 ) ^ 2 ) ) ) = %s' % EV)
    omv2 = qa.d('eqtrd', [omv, qa.d('oveq2d', [ev], '%s = ( ( %s ^ P ) x. %s )' % (bo('c'), U, EV))], '( %s ` c ) = ( ( %s ^ P ) x. %s )' % (OMJ, U, EV))
    sbc = qa.d('breqtrd', [qa.d('eqbrtrd', [qa.d('fveq2d', [omv2], '( abs ` ( %s ` c ) ) = ( abs ` ( ( %s ^ P ) x. %s ) )' % (OMJ, U, EV)), gcb], '( abs ` ( %s ` c ) ) <_ ( %s x. ( 2 ^c -u %s ) )' % (OMJ, Mc, ARV)),
                           qa.d('oveq2d', [qa.d('oveq2d', [qa.d('negeqd', [arv], '-u %s = -u ( abs ` %s )' % (ARV, IC))], '( 2 ^c -u %s ) = ( 2 ^c -u ( abs ` %s ) )' % (ARV, IC))],
                                '( %s x. ( 2 ^c -u %s ) ) = ( %s x. ( 2 ^c -u ( abs ` %s ) ) )' % (Mc, ARV, Mc, IC))], '( abs ` ( %s ` c ) ) <_ ( %s x. ( 2 ^c -u ( abs ` %s ) ) )' % (OMJ, Mc, IC))
    SBa = 'A. c e. CC ( ( abs ` ( Re ` c ) ) <_ %s -> ( abs ` ( %s ` c ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) )' % (ANK, OMJ, Mc)
    sba = w.s([w.s([sbc], 'ex', '( ( %s /\\ c e. CC ) -> ( ( abs ` ( Re ` c ) ) <_ %s -> ( abs ` ( %s ` c ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Im ` c ) ) ) ) ) )' % (ph, ANK, OMJ, Mc))], 'ralrimiva', '( %s -> %s )' % (ph, SBa))
    mcr = q.cl.mem(Mc, 'RR') if False else None
    mcr = D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), D(w, ph, 'remulcld', [cst(w, ph, '2re', '2 e. RR'), D(w, ph, 'abscld', [kc], '%s e. RR' % AK)], '( 2 x. %s ) e. RR' % AK)], '( 1 + ( 2 x. %s ) ) e. RR' % AK),
                                D(w, ph, 'remulcld', [D(w, ph, 'reefcld', [D(w, ph, 'remulcld', [D(w, ph, 'rpred', [D(w, ph, 'rpmulcld', [cst(w, ph, 'pirp', '_pi e. RR+'), tp], '%s e. RR+' % PT)], '%s e. RR' % PT),
                                                                                                  D(w, ph, 'resqcld', [D(w, ph, 'abscld', [kc], '%s e. RR' % AK)], '( %s ^ 2 ) e. RR' % AK)], '( %s x. ( %s ^ 2 ) ) e. RR' % (PT, AK))], '( exp ` ( %s x. ( %s ^ 2 ) ) ) e. RR' % (PT, AK)),
                                                      D(w, ph, 'reefcld', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), D(w, ph, 'rpmulcld', [cst(w, ph, 'pirp', '_pi e. RR+'), tp], '%s e. RR+' % PT)], '( 1 / %s ) e. RR' % PT)], '( exp ` ( 1 / %s ) ) e. RR' % PT)],
                                  '( ( exp ` ( %s x. ( %s ^ 2 ) ) ) x. ( exp ` ( 1 / %s ) ) ) e. RR' % (PT, AK, PT))], '%s e. RR' % Mc)
    # (4) zl3csh
    csh = D(w, ph, 'syl', [w.s([w.s([nkr, ar], 'jca', '( %s -> ( -u %s e. RR /\\ A e. RR ) )' % (ph, K)), w.s([hom, w.s([mcr, sba], 'jca', '( %s -> ( %s e. RR /\\ %s ) )' % (ph, Mc, SBa))], 'jca', '( %s -> ( %s /\\ ( %s e. RR /\\ %s ) ) )' % (ph, HOLt(OMJ), Mc, SBa))],
                               'jca', '( %s -> ( ( -u %s e. RR /\\ A e. RR ) /\\ ( %s /\\ ( %s e. RR /\\ %s ) ) ) )' % (ph, K, HOLt(OMJ), Mc, SBa)), w.inst('zl3csh')],
            '( t e. RR+ |-> %s ) ~~>r %s' % (LT(TRO, '0', 't'), VL(OMJ, '0')))
    # (5) zl3ftw
    VW = '( ( %s ^ P ) x. ( %s / ( sqrt ` T ) ) )' % (K, C0)
    ftw = w.s([D(w, ph, 'syl3anc', [tp, pp, kr, w.inst('zl3ftw')], '( ( t e. RR+ |-> %s ) ~~>r %s /\\ %s e. CC )' % (LT(OMJ, '0', 't'), VW, C0))], 'simpld', '( %s -> ( t e. RR+ |-> %s ) ~~>r %s )' % (ph, LT(OMJ, '0', 't'), VW))
    vom = val_of(w, ph, '( t e. RR+ |-> %s )' % LT(OMJ, '0', 't'), VW, ftw, lt_cl(w, ph, OMJ, omc))
    # (7) continuity of TRO and zl3vl0
    bs = lambda v: '( %s ` ( %s + %s ) )' % (OMJ, v, SJ)
    SK = '( %s + %s )' % (SJ, K)
    bg = lambda v: gfbody('-u T', SJ, SK, 'P', v)
    hy2 = D(w, ph, 'syl', [w.s([w.s([D(w, ph, 'negcld', [q.c('T')], '-u T e. CC'), pn], 'jca', '( %s -> ( -u T e. CC /\\ P e. NN0 ) )' % ph),
                                w.s([q.c(SJ), D(w, ph, 'addcld', [q.c(SJ), kc], '%s e. CC' % SK)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ph, SJ, SK))], 'jca',
                               '( %s -> ( ( -u T e. CC /\\ P e. NN0 ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (ph, SJ, SK)), w.inst('zl3hol')], HOLt(GF('-u T', SJ, SK, 'P')))
    def pt_tro(Av):
        yc = w.s([], 'simpr', '( %s -> y e. CC )' % Av)
        qy = Q(w, Av, {'T': w.s([tp], 'adantr', '( %s -> T e. RR+ )' % Av), 'A': w.s([ar], 'adantr', '( %s -> A e. RR )' % Av), 'j': w.s([jz], 'adantr', '( %s -> j e. ZZ )' % Av),
                       'P': w.s([pn], 'adantr', '( %s -> P e. NN0 )' % Av), 'y': yc, '_i': cst(w, Av, 'ax-icn', '_i e. CC'), '_pi': cst(w, Av, 'pirp', '_pi e. RR+')})
        YS = '( y + %s )' % SJ
        v_ = gfv(w, Av, '-u T', '0', K, 'P', YS, qy.c(YS), g, 'w')
        a_ = qy.eq('addassd', ['y', SJ, K], '( %s + %s )' % (YS, K), '( y + %s )' % SK)
        b_ = qy.eq('addridd', [YS], '( %s + 0 )' % YS, YS)
        e_ = qy.d('oveq12d', [qy.d('oveq1d', [a_], '( ( %s + %s ) ^ P ) = ( ( y + %s ) ^ P )' % (YS, K, SK)),
                              qy.d('fveq2d', [qy.d('negeqd', [qy.d('oveq2d', [qy.d('oveq1d', [b_], '( ( %s + 0 ) ^ 2 ) = ( %s ^ 2 )' % (YS, YS))], '( ( _pi x. -u T ) x. ( ( %s + 0 ) ^ 2 ) ) = ( ( _pi x. -u T ) x. ( %s ^ 2 ) )' % (YS, YS))],
                                                      '-u ( ( _pi x. -u T ) x. ( ( %s + 0 ) ^ 2 ) ) = -u ( ( _pi x. -u T ) x. ( %s ^ 2 ) )' % (YS, YS))],
                                     '( exp ` -u ( ( _pi x. -u T ) x. ( ( %s + 0 ) ^ 2 ) ) ) = ( exp ` -u ( ( _pi x. -u T ) x. ( %s ^ 2 ) ) )' % (YS, YS))],
                    '%s = %s' % (bo(YS), bg('y')))
        return qy.d('eqtrd', [v_, e_], '%s = %s' % (bs('y'), bg('y')))
    eqt = mpt_rw(w, ph, 'y', bs, 'y', bg, pt_tro, g)
    trc = w.s([hol_rw(w, ph, hy2, TRO, GF('-u T', SJ, SK, 'P'), eqt) if False else
               D(w, ph, 'mpbird', [w.s([hy2], 'simpld', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, GF('-u T', SJ, SK, 'P'))), D(w, ph, 'eleq1d', [eqt], '( %s e. ( CC -cn-> CC ) <-> %s e. ( CC -cn-> CC ) )' % (TRO, GF('-u T', SJ, SK, 'P')))],
                 '%s e. ( CC -cn-> CC )' % TRO)], 'idi', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, TRO))
    # line bound for TRO
    Ab = '( %s /\\ b e. RR )' % ph
    br = w.s([], 'simpr', '( %s -> b e. RR )' % Ab)
    La = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Ab, f))
    qb = Q(w, Ab, {'T': La(tp, 'T e. RR+'), 'A': La(ar, 'A e. RR'), 'j': La(jz, 'j e. ZZ'), 'P': La(pn, 'P e. NN0'), 'b': br, '_i': cst(w, Ab, 'ax-icn', '_i e. CC'), '_pi': cst(w, Ab, 'pirp', '_pi e. RR+')})
    fti = D(w, Ab, 'syl', [w.s([w.s([La(tp, 'T e. RR+'), La(ar, 'A e. RR'), La(pp, 'P e. { 0 , 1 }')], '3jca', '( %s -> %s )' % (Ab, TPAR)), w.s([La(jz, 'j e. ZZ'), br], 'jca', '( %s -> ( j e. ZZ /\\ b e. RR ) )' % Ab)], 'jca',
                               '( %s -> ( %s /\\ ( j e. ZZ /\\ b e. RR ) ) )' % (Ab, TPAR)), w.inst('zl3fti')],
            '( %s x. ( %s ` %s ) ) = ( ( %s ` b ) x. ( exp ` -u ( ( 2 x. ( _i x. _pi ) ) x. ( j x. b ) ) ) )' % (CSTJ, TRO, CP('0', 'b'), FF))
    TB = '( %s ` %s )' % (TRO, CP('0', 'b'))
    EB = '( exp ` -u ( ( 2 x. ( _i x. _pi ) ) x. ( j x. b ) ) )'
    FB = '( %s ` b )' % FF
    # | EB | = 1
    TIP = '( 2 x. ( _i x. _pi ) )'; JB = '( j x. b )'; RB = '-u ( ( 2 x. _pi ) x. %s )' % JB
    r1 = qb.chain('( %s x. %s )' % (TIP, JB), [(qb.d('oveq1d', [qb.eq('mul12d', ['2', '_i', '_pi'], TIP, '( _i x. ( 2 x. _pi ) )')], '( %s x. %s ) = ( ( _i x. ( 2 x. _pi ) ) x. %s )' % (TIP, JB, JB)), '( ( _i x. ( 2 x. _pi ) ) x. %s )' % JB),
                                               (qb.eq('mulassd', ['_i', '( 2 x. _pi )', JB], '( ( _i x. ( 2 x. _pi ) ) x. %s )' % JB, '( _i x. ( ( 2 x. _pi ) x. %s ) )' % JB), '( _i x. ( ( 2 x. _pi ) x. %s ) )' % JB)])
    r2 = qb.chain('-u ( %s x. %s )' % (TIP, JB), [(qb.d('negeqd', [r1], '-u ( %s x. %s ) = -u ( _i x. ( ( 2 x. _pi ) x. %s ) )' % (TIP, JB, JB)), '-u ( _i x. ( ( 2 x. _pi ) x. %s ) )' % JB),
                                                  (qb.sym(qb.eq('mulneg2d', ['_i', '( ( 2 x. _pi ) x. %s )' % JB], '( _i x. %s )' % RB, '-u ( _i x. ( ( 2 x. _pi ) x. %s ) )' % JB), '( _i x. %s )' % RB, '-u ( _i x. ( ( 2 x. _pi ) x. %s ) )' % JB), '( _i x. %s )' % RB)])
    rbr = qb.cl.mem(RB, 'RR')
    aeb = qb.d('eqtrd', [qb.d('fveq2d', [qb.d('fveq2d', [r2], '%s = ( exp ` ( _i x. %s ) )' % (EB, RB))], '( abs ` %s ) = ( abs ` ( exp ` ( _i x. %s ) ) )' % (EB, RB)), w.s([rbr, w.inst('absefi')], 'syl', '( %s -> ( abs ` ( exp ` ( _i x. %s ) ) ) = 1 )' % (Ab, RB))],
                '( abs ` %s ) = 1' % EB)
    # | CSTJ | x. | TB | = | FB |
    csc = qb.c(CSTJ); tbc = w.s([w.s([La(trc, '%s e. ( CC -cn-> CC )' % TRO), w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (Ab, TRO)), qb.c(CP('0', 'b'))], 'ffvelcdmd', '( %s -> %s e. CC )' % (Ab, TB))
    fbc = qb.c(FB) if False else None
    ffv = D(w, Ab, 'eqeltrrd', [fti, D(w, Ab, 'mulcld', [csc, tbc], '( %s x. %s ) e. CC' % (CSTJ, TB))], '( %s x. %s ) e. CC' % (FB, EB))
    a1 = qb.d('eqtr3d', [qb.d('fveq2d', [fti], '( abs ` ( %s x. %s ) ) = ( abs ` ( %s x. %s ) )' % (CSTJ, TB, FB, EB)), qb.d('absmuld', [csc, tbc], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CSTJ, TB, CSTJ, TB))],
                '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (FB, EB, CSTJ, TB)) if False else None
    ebc = qb.c(EB)
    fbc = D(w, Ab, 'syl', [br, w.s([], 'IGNORE', 'x')], 'x') if False else None
    # FB e. CC from FF : CC --> CC
    hff = D(w, Ab, 'syl', [w.s([w.s([La(pn, 'P e. NN0'), w.s([], 'IGNORE', 'x')], 'IGNORE', 'x')], 'IGNORE', 'x')], 'x') if False else None
    ffc = D(w, Ab, 'syl', [w.s([w.s([D(w, Ab, 'rpcnd', [La(tp, 'T e. RR+')], 'T e. CC') if False else qb.c('T'), La(pn, 'P e. NN0')], 'jca', '( %s -> ( T e. CC /\\ P e. NN0 ) )' % Ab) if False else
                                w.s([qb.c('T'), La(pn, 'P e. NN0')], 'jca', '( %s -> ( T e. CC /\\ P e. NN0 ) )' % Ab),
                                w.s([qb.c('A'), qb.c('A')], 'jca', '( %s -> ( A e. CC /\\ A e. CC ) )' % Ab)], 'jca', '( %s -> ( ( T e. CC /\\ P e. NN0 ) /\\ ( A e. CC /\\ A e. CC ) ) )' % Ab), w.inst('zl3hol')], HOLt(FF))
    fbc = D(w, Ab, 'ffvelcdmd', [w.s([w.s([ffc], 'simpld', '( %s -> %s e. ( CC -cn-> CC ) )' % (Ab, FF)), w.inst('cncff')], 'syl', '( %s -> %s : CC --> CC )' % (Ab, FF)), qb.c('b')], '%s e. CC' % FB)
    ab1 = qb.d('eqtr3d', [qb.d('absmuld', [csc, tbc], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CSTJ, TB, CSTJ, TB)),
                          qb.d('eqtrd', [qb.d('fveq2d', [fti], '( abs ` ( %s x. %s ) ) = ( abs ` ( %s x. %s ) )' % (CSTJ, TB, FB, EB)),
                                         qb.d('eqtrd', [qb.d('absmuld', [fbc, ebc], '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (FB, EB, FB, EB)),
                                                        qb.d('eqtrd', [qb.d('oveq2d', [aeb], '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. 1 )' % (FB, EB, FB)), qb.d('mulridd', [qb.d('recnd', [qb.d('abscld', [fbc], '( abs ` %s ) e. RR' % FB)], '( abs ` %s ) e. CC' % FB)], '( ( abs ` %s ) x. 1 ) = ( abs ` %s )' % (FB, FB))],
                                                               '( ( abs ` %s ) x. ( abs ` %s ) ) = ( abs ` %s )' % (FB, EB, FB))], '( abs ` ( %s x. %s ) ) = ( abs ` %s )' % (FB, EB, FB))], '( abs ` ( %s x. %s ) ) = ( abs ` %s )' % (CSTJ, TB, FB))],
                 '( ( abs ` %s ) x. ( abs ` %s ) ) = ( abs ` %s )' % (CSTJ, TB, FB))
    # zl3fb at z = b
    fb = w.s([w.s([La(tp, 'T e. RR+'), La(ar, 'A e. RR'), La(pp, 'P e. { 0 , 1 }')], '3jca', '( %s -> %s )' % (Ab, TPAR)), w.inst('zl3fb')], 'syl', '( %s -> ( %s e. RR+ /\\ A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( %s ` z ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) ) ) )' % (Ab, KF, FF, KF))
    kfp = w.s([fb], 'simpld', '( %s -> %s e. RR+ )' % (Ab, KF))
    FBZ = lambda z: '( ( abs ` ( Im ` %s ) ) <_ 1 -> ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` %s ) ) ) ) )' % (z, FF, z, KF, z)
    Ez = 'z = b'
    iz = w.s([], 'id', '( %s -> %s )' % (Ez, Ez))
    stz, _ = congr.wff_congruence(FBZ('z'), {'z': 'b'}, Ez, {'z': iz}, g)
    w.lines.extend(g.lines); g.lines = []
    fbb = w.s([stz, w.s([fb], 'simprd', '( %s -> A. z e. CC %s )' % (Ab, FBZ('z'))), qb.c('b')], 'rspcdva', '( %s -> %s )' % (Ab, FBZ('b')))
    imb = qb.d('reim0d', [br], '( Im ` b ) = 0'); reb = qb.d('rered', [br], '( Re ` b ) = b')
    ib0 = qb.d('eqbrtrd', [qb.d('eqtrd', [qb.d('fveq2d', [imb], '( abs ` ( Im ` b ) ) = ( abs ` 0 )'), cst(w, Ab, 'abs0', '( abs ` 0 ) = 0')], '( abs ` ( Im ` b ) ) = 0'), cst(w, Ab, '0le1', '0 <_ 1')], '( abs ` ( Im ` b ) ) <_ 1')
    fbl = qb.d('breqtrd', [qb.d('mpd', [ib0, fbb], '( abs ` %s ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` b ) ) ) )' % (FB, KF)),
                           qb.d('oveq2d', [qb.d('oveq2d', [qb.d('negeqd', [qb.d('fveq2d', [reb], '( abs ` ( Re ` b ) ) = ( abs ` b )')], '-u ( abs ` ( Re ` b ) ) = -u ( abs ` b )')], '( 2 ^c -u ( abs ` ( Re ` b ) ) ) = ( 2 ^c -u ( abs ` b ) )')],
                                '( %s x. ( 2 ^c -u ( abs ` ( Re ` b ) ) ) ) = ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (KF, KF))], '( abs ` %s ) <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (FB, KF))
    AC = '( abs ` %s )' % CSTJ
    csn0 = qb.d('mulne0d', [qb.c(NI) if False else qb.c('( -u _i ^ P )'), qb.d('expne0d', [qb.c('-u _i'), qb.d('negne0d', [qb.c('_i'), cst(w, Ab, 'ine0', '_i =/= 0')], '-u _i =/= 0') if False else
                                                                                  qb.d('negne0d', [cst(w, Ab, 'ine0', '_i =/= 0')], '-u _i =/= 0'), La(pn, 'P e. NN0') if False else w.s([La(pn, 'P e. NN0'), w.inst('nn0zd')], 'IGNORE', 'x') if False else qb.d('nn0zd', [La(pn, 'P e. NN0')], 'P e. ZZ')],
                                                  '( -u _i ^ P ) =/= 0'),
                            qb.c(EJ), qb.d('mulne0d', [qb.c('( exp ` -u ( _pi x. ( ( j ^ 2 ) / T ) ) )'), qb.d('efne0d', [qb.c('-u ( _pi x. ( ( j ^ 2 ) / T ) )')], '( exp ` -u ( _pi x. ( ( j ^ 2 ) / T ) ) ) =/= 0'),
                                                       qb.c('( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) ) )'), qb.d('efne0d', [qb.c('( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) )')], '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) ) ) =/= 0')],
                                               '%s =/= 0' % EJ)], '%s =/= 0' % CSTJ)
    acp = qb.d('absrpcld', [csc, csn0], '%s e. RR+' % AC)
    TBa = '( abs ` %s )' % TB
    YB = '( %s x. ( 2 ^c -u ( abs ` b ) ) )' % KF
    ybr = qb.cl.mem(YB, 'RR') if False else D(w, Ab, 'remulcld', [D(w, Ab, 'rpred', [kfp], '%s e. RR' % KF), D(w, Ab, 'rpred', [D(w, Ab, 'rpcxpcld', [cst(w, Ab, '2rp', '2 e. RR+'), D(w, Ab, 'renegcld', [D(w, Ab, 'abscld', [qb.c('b')], '( abs ` b ) e. RR')], '-u ( abs ` b ) e. RR')], '( 2 ^c -u ( abs ` b ) ) e. RR+')], '( 2 ^c -u ( abs ` b ) ) e. RR')], '%s e. RR' % YB)
    l1 = qb.d('eqbrtrd', [ab1, fbl], '( %s x. %s ) <_ %s' % (AC, TBa, YB))
    tbr = qb.d('abscld', [tbc], '%s e. RR' % TBa)
    l2 = qb.d('lediv1dd', [qb.d('remulcld', [qb.d('rpred', [acp], '%s e. RR' % AC), tbr], '( %s x. %s ) e. RR' % (AC, TBa)), ybr, acp, l1], '( ( %s x. %s ) / %s ) <_ ( %s / %s )' % (AC, TBa, AC, YB, AC))
    l3 = qb.d('divcan3d', [qb.d('recnd', [tbr], '%s e. CC' % TBa), qb.d('rpcnd', [acp], '%s e. CC' % AC), qb.d('rpne0d', [acp], '%s =/= 0' % AC)], '( ( %s x. %s ) / %s ) = %s' % (AC, TBa, AC, TBa))
    M2 = '( %s / %s )' % (KF, AC)
    l4 = qb.d('div23d', [qb.d('rpcnd', [kfp], '%s e. CC' % KF), qb.d('recnd', [D(w, Ab, 'rpred', [D(w, Ab, 'rpcxpcld', [cst(w, Ab, '2rp', '2 e. RR+'), D(w, Ab, 'renegcld', [D(w, Ab, 'abscld', [qb.c('b')], '( abs ` b ) e. RR')], '-u ( abs ` b ) e. RR')], '( 2 ^c -u ( abs ` b ) ) e. RR+')], '( 2 ^c -u ( abs ` b ) ) e. RR')], '( 2 ^c -u ( abs ` b ) ) e. CC'),
                         qb.d('rpcnd', [acp], '%s e. CC' % AC), qb.d('rpne0d', [acp], '%s =/= 0' % AC)], '( %s / %s ) = ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (YB, AC, M2))
    lb = qb.d('breqtrd', [qb.d('eqbrtrrd', [l3, l2], '%s <_ ( %s / %s )' % (TBa, YB, AC)), l4], '%s <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (TBa, M2))
    BLT = 'A. b e. RR ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (TRO, CP('0', 'b'), M2)
    blt = w.s([lb], 'ralrimiva', '( %s -> %s )' % (ph, BLT))
    # M2 e. RR: needs | CSTJ | in the outer context; derive from the b = 0 instance is overkill -- redo in ph
    csc0 = q.c(CSTJ)
    csn00 = D(w, ph, 'mulne0d', [q.c('( -u _i ^ P )'), D(w, ph, 'expne0d', [q.c('-u _i'), D(w, ph, 'negne0d', [cst(w, ph, 'ine0', '_i =/= 0')], '-u _i =/= 0'), D(w, ph, 'nn0zd', [pn], 'P e. ZZ')], '( -u _i ^ P ) =/= 0'),
                                 q.c(EJ), D(w, ph, 'mulne0d', [q.c('( exp ` -u ( _pi x. ( ( j ^ 2 ) / T ) ) )'), D(w, ph, 'efne0d', [q.c('-u ( _pi x. ( ( j ^ 2 ) / T ) )')], '( exp ` -u ( _pi x. ( ( j ^ 2 ) / T ) ) ) =/= 0'),
                                                               q.c('( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) ) )'), D(w, ph, 'efne0d', [q.c('( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) )')], '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) ) ) =/= 0')],
                                   '%s =/= 0' % EJ)], '%s =/= 0' % CSTJ)
    kfp0 = w.s([w.s([tp, ar, pp], '3jca', '( %s -> %s )' % (ph, TPAR)), w.inst('zl3fb')], 'syl', '( %s -> ( %s e. RR+ /\\ A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( %s ` z ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` z ) ) ) ) ) ) )' % (ph, KF, FF, KF))
    m2r = D(w, ph, 'rerpdivcld', [D(w, ph, 'rpred', [w.s([kfp0], 'simpld', '( %s -> %s e. RR+ )' % (ph, KF))], '%s e. RR' % KF), D(w, ph, 'absrpcld', [csc0, csn00], '%s e. RR+' % AC)], '%s e. RR' % M2)
    VLI = '( ~~>r ` %s )' % ITR
    vl0 = D(w, ph, 'syl', [w.s([w.s([trc, m2r], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ %s e. RR ) )' % (ph, TRO, M2)), blt], 'jca', '( %s -> ( ( %s e. ( CC -cn-> CC ) /\\ %s e. RR ) /\\ %s ) )' % (ph, TRO, M2, BLT)), w.inst('zl3vl0')],
            '( ( %s e. dom ~~>r /\\ %s e. CC ) /\\ %s = ( _i x. %s ) )' % (ITR, VLI, VL(TRO, '0'), VLI))
    # (6) VL ( TRO , 0 ) = VL ( OMJ , 0 )
    vtr = val_of(w, ph, '( t e. RR+ |-> %s )' % LT(TRO, '0', 't'), VL(OMJ, '0'), csh, lt_cl(w, ph, TRO, trc))
    # i x. VLI = VW
    iv_ = D(w, ph, 'eqtrd', [D(w, ph, 'eqtr3d', [w.s([vl0], 'simprd', '( %s -> %s = ( _i x. %s ) )' % (ph, VL(TRO, '0'), VLI)), vtr], '( _i x. %s ) = %s' % (VLI, VL(OMJ, '0'))), vom], '( _i x. %s ) = %s' % (VLI, VW))
    vlic = w.s([w.s([vl0], 'simpld', '( %s -> ( %s e. dom ~~>r /\\ %s e. CC ) )' % (ph, ITR, VLI))], 'simprd', '( %s -> %s e. CC )' % (ph, VLI))
    lam = D(w, ph, 'eqtr3d', [mi(w, ph, VLI, vlic), D(w, ph, 'oveq2d', [iv_], '( -u _i x. ( _i x. %s ) ) = ( -u _i x. %s )' % (VLI, VW))], '%s = ( -u _i x. %s )' % (VLI, VW))
    dm = w.s([w.s([vl0], 'simpld', '( %s -> ( %s e. dom ~~>r /\\ %s e. CC ) )' % (ph, ITR, VLI))], 'simpld', '( %s -> %s e. dom ~~>r )' % (ph, ITR))
    # ITR : RR+ --> CC
    At = '( %s /\\ t e. RR+ )' % ph
    tt = w.s([], 'simpr', '( %s -> t e. RR+ )' % At)
    pre = w.s([w.s([cst(w, At, '0re', '0 e. RR'), tt], 'jca', '( %s -> ( 0 e. RR /\\ t e. RR+ ) )' % At),
               w.s([w.s([trc], 'adantr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At, TRO)),
                    D(w, At, 'syl2anc', [D(w, At, 'addcld', [cst(w, At, '0cn', '0 e. CC'), D(w, At, 'mulcld', [cst(w, At, 'ax-icn', '_i e. CC'), D(w, At, 'negcld', [D(w, At, 'rpcnd', [tt], 't e. CC')], '-u t e. CC')], '( _i x. -u t ) e. CC')], '%s e. CC' % CP('0', '-u t')),
                                         D(w, At, 'addcld', [cst(w, At, '0cn', '0 e. CC'), D(w, At, 'mulcld', [cst(w, At, 'ax-icn', '_i e. CC'), D(w, At, 'rpcnd', [tt], 't e. CC')], '( _i x. t ) e. CC')], '%s e. CC' % CP('0', 't')), w.inst('csegcl')],
                      '( %s cseg %s ) C_ CC' % (CP('0', '-u t'), CP('0', 't')))], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (At, TRO, CP('0', '-u t'), CP('0', 't')))],
              'jca', '( %s -> ( ( 0 e. RR /\\ t e. RR+ ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At, TRO, CP('0', '-u t'), CP('0', 't')))
    UL = '( u e. ( -u t (,) t ) |-> ( %s ` %s ) )' % (TRO, CP('0', 'u'))
    lv = D(w, At, 'syl', [pre, w.inst('z6lvert')], '( %s e. L^1 /\\ %s = ( _i x. S. ( -u t (,) t ) ( %s ` %s ) _d u ) )' % (UL, LT(TRO, '0', 't'), TRO, CP('0', 'u')))
    Eux = 'u = x'
    iux = w.s([], 'id', '( %s -> %s )' % (Eux, Eux))
    stu, _ = congr.congruence('( %s ` %s )' % (TRO, CP('0', 'u')), {'u': 'x'}, Eux, {'u': iux}, g)
    w.lines.extend(g.lines); g.lines = []
    XL = '( x e. ( -u t (,) t ) |-> ( %s ` %s ) )' % (TRO, CP('0', 'x'))
    cbu = w.s([stu], 'cbvmptv', '%s = %s' % (UL, XL))
    l1x = D(w, At, 'eqeltrrd', [w.s([cbu], 'a1i', '( %s -> %s = %s )' % (At, UL, XL)), w.s([lv], 'simpld', '( %s -> %s e. L^1 )' % (At, UL))], '%s e. L^1' % XL)
    Ax = '( %s /\\ x e. ( -u t (,) t ) )' % At
    itc = w.s([cst(w, Ax, 'fvex', '( %s ` %s ) e. _V' % (TRO, CP('0', 'x'))), l1x], 'itgcl', '( %s -> S. ( -u t (,) t ) ( %s ` %s ) _d x e. CC )' % (At, TRO, CP('0', 'x')))
    ff = w.s([itc], 'fmptd', '( %s -> %s : RR+ --> CC )' % (ph, ITR))
    sup = cst(w, ph, 'rpsup', 'sup ( RR+ , RR* , < ) = +oo')
    rv = D(w, ph, 'mpbid', [dm, w.s([ff, sup], 'rlimdm', '( %s -> ( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) ) )' % (ph, ITR, ITR, ITR))], '%s ~~>r %s' % (ITR, VLI))
    w.qed([rv, lam], 'breqtrd', S['zl3ftv'])
    go(w, only)


class Prod:
    """equalities between products of the same atoms (commutativity/associativity of x. over CC)"""
    def __init__(self, w, ph, mems):
        self.w, self.ph, self.mems = w, ph, dict(mems)

    @staticmethod
    def split(e):
        t = e.split()
        if len(t) < 5 or t[0] != '(' or t[-1] != ')':
            return None
        d = 0
        for i in range(1, len(t) - 1):
            if t[i] == '(':
                d += 1
            elif t[i] == ')':
                d -= 1
            elif d == 0 and t[i] == 'x.':
                return ' '.join(t[1:i]), ' '.join(t[i + 1:-1])
        return None

    def mem(self, e):
        if e in self.mems:
            return self.mems[e]
        sp = self.split(e)
        assert sp, 'no membership for atom ' + e
        st = D(self.w, self.ph, 'mulcld', [self.mem(sp[0]), self.mem(sp[1])], '%s e. CC' % e)
        self.mems[e] = st
        return st

    def atoms(self, e):
        sp = self.split(e)
        return self.atoms(sp[0]) + self.atoms(sp[1]) if sp else [e]

    @staticmethod
    def canon(lst):
        return lst[0] if len(lst) == 1 else '( %s x. %s )' % (lst[0], Prod.canon(lst[1:]))

    def eq(self, a, b, st):
        return st

    def trans(self, e, pairs):
        """pairs: [(step or None, rhs)]; returns step ( ph -> e = last ) or None"""
        cur = None
        for st, r in pairs:
            if st is None:
                continue
            cur = st if cur is None else D(self.w, self.ph, 'eqtrd', [cur, st], '%s = %s' % (e, r))
        return cur

    def insert(self, a, ylst):
        """( a x. canon(y) ) = canon(sorted insert)"""
        y = self.canon(ylst)
        e = '( %s x. %s )' % (a, y)
        if len(ylst) == 1:
            b = ylst[0]
            if a <= b:
                return None, [a, b]
            return D(self.w, self.ph, 'mulcomd', [self.mem(a), self.mem(b)], '%s = ( %s x. %s )' % (e, b, a)), [b, a]
        b, yr = ylst[0], ylst[1:]
        if a <= b:
            return None, [a] + ylst
        s1 = D(self.w, self.ph, 'mul12d', [self.mem(a), self.mem(b), self.mem(self.canon(yr))], '%s = ( %s x. ( %s x. %s ) )' % (e, b, a, self.canon(yr)))
        si, ins = self.insert(a, yr)
        r = [b] + ins
        s2 = None if si is None else D(self.w, self.ph, 'oveq2d', [si], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (b, a, self.canon(yr), b, self.canon(ins)))
        return self.trans(e, [(s1, '( %s x. ( %s x. %s ) )' % (b, a, self.canon(yr))), (s2, self.canon(r))]), r

    def merge(self, xl, yl):
        x, y = self.canon(xl), self.canon(yl)
        e = '( %s x. %s )' % (x, y)
        if len(xl) == 1:
            return self.insert(xl[0], yl)
        a, xr = xl[0], xl[1:]
        s1 = D(self.w, self.ph, 'mulassd', [self.mem(a), self.mem(self.canon(xr)), self.mem(y)], '%s = ( %s x. ( %s x. %s ) )' % (e, a, self.canon(xr), y))
        sm, ml = self.merge(xr, yl)
        s2 = None if sm is None else D(self.w, self.ph, 'oveq2d', [sm], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (a, self.canon(xr), y, a, self.canon(ml)))
        si, il = self.insert(a, ml)
        return self.trans(e, [(s1, '( %s x. ( %s x. %s ) )' % (a, self.canon(xr), y)), (s2, '( %s x. %s )' % (a, self.canon(ml))), (si, self.canon(il))]), il

    def norm(self, e):
        sp = self.split(e)
        if not sp or e in self.mems and not sp:
            return None, [e]
        sl, ll = self.norm(sp[0]); sr, lr = self.norm(sp[1])
        mid = '( %s x. %s )' % (self.canon(ll), self.canon(lr))
        s1 = None
        if sl is not None and sr is not None:
            s1 = D(self.w, self.ph, 'oveq12d', [sl, sr], '%s = %s' % (e, mid))
        elif sl is not None:
            s1 = D(self.w, self.ph, 'oveq1d', [sl], '%s = %s' % (e, mid))
        elif sr is not None:
            s1 = D(self.w, self.ph, 'oveq2d', [sr], '%s = %s' % (e, mid))
        sm, ml = self.merge(ll, lr)
        return self.trans(e, [(s1, mid), (sm, self.canon(ml))]), ml

    def prove(self, L, R):
        sl, ll = self.norm(L); sr, lr = self.norm(R)
        assert ll == lr, (ll, lr)
        c = self.canon(ll)
        if sl is None and sr is None:
            return D(self.w, self.ph, 'eqidd', [], '%s = %s' % (L, R))
        if sr is None:
            return sl
        if sl is None:
            return D(self.w, self.ph, 'eqcomd', [sr], '%s = %s' % (R, L)) if False else D(self.w, self.ph, 'eqcomd', [sr], '%s = %s' % (c, R)) if L == c else D(self.w, self.ph, 'eqtr4d', [D(self.w, self.ph, 'eqidd', [], '%s = %s' % (L, c)), sr], '%s = %s' % (L, R))
        return D(self.w, self.ph, 'eqtr4d', [sl, sr], '%s = %s' % (L, R))


# ---------------------------------------------------------------- zl3ft
if __name__ == '__main__' and (not only or 'zl3ft' in only):
    w = W('zl3ft', 'The Fourier transform of the shifted Gaussian ` FF `.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3ft'])
    tp = w.s([], 'simpl1', '( %s -> T e. RR+ )' % ph); ar = w.s([], 'simpl2', '( %s -> A e. RR )' % ph); pp = w.s([], 'simpl3', '( %s -> P e. { 0 , 1 } )' % ph)
    jz = w.s([], 'simpr', '( %s -> j e. ZZ )' % ph)
    pn = p_nn0(w, ph, pp)
    icc = cst(w, ph, 'ax-icn', '_i e. CC')
    q = Q(w, ph, {'T': tp, 'A': ar, 'j': jz, 'P': pn, '_i': icc, '_pi': cst(w, ph, 'pirp', '_pi e. RR+')})
    tn0 = D(w, ph, 'rpne0d', [tp], 'T =/= 0')
    TRO = TRN(OMJ, SJ)
    TIP = '( 2 x. ( _i x. _pi ) )'
    BODY = lambda k: '( ~~>r ` ( t e. RR+ |-> S. ( -u t (,) t ) ( ( %s ` x ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x ) )' % (FF, TIP, k)
    assert FTF == '( k e. ZZ |-> %s )' % BODY('k')
    Ek = 'k = j'
    ik = w.s([], 'id', '( %s -> %s )' % (Ek, Ek))
    Ekx = '( %s /\\ x e. ( -u t (,) t ) )' % Ek
    ikx = w.s([ik], 'adantr', '( %s -> %s )' % (Ekx, Ek))
    inner = D(w, Ekx, 'oveq2d', [D(w, Ekx, 'fveq2d', [D(w, Ekx, 'negeqd', [D(w, Ekx, 'oveq2d', [D(w, Ekx, 'oveq1d', [ikx], '( k x. x ) = ( j x. x )')], '( %s x. ( k x. x ) ) = ( %s x. ( j x. x ) )' % (TIP, TIP))],
                                                                  '-u ( %s x. ( k x. x ) ) = -u ( %s x. ( j x. x ) )' % (TIP, TIP))], '( exp ` -u ( %s x. ( k x. x ) ) ) = ( exp ` -u ( %s x. ( j x. x ) ) )' % (TIP, TIP))],
                  '( ( %s ` x ) x. ( exp ` -u ( %s x. ( k x. x ) ) ) ) = ( ( %s ` x ) x. ( exp ` -u ( %s x. ( j x. x ) ) ) )' % (FF, TIP, FF, TIP))
    IK = lambda k: 'S. ( -u t (,) t ) ( ( %s ` x ) x. ( exp ` -u ( %s x. ( %s x. x ) ) ) ) _d x' % (FF, TIP, k)
    igk = w.s([inner], 'itgeq2dv', '( %s -> %s = %s )' % (Ek, IK('k'), IK('j')))
    stk = D(w, Ek, 'fveq2d', [D(w, Ek, 'mpteq2dv', [igk], '( t e. RR+ |-> %s ) = ( t e. RR+ |-> %s )' % (IK('k'), IK('j')))], '%s = %s' % (BODY('k'), BODY('j')))
    fv1 = w.s([jz, w.s([stk, w.s([], 'eqid', '%s = %s' % (FTF, FTF)), w.s([], 'fvex', '%s e. _V' % BODY('j'))], 'fvmpt', '( j e. ZZ -> ( %s ` j ) = %s )' % (FTF, BODY('j')))], 'syl', '( %s -> ( %s ` j ) = %s )' % (ph, FTF, BODY('j')))
    # per t: the integral is CSTJ x. I_t
    At = '( %s /\\ t e. RR+ )' % ph
    tt = w.s([], 'simpr', '( %s -> t e. RR+ )' % At)
    Ax = '( %s /\\ x e. ( -u t (,) t ) )' % At
    xr = w.s([w.s([], 'simpr', '( %s -> x e. ( -u t (,) t ) )' % Ax), w.inst('elioore')], 'syl', '( %s -> x e. RR )' % Ax)
    LA = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Ax, f))
    TX = '( %s ` %s )' % (TRO, CP('0', 'x'))
    FX = '( ( %s ` x ) x. ( exp ` -u ( %s x. ( j x. x ) ) ) )' % (FF, TIP)
    fti = D(w, Ax, 'syl', [w.s([w.s([LA(tp, 'T e. RR+'), LA(ar, 'A e. RR'), LA(pp, 'P e. { 0 , 1 }')], '3jca', '( %s -> %s )' % (Ax, TPAR)), w.s([LA(jz, 'j e. ZZ'), xr], 'jca', '( %s -> ( j e. ZZ /\\ x e. RR ) )' % Ax)], 'jca',
                               '( %s -> ( %s /\\ ( j e. ZZ /\\ x e. RR ) ) )' % (Ax, TPAR)), w.inst('zl3fti')], '( %s x. %s ) = %s' % (CSTJ, TX, FX))
    ig1 = w.s([D(w, Ax, 'eqcomd', [fti], '%s = ( %s x. %s )' % (FX, CSTJ, TX))], 'itgeq2dv', '( %s -> S. ( -u t (,) t ) %s _d x = S. ( -u t (,) t ) ( %s x. %s ) _d x )' % (At, FX, CSTJ, TX))
    # L^1 of x |-> TX
    # continuity of TRO: from zl3hol as in zl3ftv
    K = KAP
    kr = D(w, ph, 'redivcld', [D(w, ph, 'zred', [jz], 'j e. RR'), D(w, ph, 'rpred', [tp], 'T e. RR'), tn0], '%s e. RR' % K); kc = D(w, ph, 'recnd', [kr], '%s e. CC' % K)
    bo = lambda v: gfbody('-u T', '0', K, 'P', v)
    bs = lambda v: '( %s ` ( %s + %s ) )' % (OMJ, v, SJ)
    SK = '( %s + %s )' % (SJ, K)
    bg = lambda v: gfbody('-u T', SJ, SK, 'P', v)
    hy2 = D(w, ph, 'syl', [w.s([w.s([D(w, ph, 'negcld', [q.c('T')], '-u T e. CC'), pn], 'jca', '( %s -> ( -u T e. CC /\\ P e. NN0 ) )' % ph),
                                w.s([q.c(SJ), D(w, ph, 'addcld', [q.c(SJ), kc], '%s e. CC' % SK)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ph, SJ, SK))], 'jca',
                               '( %s -> ( ( -u T e. CC /\\ P e. NN0 ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (ph, SJ, SK)), w.inst('zl3hol')], HOLt(GF('-u T', SJ, SK, 'P')))
    def pt_tro(Av):
        yc = w.s([], 'simpr', '( %s -> y e. CC )' % Av)
        qy = Q(w, Av, {'T': w.s([tp], 'adantr', '( %s -> T e. RR+ )' % Av), 'A': w.s([ar], 'adantr', '( %s -> A e. RR )' % Av), 'j': w.s([jz], 'adantr', '( %s -> j e. ZZ )' % Av),
                       'P': w.s([pn], 'adantr', '( %s -> P e. NN0 )' % Av), 'y': yc, '_i': cst(w, Av, 'ax-icn', '_i e. CC'), '_pi': cst(w, Av, 'pirp', '_pi e. RR+')})
        YS = '( y + %s )' % SJ
        v_ = gfv(w, Av, '-u T', '0', K, 'P', YS, qy.c(YS), g, 'w')
        a_ = qy.eq('addassd', ['y', SJ, K], '( %s + %s )' % (YS, K), '( y + %s )' % SK)
        b_ = qy.eq('addridd', [YS], '( %s + 0 )' % YS, YS)
        e_ = qy.d('oveq12d', [qy.d('oveq1d', [a_], '( ( %s + %s ) ^ P ) = ( ( y + %s ) ^ P )' % (YS, K, SK)),
                              qy.d('fveq2d', [qy.d('negeqd', [qy.d('oveq2d', [qy.d('oveq1d', [b_], '( ( %s + 0 ) ^ 2 ) = ( %s ^ 2 )' % (YS, YS))], '( ( _pi x. -u T ) x. ( ( %s + 0 ) ^ 2 ) ) = ( ( _pi x. -u T ) x. ( %s ^ 2 ) )' % (YS, YS))],
                                                      '-u ( ( _pi x. -u T ) x. ( ( %s + 0 ) ^ 2 ) ) = -u ( ( _pi x. -u T ) x. ( %s ^ 2 ) )' % (YS, YS))],
                                     '( exp ` -u ( ( _pi x. -u T ) x. ( ( %s + 0 ) ^ 2 ) ) ) = ( exp ` -u ( ( _pi x. -u T ) x. ( %s ^ 2 ) ) )' % (YS, YS))],
                    '%s = %s' % (bo(YS), bg('y')))
        return qy.d('eqtrd', [v_, e_], '%s = %s' % (bs('y'), bg('y')))
    eqt = mpt_rw(w, ph, 'y', bs, 'y', bg, pt_tro, g)
    trc = D(w, ph, 'mpbird', [w.s([hy2], 'simpld', '( %s -> %s e. ( CC -cn-> CC ) )' % (ph, GF('-u T', SJ, SK, 'P'))), D(w, ph, 'eleq1d', [eqt], '( %s e. ( CC -cn-> CC ) <-> %s e. ( CC -cn-> CC ) )' % (TRO, GF('-u T', SJ, SK, 'P')))],
            '%s e. ( CC -cn-> CC )' % TRO)
    pre = w.s([w.s([cst(w, At, '0re', '0 e. RR'), tt], 'jca', '( %s -> ( 0 e. RR /\\ t e. RR+ ) )' % At),
               w.s([w.s([trc], 'adantr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At, TRO)),
                    D(w, At, 'syl2anc', [D(w, At, 'addcld', [cst(w, At, '0cn', '0 e. CC'), D(w, At, 'mulcld', [cst(w, At, 'ax-icn', '_i e. CC'), D(w, At, 'negcld', [D(w, At, 'rpcnd', [tt], 't e. CC')], '-u t e. CC')], '( _i x. -u t ) e. CC')], '%s e. CC' % CP('0', '-u t')),
                                         D(w, At, 'addcld', [cst(w, At, '0cn', '0 e. CC'), D(w, At, 'mulcld', [cst(w, At, 'ax-icn', '_i e. CC'), D(w, At, 'rpcnd', [tt], 't e. CC')], '( _i x. t ) e. CC')], '%s e. CC' % CP('0', 't')), w.inst('csegcl')],
                      '( %s cseg %s ) C_ CC' % (CP('0', '-u t'), CP('0', 't')))], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (At, TRO, CP('0', '-u t'), CP('0', 't')))],
              'jca', '( %s -> ( ( 0 e. RR /\\ t e. RR+ ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At, TRO, CP('0', '-u t'), CP('0', 't')))
    UL = '( u e. ( -u t (,) t ) |-> ( %s ` %s ) )' % (TRO, CP('0', 'u'))
    lv = D(w, At, 'syl', [pre, w.inst('z6lvert')], '( %s e. L^1 /\\ %s = ( _i x. S. ( -u t (,) t ) ( %s ` %s ) _d u ) )' % (UL, LT(TRO, '0', 't'), TRO, CP('0', 'u')))
    Eux = 'u = x'
    iux = w.s([], 'id', '( %s -> %s )' % (Eux, Eux))
    stu, _ = congr.congruence('( %s ` %s )' % (TRO, CP('0', 'u')), {'u': 'x'}, Eux, {'u': iux}, g)
    w.lines.extend(g.lines); g.lines = []
    XL = '( x e. ( -u t (,) t ) |-> %s )' % TX
    cbu = w.s([stu], 'cbvmptv', '%s = %s' % (UL, XL))
    l1x = D(w, At, 'eqeltrrd', [w.s([cbu], 'a1i', '( %s -> %s = %s )' % (At, UL, XL)), w.s([lv], 'simpld', '( %s -> %s e. L^1 )' % (At, UL))], '%s e. L^1' % XL)
    IT = 'S. ( -u t (,) t ) %s _d x' % TX
    csc_t = w.s([q.c(CSTJ)], 'adantr', '( %s -> %s e. CC )' % (At, CSTJ))
    im = w.s([csc_t, cst(w, Ax, 'fvex', '%s e. _V' % TX), l1x], 'itgmulc2', '( %s -> ( %s x. %s ) = S. ( -u t (,) t ) ( %s x. %s ) _d x )' % (At, CSTJ, IT, CSTJ, TX))
    it_eq = D(w, At, 'eqtr4d', [ig1, im], 'S. ( -u t (,) t ) %s _d x = ( %s x. %s )' % (FX, CSTJ, IT))
    itc = w.s([cst(w, Ax, 'fvex', '%s e. _V' % TX), l1x], 'itgcl', '( %s -> %s e. CC )' % (At, IT))
    F1 = '( t e. RR+ |-> S. ( -u t (,) t ) %s _d x )' % FX
    F2 = '( t e. RR+ |-> ( %s x. %s ) )' % (CSTJ, IT)
    meq = w.s([it_eq], 'mpteq2dva', '( %s -> %s = %s )' % (ph, F1, F2))
    # limits via a fresh variable s
    VW = '( ( %s ^ P ) x. ( %s / ( sqrt ` T ) ) )' % (K, C0)
    LAM = '( -u _i x. %s )' % VW
    ftv = D(w, ph, 'syl', [w.s([w.s([tp, ar, pp], '3jca', '( %s -> %s )' % (ph, TPAR)), jz], 'jca', '( %s -> ( %s /\\ j e. ZZ ) )' % (ph, TPAR)), w.inst('zl3ftv')], '%s ~~>r %s' % (ITR, LAM))
    Ets = 't = s'
    its = w.s([], 'id', '( %s -> %s )' % (Ets, Ets))
    ITs = 'S. ( -u s (,) s ) %s _d x' % TX
    st1 = D(w, Ets, 'itgeq1d', [D(w, Ets, 'oveq12d', [D(w, Ets, 'negeqd', [its], '-u t = -u s'), its], '( -u t (,) t ) = ( -u s (,) s )')], '%s = %s' % (IT, ITs))
    cb1 = w.s([st1], 'cbvmptv', '%s = ( s e. RR+ |-> %s )' % (ITR, ITs))
    ftvs = D(w, ph, 'eqbrtrrd', [w.s([cb1], 'a1i', '( %s -> %s = ( s e. RR+ |-> %s ) )' % (ph, ITR, ITs)), ftv], '( s e. RR+ |-> %s ) ~~>r %s' % (ITs, LAM))
    rcs = D(w, ph, 'syl2anc', [cst(w, ph, 'rpssre', 'RR+ C_ RR'), q.c(CSTJ), w.inst('rlimconst')], '( s e. RR+ |-> %s ) ~~>r %s' % (CSTJ, CSTJ))
    As_ = '( %s /\\ s e. RR+ )' % ph
    rms = D(w, ph, 'rlimmul', [cst(w, As_, 'ovex', '%s e. _V' % CSTJ), cst(w, As_, 'itgex', '%s e. _V' % ITs), rcs, ftvs], '( s e. RR+ |-> ( %s x. %s ) ) ~~>r ( %s x. %s )' % (CSTJ, ITs, CSTJ, LAM))
    st2 = D(w, Ets, 'oveq2d', [st1], '( %s x. %s ) = ( %s x. %s )' % (CSTJ, IT, CSTJ, ITs))
    cb2 = w.s([st2], 'cbvmptv', '%s = ( s e. RR+ |-> ( %s x. %s ) )' % (F2, CSTJ, ITs))
    conv = D(w, ph, 'eqbrtrd', [D(w, ph, 'eqtrd', [meq, w.s([cb2], 'a1i', '( %s -> %s = ( s e. RR+ |-> ( %s x. %s ) ) )' % (ph, F2, CSTJ, ITs))], '%s = ( s e. RR+ |-> ( %s x. %s ) )' % (F1, CSTJ, ITs)), rms],
             '%s ~~>r ( %s x. %s )' % (F1, CSTJ, LAM))
    ff1 = w.s([D(w, At, 'eqeltrd', [it_eq, D(w, At, 'mulcld', [csc_t, itc], '( %s x. %s ) e. CC' % (CSTJ, IT))], 'S. ( -u t (,) t ) %s _d x e. CC' % FX)], 'fmptd', '( %s -> %s : RR+ --> CC )' % (ph, F1))
    v1 = val_of(w, ph, F1, '( %s x. %s )' % (CSTJ, LAM), conv, ff1)
    ftj = D(w, ph, 'eqtrd', [fv1, v1], '( %s ` j ) = ( %s x. %s )' % (FTF, CSTJ, LAM))
    # algebra
    TN = '( T ^c -u ( ( 1 / 2 ) + P ) )'; JP = '( j ^ P )'; KP = '( %s ^ P )' % K; SQ = '( sqrt ` T )'; NIP = '( -u _i ^ P )'
    ftw = D(w, ph, 'syl3anc', [tp, pp, kr, w.inst('zl3ftw')], '( ( t e. RR+ |-> %s ) ~~>r %s /\\ %s e. CC )' % (LT(OMJ, '0', 't'), VW, C0))
    c0c = w.s([ftw], 'simprd', '( %s -> %s e. CC )' % (ph, C0))
    tc = q.c('T'); pz = D(w, ph, 'nn0zd', [pn], 'P e. ZZ')
    TP_ = '( T ^ P )'; TCP = '( T ^c P )'; TH = '( T ^c ( 1 / 2 ) )'; PH = '( P + ( 1 / 2 ) )'; HP = '( ( 1 / 2 ) + P )'
    a1 = D(w, ph, 'expdivd', [q.c('j'), tc, tn0, pn], '%s = ( %s / %s )' % (KP, JP, TP_))
    a2 = D(w, ph, 'divdiv1d', [q.c(JP), q.c(TP_), D(w, ph, 'expne0d', [tc, tn0, pz], '%s =/= 0' % TP_), q.c(SQ) if False else D(w, ph, 'rpcnd', [D(w, ph, 'rpsqrtcld', [tp], '%s e. RR+' % SQ)], '%s e. CC' % SQ),
                                  D(w, ph, 'rpne0d', [D(w, ph, 'rpsqrtcld', [tp], '%s e. RR+' % SQ)], '%s =/= 0' % SQ)], '( ( %s / %s ) / %s ) = ( %s / ( %s x. %s ) )' % (JP, TP_, SQ, JP, TP_, SQ))
    a3 = D(w, ph, 'eqcomd', [D(w, ph, 'cxpexpzd', [tc, tn0, pz], '%s = %s' % (TCP, TP_))], '%s = %s' % (TP_, TCP))
    a4 = D(w, ph, 'eqcomd', [w.s([tc, w.inst('cxpsqrt')], 'syl', '( %s -> %s = %s )' % (ph, TH, SQ))], '%s = %s' % (SQ, TH))
    hc = cst(w, ph, 'halfcn', '( 1 / 2 ) e. CC'); pc = D(w, ph, 'nn0cnd', [pn], 'P e. CC')
    a5 = D(w, ph, 'eqcomd', [D(w, ph, 'cxpaddd', [tc, tn0, pc, hc], '( T ^c %s ) = ( %s x. %s )' % (PH, TCP, TH))], '( %s x. %s ) = ( T ^c %s )' % (TCP, TH, PH))
    a6 = D(w, ph, 'oveq2d', [D(w, ph, 'addcomd', [pc, hc], '%s = %s' % (PH, HP))], '( T ^c %s ) = ( T ^c %s )' % (PH, HP))
    den = D(w, ph, 'eqtrd', [D(w, ph, 'eqtrd', [D(w, ph, 'oveq12d', [a3, a4], '( %s x. %s ) = ( %s x. %s )' % (TP_, SQ, TCP, TH)), a5], '( %s x. %s ) = ( T ^c %s )' % (TP_, SQ, PH)), a6],
             '( %s x. %s ) = ( T ^c %s )' % (TP_, SQ, HP))
    THP = '( T ^c %s )' % HP
    thpc = D(w, ph, 'cxpcld', [tc, D(w, ph, 'addcld', [hc, pc], '%s e. CC' % HP)], '%s e. CC' % THP)
    a7 = D(w, ph, 'divrecd', [q.c(JP), thpc, D(w, ph, 'cxpne0d', [tc, tn0, D(w, ph, 'addcld', [hc, pc], '%s e. CC' % HP)], '%s =/= 0' % THP)], '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (JP, THP, JP, THP))
    a8 = D(w, ph, 'oveq2d', [D(w, ph, 'eqcomd', [D(w, ph, 'cxpnegd', [tc, tn0, D(w, ph, 'addcld', [hc, pc], '%s e. CC' % HP)], '%s = ( 1 / %s )' % (TN, THP))], '( 1 / %s ) = %s' % (THP, TN))],
           '( %s x. ( 1 / %s ) ) = ( %s x. %s )' % (JP, THP, JP, TN))
    ks = q.chain('( %s / %s )' % (KP, SQ), [(D(w, ph, 'oveq1d', [a1], '( %s / %s ) = ( ( %s / %s ) / %s )' % (KP, SQ, JP, TP_, SQ)), '( ( %s / %s ) / %s )' % (JP, TP_, SQ)),
                                            (a2, '( %s / ( %s x. %s ) )' % (JP, TP_, SQ)), (D(w, ph, 'oveq2d', [den], '( %s / ( %s x. %s ) ) = ( %s / %s )' % (JP, TP_, SQ, JP, THP)), '( %s / %s )' % (JP, THP)),
                                            (a7, '( %s x. ( 1 / %s ) )' % (JP, THP)), (a8, '( %s x. %s )' % (JP, TN))])
    sqc = D(w, ph, 'rpcnd', [D(w, ph, 'rpsqrtcld', [tp], '%s e. RR+' % SQ)], '%s e. CC' % SQ); sqn = D(w, ph, 'rpne0d', [D(w, ph, 'rpsqrtcld', [tp], '%s e. RR+' % SQ)], '%s =/= 0' % SQ)
    kpc = D(w, ph, 'expcld', [kc, pn], '%s e. CC' % KP)
    vw = q.chain(VW, [(D(w, ph, 'eqcomd', [D(w, ph, 'divassd', [kpc, c0c, sqc, sqn], '( ( %s x. %s ) / %s ) = %s' % (KP, C0, SQ, VW))], '%s = ( ( %s x. %s ) / %s )' % (VW, KP, C0, SQ)), '( ( %s x. %s ) / %s )' % (KP, C0, SQ)),
                      (D(w, ph, 'div23d', [kpc, c0c, sqc, sqn], '( ( %s x. %s ) / %s ) = ( ( %s / %s ) x. %s )' % (KP, C0, SQ, KP, SQ, C0)), '( ( %s / %s ) x. %s )' % (KP, SQ, C0)),
                      (D(w, ph, 'oveq1d', [ks], '( ( %s / %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (KP, SQ, C0, JP, TN, C0)), '( ( %s x. %s ) x. %s )' % (JP, TN, C0))])
    NEW = '( ( %s x. %s ) x. %s )' % (JP, TN, C0)
    f1 = D(w, ph, 'eqtrd', [ftj, D(w, ph, 'oveq2d', [D(w, ph, 'oveq2d', [vw], '%s = ( -u _i x. %s )' % (LAM, NEW))], '( %s x. %s ) = ( %s x. ( -u _i x. %s ) )' % (CSTJ, LAM, CSTJ, NEW))],
           '( %s ` j ) = ( %s x. ( -u _i x. %s ) )' % (FTF, CSTJ, NEW))
    # GR ` j
    GRB = lambda k: '( ( %s ^ P ) x. ( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / T ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. A ) ) ) ) )' % (k, k, k)
    assert GAR == '( k e. ZZ |-> %s )' % GRB('k')
    st3, n3 = congr.congruence(GRB('k'), {'k': 'j'}, Ek, {'k': ik}, g); w.lines.extend(g.lines); g.lines = []
    grj = w.s([jz, w.s([st3, w.s([], 'eqid', '%s = %s' % (GAR, GAR)), w.s([], 'ovex', '%s e. _V' % GRB('j'))], 'fvmpt', '( j e. ZZ -> ( %s ` j ) = %s )' % (GAR, GRB('j')))], 'syl', '( %s -> ( %s ` j ) = %s )' % (ph, GAR, GRB('j')))
    E1 = '( exp ` -u ( _pi x. ( ( j ^ 2 ) / T ) ) )'; E2 = '( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( j x. A ) ) )'
    thn = D(w, ph, 'cxpcld', [tc, D(w, ph, 'negcld', [D(w, ph, 'addcld', [hc, pc], '%s e. CC' % HP)], '-u %s e. CC' % HP)], '%s e. CC' % TN)
    pr = Prod(w, ph, {NIP: q.c(NIP), E1: q.c(E1), E2: q.c(E2), '-u _i': q.c('-u _i'), JP: q.c(JP), TN: thn, C0: c0c})
    RHS = '( ( %s x. ( -u _i x. %s ) ) x. %s )' % (CTP, C0, GRB('j'))
    pe = pr.prove('( %s x. ( -u _i x. %s ) )' % (CSTJ, NEW), RHS)
    fin = D(w, ph, 'eqtr4d', [D(w, ph, 'eqtrd', [f1, pe], '( %s ` j ) = %s' % (FTF, RHS)), D(w, ph, 'oveq2d', [grj], '( ( %s x. ( -u _i x. %s ) ) x. ( %s ` j ) ) = %s' % (CTP, C0, GAR, RHS))],
            '( %s ` j ) = ( ( %s x. ( -u _i x. %s ) ) x. ( %s ` j ) )' % (FTF, CTP, C0, GAR))
    w.qed([fin], 'idi', S['zl3ft'])
    go(w, only)
