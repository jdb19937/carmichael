"""ZL3b E3: the Gaussian GF ( U , A , B , P ): holomorphy (zl3hol) and bounds (zl3gre, zl3gcb, zl3fb).
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_e3.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of
from zl3b_d2 import cst
import lin, congr

only = sys.argv[1:]
S = STATEMENTS
HOLt = lambda f: '( %s e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D %s ) )' % (f, f)


def mpt_rw(w, A_, b1, body1, b2, body2, pt, g):
    """( A_ -> ( b1 e. CC |-> body1(b1) ) = ( b2 e. CC |-> body2(b2) ) ); pt(Av) proves ( Av -> body1(b1) = body2(b1) ), Av = ( A_ /\\ b1 e. CC )"""
    Av = '( %s /\\ %s e. CC )' % (A_, b1)
    m1 = w.s([pt(Av)], 'mpteq2dva', '( %s -> ( %s e. CC |-> %s ) = ( %s e. CC |-> %s ) )' % (A_, b1, body1(b1), b1, body2(b1)))
    if b1 == b2:
        return m1
    E = '%s = %s' % (b1, b2)
    idx = w.s([], 'id', '( %s -> %s )' % (E, E))
    st, nt = congr.congruence(body2(b1), {b1: b2}, E, {b1: idx}, g)
    w.lines.extend(g.lines); g.lines = []
    assert ' '.join(nt.split()) == ' '.join(body2(b2).split()), (nt, body2(b2))
    cb = w.s([st], 'cbvmptv', '( %s e. CC |-> %s ) = ( %s e. CC |-> %s )' % (b1, body2(b1), b2, body2(b2)))
    return D(w, A_, 'eqtrd', [m1, w.s([cb], 'a1i', '( %s -> ( %s e. CC |-> %s ) = ( %s e. CC |-> %s ) )' % (A_, b1, body2(b1), b2, body2(b2)))],
             '( %s e. CC |-> %s ) = ( %s e. CC |-> %s )' % (b1, body1(b1), b2, body2(b2)))


def hol_rw(w, A_, hst, F1, F2, eq):
    """( A_ -> HOL(F2) ) from hst: ( A_ -> HOL(F1) ), eq: ( A_ -> F1 = F2 )"""
    h1 = D(w, A_, 'eleq1d', [eq], '( %s e. ( CC -cn-> CC ) <-> %s e. ( CC -cn-> CC ) )' % (F1, F2))
    h2 = D(w, A_, 'sseq2d', [D(w, A_, 'dmeqd', [D(w, A_, 'oveq2d', [eq], '( CC _D %s ) = ( CC _D %s )' % (F1, F2))], 'dom ( CC _D %s ) = dom ( CC _D %s )' % (F1, F2))],
            '( CC C_ dom ( CC _D %s ) <-> CC C_ dom ( CC _D %s ) )' % (F1, F2))
    return D(w, A_, 'mpbid', [hst, D(w, A_, 'anbi12d', [h1, h2], '( %s <-> %s )' % (HOLt(F1), HOLt(F2)))], HOLt(F2))


def fvm(w, A_, x, body, T, mem, g):
    if x == T:
        F = '( %s e. CC |-> %s )' % (x, body)
        k = congr.parse(body).kind
        ex = w.s([], 'fvexd' if k == 'fv' else 'ovexd', '( %s -> %s e. _V )' % (A_, body))
        f2 = w.s([w.s([], 'eqid', '%s = %s' % (F, F))], 'fvmpt2', '( ( %s e. CC /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (x, body, F, x, body))
        return w.s([mem, ex, f2], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (A_, F, x, body)), body
    E = '%s = %s' % (x, T)
    idx = w.s([], 'id', '( %s -> %s )' % (E, E))
    st, val = congr.congruence(body, {x: T}, E, {x: idx}, g)
    w.lines.extend(g.lines); g.lines = []
    F = '( %s e. CC |-> %s )' % (x, body)
    k = congr.parse(val).kind
    fv = w.s([st, w.s([], 'eqid', '%s = %s' % (F, F)), w.s([], 'fvex' if k == 'fv' else 'ovex', '%s e. _V' % val)], 'fvmpt', '( %s e. CC -> ( %s ` %s ) = %s )' % (T, F, T, val))
    return w.s([mem, fv], 'syl', '( %s -> ( %s ` %s ) = %s )' % (A_, F, T, val)), val


# ---------------------------------------------------------------- zl3hol
if __name__ == '__main__' and (not only or 'zl3hol' in only):
    w = W('zl3hol', 'The Gaussian ` ( y + B ) ^ P e ^ ( -pi U ( y + A ) ^ 2 ) ` is entire.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3hol'])
    uc = w.s([], 'simpll', '( %s -> U e. CC )' % ph); pn = w.s([], 'simplr', '( %s -> P e. NN0 )' % ph)
    ac = w.s([], 'simprl', '( %s -> A e. CC )' % ph); bc = w.s([], 'simprr', '( %s -> B e. CC )' % ph)
    pic = cst(w, ph, 'picn', '_pi e. CC')
    PU = '( _pi x. U )'; E_ = '-u %s' % PU; Q_ = '-u ( A ^ 2 )'; L_ = '( %s x. ( 2 x. A ) )' % E_
    puc = D(w, ph, 'mulcld', [pic, uc], '%s e. CC' % PU); ec = D(w, ph, 'negcld', [puc], '%s e. CC' % E_)
    a2c = D(w, ph, 'sqcld', [ac], '( A ^ 2 ) e. CC'); qc = D(w, ph, 'negcld', [a2c], '%s e. CC' % Q_)
    c2a = D(w, ph, 'mulcld', [cst(w, ph, '2cn', '2 e. CC'), ac], '( 2 x. A ) e. CC'); lc = D(w, ph, 'mulcld', [ec, c2a], '%s e. CC' % L_)
    opn = cst(w, ph, 'cnopn', 'CC e. ( TopOpen ` CCfld )'); ssc = cst(w, ph, 'ssid', 'CC C_ CC')
    GA = '( z e. CC |-> ( exp ` ( %s x. ( ( z ^ 2 ) - %s ) ) ) )' % (E_, Q_)
    hg0 = D(w, ph, 'syl3anc', [opn, ssc, w.s([ec, qc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (ph, E_, Q_)), w.inst('holgau')], HOLt(GA))
    GAb = lambda v: '( exp ` ( %s x. ( ( %s ^ 2 ) - %s ) ) )' % (E_, v, Q_)
    GA0 = GA
    GA = '( v e. CC |-> %s )' % GAb('v')
    hg = hol_rw(w, ph, hg0, GA0, GA, mpt_rw(w, ph, 'z', GAb, 'v', GAb, lambda Av: w.s([], 'eqidd', '( %s -> %s = %s )' % (Av, GAb('z'), GAb('z'))), g))
    EA = '( y e. CC |-> ( exp ` ( %s x. y ) ) )' % L_
    he = D(w, ph, 'syl', [lc, w.inst('zl3eaw')], HOLt(EA))
    PR = '( z e. CC |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (GA, EA)
    hm = D(w, ph, 'syl2anc', [hg, he, w.inst('holmul')], HOLt(PR))
    GB = lambda v: '( exp ` -u ( %s x. ( ( %s + A ) ^ 2 ) ) )' % (PU, v)
    def pt2(Av):
        zc = w.s([], 'simpr', '( %s -> z e. CC )' % Av)
        f1, v1 = fvm(w, Av, 'v', GAb('v'), 'z', zc, g)
        f2, v2 = fvm(w, Av, 'y', '( exp ` ( %s x. y ) )' % L_, 'z', zc, g)
        X1 = '( %s x. ( ( z ^ 2 ) - %s ) )' % (E_, Q_); X2 = '( %s x. z )' % L_
        lift = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Av, f))
        ec1, qc1, lc1, ac1, puc1 = lift(ec, '%s e. CC' % E_), lift(qc, '%s e. CC' % Q_), lift(lc, '%s e. CC' % L_), lift(ac, 'A e. CC'), lift(puc, '%s e. CC' % PU)
        z2 = D(w, Av, 'sqcld', [zc], '( z ^ 2 ) e. CC'); a2 = D(w, Av, 'sqcld', [ac1], '( A ^ 2 ) e. CC')
        x1c = D(w, Av, 'mulcld', [ec1, D(w, Av, 'subcld', [z2, qc1], '( ( z ^ 2 ) - %s ) e. CC' % Q_)], '%s e. CC' % X1)
        x2c = D(w, Av, 'mulcld', [lc1, zc], '%s e. CC' % X2)
        ea = D(w, Av, 'eqcomd', [D(w, Av, 'syl2anc', [x1c, x2c, w.inst('efadd')], '( exp ` ( %s + %s ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (X1, X2, X1, X2))],
               '( ( exp ` %s ) x. ( exp ` %s ) ) = ( exp ` ( %s + %s ) )' % (X1, X2, X1, X2))
        # X1 + X2 = -u ( PU x. ( ( z + A ) ^ 2 ) )
        ZA = '( z x. A )'; zac = D(w, Av, 'mulcld', [zc, ac1], '%s e. CC' % ZA)
        T2 = '( 2 x. %s )' % ZA; t2c = D(w, Av, 'mulcld', [cst(w, Av, '2cn', '2 e. CC'), zac], '%s e. CC' % T2)
        s1 = D(w, Av, 'oveq2d', [D(w, Av, 'subnegd', [z2, a2], '( ( z ^ 2 ) - %s ) = ( ( z ^ 2 ) + ( A ^ 2 ) )' % Q_)], '%s = ( %s x. ( ( z ^ 2 ) + ( A ^ 2 ) ) )' % (X1, E_))
        s2 = D(w, Av, 'eqtrd', [D(w, Av, 'mulassd', [ec1, c2a if False else D(w, Av, 'mulcld', [cst(w, Av, '2cn', '2 e. CC'), ac1], '( 2 x. A ) e. CC'), zc], '( %s x. z ) = ( %s x. ( ( 2 x. A ) x. z ) )' % (L_, E_)),
                                D(w, Av, 'oveq2d', [D(w, Av, 'eqtrd', [D(w, Av, 'mulassd', [cst(w, Av, '2cn', '2 e. CC'), ac1, zc], '( ( 2 x. A ) x. z ) = ( 2 x. ( A x. z ) )'),
                                                                      D(w, Av, 'oveq2d', [D(w, Av, 'mulcomd', [ac1, zc], '( A x. z ) = %s' % ZA)], '( 2 x. ( A x. z ) ) = %s' % T2)], '( ( 2 x. A ) x. z ) = %s' % T2)],
                                  '( %s x. ( ( 2 x. A ) x. z ) ) = ( %s x. %s )' % (E_, E_, T2))], '%s = ( %s x. %s )' % (X2, E_, T2))
        za2 = '( ( z ^ 2 ) + ( A ^ 2 ) )'
        s3 = D(w, Av, 'eqtr4d', [D(w, Av, 'oveq12d', [s1, s2], '( %s + %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (X1, X2, E_, za2, E_, T2)),
                                 D(w, Av, 'adddid', [ec1, D(w, Av, 'addcld', [z2, a2], '%s e. CC' % za2), t2c], '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (E_, za2, T2, E_, za2, E_, T2))],
                '( %s + %s ) = ( %s x. ( %s + %s ) )' % (X1, X2, E_, za2, T2))
        sq = '( ( z + A ) ^ 2 )'
        s4 = D(w, Av, 'eqtr4d', [D(w, Av, 'add32d', [z2, a2, t2c], '( %s + %s ) = ( ( ( z ^ 2 ) + %s ) + ( A ^ 2 ) )' % (za2, T2, T2)), D(w, Av, 'binom2d', [zc, ac1], '%s = ( ( ( z ^ 2 ) + %s ) + ( A ^ 2 ) )' % (sq, T2))],
                '( %s + %s ) = %s' % (za2, T2, sq))
        s5 = D(w, Av, 'eqtrd', [s3, D(w, Av, 'oveq2d', [s4], '( %s x. ( %s + %s ) ) = ( %s x. %s )' % (E_, za2, T2, E_, sq))], '( %s + %s ) = ( %s x. %s )' % (X1, X2, E_, sq))
        s6 = D(w, Av, 'eqtrd', [s5, D(w, Av, 'mulneg1d', [puc1, D(w, Av, 'sqcld', [D(w, Av, 'addcld', [zc, ac1], '( z + A ) e. CC')], '%s e. CC' % sq)], '( %s x. %s ) = -u ( %s x. %s )' % (E_, sq, PU, sq))],
                '( %s + %s ) = -u ( %s x. %s )' % (X1, X2, PU, sq))
        return D(w, Av, 'eqtrd', [D(w, Av, 'eqtrd', [D(w, Av, 'oveq12d', [f1, f2], '( ( %s ` z ) x. ( %s ` z ) ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (GA, EA, X1, X2)), ea],
                                                    '( ( %s ` z ) x. ( %s ` z ) ) = ( exp ` ( %s + %s ) )' % (GA, EA, X1, X2)), D(w, Av, 'fveq2d', [s6], '( exp ` ( %s + %s ) ) = %s' % (X1, X2, GB('z')))],
                 '( ( %s ` z ) x. ( %s ` z ) ) = %s' % (GA, EA, GB('z')))
    H2 = '( v e. CC |-> %s )' % GB('v')
    e2 = mpt_rw(w, ph, 'z', lambda v: '( ( %s ` %s ) x. ( %s ` %s ) )' % (GA, v, EA, v), 'v', GB, pt2, g)
    h2 = hol_rw(w, ph, hm, PR, H2, e2)
    # H1 = ( z e. CC |-> ( ( z + B ) ^ P ) )
    PB = lambda v: '( ( %s + B ) ^ P )' % v
    H1 = '( v e. CC |-> %s )' % PB('v')
    A1 = '( %s /\\ P e. NN )' % ph
    PW = '( y e. CC |-> ( ( y - -u B ) ^ P ) )'
    hp = D(w, A1, 'syl', [w.s([w.s([cst(w, A1, 'cnopn', 'CC e. ( TopOpen ` CCfld )'), cst(w, A1, 'ssid', 'CC C_ CC')], 'jca', '( %s -> ( CC e. ( TopOpen ` CCfld ) /\\ CC C_ CC ) )' % A1),
                               w.s([D(w, A1, 'negcld', [w.s([bc], 'adantr', '( %s -> B e. CC )' % A1)], '-u B e. CC'), w.s([], 'simpr', '( %s -> P e. NN )' % A1)], 'jca', '( %s -> ( -u B e. CC /\\ P e. NN ) )' % A1)],
                              'jca', '( %s -> ( ( CC e. ( TopOpen ` CCfld ) /\\ CC C_ CC ) /\\ ( -u B e. CC /\\ P e. NN ) ) )' % A1), w.inst('holpowp')], HOLt(PW))
    def pt1(Av):
        yc = w.s([], 'simpr', '( %s -> y e. CC )' % Av)
        return D(w, Av, 'oveq1d', [D(w, Av, 'subnegd', [yc, w.s([bc], 'ad2antrr', '( %s -> B e. CC )' % Av)], '( y - -u B ) = ( y + B )')], '( ( y - -u B ) ^ P ) = %s' % PB('y'))
    h1a = hol_rw(w, A1, hp, PW, H1, mpt_rw(w, A1, 'y', lambda v: '( ( %s - -u B ) ^ P )' % v, 'v', PB, pt1, g))
    A0 = '( %s /\\ P = 0 )' % ph
    E0 = '( y e. CC |-> ( exp ` ( 0 x. y ) ) )'
    h0 = D(w, A0, 'syl', [cst(w, A0, '0cn', '0 e. CC'), w.inst('zl3eaw')], HOLt(E0))
    def pt0(Av):
        yc = w.s([], 'simpr', '( %s -> y e. CC )' % Av)
        p0 = w.s([], 'simplr', '( %s -> P = 0 )' % Av)
        a = D(w, Av, 'eqtrd', [D(w, Av, 'fveq2d', [D(w, Av, 'mul02d', [yc], '( 0 x. y ) = 0')], '( exp ` ( 0 x. y ) ) = ( exp ` 0 )'), cst(w, Av, 'ef0', '( exp ` 0 ) = 1')], '( exp ` ( 0 x. y ) ) = 1')
        yb = D(w, Av, 'addcld', [yc, w.s([bc], 'ad2antrr', '( %s -> B e. CC )' % Av)], '( y + B ) e. CC')
        b = D(w, Av, 'eqtrd', [D(w, Av, 'oveq2d', [p0], '%s = ( ( y + B ) ^ 0 )' % PB('y')), D(w, Av, 'exp0d', [yb], '( ( y + B ) ^ 0 ) = 1')], '%s = 1' % PB('y'))
        return D(w, Av, 'eqtr4d', [a, b], '( exp ` ( 0 x. y ) ) = %s' % PB('y'))
    h1b = hol_rw(w, A0, h0, E0, H1, mpt_rw(w, A0, 'y', lambda v: '( exp ` ( 0 x. %s ) )' % v, 'v', PB, pt0, g))
    h1 = w.s([h1a, h1b, w.s([pn, w.s([], 'elnn0', '( P e. NN0 <-> ( P e. NN \\/ P = 0 ) )')], 'sylib', '( %s -> ( P e. NN \\/ P = 0 ) )' % ph)], 'mpjaodan', '( %s -> %s )' % (ph, HOLt(H1)))
    PR2 = '( z e. CC |-> ( ( %s ` z ) x. ( %s ` z ) ) )' % (H1, H2)
    hm2 = D(w, ph, 'syl2anc', [h1, h2, w.inst('holmul')], HOLt(PR2))
    GFb = lambda v: '( ( ( %s + B ) ^ P ) x. ( exp ` -u ( ( _pi x. U ) x. ( ( %s + A ) ^ 2 ) ) ) )' % (v, v)
    def ptf(Av):
        zc = w.s([], 'simpr', '( %s -> z e. CC )' % Av)
        f1, _ = fvm(w, Av, 'v', PB('v'), 'z', zc, g)
        f2, _ = fvm(w, Av, 'v', GB('v'), 'z', zc, g)
        return D(w, Av, 'oveq12d', [f1, f2], '( ( %s ` z ) x. ( %s ` z ) ) = %s' % (H1, H2, GFb('z')))
    FG = GF('U', 'A', 'B', 'P')
    assert FG == '( y e. CC |-> %s )' % GFb('y')
    w.qed([hm2, mpt_rw(w, ph, 'z', lambda v: '( ( %s ` %s ) x. ( %s ` %s ) )' % (H1, v, H2, v), 'y', GFb, ptf, g)], 'IGNORE', 'x') if False else None
    fin = hol_rw(w, ph, hm2, PR2, FG, mpt_rw(w, ph, 'z', lambda v: '( ( %s ` %s ) x. ( %s ` %s ) )' % (H1, v, H2, v), 'y', GFb, ptf, g))
    w.qed([fin], 'idi', S['zl3hol'])
    go(w, only)


# ---------------------------------------------------------------- zl3gre
if __name__ == '__main__' and (not only or 'zl3gre' in only):
    w = W('zl3gre', 'The real Gaussian times ` 1 + | X | ` is at most ` e ^ ( 1 / ( pi T ) ) 2 ^ -| X | `.')
    ph, concl = ante_of(S['zl3gre'])
    tp = w.s([], 'simpl', '( %s -> T e. RR+ )' % ph); xr = w.s([], 'simpr', '( %s -> X e. RR )' % ph)
    C = '( _pi x. T )'; A = '( abs ` X )'; R = '( 1 / %s )' % C; L2 = '( log ` 2 )'; X2 = '( X ^ 2 )'
    cp = D(w, ph, 'rpmulcld', [cst(w, ph, 'pirp', '_pi e. RR+'), tp], '%s e. RR+' % C)
    cr = D(w, ph, 'rpred', [cp], '%s e. RR' % C); cc = D(w, ph, 'rpcnd', [cp], '%s e. CC' % C)
    xc = D(w, ph, 'recnd', [xr], 'X e. CC')
    ar = D(w, ph, 'abscld', [xc], '%s e. RR' % A); a0 = D(w, ph, 'absge0d', [xc], '0 <_ %s' % A)
    rr = D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), cp], '%s e. RR' % R)
    l2r = w.s([w.s([cst(w, ph, '2rp', '2 e. RR+')], 'relogcld', '( %s -> %s e. RR )' % (ph, L2))], 'idi', '( %s -> %s e. RR )' % (ph, L2))
    x2r = D(w, ph, 'resqcld', [xr], '%s e. RR' % X2)
    CX = '( %s x. %s )' % (C, X2)
    cxr = D(w, ph, 'remulcld', [cr, x2r], '%s e. RR' % CX)
    # key: A + -u CX <_ R + -u ( A x. L2 )
    AR = '( %s - %s )' % (A, R)
    arr = D(w, ph, 'resubcld', [ar, rr], '%s e. RR' % AR)
    q = D(w, ph, 'mulge0d', [cr, D(w, ph, 'remulcld', [arr, arr], '( %s x. %s ) e. RR' % (AR, AR)), D(w, ph, 'rpge0d', [cp], '0 <_ %s' % C),
                              D(w, ph, 'msqge0d', [arr], '0 <_ ( %s x. %s )' % (AR, AR))], '0 <_ ( %s x. ( %s x. %s ) )' % (C, AR, AR))
    cr1 = D(w, ph, 'recidd', [cc, D(w, ph, 'rpne0d', [cp], '%s =/= 0' % C)], '( %s x. %s ) = 1' % (C, R))
    CR = '( %s x. %s )' % (C, R)
    e1 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq1d', [cr1], '( %s x. %s ) = ( 1 x. %s )' % (CR, A, A)), D(w, ph, 'mullidd', [D(w, ph, 'recnd', [ar], '%s e. CC' % A)], '( 1 x. %s ) = %s' % (A, A))], '( %s x. %s ) = %s' % (CR, A, A))
    e2 = D(w, ph, 'eqtrd', [D(w, ph, 'oveq1d', [cr1], '( %s x. %s ) = ( 1 x. %s )' % (CR, R, R)), D(w, ph, 'mullidd', [D(w, ph, 'recnd', [rr], '%s e. CC' % R)], '( 1 x. %s ) = %s' % (R, R))], '( %s x. %s ) = %s' % (CR, R, R))
    xa0 = D(w, ph, 'eqtr3d', [w.s([xr, w.inst('absresq')], 'syl', '( %s -> ( %s ^ 2 ) = %s )' % (ph, A, X2)), D(w, ph, 'sqvald', [D(w, ph, 'recnd', [ar], '%s e. CC' % A)], '( %s ^ 2 ) = ( %s x. %s )' % (A, A, A))],
             '%s = ( %s x. %s )' % (X2, A, A))
    xa = D(w, ph, 'oveq2d', [xa0], '%s = ( %s x. ( %s x. %s ) )' % (CX, C, A, A))
    m = D(w, ph, 'lemul2ad', [l2r, cst(w, ph, '1re', '1 e. RR'), ar, a0, D(w, ph, 'ltled', [l2r, cst(w, ph, '1re', '1 e. RR'), cst(w, ph, 'log2le1', '%s < 1' % L2)], '%s <_ 1' % L2)],
          '( %s x. %s ) <_ ( %s x. 1 )' % (A, L2, A))
    lv = {'_pi': cst(w, ph, 'pire', '_pi e. RR'), 'T': D(w, ph, 'rpred', [tp], 'T e. RR'), A: ar, R: rr, L2: l2r, 'X': xr}
    E1 = '( %s + -u %s )' % (A, CX); E2 = '( %s + -u ( %s x. %s ) )' % (R, A, L2)
    def both(st):
        f = w.lines[[i for i, l in enumerate(w.lines) if l.startswith(st + ':')][0]].split('|- ', 1)[1]
        lhs, rhs = f[len('( %s -> ' % ph):-2].split(' = ', 1) if f.count(' = ') == 1 else (None, None)
        return [D(w, ph, 'eqled', [st], '%s <_ %s' % (lhs, rhs)), D(w, ph, 'eqled', [D(w, ph, 'eqcomd', [st], '%s = %s' % (rhs, lhs))], '%s <_ %s' % (rhs, lhs))]
    key = lin.linarith(w, ph, [q, m] + both(e1) + both(e2) + both(xa), '%s <_ %s' % (E1, E2), leaves=lv, products=True, atoms=[R, A, L2])
    e1r = D(w, ph, 'readdcld', [ar, D(w, ph, 'renegcld', [cxr], '-u %s e. RR' % CX)], '%s e. RR' % E1)
    e2r = D(w, ph, 'readdcld', [rr, D(w, ph, 'renegcld', [D(w, ph, 'remulcld', [ar, l2r], '( %s x. %s ) e. RR' % (A, L2))], '-u ( %s x. %s ) e. RR' % (A, L2))], '%s e. RR' % E2)
    ek = D(w, ph, 'mpbid', [key, D(w, ph, 'syl2anc', [e1r, e2r, w.inst('efle')], '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (E1, E2, E1, E2))], '( exp ` %s ) <_ ( exp ` %s )' % (E1, E2))
    G = '( exp ` -u %s )' % CX
    gr = D(w, ph, 'reefcld', [D(w, ph, 'renegcld', [cxr], '-u %s e. RR' % CX)], '%s e. RR' % G)
    g0 = D(w, ph, 'rpge0d', [D(w, ph, 'rpefcld', [D(w, ph, 'renegcld', [cxr], '-u %s e. RR' % CX)], '%s e. RR+' % G)], '0 <_ %s' % G)
    s1 = D(w, ph, 'syl2anc', [ar, a0, w.inst('bvefge1p')], '( 1 + %s ) <_ ( exp ` %s )' % (A, A))
    s2 = D(w, ph, 'lemul1ad', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), ar], '( 1 + %s ) e. RR' % A), D(w, ph, 'reefcld', [ar], '( exp ` %s ) e. RR' % A), gr, g0, s1],
           '( ( 1 + %s ) x. %s ) <_ ( ( exp ` %s ) x. %s )' % (A, G, A, G))
    s3 = D(w, ph, 'eqcomd', [D(w, ph, 'syl2anc', [D(w, ph, 'recnd', [ar], '%s e. CC' % A), D(w, ph, 'recnd', [D(w, ph, 'renegcld', [cxr], '-u %s e. RR' % CX)], '-u %s e. CC' % CX), w.inst('efadd')],
                                  '( exp ` %s ) = ( ( exp ` %s ) x. %s )' % (E1, A, G))], '( ( exp ` %s ) x. %s ) = ( exp ` %s )' % (A, G, E1))
    TA = '( 2 ^c -u %s )' % A
    s4 = D(w, ph, 'cxpefd', [cst(w, ph, '2cn', '2 e. CC'), cst(w, ph, '2ne0', '2 =/= 0'), D(w, ph, 'negcld', [D(w, ph, 'recnd', [ar], '%s e. CC' % A)], '-u %s e. CC' % A)], '%s = ( exp ` ( -u %s x. %s ) )' % (TA, A, L2))
    s4b = D(w, ph, 'eqtrd', [s4, D(w, ph, 'fveq2d', [D(w, ph, 'mulneg1d', [D(w, ph, 'recnd', [ar], '%s e. CC' % A), D(w, ph, 'recnd', [l2r], '%s e. CC' % L2)], '( -u %s x. %s ) = -u ( %s x. %s )' % (A, L2, A, L2))],
                                                 '( exp ` ( -u %s x. %s ) ) = ( exp ` -u ( %s x. %s ) )' % (A, L2, A, L2))], '%s = ( exp ` -u ( %s x. %s ) )' % (TA, A, L2))
    s5 = D(w, ph, 'eqtr4d', [D(w, ph, 'syl2anc', [D(w, ph, 'recnd', [rr], '%s e. CC' % R), D(w, ph, 'recnd', [D(w, ph, 'renegcld', [D(w, ph, 'remulcld', [ar, l2r], '( %s x. %s ) e. RR' % (A, L2))], '-u ( %s x. %s ) e. RR' % (A, L2))], '-u ( %s x. %s ) e. CC' % (A, L2)), w.inst('efadd')],
                                    '( exp ` %s ) = ( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) )' % (E2, R, A, L2)),
                             D(w, ph, 'oveq2d', [s4b], '( ( exp ` %s ) x. %s ) = ( ( exp ` %s ) x. ( exp ` -u ( %s x. %s ) ) )' % (R, TA, R, A, L2))], '( exp ` %s ) = ( ( exp ` %s ) x. %s )' % (E2, R, TA))
    fin = D(w, ph, 'letrd', [D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), ar], '( 1 + %s ) e. RR' % A), gr], '( ( 1 + %s ) x. %s ) e. RR' % (A, G)),
                             D(w, ph, 'reefcld', [e1r], '( exp ` %s ) e. RR' % E1), D(w, ph, 'reefcld', [e2r], '( exp ` %s ) e. RR' % E2),
                             D(w, ph, 'breqtrd', [s2, s3], '( ( 1 + %s ) x. %s ) <_ ( exp ` %s )' % (A, G, E1)), ek], '( ( 1 + %s ) x. %s ) <_ ( exp ` %s )' % (A, G, E2))
    w.qed([fin, s5], 'breqtrd', S['zl3gre'])
    go(w, only)


def both(w, A_, st, lhs, rhs):
    return [D(w, A_, 'eqled', [st], '%s <_ %s' % (lhs, rhs)), D(w, A_, 'eqled', [D(w, A_, 'eqcomd', [st], '%s = %s' % (rhs, lhs))], '%s <_ %s' % (rhs, lhs))]


# ---------------------------------------------------------------- zl3gcb
if __name__ == '__main__' and (not only or 'zl3gcb' in only):
    w = W('zl3gcb', 'The complex Gaussian ` U ^ P e ^ ( -pi T V ^ 2 ) ` on a horizontal strip decays like ` 2 ^ -| Re V | `.')
    ph, concl = ante_of(S['zl3gcb'])
    tp = w.s([], 'simp1l', '( %s -> T e. RR+ )' % ph); pp = w.s([], 'simp1r', '( %s -> P e. { 0 , 1 } )' % ph)
    uc = w.s([], 'simp2l', '( %s -> U e. CC )' % ph); vc = w.s([], 'simp2r', '( %s -> V e. CC )' % ph)
    cr = w.s([w.s([], 'simp3l', '( %s -> ( C e. RR /\\ R e. RR ) )' % ph)], 'simpld', '( %s -> C e. RR )' % ph)
    rr = w.s([w.s([], 'simp3l', '( %s -> ( C e. RR /\\ R e. RR ) )' % ph)], 'simprd', '( %s -> R e. RR )' % ph)
    TRI = '( 0 <_ C /\\ ( abs ` U ) <_ ( ( abs ` ( Re ` V ) ) + C ) /\\ ( abs ` ( Im ` V ) ) <_ R )'
    tri = w.s([], 'simp3r', '( %s -> %s )' % (ph, TRI))
    c0 = w.s([tri], 'simp1d', '( %s -> 0 <_ C )' % ph); ub = w.s([tri], 'simp2d', '( %s -> ( abs ` U ) <_ ( ( abs ` ( Re ` V ) ) + C ) )' % ph)
    yb = w.s([tri], 'simp3d', '( %s -> ( abs ` ( Im ` V ) ) <_ R )' % ph)
    X = '( Re ` V )'; Y = '( Im ` V )'; A = '( abs ` %s )' % X; AY = '( abs ` %s )' % Y; AU = '( abs ` U )'
    xr = D(w, ph, 'recld', [vc], '%s e. RR' % X); yr = D(w, ph, 'imcld', [vc], '%s e. RR' % Y)
    xc = D(w, ph, 'recnd', [xr], '%s e. CC' % X); yc = D(w, ph, 'recnd', [yr], '%s e. CC' % Y)
    ar = D(w, ph, 'abscld', [xc], '%s e. RR' % A); a0 = D(w, ph, 'absge0d', [xc], '0 <_ %s' % A)
    ayr = D(w, ph, 'abscld', [yc], '%s e. RR' % AY); ay0 = D(w, ph, 'absge0d', [yc], '0 <_ %s' % AY)
    aur = D(w, ph, 'abscld', [uc], '%s e. RR' % AU); au0 = D(w, ph, 'absge0d', [uc], '0 <_ %s' % AU)
    UP = '( U ^ P )'; M1 = '( abs ` %s )' % UP
    # P e. NN0 for closure
    A0 = '( %s /\\ P = 0 )' % ph; A1 = '( %s /\\ P = 1 )' % ph
    def m1case(Ac, k):
        pe = w.s([], 'simpr', '( %s -> P = %s )' % (Ac, k))
        uc_ = w.s([uc], 'adantr', '( %s -> U e. CC )' % Ac); aur_ = w.s([aur], 'adantr', '( %s -> %s e. RR )' % (Ac, AU)); au0_ = w.s([au0], 'adantr', '( %s -> 0 <_ %s )' % (Ac, AU))
        e1 = D(w, Ac, 'fveq2d', [D(w, Ac, 'oveq2d', [pe], '%s = ( U ^ %s )' % (UP, k))], '%s = ( abs ` ( U ^ %s ) )' % (M1, k))
        if k == '0':
            e2 = D(w, Ac, 'eqtrd', [D(w, Ac, 'fveq2d', [D(w, Ac, 'exp0d', [uc_], '( U ^ 0 ) = 1')], '( abs ` ( U ^ 0 ) ) = ( abs ` 1 )'), cst(w, Ac, 'abs1', '( abs ` 1 ) = 1')], '( abs ` ( U ^ 0 ) ) = 1')
            v = '1'
            le = lin.linarith(w, Ac, [au0_], '1 <_ ( 1 + %s )' % AU, leaves={AU: aur_})
        else:
            e2 = D(w, Ac, 'fveq2d', [D(w, Ac, 'exp1d', [uc_], '( U ^ 1 ) = U')], '( abs ` ( U ^ 1 ) ) = %s' % AU)
            v = AU
            le = lin.linarith(w, Ac, [], '%s <_ ( 1 + %s )' % (AU, AU), leaves={AU: aur_})
        return D(w, Ac, 'eqbrtrd', [D(w, Ac, 'eqtrd', [e1, e2], '%s = %s' % (M1, v)), le], '%s <_ ( 1 + %s )' % (M1, AU))
    m1b = w.s([m1case(A0, '0'), m1case(A1, '1'), w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % ph)], 'mpjaodan', '( %s -> %s <_ ( 1 + %s ) )' % (ph, M1, AU))
    ca0 = D(w, ph, 'mulge0d', [cr, ar, c0, a0], '0 <_ ( C x. %s )' % A)
    N1 = '( ( 1 + C ) x. ( 1 + %s ) )' % A
    lvx = {AU: aur, A: ar, 'C': cr}
    m1n = lin.linarith(w, ph, [m1b, ub, ca0], '%s <_ %s' % (M1, N1), leaves=dict(lvx, **{M1: None}) if False else lvx, atoms=[M1], products=True) if False else None
    m1x = lin.linarith(w, ph, [ub, ca0], '( 1 + %s ) <_ %s' % (AU, N1), leaves=lvx, products=True)
    pn0 = w.s([w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % ph)], 'idi', '( %s -> ( P = 0 \\/ P = 1 ) )' % ph)
    upc = None
    # U ^ P in CC: P e. NN0
    p0n = w.s([w.s([w.s([], 'simpr', '( %s -> P = 0 )' % A0), cst(w, A0, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> P e. NN0 )' % A0),
               w.s([w.s([], 'simpr', '( %s -> P = 1 )' % A1), cst(w, A1, '1nn0', '1 e. NN0')], 'eqeltrd', '( %s -> P e. NN0 )' % A1), pn0], 'mpjaodan', '( %s -> P e. NN0 )' % ph)
    upc = D(w, ph, 'expcld', [uc, p0n], '%s e. CC' % UP)
    m1r = D(w, ph, 'abscld', [upc], '%s e. RR' % M1)
    n1r = D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), cr], '( 1 + C ) e. RR'), D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), ar], '( 1 + %s ) e. RR' % A)], '%s e. RR' % N1)
    m1n = D(w, ph, 'letrd', [m1r, D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), aur], '( 1 + %s ) e. RR' % AU), n1r, m1b, m1x], '%s <_ %s' % (M1, N1))
    # the exponential
    PT = '( _pi x. T )'; Z = '-u ( %s x. ( V ^ 2 ) )' % PT; EZ = '( exp ` %s )' % Z; M2 = '( abs ` %s )' % EZ
    ptp = D(w, ph, 'rpmulcld', [cst(w, ph, 'pirp', '_pi e. RR+'), tp], '%s e. RR+' % PT); ptr = D(w, ph, 'rpred', [ptp], '%s e. RR' % PT)
    v2 = D(w, ph, 'sqcld', [vc], '( V ^ 2 ) e. CC')
    zc = D(w, ph, 'negcld', [D(w, ph, 'mulcld', [D(w, ph, 'rpcnd', [ptp], '%s e. CC' % PT), v2], '( %s x. ( V ^ 2 ) ) e. CC' % PT)], '%s e. CC' % Z)
    ae = D(w, ph, 'syl', [zc, w.inst('absef')], '%s = ( exp ` ( Re ` %s ) )' % (M2, Z))
    RZ = '( Re ` %s )' % Z
    r1 = D(w, ph, 'renegd', [D(w, ph, 'mulcld', [D(w, ph, 'rpcnd', [ptp], '%s e. CC' % PT), v2], '( %s x. ( V ^ 2 ) ) e. CC' % PT)], '%s = -u ( Re ` ( %s x. ( V ^ 2 ) ) )' % (RZ, PT))
    r2 = D(w, ph, 'remul2d', [ptr, v2], '( Re ` ( %s x. ( V ^ 2 ) ) ) = ( %s x. ( Re ` ( V ^ 2 ) ) )' % (PT, PT))
    r3 = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [D(w, ph, 'sqvald', [vc], '( V ^ 2 ) = ( V x. V )')], '( Re ` ( V ^ 2 ) ) = ( Re ` ( V x. V ) )'), D(w, ph, 'remuld', [vc, vc], '( Re ` ( V x. V ) ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (X, X, Y, Y))],
           '( Re ` ( V ^ 2 ) ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (X, X, Y, Y))
    RZv = '-u ( %s x. ( ( %s x. %s ) - ( %s x. %s ) ) )' % (PT, X, X, Y, Y)
    rz = D(w, ph, 'eqtrd', [r1, D(w, ph, 'negeqd', [D(w, ph, 'eqtrd', [r2, D(w, ph, 'oveq2d', [r3], '( %s x. ( Re ` ( V ^ 2 ) ) ) = ( %s x. ( ( %s x. %s ) - ( %s x. %s ) ) )' % (PT, PT, X, X, Y, Y))],
                                                                  '( Re ` ( %s x. ( V ^ 2 ) ) ) = ( %s x. ( ( %s x. %s ) - ( %s x. %s ) ) )' % (PT, PT, X, X, Y, Y))], '-u ( Re ` ( %s x. ( V ^ 2 ) ) ) = %s' % (PT, RZv))], '%s = %s' % (RZ, RZv))
    # y y <_ R R
    yy = D(w, ph, 'eqtr3d', [D(w, ph, 'absmuld', [yc, yc], '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (Y, Y, AY, AY)),
                             D(w, ph, 'absidd', [D(w, ph, 'remulcld', [yr, yr], '( %s x. %s ) e. RR' % (Y, Y)), D(w, ph, 'msqge0d', [yr], '0 <_ ( %s x. %s )' % (Y, Y))], '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (Y, Y, Y, Y))],
            '( %s x. %s ) = ( %s x. %s )' % (AY, AY, Y, Y))
    yl = D(w, ph, 'lemul12ad', [ayr, rr, ayr, rr, ay0, ay0, yb, yb], '( %s x. %s ) <_ ( R x. R )' % (AY, AY))
    yl2 = D(w, ph, 'eqbrtrrd', [yy, yl], '( %s x. %s ) <_ ( R x. R )' % (Y, Y))
    fa = D(w, ph, 'lemul2ad', [D(w, ph, 'remulcld', [yr, yr], '( %s x. %s ) e. RR' % (Y, Y)), D(w, ph, 'remulcld', [rr, rr], '( R x. R ) e. RR'), ptr, D(w, ph, 'rpge0d', [ptp], '0 <_ %s' % PT), yl2],
           '( %s x. ( %s x. %s ) ) <_ ( %s x. ( R x. R ) )' % (PT, Y, Y, PT))
    X2 = '( %s ^ 2 )' % X
    E1 = '( ( %s x. ( R ^ 2 ) ) + -u ( %s x. %s ) )' % (PT, PT, X2)
    fb = both(w, ph, D(w, ph, 'oveq2d', [D(w, ph, 'sqvald', [xc], '%s = ( %s x. %s )' % (X2, X, X))], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (PT, X2, PT, X, X)),
              '( %s x. %s )' % (PT, X2), '( %s x. ( %s x. %s ) )' % (PT, X, X))
    fc = both(w, ph, D(w, ph, 'oveq2d', [D(w, ph, 'sqvald', [D(w, ph, 'recnd', [rr], 'R e. CC')], '( R ^ 2 ) = ( R x. R )')], '( %s x. ( R ^ 2 ) ) = ( %s x. ( R x. R ) )' % (PT, PT)),
              '( %s x. ( R ^ 2 ) )' % PT, '( %s x. ( R x. R ) )' % PT)
    fd = both(w, ph, rz, RZ, RZv)
    lvs = {'_pi': cst(w, ph, 'pire', '_pi e. RR'), 'T': D(w, ph, 'rpred', [tp], 'T e. RR'), X: xr, Y: yr, 'R': rr}
    rzr = D(w, ph, 'recld', [zc], '%s e. RR' % RZ)
    lvs[RZ] = rzr; lvs[X2] = D(w, ph, 'resqcld', [xr], '%s e. RR' % X2); lvs['( R ^ 2 )'] = D(w, ph, 'resqcld', [rr], '( R ^ 2 ) e. RR')
    ek = lin.linarith(w, ph, [fa] + fb + fc + fd, '%s <_ %s' % (RZ, E1), leaves=lvs, atoms=[X2, '( R ^ 2 )', RZ], products=True)
    PR2 = '( %s x. ( R ^ 2 ) )' % PT; PX2 = '( %s x. %s )' % (PT, X2)
    pr2 = D(w, ph, 'remulcld', [ptr, D(w, ph, 'resqcld', [rr], '( R ^ 2 ) e. RR')], '%s e. RR' % PR2)
    px2 = D(w, ph, 'remulcld', [ptr, D(w, ph, 'resqcld', [xr], '%s e. RR' % X2)], '%s e. RR' % PX2)
    e1r = D(w, ph, 'readdcld', [pr2, D(w, ph, 'renegcld', [px2], '-u %s e. RR' % PX2)], '%s e. RR' % E1)
    m2a = D(w, ph, 'mpbid', [ek, D(w, ph, 'syl2anc', [rzr, e1r, w.inst('efle')], '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (RZ, E1, RZ, E1))], '( exp ` %s ) <_ ( exp ` %s )' % (RZ, E1))
    N2 = '( ( exp ` %s ) x. ( exp ` -u %s ) )' % (PR2, PX2)
    m2e = D(w, ph, 'syl2anc', [D(w, ph, 'recnd', [pr2], '%s e. CC' % PR2), D(w, ph, 'recnd', [D(w, ph, 'renegcld', [px2], '-u %s e. RR' % PX2)], '-u %s e. CC' % PX2), w.inst('efadd')], '( exp ` %s ) = %s' % (E1, N2))
    m2n = D(w, ph, 'eqbrtrd', [ae, D(w, ph, 'breqtrd', [m2a, m2e], '( exp ` %s ) <_ %s' % (RZ, N2))], '%s <_ %s' % (M2, N2))
    m2r = D(w, ph, 'abscld', [D(w, ph, 'efcld', [zc], '%s e. CC' % EZ)], '%s e. RR' % M2)
    n2r = D(w, ph, 'remulcld', [D(w, ph, 'reefcld', [pr2], '( exp ` %s ) e. RR' % PR2), D(w, ph, 'reefcld', [D(w, ph, 'renegcld', [px2], '-u %s e. RR' % PX2)], '( exp ` -u %s ) e. RR' % PX2)], '%s e. RR' % N2)
    f1 = D(w, ph, 'lemul12ad', [m1r, n1r, m2r, n2r, D(w, ph, 'absge0d', [upc], '0 <_ %s' % M1), D(w, ph, 'absge0d', [D(w, ph, 'efcld', [zc], '%s e. CC' % EZ)], '0 <_ %s' % M2), m1n, m2n],
           '( %s x. %s ) <_ ( %s x. %s )' % (M1, M2, N1, N2))
    gre = D(w, ph, 'syl2anc', [tp, xr, w.inst('zl3gre')], '( ( 1 + %s ) x. ( exp ` -u %s ) ) <_ ( ( exp ` ( 1 / %s ) ) x. ( 2 ^c -u %s ) )' % (A, PX2, PT, A))
    K = '( ( 1 + C ) x. ( exp ` %s ) )' % PR2
    kr = D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), cr], '( 1 + C ) e. RR'), D(w, ph, 'reefcld', [pr2], '( exp ` %s ) e. RR' % PR2)], '%s e. RR' % K)
    k0 = D(w, ph, 'mulge0d', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), cr], '( 1 + C ) e. RR'), D(w, ph, 'reefcld', [pr2], '( exp ` %s ) e. RR' % PR2),
                              lin.linarith(w, ph, [c0], '0 <_ ( 1 + C )', leaves={'C': cr}), D(w, ph, 'rpge0d', [D(w, ph, 'rpefcld', [pr2], '( exp ` %s ) e. RR+' % PR2)], '0 <_ ( exp ` %s )' % PR2)], '0 <_ %s' % K)
    G1 = '( ( 1 + %s ) x. ( exp ` -u %s ) )' % (A, PX2); G2 = '( ( exp ` ( 1 / %s ) ) x. ( 2 ^c -u %s ) )' % (PT, A)
    f2 = D(w, ph, 'lemul2ad', [D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), ar], '( 1 + %s ) e. RR' % A), D(w, ph, 'reefcld', [D(w, ph, 'renegcld', [px2], '-u %s e. RR' % PX2)], '( exp ` -u %s ) e. RR' % PX2)], '%s e. RR' % G1),
                               D(w, ph, 'remulcld', [D(w, ph, 'reefcld', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), ptp], '( 1 / %s ) e. RR' % PT)], '( exp ` ( 1 / %s ) ) e. RR' % PT),
                                                     D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [ar], '-u %s e. RR' % A)], '( 2 ^c -u %s ) e. RR+' % A)], '( 2 ^c -u %s ) e. RR' % A)], '%s e. RR' % G2),
                               kr, k0, gre], '( %s x. %s ) <_ ( %s x. %s )' % (K, G1, K, G2))
    FIN = '( ( ( 1 + C ) x. ( ( exp ` %s ) x. ( exp ` ( 1 / %s ) ) ) ) x. ( 2 ^c -u %s ) )' % (PR2, PT, A)
    lvf = {M1: m1r, M2: m2r, 'C': cr, A: ar, '( exp ` %s )' % PR2: D(w, ph, 'reefcld', [pr2], '( exp ` %s ) e. RR' % PR2), '( exp ` -u %s )' % PX2: D(w, ph, 'reefcld', [D(w, ph, 'renegcld', [px2], '-u %s e. RR' % PX2)], '( exp ` -u %s ) e. RR' % PX2),
           '( exp ` ( 1 / %s ) )' % PT: D(w, ph, 'reefcld', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), ptp], '( 1 / %s ) e. RR' % PT)], '( exp ` ( 1 / %s ) ) e. RR' % PT),
           '( 2 ^c -u %s )' % A: D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [ar], '-u %s e. RR' % A)], '( 2 ^c -u %s ) e. RR+' % A)], '( 2 ^c -u %s ) e. RR' % A),
           '( abs ` ( %s x. %s ) )' % (UP, EZ): D(w, ph, 'abscld', [D(w, ph, 'mulcld', [upc, D(w, ph, 'efcld', [zc], '%s e. CC' % EZ)], '( %s x. %s ) e. CC' % (UP, EZ))], '( abs ` ( %s x. %s ) ) e. RR' % (UP, EZ))}
    at = list(lvf.keys())
    c1c = D(w, ph, 'recnd', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), cr], '( 1 + C ) e. RR')], '( 1 + C ) e. CC')
    a1c = D(w, ph, 'recnd', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), ar], '( 1 + %s ) e. RR' % A)], '( 1 + %s ) e. CC' % A)
    epc = D(w, ph, 'efcld', [D(w, ph, 'recnd', [pr2], '%s e. CC' % PR2)], '( exp ` %s ) e. CC' % PR2)
    enc = D(w, ph, 'efcld', [D(w, ph, 'recnd', [D(w, ph, 'renegcld', [px2], '-u %s e. RR' % PX2)], '-u %s e. CC' % PX2)], '( exp ` -u %s ) e. CC' % PX2)
    eic = D(w, ph, 'efcld', [D(w, ph, 'recnd', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), ptp], '( 1 / %s ) e. RR' % PT)], '( 1 / %s ) e. CC' % PT)], '( exp ` ( 1 / %s ) ) e. CC' % PT)
    tac = D(w, ph, 'recnd', [D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [ar], '-u %s e. RR' % A)], '( 2 ^c -u %s ) e. RR+' % A)], '( 2 ^c -u %s ) e. RR' % A)], '( 2 ^c -u %s ) e. CC' % A)
    m4 = D(w, ph, 'mul4d', [c1c, a1c, epc, enc], '( %s x. %s ) = ( %s x. %s )' % (N1, N2, K, G1))
    EI = '( exp ` ( 1 / %s ) )' % PT; TA = '( 2 ^c -u %s )' % A; EP = '( exp ` %s )' % PR2
    kc = D(w, ph, 'mulcld', [c1c, epc], '%s e. CC' % K)
    q1 = D(w, ph, 'eqcomd', [D(w, ph, 'mulassd', [kc, eic, tac], '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (K, EI, TA, K, G2))], '( %s x. %s ) = ( ( %s x. %s ) x. %s )' % (K, G2, K, EI, TA))
    q2 = D(w, ph, 'oveq1d', [D(w, ph, 'mulassd', [c1c, epc, eic], '( %s x. %s ) = ( ( 1 + C ) x. ( %s x. %s ) )' % (K, EI, EP, EI))], '( ( %s x. %s ) x. %s ) = %s' % (K, EI, TA, FIN))
    kg = D(w, ph, 'eqtrd', [q1, q2], '( %s x. %s ) = %s' % (K, G2, FIN))
    PE = '( abs ` ( %s x. %s ) )' % (UP, EZ)
    am1 = D(w, ph, 'absmuld', [upc, D(w, ph, 'efcld', [zc], '%s e. CC' % EZ)], '%s = ( %s x. %s )' % (PE, M1, M2))
    l1 = D(w, ph, 'breqtrd', [D(w, ph, 'eqbrtrd', [am1, f1], '%s <_ ( %s x. %s )' % (PE, N1, N2)), m4], '%s <_ ( %s x. %s )' % (PE, K, G1))
    fin = D(w, ph, 'breqtrd', [D(w, ph, 'letrd', [D(w, ph, 'abscld', [D(w, ph, 'mulcld', [upc, D(w, ph, 'efcld', [zc], '%s e. CC' % EZ)], '( %s x. %s ) e. CC' % (UP, EZ))], '%s e. RR' % PE),
                                                  D(w, ph, 'remulcld', [kr, D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), ar], '( 1 + %s ) e. RR' % A), D(w, ph, 'reefcld', [D(w, ph, 'renegcld', [px2], '-u %s e. RR' % PX2)], '( exp ` -u %s ) e. RR' % PX2)], '%s e. RR' % G1)], '( %s x. %s ) e. RR' % (K, G1)),
                                                  D(w, ph, 'remulcld', [kr, D(w, ph, 'remulcld', [D(w, ph, 'reefcld', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), ptp], '( 1 / %s ) e. RR' % PT)], '%s e. RR' % EI),
                                                                                             D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [ar], '-u %s e. RR' % A)], '%s e. RR+' % TA)], '%s e. RR' % TA)], '%s e. RR' % G2)], '( %s x. %s ) e. RR' % (K, G2)),
                                                  l1, f2], '%s <_ ( %s x. %s )' % (PE, K, G2)), kg], '%s <_ %s' % (PE, FIN))
    w.qed([fin], 'idi', S['zl3gcb'])
    go(w, only)


# ---------------------------------------------------------------- zl3fb
if __name__ == '__main__' and (not only or 'zl3fb' in only):
    w = W('zl3fb', 'The strip bound of the shifted Gaussian required by Poisson summation.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3fb'])
    tp = w.s([], 'simp1', '( %s -> T e. RR+ )' % ph); ar = w.s([], 'simp2', '( %s -> A e. RR )' % ph); pp = w.s([], 'simp3', '( %s -> P e. { 0 , 1 } )' % ph)
    PT = '( _pi x. T )'
    ptp = D(w, ph, 'rpmulcld', [cst(w, ph, 'pirp', '_pi e. RR+'), tp], '%s e. RR+' % PT)
    E1 = '( exp ` %s )' % PT; E2 = '( exp ` ( 1 / %s ) )' % PT; AA = '( abs ` A )'; TA = '( 2 ^c %s )' % AA
    ac = D(w, ph, 'recnd', [ar], 'A e. CC')
    aar = D(w, ph, 'abscld', [ac], '%s e. RR' % AA)
    e12 = D(w, ph, 'rpmulcld', [D(w, ph, 'rpefcld', [D(w, ph, 'rpred', [ptp], '%s e. RR' % PT)], '%s e. RR+' % E1), D(w, ph, 'rpefcld', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), ptp], '( 1 / %s ) e. RR' % PT)], '%s e. RR+' % E2)],
            '( %s x. %s ) e. RR+' % (E1, E2))
    K2 = '( 2 x. ( %s x. %s ) )' % (E1, E2)
    k2p = D(w, ph, 'rpmulcld', [cst(w, ph, '2rp', '2 e. RR+'), e12], '%s e. RR+' % K2)
    tap = D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), aar], '%s e. RR+' % TA)
    kfp = D(w, ph, 'rpmulcld', [k2p, tap], '%s e. RR+' % KF)
    Az = '( ( %s /\\ z e. CC ) /\\ ( abs ` ( Im ` z ) ) <_ 1 )' % ph
    zc = w.s([], 'simplr', '( %s -> z e. CC )' % Az); iz = w.s([], 'simpr', '( %s -> ( abs ` ( Im ` z ) ) <_ 1 )' % Az)
    L = lambda st, f: w.s([st], 'ad2antrr', '( %s -> %s )' % (Az, f))
    ar1 = L(ar, 'A e. RR'); ac1 = D(w, Az, 'recnd', [ar1], 'A e. CC'); tp1 = L(tp, 'T e. RR+'); pp1 = L(pp, 'P e. { 0 , 1 }')
    ZA = '( z + A )'
    zac = D(w, Az, 'addcld', [zc, ac1], '%s e. CC' % ZA)
    body = '( ( ( y + A ) ^ P ) x. ( exp ` -u ( ( _pi x. T ) x. ( ( y + A ) ^ 2 ) ) ) )'
    fv, val = fvm(w, Az, 'y', body, 'z', zc, g)
    rz = D(w, Az, 'eqtrd', [D(w, Az, 'readdd', [zc, ac1], '( Re ` %s ) = ( ( Re ` z ) + ( Re ` A ) )' % ZA), D(w, Az, 'oveq2d', [D(w, Az, 'rered', [ar1], '( Re ` A ) = A')], '( ( Re ` z ) + ( Re ` A ) ) = ( ( Re ` z ) + A )')],
           '( Re ` %s ) = ( ( Re ` z ) + A )' % ZA)
    imz = D(w, Az, 'eqtrd', [D(w, Az, 'imaddd', [zc, ac1], '( Im ` %s ) = ( ( Im ` z ) + ( Im ` A ) )' % ZA),
                             D(w, Az, 'eqtrd', [D(w, Az, 'oveq2d', [D(w, Az, 'reim0d', [ar1], '( Im ` A ) = 0')], '( ( Im ` z ) + ( Im ` A ) ) = ( ( Im ` z ) + 0 )'),
                                                D(w, Az, 'addridd', [D(w, Az, 'recnd', [D(w, Az, 'imcld', [zc], '( Im ` z ) e. RR')], '( Im ` z ) e. CC')], '( ( Im ` z ) + 0 ) = ( Im ` z )')], '( ( Im ` z ) + ( Im ` A ) ) = ( Im ` z )')],
            '( Im ` %s ) = ( Im ` z )' % ZA)
    IV = '( abs ` ( Im ` %s ) )' % ZA; RV = '( abs ` ( Re ` %s ) )' % ZA
    ivb = D(w, Az, 'eqbrtrd', [D(w, Az, 'fveq2d', [imz], '%s = ( abs ` ( Im ` z ) )' % IV), iz], '%s <_ 1' % IV)
    ub = D(w, Az, 'letrd', [D(w, Az, 'abscld', [zac], '( abs ` %s ) e. RR' % ZA), D(w, Az, 'readdcld', [D(w, Az, 'abscld', [D(w, Az, 'recnd', [D(w, Az, 'recld', [zac], '( Re ` %s ) e. RR' % ZA)], '( Re ` %s ) e. CC' % ZA)], '%s e. RR' % RV),
                                                                                                                 D(w, Az, 'abscld', [D(w, Az, 'recnd', [D(w, Az, 'imcld', [zac], '( Im ` %s ) e. RR' % ZA)], '( Im ` %s ) e. CC' % ZA)], '%s e. RR' % IV)], '( %s + %s ) e. RR' % (RV, IV)),
                            D(w, Az, 'readdcld', [D(w, Az, 'abscld', [D(w, Az, 'recnd', [D(w, Az, 'recld', [zac], '( Re ` %s ) e. RR' % ZA)], '( Re ` %s ) e. CC' % ZA)], '%s e. RR' % RV), cst(w, Az, '1re', '1 e. RR')], '( %s + 1 ) e. RR' % RV),
                            D(w, Az, 'syl', [zac, w.inst('abscrle')], '( abs ` %s ) <_ ( %s + %s )' % (ZA, RV, IV)),
                            D(w, Az, 'mpbid', [ivb, D(w, Az, 'leadd2d', [D(w, Az, 'abscld', [D(w, Az, 'recnd', [D(w, Az, 'imcld', [zac], '( Im ` %s ) e. RR' % ZA)], '( Im ` %s ) e. CC' % ZA)], '%s e. RR' % IV), cst(w, Az, '1re', '1 e. RR'),
                                                                          D(w, Az, 'abscld', [D(w, Az, 'recnd', [D(w, Az, 'recld', [zac], '( Re ` %s ) e. RR' % ZA)], '( Re ` %s ) e. CC' % ZA)], '%s e. RR' % RV)],
                                                         '( %s <_ 1 <-> ( %s + %s ) <_ ( %s + 1 ) )' % (IV, RV, IV, RV))], '( %s + %s ) <_ ( %s + 1 )' % (RV, IV, RV))],
            '( abs ` %s ) <_ ( %s + 1 )' % (ZA, RV))
    GB = '( ( ( 1 + 1 ) x. ( ( exp ` ( %s x. ( 1 ^ 2 ) ) ) x. %s ) ) x. ( 2 ^c -u %s ) )' % (PT, E2, RV)
    gcb = D(w, Az, 'syl', [w.s([w.s([tp1, pp1], 'jca', '( %s -> ( T e. RR+ /\\ P e. { 0 , 1 } ) )' % Az), w.s([zac, zac], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Az, ZA, ZA)),
                                w.s([w.s([cst(w, Az, '1re', '1 e. RR'), cst(w, Az, '1re', '1 e. RR')], 'jca', '( %s -> ( 1 e. RR /\\ 1 e. RR ) )' % Az),
                                     w.s([cst(w, Az, '0le1', '0 <_ 1'), ub, ivb], '3jca', '( %s -> ( 0 <_ 1 /\\ ( abs ` %s ) <_ ( %s + 1 ) /\\ %s <_ 1 ) )' % (Az, ZA, RV, IV))], 'jca',
                                    '( %s -> ( ( 1 e. RR /\\ 1 e. RR ) /\\ ( 0 <_ 1 /\\ ( abs ` %s ) <_ ( %s + 1 ) /\\ %s <_ 1 ) ) )' % (Az, ZA, RV, IV))], '3jca',
                               '( %s -> ( ( T e. RR+ /\\ P e. { 0 , 1 } ) /\\ ( %s e. CC /\\ %s e. CC ) /\\ ( ( 1 e. RR /\\ 1 e. RR ) /\\ ( 0 <_ 1 /\\ ( abs ` %s ) <_ ( %s + 1 ) /\\ %s <_ 1 ) ) ) )' % (Az, ZA, ZA, ZA, RV, IV)),
                          w.inst('zl3gcb')], '( abs ` %s ) <_ %s' % (val, GB))
    # simplify the constant
    one = D(w, Az, 'eqtrd', [D(w, Az, 'oveq2d', [cst(w, Az, 'sq1', '( 1 ^ 2 ) = 1')], '( %s x. ( 1 ^ 2 ) ) = ( %s x. 1 )' % (PT, PT)), D(w, Az, 'mulridd', [D(w, Az, 'rpcnd', [L(ptp, '%s e. RR+' % PT)], '%s e. CC' % PT)], '( %s x. 1 ) = %s' % (PT, PT))],
            '( %s x. ( 1 ^ 2 ) ) = %s' % (PT, PT))
    c1 = D(w, Az, 'oveq1d', [D(w, Az, 'oveq12d', [cst(w, Az, '1p1e2', '( 1 + 1 ) = 2'), D(w, Az, 'oveq1d', [D(w, Az, 'fveq2d', [one], '( exp ` ( %s x. ( 1 ^ 2 ) ) ) = %s' % (PT, E1))], '( ( exp ` ( %s x. ( 1 ^ 2 ) ) ) x. %s ) = ( %s x. %s )' % (PT, E2, E1, E2))],
                                                  '( ( 1 + 1 ) x. ( ( exp ` ( %s x. ( 1 ^ 2 ) ) ) x. %s ) ) = %s' % (PT, E2, K2))], '%s = ( %s x. ( 2 ^c -u %s ) )' % (GB, K2, RV))
    # 2 ^ -| Re ( z + A ) | <_ 2 ^ | A | x. 2 ^ -| Re z |
    RZ = '( Re ` z )'; ARZ = '( abs ` %s )' % RZ
    rzr = D(w, Az, 'recld', [zc], '%s e. RR' % RZ)
    rvr = D(w, Az, 'abscld', [D(w, Az, 'recnd', [D(w, Az, 'recld', [zac], '( Re ` %s ) e. RR' % ZA)], '( Re ` %s ) e. CC' % ZA)], '%s e. RR' % RV)
    arz = D(w, Az, 'abscld', [D(w, Az, 'recnd', [rzr], '%s e. CC' % RZ)], '%s e. RR' % ARZ)
    aar1 = L(aar, '%s e. RR' % AA)
    # | Re z | <_ | Re ( z + A ) | + | A |
    rza = '( ( Re ` z ) + A )'
    t0 = D(w, Az, 'syl2anc', [D(w, Az, 'recnd', [D(w, Az, 'readdcld', [rzr, ar1], '%s e. RR' % rza)], '%s e. CC' % rza), ac1, w.inst('abs2dif2d') if False else w.inst('abssub')], 'x') if False else None
    ab1 = D(w, Az, 'abs2dif2d', [D(w, Az, 'recnd', [D(w, Az, 'readdcld', [rzr, ar1], '%s e. RR' % rza)], '%s e. CC' % rza), ac1], '( abs ` ( %s - A ) ) <_ ( ( abs ` %s ) + %s )' % (rza, rza, AA))
    pc_ = D(w, Az, 'pncand', [D(w, Az, 'recnd', [rzr], '%s e. CC' % RZ), ac1], '( %s - A ) = %s' % (rza, RZ))
    ab2 = D(w, Az, 'eqbrtrrd', [D(w, Az, 'fveq2d', [pc_], '( abs ` ( %s - A ) ) = %s' % (rza, ARZ)), ab1], '%s <_ ( ( abs ` %s ) + %s )' % (ARZ, rza, AA))
    ab3 = D(w, Az, 'breqtrrd', [ab2, D(w, Az, 'oveq1d', [D(w, Az, 'fveq2d', [rz], '%s = ( abs ` %s )' % (RV, rza))], '( %s + %s ) = ( ( abs ` %s ) + %s )' % (RV, AA, rza, AA))], '%s <_ ( %s + %s )' % (ARZ, RV, AA))
    ex_ = lin.linarith(w, Az, [ab3], '-u %s <_ ( %s + -u %s )' % (RV, AA, ARZ), leaves={RV: rvr, AA: aar1, ARZ: arz})
    pl = D(w, Az, 'cxplead', [cst(w, Az, '2re', '2 e. RR'), cst(w, Az, '1le2', '1 <_ 2'), D(w, Az, 'renegcld', [rvr], '-u %s e. RR' % RV), D(w, Az, 'readdcld', [aar1, D(w, Az, 'renegcld', [arz], '-u %s e. RR' % ARZ)], '( %s + -u %s ) e. RR' % (AA, ARZ)), ex_],
            '( 2 ^c -u %s ) <_ ( 2 ^c ( %s + -u %s ) )' % (RV, AA, ARZ))
    pe = D(w, Az, 'cxpaddd', [cst(w, Az, '2cn', '2 e. CC'), cst(w, Az, '2ne0', '2 =/= 0'), D(w, Az, 'recnd', [aar1], '%s e. CC' % AA), D(w, Az, 'recnd', [D(w, Az, 'renegcld', [arz], '-u %s e. RR' % ARZ)], '-u %s e. CC' % ARZ)],
           '( 2 ^c ( %s + -u %s ) ) = ( %s x. ( 2 ^c -u %s ) )' % (AA, ARZ, TA, ARZ))
    k2r = D(w, Az, 'rpred', [L(k2p, '%s e. RR+' % K2)], '%s e. RR' % K2)
    TR = '( 2 ^c -u %s )' % ARZ
    trr = D(w, Az, 'rpred', [D(w, Az, 'rpcxpcld', [cst(w, Az, '2rp', '2 e. RR+'), D(w, Az, 'renegcld', [arz], '-u %s e. RR' % ARZ)], '%s e. RR+' % TR)], '%s e. RR' % TR)
    tar = D(w, Az, 'rpred', [L(tap, '%s e. RR+' % TA)], '%s e. RR' % TA)
    m = D(w, Az, 'lemul2ad', [D(w, Az, 'rpred', [D(w, Az, 'rpcxpcld', [cst(w, Az, '2rp', '2 e. RR+'), D(w, Az, 'renegcld', [rvr], '-u %s e. RR' % RV)], '( 2 ^c -u %s ) e. RR+' % RV)], '( 2 ^c -u %s ) e. RR' % RV),
                              D(w, Az, 'remulcld', [tar, trr], '( %s x. %s ) e. RR' % (TA, TR)), k2r, D(w, Az, 'rpge0d', [L(k2p, '%s e. RR+' % K2)], '0 <_ %s' % K2), D(w, Az, 'breqtrd', [pl, pe], '( 2 ^c -u %s ) <_ ( %s x. %s )' % (RV, TA, TR))],
          '( %s x. ( 2 ^c -u %s ) ) <_ ( %s x. ( %s x. %s ) )' % (K2, RV, K2, TA, TR))
    asc = D(w, Az, 'eqcomd', [D(w, Az, 'mulassd', [D(w, Az, 'recnd', [k2r], '%s e. CC' % K2), D(w, Az, 'recnd', [tar], '%s e. CC' % TA), D(w, Az, 'recnd', [trr], '%s e. CC' % TR)],
                                   '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (KF, TR, K2, TA, TR))], '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (K2, TA, TR, KF, TR))
    vr_ = D(w, Az, 'abscld', [D(w, Az, 'eqeltrrd', [fv, D(w, Az, 'ffvelcdmd', [D(w, Az, 'fmptd', [], 'x') if False else None, zc], 'x') if False else None], 'x') if False else None], 'x') if False else None
    valc = D(w, Az, 'mulcld', [D(w, Az, 'expcld', [zac, D(w, Az, 'syl', [pp1, w.inst('elpri')], '( P = 0 \\/ P = 1 )') if False else None], 'x') if False else None, None], 'x') if False else None
    p0n = w.s([w.s([w.s([pp1, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % Az)], 'idi', '( %s -> ( P = 0 \\/ P = 1 ) )' % Az)], 'idi', '( %s -> ( P = 0 \\/ P = 1 ) )' % Az)
    A0 = '( %s /\\ P = 0 )' % Az; A1_ = '( %s /\\ P = 1 )' % Az
    pn0 = w.s([w.s([w.s([], 'simpr', '( %s -> P = 0 )' % A0), cst(w, A0, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> P e. NN0 )' % A0),
               w.s([w.s([], 'simpr', '( %s -> P = 1 )' % A1_), cst(w, A1_, '1nn0', '1 e. NN0')], 'eqeltrd', '( %s -> P e. NN0 )' % A1_), p0n], 'mpjaodan', '( %s -> P e. NN0 )' % Az)
    PTc = D(w, Az, 'rpcnd', [L(ptp, '%s e. RR+' % PT)], '%s e. CC' % PT)
    valc = D(w, Az, 'mulcld', [D(w, Az, 'expcld', [zac, pn0], '( %s ^ P ) e. CC' % ZA), D(w, Az, 'efcld', [D(w, Az, 'negcld', [D(w, Az, 'mulcld', [PTc, D(w, Az, 'sqcld', [zac], '( %s ^ 2 ) e. CC' % ZA)], '( %s x. ( %s ^ 2 ) ) e. CC' % (PT, ZA))],
                                                                                                                                   '-u ( %s x. ( %s ^ 2 ) ) e. CC' % (PT, ZA))], '( exp ` -u ( %s x. ( %s ^ 2 ) ) ) e. CC' % (PT, ZA))], '%s e. CC' % val)
    vr_ = D(w, Az, 'abscld', [valc], '( abs ` %s ) e. RR' % val)
    m1r = D(w, Az, 'remulcld', [k2r, D(w, Az, 'rpred', [D(w, Az, 'rpcxpcld', [cst(w, Az, '2rp', '2 e. RR+'), D(w, Az, 'renegcld', [rvr], '-u %s e. RR' % RV)], '( 2 ^c -u %s ) e. RR+' % RV)], '( 2 ^c -u %s ) e. RR' % RV)], '( %s x. ( 2 ^c -u %s ) ) e. RR' % (K2, RV))
    m2r = D(w, Az, 'remulcld', [k2r, D(w, Az, 'remulcld', [tar, trr], '( %s x. %s ) e. RR' % (TA, TR))], '( %s x. ( %s x. %s ) ) e. RR' % (K2, TA, TR))
    fin = D(w, Az, 'breqtrd', [D(w, Az, 'letrd', [vr_, m1r, m2r, D(w, Az, 'breqtrd', [gcb, c1], '( abs ` %s ) <_ ( %s x. ( 2 ^c -u %s ) )' % (val, K2, RV)), m], '( abs ` %s ) <_ ( %s x. ( %s x. %s ) )' % (val, K2, TA, TR)), asc],
            '( abs ` %s ) <_ ( %s x. %s )' % (val, KF, TR))
    fin2 = D(w, Az, 'eqbrtrd', [D(w, Az, 'fveq2d', [fv], '( abs ` ( %s ` z ) ) = ( abs ` %s )' % (FF, val)), fin], '( abs ` ( %s ` z ) ) <_ ( %s x. %s )' % (FF, KF, TR))
    al = w.s([w.s([fin2], 'ex', '( ( %s /\\ z e. CC ) -> ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) ) )' % (ph, FF, KF, TR))], 'ralrimiva',
             '( %s -> A. z e. CC ( ( abs ` ( Im ` z ) ) <_ 1 -> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) ) )' % (ph, FF, KF, TR))
    w.qed([kfp, al], 'jca', S['zl3fb'])
    go(w, only)
