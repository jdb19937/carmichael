"""Sortie T21a: zone III (t21z3 = zoneIII_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21a_zz import *
import cl as _cl
from t21a_z1 import x_basics
lin.FASTPATH = True
lin.MAXDEG = 6


def gen_z3():
    w = W('t21z3', 'Zone III ( ` S <_ beta < tau = 1 - R / log X ` ): the log-free density folded ( ` C ( 9 / 2 ) ( 1 - S ) <_ 1 / 2 ` , constant 4) and summed along the grid gives ` S_III <_ 256 G Y exp ( - ( 9 / 200 ) R ) ` (Lean ` zoneIII_le ` ; ~ t21fold , ~ t21gz ).')
    A0 = ante_of(S['t21z3'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L_ = lambda s_, A_: _cl.lift(w, s_, A_)
    u = unpack(w, A0)
    body = LFD_BODY('G', 'C')
    nn, xr, xe, yr, nx, ny, yx, gr, g1, cr, c1, bst, rp, sr, s9, sT, fh = [u[k] for k in ['N e. NN', 'X e. RR', '( exp ` 1 ) <_ X', 'Y e. RR', 'N <_ ( X ^c %s )' % F191,
        '( N x. ( X ^c %s ) ) <_ Y' % F709, 'Y <_ X', 'G e. RR', '1 <_ G', 'C e. RR', '1 <_ C', body, 'R e. RR+', 'S e. RR', '%s <_ S' % F910, 'S <_ %s' % TAU,
        '( C x. ( %s x. ( 1 - S ) ) ) <_ %s' % (F92, HALF)]]
    L = LX
    one = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    e1r = st([one], 'reefcld', '( exp ` 1 ) e. RR')
    eg1 = ap_(w, A0, [st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')], 'efgt1', '1 < ( exp ` 1 )')
    x1 = lin.linarith(w, A0, [eg1, xe], '1 <_ X', leaves={'X': xr, '( exp ` 1 )': e1r})
    xp = st([xr, lin.linarith(w, A0, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    e1p = st([one], 'rpefcld', '( exp ` 1 ) e. RR+')
    lge = st([xe, st([e1p, xp], 'logled', '( ( exp ` 1 ) <_ X <-> ( log ` ( exp ` 1 ) ) <_ %s )' % L)], 'mpbid', '( log ` ( exp ` 1 ) ) <_ %s' % L)
    l1 = st([st([ap_(w, A0, [one], 'relogef', '( log ` ( exp ` 1 ) ) = 1')], 'eqcomd', '1 = ( log ` ( exp ` 1 ) )'), lge], 'eqbrtrd', '1 <_ %s' % L)
    lr = st([xp], 'relogcld', '%s e. RR' % L)
    lp = st([lr, lin.linarith(w, A0, [l1], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    RL = '( R / %s )' % L
    rlr = st([st([rp], 'rpred', 'R e. RR'), lp], 'rerpdivcld', '%s e. RR' % RL)
    rl0 = st([st([rp], 'rpred', 'R e. RR'), lp, st([rp], 'rpge0d', '0 <_ R')], 'divge0d', '0 <_ %s' % RL)
    taur = st([one, rlr], 'resubcld', '%s e. RR' % TAU)
    tau1 = lin.linarith(w, A0, [rl0], '%s <_ 1' % TAU, leaves={RL: rlr})
    g0 = lin.linarith(w, A0, [g1], '0 <_ G', leaves={'G': gr})
    Q = '( 4 x. G )'
    qr = st([st([w.s([], '4re', '4 e. RR')], 'a1i', '4 e. RR'), gr], 'remulcld', '%s e. RR' % Q)
    q0 = st([st([w.s([], '4re', '4 e. RR')], 'a1i', '4 e. RR'), gr, st([w.s([], '0le4' if False else 'x', 'x')], 'x', 'x') if False else st([num.le_lit(w, '0', '4')], 'a1i', '0 <_ 4'), g0], 'mulge0d', '0 <_ %s' % Q)
    hs = lin.linarith(w, A0, [s9], '%s <_ S' % HALF, leaves={'S': sr})
    sub = lambda text: ' '.join({'T': TAU, 'Q': Q}.get(t_, t_) for t_ in text.split())
    H1 = sub(GZH[1].split(' -> ', 1)[1][:-2])
    h1 = st([st([nn, st([xr, xe], 'jca', XE), st([yr, st([nx, ny], 'jca', LEVEL), yx], '3jca', '( Y e. RR /\\ %s /\\ Y <_ X )' % LEVEL)], '3jca', '( N e. NN /\\ %s /\\ ( Y e. RR /\\ %s /\\ Y <_ X ) )' % (XE, LEVEL)),
             st([st([sr, taur], 'jca', '( S e. RR /\\ %s e. RR )' % TAU), st([hs, sT, tau1], '3jca', '( %s <_ S /\\ S <_ %s /\\ %s <_ 1 )' % (HALF, TAU, TAU))], 'jca', '( ( S e. RR /\\ %s e. RR ) /\\ ( %s <_ S /\\ S <_ %s /\\ %s <_ 1 ) )' % (TAU, HALF, TAU, TAU)),
             st([qr, q0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (Q, Q))], '3jca', H1)
    # ---- the tails: context Ck2
    SK = '( S + ( k x. %s ) )' % LH
    Ck = '( %s /\\ ( k e. NN0 /\\ %s <_ %s ) )' % (A0, SK, TAU)
    Lk = lambda s_: L_(s_, Ck)
    kn = w.s([], 'simprl', '( %s -> k e. NN0 )' % Ck); skT = w.s([], 'simprr', '( %s -> %s <_ %s )' % (Ck, SK, TAU))
    hr_ = Lk(st([st([lp], 'rpreccld', '%s e. RR+' % LH)], 'rpred', '%s e. RR' % LH))
    KH = '( k x. %s )' % LH
    khr = w.s([w.s([kn], 'nn0red', '( %s -> k e. RR )' % Ck), hr_], 'remulcld', '( %s -> %s e. RR )' % (Ck, KH))
    kh0 = w.s([w.s([kn], 'nn0red', '( %s -> k e. RR )' % Ck), hr_, w.s([kn], 'nn0ge0d', '( %s -> 0 <_ k )' % Ck), Lk(st([st([lp], 'rpreccld', '%s e. RR+' % LH)], 'rpge0d', '0 <_ %s' % LH))], 'mulge0d', '( %s -> 0 <_ %s )' % (Ck, KH))
    skr = w.s([Lk(sr), khr], 'readdcld', '( %s -> %s e. RR )' % (Ck, SK))
    lv = {'S': Lk(sr), KH: khr, TAU: Lk(taur)}
    sk9 = lin.linarith(w, Ck, [kh0, Lk(s9)], '%s <_ %s' % (F910, SK), closure=clos(w, Ck, lv))
    sk0 = lin.linarith(w, Ck, [kh0, Lk(s9)], '0 < %s' % SK, closure=clos(w, Ck, lv))
    sk1 = lin.linarith(w, Ck, [skT, Lk(tau1)], '%s <_ 1' % SK, closure=clos(w, Ck, lv))
    W_ = '( %s x. ( 1 - %s ) )' % (F92, SK)
    wr_ = w.s([w.s([num.real(w, F92)], 'a1i', '( %s -> %s e. RR )' % (Ck, F92)), w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % Ck), skr], 'resubcld', '( %s -> ( 1 - %s ) e. RR )' % (Ck, SK))], 'remulcld', '( %s -> %s e. RR )' % (Ck, W_))
    lv2 = {'S': Lk(sr), KH: khr}
    w0_ = lin.linarith(w, Ck, [sk1], '0 <_ %s' % W_, closure=clos(w, Ck, lv2))
    W0 = '( %s x. ( 1 - S ) )' % F92
    wle = lin.linarith(w, Ck, [kh0], '%s <_ %s' % (W_, W0), closure=clos(w, Ck, lv2))
    cw = w.s([wr_, w.s([w.s([num.real(w, F92)], 'a1i', '( %s -> %s e. RR )' % (Ck, F92)), w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % Ck), Lk(sr)], 'resubcld', '( %s -> ( 1 - S ) e. RR )' % Ck)], 'remulcld', '( %s -> %s e. RR )' % (Ck, W0)),
              Lk(cr), Lk(lin.linarith(w, A0, [c1], '0 <_ C', leaves={'C': cr})), wle], 'lemul2ad', '( %s -> ( C x. %s ) <_ ( C x. %s ) )' % (Ck, W_, W0))
    cw2 = lin.linarith(w, Ck, [cw, Lk(fh)], '( C x. %s ) <_ ( 1 - %s )' % (W_, HALF), leaves={'( C x. %s )' % W_: w.s([Lk(cr), wr_], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (Ck, W_)), '( C x. %s )' % W0: w.s([Lk(cr), w.s([w.s([num.real(w, F92)], 'a1i', '( %s -> %s e. RR )' % (Ck, F92)), w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % Ck), Lk(sr)], 'resubcld', '( %s -> ( 1 - S ) e. RR )' % Ck)], 'remulcld', '( %s -> %s e. RR )' % (Ck, W0))], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (Ck, W0))})
    rhs_fold = lambda t_: '( ( G x. ( ( N x. ( %s ^c C ) ) ^c %s ) ) x. 1 )' % (t_, W_)
    def mono(Cx, got, rhs_b):
        # rhs_b = ( G x. ( ( N x. ( t ^c C ) ) ^c W ) ); the fold form multiplies by 1
        tr_ = w.s([], 'simplr', '( %s -> t e. RR )' % Cx)
        t2_ = w.s([], 'simprl', '( %s -> 2 <_ t )' % Cx)
        tp_ = w.s([tr_, lin.linarith(w, Cx, [t2_], '0 < t', leaves={'t': tr_})], 'elrpd', '( %s -> t e. RR+ )' % Cx)
        ntc = w.s([w.s([L_(nn, Cx)], 'nnrpd', '( %s -> N e. RR+ )' % Cx), w.s([tp_, L_(cr, Cx)], 'rpcxpcld', '( %s -> ( t ^c C ) e. RR+ )' % Cx)], 'rpmulcld', '( %s -> ( N x. ( t ^c C ) ) e. RR+ )' % Cx)
        pw = w.s([ntc, L_(wr_, Cx)], 'rpcxpcld', '( %s -> ( ( N x. ( t ^c C ) ) ^c %s ) e. RR+ )' % (Cx, W_))
        br = w.s([L_(gr, Cx), w.s([pw], 'rpred', '( %s -> ( ( N x. ( t ^c C ) ) ^c %s ) e. RR )' % (Cx, W_))], 'remulcld', '( %s -> %s e. RR )' % (Cx, rhs_b))
        e1 = w.s([w.s([br], 'recnd', '( %s -> %s e. CC )' % (Cx, rhs_b))], 'mulridd', '( %s -> ( %s x. 1 ) = %s )' % (Cx, rhs_b, rhs_b))
        return w.s([got, e1], 'breqtrrd', '( %s -> %s <_ %s )' % (Cx, NC(SK, 't'), rhs_fold('t')))
    fhyp = fold_hyp(w, Ck, body, Lk(bst), SK, skr, F910, sk9, sk1, X3, rhs_fold, mono)
    b = x_basics(w, A0, xr, xe)
    x32 = lin.linarith(w, A0, [b['x8']], '2 <_ %s' % X3, leaves={X3: b['x3r']})
    NW = '( N ^c %s )' % W_
    FR = '( ( ( G x. %s ) x. 1 ) x. ( 2 + ( 1 / %s ) ) )' % (NW, HALF)
    fo = ap_(w, Ck, [Lk(nn), skr, sk0, sk1, Lk(b['x3r']), Lk(x32), Lk(gr), Lk(g0), Lk(one), Lk(st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1')), Lk(cr), wr_, w0_,
                     Lk(st([num.rp(w, HALF)], 'a1i', '%s e. RR+' % HALF)), Lk(st([num.le_lit(w, HALF, '1')], 'a1i', '%s <_ 1' % HALF)), cw2, fhyp], 't21fold', '%s <_ %s' % (WS(SK, X3), FR))
    nwr = w.s([Lk(st([nn], 'nnred', 'N e. RR')), Lk(st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')), wr_], 'recxpcld', '( %s -> %s e. RR )' % (Ck, NW))
    ck = _cl.Closure(w, Ck, {})
    ck.leaf('G', 'RR', Lk(gr)); ck.leaf(NW, 'RR', nwr)
    rr2 = w.s([w.s([num.cc(w, '2')], 'a1i', '( %s -> 2 e. CC )' % Ck), w.s([num.ne0_nat(w, 2)], 'a1i', '( %s -> 2 =/= 0 )' % Ck)], 'recrecd', '( %s -> ( 1 / %s ) = 2 )' % (Ck, HALF))
    FR2 = '( ( ( G x. %s ) x. 1 ) x. ( 2 + 2 ) )' % NW
    fe = w.s([w.s([rr2], 'oveq2d', '( %s -> ( 2 + ( 1 / %s ) ) = ( 2 + 2 ) )' % (Ck, HALF))], 'oveq2d', '( %s -> %s = %s )' % (Ck, FR, FR2))
    eqf = w.s([fe, lin.lineq(w, Ck, FR2, '( %s x. %s )' % (Q, NW), closure=ck, products=True)], 'eqtrd', '( %s -> %s = ( %s x. %s ) )' % (Ck, FR, Q, NW))
    h2 = w.s([fo, eqf], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (Ck, WS(SK, X3), Q, NW))
    ET = '( X ^c ( -u %s x. ( 1 - %s ) ) )' % (F9200, TAU)
    gzc = w.s([h1, h2], 't21gz', '( %s -> %s <_ ( %s x. ( ( ; 6 4 x. Y ) x. %s ) ) )' % (A0, ZS(X3, 'Y', 'S', TAU), Q, ET))
    # the exponent
    OT = '( 1 - %s )' % TAU
    e9 = st([num.real(w, '-u %s' % F9200)], 'a1i', '-u %s e. RR' % F9200)
    otr = st([one, taur], 'resubcld', '%s e. RR' % OT)
    Z_ = '( -u %s x. %s )' % (F9200, OT)
    cxe = st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([st([e9, otr], 'remulcld', '%s e. RR' % Z_)], 'recnd', '%s e. CC' % Z_)], 'cxpefd', '%s = ( exp ` ( %s x. %s ) )' % (ET, Z_, L))
    ot = lin.lineq(w, A0, OT, RL, leaves={RL: rlr})
    ma = st([st([e9], 'recnd', '-u %s e. CC' % F9200), st([otr], 'recnd', '%s e. CC' % OT), st([lr], 'recnd', '%s e. CC' % L)], 'mulassd', '( %s x. %s ) = ( -u %s x. ( %s x. %s ) )' % (Z_, L, F9200, OT, L))
    dc = st([st([st([rp], 'rpred', 'R e. RR')], 'recnd', 'R e. CC'), st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L)], 'divcan1d', '( %s x. %s ) = R' % (RL, L))
    ol = st([st([ot], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (OT, L, RL, L)), dc], 'eqtrd', '( %s x. %s ) = R' % (OT, L))
    arg = st([ma, st([ol], 'oveq2d', '( -u %s x. ( %s x. %s ) ) = ( -u %s x. R )' % (F9200, OT, L, F9200))], 'eqtrd', '( %s x. %s ) = ( -u %s x. R )' % (Z_, L, F9200))
    EXR = '( exp ` ( -u %s x. R ) )' % F9200
    etq = st([cxe, st([arg], 'fveq2d', '( exp ` ( %s x. %s ) ) = %s' % (Z_, L, EXR))], 'eqtrd', '%s = %s' % (ET, EXR))
    fin0 = st([gzc, st([st([etq], 'oveq2d', '( ( ; 6 4 x. Y ) x. %s ) = ( ( ; 6 4 x. Y ) x. %s )' % (ET, EXR))], 'oveq2d', '( %s x. ( ( ; 6 4 x. Y ) x. %s ) ) = ( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (Q, ET, Q, EXR))], 'breqtrd',
               '%s <_ ( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (ZS(X3, 'Y', 'S', TAU), Q, EXR))
    c0 = _cl.Closure(w, A0, {})
    c0.leaf('G', 'RR', gr); c0.leaf('Y', 'RR', yr); c0.leaf(EXR, 'RR', st([st([e9, st([rp], 'rpred', 'R e. RR')], 'remulcld', '( -u %s x. R ) e. RR' % F9200)], 'reefcld', '%s e. RR' % EXR))
    eqz = lin.lineq(w, A0, '( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (Q, EXR), '( ( ( ; ; 2 5 6 x. G ) x. Y ) x. %s )' % EXR, closure=c0, products=True)
    fin = st([fin0, eqz], 'breqtrd', '%s <_ ( ( ( ; ; 2 5 6 x. G ) x. Y ) x. %s )' % (ZS(X3, 'Y', 'S', TAU), EXR))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21z3']))
    return run(w)


if __name__ == '__main__':
    gen_z3()
