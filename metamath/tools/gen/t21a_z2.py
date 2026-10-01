"""Sortie T21a: zone II (t21z2 = zoneII_le)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21a_zz import *
import cl as _cl
from t21a_z1 import x_basics
lin.FASTPATH = True
lin.MAXDEG = 6


def gen_z2():
    w = W('t21z2', 'Zone II ( ` 39 / 50 <_ beta < sigma* ` ): the logged density (profile ` P <_ 7 / 2 ` , ` C <_ 5 / 4 ` , fold constant ` 2 + 80 / 3 <_ 29 ` ) folded at ` T = X ^ 3 ` and summed along the grid; ` X ^ ( - ( 9 / 200 ) ( 1 - sigma* ) ) = ( log X ) ^ ( - ( 9 / 4 ) ( K + 2 ) ) ` absorbs ` ( 5 log X ) ^ K ` : ` S_II <_ E Y / 27 ` (Lean ` zoneII_le ` ; ~ t21fold , ~ t21gz ).')
    A0 = ante_of(S['t21z2'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L_ = lambda s_, A_: _cl.lift(w, s_, A_)
    u = unpack(w, A0)
    body = LGD_BODY('H', 'P', 'C', 'K')
    C501 = '; ; ; ; 5 0 1 1 2'
    L = LX
    HX = '( ( %s x. ( 5 ^ K ) ) x. H ) <_ ( E x. ( %s ^c %s ) )' % (C501, L, F92)
    nn, xr, xe, yr, er, nx, ny, yx, hr, h1, pr, p0, p72, cr, c1, c54, kn, bst, s39, hx = [u[k_] for k_ in ['N e. NN', 'X e. RR', '( exp ` 1 ) <_ X', 'Y e. RR', 'E e. RR',
        'N <_ ( X ^c %s )' % F191, '( N x. ( X ^c %s ) ) <_ Y' % F709, 'Y <_ X', 'H e. RR', '1 <_ H', 'P e. RR', '0 <_ P', 'P <_ ( 7 / 2 )', 'C e. RR', '1 <_ C', 'C <_ ( 5 / 4 )',
        'K e. NN0', body, '%s <_ %s' % (F3950, SSTAR), HX]]
    b = x_basics(w, A0, xr, xe)
    lr = b['lr']; one = b['one']
    lp = st([lr, lin.linarith(w, A0, [b['l1']], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    LL = '( log ` %s )' % L
    llr = st([lp], 'relogcld', '%s e. RR' % LL)
    ll0 = st([lr, b['l1']], 'logge0d', '0 <_ %s' % LL)
    K2 = '( K + 2 )'
    knr = st([kn], 'nn0red', 'K e. RR'); k0 = st([kn], 'nn0ge0d', '0 <_ K')
    k2r = st([knr, st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % K2)
    k20 = lin.linarith(w, A0, [k0], '0 <_ %s' % K2, leaves={'K': knr})
    ZK = '( %s x. %s )' % (K2, LL)
    zkr = st([k2r, llr], 'remulcld', '%s e. RR' % ZK); zk0 = st([k2r, llr, k20, ll0], 'mulge0d', '0 <_ %s' % ZK)
    NUM = '( ; 5 0 x. %s )' % ZK
    numr = st([st([num.real(w, '; 5 0')], 'a1i', '; 5 0 e. RR'), zkr], 'remulcld', '%s e. RR' % NUM)
    num0 = st([st([num.real(w, '; 5 0')], 'a1i', '; 5 0 e. RR'), zkr, st([num.le_lit(w, '0', '; 5 0')], 'a1i', '0 <_ ; 5 0'), zk0], 'mulge0d', '0 <_ %s' % NUM)
    FRc = '( %s / %s )' % (NUM, L)
    frr = st([numr, lp], 'rerpdivcld', '%s e. RR' % FRc); fr0 = st([numr, lp, num0], 'divge0d', '0 <_ %s' % FRc)
    ssr = st([one, frr], 'resubcld', '%s e. RR' % SSTAR)
    ss1 = lin.linarith(w, A0, [fr0], '%s <_ 1' % SSTAR, closure=clos(w, A0, {FRc: frr}))
    LG = '( ( 5 x. %s ) ^ K )' % L
    lgr = st([st([st([num.real(w, '5')], 'a1i', '5 e. RR'), lr], 'remulcld', '( 5 x. %s ) e. RR' % L), kn], 'reexpcld', '%s e. RR' % LG)
    lg0 = st([st([st([num.real(w, '5')], 'a1i', '5 e. RR'), lr], 'remulcld', '( 5 x. %s ) e. RR' % L), kn, st([st([num.real(w, '5')], 'a1i', '5 e. RR'), lr, st([num.le_lit(w, '0', '5')], 'a1i', '0 <_ 5'), st([lp], 'rpge0d', '0 <_ %s' % L)], 'mulge0d', '0 <_ ( 5 x. %s )' % L)], 'expge0d', '0 <_ %s' % LG)
    H29 = '( ; 2 9 x. H )'
    h0 = lin.linarith(w, A0, [h1], '0 <_ H', leaves={'H': hr})
    h29r = st([st([num.real(w, '; 2 9')], 'a1i', '; 2 9 e. RR'), hr], 'remulcld', '%s e. RR' % H29)
    h290 = st([st([num.real(w, '; 2 9')], 'a1i', '; 2 9 e. RR'), hr, st([num.le_lit(w, '0', '; 2 9')], 'a1i', '0 <_ ; 2 9'), h0], 'mulge0d', '0 <_ %s' % H29)
    Q = '( %s x. %s )' % (H29, LG)
    qr = st([h29r, lgr], 'remulcld', '%s e. RR' % Q); q0 = st([h29r, lgr, h290, lg0], 'mulge0d', '0 <_ %s' % Q)
    sub = lambda text: ' '.join({'T': SSTAR, 'Q': Q}.get(t_, t_) for t_ in text.split()).replace('S e. RR', '%s e. RR' % F3950)
    GZ1 = ' '.join({'T': SSTAR, 'Q': Q, 'S': F3950}.get(t_, t_) for t_ in GZH[1].split(' -> ', 1)[1][:-2].split())
    hs = st([num.le_lit(w, HALF, F3950)], 'a1i', '%s <_ %s' % (HALF, F3950))
    f39 = st([num.real(w, F3950)], 'a1i', '%s e. RR' % F3950)
    gz1 = st([st([nn, st([xr, xe], 'jca', XE), st([yr, st([nx, ny], 'jca', LEVEL), yx], '3jca', '( Y e. RR /\\ %s /\\ Y <_ X )' % LEVEL)], '3jca', '( N e. NN /\\ %s /\\ ( Y e. RR /\\ %s /\\ Y <_ X ) )' % (XE, LEVEL)),
              st([st([f39, ssr], 'jca', '( %s e. RR /\\ %s e. RR )' % (F3950, SSTAR)), st([hs, s39, ss1], '3jca', '( %s <_ %s /\\ %s <_ %s /\\ %s <_ 1 )' % (HALF, F3950, F3950, SSTAR, SSTAR))], 'jca',
                  '( ( %s e. RR /\\ %s e. RR ) /\\ ( %s <_ %s /\\ %s <_ %s /\\ %s <_ 1 ) )' % (F3950, SSTAR, HALF, F3950, F3950, SSTAR, SSTAR)),
              st([qr, q0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (Q, Q))], '3jca', GZ1)
    # ---- tails at Ck
    SK = '( %s + ( k x. %s ) )' % (F3950, LH)
    Ck = '( %s /\\ ( k e. NN0 /\\ %s <_ %s ) )' % (A0, SK, SSTAR)
    Lk = lambda s_: L_(s_, Ck)
    kk = w.s([], 'simprl', '( %s -> k e. NN0 )' % Ck); skT = w.s([], 'simprr', '( %s -> %s <_ %s )' % (Ck, SK, SSTAR))
    hr_ = Lk(st([st([lp], 'rpreccld', '%s e. RR+' % LH)], 'rpred', '%s e. RR' % LH))
    KH = '( k x. %s )' % LH
    khr = w.s([w.s([kk], 'nn0red', '( %s -> k e. RR )' % Ck), hr_], 'remulcld', '( %s -> %s e. RR )' % (Ck, KH))
    kh0 = w.s([w.s([kk], 'nn0red', '( %s -> k e. RR )' % Ck), hr_, w.s([kk], 'nn0ge0d', '( %s -> 0 <_ k )' % Ck), Lk(st([st([lp], 'rpreccld', '%s e. RR+' % LH)], 'rpge0d', '0 <_ %s' % LH))], 'mulge0d', '( %s -> 0 <_ %s )' % (Ck, KH))
    skr = w.s([Lk(f39), khr], 'readdcld', '( %s -> %s e. RR )' % (Ck, SK))
    cK = clos(w, Ck, {KH: khr, SSTAR: Lk(ssr)})
    sk39 = lin.linarith(w, Ck, [kh0], '%s <_ %s' % (F3950, SK), closure=cK)
    sk0 = lin.linarith(w, Ck, [kh0], '0 < %s' % SK, closure=cK)
    sk1 = lin.linarith(w, Ck, [skT, Lk(ss1)], '%s <_ 1' % SK, closure=cK)
    OM = '( 1 - %s )' % SK
    omr = w.s([Lk(one), skr], 'resubcld', '( %s -> %s e. RR )' % (Ck, OM))
    om0 = lin.linarith(w, Ck, [sk1], '0 <_ %s' % OM, closure=clos(w, Ck, {KH: khr}))
    om11 = lin.linarith(w, Ck, [kh0], '%s <_ ( ; 1 1 / ; 5 0 )' % OM, closure=clos(w, Ck, {KH: khr}))
    W_ = '( P x. %s )' % OM
    wr_ = w.s([Lk(pr), omr], 'remulcld', '( %s -> %s e. RR )' % (Ck, W_))
    w0_ = w.s([Lk(pr), omr, Lk(p0), om0], 'mulge0d', '( %s -> 0 <_ %s )' % (Ck, W_))
    lr_ = lambda t_: w.s([num.real(w, t_)], 'a1i', '( %s -> %s e. RR )' % (Ck, t_))
    F11 = '( ; 1 1 / ; 5 0 )'
    wle = w.s([Lk(pr), lr_('( 7 / 2 )'), omr, lr_(F11), Lk(p0), om0, Lk(p72), om11], 'lemul12ad', '( %s -> %s <_ ( ( 7 / 2 ) x. %s ) )' % (Ck, W_, F11))
    c0_ = lin.linarith(w, A0, [c1], '0 <_ C', leaves={'C': cr})
    cw = w.s([Lk(cr), lr_('( 5 / 4 )'), wr_, w.s([lr_('( 7 / 2 )'), lr_(F11)], 'remulcld', '( %s -> ( ( 7 / 2 ) x. %s ) e. RR )' % (Ck, F11)), Lk(c0_), w0_, Lk(c54), wle], 'lemul12ad',
             '( %s -> ( C x. %s ) <_ ( ( 5 / 4 ) x. ( ( 7 / 2 ) x. %s ) ) )' % (Ck, W_, F11))
    U80 = '( 3 / ; 8 0 )'
    cw2 = lin.linarith(w, Ck, [cw], '( C x. %s ) <_ ( 1 - %s )' % (W_, U80), closure=clos(w, Ck, {'( C x. %s )' % W_: w.s([Lk(cr), wr_], 'remulcld', '( %s -> ( C x. %s ) e. RR )' % (Ck, W_))}))
    rhs_fold = lambda t_: '( ( H x. ( ( N x. ( %s ^c C ) ) ^c %s ) ) x. %s )' % (t_, W_, LG)
    ld = ap_(w, A0, [xr, b['x2'], st([nn], 'nnred', 'N e. RR'), st([nn], 'nnge1d', '1 <_ N'), nx], 't21ld', '( log ` ( N x. ( %s + 2 ) ) ) <_ ( 5 x. %s )' % (X3, L))
    def mono(Cx, got, rhs_b):
        tr_ = w.s([], 'simplr', '( %s -> t e. RR )' % Cx)
        t2_ = w.s([], 'simprl', '( %s -> 2 <_ t )' % Cx); tX = w.s([], 'simprr', '( %s -> t <_ %s )' % (Cx, X3))
        tp_ = w.s([tr_, lin.linarith(w, Cx, [t2_], '0 < t', leaves={'t': tr_})], 'elrpd', '( %s -> t e. RR+ )' % Cx)
        nrx = L_(st([nn], 'nnred', 'N e. RR'), Cx)
        ntc = w.s([w.s([L_(nn, Cx)], 'nnrpd', '( %s -> N e. RR+ )' % Cx), w.s([tp_, L_(cr, Cx)], 'rpcxpcld', '( %s -> ( t ^c C ) e. RR+ )' % Cx)], 'rpmulcld', '( %s -> ( N x. ( t ^c C ) ) e. RR+ )' % Cx)
        pw = w.s([ntc, L_(wr_, Cx)], 'rpcxpcld', '( %s -> ( ( N x. ( t ^c C ) ) ^c %s ) e. RR+ )' % (Cx, W_))
        HP = '( H x. ( ( N x. ( t ^c C ) ) ^c %s ) )' % W_
        hpr = w.s([L_(hr, Cx), w.s([pw], 'rpred', '( %s -> ( ( N x. ( t ^c C ) ) ^c %s ) e. RR )' % (Cx, W_))], 'remulcld', '( %s -> %s e. RR )' % (Cx, HP))
        hp0 = w.s([L_(hr, Cx), w.s([pw], 'rpred', '( %s -> ( ( N x. ( t ^c C ) ) ^c %s ) e. RR )' % (Cx, W_)), L_(h0, Cx), w.s([pw], 'rpge0d', '( %s -> 0 <_ ( ( N x. ( t ^c C ) ) ^c %s ) )' % (Cx, W_))], 'mulge0d', '( %s -> 0 <_ %s )' % (Cx, HP))
        NT = '( N x. ( t + 2 ) )'; NX = '( N x. ( %s + 2 ) )' % X3
        t2r = w.s([tr_, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Cx)], 'readdcld', '( %s -> ( t + 2 ) e. RR )' % Cx)
        ntr = w.s([nrx, t2r], 'remulcld', '( %s -> %s e. RR )' % (Cx, NT))
        nt1 = lin.nlinarith(w, Cx, [L_(st([nn], 'nnge1d', '1 <_ N'), Cx), t2_], '1 <_ %s' % NT, leaves={'N': nrx, 't': tr_})
        ntp = w.s([ntr, lin.linarith(w, Cx, [nt1], '0 < %s' % NT, leaves={NT: ntr})], 'elrpd', '( %s -> %s e. RR+ )' % (Cx, NT))
        x3r_ = L_(b['x3r'], Cx)
        nxr_ = w.s([nrx, w.s([x3r_, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Cx)], 'readdcld', '( %s -> ( %s + 2 ) e. RR )' % (Cx, X3))], 'remulcld', '( %s -> %s e. RR )' % (Cx, NX))
        nxp = w.s([nxr_, lin.linarith(w, Cx, [nt1, w.s([t2r, w.s([x3r_, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Cx)], 'readdcld', '( %s -> ( %s + 2 ) e. RR )' % (Cx, X3)), nrx, L_(st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N'), Cx),
                  lin.linarith(w, Cx, [tX], '( t + 2 ) <_ ( %s + 2 )' % X3, leaves={'t': tr_, X3: x3r_})], 'lemul2ad', '( %s -> %s <_ %s )' % (Cx, NT, NX))], '0 < %s' % NX, leaves={NT: ntr, NX: nxr_})], 'elrpd', '( %s -> %s e. RR+ )' % (Cx, NX))
        nle = w.s([t2r, w.s([x3r_, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Cx)], 'readdcld', '( %s -> ( %s + 2 ) e. RR )' % (Cx, X3)), nrx, L_(st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N'), Cx),
                   lin.linarith(w, Cx, [tX], '( t + 2 ) <_ ( %s + 2 )' % X3, leaves={'t': tr_, X3: x3r_})], 'lemul2ad', '( %s -> %s <_ %s )' % (Cx, NT, NX))
        lle = w.s([nle, w.s([ntp, nxp], 'logled', '( %s -> ( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) ) )' % (Cx, NT, NX, NT, NX))], 'mpbid', '( %s -> ( log ` %s ) <_ ( log ` %s ) )' % (Cx, NT, NX))
        l5 = w.s([w.s([ntp], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (Cx, NT)), w.s([nxp], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (Cx, NX)), L_(st([st([num.real(w, '5')], 'a1i', '5 e. RR'), lr], 'remulcld', '( 5 x. %s ) e. RR' % L), Cx), lle, L_(ld, Cx)], 'letrd',
                 '( %s -> ( log ` %s ) <_ ( 5 x. %s ) )' % (Cx, NT, L))
        pk = w.s([w.s([ntp], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (Cx, NT)), L_(st([st([num.real(w, '5')], 'a1i', '5 e. RR'), lr], 'remulcld', '( 5 x. %s ) e. RR' % L), Cx), L_(kn, Cx), w.s([ntr, nt1], 'logge0d', '( %s -> 0 <_ ( log ` %s ) )' % (Cx, NT)), l5], 'leexp1ad',
                 '( %s -> ( ( log ` %s ) ^ K ) <_ %s )' % (Cx, NT, LG))
        lkr = w.s([w.s([ntp], 'relogcld', '( %s -> ( log ` %s ) e. RR )' % (Cx, NT)), L_(kn, Cx)], 'reexpcld', '( %s -> ( ( log ` %s ) ^ K ) e. RR )' % (Cx, NT))
        m = w.s([lkr, L_(lgr, Cx), hpr, hp0, pk], 'lemul2ad', '( %s -> %s <_ %s )' % (Cx, rhs_b, rhs_fold('t')))
        skx = L_(skr, Cx)
        ncx, _ = nc_real(w, Cx, L_(nn, Cx), skx, L_(sk0, Cx), L_(sk1, Cx), tr_, SK, 't')
        rbr = w.s([hpr, lkr], 'remulcld', '( %s -> %s e. RR )' % (Cx, rhs_b))
        rfr = w.s([hpr, L_(lgr, Cx)], 'remulcld', '( %s -> %s e. RR )' % (Cx, rhs_fold('t')))
        return w.s([ncx, rbr, rfr, got, m], 'letrd', '( %s -> %s <_ %s )' % (Cx, NC(SK, 't'), rhs_fold('t')))
    fhyp = fold_hyp(w, Ck, body, Lk(bst), SK, skr, F3950, sk39, sk1, X3, rhs_fold, mono)
    x32 = lin.linarith(w, A0, [b['x8']], '2 <_ %s' % X3, leaves={X3: b['x3r']})
    NW = '( N ^c %s )' % W_
    FR = '( ( ( H x. %s ) x. %s ) x. ( 2 + ( 1 / %s ) ) )' % (NW, LG, U80)
    fo = ap_(w, Ck, [Lk(nn), skr, sk0, sk1, Lk(b['x3r']), Lk(x32), Lk(hr), Lk(h0), Lk(lgr), Lk(lg0), Lk(cr), wr_, w0_,
                     Lk(st([num.rp(w, U80)], 'a1i', '%s e. RR+' % U80)), Lk(st([num.le_lit(w, U80, '1')], 'a1i', '%s <_ 1' % U80)), cw2, fhyp], 't21fold', '%s <_ %s' % (WS(SK, X3), FR))
    rd = w.s([w.s([num.cc(w, '3')], 'a1i', '( %s -> 3 e. CC )' % Ck), w.s([num.cc(w, '; 8 0')], 'a1i', '( %s -> ; 8 0 e. CC )' % Ck), w.s([num.ne0_nat(w, 3)], 'a1i', '( %s -> 3 =/= 0 )' % Ck), w.s([num.ne0_nat(w, 80)], 'a1i', '( %s -> ; 8 0 =/= 0 )' % Ck)], 'recdivd',
             '( %s -> ( 1 / %s ) = ( ; 8 0 / 3 ) )' % (Ck, U80))
    FR2 = '( ( ( H x. %s ) x. %s ) x. ( 2 + ( ; 8 0 / 3 ) ) )' % (NW, LG)
    fe = w.s([w.s([rd], 'oveq2d', '( %s -> ( 2 + ( 1 / %s ) ) = ( 2 + ( ; 8 0 / 3 ) ) )' % (Ck, U80))], 'oveq2d', '( %s -> %s = %s )' % (Ck, FR, FR2))
    N9 = '( N ^c ( %s x. %s ) )' % (F92, OM)
    nr = st([nn], 'nnred', 'N e. RR'); n1 = st([nn], 'nnge1d', '1 <_ N')
    e9r = w.s([lr_(F92), omr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Ck, F92, OM))
    wl9 = w.s([Lk(pr), lr_(F92), omr, om0, lin.linarith(w, Ck, [Lk(p72)], 'P <_ %s' % F92, leaves={'P': Lk(pr)})], 'lemul1ad', '( %s -> %s <_ ( %s x. %s ) )' % (Ck, W_, F92, OM))
    nw9 = w.s([Lk(nr), Lk(n1), wr_, e9r, wl9], 'cxplead', '( %s -> %s <_ %s )' % (Ck, NW, N9))
    n0 = st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')
    nwr = w.s([Lk(nr), Lk(n0), wr_], 'recxpcld', '( %s -> %s e. RR )' % (Ck, NW)); n9r = w.s([Lk(nr), Lk(n0), e9r], 'recxpcld', '( %s -> %s e. RR )' % (Ck, N9))
    a1 = w.s([nwr, n9r, Lk(hr), Lk(h0), nw9], 'lemul2ad', '( %s -> ( H x. %s ) <_ ( H x. %s ) )' % (Ck, NW, N9))
    hwr = w.s([Lk(hr), nwr], 'remulcld', '( %s -> ( H x. %s ) e. RR )' % (Ck, NW)); h9r = w.s([Lk(hr), n9r], 'remulcld', '( %s -> ( H x. %s ) e. RR )' % (Ck, N9))
    a2 = w.s([hwr, h9r, Lk(lgr), Lk(lg0), a1], 'lemul1ad', '( %s -> ( ( H x. %s ) x. %s ) <_ ( ( H x. %s ) x. %s ) )' % (Ck, NW, LG, N9, LG))
    C83 = '( 2 + ( ; 8 0 / 3 ) )'
    c83r = lr_(C83) if num.is_lit(C83) else w.s([lr_('2'), lr_('( ; 8 0 / 3 )')], 'readdcld', '( %s -> %s e. RR )' % (Ck, C83))
    c830 = lin.linarith(w, Ck, [], '0 <_ %s' % C83, leaves={})
    hwl = w.s([hwr, Lk(lgr)], 'remulcld', '( %s -> ( ( H x. %s ) x. %s ) e. RR )' % (Ck, NW, LG)); h9l = w.s([h9r, Lk(lgr)], 'remulcld', '( %s -> ( ( H x. %s ) x. %s ) e. RR )' % (Ck, N9, LG))
    a3 = w.s([hwl, h9l, c83r, c830, a2], 'lemul1ad', '( %s -> %s <_ ( ( ( H x. %s ) x. %s ) x. %s ) )' % (Ck, FR2, N9, LG, C83))
    h9l0 = w.s([h9r, Lk(lgr), w.s([Lk(hr), n9r, Lk(h0), w.s([Lk(nr), Lk(n0), e9r], 'cxpge0d', '( %s -> 0 <_ %s )' % (Ck, N9))], 'mulge0d', '( %s -> 0 <_ ( H x. %s ) )' % (Ck, N9)), Lk(lg0)], 'mulge0d', '( %s -> 0 <_ ( ( H x. %s ) x. %s ) )' % (Ck, N9, LG))
    a4 = w.s([c83r, lr_('; 2 9'), h9l, h9l0, lin.linarith(w, Ck, [], '%s <_ ; 2 9' % C83, leaves={})], 'lemul2ad', '( %s -> ( ( ( H x. %s ) x. %s ) x. %s ) <_ ( ( ( H x. %s ) x. %s ) x. ; 2 9 ) )' % (Ck, N9, LG, C83, N9, LG))
    ce = clos(w, Ck, {'H': Lk(hr), N9: n9r, LG: Lk(lgr)})
    a5 = lin.lineq(w, Ck, '( ( ( H x. %s ) x. %s ) x. ; 2 9 )' % (N9, LG), '( %s x. %s )' % (Q, N9), closure=ce, products=True)
    t1_ = w.s([fo, fe], 'breqtrd', '( %s -> %s <_ %s )' % (Ck, WS(SK, X3), FR2))
    fr2r = w.s([hwl, c83r], 'remulcld', '( %s -> %s e. RR )' % (Ck, FR2))
    mid = '( ( ( H x. %s ) x. %s ) x. %s )' % (N9, LG, C83)
    midr = w.s([h9l, c83r], 'remulcld', '( %s -> %s e. RR )' % (Ck, mid))
    endr = w.s([h9l, lr_('; 2 9')], 'remulcld', '( %s -> ( ( ( H x. %s ) x. %s ) x. ; 2 9 ) e. RR )' % (Ck, N9, LG))
    b1 = w.s([fr2r, midr, endr, a3, a4], 'letrd', '( %s -> %s <_ ( ( ( H x. %s ) x. %s ) x. ; 2 9 ) )' % (Ck, FR2, N9, LG))
    b2 = w.s([b1, a5], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (Ck, FR2, Q, N9))
    wsR = ws_real(w, Ck, Lk(nn), skr, sk0, sk1, Lk(b['x3r']), SK, X3)
    h2 = w.s([wsR, fr2r, w.s([Lk(qr), n9r], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Ck, Q, N9)), t1_, b2], 'letrd', '( %s -> %s <_ ( %s x. %s ) )' % (Ck, WS(SK, X3), Q, N9))
    ET = '( X ^c ( -u %s x. ( 1 - %s ) ) )' % (F9200, SSTAR)
    gzc = w.s([gz1, h2], 't21gz', '( %s -> %s <_ ( %s x. ( ( ; 6 4 x. Y ) x. %s ) ) )' % (A0, ZS(X3, 'Y', F3950, SSTAR), Q, ET))
    # ET = L ^c ( -u ( 9 / 4 ) x. ( K + 2 ) )
    xp = b['xp']
    OS = '( 1 - %s )' % SSTAR
    osr = st([one, ssr], 'resubcld', '%s e. RR' % OS)
    e9 = st([num.real(w, '-u %s' % F9200)], 'a1i', '-u %s e. RR' % F9200)
    Z_ = '( -u %s x. %s )' % (F9200, OS)
    cxe = st([st([xp], 'rpcnd', 'X e. CC'), st([xp], 'rpne0d', 'X =/= 0'), st([st([e9, osr], 'remulcld', '%s e. RR' % Z_)], 'recnd', '%s e. CC' % Z_)], 'cxpefd', '%s = ( exp ` ( %s x. %s ) )' % (ET, Z_, L))
    osq = lin.lineq(w, A0, OS, FRc, closure=clos(w, A0, {FRc: frr}))
    ma = st([st([e9], 'recnd', '-u %s e. CC' % F9200), st([osr], 'recnd', '%s e. CC' % OS), st([lr], 'recnd', '%s e. CC' % L)], 'mulassd', '( %s x. %s ) = ( -u %s x. ( %s x. %s ) )' % (Z_, L, F9200, OS, L))
    dc = st([st([numr], 'recnd', '%s e. CC' % NUM), st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L)], 'divcan1d', '( %s x. %s ) = %s' % (FRc, L, NUM))
    ol = st([st([osq], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (OS, L, FRc, L)), dc], 'eqtrd', '( %s x. %s ) = %s' % (OS, L, NUM))
    zl = st([ma, st([ol], 'oveq2d', '( -u %s x. ( %s x. %s ) ) = ( -u %s x. %s )' % (F9200, OS, L, F9200, NUM))], 'eqtrd', '( %s x. %s ) = ( -u %s x. %s )' % (Z_, L, F9200, NUM))
    W94 = '( -u ( 9 / 4 ) x. %s )' % K2
    LW = '( %s ^c %s )' % (L, W94)
    w94r = st([st([num.real(w, '-u ( 9 / 4 )')], 'a1i', '-u ( 9 / 4 ) e. RR'), k2r], 'remulcld', '%s e. RR' % W94)
    lwe = st([st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L), st([w94r], 'recnd', '%s e. CC' % W94)], 'cxpefd', '%s = ( exp ` ( %s x. %s ) )' % (LW, W94, LL))
    mb = st([st([num.cc(w, '-u ( 9 / 4 )')], 'a1i', '-u ( 9 / 4 ) e. CC'), st([k2r], 'recnd', '%s e. CC' % K2), st([llr], 'recnd', '%s e. CC' % LL)], 'mulassd', '( %s x. %s ) = ( -u ( 9 / 4 ) x. %s )' % (W94, LL, ZK))
    lq = lin.lineq(w, A0, '( -u %s x. %s )' % (F9200, NUM), '( -u ( 9 / 4 ) x. %s )' % ZK, closure=clos(w, A0, {ZK: zkr}))
    args = st([st([zl, lq], 'eqtrd', '( %s x. %s ) = ( -u ( 9 / 4 ) x. %s )' % (Z_, L, ZK)), mb], 'eqtr4d', '( %s x. %s ) = ( %s x. %s )' % (Z_, L, W94, LL))
    etw = st([st([cxe, st([args], 'fveq2d', '( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. %s ) )' % (Z_, L, W94, LL))], 'eqtrd', '%s = ( exp ` ( %s x. %s ) )' % (ET, W94, LL)), lwe], 'eqtr4d', '%s = %s' % (ET, LW))
    # LG = 5 ^ K x. L ^c K
    LK = '( %s ^c K )' % L; FK = '( 5 ^ K )'
    me = st([st([num.cc(w, '5')], 'a1i', '5 e. CC'), st([lr], 'recnd', '%s e. CC' % L), kn], 'mulexpd', '%s = ( %s x. ( %s ^ K ) )' % (LG, FK, L))
    ce_ = ap_(w, A0, [st([lr], 'recnd', '%s e. CC' % L), kn], 'cxpexp', '%s = ( %s ^ K )' % (LK, L))
    lge = st([me, st([ce_], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s ^ K ) )' % (FK, LK, FK, L))], 'eqtr4d', '%s = ( %s x. %s )' % (LG, FK, LK))
    # LK x. LW <_ L ^c -u ( 9 / 2 )
    LN = '( %s ^c -u %s )' % (L, F92); LP = '( %s ^c %s )' % (L, F92)
    kw = '( K + %s )' % W94
    ca = st([st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L), st([knr], 'recnd', 'K e. CC'), st([w94r], 'recnd', '%s e. CC' % W94)], 'cxpaddd', '( %s ^c %s ) = ( %s x. %s )' % (L, kw, LK, LW))
    kwr = st([knr, w94r], 'readdcld', '%s e. RR' % kw)
    kwl = lin.linarith(w, A0, [k0], '%s <_ -u %s' % (kw, F92), leaves={'K': knr})
    cl_ = st([lr, b['l1'], kwr, st([num.real(w, '-u %s' % F92)], 'a1i', '-u %s e. RR' % F92), kwl], 'cxplead', '( %s ^c %s ) <_ %s' % (L, kw, LN))
    mm = st([ca, cl_], 'eqbrtrrd', '( %s x. %s ) <_ %s' % (LK, LW, LN))
    # algebra
    FKr = st([st([num.real(w, '5')], 'a1i', '5 e. RR'), kn], 'reexpcld', '%s e. RR' % FK)
    FK0 = st([st([num.real(w, '5')], 'a1i', '5 e. RR'), kn, st([num.le_lit(w, '0', '5')], 'a1i', '0 <_ 5')], 'expge0d', '0 <_ %s' % FK)
    lkr = st([lp, knr], 'rpcxpcld', '%s e. RR+' % LK); lwr = st([lp, w94r], 'rpcxpcld', '%s e. RR+' % LW)
    Q2 = '( %s x. ( %s x. %s ) )' % (H29, FK, LK)
    t0 = st([gzc, st([st([st([etw], 'oveq2d', '( ( ; 6 4 x. Y ) x. %s ) = ( ( ; 6 4 x. Y ) x. %s )' % (ET, LW))], 'oveq2d', '( %s x. ( ( ; 6 4 x. Y ) x. %s ) ) = ( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (Q, ET, Q, LW)),
                              st([st([lge], 'oveq2d', '%s = %s' % (Q, Q2))], 'oveq1d', '( %s x. ( ( ; 6 4 x. Y ) x. %s ) ) = ( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (Q, LW, Q2, LW))], 'eqtrd',
                          '( %s x. ( ( ; 6 4 x. Y ) x. %s ) ) = ( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (Q, ET, Q2, LW))], 'breqtrd', '%s <_ ( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (ZS(X3, 'Y', F3950, SSTAR), Q2, LW))
    V1 = '( ; ; ; 1 8 5 6 x. ( H x. ( %s x. Y ) ) )' % FK
    ca_ = clos(w, A0, {'H': hr, FK: FKr, 'Y': yr, LK: st([lkr], 'rpred', '%s e. RR' % LK), LW: st([lwr], 'rpred', '%s e. RR' % LW)})
    ide = lin.lineq(w, A0, '( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (Q2, LW), '( %s x. ( %s x. %s ) )' % (V1, LK, LW), closure=ca_, products=True)
    # Y >= 1
    X7p = '( X ^c %s )' % F709
    x70 = st([xr, b['x1'], st([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), st([num.real(w, F709)], 'a1i', '%s e. RR' % F709), st([num.le_lit(w, '0', F709)], 'a1i', '0 <_ %s' % F709)], 'cxplead', '( X ^c 0 ) <_ %s' % X7p)
    x71 = st([st([st([xr], 'recnd', 'X e. CC')], 'cxp0d', '( X ^c 0 ) = 1'), x70], 'eqbrtrrd', '1 <_ %s' % X7p)
    x7r = st([st([xp, st([num.real(w, F709)], 'a1i', '%s e. RR' % F709)], 'rpcxpcld', '%s e. RR+' % X7p)], 'rpred', '%s e. RR' % X7p)
    m11 = st([one, nr, one, x7r, st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), n1, x71], 'lemul12ad', '( 1 x. 1 ) <_ ( N x. %s )' % X7p)
    y1 = st([one, st([nr, x7r], 'remulcld', '( N x. %s ) e. RR' % X7p), yr, st([st([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'), m11], 'eqbrtrrd', '1 <_ ( N x. %s )' % X7p), ny], 'letrd', '1 <_ Y')
    y0 = lin.linarith(w, A0, [y1], '0 <_ Y', leaves={'Y': yr})
    v1r = st([st([num.real(w, '; ; ; 1 8 5 6')], 'a1i', '; ; ; 1 8 5 6 e. RR'), st([hr, st([FKr, yr], 'remulcld', '( %s x. Y ) e. RR' % FK)], 'remulcld', '( H x. ( %s x. Y ) ) e. RR' % FK)], 'remulcld', '%s e. RR' % V1)
    v10 = st([st([num.real(w, '; ; ; 1 8 5 6')], 'a1i', '; ; ; 1 8 5 6 e. RR'), st([hr, st([FKr, yr], 'remulcld', '( %s x. Y ) e. RR' % FK)], 'remulcld', '( H x. ( %s x. Y ) ) e. RR' % FK),
              st([num.le_lit(w, '0', '; ; ; 1 8 5 6')], 'a1i', '0 <_ ; ; ; 1 8 5 6'), st([hr, st([FKr, yr], 'remulcld', '( %s x. Y ) e. RR' % FK), h0, st([FKr, yr, FK0, y0], 'mulge0d', '0 <_ ( %s x. Y )' % FK)], 'mulge0d', '0 <_ ( H x. ( %s x. Y ) )' % FK)], 'mulge0d', '0 <_ %s' % V1)
    lpp = st([lp, st([num.real(w, F92)], 'a1i', '%s e. RR' % F92)], 'rpcxpcld', '%s e. RR+' % LP)
    lnr = st([lp, st([num.real(w, '-u %s' % F92)], 'a1i', '-u %s e. RR' % F92)], 'rpcxpcld', '%s e. RR+' % LN)
    s1_ = st([st([st([lkr], 'rpred', '%s e. RR' % LK), st([lwr], 'rpred', '%s e. RR' % LW)], 'remulcld', '( %s x. %s ) e. RR' % (LK, LW)), st([lnr], 'rpred', '%s e. RR' % LN), v1r, v10, mm], 'lemul2ad', '( %s x. ( %s x. %s ) ) <_ ( %s x. %s )' % (V1, LK, LW, V1, LN))
    ng = st([st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L), st([num.cc(w, F92)], 'a1i', '%s e. CC' % F92)], 'cxpnegd', '%s = ( 1 / %s )' % (LN, LP))
    dv = st([st([v1r], 'recnd', '%s e. CC' % V1), st([lpp], 'rpcnd', '%s e. CC' % LP), st([lpp], 'rpne0d', '%s =/= 0' % LP)], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (V1, LP, V1, LP))
    vln = st([st([ng], 'oveq2d', '( %s x. %s ) = ( %s x. ( 1 / %s ) )' % (V1, LN, V1, LP)), dv], 'eqtr4d', '( %s x. %s ) = ( %s / %s )' % (V1, LN, V1, LP))
    hxy = st([st([st([st([num.real(w, C501)], 'a1i', '%s e. RR' % C501), FKr], 'remulcld', '( %s x. %s ) e. RR' % (C501, FK)), hr], 'remulcld', '( ( %s x. %s ) x. H ) e. RR' % (C501, FK)), st([er, st([lpp], 'rpred', '%s e. RR' % LP)], 'remulcld', '( E x. %s ) e. RR' % LP), yr, y0, hx], 'lemul1ad',
              '( ( ( %s x. %s ) x. H ) x. Y ) <_ ( ( E x. %s ) x. Y )' % (C501, FK, LP))
    EY27 = '( ( E x. Y ) / ; 2 7 )'
    cb = clos(w, A0, {'H': hr, FK: FKr, 'Y': yr, 'E': er, LP: st([lpp], 'rpred', '%s e. RR' % LP)})
    vle = lin.linarith(w, A0, [hxy], '%s <_ ( %s x. %s )' % (V1, LP, EY27), closure=cb, products=True)
    vq = st([vle, st([v1r, st([st([er, yr], 'remulcld', '( E x. Y ) e. RR'), st([num.rp(w, '; 2 7')], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '%s e. RR' % EY27), lpp], 'ledivmuld',
             '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (V1, LP, EY27, V1, LP, EY27))], 'mpbird', '( %s / %s ) <_ %s' % (V1, LP, EY27))
    cf = clos(w, A0, {'( %s x. ( ( ; 6 4 x. Y ) x. %s ) )' % (Q2, LW): st([st([h29r, st([FKr, st([lkr], 'rpred', '%s e. RR' % LK)], 'remulcld', '( %s x. %s ) e. RR' % (FK, LK))], 'remulcld', '%s e. RR' % Q2),
                                                                             st([st([st([num.real(w, '; 6 4')], 'a1i', '; 6 4 e. RR'), yr], 'remulcld', '( ; 6 4 x. Y ) e. RR'), st([lwr], 'rpred', '%s e. RR' % LW)], 'remulcld', '( ( ; 6 4 x. Y ) x. %s ) e. RR' % LW)], 'remulcld', '( %s x. ( ( ; 6 4 x. Y ) x. %s ) ) e. RR' % (Q2, LW)),
                      '( %s x. ( %s x. %s ) )' % (V1, LK, LW): st([v1r, st([st([lkr], 'rpred', '%s e. RR' % LK), st([lwr], 'rpred', '%s e. RR' % LW)], 'remulcld', '( %s x. %s ) e. RR' % (LK, LW))], 'remulcld', '( %s x. ( %s x. %s ) ) e. RR' % (V1, LK, LW)),
                      '( %s x. %s )' % (V1, LN): st([v1r, st([lnr], 'rpred', '%s e. RR' % LN)], 'remulcld', '( %s x. %s ) e. RR' % (V1, LN)),
                      '( %s / %s )' % (V1, LP): st([v1r, lpp], 'rerpdivcld', '( %s / %s ) e. RR' % (V1, LP)),
                      EY27: st([st([er, yr], 'remulcld', '( E x. Y ) e. RR'), st([num.rp(w, '; 2 7')], 'a1i', '; 2 7 e. RR+')], 'rerpdivcld', '%s e. RR' % EY27)})
    ZSt = ZS(X3, 'Y', F3950, SSTAR)
    f390 = st([num.le_lit(w, '0', F3950, strict=True)], 'a1i', '0 < %s' % F3950); f391 = st([num.le_lit(w, F3950, '1')], 'a1i', '%s <_ 1' % F3950)
    cf.leaf(ZSt, 'RR', zs_real(w, A0, nn, f39, f390, f391, b['x3r'], yr, y0, F3950, SSTAR, X3))
    fin = lin.linarith(w, A0, [t0, ide, s1_, vln, vq], '%s <_ %s' % (ZSt, EY27), closure=cf)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21z2']))
    return run(w)


if __name__ == '__main__':
    gen_z2()
