"""Sortie CM: the numeric walk (cmbud).
MM_DB=sorties/cm.mm MM_ENGINE=mmatch python3 tools/gen/cm_g.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cmlib import *
from lin import linarith, nlinarith, lineq

only = sys.argv[1:]


def elt3(w, C):
    """( C -> ( exp ` 1 ) < 3 )"""
    e3 = w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')
    x = w.s([w.s([], 'df-e', '_e = ( exp ` 1 )'), e3], 'eqbrtrri', '( exp ` 1 ) < 3')
    return w.s([x], 'a1i', '( %s -> ( exp ` 1 ) < 3 )' % C)


def gen_bud():
    from mvlib import ringeq, ringeqp
    w = W('cmbud', 'THE NUMERIC WALK: from the family bound at ` E = ( 11 / 10 ) eta0 ` , ` D = eta0 / 3 ` , ` eta0 = ( 1 - S ) + 1 / ( 12 L ) ` , ` L > 500 ` , the count ` R ` satisfies ` 1 + R <_ exp ( 4 . 10 ^ 9 + 4 . 10 ^ 10 ( 1 - S ) L ) ` ( ` M ^ 4 <_ 4 ! e ^ M ` by ~ tppowfac , ` e ^ 2 < 9 ` , ` 1 + A + A ^ 2 / 2 <_ e ^ A ` at ` A = 2 . 10 ^ 5 ` ; Lean ` budget_close ` , constants 118000000 , 1190000000 there, NUMERALS.md).')
    A0, C0 = split_imp(S['cmbud'])
    d = mk(w, A0)
    F = split_all(w, A0, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    g = lambda f: F[f]
    sr = g('S e. RR'); s1 = g('S <_ 1'); lr = g('L e. RR'); l500 = g('; ; 5 0 0 < L'); rr = g('R e. RR'); r0 = g('R e. RR') and g('0 <_ R')
    fam = g(FAMC())
    c0 = Closure(w, A0, {'S': ('RR', sr), 'L': ('RR', lr), 'R': ('RR', rr)})
    lp = linarith(w, A0, [l500], '0 < L', closure=c0); c0.have('L', 'gt0', lp)
    l0 = linarith(w, A0, [l500], '0 <_ L', closure=c0)
    IL = '( 1 / ( ; 1 2 x. L ) )'
    ilr = c0.mem(IL, 'RR'); ilp = c0.gt0(IL)
    c0.atom(IL)
    E = EEX(); D_ = DDX(); ET = ETA0()
    s0 = linarith(w, A0, [s1], '0 <_ ( 1 - S )', closure=c0)
    etp = linarith(w, A0, [s0, ilp], '0 < %s' % ET, closure=c0)
    er = c0.mem(E, 'RR')
    ep = linarith(w, A0, [etp], '0 < %s' % E, closure=c0)
    erp = d('elrpd', [er, ep], '%s e. RR+' % E)
    e0 = linarith(w, A0, [etp], '0 <_ %s' % E, closure=c0)
    c0.atom(E); c0.have(E, 'gt0', ep)
    kn = d('syl', [d('jca', [d('jca', [er, e0], '( %s e. RR /\\ 0 <_ %s )' % (E, E)), d('jca', [lr, l0], '( L e. RR /\\ 0 <_ L )')], '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( L e. RR /\\ 0 <_ L ) )' % (E, E)), w.inst('kdndet')],
           inst('kdndet', {'E': E})[1])
    KN = split_all(w, A0, inst('kdndet', {'E': E})[1], kn)
    N = NDET(E, 'L'); M = MDET(E, 'L')
    nnn = KN['%s e. NN' % N]; n6 = KN['6 <_ %s' % N]
    CN = '; ; ; ; ; ; ; ; 8 4 0 0 0 0 0 0 0'
    nlt = KN['%s < ( 7 + ( ( %s x. %s ) x. L ) )' % (N, CN, E)]
    nr = d('nnred', [nnn], '%s e. RR' % N)
    c0.have(N, 'RR', nr); c0.have(N, 'NN', nnn); c0.atom(N)
    mr = c0.mem(M, 'RR')
    m0 = linarith(w, A0, [n6], '0 <_ %s' % M, closure=c0)
    # the logarithms of the window ends
    Q = '( ( ; 1 6 x. %s ) / %s )' % (M, E)
    Q1 = '( %s / ( ; 1 6 x. %s ) )' % (M, E)
    x1, x2 = XONE(E, 'L'), XTWO(E, 'L')
    qr = c0.mem(Q, 'RR'); q1r = c0.mem(Q1, 'RR')
    lq = d('syl', [qr, w.inst('relogef')], '( log ` %s ) = %s' % (x2, Q))
    lq1 = d('syl', [q1r, w.inst('relogef')], '( log ` %s ) = %s' % (x1, Q1))
    q10 = d('divge0d', [c0.mem(M, 'RR'), c0.mem('( ; 1 6 x. %s )' % E, 'RR+'), m0], '0 <_ %s' % Q1)
    LX2 = '( log ` %s )' % x2; LX1 = '( log ` %s )' % x1
    DL = '( %s - %s )' % (LX2, LX1)
    dlq = d('eqtrd', [d('oveq12d', [lq, lq1], '%s = ( %s - %s )' % (DL, Q, Q1)), a1(w, A0, 'eqid', '( %s - %s ) = ( %s - %s )' % (Q, Q1, Q, Q1))], '%s = ( %s - %s )' % (DL, Q, Q1))
    c0.atom(Q); c0.atom(Q1)
    dlle = linarith(w, A0, [dlq, q10], '%s <_ %s' % (DL, Q), closure=Closure(w, A0, {DL: ('RR', d('eqeltrd', [dlq, c0.mem('( %s - %s )' % (Q, Q1), 'RR')], '%s e. RR' % DL)), Q: ('RR', qr), Q1: ('RR', q1r)}))
    q0 = d('divge0d', [c0.mem('( ; 1 6 x. %s )' % M, 'RR'), erp, linarith(w, A0, [m0], '0 <_ ( ; 1 6 x. %s )' % M, closure=c0)], '0 <_ %s' % Q)
    L2 = '( %s ^ 2 )' % LX2
    l2e = d('oveq1d', [lq], '%s = ( %s ^ 2 )' % (L2, Q))
    CDT = CDX(E, 'L')
    X6 = '( exp ` ( 6 x. %s ) )' % M
    c0.have(X6, 'RR+', d('rpefcld', [c0.mem('( 6 x. %s )' % M, 'RR')], '%s e. RR+' % X6)); c0.atom(X6)
    cr = c0.mem(CDT, 'RR'); cg = c0.ge0(CDT)
    C7 = C750
    c0.have(EE2, 'RR', d('resqcld', [ere(w, A0)], '%s e. RR' % EE2)); c0.have(EE2, 'ge0', d('sqge0d', [ere(w, A0)], '0 <_ %s' % EE2)); c0.atom(EE2)
    KC = '( %s x. %s )' % (C7, CDT)
    kcr = c0.mem(KC, 'RR'); kc0 = c0.ge0(KC)
    # B <_ KC ( Q ^ 2 x. Q )
    b1 = d('lemul2ad', [d('eqeltrd', [dlq, c0.mem('( %s - %s )' % (Q, Q1), 'RR')], '%s e. RR' % DL), qr, d('eqeltrd', [l2e, c0.mem('( %s ^ 2 )' % Q, 'RR')], '%s e. RR' % L2), d('eqbrtrrd' if False else 'breqtrrd', [d('sqge0d', [qr], '0 <_ ( %s ^ 2 )' % Q), l2e], '0 <_ %s' % L2), dlle],
           '( %s x. %s ) <_ ( %s x. %s )' % (L2, DL, L2, Q))
    b2 = d('lemul2ad', [d('remulcld', [d('eqeltrd', [l2e, c0.mem('( %s ^ 2 )' % Q, 'RR')], '%s e. RR' % L2), d('eqeltrd', [dlq, c0.mem('( %s - %s )' % (Q, Q1), 'RR')], '%s e. RR' % DL)], '( %s x. %s ) e. RR' % (L2, DL)),
                        d('remulcld', [d('eqeltrd', [l2e, c0.mem('( %s ^ 2 )' % Q, 'RR')], '%s e. RR' % L2), qr], '( %s x. %s ) e. RR' % (L2, Q)), kcr, kc0, b1],
           '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (KC, L2, DL, KC, L2, Q))
    b3 = d('oveq2d', [d('oveq1d', [l2e], '( %s x. %s ) = ( ( %s ^ 2 ) x. %s )' % (L2, Q, Q, Q))], '( %s x. ( %s x. %s ) ) = ( %s x. ( ( %s ^ 2 ) x. %s ) )' % (KC, L2, Q, KC, Q, Q))
    # KC ( Q ^ 2 Q ) = 3072000 ( e ^ 2 ( M ^ 4 X6 ) )
    qe = d('divcan1d', [c0.mem('( ; 1 6 x. %s )' % M, 'CC'), d('rpcnd', [erp], '%s e. CC' % E), d('rpne0d', [erp], '%s =/= 0' % E)], '( %s x. %s ) = ( ; 1 6 x. %s )' % (Q, E, M))
    ccl = Closure(w, A0, {Q: ('CC', d('recnd', [qr], '%s e. CC' % Q)), E: ('CC', d('rpcnd', [erp], '%s e. CC' % E)), N: ('CC', d('recnd', [nr], '%s e. CC' % N)),
                          X6: ('CC', d('rpcnd', [c0.mem(X6, 'RR+')], '%s e. CC' % X6)), EE2: ('CC', d('recnd', [c0.mem(EE2, 'RR')], '%s e. CC' % EE2))})
    for at_ in (Q, E, N, X6, EE2):
        ccl.atom(at_)
    QE = '( %s x. %s )' % (Q, E)

    Y1 = '( ( %s ^ 4 ) x. %s )' % (M, X6)
    Z1 = '( %s x. %s )' % (EE2, Y1)
    r1 = ringeqp(w, A0, '( %s x. ( ( %s ^ 2 ) x. %s ) )' % (KC, Q, Q), '( ( ; ; 7 5 0 x. ( %s x. ( %s x. %s ) ) ) x. ( %s ^ 3 ) )' % (EE2, M, X6, QE), ccl)
    r2 = d('oveq2d', [d('oveq1d', [qe], '( %s ^ 3 ) = ( ( ; 1 6 x. %s ) ^ 3 )' % (QE, M))], '( ( ; ; 7 5 0 x. ( %s x. ( %s x. %s ) ) ) x. ( %s ^ 3 ) ) = ( ( ; ; 7 5 0 x. ( %s x. ( %s x. %s ) ) ) x. ( ( ; 1 6 x. %s ) ^ 3 ) )' % (EE2, M, X6, QE, EE2, M, X6, M))
    r3 = ringeqp(w, A0, '( ( ; ; 7 5 0 x. ( %s x. ( %s x. %s ) ) ) x. ( ( ; 1 6 x. %s ) ^ 3 ) )' % (EE2, M, X6, M), '( %s x. %s )' % (C3072, Z1), ccl)
    T3 = '( %s x. %s )' % (C3072, Z1)
    k3 = chain(w, A0, ['( %s x. ( %s x. %s ) )' % (KC, L2, Q), '( %s x. ( ( %s ^ 2 ) x. %s ) )' % (KC, Q, Q),
                       '( ( ; ; 7 5 0 x. ( %s x. ( %s x. %s ) ) ) x. ( %s ^ 3 ) )' % (EE2, M, X6, QE), '( ( ; ; 7 5 0 x. ( %s x. ( %s x. %s ) ) ) x. ( ( ; 1 6 x. %s ) ^ 3 ) )' % (EE2, M, X6, M), T3],
               [b3, r1, r2, r3])
    BB = '( %s x. ( %s x. %s ) )' % (KC, L2, DL)
    famle = d('breqtrd', [d('letrd', [c0.mem('( ( ( 2 x. %s ) x. R ) x. L )' % D_, 'RR'), d('remulcld', [kcr, d('remulcld', [d('eqeltrd', [l2e, c0.mem('( %s ^ 2 )' % Q, 'RR')], '%s e. RR' % L2), d('eqeltrd', [dlq, c0.mem('( %s - %s )' % (Q, Q1), 'RR')], '%s e. RR' % DL)], '( %s x. %s ) e. RR' % (L2, DL))], '%s e. RR' % BB),
                                       d('remulcld', [kcr, d('remulcld', [d('eqeltrd', [l2e, c0.mem('( %s ^ 2 )' % Q, 'RR')], '%s e. RR' % L2), qr], '( %s x. %s ) e. RR' % (L2, Q))], '( %s x. ( %s x. %s ) ) e. RR' % (KC, L2, Q)), fam, b2],
                                '( ( ( 2 x. %s ) x. R ) x. L ) <_ ( %s x. ( %s x. %s ) )' % (D_, KC, L2, Q)), k3], '( ( ( 2 x. %s ) x. R ) x. L ) <_ %s' % (D_, T3))
    # 1 / 18 R <_ 2 D R L
    ill = d('syl2anc', [c0.mem('( ; 1 2 x. L )', 'CC'), c0.ne0('( ; 1 2 x. L )'), w.inst('recid2')], '( %s x. ( ; 1 2 x. L ) ) = 1' % IL)
    pl = d('mulge0d', [c0.mem('( 1 - S )', 'RR'), lr, s0, l0], '0 <_ ( ( 1 - S ) x. L )')
    cr2 = Closure(w, A0, {'S': ('RR', sr), 'L': ('RR', lr), 'R': ('RR', rr), IL: ('RR', ilr)})
    cr2.atom(IL)
    dl18 = nlinarith(w, A0, [ill, pl], '( 1 / ; 1 8 ) <_ ( ( 2 x. %s ) x. L )' % D_, closure=cr2)
    r18 = nlinarith(w, A0, [dl18, g('0 <_ R')], '( ( 1 / ; 1 8 ) x. R ) <_ ( ( ( 2 x. %s ) x. R ) x. L )' % D_, closure=cr2)
    # e ^ 2 <_ 9 ; M ^ 4 <_ 24 exp M
    e3 = elt3(w, A0)
    ce = Closure(w, A0, {'( exp ` 1 )': ('RR', ere(w, A0))}); ce.have('( exp ` 1 )', 'gt0', epos(w, A0)); ce.atom('( exp ` 1 )')
    e9 = nlinarith(w, A0, [e3, epos(w, A0)], '%s <_ 9' % EE2, closure=ce)
    tp = d('syl3anc', [mr, m0, a1(w, A0, '4nn0', '4 e. NN0'), w.inst('tppowfac')], '( %s ^ 4 ) <_ ( ( ! ` 4 ) x. ( exp ` %s ) )' % (M, M))
    XM = '( exp ` %s )' % M
    tp2 = d('breqtrd', [tp, d('oveq1d', [a1(w, A0, 'fac4', '( ! ` 4 ) = ; 2 4')], '( ( ! ` 4 ) x. %s ) = ( ; 2 4 x. %s )' % (XM, XM))], '( %s ^ 4 ) <_ ( ; 2 4 x. %s )' % (M, XM))
    x6r = c0.mem(X6, 'RR'); x60 = d('rpge0d', [c0.mem(X6, 'RR+')], '0 <_ %s' % X6)
    m4r = c0.mem('( %s ^ 4 )' % M, 'RR')
    xmr = d('reefcld', [mr], '%s e. RR' % XM)
    y1 = d('lemul1ad', [m4r, d('remulcld', [c0.mem('; 2 4', 'RR'), xmr], '( ; 2 4 x. %s ) e. RR' % XM), x6r, x60, tp2], '%s <_ ( ( ; 2 4 x. %s ) x. %s )' % (Y1, XM, X6))
    y1r = d('remulcld', [m4r, x6r], '%s e. RR' % Y1); y10 = d('mulge0d', [m4r, x6r, d('sqge0d' if False else 'id', [], 'x') if False else linarith(w, A0, [], 'x', closure=c0) if False else c0.ge0('( %s ^ 4 )' % M), x60], '0 <_ %s' % Y1)
    z1 = d('lemul1ad', [c0.mem(EE2, 'RR'), a1(w, A0, '9re', '9 e. RR'), y1r, y10, e9], '( %s x. %s ) <_ ( 9 x. %s )' % (EE2, Y1, Y1))
    W2 = '( %s x. %s )' % (XM, X6)
    w2e = ringeq(w, A0, '( ( ; 2 4 x. %s ) x. %s )' % (XM, X6), '( ; 2 4 x. %s )' % W2, Closure(w, A0, {XM: ('CC', d('recnd', [xmr], '%s e. CC' % XM)), X6: ('CC', d('recnd', [x6r], '%s e. CC' % X6))}))
    cfin = Closure(w, A0, {'R': ('RR', rr)})
    for at_, st_ in ((Z1, d('remulcld', [c0.mem(EE2, 'RR'), y1r], '%s e. RR' % Z1)), (Y1, y1r), (W2, d('remulcld', [xmr, x6r], '%s e. RR' % W2)), ('( ( ( 2 x. %s ) x. R ) x. L )' % D_, c0.mem('( ( ( 2 x. %s ) x. R ) x. L )' % D_, 'RR')),
                     ('( ( ; 2 4 x. %s ) x. %s )' % (XM, X6), d('remulcld', [d('remulcld', [c0.mem('; 2 4', 'RR'), xmr], '( ; 2 4 x. %s ) e. RR' % XM), x6r], '( ( ; 2 4 x. %s ) x. %s ) e. RR' % (XM, X6)))):
        cfin.have(at_, 'RR', st_); cfin.atom(at_)
    rw2 = linarith(w, A0, [famle, r18, z1, y1, w2e], 'R <_ ( ; ; ; ; ; ; ; ; ; ; 1 1 9 4 3 9 3 6 0 0 0 x. %s )' % W2, closure=cfin)
    # 11943936000 <_ exp ( 200000 )
    A2 = '; ; ; ; ; 2 0 0 0 0 0'
    ca = Closure(w, A0, {})
    eg = d('syl', [d('jca', [ca.mem(A2, 'RR'), ca.ge0(A2)], '( %s e. RR /\\ 0 <_ %s )' % (A2, A2)), w.inst('efge1p2')], '( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) <_ ( exp ` %s )' % (A2, A2, A2))
    XA = '( exp ` %s )' % A2
    ca.have(XA, 'RR', d('reefcld', [ca.mem(A2, 'RR')], '%s e. RR' % XA)); ca.atom(XA)
    cbig = linarith(w, A0, [eg], '; ; ; ; ; ; ; ; ; ; 1 1 9 4 3 9 3 6 0 0 0 <_ %s' % XA, closure=ca)
    rw3 = d('letrd', [rr, d('remulcld', [ca.mem('; ; ; ; ; ; ; ; ; ; 1 1 9 4 3 9 3 6 0 0 0', 'RR'), cfin.mem(W2, 'RR')], '( ; ; ; ; ; ; ; ; ; ; 1 1 9 4 3 9 3 6 0 0 0 x. %s ) e. RR' % W2),
                      d('remulcld', [ca.mem(XA, 'RR'), cfin.mem(W2, 'RR')], '( %s x. %s ) e. RR' % (XA, W2)), rw2,
                      d('lemul1ad', [ca.mem('; ; ; ; ; ; ; ; ; ; 1 1 9 4 3 9 3 6 0 0 0', 'RR'), ca.mem(XA, 'RR'), cfin.mem(W2, 'RR'), d('mulge0d', [xmr, x6r, d('rpge0d', [d('rpefcld', [mr], '%s e. RR+' % XM)], '0 <_ %s' % XM), x60], '0 <_ %s' % W2), cbig],
                        '( ; ; ; ; ; ; ; ; ; ; 1 1 9 4 3 9 3 6 0 0 0 x. %s ) <_ ( %s x. %s )' % (W2, XA, W2))], 'R <_ ( %s x. %s )' % (XA, W2))
    XS = '( %s + ( %s + ( 6 x. %s ) ) )' % (A2, M, M)
    ex = chain(w, A0, ['( %s x. %s )' % (XA, W2), '( %s x. ( exp ` ( %s + ( 6 x. %s ) ) ) )' % (XA, M, M), '( exp ` %s )' % XS],
               [d('oveq2d', [d('eqcomd', [d('efaddd' if False else 'syl2anc', [c0.mem(M, 'CC'), c0.mem('( 6 x. %s )' % M, 'CC'), w.inst('efadd')], '( exp ` ( %s + ( 6 x. %s ) ) ) = %s' % (M, M, W2))], '%s = ( exp ` ( %s + ( 6 x. %s ) ) )' % (W2, M, M))],
                  '( %s x. %s ) = ( %s x. ( exp ` ( %s + ( 6 x. %s ) ) ) )' % (XA, W2, XA, M, M)),
                d('eqcomd', [d('syl2anc', [c0.mem(A2, 'CC'), c0.mem('( %s + ( 6 x. %s ) )' % (M, M), 'CC'), w.inst('efadd')], '( exp ` %s ) = ( %s x. ( exp ` ( %s + ( 6 x. %s ) ) ) )' % (XS, XA, M, M))],
                  '( %s x. ( exp ` ( %s + ( 6 x. %s ) ) ) ) = ( exp ` %s )' % (XA, M, M, XS))])
    rx = d('breqtrd', [rw3, ex], 'R <_ ( exp ` %s )' % XS)
    # 1 + exp X <_ exp ( X + 1 )
    xsr = c0.mem(XS, 'RR'); xs0 = linarith(w, A0, [m0], '0 <_ %s' % XS, closure=c0)
    EX = '( exp ` %s )' % XS
    ex1 = d('mpbid', [xs0, d('syl2anc', [a1(w, A0, '0re', '0 e. RR'), xsr, w.inst('efle')], '( 0 <_ %s <-> ( exp ` 0 ) <_ %s )' % (XS, EX))], '( exp ` 0 ) <_ %s' % EX)
    ex1b = d('eqbrtrrd' if False else 'breqtrrd' if False else 'eqbrtrrd', [a1(w, A0, 'ef0', '( exp ` 0 ) = 1'), ex1], '1 <_ %s' % EX)
    XS1 = '( %s + 1 )' % XS
    ea = d('syl2anc', [c0.mem(XS, 'CC'), a1(w, A0, 'ax-1cn', '1 e. CC'), w.inst('efadd')], '( exp ` %s ) = ( %s x. ( exp ` 1 ) )' % (XS1, EX))
    e2 = d('ltled', [a1(w, A0, '2re', '2 e. RR'), ere(w, A0), w.s([w.s([w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpli', '2 < _e'), w.s([], 'df-e', '_e = ( exp ` 1 )')], 'breqtri', '2 < ( exp ` 1 )')], 'a1i', '( %s -> 2 < ( exp ` 1 ) )' % A0)], '2 <_ ( exp ` 1 )')
    ce2 = Closure(w, A0, {EX: ('RR', d('reefcld', [xsr], '%s e. RR' % EX)), '( exp ` 1 )': ('RR', ere(w, A0)), '( exp ` %s )' % XS1: ('RR', d('reefcld', [c0.mem(XS1, 'RR')], '( exp ` %s ) e. RR' % XS1))})
    for at_ in (EX, '( exp ` 1 )', '( exp ` %s )' % XS1):
        ce2.atom(at_)
    one = nlinarith(w, A0, [ex1b, e2, ea], '( 1 + %s ) <_ ( exp ` %s )' % (EX, XS1), closure=ce2)
    # the exponent
    ELq = ringeq(w, A0, '( %s x. L )' % E, '( ( ; 1 1 / ; 1 0 ) x. ( ( ( 1 - S ) x. L ) + ( %s x. L ) ) )' % IL, Closure(w, A0, {'S': ('CC', c0.mem('S', 'CC')), 'L': ('CC', c0.mem('L', 'CC')), IL: ('CC', d('recnd', [ilr], '%s e. CC' % IL))}))
    ce3 = Closure(w, A0, {'S': ('RR', sr), 'L': ('RR', lr), IL: ('RR', ilr), N: ('RR', nr), E: ('RR', er)})
    for at_ in (IL, N, E):
        ce3.atom(at_)
    MX = MEXPL()
    ARG = '( %s + ( ( %s x. ( 1 - S ) ) x. L ) )' % (AMACH, BMACH)
    xe = nlinarith(w, A0, [nlt, ELq, ill, pl], '%s <_ %s' % (XS1, ARG), closure=ce3)
    efx = d('mpbid', [xe, d('syl2anc', [c0.mem(XS1, 'RR'), c0.mem(ARG, 'RR'), w.inst('efle')], '( %s <_ %s <-> ( exp ` %s ) <_ %s )' % (XS1, ARG, XS1, MX))], '( exp ` %s ) <_ %s' % (XS1, MX))
    ce4 = Closure(w, A0, {'R': ('RR', rr), EX: ('RR', d('reefcld', [xsr], '%s e. RR' % EX)), '( exp ` %s )' % XS1: ('RR', d('reefcld', [c0.mem(XS1, 'RR')], '( exp ` %s ) e. RR' % XS1)), MX: ('RR', d('reefcld', [c0.mem(ARG, 'RR')], '%s e. RR' % MX))})
    for at_ in (EX, '( exp ` %s )' % XS1, MX):
        ce4.atom(at_)
    fin = linarith(w, A0, [rx, one, efx], C0, closure=ce4)
    w.qed([fin], 'idi', S['cmbud'])
    return run(w, only)


if __name__ == '__main__':
    gen_bud()
