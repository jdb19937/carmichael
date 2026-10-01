# continuation of zl3wbd (exec'd from zl3b_d5.py at module level)
from zl3b_d4 import lt_sub as _lt_sub
hz_ = cst(w, ph, 'halfnz', '-. ( 1 / 2 ) e. ZZ')
hc_ = cst(w, ph, 'halfcn', '( 1 / 2 ) e. CC')
# a is not an integer, nor is -a
Bq = '( %s /\\ %s e. ZZ )' % (ph, a)
hzz = D(w, Bq, 'eqeltrrd', [w.s([w.s([nc], 'adantr', '( %s -> N e. CC )' % Bq), cst(w, Bq, 'halfcn', '( 1 / 2 ) e. CC'), w.inst('pncan2')], 'syl2anc', '( %s -> ( %s - N ) = ( 1 / 2 ) )' % (Bq, a)),
                            w.s([w.s([], 'simpr', '( %s -> %s e. ZZ )' % (Bq, a)), w.s([nz], 'adantr', '( %s -> N e. ZZ )' % Bq), w.inst('zsubcl')], 'syl2anc', '( %s -> ( %s - N ) e. ZZ )' % (Bq, a))], '( 1 / 2 ) e. ZZ')
anz = D(w, ph, 'mtod', [hz_, w.s([hzz], 'ex', '( %s -> ( %s e. ZZ -> ( 1 / 2 ) e. ZZ ) )' % (ph, a))], '-. %s e. ZZ' % a)
nanz = D(w, ph, 'mtbid', [anz, w.s([ac_, w.inst('znegclb')], 'syl', '( %s -> ( %s e. ZZ <-> %s e. ZZ ) )' % (ph, a, na))], '-. %s e. ZZ' % na)
frd = w.s([w.s([D(w, ph, 'jca', [nar, ar], '( %s e. RR /\\ %s e. RR )' % (na, a)), D(w, ph, 'jca', [nanz, anz], '( -. %s e. ZZ /\\ -. %s e. ZZ )' % (na, a)), nale], '3jca',
               '( %s -> ( ( %s e. RR /\\ %s e. RR ) /\\ ( -. %s e. ZZ /\\ -. %s e. ZZ ) /\\ %s <_ %s ) )' % (ph, na, a, na, a, na, a)), w.inst('zl3frd')], 'syl', '( %s -> %s C_ %s )' % (ph, FRC('-u 1', na, '1', a), D0))
Pa, Pb, Pc, Pd = CP('-u 1', na), CP('1', na), CP('1', a), CP('-u 1', a)
EDG = [(Pa, Pb), (Pb, Pc), (Pc, Pd), (Pd, Pa)]
FRx = FRC('-u 1', na, '1', a)
pcs = {Pa: cpcl(w, ph, '-u 1', na, m1, nar), Pb: cpcl(w, ph, '1', na, one, nar), Pc: cpcl(w, ph, '1', a, one, ar), Pd: cpcl(w, ph, '-u 1', a, m1, ar)}
def edge_cl(i):
    P, Q = EDG[i]
    seg = '( %s cseg %s )' % (P, Q)
    e0, e1, e2, e3 = ['( %s cseg %s )' % pq for pq in EDG]
    L_ = '( %s u. %s )' % (e0, e1); R2 = '( %s u. %s )' % (e2, e3)
    if i < 2:
        x = w.s([w.s([], 'ssun1' if i == 0 else 'ssun2', '%s C_ %s' % (seg, L_)), w.s([], 'ssun1', '%s C_ %s' % (L_, FRx))], 'sstri', '%s C_ %s' % (seg, FRx))
    else:
        x = w.s([w.s([], 'ssun1' if i == 2 else 'ssun2', '%s C_ %s' % (seg, R2)), w.s([], 'ssun2', '%s C_ %s' % (R2, FRx))], 'sstri', '%s C_ %s' % (seg, FRx))
    sd = D(w, ph, 'sstrd', [w.s([x], 'a1i', '( %s -> %s C_ %s )' % (ph, seg, FRx)), frd], '%s C_ %s' % (seg, D0))
    return w.s([D(w, ph, 'jca', [D(w, ph, 'jca', [pcs[P], pcs[Q]], '( %s e. CC /\\ %s e. CC )' % (P, Q)), D(w, ph, 'jca', [fkcn, sd], '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (FK, D0, seg, D0))],
                    '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (P, Q, FK, D0, seg, D0)), w.inst('lintcl')], 'syl', '( %s -> %s e. CC )' % (ph, LI(FK, P, Q)))
botc, rgtc, topc, lftc = [edge_cl(i) for i in range(4)]
lft2c = D(w, ph, 'eqeltrrd', [lrn, lftc], '%s e. CC' % LFT2)
# ---- the four bounds
P4 = '( 2 ^c -u ( %s / 4 ) )' % a
p4r = D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [D(w, ph, 'rerpdivcld', [ar, cst(w, ph, '4rp', '4 e. RR+')], '( %s / 4 ) e. RR' % a)], '-u ( %s / 4 ) e. RR' % a)], '%s e. RR+' % P4)], '%s e. RR' % P4)
Q2 = '( 2 ^c -u %s )' % a
q2r = D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [ar], '-u %s e. RR' % a)], '%s e. RR+' % Q2)], '%s e. RR' % Q2)
q2p4 = pow4(w, ph, a, ar, a1)
a0 = D(w, ph, 'rpge0d', [arp], '0 <_ %s' % a)
absa = D(w, ph, 'absidd', [ar, a0], '( abs ` %s ) = %s' % (a, a))
absna = D(w, ph, 'eqtrd', [D(w, ph, 'absnegd', [ac_], '( abs ` %s ) = ( abs ` %s )' % (na, a)), absa], '( abs ` %s ) = %s' % (na, a))
two_ = cst(w, ph, '2re', '2 e. RR'); two_c = cst(w, ph, '2cn', '2 e. CC'); c1 = cst(w, ph, 'ax-1cn', '1 e. CC')
ab2 = D(w, ph, 'absidd', [two_, D(w, ph, 'ltled', [cst(w, ph, '0re', '0 e. RR'), two_, cst(w, ph, '2pos', '0 < 2')], '0 <_ 2')], '( abs ` 2 ) = 2')
d1 = D(w, ph, 'eqtrd', [w.s([c1, c1, w.inst('subneg')], 'syl2anc', '( %s -> ( 1 - -u 1 ) = ( 1 + 1 ) )' % ph), cst(w, ph, '1p1e2', '( 1 + 1 ) = 2')], '( 1 - -u 1 ) = 2')
d2 = D(w, ph, 'eqtrd', [D(w, ph, 'eqcomd', [w.s([c1, c1, w.inst('negdi2')], 'syl2anc', '( %s -> -u ( 1 + 1 ) = ( -u 1 - 1 ) )' % ph)], '( -u 1 - 1 ) = -u ( 1 + 1 )'),
                        D(w, ph, 'negeqd', [cst(w, ph, '1p1e2', '( 1 + 1 ) = 2')], '-u ( 1 + 1 ) = -u 2')], '( -u 1 - 1 ) = -u 2')
ad1 = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [d1], '( abs ` ( 1 - -u 1 ) ) = ( abs ` 2 )'), ab2], '( abs ` ( 1 - -u 1 ) ) = 2')
ad2 = D(w, ph, 'eqtrd', [D(w, ph, 'fveq2d', [d2], '( abs ` ( -u 1 - 1 ) ) = ( abs ` -u 2 )'), D(w, ph, 'eqtrd', [D(w, ph, 'absnegd', [two_c], '( abs ` -u 2 ) = ( abs ` 2 )'), ab2], '( abs ` -u 2 ) = 2')], '( abs ` ( -u 1 - 1 ) ) = 2')
abs1_ = D(w, ph, 'eqbrtrd', [cst(w, ph, 'abs1', '( abs ` 1 ) = 1'), D(w, ph, 'leidd', [one], '1 <_ 1')], '( abs ` 1 ) <_ 1')
absm1_ = D(w, ph, 'eqbrtrd', [D(w, ph, 'eqtrd', [D(w, ph, 'absnegd', [c1], '( abs ` -u 1 ) = ( abs ` 1 )'), cst(w, ph, 'abs1', '( abs ` 1 ) = 1')], '( abs ` -u 1 ) = 1'), D(w, ph, 'leidd', [one], '1 <_ 1')], '( abs ` -u 1 ) <_ 1')
# U - 1/2 integers
nah = D(w, ph, 'eqtrd', [D(w, ph, 'eqcomd', [w.s([ac_, hc_, w.inst('negdi2')], 'syl2anc', '( %s -> -u ( %s + ( 1 / 2 ) ) = ( %s - ( 1 / 2 ) ) )' % (ph, a, na))], '( %s - ( 1 / 2 ) ) = -u ( %s + ( 1 / 2 ) )' % (na, a)),
                         D(w, ph, 'negeqd', [D(w, ph, 'eqtrd', [D(w, ph, 'addassd', [nc, hc_, hc_], '( %s + ( 1 / 2 ) ) = ( N + ( ( 1 / 2 ) + ( 1 / 2 ) ) )' % a),
                                                                D(w, ph, 'oveq2d', [w.s([c1, w.inst('2halves')], 'syl', '( %s -> ( ( 1 / 2 ) + ( 1 / 2 ) ) = 1 )' % ph)], '( N + ( ( 1 / 2 ) + ( 1 / 2 ) ) ) = ( N + 1 )')],
                                                  '( %s + ( 1 / 2 ) ) = ( N + 1 )' % a)], '-u ( %s + ( 1 / 2 ) ) = -u ( N + 1 )' % a)], '( %s - ( 1 / 2 ) ) = -u ( N + 1 )' % na)
nahz = D(w, ph, 'eqeltrd', [nah, D(w, ph, 'znegcld', [D(w, ph, 'peano2zd', [nz], '( N + 1 ) e. ZZ')], '-u ( N + 1 ) e. ZZ')], '( %s - ( 1 / 2 ) ) e. ZZ' % na)
ahz = D(w, ph, 'eqeltrd', [w.s([nc, hc_, w.inst('pncan')], 'syl2anc', '( %s -> ( %s - ( 1 / 2 ) ) = N )' % (ph, a)), nz], '( %s - ( 1 / 2 ) ) e. ZZ' % a)
def hbd(X, Y, U, xr, yr, ur, xa, ya, uz, P, Q):
    h = D(w, ph, 'jca', [w.s([xr, yr, ur], '3jca', '( %s -> ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) )' % (ph, X, Y, U)),
                         D(w, ph, 'jca', [D(w, ph, 'jca', [xa, ya], '( ( abs ` %s ) <_ 1 /\\ ( abs ` %s ) <_ 1 )' % (X, Y)), uz], '( ( ( abs ` %s ) <_ 1 /\\ ( abs ` %s ) <_ 1 ) /\\ ( %s - ( 1 / 2 ) ) e. ZZ )' % (X, Y, U))],
          '( ( %s e. RR /\\ %s e. RR /\\ %s e. RR ) /\\ ( ( ( abs ` %s ) <_ 1 /\\ ( abs ` %s ) <_ 1 ) /\\ ( %s - ( 1 / 2 ) ) e. ZZ ) )' % (X, Y, U, X, Y, U))
    return w.s([hc_ if False else w.s([], 'simpl', '( %s -> %s )' % (ph, HCTX)), h, w.inst('zl3hbd')], 'syl2anc',
               '( %s -> ( abs ` %s ) <_ ( ( K x. ( 2 ^c -u ( abs ` %s ) ) ) x. ( abs ` ( %s - %s ) ) ) )' % (ph, LI(FK, P, Q), U, Y, X))
bb0 = hbd('-u 1', '1', na, m1, one, nar, absm1_, abs1_, nahz, Pa, Pb)
tb0 = hbd('1', '-u 1', a, one, m1, ar, abs1_, absm1_, ahz, Pc, Pd)
TK = '( 2 x. K )'
tkr = D(w, ph, 'remulcld', [two_, kr], '%s e. RR' % TK)
tk0 = D(w, ph, 'mulge0d', [two_, kr, D(w, ph, 'ltled', [cst(w, ph, '0re', '0 e. RR'), two_, cst(w, ph, '2pos', '0 < 2')], '0 <_ 2'), D(w, ph, 'rpge0d', [krp], '0 <_ K')], '0 <_ %s' % TK)
def side_bound(b0, U, absU, adv, L_):
    e1 = D(w, ph, 'oveq12d', [D(w, ph, 'oveq2d', [D(w, ph, 'oveq2d', [D(w, ph, 'negeqd', [absU], '-u ( abs ` %s ) = -u %s' % (U, a))], '( 2 ^c -u ( abs ` %s ) ) = %s' % (U, Q2))],
                                        '( K x. ( 2 ^c -u ( abs ` %s ) ) ) = ( K x. %s )' % (U, Q2)), adv], '( ( K x. ( 2 ^c -u ( abs ` %s ) ) ) x. ( abs ` %s ) ) = ( ( K x. %s ) x. 2 )' % (U, L_, Q2))
    e2 = D(w, ph, 'eqtrd', [D(w, ph, 'mul32d', [kc, D(w, ph, 'recnd', [q2r], '%s e. CC' % Q2), two_c], '( ( K x. %s ) x. 2 ) = ( ( K x. 2 ) x. %s )' % (Q2, Q2)),
                            D(w, ph, 'oveq1d', [D(w, ph, 'mulcomd', [kc, two_c], '( K x. 2 ) = %s' % TK)], '( ( K x. 2 ) x. %s ) = ( %s x. %s )' % (Q2, TK, Q2))], '( ( K x. %s ) x. 2 ) = ( %s x. %s )' % (Q2, TK, Q2))
    b1 = D(w, ph, 'breqtrd', [b0, D(w, ph, 'eqtrd', [e1, e2], '( ( K x. ( 2 ^c -u ( abs ` %s ) ) ) x. ( abs ` %s ) ) = ( %s x. %s )' % (U, L_, TK, Q2))], '( abs ` %s ) <_ ( %s x. %s )' % (b0 and None or 'X', TK, Q2)) if False else None
    return e1, e2
e1b, e2b = side_bound(bb0, na, absna, ad1, '( 1 - -u 1 )')
e1t, e2t = side_bound(tb0, a, absa, ad2, '( -u 1 - 1 )')
tq = D(w, ph, 'lemul2ad', [q2r, p4r, tkr, tk0, q2p4], '( %s x. %s ) <_ ( %s x. %s )' % (TK, Q2, TK, P4))
BOTb = D(w, ph, 'letrd', [D(w, ph, 'abscld', [botc], '( abs ` %s ) e. RR' % BOT), D(w, ph, 'remulcld', [tkr, q2r], '( %s x. %s ) e. RR' % (TK, Q2)), D(w, ph, 'remulcld', [tkr, p4r], '( %s x. %s ) e. RR' % (TK, P4)),
                          D(w, ph, 'breqtrd', [bb0, D(w, ph, 'eqtrd', [e1b, e2b], '( ( K x. ( 2 ^c -u ( abs ` %s ) ) ) x. ( abs ` ( 1 - -u 1 ) ) ) = ( %s x. %s )' % (na, TK, Q2))], '( abs ` %s ) <_ ( %s x. %s )' % (BOT, TK, Q2)), tq],
      '( abs ` %s ) <_ ( %s x. %s )' % (BOT, TK, P4))
TOPb = D(w, ph, 'letrd', [D(w, ph, 'abscld', [topc], '( abs ` %s ) e. RR' % TOP), D(w, ph, 'remulcld', [tkr, q2r], '( %s x. %s ) e. RR' % (TK, Q2)), D(w, ph, 'remulcld', [tkr, p4r], '( %s x. %s ) e. RR' % (TK, P4)),
                          D(w, ph, 'breqtrd', [tb0, D(w, ph, 'eqtrd', [e1t, e2t], '( ( K x. ( 2 ^c -u ( abs ` %s ) ) ) x. ( abs ` ( -u 1 - 1 ) ) ) = ( %s x. %s )' % (a, TK, Q2))], '( abs ` %s ) <_ ( %s x. %s )' % (TOP, TK, Q2)), tq],
      '( abs ` %s ) <_ ( %s x. %s )' % (TOP, TK, P4))
# the long sides at s := a
def long_bound(ed, Pf, Cv, SS, KK, AC):
    body = lambda s_: '( 1 <_ %s -> ( abs ` ( %s - %s ) ) <_ %s )' % (s_, LT(Pf, Cv, s_), SS, EB(s_, KK, AC))
    E = 's = %s' % a
    e = w.s([], 'id', '( %s -> %s )' % (E, E))
    lts = _lt_sub(w, E, e, Pf, Cv, 's', a)
    ebs = D(w, E, 'oveq2d', [D(w, E, 'oveq1d', [D(w, E, 'oveq2d', [D(w, E, 'negeqd', [D(w, E, 'oveq1d', [e], '( s / 4 ) = ( %s / 4 )' % a)], '-u ( s / 4 ) = -u ( %s / 4 )' % a)],
                                                                   '( 2 ^c -u ( s / 4 ) ) = %s' % P4)], '( ( 2 ^c -u ( s / 4 ) ) x. ( ( exp ` %s ) / ( 1 - ( exp ` %s ) ) ) ) = ( %s x. ( ( exp ` %s ) / ( 1 - ( exp ` %s ) ) ) )' % (AC, AC, P4, AC, AC))],
            '%s = %s' % (EB('s', KK, AC), EB(a, KK, AC)))
    bs = D(w, E, 'imbi12d', [D(w, E, 'breq2d', [e], '( 1 <_ s <-> 1 <_ %s )' % a), D(w, E, 'breq12d', [D(w, E, 'fveq2d', [D(w, E, 'oveq1d', [lts], '( %s - %s ) = ( %s - %s )' % (LT(Pf, Cv, 's'), SS, LT(Pf, Cv, a), SS))],
                                                                                                           '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (LT(Pf, Cv, 's'), SS, LT(Pf, Cv, a), SS)), ebs],
                                                                                         '( ( abs ` ( %s - %s ) ) <_ %s <-> ( abs ` ( %s - %s ) ) <_ %s )' % (LT(Pf, Cv, 's'), SS, EB('s', KK, AC), LT(Pf, Cv, a), SS, EB(a, KK, AC)))],
            '( %s <-> %s )' % (body('s'), body(a)))
    al = w.s([ed, w.inst('simpr')], 'syl', '( %s -> A. s e. RR+ %s )' % (ph, body('s')))
    sp = w.s([arp, al, w.s([bs], 'rspcv', '( %s e. RR+ -> ( A. s e. RR+ %s -> %s ) )' % (a, body('s'), body(a)))], 'sylc', '( %s -> %s )' % (ph, body(a)))
    b1 = D(w, ph, 'mpd', [a1, sp], '( abs ` ( %s - %s ) ) <_ %s' % (LT(Pf, Cv, a), SS, EB(a, KK, AC)))
    X = '( ( 8 x. %s ) / ( log ` 2 ) )' % KK; RHO = '( ( exp ` %s ) / ( 1 - ( exp ` %s ) ) )' % (AC, AC)
    l2rp = w.s([two_, cst(w, ph, '1lt2', '1 < 2'), w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` 2 ) e. RR+ )' % ph)
    kkr = kr if KK == 'K' else D(w, ph, 'remulcld', [kr, etp], '%s e. RR' % KK)
    xr = D(w, ph, 'rerpdivcld', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), kkr], '( 8 x. %s ) e. RR' % KK), l2rp], '%s e. RR' % X)
    acr_ = D(w, ph, 'remulcld', [ntpr if Cv == '1' else tpr, one if Cv == '1' else m1], '%s e. RR' % AC)
    rr_ = w.s([acr_, w.inst('reefcl')], 'syl', '( %s -> ( exp ` %s ) e. RR )' % (ph, AC))
    r1_ = D(w, ph, 'breqtrd', [D(w, ph, 'mpbid', [acR if Cv == '1' else acL, w.s([acr_, cst(w, ph, '0re', '0 e. RR'), w.inst('eflt')], 'syl2anc', '( %s -> ( %s < 0 <-> ( exp ` %s ) < ( exp ` 0 ) ) )' % (ph, AC, AC))],
                                   '( exp ` %s ) < ( exp ` 0 )' % AC), cst(w, ph, 'ef0', '( exp ` 0 ) = 1')], '( exp ` %s ) < 1' % AC)
    omr = D(w, ph, 'resubcld', [one, rr_], '( 1 - ( exp ` %s ) ) e. RR' % AC)
    omp = D(w, ph, 'mpbid', [r1_, D(w, ph, 'posdifd', [rr_, one], '( ( exp ` %s ) < 1 <-> 0 < ( 1 - ( exp ` %s ) ) )' % (AC, AC))], '0 < ( 1 - ( exp ` %s ) )' % AC)
    rhor = D(w, ph, 'redivcld', [rr_, omr, D(w, ph, 'gt0ne0d', [omp], '( 1 - ( exp ` %s ) ) =/= 0' % AC)], '%s e. RR' % RHO)
    rho0 = D(w, ph, 'divge0d', [rr_, D(w, ph, 'elrpd', [omr, omp], '( 1 - ( exp ` %s ) ) e. RR+' % AC), D(w, ph, 'ltled', [cst(w, ph, '0re', '0 e. RR'), rr_, w.s([acr_, w.inst('efgt0')], 'syl', '( %s -> 0 < ( exp ` %s ) )' % (ph, AC))], '0 <_ ( exp ` %s )' % AC)],
               '0 <_ %s' % RHO)
    x0 = D(w, ph, 'divge0d', [D(w, ph, 'remulcld', [cst(w, ph, '8re', '8 e. RR'), kkr], '( 8 x. %s ) e. RR' % KK), l2rp,
                              D(w, ph, 'mulge0d', [cst(w, ph, '8re', '8 e. RR'), kkr, D(w, ph, 'ltled', [cst(w, ph, '0re', '0 e. RR'), cst(w, ph, '8re', '8 e. RR'), cst(w, ph, '8pos', '0 < 8')], '0 <_ 8'),
                                                   D(w, ph, 'rpge0d', [krp if KK == 'K' else klrp], '0 <_ %s' % KK)], '0 <_ ( 8 x. %s )' % KK)], '0 <_ %s' % X)
    cX = '( %s x. %s )' % (X, RHO)
    cxr = D(w, ph, 'remulcld', [xr, rhor], '%s e. RR' % cX); cx0 = D(w, ph, 'mulge0d', [xr, rhor, x0, rho0], '0 <_ %s' % cX)
    re = D(w, ph, 'eqtrd', [D(w, ph, 'mul12d', [D(w, ph, 'recnd', [xr], '%s e. CC' % X), D(w, ph, 'recnd', [p4r], '%s e. CC' % P4), D(w, ph, 'recnd', [rhor], '%s e. CC' % RHO)],
                              '%s = ( %s x. %s )' % (EB(a, KK, AC), P4, cX)), D(w, ph, 'mulcomd', [D(w, ph, 'recnd', [p4r], '%s e. CC' % P4), D(w, ph, 'recnd', [cxr], '%s e. CC' % cX)], '( %s x. %s ) = ( %s x. %s )' % (P4, cX, cX, P4))],
           '%s = ( %s x. %s )' % (EB(a, KK, AC), cX, P4))
    return D(w, ph, 'breqtrd', [b1, re], '( abs ` ( %s - %s ) ) <_ ( %s x. %s )' % (LT(Pf, Cv, a), SS, cX, P4)), cX, cxr, cx0
RGTb, cR, cRr, cR0 = long_bound(edR, FK, '1', SRR, 'K', '( %s x. 1 )' % TPN)
LFTb, cL, cLr, cL0 = long_bound(edL, FKL, '-u 1', SLL, KL_, '( ( 2 x. _pi ) x. -u 1 )')
assert LT(FK, '1', a) == RGT
# ---- triangle inequality
IS = '( _i x. %s )' % SUMH('-u N', 'N')
tr1 = D(w, ph, 'eqtrd', [D(w, ph, 'eqcomd', [rs], '%s = %s' % (IS, RI(FK, *RN('N')))), rv], '%s = ( ( %s + %s ) + ( %s + %s ) )' % (IS, BOT, RGT, TOP, LFT))
tr2 = D(w, ph, 'eqtrd', [tr1, D(w, ph, 'oveq2d', [D(w, ph, 'oveq2d', [lrn], '( %s + %s ) = ( %s + %s )' % (TOP, LFT, TOP, LFT2))], '( ( %s + %s ) + ( %s + %s ) ) = ( ( %s + %s ) + ( %s + %s ) )' % (BOT, RGT, TOP, LFT, BOT, RGT, TOP, LFT2))],
        '%s = ( ( %s + %s ) + ( %s + %s ) )' % (IS, BOT, RGT, TOP, LFT2))
BR = '( %s + %s )' % (BOT, RGT); TL = '( %s + %s )' % (TOP, LFT2)
brc = D(w, ph, 'addcld', [botc, rgtc], '%s e. CC' % BR); tlc = D(w, ph, 'addcld', [topc, lft2c], '%s e. CC' % TL)
x1 = D(w, ph, 'oveq1d', [tr2], '( %s - ( %s + %s ) ) = ( ( %s + %s ) - ( %s + %s ) )' % (IS, SRR, SLL, BR, TL, SRR, SLL))
x2 = D(w, ph, 'addsub4d', [brc, tlc, src, slc], '( ( %s + %s ) - ( %s + %s ) ) = ( ( %s - %s ) + ( %s - %s ) )' % (BR, TL, SRR, SLL, BR, SRR, TL, SLL))
x3 = D(w, ph, 'oveq12d', [D(w, ph, 'addsubassd', [botc, rgtc, src], '( %s - %s ) = ( %s + ( %s - %s ) )' % (BR, SRR, BOT, RGT, SRR)),
                          D(w, ph, 'addsubassd', [topc, lft2c, slc], '( %s - %s ) = ( %s + ( %s - %s ) )' % (TL, SLL, TOP, LFT2, SLL))],
      '( ( %s - %s ) + ( %s - %s ) ) = ( ( %s + ( %s - %s ) ) + ( %s + ( %s - %s ) ) )' % (BR, SRR, TL, SLL, BOT, RGT, SRR, TOP, LFT2, SLL))
U1 = '( %s + ( %s - %s ) )' % (BOT, RGT, SRR); U2 = '( %s + ( %s - %s ) )' % (TOP, LFT2, SLL)
diff = chain_eq(w, ph, '( %s - ( %s + %s ) )' % (IS, SRR, SLL), [(x1, '( ( %s + %s ) - ( %s + %s ) )' % (BR, TL, SRR, SLL)), (x2, '( ( %s - %s ) + ( %s - %s ) )' % (BR, SRR, TL, SLL)), (x3, '( %s + %s )' % (U1, U2))])
rsc = D(w, ph, 'subcld', [rgtc, src], '( %s - %s ) e. CC' % (RGT, SRR)); lsc = D(w, ph, 'subcld', [lft2c, slc], '( %s - %s ) e. CC' % (LFT2, SLL))
u1c = D(w, ph, 'addcld', [botc, rsc], '%s e. CC' % U1); u2c = D(w, ph, 'addcld', [topc, lsc], '%s e. CC' % U2)
ab_ = lambda c, t: D(w, ph, 'abscld', [c], '( abs ` %s ) e. RR' % t)
t1 = D(w, ph, 'abstrid', [u1c, u2c], '( abs ` ( %s + %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (U1, U2, U1, U2))
t2 = D(w, ph, 'abstrid', [botc, rsc], '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (U1, BOT, RGT, SRR))
t3 = D(w, ph, 'abstrid', [topc, lsc], '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (U2, TOP, LFT2, SLL))
S1 = '( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (BOT, RGT, SRR); S2 = '( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (TOP, LFT2, SLL)
s1r = D(w, ph, 'readdcld', [ab_(botc, BOT), ab_(rsc, '( %s - %s )' % (RGT, SRR))], '%s e. RR' % S1); s2r = D(w, ph, 'readdcld', [ab_(topc, TOP), ab_(lsc, '( %s - %s )' % (LFT2, SLL))], '%s e. RR' % S2)
t4 = D(w, ph, 'le2addd', [ab_(u1c, U1), s1r, ab_(u2c, U2), s2r, t2, t3], '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s + %s )' % (U1, U2, S1, S2))
V1 = '( ( %s x. %s ) + ( %s x. %s ) )' % (TK, P4, cR, P4); V2 = '( ( %s x. %s ) + ( %s x. %s ) )' % (TK, P4, cL, P4)
tkp4 = D(w, ph, 'remulcld', [tkr, p4r], '( %s x. %s ) e. RR' % (TK, P4))
v1r = D(w, ph, 'readdcld', [tkp4, D(w, ph, 'remulcld', [cRr, p4r], '( %s x. %s ) e. RR' % (cR, P4))], '%s e. RR' % V1)
v2r = D(w, ph, 'readdcld', [tkp4, D(w, ph, 'remulcld', [cLr, p4r], '( %s x. %s ) e. RR' % (cL, P4))], '%s e. RR' % V2)
t5 = D(w, ph, 'le2addd', [s1r, v1r, s2r, v2r,
                          D(w, ph, 'le2addd', [ab_(botc, BOT), tkp4, ab_(rsc, '( %s - %s )' % (RGT, SRR)), D(w, ph, 'remulcld', [cRr, p4r], '( %s x. %s ) e. RR' % (cR, P4)), BOTb, RGTb], '%s <_ %s' % (S1, V1)),
                          D(w, ph, 'le2addd', [ab_(topc, TOP), tkp4, ab_(lsc, '( %s - %s )' % (LFT2, SLL)), D(w, ph, 'remulcld', [cLr, p4r], '( %s x. %s ) e. RR' % (cL, P4)), TOPb, LFTb], '%s <_ %s' % (S2, V2))],
      '( %s + %s ) <_ ( %s + %s )' % (S1, S2, V1, V2))
# ( V1 + V2 ) = CT x. P4
tkc = D(w, ph, 'recnd', [tkr], '%s e. CC' % TK); p4c = D(w, ph, 'recnd', [p4r], '%s e. CC' % P4); cRc = D(w, ph, 'recnd', [cRr], '%s e. CC' % cR); cLc = D(w, ph, 'recnd', [cLr], '%s e. CC' % cL)
tkp4c = D(w, ph, 'mulcld', [tkc, p4c], '( %s x. %s ) e. CC' % (TK, P4))
y1 = D(w, ph, 'add4d', [tkp4c, D(w, ph, 'mulcld', [cRc, p4c], '( %s x. %s ) e. CC' % (cR, P4)), tkp4c, D(w, ph, 'mulcld', [cLc, p4c], '( %s x. %s ) e. CC' % (cL, P4))],
       '( %s + %s ) = ( ( ( %s x. %s ) + ( %s x. %s ) ) + ( ( %s x. %s ) + ( %s x. %s ) ) )' % (V1, V2, TK, P4, TK, P4, cR, P4, cL, P4))
y2 = D(w, ph, 'eqcomd', [D(w, ph, 'adddird', [tkc, tkc, p4c], '( ( %s + %s ) x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (TK, TK, P4, TK, P4, TK, P4))], '( ( %s x. %s ) + ( %s x. %s ) ) = ( ( %s + %s ) x. %s )' % (TK, P4, TK, P4, TK, TK, P4))
y3 = D(w, ph, 'eqtrd', [D(w, ph, 'eqcomd', [D(w, ph, 'adddird', [two_c, two_c, kc], '( ( 2 + 2 ) x. K ) = ( %s + %s )' % (TK, TK))], '( %s + %s ) = ( ( 2 + 2 ) x. K )' % (TK, TK)),
                        D(w, ph, 'oveq1d', [cst(w, ph, '2p2e4', '( 2 + 2 ) = 4')], '( ( 2 + 2 ) x. K ) = ( 4 x. K )')], '( %s + %s ) = ( 4 x. K )' % (TK, TK))
y4 = D(w, ph, 'eqtrd', [y2, D(w, ph, 'oveq1d', [y3], '( ( %s + %s ) x. %s ) = ( ( 4 x. K ) x. %s )' % (TK, TK, P4, P4))], '( ( %s x. %s ) + ( %s x. %s ) ) = ( ( 4 x. K ) x. %s )' % (TK, P4, TK, P4, P4))
y5 = D(w, ph, 'eqcomd', [D(w, ph, 'adddird', [cRc, cLc, p4c], '( ( %s + %s ) x. %s ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (cR, cL, P4, cR, P4, cL, P4))], '( ( %s x. %s ) + ( %s x. %s ) ) = ( ( %s + %s ) x. %s )' % (cR, P4, cL, P4, cR, cL, P4))
fkc4 = D(w, ph, 'mulcld', [cst(w, ph, '4cn', '4 e. CC'), kc], '( 4 x. K ) e. CC')
y6 = D(w, ph, 'eqcomd', [D(w, ph, 'adddird', [fkc4, D(w, ph, 'addcld', [cRc, cLc], '( %s + %s ) e. CC' % (cR, cL)), p4c], '( %s x. %s ) = ( ( ( 4 x. K ) x. %s ) + ( ( %s + %s ) x. %s ) )' % (CT, P4, P4, cR, cL, P4))],
       '( ( ( 4 x. K ) x. %s ) + ( ( %s + %s ) x. %s ) ) = ( %s x. %s )' % (P4, cR, cL, P4, CT, P4))
assert CT == '( ( 4 x. K ) + ( %s + %s ) )' % (cR, cL), (CT, cR, cL)
vsum = chain_eq(w, ph, '( %s + %s )' % (V1, V2), [(y1, '( ( ( %s x. %s ) + ( %s x. %s ) ) + ( ( %s x. %s ) + ( %s x. %s ) ) )' % (TK, P4, TK, P4, cR, P4, cL, P4)),
                                                   (D(w, ph, 'oveq12d', [y4, y5], '( ( ( %s x. %s ) + ( %s x. %s ) ) + ( ( %s x. %s ) + ( %s x. %s ) ) ) = ( ( ( 4 x. K ) x. %s ) + ( ( %s + %s ) x. %s ) )' % (TK, P4, TK, P4, cR, P4, cL, P4, P4, cR, cL, P4)),
                                                    '( ( ( 4 x. K ) x. %s ) + ( ( %s + %s ) x. %s ) )' % (P4, cR, cL, P4)), (y6, '( %s x. %s )' % (CT, P4))])
# P4 <_ ( 2 ^c -u ( 1 / 4 ) ) ^ N and CT >_ 0
ctr = D(w, ph, 'readdcld', [D(w, ph, 'remulcld', [cst(w, ph, '4re', '4 e. RR'), kr], '( 4 x. K ) e. RR'), D(w, ph, 'readdcld', [cRr, cLr], '( %s + %s ) e. RR' % (cR, cL))], '%s e. RR' % CT)
ct0 = D(w, ph, 'addge0d', [D(w, ph, 'remulcld', [cst(w, ph, '4re', '4 e. RR'), kr], '( 4 x. K ) e. RR'), D(w, ph, 'readdcld', [cRr, cLr], '( %s + %s ) e. RR' % (cR, cL)),
                           D(w, ph, 'mulge0d', [cst(w, ph, '4re', '4 e. RR'), kr, D(w, ph, 'ltled', [cst(w, ph, '0re', '0 e. RR'), cst(w, ph, '4re', '4 e. RR'), cst(w, ph, '4pos', '0 < 4')], '0 <_ 4'), D(w, ph, 'rpge0d', [krp], '0 <_ K')], '0 <_ ( 4 x. K )'),
                           D(w, ph, 'addge0d', [cRr, cLr, cR0, cL0], '0 <_ ( %s + %s )' % (cR, cL))], '0 <_ %s' % CT)
Q4 = '( ( 2 ^c -u ( 1 / 4 ) ) ^ N )'
n4 = D(w, ph, 'rerpdivcld', [nr, cst(w, ph, '4rp', '4 e. RR+')], '( N / 4 ) e. RR')
a4 = D(w, ph, 'rerpdivcld', [ar, cst(w, ph, '4rp', '4 e. RR+')], '( %s / 4 ) e. RR' % a)
le4 = D(w, ph, 'lediv1dd', [nr, ar, cst(w, ph, '4rp', '4 e. RR+'), D(w, ph, 'ltled', [nr, ar, na_], 'N <_ %s' % a)], '( N / 4 ) <_ ( %s / 4 )' % a)
lng = D(w, ph, 'mpbid', [le4, D(w, ph, 'lenegd', [n4, a4], '( ( N / 4 ) <_ ( %s / 4 ) <-> -u ( %s / 4 ) <_ -u ( N / 4 ) )' % (a, a))], '-u ( %s / 4 ) <_ -u ( N / 4 )' % a)
cpl = D(w, ph, 'mpbid', [lng, w.s([w.s([two_, cst(w, ph, '1lt2', '1 < 2')], 'jca', '( %s -> ( 2 e. RR /\\ 1 < 2 ) )' % ph), D(w, ph, 'jca', [D(w, ph, 'renegcld', [a4], '-u ( %s / 4 ) e. RR' % a), D(w, ph, 'renegcld', [n4], '-u ( N / 4 ) e. RR')],
                                                                                                                    '( -u ( %s / 4 ) e. RR /\\ -u ( N / 4 ) e. RR )' % a), w.inst('cxple')], 'syl2anc',
                                  '( %s -> ( -u ( %s / 4 ) <_ -u ( N / 4 ) <-> %s <_ ( 2 ^c -u ( N / 4 ) ) ) )' % (ph, a, P4))], '%s <_ ( 2 ^c -u ( N / 4 ) )' % P4)
c14 = D(w, ph, 'reccld' if False else 'halfcn' if False else 'x', [], 'x') if False else None
qc4 = cst(w, ph, '4cn', '4 e. CC')
nq = D(w, ph, 'eqtrd', [D(w, ph, 'negeqd', [D(w, ph, 'divrec2d', [nc, qc4, cst(w, ph, '4ne0', '4 =/= 0')], '( N / 4 ) = ( ( 1 / 4 ) x. N )')], '-u ( N / 4 ) = -u ( ( 1 / 4 ) x. N )'),
                        D(w, ph, 'eqcomd', [D(w, ph, 'mulneg1d', [D(w, ph, 'reccld', [qc4, cst(w, ph, '4ne0', '4 =/= 0')], '( 1 / 4 ) e. CC'), nc], '( -u ( 1 / 4 ) x. N ) = -u ( ( 1 / 4 ) x. N )')],
                          '-u ( ( 1 / 4 ) x. N ) = ( -u ( 1 / 4 ) x. N )')], '-u ( N / 4 ) = ( -u ( 1 / 4 ) x. N )')
cm = w.s([two_c, D(w, ph, 'negcld', [D(w, ph, 'reccld', [qc4, cst(w, ph, '4ne0', '4 =/= 0')], '( 1 / 4 ) e. CC')], '-u ( 1 / 4 ) e. CC'), D(w, ph, 'nnnn0d', [nN], 'N e. NN0'), w.inst('cxpmul2')], 'syl3anc',
         '( %s -> ( 2 ^c ( -u ( 1 / 4 ) x. N ) ) = %s )' % (ph, Q4))
pq = D(w, ph, 'breqtrd', [cpl, D(w, ph, 'eqtrd', [D(w, ph, 'oveq2d', [nq], '( 2 ^c -u ( N / 4 ) ) = ( 2 ^c ( -u ( 1 / 4 ) x. N ) )'), cm], '( 2 ^c -u ( N / 4 ) ) = %s' % Q4)], '%s <_ %s' % (P4, Q4))
q4r = D(w, ph, 'reexpcld', [D(w, ph, 'rpred', [D(w, ph, 'rpcxpcld', [cst(w, ph, '2rp', '2 e. RR+'), D(w, ph, 'renegcld', [D(w, ph, 'rerpdivcld', [one, cst(w, ph, '4rp', '4 e. RR+')], '( 1 / 4 ) e. RR')], '-u ( 1 / 4 ) e. RR')],
                                                     '( 2 ^c -u ( 1 / 4 ) ) e. RR+')], '( 2 ^c -u ( 1 / 4 ) ) e. RR'), D(w, ph, 'nnnn0d', [nN], 'N e. NN0')], '%s e. RR' % Q4)
fq = D(w, ph, 'lemul2ad', [p4r, q4r, ctr, ct0, pq], '( %s x. %s ) <_ ( %s x. %s )' % (CT, P4, CT, Q4))
DIFF = '( abs ` ( %s - ( %s + %s ) ) )' % (IS, SRR, SLL)
isc = D(w, ph, 'mulcld', [cst(w, ph, 'ax-icn', '_i e. CC'), w.s([w.s([], 'fzfid', '( %s -> ( -u N ... N ) e. Fin )' % ph),
                                                              D(w, '( %s /\\ n e. ( -u N ... N ) )' % ph, 'ffvelcdmd', [w.s([hf], 'adantr', '( ( %s /\\ n e. ( -u N ... N ) ) -> H : CC --> CC )' % ph),
                                                                                                                         D(w, '( %s /\\ n e. ( -u N ... N ) )' % ph, 'mulcld', [cst(w, '( %s /\\ n e. ( -u N ... N ) )' % ph, 'ax-icn', '_i e. CC'),
                                                                                                                                                                                  D(w, '( %s /\\ n e. ( -u N ... N ) )' % ph, 'zcnd', [w.s([w.s([], 'simpr', '( ( %s /\\ n e. ( -u N ... N ) ) -> n e. ( -u N ... N ) )' % ph), w.inst('elfzelz')], 'syl', '( ( %s /\\ n e. ( -u N ... N ) ) -> n e. ZZ )' % ph)], 'n e. CC')],
                                                                                                                           '( _i x. n ) e. CC')], '( H ` ( _i x. n ) ) e. CC')], 'fsumcl', '( %s -> %s e. CC )' % (ph, SUMH('-u N', 'N')))], '%s e. CC' % IS)
dr_ = D(w, ph, 'abscld', [D(w, ph, 'subcld', [isc, D(w, ph, 'addcld', [src, slc], '( %s + %s ) e. CC' % (SRR, SLL))], '( %s - ( %s + %s ) ) e. CC' % (IS, SRR, SLL))], '%s e. RR' % DIFF)
b_all = D(w, ph, 'eqbrtrd', [D(w, ph, 'fveq2d', [diff], '%s = ( abs ` ( %s + %s ) )' % (DIFF, U1, U2)), t1], '%s <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (DIFF, U1, U2))
b2_ = D(w, ph, 'letrd', [dr_, D(w, ph, 'readdcld', [ab_(u1c, U1), ab_(u2c, U2)], '( ( abs ` %s ) + ( abs ` %s ) ) e. RR' % (U1, U2)), D(w, ph, 'readdcld', [s1r, s2r], '( %s + %s ) e. RR' % (S1, S2)), b_all, t4],
        '%s <_ ( %s + %s )' % (DIFF, S1, S2))
b3_ = D(w, ph, 'letrd', [dr_, D(w, ph, 'readdcld', [s1r, s2r], '( %s + %s ) e. RR' % (S1, S2)), D(w, ph, 'readdcld', [v1r, v2r], '( %s + %s ) e. RR' % (V1, V2)), b2_, t5], '%s <_ ( %s + %s )' % (DIFF, V1, V2))
b4_ = D(w, ph, 'breqtrd', [b3_, vsum], '%s <_ ( %s x. %s )' % (DIFF, CT, P4))
b5_ = D(w, ph, 'letrd', [dr_, D(w, ph, 'remulcld', [ctr, p4r], '( %s x. %s ) e. RR' % (CT, P4)), D(w, ph, 'remulcld', [ctr, q4r], '( %s x. %s ) e. RR' % (CT, Q4)), b4_, fq], '%s <_ ( %s x. %s )' % (DIFF, CT, Q4))
w.qed([D(w, ph, 'jca', [convs, D(w, ph, 'addcld', [src, slc], '( %s + %s ) e. CC' % (SRR, SLL))], '( ( seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> /\\ seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> ) /\\ ( %s + %s ) e. CC )' % (VR, VLL, SRR, SLL)), b5_], 'jca', S['zl3wbd'])
go(w, only)
