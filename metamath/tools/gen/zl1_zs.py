"""ZL1: the zeta continuation on Re Z > 1 and at Z = 1 (zl1ztel, zl1zlim0, zl1zser, zl1z1)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl1lib import *
from zl1lib import mptval_ as mptval
from cl import Closure

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    return w.run()


FZ = '( 1 ... M )'
AI = lambda i: '( ( ( %s - 1 ) + Z ) x. ( %s ^c -u Z ) )' % (i, i)       # the telescoping primitive E' ( i )

# ---------------------------------------------------------------- zl1ztel
if not only or 'zl1ztel' in only:
    w = W('zl1ztel', 'The partial sums of the zeta continuation terms: ` Z + sum_ ( k <_ M ) HT ( k , Z ) = '
          '( Z - 1 ) sum_ ( k <_ M ) k ^ -Z + ( M + Z ) ( M + 1 ) ^ -Z ` ( ~ telfsum2 ).')
    A0 = '( Z e. CC /\\ M e. NN )'
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
    mn = w.s([], 'simpr', '( %s -> M e. NN )' % A0)
    mz = w.s([mn], 'nnzd', '( %s -> M e. ZZ )' % A0)
    m1u = w.s([w.s([mn, w.inst('peano2nn')], 'syl', '( %s -> ( M + 1 ) e. NN )' % A0), w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> ( M + 1 ) e. ( ZZ>= ` 1 ) )' % A0)
    # telfsum2 with k := i, j := k
    Ai = '( %s /\\ i e. ( 1 ... ( M + 1 ) ) )' % A0
    inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... ( M + 1 ) ) )' % Ai), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
    ci = Closure(w, Ai, {'i': ('NN', inn), 'Z': ('CC', w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ai))})
    acl = ci.mem(AI('i'), 'CC')
    def sb(t):
        idx = w.s([], 'id', '( i = %s -> i = %s )' % (t, t))
        st, new = w.congr(AI('i'), {'i': t}, 'i = %s' % t, {'i': idx})
        return st, new
    s1, B = sb('k'); s2, C = sb('( k + 1 )'); s3, D = sb('1'); s4, Ev = sb('( M + 1 )')
    tel = w.s([s1, s2, s3, s4, mz, m1u, acl], 'telfsum2', '( %s -> sum_ k e. %s ( %s - %s ) = ( %s - %s ) )' % (A0, FZ, C, B, Ev, D))
    # the terms: ( C - B ) = HT ( k ) - ( Z - 1 ) k ^ -Z
    Ak = '( %s /\\ k e. %s )' % (A0, FZ)
    kn = w.s([w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, FZ)), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ak)
    ck = Closure(w, Ak, {'k': ('NN', kn), 'Z': ('CC', w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))})
    m = lambda e: ck.mem(e, 'CC')
    p = '( k ^c -u Z )'; q = '( ( k + 1 ) ^c -u Z )'
    t1 = E(w, Ak, 'pncand', [m('k'), m('1')], '( ( k + 1 ) - 1 )', 'k')
    t2 = E(w, Ak, 'oveq1d', [t1], '( ( ( k + 1 ) - 1 ) + Z )', '( k + Z )')
    t3 = E(w, Ak, 'oveq1d', [t2], C, '( ( k + Z ) x. %s )' % q)
    t4 = E(w, Ak, 'addsubassd', [m('k'), m('Z'), m('1')], '( ( k + Z ) - 1 )', '( k + ( Z - 1 ) )')
    t5 = E(w, Ak, 'addsubd', [m('k'), m('Z'), m('1')], '( ( k + Z ) - 1 )', '( ( k - 1 ) + Z )')
    t6 = chain(w, Ak, ['( k + ( Z - 1 ) )', '( ( k + Z ) - 1 )', '( ( k - 1 ) + Z )'], [('r', t4), t5])
    t7 = E(w, Ak, 'adddird', [m('k'), m('( Z - 1 )'), m(p)], '( ( k + ( Z - 1 ) ) x. %s )' % p, '( ( k x. %s ) + ( ( Z - 1 ) x. %s ) )' % (p, p))
    t8 = E(w, Ak, 'oveq1d', [t6], '( ( k + ( Z - 1 ) ) x. %s )' % p, B)
    t9 = chain(w, Ak, ['( ( k x. %s ) + ( ( Z - 1 ) x. %s ) )' % (p, p), '( ( k + ( Z - 1 ) ) x. %s )' % p, B], [('r', t7), t8])
    t10 = E(w, Ak, 'subsub4d', [m('( ( k + Z ) x. %s )' % q), m('( k x. %s )' % p), m('( ( Z - 1 ) x. %s )' % p)],
            '( %s - ( ( Z - 1 ) x. %s ) )' % (HT('k', 'Z'), p), '( ( ( k + Z ) x. %s ) - ( ( k x. %s ) + ( ( Z - 1 ) x. %s ) ) )' % (q, p, p))
    t11 = E(w, Ak, 'oveq2d', [t9], '( ( ( k + Z ) x. %s ) - ( ( k x. %s ) + ( ( Z - 1 ) x. %s ) ) )' % (q, p, p), '( ( ( k + Z ) x. %s ) - %s )' % (q, B))
    t12 = E(w, Ak, 'oveq1d', [t3], '( %s - %s )' % (C, B), '( ( ( k + Z ) x. %s ) - %s )' % (q, B))
    term = chain(w, Ak, ['( %s - ( ( Z - 1 ) x. %s ) )' % (HT('k', 'Z'), p), '( ( ( k + Z ) x. %s ) - ( ( k x. %s ) + ( ( Z - 1 ) x. %s ) ) )' % (q, p, p),
                         '( ( ( k + Z ) x. %s ) - %s )' % (q, B), '( %s - %s )' % (C, B)], [t10, t11, ('r', t12)])
    SS = 'sum_ k e. %s ( %s - ( ( Z - 1 ) x. %s ) )' % (FZ, HT('k', 'Z'), p)
    su = w.s([term], 'sumeq2dv', '( %s -> %s = sum_ k e. %s ( %s - %s ) )' % (A0, SS, FZ, C, B))
    fin = w.s([], 'fzfid', '( %s -> %s e. Fin )' % (A0, FZ))
    fs = w.s([fin, m(HT('k', 'Z')), m('( ( Z - 1 ) x. %s )' % p)], 'fsumsub', '( %s -> %s = ( sum_ k e. %s %s - sum_ k e. %s ( ( Z - 1 ) x. %s ) ) )' % (A0, SS, FZ, HT('k', 'Z'), FZ, p))
    zm1 = w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % A0)
    fm = w.s([fin, zm1, m(p)], 'fsummulc2', '( %s -> ( ( Z - 1 ) x. sum_ k e. %s %s ) = sum_ k e. %s ( ( Z - 1 ) x. %s ) )' % (A0, FZ, p, FZ, p))
    SH = 'sum_ k e. %s %s' % (FZ, HT('k', 'Z')); SP = '( ( Z - 1 ) x. sum_ k e. %s %s )' % (FZ, p)
    fs2 = w.s([fs, w.s([w.s([fm], 'eqcomd', '( %s -> sum_ k e. %s ( ( Z - 1 ) x. %s ) = %s )' % (A0, FZ, p, SP))], 'oveq2d',
                       '( %s -> ( %s - sum_ k e. %s ( ( Z - 1 ) x. %s ) ) = ( %s - %s ) )' % (A0, SH, FZ, p, SH, SP))], 'eqtrd', '( %s -> %s = ( %s - %s ) )' % (A0, SS, SH, SP))
    # E ( M + 1 ) = ( M + Z ) ( M + 1 ) ^ -Z, D = Z
    c0 = Closure(w, A0, {'M': ('NN', mn), 'Z': ('CC', zc)})
    e1 = E(w, A0, 'pncand', [c0.mem('M', 'CC'), c0.mem('1', 'CC')], '( ( M + 1 ) - 1 )', 'M')
    e2 = E(w, A0, 'oveq1d', [E(w, A0, 'oveq1d', [e1], '( ( ( M + 1 ) - 1 ) + Z )', '( M + Z )')], Ev, EZ('M'))
    d1 = E(w, A0, 'oveq1d', [E(w, A0, 'subidd', [c0.mem('1', 'CC')], '( 1 - 1 )', '0')], '( ( 1 - 1 ) + Z )', '( 0 + Z )')
    d2 = E(w, A0, 'addlidd', [zc], '( 0 + Z )', 'Z')
    d3 = w.s([w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('1cxp')], 'syl', '( %s -> ( 1 ^c -u Z ) = 1 )' % A0)
    d4 = E(w, A0, 'oveq12d', [chain(w, A0, ['( ( 1 - 1 ) + Z )', '( 0 + Z )', 'Z'], [d1, d2]), d3], D, '( Z x. 1 )')
    d5 = chain(w, A0, [D, '( Z x. 1 )', 'Z'], [d4, E(w, A0, 'mulridd', [zc], '( Z x. 1 )', 'Z')])
    ed = E(w, A0, 'oveq12d', [e2, d5], '( %s - %s )' % (Ev, D), '( %s - Z )' % EZ('M'))
    main = chain(w, A0, ['( %s - %s )' % (SH, SP), SS, 'sum_ k e. %s ( %s - %s )' % (FZ, C, B), '( %s - %s )' % (Ev, D), '( %s - Z )' % EZ('M')],
                 [('r', fs2), su, tel, ed])
    # ( SH - SP ) = ( EM - Z )  =>  Z + SH = SP + EM
    shc = w.s([fin, m(HT('k', 'Z'))], 'fsumcl', '( %s -> %s e. CC )' % (A0, SH))
    spc = w.s([zm1, w.s([fin, m(p)], 'fsumcl', '( %s -> sum_ k e. %s %s e. CC )' % (A0, FZ, p))], 'mulcld', '( %s -> %s e. CC )' % (A0, SP))
    emc = c0.mem(EZ('M'), 'CC')
    r1 = w.s([main, w.s([shc, spc, w.s([emc, zc], 'subcld', '( %s -> ( %s - Z ) e. CC )' % (A0, EZ('M')))], 'subadd2d',
                        '( %s -> ( ( %s - %s ) = ( %s - Z ) <-> ( ( %s - Z ) + %s ) = %s ) )' % (A0, SH, SP, EZ('M'), EZ('M'), SP, SH))], 'mpbid',
             '( %s -> ( ( %s - Z ) + %s ) = %s )' % (A0, EZ('M'), SP, SH))
    r2 = E(w, A0, 'oveq2d', [r1], '( Z + ( ( %s - Z ) + %s ) )' % (EZ('M'), SP), '( Z + %s )' % SH)
    r3 = E(w, A0, 'pncan3d', [zc, emc], '( Z + ( %s - Z ) )' % EZ('M'), EZ('M'))
    r4 = E(w, A0, 'addassd', [zc, w.s([emc, zc], 'subcld', '( %s -> ( %s - Z ) e. CC )' % (A0, EZ('M'))), spc], '( ( Z + ( %s - Z ) ) + %s )' % (EZ('M'), SP),
           '( Z + ( ( %s - Z ) + %s ) )' % (EZ('M'), SP))
    r5 = E(w, A0, 'oveq1d', [r3], '( ( Z + ( %s - Z ) ) + %s )' % (EZ('M'), SP), '( %s + %s )' % (EZ('M'), SP))
    r6 = E(w, A0, 'addcomd', [emc, spc], '( %s + %s )' % (EZ('M'), SP), '( %s + %s )' % (SP, EZ('M')))
    chain(w, A0, ['( Z + %s )' % SH, '( Z + ( ( %s - Z ) + %s ) )' % (EZ('M'), SP), '( ( Z + ( %s - Z ) ) + %s )' % (EZ('M'), SP), '( %s + %s )' % (EZ('M'), SP),
                  '( %s + %s )' % (SP, EZ('M'))], [('r', r2), ('r', r4), r5, r6], name='qed')
    go(w)

# ---------------------------------------------------------------- zl1zlim0
SG = '( ( Re ` Z ) - 1 )'
FE = '( n e. NN |-> %s )' % EZ('n')
GA = '( n e. NN |-> ( abs ` %s ) )' % EZ('n')
C0 = '( n e. NN |-> ( n ^c -u %s ) )' % SG
CA = '( 1 + ( abs ` Z ) )'
HB = '( n e. NN |-> ( %s x. ( n ^c -u %s ) ) )' % (CA, SG)
if not only or 'zl1zlim0' in only:
    w = W('zl1zlim0', 'The boundary term ` ( n + Z ) ( n + 1 ) ^ -Z ` of the zeta continuation tends to ` 0 ` for '
          '` 1 < Re Z ` ( ~ cxpnegcvg , ~ climsqz2 , ~ climabs0 ).')
    A0 = '( Z e. CC /\\ 1 < ( Re ` Z ) )'
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
    r1z = w.s([], 'simpr', '( %s -> 1 < ( Re ` Z ) )' % A0)
    rz = w.s([zc], 'recld', '( %s -> ( Re ` Z ) e. RR )' % A0)
    sgp = w.s([w.s([w.s([rz, a1(w, A0, '1re', '1 e. RR')], 'resubcld', '( %s -> %s e. RR )' % (A0, SG)),
                    w.s([r1z, w.s([a1(w, A0, '1re', '1 e. RR'), rz, w.inst('posdif')], 'syl2anc', '( %s -> ( 1 < ( Re ` Z ) <-> 0 < %s ) )' % (A0, SG))], 'mpbid', '( %s -> 0 < %s )' % (A0, SG))],
                   'elrpd', '( %s -> %s e. RR+ )' % (A0, SG))], 'idi', '( %s -> %s e. RR+ )' % (A0, SG))
    c0 = w.s([sgp, w.inst('cxpnegcvg')], 'syl', '( %s -> %s ~~> 0 )' % (A0, C0))
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    z1 = a1(w, A0, '1z', '1 e. ZZ')
    car = w.s([a1(w, A0, '1re', '1 e. RR'), w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)], 'readdcld', '( %s -> %s e. RR )' % (A0, CA))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    sgk = w.s([sgp], 'adantr', '( %s -> %s e. RR+ )' % (Ak, SG))
    kc0 = w.s([krp, w.s([w.s([sgk], 'rpred', '( %s -> %s e. RR )' % (Ak, SG))], 'renegcld', '( %s -> -u %s e. RR )' % (Ak, SG))], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, SG))
    v0, _ = mptval(w, Ak, 'n', 'NN', '( n ^c -u %s )' % SG, 'k', kn, mp=C0)
    c0c = w.s([v0, w.s([kc0], 'rpcnd', '( %s -> ( k ^c -u %s ) e. CC )' % (Ak, SG))], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, C0))
    vh, _ = mptval(w, Ak, 'n', 'NN', '( %s x. ( n ^c -u %s ) )' % (CA, SG), 'k', kn, mp=HB)
    vh2 = w.s([vh, w.s([w.s([v0], 'eqcomd', '( %s -> ( k ^c -u %s ) = ( %s ` k ) )' % (Ak, SG, C0))], 'oveq2d',
                       '( %s -> ( %s x. ( k ^c -u %s ) ) = ( %s x. ( %s ` k ) ) )' % (Ak, CA, SG, CA, C0))], 'eqtrd', '( %s -> ( %s ` k ) = ( %s x. ( %s ` k ) ) )' % (Ak, HB, CA, C0))
    hex2 = w.s([w.s([], 'mptex', '%s e. _V' % HB)], 'a1i', '( %s -> %s e. _V )' % (A0, HB))
    hl = w.s([nu, z1, c0, w.s([car], 'recnd', '( %s -> %s e. CC )' % (A0, CA)), hex2, c0c, vh2], 'climmulc2', '( %s -> %s ~~> ( %s x. 0 ) )' % (A0, HB, CA))
    hl2 = w.s([hl, w.s([w.s([car], 'recnd', '( %s -> %s e. CC )' % (A0, CA))], 'mul01d', '( %s -> ( %s x. 0 ) = 0 )' % (A0, CA))], 'breqtrd', '( %s -> %s ~~> 0 )' % (A0, HB))
    # the bound | EZ ( k ) | <_ ( 1 + | Z | ) k ^ -( Re Z - 1 )
    zk = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)
    ck = Closure(w, Ak, {'k': ('NN', kn), 'Z': ('CC', zk)})
    m = lambda e: ck.mem(e, 'CC')
    KZ = '( k + Z )'; Q = '( ( k + 1 ) ^c -u Z )'
    a_1 = E(w, Ak, 'absmuld', [m(KZ), m(Q)], '( abs ` %s )' % EZ('k'), '( ( abs ` %s ) x. ( abs ` %s ) )' % (KZ, Q))
    kr = w.s([krp], 'rpred', '( %s -> k e. RR )' % Ak)
    az = w.s([zk], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % Ak)
    az0 = w.s([zk], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % Ak)
    tri = w.s([m('k'), zk, w.inst('abstri')], 'syl2anc', '( %s -> ( abs ` %s ) <_ ( ( abs ` k ) + ( abs ` Z ) ) )' % (Ak, KZ))
    akk = w.s([kr, w.s([krp], 'rpge0d', '( %s -> 0 <_ k )' % Ak)], 'absidd', '( %s -> ( abs ` k ) = k )' % Ak)
    tri2 = w.s([tri, w.s([akk], 'oveq1d', '( %s -> ( ( abs ` k ) + ( abs ` Z ) ) = ( k + ( abs ` Z ) ) )' % Ak)], 'breqtrd', '( %s -> ( abs ` %s ) <_ ( k + ( abs ` Z ) ) )' % (Ak, KZ))
    k1 = w.s([kn], 'nnge1d', '( %s -> 1 <_ k )' % Ak)
    zkk = w.s([w.s([w.s([az, kr], 'jca', '( %s -> ( ( abs ` Z ) e. RR /\\ k e. RR ) )' % Ak), w.s([az0, k1], 'jca', '( %s -> ( 0 <_ ( abs ` Z ) /\\ 1 <_ k ) )' % Ak)], 'jca',
                   '( %s -> ( ( ( abs ` Z ) e. RR /\\ k e. RR ) /\\ ( 0 <_ ( abs ` Z ) /\\ 1 <_ k ) ) )' % Ak), w.inst('lemulge11')], 'syl', '( %s -> ( abs ` Z ) <_ ( ( abs ` Z ) x. k ) )' % Ak)
    kz2 = w.s([az, w.s([az, kr], 'remulcld', '( %s -> ( ( abs ` Z ) x. k ) e. RR )' % Ak), kr, zkk], 'leadd2dd', '( %s -> ( k + ( abs ` Z ) ) <_ ( k + ( ( abs ` Z ) x. k ) ) )' % Ak)
    dd = chain(w, Ak, ['( %s x. k )' % CA, '( ( 1 x. k ) + ( ( abs ` Z ) x. k ) )', '( k + ( ( abs ` Z ) x. k ) )'],
               [E(w, Ak, 'adddird', [m('1'), w.s([az], 'recnd', '( %s -> ( abs ` Z ) e. CC )' % Ak), m('k')], '( %s x. k )' % CA, '( ( 1 x. k ) + ( ( abs ` Z ) x. k ) )'),
                E(w, Ak, 'oveq1d', [E(w, Ak, 'mullidd', [m('k')], '( 1 x. k )', 'k')], '( ( 1 x. k ) + ( ( abs ` Z ) x. k ) )', '( k + ( ( abs ` Z ) x. k ) )')])
    kz3 = w.s([kz2, dd], 'breqtrrd', '( %s -> ( k + ( abs ` Z ) ) <_ ( %s x. k ) )' % (Ak, CA))
    kzr = w.s([w.s([m(KZ)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, KZ)), w.s([kr, az], 'readdcld', '( %s -> ( k + ( abs ` Z ) ) e. RR )' % Ak),
               w.s([w.s([car], 'adantr', '( %s -> %s e. RR )' % (Ak, CA)), kr], 'remulcld', '( %s -> ( %s x. k ) e. RR )' % (Ak, CA)), tri2, kz3], 'letrd',
              '( %s -> ( abs ` %s ) <_ ( %s x. k ) )' % (Ak, KZ, CA))
    RZ_ = '( Re ` Z )'
    k1rp = w.s([w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( k + 1 ) e. NN )' % Ak)], 'nnrpd', '( %s -> ( k + 1 ) e. RR+ )' % Ak)
    aq = w.s([k1rp, w.s([zk], 'negcld', '( %s -> -u Z e. CC )' % Ak), w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( ( k + 1 ) ^c ( Re ` -u Z ) ) )' % (Ak, Q))
    aq2 = w.s([aq, w.s([w.s([zk, w.inst('reneg')], 'syl', '( %s -> ( Re ` -u Z ) = -u %s )' % (Ak, RZ_))], 'oveq2d', '( %s -> ( ( k + 1 ) ^c ( Re ` -u Z ) ) = ( ( k + 1 ) ^c -u %s ) )' % (Ak, RZ_))],
              'eqtrd', '( %s -> ( abs ` %s ) = ( ( k + 1 ) ^c -u %s ) )' % (Ak, Q, RZ_))
    rzk = w.s([rz], 'adantr', '( %s -> %s e. RR )' % (Ak, RZ_))
    rz0 = w.s([a1(w, Ak, '0re', '0 e. RR'), a1(w, Ak, '1re', '1 e. RR'), rzk, a1(w, Ak, '0lt1', '0 < 1'), w.s([r1z], 'adantr', '( %s -> 1 < %s )' % (Ak, RZ_))], 'lttrd',
              '( %s -> 0 < %s )' % (Ak, RZ_))
    kk1 = w.s([kr, w.s([k1rp], 'rpred', '( %s -> ( k + 1 ) e. RR )' % Ak), w.s([kr], 'ltp1d', '( %s -> k < ( k + 1 ) )' % Ak)], 'ltled', '( %s -> k <_ ( k + 1 ) )' % Ak)
    anti = w.s([w.s([krp, k1rp, rzk], '3jca', '( %s -> ( k e. RR+ /\\ ( k + 1 ) e. RR+ /\\ %s e. RR ) )' % (Ak, RZ_)),
                w.s([w.s([a1(w, Ak, '0re', '0 e. RR'), rzk, rz0], 'ltled', '( %s -> 0 <_ %s )' % (Ak, RZ_)), kk1], 'jca', '( %s -> ( 0 <_ %s /\\ k <_ ( k + 1 ) ) )' % (Ak, RZ_)),
                w.inst('cxpnegle')], 'syl2anc', '( %s -> ( ( k + 1 ) ^c -u %s ) <_ ( k ^c -u %s ) )' % (Ak, RZ_, RZ_))
    aql = w.s([aq2, anti], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( k ^c -u %s ) )' % (Ak, Q, RZ_))
    kre = w.s([w.s([krp, w.s([rzk], 'renegcld', '( %s -> -u %s e. RR )' % (Ak, RZ_))], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, RZ_))], 'rpred',
              '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ_))
    prd = w.s([w.s([m(KZ)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, KZ)), w.s([w.s([car], 'adantr', '( %s -> %s e. RR )' % (Ak, CA)), kr], 'remulcld', '( %s -> ( %s x. k ) e. RR )' % (Ak, CA)),
               w.s([m(Q)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, Q)), kre, w.s([m(KZ)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Ak, KZ)),
               w.s([m(Q)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Ak, Q)), kzr, aql], 'lemul12ad',
              '( %s -> ( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( %s x. k ) x. ( k ^c -u %s ) ) )' % (Ak, KZ, Q, CA, RZ_))
    # ( CA k ) k ^ -Re Z = CA k ^ -( Re Z - 1 )
    kcx = w.s([kre], 'recnd', '( %s -> ( k ^c -u %s ) e. CC )' % (Ak, RZ_))
    x1 = E(w, Ak, 'mulassd', [w.s([w.s([car], 'adantr', '( %s -> %s e. RR )' % (Ak, CA))], 'recnd', '( %s -> %s e. CC )' % (Ak, CA)), m('k'), kcx],
           '( ( %s x. k ) x. ( k ^c -u %s ) )' % (CA, RZ_), '( %s x. ( k x. ( k ^c -u %s ) ) )' % (CA, RZ_))
    rzc = w.s([rzk], 'recnd', '( %s -> %s e. CC )' % (Ak, RZ_))
    x2 = E(w, Ak, 'negsubdi2d', [rzc, m('1')], '-u %s' % SG, '( 1 - %s )' % RZ_)
    x3 = E(w, Ak, 'negsubd', [m('1'), rzc], '( 1 + -u %s )' % RZ_, '( 1 - %s )' % RZ_)
    x4 = E(w, Ak, 'addcomd', [w.s([rzc], 'negcld', '( %s -> -u %s e. CC )' % (Ak, RZ_)), m('1')], '( -u %s + 1 )' % RZ_, '( 1 + -u %s )' % RZ_)
    xe = chain(w, Ak, ['-u %s' % SG, '( 1 - %s )' % RZ_, '( 1 + -u %s )' % RZ_, '( -u %s + 1 )' % RZ_], [x2, ('r', x3), ('r', x4)])
    x5 = E(w, Ak, 'oveq2d', [xe], '( k ^c -u %s )' % SG, '( k ^c ( -u %s + 1 ) )' % RZ_)
    x6 = w.s([m('k'), w.s([krp], 'rpne0d', '( %s -> k =/= 0 )' % Ak), w.s([rzc], 'negcld', '( %s -> -u %s e. CC )' % (Ak, RZ_)), w.inst('cxpp1')], 'syl3anc',
             '( %s -> ( k ^c ( -u %s + 1 ) ) = ( ( k ^c -u %s ) x. k ) )' % (Ak, RZ_, RZ_))
    x7 = E(w, Ak, 'mulcomd', [kcx, m('k')], '( ( k ^c -u %s ) x. k )' % RZ_, '( k x. ( k ^c -u %s ) )' % RZ_)
    xk = chain(w, Ak, ['( k x. ( k ^c -u %s ) )' % RZ_, '( ( k ^c -u %s ) x. k )' % RZ_, '( k ^c ( -u %s + 1 ) )' % RZ_, '( k ^c -u %s )' % SG],
               [('r', x7), ('r', x6), ('r', x5)])
    x8 = E(w, Ak, 'oveq2d', [xk], '( %s x. ( k x. ( k ^c -u %s ) ) )' % (CA, RZ_), '( %s x. ( k ^c -u %s ) )' % (CA, SG))
    xx = chain(w, Ak, ['( ( %s x. k ) x. ( k ^c -u %s ) )' % (CA, RZ_), '( %s x. ( k x. ( k ^c -u %s ) ) )' % (CA, RZ_), '( %s x. ( k ^c -u %s ) )' % (CA, SG), '( %s ` k )' % HB],
               [x1, x8, ('r', vh)])
    vg, _ = mptval(w, Ak, 'n', 'NN', '( abs ` %s )' % EZ('n'), 'k', kn, mp=GA)
    gle = chain(w, Ak, ['( %s ` k )' % GA, '( abs ` %s )' % EZ('k'), '( ( abs ` %s ) x. ( abs ` %s ) )' % (KZ, Q)], [vg, a_1])
    g1 = w.s([w.s([gle, prd], 'eqbrtrd', '( %s -> ( %s ` k ) <_ ( ( %s x. k ) x. ( k ^c -u %s ) ) )' % (Ak, GA, CA, RZ_)), xx], 'breqtrd',
             '( %s -> ( %s ` k ) <_ ( %s ` k ) )' % (Ak, GA, HB))
    gr = w.s([vg, w.s([m(EZ('k'))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, EZ('k')))], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, GA))
    hr = w.s([vh, w.s([w.s([car], 'adantr', '( %s -> %s e. RR )' % (Ak, CA)), w.s([kc0], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, SG))], 'remulcld',
                  '( %s -> ( %s x. ( k ^c -u %s ) ) e. RR )' % (Ak, CA, SG))], 'eqeltrd', '( %s -> ( %s ` k ) e. RR )' % (Ak, HB))
    g0 = w.s([w.s([m(EZ('k'))], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Ak, EZ('k'))), vg], 'breqtrrd', '( %s -> 0 <_ ( %s ` k ) )' % (Ak, GA))
    gex = w.s([w.s([], 'mptex', '%s e. _V' % GA)], 'a1i', '( %s -> %s e. _V )' % (A0, GA))
    gl = w.s([nu, z1, hl2, gex, hr, gr, g1, g0], 'climsqz2', '( %s -> %s ~~> 0 )' % (A0, GA))
    fex = w.s([w.s([], 'mptex', '%s e. _V' % FE)], 'a1i', '( %s -> %s e. _V )' % (A0, FE))
    vf, _ = mptval(w, Ak, 'n', 'NN', EZ('n'), 'k', kn, mp=FE)
    fkc = w.s([vf, m(EZ('k'))], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, FE))
    gfa = chain(w, Ak, ['( %s ` k )' % GA, '( abs ` %s )' % EZ('k'), '( abs ` ( %s ` k ) )' % FE],
                [vg, ('r', w.s([vf], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, FE, EZ('k'))))])
    ab0 = w.s([nu, z1, fex, gex, fkc, gfa], 'climabs0', '( %s -> ( %s ~~> 0 <-> %s ~~> 0 ) )' % (A0, FE, GA))
    w.qed([gl, ab0], 'mpbird', '( %s -> %s ~~> 0 )' % (A0, FE))
    go(w)

# ---------------------------------------------------------------- zl1zser
HTS = '( m e. NN |-> %s )' % HT('m', 'Z')
ZTS = '( n e. NN |-> ( n ^c -u Z ) )'
SQH = lambda j: '( seq 1 ( + , %s ) ` %s )' % (HTS, j)
SQZ = lambda j: '( seq 1 ( + , %s ) ` %s )' % (ZTS, j)
G1 = '( i e. NN |-> ( %s + Z ) )' % SQH('i')      # binder i: ZTS binds n (fvmptg's $d x C)
MU = '( i e. NN |-> ( ( Z - 1 ) x. %s ) )' % SQZ('i')
G2 = '( i e. NN |-> ( ( ( Z - 1 ) x. %s ) + %s ) )' % (SQZ('i'), EZ('i'))
SH = 'sum_ k e. NN %s' % HT('k', 'Z')
SZ = 'sum_ k e. NN ( k ^c -u Z )'
if not only or 'zl1zser' in only:
    w = W('zl1zser', 'On ` 1 < Re Z ` the continuation ` Z + sum_ k HT ( k , Z ) ` is ` ( Z - 1 ) zeta ( Z ) ` '
          '( ~ zl1ztel , ~ zl1zlim0 , ~ climuni ): Lean\'s ` zeta_eq_tsum_one_div_nat_cpow ` for ` ( s - 1 ) zeta ( s ) ` .')
    A0 = '( Z e. CC /\\ 1 < ( Re ` Z ) )'
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
    r1z = w.s([], 'simpr', '( %s -> 1 < ( Re ` Z ) )' % A0)
    rz = w.s([zc], 'recld', '( %s -> ( Re ` Z ) e. RR )' % A0)
    z0 = w.s([a1(w, A0, '0re', '0 e. RR'), a1(w, A0, '1re', '1 e. RR'), rz, a1(w, A0, '0lt1', '0 < 1'), r1z], 'lttrd', '( %s -> 0 < ( Re ` Z ) )' % A0)
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    z1 = a1(w, A0, '1z', '1 e. ZZ')
    cv = w.s([w.s([zc, z0], 'jca', '( %s -> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % A0), w.inst('zl1zcv')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, HTS))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    ck = Closure(w, Ak, {'k': ('NN', kn), 'Z': ('CC', w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))})
    hk, _ = mptval(w, Ak, 'm', 'NN', HT('m', 'Z'), 'k', kn, mp=HTS)
    l1 = w.s([nu, z1, hk, ck.mem(HT('k', 'Z'), 'CC'), cv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, HTS, SH))
    cz = w.s([w.s([zc, r1z], 'jca', '( %s -> ( Z e. CC /\\ 1 < ( Re ` Z ) ) )' % A0), w.inst('zsercvgz')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, ZTS))
    zk, _ = mptval(w, Ak, 'n', 'NN', '( n ^c -u Z )', 'k', kn, mp=ZTS)
    l2 = w.s([nu, z1, zk, ck.mem('( k ^c -u Z )', 'CC'), cz], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, ZTS, SZ))
    # the sequences at j
    Aj = '( %s /\\ j e. NN )' % A0
    jn = w.s([], 'simpr', '( %s -> j e. NN )' % Aj)
    zj = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Aj)
    Ajk = '( %s /\\ k e. ( 1 ... j ) )' % Aj
    kj = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... j ) )' % Ajk), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ajk)
    cjk = Closure(w, Ajk, {'k': ('NN', kj), 'Z': ('CC', w.s([zj], 'adantr', '( %s -> Z e. CC )' % Ajk))})
    hjk, _ = mptval(w, Ajk, 'm', 'NN', HT('m', 'Z'), 'k', kj, mp=HTS)
    zjk, _ = mptval(w, Ajk, 'n', 'NN', '( n ^c -u Z )', 'k', kj, mp=ZTS)
    ju = w.s([jn, nu], 'eleqtrdi', '( %s -> j e. ( ZZ>= ` 1 ) )' % Aj)
    fh = w.s([hjk, ju, cjk.mem(HT('k', 'Z'), 'CC')], 'fsumser', '( %s -> sum_ k e. ( 1 ... j ) %s = %s )' % (Aj, HT('k', 'Z'), SQH('j')))
    fz = w.s([zjk, ju, cjk.mem('( k ^c -u Z )', 'CC')], 'fsumser', '( %s -> sum_ k e. ( 1 ... j ) ( k ^c -u Z ) = %s )' % (Aj, SQZ('j')))
    fin = w.s([], 'fzfid', '( %s -> ( 1 ... j ) e. Fin )' % Aj)
    shc = w.s([fh, w.s([fin, cjk.mem(HT('k', 'Z'), 'CC')], 'fsumcl', '( %s -> sum_ k e. ( 1 ... j ) %s e. CC )' % (Aj, HT('k', 'Z')))], 'eqeltrrd', '( %s -> %s e. CC )' % (Aj, SQH('j')))
    szc = w.s([fz, w.s([fin, cjk.mem('( k ^c -u Z )', 'CC')], 'fsumcl', '( %s -> sum_ k e. ( 1 ... j ) ( k ^c -u Z ) e. CC )' % Aj)], 'eqeltrrd', '( %s -> %s e. CC )' % (Aj, SQZ('j')))
    zm1 = w.s([zj, a1(w, Aj, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % Aj)
    cj = Closure(w, Aj, {'j': ('NN', jn), 'Z': ('CC', zj)})
    ezc = cj.mem(EZ('j'), 'CC')
    v1, _ = mptv(w, Aj, 'i', 'NN', '( %s + Z )' % SQH('i'), 'j', jn, mp=G1, exs=w.s([], 'ovexd', '( %s -> ( %s + Z ) e. _V )' % (Aj, SQH('j'))))
    v2, _ = mptv(w, Aj, 'i', 'NN', '( ( ( Z - 1 ) x. %s ) + %s )' % (SQZ('i'), EZ('i')), 'j', jn, mp=G2,
                 exs=w.s([], 'ovexd', '( %s -> ( ( ( Z - 1 ) x. %s ) + %s ) e. _V )' % (Aj, SQZ('j'), EZ('j'))))
    vm, _ = mptv(w, Aj, 'i', 'NN', '( ( Z - 1 ) x. %s )' % SQZ('i'), 'j', jn, mp=MU, exs=w.s([], 'ovexd', '( %s -> ( ( Z - 1 ) x. %s ) e. _V )' % (Aj, SQZ('j'))))
    FE = '( n e. NN |-> %s )' % EZ('n')
    vf, _ = mptv(w, Aj, 'n', 'NN', EZ('n'), 'j', jn, mp=FE, exs=w.s([], 'ovexd', '( %s -> %s e. _V )' % (Aj, EZ('j'))))
    # G1 ~~> SH + Z
    g1ex = w.s([w.s([], 'mptex', '%s e. _V' % G1)], 'a1i', '( %s -> %s e. _V )' % (A0, G1))
    l3 = w.s([nu, z1, l1, zc, g1ex, shc, v1], 'climaddc1', '( %s -> %s ~~> ( %s + Z ) )' % (A0, G1, SH))
    # G2 ~~> ( Z - 1 ) SZ + 0
    muex = w.s([w.s([], 'mptex', '%s e. _V' % MU)], 'a1i', '( %s -> %s e. _V )' % (A0, MU))
    zm1a = w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % A0)
    l4 = w.s([nu, z1, l2, zm1a, muex, szc, vm], 'climmulc2', '( %s -> %s ~~> ( ( Z - 1 ) x. %s ) )' % (A0, MU, SZ))
    l5 = w.s([w.s([zc, r1z], 'jca', '( %s -> ( Z e. CC /\\ 1 < ( Re ` Z ) ) )' % A0), w.inst('zl1zlim0')], 'syl', '( %s -> %s ~~> 0 )' % (A0, FE))
    g2ex = w.s([w.s([], 'mptex', '%s e. _V' % G2)], 'a1i', '( %s -> %s e. _V )' % (A0, G2))
    muc = w.s([vm, w.s([zm1, szc], 'mulcld', '( %s -> ( ( Z - 1 ) x. %s ) e. CC )' % (Aj, SQZ('j')))], 'eqeltrd', '( %s -> ( %s ` j ) e. CC )' % (Aj, MU))
    fec = w.s([vf, ezc], 'eqeltrd', '( %s -> ( %s ` j ) e. CC )' % (Aj, FE))
    h2 = chain(w, Aj, ['( %s ` j )' % G2, '( ( ( Z - 1 ) x. %s ) + %s )' % (SQZ('j'), EZ('j')), '( ( %s ` j ) + ( %s ` j ) )' % (MU, FE)],
               [v2, ('r', E(w, Aj, 'oveq12d', [vm, vf], '( ( %s ` j ) + ( %s ` j ) )' % (MU, FE), '( ( ( Z - 1 ) x. %s ) + %s )' % (SQZ('j'), EZ('j'))))])
    l6 = w.s([nu, z1, l4, g2ex, l5, muc, fec, h2], 'climadd', '( %s -> %s ~~> ( ( ( Z - 1 ) x. %s ) + 0 ) )' % (A0, G2, SZ))
    # G1 = G2 pointwise
    tel = w.s([w.s([zj, jn], 'jca', '( %s -> ( Z e. CC /\\ j e. NN ) )' % Aj), w.inst('zl1ztel')], 'syl',
              '( %s -> ( Z + sum_ k e. ( 1 ... j ) %s ) = ( ( ( Z - 1 ) x. sum_ k e. ( 1 ... j ) ( k ^c -u Z ) ) + %s ) )' % (Aj, HT('k', 'Z'), EZ('j')))
    e1 = E(w, Aj, 'oveq1d', [fh], '( sum_ k e. ( 1 ... j ) %s + Z )' % HT('k', 'Z'), '( %s + Z )' % SQH('j'))
    e2 = E(w, Aj, 'addcomd', [w.s([fin, cjk.mem(HT('k', 'Z'), 'CC')], 'fsumcl', '( %s -> sum_ k e. ( 1 ... j ) %s e. CC )' % (Aj, HT('k', 'Z'))), zj],
           '( sum_ k e. ( 1 ... j ) %s + Z )' % HT('k', 'Z'), '( Z + sum_ k e. ( 1 ... j ) %s )' % HT('k', 'Z'))
    e3 = E(w, Aj, 'oveq1d', [E(w, Aj, 'oveq2d', [fz], '( ( Z - 1 ) x. sum_ k e. ( 1 ... j ) ( k ^c -u Z ) )', '( ( Z - 1 ) x. %s )' % SQZ('j'))],
           '( ( ( Z - 1 ) x. sum_ k e. ( 1 ... j ) ( k ^c -u Z ) ) + %s )' % EZ('j'), '( ( ( Z - 1 ) x. %s ) + %s )' % (SQZ('j'), EZ('j')))
    eqj = chain(w, Aj, ['( %s ` j )' % G1, '( %s + Z )' % SQH('j'), '( sum_ k e. ( 1 ... j ) %s + Z )' % HT('k', 'Z'), '( Z + sum_ k e. ( 1 ... j ) %s )' % HT('k', 'Z'),
                        '( ( ( Z - 1 ) x. sum_ k e. ( 1 ... j ) ( k ^c -u Z ) ) + %s )' % EZ('j'), '( ( ( Z - 1 ) x. %s ) + %s )' % (SQZ('j'), EZ('j')), '( %s ` j )' % G2],
                [v1, ('r', e1), e2, tel, e3, ('r', v2)])
    ce = w.s([nu, g1ex, g2ex, z1, eqj], 'climeq', '( %s -> ( %s ~~> ( ( ( Z - 1 ) x. %s ) + 0 ) <-> %s ~~> ( ( ( Z - 1 ) x. %s ) + 0 ) ) )' % (A0, G1, SZ, G2, SZ))
    l7 = w.s([l6, ce], 'mpbird', '( %s -> %s ~~> ( ( ( Z - 1 ) x. %s ) + 0 ) )' % (A0, G1, SZ))
    un = w.s([l3, l7, w.inst('climuni')], 'syl2anc', '( %s -> ( %s + Z ) = ( ( ( Z - 1 ) x. %s ) + 0 ) )' % (A0, SH, SZ))
    shcc = w.s([nu, z1, hk, ck.mem(HT('k', 'Z'), 'CC'), cv], 'isumcl', '( %s -> %s e. CC )' % (A0, SH))
    szcc = w.s([nu, z1, zk, ck.mem('( k ^c -u Z )', 'CC'), cz], 'isumcl', '( %s -> %s e. CC )' % (A0, SZ))
    chain(w, A0, [ZF('Z'), '( %s + Z )' % SH, '( ( ( Z - 1 ) x. %s ) + 0 )' % SZ, '( ( Z - 1 ) x. %s )' % SZ],
          [E(w, A0, 'addcomd', [zc, shcc], ZF('Z'), '( %s + Z )' % SH), un,
           E(w, A0, 'addridd', [w.s([zm1a, szcc], 'mulcld', '( %s -> ( ( Z - 1 ) x. %s ) e. CC )' % (A0, SZ))], '( ( ( Z - 1 ) x. %s ) + 0 )' % SZ, '( ( Z - 1 ) x. %s )' % SZ)],
          name='qed')
    go(w)

# ---------------------------------------------------------------- zl1z1
if not only or 'zl1z1' in only:
    w = W('zl1z1', 'The zeta continuation terms vanish at ` 1 ` : ` sum_ k HT ( k , 1 ) = 0 ` , so ` ( s - 1 ) zeta ( s ) ` '
          'continued is ` 1 ` at ` s = 1 ` (Lean ` LFunctionTrivChar_1 ` at ` 1 ` , the residue of ` zeta ` ).')
    Ak = 'k e. NN'
    kn = w.s([], 'id', '( k e. NN -> k e. NN )')
    ck = Closure(w, Ak, {'k': ('NN', kn)})
    m = lambda e: ck.mem(e, 'CC')
    k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( k + 1 ) e. NN )' % Ak)
    def inv(K, kc, kne):
        c = w.s([kc, kne, a1(w, Ak, 'ax-1cn', '1 e. CC'), w.inst('cxpneg')], 'syl3anc', '( %s -> ( %s ^c -u 1 ) = ( 1 / ( %s ^c 1 ) ) )' % (Ak, K, K))
        c2 = E(w, Ak, 'oveq2d', [w.s([kc, w.inst('cxp1')], 'syl', '( %s -> ( %s ^c 1 ) = %s )' % (Ak, K, K))], '( 1 / ( %s ^c 1 ) )' % K, '( 1 / %s )' % K)
        c3 = chain(w, Ak, ['( %s ^c -u 1 )' % K, '( 1 / ( %s ^c 1 ) )' % K, '( 1 / %s )' % K], [c, c2])
        c4 = E(w, Ak, 'oveq2d', [c3], '( %s x. ( %s ^c -u 1 ) )' % (K, K), '( %s x. ( 1 / %s ) )' % (K, K))
        return chain(w, Ak, ['( %s x. ( %s ^c -u 1 ) )' % (K, K), '( %s x. ( 1 / %s ) )' % (K, K), '1'], [c4, E(w, Ak, 'recidd', [kc, kne], '( %s x. ( 1 / %s ) )' % (K, K), '1')])
    a = inv('( k + 1 )', m('( k + 1 )'), w.s([k1n], 'nnne0d', '( %s -> ( k + 1 ) =/= 0 )' % Ak))
    b = inv('k', m('k'), w.s([kn], 'nnne0d', '( %s -> k =/= 0 )' % Ak))
    t = E(w, Ak, 'oveq12d', [a, b], HT('k', '1'), '( 1 - 1 )')
    t2 = chain(w, Ak, [HT('k', '1'), '( 1 - 1 )', '0'], [t, E(w, Ak, 'subidd', [m('1')], '( 1 - 1 )', '0')])
    s = w.s([t2], 'sumeq2i', '%s = sum_ k e. NN 0' % HS('1'))
    sz0 = w.s([w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eqimssi', 'NN C_ ( ZZ>= ` 1 )')], 'orci', '( NN C_ ( ZZ>= ` 1 ) \\/ NN e. Fin )'), w.inst('sumz')], 'ax-mp', 'sum_ k e. NN 0 = 0')
    w.qed([s, sz0], 'eqtri', '%s = 0' % HS('1'))
    go(w)
