"""ZL1: the s-derivative of the zeta continuation term: its real primitive P
(zl1pdv), the bound (zl1hdb), and the complex derivative itself (zl1hdv)."""
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


IOO = '( K (,) ( K + 1 ) )'
EXP = '( -u %s - 1 )' % RZ
U_ = '( Z x. ( Z - 1 ) )'
V_ = '( ( 2 x. Z ) - 1 )'
AA = '( ( abs ` Z ) x. ( abs ` ( Z - 1 ) ) )'
D1 = '( -u Z x. ( b ^c ( -u Z - 1 ) ) )'
D2 = '( ( 1 - Z ) x. ( b ^c ( ( 1 - Z ) - 1 ) ) )'
LG = '( log ` b )'


def dlog(w, A0):
    """( A0 -> ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) = ( b e. RR+ |-> ( 1 / b ) ) )  (C5's lgcxpmvt route)"""
    Arp = '( %s /\\ b e. RR+ )' % A0
    brp = w.s([], 'simpr', '( %s -> b e. RR+ )' % Arp)
    lf = w.s([w.s([], 'relogf1o', '( log |` RR+ ) : RR+ -1-1-onto-> RR'), w.inst('f1of')], 'ax-mp', '( log |` RR+ ) : RR+ --> RR')
    lmp = w.s([w.s([lf], 'a1i', '( %s -> ( log |` RR+ ) : RR+ --> RR )' % A0)], 'feqmptd', '( %s -> ( log |` RR+ ) = ( b e. RR+ |-> ( ( log |` RR+ ) ` b ) ) )' % A0)
    lmp2 = w.s([lmp, w.s([w.s([brp, w.inst('fvres')], 'syl', '( %s -> ( ( log |` RR+ ) ` b ) = ( log ` b ) )' % Arp)], 'mpteq2dva',
                         '( %s -> ( b e. RR+ |-> ( ( log |` RR+ ) ` b ) ) = ( b e. RR+ |-> ( log ` b ) ) )' % A0)], 'eqtrd',
               '( %s -> ( log |` RR+ ) = ( b e. RR+ |-> ( log ` b ) ) )' % A0)
    dl = w.s([], 'dvrelog', '( RR _D ( log |` RR+ ) ) = ( x e. RR+ |-> ( 1 / x ) )')
    cbv = w.s([w.s([], 'oveq2', '( x = b -> ( 1 / x ) = ( 1 / b ) )')], 'cbvmptv', '( x e. RR+ |-> ( 1 / x ) ) = ( b e. RR+ |-> ( 1 / b ) )')
    dl2 = w.s([w.s([dl, cbv], 'eqtri', '( RR _D ( log |` RR+ ) ) = ( b e. RR+ |-> ( 1 / b ) )')], 'a1i', '( %s -> ( RR _D ( log |` RR+ ) ) = ( b e. RR+ |-> ( 1 / b ) ) )' % A0)
    return w.s([w.s([w.s([lmp2], 'oveq2d', '( %s -> ( RR _D ( log |` RR+ ) ) = ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) )' % A0)], 'eqcomd',
                    '( %s -> ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) = ( RR _D ( log |` RR+ ) ) )' % A0), dl2], 'eqtrd',
               '( %s -> ( RR _D ( b e. RR+ |-> ( log ` b ) ) ) = ( b e. RR+ |-> ( 1 / b ) ) )' % A0)


def dvP(w, A0, kr, zc):
    """( A0 -> ( RR _D PM ) = ( b e. RR+ |-> RAW ) ), the raw derivative"""
    kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
    sr = a1(w, A0, 'prid1', 'RR e. { RR , CC }')
    Ab = '( %s /\\ b e. RR+ )' % A0
    brp = w.s([], 'simpr', '( %s -> b e. RR+ )' % Ab)
    c = Closure(w, Ab, {'b': ('RR+', brp), 'Z': ('CC', w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ab)),
                        'K': ('RR', w.s([kr], 'adantr', '( %s -> K e. RR )' % Ab))})
    m = lambda e: c.mem(e, 'CC')
    nzc = w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0)
    omz = w.s([a1(w, A0, 'ax-1cn', '1 e. CC'), zc], 'subcld', '( %s -> ( 1 - Z ) e. CC )' % A0)
    d1 = w.s([nzc, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D ( b e. RR+ |-> ( b ^c -u Z ) ) ) = ( b e. RR+ |-> %s ) )' % (A0, D1))
    d2 = w.s([omz, w.inst('dvcxp1')], 'syl', '( %s -> ( RR _D ( b e. RR+ |-> ( b ^c ( 1 - Z ) ) ) ) = ( b e. RR+ |-> %s ) )' % (A0, D2))
    G1 = '( K x. ( b ^c -u Z ) )'
    dK = w.s([sr, m('( b ^c -u Z )'), m(D1), d1, kc], 'dvmptcmul', '( %s -> ( RR _D ( b e. RR+ |-> %s ) ) = ( b e. RR+ |-> ( K x. %s ) ) )' % (A0, G1, D1))
    G = '( %s - ( b ^c ( 1 - Z ) ) )' % G1
    DG = '( ( K x. %s ) - %s )' % (D1, D2)
    dG = w.s([sr, m(G1), m('( K x. %s )' % D1), dK, m('( b ^c ( 1 - Z ) )'), m(D2), d2], 'dvmptsub', '( %s -> ( RR _D ( b e. RR+ |-> %s ) ) = ( b e. RR+ |-> %s ) )' % (A0, G, DG))
    dL = dlog(w, A0)
    dF = w.s([w.s([kr, zc], 'jca', '( %s -> ( K e. RR /\\ Z e. CC ) )' % A0), w.inst('zl1fdv')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, FM, FDM))
    DLF = '( ( ( 1 / b ) x. %s ) + ( %s x. %s ) )' % (FB('b'), FD('b'), LG)
    dLF = w.s([sr, m(LG), m('( 1 / b )'), dL, m(FB('b')), m(FD('b')), dF], 'dvmptmul',
              '( %s -> ( RR _D ( b e. RR+ |-> ( %s x. %s ) ) ) = ( b e. RR+ |-> %s ) )' % (A0, LG, FB('b'), DLF))
    RAW = '( %s - %s )' % (DG, DLF)
    dP = w.s([sr, m(G), m(DG), dG, m('( %s x. %s )' % (LG, FB('b'))), m(DLF), dLF], 'dvmptsub', '( %s -> ( RR _D %s ) = ( b e. RR+ |-> %s ) )' % (A0, PM, RAW))
    return dP, RAW, Ab, brp, c


if not only or 'zl1pdv' in only:
    w = W('zl1pdv', 'The derivative of the primitive ` P ( b ) = K b ^ -Z - b ^ ( 1 - Z ) - log b F ( b ) ` of the '
          '` Z ` -derivative of the zeta continuation term: ` P\' ( b ) = ( b - K ) b ^ ( -Z - 1 ) ( ( 2 Z - 1 ) - Z ( Z - 1 ) log b ) ` .')
    A0 = '( K e. RR /\\ Z e. CC )'
    kr = w.s([], 'simpl', '( %s -> K e. RR )' % A0)
    zc = w.s([], 'simpr', '( %s -> Z e. CC )' % A0)
    dP, RAW, Ab, brp, c = dvP(w, A0, kr, zc)
    m = lambda e: c.mem(e, 'CC')
    bc = w.s([brp], 'rpcnd', '( %s -> b e. CC )' % Ab)
    bne = w.s([brp], 'rpne0d', '( %s -> b =/= 0 )' % Ab)
    zcb = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ab)
    P = '( b ^c %s )' % NZ1
    PBx = '( %s x. b )' % P
    r1 = pw1(w, Ab, 'b', bc, bne, zcb)                    # b ^ ( ( 1 - Z ) - 1 ) = P b
    nzc = w.s([zcb], 'negcld', '( %s -> -u Z e. CC )' % Ab)
    c1 = a1(w, Ab, 'ax-1cn', '1 e. CC')
    e0 = E(w, Ab, 'npcand', [nzc, c1], '( %s + 1 )' % NZ1, '-u Z')
    e1 = E(w, Ab, 'oveq2d', [e0], '( b ^c ( %s + 1 ) )' % NZ1, '( b ^c -u Z )')
    e2 = w.s([bc, bne, m(NZ1), w.inst('cxpp1')], 'syl3anc', '( %s -> ( b ^c ( %s + 1 ) ) = %s )' % (Ab, NZ1, PBx))
    r0 = chain(w, Ab, ['( b ^c -u Z )', '( b ^c ( %s + 1 ) )' % NZ1, PBx], [('r', e1), e2])   # b ^ -Z = P b
    r2a = pwm(w, Ab, 'b', bc, bne, zcb)                   # b ^ ( 1 - Z ) = ( b ^ -Z ) b
    r2b = E(w, Ab, 'oveq1d', [r0], '( ( b ^c -u Z ) x. b )', '( %s x. b )' % PBx)
    r2 = chain(w, Ab, ['( b ^c ( 1 - Z ) )', '( ( b ^c -u Z ) x. b )', '( %s x. b )' % PBx], [r2a, r2b])
    rules = {'( b ^c ( ( 1 - Z ) - 1 ) )': (PBx, r1), '( b ^c -u Z )': (PBx, r0), '( b ^c ( 1 - Z ) )': ('( %s x. b )' % PBx, r2)}
    rw, new = w.rewrite(RAW, rules, Ab)
    alg = w.s([w.s([w.s([w.s([zcb, w.s([w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)], 'adantr', '( %s -> K e. CC )' % Ab)], 'jca', '( %s -> ( Z e. CC /\\ K e. CC ) )' % Ab),
                         w.s([bc, bne], 'jca', '( %s -> ( b e. CC /\\ b =/= 0 ) )' % Ab)], 'jca', '( %s -> ( ( Z e. CC /\\ K e. CC ) /\\ ( b e. CC /\\ b =/= 0 ) ) )' % Ab),
                    w.s([m(P), m(LG)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Ab, P, LG))], 'jca',
                   '( %s -> ( ( ( Z e. CC /\\ K e. CC ) /\\ ( b e. CC /\\ b =/= 0 ) ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (Ab, P, LG)), w.inst('zl1alg3')], 'syl',
              '( %s -> %s = %s )' % (Ab, new, PD('b')))
    pt = chain(w, Ab, [RAW, new, PD('b')], [rw, alg])
    mq = w.s([pt], 'mpteq2dva', '( %s -> ( b e. RR+ |-> %s ) = %s )' % (A0, RAW, PDM))
    w.qed([dP, mq], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, PM, PDM))
    go(w)


if not only or 'zl1hdb' in only:
    w = W('zl1hdb', 'The ` Z ` -derivative ` HD ( K , Z ) ` of the zeta continuation term is bounded by '
          '` ( | 2 Z - 1 | + | Z | | Z - 1 | log ( K + 1 ) ) K ^ ( -Re Z - 1 ) ` ( ~ zl1lip at ~ zl1pdv ).')
    A0 = '( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s )' % RZ
    kn = w.s([], 'simpll', '( %s -> K e. NN )' % A0)
    zc = w.s([], 'simplr', '( %s -> Z e. CC )' % A0)
    rzp = w.s([], 'simpr', '( %s -> 0 < %s )' % (A0, RZ))
    krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
    kr = w.s([krp], 'rpred', '( %s -> K e. RR )' % A0)
    kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
    k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
    c0 = Closure(w, A0, {'K': ('NN', kn), 'Z': ('CC', zc)})
    p = '( K ^c -u Z )'; q = '( ( K + 1 ) ^c -u Z )'
    c0.have(q, 'CC', w.s([w.s([k1n], 'nncnd', '( %s -> ( K + 1 ) e. CC )' % A0), w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')],
                         'syl2anc', '( %s -> %s e. CC )' % (A0, q)))
    c0.have(p, 'CC', w.s([kc, w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')], 'syl2anc', '( %s -> %s e. CC )' % (A0, p)))
    dP, RAW, Ab, brp, c = dvP(w, A0, kr, zc)
    mb = lambda e: c.mem(e, 'CC')
    ff = w.s([mb(PB('b')), w.s([], 'eqid', '%s = %s' % (PM, PM))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, PM))
    gf = w.s([mb(PD('b')), w.s([], 'eqid', '%s = %s' % (PDM, PDM))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, PDM))
    dfg = w.s([w.s([kr, zc], 'jca', '( %s -> ( K e. RR /\\ Z e. CC ) )' % A0), w.inst('zl1pdv')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, PM, PDM))
    rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    ab1 = w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)
    zm1 = w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % A0)
    ab2 = w.s([zm1], 'abscld', '( %s -> ( abs ` ( Z - 1 ) ) e. RR )' % A0)
    aar = w.s([ab1, ab2], 'remulcld', '( %s -> %s e. RR )' % (A0, AA))
    aa0 = w.s([ab1, ab2, w.s([zc], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % A0), w.s([zm1], 'absge0d', '( %s -> 0 <_ ( abs ` ( Z - 1 ) ) )' % A0)],
              'mulge0d', '( %s -> 0 <_ %s )' % (A0, AA))
    kxr = w.s([w.s([krp, w.s([w.s([rz], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ)), a1(w, A0, '1re', '1 e. RR')], 'resubcld', '( %s -> %s e. RR )' % (A0, EXP))],
                   'rpcxpcld', '( %s -> ( K ^c %s ) e. RR+ )' % (A0, EXP))], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EXP))
    vc = c0.mem(V_, 'CC')
    vr = w.s([vc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, V_))
    lk1 = w.s([w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'relogcld', '( %s -> ( log ` ( K + 1 ) ) e. RR )' % A0)
    W1 = '( ( abs ` %s ) + ( %s x. ( log ` ( K + 1 ) ) ) )' % (V_, AA)
    w1r = w.s([vr, w.s([aar, lk1], 'remulcld', '( %s -> ( %s x. ( log ` ( K + 1 ) ) ) e. RR )' % (A0, AA))], 'readdcld', '( %s -> %s e. RR )' % (A0, W1))
    mdr = w.s([w1r, kxr], 'remulcld', '( %s -> %s e. RR )' % (A0, MD))
    # the bound on ( K , K + 1 )
    At = '( %s /\\ t e. %s )' % (A0, IOO)
    tio = w.s([], 'simpr', '( %s -> t e. %s )' % (At, IOO))
    kt = w.s([tio, w.inst('eliooord')], 'syl', '( %s -> ( K < t /\\ t < ( K + 1 ) ) )' % At)
    tre = w.s([tio, w.inst('elioore')], 'syl', '( %s -> t e. RR )' % At)
    krt = w.s([kr], 'adantr', '( %s -> K e. RR )' % At)
    ktl = w.s([kt], 'simpld', '( %s -> K < t )' % At)
    tk1 = w.s([kt], 'simprd', '( %s -> t < ( K + 1 ) )' % At)
    tpos = w.s([a1(w, At, '0re', '0 e. RR'), krt, tre, w.s([w.s([krp], 'rpgt0d', '( %s -> 0 < K )' % A0)], 'adantr', '( %s -> 0 < K )' % At), ktl], 'lttrd', '( %s -> 0 < t )' % At)
    trp = w.s([tre, tpos], 'elrpd', '( %s -> t e. RR+ )' % At)
    tv, _ = mptval(w, At, 'b', 'RR+', PD('b'), 't', trp)
    Pt = '( t ^c %s )' % NZ1
    zt = w.s([zc], 'adantr', '( %s -> Z e. CC )' % At)
    ct = Closure(w, At, {'t': ('RR+', trp), 'Z': ('CC', zt), 'K': ('RR', krt)})
    mt = lambda e: ct.mem(e, 'CC')
    LT = '( log ` t )'
    DT = '( ( t - K ) x. %s )' % Pt
    VL = '( %s - ( %s x. %s ) )' % (V_, U_, LT)
    a_1 = E(w, At, 'absmuld', [mt(DT), mt(VL)], '( abs ` %s )' % PD('t'), '( ( abs ` %s ) x. ( abs ` %s ) )' % (DT, VL))
    a_2 = E(w, At, 'absmuld', [mt('( t - K )'), mt(Pt)], '( abs ` %s )' % DT, '( ( abs ` ( t - K ) ) x. ( abs ` %s ) )' % Pt)
    a_3 = E(w, At, 'oveq1d', [a_2], '( ( abs ` %s ) x. ( abs ` %s ) )' % (DT, VL), '( ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) )' % (Pt, VL))
    # | t - K | <_ 1
    tk0 = w.s([krt, tre, ktl], 'ltled', '( %s -> K <_ t )' % At)
    tkr = w.s([tre, krt], 'resubcld', '( %s -> ( t - K ) e. RR )' % At)
    tkg = w.s([tk0, w.s([tre, krt, w.inst('subge0')], 'syl2anc', '( %s -> ( 0 <_ ( t - K ) <-> K <_ t ) )' % At)], 'mpbird', '( %s -> 0 <_ ( t - K ) )' % At)
    tabs = w.s([tkr, tkg], 'absidd', '( %s -> ( abs ` ( t - K ) ) = ( t - K ) )' % At)
    tkl = w.s([tk1, w.s([tre, krt, a1(w, At, '1re', '1 e. RR'), w.inst('ltsubadd2')], 'syl3anc', '( %s -> ( ( t - K ) < 1 <-> t < ( K + 1 ) ) )' % At)], 'mpbird',
              '( %s -> ( t - K ) < 1 )' % At)
    tabl = w.s([tabs, w.s([tkr, a1(w, At, '1re', '1 e. RR'), tkl], 'ltled', '( %s -> ( t - K ) <_ 1 )' % At)], 'eqbrtrd', '( %s -> ( abs ` ( t - K ) ) <_ 1 )' % At)
    # | P ( t ) | <_ K ^ EXP
    nzt = w.s([zt], 'negcld', '( %s -> -u Z e. CC )' % At)
    ab_p = w.s([trp, mt(NZ1), w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( t ^c ( Re ` %s ) ) )' % (At, Pt, NZ1))
    re1 = w.s([w.s([nzt, a1(w, At, 'ax-1cn', '1 e. CC'), w.inst('resub')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( Re ` -u Z ) - ( Re ` 1 ) ) )' % (At, NZ1)),
               w.s([w.s([zt, w.inst('reneg')], 'syl', '( %s -> ( Re ` -u Z ) = -u %s )' % (At, RZ)), a1(w, At, 're1', '( Re ` 1 ) = 1')], 'oveq12d',
                   '( %s -> ( ( Re ` -u Z ) - ( Re ` 1 ) ) = %s )' % (At, EXP))], 'eqtrd', '( %s -> ( Re ` %s ) = %s )' % (At, NZ1, EXP))
    ab_p2 = w.s([ab_p, w.s([re1], 'oveq2d', '( %s -> ( t ^c ( Re ` %s ) ) = ( t ^c %s ) )' % (At, NZ1, EXP))], 'eqtrd', '( %s -> ( abs ` %s ) = ( t ^c %s ) )' % (At, Pt, EXP))
    rzt = w.s([rz], 'adantr', '( %s -> %s e. RR )' % (At, RZ))
    rz1 = w.s([rzt, a1(w, At, '1re', '1 e. RR')], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (At, RZ))
    rz10 = w.s([a1(w, At, '0re', '0 e. RR'), rz1, w.s([a1(w, At, '0re', '0 e. RR'), rzt, rz1, w.s([rzp], 'adantr', '( %s -> 0 < %s )' % (At, RZ)),
                                                        w.s([rzt], 'ltp1d', '( %s -> %s < ( %s + 1 ) )' % (At, RZ, RZ))], 'lttrd', '( %s -> 0 < ( %s + 1 ) )' % (At, RZ))],
               'ltled', '( %s -> 0 <_ ( %s + 1 ) )' % (At, RZ))
    anti = w.s([w.s([w.s([krp], 'adantr', '( %s -> K e. RR+ )' % At), trp, rz1], '3jca', '( %s -> ( K e. RR+ /\\ t e. RR+ /\\ ( %s + 1 ) e. RR ) )' % (At, RZ)),
                w.s([rz10, tk0], 'jca', '( %s -> ( 0 <_ ( %s + 1 ) /\\ K <_ t ) )' % (At, RZ)), w.inst('cxpnegle')], 'syl2anc',
               '( %s -> ( t ^c -u ( %s + 1 ) ) <_ ( K ^c -u ( %s + 1 ) ) )' % (At, RZ, RZ))
    ee = w.s([w.s([rzt], 'recnd', '( %s -> %s e. CC )' % (At, RZ)), a1(w, At, 'ax-1cn', '1 e. CC')], 'negdi2d', '( %s -> -u ( %s + 1 ) = %s )' % (At, RZ, EXP))
    anti2 = w.s([w.s([w.s([ee], 'oveq2d', '( %s -> ( t ^c -u ( %s + 1 ) ) = ( t ^c %s ) )' % (At, RZ, EXP)), anti], 'eqbrtrrd',
                     '( %s -> ( t ^c %s ) <_ ( K ^c -u ( %s + 1 ) ) )' % (At, EXP, RZ)),
                 w.s([ee], 'oveq2d', '( %s -> ( K ^c -u ( %s + 1 ) ) = ( K ^c %s ) )' % (At, RZ, EXP))], 'breqtrd', '( %s -> ( t ^c %s ) <_ ( K ^c %s ) )' % (At, EXP, EXP))
    pbl = w.s([ab_p2, anti2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( K ^c %s ) )' % (At, Pt, EXP))
    kxrt = w.s([kxr], 'adantr', '( %s -> ( K ^c %s ) e. RR )' % (At, EXP))
    tkabr = w.s([mt('( t - K )')], 'abscld', '( %s -> ( abs ` ( t - K ) ) e. RR )' % At)
    pabr = w.s([mt(Pt)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, Pt))
    prd = w.s([tkabr, a1(w, At, '1re', '1 e. RR'), pabr, kxrt, w.s([mt('( t - K )')], 'absge0d', '( %s -> 0 <_ ( abs ` ( t - K ) ) )' % At),
               w.s([mt(Pt)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (At, Pt)), tabl, pbl], 'lemul12ad',
              '( %s -> ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) <_ ( 1 x. ( K ^c %s ) ) )' % (At, Pt, EXP))
    prd2 = w.s([prd, w.s([w.s([kxrt], 'recnd', '( %s -> ( K ^c %s ) e. CC )' % (At, EXP))], 'mullidd', '( %s -> ( 1 x. ( K ^c %s ) ) = ( K ^c %s ) )' % (At, EXP, EXP))],
               'breqtrd', '( %s -> ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) <_ ( K ^c %s ) )' % (At, Pt, EXP))
    # | V - U log t | <_ | V | + | Z | | Z - 1 | log ( K + 1 )
    t1 = w.s([mt(V_), mt('( %s x. %s )' % (U_, LT)), w.inst('abs2dif2')], 'syl2anc', '( %s -> ( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s x. %s ) ) ) )' % (At, VL, V_, U_, LT))
    ulc = E(w, At, 'absmuld', [mt(U_), mt(LT)], '( abs ` ( %s x. %s ) )' % (U_, LT), '( ( abs ` %s ) x. ( abs ` %s ) )' % (U_, LT))
    uab = E(w, At, 'absmuld', [mt('Z'), mt('( Z - 1 )')], '( abs ` %s )' % U_, AA)
    t1le = w.s([a1(w, At, '1re', '1 e. RR'), krt, tre, w.s([w.s([kn], 'nnge1d', '( %s -> 1 <_ K )' % A0)], 'adantr', '( %s -> 1 <_ K )' % At), tk0],
               'letrd', '( %s -> 1 <_ t )' % At)
    lt0 = w.s([tre, t1le, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ %s )' % (At, LT))
    ltr = w.s([trp], 'relogcld', '( %s -> %s e. RR )' % (At, LT))
    lab = w.s([ltr, lt0], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (At, LT, LT))
    ulv = chain(w, At, ['( abs ` ( %s x. %s ) )' % (U_, LT), '( ( abs ` %s ) x. ( abs ` %s ) )' % (U_, LT), '( %s x. %s )' % (AA, LT)],
                [ulc, E(w, At, 'oveq12d', [uab, lab], '( ( abs ` %s ) x. ( abs ` %s ) )' % (U_, LT), '( %s x. %s )' % (AA, LT))])
    k1rp = w.s([w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'adantr', '( %s -> ( K + 1 ) e. RR+ )' % At)
    llt = w.s([tk1, w.s([trp, k1rp, w.inst('logltb')], 'syl2anc', '( %s -> ( t < ( K + 1 ) <-> %s < ( log ` ( K + 1 ) ) ) )' % (At, LT))], 'mpbid',
              '( %s -> %s < ( log ` ( K + 1 ) ) )' % (At, LT))
    lk1t = w.s([lk1], 'adantr', '( %s -> ( log ` ( K + 1 ) ) e. RR )' % At)
    lle = w.s([ltr, lk1t, llt], 'ltled', '( %s -> %s <_ ( log ` ( K + 1 ) ) )' % (At, LT))
    aart = w.s([aar], 'adantr', '( %s -> %s e. RR )' % (At, AA))
    ull = w.s([ltr, lk1t, aart, w.s([aa0], 'adantr', '( %s -> 0 <_ %s )' % (At, AA)), lle], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. ( log ` ( K + 1 ) ) ) )' % (At, AA, LT, AA))
    ull2 = w.s([ulv, ull], 'eqbrtrd', '( %s -> ( abs ` ( %s x. %s ) ) <_ ( %s x. ( log ` ( K + 1 ) ) ) )' % (At, U_, LT, AA))
    vrt = w.s([vr], 'adantr', '( %s -> ( abs ` %s ) e. RR )' % (At, V_))
    t2 = w.s([w.s([mt('( %s x. %s )' % (U_, LT))], 'abscld', '( %s -> ( abs ` ( %s x. %s ) ) e. RR )' % (At, U_, LT)),
              w.s([aart, lk1t], 'remulcld', '( %s -> ( %s x. ( log ` ( K + 1 ) ) ) e. RR )' % (At, AA)), vrt, ull2], 'leadd2dd',
             '( %s -> ( ( abs ` %s ) + ( abs ` ( %s x. %s ) ) ) <_ %s )' % (At, V_, U_, LT, W1))
    vl1 = w.s([t1, t2], 'letrd', '( %s -> ( abs ` %s ) <_ %s )' % (At, VL, W1))
    # the product
    w1rt = w.s([w1r], 'adantr', '( %s -> %s e. RR )' % (At, W1))
    prr = w.s([tkabr, pabr], 'remulcld', '( %s -> ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) e. RR )' % (At, Pt))
    pr0 = w.s([tkabr, pabr, w.s([mt('( t - K )')], 'absge0d', '( %s -> 0 <_ ( abs ` ( t - K ) ) )' % At), w.s([mt(Pt)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (At, Pt))],
              'mulge0d', '( %s -> 0 <_ ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) )' % (At, Pt))
    fin = w.s([prr, kxrt, w.s([mt(VL)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, VL)), w1rt, pr0, w.s([mt(VL)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (At, VL)), prd2, vl1],
              'lemul12ad', '( %s -> ( ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) ) <_ ( ( K ^c %s ) x. %s ) )' % (At, Pt, VL, EXP, W1))
    fin2 = w.s([fin, E(w, At, 'mulcomd', [w.s([kxrt], 'recnd', '( %s -> ( K ^c %s ) e. CC )' % (At, EXP)), w.s([w1rt], 'recnd', '( %s -> %s e. CC )' % (At, W1))],
                       '( ( K ^c %s ) x. %s )' % (EXP, W1), MD)], 'breqtrd', '( %s -> ( ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) ) <_ %s )' % (At, Pt, VL, MD))
    fdv = w.s([w.s([tv], 'fveq2d', '( %s -> ( abs ` ( %s ` t ) ) = ( abs ` %s ) )' % (At, PDM, PD('t'))), a_1, a_3], '3eqtrd',
              '( %s -> ( abs ` ( %s ` t ) ) = ( ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) x. ( abs ` %s ) ) )' % (At, PDM, Pt, VL))
    bt = w.s([fdv, fin2], 'eqbrtrd', '( %s -> ( abs ` ( %s ` t ) ) <_ %s )' % (At, PDM, MD))
    bnd = w.s([bt], 'ralrimiva', '( %s -> A. t e. %s ( abs ` ( %s ` t ) ) <_ %s )' % (A0, IOO, PDM, MD))
    lip = w.s([w.s([w.s([ff, gf, dfg], '3jca', '( %s -> ( %s : RR+ --> CC /\\ %s : RR+ --> CC /\\ ( RR _D %s ) = %s ) )' % (A0, PM, PDM, PM, PDM)),
                    w.s([krp, mdr, bnd], '3jca', '( %s -> ( K e. RR+ /\\ %s e. RR /\\ A. t e. %s ( abs ` ( %s ` t ) ) <_ %s ) )' % (A0, MD, IOO, PDM, MD))], 'jca',
                   '( %s -> ( ( %s : RR+ --> CC /\\ %s : RR+ --> CC /\\ ( RR _D %s ) = %s ) /\\ ( K e. RR+ /\\ %s e. RR /\\ A. t e. %s ( abs ` ( %s ` t ) ) <_ %s ) ) )'
                   % (A0, PM, PDM, PM, PDM, MD, IOO, PDM, MD)), w.inst('zl1lip')], 'syl',
              '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ %s )' % (A0, PM, PM, MD))
    # the values P ( K ), P ( K + 1 )
    vK, PK = mptval(w, A0, 'b', 'RR+', PB('b'), 'K', krp)
    k1rp0 = w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)
    vK1, PK1 = mptval(w, A0, 'b', 'RR+', PB('b'), '( K + 1 )', k1rp0)
    kne = w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)
    k1c = w.s([k1n], 'nncnd', '( %s -> ( K + 1 ) e. CC )' % A0)
    k1ne = w.s([k1n], 'nnne0d', '( %s -> ( K + 1 ) =/= 0 )' % A0)
    pk = pwm(w, A0, 'K', kc, kne, zc)
    pk1 = pwm(w, A0, '( K + 1 )', k1c, k1ne, zc)
    rwK, PKa = w.rewrite(PK, {'( K ^c ( 1 - Z ) )': ('( %s x. K )' % p, pk)}, A0)
    rwK1, PK1a = w.rewrite(PK1, {'( ( K + 1 ) ^c ( 1 - Z ) )': ('( %s x. ( K + 1 ) )' % q, pk1)}, A0)
    FKs = '( ( %s x. %s ) - ( Z x. ( %s x. K ) ) )' % (ZK, p, p)
    FK1s = '( ( %s x. %s ) - ( Z x. ( %s x. ( K + 1 ) ) ) )' % (ZK, q, q)
    alg = w.s([w.s([w.s([zc, kc], 'jca', '( %s -> ( Z e. CC /\\ K e. CC ) )' % A0), w.s([c0.mem(p, 'CC'), c0.mem(q, 'CC')], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, p, q))],
                   'jca', '( %s -> ( ( Z e. CC /\\ K e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, p, q)), w.inst('zl1alg2')], 'syl',
              '( %s -> ( %s = -u ( K x. %s ) /\\ %s = -u ( ( K + Z ) x. %s ) ) )' % (A0, FKs, p, FK1s, q))
    a1_ = w.s([alg], 'simpld', '( %s -> %s = -u ( K x. %s ) )' % (A0, FKs, p))
    a2_ = w.s([alg], 'simprd', '( %s -> %s = -u ( ( K + Z ) x. %s ) )' % (A0, FK1s, q))
    rwK2, PKb = w.rewrite(PKa, {FKs: ('-u ( K x. %s )' % p, a1_)}, A0)
    rwK12, PK1b = w.rewrite(PK1a, {FK1s: ('-u ( ( K + Z ) x. %s )' % q, a2_)}, A0)
    PKv = chain(w, A0, ['( %s ` K )' % PM, PK, PKa, PKb], [vK, rwK, rwK2])
    PK1v = chain(w, A0, ['( %s ` ( K + 1 ) )' % PM, PK1, PK1a, PK1b], [vK1, rwK1, rwK12])
    df = E(w, A0, 'oveq12d', [PKv, PK1v], '( ( %s ` K ) - ( %s ` ( K + 1 ) ) )' % (PM, PM), '( %s - %s )' % (PKb, PK1b))
    lkc = w.s([w.s([krp], 'relogcld', '( %s -> ( log ` K ) e. RR )' % A0)], 'recnd', '( %s -> ( log ` K ) e. CC )' % A0)
    lk1c = w.s([lk1], 'recnd', '( %s -> ( log ` ( K + 1 ) ) e. CC )' % A0)
    alg4 = w.s([w.s([w.s([w.s([zc, kc], 'jca', '( %s -> ( Z e. CC /\\ K e. CC ) )' % A0), w.s([c0.mem(p, 'CC'), c0.mem(q, 'CC')], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, p, q))],
                         'jca', '( %s -> ( ( Z e. CC /\\ K e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, p, q)),
                    w.s([lkc, lk1c], 'jca', '( %s -> ( ( log ` K ) e. CC /\\ ( log ` ( K + 1 ) ) e. CC ) )' % A0)], 'jca',
                   '( %s -> ( ( ( Z e. CC /\\ K e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) /\\ ( ( log ` K ) e. CC /\\ ( log ` ( K + 1 ) ) e. CC ) ) )' % (A0, p, q)),
                w.inst('zl1alg4')], 'syl', '( %s -> ( %s - %s ) = %s )' % (A0, PKb, PK1b, HD('K', 'Z')))
    htv = chain(w, A0, ['( ( %s ` K ) - ( %s ` ( K + 1 ) ) )' % (PM, PM), '( %s - %s )' % (PKb, PK1b), HD('K', 'Z')], [df, alg4])
    fkc1 = w.s([ff, krp], 'ffvelcdmd', '( %s -> ( %s ` K ) e. CC )' % (A0, PM))
    fkc2 = w.s([ff, k1rp0], 'ffvelcdmd', '( %s -> ( %s ` ( K + 1 ) ) e. CC )' % (A0, PM))
    sw = E(w, A0, 'abssubd', [fkc1, fkc2], '( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) )' % (PM, PM), '( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) )' % (PM, PM))
    habs = w.s([htv], 'fveq2d', '( %s -> ( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) ) = ( abs ` %s ) )' % (A0, PM, PM, HD('K', 'Z')))
    eqa = chain(w, A0, ['( abs ` %s )' % HD('K', 'Z'), '( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) )' % (PM, PM), '( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) )' % (PM, PM)],
                [('r', habs), sw])
    w.qed([eqa, lip], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, HD('K', 'Z'), MD))
    go(w)


if not only or 'zl1hdv' in only:
    w = W('zl1hdv', 'The complex derivative of the zeta continuation term ` z |-> HT ( K , z ) ` on an open set '
          '( ~ cxpnegdv , ~ dvmptmul ).')
    A0 = '( K e. NN /\\ U e. %s )' % TOPO
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
    uo = w.s([], 'simpr', '( %s -> U e. %s )' % (A0, TOPO))
    krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
    kc = w.s([kn], 'nncnd', '( %s -> K e. CC )' % A0)
    k1rp = w.s([w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)
    sc = a1(w, A0, 'cnelprrecn', 'CC e. { RR , CC }')
    ek = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    ton = w.s([w.s([ek], 'cnfldtopon', '%s e. ( TopOn ` CC )' % TOP)], 'a1i', '( %s -> %s e. ( TopOn ` CC ) )' % (A0, TOP))
    ucc = w.s([ton, uo, w.inst('toponss')], 'syl2anc', '( %s -> U C_ CC )' % A0)
    Az = '( %s /\\ z e. U )' % A0
    zu = w.s([], 'simpr', '( %s -> z e. U )' % Az)
    zc = w.s([w.s([ucc], 'adantr', '( %s -> U C_ CC )' % Az), zu], 'sseldd', '( %s -> z e. CC )' % Az)
    cz = Closure(w, Az, {'z': ('CC', zc), 'K': ('NN', w.s([kn], 'adantr', '( %s -> K e. NN )' % Az))})
    m = lambda e: cz.mem(e, 'CC')
    Ac = '( %s /\\ z e. CC )' % A0
    zcc = w.s([], 'simpr', '( %s -> z e. CC )' % Ac)
    kcc = w.s([kc], 'adantr', '( %s -> K e. CC )' % Ac)
    # ( K + z ) on CC, then on U
    d0 = w.s([sc, kcc, a1(w, Ac, '0cn', '0 e. CC'), w.s([sc], 'dvmptc', '( %s -> ( CC _D ( z e. CC |-> K ) ) = ( z e. CC |-> 0 ) )' % A0),
              zcc, a1(w, Ac, 'ax-1cn', '1 e. CC'), w.s([sc], 'dvmptid', '( %s -> ( CC _D ( z e. CC |-> z ) ) = ( z e. CC |-> 1 ) )' % A0)], 'dvmptadd',
             '( %s -> ( CC _D ( z e. CC |-> ( K + z ) ) ) = ( z e. CC |-> ( 0 + 1 ) ) )' % A0)
    rest = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    d0u = w.s([sc, w.s([kcc, zcc], 'addcld', '( %s -> ( K + z ) e. CC )' % Ac), w.s([a1(w, Ac, '0cn', '0 e. CC'), a1(w, Ac, 'ax-1cn', '1 e. CC')], 'addcld', '( %s -> ( 0 + 1 ) e. CC )' % Ac), d0, ucc, rest, ek, uo], 'dvmptres',
              '( %s -> ( CC _D ( z e. U |-> ( K + z ) ) ) = ( z e. U |-> ( 0 + 1 ) ) )' % A0)
    o1 = w.s([w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'a1i', '( %s -> ( 0 + 1 ) = 1 )' % Az)], 'mpteq2dva', '( %s -> ( z e. U |-> ( 0 + 1 ) ) = ( z e. U |-> 1 ) )' % A0)
    d1 = w.s([d0u, o1], 'eqtrd', '( %s -> ( CC _D ( z e. U |-> ( K + z ) ) ) = ( z e. U |-> 1 ) )' % A0)
    q = '( ( K + 1 ) ^c -u z )'; p = '( K ^c -u z )'
    G = '( log ` ( K + 1 ) )'; A_ = '( log ` K )'
    d2 = w.s([k1rp, uo, w.inst('cxpnegdv')], 'syl2anc', '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> -u ( %s x. %s ) ) )' % (A0, q, G, q))
    d3 = w.s([krp, uo, w.inst('cxpnegdv')], 'syl2anc', '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> -u ( %s x. %s ) ) )' % (A0, p, A_, p))
    DM = '( ( 1 x. %s ) + ( -u ( %s x. %s ) x. ( K + z ) ) )' % (q, G, q)
    d4 = w.s([sc, m('( K + z )'), m('1'), d1, m(q), m('-u ( %s x. %s )' % (G, q)), d2], 'dvmptmul',
             '( %s -> ( CC _D ( z e. U |-> ( ( K + z ) x. %s ) ) ) = ( z e. U |-> %s ) )' % (A0, q, DM))
    d5 = w.s([sc, m(p), m('-u ( %s x. %s )' % (A_, p)), d3, kc], 'dvmptcmul',
             '( %s -> ( CC _D ( z e. U |-> ( K x. %s ) ) ) = ( z e. U |-> ( K x. -u ( %s x. %s ) ) ) )' % (A0, p, A_, p))
    RAW = '( %s - ( K x. -u ( %s x. %s ) ) )' % (DM, A_, p)
    d6 = w.s([sc, m('( ( K + z ) x. %s )' % q), m(DM), d4, m('( K x. %s )' % p), m('( K x. -u ( %s x. %s ) )' % (A_, p)), d5], 'dvmptsub',
             '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (A0, HT('K', 'z'), RAW))
    alg = w.s([w.s([w.s([zc, w.s([kc], 'adantr', '( %s -> K e. CC )' % Az)], 'jca', '( %s -> ( z e. CC /\\ K e. CC ) )' % Az),
                    w.s([w.s([m(p), m(q)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Az, p, q)), w.s([m(A_), m(G)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Az, A_, G))],
                        'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (Az, p, q, A_, G))], 'jca',
                   '( %s -> ( ( z e. CC /\\ K e. CC ) /\\ ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) ) )' % (Az, p, q, A_, G)), w.inst('zl1alg5')], 'syl',
              '( %s -> %s = %s )' % (Az, RAW, HD('K', 'z')))
    mq = w.s([alg], 'mpteq2dva', '( %s -> ( z e. U |-> %s ) = ( z e. U |-> %s ) )' % (A0, RAW, HD('K', 'z')))
    w.qed([d6, mq], 'eqtrd', '( %s -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (A0, HT('K', 'z'), HD('K', 'z')))
    go(w)
