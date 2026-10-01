"""ZL1: the value bound of the zeta continuation term (zl1fdv, zl1hvb)."""
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


if not only or 'zl1fdv' in only:
    w = W('zl1fdv', 'The derivative of the primitive ` F ( b ) = ( Z - 1 ) K b ^ -Z - Z b ^ ( 1 - Z ) ` of the '
          'zeta continuation term: ` F\' ( b ) = Z ( Z - 1 ) ( b - K ) b ^ ( -Z - 1 ) ` .')
    A0 = '( K e. RR /\\ Z e. CC )'
    kc = w.s([w.s([], 'simpl', '( %s -> K e. RR )' % A0)], 'recnd', '( %s -> K e. CC )' % A0)
    zc = w.s([], 'simpr', '( %s -> Z e. CC )' % A0)
    d5, RHS, Ab, brp, c = dvF(w, A0, zc, kc)
    m = lambda e: c.mem(e, 'CC')
    bc = w.s([brp], 'rpcnd', '( %s -> b e. CC )' % Ab)
    bne = w.s([brp], 'rpne0d', '( %s -> b =/= 0 )' % Ab)
    zcb = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ab)
    P = '( b ^c %s )' % NZ1
    p1 = pw1(w, Ab, 'b', bc, bne, zcb)
    q1 = E(w, Ab, 'oveq2d', [p1], '( ( 1 - Z ) x. ( b ^c ( ( 1 - Z ) - 1 ) ) )', '( ( 1 - Z ) x. ( %s x. b ) )' % P)
    q2 = E(w, Ab, 'oveq2d', [q1], '( Z x. ( ( 1 - Z ) x. ( b ^c ( ( 1 - Z ) - 1 ) ) ) )', '( Z x. ( ( 1 - Z ) x. ( %s x. b ) ) )' % P)
    q3 = E(w, Ab, 'oveq2d', [q2], RHS, '( ( %s x. ( -u Z x. %s ) ) - ( Z x. ( ( 1 - Z ) x. ( %s x. b ) ) ) )' % (ZK, P, P))
    alg = w.s([w.s([w.s([zcb, w.s([kc], 'adantr', '( %s -> K e. CC )' % Ab)], 'jca', '( %s -> ( Z e. CC /\\ K e. CC ) )' % Ab),
                    w.s([bc, m(P)], 'jca', '( %s -> ( b e. CC /\\ %s e. CC ) )' % (Ab, P))], 'jca',
                   '( %s -> ( ( Z e. CC /\\ K e. CC ) /\\ ( b e. CC /\\ %s e. CC ) ) )' % (Ab, P)), w.inst('zl1alg1')], 'syl',
              '( %s -> ( ( %s x. ( -u Z x. %s ) ) - ( Z x. ( ( 1 - Z ) x. ( %s x. b ) ) ) ) = %s )' % (Ab, ZK, P, P, FD('b')))
    pt = chain(w, Ab, [RHS, '( ( %s x. ( -u Z x. %s ) ) - ( Z x. ( ( 1 - Z ) x. ( %s x. b ) ) ) )' % (ZK, P, P), FD('b')], [q3, alg])
    mq = w.s([pt], 'mpteq2dva', '( %s -> ( b e. RR+ |-> %s ) = %s )' % (A0, RHS, FDM))
    w.qed([d5, mq], 'eqtrd', '( %s -> ( RR _D %s ) = %s )' % (A0, FM, FDM))
    go(w)


if not only or 'zl1hvb' in only:
    w = W('zl1hvb', 'The term ` HT ( K , Z ) = ( K + Z ) ( K + 1 ) ^ -Z - K K ^ -Z ` of the continuation of '
          '` ( Z - 1 ) zeta ( Z ) ` is bounded by ` | Z | | Z - 1 | K ^ ( -Re Z - 1 ) ` ( ~ zl1lip at ~ zl1fdv ).')
    A0 = '( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s )' % RZ
    kn = w.s([], 'simpll', '( %s -> K e. NN )' % A0)
    zc = w.s([], 'simplr', '( %s -> Z e. CC )' % A0)
    rzp = w.s([], 'simpr', '( %s -> 0 < %s )' % (A0, RZ))
    krp = w.s([kn], 'nnrpd', '( %s -> K e. RR+ )' % A0)
    kr = w.s([krp], 'rpred', '( %s -> K e. RR )' % A0)
    kc = w.s([kr], 'recnd', '( %s -> K e. CC )' % A0)
    c0 = Closure(w, A0, {'K': ('NN', kn), 'Z': ('CC', zc)})
    c0.have('( ( K + 1 ) ^c -u Z )', 'CC', w.s([w.s([w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)], 'nncnd',
                                                      '( %s -> ( K + 1 ) e. CC )' % A0), w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')],
                                                'syl2anc', '( %s -> ( ( K + 1 ) ^c -u Z ) e. CC )' % A0))
    c0.have('( K ^c -u Z )', 'CC', w.s([kc, w.s([zc], 'negcld', '( %s -> -u Z e. CC )' % A0), w.inst('cxpcl')], 'syl2anc', '( %s -> ( K ^c -u Z ) e. CC )' % A0))
    # F : RR+ --> CC, F' : RR+ --> CC, RR _D F = F'
    d5, RHS, Ab, brp, c = dvF(w, A0, zc, kc)
    mb = lambda e: c.mem(e, 'CC')
    ff = w.s([mb(FB('b')), w.s([], 'eqid', '%s = %s' % (FM, FM))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, FM))
    gf = w.s([mb(FD('b')), w.s([], 'eqid', '%s = %s' % (FDM, FDM))], 'fmptd', '( %s -> %s : RR+ --> CC )' % (A0, FDM))
    dfg = w.s([w.s([kr, zc], 'jca', '( %s -> ( K e. RR /\\ Z e. CC ) )' % A0), w.inst('zl1fdv')], 'syl', '( %s -> ( RR _D %s ) = %s )' % (A0, FM, FDM))
    rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    ab1 = w.s([zc], 'abscld', '( %s -> ( abs ` Z ) e. RR )' % A0)
    zm1 = w.s([zc, a1(w, A0, 'ax-1cn', '1 e. CC')], 'subcld', '( %s -> ( Z - 1 ) e. CC )' % A0)
    ab2 = w.s([zm1], 'abscld', '( %s -> ( abs ` ( Z - 1 ) ) e. RR )' % A0)
    AA = '( ( abs ` Z ) x. ( abs ` ( Z - 1 ) ) )'
    aar = w.s([ab1, ab2], 'remulcld', '( %s -> %s e. RR )' % (A0, AA))
    aa0 = w.s([ab1, ab2, w.s([zc], 'absge0d', '( %s -> 0 <_ ( abs ` Z ) )' % A0), w.s([zm1], 'absge0d', '( %s -> 0 <_ ( abs ` ( Z - 1 ) ) )' % A0)],
              'mulge0d', '( %s -> 0 <_ %s )' % (A0, AA))
    EXP = '( -u %s - 1 )' % RZ
    kxr = w.s([w.s([krp, w.s([w.s([rz], 'renegcld', '( %s -> -u %s e. RR )' % (A0, RZ)), a1(w, A0, '1re', '1 e. RR')], 'resubcld', '( %s -> %s e. RR )' % (A0, EXP))],
                   'rpcxpcld', '( %s -> ( K ^c %s ) e. RR+ )' % (A0, EXP))], 'rpred', '( %s -> ( K ^c %s ) e. RR )' % (A0, EXP))
    mvr = w.s([aar, kxr], 'remulcld', '( %s -> %s e. RR )' % (A0, MV))
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
    tv, _ = mptval(w, At, 'b', 'RR+', FD('b'), 't', trp)
    Pt = '( t ^c %s )' % NZ1
    zt = w.s([zc], 'adantr', '( %s -> Z e. CC )' % At)
    ct = Closure(w, At, {'t': ('RR+', trp), 'Z': ('CC', zt), 'K': ('RR', krt)})
    mt = lambda e: ct.mem(e, 'CC')
    U = '( Z x. ( Z - 1 ) )'
    a_1 = E(w, At, 'absmuld', [mt(U), mt('( ( t - K ) x. %s )' % Pt)], '( abs ` %s )' % FD('t'), '( ( abs ` %s ) x. ( abs ` ( ( t - K ) x. %s ) ) )' % (U, Pt))
    a_2 = E(w, At, 'absmuld', [mt('Z'), mt('( Z - 1 )')], '( abs ` %s )' % U, AA)
    a_3 = E(w, At, 'absmuld', [mt('( t - K )'), mt(Pt)], '( abs ` ( ( t - K ) x. %s ) )' % Pt, '( ( abs ` ( t - K ) ) x. ( abs ` %s ) )' % Pt)
    a_4 = E(w, At, 'oveq12d', [a_2, a_3], '( ( abs ` %s ) x. ( abs ` ( ( t - K ) x. %s ) ) )' % (U, Pt), '( %s x. ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) )' % (AA, Pt))
    # | t - K | <_ 1
    tk0 = w.s([krt, tre, ktl], 'ltled', '( %s -> K <_ t )' % At)
    tkr = w.s([tre, krt], 'resubcld', '( %s -> ( t - K ) e. RR )' % At)
    tkp = w.s([tre, krt, w.inst('subge0')], 'syl2anc', '( %s -> ( 0 <_ ( t - K ) <-> K <_ t ) )' % At)
    tkg = w.s([tk0, tkp], 'mpbird', '( %s -> 0 <_ ( t - K ) )' % At)
    tabs = w.s([tkr, tkg], 'absidd', '( %s -> ( abs ` ( t - K ) ) = ( t - K ) )' % At)
    tk1b = w.s([tre, krt, a1(w, At, '1re', '1 e. RR'), w.inst('ltsubadd2')], 'syl3anc', '( %s -> ( ( t - K ) < 1 <-> t < ( K + 1 ) ) )' % At)
    tkl = w.s([w.s([tk1, tk1b], 'mpbird', '( %s -> ( t - K ) < 1 )' % At)], 'idi', '( %s -> ( t - K ) < 1 )' % At)
    tkle = w.s([tkr, a1(w, At, '1re', '1 e. RR'), tkl], 'ltled', '( %s -> ( t - K ) <_ 1 )' % At)
    tabl = w.s([tabs, tkle], 'eqbrtrd', '( %s -> ( abs ` ( t - K ) ) <_ 1 )' % At)
    # | t ^ ( -Z - 1 ) | = t ^ ( -Re Z - 1 ) <_ K ^ ( -Re Z - 1 )
    nzt = w.s([zt], 'negcld', '( %s -> -u Z e. CC )' % At)
    ab_p = w.s([trp, mt(NZ1), w.inst('abscxp')], 'syl2anc', '( %s -> ( abs ` %s ) = ( t ^c ( Re ` %s ) ) )' % (At, Pt, NZ1))
    re1 = w.s([w.s([nzt, a1(w, At, 'ax-1cn', '1 e. CC'), w.inst('resub')], 'syl2anc', '( %s -> ( Re ` %s ) = ( ( Re ` -u Z ) - ( Re ` 1 ) ) )' % (At, NZ1)),
               w.s([w.s([w.s([zt, w.inst('reneg')], 'syl', '( %s -> ( Re ` -u Z ) = -u %s )' % (At, RZ)), a1(w, At, 're1', '( Re ` 1 ) = 1')], 'oveq12d',
                        '( %s -> ( ( Re ` -u Z ) - ( Re ` 1 ) ) = %s )' % (At, EXP))], 'idi', '( %s -> ( ( Re ` -u Z ) - ( Re ` 1 ) ) = %s )' % (At, EXP))], 'eqtrd',
              '( %s -> ( Re ` %s ) = %s )' % (At, NZ1, EXP))
    ab_p2 = w.s([ab_p, w.s([re1], 'oveq2d', '( %s -> ( t ^c ( Re ` %s ) ) = ( t ^c %s ) )' % (At, NZ1, EXP))], 'eqtrd', '( %s -> ( abs ` %s ) = ( t ^c %s ) )' % (At, Pt, EXP))
    rzt = w.s([rz], 'adantr', '( %s -> %s e. RR )' % (At, RZ))
    rz1 = w.s([rzt, a1(w, At, '1re', '1 e. RR')], 'readdcld', '( %s -> ( %s + 1 ) e. RR )' % (At, RZ))
    rz10 = w.s([a1(w, At, '0re', '0 e. RR'), rz1, w.s([a1(w, At, '0re', '0 e. RR'), rzt, rz1, w.s([rzp], 'adantr', '( %s -> 0 < %s )' % (At, RZ)),
                                                        w.s([rzt], 'ltp1d', '( %s -> %s < ( %s + 1 ) )' % (At, RZ, RZ))], 'lttrd', '( %s -> 0 < ( %s + 1 ) )' % (At, RZ))],
               'ltled', '( %s -> 0 <_ ( %s + 1 ) )' % (At, RZ))
    anti = w.s([w.s([w.s([krp], 'adantr', '( %s -> K e. RR+ )' % At), trp, rz1], '3jca', '( %s -> ( K e. RR+ /\\ t e. RR+ /\\ ( %s + 1 ) e. RR ) )' % (At, RZ)),
                w.s([rz10, tk0], 'jca', '( %s -> ( 0 <_ ( %s + 1 ) /\\ K <_ t ) )' % (At, RZ)), w.inst('cxpnegle')], 'syl2anc',
               '( %s -> ( t ^c -u ( %s + 1 ) ) <_ ( K ^c -u ( %s + 1 ) ) )' % (At, RZ, RZ))
    ee = w.s([w.s([w.s([rzt], 'recnd', '( %s -> %s e. CC )' % (At, RZ)), a1(w, At, 'ax-1cn', '1 e. CC')], 'negdi2d', '( %s -> -u ( %s + 1 ) = ( -u %s - 1 ) )' % (At, RZ, RZ))],
             'idi', '( %s -> -u ( %s + 1 ) = %s )' % (At, RZ, EXP))
    anti2 = w.s([w.s([w.s([ee], 'oveq2d', '( %s -> ( t ^c -u ( %s + 1 ) ) = ( t ^c %s ) )' % (At, RZ, EXP)), anti], 'eqbrtrrd',
                     '( %s -> ( t ^c %s ) <_ ( K ^c -u ( %s + 1 ) ) )' % (At, EXP, RZ)),
                 w.s([ee], 'oveq2d', '( %s -> ( K ^c -u ( %s + 1 ) ) = ( K ^c %s ) )' % (At, RZ, EXP))], 'breqtrd', '( %s -> ( t ^c %s ) <_ ( K ^c %s ) )' % (At, EXP, EXP))
    pbl = w.s([ab_p2, anti2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( K ^c %s ) )' % (At, Pt, EXP))
    kxrt = w.s([kxr], 'adantr', '( %s -> ( K ^c %s ) e. RR )' % (At, EXP))
    prd = w.s([w.s([mt('( t - K )')], 'abscld', '( %s -> ( abs ` ( t - K ) ) e. RR )' % At), a1(w, At, '1re', '1 e. RR'),
               w.s([mt(Pt)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, Pt)), kxrt,
               w.s([mt('( t - K )')], 'absge0d', '( %s -> 0 <_ ( abs ` ( t - K ) ) )' % At), w.s([mt(Pt)], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (At, Pt)),
               tabl, pbl], 'lemul12ad',
              '( %s -> ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) <_ ( 1 x. ( K ^c %s ) ) )' % (At, Pt, EXP))
    prd2 = w.s([prd, w.s([w.s([kxrt], 'recnd', '( %s -> ( K ^c %s ) e. CC )' % (At, EXP))], 'mullidd', '( %s -> ( 1 x. ( K ^c %s ) ) = ( K ^c %s ) )' % (At, EXP, EXP))],
               'breqtrd', '( %s -> ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) <_ ( K ^c %s ) )' % (At, Pt, EXP))
    l5 = w.s([w.s([w.s([mt('( t - K )')], 'abscld', '( %s -> ( abs ` ( t - K ) ) e. RR )' % At), w.s([mt(Pt)], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (At, Pt))],
                  'remulcld', '( %s -> ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) e. RR )' % (At, Pt)), kxrt, w.s([aar], 'adantr', '( %s -> %s e. RR )' % (At, AA)),
              w.s([aa0], 'adantr', '( %s -> 0 <_ %s )' % (At, AA)), prd2], 'lemul2ad',
             '( %s -> ( %s x. ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) ) <_ %s )' % (At, AA, Pt, MV))
    fdv = w.s([w.s([tv], 'fveq2d', '( %s -> ( abs ` ( %s ` t ) ) = ( abs ` %s ) )' % (At, FDM, FD('t'))), a_1, a_4], '3eqtrd',
              '( %s -> ( abs ` ( %s ` t ) ) = ( %s x. ( ( abs ` ( t - K ) ) x. ( abs ` %s ) ) ) )' % (At, FDM, AA, Pt))
    bt = w.s([fdv, l5], 'eqbrtrd', '( %s -> ( abs ` ( %s ` t ) ) <_ %s )' % (At, FDM, MV))
    bnd = w.s([bt], 'ralrimiva', '( %s -> A. t e. %s ( abs ` ( %s ` t ) ) <_ %s )' % (A0, IOO, FDM, MV))
    lip = w.s([w.s([w.s([ff, gf, dfg], '3jca', '( %s -> ( %s : RR+ --> CC /\\ %s : RR+ --> CC /\\ ( RR _D %s ) = %s ) )' % (A0, FM, FDM, FM, FDM)),
                    w.s([krp, mvr, bnd], '3jca', '( %s -> ( K e. RR+ /\\ %s e. RR /\\ A. t e. %s ( abs ` ( %s ` t ) ) <_ %s ) )' % (A0, MV, IOO, FDM, MV))], 'jca',
                   '( %s -> ( ( %s : RR+ --> CC /\\ %s : RR+ --> CC /\\ ( RR _D %s ) = %s ) /\\ ( K e. RR+ /\\ %s e. RR /\\ A. t e. %s ( abs ` ( %s ` t ) ) <_ %s ) ) )'
                   % (A0, FM, FDM, FM, FDM, MV, IOO, FDM, MV)), w.inst('zl1lip')], 'syl',
              '( %s -> ( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) ) <_ %s )' % (A0, FM, FM, MV))
    # the values F ( K ), F ( K + 1 )
    k1n = w.s([kn, w.inst('peano2nn')], 'syl', '( %s -> ( K + 1 ) e. NN )' % A0)
    vK, FK = mptval(w, A0, 'b', 'RR+', FB('b'), 'K', krp)
    vK1, FK1 = mptval(w, A0, 'b', 'RR+', FB('b'), '( K + 1 )', w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0))
    p = '( K ^c -u Z )'; q = '( ( K + 1 ) ^c -u Z )'
    kne = w.s([krp], 'rpne0d', '( %s -> K =/= 0 )' % A0)
    k1c = w.s([k1n], 'nncnd', '( %s -> ( K + 1 ) e. CC )' % A0)
    k1ne = w.s([k1n], 'nnne0d', '( %s -> ( K + 1 ) =/= 0 )' % A0)
    pk = pwm(w, A0, 'K', kc, kne, zc)
    pk1 = pwm(w, A0, '( K + 1 )', k1c, k1ne, zc)
    FKs = '( ( %s x. %s ) - ( Z x. ( %s x. K ) ) )' % (ZK, p, p)
    FK1s = '( ( %s x. %s ) - ( Z x. ( %s x. ( K + 1 ) ) ) )' % (ZK, q, q)
    r1_ = E(w, A0, 'oveq2d', [E(w, A0, 'oveq2d', [pk], '( Z x. ( K ^c ( 1 - Z ) ) )', '( Z x. ( %s x. K ) )' % p)], FK, FKs)
    r2_ = E(w, A0, 'oveq2d', [E(w, A0, 'oveq2d', [pk1], '( Z x. ( ( K + 1 ) ^c ( 1 - Z ) ) )', '( Z x. ( %s x. ( K + 1 ) ) )' % q)], FK1, FK1s)
    alg = w.s([w.s([w.s([zc, kc], 'jca', '( %s -> ( Z e. CC /\\ K e. CC ) )' % A0), w.s([c0.mem(p, 'CC'), c0.mem(q, 'CC')], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, p, q))],
                   'jca', '( %s -> ( ( Z e. CC /\\ K e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, p, q)), w.inst('zl1alg2')], 'syl',
              '( %s -> ( %s = -u ( K x. %s ) /\\ %s = -u ( ( K + Z ) x. %s ) ) )' % (A0, FKs, p, FK1s, q))
    a1_ = w.s([alg], 'simpld', '( %s -> %s = -u ( K x. %s ) )' % (A0, FKs, p))
    a2_ = w.s([alg], 'simprd', '( %s -> %s = -u ( ( K + Z ) x. %s ) )' % (A0, FK1s, q))
    FKv = chain(w, A0, ['( %s ` K )' % FM, FK, FKs, '-u ( K x. %s )' % p], [vK, r1_, a1_])
    FK1v = chain(w, A0, ['( %s ` ( K + 1 ) )' % FM, FK1, FK1s, '-u ( ( K + Z ) x. %s )' % q], [vK1, r2_, a2_])
    df = E(w, A0, 'oveq12d', [FKv, FK1v], '( ( %s ` K ) - ( %s ` ( K + 1 ) ) )' % (FM, FM), '( -u ( K x. %s ) - -u ( ( K + Z ) x. %s ) )' % (p, q))
    ng = E(w, A0, 'neg2subd', [c0.mem('( K x. %s )' % p, 'CC'), c0.mem('( ( K + Z ) x. %s )' % q, 'CC')],
           '( -u ( K x. %s ) - -u ( ( K + Z ) x. %s ) )' % (p, q), HT('K', 'Z'))
    htv = chain(w, A0, ['( ( %s ` K ) - ( %s ` ( K + 1 ) ) )' % (FM, FM), '( -u ( K x. %s ) - -u ( ( K + Z ) x. %s ) )' % (p, q), HT('K', 'Z')], [df, ng])
    fkc1 = w.s([ff, krp], 'ffvelcdmd', '( %s -> ( %s ` K ) e. CC )' % (A0, FM))
    fkc2 = w.s([ff, w.s([k1n], 'nnrpd', '( %s -> ( K + 1 ) e. RR+ )' % A0)], 'ffvelcdmd', '( %s -> ( %s ` ( K + 1 ) ) e. CC )' % (A0, FM))
    sw = E(w, A0, 'abssubd', [fkc1, fkc2], '( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) )' % (FM, FM), '( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) )' % (FM, FM))
    habs = w.s([htv], 'fveq2d', '( %s -> ( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) ) = ( abs ` %s ) )' % (A0, FM, FM, HT('K', 'Z')))
    eqa = chain(w, A0, ['( abs ` %s )' % HT('K', 'Z'), '( abs ` ( ( %s ` K ) - ( %s ` ( K + 1 ) ) ) )' % (FM, FM), '( abs ` ( ( %s ` ( K + 1 ) ) - ( %s ` K ) ) )' % (FM, FM)],
                [('r', habs), sw])
    w.qed([eqa, lip], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, HT('K', 'Z'), MV))
    go(w)
