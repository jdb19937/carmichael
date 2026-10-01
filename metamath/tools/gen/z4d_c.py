"""Sortie z4d, section B: numerics (pile165, lsexpb, lsnum)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tm import W
import lin
lin.FASTPATH = True
from lin import linarith, lineq, nlinarith
from z4dlib import STATEMENTS as S, RHO, D4, GW
from z4d_a import mk, a1


def pile165():
    w = W('pile165', 'An upper bound for pi from set.mm main: sin ( 4 / 5 ) >_ 17 / 24 (mvsinlb), so '
          'cos ( 8 / 5 ) < 0 and 8 / 5 is not below pi / 2 (cosq14gt0).  Lean Real.pi_lt_d4 replacement.')
    T = 'T.'
    s = mk(w, T)
    Y = '( 4 / 5 )'
    SY = '( sin ` %s )' % Y
    yre = s([w.s([w.s([], '4re', '4 e. RR'), w.s([], '5re', '5 e. RR'), w.s([], '5ne0', '5 =/= 0')], 'redivcli', '%s e. RR' % Y)], 'a1i', '%s e. RR' % Y)
    ypos = linarith(w, T, [], '0 < %s' % Y, leaves={})
    y2 = linarith(w, T, [], '%s <_ 2' % Y, leaves={})
    LB = '( %s x. ( 1 - ( ( ; 1 7 x. ( %s ^ 2 ) ) / ; 9 6 ) ) )' % (Y, Y)
    lb = s([yre, ypos, y2, w.inst('mvsinlb')], 'syl3anc', '%s <_ %s' % (LB, SY))
    K = '( ; 1 7 / ; 2 4 )'
    k1 = w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '7nn0', '7 e. NN0')], 'deccl', '; 1 7 e. NN0')], 'nn0rei', '; 1 7 e. RR')
    k24 = w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '4nn', '4 e. NN')], 'decnncl', '; 2 4 e. NN')
    kr = s([w.s([k1, w.s([k24], 'nnrei', '; 2 4 e. RR'), w.s([k24], 'nnne0i', '; 2 4 =/= 0')], 'redivcli', '%s e. RR' % K)], 'a1i', '%s e. RR' % K)
    syr = s([yre], 'resincld', '%s e. RR' % SY)
    ks = linarith(w, T, [lb], '%s <_ %s' % (K, SY), leaves={SY: syr})
    kpos = linarith(w, T, [], '0 <_ %s' % K, leaves={})
    sq = s([s([kr, kpos], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (K, K)), s([syr, ks], 'jca', '( %s e. RR /\\ %s <_ %s )' % (SY, K, SY)),
            w.inst('le2sq2')], 'syl2anc', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (K, SY))
    S2 = '( %s ^ 2 )' % SY
    s2r = s([syr], 'resqcld', '%s e. RR' % S2)
    Z = '( 8 / 5 )'
    CZ = '( cos ` %s )' % Z
    c2 = s([s([yre], 'recnd', '%s e. CC' % Y), w.inst('cos2tsin')], 'syl', '( cos ` ( 2 x. %s ) ) = ( 1 - ( 2 x. %s ) )' % (Y, S2))
    zq = lineq(w, T, '( 2 x. %s )' % Y, Z, leaves={})
    c3 = s([s([zq], 'fveq2d', '( cos ` ( 2 x. %s ) ) = %s' % (Y, CZ)), c2], 'eqtr3d', '%s = ( 1 - ( 2 x. %s ) )' % (CZ, S2))
    zre = s([w.s([w.s([], '8re', '8 e. RR'), w.s([], '5re', '5 e. RR'), w.s([], '5ne0', '5 =/= 0')], 'redivcli', '%s e. RR' % Z)], 'a1i', '%s e. RR' % Z)
    czr = s([zre], 'recoscld', '%s e. RR' % CZ)
    cneg = linarith(w, T, [c3, sq], '%s < 0' % CZ, leaves={S2: s2r, CZ: czr})
    # if 8 / 5 < pi / 2 then cos ( 8 / 5 ) > 0
    PSI = '%s < ( _pi / 2 )' % Z
    A = '( T. /\\ %s )' % PSI
    a = mk(w, A)
    P2 = '( _pi / 2 )'
    p2r = w.s([w.s([], 'halfpire', '%s e. RR' % P2)], 'a1i', '( %s -> %s e. RR )' % (A, P2))
    I = '( -u %s (,) %s )' % (P2, P2)
    ael = a([a([a([p2r], 'renegcld', '-u %s e. RR' % P2)], 'rexrd', '-u %s e. RR*' % P2), a([p2r], 'rexrd', '%s e. RR*' % P2),
             w.inst('elioo2')], 'syl2anc', '( %s e. %s <-> ( %s e. RR /\\ -u %s < %s /\\ %s < %s ) )' % (Z, I, Z, P2, Z, Z, P2))
    azr = a([zre], 'adantr', '%s e. RR' % Z)
    pir = w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A)
    pip = w.s([w.s([], 'pipos', '0 < _pi')], 'a1i', '( %s -> 0 < _pi )' % A)
    lo = linarith(w, A, [pip], '-u %s < %s' % (P2, Z), leaves={'_pi': pir})
    zin = a([ael, a([azr, lo, a([], 'simpr', PSI)], '3jca', '( %s e. RR /\\ -u %s < %s /\\ %s < %s )' % (Z, P2, Z, Z, P2))], 'mpbird',
            '%s e. %s' % (Z, I))
    cp = a([zin, w.inst('cosq14gt0')], 'syl', '0 < %s' % CZ)
    cn2 = a([a([cneg], 'adantr', '%s < 0' % CZ)], 'ltnsymd', '-. 0 < %s' % CZ)
    npsi = s([cp, cn2], 'pm2.65da', '-. %s' % PSI)
    pir0 = w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( T. -> _pi e. RR )')
    le = s([s([s([w.s([], 'halfpire', '%s e. RR' % P2)], 'a1i', '%s e. RR' % P2), zre], 'lenltd', '( %s <_ %s <-> -. %s )' % (P2, Z, PSI)), npsi],
           'mpbird', '%s <_ %s' % (P2, Z))
    fin = linarith(w, T, [le], '_pi <_ ( ; 1 6 / 5 )', leaves={'_pi': pir0})
    w.qed([fin], 'mptru', S['pile165'])
    return w

def lsexpb():
    from mvlib import ringeqp
    from cl import Closure
    w = W('lsexpb', 'The exponential-ratio numeric: 24 pi T ( exp ( pi / 4 T ) - 1 ) <_ 95 for 1 <_ T, from the '
          'cubic Taylor polynomial with the quartic tail bound (ef4p, eftlub) and pi <_ 16 / 5 (Lean exp_ratio_bound, 91).')
    A0 = '( T e. RR /\\ 1 <_ T )'
    s = mk(w, A0)
    tre = s([], 'simpl', 'T e. RR')
    t1 = s([], 'simpr', '1 <_ T')
    tpos = linarith(w, A0, [t1], '0 < T', leaves={'T': tre})
    trp = s([tre, tpos], 'elrpd', 'T e. RR+')
    pir = a1(w, A0, 'pire', '_pi e. RR')
    pirp = a1(w, A0, 'pirp', '_pi e. RR+')
    pic = a1(w, A0, 'picn', '_pi e. CC')
    pile = a1(w, A0, 'pile165', '_pi <_ ( ; 1 6 / 5 )')
    pige = s([pirp], 'rpge0d', '0 <_ _pi')
    U = D4
    F4 = '( 4 x. T )'
    four = a1(w, A0, '4re', '4 e. RR')
    f4rp = s([a1(w, A0, '4rp', '4 e. RR+'), trp], 'rpmulcld', '%s e. RR+' % F4)
    urp = s([pirp, f4rp], 'rpdivcld', '%s e. RR+' % U)
    ure = s([urp], 'rpred', '%s e. RR' % U)
    uge = s([urp], 'rpge0d', '0 <_ %s' % U)
    uc = s([ure], 'recnd', '%s e. CC' % U)
    tc = s([tre], 'recnd', 'T e. CC')
    tne = s([trp], 'rpne0d', 'T =/= 0')
    P4 = '( _pi / 4 )'
    fc = a1(w, A0, '4cn', '4 e. CC')
    fne = a1(w, A0, '4ne0', '4 =/= 0')
    dd = s([pic, fc, tc, fne, tne], 'divdiv1d', '( %s / T ) = %s' % (P4, U))
    p4c = s([pic, fc, fne], 'divcld', '%s e. CC' % P4)
    tu0 = s([p4c, tc, tne], 'divcan2d', '( T x. ( %s / T ) ) = %s' % (P4, P4))
    tu = s([s([dd], 'oveq2d', '( T x. ( %s / T ) ) = ( T x. %s )' % (P4, U)), tu0], 'eqtr3d', '( T x. %s ) = %s' % (U, P4))
    ut = s([s([ure, tre], 'jca', '( %s e. RR /\\ T e. RR )' % U), s([uge, t1], 'jca', '( 0 <_ %s /\\ 1 <_ T )' % U),
            w.inst('lemulge11')], 'syl2anc', '%s <_ ( %s x. T )' % (U, U))
    utc = s([uc, tc], 'mulcomd', '( %s x. T ) = ( T x. %s )' % (U, U))
    lv = {U: ure, '_pi': pir, 'T': tre}
    ule = linarith(w, A0, [ut, utc, tu, pile], '%s <_ ( 4 / 5 )' % U, leaves=lv, atoms=[U])
    AU = '( abs ` %s )' % U
    au = s([ure, uge], 'absidd', '%s = %s' % (AU, U))
    au1 = s([au, linarith(w, A0, [ule], '%s <_ 1' % U, leaves=lv, atoms=[U])], 'eqbrtrd', '%s <_ 1' % AU)
    FD = '( n e. NN0 |-> ( ( %s ^ n ) / ( ! ` n ) ) )' % U
    GD = '( n e. NN0 |-> ( ( %s ^ n ) / ( ! ` n ) ) )' % AU
    HD = '( n e. NN0 |-> ( ( ( %s ^ 4 ) / ( ! ` 4 ) ) x. ( ( 1 / ( 4 + 1 ) ) ^ n ) ) )' % AU
    R = 'sum_ k e. ( ZZ>= ` 4 ) ( %s ` k )' % FD
    fq = w.s([], 'eqid', '%s = %s' % (FD, FD))
    E = '( exp ` %s )' % U
    PT = '( ( ( ( 1 + %s ) + ( ( %s ^ 2 ) / 2 ) ) + ( ( %s ^ 3 ) / 6 ) ) + %s )' % (U, U, U, R)
    e4 = s([uc, w.s([fq], 'ef4p', '( %s e. CC -> %s = %s )' % (U, E, PT))], 'syl', '%s = %s' % (E, PT))
    tl = s([w.s([], 'eqid', '%s = %s' % (GD, GD)), w.s([], 'eqid', '%s = %s' % (HD, HD)), fq,
            a1(w, A0, '4nn', '4 e. NN'), uc, au1], 'eftlub',
           '( abs ` %s ) <_ ( ( %s ^ 4 ) x. ( ( 4 + 1 ) / ( ( ! ` 4 ) x. 4 ) ) )' % (R, AU))
    rre = s([ure, a1(w, A0, '4nn0', '4 e. NN0'), w.s([fq], 'reeftlcl', '( ( %s e. RR /\\ 4 e. NN0 ) -> %s e. RR )' % (U, R))], 'syl2anc', '%s e. RR' % R)
    rab = s([rre], 'leabsd', '%s <_ ( abs ` %s )' % (R, R))
    import num
    m96 = num.mul_nat(w, 24, 4)
    f4q = s([a1(w, A0, '4p1e5', '( 4 + 1 ) = 5'),
             s([s([a1(w, A0, 'fac4', '( ! ` 4 ) = ; 2 4')], 'oveq1d', '( ( ! ` 4 ) x. 4 ) = ( ; 2 4 x. 4 )'),
                s([m96], 'a1i', '( ; 2 4 x. 4 ) = ; 9 6')], 'eqtrd', '( ( ! ` 4 ) x. 4 ) = ; 9 6')], 'oveq12d',
            '( ( 4 + 1 ) / ( ( ! ` 4 ) x. 4 ) ) = ( 5 / ; 9 6 )')
    tl2 = s([tl, s([s([au], 'oveq1d', '( %s ^ 4 ) = ( %s ^ 4 )' % (AU, U)), f4q], 'oveq12d',
                   '( ( %s ^ 4 ) x. ( ( 4 + 1 ) / ( ( ! ` 4 ) x. 4 ) ) ) = ( ( %s ^ 4 ) x. ( 5 / ; 9 6 ) )' % (AU, U))],
            'breqtrd', '( abs ` %s ) <_ ( ( %s ^ 4 ) x. ( 5 / ; 9 6 ) )' % (R, U))
    ere = s([ure], 'reefcld', '%s e. RR' % E)
    arre = s([s([rre], 'recnd', '%s e. CC' % R)], 'abscld', '( abs ` %s ) e. RR' % R)
    PU = '( ( ( 1 + ( %s / 2 ) ) + ( ( %s ^ 2 ) / 6 ) ) + ( ( 5 x. ( %s ^ 3 ) ) / ; 9 6 ) )' % (U, U, U)
    lv2 = dict(lv); lv2[E] = ere; lv2[R] = rre; lv2['( abs ` %s )' % R] = arre
    U4 = '( %s ^ 4 )' % U
    lv2['( %s ^ 2 )' % U] = s([ure], 'resqcld', '( %s ^ 2 ) e. RR' % U)
    lv2['( %s ^ 3 )' % U] = s([ure, a1(w, A0, '3nn0', '3 e. NN0')], 'reexpcld', '( %s ^ 3 ) e. RR' % U)
    lv2[U4] = s([ure, a1(w, A0, '4nn0', '4 e. NN0')], 'reexpcld', '%s e. RR' % U4)
    POLY = '( ( ( %s + ( ( %s ^ 2 ) / 2 ) ) + ( ( %s ^ 3 ) / 6 ) ) + ( ( 5 x. %s ) / ; 9 6 ) )' % (U, U, U, U4)
    e0 = linarith(w, A0, [e4, rab, tl2], '( %s - 1 ) <_ %s' % (E, POLY), leaves=lv2,
                  atoms=[U, E, R, '( abs ` %s )' % R, '( %s ^ 2 )' % U, '( %s ^ 3 )' % U, U4])
    clp = Closure(w, A0, {U: ure})
    pq = ringeqp(w, A0, POLY, '( %s x. %s )' % (U, PU), clp)
    e1 = s([e0, pq], 'breqtrd', '( %s - 1 ) <_ ( %s x. %s )' % (E, U, PU))
    K45 = '( 4 / 5 )'
    k45 = s([w.s([w.s([], '4re', '4 e. RR'), w.s([], '5re', '5 e. RR'), w.s([], '5ne0', '5 =/= 0')], 'redivcli', '%s e. RR' % K45)], 'a1i', '%s e. RR' % K45)
    def pw(n, nn0):
        return s([s([ure, k45, a1(w, A0, nn0, '%s e. NN0' % n)], '3jca', '( %s e. RR /\\ %s e. RR /\\ %s e. NN0 )' % (U, K45, n)),
                  s([uge, ule], 'jca', '( 0 <_ %s /\\ %s <_ %s )' % (U, U, K45)), w.inst('leexp1a')], 'syl2anc',
                 '( %s ^ %s ) <_ ( %s ^ %s )' % (U, n, K45, n))
    u2 = pw('2', '2nn0'); u3 = pw('3', '3nn0')
    g2 = s([ure, a1(w, A0, '2nn0', '2 e. NN0'), uge], 'expge0d', '0 <_ ( %s ^ 2 )' % U)
    g3 = s([ure, a1(w, A0, '3nn0', '3 e. NN0'), uge], 'expge0d', '0 <_ ( %s ^ 3 )' % U)
    lv3 = dict(lv)
    lv3['( %s ^ 2 )' % U] = s([ure], 'resqcld', '( %s ^ 2 ) e. RR' % U)
    lv3['( %s ^ 3 )' % U] = s([ure, a1(w, A0, '3nn0', '3 e. NN0')], 'reexpcld', '( %s ^ 3 ) e. RR' % U)
    at3 = [U, '( %s ^ 2 )' % U, '( %s ^ 3 )' % U]
    pu = linarith(w, A0, [u2, u3, ule], '%s <_ ( ; 2 3 / ; 1 5 )' % PU, leaves=lv3, atoms=at3)
    pu0 = linarith(w, A0, [uge, g2, g3], '0 <_ %s' % PU, leaves=lv3, atoms=at3)
    pure = s([s([s([a1(w, A0, '1re', '1 e. RR'), s([ure], 'rehalfcld', '( %s / 2 ) e. RR' % U)], 'readdcld',
                    '( 1 + ( %s / 2 ) ) e. RR' % U),
                  s([lv3['( %s ^ 2 )' % U], a1(w, A0, '6re', '6 e. RR'), a1(w, A0, '6ne0', '6 =/= 0')], 'redivcld', '( ( %s ^ 2 ) / 6 ) e. RR' % U)],
                 'readdcld', '( ( 1 + ( %s / 2 ) ) + ( ( %s ^ 2 ) / 6 ) ) e. RR' % (U, U)),
              s([s([a1(w, A0, '5re', '5 e. RR'), lv3['( %s ^ 3 )' % U]], 'remulcld', '( 5 x. ( %s ^ 3 ) ) e. RR' % U),
                 s([w.s([w.s([w.s([], '9nn0', '9 e. NN0'), w.s([], '6nn', '6 e. NN')], 'decnncl', '; 9 6 e. NN')], 'nnrei', '; 9 6 e. RR')], 'a1i', '; 9 6 e. RR'),
                 s([w.s([w.s([w.s([], '9nn0', '9 e. NN0'), w.s([], '6nn', '6 e. NN')], 'decnncl', '; 9 6 e. NN')], 'nnne0i', '; 9 6 =/= 0')], 'a1i', '; 9 6 =/= 0')],
                'redivcld', '( ( 5 x. ( %s ^ 3 ) ) / ; 9 6 ) e. RR' % U)], 'readdcld', '%s e. RR' % PU)
    C24 = '( ( ; 2 4 x. _pi ) x. T )'
    n24 = s([w.s([w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '4nn', '4 e. NN')], 'decnncl', '; 2 4 e. NN')], 'nnrei', '; 2 4 e. RR')], 'a1i', '; 2 4 e. RR')
    c24r = s([s([n24, pir], 'remulcld', '( ; 2 4 x. _pi ) e. RR'), tre], 'remulcld', '%s e. RR' % C24)
    c24p = s([s([s([w.s([w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '4nn', '4 e. NN')], 'decnncl', '; 2 4 e. NN'), w.inst('nnrp')], 'ax-mp', '; 2 4 e. RR+')], 'a1i', '; 2 4 e. RR+'), pirp],
                 'rpmulcld', '( ; 2 4 x. _pi ) e. RR+'), trp], 'rpmulcld', '%s e. RR+' % C24)
    c24g = s([c24p], 'rpge0d', '0 <_ %s' % C24)
    UP = '( %s x. %s )' % (U, PU)
    upr = s([ure, pure], 'remulcld', '%s e. RR' % UP)
    rhoR = s([ere, a1(w, A0, '1re', '1 e. RR')], 'resubcld', '%s e. RR' % RHO)
    m1 = s([rhoR, upr, c24r, c24g, e1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (C24, RHO, C24, UP))
    # ( C24 x. ( U x. PU ) ) = ( ( 6 x. ( _pi ^ 2 ) ) x. PU )
    P6 = '( 6 x. ( _pi ^ 2 ) )'
    c24c = s([c24r], 'recnd', '%s e. CC' % C24)
    puc = s([pure], 'recnd', '%s e. CC' % PU)
    q1 = s([c24c, uc, puc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (C24, U, PU, C24, UP))
    c24pc = s([s([n24, pir], 'remulcld', '( ; 2 4 x. _pi ) e. RR')], 'recnd', '( ; 2 4 x. _pi ) e. CC')
    q2 = s([c24pc, tc, uc], 'mulassd', '( %s x. %s ) = ( ( ; 2 4 x. _pi ) x. ( T x. %s ) )' % (C24, U, U))
    q3 = s([q2, s([tu], 'oveq2d', '( ( ; 2 4 x. _pi ) x. ( T x. %s ) ) = ( ( ; 2 4 x. _pi ) x. %s )' % (U, P4))], 'eqtrd',
           '( %s x. %s ) = ( ( ; 2 4 x. _pi ) x. %s )' % (C24, U, P4))
    cl = Closure(w, A0, {'_pi': pir})
    q4 = ringeqp(w, A0, '( ( ; 2 4 x. _pi ) x. %s )' % P4, P6, cl)
    q5 = s([q3, q4], 'eqtrd', '( %s x. %s ) = %s' % (C24, U, P6))
    q6 = s([q1, s([q5], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (C24, U, PU, P6, PU))], 'eqtr3d',
           '( %s x. %s ) = ( %s x. %s )' % (C24, UP, P6, PU))
    B6 = '( 6 x. ( ( ; 1 6 / 5 ) ^ 2 ) )'
    k165 = s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '6nn0', '6 e. NN0')], 'deccl', '; 1 6 e. NN0')], 'nn0rei', '; 1 6 e. RR'),
                   w.s([], '5re', '5 e. RR'), w.s([], '5ne0', '5 =/= 0')], 'redivcli', '( ; 1 6 / 5 ) e. RR')], 'a1i', '( ; 1 6 / 5 ) e. RR')
    pi2 = s([s([pir, pige], 'jca', '( _pi e. RR /\\ 0 <_ _pi )'), s([k165, pile], 'jca', '( ( ; 1 6 / 5 ) e. RR /\\ _pi <_ ( ; 1 6 / 5 ) )'),
             w.inst('le2sq2')], 'syl2anc', '( _pi ^ 2 ) <_ ( ( ; 1 6 / 5 ) ^ 2 )')
    lvp = {'( _pi ^ 2 )': s([pir], 'resqcld', '( _pi ^ 2 ) e. RR')}
    p6 = linarith(w, A0, [pi2], '%s <_ %s' % (P6, B6), leaves=lvp, atoms=['( _pi ^ 2 )'])
    p6r = s([a1(w, A0, '6re', '6 e. RR'), lvp['( _pi ^ 2 )']], 'remulcld', '%s e. RR' % P6)
    b6r = s([a1(w, A0, '6re', '6 e. RR'), s([k165], 'resqcld', '( ( ; 1 6 / 5 ) ^ 2 ) e. RR')], 'remulcld', '%s e. RR' % B6)
    m2 = s([p6r, b6r, pure, pu0, p6], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (P6, PU, B6, PU))
    K23 = '( ; 2 3 / ; 1 5 )'
    n23 = w.s([w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '3nn0', '3 e. NN0')], 'deccl', '; 2 3 e. NN0')], 'nn0rei', '; 2 3 e. RR')
    n15 = w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '5nn', '5 e. NN')], 'decnncl', '; 1 5 e. NN')
    k23 = s([w.s([n23, w.s([n15], 'nnrei', '; 1 5 e. RR'), w.s([n15], 'nnne0i', '; 1 5 =/= 0')], 'redivcli', '%s e. RR' % K23)], 'a1i', '%s e. RR' % K23)
    b6g = linarith(w, A0, [], '0 <_ %s' % B6, leaves={})
    m3 = s([pure, k23, b6r, b6g, pu], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (B6, PU, B6, K23))
    m4 = linarith(w, A0, [], '( %s x. %s ) <_ ; 9 5' % (B6, K23), leaves={})
    X = '( %s x. %s )' % (C24, RHO)
    Y2 = '( %s x. %s )' % (P6, PU)
    Y3 = '( %s x. %s )' % (B6, PU)
    Y4 = '( %s x. %s )' % (B6, K23)
    xr = s([c24r, rhoR], 'remulcld', '%s e. RR' % X)
    y2r = s([p6r, pure], 'remulcld', '%s e. RR' % Y2)
    y3r = s([b6r, pure], 'remulcld', '%s e. RR' % Y3)
    y4r = s([b6r, k23], 'remulcld', '%s e. RR' % Y4)
    x2 = s([m1, q6], 'breqtrd', '%s <_ %s' % (X, Y2))
    x3 = s([xr, y2r, y3r, x2, m2], 'letrd', '%s <_ %s' % (X, Y3))
    x4 = s([xr, y3r, y4r, x3, m3], 'letrd', '%s <_ %s' % (X, Y4))
    w.qed([xr, y4r, s([w.s([w.s([w.s([], '9nn0', '9 e. NN0'), w.s([], '5nn0', '5 e. NN0')], 'deccl', '; 9 5 e. NN0')], 'nn0rei', '; 9 5 e. RR')], 'a1i', '; 9 5 e. RR'),
           x4, m4], 'letrd', S['lsexpb'])
    return w


def lsnum():
    w = W('lsnum', 'The per-n numeric of presifted_large_sieve: 12 T ( Q^2 + 2 pi RHO N + 4 pi ) B <_ '
          '100 ( N + Q^2 T ) B (Lean hnum, with 95 for exp_ratio_bound and pi <_ 16 / 5).')
    A0 = '( ( ( Q e. RR /\\ 2 <_ Q ) /\\ ( T e. RR /\\ 1 <_ T ) ) /\\ ( N e. NN /\\ B e. RR /\\ 0 <_ B ) )'
    s = mk(w, A0)
    qre = s([], 'simplll', 'Q e. RR')
    q2 = s([], 'simpllr', '2 <_ Q')
    tt = s([], 'simplr', '( T e. RR /\\ 1 <_ T )')
    tre = s([tt], 'simpld', 'T e. RR')
    t1 = s([tt], 'simprd', '1 <_ T')
    nnn = s([], 'simpr1', 'N e. NN')
    nre = s([nnn], 'nnred', 'N e. RR')
    bre = s([], 'simpr2', 'B e. RR')
    bge = s([], 'simpr3', '0 <_ B')
    pir = a1(w, A0, 'pire', '_pi e. RR')
    pile = a1(w, A0, 'pile165', '_pi <_ ( ; 1 6 / 5 )')
    E = '( exp ` %s )' % D4
    tpos = linarith(w, A0, [t1], '0 < T', leaves={'T': tre})
    ere = s([s([pir, s([a1(w, A0, '4re', '4 e. RR'), tre], 'remulcld', '( 4 x. T ) e. RR'),
                s([linarith(w, A0, [tpos], '0 < ( 4 x. T )', leaves={'T': tre})], 'gt0ne0d', '( 4 x. T ) =/= 0')], 'redivcld', '%s e. RR' % D4)],
            'reefcld', '%s e. RR' % E)
    C24 = '( ( ; 2 4 x. _pi ) x. T )'
    eb = s([tt, w.inst('lsexpb')], 'syl', '( %s x. %s ) <_ ; 9 5' % (C24, RHO))
    lv = {'Q': qre, 'T': tre, 'N': nre, '_pi': pir, E: ere}
    at = [E]
    ngt = s([nnn], 'nnge1d', '1 <_ N') if False else None
    n0 = s([nre, s([nnn], 'nngt0d', '0 < N')], 'ltled', '0 <_ N')
    t0 = linarith(w, A0, [t1], '0 <_ T', leaves={'T': tre})
    rhr = s([ere, a1(w, A0, '1re', '1 e. RR')], 'resubcld', '%s e. RR' % RHO)
    c24r = s([s([s([w.s([w.s([w.s([], '2nn0', '2 e. NN0'), w.s([], '4nn', '4 e. NN')], 'decnncl', '; 2 4 e. NN')], 'nnrei', '; 2 4 e. RR')], 'a1i', '; 2 4 e. RR'), pir],
                'remulcld', '( ; 2 4 x. _pi ) e. RR'), tre], 'remulcld', '%s e. RR' % C24)
    f1 = s([s([c24r, rhr], 'remulcld', '( %s x. %s ) e. RR' % (C24, RHO)),
            s([w.s([w.s([w.s([], '9nn0', '9 e. NN0'), w.s([], '5nn0', '5 e. NN0')], 'deccl', '; 9 5 e. NN0')], 'nn0rei', '; 9 5 e. RR')], 'a1i', '; 9 5 e. RR'),
            nre, n0, eb], 'lemul1ad', '( ( %s x. %s ) x. N ) <_ ( ; 9 5 x. N )' % (C24, RHO))
    k165 = s([w.s([w.s([w.s([w.s([], '1nn0', '1 e. NN0'), w.s([], '6nn0', '6 e. NN0')], 'deccl', '; 1 6 e. NN0')], 'nn0rei', '; 1 6 e. RR'),
                   w.s([], '5re', '5 e. RR'), w.s([], '5ne0', '5 =/= 0')], 'redivcli', '( ; 1 6 / 5 ) e. RR')], 'a1i', '( ; 1 6 / 5 ) e. RR')
    f2 = s([pir, k165, tre, t0, pile], 'lemul1ad', '( _pi x. T ) <_ ( ( ; 1 6 / 5 ) x. T )')
    q4 = nlinarith(w, A0, [q2], '4 <_ ( Q ^ 2 )', leaves=lv) if False else None
    q2b = s([s([a1(w, A0, '2re', '2 e. RR'), linarith(w, A0, [], '0 <_ 2', leaves={})], 'jca', '( 2 e. RR /\\ 0 <_ 2 )'),
             s([qre, q2], 'jca', '( Q e. RR /\\ 2 <_ Q )'), w.inst('le2sq2')], 'syl2anc', '( 2 ^ 2 ) <_ ( Q ^ 2 )')
    qsq = s([qre], 'resqcld', '( Q ^ 2 ) e. RR')
    s4 = s([s([s([a1(w, A0, 'sq2', '( 2 ^ 2 ) = 4')], 'eqcomd', '4 = ( 2 ^ 2 )'), q2b], 'eqbrtrd', '4 <_ ( Q ^ 2 )')], 'id', 'x') if False else \
        s([a1(w, A0, 'sq2', '( 2 ^ 2 ) = 4'), q2b], 'eqbrtrrd', '4 <_ ( Q ^ 2 )')
    f3 = s([a1(w, A0, '4re', '4 e. RR'), qsq, tre, t0, s4], 'lemul1ad', '( 4 x. T ) <_ ( ( Q ^ 2 ) x. T )')
    G = GW('N')
    goal = '( ( ; 1 2 x. T ) x. %s ) <_ ( ; ; 1 0 0 x. ( N + ( ( Q ^ 2 ) x. T ) ) )' % G
    c = nlinarith(w, A0, [f1, f2, f3, n0, t0], goal, leaves=lv, atoms=at)
    L1 = '( ( ; 1 2 x. T ) x. %s )' % G
    R1 = '( ; ; 1 0 0 x. ( N + ( ( Q ^ 2 ) x. T ) ) )'
    from cl import Closure
    cl = Closure(w, A0, lv)
    m = s([cl.mem(L1, 'RR'), cl.mem(R1, 'RR'), bre, bge, c], 'lemul1ad', '( %s x. B ) <_ ( %s x. B )' % (L1, R1))
    e1 = s([cl.mem('( ; 1 2 x. T )', 'CC'), cl.mem(G, 'CC'), s([bre], 'recnd', 'B e. CC')], 'mulassd',
           '( %s x. B ) = ( ( ; 1 2 x. T ) x. ( %s x. B ) )' % (L1, G))
    e2 = s([cl.mem('; ; 1 0 0', 'CC'), cl.mem('( N + ( ( Q ^ 2 ) x. T ) )', 'CC'), s([bre], 'recnd', 'B e. CC')], 'mulassd',
           '( %s x. B ) = ( ; ; 1 0 0 x. ( ( N + ( ( Q ^ 2 ) x. T ) ) x. B ) )' % R1)
    w.qed([e1, e2, m], '3brtr3d', S['lsnum'])
    return w


ALL = {'lsnum': lsnum, 'lsexpb': lsexpb, 'pile165': pile165}

if __name__ == '__main__':
    for n in (sys.argv[1:] or list(ALL)):
        ALL[n]().run()
