"""Sortie C6 section C: isolated zeros and the local identity theorem
(cnopnbl, cncfne0, holzisol, holid1, holid2)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *

ABSM = '( abs o. - )'


def ISO(X, r):
    return 'A. z e. D ( ( z =/= %s /\\ ( abs ` ( z - %s ) ) < %s ) -> ( F ` z ) =/= 0 )' % (X, X, r)


def VAN(X, s):
    return 'A. w e. D ( ( abs ` ( w - %s ) ) < %s -> ( F ` w ) = 0 )' % (X, s)


def HALFZ(X):
    return 'A. w e. CC ( ( abs ` ( w - %s ) ) <_ ( R / 2 ) -> ( F ` w ) = 0 )' % X


if __name__ == '__main__':
    # ---- cnopnbl: an open set contains a ball about each of its points -----------
    w = W('cnopnbl', 'An open subset of the complex plane contains a disc about each of its points.')
    A0 = '( E e. %s /\\ P e. E )' % TOP
    A1 = '( %s /\\ r e. RR+ )' % A0
    A2 = '( %s /\\ ( P ( ball ` %s ) r ) C_ E )' % (A1, ABSM)
    A3 = '( %s /\\ z e. CC )' % A2
    A4 = '( %s /\\ ( abs ` ( z - P ) ) < r )' % A3
    xm = closed(w, A0, 'cnxmet', '%s e. ( *Met ` CC )' % ABSM)
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    jm = w.s([ej], 'cnfldtopn', '%s = ( MetOpen ` %s )' % (TOP, ABSM))
    ee = w.s([], 'simpl', '( %s -> E e. %s )' % (A0, TOP))
    pe = w.s([], 'simpr', '( %s -> P e. E )' % A0)
    ex = w.s([xm, ee, pe, w.s([jm], 'mopni2', '( ( %s e. ( *Met ` CC ) /\\ E e. %s /\\ P e. E ) -> E. r e. RR+ ( P ( ball ` %s ) r ) C_ E )' % (ABSM, TOP, ABSM))], 'syl3anc',
             '( %s -> E. r e. RR+ ( P ( ball ` %s ) r ) C_ E )' % (A0, ABSM))
    # inside: z in CC with |z - P| < r is in the ball hence in E
    un = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    ecc = w.s([w.s([ee, w.inst('elssuni')], 'syl', '( %s -> E C_ U. %s )' % (A0, TOP)), w.s([un], 'eqcomi', 'U. %s = CC' % TOP)], 'sseqtrdi', '( %s -> E C_ CC )' % A0)
    pcc = w.s([ecc, pe], 'sseldd', '( %s -> P e. CC )' % A0)
    zc = w.s([], 'simpr', '( %s -> z e. CC )' % A3)
    zc4 = w.s([zc], 'adantr', '( %s -> z e. CC )' % A4)
    pc4 = w.s([pcc], 'ad4antr', '( %s -> P e. CC )' % A4)
    rr4 = w.s([w.s([w.s([], 'simpr', '( %s -> r e. RR+ )' % A1)], 'ad3antrrr', '( %s -> r e. RR+ )' % A4)], 'rpxrd', '( %s -> r e. RR* )' % A4)
    bl = w.s([w.s([closed(w, A4, 'cnxmet', '%s e. ( *Met ` CC )' % ABSM), rr4], 'jca', '( %s -> ( %s e. ( *Met ` CC ) /\\ r e. RR* ) )' % (A4, ABSM)), w.s([pc4, zc4], 'jca', '( %s -> ( P e. CC /\\ z e. CC ) )' % A4), w.inst('elbl2')], 'syl2anc',
             '( %s -> ( z e. ( P ( ball ` %s ) r ) <-> ( P %s z ) < r ) )' % (A4, ABSM, ABSM))
    dv = w.s([pc4, zc4, w.s([w.s([], 'eqid', '%s = %s' % (ABSM, ABSM))], 'cnmetdval', '( ( P e. CC /\\ z e. CC ) -> ( P %s z ) = ( abs ` ( P - z ) ) )' % ABSM)], 'syl2anc', '( %s -> ( P %s z ) = ( abs ` ( P - z ) ) )' % (A4, ABSM))
    dv2 = w.s([dv, w.s([pc4, zc4, w.inst('abssub')], 'syl2anc', '( %s -> ( abs ` ( P - z ) ) = ( abs ` ( z - P ) ) )' % A4)], 'eqtrd', '( %s -> ( P %s z ) = ( abs ` ( z - P ) ) )' % (A4, ABSM))
    lt = w.s([dv2, w.s([], 'simpr', '( %s -> ( abs ` ( z - P ) ) < r )' % A4)], 'eqbrtrd', '( %s -> ( P %s z ) < r )' % (A4, ABSM))
    inb = w.s([lt, bl], 'mpbird', '( %s -> z e. ( P ( ball ` %s ) r ) )' % (A4, ABSM))
    ine = w.s([w.s([w.s([], 'simpr', '( %s -> ( P ( ball ` %s ) r ) C_ E )' % (A2, ABSM))], 'ad2antrr', '( %s -> ( P ( ball ` %s ) r ) C_ E )' % (A4, ABSM)), inb], 'sseldd', '( %s -> z e. E )' % A4)
    imp_ = w.s([ine], 'ex', '( %s -> ( ( abs ` ( z - P ) ) < r -> z e. E ) )' % A3)
    ral = w.s([imp_], 'ralrimiva', '( %s -> A. z e. CC ( ( abs ` ( z - P ) ) < r -> z e. E ) )' % A2)
    rex = w.s([w.s([ral], 'ex', '( %s -> ( ( P ( ball ` %s ) r ) C_ E -> A. z e. CC ( ( abs ` ( z - P ) ) < r -> z e. E ) ) )' % (A1, ABSM))], 'reximdva',
              '( %s -> ( E. r e. RR+ ( P ( ball ` %s ) r ) C_ E -> E. r e. RR+ A. z e. CC ( ( abs ` ( z - P ) ) < r -> z e. E ) ) )' % (A0, ABSM))
    w.qed([ex, rex], 'mpd', '( %s -> E. r e. RR+ A. z e. CC ( ( abs ` ( z - P ) ) < r -> z e. E ) )' % A0)
    run1(w)

    # ---- cncfne0: a continuous function nonzero at P is nonzero near P ---------------
    w = W('cncfne0', 'A continuous function that is nonzero at a point is nonzero on a disc about that point.')
    A0 = '( G e. ( E -cn-> CC ) /\\ P e. E /\\ ( G ` P ) =/= 0 )'
    gcn = w.s([], 'simp1', '( %s -> G e. ( E -cn-> CC ) )' % A0)
    pe = w.s([], 'simp2', '( %s -> P e. E )' % A0)
    gne = w.s([], 'simp3', '( %s -> ( G ` P ) =/= 0 )' % A0)
    gf = w.s([gcn, w.inst('cncff')], 'syl', '( %s -> G : E --> CC )' % A0)
    gp = w.s([gf, pe], 'ffvelcdmd', '( %s -> ( G ` P ) e. CC )' % A0)
    AG = '( abs ` ( G ` P ) )'
    agrp = w.s([gp, gne, w.inst('absrpcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A0, AG))
    ex = w.s([gcn, pe, agrp, w.inst('cncfi')], 'syl3anc', '( %s -> E. r e. RR+ A. z e. E ( ( abs ` ( z - P ) ) < r -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s ) )' % (A0, AG))
    A1 = '( %s /\\ r e. RR+ )' % A0
    A2 = '( %s /\\ z e. E )' % A1
    A3 = '( %s /\\ ( ( abs ` ( z - P ) ) < r -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s ) )' % (A2, AG)
    A4 = '( %s /\\ ( abs ` ( z - P ) ) < r )' % A3
    A5 = '( %s /\\ ( G ` z ) = 0 )' % A4
    gz = w.s([w.s([gf], 'ad3antrrr', '( %s -> G : E --> CC )' % A3), w.s([w.s([], 'simpr', '( %s -> z e. E )' % A2)], 'adantr', '( %s -> z e. E )' % A3)], 'ffvelcdmd', '( %s -> ( G ` z ) e. CC )' % A3)
    lt = w.s([w.s([], 'simpr', '( %s -> ( abs ` ( z - P ) ) < r )' % A4), w.s([w.s([], 'simpr', '( %s -> ( ( abs ` ( z - P ) ) < r -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s ) )' % (A3, AG))], 'adantr',
                                                                                  '( %s -> ( ( abs ` ( z - P ) ) < r -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s ) )' % (A4, AG))], 'mpd',
            '( %s -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s )' % (A4, AG))
    gp5 = w.s([gp], 'ad5antr', '( %s -> ( G ` P ) e. CC )' % A5)
    e1 = w.s([w.s([], 'simpr', '( %s -> ( G ` z ) = 0 )' % A5)], 'oveq1d', '( %s -> ( ( G ` z ) - ( G ` P ) ) = ( 0 - ( G ` P ) ) )' % A5)
    e2 = w.s([w.s([w.s([], 'df-neg', '-u ( G ` P ) = ( 0 - ( G ` P ) )')], 'eqcomi', '( 0 - ( G ` P ) ) = -u ( G ` P )')], 'a1i', '( %s -> ( 0 - ( G ` P ) ) = -u ( G ` P ) )' % A5)
    e3 = w.s([w.s([w.s([e1, e2], 'eqtrd', '( %s -> ( ( G ` z ) - ( G ` P ) ) = -u ( G ` P ) )' % A5)], 'fveq2d', '( %s -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) = ( abs ` -u ( G ` P ) ) )' % A5),
              w.s([gp5], 'absnegd', '( %s -> ( abs ` -u ( G ` P ) ) = %s )' % (A5, AG))], 'eqtrd', '( %s -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) = %s )' % (A5, AG))
    ltp = w.s([e3, w.s([lt], 'adantr', '( %s -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s )' % (A5, AG))], 'eqbrtrrd', '( %s -> %s < %s )' % (A5, AG, AG))
    nlt = w.s([w.s([gp5], 'abscld', '( %s -> %s e. RR )' % (A5, AG))], 'ltnrd', '( %s -> -. %s < %s )' % (A5, AG, AG))
    con = w.s([ltp, nlt], 'pm2.65da', '( %s -> -. ( G ` z ) = 0 )' % A4)
    ne = w.s([con], 'neqned', '( %s -> ( G ` z ) =/= 0 )' % A4)
    im1 = w.s([ne], 'ex', '( %s -> ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) )' % A3)
    im2 = w.s([im1], 'ex', '( %s -> ( ( ( abs ` ( z - P ) ) < r -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s ) -> ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) ) )' % (A2, AG))
    ral = w.s([im2], 'ralimdva', '( %s -> ( A. z e. E ( ( abs ` ( z - P ) ) < r -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s ) -> A. z e. E ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) ) )' % (A1, AG))
    rex = w.s([ral], 'reximdva', '( %s -> ( E. r e. RR+ A. z e. E ( ( abs ` ( z - P ) ) < r -> ( abs ` ( ( G ` z ) - ( G ` P ) ) ) < %s ) -> E. r e. RR+ A. z e. E ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) ) )' % (A0, AG))
    w.qed([ex, rex], 'mpd', '( %s -> E. r e. RR+ A. z e. E ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) )' % A0)
    run1(w)

    # ---- holzisol: a zero of finite order is isolated ---------------------------------
    w = W('holzisol', 'A zero of finite order is isolated: if F is ( z - P ) ^ N times a continuous function nonzero at P, then F has no zero other than P on a disc about P.')
    FAC = 'A. z e. D ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( G ` z ) )'
    A0 = '( ( G e. ( D -cn-> CC ) /\\ P e. D /\\ ( G ` P ) =/= 0 ) /\\ ( N e. NN0 /\\ %s ) )' % FAC
    gpn = w.s([], 'simpl', '( %s -> ( G e. ( D -cn-> CC ) /\\ P e. D /\\ ( G ` P ) =/= 0 ) )' % A0)
    nf = w.s([], 'simpr', '( %s -> ( N e. NN0 /\\ %s ) )' % (A0, FAC))
    hn = w.s([nf, w.inst('simpl')], 'syl', '( %s -> N e. NN0 )' % A0)
    fac = w.s([nf, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, FAC))
    gcn = w.s([gpn, w.inst('simp1')], 'syl', '( %s -> G e. ( D -cn-> CC ) )' % A0)
    pd = w.s([gpn, w.inst('simp2')], 'syl', '( %s -> P e. D )' % A0)
    dss = w.s([gcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    pc = w.s([dss, pd], 'sseldd', '( %s -> P e. CC )' % A0)
    ex = w.s([gpn, w.inst('cncfne0')], 'syl', '( %s -> E. r e. RR+ A. z e. D ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) )' % A0)
    A1 = '( %s /\\ r e. RR+ )' % A0
    A2 = '( %s /\\ v e. D )' % A1
    A3 = '( %s /\\ ( ( abs ` ( v - P ) ) < r -> ( G ` v ) =/= 0 ) )' % A2
    A4 = '( %s /\\ ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) )' % A3
    vd = w.s([w.s([], 'simpr', '( %s -> v e. D )' % A2)], 'ad2antrr', '( %s -> v e. D )' % A4)
    cnd = w.s([], 'simpr', '( %s -> ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) )' % A4)
    vne = w.s([cnd, w.inst('simpl')], 'syl', '( %s -> v =/= P )' % A4)
    vlt = w.s([cnd, w.inst('simpr')], 'syl', '( %s -> ( abs ` ( v - P ) ) < r )' % A4)
    gvne = w.s([vlt, w.s([w.s([], 'simpr', '( %s -> ( ( abs ` ( v - P ) ) < r -> ( G ` v ) =/= 0 ) )' % A3)], 'adantr', '( %s -> ( ( abs ` ( v - P ) ) < r -> ( G ` v ) =/= 0 ) )' % A4)], 'mpd', '( %s -> ( G ` v ) =/= 0 )' % A4)
    sub = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )'), w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z - P ) = ( v - P ) )')], 'oveq1d', '( z = v -> ( ( z - P ) ^ N ) = ( ( v - P ) ^ N ) )'), w.s([], 'fveq2', '( z = v -> ( G ` z ) = ( G ` v ) )')], 'oveq12d',
                                                                                    '( z = v -> ( ( ( z - P ) ^ N ) x. ( G ` z ) ) = ( ( ( v - P ) ^ N ) x. ( G ` v ) ) )')], 'eqeq12d',
              '( z = v -> ( ( F ` z ) = ( ( ( z - P ) ^ N ) x. ( G ` z ) ) <-> ( F ` v ) = ( ( ( v - P ) ^ N ) x. ( G ` v ) ) ) )')
    fv = w.s([sub, w.s([fac], 'ad4antr', '( %s -> %s )' % (A4, FAC)), vd], 'rspcdva', '( %s -> ( F ` v ) = ( ( ( v - P ) ^ N ) x. ( G ` v ) ) )' % A4)
    vc = w.s([w.s([dss], 'ad4antr', '( %s -> D C_ CC )' % A4), vd], 'sseldd', '( %s -> v e. CC )' % A4)
    pc4 = w.s([pc], 'ad4antr', '( %s -> P e. CC )' % A4)
    vp = w.s([vc, pc4], 'subcld', '( %s -> ( v - P ) e. CC )' % A4)
    vpn = w.s([vc, pc4, vne], 'subne0d', '( %s -> ( v - P ) =/= 0 )' % A4)
    hn4 = w.s([hn], 'ad4antr', '( %s -> N e. NN0 )' % A4)
    vkn = w.s([vp, vpn, w.s([hn4], 'nn0zd', '( %s -> N e. ZZ )' % A4), w.inst('expne0i')], 'syl3anc', '( %s -> ( ( v - P ) ^ N ) =/= 0 )' % A4)
    gv = w.s([w.s([w.s([gcn], 'ad4antr', '( %s -> G e. ( D -cn-> CC ) )' % A4), w.inst('cncff')], 'syl', '( %s -> G : D --> CC )' % A4), vd], 'ffvelcdmd', '( %s -> ( G ` v ) e. CC )' % A4)
    prne = w.s([w.s([vp, hn4], 'expcld', '( %s -> ( ( v - P ) ^ N ) e. CC )' % A4), gv, vkn, gvne], 'mulne0d', '( %s -> ( ( ( v - P ) ^ N ) x. ( G ` v ) ) =/= 0 )' % A4)
    fne = w.s([fv, prne], 'eqnetrd', '( %s -> ( F ` v ) =/= 0 )' % A4)
    im1 = w.s([fne], 'ex', '( %s -> ( ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) -> ( F ` v ) =/= 0 ) )' % A3)
    im2 = w.s([im1], 'ex', '( %s -> ( ( ( abs ` ( v - P ) ) < r -> ( G ` v ) =/= 0 ) -> ( ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) -> ( F ` v ) =/= 0 ) ) )' % A2)
    ral = w.s([im2], 'ralimdva', '( %s -> ( A. v e. D ( ( abs ` ( v - P ) ) < r -> ( G ` v ) =/= 0 ) -> A. v e. D ( ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) -> ( F ` v ) =/= 0 ) ) )' % A1)
    # rename z <-> v in both quantifiers
    cb1 = w.s([w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z - P ) = ( v - P ) )')], 'fveq2d', '( z = v -> ( abs ` ( z - P ) ) = ( abs ` ( v - P ) ) )')], 'breq1d', '( z = v -> ( ( abs ` ( z - P ) ) < r <-> ( abs ` ( v - P ) ) < r ) )'),
               w.s([w.s([], 'fveq2', '( z = v -> ( G ` z ) = ( G ` v ) )')], 'neeq1d', '( z = v -> ( ( G ` z ) =/= 0 <-> ( G ` v ) =/= 0 ) )')], 'imbi12d',
              '( z = v -> ( ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) <-> ( ( abs ` ( v - P ) ) < r -> ( G ` v ) =/= 0 ) ) )')
    cbv1 = w.s([cb1], 'cbvralvw', '( A. z e. D ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) <-> A. v e. D ( ( abs ` ( v - P ) ) < r -> ( G ` v ) =/= 0 ) )')
    cb2 = w.s([w.s([w.s([], 'neeq1', '( z = v -> ( z =/= P <-> v =/= P ) )'), w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z - P ) = ( v - P ) )')], 'fveq2d', '( z = v -> ( abs ` ( z - P ) ) = ( abs ` ( v - P ) ) )')], 'breq1d',
                                                                                    '( z = v -> ( ( abs ` ( z - P ) ) < r <-> ( abs ` ( v - P ) ) < r ) )')], 'anbi12d',
                    '( z = v -> ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) <-> ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) ) )'),
               w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )')], 'neeq1d', '( z = v -> ( ( F ` z ) =/= 0 <-> ( F ` v ) =/= 0 ) )')], 'imbi12d',
              '( z = v -> ( ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) -> ( F ` z ) =/= 0 ) <-> ( ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) -> ( F ` v ) =/= 0 ) ) )')
    cbv2 = w.s([cb2], 'cbvralvw', '( %s <-> A. v e. D ( ( v =/= P /\\ ( abs ` ( v - P ) ) < r ) -> ( F ` v ) =/= 0 ) )' % ISO('P', 'r'))
    ral2 = w.s([ral, cbv1, cbv2], '3imtr4g', '( %s -> ( A. z e. D ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) -> %s ) )' % (A1, ISO('P', 'r')))
    rex = w.s([ral2], 'reximdva', '( %s -> ( E. r e. RR+ A. z e. D ( ( abs ` ( z - P ) ) < r -> ( G ` z ) =/= 0 ) -> E. r e. RR+ %s ) )' % (A0, ISO('P', 'r')))
    w.qed([ex, rex], 'mpd', '( %s -> E. r e. RR+ %s )' % (A0, ISO('P', 'r')))
    run1(w)

    # ---- holid1: the dichotomy ---------------------------------------------------------
    w = W('holid1', 'The dichotomy at a point: either a holomorphic function vanishes on the disc of radius R / 2 about P, or P is not a limit of zeros.')
    hyp(w, '1', 'holid1.c', CDEF)
    A0 = HRM
    ALLZ = 'A. k e. NN0 ( C ` k ) = 0'
    d = hrmctx(w, A0, w.s([], 'id', '( %s -> %s )' % (A0, A0)))
    # case all coefficients vanish
    AZ = '( %s /\\ %s )' % (A0, ALLZ)
    AW = '( %s /\\ w e. CC )' % AZ
    AL = '( %s /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) )' % AW
    allz = w.s([], 'simpr', '( %s -> %s )' % (AZ, ALLZ))
    z0 = closed(w, AZ, '0nn0', '0 e. NN0')
    c0 = w.s([w.s([w.s([], 'fveq2', '( k = 0 -> ( C ` k ) = ( C ` 0 ) )')], 'eqeq1d', '( k = 0 -> ( ( C ` k ) = 0 <-> ( C ` 0 ) = 0 ) )'), allz, z0], 'rspcdva', '( %s -> ( C ` 0 ) = 0 )' % AZ)
    hc0 = w.s([ad(w, d['abih'], AZ, '( %s /\\ %s /\\ %s )' % (AB, INTP, HOLO)), w.s(['1'], 'holc0', '( ( %s /\\ %s /\\ %s ) -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AB, INTP, HOLO, TPI))], 'syl',
              '( %s -> ( C ` 0 ) = ( %s x. ( F ` P ) ) )' % (AZ, TPI))
    tf0 = w.s([hc0, c0], 'eqtr3d', '( %s -> ( %s x. ( F ` P ) ) = 0 )' % (AZ, TPI))
    tpic, tne = tpisteps(w, AZ)
    fp = w.s([ad(w, d['ff'], AZ, 'F : D --> CC'), ad(w, d['pd'], AZ, 'P e. D')], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % AZ)
    orx = w.s([w.s([tpic, fp, w.inst('mul0or')], 'syl2anc', '( %s -> ( ( %s x. ( F ` P ) ) = 0 <-> ( %s = 0 \\/ ( F ` P ) = 0 ) ) )' % (AZ, TPI, TPI)), tf0], 'mpbid', '( %s -> ( %s = 0 \\/ ( F ` P ) = 0 ) )' % (AZ, TPI))
    fp0 = w.s([w.s([w.s([tne], 'neneqd', '( %s -> -. %s = 0 )' % (AZ, TPI)), w.inst('orel1')], 'syl', '( %s -> ( ( %s = 0 \\/ ( F ` P ) = 0 ) -> ( F ` P ) = 0 ) )' % (AZ, TPI)), orx], 'mpd', '( %s -> ( F ` P ) = 0 )' % AZ)
    # w = P
    AE = '( %s /\\ w = P )' % AL
    ce = w.s([w.s([w.s([], 'simpr', '( %s -> w = P )' % AE)], 'fveq2d', '( %s -> ( F ` w ) = ( F ` P ) )' % AE), w.s([fp0], 'ad3antrrr', '( %s -> ( F ` P ) = 0 )' % AE)], 'eqtrd', '( %s -> ( F ` w ) = 0 )' % AE)
    # w =/= P: rectintid at Z := w
    AN = '( %s /\\ w =/= P )' % AL
    wc = w.s([w.s([], 'simpr', '( %s -> w e. CC )' % AW)], 'ad2antrr', '( %s -> w e. CC )' % AN)
    wle = w.s([w.s([], 'simpr', '( %s -> ( abs ` ( w - P ) ) <_ ( R / 2 ) )' % AL)], 'adantr', '( %s -> ( abs ` ( w - P ) ) <_ ( R / 2 ) )' % AN)
    wne = w.s([], 'simpr', '( %s -> w =/= P )' % AN)
    def a4(st, f):
        return w.s([st], 'ad4antr', '( %s -> %s )' % (AN, f))
    aw = w.s([w.s([wc, a4(d['pc'], 'P e. CC')], 'subcld', '( %s -> ( w - P ) e. CC )' % AN)], 'abscld', '( %s -> ( abs ` ( w - P ) ) e. RR )' % AN)
    hr = w.s([a4(d['Rrp'], 'R e. RR+')], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % AN)
    ltr = w.s([aw, w.s([hr], 'rpred', '( %s -> ( R / 2 ) e. RR )' % AN), a4(d['rr'], 'R e. RR'), wle, w.s([a4(d['Rrp'], 'R e. RR+'), w.inst('rphalflt')], 'syl', '( %s -> ( R / 2 ) < R )' % AN)], 'lelttrd',
              '( %s -> ( abs ` ( w - P ) ) < R )' % AN)
    intw = w.s([w.s([a4(d['ab'], AB), a4(d['it'], INTP), a4(d['rbd'], RBDP)], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (AN, AB, INTP, RBDP)), w.s([wc, ltr], 'jca', '( %s -> ( w e. CC /\\ ( abs ` ( w - P ) ) < R ) )' % AN), w.inst('holdisint')], 'syl2anc',
               '( %s -> %s )' % (AN, INTV('w')))
    basew = w.s([a4(d['ab'], AB), w.s([a4(d['it'], INTP), intw, w.s([wne], 'necomd', '( %s -> P =/= w )' % AN)], '3jca', '( %s -> ( %s /\\ %s /\\ P =/= w ) )' % (AN, INTP, INTV('w'))), a4(d['holo'], HOLO)], '3jca',
               '( %s -> %s )' % (AN, BASEV('w')))
    ctxw = w.s([basew, w.s([w.s([a4(d['rbd'], RBDP), a4(d['rpos'], '0 < R')], 'jca', '( %s -> ( %s /\\ 0 < R ) )' % (AN, RBDP)), wle], 'jca', '( %s -> ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) )' % (AN, RBDP)),
                w.s([a4(d['mr'], 'M e. RR'), a4(d['alf'], ALF)], 'jca', '( %s -> ( M e. RR /\\ %s ) )' % (AN, ALF))], '3jca',
               '( %s -> ( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) )' % (AN, BASEV('w'), RBDP, ALF))
    # A. i e. NN0 ( H ` i ) = 0 for the family at w
    gG0, gH = famsteps(w, 'w')
    GM = '( m e. NN0 |-> %s )' % RINT(RMV(E2V('w'), 'm', 'w'), 'A', 'B')
    XYW = '( ( w - P ) / ( y - P ) )'
    gsb = w.s([w.s([w.s([w.s([w.s([], 'oveq2', '( m = n -> ( %s ^ m ) = ( %s ^ n ) )' % (XYW, XYW))], 'oveq2d', '( m = n -> ( ( F ` y ) x. ( %s ^ m ) ) = ( ( F ` y ) x. ( %s ^ n ) ) )' % (XYW, XYW))], 'oveq1d',
                       '( m = n -> ( ( ( F ` y ) x. ( %s ^ m ) ) / ( y - w ) ) = ( ( ( F ` y ) x. ( %s ^ n ) ) / ( y - w ) ) )' % (XYW, XYW))], 'mpteq2dv',
                  '( m = n -> %s = %s )' % (RMV(E2V('w'), 'm', 'w'), RMV(E2V('w'), 'n', 'w')))], 'oveq1d',
             '( m = n -> %s = %s )' % (RINT(RMV(E2V('w'), 'm', 'w'), 'A', 'B'), RINT(RMV(E2V('w'), 'n', 'w'), 'A', 'B')))
    gG = w.s([gsb], 'cbvmptv', '%s = %s' % (GM, GMAP('w')))
    AI = '( %s /\\ i e. NN0 )' % AN
    inn = w.s([], 'simpr', '( %s -> i e. NN0 )' % AI)
    ci0 = w.s([w.s([w.s([], 'fveq2', '( k = i -> ( C ` k ) = ( C ` i ) )')], 'eqeq1d', '( k = i -> ( ( C ` k ) = 0 <-> ( C ` i ) = 0 ) )'), w.s([w.s([allz], 'ad3antrrr', '( %s -> %s )' % (AN, ALLZ))], 'adantr', '( %s -> %s )' % (AI, ALLZ)), inn], 'rspcdva',
              '( %s -> ( C ` i ) = 0 )' % AI)
    hv0 = w.s([gH, '1'], 'holcfval', '( i e. NN0 -> ( %s ` i ) = ( ( ( w - P ) ^ i ) x. ( C ` i ) ) )' % HMAP('w'))
    hv = w.s([inn, hv0], 'syl', '( %s -> ( %s ` i ) = ( ( ( w - P ) ^ i ) x. ( C ` i ) ) )' % (AI, HMAP('w')))
    wpi = w.s([w.s([ad(w, wc, AI, 'w e. CC'), w.s([d['pc']], 'ad5antr', '( %s -> P e. CC )' % AI)], 'subcld', '( %s -> ( w - P ) e. CC )' % AI), inn], 'expcld', '( %s -> ( ( w - P ) ^ i ) e. CC )' % AI)
    hi0 = w.s([hv, w.s([w.s([ci0], 'oveq2d', '( %s -> ( ( ( w - P ) ^ i ) x. ( C ` i ) ) = ( ( ( w - P ) ^ i ) x. 0 ) )' % AI), w.s([wpi], 'mul01d', '( %s -> ( ( ( w - P ) ^ i ) x. 0 ) = 0 )' % AI)], 'eqtrd',
                        '( %s -> ( ( ( w - P ) ^ i ) x. ( C ` i ) ) = 0 )' % AI)], 'eqtrd', '( %s -> ( %s ` i ) = 0 )' % (AI, HMAP('w')))
    allh = w.s([hi0], 'ralrimiva', '( %s -> A. i e. NN0 ( %s ` i ) = 0 )' % (AN, HMAP('w')))
    rid0 = w.s([gG, gH], 'rectintid', '( ( ( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) /\\ A. i e. NN0 ( %s ` i ) = 0 ) -> ( F ` w ) = 0 )' % (BASEV('w'), RBDP, ALF, HMAP('w')))
    cn = w.s([w.s([ctxw, allh], 'jca', '( %s -> ( ( %s /\\ ( ( %s /\\ 0 < R ) /\\ ( abs ` ( w - P ) ) <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) /\\ A. i e. NN0 ( %s ` i ) = 0 ) )' % (AN, BASEV('w'), RBDP, ALF, HMAP('w'))), rid0], 'syl',
             '( %s -> ( F ` w ) = 0 )' % AN)
    both = w.s([ce, cn], 'pm2.61dane', '( %s -> ( F ` w ) = 0 )' % AL)
    halfz = w.s([w.s([w.s([both], 'ex', '( %s -> ( ( abs ` ( w - P ) ) <_ ( R / 2 ) -> ( F ` w ) = 0 ) )' % AW)], 'ralrimiva', '( %s -> %s )' % (AZ, HALFZ('P')))], 'orcd',
                '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (AZ, HALFZ('P'), ISO('P', 'r')))
    # case not all vanish
    ANZ = '( %s /\\ -. %s )' % (A0, ALLZ)
    PH = '( ( g e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D g ) ) /\\ ( g ` P ) =/= 0 /\\ A. z e. D ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) )'
    fac = w.s(['1'], 'holfac', '( %s -> E. n e. NN0 E. g %s )' % (ANZ, PH))
    AN1 = '( %s /\\ n e. NN0 )' % ANZ
    AN2 = '( %s /\\ %s )' % (AN1, PH)
    ph2 = w.s([], 'simpr', '( %s -> %s )' % (AN2, PH))
    gh = w.s([ph2, w.inst('simp1')], 'syl', '( %s -> ( g e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D g ) ) )' % AN2)
    gpn = w.s([w.s([gh, w.inst('simpl')], 'syl', '( %s -> g e. ( D -cn-> CC ) )' % AN2), w.s([d['pd']], 'ad3antrrr', '( %s -> P e. D )' % AN2), w.s([ph2, w.inst('simp2')], 'syl', '( %s -> ( g ` P ) =/= 0 )' % AN2)], '3jca',
              '( %s -> ( g e. ( D -cn-> CC ) /\\ P e. D /\\ ( g ` P ) =/= 0 ) )' % AN2)
    nn0 = w.s([w.s([], 'simpr', '( %s -> n e. NN0 )' % AN1)], 'adantr', '( %s -> n e. NN0 )' % AN2)
    nfac = w.s([nn0, w.s([ph2, w.inst('simp3')], 'syl', '( %s -> A. z e. D ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) )' % AN2)], 'jca', '( %s -> ( n e. NN0 /\\ A. z e. D ( F ` z ) = ( ( ( z - P ) ^ n ) x. ( g ` z ) ) ) )' % AN2)
    iso = w.s([gpn, nfac, w.inst('holzisol')], 'syl2anc', '( %s -> E. r e. RR+ %s )' % (AN2, ISO('P', 'r')))
    ex1 = w.s([w.s([iso], 'ex', '( %s -> ( %s -> E. r e. RR+ %s ) )' % (AN1, PH, ISO('P', 'r')))], 'exlimdv', '( %s -> ( E. g %s -> E. r e. RR+ %s ) )' % (AN1, PH, ISO('P', 'r')))
    ex2 = w.s([fac, w.s([ex1], 'rexlimdva', '( %s -> ( E. n e. NN0 E. g %s -> E. r e. RR+ %s ) )' % (ANZ, PH, ISO('P', 'r')))], 'mpd', '( %s -> E. r e. RR+ %s )' % (ANZ, ISO('P', 'r')))
    isoz = w.s([ex2], 'olcd', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (ANZ, HALFZ('P'), ISO('P', 'r')))
    w.qed([halfz, isoz], 'pm2.61dan', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (A0, HALFZ('P'), ISO('P', 'r')))
    run1(w, h=True)

    # ---- holid2: the local identity theorem, propagated to the half-disc ---------------
    w = W('holid2', 'The local identity theorem: a holomorphic function vanishing on some disc about P vanishes on the disc of radius R / 2 about P, R the distance from P to the boundary frame.')
    hyp(w, '1', 'holid2.c', CDEF)
    VANS = 'E. s e. RR+ %s' % VAN('P', 's')
    A0 = HRM
    hrm = w.s([], 'id', '( %s -> %s )' % (A0, HRM))
    d = hrmctx(w, A0, hrm)
    dich = w.s([hrm, w.s(['1'], 'holid1', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (HRM, HALFZ('P'), ISO('P', 'r')))], 'syl', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (A0, HALFZ('P'), ISO('P', 'r')))
    # the second disjunct is impossible
    A1 = '( %s /\\ ( s e. RR+ /\\ %s ) )' % (A0, VAN('P', 's'))
    A2 = '( %s /\\ ( r e. RR+ /\\ %s ) )' % (A1, ISO('P', 'r'))
    srp = w.s([w.s([w.s([], 'simpr', '( %s -> ( s e. RR+ /\\ %s ) )' % (A1, VAN('P', 's'))), w.inst('simpl')], 'syl', '( %s -> s e. RR+ )' % A1)], 'adantr', '( %s -> s e. RR+ )' % A2)
    vans = w.s([w.s([w.s([], 'simpr', '( %s -> ( s e. RR+ /\\ %s ) )' % (A1, VAN('P', 's'))), w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, VAN('P', 's')))], 'adantr', '( %s -> %s )' % (A2, VAN('P', 's')))
    rrp = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (A2, ISO('P', 'r'))), w.inst('simpl')], 'syl', '( %s -> r e. RR+ )' % A2)
    isor = w.s([w.s([], 'simpr', '( %s -> ( r e. RR+ /\\ %s ) )' % (A2, ISO('P', 'r'))), w.inst('simpr')], 'syl', '( %s -> %s )' % (A2, ISO('P', 'r')))
    Rrp2 = w.s([d['Rrp']], 'ad2antrr', '( %s -> R e. RR+ )' % A2)
    SM1 = '( ( r x. s ) / ( r + s ) )'
    SM2 = '( ( %s x. R ) / ( %s + R ) )' % (SM1, SM1)
    T = '( %s / 2 )' % SM2
    sm1 = w.s([rrp, srp, w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ r /\\ %s <_ s ) ) )' % (A2, SM1, SM1, SM1))
    sm1rp = w.s([sm1, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A2, SM1))
    sm2 = w.s([sm1rp, Rrp2, w.inst('softmin')], 'syl2anc', '( %s -> ( %s e. RR+ /\\ ( %s <_ %s /\\ %s <_ R ) ) )' % (A2, SM2, SM2, SM1, SM2))
    sm2rp = w.s([sm2, w.inst('simpl')], 'syl', '( %s -> %s e. RR+ )' % (A2, SM2))
    trp = w.s([sm2rp], 'rphalfcld', '( %s -> %s e. RR+ )' % (A2, T))
    tr = w.s([trp], 'rpred', '( %s -> %s e. RR )' % (A2, T))
    tc = w.s([tr], 'recnd', '( %s -> %s e. CC )' % (A2, T))
    tlt = w.s([sm2rp, w.inst('rphalflt')], 'syl', '( %s -> %s < %s )' % (A2, T, SM2))
    sm2r = w.s([sm2rp], 'rpred', '( %s -> %s e. RR )' % (A2, SM2))
    sm1r = w.s([sm1rp], 'rpred', '( %s -> %s e. RR )' % (A2, SM1))
    rr2 = w.s([Rrp2], 'rpred', '( %s -> R e. RR )' % A2)
    ltR = w.s([tr, sm2r, rr2, tlt, w.s([w.s([sm2, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ R ) )' % (A2, SM2, SM1, SM2)), w.inst('simpr')], 'syl', '( %s -> %s <_ R )' % (A2, SM2))], 'ltletrd', '( %s -> %s < R )' % (A2, T))
    lt1 = w.s([tr, sm2r, sm1r, tlt, w.s([w.s([sm2, w.inst('simpr')], 'syl', '( %s -> ( %s <_ %s /\\ %s <_ R ) )' % (A2, SM2, SM1, SM2)), w.inst('simpl')], 'syl', '( %s -> %s <_ %s )' % (A2, SM2, SM1))], 'ltletrd', '( %s -> %s < %s )' % (A2, T, SM1))
    ltr = w.s([tr, sm1r, w.s([rrp], 'rpred', '( %s -> r e. RR )' % A2), lt1, w.s([w.s([sm1, w.inst('simpr')], 'syl', '( %s -> ( %s <_ r /\\ %s <_ s ) )' % (A2, SM1, SM1)), w.inst('simpl')], 'syl', '( %s -> %s <_ r )' % (A2, SM1))], 'ltletrd', '( %s -> %s < r )' % (A2, T))
    lts = w.s([tr, sm1r, w.s([srp], 'rpred', '( %s -> s e. RR )' % A2), lt1, w.s([w.s([sm1, w.inst('simpr')], 'syl', '( %s -> ( %s <_ r /\\ %s <_ s ) )' % (A2, SM1, SM1)), w.inst('simpr')], 'syl', '( %s -> %s <_ s )' % (A2, SM1))], 'ltletrd', '( %s -> %s < s )' % (A2, T))
    # the point Z = P + T
    Z = '( P + %s )' % T
    pc2 = w.s([d['pc']], 'ad2antrr', '( %s -> P e. CC )' % A2)
    zc = w.s([pc2, tc], 'addcld', '( %s -> %s e. CC )' % (A2, Z))
    zmp = w.s([pc2, tc], 'pncan2d', '( %s -> ( %s - P ) = %s )' % (A2, Z, T))
    azp = w.s([w.s([zmp], 'fveq2d', '( %s -> ( abs ` ( %s - P ) ) = ( abs ` %s ) )' % (A2, Z, T)), w.s([tr, w.s([trp], 'rpge0d', '( %s -> 0 <_ %s )' % (A2, T))], 'absidd', '( %s -> ( abs ` %s ) = %s )' % (A2, T, T))], 'eqtrd',
              '( %s -> ( abs ` ( %s - P ) ) = %s )' % (A2, Z, T))
    zpne = w.s([zmp, w.s([trp], 'rpne0d', '( %s -> %s =/= 0 )' % (A2, T))], 'eqnetrd', '( %s -> ( %s - P ) =/= 0 )' % (A2, Z))
    zne = w.s([zpne, w.s([w.s([zc, pc2, w.inst('subeq0')], 'syl2anc', '( %s -> ( ( %s - P ) = 0 <-> %s = P ) )' % (A2, Z, Z))], 'necon3bid', '( %s -> ( ( %s - P ) =/= 0 <-> %s =/= P ) )' % (A2, Z, Z))], 'mpbid', '( %s -> %s =/= P )' % (A2, Z))
    ltR2 = w.s([azp, ltR], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < R )' % (A2, Z))
    intz = w.s([w.s([w.s([d['ab']], 'ad2antrr', '( %s -> %s )' % (A2, AB)), w.s([d['it']], 'ad2antrr', '( %s -> %s )' % (A2, INTP)), w.s([d['rbd']], 'ad2antrr', '( %s -> %s )' % (A2, RBDP))], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A2, AB, INTP, RBDP)),
                w.s([zc, ltR2], 'jca', '( %s -> ( %s e. CC /\\ ( abs ` ( %s - P ) ) < R ) )' % (A2, Z, Z)), w.inst('holdisint')], 'syl2anc', '( %s -> %s )' % (A2, INTV(Z)))
    zd = w.s([w.s([d['rd']], 'ad2antrr', '( %s -> ( A crect B ) C_ D )' % A2), w.s([w.s([d['ab']], 'ad2antrr', '( %s -> %s )' % (A2, AB)), intz, w.inst('crectinp')], 'syl2anc', '( %s -> %s e. ( A crect B ) )' % (A2, Z))], 'sseldd', '( %s -> %s e. D )' % (A2, Z))
    # F Z = 0 from VAN and F Z =/= 0 from ISO
    subv = w.s([w.s([w.s([w.s([], 'oveq1', '( w = %s -> ( w - P ) = ( %s - P ) )' % (Z, Z))], 'fveq2d', '( w = %s -> ( abs ` ( w - P ) ) = ( abs ` ( %s - P ) ) )' % (Z, Z))], 'breq1d', '( w = %s -> ( ( abs ` ( w - P ) ) < s <-> ( abs ` ( %s - P ) ) < s ) )' % (Z, Z)),
               w.s([w.s([], 'fveq2', '( w = %s -> ( F ` w ) = ( F ` %s ) )' % (Z, Z))], 'eqeq1d', '( w = %s -> ( ( F ` w ) = 0 <-> ( F ` %s ) = 0 ) )' % (Z, Z))], 'imbi12d',
              '( w = %s -> ( ( ( abs ` ( w - P ) ) < s -> ( F ` w ) = 0 ) <-> ( ( abs ` ( %s - P ) ) < s -> ( F ` %s ) = 0 ) ) )' % (Z, Z, Z))
    fz0 = w.s([w.s([azp, lts], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < s )' % (A2, Z)), w.s([subv, vans, zd], 'rspcdva', '( %s -> ( ( abs ` ( %s - P ) ) < s -> ( F ` %s ) = 0 ) )' % (A2, Z, Z))], 'mpd', '( %s -> ( F ` %s ) = 0 )' % (A2, Z))
    subi = w.s([w.s([w.s([], 'neeq1', '( z = %s -> ( z =/= P <-> %s =/= P ) )' % (Z, Z)), w.s([w.s([w.s([], 'oveq1', '( z = %s -> ( z - P ) = ( %s - P ) )' % (Z, Z))], 'fveq2d', '( z = %s -> ( abs ` ( z - P ) ) = ( abs ` ( %s - P ) ) )' % (Z, Z))], 'breq1d',
                                                                                           '( z = %s -> ( ( abs ` ( z - P ) ) < r <-> ( abs ` ( %s - P ) ) < r ) )' % (Z, Z))], 'anbi12d',
                    '( z = %s -> ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) <-> ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) ) )' % (Z, Z, Z)),
               w.s([w.s([], 'fveq2', '( z = %s -> ( F ` z ) = ( F ` %s ) )' % (Z, Z))], 'neeq1d', '( z = %s -> ( ( F ` z ) =/= 0 <-> ( F ` %s ) =/= 0 ) )' % (Z, Z))], 'imbi12d',
              '( z = %s -> ( ( ( z =/= P /\\ ( abs ` ( z - P ) ) < r ) -> ( F ` z ) =/= 0 ) <-> ( ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) -> ( F ` %s ) =/= 0 ) ) )' % (Z, Z, Z, Z))
    fzne = w.s([w.s([zne, w.s([azp, ltr], 'eqbrtrd', '( %s -> ( abs ` ( %s - P ) ) < r )' % (A2, Z))], 'jca', '( %s -> ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) )' % (A2, Z, Z)), w.s([subi, isor, zd], 'rspcdva',
                                                                                                                                                                      '( %s -> ( ( %s =/= P /\\ ( abs ` ( %s - P ) ) < r ) -> ( F ` %s ) =/= 0 ) )' % (A2, Z, Z, Z))], 'mpd',
               '( %s -> ( F ` %s ) =/= 0 )' % (A2, Z))
    fals = w.s([fzne, fz0], 'pm2.21ddne', '( %s -> F. )' % A2)
    # -. E. r e. RR+ ISO under A1: from ( A1 /\ ( r e. RR+ /\ ISO ) ) -> F.
    nex = w.s([w.s([fals], 'ex', '( %s -> ( ( r e. RR+ /\\ %s ) -> F. ) )' % (A1, ISO('P', 'r')))], 'alrimiv', '( %s -> A. r ( ( r e. RR+ /\\ %s ) -> F. ) )' % (A1, ISO('P', 'r')))
    nex3 = w.s([w.s([w.s([fals], 'ex', '( %s -> ( ( r e. RR+ /\\ %s ) -> F. ) )' % (A1, ISO('P', 'r')))], 'expd', '( %s -> ( r e. RR+ -> ( %s -> F. ) ) )' % (A1, ISO('P', 'r')))], 'rexlimdv',
               '( %s -> ( E. r e. RR+ %s -> F. ) )' % (A1, ISO('P', 'r')))
    nis = w.s([w.s([nex3], 'imp', '( ( %s /\\ E. r e. RR+ %s ) -> F. )' % (A1, ISO('P', 'r')))], 'inegd', '( %s -> -. E. r e. RR+ %s )' % (A1, ISO('P', 'r')))
    dich1 = w.s([dich], 'adantr', '( %s -> ( %s \\/ E. r e. RR+ %s ) )' % (A1, HALFZ('P'), ISO('P', 'r')))
    hz = w.s([w.s([nis, w.inst('orel2')], 'syl', '( %s -> ( ( %s \\/ E. r e. RR+ %s ) -> %s ) )' % (A1, HALFZ('P'), ISO('P', 'r'), HALFZ('P'))), dich1], 'mpd', '( %s -> %s )' % (A1, HALFZ('P')))
    e32 = w.s([hz], 'exp32', '( %s -> ( s e. RR+ -> ( %s -> %s ) ) )' % (HRM, VAN('P', 's'), HALFZ('P')))
    rl = w.s([e32], 'rexlimdv', '( %s -> ( %s -> %s ) )' % (HRM, VANS, HALFZ('P')))
    w.qed([rl], 'imp', '( ( %s /\\ %s ) -> %s )' % (HRM, VANS, HALFZ('P')))
    run1(w, h=True)
