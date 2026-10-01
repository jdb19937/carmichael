"""Z6a (block z6ab): the bounds on the log-Gamma term functions -- derivative (z6hdtb), term (z6htb)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_ghlib import *
from z6a_gh3 import V1, DD, CK, TK, DTK
from lin import linarith

S_HDTB = ('( ( K e. NN /\\ ( X e. CC /\\ 0 <_ ( Re ` X ) ) ) -> ( abs ` %s ) <_ ( ( 1 + ( abs ` X ) ) / ( K ^ 2 ) ) )' % DTK('K', 'X'))
S_HTB = ('( ( K e. NN /\\ ( Z e. CC /\\ 0 <_ ( Re ` Z ) ) ) -> ( abs ` %s ) <_ ( ( ( 1 + ( abs ` Z ) ) / ( K ^ 2 ) ) x. ( abs ` Z ) ) )' % TK('K', 'Z'))


def hdtb():
    w = W('z6hdtb', 'The derivative of a log-Gamma term function is ` O ( ( 1 + | X | ) / K ^ 2 ) ` on the closed '
          'right half-plane ( ~ logdifbnd , ~ logdiflbnd , ~ subrecd ).')
    A0 = '( K e. NN /\\ ( X e. CC /\\ 0 <_ ( Re ` X ) ) )'
    s = st(w, A0)
    C = CK()
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
    xc = w.s([], 'simprl', '( %s -> X e. CC )' % A0)
    x0 = w.s([], 'simprr', '( %s -> 0 <_ ( Re ` X ) )' % A0)
    kr = s([kn], 'nnred', 'K e. RR'); kc = s([kn], 'nncnd', 'K e. CC'); k0 = s([kn], 'nnne0d', 'K =/= 0')
    krp = s([kn], 'nnrpd', 'K e. RR+'); kge = s([krp], 'rpge0d', '0 <_ K')
    k1n = s([kn, w.inst('peano2nn')], 'syl', '( K + 1 ) e. NN')
    k1rp = s([k1n], 'nnrpd', '( K + 1 ) e. RR+'); k1c = s([k1n], 'nncnd', '( K + 1 ) e. CC'); k10 = s([k1n], 'nnne0d', '( K + 1 ) =/= 0')
    cr = s([s([k1rp, krp], 'rpdivcld', '( ( K + 1 ) / K ) e. RR+')], 'relogcld', '%s e. RR' % C)
    cc = s([cr], 'recnd', '%s e. CC' % C)
    LD = '( ( log ` ( K + 1 ) ) - ( log ` K ) )'
    ceq = s([k1rp, krp, w.inst('relogdiv')], 'syl2anc', '%s = %s' % (C, LD))
    ub = s([ceq, s([krp, w.inst('logdifbnd')], 'syl', '%s <_ ( 1 / K )' % LD)], 'eqbrtrd', '%s <_ ( 1 / K )' % C)
    lb = s([s([krp, w.inst('logdiflbnd')], 'syl', '( 1 / ( K + 1 ) ) <_ %s' % LD), ceq], 'breqtrrd', '( 1 / ( K + 1 ) ) <_ %s' % C)
    rk = s([kn], 'nnrecred', '( 1 / K ) e. RR')
    rk1 = s([k1n], 'nnrecred', '( 1 / ( K + 1 ) ) e. RR')
    sr = s([s([kc, k0, k1c, k10], 'subrecd', '( ( 1 / K ) - ( 1 / ( K + 1 ) ) ) = ( ( ( K + 1 ) - K ) / ( K x. ( K + 1 ) ) )'),
            s([s([kc, c1(w, A0, 'ax-1cn', '1 e. CC')], 'pncan2d', '( ( K + 1 ) - K ) = 1')], 'oveq1d',
              '( ( ( K + 1 ) - K ) / ( K x. ( K + 1 ) ) ) = ( 1 / ( K x. ( K + 1 ) ) )')], 'eqtrd',
           '( ( 1 / K ) - ( 1 / ( K + 1 ) ) ) = ( 1 / ( K x. ( K + 1 ) ) )')
    kk1 = s([krp, k1rp], 'rpmulcld', '( K x. ( K + 1 ) ) e. RR+')
    k2 = s([krp, c1(w, A0, '2z', '2 e. ZZ')], 'rpexpcld', '( K ^ 2 ) e. RR+')
    k2r = s([k2], 'rpred', '( K ^ 2 ) e. RR')
    kle = s([s([kc], 'sqvald', '( K ^ 2 ) = ( K x. K )'), s([kr, s([kr, w.inst('peano2re')], 'syl', '( K + 1 ) e. RR'), kr, kge, s([kr], 'lep1d', 'K <_ ( K + 1 )')], 'lemul2ad', '( K x. K ) <_ ( K x. ( K + 1 ) )')],
            'eqbrtrd', '( K ^ 2 ) <_ ( K x. ( K + 1 ) )')
    rle = s([kle, s([k2, kk1], 'lerecd', '( ( K ^ 2 ) <_ ( K x. ( K + 1 ) ) <-> ( 1 / ( K x. ( K + 1 ) ) ) <_ ( 1 / ( K ^ 2 ) ) )')], 'mpbid',
            '( 1 / ( K x. ( K + 1 ) ) ) <_ ( 1 / ( K ^ 2 ) )')
    rkk = s([s([kk1], 'rpreccld', '( 1 / ( K x. ( K + 1 ) ) ) e. RR+')], 'rpred', '( 1 / ( K x. ( K + 1 ) ) ) e. RR')
    rk2p = s([k2], 'rpreccld', '( 1 / ( K ^ 2 ) ) e. RR+')
    rk2 = s([rk2p], 'rpred', '( 1 / ( K ^ 2 ) ) e. RR')
    rk20 = s([rk2p], 'rpge0d', '0 <_ ( 1 / ( K ^ 2 ) )')
    lv = {C: cr, '( 1 / K )': rk, '( 1 / ( K + 1 ) )': rk1, '( 1 / ( K x. ( K + 1 ) ) )': rkk, '( 1 / ( K ^ 2 ) )': rk2}
    lo = linarith(w, A0, [lb, sr, rle], '-u ( 1 / ( K ^ 2 ) ) <_ ( %s - ( 1 / K ) )' % C, leaves=lv)
    hi = linarith(w, A0, [ub, rk20], '( %s - ( 1 / K ) ) <_ ( 1 / ( K ^ 2 ) )' % C, leaves=lv)
    a1r = s([cr, rk], 'resubcld', '( %s - ( 1 / K ) ) e. RR' % C)
    ab1 = s([s([lo, hi], 'jca', '( -u ( 1 / ( K ^ 2 ) ) <_ ( %s - ( 1 / K ) ) /\\ ( %s - ( 1 / K ) ) <_ ( 1 / ( K ^ 2 ) ) )' % (C, C)),
             s([a1r, rk2, w.inst('absle')], 'syl2anc', '( ( abs ` ( %s - ( 1 / K ) ) ) <_ ( 1 / ( K ^ 2 ) ) <-> ( -u ( 1 / ( K ^ 2 ) ) <_ ( %s - ( 1 / K ) ) /\\ ( %s - ( 1 / K ) ) <_ ( 1 / ( K ^ 2 ) ) ) )' % (C, C, C))],
            'mpbird', '( abs ` ( %s - ( 1 / K ) ) ) <_ ( 1 / ( K ^ 2 ) )' % C)
    # the X part
    xk = s([xc, kc], 'addcld', '( X + K ) e. CC')
    rx = s([xc], 'recld', '( Re ` X ) e. RR')
    rxk = s([s([xc, kc], 'readdd', '( Re ` ( X + K ) ) = ( ( Re ` X ) + ( Re ` K ) )'),
             s([s([kr, w.inst('rere')], 'syl', '( Re ` K ) = K')], 'oveq2d', '( ( Re ` X ) + ( Re ` K ) ) = ( ( Re ` X ) + K )')], 'eqtrd',
            '( Re ` ( X + K ) ) = ( ( Re ` X ) + K )')
    k_le = linarith(w, A0, [x0], 'K <_ ( ( Re ` X ) + K )', leaves={'( Re ` X )': rx, 'K': kr})
    k_le2 = s([k_le, rxk], 'breqtrrd', 'K <_ ( Re ` ( X + K ) )')
    axk = s([xk], 'abscld', '( abs ` ( X + K ) ) e. RR')
    kab = s([kr, s([xk], 'recld', '( Re ` ( X + K ) ) e. RR'), axk, k_le2, s([xk, w.inst('releabs')], 'syl', '( Re ` ( X + K ) ) <_ ( abs ` ( X + K ) )')], 'letrd',
            'K <_ ( abs ` ( X + K ) )')
    axk0 = s([c1(w, A0, '0re', '0 e. RR'), kr, axk, s([krp], 'rpgt0d', '0 < K'), kab], 'ltletrd', '0 < ( abs ` ( X + K ) )')
    xkn = s([axk0, s([xk, w.inst('absgt0')], 'syl', '( ( X + K ) =/= 0 <-> 0 < ( abs ` ( X + K ) ) )')], 'mpbird', '( X + K ) =/= 0')
    s2 = s([s([kc, k0, xk, xkn], 'subrecd', '( ( 1 / K ) - ( 1 / ( X + K ) ) ) = ( ( ( X + K ) - K ) / ( K x. ( X + K ) ) )'),
            s([s([xc, kc], 'pncand', '( ( X + K ) - K ) = X')], 'oveq1d', '( ( ( X + K ) - K ) / ( K x. ( X + K ) ) ) = ( X / ( K x. ( X + K ) ) )')], 'eqtrd',
           '( ( 1 / K ) - ( 1 / ( X + K ) ) ) = ( X / ( K x. ( X + K ) ) )')
    kxk = s([kc, xk], 'mulcld', '( K x. ( X + K ) ) e. CC')
    kxk0 = s([kc, xk, k0, xkn], 'mulne0d', '( K x. ( X + K ) ) =/= 0')
    ab2 = s([s([s2], 'fveq2d', '( abs ` ( ( 1 / K ) - ( 1 / ( X + K ) ) ) ) = ( abs ` ( X / ( K x. ( X + K ) ) ) )'),
             s([xc, kxk, kxk0], 'absdivd', '( abs ` ( X / ( K x. ( X + K ) ) ) ) = ( ( abs ` X ) / ( abs ` ( K x. ( X + K ) ) ) )'),
             s([s([s([kc, xk], 'absmuld', '( abs ` ( K x. ( X + K ) ) ) = ( ( abs ` K ) x. ( abs ` ( X + K ) ) )'),
                   s([s([kr, kge], 'absidd', '( abs ` K ) = K')], 'oveq1d', '( ( abs ` K ) x. ( abs ` ( X + K ) ) ) = ( K x. ( abs ` ( X + K ) ) )')], 'eqtrd',
                  '( abs ` ( K x. ( X + K ) ) ) = ( K x. ( abs ` ( X + K ) ) )')], 'oveq2d',
               '( ( abs ` X ) / ( abs ` ( K x. ( X + K ) ) ) ) = ( ( abs ` X ) / ( K x. ( abs ` ( X + K ) ) ) )')], '3eqtrd',
            '( abs ` ( ( 1 / K ) - ( 1 / ( X + K ) ) ) ) = ( ( abs ` X ) / ( K x. ( abs ` ( X + K ) ) ) )')
    axkrp = s([axk, axk0], 'elrpd', '( abs ` ( X + K ) ) e. RR+')
    den = s([s([kc], 'sqvald', '( K ^ 2 ) = ( K x. K )'), s([kr, axk, kr, kge, kab], 'lemul2ad', '( K x. K ) <_ ( K x. ( abs ` ( X + K ) ) )')], 'eqbrtrd',
          '( K ^ 2 ) <_ ( K x. ( abs ` ( X + K ) ) )')
    ax = s([xc], 'abscld', '( abs ` X ) e. RR')
    ax0 = s([xc], 'absge0d', '0 <_ ( abs ` X )')
    b2 = s([k2, s([krp, axkrp], 'rpmulcld', '( K x. ( abs ` ( X + K ) ) ) e. RR+'), ax, ax0, den], 'lediv2ad',
           '( ( abs ` X ) / ( K x. ( abs ` ( X + K ) ) ) ) <_ ( ( abs ` X ) / ( K ^ 2 ) )')
    bound2 = s([ab2, b2], 'eqbrtrd', '( abs ` ( ( 1 / K ) - ( 1 / ( X + K ) ) ) ) <_ ( ( abs ` X ) / ( K ^ 2 ) )')
    rxkc = s([xk, xkn], 'reccld', '( 1 / ( X + K ) ) e. CC')
    rkc = s([rk], 'recnd', '( 1 / K ) e. CC')
    tri = s([cc, rxkc, rkc, w.inst('abs3dif')], 'syl3anc',
            '( abs ` %s ) <_ ( ( abs ` ( %s - ( 1 / K ) ) ) + ( abs ` ( ( 1 / K ) - ( 1 / ( X + K ) ) ) ) )' % (DTK('K', 'X'), C))
    k2c = s([k2], 'rpcnd', '( K ^ 2 ) e. CC'); k20 = s([k2], 'rpne0d', '( K ^ 2 ) =/= 0')
    dd = s([c1(w, A0, 'ax-1cn', '1 e. CC'), s([ax], 'recnd', '( abs ` X ) e. CC'), k2c, k20], 'divdird',
           '( ( 1 + ( abs ` X ) ) / ( K ^ 2 ) ) = ( ( 1 / ( K ^ 2 ) ) + ( ( abs ` X ) / ( K ^ 2 ) ) )')
    lv2 = {'( abs ` %s )' % DTK('K', 'X'): s([s([cc, rxkc], 'subcld', '%s e. CC' % DTK('K', 'X'))], 'abscld', '( abs ` %s ) e. RR' % DTK('K', 'X')),
           '( abs ` ( %s - ( 1 / K ) ) )' % C: s([s([cc, rkc], 'subcld', '( %s - ( 1 / K ) ) e. CC' % C)], 'abscld', '( abs ` ( %s - ( 1 / K ) ) ) e. RR' % C),
           '( abs ` ( ( 1 / K ) - ( 1 / ( X + K ) ) ) )': s([s([rkc, rxkc], 'subcld', '( ( 1 / K ) - ( 1 / ( X + K ) ) ) e. CC')], 'abscld', '( abs ` ( ( 1 / K ) - ( 1 / ( X + K ) ) ) ) e. RR'),
           '( 1 / ( K ^ 2 ) )': rk2,
           '( ( abs ` X ) / ( K ^ 2 ) )': s([ax, k2], 'rerpdivcld', '( ( abs ` X ) / ( K ^ 2 ) ) e. RR'),
           '( ( 1 + ( abs ` X ) ) / ( K ^ 2 ) )': s([s([c1(w, A0, '1re', '1 e. RR'), ax], 'readdcld', '( 1 + ( abs ` X ) ) e. RR'), k2], 'rerpdivcld', '( ( 1 + ( abs ` X ) ) / ( K ^ 2 ) ) e. RR')}
    linarith(w, A0, [tri, ab1, bound2, dd], '( abs ` %s ) <_ ( ( 1 + ( abs ` X ) ) / ( K ^ 2 ) )' % DTK('K', 'X'), leaves=lv2, name='qed')
    return run(w)


def htb():
    w = W('z6htb', 'A log-Gamma term function is ` O ( | Z | ( 1 + | Z | ) / K ^ 2 ) ` on the closed right half-plane: '
          'the fundamental theorem along the segment from ` 0 ` to ` Z ` ( ~ lintftc ) and the ML bound ( ~ lintabs ) '
          'with the derivative bound ~ z6hdtb .')
    A0 = '( K e. NN /\\ ( Z e. CC /\\ 0 <_ ( Re ` Z ) ) )'
    s = st(w, A0)
    C = CK()
    G = '( z e. %s |-> %s )' % (V1, TK())
    F = '( z e. %s |-> %s )' % (V1, DTK())
    SG = '( 0 cseg Z )'
    M = '( ( 1 + ( abs ` Z ) ) / ( K ^ 2 ) )'
    kn = w.s([], 'simpl', '( %s -> K e. NN )' % A0)
    zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
    z0 = w.s([], 'simprr', '( %s -> 0 <_ ( Re ` Z ) )' % A0)
    kr = s([kn], 'nnred', 'K e. RR'); kc = s([kn], 'nncnd', 'K e. CC'); k0 = s([kn], 'nnne0d', 'K =/= 0')
    krp = s([kn], 'nnrpd', 'K e. RR+')
    k1rp = s([s([kn, w.inst('peano2nn')], 'syl', '( K + 1 ) e. NN')], 'nnrpd', '( K + 1 ) e. RR+')
    cc = s([s([s([k1rp, krp], 'rpdivcld', '( ( K + 1 ) / K ) e. RR+')], 'relogcld', '%s e. RR' % C)], 'recnd', '%s e. CC' % C)
    m1 = w.s([w.s([], '1re', '1 e. RR')], 'renegcli', '-u 1 e. RR')
    elv = lambda a, X: w.s([w.s([m1, w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ -u 1 < ( Re ` %s ) ) )' % (X, V1, X, X))], 'a1i',
                           '( %s -> ( %s e. %s <-> ( %s e. CC /\\ -u 1 < ( Re ` %s ) ) ) )' % (a, X, V1, X, X))
    vo = c1(w, A0, 'hpopn', '%s e. %s' % (V1, TOP))
    vss = c1(w, A0, 'hpss', '%s C_ CC' % V1)
    tri = s([kn, vo, c1(w, A0, 'ssid', '%s C_ %s' % (V1, V1))], '3jca', '( K e. NN /\\ %s e. %s /\\ %s C_ %s )' % (V1, TOP, V1, V1))
    dv = s([tri, w.inst('z6htdv')], 'syl', '( CC _D %s ) = %s' % (G, F))
    gf = s([s([s([tri, w.inst('z6hthol')], 'syl', HOLG(G, V1))], 'simpld', '%s e. ( %s -cn-> CC )' % (G, V1)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (G, V1))
    # continuity of F
    Av = '( %s /\\ z e. %s )' % (A0, V1)
    zv = w.s([], 'simpr', '( %s -> z e. %s )' % (Av, V1))
    fac = w.s([w.s([w.s([kn], 'adantr', '( %s -> K e. NN )' % Av), zv], 'jca', '( %s -> ( K e. NN /\\ z e. %s ) )' % (Av, V1)), w.inst('z6hv1')], 'syl',
              '( %s -> ( ( ( z / K ) + 1 ) e. %s /\\ ( z + K ) =/= 0 ) )' % (Av, DD))
    zkn = w.s([fac], 'simprd', '( %s -> ( z + K ) =/= 0 )' % Av)
    zcv = w.s([w.s([vss], 'adantr', '( %s -> %s C_ CC )' % (Av, V1)), zv], 'sseldd', '( %s -> z e. CC )' % Av)
    zkc = w.s([zcv, w.s([kc], 'adantr', '( %s -> K e. CC )' % Av)], 'addcld', '( %s -> ( z + K ) e. CC )' % Av)
    ccss = c1(w, A0, 'ssid', 'CC C_ CC')
    cid = s([vss, ccss, w.inst('cncfmptid')], 'syl2anc', '( z e. %s |-> z ) e. ( %s -cn-> CC )' % (V1, V1))
    ck = s([kc, vss, ccss, w.inst('cncfmptc')], 'syl3anc', '( z e. %s |-> K ) e. ( %s -cn-> CC )' % (V1, V1))
    cadd = s([cid, ck], 'addcncf', '( z e. %s |-> ( z + K ) ) e. ( %s -cn-> CC )' % (V1, V1))
    CZ = '( CC \\ { 0 } )'
    fz = s([w.s([w.s([zkc, zkn], 'jca', '( %s -> ( ( z + K ) e. CC /\\ ( z + K ) =/= 0 ) )' % Av), w.s([], 'eldifsn', '( ( z + K ) e. %s <-> ( ( z + K ) e. CC /\\ ( z + K ) =/= 0 ) )' % CZ)],
                'sylibr', '( %s -> ( z + K ) e. %s )' % (Av, CZ)), w.s([], 'eqid', '( z e. %s |-> ( z + K ) ) = ( z e. %s |-> ( z + K ) )' % (V1, V1))], 'fmptd',
           '( z e. %s |-> ( z + K ) ) : %s --> %s' % (V1, V1, CZ))
    cz = s([fz, s([c1(w, A0, 'difss', '%s C_ CC' % CZ), cadd, w.inst('cncfcdm')], 'syl2anc',
                  '( ( z e. %s |-> ( z + K ) ) e. ( %s -cn-> %s ) <-> ( z e. %s |-> ( z + K ) ) : %s --> %s )' % (V1, V1, CZ, V1, V1, CZ))], 'mpbird',
           '( z e. %s |-> ( z + K ) ) e. ( %s -cn-> %s )' % (V1, V1, CZ))
    c1f = s([c1(w, A0, 'ax-1cn', '1 e. CC'), vss, ccss, w.inst('cncfmptc')], 'syl3anc', '( z e. %s |-> 1 ) e. ( %s -cn-> CC )' % (V1, V1))
    cdiv = s([c1f, cz], 'divcncf', '( z e. %s |-> ( 1 / ( z + K ) ) ) e. ( %s -cn-> CC )' % (V1, V1))
    ccf = s([cc, vss, ccss, w.inst('cncfmptc')], 'syl3anc', '( z e. %s |-> %s ) e. ( %s -cn-> CC )' % (V1, C, V1))
    fcn = s([ccf, cdiv], 'subcncf', '%s e. ( %s -cn-> CC )' % (F, V1))
    # the segment
    Ay = '( %s /\\ y e. %s )' % (A0, SG)
    zcy = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ay)
    z0y = w.s([z0], 'adantr', '( %s -> 0 <_ ( Re ` Z ) )' % Ay)
    c0 = c1(w, Ay, '0cn', '0 e. CC')
    LN = '( 0 + ( t x. ( Z - 0 ) ) )'
    ex = w.s([w.s([], 'simpr', '( %s -> y e. %s )' % (Ay, SG)), w.s([c0, zcy, w.inst('csegel')], 'syl2anc', '( %s -> ( y e. %s <-> E. t e. ( 0 [,] 1 ) y = %s ) )' % (Ay, SG, LN))],
             'mpbid', '( %s -> E. t e. ( 0 [,] 1 ) y = %s )' % (Ay, LN))
    At = '( ( %s /\\ t e. ( 0 [,] 1 ) ) /\\ y = %s )' % (Ay, LN)
    a = st(w, At)
    t3 = a([w.s([], 'simplr', '( %s -> t e. ( 0 [,] 1 ) )' % At), w.inst('elicc01')], 'sylib', '( t e. RR /\\ 0 <_ t /\\ t <_ 1 )')
    tr = a([t3, w.inst('simp1')], 'syl', 't e. RR'); t0 = a([t3, w.inst('simp2')], 'syl', '0 <_ t'); t1 = a([t3, w.inst('simp3')], 'syl', 't <_ 1')
    zct = w.s([zcy], 'ad2antrr', '( %s -> Z e. CC )' % At)
    tc = a([tr], 'recnd', 't e. CC')
    yeq = a([w.s([], 'simpr', '( %s -> y = %s )' % (At, LN)),
             a([a([a([a([zct], 'subid1d', '( Z - 0 ) = Z')], 'oveq2d', '( t x. ( Z - 0 ) ) = ( t x. Z )')], 'oveq2d', '%s = ( 0 + ( t x. Z ) )' % LN),
                a([a([tc, zct], 'mulcld', '( t x. Z ) e. CC'), w.inst('addlid')], 'syl', '( 0 + ( t x. Z ) ) = ( t x. Z )')], 'eqtrd', '%s = ( t x. Z )' % LN)],
            'eqtrd', 'y = ( t x. Z )')
    yc = a([yeq, a([tc, zct], 'mulcld', '( t x. Z ) e. CC')], 'eqeltrd', 'y e. CC')
    rz = a([zct], 'recld', '( Re ` Z ) e. RR')
    ry = a([a([yeq], 'fveq2d', '( Re ` y ) = ( Re ` ( t x. Z ) )'), a([tr, zct], 'remul2d', '( Re ` ( t x. Z ) ) = ( t x. ( Re ` Z ) )')], 'eqtrd', '( Re ` y ) = ( t x. ( Re ` Z ) )')
    ry0 = a([a([tr, rz, t0, w.s([z0y], 'ad2antrr', '( %s -> 0 <_ ( Re ` Z ) )' % At)], 'mulge0d', '0 <_ ( t x. ( Re ` Z ) )'), ry], 'breqtrrd', '0 <_ ( Re ` y )')
    az = a([zct], 'abscld', '( abs ` Z ) e. RR')
    ay = a([a([yeq], 'fveq2d', '( abs ` y ) = ( abs ` ( t x. Z ) )'), a([tc, zct], 'absmuld', '( abs ` ( t x. Z ) ) = ( ( abs ` t ) x. ( abs ` Z ) )'),
            a([a([tr, t0], 'absidd', '( abs ` t ) = t')], 'oveq1d', '( ( abs ` t ) x. ( abs ` Z ) ) = ( t x. ( abs ` Z ) )')], '3eqtrd', '( abs ` y ) = ( t x. ( abs ` Z ) )')
    ayl = a([a([tr, c1(w, At, '1re', '1 e. RR'), az, a([zct], 'absge0d', '0 <_ ( abs ` Z )'), t1], 'lemul1ad', '( t x. ( abs ` Z ) ) <_ ( 1 x. ( abs ` Z ) )'),
             a([a([az], 'recnd', '( abs ` Z ) e. CC')], 'mullidd', '( 1 x. ( abs ` Z ) ) = ( abs ` Z )')], 'breqtrd', '( t x. ( abs ` Z ) ) <_ ( abs ` Z )')
    ayz = a([ay, ayl], 'eqbrtrd', '( abs ` y ) <_ ( abs ` Z )')
    P = '( y e. CC /\\ ( 0 <_ ( Re ` y ) /\\ ( abs ` y ) <_ ( abs ` Z ) ) )'
    pt = a([yc, a([ry0, ayz], 'jca', '( 0 <_ ( Re ` y ) /\\ ( abs ` y ) <_ ( abs ` Z ) )')], 'jca', P)
    py = w.s([pt, ex], 'r19.29a', '( %s -> %s )' % (Ay, P))
    b = st(w, Ay)
    ycy = b([py], 'simpld', 'y e. CC')
    ry0y = b([py], 'simprld', '0 <_ ( Re ` y )')
    ayzy = b([py], 'simprrd', '( abs ` y ) <_ ( abs ` Z )')
    ryr = b([ycy], 'recld', '( Re ` y ) e. RR')
    yv = b([b([ycy, linarith(w, Ay, [ry0y], '-u 1 < ( Re ` y )', leaves={'( Re ` y )': ryr})], 'jca', '( y e. CC /\\ -u 1 < ( Re ` y ) )'), elv(Ay, 'y')], 'mpbird', 'y e. %s' % V1)
    sgv = s([w.s([yv], 'ex', '( %s -> ( y e. %s -> y e. %s ) )' % (A0, SG, V1))], 'ssrdv', '%s C_ %s' % (SG, V1))
    # the bound on the segment
    kny = w.s([kn], 'adantr', '( %s -> K e. NN )' % Ay)
    db = b([b([kny, b([ycy, ry0y], 'jca', '( y e. CC /\\ 0 <_ ( Re ` y ) )')], 'jca', '( K e. NN /\\ ( y e. CC /\\ 0 <_ ( Re ` y ) ) )'), w.inst('z6hdtb')], 'syl',
           '( abs ` %s ) <_ ( ( 1 + ( abs ` y ) ) / ( K ^ 2 ) )' % DTK('K', 'y'))
    k2 = b([b([kny], 'nnrpd', 'K e. RR+'), c1(w, Ay, '2z', '2 e. ZZ')], 'rpexpcld', '( K ^ 2 ) e. RR+')
    one = c1(w, Ay, '1re', '1 e. RR')
    azy = b([zcy], 'abscld', '( abs ` Z ) e. RR')
    ayy = b([ycy], 'abscld', '( abs ` y ) e. RR')
    db2 = b([b([one, ayy], 'readdcld', '( 1 + ( abs ` y ) ) e. RR'), b([one, azy], 'readdcld', '( 1 + ( abs ` Z ) ) e. RR'), k2,
             b([ayy, azy, one, ayzy], 'leadd2dd', '( 1 + ( abs ` y ) ) <_ ( 1 + ( abs ` Z ) )')], 'lediv1dd', '( ( 1 + ( abs ` y ) ) / ( K ^ 2 ) ) <_ %s' % M)
    subd = w.s([w.s([], 'id', '( z = y -> z = y )')], 'oveq1d', '( z = y -> ( z + K ) = ( y + K ) )')
    subd2 = w.s([w.s([subd], 'oveq2d', '( z = y -> ( 1 / ( z + K ) ) = ( 1 / ( y + K ) ) )')], 'oveq2d', '( z = y -> %s = %s )' % (DTK(), DTK('K', 'y')))
    fv = w.s([subd2, w.s([], 'eqid', '%s = %s' % (F, F))], 'fvmptg', '( ( y e. %s /\\ %s e. _V ) -> ( %s ` y ) = %s )' % (V1, DTK('K', 'y'), F, DTK('K', 'y')))
    fyv = b([yv, b([], 'ovexd', '%s e. _V' % DTK('K', 'y')), fv], 'syl2anc', '( %s ` y ) = %s' % (F, DTK('K', 'y')))
    zkny = b([b([b([kny, yv], 'jca', '( K e. NN /\\ y e. %s )' % V1), w.inst('z6hv1')], 'syl', '( ( ( y / K ) + 1 ) e. %s /\\ ( y + K ) =/= 0 )' % DD)], 'simprd', '( y + K ) =/= 0')
    ccy = w.s([cc], 'adantr', '( %s -> %s e. CC )' % (Ay, C))
    dtc = b([ccy, b([b([ycy, b([kny], 'nncnd', 'K e. CC')], 'addcld', '( y + K ) e. CC'), zkny], 'reccld', '( 1 / ( y + K ) ) e. CC')], 'subcld', '%s e. CC' % DTK('K', 'y'))
    fyr = b([b([fyv, dtc], 'eqeltrd', '( %s ` y ) e. CC' % F)], 'abscld', '( abs ` ( %s ` y ) ) e. RR' % F)
    a2r = b([b([one, ayy], 'readdcld', '( 1 + ( abs ` y ) ) e. RR'), k2], 'rerpdivcld', '( ( 1 + ( abs ` y ) ) / ( K ^ 2 ) ) e. RR')
    a3r = b([b([one, azy], 'readdcld', '( 1 + ( abs ` Z ) ) e. RR'), k2], 'rerpdivcld', '%s e. RR' % M)
    fb = b([fyr, a2r, a3r, b([b([fyv], 'fveq2d', '( abs ` ( %s ` y ) ) = ( abs ` %s )' % (F, DTK('K', 'y'))), db], 'eqbrtrd', '( abs ` ( %s ` y ) ) <_ ( ( 1 + ( abs ` y ) ) / ( K ^ 2 ) )' % F), db2],
           'letrd', '( abs ` ( %s ` y ) ) <_ %s' % (F, M))
    ral = s([fb], 'ralrimiva', 'A. y e. %s ( abs ` ( %s ` y ) ) <_ %s' % (SG, F, M))
    # the FTC and the ML bound
    c00 = c1(w, A0, '0cn', '0 e. CC')
    ftc = s([s([s([c00, zc], 'jca', '( 0 e. CC /\\ Z e. CC )'), s([gf, dv], 'jca', '( %s : %s --> CC /\\ ( CC _D %s ) = %s )' % (G, V1, G, F)),
                s([fcn, sgv], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (F, V1, SG, V1))], '3jca',
               '( ( 0 e. CC /\\ Z e. CC ) /\\ ( %s : %s --> CC /\\ ( CC _D %s ) = %s ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (G, V1, G, F, F, V1, SG, V1)),
             w.inst('lintftc')], 'syl', '( %s lint <. 0 , Z >. ) = ( ( %s ` Z ) - ( %s ` 0 ) )' % (F, G, G))
    rz0 = s([zc], 'recld', '( Re ` Z ) e. RR')
    zv1 = s([s([zc, linarith(w, A0, [z0], '-u 1 < ( Re ` Z )', leaves={'( Re ` Z )': rz0})], 'jca', '( Z e. CC /\\ -u 1 < ( Re ` Z ) )'), elv(A0, 'Z')], 'mpbird', 'Z e. %s' % V1)
    subZ = w.s([w.s([w.s([], 'id', '( z = Z -> z = Z )')], 'oveq1d', '( z = Z -> ( z x. %s ) = ( Z x. %s ) )' % (C, C)),
                w.s([w.s([w.s([w.s([], 'id', '( z = Z -> z = Z )')], 'oveq1d', '( z = Z -> ( z / K ) = ( Z / K ) )')], 'oveq1d', '( z = Z -> ( ( z / K ) + 1 ) = ( ( Z / K ) + 1 ) )')], 'fveq2d',
                    '( z = Z -> ( log ` ( ( z / K ) + 1 ) ) = ( log ` ( ( Z / K ) + 1 ) ) )')], 'oveq12d', '( z = Z -> %s = %s )' % (TK(), TK('K', 'Z')))
    gz = s([zv1, s([], 'ovexd', '%s e. _V' % TK('K', 'Z')), w.s([subZ, w.s([], 'eqid', '%s = %s' % (G, G))], 'fvmptg', '( ( Z e. %s /\\ %s e. _V ) -> ( %s ` Z ) = %s )' % (V1, TK('K', 'Z'), G, TK('K', 'Z')))],
           'syl2anc', '( %s ` Z ) = %s' % (G, TK('K', 'Z')))
    sub0 = w.s([w.s([w.s([], 'id', '( z = 0 -> z = 0 )')], 'oveq1d', '( z = 0 -> ( z x. %s ) = ( 0 x. %s ) )' % (C, C)),
                w.s([w.s([w.s([w.s([], 'id', '( z = 0 -> z = 0 )')], 'oveq1d', '( z = 0 -> ( z / K ) = ( 0 / K ) )')], 'oveq1d', '( z = 0 -> ( ( z / K ) + 1 ) = ( ( 0 / K ) + 1 ) )')], 'fveq2d',
                    '( z = 0 -> ( log ` ( ( z / K ) + 1 ) ) = ( log ` ( ( 0 / K ) + 1 ) ) )')], 'oveq12d', '( z = 0 -> %s = %s )' % (TK(), TK('K', '0')))
    zero_v1 = s([s([c00, s([c1(w, A0, 'neg1lt0', '-u 1 < 0'), c1(w, A0, 're0', '( Re ` 0 ) = 0')], 'breqtrrd', '-u 1 < ( Re ` 0 )')],
                   'jca', '( 0 e. CC /\\ -u 1 < ( Re ` 0 ) )'), elv(A0, '0')], 'mpbird', '0 e. %s' % V1)
    g0 = s([zero_v1, s([], 'ovexd', '%s e. _V' % TK('K', '0')), w.s([sub0, w.s([], 'eqid', '%s = %s' % (G, G))], 'fvmptg', '( ( 0 e. %s /\\ %s e. _V ) -> ( %s ` 0 ) = %s )' % (V1, TK('K', '0'), G, TK('K', '0')))],
           'syl2anc', '( %s ` 0 ) = %s' % (G, TK('K', '0')))
    t0v = s([s([s([cc, w.inst('mul02')], 'syl', '( 0 x. %s ) = 0' % C),
                s([s([s([s([kc, k0, w.inst('div0')], 'syl2anc', '( 0 / K ) = 0')], 'oveq1d', '( ( 0 / K ) + 1 ) = ( 0 + 1 )'), c1(w, A0, '0p1e1', '( 0 + 1 ) = 1')], 'eqtrd',
                     '( ( 0 / K ) + 1 ) = 1')], 'fveq2d', '( log ` ( ( 0 / K ) + 1 ) ) = ( log ` 1 )')], 'oveq12d', '%s = ( 0 - ( log ` 1 ) )' % TK('K', '0')),
             s([c1(w, A0, 'log1', '( log ` 1 ) = 0')], 'oveq2d', '( 0 - ( log ` 1 ) ) = ( 0 - 0 )'), c1(w, A0, '0m0e0', '( 0 - 0 ) = 0')], '3eqtrd', '%s = 0' % TK('K', '0'))
    ed = w.s([], 'eqid', '%s = %s' % (DD, DD))
    qd = s([s([s([kn, zv1], 'jca', '( K e. NN /\\ Z e. %s )' % V1), w.inst('z6hv1')], 'syl', '( ( ( Z / K ) + 1 ) e. %s /\\ ( Z + K ) =/= 0 )' % DD)], 'simpld', '( ( Z / K ) + 1 ) e. %s' % DD)
    tkc = s([s([zc, cc], 'mulcld', '( Z x. %s ) e. CC' % C),
             s([s([qd], 'eldifad', '( ( Z / K ) + 1 ) e. CC'), s([qd, w.s([ed], 'logdmn0', '( ( ( Z / K ) + 1 ) e. %s -> ( ( Z / K ) + 1 ) =/= 0 )' % DD)], 'syl', '( ( Z / K ) + 1 ) =/= 0')],
               'logcld', '( log ` ( ( Z / K ) + 1 ) ) e. CC')], 'subcld', '%s e. CC' % TK('K', 'Z'))
    val = s([ftc, s([gz, s([g0, t0v], 'eqtrd', '( %s ` 0 ) = 0' % G)], 'oveq12d', '( ( %s ` Z ) - ( %s ` 0 ) ) = ( %s - 0 )' % (G, G, TK('K', 'Z'))),
             s([tkc], 'subid1d', '( %s - 0 ) = %s' % (TK('K', 'Z'), TK('K', 'Z')))], '3eqtrd', '( %s lint <. 0 , Z >. ) = %s' % (F, TK('K', 'Z')))
    mr = s([s([c1(w, A0, '1re', '1 e. RR'), s([zc], 'abscld', '( abs ` Z ) e. RR')], 'readdcld', '( 1 + ( abs ` Z ) ) e. RR'),
            s([krp, c1(w, A0, '2z', '2 e. ZZ')], 'rpexpcld', '( K ^ 2 ) e. RR+')], 'rerpdivcld', '%s e. RR' % M)
    ml = s([s([s([s([c00, zc], 'jca', '( 0 e. CC /\\ Z e. CC )'), s([fcn, sgv], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (F, V1, SG, V1))], 'jca',
                 '( ( 0 e. CC /\\ Z e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (F, V1, SG, V1)), mr, ral], '3jca',
               '( ( ( 0 e. CC /\\ Z e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) ) /\\ %s e. RR /\\ A. y e. %s ( abs ` ( %s ` y ) ) <_ %s )' % (F, V1, SG, V1, M, SG, F, M)),
            w.inst('lintabs')], 'syl', '( abs ` ( %s lint <. 0 , Z >. ) ) <_ ( %s x. ( abs ` ( Z - 0 ) ) )' % (F, M))
    fin = s([s([val], 'fveq2d', '( abs ` ( %s lint <. 0 , Z >. ) ) = ( abs ` %s )' % (F, TK('K', 'Z'))), ml,
             s([s([s([zc], 'subid1d', '( Z - 0 ) = Z')], 'fveq2d', '( abs ` ( Z - 0 ) ) = ( abs ` Z )')], 'oveq2d', '( %s x. ( abs ` ( Z - 0 ) ) ) = ( %s x. ( abs ` Z ) )' % (M, M))],
            '3brtr3d', '( abs ` %s ) <_ ( %s x. ( abs ` Z ) )' % (TK('K', 'Z'), M))
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    assert '( %s -> ( abs ` %s ) <_ ( %s x. ( abs ` Z ) ) )' % (A0, TK('K', 'Z'), M) == S_HTB
    return run(w)


if __name__ == '__main__':
    want = sys.argv[1:]
    for lab, fn in [('z6hdtb', hdtb), ('z6htb', htb)]:
        if lab in want:
            if fn():
                status(lab)
