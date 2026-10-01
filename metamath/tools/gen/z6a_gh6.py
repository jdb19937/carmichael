"""Z6a (block z6ab): Gamma is holomorphic on the right half-plane (z6hgval, z6gamhol)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6a_ghlib import *
from z6a_gh3 import V1, DD, CK, TK, DTK
from lin import linarith

SK = lambda Z: 'sum_ k e. NN %s' % TK('k', Z)
S_HGVAL = '( ( Z e. CC /\\ 0 < ( Re ` Z ) ) -> ( %s e. CC /\\ ( _G ` Z ) = ( ( exp ` %s ) / Z ) ) )' % (SK('Z'), SK('Z'))
GH = '( z e. %s |-> ( _G ` z ) )' % HPZ


def hgval():
    w = W('z6hgval', 'On the right half-plane, ` Gamma ( Z ) = exp ( S ( Z ) ) / Z ` with ` S ` the log-Gamma series '
          '( ~ lgamcvg , ~ eflgam ).')
    A0 = '( Z e. CC /\\ 0 < ( Re ` Z ) )'
    s = st(w, A0)
    zc = w.s([], 'simpl', '( %s -> Z e. CC )' % A0)
    zr = w.s([], 'simpr', '( %s -> 0 < ( Re ` Z ) )' % A0)
    zd = w.s([], 'zrenn', '( %s -> Z e. %s )' % (A0, DG))
    GM = '( m e. NN |-> %s )' % TK('m', 'Z')
    cv = s([w.s([], 'eqid', '%s = %s' % (GM, GM)), zd], 'lgamcvg', 'seq 1 ( + , %s ) ~~> ( ( log_G ` Z ) + ( log ` Z ) )' % GM)
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    fv, _ = mpval(w, Ak, 'm', 'NN', TK('m', 'Z'), 'k', kn)
    # TK ( k , Z ) e. CC
    t = st(w, Ak)
    rz = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)
    rzr = t([rz], 'recld', '( Re ` Z ) e. RR')
    gt = linarith(w, Ak, [w.s([zr], 'adantr', '( %s -> 0 < ( Re ` Z ) )' % Ak)], '-u 1 < ( Re ` Z )', leaves={'( Re ` Z )': rzr})
    m1 = w.s([w.s([], '1re', '1 e. RR')], 'renegcli', '-u 1 e. RR')
    zv = t([t([rz, gt], 'jca', '( Z e. CC /\\ -u 1 < ( Re ` Z ) )'),
            t([w.s([m1, w.inst('elhp2')], 'ax-mp', '( Z e. %s <-> ( Z e. CC /\\ -u 1 < ( Re ` Z ) ) )' % V1)], 'a1i', '( Z e. %s <-> ( Z e. CC /\\ -u 1 < ( Re ` Z ) ) )' % V1)],
           'mpbird', 'Z e. %s' % V1)
    qd = t([t([t([kn, zv], 'jca', '( k e. NN /\\ Z e. %s )' % V1), w.inst('z6hv1')], 'syl', '( ( ( Z / k ) + 1 ) e. %s /\\ ( Z + k ) =/= 0 )' % DD)], 'simpld',
           '( ( Z / k ) + 1 ) e. %s' % DD)
    ed = w.s([], 'eqid', '%s = %s' % (DD, DD))
    krp = t([kn], 'nnrpd', 'k e. RR+')
    k1rp = t([t([kn, w.inst('peano2nn')], 'syl', '( k + 1 ) e. NN')], 'nnrpd', '( k + 1 ) e. RR+')
    cck = t([t([t([k1rp, krp], 'rpdivcld', '( ( k + 1 ) / k ) e. RR+')], 'relogcld', '%s e. RR' % CK('k'))], 'recnd', '%s e. CC' % CK('k'))
    tc = t([t([rz, cck], 'mulcld', '( Z x. %s ) e. CC' % CK('k')),
            t([t([qd], 'eldifad', '( ( Z / k ) + 1 ) e. CC'), t([qd, w.s([ed], 'logdmn0', '( ( ( Z / k ) + 1 ) e. %s -> ( ( Z / k ) + 1 ) =/= 0 )' % DD)], 'syl', '( ( Z / k ) + 1 ) =/= 0')],
              'logcld', '( log ` ( ( Z / k ) + 1 ) ) e. CC')], 'subcld', '%s e. CC' % TK('k', 'Z'))
    sm = s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), c1(w, A0, '1z', '1 e. ZZ'), fv, tc, cv], 'isumclim', '%s = ( ( log_G ` Z ) + ( log ` Z ) )' % SK('Z'))
    lg = s([zd, w.inst('lgamcl')], 'syl', '( log_G ` Z ) e. CC')
    imp = w.s([w.s([w.s([], 'fveq2', '( Z = 0 -> ( Re ` Z ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( Z = 0 -> ( Re ` Z ) = 0 )')], 'necon3i',
              '( ( Re ` Z ) =/= 0 -> Z =/= 0 )')
    zn = s([s([zr], 'gt0ne0d', '( Re ` Z ) =/= 0'), imp], 'syl', 'Z =/= 0')
    lz = s([zc, zn], 'logcld', '( log ` Z ) e. CC')
    lgq = s([s([sm], 'oveq1d', '( %s - ( log ` Z ) ) = ( ( ( log_G ` Z ) + ( log ` Z ) ) - ( log ` Z ) )' % SK('Z')), s([lg, lz], 'pncand', '( ( ( log_G ` Z ) + ( log ` Z ) ) - ( log ` Z ) ) = ( log_G ` Z )')],
            'eqtrd', '( %s - ( log ` Z ) ) = ( log_G ` Z )' % SK('Z'))
    sc = s([sm, s([lg, lz], 'addcld', '( ( log_G ` Z ) + ( log ` Z ) ) e. CC')], 'eqeltrd', '%s e. CC' % SK('Z'))
    ch = s([s([s([s([zd, w.inst('eflgam')], 'syl', '( exp ` ( log_G ` Z ) ) = ( _G ` Z )')], 'eqcomd', '( _G ` Z ) = ( exp ` ( log_G ` Z ) )'), s([lgq], 'fveq2d', '( exp ` ( %s - ( log ` Z ) ) ) = ( exp ` ( log_G ` Z ) )' % SK('Z'))], 'eqtr4d',
              '( _G ` Z ) = ( exp ` ( %s - ( log ` Z ) ) )' % SK('Z')),
            s([sc, lz, w.inst('efsub')], 'syl2anc', '( exp ` ( %s - ( log ` Z ) ) ) = ( ( exp ` %s ) / ( exp ` ( log ` Z ) ) )' % (SK('Z'), SK('Z'))),
            s([s([zc, zn, w.inst('eflog')], 'syl2anc', '( exp ` ( log ` Z ) ) = Z')], 'oveq2d', '( ( exp ` %s ) / ( exp ` ( log ` Z ) ) ) = ( ( exp ` %s ) / Z )' % (SK('Z'), SK('Z')))],
           '3eqtrd', '( _G ` Z ) = ( ( exp ` %s ) / Z )' % SK('Z'))
    w.qed([sc, ch], 'jca', S_HGVAL)
    return run(w)


def gamhol():
    w = W('z6gamhol', 'The Gamma function is holomorphic on the open right half-plane: Lean\'s '
          '` Complex.differentiableAt_Gamma ` for ` 0 < Re z ` ( ~ z6hbxhol on boxes, ~ z6hexp , ~ holdiv , ~ holloc ).')
    Ay = 'y e. %s' % HPZ
    s = st(w, Ay)
    r0 = w.s([], '0re', '0 e. RR')
    bi0 = lambda a, X: w.s([w.s([r0, w.inst('elhp2')], 'ax-mp', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (X, HPZ, X, X))], 'a1i',
                           '( %s -> ( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) ) )' % (a, X, HPZ, X, X))
    both = s([w.s([], 'id', '( %s -> %s )' % (Ay, Ay)), bi0(Ay, 'y')], 'mpbid', '( y e. CC /\\ 0 < ( Re ` y ) )')
    yc = s([both], 'simpld', 'y e. CC'); ry0 = s([both], 'simprd', '0 < ( Re ` y )')
    ry = s([yc], 'recld', '( Re ` y ) e. RR'); iy = s([yc], 'imcld', '( Im ` y ) e. RR')
    ryp = s([ry, ry0], 'elrpd', '( Re ` y ) e. RR+')
    L0 = '( ( Re ` y ) / 2 )'; R0 = '( ( abs ` y ) + 1 )'
    Bx = BX(L0, R0)
    l0p = s([ryp], 'rphalfcld', '%s e. RR+' % L0)
    l0r = s([l0p], 'rpred', '%s e. RR' % L0)
    ay = s([yc], 'abscld', '( abs ` y ) e. RR')
    r0r = s([ay, c1(w, Ay, '1re', '1 e. RR')], 'readdcld', '%s e. RR' % R0)
    # y e. Bx
    l0lt = s([ryp, w.inst('rphalflt')], 'syl', '%s < ( Re ` y )' % L0)
    arl = s([s([s([ry], 'recnd', '( Re ` y ) e. CC')], 'abscld', '( abs ` ( Re ` y ) ) e. RR'), ay, r0r, s([yc, w.inst('absrele')], 'syl', '( abs ` ( Re ` y ) ) <_ ( abs ` y )'),
             s([ay], 'ltp1d', '( abs ` y ) < %s' % R0)], 'lelttrd', '( abs ` ( Re ` y ) ) < %s' % R0)
    ail = s([s([s([iy], 'recnd', '( Im ` y ) e. CC')], 'abscld', '( abs ` ( Im ` y ) ) e. RR'), ay, r0r, s([yc, w.inst('absimle')], 'syl', '( abs ` ( Im ` y ) ) <_ ( abs ` y )'),
             s([ay], 'ltp1d', '( abs ` y ) < %s' % R0)], 'lelttrd', '( abs ` ( Im ` y ) ) < %s' % R0)
    rp = s([arl, s([ry, r0r, w.inst('abslt')], 'syl2anc', '( ( abs ` ( Re ` y ) ) < %s <-> ( -u %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) )' % (R0, R0, R0))], 'mpbid',
           '( -u %s < ( Re ` y ) /\\ ( Re ` y ) < %s )' % (R0, R0))
    ip = s([ail, s([iy, r0r, w.inst('abslt')], 'syl2anc', '( ( abs ` ( Im ` y ) ) < %s <-> ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) )' % (R0, R0, R0))], 'mpbid',
           '( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s )' % (R0, R0))
    inb = s([yc, s([l0lt, s([rp], 'simprd', '( Re ` y ) < %s' % R0)], 'jca', '( %s < ( Re ` y ) /\\ ( Re ` y ) < %s )' % (L0, R0)), ip], '3jca',
            '( y e. CC /\\ ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) /\\ ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) )' % (L0, R0, R0, R0))
    ybx = s([s([s([l0r, r0r], 'jca', '( %s e. RR /\\ %s e. RR )' % (L0, R0)), inb], 'jca',
               '( ( %s e. RR /\\ %s e. RR ) /\\ ( y e. CC /\\ ( %s < ( Re ` y ) /\\ ( Re ` y ) < %s ) /\\ ( -u %s < ( Im ` y ) /\\ ( Im ` y ) < %s ) ) )' % (L0, R0, L0, R0, R0, R0)),
             w.inst('elbxr')], 'syl', 'y e. %s' % Bx)

    # points of Bx: complex with positive real part
    def pt(ante, stp, X):
        t = st(w, ante)
        el = t([stp, w.inst('elbxi')], 'syl', '( %s e. CC /\\ ( %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s ) /\\ ( -u %s < ( Im ` %s ) /\\ ( Im ` %s ) < %s ) )' % (X, L0, X, X, R0, R0, X, X, R0))
        xc = t([el, w.inst('simp1')], 'syl', '%s e. CC' % X)
        lx = t([t([el, w.inst('simp2')], 'syl', '( %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s )' % (L0, X, X, R0))], 'simpld', '%s < ( Re ` %s )' % (L0, X))
        lp = w.s([l0p], 'adantr', '( %s -> %s e. RR+ )' % (ante, L0))
        x0 = t([c1(w, ante, '0re', '0 e. RR'), t([lp], 'rpred', '%s e. RR' % L0), t([xc], 'recld', '( Re ` %s ) e. RR' % X), t([lp], 'rpgt0d', '0 < %s' % L0), lx],
               'lttrd', '0 < ( Re ` %s )' % X)
        return xc, x0
    Aw = '( %s /\\ w e. %s )' % (Ay, Bx)
    wc, w0 = pt(Aw, w.s([], 'simpr', '( %s -> w e. %s )' % (Aw, Bx)), 'w')
    whp = w.s([w.s([wc, w0], 'jca', '( %s -> ( w e. CC /\\ 0 < ( Re ` w ) ) )' % Aw), bi0(Aw, 'w')], 'mpbird', '( %s -> w e. %s )' % (Aw, HPZ))
    bss = s([w.s([whp], 'ex', '( %s -> ( w e. %s -> w e. %s ) )' % (Ay, Bx, HPZ))], 'ssrdv', '%s C_ %s' % (Bx, HPZ))
    # holomorphy of Gamma on Bx
    bo = c1(w, Ay, 'bxopn', '%s e. %s' % (Bx, TOP))
    SFz = '( z e. %s |-> %s )' % (Bx, SK('z'))
    SF = '( b e. %s |-> %s )' % (Bx, SK('b'))
    F1z = '( z e. %s |-> ( exp ` ( %s ` z ) ) )' % (Bx, SF)
    F1 = '( x e. %s |-> ( exp ` ( %s ` x ) ) )' % (Bx, SF)
    G1z = '( z e. %s |-> z )' % Bx
    G1 = '( x e. %s |-> x )' % Bx

    def cbv(bz, bx, Mz, Mx, v='x'):
        idk = w.s([], 'id', '( z = %s -> z = %s )' % (v, v))
        stp, new = w.congr(bz, {'z': v}, 'z = %s' % v, {'z': idk})
        assert new == bx, (new, bx)
        return w.s([w.s([stp if stp else idk], 'cbvmptv', '%s = %s' % (Mz, Mx))], 'a1i', '( %s -> %s = %s )' % (Ay, Mz, Mx))
    hsz = s([s([l0p, r0r], 'jca', '( %s e. RR+ /\\ %s e. RR )' % (L0, R0)), w.inst('z6hbxhol')], 'syl', HOLG(SFz, Bx))
    hs = holeq(w, Ay, SFz, SF, Bx, hsz, cbv(SK('z'), SK('b'), SFz, SF, 'b'))
    hez = s([hs, w.inst('z6hexp')], 'syl', HOLG(F1z, Bx))
    he = holeq(w, Ay, F1z, F1, Bx, hez, cbv('( exp ` ( %s ` z ) )' % SF, '( exp ` ( %s ` x ) )' % SF, F1z, F1))
    hiz = s([bo, w.inst('z6hid')], 'syl', HOLG(G1z, Bx))
    hi = holeq(w, Ay, G1z, G1, Bx, hiz, cbv('z', 'x', G1z, G1))
    Av = '( %s /\\ v e. %s )' % (Ay, Bx)
    vc, v0 = pt(Av, w.s([], 'simpr', '( %s -> v e. %s )' % (Av, Bx)), 'v')
    imp = w.s([w.s([w.s([], 'fveq2', '( v = 0 -> ( Re ` v ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( v = 0 -> ( Re ` v ) = 0 )')], 'necon3i',
              '( ( Re ` v ) =/= 0 -> v =/= 0 )')
    vn = w.s([w.s([v0], 'gt0ne0d', '( %s -> ( Re ` v ) =/= 0 )' % Av), imp], 'syl', '( %s -> v =/= 0 )' % Av)
    gv, _ = mpval(w, Av, 'x', Bx, 'x', 'v', w.s([], 'simpr', '( %s -> v e. %s )' % (Av, Bx)), exs=w.s([w.s([], 'vex', 'v e. _V')], 'a1i', '( %s -> v e. _V )' % Av))
    nz = w.s([w.s([gv, vn], 'eqnetrd', '( %s -> ( %s ` v ) =/= 0 )' % (Av, G1))], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) =/= 0 )' % (Ay, Bx, G1))
    DV = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (Bx, F1, G1)
    hd = s([he, hi, nz, w.inst('holdiv')], 'syl3anc', HOLG(DV, Bx))
    # the quotient is Gamma
    Az = '( %s /\\ z e. %s )' % (Ay, Bx)
    zb = w.s([], 'simpr', '( %s -> z e. %s )' % (Az, Bx))
    zc, z0 = pt(Az, zb, 'z')
    t = st(w, Az)
    f1z, _ = mpval(w, Az, 'x', Bx, '( exp ` ( %s ` x ) )' % SF, 'z', zb)
    g1z, _ = mpval(w, Az, 'x', Bx, 'x', 'z', zb, exs=w.s([w.s([], 'vex', 'z e. _V')], 'a1i', '( %s -> z e. _V )' % Az))
    # sum value: from the Gamma value lemma
    gv2 = t([t([zc, z0], 'jca', '( z e. CC /\\ 0 < ( Re ` z ) )'), w.inst('z6hgval')], 'syl', '( %s e. CC /\\ ( _G ` z ) = ( ( exp ` %s ) / z ) )' % (SK('z'), SK('z')))
    gz = t([gv2], 'simprd', '( _G ` z ) = ( ( exp ` %s ) / z )' % SK('z'))
    # ( SF ` z ) = sum: need the sum in CC -- it is ( SF ` z ) itself once the value is known
    sfv, _ = mpval(w, Az, 'b', Bx, SK('b'), 'z', zb, exs=t([t([gv2], 'simpld', '%s e. CC' % SK('z'))], 'elexd', '%s e. _V' % SK('z')))
    q = t([t([f1z, t([sfv], 'fveq2d', '( exp ` ( %s ` z ) ) = ( exp ` %s )' % (SF, SK('z')))], 'eqtrd', '( %s ` z ) = ( exp ` %s )' % (F1, SK('z'))), g1z], 'oveq12d',
          '( ( %s ` z ) / ( %s ` z ) ) = ( ( exp ` %s ) / z )' % (F1, G1, SK('z')))
    qg = t([q, gz], 'eqtr4d', '( ( %s ` z ) / ( %s ` z ) ) = ( _G ` z )' % (F1, G1))
    GB = '( z e. %s |-> ( _G ` z ) )' % Bx
    eqm = s([qg], 'mpteq2dva', '%s = %s' % (DV, GB))
    hg = holeq(w, Ay, DV, GB, Bx, hd, eqm)
    res = s([bss, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (GH, Bx, GB))
    dss = s([s([hg], 'simprd', '%s C_ dom ( CC _D %s )' % (Bx, GB)),
             s([s([res], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D %s )' % (GH, Bx, GB))], 'dmeqd', 'dom ( CC _D ( %s |` %s ) ) = dom ( CC _D %s )' % (GH, Bx, GB))],
            'sseqtrrd', '%s C_ dom ( CC _D ( %s |` %s ) )' % (Bx, GH, Bx))
    LOC = lambda u: '( y e. %s /\\ %s C_ %s /\\ %s C_ dom ( CC _D ( %s |` %s ) ) )' % (u, u, HPZ, u, GH, u)
    sub = w.s([w.s([], 'eleq2', '( u = %s -> ( y e. u <-> y e. %s ) )' % (Bx, Bx)), w.s([], 'sseq1', '( u = %s -> ( u C_ %s <-> %s C_ %s ) )' % (Bx, HPZ, Bx, HPZ)),
               w.s([w.s([], 'id', '( u = %s -> u = %s )' % (Bx, Bx)), w.s([w.s([w.s([], 'reseq2', '( u = %s -> ( %s |` u ) = ( %s |` %s ) )' % (Bx, GH, GH, Bx))], 'oveq2d',
                                                                              '( u = %s -> ( CC _D ( %s |` u ) ) = ( CC _D ( %s |` %s ) ) )' % (Bx, GH, GH, Bx))], 'dmeqd',
                                                                         '( u = %s -> dom ( CC _D ( %s |` u ) ) = dom ( CC _D ( %s |` %s ) ) )' % (Bx, GH, GH, Bx))], 'sseq12d',
                   '( u = %s -> ( u C_ dom ( CC _D ( %s |` u ) ) <-> %s C_ dom ( CC _D ( %s |` %s ) ) ) )' % (Bx, GH, Bx, GH, Bx))], '3anbi123d',
              '( u = %s -> ( %s <-> %s ) )' % (Bx, LOC('u'), LOC(Bx)))
    ex = s([s([bo, s([ybx, bss, dss], '3jca', LOC(Bx))], 'jca', '( %s e. %s /\\ %s )' % (Bx, TOP, LOC(Bx))),
            w.s([sub], 'rspcev', '( ( %s e. %s /\\ %s ) -> E. u e. %s %s )' % (Bx, TOP, LOC(Bx), TOP, LOC('u')))], 'syl', 'E. u e. %s %s' % (TOP, LOC('u')))
    ral = w.s([ex], 'rgen', 'A. y e. %s E. u e. %s %s' % (HPZ, TOP, LOC('u')))
    # G : HPZ --> CC
    Az2 = 'z e. %s' % HPZ
    b2 = w.s([w.s([], 'id', '( %s -> %s )' % (Az2, Az2)), bi0(Az2, 'z')], 'mpbid', '( %s -> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % Az2)
    gc = w.s([w.s([b2, w.inst('zrenn')], 'syl', '( %s -> z e. %s )' % (Az2, DG)), w.inst('gamcl')], 'syl', '( %s -> ( _G ` z ) e. CC )' % Az2)
    gf = w.s([gc], 'fmpti', '%s : %s --> CC' % (GH, HPZ))
    pre = w.s([w.s([gf, w.s([], 'hpss', '%s C_ CC' % HPZ)], 'pm3.2i', '( %s : %s --> CC /\\ %s C_ CC )' % (GH, HPZ, HPZ)), ral], 'pm3.2i',
              '( ( %s : %s --> CC /\\ %s C_ CC ) /\\ A. y e. %s E. u e. %s %s )' % (GH, HPZ, HPZ, HPZ, TOP, LOC('u')))
    w.qed([pre, w.inst('holloc')], 'ax-mp', STATEMENTS['z6gamhol'])
    return run(w)


if __name__ == '__main__':
    want = sys.argv[1:]
    for lab, fn in [('z6hgval', hgval), ('z6gamhol', gamhol)]:
        if lab in want:
            if fn():
                status(lab)
