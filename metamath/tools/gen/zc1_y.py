"""Sortie ZC1: abs of the chi Lam series is at most the Lam series at Re Z (lvmabs; the first half of C7b's lvmbnd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
import congr as _cg
from cl import lift
from c8_o import numst
import c7b_lch as L7
from c7blib import NX as NX7, RZ, ZP1, VMT, RVT
NXZ = L7.NXZ
import lin
lin.FASTPATH = True

S['lvmabs'] = '( %s -> ( abs ` sum_ k e. NN %s ) <_ sum_ k e. NN %s )' % (NXZ, VMT('k'), RVT('k', RZ))


def gen_lvmabs():
    w = W('lvmabs', 'The ` chi Lam ` Dirichlet series is at most the ` Lam ` series at ` Re Z ` in modulus, ` 1 < Re Z ` ( ~ iserabs , ~ lchvmtm ; the first half of ~ lvmbnd without ` Re Z <_ 2 ` ).')
    A0 = NXZ
    nx = w.s([], 'simpl', '( %s -> %s )' % (A0, NX7))
    zc = w.s([], 'simprl', '( %s -> Z e. CC )' % A0)
    z1 = w.s([], 'simprr', '( %s -> 1 < %s )' % (A0, RZ))
    rz = w.s([zc], 'recld', '( %s -> %s e. RR )' % (A0, RZ))
    nxz = w.s([], 'id', '( %s -> %s )' % (A0, NXZ))
    F = '( n e. NN |-> %s )' % VMT('n')
    G = '( n e. NN |-> ( abs ` %s ) )' % VMT('n')
    H = '( n e. NN |-> %s )' % RVT('n', RZ)
    fcv = w.s([nxz, w.inst('lchvmcvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, F))
    gcv = w.s([nxz, w.inst('lchvmacvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, G))
    hcv = w.s([w.s([rz, z1], 'jca', '( %s -> ( %s e. RR /\\ 1 < %s ) )' % (A0, RZ, RZ)), w.inst('vmsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, H))
    Ak = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    nxk = w.s([nx], 'adantr', '( %s -> %s )' % (Ak, NX7))
    zck = w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak)
    vc = L7.vmtcl(w, Ak, 'k', nxk, kn, zck)
    avr = w.s([vc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ak, VMT('k')))
    krp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % Ak)
    pr = w.s([krp, w.s([w.s([rz], 'adantr', '( %s -> %s e. RR )' % (Ak, RZ))], 'renegcld', '( %s -> -u %s e. RR )' % (Ak, RZ))], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (Ak, RZ))
    rvr = w.s([w.s([kn, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` k ) e. RR )' % Ak), w.s([pr], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (Ak, RZ))], 'remulcld', '( %s -> %s e. RR )' % (Ak, RVT('k', RZ)))
    vf, _ = L7.val(w, Ak, VMT('n'), 'k', kn, L7.ex_(w, Ak, VMT('k'), vc))
    vg, _ = L7.val(w, Ak, '( abs ` %s )' % VMT('n'), 'k', kn, L7.ex_(w, Ak, '( abs ` %s )' % VMT('k'), w.s([avr], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Ak, VMT('k')))))
    vh, _ = L7.val(w, Ak, RVT('n', RZ), 'k', kn, L7.ex_(w, Ak, RVT('k', RZ), w.s([rvr], 'recnd', '( %s -> %s e. CC )' % (Ak, RVT('k', RZ)))))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % A0)
    SV = 'sum_ k e. NN %s' % VMT('k'); SA = 'sum_ k e. NN ( abs ` %s )' % VMT('k'); SR = 'sum_ k e. NN %s' % RVT('k', RZ)
    lf = w.s([nnuz, one, vf, vc, fcv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, F, SV))
    lg = w.s([nnuz, one, vg, w.s([avr], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Ak, VMT('k'))), gcv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (A0, G, SA))
    fkc = w.s([vf, vc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, F))
    gk = w.s([vg, w.s([vf], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` %s ) )' % (Ak, F, VMT('k')))], 'eqtr4d', '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, G, F))
    ia = w.s([nnuz, lf, lg, one, fkc, gk], 'iserabs', '( %s -> ( abs ` %s ) <_ %s )' % (A0, SV, SA))
    tm = w.s([w.s([nxk, w.s([kn, zck], 'jca', '( %s -> ( k e. NN /\\ Z e. CC ) )' % Ak)], 'jca', '( %s -> ( %s /\\ ( k e. NN /\\ Z e. CC ) ) )' % (Ak, NX7)), w.inst('lchvmtm')], 'syl',
             '( %s -> ( abs ` %s ) <_ %s )' % (Ak, VMT('k'), RVT('k', RZ)))
    il = w.s([nnuz, one, vg, avr, vh, rvr, tm, gcv, hcv], 'isumle', '( %s -> %s <_ %s )' % (A0, SA, SR))
    w.qed([ia, il], 'letrd' if False else 'x', S['lvmabs']) if False else None
    sar = w.s([nnuz, one, vg, avr, gcv], 'isumrecl', '( %s -> %s e. RR )' % (A0, SA))
    srr = w.s([nnuz, one, vh, rvr, hcv], 'isumrecl', '( %s -> %s e. RR )' % (A0, SR))
    avr0 = w.s([w.s([nnuz, one, vf, vc, fcv], 'isumcl', '( %s -> %s e. CC )' % (A0, SV))], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, SV))
    w.qed([avr0, sar, srr, ia, il], 'letrd', S['lvmabs'])
    return run8(w)




import c9_h
patch(c9_h)
from c9_h import lf_hol
import zc1_x

S['lchrldre'] = ('( ( %s /\\ ( ( U e. RR+ /\\ U <_ 1 ) /\\ ( S e. CC /\\ ( Re ` S ) = ( 1 + U ) ) ) ) -> '
                 '( abs ` ( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) ) <_ ( ( ( 5 / 4 ) / U ) + 5 ) )') % (CHI, LFN, LFN)


def gen_lchrldre():
    w = W('lchrldre', 'Lean ` norm_logDeriv_le_of_re_eq ` : for ` chi ` nonprincipal and ` Re S = 1 + u ` , ` 0 < u <_ 1 ` , ` abs ( L \' / L ) ( S ) <_ ( 5 / 4 ) / u + 5 ` (Lean ` 1 / w + 2 ` ; ~ dvres , ~ lchrlogdv , ~ lvmabs , ~ vmsharp ).')
    A0 = ante_of(S['lchrldre'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    uu = s([], 'simprl', '( U e. RR+ /\\ U <_ 1 )'); sd = s([], 'simprr', '( S e. CC /\\ ( Re ` S ) = ( 1 + U ) )')
    up = s([uu, w.inst('simpl')], 'syl', 'U e. RR+'); ur = s([up], 'rpred', 'U e. RR')
    sc = s([sd, w.inst('simpl')], 'syl', 'S e. CC'); rs = s([sd, w.inst('simpr')], 'syl', '( Re ` S ) = ( 1 + U )')
    nx = s([chi, w.inst('simpl')], 'syl', NX)
    T = '( 1 + ( U / 2 ) )'
    tr = s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), s([s([up, w.inst('rphalfcld')], 'syl', '( U / 2 ) e. RR+')], 'rpred', '( U / 2 ) e. RR')], 'readdcld', '%s e. RR' % T)
    lvu = {'U': ur}
    t1 = lin8(w, A0, [s([up], 'rpgt0d', '0 < U')], '1 < %s' % T, lvu)
    Wd = "( `' Re \" ( %s (,) +oo ) )" % T
    rsr = s([sc], 'recld', '( Re ` S ) e. RR')
    sw = s([s([sc, lin8(w, A0, [rs, s([up], 'rpgt0d', '0 < U')], '%s < ( Re ` S )' % T, {'U': ur, '( Re ` S )': rsr})], 'jca', '( S e. CC /\\ %s < ( Re ` S ) )' % T),
            s([tr, w.inst('elhp2')], 'syl', '( S e. %s <-> ( S e. CC /\\ %s < ( Re ` S ) ) )' % (Wd, T))], 'mpbird', 'S e. %s' % Wd)
    # W C_ HP0
    Az = '( %s /\\ z e. %s )' % (A0, Wd)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zz = sz([sz([], 'simpr', 'z e. %s' % Wd), sz([lift(w, tr, Az), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ %s < ( Re ` z ) ) )' % (Wd, T))], 'mpbid', '( z e. CC /\\ %s < ( Re ` z ) )' % T)
    zc = sz([zz, w.inst('simpl')], 'syl', 'z e. CC'); zt = sz([zz, w.inst('simpr')], 'syl', '%s < ( Re ` z )' % T)
    rzr = sz([zc], 'recld', '( Re ` z ) e. RR')
    z0 = lin8(w, Az, [zt, lift(w, t1, Az)], '0 < ( Re ` z )', {'U': lift(w, ur, Az), '( Re ` z )': rzr})
    z1 = lin8(w, Az, [zt, lift(w, t1, Az)], '1 < ( Re ` z )', {'U': lift(w, ur, Az), '( Re ` z )': rzr})
    zh = sz([sz([zc, z0], 'jca', '( z e. CC /\\ 0 < ( Re ` z ) )'), sz([sz([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % HP0)],
            'mpbird', 'z e. %s' % HP0)
    wss = s([w.s([zh], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (A0, Wd, HP0))], 'ssrdv', '%s C_ %s' % (Wd, HP0))
    DSX = lambda z: 'sum_ k e. NN ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u %s ) )' % z
    DSM = '( z e. %s |-> %s )' % (Wd, DSX('z'))
    LSW = '( s e. %s |-> %s )' % (Wd, LSs('s'))
    rm = s([wss, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (LFN, Wd, LSW))
    As = '( %s /\\ s e. %s )' % (A0, Wd)
    ss_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (As, f))
    szz = ss_([ss_([], 'simpr', 's e. %s' % Wd), ss_([lift(w, tr, As), w.inst('elhp2')], 'syl', '( s e. %s <-> ( s e. CC /\\ %s < ( Re ` s ) ) )' % (Wd, T))], 'mpbid', '( s e. CC /\\ %s < ( Re ` s ) )' % T)
    s1 = lin8(w, As, [ss_([szz, w.inst('simpr')], 'syl', '%s < ( Re ` s )' % T), lift(w, t1, As)], '1 < ( Re ` s )', {'U': lift(w, ur, As), '( Re ` s )': ss_([ss_([szz, w.inst('simpl')], 'syl', 's e. CC')], 'recld', '( Re ` s ) e. RR')})
    ag = ss_([ss_([lift(w, chi, As), ss_([ss_([szz, w.inst('simpl')], 'syl', 's e. CC'), s1], 'jca', '( s e. CC /\\ 1 < ( Re ` s ) )')], 'jca', '( %s /\\ ( s e. CC /\\ 1 < ( Re ` s ) ) )' % CHI), w.inst('lchragr')],
             'syl', '%s = %s' % (LSs('s'), DSX('s')))
    me = s([ag], 'mpteq2dva', '%s = ( s e. %s |-> %s )' % (LSW, Wd, DSX('s')))
    cb = s([w.s([w.s([w.s([w.s([w.s([], 'negeq', '( s = z -> -u s = -u z )')], 'oveq2d', '( s = z -> ( k ^c -u s ) = ( k ^c -u z ) )')], 'oveq2d',
                                  '( s = z -> ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u s ) ) = ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) ) x. ( k ^c -u z ) ) )')], 'sumeq2sdv',
                           '( s = z -> %s = %s )' % (DSX('s'), DSX('z')))], 'cbvmptv', '( s e. %s |-> %s ) = %s' % (Wd, DSX('s'), DSM))], 'a1i', '( s e. %s |-> %s ) = %s' % (Wd, DSX('s'), DSM))
    resq = s([s([rm, me], 'eqtrd', '( %s |` %s ) = ( s e. %s |-> %s )' % (LFN, Wd, Wd, DSX('s'))), cb], 'eqtrd', '( %s |` %s ) = %s' % (LFN, Wd, DSM))
    hol = lf_hol(w, A0, chi)
    lff = s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0))
    hpc = s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncfrss')], 'syl', '%s C_ CC' % HP0)
    wcc = s([wss, hpc], 'sstrd', '%s C_ CC' % Wd)
    K = '( TopOpen ` CCfld )'
    k_ = w.s([], 'eqid', '%s = %s' % (K, K))
    tk = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (K, K))], 'eqcomi', '%s = ( %s |`t CC )' % (K, K))
    dv = s([s([s([s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), lff], 'jca', '( CC C_ CC /\\ %s : %s --> CC )' % (LFN, HP0)), s([hpc, wcc], 'jca', '( %s C_ CC /\\ %s C_ CC )' % (HP0, Wd))], 'jca',
               '( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) )' % (LFN, HP0, HP0, Wd)), w.s([k_, tk], 'dvres', '( ( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (LFN, HP0, HP0, Wd, LFN, Wd, LFN, K, Wd))],
           'syl', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) )' % (LFN, Wd, LFN, K, Wd))
    iw = s([s([w.s([w.s([], 'eqid', '%s = %s' % (K, K))], 'cnfldtop', '%s e. Top' % K)], 'a1i', '%s e. Top' % K), s([w.s([], 'hpopn', '%s e. %s' % (Wd, K))], 'a1i', '%s e. %s' % (Wd, K)), w.inst('isopn3i')],
           'syl2anc', '( ( int ` %s ) ` %s ) = %s' % (K, Wd, Wd))
    dv2 = s([dv, s([iw], 'reseq2d', '( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) = ( ( CC _D %s ) |` %s )' % (LFN, K, Wd, LFN, Wd))], 'eqtrd', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s )' % (LFN, Wd, LFN, Wd))
    dv3 = s([s([s([resq], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D %s )' % (LFN, Wd, DSM))], 'eqcomd', '( CC _D %s ) = ( CC _D ( %s |` %s ) )' % (DSM, LFN, Wd)), dv2], 'eqtrd',
            '( CC _D %s ) = ( ( CC _D %s ) |` %s )' % (DSM, LFN, Wd))
    dS = s([s([dv3], 'fveq1d', '( ( CC _D %s ) ` S ) = ( ( ( CC _D %s ) |` %s ) ` S )' % (DSM, LFN, Wd)), s([sw, w.inst('fvres')], 'syl', '( ( ( CC _D %s ) |` %s ) ` S ) = ( ( CC _D %s ) ` S )' % (LFN, Wd, LFN))],
           'eqtrd', '( ( CC _D %s ) ` S ) = ( ( CC _D %s ) ` S )' % (DSM, LFN))
    # value of L at S
    shp = s([wss, sw], 'sseldd', 'S e. %s' % HP0)
    lv, _ = _cg.mptval(w, A0, 's', HP0, LSs('s'), 'S', shp, exs=s([w.s([], 'sumex', '%s e. _V' % LSs('S'))], 'a1i', '%s e. _V' % LSs('S')), gen=w.g)
    s1S = lin8(w, A0, [rs, s([up], 'rpgt0d', '0 < U')], '1 < ( Re ` S )', {'U': ur, '( Re ` S )': rsr})
    agS = s([s([chi, s([sc, s1S], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', '( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % CHI), w.inst('lchragr')], 'syl', '%s = %s' % (LSs('S'), DSX('S')))
    lS = s([lv, agS], 'eqtrd', '( %s ` S ) = %s' % (LFN, DSX('S')))
    LD = tsub(stmt('lchrlogdv'), {'T': T, 'Z': 'S'})
    lda, ldc = ante_of(LD)
    ld = s([s([nx, s([s([tr, t1], 'jca', '( %s e. RR /\\ 1 < %s )' % (T, T)), sw], 'jca', top_and(lda)[1])], 'jca', lda), w.inst('lchrlogdv')], 'syl', ldc)
    VS = ldc.split(' = -u ', 1)[1][:-2] if False else ldc.rsplit(' = -u ', 1)[1]
    lSr = s([lS], 'eqcomd', '%s = ( %s ` S )' % (DSX('S'), LFN))
    rat = s([s([dS, lSr], 'oveq12d', '( ( ( CC _D %s ) ` S ) / %s ) = ( ( ( CC _D %s ) ` S ) / ( %s ` S ) )' % (DSM, DSX('S'), LFN, LFN))], 'eqcomd',
            '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( ( ( CC _D %s ) ` S ) / %s )' % (LFN, LFN, DSM, DSX('S')))
    rat2 = s([rat, ld], 'eqtrd', '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = -u %s' % (LFN, LFN, VS))
    LVA = tsub(S['lvmabs'], {'Z': 'S'})
    lvaa, lvac = ante_of(LVA)
    lva = s([s([nx, s([sc, s1S], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', lvaa), w.inst('lvmabs')], 'syl', lvac)
    RVS = lvac.split(' <_ ', 1)[1]
    VM = 'sum_ k e. NN ( ( Lam ` k ) x. ( k ^c -u ( 1 + U ) ) )'
    rv = s([s([s([rs], 'negeqd', '-u ( Re ` S ) = -u ( 1 + U )')], 'oveq2d', '( k ^c -u ( Re ` S ) ) = ( k ^c -u ( 1 + U ) )')], 'x', 'x') if False else None
    rvs = s([s([s([s([rs], 'negeqd', '-u ( Re ` S ) = -u ( 1 + U )')], 'oveq2d', '( k ^c -u ( Re ` S ) ) = ( k ^c -u ( 1 + U ) )')], 'oveq2d',
                '( ( Lam ` k ) x. ( k ^c -u ( Re ` S ) ) ) = ( ( Lam ` k ) x. ( k ^c -u ( 1 + U ) ) )')], 'sumeq2sdv', '%s = %s' % (RVS, VM))
    vm = s([uu, w.inst('vmsharp')], 'syl', '%s <_ ( ( ( 5 / 4 ) / U ) + 5 )' % VM)
    b1 = s([s([lva, rvs], 'breqtrd', '( abs ` %s ) <_ %s' % (VS, VM)), vm], 'x', 'x') if False else None
    b1 = s([lva, rvs], 'breqtrd', '( abs ` %s ) <_ %s' % (VS, VM))
    Ak = '( %s /\\ k e. NN )' % A0
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    kn = sk([], 'simpr', 'k e. NN')
    CHK = '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` k ) )'
    xk = sk([sk([lift(w, nx, Ak), kn], 'jca', '( %s /\\ k e. NN )' % NX), w.inst('lchrcl')], 'syl', '%s e. CC' % CHK)
    lk = sk([sk([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    kz = sk([sk([kn], 'nncnd', 'k e. CC'), sk([lift(w, sc, Ak)], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')
    VK = '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u S ) )' % CHK
    vk = sk([sk([xk, lk], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CHK), kz], 'mulcld', '%s e. CC' % VK)
    VN = '( ( ( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` n ) ) x. ( Lam ` n ) ) x. ( n ^c -u S ) )'
    fv, _ = _cg.mptval(w, Ak, 'n', 'NN', VN, 'k', kn, exs=sk([vk], 'elexd', '%s e. _V' % VK), gen=w.g)
    cvg = s([s([nx, s([sc, s1S], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', '( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % NX), w.inst('lchvmcvg')], 'syl',
            'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % VN)
    vsc = s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([], '1zzd', '1 e. ZZ'), fv, vk, cvg], 'isumcl', '%s e. CC' % VS)
    AL = '( abs ` ( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) )' % (LFN, LFN)
    an = s([vsc], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (VS, VS))
    al = s([s([rat2], 'fveq2d', '%s = ( abs ` -u %s )' % (AL, VS)), an], 'eqtrd', '%s = ( abs ` %s )' % (AL, VS))
    avr = s([vsc], 'abscld', '( abs ` %s ) e. RR' % VS)
    vmr = s([uu, w.inst('vmsharp')], 'syl', '%s <_ ( ( ( 5 / 4 ) / U ) + 5 )' % VM)
    vmrr = s([s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([], '1zzd', '1 e. ZZ'), ], 'x', 'x') if False else None], 'x', 'x') if False else None
    lx = w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')
    b2x = s([s([vmr, w.s([lx], 'brel', '( %s <_ ( ( ( 5 / 4 ) / U ) + 5 ) -> ( %s e. RR* /\\ ( ( ( 5 / 4 ) / U ) + 5 ) e. RR* ) )' % (VM, VM))], 'syl', '( %s e. RR* /\\ ( ( ( 5 / 4 ) / U ) + 5 ) e. RR* )' % VM),
             w.inst('simpl')], 'syl', '%s e. RR*' % VM)
    gbr = s([s([numst(w, A0, '( 5 / 4 )', 'RR'), up], 'rerpdivcld', '( ( 5 / 4 ) / U ) e. RR'), numst(w, A0, '5', 'RR')], 'readdcld', '( ( ( 5 / 4 ) / U ) + 5 ) e. RR')
    fin0 = s([s([avr], 'rexrd', '( abs ` %s ) e. RR*' % VS), b2x, s([gbr], 'rexrd', '( ( ( 5 / 4 ) / U ) + 5 ) e. RR*'), b1, vmr], 'xrletrd', '( abs ` %s ) <_ ( ( ( 5 / 4 ) / U ) + 5 )' % VS)
    fin = s([al, fin0], 'eqbrtrd', '%s <_ ( ( ( 5 / 4 ) / U ) + 5 )' % AL)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['lchrldre']))
    return run8(w)


if __name__ == '__main__':
    gen_lvmabs()
    gen_lchrldre()

