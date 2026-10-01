"""Sortie EF56: logDeriv_eta_split (ef5lds)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from cl import lift, Closure
import congr as _cg
from c8_o import numst
from zc1_r import EB
import lin
lin.FASTPATH = True

K_ = '( TopOpen ` CCfld )'


def dres(w, A0, M, D, holst, Wd, wss, sw):
    """( A0 -> ( ( CC _D ( M |` Wd ) ) ` S ) = ( ( CC _D M ) ` S ) ) and ( A0 -> S e. dom ( CC _D ( M |` Wd ) ) )
    for holst : ( A0 -> HOLF(M, D) ), wss : Wd C_ D, sw : S e. Wd, Wd open"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    mf = s([s([holst, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (M, D)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (M, D))
    dc = s([s([holst, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (M, D)), w.inst('cncfrss')], 'syl', '%s C_ CC' % D)
    wcc = s([wss, dc], 'sstrd', '%s C_ CC' % Wd)
    k_ = w.s([], 'eqid', '%s = %s' % (K_, K_))
    tk = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (K_, K_))], 'eqcomi', '%s = ( %s |`t CC )' % (K_, K_))
    HY = '( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) )' % (M, D, D, Wd)
    dv = s([s([s([s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), mf], 'jca', '( CC C_ CC /\\ %s : %s --> CC )' % (M, D)), s([dc, wcc], 'jca', '( %s C_ CC /\\ %s C_ CC )' % (D, Wd))], 'jca', HY),
            w.s([k_, tk], 'dvres', '( %s -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (HY, M, Wd, M, K_, Wd))],
           'syl', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) )' % (M, Wd, M, K_, Wd))
    iw = s([s([w.s([w.s([], 'eqid', '%s = %s' % (K_, K_))], 'cnfldtop', '%s e. Top' % K_)], 'a1i', '%s e. Top' % K_), s([w.s([], 'hpopn', '%s e. %s' % (Wd, K_))], 'a1i', '%s e. %s' % (Wd, K_)), w.inst('isopn3i')],
           'syl2anc', '( ( int ` %s ) ` %s ) = %s' % (K_, Wd, Wd))
    dv2 = s([dv, s([iw], 'reseq2d', '( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) = ( ( CC _D %s ) |` %s )' % (M, K_, Wd, M, Wd))], 'eqtrd', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s )' % (M, Wd, M, Wd))
    val = s([s([dv2], 'fveq1d', '( ( CC _D ( %s |` %s ) ) ` S ) = ( ( ( CC _D %s ) |` %s ) ` S )' % (M, Wd, M, Wd)), s([sw, w.inst('fvres')], 'syl', '( ( ( CC _D %s ) |` %s ) ` S ) = ( ( CC _D %s ) ` S )' % (M, Wd, M))],
            'eqtrd', '( ( CC _D ( %s |` %s ) ) ` S ) = ( ( CC _D %s ) ` S )' % (M, Wd, M))
    sd = s([s([holst, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D %s )' % (D, M)), s([wss, sw], 'sseldd', 'S e. %s' % D)], 'sseldd', 'S e. dom ( CC _D %s )' % M)
    dmr = s([s([dv2], 'dmeqd', 'dom ( CC _D ( %s |` %s ) ) = dom ( ( CC _D %s ) |` %s )' % (M, Wd, M, Wd)), s([w.s([], 'dmres', 'dom ( ( CC _D %s ) |` %s ) = ( %s i^i dom ( CC _D %s ) )' % (M, Wd, Wd, M))], 'a1i',
                                                                                                              'dom ( ( CC _D %s ) |` %s ) = ( %s i^i dom ( CC _D %s ) )' % (M, Wd, Wd, M))],
            'eqtrd', 'dom ( CC _D ( %s |` %s ) ) = ( %s i^i dom ( CC _D %s ) )' % (M, Wd, Wd, M))
    inn = s([s([sw, sd], 'jca', '( S e. %s /\\ S e. dom ( CC _D %s ) )' % (Wd, M)), s([w.s([], 'elin', '( S e. ( %s i^i dom ( CC _D %s ) ) <-> ( S e. %s /\\ S e. dom ( CC _D %s ) ) )' % (Wd, M, Wd, M))], 'a1i',
                                                                                     '( S e. ( %s i^i dom ( CC _D %s ) ) <-> ( S e. %s /\\ S e. dom ( CC _D %s ) ) )' % (Wd, M, Wd, M))], 'mpbird', 'S e. ( %s i^i dom ( CC _D %s ) )' % (Wd, M))
    dom = s([inn, s([dmr], 'eqcomd', '( %s i^i dom ( CC _D %s ) ) = dom ( CC _D ( %s |` %s ) )' % (Wd, M, M, Wd))], 'eleqtrd', 'S e. dom ( CC _D ( %s |` %s ) )' % (M, Wd))
    return val, dom, mf, wcc


def gen_lds():
    w = W('ef5lds', 'Lean ` logDeriv_eta_split ` : on ` Re s > 1 ` , ` eta \' / eta = g \' / g + zeta \' / zeta ` with ` zeta \' / zeta = - sum Lam ( k ) k ^ - s ` ( ~ etazser , ~ dvmul , ~ lchrlogdv at the character mod 1).')
    A0 = ante_of(S['ef5lds'])[0]
    c = Ctx(w, A0)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    sc = c.g('S e. CC'); s1 = c.g('1 < ( Re ` S )')
    rsr = c([sc], 'recld', '( Re ` S ) e. RR')
    T = '( ( 1 + ( Re ` S ) ) / 2 )'
    tr = c([c([numst(w, A0, '1', 'RR'), rsr], 'readdcld', '( 1 + ( Re ` S ) ) e. RR')], 'rehalfcld', '%s e. RR' % T)
    lvS = {'( Re ` S )': rsr}
    t1 = lin8(w, A0, [s1], '1 < %s' % T, lvS)
    Wd = "( `' Re \" ( %s (,) +oo ) )" % T
    sw = c([c([sc, lin8(w, A0, [s1], '%s < ( Re ` S )' % T, lvS)], 'jca', '( S e. CC /\\ %s < ( Re ` S ) )' % T),
            c([tr, w.inst('elhp2')], 'syl', '( S e. %s <-> ( S e. CC /\\ %s < ( Re ` S ) ) )' % (Wd, T))], 'mpbird', 'S e. %s' % Wd)
    Az = '( %s /\\ z e. %s )' % (A0, Wd)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zz = sz([sz([], 'simpr', 'z e. %s' % Wd), sz([lift(w, tr, Az), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ %s < ( Re ` z ) ) )' % (Wd, T))], 'mpbid', '( z e. CC /\\ %s < ( Re ` z ) )' % T)
    zc = sz([zz, w.inst('simpl')], 'syl', 'z e. CC'); zt = sz([zz, w.inst('simpr')], 'syl', '%s < ( Re ` z )' % T)
    rzr = sz([zc], 'recld', '( Re ` z ) e. RR')
    lvz = {'( Re ` S )': lift(w, rsr, Az), '( Re ` z )': rzr}
    z0 = lin8(w, Az, [zt, lift(w, s1, Az)], '0 < ( Re ` z )', lvz)
    z1 = lin8(w, Az, [zt, lift(w, s1, Az)], '1 < ( Re ` z )', lvz)
    zh = sz([sz([zc, z0], 'jca', '( z e. CC /\\ 0 < ( Re ` z ) )'), sz([sz([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ 0 < ( Re ` z ) ) )' % HP0)],
            'mpbird', 'z e. %s' % HP0)
    wss = s([w.s([zh], 'ex', '( %s -> ( z e. %s -> z e. %s ) )' % (A0, Wd, HP0))], 'ssrdv', '%s C_ %s' % (Wd, HP0))
    sh = s([wss, sw], 'sseldd', 'S e. %s' % HP0)
    # the objects
    CH = lambda k: '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` %s ) )' % (U1, k)
    DSX = lambda z: 'sum_ k e. NN ( %s x. ( k ^c -u %s ) )' % (CH('k'), z)
    ZSUM = lambda z: 'sum_ k e. NN ( k ^c -u %s )' % z
    DSM = '( z e. %s |-> %s )' % (Wd, DSX('z'))
    GB = '( 1 - ( 2 ^c ( 1 - z ) ) )'
    F1 = '( z e. %s |-> %s )' % (Wd, GB)
    nx = nx1(w, A0)
    hl = s([s([nx, s([tr, t1], 'jca', '( %s e. RR /\\ 1 < %s )' % (T, T))], 'jca', '( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ ( %s e. RR /\\ 1 < %s ) )' % (U1, T, T)), w.inst('lchrhol')], 'syl', HOLF(DSM, Wd))
    # conversion sum_ X ( k ) k ^ -u z = sum_ k ^ -u z
    def conv(ante, zst, zv):
        Ak = '( %s /\\ k e. NN )' % ante
        sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
        kn = sk([], 'simpr', 'k e. NN')
        x1 = sk([lift(w, nx1(w, ante), Ak) if False else sk([sk([lift(w, (lambda: None)() or nx, Ak) if ante == A0 else lift(w, nx1(w, ante), Ak), w.inst('simpr')], 'syl', '%s e. ( Base ` ( DChr ` 1 ) )' % U1),
                                                                    sk([kn], 'nnzd', 'k e. ZZ')], 'jca', '( %s e. ( Base ` ( DChr ` 1 ) ) /\\ k e. ZZ )' % U1), w.inst('zc1x1')], 'syl', '%s = 1' % CH('k'))
        kc = sk([sk([kn], 'nncnd', 'k e. CC'), sk([lift(w, zst, Ak)], 'negcld', '-u %s e. CC' % zv)], 'cxpcld', '( k ^c -u %s ) e. CC' % zv)
        e = sk([sk([x1], 'oveq1d', '( %s x. ( k ^c -u %s ) ) = ( 1 x. ( k ^c -u %s ) )' % (CH('k'), zv, zv)), sk([kc], 'mullidd', '( 1 x. ( k ^c -u %s ) ) = ( k ^c -u %s )' % (zv, zv))], 'eqtrd',
               '( %s x. ( k ^c -u %s ) ) = ( k ^c -u %s )' % (CH('k'), zv, zv))
        return w.s([e], 'sumeq2dv', '( %s -> %s = %s )' % (ante, DSX(zv), ZSUM(zv)))
    # ETA |` Wd = F1 oF x. DSM
    re_ = s([wss, w.inst('resmpt')], 'syl', '( %s |` %s ) = ( z e. %s |-> %s )' % (ETA, Wd, Wd, EB % ('z', 'z')))
    ez = sz([sz([zc, z1], 'jca', '( z e. CC /\\ 1 < ( Re ` z ) )'), w.inst('etazser')], 'syl', '%s = ( %s x. %s )' % (EB % ('z', 'z'), GB, ZSUM('z')))
    cz = conv(Az, zc, 'z')
    ez2 = sz([ez, sz([sz([cz], 'eqcomd', '%s = %s' % (ZSUM('z'), DSX('z')))], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (GB, ZSUM('z'), GB, DSX('z')))], 'eqtrd', '%s = ( %s x. %s )' % (EB % ('z', 'z'), GB, DSX('z')))
    me = s([ez2], 'mpteq2dva', '( z e. %s |-> %s ) = ( z e. %s |-> ( %s x. %s ) )' % (Wd, EB % ('z', 'z'), Wd, GB, DSX('z')))
    wv = s([w.s([w.s([], 'hpopn', '%s e. %s' % (Wd, K_))], 'elexi', '%s e. _V' % Wd)], 'a1i', '%s e. _V' % Wd)
    gbc = sz([sz([], '1cnd', '1 e. CC'), sz([sz([], '2cnd', '2 e. CC'), sz([sz([], '1cnd', '1 e. CC'), zc], 'subcld', '( 1 - z ) e. CC')], 'cxpcld', '( 2 ^c ( 1 - z ) ) e. CC')], 'subcld', '%s e. CC' % GB)
    dsm_f = s([s([hl, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (DSM, Wd)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (DSM, Wd))
    dxc = sz([sz([sz([lift(w, dsm_f, Az), sz([], 'simpr', 'z e. %s' % Wd)], 'ffvelcdmd', '( %s ` z ) e. CC' % DSM),
                  sz([sz([], 'simpr', 'z e. %s' % Wd), sz([w.s([], 'sumex', '%s e. _V' % DSX('z'))], 'a1i', '%s e. _V' % DSX('z')), w.inst('fvmpt2' if False else 'x')], 'x', 'x') if False else
                  None][0:1], 'x', 'x')] , 'x', 'x') if False else None
    # value of DSM at z as element of CC: through lchrne0-free route: fvmpt
    Azz = Az
    dv_z, _ = _cg.mptval(w, Az, 'z', Wd, DSX('z'), 'z', sz([], 'simpr', 'z e. %s' % Wd), exs=sz([w.s([], 'sumex', '%s e. _V' % DSX('z'))], 'a1i', '%s e. _V' % DSX('z')), gen=w.g) if False else (None, None)
    # DSX ( z ) e. CC: from the conversion and zsercvgz-free route: DSM ( z ) = DSX ( z ) by fvmpt2
    dmz = sz([lift(w, dsm_f, Az), sz([], 'simpr', 'z e. %s' % Wd)], 'ffvelcdmd', '( %s ` z ) e. CC' % DSM)
    fvm = sz([sz([], 'simpr', 'z e. %s' % Wd), sz([w.s([], 'sumex', '%s e. _V' % DSX('z'))], 'a1i', '%s e. _V' % DSX('z')), w.inst('fvmpt2')], 'syl2anc', '( %s ` z ) = %s' % (DSM, DSX('z')))
    dxz = sz([fvm, dmz], 'eqeltrrd', '%s e. CC' % DSX('z'))
    ov = s([wv, gbc, dxz, s([], 'eqidd', '%s = %s' % (F1, F1)), s([], 'eqidd', '%s = %s' % (DSM, DSM))], 'offval2', '( %s oF x. %s ) = ( z e. %s |-> ( %s x. %s ) )' % (F1, DSM, Wd, GB, DSX('z')))
    er = s([s([re_, me], 'eqtrd', '( %s |` %s ) = ( z e. %s |-> ( %s x. %s ) )' % (ETA, Wd, Wd, GB, DSX('z'))), s([ov], 'eqcomd', '( z e. %s |-> ( %s x. %s ) ) = ( %s oF x. %s )' % (Wd, GB, DSX('z'), F1, DSM))],
           'eqtrd', '( %s |` %s ) = ( %s oF x. %s )' % (ETA, Wd, F1, DSM))
    rg = s([wss, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (GF, Wd, F1))
    # derivatives
    hE = hol_eta(w, A0); hG = hol_gf(w, A0)
    vE, domE, _, wcc = dres(w, A0, ETA, HP0, hE, Wd, wss, sw)
    vG, domG, gff, _ = dres(w, A0, GF, HP0, hG, Wd, wss, sw)
    vG2 = s([s([s([rg], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D %s )' % (GF, Wd, F1))], 'fveq1d', '( ( CC _D ( %s |` %s ) ) ` S ) = ( ( CC _D %s ) ` S )' % (GF, Wd, F1))], 'eqcomd',
            '( ( CC _D %s ) ` S ) = ( ( CC _D ( %s |` %s ) ) ` S )' % (F1, GF, Wd))
    vG3 = s([vG2, vG], 'eqtrd', '( ( CC _D %s ) ` S ) = ( ( CC _D %s ) ` S )' % (F1, GF))
    domF1 = s([domG, s([s([rg], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D %s )' % (GF, Wd, F1))], 'dmeqd', 'dom ( CC _D ( %s |` %s ) ) = dom ( CC _D %s )' % (GF, Wd, F1))], 'eleqtrd', 'S e. dom ( CC _D %s )' % F1)
    f1f = s([s([rg], 'feq1d', '( ( %s |` %s ) : %s --> CC <-> %s : %s --> CC )' % (GF, Wd, Wd, F1, Wd)), s([gff, wss], 'fssresd', '( %s |` %s ) : %s --> CC' % (GF, Wd, Wd))], 'mpbird', '%s : %s --> CC' % (F1, Wd)) if False else \
        s([s([gff, wss], 'fssresd', '( %s |` %s ) : %s --> CC' % (GF, Wd, Wd)), s([rg], 'feq1d', '( ( %s |` %s ) : %s --> CC <-> %s : %s --> CC )' % (GF, Wd, Wd, F1, Wd))], 'mpbid', '%s : %s --> CC' % (F1, Wd))
    domD = s([s([hl, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D %s )' % (Wd, DSM)), sw], 'sseldd', 'S e. dom ( CC _D %s )' % DSM)
    ccp = s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', 'CC e. { RR , CC }')
    PR = '( ( ( ( CC _D %s ) ` S ) x. ( %s ` S ) ) + ( ( ( CC _D %s ) ` S ) x. ( %s ` S ) ) )' % (F1, DSM, DSM, F1)
    dm = s([f1f, wcc, dsm_f, wcc, ccp, domF1, domD], 'dvmul', '( ( CC _D ( %s oF x. %s ) ) ` S ) = %s' % (F1, DSM, PR))
    dE = s([s([s([s([er], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D ( %s oF x. %s ) )' % (ETA, Wd, F1, DSM))], 'fveq1d',
                  '( ( CC _D ( %s |` %s ) ) ` S ) = ( ( CC _D ( %s oF x. %s ) ) ` S )' % (ETA, Wd, F1, DSM))], 'x', 'x') if False else
            s([s([vE], 'eqcomd', '( ( CC _D %s ) ` S ) = ( ( CC _D ( %s |` %s ) ) ` S )' % (ETA, ETA, Wd)),
               s([s([s([er], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D ( %s oF x. %s ) )' % (ETA, Wd, F1, DSM))], 'fveq1d', '( ( CC _D ( %s |` %s ) ) ` S ) = ( ( CC _D ( %s oF x. %s ) ) ` S )' % (ETA, Wd, F1, DSM)), dm],
                 'eqtrd', '( ( CC _D ( %s |` %s ) ) ` S ) = %s' % (ETA, Wd, PR))], 'eqtrd', '( ( CC _D %s ) ` S ) = %s' % (ETA, PR))], 'idi', '( ( CC _D %s ) ` S ) = %s' % (ETA, PR))
    # values at S
    from zc1_f import gval
    gS, GV = gval(w, A0, sh, 'S')
    f1S, _ = _cg.mptval(w, A0, 'z', Wd, GB, 'S', sw, exs=c.a1(w.s([], 'ovex', '%s e. _V' % GV), '%s e. _V' % GV), gen=w.g)
    f1g = s([f1S, s([gS], 'eqcomd', '%s = ( %s ` S )' % (GV, GF))], 'eqtrd', '( %s ` S ) = ( %s ` S )' % (F1, GF))
    dS, _ = _cg.mptval(w, A0, 'z', Wd, DSX('z'), 'S', sw, exs=c.a1(w.s([], 'sumex', '%s e. _V' % DSX('S')), '%s e. _V' % DSX('S')), gen=w.g)
    # ETA ( S ) = GF ( S ) x. DSX ( S )
    eSv, _ = _cg.mptval(w, A0, 'z', HP0, EB % ('z', 'z'), 'S', sh, exs=c.a1(w.s([], 'sumex', '%s e. _V' % (EB % ('S', 'S'))), '%s e. _V' % (EB % ('S', 'S'))), gen=w.g)
    ezS = s([s([sc, s1], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )'), w.inst('etazser')], 'syl', '%s = ( %s x. %s )' % (EB % ('S', 'S'), GV, ZSUM('S')))
    cS = conv(A0, sc, 'S')
    eta_S = s([s([eSv, ezS], 'eqtrd', '( %s ` S ) = ( %s x. %s )' % (ETA, GV, ZSUM('S'))),
               s([s([gS], 'eqcomd', '%s = ( %s ` S )' % (GV, GF)), s([cS], 'eqcomd', '%s = %s' % (ZSUM('S'), DSX('S')))], 'oveq12d', '( %s x. %s ) = ( ( %s ` S ) x. %s )' % (GV, ZSUM('S'), GF, DSX('S')))],
              'eqtrd', '( %s ` S ) = ( ( %s ` S ) x. %s )' % (ETA, GF, DSX('S')))
    # the logarithmic derivative of the series
    LD = tsub(stmt('lchrlogdv'), {'N': '1', 'X': U1, 'T': T, 'Z': 'S'})
    lda, ldc = ante_of(LD)
    ld = s([s([nx, s([s([tr, t1], 'jca', '( %s e. RR /\\ 1 < %s )' % (T, T)), sw], 'jca', top_and(lda)[1])], 'jca', lda), w.inst('lchrlogdv')], 'syl', ldc)
    VS = ldc.rsplit(' = -u ', 1)[1]
    # nonvanishing
    gn0 = s([s([sc, s1], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )'), w.inst('gfunne0')], 'syl', '%s =/= 0' % GV)
    gn = s([gS, gn0], 'eqnetrd', '( %s ` S ) =/= 0' % GF)
    dn = s([s([nx, s([sc, s1], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', '( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % U1), w.inst('lchrne0')], 'syl', '%s =/= 0' % DSX('S'))
    # closures
    a_ = '( ( CC _D %s ) ` S )' % GF
    b_ = '( ( CC _D %s ) ` S )' % DSM
    g_ = '( %s ` S )' % GF
    z_ = DSX('S')
    def dvcc(M, D_, holst, xin):
        """( A0 -> ( ( CC _D M ) ` S ) e. CC )"""
        dvf = s([w.s([], 'dvfcn', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (M, M))], 'a1i', '( CC _D %s ) : dom ( CC _D %s ) --> CC' % (M, M))
        return s([dvf, xin], 'ffvelcdmd', '( ( CC _D %s ) ` S ) e. CC' % M)
    ac = dvcc(GF, HP0, hG, s([s([hG, w.inst('simpr')], 'syl', '%s C_ dom ( CC _D %s )' % (HP0, GF)), sh], 'sseldd', 'S e. dom ( CC _D %s )' % GF))
    bc = dvcc(DSM, Wd, hl, domD)
    gc = fcc(w, A0, hG, GF, HP0, 'S', sh)
    zc_ = s([s([dsm_f, sw], 'ffvelcdmd', '( %s ` S ) e. CC' % DSM), dS], 'x', 'x') if False else s([dS, s([dsm_f, sw], 'ffvelcdmd', '( %s ` S ) e. CC' % DSM)], 'eqeltrrd', '%s e. CC' % z_)
    # rewrite the product-rule numerator
    PR2 = '( ( %s x. %s ) + ( %s x. %s ) )' % (a_, z_, b_, g_)
    pr1 = s([s([vG3, dS], 'oveq12d', '( ( ( CC _D %s ) ` S ) x. ( %s ` S ) ) = ( %s x. %s )' % (F1, DSM, a_, z_)), s([f1g], 'oveq2d', '( ( ( CC _D %s ) ` S ) x. ( %s ` S ) ) = ( %s x. %s )' % (DSM, F1, b_, g_))],
            'oveq12d', '%s = %s' % (PR, PR2))
    dE2 = s([dE, pr1], 'eqtrd', '( ( CC _D %s ) ` S ) = %s' % (ETA, PR2))
    cl = Closure(w, A0, {a_: ('CC', ac), b_: ('CC', bc), g_: ('CC', gc), z_: ('CC', zc_)})
    for k in (a_, b_, g_, z_):
        cl.atom(k)
    PR3 = PR2
    q1 = s([dE2, eta_S], 'oveq12d', '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( %s / ( %s x. %s ) )' % (ETA, ETA, PR3, g_, z_))
    dd = s([ac, gc, bc, zc_, gn, dn], 'divadddivd', '( ( %s / %s ) + ( %s / %s ) ) = ( %s / ( %s x. %s ) )' % (a_, g_, b_, z_, PR3, g_, z_))
    q2 = s([q1, s([dd], 'eqcomd', '( %s / ( %s x. %s ) ) = ( ( %s / %s ) + ( %s / %s ) )' % (PR3, g_, z_, a_, g_, b_, z_))], 'eqtrd',
           '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( ( %s / %s ) + ( %s / %s ) )' % (ETA, ETA, a_, g_, b_, z_))
    q3 = s([q2, s([ld], 'oveq2d', '( ( %s / %s ) + ( %s / %s ) ) = ( ( %s / %s ) + -u %s )' % (a_, g_, b_, z_, a_, g_, VS))], 'eqtrd',
           '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( ( %s / %s ) + -u %s )' % (ETA, ETA, a_, g_, VS))
    # sum_ X Lam k ^ -S = sum_ Lam k ^ -S, and it is a complex number
    Ak = '( %s /\\ k e. NN )' % A0
    sk = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ak, f))
    kn = sk([], 'simpr', 'k e. NN')
    x1 = sk([sk([sk([lift(w, nx, Ak), w.inst('simpr')], 'syl', '%s e. ( Base ` ( DChr ` 1 ) )' % U1), sk([kn], 'nnzd', 'k e. ZZ')], 'jca', '( %s e. ( Base ` ( DChr ` 1 ) ) /\\ k e. ZZ )' % U1), w.inst('zc1x1')], 'syl', '%s = 1' % CH('k'))
    lk = sk([sk([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    e1 = sk([sk([sk([x1], 'oveq1d', '( %s x. ( Lam ` k ) ) = ( 1 x. ( Lam ` k ) )' % CH('k')), sk([lk], 'mullidd', '( 1 x. ( Lam ` k ) ) = ( Lam ` k )')], 'eqtrd', '( %s x. ( Lam ` k ) ) = ( Lam ` k )' % CH('k'))],
            'oveq1d', '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u S ) ) = ( ( Lam ` k ) x. ( k ^c -u S ) )' % CH('k'))
    vs = w.s([e1], 'sumeq2dv', '( %s -> %s = %s )' % (A0, VS, DLAM('S')))
    xk = sk([x1, sk([], '1cnd', '1 e. CC')], 'eqeltrd', '%s e. CC' % CH('k'))
    kz = sk([sk([kn], 'nncnd', 'k e. CC'), sk([lift(w, sc, Ak)], 'negcld', '-u S e. CC')], 'cxpcld', '( k ^c -u S ) e. CC')
    VK = '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u S ) )' % CH('k')
    vk = sk([sk([xk, lk], 'mulcld', '( %s x. ( Lam ` k ) ) e. CC' % CH('k')), kz], 'mulcld', '%s e. CC' % VK)
    VN = '( ( %s x. ( Lam ` n ) ) x. ( n ^c -u S ) )' % CH('n')
    fv, _ = _cg.mptval(w, Ak, 'n', 'NN', VN, 'k', kn, exs=sk([vk], 'elexd', '%s e. _V' % VK), gen=w.g)
    NX1 = '( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1
    cvg = s([s([nx, s([sc, s1], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', '( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % NX1), w.inst('lchvmcvg')], 'syl',
            'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % VN)
    vsc = s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), s([], '1zzd', '1 e. ZZ'), fv, vk, cvg], 'isumcl', '%s e. CC' % VS)
    AG = '( %s / %s )' % (a_, g_)
    agc = s([ac, gc, gn], 'divcld', '%s e. CC' % AG)
    q4 = s([q3, s([agc, vsc], 'negsubd', '( %s + -u %s ) = ( %s - %s )' % (AG, VS, AG, VS))], 'eqtrd', '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( %s - %s )' % (ETA, ETA, AG, VS))
    q5 = s([q4, s([vs], 'oveq2d', '( %s - %s ) = ( %s - %s )' % (AG, VS, AG, DLAM('S')))], 'eqtrd', '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( %s - %s )' % (ETA, ETA, AG, DLAM('S')))
    w.qed([q5], 'idi', S['ef5lds'])
    return run8(w)


GENS = {'ef5lds': gen_lds}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
