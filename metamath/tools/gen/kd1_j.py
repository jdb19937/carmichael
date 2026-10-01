"""Sortie KD1: - L'/L is the twisted von Mangoldt series on Re S > 1 (kdlogdv; lchrldre's bridge as a lemma)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import kd1lib as K1
import zc1lib as Z
import congr as _cg
from cl import lift
import c9_h
c9_h.stmt = K1.stmt
from c9_h import lf_hol
from c9lib import LSs
from c8lib import lin8, tsub, ante_of
from c9lib import top_and
W = K1.W

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_logdv():
    CHI, LFN, HP0, NX = K1.CHI, K1.LFN, K1.HP0, Z.NX
    w = W('kdlogdv', 'Lean ` KDerivDetect.logDeriv_LFunction_eq ` : ` L \' / L ( S ) = -u sum chi ( k ) Lam ( k ) k ^ -u S ` for nonprincipal ` chi ` and ` 1 < Re S ` (C5 ` lchragr ` , ` dvres ` , C7b ` lchrlogdv ` ; the bridge inside ZC1 ` lchrldre ` ).')
    A0 = K1.S['kdlogdv'].split(' -> ( ( ( CC _D')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    sc = s([], 'simprl', 'S e. CC'); s1S = s([], 'simprr', '1 < ( Re ` S )')
    rsr = s([sc], 'recld', '( Re ` S ) e. RR')
    nx = s([chi, w.inst('simpl')], 'syl', NX)
    T = '( ( 1 + ( Re ` S ) ) / 2 )'
    tr = s([s([s([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), rsr], 'readdcld', '( 1 + ( Re ` S ) ) e. RR')], 'rehalfcld', '%s e. RR' % T)
    lv = {'( Re ` S )': rsr}
    t1 = lin8(w, A0, [s1S], '1 < %s' % T, lv)
    Wd = "( `' Re \" ( %s (,) +oo ) )" % T
    sw = s([s([sc, lin8(w, A0, [s1S], '%s < ( Re ` S )' % T, lv)], 'jca', '( S e. CC /\\ %s < ( Re ` S ) )' % T),
            s([tr, w.inst('elhp2')], 'syl', '( S e. %s <-> ( S e. CC /\\ %s < ( Re ` S ) ) )' % (Wd, T))], 'mpbird', 'S e. %s' % Wd)
    Az = '( %s /\\ z e. %s )' % (A0, Wd)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zz = sz([sz([], 'simpr', 'z e. %s' % Wd), sz([lift(w, tr, Az), w.inst('elhp2')], 'syl', '( z e. %s <-> ( z e. CC /\\ %s < ( Re ` z ) ) )' % (Wd, T))], 'mpbid', '( z e. CC /\\ %s < ( Re ` z ) )' % T)
    zc = sz([zz, w.inst('simpl')], 'syl', 'z e. CC'); zt = sz([zz, w.inst('simpr')], 'syl', '%s < ( Re ` z )' % T)
    rzr = sz([zc], 'recld', '( Re ` z ) e. RR')
    lvz = {'( Re ` S )': lift(w, rsr, Az), '( Re ` z )': rzr}
    z0 = lin8(w, Az, [zt, lift(w, s1S, Az)], '0 < ( Re ` z )', lvz)
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
    s1 = lin8(w, As, [ss_([szz, w.inst('simpr')], 'syl', '%s < ( Re ` s )' % T), lift(w, s1S, As)], '1 < ( Re ` s )',
              {'( Re ` S )': lift(w, rsr, As), '( Re ` s )': ss_([ss_([szz, w.inst('simpl')], 'syl', 's e. CC')], 'recld', '( Re ` s ) e. RR')})
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
    Kt = '( TopOpen ` CCfld )'
    k_ = w.s([], 'eqid', '%s = %s' % (Kt, Kt))
    tk = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (Kt, Kt))], 'eqcomi', '%s = ( %s |`t CC )' % (Kt, Kt))
    dv = s([s([s([s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), lff], 'jca', '( CC C_ CC /\\ %s : %s --> CC )' % (LFN, HP0)), s([hpc, wcc], 'jca', '( %s C_ CC /\\ %s C_ CC )' % (HP0, Wd))], 'jca',
               '( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) )' % (LFN, HP0, HP0, Wd)), w.s([k_, tk], 'dvres', '( ( ( CC C_ CC /\\ %s : %s --> CC ) /\\ ( %s C_ CC /\\ %s C_ CC ) ) -> ( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) )' % (LFN, HP0, HP0, Wd, LFN, Wd, LFN, Kt, Wd))],
           'syl', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) )' % (LFN, Wd, LFN, Kt, Wd))
    iw = s([s([w.s([w.s([], 'eqid', '%s = %s' % (Kt, Kt))], 'cnfldtop', '%s e. Top' % Kt)], 'a1i', '%s e. Top' % Kt), s([w.s([], 'hpopn', '%s e. %s' % (Wd, Kt))], 'a1i', '%s e. %s' % (Wd, Kt)), w.inst('isopn3i')],
           'syl2anc', '( ( int ` %s ) ` %s ) = %s' % (Kt, Wd, Wd))
    dv2 = s([dv, s([iw], 'reseq2d', '( ( CC _D %s ) |` ( ( int ` %s ) ` %s ) ) = ( ( CC _D %s ) |` %s )' % (LFN, Kt, Wd, LFN, Wd))], 'eqtrd', '( CC _D ( %s |` %s ) ) = ( ( CC _D %s ) |` %s )' % (LFN, Wd, LFN, Wd))
    dv3 = s([s([s([resq], 'oveq2d', '( CC _D ( %s |` %s ) ) = ( CC _D %s )' % (LFN, Wd, DSM))], 'eqcomd', '( CC _D %s ) = ( CC _D ( %s |` %s ) )' % (DSM, LFN, Wd)), dv2], 'eqtrd',
            '( CC _D %s ) = ( ( CC _D %s ) |` %s )' % (DSM, LFN, Wd))
    dS = s([s([dv3], 'fveq1d', '( ( CC _D %s ) ` S ) = ( ( ( CC _D %s ) |` %s ) ` S )' % (DSM, LFN, Wd)), s([sw, w.inst('fvres')], 'syl', '( ( ( CC _D %s ) |` %s ) ` S ) = ( ( CC _D %s ) ` S )' % (LFN, Wd, LFN))],
           'eqtrd', '( ( CC _D %s ) ` S ) = ( ( CC _D %s ) ` S )' % (DSM, LFN))
    shp = s([wss, sw], 'sseldd', 'S e. %s' % HP0)
    lvv, _ = _cg.mptval(w, A0, 's', HP0, LSs('s'), 'S', shp, exs=s([w.s([], 'sumex', '%s e. _V' % LSs('S'))], 'a1i', '%s e. _V' % LSs('S')), gen=w.g)
    agS = s([s([chi, s([sc, s1S], 'jca', '( S e. CC /\\ 1 < ( Re ` S ) )')], 'jca', '( %s /\\ ( S e. CC /\\ 1 < ( Re ` S ) ) )' % CHI), w.inst('lchragr')], 'syl', '%s = %s' % (LSs('S'), DSX('S')))
    lS = s([lvv, agS], 'eqtrd', '( %s ` S ) = %s' % (LFN, DSX('S')))
    LD = tsub(K1.stmt('lchrlogdv'), {'T': T, 'Z': 'S'})
    lda, ldc = ante_of(LD)
    ld = s([s([nx, s([s([tr, t1], 'jca', '( %s e. RR /\\ 1 < %s )' % (T, T)), sw], 'jca', top_and(lda)[1])], 'jca', lda), w.inst('lchrlogdv')], 'syl', ldc)
    VS = ldc.rsplit(' = -u ', 1)[1]
    lSr = s([lS], 'eqcomd', '%s = ( %s ` S )' % (DSX('S'), LFN))
    rat = s([s([dS, lSr], 'oveq12d', '( ( ( CC _D %s ) ` S ) / %s ) = ( ( ( CC _D %s ) ` S ) / ( %s ` S ) )' % (DSM, DSX('S'), LFN, LFN))], 'eqcomd',
            '( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) = ( ( ( CC _D %s ) ` S ) / %s )' % (LFN, LFN, DSM, DSX('S')))
    w.qed([rat, ld], 'eqtrd', K1.S['kdlogdv'])
    return run(w)


if __name__ == '__main__':
    gen_logdv()
