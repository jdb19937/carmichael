"""Sortie GF2, section H: Halasz duality at the frozen parameters (Lean halasz_duality_detector,
halasz_duality_frozen, Fgen_cDet_eq_Fdet, the summability of bMaj).
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_h.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift
import lin
lin.FASTPATH = True
import gf2lib as L
from z5a_d import avre2

S_ = L.S
LXP = L.LXP; LM0 = L.LM0
E0 = '( exp ` ( %s + %s ) )' % (LXP, ELLD)
QQ = '( exp ` ( -u 1 / %s ) )' % E0
FL2 = '( ( |_ ` %s ) ^ 2 )' % RP
S_['gf2bmc'] = '( ( %s /\\ N e. V ) -> seq 1 ( + , %s ) e. dom ~~> )' % (HZ2, BM)


def dfx(w, a, hz):
    """D-facts without an index: dr d1 drp xprp m0rp ellrp and the window order M0 e^L < XP"""
    st = mkst(w, a)
    fw = st([hz, w.inst('z5fwin')], 'syl', '( ( 1 <_ %s /\\ %s < %s ) /\\ ( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s ) )' % (Z1, Z1, Z2, M0, ELLD, Z1, Z1, XP))
    f1 = st([fw], 'simpld', '( 1 <_ %s /\\ %s < %s )' % (Z1, Z1, Z2)); f2 = st([fw], 'simprd', '( ( %s x. ( exp ` %s ) ) <_ %s /\\ ( 2 x. %s ) <_ %s )' % (M0, ELLD, Z1, Z1, XP))
    z11 = st([f1], 'simpld', '1 <_ %s' % Z1); z12 = st([f1], 'simprd', '%s < %s' % (Z1, Z2))
    mz = st([f2], 'simpld', '( %s x. ( exp ` %s ) ) <_ %s' % (M0, ELLD, Z1)); zx = st([f2], 'simprd', '( 2 x. %s ) <_ %s' % (Z1, XP))
    dr = st([hz], 'simp1d', 'D e. RR'); d1 = st([hz], 'simp2d', '1 < D'); l2 = st([hz], 'simp3d', '2 <_ ( log ` D )')
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    zz = st([st([dr, d1], 'jca', '( D e. RR /\\ 1 < D )'), w.inst('zdz12')], 'syl', '( %s e. RR+ /\\ %s e. RR+ /\\ %s < %s )' % (Z1, Z2, Z1, Z2))
    z1rp = st([zz], 'simp1d', '%s e. RR+' % Z1); z2rp = st([zz], 'simp2d', '%s e. RR+' % Z2)
    z1r = st([z1rp], 'rpred', '%s e. RR' % Z1)
    xprp = st([drp, litr(w, a, '( 6 / 5 )')], 'rpcxpcld', '%s e. RR+' % XP); xpr = st([xprp], 'rpred', '%s e. RR' % XP)
    m0rp = st([drp, litr(w, a, '( 3 / 5 )')], 'rpcxpcld', '%s e. RR+' % M0)
    rprp = st([drp, litr(w, a, '( 1 / ; ; 1 0 0 )')], 'rpcxpcld', '%s e. RR+' % RP)
    lr = st([drp], 'relogcld', '( log ` D ) e. RR')
    lgt = lin.linarith(w, a, [l2], '0 < ( log ` D )', leaves={'( log ` D )': lr})
    hrp = st([litr(w, a, '( 1 / ; ; 1 0 0 )'), litle(w, a, '0', '( 1 / ; ; 1 0 0 )', strict=True)], 'elrpd', '( 1 / ; ; 1 0 0 ) e. RR+')
    ellrp = st([hrp, st([lr, lgt], 'elrpd', '( log ` D ) e. RR+')], 'rpmulcld', '%s e. RR+' % ELLD)
    ellr = st([ellrp], 'rpred', '%s e. RR' % ELLD)
    ML = '( %s x. ( exp ` %s ) )' % (M0, ELLD)
    mlr = st([st([m0rp, st([ellr], 'rpefcld', '( exp ` %s ) e. RR+' % ELLD)], 'rpmulcld', '%s e. RR+' % ML)], 'rpred', '%s e. RR' % ML)
    zlx = lin.linarith(w, a, [zx, z11], '%s < %s' % (Z1, XP), leaves={Z1: z1r, XP: xpr})
    mlx = lin.linarith(w, a, [mz, zlx], '%s < %s' % (ML, XP), leaves={ML: mlr, Z1: z1r, XP: xpr})
    lxr = st([xprp], 'relogcld', '%s e. RR' % LXP)
    lmr = st([m0rp], 'relogcld', '%s e. RR' % LM0)
    return dict(dr=dr, d1=d1, drp=drp, z1rp=z1rp, z2rp=z2rp, z1r=z1r, xprp=xprp, xpr=xpr, m0rp=m0rp, rprp=rprp, ellrp=ellrp, ellr=ellr,
                mlx=mlx, lr=lr, lgt=lgt, z11=z11, z12=z12, mz=mz, zx=zx, lxr=lxr, lmr=lmr)


def bmk(w, ak, f, nv, knn, K):
    """under ak (index K, knn: K e. NN): value of BM at K, 0 <_ BM K, and BM K <_ FL2 . QQ ^ K"""
    st = mkst(w, ak)
    F = {k: lift(w, v, ak) for k, v in f.items()}
    pfv = a1(w, ak, w.s([], 'ovex', '%s e. _V' % PF), '%s e. _V' % PF)
    wfv = a1(w, ak, w.s([], 'fvex', '%s e. _V' % WF), '%s e. _V' % WF)
    PK = '( %s ` %s )' % (PF, K); WK = '( %s ` %s )' % (WF, K); BK = '( %s ` %s )' % (BM, K)
    bv = st([pfv, wfv, knn, w.inst('z5bmajval')], 'syl21anc', '%s = %s' % (BK, BMV(PF, WF, K)))
    AVB = AV(LXP, ELLD, K); AVA = AV(LM0, ELLD, K)
    wv = st([F['m0rp'], F['xprp'], F['ellrp'], knn, w.inst('z5wwinval')], 'syl31anc', '%s = ( %s - %s )' % (WK, AVB, AVA))
    kr = st([knn], 'nnred', '%s e. RR' % K)
    k0 = st([st([knn], 'nnrpd', '%s e. RR+' % K)], 'rpge0d', '0 <_ %s' % K)
    avb = avre2(w, ak, F['lxr'], F['ellrp'], kr, LXP, ELLD, K)
    ava = avre2(w, ak, F['lmr'], F['ellrp'], kr, LM0, ELLD, K)
    hb = st([st([F['lxr'], F['ellrp']], 'jca', '( %s e. RR /\\ %s e. RR+ )' % (LXP, ELLD)), st([kr, k0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (K, K)), w.inst('z5wavg')], 'syl2anc',
            '( ( exp ` ( -u %s / ( exp ` %s ) ) ) <_ %s /\\ %s <_ ( exp ` ( -u %s / ( exp ` ( %s + %s ) ) ) ) )' % (K, LXP, AVB, AVB, K, LXP, ELLD))
    ha = st([st([F['lmr'], F['ellrp']], 'jca', '( %s e. RR /\\ %s e. RR+ )' % (LM0, ELLD)), st([kr, k0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (K, K)), w.inst('z5wavg')], 'syl2anc',
            '( ( exp ` ( -u %s / ( exp ` %s ) ) ) <_ %s /\\ %s <_ ( exp ` ( -u %s / ( exp ` ( %s + %s ) ) ) ) )' % (K, LM0, AVA, AVA, K, LM0, ELLD))
    EB = '( exp ` ( -u %s / %s ) )' % (K, E0)
    ubr = st([hb], 'simprd', '%s <_ %s' % (AVB, EB))
    ea = '( exp ` ( -u %s / ( exp ` %s ) ) )' % (K, LM0)
    lar = st([ha], 'simpld', '%s <_ %s' % (ea, AVA))
    ear = st([st([st([kr], 'renegcld', '-u %s e. RR' % K), st([F['lmr']], 'rpefcld', '( exp ` %s ) e. RR+' % LM0)], 'rerpdivcld', '( -u %s / ( exp ` %s ) ) e. RR' % (K, LM0))],
             'rpefcld', '%s e. RR+' % ea)
    e0rp = st([st([F['lxr'], F['ellr']], 'readdcld', '( %s + %s ) e. RR' % (LXP, ELLD))], 'rpefcld', '%s e. RR+' % E0)
    ebr = st([st([st([kr], 'renegcld', '-u %s e. RR' % K), e0rp], 'rerpdivcld', '( -u %s / %s ) e. RR' % (K, E0))], 'reefcld', '%s e. RR' % EB)
    ea0 = st([ear], 'rpgt0d', '0 < %s' % ea)
    wkr = st([wv, st([avb, ava], 'resubcld', '( %s - %s ) e. RR' % (AVB, AVA))], 'eqeltrd', '%s e. RR' % WK)
    wle = lin.linarith(w, ak, [wv, ubr, lar, ea0], '%s <_ %s' % (WK, EB), leaves={WK: wkr, AVB: avb, AVA: ava, EB: ebr, ea: st([ear], 'rpred', '%s e. RR' % ea)})
    wpos = st([st([F['m0rp'], F['ellrp']], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (M0, ELLD)),
               st([F['xpr'], F['mlx']], 'jca', '( %s e. RR /\\ ( %s x. ( exp ` %s ) ) < %s )' % (XP, M0, ELLD, XP)), knn, w.inst('z5wpos')], 'syl21anc', '0 < %s' % WK)
    pkr = st([nv, a1(w, ak, w.s([], 'ovex', '%s e. _V' % RP), '%s e. _V' % RP), knn, w.inst('z5pfunre')], 'syl21anc', '%s e. RR' % PK)
    return dict(bv=bv, wv=wv, kr=kr, wkr=wkr, wle=wle, wpos=wpos, pkr=pkr, ebr=ebr, e0rp=e0rp, PK=PK, WK=WK, BK=BK, EB=EB, pfv=pfv, wfv=wfv)


def gf2bmc():
    w = W('gf2bmc', 'The Halasz majorant is summable at the frozen parameters: ` b_n <_ ( |_ R ) ^ 2 q ^ n ` with ` q = e ^ ( - 1 / ( X e ^ L ) ) ` '
                    '(Lean ` hbs ` of ` halasz_duality_detector ` ; ~ z5wavg , ~ geolim2 , ~ cvgcmpce ).')
    a = '( %s /\\ N e. V )' % HZ2
    st = mkst(w, a)
    hz = st([], 'simpl', HZ2); nv = st([], 'simpr', 'N e. V')
    f = dfx(w, a, hz)
    ak = '( %s /\\ k e. NN )' % a
    sk = mkst(w, ak)
    knn = sk([], 'simpr', 'k e. NN')
    g = bmk(w, ak, f, lift(w, nv, ak), knn, 'k')
    PK = g['PK']; WK = g['WK']; BK = g['BK']; EB = g['EB']
    rprp = lift(w, f['rprp'], ak)
    rpr = sk([rprp], 'rpred', '%s e. RR' % RP)
    FLR = '( |_ ` %s )' % RP
    flr = sk([sk([rpr], 'flcld', '%s e. ZZ' % FLR)], 'zred', '%s e. RR' % FLR)
    pab = sk([sk([lift(w, nv, ak), sk([rpr, sk([rprp], 'rpge0d', '0 <_ %s' % RP)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (RP, RP))], 'jca',
                 '( N e. V /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (RP, RP)), knn, w.inst('z5pfunabs')], 'syl2anc', '( abs ` %s ) <_ %s' % (PK, FLR))
    apr = sk([g['pkr']], 'recnd', '%s e. CC' % PK)
    apa = sk([apr], 'abscld', '( abs ` %s ) e. RR' % PK)
    apg = sk([apr], 'absge0d', '0 <_ ( abs ` %s )' % PK)
    fl0 = sk([sk([rpr, sk([rprp], 'rpge0d', '0 <_ %s' % RP)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (RP, RP)), w.inst('flge0nn0')], 'syl', '%s e. NN0' % FLR)
    flg = sk([fl0], 'nn0ge0d', '0 <_ %s' % FLR)
    sq1 = sk([sk([apa, flr, apg, flg], 'le2sqd', '( ( abs ` %s ) <_ %s <-> ( ( abs ` %s ) ^ 2 ) <_ %s )' % (PK, FLR, PK, FL2)), pab], 'mpbid', '( ( abs ` %s ) ^ 2 ) <_ %s' % (PK, FL2))
    ars = sk([g['pkr'], w.inst('absresq')], 'syl', '( ( abs ` %s ) ^ 2 ) = ( %s ^ 2 )' % (PK, PK))
    p2 = sk([ars, sq1], 'eqbrtrrd', '( %s ^ 2 ) <_ %s' % (PK, FL2))
    kinv = '( 1 / k )'
    kir = sk([knn], 'nnrecred', '%s e. RR' % kinv)
    ki0 = sk([sk([knn], 'nnrpd', 'k e. RR+')], 'rpreccld', '%s e. RR+' % kinv)
    kle = lepone(w, ak, sk([], '1red', '1 e. RR'), sk([knn], 'nnrpd', 'k e. RR+'), sk([knn], 'nnge1d', '1 <_ k'), '1', 'k')
    P2 = '( %s ^ 2 )' % PK
    p2r = sk([g['pkr']], 'resqcld', '%s e. RR' % P2)
    p20 = sk([g['pkr']], 'sqge0d', '0 <_ %s' % P2)
    fl2r = sk([flr], 'resqcld', '%s e. RR' % FL2)
    m1 = sk([kir, sk([], '1red', '1 e. RR'), p2r, fl2r, sk([ki0], 'rpge0d', '0 <_ %s' % kinv), p20, kle, p2], 'lemul12ad', '( %s x. %s ) <_ ( 1 x. %s )' % (kinv, P2, FL2))
    A1 = '( %s x. %s )' % (kinv, P2)
    a1r = sk([kir, p2r], 'remulcld', '%s e. RR' % A1)
    a10 = sk([kir, p2r, sk([ki0], 'rpge0d', '0 <_ %s' % kinv), p20], 'mulge0d', '0 <_ %s' % A1)
    m2 = sk([a1r, sk([sk([], '1red', '1 e. RR'), fl2r], 'remulcld', '( 1 x. %s ) e. RR' % FL2), g['wkr'], g['ebr'], a10, sk([g['wpos']], 'ltled', '0 <_ %s' % WK), m1, g['wle']],
            'lemul12ad', '( %s x. %s ) <_ ( ( 1 x. %s ) x. %s )' % (A1, WK, FL2, EB))
    bkr = sk([g['bv'], sk([a1r, g['wkr']], 'remulcld', '( %s x. %s ) e. RR' % (A1, WK))], 'eqeltrd', '%s e. RR' % BK)
    bk0 = sk([g['bv'], sk([a1r, g['wkr'], a10, sk([g['wpos']], 'ltled', '0 <_ %s' % WK)], 'mulge0d', '0 <_ ( %s x. %s )' % (A1, WK))], 'breqtrrd', '0 <_ %s' % BK)
    # e ^ ( - k / E0 ) = QQ ^ k
    kc = sk([knn], 'nncnd', 'k e. CC')
    e0c = sk([g['e0rp']], 'rpcnd', '%s e. CC' % E0)
    e0n = sk([g['e0rp']], 'rpne0d', '%s =/= 0' % E0)
    m1c = sk([sk([sk([], '1cnd', '1 e. CC')], 'negcld', '-u 1 e. CC'), e0c, e0n], 'divcld', '( -u 1 / %s ) e. CC' % E0)
    # ( k x. ( -u 1 / E0 ) ) = ( -u k / E0 )
    # -u k / E0 = ( k x. -u 1 ) / E0 = k x. ( -u 1 / E0 )
    kneg = sk([sk([kc, sk([], '1cnd', '1 e. CC')], 'mulneg2d', '( k x. -u 1 ) = -u ( k x. 1 )'), sk([sk([kc], 'mulridd', '( k x. 1 ) = k')], 'negeqd', '-u ( k x. 1 ) = -u k')],
              'eqtrd', '( k x. -u 1 ) = -u k')
    da = sk([kc, sk([sk([], '1cnd', '1 e. CC')], 'negcld', '-u 1 e. CC'), e0c, e0n], 'divassd', '( ( k x. -u 1 ) / %s ) = ( k x. ( -u 1 / %s ) )' % (E0, E0))
    kv = sk([sk([kneg], 'oveq1d', '( ( k x. -u 1 ) / %s ) = ( -u k / %s )' % (E0, E0)), da], 'eqtr3d', '( -u k / %s ) = ( k x. ( -u 1 / %s ) )' % (E0, E0))
    ex1 = sk([kv], 'fveq2d', '%s = ( exp ` ( k x. ( -u 1 / %s ) ) )' % (EB, E0))
    ex2 = sk([m1c, sk([knn], 'nnzd', 'k e. ZZ'), w.inst('efexp')], 'syl2anc', '( exp ` ( k x. ( -u 1 / %s ) ) ) = ( %s ^ k )' % (E0, QQ))
    ebq = sk([ex1, ex2], 'eqtrd', '%s = ( %s ^ k )' % (EB, QQ))
    FQ = '( m e. NN |-> ( %s ^ m ) )' % QQ
    # q real, 0 < q < 1
    qarg = '( -u 1 / %s )' % E0
    qargr = sk([sk([sk([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), g['e0rp']], 'rerpdivcld', '%s e. RR' % qarg)
    qrp = sk([qargr], 'rpefcld', '%s e. RR+' % QQ)
    qfv, _ = mpv(w, ak, 'm', 'NN', '( %s ^ m )' % QQ, 'k', knn)
    fkr = sk([qfv, sk([sk([qrp], 'rpred', '%s e. RR' % QQ), sk([knn], 'nnnn0d', 'k e. NN0')], 'reexpcld', '( %s ^ k ) e. RR' % QQ)], 'eqeltrd', '( %s ` k ) e. RR' % FQ)
    bnd = sk([sk([bkr, bk0], 'absidd', '( abs ` %s ) = %s' % (BK, BK)), sk([g['bv'], m2], 'eqbrtrd', '%s <_ ( ( 1 x. %s ) x. %s )' % (BK, FL2, EB))], 'eqbrtrd',
             '( abs ` %s ) <_ ( ( 1 x. %s ) x. %s )' % (BK, FL2, EB))
    rhs = sk([sk([sk([fl2r], 'recnd', '%s e. CC' % FL2)], 'mullidd', '( 1 x. %s ) = %s' % (FL2, FL2)), sk([ebq, sk([qfv], 'eqcomd', '( %s ^ k ) = ( %s ` k )' % (QQ, FQ))], 'eqtrd',
                                                                                                  '%s = ( %s ` k )' % (EB, FQ))], 'oveq12d', '( ( 1 x. %s ) x. %s ) = ( %s x. ( %s ` k ) )' % (FL2, EB, FL2, FQ))
    bnd2 = sk([bnd, rhs], 'breqtrd', '( abs ` %s ) <_ ( %s x. ( %s ` k ) )' % (BK, FL2, FQ))
    # cvgcmpce over Z = NN, M = N = 1
    nu = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    Au = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    bu = w.s([bnd2, w.s([w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri', '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'sylan2', '( %s -> ( abs ` %s ) <_ ( %s x. ( %s ` k ) ) )' % (Au, BK, FL2, FQ))
    # geometric series
    e0rpa = st([st([f['lxr'], f['ellr']], 'readdcld', '( %s + %s ) e. RR' % (LXP, ELLD))], 'rpefcld', '%s e. RR+' % E0)
    qargra = st([st([st([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), e0rpa], 'rerpdivcld', '%s e. RR' % qarg)
    qrpa = st([qargra], 'rpefcld', '%s e. RR+' % QQ)
    qca = st([qrpa], 'rpcnd', '%s e. CC' % QQ)
    neg = st([st([e0rpa], 'rpreccld', '( 1 / %s ) e. RR+' % E0)], 'rpgt0d', '0 < ( 1 / %s )' % E0)
    q1 = lin.linarith(w, a, [neg], '-u ( 1 / %s ) < 0' % E0, leaves={'( 1 / %s )' % E0: st([st([e0rpa], 'rpreccld', '( 1 / %s ) e. RR+' % E0)], 'rpred', '( 1 / %s ) e. RR' % E0)})
    dn = st([st([], '1cnd', '1 e. CC'), st([e0rpa], 'rpcnd', '%s e. CC' % E0), st([e0rpa], 'rpne0d', '%s =/= 0' % E0)], 'divnegd', '-u ( 1 / %s ) = ( -u 1 / %s )' % (E0, E0))
    qn = st([st([dn], 'eqcomd', '( -u 1 / %s ) = -u ( 1 / %s )' % (E0, E0)), q1], 'eqbrtrd', '( -u 1 / %s ) < 0' % E0)
    efl = st([qargra, st([], '0red', '0 e. RR'), w.inst('eflt')], 'syl2anc', '( %s < 0 <-> %s < ( exp ` 0 ) )' % (qarg, QQ))
    ql0 = st([qn, efl], 'mpbid', '%s < ( exp ` 0 )' % QQ)
    ql1 = st([ql0, a1(w, a, w.s([], 'ef0', '( exp ` 0 ) = 1'), '( exp ` 0 ) = 1')], 'breqtrd', '%s < 1' % QQ)
    qab = st([st([qrpa], 'rpred', '%s e. RR' % QQ), st([qrpa], 'rpge0d', '0 <_ %s' % QQ)], 'absidd', '( abs ` %s ) = %s' % (QQ, QQ))
    qa1 = st([qab, ql1], 'eqbrtrd', '( abs ` %s ) < 1' % QQ)
    Ag = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    fvg = w.s([qfv, w.s([w.s([], 'elnnuz', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri', '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'sylan2', '( %s -> ( %s ` k ) = ( %s ^ k ) )' % (Ag, FQ, QQ))
    gl = st([qca, qa1, a1(w, a, w.s([], '1nn0', '1 e. NN0'), '1 e. NN0'), fvg], 'geolim2', 'seq 1 ( + , %s ) ~~> ( ( %s ^ 1 ) / ( 1 - %s ) )' % (FQ, QQ, QQ))
    gcv = w.s([w.s([], 'climrel', 'Rel ~~>'), gl, w.inst('releldm')], 'sylancr', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (a, FQ))
    fl2a = st([st([st([st([f['rprp']], 'rpred', '%s e. RR' % RP)], 'flcld', '%s e. ZZ' % FLR)], 'zred', '%s e. RR' % FLR)], 'resqcld', '%s e. RR' % FL2)
    fin = st([nu, one, fkr, sk([bkr], 'recnd', '%s e. CC' % BK), gcv, fl2a, bu], 'cvgcmpce', 'seq 1 ( + , %s ) e. dom ~~>' % BM)
    w.qed([fin], 'idi', S_['gf2bmc'])
    return w


# ================================================================== gf2hal
from mvlib import ringeq
DB = L.DB_('N')
PSI_ = lambda i: '( ( Q ` %s ) e. %s /\\ ( ( P ` %s ) e. CC /\\ T <_ ( Re ` ( P ` %s ) ) ) )' % (i, DB, i, i)
PHP = '( ( %s /\\ N e. NN ) /\\ ( J e. Fin /\\ A. i e. J %s ) )' % (H0, PSI_('i'))
ZRn = lambda n: L.ZR('N', n)
XVB = lambda i, m: '( ( ( Q ` %s ) ` %s ) x. ( %s ^c -u ( ( P ` %s ) - T ) ) )' % (i, ZRn(m), m, i)
XX = '( i e. J |-> ( m e. NN |-> %s ) )' % XVB('i', 'm')
CDf = L.CDT('T')
SJ = lambda j: '( ( P ` %s ) - T )' % j


def jfacts(w, aj, al, jin, j):
    """under aj: Q_j e. DB, P_j e. CC, T <_ Re P_j from al ( aj -> A. i e. J PSI(i) ) and jin ( aj -> j e. J )"""
    st = mkst(w, aj)
    idx = w.s([], 'id', '( i = %s -> i = %s )' % (j, j))
    sub, new = w.wcongr(PSI_('i'), {'i': j}, 'i = %s' % j, {'i': idx})
    pj = st([sub, al, jin], 'rspcdva', PSI_(j))
    qj = st([pj], 'simpld', '( Q ` %s ) e. %s' % (j, DB))
    pr = st([pj], 'simprd', '( ( P ` %s ) e. CC /\\ T <_ ( Re ` ( P ` %s ) ) )' % (j, j))
    return qj, st([pr], 'simpld', '( P ` %s ) e. CC' % j), st([pr], 'simprd', 'T <_ ( Re ` ( P ` %s ) )' % j)


def xval(w, ante, jin, nin, j, n):
    """( ante -> ( ( XX ` j ) ` n ) = XVB(j, n) )"""
    st = mkst(w, ante)
    MJ = '( m e. NN |-> %s )' % XVB(j, 'm')
    ex = a1(w, ante, w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % MJ), '%s e. _V' % MJ)
    v1, _ = mpv(w, ante, 'i', 'J', '( m e. NN |-> %s )' % XVB('i', 'm'), j, jin, exs=ex)
    v2, _ = mpv(w, ante, 'm', 'NN', XVB(j, 'm'), n, nin)
    return st([st([v1], 'fveq1d', '( ( %s ` %s ) ` %s ) = ( %s ` %s )' % (XX, j, n, MJ, n)), v2], 'eqtrd', '( ( %s ` %s ) ` %s ) = %s' % (XX, j, n, XVB(j, n)))


def sjfacts(w, ante, pc, tle, tr, j):
    """S_j e. CC and 0 <_ Re S_j"""
    st = mkst(w, ante)
    tc = st([tr], 'recnd', 'T e. CC')
    sc = st([pc, tc], 'subcld', '%s e. CC' % SJ(j))
    RP_ = '( Re ` ( P ` %s ) )' % j
    rs = st([pc, tc, w.inst('resub')], 'syl2anc', '( Re ` %s ) = ( %s - ( Re ` T ) )' % (SJ(j), RP_))
    rt = st([tr, w.inst('rere')], 'syl', '( Re ` T ) = T')
    rs2 = st([rs, st([rt], 'oveq2d', '( %s - ( Re ` T ) ) = ( %s - T )' % (RP_, RP_))], 'eqtrd', '( Re ` %s ) = ( %s - T )' % (SJ(j), RP_))
    rpr = st([pc], 'recld', '%s e. RR' % RP_)
    g0 = st([tle, st([rpr, tr], 'subge0d', '( 0 <_ ( %s - T ) <-> T <_ %s )' % (RP_, RP_))], 'mpbird', '0 <_ ( %s - T )' % RP_)
    return sc, st([g0, rs2], 'breqtrrd', '0 <_ ( Re ` %s )' % SJ(j))


def gf2hal():
    w = W('gf2hal', 'Halasz duality at the frozen parameters (Lean ` halasz_duality_frozen ` , ` halasz_duality_detector ` , ` Fgen_cDet_eq_Fdet ` ): '
                    'for zeros ` rho_j ` with ` T <_ Re rho_j ` , ` ( sum_j | F ( rho_j , chi_j ) | ) ^ 2 <_ Sigma_diag . sum_( j , k ) | B ( s_j + * s_k , chi_j chi_k ^ -1 ) | ` , '
                    '` s_j = rho_j - T ` (~ gf1hal with ` c = cDet ` , ` b = bMaj ` ; ~ gf1chb , ~ gf1chc , ~ z5sigdiag , ~ gf2bmc ).')
    a = PHP
    st = mkst(w, a)
    h0n = st([], 'simpl', '( %s /\\ N e. NN )' % H0)
    h0 = st([h0n], 'simpld', H0); nnn = st([h0n], 'simprd', 'N e. NN')
    hzd = st([h0], 'simpld', HZD); ht = st([h0], 'simprd', HT)
    tr = st([ht], 'simpld', 'T e. RR')
    jfa = st([], 'simpr', '( J e. Fin /\\ A. i e. J %s )' % PSI_('i'))
    jf = st([jfa], 'simpld', 'J e. Fin'); al = st([jfa], 'simprd', 'A. i e. J %s' % PSI_('i'))
    dr = st([hzd], 'simp1d', 'D e. RR'); d1 = st([hzd], 'simp2d', '1 < D')
    drp = st([dr, lin.linarith(w, a, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    lgr = st([drp], 'relogcld', '( log ` D ) e. RR')
    l2 = lin.linarith(w, a, [st([hzd], 'simp3d', '; ; 2 0 0 <_ ( log ` D )')], '2 <_ ( log ` D )', leaves={'( log ` D )': lgr})
    hz2 = st([dr, d1, l2], '3jca', HZ2)
    nv = st([nnn], 'elexd', 'N e. _V')
    f = dfx(w, a, hz2)
    # ---- gf1hal.2
    ajn = '( %s /\\ ( j e. J /\\ n e. NN ) )' % a
    s2 = mkst(w, ajn)
    jin = s2([], 'simprl', 'j e. J'); nin = s2([], 'simprr', 'n e. NN')
    qj, pc, tle = jfacts(w, ajn, lift(w, al, ajn), jin, 'j')
    sc, s0 = sjfacts(w, ajn, pc, tle, lift(w, tr, ajn), 'j')
    xv = xval(w, ajn, jin, nin, 'j', 'n')
    XJN = '( ( %s ` j ) ` n )' % XX
    chb = s2([s2([lift(w, nnn, ajn), qj], 'jca', '( N e. NN /\\ ( Q ` j ) e. %s )' % DB), sc, s0, nin, w.inst('gf1chb')], 'syl121anc',
             '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (XVB('j', 'n'), XVB('j', 'n')))
    e1 = s2([xv], 'eleq1d', '( %s e. CC <-> %s e. CC )' % (XJN, XVB('j', 'n')))
    e2 = s2([s2([xv], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (XJN, XVB('j', 'n')))], 'breq1d', '( ( abs ` %s ) <_ 1 <-> ( abs ` %s ) <_ 1 )' % (XJN, XVB('j', 'n')))
    h2 = s2([chb, s2([e1, e2], 'anbi12d', '( ( %s e. CC /\\ ( abs ` %s ) <_ 1 ) <-> ( %s e. CC /\\ ( abs ` %s ) <_ 1 ) )' % (XJN, XJN, XVB('j', 'n'), XVB('j', 'n')))],
            'mpbird', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (XJN, XJN))
    # ---- gf1hal.3
    an = '( %s /\\ n e. NN )' % a
    s3 = mkst(w, an)
    nn3 = s3([], 'simpr', 'n e. NN')
    F3 = {k: lift(w, v, an) for k, v in f.items()}
    g = bmk(w, an, f, lift(w, nv, an), nn3, 'n')
    PK = g['PK']; WK = g['WK']; BK = g['BK']
    pfv = g['pfv']
    CTn = CDT(Z1, Z2, PF, XP, 'T', 'n'); CVn = CDV(Z1, Z2, PF, XP, 'T', 'n'); CDn = '( %s ` n )' % CDf
    hv = s3([s3([s3([F3['z1rp'], F3['z2rp']], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (Z1, Z2)), s3([pfv, F3['xprp'], lift(w, tr, an)], '3jca', '( %s e. _V /\\ %s e. RR+ /\\ T e. RR )' % (PF, XP))],
                'jca', '( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ %s e. RR+ /\\ T e. RR ) )' % (Z1, Z2, PF, XP)), nn3], 'jca',
            '( ( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ %s e. RR+ /\\ T e. RR ) ) /\\ n e. NN )' % (Z1, Z2, PF, XP))
    cdv = s3([hv, w.inst('z5cdetval')], 'syl', '%s = %s' % (CDn, CVn))
    En = '( exp ` ( -u n / %s ) )' % XP
    nrp = s3([nn3], 'nnrpd', 'n e. RR+')
    erp = s3([s3([s3([s3([nrp], 'rpred', 'n e. RR')], 'renegcld', '-u n e. RR'), F3['xprp']], 'rerpdivcld', '( -u n / %s ) e. RR' % XP)], 'rpefcld', '%s e. RR+' % En)
    bar = s3([s3([F3['dr'], lift(w, d1, an)], 'jca', '( D e. RR /\\ 1 < D )'), nn3, w.inst('zdbvare')], 'syl2anc', '%s e. RR' % BA('n'))
    NT = '( n ^c -u T )'
    ntrp = s3([nrp, s3([lift(w, tr, an)], 'renegcld', '-u T e. RR')], 'rpcxpcld', '%s e. RR+' % NT)
    A3 = '( ( %s x. %s ) x. %s )' % (BA('n'), PK, En)
    a3r = s3([s3([bar, g['pkr']], 'remulcld', '( %s x. %s ) e. RR' % (BA('n'), PK)), s3([erp], 'rpred', '%s e. RR' % En)], 'remulcld', '%s e. RR' % A3)
    ctr = s3([a3r, s3([ntrp], 'rpred', '%s e. RR' % NT)], 'remulcld', '%s e. RR' % CTn)
    cdr = s3([cdv, s3([ctr, s3([], '0red', '0 e. RR')], 'ifcld', '%s e. RR' % CVn)], 'eqeltrd', '%s e. RR' % CDn)
    kinv = '( 1 / n )'; P2 = '( %s ^ 2 )' % PK; A1 = '( %s x. %s )' % (kinv, P2)
    ki0 = s3([nrp], 'rpreccld', '%s e. RR+' % kinv)
    a1r = s3([s3([ki0], 'rpred', '%s e. RR' % kinv), s3([g['pkr']], 'resqcld', '%s e. RR' % P2)], 'remulcld', '%s e. RR' % A1)
    a10 = s3([s3([ki0], 'rpred', '%s e. RR' % kinv), s3([g['pkr']], 'resqcld', '%s e. RR' % P2), s3([ki0], 'rpge0d', '0 <_ %s' % kinv), s3([g['pkr']], 'sqge0d', '0 <_ %s' % P2)],
             'mulge0d', '0 <_ %s' % A1)
    bkr = s3([g['bv'], s3([a1r, g['wkr']], 'remulcld', '( %s x. %s ) e. RR' % (A1, WK))], 'eqeltrd', '%s e. RR' % BK)
    bk0 = s3([g['bv'], s3([a1r, g['wkr'], a10, s3([g['wpos']], 'ltled', '0 <_ %s' % WK)], 'mulge0d', '0 <_ ( %s x. %s )' % (A1, WK))], 'breqtrrd', '0 <_ %s' % BK)
    # P ( n ) = 0 -> cDet ( n ) = 0
    az = '( %s /\\ %s = 0 )' % (an, PK)
    sz = mkst(w, az)
    pz = sz([], 'simpr', '%s = 0' % PK)
    Lz = lambda s_: lift(w, s_, az)
    CT0 = CDT(Z1, Z2, PF, XP, 'T', 'n').replace(PK, '0')
    rw, _ = w.rewrite(CTn, {PK: ('0', pz)}, az)
    B0 = '( %s x. 0 )' % BA('n'); B0E = '( %s x. %s )' % (B0, En)
    z1 = sz([sz([Lz(bar)], 'recnd', '%s e. CC' % BA('n'))], 'mul01d', '%s = 0' % B0)
    z2 = sz([sz([z1], 'oveq1d', '%s = ( 0 x. %s )' % (B0E, En)), sz([sz([Lz(s3([erp], 'rpred', '%s e. RR' % En))], 'recnd', '%s e. CC' % En)], 'mul02d', '( 0 x. %s ) = 0' % En)],
            'eqtrd', '%s = 0' % B0E)
    z3 = sz([sz([z2], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (B0E, NT, NT)), sz([sz([Lz(s3([ntrp], 'rpred', '%s e. RR' % NT))], 'recnd', '%s e. CC' % NT)], 'mul02d', '( 0 x. %s ) = 0' % NT)],
            'eqtrd', '%s = 0' % CT0)
    ct0 = sz([rw, z3], 'eqtrd', '%s = 0' % CTn)
    cd0 = sz([Lz(cdv), sz([sz([ct0], 'ifeq1d', '%s = if ( %s < n , 0 , 0 )' % (CVn, Z1)), a1(w, az, w.s([], 'ifid', 'if ( %s < n , 0 , 0 ) = 0' % Z1), 'if ( %s < n , 0 , 0 ) = 0' % Z1)], 'eqtrd', '%s = 0' % CVn)], 'eqtrd', '%s = 0' % CDn)
    imp1 = s3([cd0], 'ex', '( %s = 0 -> %s = 0 )' % (PK, CDn))
    con = s3([imp1], 'necon3d', '( %s =/= 0 -> %s =/= 0 )' % (CDn, PK))
    ap = '( %s /\\ %s =/= 0 )' % (an, PK)
    sp_ = mkst(w, ap)
    Lp = lambda s_: lift(w, s_, ap)
    p2p = sp_([Lp(g['pkr']), sp_([], 'simpr', '%s =/= 0' % PK)], 'sqgt0d', '0 < %s' % P2)
    a1p = sp_([Lp(s3([ki0], 'rpred', '%s e. RR' % kinv)), Lp(s3([g['pkr']], 'resqcld', '%s e. RR' % P2)), Lp(s3([ki0], 'rpgt0d', '0 < %s' % kinv)), p2p], 'mulgt0d', '0 < %s' % A1)
    bp = sp_([Lp(g['bv']), sp_([Lp(a1r), Lp(g['wkr']), a1p, Lp(g['wpos'])], 'mulgt0d', '0 < ( %s x. %s )' % (A1, WK))], 'breqtrrd', '0 < %s' % BK)
    imp2 = s3([bp], 'ex', '( %s =/= 0 -> 0 < %s )' % (PK, BK))
    imp = s3([con, imp2], 'syld', '( %s =/= 0 -> 0 < %s )' % (CDn, BK))
    h3 = s3([s3([cdr], 'recnd', '%s e. CC' % CDn), s3([bkr, bk0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (BK, BK)), imp], '3jca',
            '( %s e. CC /\\ ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s =/= 0 -> 0 < %s ) )' % (CDn, BK, BK, CDn, BK))
    # ---- gf1hal.4
    ANn = lambda n: 'if ( ( %s ` %s ) = 0 , 0 , ( ( ( abs ` ( %s ` %s ) ) ^ 2 ) / ( %s ` %s ) ) )' % (BM, n, CDf, n, BM, n)
    aq = s3([s3([s3([cdr, w.inst('absresq')], 'syl', '( ( abs ` %s ) ^ 2 ) = ( %s ^ 2 )' % (CDn, CDn))], 'oveq1d',
                 '( ( ( abs ` %s ) ^ 2 ) / %s ) = ( ( %s ^ 2 ) / %s )' % (CDn, BK, CDn, BK))], 'ifeq2d', '%s = %s' % (ANn('n'), L.QT('n')))
    ANF = '( n e. NN |-> %s )' % ANn('n')
    QTFn = '( n e. NN |-> %s )' % L.QT('n'); QTFk = '( k e. NN |-> %s )' % L.QT('k')
    m1 = st([aq], 'mpteq2dva', '%s = %s' % (ANF, QTFn))
    m2 = w.s([cg(w, L.QT('n'), 'n', 'k')], 'cbvmptv', '%s = %s' % (QTFn, QTFk))
    m3 = st([m1, a1(w, a, m2, '%s = %s' % (QTFn, QTFk))], 'eqtrd', '%s = %s' % (ANF, QTFk))
    sd = st([st([h0, nv], 'jca', '( %s /\\ N e. _V )' % H0), w.inst('z5sigdiag')], 'syl',
            '( seq 1 ( + , %s ) e. dom ~~> /\\ sum_ n e. NN %s <_ ( ; ; ; ; ; ; ; ; ; 1 0 0 0 0 0 0 0 0 0 x. ( %s ^c ( 2 - ( 2 x. T ) ) ) ) )' % (QTFk, L.QT('n'), XP))
    sdc = st([sd], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % QTFk)
    h4 = st([sdc, st([st([m3], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (ANF, QTFk))], 'eleq1d',
                     '( seq 1 ( + , %s ) e. dom ~~> <-> seq 1 ( + , %s ) e. dom ~~> )' % (ANF, QTFk))], 'mpbird', 'seq 1 ( + , %s ) e. dom ~~>' % ANF)
    # ---- gf1hal.5
    h5 = st([st([hz2, nv], 'jca', '( %s /\\ N e. _V )' % HZ2), w.inst('gf2bmc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % BM)
    # ---- gf1hal
    GRAM = lambda X_: 'sum_ j e. J sum_ k e. J ( abs ` %s )' % X_
    L1 = '( sum_ j e. J ( abs ` sum_ n e. NN ( %s x. ( ( %s ` j ) ` n ) ) ) ^ 2 )' % (CDn, XX)
    G1S = 'sum_ n e. NN ( ( ( %s ` n ) x. ( ( %s ` j ) ` n ) ) x. ( * ` ( ( %s ` k ) ` n ) ) )' % (BM, XX, XX)
    R1 = '( sum_ n e. NN %s x. %s )' % (ANn('n'), GRAM(G1S))
    hal = st([jf, h2, h3, h4, h5], 'gf1hal', '%s <_ %s' % (L1, R1))
    # ---- (L): the detector
    from cl import split_imp

    def concl_of(step):
        for l in w.lines:
            if l.split(':', 1)[0] == step:
                return split_imp(l.split(' |- ', 1)[1])[1]
        raise KeyError(step)

    def adlr(step, X, extras):
        """( ( X /\\ n e. NN ) -> P ) to ( ( ( X /\\ e1 ) /\\ ... ) /\\ n e. NN ) -> P ) by adantlr"""
        cur = step
        for e in extras:
            X = '( %s /\\ %s )' % (X, e)
            cur = w.s([cur], 'adantlr', '( ( %s /\\ n e. NN ) -> %s )' % (X, concl_of(cur)))
        return cur

    aj = '( %s /\\ j e. J )' % a
    sj = mkst(w, aj)
    jin2 = sj([], 'simpr', 'j e. J')
    qj2, pc2, tle2 = jfacts(w, aj, lift(w, al, aj), jin2, 'j')
    scj, s0j = sjfacts(w, aj, pc2, tle2, lift(w, tr, aj), 'j')
    CH = L.CHJ('j')
    z12 = lift(w, st([f['z1rp'], f['z2rp']], 'jca', '( %s e. RR+ /\\ %s e. RR+ )' % (Z1, Z2)), aj)
    chv = a1(w, aj, w.s([w.s([], 'nnex', 'NN e. _V')], 'mptex', '%s e. _V' % CH), '%s e. _V' % CH)
    pfvj = a1(w, aj, w.s([], 'ovex', '%s e. _V' % PF), '%s e. _V' % PF)
    FDn = FDT(Z1, Z2, PF, XP, CH, '( P ` j )', 'n')
    fd = sj([sj([z12, sj([pfvj, lift(w, f['xprp'], aj), chv], '3jca', '( %s e. _V /\\ %s e. RR+ /\\ %s e. _V )' % (PF, XP, CH))], 'jca',
                '( ( %s e. RR+ /\\ %s e. RR+ ) /\\ ( %s e. _V /\\ %s e. RR+ /\\ %s e. _V ) )' % (Z1, Z2, PF, XP, CH)), pc2, w.inst('z5fdetval')], 'syl2anc',
            '%s = sum_ n e. NN %s' % (L.FDJ('j'), FDn))
    ajn2 = '( %s /\\ n e. NN )' % aj
    sn = mkst(w, ajn2)
    Ln = lambda s_: lift(w, s_, ajn2)
    An = lambda s_: adlr(s_, a, ['j e. J'])
    nn2 = sn([], 'simpr', 'n e. NN')
    xv2 = xval(w, ajn2, Ln(jin2), nn2, 'j', 'n')
    XA = '( ( Q ` j ) ` %s )' % ZRn('n')
    chn, _ = mpv(w, ajn2, 'a', 'NN', '( ( Q ` j ) ` %s )' % ZRn('a'), 'n', nn2)
    xac = chcc(w, ajn2, Ln(lift(w, nnn, aj)), Ln(qj2), nn2, '( Q ` j )', 'n')
    NS = '( n ^c -u %s )' % SJ('j'); NP = '( n ^c -u ( P ` j ) )'
    ncn = sn([nn2], 'nncnd', 'n e. CC'); nne = sn([nn2], 'nnne0d', 'n =/= 0')
    tcn = sn([Ln(lift(w, tr, aj))], 'recnd', 'T e. CC')
    pcn = Ln(pc2)
    ntc = sn([An(s3([ntrp], 'rpred', '%s e. RR' % NT))], 'recnd', '%s e. CC' % NT)
    nsc = sn([ncn, sn([Ln(scj)], 'negcld', '-u %s e. CC' % SJ('j'))], 'cxpcld', '%s e. CC' % NS)
    a3c = sn([An(a3r)], 'recnd', '%s e. CC' % A3)
    cdv2 = An(cdv)
    t1 = sn([cdv2, xv2], 'oveq12d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (CDn, XJN, CVn, XA, NS))
    # case Z1 < n
    ac = '( %s /\\ %s < n )' % (ajn2, Z1)
    sc_ = mkst(w, ac)
    Lc = lambda s_: lift(w, s_, ac)
    c1 = sc_([], 'simpr', '%s < n' % Z1)
    it = sc_([c1, w.inst('iftrue')], 'syl', '%s = %s' % (CVn, CTn))
    CTn_ = '( %s x. %s )' % (A3, NT)
    m4 = sc_([Lc(a3c), Lc(ntc), Lc(xac), Lc(nsc)], 'mul4d', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (CTn_, XA, NS, A3, XA, NT, NS))
    EX = '( -u T + -u %s )' % SJ('j')
    clc = Closure(w, ac, {'( P ` j )': Lc(pcn), 'T': Lc(tcn)})
    ex1 = ringeq(w, ac, EX, '-u ( P ` j )', clc)
    cxa = sc_([Lc(ncn), Lc(nne), sc_([Lc(tcn)], 'negcld', '-u T e. CC'), sc_([Lc(Ln(scj))], 'negcld', '-u %s e. CC' % SJ('j'))], 'cxpaddd',
              '( n ^c %s ) = ( %s x. %s )' % (EX, NT, NS))
    npv = sc_([sc_([ex1], 'oveq2d', '( n ^c %s ) = %s' % (EX, NP)), cxa], 'eqtr3d', '%s = ( %s x. %s )' % (NP, NT, NS))
    ch2 = sc_([sc_([Lc(chn)], 'oveq2d', '( %s x. ( %s ` n ) ) = ( %s x. %s )' % (A3, CH, A3, XA)), npv], 'oveq12d',
              '( ( %s x. ( %s ` n ) ) x. %s ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (A3, CH, NP, A3, XA, NT, NS))
    fdt = sc_([c1, w.inst('iftrue')], 'syl', '%s = ( ( %s x. ( %s ` n ) ) x. %s )' % (FDn, A3, CH, NP))
    cT = sc_([sc_([sc_([it], 'oveq1d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (CVn, XA, NS, CTn_, XA, NS)), m4], 'eqtrd',
                  '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (CVn, XA, NS, A3, XA, NT, NS)),
              sc_([fdt, ch2], 'eqtrd', '%s = ( ( %s x. %s ) x. ( %s x. %s ) )' % (FDn, A3, XA, NT, NS))], 'eqtr4d', '( %s x. ( %s x. %s ) ) = %s' % (CVn, XA, NS, FDn))
    anc = '( %s /\\ -. %s < n )' % (ajn2, Z1)
    sf_ = mkst(w, anc)
    Lf = lambda s_: lift(w, s_, anc)
    c0 = sf_([], 'simpr', '-. %s < n' % Z1)
    iff = sf_([c0, w.inst('iffalse')], 'syl', '%s = 0' % CVn)
    fdf = sf_([c0, w.inst('iffalse')], 'syl', '%s = 0' % FDn)
    cF = sf_([sf_([sf_([iff], 'oveq1d', '( %s x. ( %s x. %s ) ) = ( 0 x. ( %s x. %s ) )' % (CVn, XA, NS, XA, NS)),
                   sf_([sf_([Lf(xac), Lf(nsc)], 'mulcld', '( %s x. %s ) e. CC' % (XA, NS))], 'mul02d', '( 0 x. ( %s x. %s ) ) = 0' % (XA, NS))], 'eqtrd',
                  '( %s x. ( %s x. %s ) ) = 0' % (CVn, XA, NS)), fdf], 'eqtr4d', '( %s x. ( %s x. %s ) ) = %s' % (CVn, XA, NS, FDn))
    cc = w.s([cT, cF], 'pm2.61dan', '( %s -> ( %s x. ( %s x. %s ) ) = %s )' % (ajn2, CVn, XA, NS, FDn))
    term = sn([t1, cc], 'eqtrd', '( %s x. %s ) = %s' % (CDn, XJN, FDn))
    SL = 'sum_ n e. NN ( %s x. %s )' % (CDn, XJN)
    se = sj([term], 'sumeq2dv', '%s = sum_ n e. NN %s' % (SL, FDn))
    fdj = sj([se, fd], 'eqtr4d', '%s = %s' % (SL, L.FDJ('j')))
    lhs = st([st([sj([fdj], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (SL, L.FDJ('j')))], 'sumeq2dv',
                 'sum_ j e. J ( abs ` %s ) = sum_ j e. J ( abs ` %s )' % (SL, L.FDJ('j')))], 'oveq1d',
             '%s = ( sum_ j e. J ( abs ` %s ) ^ 2 )' % (L1, L.FDJ('j')))
    # ---- (R): the Gram entries
    ajk = '( %s /\\ k e. J )' % aj
    sk_ = mkst(w, ajk)
    kin = sk_([], 'simpr', 'k e. J')
    qk, pck, tlek = jfacts(w, ajk, lift(w, al, ajk), kin, 'k')
    sck, s0k = sjfacts(w, ajk, pck, tlek, lift(w, tr, ajk), 'k')
    ajkn = '( %s /\\ n e. NN )' % ajk
    sr = mkst(w, ajkn)
    Lr = lambda s_: lift(w, s_, ajkn)
    nn4 = sr([], 'simpr', 'n e. NN')
    xvj = xval(w, ajkn, Lr(lift(w, jin2, ajk)), nn4, 'j', 'n')
    xvk = xval(w, ajkn, Lr(kin), nn4, 'k', 'n')
    XKN = '( ( %s ` k ) ` n )' % XX
    bkc = sr([adlr(bkr, a, ['j e. J', 'k e. J'])], 'recnd', '%s e. CC' % BK)
    chbj = sr([sr([Lr(lift(w, nnn, ajk)), Lr(lift(w, qj2, ajk))], 'jca', '( N e. NN /\\ ( Q ` j ) e. %s )' % DB), Lr(lift(w, scj, ajk)), Lr(lift(w, s0j, ajk)), nn4,
                w.inst('gf1chb')], 'syl121anc', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (XVB('j', 'n'), XVB('j', 'n')))
    chbk = sr([sr([Lr(lift(w, nnn, ajk)), Lr(qk)], 'jca', '( N e. NN /\\ ( Q ` k ) e. %s )' % DB), Lr(sck), Lr(s0k), nn4,
                w.inst('gf1chb')], 'syl121anc', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (XVB('k', 'n'), XVB('k', 'n')))
    xjc = sr([chbj], 'simpld', '%s e. CC' % XVB('j', 'n')); xkc = sr([chbk], 'simpld', '%s e. CC' % XVB('k', 'n'))
    chc = sr([sr([Lr(lift(w, nnn, ajk)), sr([Lr(lift(w, qj2, ajk)), Lr(qk)], 'jca', '( ( Q ` j ) e. %s /\\ ( Q ` k ) e. %s )' % (DB, DB))], 'jca',
                 '( N e. NN /\\ ( ( Q ` j ) e. %s /\\ ( Q ` k ) e. %s ) )' % (DB, DB)),
              sr([Lr(lift(w, scj, ajk)), Lr(sck)], 'jca', '( %s e. CC /\\ %s e. CC )' % (SJ('j'), SJ('k'))), nn4, w.inst('gf1chc')], 'syl3anc',
             '( %s x. ( * ` %s ) ) = ( ( %s ` %s ) x. ( n ^c -u %s ) )' % (XVB('j', 'n'), XVB('k', 'n'), L.XJK, ZRn('n'), L.SJK))
    G1T = '( ( ( %s ` n ) x. %s ) x. ( * ` %s ) )' % (BM, '( ( %s ` j ) ` n )' % XX, XKN)
    r1 = sr([sr([xvj], 'oveq2d', '( %s x. ( ( %s ` j ) ` n ) ) = ( %s x. %s )' % (BK, XX, BK, XVB('j', 'n'))), sr([xvk], 'fveq2d', '( * ` %s ) = ( * ` %s )' % (XKN, XVB('k', 'n')))],
            'oveq12d', '%s = ( ( %s x. %s ) x. ( * ` %s ) )' % (G1T, BK, XVB('j', 'n'), XVB('k', 'n')))
    r2 = sr([bkc, xjc, sr([xkc], 'cjcld', '( * ` %s ) e. CC' % XVB('k', 'n'))], 'mulassd',
            '( ( %s x. %s ) x. ( * ` %s ) ) = ( %s x. ( %s x. ( * ` %s ) ) )' % (BK, XVB('j', 'n'), XVB('k', 'n'), BK, XVB('j', 'n'), XVB('k', 'n')))
    XJKn = '( %s ` %s )' % (L.XJK, ZRn('n')); NSJK = '( n ^c -u %s )' % L.SJK
    r3 = sr([chc], 'oveq2d', '( %s x. ( %s x. ( * ` %s ) ) ) = ( %s x. ( %s x. %s ) )' % (BK, XVB('j', 'n'), XVB('k', 'n'), BK, XJKn, NSJK))
    jkc = chcc2(w, ajkn, Lr(lift(w, nnn, ajk)), Lr(lift(w, qj2, ajk)), Lr(qk), nn4)
    nsjc = sr([sr([nn4], 'nncnd', 'n e. CC'), sr([sr([Lr(lift(w, scj, ajk)), sr([Lr(sck)], 'cjcld', '( * ` %s ) e. CC' % SJ('k'))], 'addcld',
                                                                                     '%s e. CC' % L.SJK)], 'negcld', '-u %s e. CC' % L.SJK)], 'cxpcld', '%s e. CC' % NSJK)
    r4 = sr([bkc, jkc, nsjc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (BK, XJKn, NSJK, BK, XJKn, NSJK))
    GT2 = '( ( %s x. %s ) x. %s )' % (BK, XJKn, NSJK)
    rt = sr([sr([sr([r1, r2], 'eqtrd', '%s = ( %s x. ( %s x. ( * ` %s ) ) )' % (G1T, BK, XVB('j', 'n'), XVB('k', 'n'))), r3], 'eqtrd',
                '%s = ( %s x. ( %s x. %s ) )' % (G1T, BK, XJKn, NSJK)), r4], 'eqtr4d', '%s = %s' % (G1T, GT2))
    GS2 = L.BGX(L.XJK, L.SJK, 'n')
    rs = sk_([rt], 'sumeq2dv', '%s = %s' % (G1S, GS2))
    rk = sj([sk_([rs], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (G1S, GS2))], 'sumeq2dv', 'sum_ k e. J ( abs ` %s ) = sum_ k e. J ( abs ` %s )' % (G1S, GS2))
    rj = st([rk], 'sumeq2dv', '%s = %s' % (GRAM(G1S), GRAM(GS2)))
    # ---- (Q)
    qs = st([aq], 'sumeq2dv', 'sum_ n e. NN %s = sum_ n e. NN %s' % (ANn('n'), L.QT('n')))
    rhs = st([qs, rj], 'oveq12d', '%s = ( sum_ n e. NN %s x. %s )' % (R1, L.QT('n'), GRAM(GS2)))
    CONC = split_imp(S_['gf2hal'])[1]
    fin = st([hal, lhs, rhs], '3brtr3d', CONC)
    # the frozen antecedent: rename the bound j to i
    idj = w.s([], 'id', '( j = i -> j = i )')
    sbj, _ = w.wcongr(PSI_('j'), {'j': 'i'}, 'j = i', {'j': idj})
    cb = w.s([sbj], 'cbvralvw', '( A. j e. J %s <-> A. i e. J %s )' % (PSI_('j'), PSI_('i')))
    b2 = w.s([cb], 'anbi2i', '( ( J e. Fin /\\ A. j e. J %s ) <-> ( J e. Fin /\\ A. i e. J %s ) )' % (PSI_('j'), PSI_('i')))
    A0 = split_imp(S_['gf2hal'])[0]
    b3 = w.s([b2], 'anbi2i', '( %s <-> %s )' % (A0, a))
    w.qed([b3, fin], 'sylbi', S_['gf2hal'])
    return w


def chcc(w, ante, nnn, qj, nin, X, n):
    """( ante -> ( X ` ZR(n) ) e. CC ) from qj ( ante -> X e. Base DChr N ) (dchrf, znzrhfo)"""
    st = mkst(w, ante)
    G = '( DChr ` N )'; Z = '( Z/nZ ` N )'
    fz = st([w.s([], 'eqid', '%s = %s' % (G, G)), w.s([], 'eqid', '%s = %s' % (Z, Z)), w.s([], 'eqid', '( Base ` %s ) = ( Base ` %s )' % (G, G)),
             w.s([], 'eqid', '( Base ` %s ) = ( Base ` %s )' % (Z, Z)), qj], 'dchrf', '%s : ( Base ` %s ) --> CC' % (X, Z))
    zr = w.s([w.s([], 'eqid', '%s = %s' % (Z, Z)), w.s([], 'eqid', '( Base ` %s ) = ( Base ` %s )' % (Z, Z)), w.s([], 'eqid', '( ZRHom ` %s ) = ( ZRHom ` %s )' % (Z, Z))],
             'znzrhfo', '( N e. NN0 -> ( ZRHom ` %s ) : ZZ -onto-> ( Base ` %s ) )' % (Z, Z))
    zo = st([st([nnn], 'nnnn0d', 'N e. NN0'), zr], 'syl', '( ZRHom ` %s ) : ZZ -onto-> ( Base ` %s )' % (Z, Z))
    zf = st([zo, w.inst('fof')], 'syl', '( ZRHom ` %s ) : ZZ --> ( Base ` %s )' % (Z, Z))
    zv = st([zf, st([nin], 'nnzd', '%s e. ZZ' % n)], 'ffvelcdmd', '%s e. ( Base ` %s )' % (ZRn(n), Z))
    return st([fz, zv], 'ffvelcdmd', '( %s ` %s ) e. CC' % (X, ZRn(n)))


def chcc2(w, ante, nnn, qj, qk, nin):
    """( ante -> ( XJK ` ZR(n) ) e. CC ): the product character is a character (dchrabl, grpcld, grpinvcld)"""
    st = mkst(w, ante)
    G = '( DChr ` N )'; B = '( Base ` %s )' % G
    ab = st([nnn, w.s([w.s([], 'eqid', '%s = %s' % (G, G))], 'dchrabl', '( N e. NN -> %s e. Abel )' % G)], 'syl', '%s e. Abel' % G)
    gg = st([ab], 'ablgrpd', '%s e. Grp' % G)
    iv = st([w.s([], 'eqid', '%s = %s' % (B, B)), w.s([], 'eqid', '( invg ` %s ) = ( invg ` %s )' % (G, G)), gg, qk], 'grpinvcld',
            '( ( invg ` %s ) ` ( Q ` k ) ) e. %s' % (G, B))
    pr = st([w.s([], 'eqid', '%s = %s' % (B, B)), w.s([], 'eqid', '( +g ` %s ) = ( +g ` %s )' % (G, G)), gg, qj, iv], 'grpcld', '%s e. %s' % (L.XJK, B))
    return chcc(w, ante, nnn, pr, nin, L.XJK, 'n')


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
