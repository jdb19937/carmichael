"""Sortie T21a: t21gz, the grid + geometric assembly shared by zones II and III."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_
import num, lin
import cl as _cl
lin.FASTPATH = True
from tm import W


def cond_text(a, t, e=EX):
    return '( q e. CC /\\ ( ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ %s ) /\\ ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (a, t, e)


def gen_gz():
    w = W('t21gz', 'Zone from grid tails: if the tail sums at the grid points ` sigma_k = S + k / log X <_ T ` are at most ` Q N ^ ( ( 9 / 2 ) ( 1 - sigma_k ) ) ` , the zone ` S <_ beta < T ` at height ` X ^ 3 ` weighs at most ` Q 64 Y X ^ ( - ( 9 / 200 ) ( 1 - T ) ) ` (the grid and geometric steps of Lean ` zoneII_le ` , ` zoneIII_le ` ; ~ t21grid , ~ t21ggeo , ~ t21d92 ).')
    for k_ in sorted(GZH):
        w.lines.append('h%d::t21gz.%d |- %s' % (k_, k_, GZH[k_]))
    C0 = 'ph'
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C0, f))
    L_ = lambda s_, A_: _cl.lift(w, s_, A_)
    H1 = GZH[1].split(' -> ', 1)[1][:-2]
    u = unpack_step(w, C0, '1', H1)
    nn, xr, xe, yr, nx, ny, yx, sr, tr, hs, sT, t1, qr, q0 = [u[k] for k in ['N e. NN', 'X e. RR', '( exp ` 1 ) <_ X', 'Y e. RR', 'N <_ ( X ^c %s )' % F191,
        '( N x. ( X ^c %s ) ) <_ Y' % F709, 'Y <_ X', 'S e. RR', 'T e. RR', '%s <_ S' % HALF, 'S <_ T', 'T <_ 1', 'Q e. RR', '0 <_ Q']]
    L = LX; h = LH
    one = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR')
    e1r = st([one], 'reefcld', '( exp ` 1 ) e. RR')
    eg1 = ap_(w, C0, [st([w.s([], '1rp', '1 e. RR+')], 'a1i', '1 e. RR+')], 'efgt1', '1 < ( exp ` 1 )')
    x1 = lin.linarith(w, C0, [eg1, xe], '1 <_ X', leaves={'X': xr, '( exp ` 1 )': e1r})
    xp = st([xr, lin.linarith(w, C0, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    lr = st([xp], 'relogcld', '%s e. RR' % L)
    e1p = st([one], 'rpefcld', '( exp ` 1 ) e. RR+')
    lge = st([xe, st([e1p, xp], 'logled', '( ( exp ` 1 ) <_ X <-> ( log ` ( exp ` 1 ) ) <_ %s )' % L)], 'mpbid', '( log ` ( exp ` 1 ) ) <_ %s' % L)
    l1 = st([st([ap_(w, C0, [one], 'relogef', '( log ` ( exp ` 1 ) ) = 1')], 'eqcomd', '1 = ( log ` ( exp ` 1 ) )'), lge], 'eqbrtrd', '1 <_ %s' % L)
    lp = st([lr, lin.linarith(w, C0, [l1], '0 < %s' % L, leaves={L: lr})], 'elrpd', '%s e. RR+' % L)
    hp = st([lp], 'rpreccld', '%s e. RR+' % h); hr = st([hp], 'rpred', '%s e. RR' % h)
    nr = st([nn], 'nnred', 'N e. RR'); n1 = st([nn], 'nnge1d', '1 <_ N')
    # Y >= 1
    X7 = '( X ^c %s )' % F709
    x70 = st([xr, x1, st([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), st([num.real(w, F709)], 'a1i', '%s e. RR' % F709), st([num.le_lit(w, '0', F709)], 'a1i', '0 <_ %s' % F709)], 'cxplead', '( X ^c 0 ) <_ %s' % X7)
    x0e = st([st([xr], 'recnd', 'X e. CC')], 'cxp0d', '( X ^c 0 ) = 1')
    x71 = st([x0e, x70], 'eqbrtrrd', '1 <_ %s' % X7)
    x7r = st([xp, st([num.real(w, F709)], 'a1i', '%s e. RR' % F709)], 'rpcxpcld', '%s e. RR+' % X7)
    m11 = st([one, nr, one, st([x7r], 'rpred', '%s e. RR' % X7), st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), st([w.s([], '0le1', '0 <_ 1')], 'a1i', '0 <_ 1'), n1, x71], 'lemul12ad', '( 1 x. 1 ) <_ ( N x. %s )' % X7)
    m11b = st([st([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1'), m11], 'eqbrtrrd', '1 <_ ( N x. %s )' % X7)
    y1 = st([one, st([nr, st([x7r], 'rpred', '%s e. RR' % X7)], 'remulcld', '( N x. %s ) e. RR' % X7), yr, m11b, ny], 'letrd', '1 <_ Y')
    d92 = ap_(w, C0, [xr, x1, nr, n1, nx, yr, ny], 't21d92', '( N ^c %s ) <_ ( ( X ^c -u %s ) x. Y )' % (F92, F9200))
    # the grid length
    TSL = '( ( T - S ) x. %s )' % L
    tsr = st([tr, sr], 'resubcld', '( T - S ) e. RR')
    ts0 = st([sT, st([tr, sr], 'subge0d', '( 0 <_ ( T - S ) <-> S <_ T )')], 'mpbird', '0 <_ ( T - S )')
    tslr = st([tsr, lr], 'remulcld', '%s e. RR' % TSL)
    tsl0 = st([tsr, lr, ts0, st([lp], 'rpge0d', '0 <_ %s' % L)], 'mulge0d', '0 <_ %s' % TSL)
    NF = '( |_ ` %s )' % TSL; MG_ = '( %s + 1 )' % NF
    nf = ap_(w, C0, [tslr, tsl0], 'flge0nn0', '%s e. NN0' % NF)
    mg = ap_(w, C0, [nf], 'peano2nn0', '%s e. NN0' % MG_)
    mgr = st([mg], 'nn0red', '%s e. RR' % MG_)
    tm = ap_(w, C0, [tslr], 'flltp1', '%s < %s' % (TSL, MG_))
    tm2 = st([tm, st([tsr, mgr, lp], 'ltmuldivd', '( %s < %s <-> ( T - S ) < ( %s / %s ) )' % (TSL, MG_, MG_, L))], 'mpbid', '( T - S ) < ( %s / %s )' % (MG_, L))
    dv = st([st([mgr], 'recnd', '%s e. CC' % MG_), st([lp], 'rpcnd', '%s e. CC' % L), st([lp], 'rpne0d', '%s =/= 0' % L)], 'divrecd', '( %s / %s ) = ( %s x. %s )' % (MG_, L, MG_, h))
    MH = '( %s x. %s )' % (MG_, h)
    tm3 = st([tm2, dv], 'breqtrd', '( T - S ) < %s' % MH)
    tmh = lin.linarith(w, C0, [tm3], 'T <_ ( S + %s )' % MH, leaves={'T': tr, 'S': sr, MH: st([mgr, hr], 'remulcld', '%s e. RR' % MH)})
    X3r = st([xr, st([w.s([], '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')], 'reexpcld', '%s e. RR' % X3)
    # ---- grid hypotheses
    DBfin = w.s([nn, w.s([w.s([], 'eqid', '( DChr ` N ) = ( DChr ` N )'), w.s([], 'eqid', '%s = %s' % (DB, DB))], 'dchrfi', '( N e. NN -> %s e. Fin )' % DB)], 'syl', '( ph -> %s e. Fin )' % DB)
    ZS_, ZT_ = ZFX('S', X3), ZFX('T', X3)
    AA = '( %s \\ %s )' % (ZS_, ZT_)
    C1 = '( ph /\\ x e. %s )' % DB
    xin = w.s([], 'simpr', '( %s -> x e. %s )' % (C1, DB))
    s0 = lin.linarith(w, C0, [hs], '0 < S', leaves={'S': sr})
    s1 = lin.linarith(w, C0, [sT, t1], 'S <_ 1', leaves={'S': sr, 'T': tr})
    ezS = ap_(w, C1, [L_(nn, C1), xin, L_(sr, C1), L_(s0, C1), L_(s1, C1), L_(X3r, C1)], 'ezf', '( %s e. Fin /\\ A. q e. %s %s e. NN )' % (ZS_, ZS_, ORD()))
    g2 = ap_(w, C1, [w.s([ezS], 'simpld', '( %s -> %s e. Fin )' % (C1, ZS_))], 'diffi', '%s e. Fin' % AA)
    # g3
    C2 = '( %s /\\ q e. %s )' % (C1, AA)
    ed = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (C2, AA)), w.s([], 'eldif', '( q e. %s <-> ( q e. %s /\\ -. q e. %s ) )' % (AA, ZS_, ZT_))], 'sylib', '( %s -> ( q e. %s /\\ -. q e. %s ) )' % (C2, ZS_, ZT_))
    qS = w.s([ed], 'simpld', '( %s -> q e. %s )' % (C2, ZS_)); qnT = w.s([ed], 'simprd', '( %s -> -. q e. %s )' % (C2, ZT_))
    elS = ap_(w, C2, [L_(sr, C2), L_(X3r, C2)], 't21zfel', '( q e. %s <-> %s )' % (ZS_, cond_text('S', X3)))
    cS = w.s([qS, elS], 'mpbid', '( %s -> %s )' % (C2, cond_text('S', X3)))
    qc = w.s([cS], 'simp1d', '( %s -> q e. CC )' % C2)
    mS = w.s([cS], 'simp2d', '( %s -> ( ( S <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ %s ) )' % (C2, X3))
    zS = w.s([cS], 'simp3d', '( %s -> ( q =/= 1 /\\ ( %s ` q ) = 0 ) )' % (C2, EX))
    rrS = w.s([mS], 'simpld', '( %s -> ( S <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) )' % C2)
    lo = w.s([rrS], 'simpld', '( %s -> S <_ ( Re ` q ) )' % C2); hi = w.s([rrS], 'simprd', '( %s -> ( Re ` q ) <_ 1 )' % C2)
    imS = w.s([mS], 'simprd', '( %s -> ( abs ` ( Im ` q ) ) <_ %s )' % (C2, X3))
    re = w.s([qc], 'recld', '( %s -> ( Re ` q ) e. RR )' % C2)
    C2t = '( %s /\\ T <_ ( Re ` q ) )' % C2
    cT = w.s([L_(qc, C2t), w.s([w.s([w.s([], 'simpr', '( %s -> T <_ ( Re ` q ) )' % C2t), L_(hi, C2t)], 'jca', '( %s -> ( T <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) )' % C2t), L_(imS, C2t)], 'jca',
              '( %s -> ( ( T <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ %s ) )' % (C2t, X3)), L_(zS, C2t)], '3jca', '( %s -> %s )' % (C2t, cond_text('T', X3)))
    elT = ap_(w, C2t, [L_(tr, C2t), L_(X3r, C2t)], 't21zfel', '( q e. %s <-> %s )' % (ZT_, cond_text('T', X3)))
    qT = w.s([cT, elT], 'mpbird', '( %s -> q e. %s )' % (C2t, ZT_))
    imp = w.s([qT], 'ex', '( %s -> ( T <_ ( Re ` q ) -> q e. %s ) )' % (C2, ZT_))
    nle = w.s([qnT, w.s([imp], 'con3d', '( %s -> ( -. q e. %s -> -. T <_ ( Re ` q ) ) )' % (C2, ZT_))], 'mpd', '( %s -> -. T <_ ( Re ` q ) )' % C2)
    rlt = w.s([nle, w.s([re, L_(tr, C2)], 'ltnled', '( %s -> ( ( Re ` q ) < T <-> -. T <_ ( Re ` q ) ) )' % C2)], 'mpbird', '( %s -> ( Re ` q ) < T )' % C2)
    ordn = w.s([L_(w.s([ezS], 'simprd', '( %s -> A. q e. %s %s e. NN )' % (C1, ZS_, ORD())), C2), qS, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (ZS_, ORD(), ZS_, ORD()))], 'sylc', '( %s -> %s e. NN )' % (C2, ORD()))
    orr = w.s([ordn], 'nnred', '( %s -> %s e. RR )' % (C2, ORD())); or0 = w.s([w.s([ordn], 'nnnn0d', '( %s -> %s e. NN0 )' % (C2, ORD()))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (C2, ORD()))
    qf = dict(imr=w.s([w.s([w.s([qc], 'imcld', '( %s -> ( Im ` q ) e. RR )' % C2)], 'recnd', '( %s -> ( Im ` q ) e. CC )' % C2)], 'abscld', '( %s -> ( abs ` ( Im ` q ) ) e. RR )' % C2),
              im0=w.s([w.s([w.s([qc], 'imcld', '( %s -> ( Im ` q ) e. RR )' % C2)], 'recnd', '( %s -> ( Im ` q ) e. CC )' % C2)], 'absge0d', '( %s -> 0 <_ ( abs ` ( Im ` q ) ) )' % C2))
    wr, w0, _ = wt_facts(w, C2, orr, or0, qf)
    g3 = w.s([w.s([qc, w.s([wr, w0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (C2, WT(), WT()))], 'jca', '( %s -> ( q e. CC /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (C2, WT(), WT())),
              w.s([lo, rlt], 'jca', '( %s -> ( S <_ ( Re ` q ) /\\ ( Re ` q ) < T ) )' % C2)], 'jca',
             '( %s -> ( ( q e. CC /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ ( S <_ ( Re ` q ) /\\ ( Re ` q ) < T ) ) )' % (C2, WT(), WT()))
    # ---- k facts under Ck = ( ph /\ k e. ( 0 ..^ MG ) )
    FZ = '( 0 ..^ %s )' % MG_
    Ck = '( ph /\\ k e. %s )' % FZ
    Lk = lambda s_: L_(s_, Ck)
    kin = w.s([], 'simpr', '( %s -> k e. %s )' % (Ck, FZ))
    kn = ap_(w, Ck, [kin], 'elfzonn0', 'k e. NN0')
    kz = w.s([kn], 'nn0zd', '( %s -> k e. ZZ )' % Ck); kr = w.s([kn], 'nn0red', '( %s -> k e. RR )' % Ck)
    nfz = Lk(st([nf], 'nn0zd', '%s e. ZZ' % NF)); nfr = w.s([nfz], 'zred', '( %s -> %s e. RR )' % (Ck, NF))
    klt = ap_(w, Ck, [kin], 'elfzolt2', 'k < %s' % MG_)
    kle = w.s([klt, ap_(w, Ck, [kz, nfz], 'zleltp1', '( k <_ %s <-> k < %s )' % (NF, MG_))], 'mpbird', '( %s -> k <_ %s )' % (Ck, NF))
    nfle = ap_(w, C0, [tslr], 'flle', '%s <_ %s' % (NF, TSL))
    ktsl = w.s([kr, nfr, Lk(tslr), kle, Lk(nfle)], 'letrd', '( %s -> k <_ %s )' % (Ck, TSL))
    kd = w.s([ktsl, w.s([kr, Lk(tsr), Lk(lp)], 'ledivmul2d', '( %s -> ( ( k / %s ) <_ ( T - S ) <-> k <_ %s ) )' % (Ck, L, TSL))], 'mpbird', '( %s -> ( k / %s ) <_ ( T - S ) )' % (Ck, L))
    kh = w.s([w.s([kr], 'recnd', '( %s -> k e. CC )' % Ck), Lk(st([lp], 'rpcnd', '%s e. CC' % L)), Lk(st([lp], 'rpne0d', '%s =/= 0' % L))], 'divrecd', '( %s -> ( k / %s ) = ( k x. %s ) )' % (Ck, L, h))
    KH = '( k x. %s )' % h; SKt = '( S + %s )' % KH
    kd2 = w.s([kh, kd], 'eqbrtrrd', '( %s -> %s <_ ( T - S ) )' % (Ck, KH))
    khr = w.s([kr, Lk(hr)], 'remulcld', '( %s -> %s e. RR )' % (Ck, KH))
    kh0 = w.s([kr, Lk(hr), w.s([kn], 'nn0ge0d', '( %s -> 0 <_ k )' % Ck), Lk(st([hp], 'rpge0d', '0 <_ %s' % h))], 'mulge0d', '( %s -> 0 <_ %s )' % (Ck, KH))
    lvk = {'S': Lk(sr), 'T': Lk(tr), KH: khr}
    skT = lin.linarith(w, Ck, [kd2], '%s <_ T' % SKt, leaves=lvk)
    sSk = lin.linarith(w, Ck, [kh0], 'S <_ %s' % SKt, leaves=lvk)
    sk0 = lin.linarith(w, Ck, [kh0, Lk(s0)], '0 < %s' % SKt, leaves=lvk)
    sk1 = lin.linarith(w, Ck, [kd2, Lk(t1)], '%s <_ 1' % SKt, leaves=lvk)
    skr = w.s([Lk(sr), khr], 'readdcld', '( %s -> %s e. RR )' % (Ck, SKt))
    # ---- g4 under C3 = ( C1 /\ k e. FZ )
    C3 = '( %s /\\ k e. %s )' % (C1, FZ)
    m3 = w.s([w.s([], 'simpll', '( %s -> ph )' % C3), w.s([], 'simpr', '( %s -> k e. %s )' % (C3, FZ))], 'jca', '( %s -> %s )' % (C3, Ck))
    via = lambda s_, f: w.s([m3, s_], 'syl', '( %s -> %s )' % (C3, f))
    ZK = ZFX(SKt, X3)
    xin3 = w.s([], 'simplr', '( %s -> x e. %s )' % (C3, DB))
    ezK = ap_(w, C3, [L_(nn, C3), xin3, via(skr, '%s e. RR' % SKt), via(sk0, '0 < %s' % SKt), via(sk1, '%s <_ 1' % SKt), L_(X3r, C3)], 'ezf', '( %s e. Fin /\\ A. q e. %s %s e. NN )' % (ZK, ZK, ORD()))
    kfin = w.s([ezK], 'simpld', '( %s -> %s e. Fin )' % (C3, ZK))
    C3q = '( %s /\\ q e. %s )' % (C3, ZK)
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (C3q, ZK))
    qfk = q_facts(w, C3q, qin, L_(via(skr, '%s e. RR' % SKt), C3q), L_(X3r, C3q), SKt, X3)
    ordk = w.s([L_(w.s([ezK], 'simprd', '( %s -> A. q e. %s %s e. NN )' % (C3, ZK, ORD())), C3q), qin, w.s([], 'rsp', '( A. q e. %s %s e. NN -> ( q e. %s -> %s e. NN ) )' % (ZK, ORD(), ZK, ORD()))], 'sylc', '( %s -> %s e. NN )' % (C3q, ORD()))
    wrk, w0k, _ = wt_facts(w, C3q, w.s([ordk], 'nnred', '( %s -> %s e. RR )' % (C3q, ORD())), w.s([w.s([ordk], 'nnnn0d', '( %s -> %s e. NN0 )' % (C3q, ORD()))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (C3q, ORD())), qfk)
    ral1 = w.s([w.s([wrk, w0k], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (C3q, WT(), WT()))], 'ralrimiva', '( %s -> A. q e. %s ( %s e. RR /\\ 0 <_ %s ) )' % (C3, ZK, WT(), WT()))
    C3a = '( ( %s /\\ q e. %s ) /\\ %s <_ ( Re ` q ) )' % (C3, AA, SKt)
    m2 = w.s([w.s([w.s([w.s([], 'simpl', '( %s -> ( %s /\\ q e. %s ) )' % (C3a, C3, AA))], 'simpld', '( %s -> %s )' % (C3a, C3)), w.s([], 'simpl', '( %s -> %s )' % (C3, C1))], 'syl', '( %s -> %s )' % (C3a, C1)),
              w.s([w.s([], 'simpl', '( %s -> ( %s /\\ q e. %s ) )' % (C3a, C3, AA))], 'simprd', '( %s -> q e. %s )' % (C3a, AA))], 'jca', '( %s -> %s )' % (C3a, C2))
    v2 = lambda s_, f: w.s([m2, s_], 'syl', '( %s -> %s )' % (C3a, f))
    m3a = w.s([w.s([w.s([], 'simpl', '( %s -> ( %s /\\ q e. %s ) )' % (C3a, C3, AA))], 'simpld', '( %s -> %s )' % (C3a, C3)), m3], 'syl', '( %s -> %s )' % (C3a, Ck))
    cK = w.s([v2(qc, 'q e. CC'), w.s([w.s([w.s([], 'simpr', '( %s -> %s <_ ( Re ` q ) )' % (C3a, SKt)), v2(hi, '( Re ` q ) <_ 1')], 'jca', '( %s -> ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) )' % (C3a, SKt)), v2(imS, '( abs ` ( Im ` q ) ) <_ %s' % X3)], 'jca',
              '( %s -> ( ( %s <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 ) /\\ ( abs ` ( Im ` q ) ) <_ %s ) )' % (C3a, SKt, X3)), v2(zS, '( q =/= 1 /\\ ( %s ` q ) = 0 )' % EX)], '3jca', '( %s -> %s )' % (C3a, cond_text(SKt, X3)))
    elK = ap_(w, C3a, [w.s([m3a, skr], 'syl', '( %s -> %s e. RR )' % (C3a, SKt)), L_(X3r, C3a)], 't21zfel', '( q e. %s <-> %s )' % (ZK, cond_text(SKt, X3)))
    qK = w.s([cK, elK], 'mpbird', '( %s -> q e. %s )' % (C3a, ZK))
    ral2 = w.s([w.s([qK], 'ex', '( ( %s /\\ q e. %s ) -> ( %s <_ ( Re ` q ) -> q e. %s ) )' % (C3, AA, SKt, ZK))], 'ralrimiva', '( %s -> A. q e. %s ( %s <_ ( Re ` q ) -> q e. %s ) )' % (C3, AA, SKt, ZK))
    g4 = w.s([kfin, ral1, ral2], '3jca', '( %s -> ( %s e. Fin /\\ A. q e. %s ( %s e. RR /\\ 0 <_ %s ) /\\ A. q e. %s ( %s <_ ( Re ` q ) -> q e. %s ) ) )' % (C3, ZK, ZK, WT(), WT(), AA, SKt, ZK))
    # ---- g5, g6
    g5 = st([st([yr, y1], 'jca', '( Y e. RR /\\ 1 <_ Y )'), st([hp, mg], 'jca', '( %s e. RR+ /\\ %s e. NN0 )' % (h, MG_)), st([st([sr, tr], 'jca', '( S e. RR /\\ T e. RR )'), tmh], 'jca', '( ( S e. RR /\\ T e. RR ) /\\ T <_ ( S + %s ) )' % MH)], '3jca',
            '( ( Y e. RR /\\ 1 <_ Y ) /\\ ( %s e. RR+ /\\ %s e. NN0 ) /\\ ( ( S e. RR /\\ T e. RR ) /\\ T <_ ( S + %s ) ) )' % (h, MG_, MH))
    DK = '( Q x. ( N ^c ( %s x. ( 1 - %s ) ) ) )' % (F92, SKt)
    h2 = w.s([w.s([w.s([], 'simpl', '( %s -> ph )' % Ck), w.s([kn, skT], 'jca', '( %s -> ( k e. NN0 /\\ %s <_ T ) )' % (Ck, SKt))], 'jca', '( %s -> ( ph /\\ ( k e. NN0 /\\ %s <_ T ) ) )' % (Ck, SKt)), '2'], 'syl',
             '( %s -> %s <_ %s )' % (Ck, WS(SKt, X3), DK))
    omk = w.s([w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % Ck), skr], 'resubcld', '( %s -> ( 1 - %s ) e. RR )' % (Ck, SKt))
    nk = w.s([Lk(nr), Lk(st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')), w.s([w.s([num.real(w, F92)], 'a1i', '( %s -> %s e. RR )' % (Ck, F92)), omk], 'remulcld', '( %s -> ( %s x. ( 1 - %s ) ) e. RR )' % (Ck, F92, SKt))], 'recxpcld',
             '( %s -> ( N ^c ( %s x. ( 1 - %s ) ) ) e. RR )' % (Ck, F92, SKt))
    dkr = w.s([Lk(qr), nk], 'remulcld', '( %s -> %s e. RR )' % (Ck, DK))
    g6 = w.s([dkr, h2], 'jca', '( %s -> ( %s e. RR /\\ %s <_ %s ) )' % (Ck, DK, WS(SKt, X3), DK))
    YK = '( Y ^c ( S + ( ( k + 1 ) x. %s ) ) )' % h
    GS = 'sum_ k e. %s ( %s x. %s )' % (FZ, YK, DK)
    gr = ap_(w, C0, [DBfin, g2, g3, g4, g5, g6], 't21grid', '%s <_ %s' % (ZS(X3, 'Y', 'S', 'T'), GS))
    # rearrange and the geometric sum
    NK = '( N ^c ( %s x. ( 1 - %s ) ) )' % (F92, SKt)
    y0 = lin.linarith(w, C0, [y1], '0 <_ Y', leaves={'Y': yr})
    ykr = w.s([Lk(yr), Lk(y0), w.s([Lk(sr), w.s([ap_(w, Ck, [kr], 'peano2re', '( k + 1 ) e. RR'), Lk(hr)], 'remulcld', '( %s -> ( ( k + 1 ) x. %s ) e. RR )' % (Ck, h))], 'readdcld', '( %s -> ( S + ( ( k + 1 ) x. %s ) ) e. RR )' % (Ck, h))], 'recxpcld',
              '( %s -> %s e. RR )' % (Ck, YK))
    mm = w.s([w.s([ykr], 'recnd', '( %s -> %s e. CC )' % (Ck, YK)), Lk(st([qr], 'recnd', 'Q e. CC')), w.s([nk], 'recnd', '( %s -> %s e. CC )' % (Ck, NK))], 'mul12d', '( %s -> ( %s x. %s ) = ( Q x. ( %s x. %s ) ) )' % (Ck, YK, DK, YK, NK))
    GS2 = 'sum_ k e. %s ( Q x. ( %s x. %s ) )' % (FZ, YK, NK)
    e1 = st([mm], 'sumeq2dv', '%s = %s' % (GS, GS2))
    fz = st([w.s([], 'fzofi', '%s e. Fin' % FZ)], 'a1i', '%s e. Fin' % FZ)
    GN = 'sum_ k e. %s ( %s x. %s )' % (FZ, YK, NK)
    e2 = st([fz, st([qr], 'recnd', 'Q e. CC'), w.s([w.s([ykr, nk], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Ck, YK, NK))], 'recnd', '( %s -> ( %s x. %s ) e. CC )' % (Ck, YK, NK))], 'fsummulc2', '( Q x. %s ) = %s' % (GN, GS2))
    geo = ap_(w, C0, [xr, xe, yr, y1, yx, nr, n1, d92, sr, tr, sT, t1], 't21ggeo', '%s <_ ( ( ; 6 4 x. Y ) x. %s )' % (GN, EXPT))
    gnr = st([fz, w.s([ykr, nk], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Ck, YK, NK))], 'fsumrecl', '%s e. RR' % GN)
    er_ = st([st([xp, st([st([num.real(w, '-u %s' % F9200)], 'a1i', '-u %s e. RR' % F9200), st([one, tr], 'resubcld', '( 1 - T ) e. RR')], 'remulcld', '( -u %s x. ( 1 - T ) ) e. RR' % F9200)], 'rpcxpcld', '%s e. RR+' % EXPT)], 'rpred', '%s e. RR' % EXPT)
    rhsr = st([st([st([num.real(w, '; 6 4')], 'a1i', '; 6 4 e. RR'), yr], 'remulcld', '( ; 6 4 x. Y ) e. RR'), er_], 'remulcld', '( ( ; 6 4 x. Y ) x. %s ) e. RR' % EXPT)
    qg = st([gnr, rhsr, qr, q0, geo], 'lemul2ad', '( Q x. %s ) <_ ( Q x. ( ( ; 6 4 x. Y ) x. %s ) )' % (GN, EXPT))
    gse = st([e1, st([e2], 'eqcomd', '%s = ( Q x. %s )' % (GS2, GN))], 'eqtrd', '%s = ( Q x. %s )' % (GS, GN))
    gs2 = st([gse, qg], 'eqbrtrd', '%s <_ ( Q x. ( ( ; 6 4 x. Y ) x. %s ) )' % (GS, EXPT))
    gsr = st([gse, st([qr, gnr], 'remulcld', '( Q x. %s ) e. RR' % GN)], 'eqeltrd', '%s e. RR' % GS)
    yre = w.s([L_(yr, C2), L_(y0, C2), re], 'recxpcld', '( %s -> ( Y ^c ( Re ` q ) ) e. RR )' % C2)
    body = w.s([wr, yre], 'remulcld', '( %s -> ( %s x. ( Y ^c ( Re ` q ) ) ) e. RR )' % (C2, WT()))
    inner = w.s([g2, body], 'fsumrecl', '( %s -> sum_ q e. %s ( %s x. ( Y ^c ( Re ` q ) ) ) e. RR )' % (C1, AA, WT()))
    zsr = st([DBfin, inner], 'fsumrecl', '%s e. RR' % ZS(X3, 'Y', 'S', 'T'))
    fin = st([zsr, gsr, st([qr, rhsr], 'remulcld', '( Q x. ( ( ; 6 4 x. Y ) x. %s ) ) e. RR' % EXPT), gr, gs2], 'letrd', '%s <_ ( Q x. ( ( ; 6 4 x. Y ) x. %s ) )' % (ZS(X3, 'Y', 'S', 'T'), EXPT))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21gz']))
    return run(w)


if __name__ == '__main__':
    gen_gz()
