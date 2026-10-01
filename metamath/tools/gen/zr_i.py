"""Sortie ZR, REP: zrscale (two_le_scale, log_scale_pos), zridx (idx_bounds, idx_le_Qpar)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of


def scale_facts(w, A, nn_, tr, t0):
    """( A -> 2 <_ N ( T + 2 ) ), ( A -> LD e. RR ), ( A -> 0 < LD ), ( A -> N ( T + 2 ) e. RR )"""
    c = Ctx(w, A)
    D = '( N x. ( T + 2 ) )'
    nr = c([nn_], 'nnred', 'N e. RR')
    n1 = c([nn_], 'nnge1d', '1 <_ N')
    t2 = c([tr, numst8(w, A, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')
    dr = c([nr, t2], 'remulcld', '%s e. RR' % D)
    h = c([nr, tr, lin8(w, A, [n1], '0 <_ N', {'N': nr}), t0], 'mulge0d', '0 <_ ( N x. T )')
    d2 = lin8(w, A, [n1, h], '2 <_ %s' % D, {'N': nr, 'T': tr}, products=True)
    lp = c([c([dr, lin8(w, A, [d2], '1 < %s' % D, {D: dr})], 'rplogcld', '%s e. RR+' % LD)], 'rpgt0d', '0 < %s' % LD)
    lr = c([c([dr, lin8(w, A, [d2], '1 < %s' % D, {D: dr})], 'rplogcld', '%s e. RR+' % LD)], 'rpred', '%s e. RR' % LD)
    return d2, lr, lp, dr


def gen_scale():
    w = W('zrscale', 'Lean ` two_le_scale ` , ` log_scale_pos ` : ` 2 <_ N ( T + 2 ) ` and ` 0 < log ( N ( T + 2 ) ) ` for ` T >_ 0 ` .')
    A0 = ante_of(S['zrscale'])[0]
    c = Ctx(w, A0)
    d2, lr, lp, dr = scale_facts(w, A0, c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T'))
    w.qed([c([d2, lp], 'jca', ante_of(S['zrscale'])[1])], 'idi', S['zrscale'])
    return run8(w)


def gen_idx():
    w = W('zridx', 'Lean ` idx_bounds ` , ` idx_le_Qpar ` : the cell index ` |_ ( ( Im Z + T ) log ( N ( T + 2 ) ) ) ` of a point of the box is in ` NN0 ` , at most ` Qpar ` , and within ` 1 ` of its argument.')
    A0 = ante_of(S['zridx'])[0]
    c = Ctx(w, A0)
    nn_, tr, t0, zc, zi = c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T'), c.g('Z e. CC'), c.g('( abs ` ( Im ` Z ) ) <_ T')
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    ir = c([zc], 'imcld', '( Im ` Z ) e. RR')
    ab = c([zi, c([ir, tr], 'absled', '( ( abs ` ( Im ` Z ) ) <_ T <-> ( -u T <_ ( Im ` Z ) /\\ ( Im ` Z ) <_ T ) )')], 'mpbid', '( -u T <_ ( Im ` Z ) /\\ ( Im ` Z ) <_ T )')
    a1, a2 = c([ab], 'simpld', '-u T <_ ( Im ` Z )'), c([ab], 'simprd', '( Im ` Z ) <_ T')
    ARG = '( ( ( Im ` Z ) + T ) x. %s )' % LD
    it = c([ir, tr], 'readdcld', '( ( Im ` Z ) + T ) e. RR')
    argr = c([it, lr], 'remulcld', '%s e. RR' % ARG)
    arg0 = c([it, lr, lin8(w, A0, [a1], '0 <_ ( ( Im ` Z ) + T )', {'( Im ` Z )': ir, 'T': tr}), c([lp], 'ltled', '0 <_ %s' % LD)], 'mulge0d', '0 <_ %s' % ARG)
    nn0 = c([argr, arg0, w.inst('flge0nn0')], 'syl2anc', '%s e. NN0' % IDX('Z'))
    fl = c([argr, w.inst('fllelt')], 'syl', '( %s <_ %s /\\ %s < ( %s + 1 ) )' % (IDX('Z'), ARG, ARG, IDX('Z')))
    Q2 = '( ( 2 x. T ) x. %s )' % LD
    q2r = c([c([numst8(w, A0, '2', 'RR'), tr], 'remulcld', '( 2 x. T ) e. RR'), lr], 'remulcld', '%s e. RR' % Q2)
    hq = c([c([tr, ir], 'resubcld', '( T - ( Im ` Z ) ) e. RR'), lr, lin8(w, A0, [a2], '0 <_ ( T - ( Im ` Z ) )', {'( Im ` Z )': ir, 'T': tr}), c([lp], 'ltled', '0 <_ %s' % LD)],
           'mulge0d', '0 <_ ( ( T - ( Im ` Z ) ) x. %s )' % LD)
    le = lin8(w, A0, [hq], '%s <_ %s' % (ARG, Q2), {'( Im ` Z )': ir, 'T': tr, LD: lr}, products=True)
    fw = c([argr, q2r, le, w.inst('flwordi')], 'syl3anc', '%s <_ %s' % (IDX('Z'), QP))
    fin = c([c([nn0, fw], 'jca', '( %s e. NN0 /\\ %s <_ %s )' % (IDX('Z'), IDX('Z'), QP)), fl], 'jca', ante_of(S['zridx'])[1])
    w.qed([fin], 'idi', S['zridx'])
    return run8(w)


GENS = {'zrscale': gen_scale, 'zridx': gen_idx}


def gen_sdz():
    from zr_f import e12, ne0_by_re
    from ef4_g import elrab_unpack
    w = W('zrsdz', 'Lean ` sum_ord_zeta_smallDisk_le ` : the zeta zeros of the square within ` W ` of ` 1 + i T ` , ` 0 < W <_ 1 / 20 ` , have mass ` <_ 12 + 4 K W log ( abs T + 2 ) ` ( ~ zrlanx , ~ redivge , ~ lvmabs , ~ vmsharp ).')
    A0 = ante_of(S['zrsdz'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); wp = c.g('W e. RR+'); w20 = c.g('W <_ ( 1 / ; 2 0 )')
    wr = c([wp], 'rpred', 'W e. RR'); wc = c([wr], 'recnd', 'W e. CC'); tc = c([tr], 'recnd', 'T e. CC')
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    lx = c([c([tr, c([wp, w20], 'jca', W20)], 'jca', '( T e. RR /\\ %s )' % W20), w.inst('zrlanx')], 'syl', ante_of(S['zrlanx'])[1])
    XS = XSE
    RDS = '( Re ` %s )' % DL(SW)
    lx1 = c([lx], 'simpld', '%s <_ ( ( ( %s x. %s ) + ( ; 1 0 + %s ) ) - %s )' % (RDS, KL, LT2('T'), WTT, XS))
    lx0 = c([lx], 'simprd', '0 <_ %s' % XS)
    # - Re D <_ abs D <_ sum Lam k^-(1+W) <_ (5/4)/W + 5
    ow = c([c([], '1red', '1 e. RR'), wr], 'readdcld', '( 1 + W ) e. RR')
    swc = c([c([ow], 'recnd', '( 1 + W ) e. CC'), c([ic, tc], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SW)
    sre = c([ow, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + W )' % SW)
    s1 = lin8(w, A0, [sre, c([wp], 'rpgt0d', '0 < W')], '1 < ( Re ` %s )' % SW, {'( Re ` %s )' % SW: c([swc], 'recld', '( Re ` %s ) e. RR' % SW), 'W': wr})
    from ef56lib import DLVZ
    lva = c([c([nx1(w, A0), c([swc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (SW, SW))], 'jca', '( ( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) ) /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (U1, SW, SW)),
             w.inst('lvmabs')], 'syl', '( abs ` %s ) <_ sum_ k e. NN ( ( Lam ` k ) x. ( k ^c -u ( Re ` %s ) ) )' % (DLVZ(SW), SW))
    # DLVZ ( SW ) = DL ( SW )
    Ak = '( %s /\\ k e. NN )' % A0
    ck = Ctx(w, Ak)
    kn = ck([], 'simpr', 'k e. NN')
    CK = '( %s ` ( ( ZRHom ` ( Z/nZ ` 1 ) ) ` k ) )' % U1
    x1 = ck([ck([lift(w, nx1(w, A0), Ak)], 'simprd', '%s e. ( Base ` ( DChr ` 1 ) )' % U1), ck([kn], 'nnzd', 'k e. ZZ'), w.inst('zc1x1')], 'syl2anc', '%s = 1' % CK)
    lk = ck([ck([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC')
    t1 = ck([ck([x1], 'oveq1d', '( %s x. ( Lam ` k ) ) = ( 1 x. ( Lam ` k ) )' % CK), ck([lk], 'mullidd', '( 1 x. ( Lam ` k ) ) = ( Lam ` k )')], 'eqtrd', '( %s x. ( Lam ` k ) ) = ( Lam ` k )' % CK)
    t2 = ck([t1], 'oveq1d', '( ( %s x. ( Lam ` k ) ) x. ( k ^c -u %s ) ) = ( ( Lam ` k ) x. ( k ^c -u %s ) )' % (CK, SW, SW))
    dv = c([t2], 'sumeq2dv', '%s = %s' % (DLVZ(SW), DL(SW)))
    t3 = ck([ck([ck([lift(w, sre, Ak)], 'negeqd', '-u ( Re ` %s ) = -u ( 1 + W )' % SW)], 'oveq2d', '( k ^c -u ( Re ` %s ) ) = ( k ^c -u ( 1 + W ) )' % SW)], 'oveq2d',
            '( ( Lam ` k ) x. ( k ^c -u ( Re ` %s ) ) ) = ( ( Lam ` k ) x. ( k ^c -u ( 1 + W ) ) )' % SW)
    sv = c([t3], 'sumeq2dv', 'sum_ k e. NN ( ( Lam ` k ) x. ( k ^c -u ( Re ` %s ) ) ) = %s' % (SW, DL('( 1 + W )')))
    vs = c([c([wp, lin8(w, A0, [w20], 'W <_ 1', {'W': wr})], 'jca', '( W e. RR+ /\\ W <_ 1 )'), w.inst('vmsharp')], 'syl', '%s <_ ( ( ( 5 / 4 ) / W ) + 5 )' % DL('( 1 + W )'))
    from zr_g import dl_cc
    dsc = dl_cc(w, A0, SW, swc, s1)
    adl = c([dv], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (DLVZ(SW), DL(SW)))
    ngr = c([c([dsc], 'negcld', '-u %s e. CC' % DL(SW))], 'releabsd', '( Re ` -u %s ) <_ ( abs ` -u %s )' % (DL(SW), DL(SW)))
    rng = c([dsc], 'renegd', '( Re ` -u %s ) = -u %s' % (DL(SW), RDS))
    ang = c([dsc], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (DL(SW), DL(SW)))
    # W / ( W^2 + T^2 ) <_ 1 / W
    IW = '( 1 / W )'
    w2p = c([c([wr], 'resqcld', '( W ^ 2 ) e. RR'), c([wr, c([wp], 'rpne0d', 'W =/= 0')], 'sqgt0d', '0 < ( W ^ 2 )')], 'elrpd', '( W ^ 2 ) e. RR+')
    DEN = '( ( W ^ 2 ) + ( T ^ 2 ) )'
    denp = c([c([c([wr], 'resqcld', '( W ^ 2 ) e. RR'), c([tr], 'resqcld', '( T ^ 2 ) e. RR')], 'readdcld', '%s e. RR' % DEN),
              lin8(w, A0, [c([wr, c([wp], 'rpne0d', 'W =/= 0')], 'sqgt0d', '0 < ( W ^ 2 )'), c([tr], 'sqge0d', '0 <_ ( T ^ 2 )')], '0 < %s' % DEN,
                   {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( T ^ 2 )': c([tr], 'resqcld', '( T ^ 2 ) e. RR')})], 'elrpd', '%s e. RR+' % DEN)
    wt1 = c([w2p, denp, wr, c([wp], 'rpge0d', '0 <_ W'), lin8(w, A0, [c([tr], 'sqge0d', '0 <_ ( T ^ 2 )')], '( W ^ 2 ) <_ %s' % DEN, {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( T ^ 2 )': c([tr], 'resqcld', '( T ^ 2 ) e. RR')})],
            'lediv2ad', '%s <_ ( W / ( W ^ 2 ) )' % WTT)
    w0 = c([wp], 'rpne0d', 'W =/= 0')
    ww = c([c([c([wc], 'sqvald', '( W ^ 2 ) = ( W x. W )')], 'oveq2d', '( W / ( W ^ 2 ) ) = ( W / ( W x. W ) )'),
            c([c([c([wc], 'mullidd', '( 1 x. W ) = W')], 'eqcomd', 'W = ( 1 x. W )')], 'oveq1d', '( W / ( W x. W ) ) = ( ( 1 x. W ) / ( W x. W ) )')], 'eqtrd', '( W / ( W ^ 2 ) ) = ( ( 1 x. W ) / ( W x. W ) )')
    ww2 = c([ww, c([c([], '1cnd', '1 e. CC'), wc, wc, w0, w0], 'divcan5rd', '( ( 1 x. W ) / ( W x. W ) ) = ( 1 / W )')], 'eqtrd', '( W / ( W ^ 2 ) ) = ( 1 / W )')
    wt2 = c([wt1, ww2], 'breqtrd', '%s <_ %s' % (WTT, IW))
    iwr = c([c([], '1red', '1 e. RR'), wr, w0], 'redivcld', '%s e. RR' % IW)
    iww = c([c([], '1cnd', '1 e. CC'), wc, w0], 'divcan1d', '( %s x. W ) = 1' % IW)
    Q0 = '( ( 5 / 4 ) / W )'
    wq0 = c([numst8(w, A0, '( 5 / 4 )', 'CC'), wc, w0], 'divcan2d', '( W x. %s ) = ( 5 / 4 )' % Q0)
    q0r = c([numst8(w, A0, '( 5 / 4 )', 'RR'), wr, w0], 'redivcld', '%s e. RR' % Q0)
    # the disc terms
    DSK = DISK('T', 'W')
    fz = c([tr, w.inst('etazc')], 'syl', tsub(ante_of(stmt('etazc'))[1], {}))
    zfin = c([fz], 'simp1d', '%s e. Fin' % ZSE('T'))
    dss = c.a1(w.s([], 'ssrab2', '%s C_ %s' % (DSK, ZSE('T'))), '%s C_ %s' % (DSK, ZSE('T')))
    dfin = c([zfin, dss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % DSK)
    Aq = '( %s /\\ q e. %s )' % (A0, ZSE('T'))
    cq = Ctx(w, Aq)
    qz = cq([], 'simpr', 'q e. %s' % ZSE('T'))
    zs = cq([cq([lift(w, tr, Aq), qz], 'jca', '( T e. RR /\\ q e. %s )' % ZSE('T')), w.inst('zrzs')], 'syl', tsub(ante_of(S['zrzs'])[1], {'Q': 'q'}))
    qh = cq([cq([zs], 'simp1d', '( q e. %s /\\ ( %s ` q ) = 0 )' % (HP0, ETA))], 'simpld', 'q e. %s' % HP0)
    rq1 = cq([cq([zs], 'simp2d', '( ( 3 / 8 ) <_ ( Re ` q ) /\\ ( Re ` q ) <_ 1 )')], 'simprd', '( Re ` q ) <_ 1')
    qc = cq([cq([qh, cq([cq([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl', '( q e. %s <-> ( q e. CC /\\ 0 < ( Re ` q ) ) )' % HP0)], 'mpbid', '( q e. CC /\\ 0 < ( Re ` q ) )')], 'simpld', 'q e. CC')
    OE = '( %s holord q )' % E1
    od = cq([cq([cq([lift(w, hol_e1(w, A0), Aq), lift(w, e12(w, A0), Aq)], 'jca', '( %s /\\ ( %s ` 2 ) =/= 0 )' % (HOLF(E1, HP0), E1)), qh], 'jca',
                 '( ( %s /\\ ( %s ` 2 ) =/= 0 ) /\\ q e. %s )' % (HOLF(E1, HP0), E1, HP0)), w.inst('zrord')], 'syl', tsub(ante_of(S['zrord'])[1], {'F': E1, 'P': 'q'}))
    oe = cq([od], 'simpld', '%s e. NN0' % OE)
    oer = cq([oe], 'nn0red', '%s e. RR' % OE); oe0 = cq([oe], 'nn0ge0d', '0 <_ %s' % OE)
    Zq = '( %s - q )' % SW
    zqc = cq([lift(w, swc, Aq), qc], 'subcld', '%s e. CC' % Zq)
    rz = cq([lift(w, swc, Aq), qc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` q ) )' % (Zq, SW))
    RZ = '( Re ` %s )' % Zq
    lvq = {RZ: cq([zqc], 'recld', '%s e. RR' % RZ), '( Re ` %s )' % SW: lift(w, c([swc], 'recld', '( Re ` %s ) e. RR' % SW), Aq), '( Re ` q )': cq([qc], 'recld', '( Re ` q ) e. RR'), 'W': lift(w, wr, Aq)}
    rzw = lin8(w, Aq, [rz, lift(w, sre, Aq), rq1], 'W <_ %s' % RZ, lvq)
    rzp = lin8(w, Aq, [rzw, lift(w, c([wp], 'rpgt0d', '0 < W'), Aq)], '0 < %s' % RZ, lvq)
    zqn = ne0_by_re(w, Aq, zqc, cq([rzp], 'gt0ne0d', '%s =/= 0' % RZ), Zq)
    TQ = '( Re ` ( %s / %s ) )' % (OE, Zq)
    tqr = cq([cq([cq([oer], 'recnd', '%s e. CC' % OE), zqc, zqn], 'divcld', '( %s / %s ) e. CC' % (OE, Zq))], 'recld', '%s e. RR' % TQ)
    tq0 = cq([cq([cq([oer, oe0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (OE, OE)), cq([zqc, rzp], 'jca', '( %s e. CC /\\ 0 < %s )' % (Zq, RZ))], 'jca',
                  '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( %s e. CC /\\ 0 < %s ) )' % (OE, OE, Zq, RZ)), w.inst('redivnn')], 'syl', '0 <_ %s' % TQ)
    # on the disc: OE / ( 4 W ) <_ TQ
    Ad = '( %s /\\ q e. %s )' % (A0, DSK)
    cd = Ctx(w, Ad)
    qd = cd([], 'simpr', 'q e. %s' % DSK)
    qzs, qdb, _ = elrab_unpack(w, Ad, 'p', ZSE('T'), '( abs ` ( p - ( 1 + ( _i x. T ) ) ) ) <_ W', 'q', qd)
    bridge = cd([cd.g(A0), qzs], 'jca', Aq)
    rl = lambda st: w.s([bridge, st], 'syl', '( %s -> %s )' % (Ad, strip_ante(formula_of(w, st), Aq)))
    cl = Closure(w, Ad, {'W': ('CC', lift(w, wc, Ad)), 'T': ('CC', lift(w, tc, Ad)), '_i': ('CC', lift(w, ic, Ad)), 'q': ('CC', rl(qc))})
    for a_ in ('W', 'T', '_i', 'q'):
        cl.atom(a_)
    OT = '( ( 1 + ( _i x. T ) ) - q )'
    zsp = ringeq(w, Ad, Zq, '( W + %s )' % OT, cl)
    otc = cl.mem(OT, 'CC')
    az = cd([cd([zsp], 'fveq2d', '( abs ` %s ) = ( abs ` ( W + %s ) )' % (Zq, OT)), cd([lift(w, wc, Ad), otc], 'abstrid', '( abs ` ( W + %s ) ) <_ ( ( abs ` W ) + ( abs ` %s ) )' % (OT, OT))],
            'eqbrtrd', '( abs ` %s ) <_ ( ( abs ` W ) + ( abs ` %s ) )' % (Zq, OT))
    aw = cd([lift(w, wr, Ad), lift(w, c([wp], 'rpge0d', '0 <_ W'), Ad)], 'absidd', '( abs ` W ) = W')
    ao = cd([cl.mem('( 1 + ( _i x. T ) )', 'CC'), rl(qc)], 'abssubd', '( abs ` %s ) = ( abs ` ( q - ( 1 + ( _i x. T ) ) ) )' % OT)
    AZ = '( abs ` %s )' % Zq
    lvd = {AZ: cd([rl(zqc)], 'abscld', '%s e. RR' % AZ), '( abs ` W )': cd([lift(w, wc, Ad)], 'abscld', '( abs ` W ) e. RR'), '( abs ` %s )' % OT: cd([otc], 'abscld', '( abs ` %s ) e. RR' % OT),
           '( abs ` ( q - ( 1 + ( _i x. T ) ) ) )': cd([cd([rl(qc), cl.mem('( 1 + ( _i x. T ) )', 'CC')], 'subcld', '( q - ( 1 + ( _i x. T ) ) ) e. CC')], 'abscld', '( abs ` ( q - ( 1 + ( _i x. T ) ) ) ) e. RR'),
           'W': lift(w, wr, Ad)}
    az2 = lin8(w, Ad, [az, aw, ao, qdb], '%s <_ ( 2 x. W )' % AZ, lvd)
    rg = cd([cd([cd([rl(oer), rl(oe0)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (OE, OE)), cd([lift(w, wp, Ad), rl(zqc)], 'jca', '( W e. RR+ /\\ %s e. CC )' % Zq), cd([rl(rzw), az2], 'jca', '( W <_ %s /\\ %s <_ ( 2 x. W ) )' % (RZ, AZ))],
                '3jca', '( ( %s e. RR /\\ 0 <_ %s ) /\\ ( W e. RR+ /\\ %s e. CC ) /\\ ( W <_ %s /\\ %s <_ ( 2 x. W ) ) )' % (OE, OE, Zq, RZ, AZ)), w.inst('redivge')], 'syl', '( %s / ( 4 x. W ) ) <_ %s' % (OE, TQ))
    W4 = '( 4 x. W )'
    w4c = c([numst8(w, A0, '4', 'CC'), wc], 'mulcld', '%s e. CC' % W4)
    w4n = c([numst8(w, A0, '4', 'CC'), wc, c([lin8(w, A0, [], '0 < 4', {})], 'gt0ne0d', '4 =/= 0'), w0], 'mulne0d', '%s =/= 0' % W4)
    SO = 'sum_ q e. %s %s' % (DSK, OE)
    fd = c([dfin, w4c, cd([rl(oer)], 'recnd', '%s e. CC' % OE), w4n], 'fsumdivc', '( %s / %s ) = sum_ q e. %s ( %s / %s )' % (SO, W4, DSK, OE, W4))
    s1_ = c([dfin, cd([rl(oer), lift(w, c([numst8(w, A0, '4', 'RR'), wr], 'remulcld', '%s e. RR' % W4), Ad), lift(w, w4n, Ad)], 'redivcld', '( %s / %s ) e. RR' % (OE, W4)), rl(tqr), rg], 'fsumle',
             'sum_ q e. %s ( %s / %s ) <_ sum_ q e. %s %s' % (DSK, OE, W4, DSK, TQ))
    s2_ = c([zfin, tqr, tq0, dss], 'fsumless', 'sum_ q e. %s %s <_ %s' % (DSK, TQ, XS))
    SQ4 = '( %s / %s )' % (SO, W4)
    S1 = 'sum_ q e. %s ( %s / %s )' % (DSK, OE, W4)
    S2 = 'sum_ q e. %s %s' % (DSK, TQ)
    sor = c([dfin, rl(oer)], 'fsumrecl', '%s e. RR' % SO)
    w4r = c([numst8(w, A0, '4', 'RR'), wr], 'remulcld', '%s e. RR' % W4)
    sq4r = c([sor, w4r, w4n], 'redivcld', '%s e. RR' % SQ4)
    AD, ADV, AND_ = '( abs ` %s )' % DL(SW), '( abs ` %s )' % DLVZ(SW), '( abs ` -u %s )' % DL(SW)
    RND = '( Re ` -u %s )' % DL(SW)
    D1W = DL('( 1 + W )')
    from zr_g import ltv
    ltr = ltv(w, A0, tc)
    lva2 = c([lva, sv], 'breqtrd', '%s <_ %s' % (ADV, D1W))
    # DL ( 1 + W ) is real
    k1 = ck([ck([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR'), ck([ck([ck([kn], 'nnrpd', 'k e. RR+'), ck([lift(w, ow, Ak)], 'renegcld', '-u ( 1 + W ) e. RR')], 'rpcxpcld', '( k ^c -u ( 1 + W ) ) e. RR+')], 'rpred', '( k ^c -u ( 1 + W ) ) e. RR')],
            'remulcld', '( ( Lam ` k ) x. ( k ^c -u ( 1 + W ) ) ) e. RR')
    from zr_b import mv, VMF
    fk1 = mv(w, Ak, 'n', 'NN', '( ( Lam ` n ) x. ( n ^c -u ( 1 + W ) ) )', 'k', kn, ck([k1], 'recnd', '( ( Lam ` k ) x. ( k ^c -u ( 1 + W ) ) ) e. CC'))
    owc = c([ow], 'recnd', '( 1 + W ) e. CC')
    ow1 = c([lin8(w, A0, [c([wp], 'rpgt0d', '0 < W')], '1 < ( 1 + W )', {'W': wr}), c([c([ow], 'rered', '( Re ` ( 1 + W ) ) = ( 1 + W )')], 'eqcomd', '( 1 + W ) = ( Re ` ( 1 + W ) )')], 'breqtrd', '1 < ( Re ` ( 1 + W ) )')
    cv1 = c([c([owc, ow1], 'jca', '( ( 1 + W ) e. CC /\\ 1 < ( Re ` ( 1 + W ) ) )'), w.inst('zrvmc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % VMF('( 1 + W )'))
    d1r = c([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), c([], '1zzd', '1 e. ZZ'), fk1, k1, cv1], 'isumrecl', '%s e. RR' % D1W)
    DEN = '( ( W ^ 2 ) + ( T ^ 2 ) )'
    wtr = c([wr, c([denp], 'rpred', '%s e. RR' % DEN), c([denp], 'rpne0d', '%s =/= 0' % DEN)], 'redivcld', '%s e. RR' % WTT)
    dlvc = c([dv, dsc], 'eqeltrd', '%s e. CC' % DLVZ(SW))
    ndc = c([dsc], 'negcld', '-u %s e. CC' % DL(SW))
    lv = {SQ4: sq4r, S1: c([dfin, cd([rl(oer), lift(w, w4r, Ad), lift(w, w4n, Ad)], 'redivcld', '( %s / %s ) e. RR' % (OE, W4))], 'fsumrecl', '%s e. RR' % S1),
          S2: c([dfin, rl(tqr)], 'fsumrecl', '%s e. RR' % S2), XS: c([zfin, tqr], 'fsumrecl', '%s e. RR' % XS), RDS: c([dsc], 'recld', '%s e. RR' % RDS),
          AD: c([dsc], 'abscld', '%s e. RR' % AD), ADV: c([dlvc], 'abscld', '%s e. RR' % ADV), AND_: c([ndc], 'abscld', '%s e. RR' % AND_), RND: c([ndc], 'recld', '%s e. RR' % RND),
          D1W: d1r, WTT: wtr, IW: iwr, Q0: q0r, LT2('T'): ltr}
    B_ = '( ( ( %s x. %s ) + ; 1 5 ) + ( %s + %s ) )' % (KL, LT2('T'), WTT, Q0)
    l1 = lin8(w, A0, [fd, s1_, s2_, lx1, rng, ngr, ang, adl, lva2, vs], '%s <_ %s' % (SQ4, B_), lv)
    br = Closure(w, A0, {LT2('T'): ('RR', ltr), WTT: ('RR', wtr), Q0: ('RR', q0r)})
    for a_ in (LT2('T'), WTT, Q0):
        br.atom(a_)
    bbr = br.mem(B_, 'RR')
    h1 = c([w4r, c([bbr, sq4r], 'resubcld', '( %s - %s ) e. RR' % (B_, SQ4)), lin8(w, A0, [c([wp], 'rpgt0d', '0 < W')], '0 <_ %s' % W4, {'W': wr}),
            lin8(w, A0, [l1], '0 <_ ( %s - %s )' % (B_, SQ4), lv)], 'mulge0d', '0 <_ ( %s x. ( %s - %s ) )' % (W4, B_, SQ4))
    h2 = c([wr, c([iwr, wtr], 'resubcld', '( %s - %s ) e. RR' % (IW, WTT)), c([wp], 'rpge0d', '0 <_ W'), lin8(w, A0, [wt2], '0 <_ ( %s - %s )' % (IW, WTT), lv)], 'mulge0d', '0 <_ ( W x. ( %s - %s ) )' % (IW, WTT))
    so = c([c([sor], 'recnd', '%s e. CC' % SO), w4c, w4n], 'divcan1d', '( %s x. %s ) = %s' % (SQ4, W4, SO))
    lvF = dict(lv); lvF[SO] = sor; lvF['W'] = wr
    fin = lin8(w, A0, [h1, h2, so, iww, wq0, w20], ante_of(S['zrsdz'])[1], lvF, products=True)
    w.qed([fin], 'idi', S['zrsdz'])
    return run8(w)


GENS['zrsdz'] = gen_sdz
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
