"""Sortie GF2, section G: the generic Gram identity (anchor + Dirichlet identity + contour shift):
2 pi i sum_n c_n W ( n ) - VLh ( GI , -99/100 ) = 2 pi i HF ( -u S ), c_n = n ^ -1 P ( n ) ^ 2 C ( n ) n ^ -S
(Lean Bgram_eq_main_add_rem before the frozen instance).
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_g.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L
import gf1lib as G1L
from gf1lib import tsub, proj, build, HOL
from mvlib import ringeq
import gf2_a as GA_
import gf2_s as GS
import gf2_d as GD

S_ = L.S
MULT = GD.MULT
PM = GD.PM
QF = '( b e. NN |-> ( ( %s ^ 2 ) x. ( C ` b ) ) )' % PM('b')
HQ = '( ( |_ ` R ) ^ 2 )'
QS = {'Q': QF, 'H': HQ}
TNQ = lambda n: tsub(GA_.TN(n), QS)
TNFQ = tsub(GA_.TNF, QS)
GAQ = tsub(GA_.GA, QS)
GH = '( %s /\\ %s )' % (GS.MSH, MULT)
S_['gf2gram'] = '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ ( ( %s x. sum_ n e. NN %s ) - %s ) = %s ) )' % (
    GH, TNFQ, GS.TPI, TNQ('n'), GS.VLh(GS.GI, GS.CLL), GS.RES)


def gf2gram():
    w = W('gf2gram', 'The Gram identity, generic in the windows and the character (Lean ` Bgram_eq_main_add_rem ` before the frozen instance): '
          'the anchor ~ gf2anchor with ` Q ( n ) = P ( n ) ^ 2 C ( n ) ` , the anchor integrand equals ` GI ` on ` Re w = 1 ` (~ gf2dir , the interface '
          '` DSER ` , ~ gf1g1v , ~ z6vleq ), and the shift ~ gf2shiftr .')
    a = GH; st = mkst(w, a)
    P_ = lambda x: proj(w, a, x)
    rr = P_('R e. RR'); r1 = P_('1 <_ R')
    r0 = lin.linarith(w, a, [r1], '0 <_ R', leaves={'R': rr})
    nv = P_('N e. NN')
    cf = P_('C : NN --> CC'); cbj = P_(GS.CBj)
    # the coefficient function Q
    fln = st([st([rr, r0], 'jca', '( R e. RR /\\ 0 <_ R )'), w.inst('flge0nn0')], 'syl', '( |_ ` R ) e. NN0')
    flr = st([fln], 'nn0red', '( |_ ` R ) e. RR'); fl0 = st([fln], 'nn0ge0d', '0 <_ ( |_ ` R )')
    hqr = st([flr], 'resqcld', '%s e. RR' % HQ)
    an = '( %s /\\ b e. NN )' % a; tn = mkst(w, an)
    nn_ = tn([], 'simpr', 'b e. NN')
    pab = lambda ctx, k, kn: mkst(w, ctx)([mkst(w, ctx)([lift(w, nv, ctx), mkst(w, ctx)([lift(w, rr, ctx), lift(w, r0, ctx)], 'jca', '( R e. RR /\\ 0 <_ R )')], 'jca',
                                                        '( N e. NN /\\ ( R e. RR /\\ 0 <_ R ) )'), kn, w.inst('z5pfunabs')], 'syl2anc', '( abs ` %s ) <_ ( |_ ` R )' % PM(k))
    pnc = tn([pab(an, 'b', nn_), w.inst('z6absle')], 'syl', '%s e. CC' % PM('b'))
    qnc = tn([tn([pnc], 'sqcld', '( %s ^ 2 ) e. CC' % PM('b')), tn([lift(w, cf, an), nn_], 'ffvelcdmd', '( C ` b ) e. CC')], 'mulcld', '( ( %s ^ 2 ) x. ( C ` b ) ) e. CC' % PM('b'))
    qff = st([qnc, w.s([], 'eqid', '%s = %s' % (QF, QF))], 'fmptd', '%s : NN --> CC' % QF)
    aj = '( %s /\\ m e. NN )' % a; tj = mkst(w, aj)
    jn = tj([], 'simpr', 'm e. NN')
    qjv, _ = mpv(w, aj, 'b', 'NN', '( ( %s ^ 2 ) x. ( C ` b ) )' % PM('b'), 'm', jn)
    pjb = pab(aj, 'm', jn)
    pjc = tj([pjb, w.inst('z6absle')], 'syl', '%s e. CC' % PM('m'))
    cjc = tj([lift(w, cf, aj), jn], 'ffvelcdmd', '( C ` m ) e. CC')
    rspj = w.s([w.s([w.s([], 'fveq2', '( j = m -> ( C ` j ) = ( C ` m ) )')], 'fveq2d', '( j = m -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` m ) ) )')], 'breq1d',
               '( j = m -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` m ) ) <_ 1 ) )')
    cjb = tj([rspj, lift(w, cbj, aj), jn], 'rspcdva', '( abs ` ( C ` m ) ) <_ 1')
    P2 = '( %s ^ 2 )' % PM('m')
    ap2 = tj([pjc, a1(w, aj, w.s([], '2nn0', '2 e. NN0'), '2 e. NN0')], 'absexpd', '( abs ` %s ) = ( ( abs ` %s ) ^ 2 )' % (P2, PM('m')))
    apr = tj([pjc], 'abscld', '( abs ` %s ) e. RR' % PM('m')); ap0 = tj([pjc], 'absge0d', '0 <_ ( abs ` %s )' % PM('m'))
    sqb = tj([pjb, tj([apr, lift(w, flr, aj), ap0, lift(w, fl0, aj)], 'le2sqd', '( ( abs ` %s ) <_ ( |_ ` R ) <-> ( ( abs ` %s ) ^ 2 ) <_ ( ( |_ ` R ) ^ 2 ) )' % (PM('m'), PM('m')))],
             'mpbid', '( ( abs ` %s ) ^ 2 ) <_ %s' % (PM('m'), HQ))
    p2b = tj([ap2, sqb], 'eqbrtrd', '( abs ` %s ) <_ %s' % (P2, HQ))
    p2c = tj([pjc], 'sqcld', '%s e. CC' % P2)
    QJ = '( %s x. ( C ` m ) )' % P2
    qb1 = tj([tj([p2c, cjc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( C ` m ) ) )' % (QJ, P2)),
              tj([tj([p2c], 'abscld', '( abs ` %s ) e. RR' % P2), lift(w, hqr, aj), tj([cjc], 'abscld', '( abs ` ( C ` m ) ) e. RR'), tj([], '1red', '1 e. RR'),
                  tj([p2c], 'absge0d', '0 <_ ( abs ` %s )' % P2), tj([cjc], 'absge0d', '0 <_ ( abs ` ( C ` m ) )'), p2b, cjb], 'lemul12ad',
                 '( ( abs ` %s ) x. ( abs ` ( C ` m ) ) ) <_ ( %s x. 1 )' % (P2, HQ))], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. 1 )' % (QJ, HQ))
    qb2 = tj([qb1, tj([tj([lift(w, hqr, aj)], 'recnd', '%s e. CC' % HQ)], 'mulridd', '( %s x. 1 ) = %s' % (HQ, HQ))], 'breqtrd', '( abs ` %s ) <_ %s' % (QJ, HQ))
    qb3 = tj([tj([qjv], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` %s )' % (QF, QJ)), qb2], 'eqbrtrd', '( abs ` ( %s ` m ) ) <_ %s' % (QF, HQ))
    qbk = st([qb3], 'ralrimiva', 'A. m e. NN ( abs ` ( %s ` m ) ) <_ %s' % (QF, HQ))
    ckj = w.s([w.s([w.s([], 'fveq2', '( m = j -> ( %s ` m ) = ( %s ` j ) )' % (QF, QF))], 'fveq2d', '( m = j -> ( abs ` ( %s ` m ) ) = ( abs ` ( %s ` j ) ) )' % (QF, QF))], 'breq1d',
              '( m = j -> ( ( abs ` ( %s ` m ) ) <_ %s <-> ( abs ` ( %s ` j ) ) <_ %s ) )' % (QF, HQ, QF, HQ))
    qball = st([qbk, w.s([ckj], 'cbvralvw', '( A. m e. NN ( abs ` ( %s ` m ) ) <_ %s <-> A. j e. NN ( abs ` ( %s ` j ) ) <_ %s )' % (QF, HQ, QF, HQ))], 'sylib',
               'A. j e. NN ( abs ` ( %s ` j ) ) <_ %s' % (QF, HQ))
    AHQ = tsub(GA_.AH, QS)
    ah = build(w, a, AHQ, {'A e. RR': P_('A e. RR'), 'B e. RR': P_('B e. RR'), '0 <_ A': P_('0 <_ A'), '0 <_ B': P_('0 <_ B'), 'L e. RR+': P_('L e. RR+'),
                           '%s : NN --> CC' % QF: qff, '%s e. RR' % HQ: hqr, 'A. j e. NN ( abs ` ( %s ` j ) ) <_ %s' % (QF, HQ): qball, 'S e. CC': P_('S e. CC'),
                           '0 <_ ( Re ` S )': P_('0 <_ ( Re ` S )')})
    anc = st([ah, w.inst('gf2anchor')], 'syl', tsub(split_imp(S_['gf2anchor'])[1], QS))
    # the line Re w = 1: GAQ = GI there
    au = '( %s /\\ u e. RR )' % a; tu = mkst(w, au)
    ur = tu([], 'simpr', 'u e. RR')
    V = '( 1 + ( _i x. u ) )'
    ic = a1(w, au, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    vc = tu([tu([], '1cnd', '1 e. CC'), tu([ic, tu([ur], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')], 'addcld', '%s e. CC' % V)
    rv = tu([tu([], '1red', '1 e. RR'), ur], 'crred', '( Re ` %s ) = 1' % V)
    rvr = tu([vc], 'recld', '( Re ` %s ) e. RR' % V)
    sc = lift(w, P_('S e. CC'), au); s0 = lift(w, P_('0 <_ ( Re ` S )'), au)
    rsr = tu([sc], 'recld', '( Re ` S ) e. RR')
    # v =/= 0 and v =/= -u S
    c2 = '( %s /\\ %s = 0 )' % (au, V); t2 = mkst(w, c2)
    rv0 = t2([t2([t2([], 'simpr', '%s = 0' % V)], 'fveq2d', '( Re ` %s ) = ( Re ` 0 )' % V), a1(w, c2, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')], 'eqtrd',
            '( Re ` %s ) = 0' % V)
    rn0 = tu([tu([rv, a1(w, au, w.s([], 'ax-1ne0', '1 =/= 0'), '1 =/= 0')], 'eqnetrd', '( Re ` %s ) =/= 0' % V)], 'neneqd', '-. ( Re ` %s ) = 0' % V)
    vn0 = tu([w.s([rv0, lift(w, rn0, c2)], 'pm2.65da', '( %s -> -. %s = 0 )' % (au, V))], 'neqned', '%s =/= 0' % V)
    c3 = '( %s /\\ %s = -u S )' % (au, V); t3 = mkst(w, c3)
    r3 = t3([t3([t3([], 'simpr', '%s = -u S' % V)], 'fveq2d', '( Re ` %s ) = ( Re ` -u S )' % V), t3([lift(w, sc, c3)], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')], 'eqtrd',
            '( Re ` %s ) = -u ( Re ` S )' % V)
    lt3 = lin.linarith(w, au, [rv, s0], '-u ( Re ` S ) < ( Re ` %s )' % V, leaves={'( Re ` %s )' % V: rvr, '( Re ` S )': rsr})
    rn3 = tu([tu([tu([lt3], 'ltned', '-u ( Re ` S ) =/= ( Re ` %s )' % V)], 'necomd', '( Re ` %s ) =/= -u ( Re ` S )' % V)], 'neneqd', '-. ( Re ` %s ) = -u ( Re ` S )' % V)
    vns = tu([w.s([r3, lift(w, rn3, c3)], 'pm2.65da', '( %s -> -. %s = -u S )' % (au, V))], 'neqned', '%s =/= -u S' % V)
    m1 = lin.linarith(w, au, [rv], '-u 1 < ( Re ` %s )' % V, leaves={'( Re ` %s )' % V: rvr})
    vdg = tu([tu([vc, tu([m1, vn0], 'jca', '( -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (V, V))], 'jca', '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ %s =/= 0 ) )' % (V, V, V)),
              w.inst('z6rdg')], 'syl', '%s e. ( CC \\ ( ZZ \\ NN ) )' % V)
    vh = tu([tu([vc, m1], 'jca', '( %s e. CC /\\ -u 1 < ( Re ` %s ) )' % (V, V)), tu([tu([tu([], '1red', '1 e. RR')], 'renegcld', '-u 1 e. RR'), w.inst('elhp2')], 'syl',
                                                                                   '( %s e. %s <-> ( %s e. CC /\\ -u 1 < ( Re ` %s ) ) )' % (V, GS.HPM1, V, V))], 'mpbird', '%s e. %s' % (V, GS.HPM1))
    vdi = tu([tu([vh, vns], 'jca', '( %s e. %s /\\ %s =/= -u S )' % (V, GS.HPM1, V)), a1(w, au, w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. %s /\\ %s =/= -u S ) )' % (V, GS.DI, V, GS.HPM1, V)),
                                                                                     '( %s e. %s <-> ( %s e. %s /\\ %s =/= -u S ) )' % (V, GS.DI, V, GS.HPM1, V))], 'mpbird', '%s e. %s' % (V, GS.DI))
    GABQ = lambda v: tsub(GA_.GAB(v), QS)
    gav, _ = mpv(w, au, 'w', '( CC \\ ( ZZ \\ NN ) )', GABQ('w'), V, vdg)
    W_ = '( ( 1 + S ) + %s )' % V
    c1_ = tu([tu([], '1cnd', '1 e. CC'), sc], 'addcld', '( 1 + S ) e. CC')
    wc = tu([c1_, vc], 'addcld', '%s e. CC' % W_)
    rw1 = tu([c1_, vc], 'readdd', '( Re ` %s ) = ( ( Re ` ( 1 + S ) ) + ( Re ` %s ) )' % (W_, V))
    rw2 = tu([tu([tu([], '1cnd', '1 e. CC'), sc], 'readdd', '( Re ` ( 1 + S ) ) = ( ( Re ` 1 ) + ( Re ` S ) )'),
              tu([a1(w, au, w.s([w.s([], '1re', '1 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')], 'oveq1d', '( ( Re ` 1 ) + ( Re ` S ) ) = ( 1 + ( Re ` S ) )')],
             'eqtrd', '( Re ` ( 1 + S ) ) = ( 1 + ( Re ` S ) )')
    rwe = tu([rw1, tu([rw2], 'oveq1d', '( ( Re ` ( 1 + S ) ) + ( Re ` %s ) ) = ( ( 1 + ( Re ` S ) ) + ( Re ` %s ) )' % (V, V))], 'eqtrd',
             '( Re ` %s ) = ( ( 1 + ( Re ` S ) ) + ( Re ` %s ) )' % (W_, V))
    rwr = tu([wc], 'recld', '( Re ` %s ) e. RR' % W_)
    LVW = {'( Re ` %s )' % V: rvr, '( Re ` S )': rsr, '( Re ` %s )' % W_: rwr}
    w1 = lin.linarith(w, au, [rwe, rv, s0], '1 < ( Re ` %s )' % W_, leaves=LVW)
    w0 = lin.linarith(w, au, [rwe, rv, s0], '0 < ( Re ` %s )' % W_, leaves=LVW)
    # the Dirichlet identity at W
    TGW = lambda n: tsub(GD.TGT(n), {'Z': W_})
    ZQ = lambda n: '( ( %s ` %s ) x. ( %s ^c -u %s ) )' % (QF, n, n, W_)
    idnm = w.s([], 'id', '( n = m -> n = m )')
    cst, _ = w.congr(ZQ('n'), {'n': 'm'}, 'n = m', {'n': idnm})
    cb1 = a1(w, au, w.s([cst], 'cbvsumv', 'sum_ n e. NN %s = sum_ m e. NN %s' % (ZQ('n'), ZQ('m'))), 'sum_ n e. NN %s = sum_ m e. NN %s' % (ZQ('n'), ZQ('m')))
    am = '( %s /\\ m e. NN )' % au; tm = mkst(w, am)
    mn = tm([], 'simpr', 'm e. NN')
    qmv, _ = mpv(w, am, 'b', 'NN', '( ( %s ^ 2 ) x. ( C ` b ) )' % PM('b'), 'm', mn)
    tqm = tm([qmv], 'oveq1d', '%s = %s' % (ZQ('m'), TGW('m')))
    se = tu([tqm], 'sumeq2dv', 'sum_ m e. NN %s = sum_ m e. NN %s' % (ZQ('m'), TGW('m')))
    DH = tsub(GD.DH, {'V': 'NN'})
    dh = build(w, au, DH, {'N e. NN': lift(w, nv, au), 'R e. RR': lift(w, rr, au), '0 <_ R': lift(w, r0, au), 'C : NN --> CC': lift(w, cf, au), MULT: lift(w, P_(MULT), au)})
    dir_ = tu([tu([dh, tu([lift(w, cbj, au), tu([wc, w1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (W_, W_))], 'jca', '( %s /\\ ( %s e. CC /\\ 1 < ( Re ` %s ) ) )' % (GS.CBj, W_, W_))],
                  'jca', tsub(GD.DIRH, {'Z': W_, 'V': 'NN'})), w.inst('gf2dir')], 'syl', tsub(split_imp(S_['gf2dir'])[1], {'Z': W_}))
    FT = '( n e. NN |-> %s )' % TGW('n')
    ftv, _ = mpv(w, am, 'n', 'NN', TGW('n'), 'm', mn)
    pmc = tm([tm([tm([lift(w, nv, am), tm([lift(w, rr, am), lift(w, r0, am)], 'jca', '( R e. RR /\\ 0 <_ R )')], 'jca', '( N e. NN /\\ ( R e. RR /\\ 0 <_ R ) )'), mn,
                  w.inst('z5pfunabs')], 'syl2anc', '( abs ` %s ) <_ ( |_ ` R )' % PM('m')), w.inst('z6absle')], 'syl', '%s e. CC' % PM('m'))
    tgc = tm([tm([tm([pmc], 'sqcld', '( %s ^ 2 ) e. CC' % PM('m')), tm([lift(w, cf, am), mn], 'ffvelcdmd', '( C ` m ) e. CC')], 'mulcld',
                 '( ( %s ^ 2 ) x. ( C ` m ) ) e. CC' % PM('m')), tm([tm([mn], 'nncnd', 'm e. CC'), tm([lift(w, wc, am)], 'negcld', '-u %s e. CC' % W_)], 'cxpcld',
                                                                  '( m ^c -u %s ) e. CC' % W_)], 'mulcld', '%s e. CC' % TGW('m'))
    MHW = tsub(GD.MHZ, {'Z': W_}); LSW = tsub(GD.LSZ, {'Z': W_})
    isc_ = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, au, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), ftv, tgc, dir_], 'isumclim',
               '( %s -> sum_ m e. NN %s = ( %s x. %s ) )' % (au, TGW('m'), MHW, LSW))
    sumv = tu([tu([cb1, se], 'eqtrd', 'sum_ n e. NN %s = sum_ m e. NN %s' % (ZQ('n'), TGW('m'))), isc_], 'eqtrd', 'sum_ n e. NN %s = ( %s x. %s )' % (ZQ('n'), MHW, LSW))
    # DSER at W
    DS_ = proj(w, au, GS.DSER)
    inner = lambda z: '( 1 < ( Re ` %s ) -> ( E ` %s ) = ( ( %s - 1 ) x. %s ) )' % (z, z, z, tsub(GS.LSs, {'s': z}))
    ids = w.s([], 'id', '( s = %s -> s = %s )' % (W_, W_))
    bst, bval = w.wcongr(inner('s'), {'s': W_}, 's = %s' % W_, {'s': ids})
    assert bval == inner(W_), bval
    whz = tu([tu([wc, w0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (W_, W_)), tu([tu([], '0red', '0 e. RR'), w.inst('elhp2')], 'syl',
                                                                                     '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (W_, GS.HPZ, W_, W_))], 'mpbird', '%s e. %s' % (W_, GS.HPZ))
    dsw = tu([w1, tu([bst, DS_, whz], 'rspcdva', inner(W_))], 'mpd', '( E ` %s ) = ( ( %s - 1 ) x. %s )' % (W_, W_, LSW))
    D = '( %s - 1 )' % W_
    uc = tu([ur], 'recnd', 'u e. CC')
    dq = ringeq(w, au, D, '( %s - -u S )' % V, Closure(w, au, {'S': sc, '_i': ic, 'u': uc}))
    dn0 = tu([dq, tu([vc, tu([sc], 'negcld', '-u S e. CC'), vns], 'subne0d', '( %s - -u S ) =/= 0' % V)], 'eqnetrd', '%s =/= 0' % D)
    dc = tu([wc, tu([], '1cnd', '1 e. CC')], 'subcld', '%s e. CC' % D)
    lsc = tu([tu([tu([lift(w, cf, au), lift(w, cbj, au)], 'jca', '( C : NN --> CC /\\ %s )' % GS.CBj), tu([wc, w1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (W_, W_))], 'jca',
                 tsub(split_imp(S_['gf2lsc'])[0], {'Z': W_})), w.inst('gf2lsc')], 'syl', '%s e. CC' % LSW)
    EW = '( E ` %s )' % W_
    lsv = tu([tu([tu([dsw], 'oveq1d', '( %s / %s ) = ( ( %s x. %s ) / %s )' % (EW, D, D, LSW, D)), tu([lsc, dc, dn0], 'divcan3d', '( ( %s x. %s ) / %s ) = %s' % (D, LSW, D, LSW))],
                 'eqtrd', '( %s / %s ) = %s' % (EW, D, LSW))], 'eqcomd', '%s = ( %s / %s )' % (LSW, EW, D))
    # G1 ( V ) = Gamma ( V ) KK ( V )
    g1v = tu([tu([tu([lift(w, P_('A e. RR'), au), lift(w, P_('B e. RR'), au)], 'jca', '( A e. RR /\\ B e. RR )'), lift(w, P_('L e. RR+'), au)], 'jca',
                 '( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ )'), tu([vc, m1, vn0], '3jca', '( %s e. CC /\\ -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (V, V, V)), w.inst('gf1g1v')], 'syl2anc',
             '%s = ( ( _G ` %s ) x. %s )' % (GS.G1w(V), V, G1L.KK('A', 'B', 'L', V)))
    GKV = '( ( _G ` %s ) x. %s )' % (V, G1L.KK('A', 'B', 'L', V))
    G1V = GS.G1w(V)
    ecn = proj(w, au, 'E e. ( %s -cn-> CC )' % GS.HPZ)
    ewc = tu([tu([ecn, w.inst('cncff')], 'syl', 'E : %s --> CC' % GS.HPZ), whz], 'ffvelcdmd', '%s e. CC' % EW)
    idjk = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( C ` j ) = ( C ` k ) )')], 'fveq2d', '( j = k -> ( abs ` ( C ` j ) ) = ( abs ` ( C ` k ) ) )')], 'breq1d',
               '( j = k -> ( ( abs ` ( C ` j ) ) <_ 1 <-> ( abs ` ( C ` k ) ) <_ 1 ) )')
    CBk = 'A. k e. NN ( abs ` ( C ` k ) ) <_ 1'
    cbk = tu([lift(w, cbj, au), w.s([idjk], 'cbvralvw', '( %s <-> %s )' % (GS.CBj, CBk))], 'sylib', CBk)
    w00 = lin.linarith(w, au, [w0], '0 <_ ( Re ` %s )' % W_, leaves=LVW)
    mhb = tu([tu([lift(w, nv, au), lift(w, rr, au)], 'jca', '( N e. NN /\\ R e. RR )'), tu([lift(w, cf, au), cbk], 'jca', '( C : NN --> CC /\\ %s )' % CBk),
              tu([wc, w00], 'jca', '( %s e. CC /\\ 0 <_ ( Re ` %s ) )' % (W_, W_)), w.inst('gf1mhb')], 'syl3anc', '( %s e. CC /\\ ( abs ` %s ) <_ %s )' % (MHW, MHW, GS.HMNR))
    mhwc = tu([mhb], 'simpld', '%s e. CC' % MHW)
    g1c = tu([g1v, tu([tu([vdg, w.inst('gamcl')], 'syl', '( _G ` %s ) e. CC' % V), GA_.kkcc(w, au, {'A e. RR': lift(w, P_('A e. RR'), au), 'B e. RR': lift(w, P_('B e. RR'), au), 'L e. RR+': lift(w, P_('L e. RR+'), au)}, vc, V)], 'mulcld', '%s e. CC' % GKV)], 'eqeltrd', '%s e. CC' % G1V)
    # the chain
    SQ = 'sum_ n e. NN %s' % ZQ('n')
    ch1 = tu([gav, tu([sumv], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (GKV, SQ, GKV, MHW, LSW))], 'eqtrd', '( %s ` %s ) = ( %s x. ( %s x. %s ) )' % (GAQ, V, GKV, MHW, LSW))
    ch2 = tu([tu([g1v], 'eqcomd', '%s = %s' % (GKV, G1V)), tu([lsv], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s / %s ) )' % (MHW, LSW, MHW, EW, D))], 'oveq12d',
             '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. ( %s / %s ) ) )' % (GKV, MHW, LSW, G1V, MHW, EW, D))
    ME = '( %s x. %s )' % (MHW, EW)
    ch3 = tu([tu([tu([mhwc, ewc, dc, dn0], 'divassd', '( %s / %s ) = ( %s x. ( %s / %s ) )' % (ME, D, MHW, EW, D))], 'eqcomd', '( %s x. ( %s / %s ) ) = ( %s / %s )' % (MHW, EW, D, ME, D))],
             'oveq2d', '( %s x. ( %s x. ( %s / %s ) ) ) = ( %s x. ( %s / %s ) )' % (G1V, MHW, EW, D, G1V, ME, D))
    ch4 = tu([tu([g1c, tu([mhwc, ewc], 'mulcld', '%s e. CC' % ME), dc, dn0], 'divassd', '( ( %s x. %s ) / %s ) = ( %s x. ( %s / %s ) )' % (G1V, ME, D, G1V, ME, D))], 'eqcomd',
             '( %s x. ( %s / %s ) ) = ( ( %s x. %s ) / %s )' % (G1V, ME, D, G1V, ME, D))
    HBV = GS.HFB(V)
    assert HBV == '( %s x. %s )' % (G1V, ME), (HBV,)
    ch5 = tu([dq], 'oveq2d', '( %s / %s ) = %s' % (HBV, D, GS.GIB(V)))
    giv, _ = mpv(w, au, 'w', GS.DI, GS.GIB('w'), V, vdi)
    pw = tu([tu([tu([tu([tu([ch1, ch2], 'eqtrd', '( %s ` %s ) = ( %s x. ( %s x. ( %s / %s ) ) )' % (GAQ, V, G1V, MHW, EW, D)), ch3], 'eqtrd',
                        '( %s ` %s ) = ( %s x. ( %s / %s ) )' % (GAQ, V, G1V, ME, D)), ch4], 'eqtrd', '( %s ` %s ) = ( %s / %s )' % (GAQ, V, HBV, D)), ch5], 'eqtrd',
                '( %s ` %s ) = %s' % (GAQ, V, GS.GIB(V))), giv], 'eqtr4d', '( %s ` %s ) = ( %s ` %s )' % (GAQ, V, GS.GI, V))
    ral = st([pw], 'ralrimiva', 'A. u e. RR ( %s ` ( 1 + ( _i x. u ) ) ) = ( %s ` ( 1 + ( _i x. u ) ) )' % (GAQ, GS.GI))
    cnex = a1(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V')
    gaqv = st([a1(w, a, w.s([w.s([], 'cnex', 'CC e. _V')], 'difexi', '( CC \\ ( ZZ \\ NN ) ) e. _V'), '( CC \\ ( ZZ \\ NN ) ) e. _V')], 'mptexd', '%s e. _V' % GAQ)
    dicc = st([st([], 'difssd', '%s C_ %s' % (GS.DI, GS.HPM1)), a1(w, a, w.s([], 'hpss', '%s C_ CC' % GS.HPM1), '%s C_ CC' % GS.HPM1)], 'sstrd', '%s C_ CC' % GS.DI)
    giv_ = st([st([cnex, dicc], 'ssexd', '%s e. _V' % GS.DI)], 'mptexd', '%s e. _V' % GS.GI)
    vle = st([st([st([], '1red', '1 e. RR'), st([gaqv, giv_], 'jca', '( %s e. _V /\\ %s e. _V )' % (GAQ, GS.GI))], 'jca', '( 1 e. RR /\\ ( %s e. _V /\\ %s e. _V ) )' % (GAQ, GS.GI)),
              ral, w.inst('z6vleq')], 'syl2anc', '%s = %s' % (GS.VLh(GAQ, '1'), GS.VLh(GS.GI, '1')))
    idth = w.s([], 'id', '( t = h -> t = h )')
    cth, _ = w.congr(GA_.LIt_(GAQ, '1', 't'), {'t': 'h'}, 't = h', {'t': idth})
    cbm = a1(w, a, w.s([cth], 'cbvmptv', '%s = %s' % (GA_.VLF(GAQ, '1'), GS.VLhF(GAQ, '1'))), '%s = %s' % (GA_.VLF(GAQ, '1'), GS.VLhF(GAQ, '1')))
    vth = st([cbm], 'fveq2d', '%s = %s' % (GA_.VL(GAQ, '1'), GS.VLh(GAQ, '1')))
    STN = '( %s x. sum_ n e. NN %s )' % (GS.TPI, TNQ('n'))
    ae = st([anc], 'simprd', '%s = %s' % (STN, GA_.VL(GAQ, '1')))
    acv = st([anc], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % TNFQ)
    e1 = st([st([ae, vth], 'eqtrd', '%s = %s' % (STN, GS.VLh(GAQ, '1'))), vle], 'eqtrd', '%s = %s' % (STN, GS.VLh(GS.GI, '1')))
    shr = st([P_(GS.MSH), w.inst('gf2shiftr')], 'syl', split_imp(S_['gf2shiftr'])[1])
    e2 = st([st([e1], 'oveq1d', '( %s - %s ) = ( %s - %s )' % (STN, GS.VLh(GS.GI, GS.CLL), GS.VLh(GS.GI, '1'), GS.VLh(GS.GI, GS.CLL))), shr], 'eqtrd',
            '( %s - %s ) = %s' % (STN, GS.VLh(GS.GI, GS.CLL), GS.RES))
    w.qed([st([acv, e2], 'jca', split_imp(S_['gf2gram'])[1])], 'idi', S_['gf2gram'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
