"""Sortie LD1, sections 2 and 6: Lemma 2.3 on the half line (ld1lhalf) and the divisor-count mean square
(ld1taumul ld1taud ld1tau2).  Run: MM_DB=sorties/ld1.mm MM_ENGINE=mmatch python3 tools/gen/ld1_g.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ld1lib import *
import z6alib as Z6
import lin as _L
_L.MAXPOW = 8

only = sys.argv[1:]
want = lambda l: not only or l in only
L = '( log ` D )'
ONE = lambda w, A: w.s([], '1red', '( %s -> 1 e. RR )' % A)


def fin(w):
    qedlast(w)
    return go(w)


def taufacts(w, An, nstep, n, c):
    """TAU(n) e. RR and 0 <_ TAU(n) as leaves of c (n e. NN by nstep)"""
    h = ap(w, An, 'hashcl', [ap(w, An, 'dvdsfi', [nstep], '%s e. Fin' % DV(n))], '%s e. NN0' % TAU(n))
    c.leaf(TAU(n), 'RR', dst(w, An, [h], 'nn0red', '%s e. RR' % TAU(n)))
    c.leaf(TAU(n), 'ge0', dst(w, An, [h], 'nn0ge0d', '0 <_ %s' % TAU(n)))
    return h


def ld1lhalf():
    w = W('ld1lhalf', 'Lean ` norm_LFunction_half_le ` (Lemma 2.3, I1 at ` Re s = 1 / 2 ` ): ` abs L ( Z ) <_ 600000 C_tau D ^ ( 201 / 800 ) log D ( 1 + abs U ) ^ 2 ` for ` Re Z = 1 / 2 ` , ` U = Im Z - Im S ` , from the convexity interface (~ z6omgd , ~ mulcxp , ~ cxpaddd ).')
    A = ante('ld1lhalf'); P = parts(w, A)
    dr, d1, dl2, nn, hdn = P['D e. RR'], P['1 < D'], P['2 <_ ( log ` D )'], P['N e. NN'], P[Z6.HDN]
    sc, zc, rz, cvx = P['S e. CC'], P['Z e. CC'], P['( Re ` Z ) = ( 1 / 2 )'], P[Z6.CVXH]
    rp = dst(w, A, [dr, linarith(w, A, [d1], '0 < D', closure=Closure(w, A, {'D': ('RR', dr)}))], 'elrpd', 'D e. RR+')
    lr = dst(w, A, [rp], 'relogcld', '%s e. RR' % L)
    IZ, IS = '( Im ` Z )', '( Im ` S )'; U = '( %s - %s )' % (IZ, IS); AU = '( abs ` %s )' % U
    OM = '( # ` { p e. Prime | p || N } )'; OMG = '( 2 ^ %s )' % OM
    omn = ap(w, A, 'hashcl', [ap(w, A, 'prmdvdsfi', [nn], '{ p e. Prime | p || N } e. Fin')], '%s e. NN0' % OM)
    c = Closure(w, A, {'D': [('RR+', rp), ('gt1', d1)], L: ('RR', lr), 'N': ('NN', nn), 'S': ('CC', sc), 'Z': ('CC', zc), OM: ('NN0', omn)})
    # CTau e. NN from df-ctau
    ct1 = w.s([], 'df-ctau', 'CTau = ( 2 ^ ( 2 ^ ; ; 8 0 0 ) )')
    e800 = w.s([w.s([], '2nn', '2 e. NN'), num.nn0(w, 800), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ; ; 8 0 0 ) e. NN')
    ctn = w.s([w.s([], '2nn', '2 e. NN'), w.s([e800], 'nnnn0i', '( 2 ^ ; ; 8 0 0 ) e. NN0'), w.inst('nnexpcl')], 'mp2an', '( 2 ^ ( 2 ^ ; ; 8 0 0 ) ) e. NN')
    c.leaf('CTau', 'NN', w.s([w.s([ct1, ctn], 'eqeltri', 'CTau e. NN')], 'a1i', '( %s -> CTau e. NN )' % A))
    c.leaf(IZ, 'RR', dst(w, A, [zc], 'imcld', '%s e. RR' % IZ)); c.leaf(IS, 'RR', dst(w, A, [sc], 'imcld', '%s e. RR' % IS)); c.leaf('( Re ` Z )', 'RR', dst(w, A, [zc], 'recld', '( Re ` Z ) e. RR'))
    # Z e. HPZ
    rz0 = dst(w, A, [w.s([num.fact(w, '( 1 / 2 )', 'gt0')], 'a1i', '( %s -> 0 < ( 1 / 2 ) )' % A), eqc(w, A, rz)], 'breqtrd', '0 < ( Re ` Z )')
    rio = dst(w, A, [J(w, A, c.mem('( Re ` Z )', 'RR'), rz0), a1(w, A, 'elrp', '( ( Re ` Z ) e. RR+ <-> ( ( Re ` Z ) e. RR /\\ 0 < ( Re ` Z ) ) )')], 'mpbird', '( Re ` Z ) e. RR+')
    rio2 = dst(w, A, [rio, a1(w, A, 'ioorp', '( 0 (,) +oo ) = RR+')], 'eleqtrrd', '( Re ` Z ) e. ( 0 (,) +oo )')
    ffn = dst(w, A, [a1(w, A, 'ref', 'Re : CC --> RR')], 'ffnd', 'Re Fn CC')
    hp = dst(w, A, [J(w, A, zc, rio2), ap(w, A, 'elpreima', [ffn], '( Z e. %s <-> ( Z e. CC /\\ ( Re ` Z ) e. ( 0 (,) +oo ) ) )' % Z6.HPZ)], 'mpbird', 'Z e. %s' % Z6.HPZ)
    CB = '( ( ( 1 / ; ; 2 0 0 ) <_ ( Re ` s ) /\\ ( Re ` s ) <_ 2 /\\ s =/= 1 ) -> ( abs ` ( ( E ` s ) / ( s - 1 ) ) ) <_ %s )' % Z6.CVXB('s')
    assert Z6.CVXH == 'A. s e. %s %s' % (Z6.HPZ, CB), Z6.CVXH
    cg, CBZ = w.wcongr(CB, {'s': 'Z'}, 's = Z', {'s': w.s([], 'id', '( s = Z -> s = Z )')})
    inst = w.s([cg, cvx, hp], 'rspcdva', '( %s -> %s )' % (A, CBZ))
    c1 = dst(w, A, [w.s([num.le_lit(w, '( 1 / ; ; 2 0 0 )', '( 1 / 2 )')], 'a1i', '( %s -> ( 1 / ; ; 2 0 0 ) <_ ( 1 / 2 ) )' % A), rz], 'breqtrrd', '( 1 / ; ; 2 0 0 ) <_ ( Re ` Z )')
    c2 = dst(w, A, [rz, w.s([num.le_lit(w, '( 1 / 2 )', '2')], 'a1i', '( %s -> ( 1 / 2 ) <_ 2 )' % A)], 'eqbrtrd', '( Re ` Z ) <_ 2')
    A1 = '( %s /\\ Z = 1 )' % A
    r1 = eqt(w, A1, eqt(w, A1, eqc(w, A1, lift(w, rz, A1)), dst(w, A1, [w.s([], 'simpr', '( %s -> Z = 1 )' % A1)], 'fveq2d', '( Re ` Z ) = ( Re ` 1 )')), a1(w, A1, 're1', '( Re ` 1 ) = 1'))
    ne = w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], 'halflt1', '( 1 / 2 ) < 1'), w.inst('ltne')], 'mp2an', '1 =/= ( 1 / 2 )')
    nz1 = dst(w, A, [r1, dst(w, A1, [w.s([w.s([ne], 'necomi', '( 1 / 2 ) =/= 1')], 'a1i', '( %s -> ( 1 / 2 ) =/= 1 )' % A1)], 'neneqd', '-. ( 1 / 2 ) = 1')], 'pm2.65da', '-. Z = 1')
    c3 = dst(w, A, [nz1], 'neqned', 'Z =/= 1')
    cvb = dst(w, A, [J(w, A, c1, c2, c3), inst], 'mpd', '( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) <_ %s' % Z6.CVXB('Z'))
    # the exponent at Re Z = 1/2 is 1/4
    IFZ = 'if ( 1 <_ ( Re ` Z ) , 0 , ( ( 1 - ( Re ` Z ) ) / 2 ) )'
    nle = dst(w, A, [dst(w, A, [eqc(w, A, rz), w.s([w.s([], 'halflt1', '( 1 / 2 ) < 1')], 'a1i', '( %s -> ( 1 / 2 ) < 1 )' % A)], 'eqbrtrrd', '( Re ` Z ) < 1'),
                     dst(w, A, [c.mem('( Re ` Z )', 'RR'), ONE(w, A)], 'ltnled', '( ( Re ` Z ) < 1 <-> -. 1 <_ ( Re ` Z ) )')], 'mpbid', '-. 1 <_ ( Re ` Z )')
    q14 = eqt(w, A, dst(w, A, [nle], 'iffalsed', '%s = ( ( 1 - ( Re ` Z ) ) / 2 )' % IFZ),
              eqt(w, A, dst(w, A, [dst(w, A, [rz], 'oveq2d', '( 1 - ( Re ` Z ) ) = ( 1 - ( 1 / 2 ) )')], 'oveq1d', '( ( 1 - ( Re ` Z ) ) / 2 ) = ( ( 1 - ( 1 / 2 ) ) / 2 )'),
                  ringeq(w, A, '( ( 1 - ( 1 / 2 ) ) / 2 )', '( 1 / 4 )', c)))
    NZ2 = '( N x. ( ( abs ` %s ) + 2 ) )' % IZ; NZ3 = '( N x. ( ( abs ` %s ) + 3 ) )' % IZ
    QZ = '( 1 / ( abs ` ( Z - 1 ) ) )'; K2 = '; ; ; ; ; 2 0 0 0 0 0'
    P4 = '( %s ^c ( 1 / 4 ) )' % NZ2; LN3 = '( log ` %s )' % NZ3
    INN = '( ( %s x. %s ) + %s )' % (P4, LN3, QZ)
    B0 = '( ( %s x. %s ) x. %s )' % (K2, OMG, INN)
    r0, t0 = w.rewrite(Z6.CVXB('Z'), {IFZ: ('( 1 / 4 )', q14)}, A)
    assert t0 == B0, (t0, B0)
    cvb2 = dst(w, A, [cvb, r0], 'breqtrd', '( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) <_ %s' % B0)
    # abs Im Z <_ abs Im S + abs U
    AIZ, AIS = '( abs ` %s )' % IZ, '( abs ` %s )' % IS
    for e_ in (AIZ, AIS, AU):
        c.leaf(e_, 'RR', c.mem(e_, 'RR')); c.leaf(e_, 'ge0', c.ge0(e_))
    izs = dst(w, A, [c.mem(IS, 'CC'), c.mem(IZ, 'CC')], 'pncan3d', '( %s + %s ) = %s' % (IS, U, IZ))
    tri = dst(w, A, [c.mem(IS, 'CC'), c.mem(U, 'CC')], 'abstrid', '( abs ` ( %s + %s ) ) <_ ( %s + %s )' % (IS, U, AIS, AU))
    himz = dst(w, A, [dst(w, A, [izs], 'fveq2d', '( abs ` ( %s + %s ) ) = %s' % (IS, U, AIZ)), tri], 'eqbrtrrd', '%s <_ ( %s + %s )' % (AIZ, AIS, AU))
    # hpole: 1 / abs ( Z - 1 ) <_ 2
    ZM = '( Z - 1 )'; AZ = '( abs ` %s )' % ZM
    rez = eqt(w, A, dst(w, A, [zc, w.s([], '1cnd', '( %s -> 1 e. CC )' % A)], 'resubd', '( Re ` %s ) = ( ( Re ` Z ) - ( Re ` 1 ) )' % ZM),
              dst(w, A, [rz, a1(w, A, 're1', '( Re ` 1 ) = 1')], 'oveq12d', '( ( Re ` Z ) - ( Re ` 1 ) ) = ( ( 1 / 2 ) - 1 )'))
    are = ap(w, A, 'absrele', [c.mem(ZM, 'CC')], '( abs ` ( Re ` %s ) ) <_ %s' % (ZM, AZ))
    hv = eqt(w, A, dst(w, A, [rez], 'fveq2d', '( abs ` ( Re ` %s ) ) = ( abs ` ( ( 1 / 2 ) - 1 ) )' % ZM),
             eqt(w, A, dst(w, A, [ringeq(w, A, '( ( 1 / 2 ) - 1 )', '-u ( 1 / 2 )', c)], 'fveq2d', '( abs ` ( ( 1 / 2 ) - 1 ) ) = ( abs ` -u ( 1 / 2 ) )'),
                 eqt(w, A, dst(w, A, [c.mem('( 1 / 2 )', 'CC')], 'absnegd', '( abs ` -u ( 1 / 2 ) ) = ( abs ` ( 1 / 2 ) )'), dst(w, A, [c.mem('( 1 / 2 )', 'RR'), c.ge0('( 1 / 2 )')], 'absidd', '( abs ` ( 1 / 2 ) ) = ( 1 / 2 )'))))
    azh = dst(w, A, [hv, are], 'eqbrtrrd', '( 1 / 2 ) <_ %s' % AZ)
    c.leaf(AZ, 'RR', c.mem(AZ, 'RR')); azp = linarith(w, A, [azh], '0 < %s' % AZ, closure=c); c.leaf(AZ, 'gt0', azp)
    ldm = ap(w, A, 'ledivmul', [ONE(w, A), c.mem('2', 'RR'), J(w, A, c.mem(AZ, 'RR'), azp)], '( %s <_ 2 <-> 1 <_ ( %s x. 2 ) )' % (QZ, AZ))
    hpole = dst(w, A, [linarith(w, A, [azh], '1 <_ ( %s x. 2 )' % AZ, closure=c), ldm], 'mpbird', '%s <_ 2' % QZ)
    # hbase
    n0 = c.ge0('N'); n1 = dst(w, A, [nn], 'nnge1d', '1 <_ N')
    nd = nlinarith(w, A, [hdn, n0, c.ge0(AIS)], 'N <_ D', closure=c)
    DU = '( D x. ( 1 + %s ) )' % AU
    hbase = nlinarith(w, A, [hdn, himz, n0, c.ge0(AU), nd], '%s <_ %s' % (NZ2, DU), closure=c)
    # hpow
    E4 = '( D ^c ( 1 / 4 ) )'; U1 = '( 1 + %s )' % AU
    p1 = dst(w, A, [hbase, ap(w, A, 'cxple2', [J(w, A, c.mem(NZ2, 'RR'), c.ge0(NZ2)), J(w, A, c.mem(DU, 'RR'), c.ge0(DU)), c.mem('( 1 / 4 )', 'RR+')],
                                '( %s <_ %s <-> ( %s ^c ( 1 / 4 ) ) <_ ( %s ^c ( 1 / 4 ) ) )' % (NZ2, DU, NZ2, DU))], 'mpbid', '%s <_ ( %s ^c ( 1 / 4 ) )' % (P4, DU))
    mc = ap(w, A, 'mulcxp', [J(w, A, dr, c.ge0('D')), J(w, A, c.mem(U1, 'RR'), c.ge0(U1)), c.mem('( 1 / 4 )', 'CC')], '( %s ^c ( 1 / 4 ) ) = ( %s x. ( %s ^c ( 1 / 4 ) ) )' % (DU, E4, U1))
    u1ge1 = linarith(w, A, [c.ge0(AU)], '1 <_ %s' % U1, closure=c)
    cx = ap(w, A, 'cxplea', [J(w, A, c.mem(U1, 'RR'), u1ge1), J(w, A, c.mem('( 1 / 4 )', 'RR'), ONE(w, A)), w.s([num.le_lit(w, '( 1 / 4 )', '1')], 'a1i', '( %s -> ( 1 / 4 ) <_ 1 )' % A)], '( %s ^c ( 1 / 4 ) ) <_ ( %s ^c 1 )' % (U1, U1))
    cx1 = dst(w, A, [cx, ap(w, A, 'cxp1', [c.mem(U1, 'CC')], '( %s ^c 1 ) = %s' % (U1, U1))], 'breqtrd', '( %s ^c ( 1 / 4 ) ) <_ %s' % (U1, U1))
    for e_ in (E4, '( %s ^c ( 1 / 4 ) )' % U1, P4, '( %s ^c ( 1 / 4 ) )' % DU):
        c.leaf(e_, 'RR', c.mem(e_, 'RR')); c.leaf(e_, 'ge0', c.ge0(e_))
    hpow = dst(w, A, [c.mem(P4, 'RR'), c.mem('( %s ^c ( 1 / 4 ) )' % DU, 'RR'), c.mem('( %s x. %s )' % (E4, U1), 'RR'), p1,
                      dst(w, A, [mc, lemul(w, A, c, cx1, E4)], 'eqbrtrd', '( %s ^c ( 1 / 4 ) ) <_ ( %s x. %s )' % (DU, E4, U1))], 'letrd', '%s <_ ( %s x. %s )' % (P4, E4, U1))
    # hlog
    hb3 = nlinarith(w, A, [hbase, nd, c.ge0(AU), n0], '%s <_ ( 2 x. %s )' % (NZ3, DU), closure=c)
    nz3rp = dst(w, A, [c.mem(NZ3, 'RR'), c.gt0(NZ3)], 'elrpd', '%s e. RR+' % NZ3)
    durp = dst(w, A, [c.mem('( 2 x. %s )' % DU, 'RR'), c.gt0('( 2 x. %s )' % DU)], 'elrpd', '( 2 x. %s ) e. RR+' % DU)
    lg1 = dst(w, A, [hb3, dst(w, A, [nz3rp, durp], 'logled', '( %s <_ ( 2 x. %s ) <-> %s <_ ( log ` ( 2 x. %s ) ) )' % (NZ3, DU, LN3, DU))], 'mpbid', '%s <_ ( log ` ( 2 x. %s ) )' % (LN3, DU))
    u1rp = dst(w, A, [c.mem(U1, 'RR'), c.gt0(U1)], 'elrpd', '%s e. RR+' % U1)
    lm1 = dst(w, A, [a1(w, A, '2rp', '2 e. RR+'), dst(w, A, [rp, u1rp], 'rpmulcld', '%s e. RR+' % DU)], 'relogmuld', '( log ` ( 2 x. %s ) ) = ( ( log ` 2 ) + ( log ` %s ) )' % (DU, DU))
    lm2 = dst(w, A, [rp, u1rp], 'relogmuld', '( log ` %s ) = ( %s + ( log ` %s ) )' % (DU, L, U1))
    L2 = '( log ` 2 )'; LU = '( log ` %s )' % U1
    l21 = w.s([w.s([], 'log2le1', '%s < 1' % L2)], 'a1i', '( %s -> %s < 1 )' % (A, L2))
    lu0 = ap(w, A, 'logge0', [J(w, A, c.mem(U1, 'RR'), u1ge1)], '0 <_ %s' % LU)
    for e_ in (LU, L2, LN3, '( log ` ( 2 x. %s ) )' % DU, '( log ` %s )' % DU):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    ef = ap(w, A, 'bvefge1p', [J(w, A, c.mem(LU, 'RR'), lu0)], '( 1 + %s ) <_ ( exp ` %s )' % (LU, LU))
    el = ap(w, A, 'reeflog', [u1rp], '( exp ` %s ) = %s' % (LU, U1))
    luu = dst(w, A, [ef, el], 'breqtrd', '( 1 + %s ) <_ %s' % (LU, U1))
    hlog = nlinarith(w, A, [lg1, lm1, lm2, l21, luu, dl2, c.ge0(AU)], '%s <_ ( ( 2 x. %s ) x. %s )' % (LN3, L, U1), closure=c)
    # hmain, hinner
    lg0 = ap(w, A, 'logge0', [J(w, A, c.mem(NZ3, 'RR'), nlinarith(w, A, [n1, c.ge0(AIZ)], '1 <_ %s' % NZ3, closure=c))], '0 <_ %s' % LN3)
    hmain = dst(w, A, [c.mem(P4, 'RR'), c.mem('( %s x. %s )' % (E4, U1), 'RR'), c.mem(LN3, 'RR'), c.mem('( ( 2 x. %s ) x. %s )' % (L, U1), 'RR'), c.ge0(P4), lg0, hpow, hlog], 'lemul12ad',
                '( %s x. %s ) <_ ( ( %s x. %s ) x. ( ( 2 x. %s ) x. %s ) )' % (P4, LN3, E4, U1, L, U1))
    U2 = '( %s ^ 2 )' % U1; W_ = '( ( %s x. %s ) x. %s )' % (E4, L, U2)
    rgm = ringeqp(w, A, '( ( %s x. %s ) x. ( ( 2 x. %s ) x. %s ) )' % (E4, U1, L, U1), '( 2 x. %s )' % W_, c)
    e41 = dst(w, A, [ap(w, A, 'cxp0', [c.mem('D', 'CC')], '( D ^c 0 ) = 1'),
                     ap(w, A, 'cxplea', [J(w, A, dr, ltle(w, A, c, d1)), J(w, A, w.s([], '0red', '( %s -> 0 e. RR )' % A), c.mem('( 1 / 4 )', 'RR')), c.ge0('( 1 / 4 )')], '( D ^c 0 ) <_ %s' % E4)], 'eqbrtrrd', '1 <_ %s' % E4)
    u21 = ap(w, A, 'expge1', [J(w, A, c.mem(U1, 'RR'), a1(w, A, '2nn0', '2 e. NN0'), u1ge1)], '1 <_ %s' % U2)
    c.leaf(U2, 'RR', c.mem(U2, 'RR')); c.leaf(U2, 'ge0', c.ge0(U2))
    w1 = dst(w, A, [ONE(w, A), c.mem(E4, 'RR'), c.mem('2', 'RR'), c.mem(L, 'RR'), a1(w, A, '0le1', '0 <_ 1'), c.ge0('2'), e41, dl2], 'lemul12ad', '( 1 x. 2 ) <_ ( %s x. %s )' % (E4, L))
    w2 = dst(w, A, [c.mem('( 1 x. 2 )', 'RR'), c.mem('( %s x. %s )' % (E4, L), 'RR'), ONE(w, A), c.mem(U2, 'RR'), c.ge0('( 1 x. 2 )'), a1(w, A, '0le1', '0 <_ 1'), w1, u21], 'lemul12ad', '( ( 1 x. 2 ) x. 1 ) <_ %s' % W_)
    c.mem(W_, 'RR')
    two = linarith(w, A, [w2], '2 <_ %s' % W_, closure=c)
    c.leaf(P4, 'RR', c.mem(P4, 'RR')); c.leaf(LN3, 'RR', c.mem(LN3, 'RR')); c.leaf(QZ, 'RR', c.mem(QZ, 'RR'))
    c.atom('( %s x. %s )' % (P4, LN3)); c.leaf('( %s x. %s )' % (P4, LN3), 'RR', c.mem('( %s x. %s )' % (P4, LN3), 'RR'))
    c.leaf('( %s x. %s )' % (P4, LN3), 'ge0', dst(w, A, [c.mem(P4, 'RR'), c.mem(LN3, 'RR'), c.ge0(P4), lg0], 'mulge0d', '0 <_ ( %s x. %s )' % (P4, LN3)))
    hinner = linarith(w, A, [hmain, rgm, hpole, two], '%s <_ ( 3 x. %s )' % (INN, W_), closure=c)
    # omega and the product
    hom = ap(w, A, 'z6omgd', [nn, J(w, A, dr, nd)], '%s <_ ( CTau x. ( D ^c ( 1 / ; ; 8 0 0 ) ) )' % OMG)
    E8 = '( D ^c ( 1 / ; ; 8 0 0 ) )'
    for e_ in (E8, OMG):
        c.leaf(e_, 'RR', c.mem(e_, 'RR')); c.leaf(e_, 'ge0', c.ge0(e_))
    l1 = lemul(w, A, c, hom, K2)
    inn0 = linarith(w, A, [c.ge0('( %s x. %s )' % (P4, LN3)), c.ge0(QZ)], '0 <_ %s' % INN, closure=c)
    prod = dst(w, A, [c.mem('( %s x. %s )' % (K2, OMG), 'RR'), c.mem('( %s x. ( CTau x. %s ) )' % (K2, E8), 'RR'), c.mem(INN, 'RR'), c.mem('( 3 x. %s )' % W_, 'RR'), c.ge0('( %s x. %s )' % (K2, OMG)), inn0, l1, hinner], 'lemul12ad',
               '%s <_ ( ( %s x. ( CTau x. %s ) ) x. ( 3 x. %s ) )' % (B0, K2, E8, W_))
    rg = ringeq(w, A, '( ( %s x. ( CTau x. %s ) ) x. ( 3 x. %s ) )' % (K2, E8, W_), '( ( ( ; ; ; ; ; 6 0 0 0 0 0 x. CTau ) x. ( %s x. %s ) ) x. ( %s x. %s ) )' % (E8, E4, L, U2), c)
    ca = dst(w, A, [c.mem('D', 'CC'), c.ne0('D'), c.mem('( 1 / ; ; 8 0 0 )', 'CC'), c.mem('( 1 / 4 )', 'CC')], 'cxpaddd', '( D ^c ( ( 1 / ; ; 8 0 0 ) + ( 1 / 4 ) ) ) = ( %s x. %s )' % (E8, E4))
    ee = ringeq(w, A, '( ( 1 / ; ; 8 0 0 ) + ( 1 / 4 ) )', '( ; ; 2 0 1 / ; ; 8 0 0 )', c)
    e84 = eqt(w, A, eqc(w, A, ca), dst(w, A, [ee], 'oveq2d', '( D ^c ( ( 1 / ; ; 8 0 0 ) + ( 1 / 4 ) ) ) = ( D ^c ( ; ; 2 0 1 / ; ; 8 0 0 ) )'))
    o1 = dst(w, A, [e84], 'oveq2d', '( ( ; ; ; ; ; 6 0 0 0 0 0 x. CTau ) x. ( %s x. %s ) ) = %s' % (E8, E4, KHALF))
    o2 = dst(w, A, [o1], 'oveq1d', '( ( ( ; ; ; ; ; 6 0 0 0 0 0 x. CTau ) x. ( %s x. %s ) ) x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (E8, E4, L, U2, KHALF, L, U2))
    bnd = dst(w, A, [prod, eqt(w, A, rg, o2)], 'breqtrd', '%s <_ ( %s x. ( %s x. %s ) )' % (B0, KHALF, L, U2))
    # abs ( ( E ` Z ) / ( Z - 1 ) ) is only known to be an extended real (E ` Z e. CC is not among the hypotheses): xrletrd
    brl = w.s([w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')], 'brel', '( ( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) <_ %s -> ( ( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) e. RR* /\\ %s e. RR* ) )' % (B0, B0))
    lrel = w.s([cvb2, brl], 'syl', '( %s -> ( ( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) e. RR* /\\ %s e. RR* ) )' % (A, B0))
    kxr = dst(w, A, [c.mem('( %s x. ( %s x. %s ) )' % (KHALF, L, U2), 'RR')], 'rexrd', '( %s x. ( %s x. %s ) ) e. RR*' % (KHALF, L, U2))
    dst(w, A, [dst(w, A, [lrel], 'simpld', '( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) e. RR*'), dst(w, A, [lrel], 'simprd', '%s e. RR*' % B0), kxr, cvb2, bnd], 'xrletrd',
        '( abs ` ( ( E ` Z ) / ( Z - 1 ) ) ) <_ ( %s x. ( %s x. %s ) )' % (KHALF, L, U2))
    return fin(w)


def ld1taumul():
    w = W('ld1taumul', '` tau ( M N ) <_ tau ( M ) tau ( N ) ` by the injection ` e |-> <. e gcd M , e / ( e gcd M ) >. ` of the divisors of ` M N ` into pairs of divisors (~ f1mpt , ~ f1domg , ~ hashdomi , ~ hashxp , ~ coprmdvds ).')
    A = ante('ld1taumul'); P = parts(w, A); mn, nn = P['M e. NN'], P['N e. NN']
    MN = '( M x. N )'; DMN, DM, DN = DV(MN), DV('M'), DV('N')
    G = lambda e: '( %s gcd M )' % e
    F = '( e e. %s |-> <. %s , ( e / %s ) >. )' % (DMN, G('e'), G('e'))
    XP = '( %s X. %s )' % (DM, DN)
    hf = w.s([], 'eqid', '%s = %s' % (F, F))
    cg, DY = w.congr('<. %s , ( e / %s ) >.' % (G('e'), G('e')), {'e': 'y'}, 'e = y', {'e': w.s([], 'id', '( e = y -> e = y )')})
    F1 = '( %s : %s -1-1-> %s <-> ( A. e e. %s <. %s , ( e / %s ) >. e. %s /\\ A. e e. %s A. y e. %s ( <. %s , ( e / %s ) >. = %s -> e = y ) ) )' % (F, DMN, XP, DMN, G('e'), G('e'), XP, DMN, DMN, G('e'), G('e'), DY)
    f1 = w.s([hf, cg], 'f1mpt', F1)
    def divfacts(An, v, vin, DVX, X):
        el = dst(w, An, [vin, a1(w, An, 'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (v, DVX, v, v, X))], 'mpbid', '( %s e. NN /\\ %s || %s )' % (v, v, X))
        return dst(w, An, [el], 'simpld', '%s e. NN' % v), dst(w, An, [el], 'simprd', '%s || %s' % (v, X))
    # (i) values in the product
    Ae = '( %s /\\ e e. %s )' % (A, DMN)
    ein = w.s([], 'simpr', '( %s -> e e. %s )' % (Ae, DMN))
    en, edv = divfacts(Ae, 'e', ein, DMN, MN)
    ce = Closure(w, Ae, {'M': ('NN', lift(w, mn, Ae)), 'N': ('NN', lift(w, nn, Ae)), 'e': ('NN', en)})
    g = G('e'); gn = ap(w, Ae, 'gcdnncl', [en, lift(w, mn, Ae)], '%s e. NN' % g); ce.leaf(g, 'NN', gn)
    gd = ap(w, Ae, 'gcddvds', [ce.mem('e', 'ZZ'), ce.mem('M', 'ZZ')], '( %s || e /\\ %s || M )' % (g, g))
    gde = dst(w, Ae, [gd], 'simpld', '%s || e' % g); gdm = dst(w, Ae, [gd], 'simprd', '%s || M' % g)
    Q = '( e / %s )' % g
    qn = dst(w, Ae, [gde, ap(w, Ae, 'nndivdvds', [en, gn], '( %s || e <-> %s e. NN )' % (g, Q))], 'mpbid', '%s e. NN' % Q); ce.leaf(Q, 'NN', qn)
    MQ = '( M / %s )' % g
    mqn = dst(w, Ae, [gdm, ap(w, Ae, 'nndivdvds', [lift(w, mn, Ae), gn], '( %s || M <-> %s e. NN )' % (g, MQ))], 'mpbid', '%s e. NN' % MQ); ce.leaf(MQ, 'NN', mqn)
    gdv = ap(w, Ae, 'gcddiv', [J(w, Ae, ce.mem('e', 'ZZ'), ce.mem('M', 'ZZ'), gn), J(w, Ae, gde, gdm)], '( %s / %s ) = ( %s gcd %s )' % (g, g, Q, MQ))
    one = dst(w, Ae, [ce.mem(g, 'CC'), ce.ne0(g)], 'dividd', '( %s / %s ) = 1' % (g, g))
    cop = eqt(w, Ae, eqc(w, Ae, gdv), one)
    eq1 = dst(w, Ae, [ce.mem('e', 'CC'), ce.mem(g, 'CC'), ce.ne0(g)], 'divcan2d', '( %s x. %s ) = e' % (g, Q))
    eq2 = dst(w, Ae, [ce.mem('M', 'CC'), ce.mem(g, 'CC'), ce.ne0(g)], 'divcan2d', '( %s x. %s ) = M' % (g, MQ))
    br = dst(w, Ae, [eqc(w, Ae, eq1), dst(w, Ae, [eqc(w, Ae, eq2)], 'oveq1d', '%s = ( ( %s x. %s ) x. N )' % (MN, g, MQ))], 'breq12d', '( e || %s <-> ( %s x. %s ) || ( ( %s x. %s ) x. N ) )' % (MN, g, Q, g, MQ))
    d1 = dst(w, Ae, [edv, br], 'mpbid', '( %s x. %s ) || ( ( %s x. %s ) x. N )' % (g, Q, g, MQ))
    asc = dst(w, Ae, [ce.mem(g, 'CC'), ce.mem(MQ, 'CC'), ce.mem('N', 'CC')], 'mulassd', '( ( %s x. %s ) x. N ) = ( %s x. ( %s x. N ) )' % (g, MQ, g, MQ))
    d2 = dst(w, Ae, [d1, asc], 'breqtrd', '( %s x. %s ) || ( %s x. ( %s x. N ) )' % (g, Q, g, MQ))
    d3 = dst(w, Ae, [d2, ap(w, Ae, 'dvdscmulr', [ce.mem(Q, 'ZZ'), ce.mem('( %s x. N )' % MQ, 'ZZ'), J(w, Ae, ce.mem(g, 'ZZ'), ce.ne0(g))], '( ( %s x. %s ) || ( %s x. ( %s x. N ) ) <-> %s || ( %s x. N ) )' % (g, Q, g, MQ, Q, MQ))], 'mpbid', '%s || ( %s x. N )' % (Q, MQ))
    d4 = dst(w, Ae, [J(w, Ae, d3, cop), ap(w, Ae, 'coprmdvds', [ce.mem(Q, 'ZZ'), ce.mem(MQ, 'ZZ'), ce.mem('N', 'ZZ')], '( ( %s || ( %s x. N ) /\\ ( %s gcd %s ) = 1 ) -> %s || N )' % (Q, MQ, Q, MQ, Q))], 'mpd', '%s || N' % Q)
    gin = dst(w, Ae, [J(w, Ae, gn, gdm), a1(w, Ae, 'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || M ) )' % (g, DM, g, g))], 'mpbird', '%s e. %s' % (g, DM))
    qin = dst(w, Ae, [J(w, Ae, qn, d4), a1(w, Ae, 'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || N ) )' % (Q, DN, Q, Q))], 'mpbird', '%s e. %s' % (Q, DN))
    pin = dst(w, Ae, [J(w, Ae, gin, qin), a1(w, Ae, 'opelxp', '( <. %s , %s >. e. %s <-> ( %s e. %s /\\ %s e. %s ) )' % (g, Q, XP, g, DM, Q, DN))], 'mpbird', '<. %s , %s >. e. %s' % (g, Q, XP))
    part1 = dst(w, A, [pin], 'ralrimiva', 'A. e e. %s <. %s , ( e / %s ) >. e. %s' % (DMN, G('e'), G('e'), XP))
    # (ii) injectivity
    Aey = '( %s /\\ ( e e. %s /\\ y e. %s ) )' % (A, DMN, DMN)
    eiy = w.s([], 'simprl', '( %s -> e e. %s )' % (Aey, DMN)); yiy = w.s([], 'simprr', '( %s -> y e. %s )' % (Aey, DMN))
    en2, _ = divfacts(Aey, 'e', eiy, DMN, MN); yn2, _ = divfacts(Aey, 'y', yiy, DMN, MN)
    gy = G('y')
    gne = ap(w, Aey, 'gcdnncl', [en2, lift(w, mn, Aey)], '%s e. NN' % g); gny = ap(w, Aey, 'gcdnncl', [yn2, lift(w, mn, Aey)], '%s e. NN' % gy)
    QY = '( y / %s )' % gy
    assert DY == '<. %s , %s >.' % (gy, QY), DY
    Aeq = '( %s /\\ <. %s , %s >. = %s )' % (Aey, g, Q, DY)
    op = dst(w, Aeq, [w.s([], 'simpr', '( %s -> <. %s , %s >. = %s )' % (Aeq, g, Q, DY)), a1(w, Aeq, 'opth', '( <. %s , %s >. = %s <-> ( %s = %s /\\ %s = %s ) )' % (g, Q, DY, g, gy, Q, QY))], 'mpbid', '( %s = %s /\\ %s = %s )' % (g, gy, Q, QY))
    ge = dst(w, Aeq, [op], 'simpld', '%s = %s' % (g, gy)); qe = dst(w, Aeq, [op], 'simprd', '%s = %s' % (Q, QY))
    cq = Closure(w, Aeq, {'e': ('NN', lift(w, en2, Aeq)), 'y': ('NN', lift(w, yn2, Aeq)), g: ('NN', lift(w, gne, Aeq)), gy: ('NN', lift(w, gny, Aeq))})
    e1 = eqc(w, Aeq, dst(w, Aeq, [cq.mem('e', 'CC'), cq.mem(g, 'CC'), cq.ne0(g)], 'divcan2d', '( %s x. %s ) = e' % (g, Q)))
    e2 = dst(w, Aeq, [cq.mem('y', 'CC'), cq.mem(gy, 'CC'), cq.ne0(gy)], 'divcan2d', '( %s x. %s ) = y' % (gy, QY))
    ey = eqt(w, Aeq, eqt(w, Aeq, e1, dst(w, Aeq, [ge, qe], 'oveq12d', '( %s x. %s ) = ( %s x. %s )' % (g, Q, gy, QY))), e2)
    imp = dst(w, Aey, [ey], 'ex', '( <. %s , %s >. = %s -> e = y )' % (g, Q, DY))
    part2 = dst(w, A, [imp], 'ralrimivva', 'A. e e. %s A. y e. %s ( <. %s , ( e / %s ) >. = %s -> e = y )' % (DMN, DMN, G('e'), G('e'), DY))
    isf1 = dst(w, A, [J(w, A, part1, part2), w.s([f1], 'a1i', '( %s -> %s )' % (A, F1))], 'mpbird', '%s : %s -1-1-> %s' % (F, DMN, XP))
    fim = ap(w, A, 'dvdsfi', [mn], '%s e. Fin' % DM); fin_ = ap(w, A, 'dvdsfi', [nn], '%s e. Fin' % DN)
    xpf = ap(w, A, 'xpfi', [fim, fin_], '%s e. Fin' % XP)
    dom = dst(w, A, [isf1, ap(w, A, 'f1domg', [xpf], '( %s : %s -1-1-> %s -> %s ~<_ %s )' % (F, DMN, XP, DMN, XP))], 'mpd', '%s ~<_ %s' % (DMN, XP))
    hle = ap(w, A, 'hashdomi', [dom], '( # ` %s ) <_ ( # ` %s )' % (DMN, XP))
    hx = ap(w, A, 'hashxp', [fim, fin_], '( # ` %s ) = ( ( # ` %s ) x. ( # ` %s ) )' % (XP, DM, DN))
    dst(w, A, [hle, hx], 'breqtrd', '%s <_ ( %s x. %s )' % (TAU(MN), TAU('M'), TAU('N')))
    return fin(w)


def ld1taud():
    w = W('ld1taud', '` sum_ ( d <_ x ) tau ( d ) / d <_ ( 1 + log x ) ^ 2 ` (~ dvdsflsumcom , ~ harmonicubnd ).')
    A = ante('ld1taud'); P = parts(w, A); xr, x1 = P['X e. RR'], P['1 <_ X']
    c = Closure(w, A, {'X': [('RR', xr), ('ge1', x1)]})
    x0 = linarith(w, A, [x1], '0 <_ X', closure=c); c.leaf('X', 'ge0', x0)
    xrp = dst(w, A, [xr, linarith(w, A, [x1], '0 < X', closure=c)], 'elrpd', 'X e. RR+'); c.leaf('X', 'RR+', xrp)
    FX = '( |_ ` X )'; R = '( 1 ... %s )' % FX; LX = '( log ` X )'; L1 = '( 1 + %s )' % LX
    c.leaf(LX, 'RR', c.mem(LX, 'RR'))
    flr = ap(w, A, 'reflcl', [xr], '%s e. RR' % FX); fll = ap(w, A, 'flle', [xr], '%s <_ X' % FX)
    rf = dst(w, A, [], 'fzfid', '%s e. Fin' % R)
    Ad = '( %s /\\ d e. %s )' % (A, R)
    dn = ap(w, Ad, 'elfznn', [w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, R))], 'd e. NN')
    fi = ap(w, Ad, 'dvdsfi', [dn], '%s e. Fin' % DV('d'))
    cd = Closure(w, Ad, {'d': ('NN', dn), 'X': [('RR', lift(w, xr, Ad)), ('ge0', lift(w, x0, Ad))]})
    th = taufacts(w, Ad, dn, 'd', cd)
    fc = ap(w, Ad, 'fsumconst', [fi, cd.mem('( 1 / d )', 'CC')], 'sum_ a e. %s ( 1 / d ) = ( %s x. ( 1 / d ) )' % (DV('d'), TAU('d')))
    dr = dst(w, Ad, [cd.mem(TAU('d'), 'CC'), cd.mem('d', 'CC'), cd.ne0('d')], 'divrecd', '( %s / d ) = ( %s x. ( 1 / d ) )' % (TAU('d'), TAU('d')))
    e1 = dst(w, A, [eqt(w, Ad, dr, eqc(w, Ad, fc))], 'sumeq2dv', 'sum_ d e. %s ( %s / d ) = sum_ d e. %s sum_ a e. %s ( 1 / d )' % (R, TAU('d'), R, DV('d')))
    RA = lambda a: '( 1 ... ( |_ ` ( X / %s ) ) )' % a
    h1 = w.s([], 'oveq2', '( d = ( a x. m ) -> ( 1 / d ) = ( 1 / ( a x. m ) ) )')
    Ada = '( %s /\\ ( d e. %s /\\ a e. %s ) )' % (A, R, DV('d'))
    dn2 = ap(w, Ada, 'elfznn', [w.s([], 'simprl', '( %s -> d e. %s )' % (Ada, R))], 'd e. NN')
    h3 = dst(w, Ada, [dst(w, Ada, [dn2], 'nnrecred', '( 1 / d ) e. RR')], 'recnd', '( 1 / d ) e. CC')
    s2 = w.s([h1, xr, h3], 'dvdsflsumcom', '( %s -> sum_ d e. %s sum_ a e. %s ( 1 / d ) = sum_ a e. %s sum_ m e. %s ( 1 / ( a x. m ) ) )' % (A, R, DV('d'), R, RA('a')))
    Aa = '( %s /\\ a e. %s )' % (A, R)
    an = ap(w, Aa, 'elfznn', [w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, R))], 'a e. NN')
    ca = Closure(w, Aa, {'a': ('NN', an), 'X': [('RR', lift(w, xr, Aa)), ('ge0', lift(w, x0, Aa)), ('RR+', lift(w, xrp, Aa))]})
    ca.leaf(LX, 'RR', lift(w, c.mem(LX, 'RR'), Aa))
    Aam = '( %s /\\ m e. %s )' % (Aa, RA('a'))
    mn = ap(w, Aam, 'elfznn', [w.s([], 'simpr', '( %s -> m e. %s )' % (Aam, RA('a')))], 'm e. NN')
    cam = Closure(w, Aam, {'a': ('NN', lift(w, an, Aam)), 'm': ('NN', mn)})
    dm = eqc(w, Aam, dst(w, Aam, [cam.mem('1', 'CC'), cam.mem('a', 'CC'), cam.mem('1', 'CC'), cam.mem('m', 'CC'), cam.ne0('a'), cam.ne0('m')], 'divmuldivd', '( ( 1 / a ) x. ( 1 / m ) ) = ( ( 1 x. 1 ) / ( a x. m ) )'))
    dm2 = dst(w, Aam, [dst(w, Aam, [a1(w, Aam, '1t1e1', '( 1 x. 1 ) = 1')], 'oveq1d', '( ( 1 x. 1 ) / ( a x. m ) ) = ( 1 / ( a x. m ) )')], 'eqcomd', '( 1 / ( a x. m ) ) = ( ( 1 x. 1 ) / ( a x. m ) )')
    per = eqt(w, Aam, dm2, dm)
    XA = '( X / a )'
    s3 = dst(w, Aa, [per], 'sumeq2dv', 'sum_ m e. %s ( 1 / ( a x. m ) ) = sum_ m e. %s ( ( 1 / a ) x. ( 1 / m ) )' % (RA('a'), RA('a')))
    rm = dst(w, Aam, [mn], 'nnrecred', '( 1 / m ) e. RR')
    mc = eqc(w, Aa, dst(w, Aa, [dst(w, Aa, [], 'fzfid', '%s e. Fin' % RA('a')), ca.mem('( 1 / a )', 'CC'), dst(w, Aam, [rm], 'recnd', '( 1 / m ) e. CC')], 'fsummulc2',
                            '( ( 1 / a ) x. sum_ m e. %s ( 1 / m ) ) = sum_ m e. %s ( ( 1 / a ) x. ( 1 / m ) )' % (RA('a'), RA('a'))))
    ale = ap(w, Aa, 'elfzle2', [w.s([], 'simpr', '( %s -> a e. %s )' % (Aa, R))], 'a <_ %s' % FX)
    ax = dst(w, Aa, [ca.mem('a', 'RR'), lift(w, flr, Aa), ca.mem('X', 'RR'), ale, lift(w, fll, Aa)], 'letrd', 'a <_ X')
    lmd = ap(w, Aa, 'lemuldiv', [ONE(w, Aa), ca.mem('X', 'RR'), J(w, Aa, ca.mem('a', 'RR'), ca.gt0('a'))], '( ( 1 x. a ) <_ X <-> 1 <_ %s )' % XA)
    xa1 = dst(w, Aa, [dst(w, Aa, [dst(w, Aa, [ca.mem('a', 'CC')], 'mullidd', '( 1 x. a ) = a'), ax], 'eqbrtrd', '( 1 x. a ) <_ X'), lmd], 'mpbid', '1 <_ %s' % XA)
    hb = ap(w, Aa, 'harmonicubnd', [J(w, Aa, ca.mem(XA, 'RR'), xa1)], 'sum_ m e. %s ( 1 / m ) <_ ( ( log ` %s ) + 1 )' % (RA('a'), XA))
    ld = dst(w, Aa, [ca.mem('X', 'RR+'), ca.mem('a', 'RR+')], 'relogdivd', '( log ` %s ) = ( %s - ( log ` a ) )' % (XA, LX))
    la0 = ap(w, Aa, 'logge0', [J(w, Aa, ca.mem('a', 'RR'), dst(w, Aa, [an], 'nnge1d', '1 <_ a'))], '0 <_ ( log ` a )')
    ca.leaf('( log ` a )', 'RR', ca.mem('( log ` a )', 'RR')); ca.leaf('( log ` %s )' % XA, 'RR', ca.mem('( log ` %s )' % XA, 'RR'))
    HS = 'sum_ m e. %s ( 1 / m )' % RA('a')
    ca.leaf(HS, 'RR', dst(w, Aa, [dst(w, Aa, [], 'fzfid', '%s e. Fin' % RA('a')), rm], 'fsumrecl', '%s e. RR' % HS))
    hb2 = linarith(w, Aa, [hb, ld, la0], '%s <_ %s' % (HS, L1), closure=ca)
    m1 = lemul(w, Aa, ca, hb2, '( 1 / a )')
    pera = dst(w, Aa, [eqt(w, Aa, s3, mc), m1], 'eqbrtrd', 'sum_ m e. %s ( 1 / ( a x. m ) ) <_ ( ( 1 / a ) x. %s )' % (RA('a'), L1))
    IS = 'sum_ m e. %s ( 1 / ( a x. m ) )' % RA('a')
    isr = dst(w, Aa, [dst(w, Aa, [], 'fzfid', '%s e. Fin' % RA('a')), dst(w, Aam, [cam.mem('( a x. m )', 'NN')], 'nnrecred', '( 1 / ( a x. m ) ) e. RR')], 'fsumrecl', '%s e. RR' % IS)
    s4 = dst(w, A, [rf, isr, ca.mem('( ( 1 / a ) x. %s )' % L1, 'RR'), pera], 'fsumle', 'sum_ a e. %s %s <_ sum_ a e. %s ( ( 1 / a ) x. %s )' % (R, IS, R, L1))
    ra = dst(w, Aa, [an], 'nnrecred', '( 1 / a ) e. RR')
    m2 = eqc(w, A, dst(w, A, [rf, dst(w, Aa, [ra], 'recnd', '( 1 / a ) e. CC'), c.mem(L1, 'CC')], 'fsummulc1', '( sum_ a e. %s ( 1 / a ) x. %s ) = sum_ a e. %s ( ( 1 / a ) x. %s )' % (R, L1, R, L1)))
    hbx = ap(w, A, 'harmonicubnd', [J(w, A, xr, x1)], 'sum_ a e. %s ( 1 / a ) <_ ( %s + 1 )' % (R, LX))
    HX = 'sum_ a e. %s ( 1 / a )' % R
    c.leaf(HX, 'RR', dst(w, A, [rf, ra], 'fsumrecl', '%s e. RR' % HX))
    c.leaf(LX, 'ge0', ap(w, A, 'logge0', [J(w, A, xr, x1)], '0 <_ %s' % LX))
    m3 = lemul(w, A, c, hbx, L1, side=1)
    sq = ringeqp(w, A, '( ( %s + 1 ) x. %s )' % (LX, L1), '( %s ^ 2 )' % L1, c)
    c.leaf('sum_ a e. %s %s' % (R, IS), 'RR', dst(w, A, [rf, isr], 'fsumrecl', 'sum_ a e. %s %s e. RR' % (R, IS)))
    c.leaf('sum_ a e. %s ( ( 1 / a ) x. %s )' % (R, L1), 'RR', dst(w, A, [rf, ca.mem('( ( 1 / a ) x. %s )' % L1, 'RR')], 'fsumrecl', 'sum_ a e. %s ( ( 1 / a ) x. %s ) e. RR' % (R, L1)))
    c.leaf('sum_ d e. %s ( %s / d )' % (R, TAU('d')), 'RR', dst(w, A, [rf, dst(w, Ad, [cd.mem(TAU('d'), 'RR'), cd.mem('d', 'RR'), cd.ne0('d')], 'redivcld', '( %s / d ) e. RR' % TAU('d'))], 'fsumrecl', 'sum_ d e. %s ( %s / d ) e. RR' % (R, TAU('d'))))
    c.leaf('sum_ d e. %s sum_ a e. %s ( 1 / d )' % (R, DV('d')), 'RR', dst(w, A, [rf, dst(w, Ad, [fi, lift(w, dst(w, Ad, [dn], 'nnrecred', '( 1 / d ) e. RR'), '( %s /\\ a e. %s )' % (Ad, DV('d')))], 'fsumrecl', 'sum_ a e. %s ( 1 / d ) e. RR' % DV('d'))], 'fsumrecl', 'sum_ d e. %s sum_ a e. %s ( 1 / d ) e. RR' % (R, DV('d'))))
    c.leaf('( %s ^ 2 )' % L1, 'RR', c.mem('( %s ^ 2 )' % L1, 'RR'))
    linarith(w, A, [e1, s2, s4, m2, m3, sq], 'sum_ d e. %s ( %s / d ) <_ ( %s ^ 2 )' % (R, TAU('d'), L1), closure=c, name='qed')
    return go(w)


def ld1tau2():
    w = W('ld1tau2', 'Lean ` sum_card_divisors_sq_le ` : ` sum_ ( n <_ x ) tau ( n ) ^ 2 <_ x ( 1 + log x ) ^ 3 ` by ` tau ( d m ) <_ tau ( d ) tau ( m ) ` and ~ dvdsflsumcom (~ ld1taumul , ~ ld1tau1 , ~ ld1taud ).')
    A = ante('ld1tau2'); P = parts(w, A); xr, x1 = P['X e. RR'], P['1 <_ X']
    c = Closure(w, A, {'X': [('RR', xr), ('ge1', x1)]})
    x0 = linarith(w, A, [x1], '0 <_ X', closure=c); c.leaf('X', 'ge0', x0)
    xrp = dst(w, A, [xr, linarith(w, A, [x1], '0 < X', closure=c)], 'elrpd', 'X e. RR+'); c.leaf('X', 'RR+', xrp)
    FX = '( |_ ` X )'; R = '( 1 ... %s )' % FX; LX = '( log ` X )'; L1 = '( 1 + %s )' % LX
    c.leaf(LX, 'RR', c.mem(LX, 'RR'))
    flr = ap(w, A, 'reflcl', [xr], '%s e. RR' % FX); fll = ap(w, A, 'flle', [xr], '%s <_ X' % FX)
    rf = dst(w, A, [], 'fzfid', '%s e. Fin' % R)
    An = '( %s /\\ n e. %s )' % (A, R)
    nn = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, R))], 'n e. NN')
    fi = ap(w, An, 'dvdsfi', [nn], '%s e. Fin' % DV('n'))
    cn = Closure(w, An, {'n': ('NN', nn)}); taufacts(w, An, nn, 'n', cn)
    tc = cn.mem(TAU('n'), 'CC')
    fc = ap(w, An, 'fsumconst', [fi, tc], 'sum_ d e. %s %s = ( %s x. %s )' % (DV('n'), TAU('n'), TAU('n'), TAU('n')))
    sq = dst(w, An, [tc], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (TAU('n'), TAU('n'), TAU('n')))
    e1 = dst(w, A, [eqt(w, An, sq, eqc(w, An, fc))], 'sumeq2dv', 'sum_ n e. %s ( %s ^ 2 ) = sum_ n e. %s sum_ d e. %s %s' % (R, TAU('n'), R, DV('n'), TAU('n')))
    cg, TDM = w.congr(TAU('n'), {'n': '( d x. m )'}, 'n = ( d x. m )', {'n': w.s([], 'id', '( n = ( d x. m ) -> n = ( d x. m ) )')})
    assert TDM == TAU('( d x. m )'), TDM
    And = '( %s /\\ ( n e. %s /\\ d e. %s ) )' % (A, R, DV('n'))
    nn2 = ap(w, And, 'elfznn', [w.s([], 'simprl', '( %s -> n e. %s )' % (And, R))], 'n e. NN')
    h3 = dst(w, And, [ap(w, And, 'hashcl', [ap(w, And, 'dvdsfi', [nn2], '%s e. Fin' % DV('n'))], '%s e. NN0' % TAU('n'))], 'nn0cnd', '%s e. CC' % TAU('n'))
    RD = lambda d: '( 1 ... ( |_ ` ( X / %s ) ) )' % d
    s2 = w.s([cg, xr, h3], 'dvdsflsumcom', '( %s -> sum_ n e. %s sum_ d e. %s %s = sum_ d e. %s sum_ m e. %s %s )' % (A, R, DV('n'), TAU('n'), R, RD('d'), TDM))
    Ad = '( %s /\\ d e. %s )' % (A, R)
    dn = ap(w, Ad, 'elfznn', [w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, R))], 'd e. NN')
    cd = Closure(w, Ad, {'d': ('NN', dn), 'X': [('RR', lift(w, xr, Ad)), ('ge0', lift(w, x0, Ad)), ('RR+', lift(w, xrp, Ad))]})
    cd.leaf(LX, 'RR', lift(w, c.mem(LX, 'RR'), Ad)); taufacts(w, Ad, dn, 'd', cd)
    Adm = '( %s /\\ m e. %s )' % (Ad, RD('d'))
    mn = ap(w, Adm, 'elfznn', [w.s([], 'simpr', '( %s -> m e. %s )' % (Adm, RD('d')))], 'm e. NN')
    tm = ap(w, Adm, 'ld1taumul', [J(w, Adm, lift(w, dn, Adm), mn)], '%s <_ ( %s x. %s )' % (TDM, TAU('d'), TAU('m')))
    cdm = Closure(w, Adm, {'d': ('NN', lift(w, dn, Adm)), 'm': ('NN', mn)})
    taufacts(w, Adm, cdm.mem('( d x. m )', 'NN'), '( d x. m )', cdm); taufacts(w, Adm, mn, 'm', cdm); cdm.leaf(TAU('d'), 'RR', lift(w, cd.mem(TAU('d'), 'RR'), Adm))
    rdf = dst(w, Ad, [], 'fzfid', '%s e. Fin' % RD('d'))
    fle1 = dst(w, Ad, [rdf, cdm.mem(TDM, 'RR'), cdm.mem('( %s x. %s )' % (TAU('d'), TAU('m')), 'RR'), tm], 'fsumle', 'sum_ m e. %s %s <_ sum_ m e. %s ( %s x. %s )' % (RD('d'), TDM, RD('d'), TAU('d'), TAU('m')))
    SM = 'sum_ m e. %s %s' % (RD('d'), TAU('m'))
    mc = eqc(w, Ad, dst(w, Ad, [rdf, cd.mem(TAU('d'), 'CC'), cdm.mem(TAU('m'), 'CC')], 'fsummulc2', '( %s x. %s ) = sum_ m e. %s ( %s x. %s )' % (TAU('d'), SM, RD('d'), TAU('d'), TAU('m'))))
    XD = '( X / d )'
    dle = ap(w, Ad, 'elfzle2', [w.s([], 'simpr', '( %s -> d e. %s )' % (Ad, R))], 'd <_ %s' % FX)
    dx = dst(w, Ad, [cd.mem('d', 'RR'), lift(w, flr, Ad), cd.mem('X', 'RR'), dle, lift(w, fll, Ad)], 'letrd', 'd <_ X')
    lmd = ap(w, Ad, 'lemuldiv', [ONE(w, Ad), cd.mem('X', 'RR'), J(w, Ad, cd.mem('d', 'RR'), cd.gt0('d'))], '( ( 1 x. d ) <_ X <-> 1 <_ %s )' % XD)
    xd1 = dst(w, Ad, [dst(w, Ad, [dst(w, Ad, [cd.mem('d', 'CC')], 'mullidd', '( 1 x. d ) = d'), dx], 'eqbrtrd', '( 1 x. d ) <_ X'), lmd], 'mpbid', '1 <_ %s' % XD)
    t1 = ap(w, Ad, 'ld1tau1', [J(w, Ad, cd.mem(XD, 'RR'), xd1)], '%s <_ ( %s x. ( 1 + ( log ` %s ) ) )' % (SM, XD, XD))
    ld = dst(w, Ad, [cd.mem('X', 'RR+'), cd.mem('d', 'RR+')], 'relogdivd', '( log ` %s ) = ( %s - ( log ` d ) )' % (XD, LX))
    ld0 = ap(w, Ad, 'logge0', [J(w, Ad, cd.mem('d', 'RR'), dst(w, Ad, [dn], 'nnge1d', '1 <_ d'))], '0 <_ ( log ` d )')
    for e_ in ('( log ` d )', '( log ` %s )' % XD):
        cd.leaf(e_, 'RR', cd.mem(e_, 'RR'))
    cd.leaf(XD, 'RR', cd.mem(XD, 'RR')); cd.leaf(XD, 'ge0', cd.ge0(XD))
    cd.leaf(SM, 'RR', dst(w, Ad, [rdf, cdm.mem(TAU('m'), 'RR')], 'fsumrecl', '%s e. RR' % SM))
    l1 = linarith(w, Ad, [ld, ld0], '( 1 + ( log ` %s ) ) <_ %s' % (XD, L1), closure=cd)
    b1 = dst(w, Ad, [cd.mem(SM, 'RR'), cd.mem('( %s x. ( 1 + ( log ` %s ) ) )' % (XD, XD), 'RR'), cd.mem('( %s x. %s )' % (XD, L1), 'RR'), t1, lemul(w, Ad, cd, l1, XD)], 'letrd', '%s <_ ( %s x. %s )' % (SM, XD, L1))
    b2 = lemul(w, Ad, cd, b1, TAU('d'))
    dr1 = dst(w, Ad, [cd.mem('X', 'CC'), cd.mem('d', 'CC'), cd.ne0('d')], 'divrecd', '%s = ( X x. ( 1 / d ) )' % XD)
    dr2 = dst(w, Ad, [cd.mem(TAU('d'), 'CC'), cd.mem('d', 'CC'), cd.ne0('d')], 'divrecd', '( %s / d ) = ( %s x. ( 1 / d ) )' % (TAU('d'), TAU('d')))
    cd.leaf('( 1 / d )', 'RR', cd.mem('( 1 / d )', 'RR'))
    rg = ringeq(w, Ad, '( %s x. ( ( X x. ( 1 / d ) ) x. %s ) )' % (TAU('d'), L1), '( ( X x. %s ) x. ( %s x. ( 1 / d ) ) )' % (L1, TAU('d')), cd)
    eqr = eqt(w, Ad, eqt(w, Ad, dst(w, Ad, [dst(w, Ad, [dr1], 'oveq1d', '( %s x. %s ) = ( ( X x. ( 1 / d ) ) x. %s )' % (XD, L1, L1))], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( ( X x. ( 1 / d ) ) x. %s ) )' % (TAU('d'), XD, L1, TAU('d'), L1)), rg),
              dst(w, Ad, [eqc(w, Ad, dr2)], 'oveq2d', '( ( X x. %s ) x. ( %s x. ( 1 / d ) ) ) = ( ( X x. %s ) x. ( %s / d ) )' % (L1, TAU('d'), L1, TAU('d'))))
    smr = dst(w, Ad, [rdf, cdm.mem(TDM, 'RR')], 'fsumrecl', 'sum_ m e. %s %s e. RR' % (RD('d'), TDM))
    smr2 = dst(w, Ad, [rdf, cdm.mem('( %s x. %s )' % (TAU('d'), TAU('m')), 'RR')], 'fsumrecl', 'sum_ m e. %s ( %s x. %s ) e. RR' % (RD('d'), TAU('d'), TAU('m')))
    ch1 = dst(w, Ad, [smr, smr2, cd.mem('( %s x. ( %s x. %s ) )' % (TAU('d'), XD, L1), 'RR'), fle1, dst(w, Ad, [mc, b2], 'eqbrtrd', 'sum_ m e. %s ( %s x. %s ) <_ ( %s x. ( %s x. %s ) )' % (RD('d'), TAU('d'), TAU('m'), TAU('d'), XD, L1))], 'letrd',
              'sum_ m e. %s %s <_ ( %s x. ( %s x. %s ) )' % (RD('d'), TDM, TAU('d'), XD, L1))
    perd = dst(w, Ad, [ch1, eqr], 'breqtrd', 'sum_ m e. %s %s <_ ( ( X x. %s ) x. ( %s / d ) )' % (RD('d'), TDM, L1, TAU('d')))
    s4 = dst(w, A, [rf, smr, cd.mem('( ( X x. %s ) x. ( %s / d ) )' % (L1, TAU('d')), 'RR'), perd], 'fsumle', 'sum_ d e. %s sum_ m e. %s %s <_ sum_ d e. %s ( ( X x. %s ) x. ( %s / d ) )' % (R, RD('d'), TDM, R, L1, TAU('d')))
    m2 = eqc(w, A, dst(w, A, [rf, c.mem('( X x. %s )' % L1, 'CC'), cd.mem('( %s / d )' % TAU('d'), 'CC')], 'fsummulc2', '( ( X x. %s ) x. sum_ d e. %s ( %s / d ) ) = sum_ d e. %s ( ( X x. %s ) x. ( %s / d ) )' % (L1, R, TAU('d'), R, L1, TAU('d'))))
    td = ap(w, A, 'ld1taud', [J(w, A, xr, x1)], concl('ld1taud'))
    c.leaf(LX, 'ge0', ap(w, A, 'logge0', [J(w, A, xr, x1)], '0 <_ %s' % LX))
    SD = 'sum_ d e. %s ( %s / d )' % (R, TAU('d'))
    c.leaf(SD, 'RR', dst(w, A, [rf, cd.mem('( %s / d )' % TAU('d'), 'RR')], 'fsumrecl', '%s e. RR' % SD))
    m3 = lemul(w, A, c, td, '( X x. %s )' % L1)
    cube = ringeqp(w, A, '( ( X x. %s ) x. ( %s ^ 2 ) )' % (L1, L1), '( X x. ( %s ^ 3 ) )' % L1, c)
    c.leaf('sum_ d e. %s sum_ m e. %s %s' % (R, RD('d'), TDM), 'RR', dst(w, A, [rf, smr], 'fsumrecl', 'sum_ d e. %s sum_ m e. %s %s e. RR' % (R, RD('d'), TDM)))
    c.leaf('sum_ d e. %s ( ( X x. %s ) x. ( %s / d ) )' % (R, L1, TAU('d')), 'RR', dst(w, A, [rf, cd.mem('( ( X x. %s ) x. ( %s / d ) )' % (L1, TAU('d')), 'RR')], 'fsumrecl', 'sum_ d e. %s ( ( X x. %s ) x. ( %s / d ) ) e. RR' % (R, L1, TAU('d'))))
    c.leaf('sum_ n e. %s ( %s ^ 2 )' % (R, TAU('n')), 'RR', dst(w, A, [rf, dst(w, An, [cn.mem(TAU('n'), 'RR')], 'resqcld', '( %s ^ 2 ) e. RR' % TAU('n'))], 'fsumrecl', 'sum_ n e. %s ( %s ^ 2 ) e. RR' % (R, TAU('n'))))
    Anx = '( %s /\\ d e. %s )' % (An, DV('n'))
    inner = dst(w, An, [fi, lift(w, cn.mem(TAU('n'), 'RR'), Anx)], 'fsumrecl', 'sum_ d e. %s %s e. RR' % (DV('n'), TAU('n')))
    c.leaf('sum_ n e. %s sum_ d e. %s %s' % (R, DV('n'), TAU('n')), 'RR', dst(w, A, [rf, inner], 'fsumrecl', 'sum_ n e. %s sum_ d e. %s %s e. RR' % (R, DV('n'), TAU('n'))))
    c.leaf('( X x. ( %s ^ 3 ) )' % L1, 'RR', c.mem('( X x. ( %s ^ 3 ) )' % L1, 'RR')); c.leaf('( %s ^ 2 )' % L1, 'RR', c.mem('( %s ^ 2 )' % L1, 'RR'))
    linarith(w, A, [e1, s2, s4, m2, m3, cube], 'sum_ n e. %s ( %s ^ 2 ) <_ ( X x. ( %s ^ 3 ) )' % (R, TAU('n'), L1), closure=c, name='qed')
    return go(w)


if __name__ == '__main__':
    for lab in ['ld1lhalf', 'ld1taumul', 'ld1taud', 'ld1tau2']:
        if want(lab):
            if not globals()[lab]():
                sys.exit(1)
