"""Sortie C6 section B, part 2: the two Lipschitz bounds of the quotient
function at P (holqdq, holqdq2)."""
import sys, os; sys.path.insert(0, os.path.dirname(__file__)); from c6_lib import *

XCND = '( X e. D /\\ X =/= P /\\ ( abs ` ( X - P ) ) <_ ( R / 2 ) )'
A0 = '( %s /\\ %s )' % (CTX, XCND)
AX = '( abs ` ( X - P ) )'
XN = '( ( X - P ) ^ N )'
X1 = '( ( X - P ) ^ ( N + 1 ) )'
LHSX = '( %s x. ( F ` X ) )' % TPI
CN = '( C ` N )'; C1 = '( C ` ( N + 1 ) )'
G1 = '( %s ` ( N + 1 ) )' % GMAP('X')
G2 = '( %s ` ( N + 2 ) )' % GMAP('X')
G11 = '( %s ` ( ( N + 1 ) + 1 ) )' % GMAP('X')
QX = '( Q ` X )'; QPV = '( Q ` P )'
TP2 = '( 2 x. _pi )'
R1 = '( R ^ ( N + 1 ) )'; R2 = '( R ^ ( N + 2 ) )'; R11 = '( R ^ ( ( N + 1 ) + 1 ) )'
BASEX = BASEV('X')


def qsetup(w):
    d = {}
    ctx = w.s([], 'simpl', '( %s -> %s )' % (A0, CTX))
    hrm = w.s([ctx, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HRM))
    d.update(hrmctx(w, A0, hrm))
    nz = w.s([ctx, w.inst('simpr')], 'syl', '( %s -> ( N e. NN /\\ %s ) )' % (A0, ZER))
    d['nn'] = nn = w.s([nz, w.inst('simpl')], 'syl', '( %s -> N e. NN )' % A0)
    d['hn'] = hn = w.s([nn], 'nnnn0d', '( %s -> N e. NN0 )' % A0)
    d['zer'] = zer = w.s([nz, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, ZER))
    d['ctx'] = ctx
    xs = w.s([], 'simpr', '( %s -> %s )' % (A0, XCND))
    d['xd'] = xd = w.s([xs, w.inst('simp1')], 'syl', '( %s -> X e. D )' % A0)
    d['xne'] = xne = w.s([xs, w.inst('simp2')], 'syl', '( %s -> X =/= P )' % A0)
    d['xle'] = xle = w.s([xs, w.inst('simp3')], 'syl', '( %s -> %s <_ ( R / 2 ) )' % (A0, AX))
    d['xc'] = xc = w.s([d['dss'], xd], 'sseldd', '( %s -> X e. CC )' % A0)
    d['xp'] = xp = w.s([xc, d['pc']], 'subcld', '( %s -> ( X - P ) e. CC )' % A0)
    d['xpne'] = xpne = w.s([xc, d['pc'], xne], 'subne0d', '( %s -> ( X - P ) =/= 0 )' % A0)
    d['ax'] = ax = w.s([xp], 'abscld', '( %s -> %s e. RR )' % (A0, AX))
    hr = w.s([d['Rrp']], 'rphalfcld', '( %s -> ( R / 2 ) e. RR+ )' % A0)
    ltr = w.s([ax, w.s([hr], 'rpred', '( %s -> ( R / 2 ) e. RR )' % A0), d['rr'], xle, w.s([d['Rrp'], w.inst('rphalflt')], 'syl', '( %s -> ( R / 2 ) < R )' % A0)], 'lelttrd',
              '( %s -> %s < R )' % (A0, AX))
    intx = w.s([w.s([d['ab'], d['it'], d['rbd']], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (A0, AB, INTP, RBDP)), w.s([xc, ltr], 'jca', '( %s -> ( X e. CC /\\ %s < R ) )' % (A0, AX)), w.inst('holdisint')], 'syl2anc',
               '( %s -> %s )' % (A0, INTV('X')))
    pnx = w.s([xne], 'necomd', '( %s -> P =/= X )' % A0)
    d['basex'] = basex = w.s([d['ab'], w.s([d['it'], intx, pnx], '3jca', '( %s -> ( %s /\\ %s /\\ P =/= X ) )' % (A0, INTP, INTV('X'))), d['holo']], '3jca', '( %s -> %s )' % (A0, BASEX))
    d['bn'] = bn = w.s([basex, hn], 'jca', '( %s -> ( %s /\\ N e. NN0 ) )' % (A0, BASEX))
    d['aqv'] = w.s([bn, zer], 'jca', '( %s -> ( ( %s /\\ N e. NN0 ) /\\ %s ) )' % (A0, BASEX, ZER))
    d['gG'], d['gH'] = famsteps(w, 'X')
    d['tpic'], d['tne'] = tpisteps(w, A0)
    d['tp2rp'] = w.s([closed(w, A0, '2rp', '2 e. RR+'), closed(w, A0, 'pirp', '_pi e. RR+')], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, TP2))
    # holrmq's antecedent
    d['arm'] = w.s([bn, w.s([w.s([d['rbd'], d['rpos']], 'jca', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP)), xle], 'jca', '( %s -> ( ( %s /\\ 0 < R ) /\\ %s <_ ( R / 2 ) ) )' % (A0, RBDP, AX)),
                    w.s([d['mr'], d['alf']], 'jca', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))], '3jca',
                   '( %s -> ( ( %s /\\ N e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ %s <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) )' % (A0, BASEX, RBDP, AX, ALF))
    # values of Q
    qvz0 = w.s(['1', '2'], 'holqvz', '( ( %s /\\ ( X e. D /\\ X =/= P ) ) -> %s = ( ( F ` X ) / %s ) )' % (CTX, QX, XN))
    d['qx'] = qx = w.s([w.s([ctx, w.s([xd, xne], 'jca', '( %s -> ( X e. D /\\ X =/= P ) )' % A0)], 'jca', '( %s -> ( %s /\\ ( X e. D /\\ X =/= P ) ) )' % (A0, CTX)), qvz0], 'syl',
                       '( %s -> %s = ( ( F ` X ) / %s ) )' % (A0, QX, XN))
    qvp0 = w.s(['1', '2'], 'holqvp', '( %s -> %s = %s )' % (CTX, QPV, QP))
    d['qp'] = qp = w.s([ctx, qvp0], 'syl', '( %s -> %s = %s )' % (A0, QPV, QP))
    d['fx'] = fx = w.s([d['ff'], xd], 'ffvelcdmd', '( %s -> ( F ` X ) e. CC )' % A0)
    d['xn'] = xn = w.s([xp, hn], 'expcld', '( %s -> %s e. CC )' % (A0, XN))
    d['xnne'] = xnne = w.s([xp, xpne, w.s([hn], 'nn0zd', '( %s -> N e. ZZ )' % A0), w.inst('expne0i')], 'syl3anc', '( %s -> %s =/= 0 )' % (A0, XN))
    d['cn'] = cn = ccl(w, A0, 'N', hn, d['abih'], '1')
    d['qxc'] = qxc = w.s([qx, w.s([fx, xn, xnne], 'divcld', '( %s -> ( ( F ` X ) / %s ) e. CC )' % (A0, XN))], 'eqeltrd', '( %s -> %s e. CC )' % (A0, QX))
    # TPI x. QX = LHSX / XN
    tq = w.s([w.s([qx], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( ( F ` X ) / %s ) ) )' % (A0, TPI, QX, TPI, XN)),
              w.s([w.s([d['tpic'], fx, xn, xnne], 'divassd', '( %s -> ( ( %s x. ( F ` X ) ) / %s ) = ( %s x. ( ( F ` X ) / %s ) ) )' % (A0, TPI, XN, TPI, XN))], 'eqcomd',
                  '( %s -> ( %s x. ( ( F ` X ) / %s ) ) = ( %s / %s ) )' % (A0, TPI, XN, LHSX, XN))], 'eqtrd', '( %s -> ( %s x. %s ) = ( %s / %s ) )' % (A0, TPI, QX, LHSX, XN))
    # QX - QP = ( ( LHSX / XN ) - CN ) / TPI
    k1 = w.s([w.s([d['tpic'], qxc], 'mulcld', '( %s -> ( %s x. %s ) e. CC )' % (A0, TPI, QX)), cn, d['tpic'], d['tne']], 'divsubdird',
             '( %s -> ( ( ( %s x. %s ) - %s ) / %s ) = ( ( ( %s x. %s ) / %s ) - ( %s / %s ) ) )' % (A0, TPI, QX, CN, TPI, TPI, QX, TPI, CN, TPI))
    k2 = w.s([w.s([qxc, d['tpic'], d['tne']], 'divcan3d', '( %s -> ( ( %s x. %s ) / %s ) = %s )' % (A0, TPI, QX, TPI, QX)), w.s([qp], 'eqcomd', '( %s -> %s = %s )' % (A0, QP, QPV))], 'oveq12d',
             '( %s -> ( ( ( %s x. %s ) / %s ) - ( %s / %s ) ) = ( %s - %s ) )' % (A0, TPI, QX, TPI, CN, TPI, QX, QPV))
    k3 = w.s([w.s([k1, k2], 'eqtrd', '( %s -> ( ( ( %s x. %s ) - %s ) / %s ) = ( %s - %s ) )' % (A0, TPI, QX, CN, TPI, QX, QPV))], 'eqcomd',
             '( %s -> ( %s - %s ) = ( ( ( %s x. %s ) - %s ) / %s ) )' % (A0, QX, QPV, TPI, QX, CN, TPI))
    d['key'] = w.s([k3, w.s([w.s([tq], 'oveq1d', '( %s -> ( ( %s x. %s ) - %s ) = ( ( %s / %s ) - %s ) )' % (A0, TPI, QX, CN, LHSX, XN, CN))], 'oveq1d',
                             '( %s -> ( ( ( %s x. %s ) - %s ) / %s ) = ( ( ( %s / %s ) - %s ) / %s ) )' % (A0, TPI, QX, CN, TPI, LHSX, XN, CN, TPI))], 'eqtrd',
                   '( %s -> ( %s - %s ) = ( ( ( %s / %s ) - %s ) / %s ) )' % (A0, QX, QPV, LHSX, XN, CN, TPI))
    d['dif'] = w.s([qxc, w.s([qp, qpcl(w, A0, d, '1')[0]], 'eqeltrd', '( %s -> %s e. CC )' % (A0, QPV))], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (A0, QX, QPV))
    return d


def divtp(w, d, V, VC, bnd, RR_, RRC, RRNE, KDIV):
    """from bnd: ( A0 -> ( abs ` V ) <_ ( ( K / RR_ ) x. AX ) ) derive
    ( A0 -> ( abs ` ( V / TPI ) ) <_ ( ( K / ( TP2 x. RR_ ) ) x. AX ) ); VC: V e. CC;
    RRC/RRNE: RR_ e. CC / =/= 0 steps"""
    absq = w.s([VC, d['tpic'], d['tne']], 'absdivd', '( %s -> ( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) ) )' % (A0, V, TPI, V, TPI))
    absq2 = w.s([absq, w.s([closed(w, A0, 'abstpi', '( abs ` %s ) = %s' % (TPI, TP2))], 'oveq2d', '( %s -> ( ( abs ` %s ) / ( abs ` %s ) ) = ( ( abs ` %s ) / %s ) )' % (A0, V, TPI, V, TP2))], 'eqtrd',
               '( %s -> ( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / %s ) )' % (A0, V, TPI, V, TP2))
    av = w.s([VC], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, V))
    kr, k0 = d['kr'], d['k0']
    kc = w.s([kr], 'recnd', '( %s -> %s e. CC )' % (A0, KK))
    kq = w.s([kc, RRC, RRNE], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, KK, RR_))
    Y = '( ( %s / %s ) x. %s )' % (KK, RR_, AX)
    yr = w.s([kqr_(w, kr, RR_, d), d['ax']], 'remulcld', '( %s -> %s e. RR )' % (A0, Y))
    le = w.s([bnd, w.s([av, yr, d['tp2rp']], 'lediv1d', '( %s -> ( ( abs ` %s ) <_ %s <-> ( ( abs ` %s ) / %s ) <_ ( %s / %s ) ) )' % (A0, V, Y, V, TP2, Y, TP2))], 'mpbid',
             '( %s -> ( ( abs ` %s ) / %s ) <_ ( %s / %s ) )' % (A0, V, TP2, Y, TP2))
    tc = w.s([w.s([d['tp2rp']], 'rpred', '( %s -> %s e. RR )' % (A0, TP2))], 'recnd', '( %s -> %s e. CC )' % (A0, TP2))
    tne = w.s([d['tp2rp']], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, TP2))
    axc = w.s([d['ax']], 'recnd', '( %s -> %s e. CC )' % (A0, AX))
    r1 = w.s([kq, axc, tc, tne], 'div23d', '( %s -> ( %s / %s ) = ( ( ( %s / %s ) / %s ) x. %s ) )' % (A0, Y, TP2, KK, RR_, TP2, AX))
    r2 = w.s([kc, RRC, tc, RRNE, tne], 'divdiv1d', '( %s -> ( ( %s / %s ) / %s ) = ( %s / ( %s x. %s ) ) )' % (A0, KK, RR_, TP2, KK, RR_, TP2))
    r3 = w.s([w.s([RRC, tc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A0, RR_, TP2, TP2, RR_))], 'oveq2d', '( %s -> ( %s / ( %s x. %s ) ) = ( %s / ( %s x. %s ) ) )' % (A0, KK, RR_, TP2, KK, TP2, RR_))
    r4 = w.s([r1, w.s([w.s([r2, r3], 'eqtrd', '( %s -> ( ( %s / %s ) / %s ) = %s )' % (A0, KK, RR_, TP2, KDIV))], 'oveq1d', '( %s -> ( ( ( %s / %s ) / %s ) x. %s ) = ( %s x. %s ) )' % (A0, KK, RR_, TP2, AX, KDIV, AX))], 'eqtrd',
             '( %s -> ( %s / %s ) = ( %s x. %s ) )' % (A0, Y, TP2, KDIV, AX))
    return w.s([absq2, w.s([le, r4], 'breqtrd', '( %s -> ( ( abs ` %s ) / %s ) <_ ( %s x. %s ) )' % (A0, V, TP2, KDIV, AX))], 'eqbrtrd',
               '( %s -> ( abs ` ( %s / %s ) ) <_ ( %s x. %s ) )' % (A0, V, TPI, KDIV, AX))


def kqr_(w, kr, RR_, d):
    return w.s([kr, d['rrrp'][RR_]], 'rerpdivcld', '( %s -> ( %s / %s ) e. RR )' % (A0, KK, RR_))


if __name__ == '__main__':
    # ---- holqdq -----------------------------------------------------------------
    w = W('holqdq', 'The quotient function is Lipschitz at the centre: the distance from Q X to Q P is bounded by a constant times the distance from X to P, within half the distance to the frame.')
    hyp(w, '1', 'holqdq.c', CDEF)
    hyp(w, '2', 'holqdq.q', QDEF)
    d = qsetup(w)
    geo, reals = geo_of_int(w, A0, d)
    d['kr'], d['k0'] = kreal(w, A0, d, geo, reals)
    hn1 = w.s([d['hn'], w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
    r1rp = w.s([d['Rrp'], w.s([hn1], 'nn0zd', '( %s -> ( N + 1 ) e. ZZ )' % A0)], 'rpexpcld', '( %s -> %s e. RR+ )' % (A0, R1))
    d['rrrp'] = {R1: r1rp}
    r1c = w.s([w.s([r1rp], 'rpred', '( %s -> %s e. RR )' % (A0, R1))], 'recnd', '( %s -> %s e. CC )' % (A0, R1))
    r1ne = w.s([r1rp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, R1))
    qv = w.s([d['aqv'], w.s([d['gG'], d['gH'], '1'], 'holqval', '( ( ( %s /\\ N e. NN0 ) /\\ %s ) -> ( %s / %s ) = ( %s + ( %s / %s ) ) )' % (BASEX, ZER, LHSX, XN, CN, G1, XN))], 'syl',
             '( %s -> ( %s / %s ) = ( %s + ( %s / %s ) ) )' % (A0, LHSX, XN, CN, G1, XN))
    g1cc = gclv(w, A0, '( N + 1 )', hn1, d['basex'], d['gG'], 'X')
    q1 = w.s([d['cn'], w.s([g1cc, d['xn'], d['xnne']], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, G1, XN))], 'pncan2d', '( %s -> ( ( %s + ( %s / %s ) ) - %s ) = ( %s / %s ) )' % (A0, CN, G1, XN, CN, G1, XN))
    num = w.s([w.s([qv], 'oveq1d', '( %s -> ( ( %s / %s ) - %s ) = ( ( %s + ( %s / %s ) ) - %s ) )' % (A0, LHSX, XN, CN, CN, G1, XN, CN)), q1], 'eqtrd', '( %s -> ( ( %s / %s ) - %s ) = ( %s / %s ) )' % (A0, LHSX, XN, CN, G1, XN))
    key2 = w.s([d['key'], w.s([num], 'oveq1d', '( %s -> ( ( ( %s / %s ) - %s ) / %s ) = ( ( %s / %s ) / %s ) )' % (A0, LHSX, XN, CN, TPI, G1, XN, TPI))], 'eqtrd',
               '( %s -> ( %s - %s ) = ( ( %s / %s ) / %s ) )' % (A0, QX, QPV, G1, XN, TPI))
    rmq = w.s([d['arm'], w.s([d['gG']], 'holrmq', '( ( ( %s /\\ N e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ %s <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) -> ( abs ` ( %s / %s ) ) <_ ( ( %s / %s ) x. %s ) )' % (BASEX, RBDP, AX, ALF, G1, XN, KK, R1, AX))], 'syl',
              '( %s -> ( abs ` ( %s / %s ) ) <_ ( ( %s / %s ) x. %s ) )' % (A0, G1, XN, KK, R1, AX))
    KD = '( %s / ( %s x. %s ) )' % (KK, TP2, R1)
    fin = divtp(w, d, '( %s / %s )' % (G1, XN), w.s([g1cc, d['xn'], d['xnne']], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, G1, XN)), rmq, R1, r1c, r1ne, KD)
    w.qed([w.s([key2], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` ( ( %s / %s ) / %s ) ) )' % (A0, QX, QPV, G1, XN, TPI)), fin], 'eqbrtrd',
          '( %s -> ( abs ` ( %s - %s ) ) <_ ( %s x. %s ) )' % (A0, QX, QPV, KD, AX))
    run1(w, h=True)

    # ---- holqdq2 -----------------------------------------------------------------
    w = W('holqdq2', 'The difference quotient of the quotient function at the centre is within a constant times the distance from X to P of the ( N + 1 )-th Taylor coefficient over 2 pi i.')
    hyp(w, '1', 'holqdq2.c', CDEF)
    hyp(w, '2', 'holqdq2.q', QDEF)
    d = qsetup(w)
    geo, reals = geo_of_int(w, A0, d)
    d['kr'], d['k0'] = kreal(w, A0, d, geo, reals)
    hn1 = w.s([d['hn'], w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % A0)
    hn2 = w.s([hn1, w.inst('peano2nn0')], 'syl', '( %s -> ( ( N + 1 ) + 1 ) e. NN0 )' % A0)
    a12 = w.s([w.s([d['hn']], 'nn0cnd', '( %s -> N e. CC )' % A0), w.inst('add1p1')], 'syl', '( %s -> ( ( N + 1 ) + 1 ) = ( N + 2 ) )' % A0)
    r2rp = w.s([d['Rrp'], w.s([w.s([a12, hn2], 'eqeltrrd', '( %s -> ( N + 2 ) e. NN0 )' % A0)], 'nn0zd', '( %s -> ( N + 2 ) e. ZZ )' % A0)], 'rpexpcld', '( %s -> %s e. RR+ )' % (A0, R2))
    d['rrrp'] = {R2: r2rp}
    r2c = w.s([w.s([r2rp], 'rpred', '( %s -> %s e. RR )' % (A0, R2))], 'recnd', '( %s -> %s e. CC )' % (A0, R2))
    r2ne = w.s([r2rp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, R2))
    DQ = '( ( %s - %s ) / ( X - P ) )' % (QX, QPV)
    QD0 = '( ( ( %s / %s ) - %s ) / ( X - P ) )' % (LHSX, XN, CN)
    qv2 = w.s([d['aqv'], w.s([d['gG'], d['gH'], '1'], 'holqval2', '( ( ( %s /\\ N e. NN0 ) /\\ %s ) -> %s = ( %s + ( %s / %s ) ) )' % (BASEX, ZER, QD0, C1, G2, X1))], 'syl',
              '( %s -> %s = ( %s + ( %s / %s ) ) )' % (A0, QD0, C1, G2, X1))
    nm = w.s([w.s([w.s([d['tpic'], d['fx']], 'mulcld', '( %s -> %s e. CC )' % (A0, LHSX)), d['xn'], d['xnne']], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, LHSX, XN)), d['cn']], 'subcld',
             '( %s -> ( ( %s / %s ) - %s ) e. CC )' % (A0, LHSX, XN, CN))
    d32 = w.s([nm, d['tpic'], d['xp'], d['tne'], d['xpne']], 'divdiv32d', '( %s -> ( ( ( ( %s / %s ) - %s ) / %s ) / ( X - P ) ) = ( %s / %s ) )' % (A0, LHSX, XN, CN, TPI, QD0, TPI))
    dq1 = w.s([w.s([d['key']], 'oveq1d', '( %s -> %s = ( ( ( ( %s / %s ) - %s ) / %s ) / ( X - P ) ) )' % (A0, DQ, LHSX, XN, CN, TPI)), d32], 'eqtrd', '( %s -> %s = ( %s / %s ) )' % (A0, DQ, QD0, TPI))
    c1 = ccl(w, A0, '( N + 1 )', hn1, d['abih'], '1')
    x1 = w.s([d['xp'], hn1], 'expcld', '( %s -> %s e. CC )' % (A0, X1))
    x1ne = w.s([d['xp'], d['xpne'], w.s([hn1], 'nn0zd', '( %s -> ( N + 1 ) e. ZZ )' % A0), w.inst('expne0i')], 'syl3anc', '( %s -> %s =/= 0 )' % (A0, X1))
    K2 = '( ( N + 1 ) + 1 )'
    g2c = w.s([w.s([a12], 'fveq2d', '( %s -> %s = %s )' % (A0, G11, G2)), gclv(w, A0, K2, hn2, d['basex'], d['gG'], 'X')], 'eqeltrrd', '( %s -> %s e. CC )' % (A0, G2))
    g2q = w.s([g2c, x1, x1ne], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, G2, X1))
    dd = w.s([c1, g2q, d['tpic'], d['tne']], 'divdird', '( %s -> ( ( %s + ( %s / %s ) ) / %s ) = ( ( %s / %s ) + ( ( %s / %s ) / %s ) ) )' % (A0, C1, G2, X1, TPI, C1, TPI, G2, X1, TPI))
    dq2 = w.s([dq1, w.s([w.s([qv2], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s + ( %s / %s ) ) / %s ) )' % (A0, QD0, TPI, C1, G2, X1, TPI)), dd], 'eqtrd',
                        '( %s -> ( %s / %s ) = ( ( %s / %s ) + ( ( %s / %s ) / %s ) ) )' % (A0, QD0, TPI, C1, TPI, G2, X1, TPI))], 'eqtrd',
              '( %s -> %s = ( ( %s / %s ) + ( ( %s / %s ) / %s ) ) )' % (A0, DQ, C1, TPI, G2, X1, TPI))
    c1q = w.s([c1, d['tpic'], d['tne']], 'divcld', '( %s -> ( %s / %s ) e. CC )' % (A0, C1, TPI))
    g2qq = w.s([g2q, d['tpic'], d['tne']], 'divcld', '( %s -> ( ( %s / %s ) / %s ) e. CC )' % (A0, G2, X1, TPI))
    dif = w.s([w.s([dq2], 'oveq1d', '( %s -> ( %s - ( %s / %s ) ) = ( ( ( %s / %s ) + ( ( %s / %s ) / %s ) ) - ( %s / %s ) ) )' % (A0, DQ, C1, TPI, C1, TPI, G2, X1, TPI, C1, TPI)),
               w.s([c1q, g2qq], 'pncan2d', '( %s -> ( ( ( %s / %s ) + ( ( %s / %s ) / %s ) ) - ( %s / %s ) ) = ( ( %s / %s ) / %s ) )' % (A0, C1, TPI, G2, X1, TPI, C1, TPI, G2, X1, TPI))], 'eqtrd',
              '( %s -> ( %s - ( %s / %s ) ) = ( ( %s / %s ) / %s ) )' % (A0, DQ, C1, TPI, G2, X1, TPI))
    # holrmq at N + 1
    arm1 = w.s([w.s([d['basex'], hn1], 'jca', '( %s -> ( %s /\\ ( N + 1 ) e. NN0 ) )' % (A0, BASEX)), w.s([d['arm'], w.inst('simp2')], 'syl', '( %s -> ( ( %s /\\ 0 < R ) /\\ %s <_ ( R / 2 ) ) )' % (A0, RBDP, AX)),
                w.s([d['arm'], w.inst('simp3')], 'syl', '( %s -> ( M e. RR /\\ %s ) )' % (A0, ALF))], '3jca',
               '( %s -> ( ( %s /\\ ( N + 1 ) e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ %s <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) )' % (A0, BASEX, RBDP, AX, ALF))
    rmq0 = w.s([d['gG']], 'holrmq', '( ( ( %s /\\ ( N + 1 ) e. NN0 ) /\\ ( ( %s /\\ 0 < R ) /\\ %s <_ ( R / 2 ) ) /\\ ( M e. RR /\\ %s ) ) -> ( abs ` ( %s / %s ) ) <_ ( ( %s / %s ) x. %s ) )' % (BASEX, RBDP, AX, ALF, G11, X1, KK, R11, AX))
    rmq1 = w.s([arm1, rmq0], 'syl', '( %s -> ( abs ` ( %s / %s ) ) <_ ( ( %s / %s ) x. %s ) )' % (A0, G11, X1, KK, R11, AX))
    e1 = w.s([w.s([w.s([a12], 'fveq2d', '( %s -> %s = %s )' % (A0, G11, G2))], 'oveq1d', '( %s -> ( %s / %s ) = ( %s / %s ) )' % (A0, G11, X1, G2, X1))], 'fveq2d',
             '( %s -> ( abs ` ( %s / %s ) ) = ( abs ` ( %s / %s ) ) )' % (A0, G11, X1, G2, X1))
    e2 = w.s([w.s([w.s([a12], 'oveq2d', '( %s -> %s = %s )' % (A0, R11, R2))], 'oveq2d', '( %s -> ( %s / %s ) = ( %s / %s ) )' % (A0, KK, R11, KK, R2))], 'oveq1d',
             '( %s -> ( ( %s / %s ) x. %s ) = ( ( %s / %s ) x. %s ) )' % (A0, KK, R11, AX, KK, R2, AX))
    rmq = w.s([w.s([e1, rmq1], 'eqbrtrrd', '( %s -> ( abs ` ( %s / %s ) ) <_ ( ( %s / %s ) x. %s ) )' % (A0, G2, X1, KK, R11, AX)), e2], 'breqtrd',
              '( %s -> ( abs ` ( %s / %s ) ) <_ ( ( %s / %s ) x. %s ) )' % (A0, G2, X1, KK, R2, AX))
    KD = '( %s / ( %s x. %s ) )' % (KK, TP2, R2)
    fin = divtp(w, d, '( %s / %s )' % (G2, X1), g2q, rmq, R2, r2c, r2ne, KD)
    w.qed([w.s([dif], 'fveq2d', '( %s -> ( abs ` ( %s - ( %s / %s ) ) ) = ( abs ` ( ( %s / %s ) / %s ) ) )' % (A0, DQ, C1, TPI, G2, X1, TPI)), fin], 'eqbrtrd',
          '( %s -> ( abs ` ( %s - ( %s / %s ) ) ) <_ ( %s x. %s ) )' % (A0, DQ, C1, TPI, KD, AX))
    run1(w, h=True)
