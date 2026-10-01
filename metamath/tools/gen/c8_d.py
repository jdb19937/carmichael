"""Sortie C8, section 1: the Cauchy-Lipschitz estimate (rectintlip) and the
Lipschitz constant on a nested rectangle (hollip)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *

TPI = '( 2 x. ( _i x. _pi ) )'
RQ = RE('Q'); IQ = IM('Q')
INTQ = '( Q e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RQ, RQ, RB, IA, IQ, IQ, IB)
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR


def gen_rectintlip():
    RBDP = RBD('P', 'R'); RBDQ = RBD('Q', 'S')
    E2 = '( ( A crect B ) \\ { P , Q } )'
    KER = MP('z', E2, '( ( F ` z ) / ( ( z - P ) x. ( z - Q ) ) )')
    II = RINT(KER, 'A', 'B')
    C1 = '( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s )' % (AB, INTP, INTQ, HOLO)
    C2 = '( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < S ) )' % (RBDP, RBDQ)
    C3 = '( M e. RR /\\ %s )' % ALF
    DQP = '( ( F ` Q ) - ( F ` P ) )'
    DPQ = '( ( F ` P ) - ( F ` Q ) )'
    AQ = '( abs ` %s )' % DQP
    DD = '( abs ` ( Q - P ) )'
    L0 = '( ( 2 x. _pi ) x. %s )' % AQ
    RS = '( R x. S )'
    TT = '( ( ( 2 x. M ) x. %s ) x. %s )' % (PER, DD)
    w = W('rectintlip', 'Cauchy-Lipschitz estimate: a function holomorphic on a rectangle varies between two strictly interior points by at most a constant times their distance, the constant coming from the two-point Cauchy formula ( ~ rectintsch without the zero).')
    A0 = '( %s /\\ %s /\\ %s )' % (C1, C2, C3)
    c1 = w.s([], 'simp1', '( %s -> %s )' % (A0, C1))
    c2 = w.s([], 'simp2', '( %s -> %s )' % (A0, C2))
    mal = w.s([], 'simp3', '( %s -> %s )' % (A0, C3))
    mr = w.s([mal, w.inst('simpl')], 'syl', '( %s -> M e. RR )' % A0)
    rb1 = w.s([c2, w.inst('simpl')], 'syl', '( %s -> ( %s /\\ 0 < R ) )' % (A0, RBDP))
    rb2 = w.s([c2, w.inst('simpr')], 'syl', '( %s -> ( %s /\\ 0 < S ) )' % (A0, RBDQ))
    rr = w.s([w.s([rb1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDP)), w.inst('simpl')], 'syl', '( %s -> R e. RR )' % A0)
    sr = w.s([w.s([rb2, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, RBDQ)), w.inst('simpl')], 'syl', '( %s -> S e. RR )' % A0)
    rp = w.s([rb1, w.inst('simpr')], 'syl', '( %s -> 0 < R )' % A0)
    sp = w.s([rb2, w.inst('simpr')], 'syl', '( %s -> 0 < S )' % A0)
    rrp = w.s([rr, rp], 'elrpd', '( %s -> R e. RR+ )' % A0)
    srp = w.s([sr, sp], 'elrpd', '( %s -> S e. RR+ )' % A0)
    rsrp = w.s([rrp, srp], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, RS))
    ab = w.s([c1, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, AB))
    pq = w.s([c1, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s /\\ P =/= Q ) )' % (A0, INTP, INTQ))
    ho = w.s([c1, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, HOLO))
    it = w.s([pq, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, INTP))
    iq = w.s([pq, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, INTQ))
    fcn = w.s([ho, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0)
    rdv = w.s([ho, w.inst('simpr')], 'syl', '( %s -> ( A crect B ) C_ dom ( CC _D F ) )' % A0)
    ff = w.s([fcn, w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    dcc = w.s([fcn, w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % A0)
    dvs = w.s([w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0), ff, dcc], 'dvbss', '( %s -> dom ( CC _D F ) C_ D )' % A0)
    rdd = w.s([rdv, dvs], 'sstrd', '( %s -> ( A crect B ) C_ D )' % A0)
    ac = w.s([ab, w.inst('simpl')], 'syl', '( %s -> A e. CC )' % A0)
    bc = w.s([ab, w.inst('simpr')], 'syl', '( %s -> B e. CC )' % A0)
    pc = w.s([it, w.inst('simpl')], 'syl', '( %s -> P e. CC )' % A0)
    qc = w.s([iq, w.inst('simpl')], 'syl', '( %s -> Q e. CC )' % A0)
    pd = w.s([rdd, w.s([ab, it, w.inst('crectinp')], 'syl2anc', '( %s -> P e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> P e. D )' % A0)
    qd = w.s([rdd, w.s([ab, iq, w.inst('crectinp')], 'syl2anc', '( %s -> Q e. ( A crect B ) )' % A0)], 'sseldd', '( %s -> Q e. D )' % A0)
    fpc = w.s([ff, pd], 'ffvelcdmd', '( %s -> ( F ` P ) e. CC )' % A0)
    fqc = w.s([ff, qd], 'ffvelcdmd', '( %s -> ( F ` Q ) e. CC )' % A0)
    crss = w.s([ab, w.inst('crectss')], 'syl', '( %s -> ( A crect B ) C_ CC )' % A0)
    sp1 = w.s([w.s([], 'snsspr1', '{ P } C_ { P , Q }')], 'a1i', '( %s -> { P } C_ { P , Q } )' % A0)
    sp2 = w.s([w.s([], 'snsspr2', '{ Q } C_ { P , Q }')], 'a1i', '( %s -> { Q } C_ { P , Q } )' % A0)
    e2cp = w.s([crss, sp1], 'ssdif2d', '( %s -> %s C_ ( CC \\ { P } ) )' % (A0, E2))
    e2cq = w.s([crss, sp2], 'ssdif2d', '( %s -> %s C_ ( CC \\ { Q } ) )' % (A0, E2))
    e2cr = w.s([w.s([], 'difss', '%s C_ ( A crect B )' % E2)], 'a1i', '( %s -> %s C_ ( A crect B ) )' % (A0, E2))
    e2d = w.s([e2cr, rdd], 'sstrd', '( %s -> %s C_ D )' % (A0, E2))
    kcn = w.s([fcn, e2d, w.s([w.s([pc, e2cp], 'jca', '( %s -> ( P e. CC /\\ %s C_ ( CC \\ { P } ) ) )' % (A0, E2)),
                              w.s([qc, e2cq], 'jca', '( %s -> ( Q e. CC /\\ %s C_ ( CC \\ { Q } ) ) )' % (A0, E2))], 'jca',
                             '( %s -> ( ( P e. CC /\\ %s C_ ( CC \\ { P } ) ) /\\ ( Q e. CC /\\ %s C_ ( CC \\ { Q } ) ) ) )' % (A0, E2, E2)),
                 w.inst('qf2cn')], 'syl3anc', '( %s -> %s e. ( %s -cn-> CC ) )' % (A0, KER, E2))
    fre2 = w.s([ab, it, iq, w.inst('crectfrd')], 'syl3anc', '( %s -> %s C_ %s )' % (A0, FR, E2))
    iicl = w.s([ab, w.s([kcn, fre2], 'jca', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (A0, KER, E2, FR, E2)), w.inst('rectintcle')],
               'syl2anc', '( %s -> %s e. CC )' % (A0, II))
    cd = w.s([ab, pq, ho, w.inst('rectintcaud')], 'syl3anc', '( %s -> ( %s x. %s ) = ( ( P - Q ) x. %s ) )' % (A0, TPI, DPQ, II))
    tpic = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([w.s([], 'pire', '_pi e. RR')], 'recni', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI)], 'a1i', '( %s -> %s e. CC )' % (A0, TPI))
    dpqc = w.s([fpc, fqc], 'subcld', '( %s -> %s e. CC )' % (A0, DPQ))
    lhs2 = w.s([tpic, dpqc], 'absmuld', '( %s -> ( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (A0, TPI, DPQ, TPI, DPQ))
    lhs3 = w.s([w.s([w.s([], 'abstpi', '( abs ` %s ) = ( 2 x. _pi )' % TPI)], 'a1i', '( %s -> ( abs ` %s ) = ( 2 x. _pi ) )' % (A0, TPI)),
                w.s([fpc, fqc], 'abssubd', '( %s -> ( abs ` %s ) = %s )' % (A0, DPQ, AQ))], 'oveq12d',
               '( %s -> ( ( abs ` %s ) x. ( abs ` %s ) ) = %s )' % (A0, TPI, DPQ, L0))
    lhs = w.s([lhs2, lhs3], 'eqtrd', '( %s -> ( abs ` ( %s x. %s ) ) = %s )' % (A0, TPI, DPQ, L0))
    rhs1 = w.s([w.s([pc, qc], 'subcld', '( %s -> ( P - Q ) e. CC )' % A0), iicl], 'absmuld',
               '( %s -> ( abs ` ( ( P - Q ) x. %s ) ) = ( ( abs ` ( P - Q ) ) x. ( abs ` %s ) ) )' % (A0, II, II))
    rhs2 = w.s([w.s([pc, qc], 'abssubd', '( %s -> ( abs ` ( P - Q ) ) = %s )' % (A0, DD))], 'oveq1d',
               '( %s -> ( ( abs ` ( P - Q ) ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) ) )' % (A0, II, DD, II))
    rhs = w.s([rhs1, rhs2], 'eqtrd', '( %s -> ( abs ` ( ( P - Q ) x. %s ) ) = ( %s x. ( abs ` %s ) ) )' % (A0, II, DD, II))
    eqv = w.s([w.s([cd], 'fveq2d', '( %s -> ( abs ` ( %s x. %s ) ) = ( abs ` ( ( P - Q ) x. %s ) ) )' % (A0, TPI, DPQ, II)), rhs],
              'eqtrd', '( %s -> ( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) ) )' % (A0, TPI, DPQ, DD, II))
    key = w.s([w.s([lhs], 'eqcomd', '( %s -> %s = ( abs ` ( %s x. %s ) ) )' % (A0, L0, TPI, DPQ)), eqv], 'eqtrd',
              '( %s -> %s = ( %s x. ( abs ` %s ) ) )' % (A0, L0, DD, II))
    ce2 = w.s([c1, c2, mal, w.inst('rectintce2')], 'syl3anc',
              '( %s -> ( abs ` %s ) <_ ( ( 2 x. ( M / %s ) ) x. %s ) )' % (A0, II, RS, PER))
    qpc = w.s([qc, pc], 'subcld', '( %s -> ( Q - P ) e. CC )' % A0)
    ddr = w.s([qpc], 'abscld', '( %s -> %s e. RR )' % (A0, DD))
    dd0 = w.s([qpc], 'absge0d', '( %s -> 0 <_ %s )' % (A0, DD))
    iir = w.s([iicl], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (A0, II))
    ar_ = w.s([ac], 'recld', '( %s -> %s e. RR )' % (A0, RA)); br_ = w.s([bc], 'recld', '( %s -> %s e. RR )' % (A0, RB))
    ai_ = w.s([ac], 'imcld', '( %s -> %s e. RR )' % (A0, IA)); bi_ = w.s([bc], 'imcld', '( %s -> %s e. RR )' % (A0, IB))
    perr = w.s([w.s([br_, ar_], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, RB, RA)),
                w.s([bi_, ai_], 'resubcld', '( %s -> ( %s - %s ) e. RR )' % (A0, IB, IA))], 'readdcld', '( %s -> %s e. RR )' % (A0, PER))
    mrs = w.s([mr, rsrp], 'rerpdivcld', '( %s -> ( M / %s ) e. RR )' % (A0, RS))
    two = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0)
    t2md = w.s([two, mrs], 'remulcld', '( %s -> ( 2 x. ( M / %s ) ) e. RR )' % (A0, RS))
    bnd1 = w.s([iir, w.s([t2md, perr], 'remulcld', '( %s -> ( ( 2 x. ( M / %s ) ) x. %s ) e. RR )' % (A0, RS, PER)),
                w.s([ddr, dd0], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (A0, DD, DD))], '3jca',
               '( %s -> ( ( abs ` %s ) e. RR /\\ ( ( 2 x. ( M / %s ) ) x. %s ) e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (A0, II, RS, PER, DD, DD))
    bnd = w.s([bnd1, ce2, w.inst('lemul2a')], 'syl2anc',
              '( %s -> ( %s x. ( abs ` %s ) ) <_ ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) )' % (A0, DD, II, DD, RS, PER))
    step = w.s([key, bnd], 'eqbrtrd', '( %s -> %s <_ ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) )' % (A0, L0, DD, RS, PER))
    mc = w.s([mr], 'recnd', '( %s -> M e. CC )' % A0)
    perc = w.s([perr], 'recnd', '( %s -> %s e. CC )' % (A0, PER))
    ddc = w.s([ddr], 'recnd', '( %s -> %s e. CC )' % (A0, DD))
    rsc = w.s([w.s([rsrp], 'rpred', '( %s -> %s e. RR )' % (A0, RS))], 'recnd', '( %s -> %s e. CC )' % (A0, RS))
    rsne = w.s([rsrp], 'rpne0d', '( %s -> %s =/= 0 )' % (A0, RS))
    t2c = w.s([two], 'recnd', '( %s -> 2 e. CC )' % A0)
    m2c = w.s([t2c, mc], 'mulcld', '( %s -> ( 2 x. M ) e. CC )' % A0)
    q1 = w.s([w.s([t2c, mc, rsc, rsne], 'divassd', '( %s -> ( ( 2 x. M ) / %s ) = ( 2 x. ( M / %s ) ) )' % (A0, RS, RS))], 'eqcomd',
             '( %s -> ( 2 x. ( M / %s ) ) = ( ( 2 x. M ) / %s ) )' % (A0, RS, RS))
    q2 = w.s([w.s([q1], 'oveq1d', '( %s -> ( ( 2 x. ( M / %s ) ) x. %s ) = ( ( ( 2 x. M ) / %s ) x. %s ) )' % (A0, RS, PER, RS, PER)),
              w.s([w.s([m2c, perc, rsc, rsne], 'div23d',
                       '( %s -> ( ( ( 2 x. M ) x. %s ) / %s ) = ( ( ( 2 x. M ) / %s ) x. %s ) )' % (A0, PER, RS, RS, PER))], 'eqcomd',
                  '( %s -> ( ( ( 2 x. M ) / %s ) x. %s ) = ( ( ( 2 x. M ) x. %s ) / %s ) )' % (A0, RS, PER, PER, RS))], 'eqtrd',
             '( %s -> ( ( 2 x. ( M / %s ) ) x. %s ) = ( ( ( 2 x. M ) x. %s ) / %s ) )' % (A0, RS, PER, PER, RS))
    mpc = w.s([m2c, perc], 'mulcld', '( %s -> ( ( 2 x. M ) x. %s ) e. CC )' % (A0, PER))
    q3 = w.s([w.s([ddc, mpc, rsc, rsne], 'divassd', '( %s -> ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) = ( %s x. ( ( ( 2 x. M ) x. %s ) / %s ) ) )' % (A0, DD, PER, RS, DD, PER, RS))], 'eqcomd',
             '( %s -> ( %s x. ( ( ( 2 x. M ) x. %s ) / %s ) ) = ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) )' % (A0, DD, PER, RS, DD, PER, RS))
    q4 = w.s([w.s([ddc, mpc], 'mulcomd', '( %s -> ( %s x. ( ( 2 x. M ) x. %s ) ) = %s )' % (A0, DD, PER, TT))], 'oveq1d',
             '( %s -> ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) = ( %s / %s ) )' % (A0, DD, PER, RS, TT, RS))
    rw = w.s([w.s([w.s([q2], 'oveq2d', '( %s -> ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) = ( %s x. ( ( ( 2 x. M ) x. %s ) / %s ) ) )' % (A0, DD, RS, PER, DD, PER, RS)), q3],
                   'eqtrd', '( %s -> ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) = ( ( %s x. ( ( 2 x. M ) x. %s ) ) / %s ) )' % (A0, DD, RS, PER, DD, PER, RS)), q4],
              'eqtrd', '( %s -> ( %s x. ( ( 2 x. ( M / %s ) ) x. %s ) ) = ( %s / %s ) )' % (A0, DD, RS, PER, TT, RS))
    step2 = w.s([step, rw], 'breqtrd', '( %s -> %s <_ ( %s / %s ) )' % (A0, L0, TT, RS))
    aqr = w.s([w.s([fqc, fpc], 'subcld', '( %s -> %s e. CC )' % (A0, DQP))], 'abscld', '( %s -> %s e. RR )' % (A0, AQ))
    l0r = w.s([w.s([two, w.s([w.s([], 'pire', '_pi e. RR')], 'a1i', '( %s -> _pi e. RR )' % A0)], 'remulcld',
                   '( %s -> ( 2 x. _pi ) e. RR )' % A0), aqr], 'remulcld', '( %s -> %s e. RR )' % (A0, L0))
    ttr = w.s([w.s([w.s([two, mr], 'remulcld', '( %s -> ( 2 x. M ) e. RR )' % A0), perr], 'remulcld',
                   '( %s -> ( ( 2 x. M ) x. %s ) e. RR )' % (A0, PER)), ddr], 'remulcld', '( %s -> %s e. RR )' % (A0, TT))
    w.qed([step2, w.s([l0r, ttr, w.s([w.s([rsrp], 'rpred', '( %s -> %s e. RR )' % (A0, RS)), w.s([rsrp], 'rpgt0d', '( %s -> 0 < %s )' % (A0, RS))], 'jca',
                                     '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A0, RS, RS)), w.inst('lemuldiv')], 'syl3anc',
                      '( %s -> ( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) ) )' % (A0, L0, RS, TT, L0, TT, RS))],
          'mpbird', '( %s -> ( %s x. %s ) <_ %s )' % (A0, L0, RS, TT))
    return run8(w)


def nestat(w, ante, d, X, xin):
    """holnest at X: steps ( ante -> INTG(AR,BR,X) ), ( ante -> RBDG(AR,BR,X,R) )"""
    both = w.s([w.s([d['ab'], d['Rrp']], 'jca', '( %s -> ( %s /\\ R e. RR+ ) )' % (ante, AB)), xin, w.inst('holnest')], 'syl2anc',
               '( %s -> ( %s /\\ %s ) )' % (ante, INTG(AR, BR, X), RBDG(AR, BR, X, 'R')))
    return (w.s([both, w.inst('simpl')], 'syl', '( %s -> %s )' % (ante, INTG(AR, BR, X))),
            w.s([both, w.inst('simpr')], 'syl', '( %s -> %s )' % (ante, RBDG(AR, BR, X, 'R'))))


def intparts(w, ante, it, X):
    """from ( ante -> INTG(AR,BR,X) ): the four strict inequalities"""
    ineq = w.s([it, w.inst('simpr')], 'syl', '( %s -> ( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) ) )' % (
        ante, AR, X, X, BR, AR, X, X, BR))
    r = w.s([ineq, w.inst('simpl')], 'syl', '( %s -> ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) )' % (ante, AR, X, X, BR))
    i = w.s([ineq, w.inst('simpr')], 'syl', '( %s -> ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) )' % (ante, AR, X, X, BR))
    return (w.s([r, w.inst('simpl')], 'syl', '( %s -> ( Re ` %s ) < ( Re ` %s ) )' % (ante, AR, X)),
            w.s([r, w.inst('simpr')], 'syl', '( %s -> ( Re ` %s ) < ( Re ` %s ) )' % (ante, X, BR)),
            w.s([i, w.inst('simpl')], 'syl', '( %s -> ( Im ` %s ) < ( Im ` %s ) )' % (ante, AR, X)),
            w.s([i, w.inst('simpr')], 'syl', '( %s -> ( Im ` %s ) < ( Im ` %s ) )' % (ante, X, BR)))


PERB = '( ( ( Re ` %s ) - ( Re ` %s ) ) + ( ( Im ` %s ) - ( Im ` %s ) ) )' % (BR, AR, BR, AR)
FRB = FRG(AR, BR)
BIG = '( %s crect %s )' % (AR, BR)


def gen_hollip():
    w = W('hollip', 'A function holomorphic on an open set containing a nested rectangle is Lipschitz on the inner rectangle.')
    A0 = ABGEO
    st = w.s([], 'id', '( %s -> %s )' % (A0, A0))
    d = abgeoctx(w, A0, st)
    ab, geo = d['ab'], d['geo']
    arc, brc = d['arc'], d['brc']
    # the big rectangle: GEO, PERB > 0, HOLO
    ain = w.s([ab, geo, w.inst('crectcnr1')], 'syl2anc', '( %s -> A e. ( A crect B ) )' % A0)
    ita, _ = nestat(w, A0, d, 'A', ain)
    l1, l2, l3, l4 = intparts(w, A0, ita, 'A')
    rar = w.s([arc], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, AR)); rbr = w.s([brc], 'recld', '( %s -> ( Re ` %s ) e. RR )' % (A0, BR))
    iar = w.s([arc], 'imcld', '( %s -> ( Im ` %s ) e. RR )' % (A0, AR)); ibr = w.s([brc], 'imcld', '( %s -> ( Im ` %s ) e. RR )' % (A0, BR))
    ra = w.s([d['ac']], 'recld', '( %s -> ( Re ` A ) e. RR )' % A0); ia = w.s([d['ac']], 'imcld', '( %s -> ( Im ` A ) e. RR )' % A0)
    rlt = w.s([rar, ra, rbr, l1, l2], 'lttrd', '( %s -> ( Re ` %s ) < ( Re ` %s ) )' % (A0, AR, BR))
    ilt = w.s([iar, ia, ibr, l3, l4], 'lttrd', '( %s -> ( Im ` %s ) < ( Im ` %s ) )' % (A0, AR, BR))
    geob = w.s([w.s([rar, rbr, rlt], 'ltled', '( %s -> ( Re ` %s ) <_ ( Re ` %s ) )' % (A0, AR, BR)),
                w.s([iar, ibr, ilt], 'ltled', '( %s -> ( Im ` %s ) <_ ( Im ` %s ) )' % (A0, AR, BR))], 'jca', '( %s -> %s )' % (A0, GEOG(AR, BR)))
    pr1 = w.s([rlt, w.s([rar, rbr], 'posdifd', '( %s -> ( ( Re ` %s ) < ( Re ` %s ) <-> 0 < ( ( Re ` %s ) - ( Re ` %s ) ) ) )' % (A0, AR, BR, BR, AR))], 'mpbid',
              '( %s -> 0 < ( ( Re ` %s ) - ( Re ` %s ) ) )' % (A0, BR, AR))
    pi1 = w.s([ilt, w.s([iar, ibr], 'posdifd', '( %s -> ( ( Im ` %s ) < ( Im ` %s ) <-> 0 < ( ( Im ` %s ) - ( Im ` %s ) ) ) )' % (A0, AR, BR, BR, AR))], 'mpbid',
              '( %s -> 0 < ( ( Im ` %s ) - ( Im ` %s ) ) )' % (A0, BR, AR))
    dr = w.s([rbr, rar], 'resubcld', '( %s -> ( ( Re ` %s ) - ( Re ` %s ) ) e. RR )' % (A0, BR, AR))
    di = w.s([ibr, iar], 'resubcld', '( %s -> ( ( Im ` %s ) - ( Im ` %s ) ) e. RR )' % (A0, BR, AR))
    perbr = w.s([dr, di], 'readdcld', '( %s -> %s e. RR )' % (A0, PERB))
    perbp = w.s([dr, di, pr1, pi1], 'addgt0d', '( %s -> 0 < %s )' % (A0, PERB))
    perbrp = w.s([perbr, perbp], 'elrpd', '( %s -> %s e. RR+ )' % (A0, PERB))
    holob = w.s([d['hol'], d['nss'], w.inst('holcrect')], 'syl2anc', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ dom ( CC _D F ) ) )' % (A0, BIG))
    frb = w.s([d['abr'], geob, w.inst('crectfru')], 'syl2anc', '( %s -> %s C_ %s )' % (A0, FRB, BIG))
    bigbnd = w.s([d['abr'], w.s([d['fcn'], d['nss']], 'jca', '( %s -> ( F e. ( D -cn-> CC ) /\\ %s C_ D ) )' % (A0, BIG)), w.inst('crectbnd')], 'syl2anc',
                 '( %s -> E. n e. RR A. v e. %s ( abs ` ( F ` v ) ) <_ n )' % (A0, BIG))
    # ---- under a bound n
    BV = 'A. v e. %s ( abs ` ( F ` v ) ) <_ n' % BIG
    A2 = '( ( %s /\\ n e. RR ) /\\ %s )' % (A0, BV)
    a0 = w.s([], 'simpll', '( %s -> %s )' % (A2, A0))
    def up(x, f):
        return w.s([a0, x], 'syl', '( %s -> %s )' % (A2, f))
    nr = w.s([], 'simplr', '( %s -> n e. RR )' % A2)
    nb = w.s([], 'simpr', '( %s -> %s )' % (A2, BV))
    M1 = '( ( abs ` n ) + 1 )'
    nc = w.s([nr], 'recnd', '( %s -> n e. CC )' % A2)
    anr = w.s([nc], 'abscld', '( %s -> ( abs ` n ) e. RR )' % A2)
    an0 = w.s([nc], 'absge0d', '( %s -> 0 <_ ( abs ` n ) )' % A2)
    one2 = w.s([], '1red', '( %s -> 1 e. RR )' % A2)
    m1r = w.s([anr, one2], 'readdcld', '( %s -> %s e. RR )' % (A2, M1))
    m1p = w.s([anr, one2, an0, w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % A2)], 'addgegt0d', '( %s -> 0 < %s )' % (A2, M1))
    m1rp = w.s([m1r, m1p], 'elrpd', '( %s -> %s e. RR+ )' % (A2, M1))
    nle = w.s([nr, w.inst('leabs')], 'syl', '( %s -> n <_ ( abs ` n ) )' % A2)
    nm1 = w.s([nr, anr, m1r, nle, w.s([w.s([anr], 'ltp1d', '( %s -> ( abs ` n ) < %s )' % (A2, M1))], 'ltled', '( %s -> ( abs ` n ) <_ %s )' % (A2, M1))],
              'letrd', '( %s -> n <_ %s )' % (A2, M1))
    # frame bound with M1
    A3 = '( %s /\\ u e. %s )' % (A2, FRB)
    uin = w.s([w.s([w.s([a0, frb], 'syl', '( %s -> %s C_ %s )' % (A2, FRB, BIG))], 'adantr', '( %s -> %s C_ %s )' % (A3, FRB, BIG)),
               w.s([], 'simpr', '( %s -> u e. %s )' % (A3, FRB))], 'sseldd', '( %s -> u e. %s )' % (A3, BIG))
    subv = w.s([w.s([w.s([], 'fveq2', '( v = u -> ( F ` v ) = ( F ` u ) )')], 'fveq2d', '( v = u -> ( abs ` ( F ` v ) ) = ( abs ` ( F ` u ) ) )')], 'breq1d',
               '( v = u -> ( ( abs ` ( F ` v ) ) <_ n <-> ( abs ` ( F ` u ) ) <_ n ) )')
    fun = w.s([subv, uin, w.s([nb], 'adantr', '( %s -> %s )' % (A3, BV))], 'rspcdva', '( %s -> ( abs ` ( F ` u ) ) <_ n )' % A3)
    a0u = w.s([a0], 'adantr', '( %s -> %s )' % (A3, A0))
    ud = w.s([w.s([a0u, d['nss']], 'syl', '( %s -> %s C_ D )' % (A3, BIG)), uin], 'sseldd', '( %s -> u e. D )' % A3)
    fuc = w.s([w.s([a0u, d['ff']], 'syl', '( %s -> F : D --> CC )' % A3), ud], 'ffvelcdmd', '( %s -> ( F ` u ) e. CC )' % A3)
    fu2 = w.s([w.s([fuc], 'abscld', '( %s -> ( abs ` ( F ` u ) ) e. RR )' % A3), w.s([nr], 'adantr', '( %s -> n e. RR )' % A3),
               w.s([m1r], 'adantr', '( %s -> %s e. RR )' % (A3, M1)), fun, w.s([nm1], 'adantr', '( %s -> n <_ %s )' % (A3, M1))], 'letrd',
              '( %s -> ( abs ` ( F ` u ) ) <_ %s )' % (A3, M1))
    alfb = w.s([fu2], 'ralrimiva', '( %s -> A. u e. %s ( abs ` ( F ` u ) ) <_ %s )' % (A2, FRB, M1))
    malf = w.s([m1r, alfb], 'jca', '( %s -> ( %s e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ %s ) )' % (A2, M1, FRB, M1))
    # constants
    RR2 = '( R x. R )'
    Y = '( ( 2 x. _pi ) x. %s )' % RR2
    rrp = up(d['Rrp'], 'R e. RR+')
    t2pi = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A2), w.s([w.s([], 'pirp', '_pi e. RR+')], 'a1i', '( %s -> _pi e. RR+ )' % A2)],
               'rpmulcld', '( %s -> ( 2 x. _pi ) e. RR+ )' % A2)
    yrp = w.s([t2pi, w.s([rrp, rrp], 'rpmulcld', '( %s -> %s e. RR+ )' % (A2, RR2))], 'rpmulcld', '( %s -> %s e. RR+ )' % (A2, Y))
    NUM = '( ( 2 x. %s ) x. %s )' % (M1, PERB)
    numrp = w.s([w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A2), m1rp], 'rpmulcld', '( %s -> ( 2 x. %s ) e. RR+ )' % (A2, M1)),
                 up(perbrp, '%s e. RR+' % PERB)], 'rpmulcld', '( %s -> %s e. RR+ )' % (A2, NUM))
    L = '( %s / %s )' % (NUM, Y)
    lrp = w.s([numrp, yrp], 'rpdivcld', '( %s -> %s e. RR+ )' % (A2, L))
    # ---- two points
    A4 = '( %s /\\ ( p e. ( A crect B ) /\\ q e. ( A crect B ) ) )' % A2
    GOAL = '( abs ` ( ( F ` p ) - ( F ` q ) ) ) <_ ( %s x. ( abs ` ( p - q ) ) )' % L
    pin = w.s([], 'simprl', '( %s -> p e. ( A crect B ) )' % A4)
    qin = w.s([], 'simprr', '( %s -> q e. ( A crect B ) )' % A4)
    a04 = w.s([], 'simpll' if False else 'simplll', '( %s -> %s )' % (A4, A0))
    d4 = {'ab': w.s([a04, ab], 'syl', '( %s -> %s )' % (A4, AB)), 'Rrp': w.s([a04, d['Rrp']], 'syl', '( %s -> R e. RR+ )' % A4)}
    kss = w.s([a04, w.s([d['nss']], 'idi', '( %s -> %s C_ D )' % (A0, BIG))], 'syl', '( %s -> %s C_ D )' % (A4, BIG))
    crss4 = w.s([a04, d['crss']], 'syl', '( %s -> ( A crect B ) C_ CC )' % A4)
    pc = w.s([crss4, pin], 'sseldd', '( %s -> p e. CC )' % A4)
    qc = w.s([crss4, qin], 'sseldd', '( %s -> q e. CC )' % A4)
    ff4 = w.s([a04, d['ff']], 'syl', '( %s -> F : D --> CC )' % A4)
    ksd4 = w.s([a04, w.s([d['hol'], ab, d['nest'], w.inst('holnss')], 'syl3anc', '( %s -> ( A crect B ) C_ D )' % A0)], 'syl', '( %s -> ( A crect B ) C_ D )' % A4)
    fpc = w.s([ff4, w.s([ksd4, pin], 'sseldd', '( %s -> p e. D )' % A4)], 'ffvelcdmd', '( %s -> ( F ` p ) e. CC )' % A4)
    fqc = w.s([ff4, w.s([ksd4, qin], 'sseldd', '( %s -> q e. D )' % A4)], 'ffvelcdmd', '( %s -> ( F ` q ) e. CC )' % A4)
    l4r = w.s([w.s([lrp], 'adantr', '( %s -> %s e. RR+ )' % (A4, L))], 'rpred', '( %s -> %s e. RR )' % (A4, L))
    pqr = w.s([w.s([pc, qc], 'subcld', '( %s -> ( p - q ) e. CC )' % A4)], 'abscld', '( %s -> ( abs ` ( p - q ) ) e. RR )' % A4)
    # case p = q
    A5 = '( %s /\\ p = q )' % A4
    feq = w.s([w.s([], 'simpr', '( %s -> p = q )' % A5)], 'fveq2d', '( %s -> ( F ` p ) = ( F ` q ) )' % A5)
    z1 = w.s([w.s([fpc], 'adantr', '( %s -> ( F ` p ) e. CC )' % A5), feq], 'subeq0bd', '( %s -> ( ( F ` p ) - ( F ` q ) ) = 0 )' % A5)
    z2 = w.s([w.s([z1], 'fveq2d', '( %s -> ( abs ` ( ( F ` p ) - ( F ` q ) ) ) = ( abs ` 0 ) )' % A5),
              w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % A5)], 'eqtrd',
             '( %s -> ( abs ` ( ( F ` p ) - ( F ` q ) ) ) = 0 )' % A5)
    z3 = w.s([w.s([l4r], 'adantr', '( %s -> %s e. RR )' % (A5, L)), w.s([pqr], 'adantr', '( %s -> ( abs ` ( p - q ) ) e. RR )' % A5),
              w.s([w.s([w.s([lrp], 'adantr', '( %s -> %s e. RR+ )' % (A4, L))], 'rpge0d', '( %s -> 0 <_ %s )' % (A4, L))], 'adantr', '( %s -> 0 <_ %s )' % (A5, L)),
              w.s([w.s([w.s([pc, qc], 'subcld', '( %s -> ( p - q ) e. CC )' % A4)], 'absge0d', '( %s -> 0 <_ ( abs ` ( p - q ) ) )' % A4)], 'adantr',
                  '( %s -> 0 <_ ( abs ` ( p - q ) ) )' % A5)], 'mulge0d', '( %s -> 0 <_ ( %s x. ( abs ` ( p - q ) ) ) )' % (A5, L))
    case1 = w.s([z2, z3], 'eqbrtrd', '( %s -> %s )' % (A5, GOAL))
    # case p =/= q
    A6 = '( %s /\\ p =/= q )' % A4
    a06 = w.s([], 'simp1' if False else 'simplll', '( %s -> %s )' % (A6, A2)) if False else None
    ita4q, rbq = nestat(w, A4, d4, 'q', qin)
    ita4p, rbp = nestat(w, A4, d4, 'p', pin)
    nq = w.s([w.s([], 'simpr', '( %s -> p =/= q )' % A6)], 'necomd', '( %s -> q =/= p )' % A6)
    ints = w.s([w.s([ita4q], 'adantr', '( %s -> %s )' % (A6, INTG(AR, BR, 'q'))), w.s([ita4p], 'adantr', '( %s -> %s )' % (A6, INTG(AR, BR, 'p'))), nq], '3jca',
               '( %s -> ( %s /\\ %s /\\ q =/= p ) )' % (A6, INTG(AR, BR, 'q'), INTG(AR, BR, 'p')))
    HOLOB = '( F e. ( D -cn-> CC ) /\\ %s C_ dom ( CC _D F ) )' % BIG
    c1 = w.s([w.s([w.s([a04, d['abr']], 'syl', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A4, AR, BR))], 'adantr', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A6, AR, BR)),
              ints, w.s([w.s([a04, holob], 'syl', '( %s -> %s )' % (A4, HOLOB))], 'adantr', '( %s -> %s )' % (A6, HOLOB))], '3jca',
             '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s /\\ %s /\\ q =/= p ) /\\ %s ) )' % (A6, AR, BR, INTG(AR, BR, 'q'), INTG(AR, BR, 'p'), HOLOB))
    rpos4 = w.s([a04, d['rpos']], 'syl', '( %s -> 0 < R )' % A4)
    c2 = w.s([w.s([w.s([rbq, rpos4], 'jca', '( %s -> ( %s /\\ 0 < R ) )' % (A4, RBDG(AR, BR, 'q', 'R'))),
                   w.s([rbp, rpos4], 'jca', '( %s -> ( %s /\\ 0 < R ) )' % (A4, RBDG(AR, BR, 'p', 'R')))], 'jca',
                  '( %s -> ( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < R ) ) )' % (A4, RBDG(AR, BR, 'q', 'R'), RBDG(AR, BR, 'p', 'R')))], 'adantr',
             '( %s -> ( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < R ) ) )' % (A6, RBDG(AR, BR, 'q', 'R'), RBDG(AR, BR, 'p', 'R')))
    MALF = '( %s e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ %s )' % (M1, FRB, M1)
    c3 = w.s([w.s([malf], 'adantr', '( %s -> %s )' % (A4, MALF))], 'adantr', '( %s -> %s )' % (A6, MALF))
    X = '( abs ` ( ( F ` p ) - ( F ` q ) ) )'
    Z = '( %s x. ( abs ` ( p - q ) ) )' % NUM
    lip = w.s([c1, c2, c3, w.inst('rectintlip')], 'syl3anc',
              '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. %s ) <_ %s )' % (A6, X, RR2, Z))
    xc = w.s([w.s([w.s([fpc, fqc], 'subcld', '( %s -> ( ( F ` p ) - ( F ` q ) ) e. CC )' % A4)], 'abscld', '( %s -> %s e. RR )' % (A4, X))], 'adantr',
             '( %s -> %s e. RR )' % (A6, X))
    y6 = w.s([w.s([yrp], 'adantr', '( %s -> %s e. RR+ )' % (A4, Y))], 'adantr', '( %s -> %s e. RR+ )' % (A6, Y))
    t2pic = w.s([w.s([w.s([t2pi], 'adantr', '( %s -> ( 2 x. _pi ) e. RR+ )' % A4)], 'adantr', '( %s -> ( 2 x. _pi ) e. RR+ )' % A6)], 'rpcnd',
                '( %s -> ( 2 x. _pi ) e. CC )' % A6)
    rr2c = w.s([w.s([w.s([w.s([rrp, rrp], 'rpmulcld', '( %s -> %s e. RR+ )' % (A2, RR2))], 'adantr', '( %s -> %s e. RR+ )' % (A4, RR2))], 'adantr',
                    '( %s -> %s e. RR+ )' % (A6, RR2))], 'rpcnd', '( %s -> %s e. CC )' % (A6, RR2))
    xcc = w.s([xc], 'recnd', '( %s -> %s e. CC )' % (A6, X))
    r1 = w.s([t2pic, xcc, rr2c], 'mul32d', '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. %s ) = ( %s x. %s ) )' % (A6, X, RR2, Y, X))
    r2 = w.s([w.s([y6], 'rpcnd', '( %s -> %s e. CC )' % (A6, Y)), xcc], 'mulcomd', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (A6, Y, X, X, Y))
    r3 = w.s([r1, r2], 'eqtrd', '( %s -> ( ( ( 2 x. _pi ) x. %s ) x. %s ) = ( %s x. %s ) )' % (A6, X, RR2, X, Y))
    lip2 = w.s([r3, lip], 'eqbrtrrd', '( %s -> ( %s x. %s ) <_ %s )' % (A6, X, Y, Z))
    numr6 = w.s([w.s([w.s([numrp], 'adantr', '( %s -> %s e. RR+ )' % (A4, NUM))], 'adantr', '( %s -> %s e. RR+ )' % (A6, NUM))], 'rpred', '( %s -> %s e. RR )' % (A6, NUM))
    pqr6 = w.s([pqr], 'adantr', '( %s -> ( abs ` ( p - q ) ) e. RR )' % A6)
    zr = w.s([numr6, pqr6], 'remulcld', '( %s -> %s e. RR )' % (A6, Z))
    ld = w.s([lip2, w.s([xc, zr, w.s([w.s([y6], 'rpred', '( %s -> %s e. RR )' % (A6, Y)), w.s([y6], 'rpgt0d', '( %s -> 0 < %s )' % (A6, Y))], 'jca',
                                   '( %s -> ( %s e. RR /\\ 0 < %s ) )' % (A6, Y, Y)), w.inst('lemuldiv')], 'syl3anc',
                         '( %s -> ( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) ) )' % (A6, X, Y, Z, X, Z, Y))], 'mpbid',
             '( %s -> %s <_ ( %s / %s ) )' % (A6, X, Z, Y))
    dv = w.s([w.s([numr6], 'recnd', '( %s -> %s e. CC )' % (A6, NUM)), w.s([pqr6], 'recnd', '( %s -> ( abs ` ( p - q ) ) e. CC )' % A6),
              w.s([y6], 'rpcnd', '( %s -> %s e. CC )' % (A6, Y)), w.s([y6], 'rpne0d', '( %s -> %s =/= 0 )' % (A6, Y))], 'div23d',
             '( %s -> ( %s / %s ) = ( %s x. ( abs ` ( p - q ) ) ) )' % (A6, Z, Y, L))
    case2 = w.s([ld, dv], 'breqtrd', '( %s -> %s )' % (A6, GOAL))
    both = w.s([case1, case2], 'pm2.61dane', '( %s -> %s )' % (A4, GOAL))
    ral = w.s([both], 'ralrimivva', '( %s -> A. p e. ( A crect B ) A. q e. ( A crect B ) %s )' % (A2, GOAL))
    CONC = 'E. l e. RR+ A. p e. ( A crect B ) A. q e. ( A crect B ) ( abs ` ( ( F ` p ) - ( F ` q ) ) ) <_ ( l x. ( abs ` ( p - q ) ) )'
    s1 = w.s([], 'oveq1', '( l = %s -> ( l x. ( abs ` ( p - q ) ) ) = ( %s x. ( abs ` ( p - q ) ) ) )' % (L, L))
    s2 = w.s([s1], 'breq2d', '( l = %s -> ( ( abs ` ( ( F ` p ) - ( F ` q ) ) ) <_ ( l x. ( abs ` ( p - q ) ) ) <-> %s ) )' % (L, GOAL))
    s3 = w.s([s2], 'ralbidv', '( l = %s -> ( A. q e. ( A crect B ) ( abs ` ( ( F ` p ) - ( F ` q ) ) ) <_ ( l x. ( abs ` ( p - q ) ) ) <-> A. q e. ( A crect B ) %s ) )' % (L, GOAL))
    s4 = w.s([s3], 'ralbidv', '( l = %s -> ( A. p e. ( A crect B ) A. q e. ( A crect B ) ( abs ` ( ( F ` p ) - ( F ` q ) ) ) <_ ( l x. ( abs ` ( p - q ) ) ) <-> A. p e. ( A crect B ) A. q e. ( A crect B ) %s ) )' % (L, GOAL))
    ex = w.s([lrp, ral, w.s([s4], 'rspcev', '( ( %s e. RR+ /\\ A. p e. ( A crect B ) A. q e. ( A crect B ) %s ) -> %s )' % (L, GOAL, CONC))], 'syl2anc', '( %s -> %s )' % (A2, CONC))
    ex2 = w.s([w.s([ex], 'ex', '( ( %s /\\ n e. RR ) -> ( %s -> %s ) )' % (A0, BV, CONC))], 'rexlimdva', '( %s -> ( E. n e. RR %s -> %s ) )' % (A0, BV, CONC))
    w.qed([bigbnd, ex2], 'mpd', '( %s -> %s )' % (A0, CONC))
    return run8(w)


if __name__ == '__main__':
    for g in [gen_rectintlip, gen_hollip]:
        g()
