"""Sortie EF4: the zero sums of the contour (ef4zs1: zeros of the box left of S; ef4zs2: zeros of the rectangle above T;
ef4zs: Lean hadj)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
from c8_o import numst
import congr as _cg
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts
from ef4_b import ld0_mem, hp0_mem
from ef4lib import ne0_re

BXA, BXB = '( ( 1 / 2 ) + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
RFA, RFB = PTL('S', '-u U'), PTL(C1, 'V')
BZT = BZ(LFN, 'T')
BZA, BZB = '( ( 1 / 2 ) + ( _i x. -u T ) )', '( ( 3 / 2 ) + ( _i x. T ) )'
M_ = '( %s holord q )' % LFN


class Env:
    """the common facts of HZ"""
    def __init__(self, w, A0):
        self.w, self.A0 = w, A0
        c = self.c = Ctx(w, A0)
        g = c.g
        self.chi = g(CHI); self.yr = g('Y e. RR'); self.y100 = g('; ; 1 0 0 <_ Y'); self.tr = g('T e. RR'); self.t2 = g('2 <_ T')
        self.ur = g('U e. RR'); self.vr = g('V e. RR'); self.tu = g('T <_ U'); self.u1 = g('U <_ ( T + 1 )'); self.tv = g('T <_ V'); self.v1 = g('V <_ ( T + 1 )')
        self.sr = g('S e. RR'); self.s916 = g('( 9 / ; 1 6 ) <_ S'); self.s58 = g('S <_ ( 5 / 8 )')
        self.lines = g('A. v e. ( ( 1 / 2 ) [,] 3 ) ( ( %s ` %s ) =/= 0 /\\ ( %s ` %s ) =/= 0 )' % (LFN, PTL('v', '-u U'), LFN, PTL('v', 'V')))
        self.f = c1_facts(w, c, self.yr, self.y100)
        self.dd = c([self.chi, w.inst('ef2ddl')], 'syl', DD(LFN, 'N'))
        self.hol, self.nr, self.n1, _, self.nz = dd_parts(w, A0, self.dd, LFN, 'N')
        self.ntr = c([self.tr], 'renegcld', '-u T e. RR'); self.nur = c([self.ur], 'renegcld', '-u U e. RR')

    def L(self, st, A):
        return lift(self.w, st, A)

    def corners(self, cc, x, y, xr, yr):
        w = self.w
        return [cc([xr, yr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (PTL(x, y), x)), cc([xr, yr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (PTL(x, y), y))]

    def reals(self, A):
        L = lambda st: self.L(st, A)
        return {'T': L(self.tr), 'U': L(self.ur), 'V': L(self.vr), 'S': L(self.sr), 'Y': L(self.yr)}


def elrab_unpack(w, A, x, X, body, q, qin):
    st, new = elrab_(w, x, X, body, q)
    both = w.s([qin, w.s([st], 'a1i', '( %s -> ( %s e. { %s e. %s | %s } <-> ( %s e. %s /\\ %s ) ) )' % (A, q, x, X, body, q, X, new))], 'mpbid', '( %s -> ( %s e. %s /\\ %s ) )' % (A, q, X, new))
    return w.s([both, w.inst('simpl')], 'syl', '( %s -> %s e. %s )' % (A, q, X)), w.s([both, w.inst('simpr')], 'syl', '( %s -> %s )' % (A, new)), new


def elrab_pack(w, A, x, X, body, q, qX, qb):
    st, new = elrab_(w, x, X, body, q)
    return w.s([w.s([qX, qb], 'jca', '( %s -> ( %s e. %s /\\ %s ) )' % (A, q, X, new)), w.s([st], 'a1i', '( %s -> ( %s e. { %s e. %s | %s } <-> ( %s e. %s /\\ %s ) ) )' % (A, q, x, X, body, q, X, new))],
               'mpbird', '( %s -> %s e. { %s e. %s | %s } )' % (A, q, x, X, body))


def cf_facts(E, A, qin):
    """q e. CFL: q e. CC, LFN q = 0, lin facts ( 1/2 <_ Re q <_ 1, -T <_ Im q <_ T ), leaves"""
    w = E.w
    cc = Ctx(w, A)
    BX = BOX('( 1 / 2 )', 'T')
    qbx, fz, _ = elrab_unpack(w, A, 'r', BX, '( %s ` r ) = 0' % LFN, 'q', qin)
    L = lambda st: E.L(st, A)
    half = numst(w, A, '( 1 / 2 )', 'RR'); one = numst(w, A, '1', 'RR')
    ac = ptc(cc, '( 1 / 2 )', '-u T', half, L(E.ntr)); bc = ptc(cc, '1', 'T', one, L(E.tr))
    bd = crect_bounds(w, A, ac, bc, qbx, BXA, BXB, 'q')
    hy = bd['le'] + E.corners(cc, '( 1 / 2 )', '-u T', half, L(E.ntr)) + E.corners(cc, '1', 'T', one, L(E.tr))
    lv = dict(bd['cl']); lv.update(E.reals(A))
    return dict(cc=bd['cc'], fz=fz, hy=hy, lv=lv)


def rf_facts(E, A, qin):
    """q e. RF: q e. CC, LFN q = 0, SIN facts and the crect bounds"""
    w = E.w
    cc = Ctx(w, A)
    X = '( %s crect %s )' % (RFA, RFB)
    body = '( ( %s ` p ) = 0 /\\ %s )' % (LFN, SIN('p', 'S', C1, '-u U', 'V'))
    qx, bq, new = elrab_unpack(w, A, 'p', X, body, 'q', qin)
    fz = cc([bq, w.inst('simpl')], 'syl', '( %s ` q ) = 0' % LFN)
    sn = cc([bq, w.inst('simpr')], 'syl', SIN('q', 'S', C1, '-u U', 'V'))
    s1, s2 = conj_split(w, A, sn)
    a1, a2 = conj_split(w, A, s1)
    b1, b2 = conj_split(w, A, s2)
    L = lambda st: E.L(st, A)
    ac = ptc(cc, 'S', '-u U', L(E.sr), L(E.nur)); bc = ptc(cc, C1, 'V', L(E.f['c1r']), L(E.vr))
    bd = crect_bounds(w, A, ac, bc, qx, RFA, RFB, 'q')
    lv = dict(bd['cl']); lv.update(E.reals(A)); lv[C1] = L(E.f['c1r'])
    return dict(cc=bd['cc'], fz=fz, hy=[a1, a2, b1, b2], lv=lv)


def bz_in(E, A, U_, ur, q, qcc, fz, hy, lv):
    """( A -> q e. BZ(LFN, U_) ) from lin facts 1/2 <_ Re q <_ 3/2, -U_ <_ Im q <_ U_"""
    w = E.w
    cc = Ctx(w, A)
    half, th = numst(w, A, '( 1 / 2 )', 'RR'), numst(w, A, '( 3 / 2 )', 'RR')
    nu = cc([ur], 'renegcld', '-u %s e. RR' % U_)
    ac = ptc(cc, '( 1 / 2 )', '-u %s' % U_, half, nu); bc = ptc(cc, '( 3 / 2 )', U_, th, ur)
    A_, B_ = '( ( 1 / 2 ) + ( _i x. -u %s ) )' % U_, '( ( 3 / 2 ) + ( _i x. %s ) )' % U_
    hy2 = hy + E.corners(cc, '( 1 / 2 )', '-u %s' % U_, half, nu) + E.corners(cc, '( 3 / 2 )', U_, th, ur)
    qin = crect_in(w, A, A_, B_, ac, bc, q, qcc, hy2, lv)
    return elrab_pack(w, A, 'r', '( %s crect %s )' % (A_, B_), '( %s ` r ) = 0' % LFN, q, qin, fz)


def gen_zs1():
    w = W('ef4zs1', 'Lean ` contour_ne_one ` , ` hCR ` : the zeros of the box ` [ 1 / 2 , 1 ] x [ - T , T ] ` outside the contour rectangle lie left of ` S ` , so their terms are at most ` 3 Y ^ S m / ( 1 + abs Im ) ` and their sum at most ` 72000 Y ^ S log ^ 2 ( N ( T + 2 ) ) ` ( ~ ef3wt ).')
    A0, G = ante_of(S['ef4zs1'])
    E = Env(w, A0)
    c = E.c
    D1 = '( %s \\ %s )' % (CFL, RF)
    Aq = '( %s /\\ q e. %s )' % (A0, D1)
    cq = Ctx(w, Aq)
    L = lambda st: E.L(st, Aq)
    qd = cq([], 'simpr', 'q e. %s' % D1)
    qcf = cq([qd, w.inst('eldifi')], 'syl', 'q e. %s' % CFL)
    qnr = cq([qd, w.inst('eldifn')], 'syl', '-. q e. %s' % RF)
    d = cf_facts(E, Aq, qcf)
    lv = d['lv']
    rq, iq = '( Re ` q )', '( Im ` q )'
    # Im q =/= -u U and Im q =/= V
    def im_ne(y_, which):
        A2 = '( %s /\\ %s = %s )' % (Aq, iq, y_)
        c2 = Ctx(w, A2)
        qe = c2([lift(w, d['cc'], A2), w.inst('replim')], 'syl', 'q = ( %s + ( _i x. %s ) )' % (rq, iq))
        qe2 = c2([qe, c2([c2([c2([], 'simpr', '%s = %s' % (iq, y_))], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (iq, y_))], 'oveq2d', '( %s + ( _i x. %s ) ) = %s' % (rq, iq, PTL(rq, y_)))], 'eqtrd', 'q = %s' % PTL(rq, y_))
        vin = icc_in(c2, rq, '( 1 / 2 )', '3', lift(w, lv[rq], A2), numst(w, A2, '( 1 / 2 )', 'RR'), numst(w, A2, '3', 'RR'),
                     lin8(w, A2, [lift(w, h, A2) for h in d['hy']], '( 1 / 2 ) <_ %s' % rq, {k: lift(w, v, A2) for k, v in lv.items()}),
                     lin8(w, A2, [lift(w, h, A2) for h in d['hy']], '%s <_ 3' % rq, {k: lift(w, v, A2) for k, v in lv.items()}))
        LB = '( ( %s ` %s ) =/= 0 /\\ ( %s ` %s ) =/= 0 )' % (LFN, PTL('v', '-u U'), LFN, PTL('v', 'V'))
        lb, lbn = ral_at(w, A2, lift(w, E.lines, A2), 'v', rq, LB, vin)
        ne = c2([lb, w.inst('simpl' if which == 0 else 'simpr')], 'syl', '( %s ` %s ) =/= 0' % (LFN, PTL(rq, y_)))
        ne2 = c2([ne, c2([c2([qe2], 'fveq2d', '( %s ` q ) = ( %s ` %s )' % (LFN, LFN, PTL(rq, y_)))], 'neeq1d', '( ( %s ` q ) =/= 0 <-> ( %s ` %s ) =/= 0 )' % (LFN, LFN, PTL(rq, y_)))], 'mpbird', '( %s ` q ) =/= 0' % LFN)
        n3 = c2([ne2], 'neneqd', '-. ( %s ` q ) = 0' % LFN)
        p = cq([lift(w, d['fz'], A2), n3], 'pm2.65da', '-. %s = %s' % (iq, y_))
        return cq([p], 'neqned', '%s =/= %s' % (iq, y_))
    nu = im_ne('-u U', 0)
    nv = im_ne('V', 1)
    lvq = dict(lv); lvq[C1] = L(E.f['c1r'])
    hyq = d['hy'] + [L(E.tu), L(E.tv), L(E.t2)]
    lo1 = lin8(w, Aq, hyq, '-u U <_ %s' % iq, lvq)
    hi1 = lin8(w, Aq, hyq, '%s <_ V' % iq, lvq)
    ltu = cq([cq([lo1, nu], 'jca', '( -u U <_ %s /\\ %s =/= -u U )' % (iq, iq)), cq([L(E.nur), lv[iq]], 'ltlend', '( -u U < %s <-> ( -u U <_ %s /\\ %s =/= -u U ) )' % (iq, iq, iq))], 'mpbird', '-u U < %s' % iq)
    ltv = cq([cq([hi1, cq([nv], 'necomd', 'V =/= %s' % iq)], 'jca', '( %s <_ V /\\ V =/= %s )' % (iq, iq)), cq([lv[iq], L(E.vr)], 'ltlend', '( %s < V <-> ( %s <_ V /\\ V =/= %s ) )' % (iq, iq, iq))], 'mpbird', '%s < V' % iq)
    # Re q <_ S
    A3 = '( %s /\\ S < %s )' % (Aq, rq)
    c3 = Ctx(w, A3)
    L3 = lambda st: lift(w, st, A3)
    lv3 = {k: L3(v) for k, v in lvq.items()}
    hy3 = [L3(h) for h in hyq] + [c3([], 'simpr', 'S < %s' % rq), L3(E.f['c1g']), L3(ltu), L3(ltv)]
    ac = ptc(c3, 'S', '-u U', L3(E.sr), L3(E.nur)); bc = ptc(c3, C1, 'V', L3(E.f['c1r']), L3(E.vr))
    hyc = hy3 + E.corners(c3, 'S', '-u U', L3(E.sr), L3(E.nur)) + E.corners(c3, C1, 'V', L3(E.f['c1r']), L3(E.vr))
    qx = crect_in(w, A3, RFA, RFB, ac, bc, 'q', L3(d['cc']), hyc, lv3)
    sin = conj(w, A3, SIN('q', 'S', C1, '-u U', 'V'), {'S < %s' % rq: c3([], 'simpr', 'S < %s' % rq), '%s < %s' % (rq, C1): lin8(w, A3, hy3, '%s < %s' % (rq, C1), lv3), '-u U < %s' % iq: L3(ltu), '%s < V' % iq: L3(ltv)})
    body = '( ( %s ` p ) = 0 /\\ %s )' % (LFN, SIN('p', 'S', C1, '-u U', 'V'))
    qrf = elrab_pack(w, A3, 'p', '( %s crect %s )' % (RFA, RFB), body, 'q', qx, c3([L3(d['fz']), sin], 'jca', '( ( %s ` q ) = 0 /\\ %s )' % (LFN, SIN('q', 'S', C1, '-u U', 'V'))))
    nsr = cq([qrf, lift(w, qnr, A3)], 'pm2.65da', '-. S < %s' % rq)
    rs = cq([nsr, cq([lv[rq], L(E.sr)], 'lenltd', '( %s <_ S <-> -. S < %s )' % (rq, rq))], 'mpbird', '%s <_ S' % rq)
    # q in the box BZ(T): orders in NN
    qbz = bz_in(E, Aq, 'T', L(E.tr), 'q', d['cc'], d['fz'], d['hy'], lvq)
    BZI = tsub(stmt('ef3bz'), {'F': LFN, 'A': 'N', 'U': 'T'})
    bza, bzc = ante_of(BZI)
    bzs = c([c([E.dd, E.tr], 'jca', bza), w.inst('ef3bz')], 'syl', bzc)
    bzf, bzo = conj_split(w, A0, bzs)
    mo = cq([qbz, cq([L(bzo), w.inst('rsp')], 'syl', '( q e. %s -> ( %s holord q ) e. NN )' % (BZT, LFN))], 'mpd', '( %s holord q ) e. NN' % LFN)
    m = M_
    mr = cq([mo], 'nnred', '%s e. RR' % m)
    m0 = cq([cq([mo], 'nnnn0d', '%s e. NN0' % m)], 'nn0ge0d', '0 <_ %s' % m)
    rq0 = lin8(w, Aq, d['hy'], '0 < %s' % rq, lvq)
    qne = ne0_re(cq, 'q', d['cc'], rq0)
    ap = cq([d['cc'], qne], 'absrpcld', '( abs ` q ) e. RR+')
    AQ = '( abs ` q )'
    aqr = cq([ap], 'rpred', '%s e. RR' % AQ)
    YRe, YS = '( Y ^c %s )' % rq, '( Y ^c S )'
    yp = L(E.f['yp'])
    yrer = cq([cq([yp, lv[rq]], 'rpcxpcld', '%s e. RR+' % YRe)], 'rpred', '%s e. RR' % YRe)
    ysp = cq([yp, L(E.sr)], 'rpcxpcld', '%s e. RR+' % YS)
    ysr = cq([ysp], 'rpred', '%s e. RR' % YS)
    yle = cq([rs, cq([L(E.yr), L(E.f['y1']), lv[rq], L(E.sr)], 'cxpled', '( %s <_ S <-> %s <_ %s )' % (rq, YRe, YS))], 'mpbid', '%s <_ %s' % (YRe, YS))
    W1 = '( 1 + ( abs ` %s ) )' % iq
    aim = cq([cq([lv[iq]], 'recnd', '%s e. CC' % iq)], 'abscld', '( abs ` %s ) e. RR' % iq)
    w1r = cq([numst(w, Aq, '1', 'RR'), aim], 'readdcld', '%s e. RR' % W1)
    w1p = cq([w1r, lin8(w, Aq, [cq([cq([lv[iq]], 'recnd', '%s e. CC' % iq)], 'absge0d', '0 <_ ( abs ` %s )' % iq)], '0 < %s' % W1, {'( abs ` %s )' % iq: aim})], 'elrpd', '%s e. RR+' % W1)
    w3 = lin8(w, Aq, d['hy'] + [cq([d['cc'], w.inst('releabs')], 'syl', '%s <_ %s' % (rq, AQ)), cq([d['cc'], w.inst('absimle')], 'syl', '( abs ` %s ) <_ %s' % (iq, AQ))],
              '%s <_ ( 3 x. %s )' % (W1, AQ), dict(lvq, **{AQ: aqr, '( abs ` %s )' % iq: aim}))
    d1 = cq([yrer, ysr, ap, yle], 'lediv1dd', '( %s / %s ) <_ ( %s / %s )' % (YRe, AQ, YS, AQ))
    Y3 = '( 3 x. %s )' % YS
    A3_ = '( 3 x. %s )' % AQ
    d2 = cq([cq([ysr], 'recnd', '%s e. CC' % YS), cq([aqr], 'recnd', '%s e. CC' % AQ), numst(w, Aq, '3', 'CC'), cq([ap], 'rpne0d', '%s =/= 0' % AQ), cq([numst(w, Aq, '3', 'RR+')], 'rpne0d', '3 =/= 0')],
            'divcan5d', '( %s / %s ) = ( %s / %s )' % (Y3, A3_, YS, AQ))
    y3r = cq([numst(w, Aq, '3', 'RR'), ysr], 'remulcld', '%s e. RR' % Y3)
    d3 = cq([w1p, cq([numst(w, Aq, '3', 'RR+'), ap], 'rpmulcld', '%s e. RR+' % A3_), y3r, lin8(w, Aq, [cq([ysp], 'rpge0d', '0 <_ %s' % YS)], '0 <_ %s' % Y3, {YS: ysr}), w3], 'lediv2ad',
            '( %s / %s ) <_ ( %s / %s )' % (Y3, A3_, Y3, W1))
    q1 = le_tr(w, Aq, d1, '( %s / %s )' % (YRe, AQ), '( %s / %s )' % (YS, AQ), cq([cq([d2], 'eqcomd', '( %s / %s ) = ( %s / %s )' % (YS, AQ, Y3, A3_)), d3], 'eqbrtrd', '( %s / %s ) <_ ( %s / %s )' % (YS, AQ, Y3, W1)), '( %s / %s )' % (Y3, W1))
    q2 = cq([cq([yrer, ap], 'rerpdivcld', '( %s / %s ) e. RR' % (YRe, AQ)), cq([y3r, w1p], 'rerpdivcld', '( %s / %s ) e. RR' % (Y3, W1)), mr, m0, q1], 'lemul2ad',
            '( %s x. ( %s / %s ) ) <_ ( %s x. ( %s / %s ) )' % (m, YRe, AQ, m, Y3, W1))
    WQq = '( %s / %s )' % (m, W1)
    q3 = cq([cq([mr], 'recnd', '%s e. CC' % m), cq([y3r], 'recnd', '%s e. CC' % Y3), cq([w1r], 'recnd', '%s e. CC' % W1)], 'div12d', '( %s x. ( %s / %s ) ) = ( %s x. %s )' % (m, Y3, W1, Y3, WQq))
    YQ = '( ( Y ^c q ) / q )'
    yqc = cq([cq([cq([yp], 'rpcnd', 'Y e. CC'), d['cc']], 'cxpcld', '( Y ^c q ) e. CC'), d['cc'], qne], 'divcld', '%s e. CC' % YQ)
    ab = cq([cq([cq([mr], 'recnd', '%s e. CC' % m), yqc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (RS1, m, YQ)),
             cq([cq([mr, m0], 'absidd', '( abs ` %s ) = %s' % (m, m)), cq([cq([cq([cq([yp], 'rpcnd', 'Y e. CC'), d['cc']], 'cxpcld', '( Y ^c q ) e. CC'), d['cc'], qne], 'absdivd', '( abs ` %s ) = ( ( abs ` ( Y ^c q ) ) / %s )' % (YQ, AQ)),
                                                                 cq([cq([yp, d['cc'], w.inst('abscxp')], 'syl2anc', '( abs ` ( Y ^c q ) ) = %s' % YRe)], 'oveq1d', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s / %s )' % (AQ, YRe, AQ))], 'eqtrd',
                                                                '( abs ` %s ) = ( %s / %s )' % (YQ, YRe, AQ))], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( %s / %s ) )' % (m, YQ, m, YRe, AQ))], 'eqtrd',
            '( abs ` %s ) = ( %s x. ( %s / %s ) )' % (RS1, m, YRe, AQ))
    pw = cq([cq([ab, q2], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( %s / %s ) )' % (RS1, m, Y3, W1)), q3], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (RS1, Y3, WQq))
    gc = cq([cq([mr], 'recnd', '%s e. CC' % m), yqc], 'mulcld', '%s e. CC' % RS1)
    # sums
    ssb = c([w.s([qbz], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, D1, BZT))], 'ssrdv', '%s C_ %s' % (D1, BZT))
    fin = c([bzf, ssb], 'ssfid', '%s e. Fin' % D1)
    SG, SA, SW = 'sum_ q e. %s %s' % (D1, RS1), 'sum_ q e. %s ( abs ` %s )' % (D1, RS1), 'sum_ q e. %s %s' % (D1, WQq)
    s1 = c([fin, gc], 'fsumabs', '( abs ` %s ) <_ %s' % (SG, SA))
    wqr = cq([mr, w1p], 'rerpdivcld', '%s e. RR' % WQq)
    s2 = c([fin, cq([gc], 'abscld', '( abs ` %s ) e. RR' % RS1), cq([y3r, wqr], 'remulcld', '( %s x. %s ) e. RR' % (Y3, WQq)), pw], 'fsumle', '%s <_ sum_ q e. %s ( %s x. %s )' % (SA, D1, Y3, WQq))
    y3c = c([numst(w, A0, '3', 'RR'), c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpred', '%s e. RR' % YS)], 'remulcld', '%s e. RR' % Y3)
    s3 = c([fin, c([y3c], 'recnd', '%s e. CC' % Y3), cq([wqr], 'recnd', '%s e. CC' % WQq)], 'fsummulc2', '( %s x. %s ) = sum_ q e. %s ( %s x. %s )' % (Y3, SW, D1, Y3, WQq))
    WT = tsub(stmt('ef3wt'), {'F': LFN, 'A': 'N', 'U': 'T', 'G': D1})
    wta, wtc = ante_of(WT)
    wt = c([conj(w, A0, wta, {DD(LFN, 'N'): E.dd, 'T e. RR': E.tr, '2 <_ T': E.t2, '%s C_ %s' % (D1, BZT): ssb}), w.inst('ef3wt')], 'syl', wtc)
    KWL = '( ; ; ; ; 2 4 0 0 0 x. ( %s ^ 2 ) )' % LNT
    swr = c([fin, wqr], 'fsumrecl', '%s e. RR' % SW)
    ntp = c([c([E.nr, lin8(w, A0, [E.n1], '0 < N', {'N': E.nr})], 'elrpd', 'N e. RR+'), c([c([E.tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 2 )', {'T': E.tr})], 'elrpd', '( T + 2 ) e. RR+')], 'rpmulcld', '( N x. ( T + 2 ) ) e. RR+')
    lnr = c([ntp], 'relogcld', '%s e. RR' % LNT)
    kwr = c([numst(w, A0, '; ; ; ; 2 4 0 0 0', 'RR'), c([lnr], 'resqcld', '( %s ^ 2 ) e. RR' % LNT)], 'remulcld', '%s e. RR' % KWL)
    s4 = c([swr, kwr, y3c, lin8(w, A0, [c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpge0d', '0 <_ %s' % YS)], '0 <_ %s' % Y3, {YS: c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpred', '%s e. RR' % YS)}), wt],
           'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (Y3, SW, Y3, KWL))
    cl = Closure(w, A0, {YS: ('RR', c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpred', '%s e. RR' % YS)), LNT: ('RR', lnr)})
    cl.atom(YS); cl.atom(LNT)
    RHS = '( ( ; ; ; ; 7 2 0 0 0 x. %s ) x. ( %s ^ 2 ) )' % (YS, LNT)
    s5 = ringeq(w, A0, '( %s x. %s )' % (Y3, KWL), RHS, cl)
    t1 = le_tr(w, A0, s1, '( abs ` %s )' % SG, SA, c([s2, c([s3], 'eqcomd', 'sum_ q e. %s ( %s x. %s ) = ( %s x. %s )' % (D1, Y3, WQq, Y3, SW))], 'breqtrd', '%s <_ ( %s x. %s )' % (SA, Y3, SW)), '( %s x. %s )' % (Y3, SW))
    t2_ = le_tr(w, A0, t1, '( abs ` %s )' % SG, '( %s x. %s )' % (Y3, SW), c([s4, s5], 'breqtrd', '( %s x. %s ) <_ %s' % (Y3, SW, RHS)), RHS)
    w.qed([t2_], 'idi', S['ef4zs1'])
    return run8(w)



def gen_zs2():
    w = W('ef4zs2', 'Lean ` contour_ne_one ` , ` hRC ` : the zeros inside the contour rectangle outside the box ` [ 1 / 2 , 1 ] x [ - T , T ] ` have ` Re <_ 1 ` ( ` DiskData ` ), ` q =/= 1 ` ( ~ ef4l1 ), ` T < abs Im <_ T + 1 ` , so their terms are at most ` ( Y / T ) m ` and their sum at most ` 1600 Y log ( N ( T + 4 ) ) / T ` ( ~ ef4bm ).')
    A0, G = ante_of(S['ef4zs2'])
    E = Env(w, A0)
    c = E.c
    D2 = '( %s \\ %s )' % (RF, CFL)
    Aq = '( %s /\\ q e. %s )' % (A0, D2)
    cq = Ctx(w, Aq)
    L = lambda st: E.L(st, Aq)
    qd = cq([], 'simpr', 'q e. %s' % D2)
    qrf = cq([qd, w.inst('eldifi')], 'syl', 'q e. %s' % RF)
    qnc = cq([qd, w.inst('eldifn')], 'syl', '-. q e. %s' % CFL)
    d = rf_facts(E, Aq, qrf)
    lv = d['lv']
    rq, iq = '( Re ` q )', '( Im ` q )'
    hyb = d['hy'] + [L(E.s916), L(E.tu), L(E.tv), L(E.u1), L(E.v1), L(E.t2)]
    rq0 = lin8(w, Aq, hyb, '0 < %s' % rq, lv)
    qh = hp0_mem(cq, 'q', d['cc'], None, rq0)
    nzq, _ = ral_at(w, Aq, L(E.nz), 'w', 'q', '( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN, qh)
    nn_ = cq([d['fz'], cq.a1(w.s([], 'nne', '( -. ( %s ` q ) =/= 0 <-> ( %s ` q ) = 0 )' % (LFN, LFN)), '( -. ( %s ` q ) =/= 0 <-> ( %s ` q ) = 0 )' % (LFN, LFN))], 'mpbird', '-. ( %s ` q ) =/= 0' % LFN)
    n1 = cq([nn_, nzq], 'mtod', '-. 1 < %s' % rq)
    r1 = cq([n1, cq([lv[rq], numst(w, Aq, '1', 'RR')], 'lenltd', '( %s <_ 1 <-> -. 1 < %s )' % (rq, rq))], 'mpbird', '%s <_ 1' % rq)
    # T < abs Im q
    aim = cq([cq([lv[iq]], 'recnd', '%s e. CC' % iq)], 'abscld', '( abs ` %s ) e. RR' % iq)
    A3 = '( %s /\\ ( abs ` %s ) <_ T )' % (Aq, iq)
    c3 = Ctx(w, A3)
    L3 = lambda st: lift(w, st, A3)
    ab3 = c3([c3([], 'simpr', '( abs ` %s ) <_ T' % iq), c3([L3(lv[iq]), L3(E.tr)], 'absled', '( ( abs ` %s ) <_ T <-> ( -u T <_ %s /\\ %s <_ T ) )' % (iq, iq, iq))], 'mpbid', '( -u T <_ %s /\\ %s <_ T )' % (iq, iq))
    i1, i2 = conj_split(w, A3, ab3)
    half = numst(w, A3, '( 1 / 2 )', 'RR'); one = numst(w, A3, '1', 'RR')
    bac = ptc(c3, '( 1 / 2 )', '-u T', half, L3(E.ntr)); bbc = ptc(c3, '1', 'T', one, L3(E.tr))
    hy3 = [L3(h) for h in hyb] + [L3(r1), i1, i2] + E.corners(c3, '( 1 / 2 )', '-u T', half, L3(E.ntr)) + E.corners(c3, '1', 'T', one, L3(E.tr))
    lv3 = {k: L3(v) for k, v in lv.items()}
    qbx = crect_in(w, A3, BXA, BXB, bac, bbc, 'q', L3(d['cc']), hy3, lv3)
    qcf = elrab_pack(w, A3, 'r', BOX('( 1 / 2 )', 'T'), '( %s ` r ) = 0' % LFN, 'q', qbx, L3(d['fz']))
    nt = cq([qcf, lift(w, qnc, A3)], 'pm2.65da', '-. ( abs ` %s ) <_ T' % iq)
    tlt = cq([nt, cq([L(E.tr), aim], 'ltnled', '( T < ( abs ` %s ) <-> -. ( abs ` %s ) <_ T )' % (iq, iq))], 'mpbird', 'T < ( abs ` %s )' % iq)
    t1r = cq([L(E.tr), numst(w, Aq, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    ale = cq([cq([lin8(w, Aq, hyb, '-u ( T + 1 ) <_ %s' % iq, lv), lin8(w, Aq, hyb, '%s <_ ( T + 1 )' % iq, lv)], 'jca', '( -u ( T + 1 ) <_ %s /\\ %s <_ ( T + 1 ) )' % (iq, iq)),
              cq([lv[iq], t1r], 'absled', '( ( abs ` %s ) <_ ( T + 1 ) <-> ( -u ( T + 1 ) <_ %s /\\ %s <_ ( T + 1 ) ) )' % (iq, iq, iq))], 'mpbird', '( abs ` %s ) <_ ( T + 1 )' % iq)
    BQ = tsub(BAND, {'F': LFN, 'p': 'q'})
    band = conj(w, Aq, BQ, {'( %s ` q ) = 0' % LFN: d['fz'], '( 1 / 2 ) <_ %s' % rq: lin8(w, Aq, hyb, '( 1 / 2 ) <_ %s' % rq, lv), '%s <_ ( 3 / 2 )' % rq: lin8(w, Aq, [r1], '%s <_ ( 3 / 2 )' % rq, lv),
                            'T < ( abs ` %s )' % iq: tlt, '( abs ` %s ) <_ ( T + 1 )' % iq: ale})
    # orders: q in BZ ( T + 1 )
    lvb = dict(lv); lvb['( T + 1 )'] = t1r
    qbz = bz_in(E, Aq, '( T + 1 )', t1r, 'q', d['cc'], d['fz'], hyb + [r1], lv)
    BZ1 = BZ(LFN, '( T + 1 )')
    BZI = tsub(stmt('ef3bz'), {'F': LFN, 'A': 'N', 'U': '( T + 1 )'})
    bza, bzc = ante_of(BZI)
    bzs = c([c([E.dd, c([E.tr, numst(w, A0, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')], 'jca', bza), w.inst('ef3bz')], 'syl', bzc)
    bzf, bzo = conj_split(w, A0, bzs)
    mo = cq([qbz, cq([L(bzo), w.inst('rsp')], 'syl', '( q e. %s -> ( %s holord q ) e. NN )' % (BZ1, LFN))], 'mpd', '( %s holord q ) e. NN' % LFN)
    m = M_
    mr = cq([mo], 'nnred', '%s e. RR' % m)
    m0 = cq([cq([mo], 'nnnn0d', '%s e. NN0' % m)], 'nn0ge0d', '0 <_ %s' % m)
    qne = ne0_re(cq, 'q', d['cc'], rq0)
    ap = cq([d['cc'], qne], 'absrpcld', '( abs ` q ) e. RR+')
    AQ = '( abs ` q )'
    aqr = cq([ap], 'rpred', '%s e. RR' % AQ)
    yp = L(E.f['yp'])
    YRe = '( Y ^c %s )' % rq
    yrer = cq([cq([yp, lv[rq]], 'rpcxpcld', '%s e. RR+' % YRe)], 'rpred', '%s e. RR' % YRe)
    y1_ = cq([cq([r1, cq([L(E.yr), L(E.f['y1']), lv[rq], numst(w, Aq, '1', 'RR')], 'cxpled', '( %s <_ 1 <-> %s <_ ( Y ^c 1 ) )' % (rq, YRe))], 'mpbid', '%s <_ ( Y ^c 1 )' % YRe),
              cq([cq([L(E.yr)], 'recnd', 'Y e. CC'), w.inst('cxp1')], 'syl', '( Y ^c 1 ) = Y')], 'breqtrd', '%s <_ Y' % YRe)
    tq = lin8(w, Aq, [tlt, cq([d['cc'], w.inst('absimle')], 'syl', '( abs ` %s ) <_ %s' % (iq, AQ))], 'T <_ %s' % AQ, {'T': L(E.tr), '( abs ` %s )' % iq: aim, AQ: aqr})
    tp = cq([L(E.tr), lin8(w, Aq, [L(E.t2)], '0 < T', {'T': L(E.tr)})], 'elrpd', 'T e. RR+')
    d1 = cq([yrer, L(E.yr), ap, y1_], 'lediv1dd', '( %s / %s ) <_ ( Y / %s )' % (YRe, AQ, AQ))
    d2 = cq([tp, ap, L(E.yr), lin8(w, Aq, [L(E.y100)], '0 <_ Y', {'Y': L(E.yr)}), tq], 'lediv2ad', '( Y / %s ) <_ ( Y / T )' % AQ)
    q1 = le_tr(w, Aq, d1, '( %s / %s )' % (YRe, AQ), '( Y / %s )' % AQ, d2, '( Y / T )')
    q2 = cq([cq([yrer, ap], 'rerpdivcld', '( %s / %s ) e. RR' % (YRe, AQ)), cq([L(E.yr), tp], 'rerpdivcld', '( Y / T ) e. RR'), mr, m0, q1], 'lemul2ad', '( %s x. ( %s / %s ) ) <_ ( %s x. ( Y / T ) )' % (m, YRe, AQ, m))
    q3 = cq([cq([mr], 'recnd', '%s e. CC' % m), cq([cq([L(E.yr), tp], 'rerpdivcld', '( Y / T ) e. RR')], 'recnd', '( Y / T ) e. CC')], 'mulcomd', '( %s x. ( Y / T ) ) = ( ( Y / T ) x. %s )' % (m, m))
    YQ = '( ( Y ^c q ) / q )'
    yqc = cq([cq([cq([yp], 'rpcnd', 'Y e. CC'), d['cc']], 'cxpcld', '( Y ^c q ) e. CC'), d['cc'], qne], 'divcld', '%s e. CC' % YQ)
    ab = cq([cq([cq([mr], 'recnd', '%s e. CC' % m), yqc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (RS1, m, YQ)),
             cq([cq([mr, m0], 'absidd', '( abs ` %s ) = %s' % (m, m)), cq([cq([cq([cq([yp], 'rpcnd', 'Y e. CC'), d['cc']], 'cxpcld', '( Y ^c q ) e. CC'), d['cc'], qne], 'absdivd', '( abs ` %s ) = ( ( abs ` ( Y ^c q ) ) / %s )' % (YQ, AQ)),
                                                                 cq([cq([yp, d['cc'], w.inst('abscxp')], 'syl2anc', '( abs ` ( Y ^c q ) ) = %s' % YRe)], 'oveq1d', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s / %s )' % (AQ, YRe, AQ))], 'eqtrd',
                                                                '( abs ` %s ) = ( %s / %s )' % (YQ, YRe, AQ))], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( %s / %s ) )' % (m, YQ, m, YRe, AQ))], 'eqtrd',
            '( abs ` %s ) = ( %s x. ( %s / %s ) )' % (RS1, m, YRe, AQ))
    pw = cq([cq([ab, q2], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( Y / T ) )' % (RS1, m)), q3], 'breqtrd', '( abs ` %s ) <_ ( ( Y / T ) x. %s )' % (RS1, m))
    gc = cq([cq([mr], 'recnd', '%s e. CC' % m), yqc], 'mulcld', '%s e. CC' % RS1)
    # sums
    ssb = c([w.s([qbz], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, D2, BZ1))], 'ssrdv', '%s C_ %s' % (D2, BZ1))
    fin = c([bzf, ssb], 'ssfid', '%s e. Fin' % D2)
    SG, SA, SM = 'sum_ q e. %s %s' % (D2, RS1), 'sum_ q e. %s ( abs ` %s )' % (D2, RS1), 'sum_ q e. %s %s' % (D2, m)
    YT_ = '( Y / T )'
    tpp = c([E.tr, lin8(w, A0, [E.t2], '0 < T', {'T': E.tr})], 'elrpd', 'T e. RR+')
    ytr = c([E.yr, tpp], 'rerpdivcld', '%s e. RR' % YT_)
    s1 = c([fin, gc], 'fsumabs', '( abs ` %s ) <_ %s' % (SG, SA))
    s2 = c([fin, cq([gc], 'abscld', '( abs ` %s ) e. RR' % RS1), cq([lift(w, ytr, Aq), mr], 'remulcld', '( %s x. %s ) e. RR' % (YT_, m)), pw], 'fsumle', '%s <_ sum_ q e. %s ( %s x. %s )' % (SA, D2, YT_, m))
    s3 = c([fin, c([ytr], 'recnd', '%s e. CC' % YT_), cq([mr], 'recnd', '%s e. CC' % m)], 'fsummulc2', '( %s x. %s ) = sum_ q e. %s ( %s x. %s )' % (YT_, SM, D2, YT_, m))
    alb = c([band], 'ralrimiva', 'A. q e. %s %s' % (D2, BQ))
    RFo = ZR('S', C1, '-u U', 'V', LFN).replace('{ p e.', '{ o e.').replace('` p )', '` o )')
    D2o = '( %s \\ %s )' % (RFo, CFL)
    rbody = '( ( %s ` p ) = 0 /\\ %s )' % (LFN, SIN('p', 'S', C1, '-u U', 'V'))
    ceq, _ = w.wcongr(rbody, {'p': 'o'}, 'p = o', {'p': w.s([], 'id', '( p = o -> p = o )')})
    rfe = w.s([ceq], 'cbvrabv', '%s = %s' % (RF, RFo))
    de = c.a1(w.s([rfe], 'difeq1i', '%s = %s' % (D2, D2o)), '%s = %s' % (D2, D2o))
    alb2 = c([alb, c([de], 'raleqdv', '( A. q e. %s %s <-> A. q e. %s %s )' % (D2, BQ, D2o, BQ))], 'mpbid', 'A. q e. %s %s' % (D2o, BQ))
    cbb, _ = cbvral(w, D2o, 'q', 'p', BQ)
    BP = tsub(BAND, {'F': LFN})
    alp = c([alb2, c.a1(cbb, '( A. q e. %s %s <-> A. p e. %s %s )' % (D2o, BQ, D2o, BP))], 'mpbid', 'A. p e. %s %s' % (D2o, BP))
    dcc = c([c([de], 'eqcomd', '%s = %s' % (D2o, D2)), c([w.s([d['cc']], 'ex', '( %s -> ( q e. %s -> q e. CC ) )' % (A0, D2))], 'ssrdv', '%s C_ CC' % D2)], 'eqsstrd', '%s C_ CC' % D2o)
    BM = tsub(stmt('ef4bm'), {'F': LFN, 'A': 'N', 'G': D2o})
    bma, bmc = ante_of(BM)
    bm0 = c([conj(w, A0, bma, {DD(LFN, 'N'): E.dd, 'T e. RR': E.tr, '2 <_ T': E.t2, '%s C_ CC' % D2o: dcc, 'A. p e. %s %s' % (D2o, BP): alp}), w.inst('ef4bm')], 'syl', bmc)
    bm = c([c([de], 'sumeq1d', '%s = sum_ q e. %s %s' % (SM, D2o, m)), bm0], 'eqbrtrd', bmc.replace('sum_ q e. %s' % D2o, 'sum_ q e. %s' % D2))
    smr = c([fin, cq([mo], 'nnred', '%s e. RR' % m)], 'fsumrecl', '%s e. RR' % SM)
    KBL = '( %s x. %s )' % (KB, LN4)
    n4p = c([c([E.nr, lin8(w, A0, [E.n1], '0 < N', {'N': E.nr})], 'elrpd', 'N e. RR+'), c([c([E.tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 4 )', {'T': E.tr})], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( N x. ( T + 4 ) ) e. RR+')
    l4r = c([n4p], 'relogcld', '%s e. RR' % LN4)
    kbr = c([numst(w, A0, KB, 'RR'), l4r], 'remulcld', '%s e. RR' % KBL)
    yt0 = c([E.yr, tpp, lin8(w, A0, [E.y100], '0 <_ Y', {'Y': E.yr})], 'divge0d', '0 <_ %s' % YT_)
    s4 = c([smr, kbr, ytr, yt0, bm], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (YT_, SM, YT_, KBL))
    RT = '( 1 / T )'
    rtr = c([tpp], 'rpreccld', '%s e. RR+' % RT)
    e1 = c([c([E.yr], 'recnd', 'Y e. CC'), c([tpp], 'rpcnd', 'T e. CC'), c([tpp], 'rpne0d', 'T =/= 0')], 'divrecd', '%s = ( Y x. %s )' % (YT_, RT))
    e2 = c([c([l4r], 'recnd', '%s e. CC' % LN4), c([tpp], 'rpcnd', 'T e. CC'), c([tpp], 'rpne0d', 'T =/= 0')], 'divrecd', '( %s / T ) = ( %s x. %s )' % (LN4, LN4, RT))
    cl = Closure(w, A0, {'Y': ('RR', E.yr), LN4: ('RR', l4r), RT: ('RR', c([rtr], 'rpred', '%s e. RR' % RT))})
    for k in ('Y', LN4, RT):
        cl.atom(k)
    RHS = '( ( %s x. Y ) x. ( %s / T ) )' % (KB, LN4)
    e3 = ringeq(w, A0, '( ( Y x. %s ) x. %s )' % (RT, KBL), '( ( %s x. Y ) x. ( %s x. %s ) )' % (KB, LN4, RT), cl)
    e4 = c([c([c([e1], 'oveq1d', '( %s x. %s ) = ( ( Y x. %s ) x. %s )' % (YT_, KBL, RT, KBL)), e3], 'eqtrd', '( %s x. %s ) = ( ( %s x. Y ) x. ( %s x. %s ) )' % (YT_, KBL, KB, LN4, RT)),
            c([c([e2], 'eqcomd', '( %s x. %s ) = ( %s / T )' % (LN4, RT, LN4))], 'oveq2d', '( ( %s x. Y ) x. ( %s x. %s ) ) = %s' % (KB, LN4, RT, RHS))], 'eqtrd', '( %s x. %s ) = %s' % (YT_, KBL, RHS))
    t1 = le_tr(w, A0, s1, '( abs ` %s )' % SG, SA, c([s2, c([s3], 'eqcomd', 'sum_ q e. %s ( %s x. %s ) = ( %s x. %s )' % (D2, YT_, m, YT_, SM))], 'breqtrd', '%s <_ ( %s x. %s )' % (SA, YT_, SM)), '( %s x. %s )' % (YT_, SM))
    t2_ = le_tr(w, A0, t1, '( abs ` %s )' % SG, '( %s x. %s )' % (YT_, SM), c([s4, e4], 'breqtrd', '( %s x. %s ) <_ %s' % (YT_, SM, RHS)), RHS)
    w.qed([t2_], 'idi', S['ef4zs2'])
    return run8(w)



def gen_zs(scc=False):
    w = W('ef4scc', 'The contract zero sum ` SC ` and the contour residue sum ` SR ` are complex numbers (finite sums over zeros in ` BZ ( T + 1 ) ` ).') if scc else W('ef4zs', 'Lean ` contour_ne_one ` , ` hadj ` : the contract zero sum ` SC ` (zeros of ` E ` off 1 in ` [ 1 / 2 , 1 ] x [ - T , T ] ` ) differs from the contour residue sum ` SR ` by at most ` 72000 Y ^ S log ^ 2 ( N ( T + 2 ) ) + 1600 Y log ( N ( T + 4 ) ) / T ` ( ~ ef4zf , ~ ef4ssd , ~ ef4zs1 , ~ ef4zs2 ).')
    A0, G = ante_of(S['ef4scc'] if scc else S['ef4zs'])
    E = Env(w, A0)
    c = E.c
    ZE = tsub(stmt('ef4zf'), {'A': '( 1 / 2 )'})
    zea, zec = ante_of(ZE)
    half = numst(w, A0, '( 1 / 2 )', 'RR')
    ze = c([conj(w, A0, zea, {CHI: E.chi, '( 1 / 2 ) e. RR': half, '0 < ( 1 / 2 )': c.a1(w.s([], 'halfgt0', '0 < ( 1 / 2 )'), '0 < ( 1 / 2 )'),
                              '( 1 / 2 ) <_ 1': c.a1(w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], '1re', '1 e. RR'), w.s([], 'halflt1', '( 1 / 2 ) < 1')], 'ltleii', '( 1 / 2 ) <_ 1'), '( 1 / 2 ) <_ 1'),
                              'T e. RR': E.tr}), w.inst('ef4zf')], 'syl', zec)
    zeq, zord = conj_split(w, A0, ze)
    EH = '( ( N DChrLF X ) holord q )'
    TE = '( %s x. ( ( Y ^c q ) / q ) )' % EH
    Aq = '( %s /\\ q e. %s )' % (A0, ZFE)
    cq = Ctx(w, Aq)
    oq = cq([cq([], 'simpr', 'q e. %s' % ZFE), cq([lift(w, zord, Aq), w.inst('rsp')], 'syl', '( q e. %s -> %s = %s )' % (ZFE, EH, M_))], 'mpd', '%s = %s' % (EH, M_))
    s1 = c([cq([oq], 'oveq1d', '%s = %s' % (TE, RS1))], 'sumeq2dv', '%s = sum_ q e. %s %s' % (SCE, ZFE, RS1))
    s2 = c([s1, c([zeq], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (ZFE, RS1, CFL, RS1))], 'eqtrd', '%s = sum_ q e. %s %s' % (SCE, CFL, RS1))
    # finiteness and closure through BZ ( T + 1 )
    t1r = c([E.tr, numst(w, A0, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    BZ1 = BZ(LFN, '( T + 1 )')
    BZI = tsub(stmt('ef3bz'), {'F': LFN, 'A': 'N', 'U': '( T + 1 )'})
    bza, bzc = ante_of(BZI)
    bzs = c([c([E.dd, t1r], 'jca', bza), w.inst('ef3bz')], 'syl', bzc)
    bzf, bzo = conj_split(w, A0, bzs)
    def into_bz(which):
        A1 = '( %s /\\ q e. %s )' % (A0, CFL if which == 'c' else RF)
        L1 = lambda st: lift(w, st, A1)
        qin = w.s([], 'simpr', '( %s -> q e. %s )' % (A1, CFL if which == 'c' else RF))
        d = cf_facts(E, A1, qin) if which == 'c' else rf_facts(E, A1, qin)
        hy = d['hy'] + [L1(E.s916), L1(E.tu), L1(E.tv), L1(E.u1), L1(E.v1), L1(E.t2), L1(E.f['c54'])]
        lv = dict(d['lv']); lv[C1] = L1(E.f['c1r']); lv['( T + 1 )'] = L1(t1r)
        qb = bz_in(E, A1, '( T + 1 )', L1(t1r), 'q', d['cc'], d['fz'], hy, lv)
        return c([w.s([qb], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, CFL if which == 'c' else RF, BZ1))], 'ssrdv', '%s C_ %s' % (CFL if which == 'c' else RF, BZ1))
    cs, rs_ = into_bz('c'), into_bz('r')
    cf = c([bzf, cs], 'ssfid', '%s e. Fin' % CFL)
    rf = c([bzf, rs_], 'ssfid', '%s e. Fin' % RF)
    U_ = '( %s u. %s )' % (CFL, RF)
    us = c([cs, rs_], 'unssd', '%s C_ %s' % (U_, BZ1))
    Au = '( %s /\\ q e. %s )' % (A0, U_)
    cu = Ctx(w, Au)
    qbz = cu([lift(w, us, Au), cu([], 'simpr', 'q e. %s' % U_)], 'sseldd', 'q e. %s' % BZ1)
    mo = cu([qbz, cu([lift(w, bzo, Au), w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (BZ1, M_))], 'mpd', '%s e. NN' % M_)
    qx, qfz, _ = elrab_unpack(w, Au, 'r', '( ( ( 1 / 2 ) + ( _i x. -u ( T + 1 ) ) ) crect ( ( 3 / 2 ) + ( _i x. ( T + 1 ) ) ) )', '( %s ` r ) = 0' % LFN, 'q', qbz)
    half_u = numst(w, Au, '( 1 / 2 )', 'RR'); th_u = numst(w, Au, '( 3 / 2 )', 'RR')
    nt1 = cu([lift(w, t1r, Au)], 'renegcld', '-u ( T + 1 ) e. RR')
    bd = crect_bounds(w, Au, ptc(cu, '( 1 / 2 )', '-u ( T + 1 )', half_u, nt1), ptc(cu, '( 3 / 2 )', '( T + 1 )', th_u, lift(w, t1r, Au)), qx,
                      '( ( 1 / 2 ) + ( _i x. -u ( T + 1 ) ) )', '( ( 3 / 2 ) + ( _i x. ( T + 1 ) ) )', 'q')
    rq0 = lin8(w, Au, [bd['le'][0]] + E.corners(cu, '( 1 / 2 )', '-u ( T + 1 )', half_u, nt1), '0 < ( Re ` q )', dict(bd['cl']))
    qne = ne0_re(cu, 'q', bd['cc'], rq0)
    yqc = cu([cu([cu([lift(w, E.f['yp'], Au)], 'rpcnd', 'Y e. CC'), bd['cc']], 'cxpcld', '( Y ^c q ) e. CC'), bd['cc'], qne], 'divcld', '( ( Y ^c q ) / q ) e. CC')
    tc = cu([cu([mo], 'nncnd', '%s e. CC' % M_), yqc], 'mulcld', '%s e. CC' % RS1)
    if scc:
        def fsum_on(X, fin, base):
            Ax = '( %s /\\ q e. %s )' % (A0, X)
            qu = w.s([w.s([], 'simpr', '( %s -> q e. %s )' % (Ax, X)), w.inst('elun1' if base == 'c' else 'elun2')], 'syl', '( %s -> q e. %s )' % (Ax, U_))
            tcx = w.s([qu, w.s([w.s([tc], 'ex', '( %s -> ( q e. %s -> %s e. CC ) )' % (A0, U_, RS1))], 'adantr', '( %s -> ( q e. %s -> %s e. CC ) )' % (Ax, U_, RS1))], 'mpd', '( %s -> %s e. CC )' % (Ax, RS1))
            return c([fin, tcx], 'fsumcl', 'sum_ q e. %s %s e. CC' % (X, RS1))
        sc_ = c([s2, fsum_on(CFL, cf, 'c')], 'eqeltrd', '%s e. CC' % SCE)
        w.qed([c([sc_, fsum_on(RF, rf, 'r')], 'jca', G)], 'idi', S['ef4scc'])
        return run8(w)
    SD = tsub(stmt('ef4ssd'), {'A': CFL, 'B': RF, 'C': RS1, 'ph': A0})
    sd = w.s([cf, rf, tc], 'ef4ssd', SD)
    S1_, S2_ = 'sum_ q e. ( %s \\ %s ) %s' % (CFL, RF, RS1), 'sum_ q e. ( %s \\ %s ) %s' % (RF, CFL, RS1)
    e1 = c([c([s2], 'oveq1d', '( %s - %s ) = ( sum_ q e. %s %s - %s )' % (SCE, SRL, CFL, RS1, SRL)), sd], 'eqtrd', '( %s - %s ) = ( %s - %s )' % (SCE, SRL, S1_, S2_))
    def fsc(X, fin):
        Ax = '( %s /\\ q e. %s )' % (A0, X)
        base = CFL if X.startswith('( %s' % CFL) else RF
        un = lift(w, c.a1(w.s([], 'difss', '%s C_ %s' % (X, base)), '%s C_ %s' % (X, base)), Ax)
        qb = w.s([un, w.s([], 'simpr', '( %s -> q e. %s )' % (Ax, X))], 'sseldd', '( %s -> q e. %s )' % (Ax, base))
        qu = w.s([qb, w.inst('elun1' if base == CFL else 'elun2')], 'syl', '( %s -> q e. %s )' % (Ax, U_))
        tcx = w.s([qu, w.s([w.s([tc], 'ex', '( %s -> ( q e. %s -> %s e. CC ) )' % (A0, U_, RS1))], 'adantr', '( %s -> ( q e. %s -> %s e. CC ) )' % (Ax, U_, RS1))], 'mpd', '( %s -> %s e. CC )' % (Ax, RS1))
        return c([c([fin, c.a1(w.s([], 'difss', '%s C_ %s' % (X, base)), '%s C_ %s' % (X, base))], 'ssfid', '%s e. Fin' % X), tcx], 'fsumcl', 'sum_ q e. %s %s e. CC' % (X, RS1))
    c1s = fsc('( %s \\ %s )' % (CFL, RF), cf)
    c2s = fsc('( %s \\ %s )' % (RF, CFL), rf)
    ad = c([c1s, c2s, w.inst('abs2dif2')], 'syl2anc', '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (S1_, S2_, S1_, S2_))
    z1 = w.s([], 'ef4zs1', stmt('ef4zs1'))
    z2 = w.s([], 'ef4zs2', stmt('ef4zs2'))
    B1, B2 = ante_of(stmt('ef4zs1'))[1].split(' <_ ', 1)[1], ante_of(stmt('ef4zs2'))[1].split(' <_ ', 1)[1]
    la = c([c([c1s], 'abscld', '( abs ` %s ) e. RR' % S1_), c([c2s], 'abscld', '( abs ` %s ) e. RR' % S2_), cl_re(w, A0, E, B1), cl_re(w, A0, E, B2), z1, z2], 'le2addd',
           '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s + %s )' % (S1_, S2_, B1, B2))
    fin_ = le_tr(w, A0, c([c([e1], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (SCE, SRL, S1_, S2_)), ad], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (SCE, SRL, S1_, S2_)),
                 '( abs ` ( %s - %s ) )' % (SCE, SRL), '( ( abs ` %s ) + ( abs ` %s ) )' % (S1_, S2_), la, '( %s + %s )' % (B1, B2))
    w.qed([fin_], 'idi', S['ef4zs'])
    return run8(w)


def cl_re(w, A0, E, B):
    """( A0 -> B e. RR ) for the two zero-sum bounds"""
    c = E.c
    YS = '( Y ^c S )'
    ysr = c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpred', '%s e. RR' % YS)
    tpp = c([E.tr, lin8(w, A0, [E.t2], '0 < T', {'T': E.tr})], 'elrpd', 'T e. RR+')
    np_ = c([E.nr, lin8(w, A0, [E.n1], '0 < N', {'N': E.nr})], 'elrpd', 'N e. RR+')
    lnt = c([c([np_, c([c([E.tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 2 )', {'T': E.tr})], 'elrpd', '( T + 2 ) e. RR+')], 'rpmulcld', '( N x. ( T + 2 ) ) e. RR+')], 'relogcld', '%s e. RR' % LNT)
    ln4 = c([c([np_, c([c([E.tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 4 )', {'T': E.tr})], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( N x. ( T + 4 ) ) e. RR+')], 'relogcld', '%s e. RR' % LN4)
    cl = Closure(w, A0, {YS: ('RR', ysr), LNT: ('RR', lnt), LN4: ('RR', ln4), 'Y': ('RR', E.yr), 'T': ('RR+', tpp)})
    return cl.mem(B, 'RR')


GENS = {'ef4zs1': gen_zs1, 'ef4zs2': gen_zs2, 'ef4zs': gen_zs, 'ef4scc': lambda: gen_zs(True)}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
