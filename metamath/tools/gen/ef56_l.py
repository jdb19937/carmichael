"""Sortie EF56: the zero sums of the zeta contour (ef6zs1, ef6zs2, ef6zs; Lean contour_zeta hadj), after EF4's ef4_g."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts
from ef4_b import ld0_mem, hp0_mem
from ef4_g import elrab_unpack, elrab_pack, elrab_
from ef4_h import Mini
from zc1_m import e_h2

BXA, BXB = '( ( 1 / 2 ) + ( _i x. -u T ) )', '( 1 + ( _i x. T ) )'
RFA, RFB = PTL('S', '-u U'), PTL(C1, 'V')
BZTE = BZ(ETA, 'T')
M_ = '( %s holord q )' % ETA


class Env6:
    """the common facts of HZ6"""
    def __init__(self, w, A0):
        self.w, self.A0 = w, A0
        c = self.c = Ctx(w, A0)
        g = c.g
        self.yr = g('Y e. RR'); self.y100 = g('; ; 1 0 0 <_ Y'); self.tr = g('T e. RR'); self.t2 = g('2 <_ T')
        self.ur = g('U e. RR'); self.vr = g('V e. RR'); self.tu = g('T <_ U'); self.u1 = g('U <_ ( T + 1 )'); self.tv = g('T <_ V'); self.v1 = g('V <_ ( T + 1 )')
        self.sr = g('S e. RR'); self.s916 = g('( 9 / ; 1 6 ) <_ S'); self.s58 = g('S <_ ( 5 / 8 )')
        self.lines = g(NZ2E)
        self.f = c1_facts(w, c, self.yr, self.y100)
        self.dd = c.a1(w.s([], 'ef2dde', DD(ETA, '1')), DD(ETA, '1'))
        self.hol, self.nr, self.n1, _, self.nz = dd_parts(w, A0, self.dd, ETA, '1')
        self.ntr = c([self.tr], 'renegcld', '-u T e. RR'); self.nur = c([self.ur], 'renegcld', '-u U e. RR')

    def L(self, st, A):
        return lift(self.w, st, A)

    def corners(self, cc, x, y, xr, yr):
        w = self.w
        return [cc([xr, yr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (PTL(x, y), x)), cc([xr, yr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (PTL(x, y), y))]

    def reals(self, A):
        L = lambda st: self.L(st, A)
        return {'T': L(self.tr), 'U': L(self.ur), 'V': L(self.vr), 'S': L(self.sr), 'Y': L(self.yr)}


def cfz_facts(E, A, qin):
    """q e. CFZ: q e. CC, ETA q = 0, ord E1 <_ ord ETA, ord E1 e. NN0, lin facts, leaves"""
    w = E.w
    cc = Ctx(w, A)
    BX = BOX('( 1 / 2 )', 'T')
    qbx, bq, new = elrab_unpack(w, A, 'r', BX, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % E1, 'q', qin)
    qn1 = cc([bq, w.inst('simpl')], 'syl', 'q =/= 1')
    e1z = cc([bq, w.inst('simpr')], 'syl', '( %s ` q ) = 0' % E1)
    L = lambda st: E.L(st, A)
    half = numst(w, A, '( 1 / 2 )', 'RR'); one = numst(w, A, '1', 'RR')
    ac = ptc(cc, '( 1 / 2 )', '-u T', half, L(E.ntr)); bc = ptc(cc, '1', 'T', one, L(E.tr))
    bd = crect_bounds(w, A, ac, bc, qbx, BXA, BXB, 'q')
    hy = bd['le'] + E.corners(cc, '( 1 / 2 )', '-u T', half, L(E.ntr)) + E.corners(cc, '1', 'T', one, L(E.tr))
    lv = dict(bd['cl']); lv.update(E.reals(A))
    r0 = lin8(w, A, hy, '0 < ( Re ` q )', lv)
    qh = hp0_mem(cc, 'q', bd['cc'], None, r0)
    EZT = tsub(stmt('zc1ezt'), {'P': 'q'})
    eza, ezc = ante_of(EZT)
    ezt = cc([cc([qh, qn1], 'jca', eza), w.inst('zc1ezt')], 'syl', ezc)
    ole = cc([ezt, w.inst('simpl')], 'syl', top_and(ezc)[0])
    fz = cc([e1z, cc([ezt, w.inst('simpr')], 'syl', top_and(ezc)[1])], 'mpd', '( %s ` q ) = 0' % ETA)
    HF1 = tsub(stmt('hp0ordf'), {'F': E1, 'P': 'q'})
    hfa, hfc = ante_of(HF1)
    ozn = cc([cc([cc([e_h2(w, A, nx1(w, A), '1', U1), qh], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc), w.inst('simpl')], 'syl', '( %s holord q ) e. NN0' % E1)
    return dict(cc=bd['cc'], fz=fz, hy=hy, lv=lv, ole=ole, ozn=ozn, qh=qh)


def gen_zs1():
    w = W('ef6zs1', 'Lean ` contour_zeta ` , ` hCR ` : the zeros of ` zeta ` ( of ` E1 ` off 1) in the box ` [ 1 / 2 , 1 ] x [ - T , T ] ` outside the contour rectangle are zeros of ` eta ` left of ` S ` , with ` ord zeta <_ ord eta ` , so their sum is at most ` 72000 Y ^ S log ^ 2 ( T + 2 ) ` ( ~ zc1ezt , ~ ef3wt ).')
    A0, G = ante_of(S['ef6zs1'])
    E = Env6(w, A0)
    c = E.c
    D1 = '( %s \\ %s )' % (CFZ, RFE)
    Aq = '( %s /\\ q e. %s )' % (A0, D1)
    cq = Ctx(w, Aq)
    L = lambda st: E.L(st, Aq)
    qd = cq([], 'simpr', 'q e. %s' % D1)
    qcf = cq([qd, w.inst('eldifi')], 'syl', 'q e. %s' % CFZ)
    qnr = cq([qd, w.inst('eldifn')], 'syl', '-. q e. %s' % RFE)
    d = cfz_facts(E, Aq, qcf)
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
        LB = '( ( %s ` %s ) =/= 0 /\\ ( %s ` %s ) =/= 0 )' % (ETA, PTL('v', '-u U'), ETA, PTL('v', 'V'))
        lb, lbn = ral_at(w, A2, lift(w, E.lines, A2), 'v', rq, LB, vin)
        ne = c2([lb, w.inst('simpl' if which == 0 else 'simpr')], 'syl', '( %s ` %s ) =/= 0' % (ETA, PTL(rq, y_)))
        ne2 = c2([ne, c2([c2([qe2], 'fveq2d', '( %s ` q ) = ( %s ` %s )' % (ETA, ETA, PTL(rq, y_)))], 'neeq1d', '( ( %s ` q ) =/= 0 <-> ( %s ` %s ) =/= 0 )' % (ETA, ETA, PTL(rq, y_)))], 'mpbird', '( %s ` q ) =/= 0' % ETA)
        n3 = c2([ne2], 'neneqd', '-. ( %s ` q ) = 0' % ETA)
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
    body = '( ( %s ` p ) = 0 /\\ %s )' % (ETA, SIN('p', 'S', C1, '-u U', 'V'))
    qrf = elrab_pack(w, A3, 'p', '( %s crect %s )' % (RFA, RFB), body, 'q', qx, c3([L3(d['fz']), sin], 'jca', '( ( %s ` q ) = 0 /\\ %s )' % (ETA, SIN('q', 'S', C1, '-u U', 'V'))))
    nsr = cq([qrf, lift(w, qnr, A3)], 'pm2.65da', '-. S < %s' % rq)
    rs = cq([nsr, cq([lv[rq], L(E.sr)], 'lenltd', '( %s <_ S <-> -. S < %s )' % (rq, rq))], 'mpbird', '%s <_ S' % rq)
    # q in the box BZ(T): orders in NN
    qbz = bz_inF(E, Aq, 'T', L(E.tr), 'q', d['cc'], d['fz'], d['hy'], lvq, F=ETA)
    BZI = tsub(stmt('ef3bz'), {'F': ETA, 'A': '1', 'U': 'T'})
    bza, bzc = ante_of(BZI)
    bzs = c([c([E.dd, E.tr], 'jca', bza), w.inst('ef3bz')], 'syl', bzc)
    bzf, bzo = conj_split(w, A0, bzs)
    mo = cq([qbz, cq([L(bzo), w.inst('rsp')], 'syl', '( q e. %s -> ( %s holord q ) e. NN )' % (BZTE, ETA))], 'mpd', '( %s holord q ) e. NN' % ETA)
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
    OZ = '( %s holord q )' % E1
    ozn = d['ozn']
    ozr = cq([ozn], 'nn0red', '%s e. RR' % OZ)
    oz0 = cq([ozn], 'nn0ge0d', '0 <_ %s' % OZ)
    ab = cq([cq([cq([ozr], 'recnd', '%s e. CC' % OZ), yqc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TZ, OZ, YQ)),
             cq([cq([ozr, oz0], 'absidd', '( abs ` %s ) = %s' % (OZ, OZ)), cq([cq([cq([cq([yp], 'rpcnd', 'Y e. CC'), d['cc']], 'cxpcld', '( Y ^c q ) e. CC'), d['cc'], qne], 'absdivd', '( abs ` %s ) = ( ( abs ` ( Y ^c q ) ) / %s )' % (YQ, AQ)),
                                                                   cq([cq([yp, d['cc'], w.inst('abscxp')], 'syl2anc', '( abs ` ( Y ^c q ) ) = %s' % YRe)], 'oveq1d', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s / %s )' % (AQ, YRe, AQ))], 'eqtrd',
                                                                  '( abs ` %s ) = ( %s / %s )' % (YQ, YRe, AQ))], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( %s / %s ) )' % (OZ, YQ, OZ, YRe, AQ))], 'eqtrd',
            '( abs ` %s ) = ( %s x. ( %s / %s ) )' % (TZ, OZ, YRe, AQ))
    yra = cq([yrer, ap], 'rerpdivcld', '( %s / %s ) e. RR' % (YRe, AQ))
    ya0 = cq([cq([cq([yp, lv[rq]], 'rpcxpcld', '%s e. RR+' % YRe), ap], 'rpdivcld', '( %s / %s ) e. RR+' % (YRe, AQ))], 'rpge0d', '0 <_ ( %s / %s )' % (YRe, AQ))
    om = cq([ozr, mr, yra, ya0, d['ole']], 'lemul1ad', '( %s x. ( %s / %s ) ) <_ ( %s x. ( %s / %s ) )' % (OZ, YRe, AQ, m, YRe, AQ))
    pw0 = le_tr(w, Aq, cq([ab, om], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( %s / %s ) )' % (TZ, m, YRe, AQ)), '( abs ` %s )' % TZ, '( %s x. ( %s / %s ) )' % (m, YRe, AQ), q2, '( %s x. ( %s / %s ) )' % (m, Y3, W1))
    pw = cq([pw0, q3], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (TZ, Y3, WQq))
    gc = cq([cq([ozr], 'recnd', '%s e. CC' % OZ), yqc], 'mulcld', '%s e. CC' % TZ)
    # sums
    ssb = c([w.s([qbz], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, D1, BZTE))], 'ssrdv', '%s C_ %s' % (D1, BZTE))
    fin = c([bzf, ssb], 'ssfid', '%s e. Fin' % D1)
    SG, SA, SW = 'sum_ q e. %s %s' % (D1, TZ), 'sum_ q e. %s ( abs ` %s )' % (D1, TZ), 'sum_ q e. %s %s' % (D1, WQq)
    s1 = c([fin, gc], 'fsumabs', '( abs ` %s ) <_ %s' % (SG, SA))
    wqr = cq([mr, w1p], 'rerpdivcld', '%s e. RR' % WQq)
    s2 = c([fin, cq([gc], 'abscld', '( abs ` %s ) e. RR' % TZ), cq([y3r, wqr], 'remulcld', '( %s x. %s ) e. RR' % (Y3, WQq)), pw], 'fsumle', '%s <_ sum_ q e. %s ( %s x. %s )' % (SA, D1, Y3, WQq))
    y3c = c([numst(w, A0, '3', 'RR'), c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpred', '%s e. RR' % YS)], 'remulcld', '%s e. RR' % Y3)
    s3 = c([fin, c([y3c], 'recnd', '%s e. CC' % Y3), cq([wqr], 'recnd', '%s e. CC' % WQq)], 'fsummulc2', '( %s x. %s ) = sum_ q e. %s ( %s x. %s )' % (Y3, SW, D1, Y3, WQq))
    WT = tsub(stmt('ef3wt'), {'F': ETA, 'A': '1', 'U': 'T', 'G': D1})
    wta, wtc = ante_of(WT)
    wt = c([conj(w, A0, wta, {DD(ETA, '1'): E.dd, 'T e. RR': E.tr, '2 <_ T': E.t2, '%s C_ %s' % (D1, BZTE): ssb}), w.inst('ef3wt')], 'syl', wtc)
    KWL = '( ; ; ; ; 2 4 0 0 0 x. ( %s ^ 2 ) )' % LNTz
    swr = c([fin, wqr], 'fsumrecl', '%s e. RR' % SW)
    ntp = c([c.a1(w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), c([c([E.tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 2 )', {'T': E.tr})], 'elrpd', '( T + 2 ) e. RR+')], 'rpmulcld', '( 1 x. ( T + 2 ) ) e. RR+')
    lnr = c([ntp], 'relogcld', '%s e. RR' % LNTz)
    kwr = c([numst(w, A0, '; ; ; ; 2 4 0 0 0', 'RR'), c([lnr], 'resqcld', '( %s ^ 2 ) e. RR' % LNTz)], 'remulcld', '%s e. RR' % KWL)
    s4 = c([swr, kwr, y3c, lin8(w, A0, [c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpge0d', '0 <_ %s' % YS)], '0 <_ %s' % Y3, {YS: c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpred', '%s e. RR' % YS)}), wt],
           'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (Y3, SW, Y3, KWL))
    cl = Closure(w, A0, {YS: ('RR', c([c([E.f['yp'], E.sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpred', '%s e. RR' % YS)), LNTz: ('RR', lnr)})
    cl.atom(YS); cl.atom(LNTz)
    RHS = '( ( ; ; ; ; 7 2 0 0 0 x. %s ) x. ( %s ^ 2 ) )' % (YS, LNTz)
    s5 = ringeq(w, A0, '( %s x. %s )' % (Y3, KWL), RHS, cl)
    t1 = le_tr(w, A0, s1, '( abs ` %s )' % SG, SA, c([s2, c([s3], 'eqcomd', 'sum_ q e. %s ( %s x. %s ) = ( %s x. %s )' % (D1, Y3, WQq, Y3, SW))], 'breqtrd', '%s <_ ( %s x. %s )' % (SA, Y3, SW)), '( %s x. %s )' % (Y3, SW))
    t2_ = le_tr(w, A0, t1, '( abs ` %s )' % SG, '( %s x. %s )' % (Y3, SW), c([s4, s5], 'breqtrd', '( %s x. %s ) <_ %s' % (Y3, SW, RHS)), RHS)
    w.qed([t2_], 'idi', S['ef6zs1'])
    return run8(w)





def rfe_facts(E, A, qin):
    """q e. RFE: q e. CC, ETA q = 0, SIN facts and the crect bounds"""
    w = E.w
    cc = Ctx(w, A)
    X = '( %s crect %s )' % (RFA, RFB)
    body = '( ( %s ` p ) = 0 /\\ %s )' % (ETA, SIN('p', 'S', C1, '-u U', 'V'))
    qx, bq, new = elrab_unpack(w, A, 'p', X, body, 'q', qin)
    fz = cc([bq, w.inst('simpl')], 'syl', '( %s ` q ) = 0' % ETA)
    sn = cc([bq, w.inst('simpr')], 'syl', SIN('q', 'S', C1, '-u U', 'V'))
    s1, s2 = conj_split(w, A, sn)
    a1, a2 = conj_split(w, A, s1)
    b1, b2 = conj_split(w, A, s2)
    L = lambda st: E.L(st, A)
    ac = ptc(cc, 'S', '-u U', L(E.sr), L(E.nur)); bc = ptc(cc, C1, 'V', L(E.f['c1r']), L(E.vr))
    bd = crect_bounds(w, A, ac, bc, qx, RFA, RFB, 'q')
    lv = dict(bd['cl']); lv.update(E.reals(A)); lv[C1] = L(E.f['c1r'])
    return dict(cc=bd['cc'], fz=fz, hy=[a1, a2, b1, b2], lv=lv)


def gen_zs2():
    w = W('ef6zs2', 'Lean ` contour_zeta ` , ` hRC ` : the zeros of ` eta ` inside the contour rectangle outside the box ` [ 1 / 2 , 1 ] x [ - T , T ] ` carry the order of ` zeta ` ( ` E1 ` ) only where ` zeta ` vanishes; there ` q =/= 1 ` ( ~ ef5e11 ), ` Re <_ 1 ` , ` T < abs Im <_ T + 1 ` and ` ord zeta <_ ord eta ` , so the sum is at most ` 1600 Y log ( T + 4 ) / T ` ( ~ zc1ezt , ~ ef4bm ).')
    A0, G = ante_of(S['ef6zs2'])
    E = Env6(w, A0)
    c = E.c
    D2 = '( %s \\ %s )' % (RFE, CFZ)
    RFEo = RFE.replace('{ p e.', '{ o e.').replace('` p )', '` o )')
    D2o = '( %s \\ %s )' % (RFEo, CFZ)
    ZB = '{ a e. %s | ( %s ` a ) = 0 }' % (D2o, E1)
    Aq = '( %s /\\ q e. %s )' % (A0, ZB)
    cq = Ctx(w, Aq)
    L = lambda st: E.L(st, Aq)
    rbody = '( ( %s ` p ) = 0 /\\ %s )' % (ETA, SIN('p', 'S', C1, '-u U', 'V'))
    ceq, _ = w.wcongr(rbody, {'p': 'o'}, 'p = o', {'p': w.s([], 'id', '( p = o -> p = o )')})
    rfe = w.s([ceq], 'cbvrabv', '%s = %s' % (RFE, RFEo))
    de = w.s([rfe], 'difeq1i', '%s = %s' % (D2, D2o))
    qzb, e1z, _ = elrab_unpack(w, Aq, 'a', D2o, '( %s ` a ) = 0' % E1, 'q', cq([], 'simpr', 'q e. %s' % ZB))
    qd = cq([qzb, cq.a1(w.s([de], 'eqcomi', '%s = %s' % (D2o, D2)), '%s = %s' % (D2o, D2))], 'eleqtrd', 'q e. %s' % D2)
    qrf = cq([qd, w.inst('eldifi')], 'syl', 'q e. %s' % RFE)
    qnc = cq([qd, w.inst('eldifn')], 'syl', '-. q e. %s' % CFZ)
    d = rfe_facts(E, Aq, qrf)
    lv = d['lv']
    rq, iq = '( Re ` q )', '( Im ` q )'
    hyb = d['hy'] + [L(E.s916), L(E.tu), L(E.tv), L(E.u1), L(E.v1), L(E.t2)]
    rq0 = lin8(w, Aq, hyb, '0 < %s' % rq, lv)
    qh = hp0_mem(cq, 'q', d['cc'], None, rq0)
    nzq, _ = ral_at(w, Aq, L(E.nz), 'w', 'q', '( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % ETA, qh)
    nn_ = cq([d['fz'], cq.a1(w.s([], 'nne', '( -. ( %s ` q ) =/= 0 <-> ( %s ` q ) = 0 )' % (ETA, ETA)), '( -. ( %s ` q ) =/= 0 <-> ( %s ` q ) = 0 )' % (ETA, ETA))], 'mpbird', '-. ( %s ` q ) =/= 0' % ETA)
    n1 = cq([nn_, nzq], 'mtod', '-. 1 < %s' % rq)
    r1 = cq([n1, cq([lv[rq], numst(w, Aq, '1', 'RR')], 'lenltd', '( %s <_ 1 <-> -. 1 < %s )' % (rq, rq))], 'mpbird', '%s <_ 1' % rq)
    A11 = '( %s /\\ q = 1 )' % Aq
    c11 = Ctx(w, A11)
    e11 = c11([c11([c11([], 'simpr', 'q = 1'), w.inst('fveq2')], 'syl', '( %s ` q ) = ( %s ` 1 )' % (E1, E1)), c11.a1(w.s([], 'ef5e11', S['ef5e11']), S['ef5e11'])], 'eqtrd', '( %s ` q ) = 1' % E1)
    nq1 = cq([c11([lift(w, e1z, A11), e11], 'eqtr3d', '0 = 1'), c11.a1(w.s([w.s([w.s([], 'ax-1ne0', '1 =/= 0')], 'necomi', '0 =/= 1')], 'neii', '-. 0 = 1'), '-. 0 = 1')], 'pm2.65da', '-. q = 1')
    qn1 = cq([nq1], 'neqned', 'q =/= 1')
    EZT = tsub(stmt('zc1ezt'), {'P': 'q'})
    eza, ezc = ante_of(EZT)
    ole = cq([cq([cq([qh, qn1], 'jca', eza), w.inst('zc1ezt')], 'syl', ezc), w.inst('simpl')], 'syl', top_and(ezc)[0])
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
    qcf = elrab_pack(w, A3, 'r', BOX('( 1 / 2 )', 'T'), '( r =/= 1 /\\ ( %s ` r ) = 0 )' % E1, 'q', qbx, c3([L3(qn1), L3(e1z)], 'jca', '( q =/= 1 /\\ ( %s ` q ) = 0 )' % E1))
    nt = cq([qcf, lift(w, qnc, A3)], 'pm2.65da', '-. ( abs ` %s ) <_ T' % iq)
    tlt = cq([nt, cq([L(E.tr), aim], 'ltnled', '( T < ( abs ` %s ) <-> -. ( abs ` %s ) <_ T )' % (iq, iq))], 'mpbird', 'T < ( abs ` %s )' % iq)
    t1r = cq([L(E.tr), numst(w, Aq, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    ale = cq([cq([lin8(w, Aq, hyb, '-u ( T + 1 ) <_ %s' % iq, lv), lin8(w, Aq, hyb, '%s <_ ( T + 1 )' % iq, lv)], 'jca', '( -u ( T + 1 ) <_ %s /\\ %s <_ ( T + 1 ) )' % (iq, iq)),
              cq([lv[iq], t1r], 'absled', '( ( abs ` %s ) <_ ( T + 1 ) <-> ( -u ( T + 1 ) <_ %s /\\ %s <_ ( T + 1 ) ) )' % (iq, iq, iq))], 'mpbird', '( abs ` %s ) <_ ( T + 1 )' % iq)
    BQ = tsub(BAND, {'F': ETA, 'p': 'q'})
    band = conj(w, Aq, BQ, {'( %s ` q ) = 0' % ETA: d['fz'], '( 1 / 2 ) <_ %s' % rq: lin8(w, Aq, hyb, '( 1 / 2 ) <_ %s' % rq, lv), '%s <_ ( 3 / 2 )' % rq: lin8(w, Aq, [r1], '%s <_ ( 3 / 2 )' % rq, lv),
                            'T < ( abs ` %s )' % iq: tlt, '( abs ` %s ) <_ ( T + 1 )' % iq: ale})
    # orders: q in BZ ( T + 1 )
    lvb = dict(lv); lvb['( T + 1 )'] = t1r
    qbz = bz_inF(E, Aq, '( T + 1 )', t1r, 'q', d['cc'], d['fz'], hyb + [r1], lv, F=ETA)
    BZ1 = BZ(ETA, '( T + 1 )')
    BZI = tsub(stmt('ef3bz'), {'F': ETA, 'A': '1', 'U': '( T + 1 )'})
    bza, bzc = ante_of(BZI)
    bzs = c([c([E.dd, c([E.tr, numst(w, A0, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')], 'jca', bza), w.inst('ef3bz')], 'syl', bzc)
    bzf, bzo = conj_split(w, A0, bzs)
    mo = cq([qbz, cq([L(bzo), w.inst('rsp')], 'syl', '( q e. %s -> ( %s holord q ) e. NN )' % (BZ1, ETA))], 'mpd', '( %s holord q ) e. NN' % ETA)
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
    OZ = '( %s holord q )' % E1
    HF1 = tsub(stmt('hp0ordf'), {'F': E1, 'P': 'q'})
    hfa, hfc = ante_of(HF1)
    ozn = cq([cq([cq([e_h2(w, Aq, nx1(w, Aq), '1', U1), qh], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc), w.inst('simpl')], 'syl', '%s e. NN0' % OZ)
    ozr = cq([ozn], 'nn0red', '%s e. RR' % OZ)
    oz0 = cq([ozn], 'nn0ge0d', '0 <_ %s' % OZ)
    ab = cq([cq([cq([ozr], 'recnd', '%s e. CC' % OZ), yqc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TZ, OZ, YQ)),
             cq([cq([ozr, oz0], 'absidd', '( abs ` %s ) = %s' % (OZ, OZ)), cq([cq([cq([cq([yp], 'rpcnd', 'Y e. CC'), d['cc']], 'cxpcld', '( Y ^c q ) e. CC'), d['cc'], qne], 'absdivd', '( abs ` %s ) = ( ( abs ` ( Y ^c q ) ) / %s )' % (YQ, AQ)),
                                                                   cq([cq([yp, d['cc'], w.inst('abscxp')], 'syl2anc', '( abs ` ( Y ^c q ) ) = %s' % YRe)], 'oveq1d', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s / %s )' % (AQ, YRe, AQ))], 'eqtrd',
                                                                  '( abs ` %s ) = ( %s / %s )' % (YQ, YRe, AQ))], 'oveq12d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( %s / %s ) )' % (OZ, YQ, OZ, YRe, AQ))], 'eqtrd',
            '( abs ` %s ) = ( %s x. ( %s / %s ) )' % (TZ, OZ, YRe, AQ))
    yra = cq([yrer, ap], 'rerpdivcld', '( %s / %s ) e. RR' % (YRe, AQ))
    ya0 = cq([cq([cq([yp, lv[rq]], 'rpcxpcld', '%s e. RR+' % YRe), ap], 'rpdivcld', '( %s / %s ) e. RR+' % (YRe, AQ))], 'rpge0d', '0 <_ ( %s / %s )' % (YRe, AQ))
    om = cq([ozr, mr, yra, ya0, ole], 'lemul1ad', '( %s x. ( %s / %s ) ) <_ ( %s x. ( %s / %s ) )' % (OZ, YRe, AQ, m, YRe, AQ))
    pw0 = le_tr(w, Aq, cq([ab, om], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( %s / %s ) )' % (TZ, m, YRe, AQ)), '( abs ` %s )' % TZ, '( %s x. ( %s / %s ) )' % (m, YRe, AQ), q2, '( %s x. ( Y / T ) )' % m)
    pw = cq([pw0, q3], 'breqtrd', '( abs ` %s ) <_ ( ( Y / T ) x. %s )' % (TZ, m))
    gc = cq([cq([ozr], 'recnd', '%s e. CC' % OZ), yqc], 'mulcld', '%s e. CC' % TZ)
    # sums over ZB
    ssb = c([w.s([qbz], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (A0, ZB, BZ1))], 'ssrdv', '%s C_ %s' % (ZB, BZ1))
    fin = c([bzf, ssb], 'ssfid', '%s e. Fin' % ZB)
    D2 = ZB
    SG, SA, SM = 'sum_ q e. %s %s' % (D2, TZ), 'sum_ q e. %s ( abs ` %s )' % (D2, TZ), 'sum_ q e. %s %s' % (D2, m)
    YT_ = '( Y / T )'
    tpp = c([E.tr, lin8(w, A0, [E.t2], '0 < T', {'T': E.tr})], 'elrpd', 'T e. RR+')
    ytr = c([E.yr, tpp], 'rerpdivcld', '%s e. RR' % YT_)
    s1 = c([fin, gc], 'fsumabs', '( abs ` %s ) <_ %s' % (SG, SA))
    s2 = c([fin, cq([gc], 'abscld', '( abs ` %s ) e. RR' % TZ), cq([lift(w, ytr, Aq), mr], 'remulcld', '( %s x. %s ) e. RR' % (YT_, m)), pw], 'fsumle', '%s <_ sum_ q e. %s ( %s x. %s )' % (SA, D2, YT_, m))
    s3 = c([fin, c([ytr], 'recnd', '%s e. CC' % YT_), cq([mr], 'recnd', '%s e. CC' % m)], 'fsummulc2', '( %s x. %s ) = sum_ q e. %s ( %s x. %s )' % (YT_, SM, D2, YT_, m))
    alb = c([band], 'ralrimiva', 'A. q e. %s %s' % (D2, BQ))
    cbb, _ = cbvral(w, D2, 'q', 'p', BQ)
    BP = tsub(BAND, {'F': ETA})
    alp = c([alb, c.a1(cbb, '( A. q e. %s %s <-> A. p e. %s %s )' % (D2, BQ, D2, BP))], 'mpbid', 'A. p e. %s %s' % (D2, BP))
    dcc = c([w.s([d['cc']], 'ex', '( %s -> ( q e. %s -> q e. CC ) )' % (A0, D2))], 'ssrdv', '%s C_ CC' % D2)
    BM = tsub(stmt('ef4bm'), {'F': ETA, 'A': '1', 'G': D2})
    bma, bmc = ante_of(BM)
    bm = c([conj(w, A0, bma, {DD(ETA, '1'): E.dd, 'T e. RR': E.tr, '2 <_ T': E.t2, '%s C_ CC' % D2: dcc, 'A. p e. %s %s' % (D2, BP): alp}), w.inst('ef4bm')], 'syl', bmc)
    smr = c([fin, cq([mo], 'nnred', '%s e. RR' % m)], 'fsumrecl', '%s e. RR' % SM)
    KBL = '( %s x. %s )' % (KB, LN4z)
    n4p = c([c.a1(w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), c([c([E.tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 4 )', {'T': E.tr})], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( 1 x. ( T + 4 ) ) e. RR+')
    l4r = c([n4p], 'relogcld', '%s e. RR' % LN4z)
    kbr = c([numst(w, A0, KB, 'RR'), l4r], 'remulcld', '%s e. RR' % KBL)
    yt0 = c([E.yr, tpp, lin8(w, A0, [E.y100], '0 <_ Y', {'Y': E.yr})], 'divge0d', '0 <_ %s' % YT_)
    s4 = c([smr, kbr, ytr, yt0, bm], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (YT_, SM, YT_, KBL))
    RT = '( 1 / T )'
    rtr = c([tpp], 'rpreccld', '%s e. RR+' % RT)
    e1 = c([c([E.yr], 'recnd', 'Y e. CC'), c([tpp], 'rpcnd', 'T e. CC'), c([tpp], 'rpne0d', 'T =/= 0')], 'divrecd', '%s = ( Y x. %s )' % (YT_, RT))
    e2 = c([c([l4r], 'recnd', '%s e. CC' % LN4z), c([tpp], 'rpcnd', 'T e. CC'), c([tpp], 'rpne0d', 'T =/= 0')], 'divrecd', '( %s / T ) = ( %s x. %s )' % (LN4z, LN4z, RT))
    cl = Closure(w, A0, {'Y': ('RR', E.yr), LN4z: ('RR', l4r), RT: ('RR', c([rtr], 'rpred', '%s e. RR' % RT))})
    for k in ('Y', LN4z, RT):
        cl.atom(k)
    RHS = '( ( %s x. Y ) x. ( %s / T ) )' % (KB, LN4z)
    e3 = ringeq(w, A0, '( ( Y x. %s ) x. %s )' % (RT, KBL), '( ( %s x. Y ) x. ( %s x. %s ) )' % (KB, LN4z, RT), cl)
    e4 = c([c([c([e1], 'oveq1d', '( %s x. %s ) = ( ( Y x. %s ) x. %s )' % (YT_, KBL, RT, KBL)), e3], 'eqtrd', '( %s x. %s ) = ( ( %s x. Y ) x. ( %s x. %s ) )' % (YT_, KBL, KB, LN4z, RT)),
            c([c([e2], 'eqcomd', '( %s x. %s ) = ( %s / T )' % (LN4z, RT, LN4z))], 'oveq2d', '( ( %s x. Y ) x. ( %s x. %s ) ) = %s' % (KB, LN4z, RT, RHS))], 'eqtrd', '( %s x. %s ) = %s' % (YT_, KBL, RHS))
    t1 = le_tr(w, A0, s1, '( abs ` %s )' % SG, SA, c([s2, c([s3], 'eqcomd', 'sum_ q e. %s ( %s x. %s ) = ( %s x. %s )' % (D2, YT_, m, YT_, SM))], 'breqtrd', '%s <_ ( %s x. %s )' % (SA, YT_, SM)), '( %s x. %s )' % (YT_, SM))
    t2_ = le_tr(w, A0, t1, '( abs ` %s )' % SG, '( %s x. %s )' % (YT_, SM), c([s4, e4], 'breqtrd', '( %s x. %s ) <_ %s' % (YT_, SM, RHS)), RHS)
    # the sum over RFE \ CFZ is the sum over ZB
    DO = '( %s \\ %s )' % (RFE, CFZ)
    s_de = c([c.a1(de, '%s = %s' % (DO, D2o))], 'sumeq1d', 'sum_ q e. %s %s = sum_ q e. %s %s' % (DO, TZ, D2o, TZ))
    ZRF = tsub(stmt('ef3zrf'), {'F': ETA, 'A': '1', 'C': C1, 'L': '-u U', 'H': 'V'})
    zra, zrc = ante_of(ZRF)
    zrs = c([rebuild(w, c, zra, {DD(ETA, '1'): E.dd, '-u U e. RR': E.nur, '%s e. RR' % C1: E.f['c1r'], '( 1 / 2 ) <_ S': lin8(w, A0, [E.s916], '( 1 / 2 ) <_ S', {'S': E.sr}),
                                 '%s <_ ( 3 / 2 )' % C1: lin8(w, A0, [E.f['c54']], '%s <_ ( 3 / 2 )' % C1, {C1: E.f['c1r']})}), w.inst('ef3zrf')], 'syl', zrc)
    rff = c([zrs, w.inst('simpl')], 'syl', '%s e. Fin' % RFE)
    rfo = c([c.a1(w.s([rfe], 'eqcomi', '%s = %s' % (RFEo, RFE)), '%s = %s' % (RFEo, RFE)), rff], 'eqeltrd', '%s e. Fin' % RFEo)
    dof = c([rfo, c.a1(w.s([], 'difss', '%s C_ %s' % (D2o, RFEo)), '%s C_ %s' % (D2o, RFEo))], 'ssfid', '%s e. Fin' % D2o)
    Ax = '( %s /\\ q e. ( %s \\ %s ) )' % (A0, D2o, ZB)
    cx = Ctx(w, Ax)
    xin = cx([], 'simpr', 'q e. ( %s \\ %s )' % (D2o, ZB))
    xd = cx([xin, w.inst('eldifi')], 'syl', 'q e. %s' % D2o)
    xnb = cx([xin, w.inst('eldifn')], 'syl', '-. q e. %s' % ZB)
    xrf = cx([cx([xd, cx.a1(w.s([de], 'eqcomi', '%s = %s' % (D2o, DO)), '%s = %s' % (D2o, DO))], 'eleqtrd', 'q e. %s' % DO), w.inst('eldifi')], 'syl', 'q e. %s' % RFE)
    dx = rfe_facts(E, Ax, xrf)
    hyx = dx['hy'] + [lift(w, E.s916, Ax)]
    rx0 = lin8(w, Ax, hyx, '0 < ( Re ` q )', dx['lv'])
    xh = hp0_mem(cx, 'q', dx['cc'], None, rx0)
    zbe = elrab_(w, 'a', D2o, '( %s ` a ) = 0' % E1, 'q')[0]
    # -. E1 q = 0 : if E1 q = 0 then q e. ZB
    Ax2 = '( %s /\\ ( %s ` q ) = 0 )' % (Ax, E1)
    cx2 = Ctx(w, Ax2)
    inzb = cx2([cx2([lift(w, xd, Ax2), cx2([], 'simpr', '( %s ` q ) = 0' % E1)], 'jca', '( q e. %s /\\ ( %s ` q ) = 0 )' % (D2o, E1)), cx2.a1(zbe, '( q e. %s <-> ( q e. %s /\\ ( %s ` q ) = 0 ) )' % (ZB, D2o, E1))], 'mpbird', 'q e. %s' % ZB)
    ne1 = cx([inzb, lift(w, xnb, Ax2)], 'pm2.65da', '-. ( %s ` q ) = 0' % E1)
    he1x = cx([e_h2(w, Ax, nx1(w, Ax), '1', U1), w.inst('simpl')], 'syl', HOLF(E1, HP0))
    oz0x = cx([cx([he1x, cx([xh, cx([ne1], 'neqned', '( %s ` q ) =/= 0' % E1)], 'jca', '( q e. %s /\\ ( %s ` q ) =/= 0 )' % (HP0, E1))], 'jca', tsub(ante_of(S['ef6o0'])[0], {'F': E1, 'P': 'q'})), w.inst('ef6o0')], 'syl', '( %s holord q ) = 0' % E1)
    yqx = cx([cx([cx([lift(w, E.f['yp'], Ax)], 'rpcnd', 'Y e. CC'), dx['cc']], 'cxpcld', '( Y ^c q ) e. CC'), dx['cc'], ne0_re(cx, 'q', dx['cc'], rx0)], 'divcld', '( ( Y ^c q ) / q ) e. CC')
    tz0 = cx([cx([oz0x], 'oveq1d', '%s = ( 0 x. ( ( Y ^c q ) / q ) )' % TZ), cx([yqx], 'mul02d', '( 0 x. ( ( Y ^c q ) / q ) ) = 0')], 'eqtrd', '%s = 0' % TZ)
    zss = c.a1(w.s([], 'ssrab2', '%s C_ %s' % (ZB, D2o)), '%s C_ %s' % (ZB, D2o))
    fs = c([zss, gc, tz0, dof], 'fsumss', 'sum_ q e. %s %s = sum_ q e. %s %s' % (ZB, TZ, D2o, TZ))
    se = c([s_de, c([fs], 'eqcomd', 'sum_ q e. %s %s = sum_ q e. %s %s' % (D2o, TZ, ZB, TZ))], 'eqtrd', 'sum_ q e. %s %s = sum_ q e. %s %s' % (DO, TZ, ZB, TZ))
    fin2 = c([c([se], 'fveq2d', '( abs ` sum_ q e. %s %s ) = ( abs ` sum_ q e. %s %s )' % (DO, TZ, ZB, TZ)), t2_], 'eqbrtrd', '( abs ` sum_ q e. %s %s ) <_ %s' % (DO, TZ, RHS))
    w.qed([fin2], 'idi', S['ef6zs2'])
    return run8(w)
    return run8(w)





def gen_zs():
    w = W('ef6zs', 'Lean ` contour_zeta ` , ` hadj ` : the contract zero sum of ` zeta ` ( ` E1 ` off 1 on ` [ 1 / 2 , 1 ] x [ - T , T ] ` ) differs from the residue sum over the zeros of ` eta ` in the contour rectangle, weighted by the order of ` zeta ` , by at most ` 72000 Y ^ S log ^ 2 ( T + 2 ) + 1600 Y log ( T + 4 ) / T ` ( ~ ef4ssd , ~ ef6zs1 , ~ ef6zs2 ).')
    A0, G = ante_of(S['ef6zs'])
    E = Env6(w, A0)
    c = E.c
    half = numst(w, A0, '( 1 / 2 )', 'RR')
    EZ = tsub(stmt('ezf'), {'N': '1', 'X': U1, 'A': '( 1 / 2 )'})
    eza, ezc = ante_of(EZ)
    ez = c([conj(w, A0, eza, {'( 1 e. NN /\\ %s e. ( Base ` ( DChr ` 1 ) ) )' % U1: nx1(w, A0), '( 1 / 2 ) e. RR': half, '0 < ( 1 / 2 )': c.a1(w.s([], 'halfgt0', '0 < ( 1 / 2 )'), '0 < ( 1 / 2 )'),
                              '( 1 / 2 ) <_ 1': c.a1(w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], '1re', '1 e. RR'), w.s([], 'halflt1', '( 1 / 2 ) < 1')], 'ltleii', '( 1 / 2 ) <_ 1'), '( 1 / 2 ) <_ 1'),
                              'T e. RR': E.tr}), w.inst('ezf')], 'syl', ezc)
    cf = c([ez, w.inst('simpl')], 'syl', '%s e. Fin' % CFZ)
    ZRF = tsub(stmt('ef3zrf'), {'F': ETA, 'A': '1', 'C': C1, 'L': '-u U', 'H': 'V'})
    zra, zrc = ante_of(ZRF)
    zrs = c([rebuild(w, c, zra, {DD(ETA, '1'): E.dd, '-u U e. RR': E.nur, '%s e. RR' % C1: E.f['c1r'], '( 1 / 2 ) <_ S': lin8(w, A0, [E.s916], '( 1 / 2 ) <_ S', {'S': E.sr}),
                                 '%s <_ ( 3 / 2 )' % C1: lin8(w, A0, [E.f['c54']], '%s <_ ( 3 / 2 )' % C1, {C1: E.f['c1r']})}), w.inst('ef3zrf')], 'syl', zrc)
    rf = c([zrs, w.inst('simpl')], 'syl', '%s e. Fin' % RFE)
    U_ = '( %s u. %s )' % (CFZ, RFE)
    Au = '( %s /\\ q e. %s )' % (A0, U_)
    cu = Ctx(w, Au)
    def tc_side(X, facts_fn, extra):
        A1 = '( %s /\\ q e. %s )' % (Au, X)
        c1_ = Ctx(w, A1)
        d = facts_fn(E, A1, c1_([], 'simpr', 'q e. %s' % X))
        r0 = lin8(w, A1, d['hy'] + [lift(w, h, A1) for h in extra], '0 < ( Re ` q )', d['lv'])
        qh = hp0_mem(c1_, 'q', d['cc'], None, r0)
        return c1_([d['cc'], qh], 'jca', '( q e. CC /\\ q e. %s )' % HP0)
    t1 = tc_side(CFZ, cfz_facts, [])
    t2 = tc_side(RFE, rfe_facts, [E.s916])
    jo = w.s([w.s([t1], 'ex', '( %s -> ( q e. %s -> ( q e. CC /\\ q e. %s ) ) )' % (Au, CFZ, HP0)), w.s([t2], 'ex', '( %s -> ( q e. %s -> ( q e. CC /\\ q e. %s ) ) )' % (Au, RFE, HP0))], 'jaod',
             '( %s -> ( ( q e. %s \\/ q e. %s ) -> ( q e. CC /\\ q e. %s ) ) )' % (Au, CFZ, RFE, HP0))
    el = cu([cu([], 'simpr', 'q e. %s' % U_), cu.a1(w.s([], 'elun', '( q e. %s <-> ( q e. %s \\/ q e. %s ) )' % (U_, CFZ, RFE)), '( q e. %s <-> ( q e. %s \\/ q e. %s ) )' % (U_, CFZ, RFE))], 'mpbid', '( q e. %s \\/ q e. %s )' % (CFZ, RFE))
    both = cu([el, jo], 'mpd', '( q e. CC /\\ q e. %s )' % HP0)
    qc = cu([both, w.inst('simpl')], 'syl', 'q e. CC'); qh = cu([both, w.inst('simpr')], 'syl', 'q e. %s' % HP0)
    _, r0 = hp_facts(w, Au, qh, 'q')
    qne = ne0_re(cu, 'q', qc, r0)
    HF1 = tsub(stmt('hp0ordf'), {'F': E1, 'P': 'q'})
    hfa, hfc = ante_of(HF1)
    ozn = cu([cu([cu([e_h2(w, Au, nx1(w, Au), '1', U1), qh], 'jca', hfa), w.inst('hp0ordf')], 'syl', hfc), w.inst('simpl')], 'syl', '( %s holord q ) e. NN0' % E1)
    YQ = '( ( Y ^c q ) / q )'
    yqc = cu([cu([cu([lift(w, E.f['yp'], Au)], 'rpcnd', 'Y e. CC'), qc], 'cxpcld', '( Y ^c q ) e. CC'), qc, qne], 'divcld', '%s e. CC' % YQ)
    tc = cu([cu([ozn], 'nn0cnd', '( %s holord q ) e. CC' % E1), yqc], 'mulcld', '%s e. CC' % TZ)
    def fsum_on(X, fin, base):
        Ax = '( %s /\\ q e. %s )' % (A0, X)
        un = lift(w, c.a1(w.s([], 'difss', '%s C_ %s' % (X, base)), '%s C_ %s' % (X, base)), Ax) if X != base else None
        qb = w.s([un, w.s([], 'simpr', '( %s -> q e. %s )' % (Ax, X))], 'sseldd', '( %s -> q e. %s )' % (Ax, base)) if X != base else w.s([], 'simpr', '( %s -> q e. %s )' % (Ax, X))
        qu = w.s([qb, w.inst('elun1' if base == CFZ else 'elun2')], 'syl', '( %s -> q e. %s )' % (Ax, U_))
        tcx = w.s([qu, w.s([w.s([tc], 'ex', '( %s -> ( q e. %s -> %s e. CC ) )' % (A0, U_, TZ))], 'adantr', '( %s -> ( q e. %s -> %s e. CC ) )' % (Ax, U_, TZ))], 'mpd', '( %s -> %s e. CC )' % (Ax, TZ))
        xf = fin if X == base else c([fin, c.a1(w.s([], 'difss', '%s C_ %s' % (X, base)), '%s C_ %s' % (X, base))], 'ssfid', '%s e. Fin' % X)
        return c([xf, tcx], 'fsumcl', 'sum_ q e. %s %s e. CC' % (X, TZ))
    scc = fsum_on(CFZ, cf, CFZ); src = fsum_on(RFE, rf, RFE)
    SD = tsub(stmt('ef4ssd'), {'A': CFZ, 'B': RFE, 'C': TZ, 'ph': A0})
    sd = w.s([cf, rf, tc], 'ef4ssd', SD)
    S1_, S2_ = 'sum_ q e. ( %s \\ %s ) %s' % (CFZ, RFE, TZ), 'sum_ q e. ( %s \\ %s ) %s' % (RFE, CFZ, TZ)
    c1s = fsum_on('( %s \\ %s )' % (CFZ, RFE), cf, CFZ)
    c2s = fsum_on('( %s \\ %s )' % (RFE, CFZ), rf, RFE)
    ad = c([c1s, c2s, w.inst('abs2dif2')], 'syl2anc', '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (S1_, S2_, S1_, S2_))
    z1 = w.s([], 'ef6zs1', S['ef6zs1'])
    z2 = w.s([], 'ef6zs2', S['ef6zs2'])
    ysp = c([E.f['yp'], E.sr], 'rpcxpcld', '( Y ^c S ) e. RR+')
    tpp = c([E.tr, lin8(w, A0, [E.t2], '0 < T', {'T': E.tr})], 'elrpd', 'T e. RR+')
    lnt = c([c([c.a1(w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), c([c([E.tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 2 )', {'T': E.tr})], 'elrpd', '( T + 2 ) e. RR+')], 'rpmulcld', '( 1 x. ( T + 2 ) ) e. RR+')], 'relogcld', '%s e. RR' % LNTz)
    ln4 = c([c([c.a1(w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), c([c([E.tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [E.t2], '0 < ( T + 4 )', {'T': E.tr})], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( 1 x. ( T + 4 ) ) e. RR+')], 'relogcld', '%s e. RR' % LN4z)
    cl = Closure(w, A0, {'( Y ^c S )': ('RR', c([ysp], 'rpred', '( Y ^c S ) e. RR')), LNTz: ('RR', lnt), LN4z: ('RR', ln4), 'Y': ('RR', E.yr), 'T': ('RR+', tpp)})
    la = c([c([c1s], 'abscld', '( abs ` %s ) e. RR' % S1_), c([c2s], 'abscld', '( abs ` %s ) e. RR' % S2_), cl.mem(ZB1, 'RR'), cl.mem(ZB2, 'RR'), z1, z2], 'le2addd',
           '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s + %s )' % (S1_, S2_, ZB1, ZB2))
    e1 = sd
    fin_ = le_tr(w, A0, c([c([e1], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (SCz, SRz, S1_, S2_)), ad], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (SCz, SRz, S1_, S2_)),
                 '( abs ` ( %s - %s ) )' % (SCz, SRz), '( ( abs ` %s ) + ( abs ` %s ) )' % (S1_, S2_), la, '( %s + %s )' % (ZB1, ZB2))
    w.qed([fin_, c([scc, src], 'jca', '( %s e. CC /\\ %s e. CC )' % (SCz, SRz))], 'jca', S['ef6zs'])
    return run8(w)


GENS = {'ef6zs1': gen_zs1, 'ef6zs2': gen_zs2, 'ef6zs': gen_zs}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
