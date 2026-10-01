"""T2: the distinct-index stack-update algebra (blueprint D2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t1lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

DG = K('T')
GK = '( %s ` K )' % G('T')
GJ = '( %s ` J )' % G('T')
TD = '( T e. V /\\ D e. %s )' % STK('T')
PK = '( K e. %s /\\ Y e. Word %s )' % (DG, GK)
PJ = '( J e. %s /\\ Z e. Word %s )' % (DG, GJ)


def U1(D, Kk, X):
    return UPD('T', D, Kk, X)


def tm2stkupn():
    lab = 'tm2stkupn'
    ph = ('( ( T e. V /\\ D e. %s ) /\\ ( K e. %s /\\ Y e. W ) /\\ ( J e. %s /\\ J =/= K ) )'
          % (STK('T'), DG, DG))
    UP = U1('D', 'K', 'Y')
    w = W(lab, 'The value of an updated stack assignment at an index other '
               'than the updated one.  Lean: ` Function.update_of_ne ` .')
    p1 = w.s([], 'simp1', '( %s -> %s )' % (ph, TD))
    p2 = w.s([], 'simp2', '( %s -> ( K e. %s /\\ Y e. W ) )' % (ph, DG))
    p3 = w.s([], 'simp3', '( %s -> ( J e. %s /\\ J =/= K ) )' % (ph, DG))
    jj = w.s([p3], 'simpld', '( %s -> J e. %s )' % (ph, DG))
    ne = w.s([p3], 'simprd', '( %s -> J =/= K )' % ph)
    v = w.s([p1, p2, jj, w.inst('tm2stkupv')], 'syl3anc',
            '( %s -> ( %s ` J ) = if ( J = K , Y , ( D ` J ) ) )' % (ph, UP))
    nn = w.s([ne], 'neneqd', '( %s -> -. J = K )' % ph)
    f = w.s([nn], 'iffalsed', '( %s -> if ( J = K , Y , ( D ` J ) ) = ( D ` J ) )' % ph)
    w.qed([v, f], 'eqtrd', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph, UP))
    return w.run()


def tm2stkupc():
    lab = 'tm2stkupc'
    ph = '( ( %s /\\ K =/= J ) /\\ %s /\\ %s )' % (TD, PK, PJ)
    D1 = U1('D', 'K', 'Y')
    D2 = U1('D', 'J', 'Z')
    LH = U1(D1, 'J', 'Z')
    RH = U1(D2, 'K', 'Y')
    LIF = 'if ( i = J , Z , if ( i = K , Y , ( D ` i ) ) )'
    RIF = 'if ( i = K , Y , if ( i = J , Z , ( D ` i ) ) )'
    w = W(lab, 'Two updates of a stack assignment at distinct indices commute.  '
               'With ~ tm2stkup2 this is the whole multi-stack bookkeeping of '
               'the machine layer; Lean gets it from ` Function.update_comm ` .')
    p1 = w.s([], 'simp1', '( %s -> ( %s /\\ K =/= J ) )' % (ph, TD))
    td = w.s([p1], 'simpld', '( %s -> %s )' % (ph, TD))
    tv = w.s([td], 'simpld', '( %s -> T e. V )' % ph)
    kj = w.s([p1], 'simprd', '( %s -> K =/= J )' % ph)
    p2 = w.s([], 'simp2', '( %s -> %s )' % (ph, PK))
    p3 = w.s([], 'simp3', '( %s -> %s )' % (ph, PJ))
    kk = w.s([p2], 'simpld', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([p3], 'simpld', '( %s -> J e. %s )' % (ph, DG))
    dd = w.s([td], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    d1 = w.s([tv, dd, p2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D1, STK('T')))
    d2 = w.s([tv, dd, p3, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2, STK('T')))
    lh = w.s([tv, d1, p3, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, LH, STK('T')))
    rh = w.s([tv, d2, p2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, RH, STK('T')))
    lfn = w.s([tv, lh, w.inst('tm2stkfn')], 'syl2anc', '( %s -> %s Fn %s )' % (ph, LH, DG))
    rfn = w.s([tv, rh, w.inst('tm2stkfn')], 'syl2anc', '( %s -> %s Fn %s )' % (ph, RH, DG))
    # the pointwise equality
    pi = '( %s /\\ i e. %s )' % (ph, DG)
    def A(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (pi, f))
    tvi = A(tv, 'T e. V'); ddi = A(dd, 'D e. %s' % STK('T'))
    d1i = A(d1, '%s e. %s' % (D1, STK('T'))); d2i = A(d2, '%s e. %s' % (D2, STK('T')))
    p2i = A(p2, PK); p3i = A(p3, PJ); kji = A(kj, 'K =/= J')
    ii = w.s([], 'simpr', '( %s -> i e. %s )' % (pi, DG))
    t1 = w.s([tvi, d1i], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (pi, D1, STK('T')))
    t2 = w.s([tvi, d2i], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (pi, D2, STK('T')))
    t0 = w.s([tvi, ddi], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (pi, STK('T')))
    v1 = w.s([t1, p3i, ii, w.inst('tm2stkupv')], 'syl3anc',
             '( %s -> ( %s ` i ) = if ( i = J , Z , ( %s ` i ) ) )' % (pi, LH, D1))
    v2 = w.s([t0, p2i, ii, w.inst('tm2stkupv')], 'syl3anc',
             '( %s -> ( %s ` i ) = if ( i = K , Y , ( D ` i ) ) )' % (pi, D1))
    e1 = w.s([v2], 'ifeq2d', '( %s -> if ( i = J , Z , ( %s ` i ) ) = %s )' % (pi, D1, LIF))
    lv = w.s([v1, e1], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (pi, LH, LIF))
    v3 = w.s([t2, p2i, ii, w.inst('tm2stkupv')], 'syl3anc',
             '( %s -> ( %s ` i ) = if ( i = K , Y , ( %s ` i ) ) )' % (pi, RH, D2))
    v4 = w.s([t0, p3i, ii, w.inst('tm2stkupv')], 'syl3anc',
             '( %s -> ( %s ` i ) = if ( i = J , Z , ( D ` i ) ) )' % (pi, D2))
    e2 = w.s([v4], 'ifeq2d', '( %s -> if ( i = K , Y , ( %s ` i ) ) = %s )' % (pi, D2, RIF))
    rv = w.s([v3, e2], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (pi, RH, RIF))
    # the if-swap, by cases on i = J
    pa = '( %s /\\ i = J )' % pi
    a1 = w.s([], 'simpr', '( %s -> i = J )' % pa)
    a2 = w.s([kji], 'adantr', '( %s -> K =/= J )' % pa)
    a3 = w.s([a2], 'necomd', '( %s -> J =/= K )' % pa)
    a4 = w.s([a1, a3], 'eqnetrd', '( %s -> i =/= K )' % pa)
    a5 = w.s([a4], 'neneqd', '( %s -> -. i = K )' % pa)
    la = w.s([a1], 'iftrued', '( %s -> %s = Z )' % (pa, LIF))
    ra1 = w.s([a5], 'iffalsed', '( %s -> %s = if ( i = J , Z , ( D ` i ) ) )' % (pa, RIF))
    ra2 = w.s([a1], 'iftrued', '( %s -> if ( i = J , Z , ( D ` i ) ) = Z )' % pa)
    ra = w.s([ra1, ra2], 'eqtrd', '( %s -> %s = Z )' % (pa, RIF))
    ca = w.s([la, ra], 'eqtr4d', '( %s -> %s = %s )' % (pa, LIF, RIF))
    pb = '( %s /\\ -. i = J )' % pi
    b1 = w.s([], 'simpr', '( %s -> -. i = J )' % pb)
    lb = w.s([b1], 'iffalsed', '( %s -> %s = if ( i = K , Y , ( D ` i ) ) )' % (pb, LIF))
    rb0 = w.s([b1], 'iffalsed', '( %s -> if ( i = J , Z , ( D ` i ) ) = ( D ` i ) )' % pb)
    rb = w.s([rb0], 'ifeq2d', '( %s -> %s = if ( i = K , Y , ( D ` i ) ) )' % (pb, RIF))
    cb = w.s([lb, rb], 'eqtr4d', '( %s -> %s = %s )' % (pb, LIF, RIF))
    sw = w.s([ca, cb], 'pm2.61dan', '( %s -> %s = %s )' % (pi, LIF, RIF))
    t3 = w.s([lv, sw], 'eqtrd', '( %s -> ( %s ` i ) = %s )' % (pi, LH, RIF))
    fin = w.s([t3, rv], 'eqtr4d', '( %s -> ( %s ` i ) = ( %s ` i ) )' % (pi, LH, RH))
    ral = w.s([fin], 'ralrimiva', '( %s -> A. i e. %s ( %s ` i ) = ( %s ` i ) )' % (ph, DG, LH, RH))
    bi = w.s([lfn, rfn, w.inst('eqfnfv')], 'syl2anc',
             '( %s -> ( %s = %s <-> A. i e. %s ( %s ` i ) = ( %s ` i ) ) )' % (ph, LH, RH, DG, LH, RH))
    w.qed([bi, ral], 'mpbird', '( %s -> %s = %s )' % (ph, LH, RH))
    return w.run()





PK2 = '( K e. %s /\\ ( Y e. Word %s /\\ U e. Word %s ) )' % (DG, GK, GK)
PJ2 = '( J e. %s /\\ ( Z e. Word %s /\\ R e. Word %s ) )' % (DG, GJ, GJ)


def _ctx(w, ph, pk, pj):
    p1 = w.s([], 'simp1', '( %s -> ( %s /\\ K =/= J ) )' % (ph, TD))
    td = w.s([p1], 'simpld', '( %s -> %s )' % (ph, TD))
    tv = w.s([td], 'simpld', '( %s -> T e. V )' % ph)
    dd = w.s([td], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    kj = w.s([p1], 'simprd', '( %s -> K =/= J )' % ph)
    p2 = w.s([], 'simp2', '( %s -> %s )' % (ph, pk))
    p3 = w.s([], 'simp3', '( %s -> %s )' % (ph, pj))
    kk = w.s([p2], 'simpld', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([p3], 'simpld', '( %s -> J e. %s )' % (ph, DG))
    return dict(p1=p1, td=td, tv=tv, dd=dd, kj=kj, p2=p2, p3=p3, kk=kk, jj=jj)


def tm2stkup3():
    lab = 'tm2stkup3'
    ph = '( ( %s /\\ K =/= J ) /\\ %s /\\ %s )' % (TD, PK2, PJ)
    w = W(lab, 'Three updates of a stack assignment at two distinct indices: '
               'the second update at ` K ` overrides the first.  One machine '
               'step that pops ` K ` and pushes on ` J ` produces exactly this '
               'term; ~ tm2stkupc and ~ tm2stkup2 collapse it.')
    c = _ctx(w, ph, PK2, PJ)
    tv, dd, kj, p3, kk, jj = c['tv'], c['dd'], c['kj'], c['p3'], c['kk'], c['jj']
    yy = w.s([c['p2'], w.inst('simprl')], 'syl', '( %s -> Y e. Word %s )' % (ph, GK))
    u2 = w.s([c['p2'], w.inst('simprr')], 'syl', '( %s -> U e. Word %s )' % (ph, GK))
    zz = w.s([c['p3'], w.inst('simpr')], 'syl', '( %s -> Z e. Word %s )' % (ph, GJ))
    pky = w.s([kk, yy], 'jca', '( %s -> ( K e. %s /\\ Y e. Word %s ) )' % (ph, DG, GK))
    pku2 = w.s([kk, u2], 'jca', '( %s -> ( K e. %s /\\ U e. Word %s ) )' % (ph, DG, GK))
    D1 = U1('D', 'K', 'Y'); D2 = U1('D', 'J', 'Z'); DY2 = U1('D', 'K', 'U')
    LI = U1(D1, 'J', 'Z'); RI = U1(D2, 'K', 'Y')
    LH = U1(LI, 'K', 'U')
    tdj = w.s([c['td'], kj], 'jca', '( %s -> ( %s /\\ K =/= J ) )' % (ph, TD))
    sw = w.s([tdj, pky, p3, w.inst('tm2stkupc')], 'syl3anc', '( %s -> %s = %s )' % (ph, LI, RI))
    st, new = w.rewrite(LH, {LI: (RI, sw)}, ph)
    assert new == U1(RI, 'K', 'U'), new
    d2 = w.s([tv, dd, p3, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, D2, STK('T')))
    t2 = w.s([tv, d2], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D2, STK('T')))
    yj = w.s([yy, u2], 'jca', '( %s -> ( Y e. Word %s /\\ U e. Word %s ) )' % (ph, GK, GK))
    col = w.s([t2, kk, yj, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )' % (ph, U1(RI, 'K', 'U'), U1(D2, 'K', 'U')))
    sw2 = w.s([tdj, pku2, p3, w.inst('tm2stkupc')], 'syl3anc',
              '( %s -> %s = %s )' % (ph, U1(DY2, 'J', 'Z'), U1(D2, 'K', 'U')))
    sw2c = w.s([sw2], 'eqcomd', '( %s -> %s = %s )' % (ph, U1(D2, 'K', 'U'), U1(DY2, 'J', 'Z')))
    a1 = w.s([st, col], 'eqtrd', '( %s -> %s = %s )' % (ph, LH, U1(D2, 'K', 'U')))
    w.qed([a1, sw2c], 'eqtrd', '( %s -> %s = %s )' % (ph, LH, U1(DY2, 'J', 'Z')))
    return w.run()


def tm2stkup4():
    lab = 'tm2stkup4'
    ph = '( ( %s /\\ K =/= J ) /\\ %s /\\ %s )' % (TD, PK2, PJ2)
    w = W(lab, 'Four updates of a stack assignment at two distinct indices '
               'collapse to two: the term one iteration of a two-stack scan '
               'loop produces, reduced to the loop invariant\'s form.')
    c = _ctx(w, ph, PK2, PJ2)
    tv, dd, kj, kk, jj = c['tv'], c['dd'], c['kj'], c['kk'], c['jj']
    yy = w.s([c['p2'], w.inst('simprl')], 'syl', '( %s -> Y e. Word %s )' % (ph, GK))
    u2 = w.s([c['p2'], w.inst('simprr')], 'syl', '( %s -> U e. Word %s )' % (ph, GK))
    zz = w.s([c['p3'], w.inst('simprl')], 'syl', '( %s -> Z e. Word %s )' % (ph, GJ))
    r2 = w.s([c['p3'], w.inst('simprr')], 'syl', '( %s -> R e. Word %s )' % (ph, GJ))
    pjz = w.s([jj, zz], 'jca', '( %s -> ( J e. %s /\\ Z e. Word %s ) )' % (ph, DG, GJ))
    D1 = U1('D', 'K', 'Y'); DY2 = U1('D', 'K', 'U')
    LI = U1(D1, 'J', 'Z')
    L3 = U1(LI, 'K', 'U')
    M3 = U1(DY2, 'J', 'Z')
    LH = U1(L3, 'J', 'R')
    tdj = w.s([c['td'], kj], 'jca', '( %s -> ( %s /\\ K =/= J ) )' % (ph, TD))
    t3 = w.s([tdj, c['p2'], pjz, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )' % (ph, L3, M3))
    st, new = w.rewrite(LH, {L3: (M3, t3)}, ph)
    assert new == U1(M3, 'J', 'R'), new
    pku2 = w.s([kk, u2], 'jca', '( %s -> ( K e. %s /\\ U e. Word %s ) )' % (ph, DG, GK))
    dy2 = w.s([tv, dd, pku2, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DY2, STK('T')))
    t2 = w.s([tv, dy2], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, DY2, STK('T')))
    zj = w.s([zz, r2], 'jca', '( %s -> ( Z e. Word %s /\\ R e. Word %s ) )' % (ph, GJ, GJ))
    col = w.s([t2, jj, zj, w.inst('tm2stkup2')], 'syl3anc',
              '( %s -> %s = %s )' % (ph, U1(M3, 'J', 'R'), U1(DY2, 'J', 'R')))
    w.qed([st, col], 'eqtrd', '( %s -> %s = %s )' % (ph, LH, U1(DY2, 'J', 'R')))
    return w.run()


GI = '( %s ` I )' % G('T')
NE3 = "( K =/= J /\\ K =/= I /\\ J =/= I )"
QK = "( K e. %s /\\ ( Y e. Word %s /\\ Y' e. Word %s ) )" % (DG, GK, GK)
QJ = "( J e. %s /\\ ( Z e. Word %s /\\ Z' e. Word %s ) )" % (DG, GJ, GJ)
QI = "( I e. %s /\\ ( N e. Word %s /\\ N' e. Word %s ) )" % (DG, GI, GI)


def tm2stkup6():
    lab = 'tm2stkup6'
    ph = '( ( %s /\\ %s ) /\\ %s /\\ ( %s /\\ %s ) )' % (TD, NE3, QK, QJ, QI)
    w = W(lab, 'Six updates of a stack assignment at three distinct indices '
               'collapse to three: the term one iteration of a three-stack scan '
               'loop produces, reduced to the loop invariant\'s form.  '
               '~ tm2stkupc , ~ tm2stkup3 and ~ tm2stkup2 .')
    p1 = w.s([], 'simp1', '( %s -> ( %s /\\ %s ) )' % (ph, TD, NE3))
    td = w.s([p1], 'simpld', '( %s -> %s )' % (ph, TD))
    tv = w.s([td], 'simpld', '( %s -> T e. V )' % ph)
    dd = w.s([td], 'simprd', '( %s -> D e. %s )' % (ph, STK('T')))
    ne = w.s([p1], 'simprd', '( %s -> %s )' % (ph, NE3))
    kj = w.s([ne, w.inst('simp1')], 'syl', '( %s -> K =/= J )' % ph)
    ki = w.s([ne, w.inst('simp2')], 'syl', '( %s -> K =/= I )' % ph)
    ji = w.s([ne, w.inst('simp3')], 'syl', '( %s -> J =/= I )' % ph)
    ik = w.s([ki], 'necomd', '( %s -> I =/= K )' % ph)
    ij = w.s([ji], 'necomd', '( %s -> I =/= J )' % ph)
    qk = w.s([], 'simp2', '( %s -> %s )' % (ph, QK))
    q23 = w.s([], 'simp3', '( %s -> ( %s /\\ %s ) )' % (ph, QJ, QI))
    qj = w.s([q23], 'simpld', '( %s -> %s )' % (ph, QJ))
    qi = w.s([q23], 'simprd', '( %s -> %s )' % (ph, QI))
    kk = w.s([qk], 'simpld', '( %s -> K e. %s )' % (ph, DG))
    jj = w.s([qj], 'simpld', '( %s -> J e. %s )' % (ph, DG))
    ii = w.s([qi], 'simpld', '( %s -> I e. %s )' % (ph, DG))
    yy = w.s([qk, w.inst('simprl')], 'syl', '( %s -> Y e. Word %s )' % (ph, GK))
    yp = w.s([qk, w.inst('simprr')], 'syl', "( %s -> Y' e. Word %s )" % (ph, GK))
    zz = w.s([qj, w.inst('simprl')], 'syl', '( %s -> Z e. Word %s )' % (ph, GJ))
    zp = w.s([qj, w.inst('simprr')], 'syl', "( %s -> Z' e. Word %s )" % (ph, GJ))
    nn = w.s([qi, w.inst('simprl')], 'syl', '( %s -> N e. Word %s )' % (ph, GI))
    npp = w.s([qi, w.inst('simprr')], 'syl', "( %s -> N' e. Word %s )" % (ph, GI))
    pky = w.s([kk, yy], 'jca', '( %s -> ( K e. %s /\\ Y e. Word %s ) )' % (ph, DG, GK))
    pkyp = w.s([kk, yp], 'jca', "( %s -> ( K e. %s /\\ Y' e. Word %s ) )" % (ph, DG, GK))
    pjz = w.s([jj, zz], 'jca', '( %s -> ( J e. %s /\\ Z e. Word %s ) )' % (ph, DG, GJ))
    pjzp = w.s([jj, zp], 'jca', "( %s -> ( J e. %s /\\ Z' e. Word %s ) )" % (ph, DG, GJ))
    pin = w.s([ii, nn], 'jca', '( %s -> ( I e. %s /\\ N e. Word %s ) )' % (ph, DG, GI))
    pinp = w.s([ii, npp], 'jca', "( %s -> ( I e. %s /\\ N' e. Word %s ) )" % (ph, DG, GI))
    Z1 = U1('D', 'K', 'Y'); Z2 = U1(Z1, 'J', 'Z'); Z3 = U1(Z2, 'I', 'N')
    DY = U1('D', 'K', "Y'"); W2 = U1(DY, 'J', 'Z'); W3 = U1(W2, 'I', 'N')
    V2 = U1(DY, 'J', "Z'"); V3 = U1(V2, 'I', 'N')
    TGT = U1(V2, 'I', "N'")
    z1 = w.s([tv, dd, pky, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, Z1, STK('T')))
    z2 = w.s([tv, z1, pjz, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, Z2, STK('T')))
    dy = w.s([tv, dd, pkyp, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, DY, STK('T')))
    w2 = w.s([tv, dy, pjz, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, W2, STK('T')))
    v2 = w.s([tv, dy, pjzp, w.inst('tm2stkupd')], 'syl3anc', '( %s -> %s e. %s )' % (ph, V2, STK('T')))
    # step 1: UPD( Z3 , K , Y' ) = W3
    tdik = w.s([w.s([tv, z2], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, Z2, STK('T'))), ik],
               'jca', '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ I =/= K ) )' % (ph, Z2, STK('T')))
    sw1 = w.s([tdik, pin, pkyp, w.inst('tm2stkupc')], 'syl3anc',
              "( %s -> %s = %s )" % (ph, U1(Z3, 'K', "Y'"), U1(U1(Z2, 'K', "Y'"), 'I', 'N')))
    tdkj = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK('T'))), kj],
               'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= J ) )' % (ph, STK('T')))
    pk2 = w.s([kk, w.s([yy, yp], 'jca', "( %s -> ( Y e. Word %s /\\ Y' e. Word %s ) )" % (ph, GK, GK))],
              'jca', "( %s -> ( K e. %s /\\ ( Y e. Word %s /\\ Y' e. Word %s ) ) )" % (ph, DG, GK, GK))
    u3 = w.s([tdkj, pk2, pjz, w.inst('tm2stkup3')], 'syl3anc',
             "( %s -> %s = %s )" % (ph, U1(Z2, 'K', "Y'"), W2))
    r1, n1 = w.rewrite(U1(U1(Z2, 'K', "Y'"), 'I', 'N'), {U1(Z2, 'K', "Y'"): (W2, u3)}, ph)
    assert n1 == W3, n1
    t1 = w.s([sw1, r1], 'eqtrd', "( %s -> %s = %s )" % (ph, U1(Z3, 'K', "Y'"), W3))
    # step 2: UPD( W3 , J , Z' ) = V3
    tdij = w.s([w.s([tv, w2], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, W2, STK('T'))), ij],
               'jca', '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ I =/= J ) )' % (ph, W2, STK('T')))
    sw2 = w.s([tdij, pin, pjzp, w.inst('tm2stkupc')], 'syl3anc',
              "( %s -> %s = %s )" % (ph, U1(W3, 'J', "Z'"), U1(U1(W2, 'J', "Z'"), 'I', 'N')))
    tdy = w.s([tv, dy], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, DY, STK('T')))
    pj2 = w.s([zz, zp], 'jca', "( %s -> ( Z e. Word %s /\\ Z' e. Word %s ) )" % (ph, GJ, GJ))
    c2 = w.s([tdy, jj, pj2, w.inst('tm2stkup2')], 'syl3anc',
             "( %s -> %s = %s )" % (ph, U1(W2, 'J', "Z'"), V2))
    r2, n2 = w.rewrite(U1(U1(W2, 'J', "Z'"), 'I', 'N'), {U1(W2, 'J', "Z'"): (V2, c2)}, ph)
    assert n2 == V3, n2
    t2 = w.s([sw2, r2], 'eqtrd', "( %s -> %s = %s )" % (ph, U1(W3, 'J', "Z'"), V3))
    # assemble
    LH = U1(U1(U1(Z3, 'K', "Y'"), 'J', "Z'"), 'I', "N'")
    ra, na = w.rewrite(LH, {U1(Z3, 'K', "Y'"): (W3, t1)}, ph)
    assert na == U1(U1(W3, 'J', "Z'"), 'I', "N'"), na
    rb, nb = w.rewrite(U1(U1(W3, 'J', "Z'"), 'I', "N'"), {U1(W3, 'J', "Z'"): (V3, t2)}, ph)
    assert nb == U1(V3, 'I', "N'"), nb
    tv2 = w.s([tv, v2], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, V2, STK('T')))
    pi2 = w.s([nn, npp], 'jca', "( %s -> ( N e. Word %s /\\ N' e. Word %s ) )" % (ph, GI, GI))
    c3 = w.s([tv2, ii, pi2, w.inst('tm2stkup2')], 'syl3anc',
             "( %s -> %s = %s )" % (ph, U1(V3, 'I', "N'"), TGT))
    e1 = w.s([ra, rb], 'eqtrd', "( %s -> %s = %s )" % (ph, LH, U1(V3, 'I', "N'")))
    w.qed([e1, c3], 'eqtrd', "( %s -> %s = %s )" % (ph, LH, TGT))
    return w.run()


if __name__ == '__main__':
    if want('tm2stkupn'): tm2stkupn()
    if want('tm2stkupc'): tm2stkupc()
    if want('tm2stkup3'): tm2stkup3()
    if want('tm2stkup4'): tm2stkup4()
    if want('tm2stkup6'): tm2stkup6()
