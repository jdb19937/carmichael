"""Sortie C10: the Jensen count on a rectangle of zeros (jenrct)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
from cl import lift
from c10_freeze import S as FS, RX1, RX2, RX3, ZR, AM, BM
from c8_o import center_int, sqab_st


def gen_jenrct():
    w = W('jenrct', "Jensen's inequality for the zeros of ` F ` in a rectangle ` A crect B ` all within ` V ` of a point ` C ` of the rectangle with ` F ( C ) =/= 0 ` : with ` abs F <_ Y ` on the square of half-side ` R >_ V ` about ` C ` , ` sum ( F holord q ) x. log ( R / V ) <_ log ( Y / abs F ( C ) ) ` ( ~ holzfac , ~ holzord , ~ jenbl ).")
    A0 = '( %s /\\ %s /\\ %s )' % (RX1, RX2, RX3)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    x1 = s([], 'simp1', RX1); x2 = s([], 'simp2', RX2); x3 = s([], 'simp3', RX3)
    RECT = '( A crect B )'
    hol = s([x1, w.inst('simp1')], 'syl', HOL)
    abg = s([x1, w.inst('simp2')], 'syl', '( ( A e. CC /\\ B e. CC ) /\\ %s )' % GEOG('A', 'B'))
    nest = s([x1, w.inst('simp3')], 'syl', '( M e. RR+ /\\ ( %s crect %s ) C_ D )' % (AM, BM))
    x2a = s([x2, w.inst('simp1')], 'syl', '( C e. %s /\\ ( F ` C ) =/= 0 )' % RECT)
    x2b = s([x2, w.inst('simp2')], 'syl', '( R e. RR+ /\\ %s C_ D )' % SQ('C', 'R'))
    x2c = s([x2, w.inst('simp3')], 'syl', '( V e. RR+ /\\ V <_ R /\\ A. j e. %s ( abs ` ( C - j ) ) <_ V )' % RECT)
    cin = s([x2a, w.inst('simpl')], 'syl', 'C e. %s' % RECT); fc0 = s([x2a, w.inst('simpr')], 'syl', '( F ` C ) =/= 0')
    rp = s([x2b, w.inst('simpl')], 'syl', 'R e. RR+'); sqd = s([x2b, w.inst('simpr')], 'syl', '%s C_ D' % SQ('C', 'R'))
    vp = s([x2c, w.inst('simp1')], 'syl', 'V e. RR+'); vr = s([x2c, w.inst('simp2')], 'syl', 'V <_ R')
    hjr = s([x2c, w.inst('simp3')], 'syl', 'A. j e. %s ( abs ` ( C - j ) ) <_ V' % RECT)
    yr = s([x3, w.inst('simpl')], 'syl', 'Y e. RR'); ybd = s([x3, w.inst('simpr')], 'syl', 'A. x e. %s ( abs ` ( F ` x ) ) <_ Y' % SQ('C', 'R'))
    # holzfac, holzfi
    sb = w.s([w.s([], 'fveq2', '( w = C -> ( F ` w ) = ( F ` C ) )')], 'neeq1d', '( w = C -> ( ( F ` w ) =/= 0 <-> ( F ` C ) =/= 0 ) )')
    wit = s([cin, fc0, w.s([sb], 'rspcev', '( ( C e. %s /\\ ( F ` C ) =/= 0 ) -> E. w e. %s ( F ` w ) =/= 0 )' % (RECT, RECT))], 'syl2anc', 'E. w e. %s ( F ` w ) =/= 0' % RECT)
    HZ = tsub(stmt('holzfac'), {'R': 'M'})
    hza, hzc = ante_of(HZ)
    hzs = s([x1, wit], 'jca', hza)
    hz = s([hzs, w.inst('holzfac')], 'syl', hzc)
    zfin = s([hzs, w.inst('holzfi')], 'syl', '%s e. Fin' % ZR)
    zsr = w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZR, RECT))], 'a1i', '( %s -> %s C_ %s )' % (A0, ZR, RECT))
    rd = s([s([hol, s([abg, w.inst('simpl')], 'syl', '( A e. CC /\\ B e. CC )'), nest], '3jca',
              '( %s /\\ ( A e. CC /\\ B e. CC ) /\\ ( M e. RR+ /\\ ( %s crect %s ) C_ D ) )' % (HOL, AM, BM)), w.inst('holnss')], 'syl', '%s C_ D' % RECT)
    zd = s([zsr, rd], 'sstrd', '%s C_ D' % ZR)
    dcc = s([s([hol, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )'), w.inst('cncfrss')], 'syl', 'D C_ CC')
    cs = s([dcc, s([rd, cin], 'sseldd', 'C e. D')], 'sseldd', 'C e. CC')
    # inside the existentials
    PQ = 'prod_ q e. %s ( ( z - q ) ^ ( o ` q ) )' % ZR
    FACZ = 'A. z e. D ( F ` z ) = ( %s x. ( h ` z ) )' % PQ
    NZ = 'A. z e. %s ( h ` z ) =/= 0' % RECT
    BODY = '( o : %s --> NN /\\ %s /\\ ( %s /\\ %s ) )' % (ZR, HOLG('h', 'D'), FACZ, NZ)
    assert hzc == 'E. o E. h %s' % BODY, hzc
    A1 = '( %s /\\ %s )' % (A0, BODY)
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    L1 = lambda st: lift(w, st, A1)
    of = t([], 'simpr1', 'o : %s --> NN' % ZR); holh = t([], 'simpr2', HOLG('h', 'D'))
    fz3 = t([], 'simpr3', '( %s /\\ %s )' % (FACZ, NZ))
    fac = t([fz3, w.inst('simpl')], 'syl', FACZ); nz = t([fz3, w.inst('simpr')], 'syl', NZ)
    PKz = 'prod_ k e. %s ( ( z - k ) ^ ( o ` k ) )' % ZR
    PKv = 'prod_ k e. %s ( ( v - k ) ^ ( o ` k ) )' % ZR
    eqp = w.s([w.s([w.s([], 'oveq2', '( q = k -> ( z - q ) = ( z - k ) )'), w.s([], 'fveq2', '( q = k -> ( o ` q ) = ( o ` k ) )')], 'oveq12d',
                    '( q = k -> ( ( z - q ) ^ ( o ` q ) ) = ( ( z - k ) ^ ( o ` k ) ) )')], 'cbvprodv', '%s = %s' % (PQ, PKz))
    b1 = w.s([w.s([eqp], 'oveq1i', '( %s x. ( h ` z ) ) = ( %s x. ( h ` z ) )' % (PQ, PKz))], 'eqeq2i',
             '( ( F ` z ) = ( %s x. ( h ` z ) ) <-> ( F ` z ) = ( %s x. ( h ` z ) ) )' % (PQ, PKz))
    FKZ = 'A. z e. D ( F ` z ) = ( %s x. ( h ` z ) )' % PKz
    FKV = 'A. v e. D ( F ` v ) = ( %s x. ( h ` v ) )' % PKv
    r1 = w.s([b1], 'ralbii', '( %s <-> %s )' % (FACZ, FKZ))
    subv = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )'),
                w.s([w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z - k ) = ( v - k ) )')], 'oveq1d', '( z = v -> ( ( z - k ) ^ ( o ` k ) ) = ( ( v - k ) ^ ( o ` k ) ) )')], 'prodeq2sdv',
                          '( z = v -> %s = %s )' % (PKz, PKv)), w.s([], 'fveq2', '( z = v -> ( h ` z ) = ( h ` v ) )')], 'oveq12d',
                    '( z = v -> ( %s x. ( h ` z ) ) = ( %s x. ( h ` v ) ) )' % (PKz, PKv))], 'eqeq12d',
               '( z = v -> ( ( F ` z ) = ( %s x. ( h ` z ) ) <-> ( F ` v ) = ( %s x. ( h ` v ) ) ) )' % (PKz, PKv))
    r2 = w.s([subv], 'cbvralvw', '( %s <-> %s )' % (FKZ, FKV))
    fkv = t([fac, w.s([r1, r2], 'bitri', '( %s <-> %s )' % (FACZ, FKV))], 'sylib', FKV)
    NZZ = 'A. z e. %s ( h ` z ) =/= 0' % ZR
    NZV = 'A. v e. %s ( h ` v ) =/= 0' % ZR
    nzz = t([nz, t([L1(zsr), w.inst('ssralv')], 'syl', '( %s -> %s )' % (NZ, NZZ))], 'mpd', NZZ)
    nzv = t([nzz, w.s([w.s([w.s([], 'fveq2', '( z = v -> ( h ` z ) = ( h ` v ) )')], 'neeq1d', '( z = v -> ( ( h ` z ) =/= 0 <-> ( h ` v ) =/= 0 ) )')], 'cbvralvw', '( %s <-> %s )' % (NZZ, NZV))],
            'sylib', NZV)
    HO = tsub(stmt('holzord'), {'Z': ZR, 'P': 'p', 'O': 'o', 'H': 'h'})
    hoa, hoc = ante_of(HO)
    Q1 = '( %s /\\ ( %s e. Fin /\\ %s C_ D ) )' % (HOL, ZR, ZR)
    Q2 = '( ( o : %s --> NN /\\ %s ) /\\ ( %s /\\ %s ) )' % (ZR, HOLG('h', 'D'), FKV, NZV)
    assert hoa == '( %s /\\ %s /\\ p e. %s )' % (Q1, Q2, ZR), hoa
    Ap = '( %s /\\ p e. %s )' % (A1, ZR)
    Lp = lambda st: lift(w, st, Ap)
    q1 = t([L1(hol), t([L1(zfin), L1(zd)], 'jca', '( %s e. Fin /\\ %s C_ D )' % (ZR, ZR))], 'jca', Q1)
    q2 = t([t([of, holh], 'jca', '( o : %s --> NN /\\ %s )' % (ZR, HOLG('h', 'D'))), t([fkv, nzv], 'jca', '( %s /\\ %s )' % (FKV, NZV))], 'jca', Q2)
    pz = w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, ZR))
    hop = w.s([w.s([Lp(q1), Lp(q2), pz], '3jca', '( %s -> %s )' % (Ap, hoa)), w.inst('holzord')], 'syl', '( %s -> %s )' % (Ap, hoc))
    opn = w.s([Lp(of), pz], 'ffvelcdmd', '( %s -> ( o ` p ) e. NN )' % Ap)
    hpn = w.s([hop, opn], 'eqeltrrd', '( %s -> ( F holord p ) e. NN )' % Ap)
    alp = t([hpn], 'ralrimiva', 'A. p e. %s ( F holord p ) e. NN' % ZR)
    ALQN = 'A. q e. %s ( F holord q ) e. NN' % ZR
    alq = t([alp, w.s([w.s([w.s([], 'oveq2', '( p = q -> ( F holord p ) = ( F holord q ) )')], 'eleq1d', '( p = q -> ( ( F holord p ) e. NN <-> ( F holord q ) e. NN ) )')],
                      'cbvralvw', '( A. p e. %s ( F holord p ) e. NN <-> %s )' % (ZR, ALQN))], 'sylib', ALQN)
    B1p, B1q = '( o ` p ) = ( F holord p )', '( o ` q ) = ( F holord q )'
    s1p = t([hop], 'ralrimiva', 'A. p e. %s %s' % (ZR, B1p))
    c1 = w.s([w.s([w.s([], 'fveq2', '( p = q -> ( o ` p ) = ( o ` q ) )'), w.s([], 'oveq2', '( p = q -> ( F holord p ) = ( F holord q ) )')], 'eqeq12d', '( p = q -> ( %s <-> %s ) )' % (B1p, B1q))],
             'cbvralvw', '( A. p e. %s %s <-> A. q e. %s %s )' % (ZR, B1p, ZR, B1q))
    s1q = t([s1p, c1], 'sylib', 'A. q e. %s %s' % (ZR, B1q))
    SO = 'sum_ q e. %s ( o ` q )' % ZR
    SH = 'sum_ q e. %s ( F holord q )' % ZR
    se = t([s1q, w.inst('sumeq2')], 'syl', '%s = %s' % (SO, SH))
    # jenbl
    JB = tsub(FS['jenbl'], {'Z': ZR, 'O': 'o', 'H': 'h', 'B': 'Y'})
    jba, jbc = ante_of(JB)
    J1, J2, J3 = top_and(jba)
    j1 = t([q1, t([t([of, holh], 'jca', '( o : %s --> NN /\\ %s )' % (ZR, HOLG('h', 'D'))), fac], 'jca', '( ( o : %s --> NN /\\ %s ) /\\ %s )' % (ZR, HOLG('h', 'D'), FACZ))], 'jca', J1)
    hjz = t([L1(hjr), t([L1(zsr), w.inst('ssralv')], 'syl', '( A. j e. %s ( abs ` ( C - j ) ) <_ V -> A. j e. %s ( abs ` ( C - j ) ) <_ V )' % (RECT, ZR))], 'mpd',
            'A. j e. %s ( abs ` ( C - j ) ) <_ V' % ZR)
    j2 = t([t([L1(cs), L1(rp), L1(sqd)], '3jca', '( C e. CC /\\ R e. RR+ /\\ %s C_ D )' % SQ('C', 'R')), t([L1(vp), L1(vr), hjz], '3jca',
            '( V e. RR+ /\\ V <_ R /\\ A. j e. %s ( abs ` ( C - j ) ) <_ V )' % ZR)], 'jca', J2)
    rr = s([rp], 'rpred', 'R e. RR')
    ab = sqab_st(w, A0, cs, rr, 'C', 'R')
    intc = center_int(w, A0, cs, rr, s([rp], 'rpgt0d', '0 < R'), 'C', 'R')
    FR = FRM('C', 'R')
    frp = w.s([ab, intc, w.inst('crectfrp')], 'syl2anc', '( %s -> %s C_ ( %s \\ { C } ) )' % (A0, FR, SQ('C', 'R')))
    frs = s([frp, s([], 'difssd', '( %s \\ { C } ) C_ %s' % (SQ('C', 'R'), SQ('C', 'R')))], 'sstrd', '%s C_ %s' % (FR, SQ('C', 'R')))
    AX = 'A. x e. %s ( abs ` ( F ` x ) ) <_ Y' % FR
    AU = 'A. u e. %s ( abs ` ( F ` u ) ) <_ Y' % FR
    ybf = s([ybd, s([frs, w.inst('ssralv')], 'syl', '( A. x e. %s ( abs ` ( F ` x ) ) <_ Y -> %s )' % (SQ('C', 'R'), AX))], 'mpd', AX)
    ybu = s([ybf, w.s([w.s([w.s([w.s([], 'fveq2', '( x = u -> ( F ` x ) = ( F ` u ) )')], 'fveq2d', '( x = u -> ( abs ` ( F ` x ) ) = ( abs ` ( F ` u ) ) )')], 'breq1d',
                            '( x = u -> ( ( abs ` ( F ` x ) ) <_ Y <-> ( abs ` ( F ` u ) ) <_ Y ) )')], 'cbvralvw', '( %s <-> %s )' % (AX, AU))], 'sylib', AU)
    j3 = t([t([L1(yr), L1(ybu)], 'jca', '( Y e. RR /\\ %s )' % AU), L1(fc0)], 'jca', J3)
    jb = t([t([j1, j2, j3], '3jca', jba), w.inst('jenbl')], 'syl', jbc)
    INEQ = '( %s x. ( log ` ( R / V ) ) ) <_ ( log ` ( Y / ( abs ` ( F ` C ) ) ) )' % SH
    ineq = t([t([se], 'oveq1d', '( %s x. ( log ` ( R / V ) ) ) = ( %s x. ( log ` ( R / V ) ) )' % (SO, SH)), jb], 'eqbrtrrd', INEQ)
    PAIR = '( %s /\\ %s )' % (ALQN, INEQ)
    inner = t([alq, ineq], 'jca', PAIR)
    el = s([w.s([inner], 'ex', '( %s -> ( %s -> %s ) )' % (A0, BODY, PAIR))], 'exlimdvv', '( %s -> %s )' % (hzc, PAIR))
    pr = s([hz, el], 'mpd', PAIR)
    goal = '( %s -> ( %s e. Fin /\\ %s /\\ %s ) )' % (A0, ZR, ALQN, INEQ)
    assert goal == FS['jenrct'], goal
    w.qed([zfin, s([pr, w.inst('simpl')], 'syl', ALQN), s([pr, w.inst('simpr')], 'syl', INEQ)], '3jca', goal)
    return run8(w)


if __name__ == '__main__':
    gen_jenrct()
