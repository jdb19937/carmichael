"""Sortie ZC1: the zeroDiskFinset layer for a generic F on the right half-plane: finite order on the 7/4 square (zdord),
the factorisation with holord exponents on the 13/8 square (zdfac)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import num
from c8_o import numst
from c8_n import sqparts, sqre_at, sqcc
import c9_h
patch(c9_h)
from c9_h import c0_facts
import lin
lin.FASTPATH = True

HA = '( %s /\\ T e. RR /\\ ( F ` %s ) =/= 0 )' % (HOLF('F', HP0), CT('T'))
S['zdord'] = ('( ( %s /\\ U e. %s ) -> ( ( F holord U ) e. NN0 /\\ E. g ( %s /\\ ( g ` U ) =/= 0 /\\ A. z e. %s ( F ` z ) = ( ( ( z - U ) ^ ( F holord U ) ) x. ( g ` z ) ) ) ) )') % (
    HA, SQ(CT('T'), R74), HOLF('g', HP0), HP0)
Z13 = ZS('F', 'T')
S['zdfac'] = ('( %s -> E. h ( %s /\\ A. z e. %s ( F ` z ) = ( prod_ q e. %s ( ( z - q ) ^ ( F holord q ) ) x. ( h ` z ) ) /\\ A. z e. %s ( h ` z ) =/= 0 ) )') % (
    HA, HOLF('h', HP0), HP0, Z13, SQ(CT('T'), R138))


def ctr_in(w, A0, c0, re0, im0, r):
    """( A0 -> C0 e. SQ(C0, r) ) for a literal 0 < r"""
    rr = numst(w, A0, r, 'RR')
    a, b = sqcc(w, A0, c0, rr, c=C0, r=r)
    ps = sqparts(w, A0, sqre_at(w, A0, c0, rr, c=C0, r=r), c=C0, r=r)
    SA, SB = SQA(C0, r), SQB(C0, r)
    s = lambda h, rf, f: w.s(h, rf, '( %s -> %s )' % (A0, f))
    lv = {}
    for e, st in (('( Re ` %s )' % C0, c0), ('( Im ` %s )' % C0, c0), ('( Re ` %s )' % SA, a), ('( Im ` %s )' % SA, a), ('( Re ` %s )' % SB, b), ('( Im ` %s )' % SB, b)):
        lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hy = [re0, im0] + ps
    INS = INTG(SA, SB, C0)
    ins = s([c0, s([s([lin8(w, A0, hy, '( Re ` %s ) < ( Re ` %s )' % (SA, C0), lv), lin8(w, A0, hy, '( Re ` %s ) < ( Re ` %s )' % (C0, SB), lv)], 'jca',
                       '( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) )' % (SA, C0, C0, SB)),
                     s([lin8(w, A0, hy, '( Im ` %s ) < ( Im ` %s )' % (SA, C0), lv), lin8(w, A0, hy, '( Im ` %s ) < ( Im ` %s )' % (C0, SB), lv)], 'jca',
                       '( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) )' % (SA, C0, C0, SB))], 'jca', INS[len('( %s e. CC /\\ ' % C0):-2])], 'jca', INS)
    return w.s([s([a, b], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), ins, w.inst('crectinp')], 'syl2anc', '( %s -> %s e. %s )' % (A0, C0, SQ(C0, r))), a, b, ps, lv


def sq_hp(w, A0, c0, re0, r):
    """( A0 -> SQ(C0, r) C_ HP0 ) for a literal r < 2"""
    s = lambda h, rf, f: w.s(h, rf, '( %s -> %s )' % (A0, f))
    rr = numst(w, A0, r, 'RR')
    lt = s([lin8(w, A0, [], '%s < 2' % r, {}), re0], 'breqtrrd', '%s < ( Re ` %s )' % (r, C0))
    f = tsub(stmt('sqhp0'), {'C': C0, 'R': r})
    fa, fc = ante_of(f)
    return s([s([s([c0, rr], 'jca', '( %s e. CC /\\ %s e. RR )' % (C0, r)), lt], 'jca', fa), w.inst('sqhp0')], 'syl', fc)


def geo_data(w, A0, c0, re0, im0, r, m, rm):
    """the ABGEO data of holzfi/holzfac/holordfinr for the rectangle SQ(C0, r) with margin m, r + m = rm < 2;
    returns ( step ( A0 -> ABGEO-part1 ), ex step builder )"""
    s = lambda h, rf, f: w.s(h, rf, '( %s -> %s )' % (A0, f))
    cin, a, b, ps, lv = ctr_in(w, A0, c0, re0, im0, r)
    SA, SB = SQA(C0, r), SQB(C0, r)
    geo = s([lin8(w, A0, [ps[0], ps[1]], '( Re ` %s ) <_ ( Re ` %s )' % (SA, SB), lv), lin8(w, A0, [ps[2], ps[3]], '( Im ` %s ) <_ ( Im ` %s )' % (SA, SB), lv)], 'jca', GEOG(SA, SB))
    WM = '( %s + ( _i x. %s ) )' % (m, m)
    X = '( %s + %s )' % (r, m)
    nst = s([s([c0, s([numst(w, A0, r, 'CC'), numst(w, A0, m, 'CC')], 'jca', '( %s e. CC /\\ %s e. CC )' % (r, m))], 'jca', '( %s e. CC /\\ ( %s e. CC /\\ %s e. CC ) )' % (C0, r, m)),
             w.inst('sqnest')], 'syl', '( ( %s - %s ) = %s /\\ ( %s + %s ) = %s )' % (SA, WM, SQA(C0, X), SB, WM, SQB(C0, X)))
    import cl as _cl
    xe = lin.lineq(w, A0, X, rm, closure=_cl.Closure(w, A0, {}))
    ie = s([xe], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (X, rm))
    we = s([xe, ie], 'oveq12d', '( %s + ( _i x. %s ) ) = ( %s + ( _i x. %s ) )' % (X, X, rm, rm))
    ea = s([s([nst, w.inst('simpl')], 'syl', '( %s - %s ) = %s' % (SA, WM, SQA(C0, X))), s([we], 'oveq2d', '%s = %s' % (SQA(C0, X), SQA(C0, rm)))], 'eqtrd', '( %s - %s ) = %s' % (SA, WM, SQA(C0, rm)))
    eb = s([s([nst, w.inst('simpr')], 'syl', '( %s + %s ) = %s' % (SB, WM, SQB(C0, X))), s([we], 'oveq2d', '%s = %s' % (SQB(C0, X), SQB(C0, rm)))], 'eqtrd', '( %s + %s ) = %s' % (SB, WM, SQB(C0, rm)))
    NR = '( ( %s - %s ) crect ( %s + %s ) )' % (SA, WM, SB, WM)
    nd = s([s([ea, eb], 'oveq12d', '%s = %s' % (NR, SQ(C0, rm))), sq_hp(w, A0, c0, re0, rm)], 'eqsstrd', '%s C_ %s' % (NR, HP0))
    nest = s([numst(w, A0, m, 'RR+'), nd], 'jca', '( %s e. RR+ /\\ %s C_ %s )' % (m, NR, HP0))
    return cin, a, b, geo, nest


def gen_zdord():
    w = W('zdord', 'Finite order on the square of half-side ` 7 / 4 ` about ` 2 + i T ` for ` F ` holomorphic on the right half-plane with ` F ( 2 + i T ) =/= 0 ` , with the factorisation ` F = ( z - U ) ^ ( F holord U ) g ` , ` g ( U ) =/= 0 ` (Lean ` analyticOrderAt_ne_top_on_disk ` ; ~ holordfinr ).')
    A0 = '( %s /\\ U e. %s )' % (HA, SQ(C0, R74))
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ha = s([], 'simpl', HA)
    hol = s([ha, w.inst('simp1')], 'syl', HOLF('F', HP0)); tr = s([ha, w.inst('simp2')], 'syl', 'T e. RR'); fc0 = s([ha, w.inst('simp3')], 'syl', '( F ` %s ) =/= 0' % C0)
    um = s([], 'simpr', 'U e. %s' % SQ(C0, R74))
    c0, re0, im0 = c0_facts(w, A0, tr)
    cin, a, b, geo, nest = geo_data(w, A0, c0, re0, im0, R74, R18, '( ; 1 5 / 8 )')
    SA, SB = SQA(C0, R74), SQB(C0, R74)
    H = tsub(stmt('holordfinr'), {'A': SA, 'B': SB, 'R': R18, 'D': HP0, 'X': 'U'})
    ha_, hc = ante_of(H)
    P0, PX = top_and(ha_)
    P1, P2 = top_and(P0)
    Q1, Q2, Q3 = top_and(P1)
    q1 = s([hol, s([s([a, b], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), geo], 'jca', Q2), nest], '3jca', P1)
    sub = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ w = %s ) -> w = %s )' % (A0, C0, C0))], 'fveq2d', '( ( %s /\\ w = %s ) -> ( F ` w ) = ( F ` %s ) )' % (A0, C0, C0))], 'neeq1d',
              '( ( %s /\\ w = %s ) -> ( ( F ` w ) =/= 0 <-> ( F ` %s ) =/= 0 ) )' % (A0, C0, C0))
    ex = s([fc0, s([cin, sub], 'rspcedv', '( ( F ` %s ) =/= 0 -> %s )' % (C0, P2))], 'mpd', P2)
    w.qed([s([s([q1, ex], 'jca', P0), um], 'jca', ha_), w.inst('holordfinr')], 'syl', S['zdord'])
    return run8(w)


def gen_zdfac():
    w = W('zdfac', 'Factorisation on the square of half-side ` 13 / 8 ` about ` 2 + i T ` with the canonical orders: ` F ( z ) = prod ( z - q ) ^ ( F holord q ) h ( z ) ` on the right half-plane, ` h ` holomorphic and zero-free on the square (Lean ` exists_LFunction_factorization ` for a generic ` F ` ; ~ holzfac , ~ holzord ).')
    A0 = HA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    hol = s([], 'simp1', HOLF('F', HP0)); tr = s([], 'simp2', 'T e. RR'); fc0 = s([], 'simp3', '( F ` %s ) =/= 0' % C0)
    c0, re0, im0 = c0_facts(w, A0, tr)
    cin, a, b, geo, nest = geo_data(w, A0, c0, re0, im0, R138, R18, R74)
    SA, SB = SQA(C0, R138), SQB(C0, R138)
    HF = tsub(stmt('holzfac'), {'A': SA, 'B': SB, 'R': R18, 'D': HP0})
    hfa, hfc = ante_of(HF)
    P1, P2 = top_and(hfa)
    Q1, Q2, Q3 = top_and(P1)
    q1 = s([hol, s([s([a, b], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), geo], 'jca', Q2), nest], '3jca', P1)
    sub = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ w = %s ) -> w = %s )' % (A0, C0, C0))], 'fveq2d', '( ( %s /\\ w = %s ) -> ( F ` w ) = ( F ` %s ) )' % (A0, C0, C0))], 'neeq1d',
              '( ( %s /\\ w = %s ) -> ( ( F ` w ) =/= 0 <-> ( F ` %s ) =/= 0 ) )' % (A0, C0, C0))
    ex = s([fc0, s([cin, sub], 'rspcedv', '( ( F ` %s ) =/= 0 -> %s )' % (C0, P2))], 'mpd', P2)
    hfa_s = s([q1, ex], 'jca', hfa)
    hz = s([hfa_s, w.inst('holzfac')], 'syl', hfc)
    zfin = s([hfa_s, w.inst('holzfi')], 'syl', '%s e. Fin' % Z13)
    INNER = hfc[len('E. o E. h '):]
    AG = '( %s /\\ %s )' % (A0, INNER)
    sg = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (AG, f))
    I1, I2, I3 = top_and(INNER)
    of = sg([], 'simpr1', I1) if False else sg([sg([], 'simpr', INNER), w.inst('simp1')], 'syl', I1)
    hh = sg([sg([], 'simpr', INNER), w.inst('simp2')], 'syl', I2)
    i3 = sg([sg([], 'simpr', INNER), w.inst('simp3')], 'syl', I3)
    FACz, NZ = top_and(I3)
    fac = sg([i3, w.inst('simpl')], 'syl', FACz); nz = sg([i3, w.inst('simpr')], 'syl', NZ)
    # the order identification ( o ` q ) = ( F holord q ) on Z13 (holzord: index k, variable v)
    SQ13 = SQ(C0, R138)
    z13s = sg([w.s([], 'ssrab2', '%s C_ %s' % (Z13, SQ13))], 'a1i', '%s C_ %s' % (Z13, SQ13))
    zd = sg([z13s, lift(w, sq_hp(w, A0, c0, re0, R138), AG)], 'sstrd', '%s C_ %s' % (Z13, HP0))
    BZ = lambda v, q: '( ( %s - %s ) ^ ( o ` %s ) )' % (v, q, q)
    PZ = lambda v, q: 'prod_ %s e. %s %s' % (q, Z13, BZ(v, q))
    BODY = lambda v, q: '( F ` %s ) = ( %s x. ( h ` %s ) )' % (v, PZ(v, q), v)
    e1 = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )'),
              w.s([w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z - q ) = ( v - q ) )')], 'oveq1d', '( z = v -> %s = %s )' % (BZ('z', 'q'), BZ('v', 'q')))], 'prodeq2sdv',
                        '( z = v -> %s = %s )' % (PZ('z', 'q'), PZ('v', 'q'))), w.s([], 'fveq2', '( z = v -> ( h ` z ) = ( h ` v ) )')], 'oveq12d',
                  '( z = v -> ( %s x. ( h ` z ) ) = ( %s x. ( h ` v ) ) )' % (PZ('z', 'q'), PZ('v', 'q')))], 'eqeq12d', '( z = v -> ( %s <-> %s ) )' % (BODY('z', 'q'), BODY('v', 'q')))
    c1 = w.s([e1], 'cbvralvw', '( A. z e. %s %s <-> A. v e. %s %s )' % (HP0, BODY('z', 'q'), HP0, BODY('v', 'q')))
    e2 = w.s([w.s([w.s([], 'oveq2', '( q = k -> ( v - q ) = ( v - k ) )'), w.s([], 'fveq2', '( q = k -> ( o ` q ) = ( o ` k ) )')], 'oveq12d', '( q = k -> %s = %s )' % (BZ('v', 'q'), BZ('v', 'k')))],
             'cbvprodv', '%s = %s' % (PZ('v', 'q'), PZ('v', 'k')))
    e3 = w.s([w.s([w.s([e2], 'oveq1i', '( %s x. ( h ` v ) ) = ( %s x. ( h ` v ) )' % (PZ('v', 'q'), PZ('v', 'k')))], 'eqeq2i', '( %s <-> %s )' % (BODY('v', 'q'), BODY('v', 'k')))],
             'ralbii', '( A. v e. %s %s <-> A. v e. %s %s )' % (HP0, BODY('v', 'q'), HP0, BODY('v', 'k')))
    facv = sg([sg([fac, c1], 'sylib', 'A. v e. %s %s' % (HP0, BODY('v', 'q'))), e3], 'sylib', 'A. v e. %s %s' % (HP0, BODY('v', 'k')))
    en = w.s([w.s([], 'fveq2', '( z = v -> ( h ` z ) = ( h ` v ) )')], 'neeq1d', '( z = v -> ( ( h ` z ) =/= 0 <-> ( h ` v ) =/= 0 ) )')
    nzv0 = sg([nz, w.s([en], 'cbvralvw', '( A. z e. %s ( h ` z ) =/= 0 <-> A. v e. %s ( h ` v ) =/= 0 )' % (SQ13, SQ13))], 'sylib', 'A. v e. %s ( h ` v ) =/= 0' % SQ13)
    nzv = sg([z13s, nzv0, w.inst('ssralv')], 'sylc', 'A. v e. %s ( h ` v ) =/= 0' % Z13)
    ZO = tsub(stmt('holzord'), {'D': HP0, 'Z': Z13, 'O': 'o', 'H': 'h', 'P': 'p'})
    zoa, zoc = ante_of(ZO)
    C1_, C2_, BP = top_and(zoa)
    D1_, D2_ = top_and(C1_)
    E1_, E2_ = top_and(C2_)
    AGq = '( %s /\\ p e. %s )' % (AG, Z13)
    L = lambda st: lift(w, st, AGq)
    b1 = w.s([L(lift(w, hol, AG)), w.s([L(lift(w, zfin, AG)), L(zd)], 'jca', '( %s -> %s )' % (AGq, D2_))], 'jca', '( %s -> %s )' % (AGq, C1_))
    b2 = w.s([w.s([L(of), L(hh)], 'jca', '( %s -> %s )' % (AGq, E1_)), w.s([L(facv), L(nzv)], 'jca', '( %s -> %s )' % (AGq, E2_))], 'jca', '( %s -> %s )' % (AGq, C2_))
    zo = w.s([w.s([b1, b2, w.s([], 'simpr', '( %s -> p e. %s )' % (AGq, Z13))], '3jca', '( %s -> %s )' % (AGq, zoa)), w.inst('holzord')], 'syl', '( %s -> %s )' % (AGq, zoc))
    zoal = sg([zo], 'ralrimiva', 'A. p e. %s %s' % (Z13, zoc))
    ZOAL = 'A. p e. %s %s' % (Z13, zoc)
    FACK = 'A. v e. %s %s' % (HP0, BODY('v', 'k'))
    PA = '( %s /\\ %s /\\ %s )' % (A0, ZOAL, FACK)
    PAz = '( %s /\\ z e. %s )' % (PA, HP0)
    sz = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (PAz, f))
    ev = w.wcongr(BODY('v', 'k'), {'v': 'z'}, 'v = z', {'v': w.s([], 'id', '( v = z -> v = z )')})[0]
    fzk = w.s([ev, sz([], 'simpl3' if False else 'simpl', PA) and lift(w, w.s([], 'simp3', '( %s -> %s )' % (PA, FACK)), PAz), sz([], 'simpr', 'z e. %s' % HP0)], 'rspcdva',
              '( %s -> %s )' % (PAz, BODY('z', 'k')))
    cq = w.s([w.s([w.s([], 'oveq2', '( k = q -> ( z - k ) = ( z - q ) )'), w.s([], 'fveq2', '( k = q -> ( o ` k ) = ( o ` q ) )')], 'oveq12d', '( k = q -> %s = %s )' % (BZ('z', 'k'), BZ('z', 'q')))],
             'cbvprodv', '%s = %s' % (PZ('z', 'k'), PZ('z', 'q')))
    PAzq = '( %s /\\ q e. %s )' % (PAz, Z13)
    zocq = '( o ` q ) = ( F holord q )'
    eqp = w.s([w.s([], 'fveq2', '( p = q -> ( o ` p ) = ( o ` q ) )'), w.s([], 'oveq2', '( p = q -> ( F holord p ) = ( F holord q ) )')], 'eqeq12d', '( p = q -> ( %s <-> %s ) )' % (zoc, zocq))
    zq = w.s([eqp, lift(w, w.s([], 'simp2', '( %s -> %s )' % (PA, ZOAL)), PAzq), w.s([], 'simpr', '( %s -> q e. %s )' % (PAzq, Z13))], 'rspcdva', '( %s -> %s )' % (PAzq, zocq))
    PH = 'prod_ q e. %s ( ( z - q ) ^ ( F holord q ) )' % Z13
    pe = w.s([w.s([zq], 'oveq2d', '( %s -> %s = ( ( z - q ) ^ ( F holord q ) ) )' % (PAzq, BZ('z', 'q')))], 'prodeq2dv', '( %s -> %s = %s )' % (PAz, PZ('z', 'q'), PH))
    pe2 = sz([sz([cq], 'a1i', '%s = %s' % (PZ('z', 'k'), PZ('z', 'q'))), pe], 'eqtrd', '%s = %s' % (PZ('z', 'k'), PH))
    fz2 = sz([fzk, sz([pe2], 'oveq1d', '( %s x. ( h ` z ) ) = ( %s x. ( h ` z ) )' % (PZ('z', 'k'), PH))], 'eqtrd', '( F ` z ) = ( %s x. ( h ` z ) )' % PH)
    fall0 = w.s([fz2], 'ralrimiva', '( %s -> A. z e. %s ( F ` z ) = ( %s x. ( h ` z ) ) )' % (PA, HP0, PH))
    toPA = sg([sg([], 'simpl', A0), zoal, facv], '3jca', PA)
    fall = sg([toPA, fall0], 'syl', 'A. z e. %s ( F ` z ) = ( %s x. ( h ` z ) )' % (HP0, PH))
    BODYH = '( %s /\\ A. z e. %s ( F ` z ) = ( %s x. ( h ` z ) ) /\\ A. z e. %s ( h ` z ) =/= 0 )' % (HOLF('h', HP0), HP0, PH, SQ13)
    bh = sg([hh, fall, nz], '3jca', BODYH)
    exh = sg([bh, w.inst('19.8a')], 'syl', 'E. h %s' % BODYH)
    BODYG = tsub(BODYH, {'h': 'g'})
    eqg = w.wcongr(BODYH, {'h': 'g'}, 'h = g', {'h': w.s([], 'id', '( h = g -> h = g )')})[0]
    cb = w.s([eqg], 'cbvexvw', '( E. h %s <-> E. g %s )' % (BODYH, BODYG))
    exg = sg([exh, cb], 'sylib', 'E. g %s' % BODYG)
    el = s([w.s([exg], 'ex', '( %s -> ( %s -> E. g %s ) )' % (A0, INNER, BODYG))], 'exlimdvv', '( %s -> E. g %s )' % (hfc, BODYG))
    fin = s([hz, el], 'mpd', 'E. g %s' % BODYG)
    w.qed([fin, w.s([cb], 'bicomi', '( E. g %s <-> E. h %s )' % (BODYG, BODYH))], 'sylib', S['zdfac'])
    return run8(w)


if __name__ == '__main__':
    gen_zdord()
    gen_zdfac()
