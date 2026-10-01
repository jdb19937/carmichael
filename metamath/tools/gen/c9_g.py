"""Sortie C9: lndgenlem (the assembly under holzlogdv's data) and lndgen (the
Landau expansion on squares, the headline)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
from cl import lift
from c8_o import numst
from c8_n import sqcc
from c9_e import sqfrd_at
from c9_f import in_sq, nz_at, fac_at, LG
from c9_freeze import S as FS
import lin
lin.FASTPATH = True

ZSS = ZSQ()
GA, GC = ante_of(FS['lndgen'])
HZ = tsub(stmt('holzlogdv'), {'A': A138, 'B': B138, 'R': R18})
HZA, HZC = ante_of(HZ)
INNER = HZC[len('E. o E. h '):]
INO = tsub(INNER, {'o': 'O', 'h': 'H'})
LEMA = '( %s /\\ ( %s e. Fin /\\ %s ) )' % (GA, ZSS, INO)
FS['lndgenlem'] = '( %s -> %s )' % (LEMA, GC)
SUMH = 'sum_ q e. %s ( F holord q )' % ZSS


def gen_lndgenlem():
    w = W('lndgenlem', 'Lemma for ~ lndgen : the Landau expansion on squares under the data of ~ holzlogdv .')
    A0 = LEMA
    ga = w.s([], 'simpl', '( %s -> %s )' % (A0, GA))
    X1 = '( %s /\\ ( C e. CC /\\ %s C_ D ) )' % (HOL, SQ74)
    X2 = '( %s /\\ ( ( F ` C ) =/= 0 /\\ ( W e. RR+ /\\ %s <_ W ) ) )' % (FBD, SUMH)
    X3 = '( S e. CC /\\ ( abs ` ( S - C ) ) <_ ( 3 / 2 ) /\\ ( F ` S ) =/= 0 )'
    assert GA == '( %s /\\ %s /\\ %s )' % (X1, X2, X3), GA
    x1 = w.s([ga, w.inst('simp1')], 'syl', '( %s -> %s )' % (A0, X1))
    x2 = w.s([ga, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, X2))
    x3 = w.s([ga, w.inst('simp3')], 'syl', '( %s -> %s )' % (A0, X3))
    hol = w.s([x1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    cs = w.s([x1, w.inst('simprl')], 'syl', '( %s -> C e. CC )' % A0)
    s74d = w.s([x1, w.inst('simprr')], 'syl', '( %s -> %s C_ D )' % (A0, SQ74))
    fbd = w.s([x2, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, FBD))
    fc0 = w.s([x2, w.inst('simprl')], 'syl', '( %s -> ( F ` C ) =/= 0 )' % A0)
    wrp = w.s([x2, w.inst('simprrl')], 'syl', '( %s -> W e. RR+ )' % A0)
    sw = w.s([x2, w.inst('simprrr')], 'syl', '( %s -> %s <_ W )' % (A0, SUMH))
    ss = w.s([x3, w.inst('simp1')], 'syl', '( %s -> S e. CC )' % A0)
    sle = w.s([x3, w.inst('simp2')], 'syl', '( %s -> ( abs ` ( S - C ) ) <_ ( 3 / 2 ) )' % A0)
    fs0 = w.s([x3, w.inst('simp3')], 'syl', '( %s -> ( F ` S ) =/= 0 )' % A0)
    zfin = w.s([], 'simprl', '( %s -> %s e. Fin )' % (A0, ZSS))
    ino = w.s([], 'simprr', '( %s -> %s )' % (A0, INO))
    I1, LDV = top_and(INO)
    assert INO == '( %s /\\ %s )' % (I1, LDV), INO[:200]
    i1 = w.s([ino, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, I1))
    ldv = w.s([ino, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, LDV))
    FACZ = 'A. z e. D ( F ` z ) = ( %s x. ( H ` z ) )' % PRZ(ZSS, 'z')
    NZ = 'A. z e. %s ( H ` z ) =/= 0' % SQ138
    assert I1 == '( O : %s --> NN /\\ %s /\\ ( %s /\\ %s ) )' % (ZSS, HOLG('H', 'D'), FACZ, NZ), I1
    of = w.s([i1, w.inst('simp1')], 'syl', '( %s -> O : %s --> NN )' % (A0, ZSS))
    holh = w.s([i1, w.inst('simp2')], 'syl', '( %s -> %s )' % (A0, HOLG('H', 'D')))
    fz3 = w.s([i1, w.inst('simp3')], 'syl', '( %s -> ( %s /\\ %s ) )' % (A0, FACZ, NZ))
    fac = w.s([fz3, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, FACZ))
    nz = w.s([fz3, w.inst('simpr')], 'syl', '( %s -> %s )' % (A0, NZ))
    zsq = w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZSS, SQ138))], 'a1i', '( %s -> %s C_ %s )' % (A0, ZSS, SQ138))
    # ZS C_ D
    Ap = '( %s /\\ p e. %s )' % (A0, ZSS)
    ps = w.s([lift(w, zsq, Ap), w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, ZSS))], 'sseldd', '( %s -> p e. %s )' % (Ap, SQ138))
    sp, _ = sqfrd_at(w, Ap, lift(w, cs, Ap), 'p', ps)
    ip = w.s([sp, w.inst('simpl')], 'syl', '( %s -> %s )' % (Ap, INTG(A74, B74, 'p')))
    r74p = numst(w, Ap, R74, 'RR')
    a74c, b74c = sqcc(w, Ap, lift(w, cs, Ap), r74p, r=R74)
    p74 = w.s([w.s([a74c, b74c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Ap, A74, B74)), ip, w.inst('crectinp')], 'syl2anc', '( %s -> p e. %s )' % (Ap, SQ74))
    pd = w.s([lift(w, s74d, Ap), p74], 'sseldd', '( %s -> p e. D )' % Ap)
    zd = w.s([w.s([pd], 'ex', '( %s -> ( p e. %s -> p e. D ) )' % (A0, ZSS))], 'ssrdv', '( %s -> %s C_ D )' % (A0, ZSS))
    # holzord's factorisation over k, v
    PQ = PRZ(ZSS, 'z')
    PKz = 'prod_ k e. %s ( ( z - k ) ^ ( O ` k ) )' % ZSS
    PKv = 'prod_ k e. %s ( ( v - k ) ^ ( O ` k ) )' % ZSS
    eqp = w.s([w.s([w.s([], 'oveq2', '( q = k -> ( z - q ) = ( z - k ) )'), w.s([], 'fveq2', '( q = k -> ( O ` q ) = ( O ` k ) )')], 'oveq12d',
                    '( q = k -> ( ( z - q ) ^ ( O ` q ) ) = ( ( z - k ) ^ ( O ` k ) ) )')], 'cbvprodv', '%s = %s' % (PQ, PKz))
    b1 = w.s([w.s([eqp], 'oveq1i', '( %s x. ( H ` z ) ) = ( %s x. ( H ` z ) )' % (PQ, PKz))], 'eqeq2i',
             '( ( F ` z ) = ( %s x. ( H ` z ) ) <-> ( F ` z ) = ( %s x. ( H ` z ) ) )' % (PQ, PKz))
    FKZ = 'A. z e. D ( F ` z ) = ( %s x. ( H ` z ) )' % PKz
    FKV = 'A. v e. D ( F ` v ) = ( %s x. ( H ` v ) )' % PKv
    r1 = w.s([b1], 'ralbii', '( %s <-> %s )' % (FACZ, FKZ))
    subv = w.s([w.s([], 'fveq2', '( z = v -> ( F ` z ) = ( F ` v ) )'),
                w.s([w.s([w.s([w.s([], 'oveq1', '( z = v -> ( z - k ) = ( v - k ) )')], 'oveq1d', '( z = v -> ( ( z - k ) ^ ( O ` k ) ) = ( ( v - k ) ^ ( O ` k ) ) )')], 'prodeq2sdv',
                          '( z = v -> %s = %s )' % (PKz, PKv)), w.s([], 'fveq2', '( z = v -> ( H ` z ) = ( H ` v ) )')], 'oveq12d',
                    '( z = v -> ( %s x. ( H ` z ) ) = ( %s x. ( H ` v ) ) )' % (PKz, PKv))], 'eqeq12d',
               '( z = v -> ( ( F ` z ) = ( %s x. ( H ` z ) ) <-> ( F ` v ) = ( %s x. ( H ` v ) ) ) )' % (PKz, PKv))
    r2 = w.s([subv], 'cbvralvw', '( %s <-> %s )' % (FKZ, FKV))
    fkv = w.s([fac, w.s([r1, r2], 'bitri', '( %s <-> %s )' % (FACZ, FKV))], 'sylib', '( %s -> %s )' % (A0, FKV))
    NZZ = 'A. z e. %s ( H ` z ) =/= 0' % ZSS
    NZV = 'A. v e. %s ( H ` v ) =/= 0' % ZSS
    nzz = w.s([nz, w.s([zsq, w.inst('ssralv')], 'syl', '( %s -> ( %s -> %s ) )' % (A0, NZ, NZZ))], 'mpd', '( %s -> %s )' % (A0, NZZ))
    nzv = w.s([nzz, w.s([w.s([w.s([], 'fveq2', '( z = v -> ( H ` z ) = ( H ` v ) )')], 'neeq1d', '( z = v -> ( ( H ` z ) =/= 0 <-> ( H ` v ) =/= 0 ) )')], 'cbvralvw', '( %s <-> %s )' % (NZZ, NZV))],
              'sylib', '( %s -> %s )' % (A0, NZV))
    HO = tsub(stmt('holzord'), {'Z': ZSS, 'P': 'p'})
    hoa, hoc = ante_of(HO)
    Q1 = '( %s /\\ ( %s e. Fin /\\ %s C_ D ) )' % (HOL, ZSS, ZSS)
    Q2 = '( ( O : %s --> NN /\\ %s ) /\\ ( %s /\\ %s ) )' % (ZSS, HOLG('H', 'D'), FKV, NZV)
    assert hoa == '( %s /\\ %s /\\ p e. %s )' % (Q1, Q2, ZSS), hoa
    L = lambda st: lift(w, st, Ap)
    hop = w.s([w.s([L(w.s([hol, w.s([zfin, zd], 'jca', '( %s -> ( %s e. Fin /\\ %s C_ D ) )' % (A0, ZSS, ZSS))], 'jca', '( %s -> %s )' % (A0, Q1))),
                    L(w.s([w.s([of, holh], 'jca', '( %s -> ( O : %s --> NN /\\ %s ) )' % (A0, ZSS, HOLG('H', 'D'))), w.s([fkv, nzv], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, FKV, NZV))], 'jca', '( %s -> %s )' % (A0, Q2))),
                    w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, ZSS))], '3jca', '( %s -> %s )' % (Ap, hoa)), w.inst('holzord')], 'syl', '( %s -> %s )' % (Ap, hoc))
    # the two sums
    def sum_conv(bodyp, bodyq, eqstep):
        ALP = 'A. p e. %s %s' % (ZSS, bodyp)
        ALQ = 'A. q e. %s %s' % (ZSS, bodyq)
        allp = w.s([eqstep], 'ralrimiva', '( %s -> %s )' % (A0, ALP))
        return ALQ, allp
    B1p, B1q = '( O ` p ) = ( F holord p )', '( O ` q ) = ( F holord q )'
    s1p = w.s([hop], 'ralrimiva', '( %s -> A. p e. %s %s )' % (A0, ZSS, B1p))
    c1 = w.s([w.s([w.s([], 'fveq2', '( p = q -> ( O ` p ) = ( O ` q ) )'), w.s([], 'oveq2', '( p = q -> ( F holord p ) = ( F holord q ) )')], 'eqeq12d', '( p = q -> ( %s <-> %s ) )' % (B1p, B1q))],
             'cbvralvw', '( A. p e. %s %s <-> A. q e. %s %s )' % (ZSS, B1p, ZSS, B1q))
    s1q = w.s([s1p, c1], 'sylib', '( %s -> A. q e. %s %s )' % (A0, ZSS, B1q))
    SO = 'sum_ q e. %s ( O ` q )' % ZSS
    se1 = w.s([s1q, w.inst('sumeq2')], 'syl', '( %s -> %s = %s )' % (A0, SO, SUMH))
    sow = w.s([se1, sw], 'eqbrtrd', '( %s -> %s <_ W )' % (A0, SO))
    B2p = '( ( O ` p ) / ( S - p ) ) = ( ( F holord p ) / ( S - p ) )'
    B2q = '( ( O ` q ) / ( S - q ) ) = ( ( F holord q ) / ( S - q ) )'
    s2p = w.s([w.s([hop], 'oveq1d', '( %s -> %s )' % (Ap, B2p))], 'ralrimiva', '( %s -> A. p e. %s %s )' % (A0, ZSS, B2p))
    c2 = w.s([w.s([w.s([w.s([], 'fveq2', '( p = q -> ( O ` p ) = ( O ` q ) )'), w.s([], 'oveq2', '( p = q -> ( S - p ) = ( S - q ) )')], 'oveq12d', '( p = q -> ( ( O ` p ) / ( S - p ) ) = ( ( O ` q ) / ( S - q ) ) )'),
                    w.s([w.s([], 'oveq2', '( p = q -> ( F holord p ) = ( F holord q ) )'), w.s([], 'oveq2', '( p = q -> ( S - p ) = ( S - q ) )')], 'oveq12d', '( p = q -> ( ( F holord p ) / ( S - p ) ) = ( ( F holord q ) / ( S - q ) ) )')],
                   'eqeq12d', '( p = q -> ( %s <-> %s ) )' % (B2p, B2q))], 'cbvralvw', '( A. p e. %s %s <-> A. q e. %s %s )' % (ZSS, B2p, ZSS, B2q))
    s2q = w.s([s2p, c2], 'sylib', '( %s -> A. q e. %s %s )' % (A0, ZSS, B2q))
    SIGO = 'sum_ q e. %s ( ( O ` q ) / ( S - q ) )' % ZSS
    SIGH = 'sum_ q e. %s ( ( F holord q ) / ( S - q ) )' % ZSS
    se2 = w.s([s2q, w.inst('sumeq2')], 'syl', '( %s -> %s = %s )' % (A0, SIGO, SIGH))
    # DATA with Z := ZS, O, H
    D1 = '( %s /\\ ( C e. CC /\\ %s C_ D ) )' % (HOL, SQ74)
    D2 = '( ( %s e. Fin /\\ %s C_ %s ) /\\ ( O : %s --> NN /\\ %s ) )' % (ZSS, ZSS, SQ138, ZSS, HOLG('H', 'D'))
    DT = tsub(DATA, {'Z': ZSS})
    dt = w.s([x1, w.s([w.s([zfin, zsq], 'jca', '( %s -> ( %s e. Fin /\\ %s C_ %s ) )' % (A0, ZSS, ZSS, SQ138)), w.s([of, holh], 'jca', '( %s -> ( O : %s --> NN /\\ %s ) )' % (A0, ZSS, HOLG('H', 'D')))],
                         'jca', '( %s -> %s )' % (A0, D2)), fz3], '3jca', '( %s -> %s )' % (A0, DT))
    wr = w.s([wrp], 'rpred', '( %s -> W e. RR )' % A0)
    HR = tsub(stmt('lndhre'), {'Z': ZSS})
    hra, hrc = ante_of(HR)
    hre = w.s([w.s([w.s([dt, fbd], 'jca', '( %s -> ( %s /\\ %s ) )' % (A0, DT, FBD)), w.s([fc0, w.s([wr, sow], 'jca', '( %s -> ( W e. RR /\\ %s <_ W ) )' % (A0, SO))], 'jca',
                   '( %s -> ( ( F ` C ) =/= 0 /\\ ( W e. RR /\\ %s <_ W ) ) )' % (A0, SO))], 'jca', '( %s -> %s )' % (A0, hra)), w.inst('lndhre')], 'syl', '( %s -> %s )' % (A0, hrc))
    # LOGM e. RR+
    c74 = in_sq(w, A0, cs, R74)
    cd = w.s([s74d, c74], 'sseldd', '( %s -> C e. D )' % A0)
    ff = w.s([w.s([hol, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> F : D --> CC )' % A0)
    fcc = w.s([ff, cd], 'ffvelcdmd', '( %s -> ( F ` C ) e. CC )' % A0)
    afc = w.s([fcc, fc0], 'absrpcld', '( %s -> ( abs ` ( F ` C ) ) e. RR+ )' % A0)
    fb = w.s([fbd, w.inst('simpr')], 'syl', '( %s -> A. x e. %s ( abs ` ( F ` x ) ) <_ B )' % (A0, SQ74))
    subx = w.s([w.s([w.s([], 'fveq2', '( x = C -> ( F ` x ) = ( F ` C ) )')], 'fveq2d', '( x = C -> ( abs ` ( F ` x ) ) = ( abs ` ( F ` C ) ) )')], 'breq1d',
               '( x = C -> ( ( abs ` ( F ` x ) ) <_ B <-> ( abs ` ( F ` C ) ) <_ B ) )')
    fcb = w.s([subx, fb, c74], 'rspcdva', '( %s -> ( abs ` ( F ` C ) ) <_ B )' % A0)
    bst = w.s([fbd, w.inst('simpl')], 'syl', '( %s -> B e. RR )' % A0)
    bp = w.s([bst, w.s([w.s([afc], 'rpgt0d', '( %s -> 0 < ( abs ` ( F ` C ) ) )' % A0), fcb], 'ltletrd', '( %s -> 0 < B )' % A0)], 'elrpd', '( %s -> B e. RR+ )' % A0)
    LFC, LB = LG('( abs ` ( F ` C ) )'), LG('B')
    llb = w.s([fcb, w.s([afc, bp], 'logled', '( %s -> ( ( abs ` ( F ` C ) ) <_ B <-> %s <_ %s ) )' % (A0, LFC, LB))], 'mpbid', '( %s -> %s <_ %s )' % (A0, LFC, LB))
    LBF = LG('( B / ( abs ` ( F ` C ) ) )')
    lbf = w.s([bp, afc], 'relogdivd', '( %s -> %s = ( %s - %s ) )' % (A0, LBF, LB, LFC))
    L26 = LG('; 2 6')
    r26 = numst(w, A0, '; 2 6', 'RR+')
    l26r = w.s([r26], 'relogcld', '( %s -> %s e. RR )' % (A0, L26))
    l26g = w.s([lin8(w, A0, [], '1 < ; 2 6', {}), w.s([r26, w.inst('loggt0b')], 'syl', '( %s -> ( 0 < %s <-> 1 < ; 2 6 ) )' % (A0, L26))], 'mpbird', '( %s -> 0 < %s )' % (A0, L26))
    l26p = w.s([l26r, l26g], 'elrpd', '( %s -> %s e. RR+ )' % (A0, L26))
    W26 = '( W x. %s )' % L26
    w26 = w.s([wrp, l26p], 'rpmulcld', '( %s -> %s e. RR+ )' % (A0, W26))
    lv = {LFC: w.s([afc], 'relogcld', '( %s -> %s e. RR )' % (A0, LFC)), LB: w.s([bp], 'relogcld', '( %s -> %s e. RR )' % (A0, LB)),
          LBF: w.s([w.s([bp, afc], 'rpdivcld', '( %s -> ( B / ( abs ` ( F ` C ) ) ) e. RR+ )' % A0)], 'relogcld', '( %s -> %s e. RR )' % (A0, LBF)),
          W26: w.s([w26], 'rpred', '( %s -> %s e. RR )' % (A0, W26))}
    mpos = lin8(w, A0, [llb, lbf, w.s([w26], 'rpgt0d', '( %s -> 0 < %s )' % (A0, W26))], '0 < %s' % LOGM, lv)
    mrp = w.s([w.s([lv[LBF], lv[W26]], 'readdcld', '( %s -> %s e. RR )' % (A0, LOGM)), mpos], 'elrpd', '( %s -> %s e. RR+ )' % (A0, LOGM))
    # logdvbnd7 on H
    LB7 = tsub(stmt('logdvbnd7'), {'F': 'H', 'M': LOGM})
    la, lc = ante_of(LB7)
    NZY = 'A. y e. %s ( H ` y ) =/= 0' % SQ138
    nzy = w.s([nz, w.s([w.s([w.s([], 'fveq2', '( z = y -> ( H ` z ) = ( H ` y ) )')], 'neeq1d', '( z = y -> ( ( H ` z ) =/= 0 <-> ( H ` y ) =/= 0 ) )')], 'cbvralvw', '( %s <-> %s )' % (NZ, NZY))],
              'sylib', '( %s -> %s )' % (A0, NZY))
    E1 = '( %s /\\ ( C e. CC /\\ %s C_ D ) )' % (HOLG('H', 'D'), SQ74)
    E2 = '( %s /\\ ( %s e. RR+ /\\ %s ) )' % (NZY, LOGM, hrc)
    E3 = '( S e. CC /\\ ( abs ` ( S - C ) ) <_ ( 3 / 2 ) )'
    assert la == '( %s /\\ %s /\\ %s )' % (E1, E2, E3), la
    lb7 = w.s([w.s([w.s([holh, w.s([cs, s74d], 'jca', '( %s -> ( C e. CC /\\ %s C_ D ) )' % (A0, SQ74))], 'jca', '( %s -> %s )' % (A0, E1)),
                    w.s([nzy, w.s([mrp, hre], 'jca', '( %s -> ( %s e. RR+ /\\ %s ) )' % (A0, LOGM, hrc))], 'jca', '( %s -> %s )' % (A0, E2)),
                    w.s([ss, sle], 'jca', '( %s -> %s )' % (A0, E3))], '3jca', '( %s -> %s )' % (A0, la)), w.inst('logdvbnd7')], 'syl', '( %s -> %s )' % (A0, lc))
    HH = '( ( ( CC _D H ) ` S ) / ( H ` S ) )'
    assert lc == '( abs ` %s ) <_ ( %s x. %s )' % (HH, K6N, LOGM), lc
    # S in K \ ZS
    r138 = numst(w, A0, R138, 'RR')
    asc = w.s([w.s([ss, cs], 'subcld', '( %s -> ( S - C ) e. CC )' % A0)], 'abscld', '( %s -> ( abs ` ( S - C ) ) e. RR )' % A0)
    slt = lin8(w, A0, [sle], '( abs ` ( S - C ) ) < %s' % R138, {'( abs ` ( S - C ) )': asc})
    si = w.s([w.s([w.s([cs, r138], 'jca', '( %s -> ( C e. CC /\\ %s e. RR ) )' % (A0, R138)), w.s([ss, slt], 'jca', '( %s -> ( S e. CC /\\ ( abs ` ( S - C ) ) < %s ) )' % (A0, R138))], 'jca',
                  '( %s -> ( ( C e. CC /\\ %s e. RR ) /\\ ( S e. CC /\\ ( abs ` ( S - C ) ) < %s ) ) )' % (A0, R138, R138)), w.inst('sqint')], 'syl', '( %s -> %s )' % (A0, INTG(A138, B138, 'S')))
    a138c, b138c = sqcc(w, A0, cs, r138, r=R138)
    sk = w.s([w.s([a138c, b138c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A138, B138)), si, w.inst('crectinp')], 'syl2anc', '( %s -> S e. %s )' % (A0, SQ138))
    er = w.s([w.s([w.s([], 'fveq2', '( r = S -> ( F ` r ) = ( F ` S ) )')], 'eqeq1d', '( r = S -> ( ( F ` r ) = 0 <-> ( F ` S ) = 0 ) )')], 'elrab',
             '( S e. %s <-> ( S e. %s /\\ ( F ` S ) = 0 ) )' % (ZSS, SQ138))
    nzs = w.s([w.s([w.s([fs0], 'neneqd', '( %s -> -. ( F ` S ) = 0 )' % A0)], 'intnand', '( %s -> -. ( S e. %s /\\ ( F ` S ) = 0 ) )' % (A0, SQ138)), w.s([er], 'a1i', '( %s -> ( S e. %s <-> ( S e. %s /\\ ( F ` S ) = 0 ) ) )' % (A0, ZSS, SQ138))],
              'mtbird', '( %s -> -. S e. %s )' % (A0, ZSS))
    skz = w.s([sk, nzs], 'eldifd', '( %s -> S e. ( %s \\ %s ) )' % (A0, SQ138, ZSS))
    SIGz = 'sum_ q e. %s ( ( O ` q ) / ( z - q ) )' % ZSS
    BZ = '( ( ( CC _D F ) ` z ) / ( F ` z ) ) = ( %s + ( ( ( CC _D H ) ` z ) / ( H ` z ) ) )' % SIGz
    FF = '( ( ( CC _D F ) ` S ) / ( F ` S ) )'
    BS = '%s = ( %s + %s )' % (FF, SIGO, HH)
    assert LDV == 'A. z e. ( %s \\ %s ) %s' % (SQ138, ZSS, BZ), LDV
    sf = w.s([w.s([], 'fveq2', '( z = S -> ( ( CC _D F ) ` z ) = ( ( CC _D F ) ` S ) )'), w.s([], 'fveq2', '( z = S -> ( F ` z ) = ( F ` S ) )')], 'oveq12d',
             '( z = S -> ( ( ( CC _D F ) ` z ) / ( F ` z ) ) = %s )' % FF)
    sg = w.s([w.s([w.s([], 'oveq1', '( z = S -> ( z - q ) = ( S - q ) )')], 'oveq2d', '( z = S -> ( ( O ` q ) / ( z - q ) ) = ( ( O ` q ) / ( S - q ) ) )')], 'sumeq2sdv',
             '( z = S -> %s = %s )' % (SIGz, SIGO))
    sh = w.s([w.s([], 'fveq2', '( z = S -> ( ( CC _D H ) ` z ) = ( ( CC _D H ) ` S ) )'), w.s([], 'fveq2', '( z = S -> ( H ` z ) = ( H ` S ) )')], 'oveq12d',
             '( z = S -> ( ( ( CC _D H ) ` z ) / ( H ` z ) ) = %s )' % HH)
    sgh = w.s([sg, sh], 'oveq12d', '( z = S -> ( %s + ( ( ( CC _D H ) ` z ) / ( H ` z ) ) ) = ( %s + %s ) )' % (SIGz, SIGO, HH))
    subs = w.s([sf, sgh], 'eqeq12d', '( z = S -> ( %s <-> %s ) )' % (BZ, BS))
    bs = w.s([subs, ldv, skz], 'rspcdva', '( %s -> %s )' % (A0, BS))
    # closures
    zcc = w.s([zsq, w.s([w.s([a138c, b138c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A138, B138)), w.inst('crectss')], 'syl', '( %s -> %s C_ CC )' % (A0, SQ138))], 'sstrd', '( %s -> %s C_ CC )' % (A0, ZSS))
    scz = w.s([ss, nzs], 'eldifd', '( %s -> S e. ( CC \\ %s ) )' % (A0, ZSS))
    FL = tsub(stmt('fprodlcl'), {'S': ZSS, 'Z': 'S'})
    fla, flc = ante_of(FL)
    fl = w.s([w.s([w.s([zfin, zcc, of], '3jca', '( %s -> ( %s e. Fin /\\ %s C_ CC /\\ O : %s --> NN ) )' % (A0, ZSS, ZSS, ZSS)), scz], 'jca', '( %s -> %s )' % (A0, fla)), w.inst('fprodlcl')], 'syl', '( %s -> %s )' % (A0, flc))
    sigc = w.s([fl], 'simp3d', '( %s -> %s e. CC )' % (A0, SIGO))
    ab74 = sqcc(w, A0, cs, numst(w, A0, R74, 'RR'), r=R74)
    sfr, _ = sqfrd_at(w, A0, cs, 'S', sk)
    s74 = w.s([w.s([ab74[0], ab74[1]], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A74, B74)), w.s([sfr, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, INTG(A74, B74, 'S'))), w.inst('crectinp')],
              'syl2anc', '( %s -> S e. %s )' % (A0, SQ74))
    sdd = w.s([s74d, s74], 'sseldd', '( %s -> S e. D )' % A0)
    hs = w.s([w.s([w.s([holh, w.inst('simpl')], 'syl', '( %s -> H e. ( D -cn-> CC ) )' % A0), w.inst('cncff')], 'syl', '( %s -> H : D --> CC )' % A0), sdd], 'ffvelcdmd', '( %s -> ( H ` S ) e. CC )' % A0)
    hds = w.s([w.s([holh, w.inst('holf')], 'syl', '( %s -> ( CC _D H ) : D --> CC )' % A0), sdd], 'ffvelcdmd', '( %s -> ( ( CC _D H ) ` S ) e. CC )' % A0)
    hs0 = nz_at(w, A0, nz, 'S', sk)
    hhc = w.s([hds, hs, hs0], 'divcld', '( %s -> %s e. CC )' % (A0, HH))
    # the difference
    d1 = w.s([bs, w.s([se2], 'eqcomd', '( %s -> %s = %s )' % (A0, SIGH, SIGO))], 'oveq12d', '( %s -> ( %s - %s ) = ( ( %s + %s ) - %s ) )' % (A0, FF, SIGH, SIGO, HH, SIGO))
    d2 = w.s([d1, w.s([sigc, hhc], 'pncan2d', '( %s -> ( ( %s + %s ) - %s ) = %s )' % (A0, SIGO, HH, SIGO, HH))], 'eqtrd', '( %s -> ( %s - %s ) = %s )' % (A0, FF, SIGH, HH))
    d3 = w.s([d2], 'fveq2d', '( %s -> ( abs ` ( %s - %s ) ) = ( abs ` %s ) )' % (A0, FF, SIGH, HH))
    goal = FS['lndgenlem']
    w.qed([d3, lb7], 'eqbrtrd', goal)
    assert goal == '( %s -> ( abs ` ( %s - %s ) ) <_ ( %s x. %s ) )' % (A0, FF, SIGH, K6N, LOGM)
    return run8(w)


def gen_lndgen():
    w = W('lndgen', 'The Landau expansion on squares (Lean ` norm_logDeriv_sub_sum_diskZeros_le ` , ` norm_logDeriv_sub_sum_zeroDiskFinset_le ` ): for ` F ` holomorphic on an open set containing the square of half-side ` 7 / 4 ` about ` C ` , bounded by ` B ` there, with ` F ( C ) =/= 0 ` and multiplicity mass at most ` W ` on the square of half-side ` 13 / 8 ` , the logarithmic derivative at a point ` S ` within ` 3 / 2 ` of ` C ` differs from ` sum ( F holord q ) / ( S - q ) ` over the zeros ` q ` of that square by at most ` 6272 ( log ( B / abs F ( C ) ) + W log 26 ) ` ( ~ holzlogdv , ~ lndhre , ~ logdvbnd7 ).')
    A0 = GA
    X1, X2, X3 = top_and(GA)
    x1 = w.s([], 'simp1', '( %s -> %s )' % (A0, X1)); x2 = w.s([], 'simp2', '( %s -> %s )' % (A0, X2))
    hol = w.s([x1, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, HOL))
    cs = w.s([x1, w.inst('simprl')], 'syl', '( %s -> C e. CC )' % A0)
    s74d = w.s([x1, w.inst('simprr')], 'syl', '( %s -> %s C_ D )' % (A0, SQ74))
    fc0 = w.s([x2, w.inst('simprl')], 'syl', '( %s -> ( F ` C ) =/= 0 )' % A0)
    r138 = numst(w, A0, R138, 'RR')
    ac, bc = sqcc(w, A0, cs, r138, r=R138)
    from c8_n import sqparts, sqre_at, reim_leaves
    pa = sqparts(w, A0, sqre_at(w, A0, cs, r138, r=R138), r=R138)
    lv = reim_leaves(w, A0, {A138: ac, B138: bc, 'C': cs})
    geo = w.s([lin8(w, A0, [pa[0], pa[1]], '( Re ` %s ) <_ ( Re ` %s )' % (A138, B138), lv), lin8(w, A0, [pa[2], pa[3]], '( Im ` %s ) <_ ( Im ` %s )' % (A138, B138), lv)], 'jca',
              '( %s -> %s )' % (A0, GEOG(A138, B138)))
    W18 = '( %s + ( _i x. %s ) )' % (R18, R18)
    X = '( %s + %s )' % (R138, R18)
    nst = w.s([w.s([cs, w.s([numst(w, A0, R138, 'CC'), numst(w, A0, R18, 'CC')], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, R138, R18))], 'jca',
                   '( %s -> ( C e. CC /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A0, R138, R18)), w.inst('sqnest')], 'syl',
              '( %s -> ( ( %s - %s ) = %s /\\ ( %s + %s ) = %s ) )' % (A0, A138, W18, SQA('C', X), B138, W18, SQB('C', X)))
    x74 = lin.lineq(w, A0, X, R74, closure=lin.Closure(w, A0, {})) if hasattr(lin, 'Closure') else None
    if x74 is None:
        import cl as _cl
        x74 = lin.lineq(w, A0, X, R74, closure=_cl.Closure(w, A0, {}))
    i74 = w.s([x74], 'oveq2d', '( %s -> ( _i x. %s ) = ( _i x. %s ) )' % (A0, X, R74))
    w74 = w.s([x74, i74], 'oveq12d', '( %s -> ( %s + ( _i x. %s ) ) = ( %s + ( _i x. %s ) ) )' % (A0, X, X, R74, R74))
    ea = w.s([w.s([nst, w.inst('simpl')], 'syl', '( %s -> ( %s - %s ) = %s )' % (A0, A138, W18, SQA('C', X))), w.s([w74], 'oveq2d', '( %s -> %s = %s )' % (A0, SQA('C', X), A74))],
             'eqtrd', '( %s -> ( %s - %s ) = %s )' % (A0, A138, W18, A74))
    eb = w.s([w.s([nst, w.inst('simpr')], 'syl', '( %s -> ( %s + %s ) = %s )' % (A0, B138, W18, SQB('C', X))), w.s([w74], 'oveq2d', '( %s -> %s = %s )' % (A0, SQB('C', X), B74))],
             'eqtrd', '( %s -> ( %s + %s ) = %s )' % (A0, B138, W18, B74))
    NR = '( ( %s - %s ) crect ( %s + %s ) )' % (A138, W18, B138, W18)
    nd = w.s([w.s([ea, eb], 'oveq12d', '( %s -> %s = %s )' % (A0, NR, SQ74)), s74d], 'eqsstrd', '( %s -> %s C_ D )' % (A0, NR))
    nest = w.s([numst(w, A0, R18, 'RR+'), nd], 'jca', '( %s -> ( %s e. RR+ /\\ %s C_ D ) )' % (A0, R18, NR))
    P1, P2 = top_and(HZA)
    Q1, Q2, Q3 = top_and(P1)
    q1 = w.s([hol, w.s([w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A0, A138, B138)), geo], 'jca', '( %s -> %s )' % (A0, Q2)), nest], '3jca', '( %s -> %s )' % (A0, P1))
    c138 = in_sq(w, A0, cs, R138)
    sub = w.s([w.s([w.s([], 'simpr', '( ( %s /\\ w = C ) -> w = C )' % A0)], 'fveq2d', '( ( %s /\\ w = C ) -> ( F ` w ) = ( F ` C ) )' % A0)], 'neeq1d',
              '( ( %s /\\ w = C ) -> ( ( F ` w ) =/= 0 <-> ( F ` C ) =/= 0 ) )' % A0)
    ex = w.s([fc0, w.s([c138, sub], 'rspcedv', '( %s -> ( ( F ` C ) =/= 0 -> %s ) )' % (A0, P2))], 'mpd', '( %s -> %s )' % (A0, P2))
    hza = w.s([q1, ex], 'jca', '( %s -> %s )' % (A0, HZA))
    hz = w.s([hza, w.inst('holzlogdv')], 'syl', '( %s -> %s )' % (A0, HZC))
    zfin = w.s([hza, w.inst('holzfi')], 'syl', '( %s -> %s e. Fin )' % (A0, ZSS))
    LM = tsub(stmt('lndgenlem'), {'O': 'o', 'H': 'h'})
    la, lc = ante_of(LM)
    AG = '( %s /\\ %s )' % (A0, INNER)
    lm = w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (AG, A0)), w.s([lift(w, zfin, AG), w.s([], 'simpr', '( %s -> %s )' % (AG, INNER))], 'jca', '( %s -> ( %s e. Fin /\\ %s ) )' % (AG, ZSS, INNER))],
                  'jca', '( %s -> %s )' % (AG, la)), w.inst('lndgenlem')], 'syl', '( %s -> %s )' % (AG, lc))
    el = w.s([w.s([lm], 'ex', '( %s -> ( %s -> %s ) )' % (A0, INNER, GC))], 'exlimdvv', '( %s -> ( %s -> %s ) )' % (A0, HZC, GC))
    goal = FS['lndgen']
    assert goal == '( %s -> %s )' % (A0, GC)
    w.qed([hz, el], 'mpd', goal)
    return run8(w)


if __name__ == '__main__':
    gen_lndgenlem()
    gen_lndgen()
