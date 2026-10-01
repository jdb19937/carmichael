"""Sortie LD1, section 4 part 2: the Taylor split and the remainder bounds
(ld1blktay ld1blkabs ld1tremabs ld1rtabs ld1twoj ld1fifth ld1remn ld1rsabs).
Run: MM_DB=sorties/ld1.mm MM_ENGINE=mmatch python3 tools/gen/ld1_e.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ld1lib import *
from ld1_d import setupx, hab, basefacts, liftcl, termcl, coeffcl, cond_of, L, L2, D2
from mvlib import _lhs_rhs
import lin as _L
_L.MAXPOW = 8

only = sys.argv[1:]
want = lambda l: not only or l in only
KJ = '( 0 ... %s )' % JPAR
IM = '( Im ` S )'


def fin(w):
    qedlast(w)
    return go(w)


def ck_of(w, Ak, c, base):
    """closure under Ak = ( .. /\\ k e. ( 0 ... J ) ) with k, k! leaves"""
    ck = liftcl(w, None, Ak, base)
    kn = ap(w, Ak, 'elfznn0', [w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, KJ))], 'k e. NN0')
    ck.leaf('k', 'NN0', kn); ck.leaf('( ! ` k )', 'NN', dst(w, Ak, [kn], 'faccld', '( ! ` k ) e. NN'))
    return ck


def ld1blktay():
    w = W('ld1blktay', 'Lean ` blockSum_eq_taylor ` (Lemma 2.7, the Taylor split of a block): ` S_j = N_j ^ -u delta ( sum_ ( k <_ J ) ( delta ^ k / k ! ) T_jk + R_j ) ` (~ fsumcom , ~ fsummulc2 , ~ fsumadd , ~ ld1rpowtay , ~ ld1cpow ).')
    A = ante('ld1blktay'); P, c, F = setupx(w, A)
    tr, jn = P['T e. RR'], P['J e. NN0']
    h0, rp3 = hab(w, A, F)
    c.leaf('T', 'RR', tr); c.leaf('J', 'NN0', jn); c.leaf('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC'))
    NBJ = NB('J'); nbc = '( %s ^c -u %s )' % (NBJ, DELTA)
    c.leaf(nbc, 'CC', c.mem(nbc, 'CC'))
    base = basefacts(F) + [('T', 'RR', tr), ('J', 'NN0', jn), ('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC')), (nbc, 'CC', c.mem(nbc, 'CC')), ('( Re ` S )', 'RR', F['re']), (IM, 'RR', dst(w, A, [F['sc']], 'imcld', '%s e. RR' % IM))]
    CK = lambda k: '( ( %s ^ %s ) / ( ! ` %s ) )' % (DELTA, k, k)
    tk = lambda k, n: TSUMMAND('J', k, n, IM, 'T')
    R = FZN
    # step A: sum_k c_k TAYSUM(k) = sum_n sum_k c_k t(k,n)
    Ak = '( %s /\\ k e. %s )' % (A, KJ)
    ck = ck_of(w, Ak, c, base)
    Akn = '( %s /\\ n e. %s )' % (Ak, R)
    ckn = liftcl(w, None, Akn, base); ckn.leaf('k', 'NN0', lift(w, ck.mem('k', 'NN0'), Akn)); ckn.leaf('( ! ` k )', 'NN', lift(w, ck.mem('( ! ` k )', 'NN'), Akn))
    termcl(w, Akn, ckn, 'n', ap(w, Akn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Akn, R))], 'n e. NN'), F, rp3); coeffcl(w, Akn, ckn, 'n', 'k')
    m1 = dst(w, Ak, [a1(w, Ak, 'fzfid', '%s e. Fin' % R) if False else dst(w, Ak, [], 'fzfid', '%s e. Fin' % R), ck.mem(CK('k'), 'CC'), ckn.mem(tk('k', 'n'), 'CC')], 'fsummulc2',
             '( %s x. %s ) = sum_ n e. %s ( %s x. %s )' % (CK('k'), TAYSUM('J', 'k', IM), R, CK('k'), tk('k', 'n')))
    sA1 = dst(w, A, [m1], 'sumeq2dv', 'sum_ k e. %s ( %s x. %s ) = sum_ k e. %s sum_ n e. %s ( %s x. %s )' % (KJ, CK('k'), TAYSUM('J', 'k', IM), KJ, R, CK('k'), tk('k', 'n')))
    Aknn = '( %s /\\ ( k e. %s /\\ n e. %s ) )' % (A, KJ, R)
    cc2 = liftcl(w, None, Aknn, base)
    kn2 = ap(w, Aknn, 'elfznn0', [w.s([], 'simprl', '( %s -> k e. %s )' % (Aknn, KJ))], 'k e. NN0')
    cc2.leaf('k', 'NN0', kn2); cc2.leaf('( ! ` k )', 'NN', dst(w, Aknn, [kn2], 'faccld', '( ! ` k ) e. NN'))
    termcl(w, Aknn, cc2, 'n', ap(w, Aknn, 'elfznn', [w.s([], 'simprr', '( %s -> n e. %s )' % (Aknn, R))], 'n e. NN'), F, rp3); coeffcl(w, Aknn, cc2, 'n', 'k')
    com = w.s([dst(w, A, [], 'fzfid', '%s e. Fin' % KJ), dst(w, A, [], 'fzfid', '%s e. Fin' % R), cc2.mem('( %s x. %s )' % (CK('k'), tk('k', 'n')), 'CC')], 'fsumcom',
              '( %s -> sum_ k e. %s sum_ n e. %s ( %s x. %s ) = sum_ n e. %s sum_ k e. %s ( %s x. %s ) )' % (A, KJ, R, CK('k'), tk('k', 'n'), R, KJ, CK('k'), tk('k', 'n')))
    sA = eqt(w, A, sA1, com)
    # step B: sum_n sum_k + sum_n r = sum_n ( sum_k + r )
    An = '( %s /\\ n e. %s )' % (A, R)
    nN = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, R))], 'n e. NN')
    cn = liftcl(w, None, An, base); termcl(w, An, cn, 'n', nN, F, rp3)
    Ank = '( %s /\\ k e. %s )' % (An, KJ)
    cnk = ck_of(w, Ank, c, base); termcl(w, Ank, cnk, 'n', lift(w, nN, Ank), F, rp3); coeffcl(w, Ank, cnk, 'n', 'k')
    SK = 'sum_ k e. %s ( %s x. %s )' % (KJ, CK('k'), tk('k', 'n'))
    skc = dst(w, An, [dst(w, An, [], 'fzfid', '%s e. Fin' % KJ), cnk.mem('( %s x. %s )' % (CK('k'), tk('k', 'n')), 'CC')], 'fsumcl', '%s e. CC' % SK)
    cn.leaf(SK, 'CC', skc)
    cn.leaf(TREM(DELTA, NBJ, JPAR, 'n'), 'RR', None) if False else None
    # closure of TREM: its TPOLY sum
    PK = TPOLY(DELTA, NBJ, JPAR, 'n')
    cnk2 = ck_of(w, Ank, c, base); termcl(w, Ank, cnk2, 'n', lift(w, nN, Ank), F, rp3)
    LRn = LOGR('n', NBJ)
    cnk2.leaf(LRn, 'RR', cnk2.mem(LRn, 'RR'))
    pkr = dst(w, An, [dst(w, An, [], 'fzfid', '%s e. Fin' % KJ), cnk2.mem('( ( ( %s ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % (DELTA, LRn), 'RR')], 'fsumrecl', '%s e. RR' % PK)
    cn.leaf(PK, 'RR', pkr)
    rmc = cn.mem(REMTERM('J', 'n'), 'CC')
    sB = eqc(w, A, dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % R), skc, rmc], 'fsumadd', 'sum_ n e. %s ( %s + %s ) = ( sum_ n e. %s %s + %s )' % (R, SK, REMTERM('J', 'n'), R, SK, REMSUM('J'))))
    # step C: nb x. sum_n = sum_n nb x.
    sC = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % R), c.mem(nbc, 'CC'), cn.mem('( %s + %s )' % (SK, REMTERM('J', 'n')), 'CC')], 'fsummulc2',
             '( %s x. sum_ n e. %s ( %s + %s ) ) = sum_ n e. %s ( %s x. ( %s + %s ) )' % (nbc, R, SK, REMTERM('J', 'n'), R, nbc, SK, REMTERM('J', 'n')))
    # step D: per n
    a, e, cnv, nt, nx = BVA('n'), EXY('n'), '( C ` n )', '( n ^c -u T )', NEX('n', IM)
    Ab = '( %s /\\ %s )' % (An, BLKC('J', 'n'))
    cb = liftcl(w, None, Ab, base); termcl(w, Ab, cb, 'n', lift(w, nN, Ab), F, rp3)
    for e_ in (PK, ): cb.leaf(e_, 'RR', lift(w, pkr, Ab))
    cb.leaf(LRn, 'RR', cb.mem(LRn, 'RR'))
    blk = w.s([], 'simpr', '( %s -> %s )' % (Ab, BLKC('J', 'n')))
    nle = ap(w, Ab, 'elfzle2', [lift(w, w.s([], 'simpr', '( %s -> n e. %s )' % (An, R)), Ab)], 'n <_ %s' % NMAX)
    cnd = dst(w, Ab, [dst(w, Ab, [blk], 'simpld', '%s < n' % NBJ), dst(w, Ab, [blk], 'simprd', 'n <_ ( ( 2 ^ ( J + 1 ) ) x. D )'), nle], '3jca', cond_of('J', 'n'))
    Abk = '( %s /\\ k e. %s )' % (Ab, KJ)
    cbk = ck_of(w, Abk, c, base); termcl(w, Abk, cbk, 'n', lift(w, nN, Abk), F, rp3); cbk.leaf(LRn, 'RR', cbk.mem(LRn, 'RR'))
    Lk = '( %s ^ k )' % LRn
    CV = '( ( ( %s x. %s ) x. %s ) x. %s )' % (a, e, Lk, nt)
    cv = dst(w, Abk, [lift(w, cnd, Abk)], 'iftrued', '%s = %s' % (COEFF('J', 'k', 'n'), CV))
    tkv = dst(w, Abk, [dst(w, Abk, [cv], 'oveq1d', '( %s x. %s ) = ( %s x. %s )' % (COEFF('J', 'k', 'n'), cnv, CV, cnv))], 'oveq1d', '%s = ( ( %s x. %s ) x. %s )' % (tk('k', 'n'), CV, cnv, nx))
    PRE = '( ( ( ( %s x. %s ) x. %s ) x. %s ) x. %s )' % (a, e, nt, cnv, nx)
    for e_ in (a, e, nt, cnv, nx, Lk, CK('k')):
        cbk.leaf(e_, 'CC', cbk.mem(e_, 'CC'))
    rg = ringeq(w, Abk, '( %s x. ( ( %s x. %s ) x. %s ) )' % (CK('k'), CV, cnv, nx), '( %s x. ( %s x. %s ) )' % (PRE, CK('k'), Lk), cbk)
    per = eqt(w, Abk, dst(w, Abk, [tkv], 'oveq2d', '( %s x. %s ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (CK('k'), tk('k', 'n'), CK('k'), CV, cnv, nx)), rg)
    for e_ in (a, e, nt, cnv, nx):
        cb.leaf(e_, 'CC', cb.mem(e_, 'CC'))
    cb.mem(PRE, 'CC')
    sk1 = dst(w, Ab, [per], 'sumeq2dv', '%s = sum_ k e. %s ( %s x. ( %s x. %s ) )' % (SK, KJ, PRE, CK('k'), Lk))
    sk2 = eqc(w, Ab, dst(w, Ab, [dst(w, Ab, [], 'fzfid', '%s e. Fin' % KJ), cb.mem(PRE, 'CC'), cbk.mem('( %s x. %s )' % (CK('k'), Lk), 'CC')], 'fsummulc2',
                            '( %s x. %s ) = sum_ k e. %s ( %s x. ( %s x. %s ) )' % (PRE, PK, KJ, PRE, CK('k'), Lk)))
    skv = eqt(w, Ab, sk1, sk2)                                                              # SK = PRE PK
    RT = TREM(DELTA, NBJ, JPAR, 'n')
    rv = dst(w, Ab, [blk], 'iftrued', '%s = %s' % (REMTERM('J', 'n'), RBODY('J', 'n')))
    cb.leaf(RT, 'RR', cb.mem(RT, 'RR'))
    sum_ = dst(w, Ab, [skv, rv], 'oveq12d', '( %s + %s ) = ( ( %s x. %s ) + %s )' % (SK, REMTERM('J', 'n'), PRE, PK, RBODY('J', 'n')))
    GRP = '( ( ( %s x. %s ) x. %s ) x. %s )' % (a, e, cnv, nx)
    rg2 = ringeq(w, Ab, '( ( %s x. %s ) + %s )' % (PRE, PK, RBODY('J', 'n')), '( %s x. ( %s x. ( %s + %s ) ) )' % (GRP, nt, PK, RT), cb)
    rp_ = ap(w, Ab, 'ld1rpowtay', [J(w, Ab, J(w, Ab, cb.mem(NBJ, 'RR+'), cb.mem('n', 'NN')), J(w, Ab, cb.mem('T', 'RR'), cb.mem(DELTA, 'RR')), cb.mem(JPAR, 'NN0'))],
             '( n ^c -u ( T + %s ) ) = ( %s x. ( %s x. ( %s + %s ) ) )' % (DELTA, nbc, nt, PK, RT))
    tre = dst(w, Ab, [cb.mem('T', 'CC'), cb.mem('( Re ` S )', 'CC')], 'pncan3d', '( T + %s ) = ( Re ` S )' % DELTA)
    rp2 = eqt(w, Ab, eqc(w, Ab, rp_), dst(w, Ab, [dst(w, Ab, [tre], 'negeqd', '-u ( T + %s ) = -u ( Re ` S )' % DELTA)], 'oveq2d', '( n ^c -u ( T + %s ) ) = ( n ^c -u ( Re ` S ) )' % DELTA))
    cpw = ap(w, Ab, 'ld1cpow', [J(w, Ab, cb.mem('n', 'NN'), cb.mem('S', 'CC'))], '( n ^c -u S ) = ( ( n ^c -u ( Re ` S ) ) x. %s )' % nx)
    full = eqt(w, Ab, dst(w, Ab, [sum_], 'oveq2d', '( %s x. ( %s + %s ) ) = ( %s x. ( ( %s x. %s ) + %s ) )' % (nbc, SK, REMTERM('J', 'n'), nbc, PRE, PK, RBODY('J', 'n'))),
               dst(w, Ab, [rg2], 'oveq2d', '( %s x. ( ( %s x. %s ) + %s ) ) = ( %s x. ( %s x. ( %s x. ( %s + %s ) ) ) )' % (nbc, PRE, PK, RBODY('J', 'n'), nbc, GRP, nt, PK, RT)))
    nr = '( n ^c -u ( Re ` S ) )'
    cb.leaf(nr, 'CC', cb.mem(nr, 'CC'))
    rg3 = ringeq(w, Ab, '( %s x. ( %s x. ( %s x. ( %s + %s ) ) ) )' % (nbc, GRP, nt, PK, RT), '( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) )' % (a, e, cnv, nx, '( %s x. ( %s x. ( %s + %s ) ) )' % (nbc, nt, PK, RT)), cb)
    rg4 = dst(w, Ab, [dst(w, Ab, [rp2], 'oveq2d', '( %s x. ( %s x. ( %s x. ( %s + %s ) ) ) ) = ( %s x. %s )' % (nx, nbc, nt, PK, RT, nx, nr))], 'oveq2d',
              '( ( ( %s x. %s ) x. %s ) x. ( %s x. ( %s x. ( %s x. ( %s + %s ) ) ) ) ) = ( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) )' % (a, e, cnv, nx, nbc, nt, PK, RT, a, e, cnv, nx, nr))
    rg5 = dst(w, Ab, [dst(w, Ab, [cb.mem(nx, 'CC'), cb.mem(nr, 'CC')], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (nx, nr, nr, nx))], 'oveq2d',
              '( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) ) = ( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) )' % (a, e, cnv, nx, nr, a, e, cnv, nr, nx))
    rg6 = dst(w, Ab, [eqc(w, Ab, cpw)], 'oveq2d', '( ( ( %s x. %s ) x. %s ) x. ( %s x. %s ) ) = %s' % (a, e, cnv, nr, nx, BODY('n')))
    case1 = eqt(w, Ab, eqt(w, Ab, eqt(w, Ab, eqt(w, Ab, full, rg3), rg4), rg5), rg6)
    tv = dst(w, Ab, [blk], 'iftrued', 'if ( %s , %s , 0 ) = %s' % (BLKC('J', 'n'), BODY('n'), BODY('n')))
    c1 = dst(w, Ab, [case1, tv], 'eqtr4d', '( %s x. ( %s + %s ) ) = if ( %s , %s , 0 )' % (nbc, SK, REMTERM('J', 'n'), BLKC('J', 'n'), BODY('n')))
    # not in the block
    Anb = '( %s /\\ -. %s )' % (An, BLKC('J', 'n'))
    nblk = w.s([], 'simpr', '( %s -> -. %s )' % (Anb, BLKC('J', 'n')))
    Anbk = '( %s /\\ k e. %s )' % (Anb, KJ)
    cnbk = ck_of(w, Anbk, c, base); termcl(w, Anbk, cnbk, 'n', lift(w, nN, Anbk), F, rp3)
    z = dst(w, Anbk, [lift(w, nblk, Anbk), w.s([], 'ld1cjk0', '( -. %s -> %s = 0 )' % (BLKC('J', 'n'), COEFF('J', 'k', 'n')))], 'syl', '%s = 0' % COEFF('J', 'k', 'n'))
    z1 = dst(w, Anbk, [dst(w, Anbk, [z], 'oveq1d', '( %s x. %s ) = ( 0 x. %s )' % (COEFF('J', 'k', 'n'), cnv, cnv)), dst(w, Anbk, [cnbk.mem(cnv, 'CC')], 'mul02d', '( 0 x. %s ) = 0' % cnv)], 'eqtrd', '( %s x. %s ) = 0' % (COEFF('J', 'k', 'n'), cnv))
    z2 = dst(w, Anbk, [dst(w, Anbk, [z1], 'oveq1d', '%s = ( 0 x. %s )' % (tk('k', 'n'), nx)), dst(w, Anbk, [cnbk.mem(nx, 'CC')], 'mul02d', '( 0 x. %s ) = 0' % nx)], 'eqtrd', '%s = 0' % tk('k', 'n'))
    z3 = dst(w, Anbk, [dst(w, Anbk, [z2], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (CK('k'), tk('k', 'n'), CK('k'))), dst(w, Anbk, [cnbk.mem(CK('k'), 'CC')], 'mul01d', '( %s x. 0 ) = 0' % CK('k'))], 'eqtrd', '( %s x. %s ) = 0' % (CK('k'), tk('k', 'n')))
    sz = eqt(w, Anb, dst(w, Anb, [z3], 'sumeq2dv', '%s = sum_ k e. %s 0' % (SK, KJ)), ap(w, Anb, 'sumz', [dst(w, Anb, [dst(w, Anb, [], 'fzfid', '%s e. Fin' % KJ)], 'olcd', '( %s C_ ( ZZ>= ` 0 ) \\/ %s e. Fin )' % (KJ, KJ))], 'sum_ k e. %s 0 = 0' % KJ))
    rz = dst(w, Anb, [nblk], 'iffalsed', '%s = 0' % REMTERM('J', 'n'))
    s0 = dst(w, Anb, [dst(w, Anb, [sz, rz], 'oveq12d', '( %s + %s ) = ( 0 + 0 )' % (SK, REMTERM('J', 'n'))), a1(w, Anb, '00id', '( 0 + 0 ) = 0')], 'eqtrd', '( %s + %s ) = 0' % (SK, REMTERM('J', 'n')))
    m0 = dst(w, Anb, [dst(w, Anb, [s0], 'oveq2d', '( %s x. ( %s + %s ) ) = ( %s x. 0 )' % (nbc, SK, REMTERM('J', 'n'), nbc)), dst(w, Anb, [lift(w, c.mem(nbc, 'CC'), Anb)], 'mul01d', '( %s x. 0 ) = 0' % nbc)], 'eqtrd', '( %s x. ( %s + %s ) ) = 0' % (nbc, SK, REMTERM('J', 'n')))
    fv = dst(w, Anb, [nblk], 'iffalsed', 'if ( %s , %s , 0 ) = 0' % (BLKC('J', 'n'), BODY('n')))
    c2 = dst(w, Anb, [m0, fv], 'eqtr4d', '( %s x. ( %s + %s ) ) = if ( %s , %s , 0 )' % (nbc, SK, REMTERM('J', 'n'), BLKC('J', 'n'), BODY('n')))
    pern = dst(w, An, [c1, c2], 'pm2.61dan', '( %s x. ( %s + %s ) ) = if ( %s , %s , 0 )' % (nbc, SK, REMTERM('J', 'n'), BLKC('J', 'n'), BODY('n')))
    sD = dst(w, A, [pern], 'sumeq2dv', 'sum_ n e. %s ( %s x. ( %s + %s ) ) = %s' % (R, nbc, SK, REMTERM('J', 'n'), BLKSUM('J')))
    # assemble: RHS = nb ( sum_k c_k TAYSUM + REMSUM ) = nb ( sum_n SK + REMSUM ) = nb sum_n ( SK + r ) = sum_n nb (...) = BLKSUM
    RHS0 = '( %s x. ( %s + %s ) )' % (nbc, TAYK('J'), REMSUM('J'))
    r1 = dst(w, A, [dst(w, A, [sA], 'oveq1d', '( %s + %s ) = ( sum_ n e. %s %s + %s )' % (TAYK('J'), REMSUM('J'), R, SK, REMSUM('J')))], 'oveq2d', '%s = ( %s x. ( sum_ n e. %s %s + %s ) )' % (RHS0, nbc, R, SK, REMSUM('J')))
    r2 = dst(w, A, [sB], 'oveq2d', '( %s x. ( sum_ n e. %s %s + %s ) ) = ( %s x. sum_ n e. %s ( %s + %s ) )' % (nbc, R, SK, REMSUM('J'), nbc, R, SK, REMTERM('J', 'n')))
    dst(w, A, [eqt(w, A, eqt(w, A, eqt(w, A, r1, r2), sC), sD)], 'eqcomd', '%s = %s' % (BLKSUM('J'), RHS0))
    return fin(w)


def ld1blkabs():
    w = W('ld1blkabs', 'Lean ` norm_blockSum_le ` : ` abs S_j <_ sum_ ( k <_ J ) abs T_jk + abs R_j ` , from ` N_j ^ -u delta <_ 1 ` and ` delta ^ k / k ! <_ 1 ` (~ ld1blktay , ~ fsumabs , ~ cxplea ).')
    A = ante('ld1blkabs'); P, c, F = setupx(w, A)
    tr, jn = P['T e. RR'], P['J e. NN0']; t0, tle, re1 = P['0 <_ T'], P['T <_ ( Re ` S )'], P['( Re ` S ) <_ 1']
    h0, rp3 = hab(w, A, F)
    c.leaf('T', 'RR', tr); c.leaf('J', 'NN0', jn); c.leaf('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC')); c.leaf(IM, 'RR', dst(w, A, [F['sc']], 'imcld', '%s e. RR' % IM))
    base = basefacts(F) + [('T', 'RR', tr), ('J', 'NN0', jn), ('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC')), ('( Re ` S )', 'RR', F['re']), (IM, 'RR', dst(w, A, [F['sc']], 'imcld', '%s e. RR' % IM))]
    NBJ = NB('J'); nbc = '( %s ^c -u %s )' % (NBJ, DELTA)
    bt = ap(w, A, 'ld1blktay', [J(w, A, J(w, A, F['hz'], P[CFN]), J(w, A, J(w, A, F['sc'], tr), jn))], concl('ld1blktay'))
    INNER = '( %s + %s )' % (TAYK('J'), REMSUM('J'))
    # closures of TAYSUM(k), REMSUM
    Ak = '( %s /\\ k e. %s )' % (A, KJ)
    ck = ck_of(w, Ak, c, base)
    Akn = '( %s /\\ n e. %s )' % (Ak, FZN)
    ckn = liftcl(w, None, Akn, base); ckn.leaf('k', 'NN0', lift(w, ck.mem('k', 'NN0'), Akn))
    termcl(w, Akn, ckn, 'n', ap(w, Akn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Akn, FZN))], 'n e. NN'), F, rp3); coeffcl(w, Akn, ckn, 'n', 'k')
    TK = TAYSUM('J', 'k', IM)
    tkc = dst(w, Ak, [dst(w, Ak, [], 'fzfid', '%s e. Fin' % FZN), ckn.mem(TSUMMAND('J', 'k', 'n', IM), 'CC')], 'fsumcl', '%s e. CC' % TK)
    ck.leaf(TK, 'CC', tkc)
    An = '( %s /\\ n e. %s )' % (A, FZN)
    cn = liftcl(w, None, An, base); termcl(w, An, cn, 'n', ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZN))], 'n e. NN'), F, rp3)
    Ank = '( %s /\\ k e. %s )' % (An, KJ)
    cnk = ck_of(w, Ank, c, base); termcl(w, Ank, cnk, 'n', lift(w, cn.mem('n', 'NN'), Ank), F, rp3)
    LRn = LOGR('n', NBJ); cnk.leaf(LRn, 'RR', cnk.mem(LRn, 'RR'))
    PK = TPOLY(DELTA, NBJ, JPAR, 'n')
    cn.leaf(PK, 'RR', dst(w, An, [dst(w, An, [], 'fzfid', '%s e. Fin' % KJ), cnk.mem('( ( ( %s ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % (DELTA, LRn), 'RR')], 'fsumrecl', '%s e. RR' % PK))
    rsc = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % FZN), cn.mem(REMTERM('J', 'n'), 'CC')], 'fsumcl', '%s e. CC' % REMSUM('J'))
    c.leaf(BLKSUM('J'), 'CC', dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % FZN), cn.mem('if ( %s , %s , 0 )' % (BLKC('J', 'n'), BODY('n')), 'CC')], 'fsumcl', '%s e. CC' % BLKSUM('J')))
    c.leaf(REMSUM('J'), 'CC', rsc)
    CK = lambda k: '( ( %s ^ %s ) / ( ! ` %s ) )' % (DELTA, k, k)
    skc = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % KJ), ck.mem('( %s x. %s )' % (CK('k'), TK), 'CC')], 'fsumcl', '%s e. CC' % TAYK('J'))
    c.leaf(TAYK('J'), 'CC', skc)
    # abs of the product
    nbr = c.mem(nbc, 'RR'); nb0 = c.ge0(nbc)
    am = dst(w, A, [c.mem(nbc, 'CC'), c.mem(INNER, 'CC')], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (nbc, INNER, nbc, INNER))
    ai = dst(w, A, [nbr, nb0], 'absidd', '( abs ` %s ) = %s' % (nbc, nbc))
    # nb <_ 1
    nb1 = ap(w, A, 'expge1', [J(w, A, c.mem('2', 'RR'), jn, w.s([num.le_lit(w, '1', '2')], 'a1i', '( %s -> 1 <_ 2 )' % A))], '1 <_ ( 2 ^ J )')
    nbge1 = nlinarith(w, A, [nb1, F['d1']], '1 <_ %s' % NBJ, closure=c)
    dneg = linarith(w, A, [tle], '-u %s <_ 0' % DELTA, closure=c)
    cx = ap(w, A, 'cxplea', [J(w, A, c.mem(NBJ, 'RR'), nbge1), J(w, A, c.mem('-u %s' % DELTA, 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % A)), dneg], '%s <_ ( %s ^c 0 )' % (nbc, NBJ))
    nble = dst(w, A, [cx, ap(w, A, 'cxp0', [c.mem(NBJ, 'CC')], '( %s ^c 0 ) = 1' % NBJ)], 'breqtrd', '%s <_ 1' % nbc)
    # abs INNER <_ sum_k abs ( c_k TK ) + abs REMSUM <_ sum_k abs TK + abs REMSUM
    tri = dst(w, A, [c.mem(TAYK('J'), 'CC'), c.mem(REMSUM('J'), 'CC')], 'abstrid', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (INNER, TAYK('J'), REMSUM('J')))
    fa = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % KJ), ck.mem('( %s x. %s )' % (CK('k'), TK), 'CC')], 'fsumabs', '( abs ` %s ) <_ sum_ k e. %s ( abs ` ( %s x. %s ) )' % (TAYK('J'), KJ, CK('k'), TK))
    # per k: abs ( c_k TK ) <_ abs TK
    ckr = ck.mem(CK('k'), 'RR'); ck0 = ck.ge0(CK('k')) if False else None
    d0 = linarith(w, Ak, [lift(w, tle, Ak)], '0 <_ %s' % DELTA, closure=ck); d1 = linarith(w, Ak, [lift(w, t0, Ak), lift(w, re1, Ak)], '%s <_ 1' % DELTA, closure=ck)
    ck.leaf(DELTA, 'RR', ck.mem(DELTA, 'RR')); ck.leaf(DELTA, 'ge0', d0)
    pw1 = ap(w, Ak, 'exple1', [J(w, Ak, ck.mem(DELTA, 'RR'), d0, d1), ck.mem('k', 'NN0')], '( %s ^ k ) <_ 1' % DELTA)
    fk1 = dst(w, Ak, [ck.mem('( ! ` k )', 'NN')], 'nnge1d', '1 <_ ( ! ` k )')
    pk0 = ck.ge0('( %s ^ k )' % DELTA)
    ldm = ap(w, Ak, 'ledivmul', [ck.mem('( %s ^ k )' % DELTA, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % Ak), J(w, Ak, ck.mem('( ! ` k )', 'RR'), ck.gt0('( ! ` k )'))], '( %s <_ 1 <-> ( %s ^ k ) <_ ( ( ! ` k ) x. 1 ) )' % (CK('k'), DELTA))
    ck.leaf('( %s ^ k )' % DELTA, 'RR', ck.mem('( %s ^ k )' % DELTA, 'RR')); ck.leaf('( ! ` k )', 'RR', ck.mem('( ! ` k )', 'RR'))
    ck1 = dst(w, Ak, [linarith(w, Ak, [pw1, fk1], '( %s ^ k ) <_ ( ( ! ` k ) x. 1 )' % DELTA, closure=ck), ldm], 'mpbird', '%s <_ 1' % CK('k'))
    ckge = ck.ge0(CK('k'))
    amk = dst(w, Ak, [ck.mem(CK('k'), 'CC'), tkc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CK('k'), TK, CK('k'), TK))
    aik = dst(w, Ak, [ckr, ckge], 'absidd', '( abs ` %s ) = %s' % (CK('k'), CK('k')))
    ATK = '( abs ` %s )' % TK
    ck.leaf(ATK, 'RR', dst(w, Ak, [tkc], 'abscld', '%s e. RR' % ATK)); ck.leaf(ATK, 'ge0', dst(w, Ak, [tkc], 'absge0d', '0 <_ %s' % ATK))
    m1 = lemul(w, Ak, ck, ck1, ATK, side=1)                                                 # c_k ATK <_ 1 ATK
    perk = dst(w, Ak, [eqt(w, Ak, amk, dst(w, Ak, [aik], 'oveq1d', '( ( abs ` %s ) x. %s ) = ( %s x. %s )' % (CK('k'), ATK, CK('k'), ATK))), dst(w, Ak, [m1, dst(w, Ak, [ck.mem(ATK, 'CC')], 'mullidd', '( 1 x. %s ) = %s' % (ATK, ATK))], 'breqtrd', '( %s x. %s ) <_ %s' % (CK('k'), ATK, ATK))], 'eqbrtrd',
               '( abs ` ( %s x. %s ) ) <_ %s' % (CK('k'), TK, ATK))
    fle = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % KJ), dst(w, Ak, [ck.mem('( %s x. %s )' % (CK('k'), TK), 'CC')], 'abscld', '( abs ` ( %s x. %s ) ) e. RR' % (CK('k'), TK)), ck.mem(ATK, 'RR'), perk], 'fsumle',
              'sum_ k e. %s ( abs ` ( %s x. %s ) ) <_ sum_ k e. %s %s' % (KJ, CK('k'), TK, KJ, ATK))
    SAT = 'sum_ k e. %s %s' % (KJ, ATK)
    SUMABS = 'sum_ k e. %s ( abs ` ( %s x. %s ) )' % (KJ, CK('k'), TK)
    AT_, AR_, AIN = '( abs ` %s )' % TAYK('J'), '( abs ` %s )' % REMSUM('J'), '( abs ` %s )' % INNER
    satr = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % KJ), ck.mem(ATK, 'RR')], 'fsumrecl', '%s e. RR' % SAT)
    sabr = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % KJ), dst(w, Ak, [ck.mem('( %s x. %s )' % (CK('k'), TK), 'CC')], 'abscld', '( abs ` ( %s x. %s ) ) e. RR' % (CK('k'), TK))], 'fsumrecl', '%s e. RR' % SUMABS)
    atr = dst(w, A, [c.mem(TAYK('J'), 'CC')], 'abscld', '%s e. RR' % AT_); arr = dst(w, A, [c.mem(REMSUM('J'), 'CC')], 'abscld', '%s e. RR' % AR_)
    ainr = dst(w, A, [c.mem(INNER, 'CC')], 'abscld', '%s e. RR' % AIN); ain0 = dst(w, A, [c.mem(INNER, 'CC')], 'absge0d', '0 <_ %s' % AIN)
    inb1 = dst(w, A, [atr, sabr, satr, fa, fle], 'letrd', '%s <_ %s' % (AT_, SAT))
    inb2 = dst(w, A, [atr, satr, arr, arr, inb1, dst(w, A, [arr], 'leidd', '%s <_ %s' % (AR_, AR_))], 'le2addd', '( %s + %s ) <_ ( %s + %s )' % (AT_, AR_, SAT, AR_))
    sumr = dst(w, A, [satr, arr], 'readdcld', '( %s + %s ) e. RR' % (SAT, AR_))
    sum0 = dst(w, A, [atr, arr], 'readdcld', '( %s + %s ) e. RR' % (AT_, AR_))
    inb = dst(w, A, [ainr, sum0, sumr, tri, inb2], 'letrd', '%s <_ ( %s + %s )' % (AIN, SAT, AR_))
    prod = dst(w, A, [nbr, w.s([], '1red', '( %s -> 1 e. RR )' % A), ainr, sumr, nb0, ain0, nble, inb], 'lemul12ad',
               '( %s x. %s ) <_ ( 1 x. ( %s + %s ) )' % (nbc, AIN, SAT, AR_))
    e1 = eqt(w, A, dst(w, A, [bt], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s x. %s ) )' % (BLKSUM('J'), nbc, INNER)), eqt(w, A, am, dst(w, A, [ai], 'oveq1d', '( ( abs ` %s ) x. %s ) = ( %s x. %s )' % (nbc, AIN, nbc, AIN))))
    dst(w, A, [e1, dst(w, A, [prod, dst(w, A, [dst(w, A, [sumr], 'recnd', '( %s + %s ) e. CC' % (SAT, AR_))], 'mullidd', '( 1 x. ( %s + %s ) ) = ( %s + %s )' % (SAT, AR_, SAT, AR_))], 'breqtrd',
                                '( %s x. %s ) <_ ( %s + %s )' % (nbc, AIN, SAT, AR_))], 'eqbrtrd', '( abs ` %s ) <_ ( %s + %s )' % (BLKSUM('J'), SAT, AR_))
    return fin(w)


def ld1tremabs():
    w = W('ld1tremabs', 'Lean ` abs_taylorRem_le ` : the Taylor remainder on a block is at most ` ( 1 / 5 ) ^ ( J + 1 ) ` for ` 0 <_ delta <_ 11 / 50 ` (~ ld1tayrem , ~ mulexp , ~ log2ub ).')
    A = ante('ld1tremabs'); P = parts(w, A)
    er, e0, e1 = P['E e. RR'], P['0 <_ E'], P['E <_ ( ; 1 1 / ; 5 0 )']
    brp, nn, bn, n2b, jn, j3 = P['B e. RR+'], P['N e. NN'], P['B < N'], P['N <_ ( 2 x. B )'], P['J e. NN0'], P['3 <_ J']
    nrp = dst(w, A, [nn], 'nnrpd', 'N e. RR+')
    c = Closure(w, A, {'E': [('RR', er), ('ge0', e0)], 'B': ('RR+', brp), 'N': ('RR+', nrp), 'J': ('NN0', jn)})
    Q = '( N / B )'; LQ = '( log ` %s )' % Q; LR = LOGR('N', 'B')
    q1 = dst(w, A, [bn, ap(w, A, 'ltdivmul2' if False else 'x', [], '') if False else dst(w, A, [c.mem('B', 'RR'), c.mem('N', 'RR'), brp], 'ltdiv1d' if False else 'x', 'x') if False else None], 'x', 'x') if False else None
    # 1 < N / B  and  N / B <_ 2
    q1 = dst(w, A, [dst(w, A, [dst(w, A, [c.mem('B', 'CC'), c.ne0('B')], 'dividd', '( B / B ) = 1')], 'eqcomd', '1 = ( B / B )'),
                    dst(w, A, [bn, ap(w, A, 'ltdiv1', [c.mem('B', 'RR'), c.mem('N', 'RR'), J(w, A, c.mem('B', 'RR'), c.gt0('B'))], '( B < N <-> ( B / B ) < ( N / B ) )')], 'mpbid', '( B / B ) < %s' % Q)], 'eqbrtrd', '1 < %s' % Q)
    ldm = ap(w, A, 'ledivmul', [c.mem('N', 'RR'), c.mem('2', 'RR'), J(w, A, c.mem('B', 'RR'), c.gt0('B'))], '( %s <_ 2 <-> N <_ ( B x. 2 ) )' % Q)
    q2 = dst(w, A, [dst(w, A, [n2b, dst(w, A, [c.mem('2', 'CC'), c.mem('B', 'CC')], 'mulcomd', '( 2 x. B ) = ( B x. 2 )')], 'breqtrd', 'N <_ ( B x. 2 )'), ldm], 'mpbird', '%s <_ 2' % Q)
    lq0 = ap(w, A, 'logge0' if False else 'x', [], '') if False else None
    lq0 = dst(w, A, [dst(w, A, [c.mem(Q, 'RR'), q1], 'ltled', '1 <_ %s' % Q), ap(w, A, 'logge0b', [c.mem(Q, 'RR+')], '( 0 <_ %s <-> 1 <_ %s )' % (LQ, Q))], 'mpbird', '0 <_ %s' % LQ) if False else None
    lq0 = ap(w, A, 'logge0', [J(w, A, c.mem(Q, 'RR'), dst(w, A, [w.s([], '1red', '( %s -> 1 e. RR )' % A), c.mem(Q, 'RR'), q1], 'ltled', '1 <_ %s' % Q))], '0 <_ %s' % LQ)
    lq2 = dst(w, A, [q2, dst(w, A, [c.mem(Q, 'RR+'), a1(w, A, '2rp', '2 e. RR+')], 'logled', '( %s <_ 2 <-> %s <_ %s )' % (Q, LQ, L2))], 'mpbid', '%s <_ %s' % (LQ, L2))
    l2u = w.s([w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % L2)], 'a1i', '( %s -> %s < ( ; ; 2 5 3 / ; ; 3 6 5 ) )' % (A, L2))
    c.leaf(LQ, 'RR', c.mem(LQ, 'RR')); c.leaf(L2, 'RR', c.mem(L2, 'RR'))
    X = '( E x. %s )' % LR
    xr = c.mem(X, 'RR')
    ax = dst(w, A, [xr, c.mem(LQ, 'RR') if False else None], 'x', 'x') if False else None
    # abs X = E LQ
    xe = dst(w, A, [c.mem('E', 'CC'), c.mem(LQ, 'CC')], 'mulneg2d', '%s = -u ( E x. %s )' % (X, LQ))
    an = dst(w, A, [c.mem('( E x. %s )' % LQ, 'CC')], 'absnegd', '( abs ` -u ( E x. %s ) ) = ( abs ` ( E x. %s ) )' % (LQ, LQ))
    ai = dst(w, A, [c.mem('( E x. %s )' % LQ, 'RR'), dst(w, A, [er, c.mem(LQ, 'RR'), e0, lq0], 'mulge0d', '0 <_ ( E x. %s )' % LQ)], 'absidd', '( abs ` ( E x. %s ) ) = ( E x. %s )' % (LQ, LQ))
    axe = eqt(w, A, eqt(w, A, dst(w, A, [xe], 'fveq2d', '( abs ` %s ) = ( abs ` -u ( E x. %s ) )' % (X, LQ)), an), ai)   # abs X = E LQ
    b1 = nlinarith(w, A, [e0, e1, lq0, lq2, l2u], '( E x. %s ) <_ ( 1 / 6 )' % LQ, closure=c)
    ax16 = dst(w, A, [axe, b1], 'eqbrtrd', '( abs ` %s ) <_ ( 1 / 6 )' % X)
    tr = ap(w, A, 'ld1tayrem', [J(w, A, J(w, A, xr, ax16), J(w, A, jn, j3))], '( abs ` ( ( exp ` %s ) - sum_ k e. ( 0 ... J ) ( ( %s ^ k ) / ( ! ` k ) ) ) ) <_ %s' % (X, X, FIFTH('J')))
    # the polynomial: sum ( E^k / k! ) LR^k = sum X^k / k!
    Ak = '( %s /\\ k e. ( 0 ... J ) )' % A
    kn = ap(w, Ak, 'elfznn0', [w.s([], 'simpr', '( %s -> k e. ( 0 ... J ) )' % Ak)], 'k e. NN0')
    ck = Closure(w, Ak, {'E': ('RR', lift(w, er, Ak)), LR: ('RR', lift(w, c.mem(LR, 'RR'), Ak)), 'k': ('NN0', kn), X: ('RR', lift(w, xr, Ak))})
    ck.leaf('( ! ` k )', 'NN', dst(w, Ak, [kn], 'faccld', '( ! ` k ) e. NN'))
    me = ap(w, Ak, 'mulexp', [ck.mem('E', 'CC'), ck.mem(LR, 'CC'), kn], '( %s ^ k ) = ( ( E ^ k ) x. ( %s ^ k ) )' % (X, LR))
    perk = eqc(w, Ak, eqt(w, Ak, dst(w, Ak, [me], 'oveq1d', '( ( %s ^ k ) / ( ! ` k ) ) = ( ( ( E ^ k ) x. ( %s ^ k ) ) / ( ! ` k ) )' % (X, LR)),
                            dst(w, Ak, [ck.mem('( E ^ k )', 'CC'), ck.mem('( %s ^ k )' % LR, 'CC'), ck.mem('( ! ` k )', 'CC'), ck.ne0('( ! ` k )')], 'div23d', '( ( ( E ^ k ) x. ( %s ^ k ) ) / ( ! ` k ) ) = ( ( ( E ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % (LR, LR))))
    se = dst(w, A, [perk], 'sumeq2dv', '%s = sum_ k e. ( 0 ... J ) ( ( %s ^ k ) / ( ! ` k ) )' % (TPOLY('E', 'B', 'J', 'N'), X))
    dst(w, A, [dst(w, A, [dst(w, A, [se], 'oveq2d', '%s = ( ( exp ` %s ) - sum_ k e. ( 0 ... J ) ( ( %s ^ k ) / ( ! ` k ) ) )' % (TREM('E', 'B', 'J', 'N'), X, X))], 'fveq2d',
                          '( abs ` %s ) = ( abs ` ( ( exp ` %s ) - sum_ k e. ( 0 ... J ) ( ( %s ^ k ) / ( ! ` k ) ) ) )' % (TREM('E', 'B', 'J', 'N'), X, X)), tr], 'eqbrtrd',
        '( abs ` %s ) <_ %s' % (TREM('E', 'B', 'J', 'N'), FIFTH('J')))
    return fin(w)


def ld1rtabs():
    w = W('ld1rtabs', 'Lean ` norm_remTerm_le ` : the pointwise bound on the remainder summand, ` ( 1 / 5 ) ^ ( J + 1 ) N_j ^ -u sigma tau ( n ) ` on the block, ` 0 ` off it (~ ld1tremabs , ~ ld1bvatau , ~ divcxp , ~ absefi ).')
    A = ante('ld1rtabs'); P, c, F = setupx(w, A)
    tr, t0, tle, rle = P['T e. RR'], P['0 <_ T'], P['T <_ ( Re ` S )'], P['( Re ` S ) <_ ( T + ( ; 1 1 / ; 5 0 ) )']
    jn, nn = P['J e. NN0'], P['N e. NN']
    h0, rp3 = hab(w, A, F)
    c.leaf('T', 'RR', tr); c.leaf('T', 'ge0', t0); c.leaf('J', 'NN0', jn); c.leaf(IM, 'RR', dst(w, A, [F['sc']], 'imcld', '%s e. RR' % IM)); c.leaf('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC'))
    termcl(w, A, c, 'N', nn, F, rp3)
    NBJ = NB('J'); FL = '( |_ ` ( 2 x. %s ) )' % NBJ
    FF = FIFTH(JPAR); nbt = '( %s ^c -u T )' % NBJ
    RHS = 'if ( N <_ %s , ( ( %s x. %s ) x. %s ) , 0 )' % (FL, FF, nbt, TAU('N'))
    jp = ap(w, A, 'ld1jpar', [F['hz']], concl('ld1jpar'))
    j3 = dst(w, A, [dst(w, A, [jp], 'simpld', '( %s e. NN /\\ 3 <_ %s )' % (JPAR, JPAR))], 'simprd', '3 <_ %s' % JPAR)
    tau = ap(w, A, 'ld1bvatau', [J(w, A, h0, nn)], '( abs ` %s ) <_ %s' % (BVA('N'), TAU('N')))
    c.leaf(TAU('N'), 'RR', dst(w, A, [ap(w, A, 'hashcl', [ap(w, A, 'dvdsfi', [nn], '%s e. Fin' % DV('N'))], '%s e. NN0' % TAU('N'))], 'nn0red', '%s e. RR' % TAU('N')))
    c.leaf(TAU('N'), 'ge0', dst(w, A, [ap(w, A, 'hashcl', [ap(w, A, 'dvdsfi', [nn], '%s e. Fin' % DV('N'))], '%s e. NN0' % TAU('N'))], 'nn0ge0d', '0 <_ %s' % TAU('N')))
    # case in the block
    A1 = '( %s /\\ %s )' % (A, BLKC('J', 'N'))
    blk = w.s([], 'simpr', '( %s -> %s )' % (A1, BLKC('J', 'N')))
    c1 = liftcl(w, None, A1, basefacts(F) + [('T', 'RR', tr), ('T', 'ge0', t0), ('J', 'NN0', jn), ('N', 'NN', nn), (BVA('N'), 'RR', c.mem(BVA('N'), 'RR')), ('( C ` N )', 'CC', c.mem('( C ` N )', 'CC')),
                                              (IM, 'RR', c.mem(IM, 'RR')), ('_i', 'CC', c.mem('_i', 'CC')), ('( Re ` S )', 'RR', F['re']), (TAU('N'), 'RR', c.mem(TAU('N'), 'RR')), (TAU('N'), 'ge0', c.ge0(TAU('N')))])
    lt1 = dst(w, A1, [blk], 'simpld', '%s < N' % NBJ); le2 = dst(w, A1, [blk], 'simprd', 'N <_ ( ( 2 ^ ( J + 1 ) ) x. D )')
    p1 = dst(w, A1, [dst(w, A1, [c1.mem('2', 'CC'), c1.mem('J', 'NN0')], 'expp1d', '( 2 ^ ( J + 1 ) ) = ( ( 2 ^ J ) x. 2 )')], 'oveq1d', '( ( 2 ^ ( J + 1 ) ) x. D ) = ( ( ( 2 ^ J ) x. 2 ) x. D )')
    rg = ringeq(w, A1, '( ( ( 2 ^ J ) x. 2 ) x. D )', '( 2 x. %s )' % NBJ, c1)
    le2b = dst(w, A1, [le2, eqt(w, A1, p1, rg)], 'breqtrd', 'N <_ ( 2 x. %s )' % NBJ)
    fl = dst(w, A1, [le2b, ap(w, A1, 'flge', [c1.mem('( 2 x. %s )' % NBJ, 'RR'), c1.mem('N', 'ZZ')], '( N <_ ( 2 x. %s ) <-> N <_ %s )' % (NBJ, FL))], 'mpbid', 'N <_ %s' % FL)
    rv = dst(w, A1, [fl], 'iftrued', '%s = ( ( %s x. %s ) x. %s )' % (RHS, FF, nbt, TAU('N')))
    tv = dst(w, A1, [blk], 'iftrued', '%s = %s' % (REMTERM('J', 'N'), RBODY('J', 'N')))
    a, e, nt, cn, nx = BVA('N'), EXY('N'), '( N ^c -u T )', '( C ` N )', NEX('N', IM)
    RT = TREM(DELTA, NBJ, JPAR, 'N')
    # closure of RT
    Ak = '( %s /\\ k e. %s )' % (A1, KJ)
    ck = ck_of(w, Ak, c, basefacts(F) + [('N', 'NN', nn), ('T', 'RR', tr), ('( Re ` S )', 'RR', F['re']), ('J', 'NN0', jn)])
    LRn = LOGR('N', NBJ); ck.leaf(LRn, 'RR', ck.mem(LRn, 'RR'))
    PK = TPOLY(DELTA, NBJ, JPAR, 'N')
    c1.leaf(PK, 'RR', dst(w, A1, [dst(w, A1, [], 'fzfid', '%s e. Fin' % KJ), ck.mem('( ( ( %s ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % (DELTA, LRn), 'RR')], 'fsumrecl', '%s e. RR' % PK))
    c1.leaf(LRn, 'RR', c1.mem(LRn, 'RR'))
    for e_ in (a, e, nt, RT):
        c1.leaf(e_, 'RR', c1.mem(e_, 'RR'))
    c1.leaf(cn, 'CC', c1.mem(cn, 'CC')); c1.leaf(nx, 'CC', c1.mem(nx, 'CC'))
    # abs of the product: ( ( ( ( a e ) nt ) RT ) cn ) nx
    X1 = '( %s x. %s )' % (a, e); X2 = '( %s x. %s )' % (X1, nt); X3 = '( %s x. %s )' % (X2, RT); X4 = '( %s x. %s )' % (X3, cn)
    m1 = dst(w, A1, [c1.mem(X4, 'CC'), c1.mem(nx, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (RBODY('J', 'N'), X4, nx))
    m2 = dst(w, A1, [c1.mem(X3, 'CC'), c1.mem(cn, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X4, X3, cn))
    m3 = dst(w, A1, [c1.mem(X2, 'CC'), c1.mem(RT, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X3, X2, RT))
    m4 = dst(w, A1, [c1.mem(X1, 'CC'), c1.mem(nt, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X2, X1, nt))
    m5 = dst(w, A1, [c1.mem(a, 'CC'), c1.mem(e, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (X1, a, e))
    # factor facts
    AA_, AE, AT, AR, AC, AX = ['( abs ` %s )' % x for x in (a, e, nt, RT, cn, nx)]
    for x, xx in ((a, AA_), (e, AE), (nt, AT), (RT, AR), (cn, AC), (nx, AX)):
        c1.leaf(xx, 'RR', dst(w, A1, [c1.mem(x, 'CC')], 'abscld', '%s e. RR' % xx)); c1.leaf(xx, 'ge0', dst(w, A1, [c1.mem(x, 'CC')], 'absge0d', '0 <_ %s' % xx))
    fa = lift(w, tau, A1)
    fe = dst(w, A1, [dst(w, A1, [c1.mem(e, 'RR'), c1.ge0(e)], 'absidd', '%s = %s' % (AE, e)),
                     dst(w, A1, [linarith(w, A1, [c1.ge0('( N / %s )' % YP)], '( -u N / %s ) <_ 0' % YP, closure=c1) if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    # e <_ 1
    ndiv = eqc(w, A1, dst(w, A1, [c1.mem('N', 'CC'), c1.mem(YP, 'CC'), c1.ne0(YP)], 'divnegd', '-u ( N / %s ) = ( -u N / %s )' % (YP, YP)))
    c1.leaf('( N / %s )' % YP, 'RR', c1.mem('( N / %s )' % YP, 'RR')); c1.leaf('( N / %s )' % YP, 'ge0', c1.ge0('( N / %s )' % YP))
    exl = dst(w, A1, [linarith(w, A1, [ndiv, c1.ge0('( N / %s )' % YP)], '( -u N / %s ) <_ 0' % YP, closure=c1), ap(w, A1, 'efle', [c1.mem('( -u N / %s )' % YP, 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % A1)], '( ( -u N / %s ) <_ 0 <-> %s <_ ( exp ` 0 ) )' % (YP, e))], 'mpbid', '%s <_ ( exp ` 0 )' % e)
    fe1 = dst(w, A1, [exl, a1(w, A1, 'ef0', '( exp ` 0 ) = 1')], 'breqtrd', '%s <_ 1' % e)
    fe = dst(w, A1, [dst(w, A1, [c1.mem(e, 'RR'), c1.ge0(e)], 'absidd', '%s = %s' % (AE, e)), fe1], 'eqbrtrd', '%s <_ 1' % AE)
    # nt <_ nbt : ( N / NBJ ) ^c -u T <_ 1
    QN = '( N / %s )' % NBJ
    qge1 = dst(w, A1, [w.s([], '1red', '( %s -> 1 e. RR )' % A1), c1.mem(QN, 'RR'), dst(w, A1, [dst(w, A1, [dst(w, A1, [c1.mem(NBJ, 'CC'), c1.ne0(NBJ)], 'dividd', '( %s / %s ) = 1' % (NBJ, NBJ))], 'eqcomd', '1 = ( %s / %s )' % (NBJ, NBJ)),
                                                                                                dst(w, A1, [lt1, ap(w, A1, 'ltdiv1', [c1.mem(NBJ, 'RR'), c1.mem('N', 'RR'), J(w, A1, c1.mem(NBJ, 'RR'), c1.gt0(NBJ))], '( %s < N <-> ( %s / %s ) < %s )' % (NBJ, NBJ, NBJ, QN))], 'mpbid', '( %s / %s ) < %s' % (NBJ, NBJ, QN))], 'eqbrtrd', '1 < %s' % QN)], 'ltled', '1 <_ %s' % QN)
    dc = ap(w, A1, 'divcxp', [J(w, A1, c1.mem('N', 'RR'), c1.ge0('N')), c1.mem(NBJ, 'RR+'), c1.mem('-u T', 'CC')], '( %s ^c -u T ) = ( %s / %s )' % (QN, nt, nbt))
    cx = ap(w, A1, 'cxplea', [J(w, A1, c1.mem(QN, 'RR'), qge1), J(w, A1, c1.mem('-u T', 'RR'), w.s([], '0red', '( %s -> 0 e. RR )' % A1)), linarith(w, A1, [lift(w, t0, A1)], '-u T <_ 0', closure=c1)], '( %s ^c -u T ) <_ ( %s ^c 0 )' % (QN, QN))
    q01 = dst(w, A1, [cx, ap(w, A1, 'cxp0', [c1.mem(QN, 'CC')], '( %s ^c 0 ) = 1' % QN)], 'breqtrd', '( %s ^c -u T ) <_ 1' % QN)
    ldm = ap(w, A1, 'ledivmul', [c1.mem(nt, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % A1), J(w, A1, c1.mem(nbt, 'RR'), c1.gt0(nbt))], '( ( %s / %s ) <_ 1 <-> %s <_ ( %s x. 1 ) )' % (nt, nbt, nt, nbt))
    ntle = dst(w, A1, [dst(w, A1, [dst(w, A1, [dc, q01], 'eqbrtrrd', '( %s / %s ) <_ 1' % (nt, nbt)), ldm], 'mpbid', '%s <_ ( %s x. 1 )' % (nt, nbt)), dst(w, A1, [c1.mem(nbt, 'CC')], 'mulridd', '( %s x. 1 ) = %s' % (nbt, nbt))], 'breqtrd', '%s <_ %s' % (nt, nbt))
    ft = dst(w, A1, [dst(w, A1, [c1.mem(nt, 'RR'), c1.ge0(nt)], 'absidd', '%s = %s' % (AT, nt)), ntle], 'eqbrtrd', '%s <_ %s' % (AT, nbt))
    # RT bound
    d0 = linarith(w, A1, [lift(w, tle, A1)], '0 <_ %s' % DELTA, closure=c1); d1 = linarith(w, A1, [lift(w, rle, A1)], '%s <_ ( ; 1 1 / ; 5 0 )' % DELTA, closure=c1)
    fr = ap(w, A1, 'ld1tremabs', [J(w, A1, J(w, A1, c1.mem(DELTA, 'RR'), d0, d1), J(w, A1, c1.mem(NBJ, 'RR+'), J(w, A1, c1.mem('N', 'NN'), lt1, le2b)), J(w, A1, c1.mem(JPAR, 'NN0'), lift(w, j3, A1)))], '%s <_ %s' % (AR, FF))
    cg, _ = w.wcongr('( abs ` ( C ` j ) ) <_ 1', {'j': 'N'}, 'j = N', {'j': w.s([], 'id', '( j = N -> j = N )')})
    fc = w.s([cg, lift(w, F['cb'], A1), lift(w, nn, A1)], 'rspcdva', '( %s -> %s <_ 1 )' % (A1, AC))
    fx = ap(w, A1, 'absefi', [c1.mem('( -u ( log ` N ) x. %s )' % IM, 'RR')], '%s = 1' % AX)
    # multiply: ( ( ( ( AA AE ) AT ) AR ) AC ) AX <_ ( ( ( ( TAU 1 ) nbt ) FF ) 1 ) 1
    c1.leaf(FF, 'RR', c1.mem(FF, 'RR')); c1.leaf(FF, 'ge0', c1.ge0(FF)); c1.leaf(nbt, 'RR', c1.mem(nbt, 'RR')); c1.leaf(nbt, 'ge0', c1.ge0(nbt))
    def mul(st1, st2):
        X_, _, Y_ = _lhs_rhs(body(w, st1, A1)); U_, _, V_ = _lhs_rhs(body(w, st2, A1))
        return dst(w, A1, [c1.mem(X_, 'RR'), c1.mem(Y_, 'RR'), c1.mem(U_, 'RR'), c1.mem(V_, 'RR'), c1.ge0(X_), c1.ge0(U_), st1, st2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (X_, U_, Y_, V_))
    b1 = mul(fa, fe); b2 = mul(b1, ft); b3 = mul(b2, fr); b4 = mul(b3, fc)
    fx1 = dst(w, A1, [fx], 'eqled' if False else 'x', 'x') if False else dst(w, A1, [c1.mem(AX, 'RR'), fx], 'eqled', '%s <_ 1' % AX)
    b5 = mul(b4, fx1)
    lhs = eqt(w, A1, m1, dst(w, A1, [eqt(w, A1, m2, dst(w, A1, [eqt(w, A1, m3, dst(w, A1, [eqt(w, A1, m4, dst(w, A1, [m5], 'oveq1d', '( ( abs ` %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (X1, AT, AA_, AE, AT)))], 'oveq1d',
                                                                                             '( ( abs ` %s ) x. %s ) = ( ( ( %s x. %s ) x. %s ) x. %s )' % (X2, AR, AA_, AE, AT, AR)))], 'oveq1d',
                                                              '( ( abs ` %s ) x. %s ) = ( ( ( ( %s x. %s ) x. %s ) x. %s ) x. %s )' % (X3, AC, AA_, AE, AT, AR, AC)))], 'oveq1d',
                                   '( ( abs ` %s ) x. %s ) = ( ( ( ( ( %s x. %s ) x. %s ) x. %s ) x. %s ) x. %s )' % (X4, AX, AA_, AE, AT, AR, AC, AX)))
    rgt = ringeq(w, A1, '( ( ( ( ( %s x. 1 ) x. %s ) x. %s ) x. 1 ) x. 1 )' % (TAU('N'), nbt, FF), '( ( %s x. %s ) x. %s )' % (FF, nbt, TAU('N')), c1)
    bnd = dst(w, A1, [lhs, dst(w, A1, [b5, rgt], 'breqtrd', '( ( ( ( ( %s x. %s ) x. %s ) x. %s ) x. %s ) x. %s ) <_ ( ( %s x. %s ) x. %s )' % (AA_, AE, AT, AR, AC, AX, FF, nbt, TAU('N')))], 'eqbrtrd',
              '( abs ` %s ) <_ ( ( %s x. %s ) x. %s )' % (RBODY('J', 'N'), FF, nbt, TAU('N')))
    case1 = dst(w, A1, [dst(w, A1, [tv], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (REMTERM('J', 'N'), RBODY('J', 'N'))), dst(w, A1, [bnd, eqc(w, A1, rv)], 'breqtrd', '( abs ` %s ) <_ %s' % (RBODY('J', 'N'), RHS))], 'eqbrtrd', '( abs ` %s ) <_ %s' % (REMTERM('J', 'N'), RHS))
    # off the block
    A2 = '( %s /\\ -. %s )' % (A, BLKC('J', 'N'))
    c2 = liftcl(w, None, A2, basefacts(F) + [('T', 'RR', tr), ('J', 'NN0', jn), ('N', 'NN', nn), (TAU('N'), 'RR', c.mem(TAU('N'), 'RR')), (TAU('N'), 'ge0', c.ge0(TAU('N')))])
    z = dst(w, A2, [dst(w, A2, [dst(w, A2, [w.s([], 'simpr', '( %s -> -. %s )' % (A2, BLKC('J', 'N')))], 'iffalsed', '%s = 0' % REMTERM('J', 'N'))], 'fveq2d', '( abs ` %s ) = ( abs ` 0 )' % REMTERM('J', 'N')), a1(w, A2, 'abs0', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` %s ) = 0' % REMTERM('J', 'N'))
    # 0 <_ RHS
    B1 = '( %s /\\ N <_ %s )' % (A2, FL); B2 = '( %s /\\ -. N <_ %s )' % (A2, FL)
    c2b = liftcl(w, None, B1, basefacts(F) + [('T', 'RR', tr), ('J', 'NN0', jn), (TAU('N'), 'RR', c.mem(TAU('N'), 'RR')), (TAU('N'), 'ge0', c.ge0(TAU('N')))])
    g1 = dst(w, B1, [dst(w, B1, [w.s([], 'simpr', '( %s -> N <_ %s )' % (B1, FL))], 'iftrued', '%s = ( ( %s x. %s ) x. %s )' % (RHS, FF, nbt, TAU('N'))), c2b.ge0('( ( %s x. %s ) x. %s )' % (FF, nbt, TAU('N')))], 'eqbrtrrd' if False else 'x', 'x') if False else None
    g1 = dst(w, B1, [dst(w, B1, [dst(w, B1, [w.s([], 'simpr', '( %s -> N <_ %s )' % (B1, FL))], 'iftrued', '%s = ( ( %s x. %s ) x. %s )' % (RHS, FF, nbt, TAU('N')))], 'eqcomd', '( ( %s x. %s ) x. %s ) = %s' % (FF, nbt, TAU('N'), RHS)), c2b.ge0('( ( %s x. %s ) x. %s )' % (FF, nbt, TAU('N')))], 'x', 'x') if False else None
    ge_ = c2b.ge0('( ( %s x. %s ) x. %s )' % (FF, nbt, TAU('N')))
    ift = dst(w, B1, [w.s([], 'simpr', '( %s -> N <_ %s )' % (B1, FL))], 'iftrued', '%s = ( ( %s x. %s ) x. %s )' % (RHS, FF, nbt, TAU('N')))
    g1 = dst(w, B1, [ge_, ift], 'breqtrrd', '0 <_ %s' % RHS)
    iff = dst(w, B2, [w.s([], 'simpr', '( %s -> -. N <_ %s )' % (B2, FL))], 'iffalsed', '%s = 0' % RHS)
    g2 = dst(w, B2, [a1(w, B2, '0le0', '0 <_ 0'), iff], 'breqtrrd', '0 <_ %s' % RHS)
    g = dst(w, A2, [g1, g2], 'pm2.61dan', '0 <_ %s' % RHS)
    case2 = dst(w, A2, [z, g], 'eqbrtrd', '( abs ` %s ) <_ %s' % (REMTERM('J', 'N'), RHS))
    dst(w, A, [case1, case2], 'pm2.61dan', '( abs ` %s ) <_ %s' % (REMTERM('J', 'N'), RHS))
    return fin(w)


def ld1twoj():
    w = W('ld1twoj', 'For ` j < J ` : ` 2 ^ j <_ D ^ ( 7 / 10 ) ` and ` 2 ^ j D <_ D ^ ( 17 / 10 ) ` (~ log2ub , ~ cxpefd , ~ cxpp1d ).')
    A = ante('ld1twoj'); P = parts(w, A); c, F = basecl(w, A, P)
    jn, jlt = P['J e. NN0'], P['J < %s' % JPAR]
    c.leaf('J', 'NN0', jn)
    jp = ap(w, A, 'ld1jpar', [F['hz']], concl('ld1jpar'))
    jle = dst(w, A, [dst(w, A, [jp], 'simprd', '( %s <_ %s /\\ %s <_ ( %s + 1 ) /\\ %s <_ ( 2 x. %s ) )' % (L, JPAR, JPAR, L, JPAR, L))], 'simp2d', '%s <_ ( %s + 1 )' % (JPAR, L))
    jp1 = dst(w, A, [jlt, ap(w, A, 'nn0ltp1le', [jn, c.mem(JPAR, 'NN0')], '( J < %s <-> ( J + 1 ) <_ %s )' % (JPAR, JPAR))], 'mpbid', '( J + 1 ) <_ %s' % JPAR)
    jL = linarith(w, A, [jp1, jle], 'J <_ %s' % L, closure=c)
    two = dst(w, A, [a1(w, A, '2rp', '2 e. RR+')], 'relogcld', '%s e. RR' % L2); c.leaf(L2, 'RR', two)
    l2u = w.s([w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % L2)], 'a1i', '( %s -> %s < ( ; ; 2 5 3 / ; ; 3 6 5 ) )' % (A, L2))
    l2g = w.s([w.s([], 'log2ge', '( 1 / 2 ) <_ %s' % L2)], 'a1i', '( %s -> ( 1 / 2 ) <_ %s )' % (A, L2))
    x1 = ap(w, A, 'cxpexp', [c.mem('2', 'CC'), jn], '( 2 ^c J ) = ( 2 ^ J )')
    x2 = dst(w, A, [c.mem('2', 'CC'), c.ne0('2'), c.mem('J', 'CC')], 'cxpefd', '( 2 ^c J ) = ( exp ` ( J x. %s ) )' % L2)
    C7 = '( 7 / ; 1 0 )'
    x3 = dst(w, A, [c.mem('D', 'CC'), c.ne0('D'), c.mem(C7, 'CC')], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (C7, C7, L))
    l0 = linarith(w, A, [F['dl']], '0 <_ %s' % L, closure=c); c.leaf(L, 'ge0', l0)
    m1 = lemul(w, A, c, jL, L2, side=1)                                                     # J log2 <_ L log2
    m2 = lemul(w, A, c, ltle(w, A, c, l2u), L)                                              # L log2 <_ L (253/365)
    e1 = linarith(w, A, [m1, m2, l0], '( J x. %s ) <_ ( %s x. %s )' % (L2, C7, L), closure=c)
    efl = ap(w, A, 'efle', [c.mem('( J x. %s )' % L2, 'RR'), c.mem('( %s x. %s )' % (C7, L), 'RR')], '( ( J x. %s ) <_ ( %s x. %s ) <-> ( exp ` ( J x. %s ) ) <_ ( exp ` ( %s x. %s ) ) )' % (L2, C7, L, L2, C7, L))
    e2 = dst(w, A, [e1, efl], 'mpbid', '( exp ` ( J x. %s ) ) <_ ( exp ` ( %s x. %s ) )' % (L2, C7, L))
    h1 = dst(w, A, [eqt(w, A, eqc(w, A, x1), x2), dst(w, A, [e2, eqc(w, A, x3)], 'breqtrd', '( exp ` ( J x. %s ) ) <_ ( D ^c %s )' % (L2, C7))], 'eqbrtrd', '( 2 ^ J ) <_ ( D ^c %s )' % C7)
    p1 = dst(w, A, [c.mem('D', 'CC'), c.ne0('D'), c.mem(C7, 'CC')], 'cxpp1d', '( D ^c ( %s + 1 ) ) = ( ( D ^c %s ) x. D )' % (C7, C7))
    ee = ringeq(w, A, '( %s + 1 )' % C7, '( ; 1 7 / ; 1 0 )', c)
    h2 = dst(w, A, [lemul(w, A, c, h1, 'D', side=1), eqt(w, A, eqc(w, A, p1), dst(w, A, [ee], 'oveq2d', '( D ^c ( %s + 1 ) ) = ( D ^c ( ; 1 7 / ; 1 0 ) )' % C7))], 'breqtrd', '%s <_ ( D ^c ( ; 1 7 / ; 1 0 ) )' % NB('J'))
    J(w, A, h1, h2)
    return fin(w)


def ld1fifth():
    w = W('ld1fifth', '` ( 1 / 5 ) ^ ( J + 1 ) <_ D ^ -u ( 112 / 81 ) ` from ` 5 ^ ( J + 1 ) >_ 4 ^ log D = D ^ log 4 ` and ` log 4 >_ 112 / 81 ` (~ z5dlog2 , ~ exprec , ~ cxpneg ).')
    A = HZH; P = parts(w, A); c, F = basecl(w, A, P)
    M = '( %s + 1 )' % JPAR
    mn = ap(w, A, 'peano2nn', [F['jn']], '%s e. NN' % M)
    EX = '( ; ; 1 1 2 / ; 8 1 )'
    er = ap(w, A, 'exprec', [c.mem('5', 'CC'), c.ne0('5'), c.mem(M, 'ZZ')], '( ( 1 / 5 ) ^ %s ) = ( 1 / ( 5 ^ %s ) )' % (M, M))
    cn = ap(w, A, 'cxpneg', [c.mem('D', 'CC'), c.ne0('D'), c.mem(EX, 'CC')], '( D ^c -u %s ) = ( 1 / ( D ^c %s ) )' % (EX, EX))
    # D ^c EX <_ 5 ^ M
    two = dst(w, A, [a1(w, A, '2rp', '2 e. RR+')], 'relogcld', '%s e. RR' % L2); c.leaf(L2, 'RR', two)
    l2g = w.s([w.s([], 'z5dlog2', '( ; 5 6 / ; 8 1 ) <_ %s' % L2)], 'a1i', '( %s -> ( ; 5 6 / ; 8 1 ) <_ %s )' % (A, L2))
    L4 = '( log ` 4 )'
    l4 = eqt(w, A, dst(w, A, [dst(w, A, [a1(w, A, 'sq2', '( 2 ^ 2 ) = 4')], 'eqcomd', '4 = ( 2 ^ 2 )')], 'fveq2d', '%s = ( log ` ( 2 ^ 2 ) )' % L4), ap(w, A, 'relogexp', [a1(w, A, '2rp', '2 e. RR+'), a1(w, A, '2z', '2 e. ZZ')], '( log ` ( 2 ^ 2 ) ) = ( 2 x. %s )' % L2))
    c.leaf(L4, 'RR', dst(w, A, [l4, c.mem('( 2 x. %s )' % L2, 'RR')], 'eqeltrd', '%s e. RR' % L4))
    exle = linarith(w, A, [l2g, l4], '%s <_ %s' % (EX, L4), closure=c)
    d1le = ltle(w, A, c, F['d1'])
    cx1 = ap(w, A, 'cxplea', [J(w, A, F['dr'], d1le), J(w, A, c.mem(EX, 'RR'), c.mem(L4, 'RR')), exle], '( D ^c %s ) <_ ( D ^c %s )' % (EX, L4))
    x1 = dst(w, A, [c.mem('D', 'CC'), c.ne0('D'), c.mem(L4, 'CC')], 'cxpefd', '( D ^c %s ) = ( exp ` ( %s x. %s ) )' % (L4, L4, L))
    x2 = dst(w, A, [c.mem('4', 'CC'), c.ne0('4'), c.mem(L, 'CC')], 'cxpefd', '( 4 ^c %s ) = ( exp ` ( %s x. %s ) )' % (L, L, L4))
    cm = dst(w, A, [c.mem(L4, 'CC'), c.mem(L, 'CC')], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (L4, L, L, L4))
    dl4 = eqt(w, A, eqt(w, A, x1, dst(w, A, [cm], 'fveq2d', '( exp ` ( %s x. %s ) ) = ( exp ` ( %s x. %s ) )' % (L4, L, L, L4))), eqc(w, A, x2))   # D^L4 = 4^L
    jp = ap(w, A, 'ld1jpar', [F['hz']], concl('ld1jpar'))
    lj = dst(w, A, [dst(w, A, [jp], 'simprd', '( %s <_ %s /\\ %s <_ ( %s + 1 ) /\\ %s <_ ( 2 x. %s ) )' % (L, JPAR, JPAR, L, JPAR, L))], 'simp1d', '%s <_ %s' % (L, JPAR))
    lm = linarith(w, A, [lj], '%s <_ %s' % (L, M), closure=c)
    cx2 = ap(w, A, 'cxplea', [J(w, A, c.mem('4', 'RR'), w.s([num.le_lit(w, '1', '4')], 'a1i', '( %s -> 1 <_ 4 )' % A)), J(w, A, F['lr'], c.mem(M, 'RR')), lm], '( 4 ^c %s ) <_ ( 4 ^c %s )' % (L, M))
    x3 = ap(w, A, 'cxpexp', [c.mem('4', 'CC'), c.mem(M, 'NN0')], '( 4 ^c %s ) = ( 4 ^ %s )' % (M, M))
    p45 = ap(w, A, 'leexp1a', [J(w, A, c.mem('4', 'RR'), c.mem('5', 'RR'), c.mem(M, 'NN0')), J(w, A, c.ge0('4'), w.s([num.le_lit(w, '4', '5')], 'a1i', '( %s -> 4 <_ 5 )' % A))], '( 4 ^ %s ) <_ ( 5 ^ %s )' % (M, M))
    for e_ in ('( D ^c %s )' % EX, '( D ^c %s )' % L4, '( 4 ^c %s )' % L, '( 4 ^c %s )' % M, '( 4 ^ %s )' % M, '( 5 ^ %s )' % M):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    ch = linarith(w, A, [cx1, dl4, cx2, x3, p45], '( D ^c %s ) <_ ( 5 ^ %s )' % (EX, M), closure=c)
    lr = ap(w, A, 'lerec', [J(w, A, c.mem('( D ^c %s )' % EX, 'RR'), c.gt0('( D ^c %s )' % EX)), J(w, A, c.mem('( 5 ^ %s )' % M, 'RR'), c.gt0('( 5 ^ %s )' % M))],
            '( ( D ^c %s ) <_ ( 5 ^ %s ) <-> ( 1 / ( 5 ^ %s ) ) <_ ( 1 / ( D ^c %s ) ) )' % (EX, M, M, EX))
    fin_ = dst(w, A, [ch, lr], 'mpbid', '( 1 / ( 5 ^ %s ) ) <_ ( 1 / ( D ^c %s ) )' % (M, EX))
    dst(w, A, [er, dst(w, A, [fin_, cn], 'breqtrrd', '( 1 / ( 5 ^ %s ) ) <_ ( D ^c -u %s )' % (M, EX))], 'eqbrtrd', '%s <_ ( D ^c -u %s )' % (FIFTH(JPAR), EX))
    return fin(w)


def ld1remn():
    w = W('ld1remn', 'Lean ` rem_numeric ` : ` ( 1 / 5 ) ^ ( J + 1 ) N_j ^ -u sigma 2 N_j ( 1 + log 2 N_j ) <_ 1 / ( 8 J ) ` for ` j < J ` , ` 3 / 4 <_ sigma <_ 1 ` (~ ld1twoj , ~ ld1fifth , ~ ld1ntay , ~ cxpp1d , ~ cxple2 ).')
    A = ante('ld1remn'); P = parts(w, A); c, F = basecl(w, A, P)
    jn, jlt, tr, t34, t1 = P['J e. NN0'], P['J < %s' % JPAR], P['T e. RR'], P['( 3 / 4 ) <_ T'], P['T <_ 1']
    c.leaf('J', 'NN0', jn); c.leaf('T', 'RR', tr)
    NBJ = NB('J'); nbt = '( %s ^c -u T )' % NBJ; NB2 = '( 2 x. %s )' % NBJ; LG = '( 1 + ( log ` %s ) )' % NB2
    FF = FIFTH(JPAR)
    tj = ap(w, A, 'ld1twoj', [J(w, A, F['hz'], J(w, A, jn, jlt))], concl('ld1twoj'))
    nble = dst(w, A, [tj], 'simprd', '%s <_ ( D ^c ( ; 1 7 / ; 1 0 ) )' % NBJ)
    D17 = '( D ^c ( ; 1 7 / ; 1 0 ) )'; P_ = '( D ^c ( ; 1 7 / ; 4 0 ) )'; Q_ = '( D ^c -u ( ; ; 1 1 2 / ; 8 1 ) )'
    # (b) nbt NBJ = NBJ ^c ( 1 - T ) <_ NBJ ^c ( 1 / 4 ) <_ D17 ^c ( 1 / 4 ) = P_
    pp = dst(w, A, [c.mem(NBJ, 'CC'), c.ne0(NBJ), c.mem('-u T', 'CC')], 'cxpp1d', '( %s ^c ( -u T + 1 ) ) = ( %s x. %s )' % (NBJ, nbt, NBJ))
    e1 = ringeq(w, A, '( -u T + 1 )', '( 1 - T )', c)
    b0 = eqt(w, A, eqc(w, A, pp), dst(w, A, [e1], 'oveq2d', '( %s ^c ( -u T + 1 ) ) = ( %s ^c ( 1 - T ) )' % (NBJ, NBJ)))
    nb1 = ap(w, A, 'expge1', [J(w, A, c.mem('2', 'RR'), jn, w.s([num.le_lit(w, '1', '2')], 'a1i', '( %s -> 1 <_ 2 )' % A))], '1 <_ ( 2 ^ J )')
    nbge1 = nlinarith(w, A, [nb1, F['d1']], '1 <_ %s' % NBJ, closure=c)
    cx1 = ap(w, A, 'cxplea', [J(w, A, c.mem(NBJ, 'RR'), nbge1), J(w, A, c.mem('( 1 - T )', 'RR'), c.mem('( 1 / 4 )', 'RR')), linarith(w, A, [t34], '( 1 - T ) <_ ( 1 / 4 )', closure=c)], '( %s ^c ( 1 - T ) ) <_ ( %s ^c ( 1 / 4 ) )' % (NBJ, NBJ))
    cx2 = dst(w, A, [nble, ap(w, A, 'cxple2', [J(w, A, c.mem(NBJ, 'RR'), c.ge0(NBJ)), J(w, A, c.mem(D17, 'RR'), c.ge0(D17)), c.mem('( 1 / 4 )', 'RR+')], '( %s <_ %s <-> ( %s ^c ( 1 / 4 ) ) <_ ( %s ^c ( 1 / 4 ) ) )' % (NBJ, D17, NBJ, D17))], 'mpbid', '( %s ^c ( 1 / 4 ) ) <_ ( %s ^c ( 1 / 4 ) )' % (NBJ, D17))
    cm = eqc(w, A, dst(w, A, [F['rp'], c.mem('( ; 1 7 / ; 1 0 )', 'RR'), c.mem('( 1 / 4 )', 'CC')], 'cxpmuld', '( D ^c ( ( ; 1 7 / ; 1 0 ) x. ( 1 / 4 ) ) ) = ( %s ^c ( 1 / 4 ) )' % D17))
    e2 = ringeq(w, A, '( ( ; 1 7 / ; 1 0 ) x. ( 1 / 4 ) )', '( ; 1 7 / ; 4 0 )', c)
    d17 = eqt(w, A, cm, dst(w, A, [e2], 'oveq2d', '( D ^c ( ( ; 1 7 / ; 1 0 ) x. ( 1 / 4 ) ) ) = %s' % P_))
    for e_ in ('( %s ^c ( 1 - T ) )' % NBJ, '( %s ^c ( 1 / 4 ) )' % NBJ, '( %s ^c ( 1 / 4 ) )' % D17, P_, Q_, nbt, NBJ, D17):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    hb = linarith(w, A, [b0, cx1, cx2, d17], '( %s x. %s ) <_ %s' % (nbt, NBJ, P_), closure=c)
    # (c) 1 + log ( 2 NBJ ) <_ 2 L
    lm = dst(w, A, [a1(w, A, '2rp', '2 e. RR+'), c.mem(NBJ, 'RR+')], 'relogmuld', '( log ` %s ) = ( %s + ( log ` %s ) )' % (NB2, L2, NBJ))
    ll = dst(w, A, [nble, dst(w, A, [c.mem(NBJ, 'RR+'), c.mem(D17, 'RR+')], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (NBJ, D17, NBJ, D17))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (NBJ, D17))
    lc = dst(w, A, [F['rp'], c.mem('( ; 1 7 / ; 1 0 )', 'RR')], 'logcxpd', '( log ` %s ) = ( ( ; 1 7 / ; 1 0 ) x. %s )' % (D17, L))
    two = dst(w, A, [a1(w, A, '2rp', '2 e. RR+')], 'relogcld', '%s e. RR' % L2); c.leaf(L2, 'RR', two)
    l21 = w.s([w.s([], 'log2le1', '%s < 1' % L2)], 'a1i', '( %s -> %s < 1 )' % (A, L2))
    for e_ in ('( log ` %s )' % NB2, '( log ` %s )' % NBJ, '( log ` %s )' % D17):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    hc = linarith(w, A, [lm, ll, lc, l21, F['dl']], '%s <_ ( 2 x. %s )' % (LG, L), closure=c)
    lnb0 = ap(w, A, 'logge0', [J(w, A, c.mem(NBJ, 'RR'), nbge1)], '0 <_ ( log ` %s )' % NBJ)
    l2z = ap(w, A, 'logge0', [J(w, A, c.mem('2', 'RR'), w.s([num.le_lit(w, '1', '2')], 'a1i', '( %s -> 1 <_ 2 )' % A))], '0 <_ %s' % L2)
    hc0 = linarith(w, A, [lm, lnb0, l2z], '0 <_ %s' % LG, closure=c)
    # (d) FF <_ Q_
    hd = ap(w, A, 'ld1fifth', [F['hz']], concl('ld1fifth'))
    # (e) assemble: FF ( nbt ( 2 NBJ LG ) ) = FF 2 ( nbt NBJ ) LG <_ Q_ 2 P_ ( 2 L ) = 4 L ( P_ Q_ )
    LHS = '( %s x. ( %s x. ( %s x. %s ) ) )' % (FF, nbt, NB2, LG)
    rg = ringeq(w, A, LHS, '( ( 2 x. %s ) x. ( ( %s x. %s ) x. %s ) )' % (FF, nbt, NBJ, LG), c)
    c.leaf(LG, 'RR', c.mem(LG, 'RR')); c.leaf(LG, 'ge0', hc0); c.leaf(FF, 'RR', c.mem(FF, 'RR')); c.leaf(FF, 'ge0', c.ge0(FF)); c.leaf('( %s x. %s )' % (nbt, NBJ), 'RR', c.mem('( %s x. %s )' % (nbt, NBJ), 'RR')); c.leaf('( %s x. %s )' % (nbt, NBJ), 'ge0', c.ge0('( %s x. %s )' % (nbt, NBJ)))
    def mul(st1, st2):
        X_, _, Y_ = _lhs_rhs(body(w, st1, A)); U_, _, V_ = _lhs_rhs(body(w, st2, A))
        return dst(w, A, [c.mem(X_, 'RR'), c.mem(Y_, 'RR'), c.mem(U_, 'RR'), c.mem(V_, 'RR'), c.ge0(X_), c.ge0(U_), st1, st2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (X_, U_, Y_, V_))
    m1 = mul(hb, hc)                                                                       # ( nbt NBJ ) LG <_ P_ ( 2 L )
    m2 = mul(lemul(w, A, c, hd, '2'), m1)                                                  # ( 2 FF ) (( nbt NBJ ) LG ) <_ ( 2 Q_ ) ( P_ ( 2 L ) )
    # P_ Q_ = 1 / X where X = D ^c ( 3103 / 3240 ) = exp ( ( 3103 / 3240 ) L )
    C3 = '( ; ; ; 3 1 0 3 / ; ; ; 3 2 4 0 )'
    ca = ap(w, A, 'cxpaddd' if False else 'x', [], '') if False else dst(w, A, [c.mem('D', 'CC'), c.ne0('D'), c.mem('( ; 1 7 / ; 4 0 )', 'CC'), c.mem('-u ( ; ; 1 1 2 / ; 8 1 )', 'CC')], 'cxpaddd', '( D ^c ( ( ; 1 7 / ; 4 0 ) + -u ( ; ; 1 1 2 / ; 8 1 ) ) ) = ( %s x. %s )' % (P_, Q_))
    e3 = ringeq(w, A, '( ( ; 1 7 / ; 4 0 ) + -u ( ; ; 1 1 2 / ; 8 1 ) )', '-u %s' % C3, c)
    cn_ = ap(w, A, 'cxpneg', [c.mem('D', 'CC'), c.ne0('D'), c.mem(C3, 'CC')], '( D ^c -u %s ) = ( 1 / ( D ^c %s ) )' % (C3, C3))
    X_ = '( D ^c %s )' % C3
    pq = eqt(w, A, eqc(w, A, ca), eqt(w, A, dst(w, A, [e3], 'oveq2d', '( D ^c ( ( ; 1 7 / ; 4 0 ) + -u ( ; ; 1 1 2 / ; 8 1 ) ) ) = ( D ^c -u %s )' % C3), cn_))   # P_ Q_ = 1 / X_
    rg2 = ringeq(w, A, '( ( 2 x. %s ) x. ( %s x. ( 2 x. %s ) ) )' % (Q_, P_, L), '( ( 4 x. %s ) x. ( %s x. %s ) )' % (L, P_, Q_), c)
    xe = dst(w, A, [c.mem('D', 'CC'), c.ne0('D'), c.mem(C3, 'CC')], 'cxpefd', '%s = ( exp ` ( %s x. %s ) )' % (X_, C3, L))
    nt = ap(w, A, 'ld1ntay', [J(w, A, F['lr'], F['dl'])], '( ; 6 4 x. ( %s ^ 2 ) ) <_ ( exp ` ( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. %s ) )' % (L, L))
    efl = ap(w, A, 'efle', [c.mem('( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. %s )' % L, 'RR'), c.mem('( %s x. %s )' % (C3, L), 'RR')], '( ( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. %s ) <_ ( %s x. %s ) <-> ( exp ` ( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. %s ) ) <_ ( exp ` ( %s x. %s ) ) )' % (L, C3, L, L, C3, L))
    l0 = linarith(w, A, [F['dl']], '0 <_ %s' % L, closure=c); c.leaf(L, 'ge0', l0)
    ee = dst(w, A, [linarith(w, A, [l0], '( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. %s ) <_ ( %s x. %s )' % (L, C3, L), closure=c), efl], 'mpbid', '( exp ` ( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. %s ) ) <_ ( exp ` ( %s x. %s ) )' % (L, C3, L))
    jp = ap(w, A, 'ld1jpar', [F['hz']], concl('ld1jpar'))
    j2l = dst(w, A, [dst(w, A, [jp], 'simprd', '( %s <_ %s /\\ %s <_ ( %s + 1 ) /\\ %s <_ ( 2 x. %s ) )' % (L, JPAR, JPAR, L, JPAR, L))], 'simp3d', '%s <_ ( 2 x. %s )' % (JPAR, L))
    c.leaf(JPAR, 'RR', c.mem(JPAR, 'RR'))
    jl = nlinarith(w, A, [j2l, l0], '( ( 4 x. %s ) x. ( 8 x. %s ) ) <_ ( ; 6 4 x. ( %s ^ 2 ) )' % (L, JPAR, L), closure=c)
    for e_ in (X_, '( exp ` ( ( ; ; 9 5 7 / ; ; ; 1 0 0 0 ) x. %s ) )' % L, '( exp ` ( %s x. %s ) )' % (C3, L)):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    xx = linarith(w, A, [jl, nt, ee, xe], '( ( 4 x. %s ) x. ( 8 x. %s ) ) <_ %s' % (L, JPAR, X_), closure=c)
    lmd = ap(w, A, 'lemuldiv', [c.mem('( 4 x. %s )' % L, 'RR'), c.mem(X_, 'RR'), J(w, A, c.mem('( 8 x. %s )' % JPAR, 'RR'), c.gt0('( 8 x. %s )' % JPAR))], '( ( ( 4 x. %s ) x. ( 8 x. %s ) ) <_ %s <-> ( 4 x. %s ) <_ ( %s / ( 8 x. %s ) ) )' % (L, JPAR, X_, L, X_, JPAR))
    fl = dst(w, A, [xx, lmd], 'mpbid', '( 4 x. %s ) <_ ( %s / ( 8 x. %s ) )' % (L, X_, JPAR))
    # ( 4 L ) ( P_ Q_ ) = ( 4 L ) / X_ <_ 1 / ( 8 J ) :  ( 4 L ) / X_ <_ 1 / ( 8 J ) <-> 4 L <_ X_ ( 1 / ( 8 J ) )
    d1 = dst(w, A, [c.mem('( 4 x. %s )' % L, 'CC'), c.mem(X_, 'CC'), c.ne0(X_)], 'divrecd', '( ( 4 x. %s ) / %s ) = ( ( 4 x. %s ) x. ( 1 / %s ) )' % (L, X_, L, X_))
    ldm = ap(w, A, 'ledivmul', [c.mem('( 4 x. %s )' % L, 'RR'), c.mem('( 1 / ( 8 x. %s ) )' % JPAR, 'RR'), J(w, A, c.mem(X_, 'RR'), c.gt0(X_))], '( ( ( 4 x. %s ) / %s ) <_ ( 1 / ( 8 x. %s ) ) <-> ( 4 x. %s ) <_ ( %s x. ( 1 / ( 8 x. %s ) ) ) )' % (L, X_, JPAR, L, X_, JPAR))
    dr2 = dst(w, A, [c.mem(X_, 'CC'), c.mem('( 8 x. %s )' % JPAR, 'CC'), c.ne0('( 8 x. %s )' % JPAR)], 'divrecd', '( %s / ( 8 x. %s ) ) = ( %s x. ( 1 / ( 8 x. %s ) ) )' % (X_, JPAR, X_, JPAR))
    fl2 = dst(w, A, [dst(w, A, [fl, dr2], 'breqtrd', '( 4 x. %s ) <_ ( %s x. ( 1 / ( 8 x. %s ) ) )' % (L, X_, JPAR)), ldm], 'mpbird', '( ( 4 x. %s ) / %s ) <_ ( 1 / ( 8 x. %s ) )' % (L, X_, JPAR))
    fin1 = dst(w, A, [eqt(w, A, dst(w, A, [pq], 'oveq2d', '( ( 4 x. %s ) x. ( %s x. %s ) ) = ( ( 4 x. %s ) x. ( 1 / %s ) )' % (L, P_, Q_, L, X_)), eqc(w, A, d1)), fl2], 'eqbrtrd', '( ( 4 x. %s ) x. ( %s x. %s ) ) <_ ( 1 / ( 8 x. %s ) )' % (L, P_, Q_, JPAR))
    ch = dst(w, A, [m2, rg2], 'breqtrd', '( ( 2 x. %s ) x. ( ( %s x. %s ) x. %s ) ) <_ ( ( 4 x. %s ) x. ( %s x. %s ) )' % (FF, nbt, NBJ, LG, L, P_, Q_))
    c.leaf('( ( 4 x. %s ) x. ( %s x. %s ) )' % (L, P_, Q_), 'RR', c.mem('( ( 4 x. %s ) x. ( %s x. %s ) )' % (L, P_, Q_), 'RR'))
    last = dst(w, A, [c.mem('( ( 2 x. %s ) x. ( ( %s x. %s ) x. %s ) )' % (FF, nbt, NBJ, LG), 'RR'), c.mem('( ( 4 x. %s ) x. ( %s x. %s ) )' % (L, P_, Q_), 'RR'), c.mem('( 1 / ( 8 x. %s ) )' % JPAR, 'RR'), ch, fin1], 'letrd',
               '( ( 2 x. %s ) x. ( ( %s x. %s ) x. %s ) ) <_ ( 1 / ( 8 x. %s ) )' % (FF, nbt, NBJ, LG, JPAR))
    dst(w, A, [rg, last], 'eqbrtrd', '%s <_ ( 1 / ( 8 x. %s ) )' % (LHS, JPAR))
    return fin(w)


def ld1rsabs():
    w = W('ld1rsabs', 'Lean ` norm_remSum_le ` : ` abs R_j <_ 1 / ( 8 J ) ` for every block ` j < J ` (~ ld1rtabs , ~ ld1tau1 , ~ ld1remn , ~ fsumless ).')
    A = ante('ld1rsabs'); P, c, F = setupx(w, A)
    tr, t39, t1, tle, re1 = P['T e. RR'], P['( ; 3 9 / ; 5 0 ) <_ T'], P['T <_ 1'], P['T <_ ( Re ` S )'], P['( Re ` S ) <_ 1']
    jn, jlt = P['J e. NN0'], P['J < %s' % JPAR]
    h0, rp3 = hab(w, A, F)
    c.leaf('T', 'RR', tr); c.leaf('J', 'NN0', jn); c.leaf(IM, 'RR', dst(w, A, [F['sc']], 'imcld', '%s e. RR' % IM)); c.leaf('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC'))
    t0 = linarith(w, A, [t39], '0 <_ T', closure=c); c.leaf('T', 'ge0', t0)
    NBJ = NB('J'); NB2 = '( 2 x. %s )' % NBJ; FL = '( |_ ` %s )' % NB2; FF = FIFTH(JPAR); nbt = '( %s ^c -u T )' % NBJ
    CC_ = '( %s x. %s )' % (FF, nbt)
    base = basefacts(F) + [('T', 'RR', tr), ('T', 'ge0', t0), ('J', 'NN0', jn), (IM, 'RR', c.mem(IM, 'RR')), ('_i', 'CC', c.mem('_i', 'CC')), ('( Re ` S )', 'RR', F['re'])]
    An = '( %s /\\ n e. %s )' % (A, FZN)
    nN = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZN))], 'n e. NN')
    cn = liftcl(w, None, An, base); termcl(w, An, cn, 'n', nN, F, rp3)
    Ank = '( %s /\\ k e. %s )' % (An, KJ)
    cnk = ck_of(w, Ank, c, base); termcl(w, Ank, cnk, 'n', lift(w, nN, Ank), F, rp3)
    LRn = LOGR('n', NBJ); cnk.leaf(LRn, 'RR', cnk.mem(LRn, 'RR'))
    PK = TPOLY(DELTA, NBJ, JPAR, 'n')
    cn.leaf(PK, 'RR', dst(w, An, [dst(w, An, [], 'fzfid', '%s e. Fin' % KJ), cnk.mem('( ( ( %s ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % (DELTA, LRn), 'RR')], 'fsumrecl', '%s e. RR' % PK))
    rtc = cn.mem(REMTERM('J', 'n'), 'CC')
    TAUn = TAU('n')
    cn.leaf(TAUn, 'RR', dst(w, An, [ap(w, An, 'hashcl', [ap(w, An, 'dvdsfi', [nN], '%s e. Fin' % DV('n'))], '%s e. NN0' % TAUn)], 'nn0red', '%s e. RR' % TAUn))
    cn.leaf(TAUn, 'ge0', dst(w, An, [ap(w, An, 'hashcl', [ap(w, An, 'dvdsfi', [nN], '%s e. Fin' % DV('n'))], '%s e. NN0' % TAUn)], 'nn0ge0d', '0 <_ %s' % TAUn))
    rle2 = linarith(w, A, [re1, t39], '( Re ` S ) <_ ( T + ( ; 1 1 / ; 5 0 ) )', closure=c)
    IFn = 'if ( n <_ %s , ( %s x. %s ) , 0 )' % (FL, CC_, TAUn)
    pt = ap(w, An, 'ld1rtabs', [J(w, An, J(w, An, lift(w, F['hz'], An), lift(w, P[CFN], An)), J(w, An, J(w, An, lift(w, F['sc'], An), lift(w, tr, An)), J(w, An, J(w, An, lift(w, t0, An), lift(w, tle, An)), lift(w, rle2, An))), J(w, An, lift(w, jn, An), nN))],
            '( abs ` %s ) <_ %s' % (REMTERM('J', 'n'), IFn))
    fi = dst(w, A, [], 'fzfid', '%s e. Fin' % FZN)
    ab = dst(w, A, [fi, rtc], 'fsumabs', '( abs ` %s ) <_ sum_ n e. %s ( abs ` %s )' % (REMSUM('J'), FZN, REMTERM('J', 'n')))
    le1 = dst(w, A, [fi, dst(w, An, [rtc], 'abscld', '( abs ` %s ) e. RR' % REMTERM('J', 'n')), cn.mem(IFn, 'RR'), pt], 'fsumle', 'sum_ n e. %s ( abs ` %s ) <_ sum_ n e. %s %s' % (FZN, REMTERM('J', 'n'), FZN, IFn))
    # sum_ FZN IFn = sum_ ( FZN i^i ( 1 ... FL ) ) CC_ TAU <_ sum_ ( 1 ... FL ) CC_ TAU
    FZ2 = '( 1 ... %s )' % FL; I = '( %s i^i %s )' % (FZN, FZ2)
    flz = ap(w, A, 'flcl' if False else 'x', [], '') if False else dst(w, A, [c.mem(NB2, 'RR')], 'flcld', '%s e. ZZ' % FL)
    AI = '( %s /\\ n e. %s )' % (A, I)
    nI = w.s([], 'simpr', '( %s -> n e. %s )' % (AI, I))
    nI1 = ap(w, AI, 'elinel1', [nI], 'n e. %s' % FZN); nI2 = ap(w, AI, 'elinel2', [nI], 'n e. %s' % FZ2)
    cI = liftcl(w, None, AI, base); nNI = ap(w, AI, 'elfznn', [nI1], 'n e. NN'); cI.leaf('n', 'NN', nNI)
    cI.leaf(TAUn, 'RR', dst(w, AI, [ap(w, AI, 'hashcl', [ap(w, AI, 'dvdsfi', [nNI], '%s e. Fin' % DV('n'))], '%s e. NN0' % TAUn)], 'nn0red', '%s e. RR' % TAUn))
    Ad = '( %s /\\ n e. ( %s \\ %s ) )' % (A, FZN, I)
    nd = w.s([], 'simpr', '( %s -> n e. ( %s \\ %s ) )' % (Ad, FZN, I))
    inF = dst(w, Ad, [nd], 'eldifad', 'n e. %s' % FZN); notI = dst(w, Ad, [nd], 'eldifbd', '-. n e. %s' % I)
    na = dst(w, Ad, [notI, a1(w, Ad, 'elin', '( n e. %s <-> ( n e. %s /\\ n e. %s ) )' % (I, FZN, FZ2))], 'mtbid', '-. ( n e. %s /\\ n e. %s )' % (FZN, FZ2))
    im = dst(w, Ad, [na, a1(w, Ad, 'imnan', '( ( n e. %s -> -. n e. %s ) <-> -. ( n e. %s /\\ n e. %s ) )' % (FZN, FZ2, FZN, FZ2))], 'mpbird', '( n e. %s -> -. n e. %s )' % (FZN, FZ2))
    nf2 = dst(w, Ad, [inF, im], 'mpd', '-. n e. %s' % FZ2)
    nNd = ap(w, Ad, 'elfznn', [inF], 'n e. NN')
    el = ap(w, Ad, 'elfz', [dst(w, Ad, [nNd], 'nnzd', 'n e. ZZ'), a1(w, Ad, '1z', '1 e. ZZ'), lift(w, flz, Ad)], '( n e. %s <-> ( 1 <_ n /\\ n <_ %s ) )' % (FZ2, FL))
    na2 = dst(w, Ad, [nf2, el], 'mtbid', '-. ( 1 <_ n /\\ n <_ %s )' % FL)
    im2 = dst(w, Ad, [na2, a1(w, Ad, 'imnan', '( ( 1 <_ n -> -. n <_ %s ) <-> -. ( 1 <_ n /\\ n <_ %s ) )' % (FL, FL))], 'mpbird', '( 1 <_ n -> -. n <_ %s )' % FL)
    nle = dst(w, Ad, [dst(w, Ad, [nNd], 'nnge1d', '1 <_ n'), im2], 'mpd', '-. n <_ %s' % FL)
    zd = dst(w, Ad, [nle], 'iffalsed', '%s = 0' % IFn)
    # on I the summand is CC_ TAU
    AIt = dst(w, AI, [ap(w, AI, 'elfzle2', [nI2], 'n <_ %s' % FL)], 'iftrued', '%s = ( %s x. %s )' % (IFn, CC_, TAUn))
    ss1 = w.s([a1(w, A, 'inss1', '%s C_ %s' % (I, FZN)), cI.mem(IFn, 'CC'), zd, fi], 'fsumss', '( %s -> sum_ n e. %s %s = sum_ n e. %s %s )' % (A, I, IFn, FZN, IFn))
    e1 = eqt(w, A, eqc(w, A, ss1), dst(w, A, [AIt], 'sumeq2dv', 'sum_ n e. %s %s = sum_ n e. %s ( %s x. %s )' % (I, IFn, I, CC_, TAUn)))
    A2 = '( %s /\\ n e. %s )' % (A, FZ2)
    n2 = w.s([], 'simpr', '( %s -> n e. %s )' % (A2, FZ2)); nN2 = ap(w, A2, 'elfznn', [n2], 'n e. NN')
    c2 = liftcl(w, None, A2, base); c2.leaf('n', 'NN', nN2)
    c2.leaf(TAUn, 'RR', dst(w, A2, [ap(w, A2, 'hashcl', [ap(w, A2, 'dvdsfi', [nN2], '%s e. Fin' % DV('n'))], '%s e. NN0' % TAUn)], 'nn0red', '%s e. RR' % TAUn))
    c2.leaf(TAUn, 'ge0', dst(w, A2, [ap(w, A2, 'hashcl', [ap(w, A2, 'dvdsfi', [nN2], '%s e. Fin' % DV('n'))], '%s e. NN0' % TAUn)], 'nn0ge0d', '0 <_ %s' % TAUn))
    fless = w.s([dst(w, A, [], 'fzfid', '%s e. Fin' % FZ2), c2.mem('( %s x. %s )' % (CC_, TAUn), 'RR'), c2.ge0('( %s x. %s )' % (CC_, TAUn)), a1(w, A, 'inss2', '%s C_ %s' % (I, FZ2))], 'fsumless',
               '( %s -> sum_ n e. %s ( %s x. %s ) <_ sum_ n e. %s ( %s x. %s ) )' % (A, I, CC_, TAUn, FZ2, CC_, TAUn))
    mc = dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % FZ2), c.mem(CC_, 'CC'), c2.mem(TAUn, 'CC')], 'fsummulc2', '( %s x. sum_ n e. %s %s ) = sum_ n e. %s ( %s x. %s )' % (CC_, FZ2, TAUn, FZ2, CC_, TAUn))
    # sum_{n <_ FL} tau <_ FL ( 1 + log FL ) <_ 2 NBJ ( 1 + log 2 NBJ )
    nb1 = ap(w, A, 'expge1', [J(w, A, c.mem('2', 'RR'), jn, w.s([num.le_lit(w, '1', '2')], 'a1i', '( %s -> 1 <_ 2 )' % A))], '1 <_ ( 2 ^ J )')
    nbge1 = nlinarith(w, A, [nb1, F['d1']], '1 <_ %s' % NBJ, closure=c)
    c.leaf(FL, 'RR', dst(w, A, [flz], 'zred', '%s e. RR' % FL))
    fl1 = dst(w, A, [linarith(w, A, [nbge1], '1 <_ %s' % NB2, closure=c), ap(w, A, 'flge', [c.mem(NB2, 'RR'), a1(w, A, '1z', '1 e. ZZ')], '( 1 <_ %s <-> 1 <_ %s )' % (NB2, FL))], 'mpbid', '1 <_ %s' % FL)
    fle = ap(w, A, 'flle', [c.mem(NB2, 'RR')], '%s <_ %s' % (FL, NB2))
    tb = ap(w, A, 'ld1tau1', [J(w, A, c.mem(FL, 'RR'), fl1)], 'sum_ n e. ( 1 ... ( |_ ` %s ) ) %s <_ ( %s x. ( 1 + ( log ` %s ) ) )' % (FL, TAUn, FL, FL))
    fid = dst(w, A, [ap(w, A, 'flid', [flz], '( |_ ` %s ) = %s' % (FL, FL))], 'oveq2d', '( 1 ... ( |_ ` %s ) ) = %s' % (FL, FZ2))
    tb2 = dst(w, A, [dst(w, A, [fid], 'sumeq1d', 'sum_ n e. ( 1 ... ( |_ ` %s ) ) %s = sum_ n e. %s %s' % (FL, TAUn, FZ2, TAUn)), tb], 'eqbrtrrd', 'sum_ n e. %s %s <_ ( %s x. ( 1 + ( log ` %s ) ) )' % (FZ2, TAUn, FL, FL))
    c.leaf(FL, 'gt0', linarith(w, A, [fl1], '0 < %s' % FL, closure=c))
    lg = dst(w, A, [fle, dst(w, A, [c.mem(FL, 'RR+'), c.mem(NB2, 'RR+')], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (FL, NB2, FL, NB2))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (FL, NB2))
    lg0 = ap(w, A, 'logge0', [J(w, A, c.mem(FL, 'RR'), fl1)], '0 <_ ( log ` %s )' % FL)
    for e_ in ('( log ` %s )' % FL, '( log ` %s )' % NB2):
        c.leaf(e_, 'RR', c.mem(e_, 'RR'))
    LGF = '( 1 + ( log ` %s ) )' % FL; LG2 = '( 1 + ( log ` %s ) )' % NB2
    m1 = dst(w, A, [c.mem(FL, 'RR'), c.mem(NB2, 'RR'), c.mem(LGF, 'RR'), c.mem(LG2, 'RR'), c.ge0(FL), linarith(w, A, [lg0], '0 <_ %s' % LGF, closure=c), fle, linarith(w, A, [lg], '%s <_ %s' % (LGF, LG2), closure=c)], 'lemul12ad',
             '( %s x. %s ) <_ ( %s x. %s )' % (FL, LGF, NB2, LG2))
    c.leaf(FF, 'RR', c.mem(FF, 'RR')); c.leaf(FF, 'ge0', c.ge0(FF)); c.leaf(nbt, 'RR', c.mem(nbt, 'RR')); c.leaf(nbt, 'ge0', c.ge0(nbt))
    ST = 'sum_ n e. %s %s' % (FZ2, TAUn)
    c.leaf(ST, 'RR', dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % FZ2), c2.mem(TAUn, 'RR')], 'fsumrecl', '%s e. RR' % ST))
    t34 = linarith(w, A, [t39], '( 3 / 4 ) <_ T', closure=c)
    rn = ap(w, A, 'ld1remn', [J(w, A, F['hz'], J(w, A, jn, jlt), J(w, A, tr, t34, t1))], concl('ld1remn'))
    st1 = dst(w, A, [c.mem(ST, 'RR'), c.mem('( %s x. %s )' % (FL, LGF), 'RR'), c.mem('( %s x. %s )' % (NB2, LG2), 'RR'), tb2, m1], 'letrd', '%s <_ ( %s x. %s )' % (ST, NB2, LG2))
    st2 = lemul(w, A, c, st1, CC_)
    rg = ringeq(w, A, '( %s x. ( %s x. %s ) )' % (CC_, NB2, LG2), '( %s x. ( %s x. ( %s x. %s ) ) )' % (FF, nbt, NB2, LG2), c)
    for e_ in (REMSUM('J'),):
        c.leaf('( abs ` %s )' % e_, 'RR', dst(w, A, [dst(w, A, [fi, rtc], 'fsumcl', '%s e. CC' % e_)], 'abscld', '( abs ` %s ) e. RR' % e_))
    c.leaf('sum_ n e. %s ( abs ` %s )' % (FZN, REMTERM('J', 'n')), 'RR', dst(w, A, [fi, dst(w, An, [rtc], 'abscld', '( abs ` %s ) e. RR' % REMTERM('J', 'n'))], 'fsumrecl', 'sum_ n e. %s ( abs ` %s ) e. RR' % (FZN, REMTERM('J', 'n'))))
    c.leaf('sum_ n e. %s %s' % (FZN, IFn), 'RR', dst(w, A, [fi, cn.mem(IFn, 'RR')], 'fsumrecl', 'sum_ n e. %s %s e. RR' % (FZN, IFn)))
    for e_ in ('sum_ n e. %s ( %s x. %s )' % (I, CC_, TAUn),):
        c.leaf(e_, 'RR', dst(w, A, [dst(w, A, [a1(w, A, 'inss1', '%s C_ %s' % (I, FZN)), fi], 'ssfid', '%s e. Fin' % I), cI.mem('( %s x. %s )' % (CC_, TAUn), 'RR')], 'fsumrecl', '%s e. RR' % e_))
    c.leaf('sum_ n e. %s ( %s x. %s )' % (FZ2, CC_, TAUn), 'RR', dst(w, A, [dst(w, A, [], 'fzfid', '%s e. Fin' % FZ2), c2.mem('( %s x. %s )' % (CC_, TAUn), 'RR')], 'fsumrecl', 'sum_ n e. %s ( %s x. %s ) e. RR' % (FZ2, CC_, TAUn)))
    linarith(w, A, [ab, le1, e1, fless, mc, st2, rg, rn], '( abs ` %s ) <_ ( 1 / ( 8 x. %s ) )' % (REMSUM('J'), JPAR), closure=c, name='qed')
    return go(w)


if __name__ == '__main__':
    for lab in ['ld1blktay', 'ld1blkabs', 'ld1tremabs', 'ld1rtabs', 'ld1twoj', 'ld1fifth', 'ld1remn', 'ld1rsabs']:
        if want(lab):
            if not globals()[lab]():
                sys.exit(1)
