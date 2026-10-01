"""Sortie LD1, section 5: the pigeonholes (ld1pig ld1exblkl ld1extay).
Run: MM_DB=sorties/ld1.mm MM_ENGINE=mmatch python3 tools/gen/ld1_f.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from ld1lib import *
from ld1_d import setupx, hab, basefacts, liftcl, termcl, coeffcl, L, RJ
from ld1_e import ck_of, KJ, IM
import lin as _L
_L.MAXPOW = 8

only = sys.argv[1:]
want = lambda l: not only or l in only


def fin(w):
    qedlast(w)
    return go(w)


def ld1pig():
    w = W('ld1pig', 'The pigeonhole of ` Finset.exists_le_of_sum_le ` : if ` # A x. X <_ sum_ k e. A F ( k ) ` then some term is at least ` X ` (~ fsumlt , ~ fsumconst , ~ cbvsumv ).')
    A = ante('ld1pig'); P = parts(w, A)
    fi, ne, xr, ff, le = P['A e. Fin'], P['A =/= (/)'], P['X e. RR'], P['F : A --> RR'], P['( ( # ` A ) x. X ) <_ sum_ k e. A ( F ` k )']
    EX = 'E. k e. A X <_ ( F ` k )'
    A1 = '( %s /\\ -. %s )' % (A, EX)
    nr = dst(w, A1, [w.s([], 'simpr', '( %s -> -. %s )' % (A1, EX)), a1(w, A1, 'ralnex', '( A. k e. A -. X <_ ( F ` k ) <-> -. %s )' % EX)], 'mpbird', 'A. k e. A -. X <_ ( F ` k )')
    Aj = '( %s /\\ j e. A )' % A1
    jin = w.s([], 'simpr', '( %s -> j e. A )' % Aj)
    fj = dst(w, Aj, [lift(w, ff, Aj), jin], 'ffvelcdmd', '( F ` j ) e. RR')
    cg, _ = w.wcongr('-. X <_ ( F ` k )', {'k': 'j'}, 'k = j', {'k': w.s([], 'id', '( k = j -> k = j )')})
    nj = w.s([cg, lift(w, nr, Aj), jin], 'rspcdva', '( %s -> -. X <_ ( F ` j ) )' % Aj)
    lt = dst(w, Aj, [nj, dst(w, Aj, [fj, lift(w, xr, Aj)], 'ltnled', '( ( F ` j ) < X <-> -. X <_ ( F ` j ) )')], 'mpbird', '( F ` j ) < X')
    sl = w.s([lift(w, fi, A1), lift(w, ne, A1), fj, lift(w, xr, Aj), lt], 'fsumlt', '( %s -> sum_ j e. A ( F ` j ) < sum_ j e. A X )' % A1)
    fc = ap(w, A1, 'fsumconst', [lift(w, fi, A1), dst(w, A1, [lift(w, xr, A1)], 'recnd', 'X e. CC')], 'sum_ j e. A X = ( ( # ` A ) x. X )')
    cg2, _ = w.congr('( F ` k )', {'k': 'j'}, 'k = j', {'k': w.s([], 'id', '( k = j -> k = j )')})
    cb = w.s([cg2], 'cbvsumv', 'sum_ k e. A ( F ` k ) = sum_ j e. A ( F ` j )')
    SJ = 'sum_ j e. A ( F ` j )'; SK = 'sum_ k e. A ( F ` k )'
    sr = dst(w, A1, [lift(w, fi, A1), fj], 'fsumrecl', '%s e. RR' % SJ)
    hr = dst(w, A1, [ap(w, A1, 'hashcl', [lift(w, fi, A1)], '( # ` A ) e. NN0')], 'nn0red', '( # ` A ) e. RR')
    c1 = Closure(w, A1, {'X': ('RR', lift(w, xr, A1)), SJ: ('RR', sr), '( # ` A )': ('RR', hr)})
    c1.leaf('sum_ j e. A X', 'RR', dst(w, A1, [fc, c1.mem('( ( # ` A ) x. X )', 'RR')], 'eqeltrd', 'sum_ j e. A X e. RR'))
    le2 = dst(w, A1, [lift(w, le, A1), w.s([cb], 'a1i', '( %s -> %s = %s )' % (A1, SK, SJ))], 'breqtrd', '( ( # ` A ) x. X ) <_ %s' % SJ)
    bad = linarith(w, A1, [sl, fc, le2], '%s < %s' % (SJ, SJ), closure=c1)
    nlt = ap(w, A1, 'ltnr', [sr], '-. %s < %s' % (SJ, SJ))
    nn_ = dst(w, A, [bad, nlt], 'pm2.65da', '-. -. %s' % EX)
    dst(w, A, [nn_], 'notnotrd', EX)
    return fin(w)


def fval(w, Am, v, R, body_, vin, bodyr, FM):
    """( Am -> ( FM ` v ) = body ) for FM = ( v e. R |-> body ) at its own binder, from v e. R and body e. RR"""
    return dst(w, Am, [vin, bodyr, w.s([w.s([], 'eqid', '%s = %s' % (FM, FM))], 'fvmpt2', '( ( %s e. %s /\\ %s e. RR ) -> ( %s ` %s ) = %s )' % (v, R, body_, FM, v, body_))], 'syl2anc', '( %s ` %s ) = %s' % (FM, v, body_))


def ld1exblkl():
    w = W('ld1exblkl', 'Lean ` exists_block_large ` : ` abs S >_ 1 / 4 ` forces a block with ` abs S_j >_ 1 / ( 4 J ) ` (~ ld1sblk , ~ fsumabs , ~ ld1pig ).')
    A = ante('ld1exblkl'); P = parts(w, A)
    A0 = '( ( %s /\\ %s ) /\\ S e. CC )' % (HZH, CFN)
    big = P['( 1 / 4 ) <_ ( abs ` %s )' % TRUNC]
    P0, c, F = setupx(w, A0)
    h0, rp3 = hab(w, A0, F)
    sb = ap(w, A0, 'ld1sblk', [w.s([], 'id', '( %s -> %s )' % (A0, A0))], concl('ld1sblk'))
    Am = '( %s /\\ m e. %s )' % (A0, RJ)
    min_ = w.s([], 'simpr', '( %s -> m e. %s )' % (Am, RJ))
    cm = liftcl(w, None, Am, basefacts(F)); cm.leaf('m', 'NN0', ap(w, Am, 'elfzonn0', [min_], 'm e. NN0'))
    Amn = '( %s /\\ n e. %s )' % (Am, FZN)
    cmn = liftcl(w, None, Amn, basefacts(F)); cmn.leaf('m', 'NN0', lift(w, cm.mem('m', 'NN0'), Amn))
    termcl(w, Amn, cmn, 'n', ap(w, Amn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Amn, FZN))], 'n e. NN'), F, rp3)
    bsc = dst(w, Am, [dst(w, Am, [], 'fzfid', '%s e. Fin' % FZN), cmn.mem('if ( %s , %s , 0 )' % (BLKC('m', 'n'), BODY('n')), 'CC')], 'fsumcl', '%s e. CC' % BLKSUM('m'))
    fi = a1(w, A0, 'fzofi', '%s e. Fin' % RJ)
    ABm = '( abs ` %s )' % BLKSUM('m')
    absr = dst(w, Am, [bsc], 'abscld', '%s e. RR' % ABm)
    ABq = '( abs ` %s )' % BLKSUM('q')
    FM = '( q e. %s |-> %s )' % (RJ, ABq)
    Aq = '( %s /\\ q e. %s )' % (A0, RJ)
    qin = w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, RJ))
    cq = liftcl(w, None, Aq, basefacts(F)); cq.leaf('q', 'NN0', ap(w, Aq, 'elfzonn0', [qin], 'q e. NN0'))
    Aqn = '( %s /\\ n e. %s )' % (Aq, FZN)
    cqn = liftcl(w, None, Aqn, basefacts(F)); cqn.leaf('q', 'NN0', lift(w, cq.mem('q', 'NN0'), Aqn))
    termcl(w, Aqn, cqn, 'n', ap(w, Aqn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Aqn, FZN))], 'n e. NN'), F, rp3)
    bsq = dst(w, Aq, [dst(w, Aq, [], 'fzfid', '%s e. Fin' % FZN), cqn.mem('if ( %s , %s , 0 )' % (BLKC('q', 'n'), BODY('n')), 'CC')], 'fsumcl', '%s e. CC' % BLKSUM('q'))
    ff = dst(w, A0, [dst(w, Aq, [bsq], 'abscld', '%s e. RR' % ABq)], 'fmpttd', '%s : %s --> RR' % (FM, RJ))
    fv = fvmd(w, Am, 'q', RJ, ABq, 'm', min_, dst(w, Am, [absr], 'recnd', '%s e. CC' % ABm))
    SA = 'sum_ m e. %s %s' % (RJ, ABm)
    se = dst(w, A0, [fv], 'sumeq2dv', 'sum_ m e. %s ( %s ` m ) = %s' % (RJ, FM, SA))
    fa = dst(w, A0, [fi, bsc], 'fsumabs', '( abs ` sum_ m e. %s %s ) <_ %s' % (RJ, BLKSUM('m'), SA))
    hz = ap(w, A0, 'hashfzo0', [c.mem(JPAR, 'NN0')], '( # ` %s ) = %s' % (RJ, JPAR))
    z0 = dst(w, A0, [c.mem(JPAR, 'NN'), a1(w, A0, 'lbfzo0', '( 0 e. %s <-> %s e. NN )' % (RJ, JPAR))], 'mpbird', '0 e. %s' % RJ)
    ne = ap(w, A0, 'ne0i', [z0], '%s =/= (/)' % RJ)
    V = V4
    sar = dst(w, A0, [fi, absr], 'fsumrecl', '%s e. RR' % SA)
    asr = dst(w, A0, [dst(w, A0, [fi, bsc], 'fsumcl', 'sum_ m e. %s %s e. CC' % (RJ, BLKSUM('m')))], 'abscld', '( abs ` sum_ m e. %s %s ) e. RR' % (RJ, BLKSUM('m')))
    dv1 = dst(w, A0, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), c.mem('4', 'CC'), c.mem(JPAR, 'CC'), c.ne0('4'), c.ne0(JPAR)], 'divdiv1d', '( ( 1 / 4 ) / %s ) = ( 1 / ( 4 x. %s ) )' % (JPAR, JPAR))
    dc = dst(w, A0, [c.mem('( 1 / 4 )', 'CC'), c.mem(JPAR, 'CC'), c.ne0(JPAR)], 'divcan2d', '( %s x. ( ( 1 / 4 ) / %s ) ) = ( 1 / 4 )' % (JPAR, JPAR))
    jv = eqt(w, A0, dst(w, A0, [eqc(w, A0, dv1)], 'oveq2d', '( %s x. %s ) = ( %s x. ( ( 1 / 4 ) / %s ) )' % (JPAR, V, JPAR, JPAR)), dc)
    hv = eqt(w, A0, dst(w, A0, [hz], 'oveq1d', '( ( # ` %s ) x. %s ) = ( %s x. %s )' % (RJ, V, JPAR, V)), jv)
    vr = c.mem(V, 'RR')
    bi = dst(w, A0, [dst(w, Am, [fv], 'breq2d', '( %s <_ ( %s ` m ) <-> %s <_ %s )' % (V, FM, V, ABm))], 'rexbidva', '( E. m e. %s %s <_ ( %s ` m ) <-> E. m e. %s %s <_ %s )' % (RJ, V, FM, RJ, V, ABm))
    # under A
    ab = dst(w, A, [big, dst(w, A, [lift(w, sb, A)], 'fveq2d', '( abs ` %s ) = ( abs ` sum_ m e. %s %s )' % (TRUNC, RJ, BLKSUM('m')))], 'breqtrd', '( 1 / 4 ) <_ ( abs ` sum_ m e. %s %s )' % (RJ, BLKSUM('m')))
    cA = Closure(w, A, {V: ('RR', lift(w, vr, A)), SA: ('RR', lift(w, sar, A)), '( abs ` sum_ m e. %s %s )' % (RJ, BLKSUM('m')): ('RR', lift(w, asr, A)), JPAR: ('RR', lift(w, c.mem(JPAR, 'RR'), A))})
    pre = dst(w, A, [linarith(w, A, [lift(w, hv, A), ab, lift(w, fa, A)], '( ( # ` %s ) x. %s ) <_ %s' % (RJ, V, SA), closure=cA), eqc(w, A, lift(w, se, A))], 'breqtrd', '( ( # ` %s ) x. %s ) <_ sum_ m e. %s ( %s ` m )' % (RJ, V, RJ, FM))
    ex = ap(w, A, 'ld1pig', [J(w, A, J(w, A, lift(w, fi, A), lift(w, ne, A)), J(w, A, lift(w, vr, A), lift(w, ff, A)), pre)], 'E. m e. %s %s <_ ( %s ` m )' % (RJ, V, FM))
    dst(w, A, [ex, lift(w, bi, A)], 'mpbid', 'E. m e. %s %s <_ %s' % (RJ, V, ABm))
    return fin(w)


def ld1extay():
    w = W('ld1extay', 'Lean ` exists_taylor_index_large ` : ` abs S_j >_ 1 / ( 4 J ) ` forces a Taylor component with ` abs T_jk >_ 1 / ( 8 J ( J + 1 ) ) ` (~ ld1blkabs , ~ ld1rsabs , ~ ld1pig ).')
    A = ante('ld1extay'); P = parts(w, A)
    A0 = '( %s /\\ ( J e. NN0 /\\ J < %s ) )' % (HB, JPAR)
    big = P['%s <_ ( abs ` %s )' % (V4, BLKSUM('J'))]
    P0, c, F = setupx(w, A0)
    tr, t39, t1, tle, re1 = P0['T e. RR'], P0['( ; 3 9 / ; 5 0 ) <_ T'], P0['T <_ 1'], P0['T <_ ( Re ` S )'], P0['( Re ` S ) <_ 1']
    jn, jlt = P0['J e. NN0'], P0['J < %s' % JPAR]
    h0, rp3 = hab(w, A0, F)
    c.leaf('T', 'RR', tr); c.leaf('J', 'NN0', jn); c.leaf(IM, 'RR', dst(w, A0, [F['sc']], 'imcld', '%s e. RR' % IM)); c.leaf('_i', 'CC', a1(w, A0, 'ax-icn', '_i e. CC'))
    t0 = linarith(w, A0, [t39], '0 <_ T', closure=c)
    base = basefacts(F) + [('T', 'RR', tr), ('J', 'NN0', jn), (IM, 'RR', c.mem(IM, 'RR')), ('_i', 'CC', c.mem('_i', 'CC')), ('( Re ` S )', 'RR', F['re'])]
    ba = ap(w, A0, 'ld1blkabs', [J(w, A0, J(w, A0, F['hz'], P0[CFN]), J(w, A0, J(w, A0, F['sc'], tr), J(w, A0, J(w, A0, t0, tle), re1)), jn)], concl('ld1blkabs'))
    rs = ap(w, A0, 'ld1rsabs', [w.s([], 'id', '( %s -> %s )' % (A0, A0))], concl('ld1rsabs'))
    TK = TAYSUM('J', 'k', IM); ATK = '( abs ` %s )' % TK
    Ak = '( %s /\\ k e. %s )' % (A0, KJ)
    kin = w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, KJ))
    ck = ck_of(w, Ak, c, base)
    Akn = '( %s /\\ n e. %s )' % (Ak, FZN)
    ckn = liftcl(w, None, Akn, base); ckn.leaf('k', 'NN0', lift(w, ck.mem('k', 'NN0'), Akn))
    termcl(w, Akn, ckn, 'n', ap(w, Akn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Akn, FZN))], 'n e. NN'), F, rp3); coeffcl(w, Akn, ckn, 'n', 'k')
    tkc = dst(w, Ak, [dst(w, Ak, [], 'fzfid', '%s e. Fin' % FZN), ckn.mem(TSUMMAND('J', 'k', 'n', IM), 'CC')], 'fsumcl', '%s e. CC' % TK)
    absr = dst(w, Ak, [tkc], 'abscld', '%s e. RR' % ATK)
    TQ = TAYSUM('J', 'q', IM); ATQ = '( abs ` %s )' % TQ
    FM = '( q e. %s |-> %s )' % (KJ, ATQ)
    Aq = '( %s /\\ q e. %s )' % (A0, KJ)
    cq = liftcl(w, None, Aq, base); qn0 = ap(w, Aq, 'elfznn0', [w.s([], 'simpr', '( %s -> q e. %s )' % (Aq, KJ))], 'q e. NN0'); cq.leaf('q', 'NN0', qn0)
    Aqn = '( %s /\\ n e. %s )' % (Aq, FZN)
    cqn = liftcl(w, None, Aqn, base); cqn.leaf('q', 'NN0', lift(w, qn0, Aqn))
    termcl(w, Aqn, cqn, 'n', ap(w, Aqn, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (Aqn, FZN))], 'n e. NN'), F, rp3); coeffcl(w, Aqn, cqn, 'n', 'q')
    tqc = dst(w, Aq, [dst(w, Aq, [], 'fzfid', '%s e. Fin' % FZN), cqn.mem(TSUMMAND('J', 'q', 'n', IM), 'CC')], 'fsumcl', '%s e. CC' % TQ)
    ff = dst(w, A0, [dst(w, Aq, [tqc], 'abscld', '%s e. RR' % ATQ)], 'fmpttd', '%s : %s --> RR' % (FM, KJ))
    fv = fvmd(w, Ak, 'q', KJ, ATQ, 'k', kin, dst(w, Ak, [absr], 'recnd', '%s e. CC' % ATK))
    SAT = 'sum_ k e. %s %s' % (KJ, ATK)
    se = dst(w, A0, [fv], 'sumeq2dv', 'sum_ k e. %s ( %s ` k ) = %s' % (KJ, FM, SAT))
    fi = dst(w, A0, [], 'fzfid', '%s e. Fin' % KJ)
    jin = dst(w, A0, [c.mem(JPAR, 'NN0'), a1(w, A0, 'nn0fz0', '( %s e. NN0 <-> %s e. %s )' % (JPAR, JPAR, KJ))], 'mpbid', '%s e. %s' % (JPAR, KJ))
    ne = ap(w, A0, 'ne0i', [jin], '%s =/= (/)' % KJ)
    hc = dst(w, A0, [ap(w, A0, 'hashfz', [dst(w, A0, [c.mem(JPAR, 'NN0'), w.s([], 'nn0uz', 'NN0 = ( ZZ>= ` 0 )')], 'eleqtrdi', '%s e. ( ZZ>= ` 0 )' % JPAR)], '( # ` %s ) = ( ( %s - 0 ) + 1 )' % (KJ, JPAR)),
                    dst(w, A0, [dst(w, A0, [c.mem(JPAR, 'CC')], 'subid1d', '( %s - 0 ) = %s' % (JPAR, JPAR))], 'oveq1d', '( ( %s - 0 ) + 1 ) = ( %s + 1 )' % (JPAR, JPAR))], 'eqtrd', '( # ` %s ) = ( %s + 1 )' % (KJ, JPAR))
    V = V8
    vr = c.mem(V, 'RR')
    satst = dst(w, A0, [fi, absr], 'fsumrecl', '%s e. RR' % SAT)
    An = '( %s /\\ n e. %s )' % (A0, FZN)
    cn = liftcl(w, None, An, base); termcl(w, An, cn, 'n', ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZN))], 'n e. NN'), F, rp3)
    Ank = '( %s /\\ k e. %s )' % (An, KJ)
    cnk = ck_of(w, Ank, c, base); termcl(w, Ank, cnk, 'n', lift(w, cn.mem('n', 'NN'), Ank), F, rp3)
    LRn = LOGR('n', NB('J')); cnk.leaf(LRn, 'RR', cnk.mem(LRn, 'RR'))
    PK = TPOLY(DELTA, NB('J'), JPAR, 'n')
    cn.leaf(PK, 'RR', dst(w, An, [dst(w, An, [], 'fzfid', '%s e. Fin' % KJ), cnk.mem('( ( ( %s ^ k ) / ( ! ` k ) ) x. ( %s ^ k ) )' % (DELTA, LRn), 'RR')], 'fsumrecl', '%s e. RR' % PK))
    rsc = dst(w, A0, [dst(w, A0, [], 'fzfid', '%s e. Fin' % FZN), cn.mem(REMTERM('J', 'n'), 'CC')], 'fsumcl', '%s e. CC' % REMSUM('J'))
    AR_ = '( abs ` %s )' % REMSUM('J'); AB_ = '( abs ` %s )' % BLKSUM('J')
    arr = dst(w, A0, [rsc], 'abscld', '%s e. RR' % AR_)
    abr = dst(w, A0, [dst(w, A0, [dst(w, A0, [], 'fzfid', '%s e. Fin' % FZN), cn.mem('if ( %s , %s , 0 )' % (BLKC('J', 'n'), BODY('n')), 'CC')], 'fsumcl', '%s e. CC' % BLKSUM('J'))], 'abscld', '%s e. RR' % AB_)
    dv1 = dst(w, A0, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A0), c.mem('( 8 x. %s )' % JPAR, 'CC'), c.mem('( %s + 1 )' % JPAR, 'CC'), c.ne0('( 8 x. %s )' % JPAR), c.ne0('( %s + 1 )' % JPAR)], 'divdiv1d',
              '( ( 1 / ( 8 x. %s ) ) / ( %s + 1 ) ) = ( 1 / ( ( 8 x. %s ) x. ( %s + 1 ) ) )' % (JPAR, JPAR, JPAR, JPAR))
    dc = dst(w, A0, [c.mem('( 1 / ( 8 x. %s ) )' % JPAR, 'CC'), c.mem('( %s + 1 )' % JPAR, 'CC'), c.ne0('( %s + 1 )' % JPAR)], 'divcan2d', '( ( %s + 1 ) x. ( ( 1 / ( 8 x. %s ) ) / ( %s + 1 ) ) ) = ( 1 / ( 8 x. %s ) )' % (JPAR, JPAR, JPAR, JPAR))
    jv = eqt(w, A0, dst(w, A0, [eqc(w, A0, dv1)], 'oveq2d', '( ( %s + 1 ) x. %s ) = ( ( %s + 1 ) x. ( ( 1 / ( 8 x. %s ) ) / ( %s + 1 ) ) )' % (JPAR, V, JPAR, JPAR, JPAR)), dc)
    hv = eqt(w, A0, dst(w, A0, [hc], 'oveq1d', '( ( # ` %s ) x. %s ) = ( ( %s + 1 ) x. %s )' % (KJ, V, JPAR, V)), jv)
    X8 = '( 1 / ( 8 x. %s ) )' % JPAR
    d2 = dst(w, A0, [c.mem('2', 'CC'), c.mem('( 8 x. %s )' % JPAR, 'CC'), c.ne0('( 8 x. %s )' % JPAR)], 'divrecd', '( 2 / ( 8 x. %s ) ) = ( 2 x. %s )' % (JPAR, X8))
    e8 = ringeq(w, A0, '( 8 x. %s )' % JPAR, '( 2 x. ( 4 x. %s ) )' % JPAR, c)
    q4 = '( 4 x. %s )' % JPAR
    d4 = dst(w, A0, [c.mem('2', 'CC'), c.mem('2', 'CC'), c.mem(q4, 'CC'), c.ne0('2'), c.ne0(q4)], 'divdiv1d', '( ( 2 / 2 ) / %s ) = ( 2 / ( 2 x. %s ) )' % (q4, q4))
    d5 = dst(w, A0, [a1(w, A0, '2div2e1', '( 2 / 2 ) = 1')], 'oveq1d', '( ( 2 / 2 ) / %s ) = ( 1 / %s )' % (q4, q4))
    v4e = eqt(w, A0, eqt(w, A0, eqc(w, A0, d5), d4), eqt(w, A0, dst(w, A0, [eqc(w, A0, e8)], 'oveq2d', '( 2 / ( 2 x. %s ) ) = ( 2 / ( 8 x. %s ) )' % (q4, JPAR)), d2))
    x8r = c.mem(X8, 'RR')
    sumr = dst(w, A0, [satst, arr], 'readdcld', '( %s + %s ) e. RR' % (SAT, AR_)); sum8 = dst(w, A0, [satst, x8r], 'readdcld', '( %s + %s ) e. RR' % (SAT, X8))
    m2 = dst(w, A0, [satst, satst, arr, x8r, dst(w, A0, [satst], 'leidd', '%s <_ %s' % (SAT, SAT)), rs], 'le2addd', '( %s + %s ) <_ ( %s + %s )' % (SAT, AR_, SAT, X8))
    tw = dst(w, A0, [c.mem(X8, 'CC')], '2timesd', '( 2 x. %s ) = ( %s + %s )' % (X8, X8, X8))
    la = dst(w, A0, [x8r, satst, x8r], 'leadd1d', '( %s <_ %s <-> ( %s + %s ) <_ ( %s + %s ) )' % (X8, SAT, X8, X8, SAT, X8))
    bi = dst(w, A0, [dst(w, Ak, [fv], 'breq2d', '( %s <_ ( %s ` k ) <-> %s <_ %s )' % (V, FM, V, ATK))], 'rexbidva', '( E. k e. %s %s <_ ( %s ` k ) <-> E. k e. %s %s <_ %s )' % (KJ, V, FM, KJ, V, ATK))
    v4r = c.mem(V4, 'RR')
    # under A
    Lf = lambda st: lift(w, st, A)
    m1 = dst(w, A, [Lf(v4r), Lf(abr), Lf(sumr), big, Lf(ba)], 'letrd', '%s <_ ( %s + %s )' % (V4, SAT, AR_))
    m3 = dst(w, A, [Lf(v4r), Lf(sumr), Lf(sum8), m1, Lf(m2)], 'letrd', '%s <_ ( %s + %s )' % (V4, SAT, X8))
    m4 = dst(w, A, [Lf(v4e), m3], 'eqbrtrrd', '( 2 x. %s ) <_ ( %s + %s )' % (X8, SAT, X8))
    m5 = dst(w, A, [Lf(tw), m4], 'eqbrtrrd', '( %s + %s ) <_ ( %s + %s )' % (X8, X8, SAT, X8))
    m6 = dst(w, A, [m5, Lf(la)], 'mpbird', '%s <_ %s' % (X8, SAT))
    pre = dst(w, A, [dst(w, A, [Lf(hv), m6], 'eqbrtrd', '( ( # ` %s ) x. %s ) <_ %s' % (KJ, V, SAT)), eqc(w, A, Lf(se))], 'breqtrd', '( ( # ` %s ) x. %s ) <_ sum_ k e. %s ( %s ` k )' % (KJ, V, KJ, FM))
    ex = ap(w, A, 'ld1pig', [J(w, A, J(w, A, Lf(fi), Lf(ne)), J(w, A, Lf(vr), Lf(ff)), pre)], 'E. k e. %s %s <_ ( %s ` k )' % (KJ, V, FM))
    dst(w, A, [ex, Lf(bi)], 'mpbid', 'E. k e. %s %s <_ %s' % (KJ, V, ATK))
    return fin(w)


if __name__ == '__main__':
    for lab in ['ld1pig', 'ld1exblkl', 'ld1extay']:
        if want(lab):
            if not globals()[lab]():
                sys.exit(1)
