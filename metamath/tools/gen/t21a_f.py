"""Sortie T21a: the fold corollary (t21zs = sum_rpow_neg_one_sub_le, t21foldr, t21fold = fold)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from t21alib import *
from t21alib import ap as ap_
import num, lin
import cl as _cl
lin.FASTPATH = True
from tm import W


def gen_zs():
    w = W('t21zs', '` sum_ ( 1 <_ n <_ M ) n ^ - ( 1 + U ) <_ 1 + 1 / U ` for ` U > 0 ` (Lean ` sum_rpow_neg_one_sub_le ` ; ~ zserbnd , ~ isumless ).')
    A0 = ante_of(S['t21zs'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    u = unpack(w, A0)
    up, mz = u['U e. RR+'], u['M e. ZZ']
    U1 = '( 1 + U )'
    ur = st([up], 'rpred', 'U e. RR')
    u1r = st([st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), ur], 'readdcld', '%s e. RR' % U1)
    u1g = lin.linarith(w, A0, [st([up], 'rpgt0d', '0 < U')], '1 < %s' % U1, leaves={'U': ur})
    F = '( n e. NN |-> ( n ^c -u %s ) )' % U1
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one_z = st([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ')
    fin = st([], 'fzfid', '( 1 ... M ) e. Fin')
    sub = ap_(w, A0, [st([w.s([], '1nn', '1 e. NN')], 'a1i', '1 e. NN')], 'fzssnn', '( 1 ... M ) C_ NN')
    C1 = '( %s /\\ k e. NN )' % A0
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % C1)
    kp = w.s([kn], 'nnrpd', '( %s -> k e. RR+ )' % C1)
    nu1 = w.s([_cl.lift(w, u1r, C1)], 'renegcld', '( %s -> -u %s e. RR )' % (C1, U1))
    kb = w.s([kp, nu1], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (C1, U1))
    fv = w.s([w.s([w.s([], 'eqid', '%s = %s' % (F, F))], 'a1i', '( %s -> %s = %s )' % (C1, F, F)),
              w.s([w.s([], 'simpr', '( ( %s /\\ n = k ) -> n = k )' % C1)], 'oveq1d', '( ( %s /\\ n = k ) -> ( n ^c -u %s ) = ( k ^c -u %s ) )' % (C1, U1, U1)),
              kn, kb], 'fvmptd', '( %s -> ( %s ` k ) = ( k ^c -u %s ) )' % (C1, F, U1))
    cv = ap_(w, A0, [u1r, u1g], 'zsercvg', 'seq 1 ( + , %s ) e. dom ~~>' % F)
    ls = st([nnuz, one_z, fin, sub, fv, w.s([kb], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (C1, U1)), w.s([kb], 'rpge0d', '( %s -> 0 <_ ( k ^c -u %s ) )' % (C1, U1)), cv],
            'isumless', 'sum_ k e. ( 1 ... M ) ( k ^c -u %s ) <_ sum_ k e. NN ( k ^c -u %s )' % (U1, U1))
    zb = ap_(w, A0, [u1r, u1g], 'zserbnd', 'sum_ k e. NN ( k ^c -u %s ) <_ ( 1 + ( 1 / ( %s - 1 ) ) )' % (U1, U1))
    pc = st([st([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), st([ur], 'recnd', 'U e. CC')], 'pncan2d', '( %s - 1 ) = U' % U1)
    zb2 = st([zb, st([st([pc], 'oveq2d', '( 1 / ( %s - 1 ) ) = ( 1 / U )' % U1)], 'oveq2d', '( 1 + ( 1 / ( %s - 1 ) ) ) = ( 1 + ( 1 / U ) )' % U1)], 'breqtrd',
             'sum_ k e. NN ( k ^c -u %s ) <_ ( 1 + ( 1 / U ) )' % U1)
    cb = w.s([w.s([], 'oveq1', '( k = n -> ( k ^c -u %s ) = ( n ^c -u %s ) )' % (U1, U1))], 'cbvsumv', 'sum_ k e. ( 1 ... M ) ( k ^c -u %s ) = sum_ n e. ( 1 ... M ) ( n ^c -u %s )' % (U1, U1))
    kr = st([st([fin, w.s([w.s([w.s([], 'x', 'x')], 'x', 'x')], 'x', 'x') if False else None], 'x', 'x') if False else None], 'x', 'x') if False else None
    le = st([ls, st([st([], 'x', 'x')], 'x', 'x') if False else zb2], 'x', 'x') if False else None
    lsr = w.s([], 'x', 'x') if False else None
    # combine: sum_k (1...M) <= sum_k NN <= 1 + 1/U
    C2 = '( %s /\\ k e. ( 1 ... M ) )' % A0
    k2 = ap_(w, C2, [w.s([], 'simpr', '( %s -> k e. ( 1 ... M ) )' % C2)], 'elfznn', 'k e. NN')
    b2 = w.s([w.s([w.s([k2], 'nnrpd', '( %s -> k e. RR+ )' % C2), w.s([_cl.lift(w, u1r, C2)], 'renegcld', '( %s -> -u %s e. RR )' % (C2, U1))], 'rpcxpcld', '( %s -> ( k ^c -u %s ) e. RR+ )' % (C2, U1))], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (C2, U1))
    s1r = st([fin, b2], 'fsumrecl', 'sum_ k e. ( 1 ... M ) ( k ^c -u %s ) e. RR' % U1)
    snr = st([w.s([], 'x', 'x')], 'x', 'x') if False else None
    rhs = st([st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'), st([st([up], 'rpreccld', '( 1 / U ) e. RR+')], 'rpred', '( 1 / U ) e. RR')], 'readdcld', '( 1 + ( 1 / U ) ) e. RR')
    snr = st([ls, s1r], 'x', 'x') if False else None
    # sum over NN is real: sandwiched is not enough for letrd; use letrd with the isum real from isumrecl
    isr = st([nnuz, one_z, fv, w.s([kb], 'rpred', '( %s -> ( k ^c -u %s ) e. RR )' % (C1, U1)), cv], 'isumrecl', 'sum_ k e. NN ( k ^c -u %s ) e. RR' % U1)
    tr_ = st([s1r, isr, rhs, ls, zb2], 'letrd', 'sum_ k e. ( 1 ... M ) ( k ^c -u %s ) <_ ( 1 + ( 1 / U ) )' % U1)
    fin_ = st([st([cb], 'a1i', 'sum_ k e. ( 1 ... M ) ( k ^c -u %s ) = sum_ n e. ( 1 ... M ) ( n ^c -u %s )' % (U1, U1)), tr_], 'eqbrtrrd', 'sum_ n e. ( 1 ... M ) ( n ^c -u %s ) <_ ( 1 + ( 1 / U ) )' % U1)
    w.lines.append('qed:%s:idi |- %s' % (fin_, S['t21zs']))
    return run(w)

def hyps(w, H, lab):
    for k in sorted(H):
        w.lines.append('h%d::%s.%d |- %s' % (k, lab, k, H[k]))


def gen_foldr():
    w = W('t21foldr', 'The fold arithmetic: counts ` G <_ B T ^ C ` , ` H <_ B 2 ^ C ` and ` K ( n ) <_ B n ^ C ` on ` 2 <_ n <_ T ` with ` C <_ 1 - U ` give ` G / T + sum_ ( 1 <_ n <_ floor T ) K ( n ) / ( n ( n + 1 ) ) <_ B ( 2 + 1 / U ) ` , the ` n = 1 ` term read at ` H ` (Lean ` fold ` , its buckets ` n = 1 ` and ` n >_ 2 ` ; ~ t21zs ).')
    hyps(w, FOLDRH, 't21foldr')
    C0 = 'ph'
    s = lambda A_, h, r, f: w.s(h, r, '( %s -> %s )' % (A_, f))
    L = lambda st_, A_: _cl.lift(w, st_, A_)
    tr = s(C0, ['1'], 'simpld', 'T e. RR'); t2 = s(C0, ['1'], 'simprd', '2 <_ T')
    br = s(C0, ['2'], 'simpld', 'B e. RR'); b0 = s(C0, ['2'], 'simprd', '0 <_ B')
    up = s(C0, ['3'], 'simpld', 'U e. RR+'); cc_ = s(C0, ['3'], 'simprd', '( C e. RR /\\ C <_ ( 1 - U ) )')
    cr = s(C0, [cc_], 'simpld', 'C e. RR'); cu = s(C0, [cc_], 'simprd', 'C <_ ( 1 - U )')
    gr = s(C0, ['4'], 'simpld', 'G e. RR'); gle = s(C0, ['4'], 'simprd', 'G <_ ( B x. ( T ^c C ) )')
    hr = s(C0, ['5'], 'simpld', 'H e. RR'); hle = s(C0, ['5'], 'simprd', 'H <_ ( B x. ( 2 ^c C ) )')
    ur = s(C0, [up], 'rpred', 'U e. RR'); u0 = s(C0, [up], 'rpgt0d', '0 < U')
    one = s(C0, [w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'); two = s(C0, [w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    c1 = lin.linarith(w, C0, [cu, u0], 'C <_ 1', leaves={'C': cr, 'U': ur})
    t1 = lin.linarith(w, C0, [t2], '1 <_ T', leaves={'T': tr})
    tp = s(C0, [tr, lin.linarith(w, C0, [t2], '0 < T', leaves={'T': tr})], 'elrpd', 'T e. RR+')
    # (a) G / T <_ B
    tc = s(C0, [tr, t1, cr, one, c1], 'cxplead', '( T ^c C ) <_ ( T ^c 1 )')
    t1e = s(C0, [s(C0, [tr], 'recnd', 'T e. CC')], 'cxp1d', '( T ^c 1 ) = T')
    tcr = s(C0, [tr, s(C0, [tp], 'rpge0d', '0 <_ T'), cr], 'recxpcld', '( T ^c C ) e. RR')
    bt = s(C0, [tcr, tr, br, b0, s(C0, [tc, t1e], 'breqtrd', '( T ^c C ) <_ T')], 'lemul2ad', '( B x. ( T ^c C ) ) <_ ( B x. T )')
    gbt = s(C0, [gr, s(C0, [br, tcr], 'remulcld', '( B x. ( T ^c C ) ) e. RR'), s(C0, [br, tr], 'remulcld', '( B x. T ) e. RR'), gle, bt], 'letrd', 'G <_ ( B x. T )')
    gbt2 = s(C0, [gbt, s(C0, [s(C0, [br], 'recnd', 'B e. CC'), s(C0, [tr], 'recnd', 'T e. CC')], 'mulcomd', '( B x. T ) = ( T x. B )')], 'breqtrd', 'G <_ ( T x. B )')
    ga = s(C0, [gbt2, s(C0, [gr, br, tp], 'ledivmuld', '( ( G / T ) <_ B <-> G <_ ( T x. B ) )')], 'mpbird', '( G / T ) <_ B')
    # (b) H / 2 <_ B
    tw = s(C0, [two, s(C0, [w.s([], '1le2', '1 <_ 2')], 'a1i', '1 <_ 2'), cr, one, c1], 'cxplead', '( 2 ^c C ) <_ ( 2 ^c 1 )')
    tw1 = s(C0, [s(C0, [w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')], 'cxp1d', '( 2 ^c 1 ) = 2')
    twr = s(C0, [two, s(C0, [w.s([], '0le2', '0 <_ 2')], 'a1i', '0 <_ 2'), cr], 'recxpcld', '( 2 ^c C ) e. RR')
    b2 = s(C0, [twr, two, br, b0, s(C0, [tw, tw1], 'breqtrd', '( 2 ^c C ) <_ 2')], 'lemul2ad', '( B x. ( 2 ^c C ) ) <_ ( B x. 2 )')
    hb2 = s(C0, [hr, s(C0, [br, twr], 'remulcld', '( B x. ( 2 ^c C ) ) e. RR'), s(C0, [br, two], 'remulcld', '( B x. 2 ) e. RR'), hle, b2], 'letrd', 'H <_ ( B x. 2 )')
    hb3 = s(C0, [hb2, s(C0, [s(C0, [br], 'recnd', 'B e. CC'), s(C0, [w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')], 'mulcomd', '( B x. 2 ) = ( 2 x. B )')], 'breqtrd', 'H <_ ( 2 x. B )')
    two_p = s(C0, [w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+')
    ha = s(C0, [hb3, s(C0, [hr, br, two_p], 'ledivmuld', '( ( H / 2 ) <_ B <-> H <_ ( 2 x. B ) )')], 'mpbird', '( H / 2 ) <_ B')
    FT = '( |_ ` T )'
    D = '( n x. ( n + 1 ) )'; KD = '( K / %s )' % D; U1 = '( 1 + U )'; P = '( n ^c -u %s )' % U1
    ftz = s(C0, [tr], 'flcld', '%s e. ZZ' % FT)
    ft2 = s(C0, [t2, ap_(w, C0, [tr, s(C0, [w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')], 'flge', '( 2 <_ T <-> 2 <_ %s )' % FT)], 'mpbid', '2 <_ %s' % FT)
    ftr = s(C0, [ftz], 'zred', '%s e. RR' % FT)
    ft1 = lin.linarith(w, C0, [ft2], '1 <_ %s' % FT, leaves={FT: ftr})
    uz = w.s([s(C0, [s(C0, [w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), ftz, ft1], '3jca', '( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s )' % (FT, FT)),
              w.s([], 'eluz2', '( %s e. ( ZZ>= ` 1 ) <-> ( 1 e. ZZ /\\ %s e. ZZ /\\ 1 <_ %s ) )' % (FT, FT, FT))], 'sylibr', '( ph -> %s e. ( ZZ>= ` 1 ) )' % FT)
    r12 = '( ( 1 + 1 ) ... %s )' % FT; r2 = '( 2 ... %s )' % FT
    req = s(C0, [s(C0, [w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'a1i', '( 1 + 1 ) = 2')], 'oveq1d', '%s = %s' % (r12, r2))
    # context C1: n in ( 1 ... FT )
    C1 = '( ph /\\ n e. %s )' % FLT
    n1 = ap_(w, C1, [w.s([], 'simpr', '( %s -> n e. %s )' % (C1, FLT))], 'elfznn', 'n e. NN')
    fe = w.s([L(uz, C1), w.s([], 'simpr', '( %s -> n e. %s )' % (C1, FLT)), w.s([], 'elfzp12', '( %s e. ( ZZ>= ` 1 ) -> ( n e. %s <-> ( n = 1 \\/ n e. %s ) ) )' % (FT, FLT, r12))], 'x', 'x') if False else None
    fe0 = w.s([L(uz, C1), w.s([], 'elfzp12', '( %s e. ( ZZ>= ` 1 ) -> ( n e. %s <-> ( n = 1 \\/ n e. %s ) ) )' % (FT, FLT, r12))], 'syl', '( %s -> ( n e. %s <-> ( n = 1 \\/ n e. %s ) ) )' % (C1, FLT, r12))
    fe = w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (C1, FLT)), fe0], 'mpbid', '( %s -> ( n = 1 \\/ n e. %s ) )' % (C1, r12))
    Ca = '( %s /\\ n = 1 )' % C1; Cb = '( %s /\\ n e. %s )' % (C1, r12)
    ka = w.s([w.s([w.s([], 'simpr', '( %s -> n = 1 )' % Ca), '7'], 'syl', '( %s -> K = H )' % Ca), L(hr, Ca)], 'eqeltrd', '( %s -> K e. RR )' % Ca)
    nb = w.s([w.s([], 'simpr', '( %s -> n e. %s )' % (Cb, r12)), L(req, Cb)], 'eleqtrd', '( %s -> n e. %s )' % (Cb, r2))
    kb = w.s([w.s([L(w.s([], 'id', '( ph -> ph )'), Cb) if False else w.s([w.s([], 'simpl', '( %s -> %s )' % (Cb, C1))], 'simpld', '( %s -> ph )' % Cb), nb, '6'], 'syl2anc', '( %s -> ( K e. RR /\\ K <_ ( B x. ( n ^c C ) ) ) )' % Cb)], 'simpld', '( %s -> K e. RR )' % Cb)
    k1 = w.s([ka, kb, fe], 'mpjaodan', '( %s -> K e. RR )' % C1)
    dp1 = s(C1, [s(C1, [n1, s(C1, [n1], 'peano2nnd', '( n + 1 ) e. NN')], 'nnmulcld', '%s e. NN' % D)], 'nnrpd', '%s e. RR+' % D)
    kd1 = s(C1, [k1, dp1], 'rerpdivcld', '%s e. RR' % KD)
    sb = w.s([w.s(['7', w.s([w.s([], 'id', '( n = 1 -> n = 1 )'), w.s([w.s([], 'id', '( n = 1 -> n = 1 )')], 'oveq1d', '( n = 1 -> ( n + 1 ) = ( 1 + 1 ) )')], 'oveq12d', '( n = 1 -> %s = ( 1 x. ( 1 + 1 ) ) )' % D)], 'oveq12d', '( n = 1 -> %s = ( H / ( 1 x. ( 1 + 1 ) ) ) )' % KD)], 'x', 'x') if False else w.s(['7', w.s([w.s([], 'id', '( n = 1 -> n = 1 )'), w.s([w.s([], 'id', '( n = 1 -> n = 1 )')], 'oveq1d', '( n = 1 -> ( n + 1 ) = ( 1 + 1 ) )')], 'oveq12d', '( n = 1 -> %s = ( 1 x. ( 1 + 1 ) ) )' % D)], 'oveq12d', '( n = 1 -> %s = ( H / ( 1 x. ( 1 + 1 ) ) ) )' % KD)
    SK1 = 'sum_ n e. %s %s' % (FLT, KD); SK12 = 'sum_ n e. %s %s' % (r12, KD); SK2 = 'sum_ n e. %s %s' % (r2, KD)
    sp = s(C0, [uz, s(C1, [kd1], 'recnd', '%s e. CC' % KD), sb], 'fsum1p', '%s = ( ( H / ( 1 x. ( 1 + 1 ) ) ) + %s )' % (SK1, SK12))
    e12 = w.s([w.s([], 'mullidi', '( 1 x. ( 1 + 1 ) ) = ( 1 + 1 )') if False else w.s([w.s([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'oveq2i', '( 1 x. ( 1 + 1 ) ) = ( 1 x. 2 )'), w.s([w.s([], '2cn', '2 e. CC')], 'mullidi', '( 1 x. 2 ) = 2')], 'eqtri', '( 1 x. ( 1 + 1 ) ) = 2')], 'x', 'x') if False else w.s([w.s([w.s([], '1p1e2', '( 1 + 1 ) = 2')], 'oveq2i', '( 1 x. ( 1 + 1 ) ) = ( 1 x. 2 )'), w.s([w.s([], '2cn', '2 e. CC')], 'mullidi', '( 1 x. 2 ) = 2')], 'eqtri', '( 1 x. ( 1 + 1 ) ) = 2')
    hq = s(C0, [s(C0, [e12], 'a1i', '( 1 x. ( 1 + 1 ) ) = 2')], 'oveq2d', '( H / ( 1 x. ( 1 + 1 ) ) ) = ( H / 2 )')
    sq = s(C0, [req], 'sumeq1d', '%s = %s' % (SK12, SK2))
    # context Cn: n in ( 2 ... FT )
    Cn = '( ph /\\ n e. %s )' % r2
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (Cn, r2))
    nz = ap_(w, Cn, [nin], 'elfzelz', 'n e. ZZ'); nr = w.s([nz], 'zred', '( %s -> n e. RR )' % Cn)
    n2 = ap_(w, Cn, [nin], 'elfzle1', '2 <_ n')
    npos = lin.linarith(w, Cn, [n2], '0 < n', leaves={'n': nr})
    nn_ = w.s([w.s([nz, npos], 'jca', '( %s -> ( n e. ZZ /\\ 0 < n ) )' % Cn), w.s([], 'elnnz', '( n e. NN <-> ( n e. ZZ /\\ 0 < n ) )')], 'sylibr', '( %s -> n e. NN )' % Cn)
    np_ = w.s([nn_], 'nnrpd', '( %s -> n e. RR+ )' % Cn)
    n1_ = lin.linarith(w, Cn, [n2], '1 <_ n', leaves={'n': nr})
    k6 = '6'
    kr = s(Cn, [k6], 'simpld', 'K e. RR'); kle = s(Cn, [k6], 'simprd', 'K <_ ( B x. ( n ^c C ) )')
    ncr = s(Cn, [nr, s(Cn, [np_], 'rpge0d', '0 <_ n'), L(cr, Cn)], 'recxpcld', '( n ^c C ) e. RR')
    E1U = '( 1 - U )'
    e1r = s(Cn, [L(one, Cn), L(ur, Cn)], 'resubcld', '%s e. RR' % E1U)
    q1 = s(Cn, [nr, n1_, L(cr, Cn), e1r, L(cu, Cn)], 'cxplead', '( n ^c C ) <_ ( n ^c %s )' % E1U)
    nu = s(Cn, [L(s(C0, [one, ur], 'readdcld', '%s e. RR' % U1), Cn)], 'renegcld', '-u %s e. RR' % U1)
    ex = lin.lineq(w, Cn, '( -u %s + 2 )' % U1, E1U, leaves={'U': L(ur, Cn)})
    q2 = s(Cn, [s(Cn, [np_], 'rpcnd', 'n e. CC'), s(Cn, [np_], 'rpne0d', 'n =/= 0'), s(Cn, [nu], 'recnd', '-u %s e. CC' % U1), s(Cn, [w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC')], 'cxpaddd',
           '( n ^c ( -u %s + 2 ) ) = ( %s x. ( n ^c 2 ) )' % (U1, P))
    q3 = ap_(w, Cn, [s(Cn, [np_], 'rpcnd', 'n e. CC'), s(Cn, [w.s([], '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')], 'cxpexp', '( n ^c 2 ) = ( n ^ 2 )')
    q4 = s(Cn, [s(Cn, [np_], 'rpcnd', 'n e. CC')], 'sqvald', '( n ^ 2 ) = ( n x. n )')
    q5 = s(Cn, [s(Cn, [ex], 'oveq2d', '( n ^c ( -u %s + 2 ) ) = ( n ^c %s )' % (U1, E1U)), s(Cn, [q2, s(Cn, [s(Cn, [q3, q4], 'eqtrd', '( n ^c 2 ) = ( n x. n )')], 'oveq2d', '( %s x. ( n ^c 2 ) ) = ( %s x. ( n x. n ) )' % (P, P))], 'eqtrd', '( n ^c ( -u %s + 2 ) ) = ( %s x. ( n x. n ) )' % (U1, P))], 'eqtr3d',
           '( n ^c %s ) = ( %s x. ( n x. n ) )' % (E1U, P))
    pr = s(Cn, [s(Cn, [np_, nu], 'rpcxpcld', '%s e. RR+' % P)], 'rpred', '%s e. RR' % P)
    p0 = s(Cn, [s(Cn, [np_, nu], 'rpcxpcld', '%s e. RR+' % P)], 'rpge0d', '0 <_ %s' % P)
    nnr = s(Cn, [nr, nr], 'remulcld', '( n x. n ) e. RR')
    dr = s(Cn, [nr, s(Cn, [nr], 'x', 'x') if False else ap_(w, Cn, [nr], 'peano2re', '( n + 1 ) e. RR')], 'remulcld', '%s e. RR' % D)
    nnd = lin.nlinarith(w, Cn, [npos], '( n x. n ) <_ %s' % D, leaves={'n': nr})
    q6 = s(Cn, [nnr, dr, pr, p0, nnd], 'lemul2ad', '( %s x. ( n x. n ) ) <_ ( %s x. %s )' % (P, P, D))
    a1_ = s(Cn, [ncr, s(Cn, [np_, e1r], 'x', 'x') if False else s(Cn, [nr, s(Cn, [np_], 'rpge0d', '0 <_ n'), e1r], 'recxpcld', '( n ^c %s ) e. RR' % E1U), L(br, Cn), L(b0, Cn), q1], 'lemul2ad', '( B x. ( n ^c C ) ) <_ ( B x. ( n ^c %s ) )' % E1U)
    a2_ = s(Cn, [q5], 'oveq2d', '( B x. ( n ^c %s ) ) = ( B x. ( %s x. ( n x. n ) ) )' % (E1U, P))
    a3_ = s(Cn, [s(Cn, [pr, nnr], 'remulcld', '( %s x. ( n x. n ) ) e. RR' % P), s(Cn, [pr, dr], 'remulcld', '( %s x. %s ) e. RR' % (P, D)), L(br, Cn), L(b0, Cn), q6], 'lemul2ad',
            '( B x. ( %s x. ( n x. n ) ) ) <_ ( B x. ( %s x. %s ) )' % (P, P, D))
    a4_ = s(Cn, [s(Cn, [L(br, Cn)], 'recnd', 'B e. CC'), s(Cn, [pr], 'recnd', '%s e. CC' % P), s(Cn, [dr], 'recnd', '%s e. CC' % D)], 'mulassd', '( ( B x. %s ) x. %s ) = ( B x. ( %s x. %s ) )' % (P, D, P, D))
    cN = _cl.Closure(w, Cn, {})
    atoms = {'K': kr, '( B x. ( n ^c C ) )': s(Cn, [L(br, Cn), ncr], 'remulcld', '( B x. ( n ^c C ) ) e. RR'),
             '( B x. ( n ^c %s ) )' % E1U: s(Cn, [L(br, Cn), s(Cn, [nr, s(Cn, [np_], 'rpge0d', '0 <_ n'), e1r], 'recxpcld', '( n ^c %s ) e. RR' % E1U)], 'remulcld', '( B x. ( n ^c %s ) ) e. RR' % E1U),
             '( B x. ( %s x. ( n x. n ) ) )' % P: s(Cn, [L(br, Cn), s(Cn, [pr, nnr], 'remulcld', '( %s x. ( n x. n ) ) e. RR' % P)], 'remulcld', '( B x. ( %s x. ( n x. n ) ) ) e. RR' % P),
             '( B x. ( %s x. %s ) )' % (P, D): s(Cn, [L(br, Cn), s(Cn, [pr, dr], 'remulcld', '( %s x. %s ) e. RR' % (P, D))], 'remulcld', '( B x. ( %s x. %s ) ) e. RR' % (P, D)),
             '( ( B x. %s ) x. %s )' % (P, D): s(Cn, [s(Cn, [L(br, Cn), pr], 'remulcld', '( B x. %s ) e. RR' % P), dr], 'remulcld', '( ( B x. %s ) x. %s ) e. RR' % (P, D))}
    for E_, st_ in atoms.items():
        cN.leaf(E_, 'RR', st_)
    kk = lin.linarith(w, Cn, [kle, a1_, a2_, a3_, a4_], 'K <_ ( ( B x. %s ) x. %s )' % (P, D), closure=cN)
    dpn = s(Cn, [s(Cn, [nn_, s(Cn, [nn_], 'peano2nnd', '( n + 1 ) e. NN')], 'nnmulcld', '%s e. NN' % D)], 'nnrpd', '%s e. RR+' % D)
    kdb = s(Cn, [kk, s(Cn, [kr, s(Cn, [L(br, Cn), pr], 'remulcld', '( B x. %s ) e. RR' % P), dpn], 'ledivmul2d', '( %s <_ ( B x. %s ) <-> K <_ ( ( B x. %s ) x. %s ) )' % (KD, P, P, D))], 'mpbird', '%s <_ ( B x. %s )' % (KD, P))
    # (d) sums over ( 2 ... FT )
    f2 = s(C0, [], 'fzfid', '%s e. Fin' % r2)
    kdn = s(Cn, [kr, dpn], 'rerpdivcld', '%s e. RR' % KD)
    bpn = s(Cn, [L(br, Cn), pr], 'remulcld', '( B x. %s ) e. RR' % P)
    d1 = s(C0, [f2, kdn, bpn, kdb], 'fsumle', '%s <_ sum_ n e. %s ( B x. %s )' % (SK2, r2, P))
    SP2 = 'sum_ n e. %s %s' % (r2, P)
    d2 = s(C0, [f2, s(C0, [br], 'recnd', 'B e. CC'), s(Cn, [pr], 'recnd', '%s e. CC' % P)], 'fsummulc2', '( B x. %s ) = sum_ n e. %s ( B x. %s )' % (SP2, r2, P))
    # sum_{1..FT} P = 1 + sum_{2..FT} P, and <_ 1 + 1 / U
    p1 = s(C1, [s(C1, [s(C1, [n1], 'nnrpd', 'n e. RR+'), L(s(C0, [s(C0, [one, ur], 'readdcld', '%s e. RR' % U1)], 'renegcld', '-u %s e. RR' % U1), C1)], 'rpcxpcld', '%s e. RR+' % P)], 'rpcnd', '%s e. CC' % P)
    sbp = w.s([], 'oveq1', '( n = 1 -> %s = ( 1 ^c -u %s ) )' % (P, U1))
    SP1 = 'sum_ n e. %s %s' % (FLT, P); SP12 = 'sum_ n e. %s %s' % (r12, P)
    spp = s(C0, [uz, p1, sbp], 'fsum1p', '%s = ( ( 1 ^c -u %s ) + %s )' % (SP1, U1, SP12))
    o1 = ap_(w, C0, [s(C0, [s(C0, [s(C0, [one, ur], 'readdcld', '%s e. RR' % U1)], 'renegcld', '-u %s e. RR' % U1)], 'recnd', '-u %s e. CC' % U1)], '1cxp', '( 1 ^c -u %s ) = 1' % U1)
    sqp = s(C0, [req], 'sumeq1d', '%s = %s' % (SP12, SP2))
    zs = ap_(w, C0, [up, ftz], 't21zs', '%s <_ ( 1 + ( 1 / U ) )' % SP1)
    c0 = _cl.Closure(w, C0, {})
    p1r = s(C0, [s(C0, [], 'fzfid', '%s e. Fin' % FLT), s(C1, [p1], 'x', 'x') if False else s(C1, [s(C1, [s(C1, [n1], 'nnrpd', 'n e. RR+'), L(s(C0, [s(C0, [one, ur], 'readdcld', '%s e. RR' % U1)], 'renegcld', '-u %s e. RR' % U1), C1)], 'rpcxpcld', '%s e. RR+' % P)], 'rpred', '%s e. RR' % P)], 'fsumrecl', '%s e. RR' % SP1)
    p2r = s(C0, [f2, pr], 'fsumrecl', '%s e. RR' % SP2)
    ur_ = s(C0, [s(C0, [up], 'rpreccld', '( 1 / U ) e. RR+')], 'rpred', '( 1 / U ) e. RR')
    for E_, st_ in [(SP1, p1r), (SP2, p2r), ('( 1 / U )', ur_), ('( 1 ^c -u %s )' % U1, s(C0, [o1, one], 'eqeltrd', '( 1 ^c -u %s ) e. RR' % U1))]:
        c0.leaf(E_, 'RR', st_)
    c0.atom(SP12); c0.leaf(SP12, 'RR', s(C0, [sqp, p2r], 'eqeltrd', '%s e. RR' % SP12))
    pb = lin.linarith(w, C0, [spp, o1, sqp, zs], '%s <_ ( 1 / U )' % SP2, closure=c0)
    bpb = s(C0, [p2r, ur_, br, b0, pb], 'lemul2ad', '( B x. %s ) <_ ( B x. ( 1 / U ) )' % SP2)
    # final
    SBP = 'sum_ n e. %s ( B x. %s )' % (r2, P)
    for E_, st_ in [('( G / T )', s(C0, [gr, tp], 'rerpdivcld', '( G / T ) e. RR')), ('( H / 2 )', s(C0, [hr, two_p], 'rerpdivcld', '( H / 2 ) e. RR')),
                    (SK1, s(C0, [s(C0, [], 'fzfid', '%s e. Fin' % FLT), kd1], 'fsumrecl', '%s e. RR' % SK1)), (SK2, s(C0, [f2, kdn], 'fsumrecl', '%s e. RR' % SK2)),
                    (SBP, s(C0, [f2, bpn], 'fsumrecl', '%s e. RR' % SBP)), ('( B x. %s )' % SP2, s(C0, [br, p2r], 'remulcld', '( B x. %s ) e. RR' % SP2)),
                    ('( B x. ( 1 / U ) )', s(C0, [br, ur_], 'remulcld', '( B x. ( 1 / U ) ) e. RR')), ('B', br)]:
        c0.leaf(E_, 'RR', st_)
    for E_ in [SK12, '( H / ( 1 x. ( 1 + 1 ) ) )', '( B x. ( 2 + ( 1 / U ) ) )']:
        c0.atom(E_)
    c0.leaf('( H / ( 1 x. ( 1 + 1 ) ) )', 'RR', s(C0, [hq, c0.mem('( H / 2 )', 'RR')], 'eqeltrd', '( H / ( 1 x. ( 1 + 1 ) ) ) e. RR'))
    c0.leaf(SK12, 'RR', s(C0, [sq, c0.mem(SK2, 'RR')], 'eqeltrd', '%s e. RR' % SK12))
    dd = s(C0, [s(C0, [br], 'recnd', 'B e. CC'), s(C0, [w.s([], '2cn', '2 e. CC')], 'a1i', '2 e. CC'), s(C0, [ur_], 'recnd', '( 1 / U ) e. CC')], 'adddid', '( B x. ( 2 + ( 1 / U ) ) ) = ( ( B x. 2 ) + ( B x. ( 1 / U ) ) )')
    c0.leaf('( B x. ( 2 + ( 1 / U ) ) )', 'RR', s(C0, [br, s(C0, [two, ur_], 'readdcld', '( 2 + ( 1 / U ) ) e. RR')], 'remulcld', '( B x. ( 2 + ( 1 / U ) ) ) e. RR'))
    fin = lin.linarith(w, C0, [ga, ha, sp, hq, sq, d1, d2, bpb, dd], '( ( G / T ) + %s ) <_ ( B x. ( 2 + ( 1 / U ) ) )' % SK1, closure=c0)
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21foldr']))
    return run(w)

def gen_fold():
    w = W('t21fold', 'The fold corollary: a density input ` N ( A , t ) <_ C ( N t ^ P ) ^ W L ` on ` 2 <_ t <_ T ` with fold exponent ` P W <_ 1 - U ` gives the ` T ` -free bound ` sum_chi sum_rho ord / ( 1 + abs gamma ) <_ C N ^ W L ( 2 + 1 / U ) ` (Lean ` fold ` ; ~ t21lgs , ~ t21foldr ).')
    A0 = ante_of(S['t21fold'])[0]
    st = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    L_ = lambda st_, A_: _cl.lift(w, st_, A_)
    u = unpack(w, A0)
    nn, ar, a0, a1, tr, t2 = [u[k] for k in ['N e. NN', 'A e. RR', '0 < A', 'A <_ 1', 'T e. RR', '2 <_ T']]
    cr, c0, lr, l0, pr, wr, w0 = [u[k] for k in ['C e. RR', '0 <_ C', 'L e. RR', '0 <_ L', 'P e. RR', 'W e. RR', '0 <_ W']]
    up, pw = u['U e. RR+'], u['( P x. W ) <_ ( 1 - U )']
    FH = [k for k in u if k.startswith('A. t e. RR')][0]
    A1 = '( N e. NN /\\ ( A e. RR /\\ 0 < A /\\ A <_ 1 ) /\\ ( T e. RR /\\ 2 <_ T ) )'
    map0 = st([], 'simp1', A1)
    u1 = unpack(w, A1)
    cnn, car, ca0, ca1, ctr, ct2 = [u1[k] for k in ['N e. NN', 'A e. RR', '0 < A', 'A <_ 1', 'T e. RR', '2 <_ T']]

    def cmap(A_, extra):
        # ( ( A0 /\ extra ) -> ( A1 /\ extra ) )
        return w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (A_, A0)), map0], 'syl', '( %s -> %s )' % (A_, A1)), w.s([], 'simpr', '( %s -> %s )' % (A_, extra))], 'jca', '( %s -> ( %s /\\ %s ) )' % (A_, A1, extra))
    fh = u[FH]
    t1 = lin.linarith(w, A0, [t2], '1 <_ T', leaves={'T': tr})
    lg = ap_(w, A0, [nn, ar, a0, a1, tr, t1], 't21lgs', '%s <_ ( ( %s / T ) + sum_ n e. %s ( %s / ( n x. ( n + 1 ) ) ) )' % (WS('A', 'T'), NC('A', 'T'), FLT, NC('A', 'n')))
    B = '( ( C x. ( N ^c W ) ) x. L )'
    nr = st([nn], 'nnred', 'N e. RR'); n0 = st([st([nn], 'nnrpd', 'N e. RR+')], 'rpge0d', '0 <_ N')
    nwr = st([nr, n0, wr], 'recxpcld', '( N ^c W ) e. RR')
    br = st([st([cr, nwr], 'remulcld', '( C x. ( N ^c W ) ) e. RR'), lr], 'remulcld', '%s e. RR' % B)
    b0 = st([st([cr, nwr], 'remulcld', '( C x. ( N ^c W ) ) e. RR'), lr, st([cr, nwr, c0, st([nr, n0, wr], 'cxpge0d', '0 <_ ( N ^c W )')], 'mulge0d', '0 <_ ( C x. ( N ^c W ) )'), l0], 'mulge0d', '0 <_ %s' % B)
    PW = '( P x. W )'
    pwr = st([pr, wr], 'remulcld', '%s e. RR' % PW)
    R = lambda v: '( ( C x. ( ( N x. ( %s ^c P ) ) ^c W ) ) x. L )' % v

    def dens(A_, V, vrp, v2, vT, Acl=None, amap=None, vrcl=None):
        """( A_ -> ( NC(A,V) e. RR /\\ NC(A,V) <_ ( B x. ( V ^c PW ) ) ) )"""
        H = 't = %s' % V
        body = lambda v: '( ( 2 <_ %s /\\ %s <_ T ) -> %s <_ %s )' % (v, v, NC('A', v), R(v))
        e1 = nc_eq(w, 't', V)
        r1 = w.s([w.s([w.s([], 'oveq1', '( %s -> ( t ^c P ) = ( %s ^c P ) )' % (H, V))], 'oveq2d', '( %s -> ( N x. ( t ^c P ) ) = ( N x. ( %s ^c P ) ) )' % (H, V))], 'oveq1d',
                 '( %s -> ( ( N x. ( t ^c P ) ) ^c W ) = ( ( N x. ( %s ^c P ) ) ^c W ) )' % (H, V))
        r2 = w.s([w.s([r1], 'oveq2d', '( %s -> ( C x. ( ( N x. ( t ^c P ) ) ^c W ) ) = ( C x. ( ( N x. ( %s ^c P ) ) ^c W ) ) )' % (H, V))], 'oveq1d', '( %s -> %s = %s )' % (H, R('t'), R(V)))
        cnd = w.s([w.s([], 'breq2', '( %s -> ( 2 <_ t <-> 2 <_ %s ) )' % (H, V)), w.s([], 'breq1', '( %s -> ( t <_ T <-> %s <_ T ) )' % (H, V))], 'anbi12d',
                  '( %s -> ( ( 2 <_ t /\\ t <_ T ) <-> ( 2 <_ %s /\\ %s <_ T ) ) )' % (H, V, V))
        bi = w.s([cnd, w.s([e1, r2], 'breq12d', '( %s -> ( %s <_ %s <-> %s <_ %s ) )' % (H, NC('A', 't'), R('t'), NC('A', V), R(V)))], 'imbi12d', '( %s -> ( %s <-> %s ) )' % (H, body('t'), body(V)))
        rs = w.s([bi], 'rspcv', '( %s e. RR -> ( A. t e. RR %s -> %s ) )' % (V, body('t'), body(V)))
        vr = w.s([vrp], 'rpred', '( %s -> %s e. RR )' % (A_, V))
        b1 = w.s([vr, L_(fh, A_), rs], 'sylc', '( %s -> %s )' % (A_, body(V)))
        le = w.s([w.s([v2, vT], 'jca', '( %s -> ( 2 <_ %s /\\ %s <_ T ) )' % (A_, V, V)), b1], 'mpd', '( %s -> %s <_ %s )' % (A_, NC('A', V), R(V)))
        # R(V) = B x. ( V ^c PW )
        s_ = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A_, f))
        VP = '( %s ^c P )' % V
        vpr = s_([vrp, L_(pr, A_)], 'rpcxpcld', '%s e. RR+' % VP)
        m1 = s_([L_(nr, A_), L_(n0, A_), s_([vpr], 'rpred', '%s e. RR' % VP), s_([vpr], 'rpge0d', '0 <_ %s' % VP), s_([L_(wr, A_)], 'recnd', 'W e. CC')], 'mulcxpd',
                '( ( N x. %s ) ^c W ) = ( ( N ^c W ) x. ( %s ^c W ) )' % (VP, VP))
        m2 = s_([vrp, L_(pr, A_), s_([L_(wr, A_)], 'recnd', 'W e. CC')], 'cxpmuld', '( %s ^c %s ) = ( %s ^c W )' % (V, PW, VP))
        VPW = '( %s ^c %s )' % (V, PW)
        m3 = s_([m1, s_([m2], 'eqcomd', '( %s ^c W ) = %s' % (VP, VPW)) and s_([s_([m2], 'eqcomd', '( %s ^c W ) = %s' % (VP, VPW))], 'oveq2d', '( ( N ^c W ) x. ( %s ^c W ) ) = ( ( N ^c W ) x. %s )' % (VP, VPW))], 'eqtrd',
                '( ( N x. %s ) ^c W ) = ( ( N ^c W ) x. %s )' % (VP, VPW))
        cc = s_([L_(cr, A_)], 'recnd', 'C e. CC'); nwc = s_([L_(nwr, A_)], 'recnd', '( N ^c W ) e. CC')
        vpwc = s_([s_([vrp, L_(pwr, A_)], 'rpcxpcld', '%s e. RR+' % VPW)], 'rpcnd', '%s e. CC' % VPW); lc = s_([L_(lr, A_)], 'recnd', 'L e. CC')
        m4 = s_([s_([m3], 'oveq2d', '( C x. ( ( N x. %s ) ^c W ) ) = ( C x. ( ( N ^c W ) x. %s ) )' % (VP, VPW)), s_([cc, nwc, vpwc], 'mulassd', '( ( C x. ( N ^c W ) ) x. %s ) = ( C x. ( ( N ^c W ) x. %s ) )' % (VPW, VPW))], 'eqtr4d',
                '( C x. ( ( N x. %s ) ^c W ) ) = ( ( C x. ( N ^c W ) ) x. %s )' % (VP, VPW))
        m5 = s_([s_([m4], 'oveq1d', '%s = ( ( ( C x. ( N ^c W ) ) x. %s ) x. L )' % (R(V), VPW)), s_([s_([cc, nwc], 'mulcld', '( C x. ( N ^c W ) ) e. CC'), vpwc, lc], 'mul32d',
                '( ( ( C x. ( N ^c W ) ) x. %s ) x. L ) = ( %s x. %s )' % (VPW, B, VPW))], 'eqtrd', '%s = ( %s x. %s )' % (R(V), B, VPW))
        le2 = s_([le, m5], 'breqtrd', '%s <_ ( %s x. %s )' % (NC('A', V), B, VPW))
        ncc, _ = nc_real(w, Acl, L_(cnn, Acl), L_(car, Acl), L_(ca0, Acl), L_(ca1, Acl), vrcl, 'A', V)
        ncr = w.s([amap, ncc], 'syl', '( %s -> %s e. RR )' % (A_, NC('A', V)))
        return s_([ncr, le2], 'jca', '( %s e. RR /\\ %s <_ ( %s x. %s ) )' % (NC('A', V), NC('A', V), B, VPW))
    tp = st([tr, lin.linarith(w, A0, [t2], '0 < T', leaves={'T': tr})], 'elrpd', 'T e. RR+')
    h4 = dens(A0, 'T', tp, t2, st([tr], 'leidd', 'T <_ T'), A1, map0, ctr)
    two_p = st([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+')
    d2 = dens(A0, '2', two_p, st([w.s([], '2re', '2 e. RR')], 'leidd', '2 <_ 2') if False else st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'leidd', '2 <_ 2'), t2, A1, map0, w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A1))
    # N ( A , 1 ) <_ N ( A , 2 )
    one_r = st([w.s([], '1re', '1 e. RR')], 'a1i', '1 e. RR'); two_r = st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    one_c = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A1); two_c = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A1)
    n2c, inf2 = nc_real(w, A1, cnn, car, ca0, ca1, two_c, 'A', '2')
    n1c, inf1 = nc_real(w, A1, cnn, car, ca0, ca1, one_c, 'A', '1')
    n2r = st([map0, n2c], 'syl', '%s e. RR' % NC('A', '2')) if False else w.s([map0, n2c], 'syl', '( %s -> %s e. RR )' % (A0, NC('A', '2')))
    n1r = w.s([map0, n1c], 'syl', '( %s -> %s e. RR )' % (A0, NC('A', '1')))
    C1 = inf2['C1']
    ss = ap_(w, C1, [L_(car, C1), L_(car, C1), w.s([L_(car, C1)], 'leidd', '( %s -> A <_ A )' % C1), L_(one_c, C1), L_(two_c, C1), w.s([w.s([], '1le2', '1 <_ 2')], 'a1i', '( %s -> 1 <_ 2 )' % C1)], 't21zfss',
             '%s C_ %s' % (ZFX('A', '1'), ZFX('A', '2')))
    inl = w.s([inf2['zfin'], inf2['orr'], inf2['or0'], ss], 'fsumless', '( %s -> sum_ q e. %s %s <_ sum_ q e. %s %s )' % (C1, ZFX('A', '1'), ORD(), ZFX('A', '2'), ORD()))
    m12c = w.s([inf2['dfin'], inf1['inner'], inf2['inner'], inl], 'fsumle', '( %s -> %s <_ %s )' % (A1, NC('A', '1'), NC('A', '2')))
    m12 = w.s([map0, m12c], 'syl', '( %s -> %s <_ %s )' % (A0, NC('A', '1'), NC('A', '2')))
    t2pw = st([st([st([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), pwr], 'rpcxpcld', '( 2 ^c %s ) e. RR+' % PW)], 'rpred', '( 2 ^c %s ) e. RR' % PW)
    h5 = st([n1r, st([n1r, n2r, st([br, t2pw], 'remulcld', '( %s x. ( 2 ^c %s ) ) e. RR' % (B, PW)), m12, st([d2], 'simprd', '%s <_ ( %s x. ( 2 ^c %s ) )' % (NC('A', '2'), B, PW))], 'letrd', '%s <_ ( %s x. ( 2 ^c %s ) )' % (NC('A', '1'), B, PW))], 'jca',
            '( %s e. RR /\\ %s <_ ( %s x. ( 2 ^c %s ) ) )' % (NC('A', '1'), NC('A', '1'), B, PW))
    # n in ( 2 ... floor T )
    Cn = '( %s /\\ n e. %s )' % (A0, F2T)
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (Cn, F2T))
    nz = ap_(w, Cn, [nin], 'elfzelz', 'n e. ZZ'); nrr = w.s([nz], 'zred', '( %s -> n e. RR )' % Cn)
    n2 = ap_(w, Cn, [nin], 'elfzle1', '2 <_ n'); nle = ap_(w, Cn, [nin], 'elfzle2', 'n <_ ( |_ ` T )')
    npos = lin.linarith(w, Cn, [n2], '0 < n', leaves={'n': nrr})
    nrp = w.s([nrr, npos], 'elrpd', '( %s -> n e. RR+ )' % Cn)
    ftr = w.s([w.s([L_(tr, Cn)], 'flcld', '( %s -> ( |_ ` T ) e. ZZ )' % Cn)], 'zred', '( %s -> ( |_ ` T ) e. RR )' % Cn)
    nT = w.s([nrr, ftr, L_(tr, Cn), nle, ap_(w, Cn, [L_(tr, Cn)], 'flle', '( |_ ` T ) <_ T')], 'letrd', '( %s -> n <_ T )' % Cn)
    Ccl = '( %s /\\ n e. %s )' % (A1, F2T)
    ncl = ap_(w, Ccl, [w.s([], 'simpr', '( %s -> n e. %s )' % (Ccl, F2T))], 'elfzelz', 'n e. ZZ')
    h6 = dens(Cn, 'n', nrp, n2, nT, Ccl, cmap(Cn, 'n e. %s' % F2T), w.s([ncl], 'zred', '( %s -> n e. RR )' % Ccl))
    h7 = nc_eq(w, 'n', '1')
    hu = st([up, st([pwr, pw], 'jca', '( %s e. RR /\\ %s <_ ( 1 - U ) )' % (PW, PW))], 'jca', '( U e. RR+ /\\ ( %s e. RR /\\ %s <_ ( 1 - U ) ) )' % (PW, PW))
    fr = ap_(w, A0, [st([tr, t2], 'jca', '( T e. RR /\\ 2 <_ T )'), st([br, b0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (B, B)), hu, h4, h5, h6, h7], 't21foldr',
             '( ( %s / T ) + sum_ n e. %s ( %s / ( n x. ( n + 1 ) ) ) ) <_ ( %s x. ( 2 + ( 1 / U ) ) )' % (NC('A', 'T'), FLT, NC('A', 'n'), B))
    wsr = w.s([map0, ws_real(w, A1, cnn, car, ca0, ca1, ctr)], 'syl', '( %s -> %s e. RR )' % (A0, WS('A', 'T')))
    mid = '( ( %s / T ) + sum_ n e. %s ( %s / ( n x. ( n + 1 ) ) ) )' % (NC('A', 'T'), FLT, NC('A', 'n'))
    C1 = '( %s /\\ n e. %s )' % (A0, FLT)
    n1 = ap_(w, C1, [w.s([], 'simpr', '( %s -> n e. %s )' % (C1, FLT))], 'elfznn', 'n e. NN')
    Ccl1 = '( %s /\\ n e. %s )' % (A1, FLT)
    ncl1 = ap_(w, Ccl1, [w.s([], 'simpr', '( %s -> n e. %s )' % (Ccl1, FLT))], 'elfznn', 'n e. NN')
    nc1c, _ = nc_real(w, Ccl1, L_(cnn, Ccl1), L_(car, Ccl1), L_(ca0, Ccl1), L_(ca1, Ccl1), w.s([ncl1], 'nnred', '( %s -> n e. RR )' % Ccl1), 'A', 'n')
    nc1 = w.s([cmap(C1, 'n e. %s' % FLT), nc1c], 'syl', '( %s -> %s e. RR )' % (C1, NC('A', 'n')))
    dp1 = w.s([w.s([n1, w.s([n1], 'peano2nnd', '( %s -> ( n + 1 ) e. NN )' % C1)], 'nnmulcld', '( %s -> ( n x. ( n + 1 ) ) e. NN )' % C1)], 'nnrpd', '( %s -> ( n x. ( n + 1 ) ) e. RR+ )' % C1)
    bd = w.s([nc1, dp1], 'rerpdivcld', '( %s -> ( %s / ( n x. ( n + 1 ) ) ) e. RR )' % (C1, NC('A', 'n')))
    sr = st([st([], 'fzfid', '%s e. Fin' % FLT), bd], 'fsumrecl', 'sum_ n e. %s ( %s / ( n x. ( n + 1 ) ) ) e. RR' % (FLT, NC('A', 'n')))
    midr = st([st([st([h4], 'simpld', '%s e. RR' % NC('A', 'T')), tp], 'rerpdivcld', '( %s / T ) e. RR' % NC('A', 'T')), sr], 'readdcld', '%s e. RR' % mid)
    ur_ = st([st([up], 'rpreccld', '( 1 / U ) e. RR+')], 'rpred', '( 1 / U ) e. RR')
    finr = st([br, st([st([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR'), ur_], 'readdcld', '( 2 + ( 1 / U ) ) e. RR')], 'remulcld', '( %s x. ( 2 + ( 1 / U ) ) ) e. RR' % B)
    fin = st([wsr, midr, finr, lg, fr], 'letrd', '%s <_ ( %s x. ( 2 + ( 1 / U ) ) )' % (WS('A', 'T'), B))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['t21fold']))
    return run(w)


if __name__ == '__main__':
    only = sys.argv[1:]
    for lab, f in [('t21zs', gen_zs), ('t21foldr', gen_foldr), ('t21fold', gen_fold)]:
        if not only or lab in only:
            f()
