"""Sortie ZBV2, section 4 part C3: the endgame (Lean endgame_numeric, bvHarm_uncond, bvL2_star_uncond),
ZBV2-blueprint.md section 3.3.  The numerals: _e <_ ( 9 / 8 ) ^ 9 < 29 / 10 and 4 <_ log 100.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zbv2lib import *
import num
import lin
lin.MAXDEG = 5

T_ = 'T.'


def litre(w, ante, X):
    return w.s([num.real(w, X)], 'a1i', '( %s -> %s e. RR )' % (ante, X))


def litcc(w, ante, X):
    return w.s([litre(w, ante, X)], 'recnd', '( %s -> %s e. CC )' % (ante, X))


def lsq(w, ante, X):
    """( ante -> ( X ^ 2 ) = lit ) for a literal X"""
    st = mkst(w, ante)
    v = num.lit_value(X) ** 2
    a = st([litcc(w, ante, X)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (X, X, X))
    b = st([num.mul_lits(w, X, X)], 'a1i', '( %s x. %s ) = %s' % (X, X, num.lit_text(v)))
    return st([a, b], 'eqtrd', '( %s ^ 2 ) = %s' % (X, num.lit_text(v))), num.lit_text(v)


def lcube(w, ante, X):
    """( ante -> ( X ^ 3 ) = lit ) for a literal X"""
    st = mkst(w, ante)
    s2, X2 = lsq(w, ante, X)
    v = num.lit_value(X) ** 3
    e3 = st([st([clo(w, '2p1e3', '( 2 + 1 ) = 3')], 'a1i', '( 2 + 1 ) = 3')], 'eqcomd', '3 = ( 2 + 1 )')
    a = st([e3], 'oveq2d', '( %s ^ 3 ) = ( %s ^ ( 2 + 1 ) )' % (X, X))
    b = st([litcc(w, ante, X), st([clo(w, '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0'), w.inst('expp1')], 'syl2anc', '( %s ^ ( 2 + 1 ) ) = ( ( %s ^ 2 ) x. %s )' % (X, X, X))
    c = st([s2], 'oveq1d', '( ( %s ^ 2 ) x. %s ) = ( %s x. %s )' % (X, X, X2, X))
    d = st([num.mul_lits(w, X2, X)], 'a1i', '( %s x. %s ) = %s' % (X2, X, num.lit_text(v)))
    return eqtr(w, ante, [a, b, c, d], None), num.lit_text(v)


def bvebnd():
    w = W('bvebnd', 'e <= 29 / 10: log ( 9 / 8 ) >= 1 / 9 (zdmlogl1) gives e <= ( 9 / 8 ) ^ 9 = ( 729 / 512 ) ^ 3 <= ( 57 / 40 ) ^ 3 '
                    '= 185193 / 64000 <= 29 / 10.')
    A = T_
    st = mkst(w, A)
    Y = '( 9 / 8 )'
    yr = litre(w, A, Y)
    y1 = st([le_lit2(w, '1', Y, strict=True)], 'a1i', '1 < %s' % Y)
    z = st([yr, y1, w.inst('zdmlogl1')], 'syl2anc', '( 1 - ( 1 / %s ) ) <_ ( log ` %s )' % (Y, Y))
    rd = st([litcc(w, A, '9'), litcc(w, A, '8'), st([num.ne0_nat(w, 9)], 'a1i', '9 =/= 0'), st([num.ne0_nat(w, 8)], 'a1i', '8 =/= 0')], 'recdivd',
            '( 1 / %s ) = ( 8 / 9 )' % Y)
    z2 = st([st([rd], 'oveq2d', '( 1 - ( 1 / %s ) ) = ( 1 - ( 8 / 9 ) )' % Y), z], 'eqbrtrrd', '( 1 - ( 8 / 9 ) ) <_ ( log ` %s )' % Y)
    yrp = st([num.rp(w, Y)], 'a1i', '%s e. RR+' % Y)
    ly = st([yrp], 'relogcld', '( log ` %s ) e. RR' % Y)
    one = linarith(w, A, [z2], '1 <_ ( 9 x. ( log ` %s ) )' % Y, leaves={'( log ` %s )' % Y: ly})
    Y9 = '( %s ^ 9 )' % Y
    lx = st([yrp, st([num.z_nat(w, 9)], 'a1i', '9 e. ZZ'), w.inst('relogexp')], 'syl2anc', '( log ` %s ) = ( 9 x. ( log ` %s ) )' % (Y9, Y))
    one2 = st([one, lx], 'breqtrrd', '1 <_ ( log ` %s )' % Y9)
    y9rp = st([yrp, st([num.z_nat(w, 9)], 'a1i', '9 e. ZZ')], 'rpexpcld', '%s e. RR+' % Y9)
    ef = st([one2, st([st([], '1red', '1 e. RR'), st([y9rp], 'relogcld', '( log ` %s ) e. RR' % Y9), w.inst('efle')], 'syl2anc',
                     '( 1 <_ ( log ` %s ) <-> ( exp ` 1 ) <_ ( exp ` ( log ` %s ) ) )' % (Y9, Y9))], 'mpbid', '( exp ` 1 ) <_ ( exp ` ( log ` %s ) )' % Y9)
    ef2 = st([ef, sy(w, A, y9rp, 'reeflog', '( exp ` ( log ` %s ) ) = %s' % (Y9, Y9))], 'breqtrd', '( exp ` 1 ) <_ %s' % Y9)
    # ( 9 / 8 ) ^ 9 = ( ( 9 / 8 ) ^ 3 ) ^ 3
    n9 = st([st([clo(w, '3t3e9', '( 3 x. 3 ) = 9')], 'a1i', '( 3 x. 3 ) = 9')], 'eqcomd', '9 = ( 3 x. 3 )')
    three = st([clo(w, '3nn0', '3 e. NN0')], 'a1i', '3 e. NN0')
    em = eqtr(w, A, [st([n9], 'oveq2d', '%s = ( %s ^ ( 3 x. 3 ) )' % (Y9, Y)),
                     st([litcc(w, A, Y), three, three, w.inst('expmul')], 'syl3anc', '( %s ^ ( 3 x. 3 ) ) = ( ( %s ^ 3 ) ^ 3 )' % (Y, Y))], None)
    c1, Y3 = lcube(w, A, Y)
    em2 = st([em, st([c1], 'oveq1d', '( ( %s ^ 3 ) ^ 3 ) = ( %s ^ 3 )' % (Y, Y3))], 'eqtrd', '%s = ( %s ^ 3 )' % (Y9, Y3))
    Q = '( ; 5 7 / ; 4 0 )'
    le1 = st([litre(w, A, Y3), litre(w, A, Q), three, st([le_lit2(w, '0', Y3)], 'a1i', '0 <_ %s' % Y3), st([le_lit2(w, Y3, Q)], 'a1i', '%s <_ %s' % (Y3, Q))],
             'leexp1ad', '( %s ^ 3 ) <_ ( %s ^ 3 )' % (Y3, Q))
    c2, Q3 = lcube(w, A, Q)
    fin = st([le_lit2(w, Q3, '( ; 2 9 / ; 1 0 )')], 'a1i', '%s <_ ( ; 2 9 / ; 1 0 )' % Q3)
    er = st([st([], '1red', '1 e. RR')], 'reefcld', '( exp ` 1 ) e. RR')
    y33r = st([litre(w, A, Y3), three], 'reexpcld', '( %s ^ 3 ) e. RR' % Y3)
    s1 = st([ef2, em2], 'breqtrd', '( exp ` 1 ) <_ ( %s ^ 3 )' % Y3)
    s2 = st([le1, c2], 'breqtrd', '( %s ^ 3 ) <_ %s' % (Y3, Q3))
    s12 = st([er, y33r, litre(w, A, Q3), s1, s2], 'letrd', '( exp ` 1 ) <_ %s' % Q3)
    s3 = st([er, litre(w, A, Q3), litre(w, A, '( ; 2 9 / ; 1 0 )'), s12, fin], 'letrd', '( exp ` 1 ) <_ ( ; 2 9 / ; 1 0 )')
    w.qed([s3], 'mptru', STATEMENTS['bvebnd'])
    return w


def bvlog100():
    w = W('bvlog100', '4 <= log 100: exp 4 = e ^ 4 <= ( 29 / 10 ) ^ 4 = 707281 / 10000 <= 100 (bvebnd, efexp).')
    A = T_
    st = mkst(w, A)
    E1 = '( exp ` 1 )'
    e4 = eqtr(w, A, [st([st([st([num.mul_lits(w, '4', '1')], 'a1i', '( 4 x. 1 ) = 4')], 'eqcomd', '4 = ( 4 x. 1 )')], 'fveq2d', '( exp ` 4 ) = ( exp ` ( 4 x. 1 ) )'),
                     st([st([], '1cnd', '1 e. CC'), st([num.z_nat(w, 4)], 'a1i', '4 e. ZZ'), w.inst('efexp')], 'syl2anc', '( exp ` ( 4 x. 1 ) ) = ( %s ^ 4 )' % E1)], None)
    er = st([st([], '1red', '1 e. RR')], 'reefcld', '%s e. RR' % E1)
    e0 = st([st([st([], '1red', '1 e. RR')], 'rpefcld', '%s e. RR+' % E1)], 'rpge0d', '0 <_ %s' % E1)
    Q = '( ; 2 9 / ; 1 0 )'
    four = st([clo(w, '4nn0', '4 e. NN0')], 'a1i', '4 e. NN0')
    le = st([er, litre(w, A, Q), four, e0, st([clo(w, 'bvebnd', '%s <_ %s' % (E1, Q))], 'a1i', '%s <_ %s' % (E1, Q))], 'leexp1ad', '( %s ^ 4 ) <_ ( %s ^ 4 )' % (E1, Q))
    n4 = st([st([clo(w, '2t2e4', '( 2 x. 2 ) = 4')], 'a1i', '( 2 x. 2 ) = 4')], 'eqcomd', '4 = ( 2 x. 2 )')
    two = st([clo(w, '2nn0', '2 e. NN0')], 'a1i', '2 e. NN0')
    s2, Q2 = lsq(w, A, Q)
    s4, Q4 = lsq(w, A, Q2)
    q4 = eqtr(w, A, [st([n4], 'oveq2d', '( %s ^ 4 ) = ( %s ^ ( 2 x. 2 ) )' % (Q, Q)),
                     st([litcc(w, A, Q), two, two, w.inst('expmul')], 'syl3anc', '( %s ^ ( 2 x. 2 ) ) = ( ( %s ^ 2 ) ^ 2 )' % (Q, Q)),
                     st([s2], 'oveq1d', '( ( %s ^ 2 ) ^ 2 ) = ( %s ^ 2 )' % (Q, Q2)), s4], None)
    H = '; ; 1 0 0'
    ex4 = st([st([e4, le], 'eqbrtrd', '( exp ` 4 ) <_ ( %s ^ 4 )' % Q), q4], 'breqtrd', '( exp ` 4 ) <_ %s' % Q4)
    ex5 = st([st([litre(w, A, '4')], 'reefcld', '( exp ` 4 ) e. RR'), litre(w, A, Q4), litre(w, A, H), ex4,
              st([le_lit2(w, Q4, H)], 'a1i', '%s <_ %s' % (Q4, H))], 'letrd', '( exp ` 4 ) <_ %s' % H)
    lg = st([ex5, st([st([litre(w, A, '4')], 'rpefcld', '( exp ` 4 ) e. RR+'), st([num.rp(w, H)], 'a1i', '%s e. RR+' % H)], 'logled',
                     '( ( exp ` 4 ) <_ %s <-> ( log ` ( exp ` 4 ) ) <_ ( log ` %s ) )' % (H, H))], 'mpbid', '( log ` ( exp ` 4 ) ) <_ ( log ` %s )' % H)
    r = st([st([sy(w, A, litre(w, A, '4'), 'relogef', '( log ` ( exp ` 4 ) ) = 4')], 'eqcomd', '4 = ( log ` ( exp ` 4 ) )'), lg], 'eqbrtrd', '4 <_ ( log ` %s )' % H)
    w.qed([r], 'mptru', STATEMENTS['bvlog100'])
    return w



def bvharmnum():
    w = W('bvharmnum', 'The endgame numerals (Lean endgame_numeric): with e <= 29 / 10, Z <= 1 + V, K W <= 1375 / 93, '
                       'G <= 63 W, 4 <= 62 W <= V: e Z K ^ 2 8 ( 1 + G ) <= 500000 V / W (the constant is 497637).')
    from cl import split_imp
    A, _c = split_imp(STATEMENTS['bvharmnum'])
    st = mkst(w, A)
    g1 = st([], 'simpll', '( E e. RR /\\ 0 <_ E /\\ E <_ ( ; 2 9 / ; 1 0 ) )')
    g2 = st([], 'simplr', '( Z e. RR /\\ 0 <_ Z /\\ Z <_ ( 1 + V ) )')
    g3 = st([], 'simpr', '( ( K e. RR /\\ 0 <_ K /\\ ( K x. W ) <_ ( ; ; ; 1 3 7 5 / ; 9 3 ) ) /\\ ( G e. RR /\\ 0 <_ G /\\ G <_ ( ; 6 3 x. W ) ) /\\ '
                          '( ( W e. RR /\\ V e. RR ) /\\ ( 4 <_ ( ; 6 2 x. W ) /\\ ( ; 6 2 x. W ) <_ V ) ) )')
    er = st([g1], 'simp1d', 'E e. RR'); e0 = st([g1], 'simp2d', '0 <_ E'); eb = st([g1], 'simp3d', 'E <_ ( ; 2 9 / ; 1 0 )')
    zr = st([g2], 'simp1d', 'Z e. RR'); z0 = st([g2], 'simp2d', '0 <_ Z'); zb = st([g2], 'simp3d', 'Z <_ ( 1 + V )')
    hk = st([g3], 'simp1d', '( K e. RR /\\ 0 <_ K /\\ ( K x. W ) <_ ( ; ; ; 1 3 7 5 / ; 9 3 ) )')
    hg = st([g3], 'simp2d', '( G e. RR /\\ 0 <_ G /\\ G <_ ( ; 6 3 x. W ) )')
    hw = st([g3], 'simp3d', '( ( W e. RR /\\ V e. RR ) /\\ ( 4 <_ ( ; 6 2 x. W ) /\\ ( ; 6 2 x. W ) <_ V ) )')
    kr = st([hk], 'simp1d', 'K e. RR'); k0 = st([hk], 'simp2d', '0 <_ K'); kb = st([hk], 'simp3d', '( K x. W ) <_ ( ; ; ; 1 3 7 5 / ; 9 3 )')
    gr = st([hg], 'simp1d', 'G e. RR'); g0 = st([hg], 'simp2d', '0 <_ G'); gb = st([hg], 'simp3d', 'G <_ ( ; 6 3 x. W )')
    wv = st([hw], 'simpld', '( W e. RR /\\ V e. RR )'); wr = st([wv], 'simpld', 'W e. RR'); vr = st([wv], 'simprd', 'V e. RR')
    wl = st([hw], 'simprd', '( 4 <_ ( ; 6 2 x. W ) /\\ ( ; 6 2 x. W ) <_ V )')
    w4 = st([wl], 'simpld', '4 <_ ( ; 6 2 x. W )'); wvle = st([wl], 'simprd', '( ; 6 2 x. W ) <_ V')
    lv = {'E': er, 'Z': zr, 'K': kr, 'G': gr, 'W': wr, 'V': vr}
    G8 = '( 8 x. ( 1 + G ) )'; W628 = '( ; ; 6 2 8 x. W )'; K2 = '( K ^ 2 )'; V54 = '( ( 5 / 4 ) x. V )'; E29 = '( ; 2 9 / ; 1 0 )'
    s1 = linarith(w, A, [gb, w4], '%s <_ %s' % (G8, W628), leaves=lv)
    s2 = linarith(w, A, [zb, w4, wvle], 'Z <_ %s' % V54, leaves=lv)
    w0 = linarith(w, A, [w4], '0 <_ W', leaves=lv)
    g80 = linarith(w, A, [g0], '0 <_ %s' % G8, leaves=lv)
    g8r = st([st([clo(w, '8re', '8 e. RR')], 'a1i', '8 e. RR'), st([st([], '1red', '1 e. RR'), gr], 'readdcld', '( 1 + G ) e. RR')], 'remulcld', '%s e. RR' % G8)
    w628r = st([st([num.real(w, '; ; 6 2 8')], 'a1i', '; ; 6 2 8 e. RR'), wr], 'remulcld', '%s e. RR' % W628)
    k2r = st([kr], 'resqcld', '%s e. RR' % K2); k20 = st([kr], 'sqge0d', '0 <_ %s' % K2)
    M1L = '( %s x. %s )' % (K2, G8); M1R = '( %s x. %s )' % (K2, W628)
    m1 = st([g8r, w628r, k2r, k20, s1], 'lemul2ad', '%s <_ %s' % (M1L, M1R))
    m1lr = st([k2r, g8r], 'remulcld', '%s e. RR' % M1L); m1rr = st([k2r, w628r], 'remulcld', '%s e. RR' % M1R)
    m1l0 = st([k2r, g8r, k20, g80], 'mulge0d', '0 <_ %s' % M1L)
    v54r = st([st([num.real(w, '( 5 / 4 )')], 'a1i', '( 5 / 4 ) e. RR'), vr], 'remulcld', '%s e. RR' % V54)
    M2L = '( Z x. %s )' % M1L; M2R = '( %s x. %s )' % (V54, M1R)
    m2 = st([zr, v54r, m1lr, m1rr, z0, m1l0, s2, m1], 'lemul12ad', '%s <_ %s' % (M2L, M2R))
    m2lr = st([zr, m1lr], 'remulcld', '%s e. RR' % M2L); m2rr = st([v54r, m1rr], 'remulcld', '%s e. RR' % M2R)
    m2l0 = st([zr, m1lr, z0, m1l0], 'mulge0d', '0 <_ %s' % M2L)
    e29r = st([num.real(w, E29)], 'a1i', '%s e. RR' % E29)
    M3L = '( E x. %s )' % M2L; M3R = '( %s x. %s )' % (E29, M2R)
    m3 = st([er, e29r, m2lr, m2rr, e0, m2l0, eb, m2], 'lemul12ad', '%s <_ %s' % (M3L, M3R))
    m3lr = st([er, m2lr], 'remulcld', '%s e. RR' % M3L); m3rr = st([e29r, m2rr], 'remulcld', '%s e. RR' % M3R)
    m4 = st([m3lr, m3rr, wr, w0, m3], 'lemul1ad', '( %s x. W ) <_ ( %s x. W )' % (M3L, M3R))
    C0 = '( ; ; ; 4 5 5 3 / 2 )'
    KW = '( K x. W )'
    P = '( ( %s x. V ) x. ( %s ^ 2 ) )' % (C0, KW)
    eq = linarith(w, A, [], '( %s x. W ) <_ %s' % (M3R, P), products=True, leaves=lv, atoms=['K', 'W', 'V'])
    kwr = st([kr, wr], 'remulcld', '%s e. RR' % KW); kw0 = st([kr, wr, k0, w0], 'mulge0d', '0 <_ %s' % KW)
    CK = '( ; ; ; 1 3 7 5 / ; 9 3 )'
    ckr = st([num.real(w, CK)], 'a1i', '%s e. RR' % CK)
    sq = st([bind(w, A, kwr, kw0, '%s e. RR' % KW, '0 <_ %s' % KW), bind(w, A, ckr, kb, '%s e. RR' % CK, '%s <_ %s' % (KW, CK)), w.inst('le2sq2')], 'syl2anc',
            '( %s ^ 2 ) <_ ( %s ^ 2 )' % (KW, CK))
    s2c, CK2 = lsq(w, A, CK)
    sq2 = st([sq, s2c], 'breqtrd', '( %s ^ 2 ) <_ %s' % (KW, CK2))
    c0v = '( %s x. V )' % C0
    v0 = linarith(w, A, [w4, wvle], '0 <_ V', leaves=lv)
    c0vr = st([st([num.real(w, C0)], 'a1i', '%s e. RR' % C0), vr], 'remulcld', '%s e. RR' % c0v)
    c0v0 = linarith(w, A, [v0], '0 <_ %s' % c0v, leaves=lv)
    m5 = st([st([kwr], 'resqcld', '( %s ^ 2 ) e. RR' % KW), st([num.real(w, CK2)], 'a1i', '%s e. RR' % CK2), c0vr, c0v0, sq2], 'lemul2ad',
            '( %s x. ( %s ^ 2 ) ) <_ ( %s x. %s )' % (c0v, KW, c0v, CK2))
    m6 = linarith(w, A, [v0], '( %s x. %s ) <_ ( %s x. V )' % (c0v, CK2, C5), leaves=lv)
    pr = st([c0vr, st([kwr], 'resqcld', '( %s ^ 2 ) e. RR' % KW)], 'remulcld', '%s e. RR' % P)
    c5v = '( %s x. V )' % C5
    c5vr = st([st([num.real(w, C5)], 'a1i', '%s e. RR' % C5), vr], 'remulcld', '%s e. RR' % c5v)
    t1 = st([pr, st([c0vr, st([num.real(w, CK2)], 'a1i', '%s e. RR' % CK2)], 'remulcld', '( %s x. %s ) e. RR' % (c0v, CK2)), c5vr, m5, m6], 'letrd', '%s <_ %s' % (P, c5v))
    m3w = st([m3lr, wr], 'remulcld', '( %s x. W ) e. RR' % M3L)
    m3rw = st([m3rr, wr], 'remulcld', '( %s x. W ) e. RR' % M3R)
    t0 = st([m3w, m3rw, pr, m4, eq], 'letrd', '( %s x. W ) <_ %s' % (M3L, P))
    t2 = st([m3w, pr, c5vr, t0, t1], 'letrd', '( %s x. W ) <_ %s' % (M3L, c5v))
    wgt = linarith(w, A, [w4], '0 < W', leaves=lv)
    bi = st([m3lr, c5vr, st([wr, wgt], 'elrpd', 'W e. RR+')], 'lemuldivd', '( ( %s x. W ) <_ %s <-> %s <_ ( %s / W ) )' % (M3L, c5v, M3L, c5v))
    w.qed([t2, bi], 'mpbid', STATEMENTS['bvharmnum'])
    return w



def subS(text, val):
    return ' '.join(val if t == 'S' else t for t in text.split())


def bvharm():
    w = W('bvharm', 'The unconditional harmonic bound (Lean bvHarm_uncond): at z1 = D ^c ( 31 / 50 ), z2 = D ^c ( 63 / 100 ) '
                    'and Y >= z1 >= 100, sum_ n <= Y a ( n ) ^ 2 / n <= 500000 log Y / ell (bvrankin at S = 1 + 1 / log Y, '
                    'bvaicc, bvtsumle, zserbnd, bvharmnum).')
    h1, h2, h3 = hyps_of(w, 'bvharm')
    A = HD
    st = mkst(w, A)
    hd = st([], 'simpl', '( D e. RR /\\ 1 < D )'); hr = st([], 'simpr', '( ; ; 1 0 0 <_ A /\\ ( Y e. RR /\\ A <_ Y ) )')
    dr = st([hd], 'simpld', 'D e. RR'); d1 = st([hd], 'simprd', '1 < D')
    a100 = st([hr], 'simpld', '; ; 1 0 0 <_ A'); hy = st([hr], 'simprd', '( Y e. RR /\\ A <_ Y )')
    yr = st([hy], 'simpld', 'Y e. RR'); ay = st([hy], 'simprd', 'A <_ Y')
    drp = st([dr, linarith(w, A, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    ldrp = st([dr, d1, w.inst('rplogcl')], 'syl2anc', '( log ` D ) e. RR+')
    ldr = st([ldrp], 'rpred', '( log ` D ) e. RR')
    W_ = ELLD
    wr = st([st([num.real(w, '( 1 / ; ; 1 0 0 )')], 'a1i', '( 1 / ; ; 1 0 0 ) e. RR'), ldr], 'remulcld', '%s e. RR' % W_)
    C31 = '( ; 3 1 / ; 5 0 )'; C63 = '( ; 6 3 / ; ; 1 0 0 )'
    ZA = '( D ^c %s )' % C31; ZB = '( D ^c %s )' % C63
    c31r = st([num.real(w, C31)], 'a1i', '%s e. RR' % C31); c63r = st([num.real(w, C63)], 'a1i', '%s e. RR' % C63)
    ea = w.s([h1], 'a1i', '( %s -> A = %s )' % (A, ZA))
    eb = w.s([h2], 'a1i', '( %s -> B = %s )' % (A, ZB))
    arp = st([ea, st([drp, c31r], 'rpcxpcld', '%s e. RR+' % ZA)], 'eqeltrd', 'A e. RR+')
    brp = st([eb, st([drp, c63r], 'rpcxpcld', '%s e. RR+' % ZB)], 'eqeltrd', 'B e. RR+')
    ar = st([arp], 'rpred', 'A e. RR'); br = st([brp], 'rpred', 'B e. RR')
    la = eqtr(w, A, [st([ea], 'fveq2d', '( log ` A ) = ( log ` %s )' % ZA), st([drp, c31r], 'logcxpd', '( log ` %s ) = ( %s x. ( log ` D ) )' % (ZA, C31))], None)
    lb = eqtr(w, A, [st([eb], 'fveq2d', '( log ` B ) = ( log ` %s )' % ZB), st([drp, c63r], 'logcxpd', '( log ` %s ) = ( %s x. ( log ` D ) )' % (ZB, C63))], None)
    lvD = {'( log ` D )': ldr}
    la62 = st([la, lineq(w, A, '( %s x. ( log ` D ) )' % C31, '( ; 6 2 x. %s )' % W_, leaves=lvD)], 'eqtrd', '( log ` A ) = ( ; 6 2 x. %s )' % W_)
    lb63 = st([lb, lineq(w, A, '( %s x. ( log ` D ) )' % C63, '( ; 6 3 x. %s )' % W_, leaves=lvD)], 'eqtrd', '( log ` B ) = ( ; 6 3 x. %s )' % W_)
    lt = st([st([le_lit2(w, C31, C63, strict=True)], 'a1i', '%s < %s' % (C31, C63)), st([dr, d1, c31r, c63r], 'cxpltd', '( %s < %s <-> %s < %s )' % (C31, C63, ZA, ZB))],
            'mpbid', '%s < %s' % (ZA, ZB))
    ab = st([st([ea, eb], 'breq12d', '( A < B <-> %s < %s )' % (ZA, ZB)), lt], 'mpbird', 'A < B')
    lvAB = {'A': ar, 'B': br, 'Y': yr}
    a1 = linarith(w, A, [a100], '1 <_ A', leaves=lvAB)
    hab = bind(w, A, bind(w, A, ar, a1, 'A e. RR', '1 <_ A'), bind(w, A, br, ab, 'B e. RR', 'A < B'), '( A e. RR /\\ 1 <_ A )', '( B e. RR /\\ A < B )')
    b1 = linarith(w, A, [a100, ab], '1 <_ B', leaves=lvAB)
    y1 = linarith(w, A, [a100, ay], '1 < Y', leaves=lvAB)
    yrp = st([yr, linarith(w, A, [a100, ay], '0 < Y', leaves=lvAB)], 'elrpd', 'Y e. RR+')
    V = '( log ` Y )'
    vrp = st([yr, y1, w.inst('rplogcl')], 'syl2anc', '%s e. RR+' % V); vr = st([vrp], 'rpred', '%s e. RR' % V)
    lay = st([ay, st([arp, yrp], 'logled', '( A <_ Y <-> ( log ` A ) <_ %s )' % V)], 'mpbid', '( log ` A ) <_ %s' % V)
    w62v = st([st([la62], 'eqcomd', '( ; 6 2 x. %s ) = ( log ` A )' % W_), lay], 'eqbrtrd', '( ; 6 2 x. %s ) <_ %s' % (W_, V))
    H = '; ; 1 0 0'
    l100 = st([a100, st([st([num.rp(w, H)], 'a1i', '%s e. RR+' % H), arp], 'logled', '( %s <_ A <-> ( log ` %s ) <_ ( log ` A ) )' % (H, H))], 'mpbid',
              '( log ` %s ) <_ ( log ` A )' % H)
    lhr = st([st([num.rp(w, H)], 'a1i', '%s e. RR+' % H)], 'relogcld', '( log ` %s ) e. RR' % H)
    lar = st([arp], 'relogcld', '( log ` A ) e. RR')
    w4a = st([st([num.real(w, '4')], 'a1i', '4 e. RR'), lhr, lar,
              st([clo(w, 'bvlog100', '4 <_ ( log ` %s )' % H)], 'a1i', '4 <_ ( log ` %s )' % H), l100], 'letrd', '4 <_ ( log ` A )')
    w4 = st([w4a, la62], 'breqtrd', '4 <_ ( ; 6 2 x. %s )' % W_)
    wrp = st([wr, linarith(w, A, [w4], '0 < %s' % W_, leaves={'( log ` D )': ldr})], 'elrpd', '%s e. RR+' % W_)
    # sigma
    U = '( 1 / %s )' % V
    urp = st([vrp], 'rpreccld', '%s e. RR+' % U); ur = st([urp], 'rpred', '%s e. RR' % U)
    srr = st([st([], '1red', '1 e. RR'), ur], 'readdcld', '%s e. RR' % SR)
    sr1 = linarith(w, A, [st([urp], 'rpgt0d', '0 < %s' % U)], '1 < %s' % SR, leaves={U: ur})
    hs1 = bind(w, A, srr, sr1, '%s e. RR' % SR, '1 < %s' % SR)
    # the diagonal bound at S = SR
    KBs = subS(KB, SR)
    TA = TSQ(SR, NB); TC = TSQC(SR, NB); ZSs = ZS(SR)
    NBL = '( 8 x. ( 1 + ( log ` %s ) ) )' % NB
    tl = w.s([h3], 'bvtsumle', '( ( %s /\\ ( %s e. RR /\\ 1 < %s ) ) -> ( %s /\\ %s <_ ( %s x. ( ( %s ^ 2 ) x. %s ) ) ) )' % (HAB, SR, SR, TC, TA, ZSs, KBs, NBL))
    tlv = st([bind(w, A, hab, hs1, HAB, '( %s e. RR /\\ 1 < %s )' % (SR, SR)), tl], 'syl', '( %s /\\ %s <_ ( %s x. ( ( %s ^ 2 ) x. %s ) ) )' % (TC, TA, ZSs, KBs, NBL))
    tcv = st([tlv], 'simpld', TC); tle = st([tlv], 'simprd', '%s <_ ( %s x. ( ( %s ^ 2 ) x. %s ) )' % (TA, ZSs, KBs, NBL))
    # bvA = ALs termwise
    tAl = lambda v, X: '( ( %s ^c -u %s ) x. ( %s ^ 2 ) )' % (v, SR, X)
    AN = '( %s /\\ n e. NN )' % A; sn = mkst(w, AN)
    nnn = sn([], 'simpr', 'n e. NN')
    aic = w.s([h3], 'bvaicc', '( ( %s /\\ n e. NN ) -> %s = %s )' % (HAB, BVA('n'), ALs('n', NB)))
    ai = sn([bind(w, AN, lift(w, hab, AN), nnn, HAB, 'n e. NN'), aic], 'syl', '%s = %s' % (BVA('n'), ALs('n', NB)))
    te = sn([sn([ai], 'oveq1d', '( %s ^ 2 ) = ( %s ^ 2 )' % (BVA('n'), ALs('n', NB)))], 'oveq2d', '%s = %s' % (tAl('n', BVA('n')), tAl('n', ALs('n', NB))))
    MB = '( n e. NN |-> %s )' % tAl('n', BVA('n')); MA = '( n e. NN |-> %s )' % tAl('n', ALs('n', NB))
    mp = st([te], 'mpteq2dva', '%s = %s' % (MB, MA))
    sqAB = st([mp], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (MB, MA))
    cvB = st([sqAB, tcv], 'eqeltrd',
                                                                                         'seq 1 ( + , %s ) e. dom ~~>' % MB)
    idnt = w.s([], 'id', '( n = t -> n = t )')
    cg, newt = w.congr(tAl('n', BVA('n')), {'n': 't'}, 'n = t', {'n': idnt})
    assert newt == tAl('t', BVA('t')), newt
    MT = '( t e. NN |-> %s )' % tAl('t', BVA('t'))
    cbm = w.s([cg], 'cbvmptv', '%s = %s' % (MB, MT))
    cvT = st([st([st([cbm], 'a1i', '%s = %s' % (MB, MT))], 'seqeq3d', 'seq 1 ( + , %s ) = seq 1 ( + , %s )' % (MB, MT)), cvB], 'eqeltrrd', 'seq 1 ( + , %s ) e. dom ~~>' % MT)
    cgb, bt = w.congr(BVA('n'), {'n': 't'}, 'n = t', {'n': idnt})
    assert bt == BVA('t'), bt
    # bvA real
    DVn = '{ x e. NN | x || n }'
    AND_ = '( %s /\\ d e. %s )' % (AN, DVn); snd = mkst(w, AND_)
    elr = w.s([w.s([], 'breq1', '( x = d -> ( x || n <-> d || n ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || n ) )' % DVn)
    dnn = snd([snd([snd([], 'simpr', 'd e. %s' % DVn), elr], 'sylib', '( d e. NN /\\ d || n )')], 'simpld', 'd e. NN')
    from zbv2_ssum import habfacts, lvfacts
    hfd = habfacts(w, AND_, lift(w, hab, AND_))
    ldr_ = lvfacts(w, AND_, h3, hfd, dnn, 'd')['lre']
    bar = sn([sy(w, AN, nnn, 'dvdsfi', '%s e. Fin' % DVn), ldr_], 'fsumrecl', '%s e. RR' % BVA('n'))
    rk = w.s([bind(w, A, yr, y1, 'Y e. RR', '1 < Y'), bar, cvT, cgb], 'bvrankin',
             '( %s -> sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( %s ^ 2 ) / n ) <_ ( ( exp ` 1 ) x. sum_ n e. NN %s ) )' % (A, BVA('n'), tAl('n', BVA('n'))))
    SB = 'sum_ n e. NN %s' % tAl('n', BVA('n'))
    sbe = st([te], 'sumeq2dv', '%s = %s' % (SB, TA))
    RB = '( %s x. ( ( %s ^ 2 ) x. %s ) )' % (ZSs, KBs, NBL)
    sble = st([sbe, tle], 'eqbrtrd', '%s <_ %s' % (SB, RB))
    # real closure of SB through the t-mapping
    ANt = '( %s /\\ n e. NN )' % A; snt = mkst(w, ANt)
    nsr = st([srr], 'renegcld', '-u %s e. RR' % SR)
    tbr = snt([snt([snt([snt([nnn], 'nnrpd', 'n e. RR+'), lift(w, nsr, ANt)], 'rpcxpcld', '( n ^c -u %s ) e. RR+' % SR)], 'rpred', '( n ^c -u %s ) e. RR' % SR),
               snt([bar], 'resqcld', '( %s ^ 2 ) e. RR' % BVA('n'))], 'remulcld', '%s e. RR' % tAl('n', BVA('n')))
    vt, _ = mpv(w, ANt, 't', 'NN', tAl('t', BVA('t')), 'n', nnn)
    sbr = st([clo(w, 'nnuz', 'NN = ( ZZ>= ` 1 )'), st([], '1zzd', '1 e. ZZ'), vt, tbr, cvT], 'isumrecl', '%s e. RR' % SB)
    # the numeral lemma's premises
    E1 = '( exp ` 1 )'
    er = st([st([], '1red', '1 e. RR')], 'reefcld', '%s e. RR' % E1)
    e0 = st([st([st([], '1red', '1 e. RR')], 'rpefcld', '%s e. RR+' % E1)], 'rpge0d', '0 <_ %s' % E1)
    eb = st([clo(w, 'bvebnd', '%s <_ ( ; 2 9 / ; 1 0 )' % E1)], 'a1i', '%s <_ ( ; 2 9 / ; 1 0 )' % E1)
    zr = st([hs1, w.inst('zetasumcl')], 'syl', '%s e. RR' % ZSs)
    ZT = '( t e. NN |-> ( t ^c -u %s ) )' % SR
    zv, _ = mpv(w, ANt, 't', 'NN', '( t ^c -u %s )' % SR, 'n', nnn)
    nsp = snt([snt([nnn], 'nnrpd', 'n e. RR+'), lift(w, nsr, ANt)], 'rpcxpcld', '( n ^c -u %s ) e. RR+' % SR)
    z0 = st([clo(w, 'nnuz', 'NN = ( ZZ>= ` 1 )'), st([], '1zzd', '1 e. ZZ'), zv, snt([nsp], 'rpred', '( n ^c -u %s ) e. RR' % SR),
             st([hs1, w.inst('zetacvg1')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % ZT), snt([nsp], 'rpge0d', '0 <_ ( n ^c -u %s )' % SR)], 'isumge0', '0 <_ %s' % ZSs)
    zsb = st([hs1, w.inst('zserbnd')], 'syl', 'sum_ k e. NN ( k ^c -u %s ) <_ ( 1 + ( 1 / ( %s - 1 ) ) )' % (SR, SR))
    idkn = w.s([], 'id', '( k = n -> k = n )')
    cgk, nk = w.congr('( k ^c -u %s )' % SR, {'k': 'n'}, 'k = n', {'k': idkn})
    cbk = st([w.s([cgk], 'cbvsumv', 'sum_ k e. NN ( k ^c -u %s ) = %s' % (SR, ZSs))], 'a1i', 'sum_ k e. NN ( k ^c -u %s ) = %s' % (SR, ZSs))
    sm1 = lineq(w, A, '( %s - 1 )' % SR, U, leaves={U: ur})
    rr = eqtr(w, A, [st([sm1], 'oveq2d', '( 1 / ( %s - 1 ) ) = ( 1 / %s )' % (SR, U)), st([st([vrp], 'rpcnd', '%s e. CC' % V), st([vrp], 'rpne0d', '%s =/= 0' % V)], 'recrecd',
                                                                                                                    '( 1 / %s ) = %s' % (U, V))], None)
    zb = st([st([cbk, zsb], 'eqbrtrrd', '%s <_ ( 1 + ( 1 / ( %s - 1 ) ) )' % (ZSs, SR)), st([rr], 'oveq2d', '( 1 + ( 1 / ( %s - 1 ) ) ) = ( 1 + %s )' % (SR, V))],
            'breqtrd', '%s <_ ( 1 + %s )' % (ZSs, V))
    # K
    LG = LGAB
    lg = eqtr(w, A, [st([brp, arp], 'relogdivd', '%s = ( ( log ` B ) - ( log ` A ) )' % LG),
                     lineq(w, A, '( ( log ` B ) - ( log ` A ) )', W_, hyps=[lb63, la62], leaves={'( log ` B )': st([brp], 'relogcld', '( log ` B ) e. RR'),
                                                                                                 '( log ` A )': lar, '( log ` D )': ldr})], None)
    WB = subS('( 1 + ( ( S - 1 ) x. ( log ` B ) ) )', SR)
    NUM = '( ( ; 2 2 / 3 ) x. %s )' % WB
    Q = '( ( %s - 1 ) x. ( log ` B ) )' % SR
    lbr = st([brp], 'relogcld', '( log ` B ) e. RR')
    q1 = st([sm1], 'oveq1d', '%s = ( %s x. ( log ` B ) )' % (Q, U))
    q2 = st([st([lbr], 'recnd', '( log ` B ) e. CC'), st([vrp], 'rpcnd', '%s e. CC' % V), st([vrp], 'rpne0d', '%s =/= 0' % V)], 'divrec2d',
            '( ( log ` B ) / %s ) = ( %s x. ( log ` B ) )' % (V, U))
    qe = st([q1, st([q2], 'eqcomd', '( %s x. ( log ` B ) ) = ( ( log ` B ) / %s )' % (U, V))], 'eqtrd', '%s = ( ( log ` B ) / %s )' % (Q, V))
    C6362 = '( ; 6 3 / ; 6 2 )'
    lbv = linarith(w, A, [lb63, w62v], '( log ` B ) <_ ( %s x. %s )' % (V, C6362), leaves={'( log ` B )': lbr, '( log ` D )': ldr, V: vr})
    qb0 = st([lbv, st([lbr, st([num.real(w, C6362)], 'a1i', '%s e. RR' % C6362), vrp], 'ledivmuld', '( ( ( log ` B ) / %s ) <_ %s <-> ( log ` B ) <_ ( %s x. %s ) )' % (V, C6362, V, C6362))],
             'mpbird', '( ( log ` B ) / %s ) <_ %s' % (V, C6362))
    qb = st([qe, qb0], 'eqbrtrd', '%s <_ %s' % (Q, C6362))
    lb0 = st([bind(w, A, br, b1, 'B e. RR', '1 <_ B'), w.inst('logge0')], 'syl', '0 <_ ( log ` B )')
    dv0 = st([lbr, vrp, lb0], 'divge0d', '0 <_ ( ( log ` B ) / %s )' % V)
    q0 = st([dv0, qe], 'breqtrrd', '0 <_ %s' % Q)
    qr = st([st([srr, st([], '1red', '1 e. RR')], 'resubcld', '( %s - 1 ) e. RR' % SR), lbr], 'remulcld', '%s e. RR' % Q)
    numr = st([st([num.real(w, '( ; 2 2 / 3 )')], 'a1i', '( ; 2 2 / 3 ) e. RR'), st([st([], '1red', '1 e. RR'), qr], 'readdcld', '%s e. RR' % WB)], 'remulcld', '%s e. RR' % NUM)
    CK = '( ; ; ; 1 3 7 5 / ; 9 3 )'
    numb = linarith(w, A, [qb], '%s <_ %s' % (NUM, CK), leaves={Q: qr})
    num0 = linarith(w, A, [q0], '0 <_ %s' % NUM, leaves={Q: qr})
    kbe = st([lg], 'oveq2d', '%s = ( %s / %s )' % (KBs, NUM, W_))
    kbr = st([numr, wr, st([wrp], 'rpne0d', '%s =/= 0' % W_)], 'redivcld', '( %s / %s ) e. RR' % (NUM, W_))
    kbr2 = st([kbe, kbr], 'eqeltrd', '%s e. RR' % KBs)
    kb0 = st([st([numr, wrp, num0], 'divge0d', '0 <_ ( %s / %s )' % (NUM, W_)), kbe], 'breqtrrd', '0 <_ %s' % KBs)
    kw = eqtr(w, A, [st([kbe], 'oveq1d', '( %s x. %s ) = ( ( %s / %s ) x. %s )' % (KBs, W_, NUM, W_, W_)),
                     st([st([numr], 'recnd', '%s e. CC' % NUM), st([wrp], 'rpcnd', '%s e. CC' % W_), st([wrp], 'rpne0d', '%s =/= 0' % W_)], 'divcan1d',
                        '( ( %s / %s ) x. %s ) = %s' % (NUM, W_, W_, NUM))], None)
    kwb = st([kw, numb], 'eqbrtrd', '( %s x. %s ) <_ %s' % (KBs, W_, CK))
    # G
    G = '( log ` %s )' % NB
    nbn = st([br, b1, w.inst('flge1nn')], 'syl2anc', '%s e. NN' % NB)
    nbrp = st([nbn], 'nnrpd', '%s e. RR+' % NB)
    gr = st([nbrp], 'relogcld', '%s e. RR' % G)
    g0 = st([bind(w, A, st([nbn], 'nnred', '%s e. RR' % NB), st([nbn], 'nnge1d', '1 <_ %s' % NB), '%s e. RR' % NB, '1 <_ %s' % NB), w.inst('logge0')], 'syl', '0 <_ %s' % G)
    glb = st([sy(w, A, br, 'flle', '%s <_ B' % NB), st([nbrp, brp], 'logled', '( %s <_ B <-> %s <_ ( log ` B ) )' % (NB, G))], 'mpbid', '%s <_ ( log ` B )' % G)
    gb = st([glb, lb63], 'breqtrd', '%s <_ ( ; 6 3 x. %s )' % (G, W_))
    prem = '( ( ( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( ; 2 9 / ; 1 0 ) ) /\\ ( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( 1 + %s ) ) ) /\\ ( ( %s e. RR /\\ 0 <_ %s /\\ ( %s x. %s ) <_ %s ) /\\ ( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( ; 6 3 x. %s ) ) /\\ ( ( %s e. RR /\\ %s e. RR ) /\\ ( 4 <_ ( ; 6 2 x. %s ) /\\ ( ; 6 2 x. %s ) <_ %s ) ) ) )' % (
        E1, E1, E1, ZSs, ZSs, ZSs, V, KBs, KBs, KBs, W_, CK, G, G, G, W_, W_, V, W_, W_, V)
    p1 = bind(w, A, bind3(w, A, er, e0, eb, '%s e. RR' % E1, '0 <_ %s' % E1, '%s <_ ( ; 2 9 / ; 1 0 )' % E1),
              bind3(w, A, zr, z0, zb, '%s e. RR' % ZSs, '0 <_ %s' % ZSs, '%s <_ ( 1 + %s )' % (ZSs, V)),
              '( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( ; 2 9 / ; 1 0 ) )' % (E1, E1, E1), '( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( 1 + %s ) )' % (ZSs, ZSs, ZSs, V))
    pk = bind3(w, A, kbr2, kb0, kwb, '%s e. RR' % KBs, '0 <_ %s' % KBs, '( %s x. %s ) <_ %s' % (KBs, W_, CK))
    pg = bind3(w, A, gr, g0, gb, '%s e. RR' % G, '0 <_ %s' % G, '%s <_ ( ; 6 3 x. %s )' % (G, W_))
    pw = bind(w, A, bind(w, A, wr, vr, '%s e. RR' % W_, '%s e. RR' % V), bind(w, A, w4, w62v, '4 <_ ( ; 6 2 x. %s )' % W_, '( ; 6 2 x. %s ) <_ %s' % (W_, V)),
              '( %s e. RR /\\ %s e. RR )' % (W_, V), '( 4 <_ ( ; 6 2 x. %s ) /\\ ( ; 6 2 x. %s ) <_ %s )' % (W_, W_, V))
    p2 = bind3(w, A, pk, pg, pw, '( %s e. RR /\\ 0 <_ %s /\\ ( %s x. %s ) <_ %s )' % (KBs, KBs, KBs, W_, CK), '( %s e. RR /\\ 0 <_ %s /\\ %s <_ ( ; 6 3 x. %s ) )' % (G, G, G, W_),
               '( ( %s e. RR /\\ %s e. RR ) /\\ ( 4 <_ ( ; 6 2 x. %s ) /\\ ( ; 6 2 x. %s ) <_ %s ) )' % (W_, V, W_, W_, V))
    pall = w.s([p1, p2], 'jca', '( %s -> %s )' % (A, prem))
    TGT = '( ( %s x. %s ) / %s )' % (C5, V, W_)
    hn = st([pall, w.inst('bvharmnum')], 'syl', '( %s x. %s ) <_ %s' % (E1, RB, TGT))
    rbr = st([zr, st([st([kbr2], 'resqcld', '( %s ^ 2 ) e. RR' % KBs),
                      st([st([clo(w, '8re', '8 e. RR')], 'a1i', '8 e. RR'), st([st([], '1red', '1 e. RR'), gr], 'readdcld', '( 1 + %s ) e. RR' % G)], 'remulcld', '%s e. RR' % NBL)],
                     'remulcld', '( ( %s ^ 2 ) x. %s ) e. RR' % (KBs, NBL))], 'remulcld', '%s e. RR' % RB)
    m = st([sbr, rbr, er, e0, sble], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (E1, SB, E1, RB))
    srhs = st([er, sbr], 'remulcld', '( %s x. %s ) e. RR' % (E1, SB))
    t1 = st([srhs, st([er, rbr], 'remulcld', '( %s x. %s ) e. RR' % (E1, RB)), st([st([st([num.real(w, C5)], 'a1i', '%s e. RR' % C5), vr], 'remulcld', '( %s x. %s ) e. RR' % (C5, V)), wr, st([wrp], 'rpne0d', '%s =/= 0' % W_)], 'redivcld', '%s e. RR' % TGT),
             m, hn], 'letrd', '( %s x. %s ) <_ %s' % (E1, SB, TGT))
    # the finite sum is real
    AF = '( %s /\\ n e. ( 1 ... ( |_ ` Y ) ) )' % A; sf = mkst(w, AF)
    fnn = sy(w, AF, sf([], 'simpr', 'n e. ( 1 ... ( |_ ` Y ) )'), 'elfznn', 'n e. NN')
    hfd2 = habfacts(w, '( %s /\\ d e. { x e. NN | x || n } )' % AF, lift(w, hab, '( %s /\\ d e. { x e. NN | x || n } )' % AF))
    ADF = '( %s /\\ d e. { x e. NN | x || n } )' % AF; sdf = mkst(w, ADF)
    dnnf = sdf([sdf([sdf([], 'simpr', 'd e. %s' % DVn), elr], 'sylib', '( d e. NN /\\ d || n )')], 'simpld', 'd e. NN')
    ldf = lvfacts(w, ADF, h3, hfd2, dnnf, 'd')['lre']
    barf = sf([sy(w, AF, fnn, 'dvdsfi', '%s e. Fin' % DVn), ldf], 'fsumrecl', '%s e. RR' % BVA('n'))
    fr = st([st([], 'fzfid', '( 1 ... ( |_ ` Y ) ) e. Fin'), sf([sf([barf], 'resqcld', '( %s ^ 2 ) e. RR' % BVA('n')), sf([fnn], 'nnrpd', 'n e. RR+')], 'rerpdivcld',
                                                                                                '( ( %s ^ 2 ) / n ) e. RR' % BVA('n'))],
            'fsumrecl', 'sum_ n e. ( 1 ... ( |_ ` Y ) ) ( ( %s ^ 2 ) / n ) e. RR' % BVA('n'))
    w.qed([fr, srhs, st([st([st([num.real(w, C5)], 'a1i', '%s e. RR' % C5), vr], 'remulcld', '( %s x. %s ) e. RR' % (C5, V)), wr, st([wrp], 'rpne0d', '%s =/= 0' % W_)],
                        'redivcld', '%s e. RR' % TGT), rk, t1], 'letrd', STATEMENTS['bvharm'])
    return w



def bvl2star():
    w = W('bvl2star', 'UNCONDITIONAL I4* (Lean bvL2_star_uncond): at z1 = D ^c ( 31 / 50 ), z2 = D ^c ( 63 / 100 ), for '
                      'Y >= z1 >= 100 and 1 / 2 <= T <= 1: sum_ n <= Y n ^c ( 1 - 2 T ) a ( n ) ^ 2 <= 500000 Y ^c ( 2 - 2 T ) '
                      'log Y / ell (bvrankina, bvharm).')
    h1, h2, h3 = hyps_of(w, 'bvl2star')
    HT = '( T e. RR /\\ ( ( 1 / 2 ) <_ T /\\ T <_ 1 ) )'
    A = '( %s /\\ %s )' % (HD, HT)
    st = mkst(w, A)
    hd_ = st([], 'simpl', HD); ht = st([], 'simpr', HT)
    tr = st([ht], 'simpld', 'T e. RR'); t1 = st([st([ht], 'simprd', '( ( 1 / 2 ) <_ T /\\ T <_ 1 )')], 'simprd', 'T <_ 1')
    hdd = st([hd_], 'simpld', '( D e. RR /\\ 1 < D )')
    hr = st([hd_], 'simprd', '( ; ; 1 0 0 <_ A /\\ ( Y e. RR /\\ A <_ Y ) )')
    dr = st([hdd], 'simpld', 'D e. RR'); d1 = st([hdd], 'simprd', '1 < D')
    a100 = st([hr], 'simpld', '; ; 1 0 0 <_ A'); hy = st([hr], 'simprd', '( Y e. RR /\\ A <_ Y )')
    yr = st([hy], 'simpld', 'Y e. RR'); ay = st([hy], 'simprd', 'A <_ Y')
    drp = st([dr, linarith(w, A, [d1], '0 < D', leaves={'D': dr})], 'elrpd', 'D e. RR+')
    C31 = '( ; 3 1 / ; 5 0 )'; C63 = '( ; 6 3 / ; ; 1 0 0 )'
    ZA = '( D ^c %s )' % C31; ZB = '( D ^c %s )' % C63
    c31r = st([num.real(w, C31)], 'a1i', '%s e. RR' % C31); c63r = st([num.real(w, C63)], 'a1i', '%s e. RR' % C63)
    ea = w.s([h1], 'a1i', '( %s -> A = %s )' % (A, ZA)); eb = w.s([h2], 'a1i', '( %s -> B = %s )' % (A, ZB))
    arp = st([ea, st([drp, c31r], 'rpcxpcld', '%s e. RR+' % ZA)], 'eqeltrd', 'A e. RR+')
    brp = st([eb, st([drp, c63r], 'rpcxpcld', '%s e. RR+' % ZB)], 'eqeltrd', 'B e. RR+')
    ar = st([arp], 'rpred', 'A e. RR'); br = st([brp], 'rpred', 'B e. RR')
    lt = st([st([le_lit2(w, C31, C63, strict=True)], 'a1i', '%s < %s' % (C31, C63)), st([dr, d1, c31r, c63r], 'cxpltd', '( %s < %s <-> %s < %s )' % (C31, C63, ZA, ZB))],
            'mpbid', '%s < %s' % (ZA, ZB))
    ab = st([st([ea, eb], 'breq12d', '( A < B <-> %s < %s )' % (ZA, ZB)), lt], 'mpbird', 'A < B')
    lvAB = {'A': ar, 'B': br, 'Y': yr}
    a1 = linarith(w, A, [a100], '1 <_ A', leaves=lvAB)
    hab = bind(w, A, bind(w, A, ar, a1, 'A e. RR', '1 <_ A'), bind(w, A, br, ab, 'B e. RR', 'A < B'), '( A e. RR /\\ 1 <_ A )', '( B e. RR /\\ A < B )')
    y1 = linarith(w, A, [a100, ay], '1 <_ Y', leaves=lvAB)
    yrp = st([yr, linarith(w, A, [a100, ay], '0 < Y', leaves=lvAB)], 'elrpd', 'Y e. RR+')
    R = '( 1 ... ( |_ ` Y ) )'
    AF = '( %s /\\ n e. %s )' % (A, R); sf = mkst(w, AF)
    fnn = sy(w, AF, sf([], 'simpr', 'n e. %s' % R), 'elfznn', 'n e. NN')
    DVn = '{ x e. NN | x || n }'
    ADF = '( %s /\\ d e. %s )' % (AF, DVn); sdf = mkst(w, ADF)
    elr = w.s([w.s([], 'breq1', '( x = d -> ( x || n <-> d || n ) )')], 'elrab', '( d e. %s <-> ( d e. NN /\\ d || n ) )' % DVn)
    dnnf = sdf([sdf([sdf([], 'simpr', 'd e. %s' % DVn), elr], 'sylib', '( d e. NN /\\ d || n )')], 'simpld', 'd e. NN')
    from zbv2_ssum import habfacts, lvfacts
    hfd = habfacts(w, ADF, lift(w, hab, ADF))
    ldf = lvfacts(w, ADF, h3, hfd, dnnf, 'd')['lre']
    barf = sf([sy(w, AF, fnn, 'dvdsfi', '%s e. Fin' % DVn), ldf], 'fsumrecl', '%s e. RR' % BVA('n'))
    B2 = '( 2 - ( 2 x. T ) )'; B1 = '( 1 - ( 2 x. T ) )'
    YB = '( Y ^c %s )' % B2
    S2 = 'sum_ n e. %s ( ( %s ^ 2 ) / n )' % (R, BVA('n'))
    ra = w.s([bind(w, A, yr, y1, 'Y e. RR', '1 <_ Y'), bind(w, A, tr, t1, 'T e. RR', 'T <_ 1'), barf], 'bvrankina',
             '( %s -> sum_ n e. %s ( ( n ^c %s ) x. ( %s ^ 2 ) ) <_ ( %s x. %s ) )' % (A, R, B1, BVA('n'), YB, S2))
    V = '( log ` Y )'; W_ = ELLD
    TG = '( ( %s x. %s ) / %s )' % (C5, V, W_)
    hm = w.s([h1, h2, h3], 'bvharm', '( %s -> %s <_ %s )' % (HD, S2, TG))
    hmv = st([hd_, hm], 'syl', '%s <_ %s' % (S2, TG))
    s2r = st([st([], 'fzfid', '%s e. Fin' % R), sf([sf([barf], 'resqcld', '( %s ^ 2 ) e. RR' % BVA('n')), sf([fnn], 'nnrpd', 'n e. RR+')], 'rerpdivcld',
                                                                             '( ( %s ^ 2 ) / n ) e. RR' % BVA('n'))], 'fsumrecl', '%s e. RR' % S2)
    ldrp = st([dr, d1, w.inst('rplogcl')], 'syl2anc', '( log ` D ) e. RR+')
    ldr = st([ldrp], 'rpred', '( log ` D ) e. RR')
    wr = st([st([num.real(w, '( 1 / ; ; 1 0 0 )')], 'a1i', '( 1 / ; ; 1 0 0 ) e. RR'), ldr], 'remulcld', '%s e. RR' % W_)
    wgt = linarith(w, A, [st([ldrp], 'rpgt0d', '0 < ( log ` D )')], '0 < %s' % W_, leaves={'( log ` D )': ldr})
    wrp = st([wr, wgt], 'elrpd', '%s e. RR+' % W_)
    vr = st([yrp], 'relogcld', '%s e. RR' % V)
    c5r = st([num.real(w, C5)], 'a1i', '%s e. RR' % C5)
    CV = '( %s x. %s )' % (C5, V)
    cvr = st([c5r, vr], 'remulcld', '%s e. RR' % CV)
    tgr = st([cvr, wrp], 'rerpdivcld', '%s e. RR' % TG)
    b2r = st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')],
             'resubcld', '%s e. RR' % B2)
    ybrp = st([yrp, b2r], 'rpcxpcld', '%s e. RR+' % YB)
    ybr = st([ybrp], 'rpred', '%s e. RR' % YB)
    m = st([s2r, tgr, ybr, st([ybrp], 'rpge0d', '0 <_ %s' % YB), hmv], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (YB, S2, YB, TG))
    RHS = '( ( ( %s x. %s ) x. %s ) / %s )' % (C5, YB, V, W_)
    e1 = st([st([st([ybr], 'recnd', '%s e. CC' % YB), st([cvr], 'recnd', '%s e. CC' % CV), st([wrp], 'rpcnd', '%s e. CC' % W_), st([wrp], 'rpne0d', '%s =/= 0' % W_)],
                'divassd', '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (YB, CV, W_, YB, TG))], 'eqcomd', '( %s x. %s ) = ( ( %s x. %s ) / %s )' % (YB, TG, YB, CV, W_))
    e2 = st([lineq(w, A, '( %s x. %s )' % (YB, CV), '( ( %s x. %s ) x. %s )' % (C5, YB, V), products=True, leaves={YB: ybr, V: vr}, atoms=[YB, V])], 'oveq1d',
            '( ( %s x. %s ) / %s ) = %s' % (YB, CV, W_, RHS))
    t = st([m, st([e1, e2], 'eqtrd', '( %s x. %s ) = %s' % (YB, TG, RHS))], 'breqtrd', '( %s x. %s ) <_ %s' % (YB, S2, RHS))
    b1r = st([st([], '1red', '1 e. RR'), st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')], 'resubcld', '%s e. RR' % B1)
    tn = '( ( n ^c %s ) x. ( %s ^ 2 ) )' % (B1, BVA('n'))
    tnr = sf([sf([sf([sf([fnn], 'nnrpd', 'n e. RR+'), lift(w, b1r, AF)], 'rpcxpcld', '( n ^c %s ) e. RR+' % B1)], 'rpred', '( n ^c %s ) e. RR' % B1),
              sf([barf], 'resqcld', '( %s ^ 2 ) e. RR' % BVA('n'))], 'remulcld', '%s e. RR' % tn)
    lr = st([st([], 'fzfid', '%s e. Fin' % R), tnr], 'fsumrecl', 'sum_ n e. %s %s e. RR' % (R, tn))
    mr = st([ybr, s2r], 'remulcld', '( %s x. %s ) e. RR' % (YB, S2))
    rr = st([st([st([c5r, ybr], 'remulcld', '( %s x. %s ) e. RR' % (C5, YB)), vr], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (C5, YB, V)), wrp], 'rerpdivcld', '%s e. RR' % RHS)
    w.qed([lr, mr, rr, ra, t], 'letrd', STATEMENTS['bvl2star'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvebnd', 'bvlog100']:
        (runh if HYPS.get(f) else (lambda w: w.run()))(globals()[f]())
