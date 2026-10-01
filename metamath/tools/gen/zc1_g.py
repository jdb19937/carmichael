"""Sortie ZC1: the Landau expansion with the square count built in (lndk), its eta and gFun instances (lndeta, lndgf)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zc1lib import *
from cl import lift
import num
from c8_o import numst, sqab_st
from c8_n import sqparts, sqre_at, sqcc
from c10_f import crfacts, clo
import c9_h
patch(c9_h)
from c9_h import c0_facts
import zc1_d, zc1_e, zc1_f
from zc1_e import AT2, l25rp
import lin
lin.FASTPATH = True

KNUM = '; ; ; ; ; ; ; 1 7 5 0 0 0 0 0'
W8 = '( ; ; 8 0 0 x. ( log ` X ) )'


def LHSF(F, t, S_='S'):
    Z = ZS(F, t)
    return '( abs ` ( ( ( ( CC _D %s ) ` %s ) / ( %s ` %s ) ) - sum_ q e. %s ( ( %s holord q ) / ( %s - q ) ) ) )' % (F, S_, F, S_, Z, F, S_)


SD = '( S e. CC /\\ ( abs ` ( S - %s ) ) <_ ( 3 / 2 ) /\\ ( F ` S ) =/= 0 )' % CT('T')
S['lndk'] = ('( ( ( %s /\\ T e. RR ) /\\ ( ( X e. RR /\\ 2 <_ X ) /\\ ( B e. RR+ /\\ A. x e. %s ( abs ` ( F ` x ) ) <_ B ) /\\ '
             '( M e. RR+ /\\ M <_ ( abs ` ( F ` %s ) ) /\\ ( B / M ) <_ ( ; ; 1 2 8 x. X ) ) ) /\\ ( %s <_ %s /\\ %s ) ) -> %s <_ ( %s x. ( log ` X ) ) )') % (
    HOLF('F', HP0), RCT('T'), CT('T'), MASS(ZS('F', 'T'), 'F'), W8, SD, LHSF('F', 'T'), KNUM)
SDE = lambda F: '( S e. CC /\\ ( abs ` ( S - %s ) ) <_ ( 3 / 2 ) /\\ ( %s ` S ) =/= 0 )' % (CT('T'), F)
S['lndeta'] = '( ( T e. RR /\\ %s ) -> %s <_ ( %s x. ( log ` %s ) ) )' % (SDE(ETA), LHSF(ETA, 'T'), KNUM, AT2)
S['lndgf'] = '( ( T e. RR /\\ %s ) -> %s <_ ( %s x. ( log ` %s ) ) )' % (SDE(GF), LHSF(GF, 'T'), KNUM, AT2)


def gen_lndk():
    w = W('lndk', 'The Landau expansion on the square about ` 2 + i T ` with the constant ` 17500000 log X ` : ~ lndgen with the bound ` B ` taken from the rectangle ` [ 1 / 4 , 15 / 4 ] x. [ T - 3 , T + 3 ] ` , the centre bound ` M ` , ` B / M <_ 128 X ` and the square mass ` <_ 800 log X ` (the numerals of C10\'s ~ lndlchrk for a generic ` F ` ).')
    A0, GC = ante_of(S['lndk'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2, X3 = top_and(A0)
    x1 = s([], 'simp1', X1); x2 = s([], 'simp2', X2); x3 = s([], 'simp3', X3)
    hol = s([x1, w.inst('simpl')], 'syl', HOLF('F', HP0)); tr = s([x1, w.inst('simpr')], 'syl', 'T e. RR')
    P1, P2, P3 = top_and(X2)
    p1 = s([x2, w.inst('simp1')], 'syl', P1); p2 = s([x2, w.inst('simp2')], 'syl', P2); p3 = s([x2, w.inst('simp3')], 'syl', P3)
    xr = s([p1, w.inst('simpl')], 'syl', 'X e. RR'); x2_ = s([p1, w.inst('simpr')], 'syl', '2 <_ X')
    brp = s([p2, w.inst('simpl')], 'syl', 'B e. RR+'); fbx = s([p2, w.inst('simpr')], 'syl', top_and(P2)[1])
    mrp = s([p3, w.inst('simp1')], 'syl', 'M e. RR+'); mle = s([p3, w.inst('simp2')], 'syl', top_and(P3)[1]); bmx = s([p3, w.inst('simp3')], 'syl', top_and(P3)[2])
    mass = s([x3, w.inst('simpl')], 'syl', top_and(X3)[0]); sd = s([x3, w.inst('simpr')], 'syl', SD)
    c0, re0, im0 = c0_facts(w, A0, tr)
    r74 = numst(w, A0, R74, 'RR')
    # SQ ( C0 , 7 / 4 ) C_ HP0 and C_ RCT
    lt = s([lin8(w, A0, [], '%s < 2' % R74, {}), re0], 'breqtrrd', '%s < ( Re ` %s )' % (R74, C0))
    f = tsub(stmt('sqhp0'), {'C': C0, 'R': R74})
    fa, fc = ante_of(f)
    shp = s([s([s([c0, r74], 'jca', '( %s e. CC /\\ %s e. RR )' % (C0, R74)), lt], 'jca', fa), w.inst('sqhp0')], 'syl', fc)
    RA, RB = '( ( 1 / 4 ) + ( _i x. ( T - 3 ) ) )', '( ( ; 1 5 / 4 ) + ( _i x. ( T + 3 ) ) )'
    t3a = s([tr, numst(w, A0, '3', 'RR')], 'resubcld', '( T - 3 ) e. RR')
    t3b = s([tr, numst(w, A0, '3', 'RR')], 'readdcld', '( T + 3 ) e. RR')
    rac, rreA, rimA = crfacts(w, A0, '( 1 / 4 )', '( T - 3 )', numst(w, A0, '( 1 / 4 )', 'RR'), t3a)
    rbc, rreB, rimB = crfacts(w, A0, '( ; 1 5 / 4 )', '( T + 3 )', numst(w, A0, '( ; 1 5 / 4 )', 'RR'), t3b)
    SA, SB = SQA(C0, R74), SQB(C0, R74)
    sa, sb = sqcc(w, A0, c0, r74, c=C0, r=R74)
    ps = sqparts(w, A0, sqre_at(w, A0, c0, r74, c=C0, r=R74), c=C0, r=R74)
    lv = {'T': tr}
    for e, st in (('( Re ` %s )' % C0, c0), ('( Im ` %s )' % C0, c0), ('( Re ` %s )' % SA, sa), ('( Im ` %s )' % SA, sa), ('( Re ` %s )' % SB, sb), ('( Im ` %s )' % SB, sb),
                  ('( Re ` %s )' % RA, rac), ('( Im ` %s )' % RA, rac), ('( Re ` %s )' % RB, rbc), ('( Im ` %s )' % RB, rbc)):
        lv[e] = s([st], 'recld' if e.startswith('( Re') else 'imcld', '%s e. RR' % e)
    hy = [re0, im0, rreA, rimA, rreB, rimB] + ps
    CS = tsub(stmt('crectss2'), {'A': RA, 'B': RB, 'C': SA, 'E': SB})
    csa, csc = ante_of(CS)
    Z1, Z2, Z3 = top_and(csa)
    ii = [lin8(w, A0, hy, g, lv) for g in ('( Re ` %s ) <_ ( Re ` %s )' % (RA, SA), '( Re ` %s ) <_ ( Re ` %s )' % (SB, RB),
                                              '( Im ` %s ) <_ ( Im ` %s )' % (RA, SA), '( Im ` %s ) <_ ( Im ` %s )' % (SB, RB))]
    sub = s([s([s([rac, rbc], 'jca', Z1), s([sa, sb], 'jca', Z2), s([s([ii[0], ii[1]], 'jca', top_and(Z3)[0]), s([ii[2], ii[3]], 'jca', top_and(Z3)[1])], 'jca', Z3)], '3jca', csa),
               w.inst('crectss2')], 'syl', csc)
    SQ74_ = SQ(C0, R74)
    fb74 = s([sub, fbx, w.inst('ssralv')], 'sylc', 'A. x e. %s ( abs ` ( F ` x ) ) <_ B' % SQ74_)
    # F ( C0 ) =/= 0
    LC = '( F ` %s )' % C0; ALC = '( abs ` %s )' % LC
    ch = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (C0, HP0, C0, C0))
    c0h = s([s([c0, s([lin8(w, A0, [], '0 < 2', {}), re0], 'breqtrrd', '0 < ( Re ` %s )' % C0)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (C0, C0)), ch], 'mpbird', '%s e. %s' % (C0, HP0))
    lfc = s([s([s([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), c0h], 'ffvelcdmd', '%s e. CC' % LC)
    alr = s([lfc], 'abscld', '%s e. RR' % ALC)
    mr = s([mrp], 'rpred', 'M e. RR')
    apos = lin8(w, A0, [mle, s([mrp], 'rpgt0d', '0 < M')], '0 < %s' % ALC, {ALC: alr, 'M': mr})
    lne = s([apos, s([lfc, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < %s )' % (LC, ALC))], 'mpbird', '%s =/= 0' % LC)
    # W e. RR+
    LX = '( log ` X )'
    xp = s([xr, lin8(w, A0, [x2_], '0 < X', {'X': xr})], 'elrpd', 'X e. RR+')
    lxp = s([s([xp], 'relogcld', '%s e. RR' % LX), s([s([xp, w.inst('loggt0b')], 'syl', '( 0 < %s <-> 1 < X )' % LX), lin8(w, A0, [x2_], '1 < X', {'X': xr})], 'mpbird', '0 < %s' % LX)], 'elrpd', '%s e. RR+' % LX)
    wp = s([numst(w, A0, '; ; 8 0 0', 'RR+'), lxp], 'rpmulcld', '%s e. RR+' % W8)
    LG = tsub(stmt('lndgen'), {'D': HP0, 'C': C0, 'W': W8})
    la, lc = ante_of(LG)
    L1, L2, L3 = top_and(la)
    br = s([brp], 'rpred', 'B e. RR')
    l1 = s([hol, s([c0, shp], 'jca', top_and(L1)[1])], 'jca', L1)
    l2 = s([s([br, fb74], 'jca', top_and(L2)[0]), s([lne, s([wp, mass], 'jca', top_and(top_and(L2)[1])[1])], 'jca', top_and(L2)[1])], 'jca', L2)
    lg = s([s([l1, l2, sd], '3jca', la), w.inst('lndgen')], 'syl', lc)
    LHS, RHS0 = lc.split(' <_ ', 1)
    # numerals
    two = numst(w, A0, '2', 'RR+')
    L2_ = '( log ` 2 )'
    def logpow(c, n, lab, P):
        cp = numst(w, A0, c, 'RR+')
        e = w.s([], lab, '( 2 ^ %s ) = %s' % (n, P))
        le = s([w.s([num.le_lit(w, c, P)], 'a1i', '( %s -> %s <_ %s )' % (A0, c, P)), w.s([e], 'a1i', '( %s -> ( 2 ^ %s ) = %s )' % (A0, n, P))], 'breqtrrd', '%s <_ ( 2 ^ %s )' % (c, n))
        pp = s([two, w.s([num.fact(w, n, 'ZZ')], 'a1i', '( %s -> %s e. ZZ )' % (A0, n))], 'rpexpcld', '( 2 ^ %s ) e. RR+' % n)
        lg_ = s([le, s([cp, pp], 'logled', '( %s <_ ( 2 ^ %s ) <-> ( log ` %s ) <_ ( log ` ( 2 ^ %s ) ) )' % (c, n, c, n))], 'mpbid', '( log ` %s ) <_ ( log ` ( 2 ^ %s ) )' % (c, n))
        re_ = s([s([two, w.s([num.fact(w, n, 'ZZ')], 'a1i', '( %s -> %s e. ZZ )' % (A0, n))], 'jca', '( 2 e. RR+ /\\ %s e. ZZ )' % n), w.inst('relogexp')], 'syl',
                '( log ` ( 2 ^ %s ) ) = ( %s x. %s )' % (n, n, L2_))
        return s([lg_, re_], 'breqtrd', '( log ` %s ) <_ ( %s x. %s )' % (c, n, L2_))
    l128 = logpow('; ; 1 2 8', '7', '2exp7', '; ; 1 2 8')
    l26 = logpow('; 2 6', '5', '2exp5', '; 3 2')
    l2u = w.s([w.s([], 'log2ub', '%s < ( ; ; 2 5 3 / ; ; 3 6 5 )' % L2_)], 'a1i', '( %s -> %s < ( ; ; 2 5 3 / ; ; 3 6 5 ) )' % (A0, L2_))
    l2x = s([x2_, s([two, xp], 'logled', '( 2 <_ X <-> %s <_ %s )' % (L2_, LX))], 'mpbid', '%s <_ %s' % (L2_, LX))
    # log ( B / abs F C0 ) <_ log ( B / M ) <_ log ( 128 X )
    alcp = s([alr, apos], 'elrpd', '%s e. RR+' % ALC)
    dle = s([mrp, alcp, br, s([brp], 'rpge0d', '0 <_ B'), mle], 'lediv2ad', '( B / %s ) <_ ( B / M )' % ALC)
    P = '( ; ; 1 2 8 x. X )'
    pp = s([numst(w, A0, '; ; 1 2 8', 'RR+'), xp], 'rpmulcld', '%s e. RR+' % P)
    q1p = s([brp, alcp], 'rpdivcld', '( B / %s ) e. RR+' % ALC)
    q2p = s([brp, mrp], 'rpdivcld', '( B / M ) e. RR+')
    dle2 = s([dle, bmx], 'letrd' if False else 'letrd', '( B / %s ) <_ %s' % (ALC, P)) if False else None
    dd = s([s([q1p], 'rpred', '( B / %s ) e. RR' % ALC), s([q2p], 'rpred', '( B / M ) e. RR'), s([pp], 'rpred', '%s e. RR' % P), dle, bmx], 'letrd', '( B / %s ) <_ %s' % (ALC, P))
    LQ = '( log ` ( B / %s ) )' % ALC
    lq = s([dd, s([q1p, pp], 'logled', '( ( B / %s ) <_ %s <-> %s <_ ( log ` %s ) )' % (ALC, P, LQ, P))], 'mpbid', '%s <_ ( log ` %s )' % (LQ, P))
    lpe = s([numst(w, A0, '; ; 1 2 8', 'RR+'), xp], 'relogmuld', '( log ` %s ) = ( ( log ` ; ; 1 2 8 ) + %s )' % (P, LX))
    # W log 26 <_ W ( 253 / 73 )
    C26 = '( ; ; 2 5 3 / ; 7 3 )'
    L26 = '( log ` ; 2 6 )'
    l26r = s([numst(w, A0, '; 2 6', 'RR+')], 'relogcld', '%s e. RR' % L26)
    l2r = s([two], 'relogcld', '%s e. RR' % L2_)
    c26 = lin8(w, A0, [l26, l2u], '%s <_ %s' % (L26, C26), {L26: l26r, L2_: l2r})
    wr = s([wp], 'rpred', '%s e. RR' % W8)
    wl = s([l26r, numst(w, A0, C26, 'RR'), wr, s([wp], 'rpge0d', '0 <_ %s' % W8), c26], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (W8, L26, W8, C26))
    WL = '( %s x. %s )' % (W8, L26)
    lvf = {LQ: s([q1p], 'relogcld', '%s e. RR' % LQ), '( log ` %s )' % P: s([pp], 'relogcld', '( log ` %s ) e. RR' % P),
           '( log ` ; ; 1 2 8 )': s([numst(w, A0, '; ; 1 2 8', 'RR+')], 'relogcld', '( log ` ; ; 1 2 8 ) e. RR'), LX: s([lxp], 'rpred', '%s e. RR' % LX), L2_: l2r, WL: s([wr, l26r], 'remulcld', '%s e. RR' % WL)}
    c_ = clo(w, A0, lvf)
    RHS1 = '( %s x. %s )' % (KNUM, LX)
    le = lin.linarith(w, A0, [lq, lpe, l128, l2x, wl, s([lxp], 'rpge0d', '0 <_ %s' % LX)], '%s <_ %s' % (RHS0, RHS1), closure=c_)
    lx = w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')
    brl = w.s([lx], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (LHS, RHS0, LHS, RHS0))
    lhx = s([s([lg, brl], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (LHS, RHS0)), w.inst('simpl')], 'syl', '%s e. RR*' % LHS)
    r0x = s([c_.mem(RHS0, 'RR')], 'rexrd', '%s e. RR*' % RHS0)
    r1x = s([c_.mem(RHS1, 'RR')], 'rexrd', '%s e. RR*' % RHS1)
    w.qed([lhx, r0x, r1x, lg, le], 'xrletrd', S['lndk'])
    return run8(w)


def gen_lndinst(label, F, B, M, holf, rct, ctr, zc, desc):
    w = W(label, desc)
    A0 = '( T e. RR /\\ %s )' % SDE(F)
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    tr = s([], 'simpl', 'T e. RR'); sd = s([], 'simpr', SDE(F))
    hol = holf(w, A0)
    atr = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ag0 = s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')
    x2r = s([atr, numst(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % AT2)
    lv = {'( abs ` T )': atr}
    x2 = lin8(w, A0, [ag0], '2 <_ %s' % AT2, lv)
    import cl as _cl
    c = _cl.Closure(w, A0, lv)
    br = c.mem(B, 'RR')
    brp = s([br, lin8(w, A0, [ag0], '0 < %s' % B, lv)], 'elrpd', '%s e. RR+' % B)
    mrp = numst(w, A0, M, 'RR+')
    fbx = s([tr, w.inst(rct)], 'syl', ante_of(stmt(rct))[1])
    CTR = tsub(stmt(ctr), {'t': 'T'}) if ctr == 'gfctr' else stmt(ctr)
    if ctr == 'gfctr':
        phi = ante_of(stmt(ctr))[1]
        al = s([w.s([w.s([], ctr, stmt(ctr))], 'rgen', 'A. t e. RR %s' % phi)], 'a1i', 'A. t e. RR %s' % phi)
        eq, _ = w.wcongr(phi, {'t': 'T'}, 't = T', {'t': w.s([], 'id', '( t = T -> t = T )')})
        mle = w.s([eq, al, tr], 'rspcdva', '( %s -> %s )' % (A0, ante_of(CTR)[1]))
    else:
        mle = s([tr, w.inst(ctr)], 'syl', ante_of(CTR)[1])
    P = '( ; ; 1 2 8 x. %s )' % AT2
    bmx = s([lin8(w, A0, [ag0], '%s <_ ( %s x. %s )' % (B, M, P), lv), s([br, s([numst(w, A0, '; ; 1 2 8', 'RR'), x2r], 'remulcld', '%s e. RR' % P), mrp], 'ledivmuld',
             '( ( %s / %s ) <_ %s <-> %s <_ ( %s x. %s ) )' % (B, M, P, B, M, P))], 'mpbird', '( %s / %s ) <_ %s' % (B, M, P))
    zcc = ante_of(stmt(zc))[1]
    mass = s([s([tr, w.inst(zc)], 'syl', zcc), w.inst('simp3')], 'syl', top_and(zcc)[2])
    LK = tsub(S['lndk'], {'F': F, 'X': AT2, 'B': B, 'M': M})
    la, lc = ante_of(LK)
    K1, K2, K3 = top_and(la)
    Q1, Q2, Q3 = top_and(K2)
    k2 = s([s([x2r, x2], 'jca', Q1), s([brp, fbx], 'jca', Q2), s([mrp, mle, bmx], '3jca', Q3)], '3jca', K2)
    w.qed([s([s([hol, tr], 'jca', K1), k2, s([mass, sd], 'jca', K3)], '3jca', la), w.inst('lndk')], 'syl', S[label])
    return run8(w)


def eta_hol(w, A0):
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    return s([s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), s([w.s([], '0le0', '0 <_ 0')], 'a1i', '0 <_ 0')], 'jca', '( 0 e. RR /\\ 0 <_ 0 )'), w.inst('etahol')], 'syl', HOLF(ETA, HP0))


def gf_hol(w, A0):
    return w.s([w.s([], 'gfhol', S['gfhol'])], 'a1i', '( %s -> %s )' % (A0, S['gfhol']))


if __name__ == '__main__':
    gen_lndk()
    gen_lndinst('lndeta', ETA, '( ; 2 5 x. %s )' % AT2, '( 1 / 4 )', eta_hol, 'etarct', 'etactr', 'etazc',
                'The Landau expansion for the Abel-summed eta function on the square about ` 2 + i T ` : error at most ` 17500000 log ( abs T + 2 ) ` ( ~ lndk , ~ etarct , ~ etactr , ~ etazc ; Lean ` norm_logDeriv_sub_sum_diskZeros_le ` at ` diskData_etaFun ` ).')
    gen_lndinst('lndgf', GF, '3', '( 1 / 2 )', gf_hol, 'gfrct', 'gfctr', 'gfzc',
                'The Landau expansion for Lean\'s ` gFun ` on the square about ` 2 + i T ` : error at most ` 17500000 log ( abs T + 2 ) ` ( ~ lndk , ~ gfrct , ~ gfctr , ~ gfzc ; Lean ` diskData_gFun ` ).')
