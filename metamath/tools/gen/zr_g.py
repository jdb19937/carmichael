"""Sortie ZR: zrkey (the 3-4-1 inequality with the Landau input), zrl1 (no zero on Re = 1), zrhi (Lean
zeta_zero_re_le_of_two_le_abs_im)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of
from zr_b import mv, VMF


def lan_inst(w, A0, Tt, trst, wp, w20):
    """( A0 -> zrlan's conclusion at T := Tt ) and its body text"""
    c = Ctx(w, A0)
    st = tsub(S['zrlan'], {'T': Tt})
    a, b = ante_of(st)
    return c([c([trst, c([wp, w20], 'jca', W20)], 'jca', a), w.inst('zrlan')], 'syl', b), b


def gen_key():
    w = W('zrkey', 'Lean ` zeta_zero_re_le_of_two_le_abs_im ` , the inequality: for a zero ` B + i T ` of zeta, ` T =/= 0 ` , ` 3 / 8 <_ B <_ 1 ` , and ` 0 < W <_ 1 / 20 ` , '
             '` 4 / ( 1 + W - B ) <_ 3 ( 5 / 4 ) / W + 6 K log ( abs T + 2 ) + 65 + 5 W / T ^ 2 ` ( ~ zr341 , ~ vmsharp , ~ zrlan at ` T ` and ` 2 T ` ).')
    A0 = ante_of(S['zrkey'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); t0 = c.g('T =/= 0'); wp = c.g('W e. RR+'); w20 = c.g('W <_ ( 1 / ; 2 0 )')
    br = c.g('B e. RR'); b38 = c.g('( 3 / 8 ) <_ B'); b1 = c.g('B <_ 1'); bz = c.g('( %s ` ( B + ( _i x. T ) ) ) = 0' % E1)
    wr = c([wp], 'rpred', 'W e. RR'); tc = c([tr], 'recnd', 'T e. CC')
    X = '( 1 + W )'
    xr = c([c([], '1red', '1 e. RR'), wr], 'readdcld', '%s e. RR' % X)
    x1 = lin8(w, A0, [c([wp], 'rpgt0d', '0 < W')], '1 < %s' % X, {'W': wr})
    z341 = c([c([c([xr, x1], 'jca', '( %s e. RR /\\ 1 < %s )' % (X, X)), tr], 'jca', '( ( %s e. RR /\\ 1 < %s ) /\\ T e. RR )' % (X, X)), w.inst('zr341')], 'syl',
             ante_of(tsub(S['zr341'], {'X': X}))[1])
    # S0: the series at 1 + W is real, <_ (5/4)/W + 5
    Ak = '( %s /\\ k e. NN )' % A0
    ck = Ctx(w, Ak)
    kn = ck([], 'simpr', 'k e. NN')
    TK0 = '( ( Lam ` k ) x. ( k ^c -u %s ) )' % X
    tkr = ck([ck([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR'), ck([ck([ck([kn], 'nnrpd', 'k e. RR+'), ck([lift(w, xr, Ak)], 'renegcld', '-u %s e. RR' % X)], 'rpcxpcld', '( k ^c -u %s ) e. RR+' % X)], 'rpred',
                                                                                  '( k ^c -u %s ) e. RR' % X)], 'remulcld', '%s e. RR' % TK0)
    fk = mv(w, Ak, 'n', 'NN', '( ( Lam ` n ) x. ( n ^c -u %s ) )' % X, 'k', kn, ck([tkr], 'recnd', '%s e. CC' % TK0))
    xc = c([xr], 'recnd', '%s e. CC' % X)
    xre = c([xr], 'rered', '( Re ` %s ) = %s' % (X, X))
    xs1 = c([x1, c([xre], 'eqcomd', '%s = ( Re ` %s )' % (X, X))], 'breqtrd', '1 < ( Re ` %s )' % X)
    cv = c([c([xc, xs1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (X, X)), w.inst('zrvmc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % VMF(X))
    D0 = DL(X)
    d0r = c([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), c([], '1zzd', '1 e. ZZ'), fk, tkr, cv], 'isumrecl', '%s e. RR' % D0)
    rd0 = c([d0r], 'rered', '( Re ` %s ) = %s' % (D0, D0))
    vs = c([c([wp, lin8(w, A0, [w20], 'W <_ 1', {'W': wr})], 'jca', '( W e. RR+ /\\ W <_ 1 )'), w.inst('vmsharp')], 'syl', '%s <_ ( ( ( 5 / 4 ) / W ) + 5 )' % D0)
    # S1 with the zero at B
    l1, body1 = lan_inst(w, A0, 'T', tr, wp, w20)
    S1 = '( Re ` %s )' % DL(SW)
    IR = '( 1 / ( ( 1 + W ) - B ) )'
    LT = LT2('T')
    B1 = '%s <_ ( ( ( %s x. %s ) + ( ; 1 0 + %s ) ) - %s )' % (S1, KL, LT, WTT, IR)
    Ax = '( %s /\\ x e. RR )' % A0
    PSI = body1[len('E. x e. RR '):]
    Axp = '( %s /\\ %s )' % (Ax, PSI)
    cx = Ctx(w, Axp)
    xb = cx.g('( Re ` %s ) <_ ( ( ( %s x. %s ) + ( ; 1 0 + %s ) ) - x )' % (DL(SW), KL, LT, WTT))
    ALB = top_and(PSI)[1]
    alb = cx.g(ALB)
    bodyb = ALB[len('A. b e. RR '):]
    inb, newb = ral_at(w, Axp, alb, 'b', 'B', bodyb, lift(w, br, Axp))
    hb = cx([cx([lift(w, b38, Axp), lift(w, b1, Axp)], 'jca', '( ( 3 / 8 ) <_ B /\\ B <_ 1 )'), lift(w, bz, Axp)], 'jca', ante_of(newb)[0])
    irle = cx([hb, inb], 'mpd', '%s <_ x' % IR)
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    swc = c([xc, c([ic, tc], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SW)
    ow1 = lin8(w, A0, [c([wp], 'rpgt0d', '0 < W')], '1 < ( 1 + W )', {'W': wr})
    sre = c([xr, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (SW, X))
    ss1 = c([ow1, c([sre], 'eqcomd', '%s = ( Re ` %s )' % (X, SW))], 'breqtrd', '1 < ( Re ` %s )' % SW)
    d1c = dl_cc(w, A0, SW, swc, ss1)
    s1r = c([d1c], 'recld', '%s e. RR' % S1)
    lt_ = ltv(w, A0, tc)
    DEN = '( ( W ^ 2 ) + ( T ^ 2 ) )'
    wtr = c([wr, c([c([wr], 'resqcld', '( W ^ 2 ) e. RR'), c([tr], 'resqcld', '( T ^ 2 ) e. RR')], 'readdcld', '%s e. RR' % DEN),
             c([lin8(w, A0, [c([wr, c([wp], 'rpne0d', 'W =/= 0')], 'sqgt0d', '0 < ( W ^ 2 )'), c([tr], 'sqge0d', '0 <_ ( T ^ 2 )')], '0 < %s' % DEN,
                     {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( T ^ 2 )': c([tr], 'resqcld', '( T ^ 2 ) e. RR')})], 'gt0ne0d', '%s =/= 0' % DEN)], 'redivcld', '%s e. RR' % WTT)
    R = '( ( 1 + W ) - B )'
    rr = c([xr, br], 'resubcld', '%s e. RR' % R)
    rp = lin8(w, A0, [b1, c([wp], 'rpgt0d', '0 < W')], '0 < %s' % R, {'B': br, 'W': wr})
    irr = c([c([], '1red', '1 e. RR'), rr, c([rp], 'gt0ne0d', '%s =/= 0' % R)], 'redivcld', '%s e. RR' % IR)
    L_ = lambda st: lift(w, st, Axp)
    b1s = lin8(w, Axp, [xb, irle], B1, {S1: L_(s1r), 'x': cx.g('x e. RR'), IR: L_(irr), LT: L_(lt_), WTT: L_(wtr)})
    rl1 = c([w.s([b1s], 'ex', '( %s -> ( %s -> %s ) )' % (Ax, PSI, B1))], 'rexlimdva', '( %s -> %s )' % (body1, B1))
    s1b = c([l1, rl1], 'mpd', B1)
    # S2 at 2 T, zero mass dropped
    T2 = '( 2 x. T )'
    t2r = c([numst8(w, A0, '2', 'RR'), tr], 'remulcld', '%s e. RR' % T2)
    t2c = c([t2r], 'recnd', '%s e. CC' % T2)
    l2, body2 = lan_inst(w, A0, T2, t2r, wp, w20)
    SW2 = SWT('W', T2)
    S2 = '( Re ` %s )' % DL(SW2)
    LTT = LT2(T2)
    WTT2 = tsub(WTT, {'T': T2})
    B2 = '%s <_ ( ( %s x. %s ) + ( ; 1 0 + %s ) )' % (S2, KL, LTT, WTT2)
    PSI2 = body2[len('E. x e. RR '):]
    Axq = '( %s /\\ %s )' % (Ax, PSI2)
    cy = Ctx(w, Axq)
    swc2 = c([xc, c([ic, t2c], 'mulcld', '( _i x. %s ) e. CC' % T2)], 'addcld', '%s e. CC' % SW2)
    sre2 = c([xr, t2r, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (SW2, X))
    ss2 = c([ow1, c([sre2], 'eqcomd', '%s = ( Re ` %s )' % (X, SW2))], 'breqtrd', '1 < ( Re ` %s )' % SW2)
    s2r = c([dl_cc(w, A0, SW2, swc2, ss2)], 'recld', '%s e. RR' % S2)
    ltt = ltv(w, A0, t2c, T2)
    DEN2 = '( ( W ^ 2 ) + ( %s ^ 2 ) )' % T2
    den2r = c([c([wr], 'resqcld', '( W ^ 2 ) e. RR'), c([t2r], 'resqcld', '( %s ^ 2 ) e. RR' % T2)], 'readdcld', '%s e. RR' % DEN2)
    den2p = lin8(w, A0, [c([wr, c([wp], 'rpne0d', 'W =/= 0')], 'sqgt0d', '0 < ( W ^ 2 )'), c([t2r], 'sqge0d', '0 <_ ( %s ^ 2 )' % T2)], '0 < %s' % DEN2,
                 {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( %s ^ 2 )' % T2: c([t2r], 'resqcld', '( %s ^ 2 ) e. RR' % T2)})
    wtr2 = c([wr, den2r, c([den2p], 'gt0ne0d', '%s =/= 0' % DEN2)], 'redivcld', '%s e. RR' % WTT2)
    L2_ = lambda st: lift(w, st, Axq)
    xb2 = cy.g('( Re ` %s ) <_ ( ( ( %s x. %s ) + ( ; 1 0 + %s ) ) - x )' % (DL(SW2), KL, LTT, WTT2))
    x0 = cy.g('0 <_ x')
    b2s = lin8(w, Axq, [xb2, x0], B2, {S2: L2_(s2r), 'x': cy.g('x e. RR'), LTT: L2_(ltt), WTT2: L2_(wtr2)})
    rl2 = c([w.s([b2s], 'ex', '( %s -> ( %s -> %s ) )' % (Ax, PSI2, B2))], 'rexlimdva', '( %s -> %s )' % (body2, B2))
    s2b = c([l2, rl2], 'mpd', B2)
    # log ( abs ( 2 T ) + 2 ) <_ 2 log ( abs T + 2 )
    a_ = '( abs ` T )'
    ar = c([tc], 'abscld', '%s e. RR' % a_)
    a0 = c([tc], 'absge0d', '0 <_ %s' % a_)
    ab2 = c([c([c([], '2cnd', '2 e. CC'), tc], 'absmuld', '( abs ` %s ) = ( ( abs ` 2 ) x. %s )' % (T2, a_)),
             c([c([numst8(w, A0, '2', 'RR'), lin8(w, A0, [], '0 <_ 2', {})], 'absidd', '( abs ` 2 ) = 2')], 'oveq1d', '( ( abs ` 2 ) x. %s ) = ( 2 x. %s )' % (a_, a_))], 'eqtrd', '( abs ` %s ) = ( 2 x. %s )' % (T2, a_))
    U1_, U2_ = '( ( 2 x. %s ) + 2 )' % a_, '( ( %s + 2 ) ^ 2 )' % a_
    u1p = c([c([c([numst8(w, A0, '2', 'RR'), ar], 'remulcld', '( 2 x. %s ) e. RR' % a_), numst8(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % U1_),
             lin8(w, A0, [a0], '0 < %s' % U1_, {a_: ar})], 'elrpd', '%s e. RR+' % U1_)
    ap = c([c([ar, numst8(w, A0, '2', 'RR')], 'readdcld', '( %s + 2 ) e. RR' % a_), lin8(w, A0, [a0], '0 < ( %s + 2 )' % a_, {a_: ar})], 'elrpd', '( %s + 2 ) e. RR+' % a_)
    u2p = c([ap, c.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ')], 'rpexpcld', '%s e. RR+' % U2_)
    pr = c([ar, ar, a0, a0], 'mulge0d', '0 <_ ( %s x. %s )' % (a_, a_))
    ule = lin8(w, A0, [a0, pr], '%s <_ %s' % (U1_, U2_), {a_: ar}, products=True)
    lle = c([ule, c([u1p, u2p, w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (U1_, U2_, U1_, U2_))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (U1_, U2_))
    lex = c([ap, c.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ'), w.inst('relogexp')], 'syl2anc', '( log ` %s ) = ( 2 x. %s )' % (U2_, LT))
    lt2e = c([c([c([ab2], 'oveq1d', '( ( abs ` %s ) + 2 ) = %s' % (T2, U1_))], 'fveq2d', '%s = ( log ` %s )' % (LTT, U1_)), lle], 'eqbrtrd', '%s <_ ( log ` %s )' % (LTT, U2_))
    lt2 = c([lt2e, lex], 'breqtrd', '%s <_ ( 2 x. %s )' % (LTT, LT))
    # W / ( W^2 + T^2 ), W / ( W^2 + ( 2 T )^2 ) <_ W / T^2
    t2p = c([c([tr], 'resqcld', '( T ^ 2 ) e. RR'), c([tr, t0], 'sqgt0d', '0 < ( T ^ 2 )')], 'elrpd', '( T ^ 2 ) e. RR+')
    denrp = c([c([c([wr], 'resqcld', '( W ^ 2 ) e. RR'), c([tr], 'resqcld', '( T ^ 2 ) e. RR')], 'readdcld', '%s e. RR' % DEN),
               lin8(w, A0, [c([wr, c([wp], 'rpne0d', 'W =/= 0')], 'sqgt0d', '0 < ( W ^ 2 )'), c([tr], 'sqge0d', '0 <_ ( T ^ 2 )')], '0 < %s' % DEN,
                    {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( T ^ 2 )': c([tr], 'resqcld', '( T ^ 2 ) e. RR')})], 'elrpd', '%s e. RR+' % DEN)
    lvs = {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), '( T ^ 2 )': c([tr], 'resqcld', '( T ^ 2 ) e. RR'), 'T': tr}
    wt1 = c([t2p, denrp, wr, c([wp], 'rpge0d', '0 <_ W'), lin8(w, A0, [c([wr], 'sqge0d', '0 <_ ( W ^ 2 )')], '( T ^ 2 ) <_ %s' % DEN, lvs)], 'lediv2ad', '%s <_ ( W / ( T ^ 2 ) )' % WTT)
    wt2 = c([t2p, c([den2r, den2p], 'elrpd', '%s e. RR+' % DEN2), wr, c([wp], 'rpge0d', '0 <_ W'),
             lin8(w, A0, [c([wr], 'sqge0d', '0 <_ ( W ^ 2 )'), c([tr], 'sqge0d', '0 <_ ( T ^ 2 )')], '( T ^ 2 ) <_ %s' % DEN2, {'( W ^ 2 )': c([wr], 'resqcld', '( W ^ 2 ) e. RR'), 'T': tr}, products=True)],
            'lediv2ad', '%s <_ ( W / ( T ^ 2 ) )' % WTT2)
    WT2 = '( W / ( T ^ 2 ) )'
    Q0 = '( ( 5 / 4 ) / W )'
    lvK = {'( Re ` %s )' % D0: c([c([d0r], 'recnd', '%s e. CC' % D0)], 'recld', '( Re ` %s ) e. RR' % D0), D0: d0r, S1: s1r, S2: s2r, Q0: c([numst8(w, A0, '( 5 / 4 )', 'RR'), wr, c([wp], 'rpne0d', 'W =/= 0')], 'redivcld', '%s e. RR' % Q0),
           LT: lt_, LTT: ltt, WTT: wtr, WTT2: wtr2, WT2: c([wr, c([tr], 'resqcld', '( T ^ 2 ) e. RR'), c([t2p], 'rpne0d', '( T ^ 2 ) =/= 0')], 'redivcld', '%s e. RR' % WT2), IR: irr}
    fin = lin8(w, A0, [z341, rd0, vs, s1b, s2b, lt2, wt1, wt2], ante_of(S['zrkey'])[1], lvK, products=True)
    w.qed([fin], 'idi', S['zrkey'])
    return run8(w)


def dl_cc(w, A0, Sx, sc, s1):
    """( A0 -> DL(Sx) e. CC ) (isumcl, zrvmc)"""
    c = Ctx(w, A0)
    Ak = '( %s /\\ k e. NN )' % A0
    ck = Ctx(w, Ak)
    kn = ck([], 'simpr', 'k e. NN')
    TKK = '( ( Lam ` k ) x. ( k ^c -u %s ) )' % Sx
    tkc = ck([ck([ck([kn, w.inst('vmacl')], 'syl', '( Lam ` k ) e. RR')], 'recnd', '( Lam ` k ) e. CC'), ck([ck([kn], 'nncnd', 'k e. CC'), ck([lift(w, sc, Ak)], 'negcld', '-u %s e. CC' % Sx)], 'cxpcld', '( k ^c -u %s ) e. CC' % Sx)],
              'mulcld', '%s e. CC' % TKK)
    fk = mv(w, Ak, 'n', 'NN', '( ( Lam ` n ) x. ( n ^c -u %s ) )' % Sx, 'k', kn, tkc)
    cv = c([c([sc, s1], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (Sx, Sx)), w.inst('zrvmc')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % VMF(Sx))
    return c([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), c([], '1zzd', '1 e. ZZ'), fk, tkc, cv], 'isumcl', '%s e. CC' % DL(Sx))


def ltv(w, A0, tc, T='T'):
    """( A0 -> ( log ` ( ( abs ` T ) + 2 ) ) e. RR )"""
    c = Ctx(w, A0)
    at = c([tc], 'abscld', '( abs ` %s ) e. RR' % T)
    a2 = c([at, numst8(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` %s ) + 2 ) e. RR' % T)
    p = lin8(w, A0, [c([tc], 'absge0d', '0 <_ ( abs ` %s )' % T)], '0 < ( ( abs ` %s ) + 2 )' % T, {'( abs ` %s )' % T: at})
    return c([c([a2, p], 'elrpd', '( ( abs ` %s ) + 2 ) e. RR+' % T)], 'relogcld', '%s e. RR' % LT2(T))


def gen_l1():
    w = W('zrl1', 'Zeta has no zero on the line ` Re s = 1 ` off the real axis: ` E1 ( 1 + i T ) =/= 0 ` for ` T =/= 0 ` (Mathlib ` riemannZeta_ne_zero_of_one_le_re ` ; here from ~ zrkey at ` W = 1 / ( 8 A + 20 + 10 / T ^ 2 ) ` ).')
    A0 = ante_of(S['zrl1'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); t0 = c.g('T =/= 0')
    tc = c([tr], 'recnd', 'T e. CC')
    ZV = '( %s ` ( 1 + ( _i x. T ) ) )' % E1
    A1 = '( %s /\\ %s = 0 )' % (A0, ZV)
    c1 = Ctx(w, A1)
    L_ = lambda st: lift(w, st, A1)
    LT = LT2('T')
    lt_ = ltv(w, A0, tc)
    lt0 = c([c([c([tc], 'abscld', '( abs ` T ) e. RR'), numst8(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` T ) + 2 ) e. RR'),
             lin8(w, A0, [c([tc], 'absge0d', '0 <_ ( abs ` T )')], '1 <_ ( ( abs ` T ) + 2 )', {'( abs ` T )': c([tc], 'abscld', '( abs ` T ) e. RR')})], 'logge0d', '0 <_ %s' % LT)
    A_ = '( ( ( 6 x. %s ) x. %s ) + ; 6 5 )' % (KL, LT)
    ar = c([c([c([numst8(w, A0, '6', 'RR'), numst8(w, A0, KL, 'RR')], 'remulcld', '( 6 x. %s ) e. RR' % KL), lt_], 'remulcld',
                  '( ( 6 x. %s ) x. %s ) e. RR' % (KL, LT)), numst8(w, A0, '; 6 5', 'RR')], 'readdcld', '%s e. RR' % A_)
    T2 = '( T ^ 2 )'
    t2r = c([tr], 'resqcld', '%s e. RR' % T2); t2p = c([tr, t0], 'sqgt0d', '0 < %s' % T2)
    V = '( 1 / %s )' % T2
    vr = c([c([], '1red', '1 e. RR'), t2r, c([t2p], 'gt0ne0d', '%s =/= 0' % T2)], 'redivcld', '%s e. RR' % V)
    vp = c([c([t2r, t2p], 'elrpd', '%s e. RR+' % T2)], 'rpreccld', '%s e. RR+' % V)
    D = '( ( ( 8 x. %s ) + ; 2 0 ) + ( ; 1 0 x. %s ) )' % (A_, V)
    lvD = {LT: lt_, V: vr}
    dr = c([c([c([numst8(w, A0, '8', 'RR'), ar], 'remulcld', '( 8 x. %s ) e. RR' % A_), numst8(w, A0, '; 2 0', 'RR')], 'readdcld', '( ( 8 x. %s ) + ; 2 0 ) e. RR' % A_),
            c([numst8(w, A0, '; 1 0', 'RR'), vr], 'remulcld', '( ; 1 0 x. %s ) e. RR' % V)], 'readdcld', '%s e. RR' % D)
    dp = lin8(w, A0, [lt0, c([vp], 'rpgt0d', '0 < %s' % V)], '; 2 0 <_ %s' % D, lvD, products=True)
    drp = c([dr, lin8(w, A0, [dp], '0 < %s' % D, {D: dr})], 'elrpd', '%s e. RR+' % D)
    Wt = '( 1 / %s )' % D
    wrp = c([drp], 'rpreccld', '%s e. RR+' % Wt)
    wr = c([wrp], 'rpred', '%s e. RR' % Wt)
    wd = c([c([], '1cnd', '1 e. CC'), c([dr], 'recnd', '%s e. CC' % D), c([drp], 'rpne0d', '%s =/= 0' % D)], 'divcan1d', '( %s x. %s ) = 1' % (Wt, D))
    hint = c([wr, c([dr, numst8(w, A0, '; 2 0', 'RR')], 'resubcld', '( %s - ; 2 0 ) e. RR' % D), c([wrp], 'rpge0d', '0 <_ %s' % Wt), lin8(w, A0, [dp], '0 <_ ( %s - ; 2 0 )' % D, {D: dr})],
             'mulge0d', '0 <_ ( %s x. ( %s - ; 2 0 ) )' % (Wt, D))
    w20 = lin8(w, A0, [wd, hint], '%s <_ ( 1 / ; 2 0 )' % Wt, {Wt: wr, D: dr}, products=True)
    key_ante = ante_of(tsub(S['zrkey'], {'W': Wt, 'B': '1'}))
    ka = c1([c1([L_(tr), L_(t0)], 'jca', '( T e. RR /\\ T =/= 0 )'), c1([L_(wrp), L_(w20)], 'jca', '( %s e. RR+ /\\ %s <_ ( 1 / ; 2 0 ) )' % (Wt, Wt)),
             c1([c1([c1([], '1red', '1 e. RR'), c1([lin8(w, A1, [], '( 3 / 8 ) <_ 1', {}), lin8(w, A1, [], '1 <_ 1', {})], 'jca', '( ( 3 / 8 ) <_ 1 /\\ 1 <_ 1 )')], 'jca',
                     '( 1 e. RR /\\ ( ( 3 / 8 ) <_ 1 /\\ 1 <_ 1 ) )'), c1([], 'simpr', '%s = 0' % ZV)], 'jca', top_and(key_ante[0])[2])], '3jca', key_ante[0])
    kk = c1([ka, w.inst('zrkey')], 'syl', key_ante[1])
    IRt = '( 1 / ( ( 1 + %s ) - 1 ) )' % Wt
    wc = c([wr], 'recnd', '%s e. CC' % Wt)
    e1 = c([c([c([c([], '1cnd', '1 e. CC'), wc], 'pncan2d', '( ( 1 + %s ) - 1 ) = %s' % (Wt, Wt))], 'oveq2d', '%s = ( 1 / %s )' % (IRt, Wt)),
            c([c([dr], 'recnd', '%s e. CC' % D), c([drp], 'rpne0d', '%s =/= 0' % D)], 'recrecd', '( 1 / %s ) = %s' % (Wt, D))], 'eqtrd', '%s = %s' % (IRt, D))
    Q0 = '( ( 5 / 4 ) / %s )' % Wt
    e2 = c([c([numst8(w, A0, '( 5 / 4 )', 'CC'), wc, c([wrp], 'rpne0d', '%s =/= 0' % Wt)], 'divrecd', '%s = ( ( 5 / 4 ) x. ( 1 / %s ) )' % (Q0, Wt)),
            c([c([c([dr], 'recnd', '%s e. CC' % D), c([drp], 'rpne0d', '%s =/= 0' % D)], 'recrecd', '( 1 / %s ) = %s' % (Wt, D))], 'oveq2d', '( ( 5 / 4 ) x. ( 1 / %s ) ) = ( ( 5 / 4 ) x. %s )' % (Wt, D))],
           'eqtrd', '%s = ( ( 5 / 4 ) x. %s )' % (Q0, D))
    WV = '( %s / %s )' % (Wt, T2)
    e3 = c([wc, c([t2r], 'recnd', '%s e. CC' % T2), c([t2p], 'gt0ne0d', '%s =/= 0' % T2)], 'divrecd', '%s = ( %s x. %s )' % (WV, Wt, V))
    h2 = c([wr, vr, c([wrp], 'rpge0d', '0 <_ %s' % Wt), c([vp], 'rpge0d', '0 <_ %s' % V)], 'mulge0d', '0 <_ ( %s x. %s )' % (Wt, V))
    h3 = c([c([numst8(w, A0, '( 1 / ; 2 0 )', 'RR'), wr], 'resubcld', '( ( 1 / ; 2 0 ) - %s ) e. RR' % Wt), vr, lin8(w, A0, [w20], '0 <_ ( ( 1 / ; 2 0 ) - %s )' % Wt, {Wt: wr}), c([vp], 'rpge0d', '0 <_ %s' % V)],
           'mulge0d', '0 <_ ( ( ( 1 / ; 2 0 ) - %s ) x. %s )' % (Wt, V))
    rm = c([c([c([], '1red', '1 e. RR'), wr], 'readdcld', '( 1 + %s ) e. RR' % Wt), c([], '1red', '1 e. RR')], 'resubcld', '( ( 1 + %s ) - 1 ) e. RR' % Wt)
    rmn = c([c([c([], '1cnd', '1 e. CC'), wc], 'pncan2d', '( ( 1 + %s ) - 1 ) = %s' % (Wt, Wt)), c([wrp], 'rpne0d', '%s =/= 0' % Wt)], 'eqnetrd', '( ( 1 + %s ) - 1 ) =/= 0' % Wt)
    irt = c([c([], '1red', '1 e. RR'), rm, rmn], 'redivcld', '%s e. RR' % IRt)
    q0r = c([numst8(w, A0, '( 5 / 4 )', 'RR'), wr, c([wrp], 'rpne0d', '%s =/= 0' % Wt)], 'redivcld', '%s e. RR' % Q0)
    wvr = c([wr, t2r, c([t2p], 'gt0ne0d', '%s =/= 0' % T2)], 'redivcld', '%s e. RR' % WV)
    lvC = {IRt: L_(irt), Q0: L_(q0r), LT: L_(lt_), V: L_(vr), Wt: L_(wr), WV: L_(wvr)}
    bad = lin8(w, A1, [kk, L_(e1), L_(e2), L_(e3), L_(h2), L_(h3), L_(lt0), L_(c([vp], 'rpge0d', '0 <_ %s' % V))], '0 < 0', lvC, products=True)
    ir = w.s([w.s([w.s([], '0re', '0 e. RR')], 'ltnri', '-. 0 < 0')], 'a1i', '( %s -> -. 0 < 0 )' % A1)
    nn = c([bad, ir], 'pm2.65da', '-. %s = 0' % ZV)
    fin = c([nn], 'neqned', '%s =/= 0' % ZV)
    w.qed([fin], 'idi', S['zrl1'])
    return run8(w)


def gen_hi():
    w = W('zrhi', 'Lean ` zeta_zero_re_le_of_two_le_abs_im ` : a zero ` R ` of zeta with ` 2 <_ abs Im R ` , ` 3 / 8 <_ Re R ` has ` Re R <_ 1 - zfE / log ( abs Im R + 2 ) ` , ` zfE = 1 / ( 31 . 10 ^ 9 ) ` ( ~ zrkey at ` W = 1 / ( 10 ^ 9 log ( abs Im R + 2 ) ) ` ).')
    A0 = ante_of(S['zrhi'])[0]
    c = Ctx(w, A0)
    rc = c.g('R e. CC'); rz = c.g('( %s ` R ) = 0' % E1); t2 = c.g('2 <_ ( abs ` ( Im ` R ) )'); b38 = c.g('( 3 / 8 ) <_ ( Re ` R )')
    Tt, Bt = '( Im ` R )', '( Re ` R )'
    tr = c([rc], 'imcld', '%s e. RR' % Tt); br = c([rc], 'recld', '%s e. RR' % Bt)
    tc = c([tr], 'recnd', '%s e. CC' % Tt)
    AT = '( abs ` %s )' % Tt
    atr = c([tc], 'abscld', '%s e. RR' % AT)
    # Re R <_ 1
    A1 = '( %s /\\ 1 < %s )' % (A0, Bt)
    n1 = w.s([lift(w, rc, A1), w.s([], 'simpr', '( %s -> 1 < %s )' % (A1, Bt)), w.inst('zre1n')], 'syl2anc', '( %s -> ( %s ` R ) =/= 0 )' % (A1, E1))
    nb = c([lift(w, rz, A1), w.s([n1], 'neneqd', '( %s -> -. ( %s ` R ) = 0 )' % (A1, E1))], 'pm2.65da', '-. 1 < %s' % Bt)
    b1 = c([nb, c([br, c([], '1red', '1 e. RR')], 'lenltd', '( %s <_ 1 <-> -. 1 < %s )' % (Bt, Bt))], 'mpbird', '%s <_ 1' % Bt)
    # T =/= 0
    an0 = c([lin8(w, A0, [t2], '0 < %s' % AT, {AT: atr})], 'gt0ne0d', '%s =/= 0' % AT)
    imp = c.a1(w.s([w.s([], 'fveq2', '( %s = 0 -> %s = ( abs ` 0 ) )' % (Tt, AT)), w.s([], 'abs0', '( abs ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> %s = 0 )' % (Tt, AT)), '( %s = 0 -> %s = 0 )' % (Tt, AT))
    t0 = c([an0, c([imp], 'necon3d', '( %s =/= 0 -> %s =/= 0 )' % (AT, Tt))], 'mpd', '%s =/= 0' % Tt)
    # L = log ( abs T + 2 ) >_ 1
    L = LT2(Tt)
    U = '( %s + 2 )' % AT
    ur = c([atr, numst8(w, A0, '2', 'RR')], 'readdcld', '%s e. RR' % U)
    ep = c.a1(w.s([], 'epr', '_e e. RR+'), '_e e. RR+')
    e3 = c.a1(w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3'), '_e < 3')
    er = c([ep], 'rpred', '_e e. RR')
    up = c([ur, lin8(w, A0, [t2], '0 < %s' % U, {AT: atr})], 'elrpd', '%s e. RR+' % U)
    le = lin8(w, A0, [e3, t2], '_e <_ %s' % U, {AT: atr, '_e': er})
    l1a = c([le, c([ep, up, w.inst('logleb')], 'syl2anc', '( _e <_ %s <-> ( log ` _e ) <_ ( log ` %s ) )' % (U, U))], 'mpbid', '( log ` _e ) <_ %s' % L)
    lr = c([up], 'relogcld', '%s e. RR' % L)
    l1 = lin8(w, A0, [l1a, c.a1(w.s([], 'loge', '( log ` _e ) = 1'), '( log ` _e ) = 1')], '1 <_ %s' % L, {L: lr, '( log ` _e )': c([ep], 'relogcld', '( log ` _e ) e. RR')})
    # W = 1 / M, M = zfK L
    M = '( %s x. %s )' % (ZFK, L)
    mr = c([numst8(w, A0, ZFK, 'RR'), lr], 'remulcld', '%s e. RR' % M)
    mp = c([mr, lin8(w, A0, [l1], '0 < %s' % M, {L: lr}, products=True)], 'elrpd', '%s e. RR+' % M)
    Wt = '( 1 / %s )' % M
    wrp = c([mp], 'rpreccld', '%s e. RR+' % Wt); wr = c([wrp], 'rpred', '%s e. RR' % Wt); wc = c([wr], 'recnd', '%s e. CC' % Wt)
    wm = c([c([], '1cnd', '1 e. CC'), c([mr], 'recnd', '%s e. CC' % M), c([mp], 'rpne0d', '%s =/= 0' % M)], 'divcan1d', '( %s x. %s ) = 1' % (Wt, M))
    hW = c([wr, c([mr, numst8(w, A0, '; 2 0', 'RR')], 'resubcld', '( %s - ; 2 0 ) e. RR' % M), c([wrp], 'rpge0d', '0 <_ %s' % Wt), lin8(w, A0, [l1], '0 <_ ( %s - ; 2 0 )' % M, {L: lr}, products=True)],
           'mulge0d', '0 <_ ( %s x. ( %s - ; 2 0 ) )' % (Wt, M))
    w20 = lin8(w, A0, [wm, hW], '%s <_ ( 1 / ; 2 0 )' % Wt, {Wt: wr, M: mr}, products=True)
    # the zero as B + i T
    rp_ = c([rc, w.inst('replim')], 'syl', 'R = ( %s + ( _i x. %s ) )' % (Bt, Tt))
    bz = c([c([c([rp_], 'fveq2d', '( %s ` R ) = ( %s ` ( %s + ( _i x. %s ) ) )' % (E1, E1, Bt, Tt))], 'eqcomd', '( %s ` ( %s + ( _i x. %s ) ) ) = ( %s ` R )' % (E1, Bt, Tt, E1)), rz],
           'eqtrd', '( %s ` ( %s + ( _i x. %s ) ) ) = 0' % (E1, Bt, Tt))
    KA = ante_of(tsub(S['zrkey'], {'T': Tt, 'W': Wt, 'B': Bt}))
    ka = c([c([tr, t0], 'jca', top_and(KA[0])[0]), c([wrp, w20], 'jca', top_and(KA[0])[1]), c([c([br, c([b38, b1], 'jca', '( ( 3 / 8 ) <_ %s /\\ %s <_ 1 )' % (Bt, Bt))], 'jca', top_and(top_and(KA[0])[2])[0]), bz], 'jca', top_and(KA[0])[2])],
           '3jca', KA[0])
    kk = c([ka, w.inst('zrkey')], 'syl', KA[1])
    r = '( ( 1 + %s ) - %s )' % (Wt, Bt)
    rr = c([c([c([], '1red', '1 e. RR'), wr], 'readdcld', '( 1 + %s ) e. RR' % Wt), br], 'resubcld', '%s e. RR' % r)
    rpos = lin8(w, A0, [b1, c([wrp], 'rpgt0d', '0 < %s' % Wt)], '0 < %s' % r, {Bt: br, Wt: wr})
    IR = '( 1 / %s )' % r
    irr = c([c([], '1red', '1 e. RR'), rr, c([rpos], 'gt0ne0d', '%s =/= 0' % r)], 'redivcld', '%s e. RR' % IR)
    iri = c([c([], '1cnd', '1 e. CC'), c([rr], 'recnd', '%s e. CC' % r), c([rpos], 'gt0ne0d', '%s =/= 0' % r)], 'divcan1d', '( %s x. %s ) = 1' % (IR, r))
    Q0 = '( ( 5 / 4 ) / %s )' % Wt
    q0 = c([c([numst8(w, A0, '( 5 / 4 )', 'CC'), wc, c([wrp], 'rpne0d', '%s =/= 0' % Wt)], 'divrecd', '%s = ( ( 5 / 4 ) x. ( 1 / %s ) )' % (Q0, Wt)),
            c([c([c([mr], 'recnd', '%s e. CC' % M), c([mp], 'rpne0d', '%s =/= 0' % M)], 'recrecd', '( 1 / %s ) = %s' % (Wt, M))], 'oveq2d', '( ( 5 / 4 ) x. ( 1 / %s ) ) = ( ( 5 / 4 ) x. %s )' % (Wt, M))],
           'eqtrd', '%s = ( ( 5 / 4 ) x. %s )' % (Q0, M))
    q0r = c([numst8(w, A0, '( 5 / 4 )', 'RR'), wr, c([wrp], 'rpne0d', '%s =/= 0' % Wt)], 'redivcld', '%s e. RR' % Q0)
    T2 = '( %s ^ 2 )' % Tt
    t2r = c([tr], 'resqcld', '%s e. RR' % T2)
    aq = c([tr, w.inst('absresq')], 'syl', '( %s ^ 2 ) = %s' % (AT, T2))
    hq = c([c([atr, numst8(w, A0, '2', 'RR')], 'resubcld', '( %s - 2 ) e. RR' % AT)], 'msqge0d', '0 <_ ( ( %s - 2 ) x. ( %s - 2 ) )' % (AT, AT))
    t4 = lin8(w, A0, [aq, hq, t2], '4 <_ %s' % T2, {AT: atr, T2: t2r}, products=True)
    t2p = c([t2r, lin8(w, A0, [t4], '0 < %s' % T2, {T2: t2r})], 'elrpd', '%s e. RR+' % T2)
    WV = '( %s / %s )' % (Wt, T2)
    wv = c([numst8(w, A0, '4', 'RR+'), t2p, wr, c([wrp], 'rpge0d', '0 <_ %s' % Wt), t4], 'lediv2ad', '%s <_ ( %s / 4 )' % (WV, Wt))
    wvr = c([wr, t2r, c([t2p], 'rpne0d', '%s =/= 0' % T2)], 'redivcld', '%s e. RR' % WV)
    lv = {Bt: br, Wt: wr, L: lr, IR: irr, Q0: q0r, WV: wvr}
    i4 = lin8(w, A0, [kk, q0, wv, l1, w20], '( 4 x. %s ) <_ ( ( ; 3 1 / 8 ) x. %s )' % (IR, M), lv, products=True)
    rw0 = c([rr, wr, lin8(w, A0, [rpos], '0 <_ %s' % r, {Bt: br, Wt: wr}), c([wrp], 'rpge0d', '0 <_ %s' % Wt)], 'mulge0d', '0 <_ ( %s x. %s )' % (r, Wt))
    hi = c([c([rr, wr], 'remulcld', '( %s x. %s ) e. RR' % (r, Wt)), c([c([numst8(w, A0, '( ; 3 1 / 8 )', 'RR'), mr], 'remulcld', '( ( ; 3 1 / 8 ) x. %s ) e. RR' % M), c([numst8(w, A0, '4', 'RR'), irr], 'remulcld', '( 4 x. %s ) e. RR' % IR)],
                                                                'resubcld', '( ( ( ; 3 1 / 8 ) x. %s ) - ( 4 x. %s ) ) e. RR' % (M, IR)),
            rw0, lin8(w, A0, [i4], '0 <_ ( ( ( ; 3 1 / 8 ) x. %s ) - ( 4 x. %s ) )' % (M, IR), lv, products=True)], 'mulge0d', '0 <_ ( ( %s x. %s ) x. ( ( ( ; 3 1 / 8 ) x. %s ) - ( 4 x. %s ) ) )' % (r, Wt, M, IR))
    f1 = c([c([wm], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. 1 )' % (r, Wt, M, r)), c([c([rr], 'recnd', '%s e. CC' % r)], 'mulridd', '( %s x. 1 ) = %s' % (r, r))], 'eqtrd', '( %s x. ( %s x. %s ) ) = %s' % (r, Wt, M, r))
    f2 = c([c([iri], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. 1 )' % (Wt, IR, r, Wt)), c([wc], 'mulridd', '( %s x. 1 ) = %s' % (Wt, Wt))], 'eqtrd', '( %s x. ( %s x. %s ) ) = %s' % (Wt, IR, r, Wt))
    # zfE / L = W / 31
    ZL = '( %s / %s )' % (ZFE, L)
    lc = c([lr], 'recnd', '%s e. CC' % L)
    l0 = c([lin8(w, A0, [l1], '0 < %s' % L, {L: lr})], 'gt0ne0d', '%s =/= 0' % L)
    D31 = '( ; 3 1 x. %s )' % ZFK
    d31c = c([numst8(w, A0, '; 3 1', 'CC'), numst8(w, A0, ZFK, 'CC')], 'mulcld', '%s e. CC' % D31)
    d31n = c([lin8(w, A0, [], '0 < %s' % D31, {})], 'gt0ne0d', '%s =/= 0' % D31)
    z1 = c([c([], '1cnd', '1 e. CC'), d31c, lc, d31n, l0], 'divdiv1d', '%s = ( 1 / ( %s x. %s ) )' % (ZL, D31, L))
    mc = c([mr], 'recnd', '%s e. CC' % M)
    W31 = '( %s / ; 3 1 )' % Wt
    z2 = c([c([], '1cnd', '1 e. CC'), mc, numst8(w, A0, '; 3 1', 'CC'), c([mp], 'rpne0d', '%s =/= 0' % M), c([lin8(w, A0, [], '0 < ; 3 1', {})], 'gt0ne0d', '; 3 1 =/= 0')], 'divdiv1d',
           '%s = ( 1 / ( %s x. ; 3 1 ) )' % (W31, M))
    cl = Closure(w, A0, {L: ('CC', lc)})
    cl.atom(L)
    z3 = ringeq(w, A0, '( %s x. %s )' % (D31, L), '( %s x. ; 3 1 )' % M, cl)
    zlw = c([c([z1, c([z3], 'oveq2d', '( 1 / ( %s x. %s ) ) = ( 1 / ( %s x. ; 3 1 ) )' % (D31, L, M))], 'eqtrd', '%s = ( 1 / ( %s x. ; 3 1 ) )' % (ZL, M)), z2], 'eqtr4d', '%s = %s' % (ZL, W31))
    zfr = c([c([], '1red', '1 e. RR'), c([numst8(w, A0, '; 3 1', 'RR'), numst8(w, A0, ZFK, 'RR')], 'remulcld', '%s e. RR' % D31), d31n], 'redivcld', '%s e. RR' % ZFE)
    zlr = c([zfr, lr, l0], 'redivcld', '%s e. RR' % ZL)
    lvF = {Bt: br, Wt: wr, M: mr, IR: irr, ZL: zlr}
    fin = lin8(w, A0, [hi, f1, f2, zlw], ante_of(S['zrhi'])[1], lvF, products=True)
    w.qed([fin], 'idi', S['zrhi'])
    return run8(w)


GENS = {'zrkey': gen_key, 'zrl1': gen_l1, 'zrhi': gen_hi}


def gen_bx():
    from ef4_g import elrab_unpack
    w = W('zrbx', 'A zero of zeta in the box ` [ 1 / 2 , 1 ] x. [ - V , V ] ` other than ` 1 ` has real part ` < 1 ` ( ~ zrl1 ).')
    A0 = ante_of(S['zrbx'])[0]
    c = Ctx(w, A0)
    vp = c.g('V e. RR+'); rin = c.g('R e. %s' % ZBX('V'))
    vr = c([vp], 'rpred', 'V e. RR')
    CA, CB = '( ( 1 / 2 ) + ( _i x. -u V ) )', '( 1 + ( _i x. V ) )'
    RECT = '( %s crect %s )' % (CA, CB)
    rrect, rp, _ = elrab_unpack(w, A0, 'r', RECT, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % E1, 'R', rin)
    rn1 = c([rp], 'simpld', 'R =/= 1'); rz = c([rp], 'simprd', '( %s ` R ) = 0' % E1)
    ic = c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    half = numst8(w, A0, '( 1 / 2 )', 'RR')
    nvr = c([vr], 'renegcld', '-u V e. RR')
    cac = c([c([half], 'recnd', '( 1 / 2 ) e. CC'), c([ic, c([nvr], 'recnd', '-u V e. CC')], 'mulcld', '( _i x. -u V ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = c([c([], '1cnd', '1 e. CC'), c([ic, c([vr], 'recnd', 'V e. CC')], 'mulcld', '( _i x. V ) e. CC')], 'addcld', '%s e. CC' % CB)
    ra = c([half, nvr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 / 2 )' % CA)
    rb = c([c([], '1red', '1 e. RR'), vr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 1' % CB)
    EL = '( R e. CC /\\ ( Re ` R ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` R ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (CA, CB, CA, CB)
    el = c([rrect, c([cac, cbc, w.inst('elcrect')], 'syl2anc', '( R e. %s <-> %s )' % (RECT, EL))], 'mpbid', EL)
    rc = c([el], 'simp1d', 'R e. CC')
    RAr, RBr = '( Re ` %s )' % CA, '( Re ` %s )' % CB
    ic2 = c([el], 'simp2d', '( Re ` R ) e. ( %s [,] %s )' % (RAr, RBr))
    rar, rbr = c([cac], 'recld', '%s e. RR' % RAr), c([cbc], 'recld', '%s e. RR' % RBr)
    e3 = c([ic2, c([rar, rbr, w.inst('elicc2')], 'syl2anc', '( ( Re ` R ) e. ( %s [,] %s ) <-> ( ( Re ` R ) e. RR /\\ %s <_ ( Re ` R ) /\\ ( Re ` R ) <_ %s ) )' % (RAr, RBr, RAr, RBr))],
           'mpbid', '( ( Re ` R ) e. RR /\\ %s <_ ( Re ` R ) /\\ ( Re ` R ) <_ %s )' % (RAr, RBr))
    rre = c([rc], 'recld', '( Re ` R ) e. RR')
    lv = {'( Re ` R )': rre, RAr: rar, RBr: rbr}
    lo = lin8(w, A0, [ra, c([e3], 'simp2d', '%s <_ ( Re ` R )' % RAr)], '( 1 / 2 ) <_ ( Re ` R )', lv)
    hi = lin8(w, A0, [rb, c([e3], 'simp3d', '( Re ` R ) <_ %s' % RBr)], '( Re ` R ) <_ 1', lv)
    # Re R = 1 is impossible
    A1 = '( %s /\\ ( Re ` R ) = 1 )' % A0
    c1 = Ctx(w, A1)
    L_ = lambda st: lift(w, st, A1)
    IM = '( Im ` R )'
    imr = c1([L_(rc)], 'imcld', '%s e. RR' % IM)
    rp1 = c1([c1([L_(rc), w.inst('replim')], 'syl', 'R = ( ( Re ` R ) + ( _i x. %s ) )' % IM), c1([c1([], 'simpr', '( Re ` R ) = 1')], 'oveq1d', '( ( Re ` R ) + ( _i x. %s ) ) = ( 1 + ( _i x. %s ) )' % (IM, IM))],
              'eqtrd', 'R = ( 1 + ( _i x. %s ) )' % IM)
    A2 = '( %s /\\ %s = 0 )' % (A1, IM)
    c2 = Ctx(w, A2)
    r1 = c2([lift(w, rp1, A2), c2([c2([c2([c2([], 'simpr', '%s = 0' % IM)], 'oveq2d', '( _i x. %s ) = ( _i x. 0 )' % IM), c2([lift(w, ic, A2)], 'mul01d', '( _i x. 0 ) = 0')], 'eqtrd', '( _i x. %s ) = 0' % IM)],
                                     'oveq2d', '( 1 + ( _i x. %s ) ) = ( 1 + 0 )' % IM)], 'eqtrd', 'R = ( 1 + 0 )')
    r1b = c2([r1, c2([c2([], '1cnd', '1 e. CC')], 'addridd', '( 1 + 0 ) = 1')], 'eqtrd', 'R = 1')
    imn = c1([L_(rn1), c1([w.s([r1b], 'ex', '( %s -> ( %s = 0 -> R = 1 ) )' % (A1, IM))], 'necon3d', '( R =/= 1 -> %s =/= 0 )' % IM)], 'mpd', '%s =/= 0' % IM)
    zl = c1([c1([imr, imn], 'jca', '( %s e. RR /\\ %s =/= 0 )' % (IM, IM)), w.inst('zrl1')], 'syl', '( %s ` ( 1 + ( _i x. %s ) ) ) =/= 0' % (E1, IM))
    zn = c1([c1([rp1], 'fveq2d', '( %s ` R ) = ( %s ` ( 1 + ( _i x. %s ) ) )' % (E1, E1, IM)), zl], 'eqnetrd', '( %s ` R ) =/= 0' % E1)
    nr = c([L_(rz), c1([zn], 'neneqd', '-. ( %s ` R ) = 0' % E1)], 'pm2.65da', '-. ( Re ` R ) = 1')
    lt = c([rre, c([], '1red', '1 e. RR'), hi, c([c([nr], 'neqned', '( Re ` R ) =/= 1')], 'necomd', '1 =/= ( Re ` R )')], 'leneltd', '( Re ` R ) < 1')
    fin = c([lo, lt], 'jca', ante_of(S['zrbx'])[1])
    w.qed([fin], 'idi', S['zrbx'])
    return run8(w)


GENS['zrbx'] = gen_bx


def gen_box():
    from ef4_g import elrab_unpack, elrab_pack
    from zr_f import e12
    w = W('zrbox', 'Lean ` zeta_box_clearance ` : for ` V > 0 ` there is ` u e. [ 1 / 2 , 1 ) ` with no zero of zeta in ` [ u , 1 ] x. [ - V , V ] ` : the zeros of ` E1 ` in ` [ 1 / 2 , 1 ] x. [ - V , V ] ` form a finite set ( ~ zffin ) whose real parts are ` < 1 ` ( ~ zrbx ), and ` E1 ( 1 ) = 1 ` .')
    A0 = ante_of(S['zrbox'])[0]
    c = Ctx(w, A0)
    vp = c([], 'id', A0)
    vr = c([vp], 'rpred', 'V e. RR')
    Z = ZBX('V')
    half = numst8(w, A0, '( 1 / 2 )', 'RR')
    zf = c([c([c([hol_e1(w, A0), e12(w, A0)], 'jca', '( %s /\\ ( %s ` 2 ) =/= 0 )' % (HOLF(E1, HP0), E1)),
               c([c([half, lin8(w, A0, [], '0 < ( 1 / 2 )', {}), lin8(w, A0, [], '( 1 / 2 ) <_ 1', {})], '3jca', '( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 1 )'), vr], 'jca',
                 '( ( ( 1 / 2 ) e. RR /\\ 0 < ( 1 / 2 ) /\\ ( 1 / 2 ) <_ 1 ) /\\ V e. RR )')], 'jca', ante_of(tsub(stmt('zffin'), {'F': E1, 'A': '( 1 / 2 )', 'T': 'V'}))[0]),
            w.inst('zffin')], 'syl', ante_of(tsub(stmt('zffin'), {'F': E1, 'A': '( 1 / 2 )', 'T': 'V'}))[1])
    zfin = c([zf], 'simpld', '%s e. Fin' % Z)
    fre = c.a1(w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffun')], 'ax-mp', 'Fun Re'), 'Fun Re')
    RZ = '( Re " %s )' % Z
    X = '( %s u. { ( 1 / 2 ) } )' % RZ
    xfin = c([c([fre, zfin, w.inst('imafi')], 'syl2anc', '%s e. Fin' % RZ), c.a1(w.s([], 'snfi', '{ ( 1 / 2 ) } e. Fin'), '{ ( 1 / 2 ) } e. Fin'), w.inst('unfi')], 'syl2anc', '%s e. Fin' % X)
    rzs = c.a1(w.s([w.s([], 'imassrn', '%s C_ ran Re' % RZ), w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('frn')], 'ax-mp', 'ran Re C_ RR')], 'sstri', '%s C_ RR' % RZ), '%s C_ RR' % RZ)
    xss = c([rzs, c([half], 'snssd', '{ ( 1 / 2 ) } C_ RR')], 'unssd', '%s C_ RR' % X)
    hx0 = w.s([w.s([], 'ovex', '( 1 / 2 ) e. _V'), w.inst('snidg')], 'ax-mp', '( 1 / 2 ) e. { ( 1 / 2 ) }')
    hx1 = w.s([hx0, w.inst('elun2')], 'ax-mp', '( 1 / 2 ) e. %s' % X)
    hx = c.a1(hx1, '( 1 / 2 ) e. %s' % X)
    xne = c.a1(w.s([hx1, w.inst('ne0i')], 'ax-mp', '%s =/= (/)' % X), '%s =/= (/)' % X)
    FM = 'E. m e. %s A. y e. %s y <_ m' % (X, X)
    fm = c([xss, xfin, xne, w.inst('fimaxre')], 'syl3anc', FM)
    Am0 = '( %s /\\ m e. %s )' % (A0, X)
    ALY = 'A. y e. %s y <_ m' % X
    Am = '( %s /\\ %s )' % (Am0, ALY)
    cm = Ctx(w, Am)
    L_ = lambda st: lift(w, st, Am)
    mx = cm.g('m e. %s' % X); aly = cm.g(ALY)
    mr = cm([L_(xss), mx], 'sseldd', 'm e. RR')
    # m < 1
    mo = cm([mx, w.s([], 'elun', '( m e. %s <-> ( m e. %s \\/ m e. { ( 1 / 2 ) } ) )' % (X, RZ))], 'sylib',
            '( m e. %s \\/ m e. { ( 1 / 2 ) } )' % RZ)
    Ap = '( %s /\\ p e. %s )' % (Am, Z)
    cp = Ctx(w, Ap)
    bx = cp([cp([lift(w, vp, Ap), cp([], 'simpr', 'p e. %s' % Z)], 'jca', '( V e. RR+ /\\ p e. %s )' % Z), w.inst('zrbx')], 'syl', '( ( 1 / 2 ) <_ ( Re ` p ) /\\ ( Re ` p ) < 1 )')
    Apq = '( %s /\\ ( Re ` p ) = m )' % Ap
    m1a = w.s([w.s([w.s([lift(w, bx, Apq)], 'simprd', '( %s -> ( Re ` p ) < 1 )' % Apq), w.s([], 'simpr', '( %s -> ( Re ` p ) = m )' % Apq)], 'eqbrtrrd', '( %s -> m < 1 )' % Apq)], 'ex',
              '( %s -> ( ( Re ` p ) = m -> m < 1 ) )' % Ap)
    m1b = cm([m1a], 'rexlimdva', '( E. p e. %s ( Re ` p ) = m -> m < 1 )' % Z)
    fvi = w.s([w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('ffun')], 'ax-mp', 'Fun Re')], 'a1i', '( m e. %s -> Fun Re )' % RZ)
    fvj = w.s([fvi, w.s([], 'id', '( m e. %s -> m e. %s )' % (RZ, RZ)), w.inst('fvelima')], 'syl2anc', '( m e. %s -> E. p e. %s ( Re ` p ) = m )' % (RZ, Z))
    ca1 = cm([cm.a1(fvj, '( m e. %s -> E. p e. %s ( Re ` p ) = m )' % (RZ, Z)), m1b], 'syld', '( m e. %s -> m < 1 )' % RZ)
    ms = w.s([], 'elsni', '( m e. { ( 1 / 2 ) } -> m = ( 1 / 2 ) )')
    Ah = '( %s /\\ m e. { ( 1 / 2 ) } )' % Am
    ca2 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> m e. { ( 1 / 2 ) } )' % Ah), ms], 'syl', '( %s -> m = ( 1 / 2 ) )' % Ah), lin8(w, Ah, [], '( 1 / 2 ) < 1', {})],
                     'eqbrtrd', '( %s -> m < 1 )' % Ah)], 'ex', '( %s -> ( m e. { ( 1 / 2 ) } -> m < 1 ) )' % Am)
    m1 = cm([mo, cm([ca1, ca2], 'jaod', '( ( m e. %s \\/ m e. { ( 1 / 2 ) } ) -> m < 1 )' % RZ)], 'mpd', 'm < 1')
    hm, _ = ral_at(w, Am, aly, 'y', '( 1 / 2 )', 'y <_ m', L_(hx))
    U = '( ( m + 1 ) / 2 )'
    ur = cm([cm([mr, cm([], '1red', '1 e. RR')], 'readdcld', '( m + 1 ) e. RR')], 'rehalfcld', '%s e. RR' % U)
    lvm = {'m': mr}
    u1 = lin8(w, Am, [hm], '( 1 / 2 ) <_ %s' % U, lvm)
    u2 = lin8(w, Am, [m1], '%s < 1' % U, lvm)
    CA, CB = '( ( 1 / 2 ) + ( _i x. -u V ) )', '( 1 + ( _i x. V ) )'
    RECT = '( %s crect %s )' % (CA, CB)
    H = '( ( %s <_ ( Re ` s ) /\\ ( Re ` s ) <_ 1 ) /\\ ( abs ` ( Im ` s ) ) <_ V )' % U
    As = '( %s /\\ s e. CC )' % Am
    Ash = '( %s /\\ %s )' % (As, H)
    A3 = '( %s /\\ ( %s ` s ) = 0 )' % (Ash, E1)
    c3 = Ctx(w, A3)
    L3 = lambda st: lift(w, st, A3)
    sc = c3.g('s e. CC'); us = c3.g('%s <_ ( Re ` s )' % U); s1 = c3.g('( Re ` s ) <_ 1'); iv = c3.g('( abs ` ( Im ` s ) ) <_ V'); sz = c3.g('( %s ` s ) = 0' % E1)
    e1n = c3([sz, c3.a1(w.s([], '0ne1', '0 =/= 1'), '0 =/= 1')], 'eqnetrd', '( %s ` s ) =/= 1' % E1)
    imp = c3.a1(w.s([w.s([], 'fveq2', '( s = 1 -> ( %s ` s ) = ( %s ` 1 ) )' % (E1, E1)), w.s([], 'ef5e11', '( %s ` 1 ) = 1' % E1)], 'eqtrdi', '( s = 1 -> ( %s ` s ) = 1 )' % E1),
                '( s = 1 -> ( %s ` s ) = 1 )' % E1)
    sn1 = c3([e1n, c3([imp], 'necon3d', '( ( %s ` s ) =/= 1 -> s =/= 1 )' % E1)], 'mpd', 's =/= 1')
    ic = c3.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    vr3 = L3(vr)
    nvr = c3([vr3], 'renegcld', '-u V e. RR')
    h3 = L3(half)
    cac = c3([c3([h3], 'recnd', '( 1 / 2 ) e. CC'), c3([ic, c3([nvr], 'recnd', '-u V e. CC')], 'mulcld', '( _i x. -u V ) e. CC')], 'addcld', '%s e. CC' % CA)
    cbc = c3([c3([], '1cnd', '1 e. CC'), c3([ic, c3([vr3], 'recnd', 'V e. CC')], 'mulcld', '( _i x. V ) e. CC')], 'addcld', '%s e. CC' % CB)
    RAr, RBr, IAr, IBr = '( Re ` %s )' % CA, '( Re ` %s )' % CB, '( Im ` %s )' % CA, '( Im ` %s )' % CB
    ra = c3([h3, nvr, w.inst('crre')], 'syl2anc', '%s = ( 1 / 2 )' % RAr)
    rb = c3([c3([], '1red', '1 e. RR'), vr3, w.inst('crre')], 'syl2anc', '%s = 1' % RBr)
    ia = c3([h3, nvr, w.inst('crim')], 'syl2anc', '%s = -u V' % IAr)
    ib = c3([c3([], '1red', '1 e. RR'), vr3, w.inst('crim')], 'syl2anc', '%s = V' % IBr)
    rar, rbr = c3([cac], 'recld', '%s e. RR' % RAr), c3([cbc], 'recld', '%s e. RR' % RBr)
    iar, ibr = c3([cac], 'imcld', '%s e. RR' % IAr), c3([cbc], 'imcld', '%s e. RR' % IBr)
    rsr = c3([sc], 'recld', '( Re ` s ) e. RR'); isr = c3([sc], 'imcld', '( Im ` s ) e. RR')
    ab = c3([iv, c3([isr, vr3], 'absled', '( ( abs ` ( Im ` s ) ) <_ V <-> ( -u V <_ ( Im ` s ) /\\ ( Im ` s ) <_ V ) )')], 'mpbid', '( -u V <_ ( Im ` s ) /\\ ( Im ` s ) <_ V )')
    lv3 = {RAr: rar, RBr: rbr, IAr: iar, IBr: ibr, '( Re ` s )': rsr, '( Im ` s )': isr, 'V': vr3, 'm': L3(mr)}
    i1 = c3([c3([rsr, lin8(w, A3, [ra, us, L3(hm)], '%s <_ ( Re ` s )' % RAr, lv3), lin8(w, A3, [rb, s1], '( Re ` s ) <_ %s' % RBr, lv3)], '3jca',
                '( ( Re ` s ) e. RR /\\ %s <_ ( Re ` s ) /\\ ( Re ` s ) <_ %s )' % (RAr, RBr)), c3([rar, rbr, w.inst('elicc2')], 'syl2anc',
                '( ( Re ` s ) e. ( %s [,] %s ) <-> ( ( Re ` s ) e. RR /\\ %s <_ ( Re ` s ) /\\ ( Re ` s ) <_ %s ) )' % (RAr, RBr, RAr, RBr))], 'mpbird', '( Re ` s ) e. ( %s [,] %s )' % (RAr, RBr))
    i2 = c3([c3([isr, lin8(w, A3, [ia, c3([ab], 'simpld', '-u V <_ ( Im ` s )')], '%s <_ ( Im ` s )' % IAr, lv3), lin8(w, A3, [ib, c3([ab], 'simprd', '( Im ` s ) <_ V')], '( Im ` s ) <_ %s' % IBr, lv3)], '3jca',
                '( ( Im ` s ) e. RR /\\ %s <_ ( Im ` s ) /\\ ( Im ` s ) <_ %s )' % (IAr, IBr)), c3([iar, ibr, w.inst('elicc2')], 'syl2anc',
                '( ( Im ` s ) e. ( %s [,] %s ) <-> ( ( Im ` s ) e. RR /\\ %s <_ ( Im ` s ) /\\ ( Im ` s ) <_ %s ) )' % (IAr, IBr, IAr, IBr))], 'mpbird', '( Im ` s ) e. ( %s [,] %s )' % (IAr, IBr))
    EL = '( s e. CC /\\ ( Re ` s ) e. ( %s [,] %s ) /\\ ( Im ` s ) e. ( %s [,] %s ) )' % (RAr, RBr, IAr, IBr)
    srect = c3([c3([sc, i1, i2], '3jca', EL), c3([cac, cbc, w.inst('elcrect')], 'syl2anc', '( s e. %s <-> %s )' % (RECT, EL))], 'mpbird', 's e. %s' % RECT)
    sZ = elrab_pack(w, A3, 'r', RECT, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % E1, 's', srect, c3([sn1, sz], 'jca', '( s =/= 1 /\\ ( %s ` s ) = 0 )' % E1))
    zss = c3([c3.a1(w.s([], 'ssrab2', '%s C_ %s' % (Z, RECT)), '%s C_ %s' % (Z, RECT)), c3([cac, cbc, w.inst('crectss')], 'syl2anc', '%s C_ CC' % RECT)], 'sstrd', '%s C_ CC' % Z)
    zdm = c3([zss, c3.a1(w.s([w.s([], 'ref', 'Re : CC --> RR'), w.inst('fdm')], 'ax-mp', 'dom Re = CC'), 'dom Re = CC')], 'sseqtrrd', '%s C_ dom Re' % Z)
    fv = c3([sZ, c3([L3(fre), zdm, w.inst('funfvima2')], 'syl2anc', '( s e. %s -> ( Re ` s ) e. %s )' % (Z, RZ))], 'mpd', '( Re ` s ) e. %s' % RZ)
    fx = c3([fv, c3.a1(w.s([], 'elun1', '( ( Re ` s ) e. %s -> ( Re ` s ) e. %s )' % (RZ, X)), '( ( Re ` s ) e. %s -> ( Re ` s ) e. %s )' % (RZ, X))], 'mpd', '( Re ` s ) e. %s' % X)
    sm, _ = ral_at(w, A3, L3(aly), 'y', '( Re ` s )', 'y <_ m', fx)
    bad = lin8(w, A3, [us, sm, L3(m1)], '0 < 0', lv3)
    ir = w.s([w.s([w.s([], '0re', '0 e. RR')], 'ltnri', '-. 0 < 0')], 'a1i', '( %s -> -. 0 < 0 )' % A3)
    nn = w.s([bad, ir], 'pm2.65da', '( %s -> -. ( %s ` s ) = 0 )' % (Ash, E1))
    nz = w.s([nn], 'neqned', '( %s -> ( %s ` s ) =/= 0 )' % (Ash, E1))
    als = cm([w.s([nz], 'ex', '( %s -> ( %s -> ( %s ` s ) =/= 0 ) )' % (As, H, E1))], 'ralrimiva', 'A. s e. CC ( %s -> ( %s ` s ) =/= 0 )' % (H, E1))
    BODY = ante_of(S['zrbox'])[1]
    body = BODY[len('E. u e. RR '):]
    eqx, newx = w.wcongr(body, {'u': U}, 'u = %s' % U, {'u': w.s([], 'id', '( u = %s -> u = %s )' % (U, U))})
    Au = '( %s /\\ u = %s )' % (Am, U)
    at = cm([cm([u1, u2], 'jca', top_and(newx)[0]), als], 'jca', newx)
    gu = cm([ur, w.s([eqx], 'adantl', '( %s -> ( %s <-> %s ) )' % (Au, body, newx)), at], 'rspcedvd', BODY)
    rl = c([w.s([gu], 'ex', '( %s -> ( %s -> %s ) )' % (Am0, ALY, BODY))], 'rexlimdva', '( %s -> %s )' % (FM, BODY))
    fin = c([fm, rl], 'mpd', BODY)
    w.qed([fin], 'idi', S['zrbox'])
    return run8(w)


GENS['zrbox'] = gen_box
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
