"""Sortie BM: the per-divisor good-prime count (Lean per_divisor_lower, AGP (4.2) and p. 716):
bmpdlx, bmpdly, bmpdlbt, bmpdlsum, bmpdlsplit, bmpdlinj, bmpdlmain, bmpdl."""
import sys, os
from fractions import Fraction
from math import gcd
sys.path.insert(0, os.path.dirname(__file__))
from bm_base import *


def frac_add(w, A, B):
    """closed step ( A + B ) = C for two nonnegative literal texts, C canonical"""
    va, vb = num.lit_value(A), num.lit_value(B)
    r = va + vb
    C = num.lit_text(r)
    f = '( %s + %s ) = %s' % (A, B, C)
    if f in num._memo(w):
        return num._memo(w)[f]
    s_ = (va.denominator * vb.denominator) // gcd(va.denominator, vb.denominator)
    ts = num.nat_text(s_)

    def scale(L, v):
        """closed step L = ( p' / s ) with p' = v * s"""
        p_, q_ = v.numerator, v.denominator
        k = s_ // q_
        pp = p_ * k
        tp, tq, tk, tpp = num.nat_text(p_), num.nat_text(q_), num.nat_text(k), num.nat_text(pp)
        if q_ == 1:
            if k == 1:
                # L = p, want p = ( p / 1 )
                d1 = num.closed(w, [num.cc_nat(w, p_)], 'div1i', '( %s / 1 ) = %s' % (tp, tp))
                return num.closed(w, [d1], 'eqcomi', '%s = ( %s / 1 )' % (tp, tp))
            c4 = num.closed(w, [num.cc_nat(w, p_), num.cc_nat(w, k), num.ne0_nat(w, k), w.inst('divcan4')], 'mp3an', '( ( %s x. %s ) / %s ) = %s' % (tp, tk, tk, tp))
            e = num.closed(w, [num.mul_nat(w, p_, k)], 'oveq1i', '( ( %s x. %s ) / %s ) = ( %s / %s )' % (tp, tk, tk, tpp, tk))
            return num.closed(w, [c4, e], 'eqtr3i', '%s = ( %s / %s )' % (tp, tpp, tk))
        if k == 1:
            return None
        p2 = num.closed(w, [num.cc_nat(w, q_), num.ne0_nat(w, q_)], 'pm3.2i', '( %s e. CC /\\ %s =/= 0 )' % (tq, tq))
        p3 = num.closed(w, [num.cc_nat(w, k), num.ne0_nat(w, k)], 'pm3.2i', '( %s e. CC /\\ %s =/= 0 )' % (tk, tk))
        c5 = num.closed(w, [num.cc_nat(w, p_), p2, p3, w.inst('divcan5')], 'mp3an', '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (tk, tp, tk, tq, tp, tq))
        e = num.closed(w, [num.mul_nat(w, k, p_), num.mul_nat(w, k, q_)], 'oveq12i', '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (tk, tp, tk, tq, tpp, ts))
        return num.closed(w, [c5, e], 'eqtr3i', '( %s / %s ) = ( %s / %s )' % (tp, tq, tpp, ts))
    sa = scale(A, va); sb = scale(B, vb)
    pa, pb = va.numerator * (s_ // va.denominator), vb.numerator * (s_ // vb.denominator)
    tpa, tpb = num.nat_text(pa), num.nat_text(pb)
    A2 = '( %s / %s )' % (tpa, ts); B2 = '( %s / %s )' % (tpb, ts)
    dd = num.closed(w, [num.cc_nat(w, pa), num.cc_nat(w, pb), num.cc_nat(w, s_), num.ne0_nat(w, s_)], 'divdiri', '( ( %s + %s ) / %s ) = ( %s + %s )' % (tpa, tpb, ts, A2, B2))
    dd2 = num.closed(w, [dd], 'eqcomi', '( %s + %s ) = ( ( %s + %s ) / %s )' % (A2, B2, tpa, tpb, ts))
    an = num.closed(w, [num.add_nat(w, pa, pb)], 'oveq1i', '( ( %s + %s ) / %s ) = ( %s / %s )' % (tpa, tpb, ts, num.nat_text(pa + pb), ts))
    st = num.closed(w, [dd2, an], 'eqtri', '( %s + %s ) = ( %s / %s )' % (A2, B2, num.nat_text(pa + pb), ts))
    red = num._reduce_frac(w, pa + pb, s_)
    if red is not None:
        st = num.closed(w, [st, red], 'eqtri', '( %s + %s ) = %s' % (A2, B2, C))
    else:
        assert '( %s / %s )' % (num.nat_text(pa + pb), ts) == C, (C,)
    if sa is None and sb is None:
        return st
    if sa is not None and sb is not None:
        e12 = num.closed(w, [sa, sb], 'oveq12i', '( %s + %s ) = ( %s + %s )' % (A, B, A2, B2))
    elif sa is not None:
        e12 = num.closed(w, [sa], 'oveq1i', '( %s + %s ) = ( %s + %s )' % (A, B, A2, B2))
    else:
        e12 = num.closed(w, [sb], 'oveq2i', '( %s + %s ) = ( %s + %s )' % (A, B, A2, B2))
    return num.closed(w, [e12, st], 'eqtri', f)


X1 = X1B('X'); XBB = XB('X'); XHH = XH('X'); LX = '( log ` X )'
D_ = '( E x. %s )' % X1
Y_ = YC('X', 'E')
WT_ = WT('X', 'E')
PHE = '( phi ` E )'


def lit(w, ante, t):
    return w.s([num.real(w, t)], 'a1i', '( %s -> %s e. RR )' % (ante, t))


def xfacts(w, ante, xhyp):
    """steps for every leaf of XF, plus X e. RR, 3 <_ X, 0 <_ X, X e. NN0, X e. ZZ, X e. CC, E-free"""
    xf = ap(w, ante, [xhyp], 'bmpdlx', XF)
    out = unpack_step(w, ante, xf, XF)
    xn0 = w.s([xhyp], 'simpld', '( %s -> X e. NN0 )' % ante)
    out['X e. NN0'] = xn0
    out['3 <_ X'] = w.s([xhyp], 'simprd', '( %s -> 3 <_ X )' % ante)
    out['X e. RR'] = w.s([xn0], 'nn0red', '( %s -> X e. RR )' % ante)
    out['X e. ZZ'] = w.s([xn0], 'nn0zd', '( %s -> X e. ZZ )' % ante)
    out['X e. CC'] = w.s([xn0], 'nn0cnd', '( %s -> X e. CC )' % ante)
    out['0 <_ X'] = w.s([xn0], 'nn0ge0d', '( %s -> 0 <_ X )' % ante)
    for t in (X1, XBB, XHH, LX):
        out['%s e. RR' % t] = w.s([out['%s e. RR+' % t]], 'rpred', '( %s -> %s e. RR )' % (ante, t))
        out['0 <_ %s' % t] = w.s([out['%s e. RR+' % t]], 'rpge0d', '( %s -> 0 <_ %s )' % (ante, t))
        out['0 < %s' % t] = w.s([out['%s e. RR+' % t]], 'rpgt0d', '( %s -> 0 < %s )' % (ante, t))
    return out


def efacts(w, ante, ehyp):
    out = {}
    en = w.s([ehyp], 'simpld', '( %s -> E e. NN )' % ante)
    out['E e. NN'] = en
    out['E <_ %s' % XBB] = w.s([ehyp], 'simprd', '( %s -> E <_ %s )' % (ante, XBB))
    out['E e. RR'] = w.s([en], 'nnred', '( %s -> E e. RR )' % ante)
    out['E e. ZZ'] = w.s([en], 'nnzd', '( %s -> E e. ZZ )' % ante)
    out['E e. CC'] = w.s([en], 'nncnd', '( %s -> E e. CC )' % ante)
    out['E e. RR+'] = w.s([en], 'nnrpd', '( %s -> E e. RR+ )' % ante)
    out['1 <_ E'] = w.s([en], 'nnge1d', '( %s -> 1 <_ E )' % ante)
    out['0 < E'] = w.s([en], 'nngt0d', '( %s -> 0 < E )' % ante)
    out['0 <_ E'] = w.s([w.s([en], 'nnnn0d', '( %s -> E e. NN0 )' % ante)], 'nn0ge0d', '( %s -> 0 <_ E )' % ante)
    out['E =/= 0'] = w.s([en], 'nnne0d', '( %s -> E =/= 0 )' % ante)
    pn = w.s([en], 'phicld', '( %s -> %s e. NN )' % (ante, PHE))
    out['%s e. NN' % PHE] = pn
    out['%s e. RR' % PHE] = w.s([pn], 'nnred', '( %s -> %s e. RR )' % (ante, PHE))
    out['%s e. RR+' % PHE] = w.s([pn], 'nnrpd', '( %s -> %s e. RR+ )' % (ante, PHE))
    out['%s e. CC' % PHE] = w.s([pn], 'nncnd', '( %s -> %s e. CC )' % (ante, PHE))
    out['0 < %s' % PHE] = w.s([pn], 'nngt0d', '( %s -> 0 < %s )' % (ante, PHE))
    out['0 <_ %s' % PHE] = w.s([w.s([pn], 'nnnn0d', '( %s -> %s e. NN0 )' % (ante, PHE))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ante, PHE))
    out['%s =/= 0' % PHE] = w.s([pn], 'nnne0d', '( %s -> %s =/= 0 )' % (ante, PHE))
    return out


def yfacts(w, ante, xhyp, h100, ehyp):
    yf = ap(w, ante, [xhyp, h100, ehyp], 'bmpdly', YF)
    out = unpack_step(w, ante, yf, YF)
    yn0 = out['%s e. NN0' % Y_]
    out['%s e. RR' % Y_] = w.s([yn0], 'nn0red', '( %s -> %s e. RR )' % (ante, Y_))
    out['%s e. ZZ' % Y_] = w.s([yn0], 'nn0zd', '( %s -> %s e. ZZ )' % (ante, Y_))
    out['0 <_ %s' % Y_] = w.s([yn0], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ante, Y_))
    return out


def gen_x():
    w = W('bmpdlx', 'Real facts about the scale ` X >_ 3 ` of ~ bmpdl : positivity of ` X ` , ` log X ` and the three powers, and ` X ^ ( 21 / 100 ) X ^ ( 79 / 100 ) = X ` , ` X ^ ( 79 / 200 ) X ^ ( 79 / 200 ) = X ^ ( 79 / 100 ) ` (~ cxpadd ).')
    A = XHYP
    s = S_(w, A)
    xn0 = s([], 'simpl', 'X e. NN0'); x3 = s([], 'simpr', '3 <_ X')
    xr = s([xn0], 'nn0red', 'X e. RR')
    x1 = lin.linarith(w, A, [x3], '1 < X', leaves={'X': xr})
    x0 = lin.linarith(w, A, [x3], '0 < X', leaves={'X': xr})
    xrp = s([xr, x0], 'elrpd', 'X e. RR+')
    lx = s([xr, x1], 'rplogcld', '%s e. RR+' % LX)
    p1 = s([xrp, lit(w, A, F79)], 'rpcxpcld', '%s e. RR+' % X1)
    p2 = s([xrp, lit(w, A, F21)], 'rpcxpcld', '%s e. RR+' % XBB)
    p3 = s([xrp, lit(w, A, F79H)], 'rpcxpcld', '%s e. RR+' % XHH)
    xc = s([xr], 'recnd', 'X e. CC'); xn0_ = s([xrp], 'rpne0d', 'X =/= 0')
    c21 = s([num.cc(w, F21)], 'a1i', '%s e. CC' % F21); c79 = s([num.cc(w, F79)], 'a1i', '%s e. CC' % F79); c79h = s([num.cc(w, F79H)], 'a1i', '%s e. CC' % F79H)
    e1 = s([xc, xn0_, c21, c79], 'cxpaddd', '( X ^c ( %s + %s ) ) = ( %s x. %s )' % (F21, F79, XBB, X1))
    fa = frac_add(w, F21, F79)
    e2 = s([s([fa], 'a1i', '( %s + %s ) = 1' % (F21, F79))], 'oveq2d', '( X ^c ( %s + %s ) ) = ( X ^c 1 )' % (F21, F79))
    e3 = s([xc], 'cxp1d', '( X ^c 1 ) = X')
    e4 = s([s([e1, e2], 'eqtr3d', '( %s x. %s ) = ( X ^c 1 )' % (XBB, X1)), e3], 'eqtrd', '( %s x. %s ) = X' % (XBB, X1))
    f1 = s([xc, xn0_, c79h, c79h], 'cxpaddd', '( X ^c ( %s + %s ) ) = ( %s x. %s )' % (F79H, F79H, XHH, XHH))
    fb = frac_add(w, F79H, F79H)
    f2 = s([s([fb], 'a1i', '( %s + %s ) = %s' % (F79H, F79H, F79))], 'oveq2d', '( X ^c ( %s + %s ) ) = %s' % (F79H, F79H, X1))
    f3 = s([f1, f2], 'eqtr3d', '( %s x. %s ) = %s' % (XHH, XHH, X1))
    a1 = s([xrp, x1, lx], '3jca', '( X e. RR+ /\\ 1 < X /\\ %s e. RR+ )' % LX)
    a2 = s([p1, p2, p3], '3jca', '( %s e. RR+ /\\ %s e. RR+ /\\ %s e. RR+ )' % (X1, XBB, XHH))
    a3 = s([e4, f3], 'jca', '( ( %s x. %s ) = X /\\ ( %s x. %s ) = %s )' % (XBB, X1, XHH, XHH, X1))
    w.qed([a1, a2, a3], '3jca', S['bmpdlx'])
    return go(w)


def gen_y():
    w = W('bmpdly', 'The cutoff ` Y = ceil ( E X ^ ( 79 / 100 ) ) ` of ~ bmpdl (Lean ` hy_lb ` , ` hy_ub ` , ` hy_slack ` ): a natural number between ` E X ^ ( 79 / 100 ) ` and ` X ` , within ` 1 ` and within a factor ` 101 / 100 ` of ` E X ^ ( 79 / 100 ) ` .')
    A = '( %s /\\ ( %s <_ %s /\\ %s ) )' % (XHYP, N100, X1, EHYP)
    s = S_(w, A)
    xhyp = s([], 'simpl', XHYP); h100 = s([], 'simprl', '%s <_ %s' % (N100, X1)); ehyp = s([], 'simprr', EHYP)
    xf = xfacts(w, A, xhyp); ef = efacts(w, A, ehyp)
    x1r = xf['%s e. RR' % X1]; x1ge0 = xf['0 <_ %s' % X1]
    dr = s([ef['E e. RR'], x1r], 'remulcld', '%s e. RR' % D_)
    x1le = s([x1r, ef['E e. RR'], x1ge0, ef['1 <_ E']], 'lemulge12d', '%s <_ %s' % (X1, D_))
    h100r = lit(w, A, N100)
    d100 = s([h100r, x1r, dr, h100, x1le], 'letrd', '%s <_ %s' % (N100, D_))
    yz = s([dr], 'ceilcld', '%s e. ZZ' % Y_); yr = s([yz], 'zred', '%s e. RR' % Y_)
    ylb = s([dr], 'ceilged', '%s <_ %s' % (D_, Y_))
    ym1 = s([dr, w.inst('ceilm1lt')], 'syl', '( %s - 1 ) < %s' % (Y_, D_))
    yub = lin.linarith(w, A, [ym1], '%s < ( %s + 1 )' % (Y_, D_), leaves={Y_: yr, D_: dr}, atoms=[D_, Y_])
    y0 = lin.linarith(w, A, [d100, ylb], '0 <_ %s' % Y_, leaves={Y_: yr, D_: dr}, atoms=[D_, Y_])
    yn0 = s([s([yz, y0], 'jca', '( %s e. ZZ /\\ 0 <_ %s )' % (Y_, Y_)), w.s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (Y_, Y_, Y_))], 'sylibr', '%s e. NN0' % Y_)
    ysl = lin.linarith(w, A, [yub, d100], '%s <_ ( ( ; ; 1 0 1 / ; ; 1 0 0 ) x. %s )' % (Y_, D_), leaves={Y_: yr, D_: dr}, atoms=[D_, Y_], fast=False)
    dlex = s([ef['E e. RR'], xf['%s e. RR' % XBB], x1r, x1ge0, ef['E <_ %s' % XBB]], 'lemul1ad', '%s <_ ( %s x. %s )' % (D_, XBB, X1))
    dlex2 = s([dlex, xf['( %s x. %s ) = X' % (XBB, X1)]], 'breqtrd', '%s <_ X' % D_)
    ylx = s([dr, xf['X e. ZZ'], dlex2, w.inst('ceille')], 'syl3anc', '%s <_ X' % Y_)
    a1 = s([yn0, ylb], 'jca', '( %s e. NN0 /\\ %s <_ %s )' % (Y_, D_, Y_))
    a2 = s([yub, ysl], 'jca', '( %s < ( %s + 1 ) /\\ %s <_ ( ( ; ; 1 0 1 / ; ; 1 0 0 ) x. %s ) )' % (Y_, D_, Y_, D_))
    a3 = s([x1le, ylx], 'jca', '( %s <_ %s /\\ %s <_ X )' % (X1, D_, Y_))
    w.qed([a1, a2, a3], '3jca', S['bmpdly'])
    return go(w)


def gen_bt():
    w = W('bmpdlbt', 'Brun-Titchmarsh at the modulus ` E Q ` for one prime ` Q ` dividing the sieve modulus (Lean ` hbadq ` in ` per_divisor_lower ` , AGP p. 716): the primes up to ` Y ` congruent to ` 1 ` mod ` E Q ` number at most ` ( 1212 / 79 ) W / Q ` with ` W = E X ^ ( 79 / 100 ) / ( phi ( E ) log X ) ` (~ bruntitex through the hypothesis, ~ bmtot ).')
    A = '( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( Q e. Prime /\\ Q <_ %s ) )' % (XHYP, N100, X1, EHYP, THYP, BTBODY('T'), XHH)
    s = S_(w, A)
    u = unpack(w, A)
    xhyp = u[XHYP] if XHYP in u else None
    # unpack gives leaves; rebuild the group steps we need
    xhyp = w.s([u['X e. NN0'], u['3 <_ X']], 'jca', '( %s -> %s )' % (A, XHYP))
    ehyp = w.s([u['E e. NN'], u['E <_ %s' % XBB]], 'jca', '( %s -> %s )' % (A, EHYP))
    h100 = u['%s <_ %s' % (N100, X1)]
    xf = xfacts(w, A, xhyp); ef = efacts(w, A, ehyp); yf = yfacts(w, A, xhyp, h100, ehyp)
    tr_, tle, bt = u['T e. RR'], u['T <_ %s' % X1], u[BTBODY('T')]
    qp, qle = u['Q e. Prime'], u['Q <_ %s' % XHH]
    xr, x1r, xhr, lxr = xf['X e. RR'], xf['%s e. RR' % X1], xf['%s e. RR' % XHH], xf['%s e. RR' % LX]
    er, e1 = ef['E e. RR'], ef['1 <_ E']
    yr, yn0, ylb, yub, ysl, ylx = yf['%s e. RR' % Y_], yf['%s e. NN0' % Y_], yf['%s <_ %s' % (D_, Y_)], yf['%s < ( %s + 1 )' % (Y_, D_)], yf['%s <_ ( ( ; ; 1 0 1 / ; ; 1 0 0 ) x. %s )' % (Y_, D_)], yf['%s <_ X' % Y_]
    x1le = yf['%s <_ %s' % (X1, D_)]
    dr = s([er, x1r], 'remulcld', '%s e. RR' % D_)
    qn = s([qp, w.inst('prmnn')], 'syl', 'Q e. NN'); qr = s([qn], 'nnred', 'Q e. RR'); qz = s([qn], 'nnzd', 'Q e. ZZ'); qc = s([qn], 'nncnd', 'Q e. CC')
    qrp = s([qn], 'nnrpd', 'Q e. RR+'); qge0 = s([qrp], 'rpge0d', '0 <_ Q'); qne0 = s([qn], 'nnne0d', 'Q =/= 0')
    q2 = s([qp, w.inst('prmuz2')], 'syl', 'Q e. ( ZZ>= ` 2 )')
    q2le = s([q2, w.inst('eluzle')], 'syl', '2 <_ Q')
    EQ = '( E x. Q )'
    eqn = s([ef['E e. NN'], qn], 'nnmulcld', '%s e. NN' % EQ); eqr = s([eqn], 'nnred', '%s e. RR' % EQ); eqz = s([eqn], 'nnzd', '%s e. ZZ' % EQ)
    eqrp = s([eqn], 'nnrpd', '%s e. RR+' % EQ)
    # 2 <_ E Q
    eq2a = s([qr, er, qge0, e1], 'lemulge12d', 'Q <_ %s' % EQ)
    eq2 = s([lit(w, A, '2'), qr, eqr, q2le, eq2a], 'letrd', '2 <_ %s' % EQ)
    equz = s([s([s([w.s([], '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), eqz, eq2], '3jca', '( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s )' % (EQ, EQ)), w.s([], 'eluz2', '( %s e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s ) )' % (EQ, EQ, EQ))], 'sylibr', '%s e. ( ZZ>= ` 2 )' % EQ)
    # T <_ Y
    tley = s([tr_, x1r, yr, tle, s([x1r, dr, yr, x1le, ylb], 'letrd', '%s <_ %s' % (X1, Y_))], 'letrd', 'T <_ %s' % Y_)
    # E Q <_ Y ^c ( 19 / 20 )
    F1920_ = F1920; F120_ = F120; F212000 = num.lit_text(Fraction(21, 2000)); F1501 = num.lit_text(Fraction(1501, 2000))
    erp = ef['E e. RR+']
    E19 = '( E ^c %s )' % F1920_; E120 = '( E ^c %s )' % F120_
    e19 = s([erp, lit(w, A, F1920_)], 'rpcxpcld', '%s e. RR+' % E19); e120 = s([erp, lit(w, A, F120_)], 'rpcxpcld', '%s e. RR+' % E120)
    ec = ef['E e. CC']; en0 = ef['E =/= 0']
    es1 = s([ec, en0, s([num.cc(w, F1920_)], 'a1i', '%s e. CC' % F1920_), s([num.cc(w, F120_)], 'a1i', '%s e. CC' % F120_)], 'cxpaddd', '( E ^c ( %s + %s ) ) = ( %s x. %s )' % (F1920_, F120_, E19, E120))
    es2 = s([s([frac_add(w, F1920_, F120_)], 'a1i', '( %s + %s ) = 1' % (F1920_, F120_))], 'oveq2d', '( E ^c ( %s + %s ) ) = ( E ^c 1 )' % (F1920_, F120_))
    es3 = s([s([es1, es2], 'eqtr3d', '( %s x. %s ) = ( E ^c 1 )' % (E19, E120)), s([ec], 'cxp1d', '( E ^c 1 ) = E')], 'eqtrd', '( %s x. %s ) = E' % (E19, E120))
    # E ^c ( 1 / 20 ) <_ X ^c ( 21 / 2000 )
    xrp = xf['X e. RR+']
    XB120 = '( %s ^c %s )' % (XBB, F120_); X212 = '( X ^c %s )' % F212000
    h1 = s([er, ef['0 <_ E'], xf['%s e. RR' % XBB], lit(w, A, F120_), s([num.fact(w, F120_, 'ge0')], 'a1i', '0 <_ %s' % F120_), ef['E <_ %s' % XBB]], 'cxple2ad', '%s <_ %s' % (E120, XB120))
    h2 = s([xrp, lit(w, A, F21), s([num.cc(w, F120_)], 'a1i', '%s e. CC' % F120_)], 'cxpmuld', '( X ^c ( %s x. %s ) ) = %s' % (F21, F120_, XB120))
    h3 = s([s([num.mul_lits(w, F21, F120_)], 'a1i', '( %s x. %s ) = %s' % (F21, F120_, F212000))], 'oveq2d', '( X ^c ( %s x. %s ) ) = %s' % (F21, F120_, X212))
    h4 = s([h2, h3], 'eqtr3d', '%s = %s' % (XB120, X212))
    h5 = s([h1, h4], 'breqtrd', '%s <_ %s' % (E120, X212))
    x212 = s([xrp, lit(w, A, F212000)], 'rpcxpcld', '%s e. RR+' % X212)
    # E ^c ( 1 / 20 ) x. Q <_ X ^c ( 811 / 2000 ) <_ X ^c ( 1501 / 2000 )
    h6 = s([s([e120], 'rpred', '%s e. RR' % E120), s([x212], 'rpred', '%s e. RR' % X212), qr, xhr, s([e120], 'rpge0d', '0 <_ %s' % E120), qge0, h5, qle], 'lemul12ad', '( %s x. Q ) <_ ( %s x. %s )' % (E120, X212, XHH))
    h7 = s([xf['X e. CC'], xf['X =/= 0'] if 'X =/= 0' in xf else s([xrp], 'rpne0d', 'X =/= 0'), s([num.cc(w, F212000)], 'a1i', '%s e. CC' % F212000), s([num.cc(w, F79H)], 'a1i', '%s e. CC' % F79H)], 'cxpaddd', '( X ^c ( %s + %s ) ) = ( %s x. %s )' % (F212000, F79H, X212, XHH))
    F811 = num.lit_text(Fraction(811, 2000))
    h8 = s([s([frac_add(w, F212000, F79H)], 'a1i', '( %s + %s ) = %s' % (F212000, F79H, F811))], 'oveq2d', '( X ^c ( %s + %s ) ) = ( X ^c %s )' % (F212000, F79H, F811))
    h9 = s([h7, h8], 'eqtr3d', '( %s x. %s ) = ( X ^c %s )' % (X212, XHH, F811))
    h10 = s([xr, s([xf['1 < X']], 'ltled', '1 <_ X'), lit(w, A, F811), lit(w, A, F1501), s([num.le_lit(w, F811, F1501)], 'a1i', '%s <_ %s' % (F811, F1501))], 'cxplead', '( X ^c %s ) <_ ( X ^c %s )' % (F811, F1501))
    X1501 = '( X ^c %s )' % F1501
    h11a = s([h6, h9], 'breqtrd', '( %s x. Q ) <_ ( X ^c %s )' % (E120, F811))
    x1501 = s([xrp, lit(w, A, F1501)], 'rpcxpcld', '%s e. RR+' % X1501)
    h11 = s([s([s([e120], 'rpred', '%s e. RR' % E120), qr], 'remulcld', '( %s x. Q ) e. RR' % E120), s([s([xrp, lit(w, A, F811)], 'rpcxpcld', '( X ^c %s ) e. RR+' % F811)], 'rpred', '( X ^c %s ) e. RR' % F811), s([x1501], 'rpred', '%s e. RR' % X1501), h11a, h10], 'letrd', '( %s x. Q ) <_ %s' % (E120, X1501))
    # X ^c ( 1501 / 2000 ) = X1 ^c ( 19 / 20 )
    X119 = '( %s ^c %s )' % (X1, F1920_)
    h12 = s([xrp, lit(w, A, F79), s([num.cc(w, F1920_)], 'a1i', '%s e. CC' % F1920_)], 'cxpmuld', '( X ^c ( %s x. %s ) ) = %s' % (F79, F1920_, X119))
    h13 = s([s([num.mul_lits(w, F79, F1920_)], 'a1i', '( %s x. %s ) = %s' % (F79, F1920_, F1501))], 'oveq2d', '( X ^c ( %s x. %s ) ) = %s' % (F79, F1920_, X1501))
    h14 = s([h13, h12], 'eqtr3d', '%s = %s' % (X1501, X119))
    # E Q = E19 x. ( E120 x. Q ) <_ E19 x. X119 = D ^c ( 19 / 20 ) <_ Y ^c ( 19 / 20 )
    e19r = s([e19], 'rpred', '%s e. RR' % E19); e19c = s([e19r], 'recnd', '%s e. CC' % E19); e120c = s([e120], 'rpcnd', '%s e. CC' % E120)
    k1 = s([e19c, e120c, qc], 'mulassd', '( ( %s x. %s ) x. Q ) = ( %s x. ( %s x. Q ) )' % (E19, E120, E19, E120))
    k2 = s([es3], 'oveq1d', '( ( %s x. %s ) x. Q ) = %s' % (E19, E120, EQ))
    k3 = s([k2, k1], 'eqtr3d', '%s = ( %s x. ( %s x. Q ) )' % (EQ, E19, E120))
    k4 = s([s([s([e120], 'rpred', '%s e. RR' % E120), qr], 'remulcld', '( %s x. Q ) e. RR' % E120), s([x1501], 'rpred', '%s e. RR' % X1501), e19r, s([e19], 'rpge0d', '0 <_ %s' % E19), h11], 'lemul2ad', '( %s x. ( %s x. Q ) ) <_ ( %s x. %s )' % (E19, E120, E19, X1501))
    k5 = s([h14], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (E19, X1501, E19, X119))
    D19 = '( %s ^c %s )' % (D_, F1920_)
    k6 = s([s([er, ef['0 <_ E']], 'jca', '( E e. RR /\\ 0 <_ E )'), s([x1r, xf['0 <_ %s' % X1]], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (X1, X1)), s([num.cc(w, F1920_)], 'a1i', '%s e. CC' % F1920_), w.inst('mulcxp')], 'syl3anc', '%s = ( %s x. %s )' % (D19, E19, X119))
    k7 = s([s([k4, k5], 'breqtrd', '( %s x. ( %s x. Q ) ) <_ ( %s x. %s )' % (E19, E120, E19, X119)), k6], 'breqtrrd', '( %s x. ( %s x. Q ) ) <_ %s' % (E19, E120, D19))
    k8 = s([k3, k7], 'eqbrtrd', '%s <_ %s' % (EQ, D19))
    dge0 = s([er, x1r, ef['0 <_ E'], xf['0 <_ %s' % X1]], 'mulge0d', '0 <_ %s' % D_)
    Y19 = '( %s ^c %s )' % (Y_, F1920_)
    k9 = s([dr, dge0, yr, lit(w, A, F1920_), s([num.fact(w, F1920_, 'ge0')], 'a1i', '0 <_ %s' % F1920_), ylb], 'cxple2ad', '%s <_ %s' % (D19, Y19))
    d19r = s([dr, dge0, lit(w, A, F1920_)], 'recxpcld', '%s e. RR' % D19)
    y19r = s([yr, yf['0 <_ %s' % Y_], lit(w, A, F1920_)], 'recxpcld', '%s e. RR' % Y19)
    hmy = s([eqr, d19r, y19r, k8, k9], 'letrd', '%s <_ %s' % (EQ, Y19))
    # the Brun-Titchmarsh instance
    body_y = BTBODY('T')[len('A. y e. NN0 '):]
    assert body_y.startswith('A. m e.')
    body_ym = body_y[len('A. m e. %s ' % Z2):]
    c1, b1 = wc(w, body_ym, 'y', Y_)
    c2, b2 = wc(w, b1, 'm', EQ)
    inst = s([c1, c2, bt, yn0, equz], 'rspc2dv', b2)
    AQ_ = AQ(Y_, 'E', 'Q')
    BND_ = '( ( 3 x. %s ) / ( ( phi ` %s ) x. ( log ` ( %s / %s ) ) ) )' % (Y_, EQ, Y_, EQ)
    assert b2 == '( ( T <_ %s /\\ %s <_ %s ) -> ( # ` %s ) <_ %s )' % (Y_, EQ, Y19, AQ_, BND_), b2[:300]
    btq = s([s([tley, hmy], 'jca', '( T <_ %s /\\ %s <_ %s )' % (Y_, EQ, Y19)), inst], 'mpd', '( # ` %s ) <_ %s' % (AQ_, BND_))
    # the logarithm: ( 79 / 200 ) log X <_ log ( Y / E Q )
    xhc = s([xhr], 'recnd', '%s e. CC' % XHH)
    m1 = s([qr, xhr, er, ef['0 <_ E'], qle], 'lemul2ad', '( E x. Q ) <_ ( E x. %s )' % XHH)
    m2 = s([eqr, s([er, xhr], 'remulcld', '( E x. %s ) e. RR' % XHH), xhr, xf['0 <_ %s' % XHH], m1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( E x. %s ) )' % (XHH, EQ, XHH, XHH))
    m3 = s([xhc, ec, xhc], 'mul12d', '( %s x. ( E x. %s ) ) = ( E x. ( %s x. %s ) )' % (XHH, XHH, XHH, XHH))
    m4 = s([xf['( %s x. %s ) = %s' % (XHH, XHH, X1)]], 'oveq2d', '( E x. ( %s x. %s ) ) = %s' % (XHH, XHH, D_))
    m5 = s([m2, s([m3, m4], 'eqtrd', '( %s x. ( E x. %s ) ) = %s' % (XHH, XHH, D_))], 'breqtrd', '( %s x. %s ) <_ %s' % (XHH, EQ, D_))
    m6 = s([s([xhr, eqr], 'remulcld', '( %s x. %s ) e. RR' % (XHH, EQ)), dr, yr, m5, ylb], 'letrd', '( %s x. %s ) <_ %s' % (XHH, EQ, Y_))
    m7 = s([m6, s([xhr, yr, eqrp], 'lemuldivd', '( ( %s x. %s ) <_ %s <-> %s <_ ( %s / %s ) )' % (XHH, EQ, Y_, XHH, Y_, EQ))], 'mpbid', '%s <_ ( %s / %s )' % (XHH, Y_, EQ))
    YQ = '( %s / %s )' % (Y_, EQ)
    ypos = lin.linarith(w, A, [yf['%s <_ %s' % (X1, D_)], ylb, xf['0 < %s' % X1]], '0 < %s' % Y_, leaves={Y_: yr, D_: dr, X1: x1r}, atoms=[Y_, D_, X1], fast=False)
    yrp = s([yr, ypos], 'elrpd', '%s e. RR+' % Y_)
    yqrp = s([yrp, eqrp], 'rpdivcld', '%s e. RR+' % YQ)
    m8 = s([m7, s([xf['%s e. RR+' % XHH], yqrp], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) )' % (XHH, YQ, XHH, YQ))], 'mpbid', '( log ` %s ) <_ ( log ` %s )' % (XHH, YQ))
    m9 = s([xrp, lit(w, A, F79H)], 'logcxpd', '( log ` %s ) = ( %s x. %s )' % (XHH, F79H, LX))
    LQ = '( log ` %s )' % YQ
    hlogq = s([m9, m8], 'eqbrtrrd', '( %s x. %s ) <_ %s' % (F79H, LX, LQ))
    lqr = s([yqrp], 'relogcld', '%s e. RR' % LQ)
    # the totient: phi ( E ) ( Q / 2 ) <_ phi ( E Q )
    PHEQ = '( phi ` %s )' % EQ
    tot = ap(w, A, [ef['E e. NN'], qp], 'bmtot', '( %s x. ( Q - 1 ) ) <_ %s' % (PHE, PHEQ))
    q1r = s([qr, lit(w, A, '1')], 'resubcld', '( Q - 1 ) e. RR')
    qh = lin.linarith(w, A, [q2le], '( Q / 2 ) <_ ( Q - 1 )', leaves={'Q': qr})
    qhr = s([qr], 'rehalfcld', '( Q / 2 ) e. RR')
    t1 = s([qhr, q1r, ef['%s e. RR' % PHE], ef['0 <_ %s' % PHE], qh], 'lemul2ad', '( %s x. ( Q / 2 ) ) <_ ( %s x. ( Q - 1 ) )' % (PHE, PHE))
    pheqn = s([eqn], 'phicld', '%s e. NN' % PHEQ); pheqr = s([pheqn], 'nnred', '%s e. RR' % PHEQ)
    hphi = s([s([ef['%s e. RR' % PHE], qhr], 'remulcld', '( %s x. ( Q / 2 ) ) e. RR' % PHE), s([ef['%s e. RR' % PHE], q1r], 'remulcld', '( %s x. ( Q - 1 ) ) e. RR' % PHE), pheqr, t1, tot], 'letrd', '( %s x. ( Q / 2 ) ) <_ %s' % (PHE, PHEQ))
    # the products
    K = '( ( %s x. %s ) x. ( 1 / Q ) )' % (F121279, WT_)
    G1 = '( %s x. ( Q / 2 ) )' % PHE; G2 = '( %s x. %s )' % (F79H, LX)
    g1r = s([ef['%s e. RR' % PHE], qhr], 'remulcld', '%s e. RR' % G1); g2r = s([lit(w, A, F79H), lxr], 'remulcld', '%s e. RR' % G2)
    g1ge0 = s([ef['%s e. RR' % PHE], qhr, ef['0 <_ %s' % PHE], lin.linarith(w, A, [qge0], '0 <_ ( Q / 2 )', leaves={'Q': qr})], 'mulge0d', '0 <_ %s' % G1)
    g2ge0 = s([lit(w, A, F79H), lxr, s([num.fact(w, F79H, 'ge0')], 'a1i', '0 <_ %s' % F79H), xf['0 <_ %s' % LX]], 'mulge0d', '0 <_ %s' % G2)
    lqge0 = lin.linarith(w, A, [hlogq, g2ge0], '0 <_ %s' % LQ, leaves={LQ: lqr, G2: g2r}, atoms=[LQ, G2])
    ulp = s([ef['%s e. RR+' % PHE], xf['%s e. RR+' % LX]], 'rpmulcld', '( %s x. %s ) e. RR+' % (PHE, LX))
    drp = s([erp, xf['%s e. RR+' % X1]], 'rpmulcld', '%s e. RR+' % D_)
    wtrp = s([drp, ulp], 'rpdivcld', '%s e. RR+' % WT_)
    wtr = s([wtrp], 'rpred', '%s e. RR' % WT_); wtge0 = s([wtrp], 'rpge0d', '0 <_ %s' % WT_)
    iqrp = s([qrp], 'rprecred', '( 1 / Q ) e. RR')
    iqge0 = s([s([qrp], 'rpreccld', '( 1 / Q ) e. RR+')], 'rpge0d', '0 <_ ( 1 / Q )')
    kr = s([s([lit(w, A, F121279), wtr], 'remulcld', '( %s x. %s ) e. RR' % (F121279, WT_)), iqrp], 'remulcld', '%s e. RR' % K)
    kge0 = s([s([lit(w, A, F121279), wtr], 'remulcld', '( %s x. %s ) e. RR' % (F121279, WT_)), iqrp, s([lit(w, A, F121279), wtr, s([num.fact(w, F121279, 'ge0')], 'a1i', '0 <_ %s' % F121279), wtge0], 'mulge0d', '0 <_ ( %s x. %s )' % (F121279, WT_)), iqge0], 'mulge0d', '0 <_ %s' % K)
    p1 = s([g1r, pheqr, g2r, lqr, g1ge0, g2ge0, hphi, hlogq], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (G1, G2, PHEQ, LQ))
    p2 = s([s([g1r, g2r], 'remulcld', '( %s x. %s ) e. RR' % (G1, G2)), s([pheqr, lqr], 'remulcld', '( %s x. %s ) e. RR' % (PHEQ, LQ)), kr, kge0, p1], 'lemul1ad', '( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. %s )' % (G1, G2, K, PHEQ, LQ, K))
    # the identity ( ( G1 x. G2 ) x. K ) = ( 303 / 100 ) x. D
    e_1 = s([s([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC'), qc, qne0], 'divcan2d', '( Q x. ( 1 / Q ) ) = 1')
    e_2 = s([s([dr], 'recnd', '%s e. CC' % D_), s([ulp], 'rpcnd', '( %s x. %s ) e. CC' % (PHE, LX)), s([ulp], 'rpne0d', '( %s x. %s ) =/= 0' % (PHE, LX))], 'divcan2d', '( ( %s x. %s ) x. %s ) = %s' % (PHE, LX, WT_, D_))
    e_3 = s([e_2, e_1], 'oveq12d', '( ( ( %s x. %s ) x. %s ) x. ( Q x. ( 1 / Q ) ) ) = ( %s x. 1 )' % (PHE, LX, WT_, D_))
    ident = lin.lineq(w, A, '( ( %s x. %s ) x. %s )' % (G1, G2, K), '( ( ; ; 3 0 3 / ; ; 1 0 0 ) x. %s )' % D_, hyps=[e_3],
                      leaves={PHE: ef['%s e. RR' % PHE], 'Q': qr, LX: lxr, WT_: wtr, '( 1 / Q )': iqrp, 'E': er, X1: x1r}, products=True)
    # 3 Y <_ ( 303 / 100 ) D <_ ( PHEQ LQ ) K
    y3 = lin.linarith(w, A, [ysl], '( 3 x. %s ) <_ ( ( ; ; 3 0 3 / ; ; 1 0 0 ) x. %s )' % (Y_, D_), leaves={Y_: yr, D_: dr}, atoms=[Y_, D_], fast=False)
    y4 = s([y3, s([ident], 'eqcomd', '( ( ; ; 3 0 3 / ; ; 1 0 0 ) x. %s ) = ( ( %s x. %s ) x. %s )' % (D_, G1, G2, K))], 'breqtrd', '( 3 x. %s ) <_ ( ( %s x. %s ) x. %s )' % (Y_, G1, G2, K))
    y5 = s([s([lit(w, A, '3'), yr], 'remulcld', '( 3 x. %s ) e. RR' % Y_), s([s([g1r, g2r], 'remulcld', '( %s x. %s ) e. RR' % (G1, G2)), kr], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (G1, G2, K)), s([s([pheqr, lqr], 'remulcld', '( %s x. %s ) e. RR' % (PHEQ, LQ)), kr], 'remulcld', '( ( %s x. %s ) x. %s ) e. RR' % (PHEQ, LQ, K)), y4, p2], 'letrd', '( 3 x. %s ) <_ ( ( %s x. %s ) x. %s )' % (Y_, PHEQ, LQ, K))
    g2gt0 = s([s([s([num.rp(w, F79H)], 'a1i', '%s e. RR+' % F79H), xf['%s e. RR+' % LX]], 'rpmulcld', '%s e. RR+' % G2)], 'rpgt0d', '0 < %s' % G2)
    lqgt0 = lin.linarith(w, A, [hlogq, g2gt0], '0 < %s' % LQ, leaves={LQ: lqr, G2: g2r}, atoms=[LQ, G2])
    plrp = s([s([pheqn], 'nnrpd', '%s e. RR+' % PHEQ), s([lqr, lqgt0], 'elrpd', '%s e. RR+' % LQ)], 'rpmulcld', '( %s x. %s ) e. RR+' % (PHEQ, LQ))
    y6 = s([y5, s([s([lit(w, A, '3'), yr], 'remulcld', '( 3 x. %s ) e. RR' % Y_), kr, plrp], 'ledivmuld', '( %s <_ %s <-> ( 3 x. %s ) <_ ( ( %s x. %s ) x. %s ) )' % (BND_, K, Y_, PHEQ, LQ, K))], 'mpbird', '%s <_ %s' % (BND_, K))
    aqr = s([mpi(w, finrab(w, AQ_), 'hashcl', '( # ` %s ) e. NN0' % AQ_)], 'a1i', '( # ` %s ) e. NN0' % AQ_)
    aqr = s([aqr], 'nn0red', '( # ` %s ) e. RR' % AQ_)
    bndr = s([s([lit(w, A, '3'), yr], 'remulcld', '( 3 x. %s ) e. RR' % Y_), plrp], 'rerpdivcld', '%s e. RR' % BND_)
    w.qed([aqr, bndr, kr, btq, y6], 'letrd', S['bmpdlbt'])
    return go(w)


ALL = {'bmpdlx': gen_x, 'bmpdly': gen_y, 'bmpdlbt': gen_bt}


PFL = PF('L')


def gen_sum():
    w = W('bmpdlsum', 'The primes up to ` Y ` congruent to ` 1 ` mod ` E Q ` , summed over the primes ` Q ` dividing the sieve modulus ` L ` , number at most ` ( 303 / 800 ) W ` (Lean ` hsumbad ` ): ~ bmpdlbt at each ` Q ` and the hypothesis ` sum 1 / Q <_ 79 / 3200 ` .')
    A = '( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ %s )' % (XHYP, N100, X1, EHYP, THYP, BTBODY('T'), LHYP)
    HQ = 'A. v e. Prime ( v || L -> v <_ %s )' % XHH
    HQu = 'A. u e. Prime ( u || L -> u <_ %s )' % XHH
    # the v-free antecedent for the summation steps
    Ap = '( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( L e. NN /\\ %s ) )' % (XHYP, N100, X1, EHYP, THYP, BTBODY('T'), HQu)
    s = S_(w, Ap)
    u = unpack(w, Ap)
    xhyp = w.s([u['X e. NN0'], u['3 <_ X']], 'jca', '( %s -> %s )' % (Ap, XHYP))
    ehyp = w.s([u['E e. NN'], u['E <_ %s' % XBB]], 'jca', '( %s -> %s )' % (Ap, EHYP))
    h100 = u['%s <_ %s' % (N100, X1)]
    thyp = w.s([u['T e. RR'], u['T <_ %s' % X1]], 'jca', '( %s -> %s )' % (Ap, THYP))
    bt = u[BTBODY('T')]
    ln, hq = u['L e. NN'], u[HQu]
    xf = xfacts(w, Ap, xhyp); ef = efacts(w, Ap, ehyp)
    pff = s([ln, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PFL)
    AV = '( %s /\\ v e. %s )' % (Ap, PFL)
    sv = S_(w, AV)
    LV = lambda x_: lift(w, x_, AV)
    vin = sv([], 'simpr', 'v e. %s' % PFL)
    el = w.s([w.s([], 'breq1', '( u = v -> ( u || L <-> v || L ) )')], 'elrab', '( v e. %s <-> ( v e. Prime /\\ v || L ) )' % PFL)
    vp2 = sv([vin, el], 'sylib', '( v e. Prime /\\ v || L )')
    vp = sv([vp2], 'simpld', 'v e. Prime'); vl = sv([vp2], 'simprd', 'v || L')
    cgu, inst_u = wc(w, '( u || L -> u <_ %s )' % XHH, 'u', 'v')
    vle = sv([vl, sv([cgu, LV(hq), vp], 'rspcdva', inst_u)], 'mpd', 'v <_ %s' % XHH)
    AQv = AQ(Y_, 'E', 'v')
    K = '( %s x. %s )' % (F121279, WT_)
    btv = ap(w, AV, [LV(xhyp), LV(h100), LV(ehyp), LV(thyp), LV(bt), vp, vle], 'bmpdlbt', '( # ` %s ) <_ ( %s x. ( 1 / v ) )' % (AQv, K), sub={'Q': 'v'})
    aqr = sv([mpi(w, finrab(w, AQv), 'hashcl', '( # ` %s ) e. NN0' % AQv)], 'a1i', '( # ` %s ) e. NN0' % AQv)
    aqr = sv([aqr], 'nn0red', '( # ` %s ) e. RR' % AQv)
    ulp = s([ef['%s e. RR+' % PHE], xf['%s e. RR+' % LX]], 'rpmulcld', '( %s x. %s ) e. RR+' % (PHE, LX))
    drp = s([ef['E e. RR+'], xf['%s e. RR+' % X1]], 'rpmulcld', '%s e. RR+' % D_)
    wtrp = s([drp, ulp], 'rpdivcld', '%s e. RR+' % WT_)
    wtr = s([wtrp], 'rpred', '%s e. RR' % WT_); wtge0 = s([wtrp], 'rpge0d', '0 <_ %s' % WT_)
    kr = s([lit(w, Ap, F121279), wtr], 'remulcld', '%s e. RR' % K)
    kge0 = s([lit(w, Ap, F121279), wtr, s([num.fact(w, F121279, 'ge0')], 'a1i', '0 <_ %s' % F121279), wtge0], 'mulge0d', '0 <_ %s' % K)
    vrp = sv([sv([vp, w.inst('prmnn')], 'syl', 'v e. NN')], 'nnrpd', 'v e. RR+')
    ivr = sv([vrp], 'rprecred', '( 1 / v ) e. RR')
    tr = sv([LV(kr), ivr], 'remulcld', '( %s x. ( 1 / v ) ) e. RR' % K)
    f1 = s([pff, aqr, tr, btv], 'fsumle', 'sum_ v e. %s ( # ` %s ) <_ sum_ v e. %s ( %s x. ( 1 / v ) )' % (PFL, AQv, PFL, K))
    f2 = s([pff, s([kr], 'recnd', '%s e. CC' % K), sv([ivr], 'recnd', '( 1 / v ) e. CC')], 'fsummulc2', '( %s x. sum_ v e. %s ( 1 / v ) ) = sum_ v e. %s ( %s x. ( 1 / v ) )' % (K, PFL, PFL, K))
    SUMV = 'sum_ v e. %s ( 1 / v )' % PFL
    sumr = s([pff, ivr], 'fsumrecl', '%s e. RR' % SUMV)
    SL = 'sum_ v e. %s ( # ` %s )' % (PFL, AQv)
    slr = s([pff, aqr], 'fsumrecl', '%s e. RR' % SL)
    g1 = s([f1, s([f2], 'eqcomd', 'sum_ v e. %s ( %s x. ( 1 / v ) ) = ( %s x. %s )' % (PFL, K, K, SUMV))], 'breqtrd', '%s <_ ( %s x. %s )' % (SL, K, SUMV))
    ksr = s([kr, sumr], 'remulcld', '( %s x. %s ) e. RR' % (K, SUMV))
    core = s([g1, ksr, slr, sumr, kr, kge0, wtr], '3jca', 'x') if False else None
    pack = s([s([g1, ksr, slr], '3jca', '( %s <_ ( %s x. %s ) /\\ ( %s x. %s ) e. RR /\\ %s e. RR )' % (SL, K, SUMV, K, SUMV, SL)), s([sumr, kr, kge0], '3jca', '( %s e. RR /\\ %s e. RR /\\ 0 <_ %s )' % (SUMV, K, K)), wtr], '3jca',
             '( ( %s <_ ( %s x. %s ) /\\ ( %s x. %s ) e. RR /\\ %s e. RR ) /\\ ( %s e. RR /\\ %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR )' % (SL, K, SUMV, K, SUMV, SL, SUMV, K, K, WT_))
    PACK = strip_ante(formula_of(w, pack), Ap)
    # ---- back under A
    sa = S_(w, A)
    ua = unpack(w, A)
    cgv, _ = wc(w, '( v || L -> v <_ %s )' % XHH, 'v', 'u')
    hqu = sa([ua[HQ], w.s([cgv], 'cbvralvw', '( %s <-> %s )' % (HQ, HQu))], 'sylib', HQu)
    g1a = sa([ua['X e. NN0'], ua['3 <_ X']], 'jca', XHYP)
    g1b = sa([ua['%s <_ %s' % (N100, X1)], sa([ua['E e. NN'], ua['E <_ %s' % XBB]], 'jca', EHYP)], 'jca', '( %s <_ %s /\\ %s )' % (N100, X1, EHYP))
    g2 = sa([sa([ua['T e. RR'], ua['T <_ %s' % X1]], 'jca', THYP), ua[BTBODY('T')]], 'jca', '( %s /\\ %s )' % (THYP, BTBODY('T')))
    g3 = sa([ua['L e. NN'], hqu], 'jca', '( L e. NN /\\ %s )' % HQu)
    apst = sa([sa([g1a, g1b], 'jca', '( %s /\\ ( %s <_ %s /\\ %s ) )' % (XHYP, N100, X1, EHYP)), g2, g3], '3jca', Ap)
    pk = sa([apst, w.s([pack], 'x', 'x') if False else pack], 'syl', PACK) if False else sa([apst, pack], 'syl', PACK)
    pu = unpack_step(w, A, pk, PACK)
    hs = ua['sum_ v e. %s ( 1 / v ) <_ %s' % (PFL, F793200)]
    f3 = sa([pu['%s e. RR' % SUMV], lit(w, A, F793200), pu['%s e. RR' % K], pu['0 <_ %s' % K], hs], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (K, SUMV, K, F793200))
    f4 = lin.lineq(w, A, '( %s x. %s )' % (K, F793200), '( %s x. %s )' % (F303800, WT_), leaves={WT_: pu['%s e. RR' % WT_]})
    rhs = sa([lit(w, A, F303800), pu['%s e. RR' % WT_]], 'remulcld', '( %s x. %s ) e. RR' % (F303800, WT_))
    g2_ = sa([f3, f4], 'breqtrd', '( %s x. %s ) <_ ( %s x. %s )' % (K, SUMV, F303800, WT_))
    w.qed([pu['%s e. RR' % SL], pu['( %s x. %s ) e. RR' % (K, SUMV)], rhs, pu['%s <_ ( %s x. %s )' % (SL, K, SUMV)], g2_], 'letrd', S['bmpdlsum'])
    return go(w)


A_ = ASET(Y_, 'E')
A0_ = A0(Y_, 'E', 'L')
COP = lambda h: '( ( ( %s - 1 ) / E ) gcd L ) = 1' % h


def ind_facts(w, ante, cond):
    """( ante -> if ( cond , 1 , 0 ) e. RR ), ( ante -> 0 <_ if ( cond , 1 , 0 ) ) (closed facts lifted)"""
    E = 'if ( %s , 1 , 0 )' % cond
    one = w.s([], '1re', '1 e. RR'); zero = w.s([], '0re', '0 e. RR')
    r = w.s([w.s([one, zero, w.inst('ifcl')], 'mp2an', '%s e. RR' % E)], 'a1i', '( %s -> %s e. RR )' % (ante, E))
    g1 = w.s([], '0le1', '0 <_ 1'); g0 = w.s([], '0le0', '0 <_ 0')
    # 0 <_ if : by cases, closed
    c1 = w.s([w.s([g1], 'a1i', '( %s -> 0 <_ 1 )' % cond), w.s([], 'iftrue', '( %s -> %s = 1 )' % (cond, E))], 'breqtrrd', '( %s -> 0 <_ %s )' % (cond, E))
    c0 = w.s([w.s([g0], 'a1i', '( -. %s -> 0 <_ 0 )' % cond), w.s([], 'iffalse', '( -. %s -> %s = 0 )' % (cond, E))], 'breqtrrd', '( -. %s -> 0 <_ %s )' % (cond, E))
    both = w.s([c1, c0], 'pm2.61i', '0 <_ %s' % E)
    g = w.s([both], 'a1i', '( %s -> 0 <_ %s )' % (ante, E))
    return r, g


def gen_split():
    w = W('bmpdlsplit', 'The primes ` p <_ Y ` with ` p = 1 ` mod ` E ` are the good ones (` ( p - 1 ) / E ` coprime to ` L ` ) together with those counted by some ` E Q ` , ` Q ` a prime factor of ` L ` (Lean ` hkey ` , ` hsplit ` ): the bad ones are counted by the indicator sums (~ sumhash , ~ fsumcom , ~ fsumge1 , ~ prmdvdsncoprmbd ).')
    A = '( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ L e. NN )' % (XHYP, N100, X1, EHYP)
    s = S_(w, A)
    xhyp = w.s([], 'simpll', '( %s -> %s )' % (A, XHYP))
    g2 = w.s([], 'simplr', '( %s -> ( %s <_ %s /\\ %s ) )' % (A, N100, X1, EHYP))
    h100 = s([g2], 'simpld', '%s <_ %s' % (N100, X1)); ehyp = s([g2], 'simprd', EHYP)
    ln = s([], 'simpr', 'L e. NN')
    xf = xfacts(w, A, xhyp); ef = efacts(w, A, ehyp); yf = yfacts(w, A, xhyp, h100, ehyp)
    A1 = '{ h e. %s | -. %s }' % (A_, COP('h'))
    FZ = '( 0 ... %s )' % Y_
    afin = s([finrab(w, A_)], 'a1i', '%s e. Fin' % A_)
    a0ss = w.s([], 'ssrab2', '%s C_ %s' % (A0_, A_))
    d1 = s([afin, s([a0ss], 'a1i', '%s C_ %s' % (A0_, A_)), w.inst('hashssdif')], 'syl2anc', '( # ` ( %s \\ %s ) ) = ( ( # ` %s ) - ( # ` %s ) )' % (A_, A0_, A_, A0_))
    nr = w.s([], 'notrab', '( %s \\ %s ) = %s' % (A_, A0_, A1))
    d2 = s([s([nr], 'a1i', '( %s \\ %s ) = %s' % (A_, A0_, A1))], 'fveq2d', '( # ` ( %s \\ %s ) ) = ( # ` %s )' % (A_, A0_, A1))
    d3 = s([d2, d1], 'eqtr3d', '( # ` %s ) = ( ( # ` %s ) - ( # ` %s ) )' % (A1, A_, A0_))
    # ---- pointwise: for p e. FZ, if ( p e. A1 , 1 , 0 ) <_ sum_ v e. PF if ( p e. AQ ( v ) , 1 , 0 )
    AQv = AQ(Y_, 'E', 'v')
    IND1 = 'if ( p e. %s , 1 , 0 )' % A1
    INDv = 'if ( p e. %s , 1 , 0 )' % AQv
    SUMI = 'sum_ v e. %s %s' % (PFL, INDv)
    pff = s([ln, w.inst('prmdvdsfi')], 'syl', '%s e. Fin' % PFL)
    AF = '( %s /\\ p e. %s )' % (A, FZ)
    sf = S_(w, AF)
    LF = lambda x_: lift(w, x_, AF)
    AP = '( %s /\\ p e. %s )' % (AF, A1)
    sp = S_(w, AP)
    LP = lambda x_: lift(w, x_, AP)
    pin = sp([], 'simpr', 'p e. %s' % A1)
    c1, ncop = wc(w, '-. %s' % COP('h'), 'h', 'p')
    el1 = w.s([c1], 'elrab', '( p e. %s <-> ( p e. %s /\\ %s ) )' % (A1, A_, ncop))
    pa2 = sp([pin, el1], 'sylib', '( p e. %s /\\ %s )' % (A_, ncop))
    pa = sp([pa2], 'simpld', 'p e. %s' % A_); pnc = sp([pa2], 'simprd', ncop)
    c2, cond = wc(w, '( n e. Prime /\\ ( n mod E ) = ( 1 mod E ) )', 'n', 'p')
    el2 = w.s([c2], 'elrab', '( p e. %s <-> ( p e. %s /\\ %s ) )' % (A_, FZ, cond))
    pa3 = sp([pa, el2], 'sylib', '( p e. %s /\\ %s )' % (FZ, cond))
    pfz = sp([pa3], 'simpld', 'p e. %s' % FZ)
    pcond = sp([pa3], 'simprd', cond)
    pp = sp([pcond], 'simpld', 'p e. Prime'); pmod = sp([pcond], 'simprd', '( p mod E ) = ( 1 mod E )')
    pn = sp([pp, w.inst('prmnn')], 'syl', 'p e. NN'); pz = sp([pn], 'nnzd', 'p e. ZZ')
    puz = sp([pp, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )')
    pm1n = sp([puz, w.inst('uz2m1nn')], 'syl', '( p - 1 ) e. NN'); pm1z = sp([pm1n], 'nnzd', '( p - 1 ) e. ZZ')
    edv = sp([pmod, sp([LP(ef['E e. NN']), pz, sp([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), w.inst('moddvds')], 'syl3anc', '( ( p mod E ) = ( 1 mod E ) <-> E || ( p - 1 ) )')], 'mpbid', 'E || ( p - 1 )')
    KP = '( ( p - 1 ) / E )'
    kn = sp([edv, sp([pm1n, LP(ef['E e. NN']), w.inst('nndivdvds')], 'syl2anc', '( E || ( p - 1 ) <-> %s e. NN )' % KP)], 'mpbid', '%s e. NN' % KP)
    kz = sp([kn], 'nnzd', '%s e. ZZ' % KP)
    gne = sp([pnc], 'neqned', '( %s gcd L ) =/= 1' % KP)
    bd = sp([kn, LP(ln)], 'prmdvdsncoprmbd', '( E. q e. Prime ( q || %s /\\ q || L ) <-> ( %s gcd L ) =/= 1 )' % (KP, KP))
    exq = sp([gne, bd], 'mpbird', 'E. q e. Prime ( q || %s /\\ q || L )' % KP)
    # under a fixed q
    AQC = '( %s /\\ ( q e. Prime /\\ ( q || %s /\\ q || L ) ) )' % (AP, KP)
    sq = S_(w, AQC)
    LQ_ = lambda x_: lift(w, x_, AQC)
    qp = sq([], 'simprl', 'q e. Prime'); qk = sq([sq([], 'simprr', '( q || %s /\\ q || L )' % KP)], 'simpld', 'q || %s' % KP); ql = sq([sq([], 'simprr', '( q || %s /\\ q || L )' % KP)], 'simprd', 'q || L')
    qn = sq([qp, w.inst('prmnn')], 'syl', 'q e. NN'); qz = sq([qn], 'nnzd', 'q e. ZZ')
    elq = w.s([w.s([], 'breq1', '( u = q -> ( u || L <-> q || L ) )')], 'elrab', '( q e. %s <-> ( q e. Prime /\\ q || L ) )' % PFL)
    qpf = sq([sq([qp, ql], 'jca', '( q e. Prime /\\ q || L )'), elq], 'sylibr', 'q e. %s' % PFL)
    EQ = '( E x. q )'
    eqn = sq([LQ_(ef['E e. NN']), qn], 'nnmulcld', '%s e. NN' % EQ)
    m1 = sq([qk, sq([qz, LQ_(kz), LQ_(ef['E e. ZZ']), w.inst('dvdscmul')], 'syl3anc', '( q || %s -> %s || ( E x. %s ) )' % (KP, EQ, KP))], 'mpd', '%s || ( E x. %s )' % (EQ, KP))
    m2 = sq([LQ_(sp([pm1z], 'zcnd', '( p - 1 ) e. CC')), LQ_(ef['E e. CC']), LQ_(ef['E =/= 0'])], 'divcan2d', '( E x. %s ) = ( p - 1 )' % KP)
    m3 = sq([m1, m2], 'breqtrd', '%s || ( p - 1 )' % EQ)
    m4 = sq([m3, sq([eqn, LQ_(pz), sq([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), w.inst('moddvds')], 'syl3anc', '( ( p mod %s ) = ( 1 mod %s ) <-> %s || ( p - 1 ) )' % (EQ, EQ, EQ))], 'mpbird', '( p mod %s ) = ( 1 mod %s )' % (EQ, EQ))
    AQq = AQ(Y_, 'E', 'q')
    c3, condq = wc(w, '( i e. Prime /\\ ( i mod %s ) = ( 1 mod %s ) )' % (EQ, EQ), 'i', 'p')
    elaq = w.s([c3], 'elrab', '( p e. %s <-> ( p e. %s /\\ %s ) )' % (AQq, FZ, condq))
    paq = sq([sq([LQ_(pfz), sq([LQ_(pp), m4], 'jca', condq)], 'jca', '( p e. %s /\\ %s )' % (FZ, condq)), elaq], 'sylibr', 'p e. %s' % AQq)
    # 1 <_ sum_ v e. PF if ( p e. AQ ( v ) , 1 , 0 ) by fsumge1 at M := q
    INDq = 'if ( p e. %s , 1 , 0 )' % AQq
    AQV = '( %s /\\ v e. %s )' % (AQC, PFL)
    ir, ig = ind_facts(w, AQV, 'p e. %s' % AQv)
    cq, _ = cc(w, INDv, 'v', 'q')
    ge1 = sq([LQ_(pff), ir, ig, cq, qpf], 'fsumge1', '%s <_ %s' % (INDq, SUMI))
    it = sq([paq, w.s([], 'iftrue', '( p e. %s -> %s = 1 )' % (AQq, INDq))], 'syl', '%s = 1' % INDq)
    ge1b = sq([it, ge1], 'eqbrtrrd', '1 <_ %s' % SUMI)
    ge1c = w.s([exq, ge1b], 'rexlimddv', '( %s -> 1 <_ %s )' % (AP, SUMI))
    it1 = sp([pin, w.s([], 'iftrue', '( p e. %s -> %s = 1 )' % (A1, IND1))], 'syl', '%s = 1' % IND1)
    caseA = sp([it1, ge1c], 'eqbrtrd', '%s <_ %s' % (IND1, SUMI))
    AN = '( %s /\\ -. p e. %s )' % (AF, A1)
    sn = S_(w, AN)
    AFV = '( %s /\\ v e. %s )' % (AN, PFL)
    ir2, ig2 = ind_facts(w, AFV, 'p e. %s' % AQv)
    ge0 = sn([lift(w, pff, AN), ir2, ig2], 'fsumge0', '0 <_ %s' % SUMI)
    if0 = sn([sn([], 'simpr', '-. p e. %s' % A1), w.s([], 'iffalse', '( -. p e. %s -> %s = 0 )' % (A1, IND1))], 'syl', '%s = 0' % IND1)
    caseB = sn([if0, ge0], 'eqbrtrd', '%s <_ %s' % (IND1, SUMI))
    pw = w.s([caseA, caseB], 'pm2.61dan', '( %s -> %s <_ %s )' % (AF, IND1, SUMI))
    # ---- the sums
    fzfin = w.s([w.s([], 'fzfi', '%s e. Fin' % FZ)], 'a1i', '( %s -> %s e. Fin )' % (A, FZ))
    i1r, i1g = ind_facts(w, AF, 'p e. %s' % A1)
    AFV2 = '( %s /\\ v e. %s )' % (AF, PFL)
    ivr, ivg = ind_facts(w, AFV2, 'p e. %s' % AQv)
    sumr = sf([LF(pff), ivr], 'fsumrecl', '%s e. RR' % SUMI)
    f1 = s([fzfin, i1r, sumr, pw], 'fsumle', 'sum_ p e. %s %s <_ sum_ p e. %s %s' % (FZ, IND1, FZ, SUMI))
    a1ss = w.s([w.s([], 'ssrab2', '%s C_ %s' % (A1, A_)), w.s([], 'ssrab2', '%s C_ %s' % (A_, FZ))], 'sstri', '%s C_ %s' % (A1, FZ))
    e1 = s([fzfin, s([a1ss], 'a1i', '%s C_ %s' % (A1, FZ)), w.inst('sumhash')], 'syl2anc', 'sum_ p e. %s %s = ( # ` %s )' % (FZ, IND1, A1))
    APV = '( %s /\\ ( p e. %s /\\ v e. %s ) )' % (A, FZ, PFL)
    ivc = w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([], '0re', '0 e. RR'), w.inst('ifcl')], 'mp2an', '%s e. RR' % INDv)], 'a1i', '( %s -> %s e. RR )' % (APV, INDv))
    ivc = w.s([ivc], 'recnd', '( %s -> %s e. CC )' % (APV, INDv))
    e2 = s([fzfin, pff, ivc], 'fsumcom', 'sum_ p e. %s %s = sum_ v e. %s sum_ p e. %s %s' % (FZ, SUMI, PFL, FZ, INDv))
    AV = '( %s /\\ v e. %s )' % (A, PFL)
    aqss = w.s([], 'ssrab2', '%s C_ %s' % (AQv, FZ))
    e3 = w.s([lift(w, fzfin, AV), w.s([aqss], 'a1i', '( %s -> %s C_ %s )' % (AV, AQv, FZ)), w.inst('sumhash')], 'syl2anc', '( %s -> sum_ p e. %s %s = ( # ` %s ) )' % (AV, FZ, INDv, AQv))
    e4 = w.s([e3], 'sumeq2dv', '( %s -> sum_ v e. %s sum_ p e. %s %s = sum_ v e. %s ( # ` %s ) )' % (A, PFL, FZ, INDv, PFL, AQv))
    SL = 'sum_ v e. %s ( # ` %s )' % (PFL, AQv)
    h1 = s([s([e1], 'eqcomd', '( # ` %s ) = sum_ p e. %s %s' % (A1, FZ, IND1)), s([f1, s([e2, e4], 'eqtrd', 'sum_ p e. %s %s = %s' % (FZ, SUMI, SL))], 'breqtrd', 'sum_ p e. %s %s <_ %s' % (FZ, IND1, SL))], 'eqbrtrd', '( # ` %s ) <_ %s' % (A1, SL))
    # reals and the arithmetic
    ar = s([mpi(w, finrab(w, A_), 'hashcl', '( # ` %s ) e. NN0' % A_)], 'a1i', '( # ` %s ) e. NN0' % A_); ar = s([ar], 'nn0red', '( # ` %s ) e. RR' % A_)
    a0r = s([mpi(w, finrab(w, A0_), 'hashcl', '( # ` %s ) e. NN0' % A0_)], 'a1i', '( # ` %s ) e. NN0' % A0_); a0r = s([a0r], 'nn0red', '( # ` %s ) e. RR' % A0_)
    a1r = s([mpi(w, finrab(w, A1), 'hashcl', '( # ` %s ) e. NN0' % A1)], 'a1i', '( # ` %s ) e. NN0' % A1); a1r = s([a1r], 'nn0red', '( # ` %s ) e. RR' % A1)
    aqr = w.s([w.s([mpi(w, finrab(w, AQv), 'hashcl', '( # ` %s ) e. NN0' % AQv)], 'a1i', '( %s -> ( # ` %s ) e. NN0 )' % (AV, AQv))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (AV, AQv))
    slr = s([pff, aqr], 'fsumrecl', '%s e. RR' % SL)
    g = lin.linarith(w, A, [d3, h1], '( # ` %s ) <_ ( ( # ` %s ) + %s )' % (A_, A0_, SL),
                     leaves={'( # ` %s )' % A_: ar, '( # ` %s )' % A0_: a0r, '( # ` %s )' % A1: a1r, SL: slr}, atoms=[SL], fast=False, name='qed')
    return go(w)


ALL.update({'bmpdlsum': gen_sum, 'bmpdlsplit': gen_split})



KF_ = KF('X', 'L')
SK_ = SK('X', 'L', 'E')
K0 = '( |_ ` %s )' % X1


def gen_inj():
    w = W('bmpdlinj', 'The good primes ` p <_ Y ` , ` p = 1 ` mod ` E ` with ` ( p - 1 ) / E ` coprime to ` L ` , are images of admissible shifts ` k <_ floor ( X ^ ( 79 / 100 ) ) ` coprime to ` L ` with ` E k + 1 ` a prime up to ` X ` (Lean ` hinj ` ): ` p = E k + 1 ` with ` k = ( p - 1 ) / E ` , counted through the image (~ bmhashim ).')
    A = '( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ L e. NN )' % (XHYP, N100, X1, EHYP)
    s = S_(w, A)
    xhyp = w.s([], 'simpll', '( %s -> %s )' % (A, XHYP))
    g2 = w.s([], 'simplr', '( %s -> ( %s <_ %s /\\ %s ) )' % (A, N100, X1, EHYP))
    h100 = s([g2], 'simpld', '%s <_ %s' % (N100, X1)); ehyp = s([g2], 'simprd', EHYP)
    ln = s([], 'simpr', 'L e. NN')
    xf = xfacts(w, A, xhyp); ef = efacts(w, A, ehyp); yf = yfacts(w, A, xhyp, h100, ehyp)
    FZ = '( 0 ... %s )' % Y_
    M = '( w e. NN0 |-> ( ( E x. w ) + 1 ) )'; IM = '( %s " %s )' % (M, SK_)
    m1 = w.s([w.s([], 'ovex', '( ( E x. w ) + 1 ) e. _V')], 'a1i', '( w e. NN0 -> ( ( E x. w ) + 1 ) e. _V )')
    m2 = w.s([m1], 'rgen', 'A. w e. NN0 ( ( E x. w ) + 1 ) e. _V')
    m3 = w.s([m2, w.s([w.s([], 'eqid', '%s = %s' % (M, M))], 'fnmpt', '( A. w e. NN0 ( ( E x. w ) + 1 ) e. _V -> %s Fn NN0 )' % M)], 'ax-mp', '%s Fn NN0' % M)
    mfn = s([m3], 'a1i', '%s Fn NN0' % M)
    mfun = s([mfn], 'fnfund', 'Fun %s' % M)
    sk1 = w.s([], 'ssrab2', '%s C_ %s' % (SK_, KF_)); sk2 = w.s([], 'ssrab2', '%s C_ ( 1 ... %s )' % (KF_, K0))
    sk3 = w.s([w.s([sk2, w.s([], 'fz1ssnn', '( 1 ... %s ) C_ NN' % K0)], 'sstri', '%s C_ NN' % KF_), w.s([], 'nnssnn0', 'NN C_ NN0')], 'sstri', '%s C_ NN0' % KF_)
    sk4 = w.s([sk1, sk3], 'sstri', '%s C_ NN0' % SK_)
    sknn0 = s([sk4], 'a1i', '%s C_ NN0' % SK_)
    skfin = s([finrab(w, SK_)], 'a1i', '%s e. Fin' % SK_)
    imfin = s([mfun, skfin, w.inst('imafi')], 'syl2anc', '%s e. Fin' % IM)
    # A0 C_ IM
    AP = '( %s /\\ p e. %s )' % (A, A0_)
    sp = S_(w, AP)
    LP = lambda x_: lift(w, x_, AP)
    pin = sp([], 'simpr', 'p e. %s' % A0_)
    c1, cop = wc(w, COP('h'), 'h', 'p')
    el1 = w.s([c1], 'elrab', '( p e. %s <-> ( p e. %s /\\ %s ) )' % (A0_, A_, cop))
    pa2 = sp([pin, el1], 'sylib', '( p e. %s /\\ %s )' % (A_, cop))
    pa = sp([pa2], 'simpld', 'p e. %s' % A_); pcop = sp([pa2], 'simprd', cop)
    c2, cond = wc(w, '( n e. Prime /\\ ( n mod E ) = ( 1 mod E ) )', 'n', 'p')
    el2 = w.s([c2], 'elrab', '( p e. %s <-> ( p e. %s /\\ %s ) )' % (A_, FZ, cond))
    pa3 = sp([pa, el2], 'sylib', '( p e. %s /\\ %s )' % (FZ, cond))
    pfz = sp([pa3], 'simpld', 'p e. %s' % FZ)
    pcond = sp([pa3], 'simprd', cond)
    pp = sp([pcond], 'simpld', 'p e. Prime'); pmod = sp([pcond], 'simprd', '( p mod E ) = ( 1 mod E )')
    pn = sp([pp, w.inst('prmnn')], 'syl', 'p e. NN'); pz = sp([pn], 'nnzd', 'p e. ZZ'); pr = sp([pn], 'nnred', 'p e. RR'); pc = sp([pn], 'nncnd', 'p e. CC')
    puz = sp([pp, w.inst('prmuz2')], 'syl', 'p e. ( ZZ>= ` 2 )')
    pm1n = sp([puz, w.inst('uz2m1nn')], 'syl', '( p - 1 ) e. NN'); pm1r = sp([pm1n], 'nnred', '( p - 1 ) e. RR'); pm1c = sp([pm1n], 'nncnd', '( p - 1 ) e. CC')
    edv = sp([pmod, sp([LP(ef['E e. NN']), pz, sp([w.s([], '1z', '1 e. ZZ')], 'a1i', '1 e. ZZ'), w.inst('moddvds')], 'syl3anc', '( ( p mod E ) = ( 1 mod E ) <-> E || ( p - 1 ) )')], 'mpbid', 'E || ( p - 1 )')
    KP = '( ( p - 1 ) / E )'
    kn = sp([edv, sp([pm1n, LP(ef['E e. NN']), w.inst('nndivdvds')], 'syl2anc', '( E || ( p - 1 ) <-> %s e. NN )' % KP)], 'mpbid', '%s e. NN' % KP)
    kr = sp([kn], 'nnred', '%s e. RR' % KP); kz = sp([kn], 'nnzd', '%s e. ZZ' % KP)
    ply = sp([pfz, w.inst('elfzle2')], 'syl', 'p <_ %s' % Y_)
    yub = LP(yf['%s < ( %s + 1 )' % (Y_, D_)])
    dr = LP(s([ef['E e. RR'], xf['%s e. RR' % X1]], 'remulcld', '%s e. RR' % D_))
    pm1lt = lin.linarith(w, AP, [ply, yub], '( p - 1 ) < %s' % D_, leaves={'p': pr, Y_: LP(yf['%s e. RR' % Y_]), D_: dr}, atoms=[Y_, D_], fast=False)
    klt = sp([pm1lt, sp([pm1r, LP(xf['%s e. RR' % X1]), LP(ef['E e. RR+'])], 'ltdivmuld', '( %s < %s <-> ( p - 1 ) < %s )' % (KP, X1, D_))], 'mpbird', '%s < %s' % (KP, X1))
    kle = sp([kr, LP(xf['%s e. RR' % X1]), klt], 'ltled', '%s <_ %s' % (KP, X1))
    k0z = LP(s([xf['%s e. RR' % X1]], 'flcld', '%s e. ZZ' % K0))
    kle0 = sp([kle, sp([LP(xf['%s e. RR' % X1]), kz, w.inst('flge')], 'syl2anc', '( %s <_ %s <-> %s <_ %s )' % (KP, X1, KP, K0))], 'mpbid', '%s <_ %s' % (KP, K0))
    kfz = sp([sp([kn, kle0], 'jca', '( %s e. NN /\\ %s <_ %s )' % (KP, KP, K0)), sp([k0z, w.inst('fznn')], 'syl', '( %s e. ( 1 ... %s ) <-> ( %s e. NN /\\ %s <_ %s ) )' % (KP, K0, KP, KP, K0))], 'mpbird', '%s e. ( 1 ... %s )' % (KP, K0))
    c3, gcdk = wc(w, '( z gcd L ) = 1', 'z', KP)
    elkf = w.s([c3], 'elrab', '( %s e. %s <-> ( %s e. ( 1 ... %s ) /\\ %s ) )' % (KP, KF_, KP, K0, gcdk))
    kkf = sp([sp([kfz, pcop], 'jca', '( %s e. ( 1 ... %s ) /\\ %s )' % (KP, K0, gcdk)), elkf], 'sylibr', '%s e. %s' % (KP, KF_))
    e1 = sp([pm1c, LP(ef['E e. CC']), LP(ef['E =/= 0'])], 'divcan2d', '( E x. %s ) = ( p - 1 )' % KP)
    e2 = sp([e1], 'oveq1d', '( ( E x. %s ) + 1 ) = ( ( p - 1 ) + 1 )' % KP)
    e3 = sp([pc, sp([w.s([], 'ax-1cn', '1 e. CC')], 'a1i', '1 e. CC')], 'npcand', '( ( p - 1 ) + 1 ) = p')
    ekp = sp([e2, e3], 'eqtrd', '( ( E x. %s ) + 1 ) = p' % KP)
    plx = sp([pr, LP(yf['%s e. RR' % Y_]), LP(xf['X e. RR']), ply, LP(yf['%s <_ X' % Y_])], 'letrd', 'p <_ X')
    ekx = sp([ekp, plx], 'eqbrtrd', '( ( E x. %s ) + 1 ) <_ X' % KP)
    ekpr = sp([ekp, pp], 'eqeltrd', '( ( E x. %s ) + 1 ) e. Prime' % KP)
    c4, condk = wc(w, PCOND('E', 'k', 'X'), 'k', KP)
    elsk = w.s([c4], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ %s ) )' % (KP, SK_, KP, KF_, condk))
    ksk = sp([sp([kkf, sp([ekx, ekpr], 'jca', condk)], 'jca', '( %s e. %s /\\ %s )' % (KP, KF_, condk)), elsk], 'sylibr', '%s e. %s' % (KP, SK_))
    fim = sp([LP(mfn), LP(sknn0), ksk, w.inst('fnfvima')], 'syl3anc', '( %s ` %s ) e. %s' % (M, KP, IM))
    mv, val = congr.mptval(w, AP, 'w', 'NN0', '( ( E x. w ) + 1 )', KP, sp([kn], 'nnnn0d', '%s e. NN0' % KP))
    assert val == '( ( E x. %s ) + 1 )' % KP, val
    mv2 = sp([mv, ekp], 'eqtrd', '( %s ` %s ) = p' % (M, KP))
    pim = sp([mv2, fim], 'eqeltrrd', 'p e. %s' % IM)
    ss = s([w.s([pim], 'ex', '( %s -> ( p e. %s -> p e. %s ) )' % (A, A0_, IM))], 'ssrdv', '%s C_ %s' % (A0_, IM))
    h1 = s([imfin, ss, w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` %s )' % (A0_, IM))
    h2 = s([mfn, skfin, sknn0, w.inst('bmhashim')], 'syl3anc', '( # ` %s ) <_ ( # ` %s )' % (IM, SK_))
    a0r = s([mpi(w, finrab(w, A0_), 'hashcl', '( # ` %s ) e. NN0' % A0_)], 'a1i', '( # ` %s ) e. NN0' % A0_); a0r = s([a0r], 'nn0red', '( # ` %s ) e. RR' % A0_)
    imr = s([s([imfin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % IM)], 'nn0red', '( # ` %s ) e. RR' % IM)
    skr = s([mpi(w, finrab(w, SK_), 'hashcl', '( # ` %s ) e. NN0' % SK_)], 'a1i', '( # ` %s ) e. NN0' % SK_); skr = s([skr], 'nn0red', '( # ` %s ) e. RR' % SK_)
    w.qed([a0r, imr, skr, h1, h2], 'letrd', S['bmpdlinj'])
    return go(w)


def gen_main():
    w = W('bmpdlmain', 'The main term of the per-divisor count (Lean ` hmain2 ` , AGP (4.2)): from the ` B ` -membership lower bound ` pi ( Y ) / ( 2 phi ( E ) ) <_ # A ` and the Chebyshev lower bound ` Y / ( ( 11 / 10 ) log Y ) <_ pi ( Y ) ` , ` ( 5 / 11 ) W <_ # A ` .')
    A = '( ( %s /\\ ( %s <_ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ %s )' % (XHYP, N100, X1, EHYP, UHYP, PIB('U'), LOWI('X', 'E'))
    s = S_(w, A)
    u = unpack(w, A)
    xhyp = w.s([u['X e. NN0'], u['3 <_ X']], 'jca', '( %s -> %s )' % (A, XHYP))
    ehyp = w.s([u['E e. NN'], u['E <_ %s' % XBB]], 'jca', '( %s -> %s )' % (A, EHYP))
    h100 = u['%s <_ %s' % (N100, X1)]
    ur, ule, pib, lowi = u['U e. RR'], u['U <_ %s' % X1], u[PIB('U')], u[LOWI('X', 'E')]
    xf = xfacts(w, A, xhyp); ef = efacts(w, A, ehyp); yf = yfacts(w, A, xhyp, h100, ehyp)
    yr, yn0 = yf['%s e. RR' % Y_], yf['%s e. NN0' % Y_]
    dr = s([ef['E e. RR'], xf['%s e. RR' % X1]], 'remulcld', '%s e. RR' % D_)
    x1le, ylb, ylx = yf['%s <_ %s' % (X1, D_)], yf['%s <_ %s' % (D_, Y_)], yf['%s <_ X' % Y_]
    uly = s([ur, xf['%s e. RR' % X1], yr, ule, s([xf['%s e. RR' % X1], dr, yr, x1le, ylb], 'letrd', '%s <_ %s' % (X1, Y_))], 'letrd', 'U <_ %s' % Y_)
    body = PIB('U')[len('A. y e. NN0 '):]
    c1, inst = wc(w, body, 'y', Y_)
    LY = '( log ` %s )' % Y_
    hpi = s([uly, s([c1, pib, yn0], 'rspcdva', inst)], 'mpd', '( %s / ( %s x. %s ) ) <_ ( ppi ` %s )' % (Y_, F1110, LY, Y_))
    # log Y, log X
    y100 = s([lit(w, A, N100), dr, yr, s([lit(w, A, N100), xf['%s e. RR' % X1], dr, h100, x1le], 'letrd', '%s <_ %s' % (N100, D_)), ylb], 'letrd', '%s <_ %s' % (N100, Y_))
    y1 = lin.linarith(w, A, [y100], '1 < %s' % Y_, leaves={Y_: yr}, atoms=[Y_])
    yrp = s([yr, lin.linarith(w, A, [y100], '0 < %s' % Y_, leaves={Y_: yr}, atoms=[Y_])], 'elrpd', '%s e. RR+' % Y_)
    lyrp = s([yr, y1], 'rplogcld', '%s e. RR+' % LY); lyr = s([lyrp], 'rpred', '%s e. RR' % LY)
    lyx = s([ylx, s([yrp, xf['X e. RR+']], 'logled', '( %s <_ X <-> %s <_ %s )' % (Y_, LY, LX))], 'mpbid', '%s <_ %s' % (LY, LX))
    # W <_ Y / ( phi E log Y )
    PL_Y = '( %s x. %s )' % (PHE, LY); PL_X = '( %s x. %s )' % (PHE, LX)
    plyrp = s([ef['%s e. RR+' % PHE], lyrp], 'rpmulcld', '%s e. RR+' % PL_Y)
    plxr = s([ef['%s e. RR' % PHE], xf['%s e. RR' % LX]], 'remulcld', '%s e. RR' % PL_X)
    plle = s([lyr, xf['%s e. RR' % LX], ef['%s e. RR' % PHE], ef['0 <_ %s' % PHE], lyx], 'lemul2ad', '%s <_ %s' % (PL_Y, PL_X))
    dge0 = s([ef['E e. RR'], xf['%s e. RR' % X1], ef['0 <_ E'], xf['0 <_ %s' % X1]], 'mulge0d', '0 <_ %s' % D_)
    hwle = s([dr, yr, plyrp, plxr, dge0, ylb, plle], 'lediv12ad', '%s <_ ( %s / %s )' % (WT_, Y_, PL_Y))
    YPL = '( %s / %s )' % (Y_, PL_Y)
    yplr = s([yr, plyrp], 'rerpdivcld', '%s e. RR' % YPL)
    wtr = s([dr, s([ef['%s e. RR+' % PHE], xf['%s e. RR+' % LX]], 'rpmulcld', '%s e. RR+' % PL_X)], 'rerpdivcld', '%s e. RR' % WT_)
    m1 = s([wtr, yplr, lit(w, A, F511), s([num.fact(w, F511, 'ge0')], 'a1i', '0 <_ %s' % F511), hwle], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (F511, WT_, F511, YPL))
    # the identity ( Y / ( ( 11 / 10 ) LY ) ) / ( 2 PHE ) = ( 5 / 11 ) ( Y / ( PHE LY ) )
    yc = s([yr], 'recnd', '%s e. CC' % Y_)
    B1 = '( %s x. %s )' % (F1110, LY); B2 = '( 2 x. %s )' % PHE
    b1rp = s([s([num.rp(w, F1110)], 'a1i', '%s e. RR+' % F1110), lyrp], 'rpmulcld', '%s e. RR+' % B1)
    b2rp = s([s([w.s([], '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), ef['%s e. RR+' % PHE]], 'rpmulcld', '%s e. RR+' % B2)
    i1 = s([yc, s([b1rp], 'rpcnd', '%s e. CC' % B1), s([b2rp], 'rpcnd', '%s e. CC' % B2), s([b1rp], 'rpne0d', '%s =/= 0' % B1), s([b2rp], 'rpne0d', '%s =/= 0' % B2)], 'divdiv1d', '( ( %s / %s ) / %s ) = ( %s / ( %s x. %s ) )' % (Y_, B1, B2, Y_, B1, B2))
    # ( Y / ( B1 x. B2 ) ) = ( ( F511 x. Y ) / PL_Y ) by cross multiplication
    BB = '( %s x. %s )' % (B1, B2)
    bbrp = s([b1rp, b2rp], 'rpmulcld', '%s e. RR+' % BB)
    FY = '( %s x. %s )' % (F511, Y_)
    fyc = s([s([num.cc(w, F511)], 'a1i', '%s e. CC' % F511), yc], 'mulcld', '%s e. CC' % FY)
    dm = s([yc, fyc, s([bbrp], 'rpcnd', '%s e. CC' % BB), s([plyrp], 'rpcnd', '%s e. CC' % PL_Y), s([bbrp], 'rpne0d', '%s =/= 0' % BB), s([plyrp], 'rpne0d', '%s =/= 0' % PL_Y)], 'divmuleqd', '( ( %s / %s ) = ( %s / %s ) <-> ( %s x. %s ) = ( %s x. %s ) )' % (Y_, BB, FY, PL_Y, Y_, PL_Y, FY, BB))
    poly = lin.lineq(w, A, '( %s x. %s )' % (Y_, PL_Y), '( %s x. %s )' % (FY, BB), leaves={Y_: yr, LY: lyr, PHE: ef['%s e. RR' % PHE]}, products=True)
    i3 = s([poly, dm], 'mpbird', '( %s / %s ) = ( %s / %s )' % (Y_, BB, FY, PL_Y))
    i7 = s([s([num.cc(w, F511)], 'a1i', '%s e. CC' % F511), yc, s([plyrp], 'rpcnd', '%s e. CC' % PL_Y), s([plyrp], 'rpne0d', '%s =/= 0' % PL_Y)], 'divassd', '( %s / %s ) = ( %s x. %s )' % (FY, PL_Y, F511, YPL))
    ident = s([s([i1, i3], 'eqtrd', '( ( %s / %s ) / %s ) = ( %s / %s )' % (Y_, B1, B2, FY, PL_Y)), i7], 'eqtrd', '( ( %s / %s ) / %s ) = ( %s x. %s )' % (Y_, B1, B2, F511, YPL))
    # chain
    LHS = '( %s / %s )' % (Y_, B1)
    lhsr = s([yr, b1rp], 'rerpdivcld', '%s e. RR' % LHS)
    ppir = s([yr, w.inst('ppicl')], 'syl', '( ppi ` %s ) e. NN0' % Y_); ppir = s([ppir], 'nn0red', '( ppi ` %s ) e. RR' % Y_)
    q1 = s([hpi, s([lhsr, ppir, b2rp], 'lediv1d', '( %s <_ ( ppi ` %s ) <-> ( %s / %s ) <_ ( ( ppi ` %s ) / %s ) )' % (LHS, Y_, LHS, B2, Y_, B2))], 'mpbid', '( %s / %s ) <_ ( ( ppi ` %s ) / %s )' % (LHS, B2, Y_, B2))
    q2 = s([s([ident], 'eqcomd', '( %s x. %s ) = ( %s / %s )' % (F511, YPL, LHS, B2)), q1], 'eqbrtrd', '( %s x. %s ) <_ ( ( ppi ` %s ) / %s )' % (F511, YPL, Y_, B2))
    ar = s([mpi(w, finrab(w, A_), 'hashcl', '( # ` %s ) e. NN0' % A_)], 'a1i', '( # ` %s ) e. NN0' % A_); ar = s([ar], 'nn0red', '( # ` %s ) e. RR' % A_)
    ppb2r = s([ppir, b2rp], 'rerpdivcld', '( ( ppi ` %s ) / %s ) e. RR' % (Y_, B2))
    q3 = s([s([lit(w, A, F511), yplr], 'remulcld', '( %s x. %s ) e. RR' % (F511, YPL)), ppb2r, ar, q2, lowi], 'letrd', '( %s x. %s ) <_ ( # ` %s )' % (F511, YPL, A_))
    w.qed([s([lit(w, A, F511), wtr], 'remulcld', '( %s x. %s ) e. RR' % (F511, WT_)), s([lit(w, A, F511), yplr], 'remulcld', '( %s x. %s ) e. RR' % (F511, YPL)), ar, m1, q3], 'letrd', S['bmpdlmain'])
    return go(w)


def gen_pdl():
    w = W('bmpdl', 'AGP p. 716, Lean ` per_divisor_lower ` : for a divisor ` E <_ X ^ ( 21 / 100 ) ` of the reduced modulus, at least ` X ^ ( 79 / 100 ) / ( 20 log X ) ` shifts ` k <_ X ^ ( 79 / 100 ) ` coprime to ` L ` have ` E k + 1 ` a prime up to ` X ` : the main term ~ bmpdlmain less the discarded primes ~ bmpdlsum , counted through ~ bmpdlsplit and ~ bmpdlinj .')
    A = '( ( %s /\\ %s /\\ ( %s <_ %s /\\ %s /\\ %s ) ) /\\ ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (XHYP, LHYP, N100, X1, THYP, UHYP, BTBODY('T'), PIB('U'), EHYP, LOWI('X', 'E'))
    s = S_(w, A)
    u = unpack(w, A)
    xhyp = w.s([u['X e. NN0'], u['3 <_ X']], 'jca', '( %s -> %s )' % (A, XHYP))
    ehyp = w.s([u['E e. NN'], u['E <_ %s' % XBB]], 'jca', '( %s -> %s )' % (A, EHYP))
    thyp = w.s([u['T e. RR'], u['T <_ %s' % X1]], 'jca', '( %s -> %s )' % (A, THYP))
    uhyp = w.s([u['U e. RR'], u['U <_ %s' % X1]], 'jca', '( %s -> %s )' % (A, UHYP))
    lhyp = w.s([u['L e. NN'], u['A. v e. Prime ( v || L -> v <_ %s )' % XHH], u['sum_ v e. %s ( 1 / v ) <_ %s' % (PFL, F793200)]], '3jca', '( %s -> %s )' % (A, LHYP))
    h100 = u['%s <_ %s' % (N100, X1)]
    ln = u['L e. NN']; bt = u[BTBODY('T')]; pib = u[PIB('U')]; lowi = u[LOWI('X', 'E')]
    xf = xfacts(w, A, xhyp); ef = efacts(w, A, ehyp)
    G1 = '( %s /\\ ( %s <_ %s /\\ %s ) )' % (XHYP, N100, X1, EHYP)
    g1 = s([xhyp, s([h100, ehyp], 'jca', '( %s <_ %s /\\ %s )' % (N100, X1, EHYP))], 'jca', G1)
    SL = 'sum_ v e. %s ( # ` %s )' % (PFL, AQ(Y_, 'E', 'v'))
    main = ap(w, A, [g1, uhyp, pib, lowi], 'bmpdlmain', '( %s x. %s ) <_ ( # ` %s )' % (F511, WT_, A_))
    sm = ap(w, A, [g1, thyp, bt, lhyp], 'bmpdlsum', '%s <_ ( %s x. %s )' % (SL, F303800, WT_))
    sp_ = ap(w, A, [g1, ln], 'bmpdlsplit', '( # ` %s ) <_ ( ( # ` %s ) + %s )' % (A_, A0_, SL))
    inj = ap(w, A, [g1, ln], 'bmpdlinj', '( # ` %s ) <_ ( # ` %s )' % (A0_, SK_))
    # X1 / LX <_ WT
    PL_X = '( %s x. %s )' % (PHE, LX); EL = '( E x. %s )' % LX
    plxrp = s([ef['%s e. RR+' % PHE], xf['%s e. RR+' % LX]], 'rpmulcld', '%s e. RR+' % PL_X)
    elrp = s([ef['E e. RR+'], xf['%s e. RR+' % LX]], 'rpmulcld', '%s e. RR+' % EL)
    phle = s([s([ef['E e. NN'], w.inst('phicl2')], 'syl', '%s e. ( 1 ... E )' % PHE), w.inst('elfzle2')], 'syl', '%s <_ E' % PHE)
    plle = s([ef['%s e. RR' % PHE], ef['E e. RR'], xf['%s e. RR' % LX], xf['0 <_ %s' % LX], phle], 'lemul1ad', '%s <_ %s' % (PL_X, EL))
    dge0 = s([ef['E e. RR'], xf['%s e. RR' % X1], ef['0 <_ E'], xf['0 <_ %s' % X1]], 'mulge0d', '0 <_ %s' % D_)
    dr = s([ef['E e. RR'], xf['%s e. RR' % X1]], 'remulcld', '%s e. RR' % D_)
    l2 = s([s([s([s([plxrp], 'rpred', '%s e. RR' % PL_X), s([plxrp], 'rpgt0d', '0 < %s' % PL_X)], 'jca', '( %s e. RR /\\ 0 < %s )' % (PL_X, PL_X)), s([s([elrp], 'rpred', '%s e. RR' % EL), s([elrp], 'rpgt0d', '0 < %s' % EL)], 'jca', '( %s e. RR /\\ 0 < %s )' % (EL, EL)), s([dr, dge0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (D_, D_))], '3jca', '( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (PL_X, PL_X, EL, EL, D_, D_)), plle], 'jca', '( ( ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ 0 < %s ) /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ %s <_ %s )' % (PL_X, PL_X, EL, EL, D_, D_, PL_X, EL))
    l3 = s([l2, w.inst('lediv2a')], 'syl', '( %s / %s ) <_ ( %s / %s )' % (D_, EL, D_, PL_X))
    l4 = s([xf['%s e. CC' % X1] if '%s e. CC' % X1 in xf else s([xf['%s e. RR' % X1]], 'recnd', '%s e. CC' % X1), s([xf['%s e. RR' % LX]], 'recnd', '%s e. CC' % LX), ef['E e. CC'], s([xf['%s e. RR+' % LX]], 'rpne0d', '%s =/= 0' % LX), ef['E =/= 0']], 'divcan5d', '( %s / %s ) = ( %s / %s )' % (D_, EL, X1, LX))
    hwge = s([l4, l3], 'eqbrtrrd', '( %s / %s ) <_ %s' % (X1, LX, WT_))
    XL = '( %s / %s )' % (X1, LX)
    xlr = s([xf['%s e. RR' % X1], xf['%s e. RR+' % LX]], 'rerpdivcld', '%s e. RR' % XL)
    wtr = s([dr, plxrp], 'rerpdivcld', '%s e. RR' % WT_)
    wtge0 = s([s([s([ef['E e. RR+'], xf['%s e. RR+' % X1]], 'rpmulcld', '%s e. RR+' % D_), plxrp], 'rpdivcld', '%s e. RR+' % WT_)], 'rpge0d', '0 <_ %s' % WT_)
    ar = s([mpi(w, finrab(w, A_), 'hashcl', '( # ` %s ) e. NN0' % A_)], 'a1i', '( # ` %s ) e. NN0' % A_); ar = s([ar], 'nn0red', '( # ` %s ) e. RR' % A_)
    a0r = s([mpi(w, finrab(w, A0_), 'hashcl', '( # ` %s ) e. NN0' % A0_)], 'a1i', '( # ` %s ) e. NN0' % A0_); a0r = s([a0r], 'nn0red', '( # ` %s ) e. RR' % A0_)
    skr = s([mpi(w, finrab(w, SK_), 'hashcl', '( # ` %s ) e. NN0' % SK_)], 'a1i', '( # ` %s ) e. NN0' % SK_); skr = s([skr], 'nn0red', '( # ` %s ) e. RR' % SK_)
    # SL e. RR from the v-free antecedent L e. NN
    AV = '( L e. NN /\\ v e. %s )' % PFL
    aqr = w.s([w.s([mpi(w, finrab(w, AQ(Y_, 'E', 'v')), 'hashcl', '( # ` %s ) e. NN0' % AQ(Y_, 'E', 'v'))], 'a1i', '( %s -> ( # ` %s ) e. NN0 )' % (AV, AQ(Y_, 'E', 'v')))], 'nn0red', '( %s -> ( # ` %s ) e. RR )' % (AV, AQ(Y_, 'E', 'v')))
    slr0 = w.s([w.s([w.s([], 'id', '( L e. NN -> L e. NN )'), w.inst('prmdvdsfi')], 'syl', '( L e. NN -> %s e. Fin )' % PFL), aqr], 'fsumrecl', '( L e. NN -> %s e. RR )' % SL)
    slr = s([ln, slr0], 'syl', '%s e. RR' % SL)
    lin.linarith(w, A, [hwge, main, sm, sp_, inj, wtge0], '%s <_ ( # ` %s )' % (PDLC('X'), SK_),
                 leaves={XL: xlr, WT_: wtr, '( # ` %s )' % A_: ar, '( # ` %s )' % A0_: a0r, '( # ` %s )' % SK_: skr, SL: slr},
                 atoms=[XL, WT_, SL, '( # ` %s )' % A_, '( # ` %s )' % A0_, '( # ` %s )' % SK_], fast=False, name='qed')
    return go(w)


ALL.update({'bmpdlinj': gen_inj, 'bmpdlmain': gen_main, 'bmpdl': gen_pdl})

if __name__ == '__main__':
    for n in (only or list(ALL)):
        ALL[n]()
