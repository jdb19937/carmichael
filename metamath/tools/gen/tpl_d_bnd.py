"""T-PL: the budget identities and bounds of TM/PrimTD.lean and TM/PrimList.lean
that Step4/Step5/Steps23/Overhead read directly (blueprint D7): ~ tplb34
(` B_three_add_four `), ~ tplb37 (` B_three_add_seven `), ~ tplb410
(` B_four_add_ten `), ~ tplbsuc (` B_succ_le `), ~ tplbscale (` B_scale `),
~ tpl2pow (` two_pow_mul_le `), ~ tplpowsuc (` lt_pow_succ `), ~ tplprodle
(` prodL_le_two_pow ` on A1b's ~ prodlspec )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tpllib import *
from cl import Closure
from lin import lineq, linarith
import num

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def tmbscale(w, ph, c, X, Y, K, K3, k3step):
    """( ph -> ( TMB ` X ) = ( K3 x. ( TMB ` Y ) ) ) given ( X + 2 ) = ( K x. ( Y + 2 ) ) linearly,
    k3step : ( K ^ 3 ) = K3 (closed), c a Closure knowing the atoms of X, Y"""
    xn = c.mem(X, 'NN0'); yn = c.mem(Y, 'NN0')
    C3 = lambda Z: '( ( %s + 2 ) ^ 3 )' % Z
    v1 = w.s([xn, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` %s ) = ( ; 6 4 x. %s ) )' % (ph, X, C3(X)))
    e1 = lineq(w, ph, '( %s + 2 )' % X, '( %s x. ( %s + 2 ) )' % (K, Y), closure=c)
    e2 = w.s([e1], 'oveq1d', '( %s -> %s = ( ( %s x. ( %s + 2 ) ) ^ 3 ) )' % (ph, C3(X), K, Y))
    kc = w.s([num.cc_nat(w, int(K))], 'a1i', '( %s -> %s e. CC )' % (ph, K))
    yc = c.mem('( %s + 2 )' % Y, 'CC')
    n3 = w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % ph)
    e3 = w.s([kc, yc, n3, w.inst('mulexp')], 'syl3anc', '( %s -> ( ( %s x. ( %s + 2 ) ) ^ 3 ) = ( ( %s ^ 3 ) x. %s ) )' % (ph, K, Y, K, C3(Y)))
    e4 = w.s([k3step], 'oveq1i', '( ( %s ^ 3 ) x. %s ) = ( %s x. %s )' % (K, C3(Y), K3, C3(Y)))
    e4a = w.s([e4], 'a1i', '( %s -> ( ( %s ^ 3 ) x. %s ) = ( %s x. %s ) )' % (ph, K, C3(Y), K3, C3(Y)))
    e5 = w.s([w.s([e2, e3], 'eqtrd', '( %s -> %s = ( ( %s ^ 3 ) x. %s ) )' % (ph, C3(X), K, C3(Y))), e4a], 'eqtrd',
             '( %s -> %s = ( %s x. %s ) )' % (ph, C3(X), K3, C3(Y)))
    e6 = w.s([e5], 'oveq2d', '( %s -> ( ; 6 4 x. %s ) = ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, C3(X), K3, C3(Y)))
    c64 = w.s([num.cc_nat(w, 64)], 'a1i', '( %s -> ; 6 4 e. CC )' % ph)
    ck3 = w.s([num.cc_nat(w, int(K3.replace(' ', '').replace(';', ''))) if ';' in K3 else num.cc_nat(w, int(K3))], 'a1i', '( %s -> %s e. CC )' % (ph, K3))
    c3y = c.mem(C3(Y), 'CC')
    e7 = w.s([c64, ck3, c3y, w.inst('mul12')], 'syl3anc', '( %s -> ( ; 6 4 x. ( %s x. %s ) ) = ( %s x. ( ; 6 4 x. %s ) ) )' % (ph, K3, C3(Y), K3, C3(Y)))
    v2 = w.s([yn, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` %s ) = ( ; 6 4 x. %s ) )' % (ph, Y, C3(Y)))
    v2c = w.s([v2], 'eqcomd', '( %s -> ( ; 6 4 x. %s ) = ( TMB ` %s ) )' % (ph, C3(Y), Y))
    e8 = w.s([v2c], 'oveq2d', '( %s -> ( %s x. ( ; 6 4 x. %s ) ) = ( %s x. ( TMB ` %s ) ) )' % (ph, K3, C3(Y), K3, Y))
    t1 = w.s([v1, e6], 'eqtrd', '( %s -> ( TMB ` %s ) = ( ; 6 4 x. ( %s x. %s ) ) )' % (ph, X, K3, C3(Y)))
    t2 = w.s([t1, e7], 'eqtrd', '( %s -> ( TMB ` %s ) = ( %s x. ( ; 6 4 x. %s ) ) )' % (ph, X, K3, C3(Y)))
    return w.s([t2, e8], 'eqtrd', '( %s -> ( TMB ` %s ) = ( %s x. ( TMB ` %s ) ) )' % (ph, X, K3, Y))


def cube4(w):
    """closed: ( 4 ^ 3 ) = ; 6 4"""
    a = w.s([], '2t2e4', '( 2 x. 2 ) = 4')
    b = w.s([a], 'eqcomi', '4 = ( 2 x. 2 )')
    c_ = w.s([b], 'oveq1i', '( 4 ^ 3 ) = ( ( 2 x. 2 ) ^ 3 )')
    c2 = w.s([], '2cn', '2 e. CC'); n3 = w.s([], '3nn0', '3 e. NN0')
    d = w.s([c2, c2, n3, w.inst('mulexp')], 'mp3an', '( ( 2 x. 2 ) ^ 3 ) = ( ( 2 ^ 3 ) x. ( 2 ^ 3 ) )')
    cu = w.s([], 'cu2', '( 2 ^ 3 ) = 8')
    e = w.s([cu, cu], 'oveq12i', '( ( 2 ^ 3 ) x. ( 2 ^ 3 ) ) = ( 8 x. 8 )')
    f = num.mul_lits(w, '8', '8')
    return w.s([w.s([w.s([c_, d], 'eqtri', '( 4 ^ 3 ) = ( ( 2 ^ 3 ) x. ( 2 ^ 3 ) )'), e], 'eqtri', '( 4 ^ 3 ) = ( 8 x. 8 )'), f], 'eqtri', '( 4 ^ 3 ) = ; 6 4')


def tplb34():
    w = W('tplb34', 'The budget identity ` B ( 3 b + 4 ) = 27 B b ` of TM/PrimTD.lean (` B_three_add_four ` , read by Step5.lean).')
    ph = 'B e. NN0'
    bn = w.s([], 'id', '( %s -> B e. NN0 )' % ph)
    c = Closure(w, ph, {'B': bn})
    st = tmbscale(w, ph, c, '( ( 3 x. B ) + 4 )', 'B', '3', '; 2 7', w.s([], '3exp3', '( 3 ^ 3 ) = ; 2 7'))
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w.run()


def tplb37():
    w = W('tplb37', 'The budget identity ` B ( 3 b + 7 ) = 27 B ( b + 1 ) ` of TM/PrimTD.lean (` B_three_add_seven ` , read by Step5.lean).')
    ph = 'B e. NN0'
    bn = w.s([], 'id', '( %s -> B e. NN0 )' % ph)
    c = Closure(w, ph, {'B': bn})
    st = tmbscale(w, ph, c, '( ( 3 x. B ) + 7 )', '( B + 1 )', '3', '; 2 7', w.s([], '3exp3', '( 3 ^ 3 ) = ; 2 7'))
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w.run()


def tplb410():
    w = W('tplb410', 'The budget identity ` B ( 4 b + 10 ) = 64 B ( b + 1 ) ` of TM/PrimTD.lean (` B_four_add_ten ` , the '
                     'bound of ` smoothGoF_le_B ` and ` smoothTDF_le_B `).')
    ph = 'B e. NN0'
    bn = w.s([], 'id', '( %s -> B e. NN0 )' % ph)
    c = Closure(w, ph, {'B': bn})
    st = tmbscale(w, ph, c, '( ( 4 x. B ) + ; 1 0 )', '( B + 1 )', '4', '; 6 4', cube4(w))
    w.lines[-1] = w.lines[-1].replace(st + ':', 'qed:', 1)
    return w.run()


def tplbsuc():
    w = W('tplbsuc', 'The budget is monotone in the bit bound: ` B b <_ B ( b + 1 ) ` (` B_succ_le ` of TM/PrimTD.lean, read by Step5.lean).')
    ph = 'B e. NN0'
    bn = w.s([], 'id', '( %s -> B e. NN0 )' % ph)
    b1 = w.s([bn, w.inst('peano2nn0')], 'syl', '( %s -> ( B + 1 ) e. NN0 )' % ph)
    br = w.s([bn], 'nn0red', '( %s -> B e. RR )' % ph)
    le = w.s([br], 'lep1d', '( %s -> B <_ ( B + 1 ) )' % ph)
    w.qed([bn, b1, le, w.inst('tmbmono')], 'syl3anc', ST_BSUC)
    return w.run()


def tplbscale():
    w = W('tplbscale', 'Scaling the argument of the budget scales it cubically: ` ( c + 1 ) ^ 3 B m = B ( ( c + 1 ) m + 2 c ) ` '
                       '(` B_scale ` of TM/PrimList.lean, read by Steps23.lean and Step5.lean).')
    ph = '( C e. NN0 /\\ M e. NN0 )'
    cn = w.s([], 'simpl', '( %s -> C e. NN0 )' % ph); mn = w.s([], 'simpr', '( %s -> M e. NN0 )' % ph)
    c = Closure(w, ph, {'C': cn, 'M': mn})
    X = '( ( ( C + 1 ) x. M ) + ( 2 x. C ) )'
    K = '( C + 1 )'
    C3 = lambda Z: '( ( %s + 2 ) ^ 3 )' % Z
    xn = c.mem(X, 'NN0')
    v1 = w.s([xn, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` %s ) = ( ; 6 4 x. %s ) )' % (ph, X, C3(X)))
    e1 = lineq(w, ph, '( %s + 2 )' % X, '( %s x. ( M + 2 ) )' % K, closure=c, products=True)
    e2 = w.s([e1], 'oveq1d', '( %s -> %s = ( ( %s x. ( M + 2 ) ) ^ 3 ) )' % (ph, C3(X), K))
    kc = c.mem(K, 'CC'); mc = c.mem('( M + 2 )', 'CC')
    n3 = w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % ph)
    e3 = w.s([kc, mc, n3, w.inst('mulexp')], 'syl3anc', '( %s -> ( ( %s x. ( M + 2 ) ) ^ 3 ) = ( ( %s ^ 3 ) x. %s ) )' % (ph, K, K, C3('M')))
    e5 = w.s([e2, e3], 'eqtrd', '( %s -> %s = ( ( %s ^ 3 ) x. %s ) )' % (ph, C3(X), K, C3('M')))
    e6 = w.s([e5], 'oveq2d', '( %s -> ( ; 6 4 x. %s ) = ( ; 6 4 x. ( ( %s ^ 3 ) x. %s ) ) )' % (ph, C3(X), K, C3('M')))
    c64 = w.s([num.cc_nat(w, 64)], 'a1i', '( %s -> ; 6 4 e. CC )' % ph)
    k3c = c.mem('( %s ^ 3 )' % K, 'CC'); c3m = c.mem(C3('M'), 'CC')
    e7 = w.s([c64, k3c, c3m, w.inst('mul12')], 'syl3anc', '( %s -> ( ; 6 4 x. ( ( %s ^ 3 ) x. %s ) ) = ( ( %s ^ 3 ) x. ( ; 6 4 x. %s ) ) )' % (ph, K, C3('M'), K, C3('M')))
    v2 = w.s([mn, w.inst('tmbval')], 'syl', '( %s -> ( TMB ` M ) = ( ; 6 4 x. %s ) )' % (ph, C3('M')))
    v2c = w.s([v2], 'eqcomd', '( %s -> ( ; 6 4 x. %s ) = ( TMB ` M ) )' % (ph, C3('M')))
    e8 = w.s([v2c], 'oveq2d', '( %s -> ( ( %s ^ 3 ) x. ( ; 6 4 x. %s ) ) = ( ( %s ^ 3 ) x. ( TMB ` M ) ) )' % (ph, K, C3('M'), K))
    t1 = w.s([v1, e6], 'eqtrd', '( %s -> ( TMB ` %s ) = ( ; 6 4 x. ( ( %s ^ 3 ) x. %s ) ) )' % (ph, X, K, C3('M')))
    t2 = w.s([t1, e7], 'eqtrd', '( %s -> ( TMB ` %s ) = ( ( %s ^ 3 ) x. ( ; 6 4 x. %s ) ) )' % (ph, X, K, C3('M')))
    t3 = w.s([t2, e8], 'eqtrd', '( %s -> ( TMB ` %s ) = ( ( %s ^ 3 ) x. ( TMB ` M ) ) )' % (ph, X, K))
    w.qed([t3], 'eqcomd', ST_BSCALE)
    return w.run()


def tpl2pow():
    w = W('tpl2pow', '` n + 1 <_ 2 ^ n ` (` two_pow_mul_le ` of TM/PrimList.lean, read by Steps23.lean), from ~ bernneq3 .')
    ph = 'N e. NN0'
    nn = w.s([], 'id', '( %s -> N e. NN0 )' % ph)
    z2 = w.s([], '2z', '2 e. ZZ'); u2 = w.s([z2, w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    u2a = w.s([u2], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    lt = w.s([u2a, nn, w.inst('bernneq3')], 'syl2anc', '( %s -> N < ( 2 ^ N ) )' % ph)
    n2 = w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % ph)
    pn = w.s([n2, nn], 'nn0expcld', '( %s -> ( 2 ^ N ) e. NN0 )' % ph)
    bi = w.s([nn, pn, w.inst('nn0ltp1le')], 'syl2anc', '( %s -> ( N < ( 2 ^ N ) <-> ( N + 1 ) <_ ( 2 ^ N ) ) )' % ph)
    w.qed([bi, lt], 'mpbid', ST_2POW)
    return w.run()


def tplpowsuc():
    w = W('tplpowsuc', '` a < 2 ^ b -> a < 2 ^ ( b + 1 ) ` (` lt_pow_succ ` of TM/PrimTD.lean, read by Steps23, Overhead and Step5).')
    ph = '( A e. RR /\\ B e. NN0 /\\ A < ( 2 ^ B ) )'
    ar = w.s([], 'simp1', '( %s -> A e. RR )' % ph); bn = w.s([], 'simp2', '( %s -> B e. NN0 )' % ph); lt = w.s([], 'simp3', '( %s -> A < ( 2 ^ B ) )' % ph)
    r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph)
    bz = w.s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph)
    b1z = w.s([bz], 'peano2zd', '( %s -> ( B + 1 ) e. ZZ )' % ph)
    l12 = w.s([w.s([], '1lt2', '1 < 2')], 'a1i', '( %s -> 1 < 2 )' % ph)
    br = w.s([bn], 'nn0red', '( %s -> B e. RR )' % ph)
    bl = w.s([br], 'ltp1d', '( %s -> B < ( B + 1 ) )' % ph)
    j1 = w.s([r2, bz, b1z], '3jca', '( %s -> ( 2 e. RR /\\ B e. ZZ /\\ ( B + 1 ) e. ZZ ) )' % ph)
    j2 = w.s([l12, bl], 'jca', '( %s -> ( 1 < 2 /\\ B < ( B + 1 ) ) )' % ph)
    pl = w.s([j1, j2, w.inst('ltexp2a')], 'syl2anc', '( %s -> ( 2 ^ B ) < ( 2 ^ ( B + 1 ) ) )' % ph)
    pr = w.s([r2, bn], 'reexpcld', '( %s -> ( 2 ^ B ) e. RR )' % ph)
    b1n = w.s([bn, w.inst('peano2nn0')], 'syl', '( %s -> ( B + 1 ) e. NN0 )' % ph)
    pr1 = w.s([r2, b1n], 'reexpcld', '( %s -> ( 2 ^ ( B + 1 ) ) e. RR )' % ph)
    w.qed([ar, pr, pr1, lt, pl], 'lttrd', ST_POWSUC)
    return w.run()


def tplprodle():
    w = W('tplprodle', 'The product of a list of numbers below ` 2 ^ b ` is at most ` 2 ^ ( |l| b ) ` (` prodL_le_two_pow ` of '
                       'TM/PrimList.lean, read by Step4, Steps23 and Step5), on A1b\'s ~ prodlspec by ~ fprodle .')
    ph = '( L e. Word NN0 /\\ B e. NN0 /\\ A. p e. ran L p < ( 2 ^ B ) )'
    ll = w.s([], 'simp1', '( %s -> L e. Word NN0 )' % ph); bn = w.s([], 'simp2', '( %s -> B e. NN0 )' % ph); ral = w.s([], 'simp3', '( %s -> A. p e. ran L p < ( 2 ^ B ) )' % ph)
    NL = '( # ` L )'; A = '( 0 ..^ %s )' % NL
    spec = w.s([ll, w.inst('prodlspec')], 'syl', '( %s -> ( 1st ` ( ProdL ` L ) ) = prod_ i e. %s ( L ` i ) )' % (ph, A))
    pi = '( %s /\\ i e. %s )' % (ph, A)
    nf = w.s([], 'nfv', 'F/ i %s' % ph)
    fi = w.s([w.s([], 'fzofi', '%s e. Fin' % A)], 'a1i', '( %s -> %s e. Fin )' % (ph, A))
    lla = w.s([ll], 'adantr', '( %s -> L e. Word NN0 )' % pi); ii = w.s([], 'simpr', '( %s -> i e. %s )' % (pi, A))
    li = w.s([lla, ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` i ) e. NN0 )' % pi)
    lir = w.s([li], 'nn0red', '( %s -> ( L ` i ) e. RR )' % pi)
    lig = w.s([li], 'nn0ge0d', '( %s -> 0 <_ ( L ` i ) )' % pi)
    r2 = w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % ph)
    pr = w.s([r2, bn], 'reexpcld', '( %s -> ( 2 ^ B ) e. RR )' % ph)
    pra = w.s([pr], 'adantr', '( %s -> ( 2 ^ B ) e. RR )' % pi)
    fn = w.s([lla, w.inst('wrdfn')], 'syl', '( %s -> L Fn %s )' % (pi, A))
    rn = w.s([fn, ii, w.inst('fnfvelrn')], 'syl2anc', '( %s -> ( L ` i ) e. ran L )' % pi)
    cg = w.s([], 'breq1', '( p = ( L ` i ) -> ( p < ( 2 ^ B ) <-> ( L ` i ) < ( 2 ^ B ) ) )')
    rala = w.s([ral], 'adantr', '( %s -> A. p e. ran L p < ( 2 ^ B ) )' % pi)
    lt = w.s([cg, rala, rn], 'rspcdva', '( %s -> ( L ` i ) < ( 2 ^ B ) )' % pi)
    le = w.s([lt], 'ltled', '( %s -> ( L ` i ) <_ ( 2 ^ B ) )' % pi)
    pl = w.s([nf, fi, lir, lig, pra, le], 'fprodle', '( %s -> prod_ i e. %s ( L ` i ) <_ prod_ i e. %s ( 2 ^ B ) )' % (ph, A, A))
    pc = w.s([pr], 'recnd', '( %s -> ( 2 ^ B ) e. CC )' % ph)
    fc = w.s([fi, pc, w.inst('fprodconst')], 'syl2anc', '( %s -> prod_ i e. %s ( 2 ^ B ) = ( ( 2 ^ B ) ^ ( # ` %s ) ) )' % (ph, A, A))
    nl = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    hs = w.s([nl, w.inst('hashfzo0')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, A, NL))
    fc2 = w.s([hs], 'oveq2d', '( %s -> ( ( 2 ^ B ) ^ ( # ` %s ) ) = ( ( 2 ^ B ) ^ %s ) )' % (ph, A, NL))
    c2 = w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % ph)
    em = w.s([c2, bn, nl, w.inst('expmul')], 'syl3anc', '( %s -> ( 2 ^ ( B x. %s ) ) = ( ( 2 ^ B ) ^ %s ) )' % (ph, NL, NL))
    bc = w.s([bn], 'nn0cnd', '( %s -> B e. CC )' % ph); nc = w.s([nl], 'nn0cnd', '( %s -> %s e. CC )' % (ph, NL))
    mc = w.s([bc, nc], 'mulcomd', '( %s -> ( B x. %s ) = ( %s x. B ) )' % (ph, NL, NL))
    mc2 = w.s([mc], 'oveq2d', '( %s -> ( 2 ^ ( B x. %s ) ) = ( 2 ^ ( %s x. B ) ) )' % (ph, NL, NL))
    e1 = w.s([fc, fc2], 'eqtrd', '( %s -> prod_ i e. %s ( 2 ^ B ) = ( ( 2 ^ B ) ^ %s ) )' % (ph, A, NL))
    e2 = w.s([em, mc2], 'eqtr3d', '( %s -> ( ( 2 ^ B ) ^ %s ) = ( 2 ^ ( %s x. B ) ) )' % (ph, NL, NL))
    e3 = w.s([e1, e2], 'eqtrd', '( %s -> prod_ i e. %s ( 2 ^ B ) = ( 2 ^ ( %s x. B ) ) )' % (ph, A, NL))
    pl2 = w.s([pl, e3], 'breqtrd', '( %s -> prod_ i e. %s ( L ` i ) <_ ( 2 ^ ( %s x. B ) ) )' % (ph, A, NL))
    w.qed([spec, pl2], 'eqbrtrd', ST_PRODLE)
    return w.run()


if __name__ == '__main__':
    for f in [tplb34, tplb37, tplb410, tplbsuc, tplbscale, tpl2pow, tplpowsuc, tplprodle]:
        if want(f.__name__): f()
