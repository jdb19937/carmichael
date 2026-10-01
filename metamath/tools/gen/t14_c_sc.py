"""Sortie T14 (c2): the three power-of-two scales of ScTM against their real targets
(sctmw: z99, sctmy: y, sctmth: theta).  MM_DB=sorties/t14.mm python3 tools/gen/t14_c_sc.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t14lib import *


def two_pow_le4(w, A, cl, s, sle2):
    """( A -> ( 2 ^c s ) <_ 4 ) from ( A -> s <_ 2 )"""
    t2 = w.s([w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2')], 'pm3.2i', '( 2 e. RR /\\ 1 < 2 )')], 'a1i',
             '( %s -> ( 2 e. RR /\\ 1 < 2 ) )' % A)
    bi = w.s([t2, cj(w, A, [cl.mem(s, 'RR'), cl.mem('2', 'RR')]), w.inst('cxple')], 'syl2anc',
             '( %s -> ( %s <_ 2 <-> ( 2 ^c %s ) <_ ( 2 ^c 2 ) ) )' % (A, s, s))
    a = w.s([sle2, bi], 'mpbid', '( %s -> ( 2 ^c %s ) <_ ( 2 ^c 2 ) )' % (A, s))
    e = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([], '2nn0', '2 e. NN0'), w.inst('cxpexp')], 'mp2an', '( 2 ^c 2 ) = ( 2 ^ 2 )'),
             w.s([], 'sq2', '( 2 ^ 2 ) = 4')], 'eqtri', '( 2 ^c 2 ) = 4')
    return w.s([a, w.s([e], 'a1i', '( %s -> ( 2 ^c 2 ) = 4 )' % A)], 'breqtrd', '( %s -> ( 2 ^c %s ) <_ 4 )' % (A, s))


def sandwich(w, A, cl, X, R, Q, al, rr, bnds, label, slehyps=()):
    """the common tail: ceildv at R , Q; bnds(c1, c2, f) returns the steps
    ( al x. B ) <_ f and f <_ ( ( al x. B ) + rr ) with B = ( Nlog X + 1 ); then p2sw and 2 ^c ( al + rr ) <_ 4"""
    f = '( |_ ` ( %s / %s ) )' % (R, Q)
    cd = use(w, A, 'ceildv', [cl.mem(R, 'ZZ'), cl.mem(Q, 'NN')],
             '( ( ( %s - %s ) + 1 ) <_ ( %s x. %s ) /\\ ( %s x. %s ) <_ %s )' % (R, Q, Q, f, Q, f, R))
    c1, c2 = proj(w, A, cd, 0), proj(w, A, cd, 1)
    qre = cl.mem('( %s / %s )' % (R, Q), 'RR')
    q0 = cl.ge0('( %s / %s )' % (R, Q))
    fn = w.s([qre, q0, w.inst('flge0nn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (A, f))
    cl.have(f, 'NN0', fn); cl.atom(f)
    h1, h2 = bnds(c1, c2, f)
    B = '( %s + 1 )' % NL(X)
    xa = '( %s ^c %s )' % (X, al)
    p = use(w, A, 'p2sw', [[cl.mem(X, 'NN'), fn], [cl.mem(al, 'RR'), cl.ge0(al), cl.mem(rr, 'RR')], [h1, h2]],
            '( %s <_ ( 2 ^ %s ) /\\ ( 2 ^ %s ) <_ ( ( 2 ^c ( %s + %s ) ) x. %s ) )' % (xa, f, f, al, rr, xa))
    lo, hi = proj(w, A, p, 0), proj(w, A, p, 1)
    s = '( %s + %s )' % (al, rr)
    sle2 = linarith(w, A, list(slehyps), '%s <_ 2' % s, closure=cl)
    t4 = two_pow_le4(w, A, cl, s, sle2)
    xa0 = w.s([cl.mem(X, 'RR+'), cl.mem(al, 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, xa))
    m = w.s([cl.mem('( 2 ^c %s )' % s, 'RR'), cl.mem('4', 'RR'), cl.mem(xa, 'RR'),
             w.s([xa0], 'rpge0d', '( %s -> 0 <_ %s )' % (A, xa)), t4], 'lemul1ad',
            '( %s -> ( ( 2 ^c %s ) x. %s ) <_ ( 4 x. %s ) )' % (A, s, xa, xa))
    hi2 = w.s([cl.mem('( 2 ^ %s )' % f, 'RR'), cl.mem('( ( 2 ^c %s ) x. %s )' % (s, xa), 'RR'), cl.mem('( 4 x. %s )' % xa, 'RR'),
               hi, m], 'letrd', '( %s -> ( 2 ^ %s ) <_ ( 4 x. %s ) )' % (A, f, xa))
    w.qed([lo, hi2], 'jca', '( %s -> %s )' % (A, STMTS14[label].split(' -> ', 1)[1][:-2]))


# ------------------------------------------------------------------ sctmw
def sctmw():
    w = W('sctmw', 'The reservoir floor of the machine scales: z ^c 0.99 <_ 2 ^ |_ ( 99 bits z + 99 ) / 100 _| <_ '
                   '4 z ^c 0.99 (Lean: the w_lo, w_hi of scalesTM_inWindow).')
    A = 'Z e. NN'
    cl = Closure(w, A, {'Z': ('NN', w.s([], 'id', '( Z e. NN -> Z e. NN )'))})
    B = BZ_('Z'); cl.atom(NL('Z'))
    R = '( ( ; 9 9 x. %s ) + ; 9 9 )' % B

    def bnds(c1, c2, f):
        h1 = linarith(w, A, [c1], '( %s x. %s ) <_ %s' % (C99, B, f), closure=cl)
        h2 = linarith(w, A, [c2], '%s <_ ( ( %s x. %s ) + %s )' % (f, C99, B, C99), closure=cl)
        return h1, h2
    sandwich(w, A, cl, 'Z', R, '; ; 1 0 0', C99, C99, bnds, 'sctmw')
    return run(w)


# ------------------------------------------------------------------ sctmth
def sctmth():
    w = W('sctmth', 'The pool threshold of the machine scales: X ^c 1.2 <_ 2 ^ |_ ( 6 bits X + 4 ) / 5 _| <_ '
                    '4 X ^c 1.2 (Lean: the theta_lo, theta_hi of scalesTM_inWindow, at X = Nlog n + 1).')
    A = 'X e. NN'
    cl = Closure(w, A, {'X': ('NN', w.s([], 'id', '( X e. NN -> X e. NN )'))})
    B = BX; cl.atom(NL('X'))
    R = '( ( 6 x. %s ) + 4 )' % B

    def bnds(c1, c2, f):
        h1 = linarith(w, A, [c1], '( %s x. %s ) <_ %s' % (C65, B, f), closure=cl)
        h2 = linarith(w, A, [c2], '%s <_ ( ( %s x. %s ) + ( 4 / 5 ) )' % (f, C65, B), closure=cl)
        return h1, h2
    sandwich(w, A, cl, 'X', R, '5', C65, '( 4 / 5 )', bnds, 'sctmth')
    return run(w)


# ------------------------------------------------------------------ sctmy
def sctmy():
    w = W('sctmy', 'The smoothness bound of the machine scales: z ^c ( 1 - 1 / K ) <_ 2 ^ |_ ( ( K - 1 ) bits z + K - 1 ) / K _| '
                   '<_ 4 z ^c ( 1 - 1 / K ) (Lean: the y_lo, y_hi of scalesTM_inWindow).')
    A = '( Z e. NN /\\ K e. NN )'
    pj = Proj(w, A)
    cl = Closure(w, A, {'Z': ('NN', pj('Z e. NN')), 'K': ('NN', pj('K e. NN'))})
    B = BZ_('Z'); cl.atom(NL('Z'))
    R = '( ( ( ( K - 1 ) x. %s ) + K ) - 1 )' % B
    rk = '( 1 / K )'
    rkre = w.s([pj('K e. NN'), w.inst('nnrecre')], 'syl', '( %s -> %s e. RR )' % (A, rk))
    rk0 = w.s([pj('K e. NN'), w.inst('nnrecgt0')], 'syl', '( %s -> 0 < %s )' % (A, rk))
    k1 = w.s([cl.mem('K', 'NN'), w.inst('nnge1')], 'syl', '( %s -> 1 <_ K )' % A)
    one = w.s([w.s([], '1rp', '1 e. RR+')], 'a1i', '( %s -> 1 e. RR+ )' % A)
    lr = w.s([one, cl.mem('K', 'RR+')], 'lerecd', '( %s -> ( 1 <_ K <-> ( 1 / K ) <_ ( 1 / 1 ) ) )' % A)
    lr2 = w.s([k1, lr], 'mpbid', '( %s -> ( 1 / K ) <_ ( 1 / 1 ) )' % A)
    rk1 = w.s([lr2, w.s([w.s([], '1div1e1', '( 1 / 1 ) = 1')], 'a1i', '( %s -> ( 1 / 1 ) = 1 )' % A)], 'breqtrd',
              '( %s -> ( 1 / K ) <_ 1 )' % A)
    cl.leaf(rk, 'RR', rkre)
    al0 = linarith(w, A, [rk1], '0 <_ %s' % AK, closure=cl); cl.have(AK, 'ge0', al0)
    kcn = cl.mem('K', 'CC'); bcn = cl.mem(B, 'CC')
    e1 = w.s([kcn, cl.mem('1', 'CC'), cl.mem(rk, 'CC')], 'subdid', '( %s -> ( K x. %s ) = ( ( K x. 1 ) - ( K x. %s ) ) )' % (A, AK, rk))
    e2 = w.s([kcn], 'mulridd', '( %s -> ( K x. 1 ) = K )' % A)
    e3 = w.s([kcn, cl.ne0('K')], 'recidd', '( %s -> ( K x. %s ) = 1 )' % (A, rk))
    e4 = w.s([e2, e3], 'oveq12d', '( %s -> ( ( K x. 1 ) - ( K x. %s ) ) = ( K - 1 ) )' % (A, rk))
    e5 = w.s([e1, e4], 'eqtrd', '( %s -> ( K x. %s ) = ( K - 1 ) )' % (A, AK))
    e6 = w.s([kcn, cl.mem(AK, 'CC'), bcn], 'mulassd', '( %s -> ( ( K x. %s ) x. %s ) = ( K x. ( %s x. %s ) ) )' % (A, AK, B, AK, B))
    e7 = w.s([e5], 'oveq1d', '( %s -> ( ( K x. %s ) x. %s ) = ( ( K - 1 ) x. %s ) )' % (A, AK, B, B))
    eq = w.s([e6, e7], 'eqtr3d', '( %s -> ( K x. ( %s x. %s ) ) = ( ( K - 1 ) x. %s ) )' % (A, AK, B, B))
    X1 = '( K x. ( %s x. %s ) )' % (AK, B)
    cl.atom(X1)
    krp = cl.mem('K', 'RR+')

    def bnds(c1, c2, f):
        cl.atom('( K x. %s )' % f)
        g1 = nlinarith(w, A, [c1, eq], '%s <_ ( K x. %s )' % (X1, f), closure=cl)
        bi = w.s([cl.mem('( %s x. %s )' % (AK, B), 'RR'), cl.mem(f, 'RR'), krp], 'lemul2d',
                 '( %s -> ( ( %s x. %s ) <_ %s <-> %s <_ ( K x. %s ) ) )' % (A, AK, B, f, X1, f))
        h1 = w.s([g1, bi], 'mpbird', '( %s -> ( %s x. %s ) <_ %s )' % (A, AK, B, f))
        Y = '( ( %s x. %s ) + 1 )' % (AK, B)
        d = w.s([kcn, cl.mem('( %s x. %s )' % (AK, B), 'CC'), cl.mem('1', 'CC')], 'adddid',
                '( %s -> ( K x. %s ) = ( %s + ( K x. 1 ) ) )' % (A, Y, X1))
        cl.atom('( K x. %s )' % Y)
        g2 = nlinarith(w, A, [c2, eq, d, e2], '( K x. %s ) <_ ( K x. %s )' % (f, Y), closure=cl)
        bi2 = w.s([cl.mem(f, 'RR'), cl.mem(Y, 'RR'), krp], 'lemul2d',
                  '( %s -> ( %s <_ %s <-> ( K x. %s ) <_ ( K x. %s ) ) )' % (A, f, Y, f, Y))
        h2 = w.s([g2, bi2], 'mpbird', '( %s -> %s <_ %s )' % (A, f, Y))
        return h1, h2
    b0 = cl.ge0(B)
    cl.have(R, 'ge0', nlinarith(w, A, [k1, b0], '0 <_ %s' % R, closure=cl))
    sandwich(w, A, cl, 'Z', R, 'K', AK, '1', bnds, 'sctmy', [rk0])
    return run(w)


if __name__ == '__main__':
    for f in (sctmw, sctmth, sctmy):
        if want(f.__name__):
            f()
