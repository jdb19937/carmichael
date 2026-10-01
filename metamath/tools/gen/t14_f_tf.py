"""Sortie T14 (d): the time function of the input length (Lean: exists_timeFun, exists_timeFun_of_ExpB).
MM_DB=sorties/t14.mm python3 tools/gen/t14_f_tf.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t14lib import *
from tm import sub

TFt = TF()
FL = lambda k: '( |_ ` ( exp ` ( ( C x. ( log ` %s ) ) x. ( log ` ( log ` %s ) ) ) ) )' % (k, k)
EX = lambda k: '( exp ` ( ( C x. ( log ` %s ) ) x. ( log ` ( log ` %s ) ) ) )' % (k, k)
SUMk = lambda k: 'sum_ j e. ( 0 ..^ ( 2 ^ %s ) ) ( G ` j )' % k
IFk = lambda k: 'if ( ( M + 3 ) <_ %s , %s , %s )' % (k, FL(k), SUMk(k))
BODY = lambda x: '( 1 <_ %s /\\ ( G ` %s ) <_ %s )' % (L2(x), x, EXP('C', MM(x)))


def tmfun():
    w = W('tmfun', 'The time function of the input length: from per-input step counts G n <_ exp ( C ell2 n ell3 n ) '
                   'for n >= M, the function k |-> |_ exp ( C log k log log k ) _| for k >= M + 3 and the sum of G over '
                   'the inputs below 2 ^ k otherwise dominates every input of length k (Lean: exists_timeFun, '
                   'exists_timeFun_of_ExpB, with a sum for the finite maximum).')
    A0 = STMTS14['tmfun'].split(' -> ( %s' % TFt)[0][2:]
    TYP = '( G : NN0 --> NN0 /\\ C e. RR+ /\\ M e. NN0 )'
    HX = 'A. x e. ( ZZ>= ` M ) %s' % BODY('x')
    A = '( %s /\\ %s )' % (TYP, HX)
    assert A0 == '( %s /\\ A. n e. ( ZZ>= ` M ) %s )' % (TYP, BODY('n')), A0[:200]
    pj = Proj(w, A)
    gf = pj('G : NN0 --> NN0'); crp = pj('C e. RR+'); mn0 = pj('M e. NN0')
    hx = pj(HX)
    # (1) TF : NN0 --> NN0
    Ak = '( %s /\\ k e. NN0 )' % A
    k1 = '( %s /\\ ( M + 3 ) <_ k )' % Ak
    pk = Proj(w, k1)
    clk = Closure(w, k1, {'k': ('NN0', pk('k e. NN0')), 'M': ('NN0', lift(w, mn0, k1)), 'C': ('RR+', lift(w, crp, k1))})
    kge = pk('( M + 3 ) <_ k')
    k1gt = linarith(w, k1, [kge, clk.ge0('M')], '1 < k', closure=clk)
    lkrp = w.s([clk.mem('k', 'RR'), k1gt, w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` k ) e. RR+ )' % k1)
    clk.have('( log ` k )', 'RR+', lkrp)
    exre = clk.mem(EX('k'), 'RR')
    ex0 = w.s([w.s([], '0red', '( %s -> 0 e. RR )' % k1), exre,
               w.s([clk.mem('( ( C x. ( log ` k ) ) x. ( log ` ( log ` k ) ) )', 'RR'), w.inst('efgt0')], 'syl',
                   '( %s -> 0 < %s )' % (k1, EX('k')))], 'ltled', '( %s -> 0 <_ %s )' % (k1, EX('k')))
    f1 = w.s([exre, ex0, w.inst('flge0nn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (k1, FL('k')))
    k2 = '( %s /\\ -. ( M + 3 ) <_ k )' % Ak
    pk2 = Proj(w, k2)
    k2j = '( %s /\\ j e. ( 0 ..^ ( 2 ^ k ) ) )' % k2
    gj = w.s([lift(w, gf, k2j), w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ ( 2 ^ k ) ) )' % k2j), w.inst('elfzonn0')], 'syl',
                                    '( %s -> j e. NN0 )' % k2j)], 'ffvelcdmd', '( %s -> ( G ` j ) e. NN0 )' % k2j)
    fin = w.s([w.s([], 'fzofi', '( 0 ..^ ( 2 ^ k ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( 2 ^ k ) ) e. Fin )' % k2)
    f2 = w.s([fin, gj], 'fsumnn0cl', '( %s -> %s e. NN0 )' % (k2, SUMk('k')))
    ifc = w.s([f1, f2], 'ifclda', '( %s -> %s e. NN0 )' % (Ak, IFk('k')))
    tff = w.s([ifc, w.s([], 'eqid', '%s = %s' % (TFt, TFt))], 'fmptd', '( %s -> %s : NN0 --> NN0 )' % (A, TFt))
    # the value at a natural argument
    def value(ante, X, xn0, ifcX):
        """( ante -> ( TF ` X ) = IF( X ) )"""
        Ae = '( %s /\\ k = %s )' % (ante, X)
        eqk = w.s([], 'simpr', '( %s -> k = %s )' % (Ae, X))
        cg, new = w.congr(IFk('k'), {'k': X}, Ae, {'k': eqk})
        assert new == IFk(X), new[:200]
        return w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, TFt, TFt)), cg, xn0, ifcX], 'fvmptd',
                   '( %s -> ( %s ` %s ) = %s )' % (ante, TFt, X, IFk(X)))

    def rsp_at(w, ante, A, ifc, X, xn0):
        ral = lift(w, w.s([ifc], 'ralrimiva', '( %s -> A. k e. NN0 %s e. NN0 )' % (A, IFk('k'))), ante)
        idk = w.s([], 'id', '( k = %s -> k = %s )' % (X, X))
        cg, new = w.wcongr('%s e. NN0' % IFk('k'), {'k': X}, 'k = %s' % X, {'k': idk})
        return w.s([cg, ral, xn0], 'rspcdva', '( %s -> %s e. NN0 )' % (ante, IFk(X)))
    # (3) the bound for k >= M + 3
    A3 = '( %s /\\ n e. ( ZZ>= ` ( M + 3 ) ) )' % A
    p3 = Proj(w, A3)
    nz = p3('n e. ( ZZ>= ` ( M + 3 ) )')
    mge = w.s([nz, w.inst('eluzle')], 'syl', '( %s -> ( M + 3 ) <_ n )' % A3)
    cl3 = Closure(w, A3, {'M': ('NN0', lift(w, mn0, A3)), 'C': ('RR+', lift(w, crp, A3))})
    nzz = w.s([nz, w.inst('eluzelz')], 'syl', '( %s -> n e. ZZ )' % A3)
    cl3.have('n', 'ZZ', nzz)
    n0 = linarith(w, A3, [mge, cl3.ge0('M')], '0 <_ n', closure=cl3)
    nn0 = w.s([nzz, n0], 'jca', '( %s -> ( n e. ZZ /\\ 0 <_ n ) )' % A3)
    nn0 = w.s([nn0, w.s([w.s([], 'elnn0z', '( n e. NN0 <-> ( n e. ZZ /\\ 0 <_ n ) )')], 'a1i',
                        '( %s -> ( n e. NN0 <-> ( n e. ZZ /\\ 0 <_ n ) ) )' % A3)], 'mpbird', '( %s -> n e. NN0 )' % A3)
    cl3.have('n', 'NN0', nn0)
    v3 = value(A3, 'n', nn0, rsp_at(w, A3, A, ifc, 'n', nn0))
    it3 = w.s([mge], 'iftrued', '( %s -> %s = %s )' % (A3, IFk('n'), FL('n')))
    n1 = linarith(w, A3, [mge, cl3.ge0('M')], '1 < n', closure=cl3)
    cl3.have('( log ` n )', 'RR+', w.s([cl3.mem('n', 'RR'), n1, w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` n ) e. RR+ )' % A3))
    fl3 = w.s([cl3.mem(EX('n'), 'RR'), w.inst('flle')], 'syl', '( %s -> %s <_ %s )' % (A3, FL('n'), EX('n')))
    b3 = w.s([w.s([v3, it3], 'eqtrd', '( %s -> ( %s ` n ) = %s )' % (A3, TFt, FL('n'))), fl3], 'eqbrtrd',
             '( %s -> ( %s ` n ) <_ %s )' % (A3, TFt, EX('n')))
    r3 = w.s([b3], 'ralrimiva', '( %s -> A. n e. ( ZZ>= ` ( M + 3 ) ) ( %s ` n ) <_ %s )' % (A, TFt, EX('n')))
    # (2) every input: G n <_ TF ( # encodeNat n )
    A2 = '( %s /\\ n e. NN0 )' % A
    p2 = Proj(w, A2)
    n0_ = p2('n e. NN0')
    Nn = '( # ` ( encodeNat ` n ) )'
    nw = w.s([n0_, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` n ) e. Word 2o )' % A2)
    Nn0 = w.s([nw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (A2, Nn))
    v2 = value(A2, Nn, Nn0, rsp_at(w, A2, A, ifc, Nn, Nn0))
    gn = w.s([lift(w, gf, A2), n0_], 'ffvelcdmd', '( %s -> ( G ` n ) e. NN0 )' % A2)
    # case M + 3 <_ N
    B1 = '( %s /\\ ( M + 3 ) <_ %s )' % (A2, Nn)
    q1 = Proj(w, B1)
    cb = Closure(w, B1, {'M': ('NN0', lift(w, mn0, B1)), 'C': ('RR+', lift(w, crp, B1)), 'n': ('NN0', lift(w, n0_, B1)),
                         Nn: ('NN0', lift(w, Nn0, B1)), '( G ` n )': ('NN0', lift(w, gn, B1))})
    cb.atom(Nn); cb.atom('( G ` n )')
    ng = q1('( M + 3 ) <_ %s' % Nn)
    m2 = linarith(w, B1, [ng], '( ( M + 2 ) + 1 ) <_ %s' % Nn, closure=cb)
    mn = w.s([cj(w, B1, [cb.mem('n', 'NN0'), cb.mem('( M + 2 )', 'NN0'), m2]), w.inst('encnatlensuc')], 'syl',
             '( %s -> ( M + 2 ) <_ n )' % B1)
    nM = w.s([w.s([cb.mem('M', 'ZZ'), cb.mem('n', 'ZZ'), linarith(w, B1, [mn], 'M <_ n', closure=cb)], '3jca',
                  '( %s -> ( M e. ZZ /\\ n e. ZZ /\\ M <_ n ) )' % B1),
              w.s([w.s([], 'eluz2', '( n e. ( ZZ>= ` M ) <-> ( M e. ZZ /\\ n e. ZZ /\\ M <_ n ) )')], 'a1i',
                  '( %s -> ( n e. ( ZZ>= ` M ) <-> ( M e. ZZ /\\ n e. ZZ /\\ M <_ n ) ) )' % B1)], 'mpbird',
             '( %s -> n e. ( ZZ>= ` M ) )' % B1)
    idx = w.s([], 'id', '( x = n -> x = n )')
    cgx, newx = w.wcongr(BODY('x'), {'x': 'n'}, 'x = n', {'x': idx})
    assert newx == BODY('n'), newx
    hn = w.s([cgx, lift(w, hx, B1), nM], 'rspcdva', '( %s -> %s )' % (B1, BODY('n')))
    l21 = proj(w, B1, hn, 0); gle = proj(w, B1, hn, 1)
    l2, l3 = L2('n'), L3('n')
    nnn = linarith(w, B1, [mn, cb.ge0('M')], '1 < n', closure=cb)
    cb.have('n', 'gt0', linarith(w, B1, [nnn], '0 < n', closure=cb))
    lnrp = w.s([cb.mem('n', 'RR'), nnn, w.inst('rplogcl')], 'syl2anc', '( %s -> ( log ` n ) e. RR+ )' % B1)
    cb.have('( log ` n )', 'RR+', lnrp); cb.atom('( log ` n )')
    v2e = w.s([cb.mem('n', 'NN0'), w.inst('ell2val')], 'syl', '( %s -> %s = ( log ` ( log ` n ) ) )' % (B1, l2))
    v3e = w.s([cb.mem('n', 'NN0'), w.inst('ell3val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (B1, l3, l2))
    l2re = w.s([v2e, cb.mem('( log ` ( log ` n ) )', 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (B1, l2))
    cb.have(l2, 'RR', l2re); cb.atom(l2)
    l2rp = w.s([l2re, linarith(w, B1, [l21], '0 < %s' % l2, closure=cb)], 'elrpd', '( %s -> %s e. RR+ )' % (B1, l2))
    cb.have(l2, 'RR+', l2rp)
    l3re = w.s([v3e, cb.mem('( log ` %s )' % l2, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (B1, l3))
    cb.have(l3, 'RR', l3re); cb.atom(l3)
    # log n < N log 2 <_ N
    lt = w.s([cb.mem('n', 'NN0'), w.inst('encnatlt')], 'syl', '( %s -> n < ( 2 ^ %s ) )' % (B1, Nn))
    two = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % B1)
    p2rp = w.s([two, cb.mem(Nn, 'ZZ')], 'rpexpcld', '( %s -> ( 2 ^ %s ) e. RR+ )' % (B1, Nn))
    bi = w.s([cb.mem('n', 'RR+'), p2rp, w.inst('logltb')], 'syl2anc',
             '( %s -> ( n < ( 2 ^ %s ) <-> ( log ` n ) < ( log ` ( 2 ^ %s ) ) ) )' % (B1, Nn, Nn))
    lt2 = w.s([lt, bi], 'mpbid', '( %s -> ( log ` n ) < ( log ` ( 2 ^ %s ) ) )' % (B1, Nn))
    re2 = w.s([two, cb.mem(Nn, 'ZZ'), w.inst('relogexp')], 'syl2anc', '( %s -> ( log ` ( 2 ^ %s ) ) = ( %s x. ( log ` 2 ) ) )' % (B1, Nn, Nn))
    lg1 = w.s([w.s([], 'log2le1', '( log ` 2 ) < 1')], 'a1i', '( %s -> ( log ` 2 ) < 1 )' % B1)
    cb.have('( log ` 2 )', 'RR', w.s([two, w.inst('relogcl')], 'syl', '( %s -> ( log ` 2 ) e. RR )' % B1)); cb.atom('( log ` 2 )')
    cb.atom('( log ` ( 2 ^ %s ) )' % Nn)
    lnN = nlinarith(w, B1, [lt2, re2, lg1, cb.ge0(Nn)], '( log ` n ) <_ %s' % Nn, closure=cb)
    N3 = linarith(w, B1, [ng, cb.ge0('M')], '1 < %s' % Nn, closure=cb)
    cb.have(Nn, 'RR+', w.s([cb.mem(Nn, 'RR'), linarith(w, B1, [N3], '0 < %s' % Nn, closure=cb)], 'elrpd', '( %s -> %s e. RR+ )' % (B1, Nn)))
    import t14_d_win as dw
    a1 = dw.logmono(w, B1, cb, '( log ` n )', Nn, lnN)                       # log log n <_ log N
    a1b = w.s([v2e, a1], 'eqbrtrd', '( %s -> %s <_ ( log ` %s ) )' % (B1, l2, Nn))
    cb.atom('( log ` %s )' % Nn)
    lNrp = w.s([cb.mem('( log ` %s )' % Nn, 'RR'), linarith(w, B1, [a1b, l21], '0 < ( log ` %s )' % Nn, closure=cb)], 'elrpd',
               '( %s -> ( log ` %s ) e. RR+ )' % (B1, Nn))
    cb.have('( log ` %s )' % Nn, 'RR+', lNrp)
    a2 = dw.logmono(w, B1, cb, l2, '( log ` %s )' % Nn, a1b)
    a2b = w.s([v3e, a2], 'eqbrtrd', '( %s -> %s <_ ( log ` ( log ` %s ) ) )' % (B1, l3, Nn))
    l30 = w.s([w.s([l2re, l21, w.inst('logge0')], 'syl2anc', '( %s -> 0 <_ ( log ` %s ) )' % (B1, l2)), v3e], 'breqtrrd',
              '( %s -> 0 <_ %s )' % (B1, l3))
    LN = '( log ` %s )' % Nn; LLN = '( log ` ( log ` %s ) )' % Nn
    pr = w.s([cb.mem(l2, 'RR'), cb.mem(LN, 'RR'), cb.mem(l3, 'RR'), cb.mem(LLN, 'RR'),
              linarith(w, B1, [l21], '0 <_ %s' % l2, closure=cb), l30, a1b, a2b], 'lemul12ad',
             '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (B1, l2, l3, LN, LLN))
    pr2 = w.s([cb.mem('( %s x. %s )' % (l2, l3), 'RR'), cb.mem('( %s x. %s )' % (LN, LLN), 'RR'), cb.mem('C', 'RR'),
               cb.ge0('C'), pr], 'lemul2ad', '( %s -> ( C x. ( %s x. %s ) ) <_ ( C x. ( %s x. %s ) ) )' % (B1, l2, l3, LN, LLN))
    ma = w.s([cb.mem('C', 'CC'), cb.mem(LN, 'CC'), cb.mem(LLN, 'CC')], 'mulassd',
             '( %s -> ( ( C x. %s ) x. %s ) = ( C x. ( %s x. %s ) ) )' % (B1, LN, LLN, LN, LLN))
    pr3 = w.s([pr2, ma], 'breqtrrd', '( %s -> ( C x. %s ) <_ ( ( C x. %s ) x. %s ) )' % (B1, MM('n'), LN, LLN))
    bie = w.s([cb.mem('( C x. %s )' % MM('n'), 'RR'), cb.mem('( ( C x. %s ) x. %s )' % (LN, LLN), 'RR'), w.inst('efle')], 'syl2anc',
              '( %s -> ( ( C x. %s ) <_ ( ( C x. %s ) x. %s ) <-> %s <_ %s ) )' % (B1, MM('n'), LN, LLN, EXP('C', MM('n')), EX(Nn)))
    em = w.s([pr3, bie], 'mpbid', '( %s -> %s <_ %s )' % (B1, EXP('C', MM('n')), EX(Nn)))
    gx = w.s([cb.mem('( G ` n )', 'RR'), cb.mem(EXP('C', MM('n')), 'RR'), cb.mem(EX(Nn), 'RR'), gle, em], 'letrd',
             '( %s -> ( G ` n ) <_ %s )' % (B1, EX(Nn)))
    fb = w.s([cb.mem(EX(Nn), 'RR'), cb.mem('( G ` n )', 'ZZ'), w.inst('flge')], 'syl2anc',
             '( %s -> ( ( G ` n ) <_ %s <-> ( G ` n ) <_ %s ) )' % (B1, EX(Nn), FL(Nn)))
    gf1 = w.s([gx, fb], 'mpbid', '( %s -> ( G ` n ) <_ %s )' % (B1, FL(Nn)))
    it1 = w.s([ng], 'iftrued', '( %s -> %s = %s )' % (B1, IFk(Nn), FL(Nn)))
    c1 = w.s([gf1, w.s([lift(w, v2, B1), it1], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (B1, TFt, Nn, FL(Nn)))], 'breqtrrd',
             '( %s -> ( G ` n ) <_ ( %s ` %s ) )' % (B1, TFt, Nn))
    # case N < M + 3: the sum
    B2 = '( %s /\\ -. ( M + 3 ) <_ %s )' % (A2, Nn)
    it2 = w.s([w.s([], 'simpr', '( %s -> -. ( M + 3 ) <_ %s )' % (B2, Nn))], 'iffalsed', '( %s -> %s = %s )' % (B2, IFk(Nn), SUMk(Nn)))
    B2j = '( %s /\\ j e. ( 0 ..^ ( 2 ^ %s ) ) )' % (B2, Nn)
    gj2 = w.s([lift(w, gf, B2j), w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ..^ ( 2 ^ %s ) ) )' % (B2j, Nn)), w.inst('elfzonn0')], 'syl',
                                     '( %s -> j e. NN0 )' % B2j)], 'ffvelcdmd', '( %s -> ( G ` j ) e. NN0 )' % B2j)
    gjr = w.s([gj2], 'nn0red', '( %s -> ( G ` j ) e. RR )' % B2j)
    gj0 = w.s([gj2], 'nn0ge0d', '( %s -> 0 <_ ( G ` j ) )' % B2j)
    idj = w.s([], 'id', '( j = n -> j = n )')
    cgj, newj = w.congr('( G ` j )', {'j': 'n'}, 'j = n', {'j': idj})
    fin2 = w.s([w.s([], 'fzofi', '( 0 ..^ ( 2 ^ %s ) ) e. Fin' % Nn)], 'a1i', '( %s -> ( 0 ..^ ( 2 ^ %s ) ) e. Fin )' % (B2, Nn))
    B2c = Closure(w, B2, {'n': ('NN0', lift(w, n0_, B2)), Nn: ('NN0', lift(w, Nn0, B2))})
    ltn = w.s([lift(w, n0_, B2), w.inst('encnatlt')], 'syl', '( %s -> n < ( 2 ^ %s ) )' % (B2, Nn))
    E3_ = '( n e. NN0 /\\ ( 2 ^ %s ) e. ZZ /\\ n < ( 2 ^ %s ) )' % (Nn, Nn)
    nin = w.s([w.s([B2c.mem('n', 'NN0'), B2c.mem('( 2 ^ %s )' % Nn, 'ZZ'), ltn], '3jca', '( %s -> %s )' % (B2, E3_)),
               w.s([w.s([], 'elfzo0z', '( n e. ( 0 ..^ ( 2 ^ %s ) ) <-> %s )' % (Nn, E3_))], 'a1i',
                   '( %s -> ( n e. ( 0 ..^ ( 2 ^ %s ) ) <-> %s ) )' % (B2, Nn, E3_))], 'mpbird',
              '( %s -> n e. ( 0 ..^ ( 2 ^ %s ) ) )' % (B2, Nn))
    ge = w.s([fin2, gjr, gj0, cgj, nin], 'fsumge1', '( %s -> ( G ` n ) <_ %s )' % (B2, SUMk(Nn)))
    c2 = w.s([ge, w.s([lift(w, v2, B2), it2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (B2, TFt, Nn, SUMk(Nn)))], 'breqtrrd',
             '( %s -> ( G ` n ) <_ ( %s ` %s ) )' % (B2, TFt, Nn))
    c = w.s([c1, c2], 'pm2.61dan', '( %s -> ( G ` n ) <_ ( %s ` %s ) )' % (A2, TFt, Nn))
    r2 = w.s([c], 'ralrimiva', '( %s -> A. n e. NN0 ( G ` n ) <_ ( %s ` %s ) )' % (A, TFt, Nn))
    concl = w.s([tff, r2, r3], '3jca', '( %s -> %s )' % (A, STMTS14['tmfun'].split(' -> ', 1)[1][:-2]))
    # the renamed hypothesis
    idn = w.s([], 'id', '( n = x -> n = x )')
    cgn, newn = w.wcongr(BODY('n'), {'n': 'x'}, 'n = x', {'n': idn})
    cb_ = w.s([cgn], 'cbvralvw', '( A. n e. ( ZZ>= ` M ) %s <-> %s )' % (BODY('n'), HX))
    an = w.s([cb_], 'anbi2i', '( %s <-> %s )' % (A0, A))
    w.qed([w.s([an], 'biimpi', '( %s -> %s )' % (A0, A)), concl], 'syl', STMTS14['tmfun'])
    return run(w)


if __name__ == '__main__':
    for f in (tmfun,):
        if want(f.__name__):
            f()
