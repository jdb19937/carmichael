"""Sortie T14 (c3): the three layers of iterated Nlog (sctmab), the window of the machine
scales (sctmwin, Lean: scalesTM_inWindow) and its eventual form (sctmwinev).
MM_DB=sorties/t14.mm python3 tools/gen/t14_d_win.py [LABEL...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t14lib import *


def nat_nn(w, A, cl, E, lo):
    """( A -> E e. NN ) from E e. NN0 (closure) and ( A -> x <_ E ) with x >= 1 derivable by lin from lo's hyps"""
    one = linarith(w, A, lo, '1 <_ %s' % E, closure=cl)
    j = cj(w, A, [cl.mem(E, 'NN0'), one])
    st = w.s([j, w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (E, E, E)) and
              w.s([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (E, E, E))], 'a1i',
                  '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) ) )' % (A, E, E, E))], 'mpbird', '( %s -> %s e. NN )' % (A, E))
    cl.have(E, 'NN', st)
    return st


def logmono(w, A, cl, x, y, le):
    """( A -> ( log ` x ) <_ ( log ` y ) ) from x <_ y, both RR+ (closure)"""
    bi = w.s([cl.mem(x, 'RR+'), cl.mem(y, 'RR+'), w.inst('logleb')], 'syl2anc',
             '( %s -> ( %s <_ %s <-> ( log ` %s ) <_ ( log ` %s ) ) )' % (A, x, y, x, y))
    return w.s([le, bi], 'mpbid', '( %s -> ( log ` %s ) <_ ( log ` %s ) )' % (A, x, y))


def logfrac(w, A, q, qm1):
    """( A -> ( log ` q ) <_ qm1 ) for a numeral fraction q >= 1 with q - 1 = qm1 (extrwlogle)"""
    cl0 = Closure(w, A, {})
    ql = linarith(w, A, [], '1 <_ %s' % q, closure=cl0)
    a = w.s([cl0.mem(q, 'RR'), ql, w.inst('extrwlogle')], 'syl2anc', '( %s -> ( log ` %s ) <_ ( %s - 1 ) )' % (A, q, q))
    e = linarith(w, A, [], '( %s - 1 ) <_ %s' % (q, qm1), closure=cl0)
    lre = w.s([cl0.mem(q, 'RR+'), w.inst('relogcl')], 'syl', '( %s -> ( log ` %s ) e. RR )' % (A, q))
    return w.s([lre, cl0.mem('( %s - 1 )' % q, 'RR'), cl0.mem(qm1, 'RR'), a, e], 'letrd', '( %s -> ( log ` %s ) <_ %s )' % (A, q, qm1))


# ------------------------------------------------------------------ sctmab
def sctmab():
    w = W('sctmab', 'The three layers of the machine scales: log n <_ Nlog n <_ 3 / 2 log n, ell2 n <_ a <_ '
                    '3 / 2 ( ell2 n + 1 / 2 ), ell3 n <_ b <_ 3 / 2 ( ell3 n + 0.51 ) for a = Nlog Nlog n, b = Nlog a '
                    '(Lean: layers 1-3 of scalesTM_inWindow).')
    A = WN('N')
    pj = Proj(w, A)
    nuz = pj('N e. ( ZZ>= ` 3 )')
    nnn = w.s([nuz, w.inst('eluz3nn')], 'syl', '( %s -> N e. NN )' % A)
    cl = Closure(w, A, {'N': ('NN', nnn)})
    l2 = L2('N'); l3 = L3('N'); lN = LOG('N')
    h200 = pj('; ; 2 0 0 <_ %s' % l2); h3 = pj('3 <_ %s' % l3)
    n3 = w.s([nuz, w.inst('eluzle')], 'syl', '( %s -> 3 <_ N )' % A)
    n1 = linarith(w, A, [n3], '1 < N', closure=cl)
    lNrp = w.s([cl.mem('N', 'RR'), n1, w.inst('rplogcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A, lN))
    cl.have(lN, 'RR+', lNrp); cl.atom(lN)
    v2 = w.s([cl.mem('N', 'NN0'), w.inst('ell2val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, l2, lN))
    v3 = w.s([cl.mem('N', 'NN0'), w.inst('ell3val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, l3, l2))
    l2re = w.s([v2, cl.mem('( log ` %s )' % lN, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A, l2))
    cl.have(l2, 'RR', l2re); cl.atom(l2)
    l2rp = w.s([l2re, linarith(w, A, [h200], '0 < %s' % l2, closure=cl)], 'elrpd', '( %s -> %s e. RR+ )' % (A, l2))
    cl.have(l2, 'RR+', l2rp)
    l3re = w.s([v3, cl.mem('( log ` %s )' % l2, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A, l3))
    cl.have(l3, 'RR', l3re); cl.atom(l3)
    # log n = exp ( ell2 n ) >= 1 + ell2 n
    ef = w.s([lNrp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` ( log ` %s ) ) = %s )' % (A, lN, lN))
    ef2 = w.s([w.s([v2], 'fveq2d', '( %s -> ( exp ` %s ) = ( exp ` ( log ` %s ) ) )' % (A, l2, lN)), ef], 'eqtrd',
              '( %s -> ( exp ` %s ) = %s )' % (A, l2, lN))
    bv = w.s([l2re, linarith(w, A, [h200], '0 <_ %s' % l2, closure=cl), w.inst('bvefge1p')], 'syl2anc',
             '( %s -> ( 1 + %s ) <_ ( exp ` %s ) )' % (A, l2, l2))
    lN3 = linarith(w, A, [ef2, bv, h200], '3 <_ %s' % lN, closure=cl)
    # layer 1
    LL = NL('N')
    ly1 = use(w, A, 'nloglay', [nnn, [cl.mem(lN, 'RR'), cl.mem('0', 'RR')],
                                [lN3, linarith(w, A, [], '%s <_ %s' % (lN, lN), closure=cl),
                                 linarith(w, A, [], '%s <_ ( %s + 0 )' % (lN, lN), closure=cl)]],
              '( %s <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( %s + 0 ) ) )' % (lN, LL, LL, lN))
    a1, a2 = proj(w, A, ly1, 0), proj(w, A, ly1, 1)
    cl.atom(LL)
    nat_nn(w, A, cl, LL, [a1, lN3])
    # layer 2
    AA = SCA_('N')
    b1 = w.s([v2, logmono(w, A, cl, lN, LL, a1)], 'eqbrtrd', '( %s -> %s <_ ( log ` %s ) )' % (A, l2, LL))
    q32 = '( 3 / 2 )'
    t1 = linarith(w, A, [a2], '%s <_ ( %s x. %s )' % (LL, q32, lN), closure=cl)
    t2 = logmono(w, A, cl, LL, '( %s x. %s )' % (q32, lN), t1)
    t3 = w.s([cl.mem(q32, 'RR+'), lNrp], 'relogmuld', '( %s -> ( log ` ( %s x. %s ) ) = ( ( log ` %s ) + ( log ` %s ) ) )'
             % (A, q32, lN, q32, lN))
    t4 = logfrac(w, A, q32, '( 1 / 2 )')
    cl.atom('( log ` %s )' % LL); cl.atom('( log ` ( %s x. %s ) )' % (q32, lN)); cl.atom('( log ` %s )' % q32)
    cl.atom('( log ` %s )' % lN)
    b2 = linarith(w, A, [t2, t3, t4, v2], '( log ` %s ) <_ ( %s + ( 1 / 2 ) )' % (LL, l2), closure=cl)
    ly2 = use(w, A, 'nloglay', [cl.mem(LL, 'NN'), [l2re, cl.mem('( 1 / 2 )', 'RR')],
                                [linarith(w, A, [h200], '3 <_ %s' % l2, closure=cl), b1, b2]],
              '( %s <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( %s + ( 1 / 2 ) ) ) )' % (l2, AA, AA, l2))
    c1, c2 = proj(w, A, ly2, 0), proj(w, A, ly2, 1)
    cl.atom(AA)
    nat_nn(w, A, cl, AA, [c1, h200])
    # layer 3
    BB = SCB_('N')
    d1 = w.s([v3, logmono(w, A, cl, l2, AA, c1)], 'eqbrtrd', '( %s -> %s <_ ( log ` %s ) )' % (A, l3, AA))
    q151 = '( ; ; 1 5 1 / ; ; 1 0 0 )'
    s1 = linarith(w, A, [c2, h200], '%s <_ ( %s x. %s )' % (AA, q151, l2), closure=cl)
    s2 = logmono(w, A, cl, AA, '( %s x. %s )' % (q151, l2), s1)
    s3 = w.s([cl.mem(q151, 'RR+'), l2rp], 'relogmuld', '( %s -> ( log ` ( %s x. %s ) ) = ( ( log ` %s ) + ( log ` %s ) ) )'
             % (A, q151, l2, q151, l2))
    s4 = logfrac(w, A, q151, '( ; 5 1 / ; ; 1 0 0 )')
    cl.atom('( log ` %s )' % AA); cl.atom('( log ` ( %s x. %s ) )' % (q151, l2)); cl.atom('( log ` %s )' % q151)
    cl.atom('( log ` %s )' % l2)
    d2 = linarith(w, A, [s2, s3, s4, v3], '( log ` %s ) <_ ( %s + ( ; 5 1 / ; ; 1 0 0 ) )' % (AA, l3), closure=cl)
    ly3 = use(w, A, 'nloglay', [cl.mem(AA, 'NN'), [l3re, cl.mem('( ; 5 1 / ; ; 1 0 0 )', 'RR')], [h3, d1, d2]],
              '( %s <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( %s + ( ; 5 1 / ; ; 1 0 0 ) ) ) )' % (l3, BB, BB, l3))
    w.qed([ly1, ly2, ly3], '3jca', '( %s -> %s )' % (A, STMTS14['sctmab'].split(' -> ', 1)[1][:-2]))
    return run(w)


def logn_facts(w, A, cl, nnn, nuz, h200, l2, lN):
    """( A -> log N e. RR+ ), ( A -> 3 <_ log N ) at N with ell2 N >= 200"""
    n3 = w.s([nuz, w.inst('eluzle')], 'syl', '( %s -> 3 <_ N )' % A)
    n1 = linarith(w, A, [n3], '1 < N', closure=cl)
    lNrp = w.s([cl.mem('N', 'RR'), n1, w.inst('rplogcl')], 'syl2anc', '( %s -> %s e. RR+ )' % (A, lN))
    cl.have(lN, 'RR+', lNrp); cl.atom(lN)
    v2 = w.s([cl.mem('N', 'NN0'), w.inst('ell2val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, l2, lN))
    l2re = w.s([v2, cl.mem('( log ` %s )' % lN, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A, l2))
    cl.have(l2, 'RR', l2re); cl.atom(l2)
    ef = w.s([lNrp, w.inst('reeflog')], 'syl', '( %s -> ( exp ` ( log ` %s ) ) = %s )' % (A, lN, lN))
    ef2 = w.s([w.s([v2], 'fveq2d', '( %s -> ( exp ` %s ) = ( exp ` ( log ` %s ) ) )' % (A, l2, lN)), ef], 'eqtrd',
              '( %s -> ( exp ` %s ) = %s )' % (A, l2, lN))
    bv = w.s([l2re, linarith(w, A, [h200], '0 <_ %s' % l2, closure=cl), w.inst('bvefge1p')], 'syl2anc',
             '( %s -> ( 1 + %s ) <_ ( exp ` %s ) )' % (A, l2, l2))
    lN3 = linarith(w, A, [ef2, bv, h200], '3 <_ %s' % lN, closure=cl)
    return lNrp, lN3, ef2, v2


# ------------------------------------------------------------------ sctmwin
def sctmwin():
    import importlib
    two_pow_le4 = importlib.import_module('t14_c_sc').two_pow_le4
    w = W('sctmwin', 'The machine scales lie in the analysis window at E = 1 / K, with the pool threshold within '
                     '( log n ) ^c 1.2 and 16 ( log n ) ^c 1.2, once ell2 n >= 200 and ell3 n >= 3 '
                     '(Lean: scalesTM_inWindow, pointwise).')
    A = STMTS14['sctmwin'].split(' -> ')[0][2:]
    pj = Proj(w, A)
    nuz = pj('N e. ( ZZ>= ` 3 )')
    nnn = w.s([nuz, w.inst('eluz3nn')], 'syl', '( %s -> N e. NN )' % A)
    cl = Closure(w, A, {'N': ('NN', nnn), 'C': [('NN0', pj('C e. NN0'))], 'K': ('NN', pj('K e. NN'))})
    c1000 = pj('; ; ; 1 0 0 0 <_ C')
    l2 = L2('N'); l3 = L3('N'); lN = LOG('N')
    h200 = pj('; ; 2 0 0 <_ %s' % l2); h3 = pj('3 <_ %s' % l3)
    lNrp, lN3, ef2, v2 = logn_facts(w, A, cl, nnn, nuz, h200, l2, lN)
    cl.have(l2, 'RR+', w.s([cl.mem(l2, 'RR'), linarith(w, A, [h200], '0 < %s' % l2, closure=cl)], 'elrpd',
                           '( %s -> %s e. RR+ )' % (A, l2)))
    v3 = w.s([cl.mem('N', 'NN0'), w.inst('ell3val')], 'syl', '( %s -> %s = ( log ` %s ) )' % (A, l3, l2))
    l3re = w.s([v3, cl.mem('( log ` %s )' % l2, 'RR')], 'eqeltrd', '( %s -> %s e. RR )' % (A, l3))
    cl.have(l3, 'RR', l3re); cl.atom(l3)
    WNA = WN('N')
    ab = w.s([pj(WNA), w.inst('sctmab')], 'syl', '( %s -> %s )' % (A, STMTS14['sctmab'].split(' -> ', 1)[1][:-2]))
    ab1, ab2, ab3 = [proj(w, A, ab, i) for i in range(3)]
    a1, a2 = proj(w, A, ab1, 0), proj(w, A, ab1, 1)
    b1, b2 = proj(w, A, ab2, 0), proj(w, A, ab2, 1)
    d1, d2 = proj(w, A, ab3, 0), proj(w, A, ab3, 1)
    LL, AA, BB = NL('N'), SCA_('N'), SCB_('N')
    for x in (LL, AA, BB):
        cl.atom(x)
    Z = SCZ_('C', 'N'); W9 = W99_(Z); Y = YK_(Z, 'K'); T = '( 3 x. %s )' % AA; X = '( %s + 1 )' % LL; TH = TH_(X)
    CM = '( ( C x. %s ) x. %s )' % (l2, l3)
    c0 = cl.ge0('C')
    # z bounds
    zl1 = w.s([cl.mem(l2, 'RR'), cl.mem(AA, 'RR'), cl.mem('C', 'RR'), c0, b1], 'lemul2ad',
              '( %s -> ( C x. %s ) <_ ( C x. %s ) )' % (A, l2, AA))
    l20 = linarith(w, A, [h200], '0 <_ %s' % l2, closure=cl); l30 = linarith(w, A, [h3], '0 <_ %s' % l3, closure=cl)
    cl2_0 = w.s([cl.mem('C', 'RR'), cl.mem(l2, 'RR'), c0, l20], 'mulge0d', '( %s -> 0 <_ ( C x. %s ) )' % (A, l2))
    zlo = w.s([cl.mem('( C x. %s )' % l2, 'RR'), cl.mem('( C x. %s )' % AA, 'RR'), cl.mem(l3, 'RR'), cl.mem(BB, 'RR'),
               cl2_0, l30, zl1, d1], 'lemul12ad', '( %s -> %s <_ %s )' % (A, CM, Z))
    q151 = '( ; ; 1 5 1 / ; ; 1 0 0 )'
    s1 = linarith(w, A, [b2, h200], '%s <_ ( %s x. %s )' % (AA, q151, l2), closure=cl)
    s2 = linarith(w, A, [d2, h3], '%s <_ ( 2 x. %s )' % (BB, l3), closure=cl)
    zh1 = w.s([cl.mem(AA, 'RR'), cl.mem('( %s x. %s )' % (q151, l2), 'RR'), cl.mem('C', 'RR'), c0, s1], 'lemul2ad',
              '( %s -> ( C x. %s ) <_ ( C x. ( %s x. %s ) ) )' % (A, AA, q151, l2))
    zh2 = w.s([cl.mem('( C x. %s )' % AA, 'RR'), cl.mem('( C x. ( %s x. %s ) )' % (q151, l2), 'RR'), cl.mem(BB, 'RR'),
               cl.mem('( 2 x. %s )' % l3, 'RR'), cl.ge0('( C x. %s )' % AA), cl.ge0(BB), zh1, s2], 'lemul12ad',
              '( %s -> %s <_ ( ( C x. ( %s x. %s ) ) x. ( 2 x. %s ) ) )' % (A, Z, q151, l2, l3))
    cm0 = w.s([cl.mem('( C x. %s )' % l2, 'RR'), cl.mem(l3, 'RR'), cl2_0, l30], 'mulge0d', '( %s -> 0 <_ %s )' % (A, CM))
    zhi = nlinarith(w, A, [zh2, cm0], '%s <_ ( 4 x. %s )' % (Z, CM), closure=cl)
    # z e. NN
    z1 = nlinarith(w, A, [zlo, c1000, h200, h3, cl2_0, l30], '1 <_ %s' % Z, closure=cl)
    cl.atom(Z)
    znn = w.s([w.s([cl.mem(Z, 'NN0'), z1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (A, Z, Z)),
               w.s([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (Z, Z, Z))], 'a1i',
                   '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) ) )' % (A, Z, Z, Z))], 'mpbird', '( %s -> %s e. NN )' % (A, Z))
    cl.have(Z, 'NN', znn)
    # w , y
    wv = w.s([znn, w.inst('sctmw')], 'syl', '( %s -> %s )' % (A, STMTS14['sctmw'].split(' -> ', 1)[1][:-2].replace('Z', '@').replace('@', Z)))
    wlo0, whi = proj(w, A, wv, 0), proj(w, A, wv, 1)
    zc = '( %s ^c %s )' % (Z, C99)
    cl.atom(zc); cl.atom(W9)
    zcre = w.s([cl.mem(Z, 'RR+'), cl.mem(C99, 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, zc))
    cl.have(zc, 'RR+', zcre)
    wlo = linarith(w, A, [wlo0], '%s <_ ( %s + 1 )' % (zc, W9), closure=cl)
    yv = use(w, A, 'sctmy', [znn, cl.mem('K', 'NN')],
             STMTS14['sctmy'].split(' -> ', 1)[1][:-2].replace('Z', '@').replace('@', Z))
    ylo, yhi = proj(w, A, yv, 0), proj(w, A, yv, 1)
    tlo = linarith(w, A, [b1], '( 3 x. %s ) <_ %s' % (l2, T), closure=cl)
    thi = linarith(w, A, [b2, h200], '%s <_ ( 5 x. %s )' % (T, l2), closure=cl)
    # theta
    xnn = cl.mem(X, 'NN')
    tv = w.s([xnn, w.inst('sctmth')], 'syl', '( %s -> %s )' % (A, STMTS14['sctmth'].split(' -> ', 1)[1][:-2].replace('X', '@').replace('@', X)))
    th1, th2 = proj(w, A, tv, 0), proj(w, A, tv, 1)
    xc = '( %s ^c %s )' % (X, C65); lc = '( %s ^c %s )' % (lN, C65); l2N = '( 2 x. %s )' % lN
    lx = linarith(w, A, [a1], '%s <_ %s' % (lN, X), closure=cl)
    c65re = cl.mem(C65, 'RR'); c650 = cl.ge0(C65)
    lNre = cl.mem(lN, 'RR'); lN0 = w.s([lNrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A, lN))
    p1 = use(w, A, 'cxple2a', [[lNre, cl.mem(X, 'RR'), c65re], [lN0, c650], lx], '%s <_ %s' % (lc, xc))
    x2 = linarith(w, A, [a2, lN3], '%s <_ %s' % (X, l2N), closure=cl)
    p2 = use(w, A, 'cxple2a', [[cl.mem(X, 'RR'), cl.mem(l2N, 'RR'), c65re], [cl.ge0(X), c650], x2],
             '%s <_ ( %s ^c %s )' % (xc, l2N, C65))
    mc = w.s([cl.mem('2', 'RR'), cl.ge0('2'), lNre, lN0, cl.mem(C65, 'CC')], 'mulcxpd',
             '( %s -> ( %s ^c %s ) = ( ( 2 ^c %s ) x. %s ) )' % (A, l2N, C65, C65, lc))
    t4 = two_pow_le4(w, A, cl, C65, linarith(w, A, [], '%s <_ 2' % C65, closure=cl))
    lc0 = w.s([w.s([lNrp, cl.mem(C65, 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, lc))], 'rpge0d', '( %s -> 0 <_ %s )' % (A, lc))
    for x in (xc, lc, TH, '( 2 ^c %s )' % C65, '( %s ^c %s )' % (l2N, C65)):
        cl.atom(x)
    cl.have(lc, 'RR', w.s([w.s([lNrp, cl.mem(C65, 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, lc))], 'rpred', '( %s -> %s e. RR )' % (A, lc)))
    cl.have(xc, 'RR', w.s([w.s([cl.mem(X, 'RR+'), cl.mem(C65, 'RR')], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A, xc))], 'rpred', '( %s -> %s e. RR )' % (A, xc)))
    cl.have('( %s ^c %s )' % (l2N, C65), 'RR', w.s([w.s([cl.mem(l2N, 'RR+'), cl.mem(C65, 'RR')], 'rpcxpcld',
            '( %s -> ( %s ^c %s ) e. RR+ )' % (A, l2N, C65))], 'rpred', '( %s -> ( %s ^c %s ) e. RR )' % (A, l2N, C65)))
    cl.have('( 2 ^c %s )' % C65, 'RR', w.s([w.s([cl.mem('2', 'RR+'), cl.mem(C65, 'RR')], 'rpcxpcld',
            '( %s -> ( 2 ^c %s ) e. RR+ )' % (A, C65))], 'rpred', '( %s -> ( 2 ^c %s ) e. RR )' % (A, C65)))
    thlo = w.s([cl.mem(lc, 'RR'), cl.mem(xc, 'RR'), cl.mem(TH, 'RR'), p1, th1], 'letrd', '( %s -> %s <_ %s )' % (A, lc, TH))
    thhi = nlinarith(w, A, [th2, p2, mc, t4, lc0], '%s <_ ( ; 1 6 x. %s )' % (TH, lc), closure=cl)
    # the tuple
    SCN = SC('C', 'K', 'N')
    IW = '<. <. %s , %s >. , <. %s , %s >. >.' % (Z, W9, Y, T)
    TUP = '<. %s , %s >.' % (IW, TH)
    sv = use(w, A, 'sctmval', [cl.mem('C', 'NN0'), cl.mem('K', 'NN'), cl.mem('N', 'NN0')], '%s = %s' % (SCN, TUP))
    RY = '( ( ( ( K - 1 ) x. %s ) + K ) - 1 )' % BZ_(Z)
    k1 = w.s([cl.mem('K', 'NN'), w.inst('nnge1')], 'syl', '( %s -> 1 <_ K )' % A)
    cl.atom(NL(Z))
    cl.have(RY, 'ge0', nlinarith(w, A, [k1, cl.ge0(BZ_(Z))], '0 <_ %s' % RY, closure=cl))
    wn0 = cl.mem(W9, 'NN0'); ynn = cl.mem(Y, 'NN'); tn0 = cl.mem(T, 'NN0'); thn0 = cl.mem(TH, 'NN0')
    o1 = use(w, A, 'opelxpi', [znn, wn0], '<. %s , %s >. e. ( NN X. NN0 )' % (Z, W9))
    o2 = use(w, A, 'opelxpi', [ynn, tn0], '<. %s , %s >. e. ( NN X. NN0 )' % (Y, T))
    o3 = use(w, A, 'opelxpi', [o1, o2], '%s e. ( ( NN X. NN0 ) X. ( NN X. NN0 ) )' % IW)
    o4 = use(w, A, 'opelxpi', [o3, thn0], '%s e. ( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 )' % TUP)
    dsc = w.s([w.s([], 'df-scales', 'Scales = ( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 )')], 'a1i',
              '( %s -> Scales = ( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 ) )' % A)
    o5 = w.s([o4, dsc], 'eleqtrrd', '( %s -> %s e. Scales )' % (A, TUP))
    msc = w.s([sv, o5], 'eqeltrd', '( %s -> %s e. Scales )' % (A, SCN))
    # InWindow at the explicit tuple
    ew = use(w, A, 'elinwin', [[cl.mem('C', 'RR'), cl.mem('( 1 / K )', 'RR'), cl.mem('N', 'NN0')],
                                [cl.mem(Z, 'NN0'), wn0], [cl.mem(Y, 'NN0'), tn0]],
             '( <. <. C , ( 1 / K ) >. , N >. InWindow %s <-> %s )' % (IW, WINBODY(Z, W9, Y, T)))
    body = cj(w, A, [cj(w, A, [cj(w, A, [zlo, zhi]), cj(w, A, [wlo, whi])]),
                     cj(w, A, [cj(w, A, [ylo, yhi]), cj(w, A, [tlo, thi])])])
    iw = w.s([body, ew], 'mpbird', '( %s -> <. <. C , ( 1 / K ) >. , N >. InWindow %s )' % (A, IW))
    e1 = w.s([sv], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (A, SCN, TUP))
    e2 = w.s([w.s([], 'opex', '%s e. _V' % IW), w.s([], 'ovex', '%s e. _V' % TH)], 'op1st', '( 1st ` %s ) = %s' % (TUP, IW))
    e3 = w.s([e1, w.s([e2], 'a1i', '( %s -> ( 1st ` %s ) = %s )' % (A, TUP, IW))], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (A, SCN, IW))
    iw2 = w.s([iw, e3], 'breqtrrd', '( %s -> <. <. C , ( 1 / K ) >. , N >. InWindow ( 1st ` %s ) )' % (A, SCN))
    f1 = w.s([sv], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (A, SCN, TUP))
    f2 = w.s([w.s([], 'opex', '%s e. _V' % IW), w.s([], 'ovex', '%s e. _V' % TH)], 'op2nd', '( 2nd ` %s ) = %s' % (TUP, TH))
    f3 = w.s([f1, w.s([f2], 'a1i', '( %s -> ( 2nd ` %s ) = %s )' % (A, TUP, TH))], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (A, SCN, TH))
    g1 = w.s([thlo, f3], 'breqtrrd', '( %s -> %s <_ ( 2nd ` %s ) )' % (A, lc, SCN))
    g2 = w.s([f3, thhi], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( ; 1 6 x. %s ) )' % (A, SCN, lc))
    w.qed([msc, cj(w, A, [iw2, cj(w, A, [g1, g2])])], 'jca', '( %s -> %s )' % (A, WIN('C', 'K', 'N')))
    return run(w)


def ev_n3(w):
    """|- E. m e. NN0 A. n e. ( ZZ>= ` m ) n e. ( ZZ>= ` 3 )"""
    U = 'n e. ( ZZ>= ` 3 )'
    rg = w.s([w.s([], 'id', '( %s -> %s )' % (U, U))], 'rgen', 'A. n e. ( ZZ>= ` 3 ) %s' % U)
    idm = w.s([], 'id', '( m = 3 -> m = 3 )')
    cg, new = w.wcongr('A. n e. ( ZZ>= ` m ) %s' % U, {'m': '3'}, 'm = 3', {'m': idm})
    assert new == 'A. n e. ( ZZ>= ` 3 ) %s' % U, new
    return w.s([w.s([], '3nn0', '3 e. NN0'), rg, w.s([cg], 'rspcev',
                '( ( 3 e. NN0 /\\ A. n e. ( ZZ>= ` 3 ) %s ) -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (U, U))],
               'mp2an', 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % U)


def evge(w, lab, lit_, f):
    """|- E. m e. NN0 A. n e. ( ZZ>= ` m ) lit <_ f ( n ) by ell2ge / ell3ge"""
    re = Closure(w, '1 = 1', {}).mem(lit_, 'RR')
    re2 = w.s([w.s([], 'eqid', '1 = 1'), re], 'ax-mp', '%s e. RR' % lit_)
    return w.s([re2, w.inst(lab)], 'ax-mp', 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s <_ %s' % (lit_, f))


EV = lambda P: 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % P


# ------------------------------------------------------------------ sctmwinev
def sctmwinev():
    w = W('sctmwinev', 'For n large the machine scales lie in the analysis window at E = 1 / K with the pool threshold '
                       'between ( log n ) ^c 1.2 and 16 ( log n ) ^c 1.2 (Lean: scalesTM_inWindow).')
    A = CK
    a, b, c = 'n e. ( ZZ>= ` 3 )', '; ; 2 0 0 <_ %s' % L2('n'), '3 <_ %s' % L3('n')
    e0 = ev_n3(w)
    e2 = evge(w, 'ell2ge', '; ; 2 0 0', L2('n'))
    e3 = evge(w, 'ell3ge', '3', L3('n'))
    ab = '( %s /\\ %s )' % (a, b); abc = '( %s /\\ %s )' % (ab, c)
    j1 = w.s([w.s([e0, e2], 'pm3.2i', '( %s /\\ %s )' % (EV(a), EV(b))), w.inst('extrwevan')], 'ax-mp', EV(ab))
    j2 = w.s([w.s([j1, e3], 'pm3.2i', '( %s /\\ %s )' % (EV(ab), EV(c))), w.inst('extrwevan')], 'ax-mp', EV(abc))
    WINn = WIN('C', 'K', 'n')
    t1 = w.s([], 'sctmwin', '( ( %s /\\ ( %s /\\ %s /\\ %s ) ) -> %s )' % (A, a, b, c, WINn))
    t2 = w.s([t1], 'ex', '( %s -> ( ( %s /\\ %s /\\ %s ) -> %s ) )' % (A, a, b, c, WINn))
    t3 = w.s([w.s([], 'df-3an', '( ( %s /\\ %s /\\ %s ) <-> %s )' % (a, b, c, abc))], 'biimpri',
             '( %s -> ( %s /\\ %s /\\ %s ) )' % (abc, a, b, c))
    t4 = w.s([t3, t2], 'syl5', '( %s -> ( %s -> %s ) )' % (A, abc, WINn))
    t5 = w.s([t4], 'adantr', '( ( %s /\\ n e. NN0 ) -> ( %s -> %s ) )' % (A, abc, WINn))
    t6 = w.s([t5], 'ralrimiva', '( %s -> A. n e. NN0 ( %s -> %s ) )' % (A, abc, WINn))
    j3 = w.s([w.s([j2], 'a1i', '( %s -> %s )' % (A, EV(abc))), t6], 'jca',
             '( %s -> ( %s /\\ A. n e. NN0 ( %s -> %s ) ) )' % (A, EV(abc), abc, WINn))
    w.qed([j3, w.inst('extrwevim')], 'syl', '( %s -> %s )' % (A, EV(WINn)))
    return run(w)


# ------------------------------------------------------------------ sctm16
def sctm16():
    w = W('sctm16', 'From n >= 16 on the machine scales are a tuple of Scales with 1 <_ z ( Nlog n >= 4 , '
                    'a = Nlog Nlog n >= 2 , b = Nlog a >= 1 ; the small inputs of route beta are n < 16 ).')
    A = STMTS14['sctm16'].split(' -> ')[0][2:]
    pj = Proj(w, A)
    nuz = pj('N e. ( ZZ>= ` ; 1 6 )')
    n16 = w.s([nuz, w.inst('eluzle')], 'syl', '( %s -> ; 1 6 <_ N )' % A)
    nz = w.s([nuz, w.inst('eluzelz')], 'syl', '( %s -> N e. ZZ )' % A)
    cl = Closure(w, A, {'N': ('ZZ', nz), 'C': ('NN0', pj('C e. NN0')), 'K': ('NN', pj('K e. NN'))})
    nnn = w.s([w.s([nz, linarith(w, A, [n16], '0 < N', closure=cl)], 'jca', '( %s -> ( N e. ZZ /\\ 0 < N ) )' % A),
               w.s([w.s([], 'elnnz', '( N e. NN <-> ( N e. ZZ /\\ 0 < N ) )')], 'a1i', '( %s -> ( N e. NN <-> ( N e. ZZ /\\ 0 < N ) ) )' % A)],
              'mpbird', '( %s -> N e. NN )' % A)
    cl.have('N', 'NN', nnn)
    tu = w.s([w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % A)

    def lb(X, xnn, i, p, pv, ple):
        """( A -> i <_ ( 2 Nlog X ) ) from 2 ^ i = pv <_ X"""
        e = w.s([w.s([], p, '( 2 ^ %s ) = %s' % (i, pv))], 'a1i', '( %s -> ( 2 ^ %s ) = %s )' % (A, i, pv))
        le = w.s([e, ple], 'eqbrtrd', '( %s -> ( 2 ^ %s ) <_ %s )' % (A, i, X))
        return use(w, A, 'nlogub', [[tu, xnn], [cl.mem(i, 'NN0'), le]], '%s <_ ( 2 Nlog %s )' % (i, X))
    LL, AA, BB = NL('N'), SCA_('N'), SCB_('N')
    l4 = lb('N', nnn, '4', '2exp4', '; 1 6', n16)
    cl.atom(LL)
    nat_nn(w, A, cl, LL, [l4])
    a2 = lb(LL, cl.mem(LL, 'NN'), '2', 'sq2', '4', l4)
    cl.atom(AA)
    nat_nn(w, A, cl, AA, [a2])
    e21 = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.inst('exp1')], 'ax-mp', '( 2 ^ 1 ) = 2')], 'a1i', '( %s -> ( 2 ^ 1 ) = 2 )' % A)
    le21 = w.s([e21, a2], 'eqbrtrd', '( %s -> ( 2 ^ 1 ) <_ %s )' % (A, AA))
    b1 = use(w, A, 'nlogub', [[tu, cl.mem(AA, 'NN')], [cl.mem('1', 'NN0'), le21]], '1 <_ %s' % BB)
    cl.atom(BB)
    Z = SCZ_('C', 'N'); W9 = W99_(Z); Y = YK_(Z, 'K'); T = '( 3 x. %s )' % AA; X = '( %s + 1 )' % LL; TH = TH_(X)
    c1 = pj('1 <_ C')
    z1 = nlinarith(w, A, [c1, a2, b1, cl.ge0('C')], '1 <_ %s' % Z, closure=cl)
    cl.atom(Z)
    znn = w.s([w.s([cl.mem(Z, 'NN0'), z1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (A, Z, Z)),
               w.s([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (Z, Z, Z))], 'a1i',
                   '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) ) )' % (A, Z, Z, Z))], 'mpbird', '( %s -> %s e. NN )' % (A, Z))
    cl.have(Z, 'NN', znn)
    RY = '( ( ( ( K - 1 ) x. %s ) + K ) - 1 )' % BZ_(Z)
    k1 = w.s([cl.mem('K', 'NN'), w.inst('nnge1')], 'syl', '( %s -> 1 <_ K )' % A)
    cl.atom(NL(Z))
    cl.have(RY, 'ge0', nlinarith(w, A, [k1, cl.ge0(BZ_(Z))], '0 <_ %s' % RY, closure=cl))
    wn0 = cl.mem(W9, 'NN0'); ynn = cl.mem(Y, 'NN'); tn0 = cl.mem(T, 'NN0'); thn0 = cl.mem(TH, 'NN0')
    SCN = SC('C', 'K', 'N')
    IW = '<. <. %s , %s >. , <. %s , %s >. >.' % (Z, W9, Y, T)
    TUP = '<. %s , %s >.' % (IW, TH)
    sv = use(w, A, 'sctmval', [cl.mem('C', 'NN0'), cl.mem('K', 'NN'), cl.mem('N', 'NN0')], '%s = %s' % (SCN, TUP))
    o1 = use(w, A, 'opelxpi', [znn, wn0], '<. %s , %s >. e. ( NN X. NN0 )' % (Z, W9))
    o2 = use(w, A, 'opelxpi', [ynn, tn0], '<. %s , %s >. e. ( NN X. NN0 )' % (Y, T))
    o3 = use(w, A, 'opelxpi', [o1, o2], '%s e. ( ( NN X. NN0 ) X. ( NN X. NN0 ) )' % IW)
    o4 = use(w, A, 'opelxpi', [o3, thn0], '%s e. ( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 )' % TUP)
    dsc = w.s([w.s([], 'df-scales', 'Scales = ( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 )')], 'a1i',
              '( %s -> Scales = ( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 ) )' % A)
    o5 = w.s([o4, dsc], 'eleqtrrd', '( %s -> %s e. Scales )' % (A, TUP))
    msc = w.s([sv, o5], 'eqeltrd', '( %s -> %s e. Scales )' % (A, SCN))
    # the first projection
    p1 = w.s([w.s([], 'opex', '%s e. _V' % IW), w.s([], 'ovex', '%s e. _V' % TH)], 'op1st', '( 1st ` %s ) = %s' % (TUP, IW))
    p2 = w.s([w.s([], 'opex', '<. %s , %s >. e. _V' % (Z, W9)), w.s([], 'opex', '<. %s , %s >. e. _V' % (Y, T))], 'op1st',
             '( 1st ` %s ) = <. %s , %s >.' % (IW, Z, W9))
    p3 = w.s([w.s([], 'ovex', '%s e. _V' % Z), w.s([], 'ovex', '%s e. _V' % W9)], 'op1st', '( 1st ` <. %s , %s >. ) = %s' % (Z, W9, Z))
    q1 = w.s([p1], 'fveq2i', '( 1st ` ( 1st ` %s ) ) = ( 1st ` %s )' % (TUP, IW))
    q2 = w.s([q1, p2], 'eqtri', '( 1st ` ( 1st ` %s ) ) = <. %s , %s >.' % (TUP, Z, W9))
    q3 = w.s([q2], 'fveq2i', '( 1st ` ( 1st ` ( 1st ` %s ) ) ) = ( 1st ` <. %s , %s >. )' % (TUP, Z, W9))
    q4 = w.s([q3, p3], 'eqtri', '( 1st ` ( 1st ` ( 1st ` %s ) ) ) = %s' % (TUP, Z))
    f1 = w.s([sv], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (A, SCN, TUP))
    f2 = w.s([f1], 'fveq2d', '( %s -> ( 1st ` ( 1st ` %s ) ) = ( 1st ` ( 1st ` %s ) ) )' % (A, SCN, TUP))
    f3 = w.s([f2], 'fveq2d', '( %s -> %s = ( 1st ` ( 1st ` ( 1st ` %s ) ) ) )' % (A, PZ(SCN), TUP))
    f4 = w.s([f3, w.s([q4], 'a1i', '( %s -> ( 1st ` ( 1st ` ( 1st ` %s ) ) ) = %s )' % (A, TUP, Z))], 'eqtrd',
             '( %s -> %s = %s )' % (A, PZ(SCN), Z))
    zz = w.s([z1, f4], 'breqtrrd', '( %s -> 1 <_ %s )' % (A, PZ(SCN)))
    w.qed([msc, zz], 'jca', '( %s -> ( %s e. Scales /\\ 1 <_ %s ) )' % (A, SCN, PZ(SCN)))
    return run(w)


def WINBODY(Z, W9, Y, T):
    t = STMTS_ELINWIN
    return t.replace('Z', '@Z').replace('W', '@W').replace('Y', '@Y').replace('T', '@T') \
        .replace('@Z', Z).replace('@W', W9).replace('@Y', Y).replace('@T', T)


STMTS_ELINWIN = ('( ( ( ( ( C x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) <_ Z /\\ Z <_ ( 4 x. ( ( C x. ( ell2 ` N ) ) x. ( ell3 ` N ) ) ) ) /\\ '
                 '( ( Z ^c ( ; 9 9 / ; ; 1 0 0 ) ) <_ ( W + 1 ) /\\ W <_ ( 4 x. ( Z ^c ( ; 9 9 / ; ; 1 0 0 ) ) ) ) ) /\\ '
                 '( ( ( Z ^c ( 1 - ( 1 / K ) ) ) <_ Y /\\ Y <_ ( 4 x. ( Z ^c ( 1 - ( 1 / K ) ) ) ) ) /\\ '
                 '( ( 3 x. ( ell2 ` N ) ) <_ T /\\ T <_ ( 5 x. ( ell2 ` N ) ) ) ) )')


if __name__ == '__main__':
    for f in (sctmab, sctmwin, sctmwinev, sctm16):
        if want(f.__name__):
            f()
