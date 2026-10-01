"""Sortie ZBV2, section 1 part A (continued): the chord bounds of the kernel
and the chord-slope facts (ZBV2-blueprint.md section 1.2).

bvchord   ( ( HYS /\\ ( K e. NN /\\ ( K + 1 ) <_ Y ) ) -> ( H(K+1) ELL(K) <_ G(K) - G(K+1) /\\ G(K) - G(K+1) <_ H(K) ELL(K) ) )
bvrlow    H(K+1) <_ R(K)        bvrfirst  R(K) <_ H(K)        bvrlast  CX(K+1) <_ R(K)
bvrmono   ( ( HYS /\\ ( K e. NN /\\ ( ( K + 1 ) + 1 ) <_ Y ) ) -> R(K+1) <_ R(K) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbv2lib import *

AK = '( %s /\\ %s )' % (HYS, HK('K'))


def base(w, A):
    """the standing facts under A = ( HYS /\\ HK(K) ) (or any A whose second conjunct starts with K e. NN)"""
    st = mkst(w, A)
    hys = st([], 'simpl', HYS)
    ys = ysfacts(w, A, hys)
    knn = st([], 'simprl', 'K e. NN')
    kf = kfacts(w, A, knn, 'K')
    return st, hys, ys, knn, kf


def gcl(w, A, ys, krp, k):
    c = cxfacts(w, A, krp, ys['ner'], k)
    lg = lgfacts(w, A, ys['yrp'], krp, k)
    st = mkst(w, A)
    gr = st([c['re'], lg['re']], 'remulcld', '%s e. RR' % G(k))
    hr = st([c['re'], st([st([], '1red', '1 e. RR'), st([ys['er'], lg['re']], 'remulcld', '( %s x. %s ) e. RR' % (E, LG(k)))], 'readdcld',
                                '( 1 + ( %s x. %s ) ) e. RR' % (E, LG(k)))], 'remulcld', '%s e. RR' % H(k))
    return dict(c=c, lg=lg, gr=gr, gc=st([gr], 'recnd', '%s e. CC' % G(k)), hr=hr)


def dfacts(w, A, ys, kf):
    """G(K), G(K+1), H(K), H(K+1), D = G(K) - G(K+1), ELL(K), R(K) closures"""
    st = mkst(w, A)
    g0 = gcl(w, A, ys, kf['rp'], 'K'); g1 = gcl(w, A, ys, kf['p1rp'], P1('K'))
    el = ellfacts(w, A, kf, 'K')
    D = '( %s - %s )' % (G('K'), G(P1('K')))
    dr = st([g0['gr'], g1['gr']], 'resubcld', '%s e. RR' % D)
    rr = st([dr, el['rp']], 'rerpdivcld', '%s e. RR' % R('K'))
    return g0, g1, el, D, dr, rr


def bvchord():
    w = W('bvchord', 'The chord bounds of the kernel g ( x ) = x ^c -u E log ( Y / x ) between consecutive '
                     'integers: h ( K + 1 ) l ( K ) <= g ( K ) - g ( K + 1 ) <= h ( K ) l ( K ), with '
                     'h ( x ) = x ^c -u E ( 1 + E log ( Y / x ) ) and l ( K ) = log ( ( K + 1 ) / K ).')
    A = AK
    st, hys, ys, knn, kf = base(w, A)
    k1y = st([], 'simprr', '( K + 1 ) <_ Y')
    g0, g1, el, D, dr, rr = dfacts(w, A, ys, kf)
    c, cK = g0['c'], CX('K')
    s, u = LG('K'), ELL('K')
    X = '( %s x. %s )' % (E, u)
    q = '( exp ` -u %s )' % X
    xr = st([ys['er'], el['re']], 'remulcld', '%s e. RR' % X)
    x0 = st([ys['er'], el['re'], ys['e0'], st([el['rp']], 'rpge0d', '0 <_ %s' % u)], 'mulge0d', '0 <_ %s' % X)
    qrp = st([st([xr], 'renegcld', '-u %s e. RR' % X)], 'rpefcld', '%s e. RR+' % q)
    qr = st([qrp], 'rpred', '%s e. RR' % q); qc = st([qr], 'recnd', '%s e. CC' % q); q0 = st([qrp], 'rpge0d', '0 <_ %s' % q)
    p1 = sy2(w, A, xr, x0, 'bvexpl1', '( 1 - %s ) <_ %s' % (q, X))
    p2 = sy2(w, A, xr, x0, 'bvexpl2', '( %s x. %s ) <_ ( 1 - %s )' % (q, X, q))
    # s - u = log ( Y / ( K + 1 ) )
    ly = st([ys['yrp']], 'relogcld', '( log ` Y ) e. RR'); lk = st([kf['rp']], 'relogcld', '( log ` K ) e. RR'); lk1 = st([kf['p1rp']], 'relogcld', '( log ` ( K + 1 ) ) e. RR')
    d1 = sy2(w, A, ys['yrp'], kf['rp'], 'relogdiv', '%s = ( ( log ` Y ) - ( log ` K ) )' % s)
    d2 = sy2(w, A, ys['yrp'], kf['p1rp'], 'relogdiv', '%s = ( ( log ` Y ) - ( log ` ( K + 1 ) ) )' % LG(P1('K')))
    d3 = sy2(w, A, kf['p1rp'], kf['rp'], 'relogdiv', '%s = ( ( log ` ( K + 1 ) ) - ( log ` K ) )' % u)
    SMU = '( %s - %s )' % (s, u)
    smu = lineq(w, A, LG(P1('K')), SMU, hyps=[d1, d2, d3],
                leaves={LG(P1('K')): g1['lg']['re'], s: g0['lg']['re'], u: el['re'], '( log ` Y )': ly, '( log ` K )': lk, '( log ` ( K + 1 ) )': lk1})
    # u <_ s
    qq = st([kf['p1re'], ys['yr'], kf['rp'], k1y], 'lediv1dd', '( ( K + 1 ) / K ) <_ ( Y / K )')
    bi = sy2(w, A, el['qrp'], g0['lg']['qrp'], 'logleb', '( ( ( K + 1 ) / K ) <_ ( Y / K ) <-> %s <_ %s )' % (u, s))
    uls = st([qq, bi], 'mpbid', '%s <_ %s' % (u, s))
    # the certificate lemmas' antecedent
    QH = '( %s e. RR /\\ 0 <_ %s )' % (q, q); EH = '( %s e. RR /\\ 0 <_ %s )' % (E, E); UH = '( %s e. RR /\\ 0 <_ %s )' % (u, u)
    trip = bind3(w, A, bind(w, A, qr, q0, '%s e. RR' % q, '0 <_ %s' % q), bind(w, A, ys['er'], ys['e0'], '%s e. RR' % E, '0 <_ %s' % E),
                 bind(w, A, el['re'], st([el['rp']], 'rpge0d', '0 <_ %s' % u), '%s e. RR' % u, '0 <_ %s' % u), QH, EH, UH)
    TH = '( %s e. RR /\\ %s <_ %s )' % (s, u, s)
    H56 = '( ( 1 - %s ) <_ %s /\\ ( %s x. %s ) <_ ( 1 - %s ) )' % (q, X, q, X, q)
    rest = bind(w, A, bind(w, A, g0['lg']['re'], uls, '%s e. RR' % s, '%s <_ %s' % (u, s)), bind(w, A, p1, p2, '( 1 - %s ) <_ %s' % (q, X), '( %s x. %s ) <_ ( 1 - %s )' % (q, X, q)), TH, H56)
    ant = bind(w, A, trip, rest, '( %s /\\ %s /\\ %s )' % (QH, EH, UH), '( %s /\\ %s )' % (TH, H56))
    AA = '( 1 + ( %s x. %s ) )' % (E, SMU)
    LHS2 = '( ( %s x. %s ) x. %s )' % (q, AA, u); RHS2 = '( %s - ( %s x. %s ) )' % (s, q, SMU)
    BB = '( 1 + ( %s x. %s ) )' % (E, s); RHS3 = '( %s x. %s )' % (BB, u)
    L2 = st([ant, w.inst('bvchordlem2')], 'syl', '%s <_ %s' % (LHS2, RHS2))
    L3 = st([ant, w.inst('bvchordlem3')], 'syl', '%s <_ %s' % (RHS2, RHS3))
    # closures
    smur = st([g0['lg']['re'], el['re']], 'resubcld', '%s e. RR' % SMU); smuc = st([smur], 'recnd', '%s e. CC' % SMU)
    aar = st([st([], '1red', '1 e. RR'), st([ys['er'], smur], 'remulcld', '( %s x. %s ) e. RR' % (E, SMU))], 'readdcld', '%s e. RR' % AA); aac = st([aar], 'recnd', '%s e. CC' % AA)
    qaar = st([qr, aar], 'remulcld', '( %s x. %s ) e. RR' % (q, AA)); qaac = st([qaar], 'recnd', '( %s x. %s ) e. CC' % (q, AA))
    lhs2r = st([qaar, el['re']], 'remulcld', '%s e. RR' % LHS2)
    qsmr = st([qr, smur], 'remulcld', '( %s x. %s ) e. RR' % (q, SMU)); qsmc = st([qsmr], 'recnd', '( %s x. %s ) e. CC' % (q, SMU))
    rhs2r = st([g0['lg']['re'], qsmr], 'resubcld', '%s e. RR' % RHS2); rhs2c = st([rhs2r], 'recnd', '%s e. CC' % RHS2)
    bbr = st([st([], '1red', '1 e. RR'), st([ys['er'], g0['lg']['re']], 'remulcld', '( %s x. %s ) e. RR' % (E, s))], 'readdcld', '%s e. RR' % BB); bbc = st([bbr], 'recnd', '%s e. CC' % BB)
    rhs3r = st([bbr, el['re']], 'remulcld', '%s e. RR' % RHS3)
    M2 = st([lhs2r, rhs2r, c['re'], c['ge0'], L2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (cK, LHS2, cK, RHS2))
    M3 = st([rhs2r, rhs3r, c['re'], c['ge0'], L3], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (cK, RHS2, cK, RHS3))
    # the three identities
    hs = st([hys], 'simprd', HS)
    e4 = sy2(w, A, hs, knn, 'bvchordlem4', '%s = ( %s x. %s )' % (CX(P1('K')), cK, q))
    rules = {CX(P1('K')): ('( %s x. %s )' % (cK, q), e4), LG(P1('K')): (SMU, smu)}
    r1, t1 = w.rewrite('( %s x. %s )' % (H(P1('K')), u), rules, A)
    assert t1 == '( ( ( %s x. %s ) x. %s ) x. %s )' % (cK, q, AA, u), t1
    m1 = st([st([c['cc'], qc, aac], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (cK, q, AA, cK, q, AA))], 'oveq1d',
            '%s = ( ( %s x. ( %s x. %s ) ) x. %s )' % (t1, cK, q, AA, u))
    m2 = st([c['cc'], qaac, el['cc']], 'mulassd', '( ( %s x. ( %s x. %s ) ) x. %s ) = ( %s x. %s )' % (cK, q, AA, u, cK, LHS2))
    I1 = eqtr(w, A, [r1, m1, m2], None)
    r2, t2 = w.rewrite(G(P1('K')), rules, A)
    assert t2 == '( ( %s x. %s ) x. %s )' % (cK, q, SMU), t2
    m3 = st([c['cc'], qc, smuc], 'mulassd', '%s = ( %s x. ( %s x. %s ) )' % (t2, cK, q, SMU))
    g1eq = eqtr(w, A, [r2, m3], None)
    sub = st([c['cc'], g0['lg']['cc'], qsmc], 'subdid', '( %s x. %s ) = ( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) )' % (cK, RHS2, cK, s, cK, q, SMU))
    I2 = st([st([g1eq], 'oveq2d', '%s = ( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) )' % (D, cK, s, cK, q, SMU)), st([sub], 'eqcomd', '( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) ) = ( %s x. %s )' % (cK, s, cK, q, SMU, cK, RHS2))], 'eqtrd',
            '%s = ( %s x. %s )' % (D, cK, RHS2))
    I3 = st([c['cc'], bbc, el['cc']], 'mulassd', '( %s x. %s ) = ( %s x. %s )' % (H('K'), u, cK, RHS3))
    left = st([st([I1, M2], 'eqbrtrd', '( %s x. %s ) <_ ( %s x. %s )' % (H(P1('K')), u, cK, RHS2)), I2], 'breqtrrd', CHORD_L)
    right = st([st([I2, M3], 'eqbrtrd', '%s <_ ( %s x. %s )' % (D, cK, RHS3)), I3], 'breqtrrd', CHORD_R)
    w.qed([left, right], 'jca', '( %s -> ( %s /\\ %s ) )' % (A, CHORD_L, CHORD_R))
    return w


def bvrlow():
    w = W('bvrlow', 'The chord slope against log x is at least h ( K + 1 ) (bvchord, left).')
    A = AK
    st, hys, ys, knn, kf = base(w, A)
    g0, g1, el, D, dr, rr = dfacts(w, A, ys, kf)
    ch = st([], 'bvchord', '( %s /\\ %s )' % (CHORD_L, CHORD_R))
    left = st([ch], 'simpld', CHORD_L)
    bi = st([g1['hr'], dr, el['rp']], 'lemuldivd', '( ( %s x. %s ) <_ %s <-> %s <_ %s )' % (H(P1('K')), ELL('K'), D, H(P1('K')), R('K')))
    w.qed([left, bi], 'mpbid', '( %s -> %s <_ %s )' % (A, H(P1('K')), R('K')))
    return w


def bvrfirst():
    w = W('bvrfirst', 'The chord slope against log x is at most h ( K ) (bvchord, right).')
    A = AK
    st, hys, ys, knn, kf = base(w, A)
    g0, g1, el, D, dr, rr = dfacts(w, A, ys, kf)
    ch = st([], 'bvchord', '( %s /\\ %s )' % (CHORD_L, CHORD_R))
    right = st([ch], 'simprd', CHORD_R)
    bi = st([dr, g0['hr'], el['rp']], 'ledivmul2d', '( %s <_ %s <-> %s <_ ( %s x. %s ) )' % (R('K'), H('K'), D, H('K'), ELL('K')))
    w.qed([right, bi], 'mpbird', '( %s -> %s <_ %s )' % (A, R('K'), H('K')))
    return w


def bvrlast():
    w = W('bvrlast', 'The chord slope is at least ( K + 1 ) ^c -u E: h ( K + 1 ) >= ( K + 1 ) ^c -u E '
                     'since log ( Y / ( K + 1 ) ) >= 0 (bvrlow).')
    A = AK
    st, hys, ys, knn, kf = base(w, A)
    k1y = st([], 'simprr', '( K + 1 ) <_ Y')
    g0, g1, el, D, dr, rr = dfacts(w, A, ys, kf)
    low = st([], 'bvrlow', '%s <_ %s' % (H(P1('K')), R('K')))
    Qv = '( Y / ( K + 1 ) )'
    one = st([], '1red', '1 e. RR')
    bi = st([one, ys['yr'], kf['p1rp']], 'lemuldivd', '( ( 1 x. ( K + 1 ) ) <_ Y <-> 1 <_ %s )' % Qv)
    q1 = st([st([st([kf['p1cc']], 'mullidd', '( 1 x. ( K + 1 ) ) = ( K + 1 )'), k1y], 'eqbrtrd', '( 1 x. ( K + 1 ) ) <_ Y'), bi], 'mpbid', '1 <_ %s' % Qv)
    lg0 = sy2(w, A, st([g1['lg']['qrp']], 'rpred', '%s e. RR' % Qv), q1, 'logge0', '0 <_ %s' % LG(P1('K')))
    elg = st([ys['er'], g1['lg']['re']], 'remulcld', '( %s x. %s ) e. RR' % (E, LG(P1('K'))))
    elg0 = st([ys['er'], g1['lg']['re'], ys['e0'], lg0], 'mulge0d', '0 <_ ( %s x. %s )' % (E, LG(P1('K'))))
    BB = '( 1 + ( %s x. %s ) )' % (E, LG(P1('K')))
    bbr = st([one, elg], 'readdcld', '%s e. RR' % BB)
    b1 = linarith(w, A, [elg0], '1 <_ %s' % BB, leaves={'( %s x. %s )' % (E, LG(P1('K'))): elg})
    c1 = g1['c']
    m = st([one, bbr, c1['re'], c1['ge0'], b1], 'lemul2ad', '( %s x. 1 ) <_ ( %s x. %s )' % (CX(P1('K')), CX(P1('K')), BB))
    m2 = st([st([st([c1['cc']], 'mulridd', '( %s x. 1 ) = %s' % (CX(P1('K')), CX(P1('K'))))], 'eqcomd', '%s = ( %s x. 1 )' % (CX(P1('K')), CX(P1('K')))), m], 'eqbrtrd',
            '%s <_ %s' % (CX(P1('K')), H(P1('K'))))
    w.qed([c1['re'], g1['hr'], rr, m2, low], 'letrd', '( %s -> %s <_ %s )' % (A, CX(P1('K')), R('K')))
    return w


def bvrmono():
    w = W('bvrmono', 'The chord slopes decrease: r ( K + 1 ) <= h ( K + 1 ) <= r ( K ) (bvrfirst, bvrlow).')
    A = '( %s /\\ %s )' % (HYS, HK2('K'))
    st, hys, ys, knn, kf = base(w, A)
    k2y = st([], 'simprr', '( ( K + 1 ) + 1 ) <_ Y')
    k1y = linarith(w, A, [k2y], '( K + 1 ) <_ Y', leaves={'K': kf['re'], 'Y': ys['yr']})
    a1 = bind(w, A, hys, bind(w, A, knn, k1y, 'K e. NN', '( K + 1 ) <_ Y'), HYS, HK('K'))
    a2 = bind(w, A, hys, bind(w, A, kf['p1nn'], k2y, '( K + 1 ) e. NN', '( ( K + 1 ) + 1 ) <_ Y'), HYS, HK(P1('K')))
    low = st([a1, w.inst('bvrlow')], 'syl', '%s <_ %s' % (H(P1('K')), R('K')))
    first = st([a2, w.inst('bvrfirst')], 'syl', '%s <_ %s' % (R(P1('K')), H(P1('K'))))
    g0, g1, el, D, dr, rr = dfacts(w, A, ys, kf)
    # R(K+1) real
    kf1 = kfacts(w, A, kf['p1nn'], P1('K'))
    g2 = gcl(w, A, ys, kf1['p1rp'], P1(P1('K')))
    el1 = ellfacts(w, A, kf1, P1('K'))
    d1r = st([g1['gr'], g2['gr']], 'resubcld', '( %s - %s ) e. RR' % (G(P1('K')), G(P1(P1('K')))))
    r1r = st([d1r, el1['rp']], 'rerpdivcld', '%s e. RR' % R(P1('K')))
    w.qed([r1r, g1['hr'], rr, first, low], 'letrd', '( %s -> %s <_ %s )' % (A, R(P1('K')), R('K')))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvchord', 'bvrlow', 'bvrfirst', 'bvrlast', 'bvrmono']:
        globals()[f]().run()
