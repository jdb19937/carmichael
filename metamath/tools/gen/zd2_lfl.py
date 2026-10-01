"""Sortie ZD2: THE FROZEN OUTPUT zd2lfl = ( LOGGED -> LOGFREE ) (Lean logfree_of_logged), texts of tools/zdilib.py verbatim."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from zd2_base import *
from t21alib import LOGFREE, LOGGED, LFD_BODY, LGD_BODY, NCo, ZFo

LGB = lambda cc: ('( ( ( h e. RR /\\ w e. RR /\\ %s e. RR ) /\\ k e. NN0 ) /\\ ( ( 1 <_ h /\\ 0 <_ w /\\ w <_ ( 7 / 2 ) ) /\\ ( 1 <_ %s /\\ %s <_ ( 5 / 4 ) ) ) /\\ A. m e. NN %s )'
                  % (cc, cc, cc, LGD_BODY('h', 'w', cc, 'k', 'm')))
LFB = lambda g, cc: '( ( %s e. RR /\\ %s e. RR ) /\\ ( 1 <_ %s /\\ 1 <_ %s /\\ %s <_ 2 ) /\\ A. m e. NN %s )' % (g, cc, g, cc, cc, LFD_BODY(g, cc, 'm'))
assert LOGGED == 'E. h E. w E. c E. k %s' % LGB('c'), LOGGED[:120]
assert LOGFREE == 'E. g E. c %s' % LFB('g', 'c'), LOGFREE[:120]
MATM = S['zd2thm'][len('E. a E. b '):]
MATZ = S['zd2tz'][len('E. d '):]
SUBP = {'N': 'm', 'T': 'v', 'S': 'u', 'H': 'h', 'W': 'w', 'C': 'e', 'K': 'k', 'G': 'a', 'E': 'b', 'Z': 'd'}


def nco_eq(w, m, u, v):
    """closed step: NCo(u, v, m) (letters y p o) = NC(m, u, v) (letters x q r)"""
    DBm = '( Base ` ( DChr ` %s ) )' % m
    EXy = '( %s DChrLF y )' % m
    ZFo_ = ZFo(u, v, m)
    ZFr_y = '{ r e. %s | ( r =/= 1 /\\ ( %s ` r ) = 0 ) }' % (BOX(u, v), EXy)
    idf = lambda a, b: w.s([], 'id', '( %s = %s -> %s = %s )' % (a, b, a, b))
    st1, _ = w.wcongr('( o =/= 1 /\\ ( %s ` o ) = 0 )' % EXy, {'o': 'r'}, 'o = r', {'o': idf('o', 'r')})
    e1 = w.s([st1], 'cbvrabv', '%s = %s' % (ZFo_, ZFr_y))
    st2, _ = w.congr('( %s holord p )' % EXy, {'p': 'q'}, 'p = q', {'p': idf('p', 'q')})
    SO = 'sum_ p e. %s ( %s holord p )' % (ZFo_, EXy)
    SQ_ = 'sum_ q e. %s ( %s holord q )' % (ZFo_, EXy)
    SR = 'sum_ q e. %s ( %s holord q )' % (ZFr_y, EXy)
    e2 = w.s([st2], 'cbvsumv', '%s = %s' % (SO, SQ_))
    e2b = w.s([e1], 'sumeq1i', '%s = %s' % (SQ_, SR))
    e2c = w.s([e2, e2b], 'eqtri', '%s = %s' % (SO, SR))
    NCO = NCo(u, v, m)
    assert NCO == 'sum_ y e. %s %s' % (DBm, SO), NCO[:200]
    e3 = w.s([w.s([e2c], 'a1i', '( y e. %s -> %s = %s )' % (DBm, SO, SR))], 'sumeq2i', '%s = sum_ y e. %s %s' % (NCO, DBm, SR))
    st4, new4 = w.congr(SR, {'y': 'x'}, 'y = x', {'y': idf('y', 'x')})
    NCX = NC(m, u, v)
    assert 'sum_ x e. %s %s' % (DBm, new4) == NCX, new4[:200]
    e4 = w.s([st4], 'cbvsumv', 'sum_ y e. %s %s = %s' % (DBm, SR, NCX))
    return w.s([e3, e4], 'eqtri', '%s = %s' % (NCO, NCX))


def gam2_facts(w, A, c, hr, h1, kn, ar, a0, br, dr, d1):
    """GAM2' e. RR and 1 <_ GAM2' under A (letters a b d h k)"""
    G2 = tsub(GAM2, SUBP)
    PK = '( ( %s x. ( k + 1 ) ) ^ k )' % N400
    kr = c([kn], 'nn0red', 'k e. RR')
    base = c([numst(w, A, N400, 'RR'), c([kr, numst(w, A, '1', 'RR')], 'readdcld', '( k + 1 ) e. RR')], 'remulcld', '( %s x. ( k + 1 ) ) e. RR' % N400)
    pkr = c([base, kn], 'reexpcld', '%s e. RR' % PK)
    pk0 = c([base, kn, lin8(w, A, [c([kn], 'nn0ge0d', '0 <_ k')], '0 <_ ( %s x. ( k + 1 ) )' % N400, {'k': kr})], 'expge0d', '0 <_ %s' % PK)
    HPK = '( h x. %s )' % PK
    hpkr = c([hr, pkr], 'remulcld', '%s e. RR' % HPK); hpk0 = c([hr, pkr, lin8(w, A, [h1], '0 <_ h', {'h': hr}), pk0], 'mulge0d', '0 <_ %s' % HPK)
    B2 = '( b ^ 2 )'
    b2r = c([br], 'resqcld', '%s e. RR' % B2); b20 = c([br], 'sqge0d', '0 <_ %s' % B2)
    g2r = c([c([c([numst(w, A, '2', 'RR'), c([ar, dr], 'readdcld', '( a + d ) e. RR')], 'remulcld', '( 2 x. ( a + d ) ) e. RR'), c([numst(w, A, N6400, 'RR'), b2r], 'remulcld', '( %s x. %s ) e. RR' % (N6400, B2))], 'readdcld', '( ( 2 x. ( a + d ) ) + ( %s x. %s ) ) e. RR' % (N6400, B2)),
             c([hpkr, numst(w, A, '1', 'RR')], 'readdcld', '( %s + 1 ) e. RR' % HPK)], 'readdcld', '%s e. RR' % G2)
    g21 = lin8(w, A, [a0, d1, b20, hpk0], '1 <_ %s' % G2, {'a': ar, 'd': dr, B2: b2r, HPK: hpkr})
    return G2, g2r, g21


def gen_lfl():
    w = W('zd2lfl', 'THE FROZEN OUTPUT, Theorem A (Lean ` logfree_of_logged ` , unconditional): the logged density ` LoggedDensity ` implies the log-free density ` LogFreeDensity ` , the two DensityInterface texts of tools/zdilib.py verbatim ( ~ zd2thm , ~ zd2tz , ~ zd2pt at every modulus, height and abscissa).')
    LGBe = LGB('e')
    A0 = '( ( %s /\\ %s ) /\\ %s )' % (LGBe, MATM, MATZ)
    c = Ctx(w, A0)
    hr, wr, er, kn, h1, w0, w72, e1, e54 = [c.g(x) for x in ('h e. RR', 'w e. RR', 'e e. RR', 'k e. NN0', '1 <_ h', '0 <_ w', 'w <_ ( 7 / 2 )', '1 <_ e', 'e <_ ( 5 / 4 )')]
    lgd = c.g('A. m e. NN %s' % LGD_BODY('h', 'w', 'e', 'k', 'm'))
    ar, a0, br, b1 = [c.g(x) for x in ('a e. RR', '0 <_ a', 'b e. RR', '1 <_ b')]
    mm = c.g('A. n e. NN A. t e. RR A. s e. RR %s' % MBODY('n', 't', 's'))
    dr, d1 = c.g('d e. RR'), c.g('1 <_ d')
    mz = c.g('A. n e. NN A. t e. RR A. s e. RR %s' % ZBODY('n', 't', 's'))
    PT = '( 2 <_ v /\\ ( 9 / ; 1 0 ) <_ u /\\ u <_ 1 )'
    assert LFD_BODY('g', 'e', 'm').startswith('A. v e. RR A. u e. RR ( %s -> ' % PT), LFD_BODY('g', 'e', 'm')[:200]
    A3 = '( ( ( %s /\\ m e. NN ) /\\ v e. RR ) /\\ u e. RR )' % A0
    A4 = '( %s /\\ %s )' % (A3, PT)
    c4 = Ctx(w, A4)
    L4 = lambda st: lift(w, st, A4)
    mn, vr, ur = c4.g('m e. NN'), c4.g('v e. RR'), c4.g('u e. RR')
    v2, u910, u1 = c4.g('2 <_ v'), c4.g('( 9 / ; 1 0 ) <_ u'), c4.g('u <_ 1')
    # the logged bound at ( m , v , u ) by rspa
    LG3 = LGD_BODY('h', 'w', 'e', 'k', 'm')
    LG2 = LG3[len('A. v e. RR '):]; LG1 = LG2[len('A. u e. RR '):]
    assert LG3 == 'A. v e. RR A. u e. RR %s' % LG1, LG3[:100]
    l1 = c4([L4(lgd), mn, w.s([], 'rspa', '( ( A. m e. NN %s /\\ m e. NN ) -> %s )' % (LG3, LG3))], 'syl2anc', LG3)
    l2 = c4([l1, vr, w.s([], 'rspa', '( ( %s /\\ v e. RR ) -> %s )' % (LG3, LG2))], 'syl2anc', LG2)
    l3 = c4([l2, ur, w.s([], 'rspa', '( ( %s /\\ u e. RR ) -> %s )' % (LG2, LG1))], 'syl2anc', LG1)
    # Theorem M and Z at ( m , v , u ) by substitution
    idf = lambda x_, y_: w.s([], 'id', '( %s = %s -> %s = %s )' % (x_, y_, x_, y_))
    def spec3(al, body_n, sub_n_names):
        # al : ( A4 -> A. n e. NN A. t e. RR A. s e. RR body ) -> body[m,v,u]
        bn = 'A. t e. RR A. s e. RR %s' % body_n
        s1, n1 = ral_at(w, A4, al, 'n', 'm', bn, mn)
        bt = n1[len('A. t e. RR '):]
        s2, n2 = ral_at(w, A4, s1, 't', 'v', bt, vr)
        bs = n2[len('A. s e. RR '):]
        s3, n3 = ral_at(w, A4, s2, 's', 'u', bs, ur)
        return s3, n3
    hm, hmt = spec3(L4(mm), MBODY('n', 't', 's'), None)
    hz, hzt = spec3(L4(mz), ZBODY('n', 't', 's'), None)
    assert hmt == tsub(MBODY('m', 'v', 'u'), {}), hmt[:200]
    # NCo = NC (closed) and the logged bound in the letters x q r
    eq = nco_eq(w, 'm', 'u', 'v')
    NCO = NCo('u', 'v', 'm'); NCX = NC('m', 'u', 'v')
    RH = LG1.split(' -> ', 1)[1][:-2]
    assert RH.startswith(NCO + ' <_ '), RH[:200]
    RHS_H = RH[len(NCO + ' <_ '):]
    COND = LG1.split(' -> ', 1)[0][2:]
    bi = w.s([w.s([eq], 'breq1i', '( %s <_ %s <-> %s <_ %s )' % (NCO, RHS_H, NCX, RHS_H))], 'imbi2i', '( ( %s -> %s <_ %s ) <-> ( %s -> %s <_ %s ) )' % (COND, NCO, RHS_H, COND, NCX, RHS_H))
    hh = c4([l3, c4.a1(bi, formula_of(w, bi))], 'mpbid', '( %s -> %s <_ %s )' % (COND, NCX, RHS_H))
    PTX = tsub(S['zd2pt'], SUBP)
    pta, ptc = ante_of(PTX)
    CSTx = tsub(CST, SUBP); PTHx = tsub(PTH, SUBP)
    cst = c4([c4([c4([L4(hr), L4(h1)], 'jca', '( h e. RR /\\ 1 <_ h )'), c4([L4(wr), L4(w0), L4(w72)], '3jca', '( w e. RR /\\ 0 <_ w /\\ w <_ ( 7 / 2 ) )')], 'jca', '( ( h e. RR /\\ 1 <_ h ) /\\ ( w e. RR /\\ 0 <_ w /\\ w <_ ( 7 / 2 ) ) )'),
              c4([c4([L4(er), L4(e1), L4(e54)], '3jca', '( e e. RR /\\ 1 <_ e /\\ e <_ ( 5 / 4 ) )'), L4(kn)], 'jca', '( ( e e. RR /\\ 1 <_ e /\\ e <_ ( 5 / 4 ) ) /\\ k e. NN0 )')], 'jca',
             '( ( ( h e. RR /\\ 1 <_ h ) /\\ ( w e. RR /\\ 0 <_ w /\\ w <_ ( 7 / 2 ) ) ) /\\ ( ( e e. RR /\\ 1 <_ e /\\ e <_ ( 5 / 4 ) ) /\\ k e. NN0 ) )')
    cst2 = c4([c4([L4(ar), L4(a0)], 'jca', '( a e. RR /\\ 0 <_ a )'), c4([c4([L4(br), L4(b1)], 'jca', '( b e. RR /\\ 1 <_ b )'), c4([L4(dr), L4(d1)], 'jca', '( d e. RR /\\ 1 <_ d )')], 'jca', '( ( b e. RR /\\ 1 <_ b ) /\\ ( d e. RR /\\ 1 <_ d ) )')], 'jca',
              '( ( a e. RR /\\ 0 <_ a ) /\\ ( ( b e. RR /\\ 1 <_ b ) /\\ ( d e. RR /\\ 1 <_ d ) ) )')
    cstall = c4([cst, cst2], 'jca', CSTx)
    pth = c4([mn, c4([c4([vr, v2], 'jca', '( v e. RR /\\ 2 <_ v )'), c4([ur, c4([u910, u1], 'jca', '( ( 9 / ; 1 0 ) <_ u /\\ u <_ 1 )')], 'jca', '( u e. RR /\\ ( ( 9 / ; 1 0 ) <_ u /\\ u <_ 1 ) )')], 'jca', '( ( v e. RR /\\ 2 <_ v ) /\\ ( u e. RR /\\ ( ( 9 / ; 1 0 ) <_ u /\\ u <_ 1 ) ) )')], 'jca', PTHx)
    Q = top_and(pta)
    assert Q[1] == '( %s /\\ ( %s /\\ %s ) )' % (hmt, hzt, strip_ante(formula_of(w, hh), A4)), (Q[1][:300], hmt[:100])
    pt = c4([c4([c4([cstall, pth], 'jca', Q[0]), c4([hm, c4([hz, hh], 'jca', '( %s /\\ %s )' % (hzt, strip_ante(formula_of(w, hh), A4)))], 'jca', Q[1])], 'jca', pta), w.inst('zd2pt')], 'syl', ptc)
    G2 = tsub(GAM2, SUBP)
    RHS_F = '( %s x. ( ( m x. ( v ^c e ) ) ^c ( ( 9 / 2 ) x. ( 1 - u ) ) ) )' % G2
    assert ptc == '%s <_ %s' % (NCX, RHS_F), ptc[:200]
    back = c4([c4.a1(eq, formula_of(w, eq)), pt], 'eqbrtrd', '%s <_ %s' % (NCO, RHS_F))
    BODY = LFD_BODY(G2, 'e', 'm')[len('A. v e. RR A. u e. RR '):]
    assert BODY == '( %s -> %s <_ %s )' % (PT, NCO, RHS_F), BODY[:200]
    st = w.s([back], 'ex', '( %s -> %s )' % (A3, BODY))
    r1 = ralrimi_nf(w, st, 'u', 'RR', '( ( %s /\\ m e. NN ) /\\ v e. RR )' % A0, BODY)
    r2 = ralrimi_nf(w, r1, 'v', 'RR', '( %s /\\ m e. NN )' % A0, 'A. u e. RR %s' % BODY)
    r3 = ralrimi_nf(w, r2, 'm', 'NN', A0, 'A. v e. RR A. u e. RR %s' % BODY)
    # the constants
    G2_, g2r, g21 = gam2_facts(w, A0, c, hr, h1, kn, ar, a0, br, dr, d1)
    assert G2_ == G2
    consts = c([c([g2r, er], 'jca', '( %s e. RR /\\ e e. RR )' % G2), c([g21, e1, lin8(w, A0, [e54], 'e <_ 2', {'e': er})], '3jca', '( 1 <_ %s /\\ 1 <_ e /\\ e <_ 2 )' % G2)], 'jca', '( ( %s e. RR /\\ e e. RR ) /\\ ( 1 <_ %s /\\ 1 <_ e /\\ e <_ 2 ) )' % (G2, G2))
    LFBe = LFB(G2, 'e')
    p1, p2 = top_and(LFBe)[0], top_and(LFBe)[1]
    full = c([c([g2r, er], 'jca', p1), c([g21, e1, lin8(w, A0, [e54], 'e <_ 2', {'e': er})], '3jca', p2), r3], '3jca', LFBe)
    # E. c , then E. g
    LFBc = LFB(G2, 'c')
    stc, chkc = w.wcongr(LFBc, {'c': 'e'}, 'c = e', {'c': idf('c', 'e')})
    assert chkc == LFBe, chkc[:200]
    exc = w.s([w.s([], 'vex', 'e e. _V'), stc], 'spcev', '( %s -> E. c %s )' % (LFBe, LFBc))
    stg0, chkg = w.wcongr(LFB('g', 'c'), {'g': G2}, 'g = %s' % G2, {'g': idf('g', G2)})
    assert chkg == LFBc, chkg[:200]
    stg = w.s([stg0], 'exbidv', '( g = %s -> ( E. c %s <-> E. c %s ) )' % (G2, LFB('g', 'c'), LFBc))
    exg = w.s([w.s([], 'ovex', '%s e. _V' % G2), stg], 'spcev', '( E. c %s -> %s )' % (LFBc, LOGFREE))
    f1 = c([full, c.a1(exc, formula_of(w, exc))], 'mpd', 'E. c %s' % LFBc)
    f2 = c([f1, c.a1(exg, formula_of(w, exg))], 'mpd', LOGFREE)
    # eliminate d (zd2tz), then a b (zd2thm)
    AM = '( %s /\\ %s )' % (LGBe, MATM)
    x1 = w.s([w.s([f2], 'ex', '( %s -> ( %s -> %s ) )' % (AM, MATZ, LOGFREE))], 'exlimdv', '( %s -> ( %s -> %s ) )' % (AM, S['zd2tz'], LOGFREE))
    x2 = w.s([w.s([w.s([], 'zd2tz', S['zd2tz'])], 'a1i', '( %s -> %s )' % (AM, S['zd2tz'])), x1], 'mpd', '( %s -> %s )' % (AM, LOGFREE))
    x3 = w.s([w.s([x2], 'ex', '( %s -> ( %s -> %s ) )' % (LGBe, MATM, LOGFREE))], 'exlimdvv', '( %s -> ( %s -> %s ) )' % (LGBe, S['zd2thm'], LOGFREE))
    x4 = w.s([w.s([w.s([], 'zd2thm', S['zd2thm'])], 'a1i', '( %s -> %s )' % (LGBe, S['zd2thm'])), x3], 'mpd', '( %s -> %s )' % (LGBe, LOGFREE))
    x5 = w.s([x4], 'exlimivv', '( E. e E. k %s -> %s )' % (LGBe, LOGFREE))
    LGn = 'E. h E. w E. e E. k %s' % LGBe
    x6 = w.s([x5], 'exlimivv', '( %s -> %s )' % (LGn, LOGFREE))
    # LOGGED <-> LGn (rename c -> e)
    k1, chk1 = w.wcongr(LGB('c'), {'c': 'e'}, 'c = e', {'c': idf('c', 'e')})
    assert chk1 == LGBe
    k2 = w.s([k1], 'exbidv', '( c = e -> ( E. k %s <-> E. k %s ) )' % (LGB('c'), LGBe))
    k3 = w.s([k2], 'cbvexvw', '( E. c E. k %s <-> E. e E. k %s )' % (LGB('c'), LGBe))
    k4 = w.s([k3], 'exbii', '( E. w E. c E. k %s <-> E. w E. e E. k %s )' % (LGB('c'), LGBe))
    k5 = w.s([k4], 'exbii', '( %s <-> %s )' % (LOGGED, LGn))
    w.qed([k5, x6], 'sylbi', S['zd2lfl'])
    return go(w)


GENS = {'zd2lfl': gen_lfl}

if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
