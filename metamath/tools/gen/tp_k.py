"""Sortie TP: the square of half-side R about 1 and the sup-norm distance to 1 (tpsupl: the distance is 1-Lipschitz;
tpsqf: frame points have distance R and modulus >_ 1 - R; tpsqv: a point at distance =/= R is off the frame, strictly
inside when in the square, and inside exactly when its distance is < R)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift
import cl as _cl
import ef2lib as E
import mvlib
from tp_g import FY, CN0, TPI, FRAB

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


RA = lambda v: '( abs ` ( Re ` ( %s - 1 ) ) )' % v
IA = lambda v: '( abs ` ( Im ` ( %s - 1 ) ) )' % v


def DS(v):
    """the sup-norm distance max ( abs Re ( v - 1 ) , abs Im ( v - 1 ) )"""
    return 'if ( %s <_ %s , %s , %s )' % (RA(v), IA(v), IA(v), RA(v))


S['tpsupl'] = '( ( U e. CC /\\ W e. CC ) -> ( abs ` ( %s - %s ) ) <_ ( abs ` ( U - W ) ) )' % (DS('U'), DS('W'))


def gen_supl():
    w = W('tpsupl', 'The sup-norm distance ` max ( abs Re ( v - 1 ) , abs Im ( v - 1 ) ) ` is 1-Lipschitz for the modulus.')
    A0 = '( U e. CC /\\ W e. CC )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    uc = s([], 'simpl', 'U e. CC'); wc = s([], 'simpr', 'W e. CC')
    c = Closure(w, A0, {'U': ('CC', uc), 'W': ('CC', wc)})
    e = '( abs ` ( U - W ) )'
    c.have(e, 'RR', c.mem(e, 'RR')); c.atom(e)
    facts = []
    for part, rl, sl in (('Re', 'absrele', 'resubd'), ('Im', 'absimle', 'imsubd')):
        xu = '( %s ` ( U - 1 ) )' % part; xw = '( %s ` ( W - 1 ) )' % part
        c.have(xu, 'RR', c.mem(xu, 'RR')); c.have(xw, 'RR', c.mem(xw, 'RR')); c.atom(xu); c.atom(xw)
        d1 = ap(w, A0, sl, '( %s ` ( ( U - 1 ) - ( W - 1 ) ) ) = ( %s - %s )' % (part, xu, xw), c)
        d2 = s([mvlib.ringeq(w, A0, '( ( U - 1 ) - ( W - 1 ) )', '( U - W )', c)], 'fveq2d', '( %s ` ( ( U - 1 ) - ( W - 1 ) ) ) = ( %s ` ( U - W ) )' % (part, part))
        d3 = s([d2, d1], 'eqtr3d', '( %s ` ( U - W ) ) = ( %s - %s )' % (part, xu, xw))
        d4 = s([c.mem('( U - W )', 'CC'), w.inst(rl)], 'syl', '( abs ` ( %s ` ( U - W ) ) ) <_ %s' % (part, e))
        d5 = s([s([d3], 'fveq2d', '( abs ` ( %s ` ( U - W ) ) ) = ( abs ` ( %s - %s ) )' % (part, xu, xw)), d4], 'eqbrtrrd', '( abs ` ( %s - %s ) ) <_ %s' % (xu, xw, e))
        a1 = apc(w, A0, 'abs2dif', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (xu, xw, xu, xw), c)
        a2 = apc(w, A0, 'abs2dif', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (xw, xu, xw, xu), c)
        a3 = ap(w, A0, 'abssubd', '( abs ` ( %s - %s ) ) = ( abs ` ( %s - %s ) )' % (xw, xu, xu, xw), c)
        for t in ('( abs ` %s )' % xu, '( abs ` %s )' % xw, '( abs ` ( %s - %s ) )' % (xu, xw), '( abs ` ( %s - %s ) )' % (xw, xu)):
            c.have(t, 'RR', c.mem(t, 'RR')); c.atom(t)
        f1 = lin.linarith(w, A0, [a1, d5], '( abs ` %s ) <_ ( ( abs ` %s ) + %s )' % (xu, xw, e), closure=c)
        f2 = lin.linarith(w, A0, [a2, a3, d5], '( abs ` %s ) <_ ( ( abs ` %s ) + %s )' % (xw, xu, e), closure=c)
        facts.append((f1, f2))
    m1, m2 = DS('U'), DS('W')
    for v in ('U', 'W'):
        c.have(DS(v), 'RR', c.mem(DS(v), 'RR')); c.atom(DS(v))
    mx = {}
    for v in ('U', 'W'):
        mx[v] = (apc(w, A0, 'max1', '%s <_ %s' % (RA(v), DS(v)), c), apc(w, A0, 'max2', '%s <_ %s' % (IA(v), DS(v)), c))
    (fru, frw), (fiu, fiw) = facts
    l1 = lin.linarith(w, A0, [fru, mx['W'][0]], '%s <_ ( %s + %s )' % (RA('U'), m2, e), closure=c)
    l2 = lin.linarith(w, A0, [fiu, mx['W'][1]], '%s <_ ( %s + %s )' % (IA('U'), m2, e), closure=c)
    ml1 = s([s([l1, l2], 'jca', '( %s <_ ( %s + %s ) /\\ %s <_ ( %s + %s ) )' % (RA('U'), m2, e, IA('U'), m2, e)),
             apc(w, A0, 'maxle', '( %s <_ ( %s + %s ) <-> ( %s <_ ( %s + %s ) /\\ %s <_ ( %s + %s ) ) )' % (m1, m2, e, RA('U'), m2, e, IA('U'), m2, e), c)],
            'mpbird', '%s <_ ( %s + %s )' % (m1, m2, e))
    l3 = lin.linarith(w, A0, [frw, mx['U'][0]], '%s <_ ( %s + %s )' % (RA('W'), m1, e), closure=c)
    l4 = lin.linarith(w, A0, [fiw, mx['U'][1]], '%s <_ ( %s + %s )' % (IA('W'), m1, e), closure=c)
    ml2 = s([s([l3, l4], 'jca', '( %s <_ ( %s + %s ) /\\ %s <_ ( %s + %s ) )' % (RA('W'), m1, e, IA('W'), m1, e)),
             apc(w, A0, 'maxle', '( %s <_ ( %s + %s ) <-> ( %s <_ ( %s + %s ) /\\ %s <_ ( %s + %s ) ) )' % (m2, m1, e, RA('W'), m1, e, IA('W'), m1, e), c)],
            'mpbird', '%s <_ ( %s + %s )' % (m2, m1, e))
    lo = lin.linarith(w, A0, [ml2], '-u %s <_ ( %s - %s )' % (e, m1, m2), closure=c)
    hi = lin.linarith(w, A0, [ml1], '( %s - %s ) <_ %s' % (m1, m2, e), closure=c)
    bi = ap(w, A0, 'absled', '( ( abs ` ( %s - %s ) ) <_ %s <-> ( -u %s <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s ) )' % (m1, m2, e, e, m1, m2, m1, m2, e), c)
    w.qed([s([lo, hi], 'jca', '( -u %s <_ ( %s - %s ) /\\ ( %s - %s ) <_ %s )' % (e, m1, m2, m1, m2, e)), bi], 'mpbird', S['tpsupl'])
    return run(w)



AR = '( ( 1 - R ) + ( _i x. -u R ) )'
BR = '( ( 1 + R ) + ( _i x. R ) )'
FRS = tsub(FRAB, {'A': AR, 'B': BR})
CRS = '( %s crect %s )' % (AR, BR)
INSR = lambda v: E.INS(v, AR, BR)


def sqbase(w, K, c):
    """corner facts under K, given c knows R e. RR: returns dict"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (K, f))
    c.have('_i', 'CC', s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'))
    d = {}
    d['ac'] = c.mem(AR, 'CC'); d['bc'] = c.mem(BR, 'CC')
    d['ab'] = s([d['ac'], d['bc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (AR, BR))
    r1m = c.mem('( 1 - R )', 'RR'); r1p = c.mem('( 1 + R )', 'RR'); rn = c.mem('-u R', 'RR'); rr = c.mem('R', 'RR')
    d['ra'] = s([r1m, rn, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 - R )' % AR)
    d['ia'] = s([r1m, rn, w.inst('crim')], 'syl2anc', '( Im ` %s ) = -u R' % AR)
    d['rb'] = s([r1p, rr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + R )' % BR)
    d['ib'] = s([r1p, rr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = R' % BR)
    for k, t in (('ra', '( Re ` %s )' % AR), ('ia', '( Im ` %s )' % AR), ('rb', '( Re ` %s )' % BR), ('ib', '( Im ` %s )' % BR)):
        c.have(t, 'RR', c.mem(t, 'RR')); c.atom(t)
    return d


def ptbase(w, K, c, Z, zc):
    """( Re ` ( Z - 1 ) ) = ( ( Re ` Z ) - 1 ), ( Im ` ( Z - 1 ) ) = ( Im ` Z ), atoms declared"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (K, f))
    one = s([], '1cnd', '1 e. CC')
    re_ = s([s([zc, one], 'resubd', '( Re ` ( %s - 1 ) ) = ( ( Re ` %s ) - ( Re ` 1 ) )' % (Z, Z)),
             s([s([w.s([], 're1', '( Re ` 1 ) = 1')], 'a1i', '( Re ` 1 ) = 1')], 'oveq2d', '( ( Re ` %s ) - ( Re ` 1 ) ) = ( ( Re ` %s ) - 1 )' % (Z, Z))],
            'eqtrd', '( Re ` ( %s - 1 ) ) = ( ( Re ` %s ) - 1 )' % (Z, Z))
    im0 = s([s([zc, one], 'imsubd', '( Im ` ( %s - 1 ) ) = ( ( Im ` %s ) - ( Im ` 1 ) )' % (Z, Z)),
             s([s([w.s([], 'im1', '( Im ` 1 ) = 0')], 'a1i', '( Im ` 1 ) = 0')], 'oveq2d', '( ( Im ` %s ) - ( Im ` 1 ) ) = ( ( Im ` %s ) - 0 )' % (Z, Z))],
            'eqtrd', '( Im ` ( %s - 1 ) ) = ( ( Im ` %s ) - 0 )' % (Z, Z))
    imz = s([s([zc], 'imcld', '( Im ` %s ) e. RR' % Z)], 'recnd', '( Im ` %s ) e. CC' % Z)
    im_ = s([im0, s([imz], 'subid1d', '( ( Im ` %s ) - 0 ) = ( Im ` %s )' % (Z, Z))], 'eqtrd', '( Im ` ( %s - 1 ) ) = ( Im ` %s )' % (Z, Z))
    for t, st in (('( Re ` %s )' % Z, s([zc], 'recld', '( Re ` %s ) e. RR' % Z)), ('( Im ` %s )' % Z, s([zc], 'imcld', '( Im ` %s ) e. RR' % Z)),
                  ('( Re ` ( %s - 1 ) )' % Z, None), ('( Im ` ( %s - 1 ) )' % Z, None)):
        if st is None:
            st = s([s([zc, one], 'subcld', '( %s - 1 ) e. CC' % Z)], 'recld' if 'Re' in t else 'imcld', '%s e. RR' % t)
        c.have(t, 'RR', st); c.atom(t)
    for t in (RA(Z), IA(Z), DS(Z)):
        c.have(t, 'RR', c.mem(t, 'RR')); c.atom(t)
    return re_, im_


S['tpsqf'] = '( ( ( R e. RR /\\ 0 < R ) /\\ U e. %s ) -> ( %s = R /\\ ( 1 - R ) <_ ( abs ` U ) ) )' % (FRS, DS('U'))


def gen_sqf():
    w = W('tpsqf', 'A point of the frame of the square ` [ 1 - R , 1 + R ] x [ - R , R ] ` has sup-norm distance R from 1 and modulus at least ` 1 - R ` .')
    A0 = '( ( R e. RR /\\ 0 < R ) /\\ U e. %s )' % FRS
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    rr = s([], 'simpll', 'R e. RR'); r0 = s([], 'simplr', '0 < R'); uf = s([], 'simpr', 'U e. %s' % FRS)
    c = Closure(w, A0, {'R': ('RR', rr)})
    d = sqbase(w, A0, c)
    geo1 = lin.linarith(w, A0, [d['ra'], d['rb'], r0], '( Re ` %s ) <_ ( Re ` %s )' % (AR, BR), closure=c)
    geo2 = lin.linarith(w, A0, [d['ia'], d['ib'], r0], '( Im ` %s ) <_ ( Im ` %s )' % (AR, BR), closure=c)
    G = '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) ) )' % (AR, BR, AR, BR, AR, BR)
    g = s([d['ab'], s([geo1, geo2], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (AR, BR, AR, BR))], 'jca', G)
    ucr = s([s([g, w.inst('crectfru')], 'syl', '%s C_ %s' % (FRS, CRS)), uf], 'sseldd', 'U e. %s' % CRS)
    ec = s([d['ab'], w.inst('elcrect')], 'syl', '( U e. %s <-> ( U e. CC /\\ ( Re ` U ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` U ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (CRS, AR, BR, AR, BR))
    e3 = s([ucr, ec], 'mpbid', '( U e. CC /\\ ( Re ` U ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` U ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (AR, BR, AR, BR))
    uc = s([e3], 'simp1d', 'U e. CC')
    c.have('U', 'CC', uc)
    re_, im_ = ptbase(w, A0, c, 'U', uc)
    bnd = {}
    for part, A_, B_ in (('Re', AR, BR), ('Im', AR, BR)):
        mem = s([e3], 'simp2d' if part == 'Re' else 'simp3d', '( %s ` U ) e. ( ( %s ` %s ) [,] ( %s ` %s ) )' % (part, part, A_, part, B_))
        el = s([c.mem('( %s ` %s )' % (part, A_), 'RR'), c.mem('( %s ` %s )' % (part, B_), 'RR'), w.inst('elicc2')], 'syl2anc',
               '( ( %s ` U ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( ( %s ` U ) e. RR /\\ ( %s ` %s ) <_ ( %s ` U ) /\\ ( %s ` U ) <_ ( %s ` %s ) ) )'
               % (part, part, A_, part, B_, part, part, A_, part, part, part, B_))
        tri = s([mem, el], 'mpbid', '( ( %s ` U ) e. RR /\\ ( %s ` %s ) <_ ( %s ` U ) /\\ ( %s ` U ) <_ ( %s ` %s ) )' % (part, part, A_, part, part, part, B_))
        bnd[part] = (s([tri], 'simp2d', '( %s ` %s ) <_ ( %s ` U )' % (part, A_, part)), s([tri], 'simp3d', '( %s ` U ) <_ ( %s ` %s )' % (part, part, B_)))
    X_ = '( Re ` ( U - 1 ) )'; Y_ = '( Im ` ( U - 1 ) )'
    lo = lin.linarith(w, A0, [bnd['Re'][0], d['ra'], re_], '-u R <_ %s' % X_, closure=c)
    hi = lin.linarith(w, A0, [bnd['Re'][1], d['rb'], re_], '%s <_ R' % X_, closure=c)
    ale = s([s([lo, hi], 'jca', '( -u R <_ %s /\\ %s <_ R )' % (X_, X_)), ap(w, A0, 'absled', '( ( abs ` %s ) <_ R <-> ( -u R <_ %s /\\ %s <_ R ) )' % (X_, X_, X_), c)],
            'mpbird', '%s <_ R' % RA('U'))
    lo2 = lin.linarith(w, A0, [bnd['Im'][0], d['ia'], im_], '-u R <_ %s' % Y_, closure=c)
    hi2 = lin.linarith(w, A0, [bnd['Im'][1], d['ib'], im_], '%s <_ R' % Y_, closure=c)
    ble = s([s([lo2, hi2], 'jca', '( -u R <_ %s /\\ %s <_ R )' % (Y_, Y_)), ap(w, A0, 'absled', '( ( abs ` %s ) <_ R <-> ( -u R <_ %s /\\ %s <_ R ) )' % (Y_, Y_, Y_), c)],
            'mpbird', '%s <_ R' % IA('U'))
    dle = s([s([ale, ble], 'jca', '( %s <_ R /\\ %s <_ R )' % (RA('U'), IA('U'))), apc(w, A0, 'maxle', '( %s <_ R <-> ( %s <_ R /\\ %s <_ R ) )' % (DS('U'), RA('U'), IA('U')), c)],
            'mpbird', '%s <_ R' % DS('U'))
    # R <_ DS from the frame disjunction
    FE = tsub(stmt('crectfre'), {'A': AR, 'B': BR})
    fa, fc = ante_of(FE)
    allu = s([g, w.inst('crectfre')], 'syl', fc)
    DIS = '( ( ( Re ` u ) = ( Re ` %s ) \\/ ( Re ` u ) = ( Re ` %s ) ) \\/ ( ( Im ` u ) = ( Im ` %s ) \\/ ( Im ` u ) = ( Im ` %s ) ) )' % (AR, BR, AR, BR)
    idu = w.s([], 'id', '( u = U -> u = U )')
    cgu, nu = w.wcongr(DIS, {'u': 'U'}, 'u = U', {'u': idu})
    dis = s([uf, allu, w.s([cgu], 'rspcv', '( U e. %s -> ( A. u e. %s %s -> %s ) )' % (FRS, FRS, DIS, nu))], 'sylc', nu)
    m1 = apc(w, A0, 'max1', '%s <_ %s' % (RA('U'), DS('U')), c); m2 = apc(w, A0, 'max2', '%s <_ %s' % (IA('U'), DS('U')), c)
    la = ap(w, A0, 'leabsd', '%s <_ %s' % (X_, RA('U')), c)
    lb = ap(w, A0, 'leabsd', '%s <_ %s' % (Y_, IA('U')), c)
    na = s([ap(w, A0, 'leabsd', '-u %s <_ ( abs ` -u %s )' % (X_, X_), c), ap(w, A0, 'absnegd', '( abs ` -u %s ) = %s' % (X_, RA('U')), c)], 'breqtrd', '-u %s <_ %s' % (X_, RA('U')))
    nb = s([ap(w, A0, 'leabsd', '-u %s <_ ( abs ` -u %s )' % (Y_, Y_), c), ap(w, A0, 'absnegd', '( abs ` -u %s ) = %s' % (Y_, IA('U')), c)], 'breqtrd', '-u %s <_ %s' % (Y_, IA('U')))
    cases = []
    for eqf, hyps in (('( Re ` U ) = ( Re ` %s )' % AR, [d['ra'], re_, na, m1]), ('( Re ` U ) = ( Re ` %s )' % BR, [d['rb'], re_, la, m1]),
                      ('( Im ` U ) = ( Im ` %s )' % AR, [d['ia'], im_, nb, m2]), ('( Im ` U ) = ( Im ` %s )' % BR, [d['ib'], im_, lb, m2])):
        K = '( %s /\\ %s )' % (A0, eqf)
        e = w.s([], 'simpr', '( %s -> %s )' % (K, eqf))
        hs = [_cl.lift(w, h, K) for h in hyps] + [e]
        ck2 = Closure(w, K, {})
        for t in ('R', '( Re ` U )', '( Im ` U )', X_, Y_, RA('U'), IA('U'), DS('U'), '( Re ` %s )' % AR, '( Re ` %s )' % BR, '( Im ` %s )' % AR, '( Im ` %s )' % BR):
            ck2.have(t, 'RR', _cl.lift(w, c.mem(t, 'RR'), K)); ck2.atom(t)
        r_le = lin.linarith(w, K, hs, 'R <_ %s' % DS('U'), closure=ck2)
        cases.append(w.s([r_le], 'ex', '( %s -> ( %s -> R <_ %s ) )' % (A0, eqf, DS('U'))))
    j1 = s([cases[0], cases[1]], 'jaod', '( ( ( Re ` U ) = ( Re ` %s ) \\/ ( Re ` U ) = ( Re ` %s ) ) -> R <_ %s )' % (AR, BR, DS('U')))
    j2 = s([cases[2], cases[3]], 'jaod', '( ( ( Im ` U ) = ( Im ` %s ) \\/ ( Im ` U ) = ( Im ` %s ) ) -> R <_ %s )' % (AR, BR, DS('U')))
    rle = s([dis, s([j1, j2], 'jaod', '( %s -> R <_ %s )' % (nu, DS('U')))], 'mpd', 'R <_ %s' % DS('U'))
    deq = ap(w, A0, 'letri3d', '( %s = R <-> ( %s <_ R /\\ R <_ %s ) )' % (DS('U'), DS('U'), DS('U')), c)
    deq = s([s([dle, rle], 'jca', '( %s <_ R /\\ R <_ %s )' % (DS('U'), DS('U'))), deq], 'mpbird', '%s = R' % DS('U'))
    c.have('( abs ` U )', 'RR', c.mem('( abs ` U )', 'RR')); c.atom('( abs ` U )')
    rl = s([uc, w.inst('releabs')], 'syl', '( Re ` U ) <_ ( abs ` U )')
    mo = lin.linarith(w, A0, [bnd['Re'][0], d['ra'], rl], '( 1 - R ) <_ ( abs ` U )', closure=c)
    w.qed([deq, mo], 'jca', S['tpsqf'])
    return run(w)


S['tpsqv'] = ('( ( ( R e. RR /\\ 0 < R ) /\\ ( W e. CC /\\ %s =/= R ) ) -> ( -. W e. %s /\\ ( W e. %s -> %s ) /\\ ( %s <-> %s < R ) ) )'
              % (DS('W'), FRS, CRS, INSR('W'), INSR('W'), DS('W')))


def gen_sqv():
    w = W('tpsqv', 'A point at sup-norm distance =/= R from 1 is off the frame of the square, strictly inside when in the square, '
               'and strictly inside exactly when its distance is less than R.')
    A0 = '( ( R e. RR /\\ 0 < R ) /\\ ( W e. CC /\\ %s =/= R ) )' % DS('W')
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    rr = s([], 'simpll', 'R e. RR'); r0 = s([], 'simplr', '0 < R'); wc = s([], 'simprl', 'W e. CC'); dn = s([], 'simprr', '%s =/= R' % DS('W'))
    c = Closure(w, A0, {'R': ('RR', rr), 'W': ('CC', wc)})
    d = sqbase(w, A0, c)
    re_, im_ = ptbase(w, A0, c, 'W', wc)
    X_ = '( Re ` ( W - 1 ) )'; Y_ = '( Im ` ( W - 1 ) )'
    # off the frame
    K0 = '( %s /\\ W e. %s )' % (A0, FRS)
    sq = w.s([w.s([w.s([_cl.lift(w, rr, K0), _cl.lift(w, r0, K0)], 'jca', '( %s -> ( R e. RR /\\ 0 < R ) )' % K0), w.s([], 'simpr', '( %s -> W e. %s )' % (K0, FRS))],
                  'jca', '( %s -> ( ( R e. RR /\\ 0 < R ) /\\ W e. %s ) )' % (K0, FRS)), w.inst('tpsqf')], 'syl',
             '( %s -> ( %s = R /\\ ( 1 - R ) <_ ( abs ` W ) ) )' % (K0, DS('W')))
    fr1 = w.s([w.s([sq], 'simpld', '( %s -> %s = R )' % (K0, DS('W')))], 'ex', '( %s -> ( W e. %s -> %s = R ) )' % (A0, FRS, DS('W')))
    nf = s([s([dn], 'neneqd', '-. %s = R' % DS('W')), fr1], 'mtod', '-. W e. %s' % FRS)
    # INS -> DS < R
    K1 = '( %s /\\ %s )' % (A0, INSR('W'))
    ins = w.s([], 'simpr', '( %s -> %s )' % (K1, INSR('W')))
    L1 = lambda st: _cl.lift(w, st, K1)
    c1 = Closure(w, K1, {})
    for tt in ('R', X_, Y_, '( Re ` W )', '( Im ` W )', RA('W'), IA('W'), DS('W'), '( Re ` %s )' % AR, '( Re ` %s )' % BR, '( Im ` %s )' % AR, '( Im ` %s )' % BR):
        c1.have(tt, 'RR', L1(c.mem(tt, 'RR'))); c1.atom(tt)
    rw = w.s([ins], 'simpld', '( %s -> ( ( Re ` %s ) < ( Re ` W ) /\\ ( Re ` W ) < ( Re ` %s ) ) )' % (K1, AR, BR))
    iw = w.s([ins], 'simprd', '( %s -> ( ( Im ` %s ) < ( Im ` W ) /\\ ( Im ` W ) < ( Im ` %s ) ) )' % (K1, AR, BR))
    r1 = w.s([rw], 'simpld', '( %s -> ( Re ` %s ) < ( Re ` W ) )' % (K1, AR)); r2 = w.s([rw], 'simprd', '( %s -> ( Re ` W ) < ( Re ` %s ) )' % (K1, BR))
    i1 = w.s([iw], 'simpld', '( %s -> ( Im ` %s ) < ( Im ` W ) )' % (K1, AR)); i2 = w.s([iw], 'simprd', '( %s -> ( Im ` W ) < ( Im ` %s ) )' % (K1, BR))
    xa = lin.linarith(w, K1, [r1, L1(d['ra']), L1(re_)], '-u R < %s' % X_, closure=c1)
    xb = lin.linarith(w, K1, [r2, L1(d['rb']), L1(re_)], '%s < R' % X_, closure=c1)
    ya = lin.linarith(w, K1, [i1, L1(d['ia']), L1(im_)], '-u R < %s' % Y_, closure=c1)
    yb = lin.linarith(w, K1, [i2, L1(d['ib']), L1(im_)], '%s < R' % Y_, closure=c1)
    al = w.s([w.s([xa, xb], 'jca', '( %s -> ( -u R < %s /\\ %s < R ) )' % (K1, X_, X_)), ap(w, K1, 'absltd', '( %s < R <-> ( -u R < %s /\\ %s < R ) )' % (RA('W'), X_, X_), c1)],
             'mpbird', '( %s -> %s < R )' % (K1, RA('W')))
    bl = w.s([w.s([ya, yb], 'jca', '( %s -> ( -u R < %s /\\ %s < R ) )' % (K1, Y_, Y_)), ap(w, K1, 'absltd', '( %s < R <-> ( -u R < %s /\\ %s < R ) )' % (IA('W'), Y_, Y_), c1)],
             'mpbird', '( %s -> %s < R )' % (K1, IA('W')))
    dl = w.s([w.s([al, bl], 'jca', '( %s -> ( %s < R /\\ %s < R ) )' % (K1, RA('W'), IA('W'))),
              apc(w, K1, 'maxlt', '( %s < R <-> ( %s < R /\\ %s < R ) )' % (DS('W'), RA('W'), IA('W')), c1)], 'mpbird', '( %s -> %s < R )' % (K1, DS('W')))
    fwd = w.s([dl], 'ex', '( %s -> ( %s -> %s < R ) )' % (A0, INSR('W'), DS('W')))
    # DS < R -> INS
    K2 = '( %s /\\ %s < R )' % (A0, DS('W'))
    L2 = lambda st: _cl.lift(w, st, K2)
    c2 = Closure(w, K2, {})
    for tt in ('R', X_, Y_, '( Re ` W )', '( Im ` W )', RA('W'), IA('W'), DS('W'), '( Re ` %s )' % AR, '( Re ` %s )' % BR, '( Im ` %s )' % AR, '( Im ` %s )' % BR):
        c2.have(tt, 'RR', L2(c.mem(tt, 'RR'))); c2.atom(tt)
    ml = w.s([w.s([], 'simpr', '( %s -> %s < R )' % (K2, DS('W'))), apc(w, K2, 'maxlt', '( %s < R <-> ( %s < R /\\ %s < R ) )' % (DS('W'), RA('W'), IA('W')), c2)],
             'mpbid', '( %s -> ( %s < R /\\ %s < R ) )' % (K2, RA('W'), IA('W')))
    ax_ = w.s([w.s([ml], 'simpld', '( %s -> %s < R )' % (K2, RA('W'))), ap(w, K2, 'absltd', '( %s < R <-> ( -u R < %s /\\ %s < R ) )' % (RA('W'), X_, X_), c2)],
              'mpbid', '( %s -> ( -u R < %s /\\ %s < R ) )' % (K2, X_, X_))
    ay_ = w.s([w.s([ml], 'simprd', '( %s -> %s < R )' % (K2, IA('W'))), ap(w, K2, 'absltd', '( %s < R <-> ( -u R < %s /\\ %s < R ) )' % (IA('W'), Y_, Y_), c2)],
              'mpbid', '( %s -> ( -u R < %s /\\ %s < R ) )' % (K2, Y_, Y_))
    xa2 = w.s([ax_], 'simpld', '( %s -> -u R < %s )' % (K2, X_)); xb2 = w.s([ax_], 'simprd', '( %s -> %s < R )' % (K2, X_))
    ya2 = w.s([ay_], 'simpld', '( %s -> -u R < %s )' % (K2, Y_)); yb2 = w.s([ay_], 'simprd', '( %s -> %s < R )' % (K2, Y_))
    q1 = lin.linarith(w, K2, [xa2, L2(d['ra']), L2(re_)], '( Re ` %s ) < ( Re ` W )' % AR, closure=c2)
    q2 = lin.linarith(w, K2, [xb2, L2(d['rb']), L2(re_)], '( Re ` W ) < ( Re ` %s )' % BR, closure=c2)
    q3 = lin.linarith(w, K2, [ya2, L2(d['ia']), L2(im_)], '( Im ` %s ) < ( Im ` W )' % AR, closure=c2)
    q4 = lin.linarith(w, K2, [yb2, L2(d['ib']), L2(im_)], '( Im ` W ) < ( Im ` %s )' % BR, closure=c2)
    insb = w.s([w.s([q1, q2], 'jca', '( %s -> ( ( Re ` %s ) < ( Re ` W ) /\\ ( Re ` W ) < ( Re ` %s ) ) )' % (K2, AR, BR)),
                w.s([q3, q4], 'jca', '( %s -> ( ( Im ` %s ) < ( Im ` W ) /\\ ( Im ` W ) < ( Im ` %s ) ) )' % (K2, AR, BR))], 'jca', '( %s -> %s )' % (K2, INSR('W')))
    bwd = w.s([insb], 'ex', '( %s -> ( %s < R -> %s ) )' % (A0, DS('W'), INSR('W')))
    iff = s([fwd, bwd], 'impbid', '( %s <-> %s < R )' % (INSR('W'), DS('W')))
    # in the square -> inside
    K3 = '( %s /\\ W e. %s )' % (A0, CRS)
    L3 = lambda st: _cl.lift(w, st, K3)
    c3 = Closure(w, K3, {})
    for tt in ('R', X_, Y_, '( Re ` W )', '( Im ` W )', RA('W'), IA('W'), DS('W'), '( Re ` %s )' % AR, '( Re ` %s )' % BR, '( Im ` %s )' % AR, '( Im ` %s )' % BR):
        c3.have(tt, 'RR', L3(c.mem(tt, 'RR'))); c3.atom(tt)
    ec = w.s([L3(d['ab']), w.inst('elcrect')], 'syl', '( %s -> ( W e. %s <-> ( W e. CC /\\ ( Re ` W ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` W ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) ) )'
             % (K3, CRS, AR, BR, AR, BR))
    e3 = w.s([w.s([], 'simpr', '( %s -> W e. %s )' % (K3, CRS)), ec], 'mpbid', '( %s -> ( W e. CC /\\ ( Re ` W ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` W ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )'
             % (K3, AR, BR, AR, BR))
    bn = {}
    for part in ('Re', 'Im'):
        mem = w.s([e3], 'simp2d' if part == 'Re' else 'simp3d', '( %s -> ( %s ` W ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) )' % (K3, part, part, AR, part, BR))
        el = w.s([c3.mem('( %s ` %s )' % (part, AR), 'RR'), c3.mem('( %s ` %s )' % (part, BR), 'RR'), w.inst('elicc2')], 'syl2anc',
                 '( %s -> ( ( %s ` W ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( ( %s ` W ) e. RR /\\ ( %s ` %s ) <_ ( %s ` W ) /\\ ( %s ` W ) <_ ( %s ` %s ) ) ) )'
                 % (K3, part, part, AR, part, BR, part, part, AR, part, part, part, BR))
        tri = w.s([mem, el], 'mpbid', '( %s -> ( ( %s ` W ) e. RR /\\ ( %s ` %s ) <_ ( %s ` W ) /\\ ( %s ` W ) <_ ( %s ` %s ) ) )' % (K3, part, part, AR, part, part, part, BR))
        bn[part] = (w.s([tri], 'simp2d', '( %s -> ( %s ` %s ) <_ ( %s ` W ) )' % (K3, part, AR, part)), w.s([tri], 'simp3d', '( %s -> ( %s ` W ) <_ ( %s ` %s ) )' % (K3, part, part, BR)))
    lo = lin.linarith(w, K3, [bn['Re'][0], L3(d['ra']), L3(re_)], '-u R <_ %s' % X_, closure=c3)
    hi = lin.linarith(w, K3, [bn['Re'][1], L3(d['rb']), L3(re_)], '%s <_ R' % X_, closure=c3)
    lo2 = lin.linarith(w, K3, [bn['Im'][0], L3(d['ia']), L3(im_)], '-u R <_ %s' % Y_, closure=c3)
    hi2 = lin.linarith(w, K3, [bn['Im'][1], L3(d['ib']), L3(im_)], '%s <_ R' % Y_, closure=c3)
    a3 = w.s([w.s([lo, hi], 'jca', '( %s -> ( -u R <_ %s /\\ %s <_ R ) )' % (K3, X_, X_)), ap(w, K3, 'absled', '( %s <_ R <-> ( -u R <_ %s /\\ %s <_ R ) )' % (RA('W'), X_, X_), c3)],
             'mpbird', '( %s -> %s <_ R )' % (K3, RA('W')))
    b3 = w.s([w.s([lo2, hi2], 'jca', '( %s -> ( -u R <_ %s /\\ %s <_ R ) )' % (K3, Y_, Y_)), ap(w, K3, 'absled', '( %s <_ R <-> ( -u R <_ %s /\\ %s <_ R ) )' % (IA('W'), Y_, Y_), c3)],
             'mpbird', '( %s -> %s <_ R )' % (K3, IA('W')))
    d3 = w.s([w.s([a3, b3], 'jca', '( %s -> ( %s <_ R /\\ %s <_ R ) )' % (K3, RA('W'), IA('W'))), apc(w, K3, 'maxle', '( %s <_ R <-> ( %s <_ R /\\ %s <_ R ) )' % (DS('W'), RA('W'), IA('W')), c3)],
             'mpbird', '( %s -> %s <_ R )' % (K3, DS('W')))
    ne3 = w.s([L3(dn)], 'necomd', '( %s -> R =/= %s )' % (K3, DS('W')))
    lt3 = w.s([ne3, ap(w, K3, 'leltned', '( %s < R <-> R =/= %s )' % (DS('W'), DS('W')), c3, facts=[d3])], 'mpbird', '( %s -> %s < R )' % (K3, DS('W')))
    in3 = w.s([lt3, L3(bwd)], 'mpd', '( %s -> %s )' % (K3, INSR('W')))
    crin = w.s([in3], 'ex', '( %s -> ( W e. %s -> %s ) )' % (A0, CRS, INSR('W')))
    w.qed([nf, crin, iff], '3jca', S['tpsqv'])
    return run(w)


if __name__ == '__main__':
    gen_supl()
    gen_sqf()
    gen_sqv()
