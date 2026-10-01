"""T7: the concrete composites (blueprint D5): dropNum, dup, canonNum and its
B form, as instances of ~ tm2fdrop , ~ tm2fdup , ~ tm2fcan with the handlers
concrete and the interfaces discharged."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def machine(w, ph, c, ks):
    """the machine facts from PHM7 (a Ctx c over a tree containing T_PHM7): phm, tv, geq, seq,
    and per stack index k in ks: kd (k e. DG), ge (GK = Gamma'), wge (Word GK = Word Gamma'),
    hdl (the five handler typings)"""
    phm, geq, seq = c[PHM], c[GEQ], c[SEQ]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    gs = w.s([geq, seq], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, GEQ, SEQ))
    mt = w.s([phm, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, MTY))
    out = dict(phm=phm, tv=tv, mt=mt, geq=geq, seq=seq, gs=gs, k={})
    for k in ks:
        kk = c[IDX(k)]
        j = w.s([geq, kk], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, GEQ, IDX(k)))
        both = w.s([j, w.inst('tmcgk')], 'syl', "( %s -> ( %s e. %s /\\ %s = Gamma' ) )" % (ph, k, DG, GX(k)))
        kd = w.s([both], 'simpld', '( %s -> %s e. %s )' % (ph, k, DG))
        ge = w.s([both], 'simprd', "( %s -> %s = Gamma' )" % (ph, GX(k)))
        wge = w.s([ge, w.inst('wrdeq')], 'syl', "( %s -> Word %s = Word Gamma' )" % (ph, GX(k)))
        j2 = w.s([gs, kk], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ %s ) )' % (ph, GEQ, SEQ, IDX(k)))
        hd = w.s([j2, w.inst('tmchdl')], 'syl', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) )'
                 % (ph, RTY('TMrdA', k), RTY('TMrdB', k), RTY('TMrdBit', k), RTY('TMrdEnd', k), RTY(PID, k)))
        h1 = w.s([hd, w.inst('simp1')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RTY('TMrdA', k), RTY('TMrdB', k)))
        h2 = w.s([hd, w.inst('simp2')], 'syl', '( %s -> ( %s /\\ %s ) )' % (ph, RTY('TMrdBit', k), RTY('TMrdEnd', k)))
        hdl = {'TMrdA': w.s([h1], 'simpld', '( %s -> %s )' % (ph, RTY('TMrdA', k))),
               'TMrdB': w.s([h1], 'simprd', '( %s -> %s )' % (ph, RTY('TMrdB', k))),
               'TMrdBit': w.s([h2], 'simpld', '( %s -> %s )' % (ph, RTY('TMrdBit', k))),
               'TMrdEnd': w.s([h2], 'simprd', '( %s -> %s )' % (ph, RTY('TMrdEnd', k))),
               PID: w.s([hd, w.inst('simp3')], 'syl', '( %s -> %s )' % (ph, RTY(PID, k)))}
        out['k'][k] = dict(kk=kk, kd=kd, ge=ge, wge=wge, hdl=hdl)
    return out


def togk(w, ph, mk, X, k, xg):
    """( ph -> X e. Word GK ) from xg : X e. Word Gamma'"""
    return w.s([xg, mk['k'][k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(k)))


def letgk(w, ph, mk, Z, k, zg):
    """( ph -> Z e. GK ) from zg : Z e. Gamma'"""
    return w.s([zg, mk['k'][k]['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, Z, GX(k)))


def bitsgk(w, ph, mk, k):
    """( ph -> BITS C_ GK )"""
    bs = closed(w, ph, 'tm2lbits', "%s C_ Gamma'" % BITS)
    return w.s([bs, mk['k'][k]['ge']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, BITS, GX(k)))


def lamty(w, ph, mk, lam, X_of, Y, ycl, bodycl):
    """( ph -> lam e. ( Y ^m S ) ) by tmcmapty; ycl : Y e. _V closed step; bodycl : closed step
    ( u e. TMSt -> X(u) e. Y ) (or a closed X(u) e. Y)"""
    f = formula(w, bodycl)
    if f.startswith('( u e. TMSt ->'):
        ral = w.s([bodycl], 'rgen', 'A. u e. TMSt %s e. %s' % (X_of('u'), Y))
    else:
        ral = w.s([bodycl], 'rgen' if False else 'rgenw', 'A. u e. TMSt %s e. %s' % (X_of('u'), Y))
    rala = w.s([ral], 'a1i', '( %s -> A. u e. TMSt %s e. %s )' % (ph, X_of('u'), Y))
    yv = w.s([ycl], 'a1i', '( %s -> %s e. _V )' % (ph, Y))
    j = w.s([mk['seq'], yv, rala], '3jca', '( %s -> ( %s /\\ %s e. _V /\\ A. u e. TMSt %s e. %s ) )' % (ph, SEQ, Y, X_of('u'), Y))
    return w.s([j, w.inst('tmcmapty')], 'syl', '( %s -> %s e. ( %s ^m ( 2nd ` T ) ) )' % (ph, lam, Y))


def cis_ty(w, ph, mk):
    X_of = lambda t: 'if ( ( TMra ` %s ) = %s , (/) , 1o )' % (t, NONE)
    b = w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    return lamty(w, ph, mk, CIS, X_of, '2o', w.s([], '2oex', '2o e. _V'), b)


def pbr_ty(w, ph, mk, k):
    """( ph -> PBR e. ( GK ^m S ) )"""
    X_of = lambda t: '<. 1 , ( bitOf ` ( TMra ` %s ) ) >.' % t
    b1 = w.s([], 'tmcracl', '( u e. TMSt -> ( TMra ` u ) e. ( 2o |_| 1o ) )')
    b2 = w.s([b1, w.inst('bitofcl')], 'syl', '( u e. TMSt -> ( bitOf ` ( TMra ` u ) ) e. 2o )')
    b3 = w.s([b2, w.inst('bitgamma')], 'syl', "( u e. TMSt -> %s e. Gamma' )" % X_of('u'))
    t = lamty(w, ph, mk, PBR, X_of, GAM, w.s([], 'gammaex', "Gamma' e. _V"), b3)
    e = w.s([mk['k'][k]['ge']], 'eqcomd', "( %s -> Gamma' = %s )" % (ph, GX(k)))
    e2 = w.s([e], 'oveq1d', "( %s -> ( Gamma' ^m ( 2nd ` T ) ) = ( %s ^m ( 2nd ` T ) ) )" % (ph, GX(k)))
    return w.s([t, e2], 'eleqtrd', '( %s -> %s e. ( %s ^m ( 2nd ` T ) ) )' % (ph, PBR, GX(k)))


def ral_S(w, ph, mk, st, inner, binders):
    """rewrite A. r e. TMSt [A. z e. B] inner (closed step st) into A. r e. ( 2nd ` T ) ..."""
    rest = ('A. z e. %s ' % BITS if binders == 2 else '') + inner
    seqr = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    bi = w.s([seqr], 'raleqdv', '( %s -> ( A. r e. TMSt %s <-> A. r e. ( 2nd ` T ) %s ) )' % (ph, rest, rest))
    sta = w.s([st], 'a1i', '( %s -> A. r e. TMSt %s )' % (ph, rest))
    return w.s([bi, sta], 'mpbid', '( %s -> A. r e. ( 2nd ` T ) %s )' % (ph, rest))


def tmcdrop():
    lab = 'tmcdrop'
    ph = cj(TREE_DROP)
    w = W(lab, '` dropNum x ` at the machine: ~ tm2fdrop with the handler ` readA ` , the test ` ra.isSome ` , '
               'the bit letters and the terminator ` 4 ` , the interface by ~ tmcdri .  Lean: ` dropNum_runs ` '
               '(the ` _correct ` form is this at ` W := ( encNatGam ` a ) ` ).')
    c = Ctx(w, ph, TREE_DROP)
    mk = machine(w, ph, c, ['K'])
    K = mk['k']['K']
    xg, ww, dd = c[WRD('X', GAM)], c[WRD('W', BITS)], c[STKD('D')]
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    x4 = w.s([w.s([g4], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % ph), xg, w.inst('ccatcl')], 'syl2anc',
             "( %s -> %s e. Word Gamma' )" % (ph, YX4))
    dri = w.s([], 'tmcdri', ST_DRI)
    hc = ral_S(w, ph, mk, w.s([dri], 'simpli', ST_DRI[2:].split(' /\\ A. r e. TMSt ')[0]), '( %s ` %s ) = 1o' % (CIS, NVA('r', 'z')), 2)
    he = ral_S(w, ph, mk, w.s([dri], 'simpri', 'A. r e. TMSt -. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4'))), '-. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')), 1)
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], 'K e. %s' % DG: K['kd'], RTY('TMrdA', 'K'): K['hdl']['TMrdA'], CTY(CIS): cis_ty(w, ph, mk),
             '%s C_ %s' % (BITS, GK): bitsgk(w, ph, mk, 'K'), WRD(YX4, GK): togk(w, ph, mk, YX4, 'K', x4),
             '4 e. %s' % GK: letgk(w, ph, mk, '4', 'K', g4), WRD('X', GK): togk(w, ph, mk, 'X', 'K', xg),
             formula(w, hc)[len('( %s -> ' % ph):-2]: hc, formula(w, he)[len('( %s -> ' % ph):-2]: he}
    bld = Builder(w, ph, c, extra)
    m = {'F': 'TMrdA', 'C': CIS, 'B': BITS, 'Y': '4'}
    ante, concl = split_imp(stmt('tm2fdrop'))
    tree = tsub(parse_conj(ante), m)
    st = bld(tree)
    c2 = tsub_text(concl, m)
    assert c2 == CONCL_DROP, (c2, CONCL_DROP)
    w.qed([st, w.inst('tm2fdrop')], 'syl', '( %s -> %s )' % (ph, c2))
    return w.run()


if __name__ == '__main__':
    if want('tmcdrop'): tmcdrop()


def and3dup(w, inner_c, inner_p):
    """closed: ( ( c /\\ p ) -> ( c /\\ p /\\ p ) )"""
    cp = '( %s /\\ %s )' % (inner_c, inner_p)
    i = w.s([], 'id', '( %s -> %s )' % (cp, cp))
    r = w.s([], 'simpr', '( %s -> %s )' % (cp, inner_p))
    j = w.s([i, r], 'jca', '( %s -> ( %s /\\ %s ) )' % (cp, cp, inner_p))
    d = w.s([], 'df-3an', '( ( %s /\\ %s /\\ %s ) <-> ( %s /\\ %s ) )' % (inner_c, inner_p, inner_p, cp, inner_p))
    return w.s([j, d], 'sylibr', '( %s -> ( %s /\\ %s /\\ %s ) )' % (cp, inner_c, inner_p, inner_p))


def tmcdup():
    lab = 'tmcdup'
    ph = cj(TREE_DUP)
    w = W(lab, '` dup x y s ` at the machine: ~ tm2fdup with ` readA ` , the test ` ra.isSome ` and the push '
               '` bitOf ra ` on every stage, the interfaces by ~ tmcmvi .  Lean: ` dup_runs ` .')
    c = Ctx(w, ph, TREE_DUP)
    mk = machine(w, ph, c, ['K', 'J', 'I'])
    xg, ww, dd = c[WRD('X', GAM)], c[WRD('W', BITS)], c[STKD('D')]
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    N = NVA('r', 'z')
    cis = '( %s ` %s ) = 1o' % (CIS, N)
    pbr = '( %s ` %s ) = z' % (PBR, N)
    mvi = w.s([], 'tmcmvi', ST_MVI)
    hc = w.s([mvi], 'simpli', 'A. r e. TMSt A. z e. %s ( %s /\\ %s )' % (BITS, cis, pbr))
    he = w.s([mvi], 'simpri', 'A. r e. TMSt -. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')))
    a3 = and3dup(w, cis, pbr)
    a3i = w.s([a3], 'ralimi', '( A. z e. %s ( %s /\\ %s ) -> A. z e. %s ( %s /\\ %s /\\ %s ) )' % (BITS, cis, pbr, BITS, cis, pbr, pbr))
    a3o = w.s([a3i], 'ralimi', '( A. r e. TMSt A. z e. %s ( %s /\\ %s ) -> A. r e. TMSt A. z e. %s ( %s /\\ %s /\\ %s ) )' % (BITS, cis, pbr, BITS, cis, pbr, pbr))
    hc2 = w.s([hc, a3o], 'ax-mp', 'A. r e. TMSt A. z e. %s ( %s /\\ %s /\\ %s )' % (BITS, cis, pbr, pbr))
    HC = ral_S(w, ph, mk, hc, '( %s /\\ %s )' % (cis, pbr), 2)
    HE = ral_S(w, ph, mk, he, '-. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')), 1)
    HC2 = ral_S(w, ph, mk, hc2, '( %s /\\ %s /\\ %s )' % (cis, pbr, pbr), 2)
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'], CTY(CIS): cis_ty(w, ph, mk),
             leaf(HC): HC, leaf(HE): HE, leaf(HC2): HC2}
    for k in ['K', 'J', 'I']:
        K = mk['k'][k]
        extra['%s e. %s' % (k, DG)] = K['kd']
        extra[RTY('TMrdA', k)] = K['hdl']['TMrdA']
        extra[PTY(PBR, k)] = pbr_ty(w, ph, mk, k)
        extra['%s C_ %s' % (BITS, GX(k))] = bitsgk(w, ph, mk, k)
        extra['4 e. %s' % GX(k)] = letgk(w, ph, mk, '4', k, g4)
    extra[WRD('X', GK)] = togk(w, ph, mk, 'X', 'K', xg)
    bld = Builder(w, ph, c, extra)
    m = {'F': 'TMrdA', "F'": 'TMrdA', 'C': CIS, 'P': PBR, "P'": PBR, 'O': PBR, 'B': BITS, 'Y': '4'}
    ante, concl = split_imp(stmt('tm2fdup'))
    tree = tsub(parse_conj(ante), m)
    st = bld(tree)
    c2 = tsub_text(concl, m)
    assert c2 == CONCL_DUP, (c2, CONCL_DUP)
    w.qed([st, w.inst('tm2fdup')], 'syl', '( %s -> %s )' % (ph, c2))
    return w.run()


if __name__ == '__main__':
    if want('tmcdup'): tmcdup()
