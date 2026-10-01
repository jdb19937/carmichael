"""T6b: ` copyList ` (blueprint 2.5): the body ~ tm2lcpyb (~ tm2lme then T5's
~ tm2fdup ), the loop and the pop ~ tm2lcpyl (~ tm2lfe over the three-stack
family, ~ tm2lpop ), the composite ~ tm2lcpy (~ tm2lrev2 , two ~ tm2fpshn ,
~ tm2lcpyl )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6blib import *
from cl import Closure

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

NFINS = '{ q e. %s | -. ( C ` q ) = 1o }' % SS
YBC = '( ( 4 x. B ) + 9 )'


def hleqed(w, ante, phm, C, D, N, P, tri, pcl, le):
    a = w.s([phm, tri], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, PHM, HR(C, 'T', 'M', D, N)))
    b = w.s([pcl, le], 'jca', '( %s -> ( %s e. NN0 /\\ %s <_ %s ) )' % (ante, P, N, P))
    w.qed([a, b, w.inst('tm2hle')], 'syl2anc', '( %s -> %s )' % (ante, HR(C, 'T', 'M', D, P)))


def ssidS(w, ph):
    s = w.s([], 'ssid', '%s C_ %s' % (SS, SS))
    return w.s([s], 'a1i', '( %s -> %s C_ %s )' % (ph, SS, SS))


def dupiface(w, ph, mifs):
    """T5's mover interface ( HCMOV /\\ HEMOV ) at F' C' P over S from MIFACE at S"""
    mi1 = w.s([mifs], 'simpld', '( %s -> %s )' % (ph, MIFACE_AT(SS).split(' /\\ A. r e. ')[0][2:]))
    mi2 = w.s([mifs], 'simprd', '( %s -> A. r e. %s )' % (ph, MIFACE_AT(SS).split(' /\\ A. r e. ', 1)[1][:-2]))
    a = "( ( C' ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. %s )" % (NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'), SS)
    b = "( ( C' ` %s ) = 1o /\\ ( P ` %s ) = z )" % (NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'))
    i3 = w.s([], '3simpa', '( %s -> %s )' % (a, b))
    r1 = w.s([i3], 'ralimi', '( A. z e. %s %s -> A. z e. %s %s )' % (BITS, a, BITS, b))
    r2 = w.s([r1], 'ralimi', '( A. r e. %s A. z e. %s %s -> A. r e. %s A. z e. %s %s )' % (SS, BITS, a, SS, BITS, b))
    hc = w.s([mi1, r2], 'syl', '( %s -> %s )' % (ph, HCMOV))
    a2 = "( -. ( C' ` %s ) = 1o /\\ %s e. %s )" % (NVF("F'", 'r', '4'), NVF("F'", 'r', '4'), SS)
    b2 = "-. ( C' ` %s ) = 1o" % NVF("F'", 'r', '4')
    i4 = w.s([], 'simpl', '( %s -> %s )' % (a2, b2))
    r3 = w.s([i4], 'ralimi', '( A. r e. %s %s -> A. r e. %s %s )' % (SS, a2, SS, b2))
    he = w.s([mi2, r3], 'syl', '( %s -> %s )' % (ph, HEMOV))
    return hc, he


def bitsk(w, ph, K, gk):
    """( ph -> ( { 1 } X. 2o ) C_ ( G ` K ) )"""
    b = bitsss(w, ph)
    return w.s([b, gk], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, BITS, GT(K)))


def tm2lcpyb():
    lab = 'tm2lcpyb'
    ph = PHB
    w = W(lab, 'The body of ` copyList ` \'s loop (TM/Lists.lean): ` moveEntry z x s ` then '
               '` dup x y s ` moves the top entry of stack ` I\' ` onto stack ` K ` and copies it '
               'onto stack ` J ` ; the scratch stack ` I ` is restored.  ~ tm2lme then T5\'s ~ tm2fdup .')
    c = Ctx(w, ph, T_PHB)
    phm = c[PHM]; geq = c[GEQ]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    dd = c['D e. %s' % STK_T]
    kk, jj, ii, i2 = c['K e. %s' % FZ8], c['J e. %s' % FZ8], c['I e. %s' % FZ8], c["I' e. %s" % FZ8]
    kd, gk = gamk(w, ph, 'K', geq, kk)
    jd, gj = gamk(w, ph, 'J', geq, jj)
    idd, gi = gamk(w, ph, 'I', geq, ii)
    i2d, gi2 = gamk(w, ph, "I'", geq, i2)
    ww, xx = c['W e. %s' % WB], c['X e. %s' % WG]
    di = c['( D ` I\' ) = ( W ++ ( <" 4 "> ++ X ) )']
    ex = {}
    ex["I' =/= K"] = w.s([c["K =/= I'"]], 'necomd', "( %s -> I' =/= K )" % ph)
    ex["I' =/= I"] = w.s([c["I =/= I'"]], 'necomd', "( %s -> I' =/= I )" % ph)
    ex['%s C_ %s' % (SS, SS)] = ssidS(w, ph)
    bld = Builder(w, ph, c, ex)
    # ---- stage 1: moveEntry I' K I
    m1 = {'K': "I'", 'J': 'K', 'A': 'B0', "A'": 'D0', 'A"': 'E0', "E'": 'F0', 'E': 'H0', 'N': SS, 'F': "F'", 'C': "C'"}
    s1, c1 = inst(w, ph, 'tm2lme', m1, bld)
    C0, D1, B1 = triple_parts(c1)
    WK = '( W ++ ( <" 4 "> ++ ( D ` K ) ) )'
    D1x = UPDT(UPDT('D', "I'", 'X'), 'K', WK)
    assert C0 == CL('B0', SS, 'D') and D1 == CL('H0', SS, D1x), (C0, D1)
    # ---- stage 2: dup K J I from D1x
    dkw = stkfvg(w, ph, 'D', 'K', tv, dd, kd, gk)
    djw = stkfvg(w, ph, 'D', 'J', tv, dd, jd, gj)
    wg = wbtog(w, ph, 'W', ww)
    c4 = s1g(w, ph, '4')
    c4k = ccatg(w, ph, '<" 4 ">', '( D ` K )', c4, dkw)
    wk = ccatg(w, ph, 'W', '( <" 4 "> ++ ( D ` K ) )', wg, c4k)
    wkv = w.s([wk], 'elexd', '( %s -> %s e. _V )' % (ph, WK))
    dix = updcl(w, ph, 'D', "I'", 'X', tv, dd, i2d, gi2, xx)
    d1cl = updcl(w, ph, UPDT('D', "I'", 'X'), 'K', WK, tv, dix, kd, gk, wk)
    d1k = updk(w, ph, UPDT('D', "I'", 'X'), 'K', WK, tv, dix, kd, wkv)
    ex2 = dict(ex)
    ex2['K e. %s' % DG] = kd; ex2['J e. %s' % DG] = jd; ex2['I e. %s' % DG] = idd
    ex2[FT("F'").replace(OPT, '( %s |_| 1o )' % GT('K'))] = fmapg(w, ph, "F'", 'K', gk, c[FT("F'")])
    ex2[FT('F0').replace(OPT, '( %s |_| 1o )' % GT('I'))] = fmapg(w, ph, 'F0', 'I', gi, c[FT('F0')])
    ex2['P e. ( %s ^m %s )' % (GT('I'), SS)] = pmapg(w, ph, 'P', 'I', gi, c[PT('P')])
    ex2["P' e. ( %s ^m %s )" % (GT('K'), SS)] = pmapg(w, ph, "P'", 'K', gk, c[PT("P'")])
    ex2['O e. ( %s ^m %s )' % (GT('J'), SS)] = pmapg(w, ph, 'O', 'J', gj, c[PT('O')])
    for Kx, g in (('K', gk), ('J', gj), ('I', gi)):
        ex2['%s C_ %s' % (BITS, GT(Kx))] = bitsk(w, ph, Kx, g)
        ex2['4 e. %s' % GT(Kx)] = lgk(w, ph, '4', Kx, g, gamlet(w, ph, '4'))
    ex2['( D ` K ) e. Word %s' % GT('K')] = wgk(w, ph, '( D ` K )', 'K', gk, dkw)
    ex2['%s e. %s' % (D1x, STK_T)] = d1cl
    ex2['( %s ` K ) = %s' % (D1x, WK)] = d1k
    hc, he = dupiface(w, ph, c[MIFS])
    ex2[HCMOV] = hc; ex2[HEMOV] = he
    bld2 = Builder(w, ph, c, ex2)
    m2 = {'A': 'H0', "A'": 'I0', 'A"': 'J0', "E'": 'K0', 'E"': 'L0', 'E': 'C0', 'F': "F'", "F'": 'F0', 'C': "C'",
          'B': BITS, 'Y': '4', 'X': '( D ` K )', 'D': D1x}
    s2, c2 = inst(w, ph, 'tm2fdup', m2, bld2)
    C1b, D2, B2 = triple_parts(c2)
    assert C1b == D1, (C1b, D1)
    WJ1 = '( W ++ ( <" 4 "> ++ ( %s ` J ) ) )' % D1x
    D2x = UPDT(D1x, 'J', WJ1)
    assert D2 == CL('C0', SS, D2x), D2
    # ---- ( D1x ` J ) = ( D ` J )
    xv = w.s([xx], 'elexd', '( %s -> X e. _V )' % ph)
    j1 = updn(w, ph, UPDT('D', "I'", 'X'), 'K', WK, 'J', tv, dix, kd, wkv, jd, w.s([c['K =/= J']], 'necomd', '( %s -> J =/= K )' % ph))
    j2 = updn(w, ph, 'D', "I'", 'X', 'J', tv, dd, i2d, xv, jd, c["J =/= I'"])
    j3 = w.s([j1, j2], 'eqtrd', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph, D1x))
    j4 = w.s([j3], 'oveq2d', '( %s -> ( <" 4 "> ++ ( %s ` J ) ) = ( <" 4 "> ++ ( D ` J ) ) )' % (ph, D1x))
    j5 = w.s([j4], 'oveq2d', '( %s -> %s = ( W ++ ( <" 4 "> ++ ( D ` J ) ) ) )' % (ph, WJ1))
    st, r = w.rewrite(D2x, {WJ1: ('( W ++ ( <" 4 "> ++ ( D ` J ) ) )', j5)}, ph)
    assert r == BFIN, r
    s2b = hrtransport(w, ph, s2, D1, D2, B2, None, CL('C0', SS, BFIN), eqd=cleq(w, ph, 'C0', SS, D2x, BFIN, st))
    C2 = CL('C0', SS, BFIN)
    q = hseq(w, ph, phm, C0, D1, C2, B1, B2, s1, s2b)
    TOT = '( %s + %s )' % (B1, B2)
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl = Closure(w, ph, {'( # ` W )': nw})
    eq = lineq(w, ph, TOT, BBODY, closure=cl)
    o = w.s([eq], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C2, TOT, C2, BBODY))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C2, TOT), HR(C0, 'T', 'M', C2, BBODY)))
    w.qed([b, q], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C2, BBODY)))
    return w.run()


# ---------------------------------------------------------------- the loop

def common(w, ph, c):
    """facts of PHC every stage needs"""
    u = {}
    u['phm'] = phm = c[PHM]; u['geq'] = geq = c[GEQ]
    u['tv'] = tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    u['dd'] = dd = c['D e. %s' % STK_T]
    for Kx in ('K', 'J', 'I', "I'"):
        kd, gk = gamk(w, ph, Kx, geq, c['%s e. %s' % (Kx, FZ8)])
        u['d' + Kx] = kd; u['g' + Kx] = gk
    u['ll'] = c['L e. %s' % WWB]; u['rr'] = c['R e. %s' % WG]; u['bb'] = c['B e. NN0']; u['bw'] = c[RALW('L')]
    u['dk'] = c['( D ` K ) = %s' % LST('L', 'R')]
    u['rvl'] = w.s([u['ll'], w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, REVL, WWB))
    u['nlr'] = w.s([u['rvl'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NLR))
    u['nl'] = w.s([u['ll'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL))
    u['diw'] = stkfvg(w, ph, 'D', "I'", tv, dd, u["dI'"], u["gI'"])
    u['djw'] = stkfvg(w, ph, 'D', 'J', tv, dd, u['dJ'], u['gJ'])
    u['dkw'] = stkfvg(w, ph, 'D', 'K', tv, dd, u['dK'], u['gK'])
    u['c2'] = s1g(w, ph, '2')
    u['c2r'] = ccatg(w, ph, '<" 2 ">', 'R', u['c2'], u['rr'])
    u['c2j'] = ccatg(w, ph, '<" 2 ">', '( D ` J )', u['c2'], u['djw'])
    u['njk'] = w.s([c['K =/= J']], 'necomd', '( %s -> J =/= K )' % ph)
    u['nik'] = w.s([c["K =/= I'"]], 'necomd', "( %s -> I' =/= K )" % ph)
    u['nij'] = w.s([c["J =/= I'"]], 'necomd', "( %s -> I' =/= J )" % ph)
    u['nii'] = w.s([c["I =/= I'"]], 'necomd', "( %s -> I' =/= I )" % ph)
    return u


def liftu(w, u, big):
    out = {}
    for k, v in u.items():
        f = formula(w, v)
        f = f.split(' -> ', 1)[1][:-2] if False else None
        out[k] = v
    return out


def lift_dict(w, ph, u, big):
    """every step of u (at ph) re-anteceded to big = ( ph /\\ ... )"""
    out = {}
    for k, v in u.items():
        if callable(v):
            continue
        out[k] = w.s([v], 'adantr', '( %s -> %s )' % (big, concl(w, ph, v)))
    return out


def famcl(w, ph, u, j):
    """closures of AJ(j), BJ(j), CJ(j) and PJC(j); returns dict"""
    r = {}
    pf = w.s([u['rvl'], w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ph, PFX(REVL, j), WWB))
    r['rpc'] = w.s([pf, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, RPC(j), WWB))
    r['ent'] = w.s([r['rpc'], w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENT(RPC(j)), WG))
    r['aj'] = ccatg(w, ph, ENT(RPC(j)), '( <" 2 "> ++ R )', r['ent'], u['c2r'])
    r['bj'] = ccatg(w, ph, ENT(RPC(j)), '( <" 2 "> ++ ( D ` J ) )', r['ent'], u['c2j'])
    dr = w.s([u['rvl'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DROP(REVL, j), WWB))
    ec = w.s([dr, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(DROP(REVL, j)), WG))
    r['cj'] = ccatg(w, ph, ENCB(DROP(REVL, j)), "( D ` I' )", ec, u['diw'])
    r['p1'] = updcl(w, ph, 'D', 'K', AJ(j), u['tv'], u['dd'], u['dK'], u['gK'], r['aj'])
    P2 = UPDT(UPDT('D', 'K', AJ(j)), 'J', BJ(j))
    r['p2'] = updcl(w, ph, UPDT('D', 'K', AJ(j)), 'J', BJ(j), u['tv'], r['p1'], u['dJ'], u['gJ'], r['bj'])
    r['p3'] = updcl(w, ph, P2, "I'", CJ(j), u['tv'], r['p2'], u["dI'"], u["gI'"], r['cj'])
    r['ajv'] = w.s([r['aj']], 'elexd', '( %s -> %s e. _V )' % (ph, AJ(j)))
    r['bjv'] = w.s([r['bj']], 'elexd', '( %s -> %s e. _V )' % (ph, BJ(j)))
    r['cjv'] = w.s([r['cj']], 'elexd', '( %s -> %s e. _V )' % (ph, CJ(j)))
    return r


def pvalc(w, ph, u, X, xfz):
    """( ph -> ( PDEFC ` X ) = PJC(X) ) with the closure dict of PJC(X)"""
    cg = w.s([], 'id', '( n = %s -> n = %s )' % (X, X))
    st, res = w.congr(PJC('n'), {'n': X}, 'n = %s' % X, {'n': cg})
    assert res == PJC(X), res
    eqi = w.s([], 'eqid', '%s = %s' % (PDEFC, PDEFC))
    r = famcl(w, ph, u, X)
    return w.s([eqi, st, xfz, r['p3']], 'fvmptd3', '( %s -> ( %s ` %s ) = %s )' % (ph, PDEFC, X, PJC(X))), r


def pjk(w, ph, u, r, j):
    """( ph -> ( PJC(j) ` K ) = AJ(j) ), ( ... ` J ) = BJ(j), ( ... ` I' ) = CJ(j)"""
    P2 = UPDT(UPDT('D', 'K', AJ(j)), 'J', BJ(j))
    k1 = updn(w, ph, P2, "I'", CJ(j), 'K', u['tv'], r['p2'], u["dI'"], r['cjv'], u['dK'], w.s([u['nik']], 'necomd', "( %s -> K =/= I' )" % ph) if False else None) if False else None
    k1 = updn(w, ph, P2, "I'", CJ(j), 'K', u['tv'], r['p2'], u["dI'"], r['cjv'], u['dK'], u['kni'])
    k2 = updn(w, ph, UPDT('D', 'K', AJ(j)), 'J', BJ(j), 'K', u['tv'], r['p1'], u['dJ'], r['bjv'], u['dK'], u['knj'])
    k3 = updk(w, ph, 'D', 'K', AJ(j), u['tv'], u['dd'], u['dK'], r['ajv'])
    ka = w.s([k1, k2], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` K ) )' % (ph, PJC(j), UPDT('D', 'K', AJ(j))))
    kb = w.s([ka, k3], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, PJC(j), AJ(j)))
    j1 = updn(w, ph, P2, "I'", CJ(j), 'J', u['tv'], r['p2'], u["dI'"], r['cjv'], u['dJ'], u['jni'])
    j2 = updk(w, ph, UPDT('D', 'K', AJ(j)), 'J', BJ(j), u['tv'], r['p1'], u['dJ'], r['bjv'])
    jb = w.s([j1, j2], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, PJC(j), BJ(j)))
    ib = updk(w, ph, P2, "I'", CJ(j), u['tv'], r['p2'], u["dI'"], r['cjv'])
    return kb, jb, ib


def tm2lcpyl():
    lab = 'tm2lcpyl'
    ph = PHC
    w = W(lab, 'The loop of ` copyList ` and the final pop: from the stacks after the three '
               'preparatory stages (the reversed list on ` I\' ` , a ` bra ` on ` K ` and on '
               '` J ` ), every entry of ` I\' ` is moved back onto ` K ` and copied onto ` J ` '
               '(~ tm2lfe with the body ~ tm2lcpyb and the invariant the explicit three-stack '
               'family), then the ` bra ` of ` I\' ` is popped (~ tm2lpop ).')
    c = Ctx(w, ph, T_PHC)
    u = common(w, ph, c)
    u['kni'] = c["K =/= I'"]; u['knj'] = c['K =/= J']; u['jni'] = c["J =/= I'"]
    tv, dd = u['tv'], u['dd']
    # ---- the family typing
    pn = '( %s /\\ n e. ( 0 ... %s ) )' % (ph, NLR)
    un = lift_dict(w, ph, u, pn)
    rn = famcl(w, pn, un, 'n')
    pty = w.s([rn['p3']], 'fmptd', '( %s -> %s : ( 0 ... %s ) --> %s )' % (ph, PDEFC, NLR, STK_T))
    # ---- PK
    pj = '( %s /\\ j e. ( 0 ... %s ) )' % (ph, NLR)
    uj = lift_dict(w, ph, u, pj)
    jfz = w.s([], 'simpr', '( %s -> j e. ( 0 ... %s ) )' % (pj, NLR))
    pvj, rj = pvalc(w, pj, uj, 'j', jfz)
    _, _, ibj = pjk(w, pj, uj, rj, 'j')
    k4 = w.s([pvj], 'fveq1d', '( %s -> ( ( %s ` j ) ` I\' ) = ( %s ` I\' ) )' % (pj, PDEFC, PJC('j')))
    k5 = w.s([k4, ibj], 'eqtrd', '( %s -> ( ( %s ` j ) ` I\' ) = %s )' % (pj, PDEFC, CJ('j')))
    PK = 'A. j e. ( 0 ... %s ) ( ( %s ` j ) ` I\' ) = %s' % (NLR, PDEFC, CJ('j'))
    pk = w.s([k5], 'ralrimiva', '( %s -> %s )' % (ph, PK))
    # ---- HB: the body at j e. ( 0 ..^ NLR )
    po = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NLR)
    uo = lift_dict(w, ph, u, po)
    jo = w.s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (po, NLR))
    jfzo = w.s([jo, w.inst('elfzofz')], 'syl', '( %s -> j e. ( 0 ... %s ) )' % (po, NLR))
    j1fzo = w.s([jo, w.inst('fzofzp1')], 'syl', '( %s -> ( j + 1 ) e. ( 0 ... %s ) )' % (po, NLR))
    pvo, ro = pvalc(w, po, uo, 'j', jfzo)
    pvo1, ro1 = pvalc(w, po, uo, '( j + 1 )', j1fzo)
    Pj = '( %s ` j )' % PDEFC; Pj1 = '( %s ` ( j + 1 ) )' % PDEFC
    kbo, jbo, ibo = pjk(w, po, uo, ro, 'j')
    LJ = '( %s ` j )' % REVL
    # ( PJC(j) ` I' ) = ( LJ ++ ( <" 4 "> ++ CJ(j+1) ) )
    ed = w.s([uo['rvl'], jo, w.inst('tm2lencbdrop')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, ENCB(DROP(REVL, 'j')), LJ, ENCB(DROP(REVL, '( j + 1 )'))))
    ed2 = w.s([ed], 'oveq1d', '( %s -> %s = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ ( D ` I\' ) ) )' % (po, CJ('j'), LJ, ENCB(DROP(REVL, '( j + 1 )'))))
    lj = w.s([uo['rvl'], jo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> %s e. %s )' % (po, LJ, WB))
    ljg = wbtog(w, po, LJ, lj)
    c4 = s1g(w, po, '4')
    dr1 = w.s([uo['rvl'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (po, DROP(REVL, '( j + 1 )'), WWB))
    ec1 = w.s([dr1, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (po, ENCB(DROP(REVL, '( j + 1 )')), WG))
    c4e = ccatg(w, po, '<" 4 ">', ENCB(DROP(REVL, '( j + 1 )')), c4, ec1)
    X1 = CJ('( j + 1 )')
    as1 = w.s([ljg, c4e, uo['diw'], w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ ( D ` I\' ) ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` I\' ) ) ) )' % (po, LJ, ENCB(DROP(REVL, '( j + 1 )')), LJ, ENCB(DROP(REVL, '( j + 1 )'))))
    as2 = w.s([c4, ec1, uo['diw'], w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ ( D ` I\' ) ) = ( <" 4 "> ++ %s ) )' % (po, ENCB(DROP(REVL, '( j + 1 )')), X1))
    as3 = w.s([as2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` I\' ) ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, LJ, ENCB(DROP(REVL, '( j + 1 )')), LJ, X1))
    ed3 = w.s([ed2, as1], 'eqtrd', '( %s -> %s = ( %s ++ ( ( <" 4 "> ++ %s ) ++ ( D ` I\' ) ) ) )' % (po, CJ('j'), LJ, ENCB(DROP(REVL, '( j + 1 )'))))
    ed4 = w.s([ed3, as3], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, CJ('j'), LJ, X1))
    ib2 = w.s([ibo, ed4], 'eqtrd', '( %s -> ( %s ` I\' ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, PJC('j'), LJ, X1))
    x1cl = ro1['cj']
    # tm2lcpyb at D := PJC(j), W := LJ, X := X1
    co = Ctx(w, po, T_PHC, root=w.s([], 'simpl', '( %s -> %s )' % (po, ph)))
    exb = {'%s e. %s' % (PJC('j'), STK_T): ro['p3'], '( %s ` I\' ) = ( %s ++ ( <" 4 "> ++ %s ) )' % (PJC('j'), LJ, X1): ib2,
           '%s e. %s' % (LJ, WB): lj, '%s e. %s' % (X1, WG): x1cl}
    bldb = Builder(w, po, co, exb)
    sb, cb = inst(w, po, 'tm2lcpyb', {'D': PJC('j'), 'W': LJ, 'X': X1}, bldb)
    Cb0, Db1, Bb = triple_parts(cb)
    assert Cb0 == CL('B0', SS, PJC('j')), Cb0
    WKj = '( %s ++ ( <" 4 "> ++ ( %s ` K ) ) )' % (LJ, PJC('j'))
    WJj = '( %s ++ ( <" 4 "> ++ ( %s ` J ) ) )' % (LJ, PJC('j'))
    POSTe = UPDT(UPDT(UPDT(PJC('j'), "I'", X1), 'K', WKj), 'J', WJj)
    assert Db1 == CL('C0', SS, POSTe), Db1
    # ENT( RPC(j+1) ) = ( LJ ++ ( <" 4 "> ++ ENT( RPC(j) ) ) )
    ps1 = w.s([uo['rvl'], jo, w.inst('tm2lpfxs1')], 'syl2anc', '( %s -> %s = ( %s ++ <" %s "> ) )' % (po, PFX(REVL, '( j + 1 )'), PFX(REVL, 'j'), LJ))
    rv1 = w.s([ps1], 'fveq2d', '( %s -> %s = ( reverse ` ( %s ++ <" %s "> ) ) )' % (po, RPC('( j + 1 )'), PFX(REVL, 'j'), LJ))
    pfc = w.s([uo['rvl'], w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (po, PFX(REVL, 'j'), WWB))
    ljs = w.s([lj], 's1cld', '( %s -> <" %s "> e. %s )' % (po, LJ, WWB))
    rc = w.s([pfc, ljs, w.inst('revccat')], 'syl2anc', '( %s -> ( reverse ` ( %s ++ <" %s "> ) ) = ( ( reverse ` <" %s "> ) ++ %s ) )' % (po, PFX(REVL, 'j'), LJ, LJ, RPC('j')))
    rs = w.s([], 'revs1', '( reverse ` <" %s "> ) = <" %s ">' % (LJ, LJ))
    rs2 = w.s([rs], 'oveq1i', '( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s )' % (LJ, RPC('j'), LJ, RPC('j')))
    rs2a = w.s([rs2], 'a1i', '( %s -> ( ( reverse ` <" %s "> ) ++ %s ) = ( <" %s "> ++ %s ) )' % (po, LJ, RPC('j'), LJ, RPC('j')))
    rv2 = w.s([rv1, rc], 'eqtrd', '( %s -> %s = ( ( reverse ` <" %s "> ) ++ %s ) )' % (po, RPC('( j + 1 )'), LJ, RPC('j')))
    rv3 = w.s([rv2, rs2a], 'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (po, RPC('( j + 1 )'), LJ, RPC('j')))
    en1 = w.s([rv3], 'fveq2d', '( %s -> %s = %s )' % (po, ENT(RPC('( j + 1 )')), ENT('( <" %s "> ++ %s )' % (LJ, RPC('j')))))
    en2 = w.s([lj, ro['rpc'], w.inst('tm2lentcons')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, ENT('( <" %s "> ++ %s )' % (LJ, RPC('j'))), LJ, ENT(RPC('j'))))
    en3 = w.s([en1, en2], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, ENT(RPC('( j + 1 )')), LJ, ENT(RPC('j'))))
    c4en = ccatg(w, po, '<" 4 ">', ENT(RPC('j')), c4, ro['ent'])
    def wordstep(Z, zcl, AJx, AJx1):
        """( LJ ++ ( <" 4 "> ++ ( ENT(RPC j) ++ Z ) ) ) = ( ENT(RPC(j+1)) ++ Z )"""
        b1 = w.s([ljg, c4en, zcl, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ %s ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ %s ) ) )' % (po, LJ, ENT(RPC('j')), Z, LJ, ENT(RPC('j')), Z))
        b2 = w.s([c4, ro['ent'], zcl, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ %s ) = ( <" 4 "> ++ %s ) )' % (po, ENT(RPC('j')), Z, AJx))
        b3 = w.s([b2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ %s ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, LJ, ENT(RPC('j')), Z, LJ, AJx))
        b4 = w.s([en3], 'oveq1d', '( %s -> %s = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ %s ) )' % (po, AJx1, LJ, ENT(RPC('j')), Z))
        b5 = w.s([b4, b1], 'eqtrd', '( %s -> %s = ( %s ++ ( ( <" 4 "> ++ %s ) ++ %s ) ) )' % (po, AJx1, LJ, ENT(RPC('j')), Z))
        b6 = w.s([b5, b3], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, AJx1, LJ, AJx))
        return w.s([b6], 'eqcomd', '( %s -> ( %s ++ ( <" 4 "> ++ %s ) ) = %s )' % (po, LJ, AJx, AJx1))
    wa = wordstep('( <" 2 "> ++ R )', uo['c2r'], AJ('j'), AJ('( j + 1 )'))
    wb = wordstep('( <" 2 "> ++ ( D ` J ) )', uo['c2j'], BJ('j'), BJ('( j + 1 )'))
    # POSTe -> PJC(j+1)
    st1, r1 = w.rewrite(POSTe, {'( %s ` K )' % PJC('j'): (AJ('j'), kbo), '( %s ` J )' % PJC('j'): (BJ('j'), jbo)}, po)
    POST2 = UPDT(UPDT(UPDT(PJC('j'), "I'", X1), 'K', '( %s ++ ( <" 4 "> ++ %s ) )' % (LJ, AJ('j'))), 'J', '( %s ++ ( <" 4 "> ++ %s ) )' % (LJ, BJ('j')))
    assert r1 == POST2, r1
    st2, r2 = w.rewrite(POST2, {'( %s ++ ( <" 4 "> ++ %s ) )' % (LJ, AJ('j')): (AJ('( j + 1 )'), wa), '( %s ++ ( <" 4 "> ++ %s ) )' % (LJ, BJ('j')): (BJ('( j + 1 )'), wb)}, po)
    POST3 = UPDT(UPDT(UPDT(PJC('j'), "I'", X1), 'K', AJ('( j + 1 )')), 'J', BJ('( j + 1 )'))
    assert r2 == POST3, r2
    # the nest: tm2stkup2 on I', tm2stkup3c on K, tm2stkup3 on J
    P2j = UPDT(UPDT('D', 'K', AJ('j')), 'J', BJ('j'))
    cjk = wgk(w, po, CJ('j'), "I'", uo["gI'"], ro['cj'])
    cj1k = wgk(w, po, X1, "I'", uo["gI'"], ro1['cj'])
    ajk = wgk(w, po, AJ('j'), 'K', uo['gK'], ro['aj'])
    aj1k = wgk(w, po, AJ('( j + 1 )'), 'K', uo['gK'], ro1['aj'])
    bjk = wgk(w, po, BJ('j'), 'J', uo['gJ'], ro['bj'])
    bj1k = wgk(w, po, BJ('( j + 1 )'), 'J', uo['gJ'], ro1['bj'])
    tvd = w.s([uo['tv'], uo['dd']], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (po, STK_T))
    u2a = w.s([uo['tv'], ro['p2']], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (po, P2j, STK_T))
    u2b = w.s([cjk, cj1k], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, CJ('j'), GT("I'"), X1, GT("I'")))
    up2 = w.s([u2a, uo["dI'"], u2b, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )' % (po, UPDT(PJC('j'), "I'", X1), UPDT(P2j, "I'", X1)))
    st3, r3 = w.rewrite(POST3, {UPDT(PJC('j'), "I'", X1): (UPDT(P2j, "I'", X1), up2)}, po)
    POST4 = UPDT(UPDT(UPDT(P2j, "I'", X1), 'K', AJ('( j + 1 )')), 'J', BJ('( j + 1 )'))
    assert r3 == POST4, r3
    ne3 = w.s([uo['jni'], uo['njk'], uo['nik']], '3jca', "( %s -> ( J =/= I' /\\ J =/= K /\\ I' =/= K ) )" % po)
    u3a = w.s([tvd, ne3], 'jca', "( %s -> ( ( T e. V /\\ D e. %s ) /\\ ( J =/= I' /\\ J =/= K /\\ I' =/= K ) ) )" % (po, STK_T))
    u3b = w.s([uo['dK'], w.s([ajk, aj1k], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, AJ('j'), GT('K'), AJ('( j + 1 )'), GT('K')))], 'jca',
               '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (po, DG, AJ('j'), GT('K'), AJ('( j + 1 )'), GT('K')))
    u3c = w.s([w.s([uo['dJ'], bjk], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (po, DG, BJ('j'), GT('J'))),
               w.s([uo["dI'"], cj1k], 'jca', '( %s -> ( I\' e. %s /\\ %s e. Word %s ) )' % (po, DG, X1, GT("I'")))], 'jca',
               '( %s -> ( ( J e. %s /\\ %s e. Word %s ) /\\ ( I\' e. %s /\\ %s e. Word %s ) ) )' % (po, DG, BJ('j'), GT('J'), DG, X1, GT("I'")))
    NEST3 = UPDT(UPDT(UPDT('D', 'K', AJ('( j + 1 )')), 'J', BJ('j')), "I'", X1)
    up3c = w.s([u3a, u3b, u3c, w.inst('tm2stkup3c')], 'syl3anc', '( %s -> %s = %s )' % (po, UPDT(UPDT(P2j, "I'", X1), 'K', AJ('( j + 1 )')), NEST3))
    st4, r4 = w.rewrite(POST4, {UPDT(UPDT(P2j, "I'", X1), 'K', AJ('( j + 1 )')): (NEST3, up3c)}, po)
    POST5 = UPDT(NEST3, 'J', BJ('( j + 1 )'))
    assert r4 == POST5, r4
    DK1 = UPDT('D', 'K', AJ('( j + 1 )'))
    u4a = w.s([w.s([uo['tv'], ro1['p1']], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (po, DK1, STK_T)), uo['jni']], 'jca',
               '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ J =/= I\' ) )' % (po, DK1, STK_T))
    u4b = w.s([uo['dJ'], w.s([bjk, bj1k], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, BJ('j'), GT('J'), BJ('( j + 1 )'), GT('J')))], 'jca',
               '( %s -> ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (po, DG, BJ('j'), GT('J'), BJ('( j + 1 )'), GT('J')))
    u4c = w.s([uo["dI'"], cj1k], 'jca', '( %s -> ( I\' e. %s /\\ %s e. Word %s ) )' % (po, DG, X1, GT("I'")))
    up3 = w.s([u4a, u4b, u4c, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )' % (po, POST5, PJC('( j + 1 )')))
    st5 = w.s([st1, st2], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, POST3))
    st6 = w.s([st5, st3], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, POST4))
    st7 = w.s([st6, st4], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, POST5))
    st8 = w.s([st7, up3], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, PJC('( j + 1 )')))
    pvo1r = w.s([pvo1], 'eqcomd', '( %s -> %s = %s )' % (po, PJC('( j + 1 )'), Pj1))
    st9 = w.s([st8, pvo1r], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, Pj1))
    pvor = w.s([pvo], 'eqcomd', '( %s -> %s = %s )' % (po, PJC('j'), Pj))
    tri2 = hrtransport(w, po, sb, Cb0, Db1, Bb, CL('B0', SS, Pj), CL('C0', SS, Pj1),
                       eqc=cleq(w, po, 'B0', SS, PJC('j'), Pj, pvor), eqd=cleq(w, po, 'C0', SS, POSTe, Pj1, st9))
    # the bound: ( # ` LJ ) <_ B
    lfn = w.s([uo['rvl'], w.inst('wrdfn')], 'syl', '( %s -> %s Fn ( 0 ..^ %s ) )' % (po, REVL, NLR))
    ljr = w.s([lfn, jo, w.inst('fnfvelrn')], 'syl2anc', '( %s -> %s e. ran %s )' % (po, LJ, REVL))
    rnr = w.s([uo['ll'], w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran L )' % (po, REVL))
    ljr2 = w.s([rnr, ljr], 'sseldd', '( %s -> %s e. ran L )' % (po, LJ))
    cgw, neww = w.wcongr('( # ` w ) <_ B', {'w': LJ}, 'w = %s' % LJ, {'w': w.s([], 'id', '( w = %s -> w = %s )' % (LJ, LJ))})
    lb = w.s([cgw, uo['bw'], ljr2], 'rspcdva', '( %s -> ( # ` %s ) <_ B )' % (po, LJ))
    ln = w.s([lj, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (po, LJ))
    clo = Closure(w, po, {'( # ` %s )' % LJ: ln, 'B': uo['bb']})
    le = linarith(w, po, [lb], '%s <_ %s' % (Bb, YBC), closure=clo)
    ybc = clo.mem(YBC, 'NN0')
    tri3 = hle(w, po, uo['phm'], CL('B0', SS, Pj), CL('C0', SS, Pj1), Bb, YBC, tri2, ybc, le)
    HBF = HR(CL('B0', SS, Pj), 'T', 'M', CL('C0', SS, Pj1), YBC)
    HB = 'A. j e. ( 0 ..^ %s ) %s' % (NLR, HBF)
    hb = w.s([tri3], 'ralrimiva', '( %s -> %s )' % (ph, HB))
    # ---- tm2lfe
    clp = Closure(w, ph, {'B': u['bb']})
    ybn = clp.mem(YBC, 'NN0')
    exf = {'%s C_ %s' % (SS, SS): ssidS(w, ph), '%s e. %s' % (REVL, WWB): u['rvl'], "( D ` I' ) e. %s" % WG: u['diw'],
           '%s e. NN0' % YBC: ybn, '%s : ( 0 ... %s ) --> %s' % (PDEFC, NLR, STK_T): pty, PK: pk, HB: hb}
    bldf = Builder(w, ph, c, exf)
    mf = {'K': "I'", 'N': SS, 'P1': 'J"', 'A': 'A0', "A'": 'B0', 'A"': 'C0', 'E': 'G0', 'L': REVL, 'R': "( D ` I' )", 'Y': YBC, 'P': PDEFC}
    loop, cf = inst(w, ph, 'tm2lfe', mf, bldf)
    Cf0, Df1, Bf = triple_parts(cf)
    P0 = '( %s ` 0 )' % PDEFC; PN = '( %s ` %s )' % (PDEFC, NLR)
    assert Cf0 == CL('J"', SS, P0) and Df1 == CL('G0', NFINS, PN), (Cf0, Df1)
    # ---- ( P ` 0 ) = D3C
    z0fz = w.s([u['nlr'], w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NLR))
    pv0, r0 = pvalc(w, ph, u, '0', z0fz)
    p00 = w.s([], 'pfx00', '%s = (/)' % PFX(REVL, '0'))
    p01 = w.s([p00], 'fveq2i', '%s = ( reverse ` (/) )' % RPC('0'))
    r0i = w.s([], 'rev0', '( reverse ` (/) ) = (/)')
    p02 = w.s([p01, r0i], 'eqtri', '%s = (/)' % RPC('0'))
    p03 = w.s([p02], 'fveq2i', '%s = %s' % (ENT(RPC('0')), ENT('(/)')))
    e0 = w.s([], 'tm2lent0', '%s = (/)' % ENT('(/)'))
    p04 = w.s([p03, e0], 'eqtri', '%s = (/)' % ENT(RPC('0')))
    p05a = w.s([w.s([p04], 'oveq1i', '%s = ( (/) ++ ( <" 2 "> ++ R ) )' % AJ('0'))], 'a1i', '( %s -> %s = ( (/) ++ ( <" 2 "> ++ R ) ) )' % (ph, AJ('0')))
    lida = w.s([u['c2r'], w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ ( <" 2 "> ++ R ) ) = ( <" 2 "> ++ R ) )' % ph)
    a0 = w.s([p05a, lida], 'eqtrd', '( %s -> %s = ( <" 2 "> ++ R ) )' % (ph, AJ('0')))
    p06a = w.s([w.s([p04], 'oveq1i', '%s = ( (/) ++ ( <" 2 "> ++ ( D ` J ) ) )' % BJ('0'))], 'a1i', '( %s -> %s = ( (/) ++ ( <" 2 "> ++ ( D ` J ) ) ) )' % (ph, BJ('0')))
    lidb = w.s([u['c2j'], w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ ( <" 2 "> ++ ( D ` J ) ) ) = ( <" 2 "> ++ ( D ` J ) ) )' % ph)
    b0 = w.s([p06a, lidb], 'eqtrd', '( %s -> %s = ( <" 2 "> ++ ( D ` J ) ) )' % (ph, BJ('0')))
    d0 = w.s([u['rvl'], w.inst('tm2ldrop0')], 'syl', '( %s -> %s = %s )' % (ph, DROP(REVL, '0'), REVL))
    d0b = w.s([d0], 'fveq2d', '( %s -> %s = %s )' % (ph, ENCB(DROP(REVL, '0')), ENCB(REVL)))
    c0 = w.s([d0b], 'oveq1d', '( %s -> %s = %s )' % (ph, CJ('0'), LST(REVL, "( D ` I' )")))
    st0, r0x = w.rewrite(PJC('0'), {AJ('0'): ('( <" 2 "> ++ R )', a0), BJ('0'): ('( <" 2 "> ++ ( D ` J ) )', b0), CJ('0'): (LST(REVL, "( D ` I' )"), c0)}, ph)
    assert r0x == D3C, r0x
    pd = w.s([pv0, st0], 'eqtrd', '( %s -> %s = %s )' % (ph, P0, D3C))
    # ---- ( P ` NLR ) = PNL
    nlfz = w.s([u['nlr'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NLR, NLR))
    pvn, rnl = pvalc(w, ph, u, NLR, nlfz)
    pid = w.s([u['rvl'], w.inst('pfxid')], 'syl', '( %s -> %s = %s )' % (ph, PFX(REVL, NLR), REVL))
    pid2 = w.s([pid], 'fveq2d', '( %s -> %s = ( reverse ` %s ) )' % (ph, RPC(NLR), REVL))
    rr_ = w.s([u['ll'], w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = L )' % (ph, REVL))
    pid3 = w.s([pid2, rr_], 'eqtrd', '( %s -> %s = L )' % (ph, RPC(NLR)))
    pid4 = w.s([pid3], 'fveq2d', '( %s -> %s = %s )' % (ph, ENT(RPC(NLR)), ENT('L')))
    an = w.s([pid4], 'oveq1d', '( %s -> %s = ( %s ++ ( <" 2 "> ++ R ) ) )' % (ph, AJ(NLR), ENT('L')))
    lcc = w.s([u['ll'], u['rr'], w.inst('tm2lencbcc')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 2 "> ++ R ) ) )' % (ph, LST('L', 'R'), ENT('L')))
    an2 = w.s([an, lcc], 'eqtr4d', '( %s -> %s = %s )' % (ph, AJ(NLR), LST('L', 'R')))
    an3 = w.s([an2, u['dk']], 'eqtr4d', '( %s -> %s = ( D ` K ) )' % (ph, AJ(NLR)))
    bn = w.s([pid4], 'oveq1d', '( %s -> %s = ( %s ++ ( <" 2 "> ++ ( D ` J ) ) ) )' % (ph, BJ(NLR), ENT('L')))
    jcc = w.s([u['ll'], u['djw'], w.inst('tm2lencbcc')], 'syl2anc', '( %s -> ( %s ++ ( D ` J ) ) = ( %s ++ ( <" 2 "> ++ ( D ` J ) ) ) )' % (ph, ENCB('L'), ENT('L')))
    YJ = '( %s ++ ( D ` J ) )' % ENCB('L')
    bn2 = w.s([bn, jcc], 'eqtr4d', '( %s -> %s = %s )' % (ph, BJ(NLR), YJ))
    s00 = w.s([], 'swrd00', '%s = (/)' % DROP(REVL, NLR))
    s01 = w.s([s00], 'fveq2i', '%s = %s' % (ENCB(DROP(REVL, NLR)), ENCB('(/)')))
    eb0 = w.s([], 'tm2lencb0', '%s = <" 2 ">' % ENCB('(/)'))
    s02 = w.s([s01, eb0], 'eqtri', '%s = <" 2 ">' % ENCB(DROP(REVL, NLR)))
    s03 = w.s([s02], 'oveq1i', '%s = ( <" 2 "> ++ ( D ` I\' ) )' % CJ(NLR))
    cn = w.s([s03], 'a1i', '( %s -> %s = ( <" 2 "> ++ ( D ` I\' ) ) )' % (ph, CJ(NLR)))
    stn, rn_ = w.rewrite(PJC(NLR), {AJ(NLR): ('( D ` K )', an3), BJ(NLR): (YJ, bn2), CJ(NLR): ('( <" 2 "> ++ ( D ` I\' ) )', cn)}, ph)
    PNL = UPDT(UPDT(UPDT('D', 'K', '( D ` K )'), 'J', YJ), "I'", '( <" 2 "> ++ ( D ` I\' ) )')
    assert rn_ == PNL, rn_
    pvn2 = w.s([pvn, stn], 'eqtrd', '( %s -> %s = %s )' % (ph, PN, PNL))
    loop2 = hrtransport(w, ph, loop, Cf0, Df1, Bf, CL('J"', SS, D3C), CL('G0', NFINS, PNL),
                        eqc=cleq(w, ph, 'J"', SS, P0, D3C, pd), eqd=cleq(w, ph, 'G0', NFINS, PN, PNL, pvn2))
    # ---- the pop
    c2i = ccatg(w, ph, '<" 2 ">', "( D ` I' )", u['c2'], u['diw'])
    ebl = w.s([u['ll'], w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB('L'), WG))
    yj = ccatg(w, ph, ENCB('L'), '( D ` J )', ebl, u['djw'])
    dkk = updcl(w, ph, 'D', 'K', '( D ` K )', tv, dd, u['dK'], u['gK'], u['dkw'])
    DKK = UPDT('D', 'K', '( D ` K )'); DKJ = UPDT(DKK, 'J', YJ)
    dkj = updcl(w, ph, DKK, 'J', YJ, tv, dkk, u['dJ'], u['gJ'], yj)
    pnlcl = updcl(w, ph, DKJ, "I'", '( <" 2 "> ++ ( D ` I\' ) )', tv, dkj, u["dI'"], u["gI'"], c2i)
    c2iv = w.s([c2i], 'elexd', '( %s -> ( <" 2 "> ++ ( D ` I\' ) ) e. _V )' % ph)
    pni = updk(w, ph, DKJ, "I'", '( <" 2 "> ++ ( D ` I\' ) )', tv, dkj, u["dI'"], c2iv)
    nfs = w.s([], 'ssrab2', '%s C_ %s' % (NFINS, SS)); nfsa = w.s([nfs], 'a1i', '( %s -> %s C_ %s )' % (ph, NFINS, SS))
    hp = w.s([nfsa, w.inst('ssralv')], 'syl', "( %s -> ( %s -> A. r e. %s %s e. N' ) )" % (ph, HPOP_AT(SS, "N'"), NFINS, NVF('F"', 'r', '2')))
    hp2 = w.s([hp, c[HPOP_AT(SS, "N'")]], 'mpd', "( %s -> A. r e. %s %s e. N' )" % (ph, NFINS, NVF('F"', 'r', '2')))
    exp = {'%s e. %s' % (PNL, STK_T): pnlcl, '( %s ` I\' ) = ( <" 2 "> ++ ( D ` I\' ) )' % PNL: pni, "2 e. Gamma'": gamlet(w, ph, '2'),
           "( D ` I' ) e. %s" % WG: u['diw'], '%s C_ %s' % (NFINS, SS): nfsa, "A. r e. %s %s e. N'" % (NFINS, NVF('F"', 'r', '2')): hp2}
    bldp = Builder(w, ph, c, exp)
    mp = {'A': 'G0', 'K': "I'", 'F': 'F"', 'N': NFINS, 'D': PNL, 'Z': '2', 'X': "( D ` I' )"}
    pop, cp = triple_parts(inst(w, ph, 'tm2lpop', mp, bldp)[1])[0], None
    popst = w.lines[-1].split(':')[0]
    Cp0, Dp1, Bp = triple_parts(concl(w, ph, popst))
    assert Cp0 == CL('G0', NFINS, PNL), Cp0
    POPD = UPDT(PNL, "I'", "( D ` I' )")
    assert Dp1 == CL('E', "N'", POPD), Dp1
    # collapse: POPD = CFIN
    c2ik = wgk(w, ph, '( <" 2 "> ++ ( D ` I\' ) )', "I'", u["gI'"], c2i)
    dik = wgk(w, ph, "( D ` I' )", "I'", u["gI'"], u['diw'])
    q2a = w.s([tv, dkj], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, DKJ, STK_T))
    q2b = w.s([c2ik, dik], 'jca', '( %s -> ( ( <" 2 "> ++ ( D ` I\' ) ) e. Word %s /\\ ( D ` I\' ) e. Word %s ) )' % (ph, GT("I'"), GT("I'")))
    up2f = w.s([q2a, u["dI'"], q2b, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )' % (ph, POPD, UPDT(DKJ, "I'", "( D ` I' )")))
    upk = w.s([tv, dd, u['dK'], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = D )' % (ph, DKK))
    stq, rq = w.rewrite(UPDT(DKJ, "I'", "( D ` I' )"), {DKK: ('D', upk)}, ph)
    assert rq == UPDT(CFIN, "I'", "( D ` I' )"), rq
    yjv = w.s([yj], 'elexd', '( %s -> %s e. _V )' % (ph, YJ))
    i1 = updn(w, ph, 'D', 'J', YJ, "I'", tv, dd, u['dJ'], yjv, u["dI'"], u['nij'])
    i1r = w.s([i1], 'eqcomd', '( %s -> ( D ` I\' ) = ( %s ` I\' ) )' % (ph, CFIN))
    stq2, rq2 = w.rewrite(rq, {"( D ` I' )": ('( %s ` I\' )' % CFIN, i1r)}, ph)
    cfcl = updcl(w, ph, 'D', 'J', YJ, tv, dd, u['dJ'], u['gJ'], yj)
    upid2 = w.s([tv, cfcl, u["dI'"], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = %s )' % (ph, rq2, CFIN))
    e1 = w.s([up2f, stq], 'eqtrd', '( %s -> %s = %s )' % (ph, POPD, rq))
    e2 = w.s([e1, stq2], 'eqtrd', '( %s -> %s = %s )' % (ph, POPD, rq2))
    e3 = w.s([e2, upid2], 'eqtrd', '( %s -> %s = %s )' % (ph, POPD, CFIN))
    pop2 = hrtransport(w, ph, popst, Cp0, Dp1, Bp, None, CL('E', "N'", CFIN), eqd=cleq(w, ph, 'E', "N'", POPD, CFIN, e3))
    # ---- the chain and the bound
    C0 = CL('J"', SS, D3C); C3 = CL('E', "N'", CFIN)
    q = hseq(w, ph, u['phm'], C0, CL('G0', NFINS, PNL), C3, Bf, '1', loop2, pop2)
    TOT = '( %s + 1 )' % Bf
    rl = w.s([u['ll'], w.inst('revlen')], 'syl', '( %s -> %s = %s )' % (ph, NLR, NL))
    PRR = '( %s x. ( %s + 2 ) )' % (NLR, YBC)
    PR = '( %s x. ( %s + 2 ) )' % (NL, YBC)
    pre = w.s([rl], 'oveq1d', '( %s -> %s = %s )' % (ph, PRR, PR))
    br = w.s([u['bb']], 'nn0red', '( %s -> B e. RR )' % ph)
    i1e = lineq(w, ph, '( %s + 2 )' % YBC, '( ( 4 x. B ) + ; 1 1 )', leaves={'B': br})
    i2e = w.s([i1e], 'oveq2d', '( %s -> %s = ( %s x. ( ( 4 x. B ) + ; 1 1 ) ) )' % (ph, PR, NL))
    pre2 = w.s([pre, i2e], 'eqtrd', '( %s -> %s = ( %s x. ( ( 4 x. B ) + ; 1 1 ) ) )' % (ph, PRR, NL))
    P11 = '( %s x. ( ( 4 x. B ) + ; 1 1 ) )' % NL
    nlr_ = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    clq = Closure(w, ph, {'B': br, NL: nlr_})
    p11r = clq.mem(P11, 'RR')
    t1 = w.s([pre2], 'oveq1d', '( %s -> ( %s + 2 ) = ( %s + 2 ) )' % (ph, PRR, P11))
    t2 = w.s([t1], 'oveq1d', '( %s -> %s = ( ( %s + 2 ) + 1 ) )' % (ph, TOT, P11))
    clq.atom(P11)
    eq = lineq(w, ph, '( ( %s + 2 ) + 1 )' % P11, BCPYL, closure=clq)
    eq2 = w.s([t2, eq], 'eqtrd', '( %s -> %s = %s )' % (ph, TOT, BCPYL))
    o = w.s([eq2], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C3, TOT, C3, BCPYL))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C3, TOT), HR(C0, 'T', 'M', C3, BCPYL)))
    w.qed([b, q], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C3, BCPYL)))
    return w.run()


def tm2lcpy():
    lab = 'tm2lcpy'
    ph = PHC
    w = W(lab, 'The fragment ` copyList ` of TM/Lists.lean: the list on stack ` K ` is copied '
               'onto stack ` J ` (` K ` restored) through the reversal stack ` I\' ` and the '
               'scratch stack ` I ` , both restored.  Lean: ` copyList_runs ` ; ~ tm2lrev2 , two '
               '~ tm2fpshn and ~ tm2lcpyl .')
    c = Ctx(w, ph, T_PHC)
    u = common(w, ph, c)
    tv, dd = u['tv'], u['dd']
    ex = {"I' =/= I": u['nii'], "I' =/= K": u['nik'], '%s C_ %s' % (SS, SS): ssidS(w, ph),
          HPOP_AT(SS, SS): pop_closure(w, ph, 'F"', tv, c[FT('F"')], SS, ssidS(w, ph))}
    bld = Builder(w, ph, c, ex)
    # ---- stage 1: revList K I' I
    s1, c1 = inst(w, ph, 'tm2lrev2', {'J': "I'", 'E': 'H"', 'N': SS, "N'": SS}, bld)
    C0, D1, B1 = triple_parts(c1)
    ERI = LST(REVL, "( D ` I' )")
    DKR = UPDT('D', 'K', 'R')
    D1x = UPDT(DKR, "I'", ERI)
    assert C0 == CL('P0', SS, 'D') and D1 == CL('H"', SS, D1x), (C0, D1)
    ebc = w.s([u['rvl'], w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(REVL), WG))
    eri = ccatg(w, ph, ENCB(REVL), "( D ` I' )", ebc, u['diw'])
    eriv = w.s([eri], 'elexd', '( %s -> %s e. _V )' % (ph, ERI))
    dkrcl = updcl(w, ph, 'D', 'K', 'R', tv, dd, u['dK'], u['gK'], u['rr'])
    d1cl = updcl(w, ph, DKR, "I'", ERI, tv, dkrcl, u["dI'"], u["gI'"], eri)
    # ---- stage 2: push 2 on K
    g2 = gamlet(w, ph, '2')
    ex2 = {'K e. %s' % DG: u['dK'], '2 e. %s' % GT('K'): lgk(w, ph, '2', 'K', u['gK'], g2), '%s e. %s' % (D1x, STK_T): d1cl,
           '%s C_ %s' % (SS, SS): ex['%s C_ %s' % (SS, SS)]}
    bld2 = Builder(w, ph, c, ex2)
    s2, c2 = inst(w, ph, 'tm2fpshn', {'A': 'H"', 'E': 'I"', 'Z': '2', 'N': SS, 'D': D1x}, bld2)
    _, D2, B2 = triple_parts(c2)
    D2x = UPDT(D1x, 'K', '( <" 2 "> ++ ( %s ` K ) )' % D1x)
    assert D2 == CL('I"', SS, D2x), D2
    rv_ = w.s([u['rr']], 'elexd', '( %s -> R e. _V )' % ph)
    k1 = updn(w, ph, DKR, "I'", ERI, 'K', tv, dkrcl, u["dI'"], eriv, u['dK'], c["K =/= I'"])
    k2 = updk(w, ph, 'D', 'K', 'R', tv, dd, u['dK'], rv_)
    k3 = w.s([k1, k2], 'eqtrd', '( %s -> ( %s ` K ) = R )' % (ph, D1x))
    k4 = w.s([k3], 'oveq2d', '( %s -> ( <" 2 "> ++ ( %s ` K ) ) = ( <" 2 "> ++ R ) )' % (ph, D1x))
    st2, r2 = w.rewrite(D2x, {'( <" 2 "> ++ ( %s ` K ) )' % D1x: ('( <" 2 "> ++ R )', k4)}, ph)
    D2y = UPDT(D1x, 'K', '( <" 2 "> ++ R )')
    assert r2 == D2y, r2
    s2b = hrtransport(w, ph, s2, D1, D2, B2, None, CL('I"', SS, D2y), eqd=cleq(w, ph, 'I"', SS, D2x, D2y, st2))
    # ---- stage 3: push 2 on J
    d2cl = updcl(w, ph, D1x, 'K', '( <" 2 "> ++ R )', tv, d1cl, u['dK'], u['gK'], u['c2r'])
    ex3 = {'J e. %s' % DG: u['dJ'], '2 e. %s' % GT('J'): lgk(w, ph, '2', 'J', u['gJ'], g2), '%s e. %s' % (D2y, STK_T): d2cl,
           '%s C_ %s' % (SS, SS): ex['%s C_ %s' % (SS, SS)]}
    bld3 = Builder(w, ph, c, ex3)
    s3, c3 = inst(w, ph, 'tm2fpshn', {'A': 'I"', 'E': 'J"', 'K': 'J', 'Z': '2', 'N': SS, 'D': D2y}, bld3)
    _, D3, B3 = triple_parts(c3)
    D3x = UPDT(D2y, 'J', '( <" 2 "> ++ ( %s ` J ) )' % D2y)
    assert D3 == CL('J"', SS, D3x), D3
    c2rv = w.s([u['c2r']], 'elexd', '( %s -> ( <" 2 "> ++ R ) e. _V )' % ph)
    j1 = updn(w, ph, D1x, 'K', '( <" 2 "> ++ R )', 'J', tv, d1cl, u['dK'], c2rv, u['dJ'], u['njk'])
    j2 = updn(w, ph, DKR, "I'", ERI, 'J', tv, dkrcl, u["dI'"], eriv, u['dJ'], c["J =/= I'"])
    j3 = updn(w, ph, 'D', 'K', 'R', 'J', tv, dd, u['dK'], rv_, u['dJ'], u['njk'])
    j4 = w.s([j1, j2], 'eqtrd', '( %s -> ( %s ` J ) = ( %s ` J ) )' % (ph, D2y, DKR))
    j5 = w.s([j4, j3], 'eqtrd', '( %s -> ( %s ` J ) = ( D ` J ) )' % (ph, D2y))
    j6 = w.s([j5], 'oveq2d', '( %s -> ( <" 2 "> ++ ( %s ` J ) ) = ( <" 2 "> ++ ( D ` J ) ) )' % (ph, D2y))
    st3, r3 = w.rewrite(D3x, {'( <" 2 "> ++ ( %s ` J ) )' % D2y: ('( <" 2 "> ++ ( D ` J ) )', j6)}, ph)
    D3y = UPDT(D2y, 'J', '( <" 2 "> ++ ( D ` J ) )')
    assert r3 == D3y, r3
    # D3y = D3C: tm2stkup3 then tm2stkupc
    rk = wgk(w, ph, 'R', 'K', u['gK'], u['rr'])
    c2rk = wgk(w, ph, '( <" 2 "> ++ R )', 'K', u['gK'], u['c2r'])
    erik = wgk(w, ph, ERI, "I'", u["gI'"], eri)
    c2jj = wgk(w, ph, '( <" 2 "> ++ ( D ` J ) )', 'J', u['gJ'], u['c2j'])
    tvd = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK_T))
    u3a = w.s([tvd, c["K =/= I'"]], 'jca', "( %s -> ( ( T e. V /\\ D e. %s ) /\\ K =/= I' ) )" % (ph, STK_T))
    u3b = w.s([u['dK'], w.s([rk, c2rk], 'jca', '( %s -> ( R e. Word %s /\\ ( <" 2 "> ++ R ) e. Word %s ) )' % (ph, GT('K'), GT('K')))], 'jca',
               '( %s -> ( K e. %s /\\ ( R e. Word %s /\\ ( <" 2 "> ++ R ) e. Word %s ) ) )' % (ph, DG, GT('K'), GT('K')))
    u3c = w.s([u["dI'"], erik], 'jca', '( %s -> ( I\' e. %s /\\ %s e. Word %s ) )' % (ph, DG, ERI, GT("I'")))
    DK2 = UPDT('D', 'K', '( <" 2 "> ++ R )')
    up3 = w.s([u3a, u3b, u3c, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )' % (ph, D2y, UPDT(DK2, "I'", ERI)))
    st4, r4 = w.rewrite(D3y, {D2y: (UPDT(DK2, "I'", ERI), up3)}, ph)
    assert r4 == UPDT(UPDT(DK2, "I'", ERI), 'J', '( <" 2 "> ++ ( D ` J ) )'), r4
    dk2cl = updcl(w, ph, 'D', 'K', '( <" 2 "> ++ R )', tv, dd, u['dK'], u['gK'], u['c2r'])
    uca = w.s([w.s([tv, dk2cl], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, DK2, STK_T)), u['nij']], 'jca',
               "( %s -> ( ( T e. V /\\ %s e. %s ) /\\ I' =/= J ) )" % (ph, DK2, STK_T))
    ucb = w.s([u["dI'"], erik], 'jca', '( %s -> ( I\' e. %s /\\ %s e. Word %s ) )' % (ph, DG, ERI, GT("I'")))
    ucc = w.s([u['dJ'], c2jj], 'jca', '( %s -> ( J e. %s /\\ ( <" 2 "> ++ ( D ` J ) ) e. Word %s ) )' % (ph, DG, GT('J')))
    upc = w.s([uca, ucb, ucc, w.inst('tm2stkupc')], 'syl3anc', '( %s -> %s = %s )' % (ph, r4, D3C))
    e1 = w.s([st3, st4], 'eqtrd', '( %s -> %s = %s )' % (ph, D3x, r4))
    e2 = w.s([e1, upc], 'eqtrd', '( %s -> %s = %s )' % (ph, D3x, D3C))
    s3b = hrtransport(w, ph, s3, CL('I"', SS, D2y), D3, B3, None, CL('J"', SS, D3C), eqd=cleq(w, ph, 'J"', SS, D3x, D3C, e2))
    # ---- stage 4: tm2lcpyl
    C3 = CL('J"', SS, D3C); C4 = CL('E', "N'", CFIN)
    s4 = w.s([], 'tm2lcpyl', '( %s -> %s )' % (ph, HR(C3, 'T', 'M', C4, BCPYL)))
    q1 = hseq(w, ph, u['phm'], C0, D1, CL('I"', SS, D2y), B1, '1', s1, s2b)
    q2 = hseq(w, ph, u['phm'], C0, CL('I"', SS, D2y), C3, '( %s + 1 )' % B1, '1', q1, s3b)
    q3 = hseq(w, ph, u['phm'], C0, C3, C4, '( ( %s + 1 ) + 1 )' % B1, BCPYL, q2, s4)
    TOT = '( ( ( %s + 1 ) + 1 ) + %s )' % (B1, BCPYL)
    br = w.s([u['bb']], 'nn0red', '( %s -> B e. RR )' % ph)
    nlr_ = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    nlc = w.s([u['nl']], 'nn0cnd', '( %s -> %s e. CC )' % (ph, NL))
    clq = Closure(w, ph, {'B': br, NL: nlr_})
    P26 = '( %s x. ( ( 2 x. B ) + 6 ) )' % NL
    P411 = '( %s x. ( ( 4 x. B ) + ; 1 1 ) )' % NL
    P617 = '( %s x. ( ( 6 x. B ) + ; 1 7 ) )' % NL
    i1e = lineq(w, ph, '( ( 6 x. B ) + ; 1 7 )', '( ( ( 2 x. B ) + 6 ) + ( ( 4 x. B ) + ; 1 1 ) )', closure=clq)
    i2e = w.s([i1e], 'oveq2d', '( %s -> %s = ( %s x. ( ( ( 2 x. B ) + 6 ) + ( ( 4 x. B ) + ; 1 1 ) ) ) )' % (ph, P617, NL))
    b6c = w.s([clq.mem('( ( 2 x. B ) + 6 )', 'RR')], 'recnd', '( %s -> ( ( 2 x. B ) + 6 ) e. CC )' % ph)
    b11c = w.s([clq.mem('( ( 4 x. B ) + ; 1 1 )', 'RR')], 'recnd', '( %s -> ( ( 4 x. B ) + ; 1 1 ) e. CC )' % ph)
    dis = w.s([nlc, b6c, b11c, w.inst('adddi')], 'syl3anc', '( %s -> ( %s x. ( ( ( 2 x. B ) + 6 ) + ( ( 4 x. B ) + ; 1 1 ) ) ) = ( %s + %s ) )' % (ph, NL, P26, P411))
    i3e = w.s([i2e, dis], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (ph, P617, P26, P411))
    for a in (P26, P411, P617):
        clq.atom(a)
    eq = lineq(w, ph, TOT, BCPY, hyps=[i3e], closure=clq)
    o = w.s([eq], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C4, TOT, C4, BCPY))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C4, TOT), HR(C0, 'T', 'M', C4, BCPY)))
    w.qed([b, q3], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C4, BCPY)))
    return w.run()


if __name__ == '__main__':
    if want('tm2lcpyb'): tm2lcpyb()
    if want('tm2lcpyl'): tm2lcpyl()
    if want('tm2lcpy'): tm2lcpy()
