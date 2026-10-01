"""T6b: ` listLen ` (blueprint 2.6): the loop and the pop ~ tm2llenl (~ tm2lfe
over the three-stack family with the counter family ` Q ` , the body ~ tm2lme
then the ` incr ` hypothesis ` HINC ` , ~ tm2lpop ), and the composite
~ tm2llen (push ` 4 ` on ` J ` , ~ tm2lrev2 , push ` 2 ` on ` K ` , ~ tm2llenl )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t6blib import *
from cl import Closure
from t6b_e_cpy import common, lift_dict, ssidS

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

NFINN = '{ q e. N | -. ( C ` q ) = 1o }'
YBL = '( ( ( 2 x. B ) + 4 ) + Y )'
BLENL = '( ( %s x. ( ( ( 2 x. B ) + Y ) + 6 ) ) + 3 )' % NL
D3L = UPDT(UPDT(UPDT('D', 'K', '( <" 2 "> ++ R )'), 'J', '( <" 4 "> ++ ( D ` J ) )'), "I'", LST(REVL, "( D ` I' )"))
ST_LENL = '( %s -> %s )' % (PHL, HR(CL('J"', 'N', D3L), 'T', 'M', CL('E', 'N', LFIN), BLENL))


def QJ(j): return '( ( Q ` %s ) ++ ( D ` J ) )' % j
def PJL(j): return UPDT(UPDT(UPDT('D', 'K', AJ(j)), 'J', QJ(j)), "I'", CJ(j))
PDEFL = '( n e. ( 0 ... %s ) |-> %s )' % (NLR, PJL('n'))
PSI = lambda k: ('A. d e. %s ( ( d ` J ) = %s -> %s )'
                 % (STK_T, QJ(k), HR(CL('H0', 'N', 'd'), 'T', 'M', CL('C0', 'N', UPDT('d', 'J', QJ('( %s + 1 )' % k))), 'Y')))
assert HINC == 'A. k e. ( 0 ..^ %s ) %s' % (NL, PSI('k'))


def famcll(w, ph, u, j):
    """closures of AJ(j), QJ(j), CJ(j) and PJL(j)"""
    r = {}
    pf = w.s([u['rvl'], w.inst('pfxcl')], 'syl', '( %s -> %s e. %s )' % (ph, PFX(REVL, j), WWB))
    r['rpc'] = w.s([pf, w.inst('revcl')], 'syl', '( %s -> %s e. %s )' % (ph, RPC(j), WWB))
    r['ent'] = w.s([r['rpc'], w.inst('tm2lentcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENT(RPC(j)), WG))
    r['aj'] = ccatg(w, ph, ENT(RPC(j)), '( <" 2 "> ++ R )', r['ent'], u['c2r'])
    qj = w.s([u['qf'], u['jfz_' + j] if ('jfz_' + j) in u else None], 'ffvelcdmd', '( %s -> ( Q ` %s ) e. %s )' % (ph, j, WG)) if False else None
    r['q'] = w.s([u['qf'], u['jnl'](j)], 'ffvelcdmd', '( %s -> ( Q ` %s ) e. %s )' % (ph, j, WG))
    r['bj'] = ccatg(w, ph, '( Q ` %s )' % j, '( D ` J )', r['q'], u['djw'])
    dr = w.s([u['rvl'], w.inst('swrdcl')], 'syl', '( %s -> %s e. %s )' % (ph, DROP(REVL, j), WWB))
    ec = w.s([dr, w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(DROP(REVL, j)), WG))
    r['cj'] = ccatg(w, ph, ENCB(DROP(REVL, j)), "( D ` I' )", ec, u['diw'])
    r['p1'] = updcl(w, ph, 'D', 'K', AJ(j), u['tv'], u['dd'], u['dK'], u['gK'], r['aj'])
    P2 = UPDT(UPDT('D', 'K', AJ(j)), 'J', QJ(j))
    r['p2'] = updcl(w, ph, UPDT('D', 'K', AJ(j)), 'J', QJ(j), u['tv'], r['p1'], u['dJ'], u['gJ'], r['bj'])
    r['p3'] = updcl(w, ph, P2, "I'", CJ(j), u['tv'], r['p2'], u["dI'"], u["gI'"], r['cj'])
    r['ajv'] = w.s([r['aj']], 'elexd', '( %s -> %s e. _V )' % (ph, AJ(j)))
    r['bjv'] = w.s([r['bj']], 'elexd', '( %s -> %s e. _V )' % (ph, QJ(j)))
    r['cjv'] = w.s([r['cj']], 'elexd', '( %s -> %s e. _V )' % (ph, CJ(j)))
    return r


def pvall(w, ph, u, X, xfz):
    cg = w.s([], 'id', '( n = %s -> n = %s )' % (X, X))
    st, res = w.congr(PJL('n'), {'n': X}, 'n = %s' % X, {'n': cg})
    assert res == PJL(X), res
    eqi = w.s([], 'eqid', '%s = %s' % (PDEFL, PDEFL))
    r = famcll(w, ph, u, X)
    return w.s([eqi, st, xfz, r['p3']], 'fvmptd3', '( %s -> ( %s ` %s ) = %s )' % (ph, PDEFL, X, PJL(X))), r


def pjkl(w, ph, u, r, j):
    P2 = UPDT(UPDT('D', 'K', AJ(j)), 'J', QJ(j))
    k1 = updn(w, ph, P2, "I'", CJ(j), 'K', u['tv'], r['p2'], u["dI'"], r['cjv'], u['dK'], u['kni'])
    k2 = updn(w, ph, UPDT('D', 'K', AJ(j)), 'J', QJ(j), 'K', u['tv'], r['p1'], u['dJ'], r['bjv'], u['dK'], u['knj'])
    k3 = updk(w, ph, 'D', 'K', AJ(j), u['tv'], u['dd'], u['dK'], r['ajv'])
    ka = w.s([k1, k2], 'eqtrd', '( %s -> ( %s ` K ) = ( %s ` K ) )' % (ph, PJL(j), UPDT('D', 'K', AJ(j))))
    kb = w.s([ka, k3], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, PJL(j), AJ(j)))
    j1 = updn(w, ph, P2, "I'", CJ(j), 'J', u['tv'], r['p2'], u["dI'"], r['cjv'], u['dJ'], u['jni'])
    j2 = updk(w, ph, UPDT('D', 'K', AJ(j)), 'J', QJ(j), u['tv'], r['p1'], u['dJ'], r['bjv'])
    jb = w.s([j1, j2], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ph, PJL(j), QJ(j)))
    ib = updk(w, ph, P2, "I'", CJ(j), u['tv'], r['p2'], u["dI'"], r['cjv'])
    return kb, jb, ib


def nlfacts(w, ph, u):
    """the domain conversions ( 0 ... NLR ) = ( 0 ... NL ), ( 0 ..^ NLR ) = ( 0 ..^ NL )"""
    rl = w.s([u['ll'], w.inst('revlen')], 'syl', '( %s -> %s = %s )' % (ph, NLR, NL))
    u['rl'] = rl
    u['fzeq'] = w.s([rl], 'oveq2d', '( %s -> ( 0 ... %s ) = ( 0 ... %s ) )' % (ph, NLR, NL))
    u['fzoeq'] = w.s([rl], 'oveq2d', '( %s -> ( 0 ..^ %s ) = ( 0 ..^ %s ) )' % (ph, NLR, NL))
    def jnl(X):
        """( ph -> X e. ( 0 ... NL ) ) from the stored ( ph -> X e. ( 0 ... NLR ) )"""
        st = u['fz_' + X]
        return w.s([st, u['fzeq']], 'eleqtrd', '( %s -> %s e. ( 0 ... %s ) )' % (ph, X, NL))
    u['jnl'] = jnl
    return u


def tm2llenl():
    lab = 'tm2llenl'
    ph = PHL
    w = W(lab, 'The loop of ` listLen ` and the final pop: from the stacks after the three '
               'preparatory stages, every entry of ` I\' ` is moved back onto ` K ` and the '
               'counter on ` J ` is advanced by the ` incr ` hypothesis (the family ` Q ` , '
               'blueprint decision 4); ~ tm2lfe with the body ~ tm2lme then the hypothesis, '
               'the invariant the explicit three-stack family; then ~ tm2lpop .')
    c = Ctx(w, ph, T_PHL)
    u = common(w, ph, c)
    u['kni'] = c["K =/= I'"]; u['knj'] = c['K =/= J']; u['jni'] = c["J =/= I'"]
    u['qf'] = c['Q : ( 0 ... %s ) --> %s' % (NL, WG)]
    u['q0'] = c['( Q ` 0 ) = <" 4 ">']; u['yy'] = c['Y e. NN0']; u['hinc'] = c[HINC]
    u['nss'] = c['N C_ %s' % SS]
    tv, dd = u['tv'], u['dd']
    nlfacts(w, ph, u)
    # ---- the family typing
    pn = '( %s /\\ n e. ( 0 ... %s ) )' % (ph, NLR)
    un = lift_dict(w, ph, u, pn)
    un['fz_n'] = w.s([], 'simpr', '( %s -> n e. ( 0 ... %s ) )' % (pn, NLR))
    nlfacts(w, pn, un)
    rn = famcll(w, pn, un, 'n')
    pty = w.s([rn['p3']], 'fmptd', '( %s -> %s : ( 0 ... %s ) --> %s )' % (ph, PDEFL, NLR, STK_T))
    # ---- PK
    pj = '( %s /\\ j e. ( 0 ... %s ) )' % (ph, NLR)
    uj = lift_dict(w, ph, u, pj)
    uj['fz_j'] = jfz = w.s([], 'simpr', '( %s -> j e. ( 0 ... %s ) )' % (pj, NLR))
    nlfacts(w, pj, uj)
    pvj, rj = pvall(w, pj, uj, 'j', jfz)
    _, _, ibj = pjkl(w, pj, uj, rj, 'j')
    k4 = w.s([pvj], 'fveq1d', '( %s -> ( ( %s ` j ) ` I\' ) = ( %s ` I\' ) )' % (pj, PDEFL, PJL('j')))
    k5 = w.s([k4, ibj], 'eqtrd', '( %s -> ( ( %s ` j ) ` I\' ) = %s )' % (pj, PDEFL, CJ('j')))
    PK = 'A. j e. ( 0 ... %s ) ( ( %s ` j ) ` I\' ) = %s' % (NLR, PDEFL, CJ('j'))
    pk = w.s([k5], 'ralrimiva', '( %s -> %s )' % (ph, PK))
    # ---- HB
    po = '( %s /\\ j e. ( 0 ..^ %s ) )' % (ph, NLR)
    uo = lift_dict(w, ph, u, po)
    jo = w.s([], 'simpr', '( %s -> j e. ( 0 ..^ %s ) )' % (po, NLR))
    uo['fz_j'] = jfzo = w.s([jo, w.inst('elfzofz')], 'syl', '( %s -> j e. ( 0 ... %s ) )' % (po, NLR))
    uo['fz_( j + 1 )'] = j1fzo = w.s([jo, w.inst('fzofzp1')], 'syl', '( %s -> ( j + 1 ) e. ( 0 ... %s ) )' % (po, NLR))
    nlfacts(w, po, uo)
    jonl = w.s([jo, uo['fzoeq']], 'eleqtrd', '( %s -> j e. ( 0 ..^ %s ) )' % (po, NL))
    pvo, ro = pvall(w, po, uo, 'j', jfzo)
    pvo1, ro1 = pvall(w, po, uo, '( j + 1 )', j1fzo)
    Pj = '( %s ` j )' % PDEFL; Pj1 = '( %s ` ( j + 1 ) )' % PDEFL
    kbo, jbo, ibo = pjkl(w, po, uo, ro, 'j')
    LJ = '( %s ` j )' % REVL
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
    ib2 = w.s([ibo, ed4], 'eqtrd', '( %s -> ( %s ` I\' ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, PJL('j'), LJ, X1))
    x1cl = ro1['cj']
    # stage a: tm2lme at D := PJL(j), moveEntry I' -> K through I, labels B0 D0 E0 F0 -> H0
    co = Ctx(w, po, T_PHL, root=w.s([], 'simpl', '( %s -> %s )' % (po, ph)))
    exa = {'%s e. %s' % (PJL('j'), STK_T): ro['p3'], '( %s ` I\' ) = ( %s ++ ( <" 4 "> ++ %s ) )' % (PJL('j'), LJ, X1): ib2,
           '%s e. %s' % (LJ, WB): lj, '%s e. %s' % (X1, WG): x1cl,
           "I' =/= K": uo['nik'], "I' =/= I": uo['nii']}
    blda = Builder(w, po, co, exa)
    ma = {'K': "I'", 'J': 'K', 'A': 'B0', "A'": 'D0', 'A"': 'E0', "E'": 'F0', 'E': 'H0', 'F': "F'", 'C': "C'",
          'D': PJL('j'), 'W': LJ, 'X': X1}
    sa, ca = inst(w, po, 'tm2lme', ma, blda)
    Ca0, Da1, Ba = triple_parts(ca)
    assert Ca0 == CL('B0', 'N', PJL('j')), Ca0
    WKj = '( %s ++ ( <" 4 "> ++ ( %s ` K ) ) )' % (LJ, PJL('j'))
    DA = UPDT(UPDT(PJL('j'), "I'", X1), 'K', WKj)
    assert Da1 == CL('H0', 'N', DA), Da1
    # stage b: the incr hypothesis at k := j, d := DA
    cgk, psij = w.wcongr(PSI('k'), {'k': 'j'}, 'k = j', {'k': w.s([], 'id', '( k = j -> k = j )')})
    assert psij == PSI('j'), psij
    rk = w.s([cgk], 'rspcv', '( j e. ( 0 ..^ %s ) -> ( %s -> %s ) )' % (NL, HINC, PSI('j')))
    rk2 = w.s([jonl, rk], 'syl', '( %s -> ( %s -> %s ) )' % (po, HINC, PSI('j')))
    rk3 = w.s([rk2, uo['hinc']], 'mpd', '( %s -> %s )' % (po, PSI('j')))
    BODY = lambda dx: '( ( %s ` J ) = %s -> %s )' % (dx, QJ('j'), HR(CL('H0', 'N', dx), 'T', 'M', CL('C0', 'N', UPDT(dx, 'J', QJ('( j + 1 )'))), 'Y'))
    cgd, bodyD = w.wcongr(BODY('d'), {'d': DA}, 'd = %s' % DA, {'d': w.s([], 'id', '( d = %s -> d = %s )' % (DA, DA))})
    assert bodyD == BODY(DA), bodyD
    dacl = updcl(w, po, UPDT(PJL('j'), "I'", X1), 'K', WKj, uo['tv'], updcl(w, po, PJL('j'), "I'", X1, uo['tv'], ro['p3'], uo["dI'"], uo["gI'"], x1cl), uo['dK'], uo['gK'],
                 ccatg(w, po, LJ, '( <" 4 "> ++ ( %s ` K ) )' % PJL('j'), ljg, ccatg(w, po, '<" 4 ">', '( %s ` K )' % PJL('j'), c4, stkfvg(w, po, PJL('j'), 'K', uo['tv'], ro['p3'], uo['dK'], uo['gK']))))
    rd = w.s([cgd], 'rspcv', '( %s e. %s -> ( %s -> %s ) )' % (DA, STK_T, PSI('j'), BODY(DA)))
    rd2 = w.s([dacl, rd], 'syl', '( %s -> ( %s -> %s ) )' % (po, PSI('j'), BODY(DA)))
    rd3 = w.s([rd2, rk3], 'mpd', '( %s -> %s )' % (po, BODY(DA)))
    # ( DA ` J ) = QJ(j)
    x1v = w.s([x1cl], 'elexd', '( %s -> %s e. _V )' % (po, X1))
    wkv = w.s([ccatg(w, po, LJ, '( <" 4 "> ++ ( %s ` K ) )' % PJL('j'), ljg, ccatg(w, po, '<" 4 ">', '( %s ` K )' % PJL('j'), c4, stkfvg(w, po, PJL('j'), 'K', uo['tv'], ro['p3'], uo['dK'], uo['gK'])))], 'elexd', '( %s -> %s e. _V )' % (po, WKj))
    dj1 = updn(w, po, UPDT(PJL('j'), "I'", X1), 'K', WKj, 'J', uo['tv'], updcl(w, po, PJL('j'), "I'", X1, uo['tv'], ro['p3'], uo["dI'"], uo["gI'"], x1cl), uo['dK'], wkv, uo['dJ'], uo['njk'])
    dj2 = updn(w, po, PJL('j'), "I'", X1, 'J', uo['tv'], ro['p3'], uo["dI'"], x1v, uo['dJ'], uo['jni'])
    dj3 = w.s([dj1, dj2], 'eqtrd', '( %s -> ( %s ` J ) = ( %s ` J ) )' % (po, DA, PJL('j')))
    dj4 = w.s([dj3, jbo], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (po, DA, QJ('j')))
    sb = w.s([rd3, dj4], 'mpd', '( %s -> %s )' % (po, HR(CL('H0', 'N', DA), 'T', 'M', CL('C0', 'N', UPDT(DA, 'J', QJ('( j + 1 )'))), 'Y')))
    POSTe = UPDT(DA, 'J', QJ('( j + 1 )'))
    # the word on K
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
    Z = '( <" 2 "> ++ R )'
    b1 = w.s([ljg, c4en, uo['c2r'], w.inst('ccatass')], 'syl3anc', '( %s -> ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ %s ) = ( %s ++ ( ( <" 4 "> ++ %s ) ++ %s ) ) )' % (po, LJ, ENT(RPC('j')), Z, LJ, ENT(RPC('j')), Z))
    b2 = w.s([c4, ro['ent'], uo['c2r'], w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" 4 "> ++ %s ) ++ %s ) = ( <" 4 "> ++ %s ) )' % (po, ENT(RPC('j')), Z, AJ('j')))
    b3 = w.s([b2], 'oveq2d', '( %s -> ( %s ++ ( ( <" 4 "> ++ %s ) ++ %s ) ) = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, LJ, ENT(RPC('j')), Z, LJ, AJ('j')))
    b4 = w.s([en3], 'oveq1d', '( %s -> %s = ( ( %s ++ ( <" 4 "> ++ %s ) ) ++ %s ) )' % (po, AJ('( j + 1 )'), LJ, ENT(RPC('j')), Z))
    b5 = w.s([b4, b1], 'eqtrd', '( %s -> %s = ( %s ++ ( ( <" 4 "> ++ %s ) ++ %s ) ) )' % (po, AJ('( j + 1 )'), LJ, ENT(RPC('j')), Z))
    b6 = w.s([b5, b3], 'eqtrd', '( %s -> %s = ( %s ++ ( <" 4 "> ++ %s ) ) )' % (po, AJ('( j + 1 )'), LJ, AJ('j')))
    wa = w.s([b6], 'eqcomd', '( %s -> ( %s ++ ( <" 4 "> ++ %s ) ) = %s )' % (po, LJ, AJ('j'), AJ('( j + 1 )')))
    # POSTe -> PJL(j+1)
    st1, r1 = w.rewrite(POSTe, {'( %s ` K )' % PJL('j'): (AJ('j'), kbo)}, po)
    POST2 = UPDT(UPDT(UPDT(PJL('j'), "I'", X1), 'K', '( %s ++ ( <" 4 "> ++ %s ) )' % (LJ, AJ('j'))), 'J', QJ('( j + 1 )'))
    assert r1 == POST2, r1
    st2, r2 = w.rewrite(POST2, {'( %s ++ ( <" 4 "> ++ %s ) )' % (LJ, AJ('j')): (AJ('( j + 1 )'), wa)}, po)
    POST3 = UPDT(UPDT(UPDT(PJL('j'), "I'", X1), 'K', AJ('( j + 1 )')), 'J', QJ('( j + 1 )'))
    assert r2 == POST3, r2
    P2j = UPDT(UPDT('D', 'K', AJ('j')), 'J', QJ('j'))
    cjk = wgk(w, po, CJ('j'), "I'", uo["gI'"], ro['cj'])
    cj1k = wgk(w, po, X1, "I'", uo["gI'"], ro1['cj'])
    ajk = wgk(w, po, AJ('j'), 'K', uo['gK'], ro['aj'])
    aj1k = wgk(w, po, AJ('( j + 1 )'), 'K', uo['gK'], ro1['aj'])
    bjk = wgk(w, po, QJ('j'), 'J', uo['gJ'], ro['bj'])
    bj1k = wgk(w, po, QJ('( j + 1 )'), 'J', uo['gJ'], ro1['bj'])
    tvd = w.s([uo['tv'], uo['dd']], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (po, STK_T))
    u2a = w.s([uo['tv'], ro['p2']], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (po, P2j, STK_T))
    u2b = w.s([cjk, cj1k], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, CJ('j'), GT("I'"), X1, GT("I'")))
    up2 = w.s([u2a, uo["dI'"], u2b, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )' % (po, UPDT(PJL('j'), "I'", X1), UPDT(P2j, "I'", X1)))
    st3, r3 = w.rewrite(POST3, {UPDT(PJL('j'), "I'", X1): (UPDT(P2j, "I'", X1), up2)}, po)
    POST4 = UPDT(UPDT(UPDT(P2j, "I'", X1), 'K', AJ('( j + 1 )')), 'J', QJ('( j + 1 )'))
    assert r3 == POST4, r3
    ne3 = w.s([uo['jni'], uo['njk'], uo['nik']], '3jca', "( %s -> ( J =/= I' /\\ J =/= K /\\ I' =/= K ) )" % po)
    u3a = w.s([tvd, ne3], 'jca', "( %s -> ( ( T e. V /\\ D e. %s ) /\\ ( J =/= I' /\\ J =/= K /\\ I' =/= K ) ) )" % (po, STK_T))
    u3b = w.s([uo['dK'], w.s([ajk, aj1k], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, AJ('j'), GT('K'), AJ('( j + 1 )'), GT('K')))], 'jca',
               '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (po, DG, AJ('j'), GT('K'), AJ('( j + 1 )'), GT('K')))
    u3c = w.s([w.s([uo['dJ'], bjk], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (po, DG, QJ('j'), GT('J'))),
               w.s([uo["dI'"], cj1k], 'jca', '( %s -> ( I\' e. %s /\\ %s e. Word %s ) )' % (po, DG, X1, GT("I'")))], 'jca',
               '( %s -> ( ( J e. %s /\\ %s e. Word %s ) /\\ ( I\' e. %s /\\ %s e. Word %s ) ) )' % (po, DG, QJ('j'), GT('J'), DG, X1, GT("I'")))
    NEST3 = UPDT(UPDT(UPDT('D', 'K', AJ('( j + 1 )')), 'J', QJ('j')), "I'", X1)
    up3c = w.s([u3a, u3b, u3c, w.inst('tm2stkup3c')], 'syl3anc', '( %s -> %s = %s )' % (po, UPDT(UPDT(P2j, "I'", X1), 'K', AJ('( j + 1 )')), NEST3))
    st4, r4 = w.rewrite(POST4, {UPDT(UPDT(P2j, "I'", X1), 'K', AJ('( j + 1 )')): (NEST3, up3c)}, po)
    POST5 = UPDT(NEST3, 'J', QJ('( j + 1 )'))
    assert r4 == POST5, r4
    DK1 = UPDT('D', 'K', AJ('( j + 1 )'))
    u4a = w.s([w.s([uo['tv'], ro1['p1']], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (po, DK1, STK_T)), uo['jni']], 'jca',
               '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ J =/= I\' ) )' % (po, DK1, STK_T))
    u4b = w.s([uo['dJ'], w.s([bjk, bj1k], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (po, QJ('j'), GT('J'), QJ('( j + 1 )'), GT('J')))], 'jca',
               '( %s -> ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (po, DG, QJ('j'), GT('J'), QJ('( j + 1 )'), GT('J')))
    u4c = w.s([uo["dI'"], cj1k], 'jca', '( %s -> ( I\' e. %s /\\ %s e. Word %s ) )' % (po, DG, X1, GT("I'")))
    up3 = w.s([u4a, u4b, u4c, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )' % (po, POST5, PJL('( j + 1 )')))
    st5 = w.s([st1, st2], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, POST3))
    st6 = w.s([st5, st3], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, POST4))
    st7 = w.s([st6, st4], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, POST5))
    st8 = w.s([st7, up3], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, PJL('( j + 1 )')))
    pvo1r = w.s([pvo1], 'eqcomd', '( %s -> %s = %s )' % (po, PJL('( j + 1 )'), Pj1))
    st9 = w.s([st8, pvo1r], 'eqtrd', '( %s -> %s = %s )' % (po, POSTe, Pj1))
    pvor = w.s([pvo], 'eqcomd', '( %s -> %s = %s )' % (po, PJL('j'), Pj))
    q = hseq(w, po, uo['phm'], Ca0, Da1, CL('C0', 'N', POSTe), Ba, 'Y', sa, sb)
    tri2 = hrtransport(w, po, q, Ca0, CL('C0', 'N', POSTe), '( %s + Y )' % Ba, CL('B0', 'N', Pj), CL('C0', 'N', Pj1),
                       eqc=cleq(w, po, 'B0', 'N', PJL('j'), Pj, pvor), eqd=cleq(w, po, 'C0', 'N', POSTe, Pj1, st9))
    # the bound
    lfn = w.s([uo['rvl'], w.inst('wrdfn')], 'syl', '( %s -> %s Fn ( 0 ..^ %s ) )' % (po, REVL, NLR))
    ljr = w.s([lfn, jo, w.inst('fnfvelrn')], 'syl2anc', '( %s -> %s e. ran %s )' % (po, LJ, REVL))
    rnr = w.s([uo['ll'], w.inst('tm2lrnrev')], 'syl', '( %s -> ran %s C_ ran L )' % (po, REVL))
    ljr2 = w.s([rnr, ljr], 'sseldd', '( %s -> %s e. ran L )' % (po, LJ))
    cgw, _ = w.wcongr('( # ` w ) <_ B', {'w': LJ}, 'w = %s' % LJ, {'w': w.s([], 'id', '( w = %s -> w = %s )' % (LJ, LJ))})
    lb = w.s([cgw, uo['bw'], ljr2], 'rspcdva', '( %s -> ( # ` %s ) <_ B )' % (po, LJ))
    ln = w.s([lj, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (po, LJ))
    clo = Closure(w, po, {'( # ` %s )' % LJ: ln, 'B': uo['bb'], 'Y': uo['yy']})
    le = linarith(w, po, [lb], '( %s + Y ) <_ %s' % (Ba, YBL), closure=clo)
    ybc = clo.mem(YBL, 'NN0')
    tri3 = hle(w, po, uo['phm'], CL('B0', 'N', Pj), CL('C0', 'N', Pj1), '( %s + Y )' % Ba, YBL, tri2, ybc, le)
    HBF = HR(CL('B0', 'N', Pj), 'T', 'M', CL('C0', 'N', Pj1), YBL)
    HB = 'A. j e. ( 0 ..^ %s ) %s' % (NLR, HBF)
    hb = w.s([tri3], 'ralrimiva', '( %s -> %s )' % (ph, HB))
    # ---- tm2lfe
    clp = Closure(w, ph, {'B': u['bb'], 'Y': u['yy']})
    ybn = clp.mem(YBL, 'NN0')
    exf = {'%s e. %s' % (REVL, WWB): u['rvl'], "( D ` I' ) e. %s" % WG: u['diw'],
           '%s e. NN0' % YBL: ybn, '%s : ( 0 ... %s ) --> %s' % (PDEFL, NLR, STK_T): pty, PK: pk, HB: hb}
    bldf = Builder(w, ph, c, exf)
    mf = {'K': "I'", 'P1': 'J"', 'A': 'A0', "A'": 'B0', 'A"': 'C0', 'E': 'G0', 'L': REVL, 'R': "( D ` I' )", 'Y': YBL, 'P': PDEFL}
    loop, cf = inst(w, ph, 'tm2lfe', mf, bldf)
    Cf0, Df1, Bf = triple_parts(cf)
    P0 = '( %s ` 0 )' % PDEFL; PN = '( %s ` %s )' % (PDEFL, NLR)
    assert Cf0 == CL('J"', 'N', P0) and Df1 == CL('G0', NFINN, PN), (Cf0, Df1)
    # ---- ( P ` 0 ) = D3L
    z0fz = w.s([u['nlr'], w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NLR))
    u['fz_0'] = z0fz
    pv0, r0 = pvall(w, ph, u, '0', z0fz)
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
    q0 = w.s([u['q0']], 'oveq1d', '( %s -> %s = ( <" 4 "> ++ ( D ` J ) ) )' % (ph, QJ('0')))
    d0 = w.s([u['rvl'], w.inst('tm2ldrop0')], 'syl', '( %s -> %s = %s )' % (ph, DROP(REVL, '0'), REVL))
    d0b = w.s([d0], 'fveq2d', '( %s -> %s = %s )' % (ph, ENCB(DROP(REVL, '0')), ENCB(REVL)))
    c0 = w.s([d0b], 'oveq1d', '( %s -> %s = %s )' % (ph, CJ('0'), LST(REVL, "( D ` I' )")))
    st0, r0x = w.rewrite(PJL('0'), {AJ('0'): ('( <" 2 "> ++ R )', a0), QJ('0'): ('( <" 4 "> ++ ( D ` J ) )', q0), CJ('0'): (LST(REVL, "( D ` I' )"), c0)}, ph)
    assert r0x == D3L, r0x
    pd = w.s([pv0, st0], 'eqtrd', '( %s -> %s = %s )' % (ph, P0, D3L))
    # ---- ( P ` NLR ) = PNL
    nlfz = w.s([u['nlr'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NLR, NLR))
    u['fz_' + NLR] = nlfz
    pvn, rnl = pvall(w, ph, u, NLR, nlfz)
    pid = w.s([u['rvl'], w.inst('pfxid')], 'syl', '( %s -> %s = %s )' % (ph, PFX(REVL, NLR), REVL))
    pid2 = w.s([pid], 'fveq2d', '( %s -> %s = ( reverse ` %s ) )' % (ph, RPC(NLR), REVL))
    rr_ = w.s([u['ll'], w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = L )' % (ph, REVL))
    pid3 = w.s([pid2, rr_], 'eqtrd', '( %s -> %s = L )' % (ph, RPC(NLR)))
    pid4 = w.s([pid3], 'fveq2d', '( %s -> %s = %s )' % (ph, ENT(RPC(NLR)), ENT('L')))
    an = w.s([pid4], 'oveq1d', '( %s -> %s = ( %s ++ ( <" 2 "> ++ R ) ) )' % (ph, AJ(NLR), ENT('L')))
    lcc = w.s([u['ll'], u['rr'], w.inst('tm2lencbcc')], 'syl2anc', '( %s -> %s = ( %s ++ ( <" 2 "> ++ R ) ) )' % (ph, LST('L', 'R'), ENT('L')))
    an2 = w.s([an, lcc], 'eqtr4d', '( %s -> %s = %s )' % (ph, AJ(NLR), LST('L', 'R')))
    an3 = w.s([an2, u['dk']], 'eqtr4d', '( %s -> %s = ( D ` K ) )' % (ph, AJ(NLR)))
    qn = w.s([u['rl']], 'fveq2d', '( %s -> ( Q ` %s ) = ( Q ` %s ) )' % (ph, NLR, NL))
    qn2 = w.s([qn], 'oveq1d', '( %s -> %s = %s )' % (ph, QJ(NLR), QJ(NL)))
    s00 = w.s([], 'swrd00', '%s = (/)' % DROP(REVL, NLR))
    s01 = w.s([s00], 'fveq2i', '%s = %s' % (ENCB(DROP(REVL, NLR)), ENCB('(/)')))
    eb0 = w.s([], 'tm2lencb0', '%s = <" 2 ">' % ENCB('(/)'))
    s02 = w.s([s01, eb0], 'eqtri', '%s = <" 2 ">' % ENCB(DROP(REVL, NLR)))
    s03 = w.s([s02], 'oveq1i', '%s = ( <" 2 "> ++ ( D ` I\' ) )' % CJ(NLR))
    cn = w.s([s03], 'a1i', '( %s -> %s = ( <" 2 "> ++ ( D ` I\' ) ) )' % (ph, CJ(NLR)))
    stn, rn_ = w.rewrite(PJL(NLR), {AJ(NLR): ('( D ` K )', an3), QJ(NLR): (QJ(NL), qn2), CJ(NLR): ('( <" 2 "> ++ ( D ` I\' ) )', cn)}, ph)
    PNL = UPDT(UPDT(UPDT('D', 'K', '( D ` K )'), 'J', QJ(NL)), "I'", '( <" 2 "> ++ ( D ` I\' ) )')
    assert rn_ == PNL, rn_
    pvn2 = w.s([pvn, stn], 'eqtrd', '( %s -> %s = %s )' % (ph, PN, PNL))
    loop2 = hrtransport(w, ph, loop, Cf0, Df1, Bf, CL('J"', 'N', D3L), CL('G0', NFINN, PNL),
                        eqc=cleq(w, ph, 'J"', 'N', P0, D3L, pd), eqd=cleq(w, ph, 'G0', NFINN, PN, PNL, pvn2))
    # ---- the pop
    c2i = ccatg(w, ph, '<" 2 ">', "( D ` I' )", u['c2'], u['diw'])
    u['fz_' + NL] = w.s([u['nl'], w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NL))
    u['fz_' + NL] = w.s([u['fz_' + NL], w.s([u['fzeq']], 'eqcomd', '( %s -> ( 0 ... %s ) = ( 0 ... %s ) )' % (ph, NL, NLR))], 'eleqtrrd' if False else 'eleqtrd', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL, NLR))
    qnl = w.s([u['qf'], u['jnl'](NL)], 'ffvelcdmd', '( %s -> ( Q ` %s ) e. %s )' % (ph, NL, WG))
    yj = ccatg(w, ph, '( Q ` %s )' % NL, '( D ` J )', qnl, u['djw'])
    YJ = QJ(NL)
    dkk = updcl(w, ph, 'D', 'K', '( D ` K )', tv, dd, u['dK'], u['gK'], u['dkw'])
    DKK = UPDT('D', 'K', '( D ` K )'); DKJ = UPDT(DKK, 'J', YJ)
    dkj = updcl(w, ph, DKK, 'J', YJ, tv, dkk, u['dJ'], u['gJ'], yj)
    pnlcl = updcl(w, ph, DKJ, "I'", '( <" 2 "> ++ ( D ` I\' ) )', tv, dkj, u["dI'"], u["gI'"], c2i)
    c2iv = w.s([c2i], 'elexd', '( %s -> ( <" 2 "> ++ ( D ` I\' ) ) e. _V )' % ph)
    pni = updk(w, ph, DKJ, "I'", '( <" 2 "> ++ ( D ` I\' ) )', tv, dkj, u["dI'"], c2iv)
    nfs = w.s([], 'ssrab2', '%s C_ N' % NFINN); nfsa = w.s([nfs], 'a1i', '( %s -> %s C_ N )' % (ph, NFINN))
    nfss = w.s([nfsa, u['nss']], 'sstrd', '( %s -> %s C_ %s )' % (ph, NFINN, SS))
    hp = w.s([nfsa, w.inst('ssralv')], 'syl', "( %s -> ( %s -> A. r e. %s %s e. N ) )" % (ph, HPOPN, NFINN, NVF('F"', 'r', '2')))
    hp2 = w.s([hp, c[HPOPN]], 'mpd', "( %s -> A. r e. %s %s e. N )" % (ph, NFINN, NVF('F"', 'r', '2')))
    exp = {'%s e. %s' % (PNL, STK_T): pnlcl, '( %s ` I\' ) = ( <" 2 "> ++ ( D ` I\' ) )' % PNL: pni, "2 e. Gamma'": gamlet(w, ph, '2'),
           "( D ` I' ) e. %s" % WG: u['diw'], '%s C_ %s' % (NFINN, SS): nfss, "A. r e. %s %s e. N" % (NFINN, NVF('F"', 'r', '2')): hp2}
    bldp = Builder(w, ph, c, exp)
    mp = {'A': 'G0', 'K': "I'", 'F': 'F"', 'N': NFINN, "N'": 'N', 'D': PNL, 'Z': '2', 'X': "( D ` I' )"}
    popst, cp = inst(w, ph, 'tm2lpop', mp, bldp)
    Cp0, Dp1, Bp = triple_parts(cp)
    POPD = UPDT(PNL, "I'", "( D ` I' )")
    assert Cp0 == CL('G0', NFINN, PNL) and Dp1 == CL('E', 'N', POPD), (Cp0, Dp1)
    c2ik = wgk(w, ph, '( <" 2 "> ++ ( D ` I\' ) )', "I'", u["gI'"], c2i)
    dik = wgk(w, ph, "( D ` I' )", "I'", u["gI'"], u['diw'])
    q2a = w.s([tv, dkj], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, DKJ, STK_T))
    q2b = w.s([c2ik, dik], 'jca', '( %s -> ( ( <" 2 "> ++ ( D ` I\' ) ) e. Word %s /\\ ( D ` I\' ) e. Word %s ) )' % (ph, GT("I'"), GT("I'")))
    up2f = w.s([q2a, u["dI'"], q2b, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )' % (ph, POPD, UPDT(DKJ, "I'", "( D ` I' )")))
    upk = w.s([tv, dd, u['dK'], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = D )' % (ph, DKK))
    stq, rq = w.rewrite(UPDT(DKJ, "I'", "( D ` I' )"), {DKK: ('D', upk)}, ph)
    assert rq == UPDT(LFIN, "I'", "( D ` I' )"), rq
    yjv = w.s([yj], 'elexd', '( %s -> %s e. _V )' % (ph, YJ))
    i1 = updn(w, ph, 'D', 'J', YJ, "I'", tv, dd, u['dJ'], yjv, u["dI'"], u['nij'])
    i1r = w.s([i1], 'eqcomd', '( %s -> ( D ` I\' ) = ( %s ` I\' ) )' % (ph, LFIN))
    stq2, rq2 = w.rewrite(rq, {"( D ` I' )": ('( %s ` I\' )' % LFIN, i1r)}, ph)
    cfcl = updcl(w, ph, 'D', 'J', YJ, tv, dd, u['dJ'], u['gJ'], yj)
    upid2 = w.s([tv, cfcl, u["dI'"], w.inst('tm2stkupid')], 'syl3anc', '( %s -> %s = %s )' % (ph, rq2, LFIN))
    e1 = w.s([up2f, stq], 'eqtrd', '( %s -> %s = %s )' % (ph, POPD, rq))
    e2 = w.s([e1, stq2], 'eqtrd', '( %s -> %s = %s )' % (ph, POPD, rq2))
    e3 = w.s([e2, upid2], 'eqtrd', '( %s -> %s = %s )' % (ph, POPD, LFIN))
    pop2 = hrtransport(w, ph, popst, Cp0, Dp1, Bp, None, CL('E', 'N', LFIN), eqd=cleq(w, ph, 'E', 'N', POPD, LFIN, e3))
    # ---- the chain and the bound
    C0 = CL('J"', 'N', D3L); C3 = CL('E', 'N', LFIN)
    q = hseq(w, ph, u['phm'], C0, CL('G0', NFINN, PNL), C3, Bf, '1', loop2, pop2)
    TOT = '( %s + 1 )' % Bf
    PRR = '( %s x. ( %s + 2 ) )' % (NLR, YBL)
    PR = '( %s x. ( %s + 2 ) )' % (NL, YBL)
    pre = w.s([u['rl']], 'oveq1d', '( %s -> %s = %s )' % (ph, PRR, PR))
    br = w.s([u['bb']], 'nn0red', '( %s -> B e. RR )' % ph)
    yr = w.s([u['yy']], 'nn0red', '( %s -> Y e. RR )' % ph)
    i1e = lineq(w, ph, '( %s + 2 )' % YBL, '( ( ( 2 x. B ) + Y ) + 6 )', leaves={'B': br, 'Y': yr})
    i2e = w.s([i1e], 'oveq2d', '( %s -> %s = ( %s x. ( ( ( 2 x. B ) + Y ) + 6 ) ) )' % (ph, PR, NL))
    pre2 = w.s([pre, i2e], 'eqtrd', '( %s -> %s = ( %s x. ( ( ( 2 x. B ) + Y ) + 6 ) ) )' % (ph, PRR, NL))
    P11 = '( %s x. ( ( ( 2 x. B ) + Y ) + 6 ) )' % NL
    nlr_ = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    clq = Closure(w, ph, {'B': br, NL: nlr_, 'Y': yr})
    t1 = w.s([pre2], 'oveq1d', '( %s -> ( %s + 2 ) = ( %s + 2 ) )' % (ph, PRR, P11))
    t2 = w.s([t1], 'oveq1d', '( %s -> %s = ( ( %s + 2 ) + 1 ) )' % (ph, TOT, P11))
    clq.atom(P11)
    eq = lineq(w, ph, '( ( %s + 2 ) + 1 )' % P11, BLENL, closure=clq)
    eq2 = w.s([t2, eq], 'eqtrd', '( %s -> %s = %s )' % (ph, TOT, BLENL))
    o = w.s([eq2], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C3, TOT, C3, BLENL))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C3, TOT), HR(C0, 'T', 'M', C3, BLENL)))
    w.qed([b, q], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C3, BLENL)))
    return w.run()


def tm2llen():
    lab = 'tm2llen'
    ph = PHL
    w = W(lab, 'The fragment ` listLen ` of TM/Lists.lean with the counter as the word '
               'family ` Q ` and the ` incr ` step as a hypothesis (blueprint decision 4): '
               'the number of entries of the list on ` K ` is pushed on ` J ` , ` K ` restored, '
               '` I\' ` and ` I ` restored.  Lean: ` listLen_runs ` ; a push, ~ tm2lrev2 , a push, '
               '~ tm2llenl .')
    c = Ctx(w, ph, T_PHL)
    u = common(w, ph, c)
    tv, dd = u['tv'], u['dd']
    nss = c['N C_ %s' % SS]
    ex = {"I' =/= I": u['nii'], "I' =/= K": u['nik']}
    bld = Builder(w, ph, c, ex)
    g4 = gamlet(w, ph, '4'); g2 = gamlet(w, ph, '2')
    # ---- stage 1: push 4 on J
    ex1 = {'J e. %s' % DG: u['dJ'], '4 e. %s' % GT('J'): lgk(w, ph, '4', 'J', u['gJ'], g4)}
    bld1 = Builder(w, ph, c, ex1)
    s1, c1 = inst(w, ph, 'tm2fpshn', {'A': 'P0', 'E': 'Q0', 'K': 'J', 'Z': '4'}, bld1)
    C0, D1, B1 = triple_parts(c1)
    D1x = UPDT('D', 'J', '( <" 4 "> ++ ( D ` J ) )')
    assert C0 == CL('P0', 'N', 'D') and D1 == CL('Q0', 'N', D1x), (C0, D1)
    c4j = ccatg(w, ph, '<" 4 ">', '( D ` J )', s1g(w, ph, '4'), u['djw'])
    d1cl = updcl(w, ph, 'D', 'J', '( <" 4 "> ++ ( D ` J ) )', tv, dd, u['dJ'], u['gJ'], c4j)
    c4jv = w.s([c4j], 'elexd', '( %s -> ( <" 4 "> ++ ( D ` J ) ) e. _V )' % ph)
    # ---- stage 2: revList K I' I from D1x
    d1k = updn(w, ph, 'D', 'J', '( <" 4 "> ++ ( D ` J ) )', 'K', tv, dd, u['dJ'], c4jv, u['dK'], c['K =/= J'])
    d1k2 = w.s([d1k, u['dk']], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D1x, LST('L', 'R')))
    ex2 = dict(ex)
    ex2['%s e. %s' % (D1x, STK_T)] = d1cl
    ex2['( %s ` K ) = %s' % (D1x, LST('L', 'R'))] = d1k2
    bld2 = Builder(w, ph, c, ex2)
    s2, c2 = inst(w, ph, 'tm2lrev2', {'J': "I'", 'E': 'H"', "N'": 'N', 'P0': 'Q0', 'D': D1x}, bld2)
    _, D2, B2 = triple_parts(c2)
    ERI = LST(REVL, '( %s ` I\' )' % D1x)
    D2x = UPDT(UPDT(D1x, 'K', 'R'), "I'", ERI)
    assert D2 == CL('H"', 'N', D2x), D2
    d1i = updn(w, ph, 'D', 'J', '( <" 4 "> ++ ( D ` J ) )', "I'", tv, dd, u['dJ'], c4jv, u["dI'"], u['nij'])
    d1i2 = w.s([d1i], 'oveq2d', '( %s -> %s = %s )' % (ph, ERI, LST(REVL, "( D ` I' )")))
    ERI2 = LST(REVL, "( D ` I' )")
    st2, r2 = w.rewrite(D2x, {ERI: (ERI2, d1i2)}, ph)
    D2y = UPDT(UPDT(D1x, 'K', 'R'), "I'", ERI2)
    assert r2 == D2y, r2
    s2b = hrtransport(w, ph, s2, D1, D2, B2, None, CL('H"', 'N', D2y), eqd=cleq(w, ph, 'H"', 'N', D2x, D2y, st2))
    # ---- stage 3: push 2 on K from D2y
    ebc = w.s([u['rvl'], w.inst('tm2lencbcl')], 'syl', '( %s -> %s e. %s )' % (ph, ENCB(REVL), WG))
    eri = ccatg(w, ph, ENCB(REVL), "( D ` I' )", ebc, u['diw'])
    eriv = w.s([eri], 'elexd', '( %s -> %s e. _V )' % (ph, ERI2))
    d1kr = updcl(w, ph, D1x, 'K', 'R', tv, d1cl, u['dK'], u['gK'], u['rr'])
    d2cl = updcl(w, ph, UPDT(D1x, 'K', 'R'), "I'", ERI2, tv, d1kr, u["dI'"], u["gI'"], eri)
    ex3 = {'K e. %s' % DG: u['dK'], '2 e. %s' % GT('K'): lgk(w, ph, '2', 'K', u['gK'], g2), '%s e. %s' % (D2y, STK_T): d2cl}
    bld3 = Builder(w, ph, c, ex3)
    s3, c3 = inst(w, ph, 'tm2fpshn', {'A': 'H"', 'E': 'J"', 'Z': '2', 'D': D2y}, bld3)
    _, D3, B3 = triple_parts(c3)
    D3x = UPDT(D2y, 'K', '( <" 2 "> ++ ( %s ` K ) )' % D2y)
    assert D3 == CL('J"', 'N', D3x), D3
    rv_ = w.s([u['rr']], 'elexd', '( %s -> R e. _V )' % ph)
    k1 = updn(w, ph, UPDT(D1x, 'K', 'R'), "I'", ERI2, 'K', tv, d1kr, u["dI'"], eriv, u['dK'], c["K =/= I'"])
    k2 = updk(w, ph, D1x, 'K', 'R', tv, d1cl, u['dK'], rv_)
    k3 = w.s([k1, k2], 'eqtrd', '( %s -> ( %s ` K ) = R )' % (ph, D2y))
    k4 = w.s([k3], 'oveq2d', '( %s -> ( <" 2 "> ++ ( %s ` K ) ) = ( <" 2 "> ++ R ) )' % (ph, D2y))
    st3, r3 = w.rewrite(D3x, {'( <" 2 "> ++ ( %s ` K ) )' % D2y: ('( <" 2 "> ++ R )', k4)}, ph)
    D3y = UPDT(D2y, 'K', '( <" 2 "> ++ R )')
    assert r3 == D3y, r3
    # D3y = D3L: D3y = UPD(UPD(UPD(UPD(D,J,4J),K,R),I',ERI2),K,2R) -> tm2stkup3 -> UPD(UPD(UPD(D,J,4J),K,2R),I',ERI2) -> tm2stkupc inner -> D3L
    rk = wgk(w, ph, 'R', 'K', u['gK'], u['rr'])
    c2rk = wgk(w, ph, '( <" 2 "> ++ R )', 'K', u['gK'], u['c2r'])
    erik = wgk(w, ph, ERI2, "I'", u["gI'"], eri)
    c4jj = wgk(w, ph, '( <" 4 "> ++ ( D ` J ) )', 'J', u['gJ'], c4j)
    u3a = w.s([w.s([tv, d1cl], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D1x, STK_T)), c["K =/= I'"]], 'jca',
               "( %s -> ( ( T e. V /\\ %s e. %s ) /\\ K =/= I' ) )" % (ph, D1x, STK_T))
    u3b = w.s([u['dK'], w.s([rk, c2rk], 'jca', '( %s -> ( R e. Word %s /\\ ( <" 2 "> ++ R ) e. Word %s ) )' % (ph, GT('K'), GT('K')))], 'jca',
               '( %s -> ( K e. %s /\\ ( R e. Word %s /\\ ( <" 2 "> ++ R ) e. Word %s ) ) )' % (ph, DG, GT('K'), GT('K')))
    u3c = w.s([u["dI'"], erik], 'jca', '( %s -> ( I\' e. %s /\\ %s e. Word %s ) )' % (ph, DG, ERI2, GT("I'")))
    D1K2 = UPDT(D1x, 'K', '( <" 2 "> ++ R )')
    up3 = w.s([u3a, u3b, u3c, w.inst('tm2stkup3')], 'syl3anc', '( %s -> %s = %s )' % (ph, D3y, UPDT(D1K2, "I'", ERI2)))
    tvd = w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (ph, STK_T))
    uca = w.s([tvd, u['njk']], 'jca', '( %s -> ( ( T e. V /\\ D e. %s ) /\\ J =/= K ) )' % (ph, STK_T))
    ucb = w.s([u['dJ'], c4jj], 'jca', '( %s -> ( J e. %s /\\ ( <" 4 "> ++ ( D ` J ) ) e. Word %s ) )' % (ph, DG, GT('J')))
    ucc = w.s([u['dK'], c2rk], 'jca', '( %s -> ( K e. %s /\\ ( <" 2 "> ++ R ) e. Word %s ) )' % (ph, DG, GT('K')))
    DK2J = UPDT(UPDT('D', 'K', '( <" 2 "> ++ R )'), 'J', '( <" 4 "> ++ ( D ` J ) )')
    upc = w.s([uca, ucb, ucc, w.inst('tm2stkupc')], 'syl3anc', '( %s -> %s = %s )' % (ph, D1K2, DK2J))
    st4, r4 = w.rewrite(UPDT(D1K2, "I'", ERI2), {D1K2: (DK2J, upc)}, ph)
    assert r4 == D3L, r4
    e1 = w.s([st3, up3], 'eqtrd', '( %s -> %s = %s )' % (ph, D3x, UPDT(D1K2, "I'", ERI2)))
    e2 = w.s([e1, st4], 'eqtrd', '( %s -> %s = %s )' % (ph, D3x, D3L))
    s3b = hrtransport(w, ph, s3, CL('H"', 'N', D2y), D3, B3, None, CL('J"', 'N', D3L), eqd=cleq(w, ph, 'J"', 'N', D3x, D3L, e2))
    # ---- stage 4: tm2llenl
    C3 = CL('J"', 'N', D3L); C4 = CL('E', 'N', LFIN)
    s4 = w.s([], 'tm2llenl', '( %s -> %s )' % (ph, HR(C3, 'T', 'M', C4, BLENL)))
    C1 = D1; C2 = CL('H"', 'N', D2y)
    q1 = hseq(w, ph, u['phm'], C0, C1, C2, '1', B2, s1, s2b)
    q2 = hseq(w, ph, u['phm'], C0, C2, C3, '( 1 + %s )' % B2, '1', q1, s3b)
    q3 = hseq(w, ph, u['phm'], C0, C3, C4, '( ( 1 + %s ) + 1 )' % B2, BLENL, q2, s4)
    TOT = '( ( ( 1 + %s ) + 1 ) + %s )' % (B2, BLENL)
    br = w.s([u['bb']], 'nn0red', '( %s -> B e. RR )' % ph)
    yr = w.s([u['yy'] if 'yy' in u else c['Y e. NN0']], 'nn0red', '( %s -> Y e. RR )' % ph)
    nlr_ = w.s([u['nl']], 'nn0red', '( %s -> %s e. RR )' % (ph, NL))
    nlc = w.s([u['nl']], 'nn0cnd', '( %s -> %s e. CC )' % (ph, NL))
    clq = Closure(w, ph, {'B': br, NL: nlr_, 'Y': yr})
    P26 = '( %s x. ( ( 2 x. B ) + 6 ) )' % NL
    P2Y6 = '( %s x. ( ( ( 2 x. B ) + Y ) + 6 ) )' % NL
    PALL = '( %s x. ( ( ( 4 x. B ) + Y ) + ; 1 2 ) )' % NL
    i1e = lineq(w, ph, '( ( ( 4 x. B ) + Y ) + ; 1 2 )', '( ( ( 2 x. B ) + 6 ) + ( ( ( 2 x. B ) + Y ) + 6 ) )', closure=clq)
    i2e = w.s([i1e], 'oveq2d', '( %s -> %s = ( %s x. ( ( ( 2 x. B ) + 6 ) + ( ( ( 2 x. B ) + Y ) + 6 ) ) ) )' % (ph, PALL, NL))
    b6c = w.s([clq.mem('( ( 2 x. B ) + 6 )', 'RR')], 'recnd', '( %s -> ( ( 2 x. B ) + 6 ) e. CC )' % ph)
    b2yc = w.s([clq.mem('( ( ( 2 x. B ) + Y ) + 6 )', 'RR')], 'recnd', '( %s -> ( ( ( 2 x. B ) + Y ) + 6 ) e. CC )' % ph)
    dis = w.s([nlc, b6c, b2yc, w.inst('adddi')], 'syl3anc', '( %s -> ( %s x. ( ( ( 2 x. B ) + 6 ) + ( ( ( 2 x. B ) + Y ) + 6 ) ) ) = ( %s + %s ) )' % (ph, NL, P26, P2Y6))
    i3e = w.s([i2e, dis], 'eqtrd', '( %s -> %s = ( %s + %s ) )' % (ph, PALL, P26, P2Y6))
    for a in (P26, P2Y6, PALL):
        clq.atom(a)
    eq = lineq(w, ph, TOT, BLEN, hyps=[i3e], closure=clq)
    o = w.s([eq], 'opeq2d', '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, C4, TOT, C4, BLEN))
    b = w.s([o], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, HR(C0, 'T', 'M', C4, TOT), HR(C0, 'T', 'M', C4, BLEN)))
    w.qed([b, q3], 'mpbid', '( %s -> %s )' % (ph, HR(C0, 'T', 'M', C4, BLEN)))
    return w.run()


if __name__ == '__main__':
    if want('tm2llenl'): tm2llenl()
    if want('tm2llen'): tm2llen()
