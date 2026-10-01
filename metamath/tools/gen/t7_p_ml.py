"""T7: the multiplication at the machine (Lean ` mul_runs ` , ` mulC_runs ` ,
` mulC_le_B ` ).

  tmchiun    a Hoare triple from a union of preconditions (indexed)
  tmccans    ` canonNum ` from the class of all states (the union over the
             pinned values of ~ tmccan )
  tmcml*     the instance of ~ tm2fmlv : families, interfaces, the iteration
  tmcml      ` mul_runs `
  tmcmulc    ` mulC_runs `  ,  tmcmulb  ` mulC_le_B `

    MM_DB=sorties/t7.mm python3 tools/gen/t7_p_ml.py [LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7mul import *
from cl import Closure
from lin import linarith, lineq
from t7_l_addx import two_lam_ty
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty, ral_S

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL


def leafof(w, ph, st):
    return formula(w, st)[len('( %s -> ' % ph):-2]


# ------------------------------------------------------------------ tmchiun

def tmchiun():
    lab = 'tmchiun'
    ph = split_imp(ST_HIUN)[0]
    w = W(lab, 'A Hoare triple of the machine layer from an indexed union of preconditions, each with the same '
               'postcondition and bound (the indexed form of ~ tm2hun ).')
    TM = '( T e. V /\\ M e. _V )'
    Z = '( { u | %s } i^i ( TM2Cfg ` T ) )' % BODYU
    ZB = '{ u | %s }' % BODYU
    # closed: ( ( TM /\ tri ) -> C C_ Z )
    Q = '( %s /\\ %s )' % (TM, TRIX)
    q1 = w.s([], 'simpr', '( %s -> %s )' % (Q, TRIX))
    q2 = w.s([], 'simpl', '( %s -> %s )' % (Q, TM))
    q3 = w.s([], 'tm2hrtyp', '( %s -> ( C C_ ( TM2Cfg ` T ) /\\ D C_ ( TM2Cfg ` T ) /\\ N e. NN0 ) )' % Q)
    q4 = w.s([q2, q3, w.inst('tm2hrbr2')], 'syl2anc', '( %s -> ( %s <-> A. u e. C %s ) )' % (Q, TRIX, BODYU))
    q5 = w.s([q4, q1], 'mpbid', '( %s -> A. u e. C %s )' % (Q, BODYU))
    sa = w.s([], 'ssabral', '( C C_ %s <-> A. u e. C %s )' % (ZB, BODYU))
    q6 = w.s([q5, sa], 'sylibr', '( %s -> C C_ %s )' % (Q, ZB))
    q7 = w.s([q3], 'simp1d', '( %s -> C C_ ( TM2Cfg ` T ) )' % Q)
    q8 = w.s([q6, q7], 'ssind', '( %s -> C C_ %s )' % (Q, Z))
    q9 = w.s([q8], 'ex', '( %s -> ( %s -> C C_ %s ) )' % (TM, TRIX, Z))
    q10 = w.s([q9], 'com12', '( %s -> ( %s -> C C_ %s ) )' % (TRIX, TM, Z))
    q11 = w.s([q10], 'ralimi', '( A. x e. A %s -> A. x e. A ( %s -> C C_ %s ) )' % (TRIX, TM, Z))
    q12 = w.s([], 'r19.21v', '( A. x e. A ( %s -> C C_ %s ) <-> ( %s -> A. x e. A C C_ %s ) )' % (TM, Z, TM, Z))
    m1 = w.s([], 'simp3', '( %s -> A. x e. A %s )' % (ph, TRIX))
    m0 = w.s([], 'simp1', '( %s -> %s )' % (ph, PHM))
    tv = w.s([m0], 'simpld', '( %s -> T e. V )' % ph)
    mv = w.s([m0, w.inst('tm2hmvv')], 'syl', '( %s -> M e. _V )' % ph)
    m2 = w.s([tv, mv], 'jca', '( %s -> %s )' % (ph, TM))
    m3 = w.s([m1, q11], 'syl', '( %s -> A. x e. A ( %s -> C C_ %s ) )' % (ph, TM, Z))
    m4 = w.s([m3, q12], 'sylib', '( %s -> ( %s -> A. x e. A C C_ %s ) )' % (ph, TM, Z))
    m5 = w.s([m2, m4], 'mpd', '( %s -> A. x e. A C C_ %s )' % (ph, Z))
    U = 'U_ x e. A C'
    iu = w.s([], 'iunss', '( %s C_ %s <-> A. x e. A C C_ %s )' % (U, Z, Z))
    m6 = w.s([m5, iu], 'sylibr', '( %s -> %s C_ %s )' % (ph, U, Z))
    inn = w.s([], 'inss1', '%s C_ %s' % (Z, ZB))
    inn2 = w.s([], 'inss2', '%s C_ ( TM2Cfg ` T )' % Z)
    u1 = w.s([m6, w.s([inn], 'a1i', '( %s -> %s C_ %s )' % (ph, Z, ZB))], 'sstrd', '( %s -> %s C_ %s )' % (ph, U, ZB))
    u2 = w.s([m6, w.s([inn2], 'a1i', '( %s -> %s C_ ( TM2Cfg ` T ) )' % (ph, Z))], 'sstrd', '( %s -> %s C_ ( TM2Cfg ` T ) )' % (ph, U))
    sa2 = w.s([], 'ssabral', '( %s C_ %s <-> A. u e. %s %s )' % (U, ZB, U, BODYU))
    u3 = w.s([u1, sa2], 'sylib', '( %s -> A. u e. %s %s )' % (ph, U, BODYU))
    m8 = w.s([], 'simp2', '( %s -> ( D C_ ( TM2Cfg ` T ) /\\ N e. NN0 ) )' % ph)
    dd = w.s([m8], 'simpld', '( %s -> D C_ ( TM2Cfg ` T ) )' % ph)
    nn = w.s([m8], 'simprd', '( %s -> N e. NN0 )' % ph)
    ty = w.s([u2, dd, nn], '3jca', '( %s -> ( %s C_ ( TM2Cfg ` T ) /\\ D C_ ( TM2Cfg ` T ) /\\ N e. NN0 ) )' % (ph, U))
    br = w.s([m2, ty, w.inst('tm2hrbr2')], 'syl2anc', '( %s -> ( %s ( T TM2Hoare M ) <. D , N >. <-> A. u e. %s %s ) )' % (ph, U, U, BODYU))
    w.qed([br, u3], 'mpbird', '( %s -> %s ( T TM2Hoare M ) <. D , N >. )' % (ph, U))
    return w.run()


# ------------------------------------------------------------------ tmccans

def tmccans():
    lab = 'tmccans'
    ph = cj(TREE_CAN)
    w = W(lab, '` canonNum x s ` at the machine from any state (Lean ` canonNum_runs ` with its register '
               'conclusions dropped): ~ tmccan at the values ` flag ` , ` cmp ` , ` carry ` of each state, joined '
               'by ~ tmchiun .')
    c = Ctx(w, ph, TREE_CAN)
    mk = machine(w, ph, c, ['K', 'J'])
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    ll, xg, dd = c[WRD('L', '2o')], c[WRD('X', GAM)], c[STKD('D')]
    m = {'O': '( TMfl ` x )', 'Q': '( TMcmp ` x )', 'R': '( TMcar ` x )'}
    NPX = NP(m['O'], m['Q'], m['R'])
    t = w.s([], 'tmccan', '( %s -> %s )' % (ph, tsub_text(CONCL_CAN, m)))
    U = UP('D', 'K', CC(ENL, YX4))
    n = '( ( 2 x. ( # ` L ) ) + 5 )'
    # NP_x C_ S
    s1 = w.s([], 'ssrab2', '%s C_ TMSt' % NPX)
    s2 = w.s([w.s([s1], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NPX)), seq], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NPX))
    ss = clnss(w, ph, 'E', NPX, SS, U, s2)
    # the post configuration class is in Cfg
    tn = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` L ) e. NN0 )' % ph)
    eg = w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ENL))
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    x4 = w.s([w.s([g4], 's1cld', '( %s -> <" 4 "> e. Word Gamma\' )' % ph), xg, w.inst('ccatcl')], 'syl2anc',
             "( %s -> %s e. Word Gamma' )" % (ph, YX4))
    ex = w.s([eg, x4, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, CC(ENL, YX4)))
    uc = updcl(w, ph, 'D', 'K', CC(ENL, YX4), tv, dd, mk['k']['K']['kd'], togk(w, ph, mk, CC(ENL, YX4), 'K', ex))
    ssS = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    cf = cfgcl(w, ph, 'E', SS, U, tv, c[LAB('E')], ssS, uc)
    tx = hrssd(w, ph, phm, t, CLN('A', NPX, 'D'), CLN('E', NPX, U), n, CLN('E', SS, U), ss, cf)
    TRI_X = TRI(CLN('A', NPX, 'D'), CLN('E', SS, U), n)
    ral = w.s([tx], 'ralrimivw', '( %s -> A. x e. TMSt %s )' % (ph, TRI_X))
    ll0 = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    cl = Closure(w, ph, {'( # ` L )': ('NN0', ll0)})
    nn0 = cl.mem(n, 'NN0')
    j2 = w.s([cf, nn0], 'jca', '( %s -> ( %s C_ ( TM2Cfg ` T ) /\\ %s e. NN0 ) )' % (ph, CLN('E', SS, U), n))
    UN = 'U_ x e. TMSt %s' % CLN('A', NPX, 'D')
    hi = w.s([phm, j2, ral, w.inst('tmchiun')], 'syl3anc', '( %s -> %s )' % (ph, TRI(UN, CLN('E', SS, U), n)))
    # C( A , S , D ) C_ the union
    UNP = 'U_ x e. TMSt %s' % NPX
    ydef = lambda y: NP('( TMfl ` %s )' % y, '( TMcmp ` %s )' % y, '( TMcar ` %s )' % y)
    ida = w.s([], 'id', '( x = y -> x = y )')
    cg, new = w.congr(NPX, {'x': 'y'}, 'x = y', {'x': ida})
    assert new == ydef('y'), new
    yy = w.s([], 'id', '( y e. TMSt -> y e. TMSt )')
    fe = lambda f: w.s([], 'eqidd', '( y e. TMSt -> ( %s ` y ) = ( %s ` y ) )' % (ACC[f], ACC[f]))
    cond = lambda t: '( ( TMfl ` %s ) = ( TMfl ` y ) /\\ ( TMcmp ` %s ) = ( TMcmp ` y ) /\\ ( TMcar ` %s ) = ( TMcar ` y ) )' % (t, t, t)
    c3 = w.s([fe('fl'), fe('cmp'), fe('car')], '3jca', '( y e. TMSt -> %s )' % cond('y'))
    yin = rab_in(w, 'y e. TMSt', ydef('y'), cond, 'y', yy, c3)
    s2i = w.s([cg], 'ssiun2s', '( y e. TMSt -> %s C_ %s )' % (ydef('y'), UNP))
    yu = w.s([s2i, yin], 'sseldd', '( y e. TMSt -> y e. %s )' % UNP)
    su = w.s([yu], 'ssriv', 'TMSt C_ %s' % UNP)
    su2 = w.s([seq, w.s([su], 'a1i', '( %s -> TMSt C_ %s )' % (ph, UNP))], 'eqsstrd', '( %s -> ( 2nd ` T ) C_ %s )' % (ph, UNP))
    sd = w.s([], 'ssid', '{ D } C_ { D }')
    x1 = w.s([su2, w.s([sd], 'a1i', '( %s -> { D } C_ { D } )' % ph), w.inst('xpss12')], 'syl2anc',
             '( %s -> ( ( 2nd ` T ) X. { D } ) C_ ( %s X. { D } ) )' % (ph, UNP))
    sl = w.s([], 'ssid', '{ ( inl ` A ) } C_ { ( inl ` A ) }')
    x2 = w.s([w.s([sl], 'a1i', '( %s -> { ( inl ` A ) } C_ { ( inl ` A ) } )' % ph), x1, w.inst('xpss12')], 'syl2anc',
             '( %s -> %s C_ ( { ( inl ` A ) } X. ( %s X. { D } ) ) )' % (ph, CLN('A', SS, 'D'), UNP))
    e1 = w.s([], 'xpiundir', '( %s X. { D } ) = U_ x e. TMSt ( %s X. { D } )' % (UNP, NPX))
    e1b = w.s([e1], 'xpeq2i', '( { ( inl ` A ) } X. ( %s X. { D } ) ) = ( { ( inl ` A ) } X. U_ x e. TMSt ( %s X. { D } ) )' % (UNP, NPX))
    e2 = w.s([], 'xpiundi', '( { ( inl ` A ) } X. U_ x e. TMSt ( %s X. { D } ) ) = %s' % (NPX, UN))
    e3 = w.s([e1b, e2], 'eqtri', '( { ( inl ` A ) } X. ( %s X. { D } ) ) = %s' % (UNP, UN))
    x3 = w.s([x2, w.s([e3], 'a1i', '( %s -> ( { ( inl ` A ) } X. ( %s X. { D } ) ) = %s )' % (ph, UNP, UN))], 'sseqtrd',
             '( %s -> %s C_ %s )' % (ph, CLN('A', SS, 'D'), UN))
    fin = hrssc(w, ph, phm, hi, UN, CLN('E', SS, U), n, CLN('A', SS, 'D'), x3)
    w.lines[-1] = w.lines[-1].replace(w.lines[-1].split(':', 1)[0] + ':', 'qed:', 1)
    return w.run()


# ------------------------------------------------------------------ the families of ~ tm2fmlv

def gkf(w, ph, geq, kk, k):
    """(kd, ge, wge) from geq : GEQ and kk : k e. ( 0 ..^ 8 )"""
    j = w.s([geq, kk], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, GEQ, IDX(k)))
    both = w.s([j, w.inst('tmcgk')], 'syl', "( %s -> ( %s e. %s /\\ %s = Gamma' ) )" % (ph, k, DG, GX(k)))
    kd = w.s([both], 'simpld', '( %s -> %s e. %s )' % (ph, k, DG))
    ge = w.s([both], 'simprd', "( %s -> %s = Gamma' )" % (ph, GX(k)))
    wge = w.s([ge, w.inst('wrdeq')], 'syl', "( %s -> Word %s = Word Gamma' )" % (ph, GX(k)))
    return kd, ge, wge


def famv(w, ph, FAM, body_of, v, i, inn, xex):
    """( ph -> ( FAM ` i ) = body(i) ) for FAM = ( v e. NN0 |-> body(v) )"""
    assert FAM == '( %s e. NN0 |-> %s )' % (v, body_of(v)), (FAM, body_of(v))
    return mval(w, ph, v, 'NN0', body_of, i, inn, xex)


XB = lambda t: '( ( inclBool o. ( ( (/) repeatS %s ) ++ L ) ) ++ ( <" 4 "> ++ X ) )' % t
HB = lambda t, W='W': '( ( inclBool o. %s ) ++ ( <" 4 "> ++ %s ) )' % (ACCN(t), W)
YB = lambda t: '( %s ` ( %s + 1 ) )' % (OPF("L'", 'Y'), t)
NB = lambda t: "if ( %s < ( # ` L' ) , %s , %s )" % (t, NRAL(t), NDA)
UB = lambda t: "if ( %s < ( # ` L' ) , <. 1 , ( L' ` %s ) >. , 4 )" % (t, t)


def wg_ccat(w, ph, A, B, a, b):
    return w.s([a, b, w.inst('ccatcl')], 'syl2anc', "( %s -> ( %s ++ %s ) e. Word Gamma' )" % (ph, A, B))


def four_w(w, ph, X, xg):
    """( ph -> ( <" 4 "> ++ X ) e. Word Gamma' )"""
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    return wg_ccat(w, ph, '<" 4 ">', X, s4, xg)


def xfam(w, ph, t, tn, ll, xg):
    """( ph -> ( XML ` t ) = XB( t ) ), ( ph -> XB( t ) e. Word Gamma' ), ( ph -> rep ++ L e. Word 2o )"""
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    r = w.s([b0, tn, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS %s ) e. Word 2o )' % (ph, t))
    rl = w.s([r, ll, w.inst('ccatcl')], 'syl2anc', '( %s -> ( ( (/) repeatS %s ) ++ L ) e. Word 2o )' % (ph, t))
    ib = w.s([rl, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. ( ( (/) repeatS %s ) ++ L ) ) e. Word Gamma' )" % (ph, t))
    xw = wg_ccat(w, ph, '( inclBool o. ( ( (/) repeatS %s ) ++ L ) )' % t, '( <" 4 "> ++ X )', ib, four_w(w, ph, 'X', xg))
    v = famv(w, ph, XML, XB, 'j', t, tn, elv(w, ph, xw, XB(t)))
    return v, xw, rl


def hfam(w, ph, t, tn, lls, wg, W='W'):
    """( ph -> ( HML ` t ) = HB( t ) ), ( ph -> HB( t ) e. Word Gamma' ), and the tmcacc facts"""
    a = w.s([lls, tn], 'jca', '( %s -> ( %s /\\ %s e. NN0 ) )' % (ph, PH_LL, t))
    acc = w.s([a, w.inst('tmcacc')], 'syl', '( %s -> %s )' % (ph, tsub_text(PACC('N'), {'N': t})))
    pa = parts(w, ph, acc, parse_conj(tsub_text(PACC('N'), {'N': t})))
    aw = pa[WRD(ACCN(t), '2o')]
    ib = w.s([aw, w.inst('bwmapcl')], 'syl', "( %s -> ( inclBool o. %s ) e. Word Gamma' )" % (ph, ACCN(t)))
    hw = wg_ccat(w, ph, '( inclBool o. %s )' % ACCN(t), '( <" 4 "> ++ %s )' % W, ib, four_w(w, ph, W, wg))
    v = famv(w, ph, HMLW(W), lambda x: HB(x, W), 'j', t, tn, elv(w, ph, hw, HB(t, W)))
    return v, hw, pa


def yfam(w, ph, t, tn, ll2, yg):
    """( ph -> ( YML ` t ) = YB( t ) ), ( ph -> YB( t ) e. Word Gamma' )"""
    t1 = '( %s + 1 )' % t
    t1n = w.s([tn], 'peano2nn0d' if False else 'peano2nn0', '( %s -> %s e. NN0 )' % (ph, t1)) if False else \
        w.s([tn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, t1))
    j = w.s([ll2, yg, t1n], '3jca', "( %s -> ( L' e. Word 2o /\\ Y e. Word Gamma' /\\ %s e. NN0 ) )" % (ph, t1))
    ty = tsub_text(ST_OPTY, {'L': "L'", 'X': 'Y', 'N': t1})
    yw = w.s([j, w.inst('tmcopty')], 'syl', '( %s -> %s )' % (ph, split_imp(ty)[1]))
    v = famv(w, ph, YML, YB, 'k', t, tn, elv(w, ph, yw, YB(t)))
    return v, yw


def nfam(w, ph, t, tn):
    """( ph -> ( NML ` t ) = NB( t ) ), ( ph -> NB( t ) C_ TMSt )"""
    s1 = w.s([], 'ssrab2', '%s C_ TMSt' % NRAL(t))
    s2 = w.s([], 'ssrab2', '%s C_ TMSt' % NDA)
    un = w.s([s1, s2], 'unssi', '( %s u. %s ) C_ TMSt' % (NRAL(t), NDA))
    ifs = w.s([], 'ifssun', '%s C_ ( %s u. %s )' % (NB(t), NRAL(t), NDA))
    ss = w.s([ifs, un], 'sstri', '%s C_ TMSt' % NB(t))
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    ex = w.s([sv, ss], 'ssexi', '%s e. _V' % NB(t))
    v = famv(w, ph, NML, NB, 'j', t, tn, w.s([ex], 'a1i', '( %s -> %s e. _V )' % (ph, NB(t))))
    return v, w.s([ss], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NB(t)))


def tmcmlf():
    lab = 'tmcmlf'
    ph = cj(PH_MF)
    w = W(lab, 'The families of the multiplication loop at the machine are typed (Lean ` MulInv ` : the '
               'multiplicand shifted ` i ` times on ` x ` , the multiplier\'s rest on ` y ` , the partial product '
               '` mulGo [] xs ( take i ys ) ` on ` w ` , the registers after the ` i ` -th ` popBit ` ).')
    c = Ctx(w, ph, PH_MF)
    geq, seq = c[GEQ], c[SEQ]
    ll, ll2 = c[WRD('L', '2o')], c[WRD("L'", '2o')]
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph, PH_LL))
    ps = '( %s /\\ i e. ( 0 ... ( # ` L\' ) ) )' % ph
    L_ = Lifter(w, ps, 'adantr')
    ii = w.s([], 'simpr', "( %s -> i e. ( 0 ... ( # ` L' ) ) )" % ps)
    inn = w.s([ii, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    xv, xw, _ = xfam(w, ps, 'i', inn, L_(ll, WRD('L', '2o')), L_(c[WRD('X', GAM)], WRD('X', GAM)))
    yv, yw = yfam(w, ps, 'i', inn, L_(ll2, WRD("L'", '2o')), L_(c[WRD('Y', GAM)], WRD('Y', GAM)))
    hv, hw, _ = hfam(w, ps, 'i', inn, L_(lls, PH_LL), L_(c[WRD('W', GAM)], WRD('W', GAM)))
    nv, ns = nfam(w, ps, 'i', inn)
    out = []
    for k, v, wd, F in [('K', xv, xw, XML), ('J', yv, yw, YML), ('I', hv, hw, HML)]:
        kd, ge, wge = gkf(w, ps, L_(geq, GEQ), L_(c[IDX(k)], IDX(k)), k)
        a = w.s([wd, w.s([v], 'eqcomd', '( %s -> %s = ( %s ` i ) )' % (ps, formula(w, v).split(' = ', 1)[1][:-2], F))], 'eqeltrd' if False else 'eqeltrrd',
                "( %s -> ( %s ` i ) e. Word Gamma' )" % (ps, F)) if False else \
            w.s([v, wd], 'eqeltrd', "( %s -> ( %s ` i ) e. Word Gamma' )" % (ps, F))
        out.append(w.s([a, wge], 'eleqtrrd', '( %s -> ( %s ` i ) e. Word %s )' % (ps, F, GX(k))))
    n1 = w.s([nv, ns], 'eqsstrd', '( %s -> ( %s ` i ) C_ TMSt )' % (ps, NML))
    n2 = w.s([n1, L_(seq, SEQ)], 'sseqtrrd', '( %s -> ( %s ` i ) C_ ( 2nd ` T ) )' % (ps, NML))
    body = FAMML[len("A. i e. ( 0 ... ( # ` L' ) ) "):]
    t3 = w.s(out, '3jca', '( %s -> %s )' % (ps, cj(parse_conj(body)[0])))
    b = w.s([t3, n2], 'jca', '( %s -> %s )' % (ps, body))
    w.qed([b], 'ralrimiva', '( %s -> %s )' % (ph, FAMML))
    return w.run()


def bitN(w, ph, ll2, nn, lt):
    """( ph -> ( L' ` N ) e. 2o ) and ( ph -> N e. ( 0 ..^ ( # ` L' ) ) ) from N e. NN0, N < |L'|"""
    lz = w.s([w.s([ll2, w.inst('lencl')], 'syl', "( %s -> ( # ` L' ) e. NN0 )" % ph)], 'nn0zd', "( %s -> ( # ` L' ) e. ZZ )" % ph)
    e = w.s([], 'elfzo0z', "( N e. ( 0 ..^ ( # ` L' ) ) <-> ( N e. NN0 /\\ ( # ` L' ) e. ZZ /\\ N < ( # ` L' ) ) )")
    fz = w.s([w.s([nn, lz, lt], '3jca', "( %s -> ( N e. NN0 /\\ ( # ` L' ) e. ZZ /\\ N < ( # ` L' ) ) )" % ph), e], 'sylibr',
             "( %s -> N e. ( 0 ..^ ( # ` L' ) ) )" % ph)
    b = w.s([ll2, fz, w.inst('wrdsymbcl')], 'syl2anc', "( %s -> ( L' ` N ) e. 2o )" % ph)
    return b, fz


def tmcmlpb():
    lab = 'tmcmlpb'
    ph = cj(PH_PB)
    w = W(lab, 'The multiplication loop\'s ` popBit y ` at the machine: the ` N ` -th letter of the multiplier\'s '
               'stack is a letter, and ` readBit ` on it leaves every state in the ` N ` -th class of the loop '
               '(Lean ` popBit_runs_bit ` , ` popBit_runs_end ` ).')
    c = Ctx(w, ph, PH_PB)
    seq, ll2 = c[SEQ], c[WRD("L'", '2o')]
    nfz = c["N e. ( 0 ... ( # ` L' ) )"]
    nn = w.s([nfz, w.inst('elfznn0')], 'syl', '( %s -> N e. NN0 )' % ph)
    CND = "N < ( # ` L' )"
    res = []
    for pos in (True, False):
        ps = '( %s /\\ %s%s )' % (ph, '' if pos else '-. ', CND)
        L_ = Lifter(w, ps)
        cc = w.s([], 'simpr', '( %s -> %s%s )' % (ps, '' if pos else '-. ', CND))
        nnp = L_(nn, 'N e. NN0')
        sq = L_(seq, SEQ)
        z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
        # the letter value
        g4 = closed(w, ps, 'gamma4', "4 e. Gamma'")
        rab_ex = lambda R: w.s([w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')], 'rabex', '%s e. _V' % R)
        if pos:
            b, fz = bitN(w, ps, L_(ll2, WRD("L'", '2o')), nnp, cc)
            LET = "<. 1 , ( L' ` N ) >."
            lg = w.s([b, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ps, LET))
            xu = elv(w, ps, lg, LET)
            iu = w.s([cc], 'iftrued', '( %s -> %s = %s )' % (ps, UB('N'), LET))
            NC = NRAL('N')
            inn = w.s([cc], 'iftrued', '( %s -> %s = %s )' % (ps, NB('N'), NC))
            nex = w.s([rab_ex(NC)], 'a1i', '( %s -> %s e. _V )' % (ps, NC))
        else:
            LET = '4'
            lg = g4
            xu = closed(w, ps, '4re', '4 e. RR')
            xu = w.s([xu], 'elexd', '( %s -> 4 e. _V )' % ps)
            iu = w.s([cc], 'iffalsed', '( %s -> %s = 4 )' % (ps, UB('N')))
            NC = NDA
            inn = w.s([cc], 'iffalsed', '( %s -> %s = %s )' % (ps, NB('N'), NC))
            nex = w.s([rab_ex(NC)], 'a1i', '( %s -> %s e. _V )' % (ps, NC))
        ifx = w.s([iu, xu], 'eqeltrd', '( %s -> %s e. _V )' % (ps, UB('N')))
        uv = famv(w, ps, UML, UB, 'j', 'N', nnp, ifx)
        ueq = w.s([uv, iu], 'eqtrd', '( %s -> %s = %s )' % (ps, UN_, LET))
        ug = w.s([ueq, lg], 'eqeltrd', "( %s -> %s e. Gamma' )" % (ps, UN_))
        nx = w.s([inn, nex], 'eqeltrd', '( %s -> %s e. _V )' % (ps, NB('N')))
        nv = famv(w, ps, NML, NB, 'j', 'N', nnp, nx)
        neq = w.s([nv, inn], 'eqtrd', '( %s -> %s = %s )' % (ps, NN_, NC))
        if pos:
            bs = w.s([w.s([w.s([], 'snid', '1 e. { 1 }')], 'a1i', '( %s -> 1 e. { 1 } )' % ps), b], 'opelxpd', '( %s -> %s e. %s )' % (ps, LET, BITS))
            pb = w.s([bs, w.inst('tmcpbi')], 'syl', '( %s -> A. r e. TMSt ( TMrdBit ` <. r , ( inl ` %s ) >. ) e. %s )' % (ps, LET, NRA(LET)))
            o2 = w.s([w.s([], '1ex', '1 e. _V'), w.s([], 'fvex', "( L' ` N ) e. _V"), w.inst('op2ndg')], 'mp2an', "( 2nd ` %s ) = ( L' ` N )" % LET)
            o2a = w.s([o2], 'a1i', "( %s -> ( 2nd ` %s ) = ( L' ` N ) )" % (ps, LET))
            re_, new = w.rewrite(NRA(LET), {"( 2nd ` %s )" % LET: ("( L' ` N )", o2a)}, ps)
            assert new == NC, new
            src = 'A. r e. TMSt ( TMrdBit ` <. r , ( inl ` %s ) >. ) e. %s' % (LET, NRA(LET))
            ce = w.s([re_, neq], 'eqtr4d', '( %s -> %s = %s )' % (ps, NRA(LET), NN_))
            rules = {NRA(LET): (NN_, ce)}
        else:
            pb = closed(w, ps, 'tmcpei', 'A. r e. TMSt ( TMrdBit ` <. r , ( inl ` 4 ) >. ) e. %s' % NDA)
            src = 'A. r e. TMSt ( TMrdBit ` <. r , ( inl ` 4 ) >. ) e. %s' % NDA
            ce = w.s([neq], 'eqcomd', '( %s -> %s = %s )' % (ps, NDA, NN_))
            rules = {NDA: (NN_, ce)}
        rules[LET] = (UN_, w.s([ueq], 'eqcomd', '( %s -> %s = %s )' % (ps, LET, UN_)))
        rules['TMSt'] = ('( 2nd ` T )', w.s([sq], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ps))
        bi, new = w.wcongr(src, {}, ps, {}, rules=rules)
        tgt = 'A. r e. ( 2nd ` T ) ( TMrdBit ` <. r , ( inl ` %s ) >. ) e. %s' % (UN_, NN_)
        assert new == tgt, (new, tgt)
        t = w.s([bi, pb], 'mpbid', '( %s -> %s )' % (ps, tgt))
        res.append(w.s([ug, t], 'jca', "( %s -> ( %s e. Gamma' /\\ %s ) )" % (ps, UN_, tgt)))
    w.qed(res, 'pm2.61dan', ST_MLPB)
    return w.run()


def m_unpack(w, ps, cls_text, cond_fn, m, mm):
    """from mm : ( ps -> m e. { h e. TMSt | cond( h ) } ): ( ps -> m e. TMSt ), ( ps -> cond( m ) )"""
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (m, m))
    cg, new = w.wcongr(cond_fn('h'), {'h': m}, 'h = %s' % m, {'h': idh})
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (m, cls_text, m, cond_fn(m)))
    both = w.s([mm, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ps, m, cond_fn(m)))
    return w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (ps, m)), w.s([both], 'simprd', '( %s -> %s )' % (ps, cond_fn(m)))


def cnot_val(w, ps, m, mem):
    X_of = lambda t: 'if ( ( TMda ` %s ) = 1o , (/) , 1o )' % t
    z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
    xex = ifex_closed(w, ps, '( TMda ` %s ) = 1o' % m, '(/)', '1o', z0, o1)
    return lamval(w, ps, X_of, m, mem, xex), X_of(m)


def tmcmlt():
    lab = 'tmcmlt'
    ph = "( L' e. Word 2o /\\ N e. NN0 )"
    w = W(lab, 'The tests of the multiplication loop on its class family: the loop test ` !da ` holds before the '
               'end of the multiplier and fails after it; the ` ite ` test ` ra = some true ` is the popped bit '
               '(Lean ` mul_runs ` , ` mulBody_runs ` ).')
    ll2 = w.s([], 'simpl', "( %s -> L' e. Word 2o )" % ph)
    nn = w.s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    CND = "N < ( # ` L' )"
    rab_ex = lambda R: w.s([w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')], 'rabex', '%s e. _V' % R)
    def nclass(ps, pos, nnp, cc):
        NC = NRAL('N') if pos else NDA
        inn = w.s([cc], 'iftrued' if pos else 'iffalsed', '( %s -> %s = %s )' % (ps, NB('N'), NC))
        nx = w.s([inn, w.s([rab_ex(NC)], 'a1i', '( %s -> %s e. _V )' % (ps, NC))], 'eqeltrd', '( %s -> %s e. _V )' % (ps, NB('N')))
        nv = famv(w, ps, NML, NB, 'j', 'N', nnp, nx)
        return w.s([nv, inn], 'eqtrd', '( %s -> %s = %s )' % (ps, NN_, NC)), NC
    ncA = lambda t: "( ( TMra ` %s ) = ( inl ` ( L' ` N ) ) /\\ ( TMda ` %s ) = (/) )" % (t, t)
    ncB = lambda t: '( TMda ` %s ) = 1o' % t
    n01 = w.s([w.s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')
    # part 1 and part 3
    ps = '( %s /\\ %s )' % (ph, CND)
    L_ = Lifter(w, ps)
    cc = w.s([], 'simpr', '( %s -> %s )' % (ps, CND))
    neq, NC = nclass(ps, True, L_(nn, 'N e. NN0'), cc)
    pm = '( %s /\\ m e. %s )' % (ps, NN_)
    mm0 = w.s([], 'simpr', '( %s -> m e. %s )' % (pm, NN_))
    mm = w.s([mm0, w.s([neq], 'adantr', '( %s -> %s = %s )' % (pm, NN_, NC))], 'eleqtrd', '( %s -> m e. %s )' % (pm, NC))
    mt, mc = m_unpack(w, pm, NC, ncA, 'm', mm)
    mda = w.s([mc], 'simprd', '( %s -> ( TMda ` m ) = (/) )' % pm)
    v, X = cnot_val(w, pm, 'm', mt)
    nd = w.s([w.s([mda], 'eqeq1d', '( %s -> ( ( TMda ` m ) = 1o <-> (/) = 1o ) )' % pm), w.s([n01], 'a1i', '( %s -> -. (/) = 1o )' % pm)], 'mtbird',
             '( %s -> -. ( TMda ` m ) = 1o )' % pm)
    c1 = w.s([v, w.s([nd], 'iffalsed', '( %s -> %s = 1o )' % (pm, X))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, C0ML))
    p1 = w.s([c1], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (ps, NN_, C0ML))
    P1 = w.s([p1], 'ex', '( %s -> ( %s -> A. m e. %s ( %s ` m ) = 1o ) )' % (ph, CND, NN_, C0ML))
    # part 3
    mra = w.s([mc], 'simpld', "( %s -> ( TMra ` m ) = ( inl ` ( L' ` N ) ) )" % pm)
    outs = []
    for val in ('1o', '(/)'):
        pv = "( %s /\\ ( L' ` N ) = %s )" % (ps, val)
        pvm = '( %s /\\ m e. %s )' % (pv, NN_)
        # re-derive under pvm
        mm0 = w.s([], 'simpr', '( %s -> m e. %s )' % (pvm, NN_))
        mmv = w.s([mm0, w.s([neq], 'ad2antrr', '( %s -> %s = %s )' % (pvm, NN_, NC))], 'eleqtrd', '( %s -> m e. %s )' % (pvm, NC))
        mtv, mcv = m_unpack(w, pvm, NC, ncA, 'm', mmv)
        mrav = w.s([mcv], 'simpld', "( %s -> ( TMra ` m ) = ( inl ` ( L' ` N ) ) )" % pvm)
        lv = w.s([], 'simplr', "( %s -> ( L' ` N ) = %s )" % (pvm, val))
        ra2 = w.s([mrav, w.s([lv], 'fveq2d', "( %s -> ( inl ` ( L' ` N ) ) = ( inl ` %s ) )" % (pvm, val))], 'eqtrd',
                  '( %s -> ( TMra ` m ) = ( inl ` %s ) )' % (pvm, val))
        nvv = {'mem': mtv}
        if val == '1o':
            st, _ = cra_val(w, pvm, nvv, 'm', '1o', ra2)
            r = w.s([st], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pv, NN_, CML))
            outs.append(w.s([r], 'ex', "( %s -> ( ( L' ` N ) = 1o -> A. m e. %s ( %s ` m ) = 1o ) )" % (ps, NN_, CML)))
        else:
            inj = w.s([w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'), w.inst('tmcinl11')], 'mp2an',
                      '( ( inl ` (/) ) = ( inl ` 1o ) <-> (/) = 1o )')
            ni = w.s([inj, n01], 'mtbir', '-. ( inl ` (/) ) = ( inl ` 1o )')
            dn = w.s([w.s([ra2], 'eqeq1d', '( %s -> ( ( TMra ` m ) = ( inl ` 1o ) <-> ( inl ` (/) ) = ( inl ` 1o ) ) )' % pvm),
                      w.s([ni], 'a1i', '( %s -> -. ( inl ` (/) ) = ( inl ` 1o ) )' % pvm)], 'mtbird', '( %s -> -. ( TMra ` m ) = ( inl ` 1o ) )' % pvm)
            st, _ = cra_val(w, pvm, nvv, 'm', '1o', dn)
            n1 = not1o(w, pvm, st, CML, 'm')
            r = w.s([n1], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pv, NN_, CML))
            outs.append(w.s([r], 'ex', "( %s -> ( ( L' ` N ) = (/) -> A. m e. %s -. ( %s ` m ) = 1o ) )" % (ps, NN_, CML)))
    P3i = w.s(outs, 'jca', "( %s -> ( ( ( L' ` N ) = 1o -> A. m e. %s ( %s ` m ) = 1o ) /\\ ( ( L' ` N ) = (/) -> A. m e. %s -. ( %s ` m ) = 1o ) ) )"
              % (ps, NN_, CML, NN_, CML))
    P3 = w.s([P3i], 'ex', "( %s -> ( %s -> ( ( ( L' ` N ) = 1o -> A. m e. %s ( %s ` m ) = 1o ) /\\ ( ( L' ` N ) = (/) -> A. m e. %s -. ( %s ` m ) = 1o ) ) ) )"
             % (ph, CND, NN_, CML, NN_, CML))
    # part 2
    LE = "( # ` L' ) <_ N"
    ps2 = '( %s /\\ %s )' % (ph, LE)
    L2 = Lifter(w, ps2)
    le = w.s([], 'simpr', '( %s -> %s )' % (ps2, LE))
    ln = w.s([w.s([L2(ll2, "L' e. Word 2o"), w.inst('lencl')], 'syl', "( %s -> ( # ` L' ) e. NN0 )" % ps2)], 'nn0red', "( %s -> ( # ` L' ) e. RR )" % ps2)
    nr = w.s([L2(nn, 'N e. NN0')], 'nn0red', '( %s -> N e. RR )' % ps2)
    lnl = w.s([ln, nr], 'lenltd', "( %s -> ( ( # ` L' ) <_ N <-> -. N < ( # ` L' ) ) )" % ps2)
    cc2 = w.s([lnl, le], 'mpbid', '( %s -> -. %s )' % (ps2, CND))
    neq2, NC2 = nclass(ps2, False, L2(nn, 'N e. NN0'), cc2)
    pm2 = '( %s /\\ m e. %s )' % (ps2, NN_)
    m20 = w.s([], 'simpr', '( %s -> m e. %s )' % (pm2, NN_))
    m2 = w.s([m20, w.s([neq2], 'adantr', '( %s -> %s = %s )' % (pm2, NN_, NC2))], 'eleqtrd', '( %s -> m e. %s )' % (pm2, NC2))
    mt2, mc2 = m_unpack(w, pm2, NC2, ncB, 'm', m2)
    v2, X2 = cnot_val(w, pm2, 'm', mt2)
    c2 = w.s([v2, w.s([mc2], 'iftrued', '( %s -> %s = (/) )' % (pm2, X2))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm2, C0ML))
    n2 = not1o(w, pm2, c2, C0ML, 'm')
    p2 = w.s([n2], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (ps2, NN_, C0ML))
    P2 = w.s([p2], 'ex', '( %s -> ( %s -> A. m e. %s -. ( %s ` m ) = 1o ) )' % (ph, LE, NN_, C0ML))
    w.qed([P1, P2, P3], '3jca', ST_MLT)
    return w.run()


def xstep(w, ps, i, inn, ll, xg):
    """( ps -> ( XML ` ( i + 1 ) ) = ( <" <. 1 , (/) >. "> ++ ( XML ` i ) ) )"""
    i1 = '( %s + 1 )' % i
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, i1))
    v1, w1, _ = xfam(w, ps, i1, i1n, ll, xg)
    v0, w0, rl0 = xfam(w, ps, i, inn, ll, xg)
    b0 = closed(w, ps, '0el2o', '(/) e. 2o')
    z0 = closed(w, ps, '0ex', '(/) e. _V')
    one = closed(w, ps, '1nn0', '1 e. NN0')
    rc = w.s([z0, one, inn, w.inst('repswccat')], 'syl3anc', '( %s -> ( ( (/) repeatS 1 ) ++ ( (/) repeatS %s ) ) = ( (/) repeatS ( 1 + %s ) ) )' % (ps, i, i))
    r1 = w.s([z0, w.inst('repsw1')], 'syl', '( %s -> ( (/) repeatS 1 ) = <" (/) "> )' % ps)
    r1b = w.s([r1], 'oveq1d', '( %s -> ( ( (/) repeatS 1 ) ++ ( (/) repeatS %s ) ) = ( <" (/) "> ++ ( (/) repeatS %s ) ) )' % (ps, i, i))
    ic = w.s([w.s([inn], 'nn0cnd', '( %s -> %s e. CC )' % (ps, i)), closed(w, ps, 'ax-1cn', '1 e. CC')], 'addcomd', '( %s -> ( %s + 1 ) = ( 1 + %s ) )' % (ps, i, i))
    rr = w.s([ic], 'oveq2d', '( %s -> ( (/) repeatS ( %s + 1 ) ) = ( (/) repeatS ( 1 + %s ) ) )' % (ps, i, i))
    e1 = w.s([rr, w.s([rc, r1b], 'eqtr3d', '( %s -> ( (/) repeatS ( 1 + %s ) ) = ( <" (/) "> ++ ( (/) repeatS %s ) ) )' % (ps, i, i))], 'eqtrd',
             '( %s -> ( (/) repeatS ( %s + 1 ) ) = ( <" (/) "> ++ ( (/) repeatS %s ) ) )' % (ps, i, i))
    REP = '( (/) repeatS %s )' % i
    rw_ = w.s([b0, one, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS 1 ) e. Word 2o )' % ps) if False else None
    s0 = w.s([b0], 's1cld', '( %s -> <" (/) "> e. Word 2o )' % ps)
    rw = w.s([b0, inn, w.inst('repsw')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, REP))
    e2 = w.s([e1], 'oveq1d', '( %s -> ( ( (/) repeatS ( %s + 1 ) ) ++ L ) = ( ( <" (/) "> ++ %s ) ++ L ) )' % (ps, i, REP))
    ca = w.s([s0, rw, ll, w.inst('ccatass')], 'syl3anc', '( %s -> ( ( <" (/) "> ++ %s ) ++ L ) = ( <" (/) "> ++ ( %s ++ L ) ) )' % (ps, REP, REP))
    e3 = w.s([e2, ca], 'eqtrd', '( %s -> ( ( (/) repeatS ( %s + 1 ) ) ++ L ) = ( <" (/) "> ++ ( %s ++ L ) ) )' % (ps, i, REP))
    e4 = w.s([e3], 'coeq2d', '( %s -> ( inclBool o. ( ( (/) repeatS ( %s + 1 ) ) ++ L ) ) = ( inclBool o. ( <" (/) "> ++ ( %s ++ L ) ) ) )' % (ps, i, REP))
    bc = w.s([b0, rl0, w.inst('bwmapcons')], 'syl2anc', '( %s -> ( inclBool o. ( <" (/) "> ++ ( %s ++ L ) ) ) = ( <" <. 1 , (/) >. "> ++ ( inclBool o. ( %s ++ L ) ) ) )' % (ps, REP, REP))
    IB0 = '( inclBool o. ( %s ++ L ) )' % REP
    e5 = w.s([e4, bc], 'eqtrd', '( %s -> ( inclBool o. ( ( (/) repeatS ( %s + 1 ) ) ++ L ) ) = ( <" <. 1 , (/) >. "> ++ %s ) )' % (ps, i, IB0))
    e6 = w.s([e5], 'oveq1d', '( %s -> %s = ( ( <" <. 1 , (/) >. "> ++ %s ) ++ ( <" 4 "> ++ X ) ) )' % (ps, XB(i1), IB0))
    g0 = w.s([b0, w.inst('bitgamma')], 'syl', "( %s -> <. 1 , (/) >. e. Gamma' )" % ps)
    s0g = w.s([g0], 's1cld', "( %s -> <\" <. 1 , (/) >. \"> e. Word Gamma' )" % ps)
    ibg = w.s([rl0, w.inst('bwmapcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ps, IB0))
    ca2 = w.s([s0g, ibg, four_w(w, ps, 'X', xg), w.inst('ccatass')], 'syl3anc',
              '( %s -> ( ( <" <. 1 , (/) >. "> ++ %s ) ++ ( <" 4 "> ++ X ) ) = ( <" <. 1 , (/) >. "> ++ %s ) )' % (ps, IB0, XB(i)))
    e7 = w.s([e6, ca2], 'eqtrd', '( %s -> %s = ( <" <. 1 , (/) >. "> ++ %s ) )' % (ps, XB(i1), XB(i)))
    e8 = w.s([v0], 'oveq2d', '( %s -> ( <" <. 1 , (/) >. "> ++ ( %s ` %s ) ) = ( <" <. 1 , (/) >. "> ++ %s ) )' % (ps, XML, i, XB(i)))
    return w.s([v1, e7, e8], 'eqtr4d' if False else '3eqtr4d', '( %s -> ( %s ` %s ) = ( <" <. 1 , (/) >. "> ++ ( %s ` %s ) ) )' % (ps, XML, i1, XML, i)) if False else \
        w.s([w.s([v1, e7], 'eqtrd', '( %s -> ( %s ` %s ) = ( <" <. 1 , (/) >. "> ++ %s ) )' % (ps, XML, i1, XB(i))), e8], 'eqtr4d',
            '( %s -> ( %s ` %s ) = ( <" <. 1 , (/) >. "> ++ ( %s ` %s ) ) )' % (ps, XML, i1, XML, i))


def tmcmls():
    lab = 'tmcmls'
    ph = cj(PH_MF)
    w = W(lab, 'The per-iteration facts of the multiplication loop at the machine other than the dispatch: the '
               'multiplier\'s stack pops one letter, the multiplicand\'s gains a ` 0 ` , the loop test holds, and '
               '` popBit ` enters the next class (Lean ` mulBody_runs ` , stages 2 and 3).')
    c = Ctx(w, ph, PH_MF)
    geq, seq = c[GEQ], c[SEQ]
    ll, ll2, xg, yg = c[WRD('L', '2o')], c[WRD("L'", '2o')], c[WRD('X', GAM)], c[WRD('Y', GAM)]
    ps = "( %s /\\ i e. ( 0 ..^ ( # ` L' ) ) )" % ph
    L_ = Lifter(w, ps)
    ii = w.s([], 'simpr', "( %s -> i e. ( 0 ..^ ( # ` L' ) ) )" % ps)
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', "( %s -> i < ( # ` L' ) )" % ps)
    i1 = '( i + 1 )'
    i1f = w.s([ii, w.inst('fzofzp1')], 'syl', "( %s -> %s e. ( 0 ... ( # ` L' ) ) )" % (ps, i1))
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, i1))
    lp = L_(ll2, WRD("L'", '2o'))
    # the y step
    yv0, _ = yfam(w, ps, 'i', inn, lp, L_(yg, WRD('Y', GAM)))
    yv1, _ = yfam(w, ps, i1, i1n, lp, L_(yg, WRD('Y', GAM)))
    j = w.s([lp, L_(yg, WRD('Y', GAM)), i1n], '3jca', "( %s -> ( L' e. Word 2o /\\ Y e. Word Gamma' /\\ %s e. NN0 ) )" % (ps, i1))
    OP1 = tsub_text(ST_OP1, {'L': "L'", 'X': 'Y', 'N': i1})
    o1 = w.s([j, w.inst('tmcop1')], 'syl', '( %s -> %s )' % (ps, split_imp(OP1)[1]))
    OPFY_, OPUY_ = OPF("L'", 'Y'), OPU("L'")
    f1 = '( %s e. %s -> ( %s ` %s ) = ( <" ( %s ` %s ) "> ++ ( %s ` ( %s + 1 ) ) ) )' % (i1, OPR("L'"), OPFY_, i1, OPUY_, i1, OPFY_, i1)
    o1a = w.s([o1], 'simp1d', '( %s -> %s )' % (ps, f1))
    o1b = w.s([i1f, o1a], 'mpd', '( %s -> ( %s ` %s ) = ( <" ( %s ` %s ) "> ++ ( %s ` ( %s + 1 ) ) ) )' % (ps, OPFY_, i1, OPUY_, i1, OPFY_, i1))
    yv1b = w.s([yv1], 'oveq2d', '( %s -> ( <" ( %s ` %s ) "> ++ ( %s ` %s ) ) = ( <" ( %s ` %s ) "> ++ %s ) )' % (ps, UML, i1, YML, i1, UML, i1, YB(i1)))
    ys = w.s([w.s([yv0, o1b], 'eqtrd', '( %s -> ( %s ` i ) = ( <" ( %s ` %s ) "> ++ %s ) )' % (ps, YML, UML, i1, YB(i1))), yv1b], 'eqtr4d',
             '( %s -> ( %s ` i ) = ( <" ( %s ` %s ) "> ++ ( %s ` %s ) ) )' % (ps, YML, UML, i1, YML, i1))
    xs = xstep(w, ps, 'i', inn, L_(ll, WRD('L', '2o')), L_(xg, WRD('X', GAM)))
    # popBit into the next class, the letter in GJ
    pbj = w.s([L_(seq, SEQ), lp, i1f], '3jca', "( %s -> ( %s /\\ L' e. Word 2o /\\ %s e. ( 0 ... ( # ` L' ) ) ) )" % (ps, SEQ, i1))
    PB = tsub_text(ST_MLPB, {'N': i1})
    pb = w.s([pbj, w.inst('tmcmlpb')], 'syl', '( %s -> %s )' % (ps, split_imp(PB)[1]))
    UI1 = '( %s ` %s )' % (UML, i1)
    ug = w.s([pb], 'simpld', "( %s -> %s e. Gamma' )" % (ps, UI1))
    hpb = w.s([pb], 'simprd', '( %s -> %s )' % (ps, split_imp(PB)[1].split(" e. Gamma' /\\ ", 1)[1][:-2]))
    kd, ge, wge = gkf(w, ps, L_(geq, GEQ), L_(c[IDX('J')], IDX('J')), 'J')
    ugj = w.s([ug, ge], 'eleqtrrd', '( %s -> %s e. %s )' % (ps, UI1, GX('J')))
    pP = parse_conj(HYP_P)
    a = w.s([ys, xs], 'jca', '( %s -> %s )' % (ps, cj(pP[0])))
    P = w.s([a, ugj], 'jca', '( %s -> %s )' % (ps, HYP_P))
    # the loop test holds at i
    tj = w.s([lp, inn], 'jca', "( %s -> ( L' e. Word 2o /\\ i e. NN0 ) )" % ps)
    MT = tsub_text(ST_MLT, {'N': 'i'})
    tt = w.s([tj, w.inst('tmcmlt')], 'syl', '( %s -> %s )' % (ps, split_imp(MT)[1]))
    t1 = w.s([tt], 'simp1d', '( %s -> %s )' % (ps, cj(parse_conj(split_imp(MT)[1])[0])))
    ht = w.s([ilt, t1], 'mpd', '( %s -> %s )' % (ps, cj(parse_conj(HYP_Q)[0])))
    Q = w.s([ht, hpb], 'jca', '( %s -> %s )' % (ps, HYP_Q))
    rP = w.s([P], 'ralrimiva', '( %s -> %s )' % (ph, RALI(HYP_P)))
    rQ = w.s([Q], 'ralrimiva', '( %s -> %s )' % (ph, RALI(HYP_Q)))
    w.qed([rP, rQ], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, RALI(HYP_P), RALI(HYP_Q)))
    return w.run()


def split_or(text):
    r"""the two disjuncts of ( A \/ B )"""
    toks = text.split()
    assert toks[0] == '(' and toks[-1] == ')'
    d = 0
    for i, t in enumerate(toks[1:-1], 1):
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        elif t == '\\/' and d == 0:
            return ' '.join(toks[1:i]), ' '.join(toks[i + 1:-1])
    raise ValueError(text)


def dpmf(w, ps, i, tv, dd, kd, ne, hw, xw, yw):
    """DPM( i ) = UPD3( D ; I , ( HML ` i ) ; K , ( XML ` i ) ; J , ( YML ` i ) ): typing and its values at I , K"""
    H_, X_, Y_ = '( %s ` %s )' % (HML, i), '( %s ` %s )' % (XML, i), '( %s ` %s )' % (YML, i)
    U1 = UP('D', 'I', H_); U2 = UP(U1, 'K', X_); U3 = UP(U2, 'J', Y_)
    a = updcl(w, ps, 'D', 'I', H_, tv, dd, kd['I'], hw)
    b = updcl(w, ps, U1, 'K', X_, tv, a, kd['K'], xw)
    d = updcl(w, ps, U2, 'J', Y_, tv, b, kd['J'], yw)
    hv, xv, yv = elv(w, ps, hw, H_), elv(w, ps, xw, X_), elv(w, ps, yw, Y_)
    vk1 = updnv(w, ps, U2, 'J', Y_, 'K', tv, b, kd['J'], yv, kd['K'], ne['K =/= J'])
    vk2 = updkv(w, ps, U1, 'K', X_, tv, a, kd['K'], xv)
    vk = w.s([vk1, vk2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, U3, X_))
    nij = w.s([ne['J =/= I']], 'necomd', '( %s -> I =/= J )' % ps)
    nik = w.s([ne['K =/= I']], 'necomd', '( %s -> I =/= K )' % ps)
    vi1 = updnv(w, ps, U2, 'J', Y_, 'I', tv, b, kd['J'], yv, kd['I'], nij)
    vi2 = updnv(w, ps, U1, 'K', X_, 'I', tv, a, kd['K'], xv, kd['I'], nik)
    vi3 = updkv(w, ps, 'D', 'I', H_, tv, dd, kd['I'], hv)
    vi = w.s([w.s([vi1, vi2], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (ps, U3, U1)), vi3], 'eqtrd',
             '( %s -> ( %s ` I ) = %s )' % (ps, U3, H_))
    return U3, d, vi, vk


def tmcmld():
    lab = 'tmcmld'
    TREE = TREE_MLD()
    ph = cj(TREE)
    w = W(lab, 'The dispatch of the multiplication loop at the machine (Lean ` mulBody ` \'s ` ite ` ): on a set '
               'multiplier bit the test ` ra = some true ` holds and ` dup x t s ; add w t s w ` (~ tmcmltr ) adds '
               'the shifted multiplicand into the accumulator within the per-iteration budget; on a clear bit the '
               'test fails and the accumulator is unchanged (Lean ` condAdd ` , ` mulGo_append ` ).')
    c = Ctx(w, ph, TREE)
    ks = ['K', 'J', 'I', "I'", 'I"']
    mk = machine(w, ph, c, ks)
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    ps = "( %s /\\ i e. ( 0 ..^ ( # ` L' ) ) )" % ph
    L_ = Lifter(w, ps)
    ii = w.s([], 'simpr', "( %s -> i e. ( 0 ..^ ( # ` L' ) ) )" % ps)
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', "( %s -> i < ( # ` L' ) )" % ps)
    i1 = '( i + 1 )'
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, i1))
    ll, ll2 = L_(c[WRD('L', '2o')], WRD('L', '2o')), L_(c[WRD("L'", '2o')], WRD("L'", '2o'))
    xg, yg, wg = L_(c[WRD('X', GAM)], WRD('X', GAM)), L_(c[WRD('Y', GAM)], WRD('Y', GAM)), L_(c[WRD('W', GAM)], WRD('W', GAM))
    dd = L_(c[STKD('D')], STKD('D'))
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ps, PH_LL))
    tvp, phmp, seqp = L_(tv, 'T e. V'), L_(phm, PHM), L_(seq, SEQ)
    kd = {k: L_(mk['k'][k]['kd'], '%s e. %s' % (k, DG)) for k in ks}
    wge = {k: L_(mk['k'][k]['wge'], "Word %s = Word Gamma'" % GX(k)) for k in ks}
    ne = {t: L_(c[t], t) for t in flat(DIST5)}
    # the families at i
    xv, xw, rl = xfam(w, ps, 'i', inn, ll, xg)
    hv, hw, pa = hfam(w, ps, 'i', inn, lls, wg)
    yv, yw = yfam(w, ps, 'i', inn, ll2, yg)
    tok = lambda F, v, wd, k: w.s([w.s([v, wd], 'eqeltrd', "( %s -> ( %s ` i ) e. Word Gamma' )" % (ps, F)), wge[k]], 'eleqtrrd',
                                  '( %s -> ( %s ` i ) e. Word %s )' % (ps, F, GX(k)))
    DPMI, dstk, dvi, dvk = dpmf(w, ps, 'i', tvp, dd, kd, ne, tok(HML, hv, hw, 'I'), tok(XML, xv, xw, 'K'), tok(YML, yv, yw, 'J'))
    dk = w.s([dvk, xv], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ps, DPMI, XB('i')))
    di = w.s([dvi, hv], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ps, DPMI, HB('i')))
    # tmcmltr at the stacks DPM( i )
    AC = ACCN('i'); RL = '( ( (/) repeatS i ) ++ L )'
    m = {'D': DPMI, 'L': AC, "L'": RL, 'X': 'X', 'Y': 'W'}
    extra = {WRD(AC, '2o'): pa[WRD(AC, '2o')], WRD(RL, '2o'): rl, WRD('W', GAM): wg, STKD(DPMI): dstk,
             '( %s ` K ) = %s' % (DPMI, XB('i')): dk, '( %s ` I ) = %s' % (DPMI, HB('i')): di,
             'T e. V': tvp, MTY: L_(mk['mt'], MTY)}
    cps = Ctx(w, ps, TREE, root=w.s([], 'simpl', '( %s -> %s )' % (ps, ph)))
    bld = Builder(w, ps, cps, extra)
    t1, c1 = inst(w, ps, 'tmcmltr', m, bld)
    C1, D1, n1 = triple_parts(c1)
    # the class of the i-th test is inside S
    nv, ns = nfam(w, ps, 'i', inn)
    NI = '( %s ` i )' % NML
    n1s = w.s([nv, ns], 'eqsstrd', '( %s -> %s C_ TMSt )' % (ps, NI))
    n2s = w.s([n1s, seqp], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, NI))
    # the bit and the accumulator step
    b, fz = bitN(w, ps, ll2, inn, ilt) if False else (None, None)
    lz = w.s([w.s([ll2, w.inst('lencl')], 'syl', "( %s -> ( # ` L' ) e. NN0 )" % ps)], 'nn0zd', "( %s -> ( # ` L' ) e. ZZ )" % ps)
    bI = w.s([ll2, ii, w.inst('wrdsymbcl')], 'syl2anc', "( %s -> ( L' ` i ) e. 2o )" % ps)
    tj = w.s([ll2, inn], 'jca', "( %s -> ( L' e. Word 2o /\\ i e. NN0 ) )" % ps)
    MT = tsub_text(ST_MLT, {'N': 'i'})
    tt = w.s([tj, w.inst('tmcmlt')], 'syl', '( %s -> %s )' % (ps, split_imp(MT)[1]))
    mtp = parse_conj(split_imp(MT)[1])
    t3 = w.s([tt], 'simp3d', '( %s -> %s )' % (ps, cj(mtp[2])))
    t3b = w.s([ilt, t3], 'mpd', '( %s -> %s )' % (ps, split_imp(cj(mtp[2]))[1]))
    tpart = parse_conj(split_imp(cj(mtp[2]))[1])
    acs = w.s([inn, w.inst('tmcaccs')], 'syl', '( %s -> %s )' % (ps, split_imp(tsub_text(ST_ACCS, {'N': 'i'}))[1]))
    ACC1 = ACCN(i1)
    SUMA = "( ( %s addBits ( ( (/) repeatS i ) ++ L ) ) ` (/) )" % AC
    IFA = "if ( ( L' ` i ) = 1o , %s , %s )" % (SUMA, AC)
    H1 = '( %s ` %s )' % (HML, i1)
    disj = []
    for val in ('1o', '(/)'):
        pv = "( %s /\\ ( L' ` i ) = %s )" % (ps, val)
        Lv = Lifter(w, pv)
        bv = w.s([], 'simpr', "( %s -> ( L' ` i ) = %s )" % (pv, val))
        tst = w.s([Lv(w.s([t3b], 'simpld' if val == '1o' else 'simprd', '( %s -> %s )' % (ps, cj(tpart[0 if val == '1o' else 1]))),
                      cj(tpart[0 if val == '1o' else 1])), bv], 'mpd', '( %s -> %s )' % (pv, split_imp(cj(tpart[0 if val == '1o' else 1]))[1]))
        # ACC( i + 1 )
        if val == '1o':
            ie = w.s([bv], 'iftrued', '( %s -> %s = %s )' % (pv, IFA, SUMA))
            NEW = SUMA
        else:
            n01 = w.s([w.s([], '1n0', '1o =/= (/)')], 'nesymi', '-. (/) = 1o')
            nb = w.s([w.s([bv], 'eqeq1d', "( %s -> ( ( L' ` i ) = 1o <-> (/) = 1o ) )" % pv), w.s([n01], 'a1i', '( %s -> -. (/) = 1o )' % pv)], 'mtbird',
                     "( %s -> -. ( L' ` i ) = 1o )" % pv)
            ie = w.s([nb], 'iffalsed', '( %s -> %s = %s )' % (pv, IFA, AC))
            NEW = AC
        a1 = w.s([Lv(acs, split_imp(tsub_text(ST_ACCS, {'N': 'i'}))[1]), ie], 'eqtrd', '( %s -> %s = %s )' % (pv, ACC1, NEW))
        hv1, hw1, _ = hfam(w, pv, i1, Lv(i1n, '%s e. NN0' % i1), Lv(lls, PH_LL), Lv(wg, WRD('W', GAM)))
        cog = w.s([a1], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. %s ) )' % (pv, ACC1, NEW))
        hb = w.s([cog], 'oveq1d', '( %s -> %s = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ W ) ) )' % (pv, HB(i1), NEW))
        h1 = w.s([hv1, hb], 'eqtrd', '( %s -> %s = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ W ) ) )' % (pv, H1, NEW))
        if val == '(/)':
            h0 = w.s([h1, Lv(hv, formula(w, hv)[len('( %s -> ' % ps):-2])], 'eqtr4d', '( %s -> %s = ( %s ` i ) )' % (pv, H1, HML))
            disj.append(w.s([tst, h0], 'jca', '( %s -> %s )' % (pv, split_or(HYP_D)[1])))
            continue
        # the triple: shrink the precondition, rename the accumulator, weaken the bound
        tA = hrssc(w, pv, Lv(phmp, PHM), Lv(t1, c1), C1, D1, n1, CLN("B'", NI, DPMI), clnss(w, pv, "B'", NI, SS, DPMI, Lv(n2s, '%s C_ ( 2nd ` T )' % NI)))
        OLD = '( ( inclBool o. %s ) ++ ( <" 4 "> ++ W ) )' % SUMA
        ue = upeq(w, pv, DPMI, 'I', w.s([h1], 'eqcomd', '( %s -> %s = %s )' % (pv, OLD, H1)), OLD, H1)
        tB, C2, D2, n2 = hrrw(w, pv, tA, CLN("B'", NI, DPMI), D1, n1, deq=clneq(w, pv, 'B"', SS, ue, UP(DPMI, 'I', OLD), UP(DPMI, 'I', H1)))
        # the bound: n1 <_ T'
        LRL = '( # ` %s )' % RL
        LAC = '( # ` %s )' % AC
        MX = 'if ( %s <_ %s , %s , %s )' % (LAC, LRL, LRL, LAC)
        b0 = closed(w, pv, '0el2o', '(/) e. 2o')
        rw = w.s([b0, Lv(inn, 'i e. NN0'), w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS i ) e. Word 2o )' % pv)
        cl_ = w.s([rw, Lv(ll, WRD('L', '2o')), w.inst('ccatlen')], 'syl2anc', '( %s -> %s = ( ( # ` ( (/) repeatS i ) ) + ( # ` L ) ) )' % (pv, LRL))
        rl_ = w.s([closed(w, pv, '0ex', '(/) e. _V'), Lv(inn, 'i e. NN0'), w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS i ) ) = i )' % pv)
        len1 = w.s([cl_, w.s([rl_], 'oveq1d', '( %s -> ( ( # ` ( (/) repeatS i ) ) + ( # ` L ) ) = ( i + ( # ` L ) ) )' % pv)], 'eqtrd',
                   '( %s -> %s = ( i + ( # ` L ) ) )' % (pv, LRL))
        lacle = Lv(pa['%s <_ ( ( # ` L ) + i )' % LAC], '%s <_ ( ( # ` L ) + i )' % LAC)
        lrlw = Lv(rl, WRD(RL, '2o'))
        lrl0 = w.s([lrlw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pv, LRL))
        lac0 = w.s([Lv(pa[WRD(AC, '2o')], WRD(AC, '2o')), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pv, LAC))
        la0 = w.s([Lv(ll, WRD('L', '2o')), w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % pv)
        lb0 = w.s([Lv(ll2, WRD("L'", '2o')), w.inst('lencl')], 'syl', "( %s -> ( # ` L' ) e. NN0 )" % pv)
        cl0 = Closure(w, pv, {LRL: ('NN0', lrl0), LAC: ('NN0', lac0), '( # ` L )': ('NN0', la0), "( # ` L' )": ('NN0', lb0), 'i': ('NN0', Lv(inn, 'i e. NN0'))})
        rhs = '( ( # ` L ) + i )'
        lrle = w.s([len1, w.s([w.s([Lv(inn, 'i e. NN0')], 'nn0cnd', '( %s -> i e. CC )' % pv), w.s([la0], 'nn0cnd', '( %s -> ( # ` L ) e. CC )' % pv)], 'addcomd',
                                '( %s -> ( i + ( # ` L ) ) = %s )' % (pv, rhs))], 'eqtrd', '( %s -> %s = %s )' % (pv, LRL, rhs))
        lrl_le = w.s([w.s([lrle], 'eqcomd', '( %s -> %s = %s )' % (pv, rhs, LRL)), w.s([cl0.mem(rhs, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (pv, rhs, rhs))], 'eqbrtrrd' if False else 'breqtrd',
                     '( %s -> %s <_ %s )' % (pv, rhs, LRL)) if False else \
            w.s([w.s([lrle], 'eqcomd', '( %s -> %s = %s )' % (pv, rhs, LRL)) and w.s([cl0.mem(LRL, 'RR')], 'leidd', '( %s -> %s <_ %s )' % (pv, LRL, LRL)), lrle], 'breqtrd',
                '( %s -> %s <_ %s )' % (pv, LRL, rhs))
        mle = w.s([cl0.mem(LAC, 'RR'), cl0.mem(LRL, 'RR'), cl0.mem(rhs, 'RR'), w.inst('maxle')], 'syl3anc',
                  '( %s -> ( %s <_ %s <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (pv, MX, rhs, LAC, rhs, LRL, rhs))
        mx = w.s([mle, w.s([lacle, lrl_le], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (pv, LAC, rhs, LRL, rhs))], 'mpbird', '( %s -> %s <_ %s )' % (pv, MX, rhs))
        mx0 = w.s([lrl0, lac0], 'ifcld', '( %s -> %s e. NN0 )' % (pv, MX))
        leaves = {LRL: lrl0, LAC: lac0, '( # ` L )': la0, "( # ` L' )": lb0, 'i': Lv(inn, 'i e. NN0'), MX: mx0}
        tC = bound(w, pv, Lv(phmp, PHM), tB, C2, D2, n2, TPM, leaves, hyps=[lrle, mx, Lv(ilt, "i < ( # ` L' )"), w.s([lb0], 'nn0ge0d', "( %s -> 0 <_ ( # ` L' ) )" % pv)])
        disj.append(w.s([tst, tC], 'jca', '( %s -> %s )' % (pv, split_or(HYP_D)[0])))
    d1 = w.s([disj[0]], 'orcd', '( %s -> %s )' % ("( %s /\\ ( L' ` i ) = 1o )" % ps, HYP_D))
    d0 = w.s([disj[1]], 'olcd', '( %s -> %s )' % ("( %s /\\ ( L' ` i ) = (/) )" % ps, HYP_D))
    e2 = w.s([bI, w.s([], 'df2o3', '2o = { (/) , 1o }')], 'eleqtrdi' if False else 'eleqtrd', "( %s -> ( L' ` i ) e. { (/) , 1o } )" % ps) if False else \
        w.s([bI, closed(w, ps, 'df2o3', '2o = { (/) , 1o }')], 'eleqtrd', "( %s -> ( L' ` i ) e. { (/) , 1o } )" % ps)
    ep = w.s([e2, w.inst('elpri')], 'syl', "( %s -> ( ( L' ` i ) = (/) \\/ ( L' ` i ) = 1o ) )" % ps)
    dd_ = w.s([d0, d1, ep], 'mpjaodan', '( %s -> %s )' % (ps, HYP_D))
    w.qed([dd_], 'ralrimiva', '( %s -> %s )' % (ph, RALI(HYP_D)))
    return w.run()


def tmcml():
    lab = 'tmcml'
    TREE = TREE_ML()
    ph = cj(TREE)
    w = W(lab, '` mul x y w s t ` at the machine (Lean ` mul_runs ` ): consumes the bit words ` xs ` on ` x ` and '
               '` ys ` on ` y ` and pushes the bit word ` mulGo [] xs ys ` (here the ` seq ` of ~ tmcacc ) on '
               '` w ` ; the scratch stacks ` s ` , ` t ` are restored; within Lean\'s bound '
               '` |ys| ( 4 |xs| + 6 |ys| + 14 ) + |xs| + |ys| + 4 ` .  ~ tm2fmlv with the families of ~ tmcmlf , '
               'the iteration of ~ tmcmls and ~ tmcmld , the interfaces of ~ tmcmlpb , ~ tmcmlt , ~ tmcdri .')
    c = Ctx(w, ph, TREE)
    ks = ['K', 'J', 'I', "I'", 'I"']
    mk = machine(w, ph, c, ks)
    phm, tv, seq, geq = mk['phm'], mk['tv'], mk['seq'], mk['geq']
    ll, ll2 = c[WRD('L', '2o')], c[WRD("L'", '2o')]
    xg, yg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    dk, dj = c[DATA_ML[1][0]], c[DATA_ML[1][1]]
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph, PH_LL))
    K_ = lambda k: mk['k'][k]
    DI = '( D ` I )'
    dig = w.s([w.s([tv, dd, K_('I')['kd'], w.inst('tm2stkfv')], 'syl3anc', '( %s -> %s e. Word %s )' % (ph, DI, GX('I'))), K_('I')['wge']], 'eleqtrd',
              "( %s -> %s e. Word Gamma' )" % (ph, DI))
    M = MLMAP(DI)
    extra = {PHM: phm, 'T e. V': tv, MTY: mk['mt'], WRD(DI, GAM): dig}
    for k in ['K', 'J', 'I']:
        extra['%s e. %s' % (k, DG)] = K_(k)['kd']
    # the tests' typings
    b01 = lambda X_of: w.s([w.s([], '0el2o', '(/) e. 2o'), w.s([], '1oel2o', '1o e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    b10 = lambda X_of: w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    two = w.s([], '2oex', '2o e. _V')
    XC0 = lambda t: 'if ( ( TMda ` %s ) = 1o , (/) , 1o )' % t
    XC = lambda t: 'if ( ( TMra ` %s ) = ( inl ` 1o ) , 1o , (/) )' % t
    extra[CTY(C0ML)] = lamty(w, ph, mk, C0ML, XC0, '2o', two, b01(XC0))
    extra[CTY(CML)] = lamty(w, ph, mk, CML, XC, '2o', two, b10(XC))
    extra[CTY(CIS)] = cis_ty(w, ph, mk)
    # the skip load ( _I |` TMSt )
    f1 = w.s([], 'f1oi', '( _I |` TMSt ) : TMSt -1-1-onto-> TMSt')
    ff = w.s([w.s([f1, w.inst('f1of')], 'ax-mp', '( _I |` TMSt ) : TMSt --> TMSt')], 'a1i',
                                                                                 '( %s -> ( _I |` TMSt ) : TMSt --> TMSt )' % ph)
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    em = w.s([w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), w.s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), w.inst('elmapg')], 'syl2anc',
             '( %s -> ( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt ) )' % ph)
    li = w.s([em, ff], 'mpbird', '( %s -> ( _I |` TMSt ) e. ( TMSt ^m TMSt ) )' % ph)
    sq = w.s([seq], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    mq = w.s([sq, sq], 'oveq12d', '( %s -> ( TMSt ^m TMSt ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    extra[LTY(LIDL)] = w.s([li, mq], 'eleqtrd', '( %s -> %s )' % (ph, LTY(LIDL)))
    extra[RTY('TMrdBit', 'J')] = K_('J')['hdl']['TMrdBit']
    extra[RTY('TMrdA', 'K')] = K_('K')['hdl']['TMrdA']
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    extra['%s C_ %s' % (BITS, GX('K'))] = bitsgk(w, ph, mk, 'K')
    g0 = w.s([closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> <. 1 , (/) >. e. Gamma' )" % ph)
    extra['<. 1 , (/) >. e. %s' % GX('K')] = letgk(w, ph, mk, '<. 1 , (/) >.', 'K', g0)
    extra['4 e. %s' % GX('K')] = letgk(w, ph, mk, '4', 'K', g4)
    extra['4 e. %s' % GX('I')] = letgk(w, ph, mk, '4', 'I', g4)
    # popBit at 0 and the letter ( U ` 0 )
    lz = w.s([ll2, w.inst('lencl')], 'syl', "( %s -> ( # ` L' ) e. NN0 )" % ph)
    z0f = w.s([lz, w.inst('0elfz')], 'syl', "( %s -> 0 e. ( 0 ... ( # ` L' ) ) )" % ph)
    PB0 = tsub_text(ST_MLPB, {'N': '0'})
    pb0 = w.s([w.s([seq, ll2, z0f], '3jca', '( %s -> %s )' % (ph, split_imp(PB0)[0])), w.inst('tmcmlpb')], 'syl', '( %s -> %s )' % (ph, split_imp(PB0)[1]))
    U0 = '( %s ` 0 )' % UML
    u0g = w.s([pb0], 'simpld', "( %s -> %s e. Gamma' )" % (ph, U0))
    extra['%s e. %s' % (U0, GX('J'))] = letgk(w, ph, mk, U0, 'J', u0g)
    hpb0 = w.s([pb0], 'simprd', '( %s -> %s )' % (ph, split_imp(PB0)[1].split(" e. Gamma' /\\ ", 1)[1][:-2]))
    extra[leafof(w, ph, hpb0)] = hpb0
    extra['( 2nd ` T ) C_ ( 2nd ` T )'] = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    # the initial stacks
    z0n = closed(w, ph, '0nn0', '0 e. NN0')
    xv0, xw0, _ = xfam(w, ph, '0', z0n, ll, xg)
    zex = closed(w, ph, '0ex', '(/) e. _V')
    r0 = w.s([zex, w.inst('repsw0')], 'syl', '( %s -> ( (/) repeatS 0 ) = (/) )' % ph)
    r0l = w.s([r0], 'oveq1d', '( %s -> ( ( (/) repeatS 0 ) ++ L ) = ( (/) ++ L ) )' % ph)
    cl0 = w.s([ll, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ L ) = L )' % ph)
    r0c = w.s([w.s([r0l, cl0], 'eqtrd', '( %s -> ( ( (/) repeatS 0 ) ++ L ) = L )' % ph)], 'coeq2d',
              '( %s -> ( inclBool o. ( ( (/) repeatS 0 ) ++ L ) ) = ( inclBool o. L ) )' % ph)
    xb0 = w.s([r0c], 'oveq1d', '( %s -> %s = ( ( inclBool o. L ) ++ ( <" 4 "> ++ X ) ) )' % (ph, XB('0')))
    ix = w.s([w.s([xv0, xb0], 'eqtrd', '( %s -> ( %s ` 0 ) = ( ( inclBool o. L ) ++ ( <" 4 "> ++ X ) ) )' % (ph, XML)), dk], 'eqtr4d',
             '( %s -> ( %s ` 0 ) = ( D ` K ) )' % (ph, XML))
    hv0, hw0, _ = hfam(w, ph, '0', z0n, lls, dig, DI)
    a0 = closed(w, ph, 'tmcacc0', '%s = (/)' % ACCN('0'))
    a0c = w.s([a0], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. (/) ) )' % (ph, ACCN('0')))
    a0d = w.s([a0c, closed(w, ph, 'bwmap0', '( inclBool o. (/) ) = (/)')], 'eqtrd', '( %s -> ( inclBool o. %s ) = (/) )' % (ph, ACCN('0')))
    hb0 = w.s([a0d], 'oveq1d', '( %s -> %s = ( (/) ++ ( <" 4 "> ++ %s ) ) )' % (ph, HB('0', DI), DI))
    hl = w.s([four_w(w, ph, DI, dig), w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ ( <" 4 "> ++ %s ) ) = ( <" 4 "> ++ %s ) )' % (ph, DI, DI))
    ih = w.s([w.s([hv0, hb0], 'eqtrd', '( %s -> ( %s ` 0 ) = ( (/) ++ ( <" 4 "> ++ %s ) ) )' % (ph, HMLW(DI), DI)), hl], 'eqtrd',
             '( %s -> ( %s ` 0 ) = ( <" 4 "> ++ %s ) )' % (ph, HMLW(DI), DI))
    yv0, _ = yfam(w, ph, '0', z0n, ll2, yg)
    j0 = w.s([ll2, yg, z0n], '3jca', "( %s -> ( L' e. Word 2o /\\ Y e. Word Gamma' /\\ 0 e. NN0 ) )" % ph)
    OP1 = tsub_text(ST_OP1, {'L': "L'", 'X': 'Y', 'N': '0'})
    o1 = w.s([j0, w.inst('tmcop1')], 'syl', '( %s -> %s )' % (ph, split_imp(OP1)[1]))
    OPFY_, OPUY_ = OPF("L'", 'Y'), OPU("L'")
    o1a = w.s([z0f, w.s([o1], 'simp1d', '( %s -> ( 0 e. %s -> ( %s ` 0 ) = ( <" ( %s ` 0 ) "> ++ ( %s ` ( 0 + 1 ) ) ) ) )' % (ph, OPR("L'"), OPFY_, OPUY_, OPFY_))], 'mpd',
              '( %s -> ( %s ` 0 ) = ( <" ( %s ` 0 ) "> ++ ( %s ` ( 0 + 1 ) ) ) )' % (ph, OPFY_, OPUY_, OPFY_))
    OP0 = tsub_text(ST_OP0, {'L': "L'", 'X': 'Y'})
    o0 = w.s([w.s([ll2, yg], 'jca', "( %s -> ( L' e. Word 2o /\\ Y e. Word Gamma' ) )" % ph), w.inst('tmcop0')], 'syl', '( %s -> %s )' % (ph, split_imp(OP0)[1]))
    djo = w.s([dj, o0], 'eqtr4d', '( %s -> ( D ` J ) = ( %s ` 0 ) )' % (ph, OPFY_))
    yb0 = w.s([yv0], 'oveq2d', '( %s -> ( <" ( %s ` 0 ) "> ++ ( %s ` 0 ) ) = ( <" ( %s ` 0 ) "> ++ %s ) )' % (ph, UML, YML, UML, YB('0')))
    iy = w.s([w.s([djo, o1a], 'eqtrd', '( %s -> ( D ` J ) = ( <" ( %s ` 0 ) "> ++ %s ) )' % (ph, UML, YB('0'))), yb0], 'eqtr4d',
             '( %s -> ( D ` J ) = ( <" ( %s ` 0 ) "> ++ ( %s ` 0 ) ) )' % (ph, UML, YML))
    for st in (ix, ih, iy):
        extra[leafof(w, ph, st)] = st
    # R , T' , 1 <_ T'
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    clx = Closure(w, ph, {'( # ` L )': ('NN0', la), "( # ` L' )": ('NN0', lz)})
    extra["( # ` L' ) e. NN0"] = lz
    extra['%s e. NN0' % TPM] = clx.mem(TPM, 'NN0')
    extra['1 <_ %s' % TPM] = linarith(w, ph, [w.s([la], 'nn0ge0d', '( %s -> 0 <_ ( # ` L ) )' % ph), w.s([lz], 'nn0ge0d', "( %s -> 0 <_ ( # ` L' ) )" % ph)],
                                      '1 <_ %s' % TPM, closure=clx)
    # dropNum's interface
    N_ = NVA('r', 'z')
    dri = w.s([], 'tmcdri', ST_DRI)
    hc = ral_S(w, ph, mk, w.s([dri], 'simpli', 'A. r e. TMSt A. z e. %s ( %s ` %s ) = 1o' % (BITS, CIS, N_)), '( %s ` %s ) = 1o' % (CIS, N_), 2)
    he = ral_S(w, ph, mk, w.s([dri], 'simpri', 'A. r e. TMSt -. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4'))), '-. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')), 1)
    extra[leafof(w, ph, hc)] = hc
    extra[leafof(w, ph, he)] = he
    # the families and the iteration
    sub = {'W': DI}
    mfj = w.s([w.s([geq, seq], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, GEQ, SEQ)),
               w.s([lls, w.s([xg, yg, dig], '3jca', "( %s -> ( X e. Word Gamma' /\\ Y e. Word Gamma' /\\ %s e. Word Gamma' ) )" % (ph, DI))], 'jca',
                   "( %s -> ( %s /\\ ( X e. Word Gamma' /\\ Y e. Word Gamma' /\\ %s e. Word Gamma' ) ) )" % (ph, PH_LL, DI)),
               w.s([c[IDX('K')], c[IDX('J')], c[IDX('I')]], '3jca', '( %s -> %s )' % (ph, cj(IDX3)))], '3jca',
              '( %s -> %s )' % (ph, cj(tsub(PH_MF, sub))))
    fam = w.s([mfj, w.inst('tmcmlf')], 'syl', '( %s -> %s )' % (ph, tsub_text(FAMML, sub)))
    extra[tsub_text(FAMML, sub)] = fam
    ms = w.s([mfj, w.inst('tmcmls')], 'syl', '( %s -> %s )' % (ph, tsub_text('( %s /\\ %s )' % (RALI(HYP_P), RALI(HYP_Q)), sub)))
    rP = w.s([ms], 'simpld', '( %s -> %s )' % (ph, tsub_text(RALI(HYP_P), sub)))
    rQ = w.s([ms], 'simprd', '( %s -> %s )' % (ph, tsub_text(RALI(HYP_Q), sub)))
    extra[WRD('W', GAM).replace('W', DI)] = dig
    bldd = Builder(w, ph, c, extra)
    md = w.s([bldd(tsub(TREE_MLD(), sub)), w.inst('tmcmld')], 'syl', '( %s -> %s )' % (ph, tsub_text(RALI(HYP_D), sub)))
    HP, HQ, HD = [tsub_text(x, sub) for x in (HYP_P, HYP_Q, HYP_D)]
    r3 = w.s([], 'r19.26-3', "( A. i e. ( 0 ..^ ( # ` L' ) ) ( %s /\\ %s /\\ %s ) <-> ( %s /\\ %s /\\ %s ) )" % (HP, HQ, HD, RALI(HP), RALI(HQ), RALI(HD)))
    hy = w.s([w.s([rP, rQ, md], '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ph, RALI(HP), RALI(HQ), RALI(HD))), r3], 'sylibr',
             "( %s -> A. i e. ( 0 ..^ ( # ` L' ) ) ( %s /\\ %s /\\ %s ) )" % (ph, HP, HQ, HD))
    extra[leafof(w, ph, hy)] = hy
    # the end: the multiplicand word, the failed test
    xvR, xwR, rlR = xfam(w, ph, "( # ` L' )", lz, ll, xg)
    extra[leafof(w, ph, xvR)] = xvR
    extra[WRD(WFIN, BITS)] = w.s([rlR, w.inst('tmcibw')], 'syl', '( %s -> %s e. %s )' % (ph, WFIN, WB))
    extra[WRD('X', GX('K'))] = togk(w, ph, mk, 'X', 'K', xg)
    MTR = tsub_text(ST_MLT, {'N': "( # ` L' )"})
    mt = w.s([w.s([ll2, lz], 'jca', "( %s -> ( L' e. Word 2o /\\ ( # ` L' ) e. NN0 ) )" % ph), w.inst('tmcmlt')], 'syl', '( %s -> %s )' % (ph, split_imp(MTR)[1]))
    mt2 = w.s([mt], 'simp2d', '( %s -> %s )' % (ph, cj(parse_conj(split_imp(MTR)[1])[1])))
    lzr = w.s([lz], 'nn0red', "( %s -> ( # ` L' ) e. RR )" % ph)
    htf = w.s([w.s([lzr], 'leidd', "( %s -> ( # ` L' ) <_ ( # ` L' ) )" % ph), mt2], 'mpd', '( %s -> %s )' % (ph, split_imp(cj(parse_conj(split_imp(MTR)[1])[1]))[1]))
    extra[leafof(w, ph, htf)] = htf
    bld = Builder(w, ph, c, extra)
    t, cc = inst(w, ph, 'tm2fmlv', M, bld)
    C1, D1, n1 = triple_parts(cc)
    # rewrite the final stacks and the bound
    RR_ = "( # ` L' )"
    hvR, hwR, _ = hfam(w, ph, RR_, lz, lls, dig, DI)
    yvR, ywR = yfam(w, ph, RR_, lz, ll2, yg)
    R1 = '( %s + 1 )' % RR_
    R1n = w.s([lz, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, R1))
    ltR = w.s([lzr], 'ltp1d', '( %s -> %s < %s )' % (ph, RR_, R1))
    OPE = tsub_text(ST_OPE, {'L': "L'", 'X': 'Y', 'N': R1})
    oe = w.s([w.s([w.s([ll2, yg], 'jca', "( %s -> ( L' e. Word 2o /\\ Y e. Word Gamma' ) )" % ph), w.s([R1n, ltR], 'jca', '( %s -> ( %s e. NN0 /\\ %s < %s ) )' % (ph, R1, RR_, R1))], 'jca',
                   '( %s -> %s )' % (ph, split_imp(OPE)[0])), w.inst('tmcope')], 'syl', '( %s -> %s )' % (ph, split_imp(OPE)[1]))
    yR = w.s([yvR, oe], 'eqtrd', '( %s -> ( %s ` %s ) = Y )' % (ph, YML, RR_))
    HR_ = '( %s ` %s )' % (HMLW(DI), RR_)
    YR_ = '( %s ` %s )' % (YML, RR_)
    u1 = upeq(w, ph, 'D', 'I', hvR, HR_, HFIN)
    r1, new1 = w.rewrite(UP3('D', 'I', HR_, 'K', 'X', 'J', YR_), {UP('D', 'I', HR_): (UP('D', 'I', HFIN), u1), YR_: ('Y', yR)}, ph)
    assert new1 == UP3('D', 'I', HFIN, 'K', 'X', 'J', 'Y'), new1
    deq = clneq(w, ph, "E'", SS, r1, UP3('D', 'I', HR_, 'K', 'X', 'J', YR_), new1)
    # |W| = R + |L|
    rlw = rlR
    wl = w.s([rlw, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = ( # ` ( ( (/) repeatS %s ) ++ L ) ) )' % (ph, WFIN, RR_))
    rw = w.s([closed(w, ph, '0el2o', '(/) e. 2o'), lz, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS %s ) e. Word 2o )' % (ph, RR_))
    cl_ = w.s([rw, ll, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` ( ( (/) repeatS %s ) ++ L ) ) = ( ( # ` ( (/) repeatS %s ) ) + ( # ` L ) ) )' % (ph, RR_, RR_))
    rl_ = w.s([zex, lz, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS %s ) ) = %s )' % (ph, RR_, RR_))
    wl2 = w.s([w.s([wl, cl_], 'eqtrd', '( %s -> ( # ` %s ) = ( ( # ` ( (/) repeatS %s ) ) + ( # ` L ) ) )' % (ph, WFIN, RR_)),
               w.s([rl_], 'oveq1d', '( %s -> ( ( # ` ( (/) repeatS %s ) ) + ( # ` L ) ) = ( %s + ( # ` L ) ) )' % (ph, RR_, RR_))], 'eqtrd',
              '( %s -> ( # ` %s ) = ( %s + ( # ` L ) ) )' % (ph, WFIN, RR_))
    LW = '( # ` %s )' % WFIN
    lw0 = w.s([w.s([rlR, w.inst('tmcibw')], 'syl', '( %s -> %s e. %s )' % (ph, WFIN, WB)), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW))
    clb = Closure(w, ph, {'( # ` L )': ('NN0', la), RR_: ('NN0', lz), LW: ('NN0', lw0)})
    neq = lineq(w, ph, n1, MULB, hyps=[wl2], closure=clb, products=True)
    t2, C2, D2, n2 = hrrw(w, ph, t, C1, D1, n1, deq=deq, neq=neq, qed=True)
    assert TRI(C2, D2, n2) == CONCL_ML, (TRI(C2, D2, n2)[:300], CONCL_ML[:300])
    return w.run()


def tmcmulc():
    lab = 'tmcmulc'
    TREE = TREE_MLC()
    ph = cj(TREE)
    w = W(lab, '` mulC x y w s t ` at the machine (Lean ` mulC_runs ` ): ` mul ` (~ tmcml ) then ` canonNum w s ` '
               '(~ tmccans ): the product of the values of the two bit words is pushed on ` w ` in canonical form, '
               'within Lean\'s bound ` |ys| ( 4 |xs| + 6 |ys| + 14 ) + 4 |xs| + 7 |ys| + 9 ` .')
    c = Ctx(w, ph, TREE)
    ks = ['K', 'J', 'I', "I'", 'I"']
    mk = machine(w, ph, c, ks)
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    K_ = lambda k: mk['k'][k]
    ll, ll2 = c[WRD('L', '2o')], c[WRD("L'", '2o')]
    xg, yg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph, PH_LL))
    bld = Builder(w, ph, c, {'T e. V': tv, MTY: mk['mt']})
    t1 = w.s([bld(TREE_ML()), w.inst('tmcml')], 'syl', '( %s -> %s )' % (ph, CONCL_ML))
    C1, D1, n1 = triple_parts(CONCL_ML)
    DI = '( D ` I )'
    dig = w.s([w.s([tv, dd, K_('I')['kd'], w.inst('tm2stkfv')], 'syl3anc', '( %s -> %s e. Word %s )' % (ph, DI, GX('I'))), K_('I')['wge']], 'eleqtrd',
              "( %s -> %s e. Word Gamma' )" % (ph, DI))
    lz = w.s([ll2, w.inst('lencl')], 'syl', "( %s -> ( # ` L' ) e. NN0 )" % ph)
    hvR, hwR, pa = hfam(w, ph, "( # ` L' )", lz, lls, dig, DI)
    # the stacks after mul
    U1 = UP('D', 'I', HFIN); U2 = UP(U1, 'K', 'X'); U3 = UP(U2, 'J', 'Y')
    hk = togk(w, ph, mk, HFIN, 'I', hwR)
    xk = togk(w, ph, mk, 'X', 'K', xg)
    yk = togk(w, ph, mk, 'Y', 'J', yg)
    s1 = updcl(w, ph, 'D', 'I', HFIN, tv, dd, K_('I')['kd'], hk)
    s2 = updcl(w, ph, U1, 'K', 'X', tv, s1, K_('K')['kd'], xk)
    s3 = updcl(w, ph, U2, 'J', 'Y', tv, s2, K_('J')['kd'], yk)
    nij = w.s([c['J =/= I']], 'necomd', '( %s -> I =/= J )' % ph)
    nik = w.s([c['K =/= I']], 'necomd', '( %s -> I =/= K )' % ph)
    v1 = updnv(w, ph, U2, 'J', 'Y', 'I', tv, s2, K_('J')['kd'], elv(w, ph, yg, 'Y'), K_('I')['kd'], nij)
    v2 = updnv(w, ph, U1, 'K', 'X', 'I', tv, s1, K_('K')['kd'], elv(w, ph, xg, 'X'), K_('I')['kd'], nik)
    v3 = updkv(w, ph, 'D', 'I', HFIN, tv, dd, K_('I')['kd'], elv(w, ph, hwR, HFIN))
    u3i = w.s([w.s([v1, v2], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (ph, U3, U1)), v3], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, U3, HFIN))
    # canonNum w s on U3
    CM = dict(CAN_LAB); CM.update({'L': ACCR, 'X': DI, 'D': U3})
    extra = {'T e. V': tv, MTY: mk['mt'], WRD(ACCR, '2o'): pa[WRD(ACCR, '2o')], WRD(DI, GAM): dig, STKD(U3): s3,
             '( %s ` I ) = %s' % (U3, HFIN): u3i}
    bld2 = Builder(w, ph, c, extra)
    t2, c2 = inst(w, ph, 'tmccans', CM, bld2)
    C2, D2, n2 = triple_parts(c2)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, phm, t1, t2, C1, D1, D2, n1, n2)
    # the value: toNat ACC( R ) = toNat L x. toNat L'
    PA = parse_conj(tsub_text(PACC('N'), {'N': "( # ` L' )"}))
    lzr = w.s([lz], 'nn0red', "( %s -> ( # ` L' ) e. RR )" % ph)
    tv_ = w.s([w.s([lzr], 'leidd', "( %s -> ( # ` L' ) <_ ( # ` L' ) )" % ph), pa[cj(PA[1])]], 'mpd', '( %s -> %s )' % (ph, split_imp(cj(PA[1]))[1]))
    pf = w.s([ll2, w.inst('pfxid')], 'syl', "( %s -> ( L' prefix ( # ` L' ) ) = L' )" % ph)
    tq = w.s([tv_, w.s([w.s([pf], 'fveq2d', "( %s -> ( toNat ` ( L' prefix ( # ` L' ) ) ) = ( toNat ` L' ) )" % ph)], 'oveq2d',
                       "( %s -> ( ( toNat ` L ) x. ( toNat ` ( L' prefix ( # ` L' ) ) ) ) = ( ( toNat ` L ) x. ( toNat ` L' ) ) )" % ph)], 'eqtrd',
             "( %s -> ( toNat ` %s ) = ( ( toNat ` L ) x. ( toNat ` L' ) ) )" % (ph, ACCR))
    ENA = '( encNatGam ` ( toNat ` %s ) )' % ACCR
    ee = w.s([tq], 'fveq2d', '( %s -> %s = %s )' % (ph, ENA, ENCP))
    B0 = CC(ENA, '( <" 4 "> ++ %s )' % DI)
    B1 = CC(ENCP, '( <" 4 "> ++ %s )' % DI)
    be = w.s([ee], 'oveq1d', '( %s -> %s = %s )' % (ph, B0, B1))
    # the stacks: UPD( U3 , I , B0 ) = UPD3( D ; I , B1 ; K , X ; J , Y )
    assert D2 == CLN('E"', SS, UP(U3, 'I', B0)), D2
    tn = w.s([pa[WRD(ACCR, '2o')], w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` %s ) e. NN0 )' % (ph, ACCR))
    eg = w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ENA))
    b0g = wg_ccat(w, ph, ENA, '( <" 4 "> ++ %s )' % DI, eg, four_w(w, ph, DI, dig))
    b0k = togk(w, ph, mk, B0, 'I', b0g)
    e1 = upc(w, ph, U2, 'J', 'Y', 'I', B0, tv, s2, c['J =/= I'], K_('J')['kd'], yk, K_('I')['kd'], b0k)
    e2 = upc(w, ph, U1, 'K', 'X', 'I', B0, tv, s1, c['K =/= I'], K_('K')['kd'], xk, K_('I')['kd'], b0k)
    e3 = up2(w, ph, 'D', 'I', HFIN, B0, tv, dd, K_('I')['kd'], hk, b0k)
    F0 = UP(U3, 'I', B0)
    r1, n_1 = w.rewrite(UP(UP(UP(U1, 'I', B0), 'K', 'X'), 'J', 'Y'), {UP(U1, 'I', B0): (UP('D', 'I', B0), e3)}, ph)
    r2, n_2 = w.rewrite(UP(UP(U2, 'I', B0), 'J', 'Y'), {UP(U2, 'I', B0): (UP(UP(U1, 'I', B0), 'K', 'X'), e2)}, ph)
    u4 = upeq(w, ph, 'D', 'I', be, B0, B1)
    r4, n_4 = w.rewrite(n_1, {UP('D', 'I', B0): (UP('D', 'I', B1), u4)}, ph)
    FIN = UP3('D', 'I', B1, 'K', 'X', 'J', 'Y')
    assert n_4 == FIN, n_4
    fa = w.s([e1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, F0, UP(UP(UP(U1, 'I', B0), 'K', 'X'), 'J', 'Y')))
    fb = w.s([fa, r1], 'eqtrd', '( %s -> %s = %s )' % (ph, F0, n_1))
    fc = w.s([fb, r4], 'eqtrd', '( %s -> %s = %s )' % (ph, F0, FIN))
    deq = clneq(w, ph, 'E"', SS, fc, F0, FIN)
    t3, C3, D3, n3 = hrrw(w, ph, t12, C1, D2, '( %s + %s )' % (n1, n2), deq=deq)
    # the bound
    LAC = '( # ` %s )' % ACCR
    lac = w.s([pa[WRD(ACCR, '2o')], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LAC))
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)
    PROD = "( ( # ` L' ) x. ( ( ( 4 x. ( # ` L ) ) + ( 6 x. ( # ` L' ) ) ) + ; 1 4 ) )"
    pr0 = Closure(w, ph, {'( # ` L )': ('NN0', la), "( # ` L' )": ('NN0', lz)}).mem(PROD, 'NN0')
    leaves = {'( # ` L )': la, "( # ` L' )": lz, LAC: lac, PROD: pr0}
    lacle = pa['%s <_ ( ( # ` L ) + ( # ` L\' ) )' % LAC]
    bound(w, ph, phm, t3, C3, D3, n3, MULCB, leaves, hyps=[lacle, w.s([lz], 'nn0ge0d', "( %s -> 0 <_ ( # ` L' ) )" % ph),
                                                          w.s([la], 'nn0ge0d', '( %s -> 0 <_ ( # ` L ) )' % ph)], qed=True)
    return w.run()


def tmcmulb():
    lab = 'tmcmulb'
    TREE = TREE_MB()
    ph = cj(TREE)
    w = W(lab, '` mulC_le_B ` at the machine: ` mulC x y w s t ` on the encodings of ` F , G < 2 ^ N ` pushes the '
               'encoding of ` F x. G ` on ` w ` within ` ( TMB ` N ) ` steps (~ tmcmulc , the lengths by '
               '~ encnatlenpow , the arithmetic by ~ tmdmulb ).')
    c = Ctx(w, ph, TREE)
    phm = c[PHM]
    tv = w.s([phm], 'simpld', '( %s -> T e. V )' % ph)
    mt = w.s([phm], 'simprd', '( %s -> %s )' % (ph, MTY))
    ff, gg, nn = c['F e. NN0'], c['G e. NN0'], c['N e. NN0']
    EF, EG = '( encodeNat ` F )', '( encodeNat ` G )'
    ef = w.s([ff, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EF))
    eg = w.s([gg, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    dk = w.s([c[DATA_MB[1][1][0]], w.s([w.s([ff, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` F ) = ( inclBool o. %s ) )' % (ph, EF))], 'oveq1d',
             '( %s -> ( ( encNatGam ` F ) ++ ( <" 4 "> ++ X ) ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (ph, EF))], 'eqtrd',
             '( %s -> ( D ` K ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) ) )' % (ph, EF))
    dj = w.s([c[DATA_MB[1][1][1]], w.s([w.s([gg, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` G ) = ( inclBool o. %s ) )' % (ph, EG))], 'oveq1d',
             '( %s -> ( ( encNatGam ` G ) ++ ( <" 4 "> ++ Y ) ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) ) )' % (ph, EG))], 'eqtrd',
             '( %s -> ( D ` J ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ Y ) ) )' % (ph, EG))
    m = {'L': EF, "L'": EG}
    extra = {'T e. V': tv, MTY: mt, WRD(EF, '2o'): ef, WRD(EG, '2o'): eg, formula(w, dk)[len('( %s -> ' % ph):-2]: dk,
             formula(w, dj)[len('( %s -> ' % ph):-2]: dj}
    bld = Builder(w, ph, c, extra)
    t1, c1 = inst(w, ph, 'tmcmulc', m, bld)
    C1, D1, n1 = triple_parts(c1)
    # the value
    tf = w.s([ff, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = F )' % (ph, EF))
    tg = w.s([gg, w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = G )' % (ph, EG))
    tfg = w.s([tf, tg], 'oveq12d', '( %s -> ( ( toNat ` %s ) x. ( toNat ` %s ) ) = ( F x. G ) )' % (ph, EF, EG))
    ENC0 = tsub_text(ENCP, m)
    e1 = w.s([tfg], 'fveq2d', '( %s -> %s = ( encNatGam ` ( F x. G ) ) )' % (ph, ENC0))
    B0 = CC(ENC0, '( <" 4 "> ++ ( D ` I ) )')
    B1 = CC('( encNatGam ` ( F x. G ) )', '( <" 4 "> ++ ( D ` I ) )')
    e2 = w.s([e1], 'oveq1d', '( %s -> %s = %s )' % (ph, B0, B1))
    OLD = UP3('D', 'I', B0, 'K', 'X', 'J', 'Y')
    r, new = w.rewrite(OLD, {B0: (B1, e2)}, ph)
    deq = clneq(w, ph, 'E"', SS, r, OLD, new)
    t2, C2, D2, n2 = hrrw(w, ph, t1, C1, D1, n1, deq=deq)
    # the bound
    A_, B_ = '( # ` %s )' % EF, '( # ` %s )' % EG
    la = w.s([ff, nn, c['F < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, A_))
    lb = w.s([gg, nn, c['G < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> %s <_ N )' % (ph, B_))
    a0 = w.s([ef, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, A_))
    b0 = w.s([eg, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, B_))
    j = w.s([w.s([a0, b0, nn], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ N e. NN0 ) )' % (ph, A_, B_)),
             w.s([la, lb], 'jca', '( %s -> ( %s <_ N /\\ %s <_ N ) )' % (ph, A_, B_))], 'jca',
            '( %s -> ( ( %s e. NN0 /\\ %s e. NN0 /\\ N e. NN0 ) /\\ ( %s <_ N /\\ %s <_ N ) ) )' % (ph, A_, B_, A_, B_))
    mb = w.s([j, w.inst('tmdmulb')], 'syl', '( %s -> %s <_ ( TMB ` N ) )' % (ph, n2))
    a = w.s([phm, t2], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, PHM, TRI(C2, D2, n2)))
    b = w.s([nn, mb], 'jca', '( %s -> ( N e. NN0 /\\ %s <_ ( TMB ` N ) ) )' % (ph, n2))
    w.qed([a, b, w.inst('tm2hleb')], 'syl2anc', '( %s -> %s )' % (ph, TRI(C2, D2, '( TMB ` N )')))
    assert TRI(C2, D2, '( TMB ` N )') == CONCL_MB
    return w.run()


if __name__ == '__main__':
    if want('tmchiun'): tmchiun()
    if want('tmccans'): tmccans()
    if want('tmcmlf'): tmcmlf()
    if want('tmcmlpb'): tmcmlpb()
    if want('tmcmlt'): tmcmlt()
    if want('tmcmls'): tmcmls()
    if want('tmcmld'): tmcmld()
    if want('tmcml'): tmcml()
    if want('tmcmulc'): tmcmulc()
    if want('tmcmulb'): tmcmulb()
