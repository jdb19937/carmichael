"""T7: the field tests as machine tests, and ` add x y z x ` at the machine
( ~ tm2faddx with the handlers of Lean's ` addBody ` , the operand families
of ~ tmcop1 , the classes of ~ tmcadrd / ~ tmcadbd / ~ tmcadfl ).  Lean
` add_runs_x ` ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from tm import defbody
from cl import Closure
from lin import linarith
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty, ral_S
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LN, LN2 = '( # ` L )', "( # ` L' )"


def tmcflty():
    ph = SEQ
    w = W('tmcflty', 'The ` Bool ` fields of the state record are tests of the machine (Lean ` fun v => v.carry ` , '
                     '` v.da ` , ` v.db ` , ` v.flag ` ).')
    out = {}
    for f in ['car', 'da', 'db', 'fl']:
        A = ACC[f]
        rhs = defbody('df-tm%s' % f)
        assert rhs.startswith('( v e. TMSt |-> ') and rhs.endswith(' )')
        bd = rhs[len('( v e. TMSt |-> '):-2]
        bex = w.s([], 'fvex', '%s e. _V' % bd)
        df = w.s([], 'df-tm%s' % f, '%s = %s' % (A, rhs))
        fn = w.s([bex, df], 'fnmpti', '%s Fn TMSt' % A)
        cl = w.s([], 'tmc%scl' % f, '( v e. TMSt -> ( %s ` v ) e. 2o )' % A)
        ral = w.s([cl], 'rgen', 'A. v e. TMSt ( %s ` v ) e. 2o' % A)
        ff = w.s([fn, ral], 'ffnfv' if False else 'mpbir2an', '%s : TMSt --> 2o' % A) if False else None
        bi = w.s([], 'ffnfv', '( %s : TMSt --> 2o <-> ( %s Fn TMSt /\\ A. v e. TMSt ( %s ` v ) e. 2o ) )' % (A, A, A))
        ff = w.s([fn, ral, bi], 'mpbir2an', '%s : TMSt --> 2o' % A)
        f2 = w.s([w.s([], 'id', '( %s -> %s )' % (ph, SEQ))], 'feq2d', '( %s -> ( %s : ( 2nd ` T ) --> 2o <-> %s : TMSt --> 2o ) )' % (ph, A, A))
        f3 = w.s([f2, w.s([ff], 'a1i', '( %s -> %s : TMSt --> 2o )' % (ph, A))], 'mpbird', '( %s -> %s : ( 2nd ` T ) --> 2o )' % (ph, A))
        e = w.s([closed(w, ph, '2oex', '2o e. _V'), closed(w, ph, 'fvex', '( 2nd ` T ) e. _V'), w.inst('elmapg')], 'syl2anc',
                '( %s -> ( %s e. ( 2o ^m ( 2nd ` T ) ) <-> %s : ( 2nd ` T ) --> 2o ) )' % (ph, A, A))
        out[f] = w.s([e, f3], 'mpbird', '( %s -> %s e. ( 2o ^m ( 2nd ` T ) ) )' % (ph, A))
    T_ = lambda f: '%s e. ( 2o ^m ( 2nd ` T ) )' % ACC[f]
    a = w.s([out['car'], out['da']], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, T_('car'), T_('da')))
    b = w.s([out['db'], out['fl']], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, T_('db'), T_('fl')))
    w.qed([a, b], 'jca', ST_FLTY)
    return w.run()


def flty(w, ph, mk):
    """the four field tests typed (steps keyed by accessor)"""
    st = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ph, ST_FLTY[len('( %s -> ' % SEQ):-2]))
    return parts(w, ph, st, parse_conj(ST_FLTY[len('( %s -> ' % SEQ):-2]))


def load_ty(w, ph, mk, lam, kw_of, clfn):
    """( ph -> lam e. ( S ^m S ) ) for lam = ( u e. TMSt |-> SETF( u , kw_of( u ) ) ); clfn(w, phu, comp) gives the
    closure step of a set component under phu = u e. TMSt"""
    X_of = lambda t: SETF(t, **kw_of(t))
    assert lam == '( u e. TMSt |-> %s )' % X_of('u')
    phu = 'u e. TMSt'
    uu = w.s([], 'id', '( %s -> u e. TMSt )' % phu)
    cl = st_comps(w, phu, 'u', uu)
    kw = kw_of('u')
    comps = [kw.get(f, FLD(f, 'u')) for f in ORDER]
    cls = []
    for f, comp in zip(ORDER, comps):
        if f not in kw:
            cls.append(cl[f])
        elif comp == '(/)' and CODOM[f] == '2o':
            cls.append(closed(w, phu, '0el2o', '(/) e. 2o'))
        elif comp == '1o' and CODOM[f] == '2o':
            cls.append(closed(w, phu, '1oel2o', '1o e. 2o'))
        elif comp == NONE:
            z1 = w.s([], '0lt1o', '(/) e. 1o')
            m = w.s([z1, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, OPTB))
            cls.append(w.s([m], 'a1i', '( %s -> %s e. %s )' % (phu, NONE, OPTB)))
        else:
            cls.append(clfn(w, phu, comp))
    mem, _ = tuple_facts(w, phu, comps, cls)
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    t = lamty(w, ph, mk, lam, X_of, 'TMSt', sv, mem)
    e = w.s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
    e2 = w.s([e], 'oveq1d', '( %s -> ( TMSt ^m ( 2nd ` T ) ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
    return w.s([t, e2], 'eleqtrd', '( %s -> %s e. ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % (ph, lam))


def maj_cl(w, phu, comp):
    """closure of maj ( bitOf ra ) ( bitOf rb ) carry (and sumBit, borrow) at u"""
    op = [t for t in comp.split() if t in ('majBit', 'sumBit', 'borrow')][0]
    assert op in ('majBit', 'sumBit', 'borrow'), comp
    rc = lambda f: w.s([w.s([], 'id', '( %s -> %s )' % (phu, phu)), w.inst('tmc%scl' % f)], 'syl', '( %s -> ( %s ` u ) e. %s )' % (phu, ACC[f], CODOM[f]))
    bo = lambda f: w.s([rc(f), w.inst('bitofcl')], 'syl', '( %s -> ( bitOf ` ( %s ` u ) ) e. 2o )' % (phu, ACC[f]))
    lem = {'majBit': 'majcl', 'sumBit': 'sumbitcl', 'borrow': 'borrowcl'}[op]
    return w.s([bo('ra'), bo('rb'), rc('car'), w.inst(lem)], 'syl3anc', '( %s -> %s e. 2o )' % (phu, comp))


def two_lam_ty(w, ph, mk, lam, X_of):
    """( ph -> lam e. ( 2o ^m S ) ) for a test lambda whose body is an if into { 1o , (/) }"""
    b = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % X_of('u'))
    return lamty(w, ph, mk, lam, X_of, '2o', w.s([], '2oex', '2o e. _V'), b)


def psum_ty(w, ph, mk, k, lam, X_of):
    """( ph -> lam e. ( GK ^m S ) ) for <. 1 , ( ( a op b ) ` c ) >."""
    phu = 'u e. TMSt'
    inner = X_of('u')[len('<. 1 , '):-len(' >.')]
    c = maj_cl(w, phu, inner)
    b3 = w.s([c, w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (phu, X_of('u')))
    t = lamty(w, ph, mk, lam, X_of, GAM, w.s([], 'gammaex', "Gamma' e. _V"), b3)
    e = w.s([mk['k'][k]['ge']], 'eqcomd', "( %s -> Gamma' = %s )" % (ph, GX(k)))
    e2 = w.s([e], 'oveq1d', "( %s -> ( Gamma' ^m ( 2nd ` T ) ) = ( %s ^m ( 2nd ` T ) ) )" % (ph, GX(k)))
    return w.s([t, e2], 'eleqtrd', '( %s -> %s e. ( %s ^m ( 2nd ` T ) ) )' % (ph, lam, GX(k)))


def wgk(w, ph, mk, X, k, xg):
    """( ph -> X e. Word GK ) from xg : ( ph -> X e. Word Gamma' )"""
    return w.s([xg, mk['k'][k]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(k)))


def bitsw_g(w, ph, X, xb):
    """( ph -> X e. Word Gamma' ) from xb : ( ph -> X e. Word BITS )"""
    ss = closed(w, ph, 'tm2lbits', "%s C_ Gamma'" % BITS)
    ssw = w.s([ss, w.inst('sswrd')], 'syl', "( %s -> Word %s C_ Word Gamma' )" % (ph, BITS))
    return w.s([ssw, xb], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, X))


def tmcaddx():
    lab = 'tmcaddx'
    TREE = TREE_ADDX()
    ph = cj(TREE)
    w = W(lab, '` add x y z x ` at the machine (Lean ` add_runs_x ` ): ~ tm2faddx with the handlers of '
               '` addBody ` ( ` readA ` , ` readB ` , the tests ` da ` , ` db ` , ` da && db ` , ` carry ` , the pushes '
               '` bit ( sumBit ... ) ` and ` bit true ` , the load ` carry := maj ... ` ), the operand families of '
               '~ tmcop1 , the classes of ~ tmcadrd ; the first operand\'s stack receives the sum word '
               '` bits ( addBits xs ys false ) ` in ` 2 max + 5 ` steps.')
    c = Ctx(w, ph, TREE)
    mk = machine(w, ph, c, ['K', 'J', 'I'])
    ll, ll2 = c[WRD('L', '2o')], c[WRD("L'", '2o')]
    xg, yg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    dk, dj = c[DATA_ADD[1][0]], c[DATA_ADD[1][1]]
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph, PH_LL))
    seq = mk['seq']
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    ft = flty(w, ph, mk)
    T_ = lambda f: '%s e. ( 2o ^m ( 2nd ` T ) )' % ACC[f]
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'],
             CTY('TMda'): ft[T_('da')], CTY('TMdb'): ft[T_('db')], CTY('TMcar'): ft[T_('car')], CTY(CIS): cis_ty(w, ph, mk),
             CTY(CANDD): two_lam_ty(w, ph, mk, CANDD, lambda t: 'if ( ( ( TMda ` %s ) = 1o /\\ ( TMdb ` %s ) = 1o ) , 1o , (/) )' % (t, t)),
             RTY('TMrdA', 'K'): mk['k']['K']['hdl']['TMrdA'], RTY('TMrdB', 'J'): mk['k']['J']['hdl']['TMrdB'],
             RTY('TMrdA', 'I'): mk['k']['I']['hdl']['TMrdA'],
             PTY(PSUM, 'I'): psum_ty(w, ph, mk, 'I', PSUM, lambda t: '<. 1 , ( ( ( bitOf ` ( TMra ` %s ) ) sumBit ( bitOf ` ( TMrb ` %s ) ) ) ` ( TMcar ` %s ) ) >.' % (t, t, t)),
             PTY(PBR, 'K'): pbr_ty(w, ph, mk, 'K'),
             LTY(LMAJ): load_ty(w, ph, mk, LMAJ, lambda t: dict(car='( ( ( bitOf ` ( TMra ` %s ) ) majBit ( bitOf ` ( TMrb ` %s ) ) ) ` ( TMcar ` %s ) )' % (t, t, t)), maj_cl),
             LTY(LADD0): load_ty(w, ph, mk, LADD0, lambda t: dict(car='(/)', ra=NONE, rb=NONE, da='(/)', db='(/)'), None)}
    c11g = w.s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> <. 1 , 1o >. e. Gamma' )" % ph)
    c11k = letgk(w, ph, mk, '<. 1 , 1o >.', 'I', c11g)
    extra[PTY(C11, 'I')] = constfty(w, ph, '<. 1 , 1o >.', GX('I'), c11k)
    extra["<. 1 , 1o >. e. %s" % GX('I')] = c11k
    for k in ['K', 'J', 'I']:
        extra['%s e. %s' % (k, DG)] = mk['k'][k]['kd']
    for k in ['K', 'I']:
        extra['%s C_ %s' % (BITS, GX(k))] = bitsgk(w, ph, mk, k)
        extra['4 e. %s' % GX(k)] = letgk(w, ph, mk, '4', k, g4)
    # the words Z and W
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    ifl = closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS)
    ta = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> ( toNat ` L ) e. NN0 )' % ph)
    tb = w.s([ll2, w.inst('tonatcl')], 'syl', "( %s -> ( toNat ` L' ) e. NN0 )" % ph)
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN))
    lb = w.s([ll2, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN2))
    cl0 = Closure(w, ph, {'( toNat ` L )': ('NN0', ta), "( toNat ` L' )": ('NN0', tb), LN: ('NN0', la), LN2: ('NN0', lb)})
    bn = w.s([b0, w.inst('bwbncl')], 'syl', '( %s -> ( bToNat ` (/) ) e. NN0 )' % ph)
    cl0.leaf('( bToNat ` (/) )', 'NN0', bn)
    BW = '( %s bwrd %s )' % (SUMV, MXA)
    bw = w.s([cl0.mem(SUMV, 'ZZ'), cl0.mem(MXA, 'NN0'), w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, BW))
    zb = w.s([bw, ifl, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZS, BITS))
    extra[WRD(ZS, GX('I'))] = wgk(w, ph, mk, ZS, 'I', bitsw_g(w, ph, ZS, zb))
    AB = "( ( L addBits L' ) ` (/) )"
    ab = w.s([ll, ll2, b0, w.inst('addbitscl')], 'syl3anc', '( %s -> %s e. Word 2o )' % (ph, AB))
    extra[WRD(WA, BITS)] = w.s([ab, ifl, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, WA, BITS))
    extra['( 2nd ` T ) C_ ( 2nd ` T )'] = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    extra['TMSt C_ ( 2nd ` T )'] = w.s([seq, w.inst('eqimss2')], 'syl', '( %s -> TMSt C_ ( 2nd ` T ) )' % ph)
    # the init, the mover, the classes
    c0 = w.s([lls, w.inst('tmcadc0')], 'syl', '( %s -> ( %s ` 0 ) = (/) )' % (ph, CRS))
    INIT = tsub_text(ST_ADIN, {'C': CRS})
    ini = w.s([w.s([seq, lls, c0], '3jca', '( %s -> %s )' % (ph, split_imp(INIT)[0])), w.inst('tmcadin')], 'syl', '( %s -> %s )' % (ph, split_imp(INIT)[1]))
    extra[leaf(ini)] = ini
    N = NVA('r', 'z')
    mvi = w.s([], 'tmcmvi', ST_MVI)
    hc = w.s([mvi], 'simpli', 'A. r e. TMSt A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z )' % (BITS, CIS, N, PBR, N))
    he = w.s([mvi], 'simpri', 'A. r e. TMSt -. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')))
    HC = ral_S(w, ph, mk, hc, '( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z )' % (CIS, N, PBR, N), 2)
    HE = ral_S(w, ph, mk, he, '-. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')), 1)
    extra[leaf(HC)] = HC; extra[leaf(HE)] = HE
    ZL = '( # ` %s )' % ZS
    fzs = closed(w, ph, 'fz0ssnn0', '( 0 ... %s ) C_ NN0' % ZL)
    SS_ = tsub_text(ST_ADSS, {'C': CRS})
    ssr = w.s([seq, w.inst('tmcadss')], 'syl', '( %s -> %s )' % (ph, split_imp(SS_)[1]))
    body_ss = split_imp(SS_)[1][len('A. i e. NN0 '):]
    extra['A. i e. ( 0 ... %s ) %s' % (ZL, body_ss)] = w.s([fzs, ssr, w.inst('ssralv')], 'sylc', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL, body_ss))
    RD_ = tsub_text(ST_ADRD, {'C': CRS})
    rdr = w.s([lls, w.inst('tmcadrd')], 'syl', '( %s -> %s )' % (ph, split_imp(RD_)[1]))
    body_rd = split_imp(RD_)[1][len('A. i e. NN0 '):]
    extra['A. i e. ( 0 ... %s ) %s' % (ZL, body_rd)] = w.s([fzs, rdr, w.inst('ssralv')], 'sylc', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL, body_rd))
    bd = w.s([lls, w.inst('tmcadbd')], 'syl', '( %s -> %s )' % (ph, split_imp(ST_ADBD)[1]))
    extra[leaf(bd)] = bd
    fl = w.s([w.s([seq, lls], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, SEQ, PH_LL)), w.inst('tmcadfl')], 'syl', '( %s -> %s )' % (ph, split_imp(ST_ADFL)[1]))
    extra[leaf(fl)] = fl
    # the operand families
    ZL1 = '( %s + 1 )' % ZL
    phi = '( %s /\\ i e. ( 0 ... %s ) )' % (ph, ZL1)
    Ai = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (phi, f))
    ii = w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (phi, ZL1)), w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % phi)
    def fam_ty(Lw, Xw, llst, xgst, k):
        F = OPF(Lw, Xw)
        t = w.s([Ai(llst, '%s e. Word 2o' % Lw), Ai(xgst, "%s e. Word Gamma'" % Xw), ii, w.inst('tmcopty')], 'syl3anc',
                "( %s -> ( %s ` i ) e. Word Gamma' )" % (phi, F))
        return w.s([t, Ai(mk['k'][k]['wge'], "Word %s = Word Gamma'" % GX(k))], 'eleqtrrd', '( %s -> ( %s ` i ) e. Word %s )' % (phi, F, GX(k)))
    tyx = fam_ty('L', 'X', ll, xg, 'K')
    tyy = fam_ty("L'", 'Y', ll2, yg, 'J')
    TYB = '( ( %s ` i ) e. Word %s /\\ ( %s ` i ) e. Word %s )' % (OPFX, GX('K'), OPFY, GX('J'))
    ty = w.s([w.s([tyx, tyy], 'jca', '( %s -> %s )' % (phi, TYB))], 'ralrimiva', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL1, TYB))
    extra[leaf(ty)] = ty
    for Lw, Xw, llst, xgst, dstep, k in [('L', 'X', ll, xg, dk, 'K'), ("L'", 'Y', ll2, yg, dj, 'J')]:
        F = OPF(Lw, Xw)
        v0 = w.s([llst, xgst, w.inst('tmcop0')], 'syl2anc', '( %s -> ( %s ` 0 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, F, Lw, Xw))
        e0 = w.s([v0, dstep], 'eqtr4d', '( %s -> ( %s ` 0 ) = ( D ` %s ) )' % (ph, F, k))
        extra[leaf(e0)] = e0
    phs = '( %s /\\ i e. ( 0 ... %s ) )' % (ph, ZL)
    As = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (phs, f))
    iis = w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (phs, ZL)), w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % phs)
    def step_part(Lw, Xw, llst, xgst, k):
        ST = tsub_text(ST_OP1, {'L': Lw, 'X': Xw, 'N': 'i'})
        st = w.s([As(llst, '%s e. Word 2o' % Lw), As(xgst, "%s e. Word Gamma'" % Xw), iis, w.inst('tmcop1')], 'syl3anc', '( %s -> %s )' % (phs, split_imp(ST)[1]))
        tree = parse_conj(split_imp(ST)[1])
        pp = parts(w, phs, st, tree)
        U, F = OPU(Lw), OPF(Lw, Xw)
        u1 = w.s([pp["( %s ` i ) e. Gamma'" % U], As(mk['k'][k]['ge'], "%s = Gamma'" % GX(k))], 'eleqtrrd', '( %s -> ( %s ` i ) e. %s )' % (phs, U, GX(k)))
        f1 = w.s([pp["( %s ` ( i + 1 ) ) e. Word Gamma'" % F], As(mk['k'][k]['wge'], "Word %s = Word Gamma'" % GX(k))], 'eleqtrrd',
                 '( %s -> ( %s ` ( i + 1 ) ) e. Word %s )' % (phs, F, GX(k)))
        j = w.s([u1, f1], 'jca', '( %s -> ( ( %s ` i ) e. %s /\\ ( %s ` ( i + 1 ) ) e. Word %s ) )' % (phs, U, GX(k), F, GX(k)))
        tr = tree
        return w.s([pp[cj(tr[0])], pp[cj(tr[1])], j], '3jca', '( %s -> ( %s /\\ %s /\\ ( ( %s ` i ) e. %s /\\ ( %s ` ( i + 1 ) ) e. Word %s ) ) )'
                   % (phs, cj(tr[0]), cj(tr[1]), U, GX(k), F, GX(k)))
    sx = step_part('L', 'X', ll, xg, 'K')
    sy = step_part("L'", 'Y', ll2, yg, 'J')
    SB = '( %s /\\ %s )' % (formula(w, sx)[len('( %s -> ' % phs):-2], formula(w, sy)[len('( %s -> ' % phs):-2])
    stp = w.s([w.s([sx, sy], 'jca', '( %s -> %s )' % (phs, SB))], 'ralrimiva', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL, SB))
    extra[leaf(stp)] = stp
    # apply tm2faddx
    bld = Builder(w, ph, c, extra)
    ante, concl = split_imp(stmt('tm2faddx'))
    tree = tsub(parse_conj(ante), ADD_MAP)
    st = bld(tree)
    c2 = tsub_text(concl, ADD_MAP)
    tri = w.s([st, w.inst('tm2faddx')], 'syl', '( %s -> %s )' % (ph, c2))
    C1, D1, n1 = triple_parts(c2)
    # the stacks after the loop: X ` ( |Z| + 1 ) = X , Y ` ( |Z| + 1 ) = Y
    zl = w.s([lls, w.inst('tmcadzl')], 'syl', '( %s -> %s = %s )' % (ph, ZL, MXA))
    cl0.leaf(ZL, 'NN0', w.s([zl, cl0.mem(MXA, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, ZL)))
    m1 = w.s([cl0.mem(LN, 'RR'), cl0.mem(LN2, 'RR'), w.inst('max1')], 'syl2anc', '( %s -> %s <_ %s )' % (ph, LN, MXA))
    m2 = w.s([cl0.mem(LN, 'RR'), cl0.mem(LN2, 'RR'), w.inst('max2')], 'syl2anc', '( %s -> %s <_ %s )' % (ph, LN2, MXA))
    rules = {}
    for Lw, Xw, llst, xgst, mm in [('L', 'X', ll, xg, m1), ("L'", 'Y', ll2, yg, m2)]:
        LNx = '( # ` %s )' % Lw
        lt = linarith(w, ph, [mm, zl], '%s < %s' % (LNx, ZL1), closure=cl0)
        z1 = cl0.mem(ZL1, 'NN0')
        e = w.s([w.s([llst, xgst], 'jca', "( %s -> ( %s e. Word 2o /\\ %s e. Word Gamma' ) )" % (ph, Lw, Xw)), w.s([z1, lt], 'jca', '( %s -> ( %s e. NN0 /\\ %s < %s ) )' % (ph, ZL1, LNx, ZL1)),
                 w.inst('tmcope')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ph, OPF(Lw, Xw), ZL1, Xw))
        rules['( %s ` %s )' % (OPF(Lw, Xw), ZL1)] = (Xw, e)
    deq, D2 = w.rewrite(D1, rules, ph)
    t2, C2, D2, n2 = hrrw(w, ph, tri, C1, D1, n1, deq=deq)
    # the bound: |Z| + |W| + 4 <_ 2 max + 5
    wl = w.s([ab, ifl, w.inst('lenco')], 'syl2anc', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, WA, AB))
    al = w.s([ll, ll2, b0, w.inst('addbitslen')], 'syl3anc', '( %s -> ( # ` %s ) <_ ( %s + 1 ) )' % (ph, AB, MXA))
    cl0.leaf('( # ` %s )' % WA, 'NN0', w.s([extra[WRD(WA, BITS)], w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, WA)))
    cl0.leaf('( # ` %s )' % AB, 'NN0', w.s([ab, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, AB)))
    target = '( ( 2 x. %s ) + 5 )' % MXA
    le = linarith(w, ph, [zl, wl, al], '%s <_ %s' % (n2, target), closure=cl0)
    hrle(w, ph, mk['phm'], t2, C2, D2, n2, target, cl0.mem(target, 'NN0'), le, qed=True)
    assert TRI(C2, D2, target) == CONCL_ADDX, (TRI(C2, D2, target), CONCL_ADDX)
    return w.run()


if __name__ == '__main__':
    if want('tmcflty'): tmcflty()
    if want('tmcaddx'): tmcaddx()
