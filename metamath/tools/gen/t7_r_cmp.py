"""T7: ` cmpFrag x y ` at the machine (Lean ` cmpFrag_runs ` ): the comparison
sequence (T4 ~ bwcmpf , ~ bwcmpfp1 ), the comparator's classes and their
interfaces (the adder's lemmas with ` cmp ` in place of ` carry ` ), and the
instance of ~ tm2fcmp .

    MM_DB=sorties/t7.mm python3 tools/gen/t7_r_cmp.py [LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7cmp import *
from cl import Closure
from lin import linarith
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty, ral_S
from t7_k_add import words, ifone, cand_val, CAND_X, inR_iff
from t7_l_addx import flty, load_ty, two_lam_ty, wgk

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LN, LN2 = '( # ` L )', "( # ` L' )"
TA, TB = '( toNat ` L )', "( toNat ` L' )"
FACC = dict(car='TMcar', ra='TMra', rb='TMrb', da='TMda', db='TMdb', cmp='TMcmp', fl='TMfl')
LCMP_X = lambda t: '( ( ( bitOf ` ( TMra ` %s ) ) cmpStep ( bitOf ` ( TMrb ` %s ) ) ) ` ( TMcmp ` %s ) )' % (t, t, t)
assert LCMP == LSET(cmp=LCMP_X('u'))
LCMP0_KW = lambda t: dict(cmp='1o', ra=NONE, rb=NONE, da='(/)', db='(/)')
assert LCMP0 == LSET(**LCMP0_KW('u'))


def S_(l):
    return dict(STMTS7)[l]


def tmccmss():
    ph = SEQ
    w = W('tmccmss', 'The state classes of the comparator\'s families are classes of machine states.')
    ph1 = '( %s /\\ i e. NN0 )' % ph
    inn = w.s([], 'simpr', '( %s -> i e. NN0 )' % ph1)
    seq = w.s([], 'simpl', '( %s -> %s )' % (ph1, SEQ))
    out = []
    for cond, F in [(MCOND('C'), NFMG), (OMCOND('C'), OFMG)]:
        fv = famval(w, ph1, cond, 'i', inn)
        rab = '{ h e. TMSt | %s }' % cond('h', 'i')
        ss = closed(w, ph1, 'ssrab2', '%s C_ TMSt' % rab)
        s1 = w.s([fv, ss], 'eqsstrd', '( %s -> ( %s ` i ) C_ TMSt )' % (ph1, F))
        out.append(w.s([s1, seq], 'sseqtrrd', '( %s -> ( %s ` i ) C_ ( 2nd ` T ) )' % (ph1, F)))
    j = w.s(out, 'jca', '( %s -> ( ( %s ` i ) C_ ( 2nd ` T ) /\\ ( %s ` i ) C_ ( 2nd ` T ) ) )' % (ph1, NFMG, OFMG))
    w.qed([j], 'ralrimiva', S_('tmccmss'))
    return w.run()


def tmccmin():
    ph = '( ( 2nd ` T ) = TMSt /\\ %s /\\ ( C ` 0 ) = 1o )' % PH_LL
    w = W('tmccmin', 'The comparator\'s initialisation ` { v with cmp := .eq , ra := none , rb := none , da := false , '
                     'db := false } ` puts every state into the class of iteration 0.')
    ph1 = '( %s /\\ r e. ( 2nd ` T ) )' % ph
    A1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph1, f))
    seq = A1(w.s([], 'simp1', '( %s -> %s )' % (ph, SEQ)), SEQ)
    ll = A1(w.s([w.s([], 'simp2', '( %s -> %s )' % (ph, PH_LL))], 'simpld', '( %s -> L e. Word 2o )' % ph), 'L e. Word 2o')
    ll2 = A1(w.s([w.s([], 'simp2', '( %s -> %s )' % (ph, PH_LL))], 'simprd', "( %s -> L' e. Word 2o )" % ph), "L' e. Word 2o")
    c0 = A1(w.s([], 'simp3', '( %s -> ( C ` 0 ) = 1o )' % ph), '( C ` 0 ) = 1o')
    rs = w.s([], 'simpr', '( %s -> r e. ( 2nd ` T ) )' % ph1)
    rr = w.s([rs, seq], 'eleqtrd', '( %s -> r e. TMSt )' % ph1)
    lv = load_val(w, ph1, LCMP0_KW, 'r', rr, {'1o': closed(w, ph1, 'bw1oel3o', '1o e. 3o')})
    LR = '( %s ` r )' % LCMP0
    cond = MCOND('C')
    tree = mcond_tree('C', LR, '0')
    f = lv['fields']
    cm = w.s([f['cmp'], w.s([c0], 'eqcomd', '( %s -> 1o = ( C ` 0 ) )' % ph1)], 'eqtrd', '( %s -> %s )' % (ph1, tree[0][0]))
    fl = {}
    for fld, L_ in [('da', 'L'), ('db', "L'")]:
        lw = ll if L_ == 'L' else ll2
        ln = w.s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph1, L_))
        nl = w.s([ln, w.inst('nn0nlt0')], 'syl', '( %s -> -. ( # ` %s ) < 0 )' % (ph1, L_))
        itf = w.s([nl], 'iffalsed', '( %s -> %s = (/) )' % (ph1, FLG(L_, '<', '0')))
        fl[fld] = w.s([f[fld], itf], 'eqtr4d', '( %s -> ( %s ` %s ) = %s )' % (ph1, FACC[fld], LR, FLG(L_, '<', '0')))
    ra = w.s([f['ra']], 'a1d', '( %s -> %s )' % (ph1, tree[1][0]))
    rb = w.s([f['rb']], 'a1d', '( %s -> %s )' % (ph1, tree[1][1]))
    j1 = w.s([cm, fl['da'], fl['db']], '3jca', '( %s -> %s )' % (ph1, cj(tree[0])))
    j2 = w.s([ra, rb], 'jca', '( %s -> %s )' % (ph1, cj(tree[1])))
    cst = w.s([j1, j2], 'jca', '( %s -> %s )' % (ph1, cj(tree)))
    z = closed(w, ph1, '0nn0', '0 e. NN0')
    mem = fam_pack(w, ph1, cond, '0', z, LR, lv['mem'], cst)
    w.qed([mem], 'ralrimiva', S_('tmccmin'))
    return w.run()


def tmccmrd():
    ph = PH_LL
    w = W('tmccmrd', 'The read phase of the comparator at the machine (Lean ` OpA.read ` then ` OpB.read ` ): on the '
                     'class of iteration ` i ` the flags say whether ` i ` is past each read set, and the two reads lead '
                     'into the post-read class (~ tmcadrd with ` cmp ` in place of ` carry ` ).')
    ph2 = '( %s /\\ ( i e. NN0 /\\ n e. ( %s ` i ) ) )' % (ph, NFMG)
    A2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    ll = A2(w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph), 'L e. Word 2o')
    ll2 = A2(w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph), "L' e. Word 2o")
    inn = w.s([], 'simprl', '( %s -> i e. NN0 )' % ph2)
    nin = w.s([], 'simprr', '( %s -> n e. ( %s ` i ) )' % (ph2, NFMG))
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph2, LN))
    lb = w.s([ll2, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph2, LN2))
    nmem, ncond = fam_unpack(w, ph2, MCOND('C'), 'i', inn, 'n', nin)
    T = mcond_tree('C', 'n', 'i')
    np_ = parts(w, ph2, ncond, T)
    ha = w.s([w.s([ll, inn], 'jca', '( %s -> ( L e. Word 2o /\\ i e. NN0 ) )' % ph2),
              w.s([nmem, np_[T[0][1]], np_[T[1][0]]], '3jca', '( %s -> ( n e. TMSt /\\ %s /\\ %s ) )' % (ph2, T[0][1], T[1][0]))],
             'jca', '( %s -> %s )' % (ph2, split_imp(tsub_text(ST_RDA, {'N': 'i', 'V': 'n'}))[0]))
    ca_ = split_imp(tsub_text(ST_RDA, {'N': 'i', 'V': 'n'}))[1]
    ra = w.s([ha, w.inst('tmcrda')], 'syl', '( %s -> %s )' % (ph2, ca_))
    pa = parts(w, ph2, ra, parse_conj(ca_))
    n1 = RDN1
    g = lambda f, x: '( %s ` %s )' % (FACC[f], x)
    dbn1 = w.s([pa['%s = %s' % (g('db', n1), g('db', 'n'))], np_[T[0][2]]], 'eqtrd', '( %s -> %s = %s )' % (ph2, g('db', n1), FLG("L'", '<', 'i')))
    rbe = w.s([pa['%s = %s' % (g('rb', n1), g('rb', 'n'))]], 'eqeq1d', '( %s -> ( %s = ( inr ` (/) ) <-> %s = ( inr ` (/) ) ) )' % (ph2, g('rb', n1), g('rb', 'n')))
    rbi = w.s([rbe], 'imbi2d', "( %s -> ( ( %s < i -> %s = ( inr ` (/) ) ) <-> ( %s < i -> %s = ( inr ` (/) ) ) ) )" % (ph2, LN2, g('rb', n1), LN2, g('rb', 'n')))
    rbn1 = w.s([rbi, np_[T[1][1]]], 'mpbird', "( %s -> ( %s < i -> %s = ( inr ` (/) ) ) )" % (ph2, LN2, g('rb', n1)))
    STB = tsub_text(ST_RDB, {'N': 'i', 'V': n1, 'L': "L'"})
    hb = w.s([w.s([ll2, inn], 'jca', "( %s -> ( L' e. Word 2o /\\ i e. NN0 ) )" % ph2),
              w.s([pa['%s e. TMSt' % n1], dbn1, rbn1], '3jca', '( %s -> ( %s e. TMSt /\\ %s = %s /\\ ( %s < i -> %s = ( inr ` (/) ) ) ) )'
                  % (ph2, n1, g('db', n1), FLG("L'", '<', 'i'), LN2, g('rb', n1)))], 'jca', '( %s -> %s )' % (ph2, split_imp(STB)[0]))
    cb_ = split_imp(STB)[1]
    rb = w.s([hb, w.inst('tmcrdb')], 'syl', '( %s -> %s )' % (ph2, cb_))
    pb = parts(w, ph2, rb, parse_conj(cb_))
    n2 = RDN2
    OT = omcond_tree('C', n2, 'i')
    cm2 = w.s([w.s([pb['%s = %s' % (g('cmp', n2), g('cmp', n1))], pa['%s = %s' % (g('cmp', n1), g('cmp', 'n'))]], 'eqtrd',
                   '( %s -> %s = %s )' % (ph2, g('cmp', n2), g('cmp', 'n'))), np_[T[0][0]]], 'eqtrd', '( %s -> %s )' % (ph2, OT[0][0]))
    da2 = w.s([pb['%s = %s' % (g('da', n2), g('da', n1))], pa['%s = %s' % (g('da', n1), FLG('L', '<_', 'i'))]], 'eqtrd', '( %s -> %s )' % (ph2, OT[0][1]))
    db2 = pb['%s = %s' % (g('db', n2), FLG("L'", '<_', 'i'))]
    ra2 = w.s([pb['%s = %s' % (g('ra', n2), g('ra', n1))], pa['%s = %s' % (g('ra', n1), RGV('L', 'i'))]], 'eqtrd', '( %s -> %s )' % (ph2, OT[1][0]))
    rb2 = pb['%s = %s' % (g('rb', n2), RGV("L'", 'i'))]
    oc = w.s([w.s([cm2, da2, db2], '3jca', '( %s -> %s )' % (ph2, cj(OT[0]))), w.s([ra2, rb2], 'jca', '( %s -> %s )' % (ph2, cj(OT[1])))],
             'jca', '( %s -> %s )' % (ph2, cj(OT)))
    omem = fam_pack(w, ph2, OMCOND('C'), 'i', inn, n2, pb['%s e. TMSt' % n2], oc)
    cl2 = Closure(w, ph2, {'i': ('NN0', inn), LN: ('NN0', la), LN2: ('NN0', lb)})
    def flagiff(L_, ln, fldst, h, FLDN):
        LNx = '( # ` %s )' % L_
        e = ifone(w, ph2, L_, '<', 'i', fldst, h, FLDN)
        e3 = w.s([cl2.mem(LNx, 'RR'), cl2.mem('i', 'RR')], 'ltnled', '( %s -> ( %s < i <-> -. i <_ %s ) )' % (ph2, LNx, LNx))
        e5 = w.s([inR_iff(w, ph2, L_, 'i', inn, ln)], 'notbid', '( %s -> ( -. i e. %s <-> -. i <_ %s ) )' % (ph2, OPR(L_), LNx))
        return w.s([w.s([e, e3], 'bitrd', '( %s -> ( ( %s ` %s ) = 1o <-> -. i <_ %s ) )' % (ph2, FLDN, h, LNx)), e5], 'bitr4d',
                   '( %s -> ( ( %s ` %s ) = 1o <-> -. i e. %s ) )' % (ph2, FLDN, h, OPR(L_)))
    f1 = flagiff('L', la, np_[T[0][1]], 'n', 'TMda')
    f2 = flagiff("L'", lb, dbn1, n1, 'TMdb')
    BODY = '( ( ( TMda ` n ) = 1o <-> -. i e. %s ) /\\ ( ( TMdb ` %s ) = 1o <-> -. i e. %s ) /\\ %s e. ( %s ` i ) )' % (OPR('L'), n1, OPR("L'"), n2, OFMG)
    j = w.s([f1, f2, omem], '3jca', '( %s -> %s )' % (ph2, BODY))
    w.qed([j], 'ralrimivva', ST_CMRD)
    return w.run()


def cmp_hyps(w, ph, ta, tb, nn, N):
    j3 = w.s([ta, tb, closed(w, ph, 'bw1oel3o', '1o e. 3o')], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ 1o e. 3o ) )' % (ph, TA, TB))
    return w.s([j3, nn], 'jca', '( %s -> ( ( %s e. NN0 /\\ %s e. NN0 /\\ 1o e. 3o ) /\\ %s e. NN0 ) )' % (ph, TA, TB, N))


def tmccmc0():
    ph = PH_LL
    w = W('tmccmc0', 'The comparison before bit 0 is ` .eq ` .')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    b = words(w, ph, ll, ll2)
    h = cmp_hyps(w, ph, b['ta'], b['tb'], closed(w, ph, '0nn0', '0 e. NN0'), '0')
    IFM = 'if ( ( %s mod ( 2 ^ 0 ) ) = ( %s mod ( 2 ^ 0 ) ) , 1o , ( ( %s mod ( 2 ^ 0 ) ) Ncmp ( %s mod ( 2 ^ 0 ) ) ) )' % (TA, TB, TA, TB)
    cr = w.s([h, w.inst('bwcmpf')], 'syl', '( %s -> ( %s ` 0 ) = %s )' % (ph, CMS, IFM))
    e20 = w.s([closed(w, ph, '2cn', '2 e. CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % ph)
    def m0(T, st):
        return w.s([w.s([e20], 'oveq2d', '( %s -> ( %s mod ( 2 ^ 0 ) ) = ( %s mod 1 ) )' % (ph, T, T)),
                    w.s([w.s([st], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, T)), w.inst('zmod10')], 'syl', '( %s -> ( %s mod 1 ) = 0 )' % (ph, T))],
                   'eqtrd', '( %s -> ( %s mod ( 2 ^ 0 ) ) = 0 )' % (ph, T))
    eq = w.s([m0(TA, b['ta']), m0(TB, b['tb'])], 'eqtr4d', '( %s -> ( %s mod ( 2 ^ 0 ) ) = ( %s mod ( 2 ^ 0 ) ) )' % (ph, TA, TB))
    w.qed([cr, w.s([eq], 'iftrued', '( %s -> %s = 1o )' % (ph, IFM))], 'eqtrd', S_('tmccmc0'))
    return w.run()


def tmccmcp():
    ph = '( %s /\\ N e. NN0 )' % PH_LL
    w = W('tmccmcp', 'The comparison recursion of the comparator (Lean ` cmpStep ` ), ~ bwcmpfp1 at the operands\' values.')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simplr', "( %s -> L' e. Word 2o )" % ph)
    nn = w.s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    b = words(w, ph, ll, ll2)
    w.qed([cmp_hyps(w, ph, b['ta'], b['tb'], nn, 'N'), w.inst('bwcmpfp1')], 'syl', S_('tmccmcp'))
    return w.run()


def tmccmbd():
    ph = PH_LL
    w = W('tmccmbd', 'The comparator\'s body at the machine (Lean ` cmpBody ` ): before both operands are exhausted the '
                     'test ` da && db ` fails and the load ` cmp := cmpStep ( bitOf ra ) ( bitOf rb ) cmp ` leads into the '
                     'class of the next iteration.')
    ph2 = '( %s /\\ ( i e. ( 0 ..^ %s ) /\\ p e. ( %s ` i ) ) )' % (ph, MXA, OFMS)
    A2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    ll = A2(w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph), 'L e. Word 2o')
    ll2 = A2(w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph), "L' e. Word 2o")
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph2, PH_LL))
    ifo = w.s([], 'simprl', '( %s -> i e. ( 0 ..^ %s ) )' % (ph2, MXA))
    pin = w.s([], 'simprr', '( %s -> p e. ( %s ` i ) )' % (ph2, OFMS))
    inn = w.s([ifo, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph2)
    ilt = w.s([ifo, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ph2, MXA))
    b = words(w, ph2, ll, ll2)
    cl = Closure(w, ph2, {'i': ('NN0', inn), LN: ('NN0', b['la']), LN2: ('NN0', b['lb'])})
    pmem, pc = fam_unpack(w, ph2, OMCOND(CMS), 'i', inn, 'p', pin)
    OT = omcond_tree(CMS, 'p', 'i')
    pp = parts(w, ph2, pc, OT)
    cv = cand_val(w, ph2, 'p', pmem)
    da1 = ifone(w, ph2, 'L', '<_', 'i', pp[OT[0][1]], 'p', 'TMda')
    db1 = ifone(w, ph2, "L'", '<_', 'i', pp[OT[0][2]], 'p', 'TMdb')
    an = w.s([da1, db1], 'anbi12d', "( %s -> ( ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) <-> ( %s <_ i /\\ %s <_ i ) ) )" % (ph2, LN, LN2))
    mx = w.s([cl.mem(LN, 'RR'), cl.mem(LN2, 'RR'), cl.mem('i', 'RR'), w.inst('maxle')], 'syl3anc',
             '( %s -> ( %s <_ i <-> ( %s <_ i /\\ %s <_ i ) ) )' % (ph2, MXA, LN, LN2))
    mxr = w.s([w.s([b['lb'], b['la']], 'ifcld', '( %s -> %s e. NN0 )' % (ph2, MXA))], 'nn0red', '( %s -> %s e. RR )' % (ph2, MXA))
    nmx = w.s([ilt, w.s([cl.mem('i', 'RR'), mxr], 'ltnled', '( %s -> ( i < %s <-> -. %s <_ i ) )' % (ph2, MXA, MXA))], 'mpbid',
              '( %s -> -. %s <_ i )' % (ph2, MXA))
    nan = w.s([w.s([an, mx], 'bitr4d', "( %s -> ( ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) <-> %s <_ i ) )" % (ph2, MXA)), nmx], 'mtbird',
              "( %s -> -. ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) )" % ph2)
    c0 = w.s([cv, w.s([nan], 'iffalsed', '( %s -> %s = (/) )' % (ph2, CAND_X('p')))], 'eqtrd', '( %s -> ( %s ` p ) = (/) )' % (ph2, CANDD))
    t1 = not1o(w, ph2, c0, CANDD, 'p')
    def bitreg(L_, fld, st):
        e = w.s([st], 'fveq2d', '( %s -> ( bitOf ` ( %s ` p ) ) = ( bitOf ` %s ) )' % (ph2, FACC[fld], RGV(L_, 'i')))
        lw = ll if L_ == 'L' else ll2
        g = w.s([w.s([lw, inn], 'jca', '( %s -> ( %s e. Word 2o /\\ i e. NN0 ) )' % (ph2, L_)), w.inst('tmcbrg')], 'syl',
                '( %s -> ( bitOf ` %s ) = %s )' % (ph2, RGV(L_, 'i'), BIT(L_, 'i')))
        return w.s([e, g], 'eqtrd', '( %s -> ( bitOf ` ( %s ` p ) ) = %s )' % (ph2, FACC[fld], BIT(L_, 'i')))
    ba_ = bitreg('L', 'ra', pp[OT[1][0]])
    bb_ = bitreg("L'", 'rb', pp[OT[1][1]])
    cmv = pp[OT[0][0]]
    f = w.s([ba_, bb_], 'oveq12d', '( %s -> ( ( bitOf ` ( TMra ` p ) ) cmpStep ( bitOf ` ( TMrb ` p ) ) ) = ( %s cmpStep %s ) )' % (ph2, BIT('L', 'i'), BIT("L'", 'i')))
    fold = w.s([f, cmv], 'fveq12d', '( %s -> %s = ( ( %s cmpStep %s ) ` ( %s ` i ) ) )' % (ph2, LCMP_X('p'), BIT('L', 'i'), BIT("L'", 'i'), CMS))
    rcl = lambda f_: w.s([pmem, w.inst('tmc%scl' % f_)], 'syl', '( %s -> ( %s ` p ) e. %s )' % (ph2, FACC[f_], CODOM[f_]))
    bo = lambda f_: w.s([rcl(f_), w.inst('bitofcl')], 'syl', '( %s -> ( bitOf ` ( %s ` p ) ) e. 2o )' % (ph2, FACC[f_]))
    mc = w.s([bo('ra'), bo('rb'), rcl('cmp'), w.inst('cmpstepcl')], 'syl3anc', '( %s -> %s e. 3o )' % (ph2, LCMP_X('p')))
    lv = load_val(w, ph2, lambda t: dict(cmp=LCMP_X(t)), 'p', pmem, {LCMP_X('p'): mc})
    LM = '( %s ` p )' % LCMP
    i1 = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ph2)
    NT = mcond_tree(CMS, LM, '( i + 1 )')
    cp = w.s([w.s([lls, inn], 'jca', '( %s -> ( %s /\\ i e. NN0 ) )' % (ph2, PH_LL)), w.inst('tmccmcp')], 'syl',
             '( %s -> ( %s ` ( i + 1 ) ) = ( ( %s cmpStep %s ) ` ( %s ` i ) ) )' % (ph2, CMS, BIT('L', 'i'), BIT("L'", 'i'), CMS))
    cm2 = w.s([w.s([lv['fields']['cmp'], fold], 'eqtrd', '( %s -> ( TMcmp ` %s ) = ( ( %s cmpStep %s ) ` ( %s ` i ) ) )'
                   % (ph2, LM, BIT('L', 'i'), BIT("L'", 'i'), CMS)), cp], 'eqtr4d', '( %s -> %s )' % (ph2, NT[0][0]))
    def flg(fld, L_, lnst, k):
        LNx = '( # ` %s )' % L_
        bi = w.s([lnst, inn, w.inst('nn0leltp1')], 'syl2anc', '( %s -> ( %s <_ i <-> %s < ( i + 1 ) ) )' % (ph2, LNx, LNx))
        ib = w.s([bi], 'ifbid', '( %s -> %s = %s )' % (ph2, FLG(L_, '<_', 'i'), FLG(L_, '<', '( i + 1 )')))
        return w.s([w.s([lv['fields'][fld], pp[OT[0][k]]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, FACC[fld], LM, FLG(L_, '<_', 'i'))), ib],
                   'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, FACC[fld], LM, FLG(L_, '<', '( i + 1 )'))), bi
    da2, bia = flg('da', 'L', b['la'], 1)
    db2, bib = flg('db', "L'", b['lb'], 2)
    def regnone(fld, L_, bi, k):
        LNx = '( # ` %s )' % L_
        p3 = '( %s /\\ %s < ( i + 1 ) )' % (ph2, LNx)
        le = w.s([w.s([bi], 'adantr', '( %s -> ( %s <_ i <-> %s < ( i + 1 ) ) )' % (p3, LNx, LNx)), w.s([], 'simpr', '( %s -> %s < ( i + 1 ) )' % (p3, LNx))],
                 'mpbird', '( %s -> %s <_ i )' % (p3, LNx))
        c3 = Closure(w, p3, {'i': ('NN0', w.s([inn], 'adantr', '( %s -> i e. NN0 )' % p3)),
                             LNx: ('NN0', w.s([b['la'] if L_ == 'L' else b['lb']], 'adantr', '( %s -> %s e. NN0 )' % (p3, LNx)))})
        nlt = w.s([le, w.s([c3.mem(LNx, 'RR'), c3.mem('i', 'RR')], 'lenltd', '( %s -> ( %s <_ i <-> -. i < %s ) )' % (p3, LNx, LNx))], 'mpbid',
                  '( %s -> -. i < %s )' % (p3, LNx))
        e = w.s([w.s([w.s([lv['fields'][fld], pp[OT[1][k]]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, FACC[fld], LM, RGV(L_, 'i')))], 'adantr',
                     '( %s -> ( %s ` %s ) = %s )' % (p3, FACC[fld], LM, RGV(L_, 'i'))),
                 w.s([nlt], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (p3, RGV(L_, 'i')))], 'eqtrd', '( %s -> ( %s ` %s ) = ( inr ` (/) ) )' % (p3, FACC[fld], LM))
        return w.s([e], 'ex', '( %s -> ( %s < ( i + 1 ) -> ( %s ` %s ) = ( inr ` (/) ) ) )' % (ph2, LNx, FACC[fld], LM))
    ra2 = regnone('ra', 'L', bia, 0)
    rb2 = regnone('rb', "L'", bib, 1)
    nc = w.s([w.s([cm2, da2, db2], '3jca', '( %s -> %s )' % (ph2, cj(NT[0]))), w.s([ra2, rb2], 'jca', '( %s -> %s )' % (ph2, cj(NT[1])))],
             'jca', '( %s -> %s )' % (ph2, cj(NT)))
    t3 = fam_pack(w, ph2, MCOND(CMS), '( i + 1 )', i1, LM, lv['mem'], nc)
    BODY = '( -. ( %s ` p ) = 1o /\\ ( %s ` p ) e. ( %s ` ( i + 1 ) ) )' % (CANDD, LCMP, NFMS)
    j = w.s([t1, t3], 'jca', '( %s -> %s )' % (ph2, BODY))
    w.qed([j], 'ralrimivva', ST_CMBD)
    return w.run()


def tmccmex():
    ph = PH_LL
    w = W('tmccmex', 'The comparator\'s exit at the machine: after the last iteration both operands are exhausted and '
                     'the ` cmp ` register holds the comparison of the two values (Lean ` cmpBits_eq_compare ` , T4 '
                     '~ cmpbitsfold , ~ cmpbitseq ).')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    b = words(w, ph, ll, ll2)
    mx = w.s([b['lb'], b['la']], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXA))
    phq = '( %s /\\ p e. ( %s ` %s ) )' % (ph, OFMS, MXA)
    Aq = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (phq, f))
    pin = w.s([], 'simpr', '( %s -> p e. ( %s ` %s ) )' % (phq, OFMS, MXA))
    pmem, pc = fam_unpack(w, phq, OMCOND(CMS), MXA, Aq(mx, '%s e. NN0' % MXA), 'p', pin)
    OT = omcond_tree(CMS, 'p', MXA)
    pp = parts(w, phq, pc, OT)
    cq = Closure(w, phq, {LN: ('NN0', Aq(b['la'], '%s e. NN0' % LN)), LN2: ('NN0', Aq(b['lb'], '%s e. NN0' % LN2))})
    m1 = w.s([cq.mem(LN, 'RR'), cq.mem(LN2, 'RR'), w.inst('max1')], 'syl2anc', '( %s -> %s <_ %s )' % (phq, LN, MXA))
    m2 = w.s([cq.mem(LN, 'RR'), cq.mem(LN2, 'RR'), w.inst('max2')], 'syl2anc', '( %s -> %s <_ %s )' % (phq, LN2, MXA))
    d1 = w.s([pp[OT[0][1]], w.s([m1], 'iftrued', '( %s -> %s = 1o )' % (phq, FLG('L', '<_', MXA)))], 'eqtrd', '( %s -> ( TMda ` p ) = 1o )' % phq)
    d2 = w.s([pp[OT[0][2]], w.s([m2], 'iftrued', '( %s -> %s = 1o )' % (phq, FLG("L'", '<_', MXA)))], 'eqtrd', '( %s -> ( TMdb ` p ) = 1o )' % phq)
    cv = cand_val(w, phq, 'p', pmem)
    cand = w.s([cv, w.s([w.s([d1, d2], 'jca', '( %s -> ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) )' % phq)], 'iftrued', '( %s -> %s = 1o )' % (phq, CAND_X('p')))],
               'eqtrd', '( %s -> ( %s ` p ) = 1o )' % (phq, CANDD))
    CB = "( ( L cmpBits L' ) ` 1o )"
    cf = w.s([ll, ll2, closed(w, ph, 'bw1oel3o', '1o e. 3o'), w.inst('cmpbitsfold')], 'syl3anc', '( %s -> %s = ( %s ` %s ) )' % (ph, CB, CMS, MXA))
    ce = w.s([ll, ll2, w.inst('cmpbitseq')], 'syl2anc', '( %s -> %s = %s )' % (ph, CB, NCMPV))
    fin = w.s([cf, ce], 'eqtr3d', '( %s -> ( %s ` %s ) = %s )' % (ph, CMS, MXA, NCMPV))
    cmq = w.s([pp[OT[0][0]], Aq(fin, '( %s ` %s ) = %s' % (CMS, MXA, NCMPV))], 'eqtrd', '( %s -> ( TMcmp ` p ) = %s )' % (phq, NCMPV))
    inn = rab_in(w, phq, NCMF, lambda t: '( TMcmp ` %s ) = %s' % (t, NCMPV), 'p', pmem, cmq)
    j = w.s([cand, inn], 'jca', '( %s -> ( ( %s ` p ) = 1o /\\ p e. %s ) )' % (phq, CANDD, NCMF))
    w.qed([j], 'ralrimiva', ST_CMEX)
    return w.run()


def tmccmp():
    lab = 'tmccmp'
    TREE = TREE_CMP()
    ph = cj(TREE)
    w = W(lab, '` cmpFrag x y ` at the machine (Lean ` cmpFrag_runs ` ): ~ tm2fcmp with the handlers of Lean\'s '
               '` cmpBody ` , the operand families of ~ tmcop1 , the classes of ~ tmccmrd ; both numbers are consumed '
               'and ` cmp ` holds their comparison, in ` max + 2 ` steps.')
    c = Ctx(w, ph, TREE)
    mk = machine(w, ph, c, ['K', 'J'])
    ll, ll2 = c[WRD('L', '2o')], c[WRD("L'", '2o')]
    xg, yg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    dk, dj = c[DATA_CMP[1][0]], c[DATA_CMP[1][1]]
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph, PH_LL))
    seq = mk['seq']
    ft = flty(w, ph, mk)
    T_ = lambda f: '%s e. ( 2o ^m ( 2nd ` T ) )' % FACC[f]
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    def cmp_cl(w_, phu, comp):
        if comp == '1o':
            return closed(w_, phu, 'bw1oel3o', '1o e. 3o')
        rc = lambda f: w_.s([w_.s([], 'id', '( %s -> %s )' % (phu, phu)), w_.inst('tmc%scl' % f)], 'syl', '( %s -> ( %s ` u ) e. %s )' % (phu, FACC[f], CODOM[f]))
        bo = lambda f: w_.s([rc(f), w_.inst('bitofcl')], 'syl', '( %s -> ( bitOf ` ( %s ` u ) ) e. 2o )' % (phu, FACC[f]))
        return w_.s([bo('ra'), bo('rb'), rc('cmp'), w_.inst('cmpstepcl')], 'syl3anc', '( %s -> %s e. 3o )' % (phu, comp))
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'],
             CTY('TMda'): ft[T_('da')], CTY('TMdb'): ft[T_('db')],
             CTY(CANDD): two_lam_ty(w, ph, mk, CANDD, CAND_X),
             RTY('TMrdA', 'K'): mk['k']['K']['hdl']['TMrdA'], RTY('TMrdB', 'J'): mk['k']['J']['hdl']['TMrdB'],
             LTY(LCMP): load_ty(w, ph, mk, LCMP, lambda t: dict(cmp=LCMP_X(t)), cmp_cl),
             LTY(LCMP0): load_ty(w, ph, mk, LCMP0, LCMP0_KW, cmp_cl)}
    for k in ['K', 'J']:
        extra['%s e. %s' % (k, DG)] = mk['k'][k]['kd']
    b = words(w, ph, ll, ll2)
    mx = w.s([b['lb'], b['la']], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXA))
    extra['%s e. NN0' % MXA] = mx
    extra['( 2nd ` T ) C_ ( 2nd ` T )'] = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    ncs = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NCMF)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NCMF))
    extra['%s C_ ( 2nd ` T )' % NCMF] = w.s([ncs, seq], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NCMF))
    c0 = w.s([lls, w.inst('tmccmc0')], 'syl', '( %s -> ( %s ` 0 ) = 1o )' % (ph, CMS))
    INIT = tsub_text(S_('tmccmin'), {'C': CMS})
    ini = w.s([w.s([seq, lls, c0], '3jca', '( %s -> %s )' % (ph, split_imp(INIT)[0])), w.inst('tmccmin')], 'syl', '( %s -> %s )' % (ph, split_imp(INIT)[1]))
    extra[leaf(ini)] = ini
    fzs = closed(w, ph, 'fz0ssnn0', '( 0 ... %s ) C_ NN0' % MXA)
    SS_ = tsub_text(S_('tmccmss'), {'C': CMS})
    ssr = w.s([seq, w.inst('tmccmss')], 'syl', '( %s -> %s )' % (ph, split_imp(SS_)[1]))
    body_ss = split_imp(SS_)[1][len('A. i e. NN0 '):]
    extra['A. i e. ( 0 ... %s ) %s' % (MXA, body_ss)] = w.s([fzs, ssr, w.inst('ssralv')], 'sylc', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, MXA, body_ss))
    RD_ = tsub_text(ST_CMRD, {'C': CMS})
    rdr = w.s([lls, w.inst('tmccmrd')], 'syl', '( %s -> %s )' % (ph, split_imp(RD_)[1]))
    body_rd = split_imp(RD_)[1][len('A. i e. NN0 '):]
    extra['A. i e. ( 0 ... %s ) %s' % (MXA, body_rd)] = w.s([fzs, rdr, w.inst('ssralv')], 'sylc', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, MXA, body_rd))
    bd = w.s([lls, w.inst('tmccmbd')], 'syl', '( %s -> %s )' % (ph, split_imp(ST_CMBD)[1]))
    extra[leaf(bd)] = bd
    ex = w.s([lls, w.inst('tmccmex')], 'syl', '( %s -> %s )' % (ph, split_imp(ST_CMEX)[1]))
    extra[leaf(ex)] = ex
    ZL, ZL1 = MXA, '( %s + 1 )' % MXA
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
    bld = Builder(w, ph, c, extra)
    ante, concl = split_imp(stmt('tm2fcmp'))
    tree = tsub(parse_conj(ante), CMP_MAP)
    st = bld(tree)
    c2 = tsub_text(concl, CMP_MAP)
    tri = w.s([st, w.inst('tm2fcmp')], 'syl', '( %s -> %s )' % (ph, c2))
    C1, D1, n1 = triple_parts(c2)
    cl0 = Closure(w, ph, {LN: ('NN0', b['la']), LN2: ('NN0', b['lb'])})
    m1 = w.s([cl0.mem(LN, 'RR'), cl0.mem(LN2, 'RR'), w.inst('max1')], 'syl2anc', '( %s -> %s <_ %s )' % (ph, LN, MXA))
    m2 = w.s([cl0.mem(LN, 'RR'), cl0.mem(LN2, 'RR'), w.inst('max2')], 'syl2anc', '( %s -> %s <_ %s )' % (ph, LN2, MXA))
    rules = {}
    for Lw, Xw, llst, xgst, mm in [('L', 'X', ll, xg, m1), ("L'", 'Y', ll2, yg, m2)]:
        LNx = '( # ` %s )' % Lw
        lt = linarith(w, ph, [mm], '%s < %s' % (LNx, ZL1), closure=cl0)
        z1 = cl0.mem(ZL1, 'NN0')
        e = w.s([w.s([llst, xgst], 'jca', "( %s -> ( %s e. Word 2o /\\ %s e. Word Gamma' ) )" % (ph, Lw, Xw)), w.s([z1, lt], 'jca', '( %s -> ( %s e. NN0 /\\ %s < %s ) )' % (ph, ZL1, LNx, ZL1)),
                 w.inst('tmcope')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ph, OPF(Lw, Xw), ZL1, Xw))
        rules['( %s ` %s )' % (OPF(Lw, Xw), ZL1)] = (Xw, e)
    deq, D2 = w.rewrite(D1, rules, ph)
    t2, C2, D2, n2 = hrrw(w, ph, tri, C1, D1, n1, deq=deq, qed=True)
    assert TRI(C2, D2, n2) == CONCL_CMP, (TRI(C2, D2, n2), CONCL_CMP)
    return w.run()


if __name__ == '__main__':
    for l in ['tmccmss', 'tmccmin', 'tmccmrd', 'tmccmc0', 'tmccmcp', 'tmccmbd', 'tmccmex', 'tmccmp']:
        if want(l) and l in globals(): globals()[l]()
