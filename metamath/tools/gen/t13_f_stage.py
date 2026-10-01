"""T13: the stage lemmas of the searchF assembly (T12's D7 statements ` tmisrc4 tmisrc3 tmisrc2 ` and the new ` tmisrcz ` ),
as thin assemblies over the run lemmas (tools/gen/t13_d_run.py), the helpers (t13_b_help.py, t13_c_u0.py) and the
bound helpers (t13_e_bnd.py): the case split on the callee's verdict, ` inst ` of the run lemma and of the next stage
or ~ tmisrfl , the search value reduced by the case facts, the final stacks by ` out_init13 ` , the bound by the helper.

  tmisrc4   the verify stage: ~ tmisrc4v , then ~ tmisrc4o or ~ tmisrfl by the verdict
  tmisrc3   the extract stage: ~ tmisrc3x , then ~ tmisrc4 or ~ tmisrfl by the extraction's result
  tmisrc2   the scan stage: ~ tmisrc2s , then ~ tmisrc3 or ~ tmisrfl by the scan's result
  tmisrcz   ` searchF_le_B ` at the letters: ~ tmisrczs , then ~ tmisrc2 or ~ tmisrfl by ` len < T `

    MM_DB=sorties/t13.mm python3 tools/gen/t13_f_stage.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t13lib import *
from t13_b_help import (T_TY, C_TY, T_SM, C_SM, SV_RHS, C_X, T_X, C_XB, T_XB, C_XU, T_XU, C_XL, T_XL, C_Q, T_Q, C_W, T_W, C_U, T_U, C_L2, T_L2,
                        C_SCTMV, HB5P, NPP, EXYP, pow2le, pow2lt, p2leaf, tmbleaf, tmbmono, lemul1a, SB5, UB1, E0_, WEQ)
from t13_c_u0 import C_U0, T_U0, BEQ, UEQ, X0, SB1, HB3U, CSC_, CST_
from t13_e_bnd import (T_B4, N4O, N4F, T_B3, N3F, T_B2, N2F, T_BZ, NZF, NZ, VALS4, VALS3, VALS2, VALSZ, OUTC, FALC8, TOT2_, CST3, CST2, CZ, TZ2, VERC,
                       XQ, YN, CEX, CSN, TBS)
from t13_d_run import (LMS, Z1, Z2, Z3, Z4, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, N1, PRED, MACH, SCEQ5, BH, SCALESL, RES, IRES, LTU, W0, W7, INIT7)
from t10_d_dot import cls_to
from t10_e_doa import lift_from
from t10_n_rgf import tmbn
from t5lib import upidv, upeq
from t7lib import parts
from t9lib import STY
from lin import linarith, lineq
from cl import Closure

SEL = sys.argv[1:]
SE, GETD, OUTS, POST, TOT = P.SE, P.GETD, P.OUTS, P.POST, P.TOT
EQ, LEQD, LEQT, SC_TY = P.EQ, P.LEQD, P.LEQT, P.SC_TY
S2, E2, W2, CST4, IFQ, HB5, VX4 = P.S2, P.E2, P.W2, P.CST4, P.IFQ, P.HB5, P.VX4
MR, USED, TBL, RIT, WREST, ACCW3, D6V3, D7V3, D4V3, NPEQ = P.MR, P.USED, P.TBL, P.RIT, P.WREST, P.ACCW3, P.D6V3, P.D7V3, P.D4V3, P.NPEQ
D0V, D1V, D2V, D3V, D4V, D7V = P.D0V, P.D1V, P.D2V, P.D3V, P.D4V, P.D7V
PRE2, PRE3, PRE4 = P.PRE2, P.PRE3, P.PRE4
CASE4, VF1, VF2, VF3, UN1, UN2, UN3, UN4, UN5, WD4, STK4, CSTH4 = P.CASE4, P.VF1, P.VF2, P.VF3, P.UN1, P.UN2, P.UN3, P.UN4, P.UN5, P.WD4, P.STK4, P.CSTH4
CASE3, PW1, PW2, POS, UN4W, UN5W, STK3, CSTH3 = P.CASE3, P.PW1, P.PW2, P.POS, P.UN4W, P.UN5W, P.STK3, P.CSTH3
UP1, UP2, UP3, UN2S, UN3S, STK2, CSTH2, P2U, LSQ, EXXU, NPU, VXU, HB3 = P.UP1, P.UP2, P.UP3, P.UN2S, P.UN3S, P.STK2, P.CSTH2, P.P2U, P.LSQ, P.EXXU, P.NPU, P.VXU, P.HB3
SCAN, KSC, PSC = P.SCAN, P.KSC, P.PSC
NP = NPP.replace('P', '( # ` W )')
assert NP == "( ( B' x. ( ( # ` W ) + 1 ) ) + 1 )", NP
XTY = '( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )'
COMMA1 = '<" 4 ">'
add13s('tmisrc4', STMTS12['tmisrc4'])
add13s('tmisrc3', STMTS12['tmisrc3'])
add13s('tmisrc2', STMTS12['tmisrc2'])
# tmisrcz: the letters, the frozen bit bounds, the scales as projections, the units by their definitions
TREE_SRCZ = (MACH, ((SC_TY, LEQT),
                    (((('C e. NN0', 'K e. NN', 'N e. NN0'), ('B e. NN0', 'H e. NN0', '2 <_ B')),
                      ((LT2('Z'), LT2('G'), LT2('Y')), (LT2('U'), LT2('C'), LT2('K')), (LT2('N', 'H'), LT2('O', 'H')))),
                     (SCEQ5, (BEQ, UEQ, WEQ)))))
CONCL_SRCZ = TRI(SRCHPRE, POST, TOT)
add13('tmisrcz', TREE_SRCZ, CONCL_SRCZ)


def instp(w, ph, label, m, c, ex):
    """inst with a Bld over the Ctx c and the extra leaves ex; returns (step, C, D, n) of the triple"""
    t, cc = inst(w, ph, label, m, Bld(w, ph, c, ex))
    C, D, n = triple_parts(cc)
    return t, C, D, n


def instc(w, ph, label, m, c, ex, tree):
    """inst a helper and split its conclusion (the tree at m) into leaves"""
    t, cc = inst(w, ph, label, m, Bld(w, ph, c, ex))
    tr = tsub(tree, m)
    assert cj(tr) == cc, '\n%s\n%s' % (cj(tr)[:400], cc[:400])
    return parts(w, ph, t, tr)


def leaf_dict(*ds):
    out = {}
    for d in ds:
        out.update(d)
    return out


def letters_cl(w, ph, c, ty):
    cl = Closure(w, ph, {x: ('NN0', c['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N')})
    for x in ('Z', 'Y'):
        cl.leaf(x, 'NN0', w.s([c['%s e. NN' % x]], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, x)))
    for t in ('I e. NN0', 'L e. NN0', 'X e. NN0', "C' e. NN0", '%s e. NN0' % S2, '( 2nd ` R ) e. NN0', '( 2nd ` ( ProdL ` Q ) ) e. NN0'):
        cl.leaf(t.split(' e. ')[0], 'NN0', ty[t])
    return cl


def cst_of(w, ph, svt, first, cst):
    """( ph -> ( 2nd SE ) = cst ) from svt : ( ph -> SE = <. first , cst >. )"""
    s = w.s
    fx = s([s([], 'ifex' if first.startswith('if (') else 'fvex', '%s e. _V' % first)], 'a1i', '( %s -> %s e. _V )' % (ph, first))
    cx = s([s([], 'ovex', '%s e. _V' % cst)], 'a1i', '( %s -> %s e. _V )' % (ph, cst))
    return s([s([svt], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (ph, SE, first, cst)),
              s([fx, cx, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ph, first, cst, cst))], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (ph, SE, cst))


def to_tot(w, ph, t, C, n_cur, cst2, cst_txt):
    """rewrite the bound ( TOT2 - Z' ) of the triple t to ( TOT - Z' ) by cst2 : ( 2nd SE ) = cst_txt"""
    s = w.s
    TOT2 = TOT2_(cst_txt)
    te = s([s([cst2], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( %s + 1 ) )' % (ph, SE, cst_txt))], 'oveq1d', '( %s -> %s = %s )' % (ph, TOT, TOT2))
    beq = s([te], 'oveq1d', "( %s -> ( %s - Z' ) = ( %s - Z' ) )" % (ph, TOT, TOT2))
    t2, _, _, n2 = hrrw(w, ph, t, C, POST, n_cur, neq=s([beq], 'eqcomd', "( %s -> ( %s - Z' ) = ( %s - Z' ) )" % (ph, TOT2, TOT)))
    assert n2 == "( %s - Z' )" % TOT, n2
    return t2


def rewrite_cost(w, ph, t, C, D, n, rules):
    """rewrite the cost n of the triple by the rules {old: (new, step)}"""
    rn, n2 = w.rewrite(n, rules, ph)
    t2, _, _, n3 = hrrw(w, ph, t, C, D, n, neq=rn)
    assert n3 == n2
    return t2, n2


def bound_step(w, ph, t, C, n, phm, bnd, n_expect, cst_txt):
    """hrle with the bound helper's conclusion bnd : ( n <_ ( TOT2 - Z' ) /\\ ( TOT2 - Z' ) e. NN0 )"""
    s = w.s
    assert n == n_expect, '\nGOT  %s\nWANT %s' % (n, n_expect)
    B2 = "( %s - Z' )" % TOT2_(cst_txt)
    le = s([bnd], 'simpld', '( %s -> %s <_ %s )' % (ph, n, B2))
    mem = s([bnd], 'simprd', '( %s -> %s e. NN0 )' % (ph, B2))
    return hrle(w, ph, phm, t, C, POST, n, B2, mem, le)


# ============================================================ tmisrc4
def tmisrc4():
    lab = 'tmisrc4'
    T0 = P.TREE_SRC4
    ph = cj(T0)
    w = W(lab, 'The verify stage of Lean\'s ` searchF ` at the machine (the extraction succeeded): from the third branch with '
               'the flag true, ` verifyF ` (~ tmisrc4v ), then ` outputF ` (~ tmisrc4o ) or ` failAll ` (~ tmisrfl ) by the verdict; '
               'the final stacks are ` initStacks 1 ( encodeOutput ( getD ( search sc n ) ) ) ` by A1b\'s ~ searchval (~ t13srcv ), '
               'the cost stays within the total budget less the cost so far (~ t13srcb4o , ~ t13srcb4f ).')
    s = w.s
    c, mk, ne, ex = setup_light(w, ph, T0, PRED, 'srch', children=[6])
    phm = mk['phm']
    ty = instc(w, ph, 't13srcty', {}, c, {}, C_TY)
    sm = instc(w, ph, 't13srcsm', {}, c, {}, C_SM)
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    an, fn, qw, nn = c['A e. Word NN0'], c['F e. NN0'], ty['Q e. Word NN0'], c['N e. NN0']
    gq = enclg(w, ph, 'Q', qw, '(/)', wrd0)
    gn = ewg_(w, ph, 'N', nn, '(/)', wrd0)
    ex1 = {WG(XQ): gq, WG(YN): gn}
    # the run lemma: branch + verifyF
    t0, C0, D0, n0 = instp(w, ph, 'tmisrc4v', {'X': XQ, 'Y': YN}, c, leaf_dict(ex, ex1))
    assert C0 == CLN(Z3, N1, 'D') and D0 == CLN(Z4, NFL('( 1st ` ( F Verify A ) )'), 'D'), (C0, D0)
    VF_ = '( 1st ` ( F Verify A ) )'
    qf = s([c[EQ("Q'")]], 'eqcomd', "( %s -> ( F Verify A ) = Q' )" % ph)
    q1f = s([qf], 'fveq2d', "( %s -> %s = ( 1st ` Q' ) )" % (ph, VF_))
    t0, C0, D0, n0 = cls_to(w, ph, (t0, C0, D0, n0), VF_, "( 1st ` Q' )", q1f)
    t0, n0 = rewrite_cost(w, ph, t0, C0, D0, n0, {'( F Verify A )': ("Q'", qf)})
    assert n0 == '( 1 + %s )' % VERC, n0
    # the verdict
    vcl = s([fn, an, w.inst('verifycl')], 'syl2anc', '( %s -> ( F Verify A ) e. ( 2o X. NN0 ) )' % ph)
    vcl2 = s([c[EQ("Q'")], vcl], 'eqeltrd', "( %s -> Q' e. ( 2o X. NN0 ) )" % ph)
    w2 = s([vcl2, w.inst('xp2nd')], 'syl', "( %s -> %s e. NN0 )" % (ph, W2))
    q1 = s([vcl2, w.inst('xp1st')], 'syl', "( %s -> ( 1st ` Q' ) e. 2o )" % ph)
    two = s([q1, s([s([], 'df2o3', '2o = { (/) , 1o }')], 'a1i', '( %s -> 2o = { (/) , 1o } )' % ph)], 'eleqtrd', "( %s -> ( 1st ` Q' ) e. { (/) , 1o } )" % ph)
    cases = s([two, w.inst('elpri')], 'syl', "( %s -> ( ( 1st ` Q' ) = (/) \\/ ( 1st ` Q' ) = 1o ) )" % ph)
    # the search value, reduced by the case facts (under ph)
    svt, cc = inst(w, ph, 't13srcv', {}, Bld(w, ph, c, {}))
    cl0 = letters_cl(w, ph, c, ty)
    nlt = P.not_lt(w, ph, cl0, 'U', 'I', c['U <_ I'])
    nj = s([c["( 1st ` J ) =/= %s" % INR]], 'neneqd', "( %s -> -. ( 1st ` J ) = %s )" % (ph, INR))
    nx = s([c["( 1st ` X' ) =/= %s" % INR]], 'neneqd', "( %s -> -. ( 1st ` X' ) = %s )" % (ph, INR))
    sv2, rhs2 = P.reduce_if(w, ph, svt, SV_RHS, [nlt, nj, nx])
    assert rhs2 == '<. %s , %s >.' % (IFQ, CST4), rhs2
    cst2 = cst_of(w, ph, sv2, IFQ, CST4)
    # the leaves of the bound helper's typing part, under ph
    type_leaves = {'%s e. NN0' % W2: w2, 'X e. NN0': ty['X e. NN0'], 'L e. NN0': ty['L e. NN0'], "J' e. NN0": sm["J' e. NN0"], "C' e. NN0": ty["C' e. NN0"],
                   '%s e. NN0' % S2: ty['%s e. NN0' % S2], '%s e. NN0' % E2: sm['%s e. NN0' % E2], 'Q e. Word NN0': qw}
    outs = []
    for verdict in ('(/)', '1o'):
        cond = "( 1st ` Q' ) = %s" % verdict
        Tc = (T0, cond)
        pc = cj(Tc)
        cx = CtxX(w, pc, Tc)
        L_ = lambda st_: lift_from(w, ph, pc, st_)
        vst = cx[cond]
        exl = {k: L_(v) for k, v in leaf_dict(ex, ex1, type_leaves).items()}
        tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), "( 1st ` Q' )", verdict, vst)
        assert Dc == CLN(Z4, NFL(verdict), 'D'), Dc
        if verdict == '1o':
            t2, C2, D2, n2 = instp(w, pc, 'tmisrc4o', {'X': XQ, 'Y': YN}, cx, exl)
            assert C2 == Dc and D2 == CLN('E', S, INIT('1', '( F encodeOutput A )')), (C2, D2)
            rules = {'( D ` %s )' % k: (VALS4[k], cx['( D ` %s ) = %s' % (k, VALS4[k])]) for k in ('0', '1', '2', '3', '5', '6')}
            t2, n2 = rewrite_cost(w, pc, t2, C2, D2, n2, rules)
            assert n2 == '( 1 + %s )' % OUTC(VALS4), '\n%s\n%s' % (n2, '( 1 + %s )' % OUTC(VALS4))
            ifq = s([vst], 'iftrued', '( %s -> %s = ( inl ` <. F , A >. ) )' % (pc, IFQ))
            OUTT = '( F encodeOutput A )'
            ie = out_init13(w, pc, L_(sv2), (IFQ, ifq), CST4, OUTT, None, True, 'F', 'A',
                            fv=s([L_(fn)], 'elexd', '( %s -> F e. _V )' % pc), av=s([L_(an)], 'elexd', '( %s -> A e. _V )' % pc))
            t2, _, D2b, _ = hrrw(w, pc, t2, C2, D2, n2, deq=clneq(w, pc, 'E', S, ie, INIT('1', OUTT), INIT('1', OUTS)))
            n_exp = N4O
            bnd_lab = 't13srcb4o'
        else:
            exf = dict(exl)
            t2, C2, D2, n2 = instp(w, pc, 'tmisrfl', {'A': Z4, 'X': Y7, 'Q': PL('P', 11), 'D': 'D', 'E': 'E'}, cx, exf)
            assert C2 == Dc, (C2, Dc)
            rules = {'( D ` %s )' % k: (VALS4[k], cx['( D ` %s ) = %s' % (k, VALS4[k])]) for k in N8}
            t2, n2 = rewrite_cost(w, pc, t2, C2, D2, n2, rules)
            assert n2 == '( %s + 1 )' % FALC8(VALS4), n2
            n0_ = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o'), s([], 'neneq', '( (/) =/= 1o -> -. (/) = 1o )')], 'ax-mp', '-. (/) = 1o')
            nq = s([s([n0_], 'a1i', '( %s -> -. (/) = 1o )' % pc), s([vst], 'eqeq1d', "( %s -> ( ( 1st ` Q' ) = 1o <-> (/) = 1o ) )" % pc)], 'mtbird', "( %s -> -. ( 1st ` Q' ) = 1o )" % pc)
            ifq = s([nq], 'iffalsed', '( %s -> %s = %s )' % (pc, IFQ, INR))
            ie = out_init13(w, pc, L_(sv2), (IFQ, ifq), CST4, COMMA1, None, False)
            t2, _, D2b, _ = hrrw(w, pc, t2, C2, D2, n2, deq=clneq(w, pc, 'E', S, ie, INIT('1', COMMA1), INIT('1', OUTS)))
            n_exp = N4F
            bnd_lab = 't13srcb4f'
        assert D2b == POST
        t = hrseq(w, pc, L_(phm), tc, t2, Cc, Dc, POST, nc, n2)
        n = '( %s + %s )' % (nc, n2)
        bnd, _ = inst(w, pc, bnd_lab, {}, Bld(w, pc, cx, exl))
        t = bound_step(w, pc, t, Cc, n, L_(phm), bnd, n_exp, CST4)
        t = to_tot(w, pc, t, Cc, "( %s - Z' )" % TOT2_(CST4), L_(cst2), CST4)
        outs.append(s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, P.CONCL_SRC4)))
    st = s(outs + [cases], 'mpjaod', '( %s -> %s )' % (ph, P.CONCL_SRC4))
    qed13(w, st, lab)
    return w.run()


# ============================================================ tmisrc3
def tmisrc3():
    lab = 'tmisrc3'
    T0 = P.TREE_SRC3
    ph = cj(T0)
    w = W(lab, 'The extract stage of Lean\'s ` searchF ` at the machine (the scan succeeded): from the second branch with the '
               'flag true, ` extractF 6 3 0 5 1 2 7 4 ` (~ tmisrc3x ), then the verify stage (~ tmisrc4 ) or ` failAll ` (~ tmisrfl ) '
               'by whether the extraction found a candidate (~ t13srcx ); its bounds by ~ t13srcxb , ~ t13srcxl , ~ t13srcxu .')
    s = w.s
    c, mk, ne, ex = setup_light(w, ph, T0, PRED, 'srch', children=[5])
    phm = mk['phm']
    ty = instc(w, ph, 't13srcty', {}, c, {}, C_TY)
    sm = instc(w, ph, 't13srcsm', {}, c, {}, C_SM)
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    qw, nn, ww, lnn = ty['Q e. Word NN0'], c['N e. NN0'], sm['W e. Word NN0'], sm['L e. NN']
    gq = enclg(w, ph, 'Q', qw, '(/)', wrd0)
    gn = ewg_(w, ph, 'N', nn, '(/)', wrd0)
    exw = {WG('(/)'): wrd0, 'L e. NN': lnn, 'W e. Word NN0': ww, 'Q e. Word NN0': qw}
    # the run lemma: branch + extractF
    t0, C0, D0, n0 = instp(w, ph, 'tmisrc3x', {'X': '(/)', "X'": '(/)', 'Y': '(/)', 'X"': '(/)'}, c, leaf_dict(ex, exw))
    assert C0 == CLN(Z2, N1, 'D'), C0
    XL = "( 1st ` %s )" % LEQD["X'"]
    xle = s([s([c[EQ("X'")]], 'fveq2d', "( %s -> ( 1st ` X' ) = %s )" % (ph, XL))], 'eqcomd', "( %s -> %s = ( 1st ` X' ) )" % (ph, XL))
    V1 = 'if ( %s = %s , (/) , 1o )' % (XL, INR)
    V2 = "if ( ( 1st ` X' ) = %s , (/) , 1o )" % INR
    veq = s([s([xle], 'eqeq1d', "( %s -> ( %s = %s <-> ( 1st ` X' ) = %s ) )" % (ph, XL, INR, INR))], 'ifbid', '( %s -> %s = %s )' % (ph, V1, V2))
    t0, C0, D0, n0 = cls_to(w, ph, (t0, C0, D0, n0), V1, V2, veq)
    t0, n0 = rewrite_cost(w, ph, t0, C0, D0, n0, {LEQD["X'"]: ("X'", s([c[EQ("X'")]], 'eqcomd', "( %s -> %s = X' )" % (ph, LEQD["X'"])))})
    assert n0 == '( 1 + %s )' % CEX, '\n%s\n%s' % (n0, '( 1 + %s )' % CEX)
    D3 = triple_D(D0)
    assert D0 == CLN(Z3, NFL(V2), D3), D0
    # the stacks D3 as a Stacks object
    B = LBase(w, ph, T0, 'srch', children=[])
    vals3 = {'0': D0V, '1': D1V, '2': D2V, '3': D3V, '4': ENCL('Q', '(/)'), '5': '(/)', '6': ENCL('W', '(/)'), '7': EWg('N', '(/)')}
    xb = instc(w, ph, 't13srcxb', {}, c, exw, C_XB)
    xl = instc(w, ph, 't13srcxl', {}, c, exw, C_XL)
    mrn, usedw = xb['%s e. NN0' % MR], xb['%s e. Word NN0' % USED]
    g7 = ewg_(w, ph, MR, mrn, EWg('N', '(/)'), gn)
    g4 = enclg(w, ph, USED, usedw, ENCL('Q', '(/)'), gq)
    for k in N8:
        gk = {'0': ewg_(w, ph, 'X', ty['X e. NN0'], EWg('O', '(/)'), ewg_(w, ph, 'O', c['O e. NN0'], '(/)', wrd0)),
              '1': ewg_(w, ph, 'Z', s([c['Z e. NN']], 'nnnn0d', '( %s -> Z e. NN0 )' % ph), '(/)', wrd0),
              '2': ewg_(w, ph, "J'", sm["J' e. NN0"], '(/)', wrd0), '3': ewg_(w, ph, 'L', ty['L e. NN0'], '(/)', wrd0),
              '4': gq, '5': wrd0, '6': enclg(w, ph, 'W', ww, '(/)', wrd0), '7': gn}[k]
        B.S0.vals[k] = (vals3[k], c['( D ` %s ) = %s' % (k, vals3[k])], gk)
    S3 = B.S0.upd('6', D6V3, xl[WG(D6V3)]).upd('5', ACCW3, xl[WG(ACCW3)]).upd('7', D7V3, g7).upd('4', D4V3, g4)
    assert S3.D == D3, '\n%s\n%s' % (S3.D, D3)
    # the units at the witness list (as a word: at USED)
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    xu = instc(w, ph, 't13srcxu', {'A': USED, 'P': '( # ` W )'}, c, leaf_dict(exw, {'%s e. Word NN0' % USED: usedw, RALB(USED, "B'"): xb[RALB(USED, "B'")],
                                                                                    '( # ` %s ) <_ ( # ` W )' % USED: xb['( # ` %s ) <_ ( # ` W )' % USED], '( # ` W ) e. NN0': nw}), C_XU)
    # the search value reduced by U <_ I and the scan's some case
    svt, cc = inst(w, ph, 't13srcv', {}, Bld(w, ph, c, {}))
    cl0 = letters_cl(w, ph, c, ty)
    nlt = P.not_lt(w, ph, cl0, 'U', 'I', c['U <_ I'])
    nj = s([c["( 1st ` J ) =/= %s" % INR]], 'neneqd', "( %s -> -. ( 1st ` J ) = %s )" % (ph, INR))
    sv2, rhs2 = P.reduce_if(w, ph, svt, SV_RHS, [nlt, nj])
    assert rhs2 == "if ( ( 1st ` X' ) = %s , <. %s , %s >. , <. %s , %s >. )" % (INR, INR, CST3, IFQ, CST4), rhs2
    # cex25 : ( E2 + 1 ) 25 EXY <_ ( E2 + 1 ) 25 W'
    cl0.leaf('( # ` W )', 'NN0', nw)
    cl0.leaf("B'", 'NN0', c["B' e. NN0"]); cl0.leaf("W'", 'NN0', c["W' e. NN0"]); cl0.leaf("Z'", 'NN0', c["Z' e. NN0"]); cl0.leaf("U'", 'NN0', c["U' e. NN0"])
    cl0.leaf(E2, 'NN0', sm['%s e. NN0' % E2])
    tmbleaf(w, ph, cl0, "( ( ( 3 x. ( # ` W ) ) x. B' ) + ( ( 5 x. B' ) + 5 ) )")
    cl0.leaf(P.EXY, 'NN0', cl0.mem(P.EXY, 'NN0'))
    cex25 = P.mul_le2(w, ph, cl0, '( %s + 1 )' % E2, '( ; 2 5 x. %s )' % P.EXY, "( ; 2 5 x. W' )", linarith(w, ph, [c["%s <_ W'" % P.EXY]], "( ; 2 5 x. %s ) <_ ( ; 2 5 x. W' )" % P.EXY, closure=cl0))
    type_leaves = {'X e. NN0': ty['X e. NN0'], 'L e. NN0': ty['L e. NN0'], "J' e. NN0": sm["J' e. NN0"], "C' e. NN0": ty["C' e. NN0"],
                   '%s e. NN0' % S2: ty['%s e. NN0' % S2], '%s e. NN0' % E2: sm['%s e. NN0' % E2], 'Q e. Word NN0': qw, 'W e. Word NN0': ww}
    xf3 = {'%s e. NN0' % MR: mrn, '%s e. Word NN0' % USED: usedw, "%s < ( 2 ^ N' )" % MR: xb["%s < ( 2 ^ N' )" % MR],
           "( # ` ( encList ` %s ) ) <_ W'" % USED: xu["( # ` ( encList ` %s ) ) <_ W'" % USED], "( # ` %s ) <_ W'" % ACCW3: xl["( # ` %s ) <_ W'" % ACCW3],
           "( # ` %s ) <_ W'" % D6V3: xl["( # ` %s ) <_ W'" % D6V3], WG(ACCW3): xl[WG(ACCW3)], WG(D6V3): xl[WG(D6V3)]}
    outs = []
    for some in (False, True):
        cond = "( 1st ` X' ) = %s" % INR if not some else "-. ( 1st ` X' ) = %s" % INR
        Tc = (T0, cond)
        pc = cj(Tc)
        cx = CtxX(w, pc, Tc)
        L_ = lambda st_: lift_from(w, ph, pc, st_)
        cst = cx[cond]
        base_leaves = {k: L_(v) for k, v in leaf_dict(ex, exw, type_leaves, xf3).items()}
        base_leaves[STKD(D3)] = L_(S3.memb)
        for k in N8:
            base_leaves['( %s ` %s ) = %s' % (D3, k, S3.vals[k][0])] = L_(S3.vals[k][1])
        if not some:
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2, '(/)', s([cst], 'iftrued', '( %s -> %s = (/) )' % (pc, V2)))
            t2, C2, D2, n2 = instp(w, pc, 'tmisrfl', {'A': Z3, 'X': Y6, 'Q': PL('P', 12), 'D': D3, 'E': 'E'}, cx, base_leaves)
            assert C2 == Dc, (C2, Dc)
            rules = {'( %s ` %s )' % (D3, k): (S3.vals[k][0], base_leaves['( %s ` %s ) = %s' % (D3, k, S3.vals[k][0])]) for k in N8}
            t2, n2 = rewrite_cost(w, pc, t2, C2, D2, n2, rules)
            assert n2 == '( %s + 1 )' % FALC8(VALS3), '\n%s\n%s' % (n2, '( %s + 1 )' % FALC8(VALS3))
            svt_ = s([L_(sv2), s([cst], 'iftrued', '( %s -> %s = <. %s , %s >. )' % (pc, rhs2, INR, CST3))], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (pc, SE, INR, CST3))
            ie = out_init13(w, pc, svt_, (INR, s([], 'eqidd', '( %s -> %s = %s )' % (pc, INR, INR))), CST3, COMMA1, None, False)
            t2, _, D2b, _ = hrrw(w, pc, t2, C2, D2, n2, deq=clneq(w, pc, 'E', S, ie, INIT('1', COMMA1), INIT('1', OUTS)))
            assert D2b == POST
            t = hrseq(w, pc, L_(phm), tc, t2, Cc, Dc, POST, nc, n2)
            n = '( %s + %s )' % (nc, n2)
            bnd, _ = inst(w, pc, 't13srcb3f', {}, Bld(w, pc, cx, base_leaves))
            t = bound_step(w, pc, t, Cc, n, L_(phm), bnd, N3F, CST3)
            cst2 = cst_of(w, pc, svt_, INR, CST3)
            t = to_tot(w, pc, t, Cc, "( %s - Z' )" % TOT2_(CST3), cst2, CST3)
        else:
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2, '1o', s([cst], 'iffalsed', '( %s -> %s = 1o )' % (pc, V2)))
            xne = s([cst], 'neqned', "( %s -> ( 1st ` X' ) =/= %s )" % (pc, INR))
            xx = instc(w, pc, 't13srcx', {}, cx, leaf_dict(base_leaves, {"( 1st ` X' ) =/= %s" % INR: xne}), C_X)
            fm, au = xx['F = %s' % MR], xx['A = %s' % USED]
            mf = s([fm], 'eqcomd', '( %s -> %s = F )' % (pc, MR))
            ua = s([au], 'eqcomd', '( %s -> %s = A )' % (pc, USED))
            Lb = lambda k: base_leaves[k]
            # the facts at A and F from those at USED and MR
            an_ = s([au, Lb('%s e. Word NN0' % USED)], 'eqeltrd', '( %s -> A e. Word NN0 )' % pc)
            fn_ = s([fm, Lb('%s e. NN0' % MR)], 'eqeltrd', '( %s -> F e. NN0 )' % pc)
            rna = s([au], 'rneqd', '( %s -> ran A = ran %s )' % (pc, USED))
            rala = s([s([rna], 'raleqdv', "( %s -> ( %s <-> %s ) )" % (pc, RALB('A', "B'"), RALB(USED, "B'"))), L_(xb[RALB(USED, "B'")])], 'mpbird', '( %s -> %s )' % (pc, RALB('A', "B'")))
            lae = s([au], 'fveq2d', '( %s -> ( # ` A ) = ( # ` %s ) )' % (pc, USED))
            alt = s([lae, L_(xb["( # ` %s ) < ( 2 ^ B' )" % USED])], 'eqbrtrd', "( %s -> ( # ` A ) < ( 2 ^ B' ) )" % pc)
            flt = s([fm, L_(xb["%s < ( 2 ^ N' )" % MR])], 'eqbrtrd', "( %s -> F < ( 2 ^ N' )" % pc + ' )')
            f1 = s([L_(xb['1 <_ %s' % MR]), fm], 'breqtrrd', '( %s -> 1 <_ F )' % pc)
            ral1 = s([s([rna], 'raleqdv', '( %s -> ( A. a e. ran A 1 <_ a <-> A. a e. ran %s 1 <_ a ) )' % (pc, USED)), L_(xb['A. a e. ran %s 1 <_ a' % USED])], 'mpbird',
                     '( %s -> A. a e. ran A 1 <_ a )' % pc)
            lea = s([s([au], 'fveq2d', '( %s -> ( encList ` A ) = ( encList ` %s ) )' % (pc, USED))], 'fveq2d', '( %s -> ( # ` ( encList ` A ) ) = ( # ` ( encList ` %s ) ) )' % (pc, USED))
            leaW = s([lea, L_(xu["( # ` ( encList ` %s ) ) <_ W'" % USED])], 'eqbrtrd', "( %s -> ( # ` ( encList ` A ) ) <_ W' )" % pc)
            hb5u = tsub_text(HB5, {}).replace('( # ` A )', '( # ` %s )' % USED)
            # HB5 at A from HB5 at USED : rewrite ( # USED ) -> ( # A ) in the whole inequality
            hb5 = wff_rewrite(w, pc, L_(xu[hb5u]), hb5u, '( # ` %s )' % USED, '( # ` A )', s([lae], 'eqcomd', '( %s -> ( # ` %s ) = ( # ` A ) )' % (pc, USED)))
            a2u = wff_rewrite(w, pc, L_(xu["( ( ( # ` %s ) + 2 ) x. U' ) <_ W'" % USED]), "( ( ( # ` %s ) + 2 ) x. U' ) <_ W'" % USED, '( # ` %s )' % USED, '( # ` A )',
                              s([lae], 'eqcomd', '( %s -> ( # ` %s ) = ( # ` A ) )' % (pc, USED)))
            # the stacks: 7 and 4 in tmisrc4's form
            v7 = s([Lb('( %s ` 7 ) = %s' % (D3, D7V3)), s([s([mf], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` F ) )' % (pc, MR))], 'oveq1d', '( %s -> %s = %s )' % (pc, D7V3, D7V))], 'eqtrd',
                   '( %s -> ( %s ` 7 ) = %s )' % (pc, D3, D7V))
            v4 = s([Lb('( %s ` 4 ) = %s' % (D3, D4V3)), s([s([ua], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` A ) )' % (pc, USED))], 'oveq1d', '( %s -> %s = %s )' % (pc, D4V3, D4V))], 'eqtrd',
                   '( %s -> ( %s ` 4 ) = %s )' % (pc, D3, D4V))
            # the cost so far at the verify stage
            Z4 = "( ( Z' + 1 ) + %s )" % CEX
            clx = Closure(w, pc, {"Z'": ('NN0', cx["Z' e. NN0"]), "U'": ('NN0', cx["U' e. NN0"]), "W'": ('NN0', cx["W' e. NN0"]), "C'": ('NN0', L_(ty["C' e. NN0"]))})
            clx.leaf(CEX, 'NN0', L_(cl0.mem(CEX, 'NN0')))
            clx.leaf(S2, 'NN0', L_(ty['%s e. NN0' % S2])); clx.leaf(E2, 'NN0', L_(sm['%s e. NN0' % E2]))
            z4n = clx.mem(Z4, 'NN0')
            z4le = linarith(w, pc, [cx["Z' <_ %s" % PRE3], L_(cex25)], '%s <_ %s' % (Z4, PRE4), closure=clx, products=True)
            ex4 = dict(base_leaves)
            ex4.update({"( 1st ` X' ) =/= %s" % INR: xne, '( %s ` 7 ) = %s' % (D3, D7V): v7, '( %s ` 4 ) = %s' % (D3, D4V): v4,
                        'A e. Word NN0': an_, 'F e. NN0': fn_, RALB('A', "B'"): rala, LT2('( # ` A )', "B'"): alt, LT2('F', "N'"): flt, "B' <_ N'": L_(xb["B' <_ N'"]), '1 <_ F': f1,
                        'A. a e. ran A 1 <_ a': ral1, "( # ` ( encList ` A ) ) <_ W'": leaW, HB5: hb5, "( ( ( # ` A ) + 2 ) x. U' ) <_ W'": a2u,
                        '%s e. NN0' % Z4: z4n, '%s <_ %s' % (Z4, PRE4): z4le})
            t4, C4, D4, n4 = instp(w, pc, 'tmisrc4', {'D': D3, "Y'": ACCW3, 'X"': D6V3, "Z'": Z4}, cx, ex4)
            assert C4 == Dc and D4 == POST, '\n%s\n%s' % (C4, Dc)
            t = hrseq(w, pc, L_(phm), tc, t4, Cc, Dc, POST, nc, n4)
            n = '( %s + %s )' % (nc, n4)
            svs = s([L_(sv2), s([cst], 'iffalsed', '( %s -> %s = <. %s , %s >. )' % (pc, rhs2, IFQ, CST4))], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (pc, SE, IFQ, CST4))
            cst2 = cst_of(w, pc, svs, IFQ, CST4)
            vcl2 = s([cx[EQ("Q'")], s([fn_, an_, w.inst('verifycl')], 'syl2anc', '( %s -> ( F Verify A ) e. ( 2o X. NN0 ) )' % pc)], 'eqeltrd', "( %s -> Q' e. ( 2o X. NN0 ) )" % pc)
            clx.leaf(W2, 'NN0', s([vcl2, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` Q' ) e. NN0 )" % pc))
            clx.leaf('( 2nd ` %s )' % SE, 'NN0', s([cst2, clx.mem(CST4, 'NN0')], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, SE)))
            clx.leaf(TOT, 'NN0', clx.mem(TOT, 'NN0'))
            ceq = lineq(w, pc, n, "( %s - Z' )" % TOT, closure=clx)
            t, _, _, _ = hrrw(w, pc, t, Cc, POST, n, neq=ceq)
        outs.append(s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, P.CONCL_SRC3)))
    st = s([outs[0], outs[1]], 'pm2.61d', '( %s -> %s )' % (ph, P.CONCL_SRC3))
    qed13(w, st, lab)
    return w.run()


def wff_rewrite(w, ph, st, wff, old, new, eq):
    """( ph -> wff[old := new] ) from st : ( ph -> wff ) and eq : ( ph -> old = new ) (congruence over the wff)"""
    s = w.s
    cg, new_wff = w.wcongr(wff, {}, ph, {}, rules={old: (new, eq)})
    return s([st, cg], 'mpbid', '( %s -> %s )' % (ph, new_wff))


def second_nn0(w, ph, cl_of, se_eq, rhs):
    """( ph -> ( 2nd SE ) e. NN0 ) from se_eq : ( ph -> SE = rhs ) , rhs a nest of ` if ( c , <. a , b >. , rest ) ` whose second
    components are NN0 terms of the closure cl_of(antecedent)"""
    s = w.s

    def go(pc, term):
        """( pc -> ( 2nd term ) e. NN0 )"""
        if term.startswith('<. '):
            toks = term.split()
            d = 0; cut = None
            for i, t in enumerate(toks[1:-1], 1):
                if t in ('(', '<.', '{', '<"'):
                    d += 1
                elif t in (')', '>.', '}', '">'):
                    d -= 1
                elif d == 0 and t == ',':
                    cut = i
            a, b = ' '.join(toks[1:cut]), ' '.join(toks[cut + 1:-1])
            av = s([s([], 'ifex' if a.startswith('if (') else 'fvex', '%s e. _V' % a)], 'a1i', '( %s -> %s e. _V )' % (pc, a))
            bv = s([s([], 'ovex', '%s e. _V' % b)], 'a1i', '( %s -> %s e. _V )' % (pc, b))
            e = s([av, bv, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (pc, term, b))
            return s([e, cl_of(pc).mem(b, 'NN0')], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, term))
        assert term.startswith('if ( '), term
        toks = term.split()
        d = 0; cuts = []
        for i, t in enumerate(toks[1:-1], 1):
            if t in ('(', '<.', '{', '<"'):
                d += 1
            elif t in (')', '>.', '}', '">'):
                d -= 1
            elif d == 1 and t == ',':
                cuts.append(i)
        cond = ' '.join(toks[2:cuts[0]]); A_ = ' '.join(toks[cuts[0] + 1:cuts[1]]); B_ = ' '.join(toks[cuts[1] + 1:-1])
        pt, pf = '( %s /\\ %s )' % (pc, cond), '( %s /\\ -. %s )' % (pc, cond)
        it = s([s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = %s )' % (pt, term, A_))], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (pt, term, A_))
        i1 = s([it, go(pt, A_)], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pt, term))
        if_ = s([s([s([], 'simpr', '( %s -> -. %s )' % (pf, cond))], 'iffalsed', '( %s -> %s = %s )' % (pf, term, B_))], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (pf, term, B_))
        i2 = s([if_, go(pf, B_)], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pf, term))
        return s([i1, i2], 'pm2.61dan', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, term))
    return s([s([se_eq], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (ph, SE, rhs)), go(ph, rhs)], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (ph, SE))


def stacks_of(w, pc, Tc, vals, gams):
    """an LBase under pc with the eight base values (text -> gam step)"""
    B = LBase(w, pc, Tc, 'srch', children=[])
    for k in N8:
        B.S0.vals[k] = (vals[k], B.c['( D ` %s ) = %s' % (k, vals[k])], gams[k])
        B.gam[vals[k]] = gams[k]
    return B


# ============================================================ tmisrc2
INNER3 = "if ( ( 1st ` X' ) = %s , <. %s , %s >. , <. %s , %s >. )" % (INR, INR, CST3, IFQ, CST4)
RHS2 = 'if ( ( 1st ` J ) = %s , <. %s , %s >. , %s )' % (INR, INR, CST2, INNER3)
NONE = '( 1st ` %s ) = %s' % (SCAN, INR)
X1 = '( 1 + X )'


def tmisrc2():
    lab = 'tmisrc2'
    T0 = P.TREE_SRC2
    ph = cj(T0)
    w = W(lab, 'The scan stage of Lean\'s ` searchF ` at the machine (step 2 succeeded): from the first branch with the flag true, '
               '` scanF ` (~ tmisrc2s , T11), then the extract stage (~ tmisrc3 ) or ` failAll ` (~ tmisrfl ) by whether the scan found '
               'a window; the pool\'s facts by ~ t13srcw , the units at the pool length by ~ t13srcu , the positivity by ~ t12expos .')
    s = w.s
    c, mk, ne, ex = setup_light(w, ph, T0, PRED, 'srch', children=[4])
    phm = mk['phm']
    ty = instc(w, ph, 't13srcty', {}, c, {}, C_TY)
    qa = instc(w, ph, 't13srcqa', {}, c, {}, ('( # ` Q ) = U', RALB('Q', "B'"), 'A. a e. ran Q 1 <_ a'))
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    qw, nn, on = ty['Q e. Word NN0'], c['N e. NN0'], c['O e. NN0']
    zn0 = s([c['Z e. NN']], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)
    exw = {WG('(/)'): wrd0, 'Q e. Word NN0': qw, 'Z e. NN0': zn0, 'X e. NN0': ty['X e. NN0'], RALB('Q', "B'"): qa[RALB('Q', "B'")], 'A. a e. ran Q 1 <_ a': qa['A. a e. ran Q 1 <_ a']}
    t0, C0, D0, n0 = instp(w, ph, 'tmisrc2s', {'R': '(/)', "X'": '(/)', 'Y': '(/)', "Y'": '(/)'}, c, leaf_dict(ex, exw))
    assert C0 == CLN(Z1, N1, 'D'), C0
    # ( D ` 6 ) is empty
    D2raw = triple_D(D0)
    rd6, D2 = w.rewrite(D2raw, {'( D ` 6 )': ('(/)', c[DEQ(6, '(/)')])}, ph)
    V1s = 'if ( %s , (/) , 1o )' % NONE
    t0, _, D0, _ = hrrw(w, ph, t0, C0, D0, n0, deq=clneq(w, ph, Z2, NFL(V1s), rd6, D2raw, D2))
    jsc = s([c[EQ('J')]], 'eqcomd', '( %s -> %s = J )' % (ph, SCAN))
    V2j = 'if ( ( 1st ` J ) = %s , (/) , 1o )' % INR
    veq = s([s([s([jsc], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (ph, SCAN))], 'eqeq1d', '( %s -> ( %s <-> ( 1st ` J ) = %s ) )' % (ph, NONE, INR))], 'ifbid',
            '( %s -> %s = %s )' % (ph, V1s, V2j))
    t0, C0, D0, n0 = cls_to(w, ph, (t0, C0, D0, n0), V1s, V2j, veq)
    t0, n0 = rewrite_cost(w, ph, t0, C0, D0, n0, {SCAN: ('J', jsc)})
    assert n0 == '( 1 + %s )' % CSN, '\n%s\n%s' % (n0, '( 1 + %s )' % CSN)
    assert D0 == CLN(Z2, NFL(V2j), D2), D0
    IF2 = 'if ( %s , %s , %s )' % (NONE, EWg(X1, '(/)'), EWg(KSC, '(/)'))
    IF6 = 'if ( %s , (/) , %s )' % (NONE, ENCL(PSC, '(/)'))
    assert IF2 in D2 and IF6 in D2, D2[:500]
    # the search value reduced by U <_ I
    svt, cc = inst(w, ph, 't13srcv', {}, Bld(w, ph, c, {}))
    cl0 = letters_cl(w, ph, c, ty)
    nlt = P.not_lt(w, ph, cl0, 'U', 'I', c['U <_ I'])
    sv2, rhs2 = P.reduce_if(w, ph, svt, SV_RHS, [nlt])
    assert rhs2 == RHS2, rhs2
    vals2 = {'0': D0V, '1': EWg('Z', EWg('X', '(/)')), '2': EWg('1', '(/)'), '3': D3V, '4': XQ, '5': '(/)', '6': '(/)', '7': YN}
    type_leaves = {'X e. NN0': ty['X e. NN0'], 'L e. NN0': ty['L e. NN0'], "C' e. NN0": ty["C' e. NN0"], '%s e. NN0' % S2: ty['%s e. NN0' % S2], 'Q e. Word NN0': qw}
    outs = []
    for some in (False, True):
        cond = "( 1st ` J ) = %s" % INR if not some else "-. ( 1st ` J ) = %s" % INR
        Tc = (T0, cond)
        pc = cj(Tc)
        cx = CtxX(w, pc, Tc)
        L_ = lambda st_: lift_from(w, ph, pc, st_)
        cst = cx[cond]
        nbi = s([s([L_(jsc)], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (pc, SCAN))], 'eqeq1d', '( %s -> ( %s <-> ( 1st ` J ) = %s ) )' % (pc, NONE, INR))
        base_leaves = {k: L_(v) for k, v in leaf_dict(ex, exw, type_leaves).items()}
        wrd0c = closed(w, pc, 'wrd0', "(/) e. Word Gamma'")
        gams = {'0': ewg_(w, pc, 'X', L_(ty['X e. NN0']), EWg('O', '(/)'), ewg_(w, pc, 'O', cx['O e. NN0'], '(/)', wrd0c)),
                '1': ewg_(w, pc, 'Z', L_(zn0), EWg('X', '(/)'), ewg_(w, pc, 'X', L_(ty['X e. NN0']), '(/)', wrd0c)),
                '2': ewg_(w, pc, '1', closed(w, pc, '1nn0', '1 e. NN0'), '(/)', wrd0c), '3': ewg_(w, pc, 'L', L_(ty['L e. NN0']), '(/)', wrd0c),
                '4': enclg(w, pc, 'Q', L_(qw), '(/)', wrd0c), '5': wrd0c, '6': wrd0c, '7': ewg_(w, pc, 'N', cx['N e. NN0'], '(/)', wrd0c)}
        Bx = stacks_of(w, pc, Tc, vals2, gams)
        gz = ewg_(w, pc, 'Z', L_(zn0), '(/)', wrd0c)
        if not some:
            ns = s([cst, nbi], 'mpbird', '( %s -> %s )' % (pc, NONE))
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2j, '(/)', s([cst], 'iftrued', '( %s -> %s = (/) )' % (pc, V2j)))
            e2 = s([ns], 'iftrued', '( %s -> %s = %s )' % (pc, IF2, EWg(X1, '(/)')))
            e6 = s([ns], 'iftrued', '( %s -> %s = (/) )' % (pc, IF6))
            rd, D2n = w.rewrite(D2, {IF2: (EWg(X1, '(/)'), e2), IF6: ('(/)', e6)}, pc)
            gx1 = ewg_(w, pc, X1, s([closed(w, pc, '1nn0', '1 e. NN0'), L_(ty['X e. NN0'])], 'nn0addcld', '( %s -> %s e. NN0 )' % (pc, X1)), '(/)', wrd0c)
            Sn = Bx.S0.upd('1', EWg('Z', '(/)'), gz).upd('2', EWg(X1, '(/)'), gx1)
            up6 = upidv(w, pc, Sn.D, '6', '(/)', Sn.vals['6'][1], Bx.mk['tv'], Sn.memb, Bx.mk['k']['6']['kd'])
            assert D2n == UP(Sn.D, '6', '(/)'), '\n%s\n%s' % (D2n, UP(Sn.D, '6', '(/)'))
            deq = s([rd, up6], 'eqtrd', '( %s -> %s = %s )' % (pc, D2, Sn.D))
            tc, Cc, Dc, nc = hrrw(w, pc, tc, Cc, Dc, nc, deq=clneq(w, pc, Z2, NFL('(/)'), deq, D2, Sn.D))
            exf = dict(base_leaves)
            exf[STKD(Sn.D)] = Sn.memb
            t2, C2, D2c, n2 = instp(w, pc, 'tmisrfl', {'A': Z2, 'X': Y5, 'Q': PL('P', 13), 'D': Sn.D, 'E': 'E'}, cx, exf)
            assert C2 == Dc, (C2, Dc)
            rules = {'( %s ` %s )' % (Sn.D, k): (Sn.vals[k][0], Sn.vals[k][1]) for k in N8}
            t2, n2 = rewrite_cost(w, pc, t2, C2, D2c, n2, rules)
            assert n2 == '( %s + 1 )' % FALC8(VALS2), '\n%s\n%s' % (n2, '( %s + 1 )' % FALC8(VALS2))
            svt_ = s([L_(sv2), s([cst], 'iftrued', '( %s -> %s = <. %s , %s >. )' % (pc, RHS2, INR, CST2))], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (pc, SE, INR, CST2))
            ie = out_init13(w, pc, svt_, (INR, s([], 'eqidd', '( %s -> %s = %s )' % (pc, INR, INR))), CST2, COMMA1, None, False)
            t2, _, D2b, _ = hrrw(w, pc, t2, C2, D2c, n2, deq=clneq(w, pc, 'E', S, ie, INIT('1', COMMA1), INIT('1', OUTS)))
            assert D2b == POST
            t = hrseq(w, pc, L_(phm), tc, t2, Cc, Dc, POST, nc, n2)
            n = '( %s + %s )' % (nc, n2)
            bnd, _ = inst(w, pc, 't13srcb2f', {}, Bld(w, pc, cx, base_leaves))
            t = bound_step(w, pc, t, Cc, n, L_(phm), bnd, N2F, CST2)
            cst2 = cst_of(w, pc, svt_, INR, CST2)
            t = to_tot(w, pc, t, Cc, "( %s - Z' )" % TOT2_(CST2), cst2, CST2)
        else:
            nns = s([cst, nbi], 'mtbird', '( %s -> -. %s )' % (pc, NONE))
            jne = s([cst], 'neqned', "( %s -> ( 1st ` J ) =/= %s )" % (pc, INR))
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2j, '1o', s([cst], 'iffalsed', '( %s -> %s = 1o )' % (pc, V2j)))
            sm = instc(w, pc, 't13srcsm', {}, cx, {"( 1st ` J ) =/= %s" % INR: jne}, C_SM)
            wf = instc(w, pc, 't13srcw', {}, cx, {"( 1st ` J ) =/= %s" % INR: jne, '( # ` Q ) = U': L_(qa['( # ` Q ) = U'])}, C_W)
            kj = s([cx[EQ("J'")], s([s([s([L_(jsc)], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (pc, SCAN))], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` J ) ) )' % (pc, SCAN))],
                                        'fveq2d', "( %s -> %s = %s )" % (pc, KSC, LEQD["J'"]))], 'eqtr4d', "( %s -> J' = %s )" % (pc, KSC))
            pw = s([cx[EQ('W')], s([s([s([L_(jsc)], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (pc, SCAN))], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` J ) ) )' % (pc, SCAN))],
                                        'fveq2d', "( %s -> %s = %s )" % (pc, PSC, LEQD['W']))], 'eqtr4d', "( %s -> W = %s )" % (pc, PSC))
            e2 = s([s([nns], 'iffalsed', '( %s -> %s = %s )' % (pc, IF2, EWg(KSC, '(/)'))), s([s([s([kj], 'eqcomd', "( %s -> %s = J' )" % (pc, KSC))], 'fveq2d', "( %s -> ( encNatGam ` %s ) = ( encNatGam ` J' ) )" % (pc, KSC))], 'oveq1d',
                    '( %s -> %s = %s )' % (pc, EWg(KSC, '(/)'), EWg("J'", '(/)')))], 'eqtrd', '( %s -> %s = %s )' % (pc, IF2, EWg("J'", '(/)')))
            e6 = s([s([nns], 'iffalsed', '( %s -> %s = %s )' % (pc, IF6, ENCL(PSC, '(/)'))), s([s([s([pw], 'eqcomd', '( %s -> %s = W )' % (pc, PSC))], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` W ) )' % (pc, PSC))], 'oveq1d',
                    '( %s -> %s = %s )' % (pc, ENCL(PSC, '(/)'), ENCL('W', '(/)')))], 'eqtrd', '( %s -> %s = %s )' % (pc, IF6, ENCL('W', '(/)')))
            rd, D2s = w.rewrite(D2, {IF2: (EWg("J'", '(/)'), e2), IF6: (ENCL('W', '(/)'), e6)}, pc)
            g2j = ewg_(w, pc, "J'", sm["J' e. NN0"], '(/)', wrd0c)
            g6w = enclg(w, pc, 'W', sm['W e. Word NN0'], '(/)', wrd0c)
            Ss = Bx.S0.upd('1', EWg('Z', '(/)'), gz).upd('2', EWg("J'", '(/)'), g2j).upd('6', ENCL('W', '(/)'), g6w)
            assert D2s == Ss.D, '\n%s\n%s' % (D2s, Ss.D)
            tc, Cc, Dc, nc = hrrw(w, pc, tc, Cc, Dc, nc, deq=clneq(w, pc, Z2, N1, rd, D2, Ss.D))
            # the units at # W, the positivity, the cost so far
            ww, lnn = sm['W e. Word NN0'], sm['L e. NN']
            nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % pc)
            uu = instc(w, pc, 't13srcu', {'P': '( # ` W )'}, cx, {'( # ` W ) e. NN0': nw, '( # ` W ) <_ %s' % P2U: wf['( # ` W ) <_ ( 2 ^ U )'], 'L e. NN0': L_(ty['L e. NN0'])}, C_U)
            z0 = P.z0_in_sty(w, pc)
            j = s([s([lnn, cx['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % pc), s([ww, z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (pc, P.Z0, STY))], 'jca',
                  '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (pc, P.Z0, STY))
            ritp = s([j, w.inst('exitp')], 'syl', '( %s -> %s )' % (pc, tsub_text(split_imp(stmt('exitp'))[1], {'G': 'N', 'Z': P.Z0})))
            rin = s([ritp], 'simp1d', '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (pc, RIT))
            pos, _ = inst(w, pc, 't12expos', {'I': RIT}, Bld(w, pc, cx, {'L e. NN': lnn, 'W e. Word NN0': ww, 'A. a e. ran W 2 <_ a': wf['A. a e. ran W 2 <_ a'], '%s e. ( 0 ... ( # ` W ) )' % RIT: rin}))
            clx = Closure(w, pc, {"Z'": ('NN0', cx["Z' e. NN0"]), "U'": ('NN0', cx["U' e. NN0"]), "W'": ('NN0', cx["W' e. NN0"]), "C'": ('NN0', L_(ty["C' e. NN0"])), "B'": ('NN0', cx["B' e. NN0"])})
            clx.leaf(S2, 'NN0', L_(ty['%s e. NN0' % S2])); clx.leaf('( # ` Q )', 'NN0', s([L_(qw), w.inst('lencl')], 'syl', '( %s -> ( # ` Q ) e. NN0 )' % pc))
            clx.leaf('( # ` W )', 'NN0', nw)
            tmbleaf(w, pc, clx, TBS[len('( TMB ` '):-2])
            csnle = P.mul_le2(w, pc, clx, '( %s + 1 )' % S2, TBS, "U'", cx[HB3])
            Z3v = "( ( Z' + 1 ) + %s )" % CSN
            z3n = clx.mem(Z3v, 'NN0')
            z3le = linarith(w, pc, [cx["Z' <_ %s" % PRE2], csnle], '%s <_ %s' % (Z3v, PRE3), closure=clx, products=True)
            ex3 = dict(base_leaves)
            ex3.update({STKD(Ss.D): Ss.memb, "( 1st ` J ) =/= %s" % INR: jne, '%s = %s' % (NP, NP): s([s([], 'eqid', '%s = %s' % (NP, NP))], 'a1i', '( %s -> %s = %s )' % (pc, NP, NP)),
                        P.POS1: s([pos], 'simpld', '( %s -> %s )' % (pc, P.POS1)), P.POS2: s([pos], 'simprd', '( %s -> %s )' % (pc, P.POS2)),
                        '%s e. NN0' % NP: clx.mem(NP, 'NN0'), '%s e. NN0' % Z3v: z3n, '%s <_ %s' % (Z3v, PRE3): z3le})
            ex3.update(wf); ex3.update(uu)
            for k in N8:
                ex3['( %s ` %s ) = %s' % (Ss.D, k, Ss.vals[k][0])] = Ss.vals[k][1]
            t3, C3, D3c, n3 = instp(w, pc, 'tmisrc3', {'D': Ss.D, "N'": NP, "Z'": Z3v}, cx, ex3)
            assert C3 == Dc and D3c == POST, '\n%s\n%s' % (C3, Dc)
            t = hrseq(w, pc, L_(phm), tc, t3, Cc, Dc, POST, nc, n3)
            n = '( %s + %s )' % (nc, n3)
            svs = s([L_(sv2), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, RHS2, INNER3))], 'eqtrd', '( %s -> %s = %s )' % (pc, SE, INNER3))
            clx.leaf(E2, 'NN0', sm['%s e. NN0' % E2])
            sen = second_nn0(w, pc, cl_of_final(w, pc, Tc, cx, clx, lnn, ww, wf, L_, cx["B' e. NN0"], cx['U e. NN0']), svs, INNER3)
            clx.leaf('( 2nd ` %s )' % SE, 'NN0', sen)
            clx.leaf(TOT, 'NN0', clx.mem(TOT, 'NN0'))
            clx.leaf(CSN, 'NN0', clx.mem(CSN, 'NN0'))
            ceq = lineq(w, pc, n, "( %s - Z' )" % TOT, closure=clx)
            t, _, _, _ = hrrw(w, pc, t, Cc, POST, n, neq=ceq)
        outs.append(s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, P.CONCL_SRC2)))
    st = s([outs[0], outs[1]], 'pm2.61d', '( %s -> %s )' % (ph, P.CONCL_SRC2))
    qed13(w, st, lab)
    return w.run()


def cl_of_final(w, pc, Tc, cx, clx, lnn, ww, wf, L_, b1n, un):
    """the closure factory for second_nn0 on INNER3 under pc: C' S2 E2 everywhere, ( 2nd Q' ) in the some branch of the
    extraction (F , A typed through ~ t13srcx and ~ t13srcxb at N' := the pool bound)"""
    s = w.s
    NPx = NP

    def cl_of(pc2):
        Lx = (lambda st_: lift_from(w, pc, pc2, st_)) if pc2 != pc else (lambda st_: st_)
        cl2 = Closure(w, pc2, {})
        for x_ in ("C'", S2, E2):
            cl2.leaf(x_, 'NN0', Lx(clx.mem(x_, 'NN0')))
        if pc2.endswith("/\\ -. ( 1st ` X' ) = %s )" % INR):
            ne_ = s([s([], 'simpr', "( %s -> -. ( 1st ` X' ) = %s )" % (pc2, INR))], 'neqned', "( %s -> ( 1st ` X' ) =/= %s )" % (pc2, INR))
            cx2 = CtxX(w, pc2, (Tc, "-. ( 1st ` X' ) = %s" % INR))
            xx = instc(w, pc2, 't13srcx', {}, cx2, {'L e. NN': Lx(lnn), 'W e. Word NN0': Lx(ww), "( 1st ` X' ) =/= %s" % INR: ne_}, C_X)
            xb = instc(w, pc2, 't13srcxb', {"N'": NPx}, cx2, {'L e. NN': Lx(lnn), 'W e. Word NN0': Lx(ww), RALB('W', "B'"): Lx(wf[RALB('W', "B'")]),
                                                                'A. a e. ran W 2 <_ a': Lx(wf['A. a e. ran W 2 <_ a']), '( # ` W ) <_ ( 2 ^ U )': Lx(wf['( # ` W ) <_ ( 2 ^ U )']),
                                                                '%s = %s' % (NPx, NPx): s([s([], 'eqid', '%s = %s' % (NPx, NPx))], 'a1i', '( %s -> %s = %s )' % (pc2, NPx, NPx))}, C_XB)
            fn_ = s([xx['F = %s' % MR], xb['%s e. NN0' % MR]], 'eqeltrd', '( %s -> F e. NN0 )' % pc2)
            an_ = s([xx['A = %s' % USED], xb['%s e. Word NN0' % USED]], 'eqeltrd', '( %s -> A e. Word NN0 )' % pc2)
            vcl2 = s([cx2[EQ("Q'")], s([fn_, an_, w.inst('verifycl')], 'syl2anc', '( %s -> ( F Verify A ) e. ( 2o X. NN0 ) )' % pc2)], 'eqeltrd', "( %s -> Q' e. ( 2o X. NN0 ) )" % pc2)
            cl2.leaf(W2, 'NN0', s([vcl2, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` Q' ) e. NN0 )" % pc2))
        return cl2
    return cl_of


# ============================================================ tmisrcz
class _Obj:
    pass


def lt2m(w, ph, cl, A_, an_rr, B_, C_, le, lt):
    """( ph -> A < 2 ^ C ) from lt : A < 2 ^ B , le : B <_ C (~ t13lt2m )"""
    s = w.s
    j = s([s([an_rr, cl.mem(B_, 'NN0'), cl.mem(C_, 'NN0')], '3jca', '( %s -> ( %s e. RR /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (ph, A_, B_, C_)),
           s([le, lt], 'jca', '( %s -> ( %s <_ %s /\\ %s < ( 2 ^ %s ) ) )' % (ph, B_, C_, A_, B_))], 'jca',
          '( %s -> ( ( %s e. RR /\\ %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s <_ %s /\\ %s < ( 2 ^ %s ) ) ) )' % (ph, A_, B_, C_, B_, C_, A_, B_))
    return s([j, w.inst('t13lt2m')], 'syl', '( %s -> %s < ( 2 ^ %s ) )' % (ph, A_, C_))


def tmisrcz():
    lab = 'tmisrcz'
    T0 = TREE_SRCZ
    ph = cj(T0)
    w = W(lab, 'Lean\'s ` searchF_le_B ` at the letters of A1b\'s ~ searchval , the scales as the projections of ` scalesTM C1 K n ` '
               'and the units by their definitions: ` inputF ; scalesF ; step2F ` (~ tmisrczs ), then the scan stage (~ tmisrc2 ) '
               'or ` failAll ` (~ tmisrfl ) by ` len < T ` ; the units by ~ t13srcu0 , the window by ~ t13srcq , the budget by ~ t13srcbzf .')
    s = w.s
    c, mk, ne, ex = setup_light(w, ph, T0, PRED, 'srch', children=[3])
    ob = _Obj(); ob.w, ob.ph, ob.ex = w, ph, ex
    deep2(ob, 'srch', 3, 2)
    phm = mk['phm']
    ty = instc(w, ph, 't13srcty', {}, c, {}, C_TY)
    u = instc(w, ph, 't13srcu0', {}, c, {}, C_U0)
    cn, knn, nn, bn, hn = c['C e. NN0'], c['K e. NN'], c['N e. NN0'], c['B e. NN0'], c['H e. NN0']
    zn, gn, yn, un, on = c['Z e. NN'], c['G e. NN0'], c['Y e. NN'], c['U e. NN0'], c['O e. NN0']
    zn0 = s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)
    cl = Closure(w, ph, {'C': ('NN0', cn), 'N': ('NN0', nn), 'B': ('NN0', bn), 'H': ('NN0', hn), 'U': ('NN0', un), 'O': ('NN0', on), 'G': ('NN0', gn)})
    cl.leaf('Z', 'NN0', zn0); cl.leaf('K', 'NN0', s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % ph)); cl.leaf("B'", 'NN0', u["B' e. NN0"])
    cl.leaf("U'", 'NN0', u["U' e. NN0"]); cl.leaf("W'", 'NN0', u["W' e. NN0"])
    for x in ('I', 'L', 'X', "C'", '( 2nd ` R )', '( 2nd ` ( ProdL ` Q ) )', S2):
        cl.leaf(x, 'NN0', ty['%s e. NN0' % x])
    hbh = linarith(w, ph, [cl.ge0('B')], 'H <_ %s' % BH, closure=cl)
    bbh = linarith(w, ph, [cl.ge0('H')], 'B <_ %s' % BH, closure=cl)
    nbh = lt2m(w, ph, cl, 'N', cl.mem('N', 'RR'), 'H', BH, hbh, c[LT2('N', 'H')])
    cbh = lt2m(w, ph, cl, 'C', cl.mem('C', 'RR'), 'B', BH, bbh, c[LT2('C')])
    kbh = lt2m(w, ph, cl, 'K', cl.mem('K', 'RR'), 'B', BH, bbh, c[LT2('K')])
    # the machine part
    t0, C0, D0, n0 = instp(w, ph, 'tmisrczs', {}, c, leaf_dict(ex, {LT2('N', BH): nbh, LT2('C', BH): cbh, LT2('K', BH): kbh}))
    assert C0 == SRCHPRE, C0
    # the reservoir's pieces as the letters, in the class, the stacks and the cost
    def rw(t, C_, D_, n_, old, new, eq):
        rd, D2 = w.rewrite(D_, {old: (new, eq)}, ph)
        rn, n2 = w.rewrite(n_, {old: (new, eq)}, ph)
        t2, _, D3, n3 = hrrw(w, ph, t, C_, D_, n_, deq=rd if D2 != D_ else None, neq=rn if n2 != n_ else None)
        return t2, D3, n3
    t0, D0, n0 = rw(t0, C0, D0, n0, RES, 'R', s([c[EQ('R')]], 'eqcomd', '( %s -> %s = R )' % (ph, RES)))
    t0, D0, n0 = rw(t0, C0, D0, n0, IRES.replace(RES, 'R'), 'I', s([c[EQ('I')]], 'eqcomd', '( %s -> %s = I )' % (ph, IRES.replace(RES, 'R'))))
    QQ = '( ( 1st ` R ) substr <. ( I - U ) , I >. )'
    t0, D0, n0 = rw(t0, C0, D0, n0, QQ, 'Q', s([c[EQ('Q')]], 'eqcomd', '( %s -> %s = Q )' % (ph, QQ)))
    t0, D0, n0 = rw(t0, C0, D0, n0, LEQD['L'], 'L', s([c[EQ('L')]], 'eqcomd', '( %s -> %s = L )' % (ph, LEQD['L'])))
    t0, D0, n0 = rw(t0, C0, D0, n0, LEQD['X'], 'X', s([c[EQ('X')]], 'eqcomd', '( %s -> %s = X )' % (ph, LEQD['X'])))
    LTU_ = 'I < U'
    IF0 = 'if ( %s , %s , %s )' % (LTU_, EWg('U', EWg('O', '(/)')), EWg('X', EWg('O', '(/)')))
    IF1 = 'if ( %s , %s , %s )' % (LTU_, EWg('Z', '(/)'), EWg('Z', EWg('X', '(/)')))
    IF2 = 'if ( %s , %s , %s )' % (LTU_, EWg('I', '(/)'), EWg('1', '(/)'))
    IF3 = 'if ( %s , (/) , %s )' % (LTU_, EWg('L', '(/)'))
    IF4 = 'if ( %s , %s , %s )' % (LTU_, ENCL('( 1st ` R )', '(/)'), ENCL('Q', '(/)'))
    Dz = UP(UP(UP(UP(UP(INIT7, '0', IF0), '1', IF1), '2', IF2), '3', IF3), '4', IF4)
    VZ = 'if ( %s , (/) , 1o )' % LTU_
    assert D0 == CLN(Z1, NFL(VZ), Dz), '\n%s\n%s' % (D0, CLN(Z1, NFL(VZ), Dz))
    CIN = '( ( 2 x. ( # ` ( encodeNat ` N ) ) ) + 4 )'
    IFC = 'if ( %s , ( ( 2nd ` R ) + 1 ) , ( ( ( 2nd ` R ) + ( 2 x. U ) ) + 2 ) )' % LTU_
    NZ0 = '( ( %s + ( ; 5 0 x. %s ) ) + ( ( %s + 1 ) x. %s ) )' % (CIN, CSC_, IFC, CST_)
    assert n0 == NZ0, '\n%s\n%s' % (n0, NZ0)
    # the search value and the cost pieces
    svt, cc = inst(w, ph, 't13srcv', {}, Bld(w, ph, c, {}))
    egl = s([nn, w.inst('encnatgamlen')], 'syl', '( %s -> ( # ` ( encNatGam ` N ) ) = ( # ` ( encodeNat ` N ) ) )' % ph)
    egb = s([nn, hn, c[LT2('N', 'H')], w.inst('tm2lentlt')], 'syl3anc', '( %s -> ( # ` ( encNatGam ` N ) ) <_ H )' % ph)
    cl.leaf('( # ` ( encodeNat ` N ) )', 'NN0', s([s([nn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` N ) e. Word 2o )' % ph), w.inst('lencl')], 'syl', '( %s -> ( # ` ( encodeNat ` N ) ) e. NN0 )' % ph))
    cl.leaf('( # ` ( encNatGam ` N ) )', 'NN0', s([encw(w, ph, 'N', nn), w.inst('lencl')], 'syl', '( %s -> ( # ` ( encNatGam ` N ) ) e. NN0 )' % ph))
    cin = linarith(w, ph, [egl, egb, u["( ( 2 x. H ) + 4 ) <_ U'"]], "%s <_ U'" % CIN, closure=cl)
    tmbleaf(w, ph, cl, CSC_[len('( TMB ` '):-2]); tmbleaf(w, ph, cl, CST_[len('( TMB ` '):-2])
    # the stacks
    w0g = encw(w, ph, 'N', nn)
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    w7g = wgcat(w, ph, W0, '<" 4 ">', w0g, s4)
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    e7w = s([s([s4, w.inst('ccatrid')], 'syl', '( %s -> ( <" 4 "> ++ (/) ) = <" 4 "> )' % ph)], 'oveq2d', '( %s -> %s = %s )' % (ph, YN, W7))
    outs = []
    for fail in (True, False):
        cond = LTU_ if fail else '-. %s' % LTU_
        Tc = (T0, cond)
        pc = cj(Tc)
        cx = CtxX(w, pc, Tc)
        L_ = lambda st_: lift_from(w, ph, pc, st_)
        cst = cx[cond]
        mkc = machine(w, pc, cx, N8)
        nec = ne_fn(w, pc, cx, set())
        S7 = P.init_stacks(w, pc, mkc, nec, '7', W7, L_(w7g))
        wrd0c = closed(w, pc, 'wrd0', "(/) e. Word Gamma'")
        e7 = s([S7.vals['7'][1], s([L_(e7w)], 'eqcomd', '( %s -> %s = %s )' % (pc, W7, YN))], 'eqtrd', '( %s -> ( %s ` 7 ) = %s )' % (pc, INIT7, YN))
        go = ewg_(w, pc, 'O', cx['O e. NN0'], '(/)', wrd0c)
        ul = {k: L_(v) for k, v in u.items()}
        tyl = {k: L_(v) for k, v in ty.items()}
        clc = Closure(w, pc, {'U': ('NN0', cx['U e. NN0']), 'B': ('NN0', cx['B e. NN0']), 'H': ('NN0', cx['H e. NN0']), 'N': ('NN0', cx['N e. NN0'])})
        clc.leaf("U'", 'NN0', ul["U' e. NN0"]); clc.leaf("W'", 'NN0', ul["W' e. NN0"]); clc.leaf("B'", 'NN0', ul["B' e. NN0"])
        for x in ("C'", '( 2nd ` R )', '( 2nd ` ( ProdL ` Q ) )', 'I', 'L', 'X', S2):
            clc.leaf(x, 'NN0', tyl['%s e. NN0' % x])
        clc.leaf('( # ` ( encodeNat ` N ) )', 'NN0', L_(cl.mem('( # ` ( encodeNat ` N ) )', 'NN0')))
        tmbleaf(w, pc, clc, CSC_[len('( TMB ` '):-2]); tmbleaf(w, pc, clc, CST_[len('( TMB ` '):-2])
        base_leaves = {k: L_(v) for k, v in ex.items()}
        base_leaves.update(ul); base_leaves.update(tyl)
        if fail:
            ifs = {IF0: (EWg('U', EWg('O', '(/)')), s([cst], 'iftrued', '( %s -> %s = %s )' % (pc, IF0, EWg('U', EWg('O', '(/)'))))),
                   IF1: (EWg('Z', '(/)'), s([cst], 'iftrued', '( %s -> %s = %s )' % (pc, IF1, EWg('Z', '(/)')))),
                   IF2: (EWg('I', '(/)'), s([cst], 'iftrued', '( %s -> %s = %s )' % (pc, IF2, EWg('I', '(/)')))),
                   IF3: ('(/)', s([cst], 'iftrued', '( %s -> %s = (/) )' % (pc, IF3))),
                   IF4: (ENCL('( 1st ` R )', '(/)'), s([cst], 'iftrued', '( %s -> %s = %s )' % (pc, IF4, ENCL('( 1st ` R )', '(/)'))))}
            fc = s([cst], 'iftrued', '( %s -> %s = ( ( 2nd ` R ) + 1 ) )' % (pc, IFC))
            vals = {'0': EWg('U', EWg('O', '(/)')), '1': EWg('Z', '(/)'), '2': EWg('I', '(/)'), '3': '(/)', '4': ENCL('( 1st ` R )', '(/)')}
            rcl = s([s([cx['Z e. NN'], cx['G e. NN0']], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % pc), cx['Y e. NN'], w.inst('reservoircl')], 'syl2anc',
                     '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (pc, RES))
            r1w = s([s([cx[EQ('R')], rcl], 'eqeltrd', '( %s -> R e. ( Word NN0 X. NN0 ) )' % pc), w.inst('xp1st')], 'syl', '( %s -> ( 1st ` R ) e. Word NN0 )' % pc)
            gams = {'0': ewg_(w, pc, 'U', cx['U e. NN0'], EWg('O', '(/)'), go), '1': ewg_(w, pc, 'Z', L_(zn0), '(/)', wrd0c), '2': ewg_(w, pc, 'I', tyl['I e. NN0'], '(/)', wrd0c),
                    '3': wrd0c, '4': enclg(w, pc, '( 1st ` R )', r1w, '(/)', wrd0c)}
            Vv = '(/)'
            NZv = NZ
        else:
            ifs = {IF0: (EWg('X', EWg('O', '(/)')), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, IF0, EWg('X', EWg('O', '(/)'))))),
                   IF1: (EWg('Z', EWg('X', '(/)')), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, IF1, EWg('Z', EWg('X', '(/)'))))),
                   IF2: (EWg('1', '(/)'), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, IF2, EWg('1', '(/)')))),
                   IF3: (EWg('L', '(/)'), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, IF3, EWg('L', '(/)')))),
                   IF4: (ENCL('Q', '(/)'), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, IF4, ENCL('Q', '(/)'))))}
            fc = s([cst], 'iffalsed', '( %s -> %s = ( ( ( 2nd ` R ) + ( 2 x. U ) ) + 2 ) )' % (pc, IFC))
            vals = {'0': EWg('X', EWg('O', '(/)')), '1': EWg('Z', EWg('X', '(/)')), '2': EWg('1', '(/)'), '3': EWg('L', '(/)'), '4': ENCL('Q', '(/)')}
            gx0 = ewg_(w, pc, 'X', tyl['X e. NN0'], '(/)', wrd0c)
            gams = {'0': ewg_(w, pc, 'X', tyl['X e. NN0'], EWg('O', '(/)'), go), '1': ewg_(w, pc, 'Z', L_(zn0), EWg('X', '(/)'), gx0),
                    '2': ewg_(w, pc, '1', closed(w, pc, '1nn0', '1 e. NN0'), '(/)', wrd0c), '3': ewg_(w, pc, 'L', tyl['L e. NN0'], '(/)', wrd0c),
                    '4': enclg(w, pc, 'Q', tyl['Q e. Word NN0'], '(/)', wrd0c)}
            Vv = '1o'
            NZv = '( ( %s + ( ; 5 0 x. %s ) ) + ( ( ( ( ( 2nd ` R ) + ( 2 x. U ) ) + 2 ) + 1 ) x. %s ) )' % (CIN, CSC_, CST_)
        rd, Dc_ = w.rewrite(Dz, ifs, pc)
        Sc = S7
        for k in ('0', '1', '2', '3', '4'):
            Sc = Sc.upd(k, vals[k], gams[k])
        assert Dc_ == Sc.D, '\n%s\n%s' % (Dc_, Sc.D)
        rn, nc_ = w.rewrite(NZ0, {IFC: ('( ( 2nd ` R ) + 1 )' if fail else '( ( ( 2nd ` R ) + ( 2 x. U ) ) + 2 )', fc)}, pc)
        assert nc_ == NZv, '\n%s\n%s' % (nc_, NZv)
        tc, Cc, Dc, nc = hrrw(w, pc, L_(t0), C0, D0, n0, deq=clneq(w, pc, Z1, NFL(VZ), rd, Dz, Sc.D), neq=rn)
        tc, Cc, Dc, nc = cls_to(w, pc, (tc, Cc, Dc, nc), VZ, Vv, s([cst], 'iftrued' if fail else 'iffalsed', '( %s -> %s = %s )' % (pc, VZ, Vv)))
        assert Dc == CLN(Z1, NFL(Vv), Sc.D), Dc
        v7 = s([Sc.vals['7'][1], s([L_(e7w)], 'eqcomd', '( %s -> %s = %s )' % (pc, W7, YN))], 'eqtrd', '( %s -> ( %s ` 7 ) = %s )' % (pc, Sc.D, YN))
        stk = {STKD(Sc.D): Sc.memb}
        for k in N8:
            stk['( %s ` %s ) = %s' % (Sc.D, k, Sc.vals[k][0])] = Sc.vals[k][1]
        stk['( %s ` 7 ) = %s' % (Sc.D, YN)] = v7
        if fail:
            t2, C2, D2, n2 = instp(w, pc, 'tmisrfl', {'A': Z1, 'X': Y4, 'Q': PL('P', 14), 'D': Sc.D, 'E': 'E'}, cx, leaf_dict(base_leaves, stk))
            assert C2 == Dc, (C2, Dc)
            rules = {'( %s ` %s )' % (Sc.D, k): ((YN if k == '7' else Sc.vals[k][0]), (v7 if k == '7' else Sc.vals[k][1])) for k in N8}
            t2, n2 = rewrite_cost(w, pc, t2, C2, D2, n2, rules)
            assert n2 == '( %s + 1 )' % FALC8(VALSZ), '\n%s\n%s' % (n2, '( %s + 1 )' % FALC8(VALSZ))
            svt_ = s([L_(svt), s([cst], 'iftrued', '( %s -> %s = <. %s , ( ( 2nd ` R ) + 1 ) >. )' % (pc, SV_RHS, INR))], 'eqtrd', '( %s -> %s = <. %s , ( ( 2nd ` R ) + 1 ) >. )' % (pc, SE, INR))
            ie = out_init13(w, pc, svt_, (INR, s([], 'eqidd', '( %s -> %s = %s )' % (pc, INR, INR))), CZ, COMMA1, None, False)
            t2, _, D2b, _ = hrrw(w, pc, t2, C2, D2, n2, deq=clneq(w, pc, 'E', S, ie, INIT('1', COMMA1), INIT('1', OUTS)))
            assert D2b == POST
            t = hrseq(w, pc, L_(phm), tc, t2, Cc, Dc, POST, nc, n2)
            n = '( %s + %s )' % (nc, n2)
            assert n == NZF, '\n%s\n%s' % (n, NZF)
            bnd, _ = inst(w, pc, 't13srcbzf', {}, Bld(w, pc, cx, base_leaves))
            le = s([bnd], 'simpld', '( %s -> %s <_ %s )' % (pc, NZF, TZ2))
            mem = s([bnd], 'simprd', '( %s -> %s e. NN0 )' % (pc, TZ2))
            t = hrle(w, pc, L_(phm), t, Cc, POST, n, TZ2, mem, le)
            cst2 = cst_of(w, pc, svt_, INR, CZ)
            te = s([s([cst2], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( %s + 1 ) )' % (pc, SE, CZ))], 'oveq1d', '( %s -> %s = %s )' % (pc, TOT, TZ2))
            t, _, _, nf = hrrw(w, pc, t, Cc, POST, TZ2, neq=s([te], 'eqcomd', '( %s -> %s = %s )' % (pc, TZ2, TOT)))
            assert nf == TOT
        else:
            ui = s([cst, s([clc.mem('U', 'RR'), clc.mem('I', 'RR'), w.inst('lenlt')], 'syl2anc', '( %s -> ( U <_ I <-> -. I < U ) )' % pc)], 'mpbird', '( %s -> U <_ I )' % pc)
            q = instc(w, pc, 't13srcq', {}, cx, leaf_dict(ul, {'U <_ I': ui}), C_Q)
            # the bit bounds at b1 and the encoded window
            p2leaf(w, pc, clc, 'B'); p2leaf(w, pc, clc, 'H'); p2leaf(w, pc, clc, "B'")
            nb1 = lt2m(w, pc, clc, 'N', clc.mem('N', 'RR'), 'H', "B'", ul["H <_ B'"], cx[LT2('N', 'H')])
            zb1 = lt2m(w, pc, clc, 'Z', clc.mem('Z', 'RR') if False else s([L_(zn0)], 'nn0red', '( %s -> Z e. RR )' % pc), 'B', "B'", ul["B <_ B'"], cx[LT2('Z')])
            ob1 = lt2m(w, pc, clc, 'O', clc.mem('O', 'RR') if False else s([cx['O e. NN0']], 'nn0red', '( %s -> O e. RR )' % pc), 'H', "B'", ul["H <_ B'"], cx[LT2('O', 'H')])
            l2 = instc(w, pc, 't13srcl2', {}, cx, leaf_dict(ul, tyl, {'L < ( 2 ^ %s )' % UB1: q['L < ( 2 ^ %s )' % UB1]}), C_L2)
            hb3 = wff_rewrite(w, pc, ul[HB3U], HB3U, 'U', '( # ` Q )', s([q['( # ` Q ) = U']], 'eqcomd', '( %s -> U = ( # ` Q ) )' % pc))
            assert hb3 is not None
            # ( # encList Q ) + 1 <_ ( C' + 1 ) U'
            clc.leaf('( # ` ( encList ` Q ) )', 'NN0', s([s([tyl['Q e. Word NN0'], w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` Q ) e. Word Gamma' )" % pc), w.inst('lencl')], 'syl',
                                                          '( %s -> ( # ` ( encList ` Q ) ) e. NN0 )' % pc))
            uc = linarith(w, pc, [cx[EQ("C'")], q['( 2nd ` ( ProdL ` Q ) ) = U'], clc.ge0('( 2nd ` R )'), clc.ge0('U')], "U <_ ( C' + 1 )", closure=clc)
            m1 = lemul1a(w, pc, clc, 'U', "( C' + 1 )", '( B + 1 )', uc)
            m2 = P.mul_le2(w, pc, clc, "( C' + 1 )", '( B + 2 )', "U'", ul["( B + 2 ) <_ U'"])
            c1 = linarith(w, pc, [cx[EQ("C'")], q['( 2nd ` ( ProdL ` Q ) ) = U'], clc.ge0('( 2nd ` R )'), clc.ge0('U')], "1 <_ C'", closure=clc)
            lqc = linarith(w, pc, [q['( # ` ( encList ` Q ) ) <_ ( ( U x. ( B + 1 ) ) + 1 )'], m1, m2, c1, clc.ge0('B')], "( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )", closure=clc, products=True)
            # the cost so far
            Z2v = NZv
            cst_m = P.mul_le2(w, pc, clc, '( ( ( ( 2nd ` R ) + ( 2 x. U ) ) + 2 ) + 1 )', CST_, "U'", ul["%s <_ U'" % CST_])
            z2n = clc.mem(Z2v, 'NN0')
            CTX = '( ( ( 2nd ` R ) + ( 2 x. U ) ) + 2 )'
            ceq = lineq(w, pc, "C'", CTX, hyps=[cx[EQ("C'")], q['( 2nd ` ( ProdL ` Q ) ) = U']], closure=clc)
            peq = s([s([ceq], 'oveq1d', "( %s -> ( C' + 1 ) = ( %s + 1 ) )" % (pc, CTX))], 'oveq1d', "( %s -> ( ( C' + 1 ) x. U' ) = ( ( %s + 1 ) x. U' ) )" % (pc, CTX))
            z2le = linarith(w, pc, [L_(cin), ul["%s <_ U'" % CSC_], cst_m, peq], '%s <_ %s' % (Z2v, PRE2), closure=clc, products=True)
            # tmisrc2 has ` $d D k ` : rename the bound variable of the initial stacks to j (~ cbvmptv )
            INIT7J = ' '.join('j' if tk == 'k' else tk for tk in INIT7.split())
            IFK = 'if ( k = 7 , %s , (/) )' % W7
            IFJ = 'if ( j = 7 , %s , (/) )' % W7
            cb = s([s([s([], 'eqeq1', '( k = j -> ( k = 7 <-> j = 7 ) )')], 'ifbid', '( k = j -> %s = %s )' % (IFK, IFJ))], 'cbvmptv', '%s = %s' % (INIT7, INIT7J))
            cba = s([cb], 'a1i', '( %s -> %s = %s )' % (pc, INIT7, INIT7J))
            rdj, Dj = w.rewrite(Sc.D, {INIT7: (INIT7J, cba)}, pc)
            tc, Cc, Dc, nc = hrrw(w, pc, tc, Cc, Dc, nc, deq=clneq(w, pc, Z1, NFL(Vv), rdj, Sc.D, Dj))
            stk = {STKD(Dj): s([rdj, Sc.memb], 'eqeltrrd', '( %s -> %s e. ( TM2Stk ` T ) )' % (pc, Dj))}
            for k in N8:
                vk = YN if k == '7' else Sc.vals[k][0]
                vs = v7 if k == '7' else Sc.vals[k][1]
                stk['( %s ` %s ) = %s' % (Dj, k, vk)] = s([s([rdj], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (pc, Sc.D, k, Dj, k)), vs], 'eqtr3d',
                                                           '( %s -> ( %s ` %s ) = %s )' % (pc, Dj, k, vk))
            ex2 = dict(base_leaves)
            ex2.update(stk)
            ex2.update({'U <_ I': ui, LT2('N', "B'"): nb1, LT2('Z', "B'"): zb1, LT2('O', "B'"): ob1, C_L2: l2[C_L2], HB3: hb3,
                        "( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )": lqc, '%s e. NN0' % Z2v: z2n, '%s <_ %s' % (Z2v, PRE2): z2le,
                        'Z e. NN0': L_(zn0)})
            ex2.update(q)
            t2, C2, D2, n2 = instp(w, pc, 'tmisrc2', {'D': Dj, "Z'": Z2v}, cx, ex2)
            assert C2 == Dc and D2 == POST, '\n%s\n%s' % (C2, Dc)
            t = hrseq(w, pc, L_(phm), tc, t2, Cc, Dc, POST, nc, n2)
            n = '( %s + %s )' % (nc, n2)
            svs = s([L_(svt), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, SV_RHS, RHS2))], 'eqtrd', '( %s -> %s = %s )' % (pc, SE, RHS2))
            # ( 2nd SE ) e. NN0 through the nested ifs
            def cl_of(pc2):
                Lx = (lambda st_: lift_from(w, pc, pc2, st_)) if pc2 != pc else (lambda st_: st_)
                cl2 = Closure(w, pc2, {})
                for x_ in ("C'", S2, '( 2nd ` R )'):
                    cl2.leaf(x_, 'NN0', Lx(clc.mem(x_, 'NN0')))
                if pc2 != pc:
                    # inside the scan's some case: the extraction's typing (~ t13srcsm ) gives E2 ; deeper, the verdict's cost
                    inner = pc2[len('( %s /\\ ' % pc):-2]
                    conds = []
                    tcur = pc2
                    while tcur != pc:
                        head = tcur[2:-2]
                        toks = head.split(' ')
                        d = 0; kk = None
                        for jj, tk in enumerate(toks):
                            if tk in ('(', '<.', '{'):
                                d += 1
                            elif tk in (')', '>.', '}'):
                                d -= 1
                            elif tk == '/\\' and d == 0:
                                kk = jj
                        conds.append(' '.join(toks[kk + 1:]))
                        tcur = ' '.join(toks[:kk])
                    conds = conds[::-1]
                    # conds[0] is about ( 1st J ) = inr ; the some case is its negation
                    if conds[0].startswith('-.'):
                        Tc2 = Tc
                        for cnd in conds:
                            Tc2 = (Tc2, cnd)
                        cx2 = CtxX(w, pc2, Tc2)
                        jne2 = s([cx2[conds[0]]], 'neqned', "( %s -> ( 1st ` J ) =/= %s )" % (pc2, INR))
                        sm2 = instc(w, pc2, 't13srcsm', {}, cx2, {"( 1st ` J ) =/= %s" % INR: jne2, '1 <_ L': Lx(q['1 <_ L'])}, C_SM)
                        cl2.leaf(E2, 'NN0', sm2['%s e. NN0' % E2])
                        if len(conds) == 2 and conds[1].startswith('-.'):
                            ne_ = s([cx2[conds[1]]], 'neqned', "( %s -> ( 1st ` X' ) =/= %s )" % (pc2, INR))
                            xx = instc(w, pc2, 't13srcx', {}, cx2, {'L e. NN': sm2['L e. NN'], 'W e. Word NN0': sm2['W e. Word NN0'], "( 1st ` X' ) =/= %s" % INR: ne_}, C_X)
                            wf2 = instc(w, pc2, 't13srcw', {}, cx2, {"( 1st ` J ) =/= %s" % INR: jne2, '( # ` Q ) = U': Lx(q['( # ` Q ) = U']), '1 <_ L': Lx(q['1 <_ L']),
                                                                    LT2('X', "B'"): Lx(q[LT2('X', "B'")]), "( 1 + X ) < ( 2 ^ B' )": Lx(q["( 1 + X ) < ( 2 ^ B' )"]),
                                                                    "B' e. NN0": Lx(ul["B' e. NN0"])}, C_W)
                            xb = instc(w, pc2, 't13srcxb', {"N'": NP}, cx2, {'L e. NN': sm2['L e. NN'], 'W e. Word NN0': sm2['W e. Word NN0'], RALB('W', "B'"): wf2[RALB('W', "B'")],
                                                                              'A. a e. ran W 2 <_ a': wf2['A. a e. ran W 2 <_ a'], '( # ` W ) <_ ( 2 ^ U )': wf2['( # ` W ) <_ ( 2 ^ U )'],
                                                                              '%s = %s' % (NP, NP): s([s([], 'eqid', '%s = %s' % (NP, NP))], 'a1i', '( %s -> %s = %s )' % (pc2, NP, NP)),
                                                                              "U < B'": Lx(ul["U < B'"]), "B' e. NN0": Lx(ul["B' e. NN0"])}, C_XB)
                            fn_ = s([xx['F = %s' % MR], xb['%s e. NN0' % MR]], 'eqeltrd', '( %s -> F e. NN0 )' % pc2)
                            an_ = s([xx['A = %s' % USED], xb['%s e. Word NN0' % USED]], 'eqeltrd', '( %s -> A e. Word NN0 )' % pc2)
                            vcl2 = s([cx2[EQ("Q'")], s([fn_, an_, w.inst('verifycl')], 'syl2anc', '( %s -> ( F Verify A ) e. ( 2o X. NN0 ) )' % pc2)], 'eqeltrd', "( %s -> Q' e. ( 2o X. NN0 ) )" % pc2)
                            cl2.leaf(W2, 'NN0', s([vcl2, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` Q' ) e. NN0 )" % pc2))
                return cl2
            sen = second_nn0(w, pc, cl_of, svs, RHS2)
            clc.leaf('( 2nd ` %s )' % SE, 'NN0', sen)
            clc.leaf(TOT, 'NN0', clc.mem(TOT, 'NN0'))
            clc.leaf(Z2v, 'NN0', z2n)
            ceq = lineq(w, pc, n, TOT, closure=clc)
            t, _, _, nf = hrrw(w, pc, t, Cc, POST, n, neq=ceq)
            assert nf == TOT
        outs.append(s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, CONCL_SRCZ)))
    st = s([outs[0], outs[1]], 'pm2.61d', '( %s -> %s )' % (ph, CONCL_SRCZ))
    qed13(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
