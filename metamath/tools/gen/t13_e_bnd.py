"""T13: the bound helpers of the searchF assembly (no machine): the cost of a stage's leaf against ` TOT - Z' ` , with
Lean's ` bud_A .. bud_D ` (~ t12bud ), the word lengths of the eight stacks (~ tm2lentlt , ~ ccatlen ) and the unit facts.

  t13srcb4o  the output leaf: ` 1 + verify cost + 1 + output cost <_ TOT - Z' `           (Lean 2378-2395, bud_D)
  t13srcb4f  the verify-rejects leaf: ` 1 + verify cost + failAll cost + 1 <_ TOT - Z' `  (Lean 2366-2372)
  t13srcb3f  the extract-fails leaf: ` 1 + extract cost + failAll cost + 1 <_ TOT - Z' `  (Lean 2275-2293, bud_C)
  t13srcb2f  the scan-fails leaf: ` 1 + scan cost + failAll cost + 1 <_ TOT - Z' `        (Lean 2397-2417, bud_B)
  t13srcbzf  the step-2-fails leaf: ` cin + csc + cst + failAll cost + 1 <_ TOT `         (Lean 2096-2125, bud_A)

Each conclusion also gives ` ( TOT - Z' ) e. NN0 ` (for ~ tm2hle ).  The costs are the run lemmas' costs with the stack
values written out (the assemblies rewrite ` ( # ( D ` k ) ) ` to them first).

    MM_DB=sorties/t13.mm python3 tools/gen/t13_e_bnd.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t13lib import *
from t13_b_help import pow2le, pow2lt, p2leaf, tmbleaf, tmbmono, lemul1a
from t13_c_u0 import CSC_, CST_
from t10_n_rgf import tmbn
from lin import linarith, lineq
from cl import Closure

SEL = sys.argv[1:]
S2, E2, W2, CST4, VX4, HB5 = P.S2, P.E2, P.W2, P.CST4, P.VX4, P.HB5
D0V, D1V, D2V, D3V, D4V, D7V = P.D0V, P.D1V, P.D2V, P.D3V, P.D4V, P.D7V
UN1, UN2, UN3, UN4, UN5, WD4, VF2, CSTH4 = P.UN1, P.UN2, P.UN3, P.UN4, P.UN5, P.WD4, P.VF2, P.CSTH4
UN4W, UN5W, CSTH3, PRE2, PRE3, PRE4 = P.UN4W, P.UN5W, P.CSTH3, P.PRE2, P.PRE3, P.PRE4
UN2S, UN3S, UP3, CSTH2, HB3 = P.UN2S, P.UN3S, P.UP3, P.CSTH2, P.HB3
MR, USED, ACCW3, D6V3, EXY = P.MR, P.USED, P.ACCW3, P.D6V3, P.EXY
BUDL, BUDR = P.BUDL, P.BUDR
T46 = '( TMB ` ( ( 4 x. %s ) + 6 ) )' % VX4
VERC = '( ( %s + 1 ) x. %s )' % (W2, T46)
XQ = ENCL('Q', '(/)')
YN = EWg('N', '(/)')
LB = "( ( ( C' + 1 ) x. U' ) + ( ; 5 0 x. W' ) )"
TBS = "( TMB ` ( ( ( ( ; 4 8 x. ( ( # ` Q ) + 1 ) ) x. ( B' + B' ) ) + ( 4 x. ( # ` Q ) ) ) + ; ; 1 0 2 ) )"
CSN = '( ( %s + 1 ) x. %s )' % (S2, TBS)
CEX = '( ( %s + 1 ) x. ( ; 2 5 x. %s ) )' % (E2, EXY)


def FALC8(vals):
    return lsum(*([LEN(vals[k]) for k in N8] + ['9']))


def OUTC(vals):
    """tmiout's cost with the stack values (W := A , B := B' , N := N' , X := XQ , Y := YN)"""
    return lsum(LEN(vals['0']), LEN(vals['1']), LEN(vals['2']), LEN(vals['3']), LEN(vals['5']), LEN(vals['6']), '6',
                "( ( ( # ` A ) + 1 ) x. ( TMB ` B' ) )", "( ( ( # ` A ) x. ( ( 2 x. B' ) + 6 ) ) + 3 )", "( TMB ` N' )",
                '( ( # ` %s ) + 1 )' % YN, '( ( # ` %s ) + 1 )' % XQ)


def TOT2_(cst):
    return "( ( %s + 1 ) x. ( ; ; 3 0 0 x. W' ) )" % cst


def BND(n, cst, zp="Z'"):
    T2 = TOT2_(cst)
    return '( %s <_ ( %s - %s ) /\\ ( %s - %s ) e. NN0 )' % (n, T2, zp, T2, zp)


# ------------------------------------------------------------ statements
VALS4 = {'0': D0V, '1': D1V, '2': D2V, '3': D3V, '4': D4V, '5': "Y'", '6': 'X"', '7': D7V}
TYPE4 = ((('Z e. NN', 'O e. NN0', 'N e. NN0'), ("C' e. NN0", '%s e. NN0' % S2, '%s e. NN0' % E2)),
         (('%s e. NN0' % W2, 'X e. NN0', 'L e. NN0'), ("J' e. NN0", 'F e. NN0', 'A e. Word NN0'), ('Q e. Word NN0', ("B' e. NN0", "N' e. NN0"), ('B e. NN0', 'H e. NN0'))))
T_B4 = ((TYPE4, (UN1, UN2, UN3)), ((UN4, UN5, WD4), (VF2, CSTH4)))
N4O = '( ( 1 + %s ) + ( 1 + %s ) )' % (VERC, OUTC(VALS4))
N4F = '( ( 1 + %s ) + ( %s + 1 ) )' % (VERC, FALC8(VALS4))
add13('t13srcb4o', T_B4, BND(N4O, CST4))
add13('t13srcb4f', T_B4, BND(N4F, CST4))

VALS3 = {'0': D0V, '1': D1V, '2': D2V, '3': D3V, '4': ENCL(USED, XQ), '5': ACCW3, '6': D6V3, '7': EWg(MR, YN)}
TYPE3 = ((('Z e. NN', 'O e. NN0', 'N e. NN0'), ("C' e. NN0", '%s e. NN0' % S2, '%s e. NN0' % E2)),
         (('X e. NN0', 'L e. NN0', "J' e. NN0"), ('Q e. Word NN0', 'W e. Word NN0'), (("B' e. NN0", "N' e. NN0"), ('B e. NN0', 'H e. NN0'))))
XF3 = (('%s e. NN0' % MR, '%s e. Word NN0' % USED, "%s < ( 2 ^ N' )" % MR), ("( # ` ( encList ` %s ) ) <_ W'" % USED, "( # ` %s ) <_ W'" % ACCW3, "( # ` %s ) <_ W'" % D6V3),
       (WG(ACCW3), WG(D6V3)))
T_B3 = ((TYPE3, (UN1, UN2, UN3)), ((UN4W, UN5W), (XF3, CSTH3)))
CST3 = "( ( C' + %s ) + %s )" % (S2, E2)
N3F = '( ( 1 + %s ) + ( %s + 1 ) )' % (CEX, FALC8(VALS3))
add13('t13srcb3f', T_B3, BND(N3F, CST3))

VALS2 = {'0': D0V, '1': EWg('Z', '(/)'), '2': EWg('( 1 + X )', '(/)'), '3': D3V, '4': XQ, '5': '(/)', '6': '(/)', '7': YN}
TYPE2 = ((('Z e. NN', 'O e. NN0', 'N e. NN0'), ("C' e. NN0", '%s e. NN0' % S2, 'X e. NN0')), (('L e. NN0', 'Q e. Word NN0', "B' e. NN0"), ('B e. NN0', 'H e. NN0')))
T_B2 = ((TYPE2, (UN1, UN2S, UN3S)), (UP3, CSTH2))
CST2 = "( C' + %s )" % S2
N2F = '( ( 1 + %s ) + ( %s + 1 ) )' % (CSN, FALC8(VALS2))
add13('t13srcb2f', T_B2, BND(N2F, CST2))

R1 = '( 1st ` R )'
VALSZ = {'0': EWg('U', EWg('O', '(/)')), '1': EWg('Z', '(/)'), '2': EWg('I', '(/)'), '3': '(/)', '4': ENCL(R1, '(/)'), '5': '(/)', '6': '(/)', '7': YN}
CIN = '( ( 2 x. ( # ` ( encodeNat ` N ) ) ) + 4 )'
CZ = '( ( 2nd ` R ) + 1 )'
NZ = '( ( %s + ( ; 5 0 x. %s ) ) + ( ( %s + 1 ) x. %s ) )' % (CIN, CSC_, CZ, CST_)
NZF = '( %s + ( %s + 1 ) )' % (NZ, FALC8(VALSZ))
T_BZ = ((P.SC_TY, (P.EQ('R'), P.EQ('I'))), ((('B e. NN0', 'H e. NN0'), ("U' e. NN0", "W' e. NN0"), ("U' <_ W'", "8 <_ U'")),
                                              ((LT2('Z'), LT2('U')), (LT2('O', 'H'), LT2('N', 'H'))),
                                              (("( ( 2 x. H ) + 4 ) <_ U'", "%s <_ U'" % CSC_), ("%s <_ U'" % CST_, "( B + 2 ) <_ U'"))))
TZ2 = TOT2_(CZ)
add13('t13srcbzf', T_BZ, '( %s <_ %s /\\ %s e. NN0 )' % (NZF, TZ2, TZ2))


# ------------------------------------------------------------ shared pieces
def stack_lengths(w, ph, cl, vals, atoms):
    """the length equations of the eight stack values (their atoms registered in cl); returns the steps"""
    lf = []
    for k in N8:
        P.lenfacts(w, ph, cl, vals[k], atoms, lf)
    return lf


def bud(w, ph, c, cl, C_, S_, E_, W_, cn, sn, en, wn):
    """~ t12bud at ( U' , W' , C_ , S_ , E_ , W_ )"""
    s = w.s
    j = s([s([s([c["U' e. NN0"], c["W' e. NN0"]], 'jca', "( %s -> ( U' e. NN0 /\\ W' e. NN0 ) )" % ph),
              s([c["U' <_ W'"], c["8 <_ U'"]], 'jca', "( %s -> ( U' <_ W' /\\ 8 <_ U' ) )" % ph)], 'jca',
             "( %s -> ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) )" % ph),
           s([s([cn, sn], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, C_, S_)), s([en, wn], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, E_, W_))], 'jca',
             '( %s -> ( ( %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) )' % (ph, C_, S_, E_, W_))], 'jca',
          "( %s -> ( ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) /\\ ( ( %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) ) )" % (ph, C_, S_, E_, W_))
    return s([j, w.inst('t12bud')], 'syl', '( %s -> %s )' % (ph, tsub_text('%s <_ %s' % (BUDL, BUDR), {'U': "U'", 'V': "W'", 'C': C_, 'S': S_, 'E': E_, 'W': W_})))


def zero_leaf(w, ph, cl):
    cl.leaf('0', 'NN0', closed(w, ph, '0nn0', '0 e. NN0')) if False else None


def finish_bound(w, ph, cl, lab, n, cst, hy, zp="Z'"):
    """( n <_ ( TOT2 - Z' ) /\\ ( TOT2 - Z' ) e. NN0 ) from hy (the budget, the leaf bound, the callee's bound, Z' <_ PRE)"""
    s = w.s
    T2 = TOT2_(cst)
    B2 = '( %s - %s )' % (T2, zp)
    le = linarith(w, ph, hy, '%s <_ %s' % (n, B2), closure=cl, products=True)
    zle = linarith(w, ph, hy, '%s <_ %s' % (zp, T2), closure=cl, products=True)
    bn2 = s([zle, s([cl.mem(zp, 'NN0'), cl.mem(T2, 'NN0'), w.inst('nn0sub')], 'syl2anc', '( %s -> ( %s <_ %s <-> %s e. NN0 ) )' % (ph, zp, T2, B2))], 'mpbid',
             '( %s -> %s e. NN0 )' % (ph, B2))
    st = s([le, bn2], 'jca', '( %s -> %s )' % (ph, BND(n, cst, zp)))
    qed13(w, st, lab)


def common_cl(w, ph, c, letters):
    cl = Closure(w, ph, {x: ('NN0', c['%s e. NN0' % x]) for x in letters})
    cl.leaf('Z', 'NN0', w.s([c['Z e. NN']], 'nnnn0d', '( %s -> Z e. NN0 )' % ph))
    return cl


def atoms4(w, ph, c, cl, ty_x, ty_l, ty_j, ty_f):
    """the number atoms of the stage-4/3 stacks"""
    atoms = {}
    for t_, tn_, b_, bn_, tlt_ in (('X', ty_x, "B'", c["B' e. NN0"], c[LT2('X', "B'")]), ('O', c['O e. NN0'], 'H', c['H e. NN0'], c[LT2('O', 'H')]),
                                   ('Z', cl.mem('Z', 'NN0'), 'B', c['B e. NN0'], c[LT2('Z')]), ("J'", ty_j, "B'", c["B' e. NN0"], c[LT2("J'", "B'")]),
                                   ('L', ty_l, "B'", c["B' e. NN0"], c[LT2('L', "B'")]), ('N', c['N e. NN0'], 'H', c['H e. NN0'], c[LT2('N', 'H')])):
        atoms['( encNatGam ` %s )' % t_] = P.numatom(w, ph, cl, t_, tn_, b_, bn_, tlt_)
    if ty_f is not None:
        atoms['( encNatGam ` F )'] = P.numatom(w, ph, cl, 'F', ty_f, "N'", c["N' e. NN0"], c[LT2('F', "N'")])
    return atoms


# ------------------------------------------------------------ t13srcb4o / t13srcb4f
def b4(lab, out):
    T = T_B4
    ph = cj(T)
    w = W(lab, ('The output leaf\'s budget (Lean 2378-2395): the verify cost is at most ` ( w + 1 ) U ` , the output cost at most '
                '` ( c + 1 ) U + 50 V ` from the stack lengths (~ tm2lentlt , ~ tm2lenclen ), and ~ t12bud (` bud_D ` ) closes.' if out else
                'The verify-rejects leaf\'s budget (Lean 2366-2372): the verify cost is at most ` ( w + 1 ) U ` , the ` failAll ` cost '
                'at most ` ( c + 1 ) U + 50 V ` from the stack lengths, and ~ t12bud (` bud_D ` ) closes.'))
    s = w.s
    c = Ctx(w, ph, T)
    cl = common_cl(w, ph, c, ('O', 'N', "C'", 'X', 'L', "J'", 'F', "B'", "N'", 'B', 'H', "Z'", "U'", "W'"))
    for x in (S2, E2, W2):
        cl.leaf(x, 'NN0', c['%s e. NN0' % x])
    an, qw = c['A e. Word NN0'], c['Q e. Word NN0']
    cl.leaf('( # ` A )', 'NN0', s([an, w.inst('lencl')], 'syl', '( %s -> ( # ` A ) e. NN0 )' % ph))
    tmbleaf(w, ph, cl, '( ( 4 x. %s ) + 6 )' % VX4)
    cvle = P.mul_le2(w, ph, cl, '( %s + 1 )' % W2, T46, "U'", c[HB5])
    atoms = atoms4(w, ph, c, cl, c['X e. NN0'], c['L e. NN0'], c["J' e. NN0"], c['F e. NN0'])
    atoms['( encList ` Q )'] = (s([qw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` Q ) e. Word Gamma' )" % ph), None)
    atoms['( encList ` A )'] = (s([an, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` A ) e. Word Gamma' )" % ph), None)
    atoms["Y'"] = (c[WG("Y'")], None)
    atoms['X"'] = (c[WG('X"')], None)
    lf = stack_lengths(w, ph, cl, VALS4, atoms)
    lin_hy = [c["U' <_ W'"], c["8 <_ U'"], c["( B' + 2 ) <_ U'"], c["( N' + 2 ) <_ U'"], c["B <_ B'"], c["H <_ B'"], c["( # ` Y' ) <_ W'"], c['( # ` X" ) <_ W\''],
              c["( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )"], c["( # ` ( encList ` A ) ) <_ W'"]] + lf
    if out:
        tmbleaf(w, ph, cl, "B'"); tmbleaf(w, ph, cl, "N'")
        mA1 = P.mul_le2(w, ph, cl, '( ( # ` A ) + 1 )', "( TMB ` B' )", "U'", c["( TMB ` B' ) <_ U'"])
        mA2 = P.mul_le2(w, ph, cl, '( ( # ` A ) + 2 )', "( B' + 2 )", "U'", c["( B' + 2 ) <_ U'"])
        a12 = lemul1a(w, ph, cl, '( ( # ` A ) + 1 )', '( ( # ` A ) + 2 )', "U'", linarith(w, ph, [], '( ( # ` A ) + 1 ) <_ ( ( # ` A ) + 2 )', closure=cl))
        ho1 = linarith(w, ph, [mA1, a12, c["( ( ( # ` A ) + 2 ) x. U' ) <_ W'"]], "( ( ( # ` A ) + 1 ) x. ( TMB ` B' ) ) <_ W'", closure=cl)
        PB2 = "( ( ( # ` A ) + 2 ) x. ( B' + 2 ) )"
        poly = linarith(w, ph, [cl.ge0("( ( # ` A ) x. B' )"), cl.ge0("B'"), cl.ge0('( # ` A )')], "( ( ( # ` A ) x. ( ( 2 x. B' ) + 6 ) ) + 3 ) <_ ( 3 x. %s )" % PB2,
                        closure=cl, products=True)
        m3 = P.mul_le2(w, ph, cl, '3', PB2, "( ( ( # ` A ) + 2 ) x. U' )", mA2)
        ho2 = linarith(w, ph, [poly, m3, c["( ( ( # ` A ) + 2 ) x. U' ) <_ W'"]], "( ( ( # ` A ) x. ( ( 2 x. B' ) + 6 ) ) + 3 ) <_ ( 3 x. W' )", closure=cl)
        lin_hy += [ho1, ho2, c["( TMB ` N' ) <_ U'"]]
        nl = '( 1 + %s )' % OUTC(VALS4)
        n = N4O
    else:
        nl = '( %s + 1 )' % FALC8(VALS4)
        n = N4F
    leafle = linarith(w, ph, lin_hy, '%s <_ %s' % (nl, LB), closure=cl)
    bd = bud(w, ph, c, cl, "C'", S2, E2, W2, cl.mem("C'", 'NN0'), cl.mem(S2, 'NN0'), cl.mem(E2, 'NN0'), cl.mem(W2, 'NN0'))
    hy = [c["Z' <_ %s" % PRE4], cvle, leafle, bd, c["U' <_ W'"], c["8 <_ U'"]] + [cl.ge0(x) for x in ("C'", S2, E2, W2, "Z'", "U'", "W'")]
    finish_bound(w, ph, cl, lab, n, CST4, hy)
    return w.run()


def t13srcb4o():
    return b4('t13srcb4o', True)


def t13srcb4f():
    return b4('t13srcb4f', False)


# ------------------------------------------------------------ t13srcb3f
def t13srcb3f():
    lab = 't13srcb3f'
    T = T_B3
    ph = cj(T)
    w = W(lab, 'The extract-fails leaf\'s budget (Lean 2275-2293): the extraction cost is at most ` ( e + 1 ) 25 V ` , the '
               '` failAll ` cost at most ` ( c + 1 ) U + 50 V ` from the stack lengths (the table word and the pool at most ` V ` ), '
               'and ~ t12bud (` bud_C ` ) closes.')
    s = w.s
    c = Ctx(w, ph, T)
    cl = common_cl(w, ph, c, ('O', 'N', "C'", 'X', 'L', "J'", "B'", "N'", 'B', 'H', "Z'", "U'", "W'"))
    for x in (S2, E2, MR):
        cl.leaf(x, 'NN0', c['%s e. NN0' % x])
    qw, ww, uw = c['Q e. Word NN0'], c['W e. Word NN0'], c['%s e. Word NN0' % USED]
    cl.leaf('( # ` W )', 'NN0', s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph))
    tmbleaf(w, ph, cl, "( ( ( 3 x. ( # ` W ) ) x. B' ) + ( ( 5 x. B' ) + 5 ) )")
    cl.leaf(EXY, 'NN0', cl.mem(EXY, 'NN0'))
    cex25 = P.mul_le2(w, ph, cl, '( %s + 1 )' % E2, '( ; 2 5 x. %s )' % EXY, "( ; 2 5 x. W' )", linarith(w, ph, [c["%s <_ W'" % EXY]], "( ; 2 5 x. %s ) <_ ( ; 2 5 x. W' )" % EXY, closure=cl))
    atoms = atoms4(w, ph, c, cl, c['X e. NN0'], c['L e. NN0'], c["J' e. NN0"], None)
    atoms['( encNatGam ` %s )' % MR] = P.numatom(w, ph, cl, MR, cl.mem(MR, 'NN0'), "N'", c["N' e. NN0"], c["%s < ( 2 ^ N' )" % MR])
    atoms['( encList ` Q )'] = (s([qw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` Q ) e. Word Gamma' )" % ph), None)
    atoms['( encList ` %s )' % USED] = (s([uw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, USED)), None)
    atoms[ACCW3] = (c[WG(ACCW3)], None)
    atoms[D6V3] = (c[WG(D6V3)], None)
    lf = stack_lengths(w, ph, cl, VALS3, atoms)
    lin_hy = [c["U' <_ W'"], c["8 <_ U'"], c["( B' + 2 ) <_ U'"], c["( N' + 2 ) <_ U'"], c["B <_ B'"], c["H <_ B'"],
              c["( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )"], c["( # ` ( encList ` %s ) ) <_ W'" % USED], c["( # ` %s ) <_ W'" % ACCW3], c["( # ` %s ) <_ W'" % D6V3]] + lf
    nl = '( %s + 1 )' % FALC8(VALS3)
    leafle = linarith(w, ph, lin_hy, '%s <_ %s' % (nl, LB), closure=cl)
    zero = closed(w, ph, '0nn0', '0 e. NN0')
    bd = bud(w, ph, c, cl, "C'", S2, E2, '0', cl.mem("C'", 'NN0'), cl.mem(S2, 'NN0'), cl.mem(E2, 'NN0'), zero)
    hy = [c["Z' <_ %s" % PRE3], cex25, leafle, bd, c["U' <_ W'"], c["8 <_ U'"]] + [cl.ge0(x) for x in ("C'", S2, E2, "Z'", "U'", "W'")]
    finish_bound(w, ph, cl, lab, N3F, CST3, hy)
    return w.run()


# ------------------------------------------------------------ t13srcb2f
def t13srcb2f():
    lab = 't13srcb2f'
    T = T_B2
    ph = cj(T)
    w = W(lab, 'The scan-fails leaf\'s budget (Lean 2397-2417): the scan cost is at most ` ( s + 1 ) U ` (~ tmbmono ), the '
               '` failAll ` cost at most ` ( c + 1 ) U + 50 V ` from the stack lengths, and ~ t12bud (` bud_B ` ) closes.')
    s = w.s
    c = Ctx(w, ph, T)
    cl = common_cl(w, ph, c, ('O', 'N', "C'", 'X', 'L', "B'", 'B', 'H', "Z'", "U'", "W'"))
    cl.leaf(S2, 'NN0', c['%s e. NN0' % S2])
    qw = c['Q e. Word NN0']
    cl.leaf('( # ` Q )', 'NN0', s([qw, w.inst('lencl')], 'syl', '( %s -> ( # ` Q ) e. NN0 )' % ph))
    tmbleaf(w, ph, cl, TBS[len('( TMB ` '):-2])
    csnle = P.mul_le2(w, ph, cl, '( %s + 1 )' % S2, TBS, "U'", c[HB3])
    atoms = {}
    for t_, tn_, b_, bn_, tlt_ in (('X', c['X e. NN0'], "B'", c["B' e. NN0"], c[LT2('X', "B'")]), ('O', c['O e. NN0'], 'H', c['H e. NN0'], c[LT2('O', 'H')]),
                                   ('Z', cl.mem('Z', 'NN0'), 'B', c['B e. NN0'], c[LT2('Z')]), ('( 1 + X )', cl.mem('( 1 + X )', 'NN0'), "B'", c["B' e. NN0"], c["( 1 + X ) < ( 2 ^ B' )"]),
                                   ('L', c['L e. NN0'], "B'", c["B' e. NN0"], c[LT2('L', "B'")]), ('N', c['N e. NN0'], 'H', c['H e. NN0'], c[LT2('N', 'H')])):
        atoms['( encNatGam ` %s )' % t_] = P.numatom(w, ph, cl, t_, tn_, b_, bn_, tlt_)
    atoms['( encList ` Q )'] = (s([qw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` Q ) e. Word Gamma' )" % ph), None)
    lf = stack_lengths(w, ph, cl, VALS2, atoms)
    nl = '( %s + 1 )' % FALC8(VALS2)
    leafle = linarith(w, ph, lf + [c["( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )"], c["U' <_ W'"], c["8 <_ U'"], c["( B' + 2 ) <_ U'"], c["B <_ B'"], c["H <_ B'"]],
                     '%s <_ %s' % (nl, LB), closure=cl)
    zero = closed(w, ph, '0nn0', '0 e. NN0')
    bd = bud(w, ph, c, cl, "C'", S2, '0', '0', cl.mem("C'", 'NN0'), cl.mem(S2, 'NN0'), zero, zero)
    hy = [c["Z' <_ %s" % PRE2], csnle, leafle, bd, c["U' <_ W'"], c["8 <_ U'"]] + [cl.ge0(x) for x in ("C'", S2, "Z'", "U'", "W'")]
    finish_bound(w, ph, cl, lab, N2F, CST2, hy)
    return w.run()


# ------------------------------------------------------------ t13srcbzf
def t13srcbzf():
    lab = 't13srcbzf'
    T = T_BZ
    ph = cj(T)
    w = W(lab, 'The step-2-fails leaf\'s budget (Lean 2096-2125): ` cin <_ U ` , ` csc <_ 50 U ` , ` cst <_ ( c + 1 ) U ` with '
               '` c = rc + 1 ` , the ` failAll ` cost at most ` ( c + 1 ) U + 50 V ` from the stack lengths (the reservoir has at '
               'most ` rc ` entries, ~ rgln , all at most ` z ` , ~ resspecw ), and ~ t12bud (` bud_A ` ) closes.')
    s = w.s
    c = Ctx(w, ph, T)
    zn, gn, yn, un, on, nn = [c[t] for t in ('Z e. NN', 'G e. NN0', 'Y e. NN', 'U e. NN0', 'O e. NN0', 'N e. NN0')]
    cl = common_cl(w, ph, c, ('G', 'U', 'O', 'N', 'B', 'H', "U'", "W'"))
    RES = '( ( Z Reservoir G ) ` Y )'
    rcl = s([s([zn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), yn, w.inst('reservoircl')], 'syl2anc', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, RES))
    rcl2 = s([c[P.EQ('R')], rcl], 'eqeltrd', '( %s -> R e. ( Word NN0 X. NN0 ) )' % ph)
    r1 = s([rcl2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, R1))
    r2 = s([rcl2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` R ) e. NN0 )' % ph)
    cl.leaf('( 2nd ` R )', 'NN0', r2)
    inn = s([c[P.EQ('I')], s([r1, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, R1))], 'eqeltrd', '( %s -> I e. NN0 )' % ph)
    cl.leaf('I', 'NN0', inn)
    # I <_ Z - 1 <_ ( 2nd R ) (~ rgln at ( G ResGo Y ) 2 ( Z - 1 ))
    rv = s([s([zn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), yn, w.inst('reservoirval')], 'syl2anc', '( %s -> %s = ( ( ( G ResGo Y ) ` 2 ) ` ( Z - 1 ) ) )' % (ph, RES))
    RG = '( ( ( G ResGo Y ) ` 2 ) ` ( Z - 1 ) )'
    zm1 = s([zn, w.inst('nnm1nn0')], 'syl', '( %s -> ( Z - 1 ) e. NN0 )' % ph)
    cl.leaf('( Z - 1 )', 'NN0', zm1)
    rg = s([s([s([gn, yn], 'jca', '( %s -> ( G e. NN0 /\\ Y e. NN ) )' % ph), s([closed(w, ph, '2nn', '2 e. NN'), zm1], 'jca', '( %s -> ( 2 e. NN /\\ ( Z - 1 ) e. NN0 ) )' % ph)], 'jca',
              '( %s -> ( ( G e. NN0 /\\ Y e. NN ) /\\ ( 2 e. NN /\\ ( Z - 1 ) e. NN0 ) ) )' % ph), w.inst('rgln')], 'syl',
           '( %s -> ( ( # ` ( 1st ` %s ) ) <_ ( Z - 1 ) /\\ ( Z - 1 ) <_ ( 2nd ` %s ) ) )' % (ph, RG, RG))
    req = s([c[P.EQ('R')], rv], 'eqtrd', '( %s -> R = %s )' % (ph, RG))
    l1 = s([s([rg], 'simpld', '( %s -> ( # ` ( 1st ` %s ) ) <_ ( Z - 1 ) )' % (ph, RG)),
            s([s([s([req], 'fveq2d', '( %s -> ( 1st ` R ) = ( 1st ` %s ) )' % (ph, RG))], 'fveq2d', '( %s -> ( # ` ( 1st ` R ) ) = ( # ` ( 1st ` %s ) ) )' % (ph, RG))], 'eqcomd',
              '( %s -> ( # ` ( 1st ` %s ) ) = ( # ` ( 1st ` R ) ) )' % (ph, RG))], 'eqbrtrrd' if False else 'id', '') if False else None
    lr = s([s([req], 'fveq2d', '( %s -> ( 1st ` R ) = ( 1st ` %s ) )' % (ph, RG))], 'fveq2d', '( %s -> ( # ` ( 1st ` R ) ) = ( # ` ( 1st ` %s ) ) )' % (ph, RG))
    ile1 = s([s([c[P.EQ('I')], lr], 'eqtrd', '( %s -> I = ( # ` ( 1st ` %s ) ) )' % (ph, RG)), s([rg], 'simpld', '( %s -> ( # ` ( 1st ` %s ) ) <_ ( Z - 1 ) )' % (ph, RG))], 'eqbrtrd',
             '( %s -> I <_ ( Z - 1 ) )' % ph)
    r2e = s([req], 'fveq2d', '( %s -> ( 2nd ` R ) = ( 2nd ` %s ) )' % (ph, RG))
    zle = s([s([rg], 'simprd', '( %s -> ( Z - 1 ) <_ ( 2nd ` %s ) )' % (ph, RG)), s([r2e], 'eqcomd', '( %s -> ( 2nd ` %s ) = ( 2nd ` R ) )' % (ph, RG))], 'breqtrd', '( %s -> ( Z - 1 ) <_ ( 2nd ` R ) )' % ph)
    zm = s([s([zn], 'nncnd', '( %s -> Z e. CC )' % ph), closed(w, ph, 'ax-1cn', '1 e. CC')], 'npcand', '( %s -> ( ( Z - 1 ) + 1 ) = Z )' % ph)
    ir = linarith(w, ph, [ile1, zle], 'I <_ ( 2nd ` R )', closure=cl)
    p2leaf(w, ph, cl, 'B'); p2leaf(w, ph, cl, 'H')
    ilt = linarith(w, ph, [ile1, zm, c[LT2('Z')]], 'I < ( 2 ^ B )', closure=cl)
    # the reservoir's entries are at most Z (~ resspecw , ~ goodprimeswval )
    sp = s([s([zn, gn, yn], '3jca', '( %s -> ( Z e. NN /\\ G e. NN0 /\\ Y e. NN ) )' % ph), w.inst('resspecw')], 'syl',
           '( %s -> ( Fun `\' ( 1st ` %s ) /\\ ran ( 1st ` %s ) = ( ( Z goodPrimesW G ) ` Y ) ) )' % (ph, RES, RES))
    rne = s([s([sp], 'simprd', '( %s -> ran ( 1st ` %s ) = ( ( Z goodPrimesW G ) ` Y ) )' % (ph, RES)), s([s([c[P.EQ('R')]], 'fveq2d', '( %s -> ( 1st ` R ) = ( 1st ` %s ) )' % (ph, RES))], 'rneqd',
                                                                                                                 '( %s -> ran ( 1st ` R ) = ran ( 1st ` %s ) )' % (ph, RES))], 'eqtr2d' if False else 'id', '') if False else None
    rne = s([s([s([c[P.EQ('R')]], 'fveq2d', '( %s -> ( 1st ` R ) = ( 1st ` %s ) )' % (ph, RES))], 'rneqd', '( %s -> ran ( 1st ` R ) = ran ( 1st ` %s ) )' % (ph, RES)),
             s([sp], 'simprd', '( %s -> ran ( 1st ` %s ) = ( ( Z goodPrimesW G ) ` Y ) )' % (ph, RES))], 'eqtrd', '( %s -> ran ( 1st ` R ) = ( ( Z goodPrimesW G ) ` Y ) )' % ph)
    GPW = '{ q e. ( 0 ... Z ) | ( q e. Prime /\\ G < q /\\ A. p e. Prime ( p || ( q - 1 ) -> p <_ Y ) ) }'
    gv = s([s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph), gn, s([yn], 'nnnn0d', '( %s -> Y e. NN0 )' % ph), w.inst('goodprimeswval')], 'syl3anc',
           '( %s -> ( ( Z goodPrimesW G ) ` Y ) = %s )' % (ph, GPW))
    rne2 = s([rne, gv], 'eqtrd', '( %s -> ran ( 1st ` R ) = %s )' % (ph, GPW))
    pa = '( %s /\\ a e. ran ( 1st ` R ) )' % ph
    ain = s([s([], 'simpr', '( %s -> a e. ran ( 1st ` R ) )' % pa), s([rne2], 'adantr', '( %s -> ran ( 1st ` R ) = %s )' % (pa, GPW))], 'eleqtrd', '( %s -> a e. %s )' % (pa, GPW))
    afz = s([s([ain, w.inst('elrabi')], 'syl', '( %s -> a e. ( 0 ... Z ) )' % pa)], 'id', '') if False else s([ain, w.inst('elrabi')], 'syl', '( %s -> a e. ( 0 ... Z ) )' % pa)
    ale = s([afz, w.inst('elfzle2')], 'syl', '( %s -> a <_ Z )' % pa)
    an0 = s([afz, w.inst('elfznn0')], 'syl', '( %s -> a e. NN0 )' % pa)
    cla = Closure(w, pa, {'a': ('NN0', an0), 'Z': ('NN0', s([cl.mem('Z', 'NN0')], 'adantr', '( %s -> Z e. NN0 )' % pa))})
    cla.atom('( 2 ^ B )'); cla.leaf('( 2 ^ B )', 'NN0', s([cl.mem('( 2 ^ B )', 'NN0')], 'adantr', '( %s -> ( 2 ^ B ) e. NN0 )' % pa))
    alt = linarith(w, pa, [ale, s([c[LT2('Z')]], 'adantr', '( %s -> Z < ( 2 ^ B ) )' % pa)], 'a < ( 2 ^ B )', closure=cla)
    ralr = s([alt], 'ralrimiva', '( %s -> %s )' % (ph, RALB(R1, 'B')))
    # the encoded reservoir: at most I ( B + 1 ) + 1 <_ ( c + 1 ) U'
    LR = '( # ` ( encList ` %s ) )' % R1
    lr_ = s([r1, c['B e. NN0'], ralr, w.inst('tm2lenclen')], 'syl3anc', '( %s -> %s <_ ( ( ( # ` %s ) x. ( B + 1 ) ) + 1 ) )' % (ph, LR, R1))
    lr2 = s([lr_, s([s([s([c[P.EQ('I')]], 'eqcomd', '( %s -> ( # ` %s ) = I )' % (ph, R1))], 'oveq1d', '( %s -> ( ( # ` %s ) x. ( B + 1 ) ) = ( I x. ( B + 1 ) ) )' % (ph, R1))], 'oveq1d',
                       '( %s -> ( ( ( # ` %s ) x. ( B + 1 ) ) + 1 ) = ( ( I x. ( B + 1 ) ) + 1 ) )' % (ph, R1))], 'breqtrd', '( %s -> %s <_ ( ( I x. ( B + 1 ) ) + 1 ) )' % (ph, LR))
    cl.leaf(LR, 'NN0', s([s([r1, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, R1)), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LR)))
    C1 = '( %s + 1 )' % CZ
    m1 = lemul1a(w, ph, cl, 'I', C1, '( B + 1 )', linarith(w, ph, [ir], 'I <_ %s' % C1, closure=cl))
    m2 = P.mul_le2(w, ph, cl, C1, '( B + 2 )', "U'", c["( B + 2 ) <_ U'"])
    lrc = linarith(w, ph, [lr2, m1, m2, cl.ge0('( 2nd ` R )')], "%s <_ ( ( %s + 1 ) x. U' )" % (LR, CZ), closure=cl, products=True)
    # cin, csc, cst
    en = s([s([nn, c['H e. NN0'], c[LT2('N', 'H')], w.inst('tm2lentlt')], 'syl3anc', '( %s -> ( # ` ( encNatGam ` N ) ) <_ H )' % ph),
            s([s([nn, w.inst('encnatgamlen')], 'syl', '( %s -> ( # ` ( encNatGam ` N ) ) = ( # ` ( encodeNat ` N ) ) )' % ph)], 'eqcomd', '( %s -> ( # ` ( encodeNat ` N ) ) = ( # ` ( encNatGam ` N ) ) )' % ph)],
           'eqbrtrrd' if False else 'id', '') if False else None
    egl = s([nn, w.inst('encnatgamlen')], 'syl', '( %s -> ( # ` ( encNatGam ` N ) ) = ( # ` ( encodeNat ` N ) ) )' % ph)
    egb = s([nn, c['H e. NN0'], c[LT2('N', 'H')], w.inst('tm2lentlt')], 'syl3anc', '( %s -> ( # ` ( encNatGam ` N ) ) <_ H )' % ph)
    cl.leaf('( # ` ( encodeNat ` N ) )', 'NN0', s([s([nn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` N ) e. Word 2o )' % ph), w.inst('lencl')], 'syl', '( %s -> ( # ` ( encodeNat ` N ) ) e. NN0 )' % ph))
    cl.leaf('( # ` ( encNatGam ` N ) )', 'NN0', s([encw(w, ph, 'N', nn), w.inst('lencl')], 'syl', '( %s -> ( # ` ( encNatGam ` N ) ) e. NN0 )' % ph))
    cin = linarith(w, ph, [egl, egb, c["( ( 2 x. H ) + 4 ) <_ U'"]], "%s <_ U'" % CIN, closure=cl)
    tmbleaf(w, ph, cl, CSC_[len('( TMB ` '):-2]); tmbleaf(w, ph, cl, CST_[len('( TMB ` '):-2])
    cst = P.mul_le2(w, ph, cl, C1, CST_, "U'", c["%s <_ U'" % CST_])
    # the stack lengths
    atoms = {}
    for t_, tn_, b_, bn_, tlt_ in (('U', un, 'B', c['B e. NN0'], c[LT2('U')]), ('O', on, 'H', c['H e. NN0'], c[LT2('O', 'H')]),
                                   ('Z', cl.mem('Z', 'NN0'), 'B', c['B e. NN0'], c[LT2('Z')]), ('I', inn, 'B', c['B e. NN0'], ilt), ('N', nn, 'H', c['H e. NN0'], c[LT2('N', 'H')])):
        atoms['( encNatGam ` %s )' % t_] = P.numatom(w, ph, cl, t_, tn_, b_, bn_, tlt_)
    atoms['( encList ` %s )' % R1] = (s([r1, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, R1)), None)
    lf = stack_lengths(w, ph, cl, VALSZ, atoms)
    nl = '( %s + 1 )' % FALC8(VALSZ)
    LBZ = "( ( ( %s + 1 ) x. U' ) + ( ; 5 0 x. W' ) )" % CZ
    leafle = linarith(w, ph, lf + [lrc, c["U' <_ W'"], c["8 <_ U'"], c["( B + 2 ) <_ U'"], c["( ( 2 x. H ) + 4 ) <_ U'"]], '%s <_ %s' % (nl, LBZ), closure=cl)
    zero = closed(w, ph, '0nn0', '0 e. NN0')
    bd = bud(w, ph, c, cl, CZ, '0', '0', '0', cl.mem(CZ, 'NN0'), zero, zero, zero)
    hy = [cin, c["%s <_ U'" % CSC_], cst, leafle, bd, c["U' <_ W'"], c["8 <_ U'"]] + [cl.ge0(x) for x in ('( 2nd ` R )', "U'", "W'")]
    T2 = TZ2
    le = linarith(w, ph, hy, '%s <_ %s' % (NZF, T2), closure=cl, products=True)
    st = s([le, cl.mem(T2, 'NN0')], 'jca', '( %s -> ( %s <_ %s /\\ %s e. NN0 ) )' % (ph, NZF, T2, T2))
    qed13(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
