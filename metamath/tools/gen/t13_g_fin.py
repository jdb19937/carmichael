"""T13: from ~ tmisrcz (the letters) to the frozen ` tmisrchb ` (Lean ` searchF_le_B ` ) and ` tmisrch ` (` searchF_runs ` ).

  tmisrcz1   ~ tmisrcz with the letters ` Q' F A X' W J' J ` replaced by their definitions (their equations become ~ eqid )
  tmisrcz2   ... and ` C' X L Q I R `
  tmisrcz3   ... and the units ` W' U' B' `
  tmisrchb   ... and ` V' := scalesTM C1 K n ` with the scales its projections (~ t13sctmv ): T12's frozen statement
  tmisrch    ~ tmisrchb at ` bs := sbs ` , ` bn := sbn ` (~ nloglt , ~ t13lt2m ): T12's frozen statement

    MM_DB=sorties/t13.mm python3 tools/gen/t13_g_fin.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t13lib import *
import t13_f_stage as F
from t13_b_help import C_SCTMV, T_SCTMV, TUPP, p2leaf, pow2le, pow2lt
from t13_c_u0 import BEQ, UEQ, X0, SB1
from t13_b_help import WEQ, E0_
from lin import linarith
from cl import Closure

SEL = sys.argv[1:]
LEQD, EQ, SC_TY, VTEQ, LEQT = P.LEQD, P.EQ, P.SC_TY, P.VTEQ, P.LEQT
SCEQ5 = F.SCEQ5


def expand(letters):
    """the definitions of the letters, each in terms of the letters that remain (outermost first)"""
    m = {}
    for l in letters:
        m[l] = tsub_text(LEQD[l], m)
    return m


M1 = expand(['J', "J'", 'W', "X'", 'F', 'A', "Q'"])
M2 = expand(['R', 'I', 'Q', 'L', 'X', "C'"])
UPX = tsub_text(X0, {"B'": SB1})
M3 = {"B'": SB1, "U'": '( TMB ` %s )' % UPX, "W'": '( %s x. ( TMB ` %s ) )' % (E0_, UPX)}
M4 = {"V'": SC_, 'Z': PZ(SC_), 'G': PZ99(SC_), 'Y': PY(SC_), 'U': PT(SC_), 'O': PTH(SC_)}


def elim_stmt(prev, m, dropped):
    tree, concl = TREES13[prev]
    t2 = tsub(prune(tree, set(dropped)), m)
    return t2, tsub_text(concl, m)


T_Z1, C_Z1 = elim_stmt('tmisrcz', M1, [EQ(l) for l in M1])
add13('tmisrcz1', T_Z1, C_Z1)
T_Z2, C_Z2 = elim_stmt('tmisrcz1', M2, [EQ(l) for l in M2])
add13('tmisrcz2', T_Z2, C_Z2)
T_Z3, C_Z3 = elim_stmt('tmisrcz2', M3, [BEQ, UEQ, WEQ])
add13('tmisrcz3', T_Z3, C_Z3)
add13s('tmisrchb', STMTS12['tmisrchb'])
add13s('tmisrch', STMTS12['tmisrch'])


def elim(lab, prev, m, dropped, desc):
    tree, concl = TREES13[lab]
    ph = cj(tree)
    w = W(lab, desc)
    s = w.s
    c = CtxX(w, ph, tree)
    ex = {}
    for d in dropped:
        d2 = tsub_text(d, m)
        lhs, rhs = d2.split(' = ', 1)
        assert lhs == rhs, '\n%s\n%s' % (lhs[:200], rhs[:200])
        ex[d2] = s([s([], 'eqid', d2)], 'a1i', '( %s -> %s )' % (ph, d2))
    st, cc = inst(w, ph, prev, m, Bld(w, ph, c, ex))
    assert cc == concl, '\n%s\n%s' % (cc[:300], concl[:300])
    qed13(w, st, lab)
    return w.run()


def tmisrcz1():
    return elim('tmisrcz1', 'tmisrcz', M1, [EQ(l) for l in M1],
                'Lean\'s ` searchF_le_B ` at the letters, the scan\'s and the extraction\'s letters ` J k\' P X m\' U\' Q\' ` '
                'replaced by their definitions (~ tmisrcz ).')


def tmisrcz2():
    return elim('tmisrcz2', 'tmisrcz1', M2, [EQ(l) for l in M2],
                '... and the reservoir\'s letters ` R I Q L X c ` replaced by their definitions (~ tmisrcz1 ).')


def tmisrcz3():
    return elim('tmisrcz3', 'tmisrcz2', M3, [BEQ, UEQ, WEQ],
                '... and the units ` b1 U V ` by their definitions (~ tmisrcz2 ).')


def tmisrchb():
    lab = 'tmisrchb'
    tree, concl = P.TREES12['tmisrchb']
    ph = cj(tree)
    w = W(lab, 'Lean\'s ` searchF_le_B ` (Step5.lean 1966) at the concrete machine: from ` initStacks 0 ( encNatGam n ) ` to '
               '` initStacks 1 ( encodeOutput ( getD ( search ( scalesTM C1 K n ) n ) ) ) ` within ` ( search.2 + 1 ) searchPoly ` '
               'steps, for bit bounds ` bs ` of the scales and ` bn ` of ` n ` and ` theta ` (with ` 1 <_ z ` ; ~ tmisrcz3 at '
               '` scalesTM C1 K n ` , ~ t13sctmv ).')
    s = w.s
    c = CtxX(w, ph, tree)
    cn, knn, nn = c['C e. NN0'], c['K e. NN'], c['N e. NN0']
    sv = F.instc(w, ph, 't13sctmv', {}, c, {}, P.parse_conj(C_SCTMV))
    zn0 = sv['%s e. NN0' % PZ(SC_)]
    z1 = c['1 <_ %s' % PZ(SC_)]
    znn = s([s([zn0, z1], 'jca', '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (ph, PZ(SC_), PZ(SC_))), w.inst('elnnnn0c')], 'sylibr', '( %s -> %s e. NN )' % (ph, PZ(SC_)))
    on0 = s([sv['%s e. NN' % PTH(SC_)]], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, PTH(SC_)))
    ex = {'%s e. NN' % PZ(SC_): znn, '%s e. NN0' % PZ99(SC_): sv['%s e. NN0' % PZ99(SC_)], '%s e. NN' % PY(SC_): sv['%s e. NN' % PY(SC_)],
          '%s e. NN0' % PT(SC_): sv['%s e. NN0' % PT(SC_)], '%s e. NN0' % PTH(SC_): on0, '%s = %s' % (SC_, TUPP): sv['%s = %s' % (SC_, TUPP)]}
    for l in SCEQ5[0] + SCEQ5[1]:
        d2 = tsub_text(l, M4)
        ex[d2] = s([s([], 'eqid', d2)], 'a1i', '( %s -> %s )' % (ph, d2))
    st, cc = inst(w, ph, 'tmisrcz3', M4, Bld(w, ph, c, ex))
    assert cc == concl, '\n%s\n%s' % (cc[:400], concl[:400])
    qed13(w, st, lab)
    return w.run()


def tmisrch():
    lab = 'tmisrch'
    tree, concl = P.TREES12['tmisrch']
    ph = cj(tree)
    w = W(lab, 'Lean\'s ` searchF_runs ` (Step5.lean 2427): the machine body computes ` search ` on every input ` n ` (with '
               '` 1 <_ z ` ) within ` searchBound C1 K n ` steps: ~ tmisrchb at the bit bounds ` sbs ` and ` sbn ` , which bound '
               'every scale, ` C1 ` , ` K ` , ` n ` and ` theta ` (~ nloglt ).')
    s = w.s
    c = CtxX(w, ph, tree)
    cn, knn, nn = c['C e. NN0'], c['K e. NN'], c['N e. NN0']
    sv = F.instc(w, ph, 't13sctmv', {}, c, {}, P.parse_conj(C_SCTMV))
    Z_, G_, Y_, U_, O_ = PZ(SC_), PZ99(SC_), PY(SC_), PT(SC_), PTH(SC_)
    cl = Closure(w, ph, {'C': ('NN0', cn), 'N': ('NN0', nn)})
    cl.leaf('K', 'NN0', s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % ph))
    cl.leaf(Z_, 'NN0', sv['%s e. NN0' % Z_]); cl.leaf(G_, 'NN0', sv['%s e. NN0' % G_]); cl.leaf(U_, 'NN0', sv['%s e. NN0' % U_])
    cl.leaf(Y_, 'NN0', s([sv['%s e. NN' % Y_]], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, Y_)))
    cl.leaf(O_, 'NN0', s([sv['%s e. NN' % O_]], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, O_)))
    SUM = '( ( ( ( ( %s + %s ) + %s ) + %s ) + C ) + K )' % (Z_, G_, Y_, U_)
    NLS = '( 2 Nlog %s )' % SUM
    SBS = '( %s + 2 )' % NLS
    SUMN = '( N + %s )' % O_
    NLN = '( 2 Nlog %s )' % SUMN
    SBN = '( %s + 1 )' % NLN
    assert SBS == SBS_ and SBN == SBN_, (SBS, SBN)
    two = closed(w, ph, '2nn0', '2 e. NN0')
    twoz = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    sumnn = s([cl.mem('( ( ( ( %s + %s ) + %s ) + %s ) + C )' % (Z_, G_, Y_, U_), 'NN0'), knn, w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, SUM))
    sumnnn = s([nn, sv['%s e. NN' % O_], w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> %s e. NN )' % (ph, SUMN))
    nls = s([two, s([sumnn], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, SUM)), w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, NLS))
    nln = s([two, s([sumnnn], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, SUMN)), w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, NLN))
    cl.leaf(NLS, 'NN0', nls); cl.leaf(NLN, 'NN0', nln)
    sbsn = cl.mem(SBS, 'NN0'); sbnn = cl.mem(SBN, 'NN0')
    b2 = linarith(w, ph, [cl.ge0(NLS)], '2 <_ %s' % SBS, closure=cl)
    lts = s([twoz, sumnn, w.inst('nloglt')], 'syl2anc', '( %s -> %s < ( 2 ^ ( %s + 1 ) ) )' % (ph, SUM, NLS))
    ltn = s([twoz, sumnnn, w.inst('nloglt')], 'syl2anc', '( %s -> %s < ( 2 ^ ( %s + 1 ) ) )' % (ph, SUMN, NLN))
    for e_ in ('( %s + 1 )' % NLS, SBS, SBN):
        p2leaf(w, ph, cl, e_)
    pe = pow2le(w, ph, cl, '( %s + 1 )' % NLS, SBS, linarith(w, ph, [], '( %s + 1 ) <_ %s' % (NLS, SBS), closure=cl))
    ex = {'%s e. NN0' % SBS: sbsn, '%s e. NN0' % SBN: sbnn, '2 <_ %s' % SBS: b2}
    for a_ in (Z_, G_, Y_, U_, 'C', 'K'):
        hy = [cl.ge0(x) for x in (Z_, G_, Y_, U_, 'C', 'K') if x != a_]
        ex['%s < ( 2 ^ %s )' % (a_, SBS)] = linarith(w, ph, hy + [lts, pe], '%s < ( 2 ^ %s )' % (a_, SBS), closure=cl)
    for a_ in ('N', O_):
        hy = [cl.ge0(x) for x in ('N', O_) if x != a_]
        ex['%s < ( 2 ^ %s )' % (a_, SBN)] = linarith(w, ph, hy + [ltn], '%s < ( 2 ^ %s )' % (a_, SBN), closure=cl)
    st, cc = inst(w, ph, 'tmisrchb', {'B': SBS, 'H': SBN}, Bld(w, ph, c, ex))
    assert cc == concl, '\n%s\n%s' % (cc[:400], concl[:400])
    qed13(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
