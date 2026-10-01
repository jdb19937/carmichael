"""T11 (scan): the arithmetic of ` scanF ` 's prologue, epilogue and final bound, over letters (cited by
~ tmiscfp , ~ tmiscfe , ~ tmiscfa instead of running ` linarith ` under their 3 KB antecedent).

  tmscmeb   ` L <_ B ` : ` 2 L + 4 <_ TMB B ` (a ` moveEntry ` of a numeral below ` 2 ^ B ` , ~ tmbquad )
  tmscfue   ` R <_ H ` : ` H - R e. NN0 ` , ` H - R <_ H ` , and ` 1 <_ R -> ( H - R ) + 1 <_ H ` (the fuel left at the exit)
  tmscfar   ` 4 TMB b + 64 TMB U S + 3 TMB b <_ ( S + 1 ) TMB ( 48 ( N + 1 ) ( C + b ) + 4 N + 102 ) ` , a number
            (` U = 12 ( N + 1 ) ( C + b ) + N + 24 ` , ~ tplbscale , ~ tmbmono )

    MM_DB=sorties/t11.mm python3 tools/gen/t11s_g_far.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith, nlinarith, lineq
from cl import Closure
from t11p_d_plf import tbn
import num
import t6blib

SEL = sys.argv[1:]
UO = os.environ.get('T11S_UO') == '1'
STMTS = {}
TREES = {}


def add(label, tree, concl_):
    STMTS[label] = '( %s -> %s )' % (cj(tree), concl_)
    TREES[label] = (tree, concl_)
    t6blib._STMT[label] = STMTS[label]


TBB = '( TMB ` B )'
T_MEB = (('B e. NN0', 'L e. NN0'), 'L <_ B')
C_MEB = '( ( 2 x. L ) + 4 ) <_ %s' % TBB
add('tmscmeb', T_MEB, C_MEB)

T_FUE = (('H e. NN0', 'R e. NN0'), 'R <_ H')
C_FUE = '( ( ( 1 <_ R -> ( ( H - R ) + 1 ) <_ H ) /\\ ( H - R ) <_ H ) /\\ ( H - R ) e. NN0 )'
add('tmscfue', T_FUE, C_FUE)

MSN = '( ( ( ( ; 1 2 x. ( N + 1 ) ) x. ( C + B ) ) + N ) + ; 2 4 )'
BIGN = '( ( ( ( ; 4 8 x. ( N + 1 ) ) x. ( C + B ) ) + ( 4 x. N ) ) + ; ; 1 0 2 )'
UUN = '( TMB ` %s )' % MSN
TBIGN = '( TMB ` %s )' % BIGN
LHS_FAR = '( ( ( 4 x. %s ) + ( ( ( ; 6 4 x. %s ) x. S ) + 1 ) ) + ( 3 x. %s ) )' % (TBB, UUN, TBB)
BND_FAR = '( ( S + 1 ) x. %s )' % TBIGN
T_FAR = (('N e. NN0', 'C e. NN0', 'B e. NN0'), 'S e. NN0')
C_FAR = '( %s <_ %s /\\ %s e. NN0 )' % (LHS_FAR, BND_FAR, BND_FAR)
add('tmscfar', T_FAR, C_FAR)


def tmscmeb():
    lab = 'tmscmeb'
    T = T_MEB
    ph = cj(T)
    w = W(lab, 'A ` moveEntry ` of a numeral whose code has at most ` b ` bits costs at most ` TMB b ` (~ tmbquad ; the '
               'bound of ~ tmime / ~ tmimebo at ` L = # ( encNatGam n ) ` , ` n < 2 ^ b ` ).')
    s = w.s
    c = Ctx(w, ph, T)
    bn, ln = c['B e. NN0'], c['L e. NN0']
    cl = Closure(w, ph, {'B': ('NN0', bn), 'L': ('NN0', ln)})
    cl.leaf(TBB, 'NN0', tbn(w, ph, 'B', bn))
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([bn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc', '( %s -> ( 4 x. ( ( B + 2 ) ^ 2 ) ) <_ %s )' % (ph, TBB))
    st = nlinarith(w, ph, [c['L <_ B'], qd, cl.ge0('B'), cl.ge0('L')], C_MEB, closure=cl, atoms=['B', 'L', TBB])
    qed_as(w, st, STMTS[lab])
    return w.run(unify_only=UO)


def tmscfue():
    lab = 'tmscfue'
    T = T_FUE
    ph = cj(T)
    w = W(lab, 'The fuel left at the exit of the scan loop: ` H - R ` is a number at most ` H ` , and ` ( H - R ) + 1 <_ H ` '
               'when ` 1 <_ R ` (the successful exit, ~ tmiscfe ).')
    s = w.s
    c = Ctx(w, ph, T)
    hn, rn, rle = c['H e. NN0'], c['R e. NN0'], c['R <_ H']
    cl = Closure(w, ph, {'H': ('NN0', hn), 'R': ('NN0', rn)})
    hr = s([rn, hn, rle, w.inst('nn0sub2')], 'syl3anc', '( %s -> ( H - R ) e. NN0 )' % ph)
    le = linarith(w, ph, [cl.ge0('R')], '( H - R ) <_ H', closure=cl)
    pa = '( %s /\\ 1 <_ R )' % ph
    cla = Closure(w, pa, {'H': ('NN0', s([hn], 'adantr', '( %s -> H e. NN0 )' % pa)), 'R': ('NN0', s([rn], 'adantr', '( %s -> R e. NN0 )' % pa))})
    im = s([linarith(w, pa, [s([], 'simpr', '( %s -> 1 <_ R )' % pa)], '( ( H - R ) + 1 ) <_ H', closure=cla)], 'ex',
           '( %s -> ( 1 <_ R -> ( ( H - R ) + 1 ) <_ H ) )' % ph)
    w.qed([s([im, le], 'jca', '( %s -> ( ( 1 <_ R -> ( ( H - R ) + 1 ) <_ H ) /\\ ( H - R ) <_ H ) )' % ph), hr], 'jca', STMTS[lab])
    return w.run(unify_only=UO)


def tmscfar():
    lab = 'tmscfar'
    T = T_FAR
    ph = cj(T)
    w = W(lab, 'The bound of ` scanF ` at the machine (~ tmiscfa ): the prologue ( ` 4 TMB b ` ), the loop ( ` 64 TMB U ` per unit '
               'of scan cost, ` U = 12 ( # Q + 1 ) ( bq + b ) + # Q + 24 ` ) and the epilogue ( ` 3 TMB b ` ) fit Lean\'s '
               '` ( c + 1 ) TMB ( 48 ( # Q + 1 ) ( bq + b ) + 4 # Q + 102 ) ` : ` 64 TMB U = TMB ( 4 U + 6 ) ` (~ tplbscale ) and '
               '` TMB b <_ TMB U ` (~ tmbmono ).')
    s = w.s
    c = Ctx(w, ph, T)
    nn, cn, bn, sn = c['N e. NN0'], c['C e. NN0'], c['B e. NN0'], c['S e. NN0']
    cl = Closure(w, ph, {'N': ('NN0', nn), 'C': ('NN0', cn), 'B': ('NN0', bn), 'S': ('NN0', sn)})
    msn = cl.mem(MSN, 'NN0')
    cl.leaf(UUN, 'NN0', tbn(w, ph, MSN, msn))
    cl.leaf(TBB, 'NN0', tbn(w, ph, 'B', bn))
    nb = s([nn, bn], 'nn0mulcld', '( %s -> ( N x. B ) e. NN0 )' % ph)
    nc = s([nn, cn], 'nn0mulcld', '( %s -> ( N x. C ) e. NN0 )' % ph)
    hyps0 = [cl.ge0('N'), s([nb], 'nn0ge0d', '( %s -> 0 <_ ( N x. B ) )' % ph), s([nc], 'nn0ge0d', '( %s -> 0 <_ ( N x. C ) )' % ph),
             cl.ge0('B'), cl.ge0('C')]
    bms = linarith(w, ph, hyps0, 'B <_ %s' % MSN, closure=cl, products=True)
    tbm = s([bn, msn, bms, w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, TBB, UUN))
    sc_ = s([closed(w, ph, '3nn0', '3 e. NN0'), msn, w.inst('tplbscale')], 'syl2anc',
            '( %s -> ( ( ( 3 + 1 ) ^ 3 ) x. %s ) = ( TMB ` ( ( ( 3 + 1 ) x. %s ) + ( 2 x. 3 ) ) ) )' % (ph, UUN, MSN))
    ae = lineq(w, ph, '( ( ( 3 + 1 ) x. %s ) + ( 2 x. 3 ) )' % MSN, BIGN, closure=cl, products=True)
    e64 = lineq(w, ph, '( ( ( 3 + 1 ) ^ 3 ) x. %s )' % UUN, '( ; 6 4 x. %s )' % UUN, closure=cl, products=True)
    tb64 = s([s([e64], 'eqcomd', '( %s -> ( ; 6 4 x. %s ) = ( ( ( 3 + 1 ) ^ 3 ) x. %s ) )' % (ph, UUN, UUN)),
              s([sc_, s([ae], 'fveq2d', '( %s -> ( TMB ` ( ( ( 3 + 1 ) x. %s ) + ( 2 x. 3 ) ) ) = %s )' % (ph, MSN, TBIGN))], 'eqtrd',
                '( %s -> ( ( ( 3 + 1 ) ^ 3 ) x. %s ) = %s )' % (ph, UUN, TBIGN))], 'eqtrd', '( %s -> ( ; 6 4 x. %s ) = %s )' % (ph, UUN, TBIGN))
    RHS = '( ( S + 1 ) x. ( ; 6 4 x. %s ) )' % UUN
    rr_ = s([tb64], 'oveq2d', '( %s -> %s = %s )' % (ph, RHS, BND_FAR))
    su = s([cl.mem('S', 'RR'), cl.mem(UUN, 'RR'), cl.ge0('S'), cl.ge0(UUN)], 'mulge0d', '( %s -> 0 <_ ( S x. %s ) )' % (ph, UUN))
    uu1 = s([s([msn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (ph, UUN)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, UUN))
    le2 = linarith(w, ph, [tbm, su, uu1, cl.ge0(TBB)], '%s <_ %s' % (LHS_FAR, RHS), closure=cl, atoms=[UUN, TBB, 'S'], products=True)
    le = s([le2, rr_], 'breqtrd', '( %s -> %s <_ %s )' % (ph, LHS_FAR, BND_FAR))
    bndn = s([rr_, cl.mem(RHS, 'NN0')], 'eqeltrrd', '( %s -> %s e. NN0 )' % (ph, BND_FAR))
    w.qed([le, bndn], 'jca', STMTS[lab])
    return w.run(unify_only=UO)


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
