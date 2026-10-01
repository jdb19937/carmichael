"""T11 helper (pool): Lean's ` poolAlgF ` at the machine (Steps23.lean ` poolAlgF_runs ` ) on TMIpla.

  tmipla   poolAlgF_runs: ` copyList 4 5 7 3 ` (~ tmilcpyb ), ` divisorsOfF 5 3 7 6 0 1 ` (~ tmidvsb ), ` poolGoF ` (~ tmiplf )

    MM_DB=sorties/t11p.mm python3 tools/gen/t11p_e_pla.py tmipla
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t11lib import *
from lin import linarith
from cl import Closure
from t10_e_doa import lift_from
import t6blib
import t11_c_darith as DA
import t11_a_arith as AA
import t11p_d_plf as PD
from t11p_d_plf import tbn, PGf, P1f, P2f, FZG
for _D in (STMTS11, DA.STMTS, AA.STMTS):
    t6blib._STMT.update(_D)

SEL = sys.argv[1:]
DV = '( DivisorsOf ` W )'
DV1 = '( 1st ` %s )' % DV
DV2 = '( 2nd ` %s )' % DV
CD = '( ( ( # ` W ) x. C ) + 1 )'
PA = '( ( ( W PoolAlg F ) ` Z ) ` G )'


def tmipla():
    lab = 'tmipla'
    T = numtree11(TREE_PLA)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` poolAlgF_runs ` at the machine: ` copyList 4 5 7 3 ` (~ tmilcpyb ) copies ` Q ` to 5, ` divisorsOfF ` '
               '(~ tmidvsb ) replaces it by ` ( divisorsOf Q ).1 ` (entries below ` 2 ^ ( # Q bq + 1 ) ` , ~ divisorsofle ) and '
               '` poolGoF ` (~ tmiplf ) pushes ` ( poolAlg Q x z k ).1 ` on 6 (~ poolalgval ), every other stack restored, within '
               '` ( ( poolAlg Q x z k ).2 + 1 ) 32 B ( 12 ( # Q + 1 ) bq + 3 b + 22 ) ` steps (~ divisorsofcsteq ).')
    s = w.s
    c0 = Ctx(w, ph, T)
    fn, zn, gn = c0['F e. NN0'], c0['Z e. NN0'], c0['G e. NN0']
    ww, bn, cn = c0['W e. Word NN0'], c0['B e. NN0'], c0['C e. NN0']
    eqs = {'0': (EWg('F', 'X'), ewg_(w, ph, 'F', fn, 'X', c0[WG('X')])), '1': (EWg('Z', "X'"), ewg_(w, ph, 'Z', zn, "X'", c0[WG("X'")])),
           '2': (EWg('G', 'Y'), ewg_(w, ph, 'G', gn, 'Y', c0[WG('Y')])), '4': (ENCL('W', "Y'"), enclg(w, ph, 'W', ww, "Y'", c0[WG("Y'")]))}
    B = Base(w, ph, T, N8, 'pla', eqs)
    c, mk = B.c, B.mk
    LM = FRAGS['pla'].lmap()
    g = lambda k: B.S0.vals[k][2]
    ral = c[RALB('W', 'C')]
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl = Closure(w, ph, {'B': ('NN0', bn), 'C': ('NN0', cn)})
    cl.leaf('( # ` W )', 'NN0', nw)
    WC = '( ( # ` W ) x. C )'
    cl.leaf(WC, 'NN0', s([nw, cn], 'nn0mulcld', '( %s -> %s e. NN0 )' % (ph, WC)))
    cdn = cl.mem(CD, 'NN0')
    dvc = s([ww, w.inst('divisorsofcl')], 'syl', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, DV))
    dv1w = s([dvc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DV1))
    dv2n = s([dvc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, DV2))
    # the divisors are below 2 ^ CD
    hb = s([ww, s([cn, s([ral, s([s([], 'breq1', '( a = p -> ( a < ( 2 ^ C ) <-> p < ( 2 ^ C ) ) )')], 'cbvralvw',
                                  '( A. a e. ran W a < ( 2 ^ C ) <-> A. p e. ran W p < ( 2 ^ C ) )')], 'sylib',
                       '( %s -> A. p e. ran W p < ( 2 ^ C ) )' % ph)], 'jca', '( %s -> ( C e. NN0 /\\ A. p e. ran W p < ( 2 ^ C ) ) )' % ph)],
           'jca', '( %s -> ( W e. Word NN0 /\\ ( C e. NN0 /\\ A. p e. ran W p < ( 2 ^ C ) ) ) )' % ph)
    PW = '( 2 ^ %s )' % WC
    dle = s([hb, w.inst('divisorsofle')], 'syl', '( %s -> A. x e. ran %s x <_ %s )' % (ph, DV1, PW))
    pa = '( %s /\\ p e. ran %s )' % (ph, DV1)
    Lp = lambda st: lift_from(w, ph, pa, st)
    pin = s([], 'simpr', '( %s -> p e. ran %s )' % (pa, DV1))
    ple = s([s([], 'breq1', '( x = p -> ( x <_ %s <-> p <_ %s ) )' % (PW, PW)), pin, Lp(dle)], 'rspcdva', '( %s -> p <_ %s )' % (pa, PW))
    pr = s([s([s([s([Lp(dv1w), w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (pa, DV1, DV1)), w.inst('frn')], 'syl',
                 '( %s -> ran %s C_ NN0 )' % (pa, DV1)), pin], 'sseldd', '( %s -> p e. NN0 )' % pa)], 'nn0red', '( %s -> p e. RR )' % pa)
    PCD = '( 2 ^ %s )' % CD
    wcp = Lp(cl.mem(WC, 'NN0'))
    e1 = s([closed(w, pa, '2cn', '2 e. CC'), wcp], 'expp1d', '( %s -> %s = ( %s x. 2 ) )' % (pa, PCD, PW))
    pwn = s([closed(w, pa, '2nn', '2 e. NN'), wcp, w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (pa, PW))
    clp = Closure(w, pa, {})
    clp.leaf('p', 'RR', pr)
    clp.atom(PW)
    clp.atom(PCD)
    clp.leaf(PCD, 'RR', s([s([closed(w, pa, '2nn', '2 e. NN'), Lp(cdn), w.inst('nnexpcl')], 'syl2anc', '( %s -> %s e. NN )' % (pa, PCD))], 'nnred', '( %s -> %s e. RR )' % (pa, PCD)))
    clp.leaf(PW, 'RR', s([pwn], 'nnred', '( %s -> %s e. RR )' % (pa, PW)))
    plt = linarith(w, pa, [ple, e1, s([pwn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pa, PW))], 'p < %s' % PCD, closure=clp)
    rp = s([plt], 'ralrimiva', '( %s -> A. p e. ran %s p < %s )' % (ph, DV1, PCD))
    dral = s([rp, s([s([], 'breq1', '( p = a -> ( p < %s <-> a < %s ) )' % (PCD, PCD))], 'cbvralvw',
                    '( A. p e. ran %s p < %s <-> A. a e. ran %s a < %s )' % (DV1, PCD, DV1, PCD))], 'sylib', '( %s -> A. a e. ran %s a < %s )' % (ph, DV1, PCD))
    # the Run
    R = B.run()
    E5 = ENCL('W', DK(5))
    B.call(R, 'tmilcpyb', {'K': '4', 'J': '5', 'I': '7', "I'": '3', 'L': 'W', 'R': "Y'", 'B': 'C', 'P': PL('P', 0), 'E': LM['Y2']}, {},
           [('5', E5, B.g(E5, enclg(w, ph, 'W', ww, DK(5), g('5'))))])
    E5b = ENCL(DV1, DK(5))
    B.call(R, 'tmidvsb', {'W': 'W', 'N': 'C', 'X': DK(5), 'P': PL('P', 1), 'E': LM['Y3']}, {},
           [('5', E5b, B.g(E5b, enclg(w, ph, DV1, dv1w, DK(5), g('5'))))])
    PGD = P1f(DV1)
    fzg = s([s([fn, zn], 'jca', '( %s -> ( F e. NN0 /\\ Z e. NN0 ) )' % ph), gn], 'jca', '( %s -> %s )' % (ph, FZG))
    pgc = s([s([fzg, dv1w], 'jca', '( %s -> ( %s /\\ %s e. Word NN0 ) )' % (ph, FZG, DV1)), w.inst('poolgocl')], 'syl',
            '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, PGf(DV1)))
    pgw = s([pgc, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, PGD))
    E6 = ENCL(PGD, DK(6))
    B.call(R, 'tmiplf', {'L': DV1, 'C': CD, "Y'": DK(5), 'P': PL('P', 2), 'E': 'E'},
           {'%s e. Word NN0' % DV1: dv1w, '%s e. NN0' % CD: cdn, RALB(DV1, CD): dral},
           [('5', DK(5), g('5')), ('6', E6, B.g(E6, enclg(w, ph, PGD, pgw, DK(6), g('6'))))])
    cur, out = R.normalize(N8)
    assert out == [('6', E6)], out
    # poolalgval
    pav = s([s([s([s([ww, fn], 'jca', '( %s -> ( W e. Word NN0 /\\ F e. NN0 ) )' % ph), zn], 'jca', '( %s -> ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) )' % ph),
               gn], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ F e. NN0 ) /\\ Z e. NN0 ) /\\ G e. NN0 ) )' % ph), w.inst('poolalgval')], 'syl',
            '( %s -> %s = <. %s , ( %s + %s ) >. )' % (ph, PA, P1f(DV1), DV2, P2f(DV1)))
    p2n = s([pgc, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, P2f(DV1)))
    SS = '( %s + %s )' % (DV2, P2f(DV1))
    ssn = s([dv2n, p2n], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, SS))
    a1 = s([s([pav], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ph, PA, PGD, SS)),
            s([pgw, ssn, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, PGD, SS, PGD))], 'eqtrd',
           '( %s -> ( 1st ` %s ) = %s )' % (ph, PA, PGD))
    a2 = s([s([pav], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (ph, PA, PGD, SS)),
            s([pgw, ssn, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ph, PGD, SS, SS))], 'eqtrd',
           '( %s -> ( 2nd ` %s ) = %s )' % (ph, PA, SS))
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    Dc = triple_D(D)
    DF = UP('D', '6', ENCL('( 1st ` %s )' % PA, DK(6)))
    rf, xf = w.rewrite(Dc, {PGD: ('( 1st ` %s )' % PA, s([a1], 'eqcomd', '( %s -> %s = ( 1st ` %s ) )' % (ph, PGD, PA)))}, ph)
    assert xf == DF, xf
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, rf, Dc, DF))
    # the bound
    BND = triple_parts(STMTS11['tmipla'].rsplit(' -> ', 1)[1][:-2])[2]
    MPA = '( ( ( ( ; 1 2 x. ( ( # ` W ) + 1 ) ) x. C ) + ( 3 x. B ) ) + ; 2 2 )'
    TP = '( TMB ` %s )' % MPA
    mpn = cl.mem(MPA, 'NN0')
    cl.leaf(TP, 'NN0', tbn(w, ph, MPA, mpn))
    M12 = '( ( ( ; 1 2 x. ( # ` W ) ) x. C ) + ; 2 2 )'
    M3 = '( ( 3 x. ( %s + B ) ) + ; 1 0 )' % CD
    TC, T12, T3 = '( TMB ` C )', '( TMB ` %s )' % M12, '( TMB ` %s )' % M3
    cl.leaf(TC, 'NN0', tbn(w, ph, 'C', cn))
    m12n, m3n = cl.mem(M12, 'NN0'), cl.mem(M3, 'NN0')
    cl.leaf(T12, 'NN0', tbn(w, ph, M12, m12n))
    cl.leaf(T3, 'NN0', tbn(w, ph, M3, m3n))
    cl.leaf(DV2, 'NN0', dv2n)
    cl.leaf(P2f(DV1), 'NN0', p2n)
    wcge = cl.ge0(WC)
    clm = Closure(w, ph, {'B': ('NN0', bn), 'C': ('NN0', cn)})
    clm.leaf('( # ` W )', 'NN0', nw)
    mono = lambda a_, an_, ta: s([an_, mpn, linarith(w, ph, [wcge, clm.ge0('C'), clm.ge0('B')], '%s <_ %s' % (a_, MPA), closure=clm, products=True),
                                  w.inst('tmbmono')], 'syl3anc', '( %s -> %s <_ %s )' % (ph, ta, TP))
    mc, m12, m3 = mono('C', cn, TC), mono(M12, m12n, T12), mono(M3, m3n, T3)
    cst = s([ww, w.inst('divisorsofcsteq')], 'syl', '( %s -> ( %s + 1 ) = ( 2 ^ ( # ` W ) ) )' % (ph, DV2))
    p2w = s([nw, w.inst('tpl2pow')], 'syl', '( %s -> ( ( # ` W ) + 1 ) <_ ( 2 ^ ( # ` W ) ) )' % ph)
    wle = s([p2w, s([cst], 'eqcomd', '( %s -> ( 2 ^ ( # ` W ) ) = ( %s + 1 ) )' % (ph, DV2))], 'breqtrd', '( %s -> ( ( # ` W ) + 1 ) <_ ( %s + 1 ) )' % (ph, DV2))
    W1, D1_, N1_ = '( ( # ` W ) + 1 )', '( %s + 1 )' % DV2, '( %s + 1 )' % P2f(DV1)
    R_ = lambda x: cl.mem(x, 'RR')
    f1 = s([R_(TC), R_(TP), R_(W1), cl.ge0(W1), mc], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, W1, TC, W1, TP))
    f2 = s([R_(W1), R_(D1_), R_(TP), cl.ge0(TP), wle], 'lemul1ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, W1, TP, D1_, TP))
    f3 = s([R_(T12), R_(TP), R_(D1_), cl.ge0(D1_), m12], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, D1_, T12, D1_, TP))
    f4 = s([R_(T3), R_(TP), R_(N1_), cl.ge0(N1_), m3], 'lemul2ad', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, N1_, T3, N1_, TP))
    rn, n2 = w.rewrite(BND, {'( 2nd ` %s )' % PA: (SS, a2)}, ph)
    le2 = linarith(w, ph, [f1, f2, f3, f4, cl.ge0(TP), cl.ge0(DV2), cl.ge0(P2f(DV1))], '%s <_ %s' % (n, n2), closure=cl,
                   atoms=['( # ` W )', DV2, P2f(DV1), TC, T12, T3, TP], products=True)
    le = s([le2, s([rn], 'eqcomd', '( %s -> %s = %s )' % (ph, n2, BND))], 'breqtrd', '( %s -> %s <_ %s )' % (ph, n, BND))
    bnd_n = s([rn, cl.mem(n2, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, BND))
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, bnd_n, le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
