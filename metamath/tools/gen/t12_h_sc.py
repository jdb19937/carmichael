"""T12: the scales fragments at the machine (Step5.lean ` scLogs ` ... ` scZ99 ` , ` scalesF ` ).

  t12nlogle  ` Nat.log 2 a <_ a `
  t12bllt    ` bl a < 2 ^ B ` for ` a < 2 ^ B `
  tmisclg    ` scLogs_runs `
  (the other pieces are added as built; statements via add12)

    MM_DB=sorties/t12.mm python3 tools/gen/t12_h_sc.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq, nlinarith
from cl import Closure
from t7_e_cmp import machine, togk, letgk
from t10_n_rgf import tmbn
import t12_g_sc0
import num
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
P2B = '( 2 ^ B )'
NLOG = lambda a: '( 2 Nlog %s )' % a
BL = lambda a: '( bl ` %s )' % a
ST_NLOGLE = '( A e. NN0 -> ( 2 Nlog A ) <_ A )'
ST_BLLT = '( ( A e. NN0 /\\ B e. NN0 /\\ A < ( 2 ^ B ) ) -> ( bl ` A ) < ( 2 ^ B ) )'

# ------------------------------------------------------------ scLogs_runs: n = N , m = B , r7 = X
M1, M2 = NLOG('N'), NLOG(NLOG('N'))
M3 = NLOG(M2)
DATA_SCLG = ((STKD('D'), 'N e. NN0', 'B e. NN0'), (LT2('N'), WG('X')), DEQ(7, EWg('N', 'X')))
TREE_SCLG = TREE0('sclg', DATA_SCLG)
CONCL_SCLG = TRI(CS('sclg'), CLN('E', S, UPS('D', ('1', EWg(M1, DK(1))), ('2', EWg(M2, DK(2))), ('3', EWg(M3, DK(3))))),
                 '( 6 x. ( TMB ` B ) )')
add12('tmisclg', TREE_SCLG, CONCL_SCLG)


def t12nlogle():
    lab = 't12nlogle'
    w = W(lab, 'Lean\'s ` Nat.log 2 a <_ a ` (~ cbnlogle at ` a e. NN ` , ~ nlogz at ` 0 ` ).')
    s = w.s
    a1 = s([], 'cbnlogle', '( A e. NN -> ( 2 Nlog A ) <_ A )')
    ph = 'A = 0'
    j = s([closed(w, ph, '2nn0', '2 e. NN0'), s([s([], 'id', '( A = 0 -> A = 0 )'), closed(w, ph, '0nn0', '0 e. NN0')], 'eqeltrd',
                                                 '( A = 0 -> A e. NN0 )')], 'jca', '( A = 0 -> ( 2 e. NN0 /\\ A e. NN0 ) )')
    b10 = s([s([s([], '0re', '0 e. RR'), s([], '1re', '1 e. RR')], 'ltnlei', '( 0 < 1 <-> -. 1 <_ 0 )'), s([], '0lt1', '0 < 1')], 'mpbi', '-. 1 <_ 0')
    e1 = s([], 'breq2', '( A = 0 -> ( 1 <_ A <-> 1 <_ 0 ) )')
    n1 = s([s([b10], 'a1i', '( A = 0 -> -. 1 <_ 0 )'), e1], 'mtbird', '( A = 0 -> -. 1 <_ A )')
    n2 = s([n1], 'intnand', '( A = 0 -> -. ( 2 <_ 2 /\\ 1 <_ A ) )')
    z = s([s([j, n2], 'jca', '( A = 0 -> ( ( 2 e. NN0 /\\ A e. NN0 ) /\\ -. ( 2 <_ 2 /\\ 1 <_ A ) ) )'), w.inst('nlogz')], 'syl',
          '( A = 0 -> ( 2 Nlog A ) = 0 )')
    l0 = s([z, s([s([], 'id', '( A = 0 -> A = 0 )')], 'eqcomd', '( A = 0 -> 0 = A )')], 'eqtrd', '( A = 0 -> ( 2 Nlog A ) = A )')
    aR = s([s([], 'id', '( A = 0 -> A = 0 )'), s([s([], '0re', '0 e. RR')], 'a1i', '( A = 0 -> 0 e. RR )')], 'eqeltrd', '( A = 0 -> A e. RR )')
    nR = s([l0, aR], 'eqeltrd', '( A = 0 -> ( 2 Nlog A ) e. RR )')
    a2 = s([s([nR], 'leidd', '( A = 0 -> ( 2 Nlog A ) <_ ( 2 Nlog A ) )'), l0], 'breqtrd', '( A = 0 -> ( 2 Nlog A ) <_ A )')
    j2 = s([a1, a2], 'jaoi', '( ( A e. NN \\/ A = 0 ) -> ( 2 Nlog A ) <_ A )')
    w.qed([s([], 'elnn0', '( A e. NN0 <-> ( A e. NN \\/ A = 0 ) )'), j2], 'sylbi', ST_NLOGLE)
    return w.run()


def t12bllt():
    lab = 't12bllt'
    ph = '( A e. NN0 /\\ B e. NN0 /\\ A < ( 2 ^ B ) )'
    w = W(lab, 'The bit length of a number below ` 2 ^ B ` is below ` 2 ^ B ` (~ blle , ~ bernneq3 ).')
    s = w.s
    le = s([], 'blle', '( %s -> ( bl ` A ) <_ B )' % ph)
    bn = s([], 'simp2', '( %s -> B e. NN0 )' % ph)
    u2 = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    b2 = s([u2, bn, w.inst('bernneq3')], 'syl2anc', '( %s -> B < ( 2 ^ B ) )' % ph)
    an = s([], 'simp1', '( %s -> A e. NN0 )' % ph)
    blr = s([s([an, w.inst('blcl')], 'syl', '( %s -> ( bl ` A ) e. NN0 )' % ph)], 'nn0red', '( %s -> ( bl ` A ) e. RR )' % ph)
    br = s([bn], 'nn0red', '( %s -> B e. RR )' % ph)
    pr = s([closed(w, ph, '2re', '2 e. RR'), bn], 'reexpcld', '( %s -> ( 2 ^ B ) e. RR )' % ph)
    w.qed([blr, br, pr, le, b2], 'lelttrd', ST_BLLT)
    return w.run()


def lt2(w, ph, A, an, bn, alt):
    """( ph -> ( bl ` A ) < ( 2 ^ B ) ) from an : A e. NN0 , alt : A < 2 ^ B"""
    return w.s([an, bn, alt, w.inst('t12bllt')], 'syl3anc', '( %s -> ( bl ` %s ) < ( 2 ^ B ) )' % (ph, A))


def nlog_facts(w, ph, A, an, alt, cl):
    """( 2 Nlog A ) e. NN0 , <_ A , < 2 ^ B"""
    s = w.s
    NA = NLOG(A)
    nn = s([closed(w, ph, '2nn0', '2 e. NN0'), an, w.inst('nlogcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, NA))
    le = s([an, w.inst('t12nlogle')], 'syl', '( %s -> %s <_ %s )' % (ph, NA, A))
    cl.leaf(NA, 'NN0', nn)
    lt = linarith(w, ph, [le, alt], '%s < %s' % (NA, P2B), closure=cl)
    return nn, le, lt


def tmisclg():
    lab = 'tmisclg'
    T = numtree(TREE_SCLG)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scLogs_runs ` at the machine: ` M = Nat.log 2 n ` , ` a = Nat.log 2 M ` , ` b = Nat.log 2 a ` '
               'pushed on 1 , 2 , 3 by ` bitlen ` (~ tmiblb ) and ` predNum ` (~ tmiprdbl ), within ` 6 B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    nn, bn, xg = c0['N e. NN0'], c0['B e. NN0'], c0[WG('X')]
    B = Base(w, ph, T, N8, 'sclg', {'7': (EWg('N', 'X'), ewg_(w, ph, 'N', nn, 'X', xg))})
    c, mk = B.c, B.mk
    F_ = FRAGS['sclg']
    LM = F_.lmap()
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    cl = Closure(w, ph, {'N': ('NN0', nn), 'B': ('NN0', bn)})
    cl.atom(P2B)

    def cp(j):
        fn_, cks, en, exn = F_.children[j]
        return PL('P', F_.slot(j)), LM[exn]
    nlt = c[LT2('N')]
    vals = [('N', nn, nlt)]
    for i in range(3):
        A, an, alt = vals[-1]
        J = str(i + 1)
        # bitlen ( 7 or i ) -> J
        K = '7' if i == 0 else str(i)
        P, E = cp(2 * i)
        BA = BL(A)
        ban = s([an, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, BA))
        V1 = EWg(BA, DK(J))
        B.call(R, 'tmiblb', {'K': K, 'J': J, 'I': str(i + 2), "I'": str(i + 3), 'F': A, 'N': 'B', 'X': XOF[K], 'P': P, 'E': E},
               {'%s e. NN0' % A: an, '%s < %s' % (A, P2B): alt}, [(J, V1, B.g(V1, ewg_(w, ph, BA, ban, DK(J), g(J))))])
        # predNum J -> J + 1 on bl A
        P, E = cp(2 * i + 1)
        NA = NLOG(A)
        nan, nle, nalt = nlog_facts(w, ph, A, an, alt, cl)
        V2 = EWg(NA, DK(J))
        B.call(R, 'tmiprdbl', {'K': J, 'J': str(i + 2), 'F': A, 'N': 'B', 'X': DK(J), 'P': P, 'E': E},
               {'%s e. NN0' % A: an, '%s < %s' % (BA, P2B): lt2(w, ph, A, an, bn, alt)}, [(J, V2, B.g(V2, ewg_(w, ph, NA, nan, DK(J), g(J))))])
        XOF[J] = DK(J)
        vals.append((NA, nan, nalt))
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    print('FINAL CHAIN', of, file=sys.stderr)
    TBB = '( TMB ` B )'
    cl.leaf(TBB, 'NN0', tmbn(w, ph, 'B', bn))
    BND = '( 6 x. %s )' % TBB
    le = linarith(w, ph, [], '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


XOF = {'7': 'X'}


# ------------------------------------------------------------ t12lin: Lean's ` lin_lt_two_pow ` : 8 m + 100 < 2 ^ m for 8 <_ m
LIN_ = '( ( 8 x. B ) + ; ; 1 0 0 )'
ST_LIN = '( ( B e. NN0 /\\ 8 <_ B ) -> %s < ( 2 ^ B ) )' % LIN_


def t12lin():
    lab = 't12lin'
    ph = '( B e. NN0 /\\ 8 <_ B )'
    w = W(lab, 'Lean\'s ` lin_lt_two_pow ` : ` 8 m + 100 < 2 ^ m ` once ` 8 <_ m ` ( ` 2 ^ m = 256 * 2 ^ ( m - 8 ) ` and '
               '~ bernneq3 ).')
    s = w.s
    bn = s([], 'simpl', '( %s -> B e. NN0 )' % ph)
    b8 = s([], 'simpr', '( %s -> 8 <_ B )' % ph)
    C = '( B - 8 )'
    cn = s([closed(w, ph, '8nn0', '8 e. NN0'), bn, b8, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (ph, C))
    u2 = s([s([s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ph)
    P2C = '( 2 ^ %s )' % C
    clt = s([u2, cn, w.inst('bernneq3')], 'syl2anc', '( %s -> %s < %s )' % (ph, C, P2C))
    p2c = s([closed(w, ph, '2nn0', '2 e. NN0'), cn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, P2C))
    c1 = s([clt, s([cn, p2c, w.inst('nn0ltp1le')], 'syl2anc', '( %s -> ( %s < %s <-> ( %s + 1 ) <_ %s ) )' % (ph, C, P2C, C, P2C))], 'mpbid',
           '( %s -> ( %s + 1 ) <_ %s )' % (ph, C, P2C))
    cl = Closure(w, ph, {'B': ('NN0', bn)})
    cl.leaf(C, 'NN0', cn)
    cl.leaf(P2C, 'NN0', p2c)
    np = s([cl.mem('B', 'CC'), closed(w, ph, '8cn', '8 e. CC'), w.inst('npcan')], 'syl2anc', '( %s -> ( %s + 8 ) = B )' % (ph, C))
    ea = s([closed(w, ph, '2cn', '2 e. CC'), cn, closed(w, ph, '8nn0', '8 e. NN0'), w.inst('expadd')], 'syl3anc',
           '( %s -> ( 2 ^ ( %s + 8 ) ) = ( %s x. ( 2 ^ 8 ) ) )' % (ph, C, P2C))
    e8 = s([s([s([], '2exp8', '( 2 ^ 8 ) = ; ; 2 5 6')], 'a1i', '( %s -> ( 2 ^ 8 ) = ; ; 2 5 6 )' % ph)], 'oveq2d',
           '( %s -> ( %s x. ( 2 ^ 8 ) ) = ( %s x. ; ; 2 5 6 ) )' % (ph, P2C, P2C))
    pb = s([s([s([np], 'oveq2d', '( %s -> ( 2 ^ ( %s + 8 ) ) = ( 2 ^ B ) )' % (ph, C))], 'eqcomd', '( %s -> ( 2 ^ B ) = ( 2 ^ ( %s + 8 ) ) )' % (ph, C)),
            ea, e8], '3eqtrd', '( %s -> ( 2 ^ B ) = ( %s x. ; ; 2 5 6 ) )' % (ph, P2C))
    cl.atom('( 2 ^ B )')
    cl.atom(P2C)
    le = linarith(w, ph, [pb, c1, np, cl.ge0(C)], '%s < ( 2 ^ B )' % LIN_, closure=cl, atoms=['( 2 ^ B )', P2C])
    w.qed([le, w.inst('biid')], 'mpbi', ST_LIN)
    return w.run()


# ------------------------------------------------------------ scTheta_runs: M = G , m = B , r1 = X
L_TH = '( ( 2 Nlog ( G + 1 ) ) + 1 )'
EXPTH = '( |_ ` ( ( ( 6 x. %s ) + 4 ) / 5 ) )' % L_TH
TH_ = '( 2 ^ %s )' % EXPTH
DATA_SCTH = ((STKD('D'), 'G e. NN0', 'B e. NN0'), ('8 <_ B', LT2('( G + 1 )'), '%s < B' % EXPTH), (WG('X'), DEQ(1, EWg('G', 'X'))))
TREE_SCTH = TREE0('scth', DATA_SCTH)
CONCL_SCTH = TRI(CS('scth'), CLN('E', S, UP('D', '0', EWg(TH_, DK(0)))), '( ; 1 3 x. ( TMB ` B ) )')
add12('tmiscth', TREE_SCTH, CONCL_SCTH)


def expose_call(w, ph, B, R, k):
    from t10_u_s2s import expose
    return expose(w, ph, B, R, k)


def tmiscth():
    lab = 'tmiscth'
    T = numtree(TREE_SCTH)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scTheta_runs ` at the machine: ` theta = 2 ^ ( ( 6 ( log ( M + 1 ) + 1 ) + 4 ) / 5 ) ` from ` M ` on 1 '
               '(peeked), pushed on 0: ` dup ` , ` incr ` , ` bitlen ` , ` dropNum ` , ` pushNum 4 6 ` , ` mulC ` , four ` incr ` , '
               '` pushNum 4 5 ` , ` divC ` , ` pow2 ` , within ` 13 B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    gn, bn, xg = c0['G e. NN0'], c0['B e. NN0'], c0[WG('X')]
    B = Base(w, ph, T, N8, 'scth', {'1': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xg))})
    c, mk = B.c, B.mk
    F_ = FRAGS['scth']
    LM = F_.lmap()
    g = lambda k: B.S0.vals[k][2]
    R = B.run()
    cl = Closure(w, ph, {'G': ('NN0', gn), 'B': ('NN0', bn)})
    cl.atom(P2B)
    lin8 = s([s([bn, c['8 <_ B']], 'jca', '( %s -> ( B e. NN0 /\\ 8 <_ B ) )' % ph), w.inst('t12lin')], 'syl', '( %s -> %s < %s )' % (ph, LIN_, P2B))
    g1lt = c[LT2('( G + 1 )')]
    G1 = '( G + 1 )'
    g1n = cl.mem(G1, 'NN0')
    BLG = BL(G1)
    blg = s([g1n, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, BLG))
    cl.leaf(BLG, 'NN0', blg)
    blle = s([g1n, bn, g1lt, w.inst('blle')], 'syl3anc', '( %s -> %s <_ B )' % (ph, BLG))
    hy = [lin8, blle, g1lt, cl.ge0('B')]

    def lt(x):
        return linarith(w, ph, hy, '%s < %s' % (x, P2B), closure=cl)

    def cp(j):
        fn_, cks, en, exn = F_.children[j]
        return PL('P', F_.slot(j)), LM[exn]

    def ew(t, X, xg_):
        v = EWg(t, X)
        return v, B.g(v, ewg_(w, ph, t, cl.mem(t, 'NN0'), X, xg_))
    # 1. dup 1 4 5
    P, E = cp(0)
    v, gv = ew('G', DK(4), g('4'))
    B.call(R, 'tmidupb', {'K': '1', 'J': '4', 'I': '5', 'F': 'G', 'N': 'B', 'X': 'X', 'P': P, 'E': E},
           {'G < %s' % P2B: lt('G')}, [('4', v, gv)])
    # 2. incr 4 5
    P, E = cp(1)
    v, gv = ew(G1, DK(4), g('4'))
    B.call(R, 'tmiincbs', {'K': '4', 'J': '5', 'F': 'G', 'N': 'B', 'X': DK(4), 'P': P, 'E': E}, {'G < %s' % P2B: lt('G')}, [('4', v, gv)])
    # 3. bitlen 4 5 6 0
    P, E = cp(2)
    v, gv = ew(BLG, DK(5), g('5'))
    B.call(R, 'tmiblb', {'K': '4', 'J': '5', 'I': '6', "I'": '0', 'F': G1, 'N': 'B', 'X': DK(4), 'P': P, 'E': E},
           {'%s e. NN0' % G1: g1n, '%s < %s' % (G1, P2B): g1lt}, [('5', v, gv)])
    # 4. dropNum 4
    P, E = cp(3)
    Son, old = expose_call(w, ph, B, R, '4')
    B.call(R, 'tmidropb', {'K': '4', 'F': G1, 'N': 'B', 'X': DK(4), 'P': P, 'E': E},
           {'%s e. NN0' % G1: g1n, '%s < %s' % (G1, P2B): g1lt}, [('4', DK(4), g('4'))], on=(Son, old))
    # 5. pushNum 4 6
    P, E = cp(4)
    v, gv = ew('6', DK(4), g('4'))
    B.call(R, 'tmipnvb', {'K': '4', 'N': '6', 'B': 'B', 'P': P, 'E': E},
           {'6 e. NN0': closed(w, ph, '6nn0', '6 e. NN0'), '6 < %s' % P2B: lt('6')}, [('4', v, gv)])
    # 6. mulC 4 5 6 0 2
    P, E = cp(5)
    SIX = '( 6 x. %s )' % BLG
    v, gv = ew(SIX, DK(6), g('6'))
    B.call(R, 'tmimulb', {'K': '4', 'J': '5', 'I': '6', "I'": '0', 'I"': '2', 'F': '6', 'G': BLG, 'N': 'B', 'X': DK(4), 'Y': DK(5),
                          'P': P, 'E': E},
           {'6 e. NN0': closed(w, ph, '6nn0', '6 e. NN0'), '6 < %s' % P2B: lt('6'), '%s < %s' % (BLG, P2B): lt(BLG), '%s e. NN0' % BLG: blg},
           [('6', v, gv), ('4', DK(4), g('4')), ('5', DK(5), g('5'))])
    # 7-10. incr 6 0 , four times
    cur_v = SIX
    for j in range(4):
        P, E = cp(6 + j)
        nxt = '( %s + 1 )' % cur_v
        v, gv = ew(nxt, DK(6), g('6'))
        B.call(R, 'tmiincbs', {'K': '6', 'J': '0', 'F': cur_v, 'N': 'B', 'X': DK(6), 'P': P, 'E': E},
               {'%s e. NN0' % cur_v: cl.mem(cur_v, 'NN0'), '%s < %s' % (cur_v, P2B): lt(cur_v)}, [('6', v, gv)])
        cur_v = nxt
    # 11. pushNum 4 5
    P, E = cp(10)
    v, gv = ew('5', DK(4), g('4'))
    B.call(R, 'tmipnvb', {'K': '4', 'N': '5', 'B': 'B', 'P': P, 'E': E},
           {'5 e. NN0': closed(w, ph, '5nn0', '5 e. NN0'), '5 < %s' % P2B: lt('5')}, [('4', v, gv)])
    # 12. divC 6 4 5 0 1 2
    P, E = cp(11)
    Q = '( |_ ` ( %s / 5 ) )' % cur_v
    qn = s([cl.mem(cur_v, 'NN0'), closed(w, ph, '5nn', '5 e. NN'), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Q))
    cl.leaf(Q, 'NN0', qn)
    v, gv = ew(Q, DK(5), g('5'))
    B.call(R, 'tmidivcb', {'K': '6', 'J': '4', 'I': '5', "I'": '0', 'I"': '1', 'I0': '2', 'F': cur_v, 'G': '5', 'N': 'B', 'X': DK(6), 'Y': DK(4),
                           'P': P, 'E': E},
           {'%s e. NN0' % cur_v: cl.mem(cur_v, 'NN0'), '5 e. NN': closed(w, ph, '5nn', '5 e. NN'), '%s < %s' % (cur_v, P2B): lt(cur_v),
            '5 < %s' % P2B: lt('5')},
           [('6', DK(6), g('6')), ('5', v, gv), ('4', DK(4), g('4'))])
    # 13. pow2 5 0 4 6: the exponent Q is Lean's ( 6 L + 4 ) / 5 with L = log ( M + 1 ) + 1 = bl ( M + 1 )
    P, E = cp(12)
    g1nn = s([gn, w.inst('nn0p1nn')], 'syl', '( %s -> %s e. NN )' % (ph, G1))
    bnl = s([g1nn, w.inst('blnlog')], 'syl', '( %s -> ( 2 Nlog %s ) = ( %s - 1 ) )' % (ph, G1, BLG))
    nlg = s([closed(w, ph, '2nn0', '2 e. NN0'), g1n, w.inst('nlogcl')], 'syl2anc', '( %s -> ( 2 Nlog %s ) e. NN0 )' % (ph, G1))
    cl.leaf('( 2 Nlog %s )' % G1, 'NN0', nlg)
    num_eq = linarith_eq(w, ph, cur_v, '( ( 6 x. %s ) + 4 )' % L_TH, [bnl], cl)
    qe = s([s([num_eq], 'oveq1d', '( %s -> ( %s / 5 ) = ( ( ( 6 x. %s ) + 4 ) / 5 ) )' % (ph, cur_v, L_TH))], 'fveq2d',
           '( %s -> %s = %s )' % (ph, Q, EXPTH))
    qlt = s([qe, c['%s < B' % EXPTH]], 'eqbrtrd', '( %s -> %s < B )' % (ph, Q))
    TQ = '( 2 ^ %s )' % Q
    tqn = s([closed(w, ph, '2nn0', '2 e. NN0'), qn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, TQ))
    cl.leaf(TQ, 'NN0', tqn)
    v, gv = ew(TQ, DK(0), g('0'))
    B.call(R, 'tmip2b', {'K': '5', 'J': '0', 'I': '4', "I'": '6', 'F': Q, 'N': 'B', 'X': DK(5), 'P': P, 'E': E},
           {'%s < B' % Q: qlt, '%s e. NN0' % Q: qn}, [('5', DK(5), g('5')), ('0', v, gv)])
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    print('FINAL CHAIN', of, file=sys.stderr)
    Dc = triple_D(D)
    rd, xd = w.rewrite(Dc, {Q: (EXPTH, qe)}, ph)
    assert xd == UP('D', '0', EWg(TH_, DK(0))), xd
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, rd, Dc, xd))
    TBB = '( TMB ` B )'
    cl.leaf(TBB, 'NN0', tmbn(w, ph, 'B', bn))
    BND = '( ; 1 3 x. %s )' % TBB
    le = linarith(w, ph, [], '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def linarith_eq(w, ph, a, b, hyps, cl, products=False):
    """( ph -> a = b ) from two linarith inequalities"""
    s = w.s
    l1 = linarith(w, ph, hyps, '%s <_ %s' % (a, b), closure=cl, products=products)
    l2 = linarith(w, ph, hyps, '%s <_ %s' % (b, a), closure=cl, products=products)
    rr = s([cl.mem(a, 'RR'), cl.mem(b, 'RR')], 'jca', '( %s -> ( %s e. RR /\\ %s e. RR ) )' % (ph, a, b))
    bi = s([rr, w.inst('letri3')], 'syl', '( %s -> ( %s = %s <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (ph, a, b, a, b, b, a))
    return s([bi, s([l1, l2], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ph, a, b, b, a))], 'mpbird', '( %s -> %s = %s )' % (ph, a, b))



def exp_lt(w, ph, Q, qn, bn, qlt):
    """( ph -> ( 2 ^ Q ) < ( 2 ^ B ) ) from qlt : Q < B (~ ltexp2a )"""
    s = w.s
    a = s([closed(w, ph, '2re', '2 e. RR'), s([qn], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, Q)), s([bn], 'nn0zd', '( %s -> B e. ZZ )' % ph)], '3jca',
          '( %s -> ( 2 e. RR /\\ %s e. ZZ /\\ B e. ZZ ) )' % (ph, Q))
    b = s([closed(w, ph, '1lt2', '1 < 2'), qlt], 'jca', '( %s -> ( 1 < 2 /\\ %s < B ) )' % (ph, Q))
    return s([a, b, w.inst('ltexp2a')], 'syl2anc', '( %s -> ( 2 ^ %s ) < ( 2 ^ B ) )' % (ph, Q))


class ScRun:
    """a straight-line run at the numeral stacks with a bit bound B: the Base, the Run, the Closure and the facts
    ( 8 B + 100 < 2 ^ B ) , ( x <_ B ) for the bit lengths, so that every operand bound is one linarith"""
    def __init__(self, w, ph, T, fname, eqs, leaves, bound_hyps=()):
        self.w, self.ph = w, ph
        s = w.s
        self.B = Base(w, ph, T, N8, fname, eqs)
        self.c, self.mk = self.B.c, self.B.mk
        self.F = FRAGS[fname]
        self.LM = self.F.lmap()
        self.R = self.B.run()
        self.cl = Closure(w, ph, leaves)
        self.cl.atom(P2B)
        c = self.c
        bn = leaves['B'][1]
        self.bn = bn
        self.lin8 = s([s([bn, c['8 <_ B']], 'jca', '( %s -> ( B e. NN0 /\\ 8 <_ B ) )' % ph), w.inst('t12lin')], 'syl',
                      '( %s -> %s < %s )' % (ph, LIN_, P2B))
        self.hy = [self.lin8, self.cl.ge0('B')] + list(bound_hyps)
        self.j = 0

    def g(self, k):
        return self.B.S0.vals[k][2]

    def lt(self, x):
        return linarith(self.w, self.ph, self.hy, '%s < %s' % (x, P2B), closure=self.cl)

    def mem(self, x):
        return self.cl.mem(x, 'NN0')

    def ew(self, t, X, xg):
        v = EWg(t, X)
        return v, self.B.g(v, ewg_(self.w, self.ph, t, self.mem(t), X, xg))

    def cp(self):
        fn_, cks, en, exn = self.F.children[self.j]
        self.j += 1
        return PL('P', self.F.slot(self.j - 1)), self.LM[exn]

    def call(self, label, m, extra, updates, **kw):
        P, E = self.cp()
        m = dict(m); m['P'] = P; m['E'] = E
        return self.B.call(self.R, label, m, extra, updates, **kw)

    def drop(self, k, F, X, xg):
        """dropNum k of EW( F , X ) (~ tmidropb after exposing k)"""
        Son, old = expose_call(self.w, self.ph, self.B, self.R, k)
        return self.call('tmidropb', {'K': k, 'F': F, 'N': 'B', 'X': X},
                         {'%s e. NN0' % F: self.mem(F), '%s < %s' % (F, P2B): self.lt(F)}, [(k, X, xg)], on=(Son, old))

    def finish(self, lab, final, rules=None, cost=None):
        w, ph, s = self.w, self.ph, self.w.s
        cur, of = self.R.normalize(N8)
        t, C, D, n = self.R.tri, self.R.C0, self.R.cur, self.R.n
        print('FINAL CHAIN', of, file=sys.stderr)
        Dc = triple_D(D)
        if rules:
            rd, xd = w.rewrite(Dc, rules, ph)
            assert xd == final, '\n%s\n%s' % (xd, final)
            t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, rd, Dc, xd))
        else:
            assert Dc == final, '\n%s\n%s' % (Dc, final)
        TBB = '( TMB ` B )'
        self.cl.leaf(TBB, 'NN0', tmbn(w, ph, 'B', self.bn))
        le = linarith(w, ph, list(cost or []), '%s <_ %s' % (n, self.BND), closure=self.cl)
        st = hrle(w, ph, self.mk['phm'], t, C, D, n, self.BND, self.cl.mem(self.BND, 'NN0'), le)
        finish(w, st, lab)
        return w.run()


def me_cost(w, ph, t, tn, tlt, cl):
    """( ph -> ( ( 2 x. ( # ` ( encNatGam ` t ) ) ) + 4 ) <_ ( TMB ` B ) )"""
    from t10_u_s2s import me_bound_n
    bn = cl.mem('B', 'NN0')
    if '( TMB ` B )' not in getattr(cl, 'leaves', {}):
        cl.leaf('( TMB ` B )', 'NN0', tmbn(w, ph, 'B', bn))
    return me_bound_n(w, ph, t, tn, tlt, 'B', bn, cl)


# ------------------------------------------------------------ scT_runs: a = G , m = B , r2 = X
DATA_SCTT = ((STKD('D'), 'G e. NN0', 'B e. NN0'), ('8 <_ B', LT2('G'), LT2('( 3 x. G )')), (WG('X'), DEQ(2, EWg('G', 'X'))))
TREE_SCTT = TREE0('sctt', DATA_SCTT)
CONCL_SCTT = TRI(CS('sctt'), CLN('E', S, UP('D', '0', EWg('( 3 x. G )', DK(0)))), '( 4 x. ( TMB ` B ) )')
add12('tmisctt', TREE_SCTT, CONCL_SCTT)


def tmisctt():
    lab = 'tmisctt'
    T = numtree(TREE_SCTT)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scT_runs ` at the machine: ` T = 3 a ` from ` a ` on 2 (peeked), pushed on 0: ` pushNum 4 3 ` '
               '(~ tmipnvb ), ` dup ` , ` mulC ` , ` moveEntry ` , within ` 4 B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    gn, bn, xg = c0['G e. NN0'], c0['B e. NN0'], c0[WG('X')]
    Rn = ScRun(w, ph, T, 'sctt', {'2': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xg))}, {'G': ('NN0', gn), 'B': ('NN0', bn)},
               [c0[LT2('G')], c0[LT2('( 3 x. G )')]])
    g = Rn.g
    v, gv = Rn.ew('3', DK(4), g('4'))
    Rn.call('tmipnvb', {'K': '4', 'N': '3', 'B': 'B'}, {'3 e. NN0': closed(w, ph, '3nn0', '3 e. NN0'), '3 < %s' % P2B: Rn.lt('3')}, [('4', v, gv)])
    v, gv = Rn.ew('G', DK(5), g('5'))
    Rn.call('tmidupb', {'K': '2', 'J': '5', 'I': '6', 'F': 'G', 'N': 'B', 'X': 'X'}, {}, [('5', v, gv)])
    G3 = '( 3 x. G )'
    v, gv = Rn.ew(G3, DK(6), g('6'))
    Rn.call('tmimulb', {'K': '4', 'J': '5', 'I': '6', "I'": '1', 'I"': '3', 'F': '3', 'G': 'G', 'N': 'B', 'X': DK(4), 'Y': DK(5)},
            {'3 e. NN0': closed(w, ph, '3nn0', '3 e. NN0'), '3 < %s' % P2B: Rn.lt('3')}, [('6', v, gv), ('4', DK(4), g('4')), ('5', DK(5), g('5'))])
    WG3 = '( encNatGam ` %s )' % G3
    v, gv = Rn.ew(G3, DK(0), g('0'))
    Rn.call('tmime', {'K': '6', 'J': '0', 'I': '4', 'W': WG3, 'X': DK(6)}, {WRD(WG3, BITS): engb(w, ph, G3, Rn.mem(G3))},
            [('6', DK(6), g('6')), ('0', v, gv)])
    Rn.BND = '( 4 x. ( TMB ` B ) )'
    mc = me_cost(w, ph, G3, Rn.mem(G3), c0[LT2(G3)], Rn.cl)
    return Rn.finish(lab, UP('D', '0', EWg(G3, DK(0))), cost=[mc])



# ------------------------------------------------------------ scZ_runs: C1 = C , M = F , a = G , b = H , m = B , r1 r2 r3 = X X' Y
CG = '( C x. G )'
ZZ = '( ( C x. G ) x. H )'
DATA_SCZZ = ((STKD('D'), ('C e. NN0', 'F e. NN0'), ('G e. NN0', 'H e. NN0', 'B e. NN0')),
             (('8 <_ B', LT2('C'), LT2('F')), (LT2('G'), LT2('H'), LT2(CG))),
             ((WG('X'), WG("X'"), WG('Y')), (DEQ(1, EWg('F', 'X')), DEQ(2, EWg('G', "X'")), DEQ(3, EWg('H', 'Y')))))
TREE_SCZZ = TREE0('sczz', DATA_SCZZ)
CONCL_SCZZ = TRI(CS('sczz'), CLN('E', S, UPS('D', ('1', 'X'), ('2', "X'"), ('3', 'Y'), ('5', EWg(ZZ, DK(5))))), '( 8 x. ( TMB ` B ) )')
add12('tmisczz', TREE_SCZZ, CONCL_SCZZ)


def tmisczz():
    lab = 'tmisczz'
    T = numtree(TREE_SCZZ)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scZ_runs ` at the machine: ` z = C1 a b ` pushed on 5 from ` a ` on 2 and ` b ` on 3 , then ` M ` , '
               '` a ` , ` b ` dropped: ` pushNum 4 C1 ` (~ tmipnvb ), ` dup ` , ` mulC ` , ` dup ` , ` mulC ` , three ` dropNum ` , '
               'within ` 8 B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    cn, fn, gn, hn, bn = c0['C e. NN0'], c0['F e. NN0'], c0['G e. NN0'], c0['H e. NN0'], c0['B e. NN0']
    xg, x2g, yg = c0[WG('X')], c0[WG("X'")], c0[WG('Y')]
    eqs = {'1': (EWg('F', 'X'), ewg_(w, ph, 'F', fn, 'X', xg)), '2': (EWg('G', "X'"), ewg_(w, ph, 'G', gn, "X'", x2g)),
           '3': (EWg('H', 'Y'), ewg_(w, ph, 'H', hn, 'Y', yg))}
    Rn = ScRun(w, ph, T, 'sczz', eqs, {'C': ('NN0', cn), 'F': ('NN0', fn), 'G': ('NN0', gn), 'H': ('NN0', hn), 'B': ('NN0', bn)},
               [c0[LT2(x)] for x in ('C', 'F', 'G', 'H', CG)])
    g = Rn.g
    v, gv = Rn.ew('C', DK(4), g('4'))
    Rn.call('tmipnvb', {'K': '4', 'N': 'C', 'B': 'B'}, {}, [('4', v, gv)])
    v, gv = Rn.ew('G', DK(5), g('5'))
    Rn.call('tmidupb', {'K': '2', 'J': '5', 'I': '6', 'F': 'G', 'N': 'B', 'X': "X'"}, {}, [('5', v, gv)])
    v, gv = Rn.ew(CG, DK(6), g('6'))
    Rn.call('tmimulb', {'K': '4', 'J': '5', 'I': '6', "I'": '1', 'I"': '3', 'F': 'C', 'G': 'G', 'N': 'B', 'X': DK(4), 'Y': DK(5)}, {},
            [('6', v, gv), ('4', DK(4), g('4')), ('5', DK(5), g('5'))])
    v, gv = Rn.ew('H', DK(4), g('4'))
    Rn.call('tmidupb', {'K': '3', 'J': '4', 'I': '5', 'F': 'H', 'N': 'B', 'X': 'Y'}, {}, [('4', v, gv)])
    v, gv = Rn.ew(ZZ, DK(5), g('5'))
    Rn.call('tmimulb', {'K': '6', 'J': '4', 'I': '5', "I'": '1', 'I"': '2', 'F': CG, 'G': 'H', 'N': 'B', 'X': DK(6), 'Y': DK(4)},
            {'%s e. NN0' % CG: Rn.mem(CG)}, [('5', v, gv), ('6', DK(6), g('6')), ('4', DK(4), g('4'))])
    Rn.drop('1', 'F', 'X', xg)
    Rn.drop('2', 'G', "X'", x2g)
    Rn.drop('3', 'H', 'Y', yg)
    Rn.BND = '( 8 x. ( TMB ` B ) )'
    return Rn.finish(lab, UPS('D', ('1', 'X'), ('2', "X'"), ('3', 'Y'), ('5', EWg(ZZ, DK(5)))))


# ------------------------------------------------------------ scBz_runs: z = Z , m = B , r5 = X
BZ_ = '( ( 2 Nlog Z ) + 1 )'
DATA_SCBZ = ((STKD('D'), 'Z e. NN0', 'B e. NN0'), ('8 <_ B', LT2('Z'), WG('X')), DEQ(5, EWg('Z', 'X')))
TREE_SCBZ = TREE0('scbz', DATA_SCBZ)
CONCL_SCBZ = TRI(CS('scbz'), CLN('E', S, UP('D', '4', EWg(BZ_, DK(4)))), '( 3 x. ( TMB ` B ) )')
add12('tmiscbz', TREE_SCBZ, CONCL_SCBZ)


def tmiscbz():
    lab = 'tmiscbz'
    T = numtree(TREE_SCBZ)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scBz_runs ` at the machine: ` bz = log z + 1 ` from ` z ` on 5 (peeked), pushed on 4: ` bitlen ` '
               '(~ tmiblb ), ` predNum ` (~ tmiprdbl ), ` incr ` , within ` 3 B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    zn, bn, xg = c0['Z e. NN0'], c0['B e. NN0'], c0[WG('X')]
    Rn = ScRun(w, ph, T, 'scbz', {'5': (EWg('Z', 'X'), ewg_(w, ph, 'Z', zn, 'X', xg))}, {'Z': ('NN0', zn), 'B': ('NN0', bn)},
               [c0[LT2('Z')]])
    g = Rn.g
    NZ = NLOG('Z')
    nzn, nzle, nzlt = nlog_facts(w, ph, 'Z', zn, c0[LT2('Z')], Rn.cl)
    Rn.hy.append(nzlt)
    BZL = BL('Z')
    bzn = s([zn, w.inst('blcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, BZL))
    Rn.cl.leaf(BZL, 'NN0', bzn)
    v, gv = Rn.ew(BZL, DK(4), g('4'))
    Rn.call('tmiblb', {'K': '5', 'J': '4', 'I': '6', "I'": '1', 'F': 'Z', 'N': 'B', 'X': 'X'}, {}, [('4', v, gv)])
    v, gv = Rn.ew(NZ, DK(4), g('4'))
    Rn.call('tmiprdbl', {'K': '4', 'J': '6', 'F': 'Z', 'N': 'B', 'X': DK(4)}, {'%s < %s' % (BZL, P2B): lt2(w, ph, 'Z', zn, bn, c0[LT2('Z')])},
            [('4', v, gv)])
    v, gv = Rn.ew(BZ_, DK(4), g('4'))
    Rn.call('tmiincbs', {'K': '4', 'J': '6', 'F': NZ, 'N': 'B', 'X': DK(4)}, {'%s e. NN0' % NZ: nzn, '%s < %s' % (NZ, P2B): nzlt}, [('4', v, gv)])
    Rn.BND = '( 3 x. ( TMB ` B ) )'
    return Rn.finish(lab, UP('D', '4', EWg(BZ_, DK(4))))


# ------------------------------------------------------------ scY_runs: K = K , bz = G , m = B , r4 = X
K1_ = '( K - 1 )'
KG1 = '( %s x. ( G + 1 ) )' % K1_
EXPY = '( |_ ` ( ( ( ( %s x. G ) + K ) - 1 ) / K ) )' % K1_
Y_ = '( 2 ^ %s )' % EXPY
DATA_SCYY = ((STKD('D'), ('K e. NN', 'G e. NN0', 'B e. NN0')), (('8 <_ B', LT2('( G + 1 )'), LT2('K')), (LT2(KG1), '%s < B' % EXPY)),
             (WG('X'), DEQ(4, EWg('G', 'X'))))
TREE_SCYY = TREE0('scyy', DATA_SCYY)
CONCL_SCYY = TRI(CS('scyy'), CLN('E', S, UP('D', '0', EWg(Y_, DK(0)))), '( 8 x. ( TMB ` B ) )')
add12('tmiscyy', TREE_SCYY, CONCL_SCYY)


def tmiscyy():
    lab = 'tmiscyy'
    T = numtree(TREE_SCYY)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scY_runs ` at the machine: ` y = 2 ^ ( ( ( K - 1 ) bz + K - 1 ) / K ) ` from ` bz ` on 4 (peeked), '
               'pushed on 0; the machine computes the numerator as ` ( K - 1 ) ( bz + 1 ) ` ( ` Ksub_mul ` ) and divides by '
               '` K e. NN ` ( ` divK ` , ~ tmipnvb , ~ tmidivcb ), within ` 8 B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    knn, gn, bn, xg = c0['K e. NN'], c0['G e. NN0'], c0['B e. NN0'], c0[WG('X')]
    kn = s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % ph)
    Rn = ScRun(w, ph, T, 'scyy', {'4': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xg))}, {'K': ('NN', knn), 'G': ('NN0', gn), 'B': ('NN0', bn)},
               [c0[LT2(x)] for x in ('( G + 1 )', 'K', KG1)])
    g = Rn.g
    k1n = s([knn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, K1_))
    Rn.cl.leaf(K1_, 'NN0', k1n)
    Rn.hy.append(s([k1n], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, K1_)))
    Rn.hy.append(s([Rn.cl.mem('K', 'CC'), closed(w, ph, 'ax-1cn', '1 e. CC'), w.inst('npcan')], 'syl2anc', '( %s -> ( %s + 1 ) = K )' % (ph, K1_)))
    v, gv = Rn.ew('G', DK(6), g('6'))
    Rn.call('tmidupb', {'K': '4', 'J': '6', 'I': '1', 'F': 'G', 'N': 'B', 'X': 'X'}, {'G < %s' % P2B: Rn.lt('G')}, [('6', v, gv)])
    G1 = '( G + 1 )'
    v, gv = Rn.ew(G1, DK(6), g('6'))
    Rn.call('tmiincbs', {'K': '6', 'J': '1', 'F': 'G', 'N': 'B', 'X': DK(6)}, {'G < %s' % P2B: Rn.lt('G')}, [('6', v, gv)])
    v, gv = Rn.ew(K1_, DK(1), g('1'))
    Rn.call('tmipnvb', {'K': '1', 'N': K1_, 'B': 'B'}, {'%s e. NN0' % K1_: k1n, '%s < %s' % (K1_, P2B): Rn.lt(K1_)}, [('1', v, gv)])
    Rn.cl.leaf(KG1, 'NN0', s([k1n, Rn.mem(G1), w.inst('nn0mulcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, KG1)))
    v, gv = Rn.ew(KG1, DK(2), g('2'))
    Rn.call('tmimulb', {'K': '1', 'J': '6', 'I': '2', "I'": '3', 'I"': '4', 'F': K1_, 'G': G1, 'N': 'B', 'X': DK(1), 'Y': DK(6)},
            {'%s e. NN0' % K1_: k1n, '%s e. NN0' % G1: Rn.mem(G1), '%s < %s' % (K1_, P2B): Rn.lt(K1_)},
            [('2', v, gv), ('1', DK(1), g('1')), ('6', DK(6), g('6'))])
    v, gv = Rn.ew('K', DK(1), g('1'))
    Rn.call('tmipnvb', {'K': '1', 'N': 'K', 'B': 'B'}, {'K e. NN0': kn}, [('1', v, gv)])
    Q = '( |_ ` ( %s / K ) )' % KG1
    qn = s([Rn.mem(KG1), knn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Q))
    Rn.cl.leaf(Q, 'NN0', qn)
    v, gv = Rn.ew(Q, DK(3), g('3'))
    Rn.call('tmidivcb', {'K': '2', 'J': '1', 'I': '3', "I'": '6', 'I"': '4', 'I0': '5', 'F': KG1, 'G': 'K', 'N': 'B', 'X': DK(2), 'Y': DK(1)},
            {'%s e. NN0' % KG1: Rn.mem(KG1)}, [('2', DK(2), g('2')), ('3', v, gv), ('1', DK(1), g('1'))])
    # the numerator: ( K - 1 ) ( G + 1 ) = ( ( ( K - 1 ) G + K ) - 1 )
    NUM = '( ( ( %s x. G ) + K ) - 1 )' % K1_
    cl2 = Closure(w, ph, {'K': ('NN', knn), 'G': ('NN0', gn)})
    cl2.leaf(K1_, 'NN0', k1n)
    ne = linarith_eq(w, ph, KG1, NUM, [Rn.hy[-1]], cl2, products=True)
    qe = s([s([ne], 'oveq1d', '( %s -> ( %s / K ) = ( %s / K ) )' % (ph, KG1, NUM))], 'fveq2d', '( %s -> %s = %s )' % (ph, Q, EXPY))
    qlt = s([qe, c0['%s < B' % EXPY]], 'eqbrtrd', '( %s -> %s < B )' % (ph, Q))
    TQ = '( 2 ^ %s )' % Q
    tqn = s([closed(w, ph, '2nn0', '2 e. NN0'), qn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, TQ))
    Rn.cl.leaf(TQ, 'NN0', tqn)
    v, gv = Rn.ew(TQ, DK(6), g('6'))
    Rn.call('tmip2b', {'K': '3', 'J': '6', 'I': '1', "I'": '2', 'F': Q, 'N': 'B', 'X': DK(3)}, {'%s < B' % Q: qlt, '%s e. NN0' % Q: qn},
            [('3', DK(3), g('3')), ('6', v, gv)])
    WTQ = '( encNatGam ` %s )' % TQ
    v, gv = Rn.ew(TQ, DK(0), g('0'))
    Rn.call('tmime', {'K': '6', 'J': '0', 'I': '1', 'W': WTQ, 'X': DK(6)}, {WRD(WTQ, BITS): engb(w, ph, TQ, tqn)}, [('6', DK(6), g('6')), ('0', v, gv)])
    Rn.BND = '( 8 x. ( TMB ` B ) )'
    # 2 ^ Q < 2 ^ B (Q < B) for the move
    tlt = exp_lt(w, ph, Q, qn, bn, qlt)
    mc = me_cost(w, ph, TQ, tqn, tlt, Rn.cl)
    rl = {Q: (EXPY, qe)}
    return Rn.finish(lab, UP('D', '0', EWg(Y_, DK(0))), rules=rl, cost=[mc])


# ------------------------------------------------------------ scZ99_runs: z = Z , bz = G , m = B , r4 r5 = X Y
N99 = '( ; 9 9 x. ( G + 1 ) )'
EXP99 = '( |_ ` ( ( ( ; 9 9 x. G ) + ; 9 9 ) / ; ; 1 0 0 ) )'
Z99_ = '( 2 ^ %s )' % EXP99
DATA_SC99 = ((STKD('D'), ('Z e. NN0', 'G e. NN0', 'B e. NN0')), (('8 <_ B', LT2('Z'), LT2('( G + 1 )')), (LT2(N99), '%s < B' % EXP99)),
             ((WG('X'), WG('Y')), (DEQ(4, EWg('G', 'X')), DEQ(5, EWg('Z', 'Y')))))
TREE_SC99 = TREE0('sc99', DATA_SC99)
CONCL_SC99 = TRI(CS('sc99'), CLN('E', S, UPS('D', ('0', EWg('Z', EWg(Z99_, DK(0)))), ('4', 'X'), ('5', 'Y'))), '( 8 x. ( TMB ` B ) )')
add12('tmisc99', TREE_SC99, CONCL_SC99)


def tmisc99():
    lab = 'tmisc99'
    T = numtree(TREE_SC99)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` scZ99_runs ` at the machine: ` z99 = 2 ^ ( ( 99 bz + 99 ) / 100 ) ` from ` bz ` on 4 (consumed), then '
               '` z ` (5, consumed) and ` z99 ` pushed on 0 : ` 0 := z :: z99 :: S 0 ` , within ` 8 B m ` steps.')
    s = w.s
    c0 = Ctx(w, ph, T)
    zn, gn, bn, xg, yg = c0['Z e. NN0'], c0['G e. NN0'], c0['B e. NN0'], c0[WG('X')], c0[WG('Y')]
    eqs = {'4': (EWg('G', 'X'), ewg_(w, ph, 'G', gn, 'X', xg)), '5': (EWg('Z', 'Y'), ewg_(w, ph, 'Z', zn, 'Y', yg))}
    Rn = ScRun(w, ph, T, 'sc99', eqs, {'Z': ('NN0', zn), 'G': ('NN0', gn), 'B': ('NN0', bn)},
               [c0[LT2(x)] for x in ('Z', '( G + 1 )', N99)])
    g = Rn.g
    G1 = '( G + 1 )'
    v, gv = Rn.ew(G1, 'X', xg)
    Rn.call('tmiincbs', {'K': '4', 'J': '1', 'F': 'G', 'N': 'B', 'X': 'X'}, {'G < %s' % P2B: Rn.lt('G')}, [('4', v, gv)])
    N_99, N_100 = '; 9 9', '; ; 1 0 0'
    n99 = s([num.nn0(w, 99)], 'a1i', '( %s -> %s e. NN0 )' % (ph, N_99))
    n100 = s([num.nn0(w, 100)], 'a1i', '( %s -> %s e. NN0 )' % (ph, N_100))
    v, gv = Rn.ew(N_99, DK(1), g('1'))
    Rn.call('tmipnvb', {'K': '1', 'N': N_99, 'B': 'B'}, {'%s e. NN0' % N_99: n99, '%s < %s' % (N_99, P2B): Rn.lt(N_99)}, [('1', v, gv)])
    v, gv = Rn.ew(N99, DK(2), g('2'))
    Rn.call('tmimulb', {'K': '1', 'J': '4', 'I': '2', "I'": '3', 'I"': '6', 'F': N_99, 'G': G1, 'N': 'B', 'X': DK(1), 'Y': 'X'},
            {'%s e. NN0' % N_99: n99, '%s e. NN0' % G1: Rn.mem(G1), '%s < %s' % (N_99, P2B): Rn.lt(N_99)},
            [('2', v, gv), ('1', DK(1), g('1')), ('4', 'X', xg)])
    v, gv = Rn.ew(N_100, DK(1), g('1'))
    Rn.call('tmipnvb', {'K': '1', 'N': N_100, 'B': 'B'}, {'%s e. NN0' % N_100: n100, '%s < %s' % (N_100, P2B): Rn.lt(N_100)}, [('1', v, gv)])
    Q = '( |_ ` ( %s / %s ) )' % (N99, N_100)
    nn100 = s([num.nn(w, 100)], 'a1i', '( %s -> %s e. NN )' % (ph, N_100))
    qn = s([Rn.mem(N99), nn100, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, Q))
    Rn.cl.leaf(Q, 'NN0', qn)
    v, gv = Rn.ew(Q, DK(3), g('3'))
    Rn.call('tmidivcb', {'K': '2', 'J': '1', 'I': '3', "I'": '4', 'I"': '6', 'I0': '5', 'F': N99, 'G': N_100, 'N': 'B', 'X': DK(2), 'Y': DK(1)},
            {'%s e. NN0' % N99: Rn.mem(N99), '%s e. NN' % N_100: nn100, '%s < %s' % (N_100, P2B): Rn.lt(N_100)},
            [('2', DK(2), g('2')), ('3', v, gv), ('1', DK(1), g('1'))])
    NUM = '( ( ; 9 9 x. G ) + ; 9 9 )'
    ne = lineq(w, ph, N99, NUM, closure=Rn.cl)
    qe = s([s([ne], 'oveq1d', '( %s -> ( %s / %s ) = ( %s / %s ) )' % (ph, N99, N_100, NUM, N_100))], 'fveq2d', '( %s -> %s = %s )' % (ph, Q, EXP99))
    qlt = s([qe, c0['%s < B' % EXP99]], 'eqbrtrd', '( %s -> %s < B )' % (ph, Q))
    TQ = '( 2 ^ %s )' % Q
    tqn = s([closed(w, ph, '2nn0', '2 e. NN0'), qn, w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, TQ))
    Rn.cl.leaf(TQ, 'NN0', tqn)
    v, gv = Rn.ew(TQ, DK(6), g('6'))
    Rn.call('tmip2b', {'K': '3', 'J': '6', 'I': '1', "I'": '2', 'F': Q, 'N': 'B', 'X': DK(3)}, {'%s < B' % Q: qlt, '%s e. NN0' % Q: qn},
            [('3', DK(3), g('3')), ('6', v, gv)])
    WTQ = '( encNatGam ` %s )' % TQ
    v0, gv0 = Rn.ew(TQ, DK(0), g('0'))
    Rn.call('tmime', {'K': '6', 'J': '0', 'I': '1', 'W': WTQ, 'X': DK(6)}, {WRD(WTQ, BITS): engb(w, ph, TQ, tqn)}, [('6', DK(6), g('6')), ('0', v0, gv0)])
    WZ = '( encNatGam ` Z )'
    v, gv = Rn.ew('Z', v0, gv0)
    Rn.call('tmime', {'K': '5', 'J': '0', 'I': '1', 'W': WZ, 'X': 'Y'}, {WRD(WZ, BITS): engb(w, ph, 'Z', zn)}, [('5', 'Y', yg), ('0', v, gv)])
    Rn.BND = '( 8 x. ( TMB ` B ) )'
    tlt = exp_lt(w, ph, Q, qn, bn, qlt)
    mc1 = me_cost(w, ph, TQ, tqn, tlt, Rn.cl)
    mc2 = me_cost(w, ph, 'Z', zn, c0[LT2('Z')], Rn.cl)
    return Rn.finish(lab, UPS('D', ('0', EWg('Z', EWg(Z99_, DK(0)))), ('4', 'X'), ('5', 'Y')), rules={Q: (EXP99, qe)}, cost=[mc1, mc2])


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
