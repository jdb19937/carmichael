"""T13: the run lemmas of the searchF assembly: the machine part of each stage, one branch and one callee, stated over
plain class variables for the stack values (no letter equations, no units), so their antecedents are short.

  tmisrc4v   ` branch flag ` at Z3 then ` verifyF ` (~ tm2lbrt , ~ tmiverb ): flag ` ( 1st ( m Verify U ) ) ` , stacks kept
  tmisrc4o   ` branch flag ` at Z4 then ` outputF ` (~ tmiout ): ` initStacks 1 ( encodeOutput m U ) `
  tmisrc3x   ` branch flag ` at Z2 then ` extractF 6 3 0 5 1 2 7 4 ` (~ tmiexfb ): the flag by the extraction's result
  tmisrc2s   ` branch flag ` at Z1 then ` scanF ` (~ tmiscfb ): the flag by the scan's result
  tmisrczs   ` inputF ; scalesF ; step2F ` (~ tmisrpa , ~ tmis2fb ) from ` initStacks 0 ( encNatGam n ) ` at the scale letters

The statements are registered from the Run (the pre class, the post and the cost as the callee gives them) and read back
from the database by the later generators (` stmt ` ).

    MM_DB=sorties/t13.mm python3 tools/gen/t13_d_run.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t13lib import *
from t9lib import STY, accw_g
from t7clib import Run
from t5lib import upeq
import t8alib as A8

SEL = sys.argv[1:]
LMS = P.LMS
FS = P.FS
Z1, Z2, Z3, Z4 = LMS['Z1'], LMS['Z2'], LMS['Z3'], LMS['Z4']
Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11 = [LMS['Y%d' % i] for i in range(4, 12)]
N1 = NFL('1o')
VF2, VF3 = P.VF2, P.VF3
MR, USED, TBL, RIT, WREST, ACCW3 = P.MR, P.USED, P.TBL, P.RIT, P.WREST, P.ACCW3
PRED = FS.pred()
MACH = (T_PHM7, PRED)


def setval(B, k, txt, g):
    """declare the antecedent's equation ( D ` k ) = txt as the base value of stack k"""
    B.S0.vals[k] = (txt, B.c['( D ` %s ) = %s' % (k, txt)], g)
    B.gam[txt] = g


def branch(w, ph, B, R, A, E_, F_):
    """the true branch of ` ( M ` A ) = branch flag ( goto E_ ) ( goto F_ ) ` from the flag class NFL( 1o )"""
    mk = B.mk
    ex = {STMT(GT(F_)): gotocl(w, ph, mk['tv'], F_, B.ex[LAB(F_)]), 'A. m e. %s ( TMfl ` m ) = 1o' % N1: A8.ht_nfl(w, ph, '1o'), SSS(N1): B.ss(N1)}
    B.call(R, 'tm2lbrt', {'A': A, 'C': 'TMfl', 'E': E_, 'Q': GT(F_), 'N': N1}, ex, [])


def register(w, lab, T, R, pre):
    st = TRI(pre, R.cur, R.n)
    add13(lab, T, st)
    return st


# ------------------------------------------------------------ tmisrc4v: branch + verifyF
T_R4V = (MACH, ((STKD('D'), ('A e. Word NN0', 'F e. NN0'), ("B' e. NN0", "N' e. NN0")), (VF2, VF3, (WG('X'), WG('Y'))),
                (DEQ(4, ENCL('A', 'X')), DEQ(7, EWg('F', 'Y')))))


def tmisrc4v():
    lab = 'tmisrc4v'
    T = T_R4V
    ph = cj(T)
    w = W(lab, 'The verify stage\'s machine part: at the third ` branch flag ` with the flag true, ` verifyF ` (~ tmiverb ) '
               'leaves the flag ` ( 1st ( m Verify U ) ) ` and the stacks unchanged, within one step plus its bound.')
    s = w.s
    B = LBase(w, ph, T, 'srch')
    c = B.c
    xg, yg = c[WG('X')], c[WG('Y')]
    g4 = enclg(w, ph, 'A', c['A e. Word NN0'], 'X', xg)
    g7 = ewg_(w, ph, 'F', c['F e. NN0'], 'Y', yg)
    setval(B, '4', ENCL('A', 'X'), g4)
    setval(B, '7', EWg('F', 'Y'), g7)
    R = B.run()
    branch(w, ph, B, R, Z3, Y6, Y9)
    B.call(R, 'tmiverb', {'W': 'A', 'F': 'F', 'B': "B'", 'N': "N'", 'X': 'X', 'Y': 'Y', 'P': PL('P', 9), 'E': Z4}, {}, [], pre=(N1, B.ss(N1)))
    assert R.cur == CLN(Z4, NFL('( 1st ` ( F Verify A ) )'), 'D'), R.cur
    register(w, lab, T, R, CLN(Z3, N1, 'D'))
    qed13(w, R.tri, lab)
    return w.run()


# ------------------------------------------------------------ tmisrc4o: branch + outputF
T_R4O = (MACH, ((STKD('D'), ('A e. Word NN0', 'F e. NN0'), ("B' e. NN0", "N' e. NN0")), ((RALB('A', "B'"), LT2('F', "N'")), (WG('X'), WG('Y'))),
                (DEQ(4, ENCL('A', 'X')), DEQ(7, EWg('F', 'Y')))))


def tmisrc4o():
    lab = 'tmisrc4o'
    T = T_R4O
    ph = cj(T)
    w = W(lab, 'The output leaf\'s machine part: at the fourth ` branch flag ` with the flag true, ` outputF ` (~ tmiout ) '
               'leaves ` initStacks 1 ( encodeOutput m U ) ` within one step plus its bound.')
    s = w.s
    B = LBase(w, ph, T, 'srch')
    c = B.c
    xg, yg = c[WG('X')], c[WG('Y')]
    g4 = enclg(w, ph, 'A', c['A e. Word NN0'], 'X', xg)
    g7 = ewg_(w, ph, 'F', c['F e. NN0'], 'Y', yg)
    setval(B, '4', ENCL('A', 'X'), g4)
    setval(B, '7', EWg('F', 'Y'), g7)
    R = B.run()
    branch(w, ph, B, R, Z4, Y7, Y8)
    # tmiout from C( Y7 , S , D ) : pre shrunk to NFL( 1o ) ; its post is a fresh initStacks, no update chain
    t2, cc2 = inst(w, ph, 'tmiout', {'W': 'A', 'F': 'F', 'B': "B'", 'N': "N'", 'X': 'X', 'Y': 'Y', 'P': PL('P', 10), 'E': 'E', 'D': 'D'}, Bld(w, ph, c, dict(B.ex)))
    C2, D2, n2 = triple_parts(cc2)
    assert C2 == CLN(Y7, S, 'D'), C2
    t2s = hrssc(w, ph, B.mk['phm'], t2, C2, D2, n2, CLN(Y7, N1, 'D'), clnss(w, ph, Y7, N1, S, 'D', B.ss(N1)))
    assert R.cur == CLN(Y7, N1, 'D'), R.cur
    t = hrseq(w, ph, B.mk['phm'], R.tri, t2s, R.C0, R.cur, D2, R.n, n2)
    R.tri, R.cur, R.n = t, D2, '( %s + %s )' % (R.n, n2)
    assert D2 == CLN('E', S, INIT('1', '( F encodeOutput A )')), D2
    register(w, lab, T, R, CLN(Z4, N1, 'D'))
    qed13(w, t, lab)
    return w.run()


# ------------------------------------------------------------ tmisrc3x: branch + extractF
T_R3X = (MACH, ((STKD('D'), ('L e. NN', 'N e. NN0', 'W e. Word NN0'), ("B' e. NN0", LT2('L', "B'"), LT2('N', "B'"))),
                ((RALB('W', "B'"), 'Q e. Word NN0'), (WG('X'), WG("X'")), (WG('Y'), WG('X"'))),
                ((DEQ(6, ENCL('W', 'X')), DEQ(3, EWg('L', "X'"))), (DEQ(5, '(/)'), DEQ(7, EWg('N', 'Y'))), DEQ(4, ENCL('Q', 'X"')))))


def tmisrc3x():
    lab = 'tmisrc3x'
    T = T_R3X
    ph = cj(T)
    w = W(lab, 'The extract stage\'s machine part: at the second ` branch flag ` with the flag true, ` extractF 6 3 0 5 1 2 7 4 ` '
               '(~ tmiexfb ) leaves the flag by the extraction\'s result and the rest of the pool, the table word, the candidate '
               'and the witness list on the stacks 6 5 7 4, within one step plus its bound.')
    s = w.s
    B = LBase(w, ph, T, 'srch')
    c = B.c
    lnn, nn, ww, qw = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0'], c['Q e. Word NN0']
    xg, x1g, yg, x2g = c[WG('X')], c[WG("X'")], c[WG('Y')], c[WG('X"')]
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    g6 = enclg(w, ph, 'W', ww, 'X', xg)
    g3 = ewg_(w, ph, 'L', s([lnn], 'nnnn0d', '( %s -> L e. NN0 )' % ph), "X'", x1g)
    g7 = ewg_(w, ph, 'N', nn, 'Y', yg)
    g4 = enclg(w, ph, 'Q', qw, 'X"', x2g)
    setval(B, '6', ENCL('W', 'X'), g6); setval(B, '3', EWg('L', "X'"), g3); setval(B, '5', '(/)', wrd0)
    setval(B, '7', EWg('N', 'Y'), g7); setval(B, '4', ENCL('Q', 'X"'), g4)
    R = B.run()
    branch(w, ph, B, R, Z2, Y5, Y10)
    # the extraction's post words
    z0 = P.z0_in_sty(w, ph)
    Z0 = P.Z0
    cl = Closure(w, ph, {'N': ('NN0', nn)})
    cl.leaf('L', 'NN0', s([lnn], 'nnnn0d', '( %s -> L e. NN0 )' % ph))
    j = s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0, STY))], 'jca',
          '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (ph, Z0, STY))
    ritp = s([j, w.inst('exitp')], 'syl', '( %s -> %s )' % (ph, tsub_text(split_imp(stmt('exitp'))[1], {'G': 'N', 'Z': Z0})))
    rin = s([ritp], 'simp1d', '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (ph, RIT))
    mrn, usedw, tblt, hit2 = P.sq_comps(w, ph, cl, lnn, nn, ww, z0, RIT, rin)
    wrestw = s([ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, WREST))
    V6 = ENCL(WREST, 'X')
    V5 = ACCW3
    V7 = EWg(MR, EWg('N', 'Y'))
    V4 = ENCL(USED, ENCL('Q', 'X"'))
    gg6 = B.g(V6, enclg(w, ph, WREST, wrestw, 'X', xg))
    gg5 = B.g(V5, accw_g(w, ph, TBL, tblt, 'L', cl.mem('L', 'NN0')))
    gg7 = B.g(V7, ewg_(w, ph, MR, mrn, EWg('N', 'Y'), g7))
    gg4 = B.g(V4, enclg(w, ph, USED, usedw, ENCL('Q', 'X"'), g4))
    B.call(R, 'tmiexfb', {'K': '6', 'J': '3', 'I': '0', "I'": '5', 'I"': '1', 'I0': '2', 'K0': '7', 'J0': '4', 'L': 'L', 'G': 'N', 'W': 'W', 'B': "B'",
                          'X': 'X', "X'": "X'", 'Y': 'Y', 'P': PL('P', 8), 'E': Z3},
           {}, [('6', V6, gg6), ('5', V5, gg5), ('7', V7, gg7), ('4', V4, gg4)], pre=(N1, B.ss(N1)))
    XL = '( 1st ` ( ( L Extract N ) ` W ) )'
    assert R.cur.startswith(CLN(Z3, NFL('if ( %s = %s , (/) , 1o )' % (XL, INR)), '')[:-len(' X. { } ) )')]), R.cur[:300]
    register(w, lab, T, R, CLN(Z2, N1, 'D'))
    qed13(w, R.tri, lab)
    return w.run()


# ------------------------------------------------------------ tmisrc2s: branch + scanF
SCAN = P.SCAN
KSC, PSC = P.KSC, P.PSC
NONE = '( 1st ` %s ) = %s' % (SCAN, INR)
T_R2S = (MACH, (((STKD('D'), 'Q e. Word NN0', ('X e. NN0', 'Z e. NN0', 'O e. NN0')),
                 ("B' e. NN0", (RALB('Q', "B'"), 'A. a e. ran Q 1 <_ a'), ((LT2('X', "B'"), LT2('Z', "B'")), (LT2('O', "B'"), "( 1 + X ) < ( 2 ^ B' )")))),
                (((WG('R'), WG("X'")), (WG('Y'), WG("Y'"))),
                 ((DEQ(0, EWg('X', EWg('O', 'R'))), DEQ(1, EWg('Z', EWg('X', "X'")))), (DEQ(2, EWg('1', 'Y')), DEQ(4, ENCL('Q', "Y'")))))))


def tmisrc2s():
    lab = 'tmisrc2s'
    T = T_R2S
    ph = cj(T)
    w = W(lab, 'The scan stage\'s machine part: at the first ` branch flag ` with the flag true, ` scanF ` (~ tmiscfb , T11) '
               'leaves the flag by the scan\'s result, ` z ` alone on stack 1, ` k\' ` on 2 and the pool on 6 when it found a '
               'window (` 1 + x ` on 2 otherwise), within one step plus its bound.')
    s = w.s
    B = LBase(w, ph, T, 'srch')
    c = B.c
    qw, xn, zn, on, bn = c['Q e. Word NN0'], c['X e. NN0'], c['Z e. NN0'], c['O e. NN0'], c["B' e. NN0"]
    rg, x1g, yg, y1g = c[WG('R')], c[WG("X'")], c[WG('Y')], c[WG("Y'")]
    one = closed(w, ph, '1nn0', '1 e. NN0')
    g0 = ewg_(w, ph, 'X', xn, EWg('O', 'R'), ewg_(w, ph, 'O', on, 'R', rg))
    g1 = ewg_(w, ph, 'Z', zn, EWg('X', "X'"), ewg_(w, ph, 'X', xn, "X'", x1g))
    g2 = ewg_(w, ph, '1', one, 'Y', yg)
    g4 = enclg(w, ph, 'Q', qw, "Y'", y1g)
    setval(B, '0', EWg('X', EWg('O', 'R')), g0); setval(B, '1', EWg('Z', EWg('X', "X'")), g1)
    setval(B, '2', EWg('1', 'Y'), g2); setval(B, '4', ENCL('Q', "Y'"), g4)
    deep2(B, 'srch', 3, 2)                 # the scan's entry label ( ( ( P ` 7 ) ` 2 ) ` 0 )
    R = B.run()
    branch(w, ph, B, R, Z1, Y4, Y11)
    X1 = '( 1 + X )'
    x1n = s([one, xn], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, X1))
    IF2 = 'if ( %s , %s , %s )' % (NONE, EWg(X1, 'Y'), EWg(KSC, 'Y'))
    IF6 = 'if ( %s , ( D ` 6 ) , %s )' % (NONE, ENCL(PSC, '( D ` 6 )'))
    gx1 = ewg_(w, ph, X1, x1n, 'Y', yg)
    # the some case gives k' e. NN0 and the pool a word (~ scandj )
    pj = '( %s /\\ -. %s )' % (ph, NONE)
    Lj = lambda st_: s([st_], 'adantr', '( %s -> %s )' % (pj, concl(w, ph, st_)))
    jq1 = s([Lj(qw), Lj(xn)], 'jca', '( %s -> ( Q e. Word NN0 /\\ X e. NN0 ) )' % pj)
    jq2 = s([jq1, Lj(zn)], 'jca', '( %s -> ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % pj)
    jq3 = s([jq2, Lj(on)], 'jca', '( %s -> ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % pj)
    jq4 = s([closed(w, pj, '1nn0', '1 e. NN0'), Lj(xn)], 'jca', '( %s -> ( 1 e. NN0 /\\ X e. NN0 ) )' % pj)
    jn1 = s([jq3, jq4], 'jca', '( %s -> ( ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( 1 e. NN0 /\\ X e. NN0 ) ) )' % pj)
    jne_ = s([s([], 'simpr', '( %s -> -. %s )' % (pj, NONE))], 'neqned', '( %s -> ( 1st ` %s ) =/= %s )' % (pj, SCAN, INR))
    dj = s([s([jn1, jne_], 'jca', '( %s -> ( %s /\\ ( 1st ` %s ) =/= %s ) )' % (pj, concl(w, pj, jn1), SCAN, INR)), w.inst('scandj')], 'syl',
           '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (pj, KSC, PSC))
    kn_j = s([dj], 'simpld', '( %s -> %s e. NN0 )' % (pj, KSC))
    pw_j = s([dj], 'simprd', '( %s -> %s e. Word NN0 )' % (pj, PSC))
    pt = '( %s /\\ %s )' % (ph, NONE)
    i2t = s([s([s([], 'simpr', '( %s -> %s )' % (pt, NONE))], 'iftrued', '( %s -> %s = %s )' % (pt, IF2, EWg(X1, 'Y'))), s([gx1], 'adantr', "( %s -> %s e. Word Gamma' )" % (pt, EWg(X1, 'Y')))],
            'eqeltrd', "( %s -> %s e. Word Gamma' )" % (pt, IF2))
    i2f = s([s([s([], 'simpr', '( %s -> -. %s )' % (pj, NONE))], 'iffalsed', '( %s -> %s = %s )' % (pj, IF2, EWg(KSC, 'Y'))), ewg_(w, pj, KSC, kn_j, 'Y', Lj(yg))],
            'eqeltrd', "( %s -> %s e. Word Gamma' )" % (pj, IF2))
    g2i = s([i2t, i2f], 'pm2.61dan', "( %s -> %s e. Word Gamma' )" % (ph, IF2))
    d6g = B.S0.vals['6'][2]
    i6t = s([s([s([], 'simpr', '( %s -> %s )' % (pt, NONE))], 'iftrued', '( %s -> %s = ( D ` 6 ) )' % (pt, IF6)), s([d6g], 'adantr', "( %s -> ( D ` 6 ) e. Word Gamma' )" % pt)], 'eqeltrd',
            "( %s -> %s e. Word Gamma' )" % (pt, IF6))
    i6f = s([s([s([], 'simpr', '( %s -> -. %s )' % (pj, NONE))], 'iffalsed', '( %s -> %s = %s )' % (pj, IF6, ENCL(PSC, '( D ` 6 )'))), enclg(w, pj, PSC, pw_j, '( D ` 6 )', Lj(d6g))],
            'eqeltrd', "( %s -> %s e. Word Gamma' )" % (pj, IF6))
    g6i = s([i6t, i6f], 'pm2.61dan', "( %s -> %s e. Word Gamma' )" % (ph, IF6))
    gz1 = ewg_(w, ph, 'Z', zn, "X'", x1g)
    B.g(EWg('Z', "X'"), gz1); B.g(IF2, g2i); B.g(IF6, g6i)
    B.call(R, 'tmiscfb', {'W': 'Q', 'F': 'X', 'Z': 'Z', 'O': 'O', 'G': '1', 'H': 'X', 'C': "B'", 'B': "B'", 'X': 'R', "X'": "X'", 'Y': 'Y', "Y'": "Y'", 'P': PL('P', 7), 'E': Z2},
           {'1 e. NN0': one}, [('1', EWg('Z', "X'"), gz1), ('2', IF2, g2i), ('6', IF6, g6i)], pre=(N1, B.ss(N1)))
    assert R.cur.startswith(CLN(Z2, NFL('if ( %s , (/) , 1o )' % NONE), '')[:-len(' X. { } ) )')]), R.cur[:300]
    register(w, lab, T, R, CLN(Z1, N1, 'D'))
    qed13(w, R.tri, lab)
    return w.run()


# ------------------------------------------------------------ tmisrczs: inputF ; scalesF ; step2F
SCEQ5 = (('Z = %s' % PZ(SC_), 'G = %s' % PZ99(SC_)), ('Y = %s' % PY(SC_), 'U = %s' % PT(SC_), 'O = %s' % PTH(SC_)))
BH = '( B + H )'
T_RZ = (MACH, (((('C e. NN0', 'K e. NN', 'N e. NN0'), ('B e. NN0', 'H e. NN0', '2 <_ B')),
                (('Z e. NN', 'G e. NN0', 'Y e. NN'), ('U e. NN0', 'O e. NN0'))),
               (((LT2('Z'), LT2('G'), LT2('Y')), (LT2('U'), LT2('N', BH)), (LT2('C', BH), LT2('K', BH))), SCEQ5)))
W0, W7, INIT7 = P.W0, P.W7, P.INIT7
SCALESL = EWg('Z', EWg('G', EWg('Y', EWg('U', EWg('O', '(/)')))))
RES = '( ( Z Reservoir G ) ` Y )'
IRES = '( # ` ( 1st ` %s ) )' % RES
LTU = '%s < U' % IRES


def tmisrczs():
    lab = 'tmisrczs'
    T = T_RZ
    ph = cj(T)
    w = W(lab, 'The prefix of Lean\'s ` searchF ` at the machine through step 2: ` inputF ; scalesF ` (~ tmisrpa at the bit '
               'bound ` bs + bn ` ) then ` step2F ` (~ tmis2fb , T10) at the scale letters, from ` initStacks 0 ( encNatGam n ) ` '
               'to the first ` branch flag ` with the flag ` len < T ` and the stacks of ~ tmis2fb .')
    s = w.s
    c, mk, ne, ex = setup_light(w, ph, T, PRED, 'srch')
    cn, knn, nn, bn, hn = c['C e. NN0'], c['K e. NN'], c['N e. NN0'], c['B e. NN0'], c['H e. NN0']
    zn, gn, yn, un, on = c['Z e. NN'], c['G e. NN0'], c['Y e. NN'], c['U e. NN0'], c['O e. NN0']
    bhn = s([bn, hn], 'nn0addcld', '( %s -> %s e. NN0 )' % (ph, BH))
    # 1. inputF ; scalesF at B := B + H
    t1, cc1 = inst(w, ph, 'tmisrpa', {'B': BH}, Bld(w, ph, c, dict(ex, **{'%s e. NN0' % BH: bhn})))
    C1, D1, n1 = triple_parts(cc1)
    assert C1 == SRCHPRE, C1
    D1s = triple_D(D1)
    assert D1s == UP(INIT7, '0', P.SCALES), D1s
    # the scales at the letters
    rules = {PZ(SC_): ('Z', s([c['Z = %s' % PZ(SC_)]], 'eqcomd', '( %s -> %s = Z )' % (ph, PZ(SC_)))),
             PZ99(SC_): ('G', s([c['G = %s' % PZ99(SC_)]], 'eqcomd', '( %s -> %s = G )' % (ph, PZ99(SC_)))),
             PY(SC_): ('Y', s([c['Y = %s' % PY(SC_)]], 'eqcomd', '( %s -> %s = Y )' % (ph, PY(SC_)))),
             PT(SC_): ('U', s([c['U = %s' % PT(SC_)]], 'eqcomd', '( %s -> %s = U )' % (ph, PT(SC_)))),
             PTH(SC_): ('O', s([c['O = %s' % PTH(SC_)]], 'eqcomd', '( %s -> %s = O )' % (ph, PTH(SC_))))}
    rs, new = w.rewrite(P.SCALES, rules, ph)
    assert new == SCALESL, new
    deq = upeq(w, ph, INIT7, '0', rs, P.SCALES, SCALESL)
    t1, _, D1b, _ = hrrw(w, ph, t1, C1, D1, n1, deq=clneq(w, ph, LMS['Y3'], S, deq, D1s, UP(INIT7, '0', SCALESL)))
    # the stacks: INIT7 updated at 0
    w0g = encw(w, ph, 'N', nn)
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    w7g = wgcat(w, ph, W0, '<" 4 ">', w0g, s4)
    S7 = P.init_stacks(w, ph, mk, ne, '7', W7, w7g)
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    zn0 = s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)
    yn0 = s([yn], 'nnnn0d', '( %s -> Y e. NN0 )' % ph)
    gS = ewg_(w, ph, 'Z', zn0, EWg('G', EWg('Y', EWg('U', EWg('O', '(/)')))),
              ewg_(w, ph, 'G', gn, EWg('Y', EWg('U', EWg('O', '(/)'))),
                   ewg_(w, ph, 'Y', yn0, EWg('U', EWg('O', '(/)')), ewg_(w, ph, 'U', un, EWg('O', '(/)'), ewg_(w, ph, 'O', on, '(/)', wrd0)))))
    S0 = S7.upd('0', SCALESL, gS)
    assert S0.D == UP(INIT7, '0', SCALESL), S0.D
    B = P.IBase(w, ph, c, mk, ne, ex, S7)
    B.g('(/)', wrd0); B.g(SCALESL, gS)
    R = B.run()
    R.S = S0; R.chain = [('0', SCALESL)]; R.gam[SCALESL] = gS      # the base is INIT7: the two updates at 0 merge
    # 2. step2F : the typing of the reservoir's pieces for the if-words
    rcl = s([s([zn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), yn, w.inst('reservoircl')], 'syl2anc', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, RES))
    r1 = s([rcl, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` %s ) e. Word NN0 )' % (ph, RES))
    ir = s([r1, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, IRES))
    QQ = '( ( 1st ` %s ) substr <. ( %s - U ) , %s >. )' % (RES, IRES, IRES)
    qq = s([r1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, QQ))
    LL = '( 1st ` ( ProdL ` %s ) )' % QQ
    ll = s([s([qq, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` %s ) e. ( NN0 X. NN0 ) )' % (ph, QQ)), w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, LL))
    XX = '( %s ^ 5 )' % LL
    xx = s([ll, closed(w, ph, '5nn0', '5 e. NN0')], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, XX))
    one = closed(w, ph, '1nn0', '1 e. NN0')
    E_O = EWg('O', '(/)')
    go = ewg_(w, ph, 'O', on, '(/)', wrd0)
    IF0 = 'if ( %s , %s , %s )' % (LTU, EWg('U', E_O), EWg(XX, E_O))
    IF1 = 'if ( %s , %s , %s )' % (LTU, EWg('Z', '(/)'), EWg('Z', EWg(XX, '(/)')))
    IF2 = 'if ( %s , %s , %s )' % (LTU, EWg(IRES, '(/)'), EWg('1', '(/)'))
    IF3 = 'if ( %s , (/) , %s )' % (LTU, EWg(LL, '(/)'))
    IF4 = 'if ( %s , %s , %s )' % (LTU, ENCL('( 1st ` %s )' % RES, '(/)'), ENCL(QQ, '(/)'))
    def ifg(IF, a, b):
        return s([a, b], 'ifcld', "( %s -> %s e. Word Gamma' )" % (ph, IF))
    g0 = ifg(IF0, ewg_(w, ph, 'U', un, E_O, go), ewg_(w, ph, XX, xx, E_O, go))
    g1 = ifg(IF1, ewg_(w, ph, 'Z', zn0, '(/)', wrd0), ewg_(w, ph, 'Z', zn0, EWg(XX, '(/)'), ewg_(w, ph, XX, xx, '(/)', wrd0)))
    g2 = ifg(IF2, ewg_(w, ph, IRES, ir, '(/)', wrd0), ewg_(w, ph, '1', one, '(/)', wrd0))
    g3 = ifg(IF3, wrd0, ewg_(w, ph, LL, ll, '(/)', wrd0))
    g4 = ifg(IF4, enclg(w, ph, '( 1st ` %s )' % RES, r1, '(/)', wrd0), enclg(w, ph, QQ, qq, '(/)', wrd0))
    B.call(R, 'tmis2fb', {'Z': 'Z', 'G': 'G', 'Y': 'Y', 'U': 'U', 'O': 'O', 'B': 'B', 'R': '(/)', 'P': PL('P', 6), 'E': Z1},
           {WG('(/)'): wrd0}, [('0', IF0, g0), ('1', IF1, g1), ('2', IF2, g2), ('3', IF3, g3), ('4', IF4, g4)])
    cur, out = R.normalize(N8)
    assert [k for k, v in out] == ['0', '1', '2', '3', '4'], out
    t = hrseq(w, ph, mk['phm'], t1, R.tri, C1, D1b, R.cur, n1, R.n)
    R.tri, R.C0, R.n = t, C1, '( %s + %s )' % (n1, R.n)
    assert R.cur.startswith(CLN(Z1, NFL('if ( %s , (/) , 1o )' % LTU), '')[:-len(' X. { } ) )')]), R.cur[:300]
    register(w, lab, T, R, SRCHPRE)
    qed13(w, t, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
