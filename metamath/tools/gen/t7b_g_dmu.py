"""T7b: the composite triples of the division loops at the machine.

  tmidmub   dmUpBody's calls ` incr j s ; dup y t s ; dup x s t ; cmpFrag t s `
            (from the entry of ` incr ` to the exit), on TMIdmu

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_g_dmu.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from lin import linarith
from t7_e_cmp import machine
from t7b_c_runs import runs_stmt
from t7b_e_froms import froms_stmt

SEL = sys.argv[1:]

K5 = ['K', 'J', "I'", 'I"', 'I0']
ENC = lambda t: '( encodeNat ` %s )' % t
ENG = lambda t: '( encNatGam ` %s )' % t
YX = lambda X: '( <" 4 "> ++ %s )' % X
MXLL = "if ( ( # ` L' ) <_ ( # ` L ) , ( # ` L ) , ( # ` L' ) )"
BND_UB = ("( ( ( ( 2 x. ( # ` %s ) ) + 3 ) + ( ( 2 x. ( # ` L' ) ) + 5 ) ) + ( ( ( 2 x. ( # ` L ) ) + 5 ) + ( %s + 2 ) ) )"
          % (ENC('C'), MXLL))
NCM = "{ h e. TMSt | ( TMcmp ` h ) = ( ( toNat ` L' ) Ncmp ( toNat ` L ) ) }"
DATA_UB = ((('C e. NN0', WRD('L', '2o'), WRD("L'", '2o')), (WRD('X', GAM), WRD('Y', GAM), WRD('Q', GAM)), STKD('D')),
           ('( D ` K ) = %s' % CC('( inclBool o. L )', YX('X')), "( D ` J ) = %s" % CC("( inclBool o. L' )", YX('Y')),
            "( D ` I' ) = %s" % CC(ENG('C'), YX('Q'))))


def STMT_UB():
    f = FRAGS['dmu']
    tree = ((T_PHM7, f.pred()), (idx_tree(K5), dist_tree(K5)), DATA_UB)
    post = UP('D', "I'", CC(ENG('( C + 1 )'), YX('Q')))
    return tree, TRI(CLN(PL(PL('P', 1), 0), SS, 'D'), CLN('E', NCM, post), BND_UB)


def apply(w, ph, lab, m, c, extra, stmt_fn):
    """( ph -> concl ) by the database theorem lab at the substitution m, its antecedent
    rebuilt from the Ctx c and the extra leaves"""
    bld = Bld(w, ph, c, extra)
    return inst(w, ph, lab, m, bld)


def tmidmub():
    lab = 'tmidmub'
    T, C = STMT_UB()
    ph = cj(T)
    w = W(lab, 'The calls of Lean\'s ` dmUpBody x y j s t ` after its push, ` incr j s ; dup y t s ; dup x s t ; '
               'cmpFrag t s ` , wherever ` dmUpBody ` is installed: the counter on ` j ` is incremented, ` cmp ` '
               'compares the shifted divisor on ` y ` with the dividend on ` x ` , and ` t ` , ` s ` are restored.')
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K5)
    phm, tv = mk['phm'], mk['tv']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K5))))
    f = FRAGS['dmu']
    un = unfold_all(w, ph, c[f.pred()], 'dmu', K5, 'P', 'E', rec=False)
    base = {PHM: phm, 'T e. V': tv, MTY: mk['mt']}
    cn = c['C e. NN0']; ll = c[WRD('L', '2o')]; ll2 = c[WRD("L'", '2o')]
    xg, yg, qg = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[WRD('Q', GAM)]
    dd = c[STKD('D')]
    # the initial stacks
    def selfv(s):
        return (('( D ` %s )' % s), w.s([], 'eqidd', '( %s -> ( D ` %s ) = ( D ` %s ) )' % (ph, s, s)),
                w.s([stkfv(w, ph, 'D', s, tv, dd, mk['k'][s]['kd']), mk['k'][s]['wge']], 'eleqtrd',
                    "( %s -> ( D ` %s ) e. Word Gamma' )" % (ph, s)))
    WX, WY = CC('( inclBool o. L )', YX('X')), CC("( inclBool o. L' )", YX('Y'))
    ec = w.s([cn, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, ENC('C')))
    egv = w.s([cn, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. %s ) )' % (ph, ENG('C'), ENC('C')))
    WJ = CC('( inclBool o. %s )' % ENC('C'), YX('Q'))
    dj0 = w.s([c["( D ` I' ) = %s" % CC(ENG('C'), YX('Q'))], w.s([egv], 'oveq1d', '( %s -> ( %s ++ %s ) = %s )' % (ph, ENG('C'), YX('Q'), WJ))],
              'eqtrd', "( %s -> ( D ` I' ) = %s )" % (ph, WJ))
    vals = {'K': (WX, c['( D ` K ) = %s' % WX], wgcat(w, ph, '( inclBool o. L )', YX('X'), wib(w, ph, 'L', ll), wg4(w, ph, 'X', xg))),
            'J': (WY, c["( D ` J ) = %s" % WY], wgcat(w, ph, "( inclBool o. L' )", YX('Y'), wib(w, ph, "L'", ll2), wg4(w, ph, 'Y', yg))),
            "I'": (WJ, dj0, wgcat(w, ph, '( inclBool o. %s )' % ENC('C'), YX('Q'), wib(w, ph, ENC('C'), ec), wg4(w, ph, 'Q', qg))),
            'I"': selfv('I"'), 'I0': selfv('I0')}
    S0 = Stacks(w, ph, mk, 'D', dd, ne, vals)
    # ---- incr j s
    P1, E1 = PL('P', 1), PL(PL('P', 2), 0)
    m1 = {'K': "I'", 'J': 'I"', 'P': P1, 'E': E1, 'L': ENC('C'), 'X': 'Q', 'D': 'D'}
    ex1 = dict(base); ex1.update(un)
    ex1.update({IDX("I'"): c[IDX("I'")], IDX('I"'): c[IDX('I"')], "I' =/= I\"": ne("I'", 'I"'),
                WRD(ENC('C'), '2o'): ec, "( D ` I' ) = %s" % WJ: dj0})
    t1, c1 = apply(w, ph, 'tmiincs', m1, c, ex1, None)
    Ca, Da, n1 = triple_parts(c1)
    WINC = CC('( inclBool o. ( incBits ` %s ) )' % ENC('C'), YX('Q'))
    ibw = w.s([w.s([ec, w.inst('incbitscl')], 'syl', '( %s -> ( incBits ` %s ) e. Word 2o )' % (ph, ENC('C')))], 'id' if False else 'bwmapcl',
              "( %s -> ( inclBool o. ( incBits ` %s ) ) e. Word Gamma' )" % (ph, ENC('C'))) if False else None
    icw = w.s([ec, w.inst('incbitscl')], 'syl', '( %s -> ( incBits ` %s ) e. Word 2o )' % (ph, ENC('C')))
    S1 = S0.upd("I'", WINC, wgcat(w, ph, '( inclBool o. ( incBits ` %s ) )' % ENC('C'), YX('Q'), wib(w, ph, '( incBits ` %s )' % ENC('C'), icw), wg4(w, ph, 'Q', qg)))
    assert Da == CLN(E1, SS, S1.D), (Da, S1.D)
    # ---- dup y t s at S1
    P2, E2 = PL('P', 2), PL(PL('P', 3), 0)
    WL2 = "( inclBool o. L' )"
    ib2 = w.s([ll2, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, WL2, BITS))
    m2 = {'K': 'J', 'J': 'I0', 'I': 'I"', 'P': P2, 'E': E2, 'W': WL2, 'X': 'Y', 'D': S1.D}
    ex2 = dict(base); ex2.update(un)
    ex2.update({IDX('J'): c[IDX('J')], IDX('I0'): c[IDX('I0')], IDX('I"'): c[IDX('I"')],
                'J =/= I0': ne('J', 'I0'), 'J =/= I"': ne('J', 'I"'), 'I0 =/= I"': ne('I0', 'I"'),
                WRD(WL2, BITS): ib2, STKD(S1.D): S1.memb, '( %s ` J ) = %s' % (S1.D, WY): S1.val('J')[1]})
    t2, c2 = apply(w, ph, 'tmidup', m2, c, ex2, None)
    Cb, Db, n2 = triple_parts(c2)
    R0 = '( %s ` I0 )' % S1.D
    r0g = w.s([stkfv(w, ph, S1.D, 'I0', tv, S1.memb, mk['k']['I0']['kd']), mk['k']['I0']['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, R0))
    WT = CC(WL2, YX(R0))
    S2 = S1.upd('I0', WT, wgcat(w, ph, WL2, YX(R0), wib(w, ph, "L'", ll2), wg4(w, ph, R0, r0g)))
    assert Db == CLN(E2, SS, S2.D), (Db, S2.D)
    # ---- dup x s t at S2
    P3, E3 = PL('P', 3), PL(PL('P', 4), 0)
    WL1 = '( inclBool o. L )'
    ib1 = w.s([ll, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, WL1, BITS))
    m3 = {'K': 'K', 'J': 'I"', 'I': 'I0', 'P': P3, 'E': E3, 'W': WL1, 'X': 'X', 'D': S2.D}
    ex3 = dict(base); ex3.update(un)
    ex3.update({IDX('K'): c[IDX('K')], IDX('I0'): c[IDX('I0')], IDX('I"'): c[IDX('I"')],
                'K =/= I"': ne('K', 'I"'), 'K =/= I0': ne('K', 'I0'), 'I" =/= I0': ne('I"', 'I0'),
                WRD(WL1, BITS): ib1, STKD(S2.D): S2.memb, '( %s ` K ) = %s' % (S2.D, WX): S2.val('K')[1]})
    t3, c3 = apply(w, ph, 'tmidup', m3, c, ex3, None)
    Cc_, Dc_, n3 = triple_parts(c3)
    R1 = '( %s ` I" )' % S2.D
    r1g = w.s([stkfv(w, ph, S2.D, 'I"', tv, S2.memb, mk['k']['I"']['kd']), mk['k']['I"']['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, R1))
    WS = CC(WL1, YX(R1))
    S3 = S2.upd('I"', WS, wgcat(w, ph, WL1, YX(R1), wib(w, ph, 'L', ll), wg4(w, ph, R1, r1g)))
    assert Dc_ == CLN(E3, SS, S3.D), (Dc_, S3.D)
    # ---- cmpFrag t s at S3
    P4 = PL('P', 4)
    m4 = {'K': 'I0', 'J': 'I"', 'P': P4, 'E': 'E', 'L': "L'", "L'": 'L', 'X': R0, 'Y': R1, 'D': S3.D}
    ex4 = dict(base); ex4.update(un)
    ex4.update({IDX('I0'): c[IDX('I0')], IDX('I"'): c[IDX('I"')], 'I0 =/= I"': ne('I0', 'I"'),
                WRD(R0, GAM): r0g, WRD(R1, GAM): r1g, STKD(S3.D): S3.memb,
                '( %s ` I0 ) = %s' % (S3.D, CC(WL2, YX(R0))): S3.val('I0')[1],
                '( %s ` I" ) = %s' % (S3.D, CC(WL1, YX(R1))): S3.val('I"')[1]})
    t4, c4 = apply(w, ph, 'tmicmp', m4, c, ex4, None)
    Cd, Dd, n4 = triple_parts(c4)
    # ---- sequence
    t12 = hrseq(w, ph, phm, t1, t2, Ca, Da, Db, n1, n2)
    t123 = hrseq(w, ph, phm, t12, t3, Ca, Db, Dc_, '( %s + %s )' % (n1, n2), n3)
    NN = '( ( %s + %s ) + %s )' % (n1, n2, n3)
    t1234 = hrseq(w, ph, phm, t123, t4, Ca, Dc_, Dd, NN, n4)
    NT = '( %s + %s )' % (NN, n4)
    # ---- the stacks: D4 = UPD( UPD( S3 , I0 , R0 ) , I" , R1 ) = UPD( D , I' , WINC )
    D4 = UP(UP(S3.D, 'I0', R0), 'I"', R1)
    assert Dd == CLN('E', NCM, D4), Dd
    kI0, kI2 = mk['k']['I0'], mk['k']['I"']
    togk = lambda X, s, g: w.s([g, mk['k'][s]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s)))
    u4 = up4(w, ph, S1.D, 'I0', WT, 'I"', WS, R0, R1, tv, S1.memb, ne('I0', 'I"'), kI0['kd'],
             togk(WT, 'I0', S2.vals['I0'][2]), togk(R0, 'I0', r0g), kI2['kd'], togk(WS, 'I"', S3.vals['I"'][2]), togk(R1, 'I"', r1g))
    # UPD( S1 , I0 , R0 ) = S1
    ui = upid(w, ph, S1.D, 'I0', tv, S1.memb, kI0['kd'])
    r_, newp = w.rewrite(UP(UP(S1.D, 'I0', R0), 'I"', R1), {UP(S1.D, 'I0', R0): (S1.D, ui)}, ph)
    assert newp == UP(S1.D, 'I"', R1), newp
    # R1 = ( S2 ` I" ) = ( S1 ` I" )
    r1v = updnv(w, ph, S1.D, 'I0', WT, 'I"', tv, S1.memb, kI0['kd'], w.s([S2.vals['I0'][2]], 'elexd', '( %s -> %s e. _V )' % (ph, WT)),
                kI2['kd'], ne('I"', 'I0'))
    uv = upidv(w, ph, S1.D, 'I"', R1, w.s([r1v], 'eqcomd', '( %s -> ( %s ` I" ) = %s )' % (ph, S1.D, R1)), tv, S1.memb, kI2['kd'])
    deq0 = w.s([w.s([u4, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D4, UP(S1.D, 'I"', R1))), uv], 'eqtrd', '( %s -> %s = %s )' % (ph, D4, S1.D))
    # S1 = UPD( D , I' , WINC ) -> UPD( D , I' , encNatGam ( C + 1 ) ++ ... )
    es = w.s([cn, w.inst('encnatsuc')], 'syl', '( %s -> ( encodeNat ` ( C + 1 ) ) = ( incBits ` %s ) )' % (ph, ENC('C')))
    c1n = w.s([cn, w.inst('peano2nn0')], 'syl', '( %s -> ( C + 1 ) e. NN0 )' % ph)
    eg1 = w.s([c1n, w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. ( encodeNat ` ( C + 1 ) ) ) )' % (ph, ENG('( C + 1 )')))
    eg2 = w.s([eg1, w.s([es], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` ( C + 1 ) ) ) = ( inclBool o. ( incBits ` %s ) ) )' % (ph, ENC('C')))],
              'eqtrd', '( %s -> %s = ( inclBool o. ( incBits ` %s ) ) )' % (ph, ENG('( C + 1 )'), ENC('C')))
    w3 = w.s([eg2], 'oveq1d', '( %s -> %s = %s )' % (ph, CC(ENG('( C + 1 )'), YX('Q')), WINC))
    ue = upeq(w, ph, 'D', "I'", w.s([w3], 'eqcomd', '( %s -> %s = %s )' % (ph, WINC, CC(ENG('( C + 1 )'), YX('Q')))), WINC, CC(ENG('( C + 1 )'), YX('Q')))
    POST = UP('D', "I'", CC(ENG('( C + 1 )'), YX('Q')))
    deq = w.s([deq0, ue], 'eqtrd', '( %s -> %s = %s )' % (ph, D4, POST))
    deqc = clneq(w, ph, 'E', NCM, deq, D4, POST)
    t5, C5, D5, n5 = hrrw(w, ph, t1234, Ca, Dd, NT, deq=deqc)
    # ---- the bound
    lmap = {}
    for L_ in ['L', "L'"]:
        lmap[L_] = w.s([c[WRD(L_, '2o')], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, L_, L_))
    leaves = {'( # ` %s )' % ENC('C'): ('NN0', w.s([ec, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, ENC('C')))),
              '( # ` L )': ('NN0', w.s([ll, w.inst('lencl')], 'syl', '( %s -> ( # ` L ) e. NN0 )' % ph)),
              "( # ` L' )": ('NN0', w.s([ll2, w.inst('lencl')], 'syl', "( %s -> ( # ` L' ) e. NN0 )" % ph)),
              '( # ` ( inclBool o. L ) )': ('NN0', w.s([ib1, w.inst('lencl')], 'syl', '( %s -> ( # ` ( inclBool o. L ) ) e. NN0 )' % ph)),
              "( # ` ( inclBool o. L' ) )": ('NN0', w.s([ib2, w.inst('lencl')], 'syl', "( %s -> ( # ` ( inclBool o. L' ) ) e. NN0 )" % ph))}
    cl = Closure(w, ph, leaves)
    for a in list(leaves) + [MXLL]:
        cl.atom(a)
    cl.have(MXLL, 'NN0', w.s([leaves["( # ` L' )"][1], leaves['( # ` L )'][1]], 'ifcld' if False else 'ifcld', '') if False else None) if False else None
    mxn = w.s([leaves['( # ` L )'][1], leaves["( # ` L' )"][1]], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXLL))
    cl.leaf(MXLL, 'NN0', mxn)
    mcl = cl.mem(BND_UB, 'NN0')
    le = linarith(w, ph, [lmap['L'], lmap["L'"]], '%s <_ %s' % (n5, BND_UB), closure=cl)
    hrle(w, ph, phm, t5, C5, D5, n5, BND_UB, mcl, le, qed=True)
    return w.run()



K4 = ['K', 'J', 'I"', 'I0']
PR_DDC = ('TMIdup J I0 I" T M P ( P\' ` 0 )', 'TMIdup K I" I0 T M P\' ( P" ` 0 )', 'TMIcmp I0 I" T M P" E')
DATA_DDC = (((WRD('L', '2o'), WRD("L'", '2o')), (WRD('X', GAM), WRD('Y', GAM), STKD('D'))),
            ('( D ` K ) = %s' % CC('( inclBool o. L )', YX('X')), "( D ` J ) = %s" % CC("( inclBool o. L' )", YX('Y'))))
BND_DDC = "( ( ( 2 x. ( # ` L' ) ) + 5 ) + ( ( ( 2 x. ( # ` L ) ) + 5 ) + ( %s + 2 ) ) )" % MXLL


def STMT_DDC():
    tree = ((T_PHM7, PR_DDC), (idx_tree(K4), dist_tree(K4)), DATA_DDC)
    return tree, TRI(CLN('( P ` 0 )', SS, 'D'), CLN('E', NCM, 'D'), BND_DDC)


def lens(w, ph, c, extra=()):
    leaves = {}
    for L_ in ['L', "L'"] + list(extra):
        lw = c[WRD(L_, '2o')] if isinstance(c, Ctx) else c(L_)
        leaves['( # ` %s )' % L_] = ('NN0', w.s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, L_)))
    return leaves


def ddc_run(w, ph, c, mk, base, ne, S0, preds, labs, ll, ll2, xg, yg):
    """dup y t s ; dup x s t ; cmpFrag t s from the stacks S0 (S0.val K , J the operand words);
    preds: the three predicate leaves, labs: ( P1 , E1 , P2 , E2 , P3 , E ) ; returns
    (triple step, C, D4, bound text, S1, S2, S3, R0, R1)"""
    tv, phm = mk['tv'], mk['phm']
    P1, E1, P2, E2, P3, E3 = labs
    WL2, WL1 = "( inclBool o. L' )", '( inclBool o. L )'
    WX, WY = CC(WL1, YX('X')), CC(WL2, YX('Y'))
    ib2 = w.s([ll2, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, WL2, BITS))
    ib1 = w.s([ll, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, WL1, BITS))
    D0 = S0.D
    m2 = {'K': 'J', 'J': 'I0', 'I': 'I"', 'P': P1, 'E': E1, 'W': WL2, 'X': 'Y', 'D': D0}
    ex2 = dict(base)
    ex2.update({preds[0]: c[preds[0]] if preds[0] in c.all() else base[preds[0]], IDX('J'): c[IDX('J')], IDX('I0'): c[IDX('I0')], IDX('I"'): c[IDX('I"')],
                'J =/= I0': ne('J', 'I0'), 'J =/= I"': ne('J', 'I"'), 'I0 =/= I"': ne('I0', 'I"'),
                WRD(WL2, BITS): ib2, STKD(D0): S0.memb, '( %s ` J ) = %s' % (D0, WY): S0.val('J')[1]})
    t2, c2 = inst(w, ph, 'tmidup', m2, Bld(w, ph, c, ex2))
    Cb, Db, n2 = triple_parts(c2)
    R0 = '( %s ` I0 )' % D0
    r0g = w.s([stkfv(w, ph, D0, 'I0', tv, S0.memb, mk['k']['I0']['kd']), mk['k']['I0']['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, R0))
    WT = CC(WL2, YX(R0))
    S2 = S0.upd('I0', WT, wgcat(w, ph, WL2, YX(R0), wib(w, ph, "L'", ll2), wg4(w, ph, R0, r0g)))
    m3 = {'K': 'K', 'J': 'I"', 'I': 'I0', 'P': P2, 'E': E2, 'W': WL1, 'X': 'X', 'D': S2.D}
    ex3 = dict(base)
    ex3.update({preds[1]: c[preds[1]] if preds[1] in c.all() else base[preds[1]], IDX('K'): c[IDX('K')], IDX('I0'): c[IDX('I0')], IDX('I"'): c[IDX('I"')],
                'K =/= I"': ne('K', 'I"'), 'K =/= I0': ne('K', 'I0'), 'I" =/= I0': ne('I"', 'I0'),
                WRD(WL1, BITS): ib1, STKD(S2.D): S2.memb, '( %s ` K ) = %s' % (S2.D, WX): S2.val('K')[1]})
    t3, c3 = inst(w, ph, 'tmidup', m3, Bld(w, ph, c, ex3))
    Cc_, Dc_, n3 = triple_parts(c3)
    R1 = '( %s ` I" )' % S2.D
    r1g = w.s([stkfv(w, ph, S2.D, 'I"', tv, S2.memb, mk['k']['I"']['kd']), mk['k']['I"']['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, R1))
    WS = CC(WL1, YX(R1))
    S3 = S2.upd('I"', WS, wgcat(w, ph, WL1, YX(R1), wib(w, ph, 'L', ll), wg4(w, ph, R1, r1g)))
    m4 = {'K': 'I0', 'J': 'I"', 'P': P3, 'E': E3, 'L': "L'", "L'": 'L', 'X': R0, 'Y': R1, 'D': S3.D}
    ex4 = dict(base)
    ex4.update({preds[2]: c[preds[2]] if preds[2] in c.all() else base[preds[2]], IDX('I0'): c[IDX('I0')], IDX('I"'): c[IDX('I"')], 'I0 =/= I"': ne('I0', 'I"'),
                WRD(R0, GAM): r0g, WRD(R1, GAM): r1g, STKD(S3.D): S3.memb,
                '( %s ` I0 ) = %s' % (S3.D, CC(WL2, YX(R0))): S3.val('I0')[1],
                '( %s ` I" ) = %s' % (S3.D, CC(WL1, YX(R1))): S3.val('I"')[1]})
    t4, c4 = inst(w, ph, 'tmicmp', m4, Bld(w, ph, c, ex4))
    Cd, Dd, n4 = triple_parts(c4)
    t23 = hrseq(w, ph, phm, t2, t3, Cb, Db, Dc_, n2, n3)
    t234 = hrseq(w, ph, phm, t23, t4, Cb, Dc_, Dd, '( %s + %s )' % (n2, n3), n4)
    NT = '( ( %s + %s ) + %s )' % (n2, n3, n4)
    D4 = UP(UP(S3.D, 'I0', R0), 'I"', R1)
    kI0, kI2 = mk['k']['I0'], mk['k']['I"']
    togk = lambda X, s, g: w.s([g, mk['k'][s]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s)))
    u4 = up4(w, ph, D0, 'I0', WT, 'I"', WS, R0, R1, tv, S0.memb, ne('I0', 'I"'), kI0['kd'],
             togk(WT, 'I0', S2.vals['I0'][2]), togk(R0, 'I0', r0g), kI2['kd'], togk(WS, 'I"', S3.vals['I"'][2]), togk(R1, 'I"', r1g))
    ui = upid(w, ph, D0, 'I0', tv, S0.memb, kI0['kd'])
    r_, newp = w.rewrite(UP(UP(D0, 'I0', R0), 'I"', R1), {UP(D0, 'I0', R0): (D0, ui)}, ph)
    r1v = updnv(w, ph, D0, 'I0', WT, 'I"', tv, S0.memb, kI0['kd'], w.s([S2.vals['I0'][2]], 'elexd', '( %s -> %s e. _V )' % (ph, WT)),
                kI2['kd'], ne('I"', 'I0'))
    uv = upidv(w, ph, D0, 'I"', R1, w.s([r1v], 'eqcomd', '( %s -> ( %s ` I" ) = %s )' % (ph, D0, R1)), tv, S0.memb, kI2['kd'])
    deq = w.s([w.s([u4, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, D4, UP(D0, 'I"', R1))), uv], 'eqtrd', '( %s -> %s = %s )' % (ph, D4, D0))
    return t234, Cb, Dd, NT, D4, deq, ib1, ib2


def tmidm3():
    lab = 'tmidm3'
    T, C = STMT_DDC()
    ph = cj(T)
    w = W(lab, 'The comparison run ` dup y t s ; dup x s t ; cmpFrag t s ` of Lean\'s division (the prologue of '
               '` divmodCore ` and the middle of ` dmDownBody ` ) wherever its three calls are installed in sequence: '
               '` cmp ` compares the word on ` y ` with the word on ` x ` , and the stacks are restored.')
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K4)
    phm, tv = mk['phm'], mk['tv']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K4))))
    base = {PHM: phm, 'T e. V': tv, MTY: mk['mt']}
    ll, ll2, xg, yg, dd = c[WRD('L', '2o')], c[WRD("L'", '2o')], c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    WX, WY = CC('( inclBool o. L )', YX('X')), CC("( inclBool o. L' )", YX('Y'))
    vals = {'K': (WX, c['( D ` K ) = %s' % WX], wgcat(w, ph, '( inclBool o. L )', YX('X'), wib(w, ph, 'L', ll), wg4(w, ph, 'X', xg))),
            'J': (WY, c["( D ` J ) = %s" % WY], wgcat(w, ph, "( inclBool o. L' )", YX('Y'), wib(w, ph, "L'", ll2), wg4(w, ph, 'Y', yg)))}
    for s_ in ['I"', 'I0']:
        vals[s_] = (('( D ` %s )' % s_), w.s([], 'eqidd', '( %s -> ( D ` %s ) = ( D ` %s ) )' % (ph, s_, s_)),
                    w.s([stkfv(w, ph, 'D', s_, tv, dd, mk['k'][s_]['kd']), mk['k'][s_]['wge']], 'eleqtrd', "( %s -> ( D ` %s ) e. Word Gamma' )" % (ph, s_)))
    S0 = Stacks(w, ph, mk, 'D', dd, ne, vals)
    t, Ca, Dd, NT, D4, deq, ib1, ib2 = ddc_run(w, ph, c, mk, base, ne, S0, PR_DDC,
                                           ('P', "( P' ` 0 )", "P'", '( P" ` 0 )', 'P"', 'E'), ll, ll2, xg, yg)
    deqc = clneq(w, ph, 'E', NCM, deq, D4, 'D')
    t5, C5, D5, n5 = hrrw(w, ph, t, Ca, Dd, NT, deq=deqc)
    lmap = {L_: w.s([c[WRD(L_, '2o')], w.inst('bwmaplen')], 'syl', '( %s -> ( # ` ( inclBool o. %s ) ) = ( # ` %s ) )' % (ph, L_, L_)) for L_ in ['L', "L'"]}
    leaves = lens(w, ph, c)
    leaves['( # ` ( inclBool o. L ) )'] = ('NN0', w.s([ib1, w.inst('lencl')], 'syl', '( %s -> ( # ` ( inclBool o. L ) ) e. NN0 )' % ph))
    leaves["( # ` ( inclBool o. L' ) )"] = ('NN0', w.s([ib2, w.inst('lencl')], 'syl', "( %s -> ( # ` ( inclBool o. L' ) ) e. NN0 )" % ph))
    cl = Closure(w, ph, leaves)
    for a in leaves:
        cl.atom(a)
    cl.leaf(MXLL, 'NN0', w.s([leaves['( # ` L )'][1], leaves["( # ` L' )"][1]], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXLL)))
    mcl = cl.mem(BND_DDC, 'NN0')
    le = linarith(w, ph, [lmap['L'], lmap["L'"]], '%s <_ %s' % (n5, BND_DDC), closure=cl)
    hrle(w, ph, phm, t5, C5, D5, n5, BND_DDC, mcl, le, qed=True)
    return w.run()



K5S = ['K', 'J', 'I', 'I"', 'I0']
PR_DSI = ('TMIdup J I0 I" T M P ( P\' ` 0 )', 'TMIsub K I0 I" T M P\' ( P" ` 0 )', 'TMIinc I I" T M P" E')
DATA_DSI = (((WRD('L', '2o'), WRD("L'", '2o'), WRD('L"', '2o')), (WRD('X', GAM), WRD('Y', GAM), WRD('H', GAM)), STKD('D')),
            ('( D ` K ) = %s' % CC('( inclBool o. L )', YX('X')), "( D ` J ) = %s" % CC("( inclBool o. L' )", YX('Y')),
             '( D ` I ) = %s' % CC('( inclBool o. L" )', YX('H'))))
MXA_ = "if ( ( # ` L ) <_ ( # ` L' ) , ( # ` L' ) , ( # ` L ) )"
BND_DSI = "( ( ( 2 x. ( # ` L' ) ) + 5 ) + ( ( ( 3 x. %s ) + 5 ) + ( ( 2 x. ( # ` L\" ) ) + 3 ) ) )" % MXA_
ZTW = CC("( inclBool o. ( ( L subTrunc L' ) ` (/) ) )", YX('X'))
INW = CC('( inclBool o. ( incBits ` L" ) )', YX('H'))


def STMT_DSI():
    tree = ((T_PHM7, PR_DSI), (idx_tree(K5S), dist_tree(K5S)), DATA_DSI)
    return tree, TRI(CLN('( P ` 0 )', SS, 'D'), CLN('E', SS, UP(UP('D', 'K', ZTW), 'I', INW)), BND_DSI)


def tmidmsb():
    lab = 'tmidmsb'
    T, C = STMT_DSI()
    ph = cj(T)
    w = W(lab, 'The subtraction run ` dup y t s ; sub x t s x ; incr q s ` of Lean\'s ` dmDownBody ` (the ` ite ` \'s '
               'true branch) wherever its three calls are installed in sequence: ` x ` loses the word on ` y ` , '
               '` q ` is incremented, ` t ` and ` s ` are restored.')
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K5S)
    phm, tv = mk['phm'], mk['tv']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K5S))))
    base = {PHM: phm, 'T e. V': tv, MTY: mk['mt']}
    ll, ll2, llq = c[WRD('L', '2o')], c[WRD("L'", '2o')], c[WRD('L"', '2o')]
    xg, yg, hg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[WRD('H', GAM)], c[STKD('D')]
    WL1, WL2, WLQ = '( inclBool o. L )', "( inclBool o. L' )", '( inclBool o. L" )'
    WX, WY, WH = CC(WL1, YX('X')), CC(WL2, YX('Y')), CC(WLQ, YX('H'))
    vals = {'K': (WX, c['( D ` K ) = %s' % WX], wgcat(w, ph, WL1, YX('X'), wib(w, ph, 'L', ll), wg4(w, ph, 'X', xg))),
            'J': (WY, c['( D ` J ) = %s' % WY], wgcat(w, ph, WL2, YX('Y'), wib(w, ph, "L'", ll2), wg4(w, ph, 'Y', yg))),
            'I': (WH, c['( D ` I ) = %s' % WH], wgcat(w, ph, WLQ, YX('H'), wib(w, ph, 'L"', llq), wg4(w, ph, 'H', hg)))}
    for s_ in ['I"', 'I0']:
        vals[s_] = (('( D ` %s )' % s_), w.s([], 'eqidd', '( %s -> ( D ` %s ) = ( D ` %s ) )' % (ph, s_, s_)),
                    w.s([stkfv(w, ph, 'D', s_, tv, dd, mk['k'][s_]['kd']), mk['k'][s_]['wge']], 'eleqtrd', "( %s -> ( D ` %s ) e. Word Gamma' )" % (ph, s_)))
    S0 = Stacks(w, ph, mk, 'D', dd, ne, vals)
    # dup y t s
    ib2 = w.s([ll2, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, WL2, BITS))
    m1 = {'K': 'J', 'J': 'I0', 'I': 'I"', 'P': 'P', 'E': "( P' ` 0 )", 'W': WL2, 'X': 'Y', 'D': 'D'}
    ex1 = dict(base)
    ex1.update({'J =/= I0': ne('J', 'I0'), 'J =/= I"': ne('J', 'I"'), 'I0 =/= I"': ne('I0', 'I"'), WRD(WL2, BITS): ib2})
    t1, c1 = inst(w, ph, 'tmidup', m1, Bld(w, ph, c, ex1))
    Ca, Da, n1 = triple_parts(c1)
    R0 = '( D ` I0 )'
    WT = CC(WL2, YX(R0))
    S1 = S0.upd('I0', WT, wgcat(w, ph, WL2, YX(R0), wib(w, ph, "L'", ll2), wg4(w, ph, R0, S0.vals['I0'][2])))
    assert Da == CLN("( P' ` 0 )", SS, S1.D), Da
    # sub x t s x
    m2 = {'K': 'K', 'J': 'I0', 'I': 'I"', 'P': "P'", 'E': '( P" ` 0 )', 'L': 'L', "L'": "L'", 'X': 'X', 'Y': R0, 'D': S1.D}
    ex2 = dict(base)
    ex2.update({'K =/= I0': ne('K', 'I0'), 'K =/= I"': ne('K', 'I"'), 'I0 =/= I"': ne('I0', 'I"'), WRD(R0, GAM): S0.vals['I0'][2],
                STKD(S1.D): S1.memb, '( %s ` K ) = %s' % (S1.D, WX): S1.val('K')[1], '( %s ` I0 ) = %s' % (S1.D, WT): S1.val('I0')[1]})
    t2, c2 = inst(w, ph, 'tmisub', m2, Bld(w, ph, c, ex2))
    Cb, Db, n2 = triple_parts(c2)
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    ztw = w.s([ll, ll2, b0, w.inst('subtrunccl')], 'syl3anc', "( %s -> ( ( L subTrunc L' ) ` (/) ) e. Word 2o )" % ph)
    Sa = S1.upd('K', ZTW, wgcat(w, ph, "( inclBool o. ( ( L subTrunc L' ) ` (/) ) )", YX('X'), wib(w, ph, "( ( L subTrunc L' ) ` (/) )", ztw), wg4(w, ph, 'X', xg)))
    S2 = Sa.upd('I0', R0, S0.vals['I0'][2])
    assert Db == CLN('( P" ` 0 )', SS, S2.D), (Db, S2.D)
    # incr q s
    m3 = {'K': 'I', 'J': 'I"', 'P': 'P"', 'E': 'E', 'L': 'L"', 'X': 'H', 'D': S2.D}
    ex3 = dict(base)
    ex3.update({'I =/= I"': ne('I', 'I"'), STKD(S2.D): S2.memb, '( %s ` I ) = %s' % (S2.D, WH): S2.val('I')[1]})
    t3, c3 = inst(w, ph, 'tmiincs', m3, Bld(w, ph, c, ex3))
    Cc_, Dc_, n3 = triple_parts(c3)
    t12 = hrseq(w, ph, phm, t1, t2, Ca, Da, Db, n1, n2)
    t123 = hrseq(w, ph, phm, t12, t3, Ca, Db, Dc_, '( %s + %s )' % (n1, n2), n3)
    NT = '( ( %s + %s ) + %s )' % (n1, n2, n3)
    # the stacks
    icw = w.s([llq, w.inst('incbitscl')], 'syl', '( %s -> ( incBits ` L" ) e. Word 2o )' % ph)
    D3 = UP(S2.D, 'I', INW)
    assert Dc_ == CLN('E', SS, D3), Dc_
    kI0, kK = mk['k']['I0'], mk['k']['K']
    togk = lambda X, s_, g: w.s([g, mk['k'][s_]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, X, GX(s_)))
    u3 = up3(w, ph, 'D', 'I0', WT, 'K', ZTW, R0, tv, dd, ne('I0', 'K'), kI0['kd'], togk(WT, 'I0', S1.vals['I0'][2]),
             togk(R0, 'I0', S0.vals['I0'][2]), kK['kd'], togk(ZTW, 'K', Sa.vals['K'][2]))
    ui = upid(w, ph, 'D', 'I0', tv, dd, kI0['kd'])
    r_, newp = w.rewrite(UP(UP('D', 'I0', R0), 'K', ZTW), {UP('D', 'I0', R0): ('D', ui)}, ph)
    e2 = w.s([u3, r_], 'eqtrd', '( %s -> %s = %s )' % (ph, S2.D, UP('D', 'K', ZTW)))
    r2, new2 = w.rewrite(D3, {S2.D: (UP('D', 'K', ZTW), e2)}, ph)
    POST = UP(UP('D', 'K', ZTW), 'I', INW)
    assert new2 == POST, new2
    deqc = clneq(w, ph, 'E', SS, r2, D3, POST)
    t5, C5, D5, n5 = hrrw(w, ph, t123, Ca, Dc_, NT, deq=deqc)
    lmap = w.s([ll2, w.inst('bwmaplen')], 'syl', "( %s -> ( # ` ( inclBool o. L' ) ) = ( # ` L' ) )" % ph)
    leaves = lens(w, ph, c, extra=['L"'])
    leaves["( # ` ( inclBool o. L' ) )"] = ('NN0', w.s([ib2, w.inst('lencl')], 'syl', "( %s -> ( # ` ( inclBool o. L' ) ) e. NN0 )" % ph))
    cl = Closure(w, ph, leaves)
    for a in leaves:
        cl.atom(a)
    cl.leaf(MXA_, 'NN0', w.s([leaves["( # ` L' )"][1], leaves['( # ` L )'][1]], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXA_)))
    mcl = cl.mem(BND_DSI, 'NN0')
    le = linarith(w, ph, [lmap], '%s <_ %s' % (n5, BND_DSI), closure=cl)
    hrle(w, ph, phm, t5, C5, D5, n5, BND_DSI, mcl, le, qed=True)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
