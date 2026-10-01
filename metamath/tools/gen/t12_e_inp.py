"""T12: inputF at the machine (Lean ` inputF_runs ` , ` moveNum_runs_raw ` ).

  t12rdan   ` readA ` at the empty stack ( ` none ` ) acts as at the terminator
  tmimvt    ` moveNum K J ` at the machine on a terminated number (~ tm2fmvn at the concrete handlers)
  tmimvr    ` moveNum K J ` at the machine on an unterminated number (~ tm2fmvnw , then ~ t12pop0 )
  tmiinpd   inputF from any stacks with the values of ` Frag.initStacks 0 ( encodeNatGamma' n ) `
  tmiinp    Lean's ` inputF_runs `

    MM_DB=sorties/t12.mm python3 tools/gen/t12_e_inp.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq
from cl import Closure
from t7_e_cmp import machine, togk, letgk, bitsgk, cis_ty
import t7c_h_lst as LST
from t12_d_fal import to_init
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
NONE_ = '( inr ` (/) )'
ST_RDAN = '( V e. TMSt -> ( TMrdA ` <. V , %s >. ) = ( TMrdA ` <. V , ( inl ` 4 ) >. ) )' % NONE_
MVST = MOVST('K', 'J', 'A', 'E')
TREE_MVH = ((T_PHM7, MEQ('A', MVST)), ((LAB('A'), LAB('E')), (IDX('K'), IDX('J'), 'K =/= J')))
TREE_MVT = (TREE_MVH, ((WRD('W', BITS), WG('X'), STKD('D')), '( D ` K ) = ( W ++ ( <" 4 "> ++ X ) )'))
CONCL_MVT = TRI(CLN('A', S, 'D'), CLN('E', S, UP(UP('D', 'K', 'X'), 'J', '( ( reverse ` W ) ++ ( D ` J ) )')), '( ( # ` W ) + 1 )')
TREE_MVR = (TREE_MVH, ((WRD('W', BITS), STKD('D')), '( D ` K ) = W'))
CONCL_MVR = TRI(CLN('A', S, 'D'), CLN('E', S, UP(UP('D', 'K', '(/)'), 'J', '( ( reverse ` W ) ++ ( D ` J ) )')), '( ( # ` W ) + 1 )')
add12('tmimvt', TREE_MVT, CONCL_MVT)
add12('tmimvr', TREE_MVR, CONCL_MVR)

WN = '( encNatGam ` N )'
DEQS_INP = (((DEQ(0, WN), DEQ(1, '(/)')), (DEQ(2, '(/)'), DEQ(3, '(/)'))), ((DEQ(4, '(/)'), DEQ(5, '(/)')), (DEQ(6, '(/)'), DEQ(7, '(/)'))))
TREE_INPD = TREE0('inp', ((STKD('D'), 'N e. NN0'), DEQS_INP))
CONCL_INPD = TRI(CS('inp'), CLN('E', S, INIT('7', '( %s ++ %s )' % (WN, COMMA1))), '( ( 2 x. ( # ` ( encodeNat ` N ) ) ) + 4 )')
add12('tmiinpd', TREE_INPD, CONCL_INPD)


def t12rdan():
    lab = 't12rdan'
    ph = 'V e. TMSt'
    w = W(lab, 'The pop handler ` readA ` reading ` none ` (an empty stack) sets the state as reading the terminator '
               '(Lean: ` readA v none = { v with ra := none , da := true } ` , the second clause of ~ df-tmrda ; used by '
               '` moveNum_loop_raw ` ).')
    s = w.s
    vv = s([], 'id', '( %s -> V e. TMSt )' % ph)
    # the value of df-tmrda at ( V , none )
    O = NONE_
    X1 = lambda v, o: MK('( TMcar ` %s )' % v, '( inl ` ( 2nd ` ( 2nd ` %s ) ) )' % o, '( TMrb ` %s )' % v, '( TMda ` %s )' % v,
                         '( TMdb ` %s )' % v, '( TMcmp ` %s )' % v, '( TMfl ` %s )' % v)
    X2 = lambda v: MK('( TMcar ` %s )' % v, NONE_, '( TMrb ` %s )' % v, '1o', '( TMdb ` %s )' % v, '( TMcmp ` %s )' % v,
                      '( TMfl ` %s )' % v)
    CND = lambda o: '( ( 1st ` %s ) = (/) /\\ ( 2nd ` %s ) e. %s )' % (o, o, BITS)
    BODY = lambda v, o: 'if ( %s , %s , %s )' % (CND(o), X1(v, o), X2(v))
    ante = '( v = V /\\ o = %s )' % O
    ev = s([], 'simpl', '( %s -> v = V )' % ante)
    eo = s([], 'simpr', '( %s -> o = %s )' % (ante, O))
    cg, nb = w.congr(BODY('v', 'o'), {'v': 'V', 'o': O}, ante, {'v': ev, 'o': eo})
    assert nb == BODY('V', O), nb
    d = s([], 'df-tmrda', 'TMrdA = ( v e. TMSt , o e. %s |-> %s )' % (OPT, BODY('v', 'o')))
    oo = s([s([s([], '0lt1o', '(/) e. 1o'), w.inst('djurcl')], 'ax-mp', '%s e. %s' % (O, OPT))], 'a1i', '( %s -> %s e. %s )' % (ph, O, OPT))
    ifx = s([s([], 'ifex', '%s e. _V' % BODY('V', O))], 'a1i', '( %s -> %s e. _V )' % (ph, BODY('V', O)))
    j = s([vv, oo, ifx], '3jca', '( %s -> ( V e. TMSt /\\ %s e. %s /\\ %s e. _V ) )' % (ph, O, OPT, BODY('V', O)))
    ovi = s([cg, d], 'ovmpoga', '( ( V e. TMSt /\\ %s e. %s /\\ %s e. _V ) -> ( V TMrdA %s ) = %s )' % (O, OPT, BODY('V', O), O, BODY('V', O)))
    ov = s([j, ovi], 'syl', '( %s -> ( V TMrdA %s ) = %s )' % (ph, O, BODY('V', O)))
    dov = s([s([], 'df-ov', '( V TMrdA %s ) = ( TMrdA ` <. V , %s >. )' % (O, O))], 'a1i',
            '( %s -> ( V TMrdA %s ) = ( TMrdA ` <. V , %s >. ) )' % (ph, O, O))
    v1 = s([dov, ov], 'eqtr3d', '( %s -> ( TMrdA ` <. V , %s >. ) = %s )' % (ph, O, BODY('V', O)))
    # the condition is false: ( 1st ` ( inr ` (/) ) ) = 1o =/= (/)
    f1 = s([s([], '0ex', '(/) e. _V'), w.inst('1stinr')], 'ax-mp', '( 1st ` %s ) = 1o' % O)
    n0 = s([f1, s([], '1n0', '1o =/= (/)')], 'eqnetri', '( 1st ` %s ) =/= (/)' % O)
    nn = s([n0], 'neii', '-. ( 1st ` %s ) = (/)' % O)
    nc = s([s([nn], 'intnanr', '-. %s' % CND(O))], 'a1i', '( %s -> -. %s )' % (ph, CND(O)))
    v2 = s([nc], 'iffalsed', '( %s -> %s = %s )' % (ph, BODY('V', O), X2('V')))
    va = s([v1, v2], 'eqtrd', '( %s -> ( TMrdA ` <. V , %s >. ) = %s )' % (ph, O, X2('V')))
    # tmcrdan at the terminator 4
    g4 = s([s([], 'gamma4', "4 e. Gamma'")], 'a1i', "( %s -> 4 e. Gamma' )" % ph)
    n4 = s([s([s([], '4re', '4 e. RR'), w.inst('tmcnbits')], 'ax-mp', '-. 4 e. %s' % BITS)], 'a1i', '( %s -> -. 4 e. %s )' % (ph, BITS))
    vb = s([vv, g4, n4, w.inst('tmcrdan')], 'syl3anc', '( %s -> ( TMrdA ` <. V , ( inl ` 4 ) >. ) = %s )' % (ph, X2('V')))
    w.qed([va, vb], 'eqtr4d', ST_RDAN)
    return w.run()


def mover_extra(w, ph, c, mk):
    """the leaves of ~ tm2fmvn / ~ tm2fmvnw at the concrete handlers readA , isSome , bit ( bitOf ra ) , all states"""
    s = w.s
    ex = LST.handler_extra(w, ph, mk, LST.IFACE)
    ex[RTY('TMrdA', 'K')] = mk['k']['K']['hdl']['TMrdA']
    ex['%s e. ( 2o ^m %s )' % (CIS, S)] = cis_ty(w, ph, mk)
    pb = ex["%s e. ( Gamma' ^m %s )" % (PBR, S)]
    ge = mk['k']['J']['ge']
    e = s([ge], 'oveq1d', "( %s -> ( %s ^m %s ) = ( Gamma' ^m %s ) )" % (ph, GX('J'), S, S))
    ex['%s e. ( %s ^m %s )' % (PBR, GX('J'), S)] = s([pb, e], 'eleqtrrd', '( %s -> %s e. ( %s ^m %s ) )' % (ph, PBR, GX('J'), S))
    ex['%s C_ %s' % (BITS, GX('K'))] = bitsgk(w, ph, mk, 'K')
    ex['%s C_ %s' % (BITS, GX('J'))] = bitsgk(w, ph, mk, 'J')
    ex['4 e. %s' % GX('K')] = letgk(w, ph, mk, '4', 'K', closed(w, ph, 'gamma4', "4 e. Gamma'"))
    ex['K e. %s' % DOMT] = mk['k']['K']['kd']
    ex['J e. %s' % DOMT] = mk['k']['J']['kd']
    ex['%s C_ %s' % (S, S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    return ex


def tmimvt():
    lab = 'tmimvt'
    T = TREE_MVT
    ph = cj(T)
    w = W(lab, 'Lean\'s ` moveNum_runs ` at the machine: the one-label mover ` moveNum K J ` (pop ` readA ` , branch '
               '` isSome ` , push ` bit ( bitOf ra ) ` ) moves the number on ` K ` , reversed, onto ` J ` and consumes the '
               'terminator (~ tm2fmvn at the concrete handlers, ~ tmclhi ).')
    s = w.s
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, ['K', 'J'])
    ex = mover_extra(w, ph, c, mk)
    dd = c[STKD('D')]
    xg = c[WG('X')]
    ex[WRD('X', GX('K'))] = togk(w, ph, mk, 'X', 'K', xg)
    DJ = '( D ` J )'
    djg = s([stkfv(w, ph, 'D', 'J', mk['tv'], dd, mk['k']['J']['kd']), mk['k']['J']['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, DJ))
    ex[WRD(DJ, GX('J'))] = togk(w, ph, mk, DJ, 'J', djg)
    ex[PHM] = mk['phm']
    m = {'F': 'TMrdA', 'C': CIS, 'P': PBR, 'B': BITS, 'Y': '4', 'N': S, 'H': DJ, 'W': 'W', 'X': 'X', 'K': 'K', 'J': 'J',
         'A': 'A', 'E': 'E', 'D': 'D'}
    t, cc = inst(w, ph, 'tm2fmvn', m, Bld(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc)
    W4X = '( W ++ ( <" 4 "> ++ X ) )'
    PRE = UP(UP('D', 'K', W4X), 'J', DJ)
    assert C1 == CLN('A', S, PRE), C1
    e1 = upidv(w, ph, 'D', 'K', W4X, c['( D ` K ) = %s' % W4X], mk['tv'], dd, mk['k']['K']['kd'])
    r1, x1 = w.rewrite(PRE, {UP('D', 'K', W4X): ('D', e1)}, ph)
    assert x1 == UP('D', 'J', DJ), x1
    e2 = upid(w, ph, 'D', 'J', mk['tv'], dd, mk['k']['J']['kd'])
    deq = s([r1, e2], 'eqtrd', '( %s -> %s = D )' % (ph, PRE))
    t, C, D, n = hrrw(w, ph, t, C1, D1, n1, ceq=clneq(w, ph, 'A', S, deq, PRE, 'D'))
    assert (C, D, n) == (CLN('A', S, 'D'), CLN('E', S, UP(UP('D', 'K', 'X'), 'J', '( ( reverse ` W ) ++ ( D ` J ) )')), '( ( # ` W ) + 1 )'), (C, D, n)
    w.qed([t, w.inst('biid')], 'mpbi', STMTS12[lab])
    return w.run()


def tmimvr():
    lab = 'tmimvr'
    T = TREE_MVR
    ph = cj(T)
    w = W(lab, 'Lean\'s ` moveNum_runs_raw ` at the machine: the one-label mover ` moveNum K J ` on a stack holding only the '
               'bits of a number moves them, reversed, onto ` J ` ; the last pop reads ` none ` , which ` readA ` treats as '
               'the terminator (~ tm2fmvnw , ~ t12rdan , ~ t12pop0 ).')
    s = w.s
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, ['K', 'J'])
    ex = mover_extra(w, ph, c, mk)
    dd = c[STKD('D')]
    tv = mk['tv']
    DJ = '( D ` J )'
    djg = s([stkfv(w, ph, 'D', 'J', tv, dd, mk['k']['J']['kd']), mk['k']['J']['wge']], 'eleqtrd', "( %s -> %s e. Word Gamma' )" % (ph, DJ))
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    ex[WRD('(/)', GX('K'))] = togk(w, ph, mk, '(/)', 'K', wrd0)
    ex[WRD(DJ, GX('J'))] = togk(w, ph, mk, DJ, 'J', djg)
    ex['(/) e. Word %s' % BITS] = closed(w, ph, 'wrd0', '(/) e. Word %s' % BITS)
    ex[PHM] = mk['phm']
    QE = GT('E')
    ex['%s e. ( TM2Stmt ` T )' % QE] = gotocl(w, ph, tv, 'E', c[LAB('E')])
    m = {'F': 'TMrdA', 'C': CIS, 'P': PBR, 'B': BITS, 'N': S, 'H': DJ, 'W': 'W', 'R': '(/)', 'U': '(/)', 'Q': QE,
         'K': 'K', 'J': 'J', 'A': 'A', 'D': 'D'}
    t1, cc1 = inst(w, ph, 'tm2fmvnw', m, Bld(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc1)
    PRE = UP(UP('D', 'K', '( W ++ (/) )'), 'J', '( (/) ++ %s )' % DJ)
    assert C1 == CLN('A', S, PRE), C1
    wb = c[WRD('W', BITS)]
    ww = s([wb, s([closed(w, ph, 'tm2lbits', "%s C_ Gamma'" % BITS), w.inst('sswrd')], 'syl', "( %s -> Word %s C_ Word Gamma' )" % (ph, BITS))],
           'sseldd', "( %s -> W e. Word Gamma' )" % ph)
    cw = s([ww, w.inst('ccatrid')], 'syl', '( %s -> ( W ++ (/) ) = W )' % ph)
    cj_ = s([djg, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, DJ, DJ))
    r1, x1 = w.rewrite(PRE, {'( W ++ (/) )': ('W', cw), '( (/) ++ %s )' % DJ: (DJ, cj_)}, ph)
    assert x1 == UP(UP('D', 'K', 'W'), 'J', DJ), x1
    e1 = upidv(w, ph, 'D', 'K', 'W', c['( D ` K ) = W'], tv, dd, mk['k']['K']['kd'])
    r2, x2 = w.rewrite(x1, {UP('D', 'K', 'W'): ('D', e1)}, ph)
    e2 = upid(w, ph, 'D', 'J', tv, dd, mk['k']['J']['kd'])
    deq = s([r1, r2, e2], '3eqtrd', '( %s -> %s = D )' % (ph, PRE))
    # the post of the loop part: K := ( (/) ++ (/) ) , J := ( ( ( reverse ` W ) ++ (/) ) ++ ( D ` J ) )
    RW = '( reverse ` W )'
    Y = '( %s ++ %s )' % (RW, DJ)
    POST1 = UP(UP('D', 'K', '( (/) ++ (/) )'), 'J', '( ( %s ++ (/) ) ++ %s )' % (RW, DJ))
    assert D1 == CLN('A', S, POST1), D1
    c00 = s([wrd0, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ (/) ) = (/) )' % ph)
    rwg = s([ww, w.inst('revcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, RW))
    crw = s([rwg, w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (ph, RW, RW))
    r3, x3 = w.rewrite(POST1, {'( (/) ++ (/) )': ('(/)', c00), '( %s ++ (/) )' % RW: (RW, crw)}, ph)
    POST2 = UP(UP('D', 'K', '(/)'), 'J', Y)
    assert x3 == POST2, x3
    # commute: ( ( D |` .. K ) u. K := (/) ) then J := Y  =  J := Y then K := (/)
    yg = wgcat(w, ph, RW, DJ, rwg, djg)
    com = s([s([s([tv, dd], 'jca', '( %s -> ( T e. V /\\ D e. ( TM2Stk ` T ) ) )' % ph), c['K =/= J']], 'jca',
               '( %s -> ( ( T e. V /\\ D e. ( TM2Stk ` T ) ) /\\ K =/= J ) )' % ph),
             s([mk['k']['K']['kd'], ex[WRD('(/)', GX('K'))]], 'jca', '( %s -> ( K e. %s /\\ (/) e. Word %s ) )' % (ph, DOMT, GX('K'))),
             s([mk['k']['J']['kd'], togk(w, ph, mk, Y, 'J', yg)], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DOMT, Y, GX('J'))),
             w.inst('tm2stkupc')], 'syl3anc', '( %s -> %s = %s )' % (ph, POST2, UP(UP('D', 'J', Y), 'K', '(/)')))
    POST3 = UP(UP('D', 'J', Y), 'K', '(/)')
    d13 = s([r3, com], 'eqtrd', '( %s -> %s = %s )' % (ph, POST1, POST3))
    t1, C, D, n = hrrw(w, ph, t1, C1, D1, n1, ceq=clneq(w, ph, 'A', S, deq, PRE, 'D'), deq=clneq(w, ph, 'A', S, d13, POST1, POST3))
    # the exit step at the empty stack (t12pop0 at D' = UP( D , J , Y ))
    DJY = UP('D', 'J', Y)
    djy = updcl(w, ph, 'D', 'J', Y, tv, dd, mk['k']['J']['kd'], togk(w, ph, mk, Y, 'J', yg))
    PU = PUSH('J', PBR, GT('A'))
    ex2 = dict(ex)
    ex2[STKD(DJY)] = djy
    ex2['%s e. ( TM2Stmt ` T )' % PU] = pushcl(w, ph, tv, 'J', PBR, GT('A'), mk['k']['J']['kd'], ex['%s e. ( %s ^m %s )' % (PBR, GX('J'), S)],
                                               gotocl(w, ph, tv, 'A', c[LAB('A')]))
    # A. r e. S -. ( CIS ` ( TMrdA ` <. r , none >. ) ) = 1o , from t12rdan and the terminator clause of tmclhi
    pr = '( %s /\\ r e. %s )' % (ph, S)
    MV2 = LST.MV2
    mv2 = s([ex[MV2]], 'r19.21bi', '( %s -> ( -. ( %s ` %s ) = 1o /\\ %s e. %s ) )' % (pr, CIS, NVA('r', '4'), NVA('r', '4'), S))
    n4 = s([mv2], 'simpld', '( %s -> -. ( %s ` %s ) = 1o )' % (pr, CIS, NVA('r', '4')))
    rt = s([s([], 'simpr', '( %s -> r e. %s )' % (pr, S)), s([mk['seq']], 'adantr', '( %s -> %s )' % (pr, SEQ))],
           'eleqtrd', '( %s -> r e. TMSt )' % pr)
    NN_ = '( TMrdA ` <. r , %s >. )' % NONE_
    rd = s([rt, w.inst('t12rdan')], 'syl', '( %s -> %s = %s )' % (pr, NN_, NVA('r', '4')))
    cq = s([s([rd], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (pr, CIS, NN_, CIS, NVA('r', '4')))], 'eqeq1d',
           '( %s -> ( ( %s ` %s ) = 1o <-> ( %s ` %s ) = 1o ) )' % (pr, CIS, NN_, CIS, NVA('r', '4')))
    nn = s([n4, cq], 'mtbird', '( %s -> -. ( %s ` %s ) = 1o )' % (pr, CIS, NN_))
    ex2['A. r e. %s -. ( %s ` %s ) = 1o' % (S, CIS, NN_)] = s([nn], 'ralrimiva', '( %s -> A. r e. %s -. ( %s ` %s ) = 1o )' % (ph, S, CIS, NN_))
    m2 = {'F': 'TMrdA', 'C': CIS, 'Q': PU, 'K': 'K', 'A': 'A', 'E': 'E', 'D': DJY}
    t2, cc2 = inst(w, ph, 't12pop0', m2, Bld(w, ph, c, ex2))
    C2, D2, n2 = triple_parts(cc2)
    assert C2 == CLN('A', S, POST3), C2
    t = hrseq(w, ph, mk['phm'], t1, t2, C, D, D2, n, n2)
    # commute back
    comb = s([com], 'eqcomd', '( %s -> %s = %s )' % (ph, POST3, POST2))
    t, C, D, n = hrrw(w, ph, t, C, D2, '( %s + %s )' % (n, n2), deq=clneq(w, ph, 'E', S, comb, POST3, POST2))
    w.qed([t, w.inst('biid')], 'mpbi', STMTS12[lab]) if n == '( ( # ` W ) + 1 )' else None
    if n != '( ( # ` W ) + 1 )':
        raise ValueError(n)
    return w.run()



def tmiinpd():
    lab = 'tmiinpd'
    T = numtree(TREE_INPD)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` inputF_runs ` from any stacks holding the raw ` encodeNatGamma\' n ` on 0 and nothing else: '
               '` pushSym 2 comma ` , the raw ` moveNum 0 2 ` (~ tmimvr ), ` pushSym 7 comma ` , ` moveNum 2 7 ` (~ tmimvt ) '
               'leave ` Frag.initStacks 7 ( encodeNatGamma\' n ++ [ comma ] ) ` .')
    s = w.s
    c0 = Ctx(w, ph, T)
    nn = c0['N e. NN0']
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    gW = encw(w, ph, 'N', nn)
    eqs = {'0': (WN, gW)}
    for k in N8[1:]:
        eqs[k] = ('(/)', wrd0)
    B = Base(w, ph, T, N8, 'inp', eqs)
    c, mk = B.c, B.mk
    LM = FRAGS['inp'].lmap()
    R = B.run()
    E0 = '( <" 4 "> ++ (/) )'
    g40 = B.g(E0, wg4(w, ph, '(/)', wrd0))
    def g4k(k):
        return s([closed(w, ph, 'gamma4', "4 e. Gamma'"), mk['k'][k]['ge']], 'eleqtrrd', '( %s -> 4 e. %s )' % (ph, GX(k)))
    # 1. pushSym 2 comma
    B.call(R, 'tm2fpshn', {'A': LM['Z1'], 'E': LM['Z2'], 'K': '2', 'Z': '4', 'N': S}, {'4 e. %s' % GX('2'): g4k('2')}, [('2', E0, g40)])
    # 2. the raw moveNum 0 2
    wb = engb(w, ph, 'N', nn)
    RW = '( reverse ` %s )' % WN
    rwb = s([wb, w.inst('revcl')], 'syl', '( %s -> %s e. Word %s )' % (ph, RW, BITS))
    rwg = s([gW, w.inst('revcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, RW))
    V2 = '( %s ++ %s )' % (RW, E0)
    g2 = B.g(V2, wgcat(w, ph, RW, E0, rwg, g40))
    B.call(R, 'tmimvr', {'K': '0', 'J': '2', 'A': LM['Z2'], 'E': LM['Z3'], 'W': WN},
           {WRD(WN, BITS): wb}, [('0', '(/)', wrd0), ('2', V2, g2)])
    # 3. pushSym 7 comma
    B.call(R, 'tm2fpshn', {'A': LM['Z3'], 'E': LM['Z4'], 'K': '7', 'Z': '4', 'N': S}, {'4 e. %s' % GX('7'): g4k('7')}, [('7', E0, g40)])
    # 4. moveNum 2 7
    RRW = '( reverse ` %s )' % RW
    rrwg = s([rwg, w.inst('revcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, RRW))
    V7 = '( %s ++ %s )' % (RRW, E0)
    g7 = B.g(V7, wgcat(w, ph, RRW, E0, rrwg, g40))
    B.call(R, 'tmimvt', {'K': '2', 'J': '7', 'A': LM['Z4'], 'E': 'E', 'W': RW, 'X': '(/)'},
           {WRD(RW, BITS): rwb, WG('(/)'): wrd0}, [('2', '(/)', wrd0), ('7', V7, g7)])
    cur, of = R.normalize(N8)
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    print('FINAL CHAIN', of, file=sys.stderr)
    print('COST', n, file=sys.stderr)
    Dc = triple_D(D)
    W7 = '( %s ++ %s )' % (WN, COMMA1)
    rr = s([gW, w.inst('revrev')], 'syl', '( %s -> %s = %s )' % (ph, RRW, WN))
    s1 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> %s e. Word Gamma' )" % (ph, COMMA1))
    cr = s([s1, w.inst('ccatrid')], 'syl', '( %s -> %s = %s )' % (ph, E0, COMMA1))
    e7, x7 = w.rewrite(V7, {RRW: (WN, rr), E0: (COMMA1, cr)}, ph)
    assert x7 == W7, x7
    vals = {}
    for k in N8:
        txt, st, g = R.S.vals[k]
        if k == '7':
            assert txt == V7, txt
            vals[k] = s([st, e7], 'eqtrd', '( %s -> ( %s ` 7 ) = %s )' % (ph, Dc, W7))
        else:
            assert txt == '(/)', (k, txt)
            vals[k] = st
    w7g = wgcat(w, ph, WN, COMMA1, gW, s1)
    wv = s([w7g], 'elexd', '( %s -> %s e. _V )' % (ph, W7))
    deq = to_init(w, ph, B, R, '7', W7, wv, w7g, vals, Dc)
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, 'E', S, deq, Dc, INIT('7', W7)))
    # the bound: # ( reverse W ) = # W = # ( encodeNat N )
    LW, LRW, LEN_ = '( # ` %s )' % WN, '( # ` %s )' % RW, '( # ` ( encodeNat ` N ) )'
    cl = Closure(w, ph, {'N': ('NN0', nn)})
    le0 = s([nn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = %s )' % (ph, LW, LEN_))
    lr = s([gW, w.inst('revlen')], 'syl', '( %s -> %s = %s )' % (ph, LRW, LW))
    en = s([s([nn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` N ) e. Word 2o )' % ph), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN_))
    cl.leaf(LEN_, 'NN0', en)
    cl.leaf(LW, 'NN0', s([le0, en], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, LW)))
    cl.leaf(LRW, 'NN0', s([lr, cl.mem(LW, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, LRW)))
    BND = '( ( 2 x. ( # ` ( encodeNat ` N ) ) ) + 4 )'
    le = linarith(w, ph, [le0, lr], '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


def tmiinp():
    lab = 'tmiinp'
    T = numtree(TREE_INP)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` inputF_runs ` at the machine: wherever ` inputF ` is installed, from '
               '` Frag.initStacks 0 ( encodeNatGamma\' n ) ` it leaves ` Frag.initStacks 7 ( encodeNatGamma\' n ++ [ comma ] ) ` '
               'within ` 2 # ( encodeNat n ) + 4 ` steps (~ tmiinpd at the initial stacks, ~ t12ini ).')
    s = w.s
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, N8)
    nn = c['N e. NN0']
    from t12_d_fal import init_vals
    gW = encw(w, ph, 'N', nn)
    IN0 = INIT('0', WN)
    iv = init_vals(w, ph, mk, '0', WN, s([gW], 'elexd', '( %s -> %s e. _V )' % (ph, WN)))
    ex = {}
    for k in N8:
        ex['( %s ` %s ) = %s' % (IN0, k, WN if k == '0' else '(/)')] = iv[k]
    ex[STKD(IN0)] = s([mk['tv'], mk['k']['0']['kd'], togk(w, ph, mk, WN, '0', gW), w.inst('tm2initstk')], 'syl3anc',
                      '( %s -> %s e. ( TM2Stk ` T ) )' % (ph, IN0))
    ex[PHM] = mk['phm']
    t, cc = inst(w, ph, 'tmiinpd', {'D': IN0}, Bld(w, ph, c, ex))
    assert cc == CONCL_INP, cc
    k = w.s([], 't10stk', ST_NUMS)
    w.qed([k, t], 'mpan2', STMTS12[lab])
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
