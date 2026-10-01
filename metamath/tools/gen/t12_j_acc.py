"""T12: the accumulator of verifyF's list checks (Step5.lean ` accAnd ` , ` accLoopF ` ; blueprint D4).

  tmiaca   ` accAnd_runs ` : ` acc := acc && flag ` on stack 1, from the flag class ` NFL( O ) `
  tmiacl   the generic accumulator loop ( ` accLoopF_runs ` ) on ~ tm2lfes , over the own equations of
           ` accLoopF ` and a stack family ` P `

    MM_DB=sorties/t12.mm python3 tools/gen/t12_j_acc.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq
from cl import Closure
from t7_e_cmp import machine, togk, letgk
from t10_n_rgf import tmbn
from t10_d_dot import skip_ty, skip_in, cls_to, load_nfl
from t10_e_doa import lift_from
from t10_u_s2s import expose
import t8alib as A8
import t7c_h_lst as LST
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]

# ------------------------------------------------------------ accAnd_runs: acc = A , the flag O , r1 = X
IFO = 'if ( O = 1o , A , 0 )'
DATA_ACA = ((STKD('D'), 'A e. NN0', 'B e. NN0'), (LT2('A'), WG('X')), DEQ(1, EWg('A', 'X')))
TREE_ACA = TREE0('aca', DATA_ACA)
ACA_ENTRY = FRAGS['aca'].entry()
CONCL_ACA = TRI(CLN(ACA_ENTRY, NFL('O'), 'D'), CLN('E', S, UP('D', '1', EWg(IFO, 'X'))), '( ( 2 x. ( TMB ` B ) ) + 1 )')
add12('tmiaca', TREE_ACA, CONCL_ACA)


def nfl_all(w, pc, O, truth, ost):
    """( pc -> A. m e. NFL( O ) ( TMfl ` m ) = 1o ) from ost : ( pc -> O = 1o ), or the negated form from
    ost : ( pc -> -. O = 1o )"""
    s = w.s
    N0 = NFL(O)
    pm = '( %s /\\ m e. %s )' % (pc, N0)
    mm, mf = A8.nfl_unpack(w, pm, O, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, N0)))
    if truth:
        e = s([mf, lift_from(w, pc, pm, ost)], 'eqtrd', '( %s -> ( TMfl ` m ) = 1o )' % pm)
        return s([e], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (pc, N0))
    q = s([mf], 'eqeq1d', '( %s -> ( ( TMfl ` m ) = 1o <-> O = 1o ) )' % pm)
    n = s([lift_from(w, pc, pm, ost), q], 'mtbird', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)
    return s([n], 'ralrimiva', '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (pc, N0))


def skip_to_s(w, pc, mk, N0):
    """( pc -> A. r e. N0 ( ( _I |` TMSt ) ` r ) e. S ) for N0 = { h e. TMSt | ... }"""
    s = w.s
    pr = '( %s /\\ r e. %s )' % (pc, N0)
    rin = s([], 'simpr', '( %s -> r e. %s )' % (pr, N0))
    rt = s([rin, w.inst('elrabi')], 'syl', '( %s -> r e. TMSt )' % pr)
    fv = s([rt, w.inst('fvresi')], 'syl', '( %s -> ( ( _I |` TMSt ) ` r ) = r )' % pr)
    rs = s([rt, lift_from(w, pc, pr, s([mk['seq']], 'eqcomd', '( %s -> TMSt = %s )' % (pc, S)))], 'eleqtrd', '( %s -> r e. %s )' % (pr, S))
    return s([s([fv, rs], 'eqeltrd', '( %s -> ( ( _I |` TMSt ) ` r ) e. %s )' % (pr, S))], 'ralrimiva',
             '( %s -> A. r e. %s ( ( _I |` TMSt ) ` r ) e. %s )' % (pc, N0, S))


def encgam0(w, ph):
    """( ph -> ( encNatGam ` 0 ) = (/) )"""
    s = w.s
    e0 = s([closed(w, ph, '0nn0', '0 e. NN0'), w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` 0 ) = ( inclBool o. ( encodeNat ` 0 ) ) )' % ph)
    e0b = s([closed(w, ph, 'encnat0', '( encodeNat ` 0 ) = (/)')], 'coeq2d', '( %s -> ( inclBool o. ( encodeNat ` 0 ) ) = ( inclBool o. (/) ) )' % ph)
    e0c = closed(w, ph, 'co02', '( inclBool o. (/) ) = (/)')
    return s([e0, e0b, e0c], '3eqtrd', '( %s -> ( encNatGam ` 0 ) = (/) )' % ph)


def widen_post(w, pc, B, R, N0, lab_e='E'):
    """the post class N0 of the Run to S (~ tm2hssd )"""
    Dc = R.S.D
    ss = clnss(w, pc, lab_e, N0, S, Dc, B.ss(N0))
    cfg = cfgcl(w, pc, lab_e, S, Dc, B.mk['tv'], B.c[LAB(lab_e)] if LAB(lab_e) in B.c.all() else B.ex[LAB(lab_e)],
                closed(w, pc, 'ssid', '%s C_ %s' % (S, S)), R.S.memb)
    R.tri = hrssd(w, pc, B.mk['phm'], R.tri, R.C0, R.cur, R.n, CLN(lab_e, S, Dc), ss, cfg)
    R.cur = CLN(lab_e, S, Dc)


def tmiaca():
    lab = 'tmiaca'
    T0 = numtree(TREE_ACA)
    ph = cj(T0)
    w = W(lab, 'Lean\'s ` accAnd_runs ` at the machine: ` ite flag skip ( dropNum 1 ; pushNum 1 0 ) ` from the flag '
               'class ` O ` with the accumulator ` A ` on 1 leaves ` if ( O = 1o , A , 0 ) ` on 1, every other stack '
               'restored, within ` 2 B b + 1 ` steps (by cases on ` O = 1o ` ; ~ tm2lbrt , ~ tm2fbrg , ~ tmidropnb , '
               '~ tm2fpshn ).')
    s = w.s
    P0, P1, P2, P3 = PL('P', 0), PL('P', 1), PL('P', 2), PL('P', 3)
    D0 = PL(P3, 0)
    outs = []
    for tr in (True, False):
        cc = 'O = 1o' if tr else '-. O = 1o'
        T = (T0, cc)
        pc = cj(T)
        c0 = Ctx(w, pc, T)
        an, bn, xg = c0['A e. NN0'], c0['B e. NN0'], c0[WG('X')]
        B = Base(w, pc, T, N8, 'aca', {'1': (EWg('A', 'X'), ewg_(w, pc, 'A', an, 'X', xg))})
        c, mk = B.c, B.mk
        R = B.run()
        N0 = NFL('O')
        ost = c[cc]
        ex = {SSS(N0): B.ss(N0)}
        E1 = EWg(IFO, 'X')
        cl = Closure(w, pc, {'A': ('NN0', an), 'B': ('NN0', bn)})
        TB = '( TMB ` B )'
        cl.leaf(TB, 'NN0', tmbn(w, pc, 'B', bn))
        tb1 = s([s([bn, w.inst('tmbcl')], 'syl', '( %s -> %s e. NN )' % (pc, TB)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pc, TB))
        if tr:
            ex[STMT(GT(D0))] = gotocl(w, pc, mk['tv'], D0, B.ex[LAB(D0)])
            ex['A. m e. %s ( TMfl ` m ) = 1o' % N0] = nfl_all(w, pc, 'O', True, ost)
            B.call(R, 'tm2lbrt', {'A': P0, 'C': 'TMfl', 'E': P1, 'Q': GT(D0), 'N': N0}, ex, [])
            B.call(R, 'tm2flg', {'A': P1, 'E': 'E', 'F': LID, 'N': N0, "N'": S},
                   {LTY(LID): skip_ty(w, pc, mk), SSS(N0): B.ss(N0), SSS(S): closed(w, pc, 'ssid', '%s C_ %s' % (S, S)),
                    'A. r e. %s ( %s ` r ) e. %s' % (N0, LID, S): skip_to_s(w, pc, mk, N0)}, [])
            cur, out = R.normalize(N8)
            assert out == [], out
            # D = UP( D , 1 , EW( IFO , X ) ) : IFO = A
            ia = s([ost], 'iftrued', '( %s -> %s = A )' % (pc, IFO))
            e1 = s([s([s([ia], 'eqcomd', '( %s -> A = %s )' % (pc, IFO))], 'fveq2d', '( %s -> ( encNatGam ` A ) = ( encNatGam ` %s ) )' % (pc, IFO))],
                   'oveq1d', '( %s -> %s = %s )' % (pc, EWg('A', 'X'), E1))
            dk = s([c[DEQ(1, EWg('A', 'X'))], e1], 'eqtrd', '( %s -> ( D ` 1 ) = %s )' % (pc, E1))
            up = upidv(w, pc, 'D', '1', E1, dk, mk['tv'], B.dd, mk['k']['1']['kd'])
            deq = s([up], 'eqcomd', '( %s -> D = %s )' % (pc, UP('D', '1', E1)))
            t, C, D, n = hrrw(w, pc, R.tri, R.C0, R.cur, R.n, deq=clneq(w, pc, 'E', S, deq, 'D', UP('D', '1', E1)))
        else:
            ex[STMT(GT(P1))] = gotocl(w, pc, mk['tv'], P1, B.ex[LAB(P1)])
            ex['A. m e. %s -. ( TMfl ` m ) = 1o' % N0] = nfl_all(w, pc, 'O', False, ost)
            B.call(R, 'tm2fbrg', {'A': P0, 'C': 'TMfl', 'E': D0, 'Q': GT(P1), 'N': N0}, ex, [])
            Son, old = expose(w, pc, B, R, '1')
            B.call(R, 'tmidropnb', {'K': '1', 'F': 'A', 'N': 'B', 'X': 'X', 'O': 'O', 'P': P3, 'E': P2},
                   {'A e. NN0': an, 'B e. NN0': bn, LT2('A'): c[LT2('A')], WG('X'): xg}, [('1', 'X', xg)], on=(Son, old))
            K4 = '( <" 4 "> ++ X )'
            g4 = B.g(K4, wg4(w, pc, 'X', xg))
            B.call(R, 'tm2fpshn', {'A': P2, 'E': 'E', 'K': '1', 'Z': '4', 'N': N0},
                   {'4 e. %s' % GX('1'): letgk(w, pc, mk, '4', '1', closed(w, pc, 'gamma4', "4 e. Gamma'")), SSS(N0): B.ss(N0)},
                   [('1', K4, g4)])
            cur, out = R.normalize(N8)
            assert out == [('1', K4)], out
            widen_post(w, pc, B, R, N0)
            # ( <" 4 "> ++ X ) = EW( IFO , X ) : IFO = 0 , encNatGam 0 = (/)
            i0 = s([ost], 'iffalsed', '( %s -> %s = 0 )' % (pc, IFO))
            eg = s([s([i0], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` 0 ) )' % (pc, IFO)), encgam0(w, pc)], 'eqtrd',
                   '( %s -> ( encNatGam ` %s ) = (/) )' % (pc, IFO))
            e2 = s([s([eg], 'oveq1d', '( %s -> %s = ( (/) ++ %s ) )' % (pc, E1, K4)), s([g4, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (pc, K4, K4))],
                   'eqtrd', '( %s -> %s = %s )' % (pc, E1, K4))
            ue = upeq(w, pc, 'D', '1', s([e2], 'eqcomd', '( %s -> %s = %s )' % (pc, K4, E1)), K4, E1)
            t, C, D, n = hrrw(w, pc, R.tri, R.C0, R.cur, R.n, deq=clneq(w, pc, 'E', S, ue, UP('D', '1', K4), UP('D', '1', E1)))
        BND = '( ( 2 x. %s ) + 1 )' % TB
        le = linarith(w, pc, [tb1], '%s <_ %s' % (n, BND), closure=cl)
        outs.append(hrle(w, pc, mk['phm'], t, C, D, n, BND, cl.mem(BND, 'NN0'), le))
    st = s(outs, 'pm2.61dan', '( %s -> %s )' % (ph, CONCL_ACA))
    finish(w, st, lab)
    return w.run()


# ------------------------------------------------------------ the generic accumulator loop (Lean accLoopF_runs)
# letters: A0 (push comma) P0 (push bit 1) P1 (peek) A (branch) A' (body entry) A" (peek back) E' (pop) E" (load)
# Q (isZero's label function) Q1 (dropNum's) E (exit); data L R D P Y U G B
from t7clib import setup, selfval
NQ_ = '{ q e. %s | -. ( %s ` q ) = 1o }' % (S, CNFL)
NL_ = '( # ` L )'
_GM = {'K': '5', 'F': 'TMrdBra', 'C': CNFL, 'N': S, 'E': "E'"}
_GA, _GC = split_imp(stmt('tm2lfes'))
GTREE = tsub(parse_conj(_GA), _GM)
GCONCL = tsub_text(_GC, _GM)
_fl = flat(GTREE)
PER = [t for t in _fl if t.startswith('A. j e. ( 0 ..^ ')][0]
FTY = [t for t in _fl if t.startswith('P : ')][0]
FCOL = [t for t in _fl if t.startswith('A. j e. ( 0 ... ')][0]
COLF = lambda j: '( ( P ` %s ) ` 5 ) = ( ( encListB ` ( L substr <. %s , %s >. ) ) ++ R )' % (j, j, NL_)
assert FCOL == 'A. j e. ( 0 ... %s ) %s' % (NL_, COLF('j')), FCOL
V1_ = 'if ( G = 0 , 1o , (/) )'
V2_ = 'if ( G = 0 , (/) , 1o )'
W2R = '( <" 2 "> ++ R )'
P0EQ = '( P ` 0 ) = %s' % UP('D', '1', EWg('1', DK(1)))
PNEQ = '( P ` %s ) = %s' % (NL_, UP(UP('D', '1', EWg('G', DK(1))), '5', W2R))
SUM_ = 'sum_ j e. ( 0 ..^ %s ) ( ( Y ` j ) + 2 )' % NL_
SUMLE = '%s <_ U' % SUM_
EQ_P1, EQ_A, EQ_A2 = MEQ('P1', PEEK('5', 'TMrdBra', GT('A'))), MEQ('A', BRANCH(CNFL, GT("A'"), GT("E'"))), MEQ('A"', PEEK('5', 'TMrdBra', GT('A')))
for _e in (EQ_P1, EQ_A, EQ_A2):
    assert _e in _fl, _e
EQS_ACL = ((MEQ('A0', PUSH('1', CONST('4'), GT('P0'))), MEQ('P0', PUSH('1', CONST(BIT1_), GT('P1'))), EQ_P1),
           (EQ_A, EQ_A2, MEQ("E'", POP('5', PID, GT(PL('Q', 0))))),
           (MEQ('E"', LOAD(L_NOTF, GT(PL('Q1', 0)))), 'TMIiz 1 2 T M Q E"', 'TMIdrop 1 T M Q1 E'))
LABS_ACL = ((LAB('A0'), LAB('P0'), LAB('P1')), (LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E"'), LAB('E')))
DATA_ACL = ((('L e. Word Word %s' % BITS, WG('R'), STKD('D')), ('G e. NN0', 'B e. NN0', LT2('G')), 'U e. NN0'),
            ((FTY, FCOL), (P0EQ, PNEQ), (PER, SUMLE)))
TREE_ACL = ((T_PHM7, EQS_ACL), (LABS_ACL, DATA_ACL))
CONCL_ACL = TRI(CLN('A0', S, 'D'), CLN('E', NFL(V2_), UP('D', '5', 'R')), '( U + ( ( 2 x. ( TMB ` B ) ) + 6 ) )')
add12('tmiacl', TREE_ACL, CONCL_ACL)


class Plain(Base):
    """a Base without a fragment predicate: the machine, the list handlers' interface, the stacks D"""
    def __init__(self, w, ph, T, eqs=None):
        self.w, self.ph, self.ks = w, ph, N8
        c, mk, ne, ex = setup(w, ph, T, N8)
        ex.update(LST.handler_extra(w, ph, mk, LST.IFACE))
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        self.dd = c[STKD('D')]
        vals = {k: selfval(w, ph, mk, 'D', self.dd, k) for k in N8}
        self.gam = {v[0]: v[2] for v in vals.values()}
        for k, (txt, gst) in (eqs or {}).items():
            vals[k] = (txt, c['( D ` %s ) = %s' % (k, txt)], gst)
            self.gam[txt] = gst
        self.S0 = Stacks(w, ph, mk, 'D', self.dd, ne, vals)


def notif_fleq(w, cond):
    """fleq for ~ load_nfl at ` flag := !flag ` from ` if ( cond , 1o , (/) ) ` to ` if ( cond , (/) , 1o ) ` """
    V1 = 'if ( %s , 1o , (/) )' % cond
    V2 = 'if ( %s , (/) , 1o )' % cond
    IF = lambda t: 'if ( %s = 1o , (/) , 1o )' % t

    def fleq(pr, f):
        s = w.s
        x = s([f], 'eqeq1d', '( %s -> ( ( TMfl ` r ) = 1o <-> %s = 1o ) )' % (pr, V1))
        i1 = s([x], 'ifbid', '( %s -> %s = %s )' % (pr, IF('( TMfl ` r )'), IF(V1)))
        pt = '( %s /\\ %s )' % (pr, cond)
        pn = '( %s /\\ -. %s )' % (pr, cond)
        a1 = s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = 1o )' % (pt, V1))
        b1 = s([a1], 'iftrued', '( %s -> %s = (/) )' % (pt, IF(V1)))
        c1 = s([s([], 'simpr', '( %s -> %s )' % (pt, cond))], 'iftrued', '( %s -> %s = (/) )' % (pt, V2))
        t1 = s([b1, c1], 'eqtr4d', '( %s -> %s = %s )' % (pt, IF(V1), V2))
        a2 = s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond))], 'iffalsed', '( %s -> %s = (/) )' % (pn, V1))
        n0 = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o'), s([], 'neneq', '( (/) =/= 1o -> -. (/) = 1o )')], 'ax-mp', '-. (/) = 1o')
        nn = s([s([n0], 'a1i', '( %s -> -. (/) = 1o )' % pn), s([a2], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (pn, V1))], 'mtbird',
               '( %s -> -. %s = 1o )' % (pn, V1))
        b2 = s([nn], 'iffalsed', '( %s -> %s = 1o )' % (pn, IF(V1)))
        c2 = s([s([], 'simpr', '( %s -> -. %s )' % (pn, cond))], 'iffalsed', '( %s -> %s = 1o )' % (pn, V2))
        t2 = s([b2, c2], 'eqtr4d', '( %s -> %s = %s )' % (pn, IF(V1), V2))
        tt = s([t1, t2], 'pm2.61dan', '( %s -> %s = %s )' % (pr, IF(V1), V2))
        return s([i1, tt], 'eqtrd', '( %s -> %s = %s )' % (pr, IF('( TMfl ` r )'), V2))
    return fleq


def sum_nn0(w, ph, per, NL):
    """( ph -> sum_ j e. ( 0 ..^ NL ) ( ( Y ` j ) + 2 ) e. NN0 ) from per : ( ph -> PER ) (the sum is formed over ` i `
    and renamed: ~ fsumnn0cl has ` $d ph k ` and the antecedent binds ` j ` )"""
    s = w.s
    PERB = PER[len('A. j e. ( 0 ..^ %s ) ' % NL):]
    A_ = '( 0 ..^ %s )' % NL
    ri = s([s([], 'simpl', '( %s -> ( Y ` j ) e. NN0 )' % PERB)], 'ralimi', '( %s -> A. j e. %s ( Y ` j ) e. NN0 )' % (PER, A_))
    rj = s([per, ri], 'syl', '( %s -> A. j e. %s ( Y ` j ) e. NN0 )' % (ph, A_))
    cb = s([s([s([], 'fveq2', '( j = i -> ( Y ` j ) = ( Y ` i ) )')], 'eleq1d', '( j = i -> ( ( Y ` j ) e. NN0 <-> ( Y ` i ) e. NN0 ) )')],
           'cbvralvw', '( A. j e. %s ( Y ` j ) e. NN0 <-> A. i e. %s ( Y ` i ) e. NN0 )' % (A_, A_))
    rii = s([rj, cb], 'sylib', '( %s -> A. i e. %s ( Y ` i ) e. NN0 )' % (ph, A_))
    pi = '( %s /\\ i e. %s )' % (ph, A_)
    yn = s([rii], 'r19.21bi', '( %s -> ( Y ` i ) e. NN0 )' % pi)
    y2 = s([yn, closed(w, pi, '2nn0', '2 e. NN0')], 'nn0addcld', '( %s -> ( ( Y ` i ) + 2 ) e. NN0 )' % pi)
    fi = s([s([], 'fzofi', '%s e. Fin' % A_)], 'a1i', '( %s -> %s e. Fin )' % (ph, A_))
    si = s([fi, y2], 'fsumnn0cl', '( %s -> sum_ i e. %s ( ( Y ` i ) + 2 ) e. NN0 )' % (ph, A_))
    cs = s([s([s([], 'fveq2', '( i = j -> ( Y ` i ) = ( Y ` j ) )')], 'oveq1d', '( i = j -> ( ( Y ` i ) + 2 ) = ( ( Y ` j ) + 2 ) )')],
           'cbvsumv', 'sum_ i e. %s ( ( Y ` i ) + 2 ) = sum_ j e. %s ( ( Y ` j ) + 2 )' % (A_, A_))
    return s([s([cs], 'a1i', '( %s -> sum_ i e. %s ( ( Y ` i ) + 2 ) = sum_ j e. %s ( ( Y ` j ) + 2 ) )' % (ph, A_, A_)), si], 'eqeltrrd',
             '( %s -> sum_ j e. %s ( ( Y ` j ) + 2 ) e. NN0 )' % (ph, A_))


def tmiacl():
    lab = 'tmiacl'
    T = numtree(TREE_ACL)
    ph = cj(T)
    w = W(lab, 'Lean\'s ` accLoopF_runs ` at the machine, generic in the body: ` pushNum 1 1 ` , the entry loop '
               '` forEntries 5 body ` (~ tm2lfes at ` readBra ` , ` !flag ` , the body one triple per entry along the stack '
               'family ` P ` ), ` popTop 5 ` (~ tm2lpop ), ` isZero 1 2 ` (~ tmiizbs ) on the final accumulator ` G ` , '
               '` load\' ( flag := !flag ) ` and ` dropNum 1 ` (~ tmidropnb ): the flag is ` G =/= 0 ` , the list\'s '
               '` bra ` is gone from 5, within the entries\' budget plus ` 2 B b + 6 ` .')
    s = w.s
    B = Plain(w, ph, T)
    c, mk, ex = B.c, B.mk, B.ex
    ex.update(unfold_all(w, ph, c['TMIiz 1 2 T M Q E"'], 'iz', ['1', '2'], 'Q', 'E"', rec=False))
    ex.update(unfold_all(w, ph, c['TMIdrop 1 T M Q1 E'], 'drop', ['1'], 'Q1', 'E', rec=False))
    tv, dd = mk['tv'], B.dd
    rw, ll, gn, bn, un = c[WG('R')], c['L e. Word Word %s' % BITS], c['G e. NN0'], c['B e. NN0'], c['U e. NN0']
    nl = s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, NL_))
    g = lambda k: B.S0.vals[k][2]
    ssid = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    # 1-2. pushNum 1 1
    R = B.run()
    K4 = '( <" 4 "> ++ ( D ` 1 ) )'
    g4 = B.g(K4, wg4(w, ph, DK(1), g('1')))
    B.call(R, 'tm2fpshn', {'A': 'A0', 'E': 'P0', 'K': '1', 'Z': '4', 'N': S},
           {'4 e. %s' % GX('1'): letgk(w, ph, mk, '4', '1', closed(w, ph, 'gamma4', "4 e. Gamma'")), SSS(S): ssid}, [('1', K4, g4)])
    bg1 = s([closed(w, ph, '1oel2o', '1o e. 2o'), w.inst('bitgamma')], 'syl', "( %s -> %s e. Gamma' )" % (ph, BIT1_))
    K41 = '( <" %s "> ++ %s )' % (BIT1_, K4)
    g41 = B.g(K41, wgcat(w, ph, '<" %s ">' % BIT1_, K4, s([bg1], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ph, BIT1_)), g4))
    B.call(R, 'tm2fpshn', {'A': 'P0', 'E': 'P1', 'K': '1', 'Z': BIT1_, 'N': S},
           {'%s e. %s' % (BIT1_, GX('1')): s([bg1, mk['k']['1']['ge']], 'eleqtrrd', '( %s -> %s e. %s )' % (ph, BIT1_, GX('1'))), SSS(S): ssid},
           [('1', K41, g41)])
    cur, out = R.normalize(N8)
    assert out == [('1', K41)], out
    E1 = EWg('1', DK(1))
    e1 = s([s([g('1'), w.inst('tmienc1')], 'syl', '( %s -> %s = %s )' % (ph, E1, K41))], 'eqcomd', '( %s -> %s = %s )' % (ph, K41, E1))
    ue = upeq(w, ph, 'D', '1', e1, K41, E1)
    p0 = s([ue, s([c[P0EQ]], 'eqcomd', '( %s -> %s = ( P ` 0 ) )' % (ph, UP('D', '1', E1)))], 'eqtrd',
           '( %s -> %s = ( P ` 0 ) )' % (ph, UP('D', '1', K41)))
    t1, C1, D1, n1 = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=clneq(w, ph, 'P1', S, p0, UP('D', '1', K41), '( P ` 0 )'))
    assert D1 == CLN('P1', S, '( P ` 0 )'), D1
    # 3. the entry loop
    st = Bld(w, ph, c, dict(ex))(GTREE)
    t2 = s([st, w.inst('tm2lfes')], 'syl', '( %s -> %s )' % (ph, GCONCL))
    C2, D2, n2 = triple_parts(GCONCL)
    assert C2 == D1, (C2, D1)
    t12 = hrseq(w, ph, mk['phm'], t1, t2, C1, D1, D2, n1, n2)
    n12 = '( %s + %s )' % (n1, n2)
    # 4. popTop 5 at E' on ( P ` # L )
    PN = '( P ` %s )' % NL_
    nfz = s([nl, w.inst('nn0fz0')], 'sylib', '( %s -> %s e. ( 0 ... %s ) )' % (ph, NL_, NL_))
    cg, new = w.wcongr(COLF('j'), {'j': NL_}, 'j = %s' % NL_, {'j': s([], 'id', '( j = %s -> j = %s )' % (NL_, NL_))})
    assert new == COLF(NL_), new
    pkn = s([cg, c[FCOL], nfz], 'rspcdva', '( %s -> %s )' % (ph, COLF(NL_)))
    DR = '( L substr <. %s , %s >. )' % (NL_, NL_)
    e2 = s([s([closed(w, ph, 'swrd00', '%s = (/)' % DR)], 'fveq2d', '( %s -> ( encListB ` %s ) = ( encListB ` (/) ) )' % (ph, DR)),
            closed(w, ph, 'tm2lencb0', '( encListB ` (/) ) = <" 2 ">')], 'eqtrd', '( %s -> ( encListB ` %s ) = <" 2 "> )' % (ph, DR))
    hd = s([pkn, s([e2], 'oveq1d', '( %s -> ( ( encListB ` %s ) ++ R ) = %s )' % (ph, DR, W2R))], 'eqtrd', '( %s -> ( %s ` 5 ) = %s )' % (ph, PN, W2R))
    pst = s([c[FTY], nfz], 'ffvelcdmd', '( %s -> %s e. ( TM2Stk ` T ) )' % (ph, PN))
    ssq = s([s([], 'ssrab2', '%s C_ %s' % (NQ_, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, NQ_, S))
    POPI_ = 'A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (S, PID, S)
    POPQ_ = 'A. r e. %s ( %s ` <. r , ( inl ` 2 ) >. ) e. %s' % (NQ_, PID, S)
    popq = s([ssq, ex[POPI_], w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ph, POPQ_))
    ex3 = dict(ex)
    ex3.update({SSS(NQ_): ssq, SSS(S): ssid, STKD(PN): pst, '( %s ` 5 ) = %s' % (PN, W2R): hd,
                "2 e. Gamma'": closed(w, ph, 'gamma2', "2 e. Gamma'"), WG('R'): rw, POPQ_: popq})
    t3, cc3 = inst(w, ph, 'tm2lpop', {'A': "E'", 'E': PL('Q', 0), 'K': '5', 'F': PID, 'D': PN, 'Z': '2', 'X': 'R', 'N': NQ_, "N'": S},
                   Bld(w, ph, c, ex3))
    C3, D3, n3 = triple_parts(cc3)
    assert C3 == D2, (C3, D2)
    t123 = hrseq(w, ph, mk['phm'], t12, t3, C1, D2, D3, n12, n3)
    n123 = '( %s + %s )' % (n12, n3)
    # 5. UP( P # L , 5 , R ) = UP( UP( D , 5 , R ) , 1 , EW( G , D 1 ) )
    EG = EWg('G', DK(1))
    B.g('R', rw)
    B.g(EG, ewg_(w, ph, 'G', gn, DK(1), g('1')))
    B.g(W2R, wgcat(w, ph, '<" 2 ">', 'R', s([closed(w, ph, 'gamma2', "2 e. Gamma'")], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % ph), rw))
    S5 = B.S0.upd('5', 'R', B.gam['R'])
    S51 = S5.upd('1', EG, B.gam[EG])
    nst, outn = stk_normalize(w, ph, mk, 'D', dd, B.ne, [('1', EG), ('5', W2R), ('5', 'R')], B.gam, ['0', '5', '1', '2', '3', '4', '6', '7'])
    assert outn == [('5', 'R'), ('1', EG)], outn
    UPN = UP(PN, '5', 'R')
    r1, x1 = w.rewrite(UPN, {PN: (UP(UP('D', '1', EG), '5', W2R), c[PNEQ])}, ph)
    deq = s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (ph, UPN, S51.D))
    assert triple_D(D3) == UPN, D3
    t123, _, D3b, _ = hrrw(w, ph, t123, C1, D3, n123, deq=clneq(w, ph, PL('Q', 0), S, deq, UPN, S51.D))
    # 6. isZero 1 2 , flag := !flag , dropNum 1
    R2 = B.run(S51)
    B.call(R2, 'tmiizbs', {'K': '1', 'I': '2', 'F': 'G', 'N': 'B', 'X': DK(1), 'P': 'Q', 'E': 'E"'},
           {'G e. NN0': gn, 'B e. NN0': bn, LT2('G'): c[LT2('G')], WG(DK(1)): g('1')}, [])
    kw = lambda t: dict(fl='if ( ( TMfl ` %s ) = 1o , (/) , 1o )' % t)
    ex4 = {LTY(L_NOTF): lset_ty2(w, ph, mk, L_NOTF, kw), SSS(NFL(V1_)): B.ss(NFL(V1_)), SSS(NFL(V2_)): B.ss(NFL(V2_)),
           'A. r e. %s ( %s ` r ) e. %s' % (NFL(V1_), L_NOTF, NFL(V2_)): load_nfl(w, ph, mk, L_NOTF, kw, V1_, V2_, notif_fleq(w, 'G = 0'))}
    B.call(R2, 'tm2flg', {'A': 'E"', 'E': PL('Q1', 0), 'F': L_NOTF, 'N': NFL(V1_), "N'": NFL(V2_)}, ex4, [])
    B.call(R2, 'tmidropnb', {'K': '1', 'F': 'G', 'N': 'B', 'X': DK(1), 'O': V2_, 'P': 'Q1', 'E': 'E'},
           {'G e. NN0': gn, 'B e. NN0': bn, LT2('G'): c[LT2('G')], WG(DK(1)): g('1')}, [('1', DK(1), g('1'))], on=(S5, []))
    e5 = updnv(w, ph, 'D', '5', 'R', '1', tv, dd, mk['k']['5']['kd'], s([rw], 'elexd', '( %s -> R e. _V )' % ph), mk['k']['1']['kd'], B.ne('1', '5'))
    fin = upidv(w, ph, S5.D, '1', DK(1), e5, tv, S5.memb, mk['k']['1']['kd'])
    t4, C4, D4, n4 = R2.tri, R2.C0, R2.cur, R2.n
    assert triple_D(D4) == UP(S5.D, '1', DK(1)), D4
    t4, C4, D4, n4 = hrrw(w, ph, t4, C4, D4, n4, deq=clneq(w, ph, 'E', NFL(V2_), fin, UP(S5.D, '1', DK(1)), S5.D))
    assert C4 == D3b, (C4, D3b)
    t = hrseq(w, ph, mk['phm'], t123, t4, C1, D3b, D4, n123, n4)
    n = '( %s + %s )' % (n123, n4)
    assert D4 == CLN('E', NFL(V2_), UP('D', '5', 'R')), D4
    # the bound
    cl = Closure(w, ph, {'B': ('NN0', bn), 'U': ('NN0', un)})
    TB = '( TMB ` B )'
    cl.leaf(TB, 'NN0', tmbn(w, ph, 'B', bn))
    cl.leaf(SUM_, 'NN0', sum_nn0(w, ph, c[PER], NL_))
    BND = '( U + ( ( 2 x. %s ) + 6 ) )' % TB
    le = linarith(w, ph, [c[SUMLE]], '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, C1, D4, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
