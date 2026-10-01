"""T5: the composites over the two-operand loops: ~ tm2fcmp (` cmpFrag_runs ` :
the initialising load, then ~ tm2fcml ) and ~ tm2fadd (` add_runs ` : the
initialising load-and-push, ~ tm2fadl , a push and ~ tm2fmov )."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *
from t5_f_rd import BODY, STEPX, STEPY, HA, HDL
from t5_g_core import BI, N0, XF, YF, NF, OFC, DI, RESTQ, LOADG
from t5_h_loop import inst_v

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GJ, GI, GH = GX('K'), GX('J'), GX('I'), GX('H')
GE = GT('E')
CC, CP, CD, C0, C1 = ['%s e. ( 2o ^m %s )' % (x, SS) for x in ('C', "C'", 'C"', 'C0', 'C1_')]
FT, FPT = 'F e. %s' % HDL('K'), "F' e. %s" % HDL('J')
GTY = 'G e. ( %s ^m %s )' % (SS, SS)
LTY = 'L e. ( %s ^m %s )' % (SS, SS)


def hyps_i(cmp):
    n0 = N0(cmp)
    return dict(
        famn='A. i e. ( 0 ... %s ) ( %s C_ %s /\\ %s C_ %s )' % (n0, NF('i'), SS, OFC('i'), SS),
        famxy='A. i e. ( 0 ... ( %s + 1 ) ) ( %s e. Word %s /\\ %s e. Word %s )' % (n0, XF('i'), GK, YF('i'), GJ),
        steps='A. i e. ( 0 ... %s ) ( %s /\\ %s )' % (n0, STEPX('i'), STEPY('i')),
        has='A. i e. ( 0 ... %s ) %s' % (n0, HA('i')),
        bis='A. i e. ( 0 ..^ %s ) %s' % (n0, BI('i', cmp)))


def tm2fcmp():
    lab = 'tm2fcmp'
    cmp = True
    n0 = 'B'
    Q = GE
    REST = RESTQ(cmp, Q)
    BODYQ = BODY(REST)
    INIT = LOAD('L', GT('A'))
    h = hyps_i(cmp)
    ON = OFC(n0)
    EXIT = "A. p e. %s ( ( C\" ` p ) = 1o /\\ p e. N' )" % ON
    INITH = 'A. r e. N0 ( L ` r ) e. %s' % NF('0')
    X0, Y0 = '( X ` 0 ) = ( D ` K )', '( Y ` 0 ) = ( D ` J )'
    tree = (((PHM, "( M ` A' ) = %s" % INIT, '( M ` A ) = %s' % BODYQ),
             (("A' e. %s" % LL, 'A e. %s' % LL, 'E e. %s' % LL), ('K e. %s' % DG, 'J e. %s' % DG), 'K =/= J'),
             ((CC, CP, CD), ((FT, FPT), (GTY, LTY)), (('B e. NN0', 'D e. %s' % STK_T), ('N0 C_ %s' % SS, "N' C_ %s" % SS), INITH))),
            (((h['famn'], h['famxy']), (X0, Y0)), ((h['steps'], h['has']), (h['bis'], EXIT))))
    ph = cj(tree)
    w = W(lab, 'The comparator ` cmpFrag ` of TM/Arith.lean: the initialising load at ` A\' ` '
               '(Lean: ` cmp := .eq , ra := none , ... ` , ~ tm2flg ) moves the state from ` N0 ` '
               'into ` ( N ` 0 ) ` , then ~ tm2fcml runs the loop; the verdict is in the exit '
               'class ` N\' ` and the operands are consumed.  Lean: ` cmpFrag_runs ` (the '
               'N-level ` cmpBits_eq_compare ` is T4\'s).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    dd = c['D e. %s' % STK_T]
    n0cl = c['B e. NN0']
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([n0cl, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ %s )' % (ph, n0))
    z0fz = w.s([w.s([z0a, n0cl, ge0], '3jca', '( %s -> ( 0 e. NN0 /\\ %s e. NN0 /\\ 0 <_ %s ) )' % (ph, n0, n0)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, n0))
    fn0, _ = inst_v(w, ph, c[h['famn']], '( %s C_ %s /\\ %s C_ %s )' % (NF('i'), SS, OFC('i'), SS), 'i', '0', z0fz)
    n0s = w.s([fn0], 'simpld', '( %s -> %s C_ %s )' % (ph, NF('0'), SS))
    t1 = applylem(w, ph, 'tm2flg',
                  ((phm, c["( M ` A' ) = %s" % INIT]), (c["A' e. %s" % LL], c['A e. %s' % LL], dd),
                   (c[LTY], (c['N0 C_ %s' % SS], n0s), c[INITH])),
                  HR(CLN("A'", 'N0', 'D'), 'T', 'M', CLN('A', NF('0'), 'D'), '1'))
    X1, Y1 = XF('( %s + 1 )' % n0), YF('( %s + 1 )' % n0)
    FIN = UP(UP('D', 'K', X1), 'J', Y1)
    t2 = applylem(w, ph, 'tm2fcml',
                  (((phm, c['( M ` A ) = %s' % BODYQ]),
                    ((c['A e. %s' % LL], c['E e. %s' % LL]), (c['K e. %s' % DG], c['J e. %s' % DG]), c['K =/= J']),
                    ((c[CC], c[CP], c[CD]), ((c[FT], c[FPT]), c[GTY]), (n0cl, (dd, c["N' C_ %s" % SS])))),
                   (((c[h['famn']], c[h['famxy']]), (c[X0], c[Y0])), ((c[h['steps']], c[h['has']]), (c[h['bis']], c[EXIT])))),
                  HR(CLN('A', NF('0'), 'D'), 'T', 'M', CLN('E', "N'", FIN), '( %s + 1 )' % n0))
    tall = hrseq(w, ph, phm, t1, t2, CLN("A'", 'N0', 'D'), CLN('A', NF('0'), 'D'), CLN('E', "N'", FIN), '1', '( %s + 1 )' % n0)
    bound(w, ph, phm, tall, CLN("A'", 'N0', 'D'), CLN('E', "N'", FIN), '( 1 + ( %s + 1 ) )' % n0, '( %s + 2 )' % n0,
          {n0: n0cl}, qed=True)
    return w.run()


def tm2fadd():
    lab = 'tm2fadd'
    cmp = False
    n0 = N0(cmp)
    Q = BRANCH('C0', PUSH('I', "P'", GE), GE)
    REST = RESTQ(cmp, Q)
    BODYQ = BODY(REST)
    INIT = LOAD('L', PUSH('I', CONSTF('T', 'Q'), GT('A')))
    PUSHH = PUSH('H', CONSTF('T', 'Q'), GT("E'"))
    MOV = POP('I', 'F"', BRANCH('C1_', PUSH('H', 'P"', GT("E'")), GT('E"')))
    h = hyps_i(cmp)
    ON = OFC(n0)
    IFC = "A. p e. %s ( ( ( C\" ` p ) = 1o /\\ ( C0 ` p ) = 1o ) /\\ ( ( P' ` p ) = Z' /\\ p e. N' ) )" % ON
    IFN = "A. p e. %s ( ( C\" ` p ) = 1o /\\ -. ( C0 ` p ) = 1o /\\ p e. N' )" % ON
    EXIT = "( ( %s /\\ W = ( Z ++ <\" Z' \"> ) ) \\/ ( %s /\\ W = Z ) )" % (IFC, IFN)
    INITH = 'A. r e. N0 ( L ` r ) e. %s' % NF('0')
    NVM = lambda r, z: NVF('F"', r, z)
    MOVH = ('( A. r e. %s A. z e. B ( ( C1_ ` %s ) = 1o /\\ ( P" ` %s ) = z ) /\\ A. r e. %s -. ( C1_ ` %s ) = 1o )'
            % (SS, NVM('r', 'z'), NVM('r', 'z'), SS, NVM('r', 'Q')))
    X0, Y0 = '( X ` 0 ) = ( D ` K )', '( Y ` 0 ) = ( D ` J )'
    PT, PPT, PMT = 'P e. ( %s ^m %s )' % (GI, SS), "P' e. ( %s ^m %s )" % (GI, SS), 'P" e. ( %s ^m %s )' % (GH, SS)
    FMT = 'F" e. %s' % HDL('I')
    tree = ((((PHM, "( M ` A' ) = %s" % INIT, '( M ` A ) = %s' % BODYQ), ('( M ` E ) = %s' % PUSHH, "( M ` E' ) = %s" % MOV)),
             ((("A' e. %s" % LL, 'A e. %s' % LL), ('E e. %s' % LL, "E' e. %s" % LL, 'E" e. %s' % LL)),
              (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, 'H e. %s' % DG)),
              (('K =/= J', 'K =/= I', 'J =/= I'), ('H =/= K', 'H =/= J', 'H =/= I'))),
             ((((CC, CP), (CD, C0), C1), ((FT, FPT, FMT), (PT, PPT, GTY), (LTY, PMT))),
              ((('Z e. Word %s' % GI, "Z' e. %s" % GI), ('W e. Word B', ('B C_ %s' % GI, 'B C_ %s' % GH)), ('Q e. %s' % GI, 'Q e. %s' % GH)),
               ('D e. %s' % STK_T, ('N0 C_ %s' % SS, "N' C_ %s" % SS))),
              (INITH, MOVH))),
            (((h['famn'], h['famxy']), (X0, Y0)), ((h['steps'], h['has']), (h['bis'], EXIT))))
    ph = cj(tree)
    w = W(lab, 'The adder ` add ` of TM/Arith.lean: ` addLoop x y z ; push comma w ; moveNum z w ` .  '
               'The initialising load-and-push at ` A\' ` (~ tm2flpg ) sets the registers and pushes '
               'the output terminator ` Q ` on the scratch stack ` I ` , ~ tm2fadl runs the loop, the '
               'terminator is pushed on ` H ` and the sum word ` W ` is moved from ` I ` onto ` H ` '
               '(~ tm2fmov ), so ` H ` holds ` W ++ Q :: ( D ` H ) ` , the operands are consumed and '
               '` I ` is restored.  Lean: ` addLoop_runs ` and ` add_runs ` ; the bound is the exact '
               '` ( # ` Z ) + ( # ` W ) + 4 ` , Lean\'s ` 2 * max + 5 ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, ii, hh = [c['%s e. %s' % (x, DG)] for x in 'KJIH']
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    nhk, nhj, nhi = c['H =/= K'], c['H =/= J'], c['H =/= I']
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph); nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    nih = w.s([nhi], 'necomd', '( %s -> I =/= H )' % ph)
    dd = c['D e. %s' % STK_T]; zw = c['Z e. Word %s' % GI]; ww = c['W e. Word B']
    bi, bh = c['B C_ %s' % GI], c['B C_ %s' % GH]; qi, qh = c['Q e. %s' % GI], c['Q e. %s' % GH]
    n0s0, npss = c['N0 C_ %s' % SS], c["N' C_ %s" % SS]
    n0cl = w.s([zw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, n0))
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii); dhw = stkfv(w, ph, 'D', 'H', tv, dd, hh)
    qsi = s1w(w, ph, qi, 'Q', GI); qsh = s1w(w, ph, qh, 'Q', GH)
    QDI = '( <" Q "> ++ %s )' % DI; QDH = '( <" Q "> ++ ( D ` H ) )'
    qdiw = ccatw(w, ph, qsi, diw, '<" Q ">', DI, GI); qdhw = ccatw(w, ph, qsh, dhw, '<" Q ">', '( D ` H )', GH)
    wi = sswordd(w, ph, ww, 'W', 'B', GI, bi)
    RW = '( reverse ` W )'
    rwb = revw(w, ph, ww, 'W', 'B'); rwi = sswordd(w, ph, rwb, RW, 'B', GI, bi)
    RWQDI = '( %s ++ %s )' % (RW, QDI)
    rwqdiw = ccatw(w, ph, rwi, qdiw, RW, QDI, GI)
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([n0cl, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ %s )' % (ph, n0))
    z0fz = w.s([w.s([z0a, n0cl, ge0], '3jca', '( %s -> ( 0 e. NN0 /\\ %s e. NN0 /\\ 0 <_ %s ) )' % (ph, n0, n0)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, n0))
    fn0, _ = inst_v(w, ph, c[h['famn']], '( %s C_ %s /\\ %s C_ %s )' % (NF('i'), SS, OFC('i'), SS), 'i', '0', z0fz)
    n0s = w.s([fn0], 'simpld', '( %s -> %s C_ %s )' % (ph, NF('0'), SS))
    n1n = w.s([n0cl, w.inst('peano2nn0')], 'syl', '( %s -> ( %s + 1 ) e. NN0 )' % (ph, n0))
    n1r = w.s([n1n, w.inst('nn0red')], 'syl', '( %s -> ( %s + 1 ) e. RR )' % (ph, n0))
    n1fz1 = w.s([w.s([n1n, n1n, w.s([n1r, w.inst('leidd')], 'syl', '( %s -> ( %s + 1 ) <_ ( %s + 1 ) )' % (ph, n0, n0))], '3jca',
                     '( %s -> ( ( %s + 1 ) e. NN0 /\\ ( %s + 1 ) e. NN0 /\\ ( %s + 1 ) <_ ( %s + 1 ) ) )' % (ph, n0, n0, n0, n0)),
                 w.inst('elfz2nn0')], 'sylibr', '( %s -> ( %s + 1 ) e. ( 0 ... ( %s + 1 ) ) )' % (ph, n0, n0))
    fx1, _ = inst_v(w, ph, c[h['famxy']], '( %s e. Word %s /\\ %s e. Word %s )' % (XF('i'), GK, YF('i'), GJ), 'i', '( %s + 1 )' % n0, n1fz1)
    X1, Y1 = XF('( %s + 1 )' % n0), YF('( %s + 1 )' % n0)
    x1w = w.s([fx1], 'simpld', '( %s -> %s e. Word %s )' % (ph, X1, GK)); y1w = w.s([fx1], 'simprd', '( %s -> %s e. Word %s )' % (ph, Y1, GJ))
    # ---- stage 1: the init
    D1 = UP('D', 'I', QDI)
    d1cl = updcl(w, ph, 'D', 'I', QDI, tv, dd, ii, qdiw)
    t1 = applylem(w, ph, 'tm2flpg',
                  ((phm, c["( M ` A' ) = %s" % INIT]), ((c["A' e. %s" % LL], c['A e. %s' % LL], dd), (ii, qi)),
                   (c[LTY], (n0s0, n0s), c[INITH])),
                  HR(CLN("A'", 'N0', 'D'), 'T', 'M', CLN('A', NF('0'), D1), '1'))
    # ---- stage 2: the loop at D := D1
    qdiv = elv(w, ph, qdiw, QDI)
    d1k = updnv(w, ph, 'D', 'I', QDI, 'K', tv, dd, ii, qdiv, kk, nki)
    d1j = updnv(w, ph, 'D', 'I', QDI, 'J', tv, dd, ii, qdiv, jj, nji)
    x01 = w.s([c[X0], d1k], 'eqtr4d', '( %s -> ( X ` 0 ) = ( %s ` K ) )' % (ph, D1))
    y01 = w.s([c[Y0], d1j], 'eqtr4d', '( %s -> ( Y ` 0 ) = ( %s ` J ) )' % (ph, D1))
    D1I = '( %s ` I )' % D1
    POST2 = UP(UP(UP(D1, 'I', '( %s ++ %s )' % (RW, D1I)), 'K', X1), 'J', Y1)
    t2 = applylem(w, ph, 'tm2fadl',
                  (((phm, c['( M ` A ) = %s' % BODYQ]),
                    ((c['A e. %s' % LL], c['E e. %s' % LL]), (kk, jj, ii), (nkj, nki, nji)),
                    (((c[CC], c[CP]), (c[CD], c[C0])), ((c[FT], c[FPT]), (c[PT], c[PPT], c[GTY])), ((zw, c["Z' e. %s" % GI]), (d1cl, npss)))),
                   (((c[h['famn']], c[h['famxy']]), (x01, y01)), ((c[h['steps']], c[h['has']]), (c[h['bis']], c[EXIT])))),
                  HR(CLN('A', NF('0'), D1), 'T', 'M', CLN('E', "N'", POST2), '( %s + 1 )' % n0))
    d1i = updkv(w, ph, 'D', 'I', QDI, tv, dd, ii, qdiv)
    u2 = up2(w, ph, 'D', 'I', QDI, RWQDI, tv, dd, ii, qdiw, rwqdiw)
    tbl2 = {D1I: (QDI, d1i), UP(D1, 'I', RWQDI): (UP('D', 'I', RWQDI), u2)}
    e2, D2 = evaluate(w, ph, POST2, {}, extra_rules=(lambda n: tbl2.get(n.text())))
    assert D2 == UP(UP(UP('D', 'I', RWQDI), 'K', X1), 'J', Y1), D2
    t2r, _, _, _ = hrrw(w, ph, t2, CLN('A', NF('0'), D1), CLN('E', "N'", POST2), '( %s + 1 )' % n0, deq=clneq(w, ph, 'E', "N'", e2, POST2, D2))
    t12 = hrseq(w, ph, phm, t1, t2r, CLN("A'", 'N0', 'D'), CLN('A', NF('0'), D1), CLN('E', "N'", D2), '1', '( %s + 1 )' % n0)
    N12 = '( 1 + ( %s + 1 ) )' % n0
    # ---- stage 3: push Q on H (all states; shrink the precondition to N')
    BI_ = UP('D', 'I', RWQDI)
    bicl = updcl(w, ph, 'D', 'I', RWQDI, tv, dd, ii, rwqdiw)
    bkcl = updcl(w, ph, BI_, 'K', X1, tv, bicl, kk, x1w)
    d2cl = updcl(w, ph, UP(BI_, 'K', X1), 'J', Y1, tv, bkcl, jj, y1w)
    D3 = UP(D2, 'H', '( <" Q "> ++ ( %s ` H ) )' % D2)
    t3 = applylem(w, ph, 'tm2fpush',
                  ((phm, c['( M ` E ) = %s' % PUSHH]), (c['E e. %s' % LL], c["E' e. %s" % LL], (hh, qh)), d2cl),
                  HR(CLN('E', SS, D2), 'T', 'M', CLN("E'", SS, D3), '1'))
    t3s = hrssc(w, ph, phm, t3, CLN('E', SS, D2), CLN("E'", SS, D3), '1', CLN('E', "N'", D2), clnss(w, ph, 'E', "N'", SS, D2, npss))
    h1 = updnv(w, ph, UP(BI_, 'K', X1), 'J', Y1, 'H', tv, bkcl, jj, elv(w, ph, y1w, Y1), hh, nhj)
    h2 = updnv(w, ph, BI_, 'K', X1, 'H', tv, bicl, kk, elv(w, ph, x1w, X1), hh, nhk)
    h3 = updnv(w, ph, 'D', 'I', RWQDI, 'H', tv, dd, ii, elv(w, ph, rwqdiw, RWQDI), hh, nhi)
    d2h = w.s([h1, w.s([h2, h3], 'eqtrd', '( %s -> ( %s ` H ) = ( D ` H ) )' % (ph, UP(BI_, 'K', X1)))], 'eqtrd', '( %s -> ( %s ` H ) = ( D ` H ) )' % (ph, D2))
    e3, D3p = w.rewrite(D3, {'( %s ` H )' % D2: ('( D ` H )', d2h)}, ph)
    assert D3p == UP(D2, 'H', QDH), D3p
    t3r, _, _, _ = hrrw(w, ph, t3s, CLN('E', "N'", D2), CLN("E'", SS, D3), '1', deq=clneq(w, ph, "E'", SS, e3, D3, D3p))
    t123 = hrseq(w, ph, phm, t12, t3r, CLN("A'", 'N0', 'D'), CLN('E', "N'", D2), CLN("E'", SS, D3p), N12, '1')
    N123 = '( %s + 1 )' % N12
    # ---- stage 4: moveNum I -> H at K := I , J := H , W := RW , X := DI , H := QDH , D := D3p
    d3cl = updcl(w, ph, D2, 'H', QDH, tv, d2cl, hh, qdhw)
    PRE4 = UP(UP(D3p, 'I', RWQDI), 'H', QDH)
    RRW = '( reverse ` %s )' % RW
    POST4 = UP(UP(D3p, 'I', DI), 'H', '( %s ++ %s )' % (RRW, QDH))
    N4 = '( ( # ` %s ) + 1 )' % RW
    t4 = applylem(w, ph, 'tm2fmov',
                  ((((phm, c["( M ` E' ) = %s" % MOV]),
                     ((c["E' e. %s" % LL], c['E" e. %s' % LL]), (ii, hh), nih),
                     ((c[FMT], c[C1], c[PMT]), ((bi, bh), (qi, diw, qdhw), d3cl), (w.s([c[MOVH]], 'simpld', '( %s -> A. r e. %s A. z e. B ( ( C1_ ` %s ) = 1o /\\ ( P" ` %s ) = z ) )' % (ph, SS, NVM('r', 'z'), NVM('r', 'z'))),
                                                                                    w.s([c[MOVH]], 'simprd', '( %s -> A. r e. %s -. ( C1_ ` %s ) = 1o )' % (ph, SS, NVM('r', 'Q')))))),
                    rwb)),
                  HR(CLN("E'", SS, PRE4), 'T', 'M', CLN('E"', SS, POST4), N4))
    i1 = updnv(w, ph, D2, 'H', QDH, 'I', tv, d2cl, hh, elv(w, ph, qdhw, QDH), ii, nih)
    i2 = updnv(w, ph, UP(BI_, 'K', X1), 'J', Y1, 'I', tv, bkcl, jj, elv(w, ph, y1w, Y1), ii, nij)
    i3 = updnv(w, ph, BI_, 'K', X1, 'I', tv, bicl, kk, elv(w, ph, x1w, X1), ii, nik)
    i4 = updkv(w, ph, 'D', 'I', RWQDI, tv, dd, ii, elv(w, ph, rwqdiw, RWQDI))
    d3i = w.s([i1, w.s([i2, w.s([i3, i4], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, UP(BI_, 'K', X1), RWQDI))], 'eqtrd',
                       '( %s -> ( %s ` I ) = %s )' % (ph, D2, RWQDI))], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, D3p, RWQDI))
    f1 = upidv(w, ph, D3p, 'I', RWQDI, d3i, tv, d3cl, ii)
    d3h = updkv(w, ph, D2, 'H', QDH, tv, d2cl, hh, elv(w, ph, qdhw, QDH))
    f2 = upidv(w, ph, D3p, 'H', QDH, d3h, tv, d3cl, hh)
    tbl4 = {UP(D3p, 'I', RWQDI): (D3p, f1), UP(D3p, 'H', QDH): (D3p, f2)}
    g4, pre4n = evaluate(w, ph, PRE4, {}, extra_rules=(lambda n: tbl4.get(n.text())))
    assert pre4n == D3p, pre4n
    ceq4 = w.s([clneq(w, ph, "E'", SS, w.s([g4], 'eqcomd', '( %s -> %s = %s )' % (ph, D3p, PRE4)), D3p, PRE4)], 'eqcomd',
               '( %s -> %s = %s )' % (ph, CLN("E'", SS, PRE4), CLN("E'", SS, D3p)))
    # POST4 collapses
    rr = w.s([ww, w.inst('revrev')], 'syl', '( %s -> %s = W )' % (ph, RRW))
    WQDH = '( W ++ %s )' % QDH
    wh = sswordd(w, ph, ww, 'W', 'B', GH, bh)
    wqdhw = ccatw(w, ph, wh, qdhw, 'W', QDH, GH)
    D3b = UP(UP(BI_, 'K', X1), 'J', Y1)      # = D2
    # UP( UP( D2 , H , QDH ) , I , DI ) = UP( UP( D2 , I , DI ) , H , QDH )
    cm = upc(w, ph, D2, 'H', QDH, 'I', DI, tv, d2cl, nhi, hh, qdhw, ii, diw)
    # UP( UP( UP( D2 , I , DI ) , H , QDH ) , H , WQDH ) = UP( UP( D2 , I , DI ) , H , WQDH )
    d2icl = updcl(w, ph, D2, 'I', DI, tv, d2cl, ii, diw)
    cm2 = up2(w, ph, UP(D2, 'I', DI), 'H', QDH, WQDH, tv, d2icl, hh, qdhw, wqdhw)
    # UP( D2 , I , DI ) = UP( UP( UP( D , I , DI ) , K , X1 ) , J , Y1 ) by tm2stkup3c, then upid
    c3c = applylem(w, ph, 'tm2stkup3c',
                   (((tv, dd), (nkj, nki, nji)), (ii, (rwqdiw, diw)), ((kk, x1w), (jj, y1w))),
                   '%s = %s' % (UP(D2, 'I', DI), UP(UP(UP('D', 'I', DI), 'K', X1), 'J', Y1)))
    ui = upid(w, ph, 'D', 'I', tv, dd, ii)
    FIN = UP(UP(UP('D', 'K', X1), 'J', Y1), 'H', WQDH)
    tbl5 = {RRW: ('W', rr), UP(D3p, 'I', DI): (UP(UP(D2, 'I', DI), 'H', QDH), cm),
            UP(UP(UP(D2, 'I', DI), 'H', QDH), 'H', WQDH): (UP(UP(D2, 'I', DI), 'H', WQDH), cm2),
            UP(D2, 'I', DI): (UP(UP(UP('D', 'I', DI), 'K', X1), 'J', Y1), c3c), UP('D', 'I', DI): ('D', ui)}
    g5, postn = evaluate(w, ph, POST4, {}, extra_rules=(lambda n: tbl5.get(n.text())))
    assert postn == FIN, (postn, FIN)
    rl = w.s([ww, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` W ) )' % (ph, RW))
    n4 = w.s([rl], 'oveq1d', '( %s -> %s = ( ( # ` W ) + 1 ) )' % (ph, N4))
    t4r, _, _, _ = hrrw(w, ph, t4, CLN("E'", SS, PRE4), CLN('E"', SS, POST4), N4, ceq=ceq4, deq=clneq(w, ph, 'E"', SS, g5, POST4, FIN), neq=n4)
    tall = hrseq(w, ph, phm, t123, t4r, CLN("A'", 'N0', 'D'), CLN("E'", SS, D3p), CLN('E"', SS, FIN), N123, '( ( # ` W ) + 1 )')
    nw = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    bound(w, ph, phm, tall, CLN("A'", 'N0', 'D'), CLN('E"', SS, FIN), '( %s + ( ( # ` W ) + 1 ) )' % N123,
          '( ( %s + ( # ` W ) ) + 4 )' % n0, {n0: n0cl, '( # ` W )': nw}, qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fcmp'): tm2fcmp()
    if want('tm2fadd'): tm2fadd()
