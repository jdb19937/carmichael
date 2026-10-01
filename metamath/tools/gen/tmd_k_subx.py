"""T-MD: the in-place subtractor ` sub x y z x ` (~ tm2fsubx , Lean ` sub_runs_x ` ,
blueprint D6): T5's ~ tm2fsub with the output stack the first operand's stack
` K ` (tools/gen/t5_j_sub.py's ` subasm ` at ` H := K ` )."""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
from t5_i_add import hyps_i, CC as CCT, CP, CD, C0 as C0T, FT, FPT, GTY, LTY as LTYT
from t5_g_core import N0, OFC, DI, RESTQ, LOADG
from t5_f_rd import BODY

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

QX = '( <" Q "> ++ X )'


def sbt_parts(lab_a, lab_a1, lab_a2, lab_e, F, C, Cc, Fl, P, Pm, N, Np, H='K'):
    NV_ = lambda r, z: NVF(F, r, z)
    ZB = BRANCH(Cc, POP('I', F, BRANCH(C, GT(lab_a), PUSH('I', P, LOAD(Fl, GT(lab_a1))))), GT(lab_a1))
    POPST = POP('I', F, BRANCH(C, GT(lab_a), PUSH('I', P, LOAD(Fl, GT(lab_a1)))))
    PUSHH = PUSH(H, CONSTF('T', 'Q'), GT(lab_a2))
    MOV = POP('I', F, BRANCH(C, PUSH(H, Pm, GT(lab_a2)), GT(lab_e)))
    HC = ('A. r e. %s A. z e. B ( ( %s ` r ) = 1o /\\ ( %s ` %s ) = 1o /\\ %s e. %s )'
          % (N, Cc, C, NV_('r', 'z'), NV_('r', 'z'), N))
    HE = ('A. m e. %s ( ( %s ` m ) = 1o /\\ -. ( %s ` %s ) = 1o /\\ ( ( %s ` %s ) = Q /\\ ( %s ` %s ) e. %s ) )'
          % (N, Cc, C, NV_('m', 'Q'), P, NV_('m', 'Q'), Fl, NV_('m', 'Q'), Np))
    BR = 'A. m e. %s -. ( %s ` m ) = 1o' % (N, Cc)
    MOVH = ('( A. r e. %s A. z e. B ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z ) /\\ A. r e. %s -. ( %s ` %s ) = 1o )'
            % (SS, C, NV_('r', 'z'), Pm, NV_('r', 'z'), SS, C, NV_('r', 'Q')))
    return dict(ZB=ZB, POPST=POPST, PUSHH=PUSHH, MOV=MOV, HC=HC, HE=HE, BR=BR, MOVH=MOVH)


def subx_tree():
    cmp = False
    n0 = N0(cmp)
    QEX = GT('A"')
    REST = RESTQ(cmp, QEX)
    BODYQ = BODY(REST)
    INIT = LOAD('L', PUSH('I', CONSTF('T', 'Q'), GT('A')))
    h = hyps_i(cmp)
    ON = OFC(n0)
    EXIT = "A. p e. %s ( ( C\" ` p ) = 1o /\\ p e. N' )" % ON
    INITH = 'A. r e. N0 ( L ` r ) e. %s' % NF('0')
    p = sbt_parts('A"', "E'", 'E"', 'E', 'F"', 'C1_', 'C0', "L'", "P'", 'P"', "N'", 'N"')
    DISJ = '( ( ( %s /\\ %s ) /\\ Z" = (/) ) \\/ ( %s /\\ Z" = Z ) )' % (p['HC'], p['HE'], p['BR'])
    X0, Y0 = '( X ` 0 ) = ( D ` K )', '( Y ` 0 ) = ( D ` J )'
    PT, PPT, PMT = 'P e. ( %s ^m %s )' % (GI, SS), "P' e. ( %s ^m %s )" % (GI, SS), 'P" e. ( %s ^m %s )' % (GK, SS)
    FMT = 'F" e. %s' % HDL('I')
    LPT = "L' e. ( %s ^m %s )" % (SS, SS)
    C1 = 'C1_ e. ( 2o ^m %s )' % SS
    tree = ((((PHM, "( M ` A' ) = %s" % INIT, '( M ` A ) = %s' % BODYQ), ('( M ` A" ) = %s' % p['ZB'], "( M ` E' ) = %s" % p['PUSHH'], '( M ` E" ) = %s' % p['MOV'])),
             ((("A' e. %s" % LL, 'A e. %s' % LL, 'A" e. %s' % LL), ("E' e. %s" % LL, 'E" e. %s' % LL, 'E e. %s' % LL)),
              ('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG), ('K =/= J', 'K =/= I', 'J =/= I')),
             ((((CCT, CP, CD), (C0T, C1)), ((FT, FPT, FMT), (PT, PPT, PMT), (GTY, LTYT, LPT))),
              ((('Z e. Word %s' % GI, 'Z e. Word B'), ('B C_ %s' % GI, 'B C_ %s' % GK), ('Q e. %s' % GI, 'Q e. %s' % GK)),
               ('D e. %s' % STK_T, ('N0 C_ %s' % SS, "N' C_ %s" % SS, 'N" C_ %s' % SS))),
              ((INITH, p['MOVH']), DISJ))),
            (((h['famn'], h['famxy']), (X0, Y0)), ((h['steps'], h['has']), (h['bis'], EXIT))))
    X1, Y1 = XF('( %s + 1 )' % n0), YF('( %s + 1 )' % n0)
    FIN = UP(UP('D', 'K', '( Z" ++ ( <" Q "> ++ %s ) )' % X1), 'J', Y1)
    concl_ = HR(CLN("A'", 'N0', 'D'), 'T', 'M', CLN('E', SS, FIN), '( ( 3 x. ( # ` Z ) ) + 5 )')
    return tree, concl_, dict(n0=n0, BODYQ=BODYQ, INIT=INIT, h=h, EXIT=EXIT, INITH=INITH, p=p, DISJ=DISJ, X0=X0, Y0=Y0,
                              PT=PT, PPT=PPT, PMT=PMT, FMT=FMT, LPT=LPT, C1=C1, X1=X1, Y1=Y1, FIN=FIN)


TREE_SUBX, CONCL_SUBX, P_SUBX = subx_tree()


def tm2fsubx():
    lab = 'tm2fsubx'
    tree, ph = TREE_SUBX, cj(TREE_SUBX)
    q = P_SUBX
    n0, BODYQ, INIT, h, EXIT, INITH, p, DISJ = [q[k] for k in ('n0', 'BODYQ', 'INIT', 'h', 'EXIT', 'INITH', 'p', 'DISJ')]
    X0, Y0, PT, PPT, PMT, FMT, LPT, C1, X1, Y1, FIN = [q[k] for k in ('X0', 'Y0', 'PT', 'PPT', 'PMT', 'FMT', 'LPT', 'C1', 'X1', 'Y1', 'FIN')]
    w = W(lab, 'The in-place subtractor ` sub x y z x ` of TM/MulDiv.lean: ~ tm2fsub with the '
               'difference pushed back on the first operand\'s stack ` K ` after the loop consumed '
               'the operand: ` K ` holds ` Z" ++ Q :: ( X ` ( ( # ` Z ) + 1 ) ) ` (` Z" ` the '
               'difference or ` (/) ` by ~ tm2fsbt \'s disjunction) and ` I ` is restored.  Lean: '
               '` sub_runs_x ` (Steps23.lean, Table.lean).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, jj, ii = c['K e. %s' % DG], c['J e. %s' % DG], c['I e. %s' % DG]
    nkj, nki, nji = c['K =/= J'], c['K =/= I'], c['J =/= I']
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph); nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    dd, zw, zb = c['D e. %s' % STK_T], c['Z e. Word %s' % GI], c['Z e. Word B']
    bi, bk, qi, qk = c['B C_ %s' % GI], c['B C_ %s' % GK], c['Q e. %s' % GI], c['Q e. %s' % GK]
    n0s0, npss, nqss = c['N0 C_ %s' % SS], c["N' C_ %s" % SS], c['N" C_ %s' % SS]
    disj = c[DISJ]
    n0cl = w.s([zw, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, n0))
    diw = stkfv(w, ph, 'D', 'I', tv, dd, ii)
    qsi = s1w(w, ph, qi, 'Q', GI); qsk = s1w(w, ph, qk, 'Q', GK)
    QDI = '( <" Q "> ++ %s )' % DI
    qdiw = ccatw(w, ph, qsi, diw, '<" Q ">', DI, GI)
    RZ = '( reverse ` Z )'
    rzb = revw(w, ph, zb, 'Z', 'B'); rzi = sswordd(w, ph, rzb, RZ, 'B', GI, bi)
    RZQDI = '( %s ++ %s )' % (RZ, QDI)
    rzqdiw = ccatw(w, ph, rzi, qdiw, RZ, QDI, GI)
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
    x1w = w.s([fx1], 'simpld', '( %s -> %s e. Word %s )' % (ph, X1, GK)); y1w = w.s([fx1], 'simprd', '( %s -> %s e. Word %s )' % (ph, Y1, GJ))
    # ---- stage 1: init
    D1 = UP('D', 'I', QDI)
    d1cl = updcl(w, ph, 'D', 'I', QDI, tv, dd, ii, qdiw)
    t1 = applylem(w, ph, 'tm2flpg',
                  ((phm, c["( M ` A' ) = %s" % INIT]), ((c["A' e. %s" % LL], c['A e. %s' % LL], dd), (ii, qi)),
                   (c[LTYT], (n0s0, n0s), c[INITH])),
                  HR(CLN("A'", 'N0', 'D'), 'T', 'M', CLN('A', NF('0'), D1), '1'))
    # ---- stage 2: the loop at D := D1
    qdiv = elv(w, ph, qdiw, QDI)
    d1k = updnv(w, ph, 'D', 'I', QDI, 'K', tv, dd, ii, qdiv, kk, nki)
    d1j = updnv(w, ph, 'D', 'I', QDI, 'J', tv, dd, ii, qdiv, jj, nji)
    x01 = w.s([c[X0], d1k], 'eqtr4d', '( %s -> ( X ` 0 ) = ( %s ` K ) )' % (ph, D1))
    y01 = w.s([c[Y0], d1j], 'eqtr4d', '( %s -> ( Y ` 0 ) = ( %s ` J ) )' % (ph, D1))
    POST2 = UP(UP(UP(D1, 'I', '( %s ++ ( %s ` I ) )' % (RZ, D1)), 'K', X1), 'J', Y1)
    t2 = applylem(w, ph, 'tm2fsbl',
                  (((phm, c['( M ` A ) = %s' % BODYQ]),
                    ((c['A e. %s' % LL], c['A" e. %s' % LL]), (kk, jj, ii), (nkj, nki, nji)),
                    ((c[CCT], c[CP], c[CD]), ((c[FT], c[FPT]), (c[PT], c[GTY])), (zw, (d1cl, npss)))),
                   (((c[h['famn']], c[h['famxy']]), (x01, y01)), ((c[h['steps']], c[h['has']]), (c[h['bis']], c[EXIT])))),
                  HR(CLN('A', NF('0'), D1), 'T', 'M', CLN('A"', "N'", POST2), '( %s + 1 )' % n0))
    d1i = updkv(w, ph, 'D', 'I', QDI, tv, dd, ii, qdiv)
    u2 = up2(w, ph, 'D', 'I', QDI, RZQDI, tv, dd, ii, qdiw, rzqdiw)
    tbl2 = {'( %s ` I )' % D1: (QDI, d1i), UP(D1, 'I', RZQDI): (UP('D', 'I', RZQDI), u2)}
    e2, D2 = evaluate(w, ph, POST2, {}, extra_rules=(lambda n: tbl2.get(n.text())))
    BI_ = UP('D', 'I', RZQDI)
    assert D2 == UP(UP(BI_, 'K', X1), 'J', Y1), D2
    t2r, _, _, _ = hrrw(w, ph, t2, CLN('A', NF('0'), D1), CLN('A"', "N'", POST2), '( %s + 1 )' % n0, deq=clneq(w, ph, 'A"', "N'", e2, POST2, D2))
    t12 = hrseq(w, ph, phm, t1, t2r, CLN("A'", 'N0', 'D'), CLN('A', NF('0'), D1), CLN('A"', "N'", D2), '1', '( %s + 1 )' % n0)
    N12 = '( 1 + ( %s + 1 ) )' % n0
    # ---- stage 3: the tail at H := K , W := RZ , X := DI , D := D2 , N := N' , N' := N" , Z0 := ( reverse ` Z" )
    bicl = updcl(w, ph, 'D', 'I', RZQDI, tv, dd, ii, rzqdiw)
    bkcl = updcl(w, ph, BI_, 'K', X1, tv, bicl, kk, x1w)
    d2cl = updcl(w, ph, UP(BI_, 'K', X1), 'J', Y1, tv, bkcl, jj, y1w)
    i2 = updnv(w, ph, UP(BI_, 'K', X1), 'J', Y1, 'I', tv, bkcl, jj, elv(w, ph, y1w, Y1), ii, nij)
    i3 = updnv(w, ph, BI_, 'K', X1, 'I', tv, bicl, kk, elv(w, ph, x1w, X1), ii, nik)
    i4 = updkv(w, ph, 'D', 'I', RZQDI, tv, dd, ii, elv(w, ph, rzqdiw, RZQDI))
    d2i = w.s([i2, w.s([i3, i4], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, UP(BI_, 'K', X1), RZQDI))], 'eqtrd', '( %s -> ( %s ` I ) = %s )' % (ph, D2, RZQDI))
    RZP = '( reverse ` Z" )'
    pt = p
    DISJT = '( ( ( %s /\\ %s ) /\\ %s = (/) ) \\/ ( %s /\\ %s = %s ) )' % (pt['HC'], pt['HE'], RZP, pt['BR'], RZP, RZ)
    pha = '( %s /\\ ( ( %s /\\ %s ) /\\ Z" = (/) ) )' % (ph, pt['HC'], pt['HE'])
    hce = w.s([], 'simprl', '( %s -> ( %s /\\ %s ) )' % (pha, pt['HC'], pt['HE']))
    zpe = w.s([], 'simprr', '( %s -> Z" = (/) )' % pha)
    r0 = w.s([], 'rev0', '( reverse ` (/) ) = (/)')
    zr = w.s([w.s([zpe], 'fveq2d', '( %s -> %s = ( reverse ` (/) ) )' % (pha, RZP)), w.s([r0], 'a1i', '( %s -> ( reverse ` (/) ) = (/) )' % pha)], 'eqtrd', '( %s -> %s = (/) )' % (pha, RZP))
    da = w.s([w.s([hce, zr], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ %s = (/) ) )' % (pha, pt['HC'], pt['HE'], RZP))], 'orcd', '( %s -> %s )' % (pha, DISJT))
    phb = '( %s /\\ ( %s /\\ Z" = Z ) )' % (ph, pt['BR'])
    brs = w.s([], 'simprl', '( %s -> %s )' % (phb, pt['BR'])); zze = w.s([], 'simprr', '( %s -> Z" = Z )' % phb)
    zr2 = w.s([zze], 'fveq2d', '( %s -> %s = %s )' % (phb, RZP, RZ))
    db = w.s([w.s([brs, zr2], 'jca', '( %s -> ( %s /\\ %s = %s ) )' % (phb, pt['BR'], RZP, RZ))], 'olcd', '( %s -> %s )' % (phb, DISJT))
    dj = w.s([disj, w.s([da, db], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ, DISJT))], 'mpdan', '( %s -> %s )' % (ph, DISJT))
    QDK = '( <" Q "> ++ ( %s ` K ) )' % D2
    RZPQDK = '( ( reverse ` %s ) ++ %s )' % (RZP, QDK)
    POST3 = UP(UP(D2, 'I', DI), 'K', RZPQDK)
    mh = c[pt['MOVH']]
    d2kw = stkfv(w, ph, D2, 'K', tv, d2cl, kk)
    qdkw = ccatw(w, ph, qsk, d2kw, '<" Q ">', '( %s ` K )' % D2, GK)
    t3 = applylem(w, ph, 'tm2fsbt',
                  ((((phm, c['( M ` A" ) = %s' % pt['ZB']], c["( M ` E' ) = %s" % pt['PUSHH']]), c['( M ` E" ) = %s' % pt['MOV']]),
                    (((c['A" e. %s' % LL], c["E' e. %s" % LL]), (c['E" e. %s' % LL], c['E e. %s' % LL])), (ii, kk, nik),
                     ((c[FMT], c[C1], c[C0T]), (c[PPT], c[PMT], c[LPT]))),
                    (((bi, bk), (qi, qk), (rzb, diw, d2cl)), (d2i, (npss, nqss), mh), dj))),
                  HR(CLN('A"', "N'", D2), 'T', 'M', CLN('E', SS, POST3), '( ( 2 x. ( # ` %s ) ) + 3 )' % RZ))
    zpw = w.s([disj, w.s([w.s([zpe, w.s([w.s([], 'wrd0', '(/) e. Word B')], 'a1i', '( %s -> (/) e. Word B )' % pha)], 'eqeltrd', '( %s -> Z" e. Word B )' % pha),
                          w.s([zze, lift(w, zb, phb, 'Z e. Word B')], 'eqeltrd', '( %s -> Z" e. Word B )' % phb)], 'jaodan',
                         '( ( %s /\\ %s ) -> Z" e. Word B )' % (ph, DISJ))], 'mpdan', '( %s -> Z" e. Word B )' % ph)
    rr = w.s([zpw, w.inst('revrev')], 'syl', '( %s -> ( reverse ` %s ) = Z" )' % (ph, RZP))
    c3c = applylem(w, ph, 'tm2stkup3c',
                   (((tv, dd), (nkj, nki, nji)), (ii, (rzqdiw, diw)), ((kk, x1w), (jj, y1w))),
                   '%s = %s' % (UP(D2, 'I', DI), UP(UP(UP('D', 'I', DI), 'K', X1), 'J', Y1)))
    ui = upid(w, ph, 'D', 'I', tv, dd, ii)
    k1 = updnv(w, ph, UP(BI_, 'K', X1), 'J', Y1, 'K', tv, bkcl, jj, elv(w, ph, y1w, Y1), kk, nkj)
    k2 = updkv(w, ph, BI_, 'K', X1, tv, bicl, kk, elv(w, ph, x1w, X1))
    d2k = w.s([k1, k2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, D2, X1))
    ZQX1 = '( Z" ++ ( <" Q "> ++ %s ) )' % X1
    zpk = sswordd(w, ph, zpw, 'Z"', 'B', GK, bk)
    zqx1w = ccatw(w, ph, zpk, ccatw(w, ph, qsk, x1w, '<" Q ">', X1, GK), 'Z"', '( <" Q "> ++ %s )' % X1, GK)
    u3 = up3(w, ph, 'D', 'K', X1, 'J', Y1, ZQX1, tv, dd, nkj, kk, x1w, zqx1w, jj, y1w)
    tbl = {'( reverse ` %s )' % RZP: ('Z"', rr), '( %s ` K )' % D2: (X1, d2k),
           UP(D2, 'I', DI): (UP(UP(UP('D', 'I', DI), 'K', X1), 'J', Y1), c3c), UP('D', 'I', DI): ('D', ui),
           UP(UP(UP('D', 'K', X1), 'J', Y1), 'K', ZQX1): (FIN, u3)}
    g, postn = evaluate(w, ph, POST3, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert postn == FIN, (postn, FIN)
    t3r, _, _, _ = hrrw(w, ph, t3, CLN('A"', "N'", D2), CLN('E', SS, POST3), '( ( 2 x. ( # ` %s ) ) + 3 )' % RZ, deq=clneq(w, ph, 'E', SS, g, POST3, FIN))
    tall = hrseq(w, ph, phm, t12, t3r, CLN("A'", 'N0', 'D'), CLN('A"', "N'", D2), CLN('E', SS, FIN), N12, '( ( 2 x. ( # ` %s ) ) + 3 )' % RZ)
    rl = w.s([zb, w.inst('revlen')], 'syl', '( %s -> ( # ` %s ) = ( # ` Z ) )' % (ph, RZ))
    nrz = w.s([rzb, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, RZ))
    bound(w, ph, phm, tall, CLN("A'", 'N0', 'D'), CLN('E', SS, FIN), '( %s + ( ( 2 x. ( # ` %s ) ) + 3 ) )' % (N12, RZ),
          '( ( 3 x. ( # ` Z ) ) + 5 )', {n0: n0cl, '( # ` %s )' % RZ: nrz}, hyps=[rl], qed=True)
    return w.run()


if __name__ == '__main__':
    if want('tm2fsubx'): tm2fsubx()
