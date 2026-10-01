"""T5: the transducing scan loop with an abstract exit (~ tm2fscl ), and the
assembled loops of `incLoop` and `predLoop` (TM/Prims.lean) whose exits are
discharged by ~ tm2fin0 / ~ tm2fin0t and ~ tm2fpr0a / ~ tm2fpr0b / ~ tm2fpr0c
under a disjunctive hypothesis (blueprint D3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t5lib import *

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

GK, GJ = GX('K'), GX('J')
HDL = lambda k: '( %s ^m ( %s X. ( %s |_| 1o ) ) )' % (SS, SS, GX(k))
RATY = 'F e. %s' % HDL('K')
CTY = 'C e. ( 2o ^m %s )' % SS
PTY = 'P e. ( %s ^m %s )' % (GJ, SS)
GA = GT('A')
GE = GT('E')
PU = PUSH('J', 'P', GA)
STM = lambda Q: POP('K', 'F', BRANCH('C', PU, Q))
NV = lambda r, z: NVF('F', r, z)
HC = ('A. r e. N A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = ( G ` z ) /\\ %s e. N )'
      % (NV('r', 'z'), NV('r', 'z'), NV('r', 'z')))
GTY = 'G : B --> %s' % GJ
UP2 = lambda x, y: UP(UP('D', 'K', x), 'J', y)
CO = lambda s: '( G o. %s )' % s
RGW = '( reverse ` %s )' % CO('W')
RGWH = '( %s ++ H )' % RGW
DL = UP2('R', RGWH)


def PHTRW(Q):
    return (((PHM, '( M ` A ) = %s' % STM(Q)),
             ('A e. %s' % LL, ('K e. %s' % DG, 'J e. %s' % DG), 'K =/= J'),
             ((RATY, CTY, PTY),
              (('B C_ %s' % GK, GTY), ('R e. Word %s' % GK, 'H e. Word %s' % GJ), 'D e. %s' % STK_T),
              ('%s e. %s' % (Q, STMT_T), ('N C_ %s' % SS, HC)))))


def EXIT(Z):
    return HR(CLN('A', 'N', DL), 'T', 'M', CLN('E', 'N', UP(DL, 'K', Z)), '1')


TREE_SCL = ((PHTRW('Q'), 'W e. Word B'), ('Z e. Word %s' % GK, EXIT('Z')))


def loop_part(w, ph, c, Q, ww):
    """the loop tm2ftrw at U := (/) in its reduced form; returns (step, PRE, MID)
    with PRE = UP2( ( W ++ R ) , H ), MID = DL.  c is a Ctx of PHTRW(Q)."""
    phm = c[PHM]
    hw = c['H e. Word %s' % GJ]; gf = c[GTY]; rw = c['R e. Word %s' % GK]
    w0 = w.s([], 'wrd0', '(/) e. Word B')
    w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word B )' % ph)
    CL0 = CLN('A', 'N', UP2('( W ++ R )', '( %s ++ H )' % CO('(/)')))
    RV0 = '( ( reverse ` W ) ++ (/) )'
    CL1 = CLN('A', 'N', UP2('( (/) ++ R )', '( %s ++ H )' % CO(RV0)))
    tree = ((PHTRW(Q)), (ww, w0a))
    def leaves(t):
        if isinstance(t, str):
            return c[t]
        return tuple(leaves(x) for x in t)
    ant = (leaves(PHTRW(Q)), (ww, w0a))
    loop = applylem(w, ph, 'tm2ftrw', ant, HR(CL0, 'T', 'M', CL1, '( # ` W )'))
    co0 = w.s([], 'co02', '%s = (/)' % CO('(/)'))
    co0a = w.s([co0], 'a1i', '( %s -> %s = (/) )' % (ph, CO('(/)')))
    lidh = w.s([hw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ H ) = H )' % ph)
    tbl = {CO('(/)'): ('(/)', co0a), '( (/) ++ H )': ('H', lidh)}
    cs, PRE = evaluate(w, ph, CL0, {}, extra_rules=(lambda n: tbl.get(n.text())))
    assert PRE == CLN('A', 'N', UP2('( W ++ R )', 'H')), PRE
    rvc = w.s([ww, w.inst('revcl')], 'syl', '( %s -> ( reverse ` W ) e. Word B )' % ph)
    ridw = w.s([rvc, w.inst('ccatrid')], 'syl', '( %s -> %s = ( reverse ` W ) )' % (ph, RV0))
    rvco = w.s([ww, gf, w.inst('revco')], 'syl2anc', '( %s -> %s = %s )' % (ph, CO('( reverse ` W )'), RGW))
    lidr = w.s([rw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ R ) = R )' % ph)
    tbl2 = {RV0: ('( reverse ` W )', ridw), CO('( reverse ` W )'): (RGW, rvco), '( (/) ++ R )': ('R', lidr)}
    ds, MID = evaluate(w, ph, CL1, {}, extra_rules=(lambda n: tbl2.get(n.text())))
    assert MID == CLN('A', 'N', DL), MID
    loop2, _, _, _ = hrrw(w, ph, loop, CL0, CL1, '( # ` W )', ceq=cs, deq=ds)
    return loop2, PRE, MID


def tm2fscl():
    lab = 'tm2fscl'
    ph = cj(TREE_SCL)
    w = W(lab, 'The transducing scan loop with an abstract exit: after the run '
               '` W ` on stack ` K ` has been moved onto stack ` J ` letterwise '
               'mapped by ` G ` , any one-step triple that leaves for ` E ` with the '
               'contents of ` K ` replaced by ` Z ` completes the fragment.  '
               '~ tm2ftr is the instance whose exit is ~ tm2fpb0 ; the loops of '
               '` incLoop ` and ` predLoop ` (Lean\'s ` incLoop_loop ` , '
               '` predLoop_loop ` ) are the instances whose exits are the '
               'three-way branches ~ tm2fin0 , ~ tm2fin0t , ~ tm2fpr0a , ~ tm2fpr0b , '
               '~ tm2fpr0c .')
    c = Ctx(w, ph, TREE_SCL)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    ww = c['W e. Word B']; zw = c['Z e. Word %s' % GK]; ex = c[EXIT('Z')]
    kk, jj = c['K e. %s' % DG], c['J e. %s' % DG]
    ne = c['K =/= J']; dd = c['D e. %s' % STK_T]
    rw = c['R e. Word %s' % GK]; hw = c['H e. Word %s' % GJ]; gf = c[GTY]
    loop2, PRE, MID = loop_part(w, ph, c, 'Q', ww)
    # the exit's stacks collapse
    gww = w.s([ww, gf, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, CO('W'), GJ))
    rgw = revw(w, ph, gww, CO('W'), GJ)
    rgwh = ccatw(w, ph, rgw, hw, RGW, 'H', GJ)
    col = up3(w, ph, 'D', 'K', 'R', 'J', RGWH, 'Z', tv, dd, ne, kk, rw, zw, jj, rgwh)
    CLE = CLN('E', 'N', UP(DL, 'K', 'Z'))
    CLE2 = CLN('E', 'N', UP2('Z', RGWH))
    ex2, _, _, _ = hrrw(w, ph, ex, MID, CLE, '1', deq=clneq(w, ph, 'E', 'N', col, UP(DL, 'K', 'Z'), UP2('Z', RGWH)))
    w.qed([phm, loop2, ex2], 'syl3anc', '( %s -> %s )' % (ph, HR(PRE, 'T', 'M', CLE2, '( ( # ` W ) + 1 )')))
    return w.run()


# ---------------------------------------------------------------- incLoop
PK = lambda f, q: PUSH('K', f, q)
QINC = BRANCH("C'", PK("P'", GE), PK('P"', PK("P'", GE)))
STINC = STM(QINC)
ZX = '( <" Z "> ++ X )'
NVZ = lambda m: NV(m, 'Z')
IFA = ('A. m e. N ( -. ( C ` %s ) = 1o /\\ ( C\' ` %s ) = 1o /\\ ( ( P\' ` %s ) = Z\' /\\ %s e. N ) )'
       % (NVZ('m'), NVZ('m'), NVZ('m'), NVZ('m')))
IFB = ('A. m e. N ( ( -. ( C ` %s ) = 1o /\\ -. ( C\' ` %s ) = 1o ) /\\ ( ( ( P\' ` %s ) = Z\' /\\ ( P" ` %s ) = Z" ) /\\ %s e. N ) )'
       % (NVZ('m'), NVZ('m'), NVZ('m'), NVZ('m'), NVZ('m')))
ZA = "( <\" Z' \"> ++ X )"
ZB = "( <\" Z' \"> ++ ( <\" Z\" \"> ++ X ) )"
DISJ_INC = '( ( %s /\\ Z0 = %s ) \\/ ( %s /\\ Z0 = %s ) )' % (IFA, ZA, IFB, ZB)
CTY2 = "C' e. ( 2o ^m %s )" % SS
PKTY = lambda f: '%s e. ( %s ^m %s )' % (f, GK, SS)

TREE_INC = (((PHM, '( M ` A ) = %s' % STINC),
             (('A e. %s' % LL, 'E e. %s' % LL), ('K e. %s' % DG, 'J e. %s' % DG), 'K =/= J'),
             (((RATY, CTY, CTY2), (PTY, PKTY("P'"), PKTY('P"'))),
              (('B C_ %s' % GK, GTY), (('Z e. %s' % GK, "Z' e. %s" % GK, 'Z" e. %s' % GK), 'X e. Word %s' % GK, 'H e. Word %s' % GJ), 'D e. %s' % STK_T),
              (('N C_ %s' % SS, HC), DISJ_INC))),
            'W e. Word B')


def exit_stack(w, ph, tv, dd, kk, jj, ne, rw, rgwh, R):
    """( ph -> ( DL ` K ) = R ) and ( ph -> DL e. Stk ); DL = UP2( R , RGWH )"""
    dkr = updcl(w, ph, 'D', 'K', R, tv, dd, kk, rw)
    dlcl = updcl(w, ph, UP('D', 'K', R), 'J', RGWH, tv, dkr, jj, rgwh)
    a1 = updnv(w, ph, UP('D', 'K', R), 'J', RGWH, 'K', tv, dkr, jj, elv(w, ph, rgwh, RGWH), kk, ne)
    a2 = updkv(w, ph, 'D', 'K', R, tv, dd, kk, elv(w, ph, rw, R))
    dlk = w.s([a1, a2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, UP(UP('D', 'K', R), 'J', RGWH), R))
    return dlk, dlcl


def tm2fincl():
    lab = 'tm2fincl'
    ph = cj(TREE_INC)
    w = W(lab, 'The assembled loop of ` incLoop ` (TM/Prims.lean): the run ` W ` of '
               'letters the carry chain continues on is moved onto the scratch stack '
               '` J ` mapped by ` G ` (a run of ones becomes a run of zeros), and the '
               'letter ` Z ` after it ends the chain in one of two ways --- a bit that '
               'is put back changed (~ tm2fin0 ), or the terminator, which is put back '
               'under a one (~ tm2fin0t ) --- so the final contents ` Z0 ` of ` K ` '
               'are given by a two-way disjunction.  Lean: ` incLoop_loop ` , whose '
               '` incRest.induct ` is the same split.')
    c = Ctx(w, ph, TREE_INC)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    ww = c['W e. Word B']
    kk, jj = c['K e. %s' % DG], c['J e. %s' % DG]
    ne = c['K =/= J']; dd = c['D e. %s' % STK_T]
    al, el = c['A e. %s' % LL], c['E e. %s' % LL]
    xx = c['X e. Word %s' % GK]; hw = c['H e. Word %s' % GJ]; gf = c[GTY]
    zz, zp, zpp = c['Z e. %s' % GK], c["Z' e. %s" % GK], c['Z" e. %s' % GK]
    nss = c['N C_ %s' % SS]; disj = c[DISJ_INC]
    ra, cc, c2 = c[RATY], c[CTY], c[CTY2]
    pp, pk1, pk2 = c[PTY], c[PKTY("P'")], c[PKTY('P"')]
    # words
    zs = s1w(w, ph, zz, 'Z', GK); zps = s1w(w, ph, zp, "Z'", GK); zpps = s1w(w, ph, zpp, 'Z"', GK)
    zxw = ccatw(w, ph, zs, xx, '<" Z ">', 'X', GK)
    zaw = ccatw(w, ph, zps, xx, '<" Z\' ">', 'X', GK)
    zppx = ccatw(w, ph, zpps, xx, '<" Z" ">', 'X', GK)
    zbw = ccatw(w, ph, zps, zppx, '<" Z\' ">', '( <" Z" "> ++ X )', GK)
    gww = w.s([ww, gf, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, CO('W'), GJ))
    rgw = revw(w, ph, gww, CO('W'), GJ)
    rgwh = ccatw(w, ph, rgw, hw, RGW, 'H', GJ)
    # statement typings
    ge = gotocl(w, ph, tv, 'E', el)
    pe1 = pushcl(w, ph, tv, 'K', "P'", GE, kk, pk1, ge)
    pe2 = pushcl(w, ph, tv, 'K', 'P"', PK("P'", GE), kk, pk2, pe1)
    qcl = brcl(w, ph, tv, "C'", PK("P'", GE), PK('P"', PK("P'", GE)), c2, pe1, pe2)
    ga = gotocl(w, ph, tv, 'A', al)
    pucl = pushcl(w, ph, tv, 'J', 'P', GA, jj, pp, ga)
    # the exit stack DL at R := ( <" Z "> ++ X )
    DLZ = DL.replace('R', ZX) if False else UP2(ZX, RGWH)
    dlk, dlcl = exit_stack(w, ph, tv, dd, kk, jj, ne, zxw, rgwh, ZX)
    # ---- the two cases
    def case(ifx, zeq, ref, lemtree, post):
        pha = '( %s /\\ ( %s /\\ Z0 = %s ) )' % (ph, ifx, zeq)
        A_ = Lifter(w, pha)
        cif = w.s([], 'simprl', '( %s -> %s )' % (pha, ifx))
        czq = w.s([], 'simprr', '( %s -> Z0 = %s )' % (pha, zeq))
        tri = applylem(w, pha, ref, lemtree(A_, cif),
                       HR(CLN('A', 'N', DLZ), 'T', 'M', CLN('E', 'N', UP(DLZ, 'K', post)), '1'))
        czqc = w.s([czq], 'eqcomd', '( %s -> %s = Z0 )' % (pha, zeq))
        deq = clneq(w, pha, 'E', 'N', upeq(w, pha, DLZ, 'K', czqc, zeq, 'Z0'), UP(DLZ, 'K', post), UP(DLZ, 'K', 'Z0'))
        tri2, _, _, _ = hrrw(w, pha, tri, CLN('A', 'N', DLZ), CLN('E', 'N', UP(DLZ, 'K', post)), '1', deq=deq)
        zw = {ZA: zaw, ZB: zbw}[zeq]
        z0w = w.s([czq, A_(zw, '%s e. Word %s' % (zeq, GK))], 'eqeltrd', '( %s -> Z0 e. Word %s )' % (pha, GK))
        return w.s([z0w, tri2], 'jca', '( %s -> ( Z0 e. Word %s /\\ %s ) )' % (pha, GK, EXITZ))
    EXITZ = HR(CLN('A', 'N', DLZ), 'T', 'M', CLN('E', 'N', UP(DLZ, 'K', 'Z0')), '1')
    # tm2fin0 at Q := PU , P := P' , R := PK( P" , PK( P' , GE ) )
    def tree_a(A_, cif):
        return ((A_(phm, PHM), A_(c['( M ` A ) = %s' % STINC], '( M ` A ) = %s' % STINC)),
                ((A_(al, 'A e. %s' % LL), A_(el, 'E e. %s' % LL), A_(kk, 'K e. %s' % DG)),
                 ((A_(ra, RATY), A_(cc, CTY), A_(c2, CTY2)),
                  (A_(pk1, PKTY("P'")), (A_(pucl, '%s e. %s' % (PU, STMT_T)), A_(pe2, '%s e. %s' % (PK('P"', PK("P'", GE)), STMT_T)))))),
                ((A_(dlcl, '%s e. %s' % (DLZ, STK_T)), A_(dlk, '( %s ` K ) = %s' % (DLZ, ZX)),
                  ((A_(zz, 'Z e. %s' % GK), A_(zp, "Z' e. %s" % GK)), A_(xx, 'X e. Word %s' % GK))),
                 (A_(nss, 'N C_ %s' % SS), cif)))
    # tm2fin0t at Q := PU , R := PK( P' , GE ) , P' := P" , P := P'
    def tree_b(A_, cif):
        return ((A_(phm, PHM), A_(c['( M ` A ) = %s' % STINC], '( M ` A ) = %s' % STINC)),
                ((A_(al, 'A e. %s' % LL), A_(el, 'E e. %s' % LL), A_(kk, 'K e. %s' % DG)),
                 ((A_(ra, RATY), A_(cc, CTY), A_(c2, CTY2)),
                  ((A_(pk1, PKTY("P'")), A_(pk2, PKTY('P"'))),
                   (A_(pucl, '%s e. %s' % (PU, STMT_T)), A_(pe1, '%s e. %s' % (PK("P'", GE), STMT_T)))))),
                ((A_(dlcl, '%s e. %s' % (DLZ, STK_T)), A_(dlk, '( %s ` K ) = %s' % (DLZ, ZX)),
                  ((A_(zz, 'Z e. %s' % GK), A_(zp, "Z' e. %s" % GK), A_(zpp, 'Z" e. %s' % GK)), A_(xx, 'X e. Word %s' % GK))),
                 (A_(nss, 'N C_ %s' % SS), cif)))
    ca = case(IFA, ZA, 'tm2fin0', tree_a, ZA)
    cb = case(IFB, ZB, 'tm2fin0t', tree_b, ZB)
    both = w.s([ca, cb], 'jaodan', '( ( %s /\\ %s ) -> ( Z0 e. Word %s /\\ %s ) )' % (ph, DISJ_INC, GK, EXITZ))
    exz = w.s([disj, both], 'mpdan', '( %s -> ( Z0 e. Word %s /\\ %s ) )' % (ph, GK, EXITZ))
    # ---- tm2fscl at Q := QINC , R := ZX , Z := Z0
    trw = PHTRW(QINC)
    def leaves(t):
        if isinstance(t, str):
            if t == 'R e. Word %s' % GK:
                return zxw
            if t == '%s e. %s' % (QINC, STMT_T):
                return qcl
            return c[t]
        return tuple(leaves(x) for x in t)
    PRE = CLN('A', 'N', UP2('( W ++ %s )' % ZX, 'H'))
    POST = CLN('E', 'N', UP2('Z0', RGWH))
    trwst, trwtxt = jtree(w, ph, leaves(trw))
    w.qed([w.s([w.s([trwst, ww], 'jca', '( %s -> ( %s /\\ W e. Word B ) )' % (ph, trwtxt)), exz], 'jca',
               '( %s -> ( ( %s /\\ W e. Word B ) /\\ ( Z0 e. Word %s /\\ %s ) ) )' % (ph, trwtxt, GK, EXITZ)),
           w.inst('tm2fscl')], 'syl', '( %s -> %s )' % (ph, HR(PRE, 'T', 'M', POST, '( ( # ` W ) + 1 )')))
    return w.run()


# ---------------------------------------------------------------- predLoop
PEEKST = PEEK('K', "F'", BRANCH('C"', GE, PK("P'", GE)))
QPRD = BRANCH("C'", PEEKST, PK('P"', GE))
STPRD = STM(QPRD)
NV2 = lambda r, z: NVF("F'", r, z)
PKD = lambda m: NV2(NVZ(m), "Z'")
IFPA = ('A. m e. N ( ( -. ( C ` %s ) = 1o /\\ ( C\' ` %s ) = 1o ) /\\ ( ( C" ` %s ) = 1o /\\ %s e. N ) )'
        % (NVZ('m'), NVZ('m'), PKD('m'), PKD('m')))
IFPB = ('A. m e. N ( ( -. ( C ` %s ) = 1o /\\ ( C\' ` %s ) = 1o ) /\\ ( -. ( C" ` %s ) = 1o /\\ ( ( P\' ` %s ) = Z" /\\ %s e. N ) ) )'
        % (NVZ('m'), NVZ('m'), PKD('m'), PKD('m'), PKD('m')))
IFPC = ('A. m e. N ( -. ( C ` %s ) = 1o /\\ -. ( C\' ` %s ) = 1o /\\ ( ( P" ` %s ) = Y /\\ %s e. N ) )'
        % (NVZ('m'), NVZ('m'), NVZ('m'), NVZ('m')))
XPX = "( <\" Z' \"> ++ X' )"
PA = XPX
PB = "( <\" Z\" \"> ++ ( <\" Z' \"> ++ X' ) )"
PC = '( <" Y "> ++ X )'
DISJ_PRD = ('( ( X = %s /\\ %s /\\ Z0 = %s ) \\/ ( X = %s /\\ %s /\\ Z0 = %s ) \\/ ( %s /\\ Z0 = %s ) )'
            % (XPX, IFPA, PA, XPX, IFPB, PB, IFPC, PC))
CTY3 = 'C" e. ( 2o ^m %s )' % SS
RATY2 = "F' e. %s" % HDL('K')

TREE_PRD = (((PHM, '( M ` A ) = %s' % STPRD),
             (('A e. %s' % LL, 'E e. %s' % LL), ('K e. %s' % DG, 'J e. %s' % DG), 'K =/= J'),
             ((((RATY, RATY2), (CTY, CTY2, CTY3)), (PTY, PKTY("P'"), PKTY('P"'))),
              (('B C_ %s' % GK, GTY),
               ((('Z e. %s' % GK, "Z' e. %s" % GK), ('Z" e. %s' % GK, 'Y e. %s' % GK)), ('X e. Word %s' % GK, "X' e. Word %s" % GK), 'H e. Word %s' % GJ),
               'D e. %s' % STK_T),
              (('N C_ %s' % SS, HC), DISJ_PRD))),
            'W e. Word B')


def tm2fprdl():
    lab = 'tm2fprdl'
    ph = cj(TREE_PRD)
    w = W(lab, 'The assembled loop of ` predLoop ` (TM/Prims.lean): the run ` W ` of '
               'letters the borrow chain continues on is moved onto the scratch stack '
               '` J ` mapped by ` G ` (a run of zeros becomes a run of ones), and the '
               'letter ` Z ` after it ends the chain in one of three ways --- a bit '
               'whose peek finds the terminator (~ tm2fpr0a , the bit is dropped), a bit '
               'whose peek finds a bit (~ tm2fpr0b , the bit is put back changed), or '
               'the terminator (~ tm2fpr0c , put back) --- so the final contents ` Z0 ` '
               'of ` K ` are given by a three-way disjunction.  Lean: ` predLoop_loop ` , '
               'whose ` predRest.induct ` is the same split.')
    c = Ctx(w, ph, TREE_PRD)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    ww = c['W e. Word B']
    kk, jj = c['K e. %s' % DG], c['J e. %s' % DG]
    ne = c['K =/= J']; dd = c['D e. %s' % STK_T]
    al, el = c['A e. %s' % LL], c['E e. %s' % LL]
    xx, xpw = c['X e. Word %s' % GK], c["X' e. Word %s" % GK]
    hw = c['H e. Word %s' % GJ]; gf = c[GTY]
    zz, zp, zpp, yy = c['Z e. %s' % GK], c["Z' e. %s" % GK], c['Z" e. %s' % GK], c['Y e. %s' % GK]
    nss = c['N C_ %s' % SS]; disj = c[DISJ_PRD]
    ra, ra2, cc, c2, c3 = c[RATY], c[RATY2], c[CTY], c[CTY2], c[CTY3]
    pp, pk1, pk2 = c[PTY], c[PKTY("P'")], c[PKTY('P"')]
    zs = s1w(w, ph, zz, 'Z', GK); zps = s1w(w, ph, zp, "Z'", GK); zpps = s1w(w, ph, zpp, 'Z"', GK)
    ys = s1w(w, ph, yy, 'Y', GK)
    zxw = ccatw(w, ph, zs, xx, '<" Z ">', 'X', GK)
    xpxw = ccatw(w, ph, zps, xpw, '<" Z\' ">', "X'", GK)
    pbw = ccatw(w, ph, zpps, xpxw, '<" Z" ">', XPX, GK)
    pcw = ccatw(w, ph, ys, xx, '<" Y ">', 'X', GK)
    gww = w.s([ww, gf, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, CO('W'), GJ))
    rgw = revw(w, ph, gww, CO('W'), GJ)
    rgwh = ccatw(w, ph, rgw, hw, RGW, 'H', GJ)
    ge = gotocl(w, ph, tv, 'E', el)
    pe1 = pushcl(w, ph, tv, 'K', "P'", GE, kk, pk1, ge)
    br3 = brcl(w, ph, tv, 'C"', GE, PK("P'", GE), c3, ge, pe1)
    pkcl = peekcl(w, ph, tv, 'K', "F'", BRANCH('C"', GE, PK("P'", GE)), kk, ra2, br3)
    pe2 = pushcl(w, ph, tv, 'K', 'P"', GE, kk, pk2, ge)
    qcl = brcl(w, ph, tv, "C'", PEEKST, PK('P"', GE), c2, pkcl, pe2)
    ga = gotocl(w, ph, tv, 'A', al)
    pucl = pushcl(w, ph, tv, 'J', 'P', GA, jj, pp, ga)
    DLZ = UP2(ZX, RGWH)
    dlk, dlcl = exit_stack(w, ph, tv, dd, kk, jj, ne, zxw, rgwh, ZX)
    EXITZ = HR(CLN('A', 'N', DLZ), 'T', 'M', CLN('E', 'N', UP(DLZ, 'K', 'Z0')), '1')
    ZZPX = "( <\" Z \"> ++ ( <\" Z' \"> ++ X' ) )"

    def case(casef, ifx, zeq, ref, lemtree, post, zw, withx):
        pha = '( %s /\\ %s )' % (ph, casef)
        A_ = Lifter(w, pha)
        cs = w.s([], 'simpr', '( %s -> %s )' % (pha, casef))
        if withx:
            cxe = w.s([cs, w.inst('simp1')], 'syl', '( %s -> X = %s )' % (pha, XPX))
            cif = w.s([cs, w.inst('simp2')], 'syl', '( %s -> %s )' % (pha, ifx))
            czq = w.s([cs, w.inst('simp3')], 'syl', '( %s -> Z0 = %s )' % (pha, zeq))
            e1 = w.s([cxe], 'oveq2d', '( %s -> %s = %s )' % (pha, ZX, ZZPX))
            dlk2 = w.s([A_(dlk, '( %s ` K ) = %s' % (DLZ, ZX)), e1], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (pha, DLZ, ZZPX))
        else:
            cif = w.s([cs], 'simpld', '( %s -> %s )' % (pha, ifx))
            czq = w.s([cs], 'simprd', '( %s -> Z0 = %s )' % (pha, zeq))
            dlk2 = A_(dlk, '( %s ` K ) = %s' % (DLZ, ZX))
        tri = applylem(w, pha, ref, lemtree(A_, cif, dlk2),
                       HR(CLN('A', 'N', DLZ), 'T', 'M', CLN('E', 'N', UP(DLZ, 'K', post)), '1'))
        czqc = w.s([czq], 'eqcomd', '( %s -> %s = Z0 )' % (pha, zeq))
        deq = clneq(w, pha, 'E', 'N', upeq(w, pha, DLZ, 'K', czqc, zeq, 'Z0'), UP(DLZ, 'K', post), UP(DLZ, 'K', 'Z0'))
        tri2, _, _, _ = hrrw(w, pha, tri, CLN('A', 'N', DLZ), CLN('E', 'N', UP(DLZ, 'K', post)), '1', deq=deq)
        z0w = w.s([czq, A_(zw, '%s e. Word %s' % (zeq, GK))], 'eqeltrd', '( %s -> Z0 e. Word %s )' % (pha, GK))
        return w.s([z0w, tri2], 'jca', '( %s -> ( Z0 e. Word %s /\\ %s ) )' % (pha, GK, EXITZ))

    def common(A_):
        return ((A_(phm, PHM), A_(c['( M ` A ) = %s' % STPRD], '( M ` A ) = %s' % STPRD)),
                (A_(al, 'A e. %s' % LL), A_(el, 'E e. %s' % LL), A_(kk, 'K e. %s' % DG)))
    # tm2fpr0a / tm2fpr0b : program POP( K , F , BRANCH( C , Q , BRANCH( C' , PEEK( K , F' , BRANCH( C" , GE , PK( P , GE ) ) ) , R ) ) )
    #   Q := PU , P := P' , R := PK( P" , GE )
    def tree_ab(letters3):
        def t(A_, cif, dlk2):
            pm, lb = common(A_)
            lets = ((A_(zz, 'Z e. %s' % GK), A_(zp, "Z' e. %s" % GK), A_(zpp, 'Z" e. %s' % GK)) if letters3
                    else (A_(zz, 'Z e. %s' % GK), A_(zp, "Z' e. %s" % GK)))
            return (pm,
                    (lb, ((A_(ra, RATY), A_(ra2, RATY2), A_(cc, CTY)),
                          ((A_(c2, CTY2), A_(c3, CTY3), A_(pk1, PKTY("P'"))),
                           (A_(pucl, '%s e. %s' % (PU, STMT_T)), A_(pe2, '%s e. %s' % (PK('P"', GE), STMT_T)))))),
                    ((A_(dlcl, '%s e. %s' % (DLZ, STK_T)), dlk2, (lets, A_(xpw, "X' e. Word %s" % GK))),
                     (A_(nss, 'N C_ %s' % SS), cif)))
        return t
    # tm2fpr0c : program POP( K , F , BRANCH( C , Q , BRANCH( C' , R , PK( P , GE ) ) ) ) , Q := PU , R := PEEKST , P := P"
    def tree_c(A_, cif, dlk2):
        pm, lb = common(A_)
        return (pm,
                (lb, ((A_(ra, RATY), A_(cc, CTY), A_(c2, CTY2)),
                      (A_(pk2, PKTY('P"')), (A_(pucl, '%s e. %s' % (PU, STMT_T)), A_(pkcl, '%s e. %s' % (PEEKST, STMT_T)))))),
                ((A_(dlcl, '%s e. %s' % (DLZ, STK_T)), dlk2, ((A_(zz, 'Z e. %s' % GK), A_(yy, 'Y e. %s' % GK)), A_(xx, 'X e. Word %s' % GK))),
                 (A_(nss, 'N C_ %s' % SS), cif)))
    CA = '( X = %s /\\ %s /\\ Z0 = %s )' % (XPX, IFPA, PA)
    CB = '( X = %s /\\ %s /\\ Z0 = %s )' % (XPX, IFPB, PB)
    CC = '( %s /\\ Z0 = %s )' % (IFPC, PC)
    ca = case(CA, IFPA, PA, 'tm2fpr0a', tree_ab(False), PA, xpxw, True)
    cb = case(CB, IFPB, PB, 'tm2fpr0b', tree_ab(True), PB, pbw, True)
    cc_ = case(CC, IFPC, PC, 'tm2fpr0c', tree_c, PC, pcw, False)
    all3 = w.s([ca, cb, cc_], '3jaodan', '( ( %s /\\ %s ) -> ( Z0 e. Word %s /\\ %s ) )' % (ph, DISJ_PRD, GK, EXITZ))
    exz = w.s([disj, all3], 'mpdan', '( %s -> ( Z0 e. Word %s /\\ %s ) )' % (ph, GK, EXITZ))
    trw = PHTRW(QPRD)
    def leaves(t):
        if isinstance(t, str):
            if t == 'R e. Word %s' % GK:
                return zxw
            if t == '%s e. %s' % (QPRD, STMT_T):
                return qcl
            return c[t]
        return tuple(leaves(x) for x in t)
    PRE = CLN('A', 'N', UP2('( W ++ %s )' % ZX, 'H'))
    POST = CLN('E', 'N', UP2('Z0', RGWH))
    trwst, trwtxt = jtree(w, ph, leaves(trw))
    w.qed([w.s([w.s([trwst, ww], 'jca', '( %s -> ( %s /\\ W e. Word B ) )' % (ph, trwtxt)), exz], 'jca',
               '( %s -> ( ( %s /\\ W e. Word B ) /\\ ( Z0 e. Word %s /\\ %s ) ) )' % (ph, trwtxt, GK, EXITZ)),
           w.inst('tm2fscl')], 'syl', '( %s -> %s )' % (ph, HR(PRE, 'T', 'M', POST, '( ( # ` W ) + 1 )')))
    return w.run()


if __name__ == '__main__':
    if want('tm2fscl'): tm2fscl()
    if want('tm2fincl'): tm2fincl()
    if want('tm2fprdl'): tm2fprdl()
