"""Sortie T-MD: Canon.lean and MulDiv.lean of the machine layer, and the two
copyList N-level forms T6b left.

Statement texts (the frozen statements of TMD-blueprint.md are produced
here, `STMTS`) and helpers on top of tools/t5lib.py, tools/t5blib.py and
tools/t6blib.py (all read-only).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
import lin
lin.FASTPATH = True
from t6blib import *          # PHC, DATA, DATAN, ENC, ENCB, LST, NL, TMB, BLB, Ctx, Builder, inst, ...

# ------------------------------------------------------------- copyList, N level

PHCN = PHC.replace(DATA, DATAN)
assert PHCN != PHC
CFINN = UPDT('D', 'J', '( %s ++ ( D ` J ) )' % ENC('L'))
ST_CPYN = '( %s -> %s )' % (PHCN, HR(CL('P0', SS, 'D'), 'T', 'M', CL('E', "N'", CFINN), BCPY))
ST_CPYB2 = '( %s -> %s )' % (PHCN, HR(CL('P0', SS, 'D'), 'T', 'M', CL('E', "N'", CFINN), BLB))
T_PHCN = parse_conj(PHCN); assert cj(T_PHCN) == PHCN

STMTS_TMD = {'tm2lcpyn': ST_CPYN, 'tm2lcpyb2': ST_CPYB2}

# ============================================================ the machine layer
from t5blib import (GK, GJ, GI, GIP, HDL, CTY, LTY, PTY, RTY, LAB, STKD, STMT, CONST, S1, CC, WRD, FV, P1, MEQ, NV, SSS,
                    TRI, UP3, ren, flat, HT, HTF, inst_v, ifval, clnex, up6, up3cK, statement)
from t5lib import (lift, CLN, GT, UP, NVF, conj, cj, Ctx, Lifter, hrseq, hrle, hrssc, hrssd, hrrw, cfgcl, clnss, upid, updcl,
                   updkv, updnv, stkfv, elv, upc, up2, up3, up4, gotocl, pushcl, pushccl, popcl, peekcl, brcl, loadcl,
                   s1w, ccatw, revw, sswordd, jtree, applylem, nn0cl, bound, clneq, clnneq, upeq, upidv, GX, DG, LL,
                   STK_T, CFG_T, STMT_T, SS)
from t1lib import PUSH, PEEK, POP, LOAD, BRANCH, GOTO, UPD, CONSTF, HR, PHM, Exec, evaluate
from t3_lib import hstepc2

GH = GX('H')
YX = CC(S1('Y'), 'X')
WYX = CC('W', YX)

# ------------------------------------------------------------- Canon: N level

E_ = lambda L: '( encodeNat ` ( toNat ` %s ) )' % L
NZ = lambda L: '( ( # ` %s ) - ( # ` %s ) )' % (L, E_(L))
REP0 = lambda n: '( (/) repeatS %s )' % n
ST_STRIPLEN = '( L e. Word 2o -> ( # ` %s ) <_ ( # ` L ) )' % E_('L')
ST_STRIPH = '( L e. Word 2o -> L = ( %s ++ %s ) )' % (E_('L'), REP0(NZ('L')))
ST_STRIPREV = '( L e. Word 2o -> ( reverse ` L ) = ( %s ++ ( reverse ` %s ) ) )' % (REP0(NZ('L')), E_('L'))
IB = lambda X: '( inclBool o. %s )' % X
ST_STRIPREVG = ('( L e. Word 2o -> ( reverse ` %s ) = ( ( <. 1 , (/) >. repeatS %s ) ++ ( reverse ` %s ) ) )'
                % (IB('L'), NZ('L'), IB(E_('L'))))
ST_STRIPFST = '( N e. NN -> ( ( reverse ` %s ) ` 0 ) = <. 1 , 1o >. )' % IB('( encodeNat ` N )')

# ------------------------------------------------------------- the strip loop

GA = GT('A'); GE = GT('E')
STM_SP = PEEK('K', 'F', BRANCH('C', POP('K', "F'", GA), GE))
HSPC = lambda N: ('A. r e. %s A. z e. B0 ( ( C ` %s ) = 1o /\\ %s e. %s )'
                  % (N, NV('F', 'r', 'z'), NV("F'", NV('F', 'r', 'z'), 'z'), N))
HSPE = lambda N, Y: 'A. m e. %s ( -. ( C ` %s ) = 1o /\\ %s e. %s )' % (N, NV('F', 'm', Y), NV('F', 'm', Y), N)
LAB_SP = (LAB('A'), LAB('E'), 'K e. %s' % DG)
FTY_SP = ((RTY('F', 'K'), RTY("F'", 'K'), CTY('C')), 'B0 C_ %s' % GK)
# the continue step (x a word of B0 to be popped, R the rest of the stack)
TREE_SP1 = ((((PHM, MEQ('A', STM_SP)), (LAB_SP, FTY_SP), ((STKD('D'), WRD('R', GK)), (SSS('N'), HSPC('N')))),
             WRD('x', 'B0')), 'x =/= (/)')
XR = CC('x', 'R'); TLX = '( x substr <. 1 , ( # ` x ) >. )'
CONCL_SP1 = TRI(CLN('A', 'N', UP('D', 'K', XR)), CLN('A', 'N', UP('D', 'K', CC(TLX, 'R'))), '1')
PH_SP1 = TREE_SP1[0][0]
TREE_SPW = (PH_SP1, WRD('W', 'B0'))
CONCL_SPW = TRI(CLN('A', 'N', UP('D', 'K', CC('W', 'R'))), CLN('A', 'N', UP('D', 'K', CC('(/)', 'R'))), '( # ` W )')
# the exit step
TREE_SP0 = ((PHM, MEQ('A', STM_SP)), (LAB_SP, FTY_SP),
            ((STKD('D'), '( D ` K ) = %s' % YX, ('Y e. %s' % GK, WRD('X', GK))), (SSS('N'), HSPE('N', 'Y'))))
CONCL_SP0 = TRI(CLN('A', 'N', 'D'), CLN('E', 'N', 'D'), '1')
# the fragment
TREE_SP = (((PHM, MEQ('A', STM_SP)), (LAB_SP, (FTY_SP, 'Y e. %s' % GK)),
            ((STKD('D'), WRD('X', GK)), (SSS('N'), (HSPC('N'), HSPE('N', 'Y'))))), WRD('W', 'B0'))
CONCL_SP = TRI(CLN('A', 'N', UP('D', 'K', WYX)), CLN('E', 'N', UP('D', 'K', YX)), '( ( # ` W ) + 1 )')

# ------------------------------------------------------------- canonNum

ST_C1 = PUSH('J', CONST('Y'), GT("A'"))
ST_CMV1 = POP('K', 'F', BRANCH('C', PUSH('J', 'P', GT("A'")), GT('A"')))
ST_CSP = PEEK('J', "F'", BRANCH("C'", POP('J', 'F"', GT('A"')), GT("E'")))
ST_C4 = PUSH('K', CONST('Y'), GT('E"'))
ST_CMV2 = POP('J', 'F', BRANCH('C', PUSH('K', 'P', GT('E"')), GT('E')))
HCMVG = lambda N: ('A. r e. %s A. z e. B ( ( C ` %s ) = 1o /\\ ( P ` %s ) = ( G ` z ) /\\ %s e. %s )'
                   % (N, NV('F', 'r', 'z'), NV('F', 'r', 'z'), NV('F', 'r', 'z'), N))
HEMVG = lambda N: 'A. m e. %s ( -. ( C ` %s ) = 1o /\\ %s e. %s )' % (N, NV('F', 'm', 'Y'), NV('F', 'm', 'Y'), N)
HSPC2 = lambda N: ('A. r e. %s A. z e. B0 ( ( C\' ` %s ) = 1o /\\ %s e. %s )'
                   % (N, NV("F'", 'r', 'z'), NV('F"', NV("F'", 'r', 'z'), 'z'), N))
HSPE2 = lambda N, Y: 'A. m e. %s ( -. ( C\' ` %s ) = 1o /\\ %s e. %s )' % (N, NV("F'", 'm', Y), NV("F'", 'm', Y), N)
GW = '( G o. W )'
RGW = '( reverse ` %s )' % GW
RGWP = "( reverse ` ( G o. W' ) )"
TREE_CAN = (((PHM, (MEQ('A', ST_C1), MEQ("A'", ST_CMV1)), (MEQ('A"', ST_CSP), MEQ("E'", ST_C4), MEQ('E"', ST_CMV2))),
             (((LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E"'), LAB('E'))), ('K e. %s' % DG, 'J e. %s' % DG, 'K =/= J')),
             (((RTY('F', 'K'), RTY('F', 'J')), (PTY('P', 'J'), PTY('P', 'K')), CTY('C')),
              ((RTY("F'", 'J'), RTY('F"', 'J')), CTY("C'")))),
            (((('B C_ %s' % GK, 'B C_ %s' % GJ), ('B0 C_ B', 'G : B --> B')), ('Y e. %s' % GK, 'Y e. %s' % GJ), ("Y' e. %s" % GJ, WRD("X'", GJ))),
             (((WRD('W', 'B'), WRD('X', GK)), (WRD('W0', 'B0'), WRD("W'", 'B'))),
              ('%s = %s' % (RGW, CC('W0', "W'")), "( W' ++ <\" Y \"> ) = %s" % CC(S1("Y'"), "X'")),
              (STKD('D'), '( D ` K ) = %s' % WYX)),
             (SSS('N'), (HCMVG('N'), HEMVG('N')), (HSPC2('N'), HSPE2('N', "Y'")))))
CONCL_CAN = TRI(CLN('A', 'N', 'D'), CLN('E', 'N', UP('D', 'K', CC(RGWP, YX))), '( ( 2 x. ( # ` W ) ) + 5 )')

# ------------------------------------------------------------- the generic pop at a class

STM_POPN = POP('K', 'F', GE)
TREE_POPN = (((PHM, MEQ('A', STM_POPN)), (LAB('A'), LAB('E'), 'K e. %s' % DG)),
             ((RTY('F', 'K'), STKD('D')), ('( D ` K ) = %s' % CC(S1('Z'), 'X'), 'Z e. %s' % GK, WRD('X', GK)),
              ((SSS('N'), SSS("N'")), 'A. r e. N %s e. N\'' % NV('F', 'r', 'Z'))))
CONCL_POPN = TRI(CLN('A', 'N', 'D'), CLN('E', "N'", UP('D', 'K', 'X')), '1')

# ------------------------------------------------------------- mul: the iteration

STM_MT = BRANCH('C0', GT('B0'), 'Q')             # the loop test (exit branch abstract)
STM_MTE = BRANCH('C0', GT('B0'), GT('E'))        # the loop test with its exit
STM_MI = BRANCH('C', GT("B'"), GT('E0'))         # Frag.ite
STM_MSK = LOAD("L'", GT('B"'))                   # Frag.skip
STM_MPZ = PUSH('K', CONST('Z0'), GT('A0'))       # push (bit false) on x
STM_MPB = POP('J', 'F', GA)                      # popBit y, back to the test
HTC = lambda N: 'A. m e. %s ( C ` m ) = 1o' % N
HTCF = lambda N: 'A. m e. %s -. ( C ` m ) = 1o' % N
HPB = lambda N, U, N2: 'A. r e. %s %s e. %s' % (N, NV('F', 'r', U), N2)
DISJ_ML = ('( ( %s /\\ %s ) \\/ ( %s /\\ H\' = ( D ` I ) ) )'
           % (HTC('N'), TRI(CLN("B'", 'N', 'D'), CLN('B"', SS, UP('D', 'I', "H'")), "T'"), HTCF('N')))
TREE_MLB = ((((PHM, MEQ('A', STM_MT), MEQ('B0', STM_MI)), (MEQ('E0', STM_MSK), MEQ('B"', STM_MPZ), MEQ('A0', STM_MPB))),
             (((LAB('A'), LAB('B0'), LAB("B'")), (LAB('B"'), LAB('E0'), LAB('A0'))),
              (('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG), ('K =/= J', 'K =/= I', 'J =/= I')),
              ((CTY('C0'), CTY('C'), LTY("L'")), (RTY('F', 'J'), STMT('Q')), ('Z0 e. %s' % GK, 'U e. %s' % GJ)))),
            (((STKD('D'), '( D ` J ) = %s' % CC(S1('U'), "Y'")), (WRD("Y'", GJ), WRD("H'", GI)), ("T' e. NN0", "1 <_ T'")),
             ((SSS('N'), SSS("N'")), (HT('N'), HPB(SS, 'U', "N'"))),
             DISJ_ML))
POST_MLB = UP3('D', 'I', "H'", 'K', CC(S1('Z0'), '( D ` K )'), 'J', "Y'")
CONCL_MLB = TRI(CLN('A', 'N', 'D'), CLN('A', "N'", POST_MLB), "( T' + 4 )")

# ------------------------------------------------------------- mul: the loop (families)

XF = lambda i: '( X ` %s )' % i
YF = lambda i: '( Y ` %s )' % i
HF = lambda i: '( H ` %s )' % i
NF = lambda i: '( N ` %s )' % i
UF = lambda i: '( U ` %s )' % i
DPM = lambda i: UP3('D', 'I', HF(i), 'K', XF(i), 'J', YF(i))


def DISJ_MQ(i):
    i1 = P1(i)
    return ('( ( %s /\\ %s ) \\/ ( %s /\\ %s = %s ) )'
            % (HTC(NF(i)), TRI(CLN("B'", NF(i), DPM(i)), CLN('B"', SS, UP(DPM(i), 'I', HF(i1))), "T'"),
               HTCF(NF(i)), HF(i1), HF(i)))


def HYP_MQ_TREE(i):
    i1 = P1(i)
    return ((('%s = %s' % (YF(i), CC(S1(UF(i1)), YF(i1))), '%s = %s' % (XF(i1), CC(S1('Z0'), XF(i)))), '%s e. %s' % (UF(i1), GJ)),
            (HT(NF(i)), HPB(SS, UF(i1), NF(i1))),
            DISJ_MQ(i))


HYPS_MQ = 'A. i e. ( 0 ..^ R ) %s' % cj(HYP_MQ_TREE('i'))
FAMB_MQ = lambda i: ((WRD(XF(i), GK), WRD(YF(i), GJ), WRD(HF(i), GI)), SSS(NF(i)))
FAM_MQ = 'A. i e. ( 0 ... R ) %s' % cj(FAMB_MQ('i'))
TREE_MLQ = ((((PHM, MEQ('A', STM_MTE), MEQ('B0', STM_MI)), (MEQ('E0', STM_MSK), MEQ('B"', STM_MPZ), MEQ('A0', STM_MPB))),
             (((LAB('A'), LAB('B0'), LAB("B'")), (LAB('B"'), LAB('E0'), LAB('A0')), LAB('E')),
              (('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG), ('K =/= J', 'K =/= I', 'J =/= I')),
              ((CTY('C0'), CTY('C'), LTY("L'")), RTY('F', 'J'), 'Z0 e. %s' % GK))),
            ((STKD('D'), ('R e. NN0', "T' e. NN0", "1 <_ T'")), (FAM_MQ, HYPS_MQ)))
CONCL_MLQ = TRI(CLN('A', NF('0'), DPM('0')), CLN('A', NF('R'), DPM('R')), "( R x. ( T' + 4 ) )")

# ------------------------------------------------------------- mul assembled

ST_MP0 = PUSH('I', CONST('Y'), GT('P1'))
ST_MP1 = POP('J', 'F', GA)
ST_MDR = POP('K', "F'", BRANCH("C'", GE, GT("E'")))
HCDR = "A. r e. %s A. z e. B ( C' ` %s ) = 1o" % (SS, NV("F'", 'r', 'z'))
HEDR = "A. r e. %s -. ( C' ` %s ) = 1o" % (SS, NV("F'", 'r', 'Y'))
INIT_ML = ('( %s = ( D ` K ) /\\ %s = %s /\\ ( D ` J ) = %s )'
           % (XF('0'), HF('0'), CC(S1('Y'), '( D ` I )'), CC(S1(UF('0')), YF('0'))))
YX0 = CC(S1('Y'), 'X0')
FIN_ML = ('( ( %s = %s /\\ %s ) /\\ ( WRD_X0 /\\ %s ) )' % (XF('R'), CC('W', YX0), WRD('W', 'B'), HTF(NF('R'), 'C0'))).replace('WRD_X0', WRD('X0', GK))
TREE_ML = (((PHM, (MEQ('P0', ST_MP0), MEQ('P1', ST_MP1)), (MEQ('A', STM_MTE), MEQ('B0', STM_MI))),
            ((MEQ('E0', STM_MSK), MEQ('B"', STM_MPZ)), (MEQ('A0', STM_MPB), MEQ('E', ST_MDR)))),
           ((((LAB('P0'), LAB('P1'), LAB('A')), (LAB('B0'), LAB("B'"), LAB('B"')), (LAB('E0'), LAB('A0'), (LAB('E'), LAB("E'")))),
             (('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG), ('K =/= J', 'K =/= I', 'J =/= I'))),
            (((CTY('C0'), CTY('C'), CTY("C'")), (LTY("L'"), RTY('F', 'J'), RTY("F'", 'K'))),
             (('B C_ %s' % GK, 'Z0 e. %s' % GK), ('Y e. %s' % GK, 'Y e. %s' % GI), '%s e. %s' % (UF('0'), GJ)))),
           (((STKD('D'), INIT_ML), (('R e. NN0', "T' e. NN0", "1 <_ T'"), (SSS('N0'), HPB('N0', UF('0'), NF('0'))))),
            ((HCDR, HEDR), (FAM_MQ, HYPS_MQ)), FIN_ML))
CONCL_ML = TRI(CLN('P0', 'N0', 'D'), CLN("E'", SS, UP3('D', 'I', HF('R'), 'K', 'X0', 'J', YF('R'))),
               "( ( R x. ( T' + 4 ) ) + ( ( # ` W ) + 4 ) )")

STATEMENTS = [
    ('tm2fsp1', TREE_SP1, CONCL_SP1), ('tm2fspw', TREE_SPW, CONCL_SPW), ('tm2fsp0', TREE_SP0, CONCL_SP0),
    ('tm2fsp', TREE_SP, CONCL_SP), ('tm2fcan', TREE_CAN, CONCL_CAN), ('tm2fpopn', TREE_POPN, CONCL_POPN),
    ('tm2fmlb', TREE_MLB, CONCL_MLB), ('tm2fmlq', TREE_MLQ, CONCL_MLQ), ('tm2fml', TREE_ML, CONCL_ML)]
NSTMTS = [('bwstriplen', ST_STRIPLEN), ('bwstriph', ST_STRIPH), ('bwstriprev', ST_STRIPREV),
          ('bwstriprevg', ST_STRIPREVG), ('bwstripfst', ST_STRIPFST)]


# ------------------------------------------------------------- proof helpers

def hdapply(w, av, F, fty, r, rcl, Z, zcl, k='K'):
    """( av -> NV( F ; r , Z ) e. S ) from fty : F e. HDL( k ), rcl : r e. S, zcl : Z e. Gk"""
    OPTK = '( %s |_| 1o )' % GX(k)
    ff = w.s([fty, w.inst('elmapi')], 'syl', '( %s -> %s : ( %s X. %s ) --> %s )' % (av, F, SS, OPTK, SS))
    zi = w.s([zcl, w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (av, Z, OPTK))
    op = w.s([rcl, zi], 'opelxpd', '( %s -> <. %s , ( inl ` %s ) >. e. ( %s X. %s ) )' % (av, r, Z, SS, OPTK))
    return w.s([ff, op], 'ffvelcdmd', '( %s -> %s e. %s )' % (av, NV(F, r, Z), SS))


def ral2at(w, av, body_rz, hyp, vst, vcl, Z, zcl, dom='B0'):
    """instantiate hyp : ( av -> A. r e. N A. z e. dom body(r,z) ) at r := v (vcl : v e. N)
    and z := Z (zcl : Z e. dom); returns the step proving ( av -> body(v,Z) )"""
    inner = 'A. z e. %s %s' % (dom, body_rz)
    cg, new = W.wcongr(w, inner, {'r': 'v'}, 'r = v', {'r': w.s([], 'id', '( r = v -> r = v )')})
    h1 = w.s([cg, hyp, vcl], 'rspcdva', '( %s -> %s )' % (av, new))
    bv = new[len('A. z e. %s ' % dom):]
    cg2, new2 = W.wcongr(w, bv, {'z': Z}, 'z = %s' % Z, {'z': w.s([], 'id', '( z = %s -> z = %s )' % (Z, Z))})
    return w.s([cg2, h1, zcl], 'rspcdva', '( %s -> %s )' % (av, new2)), new2


def ralat(w, av, body_m, hyp, vcl, v='v', m='m'):
    """instantiate hyp : ( av -> A. m e. N body(m) ) at m := v"""
    cg, new = W.wcongr(w, body_m, {m: v}, '%s = %s' % (m, v), {m: w.s([], 'id', '( %s = %s -> %s = %s )' % (m, v, m, v))})
    return w.s([cg, hyp, vcl], 'rspcdva', '( %s -> %s )' % (av, new)), new


MTY = 'M : ( 2nd ` ( 1st ` T ) ) --> ( TM2Stmt ` T )'


def bldr(w, ph, c, phm, extra=None):
    """a Builder whose extras include the two halves of PHM"""
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    mt = w.s([phm, w.inst('simpr')], 'syl', '( %s -> %s )' % (ph, MTY))
    ex = {'T e. V': tv, MTY: mt}
    ex.update(extra or {})
    return Builder(w, ph, c, ex)


def up6g(w, ph, D, a, b, c_, Y, Yp, Z, Zp, Nw, Npw, tv, dd, nab, nac, nbc, aa, bb, cc, yw, ypw, zw, zpw, nw, npw):
    """tm2stkup6 at K := a , J := b , I := c_:
    UPD3( UPD3( D ; a , Y ; b , Z ; c_ , Nw ) ; a , Yp ; b , Zp ; c_ , Npw ) = UPD3( D ; a , Yp ; b , Zp ; c_ , Npw );
    nab : a =/= b, nac : a =/= c_, nbc : b =/= c_; the words typed at GX(a), GX(b), GX(c_)"""
    GA_, GB_, GC_ = GX(a), GX(b), GX(c_)
    p1 = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T)),
              w.s([nab, nac, nbc], '3jca', '( %s -> ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) )' % (ph, a, b, a, c_, b, c_))], 'jca',
             '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) ) )' % (ph, D, STK_T, a, b, a, c_, b, c_))
    p2 = w.s([aa, w.s([yw, ypw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Y, GA_, Yp, GA_))], 'jca',
             '( %s -> ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, a, DG, Y, GA_, Yp, GA_))
    q1 = w.s([bb, w.s([zw, zpw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Z, GB_, Zp, GB_))], 'jca',
             '( %s -> ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, b, DG, Z, GB_, Zp, GB_))
    q2 = w.s([cc, w.s([nw, npw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Nw, GC_, Npw, GC_))], 'jca',
             '( %s -> ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, c_, DG, Nw, GC_, Npw, GC_))
    p3 = w.s([q1, q2], 'jca', '( %s -> ( ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) /\\ ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) ) )'
             % (ph, b, DG, Z, GB_, Zp, GB_, c_, DG, Nw, GC_, Npw, GC_))
    LHS = UP3(UP3(D, a, Y, b, Z, c_, Nw), a, Yp, b, Zp, c_, Npw)
    RHS = UP3(D, a, Yp, b, Zp, c_, Npw)
    return w.s([p1, p2, p3, w.inst('tm2stkup6')], 'syl3anc', '( %s -> %s = %s )' % (ph, LHS, RHS)), RHS


def leafsteps(tree, look):
    if isinstance(tree, str):
        return look(tree)
    return tuple(leafsteps(t, look) for t in tree)


def dpmfacts(w, ph, X, tv, dd, kk, jj, ii, nkj, nki, nji, hw, xw, yw):
    """DPM( X ) = UPD3( D ; I , H ; K , X ; J , Y ) e. Stk and its values at I , K , J"""
    a = updcl(w, ph, 'D', 'I', HF(X), tv, dd, ii, hw)
    b = updcl(w, ph, UP('D', 'I', HF(X)), 'K', XF(X), tv, a, kk, xw)
    d = updcl(w, ph, UP(UP('D', 'I', HF(X)), 'K', XF(X)), 'J', YF(X), tv, b, jj, yw)
    hv, xv, yv = elv(w, ph, hw, HF(X)), elv(w, ph, xw, XF(X)), elv(w, ph, yw, YF(X))
    U1 = UP('D', 'I', HF(X)); U2 = UP(U1, 'K', XF(X))
    njk = w.s([nkj], 'necomd', '( %s -> J =/= K )' % ph)
    nik = w.s([nki], 'necomd', '( %s -> I =/= K )' % ph)
    nij = w.s([nji], 'necomd', '( %s -> I =/= J )' % ph)
    # ( DPM ` J ) = Y
    vj = updkv(w, ph, U2, 'J', YF(X), tv, b, jj, yv)
    # ( DPM ` K ) = ( U2 ` K ) = X
    vk1 = updnv(w, ph, U2, 'J', YF(X), 'K', tv, b, jj, yv, kk, nkj)
    vk2 = updkv(w, ph, U1, 'K', XF(X), tv, a, kk, xv)
    vk = w.s([vk1, vk2], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, DPM(X), XF(X)))
    # ( DPM ` I ) = ( U2 ` I ) = ( U1 ` I ) = H
    vi1 = updnv(w, ph, U2, 'J', YF(X), 'I', tv, b, jj, yv, ii, nij)
    vi2 = updnv(w, ph, U1, 'K', XF(X), 'I', tv, a, kk, xv, ii, nik)
    vi3 = updkv(w, ph, 'D', 'I', HF(X), tv, dd, ii, hv)
    vi = w.s([w.s([vi1, vi2], 'eqtrd', '( %s -> ( %s ` I ) = ( %s ` I ) )' % (ph, DPM(X), U1)), vi3], 'eqtrd',
             '( %s -> ( %s ` I ) = %s )' % (ph, DPM(X), HF(X)))
    return d, vi, vk, vj


# ============================================================ divmod (blueprint 6.1, frozen here)
# stacks: K = x (dividend / remainder), J = y (divisor), I = q (quotient), I' = j (shift counter);
# the scratch stacks s t live inside the hypothesis triples only.
GIP = GX("I'")
QF = lambda i: '( Q ` %s )' % i
N1F = lambda i: '( N1 ` %s )' % i
N2F = lambda i: '( N2 ` %s )' % i
N3F = lambda i: '( N3 ` %s )' % i
DPU = lambda i: UP(UP('D', 'J', YF(i)), "I'", QF(i))                                # the up loop's family
DPD = lambda i: UP(UP(UP(UP('D', "I'", QF(i)), 'J', YF(i)), 'I', HF(i)), 'K', XF(i))  # the down loop's family
IDX4 = (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, "I' e. %s" % DG))
DIST4 = (('K =/= J', 'K =/= I', "K =/= I'"), ('J =/= I', "J =/= I'", "I =/= I'"))

# ---- the shift-up iteration: test at A (C0), push Z0 on J at B0 -> B', the composite
#      ` incr j s ; dup y t s ; dup x s t ; cmpFrag t s ` as one triple B' -> A
STM_UT = BRANCH('C0', GT('B0'), 'Q')
STM_UTE = BRANCH('C0', GT('B0'), GT('E'))
STM_UPZ = PUSH('J', CONST('Z0'), GT("B'"))
Z0DJ = CC(S1('Z0'), '( D ` J )')
TRIP_UB = TRI(CLN("B'", 'N', UP('D', 'J', Z0DJ)), CLN('A', "N'", UP(UP('D', 'J', Z0DJ), "I'", "Q'")), "T'")
TREE_DMUB = ((((PHM, MEQ('A', STM_UT), MEQ('B0', STM_UPZ)), ((LAB('A'), LAB('B0'), LAB("B'")), ('J e. %s' % DG, "I' e. %s" % DG), (CTY('C0'), STMT('Q')))),
              ('Z0 e. %s' % GJ, WRD("Q'", GIP), "T' e. NN0")),
             ((STKD('D'), (SSS('N'), SSS("N'"))), (HT('N'), TRIP_UB)))
CONCL_DMUB = TRI(CLN('A', 'N', 'D'), CLN('A', "N'", UP(UP('D', 'J', Z0DJ), "I'", "Q'")), "( T' + 2 )")


def TRIP_UQ(i):
    i1 = P1(i)
    return TRI(CLN("B'", NF(i), UP(DPU(i), 'J', YF(i1))), CLN('A', NF(i1), UP(UP(DPU(i), 'J', YF(i1)), "I'", QF(i1))), "T'")


def HYP_UQ_TREE(i):
    i1 = P1(i)
    return ('%s = %s' % (YF(i1), CC(S1('Z0'), YF(i))), HT(NF(i)), TRIP_UQ(i))


HYPS_UQ = 'A. i e. ( 0 ..^ R ) %s' % cj(HYP_UQ_TREE('i'))
FAMB_UQ = lambda i: ((WRD(YF(i), GJ), WRD(QF(i), GIP)), SSS(NF(i)))
FAM_UQ = 'A. i e. ( 0 ... R ) %s' % cj(FAMB_UQ('i'))
TREE_DMUQ = ((((PHM, MEQ('A', STM_UTE), MEQ('B0', STM_UPZ)), ((LAB('A'), LAB('B0'), LAB("B'")), LAB('E'))),
              (('J e. %s' % DG, "I' e. %s" % DG, "J =/= I'"), (CTY('C0'), 'Z0 e. %s' % GJ))),
             ((STKD('D'), ('R e. NN0', "T' e. NN0")), (FAM_UQ, HYPS_UQ)))
CONCL_DMUQ = TRI(CLN('A', NF('0'), DPU('0')), CLN('A', NF('R'), DPU('R')), "( R x. ( T' + 2 ) )")

# ---- the shift-down iteration (Lean dmDownBody): test at A (C0); predNum j s (triple B0 -> B',
#      N -> N1); popBit y at B' (F, N1 -> N"); push Z0 on I at B" -> D0; ` dup y t s ; dup x s t ;
#      cmpFrag t s ` (triple D0 -> E0, N" -> N0); Frag.ite at E0 on C (cmp =/= gt): ` dup y t s ;
#      subx x t s x ; incr q s ` (triple B1_ -> G0, into S) or skip at E" (L') -> G0; isZero j s
#      (triple G0 -> A, S -> N').  Bounds T1 T" T0 T' (the pool has no T2_ T3_ T4_ N2 N3).
STM_DT = BRANCH('C0', GT('B0'), 'Q')
STM_DTE = BRANCH('C0', GT('B0'), GT('E'))
STM_DPB = POP('J', 'F', GT('B"'))
STM_DPZ = PUSH('I', CONST('Z0'), GT('D0'))
STM_DI = BRANCH('C', GT('B1_'), GT('E"'))
STM_DSK = LOAD("L'", GT('G0'))
D1D = UP('D', "I'", "Q'")
D2D = UP(D1D, 'J', "Y'")
Z0DI = CC(S1('Z0'), '( D ` I )')
D3D = UP(D2D, 'I', Z0DI)
D7D = UP(UP(D3D, 'K', "X'"), 'I', "H'")
TRIP_D1 = TRI(CLN('B0', 'N', 'D'), CLN("B'", 'N1', D1D), 'T1')
TRIP_D2 = TRI(CLN('D0', 'N"', D3D), CLN('E0', 'N0', D3D), 'T"')
TRIP_D3 = TRI(CLN('B1_', 'N0', D3D), CLN('G0', SS, D7D), 'T0')
TRIP_D4 = TRI(CLN('G0', SS, D7D), CLN('A', "N'", D7D), "T'")
DISJ_DL = ('( ( %s /\\ %s ) \\/ ( %s /\\ ( X\' = ( D ` K ) /\\ H\' = %s ) ) )' % (HTC('N0'), TRIP_D3, HTCF('N0'), Z0DI))
PROG_DB = (PHM, (MEQ('A', STM_DT), MEQ("B'", STM_DPB)), (MEQ('B"', STM_DPZ), MEQ('E0', STM_DI), MEQ('E"', STM_DSK)))
LABS_DB = ((LAB('A'), LAB('B0'), LAB("B'")), (LAB('B"'), LAB('D0'), LAB('E0')), (LAB('B1_'), LAB('E"'), LAB('G0')))
TYPS_DB = ((CTY('C0'), CTY('C'), LTY("L'")), (RTY('F', 'J'), STMT('Q')), ('Z0 e. %s' % GJ, 'Z0 e. %s' % GI))
BNDS_D = (('T1 e. NN0', 'T" e. NN0'), ("T0 e. NN0", "T' e. NN0"), '1 <_ T0')
DATA_DB = ((STKD('D'), '( D ` J ) = %s' % CC(S1('Z0'), "Y'")), ((WRD("Q'", GIP), WRD("Y'", GJ)), (WRD("X'", GK), WRD("H'", GI))), BNDS_D)
CLS_DB = (((SSS('N'), SSS('N1')), (SSS('N"'), SSS('N0')), SSS("N'")), (HT('N'), HPB('N1', 'Z0', 'N"')))
TREE_DMDB = ((PROG_DB, (LABS_DB, (IDX4, DIST4), TYPS_DB)), (DATA_DB, CLS_DB, ((TRIP_D1, TRIP_D2), TRIP_D4, DISJ_DL)))
POST_DMDB = UP(UP(UP(UP('D', "I'", "Q'"), 'J', "Y'"), 'I', "H'"), 'K', "X'")
TD4 = '( ( ( T1 + T" ) + ( T0 + T\' ) ) + 4 )'
CONCL_DMDB = TRI(CLN('A', 'N', 'D'), CLN('A', "N'", POST_DMDB), TD4)

# ---- the shift-down loop: the stacks of the iterations are a FAMILY ` ( P ` i ) ` (blueprint D8):
#      the per-iteration hypotheses are tm2fdmdb's at D := ( P ` i ), and the step equation
#      ` ( P ` ( i + 1 ) ) = POST_DMDB[ D := ( P ` i ) ] ` replaces the eight-update collapse
#      (T7 proves it once, generically in i, by ~ tm2stkup8 ).
PF = lambda i: '( P ` %s )' % i
N2F = lambda i: '( N" ` %s )' % i
N3F = lambda i: '( N0 ` %s )' % i


def DMD_MAP(i):
    i1 = P1(i)
    return {'N': NF(i), 'N1': N1F(i), 'N"': N2F(i), 'N0': N3F(i), "N'": NF(i1), 'D': PF(i),
            "Q'": QF(i1), "Y'": YF(i1), "X'": XF(i1), "H'": HF(i1)}


def DMD_AT(i):
    """the three hypothesis triples, the disjunction and the post stack of the down iteration at i"""
    m = DMD_MAP(i)
    return sub(TRIP_D1, m), sub(TRIP_D2, m), sub(TRIP_D4, m), sub(DISJ_DL, m), sub(POST_DMDB, m)


def HYP_DQ_TREE(i):
    i1 = P1(i)
    t1, t2, t4, dj, post = DMD_AT(i)
    return ((('( %s ` J ) = %s' % (PF(i), CC(S1('Z0'), YF(i1))), '%s = %s' % (PF(i1), post)), (HT(NF(i)), HPB(N1F(i), 'Z0', N2F(i)))),
            ((SSS(N1F(i)), SSS(N2F(i))), SSS(N3F(i))),
            ((t1, t2), t4, dj))


HYPS_DQ = 'A. i e. ( 0 ..^ R ) %s' % cj(HYP_DQ_TREE('i'))
FAMB_DQ = lambda i: (((WRD(XF(i), GK), WRD(YF(i), GJ)), (WRD(HF(i), GI), WRD(QF(i), GIP))), (STKD(PF(i)), SSS(NF(i))))
FAM_DQ = 'A. i e. ( 0 ... R ) %s' % cj(FAMB_DQ('i'))
PROG_DQ = (PHM, (MEQ('A', STM_DTE), MEQ("B'", STM_DPB)), (MEQ('B"', STM_DPZ), MEQ('E0', STM_DI), MEQ('E"', STM_DSK)))
LABS_DQ = (LABS_DB, LAB('E'))
TYPS_DQ = ((CTY('C0'), CTY('C'), LTY("L'")), RTY('F', 'J'), ('Z0 e. %s' % GJ, 'Z0 e. %s' % GI))
DATA_DQ = ('R e. NN0', BNDS_D)
TREE_DMDQ = ((PROG_DQ, (LABS_DQ, (IDX4, DIST4), TYPS_DQ)), (DATA_DQ, (FAM_DQ, HYPS_DQ)))
CONCL_DMDQ = TRI(CLN('A', NF('0'), PF('0')), CLN('A', NF('R'), PF('R')), '( R x. %s )' % TD4)

STATEMENTS += [('tm2fdmub', TREE_DMUB, CONCL_DMUB), ('tm2fdmuq', TREE_DMUQ, CONCL_DMUQ),
               ('tm2fdmdb', TREE_DMDB, CONCL_DMDB), ('tm2fdmdq', TREE_DMDQ, CONCL_DMDQ)]

# ============================================================ divmodCore assembled (Lean divmodCore_runs)
# Labels: P0 push Y on I' (pushNum j 0) -> P1; P1 ` dup y t s ; dup x s t ; cmpFrag t s ` (triple, O -> ( N' ` 0 ))
# -> A; A .. B' the up loop (families Y' Q' N', count R, iteration bound U'); A -> E on the failed test;
# E push Y on I (pushSym q comma) -> E1; E1 ` isZero j s ` (triple, into ( N ` 0 ) at ( P ` 0 )) -> A';
# A' .. G0 the down loop (test C", families X Y H Q N N1 N" N0 P, count R'); A' -> E' on the failed test;
# E' dropNum I' (F' C', the counter word W e. Word B) -> G'.
UPMAP = {'Y': "Y'", 'Q': "Q'", 'N': "N'", "T'": "U'"}
DNMAP = {'A': "A'", 'B0': 'A"', "B'": 'A0', 'E': "E'", 'C0': 'C"'}
DPU_ = lambda i: sub(DPU(i), UPMAP)
YIP = CC(S1('Y'), "( D ` I' )")
YDI = CC(S1('Y'), '( D ` I )')
TRIP_C1 = TRI(CLN('P1', 'O', UP('D', "I'", YIP)), CLN('A', "( N' ` 0 )", DPU_('0')), 'U"')
TRIP_C2 = TRI(CLN('E1', "( N' ` R )", UP(DPU_('R'), 'I', YDI)), CLN("A'", NF('0'), PF('0')), 'U0')
STM_CP0 = PUSH("I'", CONST('Y'), GT('P1'))
STM_CE = PUSH('I', CONST('Y'), GT('E1'))
STM_CDR = POP("I'", "F'", BRANCH("C'", GT("E'"), GT("G'")))
PROG_C1 = ((PHM, MEQ('P0', STM_CP0)), (MEQ('A', STM_UTE), MEQ('B0', STM_UPZ), MEQ('E', STM_CE)))
LABS_C1 = ((LAB('P0'), LAB('P1'), LAB('A')), (LAB('B0'), LAB("B'"), LAB('E')), LAB('E1'))
FAM_UQ_ = sub(FAM_UQ, UPMAP); HYPS_UQ_ = sub(HYPS_UQ, UPMAP)
HCDR_ = "A. r e. %s A. z e. B ( C' ` %s ) = 1o" % (SS, NV("F'", 'r', 'z'))
HEDR_ = "A. r e. %s -. ( C' ` %s ) = 1o" % (SS, NV("F'", 'r', 'Y'))
TREE_DMC1 = ((PROG_C1, (LABS_C1, (IDX4, DIST4), ((CTY('C0'), 'Z0 e. %s' % GJ), ('Y e. %s' % GIP, 'Y e. %s' % GI)))),
             (((STKD('D'), SSS('O')), (('R e. NN0', "U' e. NN0"), ('U" e. NN0', 'U0 e. NN0'))),
              ((FAM_UQ_, HYPS_UQ_), HTF("( N' ` R )")),
              ((TRIP_C1, TRIP_C2), (STKD(PF('0')), SSS(NF('0'))))))
CONCL_DMC1 = TRI(CLN('P0', 'O', 'D'), CLN("A'", NF('0'), PF('0')), '( ( ( U" + U0 ) + ( R x. ( U\' + 2 ) ) ) + 3 )')
# the second half: the down loop from A', its failed test, dropNum I'
PROG_DQ_ = ren(PROG_DQ, DNMAP)
LABS_DQ_ = ren(LABS_DQ, DNMAP)
TYPS_C2 = ((CTY('C"'), CTY('C'), CTY("C'")), (LTY("L'"), RTY('F', 'J'), RTY("F'", "I'")),
           (('Z0 e. %s' % GJ, 'Z0 e. %s' % GI), ('Y e. %s' % GIP, 'B C_ %s' % GIP)))
FAM_DQ_ = sub(FAM_DQ, {'R': "R'"}); HYPS_DQ_ = sub(HYPS_DQ, dict(DNMAP, R="R'"))
DROP_C2 = (('( %s ` I\' ) = %s' % (PF("R'"), CC('W', CC(S1('Y'), 'X"'))), (WRD('W', 'B'), WRD('X"', GIP))), (HCDR_, HEDR_))
TREE_DMC2 = (((PROG_DQ_, MEQ("E'", STM_CDR)), (LABS_DQ_, LAB("G'")), ((IDX4, DIST4), TYPS_C2)),
             (("R' e. NN0", BNDS_D), (FAM_DQ_, HYPS_DQ_), (HTF("( N ` R' )", 'C"'), DROP_C2)))
POST_C2 = UP(PF("R'"), "I'", 'X"')
CONCL_DMC2 = TRI(CLN("A'", NF('0'), PF('0')), CLN("G'", SS, POST_C2), '( ( R\' x. %s ) + ( ( # ` W ) + 2 ) )' % TD4)
# the whole
TREE_DMC = (TREE_DMC1, TREE_DMC2)
CONCL_DMC = TRI(CLN('P0', 'O', 'D'), CLN("G'", SS, POST_C2),
                '( ( ( U" + U0 ) + ( ( R x. ( U\' + 2 ) ) + ( R\' x. %s ) ) ) + ( ( # ` W ) + 5 ) )' % TD4)
# divmod: dropNum J at G' -> G" (F" C', the divisor word W' e. Word B')
STM_DRJ = POP('J', 'F"', BRANCH("C'", GT("G'"), GT('G"')))
HCDR_J = "A. r e. %s A. z e. B' ( C' ` %s ) = 1o" % (SS, NV('F"', 'r', 'z'))
HEDR_J = "A. r e. %s -. ( C' ` %s ) = 1o" % (SS, NV('F"', 'r', 'Y'))
DROP_J = ((MEQ("G'", STM_DRJ), (LAB('G"'), RTY('F"', 'J'))), (("B' C_ %s" % GJ, 'Y e. %s' % GJ), (WRD("W'", "B'"), WRD("X'", GJ))),
          ('( %s ` J ) = %s' % (PF("R'"), CC("W'", CC(S1('Y'), "X'"))), (HCDR_J, HEDR_J)))
TREE_DM = (TREE_DMC, DROP_J)
POST_DM = UP(POST_C2, 'J', "X'")
CONCL_DM = TRI(CLN('P0', 'O', 'D'), CLN('G"', SS, POST_DM),
               '( ( ( U" + U0 ) + ( ( R x. ( U\' + 2 ) ) + ( R\' x. %s ) ) ) + ( ( ( # ` W ) + ( # ` W\' ) ) + 6 ) )' % TD4)
# divFrag / modFrag: dropNum K resp. I at G" -> D' (F0 C', the word W" e. Word B")
def DROP_X(k):
    stm = POP(k, 'F0', BRANCH("C'", GT('G"'), GT("D'")))
    hc = "A. r e. %s A. z e. B\" ( C' ` %s ) = 1o" % (SS, NV('F0', 'r', 'z'))
    he = "A. r e. %s -. ( C' ` %s ) = 1o" % (SS, NV('F0', 'r', 'Y'))
    return ((MEQ('G"', stm), (LAB("D'"), RTY('F0', k))), (('B" C_ %s' % GX(k), 'Y e. %s' % GX(k)), (WRD('W"', 'B"'), WRD('X0', GX(k)))),
            ('( %s ` %s ) = %s' % (PF("R'"), k, CC('W"', CC(S1('Y'), 'X0'))), (hc, he)))
TREE_DIV = (TREE_DM, DROP_X('K'))
TREE_MOD = (TREE_DM, DROP_X('I'))
BND_DX = '( ( ( U" + U0 ) + ( ( R x. ( U\' + 2 ) ) + ( R\' x. %s ) ) ) + ( ( ( # ` W ) + ( ( # ` W\' ) + ( # ` W" ) ) ) + 7 ) )' % TD4
CONCL_DIV = TRI(CLN('P0', 'O', 'D'), CLN("D'", SS, UP(POST_DM, 'K', 'X0')), BND_DX)
CONCL_MOD = TRI(CLN('P0', 'O', 'D'), CLN("D'", SS, UP(POST_DM, 'I', 'X0')), BND_DX)

STATEMENTS += [('tm2fdmc1', TREE_DMC1, CONCL_DMC1), ('tm2fdmc2', TREE_DMC2, CONCL_DMC2), ('tm2fdmc', TREE_DMC, CONCL_DMC),
               ('tm2fdm', TREE_DM, CONCL_DM), ('tm2fdiv', TREE_DIV, CONCL_DIV), ('tm2fmod', TREE_MOD, CONCL_MOD)]

# ---- tm2stkup8: eight updates at four distinct indices collapse to four
TREE_UP8 = ((('T e. V', STKD('D')), (('K =/= J', 'K =/= I', "K =/= I'"), ('J =/= I', "J =/= I'", "I =/= I'"))),
            (('K e. %s' % DG, (WRD('Y', GK), WRD("Y'", GK))), ('J e. %s' % DG, (WRD('Z', GJ), WRD("Z'", GJ)))),
            (('I e. %s' % DG, (WRD('N', GI), WRD("N'", GI))), ("I' e. %s" % DG, (WRD('O', GIP), WRD("O'", GIP)))))
UP4_ = lambda D, y, z, n, o: UP(UP3(D, 'K', y, 'J', z, 'I', n), "I'", o)
CONCL_UP8 = '%s = %s' % (UP4_(UP4_('D', 'Y', 'Z', 'N', 'O'), "Y'", "Z'", "N'", "O'"), UP4_('D', "Y'", "Z'", "N'", "O'"))
STATEMENTS.append(('tm2stkup8', TREE_UP8, CONCL_UP8))


def up8g(w, ph, D, a, b, c_, d, vals, tv, dd, ne, idx, wds):
    """tm2stkup8 at ( K , J , I , I' ) := ( a , b , c_ , d ):
    UP4( UP4( D ; a Y ; b Z ; c_ N ; d O ) ; a Y' ; b Z' ; c_ N' ; d O' ) = UP4( D ; a Y' ; ... );
    vals = (Y, Yp, Z, Zp, Nw, Npw, O, Op); ne = dict of the six inequality steps keyed 'ab','ac','ad','bc','bd','cd';
    idx = (aa, bb, cc, dd_) the index memberships; wds = the eight word steps in vals' order"""
    Y, Yp, Z, Zp, Nw, Npw, O, Op = vals
    aa, bb, cc, ddx = idx
    yw, ypw, zw, zpw, nw, npw, ow, opw = wds
    GA_, GB_, GC_, GD_ = GX(a), GX(b), GX(c_), GX(d)
    p1 = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T)),
              w.s([w.s([ne['ab'], ne['ac'], ne['ad']], '3jca', '( %s -> ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) )' % (ph, a, b, a, c_, a, d)),
                   w.s([ne['bc'], ne['bd'], ne['cd']], '3jca', '( %s -> ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) )' % (ph, b, c_, b, d, c_, d))], 'jca',
                  '( %s -> ( ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) /\\ ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) ) )' % (ph, a, b, a, c_, a, d, b, c_, b, d, c_, d))], 'jca',
             '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ ( ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) /\\ ( %s =/= %s /\\ %s =/= %s /\\ %s =/= %s ) ) ) )'
             % (ph, D, STK_T, a, b, a, c_, a, d, b, c_, b, d, c_, d))
    def pair(kk, G_, u, v, uw, vw):
        return w.s([kk, w.s([uw, vw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, u, G_, v, G_))], 'jca',
                   '( %s -> ( %s e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, kk_name(kk), DG, u, G_, v, G_))
    def kk_name(st):
        return concl(w, ph, st).split(' e. ')[0]
    pa = pair(aa, GA_, Y, Yp, yw, ypw); pb = pair(bb, GB_, Z, Zp, zw, zpw)
    pc = pair(cc, GC_, Nw, Npw, nw, npw); pd = pair(ddx, GD_, O, Op, ow, opw)
    p2 = w.s([pa, pb], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, concl(w, ph, pa), concl(w, ph, pb)))
    p3 = w.s([pc, pd], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, concl(w, ph, pc), concl(w, ph, pd)))
    LHS = UP(UP3(UP(UP3(D, a, Y, b, Z, c_, Nw), d, O), a, Yp, b, Zp, c_, Npw), d, Op)
    RHS = UP(UP3(D, a, Yp, b, Zp, c_, Npw), d, Op)
    return w.s([p1, p2, p3, w.inst('tm2stkup8')], 'syl3anc', '( %s -> %s = %s )' % (ph, LHS, RHS)), RHS

# ============================================================ the budget arithmetic of the _le_B forms
# (alphabet-independent cores of Canon.lean's mulC_le_B and canonDivBound_B / divBound_B; T7 glues)
QUAD_M = '( ( M x. M ) + ( ( 4 x. M ) + 4 ) )'
ST_QUAD = '( ( M e. NN0 /\\ C e. NN0 /\\ C <_ ; 6 4 ) -> ( C x. %s ) <_ ( TMB ` M ) )' % QUAD_M
MULB_LHS = '( ( B x. ( ( ( 4 x. A ) + ( 6 x. B ) ) + ; 1 4 ) ) + ( ( ( 4 x. A ) + ( 7 x. B ) ) + 9 ) )'
ST_MULB = '( ( ( A e. NN0 /\\ B e. NN0 /\\ M e. NN0 ) /\\ ( A <_ M /\\ B <_ M ) ) -> %s <_ ( TMB ` M ) )' % MULB_LHS
DIVB_LHS = '( ( A x. ( ( ; 2 3 x. ( A + D ) ) + ; 6 0 ) ) + ( ( C x. ( A + D ) ) + ; 3 7 ) )'
ST_DIVB = ('( ( ( A e. NN0 /\\ D e. NN0 /\\ M e. NN0 ) /\\ ( C e. NN0 /\\ C <_ ; 1 4 ) /\\ ( A <_ M /\\ D <_ M ) ) -> %s <_ ( TMB ` M ) )'
           % DIVB_LHS)
NSTMTS += [('tmdquad', ST_QUAD), ('tmdmulb', ST_MULB), ('tmddivb', ST_DIVB)]
