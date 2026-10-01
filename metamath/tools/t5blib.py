"""Sortie T5b: the phase loops `bitlen` and `pow2` of TM/Prims.lean.

The frozen statements of T5b-blueprint.md as antecedent trees (nested tuples
of arity 2 or 3, the leaves wff texts, as tools/t5lib.py's `Ctx` reads them)
with their conclusions, and helpers on top of tools/t5lib.py.

Notation: S = ( 2nd ` T ), L = ( 2nd ` ( 1st ` T ) ), DG = dom ( 1st ` ( 1st ` T ) ),
GK = ( ( 1st ` ( 1st ` T ) ) ` K ), C( A , N , D ) = ( { ( inl ` A ) } X. ( N X. { D } ) ),
UPD( D , K , X ) = Lean's Function.update, NV( F ; r , z ) = ( F ` <. r , ( inl ` z ) >. ),
GT( X ) = <. 5 , ( S X. { X } ) >., CONST( Z ) = ( S X. { Z } ).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t5lib import *
import lin
lin.FASTPATH = True
from t5_d_scl import DISJ_INC as _DISJ_INC, DISJ_PRD as _DISJ_PRD
from t5_e_inc import tree as _incr_tree
from t5_c_iz import TREE as _IZ_TREE

GK, GJ, GI, GIP = GX('K'), GX('J'), GX('I'), GX("I'")
HDL = lambda k: '( %s ^m ( %s X. ( %s |_| 1o ) ) )' % (SS, SS, GX(k))
CTY = lambda c: '%s e. ( 2o ^m %s )' % (c, SS)
LTY = lambda f: '%s e. ( %s ^m %s )' % (f, SS, SS)
PTY = lambda p, k: '%s e. ( %s ^m %s )' % (p, GX(k), SS)
RTY = lambda f, k: '%s e. %s' % (f, HDL(k))
LAB = lambda a: '%s e. %s' % (a, LL)
STKD = lambda d: '%s e. %s' % (d, STK_T)
STMT = lambda q: '%s e. %s' % (q, STMT_T)
CONST = lambda z: CONSTF('T', z)
S1 = lambda z: '<" %s ">' % z
CC = lambda a, b: '( %s ++ %s )' % (a, b)
WRD = lambda x, a: '%s e. Word %s' % (x, a)
FV = lambda f, x: '( %s ` %s )' % (f, x)
P1 = lambda x: '( %s + 1 )' % x
MEQ = lambda a, stm: '( M ` %s ) = %s' % (a, stm)
NV = NVF
SSS = lambda n: '%s C_ %s' % (n, SS)
TRI = lambda C, D, n: HR(C, 'T', 'M', D, n)


def UP3(D, k1, x1, k2, x2, k3, x3):
    return UP(UP(UP(D, k1, x1), k2, x2), k3, x3)


def ren(tree, m):
    """rename class variables (tokens) throughout a tree of wff texts"""
    if isinstance(tree, str):
        return sub(tree, m)
    return tuple(ren(t, m) for t in tree)


def flat(tree):
    if isinstance(tree, str):
        return [tree]
    out = []
    for t in tree:
        out.extend(flat(t))
    return out


# ------------------------------------------------------------ interfaces

def HT(N, C='C0'):
    """the loop test succeeds on N"""
    return 'A. m e. %s ( %s ` m ) = 1o' % (N, C)


def HTF(N, C='C0'):
    """the loop test fails on N"""
    return 'A. m e. %s -. ( %s ` m ) = 1o' % (N, C)


def HSCAN(N, Z, Zp, O, F='F', C='C', P='P', L='L'):
    """blScan on the bit Z: not the terminator, Zp is pushed, the load lands in O"""
    nv = NV(F, 'm', Z)
    return ('A. m e. %s ( -. ( %s ` %s ) = 1o /\\ ( %s ` %s ) = %s /\\ ( %s ` %s ) e. %s )'
            % (N, C, nv, P, nv, Zp, L, nv, O))


def HEND(N, Y, O, F='F', C='C', L='L'):
    """blScan on the terminator Y: the branch is taken, the load lands in O"""
    nv = NV(F, 'm', Y)
    return 'A. m e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) e. %s )' % (N, C, nv, L, nv, O)


def HLOAD(N, O, L="L'"):
    return 'A. m e. %s ( %s ` m ) e. %s' % (N, L, O)


# ------------------------------------------------------------ the one-step lemmas

STM_BLS1 = POP('K', 'F', BRANCH('C', 'Q', PUSH('J', 'P', LOAD('L', GT('E')))))
D2_BLS1 = UP(UP('D', 'K', 'X'), 'J', CC(S1("Z'"), '( D ` J )'))
ZX = CC(S1('Z'), 'X')
YX = CC(S1('Y'), 'X')

TREE_BLS1 = (((PHM, MEQ('A', STM_BLS1)),
              ((LAB('A'), LAB('E')), ('K e. %s' % DG, 'J e. %s' % DG), 'K =/= J'),
              ((RTY('F', 'K'), CTY('C')), (PTY('P', 'J'), LTY('L')), STMT('Q'))),
             ((STKD('D'), '( D ` K ) = %s' % ZX, (('Z e. %s' % GK, "Z' e. %s" % GJ), WRD('X', GK))),
              ((SSS('N'), SSS("N'")), HSCAN('N', 'Z', "Z'", "N'"))))
CONCL_BLS1 = TRI(CLN('A', 'N', 'D'), CLN('E', "N'", D2_BLS1), '1')

STM_BLS0 = POP('K', 'F', BRANCH('C', LOAD('L', GT('E')), 'Q'))
TREE_BLS0 = (((PHM, MEQ('A', STM_BLS0)),
              (LAB('A'), LAB('E'), 'K e. %s' % DG),
              ((RTY('F', 'K'), CTY('C')), (LTY('L'), STMT('Q')))),
             ((STKD('D'), '( D ` K ) = %s' % YX, ('Y e. %s' % GK, WRD('X', GK))),
              ((SSS('N'), SSS("N'")), HEND('N', 'Y', "N'"))))
CONCL_BLS0 = TRI(CLN('A', 'N', 'D'), CLN('E', "N'", UP('D', 'K', 'X')), '1')

# ------------------------------------------------------------ the bitlen iteration, continuations abstract

STM_T = BRANCH('C0', GT("A'"), 'Q')
STM_S = POP('K', 'F', BRANCH('C', "Q'", PUSH('J', 'P', LOAD('L', GT('A"')))))
STM_DA = BRANCH("C'", 'Q"', GT("E'"))
STM_FL = BRANCH('C"', GT('E"'), GT('E0'))
HDA = lambda O: HTF(O, "C'")
HDAT = lambda O: HT(O, "C'")
HFT = lambda O: HT(O, 'C"')
HFF = lambda O: HTF(O, 'C"')
DISJ_BLB = ('( ( %s /\\ %s ) \\/ ( %s /\\ %s ) )'
            % (HFT('O'), TRI(CLN('E"', 'O', D2_BLS1), CLN('A', "N'", "D'"), 'R'),
               HFF('O'), TRI(CLN('E0', 'O', D2_BLS1), CLN('A', "N'", "D'"), 'R')))
TREE_BLB = ((((PHM, MEQ('A', STM_T), MEQ("A'", STM_S)), (MEQ('A"', STM_DA), MEQ("E'", STM_FL))),
             (((LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E"'), LAB('E0'))),
              ('K e. %s' % DG, 'J e. %s' % DG, 'K =/= J'),
              (((CTY('C0'), CTY('C')), (CTY("C'"), CTY('C"'))), (RTY('F', 'K'), PTY('P', 'J'), LTY('L')),
               (STMT('Q'), STMT("Q'"), STMT('Q"'))))),
            ((STKD('D'), '( D ` K ) = %s' % ZX, (('Z e. %s' % GK, "Z' e. %s" % GJ), WRD('X', GK))),
             ((SSS('N'), SSS('O'), SSS("N'")), (HT('N'), HSCAN('N', 'Z', "Z'", 'O'), HDA('O')),
              (DISJ_BLB, 'R e. NN0'))))
CONCL_BLB = TRI(CLN('A', 'N', 'D'), CLN('A', "N'", "D'"), '( R + 4 )')

# ------------------------------------------------------------ the final iteration and the exit

STM_TE = BRANCH('C0', GT("A'"), GT('E'))
STM_SE = POP('K', 'F', BRANCH('C', LOAD('L', GT('A"')), "Q'"))
STM_DAE = BRANCH("C'", GT('E0'), 'Q"')
STM_SK = LOAD("L'", GT('A'))
TREE_BLE = ((((PHM, MEQ('A', STM_TE), MEQ("A'", STM_SE)), (MEQ('A"', STM_DAE), MEQ('E0', STM_SK))),
             (((LAB('A'), LAB("A'"), LAB('A"')), (LAB('E0'), LAB('E'))), 'K e. %s' % DG,
              (((CTY('C0'), CTY('C')), CTY("C'")), (RTY('F', 'K'), LTY('L'), LTY("L'")),
               (STMT("Q'"), STMT('Q"'))))),
            ((STKD('D'), '( D ` K ) = %s' % YX, ('Y e. %s' % GK, WRD('X', GK))),
             ((SSS('N'), SSS('O'), SSS("N'")),
              ((HT('N'), HEND('N', 'Y', 'O')), (HDAT('O'), HLOAD('O', "N'"), HTF("N'"))))))
CONCL_BLE = TRI(CLN('A', 'N', 'D'), CLN('E', "N'", UP('D', 'K', 'X')), '5')

# ------------------------------------------------------------ the bitlen iteration with incr / skip

# tm2fincr instantiated inside the iteration: its labels A , A' , A" , E become
# A0 , H0 , H' , A ; its stacks K , J become I , I' ; its functions and letters are
# renamed as below (the run alphabet B , the image alphabet B' , the letter map G ,
# the terminator Y and the run W keep their names)
INCR_MAP = {'A': 'A0', "A'": 'H0', 'A"': "H'", 'E': 'A', 'K': 'I', 'J': "I'",
            'F': "F'", 'C': 'D0', 'P': "P'", "C'": "D'", "P'": 'P"', 'P"': 'P0',
            'F"': 'F"', 'C0': 'D"', 'O': 'O', 'Z': 'Z"', "Z'": "Y'", 'Z"': 'Y"',
            'X': "X'", 'N': 'N1', 'Z0': 'Z0'}
INCR_TREE = ren(_incr_tree(False), INCR_MAP)         # tm2fincr's antecedent, renamed, at D
INCR_ST = ren(_incr_tree(False)[0], INCR_MAP)        # the three code equations (at A0 , H0 , H')
STM_IP = INCR_ST[0][1].split(' = ', 1)[1]
STM_IL = INCR_ST[0][2].split(' = ', 1)[1]
STM_IM = INCR_ST[1].split(' = ', 1)[1]
DISJ_INC1 = sub(_DISJ_INC, INCR_MAP)
HC1 = sub(flat(_incr_tree(False)[2][1])[2], INCR_MAP)   # A. r e. N1 A. z e. B ( ... )
HC2 = sub(flat(_incr_tree(False)[2][1])[3], INCR_MAP)
HE2 = sub(flat(_incr_tree(False)[2][1])[4], INCR_MAP)
STM_FLK = BRANCH('C"', GT('A0'), GT('E0'))
STM_SK2 = LOAD("L'", GT('A'))
GW = '( G o. W )'
INCDJ = ('( ( O\' C_ N1 /\\ N1 C_ N\' ) /\\ ( W1 = %s /\\ ( ( 2 x. ( # ` W ) ) + 3 ) <_ T\' ) /\\ ( %s /\\ W0 = %s ) )'
         % (CC('W', CC(S1('Z"'), "X'")), DISJ_INC1, CC(GW, 'Z0')))
SKPDJ = '( %s /\\ %s /\\ W0 = W1 )' % (HFF("O'"), HLOAD("O'", "N'"))
DISJ_BLK = '( %s \\/ %s )' % (SKPDJ, INCDJ)
TREE_BLK = (
    ((PHM, (MEQ('A', STM_T), MEQ("A'", STM_S)), (MEQ('A"', STM_DA), MEQ("E'", STM_FLK))),
     ((MEQ('E0', STM_SK2), MEQ('A0', STM_IP)), (MEQ('H0', STM_IL), MEQ("H'", STM_IM)))),
    ((((LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E0')), (LAB('A0'), LAB('H0'), LAB("H'"))),
      (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, "I' e. %s" % DG)),
      (('K =/= J', 'K =/= I'), ('J =/= I', "I =/= I'"))),
     ((((CTY('C0'), CTY('C')), (CTY("C'"), CTY('C"'))), ((CTY('D0'), CTY("D'")), CTY('D"'))),
      ((RTY('F', 'K'), RTY("F'", 'I'), RTY('F"', "I'")),
       (PTY('P', 'J'), PTY("P'", "I'"), (PTY('P"', 'I'), PTY('P0', 'I'), PTY('O', 'I'))),
       (LTY('L'), LTY("L'"))),
      (STMT('Q'), STMT("Q'"), STMT('Q"')))),
    (((('B C_ %s' % GI, "B' C_ %s" % GI, "B' C_ %s" % GIP), ("G : B --> B'", 'Y e. %s' % GIP),
       (('Z" e. %s' % GI, "Y' e. %s" % GI, 'Y" e. %s' % GI), (WRD('W', 'B'), WRD("X'", GI)))),
      ((STKD('D'), '( D ` K ) = %s' % ZX, '( D ` I ) = W1'), (('Z e. %s' % GK, "Z' e. %s" % GJ), WRD('X', GK)))),
     (((SSS('N'), SSS("O'")), (SSS("N'"), SSS('N1'))),
      ((HT('N'), HSCAN('N', 'Z', "Z'", "O'")), (HDA("O'"), HFT('N1'))),
      ((HC1, HC2), HE2)),
     (DISJ_BLK, ("T' e. NN0", "1 <_ T'"))))
CONCL_BLK = TRI(CLN('A', 'N', 'D'), CLN('A', "N'", UP(D2_BLS1, 'I', 'W0')), "( T' + 4 )")

# ------------------------------------------------------------ the bitlen prologue

ST_P1 = PUSH('J', CONST('Y'), GT("A'"))
ST_PMV = POP('K', 'F', BRANCH('C', PUSH('J', 'P', GT("A'")), GT('A"')))
ST_P3 = PUSH('K', CONST('Y'), GT("E'"))
ST_P4 = PUSH('I', CONST('Y'), GT('E"'))
ST_P5 = LOAD('L', GT('E'))
HCMVN = lambda N, F='F', C='C', P='P': ('A. r e. %s A. z e. B ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ %s e. %s )'
                                        % (N, C, NV(F, 'r', 'z'), P, NV(F, 'r', 'z'), NV(F, 'r', 'z'), N))
HEMVN = lambda N, F='F', C='C': ('A. r e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s )'
                                 % (N, C, NV(F, 'r', 'Y'), NV(F, 'r', 'Y'), N))
HLD = lambda N, O, L='L': 'A. r e. %s ( %s ` r ) e. %s' % (N, L, O)
WYX = CC('W', YX)
RWYDJ = CC('( reverse ` W )', CC(S1('Y'), '( D ` J )'))
YDI = CC(S1('Y'), '( D ` I )')
TREE_BLP = (((PHM, MEQ('A', ST_P1), MEQ("A'", ST_PMV)), (MEQ('A"', ST_P3), MEQ("E'", ST_P4), MEQ('E"', ST_P5))),
            (((LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E"'), LAB('E'))),
             ('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG), ('K =/= J', 'K =/= I', 'J =/= I')),
            (((RTY('F', 'K'), CTY('C'), PTY('P', 'J')), LTY('L')),
             (('B C_ %s' % GK, 'B C_ %s' % GJ), ('Y e. %s' % GK, 'Y e. %s' % GJ, 'Y e. %s' % GI),
              (WRD('W', 'B'), WRD('X', GK), STKD('D'))),
             ('( D ` K ) = %s' % WYX, (SSS('N'), SSS("N'")), ((HCMVN('N'), HEMVN('N')), HLD('N', "N'")))))
CONCL_BLP = TRI(CLN('A', 'N', 'D'), CLN('E', "N'", UP3('D', 'J', RWYDJ, 'K', YX, 'I', YDI)), '( ( # ` W ) + 5 )')

# ------------------------------------------------------------ the bitlen loop (families)

XF = lambda i: '( X ` %s )' % i
UF = lambda i: '( U ` %s )' % i
HF = lambda i: '( H ` %s )' % i
WF = lambda i: '( W ` %s )' % i
NF = lambda i: '( N ` %s )' % i
OF = lambda i: "( O' ` %s )" % i
WPF = lambda i: "( W' ` %s )" % i
ZF = lambda i: '( Z ` %s )' % i
XPF = lambda i: "( X' ` %s )" % i
Z0F = lambda i: '( Z0 ` %s )' % i
DP = lambda i: UP3('D', 'K', XF(i), 'J', HF(i), 'I', WF(i))

STM_TQ = BRANCH('C0', GT("A'"), GT('E'))
STM_SQ = POP('K', 'F', BRANCH('C', LOAD('L0', GT('A"')), PUSH('J', 'P', LOAD('L', GT('A"')))))
STM_DAQ = BRANCH("C'", GT('E"'), GT("E'"))
STM_SK1 = LOAD("L'", GT('A'))


def DISJ_INC_AT(i):
    return sub(DISJ_INC1, {'Z"': ZF(i), "X'": XPF(i), 'Z0': Z0F(i)})


def DISJ_Q(i):
    i1 = P1(i)
    skp = '( %s /\\ %s /\\ %s = %s )' % (HFF(OF(i)), HLOAD(OF(i), NF(i1)), WF(i1), WF(i))
    inc = ('( ( %s C_ N1 /\\ N1 C_ %s ) /\\ ( %s = %s /\\ ( ( 2 x. ( # ` %s ) ) + 3 ) <_ T\' ) /\\ ( %s /\\ %s = %s ) )'
           % (OF(i), NF(i1), WF(i), CC(WPF(i), CC(S1(ZF(i)), XPF(i))), WPF(i), DISJ_INC_AT(i), WF(i1),
              CC('( G o. %s )' % WPF(i), Z0F(i))))
    return '( %s \\/ %s )' % (skp, inc)


def HYP_Q_TREE(i):
    i1 = P1(i)
    return ((('%s = %s' % (XF(i), CC(S1(UF(i)), XF(i1))), '%s = %s' % (HF(i1), CC(S1(UF(i)), HF(i)))),
             ('%s e. B0' % UF(i), (WRD(WPF(i), 'B'), '%s e. %s' % (ZF(i), GI), WRD(XPF(i), GI)))),
            (HT(NF(i)), HSCAN(NF(i), UF(i), UF(i), OF(i)), HDA(OF(i))),
            DISJ_Q(i))


def HYP_Q(i):
    return cj(HYP_Q_TREE(i))


HYPS_Q = 'A. i e. ( 0 ..^ R ) %s' % HYP_Q('i')
FAMB_Q = lambda i: ((WRD(XF(i), GK), WRD(HF(i), GJ), WRD(WF(i), GI)), (SSS(NF(i)), SSS(OF(i))))
FAM_Q = 'A. i e. ( 0 ... R ) %s' % cj(FAMB_Q('i'))
FAMN_Q = SSS(NF('( R + 1 )'))
INIT_Q_TREE = ('%s = ( D ` K )' % XF('0'), '%s = ( D ` J )' % HF('0'), '%s = ( D ` I )' % WF('0'))
INIT_Q = cj(INIT_Q_TREE)
FIN_Q_TREE = (('%s = %s' % (XF('R'), CC(S1('Y'), 'X0')), WRD('X0', GK)),
              (HT(NF('R')), HEND(NF('R'), 'Y', OF('R'), L='L0'), HDAT(OF('R'))),
              (HLOAD(OF('R'), NF('( R + 1 )')), HTF(NF('( R + 1 )'))))
FIN_Q = cj(FIN_Q_TREE)
TREE_BLQ = (((PHM, (MEQ('A', STM_TQ), MEQ("A'", STM_SQ)), (MEQ('A"', STM_DAQ), MEQ("E'", STM_FLK))),
             ((MEQ('E"', STM_SK1), MEQ('E0', STM_SK2)), (MEQ('A0', STM_IP), MEQ('H0', STM_IL), MEQ("H'", STM_IM)))),
            (((((LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E"'), LAB('E0'))),
               ((LAB('A0'), LAB('H0'), LAB("H'")), LAB('E'))),
              (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, "I' e. %s" % DG)),
              (('K =/= J', 'K =/= I'), ('J =/= I', "I =/= I'"))),
             ((((CTY('C0'), CTY('C')), (CTY("C'"), CTY('C"'))), ((CTY('D0'), CTY("D'")), CTY('D"'))),
              ((RTY('F', 'K'), RTY("F'", 'I'), RTY('F"', "I'")),
               (PTY('P', 'J'), PTY("P'", "I'"), (PTY('P"', 'I'), PTY('P0', 'I'), PTY('O', 'I'))),
               ((LTY('L'), LTY('L0')), LTY("L'"))))),
            (((('B C_ %s' % GI, "B' C_ %s" % GI, "B' C_ %s" % GIP), ("G : B --> B'", ('Y e. %s' % GIP, 'Y e. %s' % GK)),
               (("Y' e. %s" % GI, 'Y" e. %s' % GI), ('B0 C_ %s' % GK, 'B0 C_ %s' % GJ))),
              ((STKD('D'), INIT_Q), ('R e. NN0', ("T' e. NN0", "1 <_ T'")))),
             ((SSS('N1'), HFT('N1')), ((HC1, HC2), HE2), (FAM_Q, FAMN_Q)),
             (HYPS_Q, FIN_Q)))
CONCL_BLQ = TRI(CLN('A', NF('0'), 'D'), CLN('E', NF('( R + 1 )'), UP3('D', 'K', 'X0', 'J', HF('R'), 'I', WF('R'))),
                "( ( R x. ( T' + 4 ) ) + 5 )")

# ------------------------------------------------------------ bitlen assembled

# the prologue renamed into the loop's names: its labels A A' A" E' E" E become
# R R' R" R0 Q A, its stacks K J become J K (the number is on J = x, the scan
# runs on K = s), its handlers F C P L become F0 O0 O' L", its alphabet B0, its
# words W0 X0, its class N0 and its exit class ( N ` 0 )
PRO_MAP = {'A': 'R', "A'": "R'", 'A"': 'R"', "E'": 'R0', 'E"': 'Q', 'E': 'A', 'K': 'J', 'J': 'K',
           'F': 'F0', 'C': 'O0', 'P': "O'", 'L': 'L"', 'B': 'B0', 'W': 'W0', 'X': 'X0', 'N': 'N0', "N'": NF('0')}
PRO_TREE = ren(TREE_BLP, PRO_MAP)
NW0 = '( # ` W0 )'
QMAP = {'R': NW0, 'X0': '( D ` K )'}
INIT_L = ('( %s = %s /\\ %s = %s /\\ %s = %s )'
          % (XF('0'), CC('( reverse ` W0 )', CC(S1('Y'), '( D ` K )')), HF('0'), CC(S1('Y'), 'X0'), WF('0'), YDI))
FIN_L = sub(FIN_Q, QMAP)
FIN_L2 = '( %s /\\ %s = ( D ` J ) )' % (FIN_L, HF(NW0))
TREE_BLL = ((PRO_TREE[0], TREE_BLQ[0]),
            (PRO_TREE[1], PRO_TREE[2], TREE_BLQ[1]),
            ((((TREE_BLQ[2][0][0], (STKD('D'), INIT_L)), (('B0 C_ %s' % GK, 'B0 C_ %s' % GJ), ("T' e. NN0", "1 <_ T'"))),
              TREE_BLQ[2][1]),
             (sub(HYPS_Q, QMAP), sub(FAM_Q, QMAP), sub(FAMN_Q, QMAP)), FIN_L2))
CONCL_BLL = TRI(CLN('R', 'N0', 'D'), CLN('E', NF('( %s + 1 )' % NW0), UP('D', 'I', WF(NW0))),
                "( ( %s + 5 ) + ( ( %s x. ( T' + 4 ) ) + 5 ) )" % (NW0, NW0))

# ------------------------------------------------------------ the pow2 iteration

PRD_MAP = {'A': "A'", "A'": 'A"', 'A"': 'A0', 'E': "E'", 'J': "I'", 'C0': 'D0', 'N': 'N1'}
PRD_TREE = ren(_incr_tree(True), PRD_MAP)
PRD_ST = PRD_TREE[0]
STM_PP = PRD_ST[0][1].split(' = ', 1)[1]      # push Y on I'          at A'
STM_PL = PRD_ST[0][2].split(' = ', 1)[1]      # predLoop              at A"
STM_PM = PRD_ST[1].split(' = ', 1)[1]         # moveNum I' -> K       at A0
DISJ_PRD1 = sub(_DISJ_PRD, PRD_MAP)
_prdh = flat(_incr_tree(True)[2][1])
HCP, HCMVP, HEMVP = [sub(x, PRD_MAP) for x in _prdh[2:5]]
IZ_MAP = {'A': 'E"', "A'": 'E0', 'A"': 'H0', "E'": "H'", 'E"': 'H"', 'E': 'A',
          'F': 'F0', "F'": "G'", 'C': "D'", 'P': 'P0', "P'": "O'", 'B': 'B"', 'W': "W'", 'X': 'X"',
          'N': 'N1', 'O': 'O0'}
IZ_TREE = ren(_IZ_TREE, IZ_MAP)
IZ_ST = IZ_TREE[0]
STM_ZP = IZ_ST[0][1].split(' = ', 1)[1]       # push Y on I           at E"
STM_ZM = IZ_ST[0][2].split(' = ', 1)[1]       # moveNum K -> I        at E0
STM_Z3 = IZ_ST[1][0].split(' = ', 1)[1]       # push Y on K           at H0
STM_Z4 = IZ_ST[1][1].split(' = ', 1)[1]       # load L                at H'
STM_ZS = IZ_ST[1][2].split(' = ', 1)[1]       # zeroScan I -> K       at H"
_izh = flat(_IZ_TREE[2])
HCMVZ, HEMVZ, HLDZ, HCZSZ, HEZSZ = [sub(x, IZ_MAP) for x in _izh[-5:]]
FOLD = lambda w: "{ q e. %s | ( S' ` q ) = ( O0 ` %s ) }" % (SS, w)
STM_PZ = PUSH('J', CONST('Z1'), GT('E"'))
Z1DJ = CC(S1('Z1'), '( D ` J )')
D2_P2 = UP(UP('D', 'K', 'X0'), 'J', Z1DJ)
WZX = CC('W', CC(S1('Z'), 'X'))
WPYX = CC("W'", CC(S1('Y'), 'X"'))
TREE_P2K = (((PHM, (MEQ('A', STM_T), MEQ("A'", STM_PP)), (MEQ('A"', STM_PL), MEQ('A0', STM_PM))),
             ((MEQ("E'", STM_PZ), MEQ('E"', STM_ZP)), (MEQ('E0', STM_ZM), MEQ('H0', STM_Z3)), (MEQ("H'", STM_Z4), MEQ('H"', STM_ZS)))),
            ((((LAB('A'), LAB("A'"), LAB('A"')), (LAB('A0'), LAB("E'"), LAB('E"')), (LAB('E0'), LAB('H0'), (LAB("H'"), LAB('H"')))),
              (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, "I' e. %s" % DG)),
              ('K =/= J', 'K =/= I', "K =/= I'")),
             (((CTY('C0'), (CTY('C'), CTY("C'"), CTY('C"'))), (CTY('D0'), CTY("D'"))),
              ((RTY('F', 'K'), RTY("F'", 'K'), RTY('F"', "I'")), (RTY('F0', 'K'), RTY("G'", 'I'))),
              (((PTY('P', "I'"), PTY('O', 'K')), (PTY("P'", 'K'), PTY('P"', 'K'))), (PTY('P0', 'I'), PTY("O'", 'K')), (LTY('L'), LTY("L'")))),
             STMT('Q')),
            (((('B C_ %s' % GK, "B' C_ %s" % GK, "B' C_ %s" % GIP), ('B" C_ %s' % GK, 'B" C_ %s' % GI), "G : B --> B'"),
              ((('Y e. %s' % GIP, 'Y e. %s' % GK, 'Y e. %s' % GI), 'Z1 e. %s' % GJ),
               ((('Z e. %s' % GK, "Z' e. %s" % GK), 'Z" e. %s' % GK), (WRD('W', 'B'), (WRD('X', GK), WRD("X'", GK))), (WRD("W'", 'B"'), WRD('X"', GK)))),
              (STKD('D'), '( D ` K ) = %s' % WZX, ('X0 = %s' % CC(GW, 'Z0'), 'X0 = %s' % WPYX))),
             (((SSS('N'), 'N C_ N1', SSS('N1')), SSS("N'")),
              ((HT('N1'), HCP, (HCMVP, HEMVP)), (HCMVZ, HEMVZ), (HLDZ, (HCZSZ, HEZSZ))),
              (DISJ_PRD1, ("%s C_ N'" % FOLD("W'"), "( ( ( 2 x. ( # ` W ) ) + 3 ) + ( ( 2 x. ( # ` W' ) ) + 5 ) ) <_ T'"))),
             "T' e. NN0"))
CONCL_P2K = TRI(CLN('A', 'N', 'D'), CLN('A', "N'", D2_P2), "( T' + 2 )")

# ------------------------------------------------------------ the pow2 loop, exit and drop

ZPF = lambda i: "( Z' ` %s )" % i
UPF = lambda i: '( U ` %s )' % i
DP2 = lambda i: UP(UP('D', 'K', XF(i)), 'J', HF(i))
STM_DR = POP('K', 'G"', BRANCH('D"', GT('E'), GT('E1')))
HCDR = 'A. r e. %s A. z e. B" ( D" ` %s ) = 1o' % (SS, NV('G"', 'r', 'z'))
HEDR = 'A. r e. %s -. ( D" ` %s ) = 1o' % (SS, NV('G"', 'r', 'Y'))


def DISJ_P(i):
    return sub(DISJ_PRD1, {'Z': ZF(i), "Z'": ZPF(i), 'X': XPF(i), "X'": UPF(i), 'Z0': Z0F(i)})


def HYP_P_TREE(i):
    i1 = P1(i)
    return ((('%s = %s' % (XF(i), CC(WF(i), CC(S1(ZF(i)), XPF(i)))), '%s = %s' % (XF(i1), CC('( G o. %s )' % WF(i), Z0F(i))),
              '%s = %s' % (XF(i1), CC(WPF(i1), CC(S1('Y'), 'X"')))),
             ('%s = %s' % (HF(i1), CC(S1('Z1'), HF(i))), ('%s C_ N1' % NF(i), '%s C_ %s' % (FOLD(WPF(i1)), NF(i1))))),
            ((WRD(WF(i), 'B'), ('%s e. %s' % (ZF(i), GK), '%s e. %s' % (ZPF(i), GK)), (WRD(XPF(i), GK), WRD(UPF(i), GK))),
             "( ( ( 2 x. ( # ` %s ) ) + 3 ) + ( ( 2 x. ( # ` %s ) ) + 5 ) ) <_ T'" % (WF(i), WPF(i1))),
            DISJ_P(i))


def HYP_P(i):
    return cj(HYP_P_TREE(i))


HYPS_P = 'A. i e. ( 0 ..^ R ) %s' % HYP_P('i')
FAMB_P = lambda i: ((WRD(XF(i), GK), WRD(HF(i), GJ)), (SSS(NF(i)), WRD(WPF(i), 'B"')))
FAM_P = 'A. i e. ( 0 ... R ) %s' % cj(FAMB_P('i'))
INIT_P_TREE = ('%s = ( D ` K )' % XF('0'), '%s = ( D ` J )' % HF('0'))
INIT_P = cj(INIT_P_TREE)
FIN_P_TREE = ('%s = %s' % (XF('R'), CC(WPF('R'), CC(S1('Y'), 'X"'))), HTF(NF('R')))
FIN_P = cj(FIN_P_TREE)
TREE_P2Q = (((PHM, (MEQ('A', STM_TE), MEQ("A'", STM_PP)), (MEQ('A"', STM_PL), MEQ('A0', STM_PM))),
             ((MEQ("E'", STM_PZ), MEQ('E"', STM_ZP)), (MEQ('E0', STM_ZM), MEQ('H0', STM_Z3)), (MEQ("H'", STM_Z4), MEQ('H"', STM_ZS))),
             MEQ('E', STM_DR)),
            ((((LAB('A'), LAB("A'"), LAB('A"')), (LAB('A0'), LAB("E'"), LAB('E"')), (LAB('E0'), LAB('H0'), (LAB("H'"), LAB('H"')))),
              (LAB('E'), LAB('E1')),
              (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, "I' e. %s" % DG), ('K =/= J', 'K =/= I', "K =/= I'"))),
             (((CTY('C0'), (CTY('C'), CTY("C'"), CTY('C"'))), (CTY('D0'), CTY("D'"), CTY('D"'))),
              ((RTY('F', 'K'), RTY("F'", 'K'), RTY('F"', "I'")), (RTY('F0', 'K'), RTY("G'", 'I'), RTY('G"', 'K'))),
              (((PTY('P', "I'"), PTY('O', 'K')), (PTY("P'", 'K'), PTY('P"', 'K'))), (PTY('P0', 'I'), PTY("O'", 'K')), (LTY('L'), LTY("L'"))))),
            (((('B C_ %s' % GK, "B' C_ %s" % GK, "B' C_ %s" % GIP), ('B" C_ %s' % GK, 'B" C_ %s' % GI), "G : B --> B'"),
              ((('Y e. %s' % GIP, 'Y e. %s' % GK, 'Y e. %s' % GI), ('Z1 e. %s' % GJ, 'Z" e. %s' % GK)), (WRD('X"', GK), STKD('D'))),
              (INIT_P, ('R e. NN0', "T' e. NN0"))),
             (((SSS('N1'), HT('N1')), (HCP, (HCMVP, HEMVP)), ((HCMVZ, HEMVZ), (HLDZ, (HCZSZ, HEZSZ)))),
              ((HCDR, HEDR), FAM_P)),
             (HYPS_P, FIN_P)))
CONCL_P2Q = TRI(CLN('A', NF('0'), 'D'), CLN('E1', SS, UP(UP('D', 'J', HF('R')), 'K', 'X"')),
                "( ( ( R x. ( T' + 2 ) ) + 1 ) + ( ( # ` %s ) + 1 ) )" % WPF('R'))

# ------------------------------------------------------------ the pow2 prologue

ST_Q1 = PUSH('J', CONST('Y'), GT("A'"))
ST_Q2 = PUSH('J', CONST("Y'"), GT('A"'))
IZP_MAP = {'A': 'A"', "A'": "E'", 'A"': 'E"', "E'": 'E0', 'E"': 'H0'}
IZP_TREE = ren(_IZ_TREE, IZP_MAP)
IZP_ST = IZP_TREE[0]
_izp = flat(_IZ_TREE[2])
HCMVZP, HEMVZP, HLDZP, HCZSZP, HEZSZP = _izp[-5:]
YPYDJ = CC(S1("Y'"), CC(S1('Y'), '( D ` J )'))
TREE_P2P = (((PHM, (MEQ('A', ST_Q1), MEQ("A'", ST_Q2)), (IZP_ST[0][1], IZP_ST[0][2])), (IZP_ST[1][0], IZP_ST[1][1], IZP_ST[1][2])),
            ((((LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E"'), LAB('E0')), (LAB('H0'), LAB('E'))),
              ('K e. %s' % DG, 'J e. %s' % DG, 'I e. %s' % DG), ('K =/= J', 'K =/= I')),
             ((RTY('F', 'K'), RTY("F'", 'I'), CTY('C')), (PTY('P', 'I'), PTY("P'", 'K')), (LTY('L'), LTY("L'")))),
            (((('B C_ %s' % GK, 'B C_ %s' % GI), ('Y e. %s' % GK, 'Y e. %s' % GI, 'Y e. %s' % GJ),
               ("Y' e. %s" % GJ, WRD('W', 'B'), WRD('X', GK))),
              (STKD('D'), '( D ` K ) = %s' % WYX)),
             ((SSS('N'), HCMVZP, HEMVZP), (HLDZP, (HCZSZP, HEZSZP)))))
CONCL_P2P = TRI(CLN('A', 'N', 'D'), CLN('E', "{ q e. %s | ( S' ` q ) = ( O ` W ) }" % SS, UP('D', 'J', YPYDJ)),
                '( ( 2 x. ( # ` W ) ) + 7 )')

# ------------------------------------------------------------ pow2 assembled

# the prologue renamed into the loop's names: labels A A' A" E' E" E0 H0 E become
# Q Q' Q" Q0 R' R" R0 A; the isZero functions are the loop's (F0 G' D' P0 O' L L'),
# its alphabet B", its digit word ( W' ` 0 ), its rest X", its class N0, the fold O0
PRO2_MAP = {'A': 'Q', "A'": "Q'", 'A"': 'Q"', "E'": 'Q0', 'E"': "R'", 'E0': 'R"', 'H0': 'R0', 'E': 'A',
            'F': 'F0', "F'": "G'", 'C': "D'", 'P': 'P0', "P'": "O'", 'B': 'B"', 'W': WPF('0'), 'X': 'X"',
            'N': 'N0', 'O': 'O0'}
PRO2_TREE = ren(TREE_P2P, PRO2_MAP)
INIT_P2_TREE = (('%s = ( D ` K )' % XF('0'), '%s = %s' % (XF('0'), CC(WPF('0'), CC(S1('Y'), 'X"')))),
                ('%s = %s' % (HF('0'), YPYDJ), '%s C_ %s' % (FOLD(WPF('0')), NF('0'))))
INIT_P2 = cj(INIT_P2_TREE)
TREE_P2 = ((PRO2_TREE[0], TREE_P2Q[0]),
           ((PRO2_TREE[1][0], PRO2_TREE[1][1]), TREE_P2Q[1]),
           ((((TREE_P2Q[2][0][0], TREE_P2Q[2][0][1], ('Y e. %s' % GJ, "Y' e. %s" % GJ)), (INIT_P2, ('R e. NN0', "T' e. NN0"))),
             ((SSS('N0'), HCMVZ.replace('N1', 'N0'), HEMVZ.replace('N1', 'N0')),
              (HLDZ.replace('N1', 'N0'), (HCZSZ, HEZSZ)))),
            (TREE_P2Q[2][1], (HYPS_P, FIN_P))))
CONCL_P2 = TRI(CLN('Q', 'N0', 'D'), CLN('E1', SS, UP(UP('D', 'J', HF('R')), 'K', 'X"')),
               "( ( ( 2 x. ( # ` %s ) ) + 7 ) + ( ( ( R x. ( T' + 2 ) ) + 1 ) + ( ( # ` %s ) + 1 ) ) )" % (WPF('0'), WPF('R')))

STATEMENTS = [
    ('tm2fbls1', TREE_BLS1, CONCL_BLS1), ('tm2fbls0', TREE_BLS0, CONCL_BLS0),
    ('tm2fblb', TREE_BLB, CONCL_BLB), ('tm2fble', TREE_BLE, CONCL_BLE),
    ('tm2fblk', TREE_BLK, CONCL_BLK), ('tm2fblp', TREE_BLP, CONCL_BLP),
    ('tm2fblq', TREE_BLQ, CONCL_BLQ), ('tm2fbll', TREE_BLL, CONCL_BLL),
    ('tm2fp2k', TREE_P2K, CONCL_P2K), ('tm2fp2p', TREE_P2P, CONCL_P2P),
    ('tm2fp2q', TREE_P2Q, CONCL_P2Q), ('tm2fp2', TREE_P2, CONCL_P2)]


def statement(tree, concl):
    return '( %s -> %s )' % (cj(tree), concl)


# ------------------------------------------------------------ helpers for the loop assemblies

def inst_v(w, ph, st, body_v, v, X, xcl):
    """( ph -> body(X) ) from st : ( ph -> A. v e. A body(v) ), xcl : ( ph -> X e. A )"""
    cg, new = W.wcongr(w, body_v, {v: X}, '%s = %s' % (v, X), {v: w.s([], 'id', '( %s = %s -> %s = %s )' % (v, X, v, X))})
    return w.s([cg, st, xcl], 'rspcdva', '( %s -> %s )' % (ph, new)), new


def ifval(w, ph, IF, body_j, X, xcl, CLX, clex):
    """( ph -> ( IF ` X ) = CLX ) for IF = ( j e. NN0 |-> body_j ), body_j at j := X being CLX,
    clex : ( ph -> CLX e. _V )"""
    aq = '( %s /\\ j = %s )' % (ph, X)
    lj = w.s([], 'simpr', '( %s -> j = %s )' % (aq, X))
    st, res = W.congr(w, body_j, {'j': X}, aq, {'j': lj})
    assert res == CLX, (res, CLX)
    eqi = w.s([], 'eqid', '%s = %s' % (IF, IF))
    return w.s([st, eqi, xcl, clex], 'fvmptd2', '( %s -> ( %s ` %s ) = %s )' % (ph, IF, X, CLX))


def clnex(w, ph, A, N, D):
    """( ph -> C( A , N , D ) e. _V )"""
    a = w.s([], 'snex', '{ ( inl ` %s ) } e. _V' % A)
    b = w.s([], 'fvex', '%s e. _V' % N) if N.startswith('( ') and N.endswith(' )') and ' ` ' in N else None
    if b is None:
        b = w.s([], {'( 2nd ` T )': 'fvex'}.get(N, 'fvex'), '%s e. _V' % N)
    c_ = w.s([], 'snex', '{ %s } e. _V' % D)
    d = w.s([b, c_], 'xpex', '( %s X. { %s } ) e. _V' % (N, D))
    e = w.s([a, d], 'xpex', '%s e. _V' % CLN(A, N, D))
    return w.s([e], 'a1i', '( %s -> %s e. _V )' % (ph, CLN(A, N, D)))


def up6(w, ph, D, Y, Yp, Z, Zp, Nw, Npw, tv, dd, nkj, nki, nji, kk, jj, ii, yw, ypw, zw, zpw, nw, npw):
    """( ph -> UPD3( UPD3( D ; K , Y ; J , Z ; I , Nw ) ; K , Yp ; J , Zp ; I , Npw ) = UPD3( D ; K , Yp ; J , Zp ; I , Npw ) )"""
    a = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T)),
             w.s([nkj, nki, nji], '3jca', '( %s -> ( K =/= J /\\ K =/= I /\\ J =/= I ) )' % ph)], 'jca',
            '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ ( K =/= J /\\ K =/= I /\\ J =/= I ) ) )' % (ph, D, STK_T))
    b = w.s([kk, w.s([yw, ypw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Y, GK, Yp, GK))], 'jca',
            '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, DG, Y, GK, Yp, GK))
    c1 = w.s([jj, w.s([zw, zpw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Z, GJ, Zp, GJ))], 'jca',
             '( %s -> ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, DG, Z, GJ, Zp, GJ))
    c2 = w.s([ii, w.s([nw, npw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, Nw, GI, Npw, GI))], 'jca',
             '( %s -> ( I e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, DG, Nw, GI, Npw, GI))
    c_ = w.s([c1, c2], 'jca', '( %s -> ( ( J e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) /\\ ( I e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) ) )'
             % (ph, DG, Z, GJ, Zp, GJ, DG, Nw, GI, Npw, GI))
    LHS = UP3(UP3(D, 'K', Y, 'J', Z, 'I', Nw), 'K', Yp, 'J', Zp, 'I', Npw)
    RHS = UP3(D, 'K', Yp, 'J', Zp, 'I', Npw)
    return w.s([a, b, c_, w.inst('tm2stkup6')], 'syl3anc', '( %s -> %s = %s )' % (ph, LHS, RHS)), RHS


def up3cK(w, ph, D, X_, Xp, Hh, Ww, tv, dd, njk, nji, nik, kk, jj, ii, xw, xpw, hw, ww):
    """( ph -> UPD( UPD3( D ; K , X_ ; J , Hh ; I , Ww ) , K , Xp ) = UPD3( D ; K , Xp ; J , Hh ; I , Ww ) )
    --- tm2stkup3c with its ( I , K , J ) := ( K , J , I ); njk : J =/= K, nji : J =/= I, nik : I =/= K"""
    a = w.s([w.s([tv, dd], 'jca', '( %s -> ( T e. V /\\ %s e. %s ) )' % (ph, D, STK_T)),
             w.s([nji, njk, nik], '3jca', '( %s -> ( J =/= I /\\ J =/= K /\\ I =/= K ) )' % ph)], 'jca',
            '( %s -> ( ( T e. V /\\ %s e. %s ) /\\ ( J =/= I /\\ J =/= K /\\ I =/= K ) ) )' % (ph, D, STK_T))
    b = w.s([kk, w.s([xw, xpw], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (ph, X_, GK, Xp, GK))], 'jca',
            '( %s -> ( K e. %s /\\ ( %s e. Word %s /\\ %s e. Word %s ) ) )' % (ph, DG, X_, GK, Xp, GK))
    c_ = w.s([w.s([jj, hw], 'jca', '( %s -> ( J e. %s /\\ %s e. Word %s ) )' % (ph, DG, Hh, GJ)),
              w.s([ii, ww], 'jca', '( %s -> ( I e. %s /\\ %s e. Word %s ) )' % (ph, DG, Ww, GI))], 'jca',
             '( %s -> ( ( J e. %s /\\ %s e. Word %s ) /\\ ( I e. %s /\\ %s e. Word %s ) ) )' % (ph, DG, Hh, GJ, DG, Ww, GI))
    LHS = UP(UP3(D, 'K', X_, 'J', Hh, 'I', Ww), 'K', Xp)
    RHS = UP3(D, 'K', Xp, 'J', Hh, 'I', Ww)
    return w.s([a, b, c_, w.inst('tm2stkup3c')], 'syl3anc', '( %s -> %s = %s )' % (ph, LHS, RHS)), RHS
