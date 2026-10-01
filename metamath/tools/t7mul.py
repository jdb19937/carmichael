r"""Sortie T7: the statements of the multiplication at the machine (Lean
` mul_runs ` , ` mulC_runs ` , ` mulC_le_B ` ), on top of tools/t7lib.py.
Registered in ` STMTS7 ` (the frozen set of T7-blueprint.md)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t7lib import *
from t7lib import add7, STMTS7

# ------------------------------------------------------------- the indexed union of preconditions
TRIX = 'C ( T TM2Hoare M ) <. D , N >.'
BODYU = 'E. i e. ( 0 ... N ) E. w e. D ( ( ( OptStep ` ( T TM2step M ) ) ^r i ) ` ( inl ` u ) ) = ( inl ` w )'
ST_HIUN = ('( ( %s /\\ ( D C_ ( TM2Cfg ` T ) /\\ N e. NN0 ) /\\ A. x e. A %s ) -> U_ x e. A C ( T TM2Hoare M ) <. D , N >. )'
           % (PHM, TRIX))
add7('tmchiun', ST_HIUN)

# ------------------------------------------------------------- canonNum from any state
CONCL_CANS = TRI(CLN('A', SS, 'D'), CLN('E', SS, UP('D', 'K', CC(ENL, YX4))), '( ( 2 x. ( # ` L ) ) + 5 )')
add7('tmccans', statement(TREE_CAN, CONCL_CANS))

# ============================================================= mul at the machine: ~ tm2fmlv instantiated
# stacks K = x (multiplicand word L), J = y (multiplier word L'), I = w (the accumulator), I' = s, I" = t;
# the accumulator's rest is W (the lemmas) resp. ( D ` I ) (the composite).
LN, LN2 = '( # ` L )', "( # ` L' )"
XML = '( j e. NN0 |-> ( ( inclBool o. ( ( (/) repeatS j ) ++ L ) ) ++ ( <" 4 "> ++ X ) ) )'
YML = "( k e. NN0 |-> ( %s ` ( k + 1 ) ) )" % OPF("L'", 'Y')
def HMLW(W): return '( j e. NN0 |-> ( ( inclBool o. %s ) ++ ( <" 4 "> ++ %s ) ) )' % (ACCN('j'), W)
HML = HMLW('W')
UML = OPU("L'")
NRAL = lambda t: "{ h e. TMSt | ( ( TMra ` h ) = ( inl ` ( L' ` %s ) ) /\\ ( TMda ` h ) = (/) ) }" % t
NML = "( j e. NN0 |-> if ( j < ( # ` L' ) , %s , %s ) )" % (NRAL('j'), NDA)
TPM = "( ( ( 4 x. ( # ` L ) ) + ( 6 x. ( # ` L' ) ) ) + ; 1 0 )"
WFIN = "( inclBool o. ( ( (/) repeatS ( # ` L' ) ) ++ L ) )"
C0ML = CNOT('da')
CML = CRAEQ('1o')
LIDL = LID
def MLMAP(W='W'):
    return {'Y': '4', 'F': 'TMrdBit', 'C0': C0ML, 'C': CML, "L'": LIDL, 'Z0': BIT0, "F'": 'TMrdA', "C'": CIS, 'B': BITS,
            'U': UML, 'R': LN2, "T'": TPM, 'N0': '( 2nd ` T )', 'N': NML, 'X': XML, "Y'": YML, 'H': HMLW(W), 'W': WFIN, 'X0': 'X'}

_FA, _FC = split_imp(stmt('tm2fmlv'))
T_FML = parse_conj(_FA)
def fsub(path, W='W'):
    t = T_FML
    for i in path:
        t = t[i]
    return tsub(t, MLMAP(W))

FAMML = fsub((2, 1, 1, 0))                      # A. i e. ( 0 ... R ) typing
_HYP = fsub((2, 1, 1, 1))                       # A. i e. ( 0 ..^ R ) ( P /\ Q /\ DISJ )
assert _HYP.startswith("A. i e. ( 0 ..^ ( # ` L' ) ) ( ")
_HB = parse_conj(_HYP[len("A. i e. ( 0 ..^ ( # ` L' ) ) "):])
assert len(_HB) == 3
HYP_P, HYP_Q, HYP_D = [cj(x) for x in _HB]
RALI = lambda b: "A. i e. ( 0 ..^ ( # ` L' ) ) %s" % b
IDX3 = (IDX('K'), IDX('J'), IDX('I'))
PH_MF = ((GEQ, SEQ), ((WRD('L', '2o'), WRD("L'", '2o')), (WRD('X', GAM), WRD('Y', GAM), WRD('W', GAM))), IDX3)
add7('tmcmlf', statement(PH_MF, FAMML))
# the popped letter and the class after popBit, at any index of the read set
PH_PB = (SEQ, WRD("L'", '2o'), "N e. ( 0 ... ( # ` L' ) )")
UN_ = '( %s ` N )' % UML
NN_ = '( %s ` N )' % NML
ST_MLPB = statement(PH_PB, "( %s e. Gamma' /\\ A. r e. ( 2nd ` T ) ( TMrdBit ` <. r , ( inl ` %s ) >. ) e. %s )" % (UN_, UN_, NN_))
add7('tmcmlpb', ST_MLPB)
# the tests on the class family
ST_MLT = ("( ( L' e. Word 2o /\\ N e. NN0 ) -> ( ( N < ( # ` L' ) -> A. m e. %s ( %s ` m ) = 1o ) /\\ "
          "( ( # ` L' ) <_ N -> A. m e. %s -. ( %s ` m ) = 1o ) /\\ "
          "( N < ( # ` L' ) -> ( ( ( L' ` N ) = 1o -> A. m e. %s ( %s ` m ) = 1o ) /\\ ( ( L' ` N ) = (/) -> A. m e. %s -. ( %s ` m ) = 1o ) ) ) ) )"
          % (NN_, C0ML, NN_, C0ML, NN_, CML, NN_, CML))
add7('tmcmlt', ST_MLT)
add7('tmcmls', statement(PH_MF, '( %s /\\ %s )' % (RALI(HYP_P), RALI(HYP_Q))))
# the iteration's dispatch (Lean ` mulBody ` 's ite), from ~ tmcmltr
IDX5 = ((IDX('K'), IDX('J'), IDX('I')), (IDX("I'"), IDX('I"')))
DIST5 = (('K =/= J', 'K =/= I', 'J =/= I'), (("K =/= I'", 'K =/= I"'), ("J =/= I'", 'J =/= I"')), (("I =/= I'", 'I =/= I"'), 'I" =/= I\''))
DATA_MLD = ((WRD('L', '2o'), WRD("L'", '2o')), ((WRD('X', GAM), WRD('Y', GAM)), (WRD('W', GAM), STKD('D'))))
def TREE_MLD():
    return ((T_PHM7, PROG_MLTR()), (LABS_MLTR, IDX5, DIST5), DATA_MLD)
add7('tmcmld', statement(TREE_MLD(), RALI(HYP_D)))
# the composite
PROG_FML = tsub(((T_FML[0][0][1], T_FML[0][0][2]), T_FML[0][1]), MLMAP())
LABS_FML = tsub(T_FML[1][0][0], MLMAP())
LABS_X = ((LAB("G'"), LAB('G"'), LAB("Q'")), (LAB('Q"'), LAB('Q0'), LAB('G0')), (LAB("O'"), LAB('O0')))
DATA_ML = (((WRD('L', '2o'), WRD("L'", '2o')), (WRD('X', GAM), WRD('Y', GAM), STKD('D'))),
           ('( D ` K ) = ( ( inclBool o. L ) ++ ( <" 4 "> ++ X ) )', "( D ` J ) = ( ( inclBool o. L' ) ++ ( <\" 4 \"> ++ Y ) )"))
def TREE_ML():
    return ((T_PHM7, (PROG_FML, PROG_MLTR())), ((LABS_FML, LABS_X), IDX5, DIST5), DATA_ML)
ACCR = ACCN("( # ` L' )")
HFIN = '( ( inclBool o. %s ) ++ ( <" 4 "> ++ ( D ` I ) ) )' % ACCR
MULB = "( ( ( # ` L' ) x. ( ( ( 4 x. ( # ` L ) ) + ( 6 x. ( # ` L' ) ) ) + ; 1 4 ) ) + ( ( ( # ` L ) + ( # ` L' ) ) + 4 ) )"
CONCL_ML = TRI(CLN('P0', SS, 'D'), CLN("E'", SS, UP3('D', 'I', HFIN, 'K', 'X', 'J', 'Y')), MULB)
try:
    add7('tmcml', statement(TREE_ML(), CONCL_ML))
except Exception:
    pass

# ------------------------------------------------------------- mulC = mul ; canonNum w s  (Canon.lean ` mulC ` )
CAN_LAB = {'A': "E'", "A'": "R'", 'A"': 'R"', "E'": "S'", 'E"': 'S"', 'E': 'E"', 'K': 'I', 'J': "I'"}
PROG_CANW = tsub(PROG_CAN, CAN_LAB)
LABS_CANW = ((LAB("R'"), LAB('R"')), (LAB("S'"), LAB('S"'), LAB('E"')))
def TREE_MLC():
    return ((T_PHM7, (PROG_FML, PROG_MLTR(), PROG_CANW)), ((LABS_FML, LABS_X, LABS_CANW), IDX5, DIST5), DATA_ML)
ENCP = "( encNatGam ` ( ( toNat ` L ) x. ( toNat ` L' ) ) )"
MULCB = "( ( ( # ` L' ) x. ( ( ( 4 x. ( # ` L ) ) + ( 6 x. ( # ` L' ) ) ) + ; 1 4 ) ) + ( ( ( 4 x. ( # ` L ) ) + ( 7 x. ( # ` L' ) ) ) + 9 ) )"
CONCL_MLC = TRI(CLN('P0', SS, 'D'), CLN('E"', SS, UP3('D', 'I', CC(ENCP, '( <" 4 "> ++ ( D ` I ) )'), 'K', 'X', 'J', 'Y')), MULCB)
try:
    add7('tmcmulc', statement(TREE_MLC(), CONCL_MLC))
except Exception:
    pass
# mulC_le_B: the operands encoded numbers F , G below 2 ^ N
DATA_MB = ((('F e. NN0', 'G e. NN0', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )')),
           ((WRD('X', GAM), WRD('Y', GAM), STKD('D')),
            ('( D ` K ) = ( ( encNatGam ` F ) ++ ( <" 4 "> ++ X ) )', '( D ` J ) = ( ( encNatGam ` G ) ++ ( <" 4 "> ++ Y ) )')))
def TREE_MB():
    return ((T_PHM7, (PROG_FML, PROG_MLTR(), PROG_CANW)), ((LABS_FML, LABS_X, LABS_CANW), IDX5, DIST5), DATA_MB)
CONCL_MB = TRI(CLN('P0', SS, 'D'), CLN('E"', SS, UP3('D', 'I', CC('( encNatGam ` ( F x. G ) )', '( <" 4 "> ++ ( D ` I ) )'), 'K', 'X', 'J', 'Y')),
               '( TMB ` N )')
try:
    add7('tmcmulb', statement(TREE_MB(), CONCL_MB))
except Exception:
    pass
