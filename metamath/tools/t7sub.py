r"""Sortie T7: ` sub x y z x ` at the machine (Lean ` sub_runs_x ` ): the N-level
facts of the borrow and difference sequences, the subtractor's body, exit and
` zeroIfBorrow ` interfaces, and the instance of ~ tm2fsubx .  The read phase
and the state classes are the adder's ( ~ tmcadrd , ~ tmcadss , ~ tmcadin ,
generic in the carry sequence ` C ` ) at the borrow sequence."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t7lib import *
from t7lib import add7

TA, TB = '( toNat ` L )', "( toNat ` L' )"
CRB = "( borrow ( ( toNat ` L ) bwFold ( toNat ` L' ) ) (/) )"
SUBV = "( ( toNat ` L ) - ( ( toNat ` L' ) + ( bToNat ` (/) ) ) )"
ZSB = '( inclBool o. ( %s bwrd %s ) )' % (SUBV, MXA)
ZT = "( inclBool o. ( ( L subTrunc L' ) ` (/) ) )"
NFB, OFB = NFC(CRB), OFC(CRB)
CRBM = '( %s ` %s )' % (CRB, MXA)
NCB = '{ h e. TMSt | ( TMcar ` h ) = %s }' % CRBM
LBOR_X = lambda t: '( ( ( bitOf ` ( TMra ` %s ) ) borrow ( bitOf ` ( TMrb ` %s ) ) ) ` ( TMcar ` %s ) )' % (t, t, t)
assert LBOR == LSET(car=LBOR_X('u'))
C4S = "( ( 2nd ` T ) X. { 4 } )"

add7('tmcsbc0', '( %s -> ( %s ` 0 ) = (/) )' % (PH_LL, CRB))
add7('tmcsbdg', "( ( %s /\\ N e. NN0 ) -> ( ( %s sumBit %s ) ` ( %s ` N ) ) = if ( N e. ( bits ` %s ) , 1o , (/) ) )"
     % (PH_LL, BIT('L', 'N'), BIT("L'", 'N'), CRB, SUBV))
add7('tmcsbcp', "( ( %s /\\ N e. NN0 ) -> ( %s ` ( N + 1 ) ) = ( ( %s borrow %s ) ` ( %s ` N ) ) )"
     % (PH_LL, CRB, BIT('L', 'N'), BIT("L'", 'N'), CRB))
add7('tmcsbzl', '( %s -> ( # ` %s ) = %s )' % (PH_LL, ZSB, MXA))
add7('tmcsbzv', '( ( %s /\\ N e. ( 0 ..^ %s ) ) -> ( %s ` N ) = <. 1 , if ( N e. ( bits ` %s ) , 1o , (/) ) >. )' % (PH_LL, MXA, ZSB, SUBV))
ST_SBBD = ("( %s -> A. i e. ( 0 ..^ ( # ` %s ) ) A. p e. ( %s ` i ) ( -. ( %s ` p ) = 1o /\\ ( %s ` p ) = ( %s ` i ) /\\ ( %s ` p ) e. ( %s ` ( i + 1 ) ) ) )"
           % (PH_LL, ZSB, OFB, CANDD, PSUM, ZSB, LBOR, NFB))
add7('tmcsbbd', ST_SBBD)
ST_SBEX = "( %s -> A. p e. ( %s ` ( # ` %s ) ) ( ( %s ` p ) = 1o /\\ p e. %s ) )" % (PH_LL, OFB, ZSB, CANDD, NCB)
add7('tmcsbex', ST_SBEX)

SUB_MAP = {'C': 'TMda', "C'": 'TMdb', 'C"': CANDD, 'C0': 'TMcar', 'C1_': CIS, 'F': 'TMrdA', "F'": 'TMrdB', 'F"': 'TMrdA',
           'P': PSUM, "P'": C4S, 'P"': PBR, 'G': LBOR, 'L': LADD0, "L'": LCAR0, 'Q': '4', 'B': BITS, 'Z': ZSB, 'Z"': ZT,
           'N0': '( 2nd ` T )', "N'": NCB, 'N"': '( 2nd ` T )', 'N': NFB, 'O': OFB, 'X': OPFX, 'Y': OPFY, 'U': OPUX, "U'": OPUY,
           'R': OPR('L'), "R'": OPR("L'")}
_SA, _SC = split_imp(stmt('tm2fsubx'))
T_FSUB = parse_conj(_SA)
ZR_DISJ = cj(tsub(T_FSUB[0][2][2][1], SUB_MAP))
ST_SBZR = '( ( %s /\\ %s ) -> %s )' % (SEQ, PH_LL, ZR_DISJ)
add7('tmcsbzr', ST_SBZR)


def PROG_SUBX():
    return tsub((T_FSUB[0][0][0][1:], T_FSUB[0][0][1]), SUB_MAP)
LABS_SUB = tsub(T_FSUB[0][1][0], SUB_MAP)
def TREE_SUBX():
    return ((T_PHM7, PROG_SUBX()), (LABS_SUB, (IDX('K'), IDX('J'), IDX('I')), ('K =/= J', 'K =/= I', 'J =/= I')), DATA_ADD)
CONCL_SUBX = TRI(CLN("A'", SS, 'D'), CLN('E', SS, UP(UP('D', 'K', CC(ZT, '( <" 4 "> ++ X )')), 'J', 'Y')), '( ( 3 x. %s ) + 5 )' % MXA)
add7('tmcsubx', statement(TREE_SUBX(), CONCL_SUBX))

# ------------------------------------------------------------- subCx = sub x y z x ; canonNum x z  (Steps23 ` subCx_le_B ` )
CANS_LAB = {'A': 'E', "A'": "R'", 'A"': 'R"', "E'": "S'", 'E"': 'S"', 'E': 'G0', 'K': 'K', 'J': 'I'}
PROG_CANS = tsub(PROG_CAN, CANS_LAB)
LABS_CANS = ((LAB("R'"), LAB('R"')), (LAB("S'"), LAB('S"'), LAB('G0')))
DATA_SUBC = ((('F e. NN0', 'G e. NN0', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )')),
             ((WRD('X', GAM), WRD('Y', GAM), STKD('D')),
              ('( D ` K ) = ( ( encNatGam ` F ) ++ ( <" 4 "> ++ X ) )', '( D ` J ) = ( ( encNatGam ` G ) ++ ( <" 4 "> ++ Y ) )')))
def TREE_SUBC():
    return ((T_PHM7, (PROG_SUBX(), PROG_CANS)), ((LABS_SUB, LABS_CANS), (IDX('K'), IDX('J'), IDX('I')), ('K =/= J', 'K =/= I', 'J =/= I')), DATA_SUBC)
TRUNC = 'if ( F < G , 0 , ( F - G ) )'
CONCL_SUBC = TRI(CLN("A'", SS, 'D'), CLN('G0', SS, UP(UP('D', 'K', CC('( encNatGam ` %s )' % TRUNC, '( <" 4 "> ++ X )')), 'J', 'Y')), '( TMB ` N )')
add7('tmcsubcb', statement(TREE_SUBC(), CONCL_SUBC))
