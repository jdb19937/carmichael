r"""Sortie T7: ` incr y s ` at the machine (Lean ` incr_runs ` ): the carry run
of the word, the two cases on the stop letter, and the instance of
~ tm2fincr ."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t7lib import *
from t7lib import add7

CAR = '( carries ` L )'
RR_ = '( L substr <. ( carries ` L ) , ( # ` L ) >. )'
RP_ = '( %s substr <. 1 , ( # ` %s ) >. )' % (RR_, RR_)
WI = '( inclBool o. ( 1o repeatS ( carries ` L ) ) )'
C4S = "( ( 2nd ` T ) X. { 4 } )"
CB0 = "( ( 2nd ` T ) X. { <. 1 , (/) >. } )"
CB1 = "( ( 2nd ` T ) X. { <. 1 , 1o >. } )"
B1S = '{ <. 1 , 1o >. }'
GINC = '( { <. 1 , 1o >. } X. { <. 1 , (/) >. } )'
XFP = '( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) )' % RP_
Z0P = '( <" <. 1 , 1o >. "> ++ %s )' % XFP
Z0T = '( <" <. 1 , 1o >. "> ++ ( <" 4 "> ++ X ) )'

add7('tmcinc1', '( ( M e. Word 2o /\\ C e. NN0 ) -> ( incBits ` ( ( 1o repeatS C ) ++ M ) ) = ( ( (/) repeatS C ) ++ ( incBits ` M ) ) )')

INC_MAP0 = {'F': 'TMrdA', 'C': CRAEQ('1o'), 'P': CB0, "C'": CRAEQ('(/)'), "P'": CB1, 'P"': C4S, 'F"': 'TMrdA', 'C0': CIS,
            'O': PBR, 'Y': '4', 'B': B1S, "B'": B0, 'G': GINC, 'N': NPC, 'W': WI, "Z'": BIT1, 'Z"': '4'}
def INC_MAP(pos):
    m = dict(INC_MAP0)
    if pos:
        m.update({'Z': BIT0, 'X': XFP, 'Z0': Z0P})
    else:
        m.update({'Z': '4', 'X': 'X', 'Z0': Z0T})
    return m
_IA, _IC = split_imp(stmt('tm2fincr'))
T_FINC = parse_conj(_IA)
PROG_INC = tsub((T_FINC[0][0][1], T_FINC[0][0][2], T_FINC[0][1]), INC_MAP0)
LABS_INC = tsub(T_FINC[1][0], INC_MAP0)
TREE_INC = ((T_PHM7, PROG_INC), (LABS_INC, (IDX('K'), IDX('J'), 'K =/= J')), DATA_CAN)
CONCL_INC = TRI(CLN('A', NPC, 'D'), CLN('E', NPC, UP('D', 'K', CC("( inclBool o. ( incBits ` L ) )", YX4))), '( ( 2 x. ( # ` L ) ) + 3 )')
add7('tmcincp', statement((TREE_INC, '%s =/= (/)' % RR_), CONCL_INC))
add7('tmcinct', statement((TREE_INC, '%s = (/)' % RR_), CONCL_INC))
add7('tmcincr', statement(TREE_INC, CONCL_INC))
