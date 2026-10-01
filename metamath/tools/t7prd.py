r"""Sortie T7: ` predNum x s ` at the machine (Lean ` predNum_runs ` ): the
borrow run of the word, the three cases on what follows it (nothing, the top
bit, the top bit and more), and the instance of ~ tm2fprdn ."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t7lib import *
from t7lib import add7

BOR = '( borrows ` L )'
RRB = '( L substr <. ( borrows ` L ) , ( # ` L ) >. )'
RPB = '( %s substr <. 1 , ( # ` %s ) >. )' % (RRB, RRB)
RQB = '( %s substr <. 1 , ( # ` %s ) >. )' % (RPB, RPB)
WB0 = '( inclBool o. ( (/) repeatS ( borrows ` L ) ) )'
C4S = "( ( 2nd ` T ) X. { 4 } )"
CB0 = "( ( 2nd ` T ) X. { <. 1 , (/) >. } )"
CB1 = "( ( 2nd ` T ) X. { <. 1 , 1o >. } )"
B1S = '{ <. 1 , 1o >. }'
GPRD = '( { <. 1 , (/) >. } X. { <. 1 , 1o >. } )'
ZQ = '<. 1 , ( %s ` 0 ) >.' % RPB
XQ = '( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) )' % RQB
XP2 = '( ( inclBool o. %s ) ++ ( <" 4 "> ++ X ) )' % RPB

add7('tmcprdi', '( ( M e. Word 2o /\\ C e. NN0 ) -> ( predBits ` ( ( (/) repeatS C ) ++ M ) ) = ( ( 1o repeatS C ) ++ ( predBits ` M ) ) )')

PRD_MAP0 = {'F': 'TMrdA', 'C': CRAEQ('(/)'), 'P': CB1, "C'": CRAEQ('1o'), "F'": 'TMrdEnd', 'C"': 'TMdb', "P'": CB0, 'P"': C4S,
            'F"': 'TMrdA', 'C0': CIS, 'O': PBR, 'Y': '4', 'B': B0, "B'": B1S, 'G': GPRD, 'N': NPC, 'W': WB0}
def PRD_MAP(case):
    m = dict(PRD_MAP0)
    if case == 0:      # nothing after the zeros: the terminator
        m.update({'Z': '4', 'X': 'X', "Z'": '4', "X'": 'X', 'Z"': BIT0, 'Z0': CC(S1('4'), 'X')})
    elif case == 1:    # the top bit, then the terminator
        m.update({'Z': BIT1, 'X': YX4, "Z'": '4', "X'": 'X', 'Z"': BIT0, 'Z0': YX4})
    else:              # the lowest one bit and more bits
        m.update({'Z': BIT1, 'X': XP2, "Z'": ZQ, "X'": XQ, 'Z"': BIT0, 'Z0': CC(S1(BIT0), CC(S1(ZQ), XQ))})
    return m
_PA, _PC = split_imp(stmt('tm2fprdn'))
T_FPRD = parse_conj(_PA)
PROG_PRD = tsub((T_FPRD[0][0][1], T_FPRD[0][0][2], T_FPRD[0][1]), PRD_MAP0)
LABS_PRD = tsub(T_FPRD[1][0], PRD_MAP0)
TREE_PRD = ((T_PHM7, PROG_PRD), (LABS_PRD, (IDX('K'), IDX('J'), 'K =/= J')), DATA_CAN)
CONCL_PRD = TRI(CLN('A', NPC, 'D'), CLN('E', NPC, UP('D', 'K', CC("( inclBool o. ( predBits ` L ) )", YX4))), '( ( 2 x. ( # ` L ) ) + 3 )')
PRD_CASES = ['%s = (/)' % RRB, ('%s =/= (/)' % RRB, '%s = (/)' % RPB), ('%s =/= (/)' % RRB, '%s =/= (/)' % RPB)]
for _k, _l in enumerate(['tmcprd0', 'tmcprd1', 'tmcprd2']):
    add7(_l, statement((TREE_PRD, PRD_CASES[_k]), CONCL_PRD))
add7('tmcprdn', statement(TREE_PRD, CONCL_PRD))
