r"""Sortie T7: the ` _le_B ` forms of the delivered composites at the encodings
of numbers below ` 2 ^ N ` (Lean ` dup_le_B ` , ` dropNum_le_B ` ,
` isZero_le_B ` , ` incr_le_B ` , ` predNum_le_B ` , ` cmp_correct ` with a
` TMB ` bound)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t7lib import *
from t7lib import add7
from t7cmp import PROG_CMP, LABS_CMP
from t7inc import TREE_INC, PROG_INC, LABS_INC
from t7prd import TREE_PRD, PROG_PRD, LABS_PRD

NUMS = ('F e. NN0', 'N e. NN0', 'F < ( 2 ^ N )')
ENF = '( encNatGam ` F )'
ENG = '( encNatGam ` G )'
TB = '( TMB ` N )'
DK_F = '( D ` K ) = ( %s ++ ( <" 4 "> ++ X ) )' % ENF

# dup x y s
TREE_DUPB = ((T_PHM7, PROG_DUP), (LABS6, (IDX('K'), IDX('J'), IDX('I')), ('K =/= J', 'K =/= I', 'J =/= I')),
             (NUMS, (WRD('X', GAM), STKD('D')), DK_F))
CONCL_DUPB = TRI(CLN('A', SS, 'D'), CLN('E', SS, UP('D', 'J', CC(ENF, CC(S1('4'), '( D ` J )')))), TB)
add7('tmcdupb', statement(TREE_DUPB, CONCL_DUPB))
# dropNum x
STM_DROPB = POP('K', 'TMrdA', BRANCH(CIS, GT('A'), GT('E')))
TREE_DROPB = ((T_PHM7, MEQ('A', STM_DROPB)), ((LAB('A'), LAB('E')), IDX('K')), (NUMS, (STKD('D'), WRD('X', GAM))))
CONCL_DROPB = TRI(CLN('A', SS, UP('D', 'K', CC(ENF, YX4))), CLN('E', SS, UP('D', 'K', 'X')), TB)
add7('tmcdropb', statement(TREE_DROPB, CONCL_DROPB))
# isZero x s
DATA_ENC = (NUMS, (WRD('X', GAM), STKD('D')), DK_F)
TREE_IZB = ((T_PHM7, PROG_IZ), (LABS6, (IDX('K'), IDX('I'), 'K =/= I')), DATA_ENC)
NZF = '{ h e. TMSt | ( ( TMfl ` h ) = if ( F = 0 , 1o , (/) ) /\\ ( TMcmp ` h ) = Q ) }'
CONCL_IZB = TRI(CLN('A', NPC, 'D'), CLN('E', NZF, 'D'), TB)
add7('tmcizb', statement(TREE_IZB, CONCL_IZB))
# incr y s
TREE_INCB = ((T_PHM7, PROG_INC), (LABS_INC, (IDX('K'), IDX('J'), 'K =/= J')), DATA_ENC)
CONCL_INCB = TRI(CLN('A', NPC, 'D'), CLN('E', NPC, UP('D', 'K', CC('( encNatGam ` ( F + 1 ) )', YX4))), TB)
add7('tmcincb', statement(TREE_INCB, CONCL_INCB))
# predNum x s  ( 1 <_ F )
add7('tmcpredenc', '( F e. NN -> ( predBits ` ( encodeNat ` F ) ) = ( encodeNat ` ( F - 1 ) ) )')
TREE_PRDB = ((T_PHM7, PROG_PRD), (LABS_PRD, (IDX('K'), IDX('J'), 'K =/= J')), ((('F e. NN', 'N e. NN0', 'F < ( 2 ^ N )'), (WRD('X', GAM), STKD('D')), DK_F)))
CONCL_PRDB = TRI(CLN('A', NPC, 'D'), CLN('E', NPC, UP('D', 'K', CC('( encNatGam ` ( F - 1 ) )', YX4))), TB)
add7('tmcprdb', statement(TREE_PRDB, CONCL_PRDB))
# cmpFrag x y
NUMS2 = (('F e. NN0', 'G e. NN0', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )'))
DATA_ENC2 = (NUMS2, ((WRD('X', GAM), WRD('Y', GAM), STKD('D')),
                     (DK_F, '( D ` J ) = ( %s ++ ( <" 4 "> ++ Y ) )' % ENG)))
TREE_CMPB = ((T_PHM7, PROG_CMP()), (LABS_CMP, (IDX('K'), IDX('J'), 'K =/= J')), DATA_ENC2)
NCFG = '{ h e. TMSt | ( TMcmp ` h ) = ( F Ncmp G ) }'
CONCL_CMPB = TRI(CLN("A'", SS, 'D'), CLN('E', NCFG, UP(UP('D', 'K', 'X'), 'J', 'Y')), TB)
add7('tmccmpb', statement(TREE_CMPB, CONCL_CMPB))
