r"""Sortie T7: ` cmpFrag x y ` at the machine (Lean ` cmpFrag_runs ` ,
` cmp_correct ` ): the comparison sequence, the classes of the comparator
(the adder's with ` cmp ` in place of ` carry ` ), their interfaces, and the
instance of ~ tm2fcmp ."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t7lib import *
from t7lib import add7

CMS = "( cmpStep ( ( toNat ` L ) bwFold ( toNat ` L' ) ) 1o )"
NCMPV = "( ( toNat ` L ) Ncmp ( toNat ` L' ) )"
def MCOND(C):
    f = NCOND(C)
    return lambda h, j: f(h, j).replace('( TMcar ` %s )' % h, '( TMcmp ` %s )' % h, 1)
def OMCOND(C):
    f = OCOND(C)
    return lambda h, j: f(h, j).replace('( TMcar ` %s )' % h, '( TMcmp ` %s )' % h, 1)
def NFM(C): return '( j e. NN0 |-> { h e. TMSt | %s } )' % MCOND(C)('h', 'j')
def OFM(C): return '( j e. NN0 |-> { h e. TMSt | %s } )' % OMCOND(C)('h', 'j')
def mcond_tree(C, h, j):
    t = ncond_tree(C, h, j)
    return ((t[0][0].replace('TMcar', 'TMcmp', 1), t[0][1], t[0][2]), t[1])
def omcond_tree(C, h, j):
    t = ocond_tree(C, h, j)
    return ((t[0][0].replace('TMcar', 'TMcmp', 1), t[0][1], t[0][2]), t[1])
assert cj(mcond_tree('C', 'h', 'j')) == MCOND('C')('h', 'j') and cj(omcond_tree('C', 'h', 'j')) == OMCOND('C')('h', 'j')
NFMG, OFMG = NFM('C'), OFM('C')
NFMS, OFMS = NFM(CMS), OFM(CMS)
NCMF = '{ h e. TMSt | ( TMcmp ` h ) = %s }' % NCMPV

add7('tmccmss', "( ( 2nd ` T ) = TMSt -> A. i e. NN0 ( ( %s ` i ) C_ ( 2nd ` T ) /\\ ( %s ` i ) C_ ( 2nd ` T ) ) )" % (NFMG, OFMG))
add7('tmccmin', "( ( ( 2nd ` T ) = TMSt /\\ %s /\\ ( C ` 0 ) = 1o ) -> A. r e. ( 2nd ` T ) ( %s ` r ) e. ( %s ` 0 ) )" % (PH_LL, LCMP0, NFMG))
RDN1 = RDIF('TMrdA', 'n', 'L', 'i')
RDN2 = RDIF('TMrdB', RDN1, "L'", 'i')
ST_CMRD = ("( %s -> A. i e. NN0 A. n e. ( %s ` i ) ( ( ( TMda ` n ) = 1o <-> -. i e. %s ) /\\ ( ( TMdb ` %s ) = 1o <-> -. i e. %s ) /\\ %s e. ( %s ` i ) ) )"
           % (PH_LL, NFMG, OPR('L'), RDN1, OPR("L'"), RDN2, OFMG))
add7('tmccmrd', ST_CMRD)
add7('tmccmc0', '( %s -> ( %s ` 0 ) = 1o )' % (PH_LL, CMS))
add7('tmccmcp', "( ( %s /\\ N e. NN0 ) -> ( %s ` ( N + 1 ) ) = ( ( %s cmpStep %s ) ` ( %s ` N ) ) )" % (PH_LL, CMS, BIT('L', 'N'), BIT("L'", 'N'), CMS))
ST_CMBD = ("( %s -> A. i e. ( 0 ..^ %s ) A. p e. ( %s ` i ) ( -. ( %s ` p ) = 1o /\\ ( %s ` p ) e. ( %s ` ( i + 1 ) ) ) )"
           % (PH_LL, MXA, OFMS, CANDD, LCMP, NFMS))
add7('tmccmbd', ST_CMBD)
ST_CMEX = "( %s -> A. p e. ( %s ` %s ) ( ( %s ` p ) = 1o /\\ p e. %s ) )" % (PH_LL, OFMS, MXA, CANDD, NCMF)
add7('tmccmex', ST_CMEX)

CMP_MAP = {'C': 'TMda', "C'": 'TMdb', 'C"': CANDD, 'F': 'TMrdA', "F'": 'TMrdB', 'G': LCMP, 'L': LCMP0, 'B': MXA,
           'N0': '( 2nd ` T )', "N'": NCMF, 'N': NFMS, 'O': OFMS, 'X': OPFX, 'Y': OPFY, 'U': OPUX, "U'": OPUY,
           'R': OPR('L'), "R'": OPR("L'")}
_CA, _CC = split_imp(stmt('tm2fcmp'))
T_FCMP = parse_conj(_CA)
def PROG_CMP():
    return tsub((T_FCMP[0][0][1], T_FCMP[0][0][2]), CMP_MAP)
LABS_CMP = tsub(T_FCMP[0][1][0], CMP_MAP)
DATA_CMP = DATA_ADD
def TREE_CMP():
    return ((T_PHM7, PROG_CMP()), (LABS_CMP, (IDX('K'), IDX('J'), 'K =/= J')), DATA_CMP)
CONCL_CMP = TRI(CLN("A'", SS, 'D'), CLN('E', NCMF, UP(UP('D', 'K', 'X'), 'J', 'Y')), '( %s + 2 )' % MXA)
add7('tmccmp', statement(TREE_CMP(), CONCL_CMP))
