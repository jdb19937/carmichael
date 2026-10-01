r"""Sortie T11: Steps23.lean at the concrete machine, the scan half (coprimeToF, mulAllF, divisorsOfF,
the pool, the scan; the frozen headline ~ tmiscfb = scanF_le_B).

The installation predicates are T10's (tools/t10lib.py, read-only): every predicate sits at the numeral
stacks of its one call in Steps23.lean and takes ` T M P E ` only.  This module adds the frozen statements
of the runs forms (T11-blueprint.md section 2) and the helpers of the T11 generators.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t10lib import *
import t10lib as T10

STMTS11 = {}
TREES11 = {}
ORDER11 = []


def add11(label, tree, concl):
    STMTS11[label] = '( %s -> %s )' % (cj(tree), concl)
    TREES11[label] = (tree, concl)
    if label not in ORDER11:
        ORDER11.append(label)
    # T10's finish() reads TREES10 / STMTS10
    T10.STMTS10[label] = STMTS11[label]
    T10.TREES10[label] = (tree, concl)


def allstmts11():
    return [(l, STMTS11[l]) for l in ORDER11]


TB = lambda x: '( TMB ` %s )' % x

# ------------------------------------------------------------ mulAllF_le_B at x y r s t = 6 3 5 0 1 (ds = W , q = F)
MA_ = '( F MulAll W )'
DATA_MAF = ((STKD('D'), ('W e. Word NN0', 'F e. NN0', 'N e. NN0'), (RALB('W', 'N'), LT2('F', 'N'))),
            (WG('X'), WG('Y')), (DEQ(6, ENCL('W', 'X')), DEQ(3, EWg('F', 'Y'))))
TREE_MAF = TREE0('maf', DATA_MAF)
CONCL_MAF = TRI(CS('maf'), CLN('E', S, UP('D', '6', ENCL('( 1st ` %s )' % MA_, 'X'))),
                '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (MA_, TB('( ( 4 x. N ) + 2 )')))
add11('tmimafb', TREE_MAF, CONCL_MAF)

# ------------------------------------------------------------ divisorsOfF_le_B at x z a c s t = 5 3 7 6 0 1 (Q = W)
DV_ = '( DivisorsOf ` W )'
DATA_DVS = ((STKD('D'), 'W e. Word NN0', 'N e. NN0'), (RALB('W', 'N'), WG('X')), DEQ(5, ENCL('W', 'X')))
TREE_DVS = TREE0('dvs', DATA_DVS)
CONCL_DVS = TRI(CS('dvs'), CLN('E', S, UP('D', '5', ENCL('( 1st ` %s )' % DV_, 'X'))),
                '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (DV_, TB('( ( ( ; 1 2 x. ( # ` W ) ) x. N ) + ; 2 2 )')))
add11('tmidvsb', TREE_DVS, CONCL_DVS)

# ------------------------------------------------------------ coprimeToF_le_B at x y z s t u = 4 2 3 5 6 7 (Q = W , k = G)
CP_ = '( W CoprimeTo G )'
DATA_CPT = ((STKD('D'), ('W e. Word NN0', 'G e. NN0', 'N e. NN0'), (RALB('W', 'N'), 'A. a e. ran W 1 <_ a', LT2('G', 'N'))),
            (WG('X'), WG('Y')), (DEQ(4, ENCL('W', 'X')), DEQ(2, EWg('G', 'Y'))))
TREE_CPT = TREE0('cpt', DATA_CPT)
CONCL_CPT = TRI(CS('cpt'), CLN('E', NFL('( 1st ` %s )' % CP_), 'D'),
                '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (CP_, TB('( ( 2 x. N ) + 2 )')))
add11('tmicptb', TREE_CPT, CONCL_CPT)

# ------------------------------------------------------------ poolGoF_runs (x = F , z = Z , k = G , ds = L , bd = C , b = B)
PG_ = '( ( ( F PoolGo Z ) ` G ) ` L )'
DATA_PLF = ((STKD('D'), ('F e. NN0', 'Z e. NN0', 'G e. NN0'), ('L e. Word NN0', 'B e. NN0', 'C e. NN0')),
            ((LT2('F'), LT2('Z'), LT2('G')), (RALB('L', 'C'), (WG('X'), WG("X'")), (WG('Y'), WG("Y'")))),
            ((DEQ(0, EWg('F', 'X')), DEQ(1, EWg('Z', "X'"))), (DEQ(2, EWg('G', 'Y')), DEQ(5, ENCL('L', "Y'")))))
TREE_PLF = TREE0('plf', DATA_PLF)
CONCL_PLF = TRI(CS('plf'), CLN('E', S, UPS('D', ('5', "Y'"), ('6', ENCL('( 1st ` %s )' % PG_, DK(6))))),
                '( ( ( 2nd ` %s ) + 1 ) x. ( ; 1 6 x. %s ) )' % (PG_, TB('( ( 3 x. ( C + B ) ) + ; 1 0 )')))
add11('tmiplf', TREE_PLF, CONCL_PLF)

# ------------------------------------------------------------ poolAlgF_runs (Q = W , x = F , z = Z , k = G , bq = C , b = B)
PA_ = '( ( ( W PoolAlg F ) ` Z ) ` G )'
DATA_PLA = ((STKD('D'), ('F e. NN0', 'Z e. NN0', 'G e. NN0'), ('W e. Word NN0', 'B e. NN0', 'C e. NN0')),
            ((LT2('F'), LT2('Z'), LT2('G')), (RALB('W', 'C'), (WG('X'), WG("X'")), (WG('Y'), WG("Y'")))),
            ((DEQ(0, EWg('F', 'X')), DEQ(1, EWg('Z', "X'"))), (DEQ(2, EWg('G', 'Y')), DEQ(4, ENCL('W', "Y'")))))
TREE_PLA = TREE0('pla', DATA_PLA)
MPA = '( ( ( ( ; 1 2 x. ( ( # ` W ) + 1 ) ) x. C ) + ( 3 x. B ) ) + ; 2 2 )'
CONCL_PLA = TRI(CS('pla'), CLN('E', S, UP('D', '6', ENCL('( 1st ` %s )' % PA_, DK(6)))),
                '( ( ( 2nd ` %s ) + 1 ) x. ( ; 3 2 x. %s ) )' % (PA_, TB(MPA)))
add11('tmipla', TREE_PLA, CONCL_PLA)

# ------------------------------------------------------------ scanTest_runs (Q = W , x = F , z = Z , theta = O , k' = G)
DATA_SCT = ((STKD('D'), ('F e. NN0', 'Z e. NN0', 'O e. NN0'), ('G e. NN0', 'W e. Word NN0', ('B e. NN0', 'C e. NN0'))),
            ((RALB('W', 'C'), (LT2('F'), LT2('Z')), (LT2('O'), LT2('G'))), ((WG('X'), WG("X'")), (WG('Y'), WG("Y'")))),
            ((DEQ(0, EWg('F', EWg('O', 'X'))), DEQ(1, EWg('Z', "X'"))), (DEQ(2, EWg('G', 'Y')), DEQ(4, ENCL('W', "Y'")))))
TREE_SCT = TREE0('sct', DATA_SCT)
MS_ = '( ( ( ( ; 1 2 x. ( ( # ` W ) + 1 ) ) x. ( C + B ) ) + ( # ` W ) ) + ; 2 4 )'
PLEN_ = '( # ` ( 1st ` %s ) )' % PA_
SCTB = ('( ( ( ( ( 2nd ` %s ) + 1 ) x. ( ; 3 2 x. %s ) ) + ( ( %s + 1 ) x. %s ) ) + ( 4 x. %s ) )'
        % (PA_, TB(MS_), PLEN_, TB(MS_), TB(MS_)))
CONCL_SCT = TRI(CS('sct'), CLN('E', '{ h e. TMSt | ( TMcmp ` h ) = ( O Ncmp %s ) }' % PLEN_,
                              UP('D', '6', ENCL('( 1st ` %s )' % PA_, DK(6)))), SCTB)
add11('tmisct', TREE_SCT, CONCL_SCT)

# ------------------------------------------------------------ the headline (T10's frozen text)
add11('tmiscfb', TREE_SCF, CONCL_SCF)


def numtree11(tree):
    return (tree, NUMS)
