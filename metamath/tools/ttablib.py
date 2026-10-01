"""Sortie T-TAB: TM/Table.lean of the machine layer.

Statement texts (the frozen statements of TTAB-blueprint.md: `STATEMENTS` as
antecedent trees with conclusions, `NSTMTS` as plain texts, listed by `ORDER`)
and helpers on top of tools/tpllib.py (read-only), in T-PL's generic style:
every composite call of Table.lean (T5's `isZero`/`predNum`/`dropNum`/`dup`,
T6's `revList`/`copyList`/`moveEntry`, T-MD's `sub`/`modFrag`, and this file's
own `moveSlot`, `copySlot`, `walkDown`, `walkUp`, `dropList`, `setIfNoneF`,
`resStep`, `dpBodyF`) enters a theorem as a hypothesis triple at the stacks
the previous stage leaves, a maximal run of calls one triple; intermediate
stacks are class variables; the loops (`forSlots`, the counted loops of
`emptyTbl`/`walkDown`) run over a class family ` ( N `` i ) ` and a stack
family ` ( P `` i ) ` through ~ tm2floopu ; an ` ite ` is a disjunction
hypothesis.  The theorems execute the control: the peeks (~ tm2lpk ), the
pops (~ tm2lpop ), the pushes of a fixed letter (~ tm2fpshn ), the tests
(~ tm2lbrt / ~ tm2fbrg ) and the loops.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from tpllib import *

GAMW = "Word Gamma'"
N1F = lambda i: '( N1 ` %s )' % i
YPUSH = lambda D, K, Y: UP(D, K, CC(S1(Y), '( %s ` %s )' % (D, K)))    # push of the letter Y on stack K

# ============================================================ forSlots (Lean forSlots_runs), at TMGam
# P0: peek K F ( goto A ) [peekBlank]; A: branch C0 ( goto B0 ) ( goto E ) [Frag.loop ( ! flag )];
# the body a triple from B0 into B' at ( P ` ( i + 1 ) ) ; B': peek K F ( goto A ) [peekBlank].
# The peeked letter before iteration i is ( Z ` i ), the rest ( X ` i ), over ( 0 ... R ).
PROG_FS = (MEQ('P0', PEEKL('K', 'F', 'A')), MEQ('A', STM_LT), MEQ("B'", PEEKL('K', 'F', 'A')))
LABS_FS = ((LAB('P0'), LAB('A'), LAB('B0')), (LAB("B'"), LAB('E'), GAMK('K')))
TYPS_FS = (FTG('F'), CTY('C0'))
PKDT = lambda i: ('( ( P ` %s ) ` K ) = %s' % (i, CC(S1(ZF(i)), XF(i))), '%s e. %s' % (ZF(i), GAM), '%s e. %s' % (XF(i), GAMW))
PKDF = lambda i: cj(PKDT(i))
PKD = 'A. i e. ( 0 ... R ) %s' % PKDF('i')
BODY_FS = lambda i: TRI(CLN('B0', NF(i), PF(i)), CLN("B'", N1F(i), PF(P1(i))), "T'")
HYPF_FS = lambda i: ((HT(NF(i)), SSS(N1F(i))), (BODY_FS(i), HPK(N1F(i), 'F', ZF(P1(i)), NF(P1(i)))))
HYPS_FS = 'A. i e. ( 0 ..^ R ) %s' % cj(HYPF_FS('i'))
TREE_FS = (((T_PHM6, PROG_FS), (LABS_FS, TYPS_FS)),
           (('R e. NN0', "T' e. NN0"), (SSS('O'), HPK('O', 'F', ZF('0'), NF('0')))),
           ((FAM_L, PKD), HYPS_FS, HTF(NF('R'))))
BND_FS = "( ( R x. ( T' + 2 ) ) + 2 )"
CONCL_FS = TRI(CLN('P0', 'O', PF('0')), CLN('E', NF('R'), PF('R')), BND_FS)

# ============================================================ walkUp (Lean walkUp_runs): forSlots, then popTop at E
UPR = UP(PF('R'), 'K', XF('R'))
TREE_WUP = (TREE_FS, ((MEQ('E', POPL('K', 'F"', "E'")), LAB("E'")), (FTG('F"'), SSS("N'"), HPK(NF('R'), 'F"', ZF('R'), "N'"))))
BND_WUP = "( ( R x. ( T' + 2 ) ) + 3 )"
CONCL_WUP = TRI(CLN('P0', 'O', PF('0')), CLN("E'", "N'", UPR), BND_WUP)

# ============================================================ moveSlot (Lean moveSlot_runs), at TMGam
# P0: peek K F ( goto B' ) [peekKet src]; B': branch C ( goto B" ) ( goto E0 ) [ite flag];
# B": pop K F' ( goto B1_ ) [popTop src]; B1_: push J Y ( goto E ) [pushSym dst ket];
# E0 -> E: [ revList src s' s ; revList s' dst s ] one triple.
PROG_MVS = ((T_PHM6, (MEQ('P0', PEEKL('K', 'F', "B'")), MEQ("B'", BR('C', 'B"', 'E0')))),
            (MEQ('B"', POPL('K', "F'", 'B1_')), MEQ('B1_', PSH('J', 'Y', 'E'))))
LABS_MVS = ((LAB('P0'), LAB("B'"), LAB('B"')), (LAB('B1_'), LAB('E0'), LAB('E')), ((GAMK('K'), GAMK('J')), 'K =/= J'))
TYPS_MVS = ((FTG('F'), FTG("F'")), (CTY('C'), "Y e. %s" % GAM))
PEEK_ZX = lambda D: ('( %s ` K ) = %s' % (D, CC(S1('Z'), 'X')), 'Z e. %s' % GAM, 'X e. %s' % GAMW)
DATA_MVS = ((STKD('D'), STKD("D'")), PEEK_ZX('D'), ('T1 e. NN0', '2 <_ T1'))
CLS_MVS = (SSS('N'), SSS('N1'), SSS("N'"))
D2_MVS = UP(UP('D', 'K', 'X'), 'J', CC(S1('Y'), '( D ` J )'))
CASE_MVA = "( %s /\\ %s /\\ D' = %s )" % (HT('N1', 'C'), HPK('N1', "F'", 'Z', "N'"), D2_MVS)
TRIP_MVB = TRI(CLN('E0', 'N1', 'D'), CLN('E', "N'", "D'"), 'T1')
CASE_MVB = '( %s /\\ %s )' % (HTF('N1', 'C'), TRIP_MVB)
DISJ_MV = '( %s \\/ %s )' % (CASE_MVA, CASE_MVB)
TREE_MVS = ((PROG_MVS, LABS_MVS, TYPS_MVS), (DATA_MVS, CLS_MVS), (HPK('N', 'F', 'Z', 'N1'), DISJ_MV))
CONCL_MVS = TRI(CLN('P0', 'N', 'D'), CLN('E', "N'", "D'"), '( T1 + 2 )')

# ============================================================ copySlot (Lean copySlot_runs), at TMGam
# P0: peek K F ( goto B' ) ; B': branch C ( goto B" ) ( goto E0 ) ; B": push J Y ( goto E ) [pushSym dst ket] ;
# E0 -> E: [ copyList src dst s s' ] one triple.
PROG_CPS = (T_PHM6, (MEQ('P0', PEEKL('K', 'F', "B'")), MEQ("B'", BR('C', 'B"', 'E0')), MEQ('B"', PSH('J', 'Y', 'E'))))
LABS_CPS = ((LAB('P0'), LAB("B'"), LAB('B"')), (LAB('E0'), LAB('E')), (GAMK('K'), GAMK('J')))
TYPS_CPS = (FTG('F'), CTY('C'), "Y e. %s" % GAM)
DATA_CPS = ((STKD('D'), STKD("D'")), PEEK_ZX('D'), ('T1 e. NN0', '1 <_ T1'))
CASE_CPA = "( %s /\\ N1 C_ N' /\\ D' = %s )" % (HT('N1', 'C'), YPUSH('D', 'J', 'Y'))
CASE_CPB = '( %s /\\ %s )' % (HTF('N1', 'C'), TRIP_MVB)
DISJ_CP = '( %s \\/ %s )' % (CASE_CPA, CASE_CPB)
TREE_CPS = ((PROG_CPS, LABS_CPS, TYPS_CPS), (DATA_CPS, CLS_MVS), (HPK('N', 'F', 'Z', 'N1'), DISJ_CP))
CONCL_CPS = TRI(CLN('P0', 'N', 'D'), CLN('E', "N'", "D'"), '( T1 + 2 )')

# ============================================================ dropList (Lean dropList_runs): T6's tm2lfe with the
# body ` dropNum x ` one triple per entry, then popTop x at E.
TREE_DPL = ((T_PHF, MEQ('E', POPL('K', 'F"', "E'"))), ((LAB("E'"), FTG('F"')), (SSS("N'"), HPK(NFIN, 'F"', '2', "N'"))))
CONCL_DPL = HR(CL('P1', 'N', PF('0')), 'T', 'M', CL("E'", "N'", UPDT(PF(NL), 'K', 'R')), '( ( ( %s x. ( Y + 2 ) ) + 2 ) + 1 )' % NL)

# ============================================================ the counted loop with a marker (Lean walkDown_runs;
# emptyTbl_runs is its instance with a pushing body): alphabet-free.
# P0: push K Y ( goto P1 ) [pushSym scr blank] ; P1 -> A: [ isZero j s ] one triple (O -> ( N ` 0 ) , ( P ` 0 )) ;
# A: the loop test, the body one triple from B0 back to A (walkBody = moveSlot ; predNum ; isZero) ;
# E -> E': [ dropNum j ] one triple.
PROG_WDN = (PHM, (MEQ('P0', PSH('K', 'Y', 'P1')), MEQ('A', STM_LT)))
LABS_WDN = ((LAB('P0'), LAB('P1'), LAB('A')), (LAB('B0'), LAB('E'), LAB("E'")), (('K e. %s' % DG, 'Y e. %s' % GK), CTY('C0')))
DATA_WDN = ((STKD('D'), 'R e. NN0', "T' e. NN0"), ('U e. NN0', "U' e. NN0"))
TRIP_WD0 = TRI(CLN('P1', 'O', YPUSH('D', 'K', 'Y')), CLN('A', NF('0'), PF('0')), 'U')
TRIP_WDX = TRI(CLN('E', NF('R'), PF('R')), CLN("E'", "N'", "D'"), "U'")
TREE_WDN = ((PROG_WDN, LABS_WDN, DATA_WDN), (SSS('O'), (TRIP_WD0, TRIP_WDX)), (FAM_L, HYPS_LU, HTF(NF('R'))))
CONCL_WDN = TRI(CLN('P0', 'O', 'D'), CLN("E'", "N'", "D'"), "( ( ( U + ( R x. ( T' + 1 ) ) ) + U' ) + 2 )")

# ---- emptyTbl (Lean emptyTbl_runs, emptyBody_runs): the same with the body B0: push K Y' ( goto B' ) [pushSym tbl ket]
#      and the triple [ predNum c s ; isZero c s ] from B' back to A.
PROG_ETB = (PHM, (MEQ('P0', PSH('K', 'Y', 'P1')), MEQ('A', STM_LT), MEQ('B0', PSH('K', "Y'", "B'"))))
LABS_ETB = ((LAB('P0'), LAB('P1'), LAB('A')), (LAB('B0'), LAB("B'"), (LAB('E'), LAB("E'"))),
            (('K e. %s' % DG, 'Y e. %s' % GK, "Y' e. %s" % GK), CTY('C0')))
BODY_ETB = lambda i: TRI(CLN("B'", NF(i), YPUSH(PF(i), 'K', "Y'")), CLN('A', NF(P1(i)), PF(P1(i))), "T'")
HYPS_ETB = 'A. i e. ( 0 ..^ R ) ( %s /\\ %s )' % (HT(NF('i')), BODY_ETB('i'))
TREE_ETB = ((PROG_ETB, LABS_ETB, DATA_WDN), (SSS('O'), (TRIP_WD0, TRIP_WDX)), (FAM_L, HYPS_ETB, HTF(NF('R'))))
CONCL_ETB = TRI(CLN('P0', 'O', 'D'), CLN("E'", "N'", "D'"), "( ( ( U + ( R x. ( T' + 2 ) ) ) + U' ) + 2 )")

# ============================================================ setIfNoneF (Lean setIfNoneF_runs), at TMGam
# P0 -> Q0: [ walkDown ] triple (N -> N1, D -> D') ; Q0: peek K F ( goto B' ) [peekKet tbl] ; B': branch C ( goto B" ) ( goto E0 ) ;
# B": pop K F' ( goto B1_ ) [popTop tbl] ; B1_ -> A': [ moveSlot w tbl s j ] triple ; E0 -> A': [ dropList w ] triple ;
# A' -> E: [ walkUp ] triple.
PROG_SIN = (T_PHM6, (MEQ('Q0', PEEKL('K', 'F', "B'")), MEQ("B'", BR('C', 'B"', 'E0')), MEQ('B"', POPL('K', "F'", 'B1_'))))
LABS_SIN = ((LAB('Q0'), LAB("B'"), LAB('B"')), (LAB('B1_'), LAB('E0'), LAB("A'")), GAMK('K'))
TYPS_SIN = ((FTG('F'), FTG("F'")), CTY('C'))
DATA_SIN = (STKD("D'"), PEEK_ZX("D'"), (('U e. NN0', "U' e. NN0"), ('T1 e. NN0', 'T" e. NN0'), 'T" <_ ( T1 + 1 )'))
CLS_SIN = ((SSS('N1'), SSS('N"')), (SSS('N0'), SSS("N'")))
TRIP_SIN1 = TRI(CLN('P0', 'N', 'D'), CLN('Q0', 'N1', "D'"), 'U')
TRIP_SINA = TRI(CLN('B1_', 'N0', UP("D'", 'K', 'X')), CLN("A'", "N'", 'D"'), 'T1')
TRIP_SINB = TRI(CLN('E0', 'N"', "D'"), CLN("A'", "N'", 'D"'), 'T"')
TRIP_SIN4 = TRI(CLN("A'", "N'", 'D"'), CLN('E', 'O', 'D0'), "U'")
CASE_SINA = '( %s /\\ %s /\\ %s )' % (HT('N"', 'C'), HPK('N"', "F'", 'Z', 'N0'), TRIP_SINA)
CASE_SINB = '( %s /\\ %s )' % (HTF('N"', 'C'), TRIP_SINB)
DISJ_SIN = '( %s \\/ %s )' % (CASE_SINA, CASE_SINB)
TREE_SIN = ((PROG_SIN, LABS_SIN, TYPS_SIN), (DATA_SIN, CLS_SIN), ((TRIP_SIN1, HPK('N1', 'F', 'Z', 'N"')), DISJ_SIN, TRIP_SIN4))
CONCL_SIN = TRI(CLN('P0', 'N', 'D'), CLN('E', 'O', 'D0'), "( ( ( U + T1 ) + U' ) + 3 )")

# ============================================================ lookupSlot (Lean lookupSlot_runs), at TMGam
# as setIfNoneF with B": push J Y ( goto A' ) [pushSym w ket] and E0 -> A': [ copyList tbl w s j ] triple.
PROG_LKS = (T_PHM6, (MEQ('Q0', PEEKL('K', 'F', "B'")), MEQ("B'", BR('C', 'B"', 'E0')), MEQ('B"', PSH('J', 'Y', "A'"))))
LABS_LKS = ((LAB('Q0'), LAB("B'"), LAB('B"')), (LAB('E0'), LAB("A'")), (GAMK('K'), GAMK('J')))
TYPS_LKS = (FTG('F'), CTY('C'), "Y e. %s" % GAM)
DATA_LKS = ((STKD("D'"), STKD('D"')), PEEK_ZX("D'"), (('U e. NN0', "U' e. NN0"), 'T1 e. NN0', '1 <_ T1'))
CLS_LKS = (SSS('N1'), SSS('N"'), SSS("N'"))
TRIP_LKSB = TRI(CLN('E0', 'N"', "D'"), CLN("A'", "N'", 'D"'), 'T1')
CASE_LKSA = '( %s /\\ N" C_ N\' /\\ D" = %s )' % (HT('N"', 'C'), YPUSH("D'", 'J', 'Y'))
CASE_LKSB = '( %s /\\ %s )' % (HTF('N"', 'C'), TRIP_LKSB)
DISJ_LKS = '( %s \\/ %s )' % (CASE_LKSA, CASE_LKSB)
TREE_LKS = ((PROG_LKS, LABS_LKS, TYPS_LKS), (DATA_LKS, CLS_LKS), ((TRIP_SIN1, HPK('N1', 'F', 'Z', 'N"')), DISJ_LKS, TRIP_SIN4))
CONCL_LKS = TRI(CLN('P0', 'N', 'D'), CLN('E', 'O', 'D0'), "( ( ( U + T1 ) + U' ) + 2 )")

# ============================================================ copyTbl (Lean copyTbl_runs), at TMGam
# P0: push J Y ( goto P1 ) [pushSym dst blank] ; P1: push I Y ( goto Q0 ) [pushSym hold blank] ;
# Q0: forSlots src ( copySlot ; moveSlot ) [the body one triple] ; E -> E': [ walkUp src s' s hold ] triple.
FS_Q0 = {'P0': 'Q0'}
TREE_FSQ = ren(TREE_FS, FS_Q0)
INIT_CTB = '%s = %s' % (PF('0'), UP(YPUSH('D', 'J', 'Y'), 'I', CC(S1('Y'), '( D ` I )')))
TREE_CTB = (TREE_FSQ,
            ((MEQ('P0', PSH('J', 'Y', 'P1')), MEQ('P1', PSH('I', 'Y', 'Q0'))), ((LAB('P0'), LAB('P1')), (GAMK('J'), GAMK('I')), 'I =/= J'),
             ("Y e. %s" % GAM, STKD('D'), INIT_CTB)),
            ('U e. NN0', TRI(CLN('E', NF('R'), PF('R')), CLN("E'", "N'", "D'"), 'U')))
CONCL_CTB = TRI(CLN('P0', 'O', 'D'), CLN("E'", "N'", "D'"), "( ( ( R x. ( T' + 2 ) ) + U ) + 4 )")

# ============================================================ resStep (Lean resStep_runs), alphabet-free
# P0 -> B': [ moveEntry ; dup ; dup ; cmpFrag ] triple ; B': branch C ( goto E0 ) ( goto E1 ) [ite ( cmp = lt )] ;
# E0 -> A: the seven calls, one triple ; E1 -> A: [ dup ; sub ] one triple ; A -> E: [ moveEntry ] triple.
PROG_RST = (PHM, MEQ("B'", BR('C', 'E0', 'E1')))
LABS_RST = ((LAB("B'"), LAB('E0'), LAB('E1')), CTY('C'))
DATA_RST = ((STKD("D'"), SSS('N1')), (('T1 e. NN0', 'T" e. NN0'), ("T0 e. NN0", "T' e. NN0"), 'T0 <_ T"'))
TRIP_RST1 = TRI(CLN('P0', 'N', 'D'), CLN("B'", 'N1', "D'"), 'T1')
TRIP_RSTA = TRI(CLN('E0', 'N1', "D'"), CLN('A', 'N"', 'D"'), 'T"')
TRIP_RSTB = TRI(CLN('E1', 'N1', "D'"), CLN('A', 'N"', 'D"'), 'T0')
TRIP_RST4 = TRI(CLN('A', 'N"', 'D"'), CLN('E', "N'", 'D0'), "T'")
DISJ_RST = '( ( %s /\\ %s ) \\/ ( %s /\\ %s ) )' % (HT('N1', 'C'), TRIP_RSTA, HTF('N1', 'C'), TRIP_RSTB)
TREE_RST = ((PROG_RST, LABS_RST), DATA_RST, (TRIP_RST1, DISJ_RST, TRIP_RST4))
CONCL_RST = TRI(CLN('P0', 'N', 'D'), CLN('E', "N'", 'D0'), "( ( ( T1 + T\" ) + T' ) + 1 )")

# ============================================================ dpBodyF (Lean dpBodyF_runs), at TMGam
# P0 -> Q0: [ resStep ] triple ; Q0: peek K F ( goto B' ) [peekKet snap] ; B': branch C ( goto B" ) ( goto E0 ) ;
# B": pop K F' ( goto A ) [popTop snap] ; E0 -> A: [ dup np snap s ; dup nL np s ; setIfNoneF acc np snap s t ] triple.
PROG_DPB = (T_PHM6, (MEQ('Q0', PEEKL('K', 'F', "B'")), MEQ("B'", BR('C', 'B"', 'E0')), MEQ('B"', POPL('K', "F'", 'A'))))
LABS_DPB = ((LAB('Q0'), LAB("B'"), LAB('B"')), (LAB('E0'), LAB('A')), GAMK('K'))
DATA_DPB = (STKD("D'"), PEEK_ZX("D'"), ('U e. NN0', 'T1 e. NN0', '1 <_ T1'))
CLS_DPB = (SSS('N1'), SSS('N"'), SSS("N'"))
TRIP_DPB1 = TRI(CLN('P0', 'N', 'D'), CLN('Q0', 'N1', "D'"), 'U')
CASE_DPBA = '( %s /\\ %s /\\ D" = %s )' % (HT('N"', 'C'), HPK('N"', "F'", 'Z', "N'"), UP("D'", 'K', 'X'))
CASE_DPBB = '( %s /\\ %s )' % (HTF('N"', 'C'), TRI(CLN('E0', 'N"', "D'"), CLN('A', "N'", 'D"'), 'T1'))
DISJ_DPB = '( %s \\/ %s )' % (CASE_DPBA, CASE_DPBB)
TREE_DPB = ((PROG_DPB, LABS_DPB, TYPS_SIN), (DATA_DPB, CLS_DPB), (TRIP_DPB1, HPK('N1', 'F', 'Z', 'N"'), DISJ_DPB))
CONCL_DPB = TRI(CLN('P0', 'N', 'D'), CLN('A', "N'", 'D"'), '( ( U + T1 ) + 2 )')

# ============================================================ dpStepF (Lean dpStepF_runs), at TMGam
# P0 -> Q0: [ dup nL t s ; dup np nL s ; modFrag ] triple ; Q0: push K Y ( goto Q' ) [pushSym snap bra] ;
# Q' -> P1: [ dup np snap s ; dup nL np s ; setIfNoneF ; pushNum nL 0 ] triple ; P1: walkUp's shape on snap
# (forSlots snap dpBodyF, the body one triple ; popTop snap at E) ; E' -> E": [ dropNum ; dropNum ; dropNum ] triple.
WUP_P1 = {'P0': 'P1', 'O': 'O"'}
TREE_WUPP = ren(TREE_WUP, WUP_P1)
TRIP_DPS1 = TRI(CLN('P0', 'O', 'D'), CLN('Q0', "O'", "D'"), 'U')
TRIP_DPS2 = TRI(CLN("Q'", "O'", YPUSH("D'", 'K', 'Y')), CLN('P1', 'O"', PF('0')), "U'")
TRIP_DPS3 = TRI(CLN("E'", "N'", UPR), CLN('E"', 'N0', 'D0'), 'U"')
TREE_DPS = (TREE_WUPP,
            ((MEQ('Q0', PSH('K', 'Y', "Q'")), (LAB('Q0'), LAB("Q'")), "Y e. %s" % GAM),
             (STKD("D'"), SSS("O'"), ('U e. NN0', "U' e. NN0", 'U" e. NN0'))),
            (TRIP_DPS1, TRIP_DPS2, TRIP_DPS3))
CONCL_DPS = TRI(CLN('P0', 'O', 'D'), CLN('E"', 'N0', 'D0'), "( ( ( ( U + U' ) + U\" ) + ( R x. ( T' + 2 ) ) ) + 4 )")

STATEMENTS = [
    ('tm2ftfs', TREE_FS, CONCL_FS), ('tm2fwup', TREE_WUP, CONCL_WUP),
    ('tm2fmvs', TREE_MVS, CONCL_MVS), ('tm2fcps', TREE_CPS, CONCL_CPS), ('tm2fdpl', TREE_DPL, CONCL_DPL),
    ('tm2fwdn', TREE_WDN, CONCL_WDN), ('tm2fetb', TREE_ETB, CONCL_ETB),
    ('tm2fsin', TREE_SIN, CONCL_SIN), ('tm2flks', TREE_LKS, CONCL_LKS), ('tm2fctb', TREE_CTB, CONCL_CTB),
    ('tm2frst', TREE_RST, CONCL_RST), ('tm2fdpb', TREE_DPB, CONCL_DPB), ('tm2fdps', TREE_DPS, CONCL_DPS)]

# ============================================================ the budget arithmetic of the _le_B wrappers (N level, D7)
# Lean's cost functions, expanded (letters: J the index, L the table length, N the slot bound, B the bit bound b,
# M the index bit bound m).
def SLOT(N='N', B='B'):
    """slotC N b = N * (4 * b + 12) + 10"""
    return '( ( %s x. ( ( 4 x. %s ) + ; 1 2 ) ) + ; 1 0 )' % (N, B)


def SETC(J, N, B, M):
    """setC j N b m = j * (2 * slotC N b + 4 * m + 11) + slotC N b + 3 * m + 14"""
    return ('( ( ( ( %s x. ( ( ( 2 x. %s ) + ( 4 x. %s ) ) + ; 1 1 ) ) + %s ) + ( 3 x. %s ) ) + ; 1 4 )'
            % (J, SLOT(N, B), M, SLOT(N, B), M))


def LOOKC(J, N, B, M):
    """lookC j N b m = j * (2 * slotC N b + 4 * m + 11) + N * (6 * b + 17) + 3 * m + 22"""
    return ('( ( ( ( %s x. ( ( ( 2 x. %s ) + ( 4 x. %s ) ) + ; 1 1 ) ) + ( %s x. ( ( 6 x. %s ) + ; 1 7 ) ) ) + ( 3 x. %s ) ) + ; 2 2 )'
            % (J, SLOT(N, B), M, N, B, M))


def COPYC(L, N, B):
    """copyC L N b = L * copySlotC N b + 8, copySlotC N b = N * (6 * b + 17) + 2 * slotC N b + 15"""
    return '( ( %s x. ( ( ( %s x. ( ( 6 x. %s ) + ; 1 7 ) ) + ( 2 x. %s ) ) + ; 1 5 ) ) + 8 )' % (L, N, B, SLOT(N, B))


def DPBODYC(L, N, B):
    """dpBodyC L N b = 56 * b + 67 + setC L (N + 1) b (2 * b)"""
    return '( ( ( ; 5 6 x. %s ) + ; 6 7 ) + %s )' % (B, SETC(L, '( %s + 1 )' % N, B, '( 2 x. %s )' % B))


def DPC(L, N, B):
    """dpC L N b = b * (46 * b + 60) + 33 * b + 64 + setC L (N + 1) b (2 * b) + L * (dpBodyC L N b + 2)"""
    return ('( ( ( ( ( %s x. ( ( ; 4 6 x. %s ) + ; 6 0 ) ) + ( ; 3 3 x. %s ) ) + ; 6 4 ) + %s ) + ( %s x. ( %s + 2 ) ) )'
            % (B, B, B, SETC(L, '( %s + 1 )' % N, B, '( 2 x. %s )' % B), L, DPBODYC(L, N, B)))


TB = TMB('B')
NN0S = lambda *xs: ' /\\ '.join('%s e. NN0' % x for x in xs)
ST_SETM = ("( ( ( J e. NN0 /\\ J' e. NN0 /\\ J <_ J' ) /\\ ( N e. NN0 /\\ B e. NN0 /\\ M e. NN0 ) ) -> %s <_ %s )"
           % (SETC('J', 'N', 'B', 'M'), SETC("J'", 'N', 'B', 'M')))
ST_SETLE = ('( ( J e. NN0 /\\ N e. NN0 /\\ B e. NN0 ) -> %s <_ ( ( ( J + 1 ) x. ( N + 2 ) ) x. ( ( ; 1 6 x. B ) + ; 4 9 ) ) )'
            % SETC('J', '( N + 1 )', 'B', '( 2 x. B )'))
ST_LKB = ('( ( J e. NN0 /\\ N e. NN0 /\\ B e. NN0 ) -> %s <_ ( ( ( J + 1 ) x. ( N + 2 ) ) x. %s ) )'
          % (LOOKC('J', 'N', 'B', '( 2 x. B )'), TB))
ST_CPB = '( ( L e. NN0 /\\ N e. NN0 /\\ B e. NN0 ) -> %s <_ ( ( ( L + 1 ) x. ( N + 2 ) ) x. %s ) )' % (COPYC('L', 'N', 'B'), TB)
ST_DPC = ('( ( L e. NN0 /\\ N e. NN0 /\\ B e. NN0 ) -> %s <_ ( ( ( ( L + 1 ) ^ 2 ) x. ( N + 2 ) ) x. %s ) )'
          % (DPC('L', 'N', 'B'), TB))
NSTMTS = [('ttabsetm', ST_SETM), ('ttabsetle', ST_SETLE), ('ttablkb', ST_LKB), ('ttabcpb', ST_CPB), ('ttabdpc', ST_DPC)]

# ============================================================ the table encodings consumed by Step4 / Step5
# (df-tm2encslot, df-tm2enctbla, df-tm2enctbld in the sortie file).  TblBounded is inlined, over every residue
# (blueprint D9): TBB( T , N , B ) = A. d e. NN0 ( ( T ` d ) =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` ( T ` d ) ) ) <_ N /\
# A. q e. ran ( 2nd ` ( T ` d ) ) q < ( 2 ^ B ) ) ).
NONE = '( inr ` (/) )'
TBB = lambda T, N, B: ('A. d e. NN0 ( ( %s ` d ) =/= %s -> ( ( # ` ( 2nd ` ( %s ` d ) ) ) <_ %s /\\ A. q e. ran ( 2nd ` ( %s ` d ) ) q < ( 2 ^ %s ) ) )'
                       % (T, NONE, T, N, T, B))
ST_KETHD = "( ( W e. Word NN0 /\\ R e. Word Gamma' ) -> ( ( ( encList ` W ) ++ R ) ` 0 ) =/= 3 )"
ST_SLOTK = ("( ( O e. ( Word NN0 |_| 1o ) /\\ R e. Word Gamma' ) -> ( ( ( ( encSlot ` O ) ++ R ) ` 0 ) = 3 <-> O = %s ) )" % NONE)
ST_TBB0 = '( ( N e. NN0 /\\ B e. NN0 ) -> %s )' % TBB('EmptyTbl', 'N', 'B')
ST_TBBM = "( ( ( N e. NN0 /\\ N' e. NN0 /\\ N <_ N' ) /\\ %s ) -> %s )" % (TBB('T', 'N', 'B'), TBB('T', "N'", 'B'))
ST_TBLL = ('( ( ( L e. NN0 /\\ T e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 ) /\\ %s ) -> ( # ` ( L encTblAsc T ) ) <_ ( L x. ( ( N x. ( B + 1 ) ) + 1 ) ) )'
           % TBB('T', 'N', 'B'))
ST_TBDP = ('( ( ( L e. NN /\\ P e. NN0 /\\ T e. Tbl ) /\\ ( N e. NN0 /\\ B e. NN0 /\\ P < ( 2 ^ B ) ) /\\ %s ) -> %s )'
           % (TBB('T', 'N', 'B'), TBB('( 1st ` ( ( L DpStep P ) ` T ) )', '( N + 1 )', 'B')))
NSTMTS += [('ttabkethd', ST_KETHD), ('ttabslotk', ST_SLOTK), ('ttabtbb0', ST_TBB0), ('ttabtbbm', ST_TBBM),
           ('ttabtbll', ST_TBLL), ('ttabtbdp', ST_TBDP)]

ORDER = ['tm2ftfs', 'tm2fwup', 'tm2fmvs', 'tm2fcps', 'tm2fdpl', 'tm2fwdn', 'tm2fetb', 'tm2fsin', 'tm2flks', 'tm2fctb',
         'tm2frst', 'tm2fdpb', 'tm2fdps', 'ttabsetm', 'ttabsetle', 'ttablkb', 'ttabcpb', 'ttabdpc',
         'ttabkethd', 'ttabslotk', 'ttabtbb0', 'ttabtbbm', 'ttabtbll', 'ttabtbdp']


def allstmts():
    d = dict(NSTMTS)
    d.update({l: statement(t, c) for l, t, c in STATEMENTS})
    assert set(d) == set(ORDER), set(d) ^ set(ORDER)
    return [(l, d[l]) for l in ORDER]
