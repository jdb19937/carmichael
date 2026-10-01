"""Sortie T-PL: PrimTD.lean and PrimList.lean of the machine layer.

Statement texts (the frozen statements of TPL-blueprint.md are produced
here: `STATEMENTS` as antecedent trees with conclusions, `NSTMTS` as plain
texts) and helpers on top of tools/t5lib.py, tools/t5blib.py, tools/t6blib.py
and tools/tmdlib.py (all read-only).

Style (blueprint D1-D6): every composite call of the two Lean files enters
the generic theorem as a hypothesis triple at the stacks the previous stage
leaves; intermediate stacks are class variables; a loop runs over a stack
family ` ( P `` i ) ` and a class family ` ( N `` i ) ` ; PrimTD is
alphabet-free (T5 style), PrimList is at ` TMGam ` (T6 style, it cites the
Lists layer).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
import lin
lin.FASTPATH = True
from t6blib import *          # t6lib names (CL, UPDT, PSH, PEEKL, POPL, TESTL, GOTOL, FZ8, WWB, WG, B4, PHM6, ...),
                              # t6_f_mes names (FT, CT, IFACE, HPOP, NFIN, ...), Builder, inst, parse_conj, stmt, tsub, triple_parts
from t5blib import (GK, GJ, GI, GIP, HDL, CTY, LTY, PTY, RTY, LAB, STKD, STMT, CONST, S1, CC, WRD, FV, P1, MEQ, NV, SSS,
                    TRI, UP3, ren, flat, HT, HTF, inst_v, ifval, clnex, statement)
from t5lib import (lift, CLN, GT, UP, NVF, conj, cj, Ctx, Lifter, hrseq, hrle, hrssc, hrssd, hrrw, cfgcl, clnss, upid, updcl,
                   updkv, updnv, stkfv, elv, upc, up2, up3, up4, gotocl, pushcl, pushccl, popcl, peekcl, brcl, loadcl,
                   s1w, ccatw, revw, sswordd, jtree, applylem, nn0cl, bound, clneq, clnneq, upeq, upidv, GX, DG, LL,
                   STK_T, CFG_T, STMT_T, SS)
from t1lib import PUSH, PEEK, POP, LOAD, BRANCH, GOTO, UPD, CONSTF, HR, PHM, Exec, evaluate
from t3_lib import hstepc2
from tmdlib import bldr, leafsteps
import t6_d_fe as fe

# ------------------------------------------------------------- notation

BR = lambda C, X, Y: BRANCH(C, GT(X), GT(Y))        # Frag.loop's test / Frag.ite: branch C ( goto X ) ( goto Y )
LD = lambda Lf, X: LOAD(Lf, GT(X))                  # Frag.load' : load Lf ( goto X )
HLD = lambda N, O, Lf: 'A. m e. %s ( %s ` m ) e. %s' % (N, Lf, O)   # the load lands in O
NF = lambda i: '( N ` %s )' % i
N1F = lambda i: '( N1 ` %s )' % i
N2F = lambda i: '( N" ` %s )' % i
N3F = lambda i: '( N0 ` %s )' % i
PF = lambda i: '( P ` %s )' % i
PPF = lambda i: "( P' ` %s )" % i
UF = lambda i: '( U ` %s )' % i
UPF = lambda i: "( U' ` %s )" % i
ZF = lambda i: '( Z ` %s )' % i
XF = lambda i: '( X ` %s )' % i
SUM = lambda i, R, body: 'sum_ %s e. ( 0 ..^ %s ) %s' % (i, R, body)

# ============================================================ the calculus: Sigma-cost iteration and the loop rules

# tm2hitsum: tm2hitr with a per-iteration bound family ( U ` i )
HITS_HYP = lambda R: 'A. i e. ( 0 ..^ %s ) ( %s e. NN0 /\\ %s )' % (R, UF('i'), TRI('( I ` i )', '( I ` ( i + 1 ) )', UF('i')))
HITS_ANTE = lambda R: '( %s /\\ ( I ` 0 ) C_ %s /\\ %s )' % (PHM, CFG_T, HITS_HYP(R))
HITS_CONCL = lambda R: TRI('( I ` 0 )', '( I ` %s )' % R, SUM('i', R, UF('i')))
ST_HITSUM = '( R e. NN0 -> ( %s -> %s ) )' % (HITS_ANTE('R'), HITS_CONCL('R'))

# the loop rules (Lean Frag.loop_runs' and Frag.loop_runs): test at A on C0, body from B0 back to A, exit E
STM_LT = BR('C0', 'B0', 'E')
FAM_L = 'A. i e. ( 0 ... R ) ( %s /\\ %s )' % (SSS(NF('i')), STKD(PF('i')))
BODY_L = lambda i, U: TRI(CLN('B0', NF(i), PF(i)), CLN('A', NF(P1(i)), PF(P1(i))), U)
HYPS_LS = 'A. i e. ( 0 ..^ R ) ( ( %s /\\ %s e. NN0 ) /\\ %s )' % (HT(NF('i')), UF('i'), BODY_L('i', UF('i')))
HYPS_LU = 'A. i e. ( 0 ..^ R ) ( %s /\\ %s )' % (HT(NF('i')), BODY_L('i', "T'"))
HEAD_L = ((PHM, MEQ('A', STM_LT)), ((LAB('A'), LAB('B0'), LAB('E')), (CTY('C0'), 'R e. NN0')))
TREE_LOOPS = (HEAD_L, (FAM_L, HYPS_LS, HTF(NF('R'))))
CONCL_LOOPS = TRI(CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R')), '( %s + 1 )' % SUM('i', 'R', '( %s + 1 )' % UF('i')))
TREE_LOOPU = ((HEAD_L, "T' e. NN0"), (FAM_L, HYPS_LU, HTF(NF('R'))))
CONCL_LOOPU = TRI(CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R')), "( ( R x. ( T' + 1 ) ) + 1 )")

# ============================================================ PrimTD.lean (alphabet-free)

# ---- primeGoBody (blueprint 2.1): from the body entry B0 back to the test A.
#      B0: [ dup xd s t ; dup xd t s ; mulC ; dup xm s t ; cmpFrag ] (triple, N -> N1, stacks restored) -> B'
#      B': ite ( cmp = lt ) : B" load L -> A  |  E0: [ dup ; dup ; modC ; isZero ; dropNum ] (triple, N1 -> N") -> E'
#      E': ite flag : E" load L' -> A  |  A0: [ incr xd ; predNum xf ; isZero xf ] (triple, N" -> N0, stacks D') -> A' load L" -> A
PROG_PGB = ((PHM, (MEQ("B'", BR('C', 'B"', 'E0')), MEQ('B"', LD('L', 'A')))),
            (MEQ("E'", BR("C'", 'E"', 'A0')), MEQ('E"', LD("L'", 'A')), MEQ("A'", LD('L"', 'A'))))
LABS_PGB = ((LAB('B0'), LAB("B'"), LAB('B"')), (LAB('E0'), LAB("E'"), LAB('E"')), (LAB('A0'), LAB("A'"), LAB('A')))
TYPS_PGB = ((CTY('C'), CTY("C'")), (LTY('L'), LTY("L'"), LTY('L"')))
DATA_PGB = ((STKD('D'), STKD("D'")), ('T1 e. NN0', 'T" e. NN0', 'T0 e. NN0'))
CLS_PGB = ((SSS('N'), SSS('N1')), (SSS('N"'), SSS('N0'), SSS("N'")))
TRIP_PG1 = TRI(CLN('B0', 'N', 'D'), CLN("B'", 'N1', 'D'), 'T1')
TRIP_PG2 = TRI(CLN('E0', 'N1', 'D'), CLN("E'", 'N"', 'D'), 'T"')
TRIP_PG3 = TRI(CLN('A0', 'N"', 'D'), CLN("A'", 'N0', "D'"), 'T0')
CASE_PGA = '( %s /\\ %s /\\ D\' = D )' % (HT('N1', 'C'), HLD('N1', "N'", 'L'))
CASE_PGB1 = '( %s /\\ %s /\\ D\' = D )' % (HT('N"', "C'"), HLD('N"', "N'", "L'"))
CASE_PGB2 = '( %s /\\ %s /\\ %s )' % (HTF('N"', "C'"), TRIP_PG3, HLD('N0', "N'", 'L"'))
DISJ_PG2 = '( %s \\/ %s )' % (CASE_PGB1, CASE_PGB2)
CASE_PGB = '( %s /\\ %s /\\ %s )' % (HTF('N1', 'C'), TRIP_PG2, DISJ_PG2)
DISJ_PG = '( %s \\/ %s )' % (CASE_PGA, CASE_PGB)
TREE_PGB = ((PROG_PGB, (LABS_PGB, TYPS_PGB)), (DATA_PGB, CLS_PGB, (TRIP_PG1, DISJ_PG)))
TD_PG = '( ( ( T1 + T" ) + T0 ) + 3 )'
CONCL_PGB = TRI(CLN('B0', 'N', 'D'), CLN('A', "N'", "D'"), TD_PG)

# ---- the loop of primeGoF (Frag.loop_runs at PGInv): tm2fpgb at every iteration, the families
#      ( N ` i ) ( N1 ` i ) ( N" ` i ) ( N0 ` i ) and the stacks ( P ` i )
PGQ_MAP = lambda i: {'N': NF(i), 'N1': N1F(i), 'N"': N2F(i), 'N0': N3F(i), "N'": NF(P1(i)), 'D': PF(i), "D'": PF(P1(i))}
PGB_AT = lambda i: (sub(TRIP_PG1, PGQ_MAP(i)), sub(DISJ_PG, PGQ_MAP(i)))
HYP_PGQ_TREE = lambda i: ((HT(NF(i)), (SSS(N1F(i)), SSS(N2F(i)), SSS(N3F(i)))), PGB_AT(i))
HYPS_PGQ = 'A. i e. ( 0 ..^ R ) %s' % cj(HYP_PGQ_TREE('i'))
PROG_PGQ = (PROG_PGB, MEQ('A', STM_LT))
LABS_PGQ = (LABS_PGB, LAB('E'))
TYPS_PGQ = (TYPS_PGB, CTY('C0'))
DATA_PGQ = ('R e. NN0', ('T1 e. NN0', 'T" e. NN0', 'T0 e. NN0'))
TREE_PGQ = ((PROG_PGQ, (LABS_PGQ, TYPS_PGQ)), (DATA_PGQ, (FAM_L, HYPS_PGQ), HTF(NF('R'))))
BND_PGQ = '( ( R x. ( %s + 1 ) ) + 1 )' % TD_PG
CONCL_PGQ = TRI(CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R')), BND_PGQ)

# ---- primeGoF: P0 [ isZero xf s ] (triple, O -> O') -> P1 load L0 -> A, the loop, exit E
TRIP_PG0 = TRI(CLN('P0', 'O', PF('0')), CLN('P1', "O'", PF('0')), 'U')
TREE_PG = (((PROG_PGQ, MEQ('P1', LD('L0', 'A'))), ((LABS_PGQ, (LAB('P0'), LAB('P1'))), (TYPS_PGQ, LTY('L0')))),
           ((DATA_PGQ, 'U e. NN0'), (FAM_L, HYPS_PGQ), HTF(NF('R'))),
           ((SSS('O'), SSS("O'")), (TRIP_PG0, HLD("O'", NF('0'), 'L0'))))
BND_PG = '( ( U + 1 ) + %s )' % BND_PGQ
CONCL_PG = TRI(CLN('P0', 'O', PF('0')), CLN('E', NF('R'), PF('R')), BND_PG)

# ---- isPrimeTDF: P0 [ pushNum s 2 ; dup xm t u ; cmpFrag t s ] (triple, N -> N1, stacks D) -> B'
#      B': ite ( cmp = lt ) : B" load L -> E  |  E0 [ pushNum xd 2 ; dup xm xf s ] -> E' [ primeGoF ] -> E" [ dropNum ; dropNum ] -> E
PROG_IPT = (PHM, (MEQ("B'", BR('C', 'B"', 'E0')), MEQ('B"', LD('L', 'E'))))
LABS_IPT = ((LAB('P0'), LAB("B'"), LAB('B"')), (LAB('E0'), LAB("E'"), LAB('E"')), LAB('E'))
TYPS_IPT = (CTY('C'), LTY('L'))
BNDS_IPT = (('T1 e. NN0', 'T" e. NN0'), ("T0 e. NN0", "T' e. NN0"), '1 <_ T"')
CLS_IPT = ((SSS('N'), SSS('N1')), (SSS('N"'), SSS('N0'), SSS("N'")))
TRIP_IP1 = TRI(CLN('P0', 'N', 'D'), CLN("B'", 'N1', 'D'), 'T1')
TRIP_IPA = TRI(CLN('E0', 'N1', 'D'), CLN("E'", 'N"', "D'"), 'T"')
TRIP_IPB = TRI(CLN("E'", 'N"', "D'"), CLN('E"', 'N0', 'D"'), 'T0')
TRIP_IPC = TRI(CLN('E"', 'N0', 'D"'), CLN('E', "N'", 'D0'), "T'")
CASE_IPA = '( %s /\\ %s /\\ D0 = D )' % (HT('N1', 'C'), HLD('N1', "N'", 'L'))
CASE_IPB = '( %s /\\ ( %s /\\ %s /\\ %s ) )' % (HTF('N1', 'C'), TRIP_IPA, TRIP_IPB, TRIP_IPC)
DISJ_IP = '( %s \\/ %s )' % (CASE_IPA, CASE_IPB)
TREE_IPT = ((PROG_IPT, (LABS_IPT, TYPS_IPT)), ((STKD('D'), BNDS_IPT), CLS_IPT, (TRIP_IP1, DISJ_IP)))
CONCL_IPT = TRI(CLN('P0', 'N', 'D'), CLN('E', "N'", 'D0'), '( ( T1 + ( ( T" + T0 ) + T\' ) ) + 1 )')

# ---- divOutTest: A [ dup ; dup ; divmodC ; isZero ; dropNum ] (triple, N -> N1, stacks D -> D') -> B'
#      B': ite flag : B" [ isZero xf s ] (triple, N1 -> N") -> E0 load L -> E  |  E' skip ( load L' ) -> E
PROG_DOT = (PHM, (MEQ("B'", BR('C', 'B"', "E'")), MEQ('E0', LD('L', 'E')), MEQ("E'", LD("L'", 'E'))))
LABS_DOT = ((LAB('A'), LAB("B'"), LAB('B"')), (LAB('E0'), LAB("E'"), LAB('E')))
TYPS_DOT = (CTY('C'), (LTY('L'), LTY("L'")))
DATA_DOT = (STKD("D'"), ('T1 e. NN0', 'T" e. NN0'))
CLS_DOT = ((SSS('N'), SSS('N1')), (SSS('N"'), SSS("N'")))
TRIP_DO1 = TRI(CLN('A', 'N', 'D'), CLN("B'", 'N1', "D'"), 'T1')
TRIP_DO2 = TRI(CLN('B"', 'N1', "D'"), CLN('E0', 'N"', "D'"), 'T"')
CASE_DOA = '( %s /\\ %s /\\ %s )' % (HT('N1', 'C'), TRIP_DO2, HLD('N"', "N'", 'L'))
CASE_DOB = '( %s /\\ %s )' % (HTF('N1', 'C'), HLD('N1', "N'", "L'"))
DISJ_DO = '( %s \\/ %s )' % (CASE_DOA, CASE_DOB)
TREE_DOT = ((PROG_DOT, (LABS_DOT, TYPS_DOT)), (DATA_DOT, CLS_DOT, (TRIP_DO1, DISJ_DO)))
CONCL_DOT = TRI(CLN('A', 'N', 'D'), CLN('E', "N'", "D'"), '( ( T1 + T" ) + 2 )')

# ---- divOutF: P0 [ divOutTest ] (triple, O -> ( N ` 0 ), D -> ( P ` 0 )) -> A ; the loop (body = one triple
#      per iteration, ` dropNum xr ; moveEntry u xr s ; predNum xf s ; divOutTest ` ) ; E [ dropNum u ] (triple) -> E'
TRIP_DO0 = TRI(CLN('P0', 'O', 'D'), CLN('A', NF('0'), PF('0')), 'U')
TRIP_DOX = TRI(CLN('E', NF('R'), PF('R')), CLN("E'", "N'", "D'"), "U'")
TREE_DO = ((HEAD_L, ((LAB('P0'), LAB("E'")), ("T' e. NN0", ('U e. NN0', "U' e. NN0")))),
           ((FAM_L, HYPS_LU, HTF(NF('R'))), ((SSS('O'), SSS("N'")), (TRIP_DO0, TRIP_DOX))))
CONCL_DO = TRI(CLN('P0', 'O', 'D'), CLN("E'", "N'", "D'"), "( ( U + ( ( R x. ( T' + 1 ) ) + 1 ) ) + U' )")

# ---- smoothGoF: P0 [ isZero xF s ] (triple, O -> ( N ` 0 ), stacks ( P ` 0 )) -> A ; the loop with the body
#      ` dup xr xf s ; divOutF ; dropNum xf ; incr xd s ; predNum xF s ; isZero xF s ` one triple per iteration,
#      its cost ( U' ` i ) (Lean Frag.loop_runs_budget: the Sigma form)
HYPS_SG = 'A. i e. ( 0 ..^ R ) ( ( %s /\\ %s e. NN0 ) /\\ %s )' % (HT(NF('i')), UPF('i'), BODY_L('i', UPF('i')))
TRIP_SG0 = TRI(CLN('P0', 'O', PF('0')), CLN('A', NF('0'), PF('0')), 'U')
TREE_SG = ((HEAD_L, (LAB('P0'), 'U e. NN0')), ((FAM_L, HYPS_SG, HTF(NF('R'))), (SSS('O'), TRIP_SG0)))
CONCL_SG = TRI(CLN('P0', 'O', PF('0')), CLN('E', NF('R'), PF('R')), '( U + ( %s + 1 ) )' % SUM('i', 'R', '( %s + 1 )' % UPF('i')))

# ---- smoothTDF: P0 [ dup ; predNum ; moveEntry ; pushNum xd 2 ] -> P1 [ smoothGoF ] -> A [ dropNum ; dropNum ; pushNum s 1 ; cmpFrag ] -> A' load L -> E
TRIP_ST1 = TRI(CLN('P0', 'N', 'D'), CLN('P1', 'N1', "D'"), 'T1')
TRIP_ST2 = TRI(CLN('P1', 'N1', "D'"), CLN('A', 'N"', 'D"'), 'T"')
TRIP_ST3 = TRI(CLN('A', 'N"', 'D"'), CLN("A'", 'N0', 'D0'), 'T0')
TREE_STD = (((PHM, MEQ("A'", LD('L', 'E'))), ((LAB("A'"), LAB('E')), (LTY('L'), STKD('D0')))),
            ((('T1 e. NN0', 'T" e. NN0', 'T0 e. NN0'), (SSS('N0'), SSS("N'"))), ((TRIP_ST1, TRIP_ST2), (TRIP_ST3, HLD('N0', "N'", 'L')))))
CONCL_STD = TRI(CLN('P0', 'N', 'D'), CLN('E', "N'", 'D0'), '( ( ( T1 + T" ) + T0 ) + 1 )')

STATEMENTS = [
    ('tm2floop', TREE_LOOPS, CONCL_LOOPS), ('tm2floopu', TREE_LOOPU, CONCL_LOOPU),
    ('tm2fpgb', TREE_PGB, CONCL_PGB), ('tm2fpgq', TREE_PGQ, CONCL_PGQ), ('tm2fpg', TREE_PG, CONCL_PG),
    ('tm2fipt', TREE_IPT, CONCL_IPT), ('tm2fdot', TREE_DOT, CONCL_DOT), ('tm2fdo', TREE_DO, CONCL_DO),
    ('tm2fsg', TREE_SG, CONCL_SG), ('tm2fstd', TREE_STD, CONCL_STD)]
NSTMTS = [('tm2hitsum', ST_HITSUM)]

# ============================================================ the budget lemmas consumed by Step5 / Steps23 / Overhead (N level)

TMB = lambda x: '( TMB ` %s )' % x
ST_B34 = '( B e. NN0 -> %s = ( ; 2 7 x. %s ) )' % (TMB('( ( 3 x. B ) + 4 )'), TMB('B'))
ST_B37 = '( B e. NN0 -> %s = ( ; 2 7 x. %s ) )' % (TMB('( ( 3 x. B ) + 7 )'), TMB('( B + 1 )'))
ST_B410 = '( B e. NN0 -> %s = ( ; 6 4 x. %s ) )' % (TMB('( ( 4 x. B ) + ; 1 0 )'), TMB('( B + 1 )'))
ST_BSUC = '( B e. NN0 -> %s <_ %s )' % (TMB('B'), TMB('( B + 1 )'))
ST_BSCALE = '( ( C e. NN0 /\\ M e. NN0 ) -> ( ( ( C + 1 ) ^ 3 ) x. %s ) = %s )' % (TMB('M'), TMB('( ( ( C + 1 ) x. M ) + ( 2 x. C ) )'))
ST_2POW = '( N e. NN0 -> ( N + 1 ) <_ ( 2 ^ N ) )'
ST_POWSUC = '( ( A e. RR /\\ B e. NN0 /\\ A < ( 2 ^ B ) ) -> A < ( 2 ^ ( B + 1 ) ) )'
ST_PRODLE = ('( ( L e. Word NN0 /\\ B e. NN0 /\\ A. p e. ran L p < ( 2 ^ B ) ) -> ( 1st ` ( ProdL ` L ) ) <_ ( 2 ^ ( ( # ` L ) x. B ) ) )')
NSTMTS += [('tplb34', ST_B34), ('tplb37', ST_B37), ('tplb410', ST_B410), ('tplbsuc', ST_BSUC), ('tplbscale', ST_BSCALE),
           ('tpl2pow', ST_2POW), ('tplpowsuc', ST_POWSUC), ('tplprodle', ST_PRODLE)]

# ============================================================ PrimList.lean (at TMGam, the Lists layer's alphabet)

GAMK = lambda k: '%s e. %s' % (k, FZ8)
GAM = "Gamma'"
FTG = lambda F: FT(F)                                 # F e. ( S ^m ( S X. ( Gamma' |_| 1o ) ) )
PTG = lambda G: "%s e. ( Gamma' ^m %s )" % (G, SS)   # a push-letter function at the concrete alphabet
HPK = lambda N, F, Z, O: 'A. r e. %s %s e. %s' % (N, NVF(F, 'r', Z), O)   # the peek / pop handler lands in O

# ---- the generic push of a state-dependent letter (Lean pushBit): push K P ( goto E ) with P constant Z on N
STM_PSHF = PUSH('K', 'P', GT('E'))
TREE_PSHF = ((PHM, MEQ('A', STM_PSHF)), (LAB('A'), LAB('E'), ('K e. %s' % DG, 'Z e. %s' % GK)),
             ((PTY('P', 'K'), 'A. r e. N ( P ` r ) = Z'), (STKD('D'), SSS('N'))))
CONCL_PSHF = TRI(CLN('A', 'N', 'D'), CLN('E', 'N', UP('D', 'K', CC(S1('Z'), '( D ` K )'))), '1')

GEQ = '( 1st ` ( 1st ` T ) ) = TMGam'
T_PHM6 = (PHM, GEQ)
assert cj(T_PHM6) == PHM6

# ---- forEntries, Sigma cost (Lean forEntries_runs'): T6's tm2lfe with the per-entry bound ( Y ` j )
NL = fe.NL
YF = lambda j: '( Y ` %s )' % j
HBSF = lambda j: '( %s e. NN0 /\\ %s )' % (YF(j), HR(CL("A'", 'N', PF(j)), 'T', 'M', CL('A"', 'N', PF(P1(j))), YF(j)))
HBS = 'A. j e. ( 0 ..^ %s ) %s' % (NL, HBSF('j'))
T_PROG_FE = parse_conj(fe.PROG)
T_LABS_FE = (parse_conj(fe.LAB1), parse_conj(fe.LAB2))
T_TYPS_FE = (fe.FTY, fe.CTY)
T_IFS_FE = ('N C_ %s' % SS, parse_conj(fe.IFACE))
T_LR = ('L e. %s' % WWB, 'R e. %s' % WG)
T_PP = (fe.PTY, fe.PK)
TREE_PHP = ((T_PHM6, T_PROG_FE), (T_LABS_FE, T_TYPS_FE, T_IFS_FE), (T_LR, T_PP))          # the peek lemmas' antecedent
TREE_FES = ((T_PHM6, T_PROG_FE), (T_LABS_FE, T_TYPS_FE, T_IFS_FE), (T_LR, T_PP, HBS))     # the Sigma loop's antecedent
PHP = cj(TREE_PHP); PHFS = cj(TREE_FES)
NFJ = fe.NF
CONCL_FES = HR(CL('P1', 'N', PF('0')), 'T', 'M', CL('E', NFIN, PF(NL)), '( %s + 2 )' % SUM('j', NL, '( %s + 2 )' % YF('j')))
# the sublemmas (T6's tm2lfe1a / 1b / 1 / 2 / 3 in the Sigma setting)
ST_FES1A = '( ( %s /\\ J e. ( 0 ..^ %s ) ) -> %s )' % (PHP, NL, fe.RAL('J'))
ST_FES1B = '( ( %s /\\ J = %s ) -> %s )' % (PHP, NL, fe.RAL('J'))
UH_FES = '( U e. %s /\\ ( M ` U ) = %s )' % (LL, fe.PEEKS)
ST_FES1 = '( ( %s /\\ %s /\\ J e. ( 0 ... %s ) ) -> %s )' % (PHP, UH_FES, NL, HR(CL('U', 'N', PF('J')), 'T', 'M', CL('A', NFJ('J'), PF('J')), '1'))
ST_FES2 = '( ( %s /\\ J e. ( 0 ..^ %s ) ) -> %s )' % (PHFS, NL, HR(CL('A', NFJ('J'), PF('J')), 'T', 'M', CL('A', NFJ('( J + 1 )'), PF('( J + 1 )')), '( %s + 2 )' % YF('J')))
ST_FES3 = '( %s -> %s )' % (PHFS, HR(CL('A', NFJ('0'), PF('0')), 'T', 'M', CL('A', NFJ(NL), PF(NL)), SUM('j', NL, '( %s + 2 )' % YF('j'))))
ST_FES = '( %s -> %s )' % (PHFS, CONCL_FES)

# ---- prodLF (blueprint 3.2): P0 [ copyList x c s t ; pushNum w 1 ] (triple, O -> N, D -> ( P ` 0 )) -> P1 ,
#      forEntries c prodBody (tm2lfe, the body ` mulC c w x s t ; moveEntry x w s ` one triple per entry) -> E ,
#      E popTop c ( pop K F" ( goto E' ) ) -> E'.  Stack K = c.
T_PHF = parse_conj(fe.PHF)
TRIP_PRL = HR(CL('P0', 'O', 'D'), 'T', 'M', CL('P1', 'N', PF('0')), 'U')
TREE_PRL = ((T_PHF, MEQ('E', POPL('K', 'F"', "E'"))),
            ((LAB('P0'), LAB("E'"), FTG('F"')), (SSS('O'), SSS("N'"), 'U e. NN0'), (TRIP_PRL, HPK(NFIN, 'F"', '2', "N'"))))
CONCL_PRL = HR(CL('P0', 'O', 'D'), 'T', 'M', CL("E'", "N'", UPDT(PF(NL), 'K', 'R')), '( ( U + ( ( %s x. ( Y + 2 ) ) + 2 ) ) + 1 )' % NL)

# ---- cpBody (blueprint 3.3): B0 [ dup x t s ; dup y u s ; modC ; isZero u s ] (triple, N -> N1, D -> D') -> B'
#      B' load L -> B" [ dropNum u ; moveEntry x z s ] (triple, N" -> N0, D' -> D") -> B1_ peekBraOr x ( peek K F ( goto A ) ) -> A
PROG_CPB = (T_PHM6, (MEQ("B'", LD('L', 'B"')), MEQ('B1_', PEEKL('K', 'F', 'A'))))
LABS_CPB = ((LAB('B0'), LAB("B'"), LAB('B"')), (LAB('B1_'), LAB('A'), GAMK('K')))
TYPS_CPB = (LTY('L'), FTG('F'))
DATA_CPB = ((STKD("D'"), STKD('D"')), ('( D" ` K ) = %s' % CC(S1('Z'), 'X'), 'Z e. %s' % GAM, 'X e. %s' % WG), ('T1 e. NN0', 'T" e. NN0'))
CLS_CPB = ((SSS('N'), SSS('N1')), (SSS('N"'), SSS('N0'), SSS("N'")))
TRIP_CP1 = TRI(CLN('B0', 'N', 'D'), CLN("B'", 'N1', "D'"), 'T1')
TRIP_CP2 = TRI(CLN('B"', 'N"', "D'"), CLN('B1_', 'N0', 'D"'), 'T"')
IFS_CPB = (HLD('N1', 'N"', 'L'), HPK('N0', 'F', 'Z', "N'"))
TREE_CPB = ((PROG_CPB, (LABS_CPB, TYPS_CPB)), (DATA_CPB, CLS_CPB, (IFS_CPB, (TRIP_CP1, TRIP_CP2))))
TD_CP = '( ( T1 + T" ) + 2 )'
CONCL_CPB = TRI(CLN('B0', 'N', 'D'), CLN('A', "N'", 'D"'), TD_CP)

# ---- the loop of coprimeToF: tm2fcpb at every iteration over the families ( N ` i ) ( N1 ` i ) ( N" ` i ) ( N0 ` i ),
#      the stacks ( P ` i ) ( P' ` i ) ( P ` ( i + 1 ) ), the peeked letter ( Z ` i ) and rest ( X ` i )
CPQ_MAP = lambda i: {'N': NF(i), 'N1': N1F(i), 'N"': N2F(i), 'N0': N3F(i), "N'": NF(P1(i)), 'D': PF(i), "D'": PPF(i), 'D"': PF(P1(i)),
                     'Z': ZF(i), 'X': XF(i)}
HYP_CPQ_TREE = lambda i: ((HT(NF(i)), (SSS(N1F(i)), SSS(N2F(i)), SSS(N3F(i)))),
                          (STKD(PPF(i)), ren(DATA_CPB[1], CPQ_MAP(i))),
                          (ren(IFS_CPB, CPQ_MAP(i)), (sub(TRIP_CP1, CPQ_MAP(i)), sub(TRIP_CP2, CPQ_MAP(i)))))
HYPS_CPQ = 'A. i e. ( 0 ..^ R ) %s' % cj(HYP_CPQ_TREE('i'))
PROG_CPQ = (PROG_CPB, MEQ('A', STM_LT))
LABS_CPQ = (LABS_CPB, LAB('E'))
TYPS_CPQ = (TYPS_CPB, CTY('C0'))
TREE_CPQ = ((PROG_CPQ, (LABS_CPQ, TYPS_CPQ)), (('R e. NN0', ('T1 e. NN0', 'T" e. NN0')), (FAM_L, HYPS_CPQ), HTF(NF('R'))))
BND_CPQ = '( ( R x. ( %s + 1 ) ) + 1 )' % TD_CP
CONCL_CPQ = TRI(CLN('A', NF('0'), PF('0')), CLN('E', NF('R'), PF('R')), BND_CPQ)

# ---- coprimeToF: P0 pushSym z bra ( push I 2 -> P1 ) ; P1 load L0 -> Q0 ; Q0 peekBra x ( peek K F0 -> A ) ; the loop ;
#      E pushSym t comma ( push I' 4 -> E' ) ; E' pushBit t G ( push I' G -> E" ) ; E" [ moveEntries z x s ] -> E0 [ isZero t s ] -> E1 [ dropNum t ] -> D'
#      Stacks K = x, I = z, I' = t.
P0R = PF('R')
D2_CPT = UPDT(P0R, "I'", CC(S1("Z'"), CC(S1('4'), "( %s ` I' )" % P0R)))
TRIP_CPM = TRI(CLN('E"', NF('R'), D2_CPT), CLN('E0', 'N"', 'D"'), 'U')
TRIP_CPZ = TRI(CLN('E0', 'N"', 'D"'), CLN('E1', 'N0', 'D0'), "U'")
TRIP_CPD = TRI(CLN('E1', 'N0', 'D0'), CLN("D'", "N'", 'D1_'), 'U"')
PROG_CPT = ((PROG_CPQ, (MEQ('P0', PSH('I', '2', 'P1')), MEQ('P1', LD('L0', 'Q0')), MEQ('Q0', PEEKL('K', 'F0', 'A')))),
            (MEQ('E', PSH("I'", '4', "E'")), MEQ("E'", PUSH("I'", 'G', GT('E"')))))
LABS_CPT = ((LABS_CPQ, (LAB('P0'), LAB('P1'), LAB('Q0'))), ((LAB("E'"), LAB('E"'), LAB('E0')), (LAB('E1'), LAB("D'"))))
IDX_CPT = ((GAMK('I'), GAMK("I'")), ('K =/= I', "I' =/= K"))
TYPS_CPT = (TYPS_CPQ, (LTY('L0'), FTG('F0'), PTG('G')))
INIT_CPT = ('%s = %s' % (PF('0'), UPDT('D', 'I', CC(S1('2'), '( D ` I )'))),
            ('( ( P ` 0 ) ` K ) = %s' % CC(S1('Z0'), 'X0'), 'Z0 e. %s' % GAM, 'X0 e. %s' % WG))
DATA_CPT = ((STKD('D'), INIT_CPT), (('R e. NN0', ('T1 e. NN0', 'T" e. NN0')), ('U e. NN0', "U' e. NN0", 'U" e. NN0')))
CLS_CPT = ((SSS('O'), SSS("O'")), (SSS('N"'), SSS('N0'), SSS("N'")))
IFS_CPT = ((HLD('O', "O'", 'L0'), HPK("O'", 'F0', 'Z0', NF('0'))), ("A. r e. %s ( G ` r ) = Z'" % NF('R'), "Z' e. %s" % GAM))
TREE_CPT = ((PROG_CPT, (LABS_CPT, IDX_CPT, TYPS_CPT)), (DATA_CPT, CLS_CPT), ((FAM_L, HYPS_CPQ, HTF(NF('R'))), (IFS_CPT, (TRIP_CPM, TRIP_CPZ, TRIP_CPD))))
CONCL_CPT = TRI(CLN('P0', 'O', 'D'), CLN("D'", "N'", 'D1_'), '( ( %s + ( ( U + U\' ) + U" ) ) + 5 )' % BND_CPQ)

# ---- mulAllF: P0 pushSym r bra ( push I 2 -> P1 ) ; forEntries x mulAllBody (tm2lfe, body ` dup y t s ; mulC x t r s y ` one triple)
#      -> E popTop x ( pop K F" -> E' ) ; E' [ revList r x s ] (triple) -> E".  Stacks K = x, I = r.
INIT_MLA = '%s = %s' % (PF('0'), UPDT('D', 'I', CC(S1('2'), '( D ` I )')))
TRIP_MLA = HR(CL("E'", "N'", UPDT(PF(NL), 'K', 'R')), 'T', 'M', CL('E"', 'N"', "D'"), 'U')
TREE_MLA = ((T_PHF, (MEQ('P0', PSH('I', '2', 'P1')), MEQ('E', POPL('K', 'F"', "E'")))),
            (((LAB('P0'), LAB("E'"), LAB('E"')), (GAMK('I'), 'K =/= I'), FTG('F"')), ((STKD('D'), INIT_MLA), (SSS("N'"), SSS('N"'), 'U e. NN0'))),
            (HPK(NFIN, 'F"', '2', "N'"), TRIP_MLA))
CONCL_MLA = HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E"', 'N"', "D'"), '( ( ( %s x. ( Y + 2 ) ) + U ) + 4 )' % NL)

# ---- divisorsOfF: P0 [ revList x z s ] (triple, O -> N, D -> D') -> Q0 pushSym a bra ( push J 2 -> Q' ) ;
#      Q' [ pushNum a 1 ] (triple) -> P1 ; forEntries z divBody (tm2lfes, the body one triple per entry, cost ( Y ` j )) -> E ;
#      E popTop z ( pop K F" -> E' ) ; E' [ revList a x s ] (triple) -> E".  Stacks K = z, J = a.
TRIP_DV1 = HR(CL('P0', 'O', 'D'), 'T', 'M', CL('Q0', 'N', "D'"), 'U')
TRIP_DV2 = HR(CL("Q'", 'N', UPDT("D'", 'J', CC(S1('2'), "( D' ` J )"))), 'T', 'M', CL('P1', 'N', PF('0')), "U'")
TRIP_DV3 = HR(CL("E'", "N'", UPDT(PF(NL), 'K', 'R')), 'T', 'M', CL('E"', 'N"', 'D"'), 'U"')
TREE_DVS = ((TREE_FES, (MEQ('Q0', PSH('J', '2', "Q'")), MEQ('E', POPL('K', 'F"', "E'")))),
            (((LAB('P0'), LAB('Q0'), LAB("Q'")), (LAB("E'"), LAB('E"')), (GAMK('J'), FTG('F"'))),
             ((STKD("D'"), (SSS('O'), SSS("N'"), SSS('N"'))), ('U e. NN0', "U' e. NN0", 'U" e. NN0'))),
            (HPK(NFIN, 'F"', '2', "N'"), (TRIP_DV1, TRIP_DV2, TRIP_DV3)))
CONCL_DVS = HR(CL('P0', 'O', 'D'), 'T', 'M', CL('E"', 'N"', 'D"'), '( ( ( U + U\' ) + U" ) + ( %s + 4 ) )' % SUM('j', NL, '( %s + 2 )' % YF('j')))

STATEMENTS += [('tm2fpshf', TREE_PSHF, CONCL_PSHF),
               ('tm2fprl', TREE_PRL, CONCL_PRL), ('tm2fcpb', TREE_CPB, CONCL_CPB), ('tm2fcpq', TREE_CPQ, CONCL_CPQ),
               ('tm2fcpt', TREE_CPT, CONCL_CPT), ('tm2fmla', TREE_MLA, CONCL_MLA), ('tm2fdvs', TREE_DVS, CONCL_DVS)]
NSTMTS += [('tm2lfes1a', ST_FES1A), ('tm2lfes1b', ST_FES1B), ('tm2lfes1', ST_FES1), ('tm2lfes2', ST_FES2), ('tm2lfes3', ST_FES3),
           ('tm2lfes', ST_FES)]

ORDER = ['tm2hitsum', 'tm2floop', 'tm2floopu', 'tm2fpgb', 'tm2fpgq', 'tm2fpg', 'tm2fipt', 'tm2fdot', 'tm2fdo', 'tm2fsg', 'tm2fstd',
         'tplb34', 'tplb37', 'tplb410', 'tplbsuc', 'tplbscale', 'tpl2pow', 'tplpowsuc', 'tplprodle',
         'tm2fpshf', 'tm2lfes1a', 'tm2lfes1b', 'tm2lfes1', 'tm2lfes2', 'tm2lfes3', 'tm2lfes',
         'tm2fprl', 'tm2fcpb', 'tm2fcpq', 'tm2fcpt', 'tm2fmla', 'tm2fdvs']


def allstmts():
    d = dict(NSTMTS)
    d.update({l: statement(t, c) for l, t, c in STATEMENTS})
    assert set(d) == set(ORDER), set(d) ^ set(ORDER)
    return [(l, d[l]) for l in ORDER]


# ------------------------------------------------------------- proof helpers

def brstep(w, ph, ref, phm, meq, al, el, dd, cc, qcl, nss, test, A, E, N, D):
    """tm2lbrt / tm2fbrg: the branch at A on the class N with stacks D, to E"""
    return applylem(w, ph, ref, ((phm, meq), (al, el, dd), ((cc, qcl), (nss, test))), TRI(CLN(A, N, D), CLN(E, N, D), '1'))


def ldstep(w, ph, phm, meq, al, el, dd, lty, nss, n2ss, hld, A, E, N, N2, D):
    """tm2flg: load at A from N into N2 (hld : A. m e. N ( L ` m ) e. N2), stacks D, to E"""
    return applylem(w, ph, 'tm2flg', ((phm, meq), (al, el, dd), (lty, (nss, n2ss), hld)), TRI(CLN(A, N, D), CLN(E, N2, D), '1'))


def fzmem(w, ph, X, xnn, xle, rr, R='R'):
    return w.s([w.s([xnn, rr, xle], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, X, R, X, R)),
                w.inst('elfz2nn0')], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, X, R))


def rmem(w, ph, rr, R='R'):
    """( ph -> R e. ( 0 ... R ) )"""
    rnn = w.s([rr, w.inst('nn0red')], 'syl', '( %s -> %s e. RR )' % (ph, R))
    rle = w.s([rnn, w.inst('leidd')], 'syl', '( %s -> %s <_ %s )' % (ph, R, R))
    return fzmem(w, ph, R, rr, rle, rr, R)


def zmem(w, ph, rr, R='R'):
    """( ph -> 0 e. ( 0 ... R ) )"""
    z0 = w.s([], '0nn0', '0 e. NN0'); z0a = w.s([z0], 'a1i', '( %s -> 0 e. NN0 )' % ph)
    ge0 = w.s([rr, w.inst('nn0ge0')], 'syl', '( %s -> 0 <_ %s )' % (ph, R))
    return fzmem(w, ph, '0', z0a, ge0, rr, R)


def famat(w, ph, fam, X, xfz, Lf=None):
    """the two facts of FAM_L at X: dict(nss=( N ` X ) C_ S, pst=( P ` X ) e. Stk)"""
    st, _ = inst_v(w, ph, fam, '( %s /\\ %s )' % (SSS(NF('i')), STKD(PF('i'))), 'i', X, xfz)
    cx = Ctx(w, ph, (SSS(NF(X)), STKD(PF(X))), root=st)
    return dict(nss=cx[SSS(NF(X))], pst=cx[STKD(PF(X))])


def kfacts(w, pk, R='R'):
    """k e. ( 0 ..^ R ) under pk = ( ph and k e. ( 0 ..^ R ) ): the memberships the iteration needs"""
    kin = w.s([], 'simpr', '( %s -> k e. ( 0 ..^ %s ) )' % (pk, R))
    kfz = w.s([kin, w.inst('elfzofz')], 'syl', '( %s -> k e. ( 0 ... %s ) )' % (pk, R))
    k1fz = w.s([kin, w.inst('fzofzp1')], 'syl', '( %s -> ( k + 1 ) e. ( 0 ... %s ) )' % (pk, R))
    knn = w.s([kin, w.inst('elfzonn0')], 'syl', '( %s -> k e. NN0 )' % pk)
    k1nn = w.s([knn, w.inst('peano2nn0')], 'syl', '( %s -> ( k + 1 ) e. NN0 )' % pk)
    return kin, kfz, k1fz, knn, k1nn


def casesplit(w, ph, disj, DISJ, CASEA, CASEB, proveA, proveB, concl):
    """( ph -> concl ) from disj : ( ph -> ( CASEA \\/ CASEB ) ), proveA(pha, cs) proving ( pha -> concl )
    with pha = ( ph /\\ CASEA ) and cs the step ( pha -> CASEA ); likewise proveB"""
    pha = '( %s /\\ %s )' % (ph, CASEA)
    csa = w.s([], 'simpr', '( %s -> %s )' % (pha, CASEA))
    ta = proveA(pha, csa)
    phb = '( %s /\\ %s )' % (ph, CASEB)
    csb = w.s([], 'simpr', '( %s -> %s )' % (phb, CASEB))
    tb = proveB(phb, csb)
    both = w.s([ta, tb], 'jaodan', '( ( %s /\\ %s ) -> %s )' % (ph, DISJ, concl))
    return w.s([disj, both], 'mpdan', '( %s -> %s )' % (ph, concl))


def bound0(w, ph, phm, tri, C, D, n, m, leaves, hyps=(), qed=False):
    """t5lib.bound with ` 0 <_ X ` supplied for every NN0 leaf (lin.py does not read the closure for signs)"""
    ge = [w.s([st], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, X)) for X, st in leaves.items()]
    return bound(w, ph, phm, tri, C, D, n, m, leaves, hyps=list(hyps) + ge, qed=qed)
