r"""Sortie T9: Step4.lean (extractF and its parts) at the concrete machine.

The installation predicates of ` prodLF ` (PrimList.lean), ` exTest ` , ` exSome ` ,
` exPre ` , ` exBody ` , ` extractGoF ` , ` extractF ` (T7b's encoding: one wff
predicate per fragment, own equations written by hand, callees as predicates),
the handler ` readEmpty ` of ` clear ` , the step operation ` ExStOp ` of the
extraction loop's state sequence and the statements of the runs forms (the
frozen statements of T9-blueprint.md).  Built on tools/t8blib.py (read-only).

Stack letters (Lean's ` Dist8 ` order): np = K , nL = J , snap = I , acc = I' ,
s = I" , t = I0 , nm = K0 , nu = J0 .
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t8blib import *
import t8blib as T8B

K8 = ['K', 'J', 'I', "I'", 'I"', 'I0', 'K0', 'J0']
NP_, NL_, SNAP, ACC, SS_, TT, NM, NU = K8
B1 = '<. 1 , 1o >.'                       # the letter ` bit true `
RDE = 'TMrdEmp'                            # Lean ` readEmpty `
CNDA = CNOT('da')                          # ` fun v => !v.da `
RDBRA = 'TMrdBra'

# ------------------------------------------------------------ the handler readEmpty (Prims.lean)
IFE = 'if ( o = ( inr ` (/) ) , 1o , (/) )'


def EVAL(v, o):
    """the value of ` readEmpty v o ` : ` da := o.isNone ` , the other fields kept"""
    return MK(*([FLD(f, v) for f in ORDER[:3]] + ['if ( %s = ( inr ` (/) ) , 1o , (/) )' % o] +
                [FLD(f, v) for f in ORDER[4:]]))


DF_RDE = '%s = ( v e. TMSt , o e. %s |-> %s )' % (RDE, OPT, EVAL('v', 'o'))

# ------------------------------------------------------------ the installation predicates
# prodLF x w c s t  (K J I I' I")
comp('prl', 'TMIprl', ['K', 'J', 'I', "I'", 'I"'], ['Q1', 'Q2', 'P1', 'A', 'A"', 'Q3'], "E'",
     ((MEQ('Q1', PUSH('J', CONST('4'), GT('Q2'))), MEQ('Q2', PUSH('J', CONST(B1), GT('P1')))),
      (MEQ('P1', PEEK('I', RDBRA, GT('A'))), MEQ('A', BRANCH(CNFL, GT("A'"), GT('Q3')))),
      (MEQ('A"', PEEK('I', RDBRA, GT('A'))), MEQ('Q3', POP('I', PID, GT("E'"))))),
     ((LAB('Q1'), LAB('Q2'), LAB('P1')), (LAB('A'), LAB('A"')), (LAB('Q3'), LAB("E'"))),
     "` prodLF x w c s t = copyList x c s t ; pushNum w 1 ; forEntries c ( prodBody x w c s t ) ; popTop c ` , "
     "` prodBody x w c s t = mulC c w x s t ; moveEntry x w s ` , ` forEntries x body = peekBra x ; "
     "loop ( !flag ) ( body ; peekBra x ) ` , ` pushNum w 1 = pushSym w comma ; pushSym w ( bit true ) `",
     [('lcpy', ['K', 'I', "I'", 'I"'], 'C0', 'Q1'), ('mulc', ['I', 'J', 'K', "I'", 'I"'], "A'", 'X1'),
      ('me', ['K', 'J', "I'"], 'X1', 'A"')])
FRAGS['prl'].start = 'C0'

# exTest np snap s t nm  (K I I" I0 K0)
comp('ext', 'TMIext', [NP_, SNAP, SS_, TT, NM], ['Q1', 'Q2', 'Q3', 'Q4'], 'E',
     ((MEQ('Q1', BRANCH(CLT, GT('Q2'), GT('Q4'))), MEQ('Q2', PUSH(NP_, CONST('3'), GT('Q3')))),
      (MEQ('Q3', LOAD(LFL1, GT('E'))), MEQ('Q4', PEEK(NP_, RDBRA, GT('E'))))),
     ((LAB('Q1'), LAB('Q2')), (LAB('Q3'), LAB('Q4'), LAB('E'))),
     "` exTest np snap s t nm = moveEntry nm snap s ; dup nm t s ; moveEntry snap nm s ; dup nm snap s ; "
     "cmpFrag t snap ; ite ( cmp = lt ) ( pushSym np ket ; load' ( flag := true ) ) ( peekBra np ) `",
     [('me', [NM, SNAP, SS_], 'C0', 'X1'), ('dup', [NM, TT, SS_], 'X1', 'X2'), ('me', [SNAP, NM, SS_], 'X2', 'X3'),
      ('dup', [NM, SNAP, SS_], 'X3', 'X4'), ('cmp', [TT, SNAP], 'X4', 'Q1')])
FRAGS['ext'].start = 'C0'

# exSome np nL snap acc s t nm nu  (K8); ` clear acc ` is the own label Q1 (T4's tm2fclr form)
comp('exs', 'TMIexs', K8, ['Q1'], 'E',
     MEQ('Q1', POP(ACC, RDE, BRANCH(CNDA, GT('Q1'), GT('X4')))),
     (LAB('Q1'), LAB('E')),
     "` exSome np nL snap acc s t nm nu = prodLF snap t np s nu ; mulC nm t s np nu ; moveEntry s nm t ; "
     "appendList snap nu t s ; clear acc ; dup nL t s ; emptyTbl t acc s ; exTest np snap s t nm ` "
     "( ` clear acc ` : one label, ` pop acc readEmpty ` then ` branch ( !da ) ( goto self ) ( goto exit ) ` )",
     [('prl', [SNAP, TT, NP_, SS_, NU], 'C0', 'X1'), ('mulc', [NM, TT, SS_, NP_, NU], 'X1', 'X2'),
      ('me', [SS_, NM, TT], 'X2', 'X3'), ('lapp', [SNAP, NU, SS_, TT], 'X3', 'Q1'),
      ('dup', [NL_, TT, SS_], 'X4', 'X5'), ('etb', [TT, ACC, SS_], 'X5', 'X6'),
      ('ext', [NP_, SNAP, SS_, TT, NM], 'X6', 'E')])
FRAGS['exs'].start = 'C0'

# exPre np nL snap acc s t nu  (K J I I' I" I0 J0)
K7P = [NP_, NL_, SNAP, ACC, SS_, TT, NU]
comp('exp', 'TMIexp', K7P, ['Q1', 'Q2', 'Q3'], 'E',
     ((MEQ('Q1', PUSH(TT, CONST('4'), GT('Q2'))), MEQ('Q2', PUSH(TT, CONST(B1), GT('X2')))),
      MEQ('Q3', PEEK(SNAP, RDK, GT('E')))),
     ((LAB('Q1'), LAB('Q2')), (LAB('Q3'), LAB('E'))),
     "` exPre np nL snap acc s t nu = copyTbl acc snap np s t ; dpStepF np nL snap acc s t ; pushNum t 1 ; "
     "dup nL snap s ; modC t snap np acc s nu ; lookupSlot acc t snap s np ; peekKet snap ` "
     "( ` pushNum t 1 = pushSym t comma ; pushSym t ( bit true ) ` )",
     [('ctb', [ACC, SNAP, NP_, SS_, TT], 'C0', 'X1'), ('dps', [NP_, NL_, SNAP, ACC, SS_, TT], 'X1', 'Q1'),
      ('dup', [NL_, SNAP, SS_], 'X2', 'X3'), ('modc', [TT, SNAP, NP_, ACC, SS_, NU], 'X3', 'X4'),
      ('lks', [ACC, TT, SNAP, SS_, NP_], 'X4', 'Q3')])
FRAGS['exp'].start = 'C0'

# exBody (K8): ` exNone np snap = popTop snap ; peekBra np ` inline (labels Q2 Q3)
comp('exb', 'TMIexb', K8, ['Q1', 'Q2', 'Q3'], 'E',
     (MEQ('Q1', BRANCH('TMfl', GT('Q2'), GT('X1'))),
      (MEQ('Q2', POP(SNAP, PID, GT('Q3'))), MEQ('Q3', PEEK(NP_, RDBRA, GT('E'))))),
     ((LAB('Q1'), LAB('Q2')), (LAB('Q3'), LAB('E'))),
     "` exBody np nL snap acc s t nm nu = exPre np nL snap acc s t nu ; ite flag ( exNone np snap ) "
     "( exSome np nL snap acc s t nm nu ) ` , ` exNone np snap = popTop snap ; peekBra np ` (inline)",
     [('exp', K7P, 'C0', 'Q1'), ('exs', K8, 'X1', 'E')])
FRAGS['exb'].start = 'C0'

# extractGoF (K8)
comp('exg', 'TMIexg', K8, ['Q1', 'Q2', 'Q3', 'Q4', 'Q5', 'Q6'], 'E',
     ((MEQ('Q1', PEEK(NP_, RDBRA, GT('Q2'))), MEQ('Q2', BRANCH(CNFL, GT('B0'), GT('Q3')))),
      (MEQ('Q3', PEEK(NP_, RDK, GT('Q4'))), MEQ('Q4', BRANCH('TMfl', GT('Q5'), GT('Q6')))),
      (MEQ('Q5', POP(NP_, PID, GT('E'))), MEQ('Q6', LOAD(LID, GT('E'))))),
     ((LAB('Q1'), LAB('Q2'), LAB('Q3')), (LAB('Q4'), LAB('Q5')), (LAB('Q6'), LAB('E'))),
     "` extractGoF np nL snap acc s t nm nu = peekBra np ; loop ( !flag ) ( exBody np nL snap acc s t nm nu ) ; "
     "peekKet np ; ite flag ( popTop np ) skip `",
     [('exb', K8, 'B0', 'Q2')])

# extractF (K8)
comp('exf', 'TMIexf', K8, ['Q1', 'Q2', 'Q3'], 'E',
     (MEQ('Q1', PUSH(NM, CONST('4'), GT('Q2'))), MEQ('Q2', PUSH(NM, CONST(B1), GT('Q3'))), MEQ('Q3', PUSH(NU, CONST('2'), GT('X1')))),
     ((LAB('Q1'), LAB('Q2')), (LAB('Q3'), LAB('E'))),
     "` extractF np nL snap acc s t nm nu = pushNum nm 1 ; pushSym nu bra ; dup nL t s ; emptyTbl t acc s ; "
     "extractGoF np nL snap acc s t nm nu ` ( ` pushNum nm 1 = pushSym nm comma ; pushSym nm ( bit true ) ` )",
     [('dup', [NL_, TT, SS_], 'X1', 'X2'), ('etb', [TT, ACC, SS_], 'X2', 'X3'), ('exg', K8, 'X3', 'E')])
PREDS9 = ['prl', 'ext', 'exs', 'exp', 'exb', 'exg', 'exf']


# ============================================================ new definitions (hand-written in the sortie file)
STY = '( NN0 X. ( Word NN0 X. ( Tbl X. 2o ) ) )'          # the state ( m , used , table , hit )
ZM = lambda z: '( 1st ` %s )' % z                        # m
ZU = lambda z: '( 1st ` ( 2nd ` %s ) )' % z              # used
ZA = lambda z: '( 1st ` ( 2nd ` ( 2nd ` %s ) ) )' % z    # table
ZH = lambda z: '( 2nd ` ( 2nd ` ( 2nd ` %s ) ) )' % z    # hit flag
ZT = lambda m, u, a, h: '<. %s , <. %s , <. %s , %s >. >. >.' % (m, u, a, h)
DPS_ = lambda l, p, a: '( ( %s DpStep %s ) ` %s )' % (l, p, a)
DP1 = lambda l, p, a: '( 1st ` %s )' % DPS_(l, p, a)
SLF = lambda l, p, a: '( %s ` ( 1 mod %s ) )' % (DP1(l, p, a), l)
PRL = lambda w_: '( 1st ` ( ProdL ` %s ) )' % w_


def STOPB(l, n, x, p):
    """the value of ` ( x ( l ExStOp n ) p ) ` (df-exstop's body)"""
    a = ZA(x)
    sl = SLF(l, p, a)
    wv = '( 2nd ` %s )' % sl
    mm = '( %s x. %s )' % (ZM(x), PRL(wv))
    return ('if ( %s = ( inr ` (/) ) , %s , %s )'
            % (sl, ZT(ZM(x), ZU(x), DP1(l, p, a), '(/)'),
               ZT(mm, '( %s ++ %s )' % (wv, ZU(x)), 'EmptyTbl', 'if ( %s < %s , 1o , (/) )' % (n, mm))))


DF_EXSTOP = 'ExStOp = ( l e. NN , n e. NN0 |-> ( x e. %s , p e. NN0 |-> %s ) )' % (STY, STOPB('l', 'n', 'x', 'p'))
SQF_ = lambda p, x, l, n: '( k e. NN0 |-> if ( k = 0 , %s , ( %s ` ( k - 1 ) ) ) )' % (x, p)
DF_EXST = ('ExSt = ( l e. NN , n e. NN0 |-> ( p e. Word NN0 , x e. %s |-> seq 0 ( ( l ExStOp n ) , %s ) ) )'
           % (STY, SQF_('p', 'x', 'l', 'n')))
STOPSET = lambda p, sq: '{ i e. ( 0 ... ( # ` %s ) ) | ( i = ( # ` %s ) \\/ %s = 1o ) }' % (p, p, ZH('( %s ` i )' % sq))
DF_EXIT = ('ExIt = ( l e. NN , n e. NN0 |-> ( p e. Word NN0 , x e. %s |-> inf ( %s , RR , < ) ) )'
           % (STY, STOPSET('p', '( p ( l ExSt n ) x )')))
OPX = lambda l, n: '( %s ExStOp %s )' % (l, n)
SQ = lambda w_, l, n, z: '( %s ( %s ExSt %s ) %s )' % (w_, l, n, z)      # the state sequence
RIT = lambda w_, l, n, z: '( %s ( %s ExIt %s ) %s )' % (w_, l, n, z)     # the stop index
EGO = lambda l, n, w_, m, u, a: '( ( ( ( ( %s ExtractGo %s ) ` %s ) ` %s ) ` %s ) ` %s )' % (l, n, w_, m, u, a)

# ============================================================ statement notation
ENCL = lambda v, x: '( ( encList ` %s ) ++ %s )' % (v, x)
ACCW = lambda a: '( ( L encTblAsc %s ) ++ <" 0 "> )' % a
TMBx = lambda b: '( TMB ` %s )' % b
TWO = lambda b: '( 2 ^ %s )' % b
RALB = lambda w_, b='B': 'A. a e. ran %s a < ( 2 ^ %s )' % (w_, b)
NFLi = lambda c: NFL('if ( %s , 1o , (/) )' % c)
WG = lambda x: WRD(x, GAM)
CEN9 = lambda fname, D: CLN(FRAGS[fname].entry(), S, D)


def UPS(D, *pairs):
    for k, v in pairs:
        D = UP(D, k, v)
    return D


# ------------------------------------------------------------ prodLF_le_B  (x w c s t = K J I I' I")
K5P = ['K', 'J', 'I', "I'", 'I"']
DATA_PRL = ((STKD('D'), '( D ` K ) = %s' % ENCL('L', 'R')), ('L e. Word NN0', WG('R')), ('B e. NN0', RALB('L')))
TREE_PRL = TREE(K5P, 'prl', DATA_PRL)
PRLB = '( ( ( 2nd ` ( ProdL ` L ) ) + 1 ) x. ( TMB ` ( ( ( 2 x. ( ( # ` L ) + 1 ) ) x. B ) + 4 ) ) )'
CONCL_PRL = TRI(CEN9('prl', 'D'), CE(UP('D', 'J', EWg(PRL('L'), '( D ` J )'))), PRLB)

# ------------------------------------------------------------ exTest_runs  (np snap s t nm = K I I" I0 K0)
K5T = [NP_, SNAP, SS_, TT, NM]
DATA_EXT = ((STKD('D'), ('F e. NN0', 'G e. NN0', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )')),
            ('S e. Word NN0', WG('X'), WG('Y')),
            ('( D ` K ) = %s' % ENCL('S', 'X'), '( D ` K0 ) = %s' % EWg('F', EWg('G', 'Y'))))
TREE_EXT = TREE(K5T, 'ext', DATA_EXT)
EXTC = '( ( 5 x. ( TMB ` N ) ) + 3 )'
CONCL_EXT = TRI(CEN9('ext', 'D'),
                CLN('E', NFLi('( G < F \\/ S = (/) )'),
                    UP('D', 'K', 'if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) )')), EXTC)

# ------------------------------------------------------------ exSome_runs  (K8)
PRW = PRL('W')
FPW = '( F x. %s )' % PRW
DATA_EXS = (((STKD('D'), ('L e. NN0', 'B e. NN0', 'L < ( 2 ^ B )'), ('A e. Tbl', 'N e. NN0', TBB('A'))),
             (('W e. Word NN0', RALB('W')), ('F e. NN0', 'G e. NN0', 'H e. NN0'),
              (('F < ( 2 ^ H )', 'G < ( 2 ^ H )'), ('%s < ( 2 ^ H )' % PRW, '%s < ( 2 ^ H )' % FPW)))),
            (('S e. Word NN0', 'U e. Word NN0'), ((WG('X'), WG("X'")), (WG('Z'), WG('Y'), WG('R'))),
             (('( D ` K ) = %s' % ENCL('S', 'X'), '( D ` J ) = %s' % EWg('L', "X'"), '( D ` I ) = %s' % ENCL('W', 'Z')),
              ("( D ` I' ) = %s" % ACCW('A'), '( D ` K0 ) = %s' % EWg('F', EWg('G', 'Y')), '( D ` J0 ) = %s' % ENCL('U', 'R')))))
TREE_EXS = TREE(K8, 'exs', DATA_EXS)
HITW = 'G < %s' % FPW
DFIN_EXS = UPS('D', ('K', 'if ( %s , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) )' % HITW), ('I', 'Z'),
               ("I'", ACCW('EmptyTbl')), ('K0', EWg(FPW, EWg('G', 'Y'))), ('J0', ENCL('( W ++ U )', 'R')))


def LSUM(*ts):
    """left-associated sum ( ( t1 + t2 ) + t3 ) ... (Lean's ` a + b + c ` )"""
    acc = ts[0]
    for t in ts[1:]:
        acc = '( %s + %s )' % (acc, t)
    return acc


def EXSOMEC(l, n, b, sl, bm):
    """Lean ` exSomeC L N' b sl bM ` """
    tb, tm = '( TMB ` %s )' % b, '( TMB ` %s )' % bm
    return LSUM('( ( %s + 1 ) x. ( TMB ` ( ( ( 2 x. ( %s + 1 ) ) x. %s ) + 4 ) ) )' % (sl, sl, b), tm, tm,
                '( ( %s + 1 ) x. %s )' % (sl, tb), '( ( %s x. ( ( %s x. ( %s + 1 ) ) + 1 ) ) + 2 )' % (l, n, b), tb,
                '( ( %s + 1 ) x. %s )' % (l, tb), '( ( 5 x. %s ) + 3 )' % tm)


def EXPREC(l, n, b):
    """Lean ` exPreC L N b ` """
    tb = '( TMB ` %s )' % b
    return LSUM('( ( ( %s + 1 ) x. ( %s + 2 ) ) x. %s )' % (l, n, tb), '( ( ( ( %s + 1 ) ^ 2 ) x. ( %s + 2 ) ) x. %s )' % (l, n, tb),
                tb, tb, tb, '( ( ( %s + 1 ) x. ( ( %s + 1 ) + 2 ) ) x. %s )' % (l, n, tb), '1')


CONCL_EXS = TRI(CEN9('exs', 'D'), CLN('E', NFLi('( %s \\/ S = (/) )' % HITW), DFIN_EXS),
                EXSOMEC('L', 'N', 'B', '( # ` W )', 'H'))

# ------------------------------------------------------------ exPre_runs  (np nL snap acc s t nu)
DATA_EXP = ((STKD('D'), ('F e. NN0', 'L e. NN', 'A e. Tbl'), ('N e. NN0', 'B e. NN0')),
            ((WG('X'), WG('Y')), ('( D ` K ) = %s' % EWg('F', 'X'), '( D ` J ) = %s' % EWg('L', 'Y'), "( D ` I' ) = %s" % ACCW('A'))),
            (('F < ( 2 ^ B )', 'L < ( 2 ^ B )'), TBB('A')))
TREE_EXP = TREE(K7P, 'exp', DATA_EXP)
SLP = SLF('L', 'F', 'A')
DFIN_EXP = UPS('D', ('K', 'X'), ('I', '( ( encSlot ` %s ) ++ ( D ` I ) )' % SLP), ("I'", ACCW(DP1('L', 'F', 'A'))))
CONCL_EXP = TRI(CEN9('exp', 'D'), CLN('E', NFLi('%s = ( inr ` (/) )' % SLP), DFIN_EXP), EXPREC('L', 'N', 'B'))

# ------------------------------------------------------------ exBody_runs  (K8), both cases through ExStOp
ZP = '( Z %s F )' % OPX('L', 'G')                       # the next state
EXC = lambda l, h, q: '( ; 2 0 x. ( ( ( ( %s + 1 ) ^ 2 ) x. ( %s + 2 ) ) x. ( TMB ` %s ) ) )' % (l, h, q)
DATA_EXB = (((STKD('D'), ('L e. NN', 'Z e. %s' % STY, 'F e. NN0')), ('G e. NN0', 'S e. Word NN0'),
             ((WG('X'), WG("X'")), (WG('Y'), WG('R')))),
            (('( D ` K ) = %s' % EWg('F', ENCL('S', 'X')), '( D ` J ) = %s' % EWg('L', "X'"), "( D ` I' ) = %s" % ACCW(ZA('Z'))),
             ('( D ` K0 ) = %s' % EWg(ZM('Z'), EWg('G', 'Y')), '( D ` J0 ) = %s' % ENCL(ZU('Z'), 'R'))),
            ((('N e. NN0', 'B e. NN0', 'H e. NN0'), ('C e. NN0', 'O e. NN0', 'Q e. NN0')),
             ((TBB(ZA('Z')), 'F < ( 2 ^ B )', 'L < ( 2 ^ B )'), ('( N + 1 ) <_ H', 'B <_ Q')),
             (('%s < ( 2 ^ C )' % ZM('Z'), '1 <_ C', '( C + ( B x. ( N + 1 ) ) ) <_ O'),
              ('G < ( 2 ^ O )', 'O <_ Q', '( ( ( 2 x. ( H + 2 ) ) x. B ) + 4 ) <_ Q'))))
TREE_EXB = TREE(K8, 'exb', DATA_EXB)
NPREST = ENCL('S', 'X')
DFIN_EXB = UPS('D', ('K', 'if ( %s = 1o , ( <" 3 "> ++ %s ) , %s )' % (ZH(ZP), NPREST, NPREST)), ("I'", ACCW(ZA(ZP))),
               ('K0', EWg(ZM(ZP), EWg('G', 'Y'))), ('J0', ENCL(ZU(ZP), 'R')))
CONCL_EXB = TRI(CEN9('exb', 'D'), CLN('E', NFLi('( S = (/) \\/ %s = 1o )' % ZH(ZP)), DFIN_EXB), EXC('L', 'H', 'Q'))

# ------------------------------------------------------------ extractGoF_runs (K8)
Z0G = ZT('F', 'U', 'A', '(/)')
SQG = SQ('W', 'L', 'G', Z0G)
RG = RIT('W', 'L', 'G', Z0G)
FING = '( %s ` %s )' % (SQG, RG)
EGG = EGO('L', 'G', 'W', 'F', 'U', 'A')
DATA_EXG = (((STKD('D'), ('L e. NN', 'G e. NN0', 'W e. Word NN0'), ('F e. NN0', 'U e. Word NN0', 'A e. Tbl')),
             ((WG('X'), WG("X'")), (WG('Y'), WG('R')))),
            (('( D ` K ) = %s' % ENCL('W', 'X'), '( D ` J ) = %s' % EWg('L', "X'"), "( D ` I' ) = %s" % ACCW('A')),
             ('( D ` K0 ) = %s' % EWg('F', EWg('G', 'Y')), '( D ` J0 ) = %s' % ENCL('U', 'R'))),
            ((('N e. NN0', 'B e. NN0', 'H e. NN0'), ('C e. NN0', 'O e. NN0', 'Q e. NN0')),
             ((TBB('A'), RALB('W'), 'L < ( 2 ^ B )'), ('( N + ( # ` W ) ) <_ H', 'B <_ Q')),
             (('F < ( 2 ^ C )', '1 <_ C', '( C + ( B x. ( N + ( # ` W ) ) ) ) <_ O'),
              ('G < ( 2 ^ O )', 'O <_ Q', '( ( ( 2 x. ( H + 2 ) ) x. B ) + 4 ) <_ Q'))))
TREE_EXG = TREE(K8, 'exg', DATA_EXG)
DFIN_EXG = UPS('D', ('K', ENCL('( W substr <. %s , ( # ` W ) >. )' % RG, 'X')), ("I'", ACCW(ZA(FING))),
               ('K0', EWg(ZM(FING), EWg('G', 'Y'))), ('J0', ENCL(ZU(FING), 'R')))
EXGB = '( ( ( 2nd ` %s ) + 1 ) x. ( %s + 5 ) )' % (EGG, EXC('L', 'H', 'Q'))
CONCL_EXG = TRI(CEN9('exg', 'D'), CLN('E', NFL('if ( ( 1st ` %s ) = ( inr ` (/) ) , (/) , 1o )' % EGG), DFIN_EXG), EXGB)

# ------------------------------------------------------------ extractF_le_B (K8)
Z0F = ZT('1', '(/)', 'EmptyTbl', '(/)')
SQF = SQ('W', 'L', 'G', Z0F)
RF = RIT('W', 'L', 'G', Z0F)
FINF = '( %s ` %s )' % (SQF, RF)
EXT_ = '( ( L Extract G ) ` W )'
DATA_EXF = ((STKD('D'), ('L e. NN', 'G e. NN0', 'W e. Word NN0'), ('B e. NN0', 'L < ( 2 ^ B )', 'G < ( 2 ^ B )')),
            (RALB('W'), (WG('X'), WG("X'"), WG('Y'))),
            (('( D ` K ) = %s' % ENCL('W', 'X'), '( D ` J ) = %s' % EWg('L', "X'")),
             ("( D ` I' ) = (/)", '( D ` K0 ) = %s' % EWg('G', 'Y'))))
TREE_EXF = TREE(K8, 'exf', DATA_EXF)
DFIN_EXF = UPS('D', ('K', ENCL('( W substr <. %s , ( # ` W ) >. )' % RF, 'X')), ("I'", ACCW(ZA(FINF))),
               ('K0', EWg(ZM(FINF), EWg('G', 'Y'))), ('J0', ENCL(ZU(FINF), '( D ` J0 )')))
EXX = '( ( ( 3 x. ( # ` W ) ) x. B ) + ( ( 5 x. B ) + 5 ) )'
EXFB = ('( ( ( 2nd ` %s ) + 1 ) x. ( ; 2 5 x. ( ( ( ( L + 1 ) ^ 2 ) x. ( ( # ` W ) + 2 ) ) x. ( TMB ` %s ) ) ) )'
        % (EXT_, EXX))
CONCL_EXF = TRI(CEN9('exf', 'D'), CLN('E', NFL('if ( ( 1st ` %s ) = ( inr ` (/) ) , (/) , 1o )' % EXT_), DFIN_EXF), EXFB)

STMTS9 = {}
for _n in PREDS9:
    STMTS9['tmi%su' % _n] = unfold_stmt(FRAGS[_n])
for _l, _t, _c in [('tmiprlb', TREE_PRL, CONCL_PRL), ('tmiext', TREE_EXT, CONCL_EXT), ('tmiexs', TREE_EXS, CONCL_EXS),
                   ('tmiexp', TREE_EXP, CONCL_EXP), ('tmiexb', TREE_EXB, CONCL_EXB), ('tmiexg', TREE_EXG, CONCL_EXG),
                   ('tmiexfb', TREE_EXF, CONCL_EXF)]:
    STMTS9[_l] = '( %s -> %s )' % (cj(_t), _c)
ORDER9 = ['tmi%su' % n for n in PREDS9] + ['tmiprlb', 'tmiext', 'tmiexs', 'tmiexp', 'tmiexb', 'tmiexg', 'tmiexfb']


def allstmts9():
    return [(l, STMTS9[l]) for l in ORDER9 if l in STMTS9]


# ============================================================ proof helpers
import t8alib as A8
from t7lib import mval, ifex_closed, not1o, lamval
from t7_e_cmp import lamty
A8.HANDLERS[RDBRA] = '2'          # readBra: flag := decide ( o = some bra ) , its class lemma ~ tmcrdbrac
A8.HLAB[RDBRA] = 'bra'
CMPC = lambda a, b: '{ h e. TMSt | ( TMcmp ` h ) = ( %s Ncmp %s ) }' % (a, b)


def Lft(w, pc, ph, st):
    """( pc -> X ) from st : ( ph -> X ), pc = ( ph /\\ ... )"""
    return w.s([st], 'adantr', '( %s -> %s )' % (pc, concl(w, ph, st)))


class Base:
    """the facts of a runs-form theorem: Ctx, machine, ne, the predicate unfolded (callees one level), the
    stack values of D (the antecedent's equations where given, selfval otherwise)"""
    def __init__(self, w, ph, T, ks, fname, eqs=None):
        self.w, self.ph, self.ks = w, ph, ks
        c, mk, ne, ex = hsetup(w, ph, T, ks, fname)
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        self.dd = c[STKD('D')]
        vals = {k: selfval(w, ph, mk, 'D', self.dd, k) for k in ks}
        self.gam = {v[0]: v[2] for v in vals.values()}
        for k, (txt, gst) in (eqs or {}).items():
            vals[k] = (txt, c['( D ` %s ) = %s' % (k, txt)], gst)
            self.gam[txt] = gst
        self.S0 = Stacks(w, ph, mk, 'D', self.dd, ne, vals)

    def g(self, txt, st):
        self.gam[txt] = st
        return st

    def deep(self, fname, j):
        """unfold the callee at slot j of the fragment fname fully (its entry label's typing and equations)"""
        f = FRAGS[fname]
        lm = f.lmap()
        fn, cks, en, exn = f.children[j]
        P_ = PL('P', f.slot(j))
        pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
        self.ex.update(unfold_all(self.w, self.ph, self.ex[pr], fn, cks, P_, lm[exn], rec=True))

    def run(self, S=None):
        return Run(self.w, self.ph, self.mk, S or self.S0, self.ex, self.c)

    def call(self, R, label, m, extra, updates, **kw):
        """R.call with the Gamma'-typings of every known word available as leaves"""
        ex = {WG(t): st for t, st in self.gam.items() if st is not None}
        for k, v in R.S.vals.items():
            ex['( %s ` %s ) = %s' % (R.S.D, k, v[0])] = v[1]
        ex.update(extra)
        return R.call(label, m, ex, updates, **kw)

    def ss(self, N):
        """( ph -> N C_ ( 2nd ` T ) ) for a class { h e. TMSt | ... }"""
        w, ph = self.w, self.ph
        a = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % N)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, N))
        return w.s([a, self.mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, N, S))


def encw(w, ph, t, tn):
    return w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` %s ) e. Word Gamma' )" % (ph, t))


def ewg_(w, ph, t, tn, X, xg):
    """( ph -> EW( t , X ) e. Word Gamma' )"""
    return wgcat(w, ph, '( encNatGam ` %s )' % t, '( <" 4 "> ++ %s )' % X, encw(w, ph, t, tn), wg4(w, ph, X, xg))


def enclg(w, ph, V, vw, X, xg):
    """( ph -> ( ( encList ` V ) ++ X ) e. Word Gamma' )"""
    e = w.s([vw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, V))
    return wgcat(w, ph, '( encList ` %s )' % V, X, e, xg)


def engb(w, ph, t, tn):
    """( ph -> ( encNatGam ` t ) e. Word BITS )"""
    ev = w.s([tn, w.inst('encnatgamval')], 'syl', '( %s -> ( encNatGam ` %s ) = ( inclBool o. ( encodeNat ` %s ) ) )' % (ph, t, t))
    ec = w.s([tn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` %s ) e. Word 2o )' % (ph, t))
    ib = w.s([ec, w.inst('tmcibw')], 'syl', '( %s -> ( inclBool o. ( encodeNat ` %s ) ) e. Word %s )' % (ph, t, BITS))
    return w.s([ev, ib], 'eqeltrd', '( %s -> ( encNatGam ` %s ) e. Word %s )' % (ph, t, BITS))


def encl_ne0(w, ph, V, vw, X, xg):
    """( ph -> ( ( encList ` V ) ++ X ) =/= (/) ) (a list word ends with bra)"""
    s = w.s
    G = '( encNatGam o. %s )' % V
    gw = s([vw, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (ph, G, BITS))
    le = s([vw, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` %s ) = ( encListB ` %s ) )' % (ph, V, G))
    lb = s([gw, w.inst('tm2lencbval')], 'syl', '( %s -> ( encListB ` %s ) = ( ( entries ` %s ) ++ <" 2 "> ) )' % (ph, G, G))
    et = s([gw, w.inst('tm2lentcl')], 'syl', "( %s -> ( entries ` %s ) e. Word Gamma' )" % (ph, G))
    n1 = s([et, w.inst('ccatws1n0')], 'syl', '( %s -> ( ( entries ` %s ) ++ <" 2 "> ) =/= (/) )' % (ph, G))
    e2 = s([le, lb], 'eqtrd', '( %s -> ( encList ` %s ) = ( ( entries ` %s ) ++ <" 2 "> ) )' % (ph, V, G))
    n2 = s([e2, n1], 'eqnetrd', '( %s -> ( encList ` %s ) =/= (/) )' % (ph, V))
    enl = s([vw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, V))
    W_ = ENCL(V, X)
    c0 = s([enl, xg, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( ( encList ` %s ) = (/) /\\ %s = (/) ) ) )' % (ph, W_, V, X))
    n3 = s([s([s([n2], 'neneqd', '( %s -> -. ( encList ` %s ) = (/) )' % (ph, V))], 'intnanrd',
              '( %s -> -. ( ( encList ` %s ) = (/) /\\ %s = (/) ) )' % (ph, V, X)), c0], 'mtbird' if False else 'mtbird', '') if False else None
    n3 = s([c0, s([s([n2], 'neneqd', '( %s -> -. ( encList ` %s ) = (/) )' % (ph, V))], 'intnanrd',
                  '( %s -> -. ( ( encList ` %s ) = (/) /\\ %s = (/) ) )' % (ph, V, X))], 'mtbird', '( %s -> -. %s = (/) )' % (ph, W_))
    return s([n3], 'neqned', '( %s -> %s =/= (/) )' % (ph, W_))


def fam_at(w, ph, mk, ne, fam_eq, PV, binder, dom, PBf, t, tmem, St):
    """the stack family value at t: fam_eq : ( ph -> PV = ( binder e. dom |-> PBf( binder ) ) ), St the Stacks of PBf( t )
    (its D text is PBf( t )).  Returns (pv : ( ph -> ( PV ` t ) = PBf( t ) ), Stacks at ( PV ` t ))"""
    s = w.s
    F = '( %s e. %s |-> %s )' % (binder, dom, PBf(binder))
    assert St.D == PBf(t), (St.D, PBf(t))
    xex = s([St.memb], 'elexd', '( %s -> %s e. _V )' % (ph, PBf(t)))
    v0 = mval(w, ph, binder, dom, PBf, t, tmem, xex)
    pe = s([fam_eq], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, PV, t, F, t))
    pv = s([pe, v0], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, PV, t, PBf(t)))
    PT = '( %s ` %s )' % (PV, t)
    mem = s([pv, St.memb], 'eqeltrd', '( %s -> %s e. ( TM2Stk ` T ) )' % (ph, PT))
    out = {}
    for k, (txt, st, g) in St.vals.items():
        e = s([pv], 'fveq1d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, PT, k, St.D, k))
        out[k] = (txt, s([e, st], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, PT, k, txt)), g)
    return pv, Stacks(w, ph, mk, PT, mem, ne, out)


def renorm(w, ph, B, R, base_chain, order, PT=None, pv=None):
    """normalize a Run relative to D: the Run's stacks are chain_text( PT , out ) with PT = chain_text( D , base_chain )
    (or PT given with pv : ( ph -> PT = chain_text( D , base_chain ) )).  Returns (step ( ph -> cur_stacks = normal ),
    normal text, normal chain)"""
    cur, out = R.normalize(order)
    Dcur = chain_text(R.S0.D, out)
    chi = list(base_chain) + out
    nst, out2 = stk_normalize(w, ph, B.mk, 'D', B.dd, B.ne, chi, B.gam, order)
    full = chain_text('D', chi)
    if pv is not None:
        r1, x1 = w.rewrite(Dcur, {PT: (chain_text('D', base_chain), pv)}, ph)
        assert x1 == full, (x1, full)
        e = r1 if nst is None else w.s([r1, nst], 'eqtrd', '( %s -> %s = %s )' % (ph, Dcur, chain_text('D', out2)))
    else:
        assert Dcur == full, (Dcur, full)
        e = nst if nst is not None else w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, Dcur, Dcur))
    return e, chain_text('D', out2), out2


def tblw(w, ph, A, an, L, ln):
    """( ph -> ( L encTblAsc A ) e. Word Gamma' ) from an : A e. Tbl, ln : L e. NN0"""
    s = w.s
    j = s([an, ln], 'jca', '( %s -> ( %s e. Tbl /\\ %s e. NN0 ) )' % (ph, A, L))
    RS = '( %s |` ( 0 ..^ %s ) )' % (A, L)
    b = s([j, w.inst('tttbles')], 'syl', '( %s -> ( ( %s encTblAsc %s ) = ( encSlots ` %s ) /\\ ( %s encTblDesc %s ) = ( encSlots ` ( reverse ` %s ) ) ) )'
          % (ph, L, A, RS, L, A, RS))
    e = s([b], 'simpld', '( %s -> ( %s encTblAsc %s ) = ( encSlots ` %s ) )' % (ph, L, A, RS))
    tw = s([s([j, w.inst('tttblw')], 'syl', '( %s -> ( %s e. Word ( Word NN0 |_| 1o ) /\\ ( # ` %s ) = %s ) )' % (ph, RS, RS, L))],
           'simpld', '( %s -> %s e. Word ( Word NN0 |_| 1o ) )' % (ph, RS))
    es = s([tw, w.inst('ttsescl')], 'syl', "( %s -> ( encSlots ` %s ) e. Word Gamma' )" % (ph, RS))
    return s([e, es], 'eqeltrd', "( %s -> ( %s encTblAsc %s ) e. Word Gamma' )" % (ph, L, A))


def accw_g(w, ph, A, an, L, ln):
    """( ph -> ( ( L encTblAsc A ) ++ <" 0 "> ) e. Word Gamma' )"""
    s0 = w.s([closed(w, ph, 'gamma0', "0 e. Gamma'")], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph)
    return wgcat(w, ph, '( %s encTblAsc %s )' % (L, A), '<" 0 ">', tblw(w, ph, A, an, L, ln), s0)


def triple_D(Dcls):
    """the stack term of a class text C( A , N , D )"""
    tail = Dcls.rsplit(' X. { ', 1)[1]
    assert tail.endswith(' } ) )')
    return tail[:-len(' } ) )')]


def qed_as(w, st, formula):
    """the qed line proving formula from the step st that proves it"""
    w.qed([st, w.inst('biid')], 'mpbi', formula)


def tup_comps(w, ph, Zt, zeq, m, u, a, h, vex):
    """from zeq : ( ph -> Zt = <. m , <. u , <. a , h >. >. >. ) and vex[x] : ( ph -> x e. _V ) for m u a h: steps
    ( ph -> ZM( Zt ) = m ) etc. as a dict 'm' 'u' 'a' 'h'"""
    s = w.s
    T3 = '<. %s , %s >.' % (a, h)
    T2 = '<. %s , %s >.' % (u, T3)
    T1 = '<. %s , %s >.' % (m, T2)
    t3v = s([], 'opex', '%s e. _V' % T3)
    t3a = s([t3v], 'a1i', '( %s -> %s e. _V )' % (ph, T3))
    t2v = s([s([], 'opex', '%s e. _V' % T2)], 'a1i', '( %s -> %s e. _V )' % (ph, T2))
    out = {}
    f1 = s([zeq], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph, Zt, T1))
    out['m'] = s([f1, s([vex['m'], t2v, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (ph, T1, m))], 'eqtrd',
                 '( %s -> %s = %s )' % (ph, ZM(Zt), m))
    s2 = s([s([zeq], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (ph, Zt, T1)),
            s([vex['m'], t2v, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (ph, T1, T2))], 'eqtrd',
           '( %s -> ( 2nd ` %s ) = %s )' % (ph, Zt, T2))
    out['u'] = s([s([s2], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (ph, ZU(Zt), T2)),
                  s([vex['u'], t3a, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (ph, T2, u))], 'eqtrd',
                 '( %s -> %s = %s )' % (ph, ZU(Zt), u))
    s3 = s([s([s2], 'fveq2d', '( %s -> ( 2nd ` ( 2nd ` %s ) ) = ( 2nd ` %s ) )' % (ph, Zt, T2)),
            s([vex['u'], t3a, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (ph, T2, T3))], 'eqtrd',
           '( %s -> ( 2nd ` ( 2nd ` %s ) ) = %s )' % (ph, Zt, T3))
    out['a'] = s([s([s3], 'fveq2d', '( %s -> %s = ( 1st ` %s ) )' % (ph, ZA(Zt), T3)),
                  s([vex['a'], vex['h'], w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = %s )' % (ph, T3, a))], 'eqtrd',
                 '( %s -> %s = %s )' % (ph, ZA(Zt), a))
    out['h'] = s([s([s3], 'fveq2d', '( %s -> %s = ( 2nd ` %s ) )' % (ph, ZH(Zt), T3)),
                  s([vex['a'], vex['h'], w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (ph, T3, h))], 'eqtrd',
                 '( %s -> %s = %s )' % (ph, ZH(Zt), h))
    return out


def vex_(w, ph, x):
    """( ph -> x e. _V ) for a class expression headed by ` or an operation, or a constant"""
    s = w.s
    toks = x.split()
    if x in ('(/)',):
        return s([s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % ph)
    if x == '1o':
        return s([s([], '1oex', '1o e. _V')], 'a1i', '( %s -> 1o e. _V )' % ph)
    if x == 'EmptyTbl':
        return s([closed(w, ph, 'emptytblcl', 'EmptyTbl e. Tbl')], 'elexd', '( %s -> EmptyTbl e. _V )' % ph)
    if toks[0] == 'if':
        raise ValueError('if: give the step')
    if toks[0] == '(' and toks[-1] == ')' and len(toks) > 3:
        # ( f ` a ) or ( a F b )
        inner = toks[1:-1]
        d = 0
        for t in inner:
            if t in ('(', '<.', '{', '<"'):
                d += 1
            elif t in (')', '>.', '}', '">'):
                d -= 1
            elif d == 0 and t == '`':
                return s([s([], 'fvex', '%s e. _V' % x)], 'a1i', '( %s -> %s e. _V )' % (ph, x))
        return s([s([], 'ovex', '%s e. _V' % x)], 'a1i', '( %s -> %s e. _V )' % (ph, x))
    raise ValueError(x)


# lin.py names the steps of its power expansion p1, p2, ... with a fresh counter per call: two expansions in one
# worksheet collide ("Duplicate Step number").  Give every such generator a prefix of its own (runtime patch; the
# shared module is not edited).
import congr as _congr
if not getattr(_congr.StepGen, '_t9', False):
    _SG0 = _congr.StepGen

    class _SG(_SG0):
        _t9 = True
        _cnt = [0]

        def __init__(self, prefix='c'):
            if prefix == 'p':
                _SG._cnt[0] += 1
                prefix = 'p%dq' % _SG._cnt[0]
            _SG0.__init__(self, prefix)
    _congr.StepGen = _SG
