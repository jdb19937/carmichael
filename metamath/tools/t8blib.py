r"""Sortie T8b: the concrete Table, part 2 (TM/Table.lean at the machine).

The installation predicates of ` setIfNoneF ` , ` lookupSlot ` , ` copyTbl ` ,
` moveEntry ` , ` resStep ` , ` dpBodyF ` , ` dpStepF ` (T7b's encoding: one wff
predicate per fragment, own equations read from the TTAB generic with the
concrete handlers, callees as predicates), and the statements of their runs
forms (the frozen statements of T8b-blueprint.md section 4: ` STMTS ` ).
Built on tools/t8alib.py (read-only).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t8alib import *
import t8alib as A8

K5 = ['K', 'J', 'I', "I'", 'I"']
K6 = ['K', 'J', 'I', "I'", 'I"', 'I0']


def register2(name, const, generic, ks, order, exit, hmap, children, lean, extra=(), start=None):
    """t8alib.register with extra own equations (text with generic label names) and a start callee"""
    eqs = own_eqs(generic, hmap, [l for l in order if l not in dict(extra)])
    byl = {e.split()[3]: e for e in eqs}
    byl.update(dict(extra))
    prog = grp([byl[l] for l in order])
    labt = grp([LAB(l) for l in order] + [LAB(exit)])
    f = comp(name, const, ks, order, exit, prog, labt, lean, children)
    if start is not None:
        f.start = start
    return f


# setIfNoneF tbl j w s scr  (K J I I' I")
register2('sin', 'TMIsin', 'tm2fsin', K5, ['Q0', "B'", 'B"'], 'E', {'F': RDK, 'C': 'TMfl', "F'": PID},
          [('wdn', ['K', 'J', "I'", 'I"'], 'P0', 'Q0'), ('mvs', ['I', 'K', "I'", 'J'], 'B1_', "A'"),
           ('dpl', ['I'], 'E0', "A'"), ('wup', ['K', 'J', "I'", 'I"'], "A'", 'E')],
          "` setIfNoneF tbl j w s scr = walkDown tbl j s scr ; peekKet tbl ; "
          "ite flag ( popTop tbl ; moveSlot w tbl s j ) ( dropList w ) ; walkUp tbl j s scr `",
          start='P0')
# lookupSlot tbl j w s scr  (K J I I' I")
register2('lks', 'TMIlks', 'tm2flks', K5, ['Q0', "B'", 'B"'], 'E', {'F': RDK, 'C': 'TMfl', 'J': 'I', 'Y': KET},
          [('wdn', ['K', 'J', "I'", 'I"'], 'P0', 'Q0'), ('lcpy', ['K', 'I', "I'", 'J'], 'E0', "A'"),
           ('wup', ['K', 'J', "I'", 'I"'], "A'", 'E')],
          "` lookupSlot tbl j w s scr = walkDown tbl j s scr ; peekKet tbl ; "
          "ite flag ( pushSym w ket ) ( copyList tbl w s j ) ; walkUp tbl j s scr `",
          start='P0')
# copyTbl src dst hold s s'  (K J I I' I")
register2('ctb', 'TMIctb', 'tm2fctb', K5, ['P0', 'P1', 'Q0', 'A', "B'"], "E'", {'F': RDBL, 'C0': CNFL, 'Y': BLANK},
          [('cps', ['K', 'J', "I'", 'I"'], 'B0', 'X1'), ('mvs', ['K', 'I', "I'", 'I"'], 'X1', "B'"),
           ('wup', ['K', 'I"', "I'", 'I'], 'E', "E'")],
          "` copyTbl src dst hold s s' = pushSym dst blank ; pushSym hold blank ; "
          "forSlots src ( copySlot src dst s s' ; moveSlot src hold s s' ) ; walkUp src s' s hold `")
# moveEntry src dst s  (K J I): a leaf, T6's tm2lme at readA / isSome / bit push (a runtime entry of
# t7c_h_lst's handler table; the module file is not edited)
H.HMX['tm2lme'] = {'F': 'TMrdA', 'C': CIS, 'P': PBR}
H.register('me', 'TMIme', 'tm2lme', ['K', 'J', 'I'], ['A', "A'", 'A"', "E'"], [],
           "` moveEntry src dst s = pushSym s comma ; moveNum src s ; pushSym dst comma ; moveNum s dst ` "
           "(the two ` moveNum ` loops inline)")
# resStep nL np s t  (K J I I')
CLT_ = '( u e. TMSt |-> if ( ( TMcmp ` u ) = (/) , 1o , (/) ) )'
register2('rst', 'TMIrst', 'tm2frst', ['K', 'J', 'I', "I'"], ["B'"], 'E', {'C': CLT_},
          [('me', ['K', 'J', 'I'], 'P0', 'X1'), ('dup', ['J', "I'", 'I'], 'X1', 'X2'), ('dup', ['K', 'I', "I'"], 'X2', 'X3'),
           ('cmp', ["I'", 'I'], 'X3', "B'"),
           ('dup', ['K', "I'", 'I'], 'E0', 'Y1'), ('sub', ["I'", 'J', 'I'], 'Y1', 'Y2'), ('me', ['K', 'J', 'I'], 'Y2', 'Y3'),
           ('dup', ['K', 'I', "I'"], 'Y3', 'Y4'), ('sub', ['I', "I'", 'J'], 'Y4', 'Y5'), ('me', ['J', 'K', "I'"], 'Y5', 'Y6'),
           ('me', ['I', 'J', "I'"], 'Y6', 'A'),
           ('dup', ['K', "I'", 'I'], 'E1', 'Z1'), ('sub', ['J', "I'", 'I'], 'Z1', 'A'),
           ('me', ['J', 'K', 'I'], 'A', 'E')],
          "` resStep nL np s t = moveEntry nL np s ; dup np t s ; dup nL s t ; cmpFrag t s ; "
          "ite ( cmp = lt ) ( dup nL t s ; sub t np s t ; moveEntry nL np s ; dup nL s t ; sub s t np s ; "
          "moveEntry np nL t ; moveEntry s np t ) ( dup nL t s ; sub np t s np ) ; moveEntry np nL s `",
          start='P0')
# dpBodyF np nL snap acc s t  (K J I I' I" I0)
register2('dpb', 'TMIdpb', 'tm2fdpb', K6, ['Q0', "B'", 'B"'], 'A', {'K': 'I', 'F': RDK, 'C': 'TMfl', "F'": PID},
          [('rst', ['J', 'K', 'I"', 'I0'], 'P0', 'Q0'), ('dup', ['K', 'I', 'I"'], 'E0', 'W1'),
           ('dup', ['J', 'K', 'I"'], 'W1', 'W2'), ('sin', ["I'", 'K', 'I', 'I"', 'I0'], 'W2', 'A')],
          "` dpBodyF np nL snap acc s t = resStep nL np s t ; peekKet snap ; ite flag ( popTop snap ) "
          "( dup np snap s ; dup nL np s ; setIfNoneF acc np snap s t ) `",
          start='P0')
# dpStepF np nL snap acc s t  (K J I I' I" I0); the pushNum nL 0 is the own label H0
H0EQ = MEQ('H0', PUSH('J', CONST('4'), GT('P1')))
register2('dps', 'TMIdps', 'tm2fdps', K6, ['Q0', 'H0', 'P1', 'A', "B'", 'E'], 'E"',
          {'K': 'I', 'F': RDBL, 'C0': CNFL, 'F"': PID, 'Y': '2'},
          [('dup', ['J', 'I0', 'I"'], 'P0', 'V1'), ('dup', ['K', 'J', 'I"'], 'V1', 'V2'),
           ('modf', ['J', 'I0', 'K', 'I', 'I"', "I'"], 'V2', 'Q0'),
           ('dup', ['K', 'I', 'I"'], "Q'", 'V3'), ('dup', ['J', 'K', 'I"'], 'V3', 'V4'),
           ('sin', ["I'", 'K', 'I', 'I"', 'I0'], 'V4', 'H0'),
           ('dpb', K6, 'B0', "B'"),
           ('drop', ['J'], "E'", 'V5'), ('drop', ['J'], 'V5', 'V6'), ('drop', ['K'], 'V6', 'E"')],
          "` dpStepF np nL snap acc s t = dup nL t s ; dup np nL s ; modFrag nL t np snap s acc ; "
          "pushSym snap bra ; dup np snap s ; dup nL np s ; setIfNoneF acc np snap s t ; pushNum nL 0 ; "
          "forSlots snap ( dpBodyF np nL snap acc s t ) ; popTop snap ; dropNum nL ; dropNum nL ; dropNum np ` "
          "( ` pushNum nL 0 = pushSym nL comma ` )",
          extra=[('H0', H0EQ)], start='P0')
PREDS8B = ['sin', 'lks', 'ctb', 'me', 'rst', 'dpb', 'dps']


# ============================================================ statements (T8b-blueprint section 4)
JN = FG                                           # ( toNat ` G ): Lean's ` toNat js `
SLOTCN = lambda n: '( ( %s x. ( ( 4 x. B ) + ; 1 2 ) ) + ; 1 0 )' % n


def SETC(j, n, m):
    """Lean ` setC j n b m ` """
    sc = SLOTCN(n)
    return '( ( ( ( %s x. ( ( ( 2 x. %s ) + ( 4 x. %s ) ) + ; 1 1 ) ) + %s ) + ( 3 x. %s ) ) + ; 1 4 )' % (j, sc, m, sc, m)


def LOOKC(j, m):
    """Lean ` lookC j N b m ` """
    return ('( ( ( ( %s x. ( ( ( 2 x. %s ) + ( 4 x. %s ) ) + ; 1 1 ) ) + ( N x. ( ( 6 x. B ) + ; 1 7 ) ) ) + ( 3 x. %s ) ) + ; 2 2 )'
            % (j, SLOTC, m, m))


def COPYC(l):
    """Lean ` copyC l N b ` """
    return '( ( %s x. ( ( ( N x. ( ( 6 x. B ) + ; 1 7 ) ) + ( 2 x. %s ) ) + ; 1 5 ) ) + 8 )' % (l, SLOTC)


BLB = lambda l: '( ( ( %s + 1 ) x. ( N + 2 ) ) x. ( TMB ` B ) )' % l
FILL = 'if ( ( L ` %s ) = ( inr ` (/) ) , ( inl ` W ) , ( L ` %s ) )' % (JN, JN)
SSL = '( %s ++ ( <" %s "> ++ %s ) )' % (PFX('L', JN), FILL, DROP('L', '( %s + 1 )' % JN))


def TBB(A, n='N'):
    """TTAB's inlined ` TblBounded ` over every residue"""
    return ('A. d e. NN0 ( ( %s ` d ) =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` ( %s ` d ) ) ) <_ %s /\\ '
            'A. q e. ran ( 2nd ` ( %s ` d ) ) q < ( 2 ^ B ) ) )' % (A, A, n, A))


CEN = lambda fname, D: CLN(FRAGS[fname].entry(), S, D)

# setIfNoneF / lookupSlot (slot lists)
DATA_W = (('W e. Word NN0', WRD('R', GAM)), '( D ` I ) = ( ( encList ` W ) ++ R )',
          ('( # ` W ) <_ N', 'A. a e. ran W a < ( 2 ^ B )'))
TREE_SIN = TREE(K5, 'sin', (DATA_WDN, DATA_W))
DFIN_SIN = UP(UP(UP('D', 'K', CC(ES(SSL), 'X')), 'J', 'Y'), 'I', 'R')
CONCL_SIN = TRI(CEN('sin', 'D'), CE(DFIN_SIN), SETC(JN, 'N', 'H'))
TREE_LKS = TREE(K5, 'lks', DATA_WDN)
DFIN_LKS = UP(UP('D', 'J', 'Y'), 'I', CC(ESL('( L ` %s )' % JN), '( D ` I )'))
CONCL_LKS = TRI(CEN('lks', 'D'), CE(DFIN_LKS), LOOKC(JN, 'H'))

# copyTbl (slot lists)
Z0X_ = '( <" 0 "> ++ X )'
DATA_CTB = ((STKD('D'), 'L e. %s' % WSLOT, WRD('X', GAM)), '( D ` K ) = ( %s ++ %s )' % (ES('L'), Z0X_),
            (('N e. NN0', 'B e. NN0'), RSB))
TREE_CTB = TREE(K5, 'ctb', DATA_CTB)
DFIN_CTB = UP('D', 'J', CC(ES(REV('L')), '( <" 0 "> ++ ( D ` J ) )'))
CONCL_CTB = TRI(C0('D'), CE(DFIN_CTB), COPYC('( # ` L )'))

# moveEntry
DATA_ME = ((WRD('W', BITS), WRD('X', GAM), STKD('D')), '( D ` K ) = ( W ++ ( <" 4 "> ++ X ) )')
TREE_ME = TREE(K3, 'me', DATA_ME)
DFIN_ME = UP(UP('D', 'K', 'X'), 'J', CC('W', '( <" 4 "> ++ ( D ` J ) )'))
CONCL_ME = TRI(C0('D'), CE(DFIN_ME), '( ( 2 x. ( # ` W ) ) + 4 )')
CONCL_MEN = TRI(CLN('( P ` 0 )', NPC, 'D'), CLN('E', NPC, DFIN_ME), '( ( 2 x. ( # ` W ) ) + 4 )')
DATA_MEB = (('F e. NN0', 'N e. NN0', 'F < ( 2 ^ N )'), (WRD('X', GAM), STKD('D')),
            '( D ` K ) = ( ( encNatGam ` F ) ++ ( <" 4 "> ++ X ) )')
TREE_MEB = TREE(K3, 'me', DATA_MEB)
DFIN_MEB = UP(UP('D', 'K', 'X'), 'J', CC('( encNatGam ` F )', '( <" 4 "> ++ ( D ` J ) )'))
CONCL_MEB = TRI(CLN('( P ` 0 )', NPC, 'D'), CLN('E', NPC, DFIN_MEB), '( TMB ` N )')

# modFrag
NFE, NGE = '( # ` ( encodeNat ` F ) )', '( # ` ( encodeNat ` G ) )'
DATA_MODF = ((('F e. NN0', 'G e. NN', 'N e. NN0'), ('F < ( 2 ^ N )', 'G < ( 2 ^ N )')),
             ((WRD('X', GAM), WRD('Y', GAM), STKD('D')),
              ('( D ` K ) = ( ( encNatGam ` F ) ++ ( <" 4 "> ++ X ) )', '( D ` J ) = ( ( encNatGam ` G ) ++ ( <" 4 "> ++ Y ) )')))
TREE_MODF = TREE(K6, 'modf', DATA_MODF)
XBM = '( ( F mod G ) bwrd %s )' % NFE
DFIN_MODF = UP(UP('D', 'K', CC('( inclBool o. %s )' % XBM, '( <" 4 "> ++ X )')), 'J', 'Y')
MODB = '( ( %s x. ( ( ; 2 3 x. ( %s + %s ) ) + ; 6 0 ) ) + ( ( 9 x. ( %s + %s ) ) + ; 2 8 ) )' % (NFE, NFE, NGE, NFE, NGE)
CONCL_MODF = TRI(CEN('modf', 'D'), CE(DFIN_MODF), MODB)

# resStep
BW = lambda l, rest: CC('( inclBool o. %s )' % l, '( <" 4 "> ++ %s )' % rest)
W3 = lambda l: BW(l, BW("L'", BW('L"', 'X')))
RW = ("if ( ( toNat ` L' ) <_ ( toNat ` L ) , ( ( L subTrunc L' ) ` (/) ) , "
      "( ( L\" subTrunc ( ( L' subTrunc L ) ` (/) ) ) ` (/) ) )")
DATA_RST = ((STKD('D'), ('L e. Word 2o', "L' e. Word 2o", 'L" e. Word 2o'), (WRD('X', GAM), 'H e. NN0')),
            '( D ` K ) = %s' % W3('L'), ('( # ` L ) <_ H', "( # ` L' ) <_ H", '( # ` L" ) <_ H'))
TREE_RST = TREE(K4, 'rst', DATA_RST)
CONCL_RST = TRI(CEN('rst', 'D'), CE(UP('D', 'K', W3(RW))), '( ( ; 2 5 x. H ) + ; 5 3 )')

# table-level forms and the budget wrappers
DATA_TWDN = ((STKD('D'), ('A e. Tbl', 'L e. NN0', 'G e. Word 2o'), (WRD('X', GAM), WRD('Y', GAM))),
             ('( D ` K ) = ( ( L encTblAsc A ) ++ X )', '( D ` J ) = ( ( inclBool o. G ) ++ ( <" 4 "> ++ Y ) )'),
             (('N e. NN0', 'B e. NN0'), ('( # ` G ) <_ ( 2 x. B )', '%s < L' % JN), TBB('A')))
TREE_LKSB = TREE(K5, 'lks', DATA_TWDN)
DFIN_LKSB = UP(UP('D', 'J', 'Y'), 'I', CC(ESL('( A ` %s )' % JN), '( D ` I )'))
CONCL_LKSB = TRI(CEN('lks', 'D'), CE(DFIN_LKSB), BLB('L'))
DATA_TWDNH = ((STKD('D'), ('A e. Tbl', 'L e. NN0', 'G e. Word 2o'), (WRD('X', GAM), WRD('Y', GAM))),
              ('( D ` K ) = ( ( L encTblAsc A ) ++ X )', '( D ` J ) = ( ( inclBool o. G ) ++ ( <" 4 "> ++ Y ) )'),
              (('N e. NN0', 'B e. NN0', 'H e. NN0'), ('( # ` G ) <_ H', '%s < L' % JN), TBB('A')))
TREE_SINT = TREE(K5, 'sin', (DATA_TWDNH, DATA_W))
DFIN_SINT = UP(UP(UP('D', 'K', CC('( L encTblAsc ( ( A SetIfNone %s ) ` W ) )' % JN, 'X')), 'J', 'Y'), 'I', 'R')
CONCL_SINT = TRI(CEN('sin', 'D'), CE(DFIN_SINT), SETC(JN, 'N', 'H'))
DATA_CTBB = ((STKD('D'), ('A e. Tbl', 'L e. NN0'), WRD('X', GAM)), '( D ` K ) = ( ( L encTblAsc A ) ++ %s )' % Z0X_,
             (('N e. NN0', 'B e. NN0'), TBB('A')))
TREE_CTBB = TREE(K5, 'ctb', DATA_CTBB)
DFIN_CTBB = UP('D', 'J', CC('( L encTblDesc A )', '( <" 0 "> ++ ( D ` J ) )'))
CONCL_CTBB = TRI(C0('D'), CE(DFIN_CTBB), BLB('L'))

STMTS8B = {}
for _n in PREDS8B:
    STMTS8B['tmi%su' % _n] = unfold_stmt(FRAGS[_n])
for _l, _t, _c in [('tmisin', TREE_SIN, CONCL_SIN), ('tmilks', TREE_LKS, CONCL_LKS), ('tmictb', TREE_CTB, CONCL_CTB),
                   ('tmime', TREE_ME, CONCL_ME), ('tmimen', TREE_ME, CONCL_MEN), ('tmimeb', TREE_MEB, CONCL_MEB),
                   ('tmimodf', TREE_MODF, CONCL_MODF), ('tmirst', TREE_RST, CONCL_RST),
                   ('tmisint', TREE_SINT, CONCL_SINT), ('tmilksb', TREE_LKSB, CONCL_LKSB), ('tmictbb', TREE_CTBB, CONCL_CTBB)]:
    STMTS8B[_l] = '( %s -> %s )' % (cj(_t), _c)
ORDER8B = (['tmi%su' % n for n in PREDS8B] +
           ['tmime', 'tmimen', 'tmimeb', 'tmimodf', 'tmisin', 'tmilks', 'tmictb', 'tmirst', 'tmisint', 'tmilksb', 'tmictbb'])


def allstmts8b():
    return [(l, STMTS8B[l]) for l in ORDER8B]


# ============================================================ the DP step (T8b-blueprint section 4b)
EWg = lambda t, X: CC('( encNatGam ` %s )' % t, '( <" 4 "> ++ %s )' % X)
SETCL = SETC('L', '( N + 1 )', '( 2 x. B )')
DPBC = '( ( ( ; 5 6 x. B ) + ; 6 7 ) + %s )' % SETCL
DPC = ('( ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 3 3 x. B ) ) + ; 6 4 ) + %s ) + ( L x. ( %s + 2 ) ) )'
       % (SETCL, DPBC))
DPC = '( ( ( ( ( B x. ( ( ; 4 6 x. B ) + ; 6 0 ) ) + ( ; 3 3 x. B ) ) + ; 6 4 ) + %s ) + ( L x. ( %s + 2 ) ) )' % (SETCL, DPBC)
BLB2 = '( ( ( ( L + 1 ) ^ 2 ) x. ( N + 2 ) ) x. ( TMB ` B ) )'
RWD = tsub_text(RW, {'L': 'G', "L'": 'Q', 'L"': '( encodeNat ` L )'})
ACCP = 'if ( O = ( inr ` (/) ) , C , ( ( C SetIfNone ( toNat ` %s ) ) ` ( <" F "> ++ ( 2nd ` O ) ) ) )' % RWD
DATA_DPB = (((STKD('D'), ('F e. NN0', 'L e. NN', 'C e. Tbl'), ('N e. NN0', 'B e. NN0')),
             (('G e. Word 2o', 'Q e. Word 2o', 'O e. %s' % SLOT), (WRD('X', GAM), WRD('Y', GAM)), (WRD('Z', GAM), WRD('U', GAM)))),
            ((('( D ` K ) = %s' % EWg('F', 'X'), '( D ` J ) = %s' % BW('G', BW('Q', EWg('L', 'Y')))),
              ('( D ` I ) = ( %s ++ Z )' % ESL('O'), "( D ` I' ) = ( ( L encTblAsc C ) ++ U )")),
             ((('F < ( 2 ^ B )', 'L < ( 2 ^ B )'), ('( toNat ` G ) < L', '( toNat ` Q ) < L'),
               ('( # ` G ) <_ ( 2 x. B )', '( # ` Q ) <_ ( 2 x. B )')), (SB('O'), TBB('C', '( N + 1 )')))))
TREE_DPB = TREE(K6, 'dpb', DATA_DPB)
DFIN_DPB = UP(UP(UP('D', 'J', BW(RWD, BW('Q', EWg('L', 'Y')))), 'I', 'Z'), "I'", '( ( L encTblAsc %s ) ++ U )' % ACCP)
CONCL_DPB = TRI(CEN('dpb', 'D'), CE(DFIN_DPB), DPBC)
DATA_DPS = ((STKD('D'), ('F e. NN0', 'L e. NN', 'A e. Tbl'), ('N e. NN0', 'B e. NN0')),
            ((WRD('X', GAM), WRD('Y', GAM)), (WRD('R', GAM), WRD('U', GAM))),
            ((('( D ` K ) = %s' % EWg('F', 'X'), '( D ` J ) = %s' % EWg('L', 'Y')),
              ('( D ` I ) = ( ( L encTblDesc A ) ++ ( <" 0 "> ++ R ) )', "( D ` I' ) = ( ( L encTblAsc A ) ++ ( <\" 0 \"> ++ U ) )")),
             (('F < ( 2 ^ B )', 'L < ( 2 ^ B )'), TBB('A'))))
TREE_DPS = TREE(K6, 'dps', DATA_DPS)
DFIN_DPS = UP(UP(UP('D', 'K', 'X'), 'I', 'R'), "I'", '( ( L encTblAsc ( 1st ` ( ( L DpStep F ) ` A ) ) ) ++ ( <" 0 "> ++ U ) )')
CONCL_DPS = TRI(CEN('dps', 'D'), CE(DFIN_DPS), DPC)
CONCL_DPSB = TRI(CEN('dps', 'D'), CE(DFIN_DPS), BLB2)
for _l, _t, _c in [('tmidpb', TREE_DPB, CONCL_DPB), ('tmidps', TREE_DPS, CONCL_DPS), ('tmidpsb', TREE_DPS, CONCL_DPSB)]:
    STMTS8B[_l] = '( %s -> %s )' % (cj(_t), _c)
ORDER8B += ['tmidpb', 'tmidps', 'tmidpsb']


# ------------------------------------------------------------ the sequences of dpStepF's loop
PLW = '( ( F mod L ) bwrd ( # ` ( encodeNat ` F ) ) )'
ELW = '( encodeNat ` L )'
RWX = lambda x: tsub_text(RW, {'L': x, "L'": PLW, 'L"': ELW})
OPR = '( %s ResWOp %s )' % (PLW, ELW)
G1R = '( k e. NN0 |-> if ( k = 0 , (/) , k ) )'
RRS = lambda t: '( seq 0 ( %s , %s ) ` %s )' % (OPR, G1R, t)
ACC0 = '( ( A SetIfNone ( F mod L ) ) ` <" F "> )'
SLY = lambda y: '( A ` ( L - %s ) )' % y
OPAB = lambda x, y: ('if ( %s = ( inr ` (/) ) , %s , ( ( %s SetIfNone ( ( ( L - %s ) x. F ) mod L ) ) ` ( <" F "> ++ ( 2nd ` %s ) ) ) )'
                     % (SLY(y), x, x, y, SLY(y)))
OPA = '( ( L DpAccOp F ) ` A )'
G2A = '( k e. NN0 |-> if ( k = 0 , %s , k ) )' % ACC0
ACCS = lambda t: '( seq 0 ( %s , %s ) ` %s )' % (OPA, G2A, t)
