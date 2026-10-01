r"""Sortie T7: the concrete machine of the Lean development (TM/Frag.lean's
alphabet ` Gamma' ` , state record ` TMSt ` , handlers ` readA ` ... ) and the
concrete instances of the generic composites of T2-T6b/T-MD.

Statement texts (the frozen statements of T7-blueprint.md, ` STMTS7 ` ) and
helpers on top of tools/tmdlib.py (which carries t5lib, t5blib, t6blib,
t1lib).  Notation of the blueprint:

  S = ( 2nd ` T ),  L = ( 2nd ` ( 1st ` T ) ),  DG = dom ( 1st ` ( 1st ` T ) ),
  GK = ( ( 1st ` ( 1st ` T ) ) ` K ),  BITS = ( { 1 } X. 2o ),  OPT = ( Gamma' |_| 1o ),
  GEQ = ( 1st ` ( 1st ` T ) ) = TMGam,  SEQ = ( 2nd ` T ) = TMSt,  PHM7 = ( PHM /\ ( GEQ /\ SEQ ) ),
  MK( a , b , c , d , e , f , g ) = <. a , <. b , <. c , <. d , <. e , <. f , g >. >. >. >. >. >. ,
  SETF( v ; f := x , ... ) = MK with the untouched fields read by the accessors,
  NVA( r , z ) = ( TMrdA ` <. r , ( inl ` z ) >. ),
  NP( O , Q , R ) = { h e. TMSt | ( ( TMfl ` h ) = O /\ ( TMcmp ` h ) = Q /\ ( TMcar ` h ) = R ) } .
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
import lin
lin.FASTPATH = True
from tmdlib import *          # t1lib/t5lib/t5blib/t6blib/tmdlib names (Ctx, Builder, inst, stmt, ...)
from t6blib import stmt, parse_conj, tsub, tsub_text, split_imp, triple_parts, Builder, inst
from t5blib import (GK, GJ, GI, GIP, HDL, CTY, LTY, PTY, RTY, LAB, STKD, STMT, CONST, S1, CC, WRD, FV, P1, MEQ, SSS,
                    TRI, UP3, ren, flat, HT, HTF, statement)
from t5lib import (CLN, GT, UP, NVF, conj, cj, SS, LL, DG, STK_T, GX)

# ------------------------------------------------------------- the concrete alphabet and machine

TMST = 'TMSt'
BITS = '( { 1 } X. 2o )'
B0 = '{ <. 1 , (/) >. }'
BIT0 = '<. 1 , (/) >.'
BIT1 = '<. 1 , 1o >.'
COMMA = '4'
BRA = '2'
OPT = "( Gamma' |_| 1o )"
GAM = "Gamma'"
WG = "Word Gamma'"
WB = 'Word ( { 1 } X. 2o )'
FZ8 = '( 0 ..^ 8 )'
GEQ = '( 1st ` ( 1st ` T ) ) = TMGam'
SEQ = '( 2nd ` T ) = TMSt'
PHT = (GEQ, SEQ)
T_PHM7 = (PHM, PHT)
PHM7 = cj(T_PHM7)
HDLC = "( TMSt ^m ( TMSt X. ( Gamma' |_| 1o ) ) )"
NONE = '( inr ` (/) )'
def SOME(b): return '( inl ` %s )' % b
def IDX(k): return '%s e. ( 0 ..^ 8 )' % k

# ------------------------------------------------------------- the state record

ORDER = ['car', 'ra', 'rb', 'da', 'db', 'cmp', 'fl']
ACC = dict(car='TMcar', ra='TMra', rb='TMrb', da='TMda', db='TMdb', cmp='TMcmp', fl='TMfl')
CODOM = dict(car='2o', ra='( 2o |_| 1o )', rb='( 2o |_| 1o )', da='2o', db='2o', cmp='3o', fl='2o')
READERS = dict(A='TMrdA', B='TMrdB', Bit='TMrdBit', End='TMrdEnd')


def FLD(f, v):
    return '( %s ` %s )' % (ACC[f], v)


def MK(*c):
    assert len(c) == 7
    out = c[6]
    for x in reversed(c[:6]):
        out = '<. %s , %s >.' % (x, out)
    return out


def SETF(v, **kw):
    """Lean's ` { v with f := x , ... } ` as the rebuilt seven-tuple"""
    return MK(*[kw.get(f, FLD(f, v)) for f in ORDER])


TY7 = (('A e. 2o', 'B e. ( 2o |_| 1o )', 'C e. ( 2o |_| 1o )'), ('D e. 2o', 'E e. 2o'), ('F e. 3o', 'G e. 2o'))
MK7 = MK('A', 'B', 'C', 'D', 'E', 'F', 'G')
LET7 = dict(zip(ORDER, 'ABCDEFG'))

# the record updates of the four readers
RDBIT = dict(A=dict(ra=SOME('( 2nd ` Z )')), B=dict(rb=SOME('( 2nd ` Z )')),
             Bit=dict(ra=SOME('( 2nd ` Z )'), da='(/)'), End=dict(db='(/)'))
RDNONE = dict(A=dict(ra=NONE, da='1o'), B=dict(rb=NONE, db='1o'), Bit=dict(ra=NONE, da='1o'), End=dict(db='1o'))

# ------------------------------------------------------------- the concrete handler terms

CIS = '( u e. TMSt |-> if ( ( TMra ` u ) = ( inr ` (/) ) , (/) , 1o ) )'      # fun v => v.ra.isSome
def CRAEQ(b): return '( u e. TMSt |-> if ( ( TMra ` u ) = ( inl ` %s ) , 1o , (/) ) )' % b   # decide (v.ra = some b)
def CNOT(f): return '( u e. TMSt |-> if ( ( %s ` u ) = 1o , (/) , 1o ) )' % ACC[f]           # fun v => !v.f
def CAND(f, g): return '( u e. TMSt |-> if ( ( ( %s ` u ) = 1o /\\ ( %s ` u ) = 1o ) , 1o , (/) ) )' % (ACC[f], ACC[g])
CNGT = '( u e. TMSt |-> if ( ( TMcmp ` u ) = 2o , (/) , 1o ) )'                # fun v => !decide (v.cmp = .gt)
PBR = '( u e. TMSt |-> <. 1 , ( bitOf ` ( TMra ` u ) ) >. )'                   # fun v => .bit (bitOf v.ra)
PSUM = ('( u e. TMSt |-> <. 1 , ( ( ( bitOf ` ( TMra ` u ) ) sumBit ( bitOf ` ( TMrb ` u ) ) ) ` ( TMcar ` u ) ) >. )')
PID = "( 1st |` ( TMSt X. ( Gamma' |_| 1o ) ) )"                               # fun v _ => v
LID = '( _I |` TMSt )'                                                          # Frag.skip's load
def LSET(**kw): return '( u e. TMSt |-> %s )' % SETF('u', **kw)                # fun v => { v with ... }
LMAJ = LSET(car='( ( ( bitOf ` ( TMra ` u ) ) majBit ( bitOf ` ( TMrb ` u ) ) ) ` ( TMcar ` u ) )')
LBOR = LSET(car='( ( ( bitOf ` ( TMra ` u ) ) borrow ( bitOf ` ( TMrb ` u ) ) ) ` ( TMcar ` u ) )')
LCMP = LSET(cmp='( ( ( bitOf ` ( TMra ` u ) ) cmpStep ( bitOf ` ( TMrb ` u ) ) ) ` ( TMcmp ` u ) )')
LZS = LSET(fl='if ( ( ( TMfl ` u ) = 1o /\\ -. ( bitOf ` ( TMra ` u ) ) = 1o ) , 1o , (/) )')   # flag := flag && !bit
LFL1 = LSET(fl='1o')
LADD0 = LSET(car='(/)', ra=NONE, rb=NONE, da='(/)', db='(/)')
LCMP0 = LSET(cmp='1o', ra=NONE, rb=NONE, da='(/)', db='(/)')
def LSUB0(c0, db0): return LSET(car=c0, ra=NONE, rb=NONE, da='(/)', db=db0)
LCAR0 = LSET(car='(/)')
def NVA(r, z): return NVF('TMrdA', r, z)
def NP(o='O', q='Q', r='R'):
    return '{ h e. TMSt | ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = %s /\\ ( TMcar ` h ) = %s ) }' % (o, q, r)
def NRA(z): return '{ h e. TMSt | ( ( TMra ` h ) = ( inl ` ( 2nd ` %s ) ) /\\ ( TMda ` h ) = (/) ) }' % z
NDA = '{ h e. TMSt | ( TMda ` h ) = 1o }'
GID = '( _I |` ( { 1 } X. 2o ) )'

# ============================================================ statements: the state record

STMTS7 = []


def add7(label, text):
    STMTS7.append((label, text))
    return text


for f in ORDER:
    add7('tmc%scl' % f, '( V e. TMSt -> %s e. %s )' % (FLD(f, 'V'), CODOM[f]))
add7('tmcstmk', '( %s -> %s e. TMSt )' % (cj(TY7), MK7))
for f in ORDER:
    add7('tmc%smk' % f, '( %s -> ( %s ` %s ) = %s )' % (cj(TY7), ACC[f], MK7, LET7[f]))
add7('tmcnbit', '( ( A e. RR /\\ B e. 2o ) -> -. A = <. C , B >. )')
add7('tmcnbits', '( A e. RR -> -. A e. ( { 1 } X. 2o ) )')
add7('tmcbit2', '( Z e. ( { 1 } X. 2o ) -> ( 2nd ` Z ) e. 2o )')
add7('tmcbitop', '( Z e. ( { 1 } X. 2o ) -> Z = <. 1 , ( 2nd ` Z ) >. )')
for h, name in READERS.items():
    add7('tmcrd%sf' % h.lower(), '%s e. %s' % (name, HDLC))
for h, name in READERS.items():
    add7('tmcrd%sb' % h.lower(), '( ( V e. TMSt /\\ Z e. %s ) -> ( %s ` <. V , ( inl ` Z ) >. ) = %s )'
         % (BITS, name, SETF('V', **RDBIT[h])))
    add7('tmcrd%sn' % h.lower(), "( ( V e. TMSt /\\ Z e. Gamma' /\\ -. Z e. %s ) -> ( %s ` <. V , ( inl ` Z ) >. ) = %s )"
         % (BITS, name, SETF('V', **RDNONE[h])))
add7('tmcpidf', '%s e. %s' % (PID, HDLC))
add7('tmcdg', '( %s -> dom ( 1st ` ( 1st ` T ) ) = ( 0 ..^ 8 ) )' % GEQ)
add7('tmcgk', "( ( %s /\\ K e. ( 0 ..^ 8 ) ) -> ( K e. dom ( 1st ` ( 1st ` T ) ) /\\ ( ( 1st ` ( 1st ` T ) ) ` K ) = Gamma' ) )" % GEQ)
add7('tmchdl', '( ( ( %s /\\ %s ) /\\ K e. ( 0 ..^ 8 ) ) -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) )'
     % (GEQ, SEQ, RTY('TMrdA', 'K'), RTY('TMrdB', 'K'), RTY('TMrdBit', 'K'), RTY('TMrdEnd', 'K'), RTY(PID, 'K')))
add7('tmcmapty', '( ( %s /\\ Y e. V /\\ A. u e. TMSt X e. Y ) -> ( u e. TMSt |-> X ) e. ( Y ^m ( 2nd ` T ) ) )' % SEQ)

# ============================================================ statements: the interfaces (closed)

NPC = NP()
ST_MVI = ('( A. r e. TMSt A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z ) /\\ A. r e. TMSt -. ( %s ` %s ) = 1o )'
          % (BITS, CIS, NVA('r', 'z'), PBR, NVA('r', 'z'), CIS, NVA('r', '4')))
ST_DRI = ('( A. r e. TMSt A. z e. %s ( %s ` %s ) = 1o /\\ A. r e. TMSt -. ( %s ` %s ) = 1o )'
          % (BITS, CIS, NVA('r', 'z'), CIS, NVA('r', '4')))
ST_MVIN = ('( A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z /\\ %s e. %s ) /\\ A. r e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s ) )'
           % (NPC, BITS, CIS, NVA('r', 'z'), PBR, NVA('r', 'z'), NVA('r', 'z'), NPC, NPC, CIS, NVA('r', '4'), NVA('r', '4'), NPC))
ST_MVING = ('( A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = ( %s ` z ) /\\ %s e. %s ) /\\ A. m e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s ) )'
            % (NPC, BITS, CIS, NVA('r', 'z'), PBR, NVA('r', 'z'), GID, NVA('r', 'z'), NPC, NPC, CIS, NVA('m', '4'), NVA('m', '4'), NPC))
CRA0 = CRAEQ('(/)')
ST_SPI = ("( ( Y e. Gamma' /\\ Y =/= <. 1 , (/) >. ) -> ( A. r e. %s A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` <. %s , ( inl ` z ) >. ) e. %s ) /\\ A. m e. %s ( -. ( %s ` %s ) = 1o /\\ %s e. %s ) ) )"
          % (NPC, B0, CRA0, NVA('r', 'z'), PID, NVA('r', 'z'), NPC, NPC, CRA0, NVA('m', 'Y'), NVA('m', 'Y'), NPC))
ST_PBI = '( Z e. %s -> A. r e. TMSt ( TMrdBit ` <. r , ( inl ` Z ) >. ) e. %s )' % (BITS, NRA('Z'))
ST_PEI = 'A. r e. TMSt ( TMrdBit ` <. r , ( inl ` 4 ) >. ) e. %s' % NDA
for l, s in [('tmcmvi', ST_MVI), ('tmcdri', ST_DRI), ('tmcmvin', ST_MVIN), ('tmcmving', ST_MVING),
             ('tmcspi', ST_SPI), ('tmcpbi', ST_PBI), ('tmcpei', ST_PEI)]:
    add7(l, s)

# ============================================================ statements: the concrete composites

C4 = CONST('4')
YX4 = CC(S1('4'), 'X')
WYX4 = CC('W', YX4)
# dropNum x (T1 tm2fdrop): pop K readA ( branch isSome ( goto A ) ( goto E ) )
STM_DROP = POP('K', 'TMrdA', BRANCH(CIS, GT('A'), GT('E')))
TREE_DROP = ((T_PHM7, MEQ('A', STM_DROP)), ((LAB('A'), LAB('E')), IDX('K')), ((STKD('D'), WRD('X', GAM)), WRD('W', BITS)))
CONCL_DROP = TRI(CLN('A', SS, UP('D', 'K', WYX4)), CLN('E', SS, UP('D', 'K', 'X')), '( ( # ` W ) + 1 )')
# dup x y s (T5 tm2fdup at K J I): push 4 on I ; moveNum K I ; push 4 on K ; push 4 on J ; move2Num I K J
ST_D1 = PUSH('I', C4, GT("A'"))
ST_DMOV = POP('K', 'TMrdA', BRANCH(CIS, PUSH('I', PBR, GT("A'")), GT('A"')))
ST_D3 = PUSH('K', C4, GT("E'"))
ST_D4 = PUSH('J', C4, GT('E"'))
ST_DMV2 = POP('I', 'TMrdA', BRANCH(CIS, PUSH('K', PBR, PUSH('J', PBR, GT('E"'))), GT('E')))
PROG_DUP = ((MEQ('A', ST_D1), MEQ("A'", ST_DMOV)), (MEQ('A"', ST_D3), MEQ("E'", ST_D4), MEQ('E"', ST_DMV2)))
LABS6 = ((LAB('A'), LAB("A'"), LAB('A"')), (LAB("E'"), LAB('E"'), LAB('E')))
TREE_DUP = ((T_PHM7, PROG_DUP), (LABS6, (IDX('K'), IDX('J'), IDX('I')), ('K =/= J', 'K =/= I', 'J =/= I')),
            ((WRD('W', BITS), WRD('X', GAM), STKD('D')), '( D ` K ) = %s' % WYX4))
CONCL_DUP = TRI(CLN('A', SS, 'D'), CLN('E', SS, UP('D', 'J', CC('W', CC(S1('4'), '( D ` J )')))), '( ( 2 x. ( # ` W ) ) + 5 )')
# canonNum x s (T-MD tm2fcan at K J): push 4 on J ; moveNum K J ; stripLoop J ; push 4 on K ; moveNum J K
ST_C1 = PUSH('J', C4, GT("A'"))
ST_CMV1 = POP('K', 'TMrdA', BRANCH(CIS, PUSH('J', PBR, GT("A'")), GT('A"')))
ST_CSP = PEEK('J', 'TMrdA', BRANCH(CRA0, POP('J', PID, GT('A"')), GT("E'")))
ST_C4 = PUSH('K', C4, GT('E"'))
ST_CMV2 = POP('J', 'TMrdA', BRANCH(CIS, PUSH('K', PBR, GT('E"')), GT('E')))
PROG_CAN = ((MEQ('A', ST_C1), MEQ("A'", ST_CMV1)), (MEQ('A"', ST_CSP), MEQ("E'", ST_C4), MEQ('E"', ST_CMV2)))
IBL = '( inclBool o. L )'
ENL = '( encNatGam ` ( toNat ` L ) )'
DATA_CAN = ((WRD('L', '2o'), WRD('X', GAM), STKD('D')), '( D ` K ) = %s' % CC(IBL, YX4))
TREE_CAN = ((T_PHM7, PROG_CAN), (LABS6, (IDX('K'), IDX('J'), 'K =/= J')), DATA_CAN)
CONCL_CAN = TRI(CLN('A', NPC, 'D'), CLN('E', NPC, UP('D', 'K', CC(ENL, YX4))), '( ( 2 x. ( # ` L ) ) + 5 )')
TREE_CAN0 = (TREE_CAN, '( toNat ` L ) = 0')
TREE_CANP = (TREE_CAN, '( toNat ` L ) e. NN')
TREE_CANB = (TREE_CAN, ('B e. NN0', '( # ` L ) <_ B'))
CONCL_CANB = TRI(CLN('A', NPC, 'D'), CLN('E', NPC, UP('D', 'K', CC(ENL, YX4))), '( TMB ` B )')
# the shift-down loop's stack family (T-MD D8): the step equation by tm2stkup8
XF = lambda i: '( X ` %s )' % i
YF = lambda i: '( Y ` %s )' % i
HF = lambda i: '( H ` %s )' % i
QF = lambda i: '( Q ` %s )' % i
def UPD4(D, i):
    return UP(UP(UP(UP(D, "I'", QF(i)), 'J', YF(i)), 'I', HF(i)), 'K', XF(i))
PFAM = '( j e. NN0 |-> %s )' % UPD4('D', 'j')   # binder j: tm2fdmc2 has $d P i, fvmptd $d ph x
IDX4 = (('K e. %s' % DG, 'J e. %s' % DG), ('I e. %s' % DG, "I' e. %s" % DG))
DIST4 = (('K =/= J', 'K =/= I', "K =/= I'"), ('J =/= I', "J =/= I'", "I =/= I'"))
FAM4 = 'A. i e. NN0 ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) )' % (WRD(XF('i'), GK), WRD(YF('i'), GJ), WRD(HF('i'), GI), WRD(QF('i'), GIP))
TREE_DMSTP = ((('T e. V', STKD('D')), (IDX4, DIST4)), (FAM4, 'N e. NN0'))
CONCL_DMSTP = '( %s ` ( N + 1 ) ) = %s' % (PFAM, UPD4('( %s ` N )' % PFAM, '( N + 1 )'))

for l, t, c in [('tmcdrop', TREE_DROP, CONCL_DROP), ('tmcdup', TREE_DUP, CONCL_DUP),
                ('tmccan0', TREE_CAN0, CONCL_CAN), ('tmccanp', TREE_CANP, CONCL_CAN), ('tmccan', TREE_CAN, CONCL_CAN),
                ('tmccanb', TREE_CANB, CONCL_CANB), ('tmcdmstp', TREE_DMSTP, CONCL_DMSTP)]:
    add7(l, statement(t, c))

# ============================================================ concretizing a generic database statement

REPL = [('K e. dom ( 1st ` ( 1st ` T ) )', 'K e. ( 0 ..^ 8 )'), ('J e. dom ( 1st ` ( 1st ` T ) )', 'J e. ( 0 ..^ 8 )'),
        ('I e. dom ( 1st ` ( 1st ` T ) )', 'I e. ( 0 ..^ 8 )'), ("I' e. dom ( 1st ` ( 1st ` T ) )", "I' e. ( 0 ..^ 8 )"),
        ('I" e. dom ( 1st ` ( 1st ` T ) )', 'I" e. ( 0 ..^ 8 )')]
for _k in ['K', 'J', 'I', "I'", 'I"']:
    REPL.append(('( ( 1st ` ( 1st ` T ) ) ` %s )' % _k, "Gamma'"))


def _replace(text):
    for a, b in REPL:
        text = text.replace(a, b)
    return text


def prune(tree, drop):
    """remove the leaves whose text is in `drop`; collapse degenerate tuples"""
    if isinstance(tree, str):
        return None if tree in drop else tree
    kids = [prune(t, drop) for t in tree]
    kids = [k for k in kids if k is not None]
    if not kids:
        return None
    if len(kids) == 1:
        return kids[0]
    return tuple(kids)


def conc(label, m, drop=(), extra=None):
    """the concrete form of the generic theorem `label`: class variables
    substituted by `m`, the leaves in `drop` (discharged typings and
    interfaces) removed, the machine shape PHM7 in place of PHM, the stack
    indices in ( 0 ..^ 8 ) and the alphabets Gamma'.  Returns (tree, concl)."""
    ante, concl = split_imp(stmt(label))
    tree = tsub(parse_conj(ante), m)
    drop = set(tsub_text(d, m) for d in drop)
    tree = prune(tree, drop)

    def fix(t):
        if isinstance(t, str):
            if t == PHM:
                return T_PHM7
            return _replace(t)
        return tuple(fix(x) for x in t)
    tree = fix(tree)
    if extra:
        tree = (tree, extra)
    return tree, _replace(tsub_text(concl, m))

add7('tmcinclf', 'inclBool : 2o --> ( { 1 } X. 2o )')
add7('tmcibw', '( L e. Word 2o -> ( inclBool o. L ) e. Word ( { 1 } X. 2o ) )')
add7('tmcinlne', '( A e. V -> -. ( inl ` A ) = ( inr ` (/) ) )')
add7('tmcinl11', '( ( A e. V /\\ B e. W ) -> ( ( inl ` A ) = ( inl ` B ) <-> A = B ) )')
OPTB = '( 2o |_| 1o )'


# ============================================================ proof helpers

def closed(w, ph, ref, fact):
    """( ph -> fact ) from the closed theorem ref"""
    c = w.s([], ref, fact)
    return w.s([c], 'a1i', '( %s -> %s )' % (ph, fact))


def st_comps(w, ph, r, rr):
    """the seven accessor closures of the state r (rr : ( ph -> r e. TMSt ))"""
    return {f: w.s([rr, w.inst('tmc%scl' % f)], 'syl', '( %s -> %s e. %s )' % (ph, FLD(f, r), CODOM[f])) for f in ORDER}


def tuple_facts(w, ph, comps, cls):
    """comps: the seven component texts, cls: steps ( ph -> comp e. CODOM ).
    Returns (step : MK e. TMSt, dict f -> step ( ph -> ( TMxx ` MK ) = comp ))"""
    t1 = w.s(cls[0:3], '3jca', '( %s -> ( %s e. 2o /\\ %s e. %s /\\ %s e. %s ) )' % (ph, comps[0], comps[1], OPTB, comps[2], OPTB))
    t2 = w.s(cls[3:5], 'jca', '( %s -> ( %s e. 2o /\\ %s e. 2o ) )' % (ph, comps[3], comps[4]))
    t3 = w.s(cls[5:7], 'jca', '( %s -> ( %s e. 3o /\\ %s e. 2o ) )' % (ph, comps[5], comps[6]))
    ty = w.s([t1, t2, t3], '3jca', '( %s -> %s )' % (ph, cj(tsub(TY7, dict(zip('ABCDEFG', comps))))))
    mk = MK(*comps)
    mem = w.s([ty, w.inst('tmcstmk')], 'syl', '( %s -> %s e. TMSt )' % (ph, mk))
    vals = {f: w.s([ty, w.inst('tmc%smk' % f)], 'syl', '( %s -> ( %s ` %s ) = %s )' % (ph, ACC[f], mk, comps[i]))
            for i, f in enumerate(ORDER)}
    return mem, vals


def _transport(w, ph, N, val, mem, vals, comps):
    """from val : ( ph -> N = MK ) carry the tuple's membership and field values to N"""
    memN = w.s([val, mem], 'eqeltrd', '( %s -> %s e. TMSt )' % (ph, N))
    fields = {}
    for i, f in enumerate(ORDER):
        e = w.s([val], 'fveq2d', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (ph, ACC[f], N, ACC[f], MK(*comps)))
        fields[f] = w.s([e, vals[f]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, ACC[f], N, comps[i]))
    return dict(val=val, mem=memN, fields=fields, comps=comps, tmem=mem, tvals=vals)


def rd_bit(w, ph, h, r, z, rr, zz):
    """the reader h on the bit letter z at the state r: value, membership, field values
    (rr : ( ph -> r e. TMSt ), zz : ( ph -> z e. BITS ))"""
    N = NVF(READERS[h], r, z)
    upd = {k: v.replace('( 2nd ` Z )', '( 2nd ` %s )' % z) for k, v in RDBIT[h].items()}
    val = w.s([rr, zz, w.inst('tmcrd%sb' % h.lower())], 'syl2anc', '( %s -> %s = %s )' % (ph, N, SETF(r, **upd)))
    cl = st_comps(w, ph, r, rr)
    z2 = w.s([zz, w.inst('tmcbit2')], 'syl', '( %s -> ( 2nd ` %s ) e. 2o )' % (ph, z))
    iz = w.s([z2, w.inst('djulcl')], 'syl', '( %s -> ( inl ` ( 2nd ` %s ) ) e. %s )' % (ph, z, OPTB))
    comps = [upd.get(f, FLD(f, r)) for f in ORDER]
    cls = []
    for f, c in zip(ORDER, comps):
        if c == SOME('( 2nd ` %s )' % z):
            cls.append(iz)
        elif c == '(/)':
            cls.append(closed(w, ph, '0el2o', '(/) e. 2o'))
        else:
            cls.append(cl[f])
    mem, vals = tuple_facts(w, ph, comps, cls)
    return _transport(w, ph, N, val, mem, vals, comps)


def rd_nb(w, ph, h, r, Z, rr, zg, znb):
    """the reader h on a non-bit letter Z (zg : Z e. Gamma', znb : -. Z e. BITS)"""
    N = NVF(READERS[h], r, Z)
    upd = RDNONE[h]
    val = w.s([rr, zg, znb, w.inst('tmcrd%sn' % h.lower())], 'syl3anc', '( %s -> %s = %s )' % (ph, N, SETF(r, **upd)))
    cl = st_comps(w, ph, r, rr)
    comps = [upd.get(f, FLD(f, r)) for f in ORDER]
    cls = []
    for f, c in zip(ORDER, comps):
        if c == NONE:
            z1 = w.s([], '0lt1o', '(/) e. 1o')
            m = w.s([z1, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, OPTB))
            cls.append(w.s([m], 'a1i', '( %s -> %s e. %s )' % (ph, NONE, OPTB)))
        elif c == '1o':
            cls.append(closed(w, ph, '1oel2o', '1o e. 2o'))
        else:
            cls.append(cl[f])
    mem, vals = tuple_facts(w, ph, comps, cls)
    return _transport(w, ph, N, val, mem, vals, comps)


def rd_comma(w, ph, h, r, rr):
    """the reader h on the terminator 4"""
    zg = closed(w, ph, 'gamma4', "4 e. Gamma'")
    r4 = closed(w, ph, '4re', '4 e. RR')
    znb = w.s([r4, w.inst('tmcnbits')], 'syl', '( %s -> -. 4 e. %s )' % (ph, BITS))
    return rd_nb(w, ph, h, r, '4', rr, zg, znb)


def lamval(w, ph, X_of, A, amem, xex):
    """( ph -> ( ( u e. TMSt |-> X(u) ) ` A ) = X(A) ) by fvmptd; amem : A e. TMSt, xex : X(A) e. _V"""
    F = '( u e. TMSt |-> %s )' % X_of('u')
    da = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, F, F))
    idu = w.s([], 'id', '( u = %s -> u = %s )' % (A, A))
    cg, newX = w.congr(X_of('u'), {'u': A}, 'u = %s' % A, {'u': idu})
    assert newX == X_of(A), (newX, X_of(A))
    if ' u ' in ' %s ' % ph:     # fvmptd's $d ph x: the antecedent carries the program's lambdas
        return fvg(w, ph, F, 'TMSt', X_of, A, cg, amem, xex)
    cga = w.s([cg], 'adantl', '( ( %s /\\ u = %s ) -> %s = %s )' % (ph, A, X_of('u'), X_of(A)))
    return w.s([da, cga, amem, xex], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ph, F, A, X_of(A)))


def fvg(w, ph, F, D, X_of, A, cg, amem, xex):
    """( ph -> ( F ` A ) = X(A) ) by ~ fvmptg (no $d on ph); cg : ( u = A -> X(u) = X(A) )"""
    assert ' u ' not in ' %s ' % A, A
    fe = w.s([], 'eqid', '%s = %s' % (F, F))
    g = w.s([cg, fe], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (A, D, X_of(A), F, A, X_of(A)))
    return w.s([amem, xex, g], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ph, F, A, X_of(A)))


def ifex_closed(w, ph, cond, A, B, aex, bex):
    """( ph -> if ( cond , A , B ) e. _V ) from closed steps aex : A e. _V, bex : B e. _V"""
    e = w.s([aex, bex], 'ifex', 'if ( %s , %s , %s ) e. _V' % (cond, A, B))
    return w.s([e], 'a1i', '( %s -> if ( %s , %s , %s ) e. _V )' % (ph, cond, A, B))


def cis_val(w, ph, nv, N):
    """( ph -> ( CIS ` N ) = 1o ) when nv['comps'][1] is a some, ( ... ) = (/) when it is NONE"""
    X_of = lambda t: 'if ( ( TMra ` %s ) = %s , (/) , 1o )' % (t, NONE)
    z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
    xex = ifex_closed(w, ph, '( TMra ` %s ) = %s' % (N, NONE), '(/)', '1o', z0, o1)
    v = lamval(w, ph, X_of, N, nv['mem'], xex)
    ra = nv['comps'][1]
    fr = nv['fields']['ra']
    if ra == NONE:
        it = w.s([fr], 'iftrued', '( %s -> %s = (/) )' % (ph, X_of(N)))
        return w.s([v, it], 'eqtrd', '( %s -> ( %s ` %s ) = (/) )' % (ph, CIS, N)), '(/)'
    # ra = ( inl ` X ) : not NONE
    inner = ra[len('( inl ` '):-2]
    xv = w.s([], 'fvex', '%s e. _V' % inner) if inner.startswith('(') else None
    if xv is None:
        xv = w.s([], 'vex' if len(inner) == 1 and inner.islower() else 'elexi', '%s e. _V' % inner)
    ne = w.s([xv, w.inst('tmcinlne')], 'ax-mp', '-. %s = %s' % (ra, NONE))
    nea = w.s([ne], 'a1i', '( %s -> -. %s = %s )' % (ph, ra, NONE))
    eq = w.s([fr], 'eqeq1d', '( %s -> ( ( TMra ` %s ) = %s <-> %s = %s ) )' % (ph, N, NONE, ra, NONE))
    nn = w.s([eq, nea], 'mtbird', '( %s -> -. ( TMra ` %s ) = %s )' % (ph, N, NONE))
    it = w.s([nn], 'iffalsed', '( %s -> %s = 1o )' % (ph, X_of(N)))
    return w.s([v, it], 'eqtrd', '( %s -> ( %s ` %s ) = 1o )' % (ph, CIS, N)), '1o'


def craeq_val(w, ph, nv, N, b):
    """( ph -> ( CRAEQ( b ) ` N ) = 1o / (/) ) : decide ( ra = some b ); returns (step, value, is_eq)
    given the register's value nv['comps'][1] (a some of a term equal or not to b is decided by the
    caller through `eqstep`: pass a step ( ph -> ( TMra ` N ) = ( inl ` b ) ) or ( ph -> -. ... ))"""
    raise NotImplementedError


def pbr_val(w, ph, nv, N, z, zz):
    """( ph -> ( PBR ` N ) = z ) when ( TMra ` N ) = ( inl ` ( 2nd ` z ) ), z e. BITS"""
    X_of = lambda t: '<. 1 , ( bitOf ` ( TMra ` %s ) ) >.' % t
    xex = closed(w, ph, 'opex', '%s e. _V' % X_of(N))
    v = lamval(w, ph, X_of, N, nv['mem'], xex)
    fr = nv['fields']['ra']
    b = w.s([fr], 'fveq2d', '( %s -> ( bitOf ` ( TMra ` %s ) ) = ( bitOf ` ( inl ` ( 2nd ` %s ) ) ) )' % (ph, N, z))
    z2 = w.s([zz, w.inst('tmcbit2')], 'syl', '( %s -> ( 2nd ` %s ) e. 2o )' % (ph, z))
    bs = w.s([z2, w.inst('bitofsome')], 'syl', '( %s -> ( bitOf ` ( inl ` ( 2nd ` %s ) ) ) = ( 2nd ` %s ) )' % (ph, z, z))
    b2 = w.s([b, bs], 'eqtrd', '( %s -> ( bitOf ` ( TMra ` %s ) ) = ( 2nd ` %s ) )' % (ph, N, z))
    o = w.s([b2], 'opeq2d', '( %s -> %s = <. 1 , ( 2nd ` %s ) >. )' % (ph, X_of(N), z))
    zop = w.s([zz, w.inst('tmcbitop')], 'syl', '( %s -> %s = <. 1 , ( 2nd ` %s ) >. )' % (ph, z, z))
    o2 = w.s([o, zop], 'eqtr4d', '( %s -> %s = %s )' % (ph, X_of(N), z))
    return w.s([v, o2], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph, PBR, N, z))


NPCOND = lambda t: '( ( TMfl ` %s ) = O /\\ ( TMcmp ` %s ) = Q /\\ ( TMcar ` %s ) = R )' % (t, t, t)


def np_out(w, ph, r, rin):
    """from rin : ( ph -> r e. NP ) : (r e. TMSt, fl = O, cmp = Q, car = R)"""
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (r, r))
    cg, new = w.wcongr(NPCOND('h'), {'h': r}, 'h = %s' % r, {'h': idh})
    assert new == NPCOND(r)
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (r, NPC, r, NPCOND(r)))
    both = w.s([rin, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ph, r, NPCOND(r)))
    rr = w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (ph, r))
    cnd = w.s([both], 'simprd', '( %s -> %s )' % (ph, NPCOND(r)))
    fl = w.s([cnd, w.inst('simp1')], 'syl', '( %s -> ( TMfl ` %s ) = O )' % (ph, r))
    cm = w.s([cnd, w.inst('simp2')], 'syl', '( %s -> ( TMcmp ` %s ) = Q )' % (ph, r))
    ca = w.s([cnd, w.inst('simp3')], 'syl', '( %s -> ( TMcar ` %s ) = R )' % (ph, r))
    return rr, fl, cm, ca


def np_in(w, ph, A, amem, fl, cm, ca):
    """( ph -> A e. NP ) from amem : A e. TMSt and the three field equations"""
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (A, A))
    cg, new = w.wcongr(NPCOND('h'), {'h': A}, 'h = %s' % A, {'h': idh})
    assert new == NPCOND(A)
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (A, NPC, A, NPCOND(A)))
    cnd = w.s([fl, cm, ca], '3jca', '( %s -> %s )' % (ph, NPCOND(A)))
    both = w.s([amem, cnd], 'jca', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ph, A, NPCOND(A)))
    return w.s([both, el], 'sylibr', '( %s -> %s e. %s )' % (ph, A, NPC))


def np_keep(w, ph, nv, N, fl, cm, ca):
    """( ph -> N e. NP ) for a reader value nv whose flag cmp carry are the state's, given the
    state's equations fl cm ca (steps on r)"""
    f = w.s([nv['fields']['fl'], fl], 'eqtrd', '( %s -> ( TMfl ` %s ) = O )' % (ph, N))
    c = w.s([nv['fields']['cmp'], cm], 'eqtrd', '( %s -> ( TMcmp ` %s ) = Q )' % (ph, N))
    a = w.s([nv['fields']['car'], ca], 'eqtrd', '( %s -> ( TMcar ` %s ) = R )' % (ph, N))
    return np_in(w, ph, N, nv['mem'], f, c, a)


def rab_in(w, ph, cls, cond_fn, A, amem, cond_step):
    """( ph -> A e. cls ) for cls = { h e. TMSt | cond_fn( h ) } from amem : A e. TMSt and
    cond_step : ( ph -> cond_fn( A ) )"""
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (A, A))
    cg, new = w.wcongr(cond_fn('h'), {'h': A}, 'h = %s' % A, {'h': idh})
    assert new == cond_fn(A), (new, cond_fn(A))
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (A, cls, A, cond_fn(A)))
    both = w.s([amem, cond_step], 'jca', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ph, A, cond_fn(A)))
    return w.s([both, el], 'sylibr', '( %s -> %s e. %s )' % (ph, A, cls))


def cra_val(w, ph, nv, N, b, decided):
    """( ph -> ( CRAEQ( b ) ` N ) = 1o ) when decided : ( ph -> ( TMra ` N ) = ( inl ` b ) ),
    ( ... ) = (/) when decided : ( ph -> -. ( TMra ` N ) = ( inl ` b ) ); returns (step, value)"""
    X_of = lambda t: 'if ( ( TMra ` %s ) = ( inl ` %s ) , 1o , (/) )' % (t, b)
    z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
    xex = ifex_closed(w, ph, '( TMra ` %s ) = ( inl ` %s )' % (N, b), '1o', '(/)', o1, z0)
    v = lamval(w, ph, X_of, N, nv['mem'], xex)
    f = formula(w, decided)
    if f.startswith('( %s -> -.' % ph):
        it = w.s([decided], 'iffalsed', '( %s -> %s = (/) )' % (ph, X_of(N)))
        return w.s([v, it], 'eqtrd', '( %s -> ( %s ` %s ) = (/) )' % (ph, CRAEQ(b), N)), '(/)'
    it = w.s([decided], 'iftrued', '( %s -> %s = 1o )' % (ph, X_of(N)))
    return w.s([v, it], 'eqtrd', '( %s -> ( %s ` %s ) = 1o )' % (ph, CRAEQ(b), N)), '1o'


def not1o(w, ph, st, F, N):
    """( ph -> -. ( F ` N ) = 1o ) from st : ( ph -> ( F ` N ) = (/) )"""
    n0 = w.s([], '1n0', '1o =/= (/)')
    n0b = w.s([n0], 'nesymi', '-. (/) = 1o')
    n0a = w.s([n0b], 'a1i', '( %s -> -. (/) = 1o )' % ph)
    e2 = w.s([st], 'eqeq1d', '( %s -> ( ( %s ` %s ) = 1o <-> (/) = 1o ) )' % (ph, F, N))
    return w.s([e2, n0a], 'mtbird', '( %s -> -. ( %s ` %s ) = 1o )' % (ph, F, N))


# ============================================================ isZero at the machine (consumer form)

P2 = "( 2nd |` ( { 1 } X. 2o ) )"
SPAIR = '( u e. TMSt |-> <. ( TMfl ` u ) , ( TMcmp ` u ) >. )'
OZ = '( u e. Word ( { 1 } X. 2o ) |-> <. if ( ( toNat ` ( %s o. u ) ) = 0 , 1o , (/) ) , Q >. )' % P2
IFL = 'if ( ( toNat ` L ) = 0 , 1o , (/) )'
NZC = '{ h e. TMSt | ( ( TMfl ` h ) = %s /\\ ( TMcmp ` h ) = Q ) }' % IFL
ST_Z1 = PUSH('I', C4, GT("A'"))
ST_ZMOV = POP('K', 'TMrdA', BRANCH(CIS, PUSH('I', PBR, GT("A'")), GT('A"')))
ST_Z3 = PUSH('K', C4, GT("E'"))
ST_Z4 = LOAD(LFL1, GT('E"'))
ST_ZZS = POP('I', 'TMrdA', BRANCH(CIS, PUSH('K', PBR, LOAD(LZS, GT('E"'))), GT('E')))
PROG_IZ = ((MEQ('A', ST_Z1), MEQ("A'", ST_ZMOV)), (MEQ('A"', ST_Z3), MEQ("E'", ST_Z4), MEQ('E"', ST_ZZS)))
TREE_IZ = ((T_PHM7, PROG_IZ), (LABS6, (IDX('K'), IDX('I'), 'K =/= I')), DATA_CAN)
CONCL_IZ = TRI(CLN('A', NPC, 'D'), CLN('E', NZC, 'D'), '( ( 2 x. ( # ` L ) ) + 5 )')
add7('tmcif1', '( if ( ph , 1o , (/) ) = 1o <-> ph )')
add7('tmctn0c', '( ( B e. 2o /\\ L e. Word 2o ) -> ( ( toNat ` ( <" B "> ++ L ) ) = 0 <-> ( B = (/) /\\ ( toNat ` L ) = 0 ) ) )')
add7('tmcibinv', '( L e. Word 2o -> ( %s o. ( inclBool o. L ) ) = L )' % P2)
add7('tmciz', statement(TREE_IZ, CONCL_IZ))

# ============================================================ the two-operand loops (add; sub and cmp share the reads)
# Operand families of T5 D4 at the machine, over a bit word L and a rest X:
#   OPF( L , X ) = the stack after j reads, OPU( L ) = the letter of the j-th read.
def OPF(L, X):
    return ('( j e. NN0 |-> if ( j <_ ( # ` %s ) , ( ( ( inclBool o. %s ) substr <. j , ( # ` %s ) >. ) ++ ( <" 4 "> ++ %s ) ) , %s ) )'
            % (L, L, L, X, X))
def OPU(L):
    return '( j e. NN0 |-> if ( j < ( # ` %s ) , <. 1 , ( %s ` j ) >. , 4 ) )' % (L, L)
def OPR(L):
    return '( 0 ... ( # ` %s ) )' % L
def FLG(L, rel, j):
    """[ |L| rel j ] as a bit"""
    return 'if ( ( # ` %s ) %s %s , 1o , (/) )' % (L, rel, j)
def RGV(L, j):
    """the register after the j-th read: some ( L ` j ) or none"""
    return 'if ( %s < ( # ` %s ) , ( inl ` ( %s ` %s ) ) , ( inr ` (/) ) )' % (j, L, L, j)

LX, LY = 'L', "L'"
OPFX, OPFY = OPF(LX, 'X'), OPF(LY, 'Y')
OPUX, OPUY = OPU(LX), OPU(LY)
FAMX = lambda i: '( %s ` %s )' % (OPF('L', 'X'), i)

# the operand-family lemmas (generic in the word L and the rest X)
PH_OP = "( L e. Word 2o /\\ X e. Word Gamma' /\\ N e. NN0 )"
ST_OPTY = "( %s -> ( %s ` N ) e. Word Gamma' )" % (PH_OP, OPFX)
ST_OP0 = "( ( L e. Word 2o /\\ X e. Word Gamma' ) -> ( %s ` 0 ) = ( ( inclBool o. L ) ++ ( <\" 4 \"> ++ X ) ) )" % OPFX
ST_OPE = "( ( ( L e. Word 2o /\\ X e. Word Gamma' ) /\\ ( N e. NN0 /\\ ( # ` L ) < N ) ) -> ( %s ` N ) = X )" % OPFX
ST_OP1 = ("( %s -> ( ( N e. %s -> ( %s ` N ) = ( <\" ( %s ` N ) \"> ++ ( %s ` ( N + 1 ) ) ) ) /\\ "
          "( -. N e. %s -> ( %s ` ( N + 1 ) ) = ( %s ` N ) ) /\\ ( ( %s ` N ) e. Gamma' /\\ ( %s ` ( N + 1 ) ) e. Word Gamma' ) ) )"
          % (PH_OP, OPR('L'), OPFX, OPUX, OPFX, OPR('L'), OPFX, OPFX, OPUX, OPFX))
for _l, _s in [('tmcopty', ST_OPTY), ('tmcop0', ST_OP0), ('tmcope', ST_OPE), ('tmcop1', ST_OP1)]:
    add7(_l, _s)

# the pointwise reads: branch da ( pop K readA ) at iteration N of a state V
def RDIF(F, V, L, N):
    return 'if ( %s e. %s , ( %s ` <. %s , ( inl ` ( %s ` %s ) ) >. ) , %s )' % (N, OPR(L), F, V, OPU(L), N, V)
RD1 = RDIF('TMrdA', 'V', 'L', 'N')
PH_RDA = ("( ( L e. Word 2o /\\ N e. NN0 ) /\\ ( V e. TMSt /\\ ( TMda ` V ) = %s /\\ ( ( # ` L ) < N -> ( TMra ` V ) = ( inr ` (/) ) ) ) )"
          % FLG('L', '<', 'N'))
ST_RDA = ("( %s -> ( %s e. TMSt /\\ ( ( TMda ` %s ) = %s /\\ ( TMra ` %s ) = %s ) /\\ "
          "( ( ( TMcar ` %s ) = ( TMcar ` V ) /\\ ( TMrb ` %s ) = ( TMrb ` V ) ) /\\ ( ( TMdb ` %s ) = ( TMdb ` V ) /\\ ( TMcmp ` %s ) = ( TMcmp ` V ) ) ) ) )"
          % (PH_RDA, RD1, RD1, FLG('L', '<_', 'N'), RD1, RGV('L', 'N'), RD1, RD1, RD1, RD1))
RD2 = RDIF('TMrdB', 'V', 'L', 'N')
PH_RDB = ("( ( L e. Word 2o /\\ N e. NN0 ) /\\ ( V e. TMSt /\\ ( TMdb ` V ) = %s /\\ ( ( # ` L ) < N -> ( TMrb ` V ) = ( inr ` (/) ) ) ) )"
          % FLG('L', '<', 'N'))
ST_RDB = ("( %s -> ( %s e. TMSt /\\ ( ( TMdb ` %s ) = %s /\\ ( TMrb ` %s ) = %s ) /\\ "
          "( ( ( TMcar ` %s ) = ( TMcar ` V ) /\\ ( TMra ` %s ) = ( TMra ` V ) ) /\\ ( ( TMda ` %s ) = ( TMda ` V ) /\\ ( TMcmp ` %s ) = ( TMcmp ` V ) ) ) ) )"
          % (PH_RDB, RD2, RD2, FLG('L', '<_', 'N'), RD2, RGV('L', 'N'), RD2, RD2, RD2, RD2))
add7('tmcrda', ST_RDA)
add7('tmcrdb', ST_RDB)


def mval(w, ph, v, D, X_of, A, amem, xex, force_g=False):
    """( ph -> ( ( v e. D |-> X(v) ) ` A ) = X(A) ); fvmptd when ph and A avoid v, else (or when
    force_g: no $d between v and the antecedent's variables) fvmptg"""
    F = '( %s e. %s |-> %s )' % (v, D, X_of(v))
    idu = w.s([], 'id', '( %s = %s -> %s = %s )' % (v, A, v, A))
    cg, newX = w.congr(X_of(v), {v: A}, '%s = %s' % (v, A), {v: idu})
    assert newX == X_of(A), (newX, X_of(A))
    if force_g or (' %s ' % v) in (' %s ' % ph):
        fe = w.s([], 'eqid', '%s = %s' % (F, F))
        g = w.s([cg, fe], 'fvmptg', '( ( %s e. %s /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (A, D, X_of(A), F, A, X_of(A)))
        return w.s([amem, xex, g], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ph, F, A, X_of(A)))
    da = w.s([], 'eqidd', '( %s -> %s = %s )' % (ph, F, F))
    cga = w.s([cg], 'adantl', '( ( %s /\\ %s = %s ) -> %s = %s )' % (ph, v, A, X_of(v), X_of(A)))
    return w.s([da, cga, amem, xex], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ph, F, A, X_of(A)))


def elexs(w, ph, st, X):
    """( ph -> X e. _V ) from st : ( ph -> X e. A )"""
    return w.s([st], 'elexd', '( %s -> %s e. _V )' % (ph, X))


# ------------------------------------------------------------ add at the machine (T5 D4's families for ~ tm2faddx)
def BIT(L, i):
    """the i-th bit of the value of L (zero past the word): Lean ` bitOf ` of the register"""
    return 'if ( %s e. ( bits ` ( toNat ` %s ) ) , 1o , (/) )' % (i, L)
MXA = "if ( ( # ` L ) <_ ( # ` L' ) , ( # ` L' ) , ( # ` L ) )"
CRS = "( majBit ( ( toNat ` L ) bwFold ( toNat ` L' ) ) (/) )"
SUMV = "( ( ( toNat ` L ) + ( toNat ` L' ) ) + ( bToNat ` (/) ) )"
ZS = '( inclBool o. ( %s bwrd %s ) )' % (SUMV, MXA)
WA = "( inclBool o. ( ( L addBits L' ) ` (/) ) )"
def NFC(C):
    return ("( j e. NN0 |-> { h e. TMSt | ( ( ( TMcar ` h ) = ( %s ` j ) /\\ ( TMda ` h ) = %s /\\ ( TMdb ` h ) = %s ) /\\ "
            "( ( ( # ` L ) < j -> ( TMra ` h ) = ( inr ` (/) ) ) /\\ ( ( # ` L' ) < j -> ( TMrb ` h ) = ( inr ` (/) ) ) ) ) } )"
            % (C, FLG('L', '<', 'j'), FLG("L'", '<', 'j')))
def OFC(C):
    return ("( j e. NN0 |-> { h e. TMSt | ( ( ( TMcar ` h ) = ( %s ` j ) /\\ ( TMda ` h ) = %s /\\ ( TMdb ` h ) = %s ) /\\ "
            "( ( TMra ` h ) = %s /\\ ( TMrb ` h ) = %s ) ) } )"
            % (C, FLG('L', '<_', 'j'), FLG("L'", '<_', 'j'), RGV('L', 'j'), RGV("L'", 'j')))
NFG, OFG = NFC('C'), OFC('C')
NFA, OFA = NFC(CRS), OFC(CRS)
CANDD = CAND('da', 'db')
PH_LL = "( L e. Word 2o /\\ L' e. Word 2o )"
RDN1 = RDIF('TMrdA', 'n', 'L', 'i')
RDN2 = RDIF('TMrdB', RDN1, "L'", 'i')
ST_ADRD = ("( %s -> A. i e. NN0 A. n e. ( %s ` i ) ( ( ( TMda ` n ) = 1o <-> -. i e. %s ) /\\ ( ( TMdb ` %s ) = 1o <-> -. i e. %s ) /\\ %s e. ( %s ` i ) ) )"
           % (PH_LL, NFG, OPR('L'), RDN1, OPR("L'"), RDN2, OFG))
ST_ADSS = ("( ( 2nd ` T ) = TMSt -> A. i e. NN0 ( ( %s ` i ) C_ ( 2nd ` T ) /\\ ( %s ` i ) C_ ( 2nd ` T ) ) )" % (NFG, OFG))
ST_ADIN = ("( ( ( 2nd ` T ) = TMSt /\\ %s /\\ ( C ` 0 ) = (/) ) -> A. r e. ( 2nd ` T ) ( %s ` r ) e. ( %s ` 0 ) )" % (PH_LL, LADD0, NFG))
ST_ADC0 = "( %s -> ( %s ` 0 ) = (/) )" % (PH_LL, CRS)
ST_BRG = "( ( L e. Word 2o /\\ N e. NN0 ) -> ( bitOf ` %s ) = %s )" % (RGV('L', 'N'), BIT('L', 'N'))
ST_2OIF = '( ( A e. 2o /\\ ( A = 1o <-> ph ) ) -> A = if ( ph , 1o , (/) ) )'
ST_ADSUM = ("( ( %s /\\ N e. NN0 ) -> ( ( %s sumBit %s ) ` ( %s ` N ) ) = if ( N e. ( bits ` %s ) , 1o , (/) ) )"
            % (PH_LL, BIT('L', 'N'), BIT("L'", 'N'), CRS, SUMV))
ST_ADCP = ("( ( %s /\\ N e. NN0 ) -> ( %s ` ( N + 1 ) ) = ( ( %s majBit %s ) ` ( %s ` N ) ) )"
           % (PH_LL, CRS, BIT('L', 'N'), BIT("L'", 'N'), CRS))
ST_ADZL = "( %s -> ( # ` %s ) = %s )" % (PH_LL, ZS, MXA)
ST_ADZV = ("( ( %s /\\ N e. ( 0 ..^ %s ) ) -> ( %s ` N ) = <. 1 , if ( N e. ( bits ` %s ) , 1o , (/) ) >. )"
           % (PH_LL, MXA, ZS, SUMV))
ST_ADBD = ("( %s -> A. i e. ( 0 ..^ ( # ` %s ) ) A. p e. ( %s ` i ) ( -. ( %s ` p ) = 1o /\\ ( %s ` p ) = ( %s ` i ) /\\ ( %s ` p ) e. ( %s ` ( i + 1 ) ) ) )"
           % (PH_LL, ZS, OFA, CANDD, PSUM, ZS, LMAJ, NFA))
C11 = "( ( 2nd ` T ) X. { <. 1 , 1o >. } )"
ST_ADFL = ("( ( ( 2nd ` T ) = TMSt /\\ %s ) -> ( ( A. p e. ( %s ` ( # ` %s ) ) ( ( ( %s ` p ) = 1o /\\ ( TMcar ` p ) = 1o ) /\\ ( ( %s ` p ) = <. 1 , 1o >. /\\ p e. TMSt ) ) /\\ %s = ( %s ++ <\" <. 1 , 1o >. \"> ) ) \\/ "
           "( A. p e. ( %s ` ( # ` %s ) ) ( ( %s ` p ) = 1o /\\ -. ( TMcar ` p ) = 1o /\\ p e. TMSt ) /\\ %s = %s ) ) )"
           % (PH_LL, OFA, ZS, CANDD, C11, WA, ZS, OFA, ZS, CANDD, WA, ZS))
for _l, _s in [('tmcadrd', ST_ADRD), ('tmcadss', ST_ADSS), ('tmcadin', ST_ADIN), ('tmcadc0', ST_ADC0), ('tmcbrg', ST_BRG),
               ('tmc2oif', ST_2OIF), ('tmcadsum', ST_ADSUM), ('tmcadcp', ST_ADCP), ('tmcadzl', ST_ADZL), ('tmcadzv', ST_ADZV),
               ('tmcadbd', ST_ADBD), ('tmcadfl', ST_ADFL)]:
    add7(_l, _s)


def load_val(w, ph, kw_of, A, amem, clmap=None):
    """the load ( u e. TMSt |-> SETF( u , kw_of( u ) ) ) at the state A (A free of u): value,
    membership and field values, as rd_bit; clmap maps a set component's text to its closure step"""
    clmap = clmap or {}
    X_of = lambda t: SETF(t, **kw_of(t))
    val = lamval(w, ph, X_of, A, amem, closed(w, ph, 'opex', '%s e. _V' % X_of(A)))
    kw = kw_of(A)
    cl = st_comps(w, ph, A, amem)
    comps = [kw.get(f, FLD(f, A)) for f in ORDER]
    cls = []
    for f, comp in zip(ORDER, comps):
        if f not in kw:
            cls.append(cl[f])
        elif comp in clmap:
            cls.append(clmap[comp])
        elif comp == '(/)' and CODOM[f] == '2o':
            cls.append(closed(w, ph, '0el2o', '(/) e. 2o'))
        elif comp == '1o' and CODOM[f] == '2o':
            cls.append(closed(w, ph, '1oel2o', '1o e. 2o'))
        elif comp == NONE:
            z1 = w.s([], '0lt1o', '(/) e. 1o')
            m = w.s([z1, w.inst('djurcl')], 'ax-mp', '%s e. %s' % (NONE, OPTB))
            cls.append(w.s([m], 'a1i', '( %s -> %s e. %s )' % (ph, NONE, OPTB)))
        else:
            raise KeyError('no closure for %s := %s' % (f, comp))
    mem, vals = tuple_facts(w, ph, comps, cls)
    N = '( ( u e. TMSt |-> %s ) ` %s )' % (X_of('u'), A)
    return _transport(w, ph, N, val, mem, vals, comps)


# ------------------------------------------------------------ class families ( j e. NN0 |-> { h e. TMSt | cond( h , j ) } )
def NCOND(C):
    return lambda h, j: ("( ( ( TMcar ` %s ) = ( %s ` %s ) /\\ ( TMda ` %s ) = %s /\\ ( TMdb ` %s ) = %s ) /\\ "
                         "( ( ( # ` L ) < %s -> ( TMra ` %s ) = ( inr ` (/) ) ) /\\ ( ( # ` L' ) < %s -> ( TMrb ` %s ) = ( inr ` (/) ) ) ) )"
                         % (h, C, j, h, FLG('L', '<', j), h, FLG("L'", '<', j), j, h, j, h))
def OCOND(C):
    return lambda h, j: ("( ( ( TMcar ` %s ) = ( %s ` %s ) /\\ ( TMda ` %s ) = %s /\\ ( TMdb ` %s ) = %s ) /\\ "
                         "( ( TMra ` %s ) = %s /\\ ( TMrb ` %s ) = %s ) )"
                         % (h, C, j, h, FLG('L', '<_', j), h, FLG("L'", '<_', j), h, RGV('L', j), h, RGV("L'", j)))
assert NFC('C') == '( j e. NN0 |-> { h e. TMSt | %s } )' % NCOND('C')('h', 'j')
assert OFC('C') == '( j e. NN0 |-> { h e. TMSt | %s } )' % OCOND('C')('h', 'j')


def rabV(w, ph, rab):
    sv = w.s([w.s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
    return w.s([w.s([sv], 'rabex', '%s e. _V' % rab)], 'a1i', '( %s -> %s e. _V )' % (ph, rab))


def famval(w, ph, cond, i, inn):
    """( ph -> ( ( j e. NN0 |-> { h e. TMSt | cond( h , j ) } ) ` i ) = { h e. TMSt | cond( h , i ) } )"""
    X_of = lambda t: '{ h e. TMSt | %s }' % cond('h', t)
    return mval(w, ph, 'j', 'NN0', X_of, i, inn, rabV(w, ph, X_of(i)))


def fam_unpack(w, ph, cond, i, inn, x, xin):
    """from xin : ( ph -> x e. ( FAM ` i ) ): steps ( ph -> x e. TMSt ), ( ph -> cond( x , i ) )"""
    FAM = '( j e. NN0 |-> { h e. TMSt | %s } )' % cond('h', 'j')
    fv = famval(w, ph, cond, i, inn)
    rab = '{ h e. TMSt | %s }' % cond('h', i)
    e = w.s([xin, fv], 'eleqtrd', '( %s -> %s e. %s )' % (ph, x, rab))
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (x, x))
    cg, new = w.wcongr(cond('h', i), {'h': x}, 'h = %s' % x, {'h': idh})
    assert new == cond(x, i), (new, cond(x, i))
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (x, rab, x, cond(x, i)))
    both = w.s([e, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ph, x, cond(x, i)))
    return (w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (ph, x)),
            w.s([both], 'simprd', '( %s -> %s )' % (ph, cond(x, i))))


def fam_pack(w, ph, cond, i, inn, x, xmem, cstep):
    """( ph -> x e. ( FAM ` i ) )"""
    FAM = '( j e. NN0 |-> { h e. TMSt | %s } )' % cond('h', 'j')
    fv = famval(w, ph, cond, i, inn)
    rab = '{ h e. TMSt | %s }' % cond('h', i)
    r = rab_in(w, ph, rab, lambda t: cond(t, i), x, xmem, cstep)
    return w.s([r, fv], 'eleqtrrd', '( %s -> %s e. ( %s ` %s ) )' % (ph, x, FAM, i))


def parts(w, ph, st, tree):
    """the leaves of a conjunction tree proved by st : ( ph -> cj( tree ) ), as a dict text -> step"""
    out = {}
    def go(s, t):
        if isinstance(t, str):
            out[t] = s; return
        if len(t) == 2:
            go(w.s([s], 'simpld', '( %s -> %s )' % (ph, cj(t[0]))), t[0])
            go(w.s([s], 'simprd', '( %s -> %s )' % (ph, cj(t[1]))), t[1])
        else:
            for k, ref in enumerate(['simp1d', 'simp2d', 'simp3d']):
                go(w.s([s], ref, '( %s -> %s )' % (ph, cj(t[k]))), t[k])
    go(st, tree)
    return out


def ncond_tree(C, h, j):
    return ((('( TMcar ` %s ) = ( %s ` %s )' % (h, C, j)), ('( TMda ` %s ) = %s' % (h, FLG('L', '<', j))), ('( TMdb ` %s ) = %s' % (h, FLG("L'", '<', j)))),
            ('( ( # ` L ) < %s -> ( TMra ` %s ) = ( inr ` (/) ) )' % (j, h), "( ( # ` L' ) < %s -> ( TMrb ` %s ) = ( inr ` (/) ) )" % (j, h)))
def ocond_tree(C, h, j):
    return ((('( TMcar ` %s ) = ( %s ` %s )' % (h, C, j)), ('( TMda ` %s ) = %s' % (h, FLG('L', '<_', j))), ('( TMdb ` %s ) = %s' % (h, FLG("L'", '<_', j)))),
            ('( TMra ` %s ) = %s' % (h, RGV('L', j)), '( TMrb ` %s ) = %s' % (h, RGV("L'", j))))
assert cj(ncond_tree('C', 'h', 'j')) == NCOND('C')('h', 'j') and cj(ocond_tree('C', 'h', 'j')) == OCOND('C')('h', 'j')


# ------------------------------------------------------------ the field tests and the in-place adder
ST_FLTY = ('( ( 2nd ` T ) = TMSt -> ( ( TMcar e. ( 2o ^m ( 2nd ` T ) ) /\\ TMda e. ( 2o ^m ( 2nd ` T ) ) ) /\\ '
           '( TMdb e. ( 2o ^m ( 2nd ` T ) ) /\\ TMfl e. ( 2o ^m ( 2nd ` T ) ) ) ) )')
add7('tmcflty', ST_FLTY)
C11 = "( ( 2nd ` T ) X. { <. 1 , 1o >. } )"
ADD_MAP = {'C': 'TMda', "C'": 'TMdb', 'C"': CANDD, 'C0': 'TMcar', 'C1_': CIS, 'F': 'TMrdA', "F'": 'TMrdB', 'F"': 'TMrdA',
           'P': PSUM, "P'": C11, 'P"': PBR, 'G': LMAJ, 'L': LADD0, 'Q': '4', 'B': BITS, 'Z': ZS, "Z'": '<. 1 , 1o >.', 'W': WA,
           'N0': '( 2nd ` T )', "N'": 'TMSt', 'N': NFA, 'O': OFA, 'X': OPFX, 'Y': OPFY, 'U': OPUX, "U'": OPUY,
           'R': OPR('L'), "R'": OPR("L'")}


def prog_of(label, m, keys):
    """the program equations (leaves ( M ` X ) = ... ) of a generic theorem under the map m, in the order of keys"""
    ante, _ = split_imp(stmt(label))
    leaves = {}
    def go(t):
        if isinstance(t, str):
            if t.startswith('( M ` '):
                lab = t.split()[3]
                leaves[lab] = tsub_text(t, m)
            return
        for x in t:
            go(x)
    go(parse_conj(ante))
    return [leaves[k] for k in keys]


def PROG_ADDX():
    a1, a0, e0, e1 = prog_of('tm2faddx', ADD_MAP, ["A'", 'A', 'E', "E'"])
    return ((a1, a0), (e0, e1))
LABS_ADD = ((LAB("A'"), LAB('A')), (LAB('E'), LAB("E'"), LAB('E"')))
DATA_ADD = (((WRD('L', '2o'), WRD("L'", '2o')), (WRD('X', GAM), WRD('Y', GAM), STKD('D'))),
            ('( D ` K ) = ( ( inclBool o. L ) ++ ( <" 4 "> ++ X ) )', "( D ` J ) = ( ( inclBool o. L' ) ++ ( <\" 4 \"> ++ Y ) )"))
def TREE_ADDX():
    return ((T_PHM7, PROG_ADDX()), (LABS_ADD, (IDX('K'), IDX('J'), IDX('I')), ('K =/= J', 'K =/= I', 'J =/= I')), DATA_ADD)
CONCL_ADDX = TRI(CLN("A'", SS, 'D'), CLN('E"', SS, UP(UP('D', 'K', CC(WA, '( <" 4 "> ++ X )')), 'J', 'Y')), '( ( 2 x. %s ) + 5 )' % MXA)
try:
    add7('tmcaddx', statement(TREE_ADDX(), CONCL_ADDX))
except Exception as _e:   # the database statement of tm2faddx is needed
    pass


# ------------------------------------------------------------ the multiplication accumulator (Lean ` mulGo [] xs ( take i ys ) ` )
SHF = lambda t: '( ( (/) repeatS %s ) ++ L )' % t
STEPB = lambda a, b: "if ( ( L' ` %s ) = 1o , ( ( %s addBits ( ( (/) repeatS %s ) ++ L ) ) ` (/) ) , %s )" % (b, a, b, a)
STEPF = '( a e. _V , b e. _V |-> %s )' % STEPB('a', 'b')
STEPG = '( c e. _V , d e. _V |-> %s )' % STEPB('c', 'd')
INITB = lambda t: 'if ( %s = 0 , (/) , ( %s - 1 ) )' % (t, t)
INITF = '( k e. NN0 |-> %s )' % INITB('k')
ACCF = 'seq 0 ( %s , %s )' % (STEPF, INITF)
ACCN = lambda t: '( %s ` %s )' % (ACCF, t)
ST_ACC0 = '%s = (/)' % ACCN('0')
ST_ACCS = '( N e. NN0 -> %s = %s )' % (ACCN('( N + 1 )'), STEPB(ACCN('N'), 'N'))
def PACC(t):
    return ("( ( %s e. Word 2o /\\ ( # ` %s ) <_ ( ( # ` L ) + %s ) ) /\\ ( %s <_ ( # ` L' ) -> ( toNat ` %s ) = ( ( toNat ` L ) x. ( toNat ` ( L' prefix %s ) ) ) ) )"
            % (ACCN(t), ACCN(t), t, t, ACCN(t), t))
ST_ACC = '( ( %s /\\ N e. NN0 ) -> %s )' % (PH_LL, PACC('N'))
for _l, _s in [('tmcacc0', ST_ACC0), ('tmcaccs', ST_ACCS), ('tmcacc', ST_ACC)]:
    add7(_l, _s)


# ------------------------------------------------------------ the multiplication's per-iteration composite ( dup x t s ; add w t s w )
# stacks: K = x , I = w (accumulator) , I" = t (the copy) , I' = s (scratch)
ML_DUP = {'K': 'K', 'J': 'I"', 'I': "I'", 'A': "B'", "A'": "G'", 'A"': 'G"', "E'": "Q'", 'E"': 'Q"', 'E': 'Q0'}
ML_ADD = {'K': 'I', 'J': 'I"', 'I': "I'", "A'": 'Q0', 'A': 'G0', 'E': "O'", "E'": 'O0', 'E"': 'B"'}
def PROG_MLTR():
    pd = tsub(PROG_DUP, ML_DUP)
    pa = tsub(PROG_ADDX(), ML_ADD)
    return (pd, pa)
LABS_MLTR = ((LAB("B'"), LAB("G'"), LAB('G"')), (LAB("Q'"), LAB('Q"'), LAB('Q0')), ((LAB('G0'), LAB("O'")), (LAB('O0'), LAB('B"'))))
IDX_ML4 = ((IDX('K'), IDX('I')), (IDX("I'"), IDX('I"')))
DIST_ML4 = (('K =/= I', "K =/= I'", 'K =/= I"'), ("I =/= I'", 'I =/= I"', 'I" =/= I\''))
DATA_MLTR = (((WRD('L', '2o'), WRD("L'", '2o')), (WRD('X', GAM), WRD('Y', GAM), STKD('D'))),
             ("( D ` K ) = ( ( inclBool o. L' ) ++ ( <\" 4 \"> ++ X ) )", '( D ` I ) = ( ( inclBool o. L ) ++ ( <" 4 "> ++ Y ) )'))
def TREE_MLTR():
    return ((T_PHM7, PROG_MLTR()), (LABS_MLTR, IDX_ML4, DIST_ML4), DATA_MLTR)
BND_MLTR = "( ( ( 2 x. ( # ` L' ) ) + 5 ) + ( ( 2 x. %s ) + 5 ) )" % MXA
CONCL_MLTR = TRI(CLN("B'", SS, 'D'), CLN('B"', SS, UP('D', 'I', CC(WA, '( <" 4 "> ++ Y )'))), BND_MLTR)
try:
    add7('tmcmltr', statement(TREE_MLTR(), CONCL_MLTR))
except Exception:
    pass
