"""Sortie T6b: the remainder of TM/Lists.lean (appendList, the N-level and
B forms, copyList, listLen, the length lemmas).

Statement texts and helpers on top of tools/t6lib.py and the antecedent
pieces of tools/gen/t6_f_mes.py (PHS of ~ tm2lmes).  Every frozen statement
of T6b-blueprint.md is produced by a function here (`STMTS`), so that the
blueprint, the grammar check and the generators use one text.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t6lib import *
from t6_f_mes import (prelude, PHS, PHM6, PROG, PROG1, PROG2, PROG3, LAB, IDX, HNDS, NSS2, IFS,
                      IFACE, MIFACE, HPOP, IF1, IF2, MI1, MI2, DATA, NL, DFIN, NFIN, YB, FT, CT,
                      PTY, NVF, MOVEP, PEEKS, TESTS, PDEF, PJ, RP, EJ, lstcl, ejcl, pjcl, pval)
import lin
lin.FASTPATH = True
from lin import lineq, linarith

LT = L('T')
SS = S('T')
STK_T = STK('T')
REVL = '( reverse ` L )'
NLR = '( # ` ( reverse ` L ) )'
TMB = '( TMB ` B )'


def ENC(X): return '( encList ` %s )' % X
def RALW(Lx, Bx='B'): return 'A. w e. ran %s ( # ` w ) <_ %s' % (Lx, Bx)
def RALA(Lx, Bx='B'): return 'A. a e. ran %s a < ( 2 ^ %s )' % (Lx, Bx)
def PT(X): return "%s e. ( Gamma' ^m %s )" % (X, SS)
def ELL(*names): return '( ' + ' /\\ '.join('%s e. %s' % (n, LT) for n in names) + ' )'
def MV2(A, I, F, C, K, P, J, O, E):
    """T5's move2Num statement (dup's last stage) at label A: pop I with F,
    branch C, push K with P then J with O, back to A; exit E"""
    return POP(I, F, BRANCH(C, PUSH(K, P, PUSH(J, O, GOTOL(A))), GOTOL(E)))


# ------------------------------------------------ interfaces at a state class

def IFACE_AT(Nc):
    """tm2lfe's peek interface at the state class Nc (decision 3 of T6)"""
    a = 'A. r e. %s A. z e. %s ( %s e. %s /\\ ( C ` %s ) = 1o )' % (Nc, B4, NVF('F', 'r', 'z'), Nc, NVF('F', 'r', 'z'))
    b = 'A. r e. %s ( %s e. %s /\\ -. ( C ` %s ) = 1o )' % (Nc, NVF('F', 'r', '2'), Nc, NVF('F', 'r', '2'))
    return '( %s /\\ %s )' % (a, b)


def MIFACE_AT(Nc):
    """the mover interface of tm2lme/tm2lmes at the state class Nc"""
    a = "A. r e. %s A. z e. %s ( ( C' ` %s ) = 1o /\\ ( P ` %s ) = z /\\ %s e. %s )" % (Nc, BITS, NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'), Nc)
    b = "A. r e. %s ( -. ( C' ` %s ) = 1o /\\ %s e. %s )" % (Nc, NVF("F'", 'r', '4'), NVF("F'", 'r', '4'), Nc)
    return '( %s /\\ %s )' % (a, b)


def HPOP_AT(Nc, N2):
    return "A. r e. %s %s e. %s" % (Nc, NVF('F"', 'r', '2'), N2)


assert IFACE_AT('N') == IFACE and MIFACE_AT('N') == MIFACE and HPOP_AT('N', "N'") == HPOP

# dup's move2Num interface (T5's HCmv2/HEmv2 at F' := F0, C := C', P' := P', O := O,
# B := Bits, Y := 4, over the all-states class)
HCMV2 = ("A. r e. %s A. z e. %s ( ( C' ` %s ) = 1o /\\ ( P' ` %s ) = z /\\ ( O ` %s ) = z )"
         % (SS, BITS, NVF('F0', 'r', 'z'), NVF('F0', 'r', 'z'), NVF('F0', 'r', 'z')))
HEMV2 = "A. r e. %s -. ( C' ` %s ) = 1o" % (SS, NVF('F0', 'r', '4'))
HDUP = '( %s /\\ %s )' % (HCMV2, HEMV2)
# dup's mover interface (derived from MIFACE_AT(S) inside the proofs)
HCMOV = "A. r e. %s A. z e. %s ( ( C' ` %s ) = 1o /\\ ( P ` %s ) = z )" % (SS, BITS, NVF("F'", 'r', 'z'), NVF("F'", 'r', 'z'))
HEMOV = "A. r e. %s -. ( C' ` %s ) = 1o" % (SS, NVF("F'", 'r', '4'))

# ------------------------------------------------------------- tm2lrev2

AH2 = '( P0 e. %s /\\ ( M ` P0 ) = %s )' % (LT, PSH('J', '2', 'P1'))
PHR2 = '( %s /\\ %s )' % (PHS, AH2)
RFIN = UPDT(UPDT('D', 'K', 'R'), 'J', '( %s ++ ( D ` J ) )' % ENCB(REVL))
BREV = '( ( %s x. ( ( 2 x. B ) + 6 ) ) + 4 )' % NL
ST_REV2 = '( %s -> %s )' % (PHR2, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E', "N'", RFIN), BREV))

# ------------------------------------------------------------- tm2lapp

# stage 1 = revList K I' I with the push label P0, exiting at H"
PROG3R = "( ( M ` B\" ) = %s /\\ ( M ` Q' ) = %s /\\ ( M ` E' ) = %s )" % (PSH("I'", '4', "Q'"), MOVEP("Q'", 'I', "I'", 'A"'), POPL('K', 'F"', 'H"'))
PROGR = '( %s /\\ %s /\\ %s )' % (PROG1, PROG2, PROG3R)
PROGA1 = '( ( M ` P0 ) = %s /\\ %s )' % (PSH("I'", '2', 'P1'), PROGR)
# stage 2 = moveEntries I' J I: H" peek, A0 test, B0 body entry, C0 peek after the body,
# D0 E0 F0 the body's other labels, G0 the pop; exit E (tm2lmes at P1 A A' A" B' B" Q' E')
PEEK2 = PEEKL("I'", 'F', 'A0')
TEST2 = TESTL('C', 'B0', 'G0')
PROGM1 = '( ( M ` H" ) = %s /\\ ( M ` A0 ) = %s /\\ ( M ` C0 ) = %s )' % (PEEK2, TEST2, PEEK2)
PROGM2 = "( ( M ` B0 ) = %s /\\ ( M ` D0 ) = %s )" % (PSH('I', '4', 'D0'), MOVEP('D0', "I'", 'I', 'E0'))
PROGM3 = "( ( M ` E0 ) = %s /\\ ( M ` F0 ) = %s /\\ ( M ` G0 ) = %s )" % (PSH('J', '4', 'F0'), MOVEP('F0', 'I', 'J', 'C0'), POPL("I'", 'F"', 'E'))
PROGA2 = '( %s /\\ %s /\\ %s )' % (PROGM1, PROGM2, PROGM3)
PROGA = '( %s /\\ %s )' % (PROGA1, PROGA2)
LABR = LAB.replace('E e. %s' % LT, 'H" e. %s' % LT)      # tm2lmes's labels with the exit P2
LABM = '( %s /\\ %s /\\ %s )' % (ELL('H"', 'A0', 'B0'), ELL('C0', 'D0', 'E0'), ELL('F0', 'G0', 'E'))
LABA = '( ( %s /\\ P0 e. %s ) /\\ %s )' % (LABR, LT, LABM)
IDXA = ("( ( ( K e. %s /\\ J e. %s ) /\\ ( I e. %s /\\ I' e. %s ) ) /\\ ( ( K =/= J /\\ K =/= I /\\ K =/= I' ) /\\ ( J =/= I /\\ J =/= I' /\\ I =/= I' ) ) )"
        % (FZ8, FZ8, FZ8, FZ8))
NSSA = 'N C_ %s' % SS
HPOPN = HPOP_AT('N', 'N')
IFSA = '( %s /\\ %s /\\ %s )' % (IFACE, MIFACE, HPOPN)
DATAA = ("( ( D e. %s /\\ ( ( D ` K ) = %s /\\ ( D ` J ) = %s ) ) /\\ ( ( L e. %s /\\ U e. %s ) /\\ ( R e. %s /\\ R' e. %s ) ) /\\ ( B e. NN0 /\\ %s ) )"
         % (STK_T, LST('L', 'R'), LST('U', "R'"), WWB, WWB, WG, WG, RALW('L')))
PHA = '( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) /\\ %s )' % (PHM6, PROGA, LABA, IDXA, HNDS, NSSA, IFSA, DATAA)
AFIN = UPDT(UPDT('D', 'K', 'R'), 'J', LST('( L ++ U )', "R'"))
BAPP = '( ( %s x. ( ( 4 x. B ) + ; 1 2 ) ) + 7 )' % NL
ST_APP = '( %s -> %s )' % (PHA, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E', 'N', AFIN), BAPP))

# ------------------------------------------------------------- helpers

ST_RNREV = '( L e. Word A -> ran ( reverse ` L ) C_ ran L )'
ST_RNENC = '( ( L e. Word NN0 /\\ B e. NN0 /\\ %s ) -> %s )' % (RALA('L'), RALW('( encNatGam o. L )'))
ST_LISTB = ('( ( ( N e. NN0 /\\ B e. NN0 ) /\\ ( C e. NN0 /\\ D e. NN0 ) /\\ ( C <_ ( ; 6 4 x. ( B + 2 ) ) /\\ D <_ ( ; 6 4 x. ( B + 2 ) ) ) ) '
            '-> ( ( N x. C ) + D ) <_ ( ( N + 1 ) x. %s ) )' % TMB)

# ------------------------------------------------------------- N-level forms

DATAN = ("( ( D e. %s /\\ ( D ` K ) = ( %s ++ R ) ) /\\ ( L e. Word NN0 /\\ R e. %s ) /\\ ( B e. NN0 /\\ %s ) )"
         % (STK_T, ENC('L'), WG, RALA('L')))
PHSN = PHS.replace(DATA, DATAN)
assert PHSN != PHS
PHRN = '( %s /\\ %s )' % (PHSN, AH2)
RFINN = UPDT(UPDT('D', 'K', 'R'), 'J', '( %s ++ ( D ` J ) )' % ENC(REVL))
BLB = '( ( %s + 1 ) x. %s )' % (NL, TMB)
ST_REVN = '( %s -> %s )' % (PHRN, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E', "N'", RFINN), BREV))
ST_REVB = '( %s -> %s )' % (PHRN, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E', "N'", RFINN), BLB))
DATAAN = ("( ( D e. %s /\\ ( ( D ` K ) = ( %s ++ R ) /\\ ( D ` J ) = ( %s ++ R' ) ) ) /\\ ( ( L e. Word NN0 /\\ U e. Word NN0 ) /\\ ( R e. %s /\\ R' e. %s ) ) /\\ ( B e. NN0 /\\ %s ) )"
          % (STK_T, ENC('L'), ENC('U'), WG, WG, RALA('L')))
PHAN = PHA.replace(DATAA, DATAAN)
assert PHAN != PHA
AFINN = UPDT(UPDT('D', 'K', 'R'), 'J', '( %s ++ R\' )' % ENC('( L ++ U )'))
ST_APPN = '( %s -> %s )' % (PHAN, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E', 'N', AFINN), BAPP))
ST_APPB = '( %s -> %s )' % (PHAN, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E', 'N', AFINN), BLB))

# ------------------------------------------------------------- length lemmas

ST_ENTLEN = '( ( L e. %s /\\ M e. NN0 /\\ %s ) -> ( # ` %s ) <_ ( ( # ` L ) x. ( M + 1 ) ) )' % (WWB, RALW('L', 'M'), ENT('L'))
ST_ENCBLEN = '( ( L e. %s /\\ M e. NN0 /\\ %s ) -> ( # ` %s ) <_ ( ( ( # ` L ) x. ( M + 1 ) ) + 1 ) )' % (WWB, RALW('L', 'M'), ENCB('L'))
ST_ENCLEN = '( ( L e. Word NN0 /\\ B e. NN0 /\\ %s ) -> ( # ` %s ) <_ ( ( ( # ` L ) x. ( B + 1 ) ) + 1 ) )' % (RALA('L'), ENC('L'))

# ------------------------------------------------------------- copyList

# the body: moveEntry I' K I (labels B0 D0 E0 F0 -> H0) then dup K J I (labels H0 I0 J0 K0 L0 -> C0)
PROGB1 = ("( ( ( M ` B0 ) = %s /\\ ( M ` D0 ) = %s ) /\\ ( ( M ` E0 ) = %s /\\ ( M ` F0 ) = %s ) )"
          % (PSH('I', '4', 'D0'), MOVEP('D0', "I'", 'I', 'E0'), PSH('K', '4', 'F0'), MOVEP('F0', 'I', 'K', 'H0')))
MV2L = MV2('L0', 'I', 'F0', "C'", 'K', "P'", 'J', 'O', 'C0')
PROGB2 = ("( ( ( M ` H0 ) = %s /\\ ( M ` I0 ) = %s ) /\\ ( ( M ` J0 ) = %s /\\ ( M ` K0 ) = %s /\\ ( M ` L0 ) = %s ) )"
          % (PSH('I', '4', 'I0'), MOVEP('I0', 'K', 'I', 'J0'), PSH('K', '4', 'K0'), PSH('J', '4', 'L0'), MV2L))
PROGB = '( %s /\\ %s )' % (PROGB1, PROGB2)
LABB = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (ELL('B0', 'C0', 'D0'), ELL('E0', 'F0', 'H0'), ELL('I0', 'J0'), ELL('K0', 'L0'))
HNDSB = '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) )' % (FT("F'"), FT('F0'), CT("C'"), PT('P'), PT("P'"), PT('O'))
MIFS = MIFACE_AT(SS)
IFSB = '( %s /\\ %s )' % (MIFS, HDUP)
DATAB = '( ( D e. %s /\\ ( D ` I\' ) = ( W ++ ( <" 4 "> ++ X ) ) ) /\\ ( W e. %s /\\ X e. %s ) )' % (STK_T, WB, WG)
PHB = '( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ %s /\\ %s ) /\\ %s )' % (PHM6, PROGB, LABB, IDXA, HNDSB, IFSB, DATAB)
BFIN = UPDT(UPDT(UPDT('D', "I'", 'X'), 'K', '( W ++ ( <" 4 "> ++ ( D ` K ) ) )'), 'J', '( W ++ ( <" 4 "> ++ ( D ` J ) ) )')
BBODY = '( ( 4 x. ( # ` W ) ) + 9 )'
ST_CPYB = '( %s -> %s )' % (PHB, HR(CL('B0', SS, 'D'), 'T', 'M', CL('C0', SS, BFIN), BBODY))

# the composite
PROGC2 = ("( ( ( M ` H\" ) = %s /\\ ( M ` I\" ) = %s ) /\\ ( ( M ` J\" ) = %s /\\ ( M ` A0 ) = %s /\\ ( M ` C0 ) = %s ) /\\ ( M ` G0 ) = %s )"
          % (PSH('K', '2', 'I"'), PSH('J', '2', 'J"'), PEEK2, TEST2, PEEK2, POPL("I'", 'F"', 'E')))
PROGFE = '( ( M ` J" ) = %s /\\ ( M ` A0 ) = %s /\\ ( M ` C0 ) = %s )' % (PEEK2, TEST2, PEEK2)
assert PROGFE in PROGC2
PROGC = '( ( %s /\\ %s ) /\\ %s )' % (PROGA1, PROGC2, PROGB)
LABC2 = '( %s /\\ %s /\\ ( G0 e. %s /\\ E e. %s ) )' % (ELL('H"', 'I"', 'J"'), ELL('A0', 'B0', 'C0'), LT, LT)
LABC = '( ( %s /\\ P0 e. %s ) /\\ %s /\\ %s )' % (LABR, LT, LABC2, LABB)
HNDSC = '( ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) /\\ ( %s /\\ %s /\\ %s ) )' % (FT('F'), FT("F'"), FT('F"'), FT('F0'), CT('C'), CT("C'"), PT('P'), PT("P'"), PT('O'))
NSSC = "N' C_ %s" % SS
IFSC = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (IFACE_AT(SS), MIFS, HPOP_AT(SS, "N'"), HDUP)
PHC = '( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) /\\ %s )' % (PHM6, PROGC, LABC, IDXA, HNDSC, NSSC, IFSC, DATA)
CFIN = UPDT('D', 'J', '( %s ++ ( D ` J ) )' % ENCB('L'))
D3C = UPDT(UPDT(UPDT('D', 'K', '( <" 2 "> ++ R )'), 'J', '( <" 2 "> ++ ( D ` J ) )'), "I'", LST(REVL, "( D ` I' )"))
BCPYL = '( ( %s x. ( ( 4 x. B ) + ; 1 1 ) ) + 3 )' % NL
BCPY = '( ( %s x. ( ( 6 x. B ) + ; 1 7 ) ) + 9 )' % NL
ST_CPYL = '( %s -> %s )' % (PHC, HR(CL('J"', SS, D3C), 'T', 'M', CL('E', "N'", CFIN), BCPYL))
ST_CPY = '( %s -> %s )' % (PHC, HR(CL('P0', SS, 'D'), 'T', 'M', CL('E', "N'", CFIN), BCPY))
# the loop family of copyList (binder n), over ( 0 ... NLR )
def RPC(j): return '( reverse ` %s )' % PFX(REVL, j)
def AJ(j): return '( %s ++ ( <" 2 "> ++ R ) )' % ENT(RPC(j))
def BJ(j): return '( %s ++ ( <" 2 "> ++ ( D ` J ) ) )' % ENT(RPC(j))
def CJ(j): return LST(DROP(REVL, j), "( D ` I' )")
def PJC(j): return UPDT(UPDT(UPDT('D', 'K', AJ(j)), 'J', BJ(j)), "I'", CJ(j))
PDEFC = '( n e. ( 0 ... %s ) |-> %s )' % (NLR, PJC('n'))

# ------------------------------------------------------------- listLen (frozen)

PROGL1 = '( ( M ` P0 ) = %s /\\ ( ( M ` Q0 ) = %s /\\ %s ) )' % (PSH('J', '4', 'Q0'), PSH("I'", '2', 'P1'), PROGR)
PROGL2 = ("( ( M ` H\" ) = %s /\\ %s /\\ ( M ` G0 ) = %s )" % (PSH('K', '2', 'J"'), PROGFE, POPL("I'", 'F"', 'E')))
PROGL = '( ( %s /\\ %s ) /\\ %s )' % (PROGL1, PROGL2, PROGB1)
LABL2 = '( %s /\\ %s /\\ ( %s /\\ %s ) )' % (ELL('H"', 'J"', 'A0'), ELL('B0', 'C0', 'G0'), ELL('D0', 'E0'), ELL('F0', 'H0'))
LABL = '( ( %s /\\ ( P0 e. %s /\\ Q0 e. %s ) ) /\\ %s /\\ E e. %s )' % (LABR, LT, LT, LABL2, LT)
QTY = '( Q : ( 0 ... %s ) --> %s /\\ ( Q ` 0 ) = <" 4 "> /\\ Y e. NN0 )' % (NL, WG)
HINC = ('A. k e. ( 0 ..^ %s ) A. d e. %s ( ( d ` J ) = ( ( Q ` k ) ++ ( D ` J ) ) -> %s )'
        % (NL, STK_T, HR(CL('H0', 'N', 'd'), 'T', 'M', CL('C0', 'N', UPDT('d', 'J', '( ( Q ` ( k + 1 ) ) ++ ( D ` J ) )')), 'Y')))
DATAL = '( %s /\\ ( %s /\\ %s ) )' % (DATA, QTY, HINC)
PHL = '( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) /\\ %s ) /\\ %s )' % (PHM6, PROGL, LABL, IDXA, HNDS, NSSA, IFSA, DATAL)
LFIN = UPDT('D', 'J', '( ( Q ` %s ) ++ ( D ` J ) )' % NL)
BLEN = '( ( %s x. ( ( ( 4 x. B ) + Y ) + ; 1 2 ) ) + 9 )' % NL
ST_LEN = '( %s -> %s )' % (PHL, HR(CL('P0', 'N', 'D'), 'T', 'M', CL('E', 'N', LFIN), BLEN))

STMTS = {
    'tm2lrev2': ST_REV2, 'tm2lapp': ST_APP,
    'tm2lrnrev': ST_RNREV, 'tm2lrnenc': ST_RNENC, 'tm2llistb': ST_LISTB,
    'tm2lrevn': ST_REVN, 'tm2lrevb': ST_REVB, 'tm2lappn': ST_APPN, 'tm2lappb': ST_APPB,
    'tm2lentlen': ST_ENTLEN, 'tm2lencblen': ST_ENCBLEN, 'tm2lenclen': ST_ENCLEN,
    'tm2lcpyb': ST_CPYB, 'tm2lcpyl': ST_CPYL, 'tm2lcpy': ST_CPY,
    'tm2llen': ST_LEN,
}


# ------------------------------------------------------------- helpers

def A_(w, ante, st, f):
    """( ante -> f ) by adantr"""
    return w.s([st], 'adantr', '( %s -> %s )' % (ante, f))


def lift_all(w, ante, u, big):
    """re-antecede every step of a prelude dict u (proved at the antecedent
    `big`'s left conjunct) to `big` by adantr"""
    out = {}
    for k, v in u.items():
        if isinstance(v, dict):
            out[k] = lift_all(w, ante, v, big)
        else:
            f = formula(w, v)
            f = f[len('( %s -> ' % ante):-2]
            out[k] = w.s([v], 'adantr', '( %s -> %s )' % (big, f))
    return out


def formula(w, st):
    for l in w.lines:
        if l.startswith(st + ':'):
            return l.split('|-', 1)[1].strip()
    raise KeyError(st)


def concl(w, ante, st):
    """the consequent of a step ( ante -> X )"""
    f = formula(w, st)
    assert f.startswith('( %s -> ' % ante), (f[:80], ante[:80])
    return f[len('( %s -> ' % ante):-2]


def nn0lit(w, ante, n):
    """( ante -> n e. NN0 ) for a small numeral"""
    if n in ('0',):
        c = w.s([], '0nn0', '0 e. NN0')
    elif len(n) == 1:
        c = w.s([], '%snn0' % n, '%s e. NN0' % n)
    else:
        raise ValueError(n)
    return w.s([c], 'a1i', '( %s -> %s e. NN0 )' % (ante, n))


def relit(w, ante, n):
    c = w.s([], '%sre' % n, '%s e. RR' % n)
    return w.s([c], 'a1i', '( %s -> %s e. RR )' % (ante, n))


def hle2(w, ante, phm, C, D, N, P, tri, pcl, le):
    return hle(w, ante, phm, C, D, N, P, tri, pcl, le)


def revcl_(w, ante, Lx, lcl, Al=WWB):
    return w.s([lcl], 'revcl', '( %s -> ( reverse ` %s ) e. %s )' % (ante, Lx, Al)) if False else \
        w.s([lcl, w.inst('revcl')], 'syl', '( %s -> ( reverse ` %s ) e. %s )' % (ante, Lx, Al))


def wgk2(w, ante, X, K, ge, xcl):
    return wgk(w, ante, X, K, ge, xcl)


def pop_closure(w, ante, F, tv, fty, Nc, nss):
    """( ante -> A. r e. Nc ( F ` <. r , ( inl ` 2 ) >. ) e. S ) from the typing
    fty : ( ante -> F e. ( S ^m ( S X. ( Gamma' |_| 1o ) ) ) ) and nss : Nc C_ S.
    The antecedent binds r, so the generalisation is over u (T6 trap 1)."""
    ff = w.s([fty, w.inst('elmapi')], 'syl', '( %s -> %s : ( %s X. %s ) --> %s )' % (ante, F, SS, OPT, SS))
    ar = '( %s /\\ u e. %s )' % (ante, Nc)
    ffa = w.s([ff], 'adantr', '( %s -> %s : ( %s X. %s ) --> %s )' % (ar, F, SS, OPT, SS))
    rn = w.s([], 'simpr', '( %s -> u e. %s )' % (ar, Nc))
    nsa = w.s([nss], 'adantr', '( %s -> %s C_ %s )' % (ar, Nc, SS))
    rs = w.s([nsa, rn], 'sseldd', '( %s -> u e. %s )' % (ar, SS))
    g2 = gamlet(w, ar, '2')
    i2 = w.s([g2, w.inst('djulcl')], 'syl', "( %s -> ( inl ` 2 ) e. %s )" % (ar, OPT))
    pr = w.s([rs, i2], 'opelxpd', '( %s -> <. u , ( inl ` 2 ) >. e. ( %s X. %s ) )' % (ar, SS, OPT))
    fv = w.s([ffa, pr], 'ffvelcdmd', '( %s -> %s e. %s )' % (ar, NVF(F, 'u', '2'), SS))
    ru = w.s([fv], 'ralrimiva', '( %s -> A. u e. %s %s e. %s )' % (ante, Nc, NVF(F, 'u', '2'), SS))
    cg, _ = w.wcongr('%s e. %s' % (NVF(F, 'u', '2'), SS), {'u': 'r'}, 'u = r', {'u': w.s([], 'id', '( u = r -> u = r )')})
    cb = w.s([cg], 'cbvralvw', '( A. u e. %s %s e. %s <-> A. r e. %s %s e. %s )' % (Nc, NVF(F, 'u', '2'), SS, Nc, NVF(F, 'r', '2'), SS))
    return w.s([ru, cb], 'sylib', '( %s -> A. r e. %s %s e. %s )' % (ante, Nc, NVF(F, 'r', '2'), SS))


# ------------------------------------------ instantiating a cited theorem

from t5lib import Ctx, cj
import subprocess


def _split_top(toks, sep):
    """split a balanced token list at depth-0 occurrences of `sep`"""
    d = 0; parts = [[]]
    for t in toks:
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        if d == 0 and t == sep:
            parts.append([]); continue
        parts[-1].append(t)
    return [' '.join(p) for p in parts]


def _outer(text):
    """the token list inside the outermost ( ... ) if the text is one group"""
    toks = text.split()
    if toks[0] != '(' or toks[-1] != ')':
        return None
    d = 0
    for i, t in enumerate(toks):
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        if d == 0 and i != len(toks) - 1:
            return None
    return toks[1:-1]


def parse_conj(text):
    """a nested tuple of the top-level conjunction structure of a wff"""
    inner = _outer(text)
    if inner is None:
        return text
    parts = _split_top(inner, '/\\')
    if len(parts) == 1:
        return text
    assert len(parts) in (2, 3), text
    return tuple(parse_conj(p) for p in parts)


def split_imp(text):
    inner = _outer(text)
    parts = _split_top(inner, '->')
    assert len(parts) == 2, text[:100]
    return parts[0], parts[1]


_STMT = {}


def stmt(label):
    """the formula of an assertion of the database (via tools/mm.py grep)"""
    if label not in _STMT:
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        r = subprocess.run([sys.executable, os.path.join(root, 'tools', 'mm.py'), 'grep', '^%s ' % label],
                           cwd=root, capture_output=True, text=True)
        for l in r.stdout.split('\n'):
            if l.startswith(label + ' '):
                _STMT[label] = l.split('|-', 1)[1].strip()
        if label not in _STMT:
            raise KeyError(label)
    return _STMT[label]


def tsub_text(text, m):
    return ' '.join(m.get(t, t) for t in text.split())


def tsub(tree, m):
    if isinstance(tree, str):
        return tsub_text(tree, m)
    return tuple(tsub(t, m) for t in tree)


class Builder:
    """prove ( ph -> cj(tree) ) from leaf steps: `extra` (derived leaves)
    first, then the Ctx of the antecedent; subtrees are memoised by text"""
    def __init__(self, w, ph, ctx, extra=None):
        self.w = w; self.ph = ph; self.ctx = ctx; self.extra = dict(extra or {}); self.memo = {}

    def leaf(self, text):
        if text in self.extra:
            return self.extra[text]
        try:
            return self.ctx[text]
        except KeyError:
            raise KeyError('no step for leaf: ' + text)

    def __call__(self, tree):
        if isinstance(tree, str):
            return self.leaf(tree)
        key = cj(tree)
        if key in self.memo:
            return self.memo[key]
        parts = [self(t) for t in tree]
        st = self.w.s(parts, 'jca' if len(tree) == 2 else '3jca', '( %s -> %s )' % (self.ph, key))
        self.memo[key] = st
        return st


def inst(w, ph, label, m, bld):
    """( ph -> concl[m] ) by the cited theorem `label` at the token
    substitution m, its antecedent rebuilt by `bld`"""
    ante, concl = split_imp(stmt(label))
    tree = tsub(parse_conj(ante), m)
    st = bld(tree)
    c2 = tsub_text(concl, m)
    return w.s([st, w.inst(label)], 'syl', '( %s -> %s )' % (ph, c2)), c2


def triple_parts(text):
    """(C, D, N) of a triple text C ( T TM2Hoare M ) <. D , N >."""
    toks = text.split()
    d = 0
    for i, t in enumerate(toks):
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        if d == 1 and toks[i] == '(' and toks[i + 2] == 'TM2Hoare':
            C = ' '.join(toks[:i]); rest = toks[i + 5:]
            break
    assert rest[0] == '<.' and rest[-1] == '>.'
    dn = _split_top(rest[1:-1], ',')
    assert len(dn) == 2
    return C, dn[0], dn[1]


# ------------------------------------------------- the antecedent trees

GEQ = '( 1st ` ( 1st ` T ) ) = TMGam'
T_PHM6 = (PHM, GEQ)
T_PROG1 = parse_conj(PROG1); T_PROG2 = parse_conj(PROG2); T_PROG3 = parse_conj(PROG3)
T_LAB = parse_conj(LAB); T_IDX = parse_conj(IDX); T_HNDS = parse_conj(HNDS); T_NSS2 = parse_conj(NSS2)
T_IFS = parse_conj(IFS); T_DATA = parse_conj(DATA)
T_PHS = ((T_PHM6, (T_PROG1, T_PROG2, T_PROG3)), ((T_LAB, T_IDX), (T_HNDS, T_NSS2), T_IFS), T_DATA)
assert cj(T_PHS) == PHS
T_PHR2 = (T_PHS, parse_conj(AH2))
assert cj(T_PHR2) == PHR2
T_PHA = parse_conj(PHA)
assert cj(T_PHA) == PHA
T_PHB = parse_conj(PHB); assert cj(T_PHB) == PHB
T_PHC = parse_conj(PHC); assert cj(T_PHC) == PHC
T_PHL = parse_conj(PHL); assert cj(T_PHL) == PHL
T_PHRN = parse_conj(PHRN); assert cj(T_PHRN) == PHRN
T_PHAN = parse_conj(PHAN); assert cj(T_PHAN) == PHAN
