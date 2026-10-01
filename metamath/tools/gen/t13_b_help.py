"""T13: the helper lemmas of the searchF assembly (no machine; short antecedents), T12-HANDOFF "D7 status".

  t13lt2m    ` A < 2 ^ B ` and ` B <_ C ` give ` A < 2 ^ C `
  t13sctmv   ` scalesTM C1 K n ` is the tuple of its projections, with their typing (~ sctmval )
  t13srcty   the typing of the letters ` R I Q L X C' J ` from their equations (~ reservoircl , ~ prodlcl , ~ scancl )
  t13srcsm   the typing in the some case: ` J' W X' ` (~ scandj , ~ extractcl )
  t13srcv    the search value at the letters: the four-way ` if ` of ~ searchval
  t13srcx    the extraction's identification in the some case: ` F = m_R ` , ` A = used_R ` (~ exres , ~ extractval )
  t13srcxb   the extraction's bounds and positivity at ` m_R ` , ` used_R ` (~ t12exbnd , ~ t12expos )
  t13srcxu   the unit facts at the witness list from those at the pool length
  t13srcxl   the post-extraction stack words (the table word, the rest of the pool) and their lengths
  t13srcq    the Q facts: ` # Q = T ` , entries below ` 2 ^ b1 ` and at least 1, ` 1 <_ L ` , ` L X 1 + X ` below ` 2 ^ b1 ` (~ a5q )
  t13srcl2   ` ( L + 1 ) ^ 2 ( 2 ^ T + 2 ) U' <_ W' ` from ` L < 2 ^ ( T bs + 1 ) `
  t13srcu    the units at the pool length ` P ` from the units at ` 2 ^ T ` (Lean's hbMX hBM hE' hB4 hexY hPV hLPV hB5)

    MM_DB=sorties/t13.mm python3 tools/gen/t13_b_help.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t13lib import *
from t9lib import STY, tblw
from t10_n_rgf import tmbn
from t12_i_scal import proj_eq
from lin import linarith, lineq
from cl import Closure
from t10_e_doa import lift_from
import num

SEL = sys.argv[1:]
INR = P.INR
EQ, LEQD, LEQT, SC_TY, VTEQ = P.EQ, P.LEQD, P.LEQT, P.SC_TY, P.VTEQ
S2, E2, W2, CST4, IFQ, HB5, VX4 = P.S2, P.E2, P.W2, P.CST4, P.IFQ, P.HB5, P.VX4
SE = P.SE
MR, USED, TBL, HIT, RIT, WREST, ACCW3, D6V3, NPEQ = P.MR, P.USED, P.TBL, P.HIT, P.RIT, P.WREST, P.ACCW3, P.D6V3, P.NPEQ
P2U, LSQ, EXXU, NPU, VXU, UP1, UP2 = P.P2U, P.LSQ, P.EXXU, P.NPU, P.VXU, P.UP1, P.UP2
XTY = '( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )'

# ------------------------------------------------------------ statements
ST_LT2M = '( ( ( A e. RR /\\ B e. NN0 /\\ C e. NN0 ) /\\ ( B <_ C /\\ A < ( 2 ^ B ) ) ) -> A < ( 2 ^ C ) )'
add13s('t13lt2m', ST_LT2M)

TUPP = '<. <. <. %s , %s >. , <. %s , %s >. >. , %s >.' % (PZ(SC_), PZ99(SC_), PY(SC_), PT(SC_), PTH(SC_))
C_SCTMV = '( %s = %s /\\ ( ( %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN /\\ %s e. NN0 /\\ %s e. NN ) ) )' % (
    SC_, TUPP, PZ(SC_), PZ99(SC_), PY(SC_), PT(SC_), PTH(SC_))
T_SCTMV = ('C e. NN0', 'K e. NN', 'N e. NN0')
add13('t13sctmv', T_SCTMV, C_SCTMV)

T_TY = (SC_TY, LEQT)
C_TY = (('( 1st ` R ) e. Word NN0', '( 2nd ` R ) e. NN0', 'I e. NN0'), ('Q e. Word NN0', 'L e. NN0', '( 2nd ` ( ProdL ` Q ) ) e. NN0'),
        ('X e. NN0', "C' e. NN0", '%s e. NN0' % S2))
add13('t13srcty', T_TY, cj(C_TY))

T_SM = (T_TY, ('( 1st ` J ) =/= %s' % INR, '1 <_ L'))
C_SM = (("J' e. NN0", 'W e. Word NN0', 'L e. NN'), ("X' e. %s" % XTY, '%s e. NN0' % E2))
add13('t13srcsm', T_SM, cj(C_SM))

CST2 = "( C' + %s )" % S2
CST3 = "( ( C' + %s ) + %s )" % (S2, E2)
SV_RHS = ('if ( I < U , <. %s , ( ( 2nd ` R ) + 1 ) >. , if ( ( 1st ` J ) = %s , <. %s , %s >. , if ( ( 1st ` X\' ) = %s , <. %s , %s >. , <. %s , %s >. ) ) )'
          % (INR, INR, INR, CST2, INR, INR, CST3, IFQ, CST4))
add13('t13srcv', T_TY, '%s = %s' % (SE, SV_RHS))

T_X = ((('L e. NN', 'N e. NN0', 'W e. Word NN0'), (EQ("X'"), EQ('F'), EQ('A'))), "( 1st ` X' ) =/= %s" % INR)
C_X = ('F = %s' % MR, 'A = %s' % USED)
add13('t13srcx', T_X, cj(C_X))

T_XB = ((('L e. NN', 'N e. NN0', 'W e. Word NN0'), ("B' e. NN0", 'U e. NN0', NPEQ)),
        ((RALB('W', "B'"), 'A. a e. ran W 2 <_ a'), ('( # ` W ) <_ ( 2 ^ U )', "U < B'")))
C_XB = (('%s e. NN0' % MR, '%s e. Word NN0' % USED), (RALB(USED, "B'"), "( # ` %s ) < ( 2 ^ B' )" % USED, "%s < ( 2 ^ N' )" % MR),
        (('1 <_ %s' % MR, 'A. a e. ran %s 1 <_ a' % USED), ('( # ` %s ) <_ ( # ` W )' % USED, "B' <_ N'")))
add13('t13srcxb', T_XB, cj(C_XB))

HB5P = HB5.replace('( # ` A )', 'P')
T_XU = ((('A e. Word NN0', RALB('A', "B'"), '( # ` A ) <_ P'), ('P e. NN0', "B' e. NN0", "N' e. NN0"), ("U' e. NN0", "W' e. NN0")),
        (HB5P, "( ( P + 2 ) x. U' ) <_ W'", "( ( P x. ( B' + 1 ) ) + 1 ) <_ W'"))
C_XU = (HB5, "( ( ( # ` A ) + 2 ) x. U' ) <_ W'", "( # ` ( encList ` A ) ) <_ W'")
add13('t13srcxu', T_XU, cj(C_XU))

T_XL = ((('L e. NN', 'N e. NN0', 'W e. Word NN0'), ("B' e. NN0", "W' e. NN0", RALB('W', "B'"))),
        ("( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) <_ W'", "( ( L x. ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'"))
C_XL = ((WG(ACCW3), WG(D6V3)), ("( # ` %s ) <_ W'" % ACCW3, "( # ` %s ) <_ W'" % D6V3))
add13('t13srcxl', T_XL, cj(C_XL))

SB5 = '( ( 5 x. ( ( U x. B ) + 1 ) ) + 2 )'
UB1 = '( ( U x. B ) + 1 )'
T_Q = ((SC_TY, LEQT[0]), (('U <_ I', LT2('Z')), ('B e. NN0', "B' e. NN0"), ("B <_ B'", "%s <_ B'" % SB5)))
C_Q = (('( # ` Q ) = U', '( 2nd ` ( ProdL ` Q ) ) = U', RALB('Q', "B'")), ('A. a e. ran Q 1 <_ a', '1 <_ L', 'L < ( 2 ^ %s )' % UB1),
       ((LT2('L', "B'"), LT2('X', "B'"), "( 1 + X ) < ( 2 ^ B' )"), '( # ` ( encList ` Q ) ) <_ ( ( U x. ( B + 1 ) ) + 1 )'))
add13('t13srcq', T_Q, cj(C_Q))

E0_ = '( ( ( 2 ^ %s ) ^ 2 ) x. ( %s + 2 ) )' % (UB1, P2U)
WEQ = "W' = ( %s x. U' )" % E0_
T_L2 = ((('L e. NN0', 'L < ( 2 ^ %s )' % UB1), ('U e. NN0', 'B e. NN0', "U' e. NN0")), WEQ)
C_L2 = "( ( %s x. ( %s + 2 ) ) x. U' ) <_ W'" % (LSQ, P2U)
add13('t13srcl2', T_L2, C_L2)

NPP = "( ( B' x. ( P + 1 ) ) + 1 )"
HB5PN = HB5P.replace(" N' )", ' %s )' % NPP)
EXYP = "( ( ( ( L + 1 ) ^ 2 ) x. ( P + 2 ) ) x. ( TMB ` ( ( ( 3 x. P ) x. B' ) + ( ( 5 x. B' ) + 5 ) ) ) )"
T_U = ((('P e. NN0', 'P <_ %s' % P2U), ('U e. NN0', 'L e. NN0', "B' e. NN0"), ("U' e. NN0", "W' e. NN0")), (UP1, UP2, "( B' + 2 ) <_ U'"))
C_U = (("( %s + 2 ) <_ U'" % NPP, "( TMB ` %s ) <_ U'" % NPP, "( ( P + 2 ) x. U' ) <_ W'"),
       ("( ( P x. ( B' + 1 ) ) + 1 ) <_ W'", "( ( L x. ( ( P x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'"),
       (HB5PN, "%s <_ W'" % EXYP))
add13('t13srcu', T_U, cj(C_U))


# ------------------------------------------------------------ small tools
def pow2le(w, ph, cl, e1, e2, le):
    """( ph -> ( 2 ^ e1 ) <_ ( 2 ^ e2 ) ) from le : e1 <_ e2 (e1 e2 NN0 in cl)"""
    s = w.s
    eu = s([s([s([cl.mem(e1, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, e1)), s([cl.mem(e2, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, e2)), le], '3jca',
              '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (ph, e1, e2, e1, e2)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (ph, e2, e1))
    return s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), eu, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ %s ) <_ ( 2 ^ %s ) )' % (ph, e1, e2))


def pow2lt(w, ph, cl, e1, e2, lt):
    """( ph -> ( 2 ^ e1 ) < ( 2 ^ e2 ) ) from lt : e1 < e2"""
    s = w.s
    return s([s([closed(w, ph, '2re', '2 e. RR'), s([cl.mem(e1, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, e1)), s([cl.mem(e2, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, e2))],
                '3jca', '( %s -> ( 2 e. RR /\\ %s e. ZZ /\\ %s e. ZZ ) )' % (ph, e1, e2)), s([closed(w, ph, '1lt2', '1 < 2'), lt], 'jca', '( %s -> ( 1 < 2 /\\ %s < %s ) )' % (ph, e1, e2)),
              w.inst('ltexp2a')], 'syl2anc', '( %s -> ( 2 ^ %s ) < ( 2 ^ %s ) )' % (ph, e1, e2))


def p2leaf(w, ph, cl, e):
    """register ( 2 ^ e ) as an NN0 atom of cl"""
    cl.atom('( 2 ^ %s )' % e)
    cl.leaf('( 2 ^ %s )' % e, 'NN0', w.s([closed(w, ph, '2nn0', '2 e. NN0'), cl.mem(e, 'NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, e)))


def tmbleaf(w, ph, cl, e):
    cl.leaf('( TMB ` %s )' % e, 'NN0', tmbn(w, ph, e, cl.mem(e, 'NN0')))


def tmbmono(w, ph, cl, e1, e2, le):
    return w.s([cl.mem(e1, 'NN0'), cl.mem(e2, 'NN0'), le, w.inst('tmbmono')], 'syl3anc', '( %s -> ( TMB ` %s ) <_ ( TMB ` %s ) )' % (ph, e1, e2))


def lemul1a(w, ph, cl, A, B_, C_, ab):
    """( ph -> ( A x. C ) <_ ( B x. C ) ) from ab : A <_ B , 0 <_ C"""
    return P.lemul1(w, ph, cl, A, B_, C_, ab)


# ------------------------------------------------------------ t13lt2m
def t13lt2m():
    lab = 't13lt2m'
    T = (('A e. RR', 'B e. NN0', 'C e. NN0'), ('B <_ C', 'A < ( 2 ^ B )'))
    ph = cj(T)
    w = W(lab, 'A bound below ` 2 ^ B ` is a bound below ` 2 ^ C ` for ` B <_ C ` (~ leexp2a ).')
    s = w.s
    c = Ctx(w, ph, T)
    cl = Closure(w, ph, {'A': ('RR', c['A e. RR']), 'B': ('NN0', c['B e. NN0']), 'C': ('NN0', c['C e. NN0'])})
    pe = pow2le(w, ph, cl, 'B', 'C', c['B <_ C'])
    p2leaf(w, ph, cl, 'B'); p2leaf(w, ph, cl, 'C')
    st = linarith(w, ph, [c['A < ( 2 ^ B )'], pe], 'A < ( 2 ^ C )', closure=cl)
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13sctmv
def t13sctmv():
    lab = 't13sctmv'
    T = T_SCTMV
    ph = cj(T)
    w = W(lab, '` scalesTM C1 K n ` is the tuple of its five projections (~ sctmval , ~ op1st ), which are natural numbers; '
               '` y ` and ` theta ` are powers of two, hence positive.')
    s = w.s
    c = Ctx(w, ph, T)
    cn, knn, nn = c['C e. NN0'], c['K e. NN'], c['N e. NN0']
    TUP = SCTUP_('C', 'K', 'N')
    tv = s([s([cn, knn, nn], '3jca', '( %s -> ( C e. NN0 /\\ K e. NN /\\ N e. NN0 ) )' % ph), w.inst('sctmval')], 'syl', '( %s -> %s = %s )' % (ph, SC_, TUP))
    pjn = {}
    for pj in (PZ, PZ99, PY, PT, PTH):
        st_, val = proj_eq(w, ph, pj(SC_), tv, TUP)
        pjn[pj] = (val, st_)
    kn = s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % ph)
    cl2 = Closure(w, ph, {'C': ('NN0', cn), 'K': ('NN0', kn), 'N': ('NN0', nn)})
    M_ = '( 2 Nlog N )'
    A_ = '( 2 Nlog %s )' % M_
    Bb_ = '( 2 Nlog %s )' % A_

    def nlogleaf(x, xn):
        st_ = s([closed(w, ph, '2nn0', '2 e. NN0'), xn, w.inst('nlogcl')], 'syl2anc', '( %s -> ( 2 Nlog %s ) e. NN0 )' % (ph, x))
        cl2.leaf('( 2 Nlog %s )' % x, 'NN0', st_)
        return st_
    mn = nlogleaf('N', nn)
    an = nlogleaf(M_, mn)
    nlogleaf(A_, an)
    Z_ = '( ( C x. %s ) x. %s )' % (A_, Bb_)
    zn = cl2.mem(Z_, 'NN0')
    nlogleaf(Z_, zn)
    BZ_ = '( ( 2 Nlog %s ) + 1 )' % Z_
    NUM99 = '( ( ; 9 9 x. %s ) + ; 9 9 )' % BZ_
    EXP99 = '( |_ ` ( %s / ; ; 1 0 0 ) )' % NUM99
    n100 = s([num.nn(w, 100)], 'a1i', '( %s -> ; ; 1 0 0 e. NN )' % ph)
    cl2.leaf(EXP99, 'NN0', s([cl2.mem(NUM99, 'NN0'), n100, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXP99)))
    K1 = '( K - 1 )'
    cl2.leaf(K1, 'NN0', s([knn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, K1)))
    KBZ = '( %s x. %s )' % (K1, BZ_)
    NUMY = '( ( %s + K ) - 1 )' % KBZ
    kbzk = s([cl2.mem(KBZ, 'NN0'), knn, w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> ( %s + K ) e. NN )' % (ph, KBZ))
    cl2.leaf(NUMY, 'NN0', s([kbzk, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, NUMY)))
    EXPY = '( |_ ` ( %s / K ) )' % NUMY
    cl2.leaf(EXPY, 'NN0', s([cl2.mem(NUMY, 'NN0'), knn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXPY)))
    M1 = '( %s + 1 )' % M_
    nlogleaf(M1, cl2.mem(M1, 'NN0'))
    LTH = '( ( 2 Nlog %s ) + 1 )' % M1
    NUMTH = '( ( 6 x. %s ) + 4 )' % LTH
    EXPTH = '( |_ ` ( %s / 5 ) )' % NUMTH
    cl2.leaf(EXPTH, 'NN0', s([cl2.mem(NUMTH, 'NN0'), closed(w, ph, '5nn', '5 e. NN'), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXPTH)))
    two = closed(w, ph, '2nn', '2 e. NN')
    def pow_nn(e):
        return s([two, cl2.mem(e, 'NN0'), w.inst('nnexpcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN )' % (ph, e))
    vz, sz = pjn[PZ]; v99, s99 = pjn[PZ99]; vy, sy = pjn[PY]; vt, st_t = pjn[PT]; vth, sth = pjn[PTH]
    assert v99 == '( 2 ^ %s )' % EXP99 and vy == '( 2 ^ %s )' % EXPY and vth == '( 2 ^ %s )' % EXPTH, (v99, vy, vth)
    zn0 = s([sz, cl2.mem(vz, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, PZ(SC_)))
    z99n = s([s99, s([pow_nn(EXP99)], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, v99))], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, PZ99(SC_)))
    ynn = s([sy, pow_nn(EXPY)], 'eqeltrd', '( %s -> %s e. NN )' % (ph, PY(SC_)))
    tn0 = s([st_t, cl2.mem(vt, 'NN0')], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, PT(SC_)))
    thnn = s([sth, pow_nn(EXPTH)], 'eqeltrd', '( %s -> %s e. NN )' % (ph, PTH(SC_)))
    # the tuple: rewrite TUP's components back to the projections
    e1 = s([s([sz], 'eqcomd', '( %s -> %s = %s )' % (ph, vz, PZ(SC_))), s([s99], 'eqcomd', '( %s -> %s = %s )' % (ph, v99, PZ99(SC_)))], 'opeq12d',
           '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, vz, v99, PZ(SC_), PZ99(SC_)))
    e2 = s([s([sy], 'eqcomd', '( %s -> %s = %s )' % (ph, vy, PY(SC_))), s([st_t], 'eqcomd', '( %s -> %s = %s )' % (ph, vt, PT(SC_)))], 'opeq12d',
           '( %s -> <. %s , %s >. = <. %s , %s >. )' % (ph, vy, vt, PY(SC_), PT(SC_)))
    e12 = s([e1, e2], 'opeq12d', '( %s -> <. <. %s , %s >. , <. %s , %s >. >. = <. <. %s , %s >. , <. %s , %s >. >. )' % (ph, vz, v99, vy, vt, PZ(SC_), PZ99(SC_), PY(SC_), PT(SC_)))
    e3 = s([e12, s([sth], 'eqcomd', '( %s -> %s = %s )' % (ph, vth, PTH(SC_)))], 'opeq12d', '( %s -> %s = %s )' % (ph, TUP, TUPP))
    teq = s([tv, e3], 'eqtrd', '( %s -> %s = %s )' % (ph, SC_, TUPP))
    ty = s([s([zn0, z99n], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (ph, PZ(SC_), PZ99(SC_))), s([ynn, tn0, thnn], '3jca', '( %s -> ( %s e. NN /\\ %s e. NN0 /\\ %s e. NN ) )' % (ph, PY(SC_), PT(SC_), PTH(SC_)))],
           'jca', '( %s -> ( ( %s e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN /\\ %s e. NN0 /\\ %s e. NN ) ) )' % (ph, PZ(SC_), PZ99(SC_), PY(SC_), PT(SC_), PTH(SC_)))
    st = s([teq, ty], 'jca', '( %s -> %s )' % (ph, C_SCTMV))
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcty, t13srcsm, t13srcv
def letter_cl(w, ph, c):
    cl = Closure(w, ph, {x: ('NN0', c['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N')})
    for x in ('Z', 'Y'):
        cl.leaf(x, 'NN0', w.s([c['%s e. NN' % x]], 'nnnn0d', '( %s -> %s e. NN0 )' % (ph, x)))
    return cl


def t13srcty():
    lab = 't13srcty'
    ph = cj(T_TY)
    w = W(lab, 'The typing of the letters of A1b\'s ~ searchval from their equations: the reservoir (~ reservoircl ), its '
               'length, the window ` Q ` (~ swrdcl ), ` L X ` (~ prodlcl ), the step-2 charge, the scan\'s cost (~ scancl ).')
    s = w.s
    c = Ctx(w, ph, T_TY)
    cl = letter_cl(w, ph, c)
    ty = P.stage_typing(w, ph, c, cl)
    leaf = {'( 1st ` R ) e. Word NN0': ty['R1'], '( 2nd ` R ) e. NN0': ty['R2'], 'I e. NN0': ty['I'], 'Q e. Word NN0': ty['Q'], 'L e. NN0': ty['L'],
            '( 2nd ` ( ProdL ` Q ) ) e. NN0': ty['PQ2'], 'X e. NN0': ty['X'], "C' e. NN0": ty["C'"], '%s e. NN0' % S2: ty['J2']}
    st = bld_tree(w, ph, C_TY, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


def t13srcsm():
    lab = 't13srcsm'
    ph = cj(T_SM)
    w = W(lab, 'The typing of the letters in the some case of the scan: ` k\' ` and the pool (~ scandj ), the extraction '
               'and its cost (~ extractcl ), ` L e. NN ` .')
    s = w.s
    c = Ctx(w, ph, T_SM)
    cl = letter_cl(w, ph, c)
    ty = P.stage_typing(w, ph, c, cl)
    ty.update(some_typing13(w, ph, c, cl, ty))
    xcl2 = None
    # X' e. XTY (some_typing keeps only ( 2nd X' ) ; rebuild)
    lnn, ww = ty['Lnn'], ty['W']
    xcl = s([s([s([lnn, c['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), ww], 'jca', '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ W e. Word NN0 ) )' % ph), w.inst('extractcl')],
            'syl', '( %s -> %s e. %s )' % (ph, LEQD["X'"], XTY))
    xcl2 = s([c[EQ("X'")], xcl], 'eqeltrd', "( %s -> X' e. %s )" % (ph, XTY))
    leaf = {"J' e. NN0": ty["J'"], 'W e. Word NN0': ty['W'], 'L e. NN': lnn, "X' e. %s" % XTY: xcl2, '%s e. NN0' % E2: ty['E2']}
    st = bld_tree(w, ph, C_SM, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


def t13srcv():
    lab = 't13srcv'
    ph = cj(T_TY)
    w = W(lab, 'The search value at the letters of A1b\'s ~ searchval : the four-way ` if ` on ` len < T ` , the scan, '
               'the extraction and the verdict, with the costs ` c , c + s , c + s + e , c + s + e + w ` .')
    s = w.s
    c = Ctx(w, ph, T_TY)
    cl = letter_cl(w, ph, c)
    sv, rhs = P.search_value(w, ph, c, cl)
    assert rhs == SV_RHS, '\n%s\n%s' % (rhs, SV_RHS)
    qed13(w, sv, lab)
    return w.run()


# ------------------------------------------------------------ t13srcx: F = m_R , A = used_R
def t13srcx():
    lab = 't13srcx'
    ph = cj(T_X)
    w = W(lab, 'The extraction\'s result in the some case (~ exres , ~ extractval at the initial state): the candidate is '
               '` ( m_R , used_R ) ` , the state at the stop index of the loop.')
    s = w.s
    c = Ctx(w, ph, T_X)
    lnn, nn, ww = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0']
    xv, IFX, j0 = P.ext_value(w, ph, c, None, lnn, ww)
    cst = s([c["( 1st ` X' ) =/= %s" % INR]], 'neneqd', "( %s -> -. ( 1st ` X' ) = %s )" % (ph, INR))
    pn_ = '( %s /\\ -. %s = 1o )' % (ph, HIT)
    ifi = s([s([], 'simpr', '( %s -> -. %s = 1o )' % (pn_, HIT))], 'iffalsed', '( %s -> %s = %s )' % (pn_, IFX, INR))
    xinr = s([s([xv], 'adantr', "( %s -> ( 1st ` X' ) = %s )" % (pn_, IFX)), ifi], 'eqtrd', "( %s -> ( 1st ` X' ) = %s )" % (pn_, INR))
    hit1 = s([s([xinr, cst], 'mtand', '( %s -> -. -. %s = 1o )' % (ph, HIT))], 'notnotrd', '( %s -> %s = 1o )' % (ph, HIT))
    xinl = s([xv, s([hit1], 'iftrued', '( %s -> %s = ( inl ` <. %s , %s >. ) )' % (ph, IFX, MR, USED))], 'eqtrd', "( %s -> ( 1st ` X' ) = ( inl ` <. %s , %s >. ) )" % (ph, MR, USED))
    opv = s([], 'opex', '<. %s , %s >. e. _V' % (MR, USED))
    x2 = s([s([xinl], 'fveq2d', "( %s -> ( 2nd ` ( 1st ` X' ) ) = ( 2nd ` ( inl ` <. %s , %s >. ) ) )" % (ph, MR, USED)),
            s([s([opv, w.inst('alginl2')], 'ax-mp', '( 2nd ` ( inl ` <. %s , %s >. ) ) = <. %s , %s >.' % (MR, USED, MR, USED))], 'a1i', '( %s -> ( 2nd ` ( inl ` <. %s , %s >. ) ) = <. %s , %s >. )' % (ph, MR, USED, MR, USED))],
           'eqtrd', "( %s -> ( 2nd ` ( 1st ` X' ) ) = <. %s , %s >. )" % (ph, MR, USED))
    fm = s([c[EQ('F')], s([x2], 'fveq2d', "( %s -> ( 1st ` ( 2nd ` ( 1st ` X' ) ) ) = ( 1st ` <. %s , %s >. ) )" % (ph, MR, USED)),
            s([s([s([], 'fvex', '%s e. _V' % MR), s([], 'fvex', '%s e. _V' % USED)], 'op1st', '( 1st ` <. %s , %s >. ) = %s' % (MR, USED, MR))], 'a1i', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, MR, USED, MR))],
           '3eqtrd', '( %s -> F = %s )' % (ph, MR))
    au = s([c[EQ('A')], s([x2], 'fveq2d', "( %s -> ( 2nd ` ( 2nd ` ( 1st ` X' ) ) ) = ( 2nd ` <. %s , %s >. ) )" % (ph, MR, USED)),
            s([s([s([], 'fvex', '%s e. _V' % MR), s([], 'fvex', '%s e. _V' % USED)], 'op2nd', '( 2nd ` <. %s , %s >. ) = %s' % (MR, USED, USED))], 'a1i', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ph, MR, USED, USED))],
           '3eqtrd', '( %s -> A = %s )' % (ph, USED))
    st = s([fm, au], 'jca', '( %s -> %s )' % (ph, cj(C_X)))
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcxb: the extraction's bounds and positivity
def t13srcxb():
    lab = 't13srcxb'
    ph = cj(T_XB)
    w = W(lab, 'The extraction\'s bounds at the stop index (Lean ` extractFin_bounded ` , ` extractGo_some ` read by Step5, '
               '~ t12exbnd ): the entries of ` used_R ` below ` 2 ^ b1 ` , at most as many as the pool has, ` m_R < 2 ^ bM ` ; '
               'and the positivity (~ t12expos ): ` 1 <_ m_R ` , the entries of ` used_R ` at least 1.')
    s = w.s
    c = Ctx(w, ph, T_XB)
    lnn, nn, ww, bn, un, npe = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0'], c["B' e. NN0"], c['U e. NN0'], c[NPEQ]
    ralw, w2, wle, ub = c[RALB('W', "B'")], c['A. a e. ran W 2 <_ a'], c['( # ` W ) <_ ( 2 ^ U )'], c["U < B'"]
    cl = Closure(w, ph, {"B'": ('NN0', bn), 'U': ('NN0', un), 'N': ('NN0', nn)})
    cl.leaf('L', 'NN0', s([lnn], 'nnnn0d', '( %s -> L e. NN0 )' % ph))
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl.leaf('( # ` W )', 'NN0', nw)
    z0 = P.z0_in_sty(w, ph)
    Z0, STY_ = P.Z0, P.STY
    j = s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0, STY_))], 'jca',
          '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (ph, Z0, STY_))
    ritp = s([j, w.inst('exitp')], 'syl', '( %s -> %s )' % (ph, tsub_text(split_imp(stmt('exitp'))[1], {'G': 'N', 'Z': Z0})))
    rin = s([ritp], 'simp1d', '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (ph, RIT))
    mrn, usedw, tblt, hit2 = P.sq_comps(w, ph, cl, lnn, nn, ww, z0, RIT, rin)
    ritn = s([rin, w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, RIT))
    cl.leaf(RIT, 'NN0', ritn)
    ritle = s([rin, w.inst('elfzle2')], 'syl', '( %s -> %s <_ ( # ` W ) )' % (ph, RIT))
    exb = s([s([s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, bn], 'jca', "( %s -> ( W e. Word NN0 /\\ B' e. NN0 ) )" % ph)], 'jca',
                "( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ B' e. NN0 ) ) )" % ph), s([ralw, rin], 'jca',
                "( %s -> ( %s /\\ %s e. ( 0 ... ( # ` W ) ) ) )" % (ph, RALB('W', "B'"), RIT))], 'jca',
             "( %s -> ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ B' e. NN0 ) ) /\\ ( %s /\\ %s e. ( 0 ... ( # ` W ) ) ) ) )" % (ph, RALB('W', "B'"), RIT)),
           w.inst('t12exbnd')], 'syl', '( %s -> %s )' % (ph, tsub_text(P.C_EXB, {'B': "B'", 'I': RIT})))
    half1 = s([exb], 'simpld', '( %s -> ( %s /\\ ( # ` %s ) <_ %s ) )' % (ph, RALB(USED, "B'"), USED, RIT))
    ralu = s([half1], 'simpld', '( %s -> %s )' % (ph, RALB(USED, "B'")))
    ulen = s([half1], 'simprd', '( %s -> ( # ` %s ) <_ %s )' % (ph, USED, RIT))
    E1R = "( 1 + ( B' x. %s ) )" % RIT
    half2 = s([exb], 'simprd', '( %s -> ( %s < ( 2 ^ %s ) /\\ ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( %s x. ( B\' + 1 ) ) + 1 ) ) ) )' % (ph, MR, E1R, TBL, RIT))
    mlt = s([half2], 'simpld', '( %s -> %s < ( 2 ^ %s ) )' % (ph, MR, E1R))
    bm = P.mul_le2(w, ph, cl, "B'", RIT, '( # ` W )', ritle)
    cl.leaf("N'", 'NN0', s([npe, cl.mem("( ( B' x. ( ( # ` W ) + 1 ) ) + 1 )", 'NN0')], 'eqeltrd', "( %s -> N' e. NN0 )" % ph))
    ele = linarith(w, ph, [bm, npe, cl.ge0("B'")], "%s <_ N'" % E1R, closure=cl, products=True)
    pe = pow2le(w, ph, cl, E1R, "N'", ele)
    for e_ in (E1R, "N'", 'U', "B'"):
        p2leaf(w, ph, cl, e_)
    mltn = linarith(w, ph, [mlt, pe], "%s < ( 2 ^ N' )" % MR, closure=cl)
    pub = pow2lt(w, ph, cl, 'U', "B'", ub)
    ulb = linarith(w, ph, [ulen, ritle, wle, pub], "( # ` %s ) < ( 2 ^ B' )" % USED, closure=cl)
    uleW = linarith(w, ph, [ulen, ritle], '( # ` %s ) <_ ( # ` W )' % USED, closure=cl)
    bpn = linarith(w, ph, [npe, cl.ge0("( B' x. ( # ` W ) )")], "B' <_ N'", closure=cl, products=True)
    # positivity
    pos = s([s([s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, w2], 'jca', '( %s -> ( W e. Word NN0 /\\ A. a e. ran W 2 <_ a ) )' % ph)], 'jca',
                '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ A. a e. ran W 2 <_ a ) ) )' % ph), rin], 'jca',
             '( %s -> ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ A. a e. ran W 2 <_ a ) ) /\\ %s e. ( 0 ... ( # ` W ) ) ) )' % (ph, RIT)), w.inst('t12expos')], 'syl',
            '( %s -> ( %s /\\ %s ) )' % (ph, P.POS1, P.POS2))
    f1 = s([s([pos], 'simpld', '( %s -> %s )' % (ph, P.POS1)), w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (ph, MR))
    pos2 = s([pos], 'simprd', '( %s -> %s )' % (ph, P.POS2))
    bi_ = s([s([s([], 'breq2', '( a = p -> ( 2 <_ a <-> 2 <_ p ) )')], 'cbvralvw', '( A. a e. ran %s 2 <_ a <-> A. p e. ran %s 2 <_ p )' % (USED, USED))], 'a1i',
            '( %s -> ( A. a e. ran %s 2 <_ a <-> A. p e. ran %s 2 <_ p ) )' % (ph, USED, USED))
    pos2p = s([pos2, bi_], 'mpbid', '( %s -> A. p e. ran %s 2 <_ p )' % (ph, USED))
    pu = '( %s /\\ p e. ran %s )' % (ph, USED)
    a2u = s([pos2p], 'r19.21bi', '( %s -> 2 <_ p )' % pu)
    urn = s([s([usedw, w.inst('wrdf')], 'syl', '( %s -> %s : ( 0 ..^ ( # ` %s ) ) --> NN0 )' % (ph, USED, USED)), w.inst('frn')], 'syl', '( %s -> ran %s C_ NN0 )' % (ph, USED))
    pn0 = s([s([urn], 'adantr', '( %s -> ran %s C_ NN0 )' % (pu, USED)), s([], 'simpr', '( %s -> p e. ran %s )' % (pu, USED))], 'sseldd', '( %s -> p e. NN0 )' % pu)
    clp = Closure(w, pu, {'p': ('NN0', pn0)})
    a1 = linarith(w, pu, [a2u], '1 <_ p', closure=clp)
    ral1p = s([a1], 'ralrimiva', '( %s -> A. p e. ran %s 1 <_ p )' % (ph, USED))
    bi2_ = s([s([s([], 'breq2', '( p = a -> ( 1 <_ p <-> 1 <_ a ) )')], 'cbvralvw', '( A. p e. ran %s 1 <_ p <-> A. a e. ran %s 1 <_ a )' % (USED, USED))], 'a1i',
             '( %s -> ( A. p e. ran %s 1 <_ p <-> A. a e. ran %s 1 <_ a ) )' % (ph, USED, USED))
    ral1 = s([ral1p, bi2_], 'mpbid', '( %s -> A. a e. ran %s 1 <_ a )' % (ph, USED))
    leaf = {'%s e. NN0' % MR: mrn, '%s e. Word NN0' % USED: usedw, RALB(USED, "B'"): ralu, "( # ` %s ) < ( 2 ^ B' )" % USED: ulb, "%s < ( 2 ^ N' )" % MR: mltn,
            '1 <_ %s' % MR: f1, 'A. a e. ran %s 1 <_ a' % USED: ral1, '( # ` %s ) <_ ( # ` W )' % USED: uleW, "B' <_ N'": bpn}
    st = bld_tree(w, ph, C_XB, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcxu: the units at the witness list
def t13srcxu():
    lab = 't13srcxu'
    ph = cj(T_XU)
    w = W(lab, 'The unit facts at the witness list ` A ` from those at the pool length ` P ` : ` # A <_ P ` makes the verify bit '
               'bound, the clearing product and the encoded length monotone (~ tmbmono , ~ tm2lenclen ).')
    s = w.s
    c = Ctx(w, ph, T_XU)
    an, rala, alp = c['A e. Word NN0'], c[RALB('A', "B'")], c['( # ` A ) <_ P']
    pn, bn, npn, un, wn = c['P e. NN0'], c["B' e. NN0"], c["N' e. NN0"], c["U' e. NN0"], c["W' e. NN0"]
    hb5p, p2u, pb1 = c[HB5P], c["( ( P + 2 ) x. U' ) <_ W'"], c["( ( P x. ( B' + 1 ) ) + 1 ) <_ W'"]
    cl = Closure(w, ph, {'P': ('NN0', pn), "B'": ('NN0', bn), "N'": ('NN0', npn), "U'": ('NN0', un), "W'": ('NN0', wn)})
    cl.leaf('( # ` A )', 'NN0', s([an, w.inst('lencl')], 'syl', '( %s -> ( # ` A ) e. NN0 )' % ph))
    VXP = VX4.replace('( # ` A )', 'P')
    abm = lemul1a(w, ph, cl, '( # ` A )', 'P', "B'", alp)
    vxle = linarith(w, ph, [abm], '( ( 4 x. %s ) + 6 ) <_ ( ( 4 x. %s ) + 6 )' % (VX4, VXP), closure=cl, products=True)
    tbm = tmbmono(w, ph, cl, '( ( 4 x. %s ) + 6 )' % VX4, '( ( 4 x. %s ) + 6 )' % VXP, vxle)
    for e_ in (VX4, VXP):
        tmbleaf(w, ph, cl, '( ( 4 x. %s ) + 6 )' % e_)
    hb5 = linarith(w, ph, [tbm, hb5p], HB5, closure=cl)
    am2 = lemul1a(w, ph, cl, '( ( # ` A ) + 2 )', '( P + 2 )', "U'", linarith(w, ph, [alp], '( ( # ` A ) + 2 ) <_ ( P + 2 )', closure=cl))
    a2u_ = linarith(w, ph, [am2, p2u], "( ( ( # ` A ) + 2 ) x. U' ) <_ W'", closure=cl, products=True)
    LU = '( # ` ( encList ` A ) )'
    lu = s([an, bn, rala, w.inst('tm2lenclen')], 'syl3anc', "( %s -> %s <_ ( ( ( # ` A ) x. ( B' + 1 ) ) + 1 ) )" % (ph, LU))
    cl.leaf(LU, 'NN0', s([s([an, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` A ) e. Word Gamma' )" % ph), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LU)))
    muL = lemul1a(w, ph, cl, '( # ` A )', 'P', "( B' + 1 )", alp)
    luW = linarith(w, ph, [lu, muL, pb1], "%s <_ W'" % LU, closure=cl)
    leaf = {HB5: hb5, "( ( ( # ` A ) + 2 ) x. U' ) <_ W'": a2u_, "( # ` ( encList ` A ) ) <_ W'": luW}
    st = bld_tree(w, ph, C_XU, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcxl: the post-extraction stack words
def t13srcxl():
    lab = 't13srcxl'
    ph = cj(T_XL)
    w = W(lab, 'The words left by ` extractF ` on the accumulator and pool stacks (the ascending table word with a blank, the '
               'rest of the pool) are words over Gamma\' of length at most ` W\' ` (~ t12exbnd , ~ ttabtbll , ~ swrdlen ).')
    s = w.s
    c = Ctx(w, ph, T_XL)
    lnn, nn, ww, bn, wn, ralw = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0'], c["B' e. NN0"], c["W' e. NN0"], c[RALB('W', "B'")]
    h1, h2 = c["( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) <_ W'"], c["( ( L x. ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'"]
    cl = Closure(w, ph, {"B'": ('NN0', bn), "W'": ('NN0', wn), 'N': ('NN0', nn)})
    cl.leaf('L', 'NN0', s([lnn], 'nnnn0d', '( %s -> L e. NN0 )' % ph))
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl.leaf('( # ` W )', 'NN0', nw)
    z0 = P.z0_in_sty(w, ph)
    Z0, STY_ = P.Z0, P.STY
    j = s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0, STY_))], 'jca',
          '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (ph, Z0, STY_))
    ritp = s([j, w.inst('exitp')], 'syl', '( %s -> %s )' % (ph, tsub_text(split_imp(stmt('exitp'))[1], {'G': 'N', 'Z': Z0})))
    rin = s([ritp], 'simp1d', '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (ph, RIT))
    mrn, usedw, tblt, hit2 = P.sq_comps(w, ph, cl, lnn, nn, ww, z0, RIT, rin)
    ritn = s([rin, w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, RIT))
    cl.leaf(RIT, 'NN0', ritn)
    ritle = s([rin, w.inst('elfzle2')], 'syl', '( %s -> %s <_ ( # ` W ) )' % (ph, RIT))
    exb = s([s([s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, bn], 'jca', "( %s -> ( W e. Word NN0 /\\ B' e. NN0 ) )" % ph)], 'jca',
                "( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ B' e. NN0 ) ) )" % ph), s([ralw, rin], 'jca',
                "( %s -> ( %s /\\ %s e. ( 0 ... ( # ` W ) ) ) )" % (ph, RALB('W', "B'"), RIT))], 'jca',
             "( %s -> ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ B' e. NN0 ) ) /\\ ( %s /\\ %s e. ( 0 ... ( # ` W ) ) ) ) )" % (ph, RALB('W', "B'"), RIT)),
           w.inst('t12exbnd')], 'syl', '( %s -> %s )' % (ph, tsub_text(P.C_EXB, {'B': "B'", 'I': RIT})))
    E1R = "( 1 + ( B' x. %s ) )" % RIT
    tbl_ = s([s([exb], 'simprd', '( %s -> ( %s < ( 2 ^ %s ) /\\ ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( %s x. ( B\' + 1 ) ) + 1 ) ) ) )' % (ph, MR, E1R, TBL, RIT))], 'simprd',
             '( %s -> ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( %s x. ( B\' + 1 ) ) + 1 ) ) )' % (ph, TBL, RIT))
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    wrestw = s([ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, WREST))
    g6 = enclg(w, ph, WREST, wrestw, '(/)', wrd0)
    g5 = accw_g(w, ph, TBL, tblt, 'L', cl.mem('L', 'NN0'))
    # the table word
    LT_ = '( # ` ( L encTblAsc %s ) )' % TBL
    cl.leaf(LT_, 'NN0', s([tblw(w, ph, TBL, tblt, 'L', cl.mem('L', 'NN0')), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LT_)))
    rbL = lemul1a(w, ph, cl, RIT, '( # ` W )', "( B' + 1 )", ritle)
    inner = linarith(w, ph, [rbL], "( ( %s x. ( B' + 1 ) ) + 1 ) <_ ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 )" % RIT, closure=cl)
    lm = P.mul_le2(w, ph, cl, 'L', "( ( %s x. ( B' + 1 ) ) + 1 )" % RIT, "( ( ( # ` W ) x. ( B' + 1 ) ) + 1 )", inner)
    LA = '( # ` %s )' % ACCW3
    la = s([tblw(w, ph, TBL, tblt, 'L', cl.mem('L', 'NN0')), s([closed(w, ph, 'gamma0', "0 e. Gamma'")], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph), w.inst('ccatlen')], 'syl2anc',
           '( %s -> %s = ( %s + ( # ` <" 0 "> ) ) )' % (ph, LA, LT_))
    s0l = s([s([], 's1len', '( # ` <" 0 "> ) = 1')], 'a1i', '( %s -> ( # ` <" 0 "> ) = 1 )' % ph)
    cl.leaf(LA, 'NN0', s([g5, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LA)))
    cl.leaf('( # ` <" 0 "> )', 'NN0', s([s([s([], 's1len', '( # ` <" 0 "> ) = 1'), s([], '1nn0', '1 e. NN0')], 'eqeltri', '( # ` <" 0 "> ) e. NN0')], 'a1i', '( %s -> ( # ` <" 0 "> ) e. NN0 )' % ph))
    laW = linarith(w, ph, [la, s0l, tbl_, lm, h2], "%s <_ W'" % LA, closure=cl)
    # the rest of the pool
    LR = '( # ` ( encList ` %s ) )' % WREST
    nwz = s([nw, w.inst('nn0fz0')], 'sylib', '( %s -> ( # ` W ) e. ( 0 ... ( # ` W ) ) )' % ph)
    rnw = s([ww, rin, nwz, w.inst('swrdrn3')], 'syl3anc', '( %s -> ran %s = ( W " ( %s ..^ ( # ` W ) ) ) )' % (ph, WREST, RIT))
    rss = s([rnw, s([s([], 'imassrn', '( W " ( %s ..^ ( # ` W ) ) ) C_ ran W' % RIT)], 'a1i', '( %s -> ( W " ( %s ..^ ( # ` W ) ) ) C_ ran W )' % (ph, RIT))], 'eqsstrd',
            '( %s -> ran %s C_ ran W )' % (ph, WREST))
    ralr = s([rss, ralw, w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ph, RALB(WREST, "B'")))
    lr = s([wrestw, bn, ralr, w.inst('tm2lenclen')], 'syl3anc', "( %s -> %s <_ ( ( ( # ` %s ) x. ( B' + 1 ) ) + 1 ) )" % (ph, LR, WREST))
    swl = s([ww, rin, nwz, w.inst('swrdlen')], 'syl3anc', '( %s -> ( # ` %s ) = ( ( # ` W ) - %s ) )' % (ph, WREST, RIT))
    cl.leaf('( # ` %s )' % WREST, 'NN0', s([wrestw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, WREST)))
    cl.leaf(LR, 'NN0', s([s([wrestw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, WREST)), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LR)))
    swle = linarith(w, ph, [swl, cl.ge0(RIT)], '( # ` %s ) <_ ( # ` W )' % WREST, closure=cl)
    rwL = lemul1a(w, ph, cl, '( # ` %s )' % WREST, '( # ` W )', "( B' + 1 )", swle)
    lrW = linarith(w, ph, [lr, rwL, h1], "%s <_ W'" % LR, closure=cl)
    # ( # D6V3 ) = ( # encList WREST ) + ( # (/) )
    l6 = s([s([wrestw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, WREST)), wrd0, w.inst('ccatlen')], 'syl2anc',
           '( %s -> ( # ` %s ) = ( %s + ( # ` (/) ) ) )' % (ph, D6V3, LR))
    h0 = s([s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ph)
    cl.leaf('( # ` %s )' % D6V3, 'NN0', s([g6, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, D6V3)))
    cl.leaf('( # ` (/) )', 'NN0', s([s([s([], 'hash0', '( # ` (/) ) = 0'), s([], '0nn0', '0 e. NN0')], 'eqeltri', '( # ` (/) ) e. NN0')], 'a1i', '( %s -> ( # ` (/) ) e. NN0 )' % ph))
    l6W = linarith(w, ph, [l6, h0, lrW], "( # ` %s ) <_ W'" % D6V3, closure=cl)
    leaf = {WG(ACCW3): g5, WG(D6V3): g6, "( # ` %s ) <_ W'" % ACCW3: laW, "( # ` %s ) <_ W'" % D6V3: l6W}
    st = bld_tree(w, ph, C_XL, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcq: the window Q
def t13srcq():
    lab = 't13srcq'
    ph = cj(T_Q)
    w = W(lab, 'The window ` Q ` of the reservoir (~ a5q ): ` T ` primes at most ` z ` , so below ` 2 ^ b1 ` and at least 1; '
               '` L = prodL Q ` is positive (~ prodlspec , ~ fprodnncl ) and below ` 2 ^ ( T bs + 1 ) ` (~ t12prodle ); '
               '` X = L ^ 5 ` and ` 1 + X ` are below ` 2 ^ b1 ` ; the encoded window has at most ` T ( bs + 1 ) + 1 ` symbols.')
    s = w.s
    c = Ctx(w, ph, T_Q)
    zn, gn, yn, un, on, nn = [c[t] for t in ('Z e. NN', 'G e. NN0', 'Y e. NN', 'U e. NN0', 'O e. NN0', 'N e. NN0')]
    bn, b1n, ui, zb, bb1, sb5 = c['B e. NN0'], c["B' e. NN0"], c['U <_ I'], c[LT2('Z')], c["B <_ B'"], c["%s <_ B'" % SB5]
    cl = Closure(w, ph, {'U': ('NN0', un), 'B': ('NN0', bn), "B'": ('NN0', b1n), 'G': ('NN0', gn)})
    cl.leaf('Z', 'NN0', s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph))
    h1 = s([zn, gn, yn], '3jca', '( %s -> ( Z e. NN /\\ G e. NN0 /\\ Y e. NN ) )' % ph)
    aq = s([h1, un, c[EQ('R')], c[EQ('I')], c[EQ('Q')], ui], 'a5q',
           '( %s -> ( ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = U /\\ ( # ` ran Q ) = U ) ) /\\ ( ( ran Q C_ ( ( Z goodPrimesW G ) ` Y ) /\\ '
           'ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) ) )' % ph)
    qw = s([s([aq], 'simpld', '( %s -> ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = U /\\ ( # ` ran Q ) = U ) ) )' % ph)], 'simpld', '( %s -> ( Q e. Word NN0 /\\ Fun `\' Q ) )' % ph)
    qw = s([qw], 'simpld', '( %s -> Q e. Word NN0 )' % ph)
    nq = s([s([s([aq], 'simpld', '( %s -> ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = U /\\ ( # ` ran Q ) = U ) ) )' % ph)], 'simprd',
              '( %s -> ( ( # ` Q ) = U /\\ ( # ` ran Q ) = U ) )' % ph)], 'simpld', '( %s -> ( # ` Q ) = U )' % ph)
    qpr = s([s([aq], 'simprd', '( %s -> ( ( ran Q C_ ( ( Z goodPrimesW G ) ` Y ) /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) )' % ph)],
             'simprd', '( %s -> A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % ph)
    pq = '( %s /\\ c e. ran Q )' % ph
    cf = s([qpr], 'r19.21bi', '( %s -> ( c e. Prime /\\ c <_ Z ) )' % pq)
    cpr = s([cf], 'simpld', '( %s -> c e. Prime )' % pq)
    cle = s([cf], 'simprd', '( %s -> c <_ Z )' % pq)
    cuz = s([s([cpr, w.inst('prmuz2')], 'syl', '( %s -> c e. ( ZZ>= ` 2 ) )' % pq), w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ c e. ZZ /\\ 2 <_ c ) )' % pq)
    c2 = s([cuz], 'simp3d', '( %s -> 2 <_ c )' % pq)
    cz = s([cuz], 'simp2d', '( %s -> c e. ZZ )' % pq)
    clq = Closure(w, pq, {})
    clq.leaf('c', 'ZZ', cz); clq.leaf('Z', 'NN0', lift_from(w, ph, pq, cl.mem('Z', 'NN0')))
    for e_ in ('B', "B'"):
        clq.atom('( 2 ^ %s )' % e_)
        clq.leaf('( 2 ^ %s )' % e_, 'NN0', lift_from(w, ph, pq, s([closed(w, ph, '2nn0', '2 e. NN0'), cl.mem(e_, 'NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, e_))))
    pbb = pow2le(w, ph, cl, 'B', "B'", bb1)
    cltb = linarith(w, pq, [cle, lift_from(w, ph, pq, zb)], 'c < ( 2 ^ B )', closure=clq)
    clt1 = linarith(w, pq, [cltb, lift_from(w, ph, pq, pbb)], "c < ( 2 ^ B' )", closure=clq)
    c1 = linarith(w, pq, [c2], '1 <_ c', closure=clq)
    ralqb = P.cbv_a(w, ph, s([cltb], 'ralrimiva', '( %s -> A. c e. ran Q c < ( 2 ^ B ) )' % ph), None, 'c < ( 2 ^ B )', 'a < ( 2 ^ B )', 'c', 'ran Q')
    ralq = P.cbv_a(w, ph, s([clt1], 'ralrimiva', "( %s -> A. c e. ran Q c < ( 2 ^ B' ) )" % ph), None, "c < ( 2 ^ B' )", "a < ( 2 ^ B' )", 'c', 'ran Q')
    ralq1 = P.cbv_a(w, ph, s([c1], 'ralrimiva', '( %s -> A. c e. ran Q 1 <_ c )' % ph), None, '1 <_ c', '1 <_ a', 'c', 'ran Q')
    # prodL Q : cost = # Q = U , value positive and at most 2 ^ ( U B )
    pc2 = s([s([qw, w.inst('prodlcost')], 'syl', '( %s -> ( 2nd ` ( ProdL ` Q ) ) = ( # ` Q ) )' % ph), nq], 'eqtrd', '( %s -> ( 2nd ` ( ProdL ` Q ) ) = U )' % ph)
    NQ = '( # ` Q )'
    pr = s([qw, w.inst('prodlspec')], 'syl', '( %s -> ( 1st ` ( ProdL ` Q ) ) = prod_ i e. ( 0 ..^ %s ) ( Q ` i ) )' % (ph, NQ))
    fin_ = s([s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % NQ)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (ph, NQ))
    pi = '( %s /\\ i e. ( 0 ..^ %s ) )' % (ph, NQ)
    ii = s([], 'simpr', '( %s -> i e. ( 0 ..^ %s ) )' % (pi, NQ))
    qwi = s([qw], 'adantr', '( %s -> Q e. Word NN0 )' % pi)
    vin = s([qwi, ii, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( Q ` i ) e. NN0 )' % pi)
    vrn = s([s([qwi, w.inst('wrdfn')], 'syl', '( %s -> Q Fn ( 0 ..^ %s ) )' % (pi, NQ)), ii, w.inst('fnfvelrn')], 'syl2anc', '( %s -> ( Q ` i ) e. ran Q )' % pi)
    v1 = s([s([], 'breq2', '( a = ( Q ` i ) -> ( 1 <_ a <-> 1 <_ ( Q ` i ) ) )'), vrn, s([ralq1], 'adantr', '( %s -> A. a e. ran Q 1 <_ a )' % pi)], 'rspcdva',
           '( %s -> 1 <_ ( Q ` i ) )' % pi)
    vnn = s([s([vin, v1], 'jca', '( %s -> ( ( Q ` i ) e. NN0 /\\ 1 <_ ( Q ` i ) ) )' % pi), w.inst('elnnnn0c')], 'sylibr', '( %s -> ( Q ` i ) e. NN )' % pi)
    fp = s([fin_, vnn], 'fprodnncl', '( %s -> prod_ i e. ( 0 ..^ %s ) ( Q ` i ) e. NN )' % (ph, NQ))
    lnn = s([c[EQ('L')], s([pr, fp], 'eqeltrd', '( %s -> ( 1st ` ( ProdL ` Q ) ) e. NN )' % ph)], 'eqeltrd', '( %s -> L e. NN )' % ph)
    l1 = s([lnn, w.inst('nnge1')], 'syl', '( %s -> 1 <_ L )' % ph)
    cl.leaf('L', 'NN0', s([lnn], 'nnnn0d', '( %s -> L e. NN0 )' % ph))
    ple = s([qw, s([bn, ralqb], 'jca', '( %s -> ( B e. NN0 /\\ A. a e. ran Q a < ( 2 ^ B ) ) )' % ph), w.inst('t12prodle')], 'sylc',
            '( %s -> ( 1st ` ( ProdL ` Q ) ) <_ ( 2 ^ ( %s x. B ) ) )' % (ph, NQ))
    ple2 = s([c[EQ('L')], s([ple, s([s([nq], 'oveq1d', '( %s -> ( %s x. B ) = ( U x. B ) )' % (ph, NQ))], 'oveq2d', '( %s -> ( 2 ^ ( %s x. B ) ) = ( 2 ^ ( U x. B ) ) )' % (ph, NQ))],
                              'breqtrd', '( %s -> ( 1st ` ( ProdL ` Q ) ) <_ ( 2 ^ ( U x. B ) ) )' % ph)], 'eqbrtrd', '( %s -> L <_ ( 2 ^ ( U x. B ) ) )' % ph)
    UB = '( U x. B )'
    for e_ in (UB, UB1, "B'", '( 5 x. %s )' % UB, '( ( 5 x. %s ) + 1 )' % UB, '( ( 5 x. %s ) + 2 )' % UB):
        p2leaf(w, ph, cl, e_)
    lt1 = pow2lt(w, ph, cl, UB, UB1, linarith(w, ph, [], '%s < %s' % (UB, UB1), closure=cl))
    llt = linarith(w, ph, [ple2, lt1], 'L < ( 2 ^ %s )' % UB1, closure=cl)
    le1 = pow2le(w, ph, cl, UB1, "B'", linarith(w, ph, [sb5, cl.ge0(UB)], "%s <_ B'" % UB1, closure=cl))
    llt1 = linarith(w, ph, [llt, le1], "L < ( 2 ^ B' )", closure=cl)
    # X = L ^ 5 <_ ( 2 ^ ( U B ) ) ^ 5 = 2 ^ ( 5 U B )
    x5 = s([cl.mem('L', 'RR'), cl.mem('( 2 ^ %s )' % UB, 'RR'), closed(w, ph, '5nn0', '5 e. NN0'), cl.ge0('L'), ple2], 'leexp1ad' if False else 'id', '') if False else None
    j5 = s([s([cl.mem('L', 'RR'), cl.mem('( 2 ^ %s )' % UB, 'RR'), closed(w, ph, '5nn0', '5 e. NN0')], '3jca', '( %s -> ( L e. RR /\\ ( 2 ^ %s ) e. RR /\\ 5 e. NN0 ) )' % (ph, UB)),
            s([cl.ge0('L'), ple2], 'jca', '( %s -> ( 0 <_ L /\\ L <_ ( 2 ^ %s ) ) )' % (ph, UB))], 'jca',
           '( %s -> ( ( L e. RR /\\ ( 2 ^ %s ) e. RR /\\ 5 e. NN0 ) /\\ ( 0 <_ L /\\ L <_ ( 2 ^ %s ) ) ) )' % (ph, UB, UB))
    x5 = s([j5, w.inst('leexp1a')], 'syl', '( %s -> ( L ^ 5 ) <_ ( ( 2 ^ %s ) ^ 5 ) )' % (ph, UB))
    em = s([closed(w, ph, '2cn', '2 e. CC'), cl.mem(UB, 'NN0'), closed(w, ph, '5nn0', '5 e. NN0'), w.inst('expmul')], 'syl3anc',
           '( %s -> ( 2 ^ ( %s x. 5 ) ) = ( ( 2 ^ %s ) ^ 5 ) )' % (ph, UB, UB))
    e5 = lineq(w, ph, '( %s x. 5 )' % UB, '( 5 x. %s )' % UB, closure=cl, products=True)
    em2 = s([s([e5], 'oveq2d', '( %s -> ( 2 ^ ( %s x. 5 ) ) = ( 2 ^ ( 5 x. %s ) ) )' % (ph, UB, UB)), em], 'eqtr3d', '( %s -> ( 2 ^ ( 5 x. %s ) ) = ( ( 2 ^ %s ) ^ 5 ) )' % (ph, UB, UB))
    cl.leaf('( L ^ 5 )', 'NN0', s([cl.mem('L', 'NN0'), closed(w, ph, '5nn0', '5 e. NN0')], 'nn0expcld', '( %s -> ( L ^ 5 ) e. NN0 )' % ph))
    cl.leaf('( ( 2 ^ %s ) ^ 5 )' % UB, 'NN0', s([cl.mem('( 2 ^ %s )' % UB, 'NN0'), closed(w, ph, '5nn0', '5 e. NN0')], 'nn0expcld', '( %s -> ( ( 2 ^ %s ) ^ 5 ) e. NN0 )' % (ph, UB)))
    xle = linarith(w, ph, [x5, em2], '( L ^ 5 ) <_ ( 2 ^ ( 5 x. %s ) )' % UB, closure=cl)
    xeq = c[EQ('X')]
    cl.leaf('X', 'NN0', s([xeq, cl.mem('( L ^ 5 )', 'NN0')], 'eqeltrd', '( %s -> X e. NN0 )' % ph))
    xle2 = s([xeq, xle], 'eqbrtrd', '( %s -> X <_ ( 2 ^ ( 5 x. %s ) ) )' % (ph, UB))
    lt51 = pow2lt(w, ph, cl, '( 5 x. %s )' % UB, '( ( 5 x. %s ) + 1 )' % UB, linarith(w, ph, [], '( 5 x. %s ) < ( ( 5 x. %s ) + 1 )' % (UB, UB), closure=cl))
    lt52 = pow2lt(w, ph, cl, '( ( 5 x. %s ) + 1 )' % UB, '( ( 5 x. %s ) + 2 )' % UB, linarith(w, ph, [], '( ( 5 x. %s ) + 1 ) < ( ( 5 x. %s ) + 2 )' % (UB, UB), closure=cl))
    le52 = pow2le(w, ph, cl, '( ( 5 x. %s ) + 2 )' % UB, "B'", linarith(w, ph, [sb5], "( ( 5 x. %s ) + 2 ) <_ B'" % UB, closure=cl))
    xlt = linarith(w, ph, [xle2, lt51, lt52, le52], "X < ( 2 ^ B' )", closure=cl)
    # 1 + X <_ 2 ^ ( 5 U B ) + 2 ^ ( 5 U B ) = 2 ^ ( 5 U B + 1 )
    ge1 = s([closed(w, ph, '2re', '2 e. RR'), cl.mem('( 5 x. %s )' % UB, 'NN0'), closed(w, ph, '1le2', '1 <_ 2'), w.inst('expge1')], 'syl3anc', '( %s -> 1 <_ ( 2 ^ ( 5 x. %s ) ) )' % (ph, UB))
    p1 = s([closed(w, ph, '2cn', '2 e. CC'), cl.mem('( 5 x. %s )' % UB, 'NN0'), w.inst('expp1')], 'syl2anc', '( %s -> ( 2 ^ ( ( 5 x. %s ) + 1 ) ) = ( ( 2 ^ ( 5 x. %s ) ) x. 2 ) )' % (ph, UB, UB))
    x1lt = linarith(w, ph, [xle2, ge1, p1, lt52, le52], "( 1 + X ) < ( 2 ^ B' )", closure=cl)
    # the encoded window
    lq = s([qw, bn, ralqb, w.inst('tm2lenclen')], 'syl3anc', '( %s -> ( # ` ( encList ` Q ) ) <_ ( ( %s x. ( B + 1 ) ) + 1 ) )' % (ph, NQ))
    lq2 = s([lq, s([s([nq], 'oveq1d', '( %s -> ( %s x. ( B + 1 ) ) = ( U x. ( B + 1 ) ) )' % (ph, NQ))], 'oveq1d', '( %s -> ( ( %s x. ( B + 1 ) ) + 1 ) = ( ( U x. ( B + 1 ) ) + 1 ) )' % (ph, NQ))],
            'breqtrd', '( %s -> ( # ` ( encList ` Q ) ) <_ ( ( U x. ( B + 1 ) ) + 1 ) )' % ph)
    leaf = {'( # ` Q ) = U': nq, '( 2nd ` ( ProdL ` Q ) ) = U': pc2, RALB('Q', "B'"): ralq, 'A. a e. ran Q 1 <_ a': ralq1, '1 <_ L': l1, 'L < ( 2 ^ %s )' % UB1: llt,
            LT2('L', "B'"): llt1, LT2('X', "B'"): xlt, "( 1 + X ) < ( 2 ^ B' )": x1lt, '( # ` ( encList ` Q ) ) <_ ( ( U x. ( B + 1 ) ) + 1 )': lq2}
    st = bld_tree(w, ph, C_Q, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcl2
def t13srcl2():
    lab = 't13srcl2'
    ph = cj(T_L2)
    w = W(lab, 'Lean\'s ` hE ` : ` ( L + 1 ) ^ 2 ( 2 ^ T + 2 ) <_ E0 ` for ` L < 2 ^ ( T bs + 1 ) ` , times the unit ` U\' ` .')
    s = w.s
    c = Ctx(w, ph, T_L2)
    ln, llt, un, bn, upn, weq = c['L e. NN0'], c['L < ( 2 ^ %s )' % UB1], c['U e. NN0'], c['B e. NN0'], c["U' e. NN0"], c[WEQ]
    cl = Closure(w, ph, {'L': ('NN0', ln), 'U': ('NN0', un), 'B': ('NN0', bn), "U'": ('NN0', upn)})
    p2leaf(w, ph, cl, UB1); p2leaf(w, ph, cl, 'U')
    P2 = '( 2 ^ %s )' % UB1
    l1 = s([llt, s([ln, cl.mem(P2, 'NN0'), w.inst('nn0ltp1le')], 'syl2anc', '( %s -> ( L < %s <-> ( L + 1 ) <_ %s ) )' % (ph, P2, P2))], 'mpbid',
           '( %s -> ( L + 1 ) <_ %s )' % (ph, P2))
    j = s([s([cl.mem('( L + 1 )', 'RR'), cl.mem(P2, 'RR'), closed(w, ph, '2nn0', '2 e. NN0')], '3jca', '( %s -> ( ( L + 1 ) e. RR /\\ %s e. RR /\\ 2 e. NN0 ) )' % (ph, P2)),
           s([cl.ge0('( L + 1 )'), l1], 'jca', '( %s -> ( 0 <_ ( L + 1 ) /\\ ( L + 1 ) <_ %s ) )' % (ph, P2))], 'jca',
          '( %s -> ( ( ( L + 1 ) e. RR /\\ %s e. RR /\\ 2 e. NN0 ) /\\ ( 0 <_ ( L + 1 ) /\\ ( L + 1 ) <_ %s ) ) )' % (ph, P2, P2))
    sq = s([j, w.inst('leexp1a')], 'syl', '( %s -> %s <_ ( %s ^ 2 ) )' % (ph, LSQ, P2))
    cl.leaf(LSQ, 'NN0', s([cl.mem('( L + 1 )', 'NN0'), closed(w, ph, '2nn0', '2 e. NN0')], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, LSQ)))
    cl.leaf('( %s ^ 2 )' % P2, 'NN0', s([cl.mem(P2, 'NN0'), closed(w, ph, '2nn0', '2 e. NN0')], 'nn0expcld', '( %s -> ( %s ^ 2 ) e. NN0 )' % (ph, P2)))
    m1 = lemul1a(w, ph, cl, LSQ, '( %s ^ 2 )' % P2, '( %s + 2 )' % P2U, sq)
    m2 = lemul1a(w, ph, cl, '( %s x. ( %s + 2 ) )' % (LSQ, P2U), E0_, "U'", m1)
    st = s([m2, s([weq], 'eqcomd', "( %s -> ( %s x. U' ) = W' )" % (ph, E0_))], 'breqtrd', '( %s -> %s )' % (ph, C_L2))
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcu: the units at the pool length P
def t13srcu():
    lab = 't13srcu'
    ph = cj(T_U)
    w = W(lab, 'The unit facts at the pool length ` P <_ 2 ^ T ` from those at ` 2 ^ T ` (Lean\'s ` hbMU hBM hPV hLPV hB4 hexY ` '
               'and the verify bit bound): products against ` U\' ` and ` W\' = E0 U\' ` (~ lemul12a , ~ tmbmono ).')
    s = w.s
    c = Ctx(w, ph, T_U)
    pn, pl, un, ln, bn, upn, wpn = c['P e. NN0'], c['P <_ %s' % P2U], c['U e. NN0'], c['L e. NN0'], c["B' e. NN0"], c["U' e. NN0"], c["W' e. NN0"]
    cl = Closure(w, ph, {'P': ('NN0', pn), 'U': ('NN0', un), 'L': ('NN0', ln), "B'": ('NN0', bn), "U'": ('NN0', upn), "W'": ('NN0', wpn)})
    p2leaf(w, ph, cl, 'U')
    NP = NPP
    w2u = linarith(w, ph, [pl], '( P + 1 ) <_ ( %s + 1 )' % P2U, closure=cl)
    npb = P.mul_le2(w, ph, cl, "B'", '( P + 1 )', '( %s + 1 )' % P2U, w2u)
    nple = linarith(w, ph, [npb], '%s <_ %s' % (NP, NPU), closure=cl)
    np2 = linarith(w, ph, [nple, c["( %s + 2 ) <_ U'" % NPU]], "( %s + 2 ) <_ U'" % NP, closure=cl)
    for e_ in (NP, NPU, EXXU, "( ( ( 3 x. P ) x. B' ) + ( ( 5 x. B' ) + 5 ) )"):
        tmbleaf(w, ph, cl, e_)
    tbnp = linarith(w, ph, [tmbmono(w, ph, cl, NP, NPU, nple), c["( TMB ` %s ) <_ U'" % NPU]], "( TMB ` %s ) <_ U'" % NP, closure=cl)
    w2 = linarith(w, ph, [pl], '( P + 2 ) <_ ( %s + 2 )' % P2U, closure=cl)
    wu = lemul1a(w, ph, cl, '( P + 2 )', '( %s + 2 )' % P2U, "U'", w2)
    hw2 = linarith(w, ph, [wu, c["( ( %s + 2 ) x. U' ) <_ W'" % P2U]], "( ( P + 2 ) x. U' ) <_ W'", closure=cl)
    wb2 = P.mul_le2(w, ph, cl, '( P + 2 )', "( B' + 2 )", "U'", c["( B' + 2 ) <_ U'"])
    hpv = linarith(w, ph, [wb2, hw2, cl.ge0('P'), cl.ge0("B'")], "( ( P x. ( B' + 1 ) ) + 1 ) <_ W'", closure=cl, products=True)
    cl.atom(LSQ)
    cl.leaf(LSQ, 'NN0', s([cl.mem('( L + 1 )', 'NN0'), closed(w, ph, '2nn0', '2 e. NN0')], 'nn0expcld', '( %s -> %s e. NN0 )' % (ph, LSQ)))
    sq = s([cl.mem('( L + 1 )', 'CC'), w.inst('sqval')], 'syl', '( %s -> %s = ( ( L + 1 ) x. ( L + 1 ) ) )' % (ph, LSQ))
    l1sq = linarith(w, ph, [sq, P.mul_le2(w, ph, cl, '( L + 1 )', '1', '( L + 1 )', linarith(w, ph, [cl.ge0('L')], '1 <_ ( L + 1 )', closure=cl))], '( L + 1 ) <_ %s' % LSQ,
                    closure=cl, products=True)
    PRD = "( ( P + 2 ) x. ( B' + 2 ) )"
    PRDU = "( ( %s + 2 ) x. U' )" % P2U
    prdle = linarith(w, ph, [wb2, wu], '%s <_ %s' % (PRD, PRDU), closure=cl, products=True)
    l1p = P.mul_le2(w, ph, cl, '( L + 1 )', PRD, PRDU, prdle)
    l2p = lemul1a(w, ph, cl, '( L + 1 )', LSQ, PRDU, l1sq)
    hlpv = linarith(w, ph, [l1p, l2p, c["( ( %s x. ( %s + 2 ) ) x. U' ) <_ W'" % (LSQ, P2U)], cl.ge0('L'), cl.ge0('P'), cl.ge0("B'")],
                    "( ( L x. ( ( P x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'", closure=cl, products=True)
    VXP = VX4.replace('( # ` A )', 'P').replace(" N' )", ' %s )' % NP)
    wb = lemul1a(w, ph, cl, 'P', P2U, "B'", pl)
    vxw = linarith(w, ph, [wb, nple], '( ( 4 x. %s ) + 6 ) <_ ( ( 4 x. %s ) + 6 )' % (VXP, VXU), closure=cl, products=True)
    for e_ in (VXP, VXU):
        tmbleaf(w, ph, cl, '( ( 4 x. %s ) + 6 )' % e_)
    tbv = tmbmono(w, ph, cl, '( ( 4 x. %s ) + 6 )' % VXP, '( ( 4 x. %s ) + 6 )' % VXU, vxw)
    hb5w = linarith(w, ph, [tbv, c["( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ U'" % VXU]], HB5PN, closure=cl)
    assert HB5PN == "( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ U'" % VXP, (HB5PN, VXP)
    EXXW = "( ( ( 3 x. P ) x. B' ) + ( ( 5 x. B' ) + 5 ) )"
    exx = linarith(w, ph, [wb], '%s <_ %s' % (EXXW, EXXU), closure=cl, products=True)
    tbx = linarith(w, ph, [tmbmono(w, ph, cl, EXXW, EXXU, exx), c["( TMB ` %s ) <_ U'" % EXXU]], "( TMB ` %s ) <_ U'" % EXXW, closure=cl)
    m1 = P.mul_le(w, ph, cl, '( P + 2 )', '( %s + 2 )' % P2U, '( TMB ` %s )' % EXXW, "U'", w2, tbx)
    m2 = P.mul_le2(w, ph, cl, LSQ, '( ( P + 2 ) x. ( TMB ` %s ) )' % EXXW, PRDU, m1)
    asx = lineq(w, ph, "( %s x. ( ( P + 2 ) x. ( TMB ` %s ) ) )" % (LSQ, EXXW), EXYP, closure=cl, products=True)
    asu = lineq(w, ph, "( %s x. %s )" % (LSQ, PRDU), "( ( %s x. ( %s + 2 ) ) x. U' )" % (LSQ, P2U), closure=cl, products=True)
    hexy = linarith(w, ph, [m2, asx, asu, c["( ( %s x. ( %s + 2 ) ) x. U' ) <_ W'" % (LSQ, P2U)]], "%s <_ W'" % EXYP, closure=cl, products=True)
    leaf = {"( %s + 2 ) <_ U'" % NP: np2, "( TMB ` %s ) <_ U'" % NP: tbnp, "( ( P + 2 ) x. U' ) <_ W'": hw2, "( ( P x. ( B' + 1 ) ) + 1 ) <_ W'": hpv,
            "( ( L x. ( ( P x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'": hlpv, HB5PN: hb5w, "%s <_ W'" % EXYP: hexy}
    st = bld_tree(w, ph, C_U, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()



# ------------------------------------------------------------ t13srcw: the pool in the scan's some case (~ tmscsome , ~ poolalgval , ~ poolgomemi , ~ t12pglen )
SCAN = P.SCAN
KSC, PSC = P.KSC, P.PSC
T_W = ((T_TY, ('( 1st ` J ) =/= %s' % INR, '( # ` Q ) = U', '1 <_ L')), (("B' e. NN0", LT2('X', "B'")), "( 1 + X ) < ( 2 ^ B' )"))
C_W = ((RALB('W', "B'"), 'A. a e. ran W 2 <_ a'), ('( # ` W ) <_ ( 2 ^ U )', LT2("J'", "B'")))
add13('t13srcw', T_W, cj(C_W))


def t13srcw():
    lab = 't13srcw'
    ph = cj(T_W)
    w = W(lab, 'The pool of the scan\'s some case (Lean ` scan_some ` , ` poolAlg_mem ` , ` poolAlg_length_le_two_pow ` ): its '
               'entries are primes at most ` x ` , so below ` 2 ^ b1 ` and at least 2 (~ poolgomemi ), there are at most '
               '` 2 ^ T ` of them (~ t12pglen , ~ divisorsoflen ), and ` k\' < 1 + x < 2 ^ b1 ` (~ tmscsome ).')
    s = w.s
    c = Ctx(w, ph, T_W)
    cl = letter_cl(w, ph, c)
    ty = P.stage_typing(w, ph, c, cl)
    ty.update(some_typing13(w, ph, c, cl, ty))
    jne, nq, bn = c['( 1st ` J ) =/= %s' % INR], c['( # ` Q ) = U'], c["B' e. NN0"]
    cl.leaf("B'", 'NN0', bn)
    jsc = s([c[EQ('J')]], 'eqcomd', '( %s -> %s = J )' % (ph, SCAN))
    nns = s([jne, s([s([jsc], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (ph, SCAN))], 'neeq1d', '( %s -> ( ( 1st ` %s ) =/= %s <-> ( 1st ` J ) =/= %s ) )' % (ph, SCAN, INR, INR))],
             'mpbird', '( %s -> ( 1st ` %s ) =/= %s )' % (ph, SCAN, INR))
    kj = s([c[EQ("J'")], s([s([s([jsc], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (ph, SCAN))], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` J ) ) )' % (ph, SCAN))],
                            'fveq2d', "( %s -> %s = %s )" % (ph, KSC, LEQD["J'"]))], 'eqtr4d', "( %s -> J' = %s )" % (ph, KSC))
    pw = s([c[EQ('W')], s([s([s([jsc], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (ph, SCAN))], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` J ) ) )' % (ph, SCAN))],
                            'fveq2d', "( %s -> %s = %s )" % (ph, PSC, LEQD['W']))], 'eqtr4d', "( %s -> W = %s )" % (ph, PSC))
    sq1 = s([ty['Q'], s([ty['X'], ty['zn0'], c['O e. NN0']], '3jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) )' % ph)], 'jca',
             '( %s -> ( Q e. Word NN0 /\\ ( X e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) ) )' % ph)
    sq2 = s([s([closed(w, ph, '1nn0', '1 e. NN0'), ty['X']], 'jca', '( %s -> ( 1 e. NN0 /\\ X e. NN0 ) )' % ph), nns], 'jca',
            '( %s -> ( ( 1 e. NN0 /\\ X e. NN0 ) /\\ ( 1st ` %s ) =/= %s ) )' % (ph, SCAN, INR))
    sq3 = s([sq1, sq2], 'jca', '( %s -> ( ( Q e. Word NN0 /\\ ( X e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) ) /\\ ( ( 1 e. NN0 /\\ X e. NN0 ) /\\ ( 1st ` %s ) =/= %s ) ) )' % (ph, SCAN, INR))
    smc = tsub_text(split_imp(stmt('tmscsome'))[1], {'W': 'Q', 'F': 'X', 'G': '1', 'H': 'X'})
    sm = s([sq3, w.inst('tmscsome')], 'syl', '( %s -> %s )' % (ph, smc))
    csm = Ctx(w, ph, parse_conj(smc), root=sm)
    klt = csm['%s < ( 1 + X )' % KSC]
    PAV = '( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` %s ) )' % KSC
    weq = csm['%s = %s' % (PSC, PAV)]
    jpk = s([kj, klt], 'eqbrtrd', "( %s -> J' < ( 1 + X ) )" % ph)
    cl.leaf('( 1 + X )', 'NN0', cl.mem('( 1 + X )', 'NN0'))
    p2leaf(w, ph, cl, "B'")
    jlt = linarith(w, ph, [jpk, c["( 1 + X ) < ( 2 ^ B' )"]], "J' < ( 2 ^ B' )", closure=cl)
    DIVS = '( 1st ` ( DivisorsOf ` Q ) )'
    PGJ = lambda s_: "( ( ( X PoolGo Z ) ` J' ) ` %s )" % s_
    pav = s([s([s([s([ty['Q'], ty['X']], 'jca', '( %s -> ( Q e. Word NN0 /\\ X e. NN0 ) )' % ph), ty['zn0']], 'jca', '( %s -> ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % ph), ty["J'"]], 'jca',
               "( %s -> ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ J' e. NN0 ) )" % ph), w.inst('poolalgval')], 'syl',
            "( %s -> ( ( ( Q PoolAlg X ) ` Z ) ` J' ) = <. ( 1st ` %s ) , ( ( 2nd ` ( DivisorsOf ` Q ) ) + ( 2nd ` %s ) ) >. )" % (ph, PGJ(DIVS), PGJ(DIVS)))
    CST_ = '( ( 2nd ` ( DivisorsOf ` Q ) ) + ( 2nd ` %s ) )' % PGJ(DIVS)
    p1v = s([s([pav], 'fveq2d', "( %s -> ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) = ( 1st ` <. ( 1st ` %s ) , %s >. ) )" % (ph, PGJ(DIVS), CST_)),
             s([s([s([], 'fvex', '( 1st ` %s ) e. _V' % PGJ(DIVS)), s([], 'ovex', '%s e. _V' % CST_)], 'op1st', '( 1st ` <. ( 1st ` %s ) , %s >. ) = ( 1st ` %s )' % (PGJ(DIVS), CST_, PGJ(DIVS)))], 'a1i',
               '( %s -> ( 1st ` <. ( 1st ` %s ) , %s >. ) = ( 1st ` %s ) )' % (ph, PGJ(DIVS), CST_, PGJ(DIVS)))], 'eqtrd',
            "( %s -> ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) = ( 1st ` %s ) )" % (ph, PGJ(DIVS)))
    pavk = s([s([kj], 'fveq2d', "( %s -> ( ( ( Q PoolAlg X ) ` Z ) ` J' ) = ( ( ( Q PoolAlg X ) ` Z ) ` %s ) )" % (ph, KSC))], 'fveq2d',
             "( %s -> ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) = %s )" % (ph, PAV))
    wpg = s([s([pw, weq], 'eqtrd', '( %s -> W = %s )' % (ph, PAV)), s([pavk], 'eqcomd', "( %s -> %s = ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) )" % (ph, PAV)), p1v], '3eqtrd',
            '( %s -> W = ( 1st ` %s ) )' % (ph, PGJ(DIVS)))
    dcl = s([s([ty['Q'], w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` Q ) e. ( Word NN0 X. NN0 ) )' % ph), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, DIVS))
    xzj = s([ty['X'], ty['zn0'], ty["J'"]], '3jca', "( %s -> ( X e. NN0 /\\ Z e. NN0 /\\ J' e. NN0 ) )" % ph)
    pp = '( %s /\\ p e. ran W )' % ph
    wrn = s([s([ty['W'], w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % ph), w.inst('frn')], 'syl', '( %s -> ran W C_ NN0 )' % ph)
    pn0 = s([s([wrn], 'adantr', '( %s -> ran W C_ NN0 )' % pp), s([], 'simpr', '( %s -> p e. ran W )' % pp)], 'sseldd', '( %s -> p e. NN0 )' % pp)
    pin = s([s([], 'simpr', '( %s -> p e. ran W )' % pp), s([s([wpg], 'rneqd', '( %s -> ran W = ran ( 1st ` %s ) )' % (ph, PGJ(DIVS)))], 'adantr', '( %s -> ran W = ran ( 1st ` %s ) )' % (pp, PGJ(DIVS)))],
            'eleqtrd', '( %s -> p e. ran ( 1st ` %s ) )' % (pp, PGJ(DIVS)))
    gmi = s([s([s([xzj], 'adantr', "( %s -> ( X e. NN0 /\\ Z e. NN0 /\\ J' e. NN0 ) )" % pp), s([s([dcl], 'adantr', '( %s -> %s e. Word NN0 )' % (pp, DIVS)), pn0], 'jca', '( %s -> ( %s e. Word NN0 /\\ p e. NN0 ) )' % (pp, DIVS))], 'jca',
               "( %s -> ( ( X e. NN0 /\\ Z e. NN0 /\\ J' e. NN0 ) /\\ ( %s e. Word NN0 /\\ p e. NN0 ) ) )" % (pp, DIVS)), w.inst('poolgomemi')], 'syl',
            "( %s -> ( p e. ran ( 1st ` %s ) <-> E. d e. ran %s ( ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) ) ) )" % (pp, PGJ(DIVS), DIVS))
    exd = s([pin, gmi], 'mpbid', "( %s -> E. d e. ran %s ( ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) ) )" % (pp, DIVS))
    BODYD = "( ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) )"
    pd = '( %s /\\ ( d e. ran %s /\\ %s ) )' % (pp, DIVS, BODYD)
    bd = s([s([], 'simpr', '( %s -> ( d e. ran %s /\\ %s ) )' % (pd, DIVS, BODYD))], 'simprd', '( %s -> %s )' % (pd, BODYD))
    pxp = s([s([s([bd], 'simpld', "( %s -> ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) )" % pd)], 'simprd', '( %s -> p <_ X )' % pd),
             s([s([bd], 'simprd', '( %s -> ( Z < p /\\ p e. Prime ) )' % pd)], 'simprd', '( %s -> p e. Prime )' % pd)], 'jca', '( %s -> ( p <_ X /\\ p e. Prime ) )' % pd)
    pf = s([exd, pxp], 'rexlimddv', '( %s -> ( p <_ X /\\ p e. Prime ) )' % pp)
    clp = Closure(w, pp, {'p': ('NN0', pn0), 'X': ('NN0', s([ty['X']], 'adantr', '( %s -> X e. NN0 )' % pp))})
    clp.atom("( 2 ^ B' )"); clp.leaf("( 2 ^ B' )", 'NN0', s([cl.mem("( 2 ^ B' )", 'NN0')], 'adantr', "( %s -> ( 2 ^ B' ) e. NN0 )" % pp))
    plt = linarith(w, pp, [s([pf], 'simpld', '( %s -> p <_ X )' % pp), s([c[LT2('X', "B'")]], 'adantr', "( %s -> X < ( 2 ^ B' ) )" % pp)], "p < ( 2 ^ B' )", closure=clp)
    p2 = s([s([s([s([pf], 'simprd', '( %s -> p e. Prime )' % pp), w.inst('prmuz2')], 'syl', '( %s -> p e. ( ZZ>= ` 2 ) )' % pp), w.inst('eluz2')], 'sylib',
             '( %s -> ( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p ) )' % pp)], 'simp3d', '( %s -> 2 <_ p )' % pp)
    ralw = P.cbv_a(w, ph, s([plt], 'ralrimiva', "( %s -> A. p e. ran W p < ( 2 ^ B' ) )" % ph), None, "p < ( 2 ^ B' )", "a < ( 2 ^ B' )", 'p', 'ran W')
    ralw2 = P.cbv_a(w, ph, s([p2], 'ralrimiva', '( %s -> A. p e. ran W 2 <_ p )' % ph), None, '2 <_ p', '2 <_ a', 'p', 'ran W')
    pgl = s([dcl, s([ty['X'], ty['zn0'], ty["J'"]], '3jca', "( %s -> ( X e. NN0 /\\ Z e. NN0 /\\ J' e. NN0 ) )" % ph), w.inst('t12pglen')], 'sylc',
            '( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` %s ) )' % (ph, PGJ(DIVS), DIVS))
    dl = s([ty['Q'], w.inst('divisorsoflen')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` Q ) ) )' % (ph, DIVS))
    dl2 = s([dl, s([nq], 'oveq2d', '( %s -> ( 2 ^ ( # ` Q ) ) = ( 2 ^ U ) )' % ph)], 'eqtrd', '( %s -> ( # ` %s ) = ( 2 ^ U ) )' % (ph, DIVS))
    wle = s([s([s([wpg], 'fveq2d', '( %s -> ( # ` W ) = ( # ` ( 1st ` %s ) ) )' % (ph, PGJ(DIVS))), pgl], 'eqbrtrd', '( %s -> ( # ` W ) <_ ( # ` %s ) )' % (ph, DIVS)), dl2], 'breqtrd',
            '( %s -> ( # ` W ) <_ ( 2 ^ U ) )' % ph)
    leaf = {RALB('W', "B'"): ralw, 'A. a e. ran W 2 <_ a': ralw2, '( # ` W ) <_ ( 2 ^ U )': wle, LT2("J'", "B'"): jlt}
    st = bld_tree(w, ph, C_W, lambda t: leaf[t])
    qed13(w, st, lab)
    return w.run()


# ------------------------------------------------------------ t13srcqa: the window's first facts (the part of t13srcq the scan stage needs)
T_QA = ((SC_TY, LEQT[0]), (('U <_ I', LT2('Z')), ('B e. NN0', "B' e. NN0"), "B <_ B'"))
C_QA = ('( # ` Q ) = U', RALB('Q', "B'"), 'A. a e. ran Q 1 <_ a')
add13('t13srcqa', T_QA, cj(C_QA))


def t13srcqa():
    lab = 't13srcqa'
    ph = cj(T_QA)
    w = W(lab, 'The window ` Q ` of the reservoir (~ a5q ): ` T ` primes at most ` z ` , so below ` 2 ^ b1 ` and at least 1.')
    s = w.s
    c = Ctx(w, ph, T_QA)
    zn, gn, yn, un = [c[t] for t in ('Z e. NN', 'G e. NN0', 'Y e. NN', 'U e. NN0')]
    bn, b1n, ui, zb, bb1 = c['B e. NN0'], c["B' e. NN0"], c['U <_ I'], c[LT2('Z')], c["B <_ B'"]
    cl = Closure(w, ph, {'U': ('NN0', un), 'B': ('NN0', bn), "B'": ('NN0', b1n)})
    cl.leaf('Z', 'NN0', s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph))
    h1 = s([zn, gn, yn], '3jca', '( %s -> ( Z e. NN /\\ G e. NN0 /\\ Y e. NN ) )' % ph)
    aq = s([h1, un, c[EQ('R')], c[EQ('I')], c[EQ('Q')], ui], 'a5q',
           '( %s -> ( ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = U /\\ ( # ` ran Q ) = U ) ) /\\ ( ( ran Q C_ ( ( Z goodPrimesW G ) ` Y ) /\\ '
           'ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) ) )' % ph)
    nq = s([s([s([aq], 'simpld', '( %s -> ( ( Q e. Word NN0 /\\ Fun `\' Q ) /\\ ( ( # ` Q ) = U /\\ ( # ` ran Q ) = U ) ) )' % ph)], 'simprd',
              '( %s -> ( ( # ` Q ) = U /\\ ( # ` ran Q ) = U ) )' % ph)], 'simpld', '( %s -> ( # ` Q ) = U )' % ph)
    qpr = s([s([aq], 'simprd', '( %s -> ( ( ran Q C_ ( ( Z goodPrimesW G ) ` Y ) /\\ ran Q e. ( ~P Prime i^i Fin ) ) /\\ A. c e. ran Q ( c e. Prime /\\ c <_ Z ) ) )' % ph)],
             'simprd', '( %s -> A. c e. ran Q ( c e. Prime /\\ c <_ Z ) )' % ph)
    pq = '( %s /\\ c e. ran Q )' % ph
    cf = s([qpr], 'r19.21bi', '( %s -> ( c e. Prime /\\ c <_ Z ) )' % pq)
    cpr = s([cf], 'simpld', '( %s -> c e. Prime )' % pq)
    cle = s([cf], 'simprd', '( %s -> c <_ Z )' % pq)
    cuz = s([s([cpr, w.inst('prmuz2')], 'syl', '( %s -> c e. ( ZZ>= ` 2 ) )' % pq), w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ c e. ZZ /\\ 2 <_ c ) )' % pq)
    c2 = s([cuz], 'simp3d', '( %s -> 2 <_ c )' % pq)
    cz = s([cuz], 'simp2d', '( %s -> c e. ZZ )' % pq)
    clq = Closure(w, pq, {})
    clq.leaf('c', 'ZZ', cz); clq.leaf('Z', 'NN0', lift_from(w, ph, pq, cl.mem('Z', 'NN0')))
    for e_ in ('B', "B'"):
        clq.atom('( 2 ^ %s )' % e_)
        clq.leaf('( 2 ^ %s )' % e_, 'NN0', lift_from(w, ph, pq, s([closed(w, ph, '2nn0', '2 e. NN0'), cl.mem(e_, 'NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, e_))))
    pbb = pow2le(w, ph, cl, 'B', "B'", bb1)
    clt1 = linarith(w, pq, [cle, lift_from(w, ph, pq, zb), lift_from(w, ph, pq, pbb)], "c < ( 2 ^ B' )", closure=clq)
    c1 = linarith(w, pq, [c2], '1 <_ c', closure=clq)
    ralq = P.cbv_a(w, ph, s([clt1], 'ralrimiva', "( %s -> A. c e. ran Q c < ( 2 ^ B' ) )" % ph), None, "c < ( 2 ^ B' )", "a < ( 2 ^ B' )", 'c', 'ran Q')
    ralq1 = P.cbv_a(w, ph, s([c1], 'ralrimiva', '( %s -> A. c e. ran Q 1 <_ c )' % ph), None, '1 <_ c', '1 <_ a', 'c', 'ran Q')
    st = s([nq, ralq, ralq1], '3jca', '( %s -> %s )' % (ph, cj(C_QA)))
    qed13(w, st, lab)
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
