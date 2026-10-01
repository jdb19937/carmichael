"""T12: searchF at the machine (Step5.lean ` searchF_le_B ` , ` searchF_runs ` ; blueprint D7).

  tmisrfl   the failure branch: from a ` branch flag ` label with the flag ` (/) ` , ` failAll ` (~ tmifal ) leaves
            ` initStacks 1 [ comma ] ` within the stack lengths plus 10
  tmisrpa   the prefix ` inputF ; scalesF ` : from ` initStacks 0 ( encNatGam n ) ` to ` initStacks 7 ( n comma ) `
            with the five scales pushed on 0 (~ tmiinp , ~ tmiscal , ~ t12ini )
  tmisrc4   the verify stage (after extract, at the third branch with the flag true): ~ tmiverb then ~ tmiout or
            ~ tmisrfl ; the letters of A1b's ~ searchval for the intermediate values (blueprint D7)
  tmisrc3   the extract stage: ~ tmiexfb then ~ tmisrc4 or ~ tmisrfl
  tmisrc2   the scan stage: ~ tmiscfb then ~ tmisrc3 or ~ tmisrfl
  tmisrcz   ` searchF_le_B ` with the letters: ~ tmisrpa , ~ tmis2fb , then ~ tmisrc2 or ~ tmisrfl
  tmisrchb  ` searchF_le_B ` (frozen): ~ tmisrcz with every letter instantiated, one at a time
  tmisrch   ` searchF_runs ` (frozen): ~ tmisrchb at ` sbs ` , ` sbn `

    MM_DB=sorties/t12.mm python3 tools/gen/t12_p_srch.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t12lib import *
from lin import linarith, lineq, nlinarith
from cl import Closure
from t7_e_cmp import machine, togk, letgk
from t7clib import setup
from t7lib import parts
from t10_n_rgf import tmbn
from t10_d_dot import cls_to, load_nfl, skip_ty
from t10_e_doa import lift_from
from t12_d_fal import to_init, init_vals, idx8, num_ne, EQ8_
from t12_j_acc import nfl_all, Plain
from t12_i_scal import proj_eq
import t8alib as A8
import t7c_h_lst as LST
import num
import lin
lin.FASTPATH = True

SEL = sys.argv[1:]
TB = lambda x: '( TMB ` %s )' % x
LMS = FRAGS['srch'].lmap()
FS = FRAGS['srch']
FLT = (('TMcar e. ( 2o ^m ( 2nd ` T ) )', 'TMda e. ( 2o ^m ( 2nd ` T ) )'),
       ('TMdb e. ( 2o ^m ( 2nd ` T ) )', 'TMfl e. ( 2o ^m ( 2nd ` T ) )'))
W0 = '( encNatGam ` N )'
W7 = '( %s ++ <" 4 "> )' % W0
INIT0 = INIT('0', W0)
INIT7 = INIT('7', W7)
CIN = '( ( 2 x. ( # ` ( encodeNat ` N ) ) ) + 4 )'
CSC = lambda b: '( ; 5 0 x. ( TMB ` ( ( 3 x. %s ) + 8 ) ) )' % b
SCALES = EWg(PZ(SC_), EWg(PZ99(SC_), EWg(PY(SC_), EWg(PT(SC_), EWg(PTH(SC_), '(/)')))))

# ------------------------------------------------------------ tmisrfl: the failure branch
FAL0 = '( Q ` 0 )'
BR = lambda x, f: '( M ` A ) = %s' % BRANCH('TMfl', GT(x), GT(f))
TREE_SRFL = ((T_PHM7, (BR('X', FAL0), 'TMIfal T M Q E')), ((LAB('A'), LAB('X')), STKD('D')))
CONCL_SRFL = TRI(CLN('A', NFL('(/)'), 'D'), CLN('E', S, INIT('1', COMMA1)), '( %s + 1 )' % FALC)
add12('tmisrfl', TREE_SRFL, CONCL_SRFL)

# ------------------------------------------------------------ tmisrpa: inputF ; scalesF
DATA_SRPA = (('C e. NN0', 'K e. NN', 'N e. NN0'), ('B e. NN0', (LT2('N'), LT2('C'), LT2('K'))))
TREE_SRPA = TREE0('srch', DATA_SRPA)
CONCL_SRPA = TRI(SRCHPRE, CLN(LMS['Y3'], S, UP(INIT7, '0', SCALES)), '( %s + %s )' % (CIN, CSC('B')))
add12('tmisrpa', TREE_SRPA, CONCL_SRPA)


def flt_leaves(w, ph, mk, ex):
    """the flag tests' typing (~ tmcflty ) into ex"""
    fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ph, cj(FLT)))
    ex.update(parts(w, ph, fl, FLT))
    return ex


def tmisrfl():
    lab = 'tmisrfl'
    T = numtree(TREE_SRFL)
    ph = cj(T)
    w = W(lab, 'The failure branch of Lean\'s ` searchF ` at the machine: at a ` branch flag ` label whose false '
               'branch goes to an installed ` failAll ` , with the flag ` (/) ` , the machine reaches the exit with '
               '` initStacks 1 [ comma ] ` (~ tm2fbrg , ~ tmifal ) within the sum of the stack lengths plus 10.')
    s = w.s
    B = Plain(w, ph, T)
    c, mk, ex = B.c, B.mk, B.ex
    ex.update(unfold_all(w, ph, c['TMIfal T M Q E'], 'fal', [], 'Q', 'E', rec=False))
    flt_leaves(w, ph, mk, ex)
    N0 = NFL('(/)')
    ex[STMT(GT('X'))] = gotocl(w, ph, mk['tv'], 'X', c[LAB('X')])
    ex['A. m e. %s -. ( TMfl ` m ) = 1o' % N0] = A8.ht_nfl(w, ph, '(/)')
    ex[SSS(N0)] = B.ss(N0)
    R = B.run()
    B.call(R, 'tm2fbrg', {'A': 'A', 'C': 'TMfl', 'E': FAL0, 'Q': GT('X'), 'N': N0}, ex, [])
    assert R.cur == CLN(FAL0, N0, 'D'), R.cur
    # failAll from ( Q ` 0 ) with the pre class shrunk to NFL( (/) )
    t2, cc2 = inst(w, ph, 'tmifal', {'P': 'Q', 'E': 'E'}, Bld(w, ph, c, ex))
    C2, D2, n2 = triple_parts(cc2)
    assert C2 == CLN(FAL0, S, 'D'), C2
    t2s = hrssc(w, ph, mk['phm'], t2, C2, D2, n2, CLN(FAL0, N0, 'D'), clnss(w, ph, FAL0, N0, S, 'D', B.ss(N0)))
    t = hrseq(w, ph, mk['phm'], R.tri, t2s, R.C0, R.cur, D2, R.n, n2)
    n = '( %s + %s )' % (R.n, n2)
    cl = Closure(w, ph, {})
    for k in N8:
        cl.leaf(LEN(DK(k)), 'NN0', s([B.S0.vals[k][2], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LEN(DK(k)))))
    BND = '( %s + 1 )' % FALC
    le = linarith(w, ph, [], '%s <_ %s' % (n, BND), closure=cl)
    st = hrle(w, ph, mk['phm'], t, R.C0, D2, n, BND, cl.mem(BND, 'NN0'), le)
    finish(w, st, lab)
    return w.run()


class IBase(Base):
    """a Base whose stacks are a given Stacks object (an ` initStacks ` term), not the letter D"""
    def __init__(self, w, ph, c, mk, ne, ex, S0):
        self.w, self.ph, self.ks = w, ph, N8
        self.c, self.mk, self.ne, self.ex = c, mk, ne, ex
        self.dd = S0.memb
        self.S0 = S0
        self.gam = {v[0]: v[2] for v in S0.vals.values()}


def init_stacks(w, ph, mk, ne, k0, W_, wg):
    """the Stacks object of INIT( k0 , W ) from wg : ( ph -> W e. Word Gamma' )"""
    s = w.s
    IN = INIT(k0, W_)
    wv = s([wg], 'elexd', '( %s -> %s e. _V )' % (ph, W_))
    iv = init_vals(w, ph, mk, k0, W_, wv)
    wgk = s([wg, mk['k'][k0]['wge']], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ph, W_, GX(k0)))
    memb = s([mk['tv'], mk['k'][k0]['kd'], wgk, w.inst('tm2initstk')], 'syl3anc', '( %s -> %s e. ( TM2Stk ` T ) )' % (ph, IN))
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    vals = {k: ((W_ if k == k0 else '(/)'), iv[k], (wg if k == k0 else wrd0)) for k in N8}
    return Stacks(w, ph, mk, IN, memb, ne, vals)


def tmisrpa():
    lab = 'tmisrpa'
    T = numtree(TREE_SRPA)
    ph = cj(T)
    w = W(lab, 'The prefix of Lean\'s ` searchF ` at the machine: ` inputF ` (~ tmiinp ) from ` initStacks 0 ( encNatGam n ) ` '
               'to ` initStacks 7 ( n comma ) ` , then ` scalesF C1 K ` (~ tmiscal ) at the bit bound ` b ` pushing the five '
               'scales of ` scalesTM C1 K n ` on 0, within ` 2 # encodeNat n + 4 + 50 B ( 3 b + 8 ) ` steps.')
    s = w.s
    c, mk, ne, ex = hsetup(w, ph, T, N8, 'srch')
    cn, knn, nn, bn = c['C e. NN0'], c['K e. NN'], c['N e. NN0'], c['B e. NN0']
    # 1. inputF
    t1, cc1 = inst(w, ph, 'tmiinp', {'N': 'N', 'P': PL('P', 4), 'E': LMS['Y2']}, Bld(w, ph, c, ex))
    C1, D1, n1 = triple_parts(cc1)
    assert C1 == SRCHPRE, (C1, SRCHPRE)
    assert D1 == CLN(LMS['Y2'], S, INIT7), D1
    # 2. scalesF from INIT7
    w0g = encw(w, ph, 'N', nn)
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    w7g = wgcat(w, ph, W0, '<" 4 ">', w0g, s4)
    S7 = init_stacks(w, ph, mk, ne, '7', W7, w7g)
    B = IBase(w, ph, c, mk, ne, ex, S7)
    wrd0 = closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    B.g('(/)', wrd0)
    E7 = EWg('N', '(/)')
    e7 = s([S7.vals['7'][1], s([s([s4, w.inst('ccatrid')], 'syl', '( %s -> ( <" 4 "> ++ (/) ) = <" 4 "> )' % ph)], 'oveq2d',
                                '( %s -> %s = %s )' % (ph, E7, W7))], 'eqtr4d', '( %s -> ( %s ` 7 ) = %s )' % (ph, INIT7, E7))
    # the scales' typing
    cl = Closure(w, ph, {'C': ('NN0', cn), 'K': ('NN', knn), 'N': ('NN0', nn)})
    TUP = SCTUP_('C', 'K', 'N')
    tv = s([s([cn, knn, nn], '3jca', '( %s -> ( C e. NN0 /\\ K e. NN /\\ N e. NN0 )' % ph + ' )'), w.inst('sctmval')], 'syl',
           '( %s -> %s = %s )' % (ph, SC_, TUP))
    pjn = {}
    for pj in (PZ, PZ99, PY, PT, PTH):
        st_, val = proj_eq(w, ph, pj(SC_), tv, TUP)
        pjn[pj(SC_)] = (val, st_)
    # N e. NN0 for each projection through its value (the values are NN0 terms of the closure)
    kn = s([knn], 'nnnn0d', '( %s -> K e. NN0 )' % ph)
    cl2 = Closure(w, ph, {'C': ('NN0', cn), 'K': ('NN0', kn), 'N': ('NN0', nn)})
    def nn0_of(val):
        return cl2.mem(val, 'NN0')
    def proj_nn0(pj):
        val, st_ = pjn[pj(SC_)]
        return s([st_, nn0_of(val)], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, pj(SC_)))
    # register leaves bottom-up: the logs
    M_ = '( 2 Nlog N )'
    A_ = '( 2 Nlog %s )' % M_
    Bb_ = '( 2 Nlog %s )' % A_
    def nlogleaf(x, xn):
        st_ = s([closed(w, ph, '2nn0', '2 e. NN0'), xn, w.inst('nlogcl')], 'syl2anc', '( %s -> ( 2 Nlog %s ) e. NN0 )' % (ph, x))
        cl2.leaf('( 2 Nlog %s )' % x, 'NN0', st_)
        return st_
    mn = nlogleaf('N', nn)
    an = nlogleaf(M_, mn)
    bbn = nlogleaf(A_, an)
    Z_ = '( ( C x. %s ) x. %s )' % (A_, Bb_)
    zn = cl2.mem(Z_, 'NN0')
    nzn = nlogleaf(Z_, zn)
    BZ_ = '( ( 2 Nlog %s ) + 1 )' % Z_
    bzn = cl2.mem(BZ_, 'NN0')
    # z99 = 2 ^ floor( ( 99 bz + 99 ) / 100 )
    NUM99 = '( ( ; 9 9 x. %s ) + ; 9 9 )' % BZ_
    EXP99 = '( |_ ` ( %s / ; ; 1 0 0 ) )' % NUM99
    n100 = s([num.nn(w, 100)], 'a1i', '( %s -> ; ; 1 0 0 e. NN )' % ph)
    cl2.leaf(EXP99, 'NN0', s([cl2.mem(NUM99, 'NN0'), n100, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXP99)))
    cl2.leaf('( 2 ^ %s )' % EXP99, 'NN0', s([closed(w, ph, '2nn0', '2 e. NN0'), cl2.mem(EXP99, 'NN0'), w.inst('nn0expcl')], 'syl2anc',
                                            '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, EXP99)))
    # y = 2 ^ floor( ( ( K - 1 ) bz + K - 1 ) / K )
    K1 = '( K - 1 )'
    cl2.leaf(K1, 'NN0', s([knn, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, K1)))
    KBZ = '( %s x. %s )' % (K1, BZ_)
    NUMY = '( ( %s + K ) - 1 )' % KBZ
    kbzk = s([cl2.mem(KBZ, 'NN0'), knn, w.inst('nn0nnaddcl')], 'syl2anc', '( %s -> ( %s + K ) e. NN )' % (ph, KBZ))
    cl2.leaf(NUMY, 'NN0', s([kbzk, w.inst('nnm1nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, NUMY)))
    EXPY = '( |_ ` ( %s / K ) )' % NUMY
    cl2.leaf(EXPY, 'NN0', s([cl2.mem(NUMY, 'NN0'), knn, w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXPY)))
    cl2.leaf('( 2 ^ %s )' % EXPY, 'NN0', s([closed(w, ph, '2nn0', '2 e. NN0'), cl2.mem(EXPY, 'NN0'), w.inst('nn0expcl')], 'syl2anc',
                                           '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, EXPY)))
    # theta = 2 ^ floor( ( 6 ( log ( log n + 1 ) + 1 ) + 4 ) / 5 )
    M1 = '( %s + 1 )' % M_
    nm1n = nlogleaf(M1, cl2.mem(M1, 'NN0'))
    LTH = '( ( 2 Nlog %s ) + 1 )' % M1
    NUMTH = '( ( 6 x. %s ) + 4 )' % LTH
    EXPTH = '( |_ ` ( %s / 5 ) )' % NUMTH
    cl2.leaf(EXPTH, 'NN0', s([cl2.mem(NUMTH, 'NN0'), closed(w, ph, '5nn', '5 e. NN'), w.inst('fldivnn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, EXPTH)))
    cl2.leaf('( 2 ^ %s )' % EXPTH, 'NN0', s([closed(w, ph, '2nn0', '2 e. NN0'), cl2.mem(EXPTH, 'NN0'), w.inst('nn0expcl')], 'syl2anc',
                                            '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, EXPTH)))
    pn = {pj: proj_nn0(pj) for pj in (PZ, PZ99, PY, PT, PTH)}
    gS = B.g(SCALES, ewg_(w, ph, PZ(SC_), pn[PZ], EWg(PZ99(SC_), EWg(PY(SC_), EWg(PT(SC_), EWg(PTH(SC_), '(/)')))),
                          ewg_(w, ph, PZ99(SC_), pn[PZ99], EWg(PY(SC_), EWg(PT(SC_), EWg(PTH(SC_), '(/)'))),
                               ewg_(w, ph, PY(SC_), pn[PY], EWg(PT(SC_), EWg(PTH(SC_), '(/)')),
                                    ewg_(w, ph, PT(SC_), pn[PT], EWg(PTH(SC_), '(/)'), ewg_(w, ph, PTH(SC_), pn[PTH], '(/)', wrd0))))))
    R = B.run()
    B.call(R, 'tmiscal', {'C': 'C', 'K': 'K', 'N': 'N', 'B': 'B', 'X': '(/)', 'P': PL('P', 5), 'E': LMS['Y3']},
           {'( %s ` 7 ) = %s' % (INIT7, E7): e7, WG('(/)'): wrd0}, [('0', SCALES, gS)])
    cur, out = R.normalize(N8)
    assert out == [('0', SCALES)], out
    assert R.C0 == D1, (R.C0, D1)
    t = hrseq(w, ph, mk['phm'], t1, R.tri, C1, D1, R.cur, n1, R.n)
    assert TRI(C1, R.cur, '( %s + %s )' % (n1, R.n)) == CONCL_SRPA, '\n%s\n%s' % (TRI(C1, R.cur, '( %s + %s )' % (n1, R.n)), CONCL_SRPA)
    finish(w, t, lab)
    return w.run()




# ============================================================ the assembly (blueprint D7)
# letters (A1b's ~ searchval ): the scales Z G Y U O (z z99 y T theta), the tuple V' , the reservoir R , its length I ,
# Q = the T largest entries, L = prodL Q , X = L ^ 5 , C' = the step-2 charge, J = the scan, J' = k' , W = the pool,
# X' = the extraction, F = m' , A = U' (the witness list), Q' = verify m' U' ; the units U' = B X0 , W' = E0 U' ;
# b1 = B' , bM = N' ; the cost so far Z' ; the words on 5 and 6 after the extraction Y' , X"
import t6blib as _T6

VT = "V'"
TUP_ = '<. <. <. Z , G >. , <. Y , U >. >. , O >.'
SE = '( %s Search N )' % VT
UU, WW = "U'", "W'"
TOT = '( ( ( 2nd ` %s ) + 1 ) x. ( ; ; 3 0 0 x. %s ) )' % (SE, WW)
GETD = 'if ( ( 1st ` %s ) = ( inr ` (/) ) , <. 0 , (/) >. , ( 2nd ` ( 1st ` %s ) ) )' % (SE, SE)
OUTS = '( ( 1st ` %s ) encodeOutput ( 2nd ` %s ) )' % (GETD, GETD)
POST = CLN('E', S, INIT('1', OUTS))
INR = '( inr ` (/) )'
LEQ = [('R', '( ( Z Reservoir G ) ` Y )'), ('I', '( # ` ( 1st ` R ) )'), ('Q', '( ( 1st ` R ) substr <. ( I - U ) , I >. )'),
       ('L', '( 1st ` ( ProdL ` Q ) )'), ('X', '( L ^ 5 )'), ("C'", '( ( ( ( 2nd ` R ) + U ) + ( 2nd ` ( ProdL ` Q ) ) ) + 2 )'),
       ('J', '( ( ( ( ( Q Scan X ) ` Z ) ` O ) ` 1 ) ` X )'), ("J'", '( 1st ` ( 2nd ` ( 1st ` J ) ) )'), ('W', '( 2nd ` ( 2nd ` ( 1st ` J ) ) )'),
       ("X'", '( ( L Extract N ) ` W )'), ('F', "( 1st ` ( 2nd ` ( 1st ` X' ) ) )"), ('A', "( 2nd ` ( 2nd ` ( 1st ` X' ) ) )"),
       ("Q'", '( F Verify A )')]
LEQD = dict(LEQ)
EQ = lambda l: '%s = %s' % (l, LEQD[l])
VTEQ = '%s = %s' % (VT, TUP_)
SC_TY = (('Z e. NN', 'G e. NN0', 'Y e. NN'), ('U e. NN0', 'O e. NN0', 'N e. NN0'))
LEQT = (((EQ('R'), EQ('I'), EQ('Q')), (EQ('L'), EQ('X'), EQ("C'"))), ((EQ('J'), EQ("J'"), EQ('W')), (EQ("X'"), EQ('F'), EQ('A'))),
        (EQ("Q'"), VTEQ))
S2 = '( 2nd ` J )'
E2 = "( 2nd ` X' )"
W2 = "( 2nd ` Q' )"
CST4 = "( ( ( C' + %s ) + %s ) + %s )" % (S2, E2, W2)
IFQ = "if ( ( 1st ` Q' ) = 1o , ( inl ` <. F , A >. ) , %s )" % INR
PRE2 = "( ( ( ; 5 1 x. U' ) + ( ( C' + 1 ) x. U' ) ) + 1 )"
PRE3 = "( %s + ( ( ( %s + 1 ) x. U' ) + 1 ) )" % (PRE2, S2)
PRE4 = "( %s + ( ( ( %s + 1 ) x. ( ; 2 5 x. W' ) ) + 1 ) )" % (PRE3, E2)
VX4 = VX_.replace('( # ` W )', '( # ` A )').replace(' B )', " B' )").replace('( 3 x. B )', "( 3 x. B' )").replace(' N )', " N' )")
assert VX4 == "( ( ( ( ( 2 x. ( ( # ` A ) + 1 ) ) x. B' ) + ( 3 x. B' ) ) + N' ) + 8 )", VX4
HB5 = '( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ U\'' % VX4
CASE4 = ('U <_ I', "( 1st ` J ) =/= %s" % INR, "( 1st ` X' ) =/= %s" % INR)
VF1 = ('A e. Word NN0', 'F e. NN0', ("B' e. NN0", "N' e. NN0"))
VF2 = (RALB('A', "B'"), LT2('( # ` A )', "B'"), LT2('F', "N'"))
VF3 = ("B' <_ N'", '1 <_ F', 'A. a e. ran A 1 <_ a')
UN1 = (("U' e. NN0", "W' e. NN0"), ("U' <_ W'", "8 <_ U'"))
UN2 = ("( B' + 2 ) <_ U'", "( N' + 2 ) <_ U'", ("B <_ B'", "H <_ B'"))
UN3 = ((LT2('X', "B'"), LT2('L', "B'"), LT2("J'", "B'")), (LT2('Z'), LT2('O', 'H'), LT2('N', 'H')))
UN4 = (("( # ` Y' ) <_ W'", '( # ` X" ) <_ W\''), ("( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )", "( # ` ( encList ` A ) ) <_ W'"))
UN5 = ((HB5, "( TMB ` B' ) <_ U'"), ("( TMB ` N' ) <_ U'", "( ( ( # ` A ) + 2 ) x. U' ) <_ W'"))
WD4 = (WG("Y'"), WG('X"'))
D0V = EWg('X', EWg('O', '(/)'))
D1V = EWg('Z', '(/)')
D2V = EWg("J'", '(/)')
D3V = EWg('L', '(/)')
D4V = ENCL('A', ENCL('Q', '(/)'))
D7V = EWg('F', EWg('N', '(/)'))
STK4 = (STKD('D'), ((DEQ(0, D0V), DEQ(1, D1V)), (DEQ(2, D2V), DEQ(3, D3V))), ((DEQ(4, D4V), DEQ(5, "Y'")), (DEQ(6, 'X"'), DEQ(7, D7V))))
CSTH4 = ("Z' e. NN0", "Z' <_ %s" % PRE4)
TREE_SRC4 = ((T_PHM7, FS.pred()),
             ((SC_TY, LEQT), (((CASE4, VF1), (VF2, VF3)), (UN1, UN2, UN3), (UN4, UN5, WD4)), (('B e. NN0', 'H e. NN0', '1 <_ L'), STK4, CSTH4)))
Z1, Z2, Z3, Z4 = LMS['Z1'], LMS['Z2'], LMS['Z3'], LMS['Z4']
Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11 = [LMS['Y%d' % i] for i in range(4, 12)]
CONCL_SRC4 = TRI(CLN(Z3, NFL('1o'), 'D'), POST, "( %s - Z' )" % TOT)
add12('tmisrc4', TREE_SRC4, CONCL_SRC4)

# ------------------------------------------------------------ t12bud: Lean's bud_D over bare naturals
BUDL = ('( ( ( ( ( ( ( ; 5 1 x. U ) + ( ( C + 1 ) x. U ) ) + 1 ) + ( ( ( S + 1 ) x. U ) + 1 ) ) + ( ( ( E + 1 ) x. ( ; 2 5 x. V ) ) + 1 ) ) '
        '+ ( ( ( W + 1 ) x. U ) + 1 ) ) + ( ( ( C + 1 ) x. U ) + ( ; 5 0 x. V ) ) )')
BUDR = '( ( ( ( ( C + S ) + E ) + W ) + 1 ) x. ( ; ; 3 0 0 x. V ) )'
ST_BUD = ('( ( ( ( U e. NN0 /\\ V e. NN0 ) /\\ ( U <_ V /\\ 8 <_ U ) ) /\\ ( ( C e. NN0 /\\ S e. NN0 ) /\\ ( E e. NN0 /\\ W e. NN0 ) ) ) -> %s <_ %s )'
          % (BUDL, BUDR))


def mul_le(w, ph, cl, A, B_, C_, D_, ab, cd):
    """( ph -> ( A x. C ) <_ ( B x. D ) ) from ab : A <_ B , cd : C <_ D (~ lemul12a ; 0 <_ A , 0 <_ C from cl)"""
    s = w.s
    j1 = s([s([s([cl.mem(A, 'RR'), cl.ge0(A)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, A, A)), cl.mem(B_, 'RR')], 'jca',
             '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR ) )' % (ph, A, A, B_)),
            s([s([cl.mem(C_, 'RR'), cl.ge0(C_)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, C_, C_)), cl.mem(D_, 'RR')], 'jca',
              '( %s -> ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR ) )' % (ph, C_, C_, D_))], 'jca',
           '( %s -> ( ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR ) /\\ ( ( %s e. RR /\\ 0 <_ %s ) /\\ %s e. RR ) ) )' % (ph, A, A, B_, C_, C_, D_))
    return s([j1, s([ab, cd], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ph, A, B_, C_, D_)), w.inst('lemul12a')], 'sylc',
             '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, A, C_, B_, D_))


def mul_le2(w, ph, cl, A, B_, C_, bc):
    """( ph -> ( A x. B ) <_ ( A x. C ) ) from bc : B <_ C and 0 <_ A (~ lemul2a )"""
    s = w.s
    j = s([s([cl.mem(B_, 'RR'), cl.mem(C_, 'RR'), s([cl.mem(A, 'RR'), cl.ge0(A)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, A, A))], '3jca',
             '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (ph, B_, C_, A, A)), bc], 'jca',
          '( %s -> ( ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ %s <_ %s ) )' % (ph, B_, C_, A, A, B_, C_))
    return s([j, w.inst('lemul2a')], 'syl', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, A, B_, A, C_))


def t12bud():
    lab = 't12bud'
    T = ((('U e. NN0', 'V e. NN0'), ('U <_ V', '8 <_ U')), (('C e. NN0', 'S e. NN0'), ('E e. NN0', 'W e. NN0')))
    ph = cj(T)
    w = W(lab, 'The budget of Lean\'s ` searchF_le_B ` over bare naturals ( ` bud_D ` , which contains ` bud_A ` to ` bud_C ` '
               'at zero charges): the unit ` U ` , the extraction unit ` V ` , the charges ` c s e w ` of the four stages; '
               'every stage\'s leaf costs at most ` ( c + 1 ) U + 50 V ` (~ lemul12a ).')
    s = w.s
    c = Ctx(w, ph, T)
    cl = Closure(w, ph, {x: ('NN0', c['%s e. NN0' % x]) for x in ('U', 'V', 'C', 'S', 'E', 'W')})
    uv, u8 = c['U <_ V'], c['8 <_ U']
    T1 = '( ( ( ( C + S ) + E ) + W ) + 1 )'
    hy = [uv, u8]
    for x in ('C', 'S', 'W'):
        le = linarith(w, ph, [cl.ge0(y) for y in ('C', 'S', 'E', 'W')], '( %s + 1 ) <_ %s' % (x, T1), closure=cl)
        hy.append(mul_le(w, ph, cl, '( %s + 1 )' % x, T1, 'U', 'V', le, uv))
    le = linarith(w, ph, [cl.ge0(y) for y in ('C', 'S', 'E', 'W')], '( E + 1 ) <_ %s' % T1, closure=cl)
    hy.append(mul_le(w, ph, cl, '( E + 1 )', T1, '( ; 2 5 x. V )', '( ; 2 5 x. V )', le, s([cl.mem('( ; 2 5 x. V )', 'RR')], 'leidd', '( %s -> ( ; 2 5 x. V ) <_ ( ; 2 5 x. V ) )' % ph)))
    hy.append(mul_le(w, ph, cl, '1', T1, 'V', 'V', linarith(w, ph, [cl.ge0(y) for y in ('C', 'S', 'E', 'W')], '1 <_ %s' % T1, closure=cl),
                     s([cl.mem('V', 'RR')], 'leidd', '( %s -> V <_ V )' % ph)))
    hy += [cl.ge0('( %s x. V )' % x) for x in ('C', 'S', 'E', 'W')]
    hy += [cl.ge0('( %s x. U )' % x) for x in ('C', 'S', 'W')]
    w.qed(hy, None, None) if False else None
    le = linarith(w, ph, hy, '%s <_ %s' % (BUDL, BUDR), closure=cl, products=True)
    w.qed([le], 'id', ST_BUD) if False else None
    w.qed([le, w.inst('biid')], 'mpbi', ST_BUD)
    return w.run()


# ------------------------------------------------------------ word lengths: equations and atomic bounds for linarith
def lenfacts(w, ph, cl, txt, atoms, out=None):
    """( # ` txt ) expanded through ` ++ ` , ` <" 4 "> ` and ` (/) ` : equation steps into out, the atomic parts
    ` ( # ` ( encNatGam ` t ) ) ` , ` ( # ` ( encList ` V ) ) ` , ` ( # ` LETTER ) ` registered as NN0 leaves of cl
    (their bounds come from atoms[part] = step, appended to out)"""
    s = w.s
    out = [] if out is None else out
    L_ = '( # ` %s )' % txt
    if txt == '(/)':
        out.append(s([s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % ph))
        cl.leaf(L_, 'NN0', s([s([s([], 'hash0', '( # ` (/) ) = 0'), s([], '0nn0', '0 e. NN0')], 'eqeltri', '( # ` (/) ) e. NN0')], 'a1i', '( %s -> ( # ` (/) ) e. NN0 )' % ph))
        return out
    if txt == '<" 4 ">':
        out.append(s([s([], 's1len', '( # ` <" 4 "> ) = 1')], 'a1i', '( %s -> ( # ` <" 4 "> ) = 1 )' % ph))
        cl.leaf(L_, 'NN0', s([s([s([], 's1len', '( # ` <" 4 "> ) = 1'), s([], '1nn0', '1 e. NN0')], 'eqeltri', '( # ` <" 4 "> ) e. NN0')], 'a1i', '( %s -> ( # ` <" 4 "> ) e. NN0 )' % ph))
        return out
    if txt in atoms:
        g, st = atoms[txt]
        cl.leaf(L_, 'NN0', s([g, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, L_)))
        if st is not None:
            out.append(st)
        return out
    # a concatenation ( A ++ B ) at the top level
    toks = txt.split()
    assert toks[0] == '(' and toks[-1] == ')', txt
    d = 0
    for i, t in enumerate(toks[1:-1], 1):
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        elif d == 0 and t == '++':
            A_, B_ = ' '.join(toks[1:i]), ' '.join(toks[i + 1:-1])
            break
    else:
        raise AssertionError('no ++ in ' + txt)
    ga, gb = atoms.get(A_, (None, None))[0], atoms.get(B_, (None, None))[0]
    lenfacts(w, ph, cl, A_, atoms, out)
    lenfacts(w, ph, cl, B_, atoms, out)
    ga = ga or _gam(w, ph, A_, atoms)
    gb = gb or _gam(w, ph, B_, atoms)
    out.append(s([ga, gb, w.inst('ccatlen')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + ( # ` %s ) ) )' % (ph, txt, A_, B_)))
    cl.leaf(L_, 'NN0', s([wgcat(w, ph, A_, B_, ga, gb), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, L_)))
    return out


def _gam(w, ph, txt, atoms):
    """( ph -> txt e. Word Gamma' ) for the word forms of lenfacts"""
    s = w.s
    if txt in atoms:
        return atoms[txt][0]
    if txt == '(/)':
        return closed(w, ph, 'wrd0', "(/) e. Word Gamma'")
    if txt == '<" 4 ">':
        return s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    toks = txt.split()
    d = 0
    for i, t in enumerate(toks[1:-1], 1):
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        elif d == 0 and t == '++':
            A_, B_ = ' '.join(toks[1:i]), ' '.join(toks[i + 1:-1])
            return wgcat(w, ph, A_, B_, _gam(w, ph, A_, atoms), _gam(w, ph, B_, atoms))
    raise AssertionError(txt)


def numatom(w, ph, cl, t, tn, b, bn, tlt):
    """the atom entry of ( encNatGam ` t ) : (typing, ( # ` ( encNatGam ` t ) ) <_ b)"""
    return (encw(w, ph, t, tn), w.s([tn, bn, tlt, w.inst('tm2lentlt')], 'syl3anc', '( %s -> ( # ` ( encNatGam ` %s ) ) <_ %s )' % (ph, t, b)))


def init_eq(w, ph, k0, W1, W2, eq):
    """( ph -> INIT( k0 , W1 ) = INIT( k0 , W2 ) ) from eq : ( ph -> W1 = W2 )"""
    s = w.s
    i = s([eq], 'ifeq1d', '( %s -> if ( k = %s , %s , (/) ) = if ( k = %s , %s , (/) ) )' % (ph, k0, W1, k0, W2))
    return s([i], 'mpteq2dv', '( %s -> %s = %s )' % (ph, INIT(k0, W1), INIT(k0, W2)))


def search_value(w, ph, c, cl):
    """( ph -> SE = if ( I < U , <. inr , ( ( 2nd R ) + 1 ) >. , if ( ( 1st J ) = inr , <. inr , ( C' + s ) >. ,
    if ( ( 1st X' ) = inr , <. inr , ( ( C' + s ) + e ) >. , <. IFQ , CST4 >. ) ) ) ) by ~ searchval at the letters"""
    s = w.s
    zn, gn, yn, un, on, nn = [c[t] for t in ('Z e. NN', 'G e. NN0', 'Y e. NN', 'U e. NN0', 'O e. NN0', 'N e. NN0')]
    PQ = '( ProdL ` Q )'
    # the letters' equations in searchval's form
    ej = c[EQ('J')]
    rj, jx = w.rewrite(LEQD['J'], {'X': ('( L ^ 5 )', c[EQ('X')])}, ph)
    ej2 = s([ej, rj], 'eqtrd', '( %s -> J = %s )' % (ph, jx))
    eq_ = c[EQ("Q'")]
    rq, qx = w.rewrite(LEQD["Q'"], {'F': (LEQD['F'], c[EQ('F')]), 'A': (LEQD['A'], c[EQ('A')])}, ph)
    eq2 = s([eq_, rq], 'eqtrd', "( %s -> Q' = %s )" % (ph, qx))
    m = {'W': 'G', 'T': 'U', 'H': 'O', 'G': PQ, 'A': 'L', 'C': "C'", 'P': 'W', 'X': "X'", 'U': "Q'"}
    ex = {'Z e. NN': zn, 'G e. NN0': gn, 'Y e. NN': yn, 'U e. NN0': un, 'O e. NN0': on, 'N e. NN0': nn,
          EQ('R'): c[EQ('R')], EQ('I'): c[EQ('I')], EQ('Q'): c[EQ('Q')], '%s = %s' % (PQ, PQ): s([s([], 'eqid', '%s = %s' % (PQ, PQ))], 'a1i', '( %s -> %s = %s )' % (ph, PQ, PQ)),
          EQ('L'): c[EQ('L')], EQ("C'"): c[EQ("C'")], 'J = %s' % jx: ej2, EQ('W'): c[EQ('W')], EQ("X'"): c[EQ("X'")], "Q' = %s" % qx: eq2}
    st, cc = inst(w, ph, 'searchval', m, Bld(w, ph, c, ex))
    lhs, rhs = cc.split(' = ', 1)
    # the tuple is V'
    e1 = s([s([c[VTEQ]], 'oveq1d', '( %s -> %s = %s )' % (ph, SE, lhs)), st], 'eqtrd', '( %s -> %s = %s )' % (ph, SE, rhs))
    # F and A back into the innermost pair
    r2, rhs2 = w.rewrite(rhs, {LEQD['F']: ('F', s([c[EQ('F')]], 'eqcomd', '( %s -> %s = F )' % (ph, LEQD['F']))),
                              LEQD['A']: ('A', s([c[EQ('A')]], 'eqcomd', '( %s -> %s = A )' % (ph, LEQD['A'])))}, ph)
    return s([e1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, SE, rhs2)), rhs2


def reduce_if(w, ph, st, rhs, conds):
    """strip the leading ` if ( cond , _ , rest ) ` layers of the search value by iffalsed steps conds[i] : ( ph -> -. cond_i )"""
    s = w.s
    cur = rhs
    for nc in conds:
        assert cur.startswith('if ( '), cur
        node = parse_class(cur) if False else None
        # split the if
        toks = cur.split()
        d = 0; cuts = []
        for i, t in enumerate(toks[1:-1], 1):
            if t in ('(', '<.', '{', '<"'):
                d += 1
            elif t in (')', '>.', '}', '">'):
                d -= 1
            elif d == 1 and t == ',':
                cuts.append(i)
        cond = ' '.join(toks[2:cuts[0]]); rest = ' '.join(toks[cuts[1] + 1:-1])
        f = s([nc], 'iffalsed', '( %s -> %s = %s )' % (ph, cur, rest))
        st = s([st, f], 'eqtrd', '( %s -> %s = %s )' % (ph, SE, rest))
        cur = rest
    return st, cur


def not_lt(w, ph, cl, a, b, le):
    """( ph -> -. b < a ) from le : ( ph -> a <_ b )"""
    return w.s([cl.mem(a, 'RR'), cl.mem(b, 'RR'), le, w.inst('lensymd' if False else 'lenltd')], 'syl3anc', '( %s -> -. %s < %s )' % (ph, b, a)) if False else \
        w.s([le, w.s([cl.mem(b, 'RR'), cl.mem(a, 'RR'), w.inst('lenlt')], 'syl2anc', '( %s -> ( %s <_ %s <-> -. %s < %s ) )' % (ph, a, b, b, a))], 'mpbid',
            '( %s -> -. %s < %s )' % (ph, b, a))


def out_init(w, ph, st_se_pair, ifq_eq, cst_txt, out_txt, out_eq_txt, is_some, F_=None, A_=None):
    """( ph -> INIT( 1 , out_txt ) = INIT( 1 , OUTS ) ) : st_se_pair : ( ph -> SE = <. IFQ' , cst >. ) with IFQ' the first
    component text ifq_eq[0] and ifq_eq[1] : ( ph -> IFQ' = ( inl <. F , A >. ) ) (some) or ( ph -> IFQ' = inr ) (none)"""
    s = w.s
    first_txt, feq = ifq_eq
    p1 = s([st_se_pair], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ph, SE, first_txt, cst_txt))
    o1 = s([s([s([], 'ifex' if first_txt.startswith('if (') else 'fvex', '%s e. _V' % first_txt)], 'a1i', '( %s -> %s e. _V )' % (ph, first_txt)),
            s([s([], 'ovex', '%s e. _V' % cst_txt)], 'a1i', '( %s -> %s e. _V )' % (ph, cst_txt)), w.inst('op1st')], 'syl2anc',
           '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, first_txt, cst_txt, first_txt))
    f1 = s([p1, o1, feq], '3eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ph, SE, 'INL' if False else (('( inl ` <. %s , %s >. )' % (F_, A_)) if is_some else INR)))
    if is_some:
        INL = '( inl ` <. %s , %s >. )' % (F_, A_)
        opv = s([], 'opex', '<. %s , %s >. e. _V' % (F_, A_))
        ne = s([s([opv], 'tmcinlne', '-. %s = %s' % (INL, INR))], 'a1i', '( %s -> -. %s = %s )' % (ph, INL, INR))
        ne2 = s([ne, s([f1], 'eqeq1d', '( %s -> ( ( 1st ` %s ) = %s <-> %s = %s ) )' % (ph, SE, INR, INL, INR))], 'mtbird', '( %s -> -. ( 1st ` %s ) = %s )' % (ph, SE, INR))
        g = s([ne2], 'iffalsed', '( %s -> %s = ( 2nd ` ( 1st ` %s ) ) )' % (ph, GETD, SE))
        i2 = s([s([opv], 'alginl2', '( 2nd ` %s ) = <. %s , %s >.' % (INL, F_, A_))], 'a1i', '( %s -> ( 2nd ` %s ) = <. %s , %s >. )' % (ph, INL, F_, A_))
        g2 = s([g, s([f1], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` %s ) )' % (ph, SE, INL)), i2], '3eqtrd', '( %s -> %s = <. %s , %s >. )' % (ph, GETD, F_, A_))
        fx = s([], 'fvex', '%s e. _V' % F_) if F_.startswith('(') else None
        pa = s([s([g2], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ph, GETD, F_, A_)),
                s([s([], 'fvex', '%s e. _V' % F_), s([], 'fvex', '%s e. _V' % A_)], 'op1st', '( 1st ` <. %s , %s >. ) = %s' % (F_, A_, F_))], 'eqtrdi' if False else 'eqtrid' if False else 'eqtrd_i' if False else 'eqtr_dummy', '') if False else None
        a1 = s([s([s([], 'fvex', '%s e. _V' % F_), s([], 'fvex', '%s e. _V' % A_)], 'op1st', '( 1st ` <. %s , %s >. ) = %s' % (F_, A_, F_))], 'a1i',
               '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ph, F_, A_, F_))
        a2 = s([s([s([], 'fvex', '%s e. _V' % F_), s([], 'fvex', '%s e. _V' % A_)], 'op2nd', '( 2nd ` <. %s , %s >. ) = %s' % (F_, A_, A_))], 'a1i',
               '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (ph, F_, A_, A_))
        p1_ = s([s([g2], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ph, GETD, F_, A_)), a1], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ph, GETD, F_))
        p2_ = s([s([g2], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (ph, GETD, F_, A_)), a2], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (ph, GETD, A_))
        oe = s([p1_, p2_], 'oveq12d', '( %s -> %s = ( %s encodeOutput %s ) )' % (ph, OUTS, F_, A_))
        assert out_txt == '( %s encodeOutput %s )' % (F_, A_), out_txt
        return init_eq(w, ph, '1', out_txt, OUTS, s([oe], 'eqcomd', '( %s -> %s = %s )' % (ph, out_txt, OUTS)))
    # none: GETD = <. 0 , (/) >. , OUTS = ( 0 encodeOutput (/) ) = <" 4 ">
    g = s([f1], 'iftrued', '( %s -> %s = <. 0 , (/) >. )' % (ph, GETD))
    a1 = s([s([s([], 'c0ex', '0 e. _V'), s([], '0ex', '(/) e. _V')], 'op1st', '( 1st ` <. 0 , (/) >. ) = 0')], 'a1i', '( %s -> ( 1st ` <. 0 , (/) >. ) = 0 )' % ph)
    a2 = s([s([s([], 'c0ex', '0 e. _V'), s([], '0ex', '(/) e. _V')], 'op2nd', '( 2nd ` <. 0 , (/) >. ) = (/)')], 'a1i', '( %s -> ( 2nd ` <. 0 , (/) >. ) = (/) )' % ph)
    p1_ = s([s([g], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. 0 , (/) >. ) )' % (ph, GETD)), a1], 'eqtrd', '( %s -> ( 1st ` %s ) = 0 )' % (ph, GETD))
    p2_ = s([s([g], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. 0 , (/) >. ) )' % (ph, GETD)), a2], 'eqtrd', '( %s -> ( 2nd ` %s ) = (/) )' % (ph, GETD))
    oe = s([p1_, p2_], 'oveq12d', '( %s -> %s = ( 0 encodeOutput (/) ) )' % (ph, OUTS))
    from t12_j_acc import encgam0
    en = s([closed(w, ph, '0nn0', '0 e. NN0'), w.inst('encoutnil')], 'syl', '( %s -> ( 0 encodeOutput (/) ) = ( ( encNatGam ` 0 ) ++ <" 4 "> ) )' % ph)
    e0 = s([encgam0(w, ph)], 'oveq1d', '( %s -> ( ( encNatGam ` 0 ) ++ <" 4 "> ) = ( (/) ++ <" 4 "> ) )' % ph)
    s4 = s([closed(w, ph, 'gamma4', "4 e. Gamma'")], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    e1 = s([s4, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ <" 4 "> ) = <" 4 "> )' % ph)
    full = s([oe, en, e0, e1], '4eqtrd' if False else '3eqtrd', '') if False else None
    q1 = s([oe, en], 'eqtrd', '( %s -> %s = ( ( encNatGam ` 0 ) ++ <" 4 "> ) )' % (ph, OUTS))
    q2 = s([q1, e0, e1], '3eqtrd', '( %s -> %s = <" 4 "> )' % (ph, OUTS))
    return init_eq(w, ph, '1', COMMA1, OUTS, s([q2], 'eqcomd', '( %s -> <" 4 "> = %s )' % (ph, OUTS)))


# ------------------------------------------------------------ tmisrc4: the verify stage
class Src(Base):
    """the Base of a stage lemma: the eight stack values, the letters' typing, the closure"""
    def __init__(self, w, ph, T, vals8):
        c0 = Ctx(w, ph, T)
        s = w.s
        self.c0 = c0
        eqs = {}
        gam = {}
        for k, (txt, gst) in vals8.items():
            eqs[k] = (txt, gst)
        Base.__init__(self, w, ph, T, N8, 'srch', eqs)


def stage_typing(w, ph, c, cl):
    """the NN0 typings of the letters' values (R I Q L X C' J J' W X' F A Q' and their costs) as closure leaves;
    returns a dict of the steps"""
    s = w.s
    zn, gn, yn, un, on, nn = [c[t] for t in ('Z e. NN', 'G e. NN0', 'Y e. NN', 'U e. NN0', 'O e. NN0', 'N e. NN0')]
    out = {}
    rcl = s([s([zn, gn], 'jca', '( %s -> ( Z e. NN /\\ G e. NN0 ) )' % ph), yn, w.inst('reservoircl')], 'syl2anc',
            '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (ph, LEQD['R']))
    rcl2 = s([c[EQ('R')], rcl], 'eqeltrd', '( %s -> R e. ( Word NN0 X. NN0 ) )' % ph)
    out['R1'] = s([rcl2, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` R ) e. Word NN0 )' % ph)
    out['R2'] = s([rcl2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` R ) e. NN0 )' % ph)
    cl.leaf('( 2nd ` R )', 'NN0', out['R2'])
    out['I'] = s([c[EQ('I')], s([out['R1'], w.inst('lencl')], 'syl', '( %s -> ( # ` ( 1st ` R ) ) e. NN0 )' % ph)], 'eqeltrd', '( %s -> I e. NN0 )' % ph)
    cl.leaf('I', 'NN0', out['I'])
    out['Q'] = s([c[EQ('Q')], s([out['R1'], w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, LEQD['Q']))], 'eqeltrd', '( %s -> Q e. Word NN0 )' % ph)
    pcl = s([out['Q'], w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` Q ) e. ( NN0 X. NN0 ) )' % ph)
    out['L'] = s([c[EQ('L')], s([pcl, w.inst('xp1st')], 'syl', '( %s -> ( 1st ` ( ProdL ` Q ) ) e. NN0 )' % ph)], 'eqeltrd', '( %s -> L e. NN0 )' % ph)
    cl.leaf('L', 'NN0', out['L'])
    out['PQ2'] = s([pcl, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( ProdL ` Q ) ) e. NN0 )' % ph)
    cl.leaf('( 2nd ` ( ProdL ` Q ) )', 'NN0', out['PQ2'])
    out['X'] = s([c[EQ('X')], s([out['L'], closed(w, ph, '5nn0', '5 e. NN0'), w.inst('nn0expcld')], 'syl2anc' if False else 'nn0expcld', '') if False else
                 s([out['L'], closed(w, ph, '5nn0', '5 e. NN0')], 'nn0expcld', '( %s -> ( L ^ 5 ) e. NN0 )' % ph)], 'eqeltrd', '( %s -> X e. NN0 )' % ph)
    cl.leaf('X', 'NN0', out['X'])
    out["C'"] = s([c[EQ("C'")], cl.mem(LEQD["C'"], 'NN0')], 'eqeltrd', "( %s -> C' e. NN0 )" % ph)
    cl.leaf("C'", 'NN0', out["C'"])
    j1 = s([s([s([out['Q'], out['X']], 'jca', '( %s -> ( Q e. Word NN0 /\\ X e. NN0 ) )' % ph), zn and s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)], 'jca',
              '( %s -> ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % ph), on], 'jca', '( %s -> ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % ph)
    j2 = s([s([j1, closed(w, ph, '1nn0', '1 e. NN0')], 'jca', '( %s -> ( ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ 1 e. NN0 ) )' % ph), out['X']], 'jca',
           '( %s -> ( ( ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ 1 e. NN0 ) /\\ X e. NN0 ) )' % ph)
    jcl = s([c[EQ('J')], s([j2, w.inst('scancl')], 'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, LEQD['J']))], 'eqeltrd',
            '( %s -> J e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % ph)
    out['J2'] = s([jcl, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` J ) e. NN0 )' % ph)
    cl.leaf(S2, 'NN0', out['J2'])
    out['zn0'] = s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % ph)
    return out


def some_typing(w, ph, c, cl, ty):
    """with ( 1st J ) =/= inr : J' e. NN0 , W e. Word NN0 (~ scandj ); X' typing, e , F , A , Q' , w"""
    s = w.s
    out = {}
    jne = c["( 1st ` J ) =/= %s" % INR]
    j1 = s([s([s([s([ty['Q'], ty['X']], 'jca', '( %s -> ( Q e. Word NN0 /\\ X e. NN0 ) )' % ph), ty['zn0']], 'jca',
                '( %s -> ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % ph), c['O e. NN0']], 'jca',
             '( %s -> ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % ph),
            s([closed(w, ph, '1nn0', '1 e. NN0'), ty['X']], 'jca', '( %s -> ( 1 e. NN0 /\\ X e. NN0 ) )' % ph)], 'jca',
           '( %s -> ( ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( 1 e. NN0 /\\ X e. NN0 ) ) )' % ph)
    jne2 = s([jne, s([c[EQ('J')]], 'neeq1d', '( %s -> ( ( 1st ` J ) =/= %s <-> ( 1st ` %s ) =/= %s ) )' % (ph, INR, LEQD['J'], INR))], 'mpbid',
             '( %s -> ( 1st ` %s ) =/= %s )' % (ph, LEQD['J'], INR))
    dj = s([s([j1, jne2], 'jca', '( %s -> ( %s /\\ ( 1st ` %s ) =/= %s ) )' % (ph, concl(w, ph, j1), LEQD['J'], INR)), w.inst('scandj')], 'syl',
           '( %s -> ( ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) e. NN0 /\\ ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) e. Word NN0 ) )' % (ph, LEQD['J'], LEQD['J']))
    rj = s([c[EQ('J')]], 'fveq2d', '( %s -> ( 1st ` J ) = ( 1st ` %s ) )' % (ph, LEQD['J']))
    k1 = s([rj], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` J ) ) = ( 2nd ` ( 1st ` %s ) ) )' % (ph, LEQD['J']))
    kk = s([k1], 'fveq2d', "( %s -> %s = ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) )" % (ph, LEQD["J'"], LEQD['J']))
    ww = s([k1], 'fveq2d', "( %s -> %s = ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) )" % (ph, LEQD['W'], LEQD['J']))
    out["J'"] = s([s([c[EQ("J'")], kk], 'eqtrd', "( %s -> J' = ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) )" % (ph, LEQD['J'])), s([dj], 'simpld', '( %s -> ( 1st ` ( 2nd ` ( 1st ` %s ) ) ) e. NN0 )' % (ph, LEQD['J']))],
                  'eqeltrd', "( %s -> J' e. NN0 )" % ph)
    cl.leaf("J'", 'NN0', out["J'"])
    out['W'] = s([s([c[EQ('W')], ww], 'eqtrd', '( %s -> W = ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) )' % (ph, LEQD['J'])), s([dj], 'simprd', '( %s -> ( 2nd ` ( 2nd ` ( 1st ` %s ) ) ) e. Word NN0 )' % (ph, LEQD['J']))],
                'eqeltrd', '( %s -> W e. Word NN0 )' % ph)
    # the extraction
    lnn = s([s([ty['L'], c['1 <_ L']], 'jca', '( %s -> ( L e. NN0 /\\ 1 <_ L ) )' % ph), w.inst('elnnnn0c')], 'sylibr', '( %s -> L e. NN )' % ph) if '1 <_ L' in c.all() else None
    out['Lnn'] = lnn
    xcl = s([s([s([lnn, c['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), out['W']], 'jca', '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ W e. Word NN0 ) )' % ph), w.inst('extractcl')],
            'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, LEQD["X'"]))
    xcl2 = s([c[EQ("X'")], xcl], 'eqeltrd', "( %s -> X' e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )" % ph)
    out['E2'] = s([xcl2, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` X' ) e. NN0 )" % ph)
    cl.leaf(E2, 'NN0', out['E2'])
    return out


def verify_typing(w, ph, c, cl):
    """( 2nd ` Q' ) e. NN0 , ( 1st ` Q' ) e. 2o from F e. NN0 , A e. Word NN0"""
    s = w.s
    vcl = s([c['F e. NN0'], c['A e. Word NN0'], w.inst('verifycl')], 'syl2anc', '( %s -> ( F Verify A ) e. ( 2o X. NN0 ) )' % ph)
    vcl2 = s([c[EQ("Q'")], vcl], 'eqeltrd', "( %s -> Q' e. ( 2o X. NN0 ) )" % ph)
    w2 = s([vcl2, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` Q' ) e. NN0 )" % ph)
    cl.leaf(W2, 'NN0', w2)
    q1 = s([vcl2, w.inst('xp1st')], 'syl', "( %s -> ( 1st ` Q' ) e. 2o )" % ph)
    return w2, q1


def tmisrc4():
    lab = 'tmisrc4'
    T0 = numtree(TREE_SRC4)
    ph = cj(T0)
    w = W(lab, 'The verify stage of Lean\'s ` searchF ` at the machine (the extraction succeeded): from the third branch with '
               'the flag true, ` verifyF ` (~ tmiverb ), then ` outputF ` (~ tmiout ) or ` failAll ` (~ tmisrfl ) by the verdict; '
               'the final stacks are ` initStacks 1 ( encodeOutput ( getD ( search sc n ) ) ) ` by A1b\'s ~ searchval , the '
               'cost stays within the total budget less the cost so far ` Z\' ` (~ t12bud ).')
    s = w.s
    c0 = Ctx(w, ph, T0)
    # the common part: the branch and verifyF, under ph
    def base(pc, Tc):
        cc = Ctx(w, pc, Tc)
        cl = Closure(w, pc, {x: ('NN0', cc['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N', 'F', "B'", "N'", "U'", "W'", 'B', 'H', "Z'")})
        for x in ('Z', 'Y'):
            cl.leaf(x, 'NN0', s([cc['%s e. NN' % x]], 'nnnn0d', '( %s -> %s e. NN0 )' % (pc, x)))
        ty = stage_typing(w, pc, cc, cl)
        ty.update(some_typing(w, pc, cc, cl, ty)) if False else None
        # typings of the words on the stacks
        an = cc['A e. Word NN0']
        gq = enclg(w, pc, 'Q', ty['Q'], '(/)', closed(w, pc, 'wrd0', "(/) e. Word Gamma'"))
        g4 = enclg(w, pc, 'A', an, ENCL('Q', '(/)'), gq)
        gn0 = ewg_(w, pc, 'N', cc['N e. NN0'], '(/)', closed(w, pc, 'wrd0', "(/) e. Word Gamma'"))
        g7 = ewg_(w, pc, 'F', cc['F e. NN0'], EWg('N', '(/)'), gn0)
        go = ewg_(w, pc, 'O', cc['O e. NN0'], '(/)', closed(w, pc, 'wrd0', "(/) e. Word Gamma'"))
        g0 = ewg_(w, pc, 'X', ty['X'], EWg('O', '(/)'), go)
        # J' e. NN0 needs the some facts
        st_ = some_typing(w, pc, cc, cl, ty)
        ty.update(st_)
        g2 = ewg_(w, pc, "J'", ty["J'"], '(/)', closed(w, pc, 'wrd0', "(/) e. Word Gamma'"))
        g1 = ewg_(w, pc, 'Z', ty['zn0'], '(/)', closed(w, pc, 'wrd0', "(/) e. Word Gamma'"))
        g3 = ewg_(w, pc, 'L', ty['L'], '(/)', closed(w, pc, 'wrd0', "(/) e. Word Gamma'"))
        vals8 = {'0': (D0V, g0), '1': (D1V, g1), '2': (D2V, g2), '3': (D3V, g3), '4': (D4V, g4), '5': ("Y'", cc[WG("Y'")]), '6': ('X"', cc[WG('X"')]), '7': (D7V, g7)}
        B = Src(w, pc, Tc, vals8)
        B.gam[ENCL('Q', '(/)')] = gq
        B.gam[EWg('N', '(/)')] = gn0
        return cc, cl, ty, B
    cc, cl, ty, B = base(ph, T0)
    mk = B.mk
    R = B.run()
    N1 = NFL('1o')
    ex = {STMT(GT(Y9)): gotocl(w, ph, mk['tv'], Y9, B.ex[LAB(Y9)]), 'A. m e. %s ( TMfl ` m ) = 1o' % N1: A8.ht_nfl(w, ph, '1o'), SSS(N1): B.ss(N1)}
    B.call(R, 'tm2lbrt', {'A': Z3, 'C': 'TMfl', 'E': Y6, 'Q': GT(Y9), 'N': N1}, ex, [])
    B.call(R, 'tmiverb', {'W': 'A', 'F': 'F', 'B': "B'", 'N': "N'", 'X': ENCL('Q', '(/)'), 'Y': EWg('N', '(/)'), 'P': PL('P', 9), 'E': Z4},
           {WG(ENCL('Q', '(/)')): B.gam[ENCL('Q', '(/)')], WG(EWg('N', '(/)')): B.gam[EWg('N', '(/)')]}, [], pre=(N1, B.ss(N1)))
    VF_ = "( 1st ` ( F Verify A ) )"
    q1f = s([s([cc[EQ("Q'")]], 'fveq2d', "( %s -> ( 1st ` Q' ) = %s )" % (ph, VF_))], 'eqcomd', "( %s -> %s = ( 1st ` Q' ) )" % (ph, VF_))
    t0, C0, D0, n0 = cls_to(w, ph, (R.tri, R.C0, R.cur, R.n), VF_, "( 1st ` Q' )", q1f)
    assert D0 == CLN(Z4, NFL("( 1st ` Q' )"), 'D'), D0
    rq_, n0b = w.rewrite(n0, {LEQD["Q'"]: ("Q'", s([cc[EQ("Q'")]], 'eqcomd', "( %s -> %s = Q' )" % (ph, LEQD["Q'"])))}, ph)
    t0, C0, D0, n0 = hrrw(w, ph, t0, C0, D0, n0, neq=rq_)
    # the two verdicts
    w2, q1 = verify_typing(w, ph, cc, cl)
    two = s([q1, s([s([], 'df2o3', '2o = { (/) , 1o }')], 'a1i', '( %s -> 2o = { (/) , 1o } )' % ph)], 'eleqtrd', "( %s -> ( 1st ` Q' ) e. { (/) , 1o } )" % ph)
    cases = s([two, w.inst('elpri')], 'syl', "( %s -> ( ( 1st ` Q' ) = (/) \\/ ( 1st ` Q' ) = 1o ) )" % ph)
    outs = []
    for verdict in ('(/)', '1o'):
        cond = "( 1st ` Q' ) = %s" % verdict
        Tc = (T0, cond)
        pc = cj(Tc)
        ccx, clx, tyx, Bx = base(pc, Tc)
        L_ = lambda st: lift_from(w, ph, pc, st)
        vst = ccx[cond]
        mkx = Bx.mk
        # the common triple lifted, its class rewritten to the verdict
        tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), "( 1st ` Q' )", verdict, vst)
        assert Dc == CLN(Z4, NFL(verdict), 'D'), Dc
        w2x, _ = verify_typing(w, pc, ccx, clx)
        # the search value in this case
        sv, rhs = search_value(w, pc, ccx, clx)
        nlt = not_lt(w, pc, clx, 'U', 'I', ccx['U <_ I'])
        nj = s([ccx["( 1st ` J ) =/= %s" % INR]], 'neneqd', "( %s -> -. ( 1st ` J ) = %s )" % (pc, INR))
        nx = s([ccx["( 1st ` X' ) =/= %s" % INR]], 'neneqd', "( %s -> -. ( 1st ` X' ) = %s )" % (pc, INR))
        sv2, rhs2 = reduce_if(w, pc, sv, rhs, [nlt, nj, nx])
        assert rhs2 == '<. %s , %s >.' % (IFQ, CST4), '\n%s\n%s' % (rhs2, '<. %s , %s >.' % (IFQ, CST4))
        cst2 = s([s([sv2], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (pc, SE, IFQ, CST4)),
                  s([s([s([], 'ifex', '%s e. _V' % IFQ)], 'a1i', '( %s -> %s e. _V )' % (pc, IFQ)), s([s([], 'ovex', '%s e. _V' % CST4)], 'a1i', '( %s -> %s e. _V )' % (pc, CST4)), w.inst('op2nd')],
                    'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pc, IFQ, CST4, CST4))], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (pc, SE, CST4))
        Rx = Bx.run()
        if verdict == '1o':
            ifq = s([vst], 'iftrued', '( %s -> %s = ( inl ` <. F , A >. ) )' % (pc, IFQ))
            ex = {STMT(GT(Y8)): gotocl(w, pc, mkx['tv'], Y8, Bx.ex[LAB(Y8)]), 'A. m e. %s ( TMfl ` m ) = 1o' % N1: A8.ht_nfl(w, pc, '1o'), SSS(N1): Bx.ss(N1)}
            Bx.call(Rx, 'tm2lbrt', {'A': Z4, 'C': 'TMfl', 'E': Y7, 'Q': GT(Y8), 'N': N1}, ex, [])
            exo = dict(Bx.ex)
            exo.update({WG(ENCL('Q', '(/)')): Bx.gam[ENCL('Q', '(/)')], WG(EWg('N', '(/)')): Bx.gam[EWg('N', '(/)')], STKD('D'): Bx.dd})
            for k, v in Rx.S.vals.items():
                exo['( D ` %s ) = %s' % (k, v[0])] = v[1]
            t2, cc2 = inst(w, pc, 'tmiout', {'W': 'A', 'F': 'F', 'B': "B'", 'N': "N'", 'X': ENCL('Q', '(/)'), 'Y': EWg('N', '(/)'), 'P': PL('P', 10), 'E': 'E'}, Bld(w, pc, ccx, exo))
            C2, D2, n2 = triple_parts(cc2)
            assert C2 == CLN(Y7, S, 'D'), C2
            t2s = hrssc(w, pc, mkx['phm'], t2, C2, D2, n2, CLN(Y7, N1, 'D'), clnss(w, pc, Y7, N1, S, 'D', Bx.ss(N1)))
            assert Rx.cur == CLN(Y7, N1, 'D'), Rx.cur
            tl = hrseq(w, pc, mkx['phm'], Rx.tri, t2s, Rx.C0, Rx.cur, D2, Rx.n, n2)
            nl = '( %s + %s )' % (Rx.n, n2)
            OUTT = '( F encodeOutput A )'
            ie = out_init(w, pc, sv2, (IFQ, ifq), CST4, OUTT, None, True, 'F', 'A')
            tl, _, Dl, _ = hrrw(w, pc, tl, Rx.C0, D2, nl, deq=clneq(w, pc, 'E', S, ie, INIT('1', OUTT), INIT('1', OUTS)))
        else:
            ifq = s([s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o')], 'a1i', '( %s -> (/) =/= 1o )' % pc), s([vst], 'eqeq1d', "( %s -> ( ( 1st ` Q' ) = 1o <-> (/) = 1o ) )" % pc)],
                        'mtbird' if False else 'id', '') if False else None
            n0_ = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o'), s([], 'neneq', '( (/) =/= 1o -> -. (/) = 1o )')], 'ax-mp', '-. (/) = 1o')
            nq = s([s([n0_], 'a1i', '( %s -> -. (/) = 1o )' % pc), s([vst], 'eqeq1d', "( %s -> ( ( 1st ` Q' ) = 1o <-> (/) = 1o ) )" % pc)], 'mtbird', "( %s -> -. ( 1st ` Q' ) = 1o )" % pc)
            ifq = s([nq], 'iffalsed', '( %s -> %s = %s )' % (pc, IFQ, INR))
            exf = dict(Bx.ex)
            exf[STKD('D')] = Bx.dd
            t2, cc2 = inst(w, pc, 'tmisrfl', {'A': Z4, 'X': Y7, 'Q': PL('P', 11), 'D': 'D', 'E': 'E'}, Bld(w, pc, ccx, exf))
            C2, D2, n2 = triple_parts(cc2)
            assert C2 == CLN(Z4, NFL('(/)'), 'D'), C2
            Rx.tri, Rx.C0, Rx.cur, Rx.n = t2, C2, D2, n2
            tl, nl = t2, n2
            ie = out_init(w, pc, sv2, (IFQ, ifq), CST4, COMMA1, None, False)
            tl, _, Dl, _ = hrrw(w, pc, tl, C2, D2, nl, deq=clneq(w, pc, 'E', S, ie, INIT('1', COMMA1), INIT('1', OUTS)))
        assert Dl == POST, Dl
        # the whole triple of this case
        t = hrseq(w, pc, mkx['phm'], tc, tl, Cc, Dc, Dl, nc, nl)
        n = '( %s + %s )' % (nc, nl)
        # the bound: n <_ TOT - Z'
        hy = [ccx["Z' <_ %s" % PRE4], ccx["U' <_ W'"], ccx["8 <_ U'"], ccx["( B' + 2 ) <_ U'"], ccx["( N' + 2 ) <_ U'"], ccx["B <_ B'"], ccx["H <_ B'"],
              ccx["( # ` Y' ) <_ W'"], ccx['( # ` X" ) <_ W\''], ccx["( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )"], ccx["( # ` ( encList ` A ) ) <_ W'"]]
        # verify's cost: ( w + 1 ) x. TMB( 4 VX + 6 ) <_ ( w + 1 ) x. U'
        T46 = '( TMB ` ( ( 4 x. %s ) + 6 ) )' % VX4
        clx.leaf('( # ` A )', 'NN0', s([ccx['A e. Word NN0'], w.inst('lencl')], 'syl', '( %s -> ( # ` A ) e. NN0 )' % pc))
        clx.leaf(T46, 'NN0', tmbn(w, pc, '( ( 4 x. %s ) + 6 )' % VX4, clx.mem('( ( 4 x. %s ) + 6 )' % VX4, 'NN0')))
        cvle = mul_le2(w, pc, clx, '( %s + 1 )' % W2, T46, "U'", ccx[HB5])
        hy.append(cvle)
        # the stack lengths
        atoms = {}
        for t_, tn_, b_, bn_, tlt_ in (('X', tyx['X'], "B'", ccx["B' e. NN0"], ccx[LT2('X', "B'")]), ('O', ccx['O e. NN0'], 'H', ccx['H e. NN0'], ccx[LT2('O', 'H')]),
                                       ('Z', tyx['zn0'], 'B', ccx['B e. NN0'], ccx[LT2('Z')]), ("J'", tyx["J'"], "B'", ccx["B' e. NN0"], ccx[LT2("J'", "B'")]),
                                       ('L', tyx['L'], "B'", ccx["B' e. NN0"], ccx[LT2('L', "B'")]), ('F', ccx['F e. NN0'], "N'", ccx["N' e. NN0"], ccx[LT2('F', "N'")]),
                                       ('N', ccx['N e. NN0'], 'H', ccx['H e. NN0'], ccx[LT2('N', 'H')])):
            atoms['( encNatGam ` %s )' % t_] = numatom(w, pc, clx, t_, tn_, b_, bn_, tlt_)
        atoms['( encList ` Q )'] = (s([tyx['Q'], w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` Q ) e. Word Gamma' )" % pc), None)
        atoms['( encList ` A )'] = (s([ccx['A e. Word NN0'], w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` A ) e. Word Gamma' )" % pc), None)
        atoms["Y'"] = (ccx[WG("Y'")], None)
        atoms['X"'] = (ccx[WG('X"')], None)
        lf = []
        for k in N8:
            v = Rx.S0.vals[k][0] if k not in ('5', '6') else Bx.S0.vals[k][0]
            v = Bx.S0.vals[k][0]
            lenfacts(w, pc, clx, v, atoms, lf)
            e = s([Bx.S0.vals[k][1]], 'fveq2d', '( %s -> ( # ` ( D ` %s ) ) = ( # ` %s ) )' % (pc, k, v))
            clx.leaf('( # ` ( D ` %s ) )' % k, 'NN0', s([e, clx.mem('( # ` %s )' % v, 'NN0')], 'eqeltrd', '( %s -> ( # ` ( D ` %s ) ) e. NN0 )' % (pc, k)))
            lf.append(e)
        hy += lf
        if verdict == '1o':
            # ho1 : ( # A + 1 ) TMB b1 <_ W' ; ho2 : # A ( 2 b1 + 6 ) + 3 <_ 3 W' ; TMB bM <_ U'
            clx.leaf("( TMB ` B' )", 'NN0', tmbn(w, pc, "B'", ccx["B' e. NN0"]))
            clx.leaf("( TMB ` N' )", 'NN0', tmbn(w, pc, "N'", ccx["N' e. NN0"]))
            mA1 = mul_le2(w, pc, clx, '( ( # ` A ) + 1 )', "( TMB ` B' )", "U'", ccx["( TMB ` B' ) <_ U'"])
            mA2 = mul_le2(w, pc, clx, '( ( # ` A ) + 2 )', "( B' + 2 )", "U'", ccx["( B' + 2 ) <_ U'"])
            hy.append(mA1); hy.append(mA2)
            hy += [ccx["( ( ( # ` A ) + 2 ) x. U' ) <_ W'"], ccx["( TMB ` N' ) <_ U'"], clx.ge0('( # ` A )')]
        # the budget lemma at the letters
        bud = s([s([s([s([ccx["U' e. NN0"], ccx["W' e. NN0"]], 'jca', "( %s -> ( U' e. NN0 /\\ W' e. NN0 ) )" % pc),
                       s([ccx["U' <_ W'"], ccx["8 <_ U'"]], 'jca', "( %s -> ( U' <_ W' /\\ 8 <_ U' ) )" % pc)], 'jca',
                      "( %s -> ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) )" % pc),
                    s([s([tyx["C'"], tyx['J2']], 'jca', "( %s -> ( C' e. NN0 /\\ %s e. NN0 ) )" % (pc, S2)), s([tyx['E2'], w2x], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (pc, E2, W2))], 'jca',
                      "( %s -> ( ( C' e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) )" % (pc, S2, E2, W2))], 'jca',
                   "( %s -> ( ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) /\\ ( ( C' e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) ) )" % (pc, S2, E2, W2)),
                 w.inst('t12bud')], 'syl', '( %s -> %s )' % (pc, tsub_text('%s <_ %s' % (BUDL, BUDR), {'U': "U'", 'V': "W'", 'C': "C'", 'S': S2, 'E': E2, 'W': W2})))
        hy.append(bud)
        # TOT with the search cost
        TOT2 = '( ( %s + 1 ) x. ( ; ; 3 0 0 x. W\' ) )' % CST4
        te = s([s([cst2], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( %s + 1 ) )' % (pc, SE, CST4))], 'oveq1d', '( %s -> %s = %s )' % (pc, TOT, TOT2))
        for m_ in ("( C' x. U' )", "( %s x. U' )" % S2, "( %s x. W' )" % E2, "( %s x. U' )" % W2, "( C' x. W' )", "( %s x. W' )" % S2, "( %s x. W' )" % W2):
            hy.append(clx.ge0(m_))
        hy += [clx.ge0(x) for x in ("C'", S2, E2, W2, "Z'")]
        BND2 = "( %s - Z' )" % TOT2
        # (a) the leaf's cost against ( C' + 1 ) U' + 50 W' (linear in the length atoms), (b) verify's cost, (c) the budget
        LB = "( ( ( C' + 1 ) x. U' ) + ( ; 5 0 x. W' ) )"
        lin_hy = [ccx["U' <_ W'"], ccx["8 <_ U'"], ccx["( B' + 2 ) <_ U'"], ccx["( N' + 2 ) <_ U'"], ccx["B <_ B'"], ccx["H <_ B'"],
                  ccx["( # ` Y' ) <_ W'"], ccx['( # ` X" ) <_ W\''], ccx["( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )"], ccx["( # ` ( encList ` A ) ) <_ W'"]] + lf
        if verdict == '1o':
            a12 = lemul1(w, pc, clx, '( ( # ` A ) + 1 )', '( ( # ` A ) + 2 )', "U'", linarith(w, pc, [], '( ( # ` A ) + 1 ) <_ ( ( # ` A ) + 2 )', closure=clx))
            ho1 = linarith(w, pc, [mA1, a12, ccx["( ( ( # ` A ) + 2 ) x. U' ) <_ W'"]], "( ( ( # ` A ) + 1 ) x. ( TMB ` B' ) ) <_ W'", closure=clx)
            PB2 = "( ( ( # ` A ) + 2 ) x. ( B' + 2 ) )"
            poly = linarith(w, pc, [clx.ge0("( ( # ` A ) x. B' )"), clx.ge0("B'"), clx.ge0('( # ` A )')], "( ( ( # ` A ) x. ( ( 2 x. B' ) + 6 ) ) + 3 ) <_ ( 3 x. %s )" % PB2,
                            closure=clx, products=True)
            m3 = mul_le2(w, pc, clx, '3', PB2, "( ( ( # ` A ) + 2 ) x. U' )", mA2)
            ho2 = linarith(w, pc, [poly, m3, ccx["( ( ( # ` A ) + 2 ) x. U' ) <_ W'"]], "( ( ( # ` A ) x. ( ( 2 x. B' ) + 6 ) ) + 3 ) <_ ( 3 x. W' )", closure=clx)
            lin_hy += [ho1, ho2, ccx["( TMB ` N' ) <_ U'"]]
        leafle = linarith(w, pc, lin_hy, '%s <_ %s' % (nl, LB), closure=clx)
        for m_ in ("( C' x. U' )", "( %s x. U' )" % S2, "( %s x. W' )" % E2, "( %s x. U' )" % W2, "( C' x. W' )", "( %s x. W' )" % S2, "( %s x. W' )" % W2, "( %s x. W' )" % E2):
            pass
        fin_hy = [ccx["Z' <_ %s" % PRE4], cvle, leafle, bud, ccx["U' <_ W'"], ccx["8 <_ U'"]] + [clx.ge0(x) for x in ("C'", S2, E2, W2, "Z'", "U'", "W'")]
        le = linarith(w, pc, fin_hy, '%s <_ %s' % (n, BND2), closure=clx, products=True)
        zle = linarith(w, pc, fin_hy, "Z' <_ %s" % TOT2, closure=clx, products=True)
        bn2 = s([s([ccx["Z' e. NN0"], clx.mem(TOT2, 'NN0'), w.inst('nn0sub')], 'syl2anc', "( %s -> ( Z' <_ %s <-> %s e. NN0 ) )" % (pc, TOT2, BND2)), zle], 'mpbid' if False else 'id', '') if False else None
        bn2 = s([zle, s([ccx["Z' e. NN0"], clx.mem(TOT2, 'NN0'), w.inst('nn0sub')], 'syl2anc', "( %s -> ( Z' <_ %s <-> %s e. NN0 ) )" % (pc, TOT2, BND2))], 'mpbid', '( %s -> %s e. NN0 )' % (pc, BND2))
        t = hrle(w, pc, mkx['phm'], t, Cc, POST, n, BND2, bn2, le)
        # back to TOT
        beq = s([te], 'oveq1d', "( %s -> %s = ( %s - Z' ) )" % (pc, "( %s - Z' )" % TOT, BND2))
        t, _, _, _ = hrrw(w, pc, t, Cc, POST, BND2, neq=s([beq], 'eqcomd', "( %s -> %s = ( %s - Z' ) )" % (pc, BND2, TOT)))
        outs.append(s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, CONCL_SRC4)))
    st = s(outs + [cases], 'mpjaod', '( %s -> %s )' % (ph, CONCL_SRC4))
    finish(w, st, lab)
    return w.run()


T12EXTRA['t12bud'] = ST_BUD



# ------------------------------------------------------------ t12exbnd: the extraction's size bounds at any index (~ exinvu at the initial state)
Z0 = '<. 1 , <. (/) , <. EmptyTbl , (/) >. >. >.'
STY = '( NN0 X. ( Word NN0 X. ( Tbl X. 2o ) ) )'
SQ0 = lambda i: '( ( W ( L ExSt N ) %s ) ` %s )' % (Z0, i)
MI = lambda i: '( 1st ` %s )' % SQ0(i)
UI = lambda i: '( 1st ` ( 2nd ` %s ) )' % SQ0(i)
TI = lambda i: '( 1st ` ( 2nd ` ( 2nd ` %s ) ) )' % SQ0(i)
HI = lambda i: '( 2nd ` ( 2nd ` ( 2nd ` %s ) ) )' % SQ0(i)
TBC = lambda tb, n: ('A. d e. NN0 ( ( %s ` d ) =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` ( %s ` d ) ) ) <_ %s /\\ A. q e. ran ( 2nd ` ( %s ` d ) ) q < ( 2 ^ B ) ) )'
                     % (tb, tb, n, tb))
T_EXB = ((('L e. NN', 'N e. NN0'), ('W e. Word NN0', 'B e. NN0')), (RALB('W', 'B'), 'I e. ( 0 ... ( # ` W ) )'))
C_EXB = ('( ( %s /\\ ( # ` %s ) <_ I ) /\\ ( %s < ( 2 ^ ( 1 + ( B x. I ) ) ) /\\ ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( I x. ( B + 1 ) ) + 1 ) ) ) )'
         % (RALB(UI('I'), 'B'), UI('I'), MI('I'), TI('I')))
ST_EXB = '( %s -> %s )' % (cj(T_EXB), C_EXB)


def z0_in_sty(w, ph):
    """( ph -> Z0 e. STY )"""
    s = w.s
    a = s([s([], 'emptytblcl', 'EmptyTbl e. Tbl'), s([], '0el2o', '(/) e. 2o'), w.inst('opelxpi')], 'mp2an', '<. EmptyTbl , (/) >. e. ( Tbl X. 2o )')
    b = s([s([], 'wrd0', '(/) e. Word NN0'), a, w.inst('opelxpi')], 'mp2an', '<. (/) , <. EmptyTbl , (/) >. >. e. ( Word NN0 X. ( Tbl X. 2o ) )')
    z = s([s([], '1nn0', '1 e. NN0'), b, w.inst('opelxpi')], 'mp2an', '%s e. %s' % (Z0, STY))
    return s([z], 'a1i', '( %s -> %s e. %s )' % (ph, Z0, STY))


def z0_parts(w, ph):
    """( 1st Z0 ) = 1 , ( 1st ( 2nd Z0 ) ) = (/) , ( 1st ( 2nd ( 2nd Z0 ) ) ) = EmptyTbl , ( 2nd ( 2nd ( 2nd Z0 ) ) ) = (/) (closed, lifted)"""
    s = w.s
    IN2 = '<. (/) , <. EmptyTbl , (/) >. >.'
    IN3 = '<. EmptyTbl , (/) >.'
    x1 = s([], '1ex', '1 e. _V'); x2 = s([], 'opex', '%s e. _V' % IN2); x0 = s([], '0ex', '(/) e. _V'); x3 = s([], 'opex', '%s e. _V' % IN3)
    xe = s([], 'emptytblcl', 'EmptyTbl e. Tbl')
    xev = s([xe], 'elexi', 'EmptyTbl e. _V')
    p1 = s([x1, x2], 'op1st', '( 1st ` %s ) = 1' % Z0)
    q2 = s([x1, x2], 'op2nd', '( 2nd ` %s ) = %s' % (Z0, IN2))
    p2 = s([s([q2], 'fveq2i', '( 1st ` ( 2nd ` %s ) ) = ( 1st ` %s )' % (Z0, IN2)), s([x0, x3], 'op1st', '( 1st ` %s ) = (/)' % IN2)], 'eqtri',
           '( 1st ` ( 2nd ` %s ) ) = (/)' % Z0)
    q3 = s([s([q2], 'fveq2i', '( 2nd ` ( 2nd ` %s ) ) = ( 2nd ` %s )' % (Z0, IN2)), s([x0, x3], 'op2nd', '( 2nd ` %s ) = %s' % (IN2, IN3))], 'eqtri',
           '( 2nd ` ( 2nd ` %s ) ) = %s' % (Z0, IN3))
    p3 = s([s([q3], 'fveq2i', '( 1st ` ( 2nd ` ( 2nd ` %s ) ) ) = ( 1st ` %s )' % (Z0, IN3)), s([xev, x0], 'op1st', '( 1st ` %s ) = EmptyTbl' % IN3)], 'eqtri',
           '( 1st ` ( 2nd ` ( 2nd ` %s ) ) ) = EmptyTbl' % Z0)
    p4 = s([s([q3], 'fveq2i', '( 2nd ` ( 2nd ` ( 2nd ` %s ) ) ) = ( 2nd ` %s )' % (Z0, IN3)), s([xev, x0], 'op2nd', '( 2nd ` %s ) = (/)' % IN3)], 'eqtri',
           '( 2nd ` ( 2nd ` ( 2nd ` %s ) ) ) = (/)' % Z0)
    L_ = lambda st, f: s([st], 'a1i', '( %s -> %s )' % (ph, f))
    return (L_(p1, '( 1st ` %s ) = 1' % Z0), L_(p2, '( 1st ` ( 2nd ` %s ) ) = (/)' % Z0), L_(p3, '( 1st ` ( 2nd ` ( 2nd ` %s ) ) ) = EmptyTbl' % Z0),
            L_(p4, '( 2nd ` ( 2nd ` ( 2nd ` %s ) ) ) = (/)' % Z0))


def sq_comps(w, ph, cl, ln, nn, ww, z0, i_txt, ii):
    """the typing of the components of ( SQ0 ` i ) : ( m e. NN0 , used e. Word NN0 , tbl e. Tbl , hit e. 2o )"""
    s = w.s
    SQ = SQ0(i_txt)
    j = s([s([s([ln, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0, STY))], 'jca',
             '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (ph, Z0, STY)), ii], 'jca',
          '( %s -> ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) /\\ %s e. ( 0 ... ( # ` W ) ) ) )' % (ph, Z0, STY, i_txt))
    sc = s([j, w.inst('exstcl')], 'syl', '( %s -> %s e. %s )' % (ph, SQ, STY))
    m = s([sc, w.inst('xp1st')], 'syl', '( %s -> %s e. NN0 )' % (ph, MI(i_txt)))
    r2 = s([sc, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` %s ) e. ( Word NN0 X. ( Tbl X. 2o ) ) )' % (ph, SQ))
    u = s([r2, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, UI(i_txt)))
    r3 = s([r2, w.inst('xp2nd')], 'syl', '( %s -> ( 2nd ` ( 2nd ` %s ) ) e. ( Tbl X. 2o ) )' % (ph, SQ))
    tb = s([r3, w.inst('xp1st')], 'syl', '( %s -> %s e. Tbl )' % (ph, TI(i_txt)))
    h = s([r3, w.inst('xp2nd')], 'syl', '( %s -> %s e. 2o )' % (ph, HI(i_txt)))
    cl.leaf(MI(i_txt), 'NN0', m)
    cl.leaf('( # ` %s )' % UI(i_txt), 'NN0', s([u, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, UI(i_txt))))
    return m, u, tb, h


def t12exbnd():
    lab = 't12exbnd'
    T = T_EXB
    ph = cj(T)
    w = W(lab, 'The size bounds of the extraction state at any index of the pool, from the initial state ` ( 1 , [] , emptyTbl , false ) ` '
               '(Lean ` extractFin_bounded ` read by Step5): the entries of ` used ` stay below ` 2 ^ b ` and there are at most ` i ` of them, '
               '` m < 2 ^ ( 1 + b i ) ` , and the ascending table word has at most ` L ( i ( b + 1 ) + 1 ) ` symbols (~ exinvu , ~ ttabtbll ).')
    s = w.s
    c = Ctx(w, ph, T)
    ln, nn, ww, bn, ral, ii = c['L e. NN'], c['N e. NN0'], c['W e. Word NN0'], c['B e. NN0'], c[RALB('W', 'B')], c['I e. ( 0 ... ( # ` W ) )']
    cl = Closure(w, ph, {'N': ('NN0', nn), 'B': ('NN0', bn)})
    cl.leaf('L', 'NN0', s([ln], 'nnnn0d', '( %s -> L e. NN0 )' % ph))
    inn = s([ii, w.inst('elfznn0')], 'syl', '( %s -> I e. NN0 )' % ph)
    cl.leaf('I', 'NN0', inn)
    z0 = z0_in_sty(w, ph)
    p1, p2, p3, p4 = z0_parts(w, ph)
    # the initial facts for exinvu (N := 0 , C := 1)
    r0 = s([s([s([s([], 'rn0', 'ran (/) = (/)')], 'raleqi', '( A. a e. ran (/) a < ( 2 ^ B ) <-> A. a e. (/) a < ( 2 ^ B ) )'),
                s([], 'ral0', 'A. a e. (/) a < ( 2 ^ B )')], 'mpbir', 'A. a e. ran (/) a < ( 2 ^ B )')], 'a1i', '( %s -> A. a e. ran (/) a < ( 2 ^ B ) )' % ph)
    rz = s([s([s([p2], 'rneqd', '( %s -> ran ( 1st ` ( 2nd ` %s ) ) = ran (/) )' % (ph, Z0))], 'raleqdv',
              '( %s -> ( %s <-> A. a e. ran (/) a < ( 2 ^ B ) ) )' % (ph, RALB('( 1st ` ( 2nd ` %s ) )' % Z0, 'B'))), r0], 'mpbird',
            '( %s -> %s )' % (ph, RALB('( 1st ` ( 2nd ` %s ) )' % Z0, 'B')))
    tb0 = s([closed(w, ph, '0nn0', '0 e. NN0'), bn, w.inst('ttabtbb0')], 'syl2anc', '( %s -> %s )' % (ph, TBC('EmptyTbl', '0')))
    tbz = s([s([p3, w.inst('tmextbb')], 'syl', '( %s -> ( %s <-> %s ) )' % (ph, TBC('( 1st ` ( 2nd ` ( 2nd ` %s ) ) )' % Z0, '0'), TBC('EmptyTbl', '0'))), tb0],
            'mpbird', '( %s -> %s )' % (ph, TBC('( 1st ` ( 2nd ` ( 2nd ` %s ) ) )' % Z0, '0')))
    e21 = s([s([s([], '2cn', '2 e. CC'), w.inst('exp1')], 'ax-mp', '( 2 ^ 1 ) = 2')], 'a1i', '( %s -> ( 2 ^ 1 ) = 2 )' % ph)
    m0 = s([s([p1, closed(w, ph, '1lt2', '1 < 2')], 'eqbrtrd', '( %s -> ( 1st ` %s ) < 2 )' % (ph, Z0)), e21], 'breqtrrd', '( %s -> ( 1st ` %s ) < ( 2 ^ 1 ) )' % (ph, Z0))
    ex = {'L e. NN': ln, 'N e. NN0': nn, 'W e. Word NN0': ww, '%s e. %s' % (Z0, STY): z0, '0 e. NN0': closed(w, ph, '0nn0', '0 e. NN0'), 'B e. NN0': bn,
          '1 e. NN0': closed(w, ph, '1nn0', '1 e. NN0'), RALB('W', 'B'): ral, RALB('( 1st ` ( 2nd ` %s ) )' % Z0, 'B'): rz,
          TBC('( 1st ` ( 2nd ` ( 2nd ` %s ) ) )' % Z0, '0'): tbz, '( 1st ` %s ) < ( 2 ^ 1 )' % Z0: m0, 'I e. ( 0 ... ( # ` W ) )': ii}
    st, cc = inst(w, ph, 'exinvu', {'G': 'N', 'Z': Z0, 'N': '0', 'C': '1'}, Bld(w, ph, c, ex))
    # cc = ( RALB( used ) /\ E. c e. ( 0 ... ( 0 + I ) ) ( TBC( tbl , c ) /\ m < 2 ^ ( 1 + ( B x. ( ( 0 + I ) - c ) ) ) /\ ( # used + c ) <_ ( # ( 1st ( 2nd Z0 ) ) + ( 0 + I ) ) ) )
    ralu = s([st], 'simpld', '( %s -> %s )' % (ph, RALB(UI('I'), 'B')))
    exc = s([st], 'simprd', '( %s -> %s )' % (ph, cc.split(' /\\ ', 1)[1][:-2] if False else cc[len('( %s /\\ ' % RALB(UI('I'), 'B')):-2]))
    EXT = cc[len('( %s /\\ ' % RALB(UI('I'), 'B')):-2]
    assert EXT.startswith('E. c e. ( 0 ... ( 0 + I ) ) '), EXT
    BODY = EXT[len('E. c e. ( 0 ... ( 0 + I ) ) '):]
    MLT = '%s < ( 2 ^ ( 1 + ( B x. ( ( 0 + I ) - c ) ) ) )' % MI('I')
    LEN = '( ( # ` %s ) + c ) <_ ( ( # ` ( 1st ` ( 2nd ` %s ) ) ) + ( 0 + I ) )' % (UI('I'), Z0)
    assert BODY == '( %s /\\ %s /\\ %s )' % (TBC(TI('I'), 'c'), MLT, LEN), '\n%s\n%s' % (BODY, '( %s /\\ %s /\\ %s )' % (TBC(TI('I'), 'c'), MLT, LEN))
    # under the witness
    Tc = (T, ('c e. ( 0 ... ( 0 + I ) )', (TBC(TI('I'), 'c'), MLT, LEN)))
    pc = cj(Tc)
    cx = Ctx(w, pc, Tc)
    L_ = lambda st_: lift_from(w, ph, pc, st_)
    clc = Closure(w, pc, {'N': ('NN0', L_(nn)), 'B': ('NN0', L_(bn)), 'I': ('NN0', L_(inn)), 'L': ('NN0', L_(cl.mem('L', 'NN0')))})
    cin = cx['c e. ( 0 ... ( 0 + I ) )']
    cn0 = s([cin, w.inst('elfznn0')], 'syl', '( %s -> c e. NN0 )' % pc)
    clc.leaf('c', 'NN0', cn0)
    cle = s([cin, w.inst('elfzle2')], 'syl', '( %s -> c <_ ( 0 + I ) )' % pc)
    m_, u_, tb_, h_ = sq_comps(w, pc, clc, L_(ln), L_(nn), L_(ww), L_(z0), 'I', L_(ii))
    # (i) # used <_ I
    h0 = s([s([L_(p2)], 'fveq2d', '( %s -> ( # ` ( 1st ` ( 2nd ` %s ) ) ) = ( # ` (/) ) )' % (pc, Z0)), s([s([], 'hash0', '( # ` (/) ) = 0')], 'a1i', '( %s -> ( # ` (/) ) = 0 )' % pc)],
           'eqtrd', '( %s -> ( # ` ( 1st ` ( 2nd ` %s ) ) ) = 0 )' % (pc, Z0))
    clc.leaf('( # ` ( 1st ` ( 2nd ` %s ) ) )' % Z0, 'NN0', s([h0, closed(w, pc, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> ( # ` ( 1st ` ( 2nd ` %s ) ) ) e. NN0 )' % (pc, Z0)))
    ule = linarith(w, pc, [cx[LEN], h0, clc.ge0('c')], '( # ` %s ) <_ I' % UI('I'), closure=clc)
    # (ii) m < 2 ^ ( 1 + B I )
    DC = '( ( 0 + I ) - c )'
    dcn = s([clc.mem('( 0 + I )', 'NN0'), cn0, cle, w.inst('nn0sub2') if False else w.inst('nn0sub2')], 'syl3anc', '') if False else None
    dcn = s([cn0, clc.mem('( 0 + I )', 'NN0'), cle, w.inst('nn0sub2')], 'syl3anc', '( %s -> %s e. NN0 )' % (pc, DC))
    dle = linarith(w, pc, [clc.ge0('c')], '%s <_ I' % DC, closure=clc)
    bm = mul_le2(w, pc, clc, 'B', DC, 'I', dle)
    E0_ = '( 1 + ( B x. %s ) )' % DC
    E1_ = '( 1 + ( B x. I ) )'
    ele = linarith(w, pc, [bm], '%s <_ %s' % (E0_, E1_), closure=clc)
    e0n = s([closed(w, pc, '1nn0', '1 e. NN0'), s([L_(bn), dcn], 'nn0mulcld', '( %s -> ( B x. %s ) e. NN0 )' % (pc, DC))], 'nn0addcld', '( %s -> %s e. NN0 )' % (pc, E0_))
    eu = s([s([s([e0n], 'nn0zd', '( %s -> %s e. ZZ )' % (pc, E0_)), s([clc.mem(E1_, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (pc, E1_)), ele], '3jca',
              '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ %s <_ %s ) )' % (pc, E0_, E1_, E0_, E1_)), w.inst('eluz2')], 'sylibr', '( %s -> %s e. ( ZZ>= ` %s ) )' % (pc, E1_, E0_))
    pe = s([closed(w, pc, '2re', '2 e. RR'), closed(w, pc, '1le2', '1 <_ 2'), eu, w.inst('leexp2a')], 'syl3anc', '( %s -> ( 2 ^ %s ) <_ ( 2 ^ %s ) )' % (pc, E0_, E1_))
    clc.atom('( 2 ^ %s )' % E0_); clc.atom('( 2 ^ %s )' % E1_)
    p0n = s([closed(w, pc, '2nn0', '2 e. NN0'), e0n, w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (pc, E0_))
    p1n = s([closed(w, pc, '2nn0', '2 e. NN0'), clc.mem(E1_, 'NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (pc, E1_))
    clc.leaf('( 2 ^ %s )' % E0_, 'NN0', p0n); clc.leaf('( 2 ^ %s )' % E1_, 'NN0', p1n)
    mlt = linarith(w, pc, [cx[MLT], pe], '%s < ( 2 ^ %s )' % (MI('I'), E1_), closure=clc)
    # (iii) the table word
    tl = s([s([s([clc.mem('L', 'NN0'), tb_], 'jca', '( %s -> ( L e. NN0 /\\ %s e. Tbl ) )' % (pc, TI('I'))), s([cn0, L_(bn)], 'jca', '( %s -> ( c e. NN0 /\\ B e. NN0 ) )' % pc),
                cx[TBC(TI('I'), 'c')]], '3jca', '( %s -> ( ( L e. NN0 /\\ %s e. Tbl ) /\\ ( c e. NN0 /\\ B e. NN0 ) /\\ %s ) )' % (pc, TI('I'), TBC(TI('I'), 'c'))),
             w.inst('ttabtbll')], 'syl', '( %s -> ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( c x. ( B + 1 ) ) + 1 ) ) )' % (pc, TI('I')))
    cle2 = linarith(w, pc, [cle], 'c <_ I', closure=clc)
    cb = s([s([clc.mem('c', 'RR'), clc.mem('I', 'RR'), s([clc.mem('( B + 1 )', 'RR'), clc.ge0('( B + 1 )')], 'jca', '( %s -> ( ( B + 1 ) e. RR /\\ 0 <_ ( B + 1 ) ) )' % pc)], '3jca',
                '( %s -> ( c e. RR /\\ I e. RR /\\ ( ( B + 1 ) e. RR /\\ 0 <_ ( B + 1 ) ) ) )' % pc), cle2], 'jca',
             '( %s -> ( ( c e. RR /\\ I e. RR /\\ ( ( B + 1 ) e. RR /\\ 0 <_ ( B + 1 ) ) ) /\\ c <_ I ) )' % pc)
    cbm = s([cb, w.inst('lemul1a')], 'syl', '( %s -> ( c x. ( B + 1 ) ) <_ ( I x. ( B + 1 ) ) )' % pc)
    inner = linarith(w, pc, [cbm], '( ( c x. ( B + 1 ) ) + 1 ) <_ ( ( I x. ( B + 1 ) ) + 1 )', closure=clc)
    lm = mul_le2(w, pc, clc, 'L', '( ( c x. ( B + 1 ) ) + 1 )', '( ( I x. ( B + 1 ) ) + 1 )', inner)
    TW = '( # ` ( L encTblAsc %s ) )' % TI('I')
    clc.leaf(TW, 'NN0', s([tblw(w, pc, TI('I'), tb_, 'L', clc.mem('L', 'NN0')), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (pc, TW)))
    tle = linarith(w, pc, [tl, lm], '%s <_ ( L x. ( ( I x. ( B + 1 ) ) + 1 ) )' % TW, closure=clc)
    both = s([s([L_(ralu), ule], 'jca', '( %s -> ( %s /\\ ( # ` %s ) <_ I ) )' % (pc, RALB(UI('I'), 'B'), UI('I'))), s([mlt, tle], 'jca',
              '( %s -> ( %s < ( 2 ^ %s ) /\\ %s <_ ( L x. ( ( I x. ( B + 1 ) ) + 1 ) ) ) )' % (pc, MI('I'), E1_, TW))], 'jca', '( %s -> %s )' % (pc, C_EXB))
    fin = s([exc, both], 'rexlimddv', '( %s -> %s )' % (ph, C_EXB))
    w.qed([fin, w.inst('biid')], 'mpbi', ST_EXB)
    return w.run()


T12EXTRA['t12exbnd'] = ST_EXB



# ------------------------------------------------------------ t12pglen: the pool is at most as long as the list it is built from (word induction)
from a4alib import family as _family
PG = lambda s_: '( ( ( X PoolGo Z ) ` K ) ` %s )' % s_
HYP3 = '( X e. NN0 /\\ Z e. NN0 /\\ K e. NN0 )'
PHI_PG = '( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` s ) )' % (HYP3, PG('s'))
ST_PGLEN = '( W e. Word NN0 -> ( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` W ) ) )' % (HYP3, PG('W'))


def _pgb(w, goal):
    s = w.s
    ph = HYP3
    j = s([s([s([], 'simp1', '( %s -> X e. NN0 )' % ph), s([], 'simp2', '( %s -> Z e. NN0 )' % ph)], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % ph),
           s([], 'simp3', '( %s -> K e. NN0 )' % ph)], 'jca', '( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % ph)
    v = s([j, w.inst('poolgo0')], 'syl', '( %s -> %s = <. (/) , 0 >. )' % (ph, PG('(/)')))
    f = s([s([v], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. (/) , 0 >. ) )' % (ph, PG('(/)'))),
           s([s([s([], '0ex', '(/) e. _V'), s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. (/) , 0 >. ) = (/)')], 'a1i', '( %s -> ( 1st ` <. (/) , 0 >. ) = (/) )' % ph)],
          'eqtrd', '( %s -> ( 1st ` %s ) = (/) )' % (ph, PG('(/)')))
    l = s([f], 'fveq2d', '( %s -> ( # ` ( 1st ` %s ) ) = ( # ` (/) ) )' % (ph, PG('(/)')))
    le = s([s([s([], 'hash0', '( # ` (/) ) = 0'), s([], '0nn0', '0 e. NN0')], 'eqeltri', '( # ` (/) ) e. NN0')], 'nn0rei', '( # ` (/) ) e. RR')
    w.qed([l, s([s([le], 'leidi', '( # ` (/) ) <_ ( # ` (/) )')], 'a1i', '( %s -> ( # ` (/) ) <_ ( # ` (/) ) )' % ph)], 'eqbrtrd', goal)


def _pgs(w, A, ih, co):
    s = w.s
    CSV = '( <" P "> ++ V )'
    vs = s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = s([], 'simp2', '( %s -> P e. NN0 )' % A)
    ihs = s([], 'simp3', '( %s -> %s )' % (A, ih))
    pc = '( %s /\\ %s )' % (A, HYP3)
    L = lambda st: s([st], 'adantr', '( %s -> %s )' % (pc, concl(w, A, st)))
    h3 = s([], 'simpr', '( %s -> %s )' % (pc, HYP3))
    xn, zn, kn = [s([h3, w.inst(r)], 'syl', '( %s -> %s e. NN0 )' % (pc, x)) for r, x in (('simp1', 'X'), ('simp2', 'Z'), ('simp3', 'K'))]
    REST = '( 1st ` %s )' % PG('V')
    ihc = s([L(ihs), h3], 'mpd', '( %s -> ( # ` %s ) <_ ( # ` V ) )' % (pc, REST))
    xz = s([xn, zn], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % pc)
    xzk = s([xz, kn], 'jca', '( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) )' % pc)
    pcl = s([xzk, L(vs), w.inst('poolgocl')], 'syl2anc', '( %s -> %s e. ( Word NN0 X. NN0 ) )' % (pc, PG('V')))
    rw = s([pcl, w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, REST))
    QQ = '( ( P x. K ) + 1 )'
    COND = '( %s <_ X /\\ Z < %s )' % (QQ, QQ)
    PRM = '( 1st ` ( IsPrimeTD ` %s ) ) = 1o' % QQ
    ADD = '( <" %s "> ++ %s )' % (QQ, REST)
    INNER = 'if ( %s , %s , %s )' % (PRM, ADD, REST)
    C1 = '( ( ( 2nd ` %s ) + ( 2nd ` ( IsPrimeTD ` %s ) ) ) + 1 )' % (PG('V'), QQ)
    C2 = '( ( 2nd ` %s ) + 1 )' % PG('V')
    rhs = 'if ( %s , <. %s , %s >. , <. %s , %s >. )' % (COND, INNER, C1, REST, C2)
    cs = s([s([xzk, L(pn)], 'jca', '( %s -> ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ K e. NN0 ) /\\ P e. NN0 ) )' % pc), L(vs), w.inst('poolgocs')], 'syl2anc',
           '( %s -> %s = %s )' % (pc, PG(CSV), rhs))
    cl = Closure(w, pc, {})
    cl.leaf('( # ` %s )' % REST, 'NN0', s([rw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (pc, REST)))
    cl.leaf('( # ` V )', 'NN0', s([L(vs), w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % pc))
    lcs = s([L(pn), L(vs), w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (pc, CSV))
    cl.leaf('( # ` %s )' % CSV, 'NN0', s([lcs, cl.mem('( ( # ` V ) + 1 )', 'NN0')], 'eqeltrd', '( %s -> ( # ` %s ) e. NN0 )' % (pc, CSV)))
    qn = s([s([L(pn), kn], 'nn0mulcld', '( %s -> ( P x. K ) e. NN0 )' % pc), closed(w, pc, '1nn0', '1 e. NN0')], 'nn0addcld', '( %s -> %s e. NN0 )' % (pc, QQ))
    ladd = s([qn, rw, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` %s ) + 1 ) )' % (pc, ADD, REST))
    cl.leaf('( # ` %s )' % ADD, 'NN0', s([ladd, cl.mem('( ( # ` %s ) + 1 )' % REST, 'NN0')], 'eqeltrd', '( %s -> ( # ` %s ) e. NN0 )' % (pc, ADD)))
    # bounds of the two candidates
    b_add = linarith(w, pc, [ladd, ihc, lcs], '( # ` %s ) <_ ( # ` %s )' % (ADD, CSV), closure=cl)
    b_rest = linarith(w, pc, [ihc, lcs], '( # ` %s ) <_ ( # ` %s )' % (REST, CSV), closure=cl)
    # INNER by cases on PRM
    pt, pf = '( %s /\\ %s )' % (pc, PRM), '( %s /\\ -. %s )' % (pc, PRM)
    i1 = s([s([s([], 'simpr', '( %s -> %s )' % (pt, PRM))], 'iftrued', '( %s -> %s = %s )' % (pt, INNER, ADD))], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (pt, INNER, ADD))
    i1b = s([i1, s([b_add], 'adantr', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (pt, ADD, CSV))], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (pt, INNER, CSV))
    i2 = s([s([s([], 'simpr', '( %s -> -. %s )' % (pf, PRM))], 'iffalsed', '( %s -> %s = %s )' % (pf, INNER, REST))], 'fveq2d', '( %s -> ( # ` %s ) = ( # ` %s ) )' % (pf, INNER, REST))
    i2b = s([i2, s([b_rest], 'adantr', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (pf, REST, CSV))], 'eqbrtrd', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (pf, INNER, CSV))
    b_inner = s([i1b, i2b], 'pm2.61dan', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (pc, INNER, CSV))
    # the outer if
    F1 = s([cs], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (pc, PG(CSV), rhs))
    ct, cf = '( %s /\\ %s )' % (pc, COND), '( %s /\\ -. %s )' % (pc, COND)
    o1 = s([s([], 'simpr', '( %s -> %s )' % (ct, COND))], 'iftrued', '( %s -> %s = <. %s , %s >. )' % (ct, rhs, INNER, C1))
    o1v = s([s([o1], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (ct, rhs, INNER, C1)),
             s([s([s([], 'ifex', '%s e. _V' % INNER), s([], 'ovex', '%s e. _V' % C1)], 'op1st', '( 1st ` <. %s , %s >. ) = %s' % (INNER, C1, INNER))], 'a1i',
               '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (ct, INNER, C1, INNER))], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ct, rhs, INNER))
    o1b = s([s([o1v], 'fveq2d', '( %s -> ( # ` ( 1st ` %s ) ) = ( # ` %s ) )' % (ct, rhs, INNER)), s([b_inner], 'adantr', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (ct, INNER, CSV))],
             'eqbrtrd', '( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` %s ) )' % (ct, rhs, CSV))
    o2 = s([s([], 'simpr', '( %s -> -. %s )' % (cf, COND))], 'iffalsed', '( %s -> %s = <. %s , %s >. )' % (cf, rhs, REST, C2))
    o2v = s([s([o2], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` <. %s , %s >. ) )' % (cf, rhs, REST, C2)),
             s([s([s([], 'fvex', '%s e. _V' % REST), s([], 'ovex', '%s e. _V' % C2)], 'op1st', '( 1st ` <. %s , %s >. ) = %s' % (REST, C2, REST))], 'a1i',
               '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (cf, REST, C2, REST))], 'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (cf, rhs, REST))
    o2b = s([s([o2v], 'fveq2d', '( %s -> ( # ` ( 1st ` %s ) ) = ( # ` %s ) )' % (cf, rhs, REST)), s([b_rest], 'adantr', '( %s -> ( # ` %s ) <_ ( # ` %s ) )' % (cf, REST, CSV))],
             'eqbrtrd', '( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` %s ) )' % (cf, rhs, CSV))
    ob = s([o1b, o2b], 'pm2.61dan', '( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` %s ) )' % (pc, rhs, CSV))
    fin = s([s([F1], 'fveq2d', '( %s -> ( # ` ( 1st ` %s ) ) = ( # ` ( 1st ` %s ) ) )' % (pc, PG(CSV), rhs)), ob], 'eqbrtrd', '( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` %s ) )' % (pc, PG(CSV), CSV))
    w.qed([fin], 'ex', '( %s -> %s )' % (A, co))


def _run_pg(w):
    return w.run()


def t12pglen():
    return _family(_run_pg, 't12pglen', PHI_PG, _pgb, _pgs, target='W',
                   desc='The pool built from a list of divisors has at most as many entries as the list (word induction; ~ poolgocs ): '
                        'with ~ divisorsoflen this is Lean\'s ` poolAlg_length_le_two_pow ` .', only=SEL)


T12EXTRA['t12pglen'] = ST_PGLEN



# ------------------------------------------------------------ tmisrc3: the extract stage
RIT = '( W ( L ExIt N ) %s )' % Z0
SQR = SQ0(RIT)
MR, USED, TBL, HIT = MI(RIT), UI(RIT), TI(RIT), HI(RIT)
WREST = '( W substr <. %s , ( # ` W ) >. )' % RIT
ACCW3 = '( ( L encTblAsc %s ) ++ <" 0 "> )' % TBL
D6V3 = ENCL(WREST, '(/)')
D7V3 = EWg(MR, EWg('N', '(/)'))
D4V3 = ENCL(USED, ENCL('Q', '(/)'))
EXY = "( ( ( ( L + 1 ) ^ 2 ) x. ( ( # ` W ) + 2 ) ) x. ( TMB ` ( ( ( 3 x. ( # ` W ) ) x. B' ) + ( ( 5 x. B' ) + 5 ) ) ) )"
CEX = "( ( %s + 1 ) x. ( ; 2 5 x. %s ) )" % (E2, EXY)
HB5W = HB5.replace('( # ` A )', '( # ` W )')
NPEQ = "N' = ( ( B' x. ( ( # ` W ) + 1 ) ) + 1 )"
POS1 = '%s e. NN' % MR
POS2 = 'A. a e. ran %s 2 <_ a' % USED
CASE3 = ('U <_ I', "( 1st ` J ) =/= %s" % INR)
PW1 = (RALB('W', "B'"), 'A. a e. ran W 2 <_ a', "( # ` W ) <_ ( 2 ^ U )")
PW2 = (NPEQ, LT2('N', "B'"), "U < B'")
POS = (POS1, POS2)
UN4W = (("( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )", "( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) <_ W'"),
        ("( ( L x. ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'", "( ( ( # ` W ) + 2 ) x. U' ) <_ W'"))
UN5W = ((HB5W, "( TMB ` B' ) <_ U'"), ("( TMB ` N' ) <_ U'", "%s <_ W'" % EXY))
STK3 = (STKD('D'), ((DEQ(0, D0V), DEQ(1, D1V)), (DEQ(2, D2V), DEQ(3, D3V))), ((DEQ(4, ENCL('Q', '(/)')), DEQ(5, '(/)')), (DEQ(6, ENCL('W', '(/)')), DEQ(7, EWg('N', '(/)')))))
CSTH3 = ("Z' e. NN0", "Z' <_ %s" % PRE3)
TREE_SRC3 = ((T_PHM7, FS.pred()),
             ((SC_TY, LEQT), (((CASE3, PW1), (PW2, POS)), (UN1, UN2, UN3), (UN4W, UN5W)),
              ((('B e. NN0', 'H e. NN0', '1 <_ L'), ("B' e. NN0", "N' e. NN0")), STK3, CSTH3)))
CONCL_SRC3 = TRI(CLN(Z2, NFL('1o'), 'D'), POST, "( %s - Z' )" % TOT)
add12('tmisrc3', TREE_SRC3, CONCL_SRC3)


def ext_value(w, ph, c, ty, lnn, ww):
    """( ph -> ( 1st ` X' ) = if ( HIT = 1o , ( inl ` <. MR , USED >. ) , inr ) ) by ~ extractval and ~ exres at the initial state"""
    s = w.s
    nn = c['N e. NN0']
    z0 = z0_in_sty(w, ph)
    p1, p2, p3, p4 = z0_parts(w, ph)
    j = s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0, STY))], 'jca',
          '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (ph, Z0, STY))
    ex_ = s([s([j, p4], 'jca', '( %s -> ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) /\\ ( 2nd ` ( 2nd ` ( 2nd ` %s ) ) ) = (/) ) )' % (ph, Z0, STY, Z0)),
             w.inst('exres')], 'syl', '( %s -> %s )' % (ph, tsub_text(split_imp(stmt('exres'))[1], {'G': 'N', 'Z': Z0})))
    conc = tsub_text(split_imp(stmt('exres'))[1], {'G': 'N', 'Z': Z0})
    first = conc[2:].split(' /\\ ( W ( L ExIt N )', 1)[0]
    IFX = 'if ( %s = 1o , ( inl ` <. %s , %s >. ) , %s )' % (HIT, MR, USED, INR)
    EGOX = first.split(' = ', 1)[0][len('( 1st ` '):-2]
    assert first.endswith(' = ' + IFX), first
    e1 = s([ex_], 'simpld', '( %s -> ( 1st ` %s ) = %s )' % (ph, EGOX, IFX))
    # EGOX -> ( ( ( ( ( L ExtractGo N ) ` W ) ` 1 ) ` (/) ) ` EmptyTbl )
    sq0 = s([j, w.inst('exst0')], 'syl', '( %s -> %s = %s )' % (ph, SQ0('0'), Z0))
    r1 = s([s([sq0], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph, SQ0('0'), Z0)), p1], 'eqtrd', '( %s -> ( 1st ` %s ) = 1 )' % (ph, SQ0('0')))
    r2 = s([s([s([sq0], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (ph, SQ0('0'), Z0))], 'fveq2d',
              '( %s -> ( 1st ` ( 2nd ` %s ) ) = ( 1st ` ( 2nd ` %s ) ) )' % (ph, SQ0('0'), Z0)), p2], 'eqtrd', '( %s -> ( 1st ` ( 2nd ` %s ) ) = (/) )' % (ph, SQ0('0')))
    r3 = s([s([s([s([sq0], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (ph, SQ0('0'), Z0))], 'fveq2d',
                 '( %s -> ( 2nd ` ( 2nd ` %s ) ) = ( 2nd ` ( 2nd ` %s ) ) )' % (ph, SQ0('0'), Z0))], 'fveq2d',
              '( %s -> ( 1st ` ( 2nd ` ( 2nd ` %s ) ) ) = ( 1st ` ( 2nd ` ( 2nd ` %s ) ) ) )' % (ph, SQ0('0'), Z0)), p3], 'eqtrd',
           '( %s -> ( 1st ` ( 2nd ` ( 2nd ` %s ) ) ) = EmptyTbl )' % (ph, SQ0('0')))
    SW0 = '( W substr <. 0 , ( # ` W ) >. )'
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    pv = s([ww, nw, w.inst('pfxval')], 'syl2anc', '( %s -> ( W prefix ( # ` W ) ) = %s )' % (ph, SW0))
    sw = s([s([pv], 'eqcomd', '( %s -> %s = ( W prefix ( # ` W ) ) )' % (ph, SW0)), s([ww, w.inst('pfxid')], 'syl', '( %s -> ( W prefix ( # ` W ) ) = W )' % ph)], 'eqtrd',
           '( %s -> %s = W )' % (ph, SW0))
    rw, EGO1 = w.rewrite(EGOX, {SW0: ('W', sw), '( 1st ` %s )' % SQ0('0'): ('1', r1), '( 1st ` ( 2nd ` %s ) )' % SQ0('0'): ('(/)', r2),
                                '( 1st ` ( 2nd ` ( 2nd ` %s ) ) )' % SQ0('0'): ('EmptyTbl', r3)}, ph)
    assert EGO1 == '( ( ( ( ( L ExtractGo N ) ` W ) ` 1 ) ` (/) ) ` EmptyTbl )', EGO1
    ev = s([s([lnn, nn], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), ww, w.inst('extractval')], 'syl2anc', '( %s -> %s = %s )' % (ph, LEQD["X'"], EGO1))
    xe = s([c[EQ("X'")], ev], 'eqtrd', "( %s -> X' = %s )" % (ph, EGO1))
    f = s([s([xe], 'fveq2d', "( %s -> ( 1st ` X' ) = ( 1st ` %s ) )" % (ph, EGO1)), s([s([rw], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph, EGOX, EGO1))], 'eqcomd',
            '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph, EGO1, EGOX)), e1], '3eqtrd', "( %s -> ( 1st ` X' ) = %s )" % (ph, IFX))
    return f, IFX, j


def tmisrc3():
    lab = 'tmisrc3'
    T0 = numtree(TREE_SRC3)
    ph = cj(T0)
    w = W(lab, 'The extract stage of Lean\'s ` searchF ` at the machine (the scan succeeded): from the second branch with the '
               'flag true, ` extractF 6 3 0 5 1 2 7 4 ` (~ tmiexfb ), then the verify stage (~ tmisrc4 ) or ` failAll ` (~ tmisrfl ) '
               'by whether the extraction found a candidate (~ exres , ~ extractval ); the extraction\'s bounds by ~ t12exbnd .')
    s = w.s

    def base(pc, Tc):
        cc = Ctx(w, pc, Tc)
        cl = Closure(w, pc, {x: ('NN0', cc['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N', "B'", "N'", "U'", "W'", 'B', 'H', "Z'")})
        for x in ('Z', 'Y'):
            cl.leaf(x, 'NN0', s([cc['%s e. NN' % x]], 'nnnn0d', '( %s -> %s e. NN0 )' % (pc, x)))
        ty = stage_typing(w, pc, cc, cl)
        ty.update(some_typing(w, pc, cc, cl, ty))
        wrd0 = closed(w, pc, 'wrd0', "(/) e. Word Gamma'")
        gq = enclg(w, pc, 'Q', ty['Q'], '(/)', wrd0)
        gw = enclg(w, pc, 'W', ty['W'], '(/)', wrd0)
        gn0 = ewg_(w, pc, 'N', cc['N e. NN0'], '(/)', wrd0)
        go = ewg_(w, pc, 'O', cc['O e. NN0'], '(/)', wrd0)
        g0 = ewg_(w, pc, 'X', ty['X'], EWg('O', '(/)'), go)
        g1 = ewg_(w, pc, 'Z', ty['zn0'], '(/)', wrd0)
        g2 = ewg_(w, pc, "J'", ty["J'"], '(/)', wrd0)
        g3 = ewg_(w, pc, 'L', ty['L'], '(/)', wrd0)
        vals8 = {'0': (D0V, g0), '1': (D1V, g1), '2': (D2V, g2), '3': (D3V, g3), '4': (ENCL('Q', '(/)'), gq), '5': ('(/)', wrd0), '6': (ENCL('W', '(/)'), gw), '7': (EWg('N', '(/)'), gn0)}
        B = Src(w, pc, Tc, vals8)
        B.g('(/)', wrd0); B.g(ENCL('Q', '(/)'), gq); B.g(EWg('N', '(/)'), gn0)
        return cc, cl, ty, B

    cc, cl, ty, B = base(ph, T0)
    mk = B.mk
    lnn, ww = ty['Lnn'], ty['W']
    nw = s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    cl.leaf('( # ` W )', 'NN0', nw)
    R = B.run()
    N1 = NFL('1o')
    ex = {STMT(GT(Y10)): gotocl(w, ph, mk['tv'], Y10, B.ex[LAB(Y10)]), 'A. m e. %s ( TMfl ` m ) = 1o' % N1: A8.ht_nfl(w, ph, '1o'), SSS(N1): B.ss(N1)}
    B.call(R, 'tm2lbrt', {'A': Z2, 'C': 'TMfl', 'E': Y5, 'Q': GT(Y10), 'N': N1}, ex, [])
    # the extraction's post words
    z0 = z0_in_sty(w, ph)
    ritp = s([s([s([lnn, cc['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (ph, Z0, STY))], 'jca',
                '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (ph, Z0, STY)), w.inst('exitp')], 'syl',
             '( %s -> %s )' % (ph, tsub_text(split_imp(stmt('exitp'))[1], {'G': 'N', 'Z': Z0})))
    rin = s([ritp], 'simp1d', '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (ph, RIT))
    mrn, usedw, tblt, hit2 = sq_comps(w, ph, cl, lnn, cc['N e. NN0'], ww, z0, RIT, rin)
    ritn = s([rin, w.inst('elfznn0')], 'syl', '( %s -> %s e. NN0 )' % (ph, RIT))
    cl.leaf(RIT, 'NN0', ritn)
    ritle = s([rin, w.inst('elfzle2')], 'syl', '( %s -> %s <_ ( # ` W ) )' % (ph, RIT))
    wrestw = s([ww, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word NN0 )' % (ph, WREST))
    wrd0 = B.gam['(/)']
    g6 = B.g(D6V3, enclg(w, ph, WREST, wrestw, '(/)', wrd0))
    g5 = B.g(ACCW3, accw_g(w, ph, TBL, tblt, 'L', cl.mem('L', 'NN0')))
    g7 = B.g(D7V3, ewg_(w, ph, MR, mrn, EWg('N', '(/)'), B.gam[EWg('N', '(/)')]))
    g4 = B.g(D4V3, enclg(w, ph, USED, usedw, ENCL('Q', '(/)'), B.gam[ENCL('Q', '(/)')]))
    B.call(R, 'tmiexfb', {'K': '6', 'J': '3', 'I': '0', "I'": '5', 'I"': '1', 'I0': '2', 'K0': '7', 'J0': '4', 'L': 'L', 'G': 'N', 'W': 'W', 'B': "B'",
                          'X': '(/)', "X'": '(/)', 'Y': '(/)', 'P': PL('P', 8), 'E': Z3},
           {'L e. NN': lnn, 'W e. Word NN0': ww, WG('(/)'): wrd0}, [('6', D6V3, g6), ('5', ACCW3, g5), ('7', D7V3, g7), ('4', D4V3, g4)], pre=(N1, B.ss(N1)))
    XL = "( 1st ` %s )" % LEQD["X'"]
    xle = s([s([cc[EQ("X'")]], 'fveq2d', "( %s -> ( 1st ` X' ) = %s )" % (ph, XL))], 'eqcomd', "( %s -> %s = ( 1st ` X' ) )" % (ph, XL))
    V1 = 'if ( %s = %s , (/) , 1o )' % (XL, INR)
    V2 = "if ( ( 1st ` X' ) = %s , (/) , 1o )" % INR
    veq = s([s([xle], 'eqeq1d', "( %s -> ( %s = %s <-> ( 1st ` X' ) = %s ) )" % (ph, XL, INR, INR))], 'ifbid', '( %s -> %s = %s )' % (ph, V1, V2))
    t0, C0, D0, n0 = cls_to(w, ph, (R.tri, R.C0, R.cur, R.n), V1, V2, veq)
    rn, n0b = w.rewrite(n0, {LEQD["X'"]: ("X'", s([cc[EQ("X'")]], 'eqcomd', "( %s -> %s = X' )" % (ph, LEQD["X'"])))}, ph)
    t0, C0, D0, n0 = hrrw(w, ph, t0, C0, D0, n0, neq=rn)
    assert n0 == '( 1 + %s )' % CEX, '\n%s\n%s' % (n0, '( 1 + %s )' % CEX)
    D3 = triple_D(D0)
    assert D0 == CLN(Z3, NFL(V2), D3), D0
    S3 = R.S
    # the extraction's value and bounds (under ph)
    xv, IFX, j0 = ext_value(w, ph, cc, ty, lnn, ww)
    exb = s([s([s([s([lnn, cc['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % ph), s([ww, cc["B' e. NN0"]], 'jca', "( %s -> ( W e. Word NN0 /\\ B' e. NN0 ) )" % ph)], 'jca',
                  "( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ B' e. NN0 ) ) )" % ph), s([cc[RALB('W', "B'")], rin], 'jca',
                  "( %s -> ( %s /\\ %s e. ( 0 ... ( # ` W ) ) ) )" % (ph, RALB('W', "B'"), RIT))], 'jca',
               "( %s -> ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ B' e. NN0 ) ) /\\ ( %s /\\ %s e. ( 0 ... ( # ` W ) ) ) ) )" % (ph, RALB('W', "B'"), RIT)),
             w.inst('t12exbnd')], 'syl', '( %s -> %s )' % (ph, tsub_text(C_EXB, {'B': "B'", 'I': RIT})))
    ralu = s([s([exb], 'simpld', '( %s -> ( %s /\\ ( # ` %s ) <_ %s ) )' % (ph, RALB(USED, "B'"), USED, RIT))], 'simpld', '( %s -> %s )' % (ph, RALB(USED, "B'")))
    ulen = s([s([exb], 'simpld', '( %s -> ( %s /\\ ( # ` %s ) <_ %s ) )' % (ph, RALB(USED, "B'"), USED, RIT))], 'simprd', '( %s -> ( # ` %s ) <_ %s )' % (ph, USED, RIT))
    E1R = "( 1 + ( B' x. %s ) )" % RIT
    mlt = s([s([exb], 'simprd', '( %s -> ( %s < ( 2 ^ %s ) /\\ ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( %s x. ( B\' + 1 ) ) + 1 ) ) ) )' % (ph, MR, E1R, TBL, RIT))], 'simpld',
            '( %s -> %s < ( 2 ^ %s ) )' % (ph, MR, E1R))
    tbl_ = s([s([exb], 'simprd', '( %s -> ( %s < ( 2 ^ %s ) /\\ ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( %s x. ( B\' + 1 ) ) + 1 ) ) ) )' % (ph, MR, E1R, TBL, RIT))], 'simprd',
             '( %s -> ( # ` ( L encTblAsc %s ) ) <_ ( L x. ( ( %s x. ( B\' + 1 ) ) + 1 ) ) )' % (ph, TBL, RIT))
    # m < 2 ^ N'
    bm = mul_le2(w, ph, cl, "B'", RIT, '( # ` W )', ritle)
    npe = cc[NPEQ]
    ele = linarith(w, ph, [bm, npe, cl.ge0("B'")], "%s <_ N'" % E1R, closure=cl, products=True)
    eu = s([s([s([cl.mem(E1R, 'NN0')], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, E1R)), s([cc["N' e. NN0"]], 'nn0zd', "( %s -> N' e. ZZ )" % ph), ele], '3jca',
              "( %s -> ( %s e. ZZ /\\ N' e. ZZ /\\ %s <_ N' ) )" % (ph, E1R, E1R)), w.inst('eluz2')], 'sylibr', "( %s -> N' e. ( ZZ>= ` %s ) )" % (ph, E1R))
    pe = s([closed(w, ph, '2re', '2 e. RR'), closed(w, ph, '1le2', '1 <_ 2'), eu, w.inst('leexp2a')], 'syl3anc', "( %s -> ( 2 ^ %s ) <_ ( 2 ^ N' ) )" % (ph, E1R))
    for e_ in (E1R, "N'", 'U', "B'"):
        cl.atom('( 2 ^ %s )' % e_)
        cl.leaf('( 2 ^ %s )' % e_, 'NN0', s([closed(w, ph, '2nn0', '2 e. NN0'), cl.mem(e_, 'NN0'), w.inst('nn0expcl')], 'syl2anc', '( %s -> ( 2 ^ %s ) e. NN0 )' % (ph, e_)))
    mltn = linarith(w, ph, [mlt, pe], "%s < ( 2 ^ N' )" % MR, closure=cl)
    # # used < 2 ^ B' : # used <_ RIT <_ # W <_ 2 ^ U < 2 ^ B'
    pub = s([s([closed(w, ph, '2re', '2 e. RR'), s([cc['U e. NN0']], 'nn0zd', '( %s -> U e. ZZ )' % ph), s([cc["B' e. NN0"]], 'nn0zd', "( %s -> B' e. ZZ )" % ph)], '3jca',
              "( %s -> ( 2 e. RR /\\ U e. ZZ /\\ B' e. ZZ ) )" % ph), s([closed(w, ph, '1lt2', '1 < 2'), cc["U < B'"]], 'jca', "( %s -> ( 1 < 2 /\\ U < B' ) )" % ph),
             w.inst('ltexp2a')], 'syl2anc', "( %s -> ( 2 ^ U ) < ( 2 ^ B' ) )" % ph)
    ulb = linarith(w, ph, [ulen, ritle, cc["( # ` W ) <_ ( 2 ^ U )"], pub], "( # ` %s ) < ( 2 ^ B' )" % USED, closure=cl)
    uleW = linarith(w, ph, [ulen, ritle], '( # ` %s ) <_ ( # ` W )' % USED, closure=cl)
    # the word lengths of the new stacks
    LU = '( # ` ( encList ` %s ) )' % USED
    lu = s([usedw, cc["B' e. NN0"], ralu, w.inst('tm2lenclen')], 'syl3anc', "( %s -> %s <_ ( ( ( # ` %s ) x. ( B' + 1 ) ) + 1 ) )" % (ph, LU, USED))
    cl.leaf(LU, 'NN0', s([s([usedw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, USED)), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LU)))
    mu = s([s([cl.mem('( # ` %s )' % USED, 'RR'), cl.mem('( # ` W )', 'RR'), s([cl.mem("( B' + 1 )", 'RR'), cl.ge0("( B' + 1 )")], 'jca', "( %s -> ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) )" % ph)],
              '3jca', "( %s -> ( ( # ` %s ) e. RR /\\ ( # ` W ) e. RR /\\ ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) ) )" % (ph, USED)), uleW], 'jca',
           "( %s -> ( ( ( # ` %s ) e. RR /\\ ( # ` W ) e. RR /\\ ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) ) /\\ ( # ` %s ) <_ ( # ` W ) ) )" % (ph, USED, USED))
    muL = s([mu, w.inst('lemul1a')], 'syl', "( %s -> ( ( # ` %s ) x. ( B' + 1 ) ) <_ ( ( # ` W ) x. ( B' + 1 ) ) )" % (ph, USED))
    luW = linarith(w, ph, [lu, muL, cc["( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) <_ W'"]], "%s <_ W'" % LU, closure=cl)
    # the table word
    LT_ = '( # ` ( L encTblAsc %s ) )' % TBL
    cl.leaf(LT_, 'NN0', s([tblw(w, ph, TBL, tblt, 'L', cl.mem('L', 'NN0')), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LT_)))
    rb = s([s([cl.mem(RIT, 'RR'), cl.mem('( # ` W )', 'RR'), s([cl.mem("( B' + 1 )", 'RR'), cl.ge0("( B' + 1 )")], 'jca', "( %s -> ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) )" % ph)],
              '3jca', "( %s -> ( %s e. RR /\\ ( # ` W ) e. RR /\\ ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) ) )" % (ph, RIT)), ritle], 'jca',
           "( %s -> ( ( %s e. RR /\\ ( # ` W ) e. RR /\\ ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) ) /\\ %s <_ ( # ` W ) ) )" % (ph, RIT, RIT))
    rbL = s([rb, w.inst('lemul1a')], 'syl', "( %s -> ( %s x. ( B' + 1 ) ) <_ ( ( # ` W ) x. ( B' + 1 ) ) )" % (ph, RIT))
    inner = linarith(w, ph, [rbL], "( ( %s x. ( B' + 1 ) ) + 1 ) <_ ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 )" % RIT, closure=cl)
    lm = mul_le2(w, ph, cl, 'L', "( ( %s x. ( B' + 1 ) ) + 1 )" % RIT, "( ( ( # ` W ) x. ( B' + 1 ) ) + 1 )", inner)
    LA = '( # ` %s )' % ACCW3
    la = s([tblw(w, ph, TBL, tblt, 'L', cl.mem('L', 'NN0')), s([closed(w, ph, 'gamma0', "0 e. Gamma'")], 's1cld', "( %s -> <\" 0 \"> e. Word Gamma' )" % ph), w.inst('ccatlen')], 'syl2anc',
           '( %s -> %s = ( %s + ( # ` <" 0 "> ) ) )' % (ph, LA, LT_))
    s0l = s([s([], 's1len', '( # ` <" 0 "> ) = 1')], 'a1i', '( %s -> ( # ` <" 0 "> ) = 1 )' % ph)
    cl.leaf(LA, 'NN0', s([g5, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LA)))
    cl.leaf('( # ` <" 0 "> )', 'NN0', s([s([s([], 's1len', '( # ` <" 0 "> ) = 1'), s([], '1nn0', '1 e. NN0')], 'eqeltri', '( # ` <" 0 "> ) e. NN0')], 'a1i', '( %s -> ( # ` <" 0 "> ) e. NN0 )' % ph))
    laW = linarith(w, ph, [la, s0l, tbl_, lm, cc["( ( L x. ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'"]], "%s <_ W'" % LA, closure=cl)
    # the rest of the pool
    LR = '( # ` ( encList ` %s ) )' % WREST
    nwz = s([nw, w.inst('nn0fz0')], 'sylib', '( %s -> ( # ` W ) e. ( 0 ... ( # ` W ) ) )' % ph)
    rnw = s([ww, rin, nwz, w.inst('swrdrn3')], 'syl3anc', '( %s -> ran %s = ( W " ( %s ..^ ( # ` W ) ) ) )' % (ph, WREST, RIT))
    rss = s([rnw, s([s([], 'imassrn', '( W " ( %s ..^ ( # ` W ) ) ) C_ ran W' % RIT)], 'a1i', '( %s -> ( W " ( %s ..^ ( # ` W ) ) ) C_ ran W )' % (ph, RIT))], 'eqsstrd',
            '( %s -> ran %s C_ ran W )' % (ph, WREST))
    ralr = s([rss, cc[RALB('W', "B'")], w.inst('ssralv')], 'sylc', '( %s -> %s )' % (ph, RALB(WREST, "B'")))
    lr = s([wrestw, cc["B' e. NN0"], ralr, w.inst('tm2lenclen')], 'syl3anc', "( %s -> %s <_ ( ( ( # ` %s ) x. ( B' + 1 ) ) + 1 ) )" % (ph, LR, WREST))
    swl = s([ww, rin, nwz, w.inst('swrdlen')], 'syl3anc', '( %s -> ( # ` %s ) = ( ( # ` W ) - %s ) )' % (ph, WREST, RIT))
    cl.leaf('( # ` %s )' % WREST, 'NN0', s([wrestw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph, WREST)))
    cl.leaf(LR, 'NN0', s([s([wrestw, w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (ph, WREST)), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LR)))
    swle = linarith(w, ph, [swl, cl.ge0(RIT)], '( # ` %s ) <_ ( # ` W )' % WREST, closure=cl)
    rw_ = s([s([cl.mem('( # ` %s )' % WREST, 'RR'), cl.mem('( # ` W )', 'RR'), s([cl.mem("( B' + 1 )", 'RR'), cl.ge0("( B' + 1 )")], 'jca', "( %s -> ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) )" % ph)],
               '3jca', "( %s -> ( ( # ` %s ) e. RR /\\ ( # ` W ) e. RR /\\ ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) ) )" % (ph, WREST)), swle], 'jca',
            "( %s -> ( ( ( # ` %s ) e. RR /\\ ( # ` W ) e. RR /\\ ( ( B' + 1 ) e. RR /\\ 0 <_ ( B' + 1 ) ) ) /\\ ( # ` %s ) <_ ( # ` W ) ) )" % (ph, WREST, WREST))
    rwL = s([rw_, w.inst('lemul1a')], 'syl', "( %s -> ( ( # ` %s ) x. ( B' + 1 ) ) <_ ( ( # ` W ) x. ( B' + 1 ) ) )" % (ph, WREST))
    lrW = linarith(w, ph, [lr, rwL, cc["( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) <_ W'"]], "%s <_ W'" % LR, closure=cl)
    # the extraction cost
    cl.leaf('( TMB ` ( ( ( 3 x. ( # ` W ) ) x. B\' ) + ( ( 5 x. B\' ) + 5 ) ) )', 'NN0', tmbn(w, ph, "( ( ( 3 x. ( # ` W ) ) x. B' ) + ( ( 5 x. B' ) + 5 ) )", cl.mem("( ( ( 3 x. ( # ` W ) ) x. B' ) + ( ( 5 x. B' ) + 5 ) )", 'NN0')))
    exyn = cl.mem(EXY, 'NN0')
    cl.leaf(EXY, 'NN0', exyn)
    cex25 = mul_le2(w, ph, cl, '( %s + 1 )' % E2, '( ; 2 5 x. %s )' % EXY, "( ; 2 5 x. W' )", linarith(w, ph, [cc["%s <_ W'" % EXY]], "( ; 2 5 x. %s ) <_ ( ; 2 5 x. W' )" % EXY, closure=cl))
    # the search value, common part
    sv, rhs = search_value(w, ph, cc, cl)
    nlt = not_lt(w, ph, cl, 'U', 'I', cc['U <_ I'])
    nj = s([cc["( 1st ` J ) =/= %s" % INR]], 'neneqd', "( %s -> -. ( 1st ` J ) = %s )" % (ph, INR))
    sv2, rhs2 = reduce_if(w, ph, sv, rhs, [nlt, nj])
    CST3 = "( ( C' + %s ) + %s )" % (S2, E2)
    assert rhs2 == "if ( ( 1st ` X' ) = %s , <. %s , %s >. , <. %s , %s >. )" % (INR, INR, CST3, IFQ, CST4), rhs2
    # ---- the two cases
    outs = []
    for some in (False, True):
        cond = "( 1st ` X' ) = %s" % INR if not some else "-. ( 1st ` X' ) = %s" % INR
        Tc = (T0, cond)
        pc = cj(Tc)
        L_ = lambda st_: lift_from(w, ph, pc, st_)
        cx = Ctx(w, pc, Tc)
        cst = cx[cond]
        if not some:
            # the flag class is NFL( (/) ) ; failAll from Z3 at the stacks D3
            V0 = '(/)'
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2, V0, s([cst], 'iftrued', '( %s -> %s = (/) )' % (pc, V2)))
            exf = {STKD(D3): L_(S3.memb)}
            for k_, v_ in B.ex.items():
                exf[k_] = None
            exf = {STKD(D3): L_(S3.memb), LAB(Z3): L_(B.ex[LAB(Z3)]), LAB(Y6): L_(B.ex[LAB(Y6)]),
                   'TMIfal T M ( P ` ; 1 2 ) E': L_(B.ex['TMIfal T M ( P ` ; 1 2 ) E']),
                   BR('X', FAL0).replace('( M ` A )', '( M ` %s )' % Z3).replace('X', Y6, 1).replace('( Q ` 0 )', Y9): None}
            key = '( M ` %s ) = %s' % (Z3, BRANCH('TMfl', GT(Y6), GT(Y9)))
            exf[key] = L_(B.ex[key])
            exf = {k_: v_ for k_, v_ in exf.items() if v_ is not None}
            t2, cc2 = inst(w, pc, 'tmisrfl', {'A': Z3, 'X': Y6, 'Q': PL('P', 12), 'D': D3, 'E': 'E'}, Bld(w, pc, cx, exf))
            C2, D2, n2 = triple_parts(cc2)
            assert C2 == Dc, (C2, Dc)
            svt = s([L_(sv2), s([cst], 'iftrued', '( %s -> %s = <. %s , %s >. )' % (pc, rhs2, INR, CST3))], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (pc, SE, INR, CST3))
            ie = out_init(w, pc, svt, (INR, s([], 'eqidd', '( %s -> %s = %s )' % (pc, INR, INR))), CST3, COMMA1, None, False)
            t2, _, D2b, _ = hrrw(w, pc, t2, C2, D2, n2, deq=clneq(w, pc, 'E', S, ie, INIT('1', COMMA1), INIT('1', OUTS)))
            assert D2b == POST
            t = hrseq(w, pc, mk['phm'], tc, t2, Cc, Dc, POST, nc, n2)
            n = '( %s + %s )' % (nc, n2)
            # the bound
            cst2 = s([s([svt], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (pc, SE, INR, CST3)),
                      s([s([s([], 'fvex', '%s e. _V' % INR)], 'a1i', '( %s -> %s e. _V )' % (pc, INR)), s([s([], 'ovex', '%s e. _V' % CST3)], 'a1i', '( %s -> %s e. _V )' % (pc, CST3)), w.inst('op2nd')],
                        'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pc, INR, CST3, CST3))], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (pc, SE, CST3))
            clx = Closure(w, pc, {x: ('NN0', cx['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N', "B'", "N'", "U'", "W'", 'B', 'H', "Z'")})
            for x in ('Z', 'Y'):
                clx.leaf(x, 'NN0', s([cx['%s e. NN' % x]], 'nnnn0d', '( %s -> %s e. NN0 )' % (pc, x)))
            tyx = stage_typing(w, pc, cx, clx)
            tyx.update(some_typing(w, pc, cx, clx, tyx))
            clx.leaf('( # ` W )', 'NN0', L_(nw))
            hy = [cx["Z' <_ %s" % PRE3], cx["U' <_ W'"], cx["8 <_ U'"], cx["( B' + 2 ) <_ U'"], cx["( N' + 2 ) <_ U'"], cx["B <_ B'"], cx["H <_ B'"],
                  cx["( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )"], L_(luW), L_(laW), L_(lrW), L_(cex25)]
            for x_ in (EXY, LU, LA, LR):
                clx.leaf(x_, 'NN0', L_(cl.mem(x_, 'NN0')))
            atoms = {}
            for t_, tn_, b_, bn_, tlt_ in (('X', tyx['X'], "B'", cx["B' e. NN0"], cx[LT2('X', "B'")]), ('O', cx['O e. NN0'], 'H', cx['H e. NN0'], cx[LT2('O', 'H')]),
                                           ('Z', tyx['zn0'], 'B', cx['B e. NN0'], cx[LT2('Z')]), ("J'", tyx["J'"], "B'", cx["B' e. NN0"], cx[LT2("J'", "B'")]),
                                           ('L', tyx['L'], "B'", cx["B' e. NN0"], cx[LT2('L', "B'")]), (MR, L_(mrn), "N'", cx["N' e. NN0"], L_(mltn)),
                                           ('N', cx['N e. NN0'], 'H', cx['H e. NN0'], cx[LT2('N', 'H')])):
                atoms['( encNatGam ` %s )' % t_] = numatom(w, pc, clx, t_, tn_, b_, bn_, tlt_)
            atoms['( encList ` Q )'] = (s([tyx['Q'], w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` Q ) e. Word Gamma' )" % pc), None)
            atoms['( encList ` %s )' % USED] = (s([L_(usedw), w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pc, USED)), None)
            atoms['( encList ` %s )' % WREST] = (s([L_(wrestw), w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` %s ) e. Word Gamma' )" % (pc, WREST)), None)
            atoms[ACCW3] = (L_(g5), None)
            lf = []
            for k in N8:
                v = S3.vals[k][0]
                lenfacts(w, pc, clx, v, atoms, lf)
                e = s([L_(S3.vals[k][1])], 'fveq2d', '( %s -> ( # ` ( %s ` %s ) ) = ( # ` %s ) )' % (pc, D3, k, v))
                clx.leaf('( # ` ( %s ` %s ) )' % (D3, k), 'NN0', s([e, clx.mem('( # ` %s )' % v, 'NN0')], 'eqeltrd', '( %s -> ( # ` ( %s ` %s ) ) e. NN0 )' % (pc, D3, k)))
                lf.append(e)
            hy += lf
            bud = s([s([s([s([cx["U' e. NN0"], cx["W' e. NN0"]], 'jca', "( %s -> ( U' e. NN0 /\\ W' e. NN0 ) )" % pc),
                           s([cx["U' <_ W'"], cx["8 <_ U'"]], 'jca', "( %s -> ( U' <_ W' /\\ 8 <_ U' ) )" % pc)], 'jca',
                          "( %s -> ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) )" % pc),
                        s([s([tyx["C'"], tyx['J2']], 'jca', "( %s -> ( C' e. NN0 /\\ %s e. NN0 ) )" % (pc, S2)), s([tyx['E2'], closed(w, pc, '0nn0', '0 e. NN0')], 'jca', '( %s -> ( %s e. NN0 /\\ 0 e. NN0 ) )' % (pc, E2))], 'jca',
                          "( %s -> ( ( C' e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ 0 e. NN0 ) ) )" % (pc, S2, E2))], 'jca',
                       "( %s -> ( ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) /\\ ( ( C' e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ 0 e. NN0 ) ) ) )" % (pc, S2, E2)),
                     w.inst('t12bud')], 'syl', '( %s -> %s )' % (pc, tsub_text('%s <_ %s' % (BUDL, BUDR), {'U': "U'", 'V': "W'", 'C': "C'", 'S': S2, 'E': E2, 'W': '0'})))
            hy.append(bud)
            TOT2 = "( ( %s + 1 ) x. ( ; ; 3 0 0 x. W' ) )" % CST3
            te = s([s([cst2], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( %s + 1 ) )' % (pc, SE, CST3))], 'oveq1d', '( %s -> %s = %s )' % (pc, TOT, TOT2))
            for m_ in ("( C' x. U' )", "( %s x. U' )" % S2, "( %s x. W' )" % E2, "( C' x. W' )", "( %s x. W' )" % S2):
                hy.append(clx.ge0(m_))
            hy += [clx.ge0(x) for x in ("C'", S2, E2, "Z'")]
            BND2 = "( %s - Z' )" % TOT2
            le = linarith(w, pc, hy, '%s <_ %s' % (n, BND2), closure=clx, products=True)
            zle = linarith(w, pc, hy, "Z' <_ %s" % TOT2, closure=clx, products=True)
            bn2 = s([zle, s([cx["Z' e. NN0"], clx.mem(TOT2, 'NN0'), w.inst('nn0sub')], 'syl2anc', "( %s -> ( Z' <_ %s <-> %s e. NN0 ) )" % (pc, TOT2, BND2))], 'mpbid', '( %s -> %s e. NN0 )' % (pc, BND2))
            t = hrle(w, pc, mk['phm'], t, Cc, POST, n, BND2, bn2, le)
            beq = s([te], 'oveq1d', "( %s -> %s = %s )" % (pc, "( %s - Z' )" % TOT, BND2))
            t, _, _, _ = hrrw(w, pc, t, Cc, POST, BND2, neq=s([beq], 'eqcomd', "( %s -> %s = %s )" % (pc, BND2, "( %s - Z' )" % TOT)))
        else:
            # the flag class is NFL( 1o ) ; the candidate is ( m_R , used_R )
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2, '1o', s([cst], 'iffalsed', '( %s -> %s = 1o )' % (pc, V2)))
            xv_ = L_(xv)
            # HIT = 1o
            pn_ = '( %s /\\ -. %s = 1o )' % (pc, HIT)
            ifi = s([s([], 'simpr', '( %s -> -. %s = 1o )' % (pn_, HIT))], 'iffalsed', '( %s -> %s = %s )' % (pn_, IFX, INR))
            xinr = s([s([xv_], 'adantr', "( %s -> ( 1st ` X' ) = %s )" % (pn_, IFX)), ifi], 'eqtrd', "( %s -> ( 1st ` X' ) = %s )" % (pn_, INR))
            hit1 = s([s([xinr, cst], 'mtand', '( %s -> -. -. %s = 1o )' % (pc, HIT))], 'notnotrd', '( %s -> %s = 1o )' % (pc, HIT))
            xinl = s([xv_, s([hit1], 'iftrued', '( %s -> %s = ( inl ` <. %s , %s >. ) )' % (pc, IFX, MR, USED))], 'eqtrd', "( %s -> ( 1st ` X' ) = ( inl ` <. %s , %s >. ) )" % (pc, MR, USED))
            opv = s([], 'opex', '<. %s , %s >. e. _V' % (MR, USED))
            x2 = s([s([xinl], 'fveq2d', "( %s -> ( 2nd ` ( 1st ` X' ) ) = ( 2nd ` ( inl ` <. %s , %s >. ) ) )" % (pc, MR, USED)),
                    s([s([opv], 'alginl2', '( 2nd ` ( inl ` <. %s , %s >. ) ) = <. %s , %s >.' % (MR, USED, MR, USED))], 'a1i', '( %s -> ( 2nd ` ( inl ` <. %s , %s >. ) ) = <. %s , %s >. )' % (pc, MR, USED, MR, USED))],
                   'eqtrd', "( %s -> ( 2nd ` ( 1st ` X' ) ) = <. %s , %s >. )" % (pc, MR, USED))
            fm = s([cx[EQ('F')], s([x2], 'fveq2d', "( %s -> ( 1st ` ( 2nd ` ( 1st ` X' ) ) ) = ( 1st ` <. %s , %s >. ) )" % (pc, MR, USED)),
                    s([s([s([], 'fvex', '%s e. _V' % MR), s([], 'fvex', '%s e. _V' % USED)], 'op1st', '( 1st ` <. %s , %s >. ) = %s' % (MR, USED, MR))], 'a1i', '( %s -> ( 1st ` <. %s , %s >. ) = %s )' % (pc, MR, USED, MR))],
                   '3eqtrd', '( %s -> F = %s )' % (pc, MR))
            au = s([cx[EQ('A')], s([x2], 'fveq2d', "( %s -> ( 2nd ` ( 2nd ` ( 1st ` X' ) ) ) = ( 2nd ` <. %s , %s >. ) )" % (pc, MR, USED)),
                    s([s([s([], 'fvex', '%s e. _V' % MR), s([], 'fvex', '%s e. _V' % USED)], 'op2nd', '( 2nd ` <. %s , %s >. ) = %s' % (MR, USED, USED))], 'a1i', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pc, MR, USED, USED))],
                   '3eqtrd', '( %s -> A = %s )' % (pc, USED))
            mf = s([fm], 'eqcomd', '( %s -> %s = F )' % (pc, MR))
            ua = s([au], 'eqcomd', '( %s -> %s = A )' % (pc, USED))
            clx = Closure(w, pc, {x: ('NN0', cx['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N', "B'", "N'", "U'", "W'", 'B', 'H', "Z'")})
            clx.leaf('( # ` W )', 'NN0', L_(nw))
            for x_ in (EXY, RIT, '( # ` %s )' % USED, MR):
                clx.leaf(x_, 'NN0', L_(cl.mem(x_, 'NN0')))
            an_ = s([au, L_(usedw)], 'eqeltrd', '( %s -> A e. Word NN0 )' % pc)
            fn_ = s([fm, L_(mrn)], 'eqeltrd', '( %s -> F e. NN0 )' % pc)
            clx.leaf('F', 'NN0', fn_)
            clx.leaf('( # ` A )', 'NN0', s([an_, w.inst('lencl')], 'syl', '( %s -> ( # ` A ) e. NN0 )' % pc))
            rna = s([au], 'rneqd', '( %s -> ran A = ran %s )' % (pc, USED))
            rala = s([s([rna], 'raleqdv', "( %s -> ( %s <-> %s ) )" % (pc, RALB('A', "B'"), RALB(USED, "B'"))), L_(ralu)], 'mpbird', '( %s -> %s )' % (pc, RALB('A', "B'")))
            lae = s([au], 'fveq2d', '( %s -> ( # ` A ) = ( # ` %s ) )' % (pc, USED))
            alt = s([lae, L_(ulb)], 'eqbrtrd', "( %s -> ( # ` A ) < ( 2 ^ B' ) )" % pc)
            aleW = s([lae, L_(uleW)], 'eqbrtrd', '( %s -> ( # ` A ) <_ ( # ` W ) )' % pc)
            flt = s([fm, L_(mltn)], 'eqbrtrd', "( %s -> F < ( 2 ^ N' ) )" % pc)
            bpn = linarith(w, pc, [cx[NPEQ], clx.ge0("( B' x. ( # ` W ) )")], "B' <_ N'", closure=clx, products=True)
            f1 = s([fm, s([cx[POS1], w.inst('nnge1')], 'syl', '( %s -> 1 <_ %s )' % (pc, MR))], 'eqbrtrd', '( %s -> 1 <_ F )' % pc)
            pa = '( %s /\\ p e. ran A )' % pc
            ain = s([s([], 'simpr', '( %s -> p e. ran A )' % pa), s([rna], 'adantr', '( %s -> ran A = ran %s )' % (pa, USED))], 'eleqtrd', '( %s -> p e. ran %s )' % (pa, USED))
            pos2p = cbv_a(w, pc, cx[POS2], None, '2 <_ a', '2 <_ p', 'a', 'ran %s' % USED) if False else None
            # POS2 with the bound variable p (the antecedent mentions a)
            bi_ = s([s([s([], 'breq2', '( a = p -> ( 2 <_ a <-> 2 <_ p ) )')], 'cbvralvw', '( A. a e. ran %s 2 <_ a <-> A. p e. ran %s 2 <_ p )' % (USED, USED))], 'a1i',
                    '( %s -> ( A. a e. ran %s 2 <_ a <-> A. p e. ran %s 2 <_ p ) )' % (pc, USED, USED))
            pos2p = s([cx[POS2], bi_], 'mpbid', '( %s -> A. p e. ran %s 2 <_ p )' % (pc, USED))
            pu = '( %s /\\ p e. ran %s )' % (pc, USED)
            a2u = s([pos2p], 'r19.21bi', '( %s -> 2 <_ p )' % pu)
            a2 = s([s([], 'simpl', '( %s -> %s )' % (pa, pc)), ain, a2u], 'syl2anc', '( %s -> 2 <_ p )' % pa)
            arn = s([s([an_, w.inst('wrdf')], 'syl', '( %s -> A : ( 0 ..^ ( # ` A ) ) --> NN0 )' % pc), w.inst('frn')], 'syl', '( %s -> ran A C_ NN0 )' % pc)
            an0 = s([s([arn], 'adantr', '( %s -> ran A C_ NN0 )' % pa), s([], 'simpr', '( %s -> p e. ran A )' % pa)], 'sseldd', '( %s -> p e. NN0 )' % pa)
            cla = Closure(w, pa, {'p': ('NN0', an0)})
            a1 = linarith(w, pa, [a2], '1 <_ p', closure=cla)
            ral1p = s([a1], 'ralrimiva', '( %s -> A. p e. ran A 1 <_ p )' % pc)
            bi2_ = s([s([s([], 'breq2', '( p = a -> ( 1 <_ p <-> 1 <_ a ) )')], 'cbvralvw', '( A. p e. ran A 1 <_ p <-> A. a e. ran A 1 <_ a )')], 'a1i',
                     '( %s -> ( A. p e. ran A 1 <_ p <-> A. a e. ran A 1 <_ a ) )' % pc)
            ral1 = s([ral1p, bi2_], 'mpbid', '( %s -> A. a e. ran A 1 <_ a )' % pc)
            # the units at A
            lm1 = s([s([clx.mem('( # ` A )', 'RR'), clx.mem('( # ` W )', 'RR'), s([clx.mem("B'", 'RR'), clx.ge0("B'")], 'jca', "( %s -> ( B' e. RR /\\ 0 <_ B' ) )" % pc)], '3jca',
                      "( %s -> ( ( # ` A ) e. RR /\\ ( # ` W ) e. RR /\\ ( B' e. RR /\\ 0 <_ B' ) ) )" % pc), aleW], 'jca',
                   "( %s -> ( ( ( # ` A ) e. RR /\\ ( # ` W ) e. RR /\\ ( B' e. RR /\\ 0 <_ B' ) ) /\\ ( # ` A ) <_ ( # ` W ) ) )" % pc)
            abm = s([lm1, w.inst('lemul1a')], 'syl', "( %s -> ( ( # ` A ) x. B' ) <_ ( ( # ` W ) x. B' ) )" % pc)
            VXW = VX4.replace('( # ` A )', '( # ` W )')
            vxle = linarith(w, pc, [abm], '( ( 4 x. %s ) + 6 ) <_ ( ( 4 x. %s ) + 6 )' % (VX4, VXW), closure=clx, products=True)
            tbm = s([clx.mem('( ( 4 x. %s ) + 6 )' % VX4, 'NN0'), clx.mem('( ( 4 x. %s ) + 6 )' % VXW, 'NN0'), vxle, w.inst('tmbmono')], 'syl3anc',
                    '( %s -> ( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ ( TMB ` ( ( 4 x. %s ) + 6 ) ) )' % (pc, VX4, VXW))
            for e_ in (VX4, VXW):
                clx.leaf('( TMB ` ( ( 4 x. %s ) + 6 ) )' % e_, 'NN0', tmbn(w, pc, '( ( 4 x. %s ) + 6 )' % e_, clx.mem('( ( 4 x. %s ) + 6 )' % e_, 'NN0')))
            hb5 = linarith(w, pc, [tbm, cx[HB5W]], HB5, closure=clx)
            am2 = s([s([clx.mem('( ( # ` A ) + 2 )', 'RR'), clx.mem('( ( # ` W ) + 2 )', 'RR'), s([clx.mem("U'", 'RR'), clx.ge0("U'")], 'jca', "( %s -> ( U' e. RR /\\ 0 <_ U' ) )" % pc)], '3jca',
                      "( %s -> ( ( ( # ` A ) + 2 ) e. RR /\\ ( ( # ` W ) + 2 ) e. RR /\\ ( U' e. RR /\\ 0 <_ U' ) ) )" % pc), linarith(w, pc, [aleW], '( ( # ` A ) + 2 ) <_ ( ( # ` W ) + 2 )', closure=clx)],
                   'jca', "( %s -> ( ( ( ( # ` A ) + 2 ) e. RR /\\ ( ( # ` W ) + 2 ) e. RR /\\ ( U' e. RR /\\ 0 <_ U' ) ) /\\ ( ( # ` A ) + 2 ) <_ ( ( # ` W ) + 2 ) ) )" % pc)
            am2L = s([am2, w.inst('lemul1a')], 'syl', "( %s -> ( ( ( # ` A ) + 2 ) x. U' ) <_ ( ( ( # ` W ) + 2 ) x. U' ) )" % pc)
            a2u_ = linarith(w, pc, [am2L, cx["( ( ( # ` W ) + 2 ) x. U' ) <_ W'"]], "( ( ( # ` A ) + 2 ) x. U' ) <_ W'", closure=clx, products=True)
            lea = s([s([au], 'fveq2d', '( %s -> ( encList ` A ) = ( encList ` %s ) )' % (pc, USED))], 'fveq2d', '( %s -> ( # ` ( encList ` A ) ) = %s )' % (pc, LU))
            leaW = s([lea, L_(luW)], 'eqbrtrd', "( %s -> ( # ` ( encList ` A ) ) <_ W' )" % pc)
            # the cost so far at the verify stage
            tyx = stage_typing(w, pc, cx, clx)
            tyx.update(some_typing(w, pc, cx, clx, tyx))
            vcl_ = s([fn_, an_, w.inst('verifycl')], 'syl2anc', '( %s -> ( F Verify A ) e. ( 2o X. NN0 ) )' % pc)
            vcl2_ = s([cx[EQ("Q'")], vcl_], 'eqeltrd', "( %s -> Q' e. ( 2o X. NN0 ) )" % pc)
            clx.leaf(W2, 'NN0', s([vcl2_, w.inst('xp2nd')], 'syl', "( %s -> ( 2nd ` Q' ) e. NN0 )" % pc))
            Z4 = "( ( Z' + 1 ) + %s )" % CEX
            clx.leaf(CEX, 'NN0', L_(cl.mem(CEX, 'NN0')))
            z4n = clx.mem(Z4, 'NN0')
            z4le = linarith(w, pc, [cx["Z' <_ %s" % PRE3], L_(cex25)], '%s <_ %s' % (Z4, PRE4), closure=clx, products=True)
            # the stacks D3 : its eight values in tmisrc4's form
            vals = {}
            for k in N8:
                vals[k] = L_(S3.vals[k][1])
            v7 = s([vals['7'], s([s([mf], 'fveq2d', '( %s -> ( encNatGam ` %s ) = ( encNatGam ` F ) )' % (pc, MR))], 'oveq1d', '( %s -> %s = %s )' % (pc, D7V3, D7V))], 'eqtrd',
                   '( %s -> ( %s ` 7 ) = %s )' % (pc, D3, D7V))
            v4 = s([vals['4'], s([s([ua], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` A ) )' % (pc, USED))], 'oveq1d', '( %s -> %s = %s )' % (pc, D4V3, D4V))], 'eqtrd',
                   '( %s -> ( %s ` 4 ) = %s )' % (pc, D3, D4V))
            ex4 = {STKD(D3): L_(S3.memb), "( 1st ` X' ) =/= %s" % INR: s([cst], 'neqned', "( %s -> ( 1st ` X' ) =/= %s )" % (pc, INR)),
                   DEQ(7, D7V).replace('( D ` 7 )', '( %s ` 7 )' % D3): v7, DEQ(4, D4V).replace('( D ` 4 )', '( %s ` 4 )' % D3): v4,
                   'A e. Word NN0': an_, 'F e. NN0': fn_, RALB('A', "B'"): rala, LT2('( # ` A )', "B'"): alt, LT2('F', "N'"): flt, "B' <_ N'": bpn, '1 <_ F': f1,
                   'A. a e. ran A 1 <_ a': ral1, "( # ` %s ) <_ W'" % ACCW3: L_(laW), "( # ` %s ) <_ W'" % D6V3: L_(lrW), "( # ` ( encList ` A ) ) <_ W'": leaW,
                   HB5: hb5, "( ( ( # ` A ) + 2 ) x. U' ) <_ W'": a2u_, WG(ACCW3): L_(g5), WG(D6V3): L_(g6), '%s e. NN0' % Z4: z4n, '%s <_ %s' % (Z4, PRE4): z4le}
            for k in ('0', '1', '2', '3', '5', '6'):
                ex4['( %s ` %s ) = %s' % (D3, k, S3.vals[k][0])] = vals[k]
            t4, cc4 = inst(w, pc, 'tmisrc4', {'D': D3, "Y'": ACCW3, 'X"': D6V3, "Z'": Z4}, Bld(w, pc, cx, ex4))
            C4, D4, n4 = triple_parts(cc4)
            assert C4 == Dc, '\n%s\n%s' % (C4, Dc)
            assert D4 == POST
            t = hrseq(w, pc, mk['phm'], tc, t4, Cc, Dc, POST, nc, n4)
            n = '( %s + %s )' % (nc, n4)
            # ( 1 + CEX ) + ( TOT - Z4 ) = TOT - Z'
            cst2 = s([s([L_(sv2)], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (pc, SE, rhs2)), s([cst], 'iffalsed', '( %s -> %s = <. %s , %s >. )' % (pc, rhs2, IFQ, CST4))], 'eqtrd',
                    '( %s -> ( 2nd ` %s ) = <. %s , %s >. )' % (pc, SE, IFQ, CST4)) if False else None
            svs = s([L_(sv2), s([cst], 'iffalsed', '( %s -> %s = <. %s , %s >. )' % (pc, rhs2, IFQ, CST4))], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (pc, SE, IFQ, CST4))
            cst2 = s([s([svs], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (pc, SE, IFQ, CST4)),
                      s([s([s([], 'ifex', '%s e. _V' % IFQ)], 'a1i', '( %s -> %s e. _V )' % (pc, IFQ)), s([s([], 'ovex', '%s e. _V' % CST4)], 'a1i', '( %s -> %s e. _V )' % (pc, CST4)), w.inst('op2nd')],
                        'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pc, IFQ, CST4, CST4))], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (pc, SE, CST4))
            clx.leaf('( 2nd ` %s )' % SE, 'NN0', s([cst2, clx.mem(CST4, 'NN0')], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, SE)))
            clx.leaf(TOT, 'NN0', clx.mem(TOT, 'NN0'))
            ceq = lineq(w, pc, n, "( %s - Z' )" % TOT, closure=clx)
            t, _, _, _ = hrrw(w, pc, t, Cc, POST, n, neq=ceq)
        outs.append(s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, CONCL_SRC3)))
    st = s(outs, 'pm2.61d' if False else 'pm2.61dan_dummy', '') if False else None
    # ( ph -> ( cond -> C ) ) , ( ph -> ( -. cond -> C ) ) : pm2.61d
    st = s([outs[0], outs[1]], 'pm2.61d', '( %s -> %s )' % (ph, CONCL_SRC3))
    finish(w, st, lab)
    return w.run()




# ------------------------------------------------------------ t12expos: the extraction keeps m positive and the used entries at least 2 (statement; proof below)
ST_EXPOS = ('( ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ A. a e. ran W 2 <_ a ) ) /\\ I e. ( 0 ... ( # ` W ) ) ) -> '
            '( %s e. NN /\\ A. a e. ran %s 2 <_ a ) )' % (MI('I'), UI('I')))
T12EXTRA['t12expos'] = ST_EXPOS

# ------------------------------------------------------------ tmisrc2: the scan stage
SCAN = LEQD['J']
KSC = '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % SCAN
PSC = '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % SCAN
X1 = '( 1 + X )'
HB3 = "( TMB ` ( ( ( ( ; 4 8 x. ( ( # ` Q ) + 1 ) ) x. ( B' + B' ) ) + ( 4 x. ( # ` Q ) ) ) + ; ; 1 0 2 ) ) <_ U'"
CSN = "( ( %s + 1 ) x. ( TMB ` ( ( ( ( ; 4 8 x. ( ( # ` Q ) + 1 ) ) x. ( B' + B' ) ) + ( 4 x. ( # ` Q ) ) ) + ; ; 1 0 2 ) ) )" % S2
P2U = '( 2 ^ U )'
EXXU = "( ( ( 3 x. %s ) x. B' ) + ( ( 5 x. B' ) + 5 ) )" % P2U
NPU = "( ( B' x. ( %s + 1 ) ) + 1 )" % P2U
VXU = VX4.replace('( # ` A )', P2U).replace(" N' )", ' %s )' % NPU)
assert VXU == "( ( ( ( ( 2 x. ( %s + 1 ) ) x. B' ) + ( 3 x. B' ) ) + %s ) + 8 )" % (P2U, NPU), VXU
LSQ = '( ( L + 1 ) ^ 2 )'
UP1 = ("( ( %s + 2 ) x. U' ) <_ W'" % P2U, "( ( %s x. ( %s + 2 ) ) x. U' ) <_ W'" % (LSQ, P2U), "( TMB ` %s ) <_ U'" % EXXU)
UP2 = ("( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ U'" % VXU, "( %s + 2 ) <_ U'" % NPU, "( TMB ` %s ) <_ U'" % NPU)
UP3 = (HB3, "( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )", "%s < ( 2 ^ B' )" % X1)
UN2S = ("( B' + 2 ) <_ U'", ("B <_ B'", "H <_ B'"), ("U < B'", "( TMB ` B' ) <_ U'"))
UN3S = ((LT2('X', "B'"), LT2('L', "B'"), LT2('N', "B'")), (LT2('Z'), LT2('O', 'H'), LT2('N', 'H')), (LT2('Z', "B'"), LT2('O', "B'")))
STK2 = (STKD('D'), ((DEQ(0, D0V), DEQ(1, EWg('Z', EWg('X', '(/)')))), (DEQ(2, EWg('1', '(/)')), DEQ(3, D3V))),
        ((DEQ(4, ENCL('Q', '(/)')), DEQ(5, '(/)')), (DEQ(6, '(/)'), DEQ(7, EWg('N', '(/)')))))
CSTH2 = ("Z' e. NN0", "Z' <_ %s" % PRE2)
TREE_SRC2 = ((T_PHM7, FS.pred()),
             ((SC_TY, LEQT), (('U <_ I', UP1, UP2), (UP3, UN1, UN2S), UN3S),
              ((('B e. NN0', 'H e. NN0', '1 <_ L'), "B' e. NN0"), STK2, CSTH2)))
CONCL_SRC2 = TRI(CLN(Z1, NFL('1o'), 'D'), POST, "( %s - Z' )" % TOT)
add12('tmisrc2', TREE_SRC2, CONCL_SRC2)


def lemul1(w, ph, cl, A, B_, C_, ab):
    """( ph -> ( A x. C ) <_ ( B x. C ) ) from ab : A <_ B , 0 <_ C (~ lemul1a )"""
    s = w.s
    j = s([s([cl.mem(A, 'RR'), cl.mem(B_, 'RR'), s([cl.mem(C_, 'RR'), cl.ge0(C_)], 'jca', '( %s -> ( %s e. RR /\\ 0 <_ %s ) )' % (ph, C_, C_))], '3jca',
             '( %s -> ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) )' % (ph, A, B_, C_, C_)), ab], 'jca',
          '( %s -> ( ( %s e. RR /\\ %s e. RR /\\ ( %s e. RR /\\ 0 <_ %s ) ) /\\ %s <_ %s ) )' % (ph, A, B_, C_, C_, A, B_))
    return s([j, w.inst('lemul1a')], 'syl', '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, A, C_, B_, C_))


def cbv_a(w, ph, st, frm, bodyv, bodyw, v, dom):
    """( ph -> A. a e. dom bodyw ) from st : ( ph -> A. v e. dom bodyv ) , renaming the bound variable v to a"""
    s = w.s
    cg = s([], 'id', '( %s = a -> %s = a )' % (v, v))
    sub, new = w.wcongr(bodyv, {v: 'a'}, '%s = a' % v, {v: cg})
    assert new == bodyw, (new, bodyw)
    bi = s([sub], 'cbvralvw', '( A. %s e. %s %s <-> A. a e. %s %s )' % (v, dom, bodyv, dom, bodyw))
    return s([st, s([bi], 'a1i', '( %s -> ( A. %s e. %s %s <-> A. a e. %s %s ) )' % (ph, v, dom, bodyv, dom, bodyw))], 'mpbid', '( %s -> A. a e. %s %s )' % (ph, dom, bodyw))


def tmisrc2():
    lab = 'tmisrc2'
    T0 = numtree(TREE_SRC2)
    ph = cj(T0)
    w = W(lab, 'The scan stage of Lean\'s ` searchF ` at the machine (step 2 succeeded): from the first branch with the flag true, '
               '` scanF ` (~ tmiscfb , T11), then the extract stage (~ tmisrc3 ) or ` failAll ` (~ tmisrfl ) by whether the scan found '
               'a window; the pool\'s entries are primes below ` x ` (~ tmscsome , ~ poolalgval , ~ poolgomemi ) and there are at most '
               '` 2 ^ T ` of them (~ t12pglen , ~ divisorsoflen , ~ a5q ); the extraction keeps its numbers positive (~ t12expos ).')
    s = w.s

    def base(pc, Tc):
        cc = Ctx(w, pc, Tc)
        cl = Closure(w, pc, {x: ('NN0', cc['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N', "B'", "U'", "W'", 'B', 'H', "Z'")})
        for x in ('Z', 'Y'):
            cl.leaf(x, 'NN0', s([cc['%s e. NN' % x]], 'nnnn0d', '( %s -> %s e. NN0 )' % (pc, x)))
        ty = stage_typing(w, pc, cc, cl)
        wrd0 = closed(w, pc, 'wrd0', "(/) e. Word Gamma'")
        gq = enclg(w, pc, 'Q', ty['Q'], '(/)', wrd0)
        gn0 = ewg_(w, pc, 'N', cc['N e. NN0'], '(/)', wrd0)
        go = ewg_(w, pc, 'O', cc['O e. NN0'], '(/)', wrd0)
        g0 = ewg_(w, pc, 'X', ty['X'], EWg('O', '(/)'), go)
        gx0 = ewg_(w, pc, 'X', ty['X'], '(/)', wrd0)
        g1 = ewg_(w, pc, 'Z', ty['zn0'], EWg('X', '(/)'), gx0)
        g2 = ewg_(w, pc, '1', closed(w, pc, '1nn0', '1 e. NN0'), '(/)', wrd0)
        g3 = ewg_(w, pc, 'L', ty['L'], '(/)', wrd0)
        vals8 = {'0': (D0V, g0), '1': (EWg('Z', EWg('X', '(/)')), g1), '2': (EWg('1', '(/)'), g2), '3': (D3V, g3), '4': (ENCL('Q', '(/)'), gq), '5': ('(/)', wrd0),
                 '6': ('(/)', wrd0), '7': (EWg('N', '(/)'), gn0)}
        B = Src(w, pc, Tc, vals8)
        B.g('(/)', wrd0); B.g(ENCL('Q', '(/)'), gq); B.g(EWg('N', '(/)'), gn0)
        return cc, cl, ty, B

    cc, cl, ty, B = base(ph, T0)
    B.deep('srch', 3)                      # the scan fragment's own labels (its entry is ( ( ( P ` 7 ) ` 2 ) ` 0 ))
    mk = B.mk
    wrd0 = B.gam['(/)']
    lnn = s([s([ty['L'], cc['1 <_ L']], 'jca', '( %s -> ( L e. NN0 /\\ 1 <_ L ) )' % ph), w.inst('elnnnn0c')], 'sylibr', '( %s -> L e. NN )' % ph)
    # Q's entries (~ a5q ): primes at most z ; # Q = U
    h1 = s([cc['Z e. NN'], cc['G e. NN0'], cc['Y e. NN']], '3jca', '( %s -> ( Z e. NN /\\ G e. NN0 /\\ Y e. NN ) )' % ph)
    aq = s([h1, cc['U e. NN0'], cc[EQ('R')], cc[EQ('I')], cc[EQ('Q')], cc['U <_ I']], 'a5q',
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
    c2 = s([s([s([cpr, w.inst('prmuz2')], 'syl', '( %s -> c e. ( ZZ>= ` 2 ) )' % pq), w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ c e. ZZ /\\ 2 <_ c ) )' % pq)],
           'simp3d', '( %s -> 2 <_ c )' % pq)
    cz = s([s([s([cpr, w.inst('prmuz2')], 'syl', '( %s -> c e. ( ZZ>= ` 2 ) )' % pq), w.inst('eluz2')], 'sylib', '( %s -> ( 2 e. ZZ /\\ c e. ZZ /\\ 2 <_ c ) )' % pq)],
           'simp2d', '( %s -> c e. ZZ )' % pq)
    clq = Closure(w, pq, {})
    clq.leaf('c', 'ZZ', cz); clq.leaf('Z', 'NN0', lift_from(w, ph, pq, ty['zn0']))
    clq.atom("( 2 ^ B' )")
    clq.leaf("( 2 ^ B' )", 'NN0', lift_from(w, ph, pq, s([closed(w, ph, '2nn0', '2 e. NN0'), cc["B' e. NN0"], w.inst('nn0expcl')], 'syl2anc', "( %s -> ( 2 ^ B' ) e. NN0 )" % ph)))
    clt = linarith(w, pq, [cle, lift_from(w, ph, pq, cc[LT2('Z', "B'")])], "c < ( 2 ^ B' )", closure=clq)
    c1 = linarith(w, pq, [c2], '1 <_ c', closure=clq)
    ralq = cbv_a(w, ph, s([clt], 'ralrimiva', "( %s -> A. c e. ran Q c < ( 2 ^ B' ) )" % ph), None, "c < ( 2 ^ B' )", "a < ( 2 ^ B' )", 'c', 'ran Q')
    ralq1 = cbv_a(w, ph, s([c1], 'ralrimiva', '( %s -> A. c e. ran Q 1 <_ c )' % ph), None, '1 <_ c', '1 <_ a', 'c', 'ran Q')
    # the branch and the scan
    R = B.run()
    N1 = NFL('1o')
    ex = {STMT(GT(Y11)): gotocl(w, ph, mk['tv'], Y11, B.ex[LAB(Y11)]), 'A. m e. %s ( TMfl ` m ) = 1o' % N1: A8.ht_nfl(w, ph, '1o'), SSS(N1): B.ss(N1)}
    B.call(R, 'tm2lbrt', {'A': Z1, 'C': 'TMfl', 'E': Y4, 'Q': GT(Y11), 'N': N1}, ex, [])
    NONE = '( 1st ` %s ) = %s' % (SCAN, INR)
    IF2 = 'if ( %s , %s , %s )' % (NONE, EWg(X1, '(/)'), EWg(KSC, '(/)'))
    IF6 = 'if ( %s , (/) , %s )' % (NONE, ENCL(PSC, '(/)'))
    x1n = cl.mem(X1, 'NN0')
    gx1 = ewg_(w, ph, X1, x1n, '(/)', wrd0)
    # k' and the pool typing (from ~ scancl through ~ scandj needs the some case; use ~ scancl : J e. ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 and
    # the components of an ` inl ` ... instead take the words' typing by cases on NONE through ~ ifcld with a dummy in the none branch)
    # typing of the if-words: both branches are words
    pj = '( %s /\\ -. %s )' % (ph, NONE)
    Lj = lambda st_: lift_from(w, ph, pj, st_)
    jq1 = s([Lj(ty['Q']), Lj(ty['X'])], 'jca', '( %s -> ( Q e. Word NN0 /\\ X e. NN0 ) )' % pj)
    jq2 = s([jq1, Lj(ty['zn0'])], 'jca', '( %s -> ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % pj)
    jq3 = s([jq2, Lj(cc['O e. NN0'])], 'jca', '( %s -> ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % pj)
    jq4 = s([closed(w, pj, '1nn0', '1 e. NN0'), Lj(ty['X'])], 'jca', '( %s -> ( 1 e. NN0 /\\ X e. NN0 ) )' % pj)
    jn1 = s([jq3, jq4], 'jca', '( %s -> ( ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( 1 e. NN0 /\\ X e. NN0 ) ) )' % pj)
    jne_ = s([s([], 'simpr', '( %s -> -. %s )' % (pj, NONE))], 'neqned', '( %s -> ( 1st ` %s ) =/= %s )' % (pj, SCAN, INR))
    dj = s([s([jn1, jne_], 'jca', '( %s -> ( %s /\\ ( 1st ` %s ) =/= %s ) )' % (pj, concl(w, pj, jn1), SCAN, INR)), w.inst('scandj')], 'syl',
           '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (pj, KSC, PSC))
    kn_j = s([dj], 'simpld', '( %s -> %s e. NN0 )' % (pj, KSC))
    pw_j = s([dj], 'simprd', '( %s -> %s e. Word NN0 )' % (pj, PSC))
    # the if-words are words: by cases
    pt = '( %s /\\ %s )' % (ph, NONE)
    i2t = s([s([s([], 'simpr', '( %s -> %s )' % (pt, NONE))], 'iftrued', '( %s -> %s = %s )' % (pt, IF2, EWg(X1, '(/)'))), lift_from(w, ph, pt, gx1)], 'eqeltrd',
            "( %s -> %s e. Word Gamma' )" % (pt, IF2))
    i2f = s([s([s([], 'simpr', '( %s -> -. %s )' % (pj, NONE))], 'iffalsed', '( %s -> %s = %s )' % (pj, IF2, EWg(KSC, '(/)'))), ewg_(w, pj, KSC, kn_j, '(/)', closed(w, pj, 'wrd0', "(/) e. Word Gamma'"))],
            'eqeltrd', "( %s -> %s e. Word Gamma' )" % (pj, IF2))
    g2i = s([i2t, i2f], 'pm2.61dan', "( %s -> %s e. Word Gamma' )" % (ph, IF2))
    i6t = s([s([s([], 'simpr', '( %s -> %s )' % (pt, NONE))], 'iftrued', '( %s -> %s = (/) )' % (pt, IF6)), closed(w, pt, 'wrd0', "(/) e. Word Gamma'")], 'eqeltrd',
            "( %s -> %s e. Word Gamma' )" % (pt, IF6))
    i6f = s([s([s([], 'simpr', '( %s -> -. %s )' % (pj, NONE))], 'iffalsed', '( %s -> %s = %s )' % (pj, IF6, ENCL(PSC, '(/)'))), enclg(w, pj, PSC, pw_j, '(/)', closed(w, pj, 'wrd0', "(/) e. Word Gamma'"))],
            'eqeltrd', "( %s -> %s e. Word Gamma' )" % (pj, IF6))
    g6i = s([i6t, i6f], 'pm2.61dan', "( %s -> %s e. Word Gamma' )" % (ph, IF6))
    gz0 = ewg_(w, ph, 'Z', ty['zn0'], '(/)', wrd0)
    B.g(EWg('Z', '(/)'), gz0); B.g(IF2, g2i); B.g(IF6, g6i)
    B.call(R, 'tmiscfb', {'W': 'Q', 'F': 'X', 'Z': 'Z', 'O': 'O', 'G': '1', 'H': 'X', 'C': "B'", 'B': "B'", 'X': '(/)', "X'": '(/)', 'Y': '(/)', "Y'": '(/)', 'P': PL('P', 7), 'E': Z2},
           {'Q e. Word NN0': ty['Q'], 'X e. NN0': ty['X'], 'Z e. NN0': ty['zn0'], '1 e. NN0': closed(w, ph, '1nn0', '1 e. NN0'), RALB('Q', "B'"): ralq,
            'A. a e. ran Q 1 <_ a': ralq1, WG('(/)'): wrd0}, [('1', EWg('Z', '(/)'), gz0), ('2', IF2, g2i), ('6', IF6, g6i)], pre=(N1, B.ss(N1)))
    # the class and the cost in terms of J
    jsc = s([cc[EQ('J')]], 'eqcomd', '( %s -> %s = J )' % (ph, SCAN))
    V1s = 'if ( %s , (/) , 1o )' % NONE
    V2j = 'if ( ( 1st ` J ) = %s , (/) , 1o )' % INR
    veq = s([s([s([jsc], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (ph, SCAN))], 'eqeq1d', '( %s -> ( %s <-> ( 1st ` J ) = %s ) )' % (ph, NONE, INR))], 'ifbid',
            '( %s -> %s = %s )' % (ph, V1s, V2j))
    t0, C0, D0, n0 = cls_to(w, ph, (R.tri, R.C0, R.cur, R.n), V1s, V2j, veq)
    rn, n0b = w.rewrite(n0, {SCAN: ('J', jsc)}, ph)
    t0, C0, D0, n0 = hrrw(w, ph, t0, C0, D0, n0, neq=rn)
    assert n0 == '( 1 + %s )' % CSN, '\n%s\n%s' % (n0, '( 1 + %s )' % CSN)
    D2 = triple_D(D0)
    S2s = R.S
    # the search value, reduced by -. I < U
    sv, rhs = search_value(w, ph, cc, cl)
    nlt = not_lt(w, ph, cl, 'U', 'I', cc['U <_ I'])
    sv2, rhs2 = reduce_if(w, ph, sv, rhs, [nlt])
    CST2 = "( C' + %s )" % S2
    INNER3 = "if ( ( 1st ` X' ) = %s , <. %s , %s >. , <. %s , %s >. )" % (INR, INR, "( ( C' + %s ) + %s )" % (S2, E2), IFQ, CST4)
    assert rhs2 == 'if ( ( 1st ` J ) = %s , <. %s , %s >. , %s )' % (INR, INR, CST2, INNER3), rhs2
    outs = []
    for some in (False, True):
        cond = "( 1st ` J ) = %s" % INR if not some else "-. ( 1st ` J ) = %s" % INR
        Tc = (T0, cond)
        pc = cj(Tc)
        L_ = lambda st_: lift_from(w, ph, pc, st_)
        cx = Ctx(w, pc, Tc)
        cst = cx[cond]
        nsc = s([cst, s([L_(jsc)], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (pc, SCAN))], 'eqeq1d' if False else 'id', '') if False else None
        # NONE <-> cond
        nbi = s([s([L_(jsc)], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (pc, SCAN))], 'eqeq1d', '( %s -> ( %s <-> ( 1st ` J ) = %s ) )' % (pc, NONE, INR))
        clx = Closure(w, pc, {x: ('NN0', cx['%s e. NN0' % x]) for x in ('G', 'U', 'O', 'N', "B'", "U'", "W'", 'B', 'H', "Z'")})
        for x in ('Z', 'Y'):
            clx.leaf(x, 'NN0', s([cx['%s e. NN' % x]], 'nnnn0d', '( %s -> %s e. NN0 )' % (pc, x)))
        tyx = stage_typing(w, pc, cx, clx)
        if not some:
            ns = s([cst, nbi], 'mpbird', '( %s -> %s )' % (pc, NONE))
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2j, '(/)', s([cst], 'iftrued', '( %s -> %s = (/) )' % (pc, V2j)))
            e2 = s([ns], 'iftrued', '( %s -> %s = %s )' % (pc, IF2, EWg(X1, '(/)')))
            e6 = s([ns], 'iftrued', '( %s -> %s = (/) )' % (pc, IF6))
            rd, D2n = w.rewrite(D2, {IF2: (EWg(X1, '(/)'), e2), IF6: ('(/)', e6)}, pc)
            # the normal form: the stacks with 1 := EW( Z , (/) ) , 2 := EW( 1 + X , (/) ) , 6 := (/) (6 = ( D ` 6 ) already: drop the update)
            Bx = base(pc, Tc)[3]
            Sn = Bx.S0.upd('1', EWg('Z', '(/)'), L_(gz0)).upd('2', EWg(X1, '(/)'), L_(gx1))
            up6 = upidv(w, pc, Sn.D, '6', '(/)', Sn.vals['6'][1], Bx.mk['tv'], Sn.memb, Bx.mk['k']['6']['kd'])
            assert D2n == UP(Sn.D, '6', '(/)'), '\n%s\n%s' % (D2n, UP(Sn.D, '6', '(/)'))
            deq = s([rd, up6], 'eqtrd', '( %s -> %s = %s )' % (pc, D2, Sn.D))
            tc, Cc, Dc, nc = hrrw(w, pc, tc, Cc, Dc, nc, deq=clneq(w, pc, Z2, NFL('(/)'), deq, D2, Sn.D))
            exf = {STKD(Sn.D): Sn.memb, LAB(Z2): L_(B.ex[LAB(Z2)]), LAB(Y5): L_(B.ex[LAB(Y5)]), 'TMIfal T M ( P ` ; 1 3 ) E': L_(B.ex['TMIfal T M ( P ` ; 1 3 ) E'])}
            key = '( M ` %s ) = %s' % (Z2, BRANCH('TMfl', GT(Y5), GT(Y10)))
            exf[key] = L_(B.ex[key])
            t2, cc2 = inst(w, pc, 'tmisrfl', {'A': Z2, 'X': Y5, 'Q': PL('P', 13), 'D': Sn.D, 'E': 'E'}, Bld(w, pc, cx, exf))
            C2, D2c, n2 = triple_parts(cc2)
            assert C2 == Dc, (C2, Dc)
            svt = s([L_(sv2), s([cst], 'iftrued', '( %s -> %s = <. %s , %s >. )' % (pc, rhs2, INR, CST2))], 'eqtrd', '( %s -> %s = <. %s , %s >. )' % (pc, SE, INR, CST2))
            ie = out_init(w, pc, svt, (INR, s([], 'eqidd', '( %s -> %s = %s )' % (pc, INR, INR))), CST2, COMMA1, None, False)
            t2, _, D2b, _ = hrrw(w, pc, t2, C2, D2c, n2, deq=clneq(w, pc, 'E', S, ie, INIT('1', COMMA1), INIT('1', OUTS)))
            assert D2b == POST
            t = hrseq(w, pc, mk['phm'], tc, t2, Cc, Dc, POST, nc, n2)
            n = '( %s + %s )' % (nc, n2)
            cst2 = s([s([svt], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (pc, SE, INR, CST2)),
                      s([s([s([], 'fvex', '%s e. _V' % INR)], 'a1i', '( %s -> %s e. _V )' % (pc, INR)), s([s([], 'ovex', '%s e. _V' % CST2)], 'a1i', '( %s -> %s e. _V )' % (pc, CST2)), w.inst('op2nd')],
                        'syl2anc', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pc, INR, CST2, CST2))], 'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (pc, SE, CST2))
            # the lengths
            atoms = {}
            for t_, tn_, b_, bn_, tlt_ in (('X', tyx['X'], "B'", cx["B' e. NN0"], cx[LT2('X', "B'")]), ('O', cx['O e. NN0'], 'H', cx['H e. NN0'], cx[LT2('O', 'H')]),
                                           ('Z', tyx['zn0'], 'B', cx['B e. NN0'], cx[LT2('Z')]), (X1, clx.mem(X1, 'NN0'), "B'", cx["B' e. NN0"], cx["%s < ( 2 ^ B' )" % X1]),
                                           ('L', tyx['L'], "B'", cx["B' e. NN0"], cx[LT2('L', "B'")]), ('N', cx['N e. NN0'], 'H', cx['H e. NN0'], cx[LT2('N', 'H')])):
                atoms['( encNatGam ` %s )' % t_] = numatom(w, pc, clx, t_, tn_, b_, bn_, tlt_)
            atoms['( encList ` Q )'] = (s([tyx['Q'], w.inst('tm2lenccl')], 'syl', "( %s -> ( encList ` Q ) e. Word Gamma' )" % pc), None)
            lf = []
            for k in N8:
                v = Sn.vals[k][0]
                lenfacts(w, pc, clx, v, atoms, lf)
                e = s([Sn.vals[k][1]], 'fveq2d', '( %s -> ( # ` ( %s ` %s ) ) = ( # ` %s ) )' % (pc, Sn.D, k, v))
                clx.leaf('( # ` ( %s ` %s ) )' % (Sn.D, k), 'NN0', s([e, clx.mem('( # ` %s )' % v, 'NN0')], 'eqeltrd', '( %s -> ( # ` ( %s ` %s ) ) e. NN0 )' % (pc, Sn.D, k)))
                lf.append(e)
            TBS = "( TMB ` ( ( ( ( ; 4 8 x. ( ( # ` Q ) + 1 ) ) x. ( B' + B' ) ) + ( 4 x. ( # ` Q ) ) ) + ; ; 1 0 2 ) )"
            clx.leaf('( # ` Q )', 'NN0', s([tyx['Q'], w.inst('lencl')], 'syl', '( %s -> ( # ` Q ) e. NN0 )' % pc))
            clx.leaf(TBS, 'NN0', tmbn(w, pc, TBS[len('( TMB ` '):-2], clx.mem(TBS[len('( TMB ` '):-2], 'NN0')))
            csnle = mul_le2(w, pc, clx, '( %s + 1 )' % S2, TBS, "U'", cx[HB3])
            LB = "( ( ( C' + 1 ) x. U' ) + ( ; 5 0 x. W' ) )"
            leafle = linarith(w, pc, lf + [cx["( ( # ` ( encList ` Q ) ) + 1 ) <_ ( ( C' + 1 ) x. U' )"], cx["U' <_ W'"], cx["8 <_ U'"], cx["( B' + 2 ) <_ U'"], cx["B <_ B'"], cx["H <_ B'"]],
                             '%s <_ %s' % (n2, LB), closure=clx)
            bud = s([s([s([s([cx["U' e. NN0"], cx["W' e. NN0"]], 'jca', "( %s -> ( U' e. NN0 /\\ W' e. NN0 ) )" % pc),
                           s([cx["U' <_ W'"], cx["8 <_ U'"]], 'jca', "( %s -> ( U' <_ W' /\\ 8 <_ U' ) )" % pc)], 'jca',
                          "( %s -> ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) )" % pc),
                        s([s([tyx["C'"], tyx['J2']], 'jca', "( %s -> ( C' e. NN0 /\\ %s e. NN0 ) )" % (pc, S2)), s([closed(w, pc, '0nn0', '0 e. NN0'), closed(w, pc, '0nn0', '0 e. NN0')], 'jca', '( %s -> ( 0 e. NN0 /\\ 0 e. NN0 ) )' % pc)], 'jca',
                          "( %s -> ( ( C' e. NN0 /\\ %s e. NN0 ) /\\ ( 0 e. NN0 /\\ 0 e. NN0 ) ) )" % (pc, S2))], 'jca',
                       "( %s -> ( ( ( U' e. NN0 /\\ W' e. NN0 ) /\\ ( U' <_ W' /\\ 8 <_ U' ) ) /\\ ( ( C' e. NN0 /\\ %s e. NN0 ) /\\ ( 0 e. NN0 /\\ 0 e. NN0 ) ) ) )" % (pc, S2)),
                     w.inst('t12bud')], 'syl', '( %s -> %s )' % (pc, tsub_text('%s <_ %s' % (BUDL, BUDR), {'U': "U'", 'V': "W'", 'C': "C'", 'S': S2, 'E': '0', 'W': '0'})))
            TOT2 = "( ( %s + 1 ) x. ( ; ; 3 0 0 x. W' ) )" % CST2
            te = s([s([cst2], 'oveq1d', '( %s -> ( ( 2nd ` %s ) + 1 ) = ( %s + 1 ) )' % (pc, SE, CST2))], 'oveq1d', '( %s -> %s = %s )' % (pc, TOT, TOT2))
            BND2 = "( %s - Z' )" % TOT2
            fin_hy = [cx["Z' <_ %s" % PRE2], csnle, leafle, bud, cx["U' <_ W'"], cx["8 <_ U'"]] + [clx.ge0(x) for x in ("C'", S2, "Z'", "U'", "W'")]
            le = linarith(w, pc, fin_hy, '%s <_ %s' % (n, BND2), closure=clx, products=True)
            zle = linarith(w, pc, fin_hy, "Z' <_ %s" % TOT2, closure=clx, products=True)
            bn2 = s([zle, s([cx["Z' e. NN0"], clx.mem(TOT2, 'NN0'), w.inst('nn0sub')], 'syl2anc', "( %s -> ( Z' <_ %s <-> %s e. NN0 ) )" % (pc, TOT2, BND2))], 'mpbid', '( %s -> %s e. NN0 )' % (pc, BND2))
            t = hrle(w, pc, mk['phm'], t, Cc, POST, n, BND2, bn2, le)
            beq = s([te], 'oveq1d', "( %s -> %s = %s )" % (pc, "( %s - Z' )" % TOT, BND2))
            t, _, _, _ = hrrw(w, pc, t, Cc, POST, BND2, neq=s([beq], 'eqcomd', "( %s -> %s = %s )" % (pc, BND2, "( %s - Z' )" % TOT)))
        else:
            nns = s([cst, nbi], 'mtbird', '( %s -> -. %s )' % (pc, NONE))
            tc, Cc, Dc, nc = cls_to(w, pc, (L_(t0), C0, D0, n0), V2j, '1o', s([cst], 'iffalsed', '( %s -> %s = 1o )' % (pc, V2j)))
            tyx.update(some_typing(w, pc, cx, clx, tyx))
            lnnx = tyx['Lnn']
            # k' = J' , the pool = W
            kj = s([cx[EQ("J'")], s([s([s([L_(jsc)], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (pc, SCAN))], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` J ) ) )' % (pc, SCAN))],
                                    'fveq2d', "( %s -> %s = %s )" % (pc, KSC, LEQD["J'"]))], 'eqtr4d', "( %s -> J' = %s )" % (pc, KSC))
            pw = s([cx[EQ('W')], s([s([s([L_(jsc)], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` J ) )' % (pc, SCAN))], 'fveq2d', '( %s -> ( 2nd ` ( 1st ` %s ) ) = ( 2nd ` ( 1st ` J ) ) )' % (pc, SCAN))],
                                    'fveq2d', "( %s -> %s = %s )" % (pc, PSC, LEQD['W']))], 'eqtr4d', "( %s -> W = %s )" % (pc, PSC))
            e2 = s([s([nns], 'iffalsed', '( %s -> %s = %s )' % (pc, IF2, EWg(KSC, '(/)'))), s([s([s([kj], 'eqcomd', "( %s -> %s = J' )" % (pc, KSC))], 'fveq2d', "( %s -> ( encNatGam ` %s ) = ( encNatGam ` J' ) )" % (pc, KSC))], 'oveq1d',
                    '( %s -> %s = %s )' % (pc, EWg(KSC, '(/)'), EWg("J'", '(/)')))], 'eqtrd', '( %s -> %s = %s )' % (pc, IF2, EWg("J'", '(/)')))
            e6 = s([s([nns], 'iffalsed', '( %s -> %s = %s )' % (pc, IF6, ENCL(PSC, '(/)'))), s([s([s([pw], 'eqcomd', '( %s -> %s = W )' % (pc, PSC))], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` W ) )' % (pc, PSC))], 'oveq1d',
                    '( %s -> %s = %s )' % (pc, ENCL(PSC, '(/)'), ENCL('W', '(/)')))], 'eqtrd', '( %s -> %s = %s )' % (pc, IF6, ENCL('W', '(/)')))
            rd, D2s = w.rewrite(D2, {IF2: (EWg("J'", '(/)'), e2), IF6: (ENCL('W', '(/)'), e6)}, pc)
            Bx = base(pc, Tc)[3]
            g2j = ewg_(w, pc, "J'", tyx["J'"], '(/)', Bx.gam['(/)'])
            g6w = enclg(w, pc, 'W', tyx['W'], '(/)', Bx.gam['(/)'])
            Ss = Bx.S0.upd('1', EWg('Z', '(/)'), L_(gz0)).upd('2', EWg("J'", '(/)'), g2j).upd('6', ENCL('W', '(/)'), g6w)
            assert D2s == Ss.D, '\n%s\n%s' % (D2s, Ss.D)
            tc, Cc, Dc, nc = hrrw(w, pc, tc, Cc, Dc, nc, deq=clneq(w, pc, Z2, N1, rd, D2, Ss.D))
            # the pool: primes below x , at most 2 ^ U of them
            sq1 = s([tyx['Q'], s([tyx['X'], tyx['zn0'], cx['O e. NN0']], '3jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) )' % pc)], 'jca',
                     '( %s -> ( Q e. Word NN0 /\\ ( X e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) ) )' % pc)
            sq2 = s([s([closed(w, pc, '1nn0', '1 e. NN0'), tyx['X']], 'jca', '( %s -> ( 1 e. NN0 /\\ X e. NN0 ) )' % pc),
                     s([nns], 'neqned', '( %s -> ( 1st ` %s ) =/= %s )' % (pc, SCAN, INR))], 'jca',
                    '( %s -> ( ( 1 e. NN0 /\\ X e. NN0 ) /\\ ( 1st ` %s ) =/= %s ) )' % (pc, SCAN, INR))
            sq3 = s([sq1, sq2], 'jca', '( %s -> ( ( Q e. Word NN0 /\\ ( X e. NN0 /\\ Z e. NN0 /\\ O e. NN0 ) ) /\\ ( ( 1 e. NN0 /\\ X e. NN0 ) /\\ ( 1st ` %s ) =/= %s ) ) )' % (pc, SCAN, INR))
            sm = s([sq3, w.inst('tmscsome')], 'syl', '( %s -> %s )' % (pc, tsub_text(split_imp(stmt('tmscsome'))[1], {'W': 'Q', 'F': 'X', 'G': '1', 'H': 'X'})))
            smc = tsub_text(split_imp(stmt('tmscsome'))[1], {'W': 'Q', 'F': 'X', 'G': '1', 'H': 'X'})
            smt = parse_conj(smc)
            csm = Ctx(w, pc, smt, root=sm)
            klt = csm['%s < ( 1 + X )' % KSC]
            PAV = '( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` %s ) )' % KSC
            weq = csm['%s = %s' % (PSC, PAV)]
            jpk = s([kj, klt], 'eqbrtrd', "( %s -> J' < ( 1 + X ) )" % pc)
            clx.leaf(X1, 'NN0', clx.mem(X1, 'NN0'))
            clx.atom("( 2 ^ B' )")
            clx.leaf("( 2 ^ B' )", 'NN0', s([closed(w, pc, '2nn0', '2 e. NN0'), cx["B' e. NN0"], w.inst('nn0expcl')], 'syl2anc', "( %s -> ( 2 ^ B' ) e. NN0 )" % pc))
            jlt = linarith(w, pc, [jpk, cx["%s < ( 2 ^ B' )" % X1]], "J' < ( 2 ^ B' )", closure=clx)
            # W = ( 1st PoolGo(X,Z,J') ` DIVS )
            DIVS = '( 1st ` ( DivisorsOf ` Q ) )'
            PGJ = lambda s_: "( ( ( X PoolGo Z ) ` J' ) ` %s )" % s_
            pav = s([s([s([s([tyx['Q'], tyx['X']], 'jca', '( %s -> ( Q e. Word NN0 /\\ X e. NN0 ) )' % pc), tyx['zn0']], 'jca', '( %s -> ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % pc), tyx["J'"]], 'jca',
                       "( %s -> ( ( ( Q e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ J' e. NN0 ) )" % pc), w.inst('poolalgval')], 'syl',
                    "( %s -> ( ( ( Q PoolAlg X ) ` Z ) ` J' ) = <. ( 1st ` %s ) , ( ( 2nd ` ( DivisorsOf ` Q ) ) + ( 2nd ` %s ) ) >. )" % (pc, PGJ(DIVS), PGJ(DIVS)))
            CST_ = '( ( 2nd ` ( DivisorsOf ` Q ) ) + ( 2nd ` %s ) )' % PGJ(DIVS)
            p1v = s([s([pav], 'fveq2d', "( %s -> ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) = ( 1st ` <. ( 1st ` %s ) , %s >. ) )" % (pc, PGJ(DIVS), CST_)),
                     s([s([s([], 'fvex', '( 1st ` %s ) e. _V' % PGJ(DIVS)), s([], 'ovex', '%s e. _V' % CST_)], 'op1st', '( 1st ` <. ( 1st ` %s ) , %s >. ) = ( 1st ` %s )' % (PGJ(DIVS), CST_, PGJ(DIVS)))], 'a1i',
                       '( %s -> ( 1st ` <. ( 1st ` %s ) , %s >. ) = ( 1st ` %s ) )' % (pc, PGJ(DIVS), CST_, PGJ(DIVS)))], 'eqtrd',
                    "( %s -> ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) = ( 1st ` %s ) )" % (pc, PGJ(DIVS)))
            pavk = s([s([kj], 'fveq2d', "( %s -> ( ( ( Q PoolAlg X ) ` Z ) ` J' ) = ( ( ( Q PoolAlg X ) ` Z ) ` %s ) )" % (pc, KSC))], 'fveq2d',
                     "( %s -> ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) = %s )" % (pc, PAV))
            wpg = s([s([pw, weq], 'eqtrd', '( %s -> W = %s )' % (pc, PAV)), s([pavk], 'eqcomd', "( %s -> %s = ( 1st ` ( ( ( Q PoolAlg X ) ` Z ) ` J' ) ) )" % (pc, PAV)), p1v], '3eqtrd',
                    '( %s -> W = ( 1st ` %s ) )' % (pc, PGJ(DIVS)))
            dcl = s([s([tyx['Q'], w.inst('divisorsofcl')], 'syl', '( %s -> ( DivisorsOf ` Q ) e. ( Word NN0 X. NN0 ) )' % pc), w.inst('xp1st')], 'syl', '( %s -> %s e. Word NN0 )' % (pc, DIVS))
            xzj = s([s([tyx['X'], tyx['zn0']], 'jca', '( %s -> ( X e. NN0 /\\ Z e. NN0 ) )' % pc), tyx["J'"]], 'jca', "( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ J' e. NN0 ) )" % pc)
            # entries: p e. ran W -> p <_ X /\ p e. Prime
            pp = '( %s /\\ p e. ran W )' % pc
            wrn = s([s([tyx['W'], w.inst('wrdf')], 'syl', '( %s -> W : ( 0 ..^ ( # ` W ) ) --> NN0 )' % pc), w.inst('frn')], 'syl', '( %s -> ran W C_ NN0 )' % pc)
            pn0 = s([s([wrn], 'adantr', '( %s -> ran W C_ NN0 )' % pp), s([], 'simpr', '( %s -> p e. ran W )' % pp)], 'sseldd', '( %s -> p e. NN0 )' % pp)
            pin = s([s([], 'simpr', '( %s -> p e. ran W )' % pp), s([s([wpg], 'rneqd', '( %s -> ran W = ran ( 1st ` %s ) )' % (pc, PGJ(DIVS)))], 'adantr', '( %s -> ran W = ran ( 1st ` %s ) )' % (pp, PGJ(DIVS)))],
                    'eleqtrd', '( %s -> p e. ran ( 1st ` %s ) )' % (pp, PGJ(DIVS)))
            gmi = s([s([s([xzj], 'adantr', "( %s -> ( ( X e. NN0 /\\ Z e. NN0 ) /\\ J' e. NN0 ) )" % pp), s([s([dcl], 'adantr', '( %s -> %s e. Word NN0 )' % (pp, DIVS)), pn0], 'jca', '( %s -> ( %s e. Word NN0 /\\ p e. NN0 ) )' % (pp, DIVS))], 'jca',
                       "( %s -> ( ( ( X e. NN0 /\\ Z e. NN0 ) /\\ J' e. NN0 ) /\\ ( %s e. Word NN0 /\\ p e. NN0 ) ) )" % (pp, DIVS)), w.inst('poolgomemi')], 'syl',
                    "( %s -> ( p e. ran ( 1st ` %s ) <-> E. d e. ran %s ( ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) ) ) )" % (pp, PGJ(DIVS), DIVS))
            exd = s([pin, gmi], 'mpbid', "( %s -> E. d e. ran %s ( ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) ) )" % (pp, DIVS))
            BODYD = "( ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) /\\ ( Z < p /\\ p e. Prime ) )"
            pd = '( %s /\\ ( d e. ran %s /\\ %s ) )' % (pp, DIVS, BODYD)
            bd = s([s([], 'simpr', '( %s -> ( d e. ran %s /\\ %s ) )' % (pd, DIVS, BODYD))], 'simprd', '( %s -> %s )' % (pd, BODYD))
            pxp = s([s([s([bd], 'simpld', "( %s -> ( ( ( d x. J' ) + 1 ) = p /\\ p <_ X ) )" % pd)], 'simprd', '( %s -> p <_ X )' % pd),
                     s([s([bd], 'simprd', '( %s -> ( Z < p /\\ p e. Prime ) )' % pd)], 'simprd', '( %s -> p e. Prime )' % pd)], 'jca', '( %s -> ( p <_ X /\\ p e. Prime ) )' % pd)
            pf = s([exd, pxp], 'rexlimddv', '( %s -> ( p <_ X /\\ p e. Prime ) )' % pp)
            clp = Closure(w, pp, {'p': ('NN0', pn0), 'X': ('NN0', s([tyx['X']], 'adantr', '( %s -> X e. NN0 )' % pp))})
            clp.atom("( 2 ^ B' )"); clp.leaf("( 2 ^ B' )", 'NN0', s([clx.mem("( 2 ^ B' )", 'NN0')], 'adantr', "( %s -> ( 2 ^ B' ) e. NN0 )" % pp))
            plt = linarith(w, pp, [s([pf], 'simpld', '( %s -> p <_ X )' % pp), s([cx[LT2('X', "B'")]], 'adantr', "( %s -> X < ( 2 ^ B' ) )" % pp)], "p < ( 2 ^ B' )", closure=clp)
            p2 = s([s([s([s([pf], 'simprd', '( %s -> p e. Prime )' % pp), w.inst('prmuz2')], 'syl', '( %s -> p e. ( ZZ>= ` 2 ) )' % pp), w.inst('eluz2')], 'sylib',
                     '( %s -> ( 2 e. ZZ /\\ p e. ZZ /\\ 2 <_ p ) )' % pp)], 'simp3d', '( %s -> 2 <_ p )' % pp)
            ralw = cbv_a(w, pc, s([plt], 'ralrimiva', "( %s -> A. p e. ran W p < ( 2 ^ B' ) )" % pc), None, "p < ( 2 ^ B' )", "a < ( 2 ^ B' )", 'p', 'ran W')
            ralw2 = cbv_a(w, pc, s([p2], 'ralrimiva', '( %s -> A. p e. ran W 2 <_ p )' % pc), None, '2 <_ p', '2 <_ a', 'p', 'ran W')
            # # W <_ 2 ^ U
            pgl = s([dcl, s([tyx['X'], tyx['zn0'], tyx["J'"]], '3jca', "( %s -> ( X e. NN0 /\\ Z e. NN0 /\\ J' e. NN0 ) )" % pc), w.inst('t12pglen')], 'sylc',
                    '( %s -> ( # ` ( 1st ` %s ) ) <_ ( # ` %s ) )' % (pc, PGJ(DIVS), DIVS))
            dl = s([tyx['Q'], w.inst('divisorsoflen')], 'syl', '( %s -> ( # ` %s ) = ( 2 ^ ( # ` Q ) ) )' % (pc, DIVS))
            dl2 = s([dl, s([L_(nq)], 'oveq2d', '( %s -> ( 2 ^ ( # ` Q ) ) = ( 2 ^ U ) )' % pc)], 'eqtrd', '( %s -> ( # ` %s ) = ( 2 ^ U ) )' % (pc, DIVS))
            wle = s([s([s([wpg], 'fveq2d', '( %s -> ( # ` W ) = ( # ` ( 1st ` %s ) ) )' % (pc, PGJ(DIVS))), pgl], 'eqbrtrd', '( %s -> ( # ` W ) <_ ( # ` %s ) )' % (pc, DIVS)), dl2], 'breqtrd',
                    '( %s -> ( # ` W ) <_ ( 2 ^ U ) )' % pc)
            nw = s([tyx['W'], w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % pc)
            clx.leaf('( # ` W )', 'NN0', nw)
            clx.atom(P2U); clx.leaf(P2U, 'NN0', s([closed(w, pc, '2nn0', '2 e. NN0'), cx['U e. NN0'], w.inst('nn0expcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (pc, P2U)))
            # the positivity of the extraction
            z0 = z0_in_sty(w, pc)
            ritp = s([s([s([lnnx, cx['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % pc), s([tyx['W'], z0], 'jca', '( %s -> ( W e. Word NN0 /\\ %s e. %s ) )' % (pc, Z0, STY))], 'jca',
                        '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ %s e. %s ) ) )' % (pc, Z0, STY)), w.inst('exitp')], 'syl',
                     '( %s -> %s )' % (pc, tsub_text(split_imp(stmt('exitp'))[1], {'G': 'N', 'Z': Z0})))
            rin = s([ritp], 'simp1d', '( %s -> %s e. ( 0 ... ( # ` W ) ) )' % (pc, RIT))
            pos = s([s([s([s([lnnx, cx['N e. NN0']], 'jca', '( %s -> ( L e. NN /\\ N e. NN0 ) )' % pc), s([tyx['W'], ralw2], 'jca', '( %s -> ( W e. Word NN0 /\\ A. a e. ran W 2 <_ a ) )' % pc)], 'jca',
                        '( %s -> ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ A. a e. ran W 2 <_ a ) ) )' % pc), rin], 'jca',
                     '( %s -> ( ( ( L e. NN /\\ N e. NN0 ) /\\ ( W e. Word NN0 /\\ A. a e. ran W 2 <_ a ) ) /\\ %s e. ( 0 ... ( # ` W ) ) ) )' % (pc, RIT)), w.inst('t12expos')], 'syl',
                    '( %s -> ( %s /\\ %s ) )' % (pc, POS1, POS2))
            # the units at # W from the units at 2 ^ U
            NP = "( ( B' x. ( ( # ` W ) + 1 ) ) + 1 )"
            w2u = linarith(w, pc, [wle], '( ( # ` W ) + 1 ) <_ ( %s + 1 )' % P2U, closure=clx)
            npb = mul_le2(w, pc, clx, "B'", '( ( # ` W ) + 1 )', '( %s + 1 )' % P2U, w2u)
            nple = linarith(w, pc, [npb], '%s <_ %s' % (NP, NPU), closure=clx)
            np2 = linarith(w, pc, [nple, cx["( %s + 2 ) <_ U'" % NPU]], "( %s + 2 ) <_ U'" % NP, closure=clx)
            tbnp = s([s([clx.mem(NP, 'NN0'), clx.mem(NPU, 'NN0'), nple, w.inst('tmbmono')], 'syl3anc', '( %s -> ( TMB ` %s ) <_ ( TMB ` %s ) )' % (pc, NP, NPU)), cx["( TMB ` %s ) <_ U'" % NPU]],
                    'letrd' if False else 'id', '') if False else None
            for e_ in (NP, NPU, EXXU, "( ( ( 3 x. ( # ` W ) ) x. B' ) + ( ( 5 x. B' ) + 5 ) )"):
                clx.leaf('( TMB ` %s )' % e_, 'NN0', tmbn(w, pc, e_, clx.mem(e_, 'NN0')))
            tbnp = linarith(w, pc, [s([clx.mem(NP, 'NN0'), clx.mem(NPU, 'NN0'), nple, w.inst('tmbmono')], 'syl3anc', '( %s -> ( TMB ` %s ) <_ ( TMB ` %s ) )' % (pc, NP, NPU)), cx["( TMB ` %s ) <_ U'" % NPU]],
                           "( TMB ` %s ) <_ U'" % NP, closure=clx)
            w2 = linarith(w, pc, [wle], '( ( # ` W ) + 2 ) <_ ( %s + 2 )' % P2U, closure=clx)
            wu = lemul1(w, pc, clx, '( ( # ` W ) + 2 )', '( %s + 2 )' % P2U, "U'", w2)
            hw2 = linarith(w, pc, [wu, cx["( ( %s + 2 ) x. U' ) <_ W'" % P2U]], "( ( ( # ` W ) + 2 ) x. U' ) <_ W'", closure=clx)
            # # W ( B' + 1 ) + 1 <_ ( # W + 2 )( B' + 2 ) <_ ( # W + 2 ) U' <_ W'
            wb2 = mul_le2(w, pc, clx, '( ( # ` W ) + 2 )', "( B' + 2 )", "U'", cx["( B' + 2 ) <_ U'"])
            hpv = linarith(w, pc, [wb2, hw2, clx.ge0('( # ` W )'), clx.ge0("B'")], "( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) <_ W'", closure=clx, products=True)
            # L ( # W ( B' + 1 ) + 1 ) + 1 <_ ( L + 1 )( # W + 2 )( B' + 2 ) <_ ( L + 1 )^2 ( 2^U + 2 ) U' <_ W'
            clx.atom(LSQ)
            clx.leaf(LSQ, 'NN0', s([clx.mem('( L + 1 )', 'NN0'), closed(w, pc, '2nn0', '2 e. NN0')], 'nn0expcld', '( %s -> %s e. NN0 )' % (pc, LSQ)))
            sq = s([clx.mem('( L + 1 )', 'CC'), w.inst('sqval')], 'syl', '( %s -> %s = ( ( L + 1 ) x. ( L + 1 ) ) )' % (pc, LSQ))
            l1sq = linarith(w, pc, [sq, mul_le2(w, pc, clx, '( L + 1 )', '1', '( L + 1 )', linarith(w, pc, [clx.ge0('L')], '1 <_ ( L + 1 )', closure=clx))], '( L + 1 ) <_ %s' % LSQ, closure=clx, products=True)
            PRD = "( ( ( # ` W ) + 2 ) x. ( B' + 2 ) )"
            PRDU = "( ( %s + 2 ) x. U' )" % P2U
            prdle = linarith(w, pc, [wb2, wu], '%s <_ %s' % (PRD, PRDU), closure=clx, products=True)
            l1p = mul_le2(w, pc, clx, '( L + 1 )', PRD, PRDU, prdle)
            l2p = lemul1(w, pc, clx, '( L + 1 )', LSQ, PRDU, l1sq)
            hlpv = linarith(w, pc, [l1p, l2p, cx["( ( %s x. ( %s + 2 ) ) x. U' ) <_ W'" % (LSQ, P2U)], clx.ge0('L'), clx.ge0('( # ` W )'), clx.ge0("B'")],
                            "( ( L x. ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'", closure=clx, products=True)
            # HB5W from the primitive, VX monotone in # W and N'
            VXW = VX4.replace('( # ` A )', '( # ` W )')
            wb = lemul1(w, pc, clx, '( # ` W )', P2U, "B'", wle)
            vxw = linarith(w, pc, [wb, nple], '( ( 4 x. %s ) + 6 ) <_ ( ( 4 x. %s ) + 6 )' % (VXW.replace(" N' )", ' %s )' % NP), VXU), closure=clx, products=True)
            for e_ in (VXW.replace(" N' )", ' %s )' % NP), VXU):
                clx.leaf('( TMB ` ( ( 4 x. %s ) + 6 ) )' % e_, 'NN0', tmbn(w, pc, '( ( 4 x. %s ) + 6 )' % e_, clx.mem('( ( 4 x. %s ) + 6 )' % e_, 'NN0')))
            tbv = s([clx.mem('( ( 4 x. %s ) + 6 )' % VXW.replace(" N' )", ' %s )' % NP), 'NN0'), clx.mem('( ( 4 x. %s ) + 6 )' % VXU, 'NN0'), vxw, w.inst('tmbmono')], 'syl3anc',
                    '( %s -> ( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ ( TMB ` ( ( 4 x. %s ) + 6 ) ) )' % (pc, VXW.replace(" N' )", ' %s )' % NP), VXU))
            hb5w = linarith(w, pc, [tbv, cx["( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ U'" % VXU]], "( TMB ` ( ( 4 x. %s ) + 6 ) ) <_ U'" % VXW.replace(" N' )", ' %s )' % NP), closure=clx)
            # EXY <_ W'
            EXXW = "( ( ( 3 x. ( # ` W ) ) x. B' ) + ( ( 5 x. B' ) + 5 ) )"
            exx = linarith(w, pc, [wb], '%s <_ %s' % (EXXW, EXXU), closure=clx, products=True)
            tbx = linarith(w, pc, [s([clx.mem(EXXW, 'NN0'), clx.mem(EXXU, 'NN0'), exx, w.inst('tmbmono')], 'syl3anc', '( %s -> ( TMB ` %s ) <_ ( TMB ` %s ) )' % (pc, EXXW, EXXU)), cx["( TMB ` %s ) <_ U'" % EXXU]],
                           "( TMB ` %s ) <_ U'" % EXXW, closure=clx)
            m1 = mul_le(w, pc, clx, '( ( # ` W ) + 2 )', '( %s + 2 )' % P2U, '( TMB ` %s )' % EXXW, "U'", w2, tbx)
            m2 = mul_le2(w, pc, clx, LSQ, '( ( ( # ` W ) + 2 ) x. ( TMB ` %s ) )' % EXXW, PRDU, m1)
            asx = lineq(w, pc, "( %s x. ( ( ( # ` W ) + 2 ) x. ( TMB ` %s ) ) )" % (LSQ, EXXW), EXY, closure=clx, products=True)
            asu = lineq(w, pc, "( %s x. %s )" % (LSQ, PRDU), "( ( %s x. ( %s + 2 ) ) x. U' )" % (LSQ, P2U), closure=clx, products=True)
            hexy = linarith(w, pc, [m2, asx, asu, cx["( ( %s x. ( %s + 2 ) ) x. U' ) <_ W'" % (LSQ, P2U)]], "%s <_ W'" % EXY, closure=clx, products=True)
            # the cost so far at the extract stage
            TBS = "( TMB ` ( ( ( ( ; 4 8 x. ( ( # ` Q ) + 1 ) ) x. ( B' + B' ) ) + ( 4 x. ( # ` Q ) ) ) + ; ; 1 0 2 ) )"
            clx.leaf('( # ` Q )', 'NN0', s([tyx['Q'], w.inst('lencl')], 'syl', '( %s -> ( # ` Q ) e. NN0 )' % pc))
            clx.leaf(TBS, 'NN0', tmbn(w, pc, TBS[len('( TMB ` '):-2], clx.mem(TBS[len('( TMB ` '):-2], 'NN0')))
            csnle = mul_le2(w, pc, clx, '( %s + 1 )' % S2, TBS, "U'", cx[HB3])
            Z3 = "( ( Z' + 1 ) + %s )" % CSN
            z3n = clx.mem(Z3, 'NN0')
            z3le = linarith(w, pc, [cx["Z' <_ %s" % PRE2], csnle], '%s <_ %s' % (Z3, PRE3), closure=clx, products=True)
            # tmisrc3 at the stacks Ss
            ex3 = {STKD(Ss.D): Ss.memb, RALB('W', "B'"): ralw, 'A. a e. ran W 2 <_ a': ralw2, '( # ` W ) <_ ( 2 ^ U )': wle,
                   '%s = %s' % (NP, NP): s([s([], 'eqid', '%s = %s' % (NP, NP))], 'a1i', '( %s -> %s = %s )' % (pc, NP, NP)),
                   POS1: s([pos], 'simpld', '( %s -> %s )' % (pc, POS1)), POS2: s([pos], 'simprd', '( %s -> %s )' % (pc, POS2)),
                   "( %s + 2 ) <_ U'" % NP: np2, LT2("J'", "B'"): jlt, "( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) <_ W'": hpv,
                   "( ( L x. ( ( ( # ` W ) x. ( B' + 1 ) ) + 1 ) ) + 1 ) <_ W'": hlpv, "( ( ( # ` W ) + 2 ) x. U' ) <_ W'": hw2,
                   HB5W.replace(" N' )", ' %s )' % NP): hb5w, "( TMB ` %s ) <_ U'" % NP: tbnp, "%s <_ W'" % EXY: hexy, '%s e. NN0' % NP: clx.mem(NP, 'NN0'),
                   '%s e. NN0' % Z3: z3n, '%s <_ %s' % (Z3, PRE3): z3le}
            for k in N8:
                ex3['( %s ` %s ) = %s' % (Ss.D, k, Ss.vals[k][0])] = Ss.vals[k][1]
            t3, cc3 = inst(w, pc, 'tmisrc3', {'D': Ss.D, "N'": NP, "Z'": Z3}, Bld(w, pc, cx, ex3))
            C3, D3c, n3 = triple_parts(cc3)
            assert C3 == Dc, '\n%s\n%s' % (C3, Dc)
            assert D3c == POST
            t = hrseq(w, pc, mk['phm'], tc, t3, Cc, Dc, POST, nc, n3)
            n = '( %s + %s )' % (nc, n3)
            # ( 1 + CSN ) + ( TOT' - Z3 ) = TOT - Z' where TOT' has N' := NP (the search cost does not mention N')
            assert "N'" not in TOT
            svs = s([L_(sv2), s([cst], 'iffalsed', '( %s -> %s = %s )' % (pc, rhs2, INNER3))], 'eqtrd', '( %s -> %s = %s )' % (pc, SE, INNER3))
            # ( 2nd SE ) e. NN0 through the search's typing: both branches of INNER3 have NN0 costs
            w2x, _ = verify_typing(w, pc, cx, clx)
            pi_ = "( %s /\\ ( 1st ` X' ) = %s )" % (pc, INR)
            pn_ = "( %s /\\ -. ( 1st ` X' ) = %s )" % (pc, INR)
            c3a = "( ( C' + %s ) + %s )" % (S2, E2)
            i1 = s([s([s([], 'simpr', '( %s -> ( 1st ` X\' ) = %s )' % (pi_, INR))], 'iftrued', '( %s -> %s = <. %s , %s >. )' % (pi_, INNER3, INR, c3a))], 'fveq2d',
                   '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (pi_, INNER3, INR, c3a))
            i1v = s([i1, s([s([s([], 'fvex', '%s e. _V' % INR), s([], 'ovex', '%s e. _V' % c3a)], 'op2nd', '( 2nd ` <. %s , %s >. ) = %s' % (INR, c3a, c3a))], 'a1i', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pi_, INR, c3a, c3a))],
                    'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (pi_, INNER3, c3a))
            i1n = s([i1v, s([clx.mem(c3a, 'NN0')], 'adantr', '( %s -> %s e. NN0 )' % (pi_, c3a))], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pi_, INNER3))
            i2 = s([s([s([], 'simpr', '( %s -> -. ( 1st ` X\' ) = %s )' % (pn_, INR))], 'iffalsed', '( %s -> %s = <. %s , %s >. )' % (pn_, INNER3, IFQ, CST4))], 'fveq2d',
                   '( %s -> ( 2nd ` %s ) = ( 2nd ` <. %s , %s >. ) )' % (pn_, INNER3, IFQ, CST4))
            i2v = s([i2, s([s([s([], 'ifex', '%s e. _V' % IFQ), s([], 'ovex', '%s e. _V' % CST4)], 'op2nd', '( 2nd ` <. %s , %s >. ) = %s' % (IFQ, CST4, CST4))], 'a1i', '( %s -> ( 2nd ` <. %s , %s >. ) = %s )' % (pn_, IFQ, CST4, CST4))],
                    'eqtrd', '( %s -> ( 2nd ` %s ) = %s )' % (pn_, INNER3, CST4))
            i2n = s([i2v, s([clx.mem(CST4, 'NN0')], 'adantr', '( %s -> %s e. NN0 )' % (pn_, CST4))], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pn_, INNER3))
            i3n = s([i1n, i2n], 'pm2.61dan', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, INNER3))
            sen = s([s([svs], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (pc, SE, INNER3)), i3n], 'eqeltrd', '( %s -> ( 2nd ` %s ) e. NN0 )' % (pc, SE))
            clx.leaf('( 2nd ` %s )' % SE, 'NN0', sen)
            clx.leaf(TOT, 'NN0', clx.mem(TOT, 'NN0'))
            clx.leaf(CSN, 'NN0', clx.mem(CSN, 'NN0'))
            ceq = lineq(w, pc, n, "( %s - Z' )" % TOT, closure=clx)
            t, _, _, _ = hrrw(w, pc, t, Cc, POST, n, neq=ceq)
        outs.append(s([t], 'ex', '( %s -> ( %s -> %s ) )' % (ph, cond, CONCL_SRC2)))
    st = s([outs[0], outs[1]], 'pm2.61d', '( %s -> %s )' % (ph, CONCL_SRC2))
    finish(w, st, lab)
    return w.run()



if __name__ == '__main__':
    done_pg = False
    for l in SEL:
        if l.startswith('t12pglen'):
            if not done_pg:
                t12pglen(); done_pg = True
        else:
            globals()[l]()
