"""T7: ` sub x y z x ` at the machine (Lean ` sub_runs_x ` ): the borrow and
difference sequences (T4 ~ bwborrow , ~ bwsubdig ), the subtractor's body,
exit and ` zeroIfBorrow ` interfaces, and the instance of ~ tm2fsubx .  The
read phase and the classes are the adder's ( ~ tmcadrd , ~ tmcadss ,
~ tmcadin ) at the borrow sequence.

    MM_DB=sorties/t7.mm python3 tools/gen/t7_q_sub.py [LABEL...]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from t7sub import *
from cl import Closure
from lin import linarith
from t7_e_cmp import machine, togk, letgk, bitsgk, lamty, cis_ty, pbr_ty, ral_S
from t7_k_add import words, carry_hyps, ifone, cand_val, CAND_X, PSUM_X
from t7_l_addx import flty, load_ty, maj_cl, two_lam_ty, psum_ty, wgk, bitsw_g
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LN, LN2 = '( # ` L )', "( # ` L' )"
FACC = dict(car='TMcar', ra='TMra', rb='TMrb', da='TMda', db='TMdb', cmp='TMcmp', fl='TMfl')
IFB = lambda N: 'if ( ( %s mod ( 2 ^ %s ) ) < ( ( %s mod ( 2 ^ %s ) ) + ( bToNat ` (/) ) ) , 1o , (/) )' % (TA, N, TB, N)


def tmcsbc0():
    ph = PH_LL
    w = W('tmcsbc0', 'The borrow into bit 0 of a subtraction without borrow-in is 0.')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    b = words(w, ph, ll, ll2)
    h = carry_hyps(w, ph, b['ta'], b['tb'], closed(w, ph, '0nn0', '0 e. NN0'), '0')
    cr = w.s([h, w.inst('bwborrow')], 'syl', '( %s -> ( %s ` 0 ) = %s )' % (ph, CRB, IFB('0')))
    e20 = w.s([closed(w, ph, '2cn', '2 e. CC'), w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % ph)
    def m0(T):
        return w.s([w.s([e20], 'oveq2d', '( %s -> ( %s mod ( 2 ^ 0 ) ) = ( %s mod 1 ) )' % (ph, T, T)),
                    w.s([w.s([b['ta'] if T == TA else b['tb']], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, T)), w.inst('zmod10')], 'syl', '( %s -> ( %s mod 1 ) = 0 )' % (ph, T))],
                   'eqtrd', '( %s -> ( %s mod ( 2 ^ 0 ) ) = 0 )' % (ph, T))
    ma, mb = m0(TA), m0(TB)
    s = w.s([mb, closed(w, ph, 'bwbn0', '( bToNat ` (/) ) = 0')], 'oveq12d', '( %s -> ( ( %s mod ( 2 ^ 0 ) ) + ( bToNat ` (/) ) ) = ( 0 + 0 ) )' % (ph, TB))
    s2 = w.s([s, closed(w, ph, '00id', '( 0 + 0 ) = 0')], 'eqtrd', '( %s -> ( ( %s mod ( 2 ^ 0 ) ) + ( bToNat ` (/) ) ) = 0 )' % (ph, TB))
    br = w.s([ma, s2], 'breq12d', '( %s -> ( ( %s mod ( 2 ^ 0 ) ) < ( ( %s mod ( 2 ^ 0 ) ) + ( bToNat ` (/) ) ) <-> 0 < 0 ) )' % (ph, TA, TB))
    n00 = w.s([w.s([], '0re', '0 e. RR')], 'ltnri', '-. 0 < 0')
    nc = w.s([br, w.s([n00], 'a1i', '( %s -> -. 0 < 0 )' % ph)], 'mtbird',
             '( %s -> -. ( %s mod ( 2 ^ 0 ) ) < ( ( %s mod ( 2 ^ 0 ) ) + ( bToNat ` (/) ) ) )' % (ph, TA, TB))
    w.qed([cr, w.s([nc], 'iffalsed', '( %s -> %s = (/) )' % (ph, IFB('0')))], 'eqtrd', '( %s -> ( %s ` 0 ) = (/) )' % (ph, CRB))
    return w.run()


def tmcsbdg():
    ph = '( %s /\\ N e. NN0 )' % PH_LL
    w = W('tmcsbdg', 'The difference bit of the ` N ` -th iteration of the subtractor is bit ` N ` of the difference '
                     '(Lean ` subBits ` unfolded, T4 ~ bwsubdig with the borrow of ~ bwborrow ).')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simplr', "( %s -> L' e. Word 2o )" % ph)
    nn = w.s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    b = words(w, ph, ll, ll2)
    h = carry_hyps(w, ph, b['ta'], b['tb'], nn)
    cr = w.s([h, w.inst('bwborrow')], 'syl', '( %s -> ( %s ` N ) = %s )' % (ph, CRB, IFB('N')))
    dg = w.s([h, w.inst('bwsubdig')], 'syl', '( %s -> ( N e. ( bits ` %s ) <-> ( ( %s sumBit %s ) ` %s ) = 1o ) )'
             % (ph, SUBV, BIT('L', 'N'), BIT("L'", 'N'), IFB('N')))
    V = '( ( %s sumBit %s ) ` ( %s ` N ) )' % (BIT('L', 'N'), BIT("L'", 'N'), CRB)
    v1 = w.s([cr], 'fveq2d', '( %s -> %s = ( ( %s sumBit %s ) ` %s ) )' % (ph, V, BIT('L', 'N'), BIT("L'", 'N'), IFB('N')))
    v2 = w.s([v1], 'eqeq1d', '( %s -> ( %s = 1o <-> ( ( %s sumBit %s ) ` %s ) = 1o ) )' % (ph, V, BIT('L', 'N'), BIT("L'", 'N'), IFB('N')))
    v3 = w.s([v2, dg], 'bitr4d', '( %s -> ( %s = 1o <-> N e. ( bits ` %s ) ) )' % (ph, V, SUBV))
    ba = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % BIT('L', 'N'))
    bb = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % BIT("L'", 'N'))
    cc = w.s([h, w.inst('bwborrowcl')], 'syl', '( %s -> ( %s ` N ) e. 2o )' % (ph, CRB))
    vc = w.s([w.s([ba], 'a1i', '( %s -> %s e. 2o )' % (ph, BIT('L', 'N'))), w.s([bb], 'a1i', '( %s -> %s e. 2o )' % (ph, BIT("L'", 'N'))), cc,
              w.inst('sumbitcl')], 'syl3anc', '( %s -> %s e. 2o )' % (ph, V))
    j = w.s([vc, v3], 'jca', '( %s -> ( %s e. 2o /\\ ( %s = 1o <-> N e. ( bits ` %s ) ) ) )' % (ph, V, V, SUBV))
    w.qed([j, w.inst('tmc2oif')], 'syl', '( %s -> %s = if ( N e. ( bits ` %s ) , 1o , (/) ) )' % (ph, V, SUBV))
    return w.run()


def tmcsbcp():
    ph = '( %s /\\ N e. NN0 )' % PH_LL
    w = W('tmcsbcp', 'The borrow recursion of the subtractor (Lean ` borrow ` ), ~ bwborrowp1 at the operands\' values.')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simplr', "( %s -> L' e. Word 2o )" % ph)
    nn = w.s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    b = words(w, ph, ll, ll2)
    h = carry_hyps(w, ph, b['ta'], b['tb'], nn)
    w.qed([h, w.inst('bwborrowp1')], 'syl', split_imp(stmt_of('tmcsbcp'))[1].join(['( %s -> ' % ph, ' )']))
    return w.run()


def stmt_of(l):
    return dict(STMTS7)[l]


def zb(w, ph, ll, ll2):
    b = words(w, ph, ll, ll2)
    tz = w.s([b['ta']], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, TA))
    bn = w.s([closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('bwbncl')], 'syl', '( %s -> ( bToNat ` (/) ) e. NN0 )' % ph)
    s = w.s([b['tb'], bn, w.inst('nn0addcl')], 'syl2anc', "( %s -> ( %s + ( bToNat ` (/) ) ) e. NN0 )" % (ph, TB))
    sz = w.s([tz, w.s([s], 'nn0zd', "( %s -> ( %s + ( bToNat ` (/) ) ) e. ZZ )" % (ph, TB)), w.inst('zsubcld' if False else 'zsubcl')], 'syl2anc',
             '( %s -> %s e. ZZ )' % (ph, SUBV))
    mx = w.s([b['lb'], b['la']], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXA))
    return b, sz, mx


def tmcsbzl():
    ph = PH_LL
    w = W('tmcsbzl', 'The difference word of the subtractor has one letter per iteration, the longer operand\'s length.')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    b, sz, mx = zb(w, ph, ll, ll2)
    BW = '( %s bwrd %s )' % (SUBV, MXA)
    bw = w.s([sz, mx, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, BW))
    l1 = w.s([bw, closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS), w.inst('lenco')], 'syl2anc',
             '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ZSB, BW))
    l2 = w.s([sz, mx, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, BW, MXA))
    w.qed([l1, l2], 'eqtrd', stmt_of('tmcsbzl'))
    return w.run()


def tmcsbzv():
    ph = '( %s /\\ N e. ( 0 ..^ %s ) )' % (PH_LL, MXA)
    w = W('tmcsbzv', 'The ` N ` -th letter of the subtractor\'s difference word is the bit letter of bit ` N ` of the difference.')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simplr', "( %s -> L' e. Word 2o )" % ph)
    nf = w.s([], 'simpr', '( %s -> N e. ( 0 ..^ %s ) )' % (ph, MXA))
    b, sz, mx = zb(w, ph, ll, ll2)
    BW = '( %s bwrd %s )' % (SUBV, MXA)
    bf = w.s([sz, mx, w.inst('bwrdf')], 'syl2anc', '( %s -> %s : ( 0 ..^ %s ) --> 2o )' % (ph, BW, MXA))
    v1 = w.s([bf, nf, w.inst('fvco3')], 'syl2anc', '( %s -> ( %s ` N ) = ( inclBool ` ( %s ` N ) ) )' % (ph, ZSB, BW))
    v2 = w.s([sz, mx, nf, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` N ) = if ( N e. ( bits ` %s ) , 1o , (/) ) )' % (ph, BW, SUBV))
    IFS = 'if ( N e. ( bits ` %s ) , 1o , (/) )' % SUBV
    v3 = w.s([v2], 'fveq2d', '( %s -> ( inclBool ` ( %s ` N ) ) = ( inclBool ` %s ) )' % (ph, BW, IFS))
    ic = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFS)
    v4 = w.s([w.s([ic], 'a1i', '( %s -> %s e. 2o )' % (ph, IFS)), w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` %s ) = <. 1 , %s >. )' % (ph, IFS, IFS))
    w.qed([w.s([v1, v3], 'eqtrd', '( %s -> ( %s ` N ) = ( inclBool ` %s ) )' % (ph, ZSB, IFS)), v4], 'eqtrd',
          '( %s -> ( %s ` N ) = <. 1 , %s >. )' % (ph, ZSB, IFS))
    return w.run()


def tmcsbbd():
    ph = PH_LL
    w = W('tmcsbbd', 'The subtractor\'s body at the machine (Lean ` subBody ` ): before both operands are exhausted the '
                     'test ` da && db ` fails, the pushed letter is the difference bit of the iteration, and the load '
                     '` carry := borrow ( bitOf ra ) ( bitOf rb ) carry ` leads into the class of the next iteration.')
    ph2 = '( %s /\\ ( i e. ( 0 ..^ ( # ` %s ) ) /\\ p e. ( %s ` i ) ) )' % (ph, ZSB, OFB)
    A2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    ll = A2(w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph), 'L e. Word 2o')
    ll2 = A2(w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph), "L' e. Word 2o")
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph2, PH_LL))
    ifz = w.s([], 'simprl', '( %s -> i e. ( 0 ..^ ( # ` %s ) ) )' % (ph2, ZSB))
    pin = w.s([], 'simprr', '( %s -> p e. ( %s ` i ) )' % (ph2, OFB))
    zl = w.s([lls, w.inst('tmcsbzl')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph2, ZSB, MXA))
    ifo = w.s([ifz, w.s([zl], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ %s ) )' % (ph2, ZSB, MXA))], 'eleqtrd',
              '( %s -> i e. ( 0 ..^ %s ) )' % (ph2, MXA))
    inn = w.s([ifo, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph2)
    ilt = w.s([ifo, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ph2, MXA))
    b = words(w, ph2, ll, ll2)
    cl = Closure(w, ph2, {'i': ('NN0', inn), LN: ('NN0', b['la']), LN2: ('NN0', b['lb'])})
    pmem, pc = fam_unpack(w, ph2, OCOND(CRB), 'i', inn, 'p', pin)
    OT = ocond_tree(CRB, 'p', 'i')
    pp = parts(w, ph2, pc, OT)
    # (1) the test
    cv = cand_val(w, ph2, 'p', pmem)
    da1 = ifone(w, ph2, 'L', '<_', 'i', pp[OT[0][1]], 'p', 'TMda')
    db1 = ifone(w, ph2, "L'", '<_', 'i', pp[OT[0][2]], 'p', 'TMdb')
    an = w.s([da1, db1], 'anbi12d', "( %s -> ( ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) <-> ( %s <_ i /\\ %s <_ i ) ) )" % (ph2, LN, LN2))
    mx = w.s([cl.mem(LN, 'RR'), cl.mem(LN2, 'RR'), cl.mem('i', 'RR'), w.inst('maxle')], 'syl3anc',
             '( %s -> ( %s <_ i <-> ( %s <_ i /\\ %s <_ i ) ) )' % (ph2, MXA, LN, LN2))
    mxr = w.s([w.s([b['lb'], b['la']], 'ifcld', '( %s -> %s e. NN0 )' % (ph2, MXA))], 'nn0red', '( %s -> %s e. RR )' % (ph2, MXA))
    nmx = w.s([ilt, w.s([cl.mem('i', 'RR'), mxr], 'ltnled', '( %s -> ( i < %s <-> -. %s <_ i ) )' % (ph2, MXA, MXA))], 'mpbid',
              '( %s -> -. %s <_ i )' % (ph2, MXA))
    nan = w.s([w.s([an, mx], 'bitr4d', "( %s -> ( ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) <-> %s <_ i ) )" % (ph2, MXA)), nmx], 'mtbird',
              "( %s -> -. ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) )" % ph2)
    c0 = w.s([cv, w.s([nan], 'iffalsed', '( %s -> %s = (/) )' % (ph2, CAND_X('p')))], 'eqtrd', '( %s -> ( %s ` p ) = (/) )' % (ph2, CANDD))
    t1 = not1o(w, ph2, c0, CANDD, 'p')
    # (2) the pushed letter
    pv = lamval(w, ph2, PSUM_X, 'p', pmem, closed(w, ph2, 'opex', '%s e. _V' % PSUM_X('p')))
    def bitreg(L_, fld, st):
        e = w.s([st], 'fveq2d', '( %s -> ( bitOf ` ( %s ` p ) ) = ( bitOf ` %s ) )' % (ph2, FACC[fld], RGV(L_, 'i')))
        lw = ll if L_ == 'L' else ll2
        g = w.s([w.s([lw, inn], 'jca', '( %s -> ( %s e. Word 2o /\\ i e. NN0 ) )' % (ph2, L_)), w.inst('tmcbrg')], 'syl',
                '( %s -> ( bitOf ` %s ) = %s )' % (ph2, RGV(L_, 'i'), BIT(L_, 'i')))
        return w.s([e, g], 'eqtrd', '( %s -> ( bitOf ` ( %s ` p ) ) = %s )' % (ph2, FACC[fld], BIT(L_, 'i')))
    ba_ = bitreg('L', 'ra', pp[OT[1][0]])
    bb_ = bitreg("L'", 'rb', pp[OT[1][1]])
    car = pp[OT[0][0]]
    def fold(op):
        f = w.s([ba_, bb_], 'oveq12d', '( %s -> ( ( bitOf ` ( TMra ` p ) ) %s ( bitOf ` ( TMrb ` p ) ) ) = ( %s %s %s ) )' % (ph2, op, BIT('L', 'i'), op, BIT("L'", 'i')))
        return w.s([f, car], 'fveq12d', '( %s -> ( ( ( bitOf ` ( TMra ` p ) ) %s ( bitOf ` ( TMrb ` p ) ) ) ` ( TMcar ` p ) ) = ( ( %s %s %s ) ` ( %s ` i ) ) )'
                   % (ph2, op, BIT('L', 'i'), op, BIT("L'", 'i'), CRB))
    sm = fold('sumBit')
    IFS = 'if ( i e. ( bits ` %s ) , 1o , (/) )' % SUBV
    sm2 = w.s([w.s([lls, inn], 'jca', '( %s -> ( %s /\\ i e. NN0 ) )' % (ph2, PH_LL)), w.inst('tmcsbdg')], 'syl',
              '( %s -> ( ( %s sumBit %s ) ` ( %s ` i ) ) = %s )' % (ph2, BIT('L', 'i'), BIT("L'", 'i'), CRB, IFS))
    sm3 = w.s([sm, sm2], 'eqtrd', '( %s -> ( ( ( bitOf ` ( TMra ` p ) ) sumBit ( bitOf ` ( TMrb ` p ) ) ) ` ( TMcar ` p ) ) = %s )' % (ph2, IFS))
    pv2 = w.s([pv, w.s([sm3], 'opeq2d', '( %s -> %s = <. 1 , %s >. )' % (ph2, PSUM_X('p'), IFS))], 'eqtrd', '( %s -> ( %s ` p ) = <. 1 , %s >. )' % (ph2, PSUM, IFS))
    zv = w.s([w.s([lls, ifo], 'jca', '( %s -> ( %s /\\ i e. ( 0 ..^ %s ) ) )' % (ph2, PH_LL, MXA)), w.inst('tmcsbzv')], 'syl',
             '( %s -> ( %s ` i ) = <. 1 , %s >. )' % (ph2, ZSB, IFS))
    t2 = w.s([pv2, zv], 'eqtr4d', '( %s -> ( %s ` p ) = ( %s ` i ) )' % (ph2, PSUM, ZSB))
    # (3) the load
    rcl = lambda f: w.s([pmem, w.inst('tmc%scl' % f)], 'syl', '( %s -> ( %s ` p ) e. %s )' % (ph2, FACC[f], CODOM[f]))
    bo = lambda f: w.s([rcl(f), w.inst('bitofcl')], 'syl', '( %s -> ( bitOf ` ( %s ` p ) ) e. 2o )' % (ph2, FACC[f]))
    mc = w.s([bo('ra'), bo('rb'), rcl('car'), w.inst('borrowcl')], 'syl3anc', '( %s -> %s e. 2o )' % (ph2, LBOR_X('p')))
    lv = load_val(w, ph2, lambda t: dict(car=LBOR_X(t)), 'p', pmem, {LBOR_X('p'): mc})
    LM = '( %s ` p )' % LBOR
    i1 = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ph2)
    NT = ncond_tree(CRB, LM, '( i + 1 )')
    cp = w.s([w.s([lls, inn], 'jca', '( %s -> ( %s /\\ i e. NN0 ) )' % (ph2, PH_LL)), w.inst('tmcsbcp')], 'syl',
             '( %s -> ( %s ` ( i + 1 ) ) = ( ( %s borrow %s ) ` ( %s ` i ) ) )' % (ph2, CRB, BIT('L', 'i'), BIT("L'", 'i'), CRB))
    car2 = w.s([w.s([lv['fields']['car'], fold('borrow')], 'eqtrd', '( %s -> ( TMcar ` %s ) = ( ( %s borrow %s ) ` ( %s ` i ) ) )'
                    % (ph2, LM, BIT('L', 'i'), BIT("L'", 'i'), CRB)), cp], 'eqtr4d', '( %s -> %s )' % (ph2, NT[0][0]))
    def flg(fld, L_, lnst, k):
        LNx = '( # ` %s )' % L_
        bi = w.s([lnst, inn, w.inst('nn0leltp1')], 'syl2anc', '( %s -> ( %s <_ i <-> %s < ( i + 1 ) ) )' % (ph2, LNx, LNx))
        ib = w.s([bi], 'ifbid', '( %s -> %s = %s )' % (ph2, FLG(L_, '<_', 'i'), FLG(L_, '<', '( i + 1 )')))
        return w.s([w.s([lv['fields'][fld], pp[OT[0][k]]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, FACC[fld], LM, FLG(L_, '<_', 'i'))), ib],
                   'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, FACC[fld], LM, FLG(L_, '<', '( i + 1 )'))), bi
    da2, bia = flg('da', 'L', b['la'], 1)
    db2, bib = flg('db', "L'", b['lb'], 2)
    def regnone(fld, L_, bi, k):
        LNx = '( # ` %s )' % L_
        p3 = '( %s /\\ %s < ( i + 1 ) )' % (ph2, LNx)
        le = w.s([w.s([bi], 'adantr', '( %s -> ( %s <_ i <-> %s < ( i + 1 ) ) )' % (p3, LNx, LNx)), w.s([], 'simpr', '( %s -> %s < ( i + 1 ) )' % (p3, LNx))],
                 'mpbird', '( %s -> %s <_ i )' % (p3, LNx))
        c3 = Closure(w, p3, {'i': ('NN0', w.s([inn], 'adantr', '( %s -> i e. NN0 )' % p3)),
                             LNx: ('NN0', w.s([b['la'] if L_ == 'L' else b['lb']], 'adantr', '( %s -> %s e. NN0 )' % (p3, LNx)))})
        nlt = w.s([le, w.s([c3.mem(LNx, 'RR'), c3.mem('i', 'RR')], 'lenltd', '( %s -> ( %s <_ i <-> -. i < %s ) )' % (p3, LNx, LNx))], 'mpbid',
                  '( %s -> -. i < %s )' % (p3, LNx))
        e = w.s([w.s([w.s([lv['fields'][fld], pp[OT[1][k]]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, FACC[fld], LM, RGV(L_, 'i')))], 'adantr',
                     '( %s -> ( %s ` %s ) = %s )' % (p3, FACC[fld], LM, RGV(L_, 'i'))),
                 w.s([nlt], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (p3, RGV(L_, 'i')))], 'eqtrd', '( %s -> ( %s ` %s ) = ( inr ` (/) ) )' % (p3, FACC[fld], LM))
        return w.s([e], 'ex', '( %s -> ( %s < ( i + 1 ) -> ( %s ` %s ) = ( inr ` (/) ) ) )' % (ph2, LNx, FACC[fld], LM))
    ra2 = regnone('ra', 'L', bia, 0)
    rb2 = regnone('rb', "L'", bib, 1)
    nc = w.s([w.s([car2, da2, db2], '3jca', '( %s -> %s )' % (ph2, cj(NT[0]))), w.s([ra2, rb2], 'jca', '( %s -> %s )' % (ph2, cj(NT[1])))],
             'jca', '( %s -> %s )' % (ph2, cj(NT)))
    t3 = fam_pack(w, ph2, NCOND(CRB), '( i + 1 )', i1, LM, lv['mem'], nc)
    BODY = '( -. ( %s ` p ) = 1o /\\ ( %s ` p ) = ( %s ` i ) /\\ ( %s ` p ) e. ( %s ` ( i + 1 ) ) )' % (CANDD, PSUM, ZSB, LBOR, NFB)
    j = w.s([t1, t2, t3], '3jca', '( %s -> %s )' % (ph2, BODY))
    w.qed([j], 'ralrimivva', ST_SBBD)
    return w.run()


def exit_state(w, ph, ll, ll2):
    """facts about a state p of the exit class ( OFB ` ( # ` ZSB ) ) under phq = ( ph /\\ p e. ... )"""
    b, sz, mx = zb(w, ph, ll, ll2)
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph, PH_LL))
    zl = w.s([lls, w.inst('tmcsbzl')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, ZSB, MXA))
    OFZ = '( %s ` ( # ` %s ) )' % (OFB, ZSB)
    oeq = w.s([zl], 'fveq2d', '( %s -> %s = ( %s ` %s ) )' % (ph, OFZ, OFB, MXA))
    phq = '( %s /\\ p e. %s )' % (ph, OFZ)
    Aq = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (phq, f))
    pz = w.s([], 'simpr', '( %s -> p e. %s )' % (phq, OFZ))
    pin = w.s([pz, Aq(oeq, '%s = ( %s ` %s )' % (OFZ, OFB, MXA))], 'eleqtrd', '( %s -> p e. ( %s ` %s ) )' % (phq, OFB, MXA))
    mxq = Aq(mx, '%s e. NN0' % MXA)
    pmem, pc = fam_unpack(w, phq, OCOND(CRB), MXA, mxq, 'p', pin)
    OT = ocond_tree(CRB, 'p', MXA)
    pp = parts(w, phq, pc, OT)
    laq, lbq = Aq(b['la'], '%s e. NN0' % LN), Aq(b['lb'], '%s e. NN0' % LN2)
    cq = Closure(w, phq, {LN: ('NN0', laq), LN2: ('NN0', lbq)})
    m1 = w.s([cq.mem(LN, 'RR'), cq.mem(LN2, 'RR'), w.inst('max1')], 'syl2anc', '( %s -> %s <_ %s )' % (phq, LN, MXA))
    m2 = w.s([cq.mem(LN, 'RR'), cq.mem(LN2, 'RR'), w.inst('max2')], 'syl2anc', '( %s -> %s <_ %s )' % (phq, LN2, MXA))
    d1 = w.s([pp[OT[0][1]], w.s([m1], 'iftrued', '( %s -> %s = 1o )' % (phq, FLG('L', '<_', MXA)))], 'eqtrd', '( %s -> ( TMda ` p ) = 1o )' % phq)
    d2 = w.s([pp[OT[0][2]], w.s([m2], 'iftrued', '( %s -> %s = 1o )' % (phq, FLG("L'", '<_', MXA)))], 'eqtrd', '( %s -> ( TMdb ` p ) = 1o )' % phq)
    cv = cand_val(w, phq, 'p', pmem)
    cand = w.s([cv, w.s([w.s([d1, d2], 'jca', '( %s -> ( ( TMda ` p ) = 1o /\\ ( TMdb ` p ) = 1o ) )' % phq)], 'iftrued', '( %s -> %s = 1o )' % (phq, CAND_X('p')))],
               'eqtrd', '( %s -> ( %s ` p ) = 1o )' % (phq, CANDD))
    return phq, pmem, pp[OT[0][0]], cand, OFZ


def tmcsbex():
    ph = PH_LL
    w = W('tmcsbex', 'The subtractor\'s exit at the machine: after the last iteration both operands are exhausted and '
                     'the ` carry ` register holds the final borrow (Lean ` subLoop_runs ` ).')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    phq, pmem, car, cand, OFZ = exit_state(w, ph, ll, ll2)
    inn = rab_in(w, phq, NCB, lambda t: '( TMcar ` %s ) = %s' % (t, CRBM), 'p', pmem, car)
    j = w.s([cand, inn], 'jca', '( %s -> ( ( %s ` p ) = 1o /\\ p e. %s ) )' % (phq, CANDD, NCB))
    w.qed([j], 'ralrimiva', ST_SBEX)
    return w.run()


def split_or(text):
    toks = text.split()
    d = 0
    for i, t in enumerate(toks[1:-1], 1):
        if t in ('(', '<.', '{', '<"'):
            d += 1
        elif t in (')', '>.', '}', '">'):
            d -= 1
        elif t == '\\/' and d == 0:
            return ' '.join(toks[1:i]), ' '.join(toks[i + 1:-1])
    raise ValueError(text)


def rab_out(w, ps, cls_text, cond_fn, m, mm):
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (m, m))
    cg, new = w.wcongr(cond_fn('h'), {'h': m}, 'h = %s' % m, {'h': idh})
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (m, cls_text, m, cond_fn(m)))
    both = w.s([mm, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ps, m, cond_fn(m)))
    return w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (ps, m)), w.s([both], 'simprd', '( %s -> %s )' % (ps, cond_fn(m)))


def tmcsbzr():
    ph = split_imp(ST_SBZR)[0]
    w = W('tmcsbzr', 'The subtractor\'s ` zeroIfBorrow z ` at the machine (Lean ` zeroIfBorrow_runs ` ): on a final '
                     'borrow the difference word is popped (the ` carry ` test holds, ` readA ` keeps the borrow) and '
                     'the terminator pushed back with ` carry := false ` , the truncated difference being empty; '
                     'otherwise the test fails and the truncated difference is the difference word (T4 '
                     '~ subtruncval , ~ subborrowfold ).')
    seq = w.s([], 'simpl', '( %s -> %s )' % (ph, SEQ))
    lls = w.s([], 'simpr', '( %s -> %s )' % (ph, PH_LL))
    ll = w.s([lls], 'simpld', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([lls], 'simprd', "( %s -> L' e. Word 2o )" % ph)
    b, sz, mx = zb(w, ph, ll, ll2)
    crc = w.s([carry_hyps(w, ph, b['ta'], b['tb'], mx, MXA), w.inst('bwborrowcl')], 'syl', '( %s -> %s e. 2o )' % (ph, CRBM))
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    SBR = "( ( L subBorrow L' ) ` (/) )"
    STR_ = "( ( L subTrunc L' ) ` (/) )"
    SBT = "( ( L subBits L' ) ` (/) )"
    sbf = w.s([ll, ll2, b0, w.inst('subborrowfold')], 'syl3anc', '( %s -> %s = %s )' % (ph, SBR, CRBM))
    stv = w.s([ll, ll2, b0, w.inst('subtruncval')], 'syl3anc', '( %s -> %s = if ( %s = 1o , (/) , %s ) )' % (ph, STR_, SBR, SBT))
    LEFT, RIGHT = split_or(ZR_DISJ)
    TL = parse_conj(LEFT)
    TR = parse_conj(RIGHT)
    COND = lambda t: '( TMcar ` %s ) = %s' % (t, CRBM)
    # ---- case: final borrow
    p1 = '( %s /\\ %s = 1o )' % (ph, CRBM)
    c1 = w.s([], 'simpr', '( %s -> %s = 1o )' % (p1, CRBM))
    L1 = Lifter(w, p1)
    sb1 = w.s([L1(sbf, '%s = %s' % (SBR, CRBM)), c1], 'eqtrd', '( %s -> %s = 1o )' % (p1, SBR))
    st1 = w.s([L1(stv, '%s = if ( %s = 1o , (/) , %s )' % (STR_, SBR, SBT)), w.s([sb1], 'iftrued', '( %s -> if ( %s = 1o , (/) , %s ) = (/) )' % (p1, SBR, SBT))],
              'eqtrd', '( %s -> %s = (/) )' % (p1, STR_))
    zt1 = w.s([w.s([st1], 'coeq2d', '( %s -> %s = ( inclBool o. (/) ) )' % (p1, ZT)), closed(w, p1, 'bwmap0', '( inclBool o. (/) ) = (/)')], 'eqtrd',
              '( %s -> %s = (/) )' % (p1, ZT))
    # the pops of the difference word
    p2 = '( %s /\\ ( r e. %s /\\ z e. %s ) )' % (p1, NCB, BITS)
    rin = w.s([], 'simprl', '( %s -> r e. %s )' % (p2, NCB))
    zz = w.s([], 'simprr', '( %s -> z e. %s )' % (p2, BITS))
    rr, rc = rab_out(w, p2, NCB, COND, 'r', rin)
    c12 = w.s([c1], 'adantr', '( %s -> %s = 1o )' % (p2, CRBM))
    rc1 = w.s([rc, c12], 'eqtrd', '( %s -> ( TMcar ` r ) = 1o )' % p2)
    nv = rd_bit(w, p2, 'A', 'r', 'z', rr, zz)
    NV_ = NVA('r', 'z')
    ci, _ = cis_val(w, p2, nv, NV_)
    ncar = w.s([nv['fields']['car'], rc], 'eqtrd', '( %s -> %s )' % (p2, COND(NV_)))
    nin = rab_in(w, p2, NCB, COND, NV_, nv['mem'], ncar)
    body1 = cj(TL[0][0]).split(' A. z e. %s ' % BITS, 1)[1]
    a1 = w.s([rc1, ci, nin], '3jca', '( %s -> %s )' % (p2, body1))
    A1 = w.s([a1], 'ralrimivva', '( %s -> %s )' % (p1, cj(TL[0][0])))
    # the terminator
    p3 = '( %s /\\ m e. %s )' % (p1, NCB)
    mm = w.s([], 'simpr', '( %s -> m e. %s )' % (p3, NCB))
    mt, mc = rab_out(w, p3, NCB, COND, 'm', mm)
    mc1 = w.s([mc, w.s([c1], 'adantr', '( %s -> %s = 1o )' % (p3, CRBM))], 'eqtrd', '( %s -> ( TMcar ` m ) = 1o )' % p3)
    nv4 = rd_comma(w, p3, 'A', 'm', mt)
    N4 = NVA('m', '4')
    c4, _ = cis_val(w, p3, nv4, N4)
    n4 = not1o(w, p3, c4, CIS, N4)
    seq3 = w.s([seq], 'ad2antrr', '( %s -> %s )' % (p3, SEQ))
    n4s = w.s([nv4['mem'], seq3], 'eleqtrrd', '( %s -> %s e. ( 2nd ` T ) )' % (p3, N4))
    fc = w.s([closed(w, p3, '4re', '4 e. RR'), n4s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = 4 )' % (p3, C4S, N4))
    lv = load_val(w, p3, lambda t: dict(car='(/)'), N4, nv4['mem'])
    assert LCAR0 == LSET(car='(/)')
    ls = w.s([lv['mem'], seq3], 'eleqtrrd', '( %s -> ( %s ` %s ) e. ( 2nd ` T ) )' % (p3, LCAR0, N4))
    body2 = cj(TL[0][1]).split(' m e. %s ' % NCB, 1)[1]
    a2 = w.s([mc1, n4, w.s([fc, ls], 'jca', '( %s -> ( ( %s ` %s ) = 4 /\\ ( %s ` %s ) e. ( 2nd ` T ) ) )' % (p3, C4S, N4, LCAR0, N4))], '3jca',
             '( %s -> %s )' % (p3, body2))
    A2 = w.s([a2], 'ralrimiva', '( %s -> %s )' % (p1, cj(TL[0][1])))
    case1 = w.s([w.s([w.s([A1, A2], 'jca', '( %s -> %s )' % (p1, cj(TL[0]))), zt1], 'jca', '( %s -> %s )' % (p1, LEFT))], 'orcd', '( %s -> %s )' % (p1, ZR_DISJ))
    # ---- case: no final borrow
    p0 = '( %s /\\ -. %s = 1o )' % (ph, CRBM)
    n0 = w.s([], 'simpr', '( %s -> -. %s = 1o )' % (p0, CRBM))
    L0 = Lifter(w, p0)
    nsb = w.s([w.s([L0(sbf, '%s = %s' % (SBR, CRBM))], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (p0, SBR, CRBM)), n0], 'mtbird', '( %s -> -. %s = 1o )' % (p0, SBR))
    st0 = w.s([L0(stv, '%s = if ( %s = 1o , (/) , %s )' % (STR_, SBR, SBT)), w.s([nsb], 'iffalsed', '( %s -> if ( %s = 1o , (/) , %s ) = %s )' % (p0, SBR, SBT, SBT))],
              'eqtrd', '( %s -> %s = %s )' % (p0, STR_, SBT))
    sbv = w.s([L0(ll, 'L e. Word 2o'), L0(ll2, "L' e. Word 2o"), closed(w, p0, '0el2o', '(/) e. 2o'), w.inst('subbitsval')], 'syl3anc',
              '( %s -> %s = ( %s bwrd %s ) )' % (p0, SBT, SUBV, MXA))
    zt0 = w.s([w.s([st0, sbv], 'eqtrd', '( %s -> %s = ( %s bwrd %s ) )' % (p0, STR_, SUBV, MXA))], 'coeq2d', '( %s -> %s = %s )' % (p0, ZT, ZSB))
    p4 = '( %s /\\ m e. %s )' % (p0, NCB)
    mm4 = w.s([], 'simpr', '( %s -> m e. %s )' % (p4, NCB))
    _, mc4 = rab_out(w, p4, NCB, COND, 'm', mm4)
    nm = w.s([w.s([mc4], 'eqeq1d', '( %s -> ( ( TMcar ` m ) = 1o <-> %s = 1o ) )' % (p4, CRBM)), w.s([n0], 'adantr', '( %s -> -. %s = 1o )' % (p4, CRBM))],
             'mtbird', '( %s -> -. ( TMcar ` m ) = 1o )' % p4)
    R0 = w.s([nm], 'ralrimiva', '( %s -> %s )' % (p0, cj(TR[0])))
    case0 = w.s([w.s([R0, zt0], 'jca', '( %s -> %s )' % (p0, RIGHT))], 'olcd', '( %s -> %s )' % (p0, ZR_DISJ))
    em = w.s([], 'exmidd', '( %s -> ( %s = 1o \\/ -. %s = 1o ) )' % (ph, CRBM, CRBM))
    jo = w.s([case1, case0], 'jaodan', '( ( %s /\\ ( %s = 1o \\/ -. %s = 1o ) ) -> %s )' % (ph, CRBM, CRBM, ZR_DISJ))
    w.qed([em, jo], 'mpdan', ST_SBZR)
    return w.run()


def tmcsubx():
    lab = 'tmcsubx'
    TREE = TREE_SUBX()
    ph = cj(TREE)
    w = W(lab, '` sub x y z x ` at the machine (Lean ` sub_runs_x ` ): ~ tm2fsubx with the handlers of Lean\'s '
               '` subLoop ` and ` zeroIfBorrow ` , the operand families of ~ tmcop1 , the classes of ~ tmcadrd at the '
               'borrow sequence; the first operand\'s stack receives the truncated difference '
               '` bits ( subTrunc xs ys false ) ` in ` 3 max + 5 ` steps.')
    c = Ctx(w, ph, TREE)
    mk = machine(w, ph, c, ['K', 'J', 'I'])
    ll, ll2 = c[WRD('L', '2o')], c[WRD("L'", '2o')]
    xg, yg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    dk, dj = c[DATA_ADD[1][0]], c[DATA_ADD[1][1]]
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph, PH_LL))
    seq = mk['seq']
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    ft = flty(w, ph, mk)
    T_ = lambda f: '%s e. ( 2o ^m ( 2nd ` T ) )' % FACC[f]
    def leaf(st):
        return formula(w, st)[len('( %s -> ' % ph):-2]
    extra = {PHM: mk['phm'], 'T e. V': mk['tv'], MTY: mk['mt'],
             CTY('TMda'): ft[T_('da')], CTY('TMdb'): ft[T_('db')], CTY('TMcar'): ft[T_('car')], CTY(CIS): cis_ty(w, ph, mk),
             CTY(CANDD): two_lam_ty(w, ph, mk, CANDD, CAND_X),
             RTY('TMrdA', 'K'): mk['k']['K']['hdl']['TMrdA'], RTY('TMrdB', 'J'): mk['k']['J']['hdl']['TMrdB'],
             RTY('TMrdA', 'I'): mk['k']['I']['hdl']['TMrdA'],
             PTY(PSUM, 'I'): psum_ty(w, ph, mk, 'I', PSUM, PSUM_X),
             PTY(PBR, 'K'): pbr_ty(w, ph, mk, 'K'),
             LTY(LBOR): load_ty(w, ph, mk, LBOR, lambda t: dict(car=LBOR_X(t)), maj_cl),
             LTY(LADD0): load_ty(w, ph, mk, LADD0, lambda t: dict(car='(/)', ra=NONE, rb=NONE, da='(/)', db='(/)'), None),
             LTY(LCAR0): load_ty(w, ph, mk, LCAR0, lambda t: dict(car='(/)'), None)}
    g4i = letgk(w, ph, mk, '4', 'I', g4)
    extra[PTY(C4S, 'I')] = constfty(w, ph, '4', GX('I'), g4i)
    for k in ['K', 'J', 'I']:
        extra['%s e. %s' % (k, DG)] = mk['k'][k]['kd']
    for k in ['K', 'I']:
        extra['%s C_ %s' % (BITS, GX(k))] = bitsgk(w, ph, mk, k)
        extra['4 e. %s' % GX(k)] = letgk(w, ph, mk, '4', k, g4)
    # the difference word
    b, sz, mx = zb(w, ph, ll, ll2)
    ifl = closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS)
    BW = '( %s bwrd %s )' % (SUBV, MXA)
    bw = w.s([sz, mx, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, BW))
    zbw = w.s([bw, ifl, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZSB, BITS))
    extra[WRD(ZSB, BITS)] = zbw
    extra[WRD(ZSB, GX('I'))] = wgk(w, ph, mk, ZSB, 'I', bitsw_g(w, ph, ZSB, zbw))
    extra['( 2nd ` T ) C_ ( 2nd ` T )'] = closed(w, ph, 'ssid', '( 2nd ` T ) C_ ( 2nd ` T )')
    ncs = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NCB), ], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NCB))
    extra['%s C_ ( 2nd ` T )' % NCB] = w.s([ncs, seq], 'sseqtrrd', '( %s -> %s C_ ( 2nd ` T ) )' % (ph, NCB))
    # the init, the mover, the zero-if-borrow, the classes
    c0 = w.s([lls, w.inst('tmcsbc0')], 'syl', '( %s -> ( %s ` 0 ) = (/) )' % (ph, CRB))
    INIT = tsub_text(ST_ADIN, {'C': CRB})
    ini = w.s([w.s([seq, lls, c0], '3jca', '( %s -> %s )' % (ph, split_imp(INIT)[0])), w.inst('tmcadin')], 'syl', '( %s -> %s )' % (ph, split_imp(INIT)[1]))
    extra[leaf(ini)] = ini
    N = NVA('r', 'z')
    mvi = w.s([], 'tmcmvi', ST_MVI)
    hc = w.s([mvi], 'simpli', 'A. r e. TMSt A. z e. %s ( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z )' % (BITS, CIS, N, PBR, N))
    he = w.s([mvi], 'simpri', 'A. r e. TMSt -. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')))
    HC = ral_S(w, ph, mk, hc, '( ( %s ` %s ) = 1o /\\ ( %s ` %s ) = z )' % (CIS, N, PBR, N), 2)
    HE = ral_S(w, ph, mk, he, '-. ( %s ` %s ) = 1o' % (CIS, NVA('r', '4')), 1)
    extra[leaf(HC)] = HC; extra[leaf(HE)] = HE
    zr = w.s([w.s([seq, lls], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, SEQ, PH_LL)), w.inst('tmcsbzr')], 'syl', '( %s -> %s )' % (ph, ZR_DISJ))
    extra[ZR_DISJ] = zr
    ZL = '( # ` %s )' % ZSB
    fzs = closed(w, ph, 'fz0ssnn0', '( 0 ... %s ) C_ NN0' % ZL)
    SS_ = tsub_text(ST_ADSS, {'C': CRB})
    ssr = w.s([seq, w.inst('tmcadss')], 'syl', '( %s -> %s )' % (ph, split_imp(SS_)[1]))
    body_ss = split_imp(SS_)[1][len('A. i e. NN0 '):]
    extra['A. i e. ( 0 ... %s ) %s' % (ZL, body_ss)] = w.s([fzs, ssr, w.inst('ssralv')], 'sylc', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL, body_ss))
    RD_ = tsub_text(ST_ADRD, {'C': CRB})
    rdr = w.s([lls, w.inst('tmcadrd')], 'syl', '( %s -> %s )' % (ph, split_imp(RD_)[1]))
    body_rd = split_imp(RD_)[1][len('A. i e. NN0 '):]
    extra['A. i e. ( 0 ... %s ) %s' % (ZL, body_rd)] = w.s([fzs, rdr, w.inst('ssralv')], 'sylc', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL, body_rd))
    bd = w.s([lls, w.inst('tmcsbbd')], 'syl', '( %s -> %s )' % (ph, split_imp(ST_SBBD)[1]))
    extra[leaf(bd)] = bd
    ex = w.s([lls, w.inst('tmcsbex')], 'syl', '( %s -> %s )' % (ph, split_imp(ST_SBEX)[1]))
    extra[leaf(ex)] = ex
    # the operand families
    ZL1 = '( %s + 1 )' % ZL
    phi = '( %s /\\ i e. ( 0 ... %s ) )' % (ph, ZL1)
    Ai = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (phi, f))
    ii = w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (phi, ZL1)), w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % phi)
    def fam_ty(Lw, Xw, llst, xgst, k):
        F = OPF(Lw, Xw)
        t = w.s([Ai(llst, '%s e. Word 2o' % Lw), Ai(xgst, "%s e. Word Gamma'" % Xw), ii, w.inst('tmcopty')], 'syl3anc',
                "( %s -> ( %s ` i ) e. Word Gamma' )" % (phi, F))
        return w.s([t, Ai(mk['k'][k]['wge'], "Word %s = Word Gamma'" % GX(k))], 'eleqtrrd', '( %s -> ( %s ` i ) e. Word %s )' % (phi, F, GX(k)))
    tyx = fam_ty('L', 'X', ll, xg, 'K')
    tyy = fam_ty("L'", 'Y', ll2, yg, 'J')
    TYB = '( ( %s ` i ) e. Word %s /\\ ( %s ` i ) e. Word %s )' % (OPFX, GX('K'), OPFY, GX('J'))
    ty = w.s([w.s([tyx, tyy], 'jca', '( %s -> %s )' % (phi, TYB))], 'ralrimiva', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL1, TYB))
    extra[leaf(ty)] = ty
    for Lw, Xw, llst, xgst, dstep, k in [('L', 'X', ll, xg, dk, 'K'), ("L'", 'Y', ll2, yg, dj, 'J')]:
        F = OPF(Lw, Xw)
        v0 = w.s([llst, xgst, w.inst('tmcop0')], 'syl2anc', '( %s -> ( %s ` 0 ) = ( ( inclBool o. %s ) ++ ( <" 4 "> ++ %s ) ) )' % (ph, F, Lw, Xw))
        e0 = w.s([v0, dstep], 'eqtr4d', '( %s -> ( %s ` 0 ) = ( D ` %s ) )' % (ph, F, k))
        extra[leaf(e0)] = e0
    phs = '( %s /\\ i e. ( 0 ... %s ) )' % (ph, ZL)
    As = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (phs, f))
    iis = w.s([w.s([], 'simpr', '( %s -> i e. ( 0 ... %s ) )' % (phs, ZL)), w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % phs)
    def step_part(Lw, Xw, llst, xgst, k):
        ST = tsub_text(ST_OP1, {'L': Lw, 'X': Xw, 'N': 'i'})
        st = w.s([As(llst, '%s e. Word 2o' % Lw), As(xgst, "%s e. Word Gamma'" % Xw), iis, w.inst('tmcop1')], 'syl3anc', '( %s -> %s )' % (phs, split_imp(ST)[1]))
        tree = parse_conj(split_imp(ST)[1])
        pp = parts(w, phs, st, tree)
        U, F = OPU(Lw), OPF(Lw, Xw)
        u1 = w.s([pp["( %s ` i ) e. Gamma'" % U], As(mk['k'][k]['ge'], "%s = Gamma'" % GX(k))], 'eleqtrrd', '( %s -> ( %s ` i ) e. %s )' % (phs, U, GX(k)))
        f1 = w.s([pp["( %s ` ( i + 1 ) ) e. Word Gamma'" % F], As(mk['k'][k]['wge'], "Word %s = Word Gamma'" % GX(k))], 'eleqtrrd',
                 '( %s -> ( %s ` ( i + 1 ) ) e. Word %s )' % (phs, F, GX(k)))
        j = w.s([u1, f1], 'jca', '( %s -> ( ( %s ` i ) e. %s /\\ ( %s ` ( i + 1 ) ) e. Word %s ) )' % (phs, U, GX(k), F, GX(k)))
        tr = tree
        return w.s([pp[cj(tr[0])], pp[cj(tr[1])], j], '3jca', '( %s -> ( %s /\\ %s /\\ ( ( %s ` i ) e. %s /\\ ( %s ` ( i + 1 ) ) e. Word %s ) ) )'
                   % (phs, cj(tr[0]), cj(tr[1]), U, GX(k), F, GX(k)))
    sx = step_part('L', 'X', ll, xg, 'K')
    sy = step_part("L'", 'Y', ll2, yg, 'J')
    SB = '( %s /\\ %s )' % (formula(w, sx)[len('( %s -> ' % phs):-2], formula(w, sy)[len('( %s -> ' % phs):-2])
    stp = w.s([w.s([sx, sy], 'jca', '( %s -> %s )' % (phs, SB))], 'ralrimiva', '( %s -> A. i e. ( 0 ... %s ) %s )' % (ph, ZL, SB))
    extra[leaf(stp)] = stp
    # apply tm2fsubx
    bld = Builder(w, ph, c, extra)
    ante, concl = split_imp(stmt('tm2fsubx'))
    tree = tsub(parse_conj(ante), SUB_MAP)
    st = bld(tree)
    c2 = tsub_text(concl, SUB_MAP)
    tri = w.s([st, w.inst('tm2fsubx')], 'syl', '( %s -> %s )' % (ph, c2))
    C1, D1, n1 = triple_parts(c2)
    # the stacks after the loop, the bound
    cl0 = Closure(w, ph, {LN: ('NN0', b['la']), LN2: ('NN0', b['lb'])})
    zl = w.s([lls, w.inst('tmcsbzl')], 'syl', '( %s -> %s = %s )' % (ph, ZL, MXA))
    cl0.leaf(ZL, 'NN0', w.s([zl, mx], 'eqeltrd', '( %s -> %s e. NN0 )' % (ph, ZL)))
    m1 = w.s([cl0.mem(LN, 'RR'), cl0.mem(LN2, 'RR'), w.inst('max1')], 'syl2anc', '( %s -> %s <_ %s )' % (ph, LN, MXA))
    m2 = w.s([cl0.mem(LN, 'RR'), cl0.mem(LN2, 'RR'), w.inst('max2')], 'syl2anc', '( %s -> %s <_ %s )' % (ph, LN2, MXA))
    rules = {}
    for Lw, Xw, llst, xgst, mm in [('L', 'X', ll, xg, m1), ("L'", 'Y', ll2, yg, m2)]:
        LNx = '( # ` %s )' % Lw
        lt = linarith(w, ph, [mm, zl], '%s < %s' % (LNx, ZL1), closure=cl0)
        z1 = cl0.mem(ZL1, 'NN0')
        e = w.s([w.s([llst, xgst], 'jca', "( %s -> ( %s e. Word 2o /\\ %s e. Word Gamma' ) )" % (ph, Lw, Xw)), w.s([z1, lt], 'jca', '( %s -> ( %s e. NN0 /\\ %s < %s ) )' % (ph, ZL1, LNx, ZL1)),
                 w.inst('tmcope')], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ph, OPF(Lw, Xw), ZL1, Xw))
        rules['( %s ` %s )' % (OPF(Lw, Xw), ZL1)] = (Xw, e)
    deq, D2 = w.rewrite(D1, rules, ph)
    neq = w.s([w.s([zl], 'oveq2d', '( %s -> ( 3 x. %s ) = ( 3 x. %s ) )' % (ph, ZL, MXA))], 'oveq1d', '( %s -> %s = ( ( 3 x. %s ) + 5 ) )' % (ph, n1, MXA))
    t2, C2, D2, n2 = hrrw(w, ph, tri, C1, D1, n1, deq=deq, neq=neq, qed=True)
    assert TRI(C2, D2, n2) == CONCL_SUBX, (TRI(C2, D2, n2), CONCL_SUBX)
    return w.run()


if __name__ == '__main__':
    for l in ['tmcsbc0', 'tmcsbdg', 'tmcsbcp', 'tmcsbzl', 'tmcsbzv', 'tmcsbbd', 'tmcsbex', 'tmcsbzr', 'tmcsubx']:
        if want(l): globals()[l]()
