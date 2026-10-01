"""T7: ` add x y z x ` at the machine (Lean ` add_runs_x ` ): the N-level facts
of the carry and sum sequences, the state classes of T5 D4 (before and after
the reads), their interfaces, and the instance of ~ tm2faddx ."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from cl import Closure
from lin import linarith

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

LN, LN2 = '( # ` L )', "( # ` L' )"
TA, TB = '( toNat ` L )', "( toNat ` L' )"


def body(st, ph):
    return st[len('( %s -> ' % ph):-2]


def words(w, ph, ll, ll2):
    """toNat / length closures of the two operands"""
    ta = w.s([ll, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, TA))
    tb = w.s([ll2, w.inst('tonatcl')], 'syl', '( %s -> %s e. NN0 )' % (ph, TB))
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN))
    lb = w.s([ll2, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN2))
    return dict(ta=ta, tb=tb, la=la, lb=lb)


def tmc2oif():
    ph = '( A e. 2o /\\ ( A = 1o <-> ph ) )'
    w = W('tmc2oif', 'A bit is the decision of the proposition it is true for.')
    aa = w.s([], 'simpl', '( %s -> A e. 2o )' % ph)
    bi = w.s([], 'simpr', '( %s -> ( A = 1o <-> ph ) )' % ph)
    pt = '( %s /\\ ph )' % ph
    a1 = w.s([w.s([bi], 'adantr', '( %s -> ( A = 1o <-> ph ) )' % pt), w.s([], 'simpr', '( %s -> ph )' % pt)], 'mpbird', '( %s -> A = 1o )' % pt)
    i1 = w.s([w.s([], 'simpr', '( %s -> ph )' % pt), w.inst('iftrue')], 'syl', '( %s -> if ( ph , 1o , (/) ) = 1o )' % pt)
    c1 = w.s([a1, i1], 'eqtr4d', '( %s -> A = if ( ph , 1o , (/) ) )' % pt)
    pf = '( %s /\\ -. ph )' % ph
    n1 = w.s([w.s([bi], 'adantr', '( %s -> ( A = 1o <-> ph ) )' % pf), w.s([], 'simpr', '( %s -> -. ph )' % pf)], 'mtbird', '( %s -> -. A = 1o )' % pf)
    a0 = w.s([n1, w.s([w.s([aa], 'adantr', '( %s -> A e. 2o )' % pf), w.inst('bwel2on')], 'syl', '( %s -> ( -. A = 1o <-> A = (/) ) )' % pf)],
             'mpbid', '( %s -> A = (/) )' % pf)
    i0 = w.s([w.s([], 'simpr', '( %s -> -. ph )' % pf), w.inst('iffalse')], 'syl', '( %s -> if ( ph , 1o , (/) ) = (/) )' % pf)
    c0 = w.s([a0, i0], 'eqtr4d', '( %s -> A = if ( ph , 1o , (/) ) )' % pf)
    w.qed([c1, c0], 'pm2.61dan', '( %s -> A = if ( ph , 1o , (/) ) )' % ph)
    return w.run()


def tmcbrg():
    ph = '( L e. Word 2o /\\ N e. NN0 )'
    w = W('tmcbrg', 'The bit a two-operand loop sees in the register after its ` N ` -th read of ` L ` is the '
                    '` N ` -th bit of the value of ` L ` , zero past the word (Lean ` bitOf ( l.get? n ) ` ).')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    nn = w.s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN))
    RG = RGV('L', 'N')
    GOAL = '( bitOf ` %s ) = %s' % (RG, BIT('L', 'N'))
    # N < |L|
    pa = '( %s /\\ N < %s )' % (ph, LN)
    lt = w.s([], 'simpr', '( %s -> N < %s )' % (pa, LN))
    lla = w.s([ll], 'adantr', '( %s -> L e. Word 2o )' % pa)
    ca = Closure(w, pa, {'N': ('NN0', w.s([nn], 'adantr', '( %s -> N e. NN0 )' % pa)), LN: ('NN0', w.s([la], 'adantr', '( %s -> %s e. NN0 )' % (pa, LN)))})
    ez = w.s([ca.mem('N', 'ZZ'), closed(w, pa, '0z', '0 e. ZZ'), ca.mem(LN, 'ZZ'), w.inst('elfzo')], 'syl3anc',
             '( %s -> ( N e. ( 0 ..^ %s ) <-> ( 0 <_ N /\\ N < %s ) ) )' % (pa, LN, LN))
    nfo = w.s([ez, w.s([ca.ge0('N'), lt], 'jca', '( %s -> ( 0 <_ N /\\ N < %s ) )' % (pa, LN))], 'mpbird', '( %s -> N e. ( 0 ..^ %s ) )' % (pa, LN))
    lnb = w.s([lla, nfo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` N ) e. 2o )' % pa)
    r1 = w.s([w.s([lt], 'iftrued', '( %s -> %s = ( inl ` ( L ` N ) ) )' % (pa, RG))], 'fveq2d',
             '( %s -> ( bitOf ` %s ) = ( bitOf ` ( inl ` ( L ` N ) ) ) )' % (pa, RG))
    r2 = w.s([lnb, w.inst('bitofsome')], 'syl', '( %s -> ( bitOf ` ( inl ` ( L ` N ) ) ) = ( L ` N ) )' % pa)
    r3 = w.s([lla, nfo, w.inst('bwfv')], 'syl2anc', '( %s -> ( L ` N ) = %s )' % (pa, BIT('L', 'N')))
    ca_ = w.s([w.s([r1, r2], 'eqtrd', '( %s -> ( bitOf ` %s ) = ( L ` N ) )' % (pa, RG)), r3], 'eqtrd', '( %s -> %s )' % (pa, GOAL))
    # -. N < |L|
    pb = '( %s /\\ -. N < %s )' % (ph, LN)
    nlt = w.s([], 'simpr', '( %s -> -. N < %s )' % (pb, LN))
    llb = w.s([ll], 'adantr', '( %s -> L e. Word 2o )' % pb)
    s1 = w.s([w.s([nlt], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (pb, RG))], 'fveq2d',
             '( %s -> ( bitOf ` %s ) = ( bitOf ` ( inr ` (/) ) ) )' % (pb, RG))
    s2 = w.s([s1, closed(w, pb, 'bitofnone', '( bitOf ` ( inr ` (/) ) ) = (/)')], 'eqtrd', '( %s -> ( bitOf ` %s ) = (/) )' % (pb, RG))
    lt2 = w.s([w.s([], 'elfzolt2', '( N e. ( 0 ..^ %s ) -> N < %s )' % (LN, LN))], 'a1i', '( %s -> ( N e. ( 0 ..^ %s ) -> N < %s ) )' % (pb, LN, LN))
    nfo2 = w.s([nlt, lt2], 'mtod', '( %s -> -. N e. ( 0 ..^ %s ) )' % (pb, LN))
    ss = w.s([llb, w.inst('bwbitsss')], 'syl', '( %s -> ( bits ` %s ) C_ ( 0 ..^ %s ) )' % (pb, TA, LN))
    nb = w.s([ss, nfo2], 'ssneldd', '( %s -> -. N e. ( bits ` %s ) )' % (pb, TA))
    s3 = w.s([nb], 'iffalsed', '( %s -> %s = (/) )' % (pb, BIT('L', 'N')))
    cb_ = w.s([s2, s3], 'eqtr4d', '( %s -> %s )' % (pb, GOAL))
    w.qed([ca_, cb_], 'pm2.61dan', '( %s -> %s )' % (ph, GOAL))
    return w.run()


def carry_hyps(w, ph, ta, tb, nn=None, N='N'):
    """( ph -> ( ( A e. ZZ /\\ B e. ZZ /\\ (/) e. 2o ) /\\ N e. NN0 ) ) for bwcarry & co."""
    az = w.s([ta], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, TA))
    bz = w.s([tb], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, TB))
    z2 = closed(w, ph, '0el2o', '(/) e. 2o')
    j3 = w.s([az, bz, z2], '3jca', '( %s -> ( %s e. ZZ /\\ %s e. ZZ /\\ (/) e. 2o ) )' % (ph, TA, TB))
    if nn is None:
        return j3
    return w.s([j3, nn], 'jca', '( %s -> ( ( %s e. ZZ /\\ %s e. ZZ /\\ (/) e. 2o ) /\\ %s e. NN0 ) )' % (ph, TA, TB, N))


IFC = lambda N: ('if ( ( 2 ^ %s ) <_ ( ( ( %s mod ( 2 ^ %s ) ) + ( %s mod ( 2 ^ %s ) ) ) + ( bToNat ` (/) ) ) , 1o , (/) )'
                 % (N, TA, N, TB, N))


def tmcadc0():
    ph = PH_LL
    w = W('tmcadc0', 'The carry into bit 0 of an addition without carry-in is 0.')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    b = words(w, ph, ll, ll2)
    h = carry_hyps(w, ph, b['ta'], b['tb'], closed(w, ph, '0nn0', '0 e. NN0'), '0')
    cr = w.s([h, w.inst('bwcarry')], 'syl', '( %s -> ( %s ` 0 ) = %s )' % (ph, CRS, IFC('0')))
    e20 = closed(w, ph, 'exp0' if False else '2cn', '2 e. CC')
    e20 = w.s([e20, w.inst('exp0')], 'syl', '( %s -> ( 2 ^ 0 ) = 1 )' % ph)
    ma = w.s([w.s([e20], 'oveq2d', '( %s -> ( %s mod ( 2 ^ 0 ) ) = ( %s mod 1 ) )' % (ph, TA, TA)),
              w.s([w.s([b['ta']], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, TA)), w.inst('zmod10')], 'syl', '( %s -> ( %s mod 1 ) = 0 )' % (ph, TA))],
             'eqtrd', '( %s -> ( %s mod ( 2 ^ 0 ) ) = 0 )' % (ph, TA))
    mb = w.s([w.s([e20], 'oveq2d', '( %s -> ( %s mod ( 2 ^ 0 ) ) = ( %s mod 1 ) )' % (ph, TB, TB)),
              w.s([w.s([b['tb']], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, TB)), w.inst('zmod10')], 'syl', '( %s -> ( %s mod 1 ) = 0 )' % (ph, TB))],
             'eqtrd', '( %s -> ( %s mod ( 2 ^ 0 ) ) = 0 )' % (ph, TB))
    s = w.s([ma, mb], 'oveq12d', '( %s -> ( ( %s mod ( 2 ^ 0 ) ) + ( %s mod ( 2 ^ 0 ) ) ) = ( 0 + 0 ) )' % (ph, TA, TB))
    s2 = w.s([s, closed(w, ph, 'bwbn0', '( bToNat ` (/) ) = 0')], 'oveq12d',
             '( %s -> ( ( ( %s mod ( 2 ^ 0 ) ) + ( %s mod ( 2 ^ 0 ) ) ) + ( bToNat ` (/) ) ) = ( ( 0 + 0 ) + 0 ) )' % (ph, TA, TB))
    zz = w.s([], '00id', '( 0 + 0 ) = 0')
    z3 = w.s([w.s([zz], 'oveq1i', '( ( 0 + 0 ) + 0 ) = ( 0 + 0 )'), zz], 'eqtri', '( ( 0 + 0 ) + 0 ) = 0')
    s3 = w.s([s2, w.s([z3], 'a1i', '( %s -> ( ( 0 + 0 ) + 0 ) = 0 )' % ph)], 'eqtrd',
             '( %s -> ( ( ( %s mod ( 2 ^ 0 ) ) + ( %s mod ( 2 ^ 0 ) ) ) + ( bToNat ` (/) ) ) = 0 )' % (ph, TA, TB))
    br = w.s([e20, s3], 'breq12d', '( %s -> ( ( 2 ^ 0 ) <_ ( ( ( %s mod ( 2 ^ 0 ) ) + ( %s mod ( 2 ^ 0 ) ) ) + ( bToNat ` (/) ) ) <-> 1 <_ 0 ) )' % (ph, TA, TB))
    n10 = w.s([w.s([], '0lt1', '0 < 1'), w.s([w.s([], '0re', '0 e. RR'), w.s([], '1re', '1 e. RR')], 'ltnlei', '( 0 < 1 <-> -. 1 <_ 0 )')],
              'mpbi', '-. 1 <_ 0')
    nc = w.s([br, w.s([n10], 'a1i', '( %s -> -. 1 <_ 0 )' % ph)], 'mtbird',
             '( %s -> -. ( 2 ^ 0 ) <_ ( ( ( %s mod ( 2 ^ 0 ) ) + ( %s mod ( 2 ^ 0 ) ) ) + ( bToNat ` (/) ) ) )' % (ph, TA, TB))
    w.qed([cr, w.s([nc], 'iffalsed', '( %s -> %s = (/) )' % (ph, IFC('0')))], 'eqtrd', '( %s -> ( %s ` 0 ) = (/) )' % (ph, CRS))
    return w.run()


def tmcadsum():
    ph = '( %s /\\ N e. NN0 )' % PH_LL
    w = W('tmcadsum', 'The sum bit of the ` N ` -th iteration of the adder is bit ` N ` of the sum (Lean ` addBits ` '
                      'unfolded, T4 ~ bwadddig with the carry of ~ bwcarry ).')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simplr', "( %s -> L' e. Word 2o )" % ph)
    nn = w.s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    b = words(w, ph, ll, ll2)
    h = carry_hyps(w, ph, b['ta'], b['tb'], nn)
    cr = w.s([h, w.inst('bwcarry')], 'syl', '( %s -> ( %s ` N ) = %s )' % (ph, CRS, IFC('N')))
    dg = w.s([h, w.inst('bwadddig')], 'syl', '( %s -> ( N e. ( bits ` %s ) <-> ( ( %s sumBit %s ) ` %s ) = 1o ) )'
             % (ph, SUMV, BIT('L', 'N'), BIT("L'", 'N'), IFC('N')))
    V = '( ( %s sumBit %s ) ` ( %s ` N ) )' % (BIT('L', 'N'), BIT("L'", 'N'), CRS)
    v1 = w.s([cr], 'fveq2d', '( %s -> %s = ( ( %s sumBit %s ) ` %s ) )' % (ph, V, BIT('L', 'N'), BIT("L'", 'N'), IFC('N')))
    v2 = w.s([v1], 'eqeq1d', '( %s -> ( %s = 1o <-> ( ( %s sumBit %s ) ` %s ) = 1o ) )' % (ph, V, BIT('L', 'N'), BIT("L'", 'N'), IFC('N')))
    v3 = w.s([v2, dg], 'bitr4d', '( %s -> ( %s = 1o <-> N e. ( bits ` %s ) ) )' % (ph, V, SUMV))
    ba = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % BIT('L', 'N'))
    bb = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % BIT("L'", 'N'))
    cc = w.s([h, w.inst('bwcarrycl')], 'syl', '( %s -> ( %s ` N ) e. 2o )' % (ph, CRS))
    vc = w.s([w.s([ba], 'a1i', '( %s -> %s e. 2o )' % (ph, BIT('L', 'N'))), w.s([bb], 'a1i', '( %s -> %s e. 2o )' % (ph, BIT("L'", 'N'))), cc,
              w.inst('sumbitcl')], 'syl3anc', '( %s -> %s e. 2o )' % (ph, V))
    j = w.s([vc, v3], 'jca', '( %s -> ( %s e. 2o /\\ ( %s = 1o <-> N e. ( bits ` %s ) ) ) )' % (ph, V, V, SUMV))
    w.qed([j, w.inst('tmc2oif')], 'syl', '( %s -> %s = if ( N e. ( bits ` %s ) , 1o , (/) ) )' % (ph, V, SUMV))
    return w.run()


def tmcadcp():
    ph = '( %s /\\ N e. NN0 )' % PH_LL
    w = W('tmcadcp', 'The carry recursion of the adder (Lean ` maj ` ), ~ bwcarryp1 at the operands\' values.')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simplr', "( %s -> L' e. Word 2o )" % ph)
    nn = w.s([], 'simpr', '( %s -> N e. NN0 )' % ph)
    b = words(w, ph, ll, ll2)
    h = carry_hyps(w, ph, b['ta'], b['tb'], nn)
    w.qed([h, w.inst('bwcarryp1')], 'syl', ST_ADCP)
    return w.run()


def zbasics(w, ph, ll, ll2):
    b = words(w, ph, ll, ll2)
    c = Closure(w, ph, {TA: ('NN0', b['ta']), TB: ('NN0', b['tb']), LN: ('NN0', b['la']), LN2: ('NN0', b['lb'])})
    sz = c.mem(SUMV.replace('( bToNat ` (/) )', '0'), 'NN0') if False else None
    ab = w.s([b['ta'], b['tb'], w.inst('nn0addcl')], 'syl2anc', '( %s -> ( %s + %s ) e. NN0 )' % (ph, TA, TB))
    bn = closed(w, ph, 'bwbncl' if False else '0el2o', '(/) e. 2o')
    bn = w.s([bn, w.inst('bwbncl')], 'syl', '( %s -> ( bToNat ` (/) ) e. NN0 )' % ph)
    s = w.s([ab, bn, w.inst('nn0addcl')], 'syl2anc', '( %s -> %s e. NN0 )' % (ph, SUMV))
    sz = w.s([s], 'nn0zd', '( %s -> %s e. ZZ )' % (ph, SUMV))
    mx = w.s([b['lb'], b['la']], 'ifcld', '( %s -> %s e. NN0 )' % (ph, MXA))
    return b, sz, mx


def tmcadzl():
    ph = PH_LL
    w = W('tmcadzl', 'The sum word of the adder has one letter per iteration, the longer operand\'s length.')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph)
    b, sz, mx = zbasics(w, ph, ll, ll2)
    BW = '( %s bwrd %s )' % (SUMV, MXA)
    bw = w.s([sz, mx, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, BW))
    l1 = w.s([bw, closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS), w.inst('lenco')], 'syl2anc',
             '( %s -> ( # ` %s ) = ( # ` %s ) )' % (ph, ZS, BW))
    l2 = w.s([sz, mx, w.inst('bwrdlen')], 'syl2anc', '( %s -> ( # ` %s ) = %s )' % (ph, BW, MXA))
    w.qed([l1, l2], 'eqtrd', ST_ADZL[len('( %s -> ' % ph):-2].join(['( %s -> ' % ph, ' )']))
    return w.run()


def tmcadzv():
    ph = '( %s /\\ N e. ( 0 ..^ %s ) )' % (PH_LL, MXA)
    w = W('tmcadzv', 'The ` N ` -th letter of the adder\'s sum word is the bit letter of bit ` N ` of the sum.')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([], 'simplr', "( %s -> L' e. Word 2o )" % ph)
    nf = w.s([], 'simpr', '( %s -> N e. ( 0 ..^ %s ) )' % (ph, MXA))
    b, sz, mx = zbasics(w, ph, ll, ll2)
    BW = '( %s bwrd %s )' % (SUMV, MXA)
    bf = w.s([sz, mx, w.inst('bwrdf')], 'syl2anc', '( %s -> %s : ( 0 ..^ %s ) --> 2o )' % (ph, BW, MXA))
    v1 = w.s([bf, nf, w.inst('fvco3')], 'syl2anc', '( %s -> ( %s ` N ) = ( inclBool ` ( %s ` N ) ) )' % (ph, ZS, BW))
    v2 = w.s([sz, mx, nf, w.inst('bwrdfv')], 'syl3anc', '( %s -> ( %s ` N ) = if ( N e. ( bits ` %s ) , 1o , (/) ) )' % (ph, BW, SUMV))
    IFS = 'if ( N e. ( bits ` %s ) , 1o , (/) )' % SUMV
    v3 = w.s([v2], 'fveq2d', '( %s -> ( inclBool ` ( %s ` N ) ) = ( inclBool ` %s ) )' % (ph, BW, IFS))
    ic = w.s([w.s([], '1oel2o', '1o e. 2o'), w.s([], '0el2o', '(/) e. 2o')], 'ifcli', '%s e. 2o' % IFS)
    v4 = w.s([w.s([ic], 'a1i', '( %s -> %s e. 2o )' % (ph, IFS)), w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` %s ) = <. 1 , %s >. )' % (ph, IFS, IFS))
    w.qed([w.s([v1, v3], 'eqtrd', '( %s -> ( %s ` N ) = ( inclBool ` %s ) )' % (ph, ZS, IFS)), v4], 'eqtrd',
          '( %s -> ( %s ` N ) = <. 1 , %s >. )' % (ph, ZS, IFS))
    return w.run()



def tmcadss():
    ph = SEQ
    w = W('tmcadss', 'The state classes of the adder\'s families are classes of machine states.')
    ph1 = '( %s /\\ i e. NN0 )' % ph
    inn = w.s([], 'simpr', '( %s -> i e. NN0 )' % ph1)
    seq = w.s([], 'simpl', '( %s -> %s )' % (ph1, SEQ))
    out = []
    for cond, F in [(NCOND('C'), NFG), (OCOND('C'), OFG)]:
        fv = famval(w, ph1, cond, 'i', inn)
        rab = '{ h e. TMSt | %s }' % cond('h', 'i')
        ss = closed(w, ph1, 'ssrab2', '%s C_ TMSt' % rab)
        s1 = w.s([fv, ss], 'eqsstrd', '( %s -> ( %s ` i ) C_ TMSt )' % (ph1, F))
        out.append(w.s([s1, seq], 'sseqtrrd', '( %s -> ( %s ` i ) C_ ( 2nd ` T ) )' % (ph1, F)))
    j = w.s(out, 'jca', '( %s -> ( ( %s ` i ) C_ ( 2nd ` T ) /\\ ( %s ` i ) C_ ( 2nd ` T ) ) )' % (ph1, NFG, OFG))
    w.qed([j], 'ralrimiva', ST_ADSS)
    return w.run()


LADD0_KW = lambda t: dict(car='(/)', ra=NONE, rb=NONE, da='(/)', db='(/)')
assert LADD0 == LSET(**LADD0_KW('u'))


def tmcadin():
    ph = '( ( 2nd ` T ) = TMSt /\\ %s /\\ ( C ` 0 ) = (/) )' % PH_LL
    w = W('tmcadin', 'The adder\'s initialisation ` { v with carry := false , ra := none , rb := none , da := false , '
                     'db := false } ` puts every state into the class of iteration 0.')
    ph1 = '( %s /\\ r e. ( 2nd ` T ) )' % ph
    A1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph1, f))
    seq = A1(w.s([], 'simp1', '( %s -> %s )' % (ph, SEQ)), SEQ)
    ll = A1(w.s([w.s([], 'simp2', '( %s -> %s )' % (ph, PH_LL))], 'simpld', '( %s -> L e. Word 2o )' % ph), 'L e. Word 2o')
    ll2 = A1(w.s([w.s([], 'simp2', '( %s -> %s )' % (ph, PH_LL))], 'simprd', "( %s -> L' e. Word 2o )" % ph), "L' e. Word 2o")
    c0 = A1(w.s([], 'simp3', '( %s -> ( C ` 0 ) = (/) )' % ph), '( C ` 0 ) = (/)')
    rs = w.s([], 'simpr', '( %s -> r e. ( 2nd ` T ) )' % ph1)
    rr = w.s([rs, seq], 'eleqtrd', '( %s -> r e. TMSt )' % ph1)
    lv = load_val(w, ph1, LADD0_KW, 'r', rr)
    LR = '( %s ` r )' % LADD0
    cond = NCOND('C')
    tree = ncond_tree('C', LR, '0')
    f = lv['fields']
    car = w.s([f['car'], w.s([c0], 'eqcomd', '( %s -> (/) = ( C ` 0 ) )' % ph1)], 'eqtrd', '( %s -> %s )' % (ph1, tree[0][0]))
    fl = {}
    for fld, L_ in [('da', 'L'), ('db', "L'")]:
        lw = ll if L_ == 'L' else ll2
        ln = w.s([lw, w.inst('lencl')], 'syl', '( %s -> ( # ` %s ) e. NN0 )' % (ph1, L_))
        nl = w.s([ln, w.inst('nn0nlt0')], 'syl', '( %s -> -. ( # ` %s ) < 0 )' % (ph1, L_))
        itf = w.s([nl], 'iffalsed', '( %s -> %s = (/) )' % (ph1, FLG(L_, '<', '0')))
        fl[fld] = w.s([f[fld], itf], 'eqtr4d', '( %s -> ( %s ` %s ) = %s )' % (ph1, ACC[fld], LR, FLG(L_, '<', '0')))
    ra = w.s([f['ra']], 'a1d', '( %s -> %s )' % (ph1, tree[1][0]))
    rb = w.s([f['rb']], 'a1d', '( %s -> %s )' % (ph1, tree[1][1]))
    j1 = w.s([car, fl['da'], fl['db']], '3jca', '( %s -> %s )' % (ph1, cj(tree[0])))
    j2 = w.s([ra, rb], 'jca', '( %s -> %s )' % (ph1, cj(tree[1])))
    cst = w.s([j1, j2], 'jca', '( %s -> %s )' % (ph1, cj(tree)))
    z = closed(w, ph1, '0nn0', '0 e. NN0')
    mem = fam_pack(w, ph1, cond, '0', z, LR, lv['mem'], cst)
    w.qed([mem], 'ralrimiva', ST_ADIN)
    return w.run()


def ifone(w, ph, L_, rel, j, fld_st, h, FLDN):
    """( ph -> ( ( FLDN ` h ) = 1o <-> ( # ` L_ ) rel j ) ) from fld_st : ( ph -> ( FLDN ` h ) = FLG )"""
    e1 = w.s([fld_st], 'eqeq1d', '( %s -> ( ( %s ` %s ) = 1o <-> %s = 1o ) )' % (ph, FLDN, h, FLG(L_, rel, j)))
    e2 = w.s([w.s([], 'tmcif1', '( %s = 1o <-> ( # ` %s ) %s %s )' % (FLG(L_, rel, j), L_, rel, j))], 'a1i',
             '( %s -> ( %s = 1o <-> ( # ` %s ) %s %s ) )' % (ph, FLG(L_, rel, j), L_, rel, j))
    return w.s([e1, e2], 'bitrd', '( %s -> ( ( %s ` %s ) = 1o <-> ( # ` %s ) %s %s ) )' % (ph, FLDN, h, L_, rel, j))


def inR_iff(w, ph, L_, i, inn, ln):
    """( ph -> ( i e. ( 0 ... ( # ` L_ ) ) <-> i <_ ( # ` L_ ) ) )"""
    LNx = '( # ` %s )' % L_
    R = OPR(L_)
    a = w.s([w.s([], 'elfzle2', '( %s e. %s -> %s <_ %s )' % (i, R, i, LNx))], 'a1i', '( %s -> ( %s e. %s -> %s <_ %s ) )' % (ph, i, R, i, LNx))
    pl = '( %s /\\ %s <_ %s )' % (ph, i, LNx)
    j = w.s([w.s([inn], 'adantr', '( %s -> %s e. NN0 )' % (pl, i)), w.s([ln], 'adantr', '( %s -> %s e. NN0 )' % (pl, LNx)),
             w.s([], 'simpr', '( %s -> %s <_ %s )' % (pl, i, LNx))], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (pl, i, LNx, i, LNx))
    b = w.s([j, w.s([], 'elfz2nn0', '( %s e. %s <-> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (i, R, i, LNx, i, LNx))], 'sylibr',
            '( %s -> %s e. %s )' % (pl, i, R))
    return w.s([a, w.s([b], 'ex', '( %s -> ( %s <_ %s -> %s e. %s ) )' % (ph, i, LNx, i, R))], 'impbid',
               '( %s -> ( %s e. %s <-> %s <_ %s ) )' % (ph, i, R, i, LNx))


def tmcadrd():
    ph = PH_LL
    w = W('tmcadrd', 'The read phase of the adder at the machine (T5 ` tm2fadrd ` \'s interface, Lean ` OpA.read ` '
                     'then ` OpB.read ` ): on the class of iteration ` i ` the flags say whether ` i ` is past each read '
                     'set, and the two reads lead into the post-read class.')
    ph2 = '( %s /\\ ( i e. NN0 /\\ n e. ( %s ` i ) ) )' % (ph, NFG)
    A2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    ll = A2(w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph), 'L e. Word 2o')
    ll2 = A2(w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph), "L' e. Word 2o")
    inn = w.s([], 'simprl', '( %s -> i e. NN0 )' % ph2)
    nin = w.s([], 'simprr', '( %s -> n e. ( %s ` i ) )' % (ph2, NFG))
    la = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph2, LN))
    lb = w.s([ll2, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph2, LN2))
    nmem, ncond = fam_unpack(w, ph2, NCOND('C'), 'i', inn, 'n', nin)
    np_ = parts(w, ph2, ncond, ncond_tree('C', 'n', 'i'))
    T = ncond_tree('C', 'n', 'i')
    # read a
    ha = w.s([w.s([ll, inn], 'jca', '( %s -> ( L e. Word 2o /\\ i e. NN0 ) )' % ph2),
              w.s([nmem, np_[T[0][1]], np_[T[1][0]]], '3jca', '( %s -> ( n e. TMSt /\\ %s /\\ %s ) )' % (ph2, T[0][1], T[1][0]))],
             'jca', '( %s -> %s )' % (ph2, split_imp(tsub_text(ST_RDA, {'N': 'i', 'V': 'n'}))[0]))
    ca_ = split_imp(tsub_text(ST_RDA, {'N': 'i', 'V': 'n'}))[1]
    ra = w.s([ha, w.inst('tmcrda')], 'syl', '( %s -> %s )' % (ph2, ca_))
    pa = parts(w, ph2, ra, parse_conj(ca_))
    n1 = RDN1
    g = lambda f, x: '( %s ` %s )' % (ACC[f], x)
    # read b
    dbn1 = w.s([pa['%s = %s' % (g('db', n1), g('db', 'n'))], np_[T[0][2]]], 'eqtrd', '( %s -> %s = %s )' % (ph2, g('db', n1), FLG("L'", '<', 'i')))
    rbe = w.s([pa['%s = %s' % (g('rb', n1), g('rb', 'n'))]], 'eqeq1d', '( %s -> ( %s = ( inr ` (/) ) <-> %s = ( inr ` (/) ) ) )' % (ph2, g('rb', n1), g('rb', 'n')))
    rbi = w.s([rbe], 'imbi2d', "( %s -> ( ( %s < i -> %s = ( inr ` (/) ) ) <-> ( %s < i -> %s = ( inr ` (/) ) ) ) )" % (ph2, LN2, g('rb', n1), LN2, g('rb', 'n')))
    rbn1 = w.s([rbi, np_[T[1][1]]], 'mpbird', "( %s -> ( %s < i -> %s = ( inr ` (/) ) ) )" % (ph2, LN2, g('rb', n1)))
    STB = tsub_text(ST_RDB, {'N': 'i', 'V': n1, 'L': "L'"})
    hb = w.s([w.s([ll2, inn], 'jca', "( %s -> ( L' e. Word 2o /\\ i e. NN0 ) )" % ph2),
              w.s([pa['%s e. TMSt' % n1], dbn1, rbn1], '3jca', '( %s -> ( %s e. TMSt /\\ %s = %s /\\ ( %s < i -> %s = ( inr ` (/) ) ) ) )'
                  % (ph2, n1, g('db', n1), FLG("L'", '<', 'i'), LN2, g('rb', n1)))], 'jca', '( %s -> %s )' % (ph2, split_imp(STB)[0]))
    cb_ = split_imp(STB)[1]
    rb = w.s([hb, w.inst('tmcrdb')], 'syl', '( %s -> %s )' % (ph2, cb_))
    pb = parts(w, ph2, rb, parse_conj(cb_))
    n2 = RDN2
    assert n2 == RDIF('TMrdB', n1, "L'", 'i')
    # n2 in the post-read class
    OT = ocond_tree('C', n2, 'i')
    car2 = w.s([w.s([pb['%s = %s' % (g('car', n2), g('car', n1))], pa['%s = %s' % (g('car', n1), g('car', 'n'))]], 'eqtrd',
                    '( %s -> %s = %s )' % (ph2, g('car', n2), g('car', 'n'))), np_[T[0][0]]], 'eqtrd', '( %s -> %s )' % (ph2, OT[0][0]))
    da2 = w.s([pb['%s = %s' % (g('da', n2), g('da', n1))], pa['%s = %s' % (g('da', n1), FLG('L', '<_', 'i'))]], 'eqtrd', '( %s -> %s )' % (ph2, OT[0][1]))
    db2 = pb['%s = %s' % (g('db', n2), FLG("L'", '<_', 'i'))]
    ra2 = w.s([pb['%s = %s' % (g('ra', n2), g('ra', n1))], pa['%s = %s' % (g('ra', n1), RGV('L', 'i'))]], 'eqtrd', '( %s -> %s )' % (ph2, OT[1][0]))
    rb2 = pb['%s = %s' % (g('rb', n2), RGV("L'", 'i'))]
    oc = w.s([w.s([car2, da2, db2], '3jca', '( %s -> %s )' % (ph2, cj(OT[0]))), w.s([ra2, rb2], 'jca', '( %s -> %s )' % (ph2, cj(OT[1])))],
             'jca', '( %s -> %s )' % (ph2, cj(OT)))
    omem = fam_pack(w, ph2, OCOND('C'), 'i', inn, n2, pb['%s e. TMSt' % n2], oc)
    # the flag equivalences
    cl2 = Closure(w, ph2, {'i': ('NN0', inn), LN: ('NN0', la), LN2: ('NN0', lb)})
    def flagiff(L_, ln, fldst, h, FLDN):
        LNx = '( # ` %s )' % L_
        e = ifone(w, ph2, L_, '<', 'i', fldst, h, FLDN)
        e3 = w.s([cl2.mem(LNx, 'RR'), cl2.mem('i', 'RR')], 'ltnled', '( %s -> ( %s < i <-> -. i <_ %s ) )' % (ph2, LNx, LNx))
        e5 = w.s([inR_iff(w, ph2, L_, 'i', inn, ln)], 'notbid', '( %s -> ( -. i e. %s <-> -. i <_ %s ) )' % (ph2, OPR(L_), LNx))
        return w.s([w.s([e, e3], 'bitrd', '( %s -> ( ( %s ` %s ) = 1o <-> -. i <_ %s ) )' % (ph2, FLDN, h, LNx)), e5], 'bitr4d',
                   '( %s -> ( ( %s ` %s ) = 1o <-> -. i e. %s ) )' % (ph2, FLDN, h, OPR(L_)))
    f1 = flagiff('L', la, np_[T[0][1]], 'n', 'TMda')
    f2 = flagiff("L'", lb, dbn1, n1, 'TMdb')
    body_ = ST_ADRD.split(' ( TMda ` n ) = 1o', 1)
    BODY = '( ( ( TMda ` n ) = 1o <-> -. i e. %s ) /\\ ( ( TMdb ` %s ) = 1o <-> -. i e. %s ) /\\ %s e. ( %s ` i ) )' % (OPR('L'), n1, OPR("L'"), n2, OFG)
    j = w.s([f1, f2, omem], '3jca', '( %s -> %s )' % (ph2, BODY))
    w.qed([j], 'ralrimivva', ST_ADRD)
    return w.run()



CAND_X = lambda t: 'if ( ( ( TMda ` %s ) = 1o /\\ ( TMdb ` %s ) = 1o ) , 1o , (/) )' % (t, t)
PSUM_X = lambda t: '<. 1 , ( ( ( bitOf ` ( TMra ` %s ) ) sumBit ( bitOf ` ( TMrb ` %s ) ) ) ` ( TMcar ` %s ) ) >.' % (t, t, t)
MAJ_X = lambda t: '( ( ( bitOf ` ( TMra ` %s ) ) majBit ( bitOf ` ( TMrb ` %s ) ) ) ` ( TMcar ` %s ) )' % (t, t, t)
assert CANDD == '( u e. TMSt |-> %s )' % CAND_X('u') and PSUM == '( u e. TMSt |-> %s )' % PSUM_X('u')
assert LMAJ == LSET(car=MAJ_X('u'))


def cand_val(w, ph, x, xmem):
    z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
    xex = ifex_closed(w, ph, '( ( TMda ` %s ) = 1o /\\ ( TMdb ` %s ) = 1o )' % (x, x), '1o', '(/)', o1, z0)
    return lamval(w, ph, CAND_X, x, xmem, xex)


def tmcadbd():
    ph = PH_LL
    w = W('tmcadbd', 'The adder\'s body at the machine (T5 D4): before both operands are exhausted the test '
                     '` da && db ` fails, the pushed letter is the sum bit of the iteration, and the load '
                     '` carry := maj ( bitOf ra ) ( bitOf rb ) carry ` leads into the class of the next iteration.')
    ph2 = '( %s /\\ ( i e. ( 0 ..^ ( # ` %s ) ) /\\ p e. ( %s ` i ) ) )' % (ph, ZS, OFA)
    A2 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph2, f))
    ll = A2(w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph), 'L e. Word 2o')
    ll2 = A2(w.s([], 'simpr', "( %s -> L' e. Word 2o )" % ph), "L' e. Word 2o")
    lls = w.s([ll, ll2], 'jca', '( %s -> %s )' % (ph2, PH_LL))
    ifz = w.s([], 'simprl', '( %s -> i e. ( 0 ..^ ( # ` %s ) ) )' % (ph2, ZS))
    pin = w.s([], 'simprr', '( %s -> p e. ( %s ` i ) )' % (ph2, OFA))
    zl = w.s([lls, w.inst('tmcadzl')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph2, ZS, MXA))
    ifo = w.s([ifz, w.s([zl], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ %s ) )' % (ph2, ZS, MXA))], 'eleqtrd',
              '( %s -> i e. ( 0 ..^ %s ) )' % (ph2, MXA))
    inn = w.s([ifo, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ph2)
    ilt = w.s([ifo, w.inst('elfzolt2')], 'syl', '( %s -> i < %s )' % (ph2, MXA))
    b = words(w, ph2, ll, ll2)
    cl = Closure(w, ph2, {'i': ('NN0', inn), LN: ('NN0', b['la']), LN2: ('NN0', b['lb'])})
    pmem, pc = fam_unpack(w, ph2, OCOND(CRS), 'i', inn, 'p', pin)
    OT = ocond_tree(CRS, 'p', 'i')
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
        e = w.s([st], 'fveq2d', '( %s -> ( bitOf ` ( %s ` p ) ) = ( bitOf ` %s ) )' % (ph2, ACC[fld], RGV(L_, 'i')))
        lw = ll if L_ == 'L' else ll2
        g = w.s([w.s([lw, inn], 'jca', '( %s -> ( %s e. Word 2o /\\ i e. NN0 ) )' % (ph2, L_)), w.inst('tmcbrg')], 'syl',
                '( %s -> ( bitOf ` %s ) = %s )' % (ph2, RGV(L_, 'i'), BIT(L_, 'i')))
        return w.s([e, g], 'eqtrd', '( %s -> ( bitOf ` ( %s ` p ) ) = %s )' % (ph2, ACC[fld], BIT(L_, 'i')))
    ba_ = bitreg('L', 'ra', pp[OT[1][0]])
    bb_ = bitreg("L'", 'rb', pp[OT[1][1]])
    car = pp[OT[0][0]]
    def fold(op):
        f = w.s([ba_, bb_], 'oveq12d', '( %s -> ( ( bitOf ` ( TMra ` p ) ) %s ( bitOf ` ( TMrb ` p ) ) ) = ( %s %s %s ) )' % (ph2, op, BIT('L', 'i'), op, BIT("L'", 'i')))
        return w.s([f, car], 'fveq12d', '( %s -> ( ( ( bitOf ` ( TMra ` p ) ) %s ( bitOf ` ( TMrb ` p ) ) ) ` ( TMcar ` p ) ) = ( ( %s %s %s ) ` ( %s ` i ) ) )'
                   % (ph2, op, BIT('L', 'i'), op, BIT("L'", 'i'), CRS))
    sm = fold('sumBit')
    IFS = 'if ( i e. ( bits ` %s ) , 1o , (/) )' % SUMV
    sm2 = w.s([w.s([lls, inn], 'jca', '( %s -> ( %s /\\ i e. NN0 ) )' % (ph2, PH_LL)), w.inst('tmcadsum')], 'syl',
              '( %s -> ( ( %s sumBit %s ) ` ( %s ` i ) ) = %s )' % (ph2, BIT('L', 'i'), BIT("L'", 'i'), CRS, IFS))
    sm3 = w.s([sm, sm2], 'eqtrd', '( %s -> ( ( ( bitOf ` ( TMra ` p ) ) sumBit ( bitOf ` ( TMrb ` p ) ) ) ` ( TMcar ` p ) ) = %s )' % (ph2, IFS))
    pv2 = w.s([pv, w.s([sm3], 'opeq2d', '( %s -> %s = <. 1 , %s >. )' % (ph2, PSUM_X('p'), IFS))], 'eqtrd', '( %s -> ( %s ` p ) = <. 1 , %s >. )' % (ph2, PSUM, IFS))
    zv = w.s([w.s([lls, ifo], 'jca', '( %s -> ( %s /\\ i e. ( 0 ..^ %s ) ) )' % (ph2, PH_LL, MXA)), w.inst('tmcadzv')], 'syl',
             '( %s -> ( %s ` i ) = <. 1 , %s >. )' % (ph2, ZS, IFS))
    t2 = w.s([pv2, zv], 'eqtr4d', '( %s -> ( %s ` p ) = ( %s ` i ) )' % (ph2, PSUM, ZS))
    # (3) the load
    rcl = lambda f: w.s([pmem, w.inst('tmc%scl' % f)], 'syl', '( %s -> ( %s ` p ) e. %s )' % (ph2, ACC[f], CODOM[f]))
    bo = lambda f: w.s([rcl(f), w.inst('bitofcl')], 'syl', '( %s -> ( bitOf ` ( %s ` p ) ) e. 2o )' % (ph2, ACC[f]))
    mc = w.s([bo('ra'), bo('rb'), rcl('car'), w.inst('majcl')], 'syl3anc', '( %s -> %s e. 2o )' % (ph2, MAJ_X('p')))
    lv = load_val(w, ph2, lambda t: dict(car=MAJ_X(t)), 'p', pmem, {MAJ_X('p'): mc})
    LM = '( %s ` p )' % LMAJ
    i1 = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> ( i + 1 ) e. NN0 )' % ph2)
    NT = ncond_tree(CRS, LM, '( i + 1 )')
    cp = w.s([w.s([lls, inn], 'jca', '( %s -> ( %s /\\ i e. NN0 ) )' % (ph2, PH_LL)), w.inst('tmcadcp')], 'syl',
             '( %s -> ( %s ` ( i + 1 ) ) = ( ( %s majBit %s ) ` ( %s ` i ) ) )' % (ph2, CRS, BIT('L', 'i'), BIT("L'", 'i'), CRS))
    car2 = w.s([w.s([lv['fields']['car'], fold('majBit')], 'eqtrd', '( %s -> ( TMcar ` %s ) = ( ( %s majBit %s ) ` ( %s ` i ) ) )'
                    % (ph2, LM, BIT('L', 'i'), BIT("L'", 'i'), CRS)), cp], 'eqtr4d', '( %s -> %s )' % (ph2, NT[0][0]))
    def flg(fld, L_, lnst, k):
        LNx = '( # ` %s )' % L_
        bi = w.s([lnst, inn, w.inst('nn0leltp1')], 'syl2anc', '( %s -> ( %s <_ i <-> %s < ( i + 1 ) ) )' % (ph2, LNx, LNx))
        ib = w.s([bi], 'ifbid', '( %s -> %s = %s )' % (ph2, FLG(L_, '<_', 'i'), FLG(L_, '<', '( i + 1 )')))
        return w.s([w.s([lv['fields'][fld], pp[OT[0][k]]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, ACC[fld], LM, FLG(L_, '<_', 'i'))), ib],
                   'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, ACC[fld], LM, FLG(L_, '<', '( i + 1 )'))), bi
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
        e = w.s([w.s([w.s([lv['fields'][fld], pp[OT[1][k]]], 'eqtrd', '( %s -> ( %s ` %s ) = %s )' % (ph2, ACC[fld], LM, RGV(L_, 'i')))], 'adantr',
                     '( %s -> ( %s ` %s ) = %s )' % (p3, ACC[fld], LM, RGV(L_, 'i'))),
                 w.s([nlt], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (p3, RGV(L_, 'i')))], 'eqtrd', '( %s -> ( %s ` %s ) = ( inr ` (/) ) )' % (p3, ACC[fld], LM))
        return w.s([e], 'ex', '( %s -> ( %s < ( i + 1 ) -> ( %s ` %s ) = ( inr ` (/) ) ) )' % (ph2, LNx, ACC[fld], LM))
    ra2 = regnone('ra', 'L', bia, 0)
    rb2 = regnone('rb', "L'", bib, 1)
    nc = w.s([w.s([car2, da2, db2], '3jca', '( %s -> %s )' % (ph2, cj(NT[0]))), w.s([ra2, rb2], 'jca', '( %s -> %s )' % (ph2, cj(NT[1])))],
             'jca', '( %s -> %s )' % (ph2, cj(NT)))
    t3 = fam_pack(w, ph2, NCOND(CRS), '( i + 1 )', i1, LM, lv['mem'], nc)
    BODY = '( -. ( %s ` p ) = 1o /\\ ( %s ` p ) = ( %s ` i ) /\\ ( %s ` p ) e. ( %s ` ( i + 1 ) ) )' % (CANDD, PSUM, ZS, LMAJ, NFA)
    j = w.s([t1, t2, t3], '3jca', '( %s -> %s )' % (ph2, BODY))
    w.qed([j], 'ralrimivva', ST_ADBD)
    return w.run()


def tmcadfl():
    ph = '( ( 2nd ` T ) = TMSt /\\ %s )' % PH_LL
    w = W('tmcadfl', 'The adder\'s exit at the machine (T5 D3\'s flush disjunction): after the last iteration both '
                     'operands are exhausted; a final carry pushes the letter ` <. 1 , 1o >. ` and the sum word is '
                     'the sum bits then the carry (Lean ` addBits ` , T4 ~ addbitsfold ).')
    seq = w.s([], 'simpl', '( %s -> %s )' % (ph, SEQ))
    lls = w.s([], 'simpr', '( %s -> %s )' % (ph, PH_LL))
    ll = w.s([lls], 'simpld', '( %s -> L e. Word 2o )' % ph)
    ll2 = w.s([lls], 'simprd', "( %s -> L' e. Word 2o )" % ph)
    b, sz, mx = zbasics(w, ph, ll, ll2)
    zl = w.s([lls, w.inst('tmcadzl')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, ZS, MXA))
    CRM = '( %s ` %s )' % (CRS, MXA)
    crc = w.s([carry_hyps(w, ph, b['ta'], b['tb'], mx, MXA), w.inst('bwcarrycl')], 'syl', '( %s -> %s e. 2o )' % (ph, CRM))
    OFZ = '( %s ` ( # ` %s ) )' % (OFA, ZS)
    oeq = w.s([zl], 'fveq2d', '( %s -> %s = ( %s ` %s ) )' % (ph, OFZ, OFA, MXA))
    # facts about a state of the exit class
    phq = '( %s /\\ p e. %s )' % (ph, OFZ)
    Aq = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (phq, f))
    pz = w.s([], 'simpr', '( %s -> p e. %s )' % (phq, OFZ))
    pin = w.s([pz, Aq(oeq, '%s = ( %s ` %s )' % (OFZ, OFA, MXA))], 'eleqtrd', '( %s -> p e. ( %s ` %s ) )' % (phq, OFA, MXA))
    mxq = Aq(mx, '%s e. NN0' % MXA)
    pmem, pc = fam_unpack(w, phq, OCOND(CRS), MXA, mxq, 'p', pin)
    OT = ocond_tree(CRS, 'p', MXA)
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
    ps = w.s([pmem, Aq(seq, SEQ)], 'eleqtrrd', '( %s -> p e. ( 2nd ` T ) )' % phq)
    c11 = w.s([closed(w, phq, 'opex', '<. 1 , 1o >. e. _V'), ps, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` p ) = <. 1 , 1o >. )' % (phq, C11))
    carp = pp[OT[0][0]]
    # the sum word
    BW = '( %s bwrd %s )' % (SUMV, MXA)
    AC = '( addCarry ` %s )' % CRM
    wf = w.s([ll, ll2, closed(w, ph, '0el2o', '(/) e. 2o'), w.inst('addbitsfold')], 'syl3anc',
             "( %s -> ( ( L addBits L' ) ` (/) ) = ( %s ++ %s ) )" % (ph, BW, AC))
    wa1 = w.s([wf], 'coeq2d', "( %s -> %s = ( inclBool o. ( %s ++ %s ) ) )" % (ph, WA, BW, AC))
    bw = w.s([sz, mx, w.inst('bwrdcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ph, BW))
    acw = w.s([crc, w.inst('addcarrycl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, AC))
    mc = w.s([bw, acw, w.inst('bwmapccat')], 'syl2anc', '( %s -> ( inclBool o. ( %s ++ %s ) ) = ( %s ++ ( inclBool o. %s ) ) )' % (ph, BW, AC, ZS, AC))
    wa2 = w.s([wa1, mc], 'eqtrd', '( %s -> %s = ( %s ++ ( inclBool o. %s ) ) )' % (ph, WA, ZS, AC))
    ifl = closed(w, ph, 'tmcinclf', 'inclBool : 2o --> %s' % BITS)
    zw = w.s([bw, ifl, w.inst('wrdco')], 'syl2anc', '( %s -> %s e. Word %s )' % (ph, ZS, BITS))
    LEFT_P = '( ( ( %s ` p ) = 1o /\\ ( TMcar ` p ) = 1o ) /\\ ( ( %s ` p ) = <. 1 , 1o >. /\\ p e. TMSt ) )' % (CANDD, C11)
    RIGHT_P = '( ( %s ` p ) = 1o /\\ -. ( TMcar ` p ) = 1o /\\ p e. TMSt )' % CANDD
    LEFT = '( A. p e. %s %s /\\ %s = ( %s ++ <" <. 1 , 1o >. "> ) )' % (OFZ, LEFT_P, WA, ZS)
    RIGHT = '( A. p e. %s %s /\\ %s = %s )' % (OFZ, RIGHT_P, WA, ZS)
    GOAL = '( %s \\/ %s )' % (LEFT, RIGHT)
    # case carry
    p1 = '( %s /\\ %s = 1o )' % (ph, CRM)
    c1 = w.s([], 'simpr', '( %s -> %s = 1o )' % (p1, CRM))
    ac1 = w.s([w.s([c1], 'fveq2d', '( %s -> %s = ( addCarry ` 1o ) )' % (p1, AC)), closed(w, p1, 'addcarry1', '( addCarry ` 1o ) = <" 1o ">')], 'eqtrd',
              '( %s -> %s = <" 1o "> )' % (p1, AC))
    ib = w.s([closed(w, p1, '1oel2o', '1o e. 2o'), w.s([ifl], 'adantr', '( %s -> inclBool : 2o --> %s )' % (p1, BITS)), w.inst('s1co')], 'syl2anc',
             '( %s -> ( inclBool o. <" 1o "> ) = <" ( inclBool ` 1o ) "> )' % p1)
    ib2 = w.s([ib, w.s([w.s([closed(w, p1, '1oel2o', '1o e. 2o'), w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` 1o ) = <. 1 , 1o >. )' % p1)], 's1eqd',
                       '( %s -> <" ( inclBool ` 1o ) "> = <" <. 1 , 1o >. "> )' % p1)], 'eqtrd', '( %s -> ( inclBool o. <" 1o "> ) = <" <. 1 , 1o >. "> )' % p1)
    ic1 = w.s([w.s([ac1], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. <" 1o "> ) )' % (p1, AC)), ib2], 'eqtrd',
              '( %s -> ( inclBool o. %s ) = <" <. 1 , 1o >. "> )' % (p1, AC))
    w1 = w.s([w.s([wa2], 'adantr', '( %s -> %s = ( %s ++ ( inclBool o. %s ) ) )' % (p1, WA, ZS, AC)), w.s([ic1], 'oveq2d',
             '( %s -> ( %s ++ ( inclBool o. %s ) ) = ( %s ++ <" <. 1 , 1o >. "> ) )' % (p1, ZS, AC, ZS))], 'eqtrd', '( %s -> %s = ( %s ++ <" <. 1 , 1o >. "> ) )' % (p1, WA, ZS))
    pq1 = '( %s /\\ p e. %s )' % (p1, OFZ)
    L_ = lambda st, f: w.s([st], 'adantlr', '( %s -> %s )' % (pq1, f))
    carq = w.s([L_(carp, '( TMcar ` p ) = %s' % CRM), w.s([c1], 'adantr', '( %s -> %s = 1o )' % (pq1, CRM))], 'eqtrd', '( %s -> ( TMcar ` p ) = 1o )' % pq1)
    lp = w.s([w.s([L_(cand, '( %s ` p ) = 1o' % CANDD), carq], 'jca', '( %s -> ( ( %s ` p ) = 1o /\\ ( TMcar ` p ) = 1o ) )' % (pq1, CANDD)),
              w.s([L_(c11, '( %s ` p ) = <. 1 , 1o >.' % C11), L_(pmem, 'p e. TMSt')], 'jca', '( %s -> ( ( %s ` p ) = <. 1 , 1o >. /\\ p e. TMSt ) )' % (pq1, C11))],
             'jca', '( %s -> %s )' % (pq1, LEFT_P))
    lr = w.s([lp], 'ralrimiva', '( %s -> A. p e. %s %s )' % (p1, OFZ, LEFT_P))
    case1 = w.s([w.s([lr, w1], 'jca', '( %s -> %s )' % (p1, LEFT))], 'orcd', '( %s -> %s )' % (p1, GOAL))
    # case no carry
    p0 = '( %s /\\ -. %s = 1o )' % (ph, CRM)
    n0 = w.s([], 'simpr', '( %s -> -. %s = 1o )' % (p0, CRM))
    cz = w.s([n0, w.s([w.s([crc], 'adantr', '( %s -> %s e. 2o )' % (p0, CRM)), w.inst('bwel2on')], 'syl', '( %s -> ( -. %s = 1o <-> %s = (/) ) )' % (p0, CRM, CRM))],
             'mpbid', '( %s -> %s = (/) )' % (p0, CRM))
    ac0 = w.s([w.s([cz], 'fveq2d', '( %s -> %s = ( addCarry ` (/) ) )' % (p0, AC)), closed(w, p0, 'addcarry0', '( addCarry ` (/) ) = (/)')], 'eqtrd',
              '( %s -> %s = (/) )' % (p0, AC))
    ic0 = w.s([w.s([ac0], 'coeq2d', '( %s -> ( inclBool o. %s ) = ( inclBool o. (/) ) )' % (p0, AC)), closed(w, p0, 'co02', '( inclBool o. (/) ) = (/)')],
              'eqtrd', '( %s -> ( inclBool o. %s ) = (/) )' % (p0, AC))
    w0 = w.s([w.s([w.s([wa2], 'adantr', '( %s -> %s = ( %s ++ ( inclBool o. %s ) ) )' % (p0, WA, ZS, AC)),
                   w.s([ic0], 'oveq2d', '( %s -> ( %s ++ ( inclBool o. %s ) ) = ( %s ++ (/) ) )' % (p0, ZS, AC, ZS))], 'eqtrd', '( %s -> %s = ( %s ++ (/) ) )' % (p0, WA, ZS)),
              w.s([w.s([zw], 'adantr', '( %s -> %s e. Word %s )' % (p0, ZS, BITS)), w.inst('ccatrid')], 'syl', '( %s -> ( %s ++ (/) ) = %s )' % (p0, ZS, ZS))],
             'eqtrd', '( %s -> %s = %s )' % (p0, WA, ZS))
    pq0 = '( %s /\\ p e. %s )' % (p0, OFZ)
    L0 = lambda st, f: w.s([st], 'adantlr', '( %s -> %s )' % (pq0, f))
    ncq = w.s([w.s([L0(carp, '( TMcar ` p ) = %s' % CRM)], 'eqeq1d', '( %s -> ( ( TMcar ` p ) = 1o <-> %s = 1o ) )' % (pq0, CRM)),
               w.s([n0], 'adantr', '( %s -> -. %s = 1o )' % (pq0, CRM))], 'mtbird', '( %s -> -. ( TMcar ` p ) = 1o )' % pq0)
    rp = w.s([L0(cand, '( %s ` p ) = 1o' % CANDD), ncq, L0(pmem, 'p e. TMSt')], '3jca', '( %s -> %s )' % (pq0, RIGHT_P))
    rr = w.s([rp], 'ralrimiva', '( %s -> A. p e. %s %s )' % (p0, OFZ, RIGHT_P))
    case0 = w.s([w.s([rr, w0], 'jca', '( %s -> %s )' % (p0, RIGHT))], 'olcd', '( %s -> %s )' % (p0, GOAL))
    em = w.s([], 'exmidd', '( %s -> ( %s = 1o \\/ -. %s = 1o ) )' % (ph, CRM, CRM))
    jo = w.s([case1, case0], 'jaodan', '( ( %s /\\ ( %s = 1o \\/ -. %s = 1o ) ) -> %s )' % (ph, CRM, CRM, GOAL))
    w.qed([em, jo], 'mpdan', '( %s -> %s )' % (ph, GOAL))
    assert '( %s -> %s )' % (ph, GOAL) == ST_ADFL
    return w.run()


if __name__ == '__main__':
    if want('tmc2oif'): tmc2oif()
    if want('tmcbrg'): tmcbrg()
    if want('tmcadc0'): tmcadc0()
    if want('tmcadsum'): tmcadsum()
    if want('tmcadcp'): tmcadcp()
    if want('tmcadzl'): tmcadzl()
    if want('tmcadzv'): tmcadzv()
    if want('tmcadss'): tmcadss()
    if want('tmcadin'): tmcadin()
    if want('tmcadrd'): tmcadrd()
    if want('tmcadbd'): tmcadbd()
    if want('tmcadfl'): tmcadfl()
