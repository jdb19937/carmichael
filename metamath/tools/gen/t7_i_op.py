"""T7: the operand families of the two-operand loops (T5 D4) at the machine:
the stack of an operand after N reads ( OPF ) and the letter of the N-th read
( OPU ), their typing, value at 0 and past the terminator, and the step
equation of ~ tm2fadd / ~ tm2fsub / ~ tm2fcmp 's family hypothesis."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7lib import *
from cl import Closure

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

IB = '( inclBool o. L )'
Y4X = '( <" 4 "> ++ X )'
LN = '( # ` L )'
SW = lambda t: '( %s substr <. %s , %s >. )' % (IB, t, LN)
FB = lambda t: 'if ( %s <_ %s , ( %s ++ %s ) , X )' % (t, LN, SW(t), Y4X)
UB = lambda t: 'if ( %s < %s , <. 1 , ( L ` %s ) >. , 4 )' % (t, LN, t)
F = OPFX
U = OPUX
assert F == '( j e. NN0 |-> %s )' % FB('j') and U == '( j e. NN0 |-> %s )' % UB('j')
WG_ = "Word Gamma'"


def basics(w, ph, ll, xg):
    """IB typings and the length"""
    ibw = w.s([ll, w.inst('tmcibw')], 'syl', '( %s -> %s e. Word %s )' % (ph, IB, BITS))
    ss = closed(w, ph, 'tm2lbits', "%s C_ Gamma'" % BITS)
    ssw = w.s([ss, w.inst('sswrd')], 'syl', "( %s -> Word %s C_ Word Gamma' )" % (ph, BITS))
    ibg = w.s([ssw, ibw], 'sseldd', "( %s -> %s e. Word Gamma' )" % (ph, IB))
    ibl = w.s([ll, w.inst('bwmaplen')], 'syl', '( %s -> ( # ` %s ) = %s )' % (ph, IB, LN))
    ln = w.s([ll, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LN))
    g4 = closed(w, ph, 'gamma4', "4 e. Gamma'")
    s4 = w.s([g4], 's1cld', "( %s -> <\" 4 \"> e. Word Gamma' )" % ph)
    y4x = w.s([s4, xg, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, Y4X))
    return dict(ibw=ibw, ibg=ibg, ibl=ibl, ln=ln, g4=g4, s4=s4, y4x=y4x)


def fbty(w, ph, b, xg, t):
    """( ph -> FB( t ) e. Word Gamma' )"""
    sw = w.s([b['ibg'], w.inst('swrdcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, SW(t)))
    c = w.s([sw, b['y4x'], w.inst('ccatcl')], 'syl2anc', "( %s -> ( %s ++ %s ) e. Word Gamma' )" % (ph, SW(t), Y4X))
    return w.s([c, xg], 'ifcld', "( %s -> %s e. Word Gamma' )" % (ph, FB(t)))


def fval(w, ph, b, xg, t, tn):
    """( ph -> ( F ` t ) = FB( t ) ) and the typing of FB( t )"""
    ty = fbty(w, ph, b, xg, t)
    return mval(w, ph, 'j', 'NN0', FB, t, tn, elexs(w, ph, ty, FB(t))), ty


def uval(w, ph, t, tn, uty):
    return mval(w, ph, 'j', 'NN0', UB, t, tn, elexs(w, ph, uty, UB(t)))


def tmcopty():
    ph = PH_OP
    w = W('tmcopty', 'The stack of an operand of a two-operand loop after ` N ` reads is a word over the machine '
                     'alphabet.')
    ll = w.s([], 'simp1', '( %s -> L e. Word 2o )' % ph)
    xg = w.s([], 'simp2', "( %s -> X e. Word Gamma' )" % ph)
    nn = w.s([], 'simp3', '( %s -> N e. NN0 )' % ph)
    b = basics(w, ph, ll, xg)
    v, ty = fval(w, ph, b, xg, 'N', nn)
    w.qed([v, ty], 'eqeltrd', "( %s -> ( %s ` N ) e. Word Gamma' )" % (ph, F))
    return w.run()


def tmcop0():
    ph = "( L e. Word 2o /\\ X e. Word Gamma' )"
    w = W('tmcop0', 'Before the first read the operand stack holds the whole bit word, the terminator and the rest.')
    ll = w.s([], 'simpl', '( %s -> L e. Word 2o )' % ph)
    xg = w.s([], 'simpr', "( %s -> X e. Word Gamma' )" % ph)
    b = basics(w, ph, ll, xg)
    z = closed(w, ph, '0nn0', '0 e. NN0')
    v, _ = fval(w, ph, b, xg, '0', z)
    le = w.s([b['ln']], 'nn0ge0d', '( %s -> 0 <_ %s )' % (ph, LN))
    it = w.s([le], 'iftrued', '( %s -> %s = ( %s ++ %s ) )' % (ph, FB('0'), SW('0'), Y4X))
    e1 = w.s([b['ibl']], 'eqcomd', '( %s -> %s = ( # ` %s ) )' % (ph, LN, IB))
    e2 = w.s([e1], 'opeq2d', '( %s -> <. 0 , %s >. = <. 0 , ( # ` %s ) >. )' % (ph, LN, IB))
    e3 = w.s([e2], 'oveq2d', '( %s -> %s = ( %s substr <. 0 , ( # ` %s ) >. ) )' % (ph, SW('0'), IB, IB))
    d0 = w.s([b['ibw'], w.inst('tm2ldrop0')], 'syl', '( %s -> ( %s substr <. 0 , ( # ` %s ) >. ) = %s )' % (ph, IB, IB, IB))
    e4 = w.s([e3, d0], 'eqtrd', '( %s -> %s = %s )' % (ph, SW('0'), IB))
    e5 = w.s([e4], 'oveq1d', '( %s -> ( %s ++ %s ) = ( %s ++ %s ) )' % (ph, SW('0'), Y4X, IB, Y4X))
    w.qed([w.s([v, it], 'eqtrd', '( %s -> ( %s ` 0 ) = ( %s ++ %s ) )' % (ph, F, SW('0'), Y4X)), e5], 'eqtrd',
          '( %s -> ( %s ` 0 ) = ( %s ++ %s ) )' % (ph, F, IB, Y4X))
    return w.run()


def tmcope():
    ph = "( ( L e. Word 2o /\\ X e. Word Gamma' ) /\\ ( N e. NN0 /\\ ( # ` L ) < N ) )"
    w = W('tmcope', 'After the terminator is read the operand stack is the rest.')
    ll = w.s([], 'simpll', '( %s -> L e. Word 2o )' % ph)
    xg = w.s([], 'simplr', "( %s -> X e. Word Gamma' )" % ph)
    nn = w.s([], 'simprl', '( %s -> N e. NN0 )' % ph)
    lt = w.s([], 'simprr', '( %s -> %s < N )' % (ph, LN))
    b = basics(w, ph, ll, xg)
    v, _ = fval(w, ph, b, xg, 'N', nn)
    c = Closure(w, ph, {'N': ('NN0', nn), LN: ('NN0', b['ln'])})
    bi = w.s([c.mem(LN, 'RR'), c.mem('N', 'RR')], 'ltnled', '( %s -> ( %s < N <-> -. N <_ %s ) )' % (ph, LN, LN))
    nle = w.s([lt, bi], 'mpbid', '( %s -> -. N <_ %s )' % (ph, LN))
    it = w.s([nle], 'iffalsed', '( %s -> %s = X )' % (ph, FB('N')))
    w.qed([v, it], 'eqtrd', '( %s -> ( %s ` N ) = X )' % (ph, F))
    return w.run()


def elfz0(w, ph, a, bnd, an, bn, le):
    """( ph -> a e. ( 0 ... bnd ) ) from a, bnd in NN0 and a <_ bnd"""
    j = w.s([an, bn, le], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (ph, a, bnd, a, bnd))
    e = w.s([], 'elfz2nn0', '( %s e. ( 0 ... %s ) <-> ( %s e. NN0 /\\ %s e. NN0 /\\ %s <_ %s ) )' % (a, bnd, a, bnd, a, bnd))
    return w.s([j, e], 'sylibr', '( %s -> %s e. ( 0 ... %s ) )' % (ph, a, bnd))


def tmcop1():
    ph = PH_OP
    R = OPR('L')
    w = W('tmcop1', 'The step equation of an operand family (T5 D4): on the read set ` ( 0 ... ( # ` L ) ) ` '
                    'the stack loses its top letter, the ` N ` -th bit letter or the terminator; past it the '
                    'stack stays the rest.')
    ll = w.s([], 'simp1', '( %s -> L e. Word 2o )' % ph)
    xg = w.s([], 'simp2', "( %s -> X e. Word Gamma' )" % ph)
    nn = w.s([], 'simp3', '( %s -> N e. NN0 )' % ph)
    b = basics(w, ph, ll, xg)
    n1 = w.s([nn, w.inst('peano2nn0')], 'syl', '( %s -> ( N + 1 ) e. NN0 )' % ph)
    NP1 = '( N + 1 )'
    GOAL_A = '( %s ` N ) = ( <" ( %s ` N ) "> ++ ( %s ` %s ) )' % (F, U, F, NP1)
    # ---- (a) on the read set
    ph1 = '( %s /\\ N e. %s )' % (ph, R)
    A1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (ph1, f))
    nr = w.s([], 'simpr', '( %s -> N e. %s )' % (ph1, R))
    nle = w.s([nr, w.inst('elfzle2')], 'syl', '( %s -> N <_ %s )' % (ph1, LN))
    nn1 = A1(nn, 'N e. NN0'); ll1 = A1(ll, 'L e. Word 2o'); xg1 = A1(xg, "X e. Word Gamma'")
    b1 = basics(w, ph1, ll1, xg1)
    c1 = Closure(w, ph1, {'N': ('NN0', nn1), LN: ('NN0', b1['ln'])})
    fN, _ = fval(w, ph1, b1, xg1, 'N', nn1)
    fNt = w.s([nle], 'iftrued', '( %s -> %s = ( %s ++ %s ) )' % (ph1, FB('N'), SW('N'), Y4X))
    fN2 = w.s([fN, fNt], 'eqtrd', '( %s -> ( %s ` N ) = ( %s ++ %s ) )' % (ph1, F, SW('N'), Y4X))
    disj = w.s([c1.mem('N', 'RR'), c1.mem(LN, 'RR'), w.inst('leloe')], 'syl2anc',
               '( %s -> ( N <_ %s <-> ( N < %s \\/ N = %s ) ) )' % (ph1, LN, LN, LN))
    disj2 = w.s([nle, disj], 'mpbid', '( %s -> ( N < %s \\/ N = %s ) )' % (ph1, LN, LN))
    # case N < |L|
    pa = '( %s /\\ N < %s )' % (ph1, LN)
    Aa = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (pa, f))
    lt = w.s([], 'simpr', '( %s -> N < %s )' % (pa, LN))
    nna = Aa(nn1, 'N e. NN0'); lla = Aa(ll1, 'L e. Word 2o'); xga = Aa(xg1, "X e. Word Gamma'")
    ba = basics(w, pa, lla, xga)
    ca = Closure(w, pa, {'N': ('NN0', nna), LN: ('NN0', ba['ln'])})
    n1a = w.s([nna, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pa, NP1))
    fNa = Aa(fN2, '( %s ` N ) = ( %s ++ %s )' % (F, SW('N'), Y4X))
    lnz = ca.mem(LN, 'ZZ')
    # N e. ( 0 ..^ |L| )
    ez = w.s([ca.mem('N', 'ZZ'), closed(w, pa, '0z', '0 e. ZZ'), lnz, w.inst('elfzo')], 'syl3anc',
             '( %s -> ( N e. ( 0 ..^ %s ) <-> ( 0 <_ N /\\ N < %s ) ) )' % (pa, LN, LN))
    nfo = w.s([ez, w.s([ca.ge0('N'), lt], 'jca', '( %s -> ( 0 <_ N /\\ N < %s ) )' % (pa, LN))], 'mpbird',
              '( %s -> N e. ( 0 ..^ %s ) )' % (pa, LN))
    ibla = ba['ibl']
    fo = w.s([w.s([ibla], 'oveq2d', '( %s -> ( 0 ..^ ( # ` %s ) ) = ( 0 ..^ %s ) )' % (pa, IB, LN)), nfo], 'eleqtrrd',
             '( %s -> N e. ( 0 ..^ ( # ` %s ) ) )' % (pa, IB))
    # the letter
    lf = w.s([lla, w.inst('wrdf')], 'syl', '( %s -> L : ( 0 ..^ %s ) --> 2o )' % (pa, LN))
    ibv = w.s([lf, nfo, w.inst('fvco3')], 'syl2anc', '( %s -> ( %s ` N ) = ( inclBool ` ( L ` N ) ) )' % (pa, IB))
    lnb = w.s([lla, nfo, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` N ) e. 2o )' % pa)
    inc = w.s([lnb, w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` ( L ` N ) ) = <. 1 , ( L ` N ) >. )' % pa)
    ibv2 = w.s([ibv, inc], 'eqtrd', '( %s -> ( %s ` N ) = <. 1 , ( L ` N ) >. )' % (pa, IB))
    s1 = w.s([ba['ibw'], fo, w.inst('swrds1')], 'syl2anc', '( %s -> ( %s substr <. N , %s >. ) = <" ( %s ` N ) "> )' % (pa, IB, NP1, IB))
    s1b = w.s([s1, w.s([ibv2], 's1eqd', '( %s -> <" ( %s ` N ) "> = <" <. 1 , ( L ` N ) >. "> )' % (pa, IB))], 'eqtrd',
              '( %s -> ( %s substr <. N , %s >. ) = <" <. 1 , ( L ` N ) >. "> )' % (pa, IB, NP1))
    # the split
    bi1 = w.s([nna, ba['ln'], w.inst('nn0ltp1le')], 'syl2anc', '( %s -> ( N < %s <-> %s <_ %s ) )' % (pa, LN, NP1, LN))
    n1le = w.s([lt, bi1], 'mpbid', '( %s -> %s <_ %s )' % (pa, NP1, LN))
    nlep = w.s([ca.mem('N', 'RR')], 'lep1d', '( %s -> N <_ %s )' % (pa, NP1))
    fz1 = elfz0(w, pa, 'N', NP1, nna, n1a, nlep)
    fz2 = elfz0(w, pa, NP1, LN, n1a, ba['ln'], n1le)
    fz3a = w.s([ba['ln'], w.s([], 'nn0fz0', '( %s e. NN0 <-> %s e. ( 0 ... %s ) )' % (LN, LN, LN))], 'sylib',
               '( %s -> %s e. ( 0 ... %s ) )' % (pa, LN, LN))
    fz3 = w.s([w.s([ibla], 'oveq2d', '( %s -> ( 0 ... ( # ` %s ) ) = ( 0 ... %s ) )' % (pa, IB, LN)), fz3a], 'eleqtrrd',
              '( %s -> %s e. ( 0 ... ( # ` %s ) ) )' % (pa, LN, IB))
    cs = w.s([ba['ibw'], fz1, fz2, fz3, w.inst('ccatswrd')], 'syl13anc',
             '( %s -> ( ( %s substr <. N , %s >. ) ++ %s ) = %s )' % (pa, IB, NP1, SW(NP1), SW('N')))
    cs2 = w.s([s1b], 'oveq1d', '( %s -> ( ( %s substr <. N , %s >. ) ++ %s ) = ( <" <. 1 , ( L ` N ) >. "> ++ %s ) )' % (pa, IB, NP1, SW(NP1), SW(NP1)))
    swN = w.s([cs, cs2], 'eqtr3d', '( %s -> %s = ( <" <. 1 , ( L ` N ) >. "> ++ %s ) )' % (pa, SW('N'), SW(NP1)))
    # assemble the left side
    LET = '<" <. 1 , ( L ` N ) >. ">'
    letg = w.s([w.s([lnb, w.inst('bitgamma')], 'syl', "( %s -> <. 1 , ( L ` N ) >. e. Gamma' )" % pa)], 's1cld',
               "( %s -> %s e. Word Gamma' )" % (pa, LET))
    sw1g = w.s([ba['ibg'], w.inst('swrdcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (pa, SW(NP1)))
    lhs1 = w.s([swN], 'oveq1d', '( %s -> ( %s ++ %s ) = ( ( %s ++ %s ) ++ %s ) )' % (pa, SW('N'), Y4X, LET, SW(NP1), Y4X))
    asc = w.s([letg, sw1g, ba['y4x'], w.inst('ccatass')], 'syl3anc',
              '( %s -> ( ( %s ++ %s ) ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (pa, LET, SW(NP1), Y4X, LET, SW(NP1), Y4X))
    lhs = w.s([fNa, w.s([lhs1, asc], 'eqtrd', '( %s -> ( %s ++ %s ) = ( %s ++ ( %s ++ %s ) ) )' % (pa, SW('N'), Y4X, LET, SW(NP1), Y4X))],
              'eqtrd', '( %s -> ( %s ` N ) = ( %s ++ ( %s ++ %s ) ) )' % (pa, F, LET, SW(NP1), Y4X))
    # the right side
    uty = w.s([w.s([lnb, w.inst('bitgamma')], 'syl', "( %s -> <. 1 , ( L ` N ) >. e. Gamma' )" % pa), ba['g4']], 'ifcld',
              "( %s -> %s e. Gamma' )" % (pa, UB('N')))
    uv = uval(w, pa, 'N', nna, uty)
    uv2 = w.s([uv, w.s([lt], 'iftrued', '( %s -> %s = <. 1 , ( L ` N ) >. )' % (pa, UB('N')))], 'eqtrd',
              '( %s -> ( %s ` N ) = <. 1 , ( L ` N ) >. )' % (pa, U))
    f1, _ = fval(w, pa, ba, xga, NP1, n1a)
    f1b = w.s([f1, w.s([n1le], 'iftrued', '( %s -> %s = ( %s ++ %s ) )' % (pa, FB(NP1), SW(NP1), Y4X))], 'eqtrd',
              '( %s -> ( %s ` %s ) = ( %s ++ %s ) )' % (pa, F, NP1, SW(NP1), Y4X))
    rhs = w.s([w.s([uv2], 's1eqd', '( %s -> <" ( %s ` N ) "> = %s )' % (pa, U, LET)), f1b], 'oveq12d',
              '( %s -> ( <" ( %s ` N ) "> ++ ( %s ` %s ) ) = ( %s ++ ( %s ++ %s ) ) )' % (pa, U, F, NP1, LET, SW(NP1), Y4X))
    casea = w.s([lhs, rhs], 'eqtr4d', '( %s -> %s )' % (pa, GOAL_A))
    # case N = |L|
    pb = '( %s /\\ N = %s )' % (ph1, LN)
    Ab = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (pb, f))
    eq = w.s([], 'simpr', '( %s -> N = %s )' % (pb, LN))
    nnb = Ab(nn1, 'N e. NN0'); llb = Ab(ll1, 'L e. Word 2o'); xgb = Ab(xg1, "X e. Word Gamma'")
    bb = basics(w, pb, llb, xgb)
    cb = Closure(w, pb, {'N': ('NN0', nnb), LN: ('NN0', bb['ln'])})
    fNb = Ab(fN2, '( %s ` N ) = ( %s ++ %s )' % (F, SW('N'), Y4X))
    e1 = w.s([eq], 'opeq1d', '( %s -> <. N , %s >. = <. %s , %s >. )' % (pb, LN, LN, LN))
    e2 = w.s([e1], 'oveq2d', '( %s -> %s = ( %s substr <. %s , %s >. ) )' % (pb, SW('N'), IB, LN, LN))
    e3 = w.s([e2, closed(w, pb, 'swrd00', '( %s substr <. %s , %s >. ) = (/)' % (IB, LN, LN))], 'eqtrd', '( %s -> %s = (/) )' % (pb, SW('N')))
    e4 = w.s([e3], 'oveq1d', '( %s -> ( %s ++ %s ) = ( (/) ++ %s ) )' % (pb, SW('N'), Y4X, Y4X))
    e5 = w.s([bb['y4x'], w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (pb, Y4X, Y4X))
    lhsb = w.s([fNb, w.s([e4, e5], 'eqtrd', '( %s -> ( %s ++ %s ) = %s )' % (pb, SW('N'), Y4X, Y4X))], 'eqtrd',
               '( %s -> ( %s ` N ) = %s )' % (pb, F, Y4X))
    nlt0 = w.s([cb.mem(LN, 'RR')], 'ltnrd', '( %s -> -. %s < %s )' % (pb, LN, LN))
    nlt1 = w.s([eq], 'breq1d', '( %s -> ( N < %s <-> %s < %s ) )' % (pb, LN, LN, LN))
    nlt = w.s([nlt1, nlt0], 'mtbird', '( %s -> -. N < %s )' % (pb, LN))
    # the letter's typing without the bit case: L ` N in the else branch is irrelevant, use ifclda
    phu = '( %s /\\ N < %s )' % (pb, LN)
    uv = w.s([w.s([nlt], 'iffalsed', '( %s -> %s = 4 )' % (pb, UB('N'))), bb['g4']], 'eqeltrd', "( %s -> %s e. Gamma' )" % (pb, UB('N')))
    uvb = uval(w, pb, 'N', nnb, uv)
    uvb2 = w.s([uvb, w.s([nlt], 'iffalsed', '( %s -> %s = 4 )' % (pb, UB('N')))], 'eqtrd', '( %s -> ( %s ` N ) = 4 )' % (pb, U))
    n1b = w.s([nnb, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (pb, NP1))
    ltp = w.s([cb.mem('N', 'RR')], 'ltp1d', '( %s -> N < %s )' % (pb, NP1))
    bq = w.s([eq], 'breq1d', '( %s -> ( N < %s <-> %s < %s ) )' % (pb, NP1, LN, NP1))
    ltp2 = w.s([ltp, bq], 'mpbid', '( %s -> %s < %s )' % (pb, LN, NP1))
    bi2 = w.s([cb.mem(LN, 'RR'), cb.mem(NP1, 'RR')], 'ltnled', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (pb, LN, NP1, NP1, LN))
    nle1 = w.s([ltp2, bi2], 'mpbid', '( %s -> -. %s <_ %s )' % (pb, NP1, LN))
    f1, _ = fval(w, pb, bb, xgb, NP1, n1b)
    f1x = w.s([f1, w.s([nle1], 'iffalsed', '( %s -> %s = X )' % (pb, FB(NP1)))], 'eqtrd', '( %s -> ( %s ` %s ) = X )' % (pb, F, NP1))
    rhsb = w.s([w.s([uvb2], 's1eqd', '( %s -> <" ( %s ` N ) "> = <" 4 "> )' % (pb, U)), f1x], 'oveq12d',
               '( %s -> ( <" ( %s ` N ) "> ++ ( %s ` %s ) ) = %s )' % (pb, U, F, NP1, Y4X))
    caseb = w.s([lhsb, rhsb], 'eqtr4d', '( %s -> %s )' % (pb, GOAL_A))
    jo = w.s([casea, caseb], 'jaodan', '( ( %s /\\ ( N < %s \\/ N = %s ) ) -> %s )' % (ph1, LN, LN, GOAL_A))
    ga = w.s([disj2, jo], 'mpdan', '( %s -> %s )' % (ph1, GOAL_A))
    A_ = w.s([ga], 'ex', '( %s -> ( N e. %s -> %s ) )' % (ph, R, GOAL_A))
    # ---- (b) off the read set
    ph3 = '( %s /\\ -. N e. %s )' % (ph, R)
    GOAL_B = '( %s ` %s ) = ( %s ` N )' % (F, NP1, F)
    phle = '( %s /\\ N <_ %s )' % (ph, LN)
    ci = elfz0(w, phle, 'N', LN, w.s([nn], 'adantr', '( %s -> N e. NN0 )' % phle), w.s([b['ln']], 'adantr', '( %s -> %s e. NN0 )' % (phle, LN)),
               w.s([], 'simpr', '( %s -> N <_ %s )' % (phle, LN)))
    cie = w.s([ci], 'ex', '( %s -> ( N <_ %s -> N e. %s ) )' % (ph, LN, R))
    cic = w.s([cie], 'con3d', '( %s -> ( -. N e. %s -> -. N <_ %s ) )' % (ph, R, LN))
    nle3 = w.s([cic], 'imp', '( %s -> -. N <_ %s )' % (ph3, LN))
    nn3 = w.s([nn], 'adantr', '( %s -> N e. NN0 )' % ph3)
    ll3 = w.s([ll], 'adantr', '( %s -> L e. Word 2o )' % ph3); xg3 = w.s([xg], 'adantr', "( %s -> X e. Word Gamma' )" % ph3)
    b3 = basics(w, ph3, ll3, xg3)
    c3 = Closure(w, ph3, {'N': ('NN0', nn3), LN: ('NN0', b3['ln'])})
    fN3, _ = fval(w, ph3, b3, xg3, 'N', nn3)
    fN3x = w.s([fN3, w.s([nle3], 'iffalsed', '( %s -> %s = X )' % (ph3, FB('N')))], 'eqtrd', '( %s -> ( %s ` N ) = X )' % (ph3, F))
    bi3 = w.s([c3.mem(LN, 'RR'), c3.mem('N', 'RR')], 'ltnled', '( %s -> ( %s < N <-> -. N <_ %s ) )' % (ph3, LN, LN))
    lt3 = w.s([nle3, bi3], 'mpbird', '( %s -> %s < N )' % (ph3, LN))
    from lin import linarith
    lt4 = linarith(w, ph3, [lt3], '%s < %s' % (LN, NP1), closure=c3)
    bi4 = w.s([c3.mem(LN, 'RR'), c3.mem(NP1, 'RR')], 'ltnled', '( %s -> ( %s < %s <-> -. %s <_ %s ) )' % (ph3, LN, NP1, NP1, LN))
    nle4 = w.s([lt4, bi4], 'mpbid', '( %s -> -. %s <_ %s )' % (ph3, NP1, LN))
    n13 = w.s([nn3, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ph3, NP1))
    f13, _ = fval(w, ph3, b3, xg3, NP1, n13)
    f13x = w.s([f13, w.s([nle4], 'iffalsed', '( %s -> %s = X )' % (ph3, FB(NP1)))], 'eqtrd', '( %s -> ( %s ` %s ) = X )' % (ph3, F, NP1))
    gb = w.s([f13x, fN3x], 'eqtr4d', '( %s -> %s )' % (ph3, GOAL_B))
    B_ = w.s([gb], 'ex', '( %s -> ( -. N e. %s -> %s ) )' % (ph, R, GOAL_B))
    # ---- (c) typings
    phc = '( %s /\\ N < %s )' % (ph, LN)
    llc = w.s([ll], 'adantr', '( %s -> L e. Word 2o )' % phc)
    nnc = w.s([nn], 'adantr', '( %s -> N e. NN0 )' % phc)
    ltc = w.s([], 'simpr', '( %s -> N < %s )' % (phc, LN))
    lnnc = w.s([llc, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (phc, LN))
    ccc = Closure(w, phc, {'N': ('NN0', nnc), LN: ('NN0', lnnc)})
    ezc = w.s([ccc.mem('N', 'ZZ'), closed(w, phc, '0z', '0 e. ZZ'), ccc.mem(LN, 'ZZ'), w.inst('elfzo')], 'syl3anc',
              '( %s -> ( N e. ( 0 ..^ %s ) <-> ( 0 <_ N /\\ N < %s ) ) )' % (phc, LN, LN))
    nfoc = w.s([ezc, w.s([ccc.ge0('N'), ltc], 'jca', '( %s -> ( 0 <_ N /\\ N < %s ) )' % (phc, LN))], 'mpbird',
               '( %s -> N e. ( 0 ..^ %s ) )' % (phc, LN))
    lnbc = w.s([llc, nfoc, w.inst('wrdsymbcl')], 'syl2anc', '( %s -> ( L ` N ) e. 2o )' % phc)
    ubc = w.s([lnbc, w.inst('bitgamma')], 'syl', "( %s -> <. 1 , ( L ` N ) >. e. Gamma' )" % phc)
    g4c = closed(w, '( %s /\\ -. N < %s )' % (ph, LN), 'gamma4', "4 e. Gamma'")
    uty = w.s([ubc, g4c], 'ifclda', "( %s -> %s e. Gamma' )" % (ph, UB('N')))
    uv = uval(w, ph, 'N', nn, uty)
    ut = w.s([uv, uty], 'eqeltrd', "( %s -> ( %s ` N ) e. Gamma' )" % (ph, U))
    ft = w.s([ll, xg, n1, w.inst('tmcopty')], 'syl3anc', "( %s -> ( %s ` %s ) e. Word Gamma' )" % (ph, F, NP1))
    C_ = w.s([ut, ft], 'jca', "( %s -> ( ( %s ` N ) e. Gamma' /\\ ( %s ` %s ) e. Word Gamma' ) )" % (ph, U, F, NP1))
    w.qed([A_, B_, C_], '3jca', ST_OP1[len('( %s -> ' % ph):-2].join(['( %s -> ' % ph, ' )']))
    return w.run()


if __name__ == '__main__':
    if want('tmcopty'): tmcopty()
    if want('tmcop0'): tmcop0()
    if want('tmcope'): tmcope()
    if want('tmcop1'): tmcop1()
