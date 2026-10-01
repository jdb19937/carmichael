"""Sortie A4b, batch 6: the natural-number wrapper of the cost bound and the
eventual headline (Lean AlgBudget.lean, costPieces_leW).

    MM_DB=sorties/a4b.mm python3 tools/gen/a4b_wrap.py [labels]
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import a1lib
from a2lib import WH, sqrtle2
from a4blib import lit
from a4b_term import BUDGET
from tm import W
from cl import Closure
from lin import linarith, nlinarith
import num

only = [a for a in sys.argv[1:] if not a.startswith('-')]
GENS = []
def gen(fn):
    GENS.append(fn); return fn
PH = 'ph'
def A(f): return '( ph -> %s )' % f


@gen
def cbsqle():
    w = W('cbsqle', 'The square root of a real at least one is at most the real itself '
                    '(Lean AlgBudget.lean uses Nat.sqrt_le_self for the same step).')
    H = '( Z e. RR /\\ 1 <_ Z )'
    def B(f): return '( %s -> %s )' % (H, f)
    zre = w.s([], 'simpl', B('Z e. RR'))
    z1 = w.s([], 'simpr', B('1 <_ Z'))
    c = Closure(w, H, {'Z': ('RR', zre)})
    z0 = linarith(w, H, [z1], '0 <_ Z', closure=c)
    c.have('Z', 'ge0', z0)
    hmul = nlinarith(w, H, [z1], 'Z <_ ( Z x. Z )', closure=c)
    sq = w.s([c.mem('Z', 'CC')], 'sqvald', B('( Z ^ 2 ) = ( Z x. Z )'))
    hle = w.s([hmul, w.s([sq], 'eqcomd', B('( Z x. Z ) = ( Z ^ 2 )'))], 'breqtrd',
              B('Z <_ ( Z ^ 2 )'))
    st = sqrtle2(w, H, 'Z', 'Z', zre, z0, zre, z0, hle)
    w.qed([st], 'idi', B('( sqrt ` Z ) <_ Z'))
    return w


@gen
def cbnlogle():
    w = W('cbnlogle', 'The binary logarithm of a positive integer is at most the integer '
                      '(Lean AlgBudget.lean uses Nat.log_le_self for the same step).')
    H = 'Z e. NN'
    def B(f): return '( %s -> %s )' % (H, f)
    zn = w.s([], 'id', B('Z e. NN'))
    two = w.s([w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')],
              'a1i', B('2 e. ( ZZ>= ` 2 )'))
    lg = w.s([two, zn, w.inst('nlogle')], 'syl2anc', B('( 2 ^ ( 2 Nlog Z ) ) <_ Z'))
    lgn0 = w.s([w.s([num.nn0(w, 2)], 'a1i', B('2 e. NN0')), w.s([zn], 'nnnn0d', B('Z e. NN0')),
                w.inst('nlogcl')], 'syl2anc', B('( 2 Nlog Z ) e. NN0'))
    bn = w.s([two, lgn0, w.inst('bernneq3')], 'syl2anc', B('( 2 Nlog Z ) < ( 2 ^ ( 2 Nlog Z ) )'))
    c = Closure(w, H, {'Z': ('NN', zn)})
    lt = w.s([c.mem('( 2 Nlog Z )', 'RR'), c.mem('( 2 ^ ( 2 Nlog Z ) )', 'RR'),
              c.mem('Z', 'RR'), bn, lg], 'ltletrd', B('( 2 Nlog Z ) < Z'))
    w.qed([lt], 'ltled', B('( 2 Nlog Z ) <_ Z'))
    return w


AA = '( ell2 ` N )'
BB = '( ell3 ` N )'
MM = '( %s x. %s )' % (AA, BB)
VV = '( Nfloor ` ( sqrt ` Z ) )'
WW = '( 2 Nlog Z )'
UU = '( Nfloor ` ( sqrt ` X ) )'
DD = '( 2 ^ T )'
SUB = {'A': AA, 'B': BB, 'M': MM, 'V': VV, 'W': WW, 'U': UU, 'D': DD}
def inst(e):
    out = []
    for t in e.split():
        out.append(SUB.get(t, t))
    return ' '.join(out)
CP = '( ( ( ( ( ( ( Z CostPieces Y ) ` T ) ` L ) ` X ) ` K ) ` P ) ` S )'


@gen
def cbnat():
    w = WH('cbnat', 'The operation budget of the algorithm at one scale tuple in the window '
                    'is below exp ( 100 ell2 ell3 ) (Lean AlgBudget.lean, the body of '
                    'costPieces_leW after filter_upwards).')
    cre = w.h('C e. RR'); c1000 = w.h('; ; ; 1 0 0 0 <_ C')
    ere = w.h('E e. RR'); e0 = w.h('0 < E')
    nu = w.h('N e. ( ZZ>= ` 3 )')
    a1 = w.h('1 <_ %s' % AA); b12 = w.h('; 1 2 <_ %s' % BB)
    hlc = w.h('( log ` ( 4 x. C ) ) <_ %s' % BB)
    win = w.h('<. <. C , E >. , N >. InWindow <. <. Z , W >. , <. Y , T >. >.')
    zn = w.h('Z e. NN0'); yn = w.h('Y e. NN0'); tn = w.h('T e. NN0'); ln = w.h('L e. NN0')
    xn = w.h('X e. NN0'); kn = w.h('K e. NN0'); pn = w.h('P e. NN0'); sn = w.h('S e. NN0')
    lzt = w.h('L <_ ( Z ^ T )'); xeq = w.h('X = ( L ^ 5 )')
    kx = w.h('K <_ ( X ^c ( ; 7 9 / ; ; 1 0 0 ) )')
    pd = w.h('P <_ ( 2 ^ T )'); sd = w.h('S <_ ( 2 ^ T )')

    c = Closure(w, PH, {'C': ('RR', cre), 'E': ('RR', ere), 'Z': ('NN0', zn), 'Y': ('NN0', yn),
                        'T': ('NN0', tn), 'L': ('NN0', ln), 'X': ('NN0', xn), 'K': ('NN0', kn),
                        'P': ('NN0', pn), 'S': ('NN0', sn)})
    # the iterated logarithms
    nn0 = w.s([w.s([num.nn0(w, 3)], 'a1i', A('3 e. NN0')), nu, w.inst('eluznn0')], 'syl2anc',
              A('N e. NN0'))
    nu2 = w.s([nu, w.inst('uzuzle23')], 'syl', A('N e. ( ZZ>= ` 2 )'))
    are = w.s([nu2, w.inst('ell2cl')], 'syl', A('%s e. RR' % AA))
    bre = w.s([nu, w.inst('ell3cl')], 'syl', A('%s e. RR' % BB))
    c.have(AA, 'RR', are); c.have(BB, 'RR', bre)
    mre = w.s([are, bre], 'remulcld', A('%s e. RR' % MM))
    c.have(MM, 'RR', mre)
    beq = w.s([nn0, w.inst('ell3val')], 'syl', A('%s = ( log ` %s )' % (BB, AA)))
    meq = w.s([], 'eqidd', A('%s = %s' % (MM, MM)))
    # the window
    zlo0 = w.s([win, w.inst('inwinzlo')], 'syl', A('( ( C x. %s ) x. %s ) <_ Z' % (AA, BB)))
    zhi0 = w.s([win, w.inst('inwinzhi')], 'syl', A('Z <_ ( 4 x. ( ( C x. %s ) x. %s ) )' % (AA, BB)))
    yhi0 = w.s([win, w.inst('inwinyhi')], 'syl', A('Y <_ ( 4 x. ( Z ^c ( 1 - E ) ) )'))
    tlo = w.s([win, w.inst('inwintlo')], 'syl', A('( 3 x. %s ) <_ T' % AA))
    thi = w.s([win, w.inst('inwinthi')], 'syl', A('T <_ ( 5 x. %s )' % AA))
    ccn = c.mem('C', 'CC'); acn = c.mem(AA, 'CC'); bcn = c.mem(BB, 'CC')
    ass = w.s([ccn, acn, bcn], 'mulassd', A('( ( C x. %s ) x. %s ) = ( C x. %s )' % (AA, BB, MM)))
    zlo = w.s([w.s([ass], 'eqcomd', A('( C x. %s ) = ( ( C x. %s ) x. %s )' % (MM, AA, BB))),
               zlo0], 'eqbrtrd', A('( C x. %s ) <_ Z' % MM))
    i4cn = w.s([num.cc(w, '4')], 'a1i', A('4 e. CC'))
    ass3 = w.s([w.s([ass], 'oveq2d', A('( 4 x. ( ( C x. %s ) x. %s ) ) = ( 4 x. ( C x. %s ) )' % (AA, BB, MM))),
                w.s([i4cn, ccn, c.mem(MM, 'CC')], 'mulassd',
                    A('( ( 4 x. C ) x. %s ) = ( 4 x. ( C x. %s ) )' % (MM, MM)))], 'eqtr4d',
               A('( 4 x. ( ( C x. %s ) x. %s ) ) = ( ( 4 x. C ) x. %s )' % (AA, BB, MM)))
    zhi = w.s([zhi0, ass3], 'breqtrd', A('Z <_ ( ( 4 x. C ) x. %s )' % MM))
    # 1 <_ Z
    m12 = w.s([are, a1, bre, b12, mre, meq], 'cbm12', A('; 1 2 <_ %s' % MM))
    z12 = w.s([cre, c1000, mre, m12, c.mem('Z', 'RR'), zlo], 'cbz12', A('; ; ; ; 1 2 0 0 0 <_ Z'))
    z1 = linarith(w, PH, [z12], '1 <_ Z', closure=c)
    z0 = linarith(w, PH, [z12], '0 <_ Z', closure=c)
    z0s = linarith(w, PH, [z12], '0 < Z', closure=c)
    c.have('Z', 'ge1', z1)
    zrp = w.s([c.mem('Z', 'RR'), z0s], 'elrpd', A('Z e. RR+'))
    c.have('Z', 'RR+', zrp)
    # Y <_ 4 Z
    zcn = c.mem('Z', 'CC')
    e1le = linarith(w, PH, [e0], '( 1 - E ) <_ 1', closure=c)
    cxm = w.s([c.mem('Z', 'RR'), z1, c.mem('( 1 - E )', 'RR'),
               w.s([], '1red', A('1 e. RR')), e1le], 'cxplead',
              A('( Z ^c ( 1 - E ) ) <_ ( Z ^c 1 )'))
    cx1 = w.s([zcn, w.inst('cxp1')], 'syl', A('( Z ^c 1 ) = Z'))
    cxz = w.s([cxm, cx1], 'breqtrd', A('( Z ^c ( 1 - E ) ) <_ Z'))
    c.have('( Z ^c ( 1 - E ) )', 'RR', c.mem('( Z ^c ( 1 - E ) )', 'RR'))
    yz = linarith(w, PH, [yhi0, cxz], 'Y <_ ( 4 x. Z )', closure=c)
    # V = Nfloor ( sqrt Z ) and W = 2 Nlog Z
    sqz = c.mem('( sqrt ` Z )', 'RR')
    sqz0 = w.s([c.mem('Z', 'RR'), z0], 'sqrtge0d', A('0 <_ ( sqrt ` Z )'))
    vle0 = w.s([sqz, sqz0, w.inst('nfloorle')], 'syl2anc', A('%s <_ ( sqrt ` Z )' % VV))
    sqle = w.s([c.mem('Z', 'RR'), z1, w.inst('cbsqle')], 'syl2anc', A('( sqrt ` Z ) <_ Z'))
    vz = w.s([c.mem(VV, 'RR'), sqz, c.mem('Z', 'RR'), vle0, sqle], 'letrd', A('%s <_ Z' % VV))
    znn = w.s([w.s([zn, z1], 'jca', A('( Z e. NN0 /\\ 1 <_ Z )')), w.inst('elnnnn0c')], 'sylibr',
              A('Z e. NN'))
    wz = w.s([znn, w.inst('cbnlogle')], 'syl', A('%s <_ Z' % WW))
    # L <_ Z ^c T
    zne = w.s([zrp], 'rpne0d', A('Z =/= 0'))
    cxe = w.s([zcn, zne, c.mem('T', 'ZZ'), w.inst('cxpexpz')], 'syl3anc',
              A('( Z ^c T ) = ( Z ^ T )'))
    lzt2 = w.s([lzt, w.s([cxe], 'eqcomd', A('( Z ^ T ) = ( Z ^c T )'))], 'breqtrd',
               A('L <_ ( Z ^c T )'))
    # U = Nfloor ( sqrt X )
    sqx = c.mem('( sqrt ` X )', 'RR')
    sqx0 = w.s([c.mem('X', 'RR'), c.ge0('X')], 'sqrtge0d', A('0 <_ ( sqrt ` X )'))
    usx = w.s([sqx, sqx0, w.inst('nfloorle')], 'syl2anc', A('%s <_ ( sqrt ` X )' % UU))
    # D = 2 ^ T
    i2cn = w.s([num.cc(w, '2')], 'a1i', A('2 e. CC'))
    i2ne = w.s([num.fact(w, '2', 'ne0')], 'a1i', A('2 =/= 0'))
    twe = w.s([i2cn, i2ne, c.mem('T', 'ZZ'), w.inst('cxpexpz')], 'syl3anc',
              A('( 2 ^c T ) = ( 2 ^ T )'))
    dtw = w.s([w.s([c.mem(DD, 'RR')], 'leidd', A('%s <_ %s' % (DD, DD))),
               w.s([twe], 'eqcomd', A('%s = ( 2 ^c T )' % DD))], 'breqtrd',
              A('%s <_ ( 2 ^c T )' % DD))
    # the core
    args = [cre, c1000, are, a1, bre, b12, beq, hlc, mre, meq,
            c.mem('Z', 'RR'), zlo, zhi, c.mem('Y', 'RR'), yz,
            c.mem('T', 'RR'), tlo, thi, c.mem(VV, 'RR'), vz, c.mem(WW, 'RR'), wz,
            c.mem('L', 'RR'), c.ge0('L'), lzt2, c.mem('X', 'RR'), xeq,
            c.mem(UU, 'RR'), c.ge0(UU), usx, c.mem('K', 'RR'), c.ge0('K'), kx,
            c.mem(DD, 'RR'), c.ge0(DD), dtw, c.mem('P', 'RR'), c.ge0('P'), pd,
            c.mem('S', 'RR'), c.ge0('S'), sd]
    BUD = inst(BUDGET)
    core = w.s(args, 'cbcore', A('%s <_ ( exp ` ( ; ; 1 0 0 x. %s ) )' % (BUD, MM)))
    # the value of CostPieces
    ant = 'Z e. NN0'
    st = zn
    for v, h in (('Y', yn), ('T', tn), ('L', ln), ('X', xn), ('K', kn), ('P', pn), ('S', sn)):
        ant = '( %s /\\ %s e. NN0 )' % (ant, v)
        st = w.s([st, h], 'jca', A(ant))
    val = w.s([st, w.inst('costpiecesval')], 'syl', A('%s = %s' % (CP, BUD)))
    st2 = w.s([val, core], 'eqbrtrd', A('%s <_ ( exp ` ( ; ; 1 0 0 x. %s ) )' % (CP, MM)))
    i100 = w.s([num.cc(w, '; ; 1 0 0')], 'a1i', A('; ; 1 0 0 e. CC'))
    ass4 = w.s([i100, acn, bcn], 'mulassd',
               A('( ( ; ; 1 0 0 x. %s ) x. %s ) = ( ; ; 1 0 0 x. %s )' % (AA, BB, MM)))
    ee = w.s([w.s([ass4], 'fveq2d',
                  A('( exp ` ( ( ; ; 1 0 0 x. %s ) x. %s ) ) = ( exp ` ( ; ; 1 0 0 x. %s ) )' % (AA, BB, MM)))],
             'eqcomd',
             A('( exp ` ( ; ; 1 0 0 x. %s ) ) = ( exp ` ( ( ; ; 1 0 0 x. %s ) x. %s ) )' % (MM, AA, BB)))
    w.qed([st2, ee], 'breqtrd',
          A('%s <_ ( exp ` ( ( ; ; 1 0 0 x. %s ) x. %s ) )' % (CP, AA, BB)))
    return w




# --------------------------------------------------------------- the headline
Aa = '( ell2 ` n )'
Bb = '( ell3 ` n )'
PH0 = '( ( C e. RR /\\ ; ; ; 1 0 0 0 <_ C ) /\\ ( E e. RR /\\ 0 < E ) )'
EV = ('( ( ( 1 <_ %s /\\ ; 1 2 <_ %s ) /\\ ( log ` ( 4 x. C ) ) <_ %s ) /\\ n e. ( ZZ>= ` 3 ) )'
      % (Aa, Bb, Bb))
WIN = '<. <. C , E >. , n >. InWindow <. <. z , w >. , <. y , t >. >.'
HYPS = ('( ( l <_ ( z ^ t ) /\\ x = ( l ^ 5 ) ) /\\ ( k <_ ( x ^c ( ; 7 9 / ; ; 1 0 0 ) ) '
        '/\\ ( p <_ ( 2 ^ t ) /\\ s <_ ( 2 ^ t ) ) ) )')
CPn = '( ( ( ( ( ( ( z CostPieces y ) ` t ) ` l ) ` x ) ` k ) ` p ) ` s )'
CONCL = '%s <_ ( exp ` ( ( ; ; 1 0 0 x. %s ) x. %s ) )' % (CPn, Aa, Bb)
INNER = '( %s -> %s )' % (HYPS, CONCL)
for v in ('s', 'p', 'k', 'x', 'l'):
    INNER = 'A. %s e. NN0 %s' % (v, INNER)
MID = '( %s -> %s )' % (WIN, INNER)
BIG = MID
for v in ('t', 'y', 'w', 'z'):
    BIG = 'A. %s e. NN0 %s' % (v, BIG)


@gen
def cbev():
    from cl import lift
    H = '( %s /\\ %s )' % (PH0, EV)
    w = W('cbev', 'The pointwise content of the cost bound: at an n where the two iterated '
                  'logarithms are large enough, the budget is below exp ( 100 ell2 ell3 ) at '
                  'every scale tuple in the window and every admissible run of the algorithm.')
    def B(f): return '( %s -> %s )' % (H, f)
    cre = w.s([], 'simplll', B('C e. RR'))
    c1000 = w.s([], 'simpllr', B('; ; ; 1 0 0 0 <_ C'))
    ere = w.s([], 'simplrl', B('E e. RR'))
    e0 = w.s([], 'simplrr', B('0 < E'))
    ev = w.s([], 'simpr', B(EV))
    a1 = w.s([ev, w.inst('simplll')], 'syl', B('1 <_ %s' % Aa))
    b12 = w.s([ev, w.inst('simpllr')], 'syl', B('; 1 2 <_ %s' % Bb))
    hlc = w.s([ev, w.inst('simplr')], 'syl', B('( log ` ( 4 x. C ) ) <_ %s' % Bb))
    nu = w.s([ev, w.inst('simpr')], 'syl', B('n e. ( ZZ>= ` 3 )'))
    # the full antecedent of the innermost step
    levels = ['z e. NN0', 'w e. NN0', 'y e. NN0', 't e. NN0', WIN,
              'l e. NN0', 'x e. NN0', 'k e. NN0', 'p e. NN0', 's e. NN0', HYPS]
    ant = H
    antes = []
    for lv in levels:
        antes.append(ant)
        ant = '( %s /\\ %s )' % (ant, lv)
    HH = ant
    def up(st):
        return lift(w, st, HH)
    def ident(f):
        return lift(w, w.s([], 'id', '( %s -> %s )' % (f, f)), HH)
    args = [up(cre), up(c1000), up(ere), up(e0), up(nu), up(a1), up(b12), up(hlc), ident(WIN)]
    for v in ('z', 'y', 't', 'l', 'x', 'k', 'p', 's'):
        args.append(ident('%s e. NN0' % v))
    hy = w.s([], 'simpr', '( %s -> %s )' % (HH, HYPS))
    for ref, f in (('simpll', 'l <_ ( z ^ t )'), ('simplr', 'x = ( l ^ 5 )'),
                   ('simprl', 'k <_ ( x ^c ( ; 7 9 / ; ; 1 0 0 ) )'),
                   ('simprrl', 'p <_ ( 2 ^ t )'), ('simprrr', 's <_ ( 2 ^ t )')):
        args.append(w.s([hy, w.inst(ref)], 'syl', '( %s -> %s )' % (HH, f)))
    st = w.s(args, 'cbnat', '( %s -> %s )' % (HH, CONCL))
    cur = '( %s -> %s )' % (HYPS, CONCL)
    st = w.s([st], 'ex', '( %s -> %s )' % (antes[-1], cur))
    for v in ('s', 'p', 'k', 'x', 'l'):
        i = levels.index('%s e. NN0' % v)
        cur = 'A. %s e. NN0 %s' % (v, cur)
        st = w.s([st], 'ralrimiva', '( %s -> %s )' % (antes[i], cur))
    st = w.s([st], 'ex', '( %s -> ( %s -> %s ) )' % (antes[levels.index(WIN)], WIN, cur))
    cur = '( %s -> %s )' % (WIN, cur)
    for v in ('t', 'y', 'w', 'z'):
        i = levels.index('%s e. NN0' % v)
        cur = 'A. %s e. NN0 %s' % (v, cur)
        st = w.s([st], 'ralrimiva', '( %s -> %s )' % (antes[i], cur))
    w.qed([st], 'idi', '( %s -> %s )' % (H, cur))
    return w


@gen
def costpiecesle():
    from a2lib import evand, EV as EVF
    w = W('costpiecesle', 'The operation budget of the algorithm of the paper is eventually '
                          'below exp ( 100 ell2 ell3 ) at every scale tuple in the window: '
                          'Lean Carmichael/AlgBudget.lean, costPieces_leW , the bound '
                          'SearchAlg.lean instantiates for the cost of Alg.search .')
    def B(f): return '( %s -> %s )' % (PH0, f)
    cre = w.s([], 'simpll', B('C e. RR'))
    c1000 = w.s([], 'simplr', B('; ; ; 1 0 0 0 <_ C'))
    c = Closure(w, PH0, {'C': ('RR', cre), 'E': ('RR', w.s([], 'simprl', B('E e. RR')))})
    c0 = linarith(w, PH0, [c1000], '0 < C', closure=c)
    c.have('C', 'gt0', c0)
    l4c = c.mem('( log ` ( 4 x. C ) )', 'RR')
    one = w.s([], '1red', B('1 e. RR'))
    i12 = w.s([num.fact(w, '; 1 2', 'RR')], 'a1i', B('; 1 2 e. RR'))
    e1 = w.s([one, w.inst('ell2ge')], 'syl', B(EVF('1 <_ %s' % Aa)))
    e2 = w.s([i12, w.inst('ell3ge')], 'syl', B(EVF('; 1 2 <_ %s' % Bb)))
    e3 = w.s([l4c, w.inst('ell3ge')], 'syl', B(EVF('( log ` ( 4 x. C ) ) <_ %s' % Bb)))
    e4 = w.s([w.s([], 'evge3', EVF('n e. ( ZZ>= ` 3 )'))], 'a1i', B(EVF('n e. ( ZZ>= ` 3 )')))
    st, tx = evand(w, PH0, [e1, e2, e3, e4],
                   ['1 <_ %s' % Aa, '; 1 2 <_ %s' % Bb,
                    '( log ` ( 4 x. C ) ) <_ %s' % Bb, 'n e. ( ZZ>= ` 3 )'])
    w.qed([st, w.inst('cbev')], 'evimd', B(EVF(BIG)))
    return w


def main():
    ok = True
    for fn in GENS:
        if only and fn.__name__ not in only:
            continue
        ok = fn().run() and ok
    return ok

if __name__ == '__main__':
    sys.exit(0 if main() else 1)
