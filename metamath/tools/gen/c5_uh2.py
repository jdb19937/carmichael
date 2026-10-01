"""C5, generic block 2: pointwise convergence of the partial sums and the
identification of the uniform limit with the sum function."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *

PS = PSQ('F')
FM = FMAP('F')
UM = UHM('F', 'M')
A0 = UHS()
G = GSUM()
GL = '( ( ~~>u ` U ) ` %s )' % PS


def GZ(pt):
    return '( h e. NN |-> ( ( F ` h ) ` %s ) )' % pt


def AZ(pt):
    return '( h e. NN |-> ( abs ` ( ( F ` h ) ` %s ) ) )' % pt


def ctx(w, A1, uhs=None):
    """the standing steps under an antecedent A1 that contains UHS (uhs: a step proving it)"""
    d = {}
    if uhs is None:
        uhs = w.s([], 'id', '( %s -> %s )' % (A1, A0))
    d['uhs'] = uhs
    d['ff'] = w.s([uhs, w.inst('simpl')], 'syl', '( %s -> %s )' % (A1, FM))
    um = w.s([uhs, w.inst('simpr')], 'syl', '( %s -> %s )' % (A1, UM))
    d['mf'] = w.s([um, w.inst('simp1')], 'syl', '( %s -> M : NN --> RR )' % A1)
    d['mcv'] = w.s([um, w.inst('simp2')], 'syl', '( %s -> seq 1 ( + , M ) e. dom ~~> )' % A1)
    d['mb'] = w.s([um, w.inst('simp3')], 'syl', '( %s -> A. j e. NN A. y e. U ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j ) )' % A1)
    d['nu1'], d['z1'], d['n1'] = nnuz(w, A1)
    d['u1n'] = w.s([w.s([d['nu1']], 'eqcomi', '( ZZ>= ` 1 ) = NN')], 'a1i', '( %s -> ( ZZ>= ` 1 ) = NN )' % A1)
    return d


def ubnd(w, ante, i, pt, mb, mi, mp):
    """( ante -> ( abs ` ( ( F ` i ) ` pt ) ) <_ ( M ` i ) ) from the quantified bound mb
    and memberships mi: i e. NN, mp: pt e. U"""
    s1 = w.s([w.s([w.s([], 'fveq2', '( j = %s -> ( F ` j ) = ( F ` %s ) )' % (i, i))], 'fveq1d',
                  '( j = %s -> ( ( F ` j ) ` y ) = ( ( F ` %s ) ` y ) )' % (i, i))], 'fveq2d',
             '( j = %s -> ( abs ` ( ( F ` j ) ` y ) ) = ( abs ` ( ( F ` %s ) ` y ) ) )' % (i, i))
    s2 = w.s([], 'fveq2', '( j = %s -> ( M ` j ) = ( M ` %s ) )' % (i, i))
    sb1 = w.s([s1, s2], 'breq12d', '( j = %s -> ( ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j ) <-> ( abs ` ( ( F ` %s ) ` y ) ) <_ ( M ` %s ) ) )' % (i, i, i))
    s3 = w.s([w.s([], 'fveq2', '( y = %s -> ( ( F ` %s ) ` y ) = ( ( F ` %s ) ` %s ) )' % (pt, i, i, pt))], 'fveq2d',
             '( y = %s -> ( abs ` ( ( F ` %s ) ` y ) ) = ( abs ` ( ( F ` %s ) ` %s ) ) )' % (pt, i, i, pt))
    sb2 = w.s([s3], 'breq1d', '( y = %s -> ( ( abs ` ( ( F ` %s ) ` y ) ) <_ ( M ` %s ) <-> ( abs ` ( ( F ` %s ) ` %s ) ) <_ ( M ` %s ) ) )' % (pt, i, i, i, pt, i))
    return w.s([sb1, sb2, mb, mi, mp], 'rspc2dv', '( %s -> ( abs ` ( ( F ` %s ) ` %s ) ) <_ ( M ` %s ) )' % (ante, i, pt, i))


def gzval(w, ante, i, pt, mi):
    s = w.s([w.s([], 'fveq2', '( h = %s -> ( F ` h ) = ( F ` %s ) )' % (i, i))], 'fveq1d',
            '( h = %s -> ( ( F ` h ) ` %s ) = ( ( F ` %s ) ` %s ) )' % (i, pt, i, pt))
    return mpv(w, ante, GZ(pt), i, '( ( F ` %s ) ` %s )' % (i, pt), s, mi, vexd(w, ante, '( ( F ` %s ) ` %s )' % (i, pt), 'fv'))


def azval(w, ante, i, pt, mi):
    s = w.s([w.s([w.s([], 'fveq2', '( h = %s -> ( F ` h ) = ( F ` %s ) )' % (i, i))], 'fveq1d',
                 '( h = %s -> ( ( F ` h ) ` %s ) = ( ( F ` %s ) ` %s ) )' % (i, pt, i, pt))], 'fveq2d',
            '( h = %s -> ( abs ` ( ( F ` h ) ` %s ) ) = ( abs ` ( ( F ` %s ) ` %s ) ) )' % (i, pt, i, pt))
    return mpv(w, ante, AZ(pt), i, '( abs ` ( ( F ` %s ) ` %s ) )' % (i, pt), s, mi,
               vexd(w, ante, '( abs ` ( ( F ` %s ) ` %s ) )' % (i, pt), 'fv'))


def termcl(w, ante, i, pt, ff, mi, mp):
    """( ante -> ( ( F ` i ) ` pt ) e. CC )"""
    return w.s([fval(w, ante, i, mi, ff), mp], 'ffvelcdmd', '( %s -> ( ( F ` %s ) ` %s ) e. CC )' % (ante, i, pt))


def psval(w, ante, i, pt, d, mi, mp):
    """( ante -> ( ( PS ` i ) ` pt ) = sum_ k e. ( 1 ... i ) ( ( F ` k ) ` pt ) ) and the seq form
    ( ante -> ( ( PS ` i ) ` pt ) = ( seq 1 ( + , GZ(pt) ) ` i ) ); returns (sum step, seq step)"""
    pv = w.s([w.s([d['ff'], mi], 'jca', '( %s -> ( %s /\\ %s e. NN ) )' % (ante, FM, i)), w.inst('uhps')], 'syl',
             '( %s -> ( %s ` %s ) = %s )' % (ante, PS, i, PSMAP('F', i)))
    fv1 = w.s([pv], 'fveq1d', '( %s -> ( ( %s ` %s ) ` %s ) = ( %s ` %s ) )' % (ante, PS, i, pt, PSMAP('F', i), pt))
    sub = w.s([w.s([], 'fveq2', '( z = %s -> ( ( F ` k ) ` z ) = ( ( F ` k ) ` %s ) )' % (pt, pt))], 'sumeq2sdv',
              '( z = %s -> sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` z ) = sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` %s ) )' % (pt, i, i, pt))
    val = mpv(w, ante, PSMAP('F', i), pt, 'sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` %s )' % (i, pt), sub, mp,
              vexd(w, ante, 'sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` %s )' % (i, pt), 'sum'), 'U')
    sm = w.s([fv1, val], 'eqtrd', '( %s -> ( ( %s ` %s ) ` %s ) = sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` %s ) )' % (ante, PS, i, pt, i, pt))
    # the seq form
    Ak = '( %s /\\ k e. ( 1 ... %s ) )' % (ante, i)
    knn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... %s ) )' % (Ak, i)), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ak)
    gv = gzval(w, Ak, 'k', pt, knn)
    tc = termcl(w, Ak, 'k', pt, w.s([d['ff']], 'adantr', '( %s -> %s )' % (Ak, FM)), knn,
                w.s([mp], 'adantr', '( %s -> %s e. U )' % (Ak, pt)))
    iuz = w.s([mi, d['nu1']], 'eleqtrdi', '( %s -> %s e. ( ZZ>= ` 1 ) )' % (ante, i))
    fs = w.s([gv, iuz, tc], 'fsumser', '( %s -> sum_ k e. ( 1 ... %s ) ( ( F ` k ) ` %s ) = ( seq 1 ( + , %s ) ` %s ) )' % (ante, i, pt, GZ(pt), i))
    return sm, w.s([sm, fs], 'eqtrd', '( %s -> ( ( %s ` %s ) ` %s ) = ( seq 1 ( + , %s ) ` %s ) )' % (ante, PS, i, pt, GZ(pt), i))


# ---------------------------------------------------------------- uhcvg
w = W('uhcvg', 'The term sequence of a majorised term-function sequence converges at every '
      'point of the domain ( ~ cvgcmp , ~ abscvgcvg ).')
A1 = '( %s /\\ Z e. U )' % A0
d = ctx(w, A1, w.s([], 'simpl', '( %s -> %s )' % (A1, A0)))
zu = w.s([], 'simpr', '( %s -> Z e. U )' % A1)
Ak = '( %s /\\ k e. NN )' % A1
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
mk = w.s([w.s([d['mf']], 'adantr', '( %s -> M : NN --> RR )' % Ak), kn], 'ffvelcdmd', '( %s -> ( M ` k ) e. RR )' % Ak)
tc = termcl(w, Ak, 'k', 'Z', w.s([d['ff']], 'adantr', '( %s -> %s )' % (Ak, FM)), kn, w.s([zu], 'adantr', '( %s -> Z e. U )' % Ak))
av = azval(w, Ak, 'k', 'Z', kn)
ar = w.s([av, w.s([tc], 'abscld', '( %s -> ( abs ` ( ( F ` k ) ` Z ) ) e. RR )' % Ak)], 'eqeltrd',
         '( %s -> ( %s ` k ) e. RR )' % (Ak, AZ('Z')))
Au = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % A1
knu = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % Au), w.s([d['u1n']], 'adantr', '( %s -> ( ZZ>= ` 1 ) = NN )' % Au)],
          'eleqtrd', '( %s -> k e. NN )' % Au)
tcu = termcl(w, Au, 'k', 'Z', w.s([d['ff']], 'adantr', '( %s -> %s )' % (Au, FM)), knu, w.s([zu], 'adantr', '( %s -> Z e. U )' % Au))
avu = azval(w, Au, 'k', 'Z', knu)
ge0 = w.s([w.s([tcu], 'absge0d', '( %s -> 0 <_ ( abs ` ( ( F ` k ) ` Z ) ) )' % Au), avu], 'breqtrrd',
          '( %s -> 0 <_ ( %s ` k ) )' % (Au, AZ('Z')))
bd = ubnd(w, Au, 'k', 'Z', w.s([d['mb']], 'adantr', '( %s -> A. j e. NN A. y e. U ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j ) )' % Au),
          knu, w.s([zu], 'adantr', '( %s -> Z e. U )' % Au))
le = w.s([avu, bd], 'eqbrtrd', '( %s -> ( %s ` k ) <_ ( M ` k ) )' % (Au, AZ('Z')))
acv = w.s([d['nu1'], d['n1'], mk, ar, d['mcv'], ge0, le], 'cvgcmp', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A1, AZ('Z')))
gv = gzval(w, Ak, 'k', 'Z', kn)
abv = w.s([av, w.s([gv], 'fveq2d', '( %s -> ( abs ` ( %s ` k ) ) = ( abs ` ( ( F ` k ) ` Z ) ) )' % (Ak, GZ('Z')))], 'eqtr4d',
          '( %s -> ( %s ` k ) = ( abs ` ( %s ` k ) ) )' % (Ak, AZ('Z'), GZ('Z')))
gc = w.s([gv, tc], 'eqeltrd', '( %s -> ( %s ` k ) e. CC )' % (Ak, GZ('Z')))
w.qed([d['nu1'], d['z1'], abv, gc, acv], 'abscvgcvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A1, GZ('Z')))
run5(w)

# ---------------------------------------------------------------- uhcl
w = W('uhcl', 'The sum of a majorised term-function sequence at a point is a complex number.')
A1 = '( %s /\\ Z e. U )' % A0
d = ctx(w, A1, w.s([], 'simpl', '( %s -> %s )' % (A1, A0)))
zu = w.s([], 'simpr', '( %s -> Z e. U )' % A1)
Ak = '( %s /\\ k e. NN )' % A1
kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
tc = termcl(w, Ak, 'k', 'Z', w.s([d['ff']], 'adantr', '( %s -> %s )' % (Ak, FM)), kn, w.s([zu], 'adantr', '( %s -> Z e. U )' % Ak))
gv = gzval(w, Ak, 'k', 'Z', kn)
cv = w.s([], 'uhcvg', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A1, GZ('Z')))
w.qed([d['nu1'], d['z1'], gv, tc, cv], 'isumcl', '( %s -> sum_ k e. NN ( ( F ` k ) ` Z ) e. CC )' % A1)
run5(w)

# ---------------------------------------------------------------- uhf
w = W('uhf', 'The sum function of a majorised term-function sequence maps the domain into the complex numbers.')
Az = '( %s /\\ z e. U )' % A0
cl = w.s([], 'uhcl', '( %s -> sum_ k e. NN ( ( F ` k ) ` z ) e. CC )' % Az)
w.qed([cl, w.s([], 'eqid', '%s = %s' % (G, G))], 'fmptd', '( %s -> %s : U --> CC )' % (A0, G))
run5(w)


def gval(w, ante, pt, mp):
    """( ante -> ( G ` pt ) = sum_ k e. NN ( ( F ` k ) ` pt ) )"""
    sub = w.s([w.s([], 'fveq2', '( z = %s -> ( ( F ` k ) ` z ) = ( ( F ` k ) ` %s ) )' % (pt, pt))], 'sumeq2sdv',
              '( z = %s -> sum_ k e. NN ( ( F ` k ) ` z ) = sum_ k e. NN ( ( F ` k ) ` %s ) )' % (pt, pt))
    return mpv(w, ante, G, pt, 'sum_ k e. NN ( ( F ` k ) ` %s )' % pt, sub, mp,
               vexd(w, ante, 'sum_ k e. NN ( ( F ` k ) ` %s )' % pt, 'sum'), 'U')


def psseq(w, ante, pt, d, mp):
    """( ante -> ( i e. NN |-> ( ( PS ` i ) ` pt ) ) = seq 1 ( + , GZ(pt) ) ) and
    ( ante -> seq 1 ( + , GZ(pt) ) ~~> sum_ k e. NN ( ( F ` k ) ` pt ) )"""
    Ai = '( %s /\\ i e. NN )' % ante
    mi = w.s([], 'simpr', '( %s -> i e. NN )' % Ai)
    di = dict(d); di['ff'] = w.s([d['ff']], 'adantr', '( %s -> %s )' % (Ai, FM))
    di['nu1'] = d['nu1']
    sm, sq = psval(w, Ai, 'i', pt, di, mi, w.s([mp], 'adantr', '( %s -> %s e. U )' % (Ai, pt)))
    m1 = w.s([sq], 'mpteq2dva', '( %s -> ( i e. NN |-> ( ( %s ` i ) ` %s ) ) = ( i e. NN |-> ( seq 1 ( + , %s ) ` i ) ) )' % (ante, PS, pt, GZ(pt)))
    fn = w.s([w.s([d['z1'], w.inst('seqfn')], 'syl', '( %s -> seq 1 ( + , %s ) Fn ( ZZ>= ` 1 ) )' % (ante, GZ(pt))),
              w.s([d['u1n']], 'fneq2d', '( %s -> ( seq 1 ( + , %s ) Fn ( ZZ>= ` 1 ) <-> seq 1 ( + , %s ) Fn NN ) )' % (ante, GZ(pt), GZ(pt)))],
             'mpbid', '( %s -> seq 1 ( + , %s ) Fn NN )' % (ante, GZ(pt)))
    bi = w.s([], 'dffn5', '( seq 1 ( + , %s ) Fn NN <-> seq 1 ( + , %s ) = ( i e. NN |-> ( seq 1 ( + , %s ) ` i ) ) )' % (GZ(pt), GZ(pt), GZ(pt)))
    eqm = w.s([fn, w.s([bi], 'a1i', '( %s -> ( seq 1 ( + , %s ) Fn NN <-> seq 1 ( + , %s ) = ( i e. NN |-> ( seq 1 ( + , %s ) ` i ) ) ) )' % (ante, GZ(pt), GZ(pt), GZ(pt)))],
              'mpbid', '( %s -> seq 1 ( + , %s ) = ( i e. NN |-> ( seq 1 ( + , %s ) ` i ) ) )' % (ante, GZ(pt), GZ(pt)))
    ident = w.s([m1, w.s([eqm], 'eqcomd', '( %s -> ( i e. NN |-> ( seq 1 ( + , %s ) ` i ) ) = seq 1 ( + , %s ) )' % (ante, GZ(pt), GZ(pt)))],
                'eqtrd', '( %s -> ( i e. NN |-> ( ( %s ` i ) ` %s ) ) = seq 1 ( + , %s ) )' % (ante, PS, pt, GZ(pt)))
    # the limit of the term series
    Ak = '( %s /\\ k e. NN )' % ante
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    gv = gzval(w, Ak, 'k', pt, kn)
    tc = termcl(w, Ak, 'k', pt, w.s([d['ff']], 'adantr', '( %s -> %s )' % (Ak, FM)), kn, w.s([mp], 'adantr', '( %s -> %s e. U )' % (Ak, pt)))
    cv = w.s([w.s([d['uhs'], mp], 'jca', '( %s -> ( %s /\\ %s e. U ) )' % (ante, A0, pt)), w.inst('uhcvg')], 'syl',
             '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ante, GZ(pt)))
    lim = w.s([d['nu1'], d['z1'], gv, tc, cv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> sum_ k e. NN ( ( F ` k ) ` %s ) )' % (ante, GZ(pt), pt))
    return ident, lim


# ---------------------------------------------------------------- uhptl
w = W('uhptl', 'The partial-sum functions of a majorised term-function sequence converge '
      'pointwise to the sum function ( ~ isumclim2 ), in the form ~ ulmdv consumes.')
A1 = '( %s /\\ w e. U )' % A0
d = ctx(w, A1, w.s([], 'simpl', '( %s -> %s )' % (A1, A0)))
wu = w.s([], 'simpr', '( %s -> w e. U )' % A1)
ident, lim = psseq(w, A1, 'w', d, wu)
gv = gval(w, A1, 'w', wu)
w.qed([w.s([ident, lim], 'eqbrtrd', '( %s -> ( i e. NN |-> ( ( %s ` i ) ` w ) ) ~~> sum_ k e. NN ( ( F ` k ) ` w ) )' % (A1, PS)),
       gv], 'breqtrrd', '( %s -> ( i e. NN |-> ( ( %s ` i ) ` w ) ) ~~> ( %s ` w ) )' % (A1, PS, G))
run5(w)

# ---------------------------------------------------------------- uhlimv
w = W('uhlimv', 'The uniform limit of the partial-sum functions of a majorised term-function '
      'sequence takes the value of the series at every point ( ~ ulmclm , ~ climuni ).')
A1 = '( %s /\\ w e. U )' % A0
d = ctx(w, A1, w.s([], 'simpl', '( %s -> %s )' % (A1, A0)))
wu = w.s([], 'simpr', '( %s -> w e. U )' % A1)
ulm = w.s([w.s([d['uhs'], w.inst('uhmt')], 'syl', '( %s -> %s e. dom ( ~~>u ` U ) )' % (A1, PS)),
           w.s([w.s([], 'ulmdm', '( %s e. dom ( ~~>u ` U ) <-> %s ( ~~>u ` U ) %s )' % (PS, PS, GL))], 'a1i',
               '( %s -> ( %s e. dom ( ~~>u ` U ) <-> %s ( ~~>u ` U ) %s ) )' % (A1, PS, PS, GL))], 'mpbid',
          '( %s -> %s ( ~~>u ` U ) %s )' % (A1, PS, GL))
psf = w.s([d['ff'], w.inst('uhpsf')], 'syl', '( %s -> %s : NN --> ( CC ^m U ) )' % (A1, PS))
Ai = '( %s /\\ i e. NN )' % A1
mi = w.s([], 'simpr', '( %s -> i e. NN )' % Ai)
di = dict(d); di['ff'] = w.s([d['ff']], 'adantr', '( %s -> %s )' % (Ai, FM))
sm, sq = psval(w, Ai, 'i', 'w', di, mi, w.s([wu], 'adantr', '( %s -> w e. U )' % Ai))
hex_ = a1(w, A1, 'seqex', 'seq 1 ( + , %s ) e. _V' % GZ('w'))
cl = w.s([d['nu1'], d['z1'], psf, wu, hex_, sq, ulm], 'ulmclm', '( %s -> seq 1 ( + , %s ) ~~> ( %s ` w ) )' % (A1, GZ('w'), GL))
ident, lim = psseq(w, A1, 'w', d, wu)
w.qed([w.s([cl, lim], 'jca', '( %s -> ( seq 1 ( + , %s ) ~~> ( %s ` w ) /\\ seq 1 ( + , %s ) ~~> sum_ k e. NN ( ( F ` k ) ` w ) ) )' % (A1, GZ('w'), GL, GZ('w'))),
       w.inst('climuni')], 'syl', '( %s -> ( %s ` w ) = sum_ k e. NN ( ( F ` k ) ` w ) )' % (A1, GL))
run5(w)

# ---------------------------------------------------------------- uhlim
w = W('uhlim', 'The partial-sum functions of a majorised term-function sequence converge '
      'uniformly to the sum function.')
d = ctx(w, A0)
ulm = w.s([w.s([d['uhs'], w.inst('uhmt')], 'syl', '( %s -> %s e. dom ( ~~>u ` U ) )' % (A0, PS)),
           w.s([w.s([], 'ulmdm', '( %s e. dom ( ~~>u ` U ) <-> %s ( ~~>u ` U ) %s )' % (PS, PS, GL))], 'a1i',
               '( %s -> ( %s e. dom ( ~~>u ` U ) <-> %s ( ~~>u ` U ) %s ) )' % (A0, PS, PS, GL))], 'mpbid',
          '( %s -> %s ( ~~>u ` U ) %s )' % (A0, PS, GL))
glf = w.s([ulm, w.inst('ulmcl')], 'syl', '( %s -> %s : U --> CC )' % (A0, GL))
fm = w.s([glf], 'feqmptd', '( %s -> %s = ( z e. U |-> ( %s ` z ) ) )' % (A0, GL, GL))
Az = '( %s /\\ z e. U )' % A0
lv = w.s([], 'uhlimv', '( %s -> ( %s ` z ) = sum_ k e. NN ( ( F ` k ) ` z ) )' % (Az, GL))
eq = w.s([fm, w.s([lv], 'mpteq2dva', '( %s -> ( z e. U |-> ( %s ` z ) ) = %s )' % (A0, GL, G))], 'eqtrd',
         '( %s -> %s = %s )' % (A0, GL, G))
w.qed([ulm, eq], 'breqtrd', '( %s -> %s ( ~~>u ` U ) %s )' % (A0, PS, G))
run5(w)
